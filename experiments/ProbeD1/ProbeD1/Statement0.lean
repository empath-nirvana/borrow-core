import ProbeD1.Sem

/-!
# ProbeD1 — statement 0: W's `U`, `⊸` and `∀` clauses fixed together (DESIGN §4)

For each placement `p`, five groups of facts. `Statement0 p` bundles them; a placement whose
bundle is proved, with statements 1–6, survives (`Survives`, `Programs.lean`), and W is the
surviving placement first in the cuts order (`Placement.rank`).

* **The order** (`ExtPreW`, `FutReLend`): W's `Ext` is a preorder, so `WP p` meets Targets'
  `ExtPre`; and a re-lend of a future is a future of a re-lend, the order's lemma the `U` clause's
  monotonicity needs.
* **Monotonicity** (T-MONO): the value and context relations along W's order (`MonoV`, `MonoG`),
  and the computation relation (`MonoC`), which `binder0`'s `U` clause needs. `MonoHide` is the
  hiding instance of `MonoV` (`MonoHideFromMonoV`), named because it is where `binder0` is
  expected to be tested hardest (DESIGN §4.3).
* **The nil slice** (OQ-58): W at `σ = []` inside Core (`NilSoundV`, `NilSoundC`); Core's thunks
  inside W at `σ = []` (`NilAgreesU`, the draft spec's form); the equality (`NilAgrees`), which
  decides OQ-58 beside the bundle.
* **The callback-extension fact** (OQ-8's criterion (iii)): a callback related at `σ`, applied at
  a fresh lend to a value of the lend's view type, is related at `σ·y` (`CallbackExtMut` for 6.65,
  `CallbackExtImm` for 6.64).
* **The `U`-clause thaw at the guarded W**: `[force]` (`ForceRow`), a `U` value re-lent and handed
  its views is a `U` value at the re-lend (`ThawRelend`), and the `U` introductions (`ThunkFRow`,
  `ThunkVRow`, `BangThunkFRow`, `BangThunkVRow`). None is assumed to transport from `vRLs`.

Statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS ReLend TabAtS jdgCty)

/-! ### The order -/

/-- **W's order is a preorder** (Targets' `ExtPre` at `WP p`, which `WLaws` asks): a future of a
future is a future, and `Ext` composes. -/
def ExtPreW (p : Placement) : Prop := Targets.ExtPre (WP (ℍ := ℍ) p).toBWorld

/-- **A re-lend of a future is a future of a re-lend**: the lifetimes a future gives, re-lent, are
those of a future of the stack at a re-lend of its own. -/
def FutReLend : Prop :=
  ∀ (δ : LSub) (ρ : WRes) (σ σ' : LStack) (αs αs' αs'' : List Life),
    StackOK σ αs → Fut δ ρ (σ, αs) (σ', αs') → ReLend αs'' αs' →
    ∃ αs₀, ReLend αs₀ αs ∧ Fut δ ρ (σ, αs₀) (σ', αs'')

/-! ### Monotonicity -/

/-- **Values along W's order**: records by `Ext`, the stack by a future at the value's resource,
its inserted entries not read by the type. -/
def MonoV (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes)
    (σ' : LStack) (αs' : List Life),
    StackOK σ αs → Ext ls ls' ρ → Fut δ ρ (σ, αs) (σ', αs') → FutAvoidsV A σ σ' →
    TabAtS σ αs ρ → vRL p σ δ A αs ls v ρ → vRL p σ' δ A αs' ls' v ρ

/-- **Contexts along W's order.** -/
def MonoG (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls ls' : List SRec)
    (ρ : WRes) (σ' : LStack) (αs' : List Life),
    StackOK σ αs → Ext ls ls' ρ → Fut δ ρ (σ, αs) (σ', αs') →
    (∀ s ∈ Γ, s.live = true → FutAvoidsV s.ty σ σ') →
    TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ → gRL p σ' δ αs' ls' Γ γ ρ

/-- **Computations along W's order.** -/
def MonoC (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls ls' : List SRec) (e : Expr) (ρ : WRes)
    (σ' : LStack) (αs' : List Life),
    StackOK σ αs → Ext ls ls' ρ → Fut δ ρ (σ, αs) (σ', αs') → FutAvoids C σ σ' →
    TabAtS σ αs ρ → cRL p σ δ C αs ls e ρ → cRL p σ' δ C αs' ls' e ρ

/-- **The hiding instance of `MonoV`**: a value used inside a handler of the names `N`. -/
def MonoHide (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes)
    (N : UInt32 → Bool), StackOK σ αs → TabAtS σ αs ρ →
    vRL p σ δ A αs ls v ρ → vRL p (hideS N σ) δ A αs ls v ρ

/-- `MonoHide` is `MonoV` at the one-step future that inserts nothing and hides `N` at depth `0`. -/
def MonoHideFromMonoV : Prop := ∀ p : Placement, MonoV (ℍ := ℍ) p → MonoHide (ℍ := ℍ) p

/-! ### The nil slice (OQ-58) -/

/-- W's values at `σ = []` are Core's. -/
def NilSoundV (p : Placement) : Prop :=
  ∀ (δ : LSub) (A : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vRL p [] δ A [] ls v ρ → vC true A ls δ v ρ

/-- W's computations at `σ = []` are Core's. -/
def NilSoundC (p : Placement) : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (e : Expr) (ρ : WRes),
    cRL p [] δ C [] ls e ρ → cC C ls δ e ρ

/-- **OQ-58 at `U`** (the draft spec's `NilAgreesU`): a thunk of Core's relation is a thunk of W's
at `σ = []`, so forced correctly at every future the placement's `U` clause quantifies over. -/
def NilAgreesU (p : Placement) : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (f : Val) (ρ : WRes),
    vC true (.thunk C) ls δ f ρ → vRL p [] δ (.thunk C) [] ls f ρ

/-- **OQ-58 (a)**: Core's relation is W's at `σ = []`, at every type. A statement about the
identity of two definitions: it decides OQ-58 for the placement's definitions (DESIGN §6.3). -/
def NilAgrees (p : Placement) : Prop :=
  (∀ (δ : LSub) (A : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vRL p [] δ A [] ls v ρ ↔ vC true A ls δ v ρ) ∧
  (∀ (δ : LSub) (C : CTy) (ls : List SRec) (e : Expr) (ρ : WRes),
    cRL p [] δ C [] ls e ρ ↔ cC C ls δ e ρ)

/-! ### The callback-extension fact -/

/-- **A 6.65 callback read at `σ`, applied at a fresh lend, is read at `σ·y`.** The callback `f` is
a value of `U(∀'y ⊏ c. Mut 'y T ⊸ D)` at `σ`; the entry `e` lends a new place at `α` below the
callback's resource and below the stack (`OwnOK`); the argument is any value of `Mut 'y T` at the
extended stack (the lend's view among them). -/
def CallbackExtMut (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T : VTy) (D : CTy)
    (αs : List Life) (ls : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (α : Life) (ρv ρ : WRes),
    StackOK σ αs → e.x = y → e.k = .mut → y ∉ CTy.binders (.arr (.mut (.var y) T) D) →
    OwnOK δ σ αs e α ρf → LtLife (extS δ σ αs) c α → TabAtS σ αs ρf →
    vRL p σ δ (.thunk (.all y c (.arr (.mut (.var y) T) D))) αs ls f ρf →
    vRL p (e :: σ) (δ.extend y α) (.mut (.var y) T) (α :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    cRL p (e :: σ) (δ.extend y α) D (α :: αs) ls
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ

/-- **A 6.64 callback read at `σ`, applied at a fresh lend, is read at `σ·y`.** The entry fixes the
value `u` 6.64 fixes; the callback runs at a list `ls'` that extends `ls` (6.64 adds its record,
`ext_add`), where the argument is any value of `Imm 'y T` at the extended stack, its coherence with
the records (`CohE`) included. -/
def CallbackExtImm (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T : VTy) (D : CTy)
    (αs : List Life) (ls ls' : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (u : Val) (α : Life)
    (ρv ρ : WRes),
    StackOK σ αs → e.x = y → e.k = .imm u → y ∉ CTy.binders (.arr (.imm (.var y) T) D) →
    OwnOK δ σ αs e α ρf → LtLife (extS δ σ αs) c α → TabAtS σ αs ρf → Ext ls ls' ρf →
    vRL p σ δ (.thunk (.all y c (.arr (.imm (.var y) T) D))) αs ls f ρf →
    vRL p (e :: σ) (δ.extend y α) (.imm (.var y) T) (α :: αs) ls' w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    cRL p (e :: σ) (δ.extend y α) D (α :: αs) ls'
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ

/-! ### The `U`-clause thaw at the guarded W -/

/-- **`[force]` at W** (`force_RLa`'s statement at the placement's relation). -/
def ForceRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (i : Nat) (C : CTy), Ctx.SoloP Γ i (.thunk C) →
    SemS p Δ Γ (forceE C (.var i)) (.comp C)

/-- **A `U` value thaws at a re-lend** (`relendableS_thunk`'s statement at the guarded W): re-lent
at `αs'` and handed the views it dropped, it is a `U` value at `αs'`. -/
def ThawRelend (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → TabAtS σ αs ρ → vRL p σ δ (.thunk C) αs ls f ρ →
    ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ [] σ ds αs ls ρn ∧
      ∀ ls', Ext ls ls' ρz → ∀ αs', ReLend αs' αs →
        (vwS δ [] σ ds αs' ls' ─⋆ vRL p σ δ (.thunk C) αs' ls' f) ρz

/-- **`thunk M : U (F A)` at W** (the `thunkF` row). -/
def ThunkFRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy),
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

/-- **`thunk V : U C` at W** (the `thunkV` row): the row at which a callback becomes a value. -/
def ThunkVRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), C.isRet = false →
    SemS p Δ Γ (.val (.lam N)) (.comp C) → SemS p Δ Γ (.val (.lam N)) (.val (.thunk C))

/-- **Promotion of `thunk M : U (F A)` at W** (the `bangThunkF` row). -/
def BangThunkFRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), Persistent Γ →
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

/-- **Promotion of a λ-value at W** (the `bangThunkV` row): the row at which `retryR` and
`timeoutR` become values. -/
def BangThunkVRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), Persistent Γ → C.isRet = false →
    SemS p Δ Γ (.val (.lam N)) (.comp C) → SemS p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-! ### The bundle -/

/-- **Statement 0 at the placement `p`.** -/
def Statement0 (p : Placement) : Prop :=
  ExtPreW (ℍ := ℍ) p ∧ FutReLend ∧ MonoV (ℍ := ℍ) p ∧ MonoG (ℍ := ℍ) p ∧
    NilSoundV (ℍ := ℍ) p ∧ NilSoundC (ℍ := ℍ) p ∧ CallbackExtMut (ℍ := ℍ) p ∧
    CallbackExtImm (ℍ := ℍ) p ∧ ForceRow (ℍ := ℍ) p ∧ ThawRelend (ℍ := ℍ) p ∧
    ThunkFRow (ℍ := ℍ) p ∧ ThunkVRow (ℍ := ℍ) p ∧ BangThunkFRow (ℍ := ℍ) p ∧
    BangThunkVRow (ℍ := ℍ) p

end ProbeD1

end
