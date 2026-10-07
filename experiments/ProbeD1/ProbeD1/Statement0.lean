import ProbeD1.Sem

/-!
# ProbeD1 — statement 0: W's `U`, `⊸` and `∀` clauses fixed together (DESIGN §4)

Two bundles. The **shared lemmas** (`Statement0Shared`) are about definitions every placement
shares. A failure of one is a finding about those definitions, not a comparison of placements,
and stops the probe (DESIGN §12.3). The **per-placement facts** (`Statement0 p`) are the ones the
placements are compared on. A placement whose shared lemmas and facts are proved, with statements
1–6, survives (`Survives`, `Programs.lean`).

* **The order** (shared). `ExtPreW` is bookkeeping: a future is a reflexive–transitive closure and
  `Ext` composes, so `WP p` meets Targets' `ExtPre` by construction. The clauses read W's order at
  the reading substitution `δ`, and the lemmas they use are stated there: a re-lend of a future is
  a future of a re-lend (`FutReLend`), a future at a resource is a future at its parts (`FutPart`),
  and a composite future's inserted entries avoid a type when each step's do (`FutAvoidsTrans`).
* **The piece at the reflexive future** (shared): `OpenSF true` gives GhostEnd's `OpenS` at the
  stack itself (`OpenSFBridge`), so GhostEnd's lemmas that only consume a piece apply unchanged.
* **The nil slice the programs read** (shared): W's computations at `σ = []` are Core's at
  `F_Σ A` with `A` data (`NilSoundRet`), the slice Targets' `AdequateRetAt` reads.
* **Monotonicity** (per placement): contexts across the callback's own lend (`MonoOwnG`), and values
  and contexts along W's order (`MonoV`, `MonoG`). `MonoC` and `MonoHide` (`MonoHideFromMonoV`)
  are stated beside the bundles.
* **The callback-extension fact** (per placement): a callback related at `σ`, applied at a fresh
  lend to a value of the lend's view type, is related at `σ·y` (`CallbackExtMut` for 6.65,
  `CallbackExtImm` for 6.64).
* **The `U`-clause thaw at the guarded W** (per placement): `[force]` (`ForceRow`), a `U` value
  re-lent and handed its views is a `U` value at the re-lend (`ThawRelend`), and the `U`
  introductions (`ThunkFRow`, `ThunkVRow`, `BangThunkFRow`, `BangThunkVRow`). None is assumed to
  transport from `vRLs`.
* **Beside the bundles** (OQ-58): the nil slice at every type, W inside Core (`NilSoundV`,
  `NilSoundC`) and Core inside W (`NilAgreesU`, `NilAgrees`). Core's `⊸` reads its argument
  contravariantly, so W inside Core at `A ⊸ C` needs Core inside W at `A`, which at a thunk
  argument is `NilAgreesU`: OQ-58's question, decided beside the bundles (DESIGN §6.3).

Statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS ReLend TabAtS jdgCty OpenS)

/-! ### The order (shared) -/

/-- **W's world order is a preorder** (Targets' `ExtPre` at `WP p`, which `WLaws` asks).
Bookkeeping: it holds by construction, a future being a reflexive–transitive closure and `Ext`
reflexive and transitive. `WP p`'s `Ext` is `OrdW` at the empty substitution, which is not the
order the clauses read; their lemmas are `FutReLend`, `FutPart` and `FutAvoidsTrans`, at `δ`. -/
def ExtPreW (p : Placement) : Prop := Targets.ExtPre (WP (ℍ := ℍ) p).toBWorld

/-- **A re-lend of a future is a future of a re-lend**: the lifetimes a future gives, re-lent, are
those of a future of the stack at a re-lend of its own. -/
def FutReLend : Prop :=
  ∀ (δ : LSub) (ρ : WRes) (σ σ' : LStack) (αs αs' αs'' : List Life),
    StackOK σ αs → Fut δ ρ (σ, αs) (σ', αs') → ReLend αs'' αs' →
    ∃ αs₀, ReLend αs₀ αs ∧ Fut δ ρ (σ, αs₀) (σ', αs'')

/-- **A future at a resource is a future at each of its parts.** `FutOK.below` asks the inserted
lifetimes below the holder's resource, and a part lies in every stratum the whole does. A value is
carried to a future at its whole resource, while the `U` clause and the share quantify over futures
at the part `ρz` strictly above the outermost lend. -/
def FutPart : Prop :=
  ∀ (δ : LSub) (ρz ρn ρ : WRes) (s s' : Stk), ResU.CompS ρz ρn ρ → Fut δ ρ s s' → Fut δ ρz s s'

/-- **A composite future's inserted entries avoid a type when each step's do**, at computation and
at value types. A `U` value carried to a future owes its computation at the futures of that
future, and those avoid its type only through this. -/
def FutAvoidsTrans : Prop :=
  (∀ (C : CTy) (σ σ' σ'' : LStack), FutAvoids C σ σ' → FutAvoids C σ' σ'' → FutAvoids C σ σ'') ∧
  ∀ (A : VTy) (σ σ' σ'' : LStack), FutAvoidsV A σ σ' → FutAvoidsV A σ' σ'' → FutAvoidsV A σ σ''

/-! ### The piece at the reflexive future (shared) -/

/-- **The share over futures gives GhostEnd's piece at the stack itself**: every futures quantifier
of `OpenSF true` instantiated at the reflexive future (the kept part `σ.drop k` itself,
`σ.take k ++ σ.drop k = σ`). GhostEnd's lemmas that consume an `OpenS` input apply through it
unchanged; those whose output must be W's piece at `cbpv` or `binder` are restated over `OpenSF`
(DESIGN §6.2). -/
def OpenSFBridge : Prop :=
  ∀ (δ : LSub) (Tab : OpTab) (Q : LStack → List Life → List SRec → Val → WProp) (σ : LStack)
    (k : Nat) (ds : List Bool) (αi αo : List Life) (ls : List SRec) (e : Expr) (ρ : WRes),
    OpenSF (ℍ := ℍ) true δ Tab Q σ k ds αi αo ls e ρ → OpenS δ σ Tab (Q σ) k ds αi αo ls e ρ

/-! ### The nil slice the programs read (shared) -/

/-- **W's computations at `σ = []` are Core's, at a data answer**: the slice Targets'
`AdequateRetAt` reads, `F_Σ A` with `A` data (`DivFree S A` is `A.Data`). The operation types are
read by Core's `vC` in `rowTab` at both relations, and the answer is data, so no W relation sits at
a negative position. At `F A` (`S = []`) it is the route for the programs' runs (DESIGN §9.1). -/
def NilSoundRet (p : Placement) : Prop :=
  ∀ (δ : LSub) (S : Row) (A : VTy) (ls : List SRec) (e : Expr) (ρ : WRes), A.Data →
    cRL p [] δ (CTy.effOf S A) [] ls e ρ → cC (CTy.effOf S A) ls δ e ρ

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

/-- **Contexts across the callback's own lend**: a context related at `σ` is related at the stack
the own lend of the type `C` pushes on it, when the pushed variable is neither free nor bound in
the context's live types (`CtxFresh`). The push is not a future (its variable is the type's
binder, not a future's name), so `MonoG` does not give it. `ThunkVRow` and `BangThunkVRow` at
`cbpv` (the `U` clause's own push) and `AllIRow` at `binder0` and `binder` (the `∀` clause's own
push) call their premise at the pushed stack, with the context carried there by this. -/
def MonoOwnG (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackOK σ αs → OwnPush δ C ρ (σ, αs) e a → CtxFresh e.x Γ → TabAtS σ αs ρ →
    gRL p σ δ αs ls Γ γ ρ → gRL p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-- **Computations along W's order**, stated beside the bundles: `binder0`'s `U` clause needs it
for `MonoV` at a `U` value. -/
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

/-! ### The nil slice at every type (OQ-58, beside the bundles) -/

/-- W's values at `σ = []` are Core's, at every type: the W-inside-Core half of `NilAgrees`. -/
def NilSoundV (p : Placement) : Prop :=
  ∀ (δ : LSub) (A : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vRL p [] δ A [] ls v ρ → vC true A ls δ v ρ

/-- W's computations at `σ = []` are Core's, at every type. At `A ⊸ C` Core reads the argument
contravariantly (`∀ v, vCE A v ─⋆ cC C …`), so this needs Core's `A` inside W's: at a thunk
argument, `NilAgreesU`. -/
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

/-- **`thunk V : U C` at W** (the `thunkV` row): the row at which a callback becomes a value. It
takes the own lend's hygiene (`OwnHyg`), which the `U` clause's own push at `cbpv` reads. -/
def ThunkVRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), C.isRet = false → OwnHyg Δ Γ C →
    SemS p Δ Γ (.val (.lam N)) (.comp C) → SemS p Δ Γ (.val (.lam N)) (.val (.thunk C))

/-- **Promotion of `thunk M : U (F A)` at W** (the `bangThunkF` row). -/
def BangThunkFRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), Persistent Γ →
    SemS p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemS p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

/-- **Promotion of a λ-value at W** (the `bangThunkV` row): the row at which `retryR` and
`timeoutR` become values. It takes the own lend's hygiene, as `ThunkVRow` does. -/
def BangThunkVRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), Persistent Γ → C.isRet = false →
    OwnHyg Δ Γ C →
    SemS p Δ Γ (.val (.lam N)) (.comp C) → SemS p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-! ### The bundles -/

/-- **Statement 0's shared lemmas**: about definitions every placement shares. Their failure is a
finding about those definitions and stops the probe (DESIGN §12.3). -/
def Statement0Shared : Prop :=
  (∀ p : Placement, ExtPreW (ℍ := ℍ) p) ∧ FutReLend ∧ FutPart ∧ FutAvoidsTrans ∧
    OpenSFBridge (ℍ := ℍ) ∧ ∀ p : Placement, NilSoundRet (ℍ := ℍ) p

/-- **Statement 0 at the placement `p`**: the facts the placements are compared on. -/
def Statement0 (p : Placement) : Prop :=
  MonoOwnG (ℍ := ℍ) p ∧ MonoV (ℍ := ℍ) p ∧ MonoG (ℍ := ℍ) p ∧ CallbackExtMut (ℍ := ℍ) p ∧
    CallbackExtImm (ℍ := ℍ) p ∧ ForceRow (ℍ := ℍ) p ∧ ThawRelend (ℍ := ℍ) p ∧
    ThunkFRow (ℍ := ℍ) p ∧ ThunkVRow (ℍ := ℍ) p ∧ BangThunkFRow (ℍ := ℍ) p ∧
    BangThunkVRow (ℍ := ℍ) p

end ProbeD1

end
