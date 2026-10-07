import ProbeD1.Binder

/-!
# ProbeD1 — the revised W, and the `U` introductions retried at it (`BINDER.md` §5)

W as `BINDER.md` §5.1 revises it, beside W₀ (`Relation.lean`, `Sem.lean`), under the suffix `I`.
When the revision lands these replace W₀'s definitions, and W₀'s proofs are redone (`BINDER.md`
§6). Until then the target of the unit's item 4 elaborates here as the design states it.

* **The relation** (`vRLI`, `cRLI`, `effRetI`, `gRLI`): W₀'s, with
  - the guard `guardPV`: the table and the views at every depth (`PlaceViewsL`), at the clause's
    reading and list;
  - the `Mut` and `Imm` leaves conjoining `CohS`;
  - `binder0`'s `U` clause `RelendI`, over instantiations of the stack's internal lifetimes;
  - the `∀` clause's own lend at `OwnPushI`, fresh below the records (`RecsOutside` at the pushed
    stack) and the reading (`SubFresh`);
  - the futures of `⊸` and `∀` at `FutOKI`.
  `cbpv`'s and `binder`'s `U` clause stays `RelendU` (`RelendUI` is the next unit's), and the
  stop's share stays W₀'s (statement 2 restates it).
* **The judgement** (`SemSI`): `SemS` with the index invariants `RecsOutside` and `SubOutside`, and
  the guard's views beside the table.
* **Item 4.** The target `Statement0UFull`: statement 0's four `U` rows at `SemSI`, with the thaw at
  every context (`CtxRelendsAll`). The partial result `Statement0UThawFree`, at the contexts
  `CtxThawFree` admits; `ThawFreeScope` shows that typing reaches a context it excludes.

Definitions and `def … : Prop` statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS stratS ReLend bodyS OpenS rowTab TabAtS jdgCty)

/-! ### The revised relation -/

mutual
/-- **W's value relation, revised**, at the placement `p`, the stack `σ`, the lends at `αs`. -/
def vRLI (p : Placement) : LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | σ, δ, .thunk C, αs, ls, f =>
      guardPV (extS δ σ αs) σ αs ls
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRLI p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendI δ σ (fun δ' αs' ls' => cRLI p σ δ' C αs' ls' (forceE C (.val f))) αs ls)
  | σ, δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLI p σ δ A αs ls v₁ ⋆ vRLI p σ δ B αs ls v₂
  | σ, δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLI p σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLI p σ δ B αs ls v₂)
  | σ, δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRLI p σ δ A αs ls v ρ
  | σ, δ, .box a A, αs, ls, v => atLife (extS δ σ αs) a fun α => box α (vRLI p σ δ A αs ls v)
  | σ, δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLI p σ δ A αs ls v'
  | σ, δ, .mut a T, αs, ls, v => fun ρ =>
      vC true (.mut a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.mut a T) v ρ
  | σ, δ, .imm a T, αs, ls, v => fun ρ =>
      vC true (.imm a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.imm a T) v ρ
  | σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ _ A => A
/-- **W's computation relation, revised.** -/
def cRLI (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  | σ, δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRLI p σ δ B αs ls'' v
  | σ, δ, .eff n i q A B C, αs, ls, e =>
      if p.shareFut then
        bodySF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRetI p σ' δ C αs' ls v)
          (OpenSF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRetI p σ' δ C αs' ls v))
          σ αs ls e
      else
        bodyS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetI p σ δ C αs' ls v)
          (OpenS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetI p σ δ C αs' ls v)) αs ls e
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.arr A C) σ σ' → ∀ v,
          (vRLI p σ' δ A αs' ls' v ─⋆
            guardPV (extS δ σ' αs') σ' αs' ls' (cRLI p σ' δ C αs' ls' (.app e (.val v)))) ρ
  | σ, δ, .amp C D, αs, ls, e => fun ρ =>
      cRLI p σ δ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLI p σ δ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | _, _, .top, _, _, _ => fun _ => True
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.all x c C) σ σ' →
        (∀ α, (⌜LtLife (extS δ σ' αs') c α⌝ ─⋆
          guardPV (extS (δ.extend x α) σ' αs') σ' αs' ls'
            (cRLI p σ' (δ.extend x α) C αs' ls' (.app e (.val .unit)))) ρ) ∧
        (p.allOwn = true → ∀ (en : LEnt) (α : Life), OwnPushI δ (.all x c C) ρ (σ', αs') en α →
          RecsOutside (α :: αs') ls' → SubFresh δ α →
          guardPV (extS (δ.extend x α) (en :: σ') (α :: αs')) (en :: σ') (α :: αs') ls'
            (cRLI p (en :: σ') (δ.extend x α) C (α :: αs') ls' (.app e (.val .unit))) ρ)
  | σ, δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
termination_by structural _ _ C => C
/-- The answer relation of `F_Σ R`, revised: `vRLI R`. -/
def effRetI (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Val → WProp
  | σ, δ, .ret A, αs => fun ls v => vRLI p σ δ A αs ls v
  | σ, δ, .eff _ _ _ _ _ C, αs => effRetI p σ δ C αs
  | _, _, _, _ => fun _ _ _ => False
termination_by structural _ _ C => C
end

/-- `⊛_{x ∈ dom(Γ)} vRLI(Γ(x))`. -/
def gSepRLI (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then vRLI p σ δ s.ty αs ls v ⋆ gSepRLI p σ δ αs ls Γ γ
      else gSepRLI p σ δ αs ls Γ γ

/-- `𝒢⟦Γ⟧` at the revised W. -/
def gRLI (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLI p σ δ αs ls Γ γ

/-- **The semantic judgement at the revised W**: `SemS` with the records' invariant
(`RecsOutside`), the readings' invariant (`SubOutside`) and the guard's views (`PlaceViewsL`) in
the index. -/
def SemSI (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ → Δ.Models (extS δ σ αs) →
    RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLI p σ δ αs ls Γ γ ρ →
    cRLI p σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-! ### The `U` introductions retried -/

/-- **The context's thaw over instantiations**, at one row's context: at every index `SemSI` admits,
a context related at the stack is re-lendable over instantiations. -/
def CtxRelendableAtI (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → SubDom δ Δ → Δ.Models (extS δ σ αs) → RecsOutside αs ls → SubOutside σ αs δ →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLI p σ δ αs ls Γ γ ρ →
    RelendI δ σ (fun δ' αs' ls' => gRLI p σ δ' αs' ls' Γ γ) αs ls ρ

/-- **The thaw at every context**: the target. -/
def CtxRelendsAll (p : Placement) : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxRelendableAtI p Δ Γ

/-- **The thaw at the contexts the partial result handles.** -/
def CtxRelendsThawFree (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxThawFree Γ → CtxRelendableAtI p Δ Γ

/-- **A `U` value instantiated is a `U` value at the instantiation** (`ThawRelend` over
instantiations). -/
def ThawInst (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLI p σ δ (.thunk C) αs ls f ρ →
    RelendI δ σ (fun δ' αs' ls' => vRLI p σ δ' (.thunk C) αs' ls' f) αs ls ρ

/-- **`thunk M : U (F A)` at the revised W** (statement 0's `thunkF` row at `SemSI`). -/
def ThunkFRowI (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy),
    SemSI p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSI p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

/-- **`thunk V : U C` at the revised W** (the `thunkV` row). -/
def ThunkVRowI (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), C.isRet = false → OwnHyg Δ Γ C →
    SemSI p Δ Γ (.val (.lam N)) (.comp C) → SemSI p Δ Γ (.val (.lam N)) (.val (.thunk C))

/-- **Promotion of `thunk M : U (F A)` at the revised W** (the `bangThunkF` row). -/
def BangThunkFRowI (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), Persistent Γ →
    SemSI p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSI p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

/-- **Promotion of a λ-value at the revised W** (the `bangThunkV` row). -/
def BangThunkVRowI (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), Persistent Γ → C.isRet = false →
    OwnHyg Δ Γ C →
    SemSI p Δ Γ (.val (.lam N)) (.comp C) → SemSI p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 at the revised W**: the target. The four rows are statement 0's
own, read at `SemSI`, with the thaw at every context. -/
def Statement0UFull (p : Placement) : Prop :=
  ThawInst (ℍ := ℍ) p ∧ CtxRelendsAll (ℍ := ℍ) p ∧ ThunkFRowI (ℍ := ℍ) p ∧
    ThunkVRowI (ℍ := ℍ) p ∧ BangThunkFRowI (ℍ := ℍ) p ∧ BangThunkVRowI (ℍ := ℍ) p

/-- **`thunk M : U (F A)`** at a context the partial result handles. -/
def ThunkFRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ →
    SemSI p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSI p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

/-- **`thunk V : U C`** at a context the partial result handles. -/
def ThunkVRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → C.isRet = false →
    OwnHyg Δ Γ C → SemSI p Δ Γ (.val (.lam N)) (.comp C) →
    SemSI p Δ Γ (.val (.lam N)) (.val (.thunk C))

/-- **`!thunk M : !U (F A)`** at a persistent context the partial result handles. -/
def BangThunkFRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ → Persistent Γ →
    SemSI p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSI p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

/-- **`!thunk V : !U C`** at a persistent context the partial result handles. -/
def BangThunkVRowTF (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → Persistent Γ →
    C.isRet = false → OwnHyg Δ Γ C → SemSI p Δ Γ (.val (.lam N)) (.comp C) →
    SemSI p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 at the contexts `CtxThawFree` admits**: the partial result,
guarantee gap R1 (`μ`, `fam`) open. -/
def Statement0UThawFree (p : Placement) : Prop :=
  ThawInst (ℍ := ℍ) p ∧ CtxRelendsThawFree (ℍ := ℍ) p ∧ ThunkFRowTF (ℍ := ℍ) p ∧
    ThunkVRowTF (ℍ := ℍ) p ∧ BangThunkFRowTF (ℍ := ℍ) p ∧ BangThunkVRowTF (ℍ := ℍ) p

/-- `μX. 1 ⊕ X`, a list of units: a slot type `CtxThawFree` excludes. -/
abbrev listTy : VTy := .mu (.sum .unit (.tvar 0))

/-- The type of `Λ'0. λm. λxs. thunk (return (m, xs))`:
`∀'0 ⊏ ⊤. Mut '0 1 ⊸ μX. 1 ⊕ X ⊸ F (U (F (Mut '0 1 ⊗ μX. 1 ⊕ X)))`. -/
abbrev scopeC : CTy :=
  .all 0 .top (.arr (.mut (.var 0) .unit)
    (.arr listTy (.ret (.thunk (.ret (.tensor (.mut (.var 0) .unit) listTy))))))

/-- The context at the thunk: `xs : μX. 1 ⊕ X`, `m : Mut '0 1`, the `∀`'s slot dead. -/
abbrev scopeΓ : Ctx VTy := [⟨listTy, true⟩, ⟨.mut (.var 0) .unit, true⟩, ⟨.unit, false⟩]

/-- **`CtxThawFree` excludes a context typing reaches inside a lend.** The closed term
`Λ'0. λm. λxs. thunk (return (m, xs))` is derived at `scopeC`. Read at `[]`, `binder0`'s `∀`
clause pushes the own lend of `'0` (`OwnPushI`, payload `1`, `qEnt`), and at the pushed stack the
`U` introduction sits at `scopeΓ`, whose live slot `xs` is a `μ` and whose live slot `m` is the
lend's view. So the partial result says nothing of this thunk. -/
def ThawFreeScope : Prop :=
  CDerives LifeCtx.empty []
      (.val (.lam (.val (.lam (.val (.lam (.val (.lam (.pair (.var 2) (.var 1))))))))))
      (.comp scopeC) ∧
    CDerives kΔ scopeΓ (.val (.lam (.pair (.var 2) (.var 1))))
      (.val (.thunk (.ret (.tensor (.mut (.var 0) .unit) listTy)))) ∧
    OwnPushI kδ scopeC PMap.empty ([], []) qEnt kα ∧ ¬ CtxThawFree scopeΓ

end ProbeD1

end
