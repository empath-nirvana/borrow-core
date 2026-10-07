import ProbeD1.BinderRefute

/-!
# ProbeD1 — the draft W as this build revises it (`BINDER.md` §11.4)

`BinderW.lean` states the design's revision of W (`vRLI`). The build refuted three steps of its
plan (`BinderRefute.lean`), each at a configuration not shown to arise, and with them the item-4
targets as designed. This file is the one draft relation at W that replaces `vRLI`: `vRLI` with
three changes, each answering one refuted step, none to a printed BoLo definition and none in
`Core/`.

* **`RelendJ`: the extension keeps the retained part's records with their tags** (`KeepsT`).
  `ExtInst` is refuted (`not_extInst`): `Ext` keeps a relevant record untagged, so an extension may
  hold it at a tag the instantiation leaves alone while the original list holds it at one the
  instantiation moves, and the composite of two instantiations is then not covered. `KeepsT`
  composes along instantiations (`ext_inst_comp`, `BinderRows.lean`). `[force]` supplies it at the
  list itself, and the composite by `ext_inst_comp`; the share's is statement 2's (`BINDER.md`
  §3.7).
* **The retained borrow leaves read their payload type only at external lifetimes** (`PayExt`, in
  `vRLJ`'s `Mut` and `Imm` leaves at a place no entry lends). `MutPayloadInst`'s support conjunct
  is refuted (`not_mutPayloadInst`), and the thaw as designed with it (`not_ctxRelendsThawFree`):
  a retained cell whose payload type reads an internal lifetime can have its stored predicate's
  support broken by the room an instantiation's gap makes. [unchecked] A retained cell was made
  outside the frozen computation; its payload type, fixed when the cell was made (`Mut` is
  invariant: `mutSub` changes only the lifetime index), reads the variables bound then, which
  `SubOutside` reads above every lend. That every row introducing a retained `Mut` or `Imm` value
  establishes it is the next unit's to prove.
* **`SemSJ`'s index has its outermost lend below `⊤`** (`OuterBelowTop`). `CohEInst` is refuted at
  an outermost lend at `⊤` (`not_cohEInst`): the cut is then `⊤` itself, a record at `⊤` is left
  alone, and its reading below `⊤` moves in the slot's. Every own lend is below `⊤`
  (`ownPushBelowTop`). [unchecked] So is every lend [TR] 6.64 and 6.65 make, whose H4 takes it
  below a lifetime (6.65: the cell made at "α ⊏ γ ⊓ β").

Definitions only; the proofs are in `BinderRows.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS stratS ReLend bodyS OpenS rowTab TabAtS jdgCty)

/-! ### The clause, the leaves, the index -/

/-- **The extension keeps the records relevant to `ρ`, tags and all.** -/
def KeepsT (ls ls' : List SRec) (ρ : WRes) : Prop := ∀ x ∈ ls, Core.Rel x.1 ρ → x ∈ ls'

/-- **W's `U` clause over instantiations, revised**: `RelendI`, the extension keeping the retained
part's records with their tags. -/
def RelendJ (δ : LSub) (σ : LStack) (P : LSub → List Life → List SRec → WProp)
    (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwSL (extS δ σ αs) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ι, InstAt αs ι → ∀ ls', Ext (ι.recs ls) ls' ρz → KeepsT (ι.recs ls) ls' ρz →
      KeepsS (ι.recs ls) ls' ρn → RecsOutside (ι.life αs) ls' →
      (vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ─⋆
        P (ι.sub δ) (ι.life αs) ls') ρz

/-- **A payload type read only at lifetimes every instantiation of the stack fixes.** -/
def PayExt (αs : List Life) (s : LSub) (T : VTy) : Prop :=
  ∀ y, VFree y T → ∀ m, s.find? y = some m → ¬ Internal αs (OrderDual.toDual m)

/-- **A retained borrow leaf reads its payload type only at external lifetimes**: at a place no
entry of the stack lends. -/
def RetainedPay (σ : LStack) (αs : List Life) (s : LSub) (T : VTy) (v : Val) : Prop :=
  ∀ l, v = .loc l → innerAt σ αs l = none → PayExt αs s T

mutual
/-- **W's value relation as this build revises it.** -/
def vRLJ (p : Placement) : LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | σ, δ, .thunk C, αs, ls, f =>
      guardPV (extS δ σ αs) σ αs ls
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRLJ p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendJ δ σ (fun δ' αs' ls' => cRLJ p σ δ' C αs' ls' (forceE C (.val f))) αs ls)
  | σ, δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLJ p σ δ A αs ls v₁ ⋆ vRLJ p σ δ B αs ls v₂
  | σ, δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLJ p σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLJ p σ δ B αs ls v₂)
  | σ, δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRLJ p σ δ A αs ls v ρ
  | σ, δ, .box a A, αs, ls, v => atLife (extS δ σ αs) a fun α => box α (vRLJ p σ δ A αs ls v)
  | σ, δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLJ p σ δ A αs ls v'
  | σ, δ, .mut a T, αs, ls, v => fun ρ =>
      vC true (.mut a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.mut a T) v ρ ∧
        RetainedPay σ αs (extS δ σ αs) T v
  | σ, δ, .imm a T, αs, ls, v => fun ρ =>
      vC true (.imm a T) ls (extS δ σ αs) v ρ ∧ CohS σ αs (extS δ σ αs) (.imm a T) v ρ ∧
        RetainedPay σ αs (extS δ σ αs) T v
  | σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ _ A => A
/-- **W's computation relation as this build revises it.** -/
def cRLJ (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  | σ, δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRLJ p σ δ B αs ls'' v
  | σ, δ, .eff n i q A B C, αs, ls, e =>
      if p.shareFut then
        bodySF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRetJ p σ' δ C αs' ls v)
          (OpenSF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRetJ p σ' δ C αs' ls v))
          σ αs ls e
      else
        bodyS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetJ p σ δ C αs' ls v)
          (OpenS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetJ p σ δ C αs' ls v)) αs ls e
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.arr A C) σ σ' → ∀ v,
          (vRLJ p σ' δ A αs' ls' v ─⋆
            guardPV (extS δ σ' αs') σ' αs' ls' (cRLJ p σ' δ C αs' ls' (.app e (.val v)))) ρ
  | σ, δ, .amp C D, αs, ls, e => fun ρ =>
      cRLJ p σ δ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLJ p σ δ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | _, _, .top, _, _, _ => fun _ => True
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.all x c C) σ σ' →
        (∀ α, (⌜LtLife (extS δ σ' αs') c α⌝ ─⋆
          guardPV (extS (δ.extend x α) σ' αs') σ' αs' ls'
            (cRLJ p σ' (δ.extend x α) C αs' ls' (.app e (.val .unit)))) ρ) ∧
        (p.allOwn = true → ∀ (en : LEnt) (α : Life), OwnPushI δ (.all x c C) ρ (σ', αs') en α →
          RecsOutside (α :: αs') ls' → SubFresh δ α →
          guardPV (extS (δ.extend x α) (en :: σ') (α :: αs')) (en :: σ') (α :: αs') ls'
            (cRLJ p (en :: σ') (δ.extend x α) C (α :: αs') ls' (.app e (.val .unit))) ρ)
  | σ, δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
termination_by structural _ _ C => C
/-- The answer relation of `F_Σ R`: `vRLJ R`. -/
def effRetJ (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Val → WProp
  | σ, δ, .ret A, αs => fun ls v => vRLJ p σ δ A αs ls v
  | σ, δ, .eff _ _ _ _ _ C, αs => effRetJ p σ δ C αs
  | _, _, _, _ => fun _ _ _ => False
termination_by structural _ _ C => C
end

/-- `⊛_{x ∈ dom(Γ)} vRLJ(Γ(x))`. -/
def gSepRLJ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then vRLJ p σ δ s.ty αs ls v ⋆ gSepRLJ p σ δ αs ls Γ γ
      else gSepRLJ p σ δ αs ls Γ γ

/-- `𝒢⟦Γ⟧` at the revised W. -/
def gRLJ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLJ p σ δ αs ls Γ γ

/-- **The semantic judgement at the revised W**: `SemSI`, the outermost lend below `⊤`. -/
def SemSJ (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ →
    Δ.Models (extS δ σ αs) → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLJ p σ δ αs ls Γ γ ρ →
    cRLJ p σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-! ### Item 4's statements at the revised W -/

/-- **The context's thaw over instantiations**, at the revised W. -/
def CtxRelendableAtJ (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → SubDom δ Δ → Δ.Models (extS δ σ αs) →
    RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLJ p σ δ αs ls Γ γ ρ →
    RelendJ δ σ (fun δ' αs' ls' => gRLJ p σ δ' αs' ls' Γ γ) αs ls ρ

def CtxRelendsAllJ (p : Placement) : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxRelendableAtJ p Δ Γ

def CtxRelendsThawFreeJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxThawFree Γ → CtxRelendableAtJ p Δ Γ

/-- **A `U` value instantiated is a `U` value at the instantiation**, at the revised W. -/
def ThawInstJ (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLJ p σ δ (.thunk C) αs ls f ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLJ p σ δ' (.thunk C) αs' ls' f) αs ls ρ

def ThunkFRowJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy),
    SemSJ p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSJ p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

def ThunkVRowJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), C.isRet = false → OwnHyg Δ Γ C →
    SemSJ p Δ Γ (.val (.lam N)) (.comp C) → SemSJ p Δ Γ (.val (.lam N)) (.val (.thunk C))

def BangThunkFRowJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), Persistent Γ →
    SemSJ p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSJ p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

def BangThunkVRowJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), Persistent Γ → C.isRet = false →
    OwnHyg Δ Γ C →
    SemSJ p Δ Γ (.val (.lam N)) (.comp C) → SemSJ p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 at the revised W**, the thaw at every context. -/
def Statement0UFullJ (p : Placement) : Prop :=
  ThawInstJ (ℍ := ℍ) p ∧ CtxRelendsAllJ (ℍ := ℍ) p ∧ ThunkFRowJ (ℍ := ℍ) p ∧
    ThunkVRowJ (ℍ := ℍ) p ∧ BangThunkFRowJ (ℍ := ℍ) p ∧ BangThunkVRowJ (ℍ := ℍ) p

def ThunkFRowTFJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ →
    SemSJ p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSJ p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

def ThunkVRowTFJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → C.isRet = false →
    OwnHyg Δ Γ C → SemSJ p Δ Γ (.val (.lam N)) (.comp C) →
    SemSJ p Δ Γ (.val (.lam N)) (.val (.thunk C))

def BangThunkFRowTFJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxThawFree Γ → Persistent Γ →
    SemSJ p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSJ p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

def BangThunkVRowTFJ (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxThawFree Γ → Persistent Γ →
    C.isRet = false → OwnHyg Δ Γ C → SemSJ p Δ Γ (.val (.lam N)) (.comp C) →
    SemSJ p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 at the revised W, at the contexts `CtxThawFree` admits.** -/
def Statement0UThawFreeJ (p : Placement) : Prop :=
  ThawInstJ (ℍ := ℍ) p ∧ CtxRelendsThawFreeJ (ℍ := ℍ) p ∧ ThunkFRowTFJ (ℍ := ℍ) p ∧
    ThunkVRowTFJ (ℍ := ℍ) p ∧ BangThunkFRowTFJ (ℍ := ℍ) p ∧ BangThunkVRowTFJ (ℍ := ℍ) p

end ProbeD1

end
