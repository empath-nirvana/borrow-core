import ProbeD1.GapRoom

/-!
# ProbeD1 — R1 and `binder0`'s monotonicity: the statements (`R1MONO.md`)

`R1MONO.md` is the design. This file holds its definitions and `def … : Prop` statements; the
proofs go in the files the design names.

* **§1 W reads `μ`, `fam` and type variables itself.** `vRLJ` hands a slot of `μ` or `fam` type to
  Core's relation whole, whose `U` clause inside is Core's and reads Core's `ℕ`-`∀`
  (`GAP.md` §4). `vRLM` is `vRLJ` with three clauses added, each Core's clause (`vCE`,
  `Core/Relation.lean`) at W's formers: a type variable reads its environment entry (`wEnvP`),
  `μX. A` is the least fixed point over W's own clauses (`NoMut`, `Cl`, the impredicative
  intersection), and `[L]` reads each leaf at W's relation. A leaf reads its type closed by the
  environment's types (`wClose`), as Core's `Imm` clause reads `tClose`. `vRLM p none` is W's
  relation; `vRLM p (some η)` is its reading under a type-variable environment, as `vCE (some η)`
  is `vC`'s. It replaces `vRLJ` as the one draft relation; `vRLJ` stays as the statement it was.
  The thaw is then by induction on the data (`RelendMValueE`), and `Statement0UFullM` is
  `Statement0UFullJ`'s statement at `vRLM`.
* **§2 Monotonicity at `binder0`**, restated at `vRLM` with the revised futures and the revised
  index (`MonoVM`, `MonoGM`, `MonoOwnGM`), the part `binder0` carries by construction
  (`MonoExtM`, `MonoOwnGUFreeM`, each the `none` instance of a statement under an environment,
  `MonoExtME`, `MonoOwnUFreeME`), and the configuration that pins the scope of the rest (`gd…`):
  a closure whose `U` clause holds at a stack because the guard keeps every argument above the
  innermost lend, and the own lend's push of a lend below it. `GdNotCore`: the closure is no Core
  value; `GdNotRecsInsideOwn`: its index is outside the arising set's record invariant. The
  consumer, `[allI]` at `SemSM` (`AllIRowM`), is the target; `MonoOwnGM` is one route to it. The
  test of the row itself at `gd` (`gdM`, `GdAllIConclAt`, `GdRowRefutation`), and the route at a
  restricted domain: each live slot also a Core value (`gRLMC`, `SemSMC`, `MonoOwnGMC`,
  `AllIRowMC`), which excludes `gd` (`GdCtxNotCore`); its arising form (`CtxArisesAt`,
  `MonoOwnGMA`); the two facts the restricted route reads at `⊸` (`WInsideCoreM`,
  `CoreInsideWM`).
* **§3 The three obligations the binder unit left.** `OuterBelowTop` at every lend, at the
  arising set (`OuterBelowTopArises`). `RetainedPay` row by row, at every payload type
  (`LeafPos`, `PayLeaves`, `RetainedPayViewRow`, `RetainedPayLoadMutRow`,
  `RetainedPayLoadImmRow`, `RetainedPayInstRow` at every instance with no join, the
  transports), the nested `Mut` leaf through the view's `TyEq` to its entry's payload type
  (`LeafPosTyEq`, `PayExtOfTyEq`, `PayLeavesOfTyEq`, `RetainedPayLoadMutBound`), the read-out
  rows' hypotheses met (`RetainedPayLoadMutRowMet`, `RetainedPayLoadImmRowMet`), and the arising
  check of a stop (`InternalLeafArises`, `ReadOutAtInternalPayload`). The slice rows at a family
  of two or more elements, outside W (`SliceGuardFails`; `RetainedPaySliceRow` vacuous at every
  count). The variant leaf a stop would call for (`PayLeavesAt`, `mutLeafP`, `immLeafP`,
  `VwPayLeaves`, `ThawLeafP`). `KeepsT` at the share in the form `RelendJ` consumes
  (`ShareKeepsT`), from the stop's and the resume's tagged worlds (`ResumeKeepsT`, `TagFixed`),
  the bridge to the instantiated list (`RelAbove`, `ExtKeepsTInst`), and the frames the premise
  names, kept apart from the ghost-ended ones (`RelFramesNotEnded`, `ShareKeepsTMet`).
* **§4 Statement 0 at `vRLM`** (`VRLMDataE`, `FutPartI`, `Statement0SharedM`, `ForceRowM`,
  `CallbackExtMutM`, `CallbackExtImmM`, `Statement0M`; at `binder0`, the facts beside
  monotonicity, the unrestricted monotonicity statements' negation, and statement 0 read at its
  consumers: `Statement0MBesideMono0`, `MonoUnrestrictedRefuted0`, `Statement0MAtConsumers0`).

Definitions and `def … : Prop` statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS stratS ReLend TabAtS jdgCty OpenS bodyS rowTab
  innerView)

/-! ### §1 W reads `μ`, `fam` and type variables itself -/

/-- **An entry of W's type-variable environment**: the closed type the variable stands for (W's
leaves read their type closed by it) and the candidate the variable is read at. A `μ` binds its
variable at the index it is read at, and W's formers that reach a variable (`⊗`, `⊕`, `!`,
`[@a]`, `Ref`, `[L]`, a nested `μ`) keep the index, so the candidate is a predicate on the value
and its resource there. -/
structure WEnt where
  ty : VTy
  P : Val → WProp

/-- The environment of a closed type: every variable is empty (`tEnv none`'s analog). -/
def wEnv : Option (Nat → WEnt) → Nat → WEnt
  | none => fun n => ⟨.tvar n, fun _ _ => False⟩
  | some η => η

/-- A variable's candidate (`tEnvP`'s analog). -/
def wEnvP : Option (Nat → WEnt) → Nat → Val → WProp
  | none, _, _ => fun _ => False
  | some η, n, v => (η n).P v

/-- The closed type a type stands for under the environment (`tClose`'s analog). -/
def wClose : Option (Nat → WEnt) → VTy → VTy
  | none, A => A
  | some η, A => A.subst (fun n => (η n).ty)

/-! #### The instances and the own lends W's `∀` clause reads (`NEXT.md` §3.1) -/

/-- **A lifetime in scope at a reading**: the value of one of its bindings. `∀E` instantiates at a
lifetime term, whose value below `⊤` is one of its variables' (`InScopeOfInterp`). -/
def InScope (s : LSub) (α : Life) : Prop := ∃ p ∈ s.entries, OrderDual.toDual p.2 = α

/-- **The own lend at `vRLM`**: `OwnPushI`, with its payload type reading only variables free in
the type (`payLocal`) and not the binder (`selfFree`). Each callback row takes `e.T = T`, the
argument's payload type, as a hypothesis, and the constant's side condition keeps the binder out
of `T` (`hfree₁`, (E4)). -/
def OwnPushM (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life) : Prop :=
  OwnPushI δ C ρ s e a ∧ (∀ y, VFree y e.T → CFree y C) ∧ ¬ VFree e.x e.T

/-- **`StackJ` at `vRLM`.** An entry of the third kind (the innermost, new to `Δ`, named by the
type's outermost `∀`) was pushed fresh below the reading (`SubFresh`), and no entry's payload type
reads its variable. No `binder0` clause produces such an entry. `cbpv`'s `U` own push at `vRLM`
(`RelendU`'s `OwnPush`) asks neither. -/
def StackJM (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  StackJ σ αs δ Δ Γ C ∧
    ∀ e ∈ σ, Δ.find? e.x = none → σ.head? = some e → (∃ c C', C = .all e.x c C') →
      (∀ a ∈ αs.head?, SubFresh δ a) ∧ ∀ e' ∈ σ, ¬ VFree e.x e'.T

/-! #### The persistence box -/

/-- **One step of the persistence box**, read at the reading `δ` and the list `ls`: an own push at
the empty resource (`OwnOKI`). The entry is under a name no program binds (`NsVar`), new to the
stack and to the reading, and not read by its own payload type; its lifetime is below the stack
and below `⊤`, and fresh below the records and the reading, as the `∀` clause's own lend is. -/
inductive BoxStep (δ : LSub) (ls : List SRec) : Stk → Stk → Prop
  | push {σ : LStack} {αs : List Life} (e : LEnt) (a : Life) :
      OwnOKI δ σ αs e a PMap.empty → a < ⊤ → NsVar e.x → δ.find? e.x = none →
      ¬ VFree e.x e.T → RecsOutside (a :: αs) ls → SubFresh δ a →
      BoxStep δ ls (σ, αs) (e :: σ, a :: αs)

/-- **The persistence box** of a `!` value at its type `A`. At a thunk type `U C`: every
instantiation of the stack, every list the instantiated lifetimes keep outside, and every finite
sequence of `BoxStep`s from the instantiated stack there. At any other type it asks nothing. A
persistent value holds nothing, so no part of it is lent and none is moved, and the box reads it at
every world the value can be carried to: a callback's own push, a resume's instantiation, a run's
list. -/
def PBox (A : VTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (P : LStack → LSub → List Life → List SRec → Prop) : Prop :=
  match A with
  | .thunk _ => ∀ ι : Inst, InstAt αs ι → ∀ ls' : List SRec, RecsOutside (ι.life αs) ls' →
      ∀ (σ' : LStack) (αs' : List Life),
        Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs') →
        P σ' (ι.sub δ) αs' ls'
  | _ => True

mutual
/-- **W's value relation, reading `μ`, `[L]` and type variables itself.** `vRLJ`'s clauses at
`U`, `⊗`, `⊕`, `[@a]`, `Ref`, `Mut`, `Imm` and the data leaves, the environment threaded
through W's formers and the leaves' types closed by it; Core's `vCE` clauses at `tvar`, `μ` and
`fam`, at W's relation. `X` never occurs under `U` (`VTy.subst` leaves `U C` alone) nor in a
`Mut` payload (`NoMut`); in an `Imm` payload it is read through the closed type, Core's `μ` at the
observable view, as every `Imm` payload is Core's at `vRLJ`. At `!` it is `vRLJ`'s clause with the
persistence box (`PBox`): a persistent thunk is read at every instantiation and every
reserved-name push. -/
def vRLM (p : Placement) :
    Option (Nat → WEnt) → LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | _, σ, δ, .thunk C, αs, ls, f =>
      guardPV (extS δ σ αs) σ αs ls
        (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRLM p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendJ δ σ (fun δ' αs' ls' => cRLM p σ δ' C αs' ls' (forceE C (.val f))) αs ls)
  | η, σ, δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLM p η σ δ A αs ls v₁ ⋆ vRLM p η σ δ B αs ls v₂
  | η, σ, δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLM p η σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLM p η σ δ B αs ls v₂)
  | η, σ, δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRLM p η σ δ A αs ls v ρ ∧
      PBox A δ σ αs (fun σ' δ' αs' ls' => vRLM p η σ' δ' A αs' ls' v PMap.empty)
  | η, σ, δ, .box a A, αs, ls, v =>
      atLife (extS δ σ αs) a fun α => box α (vRLM p η σ δ A αs ls v)
  | η, σ, δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLM p η σ δ A αs ls v'
  | η, σ, δ, .mut a T, αs, ls, v => fun ρ =>
      vC true (.mut a (wClose η T)) ls (extS δ σ αs) v ρ ∧
        CohS σ αs (extS δ σ αs) (.mut a (wClose η T)) v ρ ∧
        RetainedPay σ αs (extS δ σ αs) (wClose η T) v
  | η, σ, δ, .imm a T, αs, ls, v => fun ρ =>
      vC true (.imm a (wClose η T)) ls (extS δ σ αs) v ρ ∧
        CohS σ αs (extS δ σ αs) (.imm a (wClose η T)) v ρ ∧
        RetainedPay σ αs (extS δ σ αs) (wClose η T) v
  | η, _, _, .tvar n, _, _, v => wEnvP η n v
  | η, σ, δ, .mu A, αs, ls, v => fun ρ => VTy.NoMut 0 A ∧ (wClose η (.mu A)).Cl 0 ∧
      ∀ P : Val → WProp,
        (∀ v' ρ', vRLM p (some (VTy.scons ⟨wClose η (.mu A), P⟩ (wEnv η))) σ δ A αs ls v' ρ' →
          P v' ρ') → P v ρ
  | η, σ, δ, .fam L, αs, ls, v => ex fun ℓ => ex fun c =>
      ⌜v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31⌝ ⋆
        sepRange (fun m => vRLM p η σ δ L αs ls (.loc m)) ℓ c.toNat
  | _, σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ _ _ A => A
/-- **W's computation relation at `vRLM`**: `cRLJ`'s clauses, the answers at `vRLM p none`. A
`ν` computation is still read by Core's `cC` whole, as at `cRLJ`: values a `ν` unfolding gives
are Core's, with Core's `U` and `ℕ`-`∀` inside. -/
def cRLM (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  | σ, δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRLM p none σ δ B αs ls'' v
  | σ, δ, .eff n i q A B C, αs, ls, e =>
      if p.shareFut then
        bodySF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRetM p σ' δ C αs' ls v)
          (OpenSF true δ (rowTab n i q A B C δ) (fun σ' αs' ls v => effRetM p σ' δ C αs' ls v))
          σ αs ls e
      else
        bodyS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetM p σ δ C αs' ls v)
          (OpenS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetM p σ δ C αs' ls v)) αs ls e
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.arr A C) σ σ' → ∀ v,
          (vRLM p none σ' δ A αs' ls' v ─⋆
            guardPV (extS δ σ' αs') σ' αs' ls' (cRLM p σ' δ C αs' ls' (.app e (.val v)))) ρ
  | σ, δ, .amp C D, αs, ls, e => fun ρ =>
      cRLM p σ δ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLM p σ δ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | _, _, .top, _, _, _ => fun _ => True
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ ls' σ' αs', ExtQ p.bindFut ls ls' ρ → FutQI p.bindFut δ ρ (σ, αs) (σ', αs') →
        FutAvoids (.all x c C) σ σ' →
        (∀ α, (⌜LtLife (extS δ σ' αs') c α ∧ InScope (extS δ σ' αs') α⌝ ─⋆
          guardPV (extS (δ.extend x α) σ' αs') σ' αs' ls'
            (cRLM p σ' (δ.extend x α) C αs' ls' (.app e (.val .unit)))) ρ) ∧
        (p.allOwn = true → ∀ (en : LEnt) (α : Life), OwnPushM δ (.all x c C) ρ (σ', αs') en α →
          RecsOutside (α :: αs') ls' → SubFresh δ α →
          guardPV (extS (δ.extend x α) (en :: σ') (α :: αs')) (en :: σ') (α :: αs') ls'
            (cRLM p (en :: σ') (δ.extend x α) C (α :: αs') ls' (.app e (.val .unit))) ρ)
  | σ, δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
termination_by structural _ _ C => C
/-- The answer relation of `F_Σ R`: `vRLM R`. -/
def effRetM (p : Placement) : LStack → LSub → CTy → List Life → List SRec → Val → WProp
  | σ, δ, .ret A, αs => fun ls v => vRLM p none σ δ A αs ls v
  | σ, δ, .eff _ _ _ _ _ C, αs => effRetM p σ δ C αs
  | _, _, _, _ => fun _ _ _ => False
termination_by structural _ _ C => C
end

/-- `⊛_{x ∈ dom(Γ)} vRLM(Γ(x))`. -/
def gSepRLM (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then vRLM p none σ δ s.ty αs ls v ⋆ gSepRLM p σ δ αs ls Γ γ
      else gSepRLM p σ δ αs ls Γ γ

/-- `𝒢⟦Γ⟧` at `vRLM`. -/
def gRLM (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLM p σ δ αs ls Γ γ

/-- **The semantic judgement at `vRLM`**: `SemSJ` with `vRLM`'s context and computation, its stack
admitted by `StackJM`. -/
def SemSM (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → StackJM σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ →
    Δ.Models (extS δ σ αs) → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLM p σ δ αs ls Γ γ ρ →
    cRLM p σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-! #### Where `vRLM` is `vRLJ` -/

mutual
/-- No `μ`, `[L]` or type variable at any depth, inside computation types included; a `Mut` or
`Imm` leaf's payload is Core's at both relations. -/
def VMuFree : VTy → Prop
  | .mu _ => False
  | .fam _ => False
  | .tvar _ => False
  | .thunk C => CMuFree C
  | .tensor A B => VMuFree A ∧ VMuFree B
  | .sum A B => VMuFree A ∧ VMuFree B
  | .bang A => VMuFree A
  | .box _ A => VMuFree A
  | .ref A => VMuFree A
  | _ => True
def CMuFree : CTy → Prop
  | .ret A => VMuFree A
  | .arr A C => VMuFree A ∧ CMuFree C
  | .amp C D => CMuFree C ∧ CMuFree D
  | .top => True
  | .all _ _ C => CMuFree C
  | .nu _ => True
  | .eff _ _ _ _ _ C => CMuFree C
end

mutual
/-- No lifetime `∀` at any depth, outside a `Mut` or `Imm` payload and outside `ν`. Both relations
read those with Core's relation. -/
def VAllFree : VTy → Prop
  | .thunk C => CAllFree C
  | .tensor A B => VAllFree A ∧ VAllFree B
  | .sum A B => VAllFree A ∧ VAllFree B
  | .bang A => VAllFree A
  | .box _ A => VAllFree A
  | .ref A => VAllFree A
  | .mu A => VAllFree A
  | .fam A => VAllFree A
  | _ => True
/-- The same at a computation type. An effect layer's operation types are read by Core's relation
(`rowTab`), so only its answer type counts. -/
def CAllFree : CTy → Prop
  | .ret A => VAllFree A
  | .arr A C => VAllFree A ∧ CAllFree C
  | .amp C D => CAllFree C ∧ CAllFree D
  | .top => True
  | .all _ _ _ => False
  | .nu _ => True
  | .eff _ _ _ _ _ C => CAllFree C
end

mutual
/-- No persistent thunk (`!U C`) at any depth, outside a `Mut` or `Imm` payload and outside `ν`:
there `vRLM`'s `!` clause reads the persistence box (`PBox`), and `vRLJ`'s does not. -/
def VBoxFree : VTy → Prop
  | .thunk C => CBoxFree C
  | .tensor A B => VBoxFree A ∧ VBoxFree B
  | .sum A B => VBoxFree A ∧ VBoxFree B
  | .bang A => (∀ C, A ≠ .thunk C) ∧ VBoxFree A
  | .box _ A => VBoxFree A
  | .ref A => VBoxFree A
  | .mu A => VBoxFree A
  | .fam A => VBoxFree A
  | _ => True
/-- The same at a computation type. -/
def CBoxFree : CTy → Prop
  | .ret A => VBoxFree A
  | .arr A C => VBoxFree A ∧ CBoxFree C
  | .amp C D => CBoxFree C ∧ CBoxFree D
  | .top => True
  | .all _ _ C => CBoxFree C
  | .nu _ => True
  | .eff _ _ _ _ _ C => CBoxFree C
end

/-- **`vRLM` is `vRLJ` where neither reads a `μ`, a `[L]`, a type variable, a lifetime `∀` or a
persistent thunk.** `vRLM`'s `∀` clause reads the instances in scope and the own lends at
`OwnPushM` (`NEXT.md` (E1), (E2)), and its `!` clause the persistence box; `vRLJ` keeps the old
clauses. Proved without `VAllFree` at commit `5210cf1`, before the edits, and without `VBoxFree`
before the box. -/
def RelMAgreesJ : Prop :=
  (∀ (p : Placement) (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec)
      (v : Val), VMuFree A → VAllFree A → VBoxFree A →
      vRLM (ℍ := ℍ) p none σ δ A αs ls v = vRLJ (ℍ := ℍ) p σ δ A αs ls v) ∧
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec)
    (e : Expr), CMuFree C → CAllFree C → CBoxFree C →
      cRLM (ℍ := ℍ) p σ δ C αs ls e = cRLJ (ℍ := ℍ) p σ δ C αs ls e

/-! #### The fixed point's facts -/

/-- **Monotone in a variable outside every `Mut` payload** (`vCE_mono_at`'s analog). -/
def VRLMMonoAt : Prop :=
  ∀ (p : Placement) (A : VTy) (k : Nat) (η₁ η₂ : Nat → WEnt), A.NoMut k →
    (∀ n, (η₁ n).ty = (η₂ n).ty) → (∀ n, n ≠ k → η₁ n = η₂ n) →
    (∀ v ρ, (η₁ k).P v ρ → (η₂ k).P v ρ) →
    ∀ σ δ αs ls v ρ, vRLM (ℍ := ℍ) p (some η₁) σ δ A αs ls v ρ →
      vRLM (ℍ := ℍ) p (some η₂) σ δ A αs ls v ρ

/-- **`roll`** (`vC_roll`'s analog): the body, its variable read at the `μ` itself, is the `μ`. -/
def VRLMRoll : Prop :=
  ∀ (p : Placement) (η : Option (Nat → WEnt)) (A : VTy) (σ : LStack) (δ : LSub)
    (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    A.NoMut 0 → (wClose η (.mu A)).Cl 0 →
    vRLM (ℍ := ℍ) p (some (VTy.scons ⟨wClose η (.mu A), vRLM p η σ δ (.mu A) αs ls⟩ (wEnv η)))
      σ δ A αs ls v ρ →
    vRLM (ℍ := ℍ) p η σ δ (.mu A) αs ls v ρ

/-- **The unroll equation** (`vC_mu_iff`'s analog), at a closed `μ`. -/
def VRLMUnroll : Prop :=
  ∀ (p : Placement) (A : VTy) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (v : Val) (ρ : WRes),
    vRLM (ℍ := ℍ) p none σ δ (.mu A) αs ls v ρ ↔
      A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vRLM (ℍ := ℍ) p none σ δ (VTy.inst (.mu A) A) αs ls v ρ

/-! #### The thaw, by induction on the data -/

/-- **The environment thaws**: its types do not depend on the index, and each variable's
candidate at the old index gives, under the guard, the clause over instantiations of the entry
the family hands at each instantiated index. -/
def EnvThaws (η : Option (Nat → WEnt)) (ηf : LSub → List Life → List SRec → Option (Nat → WEnt))
    (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) : Prop :=
  (∀ δ' αs' ls' n, (wEnv (ηf δ' αs' ls') n).ty = (wEnv η n).ty) ∧
  ∀ n v ρ, TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → wEnvP η n v ρ →
    RelendJ δ σ (fun δ' αs' ls' => wEnvP (ηf δ' αs' ls') n v) αs ls ρ

/-- **The thaw of a value at every type, under a thawing environment**: the induction the `μ`
case closes by its own fixed point. -/
def RelendMValueE : Prop :=
  ∀ (A : VTy) (η : Option (Nat → WEnt))
    (ηf : LSub → List Life → List SRec → Option (Nat → WEnt))
    (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    EnvThaws η ηf δ σ αs ls → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLM (ℍ := ℍ) .binder0 η σ δ A αs ls v ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLM (ℍ := ℍ) .binder0 (ηf δ' αs' ls') σ δ' A αs' ls' v) αs ls ρ

/-- **The thaw of a value at every type** (`RelendJValueK` with `ThawFreeK` dropped). -/
def RelendMValue : Prop :=
  ∀ (A : VTy) (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLM (ℍ := ℍ) .binder0 none σ δ A αs ls v ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLM (ℍ := ℍ) .binder0 none σ δ' A αs' ls' v) αs ls ρ

/-- **The context's thaw over instantiations**, at `vRLM`. -/
def CtxRelendableAtM (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → SubDom δ Δ → Δ.Models (extS δ σ αs) →
    RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ →
    RelendJ δ σ (fun δ' αs' ls' => gRLM (ℍ := ℍ) p σ δ' αs' ls' Γ γ) αs ls ρ

def CtxRelendsAllM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), CtxRelendableAtM (ℍ := ℍ) p Δ Γ

/-- **A `U` value instantiated is a `U` value at the instantiation**, at `vRLM`. -/
def ThawInstM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLM (ℍ := ℍ) p none σ δ (.thunk C) αs ls f ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLM (ℍ := ℍ) p none σ δ' (.thunk C) αs' ls' f) αs ls ρ

/-- A value type that reaches no `U` through the formers W reads itself (`UFree` at `vRLM`). -/
def UFreeM : VTy → Prop
  | .thunk _ => False
  | .tensor A B => UFreeM A ∧ UFreeM B
  | .sum A B => UFreeM A ∧ UFreeM B
  | .bang A => UFreeM A
  | .box _ A => UFreeM A
  | .ref A => UFreeM A
  | .mu A => UFreeM A
  | .fam L => UFreeM L
  | _ => True

/-- **A persistent context the persistence box carries**: every live slot is a persistent thunk
`!U C` (`PBox` reads it at every instantiation and every reserved-name push) or persistent data
reaching no `U` (carried by its clauses' shape). The values the rules make persistent are thunks (`bangThunkF`,
`bangThunkV`, a host operation's `!(A ⊸ B)`); a slot of persistent data reaching a `U` not itself
under a `!`, such as `!(U C ⊗ 1)`, is the case left out. -/
def PersistentBoxed (Γ : Ctx VTy) : Prop :=
  ∀ s ∈ Γ, s.live = true → ∃ B, s.ty = .bang B ∧ ((∃ C, B = .thunk C) ∨ UFreeM B)

def ThunkFRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy),
    SemSM (ℍ := ℍ) p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.val (.thunk (.ret A)))

def ThunkVRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), C.isRet = false → OwnHyg Δ Γ C →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.comp C) →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.val (.thunk C))

/-- **`!U` of `F A` at `vRLM`**, the context persistent and carried by the box (`PersistentBoxed`,
added with the box). -/
def BangThunkFRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), Persistent Γ → PersistentBoxed Γ →
    SemSM (ℍ := ℍ) p Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A))))

/-- **`!U C` at `vRLM`**, the context persistent and carried by the box. -/
def BangThunkVRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), Persistent Γ → PersistentBoxed Γ →
    C.isRet = false →
    OwnHyg Δ Γ C → SemSM (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.comp C) →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

/-- **The `U` side of statement 0 at `vRLM`, the thaw at every context**: `Statement0UFullJ`'s
statement at the relation that reads `μ` and `fam` itself. -/
def Statement0UFullM (p : Placement) : Prop :=
  ThawInstM (ℍ := ℍ) p ∧ CtxRelendsAllM (ℍ := ℍ) p ∧ ThunkFRowM (ℍ := ℍ) p ∧
    ThunkVRowM (ℍ := ℍ) p ∧ BangThunkFRowM (ℍ := ℍ) p ∧ BangThunkVRowM (ℍ := ℍ) p

/-- **`GAP.md` §4's `μ` slot at W's own `μ`**: the closure `Λ. return ℓ₀`, which Core's `μ`
clause admits there by adjacency, is no `vRLM` value. Proved of `vRLM` at commit `5210cf1`
(`muAdjNotVRLM`), before (E1) restricted the `∀` clause's first conjunct to the instances in
scope; that proof is withdrawn, and `MuAdjVRLME1` (`Nx.lean`) decides the statement after (E1). -/
def MuAdjNotVRLM : Prop :=
  ¬ vRLM (ℍ := ℍ) .binder0 none [muEnt] adjδ muAdjTy [lifeN 1] [] (Val.lam (.val (Val.loc 0)))
      (innerView 0 (lifeN 1))

/-- **A `μ` value with a lend open arises** (the template of R1's arising check): the
configuration of the revised arising set and the value arising there at the `μ` type. -/
def MuSlotArises (A : VTy) : Prop :=
  ∃ (c : Cfg) (v : Val), ArisesI (ℍ := ℍ) c ∧ c.σ ≠ [] ∧ ArisesVI (ℍ := ℍ) c v (.mu A)

/-! ### §2 Monotonicity at `binder0` -/

/-- **A future's inserted lifetimes are fresh below the records and the reading**, as a lend's
are ([TR] 6.64's and 6.65's H4): `RecsOutside` at the new vector, and every inserted lifetime
below the reading (`SubFresh`). -/
def InsertedFresh (δ : LSub) (ls : List SRec) (αs αs' : List Life) : Prop :=
  RecsOutside αs' ls ∧ ∀ a ∈ αs', a ∉ αs → SubFresh δ a

/-- **Values along W's order, at `vRLM`**: statement 0's `MonoV` with the revised futures
(`FutI`), the revised index (`OuterBelowTop`, `RecsOutside`, `SubOutside`, `PlaceViewsL`), the
extension keeping the tags (`KeepsT`) and the inserted lifetimes fresh (`InsertedFresh`). -/
def MonoVM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes)
    (σ' : LStack) (αs' : List Life),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    Ext ls ls' ρ → KeepsT ls ls' ρ → FutI δ ρ (σ, αs) (σ', αs') → InsertedFresh δ ls' αs αs' →
    FutAvoidsV A σ σ' → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p none σ' δ A αs' ls' v ρ

/-- **Contexts along W's order, at `vRLM`.** -/
def MonoGM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls ls' : List SRec)
    (ρ : WRes) (σ' : LStack) (αs' : List Life),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    Ext ls ls' ρ → KeepsT ls ls' ρ → FutI δ ρ (σ, αs) (σ', αs') → InsertedFresh δ ls' αs αs' →
    (∀ s ∈ Γ, s.live = true → FutAvoidsV s.ty σ σ') →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p σ' δ αs' ls' Γ γ ρ

/-- **Contexts across the callback's own lend, at `vRLM`**: statement 0's `MonoOwnG` with the
revised own lend (`OwnPushI`) and the freshness the `∀` clause's own-lend conjunct carries
(`RecsOutside (a :: αs) ls`, `SubFresh δ a`). -/
def MonoOwnGM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-- `MonoOwnGM` is `MonoGM`'s instance at the one-step future the push is. -/
def MonoOwnGMOfMonoGM : Prop := ∀ p : Placement, MonoGM (ℍ := ℍ) p → MonoOwnGM (ℍ := ℍ) p

/-- `MonoGM` follows from `MonoVM`, slot by slot. -/
def MonoGMOfMonoVM : Prop := ∀ p : Placement, MonoVM (ℍ := ℍ) p → MonoGM (ℍ := ℍ) p

/-- **The record half, by construction**: the same stack, an extension keeping the tags. -/
def MonoExtM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls ls' : List SRec) (v : Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → RecsOutside αs ls' →
    Ext ls ls' ρ → KeepsT ls ls' ρ → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p none σ δ A αs ls' v ρ

/-- **`MonoOwnGM` at a context whose live slots reach no `U`** (`monoOwnG_uFree` at `vRLM`). -/
def MonoOwnGUFreeM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    (∀ s ∈ Γ, s.live = true → UFreeM s.ty) →
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-! #### The two by-construction facts under an environment

`vRLM`'s `μ` candidate is a predicate at one index, so carrying a `μ` value to another list or
another stack is an induction on the data whose hypothesis is on the environment, as the thaw's
is (`EnvThaws`, `RelendMValueE`). The `none` forms are the instances at `none`. -/

/-- **The environment moves along the record order**: its types are fixed, and each candidate at
`ls` gives the one at `ls'` under the extension, the tags kept and the guard at the index. -/
def EnvExt (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls ls' : List SRec) : Prop :=
  (∀ n, (wEnv η' n).ty = (wEnv η n).ty) ∧
  ∀ n v ρ, Ext ls ls' ρ → KeepsT ls ls' ρ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → wEnvP η n v ρ → wEnvP η' n v ρ

/-- **`MonoExtM` under an environment.** -/
def MonoExtME (p : Placement) : Prop :=
  ∀ (A : VTy) (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls ls' : List SRec) (v : Val) (ρ : WRes),
    EnvExt η η' σ δ αs ls ls' → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    RecsOutside αs ls' → Ext ls ls' ρ → KeepsT ls ls' ρ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p η' σ δ A αs ls' v ρ

/-- `EnvExt` holds at `none`: the types are `.tvar n` on both sides and `wEnvP none` is `False`. -/
def EnvExtNone : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls ls' : List SRec),
    EnvExt none none σ δ αs ls ls'

/-- `MonoExtM` is `MonoExtME` at `none`. -/
def MonoExtMOfE : Prop := ∀ p : Placement, MonoExtME (ℍ := ℍ) p → MonoExtM (ℍ := ℍ) p

/-- **The environment moves across the own push**: its types are fixed and free of the pushed
variable, and each candidate at the stack gives the one at the pushed stack, under the guard, the
pushed place free and the resource above the pushed lend. -/
def EnvPush (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) (e : LEnt) (a : Life) : Prop :=
  (∀ n, (wEnv η' n).ty = (wEnv η n).ty) ∧ (∀ n, ¬ VFree e.x (wEnv η n).ty) ∧
  ∀ n v ρ, TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → (∀ ψ, ¬ DeepAt ρ e.l ψ) →
    ρ.InStratum a → wEnvP η n v ρ → wEnvP η' n v ρ

/-- **`MonoOwnGUFreeM` at one value, under an environment.** -/
def MonoOwnUFreeME (p : Placement) : Prop :=
  ∀ (A : VTy) (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) (v : Val) (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    UFreeM A → EnvPush η η' σ δ αs ls e a → StackOK σ αs → OuterBelowTop αs →
    RecsOutside αs ls → SubOutside σ αs δ → OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none →
    ¬ VFree e.x A → e.x ∉ VTy.binders A → RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ → vRLM (ℍ := ℍ) p η' (e :: σ) δ A (a :: αs) ls v ρ

/-- `EnvPush` holds at `none`. -/
def EnvPushNone : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (e : LEnt) (a : Life),
    EnvPush none none σ δ αs ls e a

/-- `MonoOwnGUFreeM` is `MonoOwnUFreeME` at `none`, slot by slot: the own lend's facts hold at a
part of the context's resource (`OwnOKI`'s fields and `placeFree` restrict to parts). -/
def MonoOwnGUFreeMOfE : Prop :=
  ∀ p : Placement, MonoOwnUFreeME (ℍ := ℍ) p → MonoOwnGUFreeM (ℍ := ℍ) p

/-! #### The test configuration: a closure whose `U` clause rests on the guard -/

/-- `U(F 1)`. -/
abbrev gdArg : VTy := .thunk (.ret .unit)

/-- `U(F 1) ⊸ F ([@'1] U(F 1))`. -/
abbrev gdC : CTy := .arr gdArg (.ret (.box (.var 1) gdArg))

abbrev gdTy : VTy := .thunk gdC

/-- `λg. return g`. -/
abbrev gdF : Val := Val.lam (.var 0)

/-- The outer lend: place `10`, variable `'0`, payload `1`, a 6.65 entry. -/
abbrev gdX : LEnt := ⟨10, 0, .unit, .mut, fun _ => true⟩

/-- The lend the callback type `gdCy`'s own lend pushes: place `11`, variable `'2`, payload `1`,
a 6.64 entry. -/
abbrev gdY : LEnt := ⟨11, 2, .unit, .imm .unit, fun _ => true⟩

abbrev gdσ : LStack := [gdX]

abbrev gdαs : List Life := [lifeN 2]

/-- `'0 ↦ 2`, then `'1 ↦ 3`: the outer `∀'0`'s own lend binds `'0` at its lend lifetime, as at
`GdReached`'s reading, and `'1` is read at `↓2`, the lifetime just below the outer lend, so the
table's first conjunct at `gdσ` is the box at `'1`. -/
abbrev gdδ : LSub := ⟨[(1, 3), (0, 2)]⟩

/-- `'0 ⊏ ⊤, '1 ⊏ '0` (`mΔ`): the lifetime context of the judgement whose `∀I` row reads
`MonoOwnGM` at `gdΓ`. -/
abbrev gdΔ : LifeCtx := (LifeCtx.empty.extend 0 .top).extend 1 (.var 0)

abbrev gdΓ : Ctx VTy := [⟨gdTy, true⟩]

abbrev gdγ : List Val := [gdF]

/-- `∀'2 ⊏ '1. Imm '2 1 ⊸ F 1`: its own lend pushes `gdY` at `4`, below `'1`. -/
abbrev gdCy : CTy := .all 2 (.var 1) (.arr (.imm (.var 2) .unit) (.ret .unit))

/-- The 6.64 record of `gdY`'s view, at its frame lifetime `4`. -/
abbrev gdRec : FrameRec := ⟨11, Val.unit, PMap.empty, .unit, ⟨[]⟩⟩

abbrev gdls : List SRec := [(gdRec, lifeN 4)]

/-- `λ_. load ℓ₁₁`: a thunk of `F 1` that reads its view ([TR] 6.144). -/
abbrev gdG : Val := Val.lam (.app (.val (.prim .load)) (.val (.loc 11)))

/-- **The configuration meets `MonoOwnGM`'s hypotheses** at `gdΓ`, the own lend of `gdCy`, and
what the consumer has beside them: `SemSM`'s index at the judgement `gdΔ; gdΓ ⊢ _ : gdCy` that the
`∀I` row at `binder0` reads (binder hygiene, scoping, the stack admitted, the reading's domain and
`gdΔ`'s models at the stack's reading). -/
def GdIndex : Prop :=
  StackOK gdσ gdαs ∧ OuterBelowTop gdαs ∧ RecsOutside gdαs gdls ∧ SubOutside gdσ gdαs gdδ ∧
    OwnPushI gdδ gdCy PMap.empty (gdσ, gdαs) gdY (lifeN 4) ∧ gdδ.find? gdY.x = none ∧
    CtxFresh gdY.x gdΓ ∧ RecsOutside (lifeN 4 :: gdαs) gdls ∧ SubFresh gdδ (lifeN 4) ∧
    TabAtS gdσ gdαs PMap.empty ∧ PlaceViewsL (extS gdδ gdσ gdαs) gdσ gdαs gdls PMap.empty ∧
    BindersLow gdΓ gdCy ∧ Scoped gdΔ gdΓ gdCy ∧ StackJ gdσ gdαs gdδ gdΔ gdΓ gdCy ∧
    SubDom gdδ gdΔ ∧ gdΔ.Models (extS gdδ gdσ gdαs)

/-- **The closure is a W value at `gdσ`**: the guard puts every argument's cells at or above the
outer lend, so above `'1`. -/
def GdRelated : Prop := gRLM (ℍ := ℍ) .binder0 gdσ gdδ gdαs gdls gdΓ gdγ PMap.empty

/-- **The closure is no W value after the own lend's push**: an argument holding the pushed
lend's view, at `4`, is returned boxed at `'1 ↦ 3`. -/
def GdNotPushed : Prop :=
  ¬ gRLM (ℍ := ℍ) .binder0 (gdY :: gdσ) gdδ (lifeN 4 :: gdαs) gdls gdΓ gdγ PMap.empty

/-- **`MonoOwnGM` at `binder0` is refuted** (`GdIndex`, `GdRelated`, `GdNotPushed`): a
refutation of ProbeD1's draft statement at a configuration not shown to arise, whose index is
outside the arising set's record invariant (`GdNotRecsInsideOwn`). It pins the scope of the
restriction `MonoOwnGMC` adds (`GdCtxNotCore`). It does not refute the lemma's consumer
`AllIRowM .binder0`. -/
def NotMonoOwnGM0 : Prop := ¬ MonoOwnGM (ℍ := ℍ) .binder0

/-- **The closure is no Core value** at the reading `gdδ`, the empty resource and every list. At
the empty resource every list extends every list, and at `gdls` the argument `gdG` over `gdY`'s
cell at `4` is returned boxed at `'1 ↦ 3`, which the run's end does not meet, as in
`GdNotPushed`'s run. -/
def GdNotCore : Prop := ∀ ls : List SRec, ¬ vC true gdTy ls gdδ gdF PMap.empty

/-- **The arising check, at the whole configuration**: the closure arises at its type at a
configuration of the revised arising set with `gd`'s stack, lifetimes and list. -/
def GdArises : Prop :=
  ∃ c : Cfg, ArisesI (ℍ := ℍ) c ∧ c.σ = gdσ ∧ c.αs = gdαs ∧ c.ls = gdls ∧
    ArisesVI (ℍ := ℍ) c gdF gdTy

/-- **`gd`'s index is outside the record invariant**: `gdRec` sits at `4`, at or below the
outermost lend `2`, and `gdσ` has no 6.64 entry whose record's lineage holds it. The list holds
`gdRec` before the push because `MonoOwnGM`, like the `∀` clause's own-lend conjunct at `binder0`,
keeps the list across a 6.64 own lend, while the lend itself extends it (`CallbackExtImmM`'s
`ls'`). -/
def GdNotRecsInsideOwn : Prop := ¬ RecsInsideOwn gdσ gdαs gdls

/-- **A configuration of the revised arising set with `gd`'s index.** -/
def GdIdxArises : Prop :=
  ∃ c : Cfg, ArisesI (ℍ := ℍ) c ∧ c.σ = gdσ ∧ c.αs = gdαs ∧ c.ls = gdls

/-- **No configuration of the set has `gd`'s index, once the record invariant arises**
(`RecsInsideOwnArises`, stated in `Binder.lean`, not attempted). -/
def GdIdxNotArisesOf : Prop := RecsInsideOwnArises (ℍ := ℍ) → ¬ GdIdxArises (ℍ := ℍ)

/-- **The failure is `binder0`'s own**: at `cbpv` the `U` clause owes the body at the push, a
future of `gdσ`, so the closure is no `U` value there to begin with. -/
def GdNotCbpv : Prop :=
  ¬ vRLM (ℍ := ℍ) .cbpv none gdσ gdδ gdTy gdαs gdls gdF PMap.empty

/-! #### The consumer: `[allI]` at `binder0`

At `binder0` the `∀` clause's own-lend conjunct asks the body at the pushed stack, and the row
carries its context there. `MonoOwnGM` is the lemma statement 0 planned for that step, and this
row is its only consumer at `binder0`. -/

/-- **`[allI]` at `SemSM`** (`AllIRow`'s statement at the revised relation): the target at
`binder0`. `NotMonoOwnGM0` refutes a lemma for it, not the row. -/
def AllIRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemSM (ℍ := ℍ) p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemSM (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.comp (.all x b C))

/-- **The route statement 0 planned for the row**: the `∀` clause's first conjunct from the
premise at the extended reading, its own-lend conjunct from the premise at the pushed index with
the context carried there by `MonoOwnGM`. At `binder0` it is closed by `NotMonoOwnGM0`. -/
def AllIRowMOfMonoOwnGM : Prop := ∀ p : Placement, MonoOwnGM (ℍ := ℍ) p → AllIRowM (ℍ := ℍ) p

/-! #### The row itself at `gd` -/

/-- `Imm '2 1 ⊸ F 1`, `gdCy`'s body. -/
abbrev gdCyBody : CTy := .arr (.imm (.var 2) .unit) (.ret .unit)

/-- **A body that exercises the closure where `GdNotPushed` fails it**: `λr. let g = f (thunk (load
r)) in force g`, at the premise's context `_ : S, f : gdTy` (`r` is `0`, the dead slot `1`, `f`
is `2`). It hands `f` a thunk holding the view the own lend pushes, and forces what comes back. -/
abbrev gdM : Expr :=
  .lam (elet (.app (.var 2) (.lam (.app (.val (.prim .load)) (.var 1))))
    (.app (.var 0) (.val .unit)))

/-- **`gdM` is derivable at the premise's judgement**: `load` at `Imm '2 1`, the thunk, `f` forced
and applied, the answer unboxed (`boxE`) and forced. -/
def GdMDerivable : Prop :=
  ProbeRules (gdΔ.extend 2 (.var 1)) (⟨.unit, false⟩ :: gdΓ) gdM (.comp gdCyBody)

/-- **The row's conclusion at `gd`'s index, at the body `M`.** -/
def GdAllIConclAt (M : Expr) : Prop :=
  cRLM (ℍ := ℍ) .binder0 gdσ gdδ gdCy gdαs gdls (substAll gdγ (.val (.lam M))) PMap.empty

/-- **At the body that exercises the closure the conclusion holds**: `gdF` hands back its argument,
the unboxed thunk loads through the view ([TR] 6.144), and the answer `()` holds nothing. -/
def GdAllIHoldsAtM : Prop := GdAllIConclAt (ℍ := ℍ) gdM

/-- **The conclusion at `gd` at every derivable body.** No route is known: a fundamental lemma
reaches a captured value through a relation it is in, and `gdF` is a value of neither W's relation
at the pushed index (`GdNotPushed`) nor Core's (`GdNotCore`). -/
def GdAllIHoldsDerivable : Prop :=
  ∀ (S : VTy) (M : Expr),
    ProbeRules (gdΔ.extend 2 (.var 1)) (⟨S, false⟩ :: gdΓ) M (.comp gdCyBody) →
    GdAllIConclAt (ℍ := ℍ) M

/-- **A body refuting the row at `gd`**: one meeting the row's premise whose conclusion fails at
`gd`'s index. -/
def GdAllIRowRefutes : Prop :=
  ∃ (S : VTy) (M : Expr),
    SemSM (ℍ := ℍ) .binder0 (gdΔ.extend 2 (.var 1)) (⟨S, false⟩ :: gdΓ) M (.comp gdCyBody) ∧
      ¬ GdAllIConclAt (ℍ := ℍ) M

/-- **Such a body refutes the row**: `gd`'s index meets the hypotheses of the row's conclusion at
`gdΔ; gdΓ ⊢ Λ. M : gdCy`. -/
def GdRowRefutation : Prop :=
  GdIndex → GdRelated (ℍ := ℍ) → GdAllIRowRefutes (ℍ := ℍ) → ¬ AllIRowM (ℍ := ℍ) .binder0

/-! #### The route at a restricted domain: each live slot also a Core value

The restriction is the added hypothesis; `gd` pins its scope (`NotMonoOwnGM0` without it,
`GdCtxNotCore` with it). Core's relation is the kernel's `vC`, read at the stack's reading as a
plain substitution; W's clauses are unchanged. -/

/-- **A context whose live slots are each W's and Core's**, on the slot's own part of the
resource, Core's read at the stack's reading. -/
def gSepRLMC (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then
        (fun ρ => vRLM p none σ δ s.ty αs ls v ρ ∧ vC true s.ty ls (extS δ σ αs) v ρ) ⋆
          gSepRLMC p σ δ αs ls Γ γ
      else gSepRLMC p σ δ αs ls Γ γ

/-- `𝒢⟦Γ⟧` at the restriction. -/
def gRLMC (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLMC p σ δ αs ls Γ γ

/-- **`SemSM` at the restriction**: the domain the `∀I` row would read for `MonoOwnGMC`'s
hypothesis at its conclusion's index. Its conclusion is `cRLM`'s alone; a row that binds a value
(`[let]`, `⊗E`, `⊕E`) would need the bound value Core's as well, which this judgement does not
give. -/
def SemSMC (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ →
    Δ.Models (extS δ σ αs) → RecsOutside αs ls → SubOutside σ αs δ → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gRLMC p σ δ αs ls Γ γ ρ →
    cRLM p σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-- **`MonoOwnGM` at the restriction.** The Core half moves by locality: the pushed variable is
free in no live type (`CtxFresh`), and the two readings agree elsewhere. -/
def MonoOwnGMC (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    gRLMC p σ δ αs ls Γ γ ρ → gRLMC p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-- **`[allI]` at `SemSMC`.** -/
def AllIRowMC (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) →
    SemSMC (ℍ := ℍ) p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemSMC (ℍ := ℍ) p Δ Γ (.val (.lam M)) (.comp (.all x b C))

/-- **The row at the restriction from the lemma at the restriction**: `AllIRowMOfMonoOwnGM`'s
argument, the restriction carried to the pushed index by `MonoOwnGMC`. -/
def AllIRowMCOfMonoOwnGMC : Prop :=
  ∀ p : Placement, MonoOwnGMC (ℍ := ℍ) p → AllIRowMC (ℍ := ℍ) p

/-- **`gd` is outside the restriction**: its one live slot's Core half fails (`GdNotCore`). -/
def GdCtxNotCore : Prop := ¬ gRLMC (ℍ := ℍ) .binder0 gdσ gdδ gdαs gdls gdΓ gdγ PMap.empty

/-- `λg. g (); λ_. ()`: forces its argument, then answers a thunk holding nothing. -/
abbrev gdF₀ : Val := Val.lam (.seq (.app (.var 0) (.val .unit)) (.val (Val.lam .unit)))

/-- **The restriction is met at `gd`'s index by a closure at `gdTy`**: `gdF₀` is W's and Core's
there, so `MonoOwnGMC`'s hypotheses hold at `gd`'s index with a `U` slot. -/
def GdRestrictedMet : Prop :=
  gRLMC (ℍ := ℍ) .binder0 gdσ gdδ gdαs gdls gdΓ [gdF₀] PMap.empty

/-- **W inside Core at a stack** (`NilSoundV` at every stack, at `vRLM`): the step the restricted
route at `⊸` takes to apply a slot's Core clause to an argument W relates at the pushed stack. -/
def WInsideCoreM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    StackOK σ αs → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vC true A ls (extS δ σ αs) v ρ

/-- **Core inside W at a stack** (`NilAgrees`' other half at every stack, at `vRLM`): the step the
restricted route at `⊸` takes to read the application's answer at W. -/
def CoreInsideWM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vC true A ls (extS δ σ αs) v ρ → vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ

/-- **A context arising at the index**: at a configuration of the revised arising set with the
index's stack, lifetimes, list and local resource, the context's values arise slot by slot. -/
def CtxArisesAt (σ : LStack) (αs : List Life) (ls : List SRec) (ρ : WRes) (Γ : Ctx VTy)
    (γ : List Val) : Prop :=
  ∃ c : Cfg, ArisesI (ℍ := ℍ) c ∧ c.σ = σ ∧ c.αs = αs ∧ c.ls = ls ∧ c.ρ = ρ ∧
    ArisesCtxI (ℍ := ℍ) c Γ γ

/-- **`MonoOwnGM` at a context that arises.** The `∀I` row has no transition to supply this
restriction from at its premise's pushed index: the own push is no constructor of `ArisesI`, and no
constructor of `ArisesVI` carries a value across a lend. -/
def MonoOwnGMA (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (αs : List Life) (ls : List SRec)
    (ρ : WRes) (C : CTy) (e : LEnt) (a : Life),
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    OwnPushI δ C ρ (σ, αs) e a → δ.find? e.x = none → CtxFresh e.x Γ →
    RecsOutside (a :: αs) ls → SubFresh δ a →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → CtxArisesAt (ℍ := ℍ) σ αs ls ρ Γ γ →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-! ### §3 The obligations the binder unit left -/

/-! #### §3.1 `OuterBelowTop` at every lend -/

/-- **A lend pushed below a bound keeps the outermost lend below `⊤`**: the own lend and the
borrow constants' lends meet a bound (`LtLife`). -/
def OuterBelowTopPush : Prop :=
  ∀ (αs : List Life) (a : Life) (s : LSub) (c : Lifetime.Life),
    OuterBelowTop αs → LtLife s c a → OuterBelowTop (a :: αs)

/-- **A lend chosen fresh below a lifetime** ([TR] 6.64's and 6.65's H4, `И`'s `∀α ⊏ β`). -/
def OuterBelowTopFresh : Prop :=
  ∀ (αs : List Life) (a β : Life), OuterBelowTop αs → a < β → OuterBelowTop (a :: αs)

/-- **Every configuration of the revised arising set has its outermost lend below `⊤`**:
`LendMutI` and `LendImmI` carry H4's consequence, and no other transition changes the lend
lifetimes. -/
def OuterBelowTopArises : Prop := ∀ c : Cfg, ArisesI (ℍ := ℍ) c → OuterBelowTop c.αs

/-! #### §3.2 `RetainedPay` row by row

A configuration carries no reading substitution, and `RetainedPay` reads one; so the obligation is
stated per row, at the index each row has (`SemIdxM`), and at every payload type. The arising
form is stated only for a leaf whose payload type reads a variable of the stack, which every
reading reads at the entry's lifetime (`InternalLeafArises`). -/

/-- **A borrow leaf of a value**: a `Mut` or `Imm` position of `(T, v)`, reached through the formers
`vRLM` reads at one index (`⊗`, `⊕`, `!`, `[@a]`, a closed `μ`'s unrolling, a family's elements) and
through `Ref` steps whose contents are read off `R`; the leaf's place and payload type. Core's
`MutPos` and `GPos` at both leaf kinds, with `!`. A `U` value's captures are not its leaves. -/
inductive LeafPos (R : WRes) : VTy → Val → BoCa.Loc → VTy → Prop
  | mut (a : Lifetime.Life) (S : VTy) (l : BoCa.Loc) : LeafPos R (.mut a S) (.loc l) l S
  | imm (a : Lifetime.Life) (S : VTy) (l : BoCa.Loc) : LeafPos R (.imm a S) (.loc l) l S
  | tensorL {A B : VTy} {v₁ v₂ : Val} {l : BoCa.Loc} {S : VTy} :
      LeafPos R A v₁ l S → LeafPos R (.tensor A B) (.pair v₁ v₂) l S
  | tensorR {A B : VTy} {v₁ v₂ : Val} {l : BoCa.Loc} {S : VTy} :
      LeafPos R B v₂ l S → LeafPos R (.tensor A B) (.pair v₁ v₂) l S
  | sumL {A B : VTy} {v : Val} {l : BoCa.Loc} {S : VTy} :
      LeafPos R A v l S → LeafPos R (.sum A B) (.inj₁ v) l S
  | sumR {A B : VTy} {v : Val} {l : BoCa.Loc} {S : VTy} :
      LeafPos R B v l S → LeafPos R (.sum A B) (.inj₂ v) l S
  | bang {A : VTy} {v : Val} {l : BoCa.Loc} {S : VTy} :
      LeafPos R A v l S → LeafPos R (.bang A) v l S
  | box {a : Lifetime.Life} {A : VTy} {v : Val} {l : BoCa.Loc} {S : VTy} :
      LeafPos R A v l S → LeafPos R (.box a A) v l S
  | ref {A : VTy} {l₀ : BoCa.Loc} {u : Val} {l : BoCa.Loc} {S : VTy} :
      R.get l₀ = some (CellU.ownOf u) → LeafPos R A u l S → LeafPos R (.ref A) (.loc l₀) l S
  | mu {A : VTy} {v : Val} {l : BoCa.Loc} {S : VTy} : (VTy.mu A).Cl 0 →
      LeafPos R (VTy.inst (.mu A) A) v l S → LeafPos R (.mu A) v l S
  | fam {L : VTy} {ℓ : BoCa.Loc} {c : UInt32} {i : Nat} {l : BoCa.Loc} {S : VTy} :
      i < c.toNat → LeafPos R L (.loc (ℓ + i)) l S → LeafPos R (.fam L) (Val.arr ℓ c) l S

/-- **Every borrow leaf of `(T, v)` meets `RetainedPay`** at the stack and the reading `s`. -/
def PayLeaves (σ : LStack) (αs : List Life) (s : LSub) (R : WRes) (T : VTy) (v : Val) : Prop :=
  ∀ (l : BoCa.Loc) (S : VTy), LeafPos R T v l S → RetainedPay σ αs s S (.loc l)

/-- **A payload type read at external lifetimes covers its leaves**: a leaf's payload type is a
part of the type (`VFree` through every former `LeafPos` crosses). The step the read-out rows take
at a retained view, whose `RetainedPay` gives `PayExt` of its payload type. -/
def PayLeavesOfPayExt : Prop :=
  ∀ (σ : LStack) (αs : List Life) (s : LSub) (R : WRes) (T : VTy) (v : Val),
    PayExt αs s T → PayLeaves σ αs s R T v

/-- **`SemSM`'s index at a judgement `Δ; Γ ⊢ _ : C`**: what every row has at its conclusion's
index. -/
def SemIdxM (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) : Prop :=
  BindersLow Γ C ∧ Scoped Δ Γ C ∧ StackOK σ αs ∧ OuterBelowTop αs ∧ StackJ σ αs δ Δ Γ C ∧
    SubDom δ Δ ∧ Δ.Models (extS δ σ αs) ∧ RecsOutside αs ls ∧ SubOutside σ αs δ ∧
    TabAtS σ αs ρ ∧ PlaceViewsL (extS δ σ αs) σ αs ls ρ

/-- **The lend's view** (`withbor` (1) and (2), their `U` and spanning forms, `withbor` (3)'s view
when its cell is at the own lend's place, the own lend at a `ViewAt` type): at the pushed stack
the view's place is the pushed entry's. At every payload type. -/
def RetainedPayViewRow : Prop :=
  ∀ (σ : LStack) (αs : List Life) (s : LSub) (e : LEnt) (α : Life) (T : VTy),
    RetainedPay (e :: σ) (α :: αs) s T (.loc e.l)

/-- **`withswap`'s read-out** (6.66's callback argument): the payload a `Mut` view's cell stores,
moved out to the callback at the view's index at the payload type `T`, has every borrow leaf
meeting `RetainedPay` there. The row reads the callback's `⊸` clause under the guard at the stack,
inside its run: so the read-out resource meets the table and the views, and is a part of a tagged
`TW` world at the list. At every payload type. -/
def RetainedPayLoadMutRow : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) (a : Lifetime.Life) (T : VTy) (l : BoCa.Loc)
    (ψ : CellU BoCa.Loc Val) (W ρr : WRes) (ps rs : List FrameRec),
    SemIdxM Δ Γ C δ σ αs ls ρ → ⟨.mut a T, true⟩ ∈ Γ →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.mut a T) αs ls (.loc l) ρ → ρ.get l = some ψ →
    TabAtS σ αs ψ.wit → PlaceViewsL (extS δ σ αs) σ αs ls ψ.wit →
    TW W ps rs → Tagged W ps ls → ResU.CompS ψ.wit ρr W →
    PayLeaves σ αs (extS δ σ αs) ψ.wit T ψ.erase

/-- **`withload`'s read-out**, and `foldImm`'s at each node: the payload an `Imm` view's cell
holds, reborrowed at `α` (`reb_α`, [TR] p. 5: an `own` or `mut` cell of the witness becomes an `imm`
cell at `α`, an `imm` cell is kept), handed to the callback at `Imm̲ 'x T` at the own lend's pushed
stack and the reading extended at `'x ↦ α`, has every borrow leaf meeting `RetainedPay` there. The
row reads the callback's clause under the guard at the pushed stack, inside its run. At every
payload type. -/
def RetainedPayLoadImmRow : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) (a : Lifetime.Life) (T : VTy) (l : BoCa.Loc)
    (ψ : CellU BoCa.Loc Val) (x : LifeVar) (c : Lifetime.Life) (D : CTy) (ρc : WRes)
    (en : LEnt) (α : Life) (ρb W ρr : WRes) (ps rs : List FrameRec),
    SemIdxM Δ Γ C δ σ αs ls ρ → ⟨.imm a T, true⟩ ∈ Γ → ¬ VFree x T → Δ.find? x = none →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.imm a T) αs ls (.loc l) ρ → ρ.get l = some ψ →
    OwnPushI δ (.all x c (.arr (T.immReborrow (.var x)) D)) ρc (σ, αs) en α →
    RecsOutside (α :: αs) ls → SubFresh δ α → ResU.Reb α ψ.wit ρb →
    TabAtS (en :: σ) (α :: αs) ρb →
    PlaceViewsL (extS (δ.extend x α) (en :: σ) (α :: αs)) (en :: σ) (α :: αs) ls ρb →
    TW W ps rs → Tagged W ps ls → ResU.CompS ρb ρr W →
    PayLeaves (en :: σ) (α :: αs) (extS (δ.extend x α) (en :: σ) (α :: αs)) PMap.empty
      (T.immReborrow (.var x)) ψ.erase

/-! ##### The nested `Mut` leaf of a bound view: through `CohS`'s `TyEq` to the entry's payload -/

/-- **A lifetime term with no join**: a variable, `⊤`, or a meet of such terms. Its value at a
reading is no longer-lived than any variable it reads, so it is external only when each of them
is. -/
def NoJoinL : Lifetime.Life → Prop
  | .var _ => True
  | .top => True
  | .join _ _ => False
  | .meet a b => NoJoinL a ∧ NoJoinL b

mutual
/-- **A value type with no join in any lifetime term**, computation types included. -/
def NoJoinV : VTy → Prop
  | .thunk C => NoJoinC C
  | .tensor A B => NoJoinV A ∧ NoJoinV B
  | .sum A B => NoJoinV A ∧ NoJoinV B
  | .bang A => NoJoinV A
  | .box a A => NoJoinL a ∧ NoJoinV A
  | .ref A => NoJoinV A
  | .imm a A => NoJoinL a ∧ NoJoinV A
  | .mut a A => NoJoinL a ∧ NoJoinV A
  | .mu A => NoJoinV A
  | .fam A => NoJoinV A
  | _ => True
/-- **A computation type with no join in any lifetime term.** -/
def NoJoinC : CTy → Prop
  | .ret A => NoJoinV A
  | .arr A C => NoJoinV A ∧ NoJoinC C
  | .amp C D => NoJoinC C ∧ NoJoinC D
  | .top => True
  | .all _ b C => NoJoinL b ∧ NoJoinC C
  | .nu C => NoJoinC C
  | .eff _ _ _ A B C => NoJoinV A ∧ NoJoinV B ∧ NoJoinC C
end

/-- **A leaf's position transfers along `TyEq`**: the matching position of a type one type with
`T` up to the readings is a leaf at the same place, its payload type one type with the leaf's.
`TyEq` is positional, and `LeafPos` crosses no lifetime binder. -/
def LeafPosTyEq : Prop :=
  ∀ (R : WRes) (T T' : VTy) (s s' : LSub) (v : Val) (l : BoCa.Loc) (S : VTy),
    TyEq T s T' s' → LeafPos R T v l S → ∃ S', LeafPos R T' v l S' ∧ TyEq S s S' s'

/-- **External readings transfer along `TyEq` to a type with no join**: a variable of `S` read at
an internal lifetime sits in a meet term, whose value is then internal, while the matching term of
`S'`, its free variables external and its bound ones read at `⊤`, has an external value. A join is
pinned by `TyEq` only as a whole. -/
def PayExtOfTyEq : Prop :=
  ∀ (αs : List Life) (s : LSub) (S S' : VTy), TyEq S s S' s → NoJoinV S →
    (∀ y, VFree y S → ∃ m, s.find? y = some m) → PayExt αs s S' → PayExt αs s S

/-- **`PayLeaves` transfers along `TyEq` to a type with no join**: `LeafPosTyEq` and
`PayExtOfTyEq` at each leaf; a leaf's place is the same on both sides, so is whether an entry
lends it. -/
def PayLeavesOfTyEq : Prop :=
  ∀ (σ : LStack) (αs : List Life) (s : LSub) (R : WRes) (T T' : VTy) (v : Val),
    TyEq T s T' s → NoJoinV T → (∀ y, VFree y T → ∃ m, s.find? y = some m) →
    PayLeaves σ αs s R T' v → PayLeaves σ αs s R T v

/-- **`withswap`'s read-out at a bound view, reduced to the entry's payload type**: the view's
`CohS` gives `TyEq T s e.T s` at the stack's reading, and `PayLeavesOfTyEq` carries the leaves of
the stored payload read at `e.T` to those read at `T`. -/
def RetainedPayLoadMutBound : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (ls : List SRec) (ρ : WRes) (a : Lifetime.Life)
    (T : VTy) (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val) (e : LEnt) (α : Life),
    innerAt σ αs l = some (e, α) → NoJoinV T →
    (∀ y, VFree y T → ∃ m, (extS δ σ αs).find? y = some m) →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.mut a T) αs ls (.loc l) ρ → ρ.get l = some ψ →
    PayLeaves σ αs (extS δ σ αs) ψ.wit e.T ψ.erase →
    PayLeaves σ αs (extS δ σ αs) ψ.wit T ψ.erase

/-- **The leftover at a bound view**: at the read-out row's index and facts, the payload a 6.65
entry's cell stores has every borrow leaf of the entry's payload type meeting `RetainedPay`.
`StackJ` lets `e.T` read `Δ`'s variables and the stack's, so the index does not carry it.
`InternalLeafArises`' second disjunct is its failure at a configuration of the arising set. -/
def EntryPayLeaves : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val) (e : LEnt) (α : Life)
    (W ρr : WRes) (ps rs : List FrameRec),
    SemIdxM Δ Γ C δ σ αs ls ρ → innerAt σ αs l = some (e, α) → e.k = .mut → ρ.get l = some ψ →
    TabAtS σ αs ψ.wit → PlaceViewsL (extS δ σ αs) σ αs ls ψ.wit →
    TW W ps rs → Tagged W ps ls → ResU.CompS ψ.wit ρr W →
    PayLeaves σ αs (extS δ σ αs) ψ.wit e.T ψ.erase

/-! ##### The read-out rows' hypotheses, met -/

/-- **`RetainedPayLoadMutRow`'s hypotheses are met at a one-entry stack, with a read-out leaf at a
place no entry lends whose payload type reads a variable**, so its conclusion is not vacuous. -/
def RetainedPayLoadMutRowMet : Prop :=
  ∃ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) (a : Lifetime.Life) (T : VTy) (l : BoCa.Loc)
    (ψ : CellU BoCa.Loc Val) (W ρr : WRes) (ps rs : List FrameRec) (lf : BoCa.Loc) (S : VTy)
    (y : LifeVar),
    σ.length = 1 ∧ SemIdxM Δ Γ C δ σ αs ls ρ ∧ ⟨.mut a T, true⟩ ∈ Γ ∧
    vRLM (ℍ := ℍ) .binder0 none σ δ (.mut a T) αs ls (.loc l) ρ ∧ ρ.get l = some ψ ∧
    TabAtS σ αs ψ.wit ∧ PlaceViewsL (extS δ σ αs) σ αs ls ψ.wit ∧
    TW W ps rs ∧ Tagged W ps ls ∧ ResU.CompS ψ.wit ρr W ∧
    LeafPos ψ.wit T ψ.erase lf S ∧ innerAt σ αs lf = none ∧ VFree y S

/-- **`RetainedPayLoadImmRow`'s hypotheses are met at a one-entry stack, with a kept leaf at a
place no entry lends whose payload type reads a variable**, so its conclusion is not vacuous. -/
def RetainedPayLoadImmRowMet : Prop :=
  ∃ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) (a : Lifetime.Life) (T : VTy) (l : BoCa.Loc)
    (ψ : CellU BoCa.Loc Val) (x : LifeVar) (c : Lifetime.Life) (D : CTy) (ρc : WRes)
    (en : LEnt) (α : Life) (ρb W ρr : WRes) (ps rs : List FrameRec) (lf : BoCa.Loc) (S : VTy)
    (y : LifeVar),
    σ.length = 1 ∧ SemIdxM Δ Γ C δ σ αs ls ρ ∧ ⟨.imm a T, true⟩ ∈ Γ ∧ ¬ VFree x T ∧
    Δ.find? x = none ∧ vRLM (ℍ := ℍ) .binder0 none σ δ (.imm a T) αs ls (.loc l) ρ ∧
    ρ.get l = some ψ ∧ OwnPushI δ (.all x c (.arr (T.immReborrow (.var x)) D)) ρc (σ, αs) en α ∧
    RecsOutside (α :: αs) ls ∧ SubFresh δ α ∧ ResU.Reb α ψ.wit ρb ∧
    TabAtS (en :: σ) (α :: αs) ρb ∧
    PlaceViewsL (extS (δ.extend x α) (en :: σ) (α :: αs)) (en :: σ) (α :: αs) ls ρb ∧
    TW W ps rs ∧ Tagged W ps ls ∧ ResU.CompS ρb ρr W ∧
    LeafPos PMap.empty (T.immReborrow (.var x)) ψ.erase lf S ∧
    innerAt (en :: σ) (α :: αs) lf = none ∧ VFree y S

/-- **A slice borrow's elements** (`sliceBorrowM`, `sliceBorrowI`, their `U` forms): the family
handed to the callback is the array's handle, each element a `Mut 'x A` (or `Imm 'x A`) leaf, a
cell at the own lend's lifetime at its place; each owes `RetainedPay` at the own lend's pushed stack
and the reading extended at `'x ↦ α`, under the guard there. Under `vRLJ` the family was Core's
whole and asked none of this; `vRLM`'s `[L]` clause reads each element as W's leaf. At every element
type. It holds vacuously at every count: at two or more elements the guard fails
(`SliceGuardFails`); at one element, a cell at `α` at a place no entry lends fails the table's
second conjunct, and at the own lend's place `RetainedPay` is vacuous. It is no evidence that a
slice row is covered: at two or more elements the callback's clause is vacuous under the guard, and
the row is outside W. -/
def RetainedPaySliceRow : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) (A : VTy) (ℓ : BoCa.Loc) (n : UInt32) (x : LifeVar)
    (c : Lifetime.Life) (L : VTy) (D : CTy) (ρc : WRes) (en : LEnt) (α : Life) (ρa : WRes),
    SemIdxM Δ Γ C δ σ αs ls ρ → ⟨.array A, true⟩ ∈ Γ → ¬ VFree x A → Δ.find? x = none →
    (L = .mut (.var x) A ∨ L = .imm (.var x) A) →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.array A) αs ls (Val.arr ℓ n) ρ →
    OwnPushI δ (.all x c (.arr (.fam L) D)) ρc (σ, αs) en α →
    RecsOutside (α :: αs) ls → SubFresh δ α →
    (∀ i < n.toNat, ∃ ψ, ρa.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = α) →
    TabAtS (en :: σ) (α :: αs) ρa →
    PlaceViewsL (extS (δ.extend x α) (en :: σ) (α :: αs)) (en :: σ) (α :: αs) ls ρa →
    ∀ i < n.toNat,
      RetainedPay (en :: σ) (α :: αs) (extS (δ.extend x α) (en :: σ) (α :: αs)) A (.loc (ℓ + i))

/-- **A family of two cells at the innermost lend's lifetime meets the table at no stack whose
entries lend none of its places but the innermost**: the table's second conjunct puts every
top-level borrow cell at a place no entry lends strictly above the outermost lend, which is at or
above the innermost. So a slice borrow's family meets the guard at no own-lend push: the own lend
lends one place, and W has no entry lending a range. -/
def SliceGuardFails : Prop :=
  ∀ (σ : LStack) (αs : List Life) (en : LEnt) (α : Life) (ρ : WRes) (ℓ : BoCa.Loc) (n : Nat),
    StackOK (en :: σ) (α :: αs) → 2 ≤ n → (∀ i < n, ℓ + i ∉ σ.map LEnt.l) →
    (∀ i < n, ∃ ψ, ρ.get (ℓ + i) = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at = α) →
    ¬ TabAtS (en :: σ) (α :: αs) ρ

/-- **`∀E` at an instance with no join**: a leaf the callee's clause gives at the reading extended
at `'x ↦ ⟦b⟧` meets `RetainedPay` at the instance `S[b/'x]` and the reading itself. At a variable,
`⊤` or a meet, every variable of `b` reads a lifetime at least as long as `⟦b⟧`, so an external one
when `⟦b⟧` is; `⊤` reads none. A join is not covered: `⟦'v ⊔ 'w⟧` external says nothing of the
shorter of the two. -/
def RetainedPayInstRow : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (x : LifeVar) (b : Lifetime.Life) (S : VTy)
    (v : Val) (m : ℕ),
    x ∉ σ.map LEnt.x → NoJoinL b → b.interp (extS δ σ αs) = some m →
    RetainedPay σ αs (extS (δ.extend x m) σ αs) S v →
    RetainedPay σ αs (extS δ σ αs) (S.instLife x b) v

/-- **`RetainedPay` across a lend pushed fresh below the reading.** -/
def RetainedPayPush : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (e : LEnt) (a : Life) (T : VTy) (v : Val),
    StackOK σ αs → List.IsChain (· < ·) (a :: αs) → SubFresh δ a → ¬ VFree e.x T →
    (∀ l, v = .loc l → l ≠ e.l) →
    RetainedPay σ αs (extS δ σ αs) T v →
    RetainedPay (e :: σ) (a :: αs) (extS δ (e :: σ) (a :: αs)) T v

/-- **`RetainedPay` across the end of a lend.** -/
def RetainedPayPop : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (e : LEnt) (a : Life) (T : VTy) (v : Val),
    StackOK (e :: σ) (a :: αs) → ¬ VFree e.x T → (∀ l, v = .loc l → l ≠ e.l) →
    RetainedPay (e :: σ) (a :: αs) (extS δ (e :: σ) (a :: αs)) T v →
    RetainedPay σ αs (extS δ σ αs) T v

/-- **`RetainedPay` across a binding the payload type does not read.** -/
def RetainedPayExtend : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (x : LifeVar) (a : Life) (T : VTy) (v : Val),
    x ∉ σ.map LEnt.x → ¬ VFree x T →
    RetainedPay σ αs (extS δ σ αs) T v → RetainedPay σ αs (extS (δ.extend x a) σ αs) T v

/-- **The arising check of a per-row refutation**: at a configuration of the revised arising set,
a borrow leaf at a place no entry lends, its cell strictly above the outermost lend (what the guard
makes of every such leaf where a row reads a callback's clause), whose payload type reads one of the
stack's variables. The leaf is one of a value arising there, or one of the payload an entry's cell
holds (what a read-out hands on). Every reading reads a stack variable at its entry's lifetime,
which is internal, so such a leaf fails `RetainedPay` at every reading. `InternalPayloadArises`'s
shape one level down. -/
def InternalLeafArises : Prop :=
  ∃ (c : Cfg) (A : VTy) (v : Val) (R : WRes) (l : BoCa.Loc) (S : VTy) (y : LifeVar)
    (ψl : CellU BoCa.Loc Val),
    ArisesI (ℍ := ℍ) c ∧
    ((ArisesVI (ℍ := ℍ) c v A ∧ R = c.ρ) ∨
      ∃ (e : LEnt) (ψ : CellU BoCa.Loc Val), e ∈ c.σ ∧ c.fρ.FlatAt e.l ψ ∧ A = e.T ∧
        v = ψ.erase ∧ R = ψ.wit) ∧
    LeafPos R A v l S ∧ innerAt c.σ c.αs l = none ∧ R.get l = some ψl ∧
    (∀ o ∈ c.αs.getLast?, o < ψl.at) ∧ VFree y S ∧ y ∈ c.σ.map LEnt.x

/-- **At `InternalPayloadArises`'s shape the read-out meets `RetainedPay`**: `x`'s payload type
`Imm 'b 1` has one leaf, whose payload type `1` reads nothing. So that configuration, if it arises,
refutes no read-out row. -/
def ReadOutAtInternalPayload : Prop :=
  ∀ (s : LSub) (R : WRes) (u : Val), PayLeaves mwσ mwαs s R mwX.T u

/-! ##### The variant leaf a stop at `EntryPayLeaves` would call for (stated, not adopted)

The global form of the invariant `BINDER.md` §11 states in prose: a borrow leaf carries
`RetainedPay` of the leaves inside its payload. Its costs are where the thaw meets a bound leaf
(`ThawLeafP`) and whether W's views carry it (`VwPayLeaves`). -/

/-- **The payload's leaves of a borrow leaf meet `RetainedPay`**: at the cell the leaf's place
holds, every borrow leaf of the stored value at the payload type, through the cell's witness. -/
def PayLeavesAt (σ : LStack) (αs : List Life) (s : LSub) (T : VTy) (v : Val) (ρ : WRes) :
    Prop :=
  ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), v = .loc l → ρ.get l = some ψ →
    PayLeaves σ αs s ψ.wit T ψ.erase

/-- **The variant `Mut` leaf**: `vRLM`'s `Mut` leaf at a closed payload type, with `PayLeavesAt`. -/
def mutLeafP (σ : LStack) (s : LSub) (a : Lifetime.Life) (T : VTy) (αs : List Life)
    (ls : List SRec) (v : Val) : WProp := fun ρ =>
  vC true (.mut a T) ls s v ρ ∧ CohS σ αs s (.mut a T) v ρ ∧ RetainedPay σ αs s T v ∧
    PayLeavesAt σ αs s T v ρ

/-- **The variant `Imm` leaf.** -/
def immLeafP (σ : LStack) (s : LSub) (a : Lifetime.Life) (T : VTy) (αs : List Life)
    (ls : List SRec) (v : Val) : WProp := fun ρ =>
  vC true (.imm a T) ls s v ρ ∧ CohS σ αs s (.imm a T) v ρ ∧ RetainedPay σ αs s T v ∧
    PayLeavesAt σ αs s T v ρ

/-- **W's views carry their payload's leaves**: a view of an entry, as `vwEW` reads it, has
`PayLeavesAt` of the entry's payload type. `vwEW` is GhostEnd's view at the reading, whose cell
stores any value of Core's relation at `e.T`, and Core's nested leaves carry no `RetainedPay`. -/
def VwPayLeaves : Prop :=
  ∀ (s : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (e : LEnt) (α : Life) (ρ : WRes),
    (e, α) ∈ σ.zip αs → vwEW s e true α ls ρ → PayLeavesAt σ αs s e.T (.loc e.l) ρ

/-- **The thaw at a bound variant leaf**: dropped and handed back at an instantiation, the view
re-establishes the variant leaf (`viewSlotInstOB` for the first three conjuncts) when it carries
`PayLeavesAt` of the entry's payload at the instantiated index: `TyEq T s e.T s` moves along the
instantiation (`tyEqInst`), and `PayLeavesOfTyEq` carries the leaves to `T`. -/
def ThawLeafP : Prop :=
  ∀ (σ : LStack) (αs : List Life) (s : LSub) (ls ls' : List SRec) (a : Lifetime.Life) (T : VTy)
    (l : BoCa.Loc) (e : LEnt) (α : Life) (ρ ρv : WRes) (ι : Inst),
    innerAt σ αs l = some (e, α) → InstAt αs ι → OuterBelowTop αs → RecsOutside αs ls →
    KeepsS (ι.recs ls) ls' ρ → NoJoinV T → (∀ y, VFree y T → ∃ m, (ι.sub s).find? y = some m) →
    mutLeafP σ s a T αs ls (.loc l) ρ →
    vwEW (ι.sub s) e true (ι.life1 α) ls' ρv →
    PayLeavesAt σ (ι.life αs) (ι.sub s) e.T (.loc e.l) ρv →
    mutLeafP σ (ι.sub s) a T (ι.life αs) ls' (.loc l) ρv

/-! #### §3.3 `KeepsT` at the share -/

/-- **A record lies in one frame's lineage** at a `TW` world. -/
def LineageUnique : Prop :=
  ∀ (W : WRes) (ps rs : List FrameRec) (p p' d : FrameRec),
    TW W ps rs → p ∈ ps → p' ∈ ps → DescR p d → DescR p' d → p = p'

/-- **A record has one tag at a `TW` world**: two lists tagged there hold it at one tag. -/
def TagFixed : Prop :=
  ∀ (W : WRes) (ps rs : List FrameRec) (ls ls' : List SRec) (x x' : SRec),
    TW W ps rs → Tagged W ps ls → Tagged W ps ls' → x ∈ ls → x' ∈ ls' → x'.1 = x.1 →
      x'.2 = x.2

/-- **`Ext` between two lists tagged at one world keeps the tags.** -/
def KeepsTOfTagged : Prop :=
  ∀ (W ρ : WRes) (ps rs : List FrameRec) (ls ls' : List SRec),
    TW W ps rs → Tagged W ps ls → Tagged W ps ls' → Ext ls ls' ρ → KeepsT ls ls' ρ

/-- **`ExtInst` with the tags kept** (`not_extInst` refutes it without them): an extension that
keeps the tags is one of the instantiated lists, at a resource above the outermost lend. Both
lists are instantiated: the record half's tool (`MonoExtM`), not the share's. -/
def ExtInstT : Prop :=
  ∀ (ls ls' : List SRec) (ρ : WRes) (αs : List Life) (ι : Inst), InstAt αs ι → stratS αs ρ →
    Ext ls ls' ρ → KeepsT ls ls' ρ →
    Ext (ι.recs ls) (ι.recs ls') ρ ∧ KeepsT (ι.recs ls) (ι.recs ls') ρ

/-- **The records of `ls` relevant to `ρ` lie strictly above the outermost lend.** -/
def RelAbove (αs : List Life) (ls : List SRec) (ρ : WRes) : Prop :=
  ∀ x ∈ ls, Core.Rel x.1 ρ → ∀ o ∈ αs.getLast?, o < x.2

/-- **At a tagged `TW` world, a part strictly above the outermost lend has its relevant records
above it**: a relevant record's tag is the lifetime of a frame whose lineage holds it (`Tagged`),
the frame's cell is at that lifetime and its lineage's cells no longer (`FrameLife`), and the part's
`imm` cell the record is relevant through is one of those, strictly above the outermost lend
(`stratS`). -/
def RelAboveOfTagged : Prop :=
  ∀ (W ρz ρr : WRes) (ps rs : List FrameRec) (ls : List SRec) (αs : List Life),
    TW W ps rs → Tagged W ps ls → ResU.CompS ρz ρr W → stratS αs ρz → RelAbove αs ls ρz

/-- **The bridge to the instantiated list**: the records relevant to the retained part are above
the outermost lend, so the instantiation fixes them (`mem_recs_iff_of_lt`), and `Ext` and `KeepsT`
from the list carry to the instantiated list. -/
def ExtKeepsTInst : Prop :=
  ∀ (αs : List Life) (ι : Inst) (ls ls' : List SRec) (ρz : WRes),
    InstAt αs ι → stratS αs ρz → RelAbove αs ls ρz → Ext ls ls' ρz → KeepsT ls ls' ρz →
    Ext (ι.recs ls) ls' ρz ∧ KeepsT (ι.recs ls) ls' ρz

/-- **The frames the retained part's records are in stay open at the resume**, with their frame
lifetimes: the premise statement 2's resume composite owes (`BINDER.md` §3.7). Only frames relevant
to `ρz` through a record of `ls` are named. -/
def FramesKept (W W' ρz : WRes) (ps ps' : List FrameRec) (ls : List SRec) : Prop :=
  ∀ p ∈ ps, (∃ x ∈ ls, DescR p x.1 ∧ Core.Rel x.1 ρz) →
    p ∈ ps' ∧ ∀ α, FrameLife W p α → FrameLife W' p α

/-- **The resume keeps the retained part's records with their tags**: the stop's list and the
resume's, each tagged at its world, `Ext`-related at the retained part, the frames `FramesKept`
names still open. -/
def ResumeKeepsT : Prop :=
  ∀ (W W' ρz : WRes) (ps ps' rs rs' : List FrameRec) (ls ls' : List SRec),
    TW W ps rs → Tagged W ps ls → TW W' ps' rs' → Tagged W' ps' ls' →
    FramesKept W W' ρz ps ps' ls → Ext ls ls' ρz → KeepsT ls ls' ρz

/-- **`KeepsT` at the share, in the form `RelendJ` consumes**: at the share's instantiation `ι` of
the stack, the retained part `ρz` above the outermost lend and a part of the stop's tagged world,
the resume's tagged world and `Ext` from the stop's list to the resume's, the resume's list
extends the instantiated list and keeps its records relevant to `ρz` with their tags. -/
def ShareKeepsT : Prop :=
  ∀ (W W' ρz ρr : WRes) (ps ps' rs rs' : List FrameRec) (ls ls' : List SRec) (αs : List Life)
    (ι : Inst),
    InstAt αs ι → stratS αs ρz → TW W ps rs → Tagged W ps ls → ResU.CompS ρz ρr W →
    TW W' ps' rs' → Tagged W' ps' ls' → FramesKept W W' ρz ps ps' ls → Ext ls ls' ρz →
    Ext (ι.recs ls) ls' ρz ∧ KeepsT (ι.recs ls) ls' ρz

/-- **The frames `FramesKept` names are no lend's frame**: such a frame's lifetime is its record's
tag, strictly above the outermost lend (`RelAboveOfTagged`), while a lend's frame is at the lend's
lifetime, at or below it. The ghost end ends the ended entries' 6.64 frames and no other
(`BINDER.md` §3.7), so it ends none `FramesKept` names. -/
def RelFramesNotEnded : Prop :=
  ∀ (W ρz ρr : WRes) (ps rs : List FrameRec) (ls : List SRec) (σ : LStack) (αs : List Life)
    (p : FrameRec),
    TW W ps rs → Tagged W ps ls → ResU.CompS ρz ρr W → StackOK σ αs → stratS αs ρz → p ∈ ps →
    (∃ x ∈ ls, DescR p x.1 ∧ Core.Rel x.1 ρz) → ∀ α ∈ αs, ¬ FrameLife W p α

/-- **`ShareKeepsT`'s premises are met at a share with a ghost-ended entry**: a 6.64 entry whose
frame is at the entry's lifetime at the stop and re-opened at the moved lifetime at the resume, a
retained part relevant to a kept frame, `FramesKept`, `Ext` from the stop's list to the resume's,
which is the instantiated list. -/
def ShareKeepsTMet : Prop :=
  ∃ (W W' ρz ρr : WRes) (ps ps' rs rs' : List FrameRec) (ls ls' : List SRec) (σ : LStack)
    (αs : List Life) (ι : Inst) (e : LEnt) (αe : Life) (pe : FrameRec) (u : Val),
    StackOK σ αs ∧ InstAt αs ι ∧ stratS αs ρz ∧
    TW W ps rs ∧ Tagged W ps ls ∧ ResU.CompS ρz ρr W ∧ TW W' ps' rs' ∧ Tagged W' ps' ls' ∧
    (e, αe) ∈ σ.zip αs ∧ e.k = .imm u ∧ pe ∈ ps ∧ pe.le = e.l ∧ FrameLife W pe αe ∧
    pe ∈ ps' ∧ FrameLife W' pe (ι.life1 αe) ∧ ι.life1 αe ≠ αe ∧
    (∃ x ∈ ls, Core.Rel x.1 ρz) ∧ FramesKept W W' ρz ps ps' ls ∧ Ext ls ls' ρz ∧
    ls' = ι.recs ls

/-! #### §3.4 `ViewSlotInst` at an outermost lend at `⊤` -/

/-- **`ViewSlotInst` as stated fails at an outermost lend at `⊤`** (only if cheap; `not_cohEInst`'s
configuration in an `Imm` view slot). -/
def NotViewSlotInst : Prop := ¬ ViewSlotInst

/-! ### §4 Statement 0 at `vRLM` -/

/-- **At a data type `vRLM` is the kernel's leaf reading**, `μ` included. -/
def VRLMData : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (A : VTy), A.Data →
    ∀ (ls : List SRec) (v : Val), vRLM (ℍ := ℍ) p none σ δ A αs ls v = vC true A ls (extS δ σ αs) v

/-- **W's environment is Core's at the mode `true` and the list `ls`**: the same types, and each
candidate Core's candidate there. Core's `μ` candidate is joint over the mode and the list; a data
body reads its variable at the mode and the list it is read at, so the comparison is at one. -/
def EnvCore (η : Option (Nat → WEnt)) (ηc : Option (Nat → TEnt)) (ls : List SRec) : Prop :=
  (∀ n, (wEnv η n).ty = (tEnv ηc n).ty) ∧ ∀ n v ρ, wEnvP η n v ρ ↔ tEnvP ηc n true ls v ρ

/-- **`VRLMData` under an environment**, at a data type with `k` bound variables: the induction the
`μ` case closes by the two fixed points (`vRLM`'s through `VRLMRoll`, Core's through `vC_roll` and
`vC_mu_ind`). -/
def VRLMDataE : Prop :=
  ∀ (p : Placement) (k : Nat) (A : VTy), VTy.DataB k A →
    ∀ (η : Option (Nat → WEnt)) (ηc : Option (Nat → TEnt)) (σ : LStack) (δ : LSub)
      (αs : List Life) (ls : List SRec) (v : Val),
      EnvCore η ηc ls →
      vRLM (ℍ := ℍ) p η σ δ A αs ls v = vCE ηc true A ls (extS δ σ αs) v

/-- `EnvCore` holds at `none`: both types are `.tvar n`, both candidates `False`. -/
def EnvCoreNone : Prop := ∀ ls : List SRec, EnvCore none none ls

/-- `VRLMData` is `VRLMDataE` at `k = 0` and `none`. -/
def VRLMDataOfE : Prop := VRLMDataE (ℍ := ℍ) → VRLMData (ℍ := ℍ)

/-- **`NilSoundRet` at `vRLM`.** -/
def NilSoundRetM (p : Placement) : Prop :=
  ∀ (δ : LSub) (S : Row) (A : VTy) (ls : List SRec) (e : Expr) (ρ : WRes), A.Data →
    cRLM (ℍ := ℍ) p [] δ (CTy.effOf S A) [] ls e ρ → cC (CTy.effOf S A) ls δ e ρ

/-- **A revised future at a resource is one at each of its parts** (`FutPart` at `FutI`):
`FutOK.below` at a part as at W₀, and `FutOKI.placesFree` at a part, a cell of a part at any depth
being a cell of the whole at any depth. `MonoGMOfMonoVM` reads it slot by slot. -/
def FutPartI : Prop :=
  ∀ (δ : LSub) (ρz ρn ρ : WRes) (s s' : Stk), ResU.CompS ρz ρn ρ → FutI δ ρ s s' → FutI δ ρz s s'

/-- **Statement 0's shared lemmas at `vRLM`**: the relation-independent ones at the revised futures
(`FutPartI` in place of `FutPart`), and the nil slice at `vRLM`. W₀'s `FutReLend` is not among
them: no clause of `binder0` reads a future (`FutQI false`), and at `cbpv` and `binder` its place
at the revised `U` clause is `FutInst` (`R1MONO.md` §4.3). -/
def Statement0SharedM : Prop :=
  (∀ p : Placement, ExtPreW (ℍ := ℍ) p) ∧ FutPartI ∧ FutAvoidsTrans ∧
    OpenSFBridge (ℍ := ℍ) ∧ ∀ p : Placement, NilSoundRetM (ℍ := ℍ) p

/-- **`[force]` at `vRLM`.** -/
def ForceRowM (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (i : Nat) (C : CTy), Ctx.SoloP Γ i (.thunk C) →
    SemSM (ℍ := ℍ) p Δ Γ (forceE C (.var i)) (.comp C)

/-- **The 6.65 callback at `σ·y`, at `vRLM`**: `CallbackExtMut` with the revised own lend and
index, and the view's payload the entry's (`e.T = T`). Stated at the `.arr` shape `∀'y ⊏ c. A ⊸ D`,
the unwinding forms' callback type (`cbUTy`). `¬ VFree y T` is the constants' side condition
(`hfree₁`, `NEXT.md` (E4)). -/
def CallbackExtMutM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T : VTy) (D : CTy)
    (αs : List Life) (ls : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (α : Life) (ρv ρ : WRes),
    ¬ VFree y T → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    e.x = y → e.k = .mut → e.T = T → y ∉ CTy.binders (.arr (.mut (.var y) T) D) →
    OwnOKI δ σ αs e α ρf → LtLife (extS δ σ αs) c α → RecsOutside (α :: αs) ls → SubFresh δ α →
    TabAtS σ αs ρf → PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    vRLM (ℍ := ℍ) p none σ δ (.thunk (.all y c (.arr (.mut (.var y) T) D))) αs ls f ρf →
    vRLM (ℍ := ℍ) p none (e :: σ) (δ.extend y α) (.mut (.var y) T) (α :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    PlaceViewsL (extS (δ.extend y α) (e :: σ) (α :: αs)) (e :: σ) (α :: αs) ls ρ →
    cRLM (ℍ := ℍ) p (e :: σ) (δ.extend y α) D (α :: αs) ls
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ

/-- **The 6.64 callback at `σ·y`, at `vRLM`**: the list the lend extends (`ext_add`) keeps the
tags. At the `.arr` shape, with (E4)'s `¬ VFree y T`. -/
def CallbackExtImmM (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life) (T : VTy) (D : CTy)
    (αs : List Life) (ls ls' : List SRec) (f w : Val) (ρf : WRes) (e : LEnt) (u : Val) (α : Life)
    (ρv ρ : WRes),
    ¬ VFree y T → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → SubOutside σ αs δ →
    e.x = y → e.k = .imm u → e.T = T → y ∉ CTy.binders (.arr (.imm (.var y) T) D) →
    OwnOKI δ σ αs e α ρf → LtLife (extS δ σ αs) c α → RecsOutside (α :: αs) ls' →
    SubFresh δ α → TabAtS σ αs ρf → PlaceViewsL (extS δ σ αs) σ αs ls ρf →
    Ext ls ls' ρf → KeepsT ls ls' ρf →
    vRLM (ℍ := ℍ) p none σ δ (.thunk (.all y c (.arr (.imm (.var y) T) D))) αs ls f ρf →
    vRLM (ℍ := ℍ) p none (e :: σ) (δ.extend y α) (.imm (.var y) T) (α :: αs) ls' w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    PlaceViewsL (extS (δ.extend y α) (e :: σ) (α :: αs)) (e :: σ) (α :: αs) ls' ρ →
    cRLM (ℍ := ℍ) p (e :: σ) (δ.extend y α) D (α :: αs) ls'
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ

/-- **Statement 0 at `vRLM`**: `Statement0`'s per-placement facts at the revised relation, the
thaw and the `U` rows at every context. -/
def Statement0M (p : Placement) : Prop :=
  MonoOwnGM (ℍ := ℍ) p ∧ MonoVM (ℍ := ℍ) p ∧ MonoGM (ℍ := ℍ) p ∧ CallbackExtMutM (ℍ := ℍ) p ∧
    CallbackExtImmM (ℍ := ℍ) p ∧ ForceRowM (ℍ := ℍ) p ∧ Statement0UFullM (ℍ := ℍ) p

/-- **Statement 0's facts at `binder0` beside monotonicity.** -/
def Statement0MBesideMono0 : Prop :=
  Statement0SharedM (ℍ := ℍ) ∧ CallbackExtMutM (ℍ := ℍ) .binder0 ∧
    CallbackExtImmM (ℍ := ℍ) .binder0 ∧ ForceRowM (ℍ := ℍ) .binder0 ∧
    Statement0UFullM (ℍ := ℍ) .binder0

/-- **The unrestricted monotonicity statements refuted at `binder0`**, at `gd`, an index outside the
arising set's record invariant and a closure that is no Core value. A fact about these three
statements of ProbeD1, not `binder0`'s status: their consumer `AllIRowM .binder0` and the
restricted route (`MonoOwnGMC`, `AllIRowMC`) are open. -/
def MonoUnrestrictedRefuted0 : Prop :=
  ¬ MonoOwnGM (ℍ := ℍ) .binder0 ∧ ¬ MonoGM (ℍ := ℍ) .binder0 ∧ ¬ MonoVM (ℍ := ℍ) .binder0

/-- **Statement 0 at `binder0`, monotonicity read at its consumers**: `AllIRowM` in place of
`MonoOwnGM`, its only consumer at `binder0`, and `MonoExtM` for the rows that move a context along
the record order (`[let]`, the end of a lend). The handler's `MonoHide` at `vRLM` is not stated. -/
def Statement0MAtConsumers0 : Prop :=
  Statement0MBesideMono0 (ℍ := ℍ) ∧ MonoExtM (ℍ := ℍ) .binder0 ∧ AllIRowM (ℍ := ℍ) .binder0

end ProbeD1

end
