import ProbeD1.GroundLedger
import Core
import GhostEnd.Below
import Affine.Programs
import SecondClass.RecLog
import Examples.CallBorrowed
import Examples.Captures
import Examples.FnMut
import Frontend.Check.CrossCheck

/-!
# ProbeD1 — the regression suite (`GROUND.md` §3, `LEDGER.md` §10)

Every borrow-only program Core accepts must be accepted by the draft. A program's obligation is
`DraftFL` restricted to its derivation: at every node `Δ; Γ ⊢ e : j` of its `CDerives` derivation,
`SemSM .binder0 Δ Γ e j` at every index (`AccNode`). Each entry here is one node, stated at every
index; a theorem proves it where it is PROVED, and otherwise its docstring names the missing lemma.
No entry is FAILS: a failure is admitted only at a configuration that arises (`ArisesI`, with
`ArisesVI` for every value read), and none is built.

* **First-order nodes are Core's** (G5, `coreToSemSM`): every closed program's root, at a flat
  answer, and every first-order callback body.
* **The producer lemmas** (`semSMCallbackOfCore`, `semSMCallbackArrOfCore`,
  `semSMBangCallbackOfCore`, `semSMBangThunkOfCore`, `semSMThunkOfCore`): a callback or closure
  built over a first-order body is the draft's at every index, by the draft's proved `U`, `∀I` and
  `!U` rows composed with G5 at the body.
* **First-order constants** (G5c, `coreToSemSMConst`) at a dead context.
* **The gate** (`LoadGateNil`): the draft-specific step of `withload`'s row, at the empty stack.
* **The seeds**: `pairLoad` and `pairLoadU` (S1, `withload` of a pair of references, at
  `withload`'s type and at its unwinding type); `bangUse` (S3, a persistent lifetime-polymorphic
  combinator written at the top of the program and called inside a load's callback at the
  callback's own lifetime); `corpus/array-get.bc` through the checker (S2's load at `array i32`,
  five cells); `reconB′` (S4, recorded).

The entries' `EntryRead` lemmas show their judgements' `BindersLow` and `Scoped` hold, so a proof
of the entry does not hold because its premises fail.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView)

/-! ### The obligation -/

/-- **An entry**: the draft's semantic judgement at one node of a Core derivation, at every index
(`DraftFL` at that node). -/
abbrev AccNode (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  SemSM (ℍ := ℍ) .binder0 Δ Γ e j

/-- The entry at the empty stack: `SemSMNilOfSemSM`'s corollary of `AccNode`. -/
abbrev AccNodeNil (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  SemSMNil (ℍ := ℍ) .binder0 Δ Γ e j

/-- **The entry is read**: its judgement's binders are no reserved names and its free lifetime
variables are `Δ`'s, so the two premises `SemSM` and `SemSMNil` open with hold, and a proof of the
entry is not vacuous. -/
def EntryRead (Δ : LifeCtx) (Γ : Ctx VTy) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) ∧ Scoped Δ Γ (jdgCty j)

/-! ### Helpers -/

/-- A flat type reaches no `U`. -/
theorem uFreeM_of_flatB : ∀ {k : Nat} {A : VTy}, FlatB k A → UFreeM A
  | _, _, .unit _ | _, _, .zero _ | _, _, .unk _ | _, _, .int _ _ | _, _, .opq _ _ => trivial
  | _, _, .tvar _ => trivial
  | _, _, .tensor hA hB => ⟨uFreeM_of_flatB hA, uFreeM_of_flatB hB⟩
  | _, _, .sum hA hB => ⟨uFreeM_of_flatB hA, uFreeM_of_flatB hB⟩
  | _, _, @FlatB.box _ _ A hA => (uFreeM_of_flatB hA : UFreeM A)
  | _, _, @FlatB.ref _ A hA => (uFreeM_of_flatB hA : UFreeM A)
  | _, _, @FlatB.bang _ A _ hA => (uFreeM_of_flatB hA : UFreeM A)
  | _, _, @FlatB.fam _ L hL => (uFreeM_of_flatB hL : UFreeM L)
  | _, _, @FlatB.mu _ A hA => (uFreeM_of_flatB hA : UFreeM A)

/-- A first-order argument reaches no `U`. -/
theorem uFreeM_of_foArg : ∀ {A : VTy}, FOArg A → UFreeM A
  | _, .flat hA => uFreeM_of_flatB hA
  | _, .mut _ _ | _, .imm _ _ => trivial
  | _, .tensor hA hB => ⟨uFreeM_of_foArg hA, uFreeM_of_foArg hB⟩
  | _, .sum hA hB => ⟨uFreeM_of_foArg hA, uFreeM_of_foArg hB⟩
  | _, @FOArg.box _ A hA => (uFreeM_of_foArg hA : UFreeM A)
  | _, @FOArg.ref A hA => (uFreeM_of_foArg hA : UFreeM A)
  | _, @FOArg.fam L hL => (uFreeM_of_foArg hL : UFreeM L)

/-- A context of first-order slots reaches no `U`. -/
theorem ctx_uFree_of_FO {Γ : Ctx VTy} (h : CtxFO Γ) : ∀ s ∈ Γ, s.live = true → UFreeM s.ty :=
  fun s hs hl => uFreeM_of_foArg (h s hs hl)

/-- A dead context is first-order. -/
theorem ctxFO_of_dead {Γ : Ctx VTy} (h : Ctx.Dead Γ) : CtxFO Γ :=
  fun s hs hl => dead_noLive (P := fun s => FOArg s.ty) h s hs hl

/-- A dead slot in front keeps a context first-order. -/
theorem ctxFO_cons_dead {Γ : Ctx VTy} {S : VTy} (h : CtxFO Γ) : CtxFO (⟨S, false⟩ :: Γ) := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · simp at hl
  · exact h s hs hl

/-- The own lend's hygiene is vacuous at a type with no outer `∀`. -/
theorem ownHyg_of_not_all {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy}
    (h : ∀ x c C', C ≠ .all x c C') : OwnHyg Δ Γ C :=
  fun x c C' hC => absurd hC (h x c C')

/-- A first-order computation type has no outer `∀`. -/
theorem foComp_not_all {C : CTy} (h : FOComp C) : ∀ x c C', C ≠ .all x c C' := by
  intro x c C' hC
  subst hC
  cases h

/-- A dead context is persistent and carried by the box: it has no live slot. -/
theorem persistent_of_dead {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Persistent Γ ∧ PersistentBoxed Γ :=
  ⟨fun s hs hl => dead_noLive (P := fun s => ∃ A, s.ty = .bang A) h s hs hl,
    fun s hs hl => dead_noLive (P := fun s => ∃ B, s.ty = .bang B ∧ ((∃ C, B = .thunk C) ∨ UFreeM B))
      h s hs hl⟩

/-! ### The producer lemmas -/

/-- The `∀I` side conditions from a well-scoped `Δ` and a binder fresh for the context. -/
theorem allI_side {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hfr : CtxFresh x Γ) :
    (∀ y u, Δ.find? y = some u → u.mentions x = false) ∧
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) ∧ (∀ s ∈ Γ, s.live = true → x ∉ VTy.binders s.ty) :=
  ⟨fun _ _ hy => LifeCtx.Ok.bound_mentions_false hΔ hx hy, fun s hs hl => (hfr s hs hl).1,
    fun s hs hl => (hfr s hs hl).2⟩

/-- **A first-order callback at the thunked shape** `∀'x ⊏ b. F (U (A ⊸ F B))`, at a context of
first-order slots the binder avoids: G5 at the λ, `ThunkVRowM`, `AllIRowMAt` at a context reaching
no `U` (`allIRowMUFree0`), and `ThunkVRowM` at the `∀`. -/
def SemSMCallbackOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (A B : VTy) (body : Expr),
    Δ.Ok → Δ.find? x = none → b.mentions x = false → CtxFO Γ → CtxFresh x Γ → FOArg A →
    FlatTy B →
    CDerives (Δ.extend x b) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.val (VTy.all x b (VTy.lolli A B)))

theorem semSMCallbackOfCore : SemSMCallbackOfCore (ℍ := ℍ) := by
  intro Δ Γ x b A B body hΔ hx hb hΓ hfr hA hB h
  have hlam : SemSM (ℍ := ℍ) .binder0 (Δ.extend x b) (⟨.unit, false⟩ :: Γ) (.val (.lam body))
      (.comp (.arr A (.ret B))) :=
    coreToSemSM _ _ _ _ (ctxFO_cons_dead hΓ) (.arr hA (.ret hB)) (.lam h)
  have hthk : SemSM (ℍ := ℍ) .binder0 (Δ.extend x b) (⟨.unit, false⟩ :: Γ) (.val (.lam body))
      (.comp (.ret (.thunk (.arr A (.ret B))))) :=
    statement0UFullM.2.2.2.1 _ _ _ _ rfl (ownHyg_of_not_all fun _ _ _ h => by cases h) hlam
  obtain ⟨hΔx, hΓx, hΓb⟩ := allI_side hΔ hx hfr
  have hall : SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.comp (.all x b (.ret (.thunk (.arr A (.ret B)))))) :=
    allIRowMUFree0 Γ (ctx_uFree_of_FO hΓ) Δ x b _ .unit _ hb hΔx hΓx hx hΓb hthk
  exact statement0UFullM.2.2.2.1 _ _ _ _ rfl (fun _ _ _ h => by cases h; exact ⟨hx, hfr⟩) hall

/-- **The same at the `.arr` shape** `∀'x ⊏ b. A ⊸ F B` (`cInst`'s `polyC`, the unwinding
constants' `cbUTy` at the empty row). -/
def SemSMCallbackArrOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (A B : VTy) (body : Expr),
    Δ.Ok → Δ.find? x = none → b.mentions x = false → CtxFO Γ → CtxFresh x Γ → FOArg A →
    FlatTy B →
    CDerives (Δ.extend x b) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.val (.thunk (.all x b (.arr A (.ret B)))))

theorem semSMCallbackArrOfCore : SemSMCallbackArrOfCore (ℍ := ℍ) := by
  intro Δ Γ x b A B body hΔ hx hb hΓ hfr hA hB h
  have hlam : SemSM (ℍ := ℍ) .binder0 (Δ.extend x b) (⟨.unit, false⟩ :: Γ) (.val (.lam body))
      (.comp (.arr A (.ret B))) :=
    coreToSemSM _ _ _ _ (ctxFO_cons_dead hΓ) (.arr hA (.ret hB)) (.lam h)
  obtain ⟨hΔx, hΓx, hΓb⟩ := allI_side hΔ hx hfr
  have hall : SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.comp (.all x b (.arr A (.ret B)))) :=
    allIRowMUFree0 Γ (ctx_uFree_of_FO hΓ) Δ x b _ .unit _ hb hΔx hΓx hx hΓb hlam
  exact statement0UFullM.2.2.2.1 _ _ _ _ rfl (fun _ _ _ h => by cases h; exact ⟨hx, hfr⟩) hall

/-- **A persistent first-order callback at a dead context**, at every lifetime context its binder
is fresh for and every bound: `d_algI`'s algebras, `c₀V`, a top-level persistent combinator. The
`!U` row at the box (`BangThunkVRowM`) over the callback's `∀`. -/
def SemSMBangCallbackOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (A B : VTy) (body : Expr),
    Δ.Ok → Δ.find? x = none → b.mentions x = false → Ctx.Dead Γ → FOArg A → FlatTy B →
    CDerives (Δ.extend x b) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.comp (.ret B)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.val (.bang (VTy.all x b (VTy.lolli A B))))

theorem semSMBangCallbackOfCore : SemSMBangCallbackOfCore (ℍ := ℍ) := by
  intro Δ Γ x b A B body hΔ hx hb hΓ hA hB h
  have hΓFO := ctxFO_of_dead hΓ
  have hfr : CtxFresh x Γ := fun s hs hl =>
    dead_noLive (P := fun s => ¬ VFree x s.ty ∧ x ∉ VTy.binders s.ty) hΓ s hs hl
  have hlam : SemSM (ℍ := ℍ) .binder0 (Δ.extend x b) (⟨.unit, false⟩ :: Γ) (.val (.lam body))
      (.comp (.arr A (.ret B))) :=
    coreToSemSM _ _ _ _ (ctxFO_cons_dead hΓFO) (.arr hA (.ret hB)) (.lam h)
  have hthk : SemSM (ℍ := ℍ) .binder0 (Δ.extend x b) (⟨.unit, false⟩ :: Γ) (.val (.lam body))
      (.comp (.ret (.thunk (.arr A (.ret B))))) :=
    statement0UFullM.2.2.2.1 _ _ _ _ rfl (ownHyg_of_not_all fun _ _ _ h => by cases h) hlam
  obtain ⟨hΔx, hΓx, hΓb⟩ := allI_side hΔ hx hfr
  have hall : SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.comp (.all x b (.ret (.thunk (.arr A (.ret B)))))) :=
    allIRowMUFree0 Γ (ctx_uFree_of_FO hΓFO) Δ x b _ .unit _ hb hΔx hΓx hx hΓb hthk
  obtain ⟨hP, hPB⟩ := persistent_of_dead hΓ
  exact statement0UFullM.2.2.2.2.2 _ _ _ _ hP hPB rfl
    (fun _ _ _ h => by cases h; exact ⟨hx, hfr⟩) hall

/-- **A persistent thunk of a first-order computation type at a dead context** (`cBang`'s closure,
`counterStep`, `tab10V`, `d_algO`'s algebras): G5 at the λ, then the `!U` row. -/
def SemSMBangThunkOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), Ctx.Dead Γ → C.isRet = false →
    FOComp C → CDerives Δ Γ (.val (.lam N)) (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.val (.bang (.thunk C)))

theorem semSMBangThunkOfCore : SemSMBangThunkOfCore (ℍ := ℍ) := by
  intro Δ Γ N C hΓ hC hFO h
  obtain ⟨hP, hPB⟩ := persistent_of_dead hΓ
  exact statement0UFullM.2.2.2.2.2 _ _ _ _ hP hPB hC (ownHyg_of_not_all (foComp_not_all hFO))
    (coreToSemSM _ _ _ _ (ctxFO_of_dead hΓ) hFO h)

/-- **A thunk of a first-order computation type at a context of first-order slots** (`cMethods`,
`pushG`, `withswap`'s callbacks): G5 at the λ, then `ThunkVRowM`. -/
def SemSMThunkOfCore : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxFO Γ → C.isRet = false → FOComp C →
    CDerives Δ Γ (.val (.lam N)) (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.val (.thunk C))

theorem semSMThunkOfCore : SemSMThunkOfCore (ℍ := ℍ) := by
  intro Δ Γ N C hΓ hC hFO h
  exact statement0UFullM.2.2.2.1 _ _ _ _ hC (ownHyg_of_not_all (foComp_not_all hFO))
    (coreToSemSM _ _ _ _ hΓ hFO h)

/-! ### The consumer gate (`withload`'s draft step at the empty stack) -/

/-- `withload`'s callback type at the thunked shape: `∀'x ⊏ c. F (U (Imm̲ 'x A ⊸ F ['x] B))`'s
body. -/
abbrev loadCbF (A B : VTy) (x : LifeVar) : CTy :=
  .ret (.lolli (A.immReborrow (.var x)) (.box (.var x) B))

/-- The same at the `.arr` shape (`withloadU`'s `cbUTy` at the empty row). -/
abbrev loadCbU (A B : VTy) (x : LifeVar) : CTy :=
  .arr (A.immReborrow (.var x)) (.ret (.box (.var x) B))

/-- **The payload a load reborrows at `ℓ`**, by `withload_compatX`'s two cases of `CohE`: the
value and payload of the record whose cell `ℓ` is (`TW.reb`), or the value a chain of `Ref` steps
from a record's value reaches, with the witness of the `imm` cell there (`TW.rebDeep`). In both,
the world's cell at `ℓ` is `imm(s, u, R)`. -/
def LoadPay (W : WRes) (rs : List FrameRec) (ℓ : BoCa.Loc) (u : Val) (R : WRes) : Prop :=
  (∃ (s : LSet) (h : R.InStratum s.join), W.get ℓ = some (CellU.immOf s u R h)) ∧
    ((∃ r ∈ rs, ℓ = r.le ∧ u = r.v ∧ R = r.R) ∨
      ∃ r ∈ rs, ∃ (p : Option BoCa.Loc) (S₀ : VTy), Chain r.R r.T r.v p ℓ S₀ u)

/-- **The `withload` gate at the empty stack** (single-entry form): at a view `CohE` admits,
whichever of its two cases, [TR] 6.175's argument, the payload reborrowed at a fresh `β`, is
admitted by some own push of the callback, related at the pushed index, with the composite meeting
the guard there. `x ∉ CTy.binders (C' x)` is added: the own push names the binder, which the body
must not bind again (`OwnPushI`), and Core's typing does not exclude it. -/
def LoadGateNil (A : VTy) (C' : LifeVar → CTy) : Prop :=
  ∀ (δ : LSub) (ls : List SRec) (W : WRes) (ℓ : BoCa.Loc) (u : Val) (R : WRes) (x : LifeVar)
    (c : Lifetime.Life) (β : Life) (cb ρc ρ : WRes),
    CohE (rsOf ls) ℓ A δ → LoadPay W (rsOf ls) ℓ u R → ¬ VFree x A → δ.find? x = none →
    x ∉ CTy.binders (C' x) →
    (∀ y, VFree y A → δ.find? y ≠ none) → ResU.Reb β R cb →
    vC true (A.immReborrow (.var x)) ls (δ.extend x β) u cb →
    ρc.InStratum β → β < ⊤ → LtLife δ c β → RecsOutside [β] ls → SubFresh δ β →
    (∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ) →
    ResU.CompS ρc cb ρ →
    ∃ en : LEnt, OwnPushM δ (.all x c (C' x)) ρc ([], []) en β ∧
      vRLM (ℍ := ℍ) .binder0 none [en] (δ.extend x β) (A.immReborrow (.var x)) [β] ls u cb ∧
      TabAtS [en] [β] ρ ∧ PlaceViewsL (extS (δ.extend x β) [en] [β]) [en] [β] ls ρ

/-- **Every resource leaves a place free at every depth.** `[TR]`'s `Res` is finite at every depth
(the stratification, `docs/adjudications.md` D10), so one exists; proved as `freePlaceExists`
(`GroundBlock.lean`).
The own push at a payload with no reborrowed cell lends such a place. -/
def FreePlaceExists : Prop := ∀ ρ : WRes, ∃ l : BoCa.Loc, ∀ ψ, ¬ DeepAt ρ l ψ

/-- **The gate at a payload with no reborrowed cell** (`1`), from what it reads: the reborrowed
resource is empty, and one own push at a free place with a closed payload type admits it. -/
theorem loadGateNil_unit_of (hfree : FreePlaceExists) (C' : LifeVar → CTy)
    (hnarr : ∀ x A D, C' x ≠ .arr A D ∨ ∀ (en : LEnt), ViewAt x en A) {δ : LSub}
    {ls : List SRec} {u : Val} {x : LifeVar} {c : Lifetime.Life} {β : Life} {cb ρc ρ : WRes}
    (hbind : x ∉ CTy.binders (C' x))
    (hv : vC true (VTy.unit.immReborrow (.var x)) ls (δ.extend x β) u cb)
    (hst : ρc.InStratum β) (hlt : LtLife δ c β) (hc : ResU.CompS ρc cb ρ) :
    ∃ en : LEnt, OwnPushM δ (.all x c (C' x)) ρc ([], []) en β ∧
      vRLM (ℍ := ℍ) .binder0 none [en] (δ.extend x β) (VTy.unit.immReborrow (.var x)) [β] ls u
        cb ∧
      TabAtS [en] [β] ρ ∧ PlaceViewsL (extS (δ.extend x β) [en] [β]) [en] [β] ls ρ := by
  have hcb : cb = PMap.empty := hv.1
  subst hcb
  have hρ : ρ = ρc := ResU.CompS.functional hc (ResU.comp_empty_right ρc)
  subst hρ
  obtain ⟨l₀, hl₀⟩ := hfree ρ
  let en : LEnt := ⟨l₀, x, .unit, .imm .unit, fun _ => true⟩
  refine ⟨en, ⟨⟨x, c, C' x, rfl, rfl, hbind,
    ⟨⟨List.isChain_singleton β, hst, List.not_mem_nil, List.not_mem_nil,
      fun y hy => absurd hy (by simp [en, VFree])⟩, hl₀⟩, hlt, fun A D hCD => ?_⟩,
    fun y hy => absurd hy (by simp [en, VFree]), fun h => h⟩, hv,
    GhostEnd.tabAtS_one.mpr (GhostEnd.tabAt_of_inStratum hst), ⟨fun l ψ hex _ e' α hi => ?_,
      fun l ψ hd _ hl => ?_⟩⟩
  · rcases hnarr x A D with h | h
    · exact absurd hCD h
    · exact h en
  · obtain ⟨hm, hel⟩ := innerAt_mem hi
    have hp : (e', α) = (en, β) := List.mem_singleton.mp hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hp
    have hl : l = l₀ := hel.symm
    subst hl
    exact absurd (ExAt.toDeepAt hex) (hl₀ ψ)
  · have : l = l₀ := by simpa [en] using hl
    subst this
    exact absurd hd (hl₀ ψ)

/-- **The gate at a payload with no reborrowed cell** (`1`): `loadGateNil_unit_of`, which reads
neither the reborrow's structure nor the callback's freedom at the reborrowed places. From
`FreePlaceExists`. -/
theorem loadGateNil_unit (hfree : FreePlaceExists) (C' : LifeVar → CTy)
    (hnarr : ∀ x A D, C' x ≠ .arr A D ∨ ∀ (en : LEnt), ViewAt x en A) :
    LoadGateNil (ℍ := ℍ) .unit C' := by
  intro δ ls W ℓ u R x c β cb ρc ρ _ _ _ _ hbind _ _ hv hst _ hlt _ _ _ hc
  exact loadGateNil_unit_of hfree C' hnarr hbind hv hst hlt hc

/-! ### `EntryRead` and the callback shape `callbackW` builds -/

/-- Discharges `EntryRead` at a concrete judgement: the types' binders are small names and their
free variables `Δ`'s. -/
syntax "entry_read" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| entry_read) => `(tactic| entry_read [])
  | `(tactic| entry_read [$ls,*]) => `(tactic| (simp [EntryRead, BindersLow, Scoped, CScoped, VScoped,
      GhostEnd.jdgCty, CTy.binders, VTy.binders, CFree, VFree, NsVar, nsBase,
      Lifetime.Life.mentions, VTy.immReborrow, LifeCtx.meetOfDom, Lifetime.meetOfDomL,
      LifeCtx.extend, LifeCtx.find?, Lifetime.assocFind, LifeCtx.empty, natN, natBody, pureL,
      pureBody, listL, listBody, FShape.resRH, FShape.resO, FShape.ty, Shape.famTy, Shape.valTy,
      famTy2, cbTy2, cbT, VTy.lolli, VTy.rename, $ls,*] <;>
      (intros; first | omega | simp_all | (rename_i h; rcases h with h | h <;> simp_all))))

/-- **A callback `callbackW` builds** (`thunk Λ. return (λx. body)` at a fresh `'x ⊏ ⊓Δ`, its body
at a value judgement), at a dead context: `semSMCallbackOfCore` at the body. -/
theorem semSM_callbackW {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {A B : VTy} {body : Expr}
    (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ) (hA : FOArg A) (hB : FlatTy B)
    (h : CDerives (Δ.extend x Δ.meetOfDom) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.val B)) :
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam (.val (.lam body))))
      (.val (VTy.all x Δ.meetOfDom (VTy.lolli A B))) :=
  semSMCallbackOfCore Δ Γ x _ A B body hΔ hx
    (Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf Δ.entries))
    (ctxFO_of_dead hΓ) (fun s hs hl => dead_noLive (P := fun s => ¬ VFree x s.ty ∧
      x ∉ VTy.binders s.ty) hΓ s hs hl) hA hB (.ret h)

/-- **A persistent algebra `d_algI` builds** (`!thunk Λ. return (λr. M)` at `'0 ⊏ ⊓∅`), at a dead
context: `semSMBangCallbackOfCore` at the body. -/
theorem semSM_algI {Γ : Ctx VTy} {A R : VTy} {M : Expr} (hΓ : Ctx.Dead Γ) (hA : FOArg A)
    (hR : FlatTy R)
    (h : CDerives (LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom)
      (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) M (.comp (.ret R))) :
    SemSM (ℍ := ℍ) .binder0 LifeCtx.empty Γ (.val (.lam (.val (.lam M))))
      (.val (.bang (VTy.all 0 LifeCtx.empty.meetOfDom (VTy.lolli A R)))) :=
  semSMBangCallbackOfCore _ Γ 0 _ A R M ok_empty rfl rfl hΓ hA hR h

/-- G5c at a dead context, for a value given as an expression with its `IsVal` proof. -/
theorem semSM_const {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} (he : IsVal e)
    (hΓ : Ctx.Dead Γ) (hA : FOConstTy A) (h : CDerives Δ Γ e (.val A)) :
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A) :=
  coreToSemSMConst Δ Γ ⟨e, he⟩ A hΓ hA h

/-- G5 at a closed program at a flat answer. -/
theorem semSM_root {Δ : LifeCtx} {e : Expr} {B : VTy} (hB : FlatTy B)
    (h : CDerives Δ [] e (.comp (.ret B))) : SemSM (ℍ := ℍ) .binder0 Δ [] e (.comp (.ret B)) :=
  coreToSemSM Δ [] e _ (fun _ hs => absurd hs List.not_mem_nil) (.ret hB) h

/-- G5 at a closed program judged at a flat value type. -/
theorem semSM_rootV {Δ : LifeCtx} {e : Expr} {B : VTy} (hB : FlatTy B)
    (h : CDerives Δ [] e (.val B)) : SemSM (ℍ := ℍ) .binder0 Δ [] e (.val B) :=
  coreToSemSM Δ [] e _ (fun _ hs => absurd hs List.not_mem_nil) (.ret hB) h

/-! ### P1 `cImmBorrow` (`Core/Examples.lean`): `withbor` (1) at `1`, `withload` at `1` -/

/-- R: the closed program at `F 1`. -/
def AccImmBorrowRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] cImmBorrow (.comp (.ret .unit))

/-- V1: the borrower at `borrowerTy 1`, at a dead context. -/
def AccImmBorrowCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (borrower cLoader) (.val (borrowerTy .unit))

/-- V2: the loader at `loaderTy 1`, at `Δ₁` and a dead context. -/
def AccImmBorrowLoader : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ cLoader (.val (loaderTy .unit))

/-- K1: `withbor` (1) at `1`. NOT BUILT: `Withbor1RowM` (the port of `withbor1_compatX`); its
draft step `CallbackExtImmMF`, stated. -/
def AccImmBorrowWithbor : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ withbor
    (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom .unit .unit))

/-- K2: `withload` at `1` (no reborrowed cell). NOT BUILT: `WithloadRowM`; its draft step, the
gate at `1`, is `loadGateNil_unit` from `FreePlaceExists`. -/
def AccImmBorrowWithload : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload
    (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom .unit (.box (.var 0) .unit)))

/-- K3: `alloc` at `1`. -/
def AccImmBorrowAlloc : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val (.prim .alloc)) (.val (.lolli .unit (.ref .unit)))

/-- K4: `free` at `Ref 1`. -/
def AccImmBorrowFree : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val (.prim .free)) (.val (.lolli (.ref .unit) .unit))

theorem accImmBorrowRoot : AccImmBorrowRoot (ℍ := ℍ) := semSM_root (.unit 0) cImmBorrow_derives

theorem accImmBorrowCb : AccImmBorrowCb (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW ok_empty rfl hΓ (.imm _ _) (.box (.unit 0))
    (CDerives.ofRet (d_borrowBody hΓ (by simp [VFree]) d_loader))

/-- The loader's body, `λy. y` boxed twice, rebuilt from `d_loader`'s constructors. -/
theorem d_loaderBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives (Δ₁.extend 1 Δ₁.meetOfDom) (⟨VTy.immReborrow (.var 1) .unit, true⟩ ::
      ⟨.unit, false⟩ :: Γ) (.var 0) (.val (.box (.var 1) (.box (.var 0) .unit))) :=
  .boxI (.boxI (.var (.here (.cons hΓ)))
      (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons hΓ)))
    (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons hΓ))

theorem accImmBorrowLoader : AccImmBorrowLoader (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW (by decide) rfl hΓ (.flat (.unit 0)) (.box (.box (.unit 0))) (d_loaderBody hΓ)

theorem accImmBorrowAlloc : AccImmBorrowAlloc (ℍ := ℍ) := fun _ hΓ =>
  semSM_const .prim hΓ (.thunk (.arr (.flat (.unit 0)) (.ret (.ref (.unit 0))))) (.alloc hΓ.toP)

theorem accImmBorrowFree : AccImmBorrowFree (ℍ := ℍ) := fun _ hΓ =>
  semSM_const .prim hΓ (.thunk (.arr (.flat (.ref (.unit 0))) (.ret (.unit 0)))) (.free hΓ.toP)

theorem readImmBorrow :
    EntryRead LifeCtx.empty [] (.comp (.ret .unit)) ∧
    EntryRead LifeCtx.empty [] (.val (borrowerTy .unit)) ∧
    EntryRead Δ₁ [] (.val (loaderTy .unit)) ∧
    EntryRead LifeCtx.empty [] (.val (.lolli .unit (.ref .unit))) ∧
    EntryRead LifeCtx.empty [] (.val (.lolli (.ref .unit) .unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · entry_read
  · entry_read [borrowerTy]
  · entry_read [loaderTy, Δ₁]
  · entry_read
  · entry_read

/-! ### Flat types the programs use -/

theorem flat_natN : FlatTy natN := .mu (.sum (.unit 1) (.tvar (by decide)))

theorem flatB_natN (k : Nat) : FlatB k natN := .mu (.sum (.unit _) (.tvar (by omega)))

theorem flat_listL : FlatTy listL := .mu (.sum (.unit 1) (.ref (.tvar (by decide))))

theorem flat_clistL : FlatTy clistL := by
  show FlatB 0 (VTy.mu (.sum .unit (.tensor (.ref natN) (.ref (.tvar 0)))))
  exact .mu (.sum (.unit 1) (.tensor (.ref (flatB_natN 1)) (.ref (.tvar (by decide)))))

theorem flat_ilistL : FlatTy ilistL :=
  .mu (.sum (.unit 1) (.tensor (.ref (.int 1 .w32)) (.ref (.tvar (by decide)))))

theorem flat_BB (k : Nat) : FlatB k BB := .sum (.unit k) (.unit k)

/-! ### P2 `cRecBorrow` (`Core/Examples.lean`): a borrowed record of methods -/

def AccRecBorrowRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] cRecBorrow (.comp (.ret .unit))

/-- V: the record of methods `cMethods` at `methodsTy = U (F 1 & F 1)`, a first-order closure. -/
def AccRecBorrowMethods : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ cMethods (.val methodsTy)

/-- V: the borrower at `borrowerTy methodsTy`. -/
def AccRecBorrowCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (borrower cRecLoader) (.val (borrowerTy methodsTy))

/-- V: the loader at `loaderTy methodsTy`, its argument `Imm̲ 'b methodsTy = Unk`. -/
def AccRecBorrowLoader : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ cRecLoader (.val (loaderTy methodsTy))

/-- K: `withbor` (1) at `methodsTy`. NOT BUILT: `Withbor1RowM`. -/
def AccRecBorrowWithbor : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ withbor
    (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom methodsTy .unit))

/-- K: `alloc` at `methodsTy`, a thunk payload. NOT BUILT: `AllocRowM` (outside G5c). -/
def AccRecBorrowAlloc : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val (.prim .alloc)) (.val (.lolli methodsTy (.ref methodsTy)))

/-- K: `forget` at `Unk`. -/
def AccRecBorrowForget : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ forget (.val axForgetUnkTy)

theorem accRecBorrowRoot : AccRecBorrowRoot (ℍ := ℍ) := semSM_root (.unit 0) cRecBorrow_derives

theorem accRecBorrowMethods : AccRecBorrowMethods (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.thunk (.amp (.ret (.unit 0)) (.ret (.unit 0)))) (d_methods hΓ)

theorem accRecBorrowCb : AccRecBorrowCb (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW ok_empty rfl hΓ (.imm _ _) (.box (.unit 0))
    (CDerives.ofRet (d_borrowBody hΓ (methodsTy_closed 1) d_recLoader))

/-- The record loader's body, rebuilt from `d_recLoader`'s constructors. -/
theorem d_recLoaderBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives (Δ₁.extend 1 Δ₁.meetOfDom) (⟨VTy.immReborrow (.var 1) methodsTy, true⟩ ::
      ⟨.unit, false⟩ :: Γ) (bindE forget (bindE (.app (.var 0) (.var 1)) (.var 0)))
      (.comp (.ret (.box (.var 1) (.box (.var 0) .unit)))) :=
  .bind (.right (.dead (deadSplit hΓ))) (.ret (.forgetUnk (.cons (.cons hΓ))))
    (.bind (.left (.left (.dead (deadSplit hΓ))))
      (.app (.left (.right (.dead (deadSplit hΓ))))
        (.force (.here (.cons (.cons hΓ)))) (.there (.here (.cons hΓ))))
      (.ret (.boxI
        (.boxI (.var (.here (.cons (.cons (.cons hΓ)))))
          (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (.cons (.cons hΓ)))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit
          (.cons (.cons (.cons hΓ)))))))

theorem accRecBorrowLoader : AccRecBorrowLoader (ℍ := ℍ) := fun Γ hΓ =>
  semSMCallbackOfCore Δ₁ Γ 1 _ _ _ _ (by decide) rfl rfl (ctxFO_of_dead hΓ)
    (fun s hs hl => dead_noLive (P := fun s => ¬ VFree 1 s.ty ∧ 1 ∉ VTy.binders s.ty) hΓ s hs hl)
    (.flat (.unk 0)) (.box (.box (.unit 0))) (d_recLoaderBody hΓ)

theorem accRecBorrowForget : AccRecBorrowForget (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.thunk (.arr (.flat (.unk 0)) (.ret (.unit 0)))) (.forgetUnk hΓ.toP)

/-! ### P3 `cBang` (`Core/Examples.lean`): a persistent closure used twice and dropped -/

def AccBangRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] cBang (.comp (.ret .unit))

/-- V: `λx. x` at `!U(1 ⊸ F 1)`, the derivation's own `bangThunkV`. -/
def AccBangClosure : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val (.lam (.var 0))) (.val (.bang (.thunk (.arr .unit (.ret .unit)))))

theorem accBangRoot : AccBangRoot (ℍ := ℍ) := semSM_root (.unit 0) cBang_derives

theorem accBangClosure : AccBangClosure (ℍ := ℍ) :=
  semSMBangThunkOfCore _ [] _ _ .nil rfl (.arr (.flat (.unit 0)) (.ret (.unit 0)))
    (.lam (.ret (.var (.here .nil))))

/-! ### P4 `cInst` (`Core/Examples.lean`): `∀E` at a computation type that is not an `F` -/

def AccInstRoot : Prop := AccNode (ℍ := ℍ) Δ₁ [] cInst (.comp (.ret .unit))

/-- V: `Λ. λy. return y` at `U polyC`, the `.arr` shape. -/
def AccInstPoly : Prop :=
  AccNode (ℍ := ℍ) Δ₁ [] (.val (.lam (.val (.lam (.var 0))))) (.val (.thunk polyC))

theorem accInstRoot : AccInstRoot (ℍ := ℍ) := semSM_root (.unit 0) cInst_derives

theorem accInstPoly : AccInstPoly (ℍ := ℍ) :=
  semSMCallbackArrOfCore Δ₁ [] 1 _ _ _ _ (by decide) rfl rfl
    (fun _ hs => absurd hs List.not_mem_nil) (fun _ hs => absurd hs List.not_mem_nil)
    (.flat (.box (.unit 0))) (.unit 0) (.ret (.boxE (.var (.here (.cons .nil)))))

/-! ### P5 `readFields` (`Core/RecordPrograms.lean`): reading a record's fields through a borrow -/

def AccReadFieldsRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] readFields (.val .unit)

/-- V: the borrower `readBorrower`, its body `d_readBody`. -/
def AccReadFieldsCb : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] readBorrower
    (.val (.all 0 LifeCtx.empty.meetOfDom
      (.lolli (.imm (.var 0) Pt.valTy) (.box (.var 0) (.tensor BB BB)))))

/-- K: `withload` at `Pt.valTy = BB ⊗ Ref BB`, one reborrowed cell (the positive control).
NOT BUILT: `WithloadRowM`; its gate at one cell is attempted with the block (part (3)). -/
def AccReadFieldsLoad : Prop := ∀ Γ : Ctx VTy, Ctx.DeadP Γ →
  AccNode (ℍ := ℍ) D1 Γ withload
    (.val (axWithloadTy (.var 0) 1 D1.meetOfDom Pt.valTy (.box (.var 1) BB)))

/-- K: `copy` at `Imm '0 Pt.valTy`. NOT BUILT: `CopyRowM` (its answer holds `Imm` leaves, D7). -/
def AccReadFieldsCopy : Prop := ∀ Γ : Ctx VTy, Ctx.DeadP Γ →
  AccNode (ℍ := ℍ) D1 Γ copy (.val (axCopyTy (.var 0) Pt.valTy))

/-- K: `alloc` at `Pt.valTy`, flat. -/
def AccReadFieldsAlloc : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ (.val (.prim .alloc)) (.val (.lolli Pt.valTy (.ref Pt.valTy)))

theorem accReadFieldsRoot : AccReadFieldsRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_readFields

theorem accReadFieldsCb : AccReadFieldsCb (ℍ := ℍ) :=
  semSM_callbackW ok_empty rfl .nil (.imm _ _) (.box (.tensor (flat_BB 0) (flat_BB 0))) d_readBody

theorem accReadFieldsAlloc : AccReadFieldsAlloc (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .prim hΓ
    (.thunk (.arr (.flat (.tensor (flat_BB 0) (.ref (flat_BB 0))))
      (.ret (.ref (.tensor (flat_BB 0) (.ref (flat_BB 0))))))) (.alloc hΓ.toP)

/-! ### P6 `mutFields` (`Core/RecordPrograms.lean`): updating fields through a mutable borrow -/

def AccMutFieldsRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] mutFields (.val .unit)

/-- V: `flipG`, a first-order closure. -/
def AccMutFieldsFlip : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ flipG (.val (.lolli BB (.tensor BB .unit)))

/-- V: `pokeG`, a first-order closure that lends inside its body (`withbor` (2), `withswap`). -/
def AccMutFieldsPoke : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) D1 Γ pokeG (.val (.lolli (.ref BB) (.tensor (.ref BB) .unit)))

/-- K: `withswap` at `Pt.valTy`. NOT BUILT: `WithswapRowM` (D7). -/
def AccMutFieldsSwap : Prop := ∀ (Γ : Ctx VTy) (a : Lifetime.Life), Ctx.DeadP Γ →
  AccNode (ℍ := ℍ) D1 Γ withswap (.val (axWithswapTy a Pt.valTy .unit))

theorem accMutFieldsRoot : AccMutFieldsRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_mutFields

theorem accMutFieldsFlip : AccMutFieldsFlip (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.thunk (.arr (.flat (flat_BB 0)) (.ret (.tensor (flat_BB 0) (.unit 0)))))
    (d_flipG hΓ)

theorem accMutFieldsPoke : AccMutFieldsPoke (ℍ := ℍ) := fun _ hΓ =>
  semSM_const .lam hΓ
    (.thunk (.arr (.flat (.ref (flat_BB 0))) (.ret (.tensor (.ref (flat_BB 0)) (.unit 0)))))
    (d_pokeG hΓ)

/-! ### P14 `exProg`, P15 `build3`, P16 `matchSome`, P17 `bagProg` -/

def AccExProgRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] exProg (.comp (.ret .unit))

/-- V: `⟨return (), ⟨⟩⟩` at `U (F 1 & ⊤)`, a first-order closure. -/
def AccExProgPair : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ (withPair (.val .unit) (.val .unit)) (.val (.thunk (.amp (.ret .unit) .top)))

theorem accExProgRoot : AccExProgRoot (ℍ := ℍ) := semSM_root (.unit 0) exProg_derives

theorem accExProgPair : AccExProgPair (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.thunk (.amp (.ret (.unit 0)) .top))
    (.thunkV rfl (.withI (.ret (.unitI (.cons (.cons hΓ)))) .topI))

def AccBuild3Root : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] build3 (.val listL)

theorem accBuild3Root : AccBuild3Root (ℍ := ℍ) := semSM_rootV flat_listL build3_derives

def AccMatchSomeRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] matchSome (.val .unit)

theorem accMatchSomeRoot : AccMatchSomeRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_matchSome

def AccBagRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] bagProg (.val .unit)

/-- V: `pushG`, a first-order closure at `L ⊸ F (L ⊗ 1)`. -/
def AccBagPush : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ pushG (.val (.lolli clistL (.tensor clistL .unit)))

theorem accBagRoot : AccBagRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_bagProg

theorem accBagPush : AccBagPush (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.thunk (.arr (.flat flat_clistL) (.ret (.tensor flat_clistL (.unit 0)))))
    (d_pushG hΓ)

/-! ### Family and block borrows: P7 `readFamily`, P8 `swapBothB`, P18 `swapBothL`, P19
`splitFour`, P9 `blockSwap`, P20 `nestSwap`, P21 `blockRead`, P22 `nestRead`, P23 `bagBlock`,
P24 `crossPack` -/

section FamilyBlock
open BoCa.Programs (alloc' free' app2 unitNoLeak entailsLt_top interp_meet_left)

def AccReadFamilyRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] readFamily (.val .unit)
def AccSwapBothBRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] swapBothB (.val .unit)
def AccSwapBothLRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] swapBothL (.val .unit)
def AccSplitFourRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] splitFour (.val .unit)
def AccBlockSwapRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] blockSwap (.val .unit)
def AccNestSwapRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] nestSwap (.val .unit)
def AccBlockReadRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] blockRead (.val .unit)
def AccNestReadRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] nestRead (.val .unit)
def AccBagBlockRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] bagBlock (.val .unit)
def AccCrossPackRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] crossPack (.val .unit)

theorem accReadFamilyRoot : AccReadFamilyRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_readFamily
theorem accSwapBothBRoot : AccSwapBothBRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_swapBothB
theorem accSwapBothLRoot : AccSwapBothLRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_swapBothL
theorem accSplitFourRoot : AccSplitFourRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_splitFour
theorem accBlockSwapRoot : AccBlockSwapRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_blockSwap
theorem accNestSwapRoot : AccNestSwapRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_nestSwap
theorem accBlockReadRoot : AccBlockReadRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_blockRead
theorem accNestReadRoot : AccNestReadRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_nestRead
theorem accBagBlockRoot : AccBagBlockRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_bagBlock
theorem accCrossPackRoot : AccCrossPackRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_crossPack

/-- V: `readCb` (P7, P21), a first-order callback at the family `Imm 'c B ⊗ Imm 'c B`; its body
calls the persistent `readOne`, `readBoth` at the callback's own variable, which G5 does not open. -/
def AccReadCb : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] readCb (.val (cbTy2 immM 0 LifeCtx.empty.meetOfDom BB BB B3))

theorem accReadCb : AccReadCb (ℍ := ℍ) :=
  semSM_callbackW ok_empty rfl .nil (.tensor (.imm _ _) (.imm _ _))
    (.box (.tensor (flat_BB 0) (.tensor (flat_BB 0) (flat_BB 0)))) <|
    letW (A := .imm (.var 0) BB) (B := .imm (.var 0) BB) (.var (by csolo)) <|
    letW (A := .imm (.var 0) BB) (B := .imm (.var 0) BB)
      (appW (.var (by csolo)) (.copy (by cdead))) <|
    eletW (appW (.var (by csolo)) (d_readOneAt d1_ok (by cdead) 0 5 6 rfl rfl rfl rfl)) <|
    eletW
      (appW (pairW (.var (by csolo)) (.var (by csolo)))
        (.allEV (x := 5) (b := .top) (A := .lolli (famTy2 immM (.var 5) BB BB) (.tensor BB BB))
          (a := .var 0) (d_readBoth d1_ok (by cdead) 5 6 7 rfl rfl rfl rfl) (entailsLt_top rfl))) <|
    .boxI (pairW (.var (by csolo)) (.var (by csolo)))
      (outlives_two (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (outlives_of_dataB rfl)
        (by cdead))

/-- V: `swapCb` (P8, P9, P18 at `B`), a first-order callback at `Mut 'c A ⊗ Mut 'c A`. -/
def AccSwapCb (A : VTy) : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] swapCb (.val (cbTy2 mutM 0 LifeCtx.empty.meetOfDom A A .unit))

theorem accSwapCb {A : VTy} : AccSwapCb (ℍ := ℍ) A :=
  semSM_callbackW ok_empty rfl .nil (.tensor (.mut _ _) (.mut _ _)) (.box (.unit 0)) <|
    letW (A := .mut (.var 0) A) (B := .mut (.var 0) A) (.var (by csolo)) <|
    letW (A := .mut (.var 0) A) (B := .unit)
      (appW (d_swapOut (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

/-- V: `nestCb` (P20), a first-order callback at the block `σ3`'s family of `Mut` leaves. -/
def AccNestCb : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] nestCb (.val (cbT mutM 0 LifeCtx.empty.meetOfDom σ3 .unit))

theorem accNestCb : AccNestCb (ℍ := ℍ) :=
  semSM_callbackW ok_empty rfl .nil (.tensor (.tensor (.mut _ _) (.mut _ _)) (.mut _ _))
    (.box (.unit 0)) <|
    letW (A := .tensor (.mut (.var 0) BB) (.mut (.var 0) BB)) (B := .mut (.var 0) BB)
      (.var (by csolo)) <|
    letW (A := .mut (.var 0) BB) (B := .mut (.var 0) BB) (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    letW (A := .mut (.var 0) BB) (B := .mut (.var 0) BB)
      (appW (pairW (.var (by csolo)) (.var (by csolo)))
        (d_swapFnAtVar d1_ok (by cdead) 0 5 (u := LifeCtx.empty.meetOfDom) rfl rfl rfl)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

/-- V: `nestReadCb` (P22), a first-order callback at `σ3`'s family of `Imm` leaves. -/
def AccNestReadCb : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] nestReadCb (.val (cbT immM 0 LifeCtx.empty.meetOfDom σ3 B21))

theorem accNestReadCb : AccNestReadCb (ℍ := ℍ) :=
  semSM_callbackW ok_empty rfl .nil (.tensor (.tensor (.imm _ _) (.imm _ _)) (.imm _ _))
    (.box (.tensor (.tensor (flat_BB 0) (flat_BB 0)) (flat_BB 0))) <|
    letW (A := famTy2 immM (.var 0) BB BB) (B := .imm (.var 0) BB) (.var (by csolo)) <|
    letW (A := .tensor BB BB) (B := BB)
      (pairW
        (appW (.var (by csolo))
          (.allEV (x := 5) (b := .top) (A := .lolli (famTy2 immM (.var 5) BB BB) (.tensor BB BB))
            (a := .var 0) (d_readBoth d1_ok (by cdead) 5 6 7 rfl rfl rfl rfl) (entailsLt_top rfl)))
        (appW (.var (by csolo)) (d_readOneAt d1_ok (by cdead) 0 5 6 rfl rfl rfl rfl))) <|
    .boxI (pairW (.var (by csolo)) (.var (by csolo)))
      (outlives_two (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (outlives_of_dataB rfl)
        (by cdead))

/-- V: `bagCb` (P23), a first-order callback at `bagS`'s family `Mut 'c N ⊗ Mut 'c L`. -/
def AccBagCb : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] bagCb (.val (cbT mutM 0 LifeCtx.empty.meetOfDom bagS .unit))

theorem accBagCb : AccBagCb (ℍ := ℍ) :=
  semSM_callbackW ok_empty rfl .nil (.tensor (.mut _ _) (.mut _ _)) (.box (.unit 0)) <|
    letW (A := .mut (.var 0) natN) (B := .mut (.var 0) clistL) (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    letW (A := .mut (.var 0) clistL) (B := .unit)
      (appW (d_pushG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

/-- K: the family borrow `withborF2` at `immM` (P7). NOT BUILT: `DraftFL` at `withborI2_wf`'s
derivation, whose inner callback captures the user's callback as a live `U` slot (`AllIRowMAt`
at a live `U` slot, D6). -/
def AccReadFamilyWithborF2 : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ withborF2
    (.val (withborF2Ty immM 0 LifeCtx.empty.meetOfDom BB BB B3))

/-- K: the block borrow `withborS` at `σ2` (P9). NOT BUILT: `DraftFL` at `withborS_wf`'s
derivation, its inner callback at the live slot `g` (D6). -/
def AccBlockSwapWithborS : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (withborS σ2) (.val (wTy mutM 0 LifeCtx.empty.meetOfDom σ2 .unit))

end FamilyBlock

/-! ### Folds: P10 `countFoldProg`, P11 `anyTreeProg`, P25 `anyListProg`, P26 `natCopyProg`; P27
`sumListProg`, P28 `signProg`; P29 `sumProg`, P30 `mapProgC`, P31 `mapProgR`; P32 `mapProg`;
P33 `countProg`, P34 `countFreeProg` -/

section Folds

def AccCountFoldRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] countFoldProg (.comp (.ret natN))
def AccAnyTreeRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] anyTreeProg (.comp (.ret boolT))
def AccAnyListRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] anyListProg (.comp (.ret boolT))
def AccNatCopyRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] natCopyProg (.comp (.ret natN))
def AccSumListRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] sumListProg (.comp (.ret .i32))
def AccSignRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] signProg (.comp (.ret signT))
def AccSumProgRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] sumProg (.comp (.ret natN))
def AccMapProgCRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] mapProgC (.comp (.ret pureL))
def AccMapProgRRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] mapProgR (.comp (.ret pureL))

theorem flat_pureL : FlatTy pureL := .mu (.sum (.unit 1) (.tensor (flatB_natN 1) (.tvar (by decide))))

theorem flat_signT : FlatTy signT :=
  .tensor (.int 0 _) (.tensor (.int 0 _) (.tensor (.int 0 _) (flat_BB 0)))

theorem accCountFoldRoot : AccCountFoldRoot (ℍ := ℍ) := semSM_root flat_natN countFoldProg_derives
theorem accAnyTreeRoot : AccAnyTreeRoot (ℍ := ℍ) := semSM_root (flat_BB 0) anyTreeProg_derives
theorem accAnyListRoot : AccAnyListRoot (ℍ := ℍ) := semSM_root (flat_BB 0) anyListProg_derives
theorem accNatCopyRoot : AccNatCopyRoot (ℍ := ℍ) := semSM_root flat_natN natCopyProg_derives
theorem accSumListRoot : AccSumListRoot (ℍ := ℍ) := semSM_root (.int 0 _) sumListProg_derives
theorem accSignRoot : AccSignRoot (ℍ := ℍ) := semSM_root flat_signT signProg_derives
theorem accSumProgRoot : AccSumProgRoot (ℍ := ℍ) := semSM_root flat_natN sumProg_derives
theorem accMapProgCRoot : AccMapProgCRoot (ℍ := ℍ) := semSM_root flat_pureL mapProgC_derives
theorem accMapProgRRoot : AccMapProgRRoot (ℍ := ℍ) := semSM_root flat_pureL mapProgR_derives

/-- V: the count algebra (P10), persistent, at `!U(∀'b. 1 ⊕ N ⊸ F N)`. -/
def AccCountAlg : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val countAlgV) (.val (algTy listF 0 natN))

theorem accCountAlg : AccCountAlg (ℍ := ℍ) := fun _ hΓ =>
  semSM_algI hΓ (.flat (.sum (.unit 0) flat_natN)) flat_natN (d_countAlgB (.cons hΓ))

/-- V: the list search algebra (P25), persistent. -/
def AccAnyListAlg : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val anyLAlgV) (.val (algTy blistF 0 boolT))

theorem accAnyListAlg : AccAnyListAlg (ℍ := ℍ) := fun _ hΓ =>
  semSM_algI hΓ (.flat (.sum (.unit 0) (.tensor (flat_BB 0) (flat_BB 0)))) (flat_BB 0) <|
    .sumE (A := .unit) (B := .tensor boolT boolT) (.left (deadSplit (.cons hΓ)))
      (.var (.here (.cons hΓ)))
      (.unitE (.left (.dead (deadSplit (.cons hΓ)))) (.var (.here (.cons (.cons hΓ))))
        (.ret (.sumI₁ (.unitI (.cons (.cons (.cons hΓ)))))))
      (.tensorE (A := boolT) (B := boolT) (.left (.dead (deadSplit (.cons hΓ))))
        (.var (.here (.cons (.cons hΓ)))) (d_or (.cons (.cons (.cons hΓ)))))

/-- V: the tree search algebra (P11), persistent. -/
def AccAnyTreeAlg : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val anyTAlgV) (.val (algTy btreeF 0 boolT))

theorem accAnyTreeAlg : AccAnyTreeAlg (ℍ := ℍ) := fun _ hΓ =>
  semSM_algI hΓ (.flat (.sum (flat_BB 0) (.tensor (flat_BB 0) (flat_BB 0)))) (flat_BB 0) <|
    .sumE (A := boolT) (B := .tensor boolT boolT) (.left (deadSplit (.cons hΓ)))
      (.var (.here (.cons hΓ))) (.ret (.var (.here (.cons (.cons hΓ)))))
      (.tensorE (A := boolT) (B := boolT) (.left (.dead (deadSplit (.cons hΓ))))
        (.var (.here (.cons (.cons hΓ)))) (d_or (.cons (.cons (.cons hΓ)))))

/-- V: the list-freeing algebra (P10), a persistent first-order thunk. -/
def AccFreeLAlg : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ (.val freeLAlgV) (.val (algOTy listF .unit))

theorem accFreeLAlg : AccFreeLAlg (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.bang (.arr (.flat (.sum (.unit 0) (.unit 0))) (.ret (.unit 0))))
    (d_freeLAlg hΓ)

/-- V: the sum algebra over a list of `I32` (P27), persistent; its body loads each leaf with
`withload`, read inside the algebra's own push. -/
def AccSumIAlg : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [⟨.lolli ilistL .unit, false⟩] (.val sumIAlgV)
    (.val (algTy ilistF 0 .i32))

theorem accSumIAlg : AccSumIAlg (ℍ := ℍ) := by
  refine semSM_algI (.cons .nil) (.sum (.flat (.unit 0)) (.tensor (.imm _ _) (.flat (.int 0 _))))
    (.int 0 _) (.ret ?_)
  · refine caseP (A := .unit) (B := .tensor (.imm (.var 0) .i32) .i32) (.var (by csoloP))
      (d_i32 0 (by cdeadP)) ?_
    refine letP (A := .imm (.var 0) .i32) (B := .i32) (.var (by csoloP)) ?_
    refine d_hop (.bin .w32 .add) (pairP ?_ (.var (by csoloP))) (by cdeadP)
    exact appW
      (callbackW ΔA_ok (x := 1) rfl (by cdead)
        (.boxI (.var (by csoloP))
          (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
            (by cdead))))
      (appW (.var (by csoloP))
        (.withload (a := .var 0) (A := .i32) (B := .i32) 1 (by cdeadP) rfl (by simp [VFree])
          (by simp [VFree])))

/-- V: the list-freeing algebra over `I32` (P27), a persistent first-order thunk. -/
def AccFreeIAlg : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val freeIAlgV) (.val (algOTy ilistF .unit))

theorem accFreeIAlg : AccFreeIAlg (ℍ := ℍ) :=
  semSM_const .lam .nil
    (.bang (.arr (.flat (.sum (.unit 0) (.tensor (.ref (.int 0 _)) (.unit 0)))) (.ret (.unit 0))))
    d_freeIAlg

/-- V: the sum algebra over the common list (P29), persistent; its body calls `natCopy` at the
algebra's own variable (D1), which G5 does not open. -/
def AccSumAlg : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val sumAlgV) (.val (algTy clistF 0 natN))

theorem accSumAlg : AccSumAlg (ℍ := ℍ) := fun _ hΓ =>
  semSM_algI hΓ (.sum (.flat (.unit 0)) (.tensor (.imm _ _) (.flat flat_natN))) flat_natN
    (d_sumAlgB (.cons hΓ))

/-- V: the counter at fuel `0`, `c₀V` (P33), a persistent first-order callback. -/
def AccCountZero : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val c₀V) (.val countTy)

theorem accCountZero : AccCountZero (ℍ := ℍ) := fun _ hΓ =>
  semSM_algI hΓ (.imm _ _) flat_natN <|
    .unitE (.left (.dead (deadSplit hΓ)))
      (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
        (.forgetImm (.cons (.cons hΓ))))
      (.ret (.roll natBody_noMut natN_closed (.sumI₁ (.unitI (.cons (.cons hΓ))))))

/-- R (P33): `countProg` open at `ΓF`, whose slots `countN : U(N ⊸ F countTy)` and
`freeAll : U(L ⊸ F 1)` are thunks, not first-order. NOT BUILT: the glue at `U` slots
(`BindRowM`, `LolliERowM`, `AppRowM`, `LetPairRowM`, `UnitERowM`). -/
def AccCountRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty ΓF countProgOpen (.comp (.ret natN))

/-- V (P33): `stepV`, the counter at fuel `k + 1` from the counter `g : countTy` at fuel `k`, the
producer of the user's case slot-carried. NOT BUILT: `AllIRowMAt .binder0 (⟨countTy, true⟩ :: Γ)`,
the `∀I` row's binder-named push at a persistent context (`VRLMStackRename`, stated; the reduction
from it with `persistentPushN`, not built; D5). -/
def AccCountStep : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty (⟨countTy, true⟩ :: Γ) (.val stepV) (.val countTy)

/-- V (P33): `cbE`, the callback at the persistent slot `g`, the carry side. NOT BUILT:
`AllIRowMAt` at the persistent slot (D5), and in the body `AllEVRowM` at `g []`
(`InScopeOfInterp`, D1) and `LolliERowM` at `g [] t` (D9). -/
def AccCountCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ (⟨.imm (.var 0) listL, false⟩ :: ⟨.unit, false⟩ :: ⟨countTy, true⟩ :: Γ)
    cbE (.val cbTy)

/-- R (P32): `mapProg` open at `ΓM`, whose slots `mapInc` and `toPure` are thunks. NOT BUILT: the
glue at `U` slots (`BindRowM`, `LolliERowM`, `LetPairRowM`, `UnitERowM`); `borrowerM` at the live
slot `mapInc` (D6). -/
def AccMapProgRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty ΓM mapProgOpen (.comp (.ret pureL))

/-- R (P30): `mapProgC` open at `ΓMC`. NOT BUILT: as P32's root. -/
def AccMapProgOpenCRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty ΓMC mapProgOpenC (.comp (.ret pureL))

/-- R (P34): `countFreeProg` open at `ΓC`. NOT BUILT: the glue at its `!U` and `U` slots, as P33's
root. -/
def AccCountFreeRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty ΓC countFreeProgOpen (.comp (.ret natN))

/-- K (P33): `withload` at `L` (one reborrowed cell). NOT BUILT: `WithloadRowM`. -/
def AccCountLoad : Prop := ∀ Γ : Ctx VTy, Ctx.DeadP Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom listL natN))

end Folds

/-! ### Affine closures and arrays: P12 `counterProg`, P35 `ofFnProg`, P36 `onceProg`, P37
`dropProg`, P38 `nestProg`, P39 `passProg n`, P40 `retProg`, P41 `logProg`; P13 `arrProg` -/

section Affine

def AccCounterRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] Aff.counterProg (.comp (.ret .i32))
def AccOfFnRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] Aff.ofFnProg (.comp (.ret .i32))
def AccOnceRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] Aff.onceProg (.comp (.ret .i32))
def AccDropRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] Aff.dropProg (.comp (.ret .i32))
def AccNestRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] Aff.nestProg (.comp (.ret .i32))
def AccPassRoot : Prop := ∀ n : ℕ, AccNode (ℍ := ℍ) LifeCtx.empty [] (Aff.passProg n) (.comp (.ret .i32))
def AccRetRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] Aff.retProg (.comp (.ret .i32))
def AccLogRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] Aff.logProg (.comp (.ret .i32))
def AccArrRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] arrProg (.comp (.ret (.tensor (.sum .i32 .i32) .i32)))

theorem accCounterRoot : AccCounterRoot (ℍ := ℍ) := semSM_root (.int 0 _) Aff.counterProg_derives
theorem accOfFnRoot : AccOfFnRoot (ℍ := ℍ) := semSM_root (.int 0 _) Aff.ofFnProg_derives
theorem accOnceRoot : AccOnceRoot (ℍ := ℍ) := semSM_root (.int 0 _) Aff.onceProg_derives
theorem accDropRoot : AccDropRoot (ℍ := ℍ) := semSM_root (.int 0 _) Aff.dropProg_derives
theorem accNestRoot : AccNestRoot (ℍ := ℍ) := semSM_root (.int 0 _) Aff.nestProg_derives
theorem accPassRoot : AccPassRoot (ℍ := ℍ) := fun n => semSM_root (.int 0 _) (Aff.passProg_derives n)
theorem accRetRoot : AccRetRoot (ℍ := ℍ) := semSM_root (.int 0 _) Aff.retProg_derives
theorem accLogRoot : AccLogRoot (ℍ := ℍ) := semSM_root (.int 0 _) Aff.logProg_derives
theorem accArrRoot : AccArrRoot (ℍ := ℍ) :=
  semSM_root (.tensor (.sum (.int 0 _) (.int 0 _)) (.int 0 _)) arrProg_derives

/-- V: `counterStep` (P12, P35–P41), the affine counter's persistent step, a first-order thunk. -/
def AccCounterStep : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (c : Lifetime.Life), Δ.Defines c →
  Ctx.Dead Γ → AccNode (ℍ := ℍ) Δ Γ (.val Aff.counterStep)
    (.val (.bang (.thunk (.arr (.ref .i32) (affStepC c .i32 .i32 (.ref .i32))))))

theorem accCounterStep : AccCounterStep (ℍ := ℍ) := fun _ _ _ hc hΓ =>
  semSM_const .lam hΓ
    (.bang (.arr (.flat (.ref (.int 0 _)))
      (.amp (.arr (.flat (.int 0 _)) (.ret (.tensor (.int 0 _) (.box (.ref (.int 0 _)))))) (.ret (.unit 0)))))
    (Aff.d_counterStep hc hΓ)

/-- V: the counter's borrower `cntCb` (P12), a first-order callback at `Mut 'w PC`. -/
def AccCntCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ Aff.cntCb (.val Aff.cntCbTy)

theorem accCntCb : AccCntCb (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW (Δ := Δ₁) (by decide) rfl hΓ (.mut _ _) (.box (.int 0 _)) (Aff.d_cntBody hΓ)

/-- V: `passCb n` (P39), a first-order callback at `Mut 'w PC` that hands the borrow through `n`
persistent functions, which G5 does not open. -/
def AccPassCb : Prop := ∀ n : ℕ, AccNode (ℍ := ℍ) Δ₁ [] (Aff.passCb n) (.val Aff.cntCbTy)

theorem accPassCb : AccPassCb (ℍ := ℍ) := fun n =>
  semSM_callbackW (Δ := Δ₁) (x := 1) (A := .mut (.var 1) Aff.PC) (B := .box (.var 1) .i32)
    (by decide) rfl .nil (.mut _ _) (.box (.int 0 _)) <|
    .letpairV (.left (.dead .nil))
      (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
        (.bangE (Aff.d_passF n (.cons (.cons .nil)))))
      (.seqV (.right (.left (.dead (.dead .nil))))
        (.lolliE (split_kill' _).toP (.var (.there (.here (.cons (.cons .nil)))))
          (.forgetMut (kill_dead _).toP))
        (.boxI (.var (.here (.cons (.cons (.cons .nil)))))
          (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide))))

/-- V: `incV` (P35), a persistent first-order thunk. -/
def AccInc : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val Aff.incV) (.val (.bang (.lolli .i32 .i32)))

theorem accInc : AccInc (ℍ := ℍ) := fun _ hΓ =>
  semSM_const .lam hΓ (.bang (.arr (.flat (.int 0 _)) (.ret (.int 0 _)))) (Aff.d_inc hΓ)

/-- V: `passF n` (P39) at `passTy = !U(Mut '1 PC ⊸ F(Mut '1 PC ⊗ I32))`. NOT BUILT: its answer
holds a `Mut` leaf, so the λ's judgement is not first-order: `LamRowM`, and in the body
`LetPairRowM`, `LolliERowM`, `BangERowM`, `TensorIRowM`, `VarRowM` at `Mut`; the leaf owes
`CohS` and `RetainedPay` (D7). `BangThunkVRowM` is proved. -/
def AccPassF : Prop := ∀ (n : ℕ) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₂ Γ (.val (Aff.passF n)) (.val Aff.passTy)

/-- K: `withbor` (3) at `PC` (P39), the reborrow of a `Mut` at a nested push. NOT BUILT:
`Withbor3RowM`. -/
def AccPassWithbor3 : Prop := ∀ Γ : Ctx VTy, Ctx.DeadP Γ →
  AccNode (ℍ := ℍ) Δ₂ Γ withbor (.val (axWithbor3Ty (.var 1) 2 Δ₂.meetOfDom Aff.PC .i32))

end Affine

/-- V: `tab10V` (P13), a persistent first-order thunk. -/
def AccTab10 : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val tab10V) (.val (.bang (.lolli .i32 .i32)))

theorem accTab10 : AccTab10 (ℍ := ℍ) := fun _ hΓ =>
  semSM_const .lam hΓ (.bang (.arr (.flat (.int 0 _)) (.ret (.int 0 _)))) (d_tab10 hΓ)

/-- V: `dropI32V` (P13), a persistent first-order thunk. -/
def AccDropI32 : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (.val dropI32V) (.val (.bang (.lolli .i32 .unit)))

theorem accDropI32 : AccDropI32 (ℍ := ℍ) := fun _ hΓ =>
  semSM_const .lam hΓ (.bang (.arr (.flat (.int 0 _)) (.ret (.unit 0)))) (d_dropI32 hΓ)

/-! ### S1 `pairLoad` and `pairLoadU`: `withload` of a pair of references

`cImmBorrow`'s skeleton at the payload `pairTy = Ref 1 ⊗ Ref 1`:

    alloc (alloc (), alloc ()) to r.
    withbor r (borrower pairLoader) to p. let (r′, t) = p in t;
    free r′ to c. let (c₁, c₂) = c in free c₁; free c₂

`pairLoadU` is the same program with `withload` at its unwinding type at the empty row, the
borrower's body binding the loader first (`borrowBodyU`). The two loads' nodes are
`NxGuardPair.lean`'s `PairWithloadTyped` and `PairWithloadUTyped` nodes, under a closed program. -/

section PairLoad
open BoCa.Programs (alloc' free' app2)

/-- `M to x. N` at the split `part M` makes. -/
theorem bindW {Δ : LifeCtx} {Γ : Ctx VTy} {M N : Expr} {A : VTy} {C : CTy}
    (hM : CDerives Δ (part M 0 Γ).1 M (.comp (.ret A)))
    (hN : CDerives Δ (⟨A, true⟩ :: (part M 0 Γ).2) N (.comp C)) :
    CDerives Δ Γ (.app (.val (.lam N)) M) (.comp C) :=
  .bind (part_split M 0 Γ) hM hN

/-- `M x` at the split `part M` makes. -/
theorem appCW {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {i : Nat} {A : VTy} {C : CTy}
    (hM : CDerives Δ (part M 0 Γ).1 M (.comp (.arr A C))) (hx : Ctx.SoloP (part M 0 Γ).2 i A) :
    CDerives Δ Γ (.app M (.var i)) (.comp C) :=
  .app (part_split M 0 Γ) hM hx

/-- `force x` at an arrow type is `x` itself. -/
theorem forceArrW {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy} {C : CTy}
    (h : Ctx.SoloP Γ i (.thunk (.arr A C))) : CDerives Δ Γ (.var i) (.comp (.arr A C)) :=
  .force h

/-- `Λ'1. return (λq. let (u, w) = q in forget u; forget w; return ())`, at `loaderTy pairTy`
(the answer boxed twice by typing): its argument is `Imm̲ '1 (Ref 1 ⊗ Ref 1) = Imm '1 1 ⊗ Imm '1 1`.
The same term types at `withloadU`'s callback type (`.arr` shape). -/
def pairLoader : Expr :=
  .val (.lam (.val (.lam (.letpair (.var 0)
    (.seq (.app forget (.var 1)) (.seq (.app forget (.var 0)) (.val .unit)))))))

theorem d_pairLoaderBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives (Δ₁.extend 1 Δ₁.meetOfDom)
      (⟨VTy.immReborrow (.var 1) pairTy, true⟩ :: ⟨.unit, false⟩ :: Γ)
      (.letpair (.var 0) (.seq (.app forget (.var 1)) (.seq (.app forget (.var 0)) (.val .unit))))
      (.val (.box (.var 1) (.box (.var 0) .unit))) :=
  letW (A := .imm (.var 1) .unit) (B := .imm (.var 1) .unit) (.var (by csolo)) <|
  seqW (appW (.var (by csolo)) (.forgetImm (by cdead))) <|
  seqW (appW (.var (by csolo)) (.forgetImm (by cdead))) <|
  .boxI (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)
    ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩

theorem d_pairLoader {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ Γ pairLoader (.val (loaderTy pairTy)) :=
  callbackW (x := 1) (by decide) rfl hΓ (d_pairLoaderBody hΓ)

/-- The loader at `withloadU`'s callback type at the empty row. -/
theorem d_pairLoaderU {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ Γ pairLoader
      (.val (cbUTy 1 Δ₁.meetOfDom (VTy.immReborrow (.var 1) pairTy) (.box (.var 0) .unit) [])) :=
  .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ hy => LifeCtx.Ok.bound_mentions_false (by decide) rfl hy) (dead_noLive hΓ)
    (.lam (.ret (d_pairLoaderBody hΓ))))

def pairLoad : Expr :=
  .letpair (app2 withbor (.app alloc' (.pair (.app alloc' (.val .unit)) (.app alloc' (.val .unit))))
      (borrower pairLoader))
    (.seq (.var 0) (.letpair (.app free' (.var 1)) (.seq (.app free' (.var 1)) (.app free' (.var 0)))))

theorem d_pairLoad : CDerives LifeCtx.empty [] pairLoad (.val .unit) :=
  letW (A := .ref pairTy) (B := .unit)
    (appW (d_borrower (by cdead) (by simp [VFree]) d_pairLoader)
      (appW (appW (pairW (appW (.unitI (by cdead)) (.alloc (by cdead)))
          (appW (.unitI (by cdead)) (.alloc (by cdead)))) (.alloc (by cdead)))
        (.withbor1 (A := pairTy) (B := .unit) 0 (by cdead) rfl
          (fun _ h => by simp [VFree] at h) (by simp [VFree]) (by simp [VFree])))) <|
  seqW (.var (by csolo)) <|
  letW (A := .ref .unit) (B := .ref .unit) (appW (.var (by csolo)) (.free (by cdead))) <|
  seqW (appW (.var (by csolo)) (.free (by cdead))) (appW (.var (by csolo)) (.free (by cdead)))

/-- The borrower's body at `withload`'s unwinding type: `L to l. withload to wl. wl b l`, at `b` =
index 0. -/
def borrowBodyU (L : Expr) : Expr :=
  bindE L (bindE withload (.app (.app (.var 0) (.var 2)) (.var 1)))

def borrowerU (L : Expr) : Expr := .val (.lam (.val (.lam (borrowBodyU L))))

theorem d_borrowBodyU {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ (⟨.imm (.var 0) pairTy, true⟩ :: ⟨.unit, false⟩ :: Γ) (borrowBodyU pairLoader)
      (.comp (.ret (.box (.var 0) .unit))) :=
  bindW (.ret (d_pairLoaderU (by cdead))) <|
  bindW (.ret (.withloadU (a := .var 0) (A := pairTy) (B := .box (.var 0) .unit) (S := []) 1
      (by cdead) rfl (by simp [VFree]) (by simp [VFree, Lifetime.Life.mentions])
      (fun o ho => absurd ho List.not_mem_nil))) <|
  appCW (appCW (forceArrW (by csolo)) (by csolo)) (by csolo)

theorem d_borrowerU {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (borrowerU pairLoader) (.val (borrowerTy pairTy)) :=
  .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy) (dead_noLive hΓ)
    (.ret (.thunkV rfl (.lam (d_borrowBodyU hΓ)))))

def pairLoadU : Expr :=
  .letpair (app2 withbor (.app alloc' (.pair (.app alloc' (.val .unit)) (.app alloc' (.val .unit))))
      (borrowerU pairLoader))
    (.seq (.var 0) (.letpair (.app free' (.var 1)) (.seq (.app free' (.var 1)) (.app free' (.var 0)))))

theorem d_pairLoadU : CDerives LifeCtx.empty [] pairLoadU (.val .unit) :=
  letW (A := .ref pairTy) (B := .unit)
    (appW (d_borrowerU (by cdead))
      (appW (appW (pairW (appW (.unitI (by cdead)) (.alloc (by cdead)))
          (appW (.unitI (by cdead)) (.alloc (by cdead)))) (.alloc (by cdead)))
        (.withbor1 (A := pairTy) (B := .unit) 0 (by cdead) rfl
          (fun _ h => by simp [VFree] at h) (by simp [VFree]) (by simp [VFree])))) <|
  seqW (.var (by csolo)) <|
  letW (A := .ref .unit) (B := .ref .unit) (appW (.var (by csolo)) (.free (by cdead))) <|
  seqW (appW (.var (by csolo)) (.free (by cdead))) (appW (.var (by csolo)) (.free (by cdead)))

/-- The pair is lent, loaded and both cells freed: the program leaves no cell. -/
theorem pairLoad_eval : BoCa.Programs.unitNoLeak (eval pairLoad) = true := by decide

theorem pairLoadU_eval : BoCa.Programs.unitNoLeak (eval pairLoadU) = true := by decide

def AccPairLoadRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] pairLoad (.val .unit)
def AccPairLoadURoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] pairLoadU (.val .unit)

/-- V1: the borrower at `borrowerTy pairTy`; its body holds the `withload` of the pair. -/
def AccPairLoadCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (borrower pairLoader) (.val (borrowerTy pairTy))

/-- V1′: `pairLoadU`'s borrower, its body at `withload`'s unwinding type. -/
def AccPairLoadCbU : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ (borrowerU pairLoader) (.val (borrowerTy pairTy))

/-- V2: the loader at `loaderTy pairTy`. -/
def AccPairLoadLoader : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ pairLoader (.val (loaderTy pairTy))

/-- V2′: the loader at `withloadU`'s callback type at the empty row. -/
def AccPairLoadLoaderU : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ pairLoader
    (.val (cbUTy 1 Δ₁.meetOfDom (VTy.immReborrow (.var 1) pairTy) (.box (.var 0) .unit) []))

/-- K1: `withbor` (1) at `pairTy`. NOT BUILT: `Withbor1RowM`. At the empty stack
(`Withbor1NilRowM`, `GroundBlock.lean`) the payload step ports at the flat `pairTy`
(`nilPayloadCore_flat`), and the own push at the frame's place reads `ImmFramePlaceFree`, not
derived. -/
def AccPairLoadWithbor : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ withbor
    (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom pairTy .unit))

/-- K2: `withload` of the pair, at every index. NOT BUILT: `WithloadRowM`. The single own push
lends one place, and the second reborrowed cell fails the table at the identity instantiation of
the answer's `U` clause, at every stack (`loadGuardFails2`). The relation also reads the block push
of both places, and at the empty stack the block gate passes (`loadGateNilB_pairTy`). The row at
the empty stack (`WithloadNilRowM`) stops at (l3): the gate reads the reborrow's structure, which
[TR] 6.150's rule does not hand its continuation (`LoadGateNilBI`, not derived). At the thunked
type the answer's `U` clause at a non-identity instantiation moves a single push below the cells
(`not_withloadPairGapInst`), a route not refuted and not built. -/
def AccPairLoadWithload : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload
    (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom pairTy (.box (.var 0) .unit)))

/-- K2′: the same at `withloadU`'s type at the empty row. NOT BUILT: `WithloadURowM`. At an arising
configuration (`withloadUPairGapReal`), at the stack of the enclosing lend of the pair, the payload
reborrowed by `TW.reb` at an own push's lifetime fails the guard at every single-push reading the
callback's clause offers (`PairGuardRejectsU`). The relation also reads the block push of both
places, which those readings do not list; at the empty stack the block gate passes
(`loadGateNilB_pairTy`), and the row there (`WithloadUNilRowM`) stops at (l3) (`LoadGateNilBI`, not
derived). The entry's own judgement is not refuted, so it is not a FAILS. -/
def AccPairLoadWithloadU : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload
    (.val (withloadUTy (.var 0) 1 Δ₁.meetOfDom pairTy (.box (.var 0) .unit) []))

/-- K3: `alloc` at the pair, flat. -/
def AccPairLoadAlloc : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ (.val (.prim .alloc)) (.val (.lolli pairTy (.ref pairTy)))

/-- K4: `free` at the pair. -/
def AccPairLoadFree : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ (.val (.prim .free)) (.val (.lolli (.ref pairTy) pairTy))

/-- K5: `forget` at the loader's leaf `Imm '1 1`. -/
def AccPairLoadForget : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ forget (.val (axForgetImmTy (.var 1) .unit))

theorem accPairLoadRoot : AccPairLoadRoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_pairLoad

theorem accPairLoadURoot : AccPairLoadURoot (ℍ := ℍ) := semSM_rootV (.unit 0) d_pairLoadU

theorem accPairLoadCb : AccPairLoadCb (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW ok_empty rfl hΓ (.imm _ _) (.box (.unit 0))
    (CDerives.ofRet (d_borrowBody hΓ (by simp [VFree]) d_pairLoader))

theorem accPairLoadCbU : AccPairLoadCbU (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW ok_empty rfl hΓ (.imm _ _) (.box (.unit 0)) (CDerives.ofRet (d_borrowBodyU hΓ))

theorem accPairLoadLoader : AccPairLoadLoader (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW (x := 1) (by decide) rfl hΓ (.tensor (.imm _ _) (.imm _ _))
    (.box (.box (.unit 0))) (d_pairLoaderBody hΓ)

theorem accPairLoadLoaderU : AccPairLoadLoaderU (ℍ := ℍ) := fun Γ hΓ =>
  semSMCallbackArrOfCore Δ₁ Γ 1 _ _ _ _ (by decide) rfl rfl (ctxFO_of_dead hΓ)
    (fun s hs hl => dead_noLive (P := fun s => ¬ VFree 1 s.ty ∧ 1 ∉ VTy.binders s.ty) hΓ s hs hl)
    (.tensor (.imm _ _) (.imm _ _)) (.box (.box (.unit 0))) (.ret (d_pairLoaderBody hΓ))

theorem accPairLoadAlloc : AccPairLoadAlloc (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .prim hΓ
    (.thunk (.arr (.flat (.tensor (.ref (.unit 0)) (.ref (.unit 0))))
      (.ret (.ref (.tensor (.ref (.unit 0)) (.ref (.unit 0))))))) (.alloc hΓ.toP)

theorem accPairLoadFree : AccPairLoadFree (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .prim hΓ
    (.thunk (.arr (.flat (.ref (.tensor (.ref (.unit 0)) (.ref (.unit 0)))))
      (.ret (.tensor (.ref (.unit 0)) (.ref (.unit 0)))))) (.free hΓ.toP)

theorem accPairLoadForget : AccPairLoadForget (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.thunk (.arr (.imm _ _) (.ret (.unit 0)))) (.forgetImm hΓ.toP)

theorem readPairLoad :
    EntryRead LifeCtx.empty [] (.val .unit) ∧
    EntryRead LifeCtx.empty [] (.val (borrowerTy pairTy)) ∧
    EntryRead Δ₁ [] (.val (loaderTy pairTy)) ∧
    EntryRead Δ₁ [] (.val (cbUTy 1 Δ₁.meetOfDom (VTy.immReborrow (.var 1) pairTy)
      (.box (.var 0) .unit) [])) ∧
    EntryRead LifeCtx.empty [] (.val (.lolli pairTy (.ref pairTy))) ∧
    EntryRead LifeCtx.empty [] (.val (.lolli (.ref pairTy) pairTy)) ∧
    EntryRead (Δ₁.extend 1 Δ₁.meetOfDom) [] (.val (axForgetImmTy (.var 1) .unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · entry_read
  · entry_read [borrowerTy]
  · entry_read [loaderTy, Δ₁]
  · entry_read [cbUTy, Δ₁, CTy.effOf]
  · entry_read
  · entry_read
  · entry_read [Core.axForgetImmTy, Δ₁]

end PairLoad

/-! ### P42 the BoLo programs, embedded (`embed`, `Core/Embedding.lean`)

Each root is G5 at `embed d_X`. Every other node is a node of `embed d_X`'s derivation: NOT BUILT,
`DraftFLEmbed` (G12) at `d_X`. -/

section BoLoPrograms
open BoCa.Programs

/-- G5 at a closed BoLo program at `1`, through `embed`. -/
theorem semSM_embedRoot {e : Expr} (h : DerivesWf LifeCtx.empty [] e .unit) :
    SemSM (ℍ := ℍ) .binder0 LifeCtx.empty [] e (.val .unit) :=
  semSM_rootV (.unit 0) (embed h ok_empty (fun _ hs => by cases hs))

def AccAllocFreeRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] allocFree (.val .unit)
def AccFig2cRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] fig2c (.val .unit)
def AccImmBorrowPRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] immBorrow (.val .unit)
def AccMutBorrowPRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] mutBorrow (.val .unit)
def AccLoadClosureRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] loadClosure (.val .unit)
def AccAliasLoadRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] aliasLoad (.val .unit)
def AccSwapTwoRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] swapTwo (.val .unit)
def AccGreetProgRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] greetProg (.val .unit)
def AccOwnedFnRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] ownedFn (.val .unit)
def AccMutClosureRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] mutClosure (.val .unit)
def AccCallBorrowedRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] callBorrowed (.val .unit)
def AccCapturesRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] captures (.val .unit)
def AccFnMutRoot : Prop := AccNode (ℍ := ℍ) LifeCtx.empty [] fnMut (.val .unit)

theorem accAllocFreeRoot : AccAllocFreeRoot (ℍ := ℍ) := semSM_embedRoot d_allocFree
theorem accFig2cRoot : AccFig2cRoot (ℍ := ℍ) := semSM_embedRoot d_fig2c
theorem accImmBorrowPRoot : AccImmBorrowPRoot (ℍ := ℍ) := semSM_embedRoot d_immBorrow
theorem accMutBorrowPRoot : AccMutBorrowPRoot (ℍ := ℍ) := semSM_embedRoot d_mutBorrow
theorem accLoadClosureRoot : AccLoadClosureRoot (ℍ := ℍ) := semSM_embedRoot d_loadClosure
theorem accAliasLoadRoot : AccAliasLoadRoot (ℍ := ℍ) := semSM_embedRoot d_aliasLoad
theorem accSwapTwoRoot : AccSwapTwoRoot (ℍ := ℍ) := semSM_embedRoot d_swapTwo
theorem accGreetProgRoot : AccGreetProgRoot (ℍ := ℍ) := semSM_embedRoot d_greetProg
theorem accOwnedFnRoot : AccOwnedFnRoot (ℍ := ℍ) := semSM_embedRoot d_ownedFn
theorem accMutClosureRoot : AccMutClosureRoot (ℍ := ℍ) := semSM_embedRoot d_mutClosure
theorem accCallBorrowedRoot : AccCallBorrowedRoot (ℍ := ℍ) := semSM_embedRoot d_callBorrowed
theorem accCapturesRoot : AccCapturesRoot (ℍ := ℍ) := semSM_embedRoot d_captures
theorem accFnMutRoot : AccFnMutRoot (ℍ := ℍ) := semSM_embedRoot d_fnMut

end BoLoPrograms

/-! ### P49 `recLog` (SecondClass): a bounded recursion over an answering capability -/

section RecLog
open SecondClass

/-- R, open at the capability `c : Mut @a I32`, at every `Δ` and `a`. NOT BUILT: the answer
`F (Mut @a I32 ⊗ 1)` holds a `Mut` leaf, so the root is not first-order: `BoundedFixRowM`, and the
glue rows `BindRowM` at a `!U` slot, `BangERowM`, `AppRowM`; the leaf owes `CohS` and
`RetainedPay` (D7). -/
def AccRecLogRoot : Prop := ∀ (Δ : LifeCtx) (a : Lifetime.Life),
  AccNode (ℍ := ℍ) Δ [⟨Cap a, true⟩] recLogE (.comp (Ans a))

/-- V: the step, a persistent closure whose argument holds its own self-reference (outside
`FOArg`). NOT BUILT: `LamRowM` at its λ (D7); `BangThunkVRowM` is proved. -/
def AccRecLogStep : Prop := ∀ (Δ : LifeCtx) (a : Lifetime.Life) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ stepE (.val (envStepTy (Cap a) .unit (Ans a)))

/-- K: the clause `λs. (s, ())` at `I32 ⊸ I32 ⊗ 1`, a first-order constant. -/
def AccRecLogClause : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ clauseE (.val (.lolli (.int .w32) (.tensor (.int .w32) .unit)))

theorem accRecLogClause : AccRecLogClause (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.thunk (.arr (.flat (.int 0 _)) (.ret (.tensor (.int 0 _) (.unit 0)))))
    (clauseE_derives hΓ)

end RecLog

/-! ### P53 `sumAffE`, P54 `blockAffE b` (Affine): drops elaborated into `CDerives` -/

section AffineElab

def AccSumAffRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] Affine.sumAffE (.comp (.ret .i32))

def AccBlockAffRoot : Prop := ∀ b : Bool,
  AccNode (ℍ := ℍ) LifeCtx.empty [] (Affine.blockAffE b) (.comp (.ret .i32))

theorem accSumAffRoot : AccSumAffRoot (ℍ := ℍ) :=
  semSM_root (.int 0 _) (Affine.ADerives.elab Affine.sumAff_derives)

theorem accBlockAffRoot : AccBlockAffRoot (ℍ := ℍ) := fun b =>
  semSM_root (.int 0 _) (Affine.ADerives.elab (Affine.blockAff_derives b))

/-- V (P53): the sum algebra at the empty context (`d_sumIAlg0`), as P27's. -/
def AccSumAffAlg : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val sumIAlgV) (.val (algTy ilistF 0 .i32))

theorem accSumAffAlg : AccSumAffAlg (ℍ := ℍ) := by
  refine semSM_algI .nil (.sum (.flat (.unit 0)) (.tensor (.imm _ _) (.flat (.int 0 _))))
    (.int 0 _) (.ret ?_)
  · refine caseP (A := .unit) (B := .tensor (.imm (.var 0) .i32) .i32) (.var (by csoloP))
      (d_i32 0 (by cdeadP)) ?_
    refine letP (A := .imm (.var 0) .i32) (B := .i32) (.var (by csoloP)) ?_
    refine d_hop (.bin .w32 .add) (pairP ?_ (.var (by csoloP))) (by cdeadP)
    exact appW
      (callbackW ΔA_ok (x := 1) rfl (by cdead)
        (.boxI (.var (by csoloP))
          (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
            (by cdead))))
      (appW (.var (by csoloP))
        (.withload (a := .var 0) (A := .i32) (B := .i32) 1 (by cdeadP) rfl (by simp [VFree])
          (by simp [VFree])))

end AffineElab

/-! ### P55 `allBelow` (GhostEnd): the derivation at which D16.1's GFP failed -/

/-- P55: GhostEnd's callback-shaped value at `Δ₀`, the derivation at which D16.1's GFP failed at
the stack `[x]` (`not_gfpAt_below`), at every index of W. NOT BUILT: the `∀I` step is proved at
the empty context (`allIRowMUFree0 []`) over `below_derives`, the λ at
`Mut 'y 1 ⊸ F (U (F (Mut 'y 1)))`, whose answer, a thunk returning the view, is not first-order:
`LamRowM`, with `ThunkFRowM` (proved) over `VarRowM` at the `Mut` slot (D7). -/
def AccBelow : Prop :=
  AccNode (ℍ := ℍ) GhostEnd.Δ₀ [] GhostEnd.allBelowE (.comp GhostEnd.allBelowC)

/-! ### P59 the I/O models (`Core/Stdio.lean`) -/

section Stdio

theorem flat_bytesTy : FlatTy bytesTy := .mu (.sum (.unit 1) (.tensor (.int 1 _) (.tvar (by decide))))

theorem flat_outRep : FlatTy outRep := .tensor (.int 0 _) flat_bytesTy

def AccMkInput : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val mkInputV) (.comp (mkInputC bytesTy))
def AccMkOutput : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val mkOutputV) (.comp (mkOutputC outRep))
def AccTakeInput : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val takeCapV) (.comp (takeInputC bytesTy))
def AccTakeOutput : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val takeCapV) (.comp (takeOutputC outRep))

theorem accMkInput : AccMkInput (ℍ := ℍ) :=
  coreToSemSM _ [] _ _ (fun _ hs => absurd hs List.not_mem_nil)
    (.arr (.flat flat_bytesTy) (.ret (.ref flat_bytesTy))) d_mkInput
theorem accMkOutput : AccMkOutput (ℍ := ℍ) :=
  coreToSemSM _ [] _ _ (fun _ hs => absurd hs List.not_mem_nil)
    (.arr (.flat (.int 0 _)) (.ret (.ref flat_outRep))) d_mkOutput
theorem accTakeInput : AccTakeInput (ℍ := ℍ) :=
  coreToSemSM _ [] _ _ (fun _ hs => absurd hs List.not_mem_nil)
    (.arr (.flat (.ref flat_bytesTy)) (.ret flat_bytesTy)) d_takeInput
theorem accTakeOutput : AccTakeOutput (ℍ := ℍ) :=
  coreToSemSM _ [] _ _ (fun _ hs => absurd hs List.not_mem_nil)
    (.arr (.flat (.ref flat_outRep)) (.ret flat_outRep)) d_takeOutput

/-- V: `readByteV` at `readByteC bytesTy`. NOT BUILT: its λ's answer holds the stream's `Mut` leaf
(`LamRowM`, D7) under the `∀I` step at the empty context (`allIRowMUFree0 []`). -/
def AccReadByte : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val readByteV) (.comp (readByteC bytesTy))

/-- V: `writeAllV` at `writeAllC outRep`. NOT BUILT: as `AccReadByte`; its inner `∀`'s argument
holds a slice at `'b`. -/
def AccWriteAll : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] (.val writeAllV) (.comp (writeAllC outRep))

end Stdio

/-! ### S3 `bangUse`: the user's case, the combinator written at the top and called in a callback

    def body : !(∀'z ⊏ ⊤. Imm 'z I32 ⊗ I32 ⊸ ['z] I32) =
      !thunk Λ'z. return (λp. let (v, acc) = p in add (withload v (Λ'w. λx. box x), acc))
    main = withbor (alloc (alloc 7)) (Λ'x. λb. box (withload b (Λ'z. λv. body ['z] (v, 1))))
             to (r′, s). free (free r′) to n. (n, s)

`body` holds no resource, is persistent and lifetime-polymorphic, and is called inside the load's
callback at the callback's own lifetime `'z`. The term is the one the checker gives for such a
`def` (it inlines a `def` at its use), so no `!U` slot is carried across a push: the slot-carried
form is P33 (`countProg`, `AccCountStep`, `AccCountCb`). The answer is `(7, 8)`. -/

section BangUse
open BoCa.Programs (alloc' free' app2)

/-- `let (v, acc) = p in add (readI v, acc) to s. return (box s)`, at `p` = index 0. -/
def bangBodyB : Expr :=
  .letpair (.var 0) (elet (hop (.bin .w32 .add) (.pair (readI (.var 1)) (.var 0))) (.var 0))

/-- The combinator `!thunk Λ'z. return (λp. bangBodyB)`. -/
def bangBodyE : Expr := lam2 bangBodyB

/-- Its type at the binder `z`: `!(∀'z ⊏ ⊤. Imm 'z I32 ⊗ I32 ⊸ ['z] I32)`. -/
abbrev bangBodyTy (z : LifeVar) : VTy :=
  .bang (VTy.all z .top (VTy.lolli (.tensor (.imm (.var z) .i32) .i32) (.box (.var z) .i32)))

/-- The combinator's λ-body, at every lifetime context its binder is fresh for: the inner load
runs at `Δ, 'z`'s fresh variable. -/
theorem d_bangBodyB {Δ : LifeCtx} {z : LifeVar} (hΔ : Δ.Ok) (hz : Δ.find? z = none) :
    CDerives (Δ.extend z .top) [⟨.tensor (.imm (.var z) .i32) .i32, true⟩, ⟨.unit, false⟩]
      bangBodyB (.val (.box (.var z) .i32)) := by
  have hΔz : (Δ.extend z .top).Ok := hΔ.extend hz rfl
  refine letP (A := .imm (.var z) .i32) (B := .i32) (.var (by csoloP)) ?_
  refine bindP (d_hop (.bin .w32 .add) (pairP ?_ (.var (by csoloP))) (by cdeadP)) ?_
  · exact appW
      (callbackW hΔz (x := (Δ.extend z .top).freshVar) (LifeCtx.freshVar_fresh _) (by cdead)
        (.boxI (.var (by csoloP))
          (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
            (by cdead))))
      (appW (.var (by csoloP))
        (.withload (a := .var z) (A := .i32) (B := .i32) _ (by cdeadP)
          (LifeCtx.freshVar_fresh _) (by simp [VFree]) (by simp [VFree])))
  · exact .boxI (.var (by csoloP)) (outlives_ctx (LifeCtx.defines_of_wf (wf_var_self _ _ _)) rfl)

/-- The combinator, at every lifetime context its binder is fresh for and every dead context. -/
theorem d_bangBodyE {Δ : LifeCtx} {z : LifeVar} {Γ : Ctx VTy} (hΔ : Δ.Ok)
    (hz : Δ.find? z = none) (hΓ : Ctx.Dead Γ) : CDerives Δ Γ bangBodyE (.val (bangBodyTy z)) :=
  .bangThunkV (persistent_dead hΓ) rfl
    (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false hΔ hz hy)
      (dead_noLive hΓ)
      (.ret (.thunkV rfl (.lam (.ret (CDerives.append_dead hΓ (d_bangBodyB hΔ hz)))))))

/-- The load's callback: `Λ'z. λv. body ['z] (v, 1)`. -/
def useCb : Expr := lam2 (.app (.app bangBodyE (.val .unit)) (.pair (.var 0) (i32E 1)))

/-- The callback's lifetime context: `'x ⊏ ⊤, 'z ⊏ ⊓('x ⊏ ⊤)`. -/
abbrev Δuse : LifeCtx := Δ₁.extend 1 Δ₁.meetOfDom

/-- The call `body ['z] (v, 1)`, the callback's λ-body. -/
theorem d_useCall0 :
    CDerives Δuse [⟨.imm (.var 1) .i32, true⟩, ⟨.unit, false⟩]
      (.app (.app bangBodyE (.val .unit)) (.pair (.var 0) (i32E 1))) (.val (.box (.var 1) .i32)) :=
  appP (A := .tensor (.imm (.var 1) .i32) .i32) (B := .box (.var 1) .i32)
    (pairP (.var (by csoloP)) (d_i32 1 (by cdeadP)))
    (.allEV (x := 2) (b := .top) (a := .var 1)
      (A := VTy.lolli (.tensor (.imm (.var 2) .i32) .i32) (.box (.var 2) .i32))
      (.bangE (d_bangBodyE (by decide) rfl (by cdead))) (BoCa.Programs.entailsLt_top rfl))

theorem d_useCall {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δuse (⟨.imm (.var 1) .i32, true⟩ :: ⟨.unit, false⟩ :: Γ)
      (.app (.app bangBodyE (.val .unit)) (.pair (.var 0) (i32E 1))) (.val (.box (.var 1) .i32)) :=
  CDerives.append_dead hΓ d_useCall0

/-- The borrower: `Λ'x. λb. withload b useCb to t. return (box t)`. -/
def useBorrower : Expr := lam2 (elet (.app (.app withload (.var 0)) useCb) (.var 0))

theorem d_useBorrowerBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ (⟨.imm (.var 0) (.ref .i32), true⟩ :: ⟨.unit, false⟩ :: Γ)
      (elet (.app (.app withload (.var 0)) useCb) (.var 0)) (.val (.box (.var 0) .i32)) :=
  eletW
    (appW (callbackW (x := 1) (by decide) rfl (by cdead) (d_useCall (by cdead)))
      (appW (.var (by csolo))
        (.withload (a := .var 0) (A := .ref .i32) (B := .i32) 1 (by cdead) rfl
          (by simp [VFree]) (by simp [VFree]))))
    (.boxI (.var (by csolo))
      (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (by cdead)))

def bangUse : Expr :=
  .letpair (app2 withbor (.app alloc' (.app alloc' (i32E 7))) useBorrower)
    (elet (.app free' (.app free' (.var 1))) (.pair (.var 0) (.var 1)))

theorem d_bangUse : CDerives LifeCtx.empty [] bangUse (.val (.tensor .i32 .i32)) :=
  letW (A := .ref (.ref .i32)) (B := .i32)
    (appW (callbackW (x := 0) ok_empty rfl (by cdead) (d_useBorrowerBody (by cdead)))
      (appW (appW (appW (d_i32 7 (by cdeadP)) (.alloc (by cdead))) (.alloc (by cdead)))
        (.withbor1 (A := .ref .i32) (B := .i32) 0 (by cdead) rfl
          (fun _ h => by simp [VFree] at h) (by simp [VFree]) (by simp [VFree])))) <|
  eletW (appW (appW (.var (by csolo)) (.free (by cdead))) (.free (by cdead))) <|
  pairW (.var (by csolo)) (.var (by csolo))

/-- The pair of `I32`s a run answers, with no cell left. -/
def i32PairNoLeak : Outcome → Option (UInt32 × UInt32)
  | .value ⟨.pair a b, _⟩ false => (i32Of a).bind fun x => (i32Of b).map fun y => (x, y)
  | _ => none

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: the cell's `7`, and `7 + 1` computed by the combinator inside
the load, no cell left. -/
theorem bangUse_eval : i32PairNoLeak (eval bangUse) = some (7, 8) := by decide

def AccBangUseRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] bangUse (.val (.tensor .i32 .i32))

/-- **S3's producer**: the combinator's node, at every lifetime context its binder is fresh for
(the use's `Δuse` among them, at `z = 2`) and every dead context. -/
def AccBangUseBody : Prop :=
  ∀ (Δ : LifeCtx) (z : LifeVar) (Γ : Ctx VTy), Δ.Ok → Δ.find? z = none → Ctx.Dead Γ →
    AccNode (ℍ := ℍ) Δ Γ bangBodyE (.val (bangBodyTy z))

/-- **S3's carry side, dereliction**: `unbang body` at the use. NOT BUILT: `BangERowM`. -/
def AccBangUseDeref : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δuse Γ bangBodyE
    (.val (VTy.all 2 .top (VTy.lolli (.tensor (.imm (.var 2) .i32) .i32) (.box (.var 2) .i32))))

/-- **S3's carry side, `∀E` at the callback's own variable `'z` (`1`)**, which `Δuse` binds.
NOT BUILT: `AllEVRowM` (its step `InScopeOfInterp`, D1). -/
def AccBangUseInst : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δuse Γ (.app bangBodyE (.val .unit))
    (.val (VTy.lolli (.tensor (.imm (.var 1) .i32) .i32) (.box (.var 1) .i32)))

/-- **The call `body ['z] (v, 1)`**, at the callback's context: first-order (its live slot is the
view `Imm 'z I32`, its answer `['z] I32`), so G5 gives it from Core's proof. The glue rows are read
below it, at `AccBangUseDeref` and `AccBangUseInst`. -/
def AccBangUseCall : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δuse (⟨.imm (.var 1) .i32, true⟩ :: ⟨.unit, false⟩ :: Γ)
    (.app (.app bangBodyE (.val .unit)) (.pair (.var 0) (i32E 1))) (.val (.box (.var 1) .i32))

/-- V: the load's callback at `∀'z ⊏ ⊓Δ₁. Imm 'z I32 ⊸ ['z] I32`. -/
def AccBangUseCb : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ useCb
    (.val (.all 1 Δ₁.meetOfDom (.lolli (.imm (.var 1) .i32) (.box (.var 1) .i32))))

/-- V: the borrower at `∀'x ⊏ ⊓∅. Imm 'x (Ref I32) ⊸ ['x] I32`. -/
def AccBangUseBorrower : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ useBorrower
    (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) (.ref .i32)) (.box (.var 0) .i32))))

/-- K: `withbor` (1) at `Ref I32`. NOT BUILT: `Withbor1RowM`. -/
def AccBangUseWithbor : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) LifeCtx.empty Γ withbor
    (.val (axWithbor1Ty 0 LifeCtx.empty.meetOfDom (.ref .i32) .i32))

/-- K: `withload` at `Ref I32` in the borrower (one reborrowed cell). NOT BUILT: `WithloadRowM`. -/
def AccBangUseLoad : Prop := ∀ Γ : Ctx VTy, Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ₁ Γ withload (.val (axWithloadTy (.var 0) 1 Δ₁.meetOfDom (.ref .i32) .i32))

/-- K: `withload` at `I32` inside the combinator (no reborrowed cell), at the use. NOT BUILT:
`WithloadRowM`. -/
def AccBangUseInnerLoad : Prop := ∀ Γ : Ctx VTy, Ctx.DeadP Γ →
  AccNode (ℍ := ℍ) (Δuse.extend 2 .top) Γ withload
    (.val (axWithloadTy (.var 2) (Δuse.extend 2 .top).freshVar (Δuse.extend 2 .top).meetOfDom
      .i32 .i32))

theorem accBangUseRoot : AccBangUseRoot (ℍ := ℍ) :=
  semSM_rootV (.tensor (.int 0 _) (.int 0 _)) d_bangUse

theorem accBangUseBody : AccBangUseBody (ℍ := ℍ) := fun Δ z Γ hΔ hz hΓ =>
  semSMBangCallbackOfCore Δ Γ z .top _ _ bangBodyB hΔ hz rfl hΓ
    (.tensor (.imm _ _) (.flat (.int 0 _))) (.box (.int 0 _))
    (.ret (CDerives.append_dead hΓ (d_bangBodyB hΔ hz)))

theorem accBangUseCall : AccBangUseCall (ℍ := ℍ) := fun Γ hΓ =>
  coreToSemSM _ _ _ _ (fun s hs hl => by
      rcases List.mem_cons.mp hs with rfl | hs
      · exact .imm _ _
      · rcases List.mem_cons.mp hs with rfl | hs
        · simp at hl
        · exact absurd hl (by simp [dead_not_live hΓ s hs]))
    (.ret (.box (.int 0 _))) (d_useCall hΓ)

theorem accBangUseCb : AccBangUseCb (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW (x := 1) (by decide) rfl hΓ (.imm _ _) (.box (.int 0 _)) (d_useCall hΓ)

theorem accBangUseBorrower : AccBangUseBorrower (ℍ := ℍ) := fun _ hΓ =>
  semSM_callbackW (x := 0) ok_empty rfl hΓ (.imm _ _) (.box (.int 0 _)) (d_useBorrowerBody hΓ)

theorem readBangUse :
    EntryRead LifeCtx.empty [] (.val (.tensor .i32 .i32)) ∧
    EntryRead LifeCtx.empty [] (.val (bangBodyTy 0)) ∧
    EntryRead Δuse [] (.val (bangBodyTy 2)) ∧
    EntryRead Δuse [⟨.imm (.var 1) .i32, true⟩, ⟨.unit, false⟩] (.val (.box (.var 1) .i32)) ∧
    EntryRead Δ₁ [] (.val (.all 1 Δ₁.meetOfDom (.lolli (.imm (.var 1) .i32) (.box (.var 1) .i32)))) ∧
    EntryRead LifeCtx.empty []
      (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) (.ref .i32)) (.box (.var 0) .i32)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · entry_read
  · entry_read
  · entry_read [Δ₁]
  · entry_read [Δ₁]
  · entry_read [Δ₁]
  · entry_read

end BangUse

/-! ### P56 `corpus/array-get.bc`, through the checker

The checker's acceptance is a `CDerives` derivation (`Checked.deriv`); `bcc_program%` embeds the
parsed file and `decide +kernel` evaluates the checker (`Frontend/Check/CrossCheck.lean`). The
`def`s `tab` and `read` erase to `tabE` and `readE` (`arrayGet_erasures`); their nodes are
derived here by hand at those erasures. The checker inlines `read` at its use, `read ['y] v`
inside the load's callback, at the callback's own lifetime.

The `withbor` (1) callback at `Imm 'x (array i32)` and the `withload` callback at the family
`array_imm 'y i32` are NOT BUILT as entries: their λ-bodies' derivations are inside the checker's
and are not re-derived here (`GROUND.md` §3.1's route for an inline sub-term, `chkC` at the
enclosing environment). Both bodies are first-order, so G5 gives each once its derivation is in
hand. -/

section ArrayGet
open Frontend.Check

/-- `corpus/array-get.bc`. -/
def arrayGetP : Frontend.Program := bcc_program% "corpus/array-get.bc"

set_option maxRecDepth 100000 in
theorem arrayGetP_checks : (mainOf arrayGetP).isSome = true := by decide +kernel

def arrayGet : Frontend.Check.Checked := (mainOf arrayGetP).get arrayGetP_checks

/-- The answer `T = I32 ⊗ (I32 ⊗ (1 ⊕ 1))`. -/
abbrev arrayGetT : VTy := .tensor (.int .w32) (.tensor (.int .w32) (.sum .unit .unit))

set_option maxRecDepth 100000 in
theorem arrayGet_shape : arrayGet.ctx = [] ∧ arrayGet.C = .ret arrayGetT := by decide +kernel

theorem arrayGet_derives : CDerives LifeCtx.empty [] arrayGet.e (.comp (.ret arrayGetT)) := by
  have h := arrayGet.deriv
  rwa [arrayGet_shape.1, arrayGet_shape.2] at h

/-- `tab`'s erasure: `!thunk λi. mul (i, 10)`. -/
def tabE : Expr := .val (.lam (hop (.bin .w32 .mul) (.pair (.var 0) (i32E 10))))

/-- `read`'s erasure: `thunk Λ'z. return (λv. withload v (Λ'w. λx. x))`. -/
def readE : Expr := lam2 (readI (.var 0))

set_option maxRecDepth 100000 in
theorem arrayGet_erasures : defErasure arrayGetP 2 = some tabE ∧ defErasure arrayGetP 3 = some readE := by
  decide +kernel

def AccArrayGetRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] arrayGet.e (.comp (.ret arrayGetT))

theorem accArrayGetRoot : AccArrayGetRoot (ℍ := ℍ) :=
  semSM_root (.tensor (.int 0 _) (.tensor (.int 0 _) (flat_BB 0))) arrayGet_derives

theorem d_tabE {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ tabE (.val (.bang (.lolli .i32 .i32))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret (.lolliE (.left (deadSplit hΓ))
    (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (d_i32 10 (Ctx.Dead.cons hΓ).toP))
    (.bangE (.hostOp _ (Ctx.Dead.cons hΓ).toP)))))

/-- V: `tab`, a persistent first-order thunk. -/
def AccArrayGetTab : Prop := ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.Dead Γ →
  AccNode (ℍ := ℍ) Δ Γ tabE (.val (.bang (.lolli .i32 .i32)))

theorem accArrayGetTab : AccArrayGetTab (ℍ := ℍ) := fun _ _ hΓ =>
  semSM_const .lam hΓ (.bang (.arr (.flat (.int 0 _)) (.ret (.int 0 _)))) (d_tabE hΓ)

/-- `read`'s λ-body at every lifetime context its binder is fresh for: the load runs at the fresh
variable of `Δ, 'z`. -/
theorem d_readBody {Δ : LifeCtx} {z : LifeVar} (hΔ : Δ.Ok) (hz : Δ.find? z = none) :
    CDerives (Δ.extend z .top) [⟨.imm (.var z) .i32, true⟩, ⟨.unit, false⟩] (readI (.var 0))
      (.val .i32) := by
  have hΔz : (Δ.extend z .top).Ok := hΔ.extend hz rfl
  exact appW
    (callbackW hΔz (x := (Δ.extend z .top).freshVar) (LifeCtx.freshVar_fresh _) (by cdead)
      (.boxI (.var (by csoloP))
        (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
          (by cdead))))
    (appW (.var (by csolo))
      (.withload (a := .var z) (A := .i32) (B := .i32) _ (by cdeadP)
        (LifeCtx.freshVar_fresh _) (by simp [VFree]) (by simp [VFree])))

/-- V: `read` at `U(∀'z ⊏ ⊤. F(U(Imm 'z I32 ⊸ F I32)))`, at every lifetime context its binder is
fresh for (the use's among them) and every dead context: a callback-shaped value, no `!`. -/
def AccArrayGetRead : Prop :=
  ∀ (Δ : LifeCtx) (z : LifeVar) (Γ : Ctx VTy), Δ.Ok → Δ.find? z = none → Ctx.Dead Γ →
    AccNode (ℍ := ℍ) Δ Γ readE (.val (VTy.all z .top (VTy.lolli (.imm (.var z) .i32) .i32)))

theorem accArrayGetRead : AccArrayGetRead (ℍ := ℍ) := fun Δ z Γ hΔ hz hΓ =>
  semSMCallbackOfCore Δ Γ z .top _ _ _ hΔ hz rfl (ctxFO_of_dead hΓ)
    (fun s hs hl => dead_noLive (P := fun s => ¬ VFree z s.ty ∧ z ∉ VTy.binders s.ty) hΓ s hs hl)
    (.imm _ _) (.int 0 _) (.ret (CDerives.append_dead hΓ (d_readBody hΔ hz)))

/-- K: `withload` at `array i32` (five cells at one lifetime: S2's case). NOT BUILT:
`WithloadRowM`. The single own push lends one place (`loadGuardFails2` at any two cells); the block
push of the reborrowed cells passes the gate at the empty stack (`loadGateNilB_arrayI32`), and the
row there (`WithloadNilRowM`) stops at (l3) (`LoadGateNilBI`, not derived). -/
def AccArrayGetLoad : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x z : LifeVar), Ctx.DeadP Γ → Δ.find? z = none →
    AccNode (ℍ := ℍ) Δ Γ withload
      (.val (axWithloadTy (.var x) z Δ.meetOfDom (.array (.int .w32)) arrayGetT))

/-- K: `withload` at `I32` inside `read` (no reborrowed cell). NOT BUILT: `WithloadRowM`. -/
def AccArrayGetReadLoad : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (z w : LifeVar), Ctx.DeadP Γ → Δ.find? w = none →
    AccNode (ℍ := ℍ) Δ Γ withload (.val (axWithloadTy (.var z) w Δ.meetOfDom .i32 .i32))

theorem readArrayGet :
    EntryRead LifeCtx.empty [] (.comp (.ret arrayGetT)) ∧
    EntryRead LifeCtx.empty [] (.val (.bang (.lolli .i32 .i32))) ∧
    EntryRead LifeCtx.empty [] (.val (VTy.all 0 .top (VTy.lolli (.imm (.var 0) .i32) .i32))) := by
  refine ⟨?_, ?_, ?_⟩
  · entry_read
  · entry_read
  · entry_read

end ArrayGet

/-! ### S4 `reconB′` (`NxRecon.lean`): recorded, not attempted

Its typing is not built; which rule types `withborUE dFlag` under `wait` is open. Its entries
are recorded, not attempted. -/

section Recon
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag)

/-- R: the program at `F (Flag ⊗ Flag)`. NOT BUILT: a flat-answer root is Core's semantic
acceptance (G7's `CRLMRetNil`); with no Core derivation, only a semantic proof of the run gives
it, and that reads no draft clause. -/
def AccReconRoot : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] reconB' (.comp (.ret (.tensor Flag Flag)))

/-- V: the borrow's callback. NOT BUILT: its typing (which rule types the lend under `wait`); the
callback row `CallbackExtImmMF`; the body at the `F_Σ` type at the push (statements 1–3).
`reconCb_allI` covers only the `∀I` step. -/
def AccReconCb (C : CTy) : Prop :=
  AccNode (ℍ := ℍ) LifeCtx.empty [] reconCb (.val (.thunk C))

end Recon

/-! ### `EntryRead` at the PROVED entries of P2–P59

At a dead context `EntryRead` reads no slot, so a lemma at `[]` serves every dead `Γ`; an entry
stated at every `Δ` at a closed type is read at every `Δ`. -/

section Reads

theorem readRoots :
    EntryRead LifeCtx.empty [] (.comp (.ret .unit)) ∧ EntryRead LifeCtx.empty [] (.val .unit) ∧
    EntryRead Δ₁ [] (.comp (.ret .unit)) ∧ EntryRead LifeCtx.empty [] (.val listL) ∧
    EntryRead LifeCtx.empty [] (.comp (.ret natN)) ∧ EntryRead LifeCtx.empty [] (.comp (.ret boolT)) ∧
    EntryRead LifeCtx.empty [] (.comp (.ret .i32)) ∧ EntryRead LifeCtx.empty [] (.comp (.ret signT)) ∧
    EntryRead LifeCtx.empty [] (.comp (.ret pureL)) ∧
    EntryRead LifeCtx.empty [] (.comp (.ret (.tensor (.sum .i32 .i32) .i32))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> entry_read [Δ₁]

theorem readRecBorrow :
    (∀ Δ, EntryRead Δ [] (.val methodsTy)) ∧
    EntryRead LifeCtx.empty [] (.val (borrowerTy methodsTy)) ∧
    EntryRead Δ₁ [] (.val (loaderTy methodsTy)) ∧
    (∀ Δ, EntryRead Δ [] (.val axForgetUnkTy)) := by
  refine ⟨fun _ => ?_, ?_, ?_, fun _ => ?_⟩
  · entry_read
  · entry_read [borrowerTy]
  · entry_read [loaderTy, Δ₁]
  · entry_read [Core.axForgetUnkTy]

theorem readBang :
    EntryRead LifeCtx.empty [] (.val (.bang (.thunk (.arr .unit (.ret .unit))))) := by
  entry_read

theorem readInst : EntryRead Δ₁ [] (.val (.thunk polyC)) := by entry_read [polyC, Δ₁]

theorem readReadFields :
    EntryRead LifeCtx.empty [] (.val (.all 0 LifeCtx.empty.meetOfDom
      (.lolli (.imm (.var 0) Pt.valTy) (.box (.var 0) (.tensor BB BB))))) ∧
    (∀ Δ, EntryRead Δ [] (.val (.lolli Pt.valTy (.ref Pt.valTy)))) := by
  refine ⟨?_, fun _ => ?_⟩ <;> entry_read

theorem readMutFields :
    (∀ Δ, EntryRead Δ [] (.val (.lolli BB (.tensor BB .unit)))) ∧
    EntryRead D1 [] (.val (.lolli (.ref BB) (.tensor (.ref BB) .unit))) := by
  refine ⟨fun _ => ?_, ?_⟩
  · entry_read
  · entry_read [D1]

theorem readExBag :
    (∀ Δ, EntryRead Δ [] (.val (.thunk (.amp (.ret .unit) .top)))) ∧
    (∀ Δ, EntryRead Δ [] (.val (.lolli clistL (.tensor clistL .unit)))) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩ <;> entry_read

theorem readFamilyBlock :
    EntryRead LifeCtx.empty [] (.val (cbTy2 immM 0 LifeCtx.empty.meetOfDom BB BB B3)) ∧
    EntryRead LifeCtx.empty [] (.val (cbTy2 mutM 0 LifeCtx.empty.meetOfDom BB BB .unit)) ∧
    EntryRead LifeCtx.empty [] (.val (cbT mutM 0 LifeCtx.empty.meetOfDom σ3 .unit)) ∧
    EntryRead LifeCtx.empty [] (.val (cbT immM 0 LifeCtx.empty.meetOfDom σ3 B21)) ∧
    EntryRead LifeCtx.empty [] (.val (cbT mutM 0 LifeCtx.empty.meetOfDom bagS .unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> entry_read

theorem readFolds :
    EntryRead LifeCtx.empty [] (.val (algTy listF 0 natN)) ∧
    EntryRead LifeCtx.empty [] (.val (algTy blistF 0 boolT)) ∧
    EntryRead LifeCtx.empty [] (.val (algTy btreeF 0 boolT)) ∧
    (∀ Δ, EntryRead Δ [] (.val (algOTy listF .unit))) ∧
    EntryRead LifeCtx.empty [⟨.lolli ilistL .unit, false⟩] (.val (algTy ilistF 0 .i32)) ∧
    EntryRead LifeCtx.empty [] (.val (algOTy ilistF .unit)) ∧
    EntryRead LifeCtx.empty [] (.val (algTy clistF 0 natN)) ∧
    EntryRead LifeCtx.empty [] (.val countTy) ∧
    EntryRead LifeCtx.empty [] (.val (algTy ilistF 0 .i32)) := by
  refine ⟨?_, ?_, ?_, fun _ => ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> entry_read

theorem readAffine :
    EntryRead Δ₁ [] (.val (.bang (.thunk (.arr (.ref .i32) (affStepC (.var 0) .i32 .i32 (.ref .i32)))))) ∧
    EntryRead Δ₁ [] (.val Aff.cntCbTy) ∧
    EntryRead LifeCtx.empty [] (.val (.bang (.lolli .i32 .i32))) ∧
    EntryRead LifeCtx.empty [] (.val (.bang (.lolli .i32 .unit))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · entry_read [affStepC, Δ₁]
  · entry_read [Aff.cntCbTy, Δ₁]
  · entry_read
  · entry_read

theorem readOthers :
    (∀ Δ, EntryRead Δ [] (.val (.lolli (.int .w32) (.tensor (.int .w32) .unit)))) ∧
    EntryRead LifeCtx.empty [] (.comp (mkInputC bytesTy)) ∧
    EntryRead LifeCtx.empty [] (.comp (mkOutputC outRep)) ∧
    EntryRead LifeCtx.empty [] (.comp (takeInputC bytesTy)) ∧
    EntryRead LifeCtx.empty [] (.comp (takeOutputC outRep)) := by
  refine ⟨fun _ => ?_, ?_, ?_, ?_, ?_⟩
  · entry_read
  · entry_read [mkInputC, bytesTy, bytesBody]
  · entry_read [mkOutputC, outRep, bytesTy, bytesBody]
  · entry_read [takeInputC, bytesTy, bytesBody]
  · entry_read [takeOutputC, outRep, bytesTy, bytesBody]

end Reads

/-! ### The programs: each program's stated entries, conjoined

A program's line in `LEDGER.md` §10 reads its entries' statuses off these; it is never written
"accepted". Entries the suite records only in prose (a glue row, a sub-derivation not extracted)
are not in the conjunctions. -/

section Programs

def AccImmBorrow : Prop := AccImmBorrowRoot (ℍ := ℍ) ∧ AccImmBorrowCb (ℍ := ℍ) ∧
  AccImmBorrowLoader (ℍ := ℍ) ∧ AccImmBorrowWithbor (ℍ := ℍ) ∧ AccImmBorrowWithload (ℍ := ℍ) ∧
  AccImmBorrowAlloc (ℍ := ℍ) ∧ AccImmBorrowFree (ℍ := ℍ)

def AccRecBorrow : Prop := AccRecBorrowRoot (ℍ := ℍ) ∧ AccRecBorrowMethods (ℍ := ℍ) ∧
  AccRecBorrowCb (ℍ := ℍ) ∧ AccRecBorrowLoader (ℍ := ℍ) ∧ AccRecBorrowWithbor (ℍ := ℍ) ∧
  AccRecBorrowAlloc (ℍ := ℍ) ∧ AccRecBorrowForget (ℍ := ℍ)

def AccBangP : Prop := AccBangRoot (ℍ := ℍ) ∧ AccBangClosure (ℍ := ℍ)

def AccInst : Prop := AccInstRoot (ℍ := ℍ) ∧ AccInstPoly (ℍ := ℍ)

def AccReadFields : Prop := AccReadFieldsRoot (ℍ := ℍ) ∧ AccReadFieldsCb (ℍ := ℍ) ∧
  AccReadFieldsLoad (ℍ := ℍ) ∧ AccReadFieldsCopy (ℍ := ℍ) ∧ AccReadFieldsAlloc (ℍ := ℍ)

def AccMutFields : Prop := AccMutFieldsRoot (ℍ := ℍ) ∧ AccMutFieldsFlip (ℍ := ℍ) ∧
  AccMutFieldsPoke (ℍ := ℍ) ∧ AccMutFieldsSwap (ℍ := ℍ)

def AccReadFamily : Prop := AccReadFamilyRoot (ℍ := ℍ) ∧ AccReadCb (ℍ := ℍ) ∧
  AccReadFamilyWithborF2 (ℍ := ℍ)

def AccBlockSwap : Prop := AccBlockSwapRoot (ℍ := ℍ) ∧ AccSwapCb (ℍ := ℍ) BB ∧
  AccBlockSwapWithborS (ℍ := ℍ)

def AccCountFold : Prop := AccCountFoldRoot (ℍ := ℍ) ∧ AccCountAlg (ℍ := ℍ) ∧ AccFreeLAlg (ℍ := ℍ)

def AccSumList : Prop := AccSumListRoot (ℍ := ℍ) ∧ AccSumIAlg (ℍ := ℍ) ∧ AccFreeIAlg (ℍ := ℍ)

def AccCount : Prop := AccCountRoot (ℍ := ℍ) ∧ AccCountZero (ℍ := ℍ) ∧ AccCountStep (ℍ := ℍ) ∧
  AccCountCb (ℍ := ℍ) ∧ AccCountLoad (ℍ := ℍ)

def AccCounter : Prop := AccCounterRoot (ℍ := ℍ) ∧ AccCounterStep (ℍ := ℍ) ∧ AccCntCb (ℍ := ℍ)

def AccPass : Prop := AccPassRoot (ℍ := ℍ) ∧ AccPassCb (ℍ := ℍ) ∧ AccPassF (ℍ := ℍ) ∧
  AccPassWithbor3 (ℍ := ℍ) ∧ AccCounterStep (ℍ := ℍ)

def AccArr : Prop := AccArrRoot (ℍ := ℍ) ∧ AccTab10 (ℍ := ℍ) ∧ AccDropI32 (ℍ := ℍ)

/-- S1. -/
def AccPairLoad : Prop := AccPairLoadRoot (ℍ := ℍ) ∧ AccPairLoadCb (ℍ := ℍ) ∧
  AccPairLoadLoader (ℍ := ℍ) ∧ AccPairLoadWithbor (ℍ := ℍ) ∧ AccPairLoadWithload (ℍ := ℍ) ∧
  AccPairLoadAlloc (ℍ := ℍ) ∧ AccPairLoadFree (ℍ := ℍ) ∧ AccPairLoadForget (ℍ := ℍ) ∧
  AccImmBorrowAlloc (ℍ := ℍ) ∧ AccImmBorrowFree (ℍ := ℍ)

/-- S1′. -/
def AccPairLoadU : Prop := AccPairLoadURoot (ℍ := ℍ) ∧ AccPairLoadCbU (ℍ := ℍ) ∧
  AccPairLoadLoaderU (ℍ := ℍ) ∧ AccPairLoadWithbor (ℍ := ℍ) ∧ AccPairLoadWithloadU (ℍ := ℍ) ∧
  AccPairLoadAlloc (ℍ := ℍ) ∧ AccPairLoadFree (ℍ := ℍ) ∧ AccPairLoadForget (ℍ := ℍ) ∧
  AccImmBorrowAlloc (ℍ := ℍ) ∧ AccImmBorrowFree (ℍ := ℍ)

/-- S3. -/
def AccBangUse : Prop := AccBangUseRoot (ℍ := ℍ) ∧ AccBangUseBody (ℍ := ℍ) ∧
  AccBangUseDeref (ℍ := ℍ) ∧ AccBangUseInst (ℍ := ℍ) ∧ AccBangUseCall (ℍ := ℍ) ∧
  AccBangUseCb (ℍ := ℍ) ∧ AccBangUseBorrower (ℍ := ℍ) ∧ AccBangUseWithbor (ℍ := ℍ) ∧
  AccBangUseLoad (ℍ := ℍ) ∧ AccBangUseInnerLoad (ℍ := ℍ)

/-- P56. -/
def AccArrayGet : Prop := AccArrayGetRoot (ℍ := ℍ) ∧ AccArrayGetTab (ℍ := ℍ) ∧
  AccArrayGetRead (ℍ := ℍ) ∧ AccArrayGetLoad (ℍ := ℍ) ∧ AccArrayGetReadLoad (ℍ := ℍ)

def AccRecLog : Prop := AccRecLogRoot (ℍ := ℍ) ∧ AccRecLogStep (ℍ := ℍ) ∧ AccRecLogClause (ℍ := ℍ)

def AccStdio : Prop := AccMkInput (ℍ := ℍ) ∧ AccMkOutput (ℍ := ℍ) ∧ AccTakeInput (ℍ := ℍ) ∧
  AccTakeOutput (ℍ := ℍ) ∧ AccReadByte (ℍ := ℍ) ∧ AccWriteAll (ℍ := ℍ)

/-- **The proved part of S1**: every entry of `pairLoad` but its two borrow constants'. -/
theorem accPairLoad_but_constants :
    AccPairLoadRoot (ℍ := ℍ) ∧ AccPairLoadCb (ℍ := ℍ) ∧ AccPairLoadLoader (ℍ := ℍ) ∧
      AccPairLoadAlloc (ℍ := ℍ) ∧ AccPairLoadFree (ℍ := ℍ) ∧ AccPairLoadForget (ℍ := ℍ) ∧
      AccImmBorrowAlloc (ℍ := ℍ) ∧ AccImmBorrowFree (ℍ := ℍ) :=
  ⟨accPairLoadRoot, accPairLoadCb, accPairLoadLoader, accPairLoadAlloc, accPairLoadFree,
    accPairLoadForget, accImmBorrowAlloc, accImmBorrowFree⟩

/-- **The proved part of S3**: the producer, the call, both callbacks and the root. -/
theorem accBangUse_proved :
    AccBangUseRoot (ℍ := ℍ) ∧ AccBangUseBody (ℍ := ℍ) ∧ AccBangUseCall (ℍ := ℍ) ∧
      AccBangUseCb (ℍ := ℍ) ∧ AccBangUseBorrower (ℍ := ℍ) :=
  ⟨accBangUseRoot, accBangUseBody, accBangUseCall, accBangUseCb, accBangUseBorrower⟩

end Programs

end ProbeD1

end
