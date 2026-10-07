import Core.Stdio
import Targets.Base.Rows

/-!
# Base — Core's machine as B, I and the Instance read it (RESTRUCTURE §0, base)

DESIGN D5–D9: platforms (a comodel, Ahman–Bauer Def. 1), runs under a
platform (`PStep`), first-order data (`VTy.Data`, `DataVal`), final configurations, the runtime's
outermost driver (`RStep`), where a run may stop (`StopsIn`), every-run safety and termination
(`SafeRuns`, `Terminates`, `SafeDrive`), the div-free answers (`DivFree`), and a run as the list of
its configurations with its allocations and releases (`PRun`, `Allocated`, `Released`, `NoReuse`,
`ReleasedOnce`).  `ReleasedOnce` is an event-level property of a run: on a run that reuses no
location it follows from the empty memory at both ends (`Targets/B/Release.lean`).

A stop is irreducible (`stop_irreducible`), and `ARun.rest` at an irreducible end
(`arun_rest_irr`).  For B5 (RESTRUCTURE §2.4): `Named`, `Expr.mapLoc`, `Heap.push`, `RelAt`,
`Expr.MentionsArr`, `BlocksAffine`, `Bump`, `BumpSim`; for the drive phase: `SafeDriveFrom`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core

/-- First-order data at `k` bound variables: `1`, `0`, integers, `⊗`, `⊕`, and `μX. A` over these.
No location, no code, no capability. -/
inductive VTy.DataB : Nat → VTy → Prop
  | unit (k) : VTy.DataB k .unit
  | zero (k) : VTy.DataB k .zero
  | int (k w) : VTy.DataB k (.int w)
  | tvar {k n} : n < k → VTy.DataB k (.tvar n)
  | tensor {k A B} : VTy.DataB k A → VTy.DataB k B → VTy.DataB k (.tensor A B)
  | sum {k A B} : VTy.DataB k A → VTy.DataB k B → VTy.DataB k (.sum A B)
  | mu {k A} : VTy.DataB (k + 1) A → VTy.DataB k (.mu A)

/-- A closed data type. -/
def VTy.Data (A : VTy) : Prop := VTy.DataB 0 A


end BoCa.Fig16.LogRel.Core

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)

/-- The values of a closed data type (`BytesV`'s shape, `Core/Stdio.lean`): the least fixed point,
with `μ` read at its unrolling. -/
inductive DataVal : VTy → Val → Prop
  | unit : DataVal .unit .unit
  | int {w v} : v.IsInt w → DataVal (.int w) v
  | pair {A B v₁ v₂} : DataVal A v₁ → DataVal B v₂ → DataVal (.tensor A B) (Val.pair v₁ v₂)
  | inj₁ {A B v} : DataVal A v → DataVal (.sum A B) (Val.inj₁ v)
  | inj₂ {A B v} : DataVal B v → DataVal (.sum A B) (Val.inj₂ v)
  | roll {A v} : DataVal (VTy.inst (.mu A) A) v → DataVal (.mu A) v

/-- A platform: the operations it answers, its state, and a co-operation per operation. -/
structure Platform where
  ops : Row
  St  : Type
  s₀  : St
  co  : St → UInt32 → UInt32 → Val → Option (Val × St)

/-- The protocol: data operations that resume once; every well-formed request answered; answers at
the operation's answer type. -/
structure Platform.Respects (P : Platform) : Prop where
  uniq  : P.ops.Uniq
  nz    : P.ops.NZ
  lin   : ∀ o ∈ P.ops, o.q = .lin ∧ o.abort = false
  data  : ∀ o ∈ P.ops, o.A.Data ∧ o.B.Data
  total : ∀ s o v, o ∈ P.ops → DataVal o.A v → ∃ w s', P.co s o.n o.i v = some (w, s')
  typed : ∀ s s' o v w, o ∈ P.ops → DataVal o.A v → P.co s o.n o.i v = some (w, s') →
            DataVal o.B w

/-- The platform with no operation. -/
def Platform.none : Platform := ⟨[], Unit, (), fun _ _ _ _ => Option.none⟩

theorem platformNone_respects : Platform.none.Respects where
  uniq := List.Pairwise.nil
  nz := fun _ h => absurd h (by simp [Platform.none])
  lin := fun _ h => absurd h (by simp [Platform.none])
  data := fun _ h => absurd h (by simp [Platform.none])
  total := fun _ _ _ h => absurd h (by simp [Platform.none])
  typed := fun _ _ _ _ _ h => absurd h (by simp [Platform.none])

/-- A configuration under a platform: memory, term, platform state. -/
structure Conf (P : Platform) where
  μ : Heap
  e : Expr
  s : P.St

/-- A step under a platform: a machine step (`Step1`: every allocator's choice), or the platform
answering an operation of its row that no handler of the program catches. -/
inductive PStep (P : Platform) : Conf P → Conf P → Prop
  | mach {μ μ' : Heap} {e e' : Expr} {s : P.St} :
      Step1 (ℍ := ℍ) μ e μ' e' → PStep P ⟨μ, e, s⟩ ⟨μ', e', s⟩
  | plat {μ : Heap} {s s' : P.St} {K : Kont} {n i : UInt32} {v w : Val} {o : OpSig} :
      K.HasHnd n = false → Row.find P.ops n i = some o →
      P.co s n i v = some (w, s') →
      PStep P ⟨μ, K.plug (performE (.val (opPayload n i v))), s⟩ ⟨μ, K.plug (.val w), s'⟩

/-- Runs under a platform. -/
abbrev PSteps (P : Platform) := Relation.ReflTransGen (PStep (ℍ := ℍ) P)

/-- A machine run is a run under every platform, its state unchanged. -/
theorem psteps_of_steps (P : Platform) (s : P.St) {μ μ' : Heap} {e e' : Expr}
    (h : Steps (ℍ := ℍ) μ e μ' e') : PSteps (ℍ := ℍ) P ⟨μ, e, s⟩ ⟨μ', e', s⟩ := by
  induction h with
  | refl => exact .refl
  | more h _ ih => exact .head (PStep.mach h) ih

/-- The initial configuration: the empty memory and the platform's initial state. -/
def init (P : Platform) (e : Expr) : Conf P := ⟨Adequacy.emptyMem, e, P.s₀⟩

/-- Final: a value of the data answer type, with the memory empty. -/
def Final (P : Platform) (A : VTy) (c : Conf P) : Prop :=
  ∃ v, c.e = .val v ∧ DataVal A v ∧ c.μ = Adequacy.emptyMem

/-- The phase of the outermost driver. -/
inductive Phase
  | main
  | drive
  deriving DecidableEq, Repr

/-- `next` of a loop thunk: its first observation (`forceE` at `ν` is the value itself). -/
def nextE (l : Val) : Expr := .app (.val l) (.val (Val.inj₁ .unit))

/-- The runtime drives a `main` that returns a loop until it finishes; it never closes it
(SPEC §11, §14). -/
inductive RStep (P : Platform) : Conf P × Phase → Conf P × Phase → Prop
  | run   {c c' : Conf P} {ph : Phase} : PStep (ℍ := ℍ) P c c' → RStep P (c, ph) (c', ph)
  | start {μ : Heap} {s : P.St} {l : Val} :
      RStep P (⟨μ, .val l, s⟩, .main) (⟨μ, nextE l, s⟩, .drive)
  | again {μ : Heap} {s : P.St} {l : Val} :
      RStep P (⟨μ, .val (Val.inj₂ l), s⟩, .drive) (⟨μ, nextE l, s⟩, .drive)

/-- A finished drive: the loop's answer, data, with the memory empty. -/
def FinalDrive (P : Platform) (A : VTy) : Conf P × Phase → Prop
  | (c, .drive) => ∃ a, c.e = .val (Val.inj₁ a) ∧ DataVal A a ∧ c.μ = Adequacy.emptyMem
  | (_, .main)  => False

/-- A stop at an operation of the row `S`: a `perform` that no handler of its name catches, or a
`raise` that no frame catches, of an operation `S` has, of the matching kind. -/
def StopsIn (S : Row) (e : Expr) : Prop :=
  (∃ K n i v o, e = Kont.plug K (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
      Row.find S n i = some o ∧ o.abort = false) ∨
  (∃ K n i v o, e = Kont.plug K (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
      Row.find S n i = some o ∧ o.abort = true)

/-- Every-run safety: no run gets stuck; a run that cannot step is final. -/
def SafeRuns (P : Platform) (A : VTy) (e : Expr) : Prop :=
  ∀ c, PSteps (ℍ := ℍ) P (init P e) c → Final P A c ∨ ∃ c', PStep (ℍ := ℍ) P c c'

/-- Termination: every run continues to a final configuration, and no run is infinite. -/
def Terminates (P : Platform) (A : VTy) (e : Expr) : Prop :=
  (∀ c, PSteps (ℍ := ℍ) P (init P e) c → ∃ c', PSteps (ℍ := ℍ) P c c' ∧ Final P A c') ∧
  ¬ ∃ f : ℕ → Conf P, f 0 = init P e ∧ ∀ n, PStep (ℍ := ℍ) P (f n) (f (n + 1))

/-- A driven loop: every finite prefix of the (possibly infinite) drive is safe. -/
def SafeDrive (P : Platform) (A : VTy) (e : Expr) : Prop :=
  ∀ rc, Relation.ReflTransGen (RStep (ℍ := ℍ) P) (init P e, .main) rc →
    FinalDrive P A rc ∨ ∃ rc', RStep (ℍ := ℍ) P rc rc'

/-- The answers whose programs terminate.  Divergence lives in `Loop` codata (decision 35), so
every `F_S A` at a data `A` is div-free; if divergence moved into rows, this predicate changes, and
the targets that read it with it. -/
def DivFree (_S : Row) (A : VTy) : Prop := A.Data

/-- A run, as the list of its configurations. -/
inductive PRun (P : Platform) : List (Conf P) → Prop
  | one (c : Conf P) : PRun P [c]
  | cons {c c' : Conf P} {cs : List (Conf P)} : PStep (ℍ := ℍ) P c c' → PRun P (c' :: cs) →
      PRun P (c :: c' :: cs)

/-- The run allocates `ℓ` at its `k`-th step. -/
def Allocated {P : Platform} (cs : List (Conf P)) (k : Nat) (ℓ : Loc) : Prop :=
  ∃ c c', cs[k]? = some c ∧ cs[k + 1]? = some c' ∧ c.μ ℓ = none ∧ (c'.μ ℓ).isSome

/-- The run releases `ℓ` at its `k`-th step. -/
def Released {P : Platform} (cs : List (Conf P)) (k : Nat) (ℓ : Loc) : Prop :=
  ∃ c c', cs[k]? = some c ∧ cs[k + 1]? = some c' ∧ (c.μ ℓ).isSome ∧ c'.μ ℓ = none

/-- The run never allocates a location it released earlier. -/
def NoReuse {P : Platform} (cs : List (Conf P)) : Prop :=
  ∀ j k ℓ, j < k → Released cs j ℓ → ¬ Allocated cs k ℓ

/-- Every location the run allocates is released exactly once, and none is released that the run
did not allocate.  An event-level property of a run: on a run that reuses no location, from the
empty memory to the empty memory, it follows from the ends alone (`releasedOnce_of_ends`). -/
def ReleasedOnce {P : Platform} (cs : List (Conf P)) : Prop :=
  (∀ ℓ k, Allocated cs k ℓ → ∃! j, Released cs j ℓ) ∧
  (∀ ℓ j, Released cs j ℓ → ∃ k, k < j ∧ Allocated cs k ℓ)


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A plugged operation its context does not catch takes no step. -/
theorem opPlug_no_step {μ μ' : Heap} {K : Kont} {r : Bool} {p : Val} {n : UInt32} {t' : Expr}
    (hn : payloadName p = some n) (hK : OpFree r n K) :
    ¬ Step1 (ℍ := ℍ) μ (K.plug (opE r p)) μ' t' := by
  rintro ⟨K', a, a', he, -, hh⟩
  rcases plug_cmp K K' (opE_not_isVal r p) hh.not_isVal he with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · have hK'' := plug_primApp (h₁.symm.trans (opE_eq_app r p)) hh.not_isVal
    subst hK''
    have h₀ : OpFree r n Kont.hole := by cases r <;> simp [OpFree, Kont.HasHnd, Kont.Catches]
    have ha : a = opE r p := by simpa [Kont.plug] using h₁.symm
    subst ha
    exact head_not_opPlug hn h₀ hh
  · subst h₂
    exact head_not_opPlug hn (opFree_right hK) (h₁ ▸ hh)

/-- **D7: a stop is irreducible.** -/
theorem stop_irreducible {S : Row} {μ μ' : Heap} {e e' : Expr} (h : StopsIn S e) :
    ¬ Step1 (ℍ := ℍ) μ e μ' e' := by
  rcases h with ⟨K, n, i, v, o, rfl, hK, -, -⟩ | ⟨K, n, i, v, o, rfl, hK, -, -⟩
  · exact opPlug_no_step (r := false) (payloadName_opPayload n i v) hK
  · exact opPlug_no_step (r := true) (payloadName_opPayload n i v) hK

/-- `ARun.rest` at an irreducible end. -/
theorem arun_rest_irr {A : Alloc} {i j j₁ : Nat} {μ μ' μ₁ : Heap} {e e₁ t : Expr}
    (hirr : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) A j μ' t k₂ μ₂ e₂)
    (h' : ARun (ℍ := ℍ) A i μ e j₁ μ₁ e₁) :
    ARun (ℍ := ℍ) A i μ e j μ' t → ARun (ℍ := ℍ) A j₁ μ₁ e₁ j μ' t := by
  induction h' with
  | refl => exact id
  | more s' _ ih =>
      intro h
      cases h with
      | refl => exact (hirr _ _ _ s').elim
      | more s t =>
          obtain ⟨rfl, rfl, rfl⟩ := AStep1.deterministic s s'
          exact ih t


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### B5's machinery: names, renamings, bump runs (RESTRUCTURE §2.4)

Restated over this branch's Core from TwoRun (`Fresh.lean`, `Sim.lean`, `Rename.lean`), which does
not build on this branch. -/

/-- `ℓ` occurs in the term. -/
def _root_.BoCa.Expr.MentionsLoc (ℓ : Loc) : Expr → Prop
  | .loc ℓ' => ℓ' = ℓ
  | .var _ | .unit | .prim _ => False
  | .pair a b | .seq a b | .letpair a b | .app a b => a.MentionsLoc ℓ ∨ b.MentionsLoc ℓ
  | .inj₁ a | .inj₂ a | .lam a => a.MentionsLoc ℓ
  | .case a b c => a.MentionsLoc ℓ ∨ b.MentionsLoc ℓ ∨ c.MentionsLoc ℓ

/-- `Named μ e ℓ`: the heap holds `ℓ`, the term mentions it, or a stored value mentions it. -/
def Named (μ : Heap) (e : Expr) (ℓ : Loc) : Prop :=
  (μ ℓ).isSome ∨ e.MentionsLoc ℓ ∨ ∃ m v, μ m = some v ∧ v.1.MentionsLoc ℓ

/-- Every location renamed along `g` (TwoRun's `Expr.rename` at a function). -/
def _root_.BoCa.Expr.mapLoc (g : Loc → Loc) : Expr → Expr
  | .var i         => .var i
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.mapLoc g) (e₂.mapLoc g)
  | .inj₁ e        => .inj₁ (e.mapLoc g)
  | .inj₂ e        => .inj₂ (e.mapLoc g)
  | .lam b         => .lam (b.mapLoc g)
  | .loc ℓ         => .loc (g ℓ)
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.mapLoc g) (e₂.mapLoc g)
  | .letpair e₁ e₂ => .letpair (e₁.mapLoc g) (e₂.mapLoc g)
  | .case e e₁ e₂  => .case (e.mapLoc g) (e₁.mapLoc g) (e₂.mapLoc g)
  | .app f a       => .app (f.mapLoc g) (a.mapLoc g)

theorem isVal_mapLoc (g : Loc → Loc) {e : Expr} (h : IsVal e) : IsVal (e.mapLoc g) := by
  induction h with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => exact .storeV ih

/-- A value with every location renamed along `g`. -/
def _root_.BoCa.Val.mapLoc (g : Loc → Loc) (v : Val) : Val := ⟨v.1.mapLoc g, isVal_mapLoc g v.2⟩

open Classical in
/-- `μ`'s cells moved along `g`, their values renamed: the cell at `g ℓ` is `μ ℓ`'s, for a live
`ℓ` (one, where `g` is injective on the live heap). -/
def _root_.BoCa.BoLo.Heap.push (g : Loc → Loc) (μ : Heap) : Heap := fun ℓ' =>
  if h : ∃ ℓ, g ℓ = ℓ' ∧ (μ ℓ).isSome then (μ (Classical.choose h)).map (Val.mapLoc g) else none

/-- The array value `(ℓ, n)` (`Val.arr ℓ n`) occurs in the term. -/
def _root_.BoCa.Expr.MentionsArr (ℓ : Loc) (n : UInt32) : Expr → Prop
  | .pair a b => (a = .loc ℓ ∧ b = (Val.i32 n).1) ∨ a.MentionsArr ℓ n ∨ b.MentionsArr ℓ n
  | .var _ | .unit | .prim _ | .loc _ => False
  | .seq a b | .letpair a b | .app a b => a.MentionsArr ℓ n ∨ b.MentionsArr ℓ n
  | .inj₁ a | .inj₂ a | .lam a => a.MentionsArr ℓ n
  | .case a b c => a.MentionsArr ℓ n ∨ b.MentionsArr ℓ n ∨ c.MentionsArr ℓ n

/-- `g` moves as a block every `[ℓ, ℓ + n]` for an array value `(ℓ, n)` that the term or a stored
value holds: the array steps compute `ℓ + j` from `(ℓ, n)`, `idx` for `j < n` and `split` for
`j ≤ n` (its last part `(ℓ + n, 0)` is based at the end location). -/
def BlocksAffine (g : Loc → Loc) (μ : Heap) (e : Expr) : Prop :=
  ∀ ℓ n, (e.MentionsArr ℓ n ∨ ∃ m v, μ m = some v ∧ v.1.MentionsArr ℓ n) →
    ∀ j, j ≤ n.toNat → g (ℓ + j) = g ℓ + j

/-- Two configurations related by `g`: `g` is injective on `cB`'s live heap, `cA`'s term is `cB`'s
renamed, `cA`'s heap is `cB`'s pushed along `g`, and the platform states agree. -/
def RelAt {P : Platform} (g : Loc → Loc) (cA cB : Conf P) : Prop :=
  Set.InjOn g {x | cB.μ x ≠ none} ∧ cA.e = cB.e.mapLoc g ∧ cA.μ = Heap.push g cB.μ ∧ cA.s = cB.s

/-- A run that allocates only locations no earlier configuration of it names: a bump allocator's
run.  It reuses nothing. -/
def Bump {P : Platform} (cs : List (Conf P)) : Prop :=
  ∀ k ℓ, Allocated cs k ℓ → ∀ j c, j ≤ k → cs[j]? = some c → ¬ Named c.μ c.e ℓ

/-- **The step-for-step simulation** (a lemma about the machine alone, OPEN: OQ-43 (b), or (c)
through a binary FP).  Where a configuration `cA` and a configuration `cB` are related by `g`, `g`
moves `cB`'s arrays as blocks, `cA` steps, and `cB` is not stuck, `cB` steps, allocating only
locations it does not name and outside `X`, to a configuration related to `cA`'s successor by a map that agrees
with `g` on what `cB` names; and the bump step can avoid any finite set `X` of locations (the
names of the run's earlier configurations: a bump allocator picks a location nothing has named).
TwoRun's `run_sim` (`TwoRun/Sim.lean:253`) is its shape for runs
with no array and no capture step; the extension to blocks, capture, `count`, `countTry`,
`boundedFix` and platform steps is not derived. -/
def BumpSim : Prop :=
  ∀ (P : Platform) (X : Finset Loc) (g : Loc → Loc) (cA cA' cB : Conf P), RelAt g cA cB →
    BlocksAffine g cB.μ cB.e → PStep (ℍ := ℍ) P cA cA' → (∃ cB'', PStep (ℍ := ℍ) P cB cB'') →
    ∃ cB' g', PStep (ℍ := ℍ) P cB cB' ∧
      (∀ ℓ, cB.μ ℓ = none → (cB'.μ ℓ).isSome → ¬ Named cB.μ cB.e ℓ ∧ ℓ ∉ X) ∧
      (∀ ℓ, Named cB.μ cB.e ℓ → g' ℓ = g ℓ) ∧ RelAt g' cA' cB' ∧ BlocksAffine g' cB'.μ cB'.e

/-! ### The drive from the drive phase -/

/-- `SafeDrive` from `(init P M, .drive)`: every finite prefix of the drive is safe. -/
def SafeDriveFrom (P : Platform) (A : VTy) (M : Expr) : Prop :=
  ∀ rc, Relation.ReflTransGen (RStep (ℍ := ℍ) P) (init P M, .drive) rc →
    FinalDrive P A rc ∨ ∃ rc', RStep (ℍ := ℍ) P rc rc'


end Targets

end
