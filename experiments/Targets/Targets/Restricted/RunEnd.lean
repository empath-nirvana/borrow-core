import Targets.Defs.Programs
import Targets.Restricted.EffectSafety
import Targets.Restricted.NonVacuity
import Targets.Statements.EndState
import LoopBorrow.Obstruction

/-!
# Targets — the run-end relation `↭` as a field of `SemWorld` (FIX-RUN-END)

**World:** [W], at every `M : SemWorld` unless a result names the pin (`SliceShape`) or a world:
`coreW` [Core σ=[]], and the witness worlds `leakW` and `carryW`.  The witness worlds exist only to
check the run-end laws (FIX-RUN-END §2) and the exclusion of a degenerate world (§3).  They are
not candidates for W.

`wpGW` ends every run under the field `M.Upd` (`Defs/World.lean`), which `SliceShape` pins to
Core's `↭` (`ResU.UpdV ρ π`, [TR] p. 5 row 18) on the nil slice.  `RunFrame` is the rest of a run's
end, and `wpGW_iff_runFrame` splits `wpGW` into `RunFrame`, the run-end relation and the
postcondition.

**AT02's run.**  `at02Body` is AT02's handled computation (`at02_eq`): it allocates a cell `c`,
lends it as `Mut` to a callback with `withborU dFlag`, and the callback performs the linear `Foo`
(`fooSig_lin`) before it reads through the lend.  Under every allocator `A`, from every count `k`,
the machine runs it from the empty memory to `Foo`'s stop `at02Stop c`, `c = A.pick k ∅ 1`
(`at02Body_run`), where it takes no step (`at02Stop_irr`).  The stop's continuation `at02StopK c`
holds `withborU`'s frame at `c`: the lend is open.  `heldRes c α` holds it in the shape [TR] 6.65
gives a lend, `c ↦ mut(α, inj₁ (), ∅, ⊤)`: `TW.alloc` of the cell from `∅`, then `TW.mutFold`
(`held_arises`).

* `at02_runEnd`: an end of a run of `at02Body` from the empty configuration that ends under Core's
  `↭`, with a postcondition that admits only values and stops of an operation table, is `Foo`'s
  stop, and its `π` holds no `mut` cell at `c`: `↭` from `∅` forbids every `mut` cell in `⦇π⦈`
  (LoopBorrow's `not_upd_of_new_mut`).  On the nil slice the `→` half of the `Upd` pin gives
  Core's `↭` (`at02_runEnd_nil`).  At a world whose `Upd` gives Core's `↭` at every index, the
  run a `wpGW` of `at02Body` from the empty configuration provides under such a postcondition
  stops at `Foo` with no `mut` cell at `c` (`wpGW_at02`).
* `at02_held_end`: at every world meeting `SliceShape`, the end at `Foo`'s stop holding the lend
  meets every conjunct of `RunFrame` at the nil index (the frame, the compositions, both lowerings,
  the run, `NoOwn`, `M.Fam`, `M.Stop`) and fails `↭`, so `M.Upd` there.  A 6.65 lend leaves the
  open 6.64 frames and the records unchanged (`TW.mutFold`), so at Core's world
  (`at02_held_end_core`) the clause that excludes it is `↭`, not R-T1.
* `at02_unfolded_end`: the same end with `c` unfolded, `c ↦ own(inj₁ ())`, meets `RunFrame` and
  `M.Upd` at the nil index.

**A degenerate world does not satisfy done** (FIX-RUN-END §3).  Done's program-level conjuncts do
not mention the world (`endState_prog`, `Restricted/Corollaries.lean`).
* `not_sliceShape_of_updTop`: a run-end relation that relates everything does not meet the pin.
* `not_adequate_of_leak`: at every world whose relation at `F_S A` is its runs (`EffInterp`) and
  whose data values hold nothing (`DataVals`), a run-end relation that lets a run from σ = [] leave
  a fresh cell behind as a `mut` cell in its garbage (`LeakAt`) puts `leakProg` in the relation,
  and `leakProg` stops with the cell allocated.  So `¬ Adequate M` and `¬ EndStateAt J M Adm RF`
  (`not_endState_of_leak`).  `leakW` meets the pin, `EffInterp`, `DataVals` and `LeakAt`; its
  `Upd` and `Stop` are true unless both ends are on the nil slice, and its `Fam` is true off it.
  It fails `Adequate` (`not_adequate_leakW`) and `UpdReclaim` (`not_updReclaim_leakW`).
* `upd2Reclaim_excludes_held`: a reclaim law that reads only `↭`'s two resources excludes AT02's
  held end at every end index it is stated at.

**The run-end laws admit an end that holds a `Mut` lend as a cell** (FIX-RUN-END §4).  `carryW`'s
stack is the `mut` cells carried open.  A run is Core's `↭` once the carried cells are taken out
at both ends (`ρ/dom(σ)`, `π/dom(σ′)`); the carried cells in its end are held by its post; a lend
it opened, or a carried cell it held, sits in its end as the end stack's cell; a carried cell it
did not hold it does not hold at its end, and that cell is carried unchanged.  `carryW` meets the
pin, `UpdRefl`, `UpdOwn`, `UpdSeq` and `UpdReclaim`.  AT02's end at `Foo` holding the lend meets
every conjunct of the run's end at `carryW` but the postcondition, at the index whose stack is the
lend (`at02_held_end_carry`).  The run that closes the lend is admitted at its `Upd` conjunct
(`upd_close_carryW`); that machine run is not built.  `carryW` reads σ as what the whole
configuration carries (`fam_nil_held_carryW`, `not_close_from_nil_carryW`).  The printed forms of
6.50 and 6.27 at W, stated at every pair of indices, exclude both runs: `not_updOutlives_of_opened`,
`not_updMutBack_of_closed`, so `not_updOutlives_carryW` and `not_updLendBack_carryW`.  `carryW` is
not shown to meet any conjunct of done.

**A 6.64 lend at AT02's stop.**  `at02_imm_end`: at every world meeting `SliceShape`, AT02's run
ended at `Foo` in the configuration a 6.64 lend gives, `c ↦ imm({α}, inj₁ (), ∅)` with 6.64's
record `immRec c` open in the visible frames and in the index.  It arises (`imm_arises`,
`imm_tagged`), meets every other conjunct of `RunFrame` at the nil index, and fails R-T1, `↭`
(LoopBorrow's `not_upd_of_new_imm`) and so `M.Upd`.  `StopVisible` excludes the same visible frame
at every index (`not_stop_imm_of_stopVisible`).  The unwinding constant's term is the same for 6.64
and 6.65 (`withborUE d` at `withbor1UTy` and `withbor2UTy`), so this is AT02's machine run ended in
the configuration a 6.64 lend gives.  AT02's callback reads through `withswap`, which a 6.64 lend
does not type, and no 6.64-typed program is built here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.RunEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core Targets
open BoCa.BoLo (Heap Step1 Head Kont Alloc ARun AStep1 AHead performE opPayload)
open BoCa.Lifetime (LSub)
open BoCa.Fig16.LogRel.Core.EffPrograms (dFlag Flag)
open BoCa.Fig16.LogRel.Core.LoopBorrow (not_upd_of_new_mut not_upd_of_new_imm mutCell
  mutCell_valid mutCell_flatAt trueP)
open BoCa.Programs (free' alloc')

/-! ### `wpGW`'s run end -/

/-- The conjuncts of the end of a `wpGW` run other than the run-end relation and the
postcondition. -/
def RunFrame (M : SemWorld) (ρf fρ : WRes) (ps : List FrameRec) (i : Idx M.Stk) (e : Expr)
    (A : Alloc) (k : Nat) (ρ' ρp fρ' fρ'p π : WRes) (t : Expr) (μ μ' : Heap)
    (ps' : List FrameRec) (i' : Idx M.Stk) : Prop :=
  ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.Lower fρ μ ∧
    ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧ (∃ k', ARun (ℍ := ℍ) A k μ e k' μ' t) ∧
    ResU.CompS ρ' ρp π ∧ NoOwn ρp ∧ M.Fam fρ'p ps' i' ∧ M.Stop (ps, i) (ps', i') t

/-- `wpGW` is `RunFrame`, the run-end relation from the run's resource `ρ` to `π = ρ′ ● ρ⁺`, and
the postcondition. -/
theorem wpGW_iff_runFrame (M : SemWorld) (i : Idx M.Stk) (e : Expr)
    (Q : Idx M.Stk → Expr → WProp) (ρ : WRes) :
    wpGW (ℍ := ℍ) M i e Q ρ ↔
      ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
        M.Fam fρ ps i → ∀ (A : Alloc) (k : Nat),
        ∃ (ρ' ρp fρ' fρ'p π : WRes) (t : Expr) (μ μ' : Heap) (ps' : List FrameRec)
          (i' : Idx M.Stk),
          RunFrame (ℍ := ℍ) M ρf fρ ps i e A k ρ' ρp fρ' fρ'p π t μ μ' ps' i' ∧
            M.Upd i i' ρ ρ' π ∧ Q i' t ρ' := by
  constructor
  · intro h ρf fρ ps h₁ h₂ h₃ A k
    obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀,
      a₁₁, a₁₂, a₁₃⟩ := h ρf fρ ps h₁ h₂ h₃ A k
    exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i',
      ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₁₀, a₁₁, a₁₂⟩, a₉, a₁₃⟩
  · intro h ρf fρ ps h₁ h₂ h₃ A k
    obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i',
      ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₁₀, a₁₁, a₁₂⟩, a₉, a₁₃⟩ := h ρf fρ ps h₁ h₂ h₃ A k
    exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀,
      a₁₁, a₁₂, a₁₃⟩

/-! ### A `mut` cell at a run's end -/

/-- `⦇π⦈(ℓ) = mut(_, _, _, _)`: `π` holds a `mut` cell at `ℓ`, at any lifetime and predicate. -/
def HeldAt (π : WRes) (l : Loc) : Prop :=
  ∃ (b : Life) (v : Val) (χ : WRes) (h : χ.InStratum b) (P : Val → SPropS Loc Val b)
    (hw : P v ⟨χ, h⟩), π.FlatAt l (CellU.mutOf b v χ h P hw)

/-- `⦇∅⦈` holds no cell. -/
theorem not_flatAt_empty (l : Loc) (ψ : CellU Loc Val) :
    ¬ ResU.FlatAt (PMap.empty : WRes) l ψ := by
  rintro ⟨σ, hσ, hg⟩
  rw [ResU.Flat.functional hσ BoCa.Fig16.BoLo.flat_empty, PMap.empty_get] at hg
  cases hg

/-- **`↭` from `∅` forbids a `mut` cell at the run's end**: `not_upd_of_new_mut` at the empty
start. -/
theorem not_updV_empty_of_held {π : WRes} {l : Loc} (h : HeldAt π l) :
    ¬ ResU.UpdV (PMap.empty : WRes) π := by
  obtain ⟨b, v, χ, hχ, P, hw, hπ⟩ := h
  exact fun hu => not_upd_of_new_mut hπ (fun _ _ _ _ hf => not_flatAt_empty l _ hf) hu.1

/-- A `mut` cell holds no own cell. -/
theorem noOwn_mutCell (l : Loc) (b : Life) (v : Val) : NoOwn (mutCell l b v) := by
  refine noOwn_iff.mpr fun m ψ hm => ?_
  by_cases hml : m = l
  · subst hml
    simp only [mutCell, ResU.single_get_self] at hm
    cases Option.some.inj hm
    rw [CellU.kind_mutOf]
    exact fun h => Kind.noConfusion h
  · simp only [mutCell] at hm
    rw [ResU.single_get_ne _ hml] at hm; exact absurd hm (by simp)

/-- A configuration that steps is neither a value nor a stop of an operation table. -/
theorem not_post_of_step {M : SemWorld} {μ μ' : Heap} {t t' : Expr}
    (hs : Step1 (ℍ := ℍ) μ t μ' t') (T : OpTabI (Idx M.Stk)) (Q : Idx M.Stk → Val → WProp)
    (P : Idx M.Stk → Expr → WProp) (i : Idx M.Stk) (ρ : WRes) :
    ¬ (valPostI Q i t ρ ∨ opTabW M T i t P ρ) := by
  rintro (⟨v, hv, -⟩ | ⟨K', n, j, v, en, hp⟩ | ⟨K', n, j, v, en, hp⟩)
  · rw [hv] at hs; exact BoCa.BoLo.no_step_val hs
  · obtain ⟨⟨ht, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [ht] at hs
    exact opPlug_no_step (r := false) (payloadName_opPayload n j v) hK hs
  · obtain ⟨⟨ht, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [ht] at hs
    exact opPlug_no_step (r := true) (payloadName_opPayload n j v) hK hs

/-! ### AT02's body, run to `Foo` -/

/-- AT02's handled computation. -/
def at02Body : Expr := lendCell (.inj₁ unit') (cb (bindE fooE (.seq (.var 0) (readThrough 1))))

theorem at02_eq : at02 = handleWith 5 resumeArg at02Body := rfl

/-- `Foo : 1 ↠^lin 1`. -/
theorem fooSig_lin : fooSig.q = .lin := rfl

/-- `lendCell`'s tail `λ(c, r). free c; r`. -/
def lendTailV : Val := Val.lam (.letpair (.var 0) (.seq (dropB (.app free' (.var 1))) (.var 0)))

/-- AT02's callback `Λ. λm. (Foo; read m)`. -/
def at02CbV : Val := Val.lam (.val (Val.lam (bindE fooE (.seq (.var 0) (readThrough 1)))))

/-- `withborU dFlag`'s frame at the cell `c`: `(λb. (c, b), λ_. dFlag c)`. -/
def lendFrameV (c : Loc) : Val :=
  Val.pair (Val.lam (.pair (.val (Val.loc c)) (.var 0))) (Val.lam (.app dFlag (.val (Val.loc c))))

/-- The continuation at `Foo`'s stop: the callback's rest at `m = c`, under `withborU`'s frame
`ubind (λb. (c, b), λ_. dFlag c)`, under `lendCell`'s tail. -/
def at02StopK (c : Loc) : Kont :=
  .appR (.val lendTailV)
    (.appR (.app (.val (Val.prim .ubind)) (.val (lendFrameV c)))
      (.appR (.val (Val.lam ((Expr.seq (.var 0) (readThrough 1)).subst 1 (Val.loc c)))) .hole))

/-- `Foo`'s stop. -/
def at02Stop (c : Loc) : Expr := (at02StopK c).plug (performE (.val (opPayload 5 0 .unit)))

/-- No frame of the stop's continuation handles `Foo`'s name. -/
theorem at02StopK_hasHnd (c : Loc) : (at02StopK c).HasHnd 5 = false := rfl

/-- The empty memory. -/
def emptyHeap : Heap := fun _ => none

/-- The cell the allocator `A` gives at count `k` from the empty memory. -/
abbrev cellOf (A : Alloc) (k : Nat) : Loc := A.pick k emptyHeap 1

/-- The memory at `Foo`'s stop: the cell, holding `inj₁ ()`. -/
def stopHeap (c : Loc) : Heap := emptyHeap.upd c (Val.inj₁ .unit)

/-- **The run**: under every allocator, from every count, `at02Body` runs from the empty memory to
`Foo`'s stop: the allocation, then seven β-steps. -/
theorem at02Body_run (A : Alloc) (k : Nat) :
    ARun (ℍ := ℍ) A k emptyHeap at02Body (k + 1) (stopHeap (cellOf A k))
      (at02Stop (cellOf A k)) := by
  refine .more ⟨.appR (.val (Val.lam _)) .hole, _, _, rfl, rfl,
    AHead.alloc k emptyHeap (Val.inj₁ .unit) rfl⟩ ?_
  refine .more ⟨.hole, _, _, rfl, rfl, .det (Head.beta _ _ _) rfl⟩ ?_
  refine .more ⟨.hole, _, _, rfl, rfl, .det (Head.beta _ _ at02CbV) rfl⟩ ?_
  refine .more ⟨.hole, _, _, rfl, rfl, .det (Head.beta _ _ (withborUV dFlag)) rfl⟩ ?_
  refine .more ⟨.appR (.val lendTailV) (.appL .hole at02CbV), _, _, rfl, rfl,
    .det (Head.beta _ _ (Val.loc (cellOf A k))) rfl⟩ ?_
  refine .more ⟨.appR (.val lendTailV) .hole, _, _, rfl, rfl,
    .det (Head.beta _ _ at02CbV) rfl⟩ ?_
  refine .more ⟨.appR (.val lendTailV)
      (.appR (.app (.val (Val.prim .ubind)) (.val (lendFrameV (cellOf A k))))
        (.appL .hole (Val.loc (cellOf A k)))), _, _, rfl, rfl,
    .det (Head.beta _ _ Val.unit) rfl⟩ ?_
  refine .more ⟨.appR (.val lendTailV)
      (.appR (.app (.val (Val.prim .ubind)) (.val (lendFrameV (cellOf A k)))) .hole), _, _,
    rfl, rfl, .det (Head.beta _ _ (Val.loc (cellOf A k))) rfl⟩ ?_
  exact .refl _ _ _

/-- **`Foo`'s stop takes no step.** -/
theorem at02Stop_irr (A : Alloc) (k : Nat) (μ : Heap) (c : Loc) :
    ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) A k μ (at02Stop c) k₂ μ₂ e₂ :=
  fun _ _ _ h => opPlug_no_step (r := false) (payloadName_opPayload 5 0 .unit)
    (at02StopK_hasHnd c) h.toStep1

/-! ### Under Core's `↭`, no run end holds the lend as a cell -/

/-- **Every end of AT02's body from the empty configuration that ends under Core's `↭` is `Foo`'s
stop, and holds no `mut` cell at the lent cell**, when the postcondition admits only values and
stops of an operation table.  `↭` is a hypothesis: at a world it is what `M.Upd` gives where `Upd`
is Core's (`at02_runEnd_nil`, `wpGW_at02`). -/
theorem at02_runEnd {M : SemWorld} {i : Idx M.Stk} (T : OpTabI (Idx M.Stk))
    (Q : Idx M.Stk → Val → WProp) (P : Idx M.Stk → Expr → WProp) (A : Alloc) (k : Nat)
    {ρ' ρp fρ' fρ'p π : WRes} {t : Expr} {μ μ' : Heap} {ps' : List FrameRec} {i' : Idx M.Stk}
    (hR : RunFrame (ℍ := ℍ) M PMap.empty PMap.empty [] i at02Body A k ρ' ρp fρ' fρ'p π t μ μ'
      ps' i')
    (hU : ResU.UpdV (PMap.empty : WRes) π) (hQ : valPostI Q i' t ρ' ∨ opTabW M T i' t P ρ') :
    t = at02Stop (cellOf A k) ∧ ¬ HeldAt π (cellOf A k) := by
  obtain ⟨-, -, -, hμ, -, -, ⟨k', hr⟩, -⟩ := hR
  obtain rfl : μ = emptyHeap := ResU.Lower.functional hμ lower_empty
  have hrest := arun_rest_irr (at02Stop_irr A (k + 1) _ _) hr (at02Body_run A k)
  refine ⟨?_, fun hh => not_updV_empty_of_held hh hU⟩
  cases hrest with
  | refl => rfl
  | more s _ => exact absurd hQ (not_post_of_step s.toStep1 T Q P i' ρ')

/-- **On the nil slice, an end of AT02's body from the empty configuration holds no `mut` cell at
the lent cell**: at every world meeting `SliceShape`, an end from a nil index to a nil index whose
postcondition admits only values and stops of an operation table is `Foo`'s stop, with no `mut`
cell at `c`.  `at02_runEnd`, with the `→` half of the `Upd` pin for its `↭` step. -/
theorem at02_runEnd_nil {M : SemWorld} (hS : SliceShape M) {ls ls' : List SRec}
    (T : OpTabI (Idx M.Stk)) (Q : Idx M.Stk → Val → WProp) (P : Idx M.Stk → Expr → WProp)
    (A : Alloc) (k : Nat) {ρ' ρp fρ' fρ'p π : WRes} {t : Expr} {μ μ' : Heap}
    {ps' : List FrameRec}
    (hR : RunFrame (ℍ := ℍ) M PMap.empty PMap.empty [] (ls, M.nil) at02Body A k ρ' ρp fρ' fρ'p
      π t μ μ' ps' (ls', M.nil))
    (hU : M.Upd (ls, M.nil) (ls', M.nil) PMap.empty ρ' π)
    (hQ : valPostI Q (ls', M.nil) t ρ' ∨ opTabW M T (ls', M.nil) t P ρ') :
    t = at02Stop (cellOf A k) ∧ ¬ HeldAt π (cellOf A k) :=
  at02_runEnd T Q P A k hR ((hS.2.2.2.2.1 ls ls' _ ρ' π).mp hU) hQ

/-- **At every world whose run-end relation gives Core's `↭` at every index, the run a `wpGW` of
AT02's body from the empty configuration provides stops at `Foo` with no `mut` cell at the lent
cell**, when the postcondition admits only values and stops of an operation table.  So no such
world stops holding the lend as a cell. -/
theorem wpGW_at02 {M : SemWorld} (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π → ResU.UpdV ρ π)
    {i : Idx M.Stk} (T : OpTabI (Idx M.Stk)) (Q : Idx M.Stk → Val → WProp)
    (P : Idx M.Stk → Expr → WProp) (hF : M.Fam (PMap.empty : WRes) [] i)
    (h : wpGW (ℍ := ℍ) M i at02Body (fun i' t ρ' => valPostI Q i' t ρ' ∨ opTabW M T i' t P ρ')
      PMap.empty) (A : Alloc) (k : Nat) :
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (μ' : Heap) (ps' : List FrameRec) (i' : Idx M.Stk),
      RunFrame (ℍ := ℍ) M PMap.empty PMap.empty [] i at02Body A k ρ' ρp fρ' fρ'p π
        (at02Stop (cellOf A k)) emptyHeap μ' ps' i' ∧
      M.Upd i i' PMap.empty ρ' π ∧ ¬ HeldAt π (cellOf A k) := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', hR, hU, hQ⟩ :=
    (wpGW_iff_runFrame M i at02Body _ PMap.empty).mp h PMap.empty PMap.empty []
      (ResU.hash_empty_right ⟨_, BoCa.Fig16.BoLo.flat_empty⟩) (compS_empty_left _) hF A k
  obtain rfl : μ = emptyHeap := ResU.Lower.functional hR.2.2.2.1 lower_empty
  obtain ⟨rfl, hn⟩ := at02_runEnd T Q P A k hR (hC _ _ _ _ _ hU) hQ
  exact ⟨ρ', ρp, fρ', fρ'p, π, μ', ps', i', hR, hU, hn⟩

/-! ### The end holding the lend fails `↭`, and so the run-end relation on the nil slice -/

/-- The configuration holding the lend at `Foo`'s stop: `c ↦ mut(α, inj₁ (), ∅, ⊤)`, the cell
[TR] 6.65 folds the lender's `c ↦ own(inj₁ ())` into. -/
abbrev heldRes (c : Loc) (α : Life) : WRes := mutCell c α (Val.inj₁ .unit)

/-- **It arises**: `TW.alloc` of the cell from `∅`, then `TW.mutFold` of the lend. -/
theorem held_arises (c : Loc) (α : Life) : TW (heldRes c α) [] [] :=
  TW.mutFold (TW.alloc TW.empty lower_empty rfl (compS_empty_left _) (ResU.valid_single_own _ _))
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (mutCell_valid c α _)

/-- **At every world whose nil slice is Core's, the end at `Foo`'s stop holding the lend meets every
conjunct of `RunFrame` at the nil index, from the empty configuration `M.Fam` reaches there, and
fails `↭`, so `M.Upd` there.** -/
theorem at02_held_end {M : SemWorld} (hS : SliceShape M) (A : Alloc) (k : Nat) (α : Life) :
    M.Fam (PMap.empty : WRes) [] ([], M.nil) ∧
    RunFrame (ℍ := ℍ) M PMap.empty PMap.empty [] ([], M.nil) at02Body A k
      (heldRes (cellOf A k) α) PMap.empty (heldRes (cellOf A k) α) (heldRes (cellOf A k) α)
      (heldRes (cellOf A k) α) (at02Stop (cellOf A k)) emptyHeap (stopHeap (cellOf A k)) []
      ([], M.nil) ∧
    HeldAt (heldRes (cellOf A k) α) (cellOf A k) ∧
    ¬ ResU.UpdV (PMap.empty : WRes) (heldRes (cellOf A k) α) ∧
    ¬ M.Upd ([], M.nil) ([], M.nil) PMap.empty (heldRes (cellOf A k) α)
      (heldRes (cellOf A k) α) := by
  have hv : ResU.Valid (heldRes (cellOf A k) α) := mutCell_valid _ α _
  have hheld : HeldAt (heldRes (cellOf A k) α) (cellOf A k) :=
    ⟨_, _, _, _, _, _, mutCell_flatAt _ α _⟩
  have hnu : ¬ ResU.UpdV (PMap.empty : WRes) (heldRes (cellOf A k) α) :=
    not_updV_empty_of_held hheld
  refine ⟨(hS.2.1 _ _ _).mpr ⟨TW.empty, fun _ hx => absurd hx (by simp)⟩,
    ⟨ResU.hash_empty_right hv, compS_empty_left _, ResU.hash_symm (ResU.hash_empty_right hv),
      lower_empty, ResU.comp_empty_right _, ?_, ⟨_, at02Body_run A k⟩, ResU.comp_empty_right _,
      noOwn_empty, (hS.2.1 _ _ _).mpr ⟨held_arises _ α, fun _ hx => absurd hx (by simp)⟩,
      (hS.2.2.2.1 _ _ _ _ _).mpr ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩⟩,
    hheld, hnu, fun hu => hnu ((hS.2.2.2.2.1 _ _ _ _ _).mp hu)⟩
  exact (ResU.six25 (compS_empty_left _) hv (ResU.valid_single_own _ _)).mpr
    (lower_compS_own (compS_empty_left _) lower_empty rfl)

/-! ### The end with the lend unfolded meets `↭`, and so the run-end relation on the nil slice -/

/-- The configuration at `Foo`'s stop with the lend unfolded: `c ↦ own(inj₁ ())`. -/
abbrev ownRes (c : Loc) : WRes := ResU.single c (CellU.ownOf (Val.inj₁ .unit))

/-- `⦇ℓ ↦ own(v)⦈` holds `own(v)` at `ℓ` and nothing else. -/
theorem flatAt_single_own {c l : Loc} {v : Val} {ψ : CellU Loc Val}
    (h : ResU.FlatAt (ResU.single c (CellU.ownOf v) : WRes) l ψ) : ψ.kind = Kind.own := by
  obtain ⟨σ, hσ, hg⟩ := h
  rw [ResU.Flat.functional hσ (ResU.flat_single_own c v)] at hg
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
  exact CellU.kind_ownOf v

/-- `↭` from `∅` to `ℓ ↦ own(v)`: neither flattening holds a borrow cell. -/
theorem updV_empty_single_own (c : Loc) (v : Val) :
    ResU.UpdV (PMap.empty : WRes) (ResU.single c (CellU.ownOf v)) :=
  ⟨⟨fun l _ _ _ _ => ⟨fun hf => absurd hf (not_flatAt_empty l _),
      fun hf => absurd (flatAt_single_own hf) CellU.kind_immOf_ne_own⟩,
    fun l _ _ => ⟨fun ⟨_, _, _, _, hf⟩ => absurd hf (not_flatAt_empty l _),
      fun ⟨_, _, _, _, hf⟩ => absurd (flatAt_single_own hf) CellU.kind_mutOf_ne_own⟩⟩,
    ⟨_, BoCa.Fig16.BoLo.flat_empty⟩, ResU.valid_single_own c v⟩

/-- **At every world whose nil slice is Core's, the end at `Foo`'s stop with the lend unfolded
meets every conjunct of `RunFrame` at the nil index, `↭`, and so `M.Upd` there.** -/
theorem at02_unfolded_end {M : SemWorld} (hS : SliceShape M) (A : Alloc) (k : Nat) :
    RunFrame (ℍ := ℍ) M PMap.empty PMap.empty [] ([], M.nil) at02Body A k
      (ownRes (cellOf A k)) PMap.empty (ownRes (cellOf A k)) (ownRes (cellOf A k))
      (ownRes (cellOf A k)) (at02Stop (cellOf A k)) emptyHeap (stopHeap (cellOf A k)) []
      ([], M.nil) ∧
    ResU.UpdV (PMap.empty : WRes) (ownRes (cellOf A k)) ∧
    M.Upd ([], M.nil) ([], M.nil) PMap.empty (ownRes (cellOf A k)) (ownRes (cellOf A k)) ∧
    ¬ HeldAt (ownRes (cellOf A k)) (cellOf A k) := by
  have hv : ResU.Valid (ownRes (cellOf A k)) := ResU.valid_single_own _ _
  refine ⟨⟨ResU.hash_empty_right hv, compS_empty_left _,
      ResU.hash_symm (ResU.hash_empty_right hv), lower_empty, ResU.comp_empty_right _,
      lower_compS_own (compS_empty_left _) lower_empty rfl,
      ⟨_, at02Body_run A k⟩, ResU.comp_empty_right _, noOwn_empty,
      (hS.2.1 _ _ _).mpr ⟨TW.alloc TW.empty lower_empty rfl (compS_empty_left _) hv,
        fun _ hx => absurd hx (by simp)⟩,
      (hS.2.2.2.1 _ _ _ _ _).mpr ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩⟩,
    updV_empty_single_own _ _, (hS.2.2.2.2.1 _ _ _ _ _).mpr (updV_empty_single_own _ _), ?_⟩
  rintro ⟨_, _, _, _, _, _, hf⟩
  exact CellU.kind_mutOf_ne_own (flatAt_single_own hf)

/-- `at02_held_end` at Core's world: the end meets `coreW.Fam` and R-T1, and fails `↭`. -/
theorem at02_held_end_core (A : Alloc) (k : Nat) (α : Life) :
    (coreW (ℍ := ℍ)).Fam (PMap.empty : WRes) [] ([], ()) ∧
    RunFrame (ℍ := ℍ) (coreW (ℍ := ℍ)) PMap.empty PMap.empty [] ([], ()) at02Body A k
      (heldRes (cellOf A k) α) PMap.empty (heldRes (cellOf A k) α) (heldRes (cellOf A k) α)
      (heldRes (cellOf A k) α) (at02Stop (cellOf A k)) emptyHeap (stopHeap (cellOf A k)) []
      ([], ()) ∧
    HeldAt (heldRes (cellOf A k) α) (cellOf A k) ∧
    ¬ ResU.UpdV (PMap.empty : WRes) (heldRes (cellOf A k) α) ∧
    ¬ (coreW (ℍ := ℍ)).Upd ([], ()) ([], ()) PMap.empty (heldRes (cellOf A k) α)
      (heldRes (cellOf A k) α) :=
  at02_held_end sliceShape_core A k α

/-! ### The pin -/

/-- **A sanity check on the pin, read through its `→` half**: a run-end relation that relates
everything does not meet it. -/
theorem not_sliceShape_of_updTop {M : SemWorld} (h : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π) :
    ¬ SliceShape M := fun hS =>
  not_updV_empty_of_held ⟨_, _, _, _, _, _, mutCell_flatAt 0 Life.top .unit⟩
    ((hS.2.2.2.2.1 [] [] PMap.empty PMap.empty (mutCell 0 Life.top .unit)).mp (h _ _ _ _ _))

/-- **A reclaim law that reads only `↭`'s two resources excludes AT02's held end** at every end
index it is stated at. -/
theorem upd2Reclaim_excludes_held {M : SemWorld}
    (R : Idx M.Stk → Idx M.Stk → WRes → WRes → Prop) (i' : Idx M.Stk)
    (h : ∀ π, R ([], M.nil) i' PMap.empty π → NoOwn π → π = PMap.empty)
    (c : Loc) (α : Life) : ¬ R ([], M.nil) i' PMap.empty (heldRes c α) := fun hR => by
  have he := h _ hR (noOwn_mutCell _ _ _)
  have hg : (heldRes c α).get c = none := by rw [he]; rfl
  simp [heldRes, mutCell, ResU.single_get_self] at hg

/-! ### A reachable leak breaks adequacy -/

/-- From every configuration `M.Fam` reaches at σ = [], a fresh cell left behind as a `mut` cell
ends a run at a value, at some end index. -/
def LeakAt (M : SemWorld) (α : Life) : Prop :=
  ∀ (ρf fρ'p : WRes) (ps : List FrameRec) (c : Loc) (v : Val),
    M.Fam ρf ps ([], M.nil) → ResU.CompS ρf (mutCell c α v) fρ'p → ResU.Valid fρ'p →
    ∃ i', M.Upd ([], M.nil) i' PMap.empty PMap.empty (mutCell c α v) ∧ M.Fam fρ'p ps i' ∧
      M.Stop (ps, ([], M.nil)) (ps, i') (.val .unit)

/-- Allocate a cell and return `()` with the cell still allocated. -/
def leakProg : Expr := bindE (.app alloc' (.inj₁ unit')) unit'

theorem leakProg_step₁ (A : Alloc) (k : Nat) (μ : Heap) (hμ : μ (A.pick k μ 1) = none) :
    AStep1 (ℍ := ℍ) A k μ leakProg (k + 1) (BoCa.BoLo.Heap.upd μ (A.pick k μ 1) (Val.inj₁ .unit))
      (.app (.val (Val.lam unit')) (.val (.loc (A.pick k μ 1)))) :=
  ⟨.appR (.val (Val.lam unit')) .hole, _, _, rfl, rfl, AHead.alloc k μ (Val.inj₁ .unit) hμ⟩

theorem leakProg_step₂ (A : Alloc) (k : Nat) (μ : Heap) (c : Loc) :
    AStep1 (ℍ := ℍ) A k μ (.app (.val (Val.lam unit')) (.val (.loc c))) k μ (.val .unit) :=
  ⟨.hole, _, _, rfl, rfl, .det (Head.beta _ _ (Val.loc _)) rfl⟩

/-- `leakProg` runs to `()` with the cell still allocated. -/
theorem leakProg_run (A : Alloc) (k : Nat) (μ : Heap) (hμ : μ (A.pick k μ 1) = none) :
    ARun (ℍ := ℍ) A k μ leakProg (k + 1)
      (BoCa.BoLo.Heap.upd μ (A.pick k μ 1) (Val.inj₁ .unit)) (.val .unit) :=
  .more (leakProg_step₁ A k μ hμ) (.more (leakProg_step₂ A (k + 1) _ _) (.refl _ _ _))

/-- A value takes no platform step. -/
theorem no_pstep_val {P : Platform} {μ : Heap} {w : Val} {s : P.St} {c' : Conf P} :
    ¬ PStep (ℍ := ℍ) P ⟨μ, .val w, s⟩ c' := by
  intro h
  generalize hc : (⟨μ, .val w, s⟩ : Conf P) = c at h
  cases h with
  | mach h => cases hc; exact BoCa.BoLo.no_step_val h
  | plat _ _ _ => exact plug_perform_ne_val _ _ _ (congrArg Conf.e hc).symm

/-- **A reachable leak breaks adequacy at the platform with no operation**, at every world whose
relation at `F_S A` is its runs and whose data values hold nothing.  The start configuration's
validity, the cell's freshness and the end's lowering come from the start's `#` (`lower_of_hash`,
`Alloc.fresh`, `hash_compS_own`, 6.24, 6.25 under a frame), so no pin of the nil slice is read. -/
theorem not_adequateRetAt_of_leak {M : SemWorld} {α : Life} (hE : EffInterp (ℍ := ℍ) M)
    (hD : DataVals M) (hL : LeakAt M α) : ¬ AdequateRetAt (ℍ := ℍ) M Platform.none := by
  intro hA
  have hcomp : M.comp (CTy.effOf [] .unit) ([], M.nil) LSub.empty leakProg PMap.empty := by
    refine (hE [] .unit ([], M.nil) LSub.empty leakProg PMap.empty
      (fun _ _ _ h => by cases h)).mpr ?_
    intro P hP
    apply hP
    intro ρf fρ ps hf hc hFam A k
    obtain rfl : ρf = fρ := ResU.eq_of_comp_empty_right hc
    obtain ⟨μ, hμ⟩ := lower_of_hash hf hc
    have hμc : μ (A.pick k μ 1) = none := by
      simpa using A.fresh k μ 1 (lower_finDom hμ) 0 one_pos
    obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hc hμ hμc
      (compS_empty_left (ResU.single (A.pick k μ 1) (CellU.ownOf (Val.inj₁ .unit))))
    have hHm : ResU.Hash ρf (mutCell (A.pick k μ 1) α (Val.inj₁ .unit)) :=
      (ResU.six24 (compS_empty_left _)).mpr hfx
    obtain ⟨F, hF, hvF⟩ := hHm.2
    have hlowF : ResU.Lower F (BoCa.BoLo.Heap.upd μ (A.pick k μ 1) (Val.inj₁ .unit)) :=
      (ResU.lower_swap_mut_own (compS_empty_left _) (mutCell_valid _ _ _)
        (ResU.valid_single_own _ _) hF hHm hσ'x hfx).mpr hlow'
    obtain ⟨i', hU, hFam', hSt⟩ := hL ρf F ps (A.pick k μ 1) (Val.inj₁ .unit) hFam hF hvF
    exact ⟨PMap.empty, mutCell (A.pick k μ 1) α (Val.inj₁ .unit), ρf, F,
      mutCell (A.pick k μ 1) α (Val.inj₁ .unit), .val .unit, μ,
      BoCa.BoLo.Heap.upd μ (A.pick k μ 1) (Val.inj₁ .unit), ps, i',
      ResU.hash_symm (ResU.hash_empty_right (hash_valid hf).1), ResU.comp_empty_right _,
      ResU.hash_symm hHm, hμ, hF, hlowF, ⟨k + 1, leakProg_run A k μ hμc⟩, compS_empty_left _,
      hU, noOwn_mutCell _ _ _, hFam', hSt,
      Or.inl ⟨.unit, rfl, (hD true .unit i' LSub.empty .unit PMap.empty (VTy.DataB.unit 0)).mpr
        ⟨rfl, DataVal.unit⟩⟩⟩
  obtain ⟨hsafe, -⟩ := hA [] .unit leakProg (VTy.DataB.unit 0) (fun _ _ _ h => by cases h) hcomp
  -- under `Platform.none` the run stops at `()` with the cell still allocated
  have hμc : Adequacy.emptyMem (Alloc.leastFree.pick 0 Adequacy.emptyMem 1) = none := rfl
  have hsteps : PSteps (ℍ := ℍ) Platform.none (init Platform.none leakProg)
      ⟨BoCa.BoLo.Heap.upd Adequacy.emptyMem (Alloc.leastFree.pick 0 Adequacy.emptyMem 1)
        (Val.inj₁ .unit), .val .unit, ()⟩ :=
    Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single
        (PStep.mach (leakProg_step₁ (ℍ := ℍ) Alloc.leastFree 0 _ hμc).toStep1))
      (PStep.mach (leakProg_step₂ (ℍ := ℍ) Alloc.leastFree 1 _ _).toStep1)
  rcases hsafe _ hsteps with ⟨v, -, -, hmem⟩ | ⟨c', hc'⟩
  · have := congrFun hmem (Alloc.leastFree.pick 0 Adequacy.emptyMem 1)
    simp only [BoCa.BoLo.Heap.upd_same] at this
    cases this
  · exact no_pstep_val hc'

/-- **A reachable leak breaks adequacy** (FIX-RUN-END §3, Layer 3): `Adequate M` holds
`AdequateRetAt M Platform.none` (`platformNone_respects`). -/
theorem not_adequate_of_leak {M : SemWorld} {α : Life} (hE : EffInterp (ℍ := ℍ) M)
    (hD : DataVals M) (hL : LeakAt M α) : ¬ Adequate (ℍ := ℍ) M :=
  fun hA => not_adequateRetAt_of_leak hE hD hL (hA Platform.none platformNone_respects).1

/-- **A world whose run-end relation admits a reachable leak does not satisfy done**: `EndStateAt`
holds `WLaws` (so `EffInterp` and `DataVals`) and `Adequate`. -/
theorem not_endState_of_leak {J : TypingJ} {M : SemWorld} {Adm : OpAdm} {RF : RowForm} {α : Life}
    (hL : LeakAt M α) : ¬ EndStateAt (ℍ := ℍ) J M Adm RF := by
  rintro ⟨-, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, hW, -, hA, -⟩⟩
  exact not_adequate_of_leak hW.2.2.2.1 hW.2.2.2.2.2.1 hL hA

/-! ### `leakW`: a world that meets the pin, `EffInterp` and `DataVals`, and admits a leak -/

/-- `leakW` without its relation at computation types; `ewpW` does not read `comp`.  Its `Upd`
and `Stop` are true unless both ends are on the nil slice, and its `Fam` is true off it. -/
def leakW₀ : SemWorld where
  Stk := Bool
  nil := false
  held _ := ([], [])
  Fam fρ ps i := i.2 = false → TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1
  Stop a b _ := a.2.2 = false → b.2.2 = false →
    (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1)
  Upd i i' ρ _ π := i.2 = false → i'.2 = false → ResU.UpdV ρ π
  Ext i i' ρ := Ext i.1 i'.1 ρ
  share _ _ _ _ _ _ := fun _ => False
  payStk _ _ := false
  val b A i δ v := vCE none b A i.1 δ v
  comp _ _ _ _ := fun _ => False

/-- `leakW`: at `F_S R` the relation is its own runs. -/
def leakW : SemWorld :=
  { leakW₀ with
    comp := fun C i δ e ρ => ∀ (S : Row) (R : VTy), C = CTy.effOf S R →
      ewpW (ℍ := ℍ) leakW₀ i e (opTabW leakW₀ (rowTabW leakW₀ S δ))
        (fun j v => leakW₀.val true R j δ v) ρ }

/-- `CTy.effOf` is injective. -/
theorem effOf_inj : ∀ {S S' : Row} {R R' : VTy}, CTy.effOf S R = CTy.effOf S' R' → S = S' ∧ R = R'
  | [], [], _, _, h => by simp [CTy.effOf] at h; exact ⟨rfl, h⟩
  | [], _ :: _, _, _, h => by simp [CTy.effOf] at h
  | _ :: _, [], _, _, h => by simp [CTy.effOf] at h
  | o :: S, o' :: S', R, R', h => by
      simp only [CTy.effOf, CTy.eff.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      obtain ⟨rfl, rfl⟩ := effOf_inj h6
      cases o; cases o'
      simp_all

theorem sliceShape_leakW : SliceShape (leakW (ℍ := ℍ)) :=
  ⟨fun _ => rfl,
   fun _ _ _ => ⟨fun h => h rfl, fun h _ => h⟩,
   fun _ _ _ => Iff.rfl,
   fun _ _ _ _ _ => ⟨fun h => h rfl rfl, fun h _ _ => h⟩,
   fun _ _ _ _ _ => ⟨fun h => h rfl rfl, fun h _ _ => h⟩,
   fun _ => rfl⟩

theorem effInterp_leakW : EffInterp (ℍ := ℍ) (leakW (ℍ := ℍ)) := by
  intro S R i δ e ρ _
  constructor
  · intro h; exact h S R rfl
  · intro h S' R' hC
    obtain ⟨rfl, rfl⟩ := effOf_inj hC
    exact h

theorem dataVals_leakW : DataVals (leakW (ℍ := ℍ)) :=
  fun _ _ _ _ _ _ hA => vC_data hA

/-- `leakW` leaves the cell at the end index `([], true)`. -/
theorem leakAt_leakW (α : Life) : LeakAt (leakW (ℍ := ℍ)) α :=
  fun _ _ _ _ _ _ _ _ => ⟨([], true), fun _ h => Bool.noConfusion h, fun h => Bool.noConfusion h,
    fun _ h => Bool.noConfusion h⟩

/-- **`leakW` fails adequacy.** -/
theorem not_adequate_leakW (α : Life) : ¬ Adequate (ℍ := ℍ) (leakW (ℍ := ℍ)) :=
  not_adequate_of_leak effInterp_leakW dataVals_leakW (leakAt_leakW α)

/-- **`leakW` fails `UpdReclaim`.** -/
theorem not_updReclaim_leakW : ¬ UpdReclaim (leakW (ℍ := ℍ)) := by
  intro h
  have := h ([], true) (mutCell 0 Life.top .unit) (fun _ h => Bool.noConfusion h)
    (noOwn_mutCell _ _ _)
  have hg : (mutCell 0 Life.top .unit).get 0 = none := by rw [this]; rfl
  simp [mutCell, ResU.single_get_self] at hg

/-! ### `carryW`: OQ-9 (a) with the lend's cell kept, as a witness for the run-end laws -/

/-- The cells a world carries open across stops are `mut` cells. -/
def MutOnly (σ : WRes) : Prop := ∀ l ψ, σ.get l = some ψ → ψ.kind = Kind.mut

/-- A carried cell of `ρ` is the stack's: at a location of `σ`, `ρ` holds `σ`'s cell or none. -/
def CarriedIn (σ ρ : WRes) : Prop :=
  ∀ l ψ, (σ.get l).isSome → ρ.get l = some ψ → σ.get l = some ψ

/-- **(a) with the lend's cell kept**, as a witness for the run-end laws.  Its stack is the `mut`
cells carried open; its run-end relation is Core's `↭` once the carried cells are taken out at
both ends (`ResU.delDom`, the restriction `ρ/dom(σ)` [TR] 6.56 uses). -/
def carryW : SemWorld where
  Stk := WRes
  nil := PMap.empty
  held _ := ([], [])
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1 ∧ MutOnly i.2 ∧ ∃ x, ResU.CompS i.2 x fρ
  Stop a b _ := (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1)
  Upd i i' ρ ρ' π := MutOnly i.2 ∧ MutOnly i'.2 ∧ CarriedIn i.2 ρ ∧ CarriedIn i'.2 π ∧
    (∃ x, ResU.CompS (π.restrictDom i'.2) x ρ') ∧
    (∀ l ψ, i'.2.get l = some ψ → (i.2.get l = none ∨ (ρ.get l).isSome) → π.get l = some ψ) ∧
    (∀ l ψ, i.2.get l = some ψ → ρ.get l = none → π.get l = none ∧ i'.2.get l = some ψ) ∧
    ResU.UpdV (ρ.delDom i.2) (π.delDom i'.2)
  Ext i i' ρ := Ext i.1 i'.1 ρ ∧ i'.2 = i.2
  share _ _ _ _ _ _ := fun _ => False
  payStk _ _ := PMap.empty
  val b A i δ v := vCE none b A i.1 δ v
  comp C i δ e := cC (ℍ := ℍ) C i.1 δ e

theorem delDom_empty (ρ : WRes) : ρ.delDom PMap.empty = ρ :=
  PMap.ext fun _ => rfl

theorem restrictDom_empty (ρ : WRes) : ρ.restrictDom PMap.empty = PMap.empty :=
  PMap.ext fun _ => rfl

theorem empty_get_ne {l : Loc} {ψ : CellU Loc Val} : ¬ (PMap.empty : WRes).get l = some ψ :=
  fun h => by cases h

theorem empty_isSome {l : Loc} : ¬ ((PMap.empty : WRes).get l).isSome = true :=
  fun h => by cases h

/-- At σ = σ′ = `∅` the carried conjuncts are trivial and `ρ/dom(∅) = ρ`. -/
theorem sliceShape_carryW : SliceShape (carryW (ℍ := ℍ)) := by
  refine ⟨fun _ => rfl, fun fρ ps ls => ?_, fun _ _ _ => ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩,
    fun _ _ _ _ _ => Iff.rfl, fun ls ls' ρ ρ' π => ?_, fun _ => rfl⟩
  · exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun _ _ hg => absurd hg empty_get_ne,
      fρ, compS_empty_left fρ⟩⟩
  · show (MutOnly PMap.empty ∧ MutOnly PMap.empty ∧ CarriedIn PMap.empty ρ ∧
      CarriedIn PMap.empty π ∧ (∃ x, ResU.CompS (π.restrictDom PMap.empty) x ρ') ∧ _ ∧ _ ∧
      ResU.UpdV (ρ.delDom PMap.empty) (π.delDom PMap.empty)) ↔ ResU.UpdV ρ π
    rw [delDom_empty, delDom_empty, restrictDom_empty]
    constructor
    · exact fun h => h.2.2.2.2.2.2.2
    · intro h
      exact ⟨fun _ _ hg => absurd hg empty_get_ne, fun _ _ hg => absurd hg empty_get_ne,
        fun _ _ hs => absurd hs empty_isSome, fun _ _ hs => absurd hs empty_isSome,
        ⟨ρ', compS_empty_left ρ'⟩, fun _ _ hg => absurd hg empty_get_ne,
        fun _ _ hg => absurd hg empty_get_ne, h⟩

/-- A post of `∅` forces the end stack to be `∅`, and Core's `reclaim` applies. -/
theorem updReclaim_carryW : UpdReclaim (carryW (ℍ := ℍ)) := by
  rintro ⟨ls', σ'⟩ π ⟨-, -, -, -, ⟨x, hx⟩, hopen, -, hu⟩ hno
  have hr : ∀ l, (π.restrictDom σ').get l = none := fun l =>
    ((ResU.Comp.eq_none_iff hx l).mp rfl).1
  have hσ' : ∀ l, σ'.get l = none := by
    intro l
    cases e : σ'.get l with
    | none => rfl
    | some ψ =>
        have hπ := hopen l ψ e (Or.inl rfl)
        have := hr l
        rw [ResU.restrictDom_get_of_some e, hπ] at this
        cases this
  have hd : π.delDom σ' = π := PMap.ext fun l => ResU.delDom_get_of_none (hσ' l)
  have he : ResU.delDom (PMap.empty : WRes) PMap.empty = PMap.empty := delDom_empty _
  change ResU.UpdV (ResU.delDom (PMap.empty : WRes) PMap.empty) (π.delDom σ') at hu
  rw [hd, he] at hu
  exact reclaim π hu hno

/-- The held lend is a `mut` cell. -/
theorem mutOnly_heldRes (c : Loc) (α : Life) : MutOnly (heldRes c α) := by
  intro l ψ hl
  by_cases e : l = c
  · subst e
    simp only [heldRes, mutCell, ResU.single_get_self] at hl
    cases Option.some.inj hl
    exact CellU.kind_mutOf _ _ _ _ _ _
  · simp only [heldRes, mutCell] at hl
    rw [ResU.single_get_ne _ e] at hl; cases hl

/-- AT02's held end at `carryW`: from `∅` at the empty stack to the stack holding the cell, the
post holding it, no garbage. -/
theorem upd_held_carryW (c : Loc) (α : Life) :
    (carryW (ℍ := ℍ)).Upd ([], PMap.empty) ([], heldRes c α) PMap.empty
      (heldRes c α) (heldRes c α) := by
  have hmut : MutOnly (heldRes c α) := mutOnly_heldRes c α
  have hrd : (heldRes c α).restrictDom (heldRes c α) = heldRes c α :=
    PMap.ext fun l => by
      cases e : (heldRes c α).get l with
      | none => rw [ResU.restrictDom_get_of_none e]
      | some ψ => rw [ResU.restrictDom_get_of_some e, e]
  have hdd : (heldRes c α).delDom (heldRes c α) = PMap.empty :=
    PMap.ext fun l => by
      cases e : (heldRes c α).get l with
      | none => exact (ResU.delDom_get_of_none e).trans e
      | some ψ => exact ResU.delDom_get_of_some e
  refine ⟨fun _ _ hg => absurd hg empty_get_ne, hmut, fun _ _ hs => absurd hs empty_isSome,
    fun _ _ _ hg => hg, ⟨PMap.empty, by rw [hrd]; exact ResU.comp_empty_right _⟩,
    fun _ _ hg _ => hg, fun _ _ hg => absurd hg empty_get_ne, ?_⟩
  show ResU.UpdV (ResU.delDom (PMap.empty : WRes) PMap.empty)
    ((heldRes c α).delDom (heldRes c α))
  rw [hdd, delDom_empty]
  exact (ResU.updV_self_iff _).mpr ⟨_, BoCa.Fig16.BoLo.flat_empty⟩

/-- The `Upd` conjunct of the run that closes the lend and frees the cell: from the stack holding
it, its resource the cell, to the empty stack with nothing.  The machine run is not built. -/
theorem upd_close_carryW (c : Loc) (α : Life) :
    (carryW (ℍ := ℍ)).Upd ([], heldRes c α) ([], PMap.empty) (heldRes c α)
      PMap.empty PMap.empty := by
  have hmut : MutOnly (heldRes c α) := mutOnly_heldRes c α
  have hdd : (heldRes c α).delDom (heldRes c α) = PMap.empty :=
    PMap.ext fun l => by
      cases e : (heldRes c α).get l with
      | none => exact (ResU.delDom_get_of_none e).trans e
      | some ψ => exact ResU.delDom_get_of_some e
  refine ⟨hmut, fun _ _ hg => absurd hg empty_get_ne, fun _ _ _ hg => hg,
    fun _ _ hs => absurd hs empty_isSome,
    ⟨PMap.empty, by rw [restrictDom_empty]; exact compS_empty_left _⟩,
    fun _ _ hg => absurd hg empty_get_ne, fun l ψ hg hn => ?_, ?_⟩
  · rw [hg] at hn; cases hn
  · show ResU.UpdV ((heldRes c α).delDom (heldRes c α))
      (ResU.delDom (PMap.empty : WRes) PMap.empty)
    rw [hdd, delDom_empty]
    exact (ResU.updV_self_iff _).mpr ⟨_, BoCa.Fig16.BoLo.flat_empty⟩

/-- A non-`imm` cell of a component sits in the composite, and the other side has none there. -/
theorem compS_get_of_left_ne_imm {a b c : WRes} (h : ResU.CompS a b c) {l : Loc}
    {φ : CellU Loc Val} (e : a.get l = some φ) (hk : φ.kind ≠ Kind.imm) :
    c.get l = some φ ∧ b.get l = none := by
  rcases ResU.Comp.get h l with ⟨f, -, -⟩ | ⟨ψ, f₁, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, -, hC⟩
  · rw [e] at f; cases f
  · rw [e] at f₁; cases f₁; exact ⟨f, f₂⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases f₁
    obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, -, -⟩ := hC
    rw [e₁, CellU.kind_immOf] at hk
    exact absurd rfl hk

theorem mut_ne_imm {ψ : CellU Loc Val} (h : ψ.kind = Kind.mut) : ψ.kind ≠ Kind.imm := by
  rw [h]; exact fun e => Kind.noConfusion e

/-- At a configuration `carryW` reaches, the run's resource holds a carried cell as the stack's. -/
theorem carriedIn_of_fam {σ x ρf ρ fρ : WRes} (hm : MutOnly σ) (hx : ResU.CompS σ x fρ)
    (hc : ResU.CompS ρf ρ fρ) : CarriedIn σ ρ := by
  intro l ψ hs hρ
  obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨hf, -⟩ := compS_get_of_left_ne_imm hx hφ (mut_ne_imm (hm l φ hφ))
  rcases ResU.CompS.get_split_of_ne_imm hc hf (mut_ne_imm (hm l φ hφ)) with ⟨-, h₂⟩ | ⟨-, h₂⟩
  · rw [hρ] at h₂; cases h₂
  · rw [hρ] at h₂; rw [hφ, h₂]

/-- A run of no steps has its end at every configuration `carryW` reaches. -/
theorem updRefl_carryW : UpdRefl (carryW (ℍ := ℍ)) := by
  rintro ⟨ls, σ⟩ ρf ρ fρ ps hf hc ⟨-, -, hm, x, hx⟩
  have hci : CarriedIn σ ρ := carriedIn_of_fam hm hx hc
  have hv : ResU.Valid (ρ.delDom σ) :=
    (ResU.Valid.split (ResU.restrictDom_compS ρ σ) (hash_valid hf).2).2
  refine ⟨hm, hm, hci, hci, ⟨ρ.delDom σ, ResU.restrictDom_compS ρ σ⟩, fun l ψ hs h => ?_,
    fun l ψ hs hn => ⟨hn, hs⟩, (ResU.updV_self_iff _).mpr hv⟩
  rcases h with h | h
  · rw [hs] at h; cases h
  · obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h
    have := hci l φ (by rw [hs]; rfl) hφ
    rw [hs] at this
    rw [hφ, this]

/-- `/dom(σ)` distributes over `●`. -/
theorem compS_delDom {a b c : WRes} (σ : WRes) (h : ResU.CompS a b c) :
    ResU.CompS (a.delDom σ) (b.delDom σ) (c.delDom σ) := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · cases e : σ.get l with
    | some ζ => rw [ResU.delDom_get_of_some e] at e₁; cases e₁
    | none =>
        rw [ResU.delDom_get_of_none e] at e₁ e₂
        exact h.1 l ψ₁ ψ₂ e₁ e₂
  · cases e : σ.get l with
    | some ζ =>
        rw [ResU.delDom_get_of_some e, ResU.delDom_get_of_some e, ResU.delDom_get_of_some e]
        rfl
    | none =>
        rw [ResU.delDom_get_of_none e, ResU.delDom_get_of_none e, ResU.delDom_get_of_none e]
        exact h.2 l

/-- A resource with no cell at `dom(σ)` is its own `/dom(σ)`. -/
theorem delDom_of_disjoint {b σ : WRes} (h : ∀ l, (σ.get l).isSome → b.get l = none) :
    b.delDom σ = b :=
  PMap.ext fun l => by
    cases e : σ.get l with
    | some ζ => rw [ResU.delDom_get_of_some e, h l (by rw [e]; rfl)]
    | none => rw [ResU.delDom_get_of_none e]

/-- An own cell added to a configuration `carryW` reaches is never at a carried location. -/
theorem own_not_carried {σ x ρf ρ fρ ρ₁ : WRes} {l : Loc} {v : Val} (hm : MutOnly σ)
    (hx : ResU.CompS σ x fρ) (hc : ResU.CompS ρf ρ fρ)
    (ho : ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ₁) (hf₁ : ResU.Hash ρf ρ₁) :
    σ.get l = none := by
  cases hφ : σ.get l with
  | none => rfl
  | some φ =>
      exfalso
      have hk := mut_ne_imm (hm l φ hφ)
      obtain ⟨hf, -⟩ := compS_get_of_left_ne_imm hx hφ hk
      rcases ResU.CompS.get_split_of_ne_imm hc hf hk with ⟨h₁, h₂⟩ | ⟨-, h₂⟩
      · have hρ₁ : ρ₁.get l = some (CellU.ownOf v) := by
          rw [ResU.Comp.get_of_left_none ho h₂, ResU.single_get_self]
        exact hk (CellU.CompatS.kind_left (hf₁.1 l φ _ h₁ hρ₁))
      · obtain ⟨-, h⟩ := compS_get_of_left_ne_imm ho h₂ hk
        rw [ResU.single_get_self] at h; cases h

/-- An own cell added or removed is never at a carried location, and `/dom(σ)` passes it through,
so `updV_compS_own` applies. -/
theorem updOwn_carryW : UpdOwn (carryW (ℍ := ℍ)) := by
  constructor
  · rintro ⟨ls, σ⟩ ρf ρ fρ ρ₁ ps l v hf hc ⟨-, -, hm, x, hx⟩ ho hf₁
    have hl : σ.get l = none := own_not_carried hm hx hc ho hf₁
    have hci : CarriedIn σ ρ := carriedIn_of_fam hm hx hc
    have hsame : ∀ l', (σ.get l').isSome → ρ₁.get l' = ρ.get l' := by
      intro l' hs
      have hne : l' ≠ l := by rintro rfl; rw [hl] at hs; cases hs
      rw [ResU.Comp.get_of_right_none ho (ResU.single_get_ne _ hne)]
    have hci₁ : CarriedIn σ ρ₁ := fun l' ψ hs h => hci l' ψ hs (by rw [← hsame l' hs]; exact h)
    have hv₁ : ResU.Valid ρ₁ := (hash_valid hf₁).2
    have hv : ResU.Valid ρ := (hash_valid hf).2
    have hsd : (ResU.single l (CellU.ownOf v) : WRes).delDom σ = ResU.single l (CellU.ownOf v) :=
      delDom_of_disjoint (σ := σ) (fun l' hs => by
        have hne : l' ≠ l := by rintro rfl; rw [hl] at hs; cases hs
        exact ResU.single_get_ne _ hne)
    have hd : ResU.CompS (ρ.delDom σ) (ResU.single l (CellU.ownOf v)) (ρ₁.delDom σ) := by
      have := compS_delDom σ ho
      rwa [hsd] at this
    refine ⟨hm, hm, hci, hci₁, ⟨ρ₁.delDom σ, ResU.restrictDom_compS ρ₁ σ⟩,
      fun l' ψ hs h => ?_, fun l' ψ hs hn => ⟨?_, hs⟩,
      updV_compS_own hd (ResU.Valid.split (ResU.restrictDom_compS ρ σ) hv).2
        (ResU.Valid.split (ResU.restrictDom_compS ρ₁ σ) hv₁).2⟩
    · rcases h with h | h
      · rw [hs] at h; cases h
      · obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h
        have := hci l' φ (by rw [hs]; rfl) hφ
        rw [hs] at this
        rw [hsame l' (by rw [hs]; rfl), hφ, this]
    · rw [hsame l' (by rw [hs]; rfl)]; exact hn
  · rintro ⟨ls, σ⟩ ρf ρ ρ₁ fρ₁ ps l v hf₁ hc₁ ⟨-, -, hm, x, hx⟩ ho
    have hci₁ : CarriedIn σ ρ₁ := carriedIn_of_fam hm hx hc₁
    -- `ℓ` is not carried: `ρ₁` holds `own` there, and the stack's cell would be `ρ₁`'s
    have hρ₁l : ρ₁.get l = some (CellU.ownOf v) :=
      (compS_get_of_left_ne_imm (ResU.CompS.comm ho) (ResU.single_get_self _ _)
        (by rw [CellU.kind_ownOf]; exact fun e => Kind.noConfusion e)).1
    have hl : σ.get l = none := by
      cases e : σ.get l with
      | none => rfl
      | some φ =>
          have := hci₁ l _ (by rw [e]; rfl) hρ₁l
          have h' : φ = CellU.ownOf v := Option.some.inj (e.symm.trans this)
          have hk := hm l φ e
          rw [h', CellU.kind_ownOf] at hk
          cases hk
    have hsame : ∀ l', (σ.get l').isSome → ρ₁.get l' = ρ.get l' := by
      intro l' hs
      have hne : l' ≠ l := by rintro rfl; rw [hl] at hs; cases hs
      rw [ResU.Comp.get_of_right_none ho (ResU.single_get_ne _ hne)]
    have hci : CarriedIn σ ρ := fun l' ψ hs h => hci₁ l' ψ hs (by rw [hsame l' hs]; exact h)
    have hv₁ : ResU.Valid ρ₁ := (hash_valid hf₁).2
    have hv : ResU.Valid ρ := (ResU.Valid.split ho hv₁).1
    have hsd : (ResU.single l (CellU.ownOf v) : WRes).delDom σ = ResU.single l (CellU.ownOf v) :=
      delDom_of_disjoint (σ := σ) (fun l' hs => by
        have hne : l' ≠ l := by rintro rfl; rw [hl] at hs; cases hs
        exact ResU.single_get_ne _ hne)
    have hd : ResU.CompS (ρ.delDom σ) (ResU.single l (CellU.ownOf v)) (ρ₁.delDom σ) := by
      have := compS_delDom σ ho
      rwa [hsd] at this
    refine ⟨hm, hm, hci₁, hci, ⟨ρ.delDom σ, ResU.restrictDom_compS ρ σ⟩,
      fun l' ψ hs h => ?_, fun l' ψ hs hn => ⟨?_, hs⟩,
      (updV_compS_own hd (ResU.Valid.split (ResU.restrictDom_compS ρ σ) hv).2
        (ResU.Valid.split (ResU.restrictDom_compS ρ₁ σ) hv₁).2).symm⟩
    · rcases h with h | h
      · rw [hs] at h; cases h
      · obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp h
        have := hci₁ l' φ (by rw [hs]; rfl) hφ
        rw [hs] at this
        rw [← hsame l' (by rw [hs]; rfl), hφ, this]
    · rw [← hsame l' (by rw [hs]; rfl)]; exact hn

/-- Run 1's garbage holds no cell at a location of `σ₁` or `σ₂`, and at `σ₂`'s locations the
composite end is run 2's.  Then, as `wpG_bind`'s last step does, 6.48 frames run 2 by `ρ⁺₁` and
6.49 composes, after `/dom(σ₁)` and `/dom(σ₂)`. -/
theorem updSeq_carryW : UpdSeq (carryW (ℍ := ℍ)) := by
  rintro ⟨ls, σ⟩ ⟨ls₁, σ₁⟩ ⟨ls₂, σ₂⟩ ρ ρ'₁ ρp₁ π₁ ρ'₂ π₂ π
    ⟨hm, hm₁, hci, hci₁, ⟨x₁, hx₁⟩, hok₁, hna₁, hu₁⟩ hc₁
    ⟨-, hm₂, -, hci₂, ⟨x₂, hx₂⟩, hok₂, hna₂, hu₂⟩ hH hc
  -- (F1) run 1's garbage holds no cell at a location of `σ₁`
  have hF1 : ∀ l, (σ₁.get l).isSome → ρp₁.get l = none := by
    intro l hs
    cases ep : ρp₁.get l with
    | none => rfl
    | some φ =>
        exfalso
        obtain ⟨ψ, hψ⟩ : ∃ ψ, π₁.get l = some ψ := by
          rcases ResU.Comp.get hc₁ l with ⟨-, f, -⟩ | ⟨-, -, f, -⟩ | ⟨ψ, -, -, f⟩ |
              ⟨-, -, ψ, -, -, f, -⟩
          · rw [ep] at f; cases f
          · rw [ep] at f; cases f
          · exact ⟨ψ, f⟩
          · exact ⟨ψ, f⟩
        have hσψ := hci₁ l ψ hs hψ
        have hk := mut_ne_imm (hm₁ l ψ hσψ)
        have hr : (π₁.restrictDom σ₁).get l = some ψ := by
          rw [ResU.restrictDom_get_of_some hσψ, hψ]
        obtain ⟨hρ', -⟩ := compS_get_of_left_ne_imm hx₁ hr hk
        rcases ResU.CompS.get_split_of_ne_imm hc₁ hψ hk with ⟨-, h⟩ | ⟨h, -⟩
        · rw [ep] at h; cases h
        · rw [hρ'] at h; cases h
  -- (F2) nor at a location of `σ₂`
  have hF2 : ∀ l, (σ₂.get l).isSome → ρp₁.get l = none := by
    intro l hs
    cases e₁ : σ₁.get l with
    | some _ => exact hF1 l (by rw [e₁]; rfl)
    | none =>
        obtain ⟨ψ₂, hψ₂⟩ := Option.isSome_iff_exists.mp hs
        have hπ₂ := hok₂ l ψ₂ hψ₂ (Or.inl e₁)
        cases ep : ρp₁.get l with
        | none => rfl
        | some φ =>
            exfalso
            have hk := (CellU.CompatS.kinds (hH.1 l φ ψ₂ ep hπ₂)).2
            rw [hm₂ l ψ₂ hψ₂] at hk; cases hk
  -- (F3) at a location of `σ₂`, the composite end is run 2's
  have hF3 : ∀ l, (σ₂.get l).isSome → π.get l = π₂.get l := fun l hs =>
    ResU.Comp.get_of_left_none hc (hF2 l hs)
  have hrd : π.restrictDom σ₂ = π₂.restrictDom σ₂ := PMap.ext fun l => by
    cases e : σ₂.get l with
    | none => rw [ResU.restrictDom_get_of_none e, ResU.restrictDom_get_of_none e]
    | some ζ => rw [ResU.restrictDom_get_of_some e, ResU.restrictDom_get_of_some e,
        hF3 l (by rw [e]; rfl)]
  refine ⟨hm, hm₂, hci, fun l ψ hs h => hci₂ l ψ hs (by rw [← hF3 l hs]; exact h),
    ⟨x₂, by rw [hrd]; exact hx₂⟩, fun l ψ hs hpre => ?_, fun l ψ hs hn => ?_, ?_⟩
  · -- a lend opened, or a carried cell held, sits in the end at the end stack's cell
    rw [hF3 l (by rw [hs]; rfl)]
    cases e₁ : σ₁.get l with
    | none => exact hok₂ l ψ hs (Or.inl e₁)
    | some ψ₁ =>
        have hπ₁ := hok₁ l ψ₁ e₁ hpre
        have hr : (π₁.restrictDom σ₁).get l = some ψ₁ := by
          rw [ResU.restrictDom_get_of_some e₁, hπ₁]
        obtain ⟨hρ', -⟩ := compS_get_of_left_ne_imm hx₁ hr (mut_ne_imm (hm₁ l ψ₁ e₁))
        exact hok₂ l ψ hs (Or.inr (by rw [hρ']; rfl))
  · -- a carried cell not held is not held at the end, and stays carried unchanged
    obtain ⟨hπ₁, hσ₁⟩ := hna₁ l ψ hs hn
    have hρ'₁ : ρ'₁.get l = none := ((ResU.Comp.eq_none_iff hc₁ l).mp hπ₁).1
    have hp₁ : ρp₁.get l = none := ((ResU.Comp.eq_none_iff hc₁ l).mp hπ₁).2
    obtain ⟨hπ₂, hσ₂⟩ := hna₂ l ψ hσ₁ hρ'₁
    exact ⟨(ResU.Comp.eq_none_iff hc l).mpr ⟨hp₁, hπ₂⟩, hσ₂⟩
  · -- 6.48 then 6.49, after the carried cells are taken out at both ends
    have hd₁ : ResU.CompS ρp₁ (ρ'₁.delDom σ₁) (π₁.delDom σ₁) := by
      have := compS_delDom σ₁ hc₁
      rw [delDom_of_disjoint hF1] at this
      exact ResU.CompS.comm this
    have hd₂ : ResU.CompS ρp₁ (π₂.delDom σ₂) (π.delDom σ₂) := by
      have := compS_delDom σ₂ hc
      rwa [delDom_of_disjoint hF2] at this
    have hvπ : ResU.Valid π := by
      obtain ⟨w, hw, hvw⟩ := hH.2
      rwa [ResU.CompS.functional hw hc] at hvw
    have hv₂ : ResU.Valid (π.delDom σ₂) :=
      (ResU.Valid.split (ResU.restrictDom_compS π σ₂) hvπ).2
    exact ResU.UpdV.trans hu₁
      (updV_frame hd₁ hd₂ ⟨hd₁.1, _, hd₁, hu₁.2.2⟩ ⟨hd₂.1, _, hd₂, hv₂⟩ hu₂)

/-- **AT02's end at `Foo` holding the lend, at `carryW`**: from the empty configuration, which
`carryW` reaches at the nil index, the end holding `c ↦ mut(α, inj₁ (), ∅, ⊤)` as the post meets
every conjunct of `RunFrame` and `carryW.Upd` at the index whose stack is the lend. -/
theorem at02_held_end_carry (A : Alloc) (k : Nat) (α : Life) :
    (carryW (ℍ := ℍ)).Fam PMap.empty [] ([], PMap.empty) ∧
    RunFrame (ℍ := ℍ) (carryW (ℍ := ℍ)) PMap.empty PMap.empty [] ([], PMap.empty) at02Body A k
      (heldRes (cellOf A k) α) PMap.empty (heldRes (cellOf A k) α) (heldRes (cellOf A k) α)
      (heldRes (cellOf A k) α) (at02Stop (cellOf A k)) emptyHeap (stopHeap (cellOf A k)) []
      ([], heldRes (cellOf A k) α) ∧
    (carryW (ℍ := ℍ)).Upd ([], PMap.empty) ([], heldRes (cellOf A k) α) PMap.empty
      (heldRes (cellOf A k) α) (heldRes (cellOf A k) α) := by
  have hv : ResU.Valid (heldRes (cellOf A k) α) := mutCell_valid _ α _
  refine ⟨⟨TW.empty, fun _ hx => absurd hx (by simp), fun _ _ hg => absurd hg empty_get_ne,
      PMap.empty, compS_empty_left _⟩,
    ⟨ResU.hash_empty_right hv, compS_empty_left _, ResU.hash_symm (ResU.hash_empty_right hv),
      lower_empty, ResU.comp_empty_right _, ?_, ⟨_, at02Body_run A k⟩, ResU.comp_empty_right _,
      noOwn_empty, ⟨held_arises _ α, fun _ hx => absurd hx (by simp), mutOnly_heldRes _ α,
        PMap.empty, ResU.comp_empty_right _⟩, fun _ => Iff.rfl, fun _ => Iff.rfl⟩,
    upd_held_carryW _ α⟩
  exact (ResU.six25 (compS_empty_left _) hv (ResU.valid_single_own _ _)).mpr
    (lower_compS_own (compS_empty_left _) lower_empty rfl)

/-- The held lend, at its location. -/
theorem heldRes_get (c : Loc) (α : Life) :
    (heldRes c α).get c = some (CellU.mutOf α (Val.inj₁ .unit) PMap.empty
      (ResU.inStratum_empty α) (trueP α) trivial) := ResU.single_get_self _ _

/-- At `carryW`, a configuration holding the lend is reached at the empty stack too: `TW` records
no 6.65 lend. -/
theorem fam_nil_held_carryW (c : Loc) (α : Life) :
    (carryW (ℍ := ℍ)).Fam (heldRes c α) [] ([], PMap.empty) :=
  ⟨held_arises c α, fun _ hx => absurd hx (by simp), fun _ _ hg => absurd hg empty_get_ne,
    heldRes c α, compS_empty_left _⟩

/-- **At `carryW`, a run from the empty stack whose resource holds the lend cannot close it, at
any end index**: with nothing carried at the start, the relation is `↭` from the lend, which
forbids ending it. -/
theorem not_close_from_nil_carryW (c : Loc) (α : Life) (i' : Idx WRes) (ρ' : WRes) :
    ¬ (carryW (ℍ := ℍ)).Upd ([], PMap.empty) i' (heldRes c α) ρ' PMap.empty := by
  rintro ⟨-, -, -, -, -, -, -, hu⟩
  have h0 : ResU.delDom (PMap.empty : WRes) i'.2 = PMap.empty := PMap.ext fun l => by
    cases e : i'.2.get l with
    | none => exact ResU.delDom_get_of_none e
    | some ψ => exact ResU.delDom_get_of_some e
  change ResU.UpdV ((heldRes c α).delDom PMap.empty) (ResU.delDom (PMap.empty : WRes) i'.2) at hu
  rw [delDom_empty, h0] at hu
  exact not_updV_empty_of_held ⟨_, _, _, _, _, _, mutCell_flatAt c α _⟩ hu.symm

/-! ### Where the printed forms of 6.50 and 6.27 at every index exclude a carried lend -/

/-- **A world whose run-end relation lets a run from `∅` end with a lend at `α` at the top of `π`
fails 6.50 at W**: `∅` outlives `α`, and the lend does not. -/
theorem not_updOutlives_of_opened {M : SemWorld} {i i' : Idx M.Stk} {c : Loc} {α : Life}
    {v : Val} {χ : WRes} {h : χ.InStratum α} {P : Val → SPropS Loc Val α} {hw : P v ⟨χ, h⟩}
    {ρ' π : WRes} (hπ : π.get c = some (CellU.mutOf α v χ h P hw))
    (hu : M.Upd i i' PMap.empty ρ' π) : ¬ UpdOutlives M := by
  intro hO
  have hc := hO i i' _ _ _ α (ResU.inStratum_empty _) hu c _ hπ
  rw [CellU.inStratum_mutOf] at hc
  exact lt_irrefl _ hc

/-- **A world whose run-end relation lets a run that starts with a lend at the top, beside a
resource that outlives it, end with no cell at the lend's location fails 6.27 at W.** -/
theorem not_updMutBack_of_closed {M : SemWorld} {i i' : Idx M.Stk} {c : Loc} {α : Life}
    {v : Val} {χ : WRes} {h : χ.InStratum α} {P : Val → SPropS Loc Val α} {hw : P v ⟨χ, h⟩}
    {ρb BM ρ' π : WRes} (hout : BoLo.Outlives ρb α)
    (hBM : ResU.CompS ρb (ResU.single c (CellU.mutOf α v χ h P hw)) BM)
    (hu : M.Upd i i' BM ρ' π) (hπ : π.get c = none) : ¬ UpdMutBack M := by
  intro hB
  obtain ⟨v', χ', h', hw', hsplit, -⟩ := hB i i' c α v χ ρb BM ρ' π h P hw hout hBM hu
  rw [ResU.compS_single_get_self (ResU.CompS.comm hsplit) (ResU.del_get_self _ _)] at hπ
  cases hπ

/-- `carryW` admits the held end's run (`upd_held_carryW`), so it fails 6.50 at W. -/
theorem not_updOutlives_carryW : ¬ UpdOutlives (carryW (ℍ := ℍ)) :=
  not_updOutlives_of_opened (heldRes_get 0 Life.top) (upd_held_carryW 0 Life.top)

/-- `carryW` admits the closing run (`upd_close_carryW`), so it fails 6.27 at W. -/
theorem not_updLendBack_carryW : ¬ UpdLendBack (carryW (ℍ := ℍ)) :=
  fun h => not_updMutBack_of_closed (ResU.inStratum_empty _) (compS_empty_left _)
    (upd_close_carryW 0 Life.top) rfl h.1

/-! ### A 6.64 lend at AT02's stop -/

/-- The record [TR] 6.64 makes when it lends AT02's cell: the location, the value, an empty
payload, the type `Flag`. -/
def immRec (c : Loc) : FrameRec := ⟨c, Val.inj₁ .unit, PMap.empty, Flag, LSub.empty⟩

/-- 6.64's lend of AT02's cell at `α`: `c ↦ imm({α}, inj₁ (), ∅)`. -/
abbrev immRes (c : Loc) (α : Life) : WRes :=
  ResU.single c (CellU.immOf (LSet.singleton α) (Val.inj₁ .unit) PMap.empty
    (ResU.inStratum_empty _))

/-- An empty payload has no sub-record. -/
theorem immRec_noDesc (c : Loc) (d : FrameRec) : ¬ Desc (immRec c) d := by
  rintro ⟨p, hp, hpath⟩
  cases hpath with
  | nil => exact hp rfl
  | cons hs _ =>
      obtain ⟨-, -, ζ, hζ, -⟩ := hs
      simp [immRec] at hζ

theorem admWf_flag : AdmWf Flag LSub.empty := by
  intro x hx
  simp [VFree] at hx

theorem vShape_flag : vShape Flag LSub.empty (Val.inj₁ .unit) (PMap.empty : WRes) :=
  Or.inl ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

/-- 6.34: the lend is compatible with nothing, so valid. -/
theorem immRes_hash (c : Loc) (α : Life) : ResU.Hash (PMap.empty : WRes) (immRes c α) :=
  ResU.six34 (compS_empty_left _)
    (ResU.hash_symm (ResU.hash_empty_right (ResU.valid_single_own c _)))

theorem immRes_valid (c : Loc) (α : Life) : ResU.Valid (immRes c α) :=
  (hash_valid (immRes_hash c α)).2

theorem own_arises (c : Loc) : TW (ResU.single c (CellU.ownOf (Val.inj₁ .unit))) [] [] :=
  TW.alloc TW.empty lower_empty rfl (compS_empty_left _) (ResU.valid_single_own _ _)

/-- **It arises**: `TW.alloc` of the cell from `∅`, then `TW.immFrame` of the lend, which records
the frame in the visible frames and in the records. -/
theorem imm_arises (c : Loc) (α : Life) : TW (immRes c α) [immRec c] [immRec c] :=
  TW.immFrame (ds := []) Flag LSub.empty (ResU.inStratum_empty _) (own_arises c) admWf_flag
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) vShape_flag
    (ResU.comp_empty_right _) (immRes_valid c α)
    (fun d => ⟨fun h => absurd h List.not_mem_nil, fun h => absurd h (immRec_noDesc c d)⟩)

/-- The record is tagged with the frame's lifetime (`frameLife_frame`, 6.64's entry). -/
theorem imm_tagged (c : Loc) (α : Life) : Tagged (immRes c α) [immRec c] [(immRec c, α)] := by
  intro x hx
  simp only [List.mem_singleton] at hx
  subst hx
  refine ⟨immRec c, List.mem_singleton_self _, DescR.refl _, ?_⟩
  exact (frameLife_frame Flag LSub.empty (ResU.valid_single_own c _)
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (own_arises c).inv).1

/-- `⦇c ↦ imm({α}, inj₁ (), ∅)⦈` holds an `imm` cell at `c`. -/
theorem immAt_immRes (c : Loc) (α : Life) :
    ∃ (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
      (immRes c α).FlatAt c (CellU.immOf s v χ h) := by
  obtain ⟨σ, hσ⟩ := immRes_valid c α
  obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ (ResU.single_get_self _ _)
  obtain ⟨s, hs, e⟩ := CellU.imm_eta (hk.trans (CellU.kind_immOf _ _ _ _))
  exact ⟨s, χ.erase, χ.wit, hs, σ, hσ, hχ.trans (congrArg some e)⟩

/-- **`↭` from `∅` forbids the lend**: LoopBorrow's `not_upd_of_new_imm`. -/
theorem not_updV_empty_immRes (c : Loc) (α : Life) :
    ¬ ResU.UpdV (PMap.empty : WRes) (immRes c α) := by
  obtain ⟨s, v, χ, h, hf⟩ := immAt_immRes c α
  exact fun hu => not_upd_of_new_imm hf (not_flatAt_empty c _) hu.1

/-- **At every world whose nil slice is Core's, AT02's run ended at `Foo` with the cell lent by
6.64 and the frame open meets every other conjunct of `RunFrame` at the nil index, and fails R-T1,
`↭` and so `M.Upd`.**  The configuration, in `M.Fam` at the nil index, holds the frame in the
visible frames and the record in the index. -/
theorem at02_imm_end {M : SemWorld} (hS : SliceShape M) (A : Alloc) (k : Nat) (α : Life) :
    M.Fam (PMap.empty : WRes) [] ([], M.nil) ∧
    M.Fam (immRes (cellOf A k) α) [immRec (cellOf A k)] ([(immRec (cellOf A k), α)], M.nil) ∧
    (RunFrame (ℍ := ℍ) M PMap.empty PMap.empty [] ([], M.nil) at02Body A k
      (immRes (cellOf A k) α) PMap.empty (immRes (cellOf A k) α) (immRes (cellOf A k) α)
      (immRes (cellOf A k) α) (at02Stop (cellOf A k)) emptyHeap (stopHeap (cellOf A k))
      [immRec (cellOf A k)] ([(immRec (cellOf A k), α)], M.nil) ↔
     M.Stop ([], ([], M.nil)) ([immRec (cellOf A k)], ([(immRec (cellOf A k), α)], M.nil))
      (at02Stop (cellOf A k))) ∧
    ¬ M.Stop ([], ([], M.nil)) ([immRec (cellOf A k)], ([(immRec (cellOf A k), α)], M.nil))
      (at02Stop (cellOf A k)) ∧
    ¬ ResU.UpdV (PMap.empty : WRes) (immRes (cellOf A k) α) ∧
    ¬ M.Upd ([], M.nil) ([(immRec (cellOf A k), α)], M.nil) PMap.empty (immRes (cellOf A k) α)
      (immRes (cellOf A k) α) := by
  have hv : ResU.Valid (immRes (cellOf A k) α) := immRes_valid _ α
  have hFam : M.Fam (immRes (cellOf A k) α) [immRec (cellOf A k)]
      ([(immRec (cellOf A k), α)], M.nil) :=
    (hS.2.1 _ _ _).mpr ⟨imm_arises _ α, imm_tagged _ α⟩
  have hlow : ResU.Lower (immRes (cellOf A k) α) (stopHeap (cellOf A k)) :=
    (ResU.six26 (compS_empty_left _) hv (ResU.valid_single_own _ _)).mpr
      (lower_compS_own (compS_empty_left _) lower_empty rfl)
  have hnu := not_updV_empty_immRes (cellOf A k) α
  refine ⟨(hS.2.1 _ _ _).mpr ⟨TW.empty, fun _ hx => absurd hx (by simp)⟩, hFam,
    ⟨fun h => h.2.2.2.2.2.2.2.2.2.2, fun hst => ⟨ResU.hash_empty_right hv, compS_empty_left _,
      ResU.hash_symm (ResU.hash_empty_right hv), lower_empty, ResU.comp_empty_right _, hlow,
      ⟨_, at02Body_run A k⟩, ResU.comp_empty_right _, noOwn_empty, hFam, hst⟩⟩, ?_,
    hnu, fun hu => hnu ((hS.2.2.2.2.1 _ _ _ _ _).mp hu)⟩
  intro hst
  have := ((hS.2.2.2.1 _ _ _ _ _).mp hst).1 (immRec (cellOf A k))
  simp at this

/-- **`StopVisible` excludes the same visible frames at every index**: a run that starts with no
visible frame cannot end with 6.64's frame visible. -/
theorem not_stop_imm_of_stopVisible {M : SemWorld} (hV : StopVisible M) (c : Loc)
    (i i' : Idx M.Stk) (t : Expr) : ¬ M.Stop ([], i) ([immRec c], i') t := by
  intro hst
  have := (hV _ _ _ _ _ hst).1 (immRec c)
  simp at this

end Targets.RunEnd

end
