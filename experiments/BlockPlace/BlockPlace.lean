import Lowering.PrintSim

/-!
# BlockPlace — an array as one block, against the print's simulation  (#701, U2 of #698)

SPEC §56's simulation (`printSimAt_lirOf`) is proved for every closed effect-free term in the
relation at `F 1`. Its input is a run of the source: `arun_of_sem` gives one under `bumpAlloc`,
and `big_of_arun` reads it big-step (`BigN`), the premise of every `FwdOne`. Placing a `tab`'s
cells as one object of the LIR, freed once at its `drop` (Backend2's `newArr` and `freeArr`), asks
of that run that every `drop` frees a whole block.

The relation does not give it. The model admits splitting an owned family: `famSplit_compatX`
holds at every leaf, `Ref A` among them (`Core/SliceOps.lean`: "An owned family is not split: it
is sound in the model, but a block is freed once"); only the typed rules leave it out
(`docs/strings-slices-design.md` §5.1, §5.4). So the class `printSimAt_lirOf` covers holds
`splitDrop`, which allocates a block of two cells, splits it, and drops each half:

* `splitDrop_sem`: `splitDrop` is in the relation at `F 1` (and effect-free, `splitDrop_effFree`;
  it mentions no slot, `splitDrop_closed`);
* `splitE_run`: under `bumpAlloc` its scrutinee runs to the two halves `(r, 1)` and `(r + 1, 1)` of
  the block `tab` placed at `r = regionBase 0`, both cells live;
* `dropHalf_run`: the first `drop` frees `r` and leaves `r + 1` live;
* `splitDrop_run`: the whole program runs to `()` at the empty memory, through these;
* `freeArr_half_faults`: the LIR's one free of an array (`freeArr`'s `freeObj`) of a half of an
  object of two addresses faults;
* `block_place_obstruction`: these together, with SPEC §56's per-cell print simulated at
  `splitDrop` (`printSimAt_lirOf`).

The typed fact that a block's cells are freed together is a fact of the typed rules, not of the
relation, and the run-based simulation reads the relation. A simulation that places an array as one
block needs a premise over the run that holds of checked programs only: a typing of the run's
configurations, which Core does not have (`Frontend/Check/TFacts.lean`), or block provenance in
the relation (`Core/Blocks.lean`: open).

No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`.
-/

namespace BlockPlace
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core Lowering
open BoCa.BoLo (Heap Head AHead)
open BoCa.Lifetime (LifeCtx)

local instance : HostIs Backend2.lirHost := ⟨⟩

/-! ### The program -/

/-- `λ_. ()`. -/
def unitFn : Val := Val.lam (.val Val.unit)

/-- The literal `n`. -/
def lit (n : UInt32) : Expr := .val (Val.i32 n)

/-- `tab (2, λ_. ())`: a block of two cells holding `()`. -/
def tabE : Expr := .app (.val (Val.prim .tab)) (.pair (lit 2) (.val unitFn))

/-- `split (tab (2, λ_. ()), 1)`. -/
def splitE : Expr := .app (.val (Val.prim .split)) (.pair tabE (lit 1))

/-- `drop (λ_. (), x)`. -/
def dropE (x : Expr) : Expr := .app (.val (Val.prim .drop)) (.pair (.val unitFn) x)

/-- The first arm: `let (a₁, a₂) = p in drop (λ_. (), a₁); drop (λ_. (), a₂)`. -/
def arm₁ : Expr := .letpair (.var 0) (.seq (dropE (.var 1)) (dropE (.var 0)))

/-- **The program**: a block of two cells, split at `1`, each half dropped. -/
def splitDrop : Expr := .case splitE arm₁ (dropE (.var 0))

theorem splitDrop_effFree : effFreeB splitDrop = true := rfl

theorem splitDrop_closed : ∀ k, mentions splitDrop k = false := by
  intro k; simp [splitDrop, splitE, tabE, arm₁, dropE, lit, unitFn, Val.i32, mentions]

/-! ### In the relation -/

theorem persistent_dead {Γ : Ctx VTy} (h : ∀ s ∈ Γ, s.live = false) : Persistent Γ :=
  fun s hs hl => absurd hl (by rw [h s hs]; simp)

/-- `λ_. () : !(A ⇒ 1)` at a dead context, `A` persistent. -/
theorem unitFn_d {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) (hd : ∀ s ∈ Γ, s.live = false)
    {A : VTy} (hA : A.Persistent) : CDerives Δ Γ (.val unitFn) (.val (.bang (.lolli A .unit))) :=
  .bangThunkV (persistent_dead hd) rfl (.lam (.ret (.unitI (.drop hA hΓ))))

/-- `drop (λ_. (), x) : 1` with `x : Array 1` the one live slot. -/
theorem dropE_d {Δ : LifeCtx} {Γ Γd : Ctx VTy} {i : Nat} (hs : Ctx.SplitP Γ Γd Γ)
    (hΓd : Ctx.DeadP Γd) (hd : ∀ s ∈ Γd, s.live = false) (hx : Ctx.SoloP Γ i (.array .unit))
    (hs₂ : Ctx.SplitP Γ Γ Γd) :
    CDerives Δ Γ (dropE (.var i)) (.val .unit) :=
  .lolliE hs₂ (.tensorI hs (unitFn_d hΓd hd rfl) (.var hx)) (.bangE (.arrFree .unit hΓd))

/-- The scrutinee, at the owned family's split. -/
theorem splitE_sem :
    SemV (ℍ := Backend2.lirHost) LifeCtx.empty [] splitE
      (.sum (.tensor (.array .unit) (.array .unit)) (.array .unit)) := by
  have htab : SemV (ℍ := Backend2.lirHost) LifeCtx.empty [] tabE (.array .unit) :=
    lolliE_compatX .nil
      (tensorI_compatC .nil (lit_compatX (.i32 2) .nil)
        (fundamentalC (unitFn_d (A := .int .w32) .nil (by simp) rfl)))
      (bangE_compatC (arrNew_compatX .nil))
  exact lolliE_compatX .nil (tensorI_compatC .nil htab (lit_compatX (.i32 1) .nil))
    (bangE_compatC (famSplit_compatX (L := .ref .unit) .nil))

/-- **`splitDrop` is in the relation at `F 1`.** -/
theorem splitDrop_sem :
    SemC (ℍ := Backend2.lirHost) LifeCtx.empty [] splitDrop (.ret .unit) := by
  let T : VTy := .tensor (.array .unit) (.array .unit)
  let a : VTy := .array .unit
  have h₁ : CDerives LifeCtx.empty [⟨T, true⟩] arm₁ (.comp (.ret .unit)) :=
    .tensorE (.left .nil) (.var (.here .nil))
      (.unitE (.right (.left (.dead .nil)))
        (dropE_d (Γd := [⟨a, false⟩, ⟨a, false⟩, ⟨T, false⟩]) (.dead (.right (.dead .nil)))
          (.cons (.cons (.cons .nil))) (by simp) (.there (.here (.cons .nil)))
          (.dead (.left (.dead .nil))))
        (.ret (dropE_d (Γd := [⟨a, false⟩, ⟨a, false⟩, ⟨T, false⟩]) (.right (.dead (.dead .nil)))
          (.cons (.cons (.cons .nil))) (by simp) (.here (.cons (.cons .nil)))
          (.left (.dead (.dead .nil))))))
  have h₂ : CDerives LifeCtx.empty [⟨a, true⟩] (dropE (.var 0)) (.comp (.ret .unit)) :=
    .ret (dropE_d (Γd := [⟨a, false⟩]) (.right .nil) (.cons .nil) (by simp) (.here .nil)
      (.left .nil))
  exact sumE_compatC .nil splitE_sem (fundamentalC h₁) (fundamentalC h₂)

/-! ### Its run under the LIR's allocator -/

/-- The base `tab` places the block at: the first region's. -/
abbrev r : Nat := regionBase 0

/-- The memory after `tab`: the block's two cells holding `()`. -/
def μ₁ : Heap := Heap.fill Adequacy.emptyMem r 2 Val.unit

/-- The memory after `tab`'s stores: the same cells, written. -/
def μ₂ : Heap := (μ₁.upd (r + 0) Val.unit).upd (r + 1) Val.unit

theorem μ₂_r : μ₂ r = some Val.unit := by
  simp [μ₂, Heap.upd]

theorem μ₂_r1 : μ₂ (r + 1) = some Val.unit := by simp [μ₂, Heap.upd]

theorem μ₁_at {i : Nat} (hi : i < 2) : μ₁ (r + i) = some Val.unit := by
  show (if r ≤ r + i ∧ r + i < r + 2 then some Val.unit else Adequacy.emptyMem (r + i)) = _
  rw [if_pos (by omega)]

/-- `(λ_. ()) v` runs to `()`. -/
theorem unitFn_app (c : Nat) (μ : Heap) (v : Val) :
    BigN (ℍ := Backend2.lirHost) bumpAlloc 1 c μ (.app (.val unitFn) (.val v)) c μ Val.unit := by
  have h := BigN.app (ℍ := Backend2.lirHost) (A := bumpAlloc) (BigN.val c μ v)
    (BigN.val c μ unitFn) (.det (Head.beta μ (.val Val.unit) v) rfl) (BigN.val c μ Val.unit)
  simpa using h

/-- `store ℓ ((λ_. ()) i)` at a written `ℓ`. -/
theorem store_run (c : Nat) (μ : Heap) (ℓ : Loc) (i : UInt32) (hℓ : μ ℓ = some Val.unit) :
    BigN (ℍ := Backend2.lirHost) bumpAlloc 3 c μ
      (.app (.app (.val (Val.prim .store)) (.val (Val.loc ℓ))) (.app (.val unitFn) (.val (Val.i32 i))))
      c (μ.upd ℓ Val.unit) Val.unit := by
  have hs := BigN.storeF (ℍ := Backend2.lirHost) (A := bumpAlloc) (BigN.val c μ (Val.loc ℓ))
    (BigN.val c μ (Val.prim .store))
  have h := BigN.app (ℍ := Backend2.lirHost) (A := bumpAlloc) (unitFn_app c μ (Val.i32 i)) hs
    (.det (Head.store μ ℓ Val.unit Val.unit hℓ) rfl) (BigN.val c (μ.upd ℓ Val.unit) Val.unit)
  simpa using h

/-- `tab (2, λ_. ())` runs to the block `(r, 2)`. -/
theorem tabE_run : ∃ k, BigN (ℍ := Backend2.lirHost) bumpAlloc k 0
    Adequacy.emptyMem tabE 1 μ₂ (Val.arr r 2) := by
  have hpick : bumpAlloc.pick 0 Adequacy.emptyMem (arrLen 2).toNat = r :=
    bumpAlloc_pick (fun _ _ => rfl)
  have hfree : ∀ i, i < (arrLen 2).toNat →
      Adequacy.emptyMem
        (bumpAlloc.pick 0 Adequacy.emptyMem (arrLen 2).toNat + i) = none :=
    fun _ _ => rfl
  have hhead := AHead.tab (ℍ := Backend2.lirHost) 0 Adequacy.emptyMem 2
    unitFn hfree
  have hlen : arrLen 2 = 2 := by decide
  rw [hpick, hlen] at hhead
  have h0 := store_run 1 μ₁ (r + 0) (UInt32.ofNat 0) (μ₁_at (by omega))
  have h1 := store_run 1 (μ₁.upd (r + 0) Val.unit) (r + 1) (UInt32.ofNat 1)
    (by show (if r + 1 = r + 0 then some Val.unit else μ₁ (r + 1)) = _
        rw [if_neg (by omega)]; exact μ₁_at (by omega))
  have hfill := BigN.seq (ℍ := Backend2.lirHost) h0 (BigN.seq h1 (BigN.val 1 μ₂ (Val.arr r 2)))
  have htf : tabFill unitFn r 2 0 (UInt32.toNat 2) =
      .seq (.app (.app (.val (Val.prim .store)) (.val (Val.loc (r + 0))))
          (.app (.val unitFn) (.val (Val.i32 (UInt32.ofNat 0)))))
        (.seq (.app (.app (.val (Val.prim .store)) (.val (Val.loc (r + 1))))
          (.app (.val unitFn) (.val (Val.i32 (UInt32.ofNat 1))))) (.val (Val.arr r 2))) := rfl
  have h01 : (0 + 1 : Nat) = 1 := rfl
  rw [htf, h01] at hhead
  exact ⟨_, BigN.app (ℍ := Backend2.lirHost) (A := bumpAlloc)
    (BigN.val 0 Adequacy.emptyMem (Val.pair (Val.i32 2) unitFn))
    (BigN.val 0 Adequacy.emptyMem (Val.prim .tab)) hhead hfill⟩

/-- The two halves of the block. -/
def halves : Val := Val.inj₁ (Val.pair (Val.arr r 1) (Val.arr (r + 1) 1))

/-- **The scrutinee runs to the block's two halves**, both cells live. -/
theorem splitE_run : ∃ k, BigN (ℍ := Backend2.lirHost) bumpAlloc k 0
    Adequacy.emptyMem splitE 1 μ₂ halves := by
  obtain ⟨k, ht⟩ := tabE_run
  have hpair := BigN.pair (ℍ := Backend2.lirHost) ht (BigN.val 1 μ₂ (Val.i32 1))
  have hans : splitAns r 2 1 = halves := by
    simp [splitAns, halves]
  have h := BigN.app (ℍ := Backend2.lirHost) (A := bumpAlloc) hpair (BigN.val 1 μ₂ (Val.prim .split))
    (.det (Head.split μ₂ r 2 1) rfl) (BigN.val 1 μ₂ (splitAns r 2 1))
  rw [hans] at h
  exact ⟨_, by simpa [splitE, lit] using h⟩

/-- `drop (λ_. (), (ℓ, 1))` at a written `ℓ` frees `ℓ` alone. -/
theorem drop1_run (μ : Heap) (ℓ : Loc) (hℓ : μ ℓ = some Val.unit) :
    ∃ k, BigN (ℍ := Backend2.lirHost) bumpAlloc k 1 μ (dropE (.val (Val.arr ℓ 1))) 1 (μ.del ℓ)
      Val.unit := by
  have hfree := BigN.app (ℍ := Backend2.lirHost) (A := bumpAlloc) (BigN.val 1 μ (Val.loc (ℓ + 0)))
    (BigN.val 1 μ (Val.prim .free)) (.det (Head.free μ (ℓ + 0) Val.unit (by simpa using hℓ)) rfl)
    (BigN.val 1 (μ.del (ℓ + 0)) Val.unit)
  have happ := BigN.app (ℍ := Backend2.lirHost) (A := bumpAlloc) hfree
    (BigN.val 1 (μ.del (ℓ + 0)) unitFn) (.det (Head.beta _ (.val Val.unit) Val.unit) rfl)
    (BigN.val 1 (μ.del (ℓ + 0)) Val.unit)
  have hfill := BigN.seq (ℍ := Backend2.lirHost) happ (BigN.val 1 (μ.del (ℓ + 0)) Val.unit)
  have h := BigN.app (ℍ := Backend2.lirHost) (A := bumpAlloc)
    (BigN.val 1 μ (Val.pair unitFn (Val.arr ℓ 1))) (BigN.val 1 μ (Val.prim .drop))
    (.det (Head.drop μ unitFn ℓ 1) rfl) (by simpa [dropFill] using hfill)
  exact ⟨_, by simpa [dropE] using h⟩

/-- **The first `drop` frees half of the block**: `r` is freed, `r + 1`, allocated by the same
`tab`, is still live. -/
theorem dropHalf_run : ∃ k, BigN (ℍ := Backend2.lirHost) bumpAlloc k 1 μ₂
      (dropE (.val (Val.arr r 1))) 1 (μ₂.del r) Val.unit ∧
    μ₂ r = some Val.unit ∧ μ₂ (r + 1) = some Val.unit ∧ (μ₂.del r) (r + 1) = some Val.unit := by
  obtain ⟨k, h⟩ := drop1_run μ₂ r μ₂_r
  exact ⟨k, h, μ₂_r, μ₂_r1, by simp [Heap.del, μ₂_r1]⟩

theorem out2 {k : Nat} (h0 : ¬ k = r) (h1 : ¬ k = r + 1) : ¬ (r ≤ k ∧ k < r + 2) := by
  intro h
  obtain ⟨ha, hb⟩ := h
  omega

/-- **The whole program runs to `()` at the empty memory**, through `splitE_run` and the two
`drop`s of the halves. -/
theorem splitDrop_run : ∃ k, BigN (ℍ := Backend2.lirHost) bumpAlloc k 0
    Adequacy.emptyMem splitDrop 1
    Adequacy.emptyMem Val.unit := by
  obtain ⟨_, hs⟩ := splitE_run
  obtain ⟨_, hd₁, -, -, hr1⟩ := dropHalf_run
  obtain ⟨_, hd₂⟩ := drop1_run (μ₂.del r) (r + 1) hr1
  have hempty : (μ₂.del r).del (r + 1) = Adequacy.emptyMem := by
    funext k
    by_cases h1 : k = r + 1
    · show (if k = r + 1 then none else _) = none; rw [if_pos h1]
    by_cases h0 : k = r
    · show (if k = r + 1 then none else if k = r then none else _) = none
      rw [if_neg h1, if_pos h0]
    show (if k = r + 1 then none else if k = r then none else
      if k = r + 1 then some Val.unit else if k = r + 0 then some Val.unit else
      if r ≤ k ∧ k < r + 2 then some Val.unit else none) = none
    have hne : ¬ (r ≤ k ∧ k < r + 2) := out2 h0 h1
    rw [if_neg h1, if_neg h0, if_neg h1, if_neg (by omega), if_neg hne]
  rw [hempty] at hd₂
  have hseq := BigN.seq (ℍ := Backend2.lirHost) hd₁ hd₂
  have hsub : ((Expr.seq (dropE (.var 1)) (dropE (.var 0))).subst 0
      ((Val.arr (r + 1) 1).shift 1 0)).subst 0 (Val.arr r 1) =
      .seq (dropE (.val (Val.arr r 1))) (dropE (.val (Val.arr (r + 1) 1))) := rfl
  rw [← hsub] at hseq
  have hlp := BigN.letpair (ℍ := Backend2.lirHost) (A := bumpAlloc)
    (BigN.val 1 μ₂ (Val.pair (Val.arr r 1) (Val.arr (r + 1) 1))) hseq
  have harm : arm₁.subst 0 (Val.pair (Val.arr r 1) (Val.arr (r + 1) 1)) =
      .letpair (.val (Val.pair (Val.arr r 1) (Val.arr (r + 1) 1)))
        (.seq (dropE (.var 1)) (dropE (.var 0))) := rfl
  rw [← harm] at hlp
  exact ⟨_, BigN.case₁ (ℍ := Backend2.lirHost) (A := bumpAlloc) (b := dropE (.var 0)) hs hlp⟩

/-! ### The LIR's one free of an array -/

/-- **Freeing a half of an object of two addresses faults**: `freeObj`, the free of Backend2's
`freeArr` (an array is one object of `n` addresses, `newArr`), on a family of one address at the
base of an object of two. -/
theorem freeArr_half_faults (s : Backend2.St) (b : Nat) (hb : s.objs[b]? = some 2) :
    ∃ msg, (Backend2.freeObj b 1).run s = .error msg := by
  simp [Backend2.freeObj, Backend2.bad, hb]
  exact ⟨_, rfl⟩

/-! ### The obstruction -/

/-- **An array placed as one block is not a property of the runs the simulation follows.**
`splitDrop` is in the class `printSimAt_lirOf` covers (effect-free, mentioning no slot, in the
relation at `F 1`), and SPEC §56's print, which keeps each cell an object of one address, is
simulated at it. The run the simulation follows (`BigN` under `bumpAlloc`) hands the first `drop`
the half `(r, 1)` of the block `tab` placed at `r`, both cells live, and that `drop` frees `r` and
leaves `r + 1`: a print that frees a `tab`'s block once, at a `drop` (`freeArr_half_faults`), has
no run to follow here. -/
theorem block_place_obstruction :
    effFreeB splitDrop = true ∧ (∀ k, mentions splitDrop k = false) ∧
    SemC (ℍ := Backend2.lirHost) LifeCtx.empty [] splitDrop (.ret .unit) ∧
    PrintSimAt (ℍ := Backend2.lirHost) splitDrop (lirOf splitDrop) ∧
    (∃ k, BigN (ℍ := Backend2.lirHost) bumpAlloc k 0 Adequacy.emptyMem splitE 1 μ₂ halves) ∧
    (∃ k, BigN (ℍ := Backend2.lirHost) bumpAlloc k 1 μ₂ (dropE (.val (Val.arr r 1))) 1 (μ₂.del r)
      Val.unit) ∧
    μ₂ r = some Val.unit ∧ μ₂ (r + 1) = some Val.unit ∧ (μ₂.del r) (r + 1) = some Val.unit := by
  obtain ⟨k, hd, h0, h1, h2⟩ := dropHalf_run
  exact ⟨splitDrop_effFree, splitDrop_closed, splitDrop_sem,
    printSimAt_lirOf _ splitDrop_effFree splitDrop_closed splitDrop_sem, splitE_run, ⟨k, hd⟩,
    h0, h1, h2⟩

end BlockPlace
