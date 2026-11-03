import Support.Model.Tree.Parent

/-!
# The cactus realised: fresh children, capture, graft

`[spec §62]`. The lifetime order the run builds. A fresh lifetime is a child of the current branch's innermost
lifetime: a parent function whose parents were opened first (`ParentFn.InAlloc`), so the order
sits inside the printed chain (`Cactus.ofParent_inChain`). Capture changes no parent: the stored
task's lifetimes stay a subtree. Spawn opens the children's lifetimes as children of the
spawning branch's innermost lifetime: two children's lifetimes are siblings or cousins.

**Graft.** Resuming a stored task inside the resumer's innermost lifetime `t` moves the task's
subtree under `t`: the root `r` of the subtree gets `t` as its parent (`ParentFn.Graft`). The
task can then hold the borrows the resumer passes it at `t`.

* When the capture point (the root's old parent) is above `t`, as it is when the resumer runs
  inside the scope the task was captured in, the graft adds order facts and removes none
  (`graft_mono`). The task's open lends keep their records and tags; their lifetimes gain
  ancestors.
* `t` may have been opened after `r`: a handler lends its own cell at `β`, after the task lent
  at `α`, and resumes the task inside `β`. Then the task's `α` lies
  inside `β`: `graftEx_lt`, and `β` is still not inside `α` (`graftEx_not_le`).
* That graft puts a lifetime inside one opened after it. The order no longer sits inside the
  printed chain (`graftEx_not_inChain`), and the printed carrier, whose strata follow the
  chain, refuses a cell the tree admits: a view at `β` is not in `α`'s printed stratum
  (`graftEx_printed_refuses`), though `α` lies inside `β`. The tree-stratified carrier admits it
  with no lifetime renamed (`Tree/CarrierGraftEx.lean`, `graftCell_admitted`).
* The other route, renaming the task's lifetimes on graft to lifetimes opened after `t`, keeps
  every parent opened before its children (`renameEx`). It is not taken.

Re-capture detaches the subtree again and removes the facts the graft added; that is sound
only if the detached subtree holds no borrow at the lifetimes it leaves. Not derived here.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

namespace ParentFn

/-- `P'` is `P` with `r`'s parent moved to `t`. -/
def Graft (P P' : ParentFn) (r t : Nat) : Prop :=
  P'.par r = t ∧ ∀ n, n ≠ r → P'.par n = P.par n

/-- Ancestry outside `r`'s subtree is unchanged by a graft at `r`. -/
theorem anc_transfer {P P' : ParentFn} {r t : Nat} (hg : P.Graft P' r t) {x c : Nat}
    (h : P.Anc x c) (hx : ¬ P.Anc x r) : P'.Anc x c := by
  induction h with
  | refl => exact .refl _
  | @up x c h ih =>
      have hxr : x ≠ r := fun e => hx (by rw [e]; exact .refl r)
      have hpx : ¬ P.Anc (P.par x) r := fun h' => hx (.up h')
      exact .up (by rw [hg.2 x hxr]; exact ih hpx)

/-- **A graft whose capture point is above the resume point adds order facts and removes
none.** `t` is not inside `r`'s subtree, and `r`'s old parent is `t` or above it. -/
theorem graft_mono {P P' : ParentFn} {r t : Nat} (hg : P.Graft P' r t)
    (hc : P.Anc t (P.par r)) (ht : ¬ P.Anc t r) {a b : Nat} (h : P.Anc a b) : P'.Anc a b := by
  induction h with
  | refl => exact .refl _
  | @up a b _ ih =>
      by_cases ha : a = r
      · subst ha
        have h₁ : P'.Anc a t := .up (by rw [hg.1]; exact .refl t)
        exact h₁.trans ((anc_transfer hg hc ht).trans ih)
      · exact .up (by rw [hg.2 a ha]; exact ih)

end ParentFn

/-! ### A handler's lend, and a task resumed inside it -/

/-- Before: the task's lend `α = 1` and the resumer's later lend `β = 2`, both children of the
scope `⊤`. -/
def beforeP : ParentFn where
  par _ := 0
  rank n := if n = 0 then 0 else 1
  par_zero := rfl
  rank_lt _ hn := by simp [hn]

theorem beforeP_inAlloc : beforeP.InAlloc := fun _ hn => Nat.pos_of_ne_zero hn

/-- After resuming the task inside `β`: `α`'s parent is `β`. -/
def graftP : ParentFn where
  par n := if n = 1 then 2 else 0
  rank n := if n = 0 then 0 else if n = 1 then 2 else 1
  par_zero := rfl
  rank_lt n hn := by
    show (if (if n = 1 then 2 else 0) = 0 then 0 else
      if (if n = 1 then 2 else 0) = 1 then 2 else 1) < (if n = 0 then 0 else if n = 1 then 2 else 1)
    split_ifs <;> omega

theorem graftEx_graft : beforeP.Graft graftP 1 2 :=
  ⟨rfl, fun n hn => by show (if n = 1 then 2 else 0) = 0; simp [hn]⟩

theorem graftEx_mono {a b : Nat} (h : beforeP.Anc a b) : graftP.Anc a b :=
  ParentFn.graft_mono graftEx_graft (beforeP.anc_zero 2) (fun h => by
    rcases h.eq_or_rank_lt with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)) h

/-- Before the graft, `α` and `β` are siblings. -/
theorem beforeEx_siblings :
    ¬ (Cactus.ofParent beforeP).le (OrderDual.toDual 2) (OrderDual.toDual 1) ∧
      ¬ (Cactus.ofParent beforeP).le (OrderDual.toDual 1) (OrderDual.toDual 2) := by
  constructor <;> intro h <;> change beforeP.Anc _ _ at h <;>
    rcases h.eq_or_rank_lt with h | h <;> simp_all [beforeP]

/-- **After the graft, `α` lies inside `β`.** -/
theorem graftEx_lt : (Cactus.ofParent graftP).lt (OrderDual.toDual 1) (OrderDual.toDual 2) :=
  ⟨.up (by show graftP.Anc (graftP.par 1) 2; exact .refl 2),
    fun h => by have := congrArg OrderDual.ofDual h; simp at this⟩

/-- After the graft, `β` is not inside `α`. -/
theorem graftEx_not_le :
    ¬ (Cactus.ofParent graftP).le (OrderDual.toDual 2) (OrderDual.toDual 1) :=
  fun h' => graftEx_lt.2 ((Cactus.ofParent graftP).antisymm graftEx_lt.1 h')

/-- **The grafted order does not sit inside the printed chain.** -/
theorem graftEx_not_inChain : ¬ (Cactus.ofParent graftP).InChain := by
  intro h
  have := h graftEx_lt.le
  have h' : OrderDual.ofDual (OrderDual.toDual 2 : Life) ≤ OrderDual.ofDual (OrderDual.toDual 1) :=
    this
  simp at h'

theorem graftP_not_inAlloc : ¬ graftP.InAlloc := fun h => by
  have := h 1 (by decide)
  simp [graftP] at this

variable {Loc Val : Type}

/-- **The printed carrier refuses what the grafted tree admits**: a view at `β = 2` is not in
`α = 1`'s printed stratum, though `α` lies inside `β` after the graft (`graftEx_lt`). -/
theorem graftEx_printed_refuses (l : Loc) (v : Val) :
    ¬ ResU.InStratum (OrderDual.toDual 1)
        (ResU.single l (CellU.immOf (LSet.singleton (OrderDual.toDual 2)) v
          (PMap.empty : ResU Loc Val) (fun _ _ e => by simp at e))) := by
  intro h
  have := h l _ (ResU.single_get_self _ _)
  have h' : OrderDual.ofDual (OrderDual.toDual 2 : Life) < OrderDual.ofDual (OrderDual.toDual 1) :=
    this
  simp at h'

/-- **Renamed on graft**: the task's `α` re-opened as `3`, a child of `β = 2`. Parents are
opened before their children again. -/
def renameP : ParentFn where
  par n := if n = 3 then 2 else 0
  rank n := n
  par_zero := rfl
  rank_lt n hn := by
    show (if n = 3 then 2 else 0) < n
    split_ifs <;> omega

theorem renameP_inAlloc : renameP.InAlloc := fun n hn => renameP.rank_lt n hn

theorem renameEx : renameP.InAlloc ∧
    (Cactus.ofParent renameP).lt (OrderDual.toDual 3) (OrderDual.toDual 2) ∧
    (Cactus.ofParent renameP).InChain :=
  ⟨renameP_inAlloc,
    ⟨.up (by show renameP.Anc (renameP.par 3) 2; exact .refl 2),
      fun h => by have := congrArg OrderDual.ofDual h; simp at this⟩,
    Cactus.ofParent_inChain renameP_inAlloc⟩

end BoCa.Fig16.Tree

end
