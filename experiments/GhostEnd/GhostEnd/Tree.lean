import Core.Wp

/-!
# GhostEnd — re-lending in stack order respects the nesting

The internal lends of a segment form a forest. A lend taken inside another lend's scope is that
lend's child. The lender frames sit on the stack in an order that puts every parent before its
children, since a child's frame is pushed while its parent's is open. So stack order, outermost
first, is a linear extension of the forest.

At a resumption the frames re-lend in that order (`ewpTS_M_frameR` at each frame). Each one picks
its lifetime fresh, below every lifetime live at that point, as 6.65's H4 does. That set includes
the lifetimes of the frames re-lent before it. `relend_respects_nesting`: every child's lifetime
is then strictly shorter than its parent's, which is the order 6.65 and 6.150 require of nested
lends. `exists_relend_lifetimes`: such a choice exists below any finite record list
(`exists_fresh`).

What is mechanised for the frames themselves is one lender frame (`ewpTS_M_frameR`).
Nested lends that are open together at a resuming stop are not mechanised. That case needs the
borrower of the outer lend to be re-lendable across the inner frame, which is `RelendOfTyped`'s
territory (`GhostEnd.Open`).
-/

noncomputable section

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core

/-- Re-lending in stack order respects the nesting forest: `par i = some j` (frame `i`'s lend was
taken inside frame `j`'s) puts `j` before `i` on the stack. Lifetimes chosen fresh in stack order
put every child strictly below its parent. -/
theorem relend_respects_nesting {n : ℕ} (par : Fin n → Option (Fin n))
    (hpar : ∀ i j, par i = some j → j < i) (α : Fin n → Life)
    (hfresh : ∀ i j, j < i → α i ⊏ α j) : ∀ i j, par i = some j → α i ⊏ α j :=
  fun i j h => hfresh i j (hpar i j h)

/-- Lifetimes fresh in stack order exist, below every record of a list. -/
theorem exists_relend_lifetimes (ls : List SRec) (n : ℕ) :
    ∃ α : Fin n → Life, (∀ i j, j < i → α i ⊏ α j) ∧ ∀ i, ∀ x ∈ ls, α i ⊏ x.2 := by
  obtain ⟨b, hb⟩ := exists_fresh ls
  refine ⟨fun i => OrderDual.toDual (OrderDual.ofDual b + i.val), fun i j hij => ?_,
    fun i x hx => lt_of_le_of_lt ?_ (hb x hx)⟩
  · show OrderDual.ofDual b + j.val < OrderDual.ofDual b + i.val
    have : j.val < i.val := hij
    omega
  · show OrderDual.ofDual b ≤ OrderDual.ofDual b + i.val
    omega

end GhostEnd
