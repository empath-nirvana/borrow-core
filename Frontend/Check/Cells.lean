import Frontend.Check.TExpr
import Frontend.Check.Decide

/-!
# Frontend — Check — cell classes  `[spec §3, §5]`

A cell's contents change type at `swap` (`Ref A ⊸ B ⊸ Ref B ⊗ A`), so the words a cell needs are
those of the widest contents it holds over its lifetime, not of the type it is allocated at. The
checker carries, for each type a cell of the program is allocated at, its **class**: every type
such a cell may hold, the allocation's type and every type a swap of the program can put into a
cell holding one of them (`Checked.cells`, `Frontend/Check/Program.lean`).

* **What changes a cell's type.** Only a `swap` of an owned `Ref`: every other rule that writes a
  location keeps its type (`withswap` and the slice swap at `Mut @a A`, `array_replace` at
  `Array A`, `store` inside them), and an array's slots are never owned `Ref`s. So the edges are
  the typed term's `swap A B` nodes, whose types the derivation fixes (they are the rule's
  arguments), and the swap inside `fold_reuse`'s term (`Core/FoldReuse.lean`): at each `Ref X`
  of its shape it empties the cell by `swap w ()`, so a cell holding `μX. T` comes to hold `1`.
* **Where cells are allocated.** An `alloc A` node, and each leaf of a block's allocation
  (`allocS σ`).
* **Up to lifetimes.** A cell's type is compared with its lifetimes erased (`VTy.eraseLife`): the
  layout of a value does not depend on them, and a cell lent under a lifetime binder is swapped
  at the binder's instance.

The class is closed under the program's edges (`cellsOkB`, checked when it is built, and
`cells_closed`), so it holds the allocation's type and everything a chain of the program's swaps
reaches from it. That a cell holds only its class's types at run time is not proved here: it is
recorded in `Frontend/Check/TFacts.lean`.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa

mutual
/-- A value type with its lifetimes erased: every lifetime `⊤`, every lifetime binder `0`. -/
def _root_.BoCa.Fig16.LogRel.Core.VTy.eraseLife : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor A.eraseLife B.eraseLife
  | .zero => .zero
  | .sum A B => .sum A.eraseLife B.eraseLife
  | .thunk C => .thunk C.eraseLife
  | .ref A => .ref A.eraseLife
  | .imm _ A => .imm .top A.eraseLife
  | .mut _ A => .mut .top A.eraseLife
  | .box _ A => .box .top A.eraseLife
  | .bang A => .bang A.eraseLife
  | .unk => .unk
  | .tvar n => .tvar n
  | .mu A => .mu A.eraseLife
  | .int w => .int w
  | .fam L => .fam L.eraseLife
  | .opq k => .opq k

/-- A computation type with its lifetimes erased. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.eraseLife : CTy → CTy
  | .ret A => .ret A.eraseLife
  | .arr A C => .arr A.eraseLife C.eraseLife
  | .amp C D => .amp C.eraseLife D.eraseLife
  | .top => .top
  | .all _ _ C => .all 0 .top C.eraseLife
  | .nu C => .nu C.eraseLife
  | .eff n i q A B fin cg C => .eff n i q A.eraseLife B.eraseLife fin.eraseLife cg C.eraseLife
end

/-- The fields of a fold's shape at `Ref X`. -/
def _root_.BoCa.Fig16.LogRel.Core.FShape.hasRefX : FShape → Bool
  | .refX => true
  | .leaf _ | .varX => false
  | .tensor F G | .sum F G => F.hasRefX || G.hasRefX

/-- The leaves of a block's shape. -/
def _root_.BoCa.Fig16.LogRel.Core.Shape.leaves : Shape → List VTy
  | .leaf A => [A]
  | .node s₁ s₂ => s₁.leaves ++ s₂.leaves

/-- The depth bound for reading a typed term. -/
def cellsFuel : Nat := 1 <<< 20

/-- **What a node does to cells**: the types it allocates cells at, and the edges along which it
changes a cell's type, lifetimes erased. -/
def TExpr.cellOps : TExpr → List VTy × List (VTy × VTy)
  | .alloc _ _ A => ([A.eraseLife], [])
  | .allocS _ _ σ => (σ.leaves.map VTy.eraseLife, [])
  | .swap _ _ A B => ([], [(A.eraseLife, B.eraseLife)])
  | .foldReuse _ _ F _ =>
      ([], if F.hasRefX then [((VTy.mu F.ty).eraseLife, .unit)] else [])
  | _ => ([], [])

/-- Every node's cell operations, added to `acc`, each once. -/
def TExpr.cellsAcc : Nat → TExpr → List VTy × List (VTy × VTy) → List VTy × List (VTy × VTy)
  | 0, _, acc => acc
  | n + 1, t, (as, es) =>
    let (a, e) := t.cellOps
    let as := a.foldl (fun as x => if as.contains x then as else as ++ [x]) as
    let es := e.foldl (fun es x => if es.contains x then es else es ++ [x]) es
    t.children.foldl (fun acc (_, k) => k.cellsAcc n acc) (as, es)

/-- **A term's cells**: the types it allocates cells at, and the edges along which it changes a
cell's type, each once. -/
def TExpr.cells (t : TExpr) : List VTy × List (VTy × VTy) := t.cellsAcc cellsFuel ([], [])

/-- A cell class: the type a cell is allocated at, and every type it may hold. -/
structure CellClass where
  root : VTy
  tys : List VTy

/-- The types reachable from `xs` along `es`, `n` rounds. -/
def reachN (es : List (VTy × VTy)) : Nat → List VTy → List VTy
  | 0, xs => xs
  | n + 1, xs =>
    let ys := (es.filter fun (a, _) => xs.contains a).map (·.2)
    let new := ys.filter (!xs.contains ·)
    if new.isEmpty then xs else reachN es n (xs ++ new.eraseDups)

/-- The classes of the allocation types `as` under the edges `es`. -/
def cellClasses (as : List VTy) (es : List (VTy × VTy)) : List CellClass :=
  as.map fun A => ⟨A, reachN es (es.length + 1) [A]⟩

/-- **The classes are closed**: each holds its root, and every edge from a type it holds leads to a
type it holds. -/
def cellsOkB (as : List VTy) (es : List (VTy × VTy)) (cs : List CellClass) : Bool :=
  as.all (fun A => cs.any (·.root == A)) &&
  cs.all fun c => c.tys.contains c.root && es.all fun (a, b) => !c.tys.contains a || c.tys.contains b

theorem cellsOkB_sound {as : List VTy} {es : List (VTy × VTy)} {cs : List CellClass}
    (h : cellsOkB as es cs = true) :
    (∀ A ∈ as, ∃ c ∈ cs, c.root = A) ∧
      ∀ c ∈ cs, c.root ∈ c.tys ∧ ∀ e ∈ es, e.1 ∈ c.tys → e.2 ∈ c.tys := by
  simp only [cellsOkB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun A hA => ?_, fun c hc => ⟨(h.2 c hc).1, fun e he h₁ => ?_⟩⟩
  · obtain ⟨c, hc, e⟩ := h.1 A hA
    exact ⟨c, hc, e⟩
  · rcases (h.2 c hc).2 e he with h' | h'
    · have : c.tys.contains e.1 = true := List.contains_iff_mem.mpr h₁
      rw [this] at h'; cases h'
    · exact h'

end BoCa.Fig16.LogRel.Core.Check
