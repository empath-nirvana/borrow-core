import Frontend.Syntax

/-!
# Frontend — Elab — a pipe chain's normal form  `[spec §70]`

A chain `a ∘₁ s₁ ∘₂ s₂ …` of `|>` (push) and `>|` (pull) edges is read as a source and a list of
edges, each marked with its mode, left-nested, the source first (`PipeChain`). `|>` and `>|`
associate to the left, so `(a ∘₁ b) ∘₂ c` is read as written. A stage that is itself a chain,
`a ∘₁ (b ∘₂ c)`, is spliced into the chain when every edge it adds *joins*: a `>|`, or a `|>`
into a stream stage (`joins`). Otherwise the parenthesised chain is a stage, as §33 reads it.

The elaboration (`Frontend.Elab.Effects.pipesV`) reads the chain's marks only, each edge at the
span from the source to its stage (not its node's, which a bracketing moves), so two bracketings
with one normal form are one core term, up to the positions of the source and stages in the text.
That they have one is `chainOf_bracketing`: the normal form of any bracketing of a sequence of
joining edges is the sequence (`chainOf_assoc` for three stages).
-/

namespace Frontend.Elab.Pipes
open Frontend

/-- One edge of a chain: the span of its `∘` node, its mode, and its stage as written. -/
structure PipeEdge where
  sp : Span
  mode : PipeMode
  stage : Val

/-- A chain in normal form: its source, and its edges in order. -/
structure PipeChain where
  src : Val
  edges : List PipeEdge

/-- What the elaboration reads of a chain besides spans: the source, and each edge's mode and
stage. -/
def PipeChain.marks (c : PipeChain) : Val × List (PipeMode × Val) :=
  (c.src, c.edges.map fun e => (e.mode, e.stage))

/-- The parts of a pipe node `e ∘ s`: the node's span, its mode, `e` and `s`. -/
def pipeParts? : Val → Option (Span × PipeMode × Val × Val)
  | .app sp (.sugar _ (.pipe m)) (.pair _ e s) => some (sp, m, e, s)
  | _ => none

/-- A pipe node, as the parser builds it (`Parser.opsLoop`). -/
def pipeNode (sp : Span) (m : PipeMode) (e s : Val) : Val :=
  .app sp (.sugar sp (.pipe m)) (.pair sp e s)

@[simp] theorem pipeParts?_pipeNode (sp : Span) (m : PipeMode) (e s : Val) :
    pipeParts? (pipeNode sp m e s) = some (sp, m, e, s) := rfl

theorem pipeParts?_eq {V : Val} {sp : Span} {m : PipeMode} {e s : Val}
    (h : pipeParts? V = some (sp, m, e, s)) :
    ∃ osp psp, V = .app sp (.sugar osp (.pipe m)) (.pair psp e s) := by
  unfold pipeParts? at h
  split at h
  · cases h; exact ⟨_, _, rfl⟩
  · cases h

theorem pipeParts?_lt_left {V : Val} {sp : Span} {m : PipeMode} {e s : Val}
    (h : pipeParts? V = some (sp, m, e, s)) : sizeOf e < sizeOf V := by
  obtain ⟨_, _, rfl⟩ := pipeParts?_eq h
  simp only [Val.app.sizeOf_spec, Val.pair.sizeOf_spec]
  omega

theorem pipeParts?_lt_right {V : Val} {sp : Span} {m : PipeMode} {e s : Val}
    (h : pipeParts? V = some (sp, m, e, s)) : sizeOf s < sizeOf V := by
  obtain ⟨_, _, rfl⟩ := pipeParts?_eq h
  simp only [Val.app.sizeOf_spec, Val.pair.sizeOf_spec]
  omega

/-- An edge of mode `m` into the stage `s` joins a chain: it is a `>|`, or `s` is a stream stage
(`stream`, the environment's test, `Frontend.Elab.Effects.PipeEnv.streamStage`). -/
def joins (stream : Val → Bool) (m : PipeMode) (s : Val) : Bool :=
  m == .pull || stream s

/-- The normal form of `V`: a pipe node's left side's chain, extended by its edge; its stage is
spliced in when it is a chain all of whose edges join, the edge into its source included. Any other
value is a source with no edges. -/
def chainOf (stream : Val → Bool) (V : Val) : PipeChain :=
  match h : pipeParts? V with
  | some (sp, m, e, r) =>
    have _ := pipeParts?_lt_left h
    have _ := pipeParts?_lt_right h
    let L := chainOf stream e
    let R := chainOf stream r
    if (pipeParts? r).isSome && joins stream m R.src && R.edges.all (fun x => joins stream x.mode x.stage)
    then ⟨L.src, L.edges ++ ⟨sp, m, R.src⟩ :: R.edges⟩
    else ⟨L.src, L.edges ++ [⟨sp, m, r⟩]⟩
  | none => ⟨V, []⟩
termination_by sizeOf V

/-! ### Bracketings -/

/-- A bracketing of a chain: its leaves are stages (or the source), its nodes edges. -/
inductive PipeTree where
  | leaf (V : Val)
  | node (sp : Span) (m : PipeMode) (l r : PipeTree)

/-- The value a bracketing writes. -/
def PipeTree.toVal : PipeTree → Val
  | .leaf V => V
  | .node sp m l r => pipeNode sp m l.toVal r.toVal

/-- Its leaves are not pipe nodes. -/
def PipeTree.leavesOk : PipeTree → Prop
  | .leaf V => pipeParts? V = none
  | .node _ _ l r => l.leavesOk ∧ r.leavesOk

/-- The sequence a bracketing brackets: its first leaf, then each edge's mode and the leaf after
it, in order. -/
def PipeTree.flat : PipeTree → Val × List (PipeMode × Val)
  | .leaf V => (V, [])
  | .node _ m l r => (l.flat.1, l.flat.2 ++ (m, r.flat.1) :: r.flat.2)

theorem chainOf_leaf (stream : Val → Bool) {V : Val} (h : pipeParts? V = none) :
    chainOf stream V = ⟨V, []⟩ := by
  rw [chainOf]; split <;> simp_all

theorem chainOf_node (stream : Val → Bool) (sp : Span) (m : PipeMode) (e r : Val) :
    chainOf stream (pipeNode sp m e r) =
      let L := chainOf stream e
      let R := chainOf stream r
      if (pipeParts? r).isSome && joins stream m R.src &&
          R.edges.all (fun x => joins stream x.mode x.stage)
      then ⟨L.src, L.edges ++ ⟨sp, m, R.src⟩ :: R.edges⟩
      else ⟨L.src, L.edges ++ [⟨sp, m, r⟩]⟩ := by
  rw [chainOf]; split
  · rename_i h; simp only [pipeParts?_pipeNode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
  · rename_i h; simp at h

/-- **The normal form of a bracketing is the sequence it brackets**, when every edge joins: the
marks of `chainOf` of any bracketing are its flattening. -/
theorem chainOf_bracketing (stream : Val → Bool) :
    ∀ (t : PipeTree), t.leavesOk → (∀ p ∈ t.flat.2, joins stream p.1 p.2 = true) →
      (chainOf stream t.toVal).marks = t.flat
  | .leaf V, hl, _ => by
    simp only [PipeTree.toVal, PipeTree.flat, chainOf_leaf stream hl, PipeChain.marks,
      List.map_nil]
  | .node sp m l r, hl, hj => by
    have hjl : ∀ p ∈ l.flat.2, joins stream p.1 p.2 = true := fun p hp =>
      hj p (by simp [PipeTree.flat, hp])
    have hjm : joins stream m r.flat.1 = true := hj (m, r.flat.1) (by simp [PipeTree.flat])
    have hjr : ∀ p ∈ r.flat.2, joins stream p.1 p.2 = true := fun p hp =>
      hj p (by simp [PipeTree.flat, hp])
    have ihl := chainOf_bracketing stream l hl.1 hjl
    have ihr := chainOf_bracketing stream r hl.2 hjr
    have ihl1 := congrArg Prod.fst ihl
    have ihl2 := congrArg Prod.snd ihl
    have ihr1 := congrArg Prod.fst ihr
    have ihr2 := congrArg Prod.snd ihr
    simp only [PipeChain.marks] at ihl1 ihl2 ihr1 ihr2
    simp only [PipeTree.toVal, chainOf_node]
    cases r with
    | leaf W =>
      have hW : pipeParts? W = none := hl.2
      simp only [PipeTree.toVal, hW, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, PipeChain.marks, List.map_append, List.map_cons, List.map_nil, PipeTree.flat,
        ihl1, ihl2]
    | node sp' m' l' r' =>
      have hall : (chainOf stream (PipeTree.node sp' m' l' r').toVal).edges.all
          (fun x => joins stream x.mode x.stage) = true := by
        rw [List.all_eq_true]
        intro x hx
        have : (x.mode, x.stage) ∈ (PipeTree.node sp' m' l' r').flat.2 := by
          rw [← ihr2]; exact List.mem_map.2 ⟨x, hx, rfl⟩
        exact hjr _ this
      have hjm' : joins stream m (chainOf stream (PipeTree.node sp' m' l' r').toVal).src = true := by
        rw [ihr1]; exact hjm
      simp only [PipeTree.toVal, pipeParts?_pipeNode, Option.isSome_some, Bool.true_and] at hjm' hall ihr1 ihr2 ⊢
      simp only [hjm', hall, Bool.and_self, ↓reduceIte, PipeChain.marks, List.map_append,
        List.map_cons]
      rw [ihl1, ihl2, ihr2, ihr1]
      rfl

/-- **Two bracketings of one chain have one normal form.** -/
theorem chainOf_bracketings_eq (stream : Val → Bool) (t u : PipeTree)
    (ht : t.leavesOk) (hu : u.leavesOk) (hflat : t.flat = u.flat)
    (hj : ∀ p ∈ t.flat.2, joins stream p.1 p.2 = true) :
    (chainOf stream t.toVal).marks = (chainOf stream u.toVal).marks := by
  rw [chainOf_bracketing stream t ht hj, chainOf_bracketing stream u hu (hflat ▸ hj), hflat]

/-- Three stages: `(a ∘₁ b) ∘₂ c` and `a ∘₁ (b ∘₂ c)` have one normal form when both edges join
(`a`, `b`, `c` not pipe nodes; any spans). -/
theorem chainOf_assoc (stream : Val → Bool) (sp₁ sp₂ sp₃ sp₄ : Span) (m₁ m₂ : PipeMode)
    (a b c : Val) (ha : pipeParts? a = none) (hb : pipeParts? b = none) (hc : pipeParts? c = none)
    (h₁ : joins stream m₁ b = true) (h₂ : joins stream m₂ c = true) :
    (chainOf stream (pipeNode sp₂ m₂ (pipeNode sp₁ m₁ a b) c)).marks =
      (chainOf stream (pipeNode sp₃ m₁ a (pipeNode sp₄ m₂ b c))).marks :=
  chainOf_bracketings_eq stream
    (.node sp₂ m₂ (.node sp₁ m₁ (.leaf a) (.leaf b)) (.leaf c))
    (.node sp₃ m₁ (.leaf a) (.node sp₄ m₂ (.leaf b) (.leaf c)))
    ⟨⟨ha, hb⟩, hc⟩ ⟨ha, hb, hc⟩ (by simp [PipeTree.flat])
    (by simp [PipeTree.flat]; exact ⟨h₁, h₂⟩)

end Frontend.Elab.Pipes
