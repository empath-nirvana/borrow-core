import Frontend.Check.TDerives
import Frontend.Check.Handled

/-!
# Frontend — Check — what the typed term does not fix  `[spec §3]`

A node holds its rule's arguments, and a typed derivation fixes each of them (`TDerivesAt`,
`Frontend/Check/TDerives.lean`). A split's use masks are fixed too: the typed rule at a split
relates them to its parts' contexts (`SplitMasks`, `TDerivesAt.split_masks`). One fact the checker
computes is on the term without being fixed by the derivation, because the rule's statement keeps
it out of it:

* **A side condition's witness.** `withbor2`'s premise `∃ b, Δ ⊨ @b ∧ Δ ⊢ A ⊒ @b` (and the
  unwinding and slice borrows', and R1's) is a `Prop`: the lifetime the source writes is checked
  and is not an argument of the rule, so it is not a field of the node
  (`TDerivesAt.withbor2_witness_free`).

A second is a fact the checker carries beside the term (`Checked.cells`, `Frontend/Check/Cells.lean`):

* **A cell's class.** For each type `main` allocates a cell at, every type such a cell may hold:
  the class is closed under the typed term's `swap` nodes, whose types the derivation fixes
  (`Checked.cells_closed`). That at run time a cell holds only types of its class is not proved.
  It would be pinned by a lemma over the machine: in a run of a term with a derivation, the
  contents of a location allocated at `A` are, at every step, of a type a chain of the
  derivation's `swap` applications reaches from `A` (from `swap`'s typing and the location's one
  owned `Ref`). The class is an upper bound: it joins the cells of one type, so a cell can be
  given a type another cell of its type is swapped to (`corpus/cells.expected`).

Three marked derived nodes (`Frontend/Check/Derived.lean`) record what the elaborator's scheme
means beside the shape their rule fixes (`walkB`, `selfCallB`, `lendCellB`):

* **A counted walk's view.** The rule fixes that the term is a `count_fold` or a `count_try`, and
  `walk_fold_index_lt`/`walk_index_lt`/`walk_get_leaf`/`walk_split_first` that its step runs below
  the bound and that below its length a view's read answers a leaf. With `read` (SPEC §46) the
  rule also fixes, of the term's erasure, that at a shared view the bound is the view's length and
  the state's first component the view, that the step reads a copy of that component at its
  counter, and that every tail of the step hands the component on unchanged, as a variable
  (`walkReadB`, `walkStepB`, `walkTailsB`); at a unique view, that the step's read is of the head
  a split by one gives (`walk_get_split`). Two things are not fixed by the derivation: that the
  read the step makes is the one its `walkGet` node marks (the elaboration's mark, and the
  checker's count of one `walkGet` in the walk), and that a tail handing the variable on hands its
  value on in every run, which a lemma over the step's reduction would pin.
* **A self-call's member.** The rule fixes that the term is a variable; that it is the recursive
  group's self-reference, and that the call reads member `j` of `n`, is the elaborator's
  (`Frontend.Elab.Effects.memberCall`). The projections that read member `j` are rule nodes after
  it; the group's generator binds the variable (`boundedFix`'s step), which a check of the
  variable against the generator's binder would pin.
* **A lent cell's release.** The rule fixes that the term is a borrow of a cell it allocates; that
  the owner it hands back is freed in the same code, after the lend, is the owner's slot's use (an
  explicit `free`, or the destructor the checker inserts), which the derivation fixes at that
  use but the node does not point to.

The `use` node's `TInfo.key` is the elaborator's key of the `def` it uses (`Frontend.DefKey`): the
template and type arguments of an instance, or the function and keys of a copy for its handlers
and sites. Copies whose keys differ only in their sites' names share a `body`. That they are one
body, the same term up to the renaming of those sites' static names, is the elaboration's: a
renaming of a typed derivation's effect names (rows, operation signatures, `handle` names) would
pin it, and the checker would then check one copy and rename it for the others.

A third is a field the checker adds to a node that its rule does not have:

* **The clause kinds at `[handle]`** (`ks`). The node holds its handler's pair `(h_ret, hs)`, the
  clauses inline (`tc`), and the checker classifies each clause from it: `ks` is
  `classifyHandler E tc` (`Frontend/Check/Kinds.lean`), a function of the node's own fields, and
  each kind gives its law's premise at the clause of the node's erasure the handler runs for the
  operation (`classifyHandler_sound`, from `classify_sound`). The rule's premises type `tc` and
  have no kinds, so the derivation does not constrain `ks` (`TDerivesAt.kinds_free`); that the
  checker writes `classifyHandler E tc` at each node it builds is its construction
  (`rEffHandle`'s argument at `[handle]`), not a statement about every typed term.
* **The `StoredAtX` records at `[handle]`** (`sshape`, on the node's `TInfo`). For each operation
  the checker classifies `stored` in `ks`, the derivation of the `StoredAtX` grammar it finds for
  the clause of the node's pair (`storedShapes E R tc ks`, `Frontend/Check/StoredAtX.lean`), a
  function of the node's own fields; a record is a derivation of the grammar at the clause of the
  node's erasure the handler runs, at a `P`-shaped answer (`storedShapes_sound`). As with `ks`,
  that the checker writes `storedShapes E R tc ks` at each node it builds is its construction, not
  a statement about every typed term; the rule does not constrain `TInfo`.

A fourth is a field the checker adds to a node and its typed rule pins:

* **The frames inside a handled computation at `[handle]`** (`inside`,
  `Frontend/Check/Handled.lean`): the typed rule's premise `inside = te.erase.hin`
  (`TDerivesAt.inside_eq`, `TDerivesP.inside_eq`, and at `effHandleVB` and `effHandleT`). It is
  the frames the handled computation holds as written, through `use` bodies and a recursive
  group's generator. It is not a bound on the frames a run puts between a `perform` and the
  handler: code that flows into the handled computation puts frames there too (a closure bound
  outside it, a continuation captured at another handler and resumed inside, a value read from
  memory). The bound the theorem reads is the program's (`Checked.flows`), which holds all such
  code at once, and so every node's `inside`.

  Condition 2 is over the names a clause's own code performs or raises (`handlerNames`,
  `Checked.unhandledNames`), and at a clause that performs and raises nothing it holds in every
  `K` without a bound. Where a clause has names, a bound per node is stated, not proved
  (`Checked.FramesPerNode`): the frames under a handler frame of the name `n` are within the
  `inside` of the nodes of the name, `0`, and, where code flows into their handled computation,
  the record of the code that may flow when only a clause that may keep `κ` lets its handled
  computation's frames flow (`Checked.flowsKept`). Two facts would give it:
  - that a clause whose kind keeps no `κ` (`tail`, `tail+state`, `resume-or-cancel`, `once`)
    never lets its `κ` leave the clause, so that only a site whose clause stores `κ` adds its
    handled computation's frames to what flows: `FramesPerNode` at `codeIn := fun _ => true`;
  - an invariant of the run, from the typing, that a value of a type with no `U` holds no code,
    so that only the handled computation's free variables, its operations' answers and the cells
    it reads at types with a `U` bring code in: `FramesPerNode` at `codeIn n` false for a name
    whose handled computations take in no code at a type with a `U`. Core has no typing of a
    run's configurations (`CDerives` types no location, and the relation is stated over runs to
    a value), which this needs.

  Neither decides a direct call of the corpus: every direct call's clause performs and raises
  nothing (`corpus/handled.expected`). Of the handle nodes where condition 2 fails at the
  program's record, two hold at the first fact's bound (`div-infer` 2.0,
  `effects-cancel-two-sites` 3.0); the six of `reconcile-chain` and `reconcile-clock` fail at
  both, since `deadline`'s handled computation is `m(())`, a parameter of a `U` type, and the
  code that may flow holds `retry`'s `to_result` handler, in its loop's body.

A fifth is a field the elaboration of effects gives a node, which the checker reads and checks:

* **The site at `[handle]`** (`site`, `HSite`): the effect, its type arguments, the handler, the
  name the `with` gives it, the kind of site and the handler's state. The elaboration of effects
  records it (`SiteRec`) on the site's sugar; it travels with the code it is in, through the
  instances of a template, to the `handle` node the typed elaboration assembles, which carries it
  with its types in the frame of the node's code (a `for`'s or a stored generator's site resolves
  them at its callee's type arguments, `siteAtCall`). The checker elaborates them there to core
  types (`siteOf`), checks that the record names the node, and that its operations are the
  node's `E`, the operations the derivation handles (at a `for`'s site with the threaded
  variables beside each argument and as each answer, `recOps`): a record that does not is an
  internal error, and `siteOf_ops` states what a site the checker gives a node satisfies. The rule
  has no site, so the derivation does not constrain it (`TDerivesAt.site_free`). What is not
  pinned:
  - that the operations are the declared operations of `eff` at `args`: the effect declarations
    are elaborated away before the checker, so it has neither, and the record's operations are
    the declaration's as the elaboration of effects instantiates it;
  - the handler, the slot and the kind are names; the kind is checked against the clause kinds
    of the nodes of the name (`siteKindMismatch`), the others not at all;
  - the handler's state: that the state is the domain of the function the node's `R` answers
    needs the elaboration of a state-passing clause stated as a rule;
  - at a `for`'s site, the threaded type is the node's, not the record's;
  - a `handle` node the elaboration writes that is no site of its own, as a counted loop's
    handler of the abortive operations of a site around it, has no record.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

/-- **A side condition's witness is not on the node**: `withbor2`'s node is the same at every
lifetime that witnesses its side condition. -/
theorem TDerivesAt.withbor2_witness_free {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo}
    {A B : VTy} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (b₁ b₂ : Lifetime.Life)
    (h₁ : Δ.Defines b₁ ∧ VOutlivesLe Δ b₁ A) (h₂ : Δ.Defines b₂ ∧ VOutlivesLe Δ b₂ A) :
    TDerivesAt Ξ Δ Γ (.withbor2 i (.val (axWithbor2Ty x Δ.meetOfDom A B)) A B x)
        (.val (axWithbor2Ty x Δ.meetOfDom A B)) ∧
      TDerivesAt Ξ Δ Γ (.withbor2 i (.val (axWithbor2Ty x Δ.meetOfDom A B)) A B x)
        (.val (axWithbor2Ty x Δ.meetOfDom A B)) :=
  ⟨.withbor2 x hΓ hx ⟨b₁, h₁⟩ hfree₁ hfree₂, .withbor2 x hΓ hx ⟨b₂, h₂⟩ hfree₁ hfree₂⟩

/-- **The clause kinds are the checker's, not the derivation's**: a typed derivation of a
`handle` node is one at any kinds. -/
theorem TDerivesAt.kinds_free {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J : Jdg}
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {ks : List ClauseKinds.HKind} (ks' : List ClauseKinds.HKind)
    {site : Option HSite} {ins : ClauseKinds.HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks site ins tc te) J) :
    TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks' site ins tc te) J := by
  cases h with
  | effHandleV hAt hs hm hd hH hc hn0 hnS hlen hdv he hins =>
      exact .effHandleV hAt hs hm hd hH hc hn0 hnS hlen hdv he hins

/-- **The site is the elaboration's, not the derivation's**: a typed derivation of a `handle`
node is one at any site record. -/
theorem TDerivesAt.site_free {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : TInfo} {J : Jdg}
    {S : Row} {E : List (Count × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite} (site' : Option HSite)
    {ins : ClauseKinds.HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks site ins tc te) J) :
    TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks site' ins tc te) J := by
  cases h with
  | effHandleV hAt hs hm hd hH hc hn0 hnS hlen hdv he hins =>
      exact .effHandleV hAt hs hm hd hH hc hn0 hnS hlen hdv he hins


/-! ### A bound for each node, stated -/

open BoCa.Fig16.LogRel.Core.ClauseKinds in
/-- **What may flow from a term when only a handler of the names `st` lets its handled
computation's frames flow**: `Expr.fl`, with a handled computation's frames counted at a name of
`st`, and only what flows from it at any other.  `[spec §19]` -/
def flKept (st : List UInt32) : Expr → HIn
  | .var _ | .unit | .loc _ => {}
  | .prim p => primHin p
  | .lam b => b.hin
  | .pair a b | .seq a b | .letpair a b => flKept st a ++ flKept st b
  | .case a b c => flKept st a ++ flKept st b ++ flKept st c
  | .inj₁ a | .inj₂ a => flKept st a
  | .app f x => match f with
      | .lam b => flKept st b ++ flKept st x
      | .prim .hnd => match x with
          | .pair (.prim (.lit (.i32 _))) X => flKept st X
          | x => HIn.top ++ flKept st x
      | .app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) X) =>
          flKept st X ++ (if st.contains n then x.hin else flKept st x)
      | .app (.prim .ubind) N => flKept st N ++ flKept st x
      | .app (.prim .cfin) s => flKept st s ++ flKept st x
      | .prim .ccatch => flKept st x
      | f => flKept st f ++ flKept st x

end BoCa.Fig16.LogRel.Core.Check

namespace Frontend.Check
open BoCa BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa.Fig16.LogRel.Core.Check

/-- The names of `main`'s `handle` nodes one of whose clauses may keep `κ` (`stored`). -/
def Checked.storing (c : Checked) : List UInt32 :=
  ((c.t.handleSites copiesFuel).filter fun h => h.ks.any (·.kind == .stored)).map (·.n)

/-- **What may flow in a run of `main` when only a clause that may keep `κ` lets its handled
computation's frames flow**: `flKept` at the storing names, the names performed of a storing
handler (a continuation captured at one of the others never leaves its clause), `Div`'s and
`0`.  `[spec §19]` -/
def Checked.flowsKept (c : Checked) : HIn :=
  flKept c.storing c.e ++ ⟨c.e.pn.names.filter c.storing.contains, false, c.e.pn.any⟩ ++
    HIn.one divEff ++ HIn.one 0

/-- The frames `inside` records at `main`'s `handle` nodes of the name `n`. -/
def Checked.insideOf (c : Checked) (n : UInt32) : HIn :=
  ((c.t.handleSites copiesFuel).filter (·.n == n)).foldl (fun a h => a ++ h.inside) {}

/-- **A bound for each node, stated, not proved**  `[spec §19]`: in every run of `main` from the
empty memory, the frames under a handler frame of the name `n`, between it and the operation its
context is filled by, are within the `inside` of the nodes of the name, the name `0`, and, where
`codeIn n` (code may flow into the handled computation), `flowsKept`. At `codeIn := fun _ => true`
it is what a clause that keeps no `κ` never letting `κ` leave it gives; at `codeIn n` false for a
name whose handled computations take in no code at a type with a `U`, it is what the typing
invariant of the run (a value of a type with no `U` holds no code) gives. -/
def Checked.FramesPerNode (c : Checked) (codeIn : UInt32 → Bool) : Prop :=
  ∀ {ℍ : BoCa.Host} [BoCa.HostIs ℍ] {μ : BoLo.Heap} {e : BoCa.Expr},
    BoLo.Steps (ℍ := ℍ) BoCa.Adequacy.emptyMem c.e μ e →
    ∀ {K₀ K : BoLo.Kont} {n : UInt32} {qs hr hs : BoCa.Val} {p : BoCa.Expr},
      e = K₀.plug (BoLo.hndE (BoLo.hndVal n qs hr hs) (K.plug p)) →
      (K.plug p).hin ≤ c.insideOf n ++ HIn.one 0 ++ (if codeIn n then c.flowsKept else {})

/-- **Condition 2 at a bound for each node**: where `FramesPerNode` holds, names none of which
the node's bound may catch are unhandled in `K`.  `[spec §19]` -/
theorem Checked.unhandledNames_perNode (c : Checked) {codeIn : UInt32 → Bool}
    (hb : c.FramesPerNode codeIn) {ℍ : BoCa.Host} [BoCa.HostIs ℍ] {μ : BoLo.Heap} {e : BoCa.Expr}
    (h : BoLo.Steps (ℍ := ℍ) BoCa.Adequacy.emptyMem c.e μ e) {K₀ K : BoLo.Kont} {n : UInt32}
    {qs hr hs : BoCa.Val} {p : BoCa.Expr} (he : e = K₀.plug (BoLo.hndE (BoLo.hndVal n qs hr hs) (K.plug p)))
    {ns : List UInt32}
    (hS : cond2B (c.insideOf n ++ HIn.one 0 ++ (if codeIn n then c.flowsKept else {})) ns = true) :
    UnhandledNames ns K := by
  have hx := hb h he
  intro m hm
  cases hc : K.Catches m
  · rfl
  · exact absurd (HIn.Catches.mono hx (catches_hin p hc)) (cond2B_names_sound hS m hm)

end Frontend.Check
