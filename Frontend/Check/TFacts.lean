import Frontend.Check.TDerives

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
  the bound and that
  below its length a view's read answers a leaf. That the step reads, at the step's index, the
  view the bound was taken from is the scheme's: `forData` threads the view in the loop's state
  and reads it there. A lemma over the step's reduction (the state's view component handed on
  unchanged by every tail of the step) would pin it.
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

A fourth is a field the checker adds to a node and its typed rule pins:

* **The frames inside a handled computation at `[handle]`** (`inside`,
  `Frontend/Check/Handled.lean`): the typed rule's premise `inside = te.erase.hin`
  (`TDerivesAt.inside_eq`, `TDerivesP.inside_eq`, and at `effHandleVB` and `effHandleT`). It is
  the frames the handled computation holds as written, through `use` bodies and a recursive
  group's generator. It is not a bound on the frames a run puts between a `perform` and the
  handler: code that flows into the handled computation puts frames there too (a closure bound
  outside it, a continuation captured at another handler and resumed inside, a value read from
  memory). The bound the theorem reads is the program's (`Checked.flows`), which holds all such
  code at once, and so every node's `inside`. A bound per node would be pinned by a bound on the
  code that flows into the handled computation: an invariant of the run, from the typing, that a
  value of a type with no `U` holds no code, so that only the handled computation's free
  variables, its operations' answers and the cells it reads at types with a `U` bring code in;
  and that a clause whose kind keeps no `κ` (`tail`, `tail+state`, `resume-or-cancel`, `once`)
  never lets its `κ` leave the clause, so that only a site whose clause stores `κ` adds its
  handled computation's frames to what flows.

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
    {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
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
    {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {u : Masks} {ks : List ClauseKinds.HKind} {site : Option HSite} (site' : Option HSite)
    {ins : ClauseKinds.HIn} {tc te : TExpr}
    (h : TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks site ins tc te) J) :
    TDerivesAt Ξ Δ Γ (.effHandleV i J S E fs n A R u ks site' ins tc te) J := by
  cases h with
  | effHandleV hAt hs hm hd hH hc hn0 hnS hlen hdv he hins =>
      exact .effHandleV hAt hs hm hd hH hc hn0 hnS hlen hdv he hins

end BoCa.Fig16.LogRel.Core.Check
