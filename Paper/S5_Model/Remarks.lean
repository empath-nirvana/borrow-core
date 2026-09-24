import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Support.Model.Propositions

/-!
# [TR] §5 Model — remarks on the definitions

Row 5.62's `wp_eq_wpU`, and the records of rows 5.56 and 5.67, whose theorems
are declared in §6's files.  Theorems about definition rows whose proofs use
`[TR]` §6.
-/

noncomputable section

/-!
### 5.56 · `⨀` — the iterated composition, with no printed empty case · [TR] p. 5, rows 11, 12, 19 · `[repair]`

The empty case is printed nowhere.  `BoCa.Fig16.BigComp.perm` (declared in
`Paper/S6_1_StandardLemmas/Lemmas.lean`) proves the fold order-independent from
`[TR]` Lemmas 6.1–6.3.
-/

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 5.62 · — [CONF] Fig. 18b's unguarded ↭, and the `wp` row read at it — · not in [TR] §5 · `[repair]`

[CONF] Fig. 18b's unguarded `↭`, kept beside [TR]'s; `wp_eq_wpU` proves the two
readings give the same `wp` (`docs/adjudications.md` D3).
-/
/-- The two readings of `↭` give the same `wp`.  `[about ours]` -/
theorem wp_eq_wpU (e : Expr) (Q : Val → WProp) : wp e Q = wpU e Q :=
  funext fun ρ => propext (wp_updV_iff_upd e Q ρ)

end BoCa.Fig16.BoLo

/-!
### 5.67 · — [CONF] §4.3's characterisation of `✓`: *"in a valid resource, every pair of aliases map to the same object and each has an immutable ancestor"*, and *"aliasing of exclusive locations … not guarded by immutable cells … violates the mutability-xor-aliasing restriction"* — · [CONF] p. 415:21, not in [TR] §5 · `[as printed]`

Prose characterising `✓ρ ≜ ⦇ρ⦈ defined` (row 5.23); [CONF] p. 415:21: *"the
advantage of reusing composition is that it already rules out all of the
inconsistent aliasing cases"*.  The clauses are theorems: *same object* is
`CellU.compatR_iff` (with `CellU.CompatS.imm_imm` at `●`); *an immutable ancestor*
is `AgW.nonimm_beneath_imm` with `ExW.immFree` (6.36); *no cell both exclusive and
aliasable* is `ResU.CompatS.disjoint_of_immFree` and `ResU.flat_eq_ag_at`
(`docs/adjudications.md` §12.52).  They are declared in the §6.1 and §6.2 files.
-/

end
