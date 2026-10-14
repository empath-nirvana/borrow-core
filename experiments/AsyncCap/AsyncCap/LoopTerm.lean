import Frontend.Check.CrossCheck
import AsyncCap.Derives

/-!
# AsyncCap — R2's term is the checked library code

`lendLoopE C` (`Derives.lean`) is written out by hand. Here it is checked against `bcc`'s
erasure of `lend_loop_imm` and `lend_loop_mut` in `experiments/AsyncCap/bc/lend-loop-term.bc`,
both at `A = i32`, `B = i32`, `R = 1`: the two combinators erase to the same term, and it is
`lendLoopE` at that loop body. The file's `main` drives both loops (`bcc interp`: `i32[2113]`,
`live 0`). The erasure depends on the loop body only through `unfold`'s `C`, which `lendLoopE`
takes as its argument; the state type `S` is not part of the term.
-/

namespace BoCa.Fig16.LogRel.Core.AsyncCap
open BoCa
open Frontend.Check (defErasure)

/-- `experiments/AsyncCap/bc/lend-loop-term.bc`. -/
def lendLoopP : Frontend.Program := bcc_program% "experiments/AsyncCap/bc/lend-loop-term.bc"

set_option maxRecDepth 100000 in
/-- `lend_loop_imm` (declaration 7) and `lend_loop_mut` (declaration 8) erase to `lendLoopE` at
`F((Ref i32 ⊗ i32) ⊕ X) & F (Ref i32 ⊗ 1)`. -/
theorem lendLoopE_is_checked :
    defErasure lendLoopP 7 = some (lendLoopE (lendLoopBody (.int .w32) (.int .w32) .unit)) ∧
    defErasure lendLoopP 8 = some (lendLoopE (lendLoopBody (.int .w32) (.int .w32) .unit)) := by
  decide +kernel

end BoCa.Fig16.LogRel.Core.AsyncCap
