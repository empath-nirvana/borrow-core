import PoolSpike.Machine
import PoolSpike.Inv
import PoolSpike.Seg
import PoolSpike.Adequacy
import PoolSpike.NonVacuity

/-!
# Pool spike (#781): does the cactus invariant carry multi-branch safety when it sees the tasks?

A throwaway spike, not for merging. No `sorry`, `axiom`, `native_decide`, `opaque`, `partial`,
`unsafe`.

The machine holds the tasks (`PoolSpike/Machine.lean`): the memory, at most one active branch, and
a pool of ready and parked branches; any branch may be started or resumed, so every schedule of
segments is a run. The invariant is over every branch, parked ones included
(`PoolSpike/Adequacy.lean`'s `Inv`): `CInv` (`CactusInvT` without its points), `PoolEsc`
(`FdEsc` between every two branches), and each branch's certificate.

**What is proved.** `poolAdequacy`: closed programs verified at `cerwpT (opTableP T)`, run under any
schedule, reach only configurations that step or are final at the empty memory, and every `free`
finds its cell. Through preservation: `seg` (a segment, every other branch re-read, R1 for the
others' records), `park_inv`, `done_inv`, `resume_inv`, `start_inv`. A parked branch is resumed
after any number of other segments from its certificate alone; the records of the stop list it is
relevant to are kept by every segment of another branch (`seg`'s `KeepRel`), from `PoolEsc` and
`TIT`'s closure. `nonvac`: the premises at a two-branch pool, and a run that parks, runs the other
branch, and resumes.

**What is changed.** The tasks' table is `opTableP`, whose share `contShareP` asks the resume list
for the re-read records the share is relevant to (`KeepRel`). Core's `contShareT` asks for a
re-reading of the whole stop list (`SRecsRR`) and `extFT` against it. `contShareP` is the stronger
promise (`contShareP_contShareT`). With `contShareT`, `extFT` follows from the certificate
(`extFT_of_keepRel`), and the resume goes through given a re-reading of the stop list
(`resume_core`); that re-reading is not derived. `EndT` re-reads the frame's records proper, not
the records of the branch that ran, which it may end, free and re-type. No obstruction is
verified.

**What is not covered.** A parked branch holding a view of a lend: no program rule at `twp` opens
or ends a lend, so no such branch is verified here. The table's `fd` is trivial (`TabOK`): the
join's guarantee nests through `fdAt` at the records owned at earlier resumes, which this spike
does not read.
-/
