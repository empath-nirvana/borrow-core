/-
The plain-path probe of the #669 hard cases (experiments only; the library never imports it).

For a program, it runs the new backend's conversion (`Backend2.lirOf`) and reports which of the
conversion's GLOBAL pieces (#670's report) ran:
- `machines`: state machines converted (§49); with none, `lirOf` returns before `tailPass`,
  `cellPass`, `threadedOf` and `stackedOf` (`Backend2/Driver.lean`, `lirOf`);
- `tailSites`: the call sites `tailPass` would read;
- `merged`: the task variants `genMerges` merges (§49 *One code per task body*);
- `threaded`/`stacked`: the second run's machines (§50 cells passed on, §52 task stacks);
- `statics`: the static cells (`cellPass`'s state cells and the stack register);
- `effectOps`: the LIR's operations of the effect layer (stack, frame, κ region, static cell);
- `reads`: the facts the conversion read, by key.

    lake env lean --run experiments/core-hard-cases/PlainPath.lean <file.bc>…
-/
import Backend2.Driver

open Backend2

def opsOf : Tm → List String
  | .prim op _ => match op with
    | .stackSwap _ => ["stackSwap"] | .stackFree => ["stackFree"] | .stackNew _ => ["stackNew"]
    | .kappaPut _ => ["kappaPut"] | .kappaTake _ => ["kappaTake"]
    | .framePush _ _ => ["framePush"] | .frameTop _ _ => ["frameTop"] | .framePut => ["framePut"]
    | .framePop _ => ["framePop"] | .staticCell _ => ["staticCell"] | .unreachable => ["unreachable"]
    | _ => []
  | .letv _ e b => opsOf e ++ opsOf b
  | .letpair _ _ _ b => opsOf b
  | .case _ _ b₁ _ b₂ => opsOf b₁ ++ opsOf b₂
  | .copy _ _ b => opsOf b
  | .drop _ b => opsOf b
  | _ => []

def main (args : List String) : IO UInt32 := do
  for file in args do
    let src ← IO.FS.readFile file
    match Backend.checkedOf file src with
    | .error e => IO.println s!"{file}: {e}"
    | .ok k =>
      match lirOf k with
      | .error e => IO.println s!"{file}: lir: {e}"
      | .ok (p, st) =>
        let ops := (p.fns.toList.flatMap fun f => opsOf f.body).eraseDups
        let reads := st.reads.toList.map (fun (k, n) => s!"{k}×{n}") |>.toArray.qsort (· < ·)
        IO.println s!"{file}:\n  machines {st.done.size} tailSites {st.tailSites.size} merged {st.merged.size} threaded {st.threaded.size} stacked {st.stacked.size} statics {st.statics.size}\n  effectOps {ops}\n  reads {reads.toList}"
  return 0
