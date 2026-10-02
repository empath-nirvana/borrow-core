import EffModel.Laws
import EffModel.Refusals

/-!
# EffModel — the acceptance tests

Every `#guard` below is checked when the library builds. The `#eval`s print the matrix.
-/

namespace EffModel

/-! ## 1. Laws -/

-- Every law: in every typed context, it holds exactly where it should; and some context types.
#guard lawResults.all LawResult.ok

-- The suite's size: contexts generated, and contexts in which both sides type.
#guard (lawResults.map (·.contexts)).sum == 952
#guard (lawResults.map (·.typed)).sum == 878

-- Sum versus tensor, pinned: absorption holds in exactly the 8 typed contexts where `Fail` is
-- outside a writer `Log`; two printing `Log`s are the 8 non-commuting contexts of 72; lent state is
-- never absorbed.
#guard (checkLaw (logFail[0]!)).holds == 8 && (checkLaw (logFail[0]!)).typed == 40
#guard (checkLaw (commuting[1]!)).holds == 64 && (checkLaw (commuting[1]!)).typed == 72
#guard (checkLaw (commuting[2]!)).holds == 0 && (checkLaw (commuting[2]!)).typed == 8

/-! ## 2. Programs -/

#guard programs.all (fun p => p.typed && p.runsAsExpected)

/-! ## 3. Refusals -/

#guard refusals.all (fun r => r.refused && r.controlOK)

-- T1 is the only rule refusing `t1Lend`, `t1Callback` and `t1Harm`; without it `t1Harm` types,
-- and its run resumes inside a lend whose owner has consumed the capability.
#guard acceptsWithoutT1 sigs t1Lend && acceptsWithoutT1 sigs t1Callback
#guard acceptsWithoutT1 sigs t1Harm && !accepts sigs t1Harm
#guard run sigs t1Harm == ⟨.stuck "a lent capability used after its owner consumed it", [], []⟩

-- Untyped runs of the other refusals show what each rule prevents.
#guard run sigs multiLinear == ⟨.stuck "a capability consumed twice", [], []⟩
#guard run sigs noDtorAbort == ⟨.ret "0", [], ["1 live capabilities"]⟩
#guard run sigs noDtor == ⟨.ret "inr ()", [.out 1], ["1 live capabilities"]⟩

/-! ## The matrix -/

def mark (b : Bool) : String := if b then "pass" else "FAIL"

def lawRow (r : LawResult) : String :=
  s!"| {r.name} | {r.contexts} | {r.typed} | {r.holds} | {mark r.ok} |"

def progRow (p : Prog) : String :=
  s!"| {p.name} | {mark p.typed} | {mark p.runsAsExpected} |"

def refRow (r : Refusal) : String :=
  s!"| {r.name} | {mark r.refused} | {rejection sigs r.rejected} | {mark r.controlOK} |"

def matrix : String :=
  String.intercalate "\n" (
    ["| law | contexts | typed | holds | verdict |", "|---|---|---|---|---|"] ++
    lawResults.map lawRow ++
    ["", "| program | typed | runs as expected |", "|---|---|---|"] ++
    programs.map progRow ++
    ["", "| refusal | refused | rule | control |", "|---|---|---|---|"] ++
    refusals.map refRow)

#eval IO.println matrix

end EffModel
