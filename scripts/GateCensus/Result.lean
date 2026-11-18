import Lean

namespace GateCensus

/-- What a census prints, and its exit status. -/
structure Result where
  lines : Array String := #[]
  code : UInt32 := 0

def Result.text (r : Result) : String :=
  String.join (r.lines.toList.map (· ++ "\n"))

end GateCensus
