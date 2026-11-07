/-!
# Pipeline — the counting runs' helpers

What `bcc-counts` (`Backend/Counts.lean`) reads with either backend: all of standard input, and
the counts a counting build writes after its report.
-/

/-- All of standard input, read in at most `fuel` chunks of 64 KiB. -/
def readAllIn (h : IO.FS.Stream) : Nat → ByteArray → IO ByteArray
  | 0, _ => throw (IO.userError "standard input is too long")
  | n + 1, acc => do
    let b ← h.read 65536
    if b.isEmpty then return acc else readAllIn h n (acc ++ b)

/-- The counts a counting run writes after its report: its last three lines. -/
def countsOf (out : String) : Option (String × String × String) :=
  match (out.splitOn "\n").reverse with
  | "" :: c :: i :: a :: _ =>
    if a.startsWith "allocs " && i.startsWith "indirect " && c.startsWith "copies " then
      some ((a.drop 7).toString, (i.drop 9).toString, (c.drop 7).toString)
    else none
  | _ => none
