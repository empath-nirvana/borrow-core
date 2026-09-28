import Backend.Driver

/-!
# Backend — `bcc-counts`

    lake exe bcc-counts <file>
    lake exe bcc-counts --sites <file>

Run the program at the flat IR (`Backend/Flat/Interp.lean`) and under `wasmtime`, each built to
count, and print `allocs N indirect M`: the objects the run allocates and the indirect calls it
makes. The two stages must agree. A program that declares `stdin` reads all of standard input
first and gives it to both. `scripts/compile-corpus.sh` compares the counts with
`corpus/counts.expected`. An indirect call is a dispatched one: a closure call whose code a
`switch` on the closure's tag chooses at run time.

With `--sites`, print the program's closure calls instead (`Flat.callSites`): how many there
are, how many are direct because their type's union has one code, how many more because the flow
analysis finds one code, and the recursive closure types, which keep heap environments, with the
number of codes in each union.
-/

/-- All of standard input, read in at most `fuel` chunks of 64 KiB. -/
def readAllIn (h : IO.FS.Stream) : Nat → ByteArray → IO ByteArray
  | 0, _ => throw (IO.userError "standard input is too long")
  | n + 1, acc => do
    let b ← h.read 65536
    if b.isEmpty then return acc else readAllIn h n (acc ++ b)

/-- The counts a counting run writes after its report: its last two lines. -/
def countsOf (out : String) : Option (String × String) :=
  match (out.splitOn "\n").reverse with
  | "" :: i :: a :: _ =>
    if a.startsWith "allocs " && i.startsWith "indirect " then
      some ((a.drop 7).toString, (i.drop 9).toString)
    else none
  | _ => none

/-- The call-site report of `--sites`. -/
def sites (file src : String) : Except String String := do
  let p ← Backend.closOf file src
  let (n, ty, fl) ← Backend.Flat.callSites p
  let T ← p.types
  let recs := T.recFn.toList.map fun t => (T.union t).size
  pure s!"calls {n} direct {ty + fl} (union {ty}, flow {fl}) dispatched {n - ty - fl} recursive-types {recs.length} {recs}"

def main (argv : List String) : IO UInt32 := do
  if let ["--sites", file] := argv then
    match sites file (← IO.FS.readFile file) with
    | .ok s => IO.println s; return 0
    | .error e => IO.eprintln e; return 1
  let [file] := argv | IO.eprintln "usage: bcc-counts [--sites] <file>"; return 2
  let src ← IO.FS.readFile file
  let input ← if Backend.readsInput file src then readAllIn (← IO.getStdin) (1 <<< 16) .empty
    else pure .empty
  let flat ← match Backend.interpStage "flat-counts" file src input.toList with
    | .ok o => pure (String.fromUTF8! o.out)
    | .error e => IO.eprintln e; return 1
  let wat ← match Backend.compileWat file src true with
    | .ok w => pure w
    | .error e => IO.eprintln e; return 1
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "main.wat") wat
  IO.FS.writeBinFile (dir / "in") input
  let r ← IO.Process.output
    { cmd := "sh",
      args := #["-c", s!"wasmtime run -W tail-call=y '{dir / "main.wat"}' < '{dir / "in"}'"] }
  IO.FS.removeDirAll dir
  match countsOf flat, countsOf r.stdout with
  | some (a, i), some (a', i') =>
    if a == a' && i == i' then
      IO.println s!"allocs {a} indirect {i}"; return 0
    else
      IO.eprintln s!"{file}: the flat IR counts allocs {a} indirect {i}, wasm allocs {a'} indirect {i'}"
      return 1
  | none, _ => IO.eprintln s!"{file}: the flat IR wrote no counts"; return 1
  | _, none => IO.eprintln s!"{file}: wasm wrote no counts: {r.stderr}"; return 1
