import Backend.Driver

/-!
# Backend — `bcc-counts`

    lake exe bcc-counts <file> [-- arg…]
    lake exe bcc-counts --sites <file>
    lake exe bcc-counts --kernel [--sites] <name>
    lake exe bcc-counts --native <file> [-- arg…]

Run the program at the flat IR (`Backend/Flat/Interp.lean`) and under `wasmtime`, each built to
count, and print `allocs N indirect M copies K`: the objects the run allocates, the indirect calls
it makes, and the copies of a variable at a non-trivial type it makes. The two stages must agree. A program that declares `stdin` reads all of standard input
first and gives it to both, and the words after `--` are the program's arguments at both
(SPEC §34). `scripts/compile-corpus.sh` compares the counts with
`corpus/counts.expected`. An indirect call is a dispatched one: a closure call whose code a
`switch` on the closure's tag chooses at run time. A copy is one that the ownership discipline
inserts where a variable is used by two sequential parts (`Backend/README.md`, Memory discipline)
at a type whose copy is not the words themselves: each is a deep copy that allocates.

With `--sites`, print the program's closure calls instead (`Flat.callSites`): how many there
are, how many are direct because their type's union has one code, how many more because the flow
analysis finds one code, the recursive closure types, which keep heap environments, with the
number of codes in each union, the owned folds compiled by pointer reversal and those that
recurse, and the scoped cells (`Backend/Flat/Lower.lean`, `frameScopes`) placed in frame slots
and those allocated.

With `--native`, the second run is the native build (`bcc run --native`, SPEC §40) instead of
`wasmtime`'s, and the two must agree on the counts and the exit status.

With `--kernel`, the program is the kernel program `name` (`Backend/Kernel.lean`).
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

/-- The call-site report of `--sites`. -/
def sites (file src : String) : Except String String := do
  let p ← Backend.closOf file src
  let (n, ty, fl) ← Backend.Flat.callSites p
  let T ← p.types
  let recs := T.recFn.toList.map fun t => (T.union t).size
  let (rev, rc) ← Backend.Flat.foldSites p
  let (sf, sa) := Backend.Flat.scopeSites p
  pure (s!"calls {n} direct {ty + fl} (union {ty}, flow {fl}) dispatched {n - ty - fl} " ++
    s!"recursive-types {recs.length} {recs} owned-folds reversed {rev} recursive {rc} " ++
    s!"scoped-cells framed {sf} allocated {sa}")

/-- The call-site report of `--sites` for a closure-IR program. -/
def sitesOfProg (p : Backend.Clos.Prog) : Except String String := do
  let (n, ty, fl) ← Backend.Flat.callSites p
  let T ← p.types
  let recs := T.recFn.toList.map fun t => (T.union t).size
  let (rev, rc) ← Backend.Flat.foldSites p
  let (sf, sa) := Backend.Flat.scopeSites p
  pure (s!"calls {n} direct {ty + fl} (union {ty}, flow {fl}) dispatched {n - ty - fl} " ++
    s!"recursive-types {recs.length} {recs} owned-folds reversed {rev} recursive {rc} " ++
    s!"scoped-cells framed {sf} allocated {sa}")

/-- `bcc-counts --kernel [--sites] <name>`. -/
def kernelMain (sitesOnly : Bool) (name : String) : IO UInt32 := do
  let some e := (Backend.kernelPrograms.lookup name) |
    IO.eprintln s!"no kernel program `{name}`"; return 1
  if sitesOnly then
    match Backend.closTypesOfExpr e >>= fun (p, _) => sitesOfProg p with
    | .ok s => IO.println s; return 0
    | .error err => IO.eprintln err; return 1
  let flat ← match Backend.interpStageExpr "flat-counts" e with
    | .ok o => pure (String.fromUTF8! o.out)
    | .error err => IO.eprintln err; return 1
  let wat ← match Backend.compileWatExpr e true with
    | .ok w => pure w
    | .error err => IO.eprintln err; return 1
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "main.wat") wat
  let r ← IO.Process.output
    { cmd := "wasmtime", args := Backend.wasmtimeArgs.push (dir / "main.wat").toString }
  IO.FS.removeDirAll dir
  match countsOf flat, countsOf r.stdout with
  | some (a, i, c), some (a', i', c') =>
    if a == a' && i == i' && c == c' then
      IO.println s!"allocs {a} indirect {i} copies {c}"; return 0
    else
      IO.eprintln (s!"{name}: the flat IR counts allocs {a} indirect {i} copies {c}, " ++
        s!"wasm allocs {a'} indirect {i'} copies {c'}")
      return 1
  | _, _ => IO.eprintln s!"{name}: no counts"; return 1

/-- `bcc-counts --native <file>`: the flat IR's counts against the native build's.  `[spec §40]` -/
def nativeMain (file : String) (args : List String) : IO UInt32 := do
  let src ← IO.FS.readFile file
  let input ← if Backend.readsInput file src then readAllIn (← IO.getStdin) (1 <<< 16) .empty
    else pure .empty
  let (flat, status) ← match Backend.interpStage "flat-counts" file src input.toList (Backend.argsBytes args) with
    | .ok o => pure (String.fromUTF8! o.out, o.status)
    | .error e => IO.eprintln e; return 1
  let ll ← match Backend.compileLL file src true with
    | .ok w => pure w
    | .error e => IO.eprintln e; return 1
  let dir ← IO.FS.createTempDir
  let exe ← match ← Backend.buildNative ll dir with
    | .ok exe => pure exe
    | .error e => IO.FS.removeDirAll dir; IO.eprintln s!"{file}: {e}"; return 1
  IO.FS.writeBinFile (dir / "in") input
  let r ← IO.Process.output
    { cmd := "sh",
      args := #["-c", s!"'{exe}'" ++
        String.join (args.map fun a => " '" ++ a.replace "'" "'\\''" ++ "'") ++ s!" < '{dir / "in"}'"] }
  IO.FS.removeDirAll dir
  if r.exitCode != status then
    IO.eprintln s!"{file}: the flat IR exits with status {status}, native with {r.exitCode}"
    return 1
  match countsOf flat, countsOf r.stdout with
  | some (a, i, c), some (a', i', c') =>
    if a == a' && i == i' && c == c' then
      IO.println s!"allocs {a} indirect {i} copies {c}"; return 0
    else
      IO.eprintln (s!"{file}: the flat IR counts allocs {a} indirect {i} copies {c}, " ++
        s!"native allocs {a'} indirect {i'} copies {c'}")
      return 1
  | none, _ => IO.eprintln s!"{file}: the flat IR wrote no counts"; return 1
  | _, none => IO.eprintln s!"{file}: native wrote no counts: {r.stderr}"; return 1

def main (argv : List String) : IO UInt32 := do
  if let "--native" :: file :: rest := argv then
    match rest with
    | [] => return ← nativeMain file []
    | "--" :: args => return ← nativeMain file args
    | _ => IO.eprintln "usage: bcc-counts --native <file> [-- arg…]"; return 2
  if let ["--kernel", name] := argv then return ← kernelMain false name
  if let ["--kernel", "--sites", name] := argv then return ← kernelMain true name
  if let ["--sites", file] := argv then
    match sites file (← IO.FS.readFile file) with
    | .ok s => IO.println s; return 0
    | .error e => IO.eprintln e; return 1
  let (file, args) ← match argv with
    | [file] => pure (file, [])
    | file :: "--" :: args => pure (file, args)
    | _ => do IO.eprintln "usage: bcc-counts [--sites] <file> [-- arg…]"; return 2
  let src ← IO.FS.readFile file
  let input ← if Backend.readsInput file src then readAllIn (← IO.getStdin) (1 <<< 16) .empty
    else pure .empty
  let (flat, status) ← match Backend.interpStage "flat-counts" file src input.toList (Backend.argsBytes args) with
    | .ok o => pure (String.fromUTF8! o.out, o.status)
    | .error e => IO.eprintln e; return 1
  let wat ← match Backend.compileWat file src true with
    | .ok w => pure w
    | .error e => IO.eprintln e; return 1
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "main.wat") wat
  IO.FS.writeBinFile (dir / "in") input
  let r ← IO.Process.output
    { cmd := "sh",
      args := #["-c", s!"wasmtime {" ".intercalate Backend.wasmtimeArgs.toList} '{dir / "main.wat"}'" ++
        String.join (args.map fun a => " '" ++ a.replace "'" "'\\''" ++ "'") ++ s!" < '{dir / "in"}'"] }
  IO.FS.removeDirAll dir
  -- The two stages end with one exit status (SPEC §39).
  if r.exitCode != status then
    IO.eprintln s!"{file}: the flat IR exits with status {status}, wasm with {r.exitCode}"
    return 1
  match countsOf flat, countsOf r.stdout with
  | some (a, i, c), some (a', i', c') =>
    if a == a' && i == i' && c == c' then
      IO.println s!"allocs {a} indirect {i} copies {c}"; return 0
    else
      IO.eprintln (s!"{file}: the flat IR counts allocs {a} indirect {i} copies {c}, " ++
        s!"wasm allocs {a'} indirect {i'} copies {c'}")
      return 1
  | none, _ => IO.eprintln s!"{file}: the flat IR wrote no counts"; return 1
  | _, none => IO.eprintln s!"{file}: wasm wrote no counts: {r.stderr}"; return 1
