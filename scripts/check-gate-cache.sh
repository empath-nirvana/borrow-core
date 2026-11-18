#!/usr/bin/env bash
# The gate's result cache (scripts/gate_cache.py) misses whenever an input of a unit changes, and
# never records a failure. On a copy of the tree's scripts, library, tables, binaries and a few
# corpus programs, with a cache of its own (`GATE_CACHE_DIR` in a scratch directory), it runs
# `compile-backend2.sh --final` on the programs twice (the second run replays every unit), then
# changes one input of each kind in turn and shows that the unit it reaches runs again:
#
#   the program's text; each sidecar (`.in`, `.args`, `.out`, `.err`, `.status`, `.key`); the
#   golden; its row in a corpus table; a library module; a script; the binary (a byte appended to
#   the copy `bcc` names); a tool's version (a `wasmtime` on PATH that reports another); an
#   environment variable (`BC_*`, `BCC_*`); and the mode (`--final` dropped). `GATE_CACHE=record`
#   runs every unit and records; `GATE_CACHE=0` runs every unit and writes nothing.
#
# Each change is undone after its run, and the next run replays again. A unit that fails (its
# golden changed so that it differs) runs, fails, and fails again on the next run: no failure is
# recorded. A whole step's key (`gate_cache.py step-key`) changes with a `.lean` file, a new
# `.lean` file, the lakefile, the manifest and the toolchain, and with a file it names; a unit
# whose input changes while it runs is not recorded. par records neither a unit that calls
# `par_nostore` nor one whose input changed, even and back, while it ran; an entry without its side
# files, or whose files do not match its checksum, is a miss; stale binaries (no build in this
# invocation) are never looked up; an unknown `GATE_CACHE` is refused; an unwritable store is reported. The tree's
# own files are only read.
#
#     scripts/check-gate-cache.sh
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
export GATE_CACHE_BUILT=1  # the binaries the result cache may key on are this build's
# Itself one unit of the result cache (scripts/gate_cache.py `step`): a recorded pass is replayed
# when the binaries, the library, the Lean sources, Lake's configuration, scripts/, the tools and
# the files it copies are as they were.
[ "${GATE_CACHE_INNER:-}" = check-gate-cache ] || exec python3 scripts/gate_cache.py step check-gate-cache bcc,lean \
  --files corpus/io-args.* corpus/ascii-upper.* corpus/*.expected -- scripts/check-gate-cache.sh "$@"
[ -x .lake/build/bin/bcc ] && [ -x .lake/build/bin/bcc-counts ] || { echo "check-gate-cache: build bcc and bcc-counts first"; exit 1; }
command -v wasmtime >/dev/null || { echo "check-gate-cache: wasmtime is not on PATH"; exit 1; }
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
w=$t/tree
mkdir -p "$w/corpus" "$w/.lake/build/bin" "$t/bin"
cp -R scripts lib Makefile "$w/"
cp corpus/*.expected "$w/corpus/"
progs=(io-args ascii-upper)
for p in "${progs[@]}"; do cp corpus/"$p".* "$w/corpus/"; done
for b in bcc bcc-counts; do cp -c .lake/build/bin/$b "$w/.lake/build/bin/$b" 2>/dev/null || cp .lake/build/bin/$b "$w/.lake/build/bin/$b"; done
files=(); for p in "${progs[@]}"; do files+=("corpus/$p.bc"); done
unset GATE_CACHE GATE_CACHE_BUILT GATE_CACHE_TOOLS_FILE GATE_CACHE_INNER GATE_CACHE_STATS PAR_CACHE PAR_CACHE_DEPS PAR_COLLECT
for v in $(env | sed -n 's/^\(BC_[A-Za-z0-9_]*\|BCC_[A-Za-z0-9_]*\|CI_LOCAL_[A-Za-z0-9_]*\)=.*/\1/p'); do unset "$v"; done
export GATE_CACHE_DIR=$t/store CI_LOCAL_BUILT=1
bad=0

# run [ARG…]: compile-backend2.sh on the programs in the copy; sets `replayed`, `ran` and `rc`.
run() {
  : > "$t/stats"
  rc=0
  GATE_CACHE_STATS=$t/stats "$w/scripts/compile-backend2.sh" "$@" "${files[@]}" > "$t/out" 2>&1 || rc=$?
  replayed=$(awk '{ s += $1 } END { print s + 0 }' "$t/stats")
  ran=$(awk '{ s += $2 } END { print s + 0 }' "$t/stats")
}
# expect WHAT REPLAYED RAN RC [ARG…]: one run, with these counts and exit status (`-`: any).
expect() {
  local what=$1 r=$2 n=$3 c=$4; shift 4
  run "$@"
  if [ "$replayed" = "$r" ] && [ "$ran" = "$n" ] && { [ "$c" = - ] || [ "$rc" = "$c" ]; }; then
    echo "check-gate-cache: $what: $replayed replayed, $ran run, exit $rc"
  else
    echo "check-gate-cache: $what: $replayed replayed, $ran run, exit $rc; expected $r replayed, $n run, exit $c"
    sed 's/^/  /' "$t/out"; bad=1
  fi
}
# change WHAT FILE CMD…: run CMD (which changes FILE in the copy), expect the unit of FILE's
# program to run and the other to replay, undo the change, and expect every unit to replay.
change() {
  local what=$1 f=$w/$2; shift 2
  local had=0; [ -e "$f" ] && { had=1; cp -p "$f" "$t/saved"; }
  "$@" "$f"
  expect "$what" 1 1 - --final
  if [ "$had" = 1 ]; then cp -p "$t/saved" "$f"; else rm -f "$f"; fi
  expect "$what, undone" 2 0 0 --final
}
append() { printf '%s\n' "${APPEND:--- a comment}" >> "$1"; }

expect "first run" 0 2 0 --final
expect "second run" 2 0 0 --final
# The switches: GATE_CACHE=record runs every unit and records; GATE_CACHE=0 runs every unit and
# neither reads nor records (no stats are kept).
GATE_CACHE=record expect "GATE_CACHE=record" 0 2 0 --final
rm -rf "$GATE_CACHE_DIR"
GATE_CACHE=record expect "GATE_CACHE=record, store emptied" 0 2 0 --final
expect "after GATE_CACHE=record" 2 0 0 --final
rm -rf "$GATE_CACHE_DIR"
GATE_CACHE=0 expect "GATE_CACHE=0, store emptied" 0 0 0 --final
if [ -e "$GATE_CACHE_DIR" ]; then echo "check-gate-cache: GATE_CACHE=0 wrote the store"; bad=1; fi
expect "after GATE_CACHE=0" 0 2 0 --final
expect "again" 2 0 0 --final
cmp -s <(grep -v '^Backend2:' "$t/out") <(GATE_CACHE=0 "$w/scripts/compile-backend2.sh" --final "${files[@]}" 2>&1 | grep -v '^Backend2:') ||
  { echo "check-gate-cache: the replayed output differs from an uncached run"; bad=1; }

p=corpus/${progs[0]}
change "program text" "$p.bc" append
APPEND=x change "standard input (.in)" "$p.in" append
APPEND=x change "arguments (.args)" "$p.args" append
change "golden output (.out)" "$p.out" append
change "golden standard error (.err)" "$p.err" append
APPEND=3 change "golden status (.status)" "$p.status" append
APPEND=x change "source key (.key)" "$p.key" append
rowof() { awk -v n="${progs[0]}" '$1 == n { $NF = $NF " "; print; next } { print }' "$1" > "$t/row"; cat "$t/row" > "$1"; }
change "its row in corpus/counts-backend2.expected" corpus/counts-backend2.expected rowof
# A change every unit reads: both run.
every() {
  local what=$1 f=$w/$2; shift 2
  cp -p "$f" "$t/saved"
  "$@" "$f"
  expect "$what" 0 2 0 --final
  cp -p "$t/saved" "$f"
  expect "$what, undone" 2 0 0 --final
}
every "a library module" lib/prelude.bc append
APPEND="# a comment" every "a script" scripts/par.sh append
byte() { printf '\0' >> "$1"; }
every "the binary bcc names" .lake/build/bin/bcc byte
# A tool's version: a wasmtime first on PATH that reports another version and runs the real one.
real=$(command -v wasmtime)
printf '#!/bin/sh\n[ "$1" = --version ] && { echo "wasmtime 0.0.0-stub"; exit 0; }\nexec "%s" "$@"\n' "$real" > "$t/bin/wasmtime"
chmod +x "$t/bin/wasmtime"
PATH="$t/bin:$PATH" expect "a tool's version (wasmtime)" 0 2 0 --final
expect "a tool's version, undone" 2 0 0 --final
BC_GATE_CACHE_PROBE=1 expect "an environment variable (BC_*)" 0 2 0 --final
BCC_GATE_CACHE_PROBE=1 expect "an environment variable (BCC_*)" 0 2 0 --final
expect "the mode (--final dropped)" 0 2 0
expect "the mode, again" 2 0 0
expect "the mode --final, again" 2 0 0 --final

# Stale binaries are never looked up: with no build in this invocation (no CI_LOCAL_BUILT), the
# script's own `lake build` runs, fails in the copy (it has no Lake project), and nothing is
# replayed though every entry for these binaries is recorded; and a whole step of class `bcc`
# whose caller built nothing runs uncached.
rc=0; : > "$t/stats"
(unset CI_LOCAL_BUILT; GATE_CACHE_STATS=$t/stats "$w/scripts/compile-backend2.sh" --final "${files[@]}" > "$t/out" 2>&1) || rc=$?
if [ "$rc" != 0 ] && [ ! -s "$t/stats" ]; then echo "check-gate-cache: stale binaries and a failing build: exit $rc, nothing replayed"
else echo "check-gate-cache: stale binaries and a failing build: exit $rc, $(cat "$t/stats")"; bad=1; fi
sp() { : > "$t/stats"; (unset CI_LOCAL_BUILT; cd "$w" && GATE_CACHE_STATS=$t/stats python3 scripts/gate_cache.py step built-probe bcc -- true); awk '{ r += $1; n += $2 } END { print r + 0, n + 0 }' "$t/stats"; }
GATE_CACHE_BUILT=1 sp > /dev/null
if [ "$(GATE_CACHE_BUILT=1 sp)" = "1 0" ] && [ "$(sp)" = "0 0" ]; then
  echo "check-gate-cache: a bcc step replays only after a build in its invocation"
else echo "check-gate-cache: a bcc step replays without a build in its invocation"; bad=1; fi

# A failure is never recorded: a golden that differs fails on every run.
cp -p "$w/$p.out" "$t/saved"; echo x >> "$w/$p.out"
expect "a failing unit" 1 1 1 --final
expect "the failing unit, again" 1 1 1 --final
cp -p "$t/saved" "$w/$p.out"
n=$(find "$GATE_CACHE_DIR" -mindepth 2 -maxdepth 2 -type d ! -name '.tmp.*' | wc -l | tr -d ' ')
echo "check-gate-cache: $n entries recorded"

# A whole step's key reads every .lean file, the Lake configuration and the files it names.
mkdir -p "$w/Core"
for f in lakefile.toml lake-manifest.json lean-toolchain Core/Judgment.lean; do cp "$f" "$w/$f"; done
key() { (cd "$w" && python3 scripts/gate_cache.py step-key probe lean --files corpus/kernel-counts.expected -- true); }
k0=$(key)
lean() {
  local what=$1; shift
  "$@"
  if [ "$(key)" = "$k0" ]; then echo "check-gate-cache: a whole step's key: $what: unchanged"; bad=1
  else echo "check-gate-cache: a whole step's key: $what: changed"; fi
}
undo() { for f in lakefile.toml lake-manifest.json lean-toolchain Core/Judgment.lean corpus/kernel-counts.expected; do cp "$f" "$w/$f"; done; rm -f "$w/Core/New.lean"; }
lean "a .lean file" eval 'echo "-- x" >> "$w/Core/Judgment.lean"'; undo
lean "a new .lean file" eval 'echo "-- x" > "$w/Core/New.lean"'; undo
lean "lakefile.toml" eval 'echo "# x" >> "$w/lakefile.toml"'; undo
lean "lake-manifest.json" eval 'echo " " >> "$w/lake-manifest.json"'; undo
lean "lean-toolchain" eval 'echo " " >> "$w/lean-toolchain"'; undo
lean "a file it names" eval 'echo "# x" >> "$w/corpus/kernel-counts.expected"'; undo
[ "$(key)" = "$k0" ] || { echo "check-gate-cache: a whole step's key differs after every change is undone"; bad=1; }

# A unit whose input changes while it runs is not recorded: a step that appends to a file its key
# names runs again on the next run.
: > "$w/corpus/probe.txt"
probe() { : > "$t/stats"; (cd "$w" && GATE_CACHE_STATS=$t/stats python3 scripts/gate_cache.py step probe bcc --files corpus/probe.txt -- sh -c 'echo x >> corpus/probe.txt') > /dev/null; awk '{ r += $1; n += $2 } END { print r + 0, n + 0 }' "$t/stats"; }
probe > /dev/null
if [ "$(probe)" = "0 1" ]; then echo "check-gate-cache: a unit whose input changes while it runs: run again"
else echo "check-gate-cache: a unit whose input changes while it runs was recorded"; bad=1; fi

# The same tree in another directory replays every unit: no path of the worktree is in a key.
w2=$t/other/tree
mkdir -p "$t/other"
cp -R "$w" "$w2"
for b in bcc bcc-counts; do cp -c "$w/.lake/build/bin/$b" "$w2/.lake/build/bin/$b" 2>/dev/null || cp "$w/.lake/build/bin/$b" "$w2/.lake/build/bin/$b"; done
w0=$w; w=$w2
expect "the same tree in another directory" 2 0 0 --final
w=$w0
if [ "$(key)" = "$(cd "$w2" && python3 scripts/gate_cache.py step-key probe lean --files corpus/kernel-counts.expected -- true)" ]; then
  echo "check-gate-cache: a whole step's key in another directory: the same"
else echo "check-gate-cache: a whole step's key in another directory: differs"; bad=1; fi

# One unit's key (`gate_cache.py unit-key`) misses on each of the inputs below.
(cd "$w" && python3 scripts/gate_cache.py tools) > "$t/tools"; export GATE_CACHE_TOOLS_FILE=$t/tools
ukey() { (cd "$w" && PAR_CACHE=probe python3 scripts/gate_cache.py unit-key fn "$1"); }
# miss WHAT ARG CMD…: ARG's unit key before and after CMD differ.
miss() {
  local what=$1 arg=$2 k; shift 2
  k=$(ukey "$arg")
  "$@"
  if [ "$(ukey "$arg")" = "$k" ]; then echo "check-gate-cache: a unit's key: $what: unchanged"; bad=1
  else echo "check-gate-cache: a unit's key: $what: changed"; fi
}
p0=corpus/${progs[0]}.bc
miss "source_digest" "$p0" export source_digest=probe
unset source_digest
miss "LC_COLLATE" "$p0" export LC_COLLATE=C.probe
unset LC_COLLATE
for d in reports trusted copies; do
  mkdir -p "$w/corpus/$d"
  miss "its corpus/$d file" "$p0" eval "echo x > '$w/corpus/$d/${progs[0]}.txt'"
  miss "corpus/$d's program" "corpus/$d/${progs[0]}.txt" eval "echo '-- x' >> '$w/$p0'"
done
mkdir -p "$w/corpus/sugar"
printf -- '-- core: other.core.bc\n' > "$w/corpus/sugar/s.bc"; echo x > "$w/corpus/sugar/other.core.bc"
printf -- '-- lowers: %s\n' "$p0" > "$w/corpus/sugar/l.lowered.bc"
PAR_CACHE_DEPS=sugar miss "a sugared file's named core form" corpus/sugar/s.bc eval "echo y >> '$w/corpus/sugar/other.core.bc'"
PAR_CACHE_DEPS=sugar miss "a lowering's program" corpus/sugar/l.lowered.bc eval "echo '-- y' >> '$w/$p0'"
PAR_CACHE_DEPS="files:corpus/${progs[1]}.out" miss "a file of a files: unit" x eval "echo y >> '$w/corpus/${progs[1]}.out'"
# A book block: its text, its index, and a keys line recorded for its text.
export tmp=$t/book
mkdir -p "$tmp" "$w/book/keys"
printf '1\trun\tbook/src/x.md\t3\n2\trun\tbook/src/x.md\t9\n' > "$tmp/manifest"
echo 'main = 1' > "$tmp/1.bc"; cp "$tmp/1.bc" "$tmp/2.bc"
bh=$({ printf 'run\n'; cat "$tmp/1.bc"; } | shasum -a 256 | cut -d' ' -f1)
PAR_CACHE_DEPS=book miss "a book block's text" 1 eval "echo '-- x' >> '$tmp/1.bc'"
if [ "$(PAR_CACHE_DEPS=book ukey 1)" = "$(PAR_CACHE_DEPS=book ukey 2)" ]; then
  echo "check-gate-cache: a unit's key: a book block's index: the same"; bad=1
else echo "check-gate-cache: a unit's key: a book block's index: changed"; fi
PAR_CACHE_DEPS=book miss "a book block's keys line" 2 eval "echo '$bh k' > '$w/book/keys/x.keys'"
unset tmp
# A file a .lean source names in a string.
mkdir -p "$w/Core"
echo 'def f := "corpus/named.txt"' > "$w/Core/Named.lean"; echo x > "$w/corpus/named.txt"
k1=$(key); echo y >> "$w/corpus/named.txt"
if [ "$(key)" = "$k1" ]; then echo "check-gate-cache: a whole step's key: a file a .lean source names: unchanged"; bad=1
else echo "check-gate-cache: a whole step's key: a file a .lean source names: changed"; fi
# The C compiler's version: an xcrun first on PATH that reports another clang.
if command -v xcrun > /dev/null; then
  printf '#!/bin/sh\n[ "$1 $2" = "clang --version" ] && { echo "clang 0.0.0-stub"; exit 0; }\nexec "%s" "$@"\n' "$(command -v xcrun)" > "$t/bin/xcrun"
  chmod +x "$t/bin/xcrun"
  unset GATE_CACHE_TOOLS_FILE
  k1=$(ukey "$p0")
  if [ "$(PATH="$t/bin:$PATH" ukey "$p0")" = "$k1" ]; then echo "check-gate-cache: a unit's key: the C compiler's version: unchanged"; bad=1
  else echo "check-gate-cache: a unit's key: the C compiler's version: changed"; fi
fi

# par itself: a unit that calls par_nostore, one whose input changes while it runs, and one whose
# input changes and changes back (same content, a new ctime) are not recorded; a plain one is. An
# entry without its side files is a miss.
cat > "$t/par-probe.sh" <<'PROBE'
#!/usr/bin/env bash
set -euo pipefail
cd "$1"; shift
. scripts/par.sh
probe() {
  case "$1" in
    *nostore*) par_nostore ;;
    *change*) echo x >> "${1%.bc}.extra" ;;
    *back*) cp -p "$1" "$PAR_TMP/c"; echo y >> "$1"; sleep 1; cat "$PAR_TMP/c" > "$1" ;;
  esac
  echo "ran $1"
}
export -f probe
export PAR_CACHE=par-probe
par probe "$@"
[ "$par_failed" = 0 ]
PROBE
chmod +x "$t/par-probe.sh"
# (Each in a directory of its own: a unit's directory listing is in its fingerprint, and the
# changing one writes beside itself.)
for n in plain nostore change back; do mkdir -p "$w/corpus/p$n"; echo "main = 1" > "$w/corpus/p$n/p-$n.bc"; done
pp=(corpus/pplain/p-plain.bc corpus/pnostore/p-nostore.bc corpus/pchange/p-change.bc corpus/pback/p-back.bc)
# pexpect WHAT REPLAYED RAN: one run of the probe.
pexpect() {
  : > "$t/stats"; rc=0
  GATE_CACHE_STATS=$t/stats "$t/par-probe.sh" "$w" "${pp[@]}" > "$t/out" 2>&1 || rc=$?
  local r n; r=$(awk '{ s += $1 } END { print s + 0 }' "$t/stats"); n=$(awk '{ s += $2 } END { print s + 0 }' "$t/stats")
  if [ "$r $n $rc" = "$2 $3 0" ]; then echo "check-gate-cache: par: $1: $r replayed, $n run"
  else echo "check-gate-cache: par: $1: $r replayed, $n run, exit $rc; expected $2 replayed, $3 run, exit 0"; sed 's/^/  /' "$t/out"; bad=1; fi
}
pexpect "first run" 0 4
rm -f "$w/corpus/pchange/p-change.extra"
pexpect "nostore, changed and changed-back units run again; the plain one replays" 1 3
rm -f "$w/corpus/pchange/p-change.extra"
find "$GATE_CACHE_DIR/par-probe" -mindepth 2 -maxdepth 2 -name side -exec rm -r {} +
pexpect "an entry without its side files is a miss" 0 4
rm -f "$w/corpus/pchange/p-change.extra"
pexpect "recorded again" 1 3
for e in "$GATE_CACHE_DIR"/par-probe/*/out; do : > "$e"; done
pexpect "an entry whose out is truncated (its checksum differs) is a miss" 0 4
rm -f "$w/corpus/pchange/p-change.extra"
pexpect "recorded again" 1 3

# The switches' values: anything but 1, 0 and record is an error.
if GATE_CACHE=off "$t/par-probe.sh" "$w" corpus/pplain/p-plain.bc > "$t/out" 2>&1; then
  echo "check-gate-cache: GATE_CACHE=off is not refused"; bad=1
else echo "check-gate-cache: GATE_CACHE=off is refused: $(grep -m1 'GATE_CACHE=off' "$t/out")"; fi
# A store that cannot be written is said, in the step's output and in the counts.
mkdir -p "$t/ro"; chmod 555 "$t/ro"
: > "$t/stats"
GATE_CACHE_DIR=$t/ro/store GATE_CACHE_STATS=$t/stats "$t/par-probe.sh" "$w" corpus/pplain/p-plain.bc > "$t/out" 2>&1 || true
chmod 755 "$t/ro"
if grep -q 'WARNING: cannot record' "$t/out" && [ "$(awk '{ s += $3 } END { print s + 0 }' "$t/stats")" -gt 0 ]; then
  echo "check-gate-cache: an unwritable store is reported: $(grep -m1 WARNING "$t/out")"
else echo "check-gate-cache: an unwritable store is not reported"; sed 's/^/  /' "$t/out"; bad=1; fi

[ "$bad" = 0 ] && echo "check-gate-cache: every change of an input misses, and no failure is recorded"
exit "$bad"
