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
#   environment variable (`BC_*`, `BCC_*`); and the mode (`--final` dropped).
#
# Each change is undone after its run, and the next run replays again. A unit that fails (its
# golden changed so that it differs) runs, fails, and fails again on the next run: no failure is
# recorded. A whole step's key (`gate_cache.py step-key`) changes with a `.lean` file, a new
# `.lean` file, the lakefile, the manifest and the toolchain, and with a file it names; a unit
# whose input changes while it runs is not recorded. The tree's own files are only read.
#
#     scripts/check-gate-cache.sh
set -euo pipefail
cd "$(dirname "$0")/.."
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
unset GATE_CACHE GATE_CACHE_TOOLS GATE_CACHE_INNER GATE_CACHE_STATS PAR_CACHE PAR_CACHE_DEPS PAR_COLLECT
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

[ "$bad" = 0 ] && echo "check-gate-cache: every change of an input misses, and no failure is recorded"
exit "$bad"
