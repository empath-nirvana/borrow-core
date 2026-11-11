#!/usr/bin/env bash
# The native target (SPEC §40, Target/Native/), checked against the flat IR: the corpus on
# Backend2, the default backend (`bcc run --native`, `bcc-counts --native`), or with
# `--backend old` on the old backend; the kernel programs on the old backend (`bcc kernel`, which
# stays there until N7). Needs a C compiler
# that builds LLVM IR (`bcc cc`); without one the script says so and passes, as the gate does for
# mdbook.
#
#   * Every corpus program (the programs scripts/compile-corpus.sh runs) is built with
#     `bcc run --native` and run on `<name>.in` with `<name>.args`: its standard output, standard
#     error and exit status must be the golden `<name>.out`, `<name>.err` and `<name>.status`,
#     which scripts/compile-corpus.sh checks the flat IR against, so native agrees with the flat
#     interpreter on all four, `live` included.
#   * Its counts (`bcc-counts --native`: the flat IR built to count, and native built to count)
#     must agree.
#   * Every kernel program (`bcc kernel list`) must print at native what it prints at the flat IR.
#   * Every host operation, on a table of operands, must answer at native what the flat-IR
#     interpreter's host (`flatHost`) answers (`bcc hostops`, Backend/Native/Tests.lean).
#   * Loops of tail calls run in constant stack: in a stack of 64 KiB, a generated loop of 10^8
#     turns, the kernel program loop-tail and corpus/deep-list.bc (owned folds by pointer
#     reversal, SPEC §67).
#
#     scripts/compile-native.sh [--backend old|new] [file.bc…]
#                                            every check, or the corpus programs named only
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
# The C compiler is the one `bcc` builds with (`bcc cc`, Backend.nativeCC): `$BC_CC`, else
# `xcrun clang` on macOS, else a clang on PATH outside a Lean toolchain.
cc=$(.lake/build/bin/bcc cc 2>/dev/null) || { echo "no C compiler for the native target: it is not checked"; exit 0; }
echo "C compiler: $cc"
. scripts/par.sh
export bcc=.lake/build/bin/bcc
export bccCounts=.lake/build/bin/bcc-counts
export backend=new
if [ "${1:-}" = --backend ]; then
  case "${2:-}" in old|new) backend=$2; shift 2 ;; *) echo "usage: scripts/compile-native.sh [--backend old|new] [file.bc…]"; exit 2 ;; esac
fi
named=1
files=("$@")
[ ${#files[@]} -gt 0 ] || { named=0; files=(corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc); }
for f in "${files[@]}"; do [ -f "$f" ] || { echo "$f: no such file"; exit 2; }; done

argsOf() {
  args=()
  local a=${1%.bc}.args line
  [ -f "$a" ] || return 0
  while IFS= read -r line || [ -n "$line" ]; do args+=("$line"); done < "$a"
}
statusOf() {
  local s=${1%.bc}.status
  if [ -f "$s" ]; then tr -d ' \n' < "$s"; else echo 0; fi
}
# One corpus program, built natively and run, then counted.
program() {
  local f=$1 w=$PAR_TMP base in err rc=0 got
  if grep -q '^-- check: parse-only' "$f" || ! grep -q '^main' "$f"; then return 0; fi
  # The old backend refuses it at compile time (scripts/compile-corpus.sh).
  if [ "$backend" = old ] && grep -q '^-- check: old-backend-refuses' "$f"; then return 0; fi
  base=${f%.bc}
  in=/dev/null; [ -f "$base.in" ] && in="$base.in"
  err=/dev/null; [ -f "$base.err" ] && err="$base.err"
  argsOf "$f"
  "$bcc" run --backend "$backend" --native "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$?
  if [ "$rc" != "$(statusOf "$f")" ]; then
    echo "$f: native exits with $rc, not $(statusOf "$f"): $(head -3 "$w/err")"; return 1
  fi
  if ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
    echo "$f: native differs from $base.out or from its standard error"
    diff "$w/out" "$base.out" | head -6 | sed 's/^/  /' || true
    diff "$w/err" "$err" | head -4 | sed 's/^/  /' || true
    return 1
  fi
  if ! got=$("$bccCounts" --backend "$backend" --native "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>&1); then
    echo "$f: counts: $got"; return 1
  fi
  echo "$f: native as $base.out | $got"
}
export -f program argsOf statusOf
par program "${files[@]}"
bad=$par_failed

if [ "$named" = 0 ]; then
  for name in $("$bcc" kernel list); do
    want=$("$bcc" kernel interp --stage flat "$name" 2>&1) || true
    out=$("$bcc" kernel run --native "$name" 2>&1) || true
    if [ "$out" = "$want" ]; then echo "kernel $name: native as flat"
    else echo "kernel $name: native differs: $out (flat: $want)"; bad=$((bad + 1)); fi
  done

  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  "$bcc" hostops flat > "$tmp/flat" || { echo "hostops: the flat IR fails"; bad=$((bad + 1)); }
  "$bcc" hostops native > "$tmp/native" || { echo "hostops: native fails"; bad=$((bad + 1)); }
  if cmp -s "$tmp/flat" "$tmp/native"; then
    echo "hostops: $(grep -c '^==' "$tmp/flat") operations, $(grep -vc '^==' "$tmp/flat") cases, native as the Lean host"
  else
    echo "hostops: native differs from the Lean host:"
    diff "$tmp/flat" "$tmp/native" | head -10 | sed 's/^/  /' || true
    bad=$((bad + 1))
  fi

  # Under `lake env` (as `lake exe bcc run --native` runs), PATH starts with the Lean toolchain's
  # bin, whose clang has no C headers: the build must not take it.
  rc=0
  lake env "$bcc" run --backend "$backend" --native corpus/div-unhandled.bc > "$tmp/out" 2> "$tmp/err" || rc=$?
  if [ "$rc" = 1 ] && cmp -s "$tmp/out" corpus/div-unhandled.out; then
    echo "corpus/div-unhandled.bc: native under lake env's PATH"
  else
    echo "corpus/div-unhandled.bc: native under lake env's PATH fails ($rc): $(head -3 "$tmp/err")"; bad=$((bad + 1))
  fi

  # Constant stack: loops of tail calls on a stack of 64 KiB (`BC_STACK`), where a frame per call
  # would last a few thousand calls: a generated loop of 10^8 turns (`bcc tailcalls`), the kernel
  # program loop-tail (10^5 operations, each a turn of a loop of tail calls through a handler),
  # and corpus/deep-list.bc (lists of 50000 built and summed by loops, folded by pointer reversal,
  # SPEC §67 on Backend2), on the backend `--backend` selects.
  "$bcc" tailcalls 100000000 || bad=$((bad + 1))
  want=$("$bcc" kernel interp --stage flat loop-tail 2>&1) || true
  out=$(BC_STACK=65536 "$bcc" kernel run --native loop-tail 2>&1) || true
  if [ "$out" = "$want" ]; then echo "kernel loop-tail: native in a stack of 64 KiB"
  else echo "kernel loop-tail: native in a stack of 64 KiB fails: $out"; bad=$((bad + 1)); fi
  if BC_STACK=65536 "$bcc" run --backend "$backend" --native corpus/deep-list.bc < /dev/null > "$tmp/out" 2> "$tmp/err" &&
      cmp -s "$tmp/out" corpus/deep-list.out; then
    echo "corpus/deep-list.bc: native in a stack of 64 KiB ($backend)"
  else
    echo "corpus/deep-list.bc: native in a stack of 64 KiB fails: $(head -3 "$tmp/err")"; bad=$((bad + 1))
  fi
  # A Json 10^6 levels deep freed by the in-place consume (SPEC §77) in a stack of 16 KiB: its
  # answer is the depth, and `live 0`.
  if [ "$backend" = new ]; then
    if BC_STACK=16384 "$bcc" run --backend new --native corpus/json-drop-deep.bc 1000000 < /dev/null > "$tmp/out" 2> "$tmp/err" &&
        [ "$(cat "$tmp/out")" = "$(printf 'built\ni32[1000000]\nlive 0')" ]; then
      echo "corpus/json-drop-deep.bc: 10^6 levels native in a stack of 16 KiB"
    else
      echo "corpus/json-drop-deep.bc: 10^6 levels native in a stack of 16 KiB fails: $(head -3 "$tmp/out") $(head -3 "$tmp/err")"; bad=$((bad + 1))
    fi
  fi
fi
# No weak imports (macOS): a native program is built pinned to the oldest supported OS
# (`Pipeline/Driver.lean`, `macosMinVersion`), so an API that OS lacks is a build error. A weak
# import would be null at run time on that OS. One program of each shape the runtime serves.
if [ "$(uname)" = Darwin ] && [ "$named" = 0 ]; then
  wdir=$tmp/weak; mkdir -p "$wdir"
  "$bcc" cc --runtime > "$wdir/runtime.c"
  read -r -a ccmd <<< "$("$bcc" cc)"; read -r -a cflags <<< "$("$bcc" cc --flags)"
  for f in corpus/io-cat.bc corpus/io-task.bc corpus/async-borrow.bc corpus/float-arith.bc corpus/deep-list.bc; do
    n=$(basename "$f" .bc)
    if "$bcc" compile --backend "$backend" --target native "$f" -o "$wdir/$n.ll" > /dev/null 2> "$wdir/$n.err" &&
        "${ccmd[@]}" "${cflags[@]}" "$wdir/$n.ll" "$wdir/runtime.c" -o "$wdir/$n" 2>> "$wdir/$n.err"; then
      weak=$(nm -m "$wdir/$n" | grep -i 'weak' | grep -i 'undefined' || true)
      if [ -n "$weak" ]; then echo "$f: native build weak-imports: $weak"; bad=$((bad + 1))
      else echo "$f: native build has no weak import"; fi
    else
      echo "$f: native build for the weak-import check fails: $(head -3 "$wdir/$n.err")"; bad=$((bad + 1))
    fi
  done
fi
echo "$bad failure(s)."
[ "$bad" -eq 0 ]
