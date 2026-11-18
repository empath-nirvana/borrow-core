#!/usr/bin/env bash
# Compile and run the kernel programs (`Backend/Kernel.lean`, `bcc kernel list`): the programs of
# `Core/` that the surface cannot spell, such as SPEC §19's acceptance programs. For each, the
# source interpreter (`bcc kernel interp`), the closure-IR and flat-IR interpreters
# (`--stage clos|flat`) and WebAssembly under wasmtime (`bcc kernel run`) must print the same
# value and then `live 0`. Its counts (`bcc-counts --kernel`: allocations, indirect calls, deep
# copies; the flat IR and wasm must agree) must be at most its entry in
# `corpus/kernel-counts.expected` (`name allocs indirect copies`).
set -euo pipefail
cd "$(dirname "$0")/.."
command -v wasmtime >/dev/null || { echo "wasmtime is not on PATH"; exit 1; }
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
export GATE_CACHE_BUILT=1  # the binaries the result cache may key on are this build's
# One unit of the result cache (scripts/gate_cache.py `step`): a recorded pass is replayed when
# the binaries, the library, scripts/, the tools and corpus/kernel-counts.expected are as they were.
[ "${GATE_CACHE_INNER:-}" = kernel ] || exec python3 scripts/gate_cache.py step kernel bcc --files corpus/kernel-counts.expected -- scripts/compile-kernel.sh "$@"
bcc=.lake/build/bin/bcc
bccCounts=.lake/build/bin/bcc-counts
expected=corpus/kernel-counts.expected
export bcc bccCounts expected
. scripts/par.sh
# One kernel program: its runs and its counts. The programs run as `par` jobs, each in a slot of
# the job pool, and report in `bcc kernel list`'s order.
kernel() {
  local name=$1 bad=0 src out got a i c want wa wi wc
  src=$("$bcc" kernel interp "$name" 2>&1) || { echo "$name: source: $src"; return 1; }
  case "$src" in *"live 0") ;; *) echo "$name: source leaves cells: $src"; return 1 ;; esac
  for stage in clos flat; do
    out=$("$bcc" kernel interp --stage "$stage" "$name" 2>&1) || true
    if [ "$out" != "$src" ]; then echo "$name: $stage differs: $out (source: $src)"; bad=1; fi
  done
  out=$("$bcc" kernel run "$name" 2>&1) || true
  if [ "$out" != "$src" ]; then echo "$name: wasm differs: $out (source: $src)"; bad=1; fi
  got=$("$bccCounts" --kernel "$name" 2>&1) || { echo "$name: counts: $got"; return 1; }
  a=$(echo "$got" | awk '{print $2}'); i=$(echo "$got" | awk '{print $4}'); c=$(echo "$got" | awk '{print $6}')
  want=$(awk -v n="$name" '$1 == n {print $2, $3, $4}' "$expected")
  if [ -z "$want" ]; then echo "$name: no entry in $expected ($got)"; return 1; fi
  read -r wa wi wc <<< "$want"
  if [ "$a" -gt "$wa" ] || [ "$i" -gt "$wi" ] || [ "$c" -gt "$wc" ]; then
    echo "$name: counts regressed: $got, expected at most allocs $wa, indirect $wi, copies $wc"; bad=1
  fi
  echo "$name: ${src%%$'\n'*}; $got"
  return "$bad"
}
export -f kernel
names=$("$bcc" kernel list)
# shellcheck disable=SC2086
par kernel $names
[ "$par_failed" = 0 ]
