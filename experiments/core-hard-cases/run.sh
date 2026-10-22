#!/usr/bin/env bash
# Each effect-free core term of the #669 hard cases through the kernel and the new backend:
#   check   `bcc check`: the assurance line, or the kernel's first error (REFUSED)
#   erasure `bcc lir --erasure`: no handle, perform or raise left
#   plain   PlainPath.lean: machines / tailPass sites / genMerges / threaded / stacked / static
#           cells, and the effect layer's LIR operations (must all be 0 / empty)
#   src lir wasm   the reference interpreter (timeout 60 s), the LIR interpreter, Wasm
#   counts  `bcc-counts --backend new`
#
#     experiments/core-hard-cases/run.sh file.bc…     (from the repository root)
cd "$(dirname "$0")/../.."
bcc=.lake/build/bin/bcc
counts=.lake/build/bin/bcc-counts
for f in "$@"; do
  n=$(basename "$f" .bc)
  args=(); [ -f "${f%.bc}.args" ] && read -r -a args < "${f%.bc}.args"
  chk=$("$bcc" check "$f" 2>&1)
  if ! a=$(grep '^assurance:' <<< "$chk"); then
    echo "$n | REFUSED: $(grep -v '^loop ' <<< "$chk" | head -2 | tr '\n' ' ')"
    continue
  fi
  er=$("$bcc" lir --erasure "$f" 2>&1)
  pl=$(lake env lean --run experiments/core-hard-cases/PlainPath.lean "$f" 2>/dev/null | sed -n 2,3p | tr -s ' \n' ' ')
  src=$(timeout 60 "$bcc" interp "$f" -- "${args[@]+"${args[@]}"}" 2>&1 | tr '\n' ' ' | cut -c1-120); [ -n "$src" ] || src=timeout
  lir=$("$bcc" interp --stage lir "$f" -- "${args[@]+"${args[@]}"}" 2>&1 | tr '\n' ' ' | cut -c1-120)
  wasm=$("$bcc" run --backend new "$f" "${args[@]+"${args[@]}"}" 2>&1 | tr '\n' ' ' | cut -c1-120)
  c=$("$counts" --backend new "$f" -- "${args[@]+"${args[@]}"}" 2>&1)
  echo "$n | $a | src: $src | lir: $lir | wasm: $wasm | $er |$pl| $c"
done
