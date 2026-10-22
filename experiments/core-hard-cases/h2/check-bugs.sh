#!/usr/bin/env bash
# Each injected bug through the kernel: REJECTED with the kernel's first error, or ACCEPTED with
# its runs at the reference interpreter and the LIR interpreter (`live` is the leak check).
#     experiments/core-hard-cases/h2/check-bugs.sh file.bc…     (from the repository root)
cd "$(dirname "$0")/../../.."
bcc=.lake/build/bin/bcc
for f in "$@"; do
  n=$(basename "$f" .bc)
  kind=$(head -1 "$f" | grep -oE '\((MEMORY|SEMANTIC)')
  r=$("$bcc" check "$f" 2>&1)
  if a=$(grep '^assurance' <<< "$r"); then
    echo "$n ${kind#(} | ACCEPTED $a | src: $("$bcc" interp "$f" 2>&1 | tr '\n' ' ' | cut -c1-140)| lir: $("$bcc" interp --stage lir "$f" 2>&1 | tr '\n' ' ' | cut -c1-140)"
  else
    echo "$n ${kind#(} | REJECTED: $(grep -vE '^(loop|effect|def|main|handler|type|fn) ' <<< "$r" | head -1 | sed 's|^.*/||')"
  fi
done
