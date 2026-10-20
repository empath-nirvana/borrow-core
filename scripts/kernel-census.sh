#!/usr/bin/env bash
# The census of kernel nodes in the checked corpus (`docs/kernel-usage.md`): check every corpus
# program `scripts/check-corpus.sh` checks (not the parse-only ones) and count, over `main`'s typed
# term, each `TExpr` node, each type former of the nodes' judgments, and the qualifiers at
# `[handle]` (`scripts/KernelCensus.lean`). The library `lib/*.bc` is counted where the programs
# use it (the `lib` column).
#
#     scripts/kernel-census.sh [file…]
set -euo pipefail
cd "$(dirname "$0")/.."
lake build kernel-census >/dev/null
if [ $# -eq 0 ]; then
  set -- corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc
fi
files=()
for f in "$@"; do grep -q '^-- check: parse-only' "$f" || files+=("$f"); done
exec .lake/build/bin/kernel-census "${files[@]}"
