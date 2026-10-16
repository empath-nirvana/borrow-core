#!/usr/bin/env bash
# The typed IR (docs/typed-elaboration.md, stage 1). For every corpus program that checks (not
# `-- check: parse-only`) and every sugar pair,
# `bcc tir` types every node of every declaration with a body and lowers back to exactly the
# program the checker is given. For every corpus/tir/<name>.tir, `bcc tir corpus/<name>.bc`
# prints exactly that file: the binders' types and classes are pinned.
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bad=0
for f in corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/sugar/*.bc; do
  grep -q '^-- check: parse-only' "$f" && continue
  if ! "$bcc" tir "$f" > /dev/null 2> $tmp/err; then
    echo "$f: $(cat $tmp/err)"; bad=$((bad + 1))
  fi
done
for g in corpus/tir/*.tir; do
  [ -e "$g" ] || continue
  f=corpus/$(basename "${g%.tir}").bc
  if ! diff -u "$g" <("$bcc" tir "$f"); then echo "$g: differs"; bad=$((bad + 1))
  else echo "$g: matches"; fi
done
echo "$bad failure(s)."
[ "$bad" -eq 0 ]
