#!/usr/bin/env bash
# Runs this experiment's programs. Each bc/*.bc is run compiled (`bcc run`, wasmtime) and by the
# model's interpreter (`bcc interp`); both must print bc/<name>.out (the value, then `live 0`).
# `bcc-counts` gives its allocations and dispatched calls, which must equal bc/counts.txt.
# Each rs/*.rs is compiled with rustc, if present, and must print rs/<name>.out.
# `--write` rewrites the goldens and the counts.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
cd "$root"
lake build bcc bcc-counts >/dev/null
bcc="$root/.lake/build/bin/bcc"; counts="$root/.lake/build/bin/bcc-counts"
write=0; [ "${1:-}" = "--write" ] && write=1
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
bad=0
: > "$tmp/counts"
for f in "$here"/bc/*.bc; do
  n=$(basename "${f%.bc}")
  run=$("$bcc" run "$f" 2>&1) || { echo "$n: run failed: $run"; bad=1; continue; }
  interp=$("$bcc" interp "$f" 2>&1) || { echo "$n: interp failed: $interp"; bad=1; continue; }
  c=$("$counts" "$f" < /dev/null)
  echo "$n $(echo "$c" | awk '{print $2, $4}')" >> "$tmp/counts"
  if [ "$write" = 1 ]; then echo "$run" > "$here/bc/$n.out"; fi
  [ "$run" = "$interp" ] || { echo "$n: run and interp differ"; bad=1; }
  [ "$run" = "$(cat "$here/bc/$n.out")" ] || { echo "$n: output differs from bc/$n.out: $run"; bad=1; }
  echo "ok  bc/$n.bc  $(echo "$run" | head -1)  ($c)"
done
if [ "$write" = 1 ]; then cp "$tmp/counts" "$here/bc/counts.txt"; fi
diff "$tmp/counts" "$here/bc/counts.txt" || { echo "counts differ from bc/counts.txt"; bad=1; }
if command -v rustc >/dev/null; then
  for f in "$here"/rs/*.rs; do
    n=$(basename "${f%.rs}")
    rustc --edition 2021 -O "$f" -o "$tmp/$n" 2>"$tmp/err" || { echo "$n.rs: rustc failed"; cat "$tmp/err"; bad=1; continue; }
    out=$("$tmp/$n")
    if [ "$write" = 1 ]; then echo "$out" > "$here/rs/$n.out"; fi
    [ "$out" = "$(cat "$here/rs/$n.out")" ] || { echo "$n.rs: output differs: $out"; bad=1; }
    echo "ok  rs/$n.rs  $out"
  done
else
  echo "rustc not found: rs/*.rs skipped"
fi
if [ "$bad" = 0 ]; then echo "InteriorMutability: ALL PASSED"; else echo "InteriorMutability: FAILURES"; exit 1; fi
