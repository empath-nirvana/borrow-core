#!/usr/bin/env bash
# Generate COUNT stress programs from seed FIRST into DIR, check each, compare its answer with the
# simulated one, and run the accepted ones under every mode of scripts/falsify.sh.
#     run.sh DIR FIRST COUNT
set -uo pipefail
root="$(cd "$(dirname "$0")/../../.." && pwd)"
bcc="$root/.lake/build/bin/bcc"
dir=$1; first=$2; count=$3
python3 "$(dirname "$0")/gen.py" "$dir" "$first" "$count"
acc=0; rej=0; wrong=0; ok=()
for f in "$dir"/s*.bc; do
  s=${f%.bc}
  if "$bcc" check "$f" > "$s.check" 2>&1; then
    acc=$((acc+1)); ok+=("$f")
    "$bcc" interp "$f" > "$s.out" 2>&1
    if ! cmp -s "$s.out" "$s.expect"; then wrong=$((wrong+1)); echo "WRONG ANSWER: $f: $(tr '\n' ' ' < "$s.out") expected $(tr '\n' ' ' < "$s.expect")"; fi
  else
    rej=$((rej+1)); echo "refused: $f: $(head -1 "$s.check" | sed 's/^[^:]*:[0-9]*:[0-9]*: //' | cut -c1-140)"
  fi
done
echo "accepted $acc, refused $rej, wrong answers $wrong"
cd "$root" && CI_LOCAL_BUILT=1 scripts/falsify.sh "${ok[@]}" 2>&1 | grep -v ': ok ' 
