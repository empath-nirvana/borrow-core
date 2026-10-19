#!/bin/bash
C=${BCC_COUNTS:-bcc-counts}; D=$(cd "$(dirname "$0")" && pwd)
cd ~/repos/borrow-core-expr
while IFS='|' read name a; do
  start=$(date +%s)
  if [[ "$a" == "<"* ]]; then out=$(timeout 600 $C bench/$name/main.bc < $D/inputs/${a#<} 2>&1 | tail -3 | tr '\n' ' ')
  else out=$(timeout 600 $C bench/$name/main.bc -- $a 2>&1 | tail -3 | tr '\n' ' '); fi
  echo "$name [$a] ($(($(date +%s)-start))s): $out"
done < $D/sizes.txt
