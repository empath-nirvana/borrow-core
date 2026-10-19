#!/bin/bash
D=$(cd "$(dirname "$0")" && pwd); cd $D; R=rs/target/release
while IFS='|' read name a; do b=$(echo $name | tr - _)
 if [[ "$a" == "<"* ]]; then out=$($R/$b < inputs/${a#<} 2>&1 | tr '\n' ' '); else out=$($R/$b $a 2>&1 </dev/null | tr '\n' ' '); fi
 echo "$name [$a]: $out"; done < sizes.txt
