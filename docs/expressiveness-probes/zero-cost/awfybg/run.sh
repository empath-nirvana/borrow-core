#!/bin/sh
# Ours (bcc-counts) and the Rust references (counting allocator), same sizes and inputs.
D=$(cd "$(dirname "$0")" && pwd)
P=~/repos/borrow-core-expr/docs/expressiveness-probes
C=~/repos/borrow-core-c3c/.lake/build/bin/bcc-counts
IN=$P/bg/fasta1000.fa
(cd "$D/rs" && cargo build --release -q)
R=$D/rs/target/release
row() { name=$1; probe=$2; shift 2
  o=$($C "$probe" "$@" < "${STDIN:-/dev/null}" 2>&1 | grep '^allocs' )
  r=$("$R/$name" "$@" < "${STDIN:-/dev/null}" 2>&1 >/dev/null | grep '^rust allocs')
  echo "$name | ours: $o | $r"; }
for x in richards:awfy/richards.bc deltablue:awfy/deltablue.bc havlak:awfy/havlak.bc cd_rbtree:awfy/cd_rbtree.bc \
         json:awfy/json.bc bounce:awfy/bounce.bc list:awfy/list.bc permute:awfy/permute_natural.bc \
         queens:awfy/queens.bc storage:awfy/storage.bc towers:awfy/towers.bc fannkuch:bg/fannkuch.bc fasta:bg/fasta.bc \
         pidigits:bg/pidigits.bc; do row ${x%%:*} $P/${x#*:}; done
for x in knuc:bg/knuc.bc regex:bg/regex.bc revcomp:bg/revcomp.bc; do STDIN=$IN row ${x%%:*} $P/${x#*:}; done
# Nested recursion (#722): nodes owning arrays of their children, dropped by the derived destructor.
K=$(cd "$D/../../../.." && pwd)/corpus
row storage $K/storage-array.bc
row btree_boxed $K/btree-boxed.bc
STDIN=$K/leetcode/trees/0208-implement-trie-boxed.in row trie_boxed $K/leetcode/trees/0208-implement-trie-boxed.bc
echo "pidigits 1000 | ours: $($C $P/bg/pidigits.bc -- 1000 2>&1 | grep '^allocs') | $($R/pidigits 1000 2>&1 >/dev/null)"
echo "regex (buffers hoisted, probe-variants/regex_reuse.bc) | ours: $($C $D/probe-variants/regex_reuse.bc < $IN 2>&1 | grep '^allocs')"
