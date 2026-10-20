#!/bin/sh
# The #593 zero-cost targets written with `data` declarations (SPEC §42), beside the probes they
# port: allocations, indirect calls, copies, loads, stores and bounds checks by `bcc-counts`, for
# each port and for its probe. The Rust counts are those of `../awfybg/results.txt`,
# `../rest/ds-rust` (`cargo run --release --bin <name>`) and `../bench/rust.txt`.
D=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$D/../../../.." && pwd)
C=${BCC_COUNTS:-$R/.lake/build/bin/bcc-counts}
P=$R/docs/expressiveness-probes
row() { echo "$1 | data: $($C "$D/$2" $4 2>&1 | grep '^allocs') | probe: $($C "$3" $4 2>&1 | grep '^allocs')"; }
row richards richards.bc "$P/awfy/richards.bc"
row deltablue deltablue.bc "$P/awfy/deltablue.bc"
row cd cd_rbtree.bc "$P/awfy/cd_rbtree.bc"
row union-find unionfind.bc "$P/ds/unionfind.bc"
row arena arena.bc "$P/ds/arena.bc"
row lru lru.bc "$P/ds/lru-arena.bc"
row n-body nbody.bc "$R/bench/n-body/main.bc" "-- 100"
