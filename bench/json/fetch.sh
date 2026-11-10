#!/bin/bash
# The three documents of nativejson-benchmark (#977), fetched into bench/json/data/ from the
# repository at a pinned commit and checked against their SHA-256. They are not committed: see
# data/SOURCES.md for their origins and licences. A file already present is only checked; a
# mismatch, on download or on a file already there, is an error and the file is removed.
# `fetch.sh --verify` checks without downloading.
set -euo pipefail
cd "$(dirname "$0")/data"
commit=478d5727c2a4048e835a29c65adecc7d795360d5
base="https://raw.githubusercontent.com/miloyip/nativejson-benchmark/$commit/data"
verify_only=0
[ "${1:-}" = "--verify" ] && verify_only=1
status=0
while read -r sum name; do
  if [ ! -f "$name" ]; then
    if [ $verify_only = 1 ]; then echo "fetch.sh: $name missing" >&2; status=1; continue; fi
    curl -fsSL --retry 3 -o "$name.part" "$base/$name"
    mv "$name.part" "$name"
  fi
  got=$(shasum -a 256 "$name" | cut -d' ' -f1)
  if [ "$got" != "$sum" ]; then
    echo "fetch.sh: $name: SHA-256 $got, expected $sum; removed" >&2
    rm -f "$name"
    status=1
  else
    echo "$name ok"
  fi
done <<'SUMS'
f83b3b354030d5dd58740c68ac4fecef64cb730a0d12a90362a7f23077f50d78 canada.json
a73e7a883f6ea8de113dff59702975e60119b4b58d451d518a929f31c92e2059 citm_catalog.json
a08b769f32b95f426cbc3abafcec65c1a19d3eb544d4ddf320eae142c99efc5d twitter.json
SUMS
exit $status
