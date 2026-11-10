#!/usr/bin/env bash
# SPEC's implementation status, assembled from `docs/status/`: one file per paragraph.
#
#   scripts/status.sh    the paragraphs, in order (the list `SPEC.md`'s Status section used to hold)
#
# Order: first `docs/status/legacy/NN-<slug>.md`, by their two-digit position (the paragraphs
# before the list was split, whose order was editorial, not by entry); then
# `docs/status/<entry>.md` by entry number (`sort -V`, so `52-53` before `54` and `9` before
# `10`). A file holds its paragraph verbatim, with the blank line that separates it from the one
# above it.
set -euo pipefail
dir="$(cd "$(dirname "$0")/.." && pwd)/docs/status"
[ $# = 0 ] || { echo "usage: scripts/status.sh" >&2; exit 2; }
for f in "$dir"/legacy/[0-9]*.md; do cat "$f"; done
for f in "$dir"/[0-9]*.md; do basename "$f" .md; done | sort -V | while IFS= read -r s; do
  cat "$dir/$s.md"
done
