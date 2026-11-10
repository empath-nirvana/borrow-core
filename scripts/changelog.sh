#!/usr/bin/env bash
# The changelog, assembled from `docs/changelog/`: one file per entry, named `<version>.md`, and
# `<version>-b.md` for a second entry that was given a number already in use.
#
#   scripts/changelog.sh            the entries, newest first (the list `SPEC.md` used to hold)
#   scripts/changelog.sh --version  the highest version
#
# Order: by version, highest first (`sort -V`, so 0.10 > 0.9 and 0.3.1 > 0.3); at one version the
# file without a suffix comes first, then `-b`, `-c`, …. An entry's file holds its text verbatim,
# with the blank lines that separate it from the entry above it.
set -euo pipefail
dir="$(cd "$(dirname "$0")/.." && pwd)/docs/changelog"

# Entries listed where their number does not place them, as
# `<file stem> <version it sorts at> <rank at that version>` lines. None today.
placed=''

# One line per entry: sort version, rank, file.
keys() {
  local f stem v suffix rank p
  for f in "$dir"/[0-9]*.md; do
    stem=$(basename "$f" .md)
    v=${stem%%-*}
    suffix=${stem#"$v"}
    case "$suffix" in
      "") rank=0 ;;
      -?) rank=$(( $(printf '%d' "'${suffix#-}") - 96 )) ;;
      *) echo "changelog: unexpected file name $f" >&2; exit 1 ;;
    esac
    p=$(printf '%s\n' "$placed" | awk -v s="$stem" '$1 == s { print $2, $3 }')
    [ -z "$p" ] || { v=${p% *}; rank=${p#* }; }
    printf '%s\t%s\t%s\n' "$v" "$rank" "$f"
  done
}

case "${1:-}" in
  --version)
    for f in "$dir"/[0-9]*.md; do b=$(basename "$f" .md); echo "${b%%-*}"; done | sort -V | tail -1 ;;
  "")
    keys | sort -t $'\t' -k1,1Vr -k2,2n | cut -f3 | while IFS= read -r f; do cat "$f"; done ;;
  *) echo "usage: scripts/changelog.sh [--version]" >&2; exit 2 ;;
esac
