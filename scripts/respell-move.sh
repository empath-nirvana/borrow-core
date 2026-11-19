#!/usr/bin/env bash
# Respell source files in place (SPEC §82, while both spellings are alive). For each file in
# today's spelling: its text moves to its twin (`corpus/.respell-old/<path>`, the pairs
# scripts/check-respell.sh checks), and `bcc respell`'s translation takes its place. Its golden, key
# and other sidecars stay where they are. A file `bcc respell` does not translate whole (a
# `#?respell:` mark, or a parse error) is left as it is and reported; so is a file already in the
# new spelling.
#
#     scripts/respell-move.sh file.bc…
set -euo pipefail
cd "$(dirname "$0")/.."
bcc=.lake/build/bin/bcc
pragma=$("$bcc" respell --pragma)
twin() { case "$1" in corpus/*) echo "corpus/.respell-old/${1#corpus/}" ;; lib/*) echo "corpus/.respell-old/$1" ;; *) return 1 ;; esac; }
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
moved=0 left=0
for f in "$@"; do
  o=$(twin "$f") || { echo "$f: not under corpus/ or lib/"; left=$((left + 1)); continue; }
  if [ "$(head -n 1 "$f")" = "$pragma" ]; then echo "$f: already in the new spelling"; left=$((left + 1)); continue; fi
  if [ -e "$o" ]; then echo "$f: its twin $o exists"; left=$((left + 1)); continue; fi
  if ! timeout 120 "$bcc" respell "$f" > "$tmp/out" 2> "$tmp/err"; then
    echo "$f: left in today's spelling:"; sed 's/^/  /' "$tmp/err"; left=$((left + 1)); continue
  fi
  mkdir -p "$(dirname "$o")"
  git mv "$f" "$o"
  cp "$tmp/out" "$f"
  git add "$f"
  moved=$((moved + 1))
done
echo "$moved file(s) respelled, $left left."
