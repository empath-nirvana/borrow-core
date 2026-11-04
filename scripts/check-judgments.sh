#!/usr/bin/env bash
# Typing judgments are frozen: every `inductive …Derives…` in a Lean source must be listed in
# scripts/judgments.allow as `path name`. A new coordinate goes into an existing judgment's index,
# never into a new judgment (#798). Adding a line to the allowlist is the only way past this
# check, and it shows up in review.
#
#     scripts/check-judgments.sh            check
#     scripts/check-judgments.sh --list     print the judgments found, in allowlist form
set -euo pipefail
cd "$(dirname "$0")/.."
found=$(git ls-files '*.lean' | xargs grep -HoE '^inductive [A-Za-z0-9_.]*Derives[A-Za-z0-9_]*' \
  | sed -E 's/:inductive / /' | sort -u)
if [ "${1:-}" = "--list" ]; then printf '%s\n' "$found"; exit 0; fi
allow=$(grep -vE '^(#|$)' scripts/judgments.allow | sort -u)
new=$(comm -23 <(printf '%s\n' "$found") <(printf '%s\n' "$allow"))
if [ -n "$new" ]; then
  echo "check-judgments: new typing judgment(s), not in scripts/judgments.allow:"
  printf '  %s\n' $new | paste - -
  echo "Add the coordinate to an existing judgment's index instead (#798)."
  exit 1
fi
gone=$(comm -13 <(printf '%s\n' "$found") <(printf '%s\n' "$allow"))
[ -z "$gone" ] || { echo "check-judgments: allowlisted but gone (remove these lines):"; printf '%s\n' "$gone"; exit 1; }
echo "check-judgments: $(printf '%s\n' "$found" | wc -l | tr -d ' ') judgments, none new"
