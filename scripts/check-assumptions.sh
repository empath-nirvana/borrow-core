#!/usr/bin/env bash
# Every named hypothesis is registered: every closed `Prop` (`def|abbrev|structure X … : Prop`)
# that a declaration takes as a premise, `(h : X …)` or `X … →`, in the library or the compiler,
# must be listed in Core/Assumptions.lean, as an entry's `decl := ``…X``` or an outside entry's
# `name := "X"`. Registering it, with its research question (issue #1122), is the only way past
# this check, and it shows up in review. A registered name whose definition is gone fails too.
#
#     scripts/check-assumptions.sh            check
#     scripts/check-assumptions.sh --list     print the hypotheses found
set -euo pipefail
cd "$(dirname "$0")/.."
reg=Core/Assumptions.lean
pats=()
for d in Core Support Paper Examples Frontend Pipeline Reference Target Backend Backend2; do pats+=("$d/*.lean"); done
# Closed `Prop`s: implicit and instance binders only, then `: Prop`. The last name component.
props=$(git grep -hoE '^(noncomputable )?(def|abbrev|structure) (_root_\.)?[A-Za-z0-9_.]+( \{[^}]*\}| \[[^]]*\])* : Prop( |$)' \
  -- "${pats[@]}" | sed -E 's/^(noncomputable )?(def|abbrev|structure) (_root_\.)?//; s/ .*//; s/.*\.//' | sort -u)
# Names in premise position: an explicit binder's type head, or a name (with `(ℍ := ℍ)`) before `→`.
used=$( { git grep -hoE "\([A-Za-z_][A-Za-z0-9_₀-₉']* : [A-Za-z0-9_.]+" -- "${pats[@]}" | sed -E 's/.* : //'
          git grep -hoE "[A-Za-z0-9_.]+( \(ℍ := ℍ\))? →" -- "${pats[@]}" | sed -E 's/ .*//'; } \
  | sed -E 's/.*\.//' | sort -u)
found=$(comm -12 <(printf '%s\n' "$props") <(printf '%s\n' "$used"))
if [ "${1:-}" = "--list" ]; then printf '%s\n' "$found"; exit 0; fi
registered=$( { grep -oE 'decl := ``[A-Za-z0-9_.]+' "$reg" | sed -E 's/.*\.//; s/.*``//'
                grep -oE 'name := "[A-Za-z0-9_.]+"' "$reg" | sed -E 's/name := "//; s/"$//; s/.*\.//'; } | sort -u)
new=$(comm -23 <(printf '%s\n' "$found") <(printf '%s\n' "$registered"))
if [ -n "$new" ]; then
  echo "check-assumptions: hypothesis(es) taken as a premise but not in $reg:"
  printf '  %s\n' $new
  echo "Register each with its research question (issue #1122), its standing and the theorems that take it."
  exit 1
fi
gone=$(comm -13 <(printf '%s\n' "$props") <(printf '%s\n' "$registered"))
[ -z "$gone" ] || { echo "check-assumptions: registered but no longer defined (remove these entries):"; printf '  %s\n' $gone; exit 1; }
echo "check-assumptions: $(printf '%s\n' "$found" | grep -c .) hypotheses taken as premises, $(printf '%s\n' "$registered" | grep -c .) registered, none new"
