#!/usr/bin/env bash
# The interpreter digest: a sha256 over the source of everything that decides the source stage's
# output beyond the term it runs (scripts/source-stage.sh, `bcc interp --key`).
#
#   * every `.lean` file of the repository in the transitive import closure of `Reference.Source`
#     (`Support`'s interpreter, the machine it steps, the report it prints), found by following
#     `import` lines through the repository's files (a module outside the repository, as
#     Mathlib's, is not followed);
#   * Reference/Driver.lean (which run a checked program gets: `sourceRunOf`, `interpSourceStage`)
#     and Reference/Key.lean (the key itself);
#   * lean-toolchain (the compiler the interpreter is built with).
#
# The falsifier (`Reference.Falsify`, `bcc interp --check`) is not on the source stage's path.
#
#     scripts/interp-digest.sh           the digest
#     scripts/interp-digest.sh --files   the files it hashes, one per line
set -euo pipefail
cd "$(dirname "$0")/.."

imports() { sed -n 's/^import \([A-Za-z0-9_.]*\).*/\1/p' "$1"; }
fileOf() { echo "${1//.//}.lean"; }

seen=" "
files=()
todo="Reference.Source"
while [ -n "$todo" ]; do
  next=""
  for i in $todo; do
    case "$seen" in *" $i "*) continue ;; esac
    seen="$seen$i "
    f=$(fileOf "$i")
    [ -f "$f" ] || continue
    files+=("$f")
    next="$next $(imports "$f")"
  done
  todo=$next
done
files+=(Reference/Driver.lean Reference/Key.lean lean-toolchain)
list=$(printf '%s\n' "${files[@]}" | LC_ALL=C sort -u)

if [ "${1:-}" = --files ]; then printf '%s\n' "$list"; exit 0; fi
[ $# = 0 ] || { echo "usage: scripts/interp-digest.sh [--files]"; exit 2; }
# Each file's path and content hash, then the hash of that list.
printf '%s\n' "$list" | while IFS= read -r f; do
  printf '%s  %s\n' "$(shasum -a 256 < "$f" | cut -d' ' -f1)" "$f"
done | shasum -a 256 | cut -d' ' -f1
