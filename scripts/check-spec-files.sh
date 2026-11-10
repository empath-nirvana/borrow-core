#!/usr/bin/env bash
# SPEC's per-entry files (`docs/changelog/`, `docs/status/`, `scripts/axioms/`): each is named and
# shaped as its README says, so the scripts that print them in order print every one.
#
# - `docs/changelog/<version>.md` (or `<version>-b.md`, …): its first non-blank line is that
#   version's entry, `- **<version>** (…`, and it holds no other entry;
# - `docs/status/<entry>.md` and `docs/status/legacy/NN-<slug>.md`: not empty;
# - `scripts/axioms/*.names`: each line a name, a `--` comment or blank;
# - `scripts/changelog.sh`, `scripts/changelog.sh --version` and `scripts/status.sh` run.
set -euo pipefail
cd "$(dirname "$0")/.."
fail=0
bad() { echo "check-spec-files: $*" >&2; fail=1; }

for f in docs/changelog/*.md; do
  b=$(basename "$f" .md)
  [ "$b" = README ] && continue
  v=${b%%-*}
  [[ "$b" =~ ^[0-9]+(\.[0-9]+)+(-[b-z])?$ ]] || { bad "$f: not named <version>.md or <version>-<letter>.md"; continue; }
  first=$(grep -m1 -v '^[[:space:]]*$' "$f" || true)
  [[ "$first" == "- **$v** ("* ]] || bad "$f: does not start with the entry \`- **$v** (…\`"
  n=$(grep -c '^- \*\*[0-9]' "$f" || true)
  [ "$n" = 1 ] || bad "$f: holds $n entries, not 1"
done

for f in docs/status/*.md docs/status/legacy/*.md; do
  b=$(basename "$f" .md)
  [ "$b" = README ] && continue
  [ -s "$f" ] && grep -q '[^[:space:]]' "$f" || bad "$f: empty"
done

for f in scripts/axioms/*.names; do
  if grep -n -v -E '^(--.*|[[:space:]]*|[^[:space:]]+)$' "$f" >/dev/null; then
    bad "$f: a line that is not a name, a \`--\` comment or blank"
  fi
done

scripts/changelog.sh >/dev/null || bad "scripts/changelog.sh failed"
scripts/changelog.sh --version >/dev/null || bad "scripts/changelog.sh --version failed"
scripts/status.sh >/dev/null || bad "scripts/status.sh failed"
exit $fail
