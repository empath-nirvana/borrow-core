# Sourced by compile-corpus.sh and book-doctest.sh: when the source stage runs. The source stage
# is `Support`'s interpreter (`bcc interp`), the reference semantics. A golden (a corpus
# `<name>.out`, a book block's `-- answer:` and `-- output:` lines) is a cached record of what it
# prints; the clos, flat and wasm stages are always checked against the golden.
#
#   BCC_SOURCE=1   the source stage runs on every program too, and must match its golden
#                  (`--source`, `make gate-full`)
#   BCC_SOURCE=0   it never runs (`ci-local.sh --changed`); a program whose golden is unverified
#                  is reported, not run
#   unset          it runs on exactly the programs whose golden is unverified (the default)
#
# Unverified: the program or its golden differs from the merge base with origin/main (or from the
# commit `CI_LOCAL_BASE` names), or is new. Committed, staged, unstaged and untracked changes
# all count. An unchanged program and golden were checked at the source stage by the gate that
# merged them (the full gate runs the source stage whenever the interpreter or the compiler
# changes: `ci-local.sh`), so they agree with the reference semantics. Without a merge base,
# every golden is unverified.
BCC_SOURCE=${BCC_SOURCE:-}
source_base=""
source_changed=""
if [ "$BCC_SOURCE" != 1 ]; then
  if source_base=${CI_LOCAL_BASE:-$(git merge-base origin/main HEAD 2>/dev/null)}; then
    source_changed=$({ git diff --name-only "$source_base"; git ls-files --others --exclude-standard; } | sort -u)
    source_base=$(git rev-parse --short "$source_base")
  else
    source_base=""
    echo "no merge base with origin/main: every golden is unverified"
  fi
fi
export BCC_SOURCE source_base source_changed
# unverified PATH...: whether any PATH differs from the merge base (all do, without one).
unverified() {
  [ -n "$source_base" ] || return 0
  local p
  for p in "$@"; do printf '%s\n' "$source_changed" | grep -qxF "$p" && return 0; done
  return 1
}
export -f unverified
