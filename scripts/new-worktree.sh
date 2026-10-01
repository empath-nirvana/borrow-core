#!/usr/bin/env bash
# A new worktree on a new branch from origin/main, with a warm build: the build directory `.lake`
# of an existing checkout (by default the main one) cloned copy-on-write, so `lake build`
# rebuilds only the modules that differ instead of starting cold (about 17,800 jobs).
#
#     scripts/new-worktree.sh <branch> [dir]      dir defaults to ../<repo>-<branch>
#     scripts/new-worktree.sh --from <checkout> <branch> [dir]
#
# The clone is as warm as its source: a checkout last built at origin/main rebuilds only what the
# branch changes. On APFS (macOS) the clone is `cp -c`, and on a reflink file system (btrfs, XFS)
# `cp --reflink=auto`: either costs no space until a file is rewritten. Elsewhere it is a copy.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
from=""
if [ "${1:-}" = "--from" ]; then from=$2; shift 2; fi
[ $# -ge 1 ] && [ $# -le 2 ] || { echo "usage: scripts/new-worktree.sh [--from <checkout>] <branch> [dir]"; exit 2; }
branch=$1
# The main worktree is the first that `git worktree list` names.
main=$(git -C "$here" worktree list --porcelain | sed -n '1s/^worktree //p')
[ -n "$from" ] || from=$main
dir=${2:-$(dirname "$main")/$(basename "$main")-$(echo "$branch" | tr '/' '-')}
[ ! -e "$dir" ] || { echo "$dir exists"; exit 1; }

git -C "$here" fetch origin
git -C "$here" worktree add "$dir" -b "$branch" origin/main
if [ -d "$from/.lake" ]; then
  echo "cloning $from/.lake"
  if cp -cR "$from/.lake" "$dir/.lake" 2>/dev/null; then :
  elif cp -R --reflink=auto "$from/.lake" "$dir/.lake" 2>/dev/null; then :
  else rm -rf "$dir/.lake"; cp -R "$from/.lake" "$dir/.lake"; fi
else
  echo "no $from/.lake: the worktree starts cold (\`make bcc\` fetches Mathlib's cache)"
fi
echo "worktree $dir on $branch (from origin/main); next: cd $dir && lake build"
