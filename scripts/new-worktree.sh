#!/usr/bin/env bash
# A new worktree on a new branch from origin/main, with a warm build, so `lake build` rebuilds only
# the modules that differ instead of starting cold (about 18,600 jobs).
#
#     scripts/new-worktree.sh <branch> [dir]      dir defaults to ../<repo>-<branch>
#     scripts/new-worktree.sh --from <checkout> <branch> [dir]
#
# `.lake` has two parts:
#
# * `.lake/build` (this package's outputs, about 9,000 files) and `.lake/config` (the elaborated
#   lakefile) are cloned from a source checkout.
#   Without `--from`, the source is the checkout among `git worktree list` whose Lean inputs
#   (`*.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, working tree included)
#   differ from origin/main in the fewest files, among those with the same toolchain and a built
#   `bcc`; ties go to the most recently built. The clone is as warm as its source: Lake rebuilds
#   whatever the source's build does not match.
# * `.lake/packages` (Mathlib and the other dependencies, about 167,000 files) is a symlink to the
#   shared read-only store for its manifest and toolchain (`scripts/lake-packages.sh`).
#
# On APFS (macOS) a clone is `cp -c`, and on a reflink file system (btrfs, XFS)
# `cp --reflink=auto`: either costs no space until a file is rewritten. Elsewhere it is a copy.
set -euo pipefail

here=$(cd "$(dirname "$0")/.." && pwd)
from=""
if [ "${1:-}" = "--from" ]; then from=$2; shift 2; fi
[ $# -ge 1 ] && [ $# -le 2 ] || { echo "usage: scripts/new-worktree.sh [--from <checkout>] <branch> [dir]"; exit 2; }
branch=$1
# The main worktree is the first that `git worktree list` names.
main=$(git -C "$here" worktree list --porcelain | sed -n '1s/^worktree //p')
dir=${2:-$(dirname "$main")/$(basename "$main")-$(echo "$branch" | tr '/' '-')}
[ ! -e "$dir" ] || { echo "$dir exists"; exit 1; }

git -C "$here" fetch origin
git -C "$here" worktree add "$dir" -b "$branch" origin/main
toolchain=$(cat "$dir/lean-toolchain")

if [ -z "$from" ]; then
  # One line per candidate, `<differing Lean inputs> <bcc mtime> <path>`; the best sorts first.
  from=$(git -C "$here" worktree list --porcelain | sed -n 's/^worktree //p' | grep -vxF "$dir" |
    while read -r c; do
      [ -x "$c/.lake/build/bin/bcc" ] && [ -d "$c/.lake/build/lib/lean" ] || continue
      [ "$(cat "$c/lean-toolchain" 2>/dev/null)" = "$toolchain" ] || continue
      printf '%s\0' "$c"
    done |
    xargs -0 -P 8 -I{} sh -c '
      n=$(git -C "$1" diff --name-only origin/main -- "*.lean" lakefile.toml lake-manifest.json lean-toolchain | wc -l) || exit 0
      t=$(stat -f %m "$1/.lake/build/bin/bcc" 2>/dev/null || stat -c %Y "$1/.lake/build/bin/bcc")
      echo $n $t "$1"' _ {} |
    sort -k1,1n -k2,2nr | head -1 | cut -d' ' -f3-)
  if [ -n "$from" ]; then echo "source: $from"; fi
fi

mkdir -p "$dir/.lake"
if [ -n "$from" ] && [ -d "$from/.lake/build" ]; then
  for d in build config; do
    [ -d "$from/.lake/$d" ] || continue
    echo "cloning $from/.lake/$d"
    if cp -cR "$from/.lake/$d" "$dir/.lake/$d" 2>/dev/null; then :
    elif cp -R --reflink=auto "$from/.lake/$d" "$dir/.lake/$d" 2>/dev/null; then :
    else rm -rf "$dir/.lake/$d"; cp -R "$from/.lake/$d" "$dir/.lake/$d"; fi
  done
else
  echo "no source build: the worktree starts cold"
fi

"$here/scripts/lake-packages.sh" share "${from:-$dir}" "$dir"
echo "worktree $dir on $branch (from origin/main); next: cd $dir && lake build"
