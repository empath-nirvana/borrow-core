#!/usr/bin/env bash
# A checkout's `.lake/packages` (Mathlib and the other dependencies, about 167,000 files) as a
# symlink to a shared read-only store, so a new worktree needs no copy of them.
#
#     scripts/lake-packages.sh share <source checkout> <checkout>
#     scripts/lake-packages.sh check [checkout]
#     scripts/lake-packages.sh unshare [checkout]
#
# The store is `<store>/<key>`: the key hashes `lake-manifest.json` (as JSON) and `lean-toolchain`, which
# alone determine the packages, and the store is `.lake-packages` beside the main checkout (or
# `$BORROW_CORE_PACKAGES_STORE`). A key's directory is created once, from a checkout whose
# packages have that key, and made read-only, so no worktree can change it under the others: a
# build, `lake env` and `lake exe cache get` only read it, and whatever would write to it fails.
#
# * `share` links `<checkout>/.lake/packages` to the store of its key, creating the store from
#   `<source checkout>`'s packages if needed. With no store and no matching source it does
#   nothing (Lake then fetches the packages).
# * `check` (run by `make`'s `tools`) follows a manifest or toolchain change: when the checkout's
#   packages link to the store of another key, it relinks them to the store of the current key
#   if there is one, and otherwise unshares them, so Lake updates a copy of the checkout's own. A
#   checkout whose `.lake/packages` is a directory is left as it is.
# * `unshare` replaces the link by a writable clone of the store, the checkout's own.
set -euo pipefail

clone() { # clone <src> <dst>: copy-on-write where the file system has it
  if cp -cR "$1" "$2" 2>/dev/null; then :
  elif cp -R --reflink=auto "$1" "$2" 2>/dev/null; then :
  else rm -rf "$2"; cp -R "$1" "$2"; fi
}
# The manifest is read as JSON, so a reformatting (as `lake update` writes) keeps the key.
key() {
  { python3 -c 'import json, sys; print(json.dumps(json.load(open(sys.argv[1])), sort_keys=True))' \
      "$1/lake-manifest.json"; cat "$1/lean-toolchain"; } | shasum -a 256 | cut -c1-16
}
store() {
  local main
  main=$(git -C "$1" worktree list --porcelain | sed -n '1s/^worktree //p')
  echo "${BORROW_CORE_PACKAGES_STORE:-$(dirname "$main")/.lake-packages}"
}
unshare() {
  local top=$1 shared
  shared=$(cd "$top/.lake/packages" && pwd -P)
  echo "lake-packages: cloning $shared into $top/.lake/packages (the checkout's own)"
  rm -rf "$top/.lake/packages.tmp"
  clone "$shared" "$top/.lake/packages.tmp"
  chmod -R u+w "$top/.lake/packages.tmp"
  rm "$top/.lake/packages"
  mv "$top/.lake/packages.tmp" "$top/.lake/packages"
}

cmd=${1:-}
case "$cmd" in
share)
  [ $# -eq 3 ] || { echo "usage: scripts/lake-packages.sh share <source checkout> <checkout>"; exit 2; }
  from=$2; top=$3; k=$(key "$top"); s=$(store "$top")
  [ ! -e "$top/.lake/packages" ] || { echo "$top/.lake/packages exists"; exit 1; }
  if [ ! -d "$s/$k" ] && [ -d "$from/.lake/packages" ] && [ "$(key "$from")" = "$k" ]; then
    # Cloned aside and renamed into place, so a store directory is always complete. `rename(2)`
    # onto a directory that is not empty fails, so if another creator got there first this copy goes.
    echo "lake-packages: creating the store $s/$k from $from"
    mkdir -p "$s"
    tmp=$(mktemp -d "$s/.$k.XXXXXX")
    clone "$(cd "$from/.lake/packages" && pwd -P)" "$tmp/p"
    chmod -R a-w "$tmp/p"
    # Moving a directory to another parent needs write permission on it; it is taken away after.
    chmod u+w "$tmp/p"
    if python3 -c 'import os, sys; os.rename(sys.argv[1], sys.argv[2])' "$tmp/p" "$s/$k" 2>/dev/null
    then chmod a-w "$s/$k"; else chmod -R u+w "$tmp/p"; rm -rf "$tmp/p"; fi
    rmdir "$tmp"
  fi
  if [ -d "$s/$k" ]; then
    mkdir -p "$top/.lake"
    ln -s "$s/$k" "$top/.lake/packages"
    echo "lake-packages: $top/.lake/packages -> $s/$k (shared, read-only)"
  else
    echo "lake-packages: no store or source for key $k: Lake fetches the packages"
  fi
  ;;
check)
  top=${2:-$(git rev-parse --show-toplevel)}
  [ -L "$top/.lake/packages" ] || exit 0
  k=$(key "$top"); s=$(store "$top")
  [ "$(basename "$(readlink "$top/.lake/packages")")" != "$k" ] || exit 0
  if [ -d "$s/$k" ]; then
    rm "$top/.lake/packages"; ln -s "$s/$k" "$top/.lake/packages"
    echo "lake-packages: manifest or toolchain changed: $top/.lake/packages -> $s/$k"
  else
    echo "lake-packages: manifest or toolchain changed, and no store has key $k"
    unshare "$top"
  fi
  ;;
unshare)
  top=${2:-$(git rev-parse --show-toplevel)}
  if [ -L "$top/.lake/packages" ]; then unshare "$top"; else echo "lake-packages: $top/.lake/packages is the checkout's own"; fi
  ;;
*) echo "usage: scripts/lake-packages.sh share <source> <checkout> | check [checkout] | unshare [checkout]"; exit 2 ;;
esac
