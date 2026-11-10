# Sourced by compile-corpus.sh and book-doctest.sh: when the source stage runs. The source stage
# is `Support`'s interpreter (`bcc interp`), the reference semantics. A golden (a corpus
# `<name>.out`, a book block's `-- answer:` and `-- output:` lines) is a cached record of what it
# prints; the clos, flat and wasm stages are always checked against the golden.
#
# The key. `bcc interp --key` (Reference/Key.lean) is a sha256 over what decides the source
# stage's output on a program: the interpreter digest (scripts/interp-digest.sh: the source of
# the interpreter and of the machine it steps), the fuel, the input and arguments, and the
# elaborated term the interpreter runs, every library definition it reaches included. It
# elaborates the program and runs nothing.
#
# A verified golden is recorded with its key:
#   corpus  `<name>.key` beside `<name>.out`: one line, `<key> <golden>`, `<golden>` the sha256
#           of the program's `.out`, `.err` and `.status` (`goldenHash`);
#   book    book/keys/<chapter path under book/src>.keys: one line per verified `bc` block, in
#           the chapter's order, `<block> <key>`, `<block>` the sha256 of the block's attributes
#           and text, which hold its golden (`-- answer:`, `-- output:`) and its input.
#
# Unverified: no key is recorded for the golden, or the recorded line is not the current one
# (the program's term, its input, the interpreter or the golden changed). The source stage runs
# exactly on the unverified goldens; each script lists them, with their count.
#
#   BCC_SOURCE=1      the source stage runs on every program, and must match its golden: an
#                     explicit re-verify (`--source`, `make verify-goldens`)
#   BCC_SOURCE=0      it never runs (`ci-local.sh --changed`); an unverified golden is reported,
#                     not run
#   unset             it runs on exactly the unverified goldens (the default)
#   BCC_WRITE_KEYS=1  record the key of every golden the source stage verified on this run. The
#                     default when the source stage runs by the key rule (BCC_SOURCE unset): a
#                     golden the interpreter has just reproduced gets its current key, so a key is
#                     never stale for long. A key that cannot be written (a read-only tree) is
#                     reported and skipped; the run's result does not depend on it, since a key
#                     only decides whether the source stage runs. `--write-keys` (`make keys`) asks
#                     for it under `--source` too; `--write-goldens` records the keys of the
#                     goldens it writes. BCC_WRITE_KEYS=0 writes none.
BCC_SOURCE=${BCC_SOURCE:-}
if [ -z "$BCC_SOURCE" ]; then BCC_WRITE_KEYS=${BCC_WRITE_KEYS:-1}; else BCC_WRITE_KEYS=${BCC_WRITE_KEYS:-0}; fi
source_digest=$(scripts/interp-digest.sh)
export BCC_SOURCE BCC_WRITE_KEYS source_digest

# sourceKey FILE INPUT [ARG…]: the source stage's key on FILE with standard input INPUT.
sourceKey() {
  local f=$1 in=$2; shift 2
  "${bcc:-.lake/build/bin/bcc}" interp --key --digest "$source_digest" "$f" -- "$@" < "$in"
}
# goldenHash BASE: the sha256 of corpus program BASE's golden, `.out`, `.err` and `.status`
# (each named, with its length; an absent file is empty).
goldenHash() {
  local x
  for x in out err status; do
    if [ -f "$1.$x" ]; then printf '%s %s\n' "$x" "$(wc -c < "$1.$x" | tr -d ' ')"; cat "$1.$x"
    else printf '%s 0\n' "$x"; fi
  done | shasum -a 256 | cut -d' ' -f1
}
# corpusKeyLine FILE: the line FILE's `.key` holds when its golden is verified now.
corpusKeyLine() {
  local f=$1 base=${1%.bc} in=/dev/null line args=()
  [ -f "$base.in" ] && in="$base.in"
  if [ -f "$base.args" ]; then
    while IFS= read -r line || [ -n "$line" ]; do args+=("$line"); done < "$base.args"
  fi
  printf '%s %s\n' "$(sourceKey "$f" "$in" "${args[@]+"${args[@]}"}")" "$(goldenHash "$base")"
}
# corpusVerified FILE LINE: whether FILE's recorded key is LINE (`corpusKeyLine`).
corpusVerified() {
  [ -f "${1%.bc}.key" ] && [ "$(cat "${1%.bc}.key")" = "$2" ]
}
# blockHash ATTRS FILE: a book block's hash, over its attributes and its text.
blockHash() { { printf '%s\n' "$1"; cat "$2"; } | shasum -a 256 | cut -d' ' -f1; }
export -f sourceKey goldenHash corpusKeyLine corpusVerified blockHash
