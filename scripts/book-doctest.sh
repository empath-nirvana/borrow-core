#!/usr/bin/env bash
# Doc-test the book. Every fenced block in book/src/**/*.md whose info string starts with `bc` is
# a program, run by its attributes as rustdoc runs Rust blocks:
#
#   ```bc          must check, and `main` must print the value on its `-- answer:` line and then
#                  `live 0`, compiled (`bcc run`: Backend2, the default backend, or the old
#                  backend with `--backend old`), and at the source stage (`bcc interp`) when it
#                  runs (below). A program with standard I/O (SPEC §11) reads its
#                  `-- stdin:` lines, each followed by a newline, as standard input, and must
#                  write its `-- output:` lines, each followed by a newline, before the value.
#                  A block with `-- output:` lines and no `-- answer:` line answers `()`: its
#                  `main` returns `1`.
#   ```bc,check    must check (a library, or a `main` whose value is not printed)
#   ```bc,reject   must parse and be rejected by the checker with the message on its `-- expect:`
#                  line (`line:col: message`, the line counted from the block's first line)
#   ```bc,ignore   not run (a fragment, or a planned feature)
#
# Failures are reported as `book/src/<file>.md:<line>`, the line of the block's opening fence.
# The binary is $BCC, or .lake/build/bin/bcc (built by `lake build`).
#
#     scripts/book-doctest.sh [--source] [--write-keys] [--backend old|new] [book/src/<file>.md[:<line>]…]
#
# runs every block, or the blocks of the files named (the one whose fence is at <line>).
#
# The source stage (scripts/source-stage.sh). A block's `-- answer:` and `-- output:` lines are
# its golden: a record of what `Support`'s interpreter prints. A verified block is recorded in
# book/keys/<chapter path under book/src>.keys as `<block> <key>`: the hash of its attributes and
# text (which hold its golden and its input), and its source stage's key (`bcc interp --key`). By
# default the interpreter runs only on the blocks that are unverified, whose line is in no keys
# file (the block, the term it elaborates to, or the interpreter changed; a block is matched
# wherever it moved); with `--source` (or `BCC_SOURCE=1`) on every block; with `BCC_SOURCE=0` on
# none. Without wasmtime, the interpreter is the only stage, and runs on every block (except with
# `BCC_SOURCE=0`). The blocks it ran on are listed at the end, with their count. `--write-keys`
# rewrites the keys file of each chapter run: a line for each of its blocks verified now (by the
# source stage on this run, or by its recorded line), the lines of its blocks not run kept.
set -euo pipefail
cd "$(dirname "$0")/.."
bcc=${BCC:-.lake/build/bin/bcc}
[ -x "$bcc" ] || { echo "no bcc at $bcc: run \`lake build bcc\`, or set BCC"; exit 1; }
want=()
backend=new
usage() { echo "usage: scripts/book-doctest.sh [--source] [--write-keys] [--backend old|new] [book/src/<file>.md[:<line>]…]"; exit 2; }
while [ $# -gt 0 ]; do
  case "$1" in
    --source) export BCC_SOURCE=1 ;;
    --write-keys) export BCC_WRITE_KEYS=1 ;;
    --backend) case "${2:-}" in old|new) backend=$2; shift ;; *) usage ;; esac ;;
    -*) usage ;;
    *) want+=("$1") ;;
  esac
  shift
done
if command -v wasmtime >/dev/null; then wasm=1; else wasm=0; echo "wasmtime is not on PATH: \`bc\` blocks run under the interpreter only"; fi

. scripts/par.sh
. scripts/source-stage.sh
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Extract the blocks of the .md files on standard input into directory $1: one file per block,
# and a manifest line `n<TAB>attrs<TAB>md file<TAB>fence line`, with `run` for a plain `bc`.
extract() {
  xargs awk -v dir="$1" '
  FNR == 1 { inb = 0 }
  /^[[:space:]]*```/ {
    if (!inb) {
      info = $0; sub(/^[[:space:]]*```[[:space:]]*/, "", info); sub(/[[:space:]]+$/, "", info)
      if (info == "bc" || info ~ /^bc,/) {
        inb = 1; n++; file = dir "/" n ".bc"; printf "" > file
        attrs = info; sub(/^bc,?/, "", attrs); if (attrs == "") attrs = "run"
        printf "%d\t%s\t%s\t%d\n", n, attrs, FILENAME, FNR > (dir "/manifest")
        next
      }
    } else if (inb) { inb = 0; close(file); next }
  }
  inb { print > file }
'
}
find book/src -name '*.md' | sort | extract "$tmp"
[ -f "$tmp/manifest" ] || { echo "no \`bc\` blocks found"; exit 1; }
cp "$tmp/manifest" "$tmp/manifest.all"
# The recorded lines (`<block> <key>`) of every chapter: a block whose line is among them is
# verified.
keysOf() { echo "book/keys/${1#book/src/}.keys"; }
find book/keys -name '*.keys' -exec cat {} + 2>/dev/null > "$tmp/verified" || : > "$tmp/verified"
mkdir "$tmp/ok"
: > "$tmp/reran"
: > "$tmp/written"
: > "$tmp/unverified"

fail() { echo "$1: $2"; shift 2; for l in "$@"; do echo "  $l"; done; }
# Block $1 of the manifest: exit 0 if it passes (or is ignored), 1 if not. Run in parallel by `par`.
block() {
  local n attrs md line f at want out in outl expect got src
  IFS=$'\t' read -r n attrs md line < <(awk -F'\t' -v n="$1" '$1 == n' "$tmp/manifest")
  f="$tmp/$n.bc"; at="$md:$line"
  case "$attrs" in
    ignore) return 0 ;;
    run)
      want=$(sed -n '/^-- answer: /{s///p;q;}' "$f")
      if [ -z "$want" ] && grep -q '^-- output:' "$f"; then want='()'; fi
      if [ -z "$want" ]; then fail "$at" "a \`bc\` block needs an \`-- answer:\` or \`-- output:\` line (or mark it \`bc,check\`)"; return 1; fi
      if ! out=$("$bcc" check "$f" 2>&1); then fail "$at" "rejected, but must check" "${out#"$f:"}"; return 1; fi
      in="$tmp/$n.in"; : > "$in"
      sed -n 's/^-- stdin: \{0,1\}//p' "$f" | while IFS= read -r l; do printf '%s\n' "$l"; done > "$in"
      outl=$(sed -n 's/^-- output: \{0,1\}//p' "$f" | while IFS= read -r l; do printf '%s\n' "$l"; done)
      if [ -n "$outl" ]; then expect=$(printf '%s\n%s\nlive 0' "$outl" "$want")
      else expect=$(printf '%s\nlive 0' "$want"); fi
      # The source stage: on every block, on none, or on an unverified one. `kl` is the block's
      # line in its chapter's keys file.
      kl=""; verified=0
      if [ "$BCC_SOURCE" != 1 ] || [ "$BCC_WRITE_KEYS" = 1 ]; then
        kl="$(blockHash "$attrs" "$f") $(sourceKey "$f" "$in")"
        grep -qxF "$kl" "$tmp/verified" && verified=1
      fi
      case "$BCC_SOURCE" in
        1) src=1 ;;
        0) src=0
           if [ "$verified" = 0 ]; then
             echo "$at: unverified, not run at the source stage (scripts/book-doctest.sh $at runs it)"
             echo "$at" >> "$tmp/unverified"
           fi ;;
        *) if [ "$verified" = 0 ]; then src=1; echo "$at" >> "$tmp/reran"
           elif [ "$wasm" = 0 ]; then src=1; else src=0; fi ;;
      esac
      if [ "$src" = 1 ]; then
        got=$("$bcc" interp "$f" < "$in" 2>&1) || true
        if [ "$got" != "$expect" ]; then
          fail "$at" "interpreter output differs" "want: $(echo "$expect" | tr '\n' ' ')" "got:  $(echo "$got" | tr '\n' ' ')"; return 1
        fi
      fi
      if [ -n "$kl" ] && { [ "$src" = 1 ] || [ "$verified" = 1 ]; }; then echo "$kl" > "$tmp/ok/$n"; fi
      if [ "$wasm" = 1 ]; then
        got=$("$bcc" run --backend "$backend" "$f" < "$in" 2>&1) || true
        if [ "$got" != "$expect" ]; then
          fail "$at" "compiled output differs" "want: $(echo "$expect" | tr '\n' ' ')" "got:  $(echo "$got" | tr '\n' ' ')"; return 1
        fi
      fi
      ;;
    check)
      if ! out=$("$bcc" check "$f" 2>&1); then fail "$at" "rejected, but must check" "${out#"$f:"}"; return 1; fi
      ;;
    reject)
      want=$(sed -n '/^-- expect: /{s///p;q;}' "$f")
      if [ -z "$want" ]; then fail "$at" "a \`bc,reject\` block needs an \`-- expect:\` line"; return 1; fi
      if ! out=$("$bcc" parse "$f" 2>&1); then fail "$at" "does not parse, so it does not test the checker" "${out#"$f:"}"; return 1; fi
      if out=$("$bcc" check "$f" 2>&1); then fail "$at" "accepted, but must be rejected"; return 1; fi
      if [ "$out" != "$f:$want" ]; then fail "$at" "wrong error" "want: $want" "got:  ${out#"$f:"}"; return 1; fi
      ;;
    *) fail "$at" "unknown attributes \`bc,$attrs\` (use bc, bc,check, bc,reject or bc,ignore)"; return 1 ;;
  esac
}
export tmp bcc wasm backend
export -f fail block
# The blocks named (every block, when none is).
if [ ${#want[@]} -gt 0 ]; then
  : > "$tmp/selected"
  for w in "${want[@]}"; do
    case "$w" in
      *.md:*) awk -F'\t' -v m="${w%:*}" -v l="${w##*:}" '$3 == m && $4 == l' "$tmp/manifest" ;;
      *) awk -F'\t' -v m="$w" '$3 == m' "$tmp/manifest" ;;
    esac >> "$tmp/selected"
  done
  [ -s "$tmp/selected" ] || { echo "no \`bc\` block at ${want[*]}"; exit 1; }
  mv "$tmp/selected" "$tmp/manifest"
fi
total=$(wc -l < "$tmp/manifest" | tr -d ' ')
ignored=$(awk -F'\t' '$2 == "ignore"' "$tmp/manifest" | wc -l | tr -d ' ')
par block $(cut -f1 "$tmp/manifest")
bad=$par_failed
ran=$((total - ignored - bad))
# --write-keys: each chapter run gets, in its order, the line of each of its `bc` blocks verified
# on this run; a block not run keeps its recorded line.
if [ "$BCC_WRITE_KEYS" = 1 ]; then
  for md in $(cut -f3 "$tmp/manifest" | sort -u); do
    kf=$(keysOf "$md")
    while IFS=$'\t' read -r n attrs _ _; do
      [ "$attrs" = run ] || continue
      if [ -f "$tmp/ok/$n" ]; then cat "$tmp/ok/$n"
      elif ! awk -F'\t' -v n="$n" '$1 == n { f = 1 } END { exit !f }' "$tmp/manifest" && [ -f "$kf" ]; then
        grep -m1 "^$(blockHash "$attrs" "$tmp/$n.bc") " "$kf" || true
      fi
    done < <(awk -F'\t' -v m="$md" '$3 == m' "$tmp/manifest.all") > "$tmp/keys.new"
    if [ -s "$tmp/keys.new" ]; then
      if cmp -s "$tmp/keys.new" "$kf"; then :
      elif mkdir -p "$(dirname "$kf")" 2> /dev/null && cp "$tmp/keys.new" "$kf" 2> /dev/null; then echo "$kf" >> "$tmp/written"
      else echo "$kf: not writable, its keys not written"; fi
    elif [ -f "$kf" ]; then rm -f "$kf" 2> /dev/null && echo "$kf (removed)" >> "$tmp/written"; fi
  done
  if [ -s "$tmp/written" ]; then
    echo "keys written: $(wc -l < "$tmp/written" | tr -d ' ') chapter file(s) under book/keys/ (commit them with the change)"
    sed 's/^/  /' "$tmp/written"
  fi
fi
case "$BCC_SOURCE" in
  1) echo "source stage: every block (--source)" ;;
  0) echo "source stage: not run (BCC_SOURCE=0); $(wc -l < "$tmp/unverified" | tr -d ' ') unverified block(s)"
     sed 's/^/  /' "$tmp/unverified" ;;
  *) echo "source stage: re-ran on $(wc -l < "$tmp/reran" | tr -d ' ') block(s) whose key is missing or changed (--source runs every block)"
     sed 's/^/  /' "$tmp/reran" ;;
esac
echo "$total block(s) ($([ "$backend" = new ] && echo Backend2 || echo "the old backend")): $ran passed, $ignored ignored, $bad failure(s)."
[ "$bad" -eq 0 ]
