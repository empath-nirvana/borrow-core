#!/usr/bin/env bash
# Doc-test the book. Every fenced block in book/src/**/*.md whose info string starts with `bc` is
# a program, run by its attributes as rustdoc runs Rust blocks:
#
#   ```bc          must check, and `main` must print the value on its `-- answer:` line and then
#                  `live 0`, compiled (`bcc run`), and at the source stage (`bcc interp`) when it
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
#     scripts/book-doctest.sh [--source] [book/src/<file>.md[:<line>]…]
#
# runs every block, or the blocks of the files named (the one whose fence is at <line>).
#
# The source stage (scripts/source-stage.sh). A block's `-- answer:` and `-- output:` lines are
# its golden: a record of what `Support`'s interpreter prints. By default the interpreter runs
# only on the blocks that are unverified, that is new or changed since the merge base with
# origin/main (a block is matched by its attributes and text, wherever it moved); with `--source`
# (or `BCC_SOURCE=1`) on every block; with `BCC_SOURCE=0` on none. Without wasmtime, the
# interpreter is the only stage, and runs on every block (except with `BCC_SOURCE=0`).
set -euo pipefail
cd "$(dirname "$0")/.."
bcc=${BCC:-.lake/build/bin/bcc}
[ -x "$bcc" ] || { echo "no bcc at $bcc: run \`lake build bcc\`, or set BCC"; exit 1; }
want=()
while [ $# -gt 0 ]; do
  case "$1" in
    --source) export BCC_SOURCE=1 ;;
    -*) echo "usage: scripts/book-doctest.sh [--source] [book/src/<file>.md[:<line>]…]"; exit 2 ;;
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
# A block's key: its attributes and its text.
key() { { printf '%s\n' "$1"; cat "$2"; } | cksum; }
find book/src -name '*.md' | sort | extract "$tmp"
[ -f "$tmp/manifest" ] || { echo "no \`bc\` blocks found"; exit 1; }
# The keys of the merge base's blocks: a block among them is verified.
: > "$tmp/verified"
if [ "$BCC_SOURCE" != 1 ] && [ -n "$source_base" ]; then
  mkdir "$tmp/base"
  git ls-tree -r --name-only "$source_base" book/src | grep '\.md$' | while read -r p; do
    mkdir -p "$tmp/base/$(dirname "$p")"; git show "$source_base:$p" > "$tmp/base/$p"
  done
  (cd "$tmp/base" && find book/src -name '*.md' | sort | extract "$tmp/base")
  if [ -f "$tmp/base/manifest" ]; then
    while IFS=$'\t' read -r n attrs _ _; do key "$attrs" "$tmp/base/$n.bc"; done < "$tmp/base/manifest" > "$tmp/verified"
  fi
fi

fail() { echo "$1: $2"; shift 2; for l in "$@"; do echo "  $l"; done; }
# Block $1 of the manifest: exit 0 if it passes (or is ignored), 1 if not. Run in parallel by `par`.
block() {
  local n attrs md line f at want out in outl expect got src
  IFS=$'\t' read -r n attrs md line < <(awk -F'\t' -v n="$1" '$1 == n' "$tmp/manifest")
  f="$tmp/$n.bc"; at="$md:$line"
  case "$attrs" in
    ignore) return 0 ;;
    run)
      want=$(sed -n 's/^-- answer: //p' "$f" | head -1)
      if [ -z "$want" ] && grep -q '^-- output:' "$f"; then want='()'; fi
      if [ -z "$want" ]; then fail "$at" "a \`bc\` block needs an \`-- answer:\` or \`-- output:\` line (or mark it \`bc,check\`)"; return 1; fi
      if ! out=$("$bcc" check "$f" 2>&1); then fail "$at" "rejected, but must check" "${out#"$f:"}"; return 1; fi
      in="$tmp/$n.in"; : > "$in"
      sed -n 's/^-- stdin: \{0,1\}//p' "$f" | while IFS= read -r l; do printf '%s\n' "$l"; done > "$in"
      outl=$(sed -n 's/^-- output: \{0,1\}//p' "$f" | while IFS= read -r l; do printf '%s\n' "$l"; done)
      if [ -n "$outl" ]; then expect=$(printf '%s\n%s\nlive 0' "$outl" "$want")
      else expect=$(printf '%s\nlive 0' "$want"); fi
      # The source stage: on every block, on none, or on an unverified one.
      case "$BCC_SOURCE" in
        1) src=1 ;;
        0) src=0; grep -qxF "$(key "$attrs" "$f")" "$tmp/verified" ||
             echo "$at: unverified: changed since $source_base, not run at the source stage (scripts/book-doctest.sh $at runs it)" ;;
        *) if [ "$wasm" = 0 ] || ! grep -qxF "$(key "$attrs" "$f")" "$tmp/verified"; then src=1; else src=0; fi ;;
      esac
      if [ "$src" = 1 ]; then
        got=$("$bcc" interp "$f" < "$in" 2>&1) || true
        if [ "$got" != "$expect" ]; then
          fail "$at" "interpreter output differs" "want: $(echo "$expect" | tr '\n' ' ')" "got:  $(echo "$got" | tr '\n' ' ')"; return 1
        fi
      fi
      if [ "$wasm" = 1 ]; then
        got=$("$bcc" run "$f" < "$in" 2>&1) || true
        if [ "$got" != "$expect" ]; then
          fail "$at" "compiled output differs" "want: $(echo "$expect" | tr '\n' ' ')" "got:  $(echo "$got" | tr '\n' ' ')"; return 1
        fi
      fi
      ;;
    check)
      if ! out=$("$bcc" check "$f" 2>&1); then fail "$at" "rejected, but must check" "${out#"$f:"}"; return 1; fi
      ;;
    reject)
      want=$(sed -n 's/^-- expect: //p' "$f" | head -1)
      if [ -z "$want" ]; then fail "$at" "a \`bc,reject\` block needs an \`-- expect:\` line"; return 1; fi
      if ! out=$("$bcc" parse "$f" 2>&1); then fail "$at" "does not parse, so it does not test the checker" "${out#"$f:"}"; return 1; fi
      if out=$("$bcc" check "$f" 2>&1); then fail "$at" "accepted, but must be rejected"; return 1; fi
      if [ "$out" != "$f:$want" ]; then fail "$at" "wrong error" "want: $want" "got:  ${out#"$f:"}"; return 1; fi
      ;;
    *) fail "$at" "unknown attributes \`bc,$attrs\` (use bc, bc,check, bc,reject or bc,ignore)"; return 1 ;;
  esac
}
export tmp bcc wasm
export -f fail block key
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
case "$BCC_SOURCE" in
  1) echo "source stage: every block" ;;
  0) echo "source stage: not run (BCC_SOURCE=0)" ;;
  *) echo "source stage: the blocks unverified since ${source_base:-(no merge base)} only (--source runs every block)" ;;
esac
echo "$total block(s): $ran passed, $ignored ignored, $bad failure(s)."
[ "$bad" -eq 0 ]
