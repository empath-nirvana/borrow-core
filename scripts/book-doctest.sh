#!/usr/bin/env bash
# Doc-test the book. Every fenced block in book/src/**/*.md whose info string starts with `bc` is
# a program, run by its attributes as rustdoc runs Rust blocks:
#
#   ```bc          must check, and `main` must print the value on its `-- answer:` line and then
#                  `live 0`, under the interpreter (`bcc interp`) and compiled (`bcc run`, when
#                  wasmtime is on PATH). A program with standard I/O (SPEC §11) reads its
#                  `-- stdin:` lines, each followed by a newline, as standard input, and must
#                  write its `-- output:` lines, each followed by a newline, before the value.
#   ```bc,check    must check (a library, or a `main` whose value is not printed)
#   ```bc,reject   must parse and be rejected by the checker with the message on its `-- expect:`
#                  line (`line:col: message`, the line counted from the block's first line)
#   ```bc,ignore   not run (a fragment, or a planned feature)
#
# Failures are reported as `book/src/<file>.md:<line>`, the line of the block's opening fence.
# The binary is $BCC, or .lake/build/bin/bcc (built by `lake build`).
set -euo pipefail
cd "$(dirname "$0")/.."
bcc=${BCC:-.lake/build/bin/bcc}
[ -x "$bcc" ] || { echo "no bcc at $bcc: run \`lake build bcc\`, or set BCC"; exit 1; }
if command -v wasmtime >/dev/null; then wasm=1; else wasm=0; echo "wasmtime is not on PATH: \`bc\` blocks run under the interpreter only"; fi

. scripts/par.sh
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# Extract: one file per block, and a manifest line `n<TAB>attrs<TAB>md file<TAB>fence line`,
# with `run` for a plain `bc`.
find book/src -name '*.md' | sort | xargs awk -v dir="$tmp" '
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
[ -f "$tmp/manifest" ] || { echo "no \`bc\` blocks found"; exit 1; }

fail() { echo "$1: $2"; shift 2; for l in "$@"; do echo "  $l"; done; }
# Block $1 of the manifest: exit 0 if it passes (or is ignored), 1 if not. Run in parallel by `par`.
block() {
  local n attrs md line f at want out in outl expect got
  IFS=$'\t' read -r n attrs md line < <(awk -F'\t' -v n="$1" '$1 == n' "$tmp/manifest")
  f="$tmp/$n.bc"; at="$md:$line"
  case "$attrs" in
    ignore) return 0 ;;
    run)
      want=$(sed -n 's/^-- answer: //p' "$f" | head -1)
      if [ -z "$want" ]; then fail "$at" "a \`bc\` block needs an \`-- answer:\` line (or mark it \`bc,check\`)"; return 1; fi
      if ! out=$("$bcc" check "$f" 2>&1); then fail "$at" "rejected, but must check" "${out#"$f:"}"; return 1; fi
      in="$tmp/$n.in"; : > "$in"
      sed -n 's/^-- stdin: \{0,1\}//p' "$f" | while IFS= read -r l; do printf '%s\n' "$l"; done > "$in"
      outl=$(sed -n 's/^-- output: \{0,1\}//p' "$f" | while IFS= read -r l; do printf '%s\n' "$l"; done)
      if [ -n "$outl" ]; then expect=$(printf '%s\n%s\nlive 0' "$outl" "$want")
      else expect=$(printf '%s\nlive 0' "$want"); fi
      got=$("$bcc" interp "$f" < "$in" 2>&1) || true
      if [ "$got" != "$expect" ]; then
        fail "$at" "interpreter output differs" "want: $(echo "$expect" | tr '\n' ' ')" "got:  $(echo "$got" | tr '\n' ' ')"; return 1
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
export -f fail block
total=$(wc -l < "$tmp/manifest" | tr -d ' ')
ignored=$(awk -F'\t' '$2 == "ignore"' "$tmp/manifest" | wc -l | tr -d ' ')
par block $(cut -f1 "$tmp/manifest")
bad=$par_failed
ran=$((total - ignored - bad))
echo "$total block(s): $ran passed, $ignored ignored, $bad failure(s)."
[ "$bad" -eq 0 ]
