#!/usr/bin/env bash
# Doc-test the book. Every fenced block in book/src/**/*.md whose info string starts with `bc` is
# a program, run by its attributes as rustdoc runs Rust blocks:
#
#   ```bc          must check, and `main` must print the value on its `-- answer:` line and then
#                  `live 0`, under the interpreter (`bcc interp`) and compiled (`bcc run`, when
#                  wasmtime is on PATH)
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

bad=0; total=0; ran=0; ignored=0
fail() { echo "$1: $2"; shift 2; for l in "$@"; do echo "  $l"; done; bad=$((bad + 1)); }
while IFS=$'\t' read -r n attrs md line; do
  total=$((total + 1))
  f="$tmp/$n.bc"; at="$md:$line"
  case "$attrs" in
    ignore) ignored=$((ignored + 1)); continue ;;
    run)
      want=$(sed -n 's/^-- answer: //p' "$f" | head -1)
      if [ -z "$want" ]; then fail "$at" "a \`bc\` block needs an \`-- answer:\` line (or mark it \`bc,check\`)"; continue; fi
      if ! out=$("$bcc" check "$f" 2>&1); then fail "$at" "rejected, but must check" "${out#"$f:"}"; continue; fi
      expect=$(printf '%s\nlive 0' "$want")
      got=$("$bcc" interp "$f" 2>&1) || true
      if [ "$got" != "$expect" ]; then
        fail "$at" "interpreter output differs" "want: $(echo "$expect" | tr '\n' ' ')" "got:  $(echo "$got" | tr '\n' ' ')"; continue
      fi
      if [ "$wasm" = 1 ]; then
        got=$("$bcc" run "$f" 2>&1) || true
        if [ "$got" != "$expect" ]; then
          fail "$at" "compiled output differs" "want: $(echo "$expect" | tr '\n' ' ')" "got:  $(echo "$got" | tr '\n' ' ')"; continue
        fi
      fi
      ;;
    check)
      if ! out=$("$bcc" check "$f" 2>&1); then fail "$at" "rejected, but must check" "${out#"$f:"}"; continue; fi
      ;;
    reject)
      want=$(sed -n 's/^-- expect: //p' "$f" | head -1)
      if [ -z "$want" ]; then fail "$at" "a \`bc,reject\` block needs an \`-- expect:\` line"; continue; fi
      if ! out=$("$bcc" parse "$f" 2>&1); then fail "$at" "does not parse, so it does not test the checker" "${out#"$f:"}"; continue; fi
      if out=$("$bcc" check "$f" 2>&1); then fail "$at" "accepted, but must be rejected"; continue; fi
      if [ "$out" != "$f:$want" ]; then fail "$at" "wrong error" "want: $want" "got:  ${out#"$f:"}"; continue; fi
      ;;
    *) fail "$at" "unknown attributes \`bc,$attrs\` (use bc, bc,check, bc,reject or bc,ignore)"; continue ;;
  esac
  ran=$((ran + 1))
done < "$tmp/manifest"
echo "$total block(s): $ran passed, $ignored ignored, $bad failure(s)."
[ "$bad" -eq 0 ]
