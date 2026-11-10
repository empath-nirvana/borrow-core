#!/bin/bash
# #977's correctness check: for each document (the three in data/, or the files given), our
# roundtrip and serde's, compared as JSON values by `jsoncmp.py`, whose reader (Python's) rounds
# every float correctly and reads every integer exactly; and our parse checksum line against
# serde's.
#
# Three comparisons per document: ours against the input, serde against the input, ours against
# serde. The check fails when ours differs from the input, when the checksums differ, or when ours
# differs from serde where serde equals the input. serde differing from the input is reported but
# does not fail: serde_json's default float reader is not correctly rounded (`canada.json`).
#
# Ours is `out/parse` and `out/roundtrip`, built by `measure.py build`; when they are not built, only
# serde is checked. `OURS_PARSE` and `OURS_ROUNDTRIP` replace them with any command reading
# standard input (e.g. `bcc interp parse.bc`). Our runtime's two closing lines (the value of
# `main` and `live N`) are removed before comparing, and `live` must be 0.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="$here/out/check"
mkdir -p "$out"
serde="$here/serde/target/release/json-bench"
ours_p="${OURS_PARSE:-}"; ours_r="${OURS_ROUNDTRIP:-}"
[ -z "$ours_p" ] && [ -x "$here/out/parse" ] && ours_p="$here/out/parse"
[ -z "$ours_r" ] && [ -x "$here/out/roundtrip" ] && ours_r="$here/out/roundtrip"
if [ ! -x "$serde" ]; then
  (cd "$here/serde" && cargo build --release --offline --locked -q) || { echo "check.sh: serde does not build" >&2; exit 1; }
fi
[ -z "$ours_r" ] && echo "check.sh: ours not built (measure.py build); checking serde only"

if [ $# -gt 0 ]; then files=("$@"); else files=("$here"/data/*.json); fi
cmp_json() { python3 -I "$here/jsoncmp.py" "$1" "$2"; }

# Ours' output in $1 with the runtime's closing lines removed, into $2; fails unless `live 0`.
strip_ours() {
  python3 -I -c '
import sys
b = open(sys.argv[1], "rb").read()
lines = b.split(b"\n")
if len(lines) < 3 or lines[-1] != b"" or not lines[-2].startswith(b"live "):
    sys.exit("no runtime trailer")
open(sys.argv[2], "wb").write(b"\n".join(lines[:-3]) + b"\n")
if lines[-2] != b"live 0":
    sys.exit(lines[-2].decode())
' "$1" "$2"
}

fail=0
for f in "${files[@]}"; do
  n=$(basename "$f" .json)
  echo "== $n ($(wc -c < "$f" | tr -d ' ') bytes)"
  "$serde" roundtrip < "$f" > "$out/$n.serde.json"; s_status=$?
  "$serde" parse < "$f" > "$out/$n.serde.parse"
  if [ $s_status -ne 0 ]; then echo "  serde: refuses the input ($(cat "$out/$n.serde.json"))"; fi
  serde_ok=0
  if [ $s_status -eq 0 ]; then
    if cmp_json "$f" "$out/$n.serde.json" 2> "$out/$n.serde.diff"; then
      echo "  serde = input"; serde_ok=1
    else
      echo "  serde ≠ input (reported, not a failure):"; sed 's/^/    /' "$out/$n.serde.diff"
    fi
  fi
  [ -z "$ours_r" ] && continue
  $ours_r < "$f" > "$out/$n.ours.raw"
  if ! strip_ours "$out/$n.ours.raw" "$out/$n.ours.json" 2> "$out/$n.ours.err"; then
    echo "  ours: MISMATCH: $(cat "$out/$n.ours.err")"; fail=1; continue
  fi
  $ours_p < "$f" > "$out/$n.ours.parse.raw"
  strip_ours "$out/$n.ours.parse.raw" "$out/$n.ours.parse" 2> "$out/$n.ours.parse.err" \
    || { echo "  ours parse: MISMATCH: $(cat "$out/$n.ours.parse.err")"; fail=1; }
  if cmp -s "$out/$n.ours.parse" "$out/$n.serde.parse"; then
    echo "  parse checksum: $(cat "$out/$n.ours.parse") (both)"
  else
    echo "  parse checksum MISMATCH: ours $(cat "$out/$n.ours.parse"), serde $(cat "$out/$n.serde.parse")"; fail=1
  fi
  if [ $s_status -ne 0 ]; then
    if grep -qx error "$out/$n.ours.json"; then echo "  ours: refuses it too"; else
      echo "  ours: MISMATCH: accepts what serde refuses"; fail=1; fi
    continue
  fi
  if cmp_json "$f" "$out/$n.ours.json" 2> "$out/$n.ours.diff"; then echo "  ours = input"; else
    echo "  ours ≠ input: MISMATCH"; sed 's/^/    /' "$out/$n.ours.diff"; fail=1; fi
  if cmp_json "$out/$n.serde.json" "$out/$n.ours.json" 2> "$out/$n.both.diff"; then echo "  ours = serde"; else
    if [ $serde_ok = 1 ]; then echo "  ours ≠ serde: MISMATCH"; fail=1
    else echo "  ours ≠ serde (serde ≠ input, so not a failure):"; fi
    sed 's/^/    /' "$out/$n.both.diff"
  fi
done
[ $fail = 0 ] && echo "check.sh: ok" || echo "check.sh: FAILED"
exit $fail
