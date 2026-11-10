#!/bin/bash
# #977's correctness check: for each document (the three in data/, or the files given), our
# roundtrip and serde's, compared as JSON values by `jsoncmp.py`, whose reader (Python's) rounds
# every float correctly and reads every integer exactly; and our parse checksum line against
# serde's.
#
# serde is built twice (`measure.py`): `exact`, the primary baseline, with `float_roundtrip`, and
# `default`, the reference, with serde_json's default features. Per document: ours, serde exact
# and serde default each against the input, and ours against serde exact. The check fails when
# ours or serde exact differs from the input, when ours differs from serde exact, or when the
# checksums differ. serde default differing from the input is reported but does not fail: its
# float reader is not correctly rounded (`canada.json`).
#
# Ours is `out/parse` and `out/roundtrip`, built by `measure.py build`; when they are not built, only
# serde is checked. `OURS_PARSE` and `OURS_ROUNDTRIP` replace them with any command reading
# standard input (e.g. `bcc interp parse.bc`). Our runtime's two closing lines (the value of
# `main` and `live N`) are removed before comparing, and `live` must be 0.
set -uo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="$here/out/check"
mkdir -p "$out"
exact="$here/serde/target-exact/release/json-bench"
default="$here/serde/target/release/json-bench"
ours_p="${OURS_PARSE:-}"; ours_r="${OURS_ROUNDTRIP:-}"
[ -z "$ours_p" ] && [ -x "$here/out/parse" ] && ours_p="$here/out/parse"
[ -z "$ours_r" ] && [ -x "$here/out/roundtrip" ] && ours_r="$here/out/roundtrip"
build() { (cd "$here/serde" && cargo build --release --offline --locked -q "$@") \
  || { echo "check.sh: serde does not build" >&2; exit 1; }; }
[ -x "$exact" ] || build --features exact --target-dir target-exact
[ -x "$default" ] || build
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
  "$exact" roundtrip < "$f" > "$out/$n.exact.json"; e_status=$?
  "$exact" parse < "$f" > "$out/$n.exact.parse"
  "$default" roundtrip < "$f" > "$out/$n.default.json"; d_status=$?
  if [ $e_status -ne 0 ]; then
    echo "  serde exact: refuses the input"
    [ $d_status -eq 0 ] && { echo "  serde default: MISMATCH: accepts it"; fail=1; }
  else
    if cmp_json "$f" "$out/$n.exact.json" 2> "$out/$n.exact.diff"; then echo "  serde exact = input"; else
      echo "  serde exact ≠ input: MISMATCH"; sed 's/^/    /' "$out/$n.exact.diff"; fail=1; fi
    if [ $d_status -ne 0 ]; then echo "  serde default: MISMATCH: refuses it"; fail=1
    elif cmp_json "$f" "$out/$n.default.json" 2> "$out/$n.default.diff"; then echo "  serde default = input"
    else echo "  serde default ≠ input (reference build, reported, not a failure):"
      sed 's/^/    /' "$out/$n.default.diff"; fi
  fi
  [ -z "$ours_r" ] && continue
  $ours_r < "$f" > "$out/$n.ours.raw"
  if ! strip_ours "$out/$n.ours.raw" "$out/$n.ours.json" 2> "$out/$n.ours.err"; then
    echo "  ours: MISMATCH: $(cat "$out/$n.ours.err")"; fail=1; continue
  fi
  $ours_p < "$f" > "$out/$n.ours.parse.raw"
  strip_ours "$out/$n.ours.parse.raw" "$out/$n.ours.parse" 2> "$out/$n.ours.parse.err" \
    || { echo "  ours parse: MISMATCH: $(cat "$out/$n.ours.parse.err")"; fail=1; }
  if cmp -s "$out/$n.ours.parse" "$out/$n.exact.parse"; then
    echo "  parse checksum: $(cat "$out/$n.ours.parse") (ours and serde exact)"
  else
    echo "  parse checksum MISMATCH: ours $(cat "$out/$n.ours.parse"), serde exact $(cat "$out/$n.exact.parse")"; fail=1
  fi
  if [ $e_status -ne 0 ]; then
    if grep -qx error "$out/$n.ours.json"; then echo "  ours: refuses it too"; else
      echo "  ours: MISMATCH: accepts what serde refuses"; fail=1; fi
    continue
  fi
  if cmp_json "$f" "$out/$n.ours.json" 2> "$out/$n.ours.diff"; then echo "  ours = input"; else
    echo "  ours ≠ input: MISMATCH"; sed 's/^/    /' "$out/$n.ours.diff"; fail=1; fi
  if cmp_json "$out/$n.exact.json" "$out/$n.ours.json" 2> "$out/$n.both.diff"; then echo "  ours = serde exact"; else
    echo "  ours ≠ serde exact: MISMATCH"; sed 's/^/    /' "$out/$n.both.diff"; fail=1; fi
done
[ $fail = 0 ] && echo "check.sh: ok" || echo "check.sh: FAILED"
exit $fail
