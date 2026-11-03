#!/usr/bin/env bash
# Files on the targets (SPEC §34, *Files*): `corpus/fs-cat.bc` and `corpus/json-field.bc` on real
# files. Their corpus goldens run the error path only (`corpus/no-such-file`: the model's file
# system is empty), so this step runs the reads: it writes files into a directory of its own
# temporary directory, and runs each program on their absolute paths in Wasm (`bcc run --dir`,
# the directory preopened), natively (`bcc run --native`), and by the new backend in both
# (`bcc run --backend new …`). No network.
#
#   * `fs-cat` on a 12-byte text file and on a 200 000-byte binary one (four chunks of 64 KiB):
#     standard output is the file's bytes, then the report (`i32[0]`, `live 0`).
#   * `fs-cat` on a path that is not there (`not found`) and on a directory (`is a directory`):
#     the message on standard error, `i32[1]`.
#   * `json-field` on a JSON file, for a string, a number, a word, an object, an array and a key
#     that is not there: the first line of standard output.
#   * `fs-copy` from the binary file over a longer file, which it truncates (an open for writing,
#     the writes): the copy must be the file's bytes, then `fs-cat` reads it back.
#   * Natively, `json-field` on a FIFO, whose size reads `0`: `read_all` grows its buffer.
#
# Natively without a C compiler (`bcc cc`), the native runs are skipped, and the summary says so.
#
#     scripts/check-fs.sh
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
command -v wasmtime >/dev/null || { echo "wasmtime is not on PATH"; exit 1; }
bcc=.lake/build/bin/bcc
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
d=$tmp/files
mkdir -p "$d/dir"
printf 'hello, file\n' > "$d/hello.txt"
python3 -c "import sys; sys.stdout.buffer.write(bytes((i * 7 + 3) % 256 for i in range(200000)))" > "$d/big.bin"
cat > "$d/pod.json" <<'EOF'
{"apiVersion": "v1", "kind": "Pod",
 "metadata": {"name": "web", "labels": {"app": "x"}},
 "replicas": 3, "ready": true, "items": [1, 2]}
EOF

# The runners: name, then the words before the program.
runners=("wasm" "run --dir $d" "new-wasm" "run --backend new --dir $d")
native=1
if "$bcc" cc >/dev/null 2>&1; then
  runners+=("native" "run --native" "new-native" "run --backend new --native")
else
  native=0
  echo "no C compiler for the native target: the native runs are skipped"
fi

fail=0
bad() { echo "$1"; fail=1; }

for ((i = 0; i < ${#runners[@]}; i += 2)); do
  name=${runners[i]}
  read -r -a how <<< "${runners[i + 1]}"
  # fs-cat: the bytes, then the report.
  for f in hello.txt big.bin; do
    "$bcc" "${how[@]}" corpus/fs-cat.bc "$d/$f" > "$tmp/out" 2> "$tmp/err" || true
    { cat "$d/$f"; printf 'i32[0]\nlive 0\n'; } > "$tmp/want"
    cmp -s "$tmp/out" "$tmp/want" || bad "fs-cat $f ($name): standard output differs from the file"
    [ ! -s "$tmp/err" ] || bad "fs-cat $f ($name): standard error: $(head -2 "$tmp/err")"
  done
  # fs-cat: the errors.
  for f in missing dir; do
    want="fs-cat: $d/$f: not found"
    [ "$f" = dir ] && want="fs-cat: $d/$f: is a directory"
    "$bcc" "${how[@]}" corpus/fs-cat.bc "$d/$f" > "$tmp/out" 2> "$tmp/err" || true
    [ "$(cat "$tmp/err")" = "$want" ] || bad "fs-cat $f ($name): standard error is '$(cat "$tmp/err")', not '$want'"
    [ "$(head -1 "$tmp/out")" = "i32[1]" ] || bad "fs-cat $f ($name): answers '$(head -1 "$tmp/out")'"
  done
  # json-field.
  for kv in "kind:Pod" "replicas:3" "ready:true" "metadata:<object>" "items:<array>" "name:missing"; do
    k=${kv%%:*}; v=${kv#*:}
    got=$("$bcc" "${how[@]}" corpus/json-field.bc "$d/pod.json" "$k" 2>&1 | head -1) || true
    [ "$got" = "$v" ] || bad "json-field $k ($name): '$got', not '$v'"
  done
  # fs-copy over a longer file, which it truncates; then the copy read back.
  head -c 300000 /dev/zero > "$d/copy.bin"
  "$bcc" "${how[@]}" corpus/fs-copy.bc "$d/big.bin" "$d/copy.bin" > "$tmp/out" 2> "$tmp/err" || true
  [ "$(head -1 "$tmp/out")" = "i32[0]" ] || bad "fs-copy ($name): answers '$(head -1 "$tmp/out")': $(head -2 "$tmp/err")"
  cmp -s "$d/big.bin" "$d/copy.bin" || bad "fs-copy ($name): the copy differs from the file"
  "$bcc" "${how[@]}" corpus/fs-cat.bc "$d/copy.bin" > "$tmp/out" 2> /dev/null || true
  { cat "$d/big.bin"; printf 'i32[0]\nlive 0\n'; } > "$tmp/want"
  cmp -s "$tmp/out" "$tmp/want" || bad "fs-copy ($name): the copy does not read back"
  # A FIFO (natively: WASI does not open one): its size reads 0, so read_all grows its buffer.
  case "$name" in
    native|new-native)
      rm -f "$d/fifo"; mkfifo "$d/fifo"
      { python3 -c "import sys; sys.stdout.write('{\"pad\": \"' + 'x' * 9000 + '\", \"kind\": \"Fifo\"}')" > "$d/fifo"; } &
      got=$("$bcc" "${how[@]}" corpus/json-field.bc "$d/fifo" kind 2>&1 | head -1) || true
      wait
      [ "$got" = "Fifo" ] || bad "json-field on a FIFO ($name): '$got', not 'Fifo'"
      ;;
  esac
  echo "fs files ($name): checked"
done
skipped=""
[ "$native" = 1 ] || skipped=" (native runs skipped: no C compiler)"
[ "$fail" = 0 ] && echo "0 failure(s)$skipped." || { echo "failures above"; exit 1; }
