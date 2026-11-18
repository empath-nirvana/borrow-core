#!/usr/bin/env bash
# A gate that runs out of file handles says so in one line and fails (scripts/exhausted.sh), and
# the job pool (scripts/slot) bounds the processes that map the library. Shown with small limits
# of its own, never near the machine's: `ulimit -n` in a subshell, a pool in a scratch directory
# (`SLOT_DIR`), a synthetic vnode sampler (`GATE_VNODE_SAMPLE`).
#
#   * a tool's out-of-handles words, ENFILE's and EMFILE's, and Lean's, are recognised;
#     ordinary output is not;
#   * slot that cannot get a descriptor fails (exit 125) with those words, never runs its command
#     outside the pool, and never sizes a pool of 0;
#   * a par job that runs out of descriptors fails, and its output says so;
#   * the vnode preflight passes a table with room or with free vnodes, waits on a full one, and
#     fails in one line when it stays full;
#   * library tokens: with two, a third holder waits until one ends.
#
#     scripts/check-exhausted.sh
set -uo pipefail
cd "$(dirname "$0")/.."
. scripts/exhausted.sh
t=$(mktemp -d)
trap 'rm -rf "$t"' EXIT
bad=0
ok() { echo "check-exhausted: $1"; }
no() { echo "check-exhausted: FAILED: $1"; bad=1; }

# The words.
for l in "_: line 4: /usr/bin/grep: Too many open files in system" "OSError: [Errno 24] Too many open files: 'x'" \
    "cannot read lib/io.bc: resource exhausted (error code: 4294967273, file table overflow)"; do
  printf '%s\n' "$l" > "$t/log"; exhausted "$t/log" && ok "recognised: $l" || no "not recognised: $l"
done
printf 'corpus/x.bc: ok at wasm\nopen files: 3\n' > "$t/log"
exhausted "$t/log" && no "ordinary output taken for exhaustion" || ok "ordinary output is not exhaustion"

# slot without descriptors: it fails, and says why.
export SLOT_DIR=$t/pool SLOT_N=2 SLOT_MEM=2 SLOT_LEAN=2
scripts/slot -s > /dev/null
# All descriptors but two taken before slot starts: perl loads its modules through those left,
# the door takes one, and the first token cannot be opened.
out=$( (ulimit -n 9; exec 3<scripts/slot 4<scripts/slot 5<scripts/slot 6<scripts/slot; scripts/slot -- echo ran) 2>&1 ); rc=$?
if [ "$rc" = 125 ] && [ "${out#*ran}" = "$out" ] && printf '%s\n' "$out" | grep -Eqi "$exhaustedRe"; then
  ok "slot without descriptors fails (125) and says so: $(printf '%s' "$out" | head -1)"
else no "slot without descriptors: exit $rc, output: $out"; fi

# A par job that runs out of descriptors: its output says so, and it counts as failed.
cat > "$t/probe.sh" <<'SH'
#!/usr/bin/env bash
set -uo pipefail
cd "$(dirname "$0")"
. "$PAR_HOME/par.sh"
opener() { python3 -c 'import sys; fs = [open(sys.argv[1]) for _ in range(64)]; print("opened")' "$PAR_HOME/par.sh"; }
export -f opener
par opener one
echo "failed $par_failed"
SH
chmod +x "$t/probe.sh"
out=$( (ulimit -n 40; GATE_CACHE=0 PAR_HOME=$PWD/scripts "$t/probe.sh") 2>&1 )
if printf '%s\n' "$out" | grep -q '^failed 1$' && printf '%s\n' "$out" > "$t/log" && exhausted "$t/log"; then
  ok "a par job out of descriptors fails and says so"
else no "a par job out of descriptors: $out"; fi

# The vnode preflight, on synthetic samples.
export GATE_VNODE_STEP=0 GATE_VNODE_POLL=1
GATE_VNODE_SAMPLE="echo 100 263168 0" vnode_preflight > "$t/out" && [ ! -s "$t/out" ] &&
  ok "preflight: a table with room passes silently" || no "preflight: a table with room: $(cat "$t/out")"
GATE_VNODE_SAMPLE="echo 263168 263168 9000" vnode_preflight > "$t/out" && [ ! -s "$t/out" ] &&
  ok "preflight: a full table with free vnodes passes silently" || no "preflight: free vnodes: $(cat "$t/out")"
if GATE_VNODE_WAIT=2 GATE_VNODE_SAMPLE="echo 263168 263168 10" vnode_preflight > "$t/out"; then
  no "preflight: a table that stays full passed"
else [ "$(grep -c 'stayed full' "$t/out")" = 1 ] && ok "preflight: a table that stays full fails in one line: $(tail -1 "$t/out")" ||
  no "preflight: $(cat "$t/out")"; fi
echo 0 > "$t/n"
drain() { local n; n=$(cat "$t/n"); echo $((n + 1)) > "$t/n"; if [ "$n" -lt 12 ]; then echo "263168 263168 10"; else echo "263168 263168 9000"; fi; }
GATE_VNODE_WAIT=30 GATE_VNODE_SAMPLE=drain vnode_preflight > "$t/out" && grep -q 'free again' "$t/out" &&
  ok "preflight: a full table that drains: waits, then starts" || no "preflight: draining: $(cat "$t/out")"

# Library tokens: two holders run, the third waits for one of them.
for i in 1 2; do scripts/slot -l 1 -- sh -c "sleep 2; echo end$i >> '$t/order'" & done
sleep 0.5
scripts/slot -l 1 -- sh -c "echo third >> '$t/order'"
wait
# The two holders sleep 2 s; the third, asked for 0.5 s after them, runs only when one has ended.
if [ "$(head -1 "$t/order")" != third ] && [ "$(wc -l < "$t/order" | tr -d ' ')" = 3 ]; then
  ok "library tokens: with 2, the third holder ran after one ended ($(tr '\n' ' ' < "$t/order"))"
else no "library tokens: $(tr '\n' ' ' < "$t/order")"; fi

[ "$bad" = 0 ] && echo "check-exhausted: out-of-handles is said and fails, and the library tokens bound their holders"
exit "$bad"
