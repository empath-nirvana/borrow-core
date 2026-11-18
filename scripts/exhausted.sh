# Sourced by scripts/ci-local.sh and scripts/check-exhausted.sh.
#
#   exhausted FILE…   whether any FILE says a tool ran out of file handles (ENFILE: the system's
#                     vnode or file table; EMFILE: the process's descriptors), by the one pattern
#                     the result cache also reads (scripts/gate_cache.py `EXHAUSTED`): a step whose
#                     output says so failed for the machine, not for the tree.
exhausted() { python3 "$(dirname "${BASH_SOURCE[0]}")/gate_cache.py" exhausted "$@"; }

# vnodes_free: whether the machine's vnode table has room. Full means `kern.num_vnodes` at
# `kern.maxvnodes` and `kern.free_vnodes` under $GATE_VNODE_MIN (default 2000) at every one of 10
# samples over 5 s. Free vnodes swing between 0 and tens of thousands within seconds on a busy
# machine (gate30 fd.md), so one low sample means nothing; ten in a row mean the table is held,
# not churning, and a new process that opens files would get ENFILE. `$GATE_VNODE_SAMPLE`, a
# command printing `num max free`, replaces sysctl (the test).
vnode_sample() {
  if [ -n "${GATE_VNODE_SAMPLE:-}" ]; then $GATE_VNODE_SAMPLE
  else sysctl -n kern.num_vnodes kern.maxvnodes kern.free_vnodes | tr '\n' ' '; echo; fi
}
vnodes_free() {
  local i num max free min=${GATE_VNODE_MIN:-2000}
  for ((i = 0; i < 10; i++)); do
    read -r num max free <<< "$(vnode_sample)" || return 0
    { [ -n "$max" ] && [ "$num" -ge "$max" ] && [ "$free" -lt "$min" ]; } || return 0
    [ "$i" = 9 ] || sleep "${GATE_VNODE_STEP:-0.5}"
  done
  return 1
}
# vnode_preflight: before a gate starts, wait (up to $GATE_VNODE_WAIT seconds, default 600) while
# the vnode table is full, saying so in one line; fail in one line if it stays full.
vnode_preflight() {
  local waited=0 limit=${GATE_VNODE_WAIT:-600}
  vnodes_free && return 0
  echo "ci-local: the machine's vnode table is full (kern.maxvnodes; free vnodes under ${GATE_VNODE_MIN:-2000} for 5 s): waiting up to ${limit}s for it to drain"
  while [ "$waited" -lt "$limit" ]; do
    sleep "${GATE_VNODE_POLL:-30}"; waited=$((waited + ${GATE_VNODE_POLL:-30}))
    if vnodes_free; then echo "ci-local: vnodes free again after ${waited}s"; return 0; fi
  done
  echo "ci-local: the machine's vnode table stayed full for ${limit}s: the gate does not start (rerun when the machine is quieter)"
  return 1
}
