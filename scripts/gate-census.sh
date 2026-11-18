#!/usr/bin/env bash
# The gate's checks that read the Lean environment (`scripts/GateCensus.lean`): builds
# `gate-census` unless the gate has (`CI_LOCAL_BUILT`), then runs it on the arguments under the
# library's search path.
#
#     scripts/gate-census.sh CENSUS[+FILE]
#     scripts/gate-census.sh --out DIR CENSUS[+FILE]...
#
# One run for the whole gate. When `GATE_CENSUS_DIR` is set and holds the gate's token
# (scripts/ci-local.sh sets both, with `GATE_CENSUS_TOKEN` and `GATE_CENSUS_ALL`, the censuses the
# steps of this gate ask for; a directory without the token is not read), the first call runs every census
# of `GATE_CENSUS_ALL` in one `gate-census --out "$GATE_CENSUS_DIR"` process, holding a lock on
# that directory; every call, that one included, then hands back the results it asked for from
# there. A census not in `GATE_CENSUS_ALL`, or one that run did not write, runs here, as when
# `GATE_CENSUS_DIR` is unset. The results are the same either way: the same program on the same
# environment (a census's view does not depend on the censuses run beside it).
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build gate-census >/dev/null
census=(lake env .lake/build/bin/gate-census)
if [ -z "${GATE_CENSUS_DIR:-}" ] || [ -z "${GATE_CENSUS_TOKEN:-}" ] ||
    [ "$(cat "$GATE_CENSUS_DIR/token" 2>/dev/null)" != "$GATE_CENSUS_TOKEN" ]; then
  exec "${census[@]}" "$@"
fi

out=""
[ "${1:-}" != --out ] || { out=$2; shift 2; }
dir=$GATE_CENSUS_DIR
# The shared run, once: the first caller runs it holding the lock, the others wait for it and
# find it done. perl's flock (macOS has no flock(1)): the lock goes with the process however it
# ends.
# shellcheck disable=SC2086
perl -MFcntl=:flock -e '
  my ($dir, @cmd) = @ARGV;
  open(my $l, ">>", "$dir/lock") or die "gate-census: $dir/lock: $!\n";
  flock($l, LOCK_EX) or die "gate-census: lock: $!\n";
  exit 0 if -e "$dir/done";
  system(@cmd);
  open(my $d, ">", "$dir/done") or die "gate-census: $dir/done: $!\n";' \
  "$dir" "${census[@]}" --out "$dir" ${GATE_CENSUS_ALL:-}

label() { case "$1" in *+*) echo "${1%%+*}-neg" ;; *) echo "$1" ;; esac; }
shared() { local a; for a in ${GATE_CENSUS_ALL:-}; do [ "$a" = "$1" ] && return 0; done; return 1; }
own=()
for a in "$@"; do
  l=$(label "$a")
  if ! shared "$a" || [ ! -f "$dir/$l.status" ]; then own+=("$a"); continue; fi
  [ -n "$out" ] || { cat "$dir/$l.out"; exit "$(cat "$dir/$l.status")"; }
  cp "$dir/$l.out" "$dir/$l.status" "$out/"
done
[ ${#own[@]} -gt 0 ] || exit 0
if [ -n "$out" ]; then exec "${census[@]}" --out "$out" "${own[@]}"; fi
exec "${census[@]}" "${own[@]}"
