# Sourced by the gate's scripts (scripts/par.sh sources it for every corpus step): `grepq`, the
# one way a gate script asks whether a file has a line, and so the one way a unit decides a skip
# from a program's text.
#
#   grepq [GREP-OPTION…] PATTERN FILE…   `grep -q` that tells a match (0) from no match (1), and
#                                        never takes an error for either: when grep cannot read a
#                                        file (exit 2: a missing or unreadable file, "Too many open
#                                        files"), it says so on standard error and ends the unit
#                                        (or the script) with status 2. A failed unit is never
#                                        recorded in the result cache, so a read error cannot be
#                                        replayed as "no main, skipped".
grepq() {
  local rc=0
  grep -q "$@" || rc=$?
  [ "$rc" -le 1 ] && return "$rc"
  echo "grepq: grep $* could not read its input (exit $rc): the unit fails" >&2
  exit 2
}
export -f grepq
