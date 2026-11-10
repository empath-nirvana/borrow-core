# Merges a run's rows into a table of rows keyed by their first field (a program's name), as
# `--write-counts` writes `corpus/counts.expected`, `counts-backend2.expected` and
# `erasure-backend2.expected`:
#
#     awk -v keep=1 -f scripts/merge-rows.awk new table > merged
#
# `new` holds this run's rows, in the order a new row is inserted in; `table` is the file as it
# stands. Comment lines (`# …`) and blank lines stay where they are. An existing row is replaced
# by the run's row of its name in place; a row the run has no row for is kept when `keep` is 1
# (the programs were named) and dropped otherwise (every program was run). A run's row whose name
# the table lacks is inserted before the first row whose name sorts after it, else at the end.
# The run's file may be empty (no program counted): it is told apart by name, not by `NR == FNR`.
# A row's trailing comment (`# …`) is kept when the run's row has none.
FILENAME == ARGV[1] {
  if ($0 ~ /^[ \t]*$/ || $0 ~ /^#/) next
  if (!($1 in row)) order[++n] = $1
  row[$1] = $0
  next
}
{ line[++m] = $0 }
function note(s) { return (s ~ /#/) ? substr(s, index(s, "#")) : "" }
END {
  for (k = 1; k <= m; k++) {
    s = line[k]
    if (s ~ /^[ \t]*$/ || s ~ /^#/) continue
    split(s, f, " ")
    there[f[1]] = 1
  }
  p = 1
  for (k = 1; k <= m; k++) {
    s = line[k]
    if (s ~ /^[ \t]*$/ || s ~ /^#/) { print s; continue }
    split(s, f, " ")
    name = f[1]
    for (; p <= n; p++) {
      if (order[p] in there) continue
      if (order[p] < name) print row[order[p]]
      else break
    }
    if (name in row) {
      r = row[name]
      if (note(r) == "" && note(s) != "") r = r " " note(s)
      print r
    } else if (keep == 1) print s
  }
  for (; p <= n; p++) if (!(order[p] in there)) print row[order[p]]
}
