# The axiom report's names

`scripts/AxiomCheck.lean` (`lake env lean scripts/AxiomCheck.lean`, the gate's "axiom report")
reads every `*.names` file here in file-name order. For each name it prints what
`#print axioms` prints, and it fails on a name that does not resolve and on any axiom outside
`propext`, `Classical.choice` and `Quot.sound`.

A line is a fully qualified declaration name, a `--` comment, or blank.

## Adding names

A PR adds its own file, `<issue>-<slug>.names` (for example `900-loop-exit.names`), and lists
there the theorems its spec entry names. It does not edit another file, so two PRs do not
conflict, and `AxiomCheck.lean` itself does not change.

The `s<NNN>.names` files are the list as it stood before the split, one per `SPEC §N` heading,
with the headings kept as comments and the names in their original order. `s000.names` is the
list's opening block, which had no heading; `s059.names` is the `!`-on-LIR-types block (#714),
whose heading named no section.
