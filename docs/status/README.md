# Implementation status

What implements each SPEC entry, one paragraph per file. `scripts/status.sh` prints them in
order: the list `SPEC.md`'s Status section points to.

## Files

- `legacy/NN-<slug>.md`: the paragraphs written before the list was split, numbered by their
  position (`01`–`41`). Their order was editorial, not by entry (Entry 22 before 21, Entry 18
  after 21, paragraphs on §3, §8 and §19 with no entry number), so the two-digit prefix keeps it.
  The slug is the entry (`e18`), or the paragraph's first words when it names no entry.
  `legacy/41-e40.md` also holds Entries 42–47, 49 and 51, which were written into it.
- `<entry>.md`: one file per entry from Entry 52 on, named by its number (`54.md`); a paragraph
  that covers several entries is named by its range (`52-53.md`). They follow the legacy files,
  by entry number (`sort -V`).

## Adding an entry's status

Add `docs/status/<entry>.md`, using the entry number docs-foreman assigned (Entry 66 is
`66.md`), holding the paragraph as it would have stood in the list: `Entry 66 (§67) is
implemented in …`. Start the file with a blank line to put one between it and the paragraph
above. To update an entry already listed, edit that entry's file; edit no other.

Two PRs that each add their own file do not conflict.
