# The changelog

One file per entry, named by its version: `1.47.md`. `scripts/changelog.sh` prints the entries
newest first (the list `SPEC.md`'s Changelog section points to); `scripts/changelog.sh --version`
prints the highest version, which is the specification's version.

## Adding an entry

1. Ask docs-foreman, the only writer of SPEC, for the version number. Numbers are assigned,
   never picked.
2. Add one new file, `docs/changelog/<version>.md`, holding the entry in the list's form:

   ```
   - **1.47** (2026-11-08) — §67 (#900): what the entry adds. What it preserves.
     Continuation lines are indented two spaces.
   ```

   A file may start with a blank line, to put one between this entry and the one above it.
3. Edit no other entry's file. Two PRs that each add a file do not conflict.

Check the result with `scripts/changelog.sh | head`.

## Order

By version, highest first, as `sort -V` orders them (`0.10` above `0.9`, `0.3.1` above `0.3`).
A number given twice keeps it: the second entry's file is `<version>-b.md`, listed after the
first. An entry listed where its number does not place it goes in the `placed` table of
`scripts/changelog.sh`.
