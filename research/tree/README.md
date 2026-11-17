# The tree archive

The tree interpretation (#840: the typed tree world's relation, its pool and scheduler programs,
the tree's semantic types) is archived here, off the default build (#1133). The relation the kernel
ships is the chain's (`Core/Chain/`).

- **Build:** `lake build ResearchTree`. `lakefile.toml`'s `ResearchTree` lib (`srcDir = "research/tree"`)
  is not a default target, and the library never imports it.
- **Checked by:** gate-full's `research archive` step (`scripts/check-research.sh`): it builds the lib
  and runs `AxiomCheck.lean` (the library's reader, under this lib's imports) on
  `axioms/*.names`, the registered names SPEC §62 cites. The sanity gate's hygiene and
  hypothesis-register checks scan this directory too.
- **Names:** module `Core.TreeX` became `ResearchTree.TreeX`; every declaration keeps its name and
  namespace (`BoCa.Fig16.Tree.*`).

## Rebasing a branch that edits the old `Core/Tree*` files (e.g. `rq1-tree`)

1. `git rebase origin/main`. Git's rename detection carries edits of a moved file to its new
   path; resolve any remaining conflicts at `research/tree/ResearchTree/<File>.lean`.
2. Move files the branch **adds** under `Core/Tree*`:
   `git mv Core/TreeX.lean research/tree/ResearchTree/TreeX.lean`.
3. Rewrite imports in every file the branch touches:
   `sed -i '' -E 's/^import Core\.(Tree[A-Za-z0-9]*)$/import ResearchTree.\1/'` on
   `research/tree/**/*.lean`, and add each new file to `research/tree/ResearchTree.lean`, not
   `Core.lean`.
4. Registered names of tree declarations go in `research/tree/axioms/` (a new
   `<issue>-<slug>.names` file, as in `scripts/axioms/README.md`), not `scripts/axioms/`.
5. A non-tree module (`Core/`, `Support/`, …) must not import `ResearchTree`. If one needs a tree
   declaration, move that declaration to the library first (as #1121 and #1123 did), with its
   statement unchanged.
6. Check: `lake build`, then `scripts/check-research.sh`.
