The generator of Support/Model/Tree/Port: the printed sources (over CellU) translated to the
tree-stratified carrier (CellUT K). [spec §62]

regen.sh    regenerates the generated files in dependency order:
              scripts/tree-port/regen.sh [FIRST]   rewrite in place from FIRST on, building each
                                                   (NOBUILD=1: rewrite only)
              scripts/tree-port/regen.sh --check   regenerate into a temporary directory and fail
                                                   unless every file equals the checked-in one
            scripts/check-hygiene.sh runs the check, so the gate does.
port.py     translates printed source to the tree carrier:
              python3 port.py OUT IMPORT1,IMPORT2 -- SRC[:a-b] ...
fixups.py   the hand fixes recorded per generated file (run after port.py). It calls drop.py
            (removes declarations by name: duplicates of carrier lemmas) and the per-file fixes
            subfix.py, six28fix.py, surgcfix.py, lifefix.py, closfix.py, six52fix.py, six59fix.py.
*.lean.txt  source fragments some generated files are assembled from or patched with
            (sub_lset*.lean.txt: the lifetime-set lemmas of Subtraction, on TSet).

Written by hand, not generated (each says so in its header): Base, Cells, RebDef, SubDef,
OutlivesB (Support/Model/Outlives.lean:257-414, 625-690); translated and then edited by hand:
Strata, Down, Six16to24, Six27, SurgeryA, SurgeryB (Support/Model/Surgery.lean:41-156).
