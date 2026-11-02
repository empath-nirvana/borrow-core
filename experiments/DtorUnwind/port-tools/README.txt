Port tooling for experiments/DtorUnwind/DtorUnwind/Tree/Port.

port.py   translates printed source (over CellU) to the tree carrier (CellUT K):
          python3 port.py OUT IMPORT1,IMPORT2 -- SRC[:a-b] ...
fixups.py the hand fixes recorded per ported file (run after port.py).
drop.py   removes declarations by name (duplicates of carrier lemmas).
regen.sh  regenerates the ported files in dependency order: ./regen.sh [FIRST]
*.lean.txt  source fragments some ports are assembled from.
Strata, Down, Six27, SurgeryA, SurgeryB, Six16to24 were translated and then edited by hand
(SurgeryB: Support/Model/Surgery.lean:41-156).
RebDef and SubDef (rows 5.28, 5.47, 5.64, 5.66) are written by hand.
subfix.py, six28fix.py: recorded fixes run by fixups.py.
sub_lset*.lean.txt: the lifetime-set lemmas of the Subtraction port, on TSet.
