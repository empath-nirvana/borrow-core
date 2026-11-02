"""Generic fixes for ports where `α` is a lifetime whose stratum is `{α}` (reborrow sites)."""
import re, sys
p = sys.argv[1]
s = open(p).read()
s = s.replace('{α : TSet}', '{α : Life}').replace('{β : TSet}', '{β : Life}')
s = re.sub(r'\(([\w\' ∪]+)\)\.join\b', r'(\1)', s)
s = s.replace('(LSet.singleton α).join', '(TSet.single α)').replace('LSet.singleton α', 'TSet.single α')
s = s.replace('(LSet.singleton β).join', '(TSet.single β)').replace('LSet.singleton β', 'TSet.single β')
s = re.sub(r'InStratum ([αβ])\b', r'InStratum (TSet.single \1)', s)
s = re.sub(r"(?<![.\w])G(?![.\w'])", 'Gr', s)
s = re.sub(r"(?<![.\w])G\.(get|InStratum|del)\b", r'Gr.\1', s)
s = s.replace('(Gr.restrict CellUT.kind', '(G.restrict CellUT.kind')
s = re.sub(r"rcases (\w+)\.get (\w+) with", r"rcases ResUT.Comp.get \1 \2 with", s)
s = re.sub(r"∀ x, ([\w']+)\.mem x → ([\w']+)\.mem x", r"\1.set ⊆ \2.set", s)
s = re.sub(r"(?<![.\w])(σ\w*'?)\.borrowPart\b", r"(ResUT.borrowPart \1)", s)
open(p, 'w').write(s)
