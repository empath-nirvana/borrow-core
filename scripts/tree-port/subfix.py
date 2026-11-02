"""Hand fixes for the Subtraction port: the lifetime-set lemmas read on TSet."""
import re, sys, os
p = sys.argv[1]
T = os.path.dirname(os.path.abspath(__file__)) + '/'
s = open(p).read()
a = s.index('namespace BoCa.Fig16.Tree\nopen BoCa.Fig16\ntheorem LSet.diff_join_le')
b = s.index('namespace BoCa.Fig16.Tree\nopen BoCa.Fig16\nvariable {Loc Val : Type} {K : WCactus}\n/-- Every `ρ ⊟ ρ′`')
s = s[:a] + open(T + 'sub_lset.lean.txt').read() + s[b:]
a = s.index('namespace BoCa.Fig16.Tree\nopen BoCa.Fig16\n/-- `ᾱ ∖ β̄` is determined')
b = s.index('end BoCa.Fig16.Tree', s.index('theorem LSet.eq_of_diffEmpty')) + len('end BoCa.Fig16.Tree')
s = s[:a] + open(T + 'sub_lset2.lean.txt').read().rstrip('\n') + s[b:]
for n in ['Diff', 'DiffEmpty', 'exists_diff', 'diff_inStratum', 'diff_union', 'eq_of_diffEmpty']:
    s = re.sub(r'\bLSet\.' + n + r'\b', 'TSet.' + n, s)
s = re.sub(r"∀ x, ([\w']+)\.mem x → ([\w']+)\.mem x", r"\1.set ⊆ \2.set", s)
s = s.replace("ResUT.InStratum.sup hu' h'", "(ResUT.inStratum_union_iff.mpr ⟨hu', h'⟩)")
open(p, 'w').write(s)
