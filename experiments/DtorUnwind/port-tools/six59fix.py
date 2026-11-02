"""Hand fixes for Six53to59 (run after lifefix.py)."""
import re, sys
p = sys.argv[1]
s = open(p).read()
def rep(a, b):
    global s
    if a not in s:
        print('[six59fix] pattern not found: ' + a[:70])
    s = s.replace(a, b)
rep('ResUT.InStratum.sup hs hs', 'ResUT.inStratum_union_iff.mpr ⟨hs, hs⟩')
rep('LSet.union_self s', 'TSet.union_self s')
s = re.sub(r"(?<![.\w])(\w+'?)\.dom_left ", r"ResUT.Comp.dom_left \1 ", s)
s = re.sub(r"(?<![.\w])(\w+'?)\.dom_right ", r"ResUT.Comp.dom_right \1 ", s)
rep('BoLo.AgWT.inStratum haL β hL', 'BoLo.AgWT.inStratum haL (TSet.single β) hL')
# 6.52 reads `↓β` through `hD`; the residuals and 6.59 carry it.
for t in ['SixFiftyNineResidualKeep', 'SixFiftyNineOffRebKeep']:
    lo = t[0].lower() + t[1:]
    rep('theorem ResUT.%s : ResUT.%s := by' % (lo, t),
        'theorem ResUT.%s {K : WCactus} : ResUT.%s (K := K) := by' % (lo, t))
s = s.replace("hYc hfX hfY l hl\n  exact", "hYc hfX hfY l hl\n  exact")
s = s.replace("  intro β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY l₀ s v hs hreb hce",
              "  intro β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY l₀ s v hs D hD hreb hce")
s = s.replace('ResUT.six52_H1 hreb ', 'ResUT.six52_H1 hD hreb ')
s = s.replace('ResUT.six52_sub_inStratum hreb ', 'ResUT.six52_sub_inStratum hD hreb ')
rep("""    {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (hce : ResUT.CompS ρ ρb ρρb) (hcp : ResUT.CompS ρ' ρp ρ'p)""", """    {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
    {D : TSet} (hD : K.DownOf D (TSet.single β))
    (hreb : ResUT.Reb β ρ'i ρ)
    (hce : ResUT.CompS ρ ρb ρρb) (hcp : ResUT.CompS ρ' ρp ρ'p)""")
s = s.replace("        l₀ s v hs hreb hce hcp hupd", "        l₀ s v hs D hD hreb hce hcp hupd")
rep("""hypotheses `hfX`, `hfY`]` -/
theorem ResUT.six59""", """hypotheses `hfX`, `hfY`]`. Over the tree-stratified carrier. **Forced change:** 6.52, which
the proof applies, reads `↓β` as a stratum `D` with `K.DownOf D {β}` (`hD`), as 6.27 does. -/
theorem ResUT.six59""")
open(p, 'w').write(s)
