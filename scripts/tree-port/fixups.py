"""fixups.py NAME FILE : apply the recorded manual fixes for port file NAME."""
import sys, re, subprocess
name, f = sys.argv[1], sys.argv[2]
import os
S = os.path.dirname(os.path.abspath(__file__)) + '/'
def drop(*names):
    subprocess.run(['python3', S+'drop.py', f] + list(names), check=True)
s = open(f).read()
def rep(a, b):
    global s
    if a not in s:
        print(f'[fixups {name}] pattern not found: {a[:70]!r}')
    s = s.replace(a, b)
if name == 'Singletons':
    rep("(ResUT.single l (CellUT.ownOf v)).InStratum α :=", "(ResUT.single l (CellUT.ownOf (K := K) (Loc := Loc) v)).InStratum α :=")
    rep("theorem ResUT.flat_single_own (l : Loc) (v : Val) :\n    ResUT.Flat (ResUT.single l (CellUT.ownOf v))", "theorem ResUT.flat_single_own (l : Loc) (v : Val) :\n    ResUT.Flat (ResUT.single l (CellUT.ownOf (K := K) v))")
    rep("ResUT.Valid (ResUT.single l (CellUT.ownOf (Val := Val) v))", "ResUT.Valid (ResUT.single l (CellUT.ownOf (K := K) (Val := Val) v))")
    rep("AgWT (ResUT.single l (CellUT.ownOf v)) (PMap.empty : ResUT Loc Val K)", "AgWT (ResUT.single l (CellUT.ownOf (K := K) v)) (PMap.empty : ResUT Loc Val K)")
if name == 'Split':
    rep("(ResUT.compatS_of_pairwise h h₁₂.1.symm h₁₃.1.symm).symm", "ResUT.CompatS.symm (ResUT.compatS_of_pairwise h (ResUT.CompatS.symm h₁₂.1) (ResUT.CompatS.symm h₁₃.1))")
if name == 'Update':
    rep("  refine ⟨fun l s v χ h => ?_, fun l b P => ?_⟩", "  refine ⟨fun l s v χ h => ?_, fun l b _ P => ?_⟩")
    rep("⟨fun l s v χ hs => (h.1 l s v χ hs).symm, fun l b P => (h.2 l b P).symm⟩", "⟨fun l s v χ hs => (h.1 l s v χ hs).symm, fun l b _ P => (h.2 l b P).symm⟩")
    rep("  rcases h with ⟨a, P, h₁, h₂⟩ | ⟨s, v, χ, hh, e₁, e₂⟩\n  · exact Or.inl ⟨a, P, h₂, h₁⟩", "  rcases h with ⟨a, i, P, h₁, h₂⟩ | ⟨s, v, χ, hh, e₁, e₂⟩\n  · exact Or.inl ⟨a, i, P, h₂, h₁⟩")
    rep("      Or.inl ⟨b, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v', χ', h', hw', rfl⟩⟩⟩", "      Or.inl ⟨b, inferInstance, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v', χ', h', hw', rfl⟩⟩⟩")
if name == 'Ancestors':
    rep("      (CellUT.mutOf b v ρ hb P hP).kind ≠ Kind.imm := by\n    intro b v ρ hb P hP", "      (CellUT.mutOf b v ρ hb P hP).kind ≠ Kind.imm := by\n    intro b _ v ρ hb P hP")
if name == 'UpdateFrame':
    rep("  (∀ (b : TSet) (P : Val → SPropST BoCa.Loc BoCa.Val K b),\n      (∃ ψ, o = some ψ ∧ IsMutSig ψ b P)", "  (∀ (b : TSet) [Fact (K.Anti b)] (P : Val → SPropST BoCa.Loc BoCa.Val K b),\n      (∃ ψ, o = some ψ ∧ IsMutSig ψ b P)")
    rep("  refine ⟨fun s v χ hh => ?_, fun b P => ?_⟩\n  · rw [← ResUT.flatAt_iff h₁", "  refine ⟨fun s v χ hh => ?_, fun b _ P => ?_⟩\n  · rw [← ResUT.flatAt_iff h₁")
    rep("  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩", "  ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩")
if name == 'AgBeneath':
    s = s.rstrip()
    if s.endswith('\nend'):
        s = s[:-4]
    s = s + '\nend BoCa.Fig16.Tree\n\nend\n'
if name == 'Six48':
    rep("noncomputable section\n\n", """noncomputable section

namespace BoCa.Fig16.Tree.BoLo
open BoCa.Fig16 BoCa.Fig16.Tree
variable {K : WCactus}

/-- The composite `#` asserts is defined is valid, wherever it is named. -/
theorem hash_valid_comp {ρ₁ ρ₂ σ : ResUT BoCa.Loc BoCa.Val K} (h : ResUT.Hash ρ₁ ρ₂)
    (hc : ResUT.CompS ρ₁ ρ₂ σ) : ResUT.Valid σ := by
  obtain ⟨x, hx, hv⟩ := h.2
  cases ResUT.CompS.functional hx hc
  exact hv

end BoCa.Fig16.Tree.BoLo

""")
    rep("  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩", "  ⟨fun _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩")
    rep("    (fun l b P => ?_), ⟨τ₁₂, hτ₁₂⟩, ⟨τ₁₃, hτ₁₃⟩⟩", "    (fun l b _ P => ?_), ⟨τ₁₂, hτ₁₂⟩, ⟨τ₁₃, hτ₁₃⟩⟩")
if name == 'Reborrow':
    s = s.replace('{α : TSet}', '{α : Life}')
    s = s.replace('(LSet.singleton α).join', '(TSet.single α)').replace('LSet.singleton α', 'TSet.single α')
    rep('h.get l with', 'ResUT.Comp.get h l with')
    rep('hc.dom_left hg', 'ResUT.Comp.dom_left hc hg')
    rep("hc.dom_right hζ'", "ResUT.Comp.dom_right hc hζ'")
    rep("hτ.dom_left hζ'", "ResUT.Comp.dom_left hτ hζ'")
    rep('(∀ x, t.mem x → s.mem x)', 't.set ⊆ s.set')
    rep('  exact lt_of_lt_of_le hx (LSet.meet_mono_of_subset hts)', '  exact fun a ha c hc => hx a ha c (hts hc)')
if name == 'ReborrowFrame':
    s = s.replace('{α : TSet}', '{α : Life}')
    s = s.replace('(LSet.singleton α).join', '(TSet.single α)').replace('LSet.singleton α', 'TSet.single α')
    s = s.replace('(∀ x, t.mem x → s.mem x)', 't.set ⊆ s.set')
    s = re.sub(r'(\w+)\.dom_left ', r'ResUT.Comp.dom_left \1 ', s)
    s = re.sub(r'(\w+)\.dom_right ', r'ResUT.Comp.dom_right \1 ', s)
    for n in ['ag_cell_of_reb', 'ag_dom_of_reb', 'frame_compatS_ag', 'frame_compatR_ag']:
        rep('theorem ResUT.%s {β : TSet}' % n, 'theorem ResUT.%s {β : Life}' % n)
    rep('    {α : Life} (h₁ : ρ₁.InStratum α) (h₂ : ρ₂.InStratum α) : ρ.InStratum α := by',
        '    {α : TSet} (h₁ : ρ₁.InStratum α) (h₂ : ρ₂.InStratum α) : ρ.InStratum α := by')
    rep('    exact ⟨t, ht, fun x hx => Or.inl (hts x hx), e⟩',
        '    exact ⟨t, ht, fun x hx => Finset.mem_union.mpr (Or.inl (hts hx)), e⟩')
    rep('    exact ⟨t₁ ∪ t₂, k₃, fun x hx => hx.elim (hts₁ x) (hts₂ x), f⟩',
        '    exact ⟨t₁ ∪ t₂, k₃, fun x hx => (Finset.mem_union.mp hx).elim (fun h => hts₁ h) (fun h => hts₂ h), f⟩')
if name == 'ReborrowLowering':
    s = s.replace('{α : TSet}', '{α : Life}').replace('{β : TSet}', '{β : Life}')
    s = s.replace('(LSet.singleton α).join', '(TSet.single α)').replace('LSet.singleton α', 'TSet.single α')
    s = re.sub(r'(\w+)\.dom_left ', r'ResUT.Comp.dom_left \1 ', s)
    s = re.sub(r'(\w+)\.dom_right ', r'ResUT.Comp.dom_right \1 ', s)
    rep('    (hts : ∀ x, t.mem x → s.mem x) :\n    CellUT.CompR (CellUT.immOf t v χ ht)',
        '    (hts : t.set ⊆ s.set) :\n    CellUT.CompR (CellUT.immOf t v χ ht)')
    rep('  have e : t ∪ s = s := LSet.ext fun x => ⟨fun h => h.elim (hts x) id, Or.inr⟩\n  have h₃ : χ.InStratum (t ∪ s).join := by rw [e]; exact hs',
        '  have e : t ∪ s = s := TSet.ext (Finset.union_eq_right.mpr hts)\n  have h₃ : χ.InStratum (t ∪ s) := by rw [e]; exact hs')
if name in ('UpdateFrame', 'Six48'):
    s = s.replace('(ResUT BoCa.Loc BoCa.Val K)', 'ResUT BoCa.Loc BoCa.Val K')
open(f, 'w').write(s)
if name == 'WalkSplitting': drop('CellUT.CompS.kind', 'CellUT.CompS.wit')
if name == 'Compatibility': drop('CellUT.compatS_iff')
if name == 'Split': drop('ResUT.CompS.assoc', 'CellUT.compatR_iff')
if name == 'AlgebraInstances': drop('ResUT.CompR.comm', 'ResUT.CompR.assoc', 'CellUT.CompS.at', 'CellUT.CompS.inStratum')
if name == 'UpdateFrame': drop('wandAll')
if name == 'Reborrow': drop('ResUT.sites_nil_of_none', 'ResUT.sites_singleton_of', 'BigCompT.nil_inv')
if name == 'ReborrowFrame': drop('ResUT.del_compS')
if name == 'Subtraction': subprocess.run(['python3', S+'subfix.py', f], check=True)
if name == 'Six28to29': subprocess.run(['python3', S+'six28fix.py', f], check=True)
if name in ('SurgeryC', 'Six34to39'): subprocess.run(['python3', S+'surgcfix.py', name, f], check=True)
if name == 'ClosingSentence':
    subprocess.run(['python3', S+'lifefix.py', f], check=True)
    subprocess.run(['python3', S+'closfix.py', f], check=True)
if name == 'Six49to52':
    subprocess.run(['python3', S+'lifefix.py', f], check=True)
    subprocess.run(['python3', S+'six52fix.py', f], check=True)
if name == 'Six43to46':
    subprocess.run(['python3', S+'lifefix.py', f], check=True)
if name == 'Six53to59':
    subprocess.run(['python3', S+'lifefix.py', f], check=True)
    subprocess.run(['python3', S+'six59fix.py', f], check=True)
