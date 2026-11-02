"""Hand fixes for the Six28to29 port."""
import re, sys
p = sys.argv[1]
s = open(p).read()
s = s.replace('fun x c Q =>', 'fun x c _ Q =>')
# 6.29: `α` is the lifetime of an `imm` cell at `{α}`; its stratum is `{α}`.
s = s.replace('{α : TSet}', '{α : Life}')
s = s.replace('(LSet.singleton α).join', '(TSet.single α)').replace('LSet.singleton α', 'TSet.single α')
s = re.sub(r'InStratum α\b', 'InStratum (TSet.single α)', s)
s = s.replace('CellUT.ownOf (Loc := BoCa.Loc) v', 'CellUT.ownOf (K := K) (Loc := BoCa.Loc) v')
s = s.replace('ResUT.flat_imm_at_top ⟨ex\', ag\', hex\', hag\', hc\'⟩ hσ\'l rfl hstratσ\'',
              'ResUT.flat_imm_at_top ⟨ex\', ag\', hex\', hag\', hc\'⟩ hσ\'l (by simp) hstratσ\'')
s = s.replace('''  have hsub : ∀ x, s'.mem x → (TSet.single α).mem x :=
    fun x hx => ResUT.Flat.get_ls_imm''', '''  have hsub : ∀ x, x ∈ s'.set → x ∈ (TSet.single α).set :=
    fun x hx => ResUT.Flat.get_ls_imm''')
s = s.replace('''  obtain ⟨y, hy⟩ := LSet.nonempty s'
  have hyα : y = α := hsub y hy
  have hseq : s' = TSet.single α := by
    refine LSet.ext (fun x => ⟨fun hx => hsub x hx, fun hx => ?_⟩)
    show s'.mem x
    have : x = α := hx
    rw [this, ← hyα]
    exact hy''', '''  obtain ⟨y, hy⟩ := s'.ne
  have hyα : y = α := by simpa using hsub y hy
  have hseq : s' = TSet.single α := by
    refine TSet.ext (Finset.ext fun x => ⟨fun hx => hsub x hx, fun hx => ?_⟩)
    have : x = α := by simpa using hx
    rw [this, ← hyα]
    exact hy''')
open(p, 'w').write(s)
s = re.sub(r'\b(compS_hC|compR_hC) α\b', r'\1 (TSet.single α)', s)
s = re.sub(r'(inStratum [^\n]*?) α (hα|hv)\)', r'\1 (TSet.single α) \2)', s)
s = re.sub(r'(inStratum [^\n]*?) α (hα|hv)$', r'\1 (TSet.single α) \2', s, flags=re.M)
s = s.replace('hEA.get m with', 'ResUT.Comp.get hEA m with')
open(p, 'w').write(s)
