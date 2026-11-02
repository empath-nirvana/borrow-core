"""Hand fixes for SurgeryC (Support/Model/Surgery.lean:156-386) and Six34to39."""
import re, sys
name, p = sys.argv[1], sys.argv[2]
s = open(p).read()
# `α` is a lifetime; its stratum is `{α}`.
s = s.replace('{α : TSet}', '{α : Life}')
s = s.replace('(LSet.singleton α).join', '(TSet.single α)').replace('LSet.singleton α', 'TSet.single α')
s = re.sub(r'InStratum α\b', 'InStratum (TSet.single α)', s)
# A resource named `G` shadows the namespace of the walks' schema.
s = re.sub(r"(?<![.\w])G(?![.\w'])", 'Gr', s)
s = s.replace('(Gr.restrict CellUT.kind', '(G.restrict CellUT.kind')
if name == 'SurgeryC':
    s = s.replace('∃ h\' : χ.InStratum (a ∪ b).join,', '∃ h\' : χ.InStratum (a ∪ b),')
    s = s.replace('refine ⟨by rw [LSet.union_self]; exact ha, ?_⟩', 'refine ⟨by rw [TSet.union_self]; exact ha, ?_⟩')
    s = s.replace('LSet.union_self a', 'TSet.union_self a')
    # A resource named `K` shadows the cactus.
    for t in ['compS_single_get_ne', 'compS_single_get_self']:
        i = s.index('theorem ResUT.' + t)
        j = s.index('\n\n', i)
        blk = s[i:j]
        blk = blk.replace('{K σ : ResUT Loc Val K}', '{Kr σ : ResUT Loc Val K}')
        blk = blk.replace('ψ) K σ)', 'ψ) Kr σ)').replace('K.get', 'Kr.get')
        s = s[:i] + blk + s[j:]
    s = s.replace('''      (CellUT.immOf s w χ hc).InStratum (TSet.single α) → s.mem α → False := by
    intro s w χ hc hin hmem
    exact absurd (s.meet_least α hmem)
      (not_le_of_gt ((CellUT.inStratum_immOf α s w χ hc).mp hin))''', '''      (CellUT.immOf s w χ hc).InStratum (TSet.single α) → α ∈ s.set → False := by
    intro s w χ hc hin hmem
    exact Cactus.lt_irrefl _ α (hin α (by simp) α hmem)''')
    s = s.replace('        exact key _ v ρv hv hφα rfl', '        exact key _ v ρv hv hφα (by simp)')
    s = s.replace('''        have hjoin : s₁.join = α := by
          have hm : (s₁.union s₂).mem s₁.join := Or.inl s₁.join_mem
          rw [hs] at hm; exact hm
        exact key _ w χ k₁ hφα (hjoin ▸ s₁.join_mem)''', '''        obtain ⟨y, hy⟩ := s₁.ne
        have hyα : y = α := by
          have hm : y ∈ (s₁ ∪ s₂).set := Finset.mem_union_left _ hy
          rw [hs] at hm; simpa using hm
        exact key _ w χ k₁ hφα (hyα ▸ hy)''')
if name == 'Six34to39':
    # Definition 6.2's `mut` alternative carries the antichain fact (`Tree/Port/Cells.lean`).
    s = re.sub(r"⟨(a'?), (P'?), ", r"⟨\1, _, \2, ", s)
    s = s.replace('refine ⟨fun l s v χ hh => ?_, fun l b P => ?_⟩', 'refine ⟨fun l s v χ hh => ?_, fun l b _ P => ?_⟩')
    s = s.replace('exact Or.inl ⟨a, _, P, hA, hC⟩', 'exact Or.inl ⟨a, inferInstance, P, hA, hC⟩')
    s = re.sub(r"(?<![.\w])(σ\w*'?)\.borrowPart\b", r"(ResUT.borrowPart \1)", s)
    s = s.replace('''    have hsub : ∀ x, s₁.mem x → (TSet.single α).mem x := fun x hx =>
      ResUT.CompR.get_ls_imm hCompRG hψ' hσρρl hx
    obtain ⟨y, hy⟩ := LSet.nonempty s₁
    have hmem : s₁.mem α := by
      have hyα : y = α := hsub y hy
      exact hyα ▸ hy
    have hstr := hσGstrat l _ hψ'
    rw [CellUT.inStratum_immOf] at hstr
    exact absurd (s₁.meet_least α hmem) (not_le_of_gt hstr)''', '''    have hsub : ∀ x, x ∈ s₁.set → x ∈ (TSet.single α).set := fun x hx =>
      ResUT.CompR.get_ls_imm hCompRG hψ' hσρρl hx
    obtain ⟨y, hy⟩ := s₁.ne
    have hmem : α ∈ s₁.set := by
      have hyα : y = α := by simpa using hsub y hy
      exact hyα ▸ hy
    have hstr := hσGstrat l _ hψ'
    rw [CellUT.inStratum_immOf] at hstr
    exact Cactus.lt_irrefl _ α (hstr α (by simp) α hmem)''')
    i = s.index('obtain ⟨e₁, e₂, EX, a₁, a₂, AG, K, he₁')
    j = s.index('  have hsim : ResUT.SimForm', i)
    blk = s[i:j]
    blk = blk.replace('AG, K, he₁', 'AG, Kr, he₁').replace("AG', K', he₁'", "AG', Kr', he₁'")
    blk = re.sub(r"(?<![.\w])K(?=\.get|\s+σif|\s+σ)", 'Kr', blk)
    blk = re.sub(r"(?<![.\w])K'(?=\.get|\s+σif|\s+σ)", "Kr'", blk)
    blk = blk.replace('hstr)) K σif', 'hstr)) Kr σif').replace("hstr)) K' σif'", "hstr)) Kr' σif'")
    s = s[:i] + blk + s[j:]
    s = re.sub(r'(?<![.\w])G\.(get|InStratum|del)\b', r'Gr.\1', s)
    s = s.replace('''theorem ResUT.sixThirtyEight_of_residual
    (h : ResUT.SixThirtyEightResidual) : ResUT.SixThirtyEight := by''', '''theorem ResUT.sixThirtyEight_of_residual {K : WCactus}
    (h : ResUT.SixThirtyEightResidual (K := K)) : ResUT.SixThirtyEight (K := K) := by''')
    s = s.replace('theorem ResUT.sixThirtyEightResidual : ResUT.SixThirtyEightResidual := by',
                  'theorem ResUT.sixThirtyEightResidual : ResUT.SixThirtyEightResidual (K := K) := by')
    s = s.replace('theorem ResUT.six38 : ResUT.SixThirtyEight :=', 'theorem ResUT.six38 {K : WCactus} : ResUT.SixThirtyEight (K := K) :=')
    i = s.index('theorem ResUT.flat_imm_normal')
    j = s.index('\ntheorem ', i + 10)
    blk = s[i:j].replace('AG K iw σ\'', 'AG Kr iw σ\'').replace('(hK : ResUT.CompS EX AG K)', '(hK : ResUT.CompS EX AG Kr)')
    blk = blk.replace('(hnone : K.get l = none)', '(hnone : Kr.get l = none)').replace('hstr)) K σ\'', 'hstr)) Kr σ\'')
    s = s[:i] + blk + s[j:]
open(p, 'w').write(s)
