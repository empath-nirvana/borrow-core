"""Hand fixes for the ClosingSentence port: the lifetime-set lemmas read on TSet."""
import re, sys
p = sys.argv[1]
s = open(p).read()
def rep(a, b):
    global s
    if a not in s:
        print('[closfix] pattern not found: ' + a[:70])
    s = s.replace(a, b)
s = s.replace("⟨b', w, ξ, hξ, P, hP, hw⟩", "⟨b', _, w, ξ, hξ, P, hP, hw⟩")
rep('''/-- `⊓ᾱ ⊐ β` gives `β ∉ ᾱ`. -/
theorem LSet.notMem_of_meet_sqsupset {s : TSet} {b : TSet} (h : s.meet ⊐ b) :
    ¬ s.mem b := fun hb => absurd (s.meet_least b hb) (by exact not_le.mpr h)''',
'''/-- `ᾱ` strictly above `{β}` gives `β ∉ ᾱ`. -/
theorem TSet.notMem_of_above {K : WCactus} {s : TSet} {b : Life}
    (h : K.Above (TSet.single b) s) : b ∉ s.set :=
  fun hb => Cactus.lt_irrefl _ b (h b (by simp) b hb)''')
rep('''    {χ : ResUT Loc Val K} {h : χ.InStratum s} {b : TSet}
    (hc : (CellUT.immOf s v χ h).InStratum b) : ¬ s.mem b :=
  LSet.notMem_of_meet_sqsupset hc''', '''    {χ : ResUT Loc Val K} {h : χ.InStratum s} {b : Life}
    (hc : (CellUT.immOf s v χ h).InStratum (TSet.single b)) : b ∉ s.set :=
  TSet.notMem_of_above hc''')
s = s.replace('LSet.union_singleton_ne_singleton', 'TSet.union_singleton_ne_singleton')
rep('''theorem TSet.union_singleton_ne_singleton {s : TSet} {b : TSet} (hs : ¬ s.mem b) :
    s ∪ LSet.singleton b ≠ LSet.singleton b := by
  intro h
  have hj : (s ∪ LSet.singleton b).mem s.join := Or.inl s.join_mem
  rw [h] at hj
  exact hs ((hj : s.join = b) ▸ s.join_mem)''', '''theorem TSet.union_singleton_ne_singleton {s : TSet} {b : Life} (hs : b ∉ s.set) :
    s ∪ TSet.single b ≠ TSet.single b := by
  intro h
  obtain ⟨y, hy⟩ := s.ne
  have hj : y ∈ (s ∪ TSet.single b).set := Finset.mem_union_left _ hy
  rw [h] at hj
  have : y = b := by simpa using hj
  exact hs (this ▸ hy)''')
s = s.replace('(s ∪ TSet.single β).join', '(s ∪ TSet.single β)')
s = s.replace('¬ s.mem β', 'β ∉ s.set')
rep('    exact absurd ((CellUT.inStratum_immOf β _ v χ hχ).mp ho) (lt_irrefl _)',
    '    exact (Cactus.lt_irrefl _ β (ho β (by simp) β (by simp))).elim')
s = s.replace('⟨_, _, _, _, _, _, _, _, _, _, -, e₂, -⟩', '⟨_, _, _, _, _, _, _, _, _, _, _, _, -, e₂, -⟩')
rep('    exact LSet.notMem_of_meet_sqsupset ((CellUT.inStratum_immOf β s₁ v χ k₁).mp ho)',
    '    exact TSet.notMem_of_above ho')
rep('''theorem LSet.union_singleton_le_cancel {s t : TSet} {b : TSet} (hs : ¬ s.mem b)
    (h : s ∪ (t ∪ LSet.singleton b) = t ∪ LSet.singleton b) : s ∪ t = t := by
  refine LSet.ext (fun x => ?_)
  have hx : (s ∪ (t ∪ LSet.singleton b)).mem x ↔ (t ∪ LSet.singleton b).mem x := by
    rw [h]
  by_cases hb : x = b
  · subst hb
    exact ⟨fun c => c.elim (fun d => absurd d hs) id, fun c => Or.inr c⟩
  · refine ⟨fun c => ?_, fun c => Or.inr c⟩
    rcases c with c | c
    · exact ((hx.mp (Or.inl c)).elim id (fun d => absurd d hb))
    · exact c''', '''theorem TSet.union_singleton_le_cancel {s t : TSet} {b : Life} (hs : b ∉ s.set)
    (h : s ∪ (t ∪ TSet.single b) = t ∪ TSet.single b) : s ∪ t = t := by
  refine TSet.ext (Finset.ext fun x => ?_)
  have hx : x ∈ (s ∪ (t ∪ TSet.single b)).set ↔ x ∈ (t ∪ TSet.single b).set := by
    rw [h]
  simp only [TSet.union_set, TSet.single_set, Finset.mem_union, Finset.mem_singleton] at hx ⊢
  by_cases hb : x = b
  · subst hb
    exact ⟨fun c => c.elim (fun d => absurd d hs) id, fun c => Or.inr c⟩
  · refine ⟨fun c => ?_, fun c => Or.inr c⟩
    rcases c with c | c
    · exact (hx.mp (Or.inl c)).elim id (fun d => absurd d hb)
    · exact c''')
s = s.replace('LSet.union_singleton_le_cancel', 'TSet.union_singleton_le_cancel')
s = s.replace('¬ a.mem β', 'β ∉ a.set')
s = s.replace('∀ (β : TSet) (ρ\'i', '∀ (β : Life) (ρ\'i')
# 6.59's residuals carry 6.52's reading of `↓β`.
s = s.replace("""    (l₀ : BoCa.Loc) (s : TSet) (v : BoCa.Val) (hs : ρ'i.InStratum s),
    ResUT.Reb β ρ'i ρ →""", """    (l₀ : BoCa.Loc) (s : TSet) (v : BoCa.Val) (hs : ρ'i.InStratum s) (D : TSet),
    K.DownOf D (TSet.single β) → ResUT.Reb β ρ'i ρ →""")
open(p, 'w').write(s)
