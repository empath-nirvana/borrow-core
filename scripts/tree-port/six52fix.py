"""Hand fixes for Six49to52 (run after lifefix.py): `↓α` read as a stratum `D` with
`K.DownOf D {α}`, as in 6.27; 6.50 at any stratum."""
import re, sys
p = sys.argv[1]
s = open(p).read()
def rep(a, b, n=1):
    global s
    if a not in s:
        print('[six52fix] pattern not found: ' + a[:70])
    s = s.replace(a, b)
# 6.49: the `mut` clause of `↭` quantifies over the antichain fact.
rep('fun l b P =>', 'fun l b _ P =>')
# 6.50 at a stratum.
rep('''theorem updV_outlives {ρ ρ' : (ResUT BoCa.Loc BoCa.Val K)} {α : Life} (h : Outlives ρ α)
    (hu : ResUT.UpdV ρ ρ') : Outlives ρ' α := by
  have hρ : ρ.InStratum (TSet.single α) := h''', '''theorem updV_outlives {ρ ρ' : (ResUT BoCa.Loc BoCa.Val K)} {α : TSet} (h : ρ.InStratum α)
    (hu : ResUT.UpdV ρ ρ') : ρ'.InStratum α := by
  have hρ : ρ.InStratum α := h''')
rep('  have hsσ : σ.InStratum (TSet.single α) := flat_inStratum hσ hρ', '  have hsσ : ResUT.InStratum α σ := flat_inStratum hσ hρ')
rep('    exact (hsσ l _ hg : b ⊐ α)', '    exact (hsσ l _ hg : K.Above α b)')
# the image of `reb_α` in `Res_D`
rep('''theorem ResUT.reb_inStratum_down {α : Life} {ρ' ρ : ResUT Loc Val K}
    (h : ResUT.Reb α ρ' ρ) : ρ.InStratum (↓α) := by''', '''theorem ResUT.reb_inStratum_down {α : Life} {D : TSet} (hD : K.DownOf D (TSet.single α))
    {ρ' ρ : ResUT Loc Val K} (h : ResUT.Reb α ρ' ρ) : ρ.InStratum D := by''')
rep('      (CellUT.InStratum.mono (le_of_lt (Life.down_sqsubset α)) (h.1 l φ hφ))',
    '      (CellUT.InStratum.mono (fun x hx => ⟨α, by simp, (hD.1 x hx α (by simp)).le⟩) (h.1 l φ hφ))')
rep('''    rw [hψ]
    exact Life.down_sqsubset α''', '''    rw [hψ]
    exact hD.1''')
# 6.52 and its parts take `D`.
s = s.replace('''    (hreb : ResUT.Reb α ρ'i ρ)
    (hce : ResUT.CompS ρ ρe ρρe)''', '''    {D : TSet} (hD : K.DownOf D (TSet.single α))
    (hreb : ResUT.Reb α ρ'i ρ)
    (hce : ResUT.CompS ρ ρe ρρe)''')
s = s.replace('''  have hdle : (↓α) ≤ α := le_of_lt (Life.down_sqsubset α)
  have hρρe : ρρe.InStratum (↓α) :=
    ResUT.CompS.inStratum hce (ResUT.reb_inStratum_down hreb)
      (ResUT.InStratum.mono hdle hse)
  have hpdown : ρp.InStratum (↓α) :=''', '''  have hdle : ∀ x ∈ D.set, ∃ y ∈ (TSet.single α).set, K.le x y :=
    fun x hx => ⟨α, by simp, (hD.1 x hx α (by simp)).le⟩
  have hρρe : ρρe.InStratum D :=
    ResUT.CompS.inStratum hce (ResUT.reb_inStratum_down hD hreb)
      (ResUT.InStratum.mono hdle hse)
  have hpdown : ρp.InStratum D :=''')
rep('''  have hnb : ∀ m φ, ρp.get m = some φ → ¬ (φ.at < α) :=
    fun m φ e => CellUT.not_at_lt_of_inStratum_down (hpdown m φ e)''', '''  have hnb : ∀ m φ, ρp.get m = some φ → ¬ φ.Shorter α :=
    ResUT.not_shorter_of_down hD hpdown''')
rep("    have hmem : s'.mem α := by rw [hs'eq]; rfl", "    have hmem : α ∈ s'.set := by rw [hs'eq]; simp")
rep('    have hmemζ : tζ.mem α :=', '    have hmemζ : α ∈ tζ.set :=')
rep('    have hmemπ : tπ.mem α :=', '    have hmemπ : α ∈ tπ.set :=')
rep('    have hmemp : ∃ ξ t, σp.get l = some ξ ∧ ξ.lsOfI = some t ∧ t.mem α := by',
    '    have hmemp : ∃ ξ t, σp.get l = some ξ ∧ ξ.lsOfI = some t ∧ α ∈ t.set := by')
rep('''      · exact absurd (t.meet_least α hxt)
          (not_le_of_gt (CellUT.sqsupset_of_lsOf ht (hσ''s l ξ e)))''', '''      · exact absurd (CellUT.above_of_lsOfI ht (hσ''s l ξ e) α (by simp) α hxt)
          (Cactus.lt_irrefl _ α)''')
s = s.replace('CellUT.kind_of_lsOf ', 'CellUT.kind_of_lsOfI ')
rep("      rw [show x = α from hx, ← htωeq]", "      rw [show x = α by simpa using hx, ← htωeq]")
s = s.replace('ResUT.six52_H1 hreb ', 'ResUT.six52_H1 hD hreb ')
s = s.replace('ResUT.six52_sub_inStratum hreb ', 'ResUT.six52_sub_inStratum hD hreb ')
rep('  refine ResUT.Sub.inStratum hsub hpdown ?_ ?_', '  refine ResUT.Sub.inStratum hD hsub hpdown ?_ ?_')
rep('        ResUT.inStratum_comp_at (CellUT.compS_hC α) hce', '        ResUT.inStratum_comp_at (CellUT.compS_hC (TSet.single α)) hce')
rep('      (fun ξ e => ResUT.updV_outlives_at hρρe hupd hρρel e) hφ', '      (fun ξ e => ResUT.updV_outlives_at hD hρρe hupd hρρel e) hφ')
rep('    exact ⟨s, TSet.single α, v, w, hs, hw, hpl, hζeq, rfl⟩', '    exact ⟨s, TSet.single α, v, w, hs, hw, hpl, hζeq, by simp⟩')
rep('''the `ResUT.SubKeep` form is `ResUT.six52_keep`]` -/
theorem ResUT.six52 {α : Life}''', '''the `ResUT.SubKeep` form is `ResUT.six52_keep`]`. Over the tree-stratified carrier.
**Forced change:** the proof's "no borrows at any lifetime shorter than `α`" reads `↓α`
(row 5.12, `α + 1`) as a stratum `D` with `K.DownOf D {α}` (`hD`), as 6.27 does; in a tree
`α` need not have a child, so it is a hypothesis, and a covering child of `α` gives one
(`WCactus.downOf_covers`). The proof is the printed one with `↓α` read through `hD`. -/
theorem ResUT.six52 {α : Life}''')
open(p, 'w').write(s)
