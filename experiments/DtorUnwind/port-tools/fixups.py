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
    rep("  · exact absurd (by simp : (CellUT.ownOf (Loc := Loc) v).kind = Kind.own) hk\n  · refine ⟨CellUT.immOf s v χ hh, ?_, Or.inr", "  · exact absurd (by simp : (CellUT.ownOf (K := K) (Loc := Loc) v).kind = Kind.own) hk\n  · refine ⟨CellUT.immOf s v χ hh, ?_, Or.inr")
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
open(f, 'w').write(s)
if name == 'WalkSplitting': drop('CellUT.CompS.kind', 'CellUT.CompS.wit')
if name == 'Compatibility': drop('CellUT.compatS_iff')
if name == 'Split': drop('ResUT.CompS.assoc', 'CellUT.compatR_iff')
if name == 'AlgebraInstances': drop('ResUT.CompR.comm', 'ResUT.CompR.assoc', 'CellUT.CompS.at', 'CellUT.CompS.inStratum')
if name == 'UpdateFrame': drop('wandAll')
