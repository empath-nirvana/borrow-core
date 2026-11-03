import Support.Model.Tree.Port.UpdateFrame

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Paper/S6_2_NonStandardLemmas/Lemmas.lean:1159-1262`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-! ### Row 5.67's theorem `BoCa.Fig16.Tree.AgWT.nonimm_beneath_imm`, declared here for Lemmas 6.38, 6.48 and 6.59; its row is in `Paper/S5_Model/Remarks.lean`. -/
/-- Every non-`imm` cell of `ag(ρ)` sits beneath an `imm` cell of `ag(ρ)`.  `[about
ours: where `ag(ρ)`'s `mut` cells come from]` -/
theorem AgWT.nonimm_beneath_imm {ρ σ : ResUT Loc Val K} (h : AgWT ρ σ) :
    ∀ (n : Loc) (φ : CellUT Loc Val K), σ.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : TSet) (u : Val) (χ : ResUT Loc Val K)
        (hh : χ.InStratum s) (ev av p : ResUT Loc Val K) (ξ : CellUT Loc Val K),
        σ.get m = some (CellUT.immOf s u χ hh) ∧
        ExRT χ ev ∧ AgWT χ av ∧ ResUT.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K, CellUT.CompR ψ₁ ψ₂ ψ → CellUT.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  refine G.AgW.rec
    (motive_1 := fun ρ σ _ => ∀ (n : Loc) (φ : CellUT Loc Val K),
      σ.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : TSet) (u : Val) (χ : ResUT Loc Val K)
        (hh : χ.InStratum s) (ev av p : ResUT Loc Val K) (ξ : CellUT Loc Val K),
        σ.get m = some (CellUT.immOf s u χ hh) ∧
        ExRT χ ev ∧ AgWT χ av ∧ ResUT.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ (n : Loc) (φ : CellUT Loc Val K),
      q.2.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : TSet) (u : Val) (χ : ResUT Loc Val K)
        (hh : χ.InStratum s) (ev av p : ResUT Loc Val K) (ξ : CellUT Loc Val K),
        q.2.get m = some (CellUT.immOf s u χ hh) ∧
        ExRT χ ev ∧ AgWT χ av ∧ ResUT.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ (n : Loc) (φ : CellUT Loc Val K),
      q.2.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (s : TSet) (u : Val) (χ : ResUT Loc Val K)
        (hh : χ.InStratum s) (ev av p : ResUT Loc Val K) (ξ : CellUT Loc Val K),
        ExRT χ ev ∧ AgWT χ av ∧ ResUT.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase ∧
        ((∃ m, q.2.get m = some (CellUT.immOf s u χ hh)) ∨
          ρ.get q.1 = some (CellUT.immOf s u χ hh)))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi n φ hg hk
    rcases ResUT.CompR.nonimm_source hσ hg hk with
      ⟨ξa, ea, ka, wa, era⟩ | ⟨ξb, eb, kb, wb, erb⟩
    · rcases ResUT.CompR.nonimm_source ha ea ka with
        ⟨ξr, er, kr, wr, err⟩ | ⟨ξm, em, km, wm2, erm⟩
      · exact absurd (ResUT.restrict_eq_some.mp er).2 kr
      · obtain ⟨τ, hmem, ξ', e', k', w', er'⟩ := BigCompT.nonimm_source hbm em km
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨m, s, u, χ, hh, ev, av, pp, ξ, hqm, hex, hag, hc, hpn, hkξ, hwξ, heξ⟩ :=
          ihm q hq n ξ' e' k'
        obtain ⟨z, hz⟩ := BigCompT.mem_factor hR ResUT.compLawsR hbm q.2
          (List.mem_map.mpr ⟨q, hq, rfl⟩)
        obtain ⟨y₁, hy₁⟩ :=
          ResUT.Comp.factor_trans hR ResUT.compLawsR hz (ResUT.CompR.comm ha)
        obtain ⟨y₂, hy₂⟩ := ResUT.Comp.factor_trans hR ResUT.compLawsR hy₁ hσ
        obtain ⟨s'', h'', hσm⟩ := ResUT.CompR.imm_left_get hy₂ hqm
        exact ⟨m, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans (wm2.trans wa)),
          heξ.trans (er'.trans (erm.trans era))⟩
    · obtain ⟨τ, hmem, ξ', e', k', w', er'⟩ := BigCompT.nonimm_source hbi eb kb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨s, u, χ, hh, ev, av, pp, ξ, hex, hag, hc, hpn, hkξ, hwξ, heξ, hdisj⟩ :=
        ihi q hq n ξ' e' k'
      obtain ⟨z, hz⟩ := BigCompT.mem_factor hR ResUT.compLawsR hbi q.2
        (List.mem_map.mpr ⟨q, hq, rfl⟩)
      obtain ⟨y₁, hy₁⟩ := ResUT.Comp.factor_trans hR ResUT.compLawsR hz (ResUT.CompR.comm hσ)
      rcases hdisj with ⟨m, hqm⟩ | hρm
      · obtain ⟨s'', h'', hσm⟩ := ResUT.CompR.imm_left_get hy₁ hqm
        exact ⟨m, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans wb), heξ.trans (er'.trans erb)⟩
      · have hri : (G.restrict CellUT.kind ρ' Kind.imm).get q.1 = some (CellUT.immOf s u χ hh) :=
          ResUT.restrict_get_some hρm (CellUT.kind_immOf _ _ _ _)
        obtain ⟨s₁, h₁, ham⟩ := ResUT.CompR.imm_left_get ha hri
        obtain ⟨s'', h'', hσm⟩ := ResUT.CompR.imm_left_get hσ ham
        exact ⟨q.1, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans wb), heξ.trans (er'.trans erb)⟩
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ihe
    · exact ihw q hq'
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro n φ hg hkφ
      obtain ⟨s, hs, heta⟩ := CellUT.imm_eta hk
      rcases ResUT.CompR.nonimm_source hc hg hkφ with
        ⟨ξe, ee, ke, we, ere⟩ | ⟨ξa, ea, ka, wa, era⟩
      · exact ⟨s, ψ.erase, ψ.wit, hs, e, a, pe, φ, hex, hag, hc, hg, hkφ, rfl, rfl,
          Or.inr (hψ.trans (congrArg some heta))⟩
      · obtain ⟨m, s', u, χ, hh, ev, av, pp, ξ, ham, hex', hag', hc', hpn,
          hkξ, hwξ, heξ⟩ := iha n ξa ea ka
        obtain ⟨s'', h'', hpm⟩ :=
          ResUT.CompR.imm_left_get (ResUT.CompR.comm hc) ham
        exact ⟨s'', u, χ, h'', ev, av, pp, ξ, hex', hag', hc', hpn, hkξ,
          hwξ.trans wa, heξ.trans era, Or.inl ⟨m, hpm⟩⟩
    · exact ihw q hq'

end BoCa.Fig16.Tree

end
