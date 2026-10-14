import Paper
import Support

/-!
# PartialLife — three of the census's class (iii) places, proved without comparing two lifetimes

The census (`scripts/classify.py`) puts twelve declarations in class (iii): their proofs compare two
lifetimes no order relation is known between. For three of them the comparison is in the proof
and not in the statement. Here each statement is proved again, as stated in the library, from
lemmas that hold in every partial order or semilattice: `InStratum.mono` along `⊔`/`⊓` bounds, and
the stratum a composite carries in the composition it is given.

* `conj_assoc'` (`SPropS.conj_assoc`): `r ∈ Res_{b ⊓ c}` from `r ∈ Res_b`, by `inf_le_left`;
* `compS_assoc'` (`CellU.compS_assoc`): the regrouped union's witness stratum
  `⊔(ᾱ₁ ∪ ᾱ₂) ≤ ⊔(ᾱ₁ ∪ (ᾱ₂ ∪ ᾱ₃))` from the given composite's, by `sup_le_sup_left`;
* `ptoImm_agree'` (`BoLo.ptoImm_agree`, `[TR]` 6.115): the composite's witness stratum read off the
  composition `ρ₁ ● ρ₂ = ρ` the statement is given.

`*_same` checks each statement is the library's, by `rfl` on the types. The census run on this file
puts every declaration in class (ii) or (i).
-/

noncomputable section

namespace PartialLife
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-- `SPropS.conj_assoc`, without comparing two lifetimes. -/
theorem conj_assoc' {a b c : Life} (P : Val → SPropS Loc Val a)
    (Q : Val → SPropS Loc Val b) (T : Val → SPropS Loc Val c) (r : ResU Loc Val)
    (hr : r.InStratum ((a ⊓ b) ⊓ c)) (hr' : r.InStratum (a ⊓ (b ⊓ c))) (w : Val) :
    SPropS.conj (SPropS.conj P Q) T w ⟨r, hr⟩ ↔
      SPropS.conj P (SPropS.conj Q T) w ⟨r, hr'⟩ := by
  simp only [SPropS.conj, SPropS.embed]
  constructor
  · rintro ⟨⟨hab, ⟨h₁, hp⟩, h₂, hq⟩, h₃, ht⟩
    exact ⟨⟨h₁, hp⟩, ⟨h₂.mono inf_le_left, ⟨h₂, hq⟩, ⟨h₃, ht⟩⟩⟩
  · rintro ⟨⟨h₁, hp⟩, hbc, ⟨h₂, hq⟩, h₃, ht⟩
    exact ⟨⟨h₁.mono inf_le_left, ⟨h₁, hp⟩, ⟨h₂, hq⟩⟩, ⟨h₃, ht⟩⟩

theorem conj_assoc'_same :
    (type_of% @conj_assoc') = (type_of% @SPropS.conj_assoc) := rfl

/-- `CellU.compS_assoc`, without comparing two lifetimes. -/
theorem compS_assoc' (ψ₁ ψ₂ ψ₃ ω : CellU Loc Val) :
    (∃ χ, CellU.CompS ψ₂ ψ₃ χ ∧ CellU.CompS ψ₁ χ ω) ↔
    (∃ υ, CellU.CompS ψ₁ ψ₂ υ ∧ CellU.CompS υ ψ₃ ω) := by
  constructor
  · rintro ⟨χ, ⟨t₂, t₃, v, ρ, k₂, k₃, k₂₃, e₂, e₃, eχ⟩,
      ⟨s₁, s', u, σ, m₁, m', m'', f₁, fχ, fω⟩⟩
    obtain ⟨hs, hv, hρ⟩ := CellU.immOf_inj (eχ.symm.trans fχ)
    subst hs; subst hv; subst hρ
    have h₁₂ : ρ.InStratum (s₁ ∪ t₂).join :=
      m''.mono (show s₁.join ⊔ t₂.join ≤ s₁.join ⊔ (t₂.join ⊔ t₃.join) from
        sup_le_sup_left le_sup_left _)
    refine ⟨CellU.immOf (s₁ ∪ t₂) v ρ h₁₂,
      ⟨s₁, t₂, v, ρ, m₁, k₂, h₁₂, f₁, e₂, rfl⟩,
      ⟨s₁ ∪ t₂, t₃, v, ρ, h₁₂, k₃, ?_, rfl, e₃, ?_⟩⟩
    · exact (LSet.union_assoc s₁ t₂ t₃) ▸ m''
    · rw [fω]
      exact CellU.immOf_congr (LSet.union_assoc s₁ t₂ t₃).symm rfl rfl m'' _
  · rintro ⟨υ, ⟨s₁, t₂, v, ρ, m₁, k₂, m₁₂, f₁, e₂, eυ⟩,
      ⟨s', t₃, u, σ, m', k₃, m'', fυ, e₃, fω⟩⟩
    obtain ⟨hs, hv, hρ⟩ := CellU.immOf_inj (eυ.symm.trans fυ)
    subst hs; subst hv; subst hρ
    have h₂₃ : ρ.InStratum (t₂ ∪ t₃).join :=
      m''.mono (show t₂.join ⊔ t₃.join ≤ (s₁.join ⊔ t₂.join) ⊔ t₃.join from
        sup_le_sup_right le_sup_right _)
    refine ⟨CellU.immOf (t₂ ∪ t₃) v ρ h₂₃,
      ⟨t₂, t₃, v, ρ, k₂, k₃, h₂₃, e₂, e₃, rfl⟩,
      ⟨s₁, t₂ ∪ t₃, v, ρ, m₁, h₂₃, ?_, f₁, rfl, ?_⟩⟩
    · exact (LSet.union_assoc s₁ t₂ t₃).symm ▸ m''
    · rw [fω]
      exact CellU.immOf_congr (LSet.union_assoc s₁ t₂ t₃) rfl rfl m'' _

theorem compS_assoc'_same :
    (type_of% @compS_assoc') = (type_of% @CellU.compS_assoc) := rfl

/-- `BoLo.ptoImm_agree` (`[TR]` 6.115), without comparing two lifetimes: the composite's witness
stratum is the one the given composition carries. -/
theorem ptoImm_agree' (l : Loc) (α β : Life) (P Q : Val → SPropU Loc Val) :
    (ptoImm l α P ⋆ ptoImm l β Q) ⊨ ptoImm l (α ⊓ β) (fun v => and (P v) (Q v)) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨s, v₁, σ₁, h₁, rfl, hP, hα⟩, ⟨t, v₂, σ₂, h₂, rfl, hQ, hβ⟩⟩
  obtain ⟨rfl, rfl⟩ := ResU.compatS_single_imm_inv hc.1
  have h₃ : σ₁.InStratum (s ∪ t).join := by
    rcases ResU.Comp.get hc l with ⟨e, -, -⟩ | ⟨ψ, -, e, -⟩ | ⟨ψ, e, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, -, hC⟩
    · exact absurd e (by simp)
    · exact absurd e (by simp)
    · exact absurd e (by simp)
    · rw [ResU.single_get_self] at e₁ e₂
      cases Option.some.inj e₁
      cases Option.some.inj e₂
      obtain ⟨s', t', v, ρ', k₁, k₂, k₃, f₁, f₂, -⟩ := hC
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj f₁
      obtain ⟨rfl, -, -⟩ := CellU.immOf_inj f₂
      exact k₃
  refine ⟨s ∪ t, v₁, σ₁, h₃,
    ResU.CompS.functional hc (ResU.compS_single_imm l s t v₁ σ₁ h₁ h₂ h₃),
    ⟨hP, hQ⟩, ?_⟩
  exact inf_le_inf hα hβ

theorem ptoImm_agree'_same :
    (type_of% @ptoImm_agree') = (type_of% @ptoImm_agree) := rfl

end PartialLife

end
