import TypedCasePort.FrameKept
import Core.Chain.SI.HeapN
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont freeE hndE ubindE ccatchE cfinE)
def rwpOwn (Φ : LocFam) (Q : PostN) (n : Nat) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TWNC fρ ps (rsOf ls) → Tagged fρ ps ls →
    ResU.Lower fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' →
      FrameKept ρf μ' ∧
      (∀ v : Val, e' = v.1 → EndOK Φ Q (n - j) ls ρ ρf ps μ' v) ∧
      (¬ IsVal e' → ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'')

/-- **G at a run's end**: the post-configuration keeps the frame. -/

theorem EndOK.frameKept {Φ : LocFam} {Q : PostN} {k : Nat} {ls : List SRec} {ρ ρf : WRes}
    {ps : List FrameRec} {μ' : Heap} {v : Val} (h : EndOK Φ Q k ls ρ ρf ps μ' v) :
    FrameKept ρf μ' := by
  obtain ⟨_, _, fρ', fρ'p, _, _, _, _, h₂, h₃, h₄, h₅, _⟩ := h
  exact ((frameKept_lower h₅).of_compS h₄ (by obtain ⟨σ, hσ, -⟩ := h₅; exact ⟨σ, hσ⟩)).of_compS
    h₂ (hash_valid h₃).2

theorem ownwp_head1 {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    {μ₀ μ₀' : Heap} {a₀ : Expr} (hred : Head (ℍ := ℍ) μ₀ e μ₀' a₀)
    (hstep : ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TWNC fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → FinDom μ →
      (∃ μ₁ e₁, Head (ℍ := ℍ) μ e μ₁ e₁) ∧
      ∀ μ₁ e₁, Head (ℍ := ℍ) μ e μ₁ e₁ →
        ∃ v : Val, e₁ = v.1 ∧ EndOK Φ Q (n - 1) ls ρ ρf ps μ₁ v) :
    rwpOwn (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun
  obtain ⟨⟨μ₁, e₁, hh⟩, hend⟩ := hstep ρf fρ ps μ hf hc hT htg hl hfd
  have hnv : ¬ IsVal e := hred.not_isVal
  cases hrun with
  | refl =>
      exact ⟨frameKept_of_lower hc hl, fun v hv => absurd (hv ▸ v.2) hnv,
        fun _ => ⟨μ₁, e₁, ⟨Kont.hole, e, e₁, by simp [Kont.plug], by simp [Kont.plug], hh⟩⟩⟩
  | @more j' _ μ₂ _ _ e₂ _ h t =>
      obtain ⟨w, rfl, hEnd⟩ := hend μ₂ e₂ (step1_head hred h)
      cases t with
      | refl =>
          refine ⟨hEnd.frameKept, fun v hv => ?_, fun hn => absurd w.2 hn⟩
          have : v = w := Subtype.ext hv.symm
          subst this
          simpa using hEnd
      | more h' _ => exact absurd h' BoLo.no_step_val


theorem ownwp_alloc {Φ : LocFam} (ls : List SRec) (v : Val) (Q : PostN) {n : Nat} {ρ : WRes}
    (h : (all fun l : BoCa.Loc => wand (ptoOwn l v) (Q (n - 1) ls (.loc l))) ρ) :
    rwpOwn (ℍ := ℍ) Φ Q n ls (.app (.val (.prim .alloc)) (.val v)) ρ := by
  refine ownwp_head1 (Head.alloc (fun _ => none) v 0 rfl) (fun ρf σ ps μ hf hσ hT htg hμ hfin => ?_)
  obtain ⟨τ, hτ, hval⟩ := id hμ
  obtain ⟨ℓ₀, hℓ₀⟩ := BoLo.finDom_block hfin
  refine ⟨⟨_, _, Head.alloc μ v ℓ₀ (by simpa using hℓ₀ 0)⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨l, hμl, rfl, rfl⟩ := head_alloc_inv hh
  have hl : τ.get l = none := (lower_eq_none_iff hval).mp hμl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ hl)).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ
  have hT' : TWNC σ' ps (rsOf ls) := TWNC.alloc hT hμ hμl hyσ' (hash_valid_comp hfx hσ'x)
  exact ⟨⟨.loc l, (Val.loc l).2⟩, rfl, x, PMap.empty, σ', σ', x, ps, ls,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    ResU.comp_empty_right σ', hlow', ResU.comp_empty_right x,
    updVN_of_updV Φ _ (updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2),
    noOwn_empty, hT', tagged_of_ag (fun a ha => alloc_ag hyσ' ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, h l _ x rfl hx⟩

/-- **`[TR]` 6.142 (`wp-free`) at the step index** (`wpTS_free`). -/

theorem ownwp_free {Φ : LocFam} (ls : List SRec) (l : BoCa.Loc) (v : Val) (Q : PostN) {n : Nat}
    {ρ : WRes} (h : (sep (ptoOwn l v) (Q (n - 1) ls v)) ρ) :
    rwpOwn (ℍ := ℍ) Φ Q n ls (.app (.val (.prim .free)) (.val (.loc l))) ρ := by
  obtain ⟨ρ₁, ρ₂, hcρ, rfl, hQ⟩ := h
  refine ownwp_head1 (Head.free (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf σ ps μ hf hσ hT htg hμ hfin => ?_)
  have h₂ : ResU.Hash ρf ρ₂ :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf ρ₂ (ResU.single l (CellU.ownOf v)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  have hdel : BoCa.BoLo.Heap.del μ l = μ₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.del_same, hnone]
    · rw [BoCa.BoLo.Heap.del_other e, hupd, BoCa.BoLo.Heap.upd_other e]
  refine ⟨⟨_, _, Head.free μ l v hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨u, hu, rfl, rfl⟩ := head_free_inv (ℍ := ℍ) hh
  rw [hlv] at hu
  cases hu
  have hT' : TWNC σ₂ ps (rsOf ls) :=
    TWNC.free hT (ResU.CompS.comm hσ₂σ) (hash_valid_comp h₂ hσ₂)
  refine ⟨v, rfl, ρ₂, PMap.empty, σ₂, σ₂, ρ₂, ps, ls,
    ResU.hash_symm h₂, hσ₂,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp h₂ hσ₂)),
    ResU.comp_empty_right σ₂, ?_, ResU.comp_empty_right ρ₂,
    updVN_of_updV Φ _
      (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm,
    noOwn_empty, hT',
    tagged_of_ag (fun a ha => (own_cell_ag (ResU.CompS.comm hσ₂σ) a).mpr ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩
  rw [hdel]; exact hlow₂


theorem ownwp_load {Φ : LocFam} (ls : List SRec) (l : BoCa.Loc) (v : Val) (Q : PostN) {n : Nat}
    {ρ : WRes} (h : (sep (ptoOwn l v) (wand (ptoOwn l v) (Q (n - 1) ls v))) ρ) :
    rwpOwn (ℍ := ℍ) Φ Q n ls (.app (.val (.prim .load)) (.val (.loc l))) ρ := by
  obtain ⟨ρ₁, ρ₂, hcρ, rfl, hwand⟩ := h
  refine ownwp_head1 (Head.load (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf σ ps μ hf hσ hT htg hμ hfin => ?_)
  have hρ : ρ.get l = some (CellU.ownOf v) := by
    rw [ResU.Comp.get_of_right_none hcρ (ResU.compatS_single_own hcρ.1),
      ResU.single_get_self]
  have hlv : μ l = some v :=
    lower_get_own hμ (by
      rw [ResU.Comp.get_of_left_none hσ (get_eq_none_of_compatS_own
        (ResU.CompatS.symm hf.1) hρ)]
      exact hρ)
  refine ⟨⟨_, _, Head.load μ l v hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨u, hu, rfl, rfl⟩ := head_load_inv hh
  rw [hlv] at hu
  cases hu
  exact ⟨v, rfl, ρ, PMap.empty, σ, σ, ρ, ps, ls,
    ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hσ)),
    ResU.comp_empty_right σ, hμ, ResU.comp_empty_right ρ,
    UpdVN.refl Φ _ (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hwand _ ρ rfl (ResU.CompS.comm hcρ)⟩


end BoCa.Fig16.LogRel.Core.Chain.SI
end
