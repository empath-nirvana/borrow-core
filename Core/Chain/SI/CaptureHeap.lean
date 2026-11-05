import Core.Chain.SI.CaptureE

/-!
# Heap steps at `crwpG`, with their exact resources

`[TR]` 6.141 (alloc), 6.142 (free) and 6.143 (load through an `imm` borrow) at `crwpG`, by the
proofs of `rwp_alloc`, `rwp_free`, `rwp_load_I` (`SI/HeapN.lean`), each at the resource the step
leaves: `ρ ● ℓ ↦ own(v)`, `ρ` without `ℓ`, `ρ` unchanged. `cerwp_bindRwp` lifts the `rwp` lemmas
with their garbage; a scheduler that must know every borrow it holds (to hand them back at a
join, `SI/CaptureScope.lean`) uses these instead.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-- **One head step to a value, at `crwpG`** (`rwp_head1`). -/
theorem crwpG_head1 {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} {e : Expr} {ρ : WRes} {μ₀ μ₀' : Heap} {a₀ : Expr}
    (hred : Head (ℍ := ℍ) μ₀ e μ₀' a₀)
    (hstep : ∀ (ρf fρ : WRes) (ps psF : List FrameRec) (μ : Heap),
      F ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → Split ps O psF →
      TWNC fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Lower fρ μ → FinDom μ →
      (∃ μ₁ e₁, Head (ℍ := ℍ) μ e μ₁ e₁) ∧
      ∀ μ₁ e₁, Head (ℍ := ℍ) μ e μ₁ e₁ → ∃ v : Val, e₁ = v.1 ∧ EndC Q (n - 1) ρf psF μ₁ v.1) :
    crwpG (ℍ := ℍ) F Q n ls O e ρ := by
  intro ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨⟨μ₁, e₁, hh⟩, hend⟩ := hstep ρf fρ ps psF μ hF hf hc hS hT htg hl hfd
  cases hrun with
  | refl =>
      exact absurd ⟨Kont.hole, e, e₁, by simp [Kont.plug], by simp [Kont.plug], hh⟩ (hfin μ₁ e₁)
  | @more j' _ μ₂ _ _ e₂ _ h t =>
      obtain ⟨w, rfl, hEnd⟩ := hend μ₂ e₂ (step1_head hred h)
      cases t with
      | refl => simpa using hEnd
      | more h' _ => exact absurd h' BoLo.no_step_val

/-- **`[TR]` 6.141 at `crwpG`**: the new cell joins the resource. -/
theorem crwpG_alloc {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} (v : Val) {ρ : WRes}
    (h : ∀ (ℓ : Loc) (ρ' : WRes), ResU.CompS ρ (ResU.single ℓ (CellU.ownOf v)) ρ' →
      Q (n - 1) ls O (Val.loc ℓ).1 ρ') :
    crwpG (ℍ := ℍ) F Q n ls O (.app (.val (.prim .alloc)) (.val v)) ρ := by
  refine crwpG_head1 (Head.alloc (fun _ => none) v 0 rfl)
    (fun ρf σ ps psF μ _ hf hσ hS hT htg hμ hfin => ?_)
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
  exact ⟨Val.loc l, rfl, x, σ', ps, O, ls, ResU.hash_symm hfx, hσ'x, hlow', hS, hT',
    tagged_of_ag (fun a ha => alloc_ag hyσ' ha) htg, h l x hx⟩

/-- **`[TR]` 6.142 at `crwpG`**: the cell leaves the resource. -/
theorem crwpG_free {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} (l : Loc) (v : Val) {ρ ρ₂ : WRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρ₂ ρ) (hQ : Q (n - 1) ls O v.1 ρ₂) :
    crwpG (ℍ := ℍ) F Q n ls O (BoLo.freeE (.val (Val.loc l))) ρ := by
  refine crwpG_head1 (Head.free (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf σ ps psF μ _ hf hσ hS hT htg hμ hfin => ?_)
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
  refine ⟨v, rfl, ρ₂, σ₂, ps, O, ls, ResU.hash_symm h₂, hσ₂, ?_, hS, hT',
    tagged_of_ag (fun a ha => (own_cell_ag (ResU.CompS.comm hσ₂σ) a).mpr ha) htg, hQ⟩
  rw [hdel]; exact hlow₂

/-- **`[TR]` 6.143 through an `imm` borrow, at `crwpG`**: the resource is kept. -/
theorem crwpG_loadI {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} (l : Loc) {s : LSet} {u : Val} {χ : WRes} {h : χ.InStratum s.join}
    {ρ ρR : WRes} (hc : ResU.CompS (ResU.single l (CellU.immOf s u χ h)) ρR ρ)
    (hQ : Q (n - 1) ls O u.1 ρ) :
    crwpG (ℍ := ℍ) F Q n ls O (.app (.val (.prim .load)) (.val (Val.loc l))) ρ := by
  refine crwpG_head1 (Head.load (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf τ ps psF μ _ hf hτ hS hT htg hμ hfin => ?_)
  obtain ⟨χ₁, hχ, heχ⟩ := compS_get_erase hc (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ := compS_get_erase (ResU.CompS.comm hτ) hχ
  have hlv : μ l = some u := by
    rw [lower_get hμ hχ', heχ', heχ]
    rfl
  refine ⟨⟨_, _, Head.load μ l u hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨w, hw, rfl, rfl⟩ := head_load_inv hh
  rw [hlv] at hw
  cases hw
  exact ⟨u, rfl, ρ, τ, ps, O, ls, ResU.hash_symm hf, hτ, hμ, hS, hT, htg, hQ⟩

/-! ### At `cerwp`, at an evaluation position -/

theorem cerwp_allocX {Tb : TableC} (hL : Tb.Local) {Q : PostCV} {F : WRes → Prop} (K : Kont)
    (v : Val) {n : Nat} {ls : List SRec} {O : List FrameRec} {ρ : WRes}
    (h : ∀ (ℓ : Loc) (ρ' : WRes), ResU.CompS ρ (ResU.single ℓ (CellU.ownOf v)) ρ' →
      cerwp (ℍ := ℍ) Tb Q F (n - 1) ls O (K.plug (.val (Val.loc ℓ))) ρ') :
    cerwp (ℍ := ℍ) Tb Q F n ls O (K.plug (.app (.val (.prim .alloc)) (.val v))) ρ := by
  rw [cerwp_eq]
  exact crwpG_bind K (crwpG_alloc v (fun ℓ ρ' hc =>
    cerwp_unfold_at hL (Nat.sub_le n 1) (h ℓ ρ' hc)))

theorem cerwp_freeX {Tb : TableC} (hL : Tb.Local) {Q : PostCV} {F : WRes → Prop} (K : Kont)
    (l : Loc) (v : Val) {n : Nat} {ls : List SRec} {O : List FrameRec} {ρ ρ₂ : WRes}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρ₂ ρ)
    (h : cerwp (ℍ := ℍ) Tb Q F (n - 1) ls O (K.plug (.val v)) ρ₂) :
    cerwp (ℍ := ℍ) Tb Q F n ls O (K.plug (BoLo.freeE (.val (Val.loc l)))) ρ := by
  rw [cerwp_eq]
  exact crwpG_bind K (crwpG_free l v hcρ (cerwp_unfold_at hL (Nat.sub_le n 1) h))

theorem cerwp_loadI {Tb : TableC} (hL : Tb.Local) {Q : PostCV} {F : WRes → Prop} (K : Kont)
    (l : Loc) {s : LSet} {u : Val} {χ : WRes} {h : χ.InStratum s.join} {n : Nat}
    {ls : List SRec} {O : List FrameRec} {ρ ρR : WRes}
    (hc : ResU.CompS (ResU.single l (CellU.immOf s u χ h)) ρR ρ)
    (hk : cerwp (ℍ := ℍ) Tb Q F (n - 1) ls O (K.plug (.val u)) ρ) :
    cerwp (ℍ := ℍ) Tb Q F n ls O (K.plug (.app (.val (.prim .load)) (.val (Val.loc l)))) ρ := by
  rw [cerwp_eq]
  exact crwpG_bind K (crwpG_loadI l hc (cerwp_unfold_at hL (Nat.sub_le n 1) hk))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
