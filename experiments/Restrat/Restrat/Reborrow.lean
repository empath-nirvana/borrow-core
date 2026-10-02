import Restrat.Flattening
import Support.Model.Update

/-!
# Restrat — naturality of `reb_α` and `↺_α`

`reb_α(ρ)` (row 5.28) is invariant: `e·ρ′ ∈ reb_{eα}(e·ρ) ↔ ρ′ ∈ reb_α(ρ)` (`reb_iff`), and
every member of `reb_{eα}(e·ρ)` is moved (`reb_image`).  Its witness `π` moves piecewise, as in
`relabel_reb` (`Support/TypedWorld/Images.lean`), whose `π` is kept unchanged: here every piece
is moved, and a piece of a moved resource is moved (`bigCompS_operands`).

Hence `↺_α P` moves to `↺_{eα} P′` at every `P′` agreeing with `P` (`agree_reborrow`).
-/

noncomputable section

namespace Restrat
open BoCa.Fig16 BoCa.Fig16.BoLo

namespace Emb
variable {c : Life} {e : Emb c} {Loc Val : Type}

theorem bigComp_iff {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (hR : e.Nat2 R)
    (hC : e.Nat3 C) (σs : List (ResU Loc Val)) (ρ : ResU Loc Val) :
    BigComp R C (σs.map e.relRU) (e.relRU ρ) ↔ BigComp R C σs ρ := by
  refine ⟨fun h => ?_, bigComp_fwd hR hC⟩
  obtain ⟨ρ', h', hb⟩ := bigComp_bwd hR hC h
  rwa [e.relRU_injective h']

/-- Every piece of a `⨀_●` with a moved value is moved. -/
theorem bigCompS_operands : ∀ {σs : List (ResU Loc Val)} {b : ResU Loc Val},
    BigComp CellU.CompatS CellU.CompS σs (e.relRU b) → ∀ σ ∈ σs, ∃ σ₀, σ = e.relRU σ₀
  | [], _, _ => fun σ h => absurd h (by simp)
  | σ :: σs, b, h => by
      cases h with
      | cons hb hc =>
          obtain ⟨⟨σ₀, rfl⟩, ⟨τ₀, rfl⟩⟩ := e.compS_operands hc
          intro σ' hσ'
          rcases List.mem_cons.mp hσ' with rfl | hσ'
          · exact ⟨σ₀, rfl⟩
          · exact bigCompS_operands hb σ' hσ'

/-- A list of pairs whose every second component is moved is a moved list. -/
theorem relL_of_pieces : ∀ (π : List (Loc × ResU Loc Val)),
    (∀ q ∈ π, ∃ p₀, q.2 = e.relRU p₀) → ∃ π₀, π = e.relL π₀
  | [], _ => ⟨[], rfl⟩
  | (l, p) :: π, h => by
      obtain ⟨p₀, hp⟩ := h (l, p) (List.mem_cons_self ..)
      obtain ⟨π₀, rfl⟩ := relL_of_pieces π fun q hq => h q (List.mem_cons_of_mem _ hq)
      have hp' : p = e.relRU p₀ := hp
      subst hp'
      exact ⟨(l, p₀) :: π₀, rfl⟩

theorem relU_eq_ownOf {ψ : CellU Loc Val} {v : Val} :
    e.relU ψ = CellU.ownOf v ↔ ψ = CellU.ownOf v := by
  constructor
  · intro h; exact e.relU_injective (h.trans (relU_ownOf e v).symm)
  · intro h; rw [h]; rfl

theorem relRU_get_own {ρ : ResU Loc Val} {l : Loc} {v : Val} :
    (e.relRU ρ).get l = some (CellU.ownOf v) ↔ ρ.get l = some (CellU.ownOf v) := by
  rw [relRU_get]
  constructor
  · intro h
    obtain ⟨ψ, hψ, h'⟩ := Option.map_eq_some_iff.mp h
    rw [hψ, relU_eq_ownOf.mp h']
  · intro h; rw [h]; rfl

theorem relRU_get_relU {ρ : ResU Loc Val} {l : Loc} {ψ : CellU Loc Val} :
    (e.relRU ρ).get l = some (e.relU ψ) ↔ ρ.get l = some ψ := by
  rw [relRU_get]
  constructor
  · intro h
    obtain ⟨ψ', hψ', h'⟩ := Option.map_eq_some_iff.mp h
    rw [hψ', e.relU_injective h']
  · intro h; rw [h]; rfl

theorem relU_immOf_single (α : Life) (v : Val) (χ : ResU Loc Val)
    (h : χ.InStratum (LSet.singleton α).join) (h' : (e.relRU χ).InStratum (LSet.singleton (e α)).join) :
    e.relU (CellU.immOf (LSet.singleton α) v χ h) =
      CellU.immOf (LSet.singleton (e α)) v (e.relRU χ) h' := by
  rw [e.relU_immOf]
  exact CellU.immOf_congr (e.mapL_singleton α) rfl rfl _ _

theorem rebAt_iff (α : Life) (ρ ρ' : ResU Loc Val) (l : Loc) (p : ResU Loc Val) :
    ResU.RebAt (e α) (e.relRU ρ) (e.relRU ρ') l (e.relRU p) ↔ ResU.RebAt α ρ ρ' l p := by
  unfold ResU.RebAt
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · -- the piece is defined at `ℓ`
    constructor
    · rintro ⟨χ, hχ⟩
      obtain ⟨ψ, hψ, -⟩ := relRU_get_eq_some hχ
      exact ⟨ψ, hψ⟩
    · rintro ⟨ψ, hψ⟩; exact ⟨e.relU ψ, by rw [relRU_get, hψ]; rfl⟩
  · -- the `own` clause
    refine forall_congr' fun v => ?_
    rw [relRU_get_own]
    refine imp_congr_right fun _ => ?_
    rw [← relRU_del]
    constructor
    · rintro ⟨h, hh⟩
      have h₀ : (p.del l).InStratum (LSet.singleton α).join :=
        (e.inStratum_relRU _ _).mp h
      refine ⟨h₀, (relRU_get_relU (e := e)).mp ?_⟩
      rw [e.relU_immOf_single α v _ h₀ h]; exact hh
    · rintro ⟨h, hh⟩
      have h' : (e.relRU (p.del l)).InStratum (LSet.singleton (e α)).join :=
        (e.inStratum_relRU _ _).mpr h
      refine ⟨h', ?_⟩
      rw [← e.relU_immOf_single α v _ h h']
      exact (relRU_get_relU (e := e)).mpr hh
  · -- the `mut` clause
    constructor
    · intro hm b v χ hb P hw hρ
      have hρ' : (e.relRU ρ).get l = some (e.relU (CellU.mutOf b v χ hb P hw)) :=
        (relRU_get_relU (e := e)).mpr hρ
      rw [e.relU_mutOf] at hρ'
      obtain ⟨⟨h, hh⟩, hd⟩ := hm _ _ _ _ _ _ hρ'
      have h₀ : χ.InStratum (LSet.singleton α).join := (e.inStratum_relRU _ _).mp h
      refine ⟨⟨h₀, (relRU_get_relU (e := e)).mp ?_⟩, (dom_iff p _).mp hd⟩
      rw [e.relU_immOf_single α v χ h₀ h]; exact hh
    · intro hm b v χ hb P hw hρ
      obtain ⟨ψ, hψ, hψe⟩ := relRU_get_eq_some hρ
      rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s₀, u, τ, m, rfl⟩ | ⟨b₀, u, τ, m, Q, w, rfl⟩
      · exact absurd hψe (by intro hx; cases hx)
      · rw [e.relU_immOf] at hψe; exact absurd hψe (by intro hx; cases hx)
      · rw [e.relU_mutOf] at hψe
        have hbb : b = e b₀ := CellU.mutOf_at hψe
        subst hbb
        obtain ⟨hv, hτ, -⟩ := CellU.mutOf_inj hψe
        subst hv; subst hτ
        obtain ⟨⟨h₀, hh⟩, hd⟩ := hm b₀ v τ m Q w hψ
        have h' : (e.relRU τ).InStratum (LSet.singleton (e α)).join :=
          (e.inStratum_relRU _ _).mpr h₀
        refine ⟨⟨h', ?_⟩, (dom_iff p _).mpr hd⟩
        rw [← e.relU_immOf_single α v τ h₀ h']
        exact (relRU_get_relU (e := e)).mpr hh
  · -- the `imm` clause
    constructor
    · intro hm s v χ h hρ
      have hρ' : (e.relRU ρ).get l = some (e.relU (CellU.immOf s v χ h)) :=
        (relRU_get_relU (e := e)).mpr hρ
      rw [e.relU_immOf] at hρ'
      obtain ⟨⟨t, ht, hsub, hh⟩, hd⟩ := hm _ _ _ _ hρ'
      refine ⟨?_, (dom_iff p _).mp hd⟩
      obtain ⟨ψ, hψ, hψe⟩ := relRU_get_eq_some hh
      rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨t₀, u, τ, m, rfl⟩ | ⟨b₀, u, τ, m, Q, w, rfl⟩
      · exact absurd hψe (by intro hx; cases hx)
      · rw [e.relU_immOf] at hψe
        obtain ⟨ht', hv, hτ⟩ := CellU.immOf_inj hψe
        subst ht'; subst hv
        have hτ' := e.relRU_injective hτ
        subst hτ'
        refine ⟨t₀, m, fun x hx => ?_, hψ⟩
        obtain ⟨y, hy, hxy⟩ := hsub (e x) ⟨x, hx, rfl⟩
        rwa [← e.injective hxy]
      · rw [e.relU_mutOf] at hψe; exact absurd hψe (by intro hx; cases hx)
    · intro hm s v χ h hρ
      obtain ⟨ψ, hψ, hψe⟩ := relRU_get_eq_some hρ
      rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s₀, u, τ, m, rfl⟩ | ⟨b₀, u, τ, m, Q, w, rfl⟩
      · exact absurd hψe (by intro hx; cases hx)
      · rw [e.relU_immOf] at hψe
        obtain ⟨hs, hv, hτ⟩ := CellU.immOf_inj hψe
        subst hs; subst hv; subst hτ
        obtain ⟨⟨t, ht, hsub, hh⟩, hd⟩ := hm s₀ v τ m hψ
        refine ⟨⟨e.mapL t, (e.inStratum_relRU _ _).mpr ht, ?_, ?_⟩, (dom_iff p _).mpr hd⟩
        · rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hsub x hx, rfl⟩
        · have := relRU_get_relU (e := e) |>.mpr hh
          rw [e.relU_immOf] at this
          exact this
      · rw [e.relU_mutOf] at hψe; exact absurd hψe (by intro hx; cases hx)

theorem reb_iff (α : Life) (ρ ρ' : ResU Loc Val) :
    ResU.Reb (e α) (e.relRU ρ) (e.relRU ρ') ↔ ResU.Reb α ρ ρ' := by
  constructor
  · rintro ⟨hs, π, b, hdom, hbig, hle, hbody⟩
    obtain ⟨b₀, rfl⟩ := e.le_image hle
    obtain ⟨π₀, rfl⟩ := relL_of_pieces π fun q hq =>
      bigCompS_operands hbig q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
    refine ⟨(e.inStratum_relRU α ρ).mp hs, π₀, b₀, ?_, ?_, (e.resLe_iff _ _).mp hle,
      fun l p hp => ?_⟩
    · rw [relL_fst] at hdom; exact (dom_iff ρ' _).mp hdom
    · rw [relL_snd] at hbig; exact (bigComp_iff e.nat2S e.nat3S _ _).mp hbig
    · exact (rebAt_iff α ρ ρ' l p).mp
        (hbody l (e.relRU p) (List.mem_map.mpr ⟨(l, p), hp, rfl⟩))
  · rintro ⟨hs, π, b, hdom, hbig, hle, hbody⟩
    refine ⟨(e.inStratum_relRU α ρ).mpr hs, e.relL π, e.relRU b, ?_, ?_,
      (e.resLe_iff _ _).mpr hle, fun l p hp => ?_⟩
    · rw [relL_fst]; exact (dom_iff ρ' _).mpr hdom
    · rw [relL_snd]; exact (bigComp_iff e.nat2S e.nat3S _ _).mpr hbig
    · obtain ⟨⟨l', p₀⟩, hq, hq'⟩ := List.mem_map.mp hp
      simp only [Prod.mk.injEq] at hq'
      obtain ⟨rfl, rfl⟩ := hq'
      exact (rebAt_iff α ρ ρ' l' p₀).mpr (hbody l' p₀ hq)

/-- Every member of `reb_{eα}(e·ρ)` is moved. -/
theorem reb_image (α : Life) (ρ : ResU Loc Val) {σ : ResU Loc Val}
    (h : ResU.Reb (e α) (e.relRU ρ) σ) : ∃ ρ', σ = e.relRU ρ' := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := h
  obtain ⟨b₀, rfl⟩ := e.le_image hle
  have hpieces := fun q (hq : q ∈ π) =>
    bigCompS_operands hbig q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
  refine e.isImage_of_cells fun l χ hχ => ?_
  obtain ⟨q, hq, hql⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨χ, hχ⟩)
  obtain ⟨l', p⟩ := q
  simp only at hql
  subst hql
  obtain ⟨p₀, hp₀⟩ := hpieces _ hq
  simp only at hp₀
  subst hp₀
  obtain ⟨⟨ψp, hψp⟩, hown, hmut, himm⟩ := hbody l' (e.relRU p₀) hq
  -- the source has a cell at `ℓ`, since the piece is a factor of it
  obtain ⟨φ, hφ⟩ : ∃ φ, (e.relRU ρ).get l' = some φ := by
    obtain ⟨b', hb1, hb2⟩ := BigComp.leS_of_sublist
      (List.singleton_sublist.mpr (List.mem_map.mpr ⟨_, hq, rfl⟩)) hbig
    have hb1' := (BigComp.singleton_iff ResU.compLawsS).mp hb1
    subst hb1'
    obtain ⟨τ, hτ⟩ := hb2.trans hle
    rcases ResU.Comp.get hτ l' with ⟨e₁, -, -⟩ | ⟨ψ, -, -, e₃⟩ | ⟨ψ, e₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, e₃, -⟩
    · exact absurd (hψp.symm.trans e₁) (by simp)
    · exact ⟨ψ, e₃⟩
    · exact absurd (hψp.symm.trans e₁) (by simp)
    · exact ⟨ψ, e₃⟩
  obtain ⟨ψ, hψ, rfl⟩ := relRU_get_eq_some hφ
  rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s₀, u, τ, m, rfl⟩ | ⟨b₁, u, τ, m, Q, w, rfl⟩
  · obtain ⟨h, hh⟩ := hown u ((relRU_get_own (e := e)).mpr hψ)
    rw [hχ] at hh; cases hh
    have hd : (e.relRU p₀).del l' = e.relRU (p₀.del l') := (relRU_del p₀ l').symm
    have h₀ : (p₀.del l').InStratum (LSet.singleton α).join :=
      (e.inStratum_relRU _ _).mp (hd ▸ h)
    refine ⟨CellU.immOf (LSet.singleton α) u (p₀.del l') h₀, ?_⟩
    rw [e.relU_immOf_single α u _ h₀ ((e.inStratum_relRU _ _).mpr h₀)]
    exact CellU.immOf_congr rfl rfl hd _ _
  · have hφ' := hφ
    rw [e.relU_immOf] at hφ'
    obtain ⟨⟨t, ht, hsub, hh⟩, -⟩ := himm _ _ _ _ hφ'
    rw [hχ] at hh; cases hh
    obtain ⟨t₀, rfl⟩ := e.mapL_of_subset (t := t) fun x hx => by
      obtain ⟨y, -, hy⟩ := hsub x hx
      exact ⟨y, hy⟩
    exact ⟨CellU.immOf t₀ u τ ((e.inStratum_relRU _ _).mp ht), by rw [e.relU_immOf]⟩
  · have hφ' := hφ
    rw [e.relU_mutOf] at hφ'
    obtain ⟨⟨h, hh⟩, -⟩ := hmut _ _ _ _ _ _ hφ'
    rw [hχ] at hh; cases hh
    refine ⟨CellU.immOf (LSet.singleton α) u τ ((e.inStratum_relRU _ _).mp h), ?_⟩
    rw [e.relU_immOf_single]

theorem agree_reborrow (α : Life) {P' P : SPropU Loc Val} (hP : e.Agree P' P) :
    e.Agree (reborrow (e α) P') (reborrow α P) := by
  intro ρ
  constructor
  · rintro ⟨σ, hσ, hP'⟩
    obtain ⟨ρ', rfl⟩ := reb_image α ρ hσ
    exact ⟨ρ', (reb_iff α ρ ρ').mp hσ, (hP ρ').mp hP'⟩
  · rintro ⟨ρ', hρ', hPρ⟩
    exact ⟨e.relRU ρ', (reb_iff α ρ ρ').mpr hρ', (hP ρ').mpr hPρ⟩

end Emb

end Restrat
