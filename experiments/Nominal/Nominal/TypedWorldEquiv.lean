import Nominal.TypedWorld

/-!
# Nominal — the typed world and `wpTS` are carried by every order automorphism

`TWN_act`: a typed world moved by `π` — resource, records, tags — is a typed world, by induction
over `TW`'s constructors, each premise moved by its own invariance: `vShape` (`vShapeN_map`), the
lineage (`descN_act_iff`, `descRN_act_iff`, `linLocN_act_iff`, `frameLifeN_act_iff`), `reb_α`
(`rebN_act`), the strata (`stratumLeN_act_iff`). `wpTSN_equiv`: **Core's `wp` is carried by every
order automorphism**, so `vR_map` holds at Core's own `wp` (`vR_map_wpTS`).
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE RefPos MutPos VFree)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]

section Ops
variable (π : L ≃o L)

theorem relRU_del (ρ : ResU L) (l : Loc) : relRU π (ρ.del l) = (relRU π ρ).del l := by
  refine PMap.ext fun l' => ?_
  show ((if l' = l then none else ρ.get l').map (relU π)) =
    (if l' = l then none else (ρ.get l').map (relU π))
  split_ifs <;> rfl

theorem dom_relRU_iff {ρ : ResU L} {d : List Loc} : (relRU π ρ).Dom d ↔ ρ.Dom d := by
  unfold ResU.Dom
  refine and_congr_right fun _ => forall_congr' fun l => ?_
  rw [relRU_get]
  refine Iff.intro (fun h => ?_) (fun h => ?_) <;> constructor
  · intro hl
    obtain ⟨ψ', e⟩ := h.mp hl
    obtain ⟨ψ, hψ, -⟩ := Option.map_eq_some_iff.mp e
    exact ⟨ψ, hψ⟩
  · rintro ⟨ψ, hψ⟩
    exact h.mpr ⟨relU π ψ, by rw [hψ]; rfl⟩
  · intro hl
    obtain ⟨ψ, hψ⟩ := h.mp hl
    exact ⟨relU π ψ, by rw [hψ]; rfl⟩
  · rintro ⟨ψ', e⟩
    obtain ⟨ψ, hψ, -⟩ := Option.map_eq_some_iff.mp e
    exact h.mpr ⟨ψ, hψ⟩

theorem le_relRU_iff {a b : ResU L} : ResU.Le (relRU π a) (relRU π b) ↔ ResU.Le a b := by
  constructor
  · rintro ⟨τ', h⟩
    obtain ⟨τ, rfl⟩ := relRU_surjective π τ'
    exact ⟨τ, (compS_relRU_iff π).mp h⟩
  · rintro ⟨τ, h⟩
    exact ⟨relRU π τ, compS_relRU h⟩

theorem relRU_restrictDom (ρ σ : ResU L) :
    relRU π (ρ.restrictDom σ) = (relRU π ρ).restrictDom (relRU π σ) := by
  refine PMap.ext fun l => ?_
  show ((if (σ.get l).isSome then ρ.get l else none).map (relU π)) =
    (if ((σ.get l).map (relU π)).isSome then (ρ.get l).map (relU π) else none)
  rw [Option.isSome_map]
  split_ifs <;> rfl

theorem relRU_exclPart (ρ : ResU L) : relRU π ρ.exclPart = (relRU π ρ).exclPart := by
  refine PMap.ext fun l => ?_
  show ((ρ.get l).bind fun ψ => if ψ.kind = .imm then none else some ψ).map (relU π) =
    ((ρ.get l).map (relU π)).bind fun ψ => if ψ.kind = .imm then none else some ψ
  cases ρ.get l with
  | none => rfl
  | some ψ =>
      simp only [Option.bind_some, Option.map_some, kind_relU]
      split_ifs <;> rfl

theorem isImm_relU_iff {ψ : CellU L} {s : Finset L} {v : Val} {χ : ResU L} :
    (relU π ψ).IsImm (mapS π s) v (relRU π χ) ↔ ψ.IsImm s v χ := by
  refine ⟨fun h => ?_, isImm_relU π⟩
  have := isImm_relU π.symm h
  rwa [relU_symm_relU, mapS_symm_mapS, relRU_symm_relRU] at this

theorem lsOf_relU (ψ : CellU L) : (relU π ψ).lsOf = ψ.lsOf.map (mapS π) := by
  unfold CellU.lsOf
  rw [kind_relU, lts_relU]
  split_ifs <;> rfl

end Ops

/-! ### `reb_α` -/

section Reb
variable (π : L ≃o L)

theorem rebAtN_act {α : L} {ρ ρ' : ResU L} {l : Loc} {p : ResU L} (h : ResU.RebAt α ρ ρ' l p) :
    ResU.RebAt (π α) (relRU π ρ) (relRU π ρ') l (relRU π p) := by
  obtain ⟨⟨ψ₀, h₀⟩, hown, hmut, himm⟩ := h
  refine ⟨⟨relU π ψ₀, by rw [relRU_get, h₀]; rfl⟩, ?_, ?_, ?_⟩
  · intro v e
    obtain ⟨ψ', hψ', hI⟩ := hown v ((relRU_get_own_iff π).mp e)
    refine ⟨relU π ψ', by rw [relRU_get, hψ']; rfl, ?_⟩
    rw [← relRU_del]
    exact isImm_relU π hI
  · rintro v χ' ⟨ψ'', e, hk, he, hw⟩
    rw [relRU_get] at e
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
    have hχ : χ' = relRU π ψ.wit := by rw [← hw, wit_relU]
    subst hχ
    obtain ⟨⟨ψ', hψ', hI⟩, hd⟩ := hmut v ψ.wit
      ⟨ψ, hψ, by rwa [kind_relU] at hk, by rwa [erase_relU] at he, rfl⟩
    exact ⟨⟨relU π ψ', by rw [relRU_get, hψ']; rfl, isImm_relU π hI⟩, (dom_relRU_iff π).mpr hd⟩
  · rintro s' v χ' ⟨ψ'', e, hI'⟩
    rw [relRU_get] at e
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
    have hs : s' = mapS π (mapS π.symm s') := by
      have := mapS_symm_mapS π.symm s'
      rw [OrderIso.symm_symm] at this
      exact this.symm
    have hχ : χ' = relRU π (relRU π.symm χ') := (relRU_relRU_symm π χ').symm
    rw [hs, hχ] at hI'
    obtain ⟨⟨t, ψ', ht, hts, hψ', hI⟩, hd⟩ :=
      himm (mapS π.symm s') v (relRU π.symm χ') ⟨ψ, hψ, (isImm_relU_iff π).mp hI'⟩
    refine ⟨⟨mapS π t, relU π ψ', mapS_nonempty.mpr ht, ?_, by rw [relRU_get, hψ']; rfl, ?_⟩,
      (dom_relRU_iff π).mpr hd⟩
    · intro y hy
      obtain ⟨y₀, hy₀, rfl⟩ := mem_mapS.mp hy
      have := (mem_mapS_apply (π := π)).mpr (hts hy₀)
      rwa [← hs] at this
    · rw [hχ]
      exact isImm_relU π hI

theorem rebN_act {α : L} {ρ ρ' : ResU L} (h : ResU.Reb α ρ ρ') :
    ResU.Reb (π α) (relRU π ρ) (relRU π ρ') := by
  obtain ⟨hst, ps, b, hd, hb, hle, hat⟩ := h
  refine ⟨(inStratum_relRU_singleton π α ρ).mpr hst, mapW π ps, relRU π b, ?_, ?_,
    (le_relRU_iff π).mpr hle, ?_⟩
  · rw [mapW_fst]; exact (dom_relRU_iff π).mpr hd
  · rw [mapW_snd]; exact bigComp_relRU (natCompatS π) (natCompS π) hb
  · intro l p' hp'
    obtain ⟨⟨l₀, p⟩, hp, e⟩ := List.mem_map.mp hp'
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact rebAtN_act π (hat l₀ p hp)

end Reb

/-! ### `vShape` -/

section Shape
variable (π : L ≃o L)

theorem vShapeN_map : ∀ (A : VTy) (δ : LSubN L) (v : Val) (ρ : ResU L),
    vShapeN A (δ.map π) v (relRU π ρ) ↔ vShapeN A δ v ρ
  | .unit, _, v, ρ => pureN_relRU_iff π (v = .unit) ρ
  | .tensor A B, δ, _, ρ =>
      exN_relRU_iff π (fun v₁ σ => exN_relRU_iff π (fun v₂ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (sepN_relRU_iff π (vShapeN_map A δ v₁) (vShapeN_map B δ v₂)) σ') σ) ρ
  | .thunk _, _, _, _ => Iff.rfl
  | .box a A, δ, v, ρ =>
      atLifeN_map π δ a (fun α σ => boxE_relRU_iff π α (vShapeN_map A δ v) σ) ρ
  | .ref A, δ, _, ρ =>
      exN_relRU_iff π (fun ℓ σ => exN_relRU_iff π (fun v' σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (sepN_relRU_iff π (ptoOwnN_relRU_iff π ℓ v') (vShapeN_map A δ v')) σ') σ) ρ
  | .imm a A, δ, _, ρ =>
      atLifeN_map π δ a (fun α σ => exN_relRU_iff π (fun ℓ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (ptoImmN_relRU_iff π ℓ α (vShapeN_map A δ)) σ') σ) ρ
  | .mut a A, δ, _, ρ =>
      atLifeN_map π δ a (fun α σ => exN_relRU_iff π (fun ℓ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _) (fun τ => by
          constructor
          · rintro ⟨P, hP, hsh⟩
            refine ⟨fun u σ'' => P u (relRU π σ''), (ptoMutN_relRU_iff π ℓ α
              (P' := P) (fun u σ'' => Iff.rfl) τ).mp hP, fun u σ'' h => ?_⟩
            exact (vShapeN_map A δ u σ'').mp (hsh u _ h)
          · rintro ⟨P, hP, hsh⟩
            refine ⟨fun u σ'' => P u (relRU π.symm σ''), (ptoMutN_relRU_iff π ℓ α
              (P := P) (P' := fun u σ'' => P u (relRU π.symm σ''))
              (fun u σ'' => by rw [relRU_symm_relRU]) τ).mpr hP, fun u σ'' h => ?_⟩
            rw [← relRU_relRU_symm π σ'']
            exact (vShapeN_map A δ u _).mpr (hsh u _ h)) σ') σ) ρ
  | .zero, _, _, _ | .sum _ _, _, _, _ | .bang _, _, _, _ | .unk, _, _, _ | .tvar _, _, _, _
  | .mu _, _, _, _ | .int _, _, _, _ | .fam _, _, _, _ | .opq _, _, _, _ => Iff.rfl

theorem admWfN_map {T : VTy} {δ : LSubN L} : AdmWfN T (δ.map π) ↔ AdmWfN T δ := by
  unfold AdmWfN
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  rw [LSubN.find?_map]
  constructor
  · rintro ⟨α', h⟩
    obtain ⟨α, hα, -⟩ := Option.map_eq_some_iff.mp h
    exact ⟨α, hα⟩
  · rintro ⟨α, hα⟩
    exact ⟨π α, by rw [hα]; rfl⟩

end Shape

/-! ### The lineage -/

section Lineage
variable (π : L ≃o L)

theorem gPosN_act_iff {R : ResU L} {T : VTy} {v : Val} {m : Loc} {S : VTy} :
    GPosN (relRU π R) T v m S ↔ GPosN R T v m S := by
  constructor
  · intro h
    induction h with
    | here hm => exact .here hm
    | step hr he _ ih => exact .step hr ((relRU_get_own_iff π).mp he) ih
  · intro h
    induction h with
    | here hm => exact .here hm
    | step hr he _ ih => exact .step hr ((relRU_get_own_iff π).mpr he) ih

theorem LSubN.map_injective : Function.Injective (LSubN.map (L := L) (L' := L) π) :=
  fun a b h => by rw [← LSubN.map_symm_map π a, h, LSubN.map_symm_map]

theorem subRecN_act_iff {r d : FrameRecN L} :
    SubRecN (r.act π) (d.act π) ↔ SubRecN r d := by
  unfold SubRecN
  simp only [FrameRecN.act]
  refine and_congr ((LSubN.map_injective π).eq_iff) (and_congr (gPosN_act_iff π) ?_)
  constructor
  · rintro ⟨ζ', e, hk, he, hw⟩
    rw [relRU_get] at e
    obtain ⟨ζ, hζ, rfl⟩ := Option.map_eq_some_iff.mp e
    refine ⟨ζ, hζ, by rwa [kind_relU] at hk, by rwa [erase_relU] at he, ?_⟩
    rw [wit_relU] at hw
    exact relRU_injective π hw
  · rintro ⟨ζ, hζ, hk, he, hw⟩
    exact ⟨relU π ζ, by rw [relRU_get, hζ]; rfl, by rw [kind_relU, hk], by rw [erase_relU, he],
      by rw [wit_relU, hw]⟩

theorem linPathN_act {r e : FrameRecN L} {p : List Loc} (h : LinPathN r p e) :
    LinPathN (r.act π) p (e.act π) := by
  induction h with
  | nil r => exact .nil _
  | @cons r d e p hs _ ih => exact .cons (d := d.act π) ((subRecN_act_iff π).mpr hs) ih

theorem linPathN_act_iff {r e : FrameRecN L} {p : List Loc} :
    LinPathN (r.act π) p (e.act π) ↔ LinPathN r p e := by
  refine ⟨fun h => ?_, linPathN_act π⟩
  have := linPathN_act π.symm h
  rwa [FrameRecN.act_symm_act, FrameRecN.act_symm_act] at this

theorem FrameRecN.act_surjective : Function.Surjective (FrameRecN.act (L := L) π) :=
  fun r => ⟨r.act π.symm, FrameRecN.act_act_symm π r⟩

theorem descRN_act_iff {r d : FrameRecN L} : DescRN (r.act π) (d.act π) ↔ DescRN r d :=
  exists_congr fun _ => linPathN_act_iff π

theorem descN_act_iff {r d : FrameRecN L} : DescN (r.act π) (d.act π) ↔ DescN r d :=
  exists_congr fun _ => and_congr_right fun _ => linPathN_act_iff π

theorem linLocN_act_iff {p : FrameRecN L} {m : Loc} : LinLocN (p.act π) m ↔ LinLocN p m := by
  unfold LinLocN
  constructor
  · rintro ⟨d', hd', ζ', e, hk⟩
    obtain ⟨d, rfl⟩ := FrameRecN.act_surjective π d'
    change (relRU π d.R).get m = some ζ' at e
    rw [relRU_get] at e
    obtain ⟨ζ, hζ, rfl⟩ := Option.map_eq_some_iff.mp e
    exact ⟨d, (descRN_act_iff π).mp hd', ζ, hζ, by rwa [kind_relU] at hk⟩
  · rintro ⟨d, hd, ζ, hζ, hk⟩
    exact ⟨d.act π, (descRN_act_iff π).mpr hd, relU π ζ,
      by show (relRU π d.R).get m = _; rw [relRU_get, hζ]; rfl, by rw [kind_relU]; exact hk⟩

theorem agW_relRU_iff {W a : ResU L} : AgW (relRU π W) (relRU π a) ↔ AgW W a := by
  refine ⟨fun h => ?_, agW_relRU⟩
  have := agW_relRU (π := π.symm) h
  rwa [relRU_symm_relRU, relRU_symm_relRU] at this

theorem frameLifeN_act_iff {W : ResU L} {p : FrameRecN L} {α : L} :
    FrameLifeN (relRU π W) (p.act π) (π α) ↔ FrameLifeN W p α := by
  unfold FrameLifeN
  refine and_congr ?_ ?_
  · constructor
    · intro h a ha ζ t e hl y hy
      have := h (relRU π a) ((agW_relRU_iff π).mpr ha) (relU π ζ) (mapS π t)
        (by show (relRU π a).get p.le = _; rw [relRU_get, e]; rfl)
        (by rw [lsOf_relU, hl]; rfl) (π y) (mem_mapS_apply.mpr hy)
      exact π.injective this
    · intro h a' ha' ζ' t' e hl y' hy'
      obtain ⟨a, rfl⟩ := relRU_surjective π a'
      change (relRU π a).get p.le = some ζ' at e
      rw [relRU_get] at e
      obtain ⟨ζ, hζ, rfl⟩ := Option.map_eq_some_iff.mp e
      rw [lsOf_relU] at hl
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hl
      obtain ⟨y, hy, rfl⟩ := mem_mapS.mp hy'
      rw [h a ((agW_relRU_iff π).mp ha') ζ t hζ ht y hy]
  · constructor
    · intro h a ha m hm ψ s e hl x hx
      have := h (relRU π a) ((agW_relRU_iff π).mpr ha) m ((linLocN_act_iff π).mpr hm)
        (relU π ψ) (mapS π s) (by rw [relRU_get, e]; rfl) (by rw [lsOf_relU, hl]; rfl) (π x)
        (mem_mapS_apply.mpr hx)
      exact π.le_iff_le.mp this
    · intro h a' ha' m hm ψ' s' e hl x' hx'
      obtain ⟨a, rfl⟩ := relRU_surjective π a'
      rw [relRU_get] at e
      obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
      rw [lsOf_relU] at hl
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp hl
      obtain ⟨x, hx, rfl⟩ := mem_mapS.mp hx'
      exact π.le_iff_le.mpr (h a ((agW_relRU_iff π).mp ha') m ((linLocN_act_iff π).mp hm) ψ s hψ
        hs x hx)

theorem stratumLeN_act_iff {W : ResU L} {β : L} :
    StratumLeN (relRU π W) (π β) ↔ StratumLeN W β := by
  unfold StratumLeN
  rw [π.surjective.forall]
  refine forall_congr' fun β' => ?_
  rw [π.lt_iff_lt, inStratum_relRU_singleton]

theorem mem_map_act {rs : List (FrameRecN L)} {r : FrameRecN L} :
    r.act π ∈ rs.map (FrameRecN.act π) ↔ r ∈ rs := by
  rw [List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => FrameRecN.act_injective π e ▸ hy, fun h => ⟨r, h, rfl⟩⟩

theorem taggedN_act_iff {W : ResU L} {ps : List (FrameRecN L)} {ls : List (SRecN L)} :
    TaggedN (relRU π W) (ps.map (FrameRecN.act π)) (actL π ls) ↔ TaggedN W ps ls := by
  unfold TaggedN
  constructor
  · intro h x hx
    obtain ⟨p', hp', hd, hf⟩ := h (x.act π) ((mem_actL π).mpr hx)
    obtain ⟨p, rfl⟩ := FrameRecN.act_surjective π p'
    exact ⟨p, (mem_map_act π).mp hp', (descRN_act_iff π).mp hd, (frameLifeN_act_iff π).mp hf⟩
  · intro h x' hx'
    obtain ⟨x, rfl⟩ := SRecN.act_surjective π x'
    obtain ⟨p, hp, hd, hf⟩ := h x ((mem_actL π).mp hx')
    exact ⟨p.act π, (mem_map_act π).mpr hp, (descRN_act_iff π).mpr hd,
      (frameLifeN_act_iff π).mpr hf⟩

end Lineage

/-! ### The typed world -/

section TW
variable (π : L ≃o L)

theorem compS_single_own (l : Loc) (v : Val) {Z W : ResU L}
    (h : ResU.CompS (ResU.single l (CellU.own v)) Z W) :
    ResU.CompS (ResU.single l (CellU.own v)) (relRU π Z) (relRU π W) := by
  have := compS_relRU (π := π) h
  rwa [relRU_single, relU_own] at this

theorem compS_into_own (l : Loc) (v : Val) {Z W : ResU L}
    (h : ResU.CompS Z (ResU.single l (CellU.own v)) W) :
    ResU.CompS (relRU π Z) (ResU.single l (CellU.own v)) (relRU π W) := by
  have := compS_relRU (π := π) h
  rwa [relRU_single, relU_own] at this

/-- **A typed world moved by `π` is a typed world.** -/
theorem TWN_act {W : ResU L} {ps rs : List (FrameRecN L)} (h : TWN W ps rs) :
    TWN (relRU π W) (ps.map (FrameRecN.act π)) (rs.map (FrameRecN.act π)) := by
  induction h with
  | empty => rw [relRU_empty]; exact .empty
  | alloc _ hlow hμ hc hv ih =>
      exact .alloc ih (lower_relRU hlow) hμ (compS_into_own π _ _ hc) (valid_relRU hv)
  | @immFrame W X Z R W' ps rs ds l v α T δ hR _ hadm hc₁ hc₂ hsh hc₃ hv hds ih =>
      have hR' : (relRU π R).InStratum {π α} := (inStratum_relRU_singleton π α R).mpr hR
      have hc₃' := compS_relRU (π := π) hc₃
      rw [relRU_single, relU_immOf] at hc₃'
      have := TWN.immFrame (W := relRU π W) (X := relRU π X) (Z := relRU π Z) (R := relRU π R)
        (W' := relRU π W') (ps := ps.map (FrameRecN.act π)) (rs := rs.map (FrameRecN.act π))
        (ds := ds.map (FrameRecN.act π)) (l := l) (v := v) (α := π α) T (δ.map π) hR' ih
        ((admWfN_map π).mpr hadm) (compS_single_own π l v hc₁) (compS_relRU hc₂)
        ((vShapeN_map π T δ v R).mpr hsh) hc₃' (valid_relRU hv) (fun d' => by
          obtain ⟨d, rfl⟩ := FrameRecN.act_surjective π d'
          rw [mem_map_act]
          exact (hds d).trans (descN_act_iff π (r := ⟨l, v, R, T, δ⟩)).symm)
      rw [List.map_cons, List.map_cons, List.map_append]
      exact this
  | @reb W W' c ps rs r le s β x _ hr hcell hfree hreb hsh hsl hc hv ih =>
      obtain ⟨ψ, hψ, hI⟩ := hcell
      refine .reb (r.act π) (le := le) (s := mapS π s) (β := π β) x ih ((mem_map_act π).mpr hr)
        ⟨relU π ψ, by rw [relRU_get, hψ]; rfl, isImm_relU π hI⟩ hfree (rebN_act π hreb) ?_
        ((stratumLeN_act_iff π).mpr hsl) (compS_relRU hc) (valid_relRU hv)
      show vShapeN (r.T.immReborrow (.var x)) ((r.δ.map π).extend x (π β)) r.v (relRU π c)
      rw [← LSubN.map_extend]
      exact (vShapeN_map π _ _ _ _).mpr hsh
  | @rebDeep W W' c ps rs r p l₀ S₀ u₀ s w₀ β x _ hr hch hcell hfree hreb hsh hst hc hv ih =>
      obtain ⟨ψ, hψ, hI⟩ := hcell
      refine .rebDeep (r.act π) (p := p) (l₀ := l₀) (S₀ := S₀) (u₀ := u₀) (s := mapS π s)
        (w₀ := relRU π w₀) (β := π β) x ih ((mem_map_act π).mpr hr)
        ((chainN_act_iff π).mpr hch) ⟨relU π ψ, by rw [relRU_get, hψ]; rfl, isImm_relU π hI⟩
        hfree (rebN_act π hreb) ?_ ((inStratum_relRU_singleton π β W).mpr hst)
        (compS_relRU hc) (valid_relRU hv)
      show vShapeN (S₀.immReborrow (.var x)) ((r.δ.map π).extend x (π β)) u₀ (relRU π c)
      rw [← LSubN.map_extend]
      exact (vShapeN_map π _ _ _ _).mpr hsh
  | mutFold _ hc₁ hc₂ hcell hv ih =>
      obtain ⟨ψ, hk, he, hw, hc₃⟩ := hcell
      refine .mutFold ih (compS_single_own π _ _ hc₁) (compS_relRU hc₂)
        ⟨relU π ψ, by rw [kind_relU, hk], by rw [erase_relU, he], by rw [wit_relU, hw], ?_⟩
        (valid_relRU hv)
      have := compS_relRU (π := π) hc₃
      rwa [relRU_single] at this
  | mutUnfold _ hcell hc₁ hc₂ hv ih =>
      obtain ⟨ψ, hk, he, hw, hc₃⟩ := hcell
      refine .mutUnfold ih
        ⟨relU π ψ, by rw [kind_relU, hk], by rw [erase_relU, he], by rw [wit_relU, hw], ?_⟩
        (compS_single_own π _ _ hc₁) (compS_relRU hc₂) (valid_relRU hv)
      have := compS_relRU (π := π) hc₃
      rwa [relRU_single] at this
  | free _ hc hv ih => exact .free ih (compS_single_own π _ _ hc) (valid_relRU hv)
  | store _ hc₁ hc₂ hv ih =>
      exact .store ih (compS_single_own π _ _ hc₁) (compS_single_own π _ _ hc₂) (valid_relRU hv)
  | @immEnd W Y X' W' ps rs ps' rs' r s _ hr hcell hc₁ hc₂ hv hps hrs ih =>
      obtain ⟨ψ, hI, hc₀⟩ := hcell
      refine .immEnd (r.act π) (s := mapS π s) ih ((mem_map_act π).mpr hr)
        ⟨relU π ψ, isImm_relU π hI, ?_⟩ (compS_single_own π _ _ hc₁) (compS_relRU hc₂)
        (valid_relRU hv) ?_ ?_
      · have := compS_relRU (π := π) hc₀
        rwa [relRU_single] at this
      · intro r''
        obtain ⟨r', rfl⟩ := FrameRecN.act_surjective π r''
        rw [mem_map_act, mem_map_act, hps r']
        exact and_congr_right fun _ => (FrameRecN.act_injective π).ne_iff.symm
      · intro d''
        obtain ⟨d, rfl⟩ := FrameRecN.act_surjective π d''
        rw [mem_map_act, hrs d]
        constructor
        · rintro ⟨p, hp, hd⟩
          exact ⟨p.act π, (mem_map_act π).mpr hp, (descRN_act_iff π).mpr hd⟩
        · rintro ⟨p', hp', hd⟩
          obtain ⟨p, rfl⟩ := FrameRecN.act_surjective π p'
          exact ⟨p, (mem_map_act π).mp hp', (descRN_act_iff π).mp hd⟩
  | @rebEnd W W' c ps rs r le s β _ hr hcell hreb hc hst ih =>
      obtain ⟨ψ, hψ, hI⟩ := hcell
      refine .rebEnd (r.act π) (le := le) (s := mapS π s) (β := π β) ih ((mem_map_act π).mpr hr)
        ⟨relU π ψ, by rw [relRU_get, hψ]; rfl, isImm_relU π hI⟩ (rebN_act π hreb) ?_
        ((inStratum_relRU_singleton π β W').mpr hst)
      have := compS_relRU (π := π) hc
      rwa [relRU_restrictDom, relRU_exclPart] at this
  | @rebEndDeep W W' c ps rs r p l₀ S₀ u₀ s w₀ β _ hr hch hcell hreb hc hst ih =>
      obtain ⟨ψ, hψ, hI⟩ := hcell
      refine .rebEndDeep (r.act π) (p := p) (l₀ := l₀) (S₀ := S₀) (u₀ := u₀) (s := mapS π s)
        (w₀ := relRU π w₀) (β := π β) ih ((mem_map_act π).mpr hr) ((chainN_act_iff π).mpr hch)
        ⟨relU π ψ, by rw [relRU_get, hψ]; rfl, isImm_relU π hI⟩ (rebN_act π hreb) ?_
        ((inStratum_relRU_singleton π β W').mpr hst)
      have := compS_relRU (π := π) hc
      rwa [relRU_restrictDom, relRU_exclPart] at this

theorem map_act_symm (rs : List (FrameRecN L)) :
    (rs.map (FrameRecN.act π)).map (FrameRecN.act π.symm) = rs := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id rs]
  exact List.map_congr_left fun r _ => FrameRecN.act_symm_act π r

theorem TWN_act_iff {W : ResU L} {ps rs : List (FrameRecN L)} :
    TWN (relRU π W) (ps.map (FrameRecN.act π)) (rs.map (FrameRecN.act π)) ↔ TWN W ps rs := by
  refine ⟨fun h => ?_, TWN_act π⟩
  have := TWN_act π.symm h
  rwa [relRU_symm_relRU, map_act_symm, map_act_symm] at this

end TW

/-! ### `wpTS` -/

section WpTS
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
variable (π : L ≃o L)

theorem wpTSN_act {ls : List (SRecN L)} {e : Expr} {Q Q' : List (SRecN L) → Val → WPropN L}
    (hQ : ∀ ls'' v σ, Q' (actL π ls'') v (relRU π σ) ↔ Q ls'' v σ) {ρ : ResU L}
    (h : wpTSN (ℍ := ℍ) ls e Q ρ) : wpTSN (ℍ := ℍ) (actL π ls) e Q' (relRU π ρ) := by
  intro ρf' fρ' ps' hf' hc' hT' htg' A k
  obtain ⟨ρf, rfl⟩ := relRU_surjective π ρf'
  obtain ⟨fρ, rfl⟩ := relRU_surjective π fρ'
  obtain ⟨ps, rfl⟩ : ∃ ps, ps.map (FrameRecN.act π) = ps' :=
    ⟨ps'.map (FrameRecN.act π.symm), by
      have := map_act_symm π.symm ps'
      rwa [OrderIso.symm_symm] at this⟩
  rw [rsOfN_actL] at hT'
  obtain ⟨ρ', ρp, fρ'', fρ'p, πr, v, μ, μ', ps'', ls'', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅⟩ :=
    h ρf fρ ps ((hash_relRU_iff π).mp hf') ((compS_relRU_iff π).mp hc') ((TWN_act_iff π).mp hT')
      ((taggedN_act_iff π).mp htg') A k
  refine ⟨relRU π ρ', relRU π ρp, relRU π fρ'', relRU π fρ'p, relRU π πr, v, μ, μ',
    ps''.map (FrameRecN.act π), actL π ls'', hash_relRU h₁, compS_relRU h₂, hash_relRU h₃,
    lower_relRU h₄, compS_relRU h₅, lower_relRU h₆, h₇, compS_relRU h₈,
    (updV_relRU_iff π).mpr h₉, noOwn_relRU h₁₀, ?_, (taggedN_act_iff π).mpr h₁₂, ?_, ?_,
    (hQ ls'' v ρ').mpr h₁₅⟩
  · rw [rsOfN_actL]; exact TWN_act π h₁₁
  · intro p'
    obtain ⟨p, rfl⟩ := FrameRecN.act_surjective π p'
    rw [mem_map_act, mem_map_act]
    exact h₁₃ p
  · intro x'
    obtain ⟨x, rfl⟩ := SRecN.act_surjective π x'
    rw [mem_actL, mem_actL]
    exact h₁₄ x

/-- **Core's `wp` is carried by every order automorphism.** -/
theorem wpTSN_equiv : WpEquiv π (wpTSN (L := L) (ℍ := ℍ)) := by
  intro ls e Q Q' hQ ρ
  refine ⟨fun h => ?_, wpTSN_act π hQ⟩
  have hQ' : ∀ ls'' v σ, Q (actL π.symm ls'') v (relRU π.symm σ) ↔ Q' ls'' v σ := by
    intro ls'' v σ
    rw [← hQ, actL_actL_symm, relRU_relRU_symm]
  have := wpTSN_act π.symm hQ' h
  rwa [actL_symm_actL, relRU_symm_relRU] at this

/-- **Core's relation at its own `wp` is equivariant under every order automorphism.** -/
theorem vR_map_wpTS (b : Bool) (A : VTy) (ls : List (SRecN L)) (δ : LSubN L) (v : Val)
    (ρ : ResU L) :
    vR (wpTSN (ℍ := ℍ)) b A (actL π ls) (δ.map π) v (relRU π ρ) ↔
      vR (wpTSN (ℍ := ℍ)) b A ls δ v ρ :=
  vR_map π _ (wpTSN_equiv π) b A ls δ v ρ

theorem cR_map_wpTS (C : CTy) (ls : List (SRecN L)) (δ : LSubN L) (e : Expr) (ρ : ResU L) :
    cR (wpTSN (ℍ := ℍ)) C (actL π ls) (δ.map π) e (relRU π ρ) ↔
      cR (wpTSN (ℍ := ℍ)) C ls δ e ρ :=
  cR_map π _ (wpTSN_equiv π) C ls δ e ρ

end WpTS

end Nominal

end
