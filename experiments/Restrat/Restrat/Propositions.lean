import Restrat.Composition
import Support.Model.Singletons
import Support.Model.Propositions

/-!
# Restrat — naturality of the propositions of [TR] p. 6

The statement shape is `Agree P′ P ≜ ∀ρ. P′(e·ρ) ↔ P(ρ)`: `P′` read at moved resources is `P`.
`Supp P′` says `P′` holds only at moved resources.  The image `img P` (`Restrat.Composition`)
is the proposition that agrees with `P` and is supported.

* `⌜p⌝`, `emp`, `⊤`, `⊥`, `∧`, `∨`, `⇒`, `∀`, `∃`, `!`, `ℓ ↦ v` agree with themselves.
* `⋆` preserves agreement (`agree_sep`): every split of a moved resource is a split into moved
  resources (`compS_operands`), because `●` only unions lifetime sets and a subset of an image is
  an image (`mapL_of_subset`).
* `─⋆` preserves agreement when the argument is supported (`agree_wand`).  The `Supp`
  hypothesis is where the induction stops at the type interpretation: `𝒱⟦T⟧_{e∘δ}` holds at
  resources outside the image (`Restrat.MutCounterexample`).
* `[α]` moves to `[eα]` (`agree_box`).
* `ℓ ↦ Imm α P̂` moves to `ℓ ↦ Imm (eα) P̂′` at any agreeing `P̂′` (`agree_ptoImm`); `ℓ ↦ Mut α P̂`
  moves to `ℓ ↦ Mut (eα) (e·P̂)` with the image (`agree_ptoMut`), and only with it.
* `И P̂`: `И P̂′ (e·ρ) ⇒ И P̂ (ρ)` at every re-stratification (`fresh_bwd`); the converse needs the
  image to be cofinal (`Cofinal`, which every shift is: `shift_cofinal`), and then holds
  (`fresh_fwd`).
-/

noncomputable section

namespace Restrat
open BoCa.Fig16 BoCa.Fig16.BoLo

namespace Emb
variable {c : Life} (e : Emb c) {Loc Val : Type}

/-- `P′` read at moved resources is `P`. -/
def Agree (P' P : SPropU Loc Val) : Prop := ∀ ρ, P' (e.relRU ρ) ↔ P ρ

/-- `P′` holds only at moved resources. -/
def Supp (P' : SPropU Loc Val) : Prop := ∀ σ, P' σ → ∃ ρ, σ = e.relRU ρ

theorem agree_img (P : SPropU Loc Val) : e.Agree (e.img P) P := e.img_relRU P

theorem supp_img (P : SPropU Loc Val) : e.Supp (e.img P) := by
  rintro σ ⟨ρ, rfl, -⟩; exact ⟨ρ, rfl⟩

/-! ### Subsets of images -/

/-- A lifetime set every member of which is moved is a moved lifetime set. -/
theorem mapL_of_subset {t : LSet} (h : ∀ x, t.mem x → ∃ y, e y = x) : ∃ t₀, t = e.mapL t₀ := by
  classical
  obtain ⟨j₀, hj⟩ := h t.join t.join_mem
  obtain ⟨m₀, hm⟩ := h t.meet t.meet_mem
  let t₀ : LSet :=
    { mem := fun x => t.mem (e x)
      join := j₀
      meet := m₀
      join_mem := by show t.mem (e j₀); rw [hj]; exact t.join_mem
      meet_mem := by show t.mem (e m₀); rw [hm]; exact t.meet_mem
      join_greatest := fun x hx => e.le_iff.mp (by rw [hj]; exact t.join_greatest _ hx)
      meet_least := fun x hx => e.le_iff.mp (by rw [hm]; exact t.meet_least _ hx) }
  refine ⟨t₀, lset_ext (fun y => ?_) hj.symm hm.symm⟩
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := h y hy
    exact ⟨x, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact hx

/-- Each operand of `●` with a moved composite is moved. -/
theorem compS_cell_left {χ₁ χ₂ : CellU Loc Val} {ψ : CellU Loc Val}
    (h : CellU.CompS χ₁ χ₂ (e.relU ψ)) : ∃ ψ₁, χ₁ = e.relU ψ₁ := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, hψ⟩ := h
  rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨b, u, τ, m, Q, w, rfl⟩
  · exact absurd hψ (CellU.ownOf_ne_immOf)
  · rw [e.relU_immOf] at hψ
    obtain ⟨hu, hv, hρ⟩ := CellU.immOf_inj hψ
    obtain ⟨t₁, rfl⟩ := e.mapL_of_subset (t := s₁) fun x hx => by
      have : (s₁ ∪ s₂).mem x := Or.inl hx
      rw [← hu] at this
      obtain ⟨y, -, hy⟩ := this
      exact ⟨y, hy⟩
    rw [← hρ] at h₁
    refine ⟨CellU.immOf t₁ u τ ((e.inStratum_relRU _ _).mp h₁), ?_⟩
    rw [e.relU_immOf]
    exact CellU.immOf_congr rfl hv.symm hρ.symm _ _
  · rw [e.relU_mutOf] at hψ
    exact absurd hψ.symm (CellU.immOf_ne_mutOf)

theorem compS_operands {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ (e.relRU ρ)) :
    (∃ ρ₁₀, ρ₁ = e.relRU ρ₁₀) ∧ (∃ ρ₂₀, ρ₂ = e.relRU ρ₂₀) := by
  constructor
  · refine e.isImage_of_cells fun l χ hχ => ?_
    rcases ResU.Comp.get h l with ⟨e₁, -, -⟩ | ⟨ψ, e₁, -, e₃⟩ | ⟨ψ, e₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e₃, hc⟩
    · rw [hχ] at e₁; cases e₁
    · rw [hχ] at e₁; cases e₁
      rw [relRU_get] at e₃
      obtain ⟨ψ₀, -, rfl⟩ := Option.map_eq_some_iff.mp e₃
      exact ⟨ψ₀, rfl⟩
    · rw [hχ] at e₁; cases e₁
    · rw [hχ] at e₁; cases e₁
      rw [relRU_get] at e₃
      obtain ⟨ψ₀, -, rfl⟩ := Option.map_eq_some_iff.mp e₃
      exact e.compS_cell_left hc
  · refine e.isImage_of_cells fun l χ hχ => ?_
    rcases ResU.Comp.get h l with ⟨-, e₂, -⟩ | ⟨ψ, -, e₂, -⟩ | ⟨ψ, -, e₂, e₃⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e₃, hc⟩
    · rw [hχ] at e₂; cases e₂
    · rw [hχ] at e₂; cases e₂
    · rw [hχ] at e₂; cases e₂
      rw [relRU_get] at e₃
      obtain ⟨ψ₀, -, rfl⟩ := Option.map_eq_some_iff.mp e₃
      exact ⟨ψ₀, rfl⟩
    · rw [hχ] at e₂; cases e₂
      rw [relRU_get] at e₃
      obtain ⟨ψ₀, -, rfl⟩ := Option.map_eq_some_iff.mp e₃
      exact e.compS_cell_left (CellU.CompS.comm hc)

theorem compS_iff (ρ₁ ρ₂ ρ : ResU Loc Val) :
    ResU.CompS (e.relRU ρ₁) (e.relRU ρ₂) (e.relRU ρ) ↔ ResU.CompS ρ₁ ρ₂ ρ :=
  comp_iff e.nat2S e.nat3S ρ₁ ρ₂ ρ

/-- `ρ ≤ σ` is invariant, and a factor of a moved resource is moved. -/
theorem resLe_iff (ρ σ : ResU Loc Val) : ResU.Le (e.relRU ρ) (e.relRU σ) ↔ ResU.Le ρ σ := by
  constructor
  · rintro ⟨τ, hτ⟩
    obtain ⟨τ₀, rfl⟩ := (e.compS_operands hτ).2
    exact ⟨τ₀, (e.compS_iff _ _ _).mp hτ⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨e.relRU τ, (e.compS_iff _ _ _).mpr hτ⟩

theorem le_image {b σ : ResU Loc Val} (h : ResU.Le b (e.relRU σ)) : ∃ b₀, b = e.relRU b₀ := by
  obtain ⟨τ, hτ⟩ := h
  exact (e.compS_operands hτ).1

/-! ### The connectives -/

theorem relRU_eq_empty {ρ : ResU Loc Val} : e.relRU ρ = PMap.empty ↔ ρ = PMap.empty := by
  constructor
  · intro h; exact e.relRU_injective (h.trans relRU_empty.symm)
  · intro h; rw [h]; exact relRU_empty

theorem agree_pure (p : Prop) : e.Agree (pure p : SPropU Loc Val) (pure p) := fun _ =>
  and_congr_left' e.relRU_eq_empty

theorem agree_emp : e.Agree (emp : SPropU Loc Val) emp := e.agree_pure True

theorem agree_and {P' P Q' Q : SPropU Loc Val} (hP : e.Agree P' P) (hQ : e.Agree Q' Q) :
    e.Agree (BoLo.and P' Q') (BoLo.and P Q) := fun ρ => and_congr (hP ρ) (hQ ρ)

theorem agree_or {P' P Q' Q : SPropU Loc Val} (hP : e.Agree P' P) (hQ : e.Agree Q' Q) :
    e.Agree (BoLo.or P' Q') (BoLo.or P Q) := fun ρ => or_congr (hP ρ) (hQ ρ)

theorem agree_imp {P' P Q' Q : SPropU Loc Val} (hP : e.Agree P' P) (hQ : e.Agree Q' Q) :
    e.Agree (BoLo.imp P' Q') (BoLo.imp P Q) := fun ρ => imp_congr (hP ρ) (hQ ρ)

theorem agree_all {A : Type} {Φ' Φ : A → SPropU Loc Val} (h : ∀ x, e.Agree (Φ' x) (Φ x)) :
    e.Agree (BoLo.all Φ') (BoLo.all Φ) := fun ρ => forall_congr' fun x => h x ρ

theorem agree_ex {A : Type} {Φ' Φ : A → SPropU Loc Val} (h : ∀ x, e.Agree (Φ' x) (Φ x)) :
    e.Agree (BoLo.ex Φ') (BoLo.ex Φ) := fun ρ => exists_congr fun x => h x ρ

theorem agree_bang {P' P : SPropU Loc Val} (hP : e.Agree P' P) :
    e.Agree (BoLo.bang P') (BoLo.bang P) := e.agree_and e.agree_emp hP

theorem agree_sep {P' P Q' Q : SPropU Loc Val} (hP : e.Agree P' P) (hQ : e.Agree Q' Q) :
    e.Agree (sep P' Q') (sep P Q) := by
  intro ρ
  constructor
  · rintro ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
    obtain ⟨⟨ρ₁₀, rfl⟩, ⟨ρ₂₀, rfl⟩⟩ := e.compS_operands hc
    exact ⟨ρ₁₀, ρ₂₀, (e.compS_iff _ _ _).mp hc, (hP _).mp h₁, (hQ _).mp h₂⟩
  · rintro ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
    exact ⟨_, _, (e.compS_iff _ _ _).mpr hc, (hP _).mpr h₁, (hQ _).mpr h₂⟩

theorem agree_wand {P' P Q' Q : SPropU Loc Val} (hP : e.Agree P' P) (hs : e.Supp P')
    (hQ : e.Agree Q' Q) : e.Agree (wand P' Q') (wand P Q) := by
  intro ρ
  constructor
  · intro h ρ₁ ρ₂ h₁ hc
    exact (hQ ρ₂).mp (h _ _ ((hP ρ₁).mpr h₁) ((e.compS_iff _ _ _).mpr hc))
  · intro h σ₁ σ₂ h₁ hc
    obtain ⟨ρ₁, rfl⟩ := hs σ₁ h₁
    obtain ⟨ρ₂, rfl, hc'⟩ := comp_bwd e.nat2S e.nat3S hc
    exact (hQ ρ₂).mpr (h ρ₁ ρ₂ ((hP ρ₁).mp h₁) hc')

theorem agree_box (α : Life) {P' P : SPropU Loc Val} (hP : e.Agree P' P) :
    e.Agree (box (e α) P') (box α P) := fun ρ =>
  and_congr (hP ρ) (e.inStratum_relRU α ρ)

theorem agree_ptoOwn (l : Loc) (v : Val) : e.Agree (ptoOwn l v) (ptoOwn (Loc := Loc) l v) := by
  intro ρ
  show e.relRU ρ = ResU.single l (CellU.ownOf v) ↔ ρ = ResU.single l (CellU.ownOf v)
  have hs : e.relRU (ResU.single l (CellU.ownOf v)) = ResU.single l (CellU.ownOf v) := by
    rw [e.relRU_single]; rfl
  constructor
  · intro h; exact e.relRU_injective (h.trans hs.symm)
  · intro h; rw [h, hs]

theorem relRU_eq_single {ρ : ResU Loc Val} {l : Loc} {χ : CellU Loc Val}
    (h : e.relRU ρ = ResU.single l χ) : ∃ ψ, χ = e.relU ψ ∧ ρ = ResU.single l ψ := by
  have hl := congrArg (fun r => PMap.get r l) h
  simp only [relRU_get, ResU.single_get_self] at hl
  obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp hl
  refine ⟨ψ, rfl, e.relRU_injective ?_⟩
  rw [h, e.relRU_single]

theorem agree_ptoImm (l : Loc) (α : Life) {P' P : Val → SPropU Loc Val}
    (hP : ∀ v, e.Agree (P' v) (P v)) :
    e.Agree (ptoImm l (e α) P') (ptoImm l α P) := by
  intro ρ
  constructor
  · rintro ⟨s, v, σ, h, hρ, hPv, hle⟩
    obtain ⟨ψ, hψ, rfl⟩ := e.relRU_eq_single hρ
    rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s₀, u, τ, m, rfl⟩ | ⟨b, u, τ, m, Q, w, rfl⟩
    · exact absurd hψ.symm CellU.ownOf_ne_immOf
    · rw [e.relU_immOf] at hψ
      obtain ⟨hs, hv, hσ⟩ := CellU.immOf_inj hψ
      subst hs; subst hσ; subst hv
      exact ⟨s₀, v, τ, m, rfl, (hP v _).mp hPv, e.le_iff.mp hle⟩
    · rw [e.relU_mutOf] at hψ
      exact absurd hψ CellU.immOf_ne_mutOf
  · rintro ⟨s, v, σ, h, rfl, hPv, hle⟩
    refine ⟨e.mapL s, v, e.relRU σ, (e.inStratum_relRU _ _).mpr h, ?_, (hP v σ).mpr hPv,
      e.le_iff.mpr hle⟩
    rw [e.relRU_single, e.relU_immOf]

theorem relW_injective : Function.Injective (e.relW (Loc := Loc) (Val := Val)) := by
  intro P Q h
  funext v ρ
  have := congrFun (congrFun h v) (e.relRU ρ)
  exact propext ((e.img_relRU _ ρ).symm.trans ((Iff.of_eq this).trans (e.img_relRU _ ρ)))

/-- `ℓ ↦ Mut α P̂` moves to `ℓ ↦ Mut (eα) (e·P̂)`. -/
theorem agree_ptoMut (l : Loc) (α : Life) (P : Val → SPropU Loc Val) :
    e.Agree (ptoMut l (e α) (e.relW P)) (ptoMut l α P) := by
  intro ρ
  constructor
  · rintro ⟨b, v, σ, h, Q, hw, hle, hρ, hQ⟩
    obtain ⟨ψ, hψ, rfl⟩ := e.relRU_eq_single hρ
    rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨b₀, u, τ, m, Q₀, w₀, rfl⟩
    · simp [CellU.ownOf, CellU.mutOf, relU] at hψ
    · rw [e.relU_immOf] at hψ
      exact absurd hψ (CellU.immOf_ne_mutOf).symm
    · rw [e.relU_mutOf] at hψ
      have hb : b = e b₀ := CellU.mutOf_at hψ
      subst hb
      obtain ⟨-, -, hQQ⟩ := CellU.mutOf_inj hψ
      refine ⟨b₀, u, τ, m, Q₀, w₀, e.le_iff.mp hle, rfl, e.relW_injective ?_⟩
      rw [← e.ofS_relS, ← hQQ, hQ]
  · rintro ⟨b, v, σ, h, Q, hw, hle, rfl, rfl⟩
    refine ⟨e b, v, e.relRU σ, _, e.relS b Q, e.relS_holds h hw, e.le_iff.mpr hle, ?_,
      e.ofS_relS b Q⟩
    rw [e.relRU_single, e.relU_mutOf]

/-! ### `И` -/

/-- Below some point under every lifetime, every lifetime is moved. -/
def Cofinal : Prop := ∀ β : Life, ∃ β₁ ≤ β, ∀ α', α' < e β₁ → ∃ α, e α = α'

theorem fresh_bwd {P' P : Life → SPropU Loc Val} (h : ∀ α, e.Agree (P' (e α)) (P α))
    (ρ : ResU Loc Val) (hf : fresh P' (e.relRU ρ)) : fresh P ρ := by
  obtain ⟨β', hβ'⟩ := hf
  refine ⟨β', fun α hα => ?_⟩
  have hα' : e α < β' := lt_of_le_of_lt (e.le_self α) hα
  obtain ⟨hP, hs⟩ := hβ' (e α) hα'
  exact ⟨(h α ρ).mp hP, (e.inStratum_relRU α ρ).mp hs⟩

theorem fresh_fwd (hcof : e.Cofinal) {P' P : Life → SPropU Loc Val}
    (h : ∀ α, e.Agree (P' (e α)) (P α)) (ρ : ResU Loc Val) (hf : fresh P ρ) :
    fresh P' (e.relRU ρ) := by
  obtain ⟨β, hβ⟩ := hf
  obtain ⟨β₁, hβ₁, hall⟩ := hcof β
  refine ⟨e β₁, fun α' hα' => ?_⟩
  obtain ⟨α, rfl⟩ := hall α' hα'
  have hα : α < β := lt_of_lt_of_le (e.lt_iff.mp hα') hβ₁
  obtain ⟨hP, hs⟩ := hβ α hα
  exact ⟨(h α ρ).mpr hP, (e.inStratum_relRU α ρ).mpr hs⟩

end Emb

/-- Every shift is cofinal: below `β ⊓ ↓c` every lifetime is moved. -/
theorem Emb.shift_cofinal (c : Life) (k : ℕ) : (Emb.shift c k).Cofinal := by
  intro β
  refine ⟨β ⊓ (↓c), inf_le_left, fun α' hα' => ?_⟩
  have hlt : β ⊓ (↓c) < c := lt_of_le_of_lt inf_le_right (Life.down_sqsubset c)
  have h1 : OrderDual.ofDual (Emb.shift c k (β ⊓ (↓c))) < OrderDual.ofDual α' := hα'
  rw [Emb.shift_apply_lt hlt] at h1
  have h2 : OrderDual.ofDual c < OrderDual.ofDual (β ⊓ (↓c)) := hlt
  refine ⟨OrderDual.toDual (OrderDual.ofDual α' - k), ?_⟩
  have h3 : OrderDual.toDual (OrderDual.ofDual α' - k) < c := by
    show OrderDual.ofDual c < OrderDual.ofDual α' - k
    omega
  apply OrderDual.ofDual.injective
  rw [Emb.shift_apply_lt h3]
  show OrderDual.ofDual α' - k + k = OrderDual.ofDual α'
  omega

end Restrat
