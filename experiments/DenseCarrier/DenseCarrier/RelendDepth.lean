import DenseCarrier.RelendFL

/-!
# DenseCarrier — re-lending at depth three, inside a closure, inside a stored continuation

The instances `RelendFL.lean`'s and `RelendRoom.lean`'s general statements are tested at.

* **Depth three**, `mmm = Mut 'a (Mut 'b (Mut 'c 1))`: a borrow of a borrow of a borrow
  (`exists_vD_mmm`); at every re-lending, re-made, it is related at the moved reading, at `mmm` and
  at `F mmm` (`relend_mmm`, an instance of `relend_fov`); moved — each cell's stored predicate
  carried to its image — it is not, at every re-slotting other than the identity
  (`move_not_remake_mmm`). The move fails at depth three for the reason it fails at depth two
  (`ofS_relS_ne_of_gap`: an image does not hold at a cell the move leaves a slot free for), and the
  re-make holds at depth three by the induction that holds at every depth.
* **A nested borrow inside a closure**: the closure the fundamental property gives the identity,
  `λx. x : U (mmm ⊸ F mmm)`, is related at every reading (`vD_idClosure`) and so re-lends
  (`relend_idClosure_mmm`); the closure `RelendRoom.lean` builds at `kU = U (boxMM ⊸ F mm0)`,
  related only because its argument type is empty, does not (`not_relend_kU`).
* **Inside a stored continuation's type**: `kMut = Mut 'a ([@'a] kU)` (`not_relend_kMut`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-! ### Lending a value -/

/-- A value of `Mut 'x B` lies in the stratum of every slot below `@'x`'s slot. -/
theorem vD_mutVar_inStratum (ι : Slots L) {x : LifeVar} {B : VTy} {δ : LSubD L} {si bo : Life}
    (hx : δ.find? x = some (ι si)) (hbs : bo < si) {ls : List SRec} {u : Val} {σ : WRes}
    (h : vD (ℍ := ℍ) ι (.mut (.var x) B) ls δ u σ) : σ.InStratum bo := by
  obtain ⟨α, ℓ, hα, -, b, w, χ, hχ, Q, hw, ls₀, hαb, hρ, -⟩ := vD_mut_inv ι h
  rw [hx] at hα
  obtain rfl := Option.some.inj hα
  subst hρ
  exact ResU.inStratum_single _ (show bo < b from lt_of_lt_of_le hbs (ι.le_iff.mp hαb))

/-- **Lending a value**: a value of `B` whose resource lies in the stratum of `bo`, every value of
`B` lying there, is related lent at a cell at `bo` at `Mut 'y B`, when `@'y ⊑ ι bo`. -/
theorem vD_wrap (ι : Slots L) {y : LifeVar} {B : VTy} {δ : LSubD L} {bo : Life} {α : L}
    (hy : δ.find? y = some α) (hα : α ≤ ι bo) (ℓ : Loc) {u : Val} {w : WRes}
    (hu : vD (ℍ := ℍ) ι B [] δ u w) (hw : w.InStratum bo)
    (hstr : ∀ ls u' σ', vD (ℍ := ℍ) ι B ls δ u' σ' → σ'.InStratum bo) :
    vD (ℍ := ℍ) ι (.mut (.var y) B) [] δ (.loc ℓ)
      (ResU.single ℓ (CellU.mutOf bo u w hw (fun v r => vD (ℍ := ℍ) ι B [] δ v r.val) hu)) :=
  ⟨α, hy, ℓ, pure_sep_mk rfl ⟨bo, u, w, hw, _, hu, [], hα, rfl,
    by funext v r; exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨hstr _ _ _ h, h⟩⟩,
    fun x => by simp, hstr⟩⟩

theorem vD_unit_inStratum (ι : Slots L) {δ : LSubD L} (bo : Life) {ls : List SRec} {u : Val}
    {σ : WRes} (h : vD (ℍ := ℍ) ι .unit ls δ u σ) : σ.InStratum bo := by
  obtain ⟨rfl, -⟩ := h
  exact ResU.inStratum_empty bo

/-! ### Depth three -/

/-- `Mut 'a (Mut 'b (Mut 'c 1))`. -/
abbrev mmm : VTy := .mut (.var 0) (.mut (.var 1) (.mut (.var 2) .unit))

/-- Its payload `Mut 'b (Mut 'c 1)`. -/
abbrev mbc : VTy := .mut (.var 1) (.mut (.var 2) .unit)

theorem fov_mmm : FOV mmm := trivial

/-- `'a`, `'b`, `'c` at the positions of three slots. -/
def δ3 (ι : Slots L) (s₀ s₁ s₂ : Life) : LSubD L := ⟨[(0, ι s₀), (1, ι s₁), (2, ι s₂)]⟩

theorem δ3_find0 (ι : Slots L) (s₀ s₁ s₂ : Life) : (δ3 ι s₀ s₁ s₂).find? 0 = some (ι s₀) := rfl
theorem δ3_find1 (ι : Slots L) (s₀ s₁ s₂ : Life) : (δ3 ι s₀ s₁ s₂).find? 1 = some (ι s₁) := rfl
theorem δ3_find2 (ι : Slots L) (s₀ s₁ s₂ : Life) : (δ3 ι s₀ s₁ s₂).find? 2 = some (ι s₂) := rfl

/-- **`Mut 'b (Mut 'c 1)` holds at a borrow of a borrow** whose outer cell is at `g`, when
`@'b ⊑ ι g` and `'c` reads a slot `s₂` above `g`. -/
theorem exists_vD_mbc (ι : Slots L) {δ : LSubD L} {g s₂ : Life} {β : L}
    (h1 : δ.find? 1 = some β) (hβ : β ≤ ι g) (h2 : δ.find? 2 = some (ι s₂)) (hg : g < s₂) :
    ∃ ρ, vD (ℍ := ℍ) ι mbc [] δ (.loc 0) ρ ∧ ∃ ψ, ρ.get 0 = some ψ ∧ ψ.at = g := by
  have hin := vD_wrap (ℍ := ℍ) ι (B := .unit) h2 le_rfl 1
    (⟨rfl, rfl⟩ : vD (ℍ := ℍ) ι .unit [] δ .unit PMap.empty) (ResU.inStratum_empty s₂)
    (fun _ _ _ h => vD_unit_inStratum ι s₂ h)
  refine ⟨_, vD_wrap (ℍ := ℍ) ι h1 hβ 0 hin (ResU.inStratum_single _ hg)
    (fun _ _ _ h => vD_mutVar_inStratum ι h2 hg h), _, ResU.single_get_self _ _, rfl⟩

/-- **A borrow of a borrow of a borrow**, related at `mmm` with `'a`, `'b`, `'c` at its three
cells' slots. -/
theorem exists_vD_mmm (ι : Slots L) {s₀ s₁ s₂ : Life} (h01 : s₀ < s₁) (h12 : s₁ < s₂) :
    ∃ ρ, vD (ℍ := ℍ) ι mmm [] (δ3 ι s₀ s₁ s₂) (.loc 0) ρ := by
  have hin := vD_wrap (ℍ := ℍ) ι (B := .unit) (δ3_find2 ι s₀ s₁ s₂) le_rfl 2
    (⟨rfl, rfl⟩ : vD (ℍ := ℍ) ι .unit [] (δ3 ι s₀ s₁ s₂) .unit PMap.empty)
    (ResU.inStratum_empty s₂) (fun _ _ _ h => vD_unit_inStratum ι s₂ h)
  have hmid := vD_wrap (ℍ := ℍ) ι (δ3_find1 ι s₀ s₁ s₂) le_rfl 1 hin (ResU.inStratum_single _ h12)
    (fun _ _ _ h => vD_mutVar_inStratum ι (δ3_find2 ι s₀ s₁ s₂) h12 h)
  exact ⟨_, vD_wrap (ℍ := ℍ) ι (δ3_find0 ι s₀ s₁ s₂) le_rfl 0 hmid (ResU.inStratum_single _ h01)
    (fun _ _ _ h => vD_mutVar_inStratum ι (δ3_find1 ι s₀ s₁ s₂) h01 h)⟩

/-- **Re-lending at depth three**: at every re-lending, a borrow of a borrow of a borrow has a
re-make related at the moved reading, at `mmm` and at `F mmm`. An instance of `relend_fov`. -/
theorem relend_mmm {ι : Slots L} (R : Relend ι) {s₀ s₁ s₂ : Life} (h01 : s₀ < s₁)
    (h12 : s₁ < s₂) :
    ∃ ρ ρ', vD (ℍ := ℍ) ι mmm [] (δ3 ι s₀ s₁ s₂) (.loc 0) ρ ∧ RemakeR R.θ ρ ρ' ∧
      vD (ℍ := ℍ) ι mmm [] ((δ3 ι s₀ s₁ s₂).map R.ψ) (.loc 0) ρ' ∧
      cD (ℍ := ℍ) ι (.ret mmm) [] (δ3 ι s₀ s₁ s₂) (.val (.loc 0)) ρ ∧
      cD (ℍ := ℍ) ι (.ret mmm) [] ((δ3 ι s₀ s₁ s₂).map R.ψ) (.val (.loc 0)) ρ' := by
  obtain ⟨ρ, hρ⟩ := exists_vD_mmm (ℍ := ℍ) ι h01 h12
  obtain ⟨ρ', hR, hρ'⟩ := relend_fov R mmm fov_mmm [] _ _ ρ hρ []
  exact ⟨ρ, ρ', hρ, hR, hρ', wpTS_val [] _ _ ρ hρ, wpTS_val [] _ _ ρ' hρ'⟩

/-! ### Moving fails at depth three -/

/-- **An image is not a predicate that holds where the move leaves a slot free**: if `P` holds at
a resource with a top-level cell at a slot `g` no slot moves to, the image of a stored predicate is
not `P`. -/
theorem ofS_relS_ne_of_gap {c : Life} (θ : Restrat.Emb c) {g : Life} (hg : ∀ x, θ x ≠ g)
    {b₀ : Life} (Q₀ : Val → SPropS Loc Val b₀) {P : Val → WProp} {u : Val} {r : WRes} {l : Loc}
    {ψ : CellU Loc Val} (hP : P u r) (hl : r.get l = some ψ) (hψ : ψ.at = g) :
    ofS (θ.relS b₀ Q₀) ≠ P := by
  intro h
  rw [← h, θ.ofS_relS] at hP
  obtain ⟨r₀, hr₀, -⟩ := hP
  have hc := congrArg (fun r => PMap.get r l) hr₀
  simp only [Restrat.Emb.relRU_get, hl] at hc
  obtain ⟨ψ₀, -, hψ₀⟩ := Option.map_eq_some_iff.mp hc
  have hat := congrArg CellU.at hψ₀
  rw [Restrat.Emb.at_relU, hψ] at hat
  exact hg _ hat

/-- The slot a re-slotting moves just below a slot it fixes has no preimage. -/
theorem no_preimage {c : Life} (θ : Restrat.Emb c) {m : ℕ}
    (hfix : θ (OrderDual.toDual m) = OrderDual.toDual m)
    (hmove : θ (OrderDual.toDual (m + 1)) < OrderDual.toDual (m + 1)) :
    ∀ x, θ x ≠ OrderDual.toDual (m + 1) := by
  intro x hx
  rcases le_or_gt (OrderDual.toDual m) x with h | h
  · have := θ.monotone h
    rw [hfix, hx] at this
    exact absurd this (not_le.mpr (succ_lt_life m))
  · have hle : x ≤ OrderDual.toDual (m + 1) := by
      have : m < OrderDual.ofDual x := h
      show m + 1 ≤ OrderDual.ofDual x
      omega
    have := θ.monotone hle
    rw [hx] at this
    exact absurd this (not_le.mpr hmove)

/-- **At depth three the move fails and the re-make holds**: for every re-lending other than the
identity, a borrow of a borrow of a borrow is related at `mmm`; moved by `θ.relRU` (stored
predicates to their images) it is not related at the moved reading; re-made it is. -/
theorem move_not_remake_mmm {ι : Slots L} (R : Relend ι) (hθ : ∃ x, R.θ x ≠ x) :
    ∃ (δ : LSubD L) (ρ : WRes), vD (ℍ := ℍ) ι mmm [] δ (.loc 0) ρ ∧
      ¬ vD (ℍ := ℍ) ι mmm [] (δ.map R.ψ) (.loc 0) (R.θ.relRU ρ) ∧
      ∃ ρ', RemakeR R.θ ρ ρ' ∧ vD (ℍ := ℍ) ι mmm [] (δ.map R.ψ) (.loc 0) ρ' := by
  obtain ⟨m, hfix, hmove⟩ := exists_adjGap R.θ hθ
  have h01 : OrderDual.toDual (m + 2) < (OrderDual.toDual (m + 1) : Life) := succ_lt_life (m + 1)
  have h12 : OrderDual.toDual (m + 1) < (OrderDual.toDual m : Life) := succ_lt_life m
  set δ := δ3 ι (OrderDual.toDual (m + 2)) (OrderDual.toDual (m + 1)) (OrderDual.toDual m)
  obtain ⟨ρ, hρ⟩ := exists_vD_mmm (ℍ := ℍ) ι h01 h12
  refine ⟨δ, ρ, hρ, ?_, relend_fov R mmm fov_mmm [] δ _ ρ hρ []⟩
  intro hmv
  -- the payload at the moved reading holds at a borrow of a borrow at the free slot `m + 1`
  have h1 : (δ.map R.ψ).find? 1 = some (ι (R.θ (OrderDual.toDual (m + 1)))) := by
    show some (R.ψ (ι _)) = _; rw [R.agree]
  have h2 : (δ.map R.ψ).find? 2 = some (ι (OrderDual.toDual m)) := by
    show some (R.ψ (ι _)) = _; rw [R.agree, hfix]
  obtain ⟨r, hr, ψ, hψ, hψat⟩ := exists_vD_mbc (ℍ := ℍ) ι h1 (ι.le_iff.mpr hmove.le) h2 h12
  -- the moved outer cell stores an image
  obtain ⟨α, ℓ, -, -, b, u, σ, hσ, Q, hw, ls₀, -, hρ', hQ, -, -⟩ := vD_mut_inv ι hmv
  obtain ⟨ψ₀, hψ₀, -⟩ := R.θ.relRU_eq_single hρ'
  rcases CellU.rep ψ₀ with ⟨w, rfl⟩ | ⟨s, w, τ, k, rfl⟩ | ⟨b₀, w, τ, k, Q₀, w₀, rfl⟩
  · rw [Restrat.Emb.relU_ownOf] at hψ₀
    exact CellU.ownOf_ne_mutOf hψ₀.symm
  · rw [R.θ.relU_immOf] at hψ₀
    exact CellU.immOf_ne_mutOf hψ₀.symm
  · rw [R.θ.relU_mutOf] at hψ₀
    obtain rfl : b = R.θ b₀ := CellU.mutOf_at hψ₀
    obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj hψ₀
    refine ofS_relS_ne_of_gap R.θ (no_preimage R.θ hfix hmove) Q₀
      (P := fun x => vD (ℍ := ℍ) ι mbc ls₀ (δ.map R.ψ) x) (u := .loc 0) ?_ hψ hψat hQ
    show vD (ℍ := ℍ) ι mbc ls₀ (δ.map R.ψ) (.loc 0) r
    rw [vD_ls ι mbc trivial ls₀ []]
    exact hr

/-! ### A nested borrow inside a closure -/

/-- **The identity closure** `λx. x`, related at `U (A ⊸ F A)` at every reading and every list, with
an empty resource: the term the fundamental property relates at every reading. -/
theorem vD_idClosure (ι : Slots L) (A : VTy) (ls : List SRec) (δ : LSubD L) :
    vD (ℍ := ℍ) ι (.thunk (.arr A (.ret A))) ls δ (.lam BoCa.v0) PMap.empty := by
  intro ls' _ w ρ₁ ρ₂ h₁ hc
  obtain rfl := eq_of_compS_empty_left hc
  refine wpTS_lolli ls' BoCa.v0 w _ _ ?_
  have he : BoCa.v0.subst 0 w = .val w := by simp [BoCa.v0, Expr.subst]
  rw [he]
  exact wpTS_val ls' w _ _ h₁

/-- **A nested borrow inside a closure re-lends when the closure is the fundamental property's**:
the identity closure at `U (mmm ⊸ F mmm)` is related at the moved reading at the re-make of its
(empty) resource. -/
theorem relend_idClosure_mmm {ι : Slots L} (R : Relend ι) (ls : List SRec) (δ : LSubD L) :
    vD (ℍ := ℍ) ι (.thunk (.arr mmm (.ret mmm))) ls δ (.lam BoCa.v0) PMap.empty ∧
      ∃ ρ', RemakeR R.θ PMap.empty ρ' ∧
        vD (ℍ := ℍ) ι (.thunk (.arr mmm (.ret mmm))) (ls.map (Targets.srecRestrat R.θ))
          (δ.map R.ψ) (.lam BoCa.v0) ρ' :=
  ⟨vD_idClosure ι mmm ls δ, PMap.empty, remakeR_empty, vD_idClosure ι mmm _ _⟩

end DenseCarrier

end
