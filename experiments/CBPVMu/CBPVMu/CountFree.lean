import CBPVMu.Count

/-!
# CBPVMu — a fuel-free borrowed fold

`countFree = Z (λself. Λ. λl. withload l (Λ. λu. case u {inj₁ w. w; 0 | inj₂ t. self [] t to n.
inj₂ n}))` counts a borrowed list by recursion on the list itself.

The measure is the number of cells in the witness of the borrowed `imm` cell (`dsize`).  A
borrow's witness is finite (`PMap.finite`), and the view `withload` hands its callback is an
image `χ ∈ reb_β(σ)` of the loaded cell's witness `σ`: at the tail `ℓ′`, `reb_β`'s `own` clause
gives `χ(ℓ′) = imm({β}, u, q/ℓ′)` for a piece `q ≤ σ` holding `ℓ′` (`typed_image_pos`), so the
tail's witness `q/ℓ′` has strictly fewer cells than `σ` (`dsize_image_lt`).

* `rebChooseTW_sized`: a chooser whose payload input carries a predicate `K` of the witness
  also returns, with the chosen image, the witness it is an image of.
* `withload_sized`: `withload` at `Imm a T₁` whose callback is asked only at the views
  `χ ∈ reb_β(σ)` of a witness `σ` with `K σ` — `K` any property of the borrowed cell's own
  witness.  The proof is `withload_compatX`'s, with the chooser of `rebChooseTW_sized`.
* `countFree_wp`: induction on a bound of `dsize`.
* `countFree_semV : SemV Δ [] countFree (!U(∀'a. Imm 'a L ⊸ F N))`.
* `countFreeProg`: build a 3-cell list, borrow it, count, end the borrow, free it; it runs from
  the empty memory to a numeral and the empty memory (`countFreeProg_runs`), and the interpreter
  returns `3` with no cell left (`countFreeProg_eval`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The measure -/

open Classical in
/-- The locations of a resource, as a finite set. -/
def rdom (ρ : WRes) : Finset Loc :=
  (Classical.choose ρ.finite).toFinset.filter (fun l => ρ.get l ≠ none)

theorem mem_rdom {ρ : WRes} {l : Loc} : l ∈ rdom ρ ↔ ρ.get l ≠ none := by
  classical
  unfold rdom
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (Classical.choose_spec ρ.finite l h), h⟩

/-- The number of cells of a resource. -/
def dsize (ρ : WRes) : Nat := (rdom ρ).card

/-- A resource whose cells are among `σ`'s, less one of `σ`'s, is smaller. -/
theorem dsize_lt {σ' σ : WRes} {l : Loc} (hl : σ.get l ≠ none)
    (h : ∀ m, σ'.get m ≠ none → σ.get m ≠ none ∧ m ≠ l) : dsize σ' < dsize σ := by
  classical
  have hsub : rdom σ' ⊆ (rdom σ).erase l := fun m hm => by
    obtain ⟨h₁, h₂⟩ := h m (mem_rdom.mp hm)
    exact Finset.mem_erase.mpr ⟨h₂, mem_rdom.mpr h₁⟩
  have hl' : l ∈ rdom σ := mem_rdom.mpr hl
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hl'] at this
  have hpos : 0 < (rdom σ).card := Finset.card_pos.mpr ⟨l, hl'⟩
  unfold dsize; omega

/-- A piece `q ≤ σ` holding `l`, less `l`, is smaller than `σ`. -/
theorem dsize_del_lt {q σ : WRes} {l : Loc} (hle : ResU.Le q σ) (hq : ∃ ψ, q.get l = some ψ) :
    dsize (q.del l) < dsize σ := by
  obtain ⟨τ, hτ⟩ := hle
  obtain ⟨ψ, eψ⟩ := hq
  obtain ⟨ψ', e', -⟩ := ResU.CompS.get_left hτ eψ
  refine dsize_lt (l := l) (by rw [e']; simp) (fun m hm => ?_)
  by_cases hml : m = l
  · subst hml; exact absurd (ResU.del_get_self q m) hm
  · have hqm : q.get m ≠ none := by
      have : (q.del l).get m = q.get m := by simp [ResU.del, hml]
      rwa [this] at hm
    obtain ⟨φ, eφ⟩ := Option.ne_none_iff_exists'.mp hqm
    obtain ⟨φ', eφ', -⟩ := ResU.CompS.get_left hτ eφ
    exact ⟨by rw [eφ']; simp, hml⟩

/-! ### `withload` with the witness the view is an image of -/

/-- A chooser whose payload input also asks `K` of the cell's witness returns, with its image
`χ`, the witness `σ` it is an image of: `K σ`, the payload input at `σ`, and `χ ∈ reb_β(σ)`. -/
theorem rebChooseTW_sized {ls : List SRec} {l : Loc} {R : Val → WRes → Prop}
    {P₀ P : Life → Val → WProp} (K : WRes → Prop) (h : RebChooseTW ls l R P₀ P) :
    RebChooseTW ls l (fun w σ => R w σ ∧ K σ) P₀
      (fun β w χ => P β w χ ∧ ∃ σ, K σ ∧ R w σ ∧ ResU.Reb β σ χ) := by
  intro W F χ₀ σ ps β w s hs hT htg hβ hW hR hreb₀ hP₀
  obtain ⟨χ, hreb, hP, hag, hEF, hEI, hin, hout⟩ := h W F χ₀ σ ps β w s hs hT htg hβ hW hR.1 hreb₀ hP₀
  exact ⟨χ, hreb, ⟨hP, σ, hR.2, hR.1, hreb⟩, hag, hEF, hEI, hin, hout⟩

/-- **`withload` with a sized callback.**  `withload ℓ v_f` at a borrow `ℓ : Imm a T₁` whose
cell's witness has the property `K`, and a callback `v_f` asked only at the views
`χ ∈ 𝒱⟦Imm̲ 'x T₁⟧` that are images `χ ∈ reb_β(σ)` of a witness `σ` with `K σ` observable at
`T₁`.  `withload_compatX`'s proof (6.144, 6.134, 6.150), with the chooser of
`rebChooseTW_sized`. -/
theorem withload_sized {T₁ : VTy} (x : LifeVar) (hfree₁ : ¬ VFree x T₁)
    {a : Lifetime.Life} {ls : List SRec} {δ : LSub} {ℓ : Loc} {vf : Val} {ρ₁ ρ₂ τ : WRes}
    (K : WRes → Prop) (Q : List SRec → Val → WProp)
    (hv : vP (.imm a T₁) ls δ (.loc ℓ) ρ₁)
    (hK : ∀ s u σ h, ρ₁ = ResU.single ℓ (CellU.immOf s u σ h) → K σ)
    (hc : ResU.CompS ρ₁ ρ₂ τ)
    (hcb : ∀ β w χ ρ', vC true (T₁.immReborrow (.var x)) ls (δ.extend x β) w χ →
        (∃ σ, K σ ∧ vC false T₁ ls δ w σ ∧ ResU.Reb β σ χ) → ResU.CompS ρ₂ χ ρ' →
        wpTS ls (.app (.app (.val vf) (.val .unit)) (.val w)) (fun ls' v => box β (Q ls' v)) ρ') :
    wpTS ls (.app (.app withload (.val (.loc ℓ))) (.val vf)) Q τ := by
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.app (.app BoCa.v0 unit') (.app load' BoCa.v1))))
      = Expr.val (Val.lam (.app (.app BoCa.v0 unit') (eLoad ℓ))) := by
    simp [eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit', load']
  have hβ₂ : Expr.subst 0 vf (Expr.app (.app BoCa.v0 unit') (eLoad ℓ))
      = Expr.app (.app (.val vf) (.val .unit)) (eLoad ℓ) := by
    simp [eLoad, Expr.subst, BoCa.v0, unit']
  refine wpTS_bind (.appL .hole vf) (.app (.val (Val.lam (.val (Val.lam
    (.app (.app BoCa.v0 unit') (.app load' BoCa.v1)))))) (.val (.loc ℓ))) ls Q τ ?_
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  simp only [Kont.plug]
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  obtain ⟨α₀, ha, ℓ', hs₂⟩ := hv
  obtain ⟨⟨hℓ', hcoh⟩, himm⟩ := pure_sep_iff.mp hs₂
  have hℓℓ : ℓ' = ℓ := by
    have := congrArg Subtype.val hℓ'; simpa using this.symm
  subst hℓℓ
  refine wpTS_bind (.appR (.app (.val vf) (.val .unit)) .hole) (eLoad ℓ') ls _ τ ?_
  have hcell₀ : ptoImm ℓ' α₀ (fun u σ => vC false T₁ ls δ u σ ∧ K σ) ρ₁ := by
    obtain ⟨s, u, σ, hs, hρ, hP, hαs⟩ := ptoImmO_toImm himm
    exact ⟨s, u, σ, hs, hρ, ⟨hP, hK s u σ hs hρ⟩, hαs⟩
  refine wpTS_load_I ls ℓ' α₀ (fun u σ => vC false T₁ ls δ u σ ∧ K σ) _ τ
    ⟨ρ₁, ρ₂, hc, hcell₀, ?_⟩
  intro vℓ ρc ρcomp hcell hccomp
  simp only [Kont.plug]
  have hesc₀ : RebChooseTW ls ℓ'
      (fun w σ => w = vℓ ∧ vC false T₁ ls δ w σ)
      (fun β w χ => vShape (T₁.immReborrow (.var x)) (δ.extend x β) w χ)
      (fun β w χ => (⌜vℓ = w⌝ ⋆ vC true (T₁.immReborrow (.var x)) ls (δ.extend x β) w) χ) := by
    obtain ⟨S₀, δ₀, he, hc⟩ := hcoh
    have hx₀ : ¬ VFree S₀.lifeBound S₀ := fun h => lt_irrefl _ (lt_vLifeBound h)
    have heβ : ∀ β : Life, TyEq (T₁.immReborrow (.var x)) (δ.extend x β)
        (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) := fun β =>
      TyEq.immReborrow (by rw [interp_ext_self, interp_ext_self])
        (TyEq.extend_left hx₀ β (TyEq.extend_left hfree₁ β he).symm).symm
    have eR : vC false T₁ ls δ = vC false S₀ ls δ₀ := vC_tyEq he false ls
    have eP₀ : ∀ β : Life, vShape (T₁.immReborrow (.var x)) (δ.extend x β)
        = vShape (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) :=
      fun β => vShape_tyEq (heβ β)
    have eP : ∀ β : Life, vC true (T₁.immReborrow (.var x)) ls (δ.extend x β)
        = vC true (S₀.immReborrow (.var S₀.lifeBound)) ls (δ₀.extend S₀.lifeBound β) :=
      fun β => vC_tyEq (heβ β) true ls
    simp only [eR, eP₀, eP]
    rcases hc with ⟨r, hr, rfl, rfl, hag⟩ | ⟨r, hr, p, u, hch, hag⟩
    · exact rebChooseTW_pin vℓ (rebChooseTW_top hr hag hx₀)
    · exact rebChooseTW_pin vℓ (rebChooseTW_deep hr hch hag hx₀)
  have hesc := rebChooseTW_sized K hesc₀
  have hcell' : ptoImm ℓ' α₀ (fun v σ => ((v = vℓ ∧ vC false T₁ ls δ v σ) ∧ K σ) ∧
      fresh (fun b => reborrow b (vShape (T₁.immReborrow (.var x)) (δ.extend x b) v)) σ) ρc := by
    refine ptoImm_mono (fun u σ h => ?_) ρc hcell
    obtain ⟨he, hobs, hKσ⟩ := pure_sep_iff.mp h
    subst he
    exact ⟨⟨⟨rfl, hobs⟩, hKσ⟩, six132_shape_fresh hfree₁ δ vℓ σ (vC_vShape false T₁ hobs)⟩
  refine wpTS_reborrow ls ℓ' α₀ _ _ _ _ Q hesc ρcomp
    ⟨ρc, ρ₂, ResU.CompS.comm hccomp, hcell', ?_⟩
  obtain ⟨g₂, hg₂⟩ := ResU.exists_stratum ρ₂
  refine ⟨g₂, fun β hβ => ⟨?_, hg₂.mono (le_of_lt hβ)⟩⟩
  intro v σ ρpc hP hpc
  obtain ⟨hP₁, σ₀, hKσ₀, ⟨hvv₀, hobs₀⟩, hreb₀⟩ := hP
  obtain ⟨hvv, hreb⟩ := pure_sep_iff.mp hP₁
  subst hvv
  exact hcb β vℓ σ ρpc hreb ⟨σ₀, hKσ₀, hobs₀, hreb₀⟩ hpc

/-! ### The counter -/

/-- A numeral at the relation, holding no resource. -/
theorem vC_num (b : Bool) (ls : List SRec) (δ : LSub) : ∀ k, vC b natN ls δ (num k) PMap.empty
  | 0 => vC_roll natBody_noMut natN_closed (Or.inl ⟨.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩)
  | k + 1 => vC_roll natBody_noMut natN_closed
      (Or.inr ⟨num k, pure_sep_iff.mpr ⟨rfl, vC_num b ls δ k⟩⟩)

/-- The callback at a closed handle `S`:
`Λ. λu. case u {inj₁ w. w; 0 | inj₂ t. S [] t to n. inj₂ n}`. -/
def cbV (S : Val) : Val := .lam (.val (.lam (.case (.var 0)
    (.seq (.var 0) (.inj₁ (.val .unit)))
    (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0))))))

/-- The callback inside `countFree`'s body, the handle `self` at index `5`. -/
def cbFE : Expr := .val (.lam (.val (.lam (.case (.var 0)
    (.seq (.var 0) (.inj₁ (.val .unit)))
    (bindE (.app (.app (.var 5) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))))))

/-- The body of `countFree = Z (λself. λ_. λl. withload l cb)`. -/
def cfB : Expr := .val (.lam (.app (.app withload (.var 0)) cbFE))

theorem cfB_closed : closedAt 2 cfB = true := rfl

/-- `countFree`, a closed λ-value. -/
def countFreeV : Val := fixV cfB

theorem countFreeV_closed : closedAt 0 countFreeV.1 = true := by
  simp [countFreeV, fixV, closedAt]
  rfl

/-- The handle `countFree` recurses through. -/
abbrev selfC : Val := selfV cfB

theorem selfC_closed : closedAt 0 selfC.1 = true := selfV_closed cfB_closed

theorem cbV_closed {S : Val} (hS : closedAt 0 S.1 = true) : closedAt 0 (cbV S).1 = true := by
  simp [cbV, bindE, closedAt, closedAt_mono S.1 hS (Nat.zero_le _)]

theorem withload_closed : closedAt 0 withload = true := rfl

/-- `countFree`'s body at `λl`, the handle `S` substituted. -/
def bodyL (S : Val) : Expr := .app (.app withload (.var 0)) (.val (cbV S))

theorem cfB_subst {S : Val} (hS : closedAt 0 S.1 = true) (w : Val) :
    (cfB.subst 1 S).subst 0 w = .val (.lam (bodyL S)) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  have h₃ : ∀ j s, Expr.subst j s withload = withload :=
    fun j s => subst_closedAt withload s withload_closed (Nat.zero_le j)
  simp [cfB, cbFE, bodyL, cbV, bindE, Expr.subst, h₁, h₂, h₃]

theorem bodyL_subst {S : Val} (hS : closedAt 0 S.1 = true) (ℓ : Loc) :
    (bodyL S).subst 0 (.loc ℓ) = .app (.app withload (.val (.loc ℓ))) (.val (cbV S)) := by
  have h₃ : ∀ j s, Expr.subst j s withload = withload :=
    fun j s => subst_closedAt withload s withload_closed (Nat.zero_le j)
  simp [bodyL, Expr.subst, h₃, val_subst_closed (cbV_closed hS)]

/-- A β-step inside an evaluation context. -/
theorem wpTS_beta_in (K : Kont) (b : Expr) (v : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (K.plug (b.subst 0 v)) Q) (wpTS ls (K.plug (.app (.val (.lam b)) (.val v))) Q) :=
  wpTS_step (step_in K (fun μ => Head.beta μ b v)) ls Q

/-- The callback applied: `cbV S [] w` reaches `case w {…}`. -/
theorem cbV_app {S : Val} (hS : closedAt 0 S.1 = true) (w : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.case (.val w) (.seq (.var 0) (.inj₁ (.val .unit)))
        (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))) Q)
      (wpTS ls (.app (.app (.val (cbV S)) (.val .unit)) (.val w)) Q) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  intro ρ h
  refine wpTS_beta_in (.appL .hole w) _ Val.unit ls Q ρ ?_
  have e : (Kont.appL .hole w).plug (Expr.subst 0 Val.unit (.val (.lam (.case (.var 0)
      (.seq (.var 0) (.inj₁ (.val .unit)))
      (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))))))
      = .app (.val (.lam (.case (.var 0) (.seq (.var 0) (.inj₁ (.val .unit)))
      (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))))) (.val w) := by
    simp [Kont.plug, bindE, Expr.subst, h₂]
  rw [e]
  refine wpTS_lolli _ _ w Q ρ ?_
  simpa [bindE, Expr.subst, h₁, h₂] using h

/-- The borrowed list's cell witness, in the view `withload` hands over: at `inj₂ (ℓ′)` the tail's
witness has fewer cells than the loaded cell's.  `typed_image_pos` at the root `ℓ′` of the
witness `σ`. -/
theorem dsize_image_lt {β : Life} {δ : LSub} {ls : List SRec} {σ χ : WRes} {ℓ' : Loc}
    (hobs : vC false listL ls δ (.inj₂ (.loc ℓ')) σ) (hreb : ResU.Reb β σ χ)
    (hview : vC true (listL.immReborrow (.var 0)) ls (δ.extend 0 β) (.inj₂ (.loc ℓ')) χ) :
    ∀ s u σ' h, χ = ResU.single ℓ' (CellU.immOf s u σ' h) → dsize σ' < dsize σ := by
  intro s u σ' h hχ
  -- the parent's payload: `σ = ℓ′ ↦ own(v″) ● …`
  obtain ⟨-, -, hunr⟩ := vC_mu_iff.mp hobs
  rcases hunr with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
  · have := congrArg Subtype.val (pure_sep_iff.mp hs).1
    simp at this
  obtain ⟨e₂, hr⟩ := pure_sep_iff.mp hs
  have e₂' : v₂ = .loc ℓ' := by
    have := congrArg Subtype.val e₂; exact Val.ext (by simpa using this.symm)
  subst e₂'
  obtain ⟨m, v'', hs'⟩ := hr
  obtain ⟨em, ρa, ρb, hcab, hown, -⟩ := pure_sep_iff.mp hs'
  have em' : m = ℓ' := by
    have := congrArg Subtype.val em; simpa using this.symm
  subst em'
  rw [hown] at hcab
  have hσ : σ.get m = some (CellU.ownOf v'') :=
    (ResU.CompS.get_left_of_ne_imm hcab (ResU.single_get_self m _) (by simp)).2
  -- the view is an image of `σ`: `reb_β`'s `own` clause at `m`
  have hx : ¬ VFree 0 listL := by simp [VFree, listL, listBody]
  obtain ⟨q, hq, eχ, hle, hqm, -⟩ := typed_image_pos (T := listL) (S := listL) hx
    (RefPos.mu listL_closed (RefPos.sumR (RefPos.ref listL m))) hσ hreb
    (vC_vShape true _ hview)
  have eχ' : χ.get m = some (CellU.immOf s u σ' h) := by rw [hχ]; simp
  rw [eχ] at eχ'
  obtain ⟨-, -, hσ'⟩ := CellU.immOf_inj (Option.some.inj eχ')
  rw [← hσ']
  exact dsize_del_lt hle hqm

/-- The postcondition of `F N`. -/
abbrev natQ (δ : LSub) : List SRec → Val → WProp := fun ls' v => vP natN ls' δ v

/-- A borrow's cell witness has fewer than `n` cells. -/
def WitLt (ℓ : Loc) (ρ : WRes) (n : Nat) : Prop :=
  ∀ s u σ h, ρ = ResU.single ℓ (CellU.immOf s u σ h) → dsize σ < n

/-- **The fuel-free count**, by induction on a bound of the borrowed cell's witness size:
`withload ℓ (cbV selfC)` counts the list at any borrow `ℓ : Imm a L`. -/
theorem countFree_body : ∀ (n : Nat) (a : Lifetime.Life) (δ : LSub) (ls : List SRec) (ℓ : Loc)
    (ρ : WRes), vP (.imm a listL) ls δ (.loc ℓ) ρ → WitLt ℓ ρ n →
    wpTS ls (.app (.app withload (.val (.loc ℓ))) (.val (cbV selfC))) (natQ δ) ρ := by
  intro n
  induction n with
  | zero =>
      intro a δ ls ℓ ρ hv hn
      obtain ⟨α₀, -, ℓ', hs⟩ := hv
      obtain ⟨⟨hℓ', -⟩, himm⟩ := pure_sep_iff.mp hs
      obtain ⟨s, u, σ, hσ, hρ, -⟩ := ptoImmO_toImm himm
      exact absurd (hn s u σ hσ (by
        have e : ℓ' = ℓ := by have := congrArg Subtype.val hℓ'; simpa using this.symm
        rw [hρ, e])) (Nat.not_lt_zero _)
  | succ n ih =>
      intro a δ ls ℓ ρ hv hn
      refine withload_sized (T₁ := listL) 0 (by simp [VFree, listL, listBody])
        (fun σ => dsize σ < n + 1) (natQ δ) hv hn (ResU.comp_empty_right ρ) ?_
      intro β w χ ρ' hview ⟨σ, hKσ, hobs, hreb⟩ hcomp
      rw [eq_of_compS_empty_left hcomp]
      refine cbV_app selfC_closed w ls _ χ ?_
      -- the view unrolls to `1 ⊕ Imm 'x L`
      have hview' := (vC_immReborrow_mu_iff (A := listBody) ⟨trivial, Nat.zero_lt_one⟩ _ true ls
        (δ.extend 0 β) w χ).mp hview
      rcases hview' with ⟨w₁, hs⟩ | ⟨t, hs⟩
      · -- `inj₁ w. w; 0`
        obtain ⟨rfl, hχ, rfl⟩ := pure_sep_iff.mp hs
        subst hχ
        refine wpTS_sum₁ _ _ _ _ _ _ ?_
        refine wpTS_1 _ _ _ _ ?_
        exact wpTS_val ls (num 0) _ _ ⟨vC_num true ls δ 0, ResU.inStratum_empty β⟩
      · -- `inj₂ t. selfC [] t to n. inj₂ n`
        obtain ⟨rfl, ht⟩ := pure_sep_iff.mp hs
        obtain ⟨ℓ', rfl⟩ : ∃ ℓ', t = Val.loc ℓ' := by
          obtain ⟨α₀, -, ℓ', hs₁⟩ := ht
          exact ⟨ℓ', (pure_sep_iff.mp hs₁).1.1⟩
        have hlt : WitLt ℓ' χ n := fun s u σ' h hχ =>
          lt_of_lt_of_le (dsize_image_lt hobs hreb hview s u σ' h hχ) (Nat.lt_succ_iff.mp hKσ)
        refine wpTS_sum₂ _ _ _ _ _ _ ?_
        have e₂ : (bindE (.app (.app (.val selfC) (.val .unit)) (.var 0)) (.inj₂ (.var 0))).subst 0
            (Val.loc ℓ') = (Kont.appR (.val (.lam (.inj₂ (.var 0)))) .hole).plug
              (.app (.app (.val selfC) (.val .unit)) (.val (.loc ℓ'))) := by
          simp [bindE, Expr.subst, val_subst_closed selfC_closed, Kont.plug]
        rw [e₂]
        refine wpTS_bind _ _ _ _ _ ?_
        refine wpTS_selfV_in cfB_closed (.appL .hole (.loc ℓ')) Val.unit ls _ χ ?_
        rw [fixV_eq cfB_closed]
        refine wpTS_beta_in (.appL .hole (.loc ℓ')) _ Val.unit ls _ χ ?_
        rw [cfB_subst selfC_closed]
        refine wpTS_lolli _ _ _ _ _ ?_
        rw [bodyL_subst selfC_closed]
        refine wpTS_mono (fun ls' v ρ' hv => ?_) χ (ih (.var 0) (δ.extend 0 β) ls ℓ' χ ht hlt)
        obtain ⟨rfl, k, rfl⟩ := vC_natN hv
        refine wpTS_lolli _ _ _ _ _ ?_
        exact wpTS_val ls' (num (k + 1)) _ _ ⟨vC_num true ls' δ (k + 1), ResU.inStratum_empty β⟩

/-- Every borrow's cell witness has a size. -/
theorem witLt_exists {a : Lifetime.Life} {T : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc}
    {ρ : WRes} (hv : vP (.imm a T) ls δ (.loc ℓ) ρ) : ∃ n, WitLt ℓ ρ n := by
  obtain ⟨α₀, -, ℓ', hs⟩ := hv
  obtain ⟨-, himm⟩ := pure_sep_iff.mp hs
  obtain ⟨s, u, σ, hσ, hρ, -⟩ := ptoImmO_toImm himm
  refine ⟨dsize σ + 1, fun s' u' σ' h' hρ' => ?_⟩
  have e : (ResU.single ℓ' (CellU.immOf s u σ hσ)).get ℓ' = ρ.get ℓ' := by rw [hρ]
  rw [hρ'] at e
  by_cases hl : ℓ' = ℓ
  · subst hl
    simp only [ResU.single_get_self] at e
    obtain ⟨-, -, hσσ⟩ := CellU.immOf_inj (Option.some.inj e)
    rw [← hσσ]; exact Nat.lt_succ_self _
  · have : (ResU.single ℓ (CellU.immOf s' u' σ' h')).get ℓ' = none := by
      simp [ResU.single, hl]
    rw [this] at e; simp at e

/-- `λl. withload l (cbV selfC)` is a value of `U(Imm 'a L ⊸ F N)` at every `'a`. -/
theorem countFree_lam_vC (δ : LSub) (ls : List SRec) :
    vC true (.lolli (.imm (.var 0) listL) natN) ls δ (.lam (bodyL selfC)) PMap.empty := by
  intro ls₁ _ v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, v = Val.loc ℓ := by
    obtain ⟨α₀, -, ℓ, hs₁⟩ := hv
    exact ⟨ℓ, (pure_sep_iff.mp hs₁).1.1⟩
  refine wpTS_lolli _ _ _ _ _ ?_
  rw [bodyL_subst selfC_closed]
  obtain ⟨n, hn⟩ := witLt_exists hv
  exact countFree_body n (.var 0) δ ls₁ ℓ ρ₁ hv hn

/-- `countFree` is a value of `!U(∀'a. Imm 'a L ⊸ F N)` at `∅`. -/
theorem countFree_vC (δ : LSub) (ls : List SRec) :
    vC true countTy ls δ countFreeV PMap.empty := by
  refine ⟨rfl, ?_⟩
  intro ls₁ _ α ρ₁ ρ₂ hp hc
  obtain ⟨rfl, -⟩ := hp
  rw [eq_of_compS_empty_left hc]
  show wpTS ls₁ (.app (.val countFreeV) (.val .unit)) _ PMap.empty
  rw [countFreeV, fixV_eq cfB_closed]
  refine wpTS_lolli _ _ _ _ _ ?_
  rw [cfB_subst selfC_closed]
  exact wpTS_val _ _ _ _ (countFree_lam_vC _ _)

/-- **`countFree : !U(∀'a. Imm 'a L ⊸ F N)`**, the semantic judgment, with no fuel. -/
theorem countFree_semV {Δ : LifeCtx} : SemV Δ [] (.val countFreeV) countTy :=
  semV_closed countFreeV_closed countFree_vC

/-! ### The program -/

/-- The program, open in `countFree` (index `0`) and `freeAll` (index `1`):

    build3 to lst. alloc lst to r. return countFree to g.
    withbor r (Λ. λb. g [] b to n. n) to p. let (r′, n) = p in
    free r′ to lst′. freeAll lst′ to u. u; n                                            -/
def countFreeProgOpen : Expr :=
  bindE build3 (bindE (.app (.val (.prim .alloc)) (.var 0))
    (bindE (.var 2)
      (bindE (.app (.app withbor (.var 1)) borrowerE)
        (.letpair (.var 0)
          (bindE (.app (.val (.prim .free)) (.var 1))
            (bindE (.app (.var 8) (.var 0)) (.seq (.var 0) (.var 2))))))))

/-- The context of `countFree` and `freeAll`. -/
abbrev ΓC : Ctx VTy := [⟨countTy, true⟩, ⟨.lolli listL .unit, true⟩]

theorem countFreeProg_derives :
    CDerives LifeCtx.empty ΓC countFreeProgOpen (.comp (.ret natN)) := by
  -- `build3 to lst`
  refine .bind (.right (.right .nil)) (.ret (d_build3 (.cons (.cons .nil)))) ?_
  -- `alloc lst to r`
  refine .bind (.left (.right (.right .nil)))
    (.ret (.lolliE (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil))))
      (.alloc (A := listL) (.cons (.cons (.cons .nil)))))) ?_
  -- `return countFree to g`
  refine .bind (.right (.dead (.left (.right .nil))))
    (.ret (.var (.there (.there (.here (.cons .nil)))))) ?_
  -- `withbor r borrower to p`
  refine .bind (.left (.left (.dead (.dead (.right .nil)))))
    (.ret (.lolliE (.left (.right (.dead (.dead (.dead .nil)))))
      (d_borrowerE (by repeat constructor))
      (.lolliE (.dead (.left (.dead (.dead (.dead .nil)))))
        (.var (.there (.here (by repeat constructor))))
        (.withbor1 (A := listL) (B := natN) 0 (by repeat constructor) rfl
          (fun _ h => by simp [VFree, listL, listBody] at h)
          (by simp [VFree, listL, listBody]) (by simp [VFree, natN, natBody]))))) ?_
  -- `let (r′, n) = p in`
  refine .tensorE (A := .ref listL) (B := natN)
    (.left (.dead (.dead (.dead (.dead (.right .nil))))))
    (.var (.here (by repeat constructor))) ?_
  -- `free r′ to lst′`
  refine .bind (.right (.left (.dead (.dead (.dead (.dead (.dead (.right .nil))))))))
    (.ret (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))
      (.var (.there (.here (by repeat constructor))))
      (.free (A := listL) (by repeat constructor)))) ?_
  -- `freeAll lst′ to u`
  refine .bind (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.left .nil)))))))))
    (.ret (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.right .nil)))))))))
      (.var (.here (by repeat constructor)))
      (.var (.there (.there (.there (.there (.there (.there (.there (.there
        (.here .nil)))))))))))) ?_
  -- `u; n`
  exact .unitE (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.var (.here (by repeat constructor)))
    (.ret (.var (.there (.there (.here (by repeat constructor))))))

/-- The program, closed by `countFree` and `freeAll`. -/
def countFreeProg : Expr := substAll [countFreeV, freeAll] countFreeProgOpen

theorem gDenC_C (ls : List SRec) (δ : LSub) : gDenC ls δ ΓC [countFreeV, freeAll] PMap.empty :=
  gDenC_mk (by simp [Ctx.LiveWithin])
    ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, countFree_vC δ ls,
      PMap.empty, PMap.empty, ResU.comp_empty_right _, freeAll_vC δ ls, ⟨rfl, trivial⟩⟩

theorem countFreeProg_wp :
    wpTS [] countFreeProg (fun _ v => Fig16.BoLo.pure (∃ k, v = num k)) (PMap.empty : WRes) := by
  have h := fundamentalC countFreeProg_derives LSub.empty [countFreeV, freeAll] [] PMap.empty
    Adequacy.models_empty (gDenC_C [] LSub.empty)
  refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty h
  obtain ⟨rfl, k, rfl⟩ := vC_natN hv
  exact ⟨rfl, k, rfl⟩

/-- **Adequacy at the fuel-free count**: the program runs from the empty memory to a numeral and
the empty memory. -/
theorem countFreeProg_runs :
    ∃ k, BoCa.BoLo.Steps Adequacy.emptyMem countFreeProg Adequacy.emptyMem (.val (num k)) := by
  obtain ⟨v, hsteps, k, rfl⟩ := theorem32 countFreeProg (fun v => ∃ k, v = num k) countFreeProg_wp
  exact ⟨k, hsteps⟩

/-- The executable interpreter counts `3` and leaves no cell. -/
theorem countFreeProg_eval : numNoLeak (eval countFreeProg) = some 3 := by decide

end BoCa.Fig16.LogRel.CBPVMu

end
