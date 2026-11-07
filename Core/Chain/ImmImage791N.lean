import Core.Chain.Goal791N0

/-!
# The observable view and the image of a reborrow at `vN₀`  `[spec §62]`

`withload_compatX`'s steps 5, 7 and 8 (`chain-interpretation.md` §6.3) at `vN₀`'s `Imm` clause, which
reads its payload in the observable view `vO₀` (Core's `vCE false`) and its location's witness in
the world's `imm` records (`ImmWitW`, Core's `CohE`):

* `vN_vO₀`: a value is observable (Core's `vC` at `true` read at `false`);
* `vN_vShape₀`, `vO_vShape₀`: the shape of a value (Core's `vC_vShape`);
* `vO_transfer₀`: the observable view transfers between two pieces of one escrow (Core's
  `obs_transfer`);
* `relabel_vN₀`: an image of an escrow re-taken at `β` is a value of `Imm̲ 'x A` at `δ['x ↦ β]`
  (Core's `relabel_obs`), the witnesses of the image's new cells supplied at the escrow's `Ref`
  and `Mut` positions;
* `RefPos.tyEq`, `MutPos.tyEq`: positions read across `TyEq`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### A value is observable -/

/-- **A value is in the observable view** (`U` read as `True`; Core's `vO_obs`, by `vN_ind₀`). -/
theorem vN_vO₀ : ∀ (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    vN₀ (ℍ := ℍ) A δ Θ n v ρ → vO₀ (ℍ := ℍ) A δ Θ n v ρ := by
  intro A δ Θ n v ρ h
  refine vN_ind₀ δ (fun _ T Θ n v ρ => vO₀ (ℍ := ℍ) T δ Θ n v ρ) ?_ true A Θ n v ρ h
  intro b T Θ n v ρ h
  cases T with
  | unit => exact h
  | int w => exact h
  | opq k => exact h
  | unk => exact h
  | zero => exact h.elim
  | tvar _ => exact h.elim
  | thunk _ => trivial
  | tensor A B =>
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃.2, h₄.2⟩
  | sum A B =>
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, h₂.2⟩
      · exact .inr ⟨v₂, h₁, h₂.2⟩
  | ref A =>
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, h₃.2⟩
  | imm a A =>
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
      exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄.1⟩, hw⟩
  | «mut» a A => cases b <;> exact h.1
  | box a A =>
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, h₁.2, h₂⟩
  | bang A => exact ⟨h.1, h.2.1⟩
  | mu A => exact vBN_roll₀ (b := false) h.1 h.2.1 h.2.2.2
  | fam L =>
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono' (fun m σ hm => hm.2) h₃⟩

/-- Extending `δ` at a variable `A` does not mention leaves `vO₀⟦A⟧` alone. -/
theorem vO_extend_of_not_free₀ {x : LifeVar} {A : VTy} (h : ¬ VFree x A) (δ : LSub) (α : Life) :
    vO₀ (ℍ := ℍ) A (δ.extend x α) = vO₀ (ℍ := ℍ) A δ :=
  vO_congr₀ A fun y hy => BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact h hy)

/-- `vN₀` and `vO₀` agree at `Imm`. -/
theorem vN_imm_eq₀ (a : Lifetime.Life) (A : VTy) :
    vN₀ (ℍ := ℍ) (.imm a A) = vO₀ (ℍ := ℍ) (.imm a A) := rfl

/-! ### The shape of a value -/

/-- **A value has its type's shape, in both modes** (Core's `vC_vShape`, by `vN_ind₀`). -/
theorem vBN_vShape₀ (b : Bool) (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes)
    (h : vBN₀ (ℍ := ℍ) none b A δ Θ n v ρ) : vShape A δ v ρ := by
  refine vN_ind₀ δ (fun _ T _ _ v ρ => vShape T δ v ρ) ?_ b A Θ n v ρ h
  intro b T Θ n v ρ h
  cases T with
  | unit => obtain ⟨hv, hρ⟩ := h; subst hρ; exact ⟨rfl, hv⟩
  | int w => obtain ⟨hv, hρ⟩ := h; subst hρ; exact ⟨rfl, hv⟩
  | opq k => exact h
  | unk => subst h; exact ⟨rfl, trivial⟩
  | zero => exact h.elim
  | tvar _ => exact h.elim
  | thunk _ => trivial
  | tensor A B =>
      obtain ⟨v₁, v₂, ρ₁, ρ₂, rfl, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, h₂, h₃.2, h₄.2⟩⟩
  | sum A B =>
      rcases h with ⟨v₁, rfl, h₂⟩ | ⟨v₂, rfl, h₂⟩
      · exact .inl ⟨v₁, pure_sep_mk rfl h₂.2⟩
      · exact .inr ⟨v₂, pure_sep_mk rfl h₂.2⟩
  | ref A =>
      obtain ⟨l, u, σ, rfl, h₂, h₃⟩ := h
      exact ⟨l, u, pure_sep_mk rfl ⟨_, σ, h₂, rfl, h₃.2⟩⟩
  | imm a A =>
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, rfl, rfl, h₃, h₄⟩, -⟩ := h
      exact ⟨α, hα, l, pure_sep_mk rfl ⟨s, u, σ, hs, rfl, h₄.2, h₃⟩⟩
  | «mut» a A =>
      obtain ⟨hm, hsub⟩ := h
      have hm' : vN₀ (ℍ := ℍ) (.mut a A) δ Θ n v ρ := by cases b <;> exact hm
      obtain ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, -, rfl, -, rfl⟩, -⟩ := hm'
      refine ⟨α, hα, l, pure_sep_mk rfl ⟨ofS (famL b (fun Θ' j u r => vN₀ (ℍ := ℍ) A δ Θ' j u r) Θ j),
        ⟨b, w, χ, hχ, _, hw, hab, rfl, rfl⟩, fun u σ hu => ?_⟩⟩
      obtain ⟨h', hu'⟩ := hu
      exact (hsub _ j u σ hu').2
  | box a A =>
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, h₁.2, h₂⟩
  | bang _ =>
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, trivial⟩
  | mu A => exact vShape_roll h.2.1 h.2.2.2
  | fam L =>
      obtain ⟨l, c, rfl, -, h₃⟩ := h
      exact ⟨l, c, pure_sep_mk rfl (sepRange_mono' (fun m σ hm => hm.2) h₃)⟩

/-- **A value has its type's shape** (Core's `vC_vShape`). -/
theorem vN_vShape₀ (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes)
    (h : vN₀ (ℍ := ℍ) A δ Θ n v ρ) : vShape A δ v ρ :=
  vBN_vShape₀ true A δ Θ n v ρ h

/-- **An observable value has its type's shape.** -/
theorem vO_vShape₀ (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes)
    (h : vO₀ (ℍ := ℍ) A δ Θ n v ρ) : vShape A δ v ρ :=
  vBN_vShape₀ false A δ Θ n v ρ h

/-! ### The observable view transfers between pieces of one escrow -/

/-- `Val.loc` is injective. -/
theorem loc_inj {l l' : Loc} (h : Val.loc l = Val.loc l') : l = l' := by
  have := congrArg Subtype.val h; simpa [Val.loc] using this

/-- **Every `imm` cell of `B` is no longer-lived than every world record coherent at its
location**: Core's `FrameLife` (a record's lineage views have lifetimes ⊑ its tag) read at the
cells of `B` and the world's records. A run's typed world supplies it at its entry
(`Withload791N.lifeBoundW_of_entry`). -/
def LifeBoundOn (I : List SRec) (P : Loc → Prop) (B : WRes) : Prop :=
  ∀ m t u σ h, B.get m = some (CellU.immOf t u σ h) → P m → ∀ x ∈ I, ∀ d, DescR x.1 d →
    ∀ S δ₀, CohE [d] m S δ₀ → ∀ y, t.mem y → y ≤ x.2

/-- `LifeBoundOn` at every location. -/
abbrev LifeBoundW (I : List SRec) (B : WRes) : Prop := LifeBoundOn I (fun _ => True) B

/-- A piece of an `imm` cell has fewer lifetimes. -/
theorem imm_piece_left {B₁ B₂ B : WRes} (hc : ResU.CompS B₁ B₂ B) {m : Loc} {t : LSet}
    {u : Val} {σ : WRes} {hσ : σ.InStratum t.join} (e : B₁.get m = some (CellU.immOf t u σ hσ)) :
    ∃ (t' : LSet) (h' : σ.InStratum t'.join), B.get m = some (CellU.immOf t' u σ h') ∧
      ∀ y, t.mem y → t'.mem y := by
  rcases ResU.Comp.get hc m with ⟨f₁, -, -⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, f₁, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, -, f, hC⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁
    exact ⟨t, hσ, f, fun _ h => h⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, rfl, rfl⟩ := hC
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₁
    exact ⟨_, h₃, f, fun _ h => Or.inl h⟩

theorem LifeBoundOn.left {I : List SRec} {P : Loc → Prop} {B₁ B₂ B : WRes}
    (hc : ResU.CompS B₁ B₂ B) (h : LifeBoundOn I P B) : LifeBoundOn I P B₁ := by
  intro m t u σ hσ e hP x hx d hd S δ₀ hco y hy
  obtain ⟨t', h', e', ht⟩ := imm_piece_left hc e
  exact h m t' u σ h' e' hP x hx d hd S δ₀ hco y (ht y hy)

theorem LifeBoundOn.right {I : List SRec} {P : Loc → Prop} {B₁ B₂ B : WRes}
    (hc : ResU.CompS B₁ B₂ B) (h : LifeBoundOn I P B) : LifeBoundOn I P B₂ := h.left hc.comm

/-- **Every cell of `c` at an `own` location of `R` has its witness bounded** (`LifeBoundW`). -/
def LifeBoundWit (I : List SRec) (R c : WRes) : Prop :=
  ∀ m ψ, c.get m = some ψ → (∃ u, R.get m = some (CellU.ownOf u)) → LifeBoundW I ψ.wit

theorem LifeBoundWit.left {I : List SRec} {R c₁ c₂ c : WRes} (hc : ResU.CompS c₁ c₂ c)
    (h : LifeBoundWit I R c) : LifeBoundWit I R c₁ := by
  intro m ψ e hR
  obtain ⟨ψ', e', -, w', -⟩ := compS_get_left' hc e
  rw [← w']
  exact h m ψ' e' hR

/-- **The observable view transfers between two pieces of one escrow** (Core's `obs_transfer`):
`A` observable at `T`, `B` shaped at `T`, both cell-matching `R`, gives `B` observable at `T`.
At a `U` position both sides are `True`; at an `Imm` or `Mut` position the cell is read off `R`'s,
and an `Imm` cell's witness is its location's, which the two pieces share; `B`'s cell is no
longer-lived than it (`LifeBoundW`). -/
theorem vO_transfer₀ {R : WRes} : ∀ (T : VTy) {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {A B : WRes}, CellMatch R A → CellMatch R B → LifeBoundW Θ.imm B →
    vO₀ (ℍ := ℍ) T δ Θ n v A → vShape T δ v B → vO₀ (ℍ := ℍ) T δ Θ n v B := by
  intro T δ Θ n v A B hA hB hL h hs
  refine vN_ind₀ δ (fun b T Θ n v A => b = false → ∀ B, CellMatch R A → CellMatch R B →
      LifeBoundW Θ.imm B → vShape T δ v B → vO₀ (ℍ := ℍ) T δ Θ n v B) ?_ false T Θ n v A h rfl B
    hA hB hL hs
  intro b T Θ n v A h hb B hA hB hL hs
  subst hb
  cases T with
  | unit => obtain ⟨hB, hv⟩ := hs; exact ⟨hv, hB⟩
  | int _ => obtain ⟨hB, hv⟩ := hs; exact ⟨hv, hB⟩
  | unk => exact hs.1
  | opq _ => exact hs
  | zero => exact h.elim
  | thunk _ => trivial
  | tvar _ => exact h.elim
  | mu M =>
      obtain ⟨hnm, hcl, hG⟩ := h
      exact vBN_roll₀ (b := false) hnm hcl (hG.2 rfl B hA hB hL (vShape_unfold hs).2)
  | fam L =>
      obtain ⟨l, c, he, hn, hsA⟩ := h
      obtain ⟨l', c', hk'⟩ := hs
      obtain ⟨he', hsB⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.arr_inj (he.symm.trans he')
      exact ⟨l, c, he, hn, sepRange_zip (RA := CellMatch R)
        (RB := fun B => CellMatch R B ∧ LifeBoundW Θ.imm B) (f := id)
        (fun _ _ _ hc h => ⟨h.left hc, h.right hc⟩)
        (fun _ _ _ hc h => ⟨⟨h.1.left hc, LifeBoundOn.left hc h.2⟩,
          ⟨h.1.right hc, LifeBoundOn.right hc h.2⟩⟩)
        (fun _ _ _ hc => hc) rfl
        (fun m _ _ a b ha hb hPa hQb => hPa.2 rfl b ha hb.1 hb.2 hQb) hA ⟨hB, hL⟩ hsA hsB⟩
  | tensor T₁ T₂ =>
      obtain ⟨v₁, v₂, A₁, A₂, rfl, hcA, h₁, h₂⟩ := h
      obtain ⟨w₁, w₂, hk⟩ := hs
      obtain ⟨he, B₁, B₂, hcB, g₁, g₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      exact ⟨v₁, v₂, B₁, B₂, rfl, hcB,
        h₁.2 rfl B₁ (hA.left hcA) (hB.left hcB) (LifeBoundOn.left hcB hL) g₁,
        h₂.2 rfl B₂ (hA.right hcA) (hB.right hcB) (LifeBoundOn.right hcB hL) g₂⟩
  | sum T₁ T₂ =>
      rcases h with ⟨a, rfl, h₁⟩ | ⟨a, rfl, h₁⟩ <;> rcases hs with ⟨b, hk⟩ | ⟨b, hk⟩
      · obtain ⟨he, g⟩ := pure_sep_iff.mp hk
        cases Val.inj₁_inj' he
        exact .inl ⟨a, rfl, h₁.2 rfl B hA hB hL g⟩
      · exact absurd (pure_sep_iff.mp hk).1 (Val.inj₁_ne_inj₂)
      · exact absurd (pure_sep_iff.mp hk).1 (fun e => Val.inj₁_ne_inj₂ e.symm)
      · obtain ⟨he, g⟩ := pure_sep_iff.mp hk
        cases Val.inj₂_inj' he
        exact .inr ⟨a, rfl, h₁.2 rfl B hA hB hL g⟩
  | box a T =>
      obtain ⟨α, hα, h₁, -⟩ := h
      obtain ⟨α', hα', hs₁, ho'⟩ := hs
      exact ⟨α', hα', h₁.2 rfl B hA hB hL hs₁, ho'⟩
  | bang T =>
      obtain ⟨rfl, hT⟩ := h
      obtain ⟨rfl, -⟩ := hs
      exact ⟨rfl, hT.1⟩
  | ref S =>
      obtain ⟨l, u, σ, rfl, hab, hS⟩ := h
      obtain ⟨l', u', hk⟩ := hs
      obtain ⟨hl', σa, σb, hab', hown', hSb⟩ := pure_sep_iff.mp hk
      obtain rfl := loc_inj hl'
      have hown₂ : σa = ResU.single l (CellU.ownOf u') := hown'
      subst hown₂
      have eA := compS_get_left_nonImm hab (ResU.single_get_self _ _) (by simp)
      have eB := compS_get_left_nonImm hab' (ResU.single_get_self _ _) (by simp)
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hA l _ eA
      obtain ⟨ζ', eζ', -, -, -, hζ'⟩ := hB l _ eB
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      have huu : u = u' := by
        have := congrArg CellU.erase ((hζ (by simp)).symm.trans (hζ' (by simp)))
        simpa using this
      subst huu
      exact ⟨l, u, σb, rfl, hab', hS.2 rfl σb (hA.right hab) (hB.right hab') (LifeBoundOn.right hab' hL) hSb⟩
  | imm a S =>
      obtain ⟨α, hα, ⟨l, s, u, σ, hσ, rfl, rfl, hαs, hP⟩, hW⟩ := h
      obtain ⟨α', hα', l', hk⟩ := hs
      obtain ⟨hl', t, w, W, hWt, rfl, -, hα't⟩ := pure_sep_iff.mp hk
      obtain rfl : l = l' := loc_inj hl'
      rw [hα] at hα'; cases Option.some.inj hα'
      obtain ⟨ζ, eζ, kζ, wζ, rζ, -⟩ := hA l _ (ResU.single_get_self _ _)
      obtain ⟨ζ', eζ', -, wζ', rζ', -⟩ := hB l _ (ResU.single_get_self _ _)
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      simp only [CellU.wit_immOf, CellU.erase_immOf] at wζ rζ wζ' rζ'
      have hW' : W = σ := wζ'.symm.trans wζ
      have hw' : w = u := rζ'.symm.trans rζ
      subst hW' hw'
      refine ⟨α, hα, ⟨l, t, w, W, hWt, rfl, rfl, hα't, hP.1⟩, fun l₀ t₀ u₀ σ₀ h₀ e => ?_⟩
      obtain ⟨rfl, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -, -⟩ := CellU.immOf_inj e'
      obtain ⟨x, hx, -, d, hd, hco⟩ := hW l s w W hσ rfl
      obtain ⟨S₀, δ₀, he, hc⟩ := hco
      exact ⟨x, hx, hL l t w W hWt (ResU.single_get_self _ _) trivial x hx d hd S δ ⟨S₀, δ₀, he, hc⟩
        t.meet t.meet_mem, d, hd, S₀, δ₀, he, hc⟩
  | «mut» a S =>
      obtain ⟨⟨α, hα, b, hab, hm, hu⟩, -⟩ := h
      obtain ⟨l, w, χ, hχ, j, hw, hnj, rfl, hl, rfl⟩ := id hm
      obtain ⟨α', -, l', hk⟩ := hs
      obtain ⟨hl', P, ⟨b', w', χ', hχ', Q', hw', -, rfl, -⟩, -⟩ := pure_sep_iff.mp hk
      obtain rfl := loc_inj hl'
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hA l _ (ResU.single_get_self _ _)
      obtain ⟨ζ', eζ', -, -, -, hζ'⟩ := hB l _ (ResU.single_get_self _ _)
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      have e := (hζ (by simp)).symm.trans (hζ' (by simp))
      rw [← e]
      exact ⟨α, hα, b, hab, hm, hu⟩

/-! ### The image of a reborrow, re-taken at `β`, at `vN₀` -/

/-- `Imm̲` at a closed `μ` is read at the reborrow of the unrolling (Core's
`vC_immReborrow_mu_iff`). -/
theorem vN_immReborrow_mu_iff₀ {A : VTy} (hA : A.Cl 1) (c : Lifetime.Life) {δ : LSub} {Θ : LocTy}
    {n : Nat} {v : Val} {ρ : WRes} :
    vN₀ (ℍ := ℍ) ((VTy.mu A).immReborrow c) δ Θ n v ρ ↔
      vN₀ (ℍ := ℍ) ((VTy.inst (.mu A) A).immReborrow c) δ Θ n v ρ := by
  rw [VTy.immReborrow_mu c hA, VTy.immReborrow_unroll' c hA, vN_mu_iff₀]
  exact ⟨fun h => h.2.2, fun h => ⟨VTy.noMut_immX c hA 0, VTy.Cl_immX c hA, h⟩⟩

/-- **An image re-taken at `β` is a value of `Imm̲ 'x T` at `δ['x ↦ β]`** (Core's `relabel_obs`,
at `vN₀`): an old image `c` shaped at `Imm̲ 'x₀ T` at `δ['x₀ ↦ β₀]`, over an escrow `R` whose part
`Rl` at the position is observable at `T`; the new cells at the `Ref` and `Mut` positions are
witnessed in the world's `imm` records (`hcr`, `hcm`). At a `Ref`/`Mut` position the new cell's
payload is observable because the old image's witness is a piece of the escrow (`vO_transfer₀`) or
the `mut` cell's content (its stored family); at an `Imm` position the kept cell is the escrow's
(`vO_transfer₀` at the cell). -/
theorem relabel_vN₀ {R : WRes} {Θ : LocTy} {n : Nat} {β β₀ : Life} {δ : LSub} {x x₀ : LifeVar} :
    ∀ (T : VTy), ¬ VFree x T → ¬ VFree x₀ T → ∀ {v : Val} {c Rl : WRes},
      vShape (T.immReborrow (.var x₀)) (δ.extend x₀ β₀) v c →
      vO₀ (ℍ := ℍ) T δ Θ n v Rl → CellMatch R Rl →
      (∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
          (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) →
      (∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
        ψ.wit.InStratum (LSet.singleton β).join) →
      LifeBoundOn Θ.imm (fun m => ∃ ζ, R.get m = some ζ ∧ ζ.kind = Kind.imm) c →
      LifeBoundWit Θ.imm R c →
      (∀ m S u, RefPos T v m S → R.get m = some (CellU.ownOf u) →
        ImmWitW Θ.imm m (LSet.singleton β) S (δ.extend x β)) →
      (∀ m S, MutPos T v m S → ImmWitW Θ.imm m (LSet.singleton β) S (δ.extend x β)) →
      vN₀ (ℍ := ℍ) (T.immReborrow (.var x)) (δ.extend x β) Θ n v (relRes R β c) := by
  intro T hx hx₀ v c Rl hc hR hRl hcR hs hLk hLo hcr hcm
  refine vN_ind₀ δ (fun b T Θ n v Rl => b = false → ¬ VFree x T → ¬ VFree x₀ T →
      ∀ c, vShape (T.immReborrow (.var x₀)) (δ.extend x₀ β₀) v c → CellMatch R Rl →
      (∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
          (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) →
      (∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
        ψ.wit.InStratum (LSet.singleton β).join) →
      LifeBoundOn Θ.imm (fun m => ∃ ζ, R.get m = some ζ ∧ ζ.kind = Kind.imm) c →
      LifeBoundWit Θ.imm R c →
      (∀ m S u, RefPos T v m S → R.get m = some (CellU.ownOf u) →
        ImmWitW Θ.imm m (LSet.singleton β) S (δ.extend x β)) →
      (∀ m S, MutPos T v m S → ImmWitW Θ.imm m (LSet.singleton β) S (δ.extend x β)) →
      vN₀ (ℍ := ℍ) (T.immReborrow (.var x)) (δ.extend x β) Θ n v (relRes R β c)) ?_
    false T Θ n v Rl hR rfl hx hx₀ c hc hRl hcR hs hLk hLo hcr hcm
  intro b T Θ n v Rl hR hb hx hx₀ c hc hRl hcR hs hLk hLo hcr hcm
  subst hb
  have hRv : vO₀ (ℍ := ℍ) T δ Θ n v Rl :=
    (vFN_vN₀ δ false T Θ n v Rl).mpr (vFN_mono₀ (fun _ _ _ _ _ _ h => h.1) δ false T Θ n v Rl hR)
  cases T with
  | unit =>
      obtain ⟨rfl, hv⟩ := hc; rw [relRes_empty]; exact ⟨hv, rfl⟩
  | int _ =>
      obtain ⟨rfl, hv⟩ := hc; rw [relRes_empty]; exact ⟨hv, rfl⟩
  | opq _ =>
      obtain ⟨rfl, -⟩ := hc; rw [relRes_empty]; rfl
  | thunk _ =>
      obtain ⟨rfl, -⟩ := hc; rw [relRes_empty]; rfl
  | unk =>
      obtain ⟨rfl, -⟩ := hc; rw [relRes_empty]; rfl
  | zero => exact hc.elim
  | tvar _ => exact hR.elim
  | mu M =>
      obtain ⟨-, hcl, hG⟩ := hR
      have hM : M.Cl 1 := hcl
      refine (vN_immReborrow_mu_iff₀ hM _).mpr ?_
      exact hG.2 rfl (fun h => (vFree_inst h).elim hx hx) (fun h => (vFree_inst h).elim hx₀ hx₀)
        _ ((vShape_immReborrow_mu_iff hM _ _ v c).mp hc) hRl hcR hs hLk hLo
        (fun m S u h => hcr m S u (RefPos.mu hcl h)) (fun m S h => hcm m S (MutPos.mu hcl h))
  | fam L =>
      obtain ⟨ℓ, k, hk₁⟩ := hc
      obtain ⟨he, hs₁⟩ := pure_sep_iff.mp hk₁
      obtain ⟨ℓ', k', he', hn, hs₂⟩ := hR
      subst he
      obtain ⟨rfl, rfl⟩ := Val.arr_inj he'
      refine ⟨ℓ, k, rfl, hn, ?_⟩
      exact sepRange_zip (RA := CellMatch R)
        (RB := fun c => (∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
          (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) ∧
          (∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
            ψ.wit.InStratum (LSet.singleton β).join) ∧
          LifeBoundOn Θ.imm (fun m => ∃ ζ, R.get m = some ζ ∧ ζ.kind = Kind.imm) c ∧
          LifeBoundWit Θ.imm R c)
        (f := relRes R β)
        (fun _ _ _ hc h => ⟨h.left hc, h.right hc⟩)
        (fun _ _ _ hc h => ⟨⟨rebMatch_left hc h.1, strat_left hc h.2.1, LifeBoundOn.left hc h.2.2.1,
            LifeBoundWit.left hc h.2.2.2⟩,
          ⟨rebMatch_left hc.comm h.1, strat_left hc.comm h.2.1, LifeBoundOn.right hc h.2.2.1,
            LifeBoundWit.left hc.comm h.2.2.2⟩⟩)
        (fun _ _ _ hc => relRes_compS hc) (relRes_empty R β)
        (fun m hm hm' a b ha hb hPa hQb => hPa.2 rfl hx hx₀ _ hQb ha hb.1 hb.2.1 hb.2.2.1
          hb.2.2.2 (fun m' S u h => hcr m' S u (RefPos.fam_at hm hm' h))
          (fun m' S h => hcm m' S (MutPos.fam_at hm hm' h)))
        hRl ⟨hcR, hs, hLk, hLo⟩ hs₂ hs₁
  | sum T₁ T₂ =>
      rcases hc with ⟨a, hk₁⟩ | ⟨a, hk₁⟩ <;> rcases hR with ⟨b, hb, h₁'⟩ | ⟨b, hb, h₁'⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk₁
        subst he; cases Val.inj₁_inj' hb
        exact .inl ⟨a, rfl, h₁'.2 rfl (fun h => hx (Or.inl h)) (fun h => hx₀ (Or.inl h)) _ h₁
          hRl hcR hs hLk hLo (fun m S u h => hcr m S u (RefPos.sumL h))
          (fun m S h => hcm m S (MutPos.sumL h))⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        subst he; exact (Val.inj₁_ne_inj₂ hb).elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        subst he; exact (Val.inj₁_ne_inj₂ hb.symm).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk₁
        subst he; cases Val.inj₂_inj' hb
        exact .inr ⟨a, rfl, h₁'.2 rfl (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) _ h₂
          hRl hcR hs hLk hLo (fun m S u h => hcr m S u (RefPos.sumR h))
          (fun m S h => hcm m S (MutPos.sumR h))⟩
  | tensor T₁ T₂ =>
      obtain ⟨a, b, hk₁⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, h₁, h₂⟩ := pure_sep_iff.mp hk₁
      obtain ⟨a', b', R₁, R₂, he', hRR, h₁', h₂'⟩ := hR
      subst he
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      exact ⟨a, b, _, _, rfl, relRes_compS hcc,
        h₁'.2 rfl (fun h => hx (Or.inl h)) (fun h => hx₀ (Or.inl h)) _ h₁ (hRl.left hRR)
          (rebMatch_left hcc hcR) (strat_left hcc hs) (LifeBoundOn.left hcc hLk) (LifeBoundWit.left hcc hLo)
          (fun m S u h => hcr m S u (RefPos.tensorL h)) (fun m S h => hcm m S (MutPos.tensorL h)),
        h₂'.2 rfl (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) _ h₂ (hRl.right hRR)
          (rebMatch_left hcc.comm hcR) (strat_left hcc.comm hs) (LifeBoundOn.right hcc hLk)
          (LifeBoundWit.left hcc.comm hLo)
          (fun m S u h => hcr m S u (RefPos.tensorR h)) (fun m S h => hcm m S (MutPos.tensorR h))⟩
  | box a T =>
      obtain ⟨α, -, hb, -⟩ := hR
      exact hb.2 rfl (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) _ hc hRl hcR hs hLk hLo
        (fun m S u h => hcr m S u (RefPos.box h)) (fun m S h => hcm m S (MutPos.box h))
  | bang S =>
      obtain ⟨rfl, -⟩ := hc
      obtain ⟨rfl, hS⟩ := hR
      rw [relRes_empty]
      exact ⟨rfl, vN_cast₀ (vN_extend_of_not_free₀ (A := S) hx δ β).symm hS.1⟩
  | ref S =>
      obtain ⟨α, hα, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, hWd, -⟩ := pure_sep_iff.mp hk₁
      obtain ⟨l'', u, ρb, hl', hab, hRb⟩ := hR
      obtain rfl : l' = l'' := loc_inj (hl.symm.trans hl')
      subst hl
      have eRl := compS_get_left_nonImm hab (ResU.single_get_self _ _) (by simp)
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hRl l' _ eRl
      have hζ' : ζ = CellU.ownOf u := hζ (by simp)
      subst hζ'
      obtain ⟨ζ₂, eζ₂, her, -, hcw⟩ := hcR l' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      simp only [CellU.erase_immOf, CellU.erase_ownOf] at her
      subst her
      have hWm : CellMatch R W := by
        have := hcw (by simp); rwa [CellU.wit_immOf] at this
      have kne : (CellU.ownOf (Loc := Loc) w).kind ≠ Kind.imm := by simp
      have hβ := hs l' _ (ResU.single_get_self _ _) ⟨_, eζ, kne⟩
      rw [CellU.wit_immOf] at hβ
      rw [relRes_single, relCell_fire eζ kne hβ]
      have hS₀ : ¬ VFree x₀ S := hx₀
      rw [vShape_extend_of_not_free hS₀] at hWd
      have hobs : vO₀ (ℍ := ℍ) S δ Θ n w W :=
        vO_transfer₀ S (hRl.right hab) hWm (by
          have := hLo l' _ (ResU.single_get_self _ _) ⟨w, eζ⟩
          rwa [CellU.wit_immOf] at this) hRb.1 hWd
      have hobs' : vO₀ (ℍ := ℍ) S (δ.extend x β) Θ n w W := by
        rw [vO_extend_of_not_free₀ (A := S) hx]
        exact hobs
      refine ⟨β, interp_ext_self δ x β, ⟨l', LSet.singleton β, w, W, hβ, rfl, rfl, le_refl _,
        hobs'⟩, fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
      obtain ⟨rfl, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -, -⟩ := CellU.immOf_inj e'
      exact hcr l' S w (RefPos.ref S l') eζ
  | imm a S =>
      have hc' : vShape (.imm a S) (δ.extend x₀ β₀) _ c := hc
      obtain ⟨α, -, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      have hR' := hR
      obtain ⟨-, -, ⟨l'', s₁, u₁, σ₁, hs₁, hv, rfl, -⟩, -⟩ := hR'
      obtain rfl : l'' = l' := loc_inj (hv.symm.trans hl)
      obtain ⟨ζ, eζ, kζ, -, -, -⟩ := hRl l'' _ (ResU.single_get_self _ _)
      have kζ' : ζ.kind = Kind.imm := by rw [kζ]; simp
      rw [relRes_single, relCell_keep eζ kζ']
      show vN₀ (ℍ := ℍ) (.imm a S) (δ.extend x β) Θ n _ _
      rw [vN_extend_of_not_free₀ hx, vN_imm_eq₀]
      rw [vShape_extend_of_not_free hx₀] at hc'
      refine vO_transfer₀ (.imm a S) hRl ?_ ?_ hRv hc'
      rotate_left
      · intro m t u σ h e _
        exact hLk m t u σ h e (by
          obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
          exact ⟨ζ, eζ, kζ'⟩)
      intro m ψ e
      obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
      obtain ⟨ζ₂, eζ₂, her, hwit, -⟩ := hcR m _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      exact ⟨ζ, eζ, by rw [kζ']; simp, (hwit (by rw [kζ']; simp)).symm, her.symm,
        fun hk => absurd (by simp) hk⟩
  | «mut» a S =>
      obtain ⟨α, -, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      obtain ⟨⟨α', -, b, -, ⟨l'', w₀, χ, hχ, j, hw, hnj, hv, -, rfl⟩, -⟩, -⟩ := hR
      obtain rfl : l'' = l' := loc_inj (hv.symm.trans hl)
      subst hl
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hRl l'' _ (ResU.single_get_self _ _)
      have hζ' := hζ (by simp)
      subst hζ'
      obtain ⟨ζ₂, eζ₂, her, hwit, -⟩ := hcR l'' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      have hw' := hwit (by simp)
      simp only [CellU.erase_immOf, CellU.erase_mutOf, CellU.wit_immOf,
        CellU.wit_mutOf] at her hw'
      subst her; subst hw'
      have kne : (CellU.mutOf b w W hχ _ hw).kind ≠ Kind.imm := by simp
      have hβ := hs l'' _ (ResU.single_get_self _ _) ⟨_, eζ, kne⟩
      rw [CellU.wit_immOf] at hβ
      rw [relRes_single, relCell_fire eζ kne hβ]
      have hS : ¬ VFree x S := fun h => hx (Or.inr h)
      have hvS : vN₀ (ℍ := ℍ) S δ Θ n w W :=
        vN_le₀ hnj ((vN_above₀ S δ Θ hχ).mp hw)
      have hobs' : vO₀ (ℍ := ℍ) S (δ.extend x β) Θ n w W := by
        rw [vO_extend_of_not_free₀ hS]
        exact vN_vO₀ S δ Θ n w W hvS
      refine ⟨β, interp_ext_self δ x β, ⟨l'', LSet.singleton β, w, W, hβ, rfl, rfl, le_refl _,
        hobs'⟩, fun l₀ s₀ u₀ σ₀ h₀ e => ?_⟩
      obtain ⟨rfl, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -, -⟩ := CellU.immOf_inj e'
      exact hcm l'' S (MutPos.mut a S l'')

/-! ### Positions across `TyEq` -/

/-- **A `Ref` position is read across `TyEq`**, at a pointee type `TyEq` to the first. -/
theorem _root_.BoCa.Fig16.LogRel.Core.RefPos.tyEq {T : VTy} {v : Val} {l : Loc} {S : VTy} (h : RefPos T v l S) :
    ∀ {T' : VTy} {δ δ' : LSub}, TyEq T δ T' δ' → ∃ S', RefPos T' v l S' ∧ TyEq S δ S' δ' := by
  induction h with
  | ref S l =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      exact ⟨_, RefPos.ref _ l, hT⟩
  | tensorL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', RefPos.tensorL h', e⟩
  | tensorR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', RefPos.tensorR h', e⟩
  | sumL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', RefPos.sumL h', e⟩
  | sumR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', RefPos.sumR h', e⟩
  | box _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', RefPos.box h', e⟩
  | @mu A _ _ _ hcl _ ih =>
      intro T' δ δ' hT
      cases T' with
      | mu A' =>
          simp only [TyEq] at hT
          have hcl' : (VTy.mu A').Cl 0 := (TyEq.Cl_iff (.mu A) (A' := .mu A') 0 hT).mp hcl
          obtain ⟨S', h', e⟩ := ih (TyEq.inst (S := .mu A) (S' := .mu A') hT hT)
          exact ⟨S', RefPos.mu hcl' h', e⟩
      | _ => simp only [TyEq] at hT
  | fam hi _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT
      exact ⟨S', RefPos.fam hi h', e⟩

/-- **A `Mut` position is read across `TyEq`**, at a pointee type `TyEq` to the first. -/
theorem _root_.BoCa.Fig16.LogRel.Core.MutPos.tyEq {T : VTy} {v : Val} {l : Loc} {S : VTy} (h : MutPos T v l S) :
    ∀ {T' : VTy} {δ δ' : LSub}, TyEq T δ T' δ' → ∃ S', MutPos T' v l S' ∧ TyEq S δ S' δ' := by
  induction h with
  | «mut» a S l =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      exact ⟨_, MutPos.mut _ _ l, hT.2⟩
  | tensorL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', MutPos.tensorL h', e⟩
  | tensorR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', MutPos.tensorR h', e⟩
  | sumL _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.1
      exact ⟨S', MutPos.sumL h', e⟩
  | sumR _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', MutPos.sumR h', e⟩
  | box _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT.2
      exact ⟨S', MutPos.box h', e⟩
  | @mu A _ _ _ hcl _ ih =>
      intro T' δ δ' hT
      cases T' with
      | mu A' =>
          simp only [TyEq] at hT
          have hcl' : (VTy.mu A').Cl 0 := (TyEq.Cl_iff (.mu A) (A' := .mu A') 0 hT).mp hcl
          obtain ⟨S', h', e⟩ := ih (TyEq.inst (S := .mu A) (S' := .mu A') hT hT)
          exact ⟨S', MutPos.mu hcl' h', e⟩
      | _ => simp only [TyEq] at hT
  | fam hi _ ih =>
      intro T' δ δ' hT
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', e⟩ := ih hT
      exact ⟨S', MutPos.fam hi h', e⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
