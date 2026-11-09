import Core.Chain.Fundamental831N
import Core.Chain.ThenK835N
import Core.Chain.IterKW835N
import Core.Chain.ReindexK835N
import Core.Chain.FrameListKW835N

/-!
# The context and bind layer, and the rules with no stop, at the typed world  `[spec §62]`

`docs/new-core/scope-835-tables.md` §10.3. The interface's relation-level lemmas
(`scope-831-interface.md` §2: the G, C, V and F entries, `Iface834N`; V1, `TyEq834N`) and the
structural rules L1 and L2 (§3), at `cN`/`SemJN` (the relation at `KW`), each Core's
compatibility lemma line by line:

* `F A` is `erwp` at the empty table at every floor (`cN_ret_iff`), so a value's judgment is read
  and built at `erwp` as before (`cN_ret_of`, `erwp_of_cN_ret`).
* `F_Σ R` is `erwpK` at every floor from `⟨Θ, c, lo⟩` at the row's table. A computation that never
  stops binds into it (`erwpK_bind_frame`: `rwp_frame`, then `erwpK_bindR`), as `erwp_bind_frame`
  binds into `erwp`; validity is assumed by `erwpK_of_valid`.
* The context relation `gN` reads `vN`; its laws follow from `vN`'s laws.
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
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-! ### `F A` at `erwp` -/

/-- `F A` from a run at the empty table. -/
theorem cN_ret_of {A : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (fun k _ v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
      n ls e ρ) : cN (ℍ := ℍ) (.ret A) δ Θ c n ls e ρ :=
  (cN_ret_iff A δ Θ c n ls e ρ).mpr h

/-- A run at the empty table from `F A`. -/
theorem erwp_of_cN_ret {A : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cN (ℍ := ℍ) (.ret A) δ Θ c n ls e ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (fun k _ v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
      n ls e ρ :=
  (cN_ret_iff A δ Θ c n ls e ρ).mp h

/-! ### Consumed contexts -/

/-- **A consumed context, up to persistent slots, owns nothing** (Core's `gSepC_deadP`). -/
theorem gN_deadP {δ : LSub} {Θ : LocTy} {n : Nat} : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ →
    ∀ {γ : List Val} {ρ : WRes}, gN (ℍ := ℍ) δ Θ Γ γ n ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; exact h
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h
      | cons v γ' => exact ih (γ := γ') (by simpa [gN] using h)
  | weaken hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h
      | cons v γ' =>
          simp only [gN, if_true] at h
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          rw [vN_empty_of_persistent _ hT hv, ih hrest] at hc
          exact eq_empty_of_compS_empty hc
/-- A consumed context relates only the empty resource. -/
theorem gN_dead {δ : LSub} {Θ : LocTy} {n : Nat} : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ →
    ∀ {γ : List Val} {ρ : WRes}, gN (ℍ := ℍ) δ Θ Γ γ n ρ ↔ ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ; cases γ <;> rfl
  | cons _ ih =>
      intro γ ρ
      cases γ with
      | nil => rfl
      | cons v γ' => simpa [gN] using ih (γ := γ')

/-! ### G11, G6, G8: the context relation down the index, along the order, at agreeing `δ` -/

/-- **`𝒢⟦Γ⟧` at a lower index** (chain only): `vN_le` slot by slot. -/
theorem gN_le {δ : LSub} {Θ : LocTy} {k n : Nat} (hkn : k ≤ n) :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, gN (ℍ := ℍ) δ Θ Γ γ n ρ → gN (ℍ := ℍ) δ Θ Γ γ k ρ
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | s :: Γ, v :: γ, ρ, h => by
      unfold gN at h ⊢
      split
      · rename_i hl
        rw [if_pos hl] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc, vN_le hkn h₁, gN_le hkn h₂⟩
      · rename_i hl
        rw [if_neg hl] at h
        exact gN_le hkn h

/-- **`𝒢⟦Γ⟧` at two `δ` its live slots read alike** (Core's `gSepC_congr`). -/
theorem gN_congr {δ₁ δ₂ : LSub} {Θ : LocTy} :
    ∀ {Γ : Ctx VTy} {γ : List Val},
      (∀ s ∈ Γ, s.live = true → vN (ℍ := ℍ) s.ty δ₁ = vN (ℍ := ℍ) s.ty δ₂) →
      gN (ℍ := ℍ) δ₁ Θ Γ γ = gN (ℍ := ℍ) δ₂ Θ Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vN (ℍ := ℍ) t.ty δ₁ = vN (ℍ := ℍ) t.ty δ₂ :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          funext n ρ
          by_cases hl : s.live
          · simp only [gN, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gN, if_neg hl, ih htail]

/-! ### G1, G2, G4: the context relation at the splits -/

/-- A persistent live slot holds only at `∅` (Core's `gSepC_cons_persistent`). -/
theorem gN_cons_persistent {δ : LSub} {Θ : LocTy} {n : Nat} {T : VTy} (hT : T.Persistent)
    {Γ : Ctx VTy} {v : Val} {γ : List Val} {ρ : WRes}
    (h : gN (ℍ := ℍ) δ Θ (⟨T, true⟩ :: Γ) (v :: γ) n ρ) :
    vN (ℍ := ℍ) T δ Θ n v PMap.empty ∧ gN (ℍ := ℍ) δ Θ Γ γ n ρ := by
  simp only [gN, if_true] at h
  obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
  obtain rfl := vN_empty_of_persistent _ hT hv
  rw [eq_of_compS_empty_left hc]
  exact ⟨hv, hrest⟩

/-- **`Γ = Γ₁, Γ₂` splits `𝒢⟦Γ⟧`; a persistent slot, at `∅`, goes to both sides** (Core's
`gSepC_splitP`, `gDenC_split`). -/
theorem gN_split {δ : LSub} {Θ : LocTy} {n : Nat} :
    ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → ∀ {γ : List Val} {ρ : WRes},
      gN (ℍ := ℍ) δ Θ Γ γ n ρ →
        ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ gN (ℍ := ℍ) δ Θ Γ₁ γ n ρ₁ ∧ gN (ℍ := ℍ) δ Θ Γ₂ γ n ρ₂ := by
  intro Γ Γ₁ Γ₂ hsp
  induction hsp with
  | nil =>
      intro γ ρ h
      refine ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ?_⟩
      cases γ <;> rfl
  | left _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, rfl⟩
      | cons v γ' =>
          simp only [gN, if_true, Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hcσ hc
          exact ⟨x, σ₂, hxρ, ⟨ρ₁, σ₁, hx, hv, h₁⟩, h₂⟩
  | right _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, rfl⟩
      | cons v γ' =>
          simp only [gN, if_true, Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_lcomm hcσ hc
          exact ⟨σ₁, x, hxρ, h₁, ⟨ρ₁, σ₂, hx, hv, h₂⟩⟩
  | dead _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, rfl⟩
      | cons v γ' =>
          simp only [gN, Bool.false_eq_true, if_false] at h ⊢
          exact ih (γ := γ') h
  | dup hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, rfl⟩
      | cons v γ' =>
          obtain ⟨hv, hrest⟩ := gN_cons_persistent hT h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          simp only [gN, if_true]
          exact ⟨σ₁, σ₂, hcσ, ⟨PMap.empty, σ₁, compS_empty_left σ₁, hv, h₁⟩,
            ⟨PMap.empty, σ₂, compS_empty_left σ₂, hv, h₂⟩⟩

/-- **The split with the view's consistency at its parts** (G1 with G12, chain only): at a valid
resource consistent with `c`, each part of the split is consistent with `c`
(`consistentX_left`/`_right`). -/
theorem gN_splitC {δ : LSub} {Θ : LocTy} {n : Nat} {Γ Γ₁ Γ₂ : Ctx VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) {γ : List Val} {ρ : WRes} {c : Loc → Option Life}
    (hg : gN (ℍ := ℍ) δ Θ Γ γ n ρ) (hc : ConsistentX c ρ) (hv : ResU.Valid ρ) :
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ gN (ℍ := ℍ) δ Θ Γ₁ γ n ρ₁ ∧ gN (ℍ := ℍ) δ Θ Γ₂ γ n ρ₂ ∧
      ConsistentX c ρ₁ ∧ ConsistentX c ρ₂ := by
  obtain ⟨ρ₁, ρ₂, hcρ, h₁, h₂⟩ := gN_split hsp hg
  exact ⟨ρ₁, ρ₂, hcρ, h₁, h₂, consistentX_left hcρ hc hv, consistentX_right hcρ hc hv⟩

/-- **`ID`'s context, up to persistent slots** (Core's `gSepC_soloP`). -/
theorem gN_soloP {δ : LSub} {Θ : LocTy} {n : Nat} :
    ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.SoloP Γ i T → ∀ {γ : List Val} {ρ : WRes},
      i < γ.length → gN (ℍ := ℍ) δ Θ Γ γ n ρ →
        ∃ v, γ[i]? = some v ∧ vN (ℍ := ℍ) T δ Θ n v ρ := by
  intro Γ i T hs
  induction hs with
  | here hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          simp only [gN, if_true] at hg
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [gN_deadP hdead hrest] at hc
          rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
          exact ⟨v, rfl, hv⟩
  | there _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          simp only [gN, Bool.false_eq_true, if_false] at hg
          obtain ⟨w, hw, hv⟩ := ih (γ := γ') (by simpa using hlen) hg
          exact ⟨w, by simpa using hw, hv⟩
  | skip hS _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨w, hw, hv⟩ :=
            ih (γ := γ') (by simpa using hlen) (gN_cons_persistent hS hg).2
          exact ⟨w, by simpa using hw, hv⟩

/-- **`!Γ` holds no resource** (Core's `gSepC_persistent`, `gDenC_persistent`). -/
theorem gN_persistent {δ : LSub} {Θ : LocTy} {n : Nat} :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, Ctx.Banged Γ →
      gN (ℍ := ℍ) δ Θ Γ γ n ρ → ρ = PMap.empty
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, ρ, hp, h => by
      have hp' : Ctx.Banged Γ := fun t ht hl => hp t (List.mem_cons_of_mem _ ht) hl
      unfold gN at h
      split at h
      · rename_i hl
        obtain ⟨T, hT⟩ := hp s List.mem_cons_self hl
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have e₁ : ρ₁ = PMap.empty := by rw [hT] at h₁; exact h₁.1
        have e₂ := gN_persistent hp' h₂
        subst e₁; subst e₂
        exact eq_of_compS_empty_left hc
      · exact gN_persistent hp' h

/-! ### G7: an outliving context lies in the stratum -/

/-- **`Δ ⊨ Γ ⊐ @a`: `𝒢⟦Γ⟧` lies in `Res_α`** (Core's `gSepC_outlives`, `[TR]` 6.62 at 6.60):
`vN_outlives` at each live slot, folded over the context. -/
theorem gN_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life} {Θ : LocTy} {n : Nat}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes},
      (∀ s ∈ Γ, s.live = true → VOutlives Δ a s.ty) →
      gN (ℍ := ℍ) δ Θ Γ γ n ρ → ρ.InStratum α := by
  intro Γ
  induction Γ with
  | nil =>
      rintro γ ρ - rfl
      exact ResU.inStratum_empty α
  | cons s Γ ih =>
      intro γ ρ hT hg
      cases γ with
      | nil =>
          obtain rfl := hg
          exact ResU.inStratum_empty α
      | cons v γ =>
          have hT' : ∀ t ∈ Γ, t.live = true → VOutlives Δ a t.ty :=
            fun t ht => hT t (List.mem_cons.mpr (Or.inr ht))
          by_cases hl : s.live = true
          · simp only [gN, if_pos hl] at hg
            obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
            exact inStratum_compS hc
              (vN_outlives hδ ha (hT s (List.mem_cons.mpr (Or.inl rfl)) hl) Θ n v ρ₁ hv)
              (ih hT' hrest)
          · simp only [gN, if_neg hl] at hg
            exact ih hT' hg

/-! ### V8, G9: own-free types own nothing -/

/-- **A value of an own-free type owns no cell** (Core's `vC_noOwn_of_ownFree`). -/
theorem vN_noOwn_of_ownFree {A : VTy} (hA : A.OwnFree) :
    ∀ {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes},
      vN (ℍ := ℍ) A δ Θ n v ρ → NoOwn ρ := by
  induction hA with
  | unit => intro δ Θ n v ρ h; rw [h.2]; exact noOwn_empty
  | zero => intro δ Θ n v ρ h; exact h.elim
  | int w => intro δ Θ n v ρ h; rw [h.2]; exact noOwn_empty
  | unk => intro δ Θ n v ρ h; rw [h]; exact noOwn_empty
  | opq k hk =>
      intro δ Θ n v ρ h
      rcases Opaque.rel_cases h with ⟨-, rfl, -⟩ | ⟨rfl, -⟩
      · exact noOwn_empty
      · exact absurd hk Opaque.tok_not_host
  | bang A => intro δ Θ n v ρ h; rw [h.1]; exact noOwn_empty
  | imm a A =>
      intro δ Θ n v ρ h
      obtain ⟨α, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩ := h
      exact ResU.restrict_single_other (by simp)
  | «mut» a A =>
      intro δ Θ n v ρ h
      obtain ⟨α, -, b, -, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩ := h
      exact ResU.restrict_single_other (by simp)
  | tensor _ _ ihA ihB =>
      intro δ Θ n v ρ h
      obtain ⟨v₁, v₂, ρ₁, ρ₂, -, hc, h₁, h₂⟩ := h
      exact noOwn_compS hc (ihA h₁) (ihB h₂)
  | sum _ _ ihA ihB =>
      intro δ Θ n v ρ h
      rcases h with ⟨v₁, -, h⟩ | ⟨v₂, -, h⟩
      · exact ihA h
      · exact ihB h

/-- **An own-free context owns no cell** (Core's `gSepC_noOwn`, `gDenC_noOwn`). -/
theorem gN_noOwn {δ : LSub} {Θ : LocTy} {n : Nat} :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, Γ.OwnFree →
      gN (ℍ := ℍ) δ Θ Γ γ n ρ → NoOwn ρ
  | [], _, _, _, h => by rw [h]; exact noOwn_empty
  | _ :: _, [], _, _, h => by rw [h]; exact noOwn_empty
  | s :: Γ, v :: γ, ρ, hd, h => by
      unfold gN at h
      split at h
      · rename_i hl
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact noOwn_compS hc (vN_noOwn_of_ownFree (hd s (by simp) hl) h₁)
          (gN_noOwn (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs')) h₂)
      · exact gN_noOwn (fun s' hs' => hd s' (List.mem_cons_of_mem _ hs')) h

/-! ### G12 at a conclusion that is not `F`/`F_Σ` -/

/-- **One unfolding may assume its resource valid**: `cN_of_valid`'s induction on the tree. -/
theorem cBN_of_valid (S : VTy) (Rc : CandN) : ∀ (D : CTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes),
    (ResU.Valid ρ → cBN (ℍ := ℍ) S Rc D δ Θ c n ls e ρ) → cBN (ℍ := ℍ) S Rc D δ Θ c n ls e ρ
  | .ret _, _, _, _, _, _, _, _, h => fun lo => erwpK_of_valid fun hv => h hv lo
  | .arr _ D, δ, Θ, _, _, ls, _, _, h => fun c' k hk v ρv ρ' hcomp hv hcon =>
      cBN_of_valid S Rc D δ Θ c' k ls _ ρ'
        (fun hv' => h (ResU.Valid.split hcomp hv').1 c' k hk v ρv ρ' hcomp hv hcon)
  | .amp C D, δ, Θ, c, n, ls, _, ρ, h =>
      ⟨cBN_of_valid S Rc C δ Θ c n ls _ ρ (fun hv => (h hv).1),
        cBN_of_valid S Rc D δ Θ c n ls _ ρ (fun hv => (h hv).2)⟩
  | .top, _, _, _, _, _, _, _, _ => trivial
  | .all x _ D, δ, Θ, c, n, ls, _, ρ, h => fun α hα =>
      cBN_of_valid S Rc D (δ.extend x α) Θ c n ls _ ρ (fun hv => h hv α hα)
  | .nu _, _, _, _, _, _, _, _, _ => trivial
  | .eff _ _ _ _ _ _ _ _, _, _, _, _, _, _, _, h => fun lo => erwpK_of_valid fun hv => h hv lo

/-- **A computation may assume its resource valid** (chain only): at `F`/`F_Σ` by
`erwp_of_valid`; at `⊸` because the resource is a part of the composite the wand runs from, and a
part of a valid resource is valid; at `&` and `∀` by their parts; at `ν` by coinduction, the
candidate being the computations valid where their resource is (`cBN_of_valid` at one
unfolding). This is what gives a split's consistency (`gN_splitC`) at a conclusion that is not
`F`/`F_Σ`. -/
theorem cN_of_valid : ∀ (C : CTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes),
    (ResU.Valid ρ → cN (ℍ := ℍ) C δ Θ c n ls e ρ) → cN (ℍ := ℍ) C δ Θ c n ls e ρ
  | .ret _, _, _, _, _, _, _, _, h => fun lo => erwpK_of_valid fun hv => h hv lo
  | .arr _ C, δ, Θ, _, _, ls, _, _, h => fun c' k hk v ρv ρ' hcomp hv hcon =>
      cN_of_valid C δ Θ c' k ls _ ρ'
        (fun hv' => h (ResU.Valid.split hcomp hv').1 c' k hk v ρv ρ' hcomp hv hcon)
  | .amp C D, δ, Θ, c, n, ls, _, ρ, h =>
      ⟨cN_of_valid C δ Θ c n ls _ ρ (fun hv => (h hv).1),
        cN_of_valid D δ Θ c n ls _ ρ (fun hv => (h hv).2)⟩
  | .top, _, _, _, _, _, _, _, _ => trivial
  | .all x _ C, δ, Θ, c, n, ls, _, ρ, h => fun α hα =>
      cN_of_valid C (δ.extend x α) Θ c n ls _ ρ (fun hv => h hv α hα)
  | .nu C, δ, Θ, c, n, ls, e, ρ, h => fun hS => by
      refine ⟨fun Θ c n ls e ρ => ResU.Valid ρ → nuCand (ℍ := ℍ) C δ Θ c n ls e ρ, ?_, h⟩
      intro Θ' c' k ls' e' ρ' hR
      refine cBN_of_valid _ _ C δ Θ' c' k ls' e' ρ' fun hv => ?_
      exact cBN_mono (R' := fun Θ c n ls e ρ => ResU.Valid ρ → nuCand (ℍ := ℍ) C δ Θ c n ls e ρ)
        (fun _ _ _ _ _ _ _ h'' _ => h'') hS.nuLeaf δ Θ' c' k ls' e' ρ'
        (cN_nu_out hS δ Θ' c' k ls' e' ρ' (hR hv))
  | .eff _ _ _ _ _ _ _ _, _, _, _, _, _, _, _, h => fun lo => erwpK_of_valid fun hv => h hv lo

/-! ### W4 at a world -/

/-- **Bind on the sub-expression into a run at a world** (`erwp_bind_frame` at `erwpK`): the
sub-expression runs at the empty table, so it never stops (`rwp_of_erwp_empty`); the frame goes
through it (`rwp_frame`), the returned resource stays consistent with the view and valid
(`rwp_consistentXV`), and the run binds into any table (`erwpK_bindR`). -/
theorem erwpK_bind_frame {ι : Type} {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (K : Kont)
    {e : Expr} {P : PostN} (R : WProp) {n : Nat} {ls : List SRec} {ρ₁ ρ₂ ρ : WRes}
    {c : Loc → Option Life} (hcρ : ResU.CompS ρ₁ ρ₂ ρ) (hc : ConsistentX c ρ)
    (hw : erwp (ℍ := ℍ) (Φ x) (opTableN OpTabN.empty) P n ls e ρ₁) (hR : R ρ₂)
    (h : ∀ k, k ≤ n → ∀ ls' (v : Val) (σ₁ σ₂ σ : WRes), ResU.CompS σ₁ σ₂ σ → P k ls' v σ₁ →
      R σ₂ → ConsistentX c σ → ResU.Valid σ → erwpK (ℍ := ℍ) V Φ Tb Q x k ls' (K.plug v.1) σ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls (K.plug e) ρ := by
  refine erwpK_bindR hL hΦ K ?_
  refine rwp_mono_le (fun k hk ls' v σ hv => ?_)
    (rwp_consistentXV (rwp_frame (fun _ => R) (fun _ _ _ _ h => h) hcρ (rwp_of_erwp_empty hw) hR)
      hc)
  obtain ⟨⟨σ₁, σ₂, hcσ, hP, hRσ⟩, hcσ', hvσ⟩ := hv
  exact h k hk ls' v σ₁ σ₂ σ hcσ hP hRσ hcσ' hvσ

/-! ### C2: bind at every computation type -/

/-- **Bind at one unfolding of an observation tree** (Core's `cB_bind`): `cN_bind`'s induction. -/
theorem cBN_bind (S : VTy) (Rc : CandN) : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down →
    ∀ (K : Kont) (M : Expr) (P : PostN), P.Down → ∀ (R : Nat → WRes → Prop),
    (∀ k k' ρ, k' ≤ k → R k ρ → R k' ρ) →
    (∀ (c : Loc → Option Life) k ls' (v : Val) (σ₁ σ₂ σ : WRes), ResU.CompS σ₁ σ₂ σ →
      P k ls' v σ₁ → R k σ₂ → ConsistentX c σ → cBN (ℍ := ℍ) S Rc C δ Θ c k ls' (K.plug v.1) σ) →
    ∀ (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ →
      (∀ c', ConsistentX c' ρ₁ → erwp (ℍ := ℍ) (Θ.view c') (opTableN OpTabN.empty) P n ls M ρ₁) →
      R n ρ₂ → ConsistentX c ρ → cBN (ℍ := ℍ) S Rc C δ Θ c n ls (K.plug M) ρ
  | .ret _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      fun lo => erwpK_of_valid fun hv => erwpK_bind_frame (Φ := fun z : KW => z.Θ.view z.c)
        (x := (⟨Θ, c, lo⟩ : KW)) (fun _ => opTableK_local _ _)
        (LocTy.view_down hΘ c) K (R n) hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ' lo)
  | .eff _ _ _ _ _ _ _ _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      fun lo => erwpK_of_valid fun hv => erwpK_bind_frame (Φ := fun z : KW => z.Θ.view z.c)
        (x := (⟨Θ, c, lo⟩ : KW)) (fun _ => opTableK_local _ _)
        (LocTy.view_down hΘ c) K (R n) hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ' lo)
  | .arr A C, δ, Θ, hΘ, K, M, P, hP, R, hR, h, _, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, _ =>
      fun c' k hk v ρv ρ' hcomp hv hcon => by
        obtain ⟨y, hy, hyx⟩ := compS_reassoc hcρ hcomp
        refine cBN_bind S Rc C δ Θ hΘ (.appL K v) M P hP
          (fun j σ => ∃ a b, ResU.CompS a b σ ∧ R j a ∧ vN (ℍ := ℍ) A δ Θ j v b)
          (fun j j' σ hj ⟨a, b, hab, hRa, hvb⟩ => ⟨a, b, hab, hR j j' a hj hRa, vN_le hj hvb⟩)
          (fun c'' j ls' w σ₁ σ₂ σ' hcσ hPw ⟨a, b, hab, hRa, hvb⟩ hcon' => ?_)
          c' k ls ρ₁ y ρ' hyx
          (fun c'' hc'' => erwp_le (LocTy.view_down hΘ c'') (opTableN_local _)
            (opTableN_down OpTabN.empty_down) hP hk (hM c'' hc''))
          ⟨ρ₂, ρv, hy, hR n k ρ₂ hk hR₂, hv⟩ hcon
        obtain ⟨z, hz, hzσ⟩ := compS_reassoc' hab hcσ
        refine cBN_of_valid S Rc C δ Θ c'' j ls' _ σ' fun hv' => ?_
        exact h c'' j ls' w σ₁ a z hz hPw hRa (consistentX_left hzσ hcon' hv') c'' j le_rfl v b σ'
          hzσ hvb hcon'
  | .amp C D, δ, Θ, hΘ, K, M, P, hP, R, hR, h, c, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, hc =>
      ⟨cBN_bind S Rc C δ Θ hΘ (.appL K _) M P hP R hR
          (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' => (h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ').1)
          c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc,
        cBN_bind S Rc D δ Θ hΘ (.appL K _) M P hP R hR
          (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' => (h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ').2)
          c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc⟩
  | .top, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | .all x _ C, δ, Θ, hΘ, K, M, P, hP, R, hR, h, c, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, hc =>
      fun α hα => cBN_bind S Rc C (δ.extend x α) Θ hΘ (.appL K .unit) M P hP R hR
        (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' => h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' α hα)
        c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc
  | .nu _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial


/-- **Bind at `𝒞⟦C⟧`** (Core's `cC_bind`). Run `M` in the hole of `K`, framing `R` through the
run; the rest of the computation (`K` and the stack `C` is eliminated by) continues at the index
the run leaves. `erwp_bind_frame` at `F`/`F_Σ`; at `⊸` the stack's argument joins the frame, read
at the wand's index; at `&` and `∀` by their parts; at `ν` by unfolding, `cBN_bind`, and rolling (Core's `cC_bind`).

The chain's obligations are in the premises: `M`'s run is asked at every view consistent with its
own part (`SemJN`'s reading), and `cN_of_valid` gives that part's consistency from the
composite's at each `⊸` the stack passes. -/
theorem cN_bind : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down →
    ∀ (K : Kont) (M : Expr) (P : PostN), P.Down → ∀ (R : Nat → WRes → Prop),
    (∀ k k' ρ, k' ≤ k → R k ρ → R k' ρ) →
    (∀ (c : Loc → Option Life) k ls' (v : Val) (σ₁ σ₂ σ : WRes), ResU.CompS σ₁ σ₂ σ →
      P k ls' v σ₁ → R k σ₂ → ConsistentX c σ → cN (ℍ := ℍ) C δ Θ c k ls' (K.plug v.1) σ) →
    ∀ (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ →
      (∀ c', ConsistentX c' ρ₁ → erwp (ℍ := ℍ) (Θ.view c') (opTableN OpTabN.empty) P n ls M ρ₁) →
      R n ρ₂ → ConsistentX c ρ → cN (ℍ := ℍ) C δ Θ c n ls (K.plug M) ρ
  | .ret _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      fun lo => erwpK_of_valid fun hv => erwpK_bind_frame (Φ := fun z : KW => z.Θ.view z.c)
        (x := (⟨Θ, c, lo⟩ : KW)) (fun _ => opTableK_local _ _)
        (LocTy.view_down hΘ c) K (R n) hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ' lo)
  | .eff _ _ _ _ _ _ _ _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      fun lo => erwpK_of_valid fun hv => erwpK_bind_frame (Φ := fun z : KW => z.Θ.view z.c)
        (x := (⟨Θ, c, lo⟩ : KW)) (fun _ => opTableK_local _ _)
        (LocTy.view_down hΘ c) K (R n) hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ' lo)
  | .arr A C, δ, Θ, hΘ, K, M, P, hP, R, hR, h, _, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, _ =>
      fun c' k hk v ρv ρ' hcomp hv hcon => by
        obtain ⟨y, hy, hyx⟩ := compS_reassoc hcρ hcomp
        refine cN_bind C δ Θ hΘ (.appL K v) M P hP
          (fun j σ => ∃ a b, ResU.CompS a b σ ∧ R j a ∧ vN (ℍ := ℍ) A δ Θ j v b)
          (fun j j' σ hj ⟨a, b, hab, hRa, hvb⟩ => ⟨a, b, hab, hR j j' a hj hRa, vN_le hj hvb⟩)
          (fun c'' j ls' w σ₁ σ₂ σ' hcσ hPw ⟨a, b, hab, hRa, hvb⟩ hcon' => ?_)
          c' k ls ρ₁ y ρ' hyx
          (fun c'' hc'' => erwp_le (LocTy.view_down hΘ c'') (opTableN_local _)
            (opTableN_down OpTabN.empty_down) hP hk (hM c'' hc''))
          ⟨ρ₂, ρv, hy, hR n k ρ₂ hk hR₂, hv⟩ hcon
        obtain ⟨z, hz, hzσ⟩ := compS_reassoc' hab hcσ
        refine cN_of_valid C δ Θ c'' j ls' _ σ' fun hv' => ?_
        exact h c'' j ls' w σ₁ a z hz hPw hRa (consistentX_left hzσ hcon' hv') c'' j le_rfl v b σ'
          hzσ hvb hcon'
  | .amp C D, δ, Θ, hΘ, K, M, P, hP, R, hR, h, c, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, hc =>
      ⟨cN_bind C δ Θ hΘ (.appL K _) M P hP R hR
          (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' => (h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ').1)
          c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc,
        cN_bind D δ Θ hΘ (.appL K _) M P hP R hR
          (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' => (h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ').2)
          c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc⟩
  | .top, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | .all x _ C, δ, Θ, hΘ, K, M, P, hP, R, hR, h, c, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, hc =>
      fun α hα => cN_bind C (δ.extend x α) Θ hΘ (.appL K .unit) M P hP R hR
        (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' => h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' α hα)
        c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc
  | .nu C, δ, Θ, hΘ, K, M, P, hP, R, hR, h, c, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, hc => fun hS =>
      (cN_nu_unfold hS δ Θ c n ls _ ρ).mpr (cBN_bind _ _ C δ Θ hΘ K M P hP R hR
        (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' =>
          (cN_nu_unfold hS δ Θ c' k ls' _ σ).mp (h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ'))
        c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc) hS

/-! ### F2: a `!`-function applied at a later world -/

/-- **A `!`-function is a function at every world, and applies** (Core's `bang_app`): `!` owns
nothing, so every world is an extension at its resource (`LocTy.extR_empty`); the `⊸` clause is
then read at the argument's world, index and view. -/
theorem bang_app {A B : VTy} {δ : LSub} {Θ Θ' : LocTy} (hΘ' : Θ'.OK) {n k : Nat} (hk : k ≤ n)
    {f v : Val} {ρv : WRes} (hf : vN (ℍ := ℍ) (.bang (.lolli A B)) δ Θ n f PMap.empty)
    {c : Loc → Option Life} (hc : ConsistentX c ρv) (hv : vN (ℍ := ℍ) A δ Θ' k v ρv)
    (ls : List SRec) :
    erwp (ℍ := ℍ) (Θ'.view c) (opTableN OpTabN.empty) (fun k _ w ρ => vN (ℍ := ℍ) B δ Θ' k w ρ)
      k ls (.app (.val f) (.val v)) ρv :=
  erwp_of_cN_ret (hf.2 Θ' (LocTy.extR_empty Θ Θ') hΘ' c (consistentX_empty c) ls c k hk v ρv ρv
    (compS_empty_left ρv) hv hc)

/-- **At a first-order type `vN` is Core's `vP`**, at every world, index and list: the clauses
are Core's with `⋆` written as `ResU.CompS` and `⌜p⌝` as `p ∧ ρ = ∅` (F1). -/
theorem vN_iff_vP : ∀ {A : VTy}, A.isFO = true → ∀ {δ : LSub} {Θ : LocTy} {n : Nat}
    {ls : List SRec} {v : Val} {ρ : WRes}, vN (ℍ := ℍ) A δ Θ n v ρ ↔ vP A ls δ v ρ
  | .unit, _, _, _, _, _, _, _ => ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩
  | .zero, _, _, _, _, _, _, _ => Iff.rfl
  | .int _, _, _, _, _, _, _, _ => ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩
  | .tensor A B, h, δ, Θ, n, ls, v, ρ => by
      simp only [VTy.isFO, Bool.and_eq_true] at h
      constructor
      · rintro ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, h₁, h₂⟩
        exact ⟨v₁, v₂, pure_sep_mk rfl
          ⟨ρ₁, ρ₂, hc, (vN_iff_vP h.1).mp h₁, (vN_iff_vP h.2).mp h₂⟩⟩
      · rintro ⟨v₁, v₂, hs⟩
        obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
        exact ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, (vN_iff_vP h.1).mpr h₁, (vN_iff_vP h.2).mpr h₂⟩
  | .sum A B, h, δ, Θ, n, ls, v, ρ => by
      simp only [VTy.isFO, Bool.and_eq_true] at h
      constructor
      · rintro (⟨v₁, rfl, h₁⟩ | ⟨v₂, rfl, h₂⟩)
        · exact Or.inl ⟨v₁, pure_sep_mk rfl ((vN_iff_vP h.1).mp h₁)⟩
        · exact Or.inr ⟨v₂, pure_sep_mk rfl ((vN_iff_vP h.2).mp h₂)⟩
      · rintro (⟨v₁, hs⟩ | ⟨v₂, hs⟩)
        · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hs
          exact Or.inl ⟨v₁, rfl, (vN_iff_vP h.1).mpr h₁⟩
        · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hs
          exact Or.inr ⟨v₂, rfl, (vN_iff_vP h.2).mpr h₂⟩
  | .thunk _, h, _, _, _, _, _, _ | .ref _, h, _, _, _, _, _, _ | .imm _ _, h, _, _, _, _, _, _
  | .mut _ _, h, _, _, _, _, _, _ | .box _ _, h, _, _, _, _, _, _ | .bang _, h, _, _, _, _, _, _
  | .unk, h, _, _, _, _, _, _ | .tvar _, h, _, _, _, _, _, _ | .mu _, h, _, _, _, _, _, _
  | .fam _, h, _, _, _, _, _, _ | .opq _, h, _, _, _, _, _, _ => by simp [VTy.isFO] at h
/-- **Every host answers at the stated type** (Core's `host_call_sound`), at `vN`: the
signatures are first-order (`hostArg_isFO`, `hostRes_isFO`), where `vN` is Core's `vP`
(`vN_iff_vP`), and Core's lemma reads the rest. -/
theorem host_call_sound (op : HostOp) {δ : LSub} {Θ Θ' : LocTy} {n n' : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) (hostArg op) δ Θ n v ρ) :
    ρ = PMap.empty ∧ ∃ r, ℍ.call op v = some r ∧ vN (ℍ := ℍ) (hostRes op) δ Θ' n' r PMap.empty := by
  obtain ⟨hρ, r, hr, hres⟩ := BoCa.Fig16.LogRel.Core.host_call_sound ℍ op (ls := []) (ls' := [])
    ((vN_iff_vP (hostArg_isFO op)).mp h)
  exact ⟨hρ, r, hr, (vN_iff_vP (hostRes_isFO op)).mpr hres⟩

mutual
/-- **`𝒱⟦A⟧` reads a type only up to `TyEq`** (Core's `vC_tyEq`, `vCE_tyEq`). -/
theorem vNE_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub} (η η' : Option (Nat → TEntN)),
    TyEq S δ S' δ' → EnvEqN η η' δ δ' → vNE (ℍ := ℍ) η S δ = vNE (ℍ := ℍ) η' S' δ'
  | .unit, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      subst h
      funext Θ k v ρ
      simp only [vNE, tEnvPN_eq, (hη _).1]
  | .mu A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (tCloseN η (.mu A)) δ (tCloseN η' (.mu A')) δ' := envEqN_tClose hη h
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN (ℍ := ℍ) (muEnvN η' A' P) b' A' δ' := by
        intro P b'
        have hη' : EnvEqN (muEnvN η A P) (muEnvN η' A' P) δ δ' := fun n => by
          cases n with
          | zero => exact ⟨rfl, hM⟩
          | succ n => exact hη n
        cases b'
        · exact vOE_tyEq A _ _ h hη'
        · exact vNE_tyEq A _ _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu (b := true)).trans (Iff.trans (and_congr (TyEq.noMut_iff A 0 h)
        (and_congr (TyEq.Cl_iff _ 0 hM) (forall_congr' fun P => imp_congr
          (by unfold MuClosedN; simp only [hb]) Iff.rfl))) (vBN_mu (b := true)).symm))
  | .fam A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE, ih]
  | .tensor A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNE_tyEq A η η' h.1 hη
      have ihB := vNE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ihA, ihB]
  | .sum A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vNE_tyEq A η η' h.1 hη
      have ihB := vNE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ihA, ihB]
  | .thunk C, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := cN_tyEq C h
      have hf := forceE_of_cTyEq h
      funext Θ n v ρ; simp only [vNE, ih, hf]
  | .code N E C, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      obtain ⟨rfl, hE, hC⟩ := h
      have ihE := vNE_tyEq E none none hE (envEqN_none _ _)
      have ih := cN_tyEq C hC
      have hf := forceE_of_cTyEq hC
      funext Θ n v ρ; simp only [vNE, ihE, ih, hf]
  | .ref A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE, ih]
  | .bang A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vNE, ih]
  | .box a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ih, h.1]
  | .imm a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      have hw := immWitW_tyEq (envEqN_tClose hη h.2)
      funext Θ n v ρ; simp only [vNE, ih, hw, h.1]
  | .mut a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vNE, ih, h.1]
  termination_by structural x => x
/-- The observable view reads a type only up to `TyEq`. -/
theorem vOE_tyEq : ∀ (S : VTy) {S' : VTy} {δ δ' : LSub} (η η' : Option (Nat → TEntN)),
    TyEq S δ S' δ' → EnvEqN η η' δ δ' → vOE (ℍ := ℍ) η S δ = vOE (ℍ := ℍ) η' S' δ'
  | .unit, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .int w, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .opq k, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; subst h; rfl
  | .zero, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .unk, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .tvar n, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      subst h
      funext Θ k v ρ
      simp only [vOE, tEnvPN_eq, (hη _).1]
  | .mu A, S', δ, δ', η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      rename_i A'
      have hM : TyEq (tCloseN η (.mu A)) δ (tCloseN η' (.mu A')) δ' := envEqN_tClose hη h
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN (ℍ := ℍ) (muEnvN η' A' P) b' A' δ' := by
        intro P b'
        have hη' : EnvEqN (muEnvN η A P) (muEnvN η' A' P) δ δ' := fun n => by
          cases n with
          | zero => exact ⟨rfl, hM⟩
          | succ n => exact hη n
        cases b'
        · exact vOE_tyEq A _ _ h hη'
        · exact vNE_tyEq A _ _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu (b := false)).trans (Iff.trans (and_congr (TyEq.noMut_iff A 0 h)
        (and_congr (TyEq.Cl_iff _ 0 hM) (forall_congr' fun P => imp_congr
          (by unfold MuClosedN; simp only [hb]) Iff.rfl))) (vBN_mu (b := false)).symm))
  | .fam A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE, ih]
  | .tensor A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOE_tyEq A η η' h.1 hη
      have ihB := vOE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ihA, ihB]
  | .sum A B, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ihA := vOE_tyEq A η η' h.1 hη
      have ihB := vOE_tyEq B η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ihA, ihB]
  | .thunk C, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .code N E C, S', _, _, η, η', h, hη => by cases S' <;> simp only [TyEq] at h; rfl
  | .ref A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE, ih]
  | .bang A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h hη
      funext Θ n v ρ; simp only [vOE, ih]
  | .box a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ih, h.1]
  | .imm a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vOE_tyEq A η η' h.2 hη
      have hw := immWitW_tyEq (envEqN_tClose hη h.2)
      funext Θ n v ρ; simp only [vOE, ih, hw, h.1]
  | .mut a A, S', _, _, η, η', h, hη => by
      cases S' <;> simp only [TyEq] at h
      have ih := vNE_tyEq A η η' h.2 hη
      funext Θ n v ρ; simp only [vOE, ih, h.1]
  termination_by structural x => x
/-- **One unfolding reads a type only up to `CTyEq`** (Core's `cB_tyEq`), at closed types for
`X` related at every pair of substitutions. -/
theorem cBN_tyEq (T T' : VTy) (R : CandN) : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub},
    CTyEq C δ C' δ' → (∀ δ₁ δ₂, TyEq T δ₁ T' δ₂) →
    cBN (ℍ := ℍ) T R C δ = cBN (ℍ := ℍ) T' R C' δ'
  | .ret A, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vNE_tyEq A _ _ h (envEqN_nu (P := thunkRN R) (hT _ _))
      funext Θ c n ls e ρ; simp only [cBN, ih]
  | .arr A C, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h.1 (envEqN_none _ _)
      have ihC := cBN_tyEq T T' R C h.2 hT
      funext Θ c n ls e ρ; simp only [cBN, ihA, ihC]
  | .amp C D, C', _, _, h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cBN_tyEq T T' R C h.1 hT
      have ihD := cBN_tyEq T T' R D h.2 hT
      funext Θ c n ls e ρ; simp only [cBN, ihC, ihD]
  | .top, C', _, _, h, _ => by cases C' <;> simp only [CTyEq] at h; rfl
  | .nu C, C', _, _, h, _ => by cases C' <;> simp only [CTyEq] at h; rfl
  | .all x b C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' b' C'
      have hC : ∀ α : Life, cBN (ℍ := ℍ) T R C (δ.extend x α) = cBN (ℍ := ℍ) T' R C' (δ'.extend x' α) :=
        fun α => cBN_tyEq T T' R C (h.2 α) hT
      have hL : ∀ α : Life, LtLife δ b α = LtLife δ' b' α := by
        intro α; unfold LtLife; rw [h.1]
      funext Θ c n ls e ρ; simp only [cBN, hC, hL]
  | .eff n i q A B fin rc C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hTb := tabN_tyEq C hC
      have hR := retNX_tyEq T T' (thunkRN R) C hC (hT _ _)
      have hz := TyEq.isZero_eq B hB
      funext Θ c k ls e ρ; simp only [cBN, entNK, ihA, ihB, ihF, hTb, hR, hz]; rw [capB_congr hz]
  termination_by structural x => x
/-- The answer of a row's layers with one type variable reads a type only up to `CTyEq`. -/
theorem retNX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (C : CTy) {C' : CTy}
    {δ δ' : LSub}, CTyEq C δ C' δ' → TyEq T δ T' δ' →
    retNX (ℍ := ℍ) T P C δ = retNX (ℍ := ℍ) T' P C' δ'
  | .ret A, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A _ _ h (envEqN_nu (P := P) hT)
      funext Θ n v ρ; simp only [retNX, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h, hT => by
      cases C' <;> simp only [CTyEq] at h
      have ih := retNX_tyEq T T' P C h.2.2.2.2.2.2 hT
      funext Θ n v ρ; simp only [retNX, ih]
  | .arr _ _, C', _, _, h, _ | .amp _ _, C', _, _, h, _ | .top, C', _, _, h, _
  | .all _ _ _, C', _, _, h, _ | .nu _, C', _, _, h, _ => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- **`𝒞⟦C⟧` reads a type only up to `CTyEq`** (Core's `cC_tyEq`, `cC_tyEq_aux`). -/
theorem cN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    cN (ℍ := ℍ) C δ = cN (ℍ := ℍ) C' δ'
  | .ret A, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := vNE_tyEq A none none h (envEqN_none _ _)
      funext Θ c n ls e ρ; simp only [cN, ih]
  | .arr A C, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h.1 (envEqN_none _ _)
      have ihC := cN_tyEq C h.2
      funext Θ c n ls e ρ; simp only [cN, ihA, ihC]
  | .amp C D, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h
      have ihC := cN_tyEq C h.1
      have ihD := cN_tyEq D h.2
      funext Θ c n ls e ρ; simp only [cN, ihC, ihD]
  | .top, C', _, _, h => by cases C' <;> simp only [CTyEq] at h; rfl
  | .nu C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i C'
      have hO : C.NuShape ↔ C'.NuShape := CTyEq.nuShape_iff h
      have hB : C.NuShape → ∀ R : CandN, cBN (ℍ := ℍ) (.thunk (.nu C)) R C δ =
          cBN (ℍ := ℍ) (.thunk (.nu C')) R C' δ' := fun hC R => by
        rw [cBN_poly_ty _ .unit R hC.nuLeaf, cBN_poly_ty _ .unit R (hO.mp hC).nuLeaf]
        exact cBN_tyEq .unit .unit R C h (fun _ _ => trivial)
      funext Θ c n ls e ρ
      simp only [cN]
      exact propext ⟨fun k hC' => by
          obtain ⟨R, hR, hr⟩ := k (hO.mpr hC')
          exact ⟨R, by rwa [← hB (hO.mpr hC') R], hr⟩,
        fun k hC => by
          obtain ⟨R, hR, hr⟩ := k (hO.mp hC)
          exact ⟨R, by rwa [hB hC R], hr⟩⟩
  | .all x b C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      rename_i x' b' C'
      have hT : ∀ α : Life, cN (ℍ := ℍ) C (δ.extend x α) = cN (ℍ := ℍ) C' (δ'.extend x' α) :=
        fun α => cN_tyEq C (h.2 α)
      have hL : ∀ α : Life, LtLife δ b α = LtLife δ' b' α := by
        intro α; unfold LtLife; rw [h.1]
      funext Θ c n ls e ρ; simp only [cN, hT, hL]
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hR := retN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c k ls e ρ; simp only [cN, entNK, ihA, ihB, ihF, hT, hR, hz]; rw [capB_congr hz]
  termination_by structural x => x
/-- The table of a row's layers reads a type only up to `CTyEq`. -/
theorem tabN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    tabN (ℍ := ℍ) C δ = tabN (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      funext Θ c; simp only [tabN, entNK, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- The cancel obligation reads a type only up to `CTyEq`. -/
theorem finN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    finN (ℍ := ℍ) C δ = finN (ℍ := ℍ) C' δ'
  | .eff n i q A B fin rc C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨rfl, rfl, rfl, hA, hB, hF, hC⟩ := h
      have ihA := vNE_tyEq A none none hA (envEqN_none _ _)
      have ihB := vNE_tyEq B none none hB (envEqN_none _ _)
      have ihF := finN_tyEq fin hF
      have hT := tabN_tyEq C hC
      have hz := TyEq.isZero_eq B hB
      simp only [finN, entNK, ihA, ihB, ihF, hT, hz]; rw [capB_congr hz]
  | .ret _, C', _, _, h | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
/-- The answer of a row's layers reads a type only up to `CTyEq`. -/
theorem retN_tyEq : ∀ (C : CTy) {C' : CTy} {δ δ' : LSub}, CTyEq C δ C' δ' →
    retN (ℍ := ℍ) C δ = retN (ℍ := ℍ) C' δ'
  | .ret A, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ihA := vNE_tyEq A none none h (envEqN_none _ _)
      funext Θ n v ρ; simp only [retN, ihA]
  | .eff _ _ _ _ _ _ _ C, C', δ, δ', h => by
      cases C' <;> simp only [CTyEq] at h
      have ih := retN_tyEq C h.2.2.2.2.2.2
      funext Θ n v ρ; simp only [retN, ih]
  | .arr _ _, C', _, _, h | .amp _ _, C', _, _, h | .top, C', _, _, h
  | .all _ _ _, C', _, _, h | .nu _, C', _, _, h => by
      cases C' <;> simp only [CTyEq] at h; rfl
  termination_by structural x => x
end

/-- **`𝒱⟦A⟧` reads a type only up to `TyEq`** (Core's `vC_tyEq`). -/
theorem vN_tyEq (S : VTy) {S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    vN (ℍ := ℍ) S δ = vN (ℍ := ℍ) S' δ' :=
  vNE_tyEq S none none h (envEqN_none _ _)

/-- The observable view reads a type only up to `TyEq`. -/
theorem vO_tyEq (S : VTy) {S' : VTy} {δ δ' : LSub} (h : TyEq S δ S' δ') :
    vO (ℍ := ℍ) S δ = vO (ℍ := ℍ) S' δ' :=
  vOE_tyEq S none none h (envEqN_none _ _)

/-- **`vNX` reads a type only up to `TyEq`**, at closed types for `X` related by `TyEq`. -/
theorem vNX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (S : VTy) {S' : VTy}
    {δ δ' : LSub}, TyEq S δ S' δ' → TyEq T δ T' δ' →
    vNX (ℍ := ℍ) T P S δ = vNX (ℍ := ℍ) T' P S' δ' :=
  fun S _ _ _ h hT => vNE_tyEq S _ _ h (envEqN_nu hT)

/-- `vOX` reads a type only up to `TyEq`. -/
theorem vOX_tyEq (T T' : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (S : VTy) {S' : VTy}
    {δ δ' : LSub}, TyEq S δ S' δ' → TyEq T δ T' δ' →
    vOX (ℍ := ℍ) T P S δ = vOX (ℍ := ℍ) T' P S' δ' :=
  fun S _ _ _ h hT => vOE_tyEq S _ _ h (envEqN_nu hT)


private theorem substAll_cons₂ (w₂ w₁ : Val) (γ : List Val) (e : Expr) :
    substAll (w₂ :: w₁ :: γ) e = Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ e)) := by
  show Expr.psub 0 (w₂ :: w₁ :: γ) e = _
  rw [Expr.psub_cons₂ 0 w₂ w₁ γ e, Val.shift_zero]

private theorem substAll_forceE {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v)
    (C : CTy) : substAll γ (forceE C (.var i)) = forceE C (.val v) := by
  cases C with
  | ret A =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var_some hv]; rfl
  | eff n j q A B C =>
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, substAll_var_some hv]; rfl
  | _ => exact substAll_var_some hv

/-! ### The context relation at a slot -/

/-- A dead slot contributes nothing (Core's `gDenC_dead_cons`). -/
theorem gN_dead_cons {δ : LSub} {Θ : LocTy} {n : Nat} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (A : VTy) (v : Val) (hg : gN (ℍ := ℍ) δ Θ Γ γ n ρ) :
    gN (ℍ := ℍ) δ Θ (⟨A, false⟩ :: Γ) (v :: γ) n ρ := by
  simpa [gN] using hg

/-- A live slot beside the rest (Core's `gDenC_mk` at a cons). -/
theorem gN_live_cons {δ : LSub} {Θ : LocTy} {n : Nat} {Γ : Ctx VTy} {A : VTy} {v : Val}
    {γ : List Val} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : vN (ℍ := ℍ) A δ Θ n v ρ₁)
    (hg : gN (ℍ := ℍ) δ Θ Γ γ n ρ₂) : gN (ℍ := ℍ) δ Θ (⟨A, true⟩ :: Γ) (v :: γ) n ρ :=
  by simp only [gN, if_true]; exact ⟨ρ₁, ρ₂, hc, hv, hg⟩

/-- A live slot of `1` gives the context relation with the slot dead (Core's
`gDenC_unit_dead`): a value of `1` holds only `∅`. -/
theorem gN_unit_dead {δ : LSub} {Θ : LocTy} {n : Nat} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (h : gN (ℍ := ℍ) δ Θ (⟨.unit, true⟩ :: Γ) γ n ρ) :
    gN (ℍ := ℍ) δ Θ (⟨.unit, false⟩ :: Γ) γ n ρ := by
  cases γ with
  | nil => exact h
  | cons v γ => exact gN_dead_cons .unit v (gN_cons_persistent (T := .unit) rfl h).2

/-! ### Values -/

/-- **`ID` at `SemJN`** (Core's `var_compatC`). -/
theorem var_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    SemJN (ℍ := ℍ) Δ Γ (.var i) (.val A) := by
  intro δ γ Θ c n ls ρ _ _ _ hlw hg
  obtain ⟨v, hv, hval⟩ := gN_soloP h (h.lt_of_liveWithin hlw) hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.var i)) ρ
  rw [substAll_var_some hv]
  exact erwp_val hval

/-- **`⊗I` at `SemJN`** (Core's `tensorI_compatC`): the split with its parts' consistency
(`gN_splitC`), then `erwp_bind_frame` twice, each later premise read at the index the run
leaves. -/
theorem tensorI_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e₁ e₂ : Expr} {A B : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : SemJN (ℍ := ℍ) Δ Γ₁ e₁ (.val A))
    (h₂ : SemJN (ℍ := ℍ) Δ Γ₂ e₂ (.val B)) :
    SemJN (ℍ := ℍ) Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have hΦ := LocTy.view_down hΘ.1 c
  refine cN_ret_of (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, -⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine erwp_bind_frame hΦ (opTableN_local _) (.pairL .hole (substAll γ e₂))
    (fun σ => gN (ℍ := ℍ) δ Θ Γ₂ γ n σ) hcρ hc (erwp_of_cN_ret (h₁ δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁)) hg₂ ?_
  intro k hk ls' v₁ σ₁ σ₂ σ hcσ hv₁ hg₂' hcσ' hvσ
  refine erwp_bind_frame hΦ (opTableN_local _) (.pairR v₁ .hole)
    (fun τ => vN (ℍ := ℍ) A δ Θ k v₁ τ) (ResU.CompS.comm hcσ) hcσ'
    (erwp_of_cN_ret (h₂ δ γ Θ c k ls' σ₂ hδ hΘ (consistentX_right hcσ hcσ' hvσ) hlw₂ (gN_le hk hg₂'))) hv₁ ?_
  intro k' hk' ls'' v₂ τ₁ τ₂ τ hcτ hv₂ hv₁' _ _
  exact erwp_val (v := Val.pair v₁ v₂)
    ⟨v₁, v₂, τ₂, τ₁, rfl, ResU.CompS.comm hcτ, vN_le hk' hv₁', hv₂⟩

/-- The thunk `λ_. M` of `thunk M : U (F A)` is a value of `U (F A)`: the closure runs at every
extension along `ExtR`, its environment moved there by `gN_extR` (Core's `gDenC_local`). -/
theorem thunkF_sem {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) {δ : LSub} {γ : List Val}
    {Θ : LocTy} {n : Nat} {ρ : WRes} (hδ : Δ.Models δ) (hlw : Ctx.LiveWithin Γ γ)
    (hg : gN (ℍ := ℍ) δ Θ Γ γ n ρ) :
    vN (ℍ := ℍ) (.thunk (.ret A)) δ Θ n (Val.lam (Expr.psub 1 γ M)) ρ := by
  intro Θ' hE hΘ' c' hc' ls'
  refine cN_head (.ret A) δ Θ' hΘ'.1 c' n ls' ρ .hole _ _
    (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 Val.unit (Expr.psub 1 γ M)) = substAll (Val.unit :: γ) M
    from (substAll_cons_psub Val.unit γ M).symm]
  exact h δ (Val.unit :: γ) Θ' c' n ls' ρ hδ hΘ' hc' hlw (gN_dead_cons _ _ (gN_extR hE hg))

/-- **`thunk M : U (F A)` at `SemJN`** (Core's `thunkF_compatC`). -/
theorem thunkF_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.val (.thunk (.ret A))) := by
  intro δ γ Θ c n ls ρ hδ _ _ hlw hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ M))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ M)) (thunkF_sem h hδ hlw hg)

/-- The λ-value `V : C`, `C` not an `F`, is a value of `U C`: it runs at every extension along
`ExtR`, its environment moved there by `gN_extR`. -/
theorem thunkV_sem {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hC : C.isRet = false)
    (h : SemJN (ℍ := ℍ) Δ Γ (.val (.lam N)) (.comp C)) {δ : LSub} {γ : List Val}
    {Θ : LocTy} {n : Nat} {ρ : WRes} (hδ : Δ.Models δ) (hlw : Ctx.LiveWithin Γ γ)
    (hg : gN (ℍ := ℍ) δ Θ Γ γ n ρ) :
    vN (ℍ := ℍ) (.thunk C) δ Θ n (Val.lam (Expr.psub 1 γ N)) ρ := by
  intro Θ' hE hΘ' c' hc' ls'
  rw [forceE_of_not_ret hC]
  exact h δ γ Θ' c' n ls' ρ hδ hΘ' hc' hlw (gN_extR hE hg)

/-- **`thunk V : U C`, `C` not an `F`, at `SemJN`** (Core's `thunkV_compatC`). -/
theorem thunkV_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hC : C.isRet = false)
    (h : SemJN (ℍ := ℍ) Δ Γ (.val (.lam N)) (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam N)) (.val (.thunk C)) := by
  intro δ γ Θ c n ls ρ hδ _ _ hlw hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ N))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ N)) (thunkV_sem hC h hδ hlw hg)

/-! ### Computations -/

/-- **`force x : C` at `SemJN`** (Core's `force_compatC`): the thunk at its own world, `x` at
`U C` or at `Code⟨N; E⟩ C`.  `[spec §68]` -/
theorem force_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {T : VTy} {C : CTy}
    (h : Ctx.SoloP Γ i T) (hT : T.forceTy = some C) :
    SemJN (ℍ := ℍ) Δ Γ (forceE C (.var i)) (.comp C) := by
  intro δ γ Θ c n ls ρ _ hΘ hc hlw hg
  obtain ⟨v, hv, hval⟩ := gN_soloP h (h.lt_of_liveWithin hlw) hg
  -- the slot at `U C`, or at `Code⟨N; E⟩ C` read at its `U C` conjunct  `[spec §68]`
  have hU : vN (ℍ := ℍ) (.thunk C) δ Θ n v ρ := by
    cases T <;> simp only [VTy.forceTy, Option.some.injEq, reduceCtorEq] at hT
    · subst hT; exact hval
    · subst hT; exact hval.2
  show cN (ℍ := ℍ) C δ Θ c n ls (substAll γ (forceE C (.var i))) ρ
  rw [substAll_forceE hv]
  exact hU Θ (LocTy.extR_refl Θ ρ) hΘ c hc ls

/-- **`λx. M : A ⊸ C` at `SemJN`** (Core's `lam_compatC`): the arrow runs at the world and the
view it is applied at; its context is read at the application's index (`gN_le`). -/
theorem lam_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (h : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.comp (.arr A C)) := by
  intro δ γ Θ c n ls ρ hδ hΘ _ hlw hg c' k hk v ρv ρ' hcomp hv hcon
  refine cN_head C δ Θ hΘ.1 c' k ls ρ' .hole _ _ (fun μ => Head.beta μ (Expr.psub 1 γ M) v) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ M)) = substAll (v :: γ) M
    from (substAll_cons_psub v γ M).symm]
  exact h δ (v :: γ) Θ c' k ls ρ' hδ hΘ hcon hlw
    (gN_live_cons (ResU.CompS.comm hcomp) hv (gN_le hk hg))

/-- **`[λ-dead]` at `SemJN`** (Core's `lamDead_compatC`): `[λ]` at the context with `x : 1` live,
whose relation gives the one with `x` dead (`gN_unit_dead`). -/
theorem lamDead_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : SemJN (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.comp (.arr .unit C)) :=
  lam_compatN fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
    h δ γ Θ c n ls ρ hδ hΘ hc (liveWithin_dead hlw) (gN_unit_dead hg)

/-- **`M x : C` at `SemJN`** (Core's `app_compatC`): the function's part of the split is
consistent with the view (`gN_splitC` at a valid resource, `cN_of_valid` at `C`). -/
theorem app_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M : Expr} {i : Nat} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (.arr A C)))
    (hx : Ctx.SoloP Γ₂ i A) : SemJN (ℍ := ℍ) Δ Γ (.app M (.var i)) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_of_valid C δ Θ c n ls _ ρ fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, -⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  obtain ⟨v, hvγ, hval⟩ := gN_soloP hx (hx.lt_of_liveWithin hlw₂) hg₂
  have he : substAll γ (.app M (.var i)) = .app (substAll γ M) (.val v) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.var i)) = _
    rw [← substAll, ← substAll, substAll_var_some hvγ]
  rw [he]
  exact hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁ c n le_rfl v ρ₂ ρ hcρ hval hc

/-- **`M to x. N : C` at `SemJN`** (Core's `bind_compatC`): the context `N` needs is framed
through `M`'s run, together with the stack `C` is eliminated by (`cN_bind`). -/
theorem bind_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (.ret A)))
    (hN : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) M) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind C δ Θ hΘ.1 (.appR (.val (.lam (Expr.psub 1 γ N))) .hole) (substAll γ M)
    (fun k _ v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
    (fun k σ => gN (ℍ := ℍ) δ Θ Γ₂ γ k σ) (fun _ _ _ hk h => gN_le hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => erwp_of_cN_ret (hM δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁)) hg₂ hc
  intro c' k ls' v σ₁ σ₂ σ hcσ hv hg₂' hcσ'
  refine cN_head C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
    from (substAll_cons_psub v γ N).symm]
  exact hN δ (v :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂ (gN_live_cons hcσ hv hg₂')

/-! ### Eliminations of values into computations -/

/-- **`V; M : C` at `SemJN`** (Core's `unitE_compatC`). -/
theorem unitE_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V M : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : SemJN (ℍ := ℍ) Δ Γ₁ V (.val .unit))
    (hM : SemJN (ℍ := ℍ) Δ Γ₂ M (.comp C)) : SemJN (ℍ := ℍ) Δ Γ (.seq V M) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind C δ Θ hΘ.1 (.seq .hole (substAll γ M)) (substAll γ V)
    (fun k _ v ρ => vN (ℍ := ℍ) .unit δ Θ k v ρ) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
    (fun k σ => gN (ℍ := ℍ) δ Θ Γ₂ γ k σ) (fun _ _ _ hk h => gN_le hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => erwp_of_cN_ret (hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁)) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ hcσ ⟨rfl, rfl⟩ hg₂' hcσ'
  rw [eq_of_compS_empty_left hcσ] at hcσ' ⊢
  exact cN_head C δ Θ hΘ.1 c' k ls' σ₂ .hole _ _ (fun μ => Head.seq μ _) rfl
    (hM δ γ Θ c' k ls' σ₂ hδ hΘ hcσ' hlw₂ hg₂')

/-- **`let (x, y) = V in M : C` at `SemJN`** (Core's `tensorE_compatC`). -/
theorem tensorE_compatN {Δ : LifeCtx} {Γ Γp Γb : Ctx VTy} {V M : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γp Γb)
    (hV : SemJN (ℍ := ℍ) Δ Γp V (.val (.tensor A B)))
    (hM : SemJN (ℍ := ℍ) Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.letpair V M) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind C δ Θ hΘ.1 (.letpair .hole (Expr.psub 2 γ M)) (substAll γ V)
    (fun k _ v ρ => vN (ℍ := ℍ) (.tensor A B) δ Θ k v ρ) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
    (fun k σ => gN (ℍ := ℍ) δ Θ Γb γ k σ) (fun _ _ _ hk h => gN_le hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => erwp_of_cN_ret (hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁)) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ hcσ ⟨w₁, w₂, b₁, b₂, rfl, hcb, hw₁, hw₂⟩ hg₂' hcσ'
  refine cN_head C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.letpair μ w₁ w₂ _) rfl ?_
  rw [← substAll_cons₂]
  obtain ⟨x, hx, hxσ⟩ := compS_reassoc hcb hcσ
  obtain ⟨y, hy, hyσ⟩ := compS_lcomm hx hxσ
  exact hM δ (w₂ :: w₁ :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂
    (gN_live_cons hyσ hw₂ (gN_live_cons hy hw₁ hg₂'))

/-- **`case V {inj₁ x. M₁ | inj₂ y. M₂} : C` at `SemJN`** (Core's `sumE_compatC`). -/
theorem sumE_compatN {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {V M₁ M₂ : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γs Γb) (hV : SemJN (ℍ := ℍ) Δ Γs V (.val (.sum A B)))
    (h₁ : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
    (h₂ : SemJN (ℍ := ℍ) Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.case V M₁ M₂) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split hsp hg
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine cN_bind C δ Θ hΘ.1 (.case .hole (Expr.psub 1 γ M₁) (Expr.psub 1 γ M₂)) (substAll γ V)
    (fun k _ v ρ => vN (ℍ := ℍ) (.sum A B) δ Θ k v ρ) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
    (fun k σ => gN (ℍ := ℍ) δ Θ Γb γ k σ) (fun _ _ _ hk h => gN_le hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => erwp_of_cN_ret (hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁)) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ hcσ hsum hg₂' hcσ'
  rcases hsum with ⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩
  · refine cN_head C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.case₁ μ w _ _) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 w (Expr.psub 1 γ M₁)) = substAll (w :: γ) M₁
      from (substAll_cons_psub w γ M₁).symm]
    exact h₁ δ (w :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂ (gN_live_cons hcσ hw hg₂')
  · refine cN_head C δ Θ hΘ.1 c' k ls' σ .hole _ _ (fun μ => Head.case₂ μ w _ _) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 w (Expr.psub 1 γ M₂)) = substAll (w :: γ) M₂
      from (substAll_cons_psub w γ M₂).symm]
    exact h₂ δ (w :: γ) Θ c' k ls' σ hδ hΘ hcσ' hlw₂ (gN_live_cons hcσ hw hg₂')

/-- **`absurd V : C` at `SemJN`** (Core's `zeroE_compatC`): no arm runs. -/
theorem zeroE_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : SemJN (ℍ := ℍ) Δ Γ₁ V (.val .zero)) :
    SemJN (ℍ := ℍ) Δ Γ (absurdE V) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂⟩ := gN_split hsp hg
  obtain ⟨hlw₁, -⟩ := hsp.liveWithin hlw
  refine cN_bind C δ Θ hΘ.1 (.case .hole (.var 0) (.var 0)) (substAll γ V)
    (fun k _ v ρ => vN (ℍ := ℍ) .zero δ Θ k v ρ) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
    (fun k σ => gN (ℍ := ℍ) δ Θ Γ₂ γ k σ) (fun _ _ _ hk h => gN_le hk h) ?_ c n ls ρ₁ ρ₂ ρ hcρ
    (fun c' hc' => erwp_of_cN_ret (hV δ γ Θ c' n ls ρ₁ hδ hΘ hc' hlw₁ hg₁)) hg₂ hc
  rintro c' k ls' v σ₁ σ₂ σ - hv - -
  exact hv.elim

/-! ### `!` and `[@a]` -/

/-- **Promotion of `thunk M : U (F A)` over `!Γ` at `SemJN`** (Core's `bangThunkF_compatC`):
`!Γ` holds nothing (`gN_persistent`). -/
theorem bangThunkF_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} (hp : Ctx.Banged Γ)
    (h : SemJN (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A)))) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ M))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ M)) ⟨gN_persistent hp hg, thunkF_sem h hδ hlw hg⟩

/-- **Promotion of a λ-value `V : C` over `!Γ` at `SemJN`** (Core's `bangThunkV_compatC`). -/
theorem bangThunkV_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (hp : Ctx.Banged Γ)
    (hC : C.isRet = false) (h : SemJN (ℍ := ℍ) Δ Γ (.val (.lam N)) (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam N)) (.val (.bang (.thunk C))) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls (.val (.lam (Expr.psub 1 γ N))) ρ
  exact erwp_val (v := Val.lam (Expr.psub 1 γ N)) ⟨gN_persistent hp hg, thunkV_sem hC h hδ hlw hg⟩

/-- **`[]I` at `SemJN`** (Core's `boxI_compatC`, `boxI_compatX`): `[TR]` 6.62 at the context
(`gN_outlives`), `wp-[]` at the run (`erwp_box`). -/
theorem boxI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {a : Lifetime.Life}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val A)) (hΓ : CtxOutlives Δ Γ a) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.box a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, ha⟩ := hΓ.1 δ hδ
  exact cN_ret_of (erwp_mono (fun _ _ _ _ ⟨hv, hst⟩ => ⟨α, ha, hv, hst⟩) (opTableN_local _) n ls _ ρ
    (erwp_box (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)) (gN_outlives hδ ha hΓ.2 hg)))

/-! ### Literals and host operations -/

/-- **An integer literal at `SemJN`** (Core's `lit_compatX`, `vP_lit`). -/
theorem lit_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (c : IntLit) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val ⟨.prim (.lit c), .prim⟩) (.val (.int c.width)) := by
  intro δ γ Θ c' n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  exact cN_ret_of (erwp_val (v := ⟨.prim (.lit c), .prim⟩) ((vN_iff_vP (ls := []) rfl).mpr (vP_lit c)))

/-- **Every host operation at `SemJN`** (Core's `hostOp_compatX`): one host step, which changes
no memory, answers in the relation at `∅` (`host_call_sound`). -/
theorem hostOp_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (op : HostOp) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim (.host op))) (.val (.bang (hostSig op))) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of (erwp_val (v := Val.prim (.host op)) ⟨rfl, ?_⟩)
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv _
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨rfl, r, hr, hres⟩ := host_call_sound op (Θ' := Θ') (n' := k) hv
  exact cN_ret_of (erwp_det (LocTy.view_down hΘ'.1 c'') (opTableN_down OpTabN.empty_down)
    (fun k _ v ρ h => vN_down _ _ _ k v ρ h)
    (fun μ => step1Only_plug (Head.host μ op v r hr) rfl .hole) (erwp_val hres))

/-! ### Call-by-value application -/

/-- **`f a` at `VTy.lolli` at `SemJN`** (Core's `lolliE_compatX`): `erwp_bind_frame` at the
argument, then at the function, then the function's `U` clause at its own world and the plain
`⊸` at the argument. -/
theorem lolliE_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {f arg : Expr} {T₁ T₂ : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (ha : SemJN (ℍ := ℍ) Δ Γ₁ arg (.val T₁))
    (hf : SemJN (ℍ := ℍ) Δ Γ₂ f (.val (.lolli T₁ T₂))) :
    SemJN (ℍ := ℍ) Δ Γ (.app f arg) (.val T₂) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have hΦ := LocTy.view_down hΘ.1 c
  refine cN_ret_of (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, -⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (substAll γ f) .hole)
    (fun σ => gN (ℍ := ℍ) δ Θ Γ₂ γ n σ) hcρ hc (erwp_of_cN_ret (ha δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁)) hg₂ ?_
  intro k hk ls' v₁ σ₁ σ₂ σ hcσ hv₁ hg₂' hcσ' hvσ
  refine erwp_bind_frame hΦ (opTableN_local _) (.appL .hole v₁)
    (fun τ => vN (ℍ := ℍ) T₁ δ Θ k v₁ τ) (ResU.CompS.comm hcσ) hcσ'
    (erwp_of_cN_ret (hf δ γ Θ c k ls' σ₂ hδ hΘ (consistentX_right hcσ hcσ' hvσ) hlw₂ (gN_le hk hg₂'))) hv₁ ?_
  intro k' hk' ls'' v₂ τ₁ τ₂ τ hcτ hv₂ hv₁' hcτ' hvτ
  exact erwp_of_cN_ret (hv₂ Θ (LocTy.extR_refl _ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'' c k'
    le_rfl v₁ τ₂ τ hcτ (vN_le hk' hv₁') hcτ')

/-! ### `∀E` and `[α]` (L2) -/

/-- **`M [] : C[@a/'x]` at `SemJN`** (Core's `allE_compatC`): `CTyEq.instLife` reads `C[@a/'x]`
at `δ` as `C` at `δ['x ↦ @aδ]`, and `cN_tyEq` carries the relation across. -/
theorem allE_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {x : LifeVar} {b a : Lifetime.Life}
    {C : CTy} (h : SemJN (ℍ := ℍ) Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
    SemJN (ℍ := ℍ) Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have he : substAll γ (.app M (.val .unit)) = .app (substAll γ M) (.val .unit) := by
    show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ (.val .unit)) = _
    simp [Expr.psub, substAll]
  show cN (ℍ := ℍ) (C.instLife x a) δ Θ c n ls (substAll γ (.app M (.val .unit))) ρ
  rw [he, cN_tyEq _ (CTyEq.instLife x a C ha)]
  exact h δ γ Θ c n ls ρ hδ hΘ hc hlw hg α ⟨β, hb, hab⟩

/-- **Call-by-value `∀E` at `SemJN`** (Core's `allE_compatX`): bind the run, then the thunk's
`U` clause at its own world, the `∀` at `@aδ`, and `vN_tyEq` at `TyEq.instLife`. -/
theorem allEV_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {x : LifeVar} {b a : Lifetime.Life}
    {A : VTy} (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
    SemJN (ℍ := ℍ) Δ Γ (.app e (.val .unit)) (.val (VTy.instLife x a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hab⟩ := hlt δ hδ
  have hΦ := LocTy.view_down hΘ.1 c
  have hsub : vN (ℍ := ℍ) (VTy.instLife x a A) δ = vN (ℍ := ℍ) A (δ.extend x α) :=
    vN_tyEq _ (TyEq.instLife x a A ha)
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) _ _ _ n ls ((Kont.appL .hole .unit).plug (substAll γ e)) ρ
  refine erwp_bindR hΦ (opTableN_local _) (.appL .hole .unit) ?_
  refine rwp_mono_le (fun k _ ls' v σ hv => ?_)
    (rwp_consistentXV (rwp_of_erwp_empty (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))) hc)
  obtain ⟨hv, hcσ, -⟩ := hv
  rw [hsub]
  exact erwp_of_cN_ret (hv Θ (LocTy.extR_refl _ _) hΘ c hcσ ls' α ⟨β, hb, hab⟩)

/-- **`[α]` at `SemJN`** (Core's `alpha_compatJ`, `alpha_compatC`): α-equivalent types are one
type (`CTy.alphaB_sound`), and the relation reads a type up to `CTyEq` (`cN_tyEq`). -/
theorem alpha_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ {j j' : Jdg}, j.alphaB j' = true → SemJN (ℍ := ℍ) Δ Γ e j → SemJN (ℍ := ℍ) Δ Γ e j'
  | .val A, .val A', hα, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg => by
      have e := cN_tyEq (ℍ := ℍ) (.ret A) (C' := .ret A')
        (CTy.alphaB_sound (.ret A) (.ret A') (alphaAgree_nil δ) hα)
      show cN (ℍ := ℍ) (.ret A') δ Θ c n ls _ ρ
      rw [← e]
      exact h δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  | .comp C, .comp C', hα, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg => by
      have e := cN_tyEq (ℍ := ℍ) C (C' := C') (CTy.alphaB_sound C C' (alphaAgree_nil δ) hα)
      show cN (ℍ := ℍ) C' δ Θ c n ls _ ρ
      rw [← e]
      exact h δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  | .val _, .comp _, hα, _ | .comp _, .val _, hα, _ => by simp [Jdg.alphaB] at hα

/-- **`⊑mut` at `SemJN`** (`mutSub`, `Core/Fundamental.lean`): Core's `mutSub_compatC` by
`ptoMutS_antitone`. The `Mut` clause's slack `@aδ ⊑ b` absorbs `@aδ ⊑ @bδ`: the cell stays at
its `b`, its key and its uniform conjunct unchanged. -/
theorem mutSub_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.mut a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine cN_ret_of (erwp_mono (fun k _ v ρ hv => ?_) (opTableN_local _) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)))
  obtain ⟨β', hβ', b', hβb', hm, hu⟩ := hv
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  exact ⟨α, ha, b', le_trans (sLe_life hle') hβb', hm, hu⟩

/-- **`⊑imm` at `SemJN`** (`immSub`): Core's `immSub_compatC` by `ptoImmS_antitone`. -/
theorem immSub_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.imm a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine cN_ret_of (erwp_mono (fun k _ v ρ hv => ?_) (opTableN_local _) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)))
  obtain ⟨β', hβ', ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := hv
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  exact ⟨α, ha, ⟨l, s, u, σ, hs, h₁, h₂, le_trans (sLe_life hle') h₃, h₄⟩, hw⟩

/-- `𝒢⟦Γ⟧` does not read `δ` at a variable no live slot mentions. -/
theorem gN_extend_of_not_free {x : LifeVar} (δ : LSub) (α : Life) (Θ : LocTy) :
    ∀ (Γ : Ctx VTy), (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → ∀ γ n ρ,
      gN (ℍ := ℍ) δ Θ Γ γ n ρ → gN (ℍ := ℍ) (δ.extend x α) Θ Γ γ n ρ
  | [], _, _, _, _, h => h
  | _ :: _, _, [], _, _, h => h
  | s :: Γ, hΓ, v :: γ, n, ρ, h => by
      have ih := gN_extend_of_not_free δ α Θ Γ (fun s' hs' => hΓ s' (List.mem_cons_of_mem _ hs'))
      unfold gN at h ⊢
      split
      · rename_i hl
        rw [if_pos hl] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        refine ⟨ρ₁, ρ₂, hc, ?_, ih γ n ρ₂ h₂⟩
        rw [vN_extend_of_not_free (hΓ s (List.mem_cons_self ..) hl)]
        exact h₁
      · rename_i hl
        rw [if_neg hl] at h
        exact ih γ n ρ h

/-- **`∀I` at `SemJN`** (`allI`, `Core/Fundamental.lean`): Core's `allI_compatC`. At every
`α ⊏ @bδ`, `δ[x ↦ α]` models `Δ, 'x ⊏ @b` (the bound and `Δ`'s bounds do not mention `'x`), the
context's reading does not change (`gN_extend_of_not_free`), and the body is one β step away
(`cN_head`). The `∀` clause reads no definedness of `@b`, as Core's `cC`, so the rule needs none. -/
theorem allI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {M : Expr}
    {S : VTy} {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemJN (ℍ := ℍ) (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.comp (.all x b C)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg α hα
  obtain ⟨β, hβ, hlt⟩ := hα
  have hδ' : (Δ.extend x b).Models (δ.extend x α) := by
    intro y u hy
    rw [LifeCtx.find?_extend] at hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨α, β, BoCa.Fig16.LogRel.find?_extend_self δ x α,
        by rw [BoCa.Fig16.LogRel.interp_extend_of_not_mentions hbx]; exact hβ, hlt⟩
    · rw [if_neg hxy] at hy
      obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
      exact ⟨m, k, by rw [BoCa.Fig16.LogRel.find?_extend_ne δ α hxy]; exact hm,
        by rw [BoCa.Fig16.LogRel.interp_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩
  show cN (ℍ := ℍ) C (δ.extend x α) Θ c n ls
    (Kont.hole.plug (.app (.val (.lam (Expr.psub 1 γ M))) (.val .unit))) ρ
  refine cN_head C _ Θ hΘ.1 c n ls ρ .hole _ _
    (fun μ => BoCa.BoLo.Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 Val.unit (Expr.psub 1 γ M)) = substAll (Val.unit :: γ) M
    from (substAll_cons_psub Val.unit γ M).symm]
  exact h (δ.extend x α) (Val.unit :: γ) Θ c n ls ρ hδ' hΘ hc hlw
    (gN_extend_of_not_free δ α Θ Γ hΓx γ n ρ hg)

/-! ### The relation at a family -/

theorem vN_fam_iff {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes} :
    vN (ℍ := ℍ) (.fam L) δ Θ n v ρ ↔
      ∃ l c, v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
        sepRange (fun m => vN (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ := Iff.rfl

theorem vN_fam_mk {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {l : Loc} {c : UInt32} {ρ : WRes}
    (hc : c.toNat < 2 ^ 31) (hs : sepRange (fun m => vN (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ) :
    vN (ℍ := ℍ) (.fam L) δ Θ n (Val.arr l c) ρ :=
  ⟨l, c, rfl, hc, hs⟩

/-- The argument of an operation on a family and an index (Core's `vP_fam_idx`). -/
theorem vN_fam_idx {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.tensor (.fam L) (.int .w32)) δ Θ n v ρ) :
    ∃ l c i, v = Val.pair (Val.arr l c) (Val.i32 i) ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vN (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ := by
  obtain ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, ⟨l, c, rfl, hn, hs⟩, ⟨⟨i, rfl⟩, rfl⟩⟩ := h
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  exact ⟨l, c, i, rfl, hn, hs⟩

/-- An `imm` leaf holds no `own` cell (Core's `noOwn_imm`). -/
theorem noOwn_immN {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.imm a A) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨α, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- A `mut` leaf holds no `own` cell (Core's `noOwn_mut`). -/
theorem noOwn_mutN {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.mut a A) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨α, -, b, -, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- A family of leaves that hold no `own` cell holds none (Core's `noOwn_fam`). -/
theorem noOwn_famN {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat}
    (hL : ∀ m ρ, vN (ℍ := ℍ) L δ Θ n (Val.loc m) ρ → NoOwn ρ) {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.fam L) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨l, c, -, -, hs⟩ := h
  exact sepRange_closed noOwn_empty (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) hL hs


/-! ### Families whose leaves own nothing -/

/-- An `imm` leaf is duplicable (Core's `vP_imm_dup`): the cell composes with itself
(`compS_imm_dup`) and its witness is the cell's. -/
theorem vN_imm_dupN {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.imm a A) δ Θ n v ρ) :
    ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ vN (ℍ := ℍ) (.imm a A) δ Θ n v τ₁ ∧
      vN (ℍ := ℍ) (.imm a A) δ Θ n v τ₂ := by
  obtain ⟨α, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩ := id h
  exact ⟨_, _, compS_imm_dup l s u σ hs, h, h⟩



/-! ### The constants at a dead context, and the adapters -/

/-- **A closed value at a dead context** (Core's `sem_const`): its resource is `∅`. -/
theorem sem_constN {Δ : LifeCtx} {Γ : Ctx VTy} {v : Val} {A : VTy} (hΓ : Ctx.DeadP Γ)
    (hcl : closedAt 0 v.1 = true)
    (h : ∀ (δ : LSub) (Θ : LocTy) (n : Nat), Δ.Models δ → Θ.OK →
      vN (ℍ := ℍ) A δ Θ n v PMap.empty) :
    SemJN (ℍ := ℍ) Δ Γ (.val v) (.val A) := by
  intro δ γ Θ c n ls ρ hδ hΘ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (.val v)) _
  rw [substAll_closed hcl]
  exact erwp_val (h δ Θ n hδ hΘ)
/-! ### Adapters -/

/-- **`return V : F A` at `SemJN`** (Core's `ret_compatC`): `jdgC (.val A)` is `F A`. -/
theorem ret_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ V (.val A)) : SemJN (ℍ := ℍ) Δ Γ V (.comp (.ret A)) := h

/-- **A computation of `F A` is a value-judged expression at `A`** (`fundamentalC`'s `ofRet`). -/
theorem ofRet_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.comp (.ret A))) : SemJN (ℍ := ℍ) Δ Γ e (.val A) := h

/-- **`⟨⟩ : ⊤` at `SemJN`** (Core's `topI_compatC`). -/
theorem topI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} :
    SemJN (ℍ := ℍ) Δ Γ (.val .unit) (.comp .top) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial

/-- **`() : 1` at `SemJN`** (Core's `unitI_compatC`). -/
theorem unitI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val .unit) (.val .unit) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP h hg
  rw [substAll_closed (v := Val.unit) rfl]
  exact cN_ret_of (erwp_val (v := Val.unit) ⟨rfl, rfl⟩)

/-- **`inj₁ e : A ⊕ B` at `SemJN`** (Core's `sumI₁_compatC`). -/
theorem sumI₁_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val A)) : SemJN (ℍ := ℍ) Δ Γ (.inj₁ e) (.val (.sum A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  refine erwp_bind (LocTy.view_down hΘ.1 c) (.inj₁ .hole) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ h => by cases h) (fun k ls' v σ hv => ?_) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))
  exact erwp_val (v := Val.inj₁ v) (Or.inl ⟨v, rfl, hv⟩)

/-- **`inj₂ e : A ⊕ B` at `SemJN`** (Core's `sumI₂_compatC`). -/
theorem sumI₂_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val B)) : SemJN (ℍ := ℍ) Δ Γ (.inj₂ e) (.val (.sum A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  refine erwp_bind (LocTy.view_down hΘ.1 c) (.inj₂ .hole) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ h => by cases h) (fun k ls' v σ hv => ?_) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))
  exact erwp_val (v := Val.inj₂ v) (Or.inr ⟨v, rfl, hv⟩)

private theorem substAll_app_val (γ : List Val) (M : Expr) (w : Val)
    (hw : ∀ k, Expr.psub k γ w.val = w.val) :
    substAll γ (.app M (.val w)) = .app (substAll γ M) (.val w) := by
  show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ w.val) = _
  rw [hw]; rfl

/-- **`π₁ M : C` at `SemJN`** (Core's `proj₁_compatC`). -/
theorem proj₁_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : SemJN (ℍ := ℍ) Δ Γ M (.comp (.amp C D))) :
    SemJN (ℍ := ℍ) Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN (ℍ := ℍ) C δ Θ c n ls (substAll γ (.app M (.val (.inj₁ .unit)))) ρ
  rw [substAll_app_val γ M _ (fun k => by simp [Expr.psub])]
  exact (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg).1

/-- **`π₂ M : D` at `SemJN`** (Core's `proj₂_compatC`). -/
theorem proj₂_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C D : CTy}
    (h : SemJN (ℍ := ℍ) Δ Γ M (.comp (.amp C D))) :
    SemJN (ℍ := ℍ) Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN (ℍ := ℍ) D δ Θ c n ls (substAll γ (.app M (.val (.inj₂ .unit)))) ρ
  rw [substAll_app_val γ M _ (fun k => by simp [Expr.psub])]
  exact (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg).2

/-- **Dereliction at `SemJN`** (Core's `bangE_compatC`): a value of `!A` is one of `A`. -/
theorem bangE_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.bang A))) : SemJN (ℍ := ℍ) Δ Γ e (.val A) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  exact erwp_mono (fun _ _ _ _ hv => hv.2) (opTableN_local _) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))

/-- **`[]E` at `SemJN`** (Core's `boxE_compatC`): a value of `[@a] A` is one of `A`. -/
theorem boxE_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a : Lifetime.Life} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.box a A))) : SemJN (ℍ := ℍ) Δ Γ e (.val A) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine cN_ret_of ?_
  exact erwp_mono (fun _ _ _ _ ⟨_, _, hv, _⟩ => hv) (opTableN_local _) n ls _ ρ
    (erwp_of_cN_ret (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg))

/-- **`SemJN` at a consumed context does not read the slots' types** (Core's `semC_dead`), at a
term no substitution moves. -/
theorem semJN_dead {Δ : LifeCtx} {Γ₁ Γ₂ : Ctx VTy} {e : Expr} {j : Jdg} (h₁ : Ctx.Dead Γ₁)
    (h₂ : Ctx.Dead Γ₂) (he : ∀ γ γ' : List Val, substAll γ e = substAll γ' e)
    (h : SemJN (ℍ := ℍ) Δ Γ₁ e j) : SemJN (ℍ := ℍ) Δ Γ₂ e j := by
  intro δ γ Θ c n ls ρ hδ hΘ hc _ hg
  obtain rfl := (gN_dead h₂).mp hg
  rw [he γ (List.replicate Γ₁.length Val.unit)]
  exact h δ _ Θ c n ls _ hδ hΘ hc (liveWithin_dead_ctx h₁ _) ((gN_dead h₁).mpr rfl)

/-- **A row's markers are not read by the relation** (Core's `semC_effOf_rc`). -/
theorem semJN_effOf_rc {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (h : S.map OpSig.unmark = S'.map OpSig.unmark)
    (hS : SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S A))) :
    SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S' A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN (ℍ := ℍ) (CTy.effOf S' A) δ Θ c n ls _ ρ
  rw [← cN_tyEq (CTy.effOf S A) (CTyEq.effOf_unmark A δ h)]
  exact hS δ γ Θ c n ls ρ hδ hΘ hc hlw hg

/-- **`forget : ? ⊸ 1` at `SemJN`** (Core's `forgetUnk_compatX`): nothing to release. -/
theorem releaseUnk_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ forget (.val axForgetUnkTy) := by
  refine sem_constN (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain rfl := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`forget : !A ⊸ 1` at `SemJN`** (Core's `releaseBang_compatC`): nothing to release. -/
theorem releaseBang_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit)))) := by
  refine sem_constN (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨rfl, -⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`copy : !A ⊸ !A ⊗ !A` at `SemJN`** (Core's `copyBang_compatC`): a value of `!A` holds `∅`. -/
theorem copyBang_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A)))))) := by
  refine sem_constN (v := Val.lam (.pair BoCa.v0 BoCa.v0)) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  have hσ : τ = PMap.empty := hv.1
  subst hσ
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have hb : Kont.hole.plug (Expr.subst 0 v (.pair BoCa.v0 BoCa.v0)) = (Val.pair v v).1 := by
    simp [BoCa.v0, Expr.subst, Kont.plug]
  rw [hb]
  exact erwp_val (v := Val.pair v v)
    ⟨v, v, PMap.empty, PMap.empty, rfl, ResU.comp_empty_right _, hv, hv⟩

/-- **`alloc : A ⊸ Ref A` at `SemJN`** (Core's `alloc_compatX`, `[TR]` 6.141): the new cell
beside the argument's resource. -/
theorem alloc_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A))) := by
  refine sem_constN (v := Val.prim .alloc) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_alloc (Kc := .hole) hΦ (opTableN_local _) v fun l σ₁ σ₂ hcell hc => ?_
  have hσ : σ₁ = ResU.single l (CellU.ownOf v) := hcell
  subst hσ
  exact erwp_val (v := Val.loc l) ⟨l, v, τ, rfl, ResU.CompS.comm hc, vN_le (Nat.sub_le k 1) hv⟩

/-- **`free : Ref A ⊸ A` at `SemJN`** (Core's `free_compatX`, `[TR]` 6.142): the cell freed, its
content's resource returned. -/
theorem free_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A)) := by
  refine sem_constN (v := Val.prim .free) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨l, u, σ', rfl, hcu, hu⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  exact erwp_free (Kc := .hole) hΦ (opTableN_local _) l u
    ⟨_, _, hcu, rfl, erwp_val (vN_le (Nat.sub_le k 1) hu)⟩

/-- **`forget : Imm @a A ⊸ 1` at `SemJN`** (Core's `forgetImm_compatX`, `[TR]` 6.171): an
`imm` cell holds no `own` cell and is let go (`erwp_garbage`). -/
theorem releaseImm_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ forget (.val (axForgetImmTy a A)) := by
  refine sem_constN (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_garbage (compS_empty_left σ) (noOwn_immN hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`forget : Mut @a A ⊸ 1` at `SemJN`** (Core's `forgetMut_compatX`, `[TR]` 6.171): a `mut`
leaf holds no `own` cell and is let go (`erwp_garbage`). -/
theorem releaseMut_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ forget (.val (axForgetMutTy a A)) := by
  refine sem_constN (v := Val.lam unit') hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_garbage (compS_empty_left σ) (noOwn_mutN hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

/-- **`copy : Imm @a A ⊸ Imm @a A ⊗ Imm @a A` at `SemJN`** (Core's `copy_compatX`): the `imm`
cell composes with itself (`vN_imm_dupN`). -/
theorem copy_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ copy (.val (axCopyTy a A)) := by
  refine sem_constN (v := Val.lam (.pair BoCa.v0 BoCa.v0)) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have hb : Kont.hole.plug (Expr.subst 0 v (.pair BoCa.v0 BoCa.v0)) = (Val.pair v v).1 := by
    simp [BoCa.v0, Expr.subst, Kont.plug]
  rw [hb]
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := vN_imm_dupN hv
  exact erwp_val (v := Val.pair v v) ⟨v, v, τ₁, τ₂, rfl, hc, h₁, h₂⟩

private theorem substAll_withPairN (γ : List Val) (M N : Expr) :
    substAll γ (withPair M N) =
      .val (.lam (.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M))
        (.seq (.var 0) (Expr.psub 2 γ N)))) := by
  show Expr.psub 0 γ (.lam _) = _
  simp [Expr.psub]

private theorem withBody_substN (γ : List Val) (M N : Expr) (s : Val) :
    (Expr.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M)) (.seq (.var 0) (Expr.psub 2 γ N))).subst 0 s
      = .case (.val s) (.seq (.var 0) (Expr.psub 1 (s :: γ) M))
          (.seq (.var 0) (Expr.psub 1 (s :: γ) N)) := by
  simp [Expr.subst, Expr.psub_cons 1 s γ]

private theorem seq_subst_unitN (e : Expr) :
    (Expr.seq (.var 0) e).subst 0 Val.unit = .seq (.val .unit) (e.subst 0 Val.unit) := by
  simp [Expr.subst]

/-- **`⟨M, N⟩ : C & D` at `SemJN`** (Core's `withI_compatC`): each projection runs three head
steps (β, `case`, `;`) to its branch, which gets the whole context resource. -/
theorem withI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {M N : Expr} {C D : CTy}
    (hM : SemJN (ℍ := ℍ) Δ (withCtx Γ) M (.comp C))
    (hN : SemJN (ℍ := ℍ) Δ (withCtx Γ) N (.comp D)) :
    SemJN (ℍ := ℍ) Δ Γ (withPair M N) (.comp (.amp C D)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  show cN (ℍ := ℍ) (.amp C D) δ Θ c n ls (substAll γ (withPair M N)) ρ
  rw [substAll_withPairN]
  refine ⟨?_, ?_⟩
  · refine cN_head C δ Θ hΘ.1 c n ls ρ .hole _ _
      (fun μ => Head.beta μ _ (Val.inj₁ Val.unit)) rfl ?_
    simp only [Kont.plug]
    rw [withBody_substN]
    refine cN_head C δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.case₁ μ Val.unit _ _) rfl ?_
    simp only [Kont.plug]
    rw [seq_subst_unitN]
    refine cN_head C δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.seq μ _) rfl ?_
    simp only [Kont.plug]
    rw [← substAll_cons_psub]
    exact hM δ _ Θ c n ls ρ hδ hΘ hc hlw (gN_dead_cons _ _ (gN_dead_cons _ _ hg))
  · refine cN_head D δ Θ hΘ.1 c n ls ρ .hole _ _
      (fun μ => Head.beta μ _ (Val.inj₂ Val.unit)) rfl ?_
    simp only [Kont.plug]
    rw [withBody_substN]
    refine cN_head D δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.case₂ μ Val.unit _ _) rfl ?_
    simp only [Kont.plug]
    rw [seq_subst_unitN]
    refine cN_head D δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.seq μ _) rfl ?_
    simp only [Kont.plug]
    rw [← substAll_cons_psub]
    exact hN δ _ Θ c n ls ρ hδ hΘ hc hlw (gN_dead_cons _ _ (gN_dead_cons _ _ hg))

/-- **`[let-poly]` at `SemJN`** (Core's `letPoly_compatC`): one β step to `N` with the closed
λ-value for its variable, read at a dead slot. -/
theorem letPoly_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} (V : Val)
    (hV : closedAt 0 V.1 = true)
    (hN : SemJN (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 V).shift 1 0) (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) (.val V)) (.comp C) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have h := hN δ (V :: γ) Θ c n ls ρ hδ hΘ hc hlw (gN_dead_cons .unit V hg)
  have e₁ : substAll (V :: γ) ((N.subst 0 V).shift 1 0) = (Expr.psub 1 γ N).subst 0 V := by
    show Expr.psub 0 (V :: γ) _ = _
    rw [psub_fill hV γ N 0, Expr.psub_cons 0 V γ N, Val.shift_zero]
  rw [e₁] at h
  show cN (ℍ := ℍ) C δ Θ c n ls (Expr.psub 0 γ (.app (.val (.lam N)) (.val V))) ρ
  simp only [Expr.psub]
  rw [psub_closedAt V.1 γ hV (Nat.zero_le 0)]
  exact cN_head C δ Θ hΘ.1 c n ls ρ .hole _ _ (fun μ => Head.beta μ (Expr.psub 1 γ N) V) rfl h

/-- **`swap : Ref A ⊸ B ⊸ Ref B ⊗ A` at `SemJN`** (Core's `swap_compatX`): the old payload
loaded, the new one stored, the cell handed back beside the old payload. -/
theorem swap_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ swap (.val (axSwapTy A B)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine cN_ret_of ?_
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ swap) _
  rw [show substAll γ swap = swap from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  refine erwp_val (v := swapV) ?_
  -- the source, at the world the constant's `U` reached
  intro Θ₁ _ hΘ₁ _ _ ls₁ c₂ k₁ _ v₁ τ₀ ρ₁ hcomp hv₁ _
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨l, w, σw, rfl, hcw, hw⟩ := hv₁
  have hΦ₁ : (Θ₁.view c₂).Down := LocTy.view_down hΘ₁.1 c₂
  refine cN_ret_of ?_
  refine erwp_det hΦ₁ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₁ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Expr.val (Val.lam (elet (.app load' BoCa.v1)
        (.seq (.app (.app store' BoCa.v2) BoCa.v1) (.pair BoCa.v2 BoCa.v0)))))) =
      (swapAt l).1 := by
    simp [Kont.plug, elet, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v2, load', store',
      swapAt, Val.loc, Val.lam, Expr.val, Val.prim]
  rw [e₁]
  refine erwp_val (v := swapAt l) ?_
  -- the new payload, at the world the body's `U` reached; the old one arrives there along `ExtR`
  intro Θ₂ hE₂ hΘ₂ _ _ ls₂ c₄ k₂ hk₂ v₂ ρv τ₂ hc₂ hv₂ _
  have hΦ : (Θ₂.view c₄).Down := LocTy.view_down hΘ₂.1 c₄
  have hw₂ : vN (ℍ := ℍ) A δ Θ₂ k₁ w σw := vN_extR A δ k₁ w σw (hE₂.right hcw) hw
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v₂) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 v₂ (elet (eLoad l)
      (.seq (.app (.app store' (.val (.loc l))) BoCa.v1) (.pair (.val (.loc l)) BoCa.v0)))) =
      (Kont.appR (.val (Val.lam (.seq (eStore l (v₂.shift 1 0)) (.pair (.val (.loc l)) BoCa.v0))))
        .hole).plug (eLoad l) := by
    simp [Kont.plug, elet, eLoad, eStore, Expr.subst, BoCa.v0, BoCa.v1, store', Val.loc, Expr.val,
      Val.prim, Val.lam]
  rw [e₂]
  -- `wp-load` of the old payload
  obtain ⟨rest, hrest, hXr⟩ := compS_reassoc hcw hc₂
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_load ls₂ l w _ ⟨_, rest, hXr, rfl, fun ρ₁' ρ₂' hpto hcomp' => ?_⟩
  obtain rfl := hpto
  obtain rfl : τ₂ = ρ₂' := ResU.CompS.functional hXr (ResU.CompS.comm hcomp')
  simp only [Kont.plug]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 w
      (.seq (eStore l (v₂.shift 1 0)) (.pair (.val (.loc l)) BoCa.v0))) =
      (Kont.seq .hole (.pair (.val (.loc l)) (.val w))).plug
        (.app (.val (Val.storeV (Val.loc l))) (.val v₂)) := by
    simp [Kont.plug, eStore, Expr.subst, BoCa.v0, Val.storeV, Val.loc, Expr.val, Val.prim,
      Expr.subst_shift 0 0 0 w v₂.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  rw [e₃]
  -- `wp-store` of the new payload, then the pair
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_store ls₂ l w v₂ _ ⟨_, rest, hXr, rfl, fun t₁ t hpto hct => ?_⟩
  obtain rfl := hpto
  simp only [Kont.plug]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_val (v := Val.pair (Val.loc l) w) ?_
  obtain ⟨cv, hcv, hct'⟩ := compS_reassoc' (ResU.CompS.comm hrest) (ResU.CompS.comm hct)
  exact ⟨Val.loc l, w, cv, σw, rfl, hct',
    ⟨l, v₂, ρv, rfl, hcv, vN_le (by omega) hv₂⟩, vN_le (by omega) hw₂⟩

/-- **The self-reference** (Core's `fixSelf_valid`): with the step a value at `Θ₀` and the index
`n₀`, the self-reference at every budget is a value of `1 ⊕ !U(A ⊸ C)` at every world and every
index up to `n₀`; by induction on the budget. -/
theorem fixSelfN_valid {A : VTy} {C : CTy} {δ : LSub} {Θ₀ : LocTy} {n₀ : Nat} (s : Val)
    (hs : vN (ℍ := ℍ) (fixStepTy A C) δ Θ₀ n₀ s PMap.empty) :
    ∀ (m : Nat) (k : UInt32), k.toNat = m → ∀ (Θ : LocTy) (n : Nat), n ≤ n₀ →
      vN (ℍ := ℍ) (fixSelfTy A C) δ Θ n (fixSelf s k) PMap.empty := by
  intro m
  induction m with
  | zero =>
      intro k hk Θ n _
      have hk0 : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
      unfold fixSelf
      rw [if_pos hk0]
      exact Or.inl ⟨Val.unit, rfl, rfl, rfl⟩
  | succ j ih =>
      intro k hk Θ n hn
      have hk0 : k ≠ 0 := fun h => by subst h; simp at hk
      have hkj : (k - 1).toNat = j := by
        have : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt32.toNat_sub_of_le]
          · rfl
          · rw [UInt32.le_iff_toNat_le]; simp; omega
        omega
      unfold fixSelf
      rw [if_neg hk0]
      refine Or.inr ⟨_, rfl, rfl, fun Θ' _ hΘ' _ _ ls' c' k' hk' x ρx ρ' hc hx hcon => ?_⟩
      obtain rfl := eq_of_compS_empty_left hc
      refine cN_head C δ Θ' hΘ'.1 c' k' ls' ρ' .hole _ _ (fun μ => Head.beta μ _ x) rfl ?_
      simp only [Kont.plug]
      rw [fixSelf_body_subst]
      refine cN_head C δ Θ' hΘ'.1 c' k' ls' ρ' .hole _ _
        (fun μ => Head.boundedFix μ s (k - 1) x) rfl ?_
      exact hs.2 Θ' (LocTy.extR_empty Θ₀ Θ') hΘ' c' (consistentX_empty c') ls' c' k' (by omega)
        (Val.pair (fixSelf s (k - 1)) x) ρ' ρ' (compS_empty_left ρ')
        ⟨fixSelf s (k - 1), x, PMap.empty, ρ', rfl, compS_empty_left ρ',
          ih (k - 1) hkj Θ' k' (by omega), hx⟩ hcon

/-- **`bounded_fix` at `SemJN`** (Core's `boundedFix_compatX`): one `boundedFix` step to the step
on its self-reference (`fixSelfN_valid`) and the argument. -/
theorem boundedFix_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} {C : CTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy A C)) := by
  refine sem_constN (v := Val.prim .boundedFix) hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨s, v₂, σ₁, σ₂, rfl, hc, hs, h₂⟩ := hv
  have e₁ : σ₁ = PMap.empty := hs.1
  subst e₁
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨vk, a, ρk, ρa, rfl, hc₂, ⟨⟨kk, rfl⟩, rfl⟩, ha⟩ := h₂
  obtain rfl := eq_of_compS_empty_left hc₂
  refine cN_head C δ Θ' hΘ'.1 c'' k ls' τ .hole _ _ (fun μ => Head.boundedFix μ s kk a) rfl ?_
  exact hs.2 Θ' (LocTy.extR_refl _ _) hΘ' c'' (consistentX_empty c'') ls' c'' k le_rfl
    (Val.pair (fixSelf s kk) a) τ τ (compS_empty_left τ)
    ⟨fixSelf s kk, a, PMap.empty, τ, rfl, compS_empty_left τ,
      fixSelfN_valid s hs _ kk rfl Θ' k le_rfl, ha⟩ hcon



end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
