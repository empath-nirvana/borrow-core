import Core.Chain.ImmLend833N
import Core.Integers

/-!
# The lemma interface for `FundamentalN`: the context and bind layer  `[spec §62]`

`docs/new-core/scope-831-interface.md` §2, unit L1. The relation-level lemmas Core's
compatibility proofs (`Core/Compat.lean`, `Core/Compatibility.lean`, `Core/Computation.lean`)
reach for, at the chain (`vN₀`/`cN₀`/`gN₀`/`erwp`), under Core's names with `N` for `C`:

* **G1/G12** `gN_split`, `gN_splitC`: Core's `gDenC_split`, the parts consistent with the view at
  a valid resource; `cN_of_valid`: a computation may assume its resource valid, at every type, so
  a split's consistency holds at a conclusion that is not `F`/`F_Σ`.
* **G2** `gN_soloP`, **G4** `gN_persistent`, **G6** `gN_extR₀`, **G7** `gN_outlives`, **G8**
  `gN_congr`, **G9** `gN_noOwn`, **G11** `gN_le`.
* **K5** `LocTy.extR_empty`: every two worlds are related at `∅` (Core's `ext_empty'`).
* **W4** `erwp_bind_frame`: Core's `wpTS_bind_frame`, the frame carried through the run and read
  at the index the run leaves, the view kept consistent.
* **C2** `cN_bind`: Core's `cC_bind`, by induction on `C`.
* **W7** `erwp_box`: Core's `wpTS_box`.
* **V8** `vN_noOwn_of_ownFree`; **F2** `bang_app`; **F4** `host_call_sound` at `vN₀`.

Core's `⊸` is a plain wand (`cC .arr`), and so is the chain's (`cN₀ .arr`): the argument is read at
the function's own world, at every later index and every view consistent with the composite. The
index is the chain's step index (Core has none); the view is the chain's `ConsistentX` (Core has
none).
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
open BoCa.BoLo (Heap Kont Head)

/-! ### K5: the order at the empty resource -/

/-- **Every two worlds are related at `∅`** (Core's `ext_empty'`): `∅` holds no borrow cell, so
neither conjunct of `ExtR` reads anything. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Chain.SI.LocTy.extR_empty (Θ Θ' : LocTy) :
    Θ.ExtR Θ' PMap.empty :=
  ⟨fun _ _ _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e),
    fun _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e)⟩

/-! ### G11, G6, G8: the context relation down the index, along the order, at agreeing `δ` -/

/-- **`𝒢⟦Γ⟧` at a lower index** (chain only): `vN_le₀` slot by slot. -/
theorem gN_le {δ : LSub} {Θ : LocTy} {k n : Nat} (hkn : k ≤ n) :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ → gN₀ (ℍ := ℍ) δ Θ Γ γ k ρ
  | [], _, _, h => h
  | _ :: _, [], _, h => h
  | s :: Γ, v :: γ, ρ, h => by
      unfold gN₀ at h ⊢
      split
      · rename_i hl
        rw [if_pos hl] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc, vN_le₀ hkn h₁, gN_le hkn h₂⟩
      · rename_i hl
        rw [if_neg hl] at h
        exact gN_le hkn h

/-- **`𝒢⟦Γ⟧` along the resource-relative order** (Core's `gSepC_local`/`gDenC_local`):
`vN_extR₀` slot by slot, the order cut to each slot's part (`ExtR.left`/`.right`). -/
theorem gN_extR₀ {δ : LSub} {Θ Θ' : LocTy} {n : Nat} :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}, Θ.ExtR Θ' ρ →
      gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ → gN₀ (ℍ := ℍ) δ Θ' Γ γ n ρ
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, ρ, hE, h => by
      unfold gN₀ at h ⊢
      split
      · rename_i hl
        rw [if_pos hl] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc, vN_extR₀ s.ty δ n v ρ₁ (hE.left hc) h₁, gN_extR₀ (hE.right hc) h₂⟩
      · rename_i hl
        rw [if_neg hl] at h
        exact gN_extR₀ hE h

/-- **`𝒢⟦Γ⟧` at two `δ` its live slots read alike** (Core's `gSepC_congr`). -/
theorem gN_congr {δ₁ δ₂ : LSub} {Θ : LocTy} :
    ∀ {Γ : Ctx VTy} {γ : List Val},
      (∀ s ∈ Γ, s.live = true → vN₀ (ℍ := ℍ) s.ty δ₁ = vN₀ (ℍ := ℍ) s.ty δ₂) →
      gN₀ (ℍ := ℍ) δ₁ Θ Γ γ = gN₀ (ℍ := ℍ) δ₂ Θ Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vN₀ (ℍ := ℍ) t.ty δ₁ = vN₀ (ℍ := ℍ) t.ty δ₂ :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          funext n ρ
          by_cases hl : s.live
          · simp only [gN₀, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gN₀, if_neg hl, ih htail]

/-! ### G1, G2, G4: the context relation at the splits -/

/-- A persistent live slot holds only at `∅` (Core's `gSepC_cons_persistent`). -/
theorem gN_cons_persistent {δ : LSub} {Θ : LocTy} {n : Nat} {T : VTy} (hT : T.Persistent)
    {Γ : Ctx VTy} {v : Val} {γ : List Val} {ρ : WRes}
    (h : gN₀ (ℍ := ℍ) δ Θ (⟨T, true⟩ :: Γ) (v :: γ) n ρ) :
    vN₀ (ℍ := ℍ) T δ Θ n v PMap.empty ∧ gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ := by
  simp only [gN₀, if_true] at h
  obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
  obtain rfl := vN_empty_of_persistent₀ _ hT hv
  rw [eq_of_compS_empty_left hc]
  exact ⟨hv, hrest⟩

/-- **`Γ = Γ₁, Γ₂` splits `𝒢⟦Γ⟧`; a persistent slot, at `∅`, goes to both sides** (Core's
`gSepC_splitP`, `gDenC_split`). -/
theorem gN_split {δ : LSub} {Θ : LocTy} {n : Nat} :
    ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → ∀ {γ : List Val} {ρ : WRes},
      gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ →
        ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ gN₀ (ℍ := ℍ) δ Θ Γ₁ γ n ρ₁ ∧ gN₀ (ℍ := ℍ) δ Θ Γ₂ γ n ρ₂ := by
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
          simp only [gN₀, if_true, Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hcσ hc
          exact ⟨x, σ₂, hxρ, ⟨ρ₁, σ₁, hx, hv, h₁⟩, h₂⟩
  | right _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, rfl⟩
      | cons v γ' =>
          simp only [gN₀, if_true, Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_lcomm hcσ hc
          exact ⟨σ₁, x, hxρ, h₁, ⟨ρ₁, σ₂, hx, hv, h₂⟩⟩
  | dead _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, rfl⟩
      | cons v γ' =>
          simp only [gN₀, Bool.false_eq_true, if_false] at h ⊢
          exact ih (γ := γ') h
  | dup hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, rfl⟩
      | cons v γ' =>
          obtain ⟨hv, hrest⟩ := gN_cons_persistent hT h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          simp only [gN₀, if_true]
          exact ⟨σ₁, σ₂, hcσ, ⟨PMap.empty, σ₁, compS_empty_left σ₁, hv, h₁⟩,
            ⟨PMap.empty, σ₂, compS_empty_left σ₂, hv, h₂⟩⟩

/-- **The split with the view's consistency at its parts** (G1 with G12, chain only): at a valid
resource consistent with `c`, each part of the split is consistent with `c`
(`consistentX_left`/`_right`). -/
theorem gN_splitC {δ : LSub} {Θ : LocTy} {n : Nat} {Γ Γ₁ Γ₂ : Ctx VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) {γ : List Val} {ρ : WRes} {c : Loc → Option Life}
    (hg : gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ) (hc : ConsistentX c ρ) (hv : ResU.Valid ρ) :
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ gN₀ (ℍ := ℍ) δ Θ Γ₁ γ n ρ₁ ∧ gN₀ (ℍ := ℍ) δ Θ Γ₂ γ n ρ₂ ∧
      ConsistentX c ρ₁ ∧ ConsistentX c ρ₂ := by
  obtain ⟨ρ₁, ρ₂, hcρ, h₁, h₂⟩ := gN_split hsp hg
  exact ⟨ρ₁, ρ₂, hcρ, h₁, h₂, consistentX_left hcρ hc hv, consistentX_right hcρ hc hv⟩

/-- **`ID`'s context, up to persistent slots** (Core's `gSepC_soloP`). -/
theorem gN_soloP {δ : LSub} {Θ : LocTy} {n : Nat} :
    ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.SoloP Γ i T → ∀ {γ : List Val} {ρ : WRes},
      i < γ.length → gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ →
        ∃ v, γ[i]? = some v ∧ vN₀ (ℍ := ℍ) T δ Θ n v ρ := by
  intro Γ i T hs
  induction hs with
  | here hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          simp only [gN₀, if_true] at hg
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [gN_deadP hdead hrest] at hc
          rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
          exact ⟨v, rfl, hv⟩
  | there _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          simp only [gN₀, Bool.false_eq_true, if_false] at hg
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
      gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ → ρ = PMap.empty
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, ρ, hp, h => by
      have hp' : Ctx.Banged Γ := fun t ht hl => hp t (List.mem_cons_of_mem _ ht) hl
      unfold gN₀ at h
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
`vN_outlives₀` at each live slot, folded over the context. -/
theorem gN_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life} {Θ : LocTy} {n : Nat}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) :
    ∀ {Γ : Ctx VTy} {γ : List Val} {ρ : WRes},
      (∀ s ∈ Γ, s.live = true → VOutlives Δ a s.ty) →
      gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ → ρ.InStratum α := by
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
          · simp only [gN₀, if_pos hl] at hg
            obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
            exact inStratum_compS hc
              (vN_outlives₀ hδ ha (hT s (List.mem_cons.mpr (Or.inl rfl)) hl) Θ n v ρ₁ hv)
              (ih hT' hrest)
          · simp only [gN₀, if_neg hl] at hg
            exact ih hT' hg

/-! ### V8, G9: own-free types own nothing -/

/-- **A value of an own-free type owns no cell** (Core's `vC_noOwn_of_ownFree`). -/
theorem vN_noOwn_of_ownFree {A : VTy} (hA : A.OwnFree) :
    ∀ {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes},
      vN₀ (ℍ := ℍ) A δ Θ n v ρ → NoOwn ρ := by
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
      gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ → NoOwn ρ
  | [], _, _, _, h => by rw [h]; exact noOwn_empty
  | _ :: _, [], _, _, h => by rw [h]; exact noOwn_empty
  | s :: Γ, v :: γ, ρ, hd, h => by
      unfold gN₀ at h
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
    (ResU.Valid ρ → cBN₀ (ℍ := ℍ) S Rc D δ Θ c n ls e ρ) → cBN₀ (ℍ := ℍ) S Rc D δ Θ c n ls e ρ
  | .ret _, _, _, _, _, _, _, _, h => erwp_of_valid h
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
  | .eff _ _ _ _ _ _ _ _, _, _, _, _, _, _, _, h => erwp_of_valid h

/-- **A computation may assume its resource valid** (chain only): at `F`/`F_Σ` by
`erwp_of_valid`; at `⊸` because the resource is a part of the composite the wand runs from, and a
part of a valid resource is valid; at `&` and `∀` by their parts; at `ν` by coinduction, the
candidate being the computations valid where their resource is (`cBN_of_valid` at one
unfolding). This is what gives a split's consistency (`gN_splitC`) at a conclusion that is not
`F`/`F_Σ`. -/
theorem cN_of_valid : ∀ (C : CTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes),
    (ResU.Valid ρ → cN₀ (ℍ := ℍ) C δ Θ c n ls e ρ) → cN₀ (ℍ := ℍ) C δ Θ c n ls e ρ
  | .ret _, _, _, _, _, _, _, _, h => erwp_of_valid h
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
      refine ⟨fun Θ c n ls e ρ => ResU.Valid ρ → nuCand₀ (ℍ := ℍ) C δ Θ c n ls e ρ, ?_, h⟩
      intro Θ' c' k ls' e' ρ' hR
      refine cBN_of_valid _ _ C δ Θ' c' k ls' e' ρ' fun hv => ?_
      exact cBN_mono₀ (R' := fun Θ c n ls e ρ => ResU.Valid ρ → nuCand₀ (ℍ := ℍ) C δ Θ c n ls e ρ)
        (fun _ _ _ _ _ _ _ h'' _ => h'') hS.nuLeaf δ Θ' c' k ls' e' ρ'
        (cN_nu_out₀ hS δ Θ' c' k ls' e' ρ' (hR hv))
  | .eff _ _ _ _ _ _ _ _, _, _, _, _, _, _, _, h => erwp_of_valid h

/-! ### W4: bind with a frame -/

/-- **Bind on the sub-expression, frame the rest through the run, then continue** (Core's
`wpTS_bind_frame`, 6.135 with 6.146). The sub-expression runs at the empty table, so its run never
stops (`rwp_of_erwp_empty`) and binds into any table (`erwp_bindR`); the frame goes through it
(`rwp_frame`); the returned resource stays consistent with the view and is valid
(`rwp_consistentXV`). The continuation is read at the index the run leaves, `k ≤ n`. -/
theorem erwp_bind_frame {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) (K : Kont)
    {e : Expr} {P Q : PostN} (R : WProp) {n : Nat} {ls : List SRec} {ρ₁ ρ₂ ρ : WRes}
    {c : Loc → Option Life} (hcρ : ResU.CompS ρ₁ ρ₂ ρ) (hc : ConsistentX c ρ)
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) P n ls e ρ₁) (hR : R ρ₂)
    (h : ∀ k, k ≤ n → ∀ ls' (v : Val) (σ₁ σ₂ σ : WRes), ResU.CompS σ₁ σ₂ σ → P k ls' v σ₁ →
      R σ₂ → ConsistentX c σ → ResU.Valid σ → erwp (ℍ := ℍ) Φ Tb Q k ls' (K.plug v.1) σ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug e) ρ := by
  refine erwp_bindR hΦ hL K ?_
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
      P k ls' v σ₁ → R k σ₂ → ConsistentX c σ → cBN₀ (ℍ := ℍ) S Rc C δ Θ c k ls' (K.plug v.1) σ) →
    ∀ (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ →
      (∀ c', ConsistentX c' ρ₁ → erwp (ℍ := ℍ) (Θ.view c') (opTableN OpTabN.empty) P n ls M ρ₁) →
      R n ρ₂ → ConsistentX c ρ → cBN₀ (ℍ := ℍ) S Rc C δ Θ c n ls (K.plug M) ρ
  | .ret _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      erwp_of_valid fun hv => erwp_bind_frame (LocTy.view_down hΘ c) (opTableN_local _) K (R n)
        hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ')
  | .eff _ _ _ _ _ _ _ _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      erwp_of_valid fun hv => erwp_bind_frame (LocTy.view_down hΘ c) (opTableN_local _) K (R n)
        hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ')
  | .arr A C, δ, Θ, hΘ, K, M, P, hP, R, hR, h, _, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, _ =>
      fun c' k hk v ρv ρ' hcomp hv hcon => by
        obtain ⟨y, hy, hyx⟩ := compS_reassoc hcρ hcomp
        refine cBN_bind S Rc C δ Θ hΘ (.appL K v) M P hP
          (fun j σ => ∃ a b, ResU.CompS a b σ ∧ R j a ∧ vN₀ (ℍ := ℍ) A δ Θ j v b)
          (fun j j' σ hj ⟨a, b, hab, hRa, hvb⟩ => ⟨a, b, hab, hR j j' a hj hRa, vN_le₀ hj hvb⟩)
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
own part (`SemJN₀`'s reading), and `cN_of_valid` gives that part's consistency from the
composite's at each `⊸` the stack passes. -/
theorem cN_bind : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down →
    ∀ (K : Kont) (M : Expr) (P : PostN), P.Down → ∀ (R : Nat → WRes → Prop),
    (∀ k k' ρ, k' ≤ k → R k ρ → R k' ρ) →
    (∀ (c : Loc → Option Life) k ls' (v : Val) (σ₁ σ₂ σ : WRes), ResU.CompS σ₁ σ₂ σ →
      P k ls' v σ₁ → R k σ₂ → ConsistentX c σ → cN₀ (ℍ := ℍ) C δ Θ c k ls' (K.plug v.1) σ) →
    ∀ (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ₁ ρ₂ ρ : WRes),
      ResU.CompS ρ₁ ρ₂ ρ →
      (∀ c', ConsistentX c' ρ₁ → erwp (ℍ := ℍ) (Θ.view c') (opTableN OpTabN.empty) P n ls M ρ₁) →
      R n ρ₂ → ConsistentX c ρ → cN₀ (ℍ := ℍ) C δ Θ c n ls (K.plug M) ρ
  | .ret _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      erwp_of_valid fun hv => erwp_bind_frame (LocTy.view_down hΘ c) (opTableN_local _) K (R n)
        hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ')
  | .eff _ _ _ _ _ _ _ _, _, Θ, hΘ, K, _, _, _, R, hR, h, c, n, _, _, _, _, hcρ, hM, hR₂, hc =>
      erwp_of_valid fun hv => erwp_bind_frame (LocTy.view_down hΘ c) (opTableN_local _) K (R n)
        hcρ hc (hM c (consistentX_left hcρ hc hv)) hR₂
        (fun k hk ls' v σ₁ σ₂ σ hcσ hPv hRσ hcσ' _ =>
          h c k ls' v σ₁ σ₂ σ hcσ hPv (hR n k σ₂ hk hRσ) hcσ')
  | .arr A C, δ, Θ, hΘ, K, M, P, hP, R, hR, h, _, n, ls, ρ₁, ρ₂, ρ, hcρ, hM, hR₂, _ =>
      fun c' k hk v ρv ρ' hcomp hv hcon => by
        obtain ⟨y, hy, hyx⟩ := compS_reassoc hcρ hcomp
        refine cN_bind C δ Θ hΘ (.appL K v) M P hP
          (fun j σ => ∃ a b, ResU.CompS a b σ ∧ R j a ∧ vN₀ (ℍ := ℍ) A δ Θ j v b)
          (fun j j' σ hj ⟨a, b, hab, hRa, hvb⟩ => ⟨a, b, hab, hR j j' a hj hRa, vN_le₀ hj hvb⟩)
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
      (cN_nu_unfold₀ hS δ Θ c n ls _ ρ).mpr (cBN_bind _ _ C δ Θ hΘ K M P hP R hR
        (fun c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ' =>
          (cN_nu_unfold₀ hS δ Θ c' k ls' _ σ).mp (h c' k ls' w σ₁ σ₂ σ hcσ hPw hRσ hcσ'))
        c n ls ρ₁ ρ₂ ρ hcρ hM hR₂ hc) hS

/-! ### W7: a run from `Res_α` ends in `Res_α` -/

/-- **`[TR]` 6.147 (`wp-box`) at `rwp`** (Core's `wpTS_box`): `↭` keeps the strata
(`updVN_inStratum`), and the returned resource is a part of its right side. -/
theorem rwp_box {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    {α : Life} (h : rwp (ℍ := ℍ) Φ Q n ls e ρ) (hρ : ρ.InStratum α) :
    rwp (ℍ := ℍ) Φ (fun k ls v ρ' => Q k ls v ρ' ∧ ρ'.InStratum α) n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
  obtain ⟨hval, hprog⟩ := h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
  refine ⟨fun v hv => ?_, hprog⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := hval v hv
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, ResU.CompS.inStratum_left h₆ (updVN_inStratum hρ h₇)⟩

/-- **`wp-box` at `erwp` at the empty table**: a run that never stops is an `rwp` run. -/
theorem erwp_box {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    {α : Life} (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e ρ) (hρ : ρ.InStratum α) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun k ls v ρ' => Q k ls v ρ' ∧ ρ'.InStratum α)
      n ls e ρ :=
  erwp_of_rwp (rwp_box (rwp_of_erwp_empty h) hρ)

/-! ### F2: a `!`-function applied at a later world -/

/-- **A `!`-function is a function at every world, and applies** (Core's `bang_app`): `!` owns
nothing, so every world is an extension at its resource (`LocTy.extR_empty`); the `⊸` clause is
then read at the argument's world, index and view. -/
theorem bang_app {A B : VTy} {δ : LSub} {Θ Θ' : LocTy} (hΘ' : Θ'.OK) {n k : Nat} (hk : k ≤ n)
    {f v : Val} {ρv : WRes} (hf : vN₀ (ℍ := ℍ) (.bang (.lolli A B)) δ Θ n f PMap.empty)
    {c : Loc → Option Life} (hc : ConsistentX c ρv) (hv : vN₀ (ℍ := ℍ) A δ Θ' k v ρv)
    (ls : List SRec) :
    erwp (ℍ := ℍ) (Θ'.view c) (opTableN OpTabN.empty) (fun k _ w ρ => vN₀ (ℍ := ℍ) B δ Θ' k w ρ)
      k ls (.app (.val f) (.val v)) ρv :=
  hf.2 Θ' (LocTy.extR_empty Θ Θ') hΘ' c (consistentX_empty c) ls c k hk v ρv ρv
    (compS_empty_left ρv) hv hc

/-! ### F4: the host operations at `vN₀` -/

/-- **The first-order value types**: `1`, `0`, the integer widths, `⊗`, `⊕`. The host operations'
signatures (`hostArg`, `hostRes`) are among them. -/
def _root_.BoCa.Fig16.LogRel.Core.VTy.isFO : VTy → Bool
  | .unit | .zero | .int _ => true
  | .tensor A B | .sum A B => A.isFO && B.isFO
  | _ => false

/-- **At a first-order type `vN₀` is Core's `vP`**, at every world, index and list: the clauses
are Core's with `⋆` written as `ResU.CompS` and `⌜p⌝` as `p ∧ ρ = ∅` (F1). -/
theorem vN_iff_vP : ∀ {A : VTy}, A.isFO = true → ∀ {δ : LSub} {Θ : LocTy} {n : Nat}
    {ls : List SRec} {v : Val} {ρ : WRes}, vN₀ (ℍ := ℍ) A δ Θ n v ρ ↔ vP A ls δ v ρ
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

theorem isFO_intOnly {w : Width} {A : VTy} (h : A.isFO = true) : (intOnly w A).isFO = true := by
  cases w <;> first | exact h | rfl

theorem hostArg_isFO (op : HostOp) : (hostArg op).isFO = true := by
  cases op <;> simp only [hostArg] <;> first | rfl | exact isFO_intOnly rfl

theorem hostRes_isFO (op : HostOp) : (hostRes op).isFO = true := by
  cases op <;> rfl

/-- **Every host answers at the stated type** (Core's `host_call_sound`), at `vN₀`: the
signatures are first-order (`hostArg_isFO`, `hostRes_isFO`), where `vN₀` is Core's `vP`
(`vN_iff_vP`), and Core's lemma reads the rest. -/
theorem host_call_sound (op : HostOp) {δ : LSub} {Θ Θ' : LocTy} {n n' : Nat} {v : Val}
    {ρ : WRes} (h : vN₀ (ℍ := ℍ) (hostArg op) δ Θ n v ρ) :
    ρ = PMap.empty ∧ ∃ r, ℍ.call op v = some r ∧ vN₀ (ℍ := ℍ) (hostRes op) δ Θ' n' r PMap.empty := by
  obtain ⟨hρ, r, hr, hres⟩ := BoCa.Fig16.LogRel.Core.host_call_sound ℍ op (ls := []) (ls' := [])
    ((vN_iff_vP (hostArg_isFO op)).mp h)
  exact ⟨hρ, r, hr, (vN_iff_vP (hostRes_isFO op)).mpr hres⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
