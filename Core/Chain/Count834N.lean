import Core.Chain.Rules834N
import Core.CountFold

/-!
# The counted loops at `SemJN`  `[spec §16]`

Core's `countLoop_wp`/`countFold_compatX` and `countTryLoop_wp`/`countTry_compatX`
(`Core/CountFold.lean`), step by step: the induction on `len(n) − i`; one `count` step (here
`erwp_det`); `f (i, s)` by the `!` function's validity (`bang_app`), framed through its run
(`erwp_bind_frame`, the frame `∅`); the loop from `i + 1`, at the index the run leaves.
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

/-- `(i, s)` at `I32 ⊗ S`. -/
theorem vN_i32_pair {S : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} (i : UInt32) {s : Val} {ρ : WRes}
    (hs : vN (ℍ := ℍ) S δ Θ n s ρ) :
    vN (ℍ := ℍ) (.tensor (.int .w32) S) δ Θ n (Val.pair (Val.i32 i) s) ρ :=
  ⟨Val.i32 i, s, PMap.empty, ρ, rfl, compS_empty_left ρ, ⟨⟨i, rfl⟩, rfl⟩, hs⟩

/-- **The loop** (Core's `countLoop_wp`). From `i`, with the state `s` in `𝒱⟦S⟧`, the loop runs
to a state in `𝒱⟦S⟧`, at every index below the function's. By induction on `len(n) − i`. -/
theorem countLoop_wpN {S : VTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {N : Nat} (f : Val)
    (n : UInt32) (hf : vN (ℍ := ℍ) (.bang (.lolli (.tensor (.int .w32) S) S)) δ Θ N f PMap.empty) :
    ∀ (k : Nat) (i : UInt32) (m : Nat) (ls : List SRec) (s : Val) (ρ : WRes)
      (c : Loc → Option Life), m ≤ N → (arrLen n).toNat - i.toNat = k → ConsistentX c ρ →
      vN (ℍ := ℍ) S δ Θ m s ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (fun k _ v ρ => vN (ℍ := ℍ) S δ Θ k v ρ)
        m ls (.app (.val (.prim .count))
          (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))))) ρ := by
  intro k
  induction k with
  | zero =>
      intro i m ls s ρ c _ hk _ hs
      have hΦ := LocTy.view_down hΘ.1 c
      refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
        (fun μ => step1Only_plug (Head.count μ f n i s) rfl .hole) ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      simp only [Kont.plug]
      unfold countNext
      rw [if_neg hi]
      exact erwp_val hs
  | succ k ih =>
      intro i m ls s ρ c hm hk hc hs
      have hΦ := LocTy.view_down hΘ.1 c
      refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
        (fun μ => step1Only_plug (Head.count μ f n i s) rfl .hole) ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [Kont.plug]
      unfold countNext
      rw [if_pos hi]
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.prim .count)) (.pairR f (.pairR (Val.i32 n) (.pairR (Val.i32 (i + 1)) .hole))))
        (fun σ => σ = PMap.empty) (ResU.comp_empty_right ρ) hc
        (bang_app hΘ hm hf hc (vN_i32_pair i hs) ls) rfl ?_
      rintro k' hk' ls' v σ₁ σ₂ σ hcσ hv rfl hcσ' -
      rw [ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)] at hcσ' ⊢
      exact ih (i + 1) k' ls' v σ₁ c (hk'.trans hm) (by omega) hcσ' hv

/-- **`count_fold` at `SemJN`** (Core's `countFold_compatX`), at every host. -/
theorem countFold_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {S : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .count)) (.val (countFoldTy S)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine erwp_val (v := Val.prim .count) ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k hk v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨f, v₂, σ₁, σ₂, rfl, hc, hf, h₂⟩ := hv
  obtain rfl : σ₁ = PMap.empty := hf.1
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨vn, v₃, ρn, ρ₃, rfl, hc₂, ⟨⟨n', rfl⟩, rfl⟩, h₃⟩ := h₂
  obtain rfl := eq_of_compS_empty_left hc₂
  obtain ⟨vi, s, ρi, ρs, rfl, hc₃, ⟨⟨i, rfl⟩, rfl⟩, hs⟩ := h₃
  obtain rfl := eq_of_compS_empty_left hc₃
  exact countLoop_wpN hΘ' f n' hf _ i k ls' s _ c'' le_rfl rfl hcon hs

/-- **The loop with an exit** (Core's `countTryLoop_wp`): `countLoop_wpN`'s induction with one
more case, the step's `inj₂`. -/
theorem countTryLoop_wpN {S E : VTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {N : Nat} (f : Val)
    (n : UInt32)
    (hf : vN (ℍ := ℍ) (.bang (.lolli (.tensor (.int .w32) S) (.sum S E))) δ Θ N f PMap.empty) :
    ∀ (k : Nat) (i : UInt32) (m : Nat) (ls : List SRec) (s : Val) (ρ : WRes)
      (c : Loc → Option Life), m ≤ N → (arrLen n).toNat - i.toNat = k → ConsistentX c ρ →
      vN (ℍ := ℍ) S δ Θ m s ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
        (fun k _ v ρ => vN (ℍ := ℍ) (.sum S E) δ Θ k v ρ)
        m ls (.app (.val (.prim .countTry))
          (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))))) ρ := by
  intro k
  induction k with
  | zero =>
      intro i m ls s ρ c _ hk _ hs
      have hΦ := LocTy.view_down hΘ.1 c
      refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
        (fun μ => step1Only_plug (Head.countTry μ f n i s) rfl .hole) ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      simp only [Kont.plug]
      unfold countTryNext
      rw [if_neg hi]
      exact erwp_val (v := Val.inj₁ s) (Or.inl ⟨s, rfl, hs⟩)
  | succ k ih =>
      intro i m ls s ρ c hm hk hc hs
      have hΦ := LocTy.view_down hΘ.1 c
      have hQd : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.sum S E) δ Θ k v ρ) :=
        fun k _ v ρ h => vN_down _ δ Θ k v ρ h
      refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQd
        (fun μ => step1Only_plug (Head.countTry μ f n i s) rfl .hole) ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [Kont.plug]
      unfold countTryNext
      rw [if_pos hi]
      let e₁ : Expr := .app (.val (.prim .countTry)) (.pair (.val (f.shift 1 0))
        (.pair (.val (.i32 n)) (.pair (.val (.i32 (i + 1))) (.var 0))))
      let e₂ : Expr := .inj₂ (.var 0)
      refine erwp_bind_frame hΦ (opTableN_local _) (.case .hole e₁ e₂)
        (fun σ => σ = PMap.empty) (ResU.comp_empty_right ρ) hc
        (bang_app hΘ hm hf hc (vN_i32_pair i hs) ls) rfl ?_
      rintro k' hk' ls' v σ₁ σ₂ σ hcσ hv rfl hcσ' -
      rw [ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)] at hcσ' ⊢
      rcases hv with ⟨s', rfl, hs₁⟩ | ⟨e, rfl, he₁⟩
      · refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQd
          (fun μ => step1Only_plug (Head.case₁ μ s' e₁ e₂) rfl .hole) ?_
        show erwp (ℍ := ℍ) _ _ _ k' ls' (Expr.subst 0 s' e₁) σ₁
        rw [countTry_cont_subst]
        exact ih (i + 1) k' ls' s' σ₁ c (hk'.trans hm) (by omega) hcσ' hs₁
      · refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQd
          (fun μ => step1Only_plug (Head.case₂ μ e e₁ e₂) rfl .hole) ?_
        exact erwp_val (v := Val.inj₂ e) (Or.inr ⟨e, rfl, he₁⟩)

/-- **`count_try` at `SemJN`** (Core's `countTry_compatX`), at every host. -/
theorem countTry_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {S E : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .countTry)) (.val (countTryTy S E)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  refine erwp_val (v := Val.prim .countTry) ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k hk v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨f, v₂, σ₁, σ₂, rfl, hc, hf, h₂⟩ := hv
  obtain rfl : σ₁ = PMap.empty := hf.1
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨vn, v₃, ρn, ρ₃, rfl, hc₂, ⟨⟨n', rfl⟩, rfl⟩, h₃⟩ := h₂
  obtain rfl := eq_of_compS_empty_left hc₂
  obtain ⟨vi, s, ρi, ρs, rfl, hc₃, ⟨⟨i, rfl⟩, rfl⟩, hs⟩ := h₃
  obtain rfl := eq_of_compS_empty_left hc₃
  exact countTryLoop_wpN hΘ' f n' hf _ i k ls' s _ c'' le_rfl rfl hcon hs

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
