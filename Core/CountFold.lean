import Core.Arrays

/-!
# Core — the counted loop  `[spec §16]`

`count_fold : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S)`, the primitive `count`: from
`(f, (n, (i, s)))` it runs `f` at `i, i + 1, …, len(n) − 1`, threading the state, and answers the
last state (`s` itself when `i ≥ len(n)`). `len(n)` is `tab`'s: `n` when `n < 2³¹`, else `0`.

The machine counts (`Head.count`, `countNext`): each step compares `i` with `len(n)` and adds one
in the machine itself, not through the host. That is what makes the loop total at every host.
A loop that counts with the host's `add` and `lt_u` terminates only at hosts whose operations
count, and every theorem here holds at every host (SPEC §8).

`countLoop_wp` is the induction on `len(n) − i`: one `count` step, then `f (i, s)` by the `!`
function's validity (`bang_app`), then the loop from `i + 1`. `countFold_compatX` is the
constant.

`count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)`, the primitive `countTry`, is the
same loop with an exit: the step answers `inj₁` of the next state, and the loop goes on, or
`inj₂ e`, and the loop answers `inj₂ e` at once; at the bound it answers `inj₁` of the last state
(`Head.countTry`, `countTryNext`). `countTryLoop_wp` is `countLoop_wp`'s induction with one more
case, and `countTry_compatX` the constant.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `count_fold : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S)`.  `[spec §16]` -/
abbrev countFoldTy (S : VTy) : VTy :=
  .bang (.lolli (.tensor (.bang (.lolli (.tensor (.int .w32) S) S))
    (.tensor (.int .w32) (.tensor (.int .w32) S))) S)

/-- The `count` step.  `[spec §16]` -/
theorem wpTS_count (ls : List SRec) (f : Val) (n i : UInt32) (s : Val)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (countNext f n i s) Q)
      (wpTS ls (.app (.val (.prim .count))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))))) Q) :=
  wpTS_head (fun μ => Head.count μ f n i s) rfl ls Q

/-- **The loop.** From `i`, with the state `s` in `𝒱⟦S⟧`, the loop runs to a state in `𝒱⟦S⟧`.
By induction on `len(n) − i`.  `[spec §16]` -/
theorem countLoop_wp {S : VTy} {δ : LSub} {ls₀ : List SRec} (f : Val) (n : UInt32)
    (hf : vP (.bang (.lolli (.tensor (.int .w32) S) S)) ls₀ δ f PMap.empty) :
    ∀ (k : Nat) (i : UInt32) (ls : List SRec) (s : Val) (ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      (arrLen n).toNat - i.toNat = k → vP S ls δ s ρ →
      wpTS ls (.app (.val (.prim .count))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))))
        (fun ls' => vP S ls' δ) ρ := by
  intro k
  induction k with
  | zero =>
      intro i ls s ρ _ hk hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      unfold countNext
      rw [if_neg hi]
      exact wpTS_val ls s _ ρ hs
  | succ k ih =>
      intro i ls s ρ hls hk hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      unfold countNext
      rw [if_pos hi]
      refine wpTS_bind_frame
        (.appR (.val (.prim .count)) (.pairR f (.pairR (Val.i32 n) (.pairR (Val.i32 (i + 1)) .hole))))
        (.app (.val f) (.val (Val.pair (Val.i32 i) s))) ls (fun ls' => vP S ls' δ) (fun _ => emp) _
        (fun _ _ _ h => h) ?_ ρ
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ,
          bang_app hf hls ⟨Val.i32 i, s, pure_sep_mk rfl
            ⟨PMap.empty, ρ, compS_empty_left ρ, vP_i32 i, hs⟩⟩, ⟨rfl, trivial⟩⟩
      rintro ls' hls' v σ ⟨σ₁, σ₂, hc, hv, ⟨rfl, -⟩⟩
      rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
      exact ih (i + 1) ls' v σ₁ (fun x => (hls' x).trans (hls x)) (by omega) hv

/-- **`count_fold` is sound**, at every host.  `[spec §16]` -/
theorem countFold_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {S : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .count)) (countFoldTy S) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨f, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, hf, h₂⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hf.1
  subst e₁
  rw [eq_of_compS_empty_left hc]
  obtain ⟨vn, v₃, hk₂⟩ := h₂
  obtain ⟨rfl, ρn, ρ₃, hc₂, ⟨en, n, rfl⟩, h₃⟩ := pure_sep_iff.mp hk₂
  subst en
  rw [eq_of_compS_empty_left hc₂]
  obtain ⟨vi, s, hk₃⟩ := h₃
  obtain ⟨rfl, ρi, ρs, hc₃, ⟨ei, i, rfl⟩, hs⟩ := pure_sep_iff.mp hk₃
  subst ei
  rw [eq_of_compS_empty_left hc₃]
  exact countLoop_wp f n hf _ i ls' s ρs (fun _ => Iff.rfl) rfl hs

/-- `count_try : !(!(I32 ⊗ S ⇒ S ⊕ E) ⊗ (I32 ⊗ (I32 ⊗ S)) ⇒ S ⊕ E)`.  `[spec §16]` -/
abbrev countTryTy (S E : VTy) : VTy :=
  .bang (.lolli (.tensor (.bang (.lolli (.tensor (.int .w32) S) (.sum S E)))
    (.tensor (.int .w32) (.tensor (.int .w32) S))) (.sum S E))

/-- The `countTry` step.  `[spec §16]` -/
theorem wpTS_countTry (ls : List SRec) (f : Val) (n i : UInt32) (s : Val)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (countTryNext f n i s) Q)
      (wpTS ls (.app (.val (.prim .countTry))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))))) Q) :=
  wpTS_head (fun μ => Head.countTry μ f n i s) rfl ls Q

/-- The continuation of `countTryNext` after the step, at `inj₁ s′`: the loop from `i + 1`. The
shifted step is the step again once the binder is filled. -/
theorem countTry_cont_subst (f : Val) (n i : UInt32) (s' : Val) :
    Expr.subst 0 s' (.app (.val (.prim .countTry)) (.pair (.val (f.shift 1 0)) (.pair (.val (.i32 n))
        (.pair (.val (.i32 i)) (.var 0)))))
      = .app (.val (.prim .countTry))
          (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s')))) := by
  have hf : Expr.subst 0 s' ((f.shift 1 0).val) = f.val := by
    rw [Val.val_shift, Expr.subst_shift 0 0 0 s' f.val (Nat.le_refl 0) (Nat.zero_le _),
      Expr.shift_zero]
  simp only [Expr.val, Expr.subst, if_pos, Val.i32] at hf ⊢
  rw [hf]
  rfl

/-- **The loop with an exit.** From `i`, with the state `s` in `𝒱⟦S⟧`, the loop answers a value
in `𝒱⟦S ⊕ E⟧`: `inj₁` of the state at the bound, or the step's first `inj₂`. By induction on
`len(n) − i`.  `[spec §16]` -/
theorem countTryLoop_wp {S E : VTy} {δ : LSub} {ls₀ : List SRec} (f : Val) (n : UInt32)
    (hf : vP (.bang (.lolli (.tensor (.int .w32) S) (.sum S E))) ls₀ δ f PMap.empty) :
    ∀ (k : Nat) (i : UInt32) (ls : List SRec) (s : Val) (ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      (arrLen n).toNat - i.toNat = k → vP S ls δ s ρ →
      wpTS ls (.app (.val (.prim .countTry))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))))
        (fun ls' => vP (.sum S E) ls' δ) ρ := by
  intro k
  induction k with
  | zero =>
      intro i ls s ρ _ hk hs
      refine wpTS_countTry ls f n i s _ ρ ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      unfold countTryNext
      rw [if_neg hi]
      exact wpTS_val ls (Val.inj₁ s) _ ρ (Or.inl ⟨s, pure_sep_mk rfl hs⟩)
  | succ k ih =>
      intro i ls s ρ hls hk hs
      refine wpTS_countTry ls f n i s _ ρ ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      unfold countTryNext
      rw [if_pos hi]
      let e₁ : Expr := .app (.val (.prim .countTry)) (.pair (.val (f.shift 1 0))
        (.pair (.val (.i32 n)) (.pair (.val (.i32 (i + 1))) (.var 0))))
      let e₂ : Expr := .inj₂ (.var 0)
      refine wpTS_bind_frame (.case .hole e₁ e₂)
        (.app (.val f) (.val (Val.pair (Val.i32 i) s))) ls (fun ls' => vP (.sum S E) ls' δ)
        (fun _ => emp) _ (fun _ _ _ h => h) ?_ ρ
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ,
          bang_app hf hls ⟨Val.i32 i, s, pure_sep_mk rfl
            ⟨PMap.empty, ρ, compS_empty_left ρ, vP_i32 i, hs⟩⟩, ⟨rfl, trivial⟩⟩
      rintro ls' hls' v σ ⟨σ₁, σ₂, hc, hv, ⟨rfl, -⟩⟩
      rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
      rcases hv with ⟨s', hs'⟩ | ⟨e, he⟩
      · obtain ⟨rfl, hs₁⟩ := pure_sep_iff.mp hs'
        refine wpTS_sum₁ ls' s' e₁ e₂ _ σ₁ ?_
        show wpTS ls' (Expr.subst 0 s' e₁) _ σ₁
        rw [countTry_cont_subst]
        exact ih (i + 1) ls' s' σ₁ (fun x => (hls' x).trans (hls x)) (by omega) hs₁
      · obtain ⟨rfl, he₁⟩ := pure_sep_iff.mp he
        refine wpTS_sum₂ ls' e e₁ e₂ _ σ₁ ?_
        exact wpTS_val ls' (Val.inj₂ e) _ σ₁ (Or.inr ⟨e, pure_sep_mk rfl he₁⟩)

/-- **`count_try` is sound**, at every host.  `[spec §16]` -/
theorem countTry_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {S E : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .countTry)) (countTryTy S E) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨f, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, hf, h₂⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hf.1
  subst e₁
  rw [eq_of_compS_empty_left hc]
  obtain ⟨vn, v₃, hk₂⟩ := h₂
  obtain ⟨rfl, ρn, ρ₃, hc₂, ⟨en, n, rfl⟩, h₃⟩ := pure_sep_iff.mp hk₂
  subst en
  rw [eq_of_compS_empty_left hc₂]
  obtain ⟨vi, s, hk₃⟩ := h₃
  obtain ⟨rfl, ρi, ρs, hc₃, ⟨ei, i, rfl⟩, hs⟩ := pure_sep_iff.mp hk₃
  subst ei
  rw [eq_of_compS_empty_left hc₃]
  exact countTryLoop_wp f n hf _ i ls' s ρs (fun _ => Iff.rfl) rfl hs

end BoCa.Fig16.LogRel.Core

end
