import NestedFold.Dispatch

/-!
# NestedFold — the owned traversal of an array

At `[Ref S]` the traversal is a `count` loop over the slots (design §4.3): the state is
`(acc, (w, s))`, and the invariant `ArrInv k` holds the accumulator in `𝒱⟦R_a⟧` beside the slots
`k, …, n − 1` not yet visited, whose cells are below the bound. One step (`step_spec`) takes the
`k`-th slot by `idx`, frees it (`wpTS_free`), traverses its content at a smaller resource
(`dsize_tail_lt`), and gives `inj₂ (acc, r)` to the algebra. `arr_spec` is the seed
`g (inj₁ ())`, the loop (`countLoop_inv`), and the accumulator.

The content's traversal is a hypothesis (`hS`), at every resource below the bound: the caller
is the generic traversal's own induction.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.NestedFold
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

-- Every reduction below normalises with one list of closedness facts; not every step uses each.
set_option linter.unusedSimpArgs false

theorem arr_closed (ℓ : Loc) (N : UInt32) : closedAt 0 (Val.arr ℓ N).1 = true := rfl

/-- An algebra applied: `g r` runs to a value of `R`. -/
theorem alg_app {A R : VTy} {δ : LSub} {g r : Val} {ρ : WRes} {ls : List SRec}
    (hg : ∀ ls, vC true (.bang (.lolli A R)) ls δ g PMap.empty) (hr : vP A ls δ r ρ) :
    wpTS ls (.app (.val g) (.val r)) (fun ls' => vP R ls' δ) ρ := by
  obtain ⟨-, hthunk⟩ := hg ls
  exact hthunk ls (Ext.refl _ _) r ρ ρ hr (ResU.CompS.comm (ResU.comp_empty_right ρ))

section
variable {S' RS RA : VTy} {δ : LSub}

/-- The slots `ℓ, …, ℓ + k − 1` of an array of `Ref S'`. -/
abbrev slots (S' : VTy) (ls : List SRec) (δ : LSub) (ℓ : Loc) (k : Nat) : WProp :=
  sepRange (fun m => vP (.ref S') ls δ (.loc m)) ℓ k

/-- **The loop's invariant** before the `k`-th step. -/
def ArrInv (S' RA : VTy) (δ : LSub) (w s : Val) (ℓ : Loc) (N : Nat) (n : Nat) (k : Nat)
    (ls : List SRec) (st : Val) : WProp := fun ρ =>
  ∃ acc, st = Val.pair acc (Val.pair w s) ∧
    (vP RA ls δ acc ⋆ fun ρ' => slots S' ls δ (ℓ + k) (N - k) ρ' ∧ dsize ρ' ≤ n) ρ

theorem slots_same {S' : VTy} {ls ls' : List SRec} {δ : LSub} (hls : ∀ x, x ∈ ls' ↔ x ∈ ls)
    {ℓ : Loc} {k : Nat} {ρ : WRes} (h : slots S' ls δ ℓ k ρ) : slots S' ls' δ ℓ k ρ :=
  sepRange_mono' (fun _ _ h => vP_same hls h) h

/-- **One step of the loop.** -/
theorem step_spec {t g s : Val} (ht : closedAt 0 t.1 = true) (hg : closedAt 0 g.1 = true)
    (hs : closedAt 0 s.1 = true) {n : Nat} {ℓ : Loc} {N : UInt32} (hN : N.toNat < 2 ^ 31)
    (hS : ∀ v ρ ls, vP S' ls δ v ρ → dsize ρ < n →
      wpTS ls (.app (.app (.val t) (.val s)) (.val v)) (fun ls' => vP RS ls' δ) ρ)
    (hgA : ∀ ls, vC true (.bang (.lolli (.sum .unit (.tensor RA RS)) RA)) ls δ g PMap.empty)
    (i : UInt32) (hi : i < arrLen N) (ls : List SRec) (st : Val) :
    Entails (ArrInv S' RA δ (Val.arr ℓ N) s ℓ N.toNat n i.toNat ls st)
      (wpTS ls (.app (.val (stepV t g)) (.val (Val.pair (Val.i32 i) st)))
        (fun ls' => ArrInv S' RA δ (Val.arr ℓ N) s ℓ N.toNat n (i.toNat + 1) ls')) := by
  rintro ρ ⟨acc, rfl, ρa, ρr, hc, hacc, hsl, hdr⟩
  rw [arrLen_of_bound hN] at hi
  have hiN : i.toNat < N.toNat := UInt32.lt_iff_toNat_lt.mp hi
  have esub : N.toNat - i.toNat = (N.toNat - (i.toNat + 1)) + 1 := by omega
  rw [esub] at hsl
  unfold slots at hsl
  rw [sepRange_succ] at hsl
  obtain ⟨ρsl, ρre, hcr, hslot, hrest⟩ := hsl
  obtain ⟨l', v, hsv⟩ := hslot
  obtain ⟨el, ρc, ρb, hcb, hown, hv⟩ := pure_sep_iff.mp hsv
  have hl' : l' = ℓ + i.toNat := (Val.loc_inj.mp el).symm
  subst hl'
  have hlt : dsize ρb < n := by
    have h₁ : dsize ρb < dsize ρsl := by
      rw [hown] at hcb
      exact dsize_tail_lt hcb ⟨PMap.empty, ResU.comp_empty_right _⟩
    have h₂ := dsize_le_left hcr
    omega
  have hre : dsize ρre ≤ n := le_trans (dsize_le_right hcr) hdr
  -- the pure steps to the `idx`
  refine wpTS_lolli ls _ _ _ ρ ?_
  simp only [stepE]
  refine wpTS_tensor ls (Val.i32 i) (Val.pair acc (Val.pair (Val.arr ℓ N) s)) _ _ ρ ?_
  simp [bindE, closed_subst ht, closed_subst hg, closed_subst hs, closed_shift ht, closed_shift hg,
    closed_shift hs]
  refine wpTS_tensor ls acc (Val.pair (Val.arr ℓ N) s) _ _ ρ ?_
  simp [bindE, closed_subst ht, closed_subst hg, closed_subst hs, closed_shift ht, closed_shift hg,
    closed_shift hs]
  refine wpTS_tensor ls (Val.arr ℓ N) s _ _ ρ ?_
  simp [bindE, closed_subst ht, closed_subst hg, closed_subst hs, closed_shift ht, closed_shift hg,
    closed_shift hs, subst_shift_succ, closed_shift (arr_closed ℓ N)]
  -- `idx`, then the `inj₁` branch
  refine wpTS_bind (.case .hole _ _)
    (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ N) (Val.i32 i)))) ls _ ρ ?_
  refine wpTS_idx ls ℓ N i _ ρ ?_
  rw [idxAns_lt ℓ hi]
  refine wpTS_val ls _ _ ρ ?_
  simp only [Kont.plug]
  refine wpTS_sum₁ ls (Val.loc (ℓ + i.toNat)) _ _ _ ρ ?_
  simp [closed_subst ht, closed_subst hg, closed_subst hs, closed_shift ht, closed_shift hg,
    closed_shift hs, subst_shift_succ, closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- the resource: the slot's cell, its content, and the frame `acc ⋆ rest`
  obtain ⟨ab₁, h₁, h₂⟩ := compS_reassoc' hcr hc
  obtain ⟨F, hF, hρF⟩ := compS_reassoc (ResU.CompS.comm h₁) h₂
  obtain ⟨Y, hY, hρY⟩ := compS_reassoc hcb hρF
  -- `free` the slot
  refine wpTS_bind (.appR (.val (.lam _)) .hole) (.app (.val (.prim .free)) (.val (.loc _))) ls _ ρ ?_
  refine wpTS_free ls _ v _ ρ ⟨ρc, Y, hρY, hown, ?_⟩
  simp only [Kont.plug]
  refine wpTS_lolli ls _ v _ Y ?_
  simp [closed_subst ht, closed_subst hg, closed_subst hs, closed_shift ht, closed_shift hg,
    closed_shift hs, subst_shift_succ, closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- the content's traversal, framing `acc ⋆ rest`
  refine wpTS_bind_frame (.appR (.val (.lam _)) .hole) (.app (.app (.val t) (.val s)) (.val v)) ls
    (fun ls' => vP RS ls' δ)
    (fun ls' => vP RA ls' δ acc ⋆ fun ρ' =>
      slots S' ls' δ (ℓ + i.toNat + 1) (N.toNat - (i.toNat + 1)) ρ' ∧ dsize ρ' ≤ n) _
    (fun ls' hls ρ' ⟨x₁, x₂, hx, h₁, h₂, h₃⟩ => ⟨x₁, x₂, hx, vP_same hls h₁, slots_same hls h₂, h₃⟩)
    ?_ Y ⟨ρb, F, hY, hS v ρb ls hv hlt, ρa, ρre, hF, hacc, hrest, hre⟩
  rintro ls' hls r σ ⟨σ₁, σ₂, hcσ, hr, τa, τre, hcτ, hacc', hrest', hre'⟩
  simp only [Kont.plug]
  refine wpTS_lolli ls' _ r _ σ ?_
  simp [closed_subst ht, closed_subst hg, closed_subst hs, closed_shift ht, closed_shift hg,
    closed_shift hs, subst_shift_succ, closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- the algebra at `inj₂ (acc, r)`, framing the rest
  obtain ⟨X, hX, hσX⟩ := compS_reassoc' hcτ hcσ
  refine wpTS_bind_frame (.appR (.val (.lam _)) .hole)
    (.app (.val g) (.val (Val.inj₂ (Val.pair acc r)))) ls'
    (fun ls'' => vP RA ls'' δ)
    (fun ls'' ρ' => slots S' ls'' δ (ℓ + i.toNat + 1) (N.toNat - (i.toNat + 1)) ρ' ∧ dsize ρ' ≤ n) _
    (fun ls'' hls' ρ' ⟨h₂, h₃⟩ => ⟨slots_same hls' h₂, h₃⟩)
    ?_ σ ⟨X, τre, hσX, alg_app hgA (Or.inr ⟨Val.pair acc r, pure_sep_iff.mpr ⟨rfl,
      ⟨acc, r, pure_sep_iff.mpr ⟨rfl, τa, σ₁, ResU.CompS.comm hX, hacc', hr⟩⟩⟩⟩), hrest', hre'⟩
  rintro ls'' hls'' acc' τ ⟨τ₁, τ₂, hcτ', hacc'', hrest'', hre''⟩
  simp only [Kont.plug]
  refine wpTS_lolli ls'' _ acc' _ τ ?_
  simp [closed_subst hs, closed_shift hs, subst_shift_succ, closed_shift (arr_closed ℓ N),
    closed_subst (arr_closed ℓ N)]
  refine wpTS_val ls'' (Val.pair acc' (Val.pair (Val.arr ℓ N) s)) _ τ ?_
  refine ⟨acc', rfl, τ₁, τ₂, hcτ', hacc'', ?_, hre''⟩
  rwa [show ℓ + (i.toNat + 1) = ℓ + i.toNat + 1 by lomega]

/-- **The owned traversal of an array**, given the traversal of a slot's content at every
resource below the bound. -/
theorem arr_spec {t g s : Val} (ht : closedAt 0 t.1 = true) (hg : closedAt 0 g.1 = true)
    (hs : closedAt 0 s.1 = true) {n : Nat}
    (hS : ∀ v ρ ls, vP S' ls δ v ρ → dsize ρ < n →
      wpTS ls (.app (.app (.val t) (.val s)) (.val v)) (fun ls' => vP RS ls' δ) ρ)
    (hgA : ∀ ls, vC true (.bang (.lolli (.sum .unit (.tensor RA RS)) RA)) ls δ g PMap.empty)
    (w : Val) (χ : WRes) (ls : List SRec) (hw : vP (.fam (.ref S')) ls δ w χ) (hn : dsize χ ≤ n) :
    wpTS ls (.app (.app (.val (travOf (arrE g (stepV t g)))) (.val s)) (.val w))
      (fun ls' => vP RA ls' δ) χ := by
  obtain ⟨ℓ, N, rfl, hN, hsl⟩ := vP_fam_iff.mp hw
  have hf := stepV_closed ht hg
  refine travOf_app _ s _ ls _ χ ?_
  simp [arrE, bindE, closed_subst hg, closed_shift hg, closed_subst hs, closed_shift hs,
    closed_subst hf, closed_shift hf]
  refine wpTS_tensor ls (Val.loc ℓ) (Val.i32 N) _ _ χ ?_
  simp [bindE, closed_subst hg, closed_shift hg, closed_subst hs, closed_shift hs,
    closed_subst hf, closed_shift hf, Val.i32]
  -- the seed, framing the slots
  refine wpTS_bind_frame (.appR (.val (.lam _)) .hole) (.app (.val g) (.val (Val.inj₁ Val.unit))) ls
    (fun ls' => vP RA ls' δ)
    (fun ls' ρ' => slots S' ls' δ ℓ N.toNat ρ' ∧ dsize ρ' ≤ n) _
    (fun ls' hls ρ' ⟨h₂, h₃⟩ => ⟨slots_same hls h₂, h₃⟩)
    ?_ χ ⟨PMap.empty, χ, compS_empty_left χ,
      alg_app hgA (Or.inl ⟨Val.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩), hsl, hn⟩
  rintro ls' hls acc₀ σ hσ
  simp only [Kont.plug]
  refine wpTS_lolli ls' _ acc₀ _ σ ?_
  simp [closed_subst hs, closed_shift hs, closed_subst hf, closed_shift hf, subst_shift_succ]
  -- the loop
  refine wpTS_bind (.appR (.val (.lam _)) .hole)
    (.app (.val (.prim .count)) (.val (Val.pair (stepV t g) (Val.pair (Val.i32 N)
      (Val.pair (Val.i32 0) (Val.pair acc₀ (Val.pair (Val.arr ℓ N) s))))))) ls' _ σ ?_
  have hloop := countLoop_inv (stepV t g) N
    (fun k ls st => ArrInv S' RA δ (Val.arr ℓ N) s ℓ N.toNat n k ls st)
    (fun i hi ls st => step_spec ht hg hs hN hS hgA i hi ls st)
    _ 0 ls' (Val.pair acc₀ (Val.pair (Val.arr ℓ N) s)) σ rfl (Nat.zero_le _)
    ⟨acc₀, rfl, hσ⟩
  refine wpTS_mono (fun ls'' st ρ hst => ?_) σ hloop
  rw [arrLen_of_bound hN] at hst
  obtain ⟨acc, rfl, ρ₁, ρ₂, hc, hacc, hsl', -⟩ := hst
  rw [Nat.sub_self] at hsl'
  obtain ⟨rfl, -⟩ := hsl'
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  simp only [Kont.plug]
  refine wpTS_lolli ls'' _ _ _ ρ₁ ?_
  refine wpTS_tensor ls'' acc (Val.pair (Val.arr ℓ N) s) _ _ ρ₁ ?_
  simp only [Expr.subst]
  refine wpTS_val ls'' acc _ ρ₁ ?_
  exact hacc

end

end BoCa.Fig16.LogRel.Core.NestedFold

end
