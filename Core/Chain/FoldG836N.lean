import Core.Chain.Mu836N
import Core.Chain.FamCancel836N
import Core.FoldOwnG

/-!
# The general owned fold at `SemJN₀`  `[spec §6]`

Core's `foldOwnG_compatX` (`Core/FoldOwnG.lean`) at the chain, line by line: Core's term
(`foldOwnGV`, the dispatch `selfG`, the traversal `trav`, the array action `arrE`/`stepV`) and its
reductions, each pure step `erwp_det` at the same index; Core's induction on the position (`P`),
the loop invariant `ArrInv`, and the lexicographic induction on cells, value size and key rank
(`hs_all`). Every run is at one world `Θ` and one view `c`, every call at an index up to `N`;
each split's part is consistent with the view because the whole is valid (`erwp_of_valid`). The
algebras have the empty resource and are read at the run's world (`bang_app₀`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.FoldP
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

-- Every reduction below normalises with one list of substitution facts, as Core's does.
set_option linter.unusedSimpArgs false

/-! ### Reductions -/

section Red
variable {Φ : LocFam} {Q : PostN}

/-- A pure head step in an evaluation context, at the empty table. -/
theorem erwp_headE (hΦ : Φ.Down) (hQ : Q.Down) (K : Kont) {a a' : Expr}
    (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a') (hn : a.allocs = false) {n : Nat} {ls : List SRec}
    {ρ : WRes} (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (K.plug a') ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (K.plug a) ρ :=
  erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ (fun μ => step1Only_plug (hh μ) hn K) h

theorem travOf_appN (hΦ : Φ.Down) (hQ : Q.Down) (e : Expr) (s w : Val) {n : Nat}
    {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls ((e.subst 1 (s.shift 1 0)).subst 0 w) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.app (.val (travOf e)) (.val s)) (.val w))
      ρ := by
  refine erwp_headE hΦ hQ (.appL .hole w) (fun μ => Head.beta μ _ s) rfl ?_
  exact erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ w) rfl hw

/-- At the tag of the `i`-th key, the dispatch runs that key's branch (Core's `dspV_run`). -/
theorem dspV_runN (ks : List Bnd) (hΦ : Φ.Down) (hQ : Q.Down) {sv : Val}
    (hsv : closedAt 0 sv.1 = true) (g w : Val) {n : Nat} {ls : List SRec} :
    ∀ (r : List Bnd) (p i : Nat) (k : Bnd), r[i]? = some k → ∀ ρ,
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls ((branchV ks sv (g.shift 1 0) (p + i) k).subst 0 w)
        ρ →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls ((dspV ks sv (g.shift 1 0) p r).subst 0 (tagV i w))
        ρ
  | [], _, _, _, h => by simp at h
  | c :: r, p, 0, k, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      intro ρ hw
      have e : (dspV ks sv (g.shift 1 0) p (c :: r)).subst 0 (tagV 0 w)
          = .case (.val (.inj₁ w)) (branchV ks sv (g.shift 1 0) p c)
              (dspV ks sv (g.shift 1 0) (p + 1) r) := by
        have hb := branchV_subst ks hsv g ((tagV 0 w).shift 1 0) p 1 le_rfl c
        have hd := dspV_subst ks hsv g r ((tagV 0 w).shift 1 0) (p + 1) 1 le_rfl
        simp only [dspV, Expr.subst, if_pos, Val.shift_shift, tagV] at hb hd ⊢
        rw [hb, hd]
      rw [e]
      exact erwp_headE hΦ hQ .hole (fun μ => Head.case₁ μ w _ _) rfl (by simpa using hw)
  | c :: r, p, i + 1, k, h => by
      simp only [List.getElem?_cons_succ] at h
      intro ρ hw
      have e : (dspV ks sv (g.shift 1 0) p (c :: r)).subst 0 (tagV (i + 1) w)
          = .case (.val (.inj₂ (tagV i w))) (branchV ks sv (g.shift 1 0) p c)
              (dspV ks sv (g.shift 1 0) (p + 1) r) := by
        have hb := branchV_subst ks hsv g ((tagV (i + 1) w).shift 1 0) p 1 le_rfl c
        have hd := dspV_subst ks hsv g r ((tagV (i + 1) w).shift 1 0) (p + 1) 1 le_rfl
        simp only [dspV, Expr.subst, if_pos, Val.shift_shift, tagV] at hb hd ⊢
        rw [hb, hd]
      rw [e]
      refine erwp_headE hΦ hQ .hole (fun μ => Head.case₂ μ (tagV i w) _ _) rfl ?_
      exact dspV_runN ks hΦ hQ hsv g w r (p + 1) i k h ρ
        (by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hw)

/-- **The dispatch** (Core's `selfG_run`). -/
theorem selfG_runN (ks : List Bnd) (hΦ : Φ.Down) (hQ : Q.Down) (gs w : Val) (i : Nat) (k : Bnd)
    (hk : ks[i]? = some k) {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      ((branchV ks (selfG ks) (gs.shift 1 0) i k).subst 0 w) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (selfG ks)) (.val gs)) (.val (tagV i w))) ρ := by
  have hT := opTableN_down OpTabN.empty_down
  refine erwp_pureSteps hΦ hT hQ (selfV_steps_in (fBG_closed ks) (.appL .hole (tagV i w)) gs) ?_
  rw [fixV_eq (fBG_closed ks)]
  refine erwp_headE hΦ hQ (.appL .hole (tagV i w)) (fun μ => Head.beta μ _ gs) rfl ?_
  have e : ((fBG ks).subst 1 (selfG ks)).subst 0 gs
      = .val (.lam (dspV ks (selfG ks) (gs.shift 1 0) 0 ks)) := by
    have h := dsp_subst ks (selfG_closed ks) gs ks 0 0
    have hc : (selfG ks).shift 1 0 = selfG ks := val_shift_closed (selfG_closed ks) 1 0
    show (Expr.subst 0 gs (Expr.subst 1 (selfG ks) (Expr.lam (dsp ks 0 0 ks))))
      = Expr.lam (dspV ks (selfG ks) (gs.shift 1 0) 0 ks)
    simp only [Expr.subst, hc]
    simpa using h
  change erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
    ((Kont.appL .hole (tagV i w)).plug (((fBG ks).subst 1 (selfG ks)).subst 0 gs)) ρ
  rw [e]
  simp only [Kont.plug]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ (tagV i w)) rfl ?_
  exact dspV_runN ks hΦ hQ (selfG_closed ks) gs w ks 0 i k hk ρ (by simpa using hw)

/-- The handle applied is the fixed point at the algebras (Core's `hG_app`). -/
theorem hG_appN (ks : List Bnd) (hΦ : Φ.Down) (hQ : Q.Down) (gs x : Val) {n : Nat}
    {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (selfG ks)) (.val gs)) (.val x)) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val (hG ks gs)) (.val x)) ρ := by
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ x) rfl ?_
  simpa [closed_subst (selfG_closed ks), subst_shift_succ] using hw

/-- The `p`-th component of a tuple, by pure steps, in an evaluation context (Core's
`proj_red`). -/
theorem proj_redN (hΦ : Φ.Down) (hQ : Q.Down) {n : Nat} :
    ∀ (vs : List Val) (p : Nat) (a : Val), vs[p]? = some a → ∀ (K : Kont) (ls : List SRec)
      (ρ : WRes), erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (K.plug (.val a)) ρ →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (K.plug (projE vs.length p (.val (tupV vs)))) ρ
  | [], _, _, h, _, _, _ => by simp at h
  | [b], p, a, h, K, ls, ρ => by
      intro hw
      have hp : p = 0 := by
        cases p with
        | zero => rfl
        | succ p => simp at h
      subst hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact hw
  | b :: c :: rest, 0, a, h, K, ls, ρ => by
      intro hw
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.length_cons, projE, tupV]
      refine erwp_headE hΦ hQ K (fun μ => Head.letpair μ b (tupV (c :: rest)) _) rfl ?_
      simpa using hw
  | b :: c :: rest, p + 1, a, h, K, ls, ρ => by
      intro hw
      simp only [List.getElem?_cons_succ] at h
      have ih := proj_redN hΦ hQ (c :: rest) p a h K ls ρ hw
      simp only [List.length_cons, projE, tupV]
      refine erwp_headE hΦ hQ K (fun μ => Head.letpair μ b (tupV (c :: rest)) _) rfl ?_
      rw [projE_subst, projE_subst_gen]
      simpa [subst_shift_succ] using ih

/-- **The `p`-th algebra of the tuple**, applied (Core's `proj_run`). -/
theorem proj_runN (hΦ : Φ.Down) (hQ : Q.Down) (vs : List Val) (p : Nat) (a : Val)
    (h : vs[p]? = some a) (r : Val) {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val a) (.val r)) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (projV vs.length p)) (.val (tupV vs))) (.val r)) ρ := by
  refine erwp_headE hΦ hQ (.appL .hole r) (fun μ => Head.beta μ _ (tupV vs)) rfl ?_
  rw [projE_subst]
  exact proj_redN hΦ hQ vs p a h (.appL .hole r) ls ρ hw

end Red

/-! ### The counted loop with an invariant (Core's `countLoop_inv`) -/

theorem countLoop_invN {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {Nb : Nat} (f : Val)
    (n : UInt32) (I : Nat → PostN) (hId : ∀ j, (I j).Down)
    (hstep : ∀ i : UInt32, i < arrLen n → ∀ k ls st ρ, k ≤ Nb → I i.toNat k ls st ρ →
      ConsistentX c ρ → erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (I (i.toNat + 1)) k ls
        (.app (.val f) (.val (Val.pair (Val.i32 i) st))) ρ) :
    ∀ (d : Nat) (i : UInt32) (k : Nat) (ls : List SRec) (st : Val) (ρ : WRes), k ≤ Nb →
      (arrLen n).toNat - i.toNat = d → i.toNat ≤ (arrLen n).toNat → I i.toNat k ls st ρ →
      ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (I (arrLen n).toNat) k ls
        (.app (.val (.prim .count)) (.val (Val.pair f (Val.pair (Val.i32 n)
          (Val.pair (Val.i32 i) st))))) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  intro d
  induction d with
  | zero =>
      intro i k ls st ρ _ hd hle hs _
      refine erwp_headE hΦ (hId _) .hole (fun μ => Head.count μ f n i st) rfl ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      simp only [Kont.plug]
      unfold countNext
      rw [if_neg hi]
      have e : i.toNat = (arrLen n).toNat := by omega
      rw [← e]
      exact erwp_val hs
  | succ d ih =>
      intro i k ls st ρ hk hd hle hs hc
      refine erwp_headE hΦ (hId _) .hole (fun μ => Head.count μ f n i st) rfl ?_
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
        (fun σ => σ = PMap.empty) (ResU.comp_empty_right ρ) hc (hstep i hi k ls st ρ hk hs hc) rfl ?_
      rintro k' hk' ls' v σ₁ σ₂ σ hcσ hv rfl hcσ' -
      rw [ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)] at hcσ' ⊢
      have hv' : I (i + 1).toNat k' ls' v σ₁ := by rw [hi1]; exact hv
      exact ih (i + 1) k' ls' v σ₁ (hk'.trans hk) (by omega) (by omega) hv' hcσ'

/-! ### The owned traversal of an array -/

section Arr
variable {S' RS RA : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {Nb : Nat}

end Arr

section Arr2
variable {S' RS RA : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {Nb : Nat}

end Arr2

/-! ### The traversal's spec, by induction on `P` (Core's `trav_spec`) -/

section Trav
variable (ks : List Bnd) (G : Algs) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (Nb : Nat)

end Trav

/-! ### The rule -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
