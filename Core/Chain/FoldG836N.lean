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

/-- The slots `ℓ, …, ℓ + m − 1` of an array of `Ref S'` at the index `j` (Core's `slots`). -/
abbrev slotsN₀ (S' : VTy) (δ : LSub) (Θ : LocTy) (j : Nat) (ℓ : Loc) (m : Nat) : WProp :=
  sepRange (fun x => vN₀ (ℍ := ℍ) (.ref S') δ Θ j (Val.loc x)) ℓ m

theorem slotsN_le₀ {S' : VTy} {δ : LSub} {Θ : LocTy} {j j' : Nat} (h : j' ≤ j) {ℓ : Loc} {m : Nat}
    {ρ : WRes} (hs : slotsN₀ (ℍ := ℍ) S' δ Θ j ℓ m ρ) : slotsN₀ (ℍ := ℍ) S' δ Θ j' ℓ m ρ :=
  sepRange_mono' (fun _ _ hm => vN_le₀ h hm) hs

/-- **The loop's invariant** before the `i`-th step, at the index (Core's `ArrInv`). -/
def ArrInvN₀ (S' RA : VTy) (δ : LSub) (Θ : LocTy) (w s : Val) (ℓ : Loc) (N n : Nat) (i : Nat) :
    PostN := fun j _ st ρ =>
  ∃ acc, st = Val.pair acc (Val.pair w s) ∧
    (vN₀ (ℍ := ℍ) RA δ Θ j acc ⋆ (sepRange todoP ℓ i ⋆
      fun ρ' => slotsN₀ (ℍ := ℍ) S' δ Θ j (ℓ + i) (N - i) ρ' ∧ dsize ρ' ≤ n)) ρ

theorem arrInvN_down₀ (S' RA : VTy) (δ : LSub) (Θ : LocTy) (w s : Val) (ℓ : Loc) (N n i : Nat) :
    (ArrInvN₀ (ℍ := ℍ) S' RA δ Θ w s ℓ N n i).Down := by
  rintro j ls st ρ ⟨acc, rfl, ρa, ρr, hc, hacc, ρd, ρs, hcr, htodo, hsl, hdr⟩
  exact ⟨acc, rfl, ρa, ρr, hc, vN_le₀ (Nat.le_succ j) hacc, ρd, ρs, hcr, htodo,
    slotsN_le₀ (Nat.le_succ j) hsl, hdr⟩

/-- **One step of the loop** (Core's `step_spec`). -/
theorem step_specN₀ (hΘ : Θ.OK) (k : Nat) {t s : Val} (ht : closedAt 0 t.1 = true) {n : Nat}
    {ℓ : Loc} {N : UInt32} (hN : N.toNat < 2 ^ 31)
    (hS : ∀ v ρ j ls, j ≤ Nb → vN₀ (ℍ := ℍ) S' δ Θ j v ρ → dsize ρ < n → ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ RS δ Θ) j ls
        (.app (.app (.val t) (.val s)) (.val v)) ρ)
    (hgA : ∀ j ls x ρ, j ≤ Nb → vN₀ (ℍ := ℍ) (.sum .unit (.tensor RA RS)) δ Θ j x ρ →
      ConsistentX c ρ → erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ RA δ Θ) j ls
        (.app (.val s) (.val (tagV k x))) ρ)
    (i : UInt32) (hi : i < arrLen N) :
    ∀ j ls st ρ, j ≤ Nb → ArrInvN₀ (ℍ := ℍ) S' RA δ Θ (Val.arr ℓ N) s ℓ N.toNat n i.toNat j ls st ρ →
      ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
        (ArrInvN₀ (ℍ := ℍ) S' RA δ Θ (Val.arr ℓ N) s ℓ N.toNat n (i.toNat + 1)) j ls
        (.app (.val (FoldP.stepV k t)) (.val (Val.pair (Val.i32 i) st))) ρ := by
  rintro j ls st ρ hj ⟨acc, rfl, ρa, ρr, hc, hacc, ρd, ρs, hcr, htodo, hsl, hdr⟩ hcρ
  have hΦ := LocTy.view_down hΘ.1 c
  have hQ := arrInvN_down₀ (ℍ := ℍ) S' RA δ Θ (Val.arr ℓ N) s ℓ N.toNat n (i.toNat + 1)
  rw [arrLen_of_bound hN] at hi
  have hiN : i.toNat < N.toNat := UInt32.lt_iff_toNat_lt.mp hi
  have esub : N.toNat - i.toNat = (N.toNat - (i.toNat + 1)) + 1 := by omega
  rw [esub] at hsl
  unfold slotsN₀ at hsl
  rw [sepRange_succ] at hsl
  obtain ⟨ρsl, ρre, hcs, hslot, hrest⟩ := hsl
  obtain ⟨l', v, ρb, el, hcb, hv⟩ := hslot
  have hl' : l' = ℓ + i.toNat := (loc_inj el).symm
  subst hl'
  have hlt : dsize ρb < n := by
    have h₁ : dsize ρb < dsize ρsl := dsize_tail_lt hcb ⟨PMap.empty, ResU.comp_empty_right _⟩
    have h₂ := dsize_le_left hcs
    omega
  have hre : dsize ρre ≤ n := le_trans (dsize_le_right hcs) hdr
  -- the pure steps to the `idx`
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ _) rfl ?_
  simp only [FoldP.stepE, Kont.plug]
  refine erwp_headE hΦ hQ .hole
    (fun μ => Head.letpair μ (Val.i32 i) (Val.pair acc (Val.pair (Val.arr ℓ N) s)) _) rfl ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.letpair μ acc (Val.pair (Val.arr ℓ N) s) _) rfl ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.letpair μ (Val.arr ℓ N) s _) rfl ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- `idx`, then the `inj₁` branch
  refine erwp_headE hΦ hQ (.case .hole _ _) (fun μ => Head.idx μ ℓ N i) rfl ?_
  simp only [Kont.plug]
  rw [idxAns_lt ℓ hi]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.case₁ μ (Val.loc (ℓ + i.toNat)) _ _) rfl ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- the resource: `ρ = cell ● (ρa ● (ρd ● (ρb ● ρre)))`
  obtain ⟨bre, hbre, hcbre⟩ := compS_reassoc hcb hcs
  obtain ⟨X, hX, hcX⟩ := compS_lcomm hcbre hcr
  obtain ⟨Y, hY, hcY⟩ := compS_lcomm hcX hc
  -- take the slot's value out
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole)
    (e := .app (.app swap (.val (.loc (ℓ + i.toNat)))) (.val .unit))
    (P := fun _ _ q σ => q = Val.pair (.loc (ℓ + i.toNat)) v ∧
      σ = ResU.single (ℓ + i.toNat) (CellU.ownOf .unit))
    (fun Y' => Y' = Y) hcY hcρ
    (erwp_swapN hΦ (fun _ _ _ _ h => h) (ℓ + i.toNat) v .unit
      ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, fun σa σ hσa hcσ => ⟨rfl, by
        rw [ResU.CompS.functional hcσ (compS_empty_left σa)]; exact hσa⟩⟩) rfl ?_
  rintro k₁ hk₁ ls₁ q σa Y' σ hcσ ⟨rfl, rfl⟩ rfl hcσ' hvσ
  simp only [Kont.plug]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ _) rfl ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.letpair μ (.loc (ℓ + i.toNat)) v _) rfl ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- `σ = ρb ● (ρa ● ((ρd ● σa) ● ρre))`
  obtain ⟨Xσ, hXσ, hcXσ⟩ := compS_reassoc hY (ResU.CompS.comm hcσ)
  obtain ⟨dσ, hdσ, hcdσ⟩ := compS_exch hX hXσ
  obtain ⟨dre, hdre, hcdre⟩ := compS_lcomm hbre hcdσ
  obtain ⟨F, hF, hcF⟩ := compS_lcomm hcdre hcXσ
  have htodo' : sepRange todoP ℓ (i.toNat + 1) dσ :=
    sepRange_append hdσ htodo ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ⟨rfl, trivial⟩⟩
  -- the value's traversal, framing `acc ⋆ (emptied ⋆ rest)`
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole)
    (e := .app (.app (.val t) (.val s)) (.val v)) (fun F' => F' = F) hcF hcσ'
    (hS v ρb k₁ ls₁ (hk₁.trans hj) (vN_le₀ hk₁ hv) hlt (consistentX_left hcF hcσ' hvσ)) rfl ?_
  rintro k₂ hk₂ ls₂ r σ₁ F' σ' hc₂ hr rfl hcσ₂ hvσ₂
  simp only [Kont.plug]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ r) rfl ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  rw [tagE_inj₂_pair]
  -- the algebra at `inj₂ (acc, r)`, framing the emptied slots and the rest
  obtain ⟨Z, hZ, hσZ⟩ := compS_reassoc' hF hc₂
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole)
    (e := .app (.val s) (.val (tagV k (Val.inj₂ (Val.pair acc r))))) (fun D => D = dre)
    hσZ hcσ₂
    (hgA k₂ ls₂ _ Z (hk₂.trans (hk₁.trans hj))
      (.inr ⟨Val.pair acc r, rfl, ⟨acc, r, ρa, σ₁, rfl, ResU.CompS.comm hZ,
        vN_le₀ (hk₂.trans hk₁) hacc, hr⟩⟩)
      (consistentX_left hσZ hcσ₂ hvσ₂)) rfl ?_
  rintro k₃ hk₃ ls₃ acc' τ₁ D τ hcτ hacc' rfl _ _
  simp only [Kont.plug]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ acc') rfl ?_
  simp [subst_shift_succ, closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  refine erwp_val (v := Val.pair acc' (Val.pair (Val.arr ℓ N) s)) ?_
  refine ⟨acc', rfl, τ₁, _, hcτ, hacc', dσ, ρre, hdre, htodo', ?_, hre⟩
  have hle : k₃ ≤ j := hk₃.trans (hk₂.trans hk₁)
  rw [show ℓ + (i.toNat + 1) = ℓ + i.toNat + 1 by lomega]
  exact slotsN_le₀ hle hrest

end Arr

section Arr2
variable {S' RS RA : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {Nb : Nat}

/-- An emptied slot is a leaf of `Array 1` (Core's `todo_done`). -/
theorem todo_doneN₀ {ℓ : Loc} {m j : Nat} {ρ : WRes} (h : sepRange todoP ℓ m ρ) :
    sepRange (fun x => vN₀ (ℍ := ℍ) (.ref .unit) δ Θ j (Val.loc x)) ℓ m ρ :=
  sepRange_mono' (fun x ρ' hm => ⟨x, .unit, PMap.empty, rfl, by rw [hm]; exact ResU.comp_empty_right _,
    rfl, rfl⟩) h

/-- **The owned traversal of an array** (Core's `arr_spec`): the seed, the loop, and the emptied
array freed by `prim .drop`. -/
theorem arr_specN₀ (hΘ : Θ.OK) (k : Nat) {t s : Val} (ht : closedAt 0 t.1 = true) {n : Nat}
    (hS : ∀ v ρ j ls, j ≤ Nb → vN₀ (ℍ := ℍ) S' δ Θ j v ρ → dsize ρ < n → ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ RS δ Θ) j ls
        (.app (.app (.val t) (.val s)) (.val v)) ρ)
    (hgA : ∀ j ls x ρ, j ≤ Nb → vN₀ (ℍ := ℍ) (.sum .unit (.tensor RA RS)) δ Θ j x ρ →
      ConsistentX c ρ → erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ RA δ Θ) j ls
        (.app (.val s) (.val (tagV k x))) ρ)
    (w : Val) (χ : WRes) (j : Nat) (ls : List SRec) (hj : j ≤ Nb)
    (hw : vN₀ (ℍ := ℍ) (.fam (.ref S')) δ Θ j w χ) (hn : dsize χ ≤ n) (hc : ConsistentX c χ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ RA δ Θ) j ls
      (.app (.app (.val (travOf (arrE k (FoldP.stepV k t)))) (.val s)) (.val w)) χ := by
  have hΦ := LocTy.view_down hΘ.1 c
  have hQ := vPostN_down₀ (ℍ := ℍ) RA δ Θ
  obtain ⟨ℓ, N, rfl, hN, hsl⟩ := vN_fam_iff₀.mp hw
  have hf := FoldP.stepV_closed k ht
  refine travOf_appN hΦ hQ _ s _ ?_
  simp [arrE, bindE, tagE_subst, subst_shift_succ, closed_subst hf, closed_shift hf,
    closed_subst unitF_closed, closed_shift unitF_closed]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.letpair μ (Val.loc ℓ) (Val.i32 N) _) rfl ?_
  simp [bindE, tagE_subst, subst_shift_succ, closed_subst hf, closed_shift hf,
    closed_subst unitF_closed, closed_shift unitF_closed, Val.i32]
  rw [tagE_inj₁_unit]
  -- the seed, framing the slots
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole)
    (e := .app (.val s) (.val (tagV k (.inj₁ .unit)))) (fun X => X = χ) (compS_empty_left χ) hc
    (hgA j ls _ _ hj (.inl ⟨Val.unit, rfl, rfl, rfl⟩) (consistentX_empty c)) rfl ?_
  rintro k₁ hk₁ ls₁ acc₀ σ₁ X σ hcσ hacc₀ rfl hcσ' -
  simp only [Kont.plug]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ acc₀) rfl ?_
  simp [subst_shift_succ, closed_subst hf, closed_shift hf, closed_subst unitF_closed,
    closed_shift unitF_closed]
  -- the loop
  have hloop := countLoop_invN hΘ (c := c) (Nb := Nb) (FoldP.stepV k t) N
    (fun i => ArrInvN₀ (ℍ := ℍ) S' RA δ Θ (Val.arr ℓ N) s ℓ N.toNat n i)
    (fun i => arrInvN_down₀ S' RA δ Θ (Val.arr ℓ N) s ℓ N.toNat n i)
    (fun i hi j' ls' st ρ' hj' h' hc' => step_specN₀ hΘ k ht hN hS hgA i hi j' ls' st ρ' hj' h' hc')
    _ 0 k₁ ls₁ (Val.pair acc₀ (Val.pair (Val.arr ℓ N) s)) σ (hk₁.trans hj) rfl (Nat.zero_le _)
    ⟨acc₀, rfl, σ₁, X, hcσ, hacc₀, PMap.empty, X, compS_empty_left X, ⟨rfl, trivial⟩,
      by simpa using slotsN_le₀ hk₁ hsl, hn⟩ hcσ'
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole) (fun E => E = PMap.empty)
    (ResU.comp_empty_right σ) hcσ' hloop rfl ?_
  rintro k₂ hk₂ ls₂ st ρ' E σ'' hcρ hst rfl hc₂ hv₂
  obtain rfl := ResU.CompS.functional hcρ (ResU.comp_empty_right ρ')
  rw [arrLen_of_bound hN] at hst
  obtain ⟨acc, rfl, ρ₁, ρ₂, hc', hacc, ρd, ρs, hcr, htodo, hsl', -⟩ := hst
  rw [Nat.sub_self] at hsl'
  obtain ⟨rfl, -⟩ := hsl'
  rw [ResU.CompS.functional hcr (ResU.comp_empty_right ρd)] at hc'
  simp only [Kont.plug]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ _) rfl ?_
  refine erwp_headE hΦ hQ .hole (fun μ => Head.letpair μ acc (Val.pair (Val.arr ℓ N) s) _) rfl ?_
  simp [subst_shift_succ, closed_subst unitF_closed, closed_shift unitF_closed]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.letpair μ (Val.arr ℓ N) s _) rfl ?_
  simp [subst_shift_succ, closed_subst unitF_closed, closed_shift unitF_closed,
    closed_subst (arr_closed ℓ N), closed_shift (arr_closed ℓ N)]
  -- `drop` the emptied array, framing the accumulator
  have hcd : ConsistentX c ρd := consistentX_right hc' hc₂ hv₂
  refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole)
    (e := .app (.val (.prim .drop)) (.val (Val.pair unitF (Val.arr ℓ N))))
    (P := vPostN₀ (ℍ := ℍ) .unit δ Θ) (fun A => A = ρ₁)
    (ResU.CompS.comm hc') hc₂ ?_ rfl ?_
  · refine erwp_headE hΦ (vPostN_down₀ (ℍ := ℍ) .unit δ Θ) .hole
      (fun μ => Head.drop μ unitF ℓ N) rfl ?_
    exact dropFill_wpN₀ hΘ unitF ℓ (dropU_sem₀ δ Θ k₂) N.toNat 0 k₂ ls₂ ρd c le_rfl hcd
      (by simpa using todo_doneN₀ (ℍ := ℍ) (δ := δ) (Θ := Θ) (j := k₂) htodo)
  rintro k₃ hk₃ ls₃ u τ₁ A τ hcτ ⟨rfl, rfl⟩ rfl _ _
  simp only [Kont.plug]
  refine erwp_headE hΦ hQ .hole (fun μ => Head.beta μ _ Val.unit) rfl ?_
  simp [subst_shift_succ]
  rw [eq_of_compS_empty_left hcτ]
  exact erwp_val (vN_le₀ hk₃ hacc)

end Arr2

/-! ### The traversal's spec, by induction on `P` (Core's `trav_spec`) -/

section Trav
variable (ks : List Bnd) (G : Algs) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (Nb : Nat)

/-- **The call of the `μ` key `B :: Bs`** (Core's `HS`). -/
def HSN₀ (s : Val) (B : VTy) (Bs : Stack) (n K : Nat) : Prop :=
  ∀ w χ j ls, j ≤ Nb → sizeOf w.1 ≤ K → vN₀ (ℍ := ℍ) (closedOf B Bs) δ Θ j w χ → dsize χ ≤ n →
    ConsistentX c χ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ (G.Res (B :: Bs)) δ Θ) j ls
      (.app (.val s) (.val (tagV (ks.idxOf (.mu (B :: Bs))) w))) χ

/-- **The environment of handles** (Core's `IHL`). -/
def IHLN₀ (s : Val) (n K r : Nat) : Prop :=
  ∀ B Bs, .mu (B :: Bs) ∈ ks → Anc ks (B :: Bs) → ∀ n' K', Lt3 n' K' (sizeOf B) n K r →
    HSN₀ (ℍ := ℍ) ks G δ Θ c Nb s B Bs n' K'

/-- The array keys' algebras through the handle (Core's `AH`). -/
def AHN₀ (s : Val) : Prop :=
  ∀ Bs S, .arr Bs S ∈ ks → ∀ j ls x ρ, j ≤ Nb →
    vN₀ (ℍ := ℍ) (.sum .unit (.tensor (G.ResA Bs S) (resO G Bs S))) δ Θ j x ρ → ConsistentX c ρ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ (G.ResA Bs S) δ Θ) j ls
      (.app (.val s) (.val (tagV (ks.idxOf (.arr Bs S)) x))) ρ

theorem IHLN₀.down {s : Val} {n K r n' : Nat} (h : IHLN₀ (ℍ := ℍ) ks G δ Θ c Nb s n K r)
    (hn : n' < n) (K' r' : Nat) : IHLN₀ (ℍ := ℍ) ks G δ Θ c Nb s n' K' r' :=
  fun B Bs hm ha n'' K'' hlt =>
    h B Bs hm ha n'' K'' (Or.inl (by rcases hlt with h | ⟨rfl, -⟩ <;> omega))

/-- A closed position: the value itself (Core's `leaf_spec`). -/
theorem leaf_specN₀ (hΘ : Θ.OK) (s : Val) (Bs : Stack) {A : VTy} (hA : FoldP.clB 0 A = true) (w : Val)
    (χ : WRes) (j : Nat) (ls : List SRec) (hv : vN₀ (ℍ := ℍ) (A.subst (env Bs)) δ Θ j w χ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ (resO G Bs A) δ Θ) j ls
      (.app (.app (.val (trav ks Bs A)) (.val s)) (.val w)) χ := by
  refine travOf_appN (LocTy.view_down hΘ.1 c) (vPostN_down₀ _ δ Θ) _ s w ?_
  rw [tE_leaf ks Bs hA]
  have e : ((Expr.var 0).subst 1 (s.shift 1 0)).subst 0 w = .val w := by simp [Expr.subst]
  rw [e, resO_leaf G Bs hA]
  rw [VTy.subst_closed0 ((clB_iff 0 A).mp hA)] at hv
  exact erwp_val hv

/-- **The generic owned traversal**, by induction on the position `A ∈ P` (Core's `trav_spec`). -/
theorem trav_specN₀ (hΘ : Θ.OK) (s : Val) (hAH : AHN₀ (ℍ := ℍ) ks G δ Θ c Nb s) :
    ∀ (A : VTy) (Bs : Stack) (n K r : Nat), IHLN₀ (ℍ := ℍ) ks G δ Θ c Nb s n K r →
      P Bs.length A → sizeOf A ≤ r → Anc ks Bs → (∀ b ∈ keysIn Bs A, b ∈ ks) →
      ∀ w χ j ls, j ≤ Nb → sizeOf w.1 ≤ K → (Hd A ∨ sizeOf w.1 < K) →
        vN₀ (ℍ := ℍ) (A.subst (env Bs)) δ Θ j w χ → dsize χ ≤ n → ConsistentX c χ →
        erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ (resO G Bs A) δ Θ) j ls
          (.app (.app (.val (trav ks Bs A)) (.val s)) (.val w)) χ
  | .tvar i, Bs, n, K, r, hI, hP, _, hA, _, w, χ, j, ls, hj, _, hhd, hv, hn, hc => by
      have hi : i < Bs.length := hP
      have hlt : sizeOf w.1 < K := by
        rcases hhd with h | h
        · rcases h with h | h
          · exact absurd h (Nat.not_lt_zero _)
          · exact h.elim
        · exact h
      have e := List.drop_eq_getElem_cons hi
      set B' := Bs[i]
      set Bs' := Bs.drop (i + 1)
      have hm : Bnd.mu (B' :: Bs') ∈ ks := e ▸ hA i hi
      have ha : Anc ks (B' :: Bs') := e ▸ anc_drop hA i
      have hH := hI B' Bs' hm ha n (sizeOf w.1) (Or.inr ⟨rfl, Or.inl hlt⟩)
      refine travOf_appN (LocTy.view_down hΘ.1 c) (vPostN_down₀ _ δ Θ) _ s w ?_
      simp only [tE]
      rw [callE_subst ks _ s w, e]
      have hv' : vN₀ (ℍ := ℍ) (closedOf B' Bs') δ Θ j w χ := by
        rw [← env_drop Bs i B' Bs' e]; exact hv
      simp only [resO, e]
      exact hH w χ j ls hj le_rfl hv' hn hc
  | .tensor A₁ A₂, Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, j, ls, hj, hK, _, hv, hn, hc => by
      by_cases hcl : FoldP.clB 0 (.tensor A₁ A₂) = true
      · exact leaf_specN₀ ks G δ Θ c hΘ s Bs hcl w χ j ls hv
      have hΦ := LocTy.view_down hΘ.1 c
      obtain ⟨v₁, v₂, χ₁, χ₂, rfl, hcχ, h₁, h₂⟩ := hv
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      have hr₁ : sizeOf A₁ ≤ r := by simp at hr; omega
      have hr₂ : sizeOf A₂ ≤ r := by simp at hr; omega
      have hk₁ : ∀ b ∈ keysIn Bs A₁, b ∈ ks := fun b h => hk b (by simp [keysIn, h])
      have hk₂ : ∀ b ∈ keysIn Bs A₂, b ∈ ks := fun b h => hk b (by simp [keysIn, h])
      have ht₁ := trav_closed ks Bs A₁
      have ht₂ := trav_closed ks Bs A₂
      refine travOf_appN hΦ (vPostN_down₀ _ δ Θ) _ s _ ?_
      simp only [tE, if_neg hcl]
      rw [FoldP.tensor_subst _ _ s v₁ v₂ ht₁ ht₂]
      refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.letpair μ v₁ v₂ _) rfl ?_
      simp only [Kont.plug]
      rw [FoldP.tensor_body _ _ s v₁ v₂ ht₁ ht₂]
      simp only [resO, if_neg hcl]
      refine erwp_of_valid fun hvχ => ?_
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (bindE (.app (.app (.val (trav ks Bs A₂)) (.val (s.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole)
        (fun X => X = χ₂) hcχ hc
        (trav_specN₀ hΘ s hAH A₁ Bs n K r hI hP.1 hr₁ hA hk₁ v₁ χ₁ j ls hj (le_of_lt hs₁)
          (Or.inr hs₁) h₁ (le_trans (dsize_le_left hcχ) hn) (consistentX_left hcχ hc hvχ)) rfl ?_
      rintro k₁ hk₁ ls₁ r₁ σ₁ X σ hcσ hr₁' rfl hcσ' hvσ
      simp only [Kont.plug]
      refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.beta μ _ r₁) rfl ?_
      rw [FoldP.tensor_body₂ _ s v₂ r₁ ht₂]
      refine erwp_bind_frame hΦ (opTableN_local _)
        (.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole)
        (fun Y => Y = σ₁) (ResU.CompS.comm hcσ) hcσ'
        (trav_specN₀ hΘ s hAH A₂ Bs n K r hI hP.2 hr₂ hA hk₂ v₂ X k₁ ls₁ (hk₁.trans hj)
          (le_of_lt hs₂) (Or.inr hs₂) (vN_le₀ hk₁ h₂) (le_trans (dsize_le_right hcχ) hn)
          (consistentX_right hcσ hcσ' hvσ)) rfl ?_
      rintro k₂ hk₂ ls₂ r₂ τ₁ Y τ hcτ hr₂' rfl _ _
      simp only [Kont.plug]
      refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.beta μ _ r₂) rfl ?_
      rw [tensor_body₃]
      exact erwp_val ⟨r₁, r₂, Y, τ₁, rfl, ResU.CompS.comm hcτ, vN_le₀ hk₂ hr₁', hr₂'⟩
  | .sum A₁ A₂, Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, j, ls, hj, hK, _, hv, hn, hc => by
      by_cases hcl : FoldP.clB 0 (.sum A₁ A₂) = true
      · exact leaf_specN₀ ks G δ Θ c hΘ s Bs hcl w χ j ls hv
      have hΦ := LocTy.view_down hΘ.1 c
      have hr₁ : sizeOf A₁ ≤ r := by simp at hr; omega
      have hr₂ : sizeOf A₂ ≤ r := by simp at hr; omega
      have hk₁ : ∀ b ∈ keysIn Bs A₁, b ∈ ks := fun b h => hk b (by simp [keysIn, h])
      have hk₂ : ∀ b ∈ keysIn Bs A₂, b ∈ ks := fun b h => hk b (by simp [keysIn, h])
      have ht₁ := trav_closed ks Bs A₁
      have ht₂ := trav_closed ks Bs A₂
      refine travOf_appN hΦ (vPostN_down₀ _ δ Θ) _ s _ ?_
      simp only [tE, if_neg hcl]
      rw [FoldP.sum_subst _ _ s w ht₁ ht₂]
      simp only [resO, if_neg hcl]
      rcases hv with ⟨v, rfl, hv⟩ | ⟨v, rfl, hv⟩
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.case₁ μ v _ _) rfl ?_
        simp only [Kont.plug]
        rw [FoldP.sum_branch _ s v ht₁ Expr.inj₁ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₁ (.var 0)))) .hole)
          (fun E => E = PMap.empty) (ResU.comp_empty_right χ) hc
          (trav_specN₀ hΘ s hAH A₁ Bs n K r hI hP.1 hr₁ hA hk₁ v χ j ls hj (le_of_lt hsz)
            (Or.inr hsz) hv hn hc) rfl ?_
        rintro k' _ ls' r' σ₁ E σ hcσ hr' rfl _ _
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.beta μ _ r') rfl ?_
        exact erwp_val (v := Val.inj₁ r') (.inl ⟨r', rfl, hr'⟩)
      · have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.case₂ μ v _ _) rfl ?_
        simp only [Kont.plug]
        rw [FoldP.sum_branch _ s v ht₂ Expr.inj₂ (fun _ _ _ => rfl)]
        refine erwp_bind_frame hΦ (opTableN_local _) (.appR (.val (.lam (Expr.inj₂ (.var 0)))) .hole)
          (fun E => E = PMap.empty) (ResU.comp_empty_right χ) hc
          (trav_specN₀ hΘ s hAH A₂ Bs n K r hI hP.2 hr₂ hA hk₂ v χ j ls hj (le_of_lt hsz)
            (Or.inr hsz) hv hn hc) rfl ?_
        rintro k' _ ls' r' σ₁ E σ hcσ hr' rfl _ _
        obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
        simp only [Kont.plug]
        refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.beta μ _ r') rfl ?_
        exact erwp_val (v := Val.inj₂ r') (.inr ⟨r', rfl, hr'⟩)
  | .ref S, Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, j, ls, hj, _, _, hv, hn, hc => by
      by_cases hcl : FoldP.clB 0 (.ref S) = true
      · exact leaf_specN₀ ks G δ Θ c hΘ s Bs hcl w χ j ls hv
      have hcl' : ¬ FoldP.clB 0 S = true := hcl
      have hΦ := LocTy.view_down hΘ.1 c
      have hrS : sizeOf S ≤ r := by simp at hr; omega
      have htS := trav_closed ks Bs S
      obtain ⟨ℓ, v', ρb, rfl, hc', hM⟩ := hv
      have hlt : dsize ρb < n :=
        lt_of_lt_of_le (dsize_tail_lt hc' ⟨PMap.empty, ResU.comp_empty_right _⟩) hn
      refine travOf_appN hΦ (vPostN_down₀ _ δ Θ) _ s _ ?_
      simp only [tE, if_neg hcl']
      rw [FoldP.ref_subst _ s _ htS]
      refine erwp_of_valid fun hvχ => ?_
      refine erwp_free hΦ (opTableN_local _) _ ℓ v' ⟨_, ρb, hc', rfl, ?_⟩
      simp only [Kont.plug]
      refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.beta μ _ v') rfl ?_
      rw [FoldP.ref_body _ s v' htS]
      simp only [resO, if_neg hcl']
      exact trav_specN₀ hΘ s hAH S Bs (dsize ρb) (sizeOf v'.1 + 1) r
        (IHLN₀.down ks G δ Θ c Nb hI hlt _ _) hP hrS hA hk v' ρb (j - 1) ls
        (le_trans (Nat.sub_le j 1) hj) (Nat.le_succ _) (Or.inr (Nat.lt_succ_self _))
        (vN_le₀ (Nat.sub_le j 1) hM) le_rfl (consistentX_right hc' hc hvχ)
  | .fam (.ref S), Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, j, ls, hj, _, _, hv, hn, hc => by
      by_cases hcl : FoldP.clB 0 S = true
      · exact leaf_specN₀ ks G δ Θ c hΘ s Bs (A := .fam (.ref S)) hcl w χ j ls hv
      have hrS : sizeOf S ≤ r := by simp at hr; omega
      have hmA : Bnd.arr Bs S ∈ ks := hk _ (by simp [keysIn, hcl])
      have hk' : ∀ b ∈ keysIn Bs S, b ∈ ks := fun b h => hk b (by simp [keysIn, hcl, h])
      simp only [trav, tE, if_neg hcl, resO]
      exact arr_specN₀ hΘ (ks.idxOf (.arr Bs S)) (trav_closed ks Bs S)
        (fun v ρ j' ls' hj' hv' hlt hcρ => trav_specN₀ hΘ s hAH S Bs (dsize ρ) (sizeOf v.1 + 1) r
          (IHLN₀.down ks G δ Θ c Nb hI (lt_of_lt_of_le hlt le_rfl) _ _) hP hrS hA hk' v ρ j' ls' hj'
          (Nat.le_succ _) (Or.inr (Nat.lt_succ_self _)) hv' le_rfl hcρ)
        (hAH Bs S hmA) w χ j ls hj hv hn hc
  | .mu B, Bs, n, K, r, hI, _, hr, hA, hk, w, χ, j, ls, hj, hK, _, hv, hn, hc => by
      by_cases hcl : FoldP.clB 0 (.mu B) = true
      · exact leaf_specN₀ ks G δ Θ c hΘ s Bs hcl w χ j ls hv
      have hm : Bnd.mu (B :: Bs) ∈ ks := hk _ (by simp [keysIn, hcl])
      have hrB : sizeOf B < r := by simp at hr; omega
      have hH := hI B Bs hm (anc_cons hm hA) n K (Or.inr ⟨rfl, Or.inr ⟨rfl, hrB⟩⟩)
      refine travOf_appN (LocTy.view_down hΘ.1 c) (vPostN_down₀ _ δ Θ) _ s w ?_
      simp only [tE, if_neg hcl]
      rw [callE_subst ks _ s w]
      simp only [resO, if_neg hcl]
      exact hH w χ j ls hj hK hv hn hc
  | .unit, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .zero, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .thunk _, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .imm _ _, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .mut _ _, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .box _ _, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .bang _, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .unk, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .int _, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .opq _, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam .unit, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.tensor _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam .zero, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.sum _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.thunk _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.imm _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.mut _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.box _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.bang _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam .unk, Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.tvar _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.mu _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.int _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.fam _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _
  | .fam (.opq _), Bs, _, _, _, _, hP, _, _, _, w, χ, j, ls, _, _, _, hv, _, _ =>
      leaf_specN₀ ks G δ Θ c hΘ s Bs (by exact (clB_iff 0 _).mpr hP) w χ j ls hv

/-- The algebra at the position `p` of the tuple `gs`, applied (Core's `ProjOK`). -/
def ProjOKN₀ (gs : Val) (p : Nat) (A R : VTy) : Prop :=
  ∀ j ls r ρ, j ≤ Nb → vN₀ (ℍ := ℍ) A δ Θ j r ρ → ConsistentX c ρ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ R δ Θ) j ls
      (.app (.app (.val (projV ks.length p)) (.val gs)) (.val r)) ρ

/-- Every listed key's algebra is in the tuple, at the key's first position (Core's `AlgsOK`). -/
def AlgsOKN₀ (gs : Val) : Prop :=
  (∀ B Bs, .mu (B :: Bs) ∈ ks →
    ProjOKN₀ (ℍ := ℍ) ks δ Θ c Nb gs (ks.idxOf (.mu (B :: Bs))) (resO G (B :: Bs) B)
      (G.Res (B :: Bs))) ∧
  ∀ Bs S, .arr Bs S ∈ ks →
    ProjOKN₀ (ℍ := ℍ) ks δ Θ c Nb gs (ks.idxOf (.arr Bs S))
      (.sum .unit (.tensor (G.ResA Bs S) (resO G Bs S))) (G.ResA Bs S)

/-- The array keys' algebras through the handle (Core's `ah_of_algs`). -/
theorem ah_of_algsN₀ (hΘ : Θ.OK) {gs : Val} (h : AlgsOKN₀ (ℍ := ℍ) ks G δ Θ c Nb gs) :
    AHN₀ (ℍ := ℍ) ks G δ Θ c Nb (hG ks gs) := by
  intro Bs S hm j ls x ρ hj hx hc
  have hΦ := LocTy.view_down hΘ.1 c
  refine hG_appN ks hΦ (vPostN_down₀ _ δ Θ) gs _ ?_
  refine selfG_runN ks hΦ (vPostN_down₀ _ δ Θ) gs x _ (.arr Bs S) (List.getElem?_idxOf hm) ?_
  rw [branchV_arr]
  exact h.2 Bs S hm j ls x ρ hj hx hc

/-- The call of the `μ` key `B :: Bs` at the fixed point itself (Core's `HSel`). -/
def HSelN₀ (gs : Val) (B : VTy) (Bs : Stack) (n K : Nat) : Prop :=
  ∀ w χ j ls, j ≤ Nb → sizeOf w.1 ≤ K → vN₀ (ℍ := ℍ) (closedOf B Bs) δ Θ j w χ → dsize χ ≤ n →
    ConsistentX c χ →
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ (G.Res (B :: Bs)) δ Θ) j ls
      (.app (.app (.val (selfG ks)) (.val gs)) (.val (tagV (ks.idxOf (.mu (B :: Bs))) w))) χ

theorem hs_of_selN₀ (hΘ : Θ.OK) {gs : Val} {B : VTy} {Bs : Stack} {n K : Nat}
    (h : HSelN₀ (ℍ := ℍ) ks G δ Θ c Nb gs B Bs n K) :
    HSN₀ (ℍ := ℍ) ks G δ Θ c Nb (hG ks gs) B Bs n K := fun w χ j ls a b d e f =>
  hG_appN ks (LocTy.view_down hΘ.1 c) (vPostN_down₀ _ δ Θ) gs _ (h w χ j ls a b d e f)

/-- One unrolling of the `μ` key `B :: Bs`: the dispatch, the traversal of the body, the
algebra (Core's `hs_step`). -/
theorem hs_stepN₀ (hΘ : Θ.OK) (hok : KeysOK ks) {gs : Val} (halg : AlgsOKN₀ (ℍ := ℍ) ks G δ Θ c Nb gs)
    {B : VTy} {Bs : Stack} {n K : Nat} (hm : .mu (B :: Bs) ∈ ks) (ha : Anc ks (B :: Bs))
    (hI : IHLN₀ (ℍ := ℍ) ks G δ Θ c Nb (hG ks gs) n K (sizeOf B)) :
    HSelN₀ (ℍ := ℍ) ks G δ Θ c Nb gs B Bs n K := by
  intro w χ j ls hj hK hv hn hc
  have hΦ := LocTy.view_down hΘ.1 c
  obtain ⟨hP, hH, hk⟩ := hok.1 B Bs hm
  refine selfG_runN ks hΦ (vPostN_down₀ _ δ Θ) gs w _ (.mu (B :: Bs)) (List.getElem?_idxOf hm) ?_
  rw [branchV_mu]
  have hv' : vN₀ (ℍ := ℍ) (B.subst (env (B :: Bs))) δ Θ j w χ := by
    rw [← inst_closedOf]; exact (vN_unfold₀ hv).2.2
  refine erwp_bind_frame hΦ (opTableN_local _)
    (.appR (.val (.lam (.app (.app (.val (projV ks.length (ks.idxOf (.mu (B :: Bs)))))
      (.val (gs.shift 1 0))) (.var 0)))) .hole)
    (fun E => E = PMap.empty) (ResU.comp_empty_right χ) hc
    (trav_specN₀ ks G δ Θ c Nb hΘ (hG ks gs) (ah_of_algsN₀ ks G δ Θ c Nb hΘ halg) B (B :: Bs) n K
      (sizeOf B) hI hP le_rfl ha hk w χ j ls hj hK (Or.inl hH) hv' hn hc) rfl ?_
  rintro k' hk' ls' r σ₁ E σ hcσ hr rfl hcσ' _
  obtain rfl := ResU.CompS.functional hcσ (ResU.comp_empty_right σ₁)
  simp only [Kont.plug]
  refine erwp_headE hΦ (vPostN_down₀ _ δ Θ) .hole (fun μ => Head.beta μ _ r) rfl ?_
  have e : (Expr.app (.app (.val (projV ks.length (ks.idxOf (.mu (B :: Bs))))) (.val (gs.shift 1 0)))
      (.var 0)).subst 0 r = .app (.app (.val (projV ks.length (ks.idxOf (.mu (B :: Bs))))) (.val gs))
        (.val r) := by
    simp [closed_subst (projV_closed _ _), subst_shift_succ]
  rw [e]
  exact halg.1 B Bs hm k' ls' r _ (hk'.trans hj) hr hcσ'

/-- **Every `μ` key's call meets its spec**, at every measure (Core's `hs_all`). -/
theorem hs_allN₀ (hΘ : Θ.OK) (hok : KeysOK ks) {gs : Val} (halg : AlgsOKN₀ (ℍ := ℍ) ks G δ Θ c Nb gs) :
    ∀ n K B Bs, .mu (B :: Bs) ∈ ks → Anc ks (B :: Bs) → HSelN₀ (ℍ := ℍ) ks G δ Θ c Nb gs B Bs n K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro K
    induction K using Nat.strong_induction_on with
    | _ K ihK =>
      suffices H : ∀ r B Bs, sizeOf B = r → .mu (B :: Bs) ∈ ks → Anc ks (B :: Bs) →
          HSelN₀ (ℍ := ℍ) ks G δ Θ c Nb gs B Bs n K from fun B Bs => H _ B Bs rfl
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ihr =>
        intro B Bs hr hm ha
        refine hs_stepN₀ ks G δ Θ c Nb hΘ hok halg hm ha ?_
        intro B' Bs' hm' ha' n' K' hlt
        refine hs_of_selN₀ ks G δ Θ c Nb hΘ ?_
        rcases hlt with h | ⟨rfl, h | ⟨rfl, h⟩⟩
        · exact ihn n' h K' B' Bs' hm' ha'
        · exact ihK K' h B' Bs' hm' ha'
        · exact ihr (sizeOf B') (hr ▸ h) B' Bs' rfl hm' ha'

end Trav

/-- **The owned fold of `μB₀`** (Core's `fold_spec`). -/
theorem fold_specN₀ {B₀ : VTy} (hB : PBody B₀) (G : Algs) (δ : LSub) {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} {Nb : Nat} {gs : Val}
    (halg : AlgsOKN₀ (ℍ := ℍ) (keys B₀) G δ Θ c Nb gs) (w : Val) (χ : WRes) (j : Nat)
    (ls : List SRec) (hj : j ≤ Nb) (hv : vN₀ (ℍ := ℍ) (.mu B₀) δ Θ j w χ) (hc : ConsistentX c χ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (vPostN₀ (G.Res [B₀]) δ Θ) j ls
      (.app (.app (.val (selfG (keys B₀))) (.val gs)) (.val (tagV 0 w))) χ := by
  have h := hs_allN₀ (keys B₀) G δ Θ c Nb hΘ (keys_ok hB) halg (dsize χ) (sizeOf w.1) B₀ []
    (root_mem B₀) (anc_root B₀)
  rw [← closedOf_root] at hv
  have h' := h w χ j ls hj le_rfl hv le_rfl hc
  rwa [root_idx] at h'

/-! ### The rule -/

/-- Every algebra's type holds the empty resource (Core's `algTy_empty`). -/
theorem algTy_emptyN₀ (G : Algs) (k : Bnd) {δ : LSub} {Θ : LocTy} {j : Nat} {v : Val} {σ : WRes}
    (h : vN₀ (ℍ := ℍ) (FoldP.algTy G k) δ Θ j v σ) : σ = PMap.empty := by
  match k, h with
  | .mu [], h => exact h.2
  | .mu (_ :: _), h => exact h.1
  | .arr _ _, h => exact h.1

/-- A tuple of values of types holding the empty resource: its components (Core's
`tup_split`). -/
theorem tup_splitN₀ {δ : LSub} {Θ : LocTy} {j : Nat} :
    ∀ (As : List VTy) (g : Val) (ρ : WRes),
      (∀ A ∈ As, ∀ v σ, vN₀ (ℍ := ℍ) A δ Θ j v σ → σ = PMap.empty) →
      vN₀ (ℍ := ℍ) (tupTy As) δ Θ j g ρ →
      ρ = PMap.empty ∧ ∃ vs, g = tupV vs ∧ vs.length = As.length ∧
        ∀ (p : Nat) (a : Val) (A : VTy), vs[p]? = some a → As[p]? = some A →
          vN₀ (ℍ := ℍ) A δ Θ j a PMap.empty
  | [], g, ρ, _, h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, [], rfl, rfl, fun p a A h => by simp at h⟩
  | [A], g, ρ, hA, h => by
      have hρ := hA A (by simp) g ρ h
      subst hρ
      refine ⟨rfl, [g], rfl, rfl, fun p a A' h₁ h₂ => ?_⟩
      cases p with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
          subst h₁; subst h₂; exact h
      | succ p => simp at h₁
  | A :: B :: r, g, ρ, hA, h => by
      obtain ⟨a, g', ρ₁, ρ₂, rfl, hc, h₁, h₂⟩ := h
      have e₁ := hA A (by simp) a ρ₁ h₁
      subst e₁
      obtain ⟨e₂, vs, rfl, hlen, hvs⟩ :=
        tup_splitN₀ (B :: r) g' ρ₂ (fun A' hA' => hA A' (List.mem_cons_of_mem _ hA')) h₂
      subst e₂
      refine ⟨eq_empty_of_compS_empty hc, a :: vs, ?_, by simp [hlen],
        fun p a' A' h₁' h₂' => ?_⟩
      · cases vs with
        | nil => simp at hlen
        | cons c vs => rfl
      · cases p with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁' h₂'
            subst h₁'; subst h₂'; exact h₁
        | succ p => exact hvs p a' A' (by simpa using h₁') (by simpa using h₂')

/-- The algebras out of a tuple valid at the keys' algebra types (Core's `algsOK_of_tuple`):
each is read at the run's world by `bang_app₀`, at every index up to the tuple's. -/
theorem algsOK_of_tupleN₀ (ks : List Bnd) (G : Algs) (δ : LSub) {Θ₀ Θ : LocTy} (hΘ : Θ.OK)
    (c : Loc → Option Life) {Nb : Nat} (vs : List Val) (hlen : vs.length = ks.length)
    (hvs : ∀ (p : Nat) (a : Val) (A : VTy), vs[p]? = some a → (ks.map (FoldP.algTy G))[p]? = some A →
      vN₀ (ℍ := ℍ) A δ Θ₀ Nb a PMap.empty) :
    AlgsOKN₀ (ℍ := ℍ) ks G δ Θ c Nb (tupV vs) := by
  have hΦ := LocTy.view_down hΘ.1 c
  have hget : ∀ k ∈ ks, ∃ a, vs[ks.idxOf k]? = some a ∧
      vN₀ (ℍ := ℍ) (FoldP.algTy G k) δ Θ₀ Nb a PMap.empty := by
    intro k hk
    have hlt : ks.idxOf k < vs.length := hlen ▸ List.idxOf_lt_length_of_mem hk
    obtain ⟨a, ha⟩ : ∃ a, vs[ks.idxOf k]? = some a := ⟨_, List.getElem?_eq_getElem hlt⟩
    refine ⟨a, ha, hvs _ a _ ha ?_⟩
    simp [List.getElem?_idxOf hk]
  have hrun : ∀ k ∈ ks, ∀ A R, FoldP.algTy G k = .bang (.lolli A R) →
      ProjOKN₀ (ℍ := ℍ) ks δ Θ c Nb (tupV vs) (ks.idxOf k) A R := by
    intro k hk A R hA j ls r ρ hj hr hc
    obtain ⟨a, ha, hva⟩ := hget k hk
    rw [hA] at hva
    rw [← hlen]
    exact proj_runN hΦ (vPostN_down₀ _ δ Θ) vs _ a ha r (bang_app₀ hΘ hj hva hc hr ls)
  exact ⟨fun B Bs hm => hrun _ hm _ _ rfl, fun Bs S hm => hrun _ hm _ _ rfl⟩

/-- **The general owned fold at `SemJN₀`** (Core's `foldOwnG_compatX`): `foldOwnG : Algs ⊸
!U(μB₀ ⊸ F R₀)` at every body `B₀` of the class `P` and every list of results. -/
theorem foldOwnG_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} (B₀ : VTy) (hB : PBody B₀) (Rs : List VTy)
    (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (foldOwnGV B₀)) (.val (foldGTy B₀ Rs)) := by
  intro δ γ Θ c n ls ρ _ hΘ _ _ hg₀
  have hρ : ρ = PMap.empty := gN_deadP₀ hΓ hg₀
  subst hρ
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.val (foldOwnGV B₀))) _
  rw [substAll_closed (foldOwnGV_closed B₀)]
  refine erwp_val ?_
  intro Θ₁ _ hOK₁ c₁ _ ls₁ c₂ k₁ _ gs ρv ρ' hcomp hv₁ _
  obtain ⟨hρv, vs, rfl, hlen, hvs⟩ := tup_splitN₀ _ gs ρv
    (fun A hA v σ hv => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hA
      exact algTy_emptyN₀ _ k hv) hv₁
  subst hρv
  obtain rfl := eq_of_compS_empty_left hcomp
  have hΦ := LocTy.view_down hOK₁.1 c₂
  refine erwp_headE hΦ (vPostN_down₀ _ δ Θ₁) .hole (fun μ => Head.beta μ _ (tupV vs)) rfl ?_
  rw [foldOwnGV_subst]
  refine erwp_val ⟨rfl, ?_⟩
  intro Θ₂ _ hOK₂ c₃ _ ls₂ c₄ k₂ hk₂ w ρw ρ'' hcomp' hw hc₄
  obtain rfl := eq_of_compS_empty_left hcomp'
  have hΦ₂ := LocTy.view_down hOK₂.1 c₄
  have halg := algsOK_of_tupleN₀ (keys B₀) (algsOf (keys B₀) Rs) δ hOK₂ c₄ (Θ₀ := Θ₁) vs
    (by simpa using hlen) (fun p a A ha hA => vN_le₀ hk₂ (hvs p a A ha (by simpa using hA)))
  refine erwp_headE hΦ₂ (vPostN_down₀ _ δ Θ₂) .hole (fun μ => Head.beta μ _ w) rfl ?_
  have e : Expr.subst 0 w (.app (.app (.val (selfG (keys B₀))) (.val ((tupV vs).shift 1 0)))
      (tagE 0 (.var 0))) = .app (.app (.val (selfG (keys B₀))) (.val (tupV vs))) (.val (tagV 0 w)) := by
    simp [tagE, tagV, closed_subst (selfG_closed _), subst_shift_succ]
  rw [e]
  exact fold_specN₀ hB _ δ hOK₂ halg w ρ'' k₂ ls₂ le_rfl hw hc₄

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
