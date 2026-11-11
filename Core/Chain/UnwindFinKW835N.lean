import Core.Chain.UnwindKW835N
import Core.Chain.ThenK835N

/-!
# The unwinding lends' finaliser at its own row, at the typed world  `[spec §19, §27]`

The hand-over of K-b: an unwinding lend's callback runs at one world (`cN_unwind_iff` at its row
`Σ_M`, whose operations are abortive), and its finaliser `d` gets the lend's source back at a
`raise` and runs at its own row `Σ_D ≤ Σ`, at the worlds of `Σ`'s tables.

* `erwpK_unwindD`: the frame `ubind (N, D)` around a one-world run at an abortive table whose
  raises carry a claim, read at a world of a row's table family (`RowRd`): a return runs `N` at
  that world; a `raise` runs `D (); raise p` there (`seq_raise_runK`, `[finalise]`), `D` from the
  claim, the raise's entry read in `Σ`.
* `fin_claimID`, `fin_claimMD`: the finaliser `λ_. d ℓ` from the claim an `imm` lend or a `mut`
  reborrow hands back, `d`'s judgment at `U(src ⊸ F_{Σ_D} 1)`: an `erwpK` run at `Σ_D`'s tables
  (`erwpK_bindR`, then `d`'s value applied at the run's world, `cN_effOf_tabF`).
* `withbor2UD_sem`: `withbor (2)` at the rows `(Σ_M, Σ_D, Σ)`, end to end at `vN`: the callback at
  `Σ_M` at one world under the Mut Frame, as `withbor2U_sem`; the result at `Σ`'s tables, the
  frame `erwpK_unwindD`, the finaliser `fin_claimID`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE opPayload ubindE)

variable {ι M : Type} {R : RowRd ι M}

/-- **The finaliser frame around a one-world run at an abortive table, its finaliser at its own
row** (`erwp_ubindRaise` with `[finalise]` at `erwpK`): the body `M` runs at one location family
`R.Φ x`, at a table `T` of abortive entries whose raises carry `Rc`. A return runs `N` at the world
`x`; a `raise` runs `D (); raise p` at `x` (`seq_raise_runK`), `D` from the claim at `Σ_D ≤ Σ`, the
raise's entry the one `Σ` holds at its key, its payload persistent where `Σ_D` may stop at an
unrestricted operation.  `[spec §19, §27]` -/
theorem erwpK_unwindD (hR : R.OK) (hPE : R.PayExt) (S SD : Row) (hDS : RowLe SD S) {μ : M}
    {T : OpTabN} (hTa : ∀ m i en, T m i = some en → en.abort = true)
    (hTr : ∀ m i en, T m i = some en → m ≠ 0) {x : ι} (hx : R.Inv x)
    (hTS : ∀ m i en, T m i = some en → ∃ o, Row.find S m i = some o ∧ o.abort = true ∧
      (SD.UnrD → o.A.Persistent) ∧
      ∀ k ls v ρ, en.PA k ls v ρ → R.vr o.A R.δ (R.Θ x) k v ρ)
    {Rc : Nat → WProp} (N D : Val) {Qd : ι → PostN}
    (hQd : ∀ y k ls v ρ, Qd y k ls v ρ → v = .unit ∧ NoOwn ρ)
    {Qin : PostN} {Qout : ι → PostN} (hQout : ∀ y, (Qout y).Down) (n : Nat)
    (hD : ∀ k, k ≤ n → ∀ ls ρ, Rc k ρ → erwpK (ℍ := ℍ) R.V R.Φ
      (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf SD .unit) z)) Qd x k ls
      (.app (.val D) (.val .unit)) ρ)
    (hN : ∀ k, k ≤ n → ∀ ls (v : Val) ρ, Qin k ls v ρ → erwpK (ℍ := ℍ) R.V R.Φ
      (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)) Qout x k ls
      (.app (.val N) (.val v)) ρ) :
    ∀ ls M ρ, erwp (ℍ := ℍ) (R.Φ x) (opTableR T Rc) Qin n ls M ρ →
      erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)) Qout x n ls
        (ubindE (.pair N D) M) ρ := by
  intro ls M ρ h
  have hΦ := hR.ΦDown x hx
  have hLo : ∀ z, (opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)).Local :=
    fun z => opTableK_local _ _
  have hPD := erwpPostK_down (V := R.V x)
    (opTableK_downI (lo := R.fl x) (tabF_downI hR μ (CTy.effOf S .unit) x)) (Q := Qout) hQout
  rw [← ubK_plug, erwpK_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at (opTableR_local T Rc) le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`: `N` at the world `x`
    have hstep := fun μ' => then_ret (ℍ := ℍ) μ' N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det hΦ (hPD _) hstep (erwpK_unfold_at hLo hk (hN k hk ls' v σ hv))
  · -- the table is abortive: no `perform`
    obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    rw [hTa m i en hT] at ha; cases ha
  · -- `[finalise]`: `D (); raise p` at `x`, `D` from the claim
    obtain ⟨⟨rfl, hK₁, hT, -⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hRc⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨o, hfo, hao, hpers, hvr⟩ := hTS m i en hT
    have hm0 := hTr m i en hT
    refine rwpG_det hΦ (hPD _)
      (fun μ' => (then_fin (ℍ := ℍ) (μ := μ') (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    -- the payload beside the finaliser, the leftover `NoOwn` part as garbage
    obtain ⟨X, hX, hcX⟩ := compS_exch hcan hcσ
    have hrun := seq_raise_runK (ℍ := ℍ) hR hPE S SD hDS hfo hao (μ := μ) hQd hQout k x hx ls'
      _ ρR (hD k hk ls' ρR hRc) ρa X ⟨hvr k ls' v ρa hPA, hnA⟩
      (fun hu => hR.vrPers _ (hpers hu) _ _ _ _ (hvr k ls' v ρa hPA)) (ResU.CompS.comm hX)
    exact erwpK_unfold_at hLo hk (erwpK_garbage hcX hnn hrun)

end BoCa.Fig16.LogRel.Core.Chain.SI


namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont ubindE)
open BoCa.Fig16.LogRel (LtLife substAll)

/-- **The finaliser `λ_. d ℓ` at its own row, from the source handed back**: `d`'s judgment at
`U(src ⊸ F_{Σ_D} 1)` read at the world and an index at or below `N`, the source a value of `src`
at `ℓ`; the run is at `Σ_D`'s tables from the world `⟨Θ, c, lo⟩` (`erwpK_bindR`: `d` to its value,
then the value applied there, `cN_effOf_tabF`).  `[spec §19, §27]` -/
theorem fin_claimD {src : VTy} {SD : Row} {d : Expr} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} (lo : Life) {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.thunk (.arr src (CTy.effOf SD .unit)))) δ Θ c
      k ls d PMap.empty)
    {l : Loc} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN (ℍ := ℍ) src δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit) z))
      (fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ⟨Θ, c, lo⟩ k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ := by
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  have hL : ∀ z : KW, (opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit)
      z)).Local := fun z => opTableK_local _ _
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ
    (opTableK_downI (tabF_downI (rdN_ok δ) () (CTy.effOf SD .unit) _))
    (fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app (d.shift 1 0) (.val (Val.loc l)))) =
      (Kont.appL .hole (Val.loc l)).plug d := by
    simp [Kont.plug, Expr.subst, subst_shift_succ (j := 0) (d := 0) _ d (le_refl _),
      Expr.shift_zero, Val.loc]
  rw [e]
  refine erwpK_bindR hL hΦ (Kont.appL .hole (Val.loc l)) ?_
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret (hd k hk ls))) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have hC := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.loc l) τ₂ τ hcτ (vN_le hk' h) hcτ'
  exact (cN_effOf_tabF SD .unit δ Θ c k' ls' _ τ).mp hC lo

/-- **`fin_claimD` at an `imm` lend's claim**: the cell owned again with the content it was lent
with, a `Ref A` value (`fin_claimI` at `Σ_D`).  `[spec §19, §27]` -/
theorem fin_claimID {A : VTy} {SD : Row} {d : Expr} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} (lo : Life) {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.thunk (.arr (.ref A) (CTy.effOf SD .unit))))
      δ Θ c k ls d PMap.empty)
    {l : Loc} {w : Val} {σ : WRes} (hw : vN (ℍ := ℍ) A δ Θ N w σ) {k : Nat} (hk : k ≤ N)
    {ls : List SRec} {ρ : WRes} (h : claimI l w σ k ρ) (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit) z))
      (fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ⟨Θ, c, lo⟩ k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ :=
  fin_claimD hΘ lo hd hk ⟨l, w, σ, rfl, h, vN_le hk hw⟩ hc

/-- **`fin_claimD` at a reborrow's source**: a `Mut @a A` value at `ℓ` (`fin_claimMN` at `Σ_D`).
`[spec §19, §27]` -/
theorem fin_claimMD {a : Lifetime.Life} {A : VTy} {SD : Row} {d : Expr} {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.OK) {c : Loc → Option Life} (lo : Life) {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN (ℍ := ℍ) (.ret (.thunk (.arr (.mut a A) (CTy.effOf SD .unit))))
      δ Θ c k ls d PMap.empty)
    {l : Loc} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (CTy.effOf SD .unit) z))
      (fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ⟨Θ, c, lo⟩ k ls
      (.app (.val (DFv (d.shift 1 0) l)) (.val .unit)) ρ :=
  fin_claimD hΘ lo hd hk h hc

/-! ### `withbor (2)` at an unwinding row, its finaliser at its own row -/

/-- **`withbor (2)`'s type with the callback at `Σ_M` and the result at `Σ`**: `withbor2UTy` at
`Σ_M = Σ`.  `[spec §19, §27]` -/
def withbor2UTyD (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (SM S : Row) : VTy :=
  withborUTy (.ref A) (cbUTy x bnd (.mut (.var x) A) B SM) S (.tensor (.ref A) B)

/-- **`withbor (2)` at an unwinding row, its finaliser at `Σ_D`, is a value of its type**:
`withbor2U_sem` with the callback at `Σ_M` (`Row.Unwind`, one world, `cN_unwind_iff`) and the
result at `Σ ≥ Σ_M, Σ_D` read at the worlds of `Σ`'s tables (`cN_effOf_tabF`); the finaliser frame
is `erwpK_unwindD`, the finaliser `fin_claimID`.  `[spec §19, §27]` -/
theorem withbor2UD_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {SM SD S : Row} {d : Expr}
    {δ : LSub} (hδ : Δ.Models δ) (hO : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hA : ¬ VFree x A)
    (hB : ¬ VFree x B) (hS : SM.Unwind x) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hPend : SD.UnrD → SM.PendPers) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN (ℍ := ℍ) (.ret (.thunk (.arr (.ref A) (CTy.effOf SD .unit)))) δ Θ c k ls d PMap.empty) :
    vN (ℍ := ℍ) (withbor2UTyD x Δ.meetOfDom A B SM S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := vN_le hk' hu
  refine (cN_effOf_tabF S _ δ Θ c k' ls _ ρ'').mpr fun lo => ?_
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S (.tensor (.ref A) B) .unit]
  refine erwpK_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set T := tabUN (ℍ := ℍ) SM δ Θ with hTdef
  have hTd : T.Down := tabUN_down SM δ Θ
  have hQo : ∀ y : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ y.Θ k v ρ) :=
    fun y k _ v ρ h => vN_down _ δ y.Θ k v ρ h
  have hTo := opTableK_downI (lo := lo) (tabF_downI (rdN_ok (ℍ := ℍ) δ) () (CTy.effOf S .unit)
    (⟨Θ, c, lo⟩ : KW))
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) ((d.shift 3 0).app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv (d.shift 1 0) l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_shift_succ (j := 2) (d := 2) _ d (le_refl _),
      subst_shift_succ (j := 1) (d := 1) _ d (le_refl _)]
  rw [e₃]
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_right hcl (consistentX_left hc' hcon hv'') hvu
  have hko : (CellU.ownOf (Loc := Loc) w₀).kind ≠ Kind.imm := by simp
  have hown : ρu.get l = some (CellU.ownOf w₀) :=
    (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
  -- the lend's lifetime
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨b, hdef, hOb⟩ := hO
  obtain ⟨βP, hβP⟩ : ∃ β : Life, b.interp δ = some β := hdef δ hδ
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(βP ⊓ βf ⊓ γ))
  have hαlt : α < βP ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαP : α < βP := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hunif : ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ' j u r →
      r.InStratum α :=
    vN_outlivesLe hδ hβP hαP hOb
  have houtP : σ₀.InStratum α := hunif Θ k' w₀ σ₀ hw₀
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP
  set Fam : Nat → Val → SPropS Loc Val α := famL α P Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam k' w₀ ⟨σ₀, houtP⟩ := (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact hw₀)
  -- the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ'.view c' = (Θ.view c).set l α Fam := LocTy.view_add Θ c l α Fam
  have hcf' : ConsistentX c' ρf := consistentX_setLife hcf (exS_none_of_part hc' hv'' hown hko) α
  have hcσ' : ConsistentX c' σ₀ :=
    consistentX_setLife hcσ (exS_none_of_part hcl hvu (ResU.single_get_self _ _) hko) α
  set Qb : PostN := fun k _ b ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k
    (Val.pair (Val.loc l) b) ρ with hQb
  have hM := erwp_M_frameR (Φ := Θ.view c) (l := l) (A := α) (F := Fam) hFamD
    (tabUN_lendOKR hS δ Θ α) (Q := Qb)
    k' k' le_rfl ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ ρu ρf ρ''
    houtP houtf (Fam k') (fun _ _ h => h) hwit hcl hc' (fun BM hBM => ?_)
  · -- the claim with the view's consistency, then the finaliser frame
    have hM' := erwp_claimX_abort (tabUN_abort hS δ Θ) hcon hM
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX (claimR l α Fam) c j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [tabUN_abort hS δ Θ m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwpK_unwindD (R := rdN (ℍ := ℍ) δ) (rdN_ok δ) (rdN_payExt δ) S SD hDS (μ := ())
      (T := T) (tabUN_abort hS δ Θ)
      (fun m i en h => tabUN_named hS δ Θ m i en h (tabUN_abort hS δ Θ m i en h))
      (x := (⟨Θ, c, lo⟩ : KW)) hΘ.1 ?_ (NFv l) (DFv (d.shift 1 0) l)
      (Qd := fun z k _ v ρ => vN (ℍ := ℍ) .unit δ z.Θ k v ρ) ?_ hQo k' ?_ ?_ ls _ ρ'' hM''
    · -- the raise's entry, read in `Σ`
      intro m i en h
      obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨o', hf', hle⟩ := hMS m i o hf
      have hab : o.abort = true := (hS o (Row.find_mem hf).1).1
      refine ⟨o', hf', by rw [← hle.1.abort_eq]; exact hab, fun hu => ?_, fun k ls v ρ hp => ?_⟩
      · have h₁ := ((hPend hu) o (Row.find_mem hf).1).1 hab
        rwa [hle.1.2.2.2.1] at h₁
      · show vN (ℍ := ℍ) o'.A δ Θ k v ρ
        rw [← hle.1.2.2.2.1]; exact hp
    · rintro y k ls' v σ ⟨rfl, rfl⟩
      exact ⟨rfl, noOwn_empty⟩
    · -- the finaliser at `Σ_D`, from the claim
      intro j hj ls' ρ hR
      obtain ⟨⟨⟨w, σ, hσ, hF, hclm⟩, hcR⟩, -⟩ := hR
      have hwσ : vN (ℍ := ℍ) A δ Θ j w σ := by rw [← hAδ]; exact (vN_above A δ' Θ hσ).mp hF
      exact fin_claimID hΘ lo
        (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hj.trans (hk'.trans hk))) ls) hwσ le_rfl hclm hcR
    · -- a return: `(ℓ, b)` at the world `⟨Θ, c, lo⟩`
      intro j _ ls' b ρ hq
      refine erwpK_det (x := (⟨Θ, c, lo⟩ : KW)) hΦ hTo hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwpK_val (v := Val.pair (Val.loc l) b) (KW.postK_refl _) hq
  · -- the callback, at the lend's world and view, from the borrow
    rw [← hview]
    have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
    have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam k') hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P le_rfl houtP hwit,
        fun Θ'' j u r h => hunif Θ'' j u r (by rw [← hAδ]; exact h)⟩
    have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
      (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
    have h2 := h1 c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
    rw [cN_unwind_iff hS, tabUN_eq_add hS δ hfr l Fam] at h2
    refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN (ℍ := ℍ) A δ Θ k w σ := by
      rw [← hAδ]; exact (vN_above A δ' Θ hσ).mp hFσ
    have hbB' : vN (ℍ := ℍ) B δ Θ k b ρ' :=
      vN_local B δ Θ l α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
    exact ⟨Val.loc l, b, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩


end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
