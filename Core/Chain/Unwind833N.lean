import Core.Chain.Borrow834N

/-!
# The unwinding reborrows `withbor (3)` and `withload` at `SemJN₀`  `[spec §19, §62]`

Core's `withbor3U_compatX` and `withloadU_compatX` (`Core/EffBorrow.lean`), step by step, at the
per-lend world, any `Δ` and a `Row.Unwind x` row. Every entry of such a row's table is abortive
(`tabN_unwind_abort`), so the callback's stops are raises and nothing is resumed under the
borrow.

* `erwp_M_antiFrameU`: the Mut Anti-Frame at an unwinding row (Core's `ewpTS_M_antiFrameU`),
  `erwp_M_antiFrameCR` at the row's own table as its twin. The twin guards no stop; only the
  raises' claim (`hRin`/`hRout`) remains, and the cancel obligations are vacuous.
* `withbor3U_sem`, `withbor3U_compatN`: `withbor3S_compat₀`'s steps with the bound `Δ.meetOfDom`,
  the callback's table the lender's (`tabN_unwind_eq_add`), the anti-frame `erwp_M_antiFrameU`,
  the claim consistent (`erwp_claimX_abort`), the finaliser frame at a raise (`erwp_ubindRaise`,
  `fin_claimMN`).
* `withloadU_sem`, `withloadU_compatN`: `withloadS_compat`'s steps, 6.150 across the row's raises
  (`withload_rebT₀`, `erwp_rebGen`). An unwinding row may hold an unrestricted operation; it is
  abortive, so it never resumes and the reborrow is never re-entered through it
  (`OpTabN.RebOKR.entry` reads only resumable entries). The row's table admits the reborrow at
  every `β` (`tabN_unwind_rebOKR`) and has no cancel obligation (`tabN_unwind_rebClosed`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- A table is its own twin. -/
theorem OpTabN.Twin.refl (T : OpTabN) : T.Twin T :=
  fun _ _ en h => ⟨en, h, rfl, rfl, rfl, rfl, rfl⟩

/-- **The Mut Anti-Frame at a table whose every entry is abortive** (Core's
`ewpTS_M_antiFrameU`): `erwp_M_antiFrameCR` with the table its own twin. No stop is resumable, so
the guard reads no stop and no cancel obligation is transferred; at a raise the claim is sealed
again into the source's entry and carried out (`hRout`). -/
theorem erwp_M_antiFrameU {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableGR T G Rin) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableR T Rout) Q n ls e ρ :=
  erwp_M_antiFrameCR hΦ hF (OpTabN.Twin.refl T)
    (fun m i en h ha => by rw [hab m i en h] at ha; cases ha) hG hRin hRout
    (fun m i en _ h _ ha => by rw [hab m i en h] at ha; cases ha)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head ubindE)

/-! ### An unwinding row's table -/

/-- **An unwinding row's table may be stopped at under a `mut` lend at any `α`, cancellable stops
included**: it has no resumable entry, and its payloads lie in every stratum. -/
theorem tabN_unwind_lendOKCR {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (α : Life) :
    (tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c).LendOKCR α where
  entry := fun m i en h ha => by
    rw [tabN_unwind_abort hS R δ Θ c m i en h] at ha; cases ha
  pa := (tabN_unwind_lendOKR hS R δ Θ c α).pa
  pb := (tabN_unwind_lendOKR hS R δ Θ c α).pb

/-- **An unwinding row's table may be stopped at under a reborrow at any `β`**: it has no
resumable entry, unrestricted or not, and its payloads lie in every stratum. -/
theorem tabN_unwind_rebOKR {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (β : Life) :
    (tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c).RebOKR β where
  entry := fun m i en h ha => by
    rw [tabN_unwind_abort hS R δ Θ c m i en h] at ha; cases ha
  pa := (tabN_unwind_lendOKR hS R δ Θ c β).pa
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
    have hp' : vN₀ (ℍ := ℍ) o.B δ Θ k w ρ := hp.1
    rw [unwind_B hS ho] at hp'
    exact hp'.elim

/-- **An unwinding row's table has no cancel obligation**: every entry is abortive. -/
theorem tabN_unwind_rebClosed {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (β : Life) (ρi χ : WRes) (Ok : List SRec → Prop) :
    RebClosed β ρi χ Ok (tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c) := by
  intro m i en h ha
  rw [tabN_unwind_abort hS R δ Θ c m i en h] at ha; cases ha

/-- **An unwinding row's table does not read `'x`, nor its base.** -/
theorem tabN_unwind_extend {S : Row} {x : LifeVar} (hS : S.Unwind x) (R₁ R₂ : VTy) (δ : LSub)
    (Θ : LocTy) (α : Life) (c : Loc → Option Life) :
    tabN₀ (ℍ := ℍ) (CTy.effOf S R₁) (δ.extend x α) Θ c = tabN₀ (ℍ := ℍ) (CTy.effOf S R₂) δ Θ c := by
  induction S with
  | nil => rfl
  | cons o S ih =>
      have ho : o ∈ o :: S := List.mem_cons_self ..
      have hS' : Row.Unwind S x := fun o' ho' => hS o' (List.mem_cons_of_mem _ ho')
      have hA : vN₀ (ℍ := ℍ) o.A (δ.extend x α) Θ = vN₀ (ℍ := ℍ) o.A δ Θ := by
        rw [vN_extend_of_not_free₀ (hS o ho).2.2.1 δ α]
      have hB := unwind_B hS ho
      simp only [CTy.effOf, tabN₀]
      rw [ih hS', hA, hB,
        entN_fin_congr (f := finN₀ (ℍ := ℍ) o.fin (δ.extend x α) Θ c)
          (f' := finN₀ (ℍ := ℍ) o.fin δ Θ c) (fun hcap => by simp [capB, VTy.isZero] at hcap)]
      rfl

/-! ### `withbor (3)` at an unwinding row -/

/-- **The finaliser `λ_. d ℓ` consumes a `Mut @a A` source**, `d`'s judgment at `Mut @a A ⊸ 1`
read at the world and an index at or below `N` (`fin_claimM₀` with the judgment at the run's
world). -/
theorem fin_claimMN {a : Lifetime.Life} {A : VTy} {d : Expr} (hdc : closedAt 0 d = true)
    {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls,
      cN₀ (ℍ := ℍ) (.ret (.lolli (.mut a A) .unit)) δ Θ c k ls d PMap.empty)
    {l : Loc} {k : Nat} (hk : k ≤ N) {ls : List SRec} {ρ : WRes}
    (h : vN₀ (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (DFv d l)) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app d (.val (Val.loc l)))) =
      (Kont.appL .hole (Val.loc l)).plug d := by
    simp [Kont.plug, Expr.subst, subst_closedAt d (s := _) hdc (Nat.zero_le _), Val.loc]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd k hk ls
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty hd0) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.loc l) τ₂ τ hcτ (vN_le₀ hk' h) hcτ'
  exact rwp_of_erwp_empty this

/-- **`withbor (3)` at an unwinding row is a value of its type**: `withborU d`, at
`Mut @a A ⊸ (∀'x ⊏ @Δ. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a A ⊗ B)` with `Σ` a `Row.Unwind x`
row. Core's `withbor3U_compatX`, step by step, as `withbor3S_compat₀`:

1. the source is `loc ℓ` with its cell `ℓ ↦ mut(β, w₀, σ₀, F_o j₀)`, `F_o = famL β 𝒱⟦A⟧ Θ`;
2. `withborU d ℓ f` steps to the callback under the finaliser frame `then b. (ℓ, b) unwind d ℓ`;
3. `MutFrame`'s premise read off the borrow: every value of `A` is in `Res_β` (`hunif`);
4. the anti-frame at the source's own entry: `c ℓ = β` (`consistentX_get`) and the view types
   `ℓ` with `F_o` (`reseal_at_entry`);
5. the opened cell lent at a fresh `α` below `β`, the bound `Δ.meetOfDom` and the callback's
   stratum (`erwp_M_frameCRG` at the row's table, `tabN_unwind_lendOKCR`), the anti-frame across
   the row's raises (`erwp_M_antiFrameU`, Core's `ewpTS_M_antiFrameU`);
6. the callback at the world `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧ Θ` and the view `setLife c ℓ α`, its table
   the lender's (`tabN_unwind_eq_add`), from the borrow `Mut @α A` (`lend_mutL`);
7. its result `['x] B` back at `Θ` (`vN_local₀`); the content handed back in `F_i k` is in `F_o k`
   (`hunif`, `vN_above₀`), and the resealed cell is a `Mut @a A` value again, beside the result and
   in every raise's claim;
8. the claim consistent with the view (`erwp_claimX_abort`) and the finaliser frame consuming it
   with `d` (`erwp_ubindRaise`, `fin_claimMN`).

Premises: `hδ`, `hA`, `hB`, `hS`, `hdc` are the rule's; `hd` is the finaliser's judgment at the
run's world and every lower index. -/
theorem withbor3U_sem {Δ : LifeCtx} {a : Lifetime.Life} {x : LifeVar} {A B : VTy} {S : Row}
    {d : Expr} {δ : LSub} (hδ : Δ.Models δ) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (hS : S.Unwind x) (hdc : closedAt 0 d = true) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN₀ (ℍ := ℍ) (.ret (.lolli (.mut a A) .unit)) δ Θ c k ls d PMap.empty) :
    vN₀ (ℍ := ℍ) (withbor3UTy a x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  set P : CPredL := fun Θ' j u r => vN₀ (ℍ := ℍ) A δ Θ' j u r with hP
  -- step 1
  obtain ⟨α₀, hα₀, (β : Life), hα₀β, hm, hunif⟩ := vN_le₀ hk' hu
  obtain ⟨l, w₀, σ₀, hσ₀, j₀, hw₀, hkj, rfl, hl, rfl⟩ := id hm
  rw [cN_effOf₀]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.mut a A) B) with hFo
  set T := tabN₀ (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hab : ∀ m i en, T m i = some en → en.abort = true := tabN_unwind_abort hS _ δ Θ c
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.mut a A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
  set Qin : PostN := fun k _ b ρ =>
    vN₀ (ℍ := ℍ) (.tensor (.mut a A) B) δ Θ k (Val.pair (Val.loc l) b) ρ with hQin
  -- step 2
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv d l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the source's cell
  set cellβ := ResU.single l (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) with hcellβ
  have hvu : ResU.Valid cellβ := (ResU.Valid.split hc' hv'').1
  have hkm : (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : ρ''.get l = some (CellU.mutOf β w₀ σ₀ hσ₀ (famL β P Θ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc' (ResU.single_get_self _ _) hkm).2
  -- step 4
  have hcl : c l = some β := by
    have h := consistentX_get hcon hv'' hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  obtain ⟨-, -, -, -, -, -, -, hFv, -⟩ :=
    reseal_at_entry (Θ' := Θ) (fun _ _ _ h => h) hcl (vN_fam_down₀ A δ β Θ) hm
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_mut_wit (consistentX_left hc' hcon hv'') hvu
  -- steps 3 and 5: the lend's lifetime, fresh, below `β`, the bound and the callback's stratum
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(β ⊓ βf ⊓ γ))
  have hαlt : α < β ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαβ : α ≤ β := hαlt.le.trans (inf_le_left.trans inf_le_left)
  have houtP : σ₀.InStratum α := hσ₀.mono hαβ
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN₀ (ℍ := ℍ) A δ' = vN₀ (ℍ := ℍ) A δ := vN_extend_of_not_free₀ hA δ α
  have hBδ : vN₀ (ℍ := ℍ) B δ' = vN₀ (ℍ := ℍ) B δ := vN_extend_of_not_free₀ hB δ α
  set P' : CPredL := fun Θ' j u r => vN₀ (ℍ := ℍ) A δ' Θ' j u r with hP'
  set Fam : Nat → Val → SPropS Loc Val α := famL α P' Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down₀ A δ' α Θ
  have hwit : Fam j₀ w₀ ⟨σ₀, houtP⟩ :=
    (vN_above₀ A δ' Θ houtP).mpr (by rw [hAδ]; exact (vN_above₀ A δ Θ hσ₀).mp hw₀)
  -- step 7's inclusion: the content handed back in `F_i k` is in `F_o k`
  have hoi : ∀ k w σ (h : σ.InStratum α), Fam k w ⟨σ, h⟩ →
      ∃ h' : σ.InStratum β, famL β P Θ k w ⟨σ, h'⟩ := by
    intro k w σ h hw
    have hv : vN₀ (ℍ := ℍ) A δ Θ k w σ := by rw [← hAδ]; exact (vN_above₀ A δ' Θ h).mp hw
    exact ⟨hunif Θ k w σ hv, (vN_above₀ A δ Θ (hunif Θ k w σ hv)).mpr hv⟩
  have hG : ∀ k ls ρ, CellFold l α Fam k ls ρ → CellFold l β (famL β P Θ) k ls ρ := by
    rintro k ls ρ ⟨w, χ, h, hw, R, rest, h1, h2⟩
    obtain ⟨h', hw'⟩ := hoi k w χ h hw
    exact ⟨w, χ, h', hw', R, rest, h1, h2⟩
  have hRin : ∀ k ρ, claimR l α Fam k ρ → claimR l β (famL β P Θ) k ρ := by
    rintro k ρ ⟨w, σ, h, hw, hcl'⟩
    obtain ⟨h', hw'⟩ := hoi k w σ h hw
    exact ⟨w, σ, h', hw', hcl'⟩
  set Rout : Nat → WProp := fun k ρ => vN₀ (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l) ρ with hRoutd
  have hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : famL β P Θ k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (famL β P Θ k) hw)) :=
    fun k w σ h hw => ⟨α₀, hα₀, β, hα₀β, ⟨l, w, σ, h, k, hw, le_rfl, rfl, hl, rfl⟩, hunif⟩
  -- step 6: the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ'.view c' = (Θ.view c).set l α Fam := LocTy.view_add Θ c l α Fam
  have hcf' : ConsistentX c' ρf :=
    consistentX_setLife hcf (exS_none_of_part hc' hv'' (ResU.single_get_self _ _) hkm) α
  have hcσ' : ConsistentX c' σ₀ := consistentX_setLife hcσ (exS_wit_none hvu) α
  -- step 5: the anti-frame at the source, across the row's raises
  have hAF := erwp_M_antiFrameU (Φ := Θ.view c) hΦ hFv hab hG hRin hRout (Q := Qin) k' ls
    (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ hσ₀ j₀ hw₀ ρf ρ'' hc'
    (fun W X hW hX => ?_)
  · -- step 8: the claim consistent, the finaliser frame consuming it
    have hM' := erwp_claimX_abort hab hcon hAF
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX Rout c j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [hab m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwp_ubindRaise hΦ hTd
      (fun m i en h ha => by rw [hab m i en h] at ha; cases ha)
      (tabN_unwind_named hS _ δ Θ c)
      (fun m i en h k ls ls' v ρ _ hp => by
        obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
        exact hp)
      (NFv l) (DFv d l) (fun j ls' ρ hR => ?_) hQo (fun j ls' b ρ hq => ?_) k' ls _ ρ'' hM''
    · obtain ⟨⟨hRj, hcR⟩, hj⟩ := hR
      exact fin_claimMN hdc hΘ
        (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hj.trans (hk'.trans hk))) ls) le_rfl hRj hcR
    · refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.loc l) b) hq
  -- step 5: the opened cell lent at `α`, at the row's table
  refine erwp_M_frameCRG (Φ := Θ.view c) (l := l) (A := α) (F := Fam) hFamD
    (tabN_unwind_lendOKCR hS _ δ Θ c α) (OpTabN.Twin.refl T)
    (fun m i en _ h _ ha => by rw [hab m i en h] at ha; cases ha)
    (Q := AFPost l β (famL β P Θ) Qin)
    k' j₀ hkj ls _ w₀ σ₀ W ρf X houtP houtf (Fam j₀) (fun _ _ h => h) hwit
    (ResU.CompS.comm hW) (ResU.CompS.comm hX) (fun BM hBM => ?_)
  -- step 6: the callback, at the lend's world and view, from the borrow
  rw [← hview]
  have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
  have hcell : vN₀ (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
      (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam j₀) hwit)) :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P' hkj houtP hwit,
      fun Θ'' j u r h => (hunif Θ'' j u r (by rw [← hAδ]; exact h)).mono hαβ⟩
  have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
    (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
  have h2 := h1 c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
  rw [cN_effOf₀, tabN_unwind_eq_add hS _ (.tensor (.mut a A) B) δ hfr l Fam c' c] at h2
  refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
  obtain ⟨β', hβ', hbB, hst⟩ := hb
  rw [interp_ext_self] at hβ'
  cases Option.some.inj hβ'
  refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
  -- step 7: the result back at `Θ`, the content in `F_o k`, the cell resealed
  obtain ⟨h', hw'⟩ := hoi k w σ hσ hFσ
  obtain ⟨ac, hac, hacZ⟩ := compS_exch hY hZ
  have hbB' : vN₀ (ℍ := ℍ) B δ Θ k b ρ' :=
    vN_local₀ B δ Θ l α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
  exact ⟨w, σ, h', hw', ρ', ac, ResU.CompS.comm hacZ, ResU.CompS.comm hac, fun X' hX' =>
    ⟨Val.loc l, b, _, ρ', rfl, ResU.CompS.comm hX', hRout k w σ h' hw', hbB'⟩⟩

/-- **`withbor3U` at `SemJN₀`** (Core's `withbor3U_compatX`), at an unwinding row and any `Δ`. -/
theorem withbor3U_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {S : Row}
    {d : Expr} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) (hdc : closedAt 0 d = true)
    (hd : SemJN₀ (ℍ := ℍ) Δ Γ d (.val (.lolli (.mut a A) .unit))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [show substAll γ (withborUE d) = withborUE d from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine erwp_val (v := withborUV d) (withbor3U_sem hδ hfree₁ hfree₂ hS hdc Θ n
    (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any₀ hΓ hg Θ' k hk)
  rwa [show substAll γ d = d from psub_closedAt d γ hdc (Nat.zero_le 0)] at h

/-! ### `withload` at an unwinding row -/

/-- **The unwinding callback at the image**: the callback, at `β ⊏ @bnd`, applied to the image
`χ` of the loaded payload, typed at `Imm̲ 'x A`, runs at the row's table with `[β]𝒱⟦B⟧` as its
post (`callback_at_image` at a `Row.Unwind` row, its table by `tabN_unwind_extend`). -/
theorem callback_at_imageU {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row}
    (hB : ¬ VFree x B) (hS : S.Unwind x) {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK)
    {c : Loc → Option Life} {n : Nat} {ls : List SRec} {f u : Val} {ρf χ Bχ : WRes} {β : Life}
    (hLt : LtLife δ bnd β)
    (hf : vN₀ (ℍ := ℍ) (cbUTy x bnd (A.immReborrow (.var x)) B S) δ Θ n f ρf)
    (hcf : ConsistentX c ρf) (hχ : ∀ m (ψ : CellU Loc Val), χ.get m = some ψ → ψ.kind = Kind.imm)
    (himg : vN₀ (ℍ := ℍ) (A.immReborrow (.var x)) (δ.extend x β) Θ n u χ)
    (hBχ : ResU.CompS ρf χ Bχ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf S B) δ Θ c))
      (RebPost β (fun k _ v ρ => vN₀ (ℍ := ℍ) B δ Θ k v ρ)) n ls
      (.app (.app (.val f) (.val .unit)) (.val u)) Bχ := by
  have h1 := (hf Θ (LocTy.extR_refl _ _) hΘ c hcf ls) β hLt
  have hcon : ConsistentX c Bχ := consistentX_compS hBχ hcf (consistentX_allImm hχ c)
  have h2 := h1 c n le_rfl u χ Bχ hBχ himg hcon
  rw [cN_effOf₀, tabN_unwind_extend hS (.box (.var x) B) B δ Θ β c] at h2
  refine erwp_mono (fun k _ w ρ hb => ?_) (opTableN_local _) n ls _ Bχ h2
  obtain ⟨α', hα', hbB, hst⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  rw [vN_extend_of_not_free₀ hB] at hbB
  exact ⟨hbB, hst⟩

/-- **`withload` at an unwinding row is a value of its type**: at
`Imm @a A ⊸ (∀'x ⊏ @Δ. Imm̲ 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ B` with `Σ` a `Row.Unwind x` row. Core's
`withloadU_compatX`, step by step, as `withloadS_compat`: the `Imm` argument is `loc ℓ`; the
load (`rwp_load_cell` under `erwp_bindR`); 6.150 at the run's first entry (`withload_rebT₀`),
across the row's raises (`erwp_rebGen`): the row's table admits the reborrow at every `β`
(`tabN_unwind_rebOKR`; an unrestricted operation of the row is abortive, so it never resumes) and
has no cancel obligation (`tabN_unwind_rebClosed`); the callback at the image
(`callback_at_imageU`), its result `['x] B` read at `B`. The source is consumed by the load, so
nothing goes back to the lender and there is no finaliser. -/
theorem withloadU_sem {Δ : LifeCtx} {a : Lifetime.Life} {x : LifeVar} {A B : VTy} {S : Row}
    {δ : LSub} (hδ : Δ.Models δ) (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Unwind x)
    (Θ₀ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (withloadUTy a x Δ.meetOfDom A B S) δ Θ₀ n withloadV PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨α₀, hα₀, ⟨l, s, w, σ, hσs, rfl, rfl, hα₀s, hpay⟩, hwit⟩ :=
    vN_le₀ hk' hu
  rw [cN_effOf₀]
  refine erwp_of_valid fun hv'' => ?_
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  have hTd := opTableN_down (tabN_down (ℍ := ℍ) (CTy.effOf S B) δ Θ hΘ.1 c)
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) B δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
  refine erwp_det hΦ hTd hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ hTd hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (.app (.app v0 unit') (.app load' v1)))) =
      (Kont.appR (.app (.val f) (.val .unit)) .hole).plug
        (.app (.val (.prim .load)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, Val.shift, Val.loc, Expr.val, Val.prim, v0, v1,
      unit', load', Val.unit]
  rw [e₃]
  -- the load
  refine erwp_bindR hΦ (opTableN_local _) _ ?_
  refine rwp_load_cell ls l s w σ hσs _ hc' ?_
  simp only [Kont.plug]
  -- 6.150 across the row's raises, the callback at the image
  exact withload_rebT₀ (Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries))
    hA (fun β _ => tabN_unwind_rebOKR hS B δ Θ c β)
    (fun β _ _ _ _ _ _ χ Ok _ _ _ => tabN_unwind_rebClosed hS B δ Θ c β _ χ Ok)
    (vO_le₀ (Nat.sub_le k' 1) hpay) (hwit l s w σ hσs rfl)
    (fun β hLt u χ Bχ hχ _ _ himg hBχ =>
      callback_at_imageU hB hS hΘ hLt (vN_le₀ (Nat.sub_le k' 1) hf) hcf hχ himg hBχ) hc'

/-- **`withloadU` at `SemJN₀`** (Core's `withloadU_compatX`), at an unwinding row and any `Δ`,
abortive unrestricted operations included. -/
theorem withloadU_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {S : Row}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) :
    SemJN₀ (ℍ := ℍ) Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ _ _ _ hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withload) _
  rw [show substAll γ withload = withload from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withloadV) (withloadU_sem hδ hfree₁ hfree₂ hS Θ n)

/-! ### An unwinding row with an unrestricted operation -/

/-- **An unwinding row whose one operation is unrestricted**: `raise : 1 ↠^unr 0`. Its table's
entry has `q = unr`, so the reborrow's table condition must leave abortive entries free. -/
def unrRaiseRow : Row := [{ n := 1, i := 0, q := .unr, A := .unit, B := .zero }]

theorem unrRaiseRow_unwind (x : LifeVar) : unrRaiseRow.Unwind x := by
  intro o ho
  simp only [unrRaiseRow, List.mem_singleton] at ho
  subst ho
  exact ⟨rfl, by decide, id, fun _ _ => .unit⟩

/-- **`withloadU` at the row with an unrestricted operation**, every hypothesis discharged. -/
theorem withloadU_unr_inst (Δ : LifeCtx) (a : Lifetime.Life) (x : LifeVar) :
    SemJN₀ (ℍ := ℍ) Δ [] withload
      (.val (withloadUTy a x Δ.meetOfDom .unit .unit unrRaiseRow)) :=
  withloadU_compatN x .nil id id (unrRaiseRow_unwind x)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
