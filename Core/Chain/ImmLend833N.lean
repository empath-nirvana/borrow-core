import Core.Chain.Withload791N
import Core.Chain.Map831N
import Core.Chain.SI.IStopRaiseN

/-!
# The `imm` lend at `SemJN₀`  `[spec §62]`

Core's `withbor1U_compatX` (`Core/EffBorrow.lean`) and `withbor1_compatX`
(`Core/Compatibility.lean`), step by step, at the per-lend world:

* the context owns nothing (`gN_deadP₀`) and the finaliser's judgment holds at every world and
  lower index (`gN_dead_any₀`, Core's `semV_dead_closed`);
* the lend's record goes into the callback's world (`LocTy.addImm`), an extension at the
  callback's resource in the lend's stratum (`LocTy.extR_addImm`, Core's `ext_add`); the
  callback's `Imm` argument is witnessed there by the record;
* the callback's run, at that world's view, is a run at the lender's view: an unwinding row's
  table never resumes, so the relation reads the tie only at the run's entry, whose list is the
  frame's and holds the record (`erwp_tieEntry`);
* the Imm Frame across the row's raises (`erwp_I_frameR`, Core's `ewpTS_I_frameU`);
* the callback's result `['x] B` returns to the world without the record (`LocTy.extR_of_addImm`,
  Core's `ext_drop`);
* the finaliser frame consumes the lend's claim at a raise (`erwp_ubindRaise`, `fin_claimI`).

The same steps give the `mut` lend `withbor (2)` at the pure row and at an unwinding row, at any
`Δ` (`withbor2_compatN₀`, `withbor2U_compatN`): the Mut Frame across raises (`erwp_M_frameR`), the
claim consistent with the view (`erwp_claimX_abort`).
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
open BoCa.BoLo (Heap Kont Head ubindE)

/-! ### A dead context -/

/-- **At a persistent type `𝒱⟦A⟧` holds only at `∅`** (Core's `vP_empty_of_persistent`). -/
theorem vN_empty_of_persistent₀ : ∀ (A : VTy), A.Persistent → ∀ {δ : LSub} {Θ : LocTy} {n : Nat}
    {v : Val} {ρ : WRes}, vN₀ (ℍ := ℍ) A δ Θ n v ρ → ρ = PMap.empty := by
  intro A hA δ Θ n v ρ h
  refine vN_ind₀ δ (fun _ T _ _ _ ρ => T.Persistent → ρ = PMap.empty) ?_ true A Θ n v ρ h hA
  intro b T Θ n v ρ h hp
  cases T with
  | unit => exact h.2
  | zero => exact h.elim
  | unk => exact h
  | int _ => exact h.2
  | bang _ => exact h.1
  | tvar _ => exact h.elim
  | opq _ => simp [VTy.Persistent, VTy.persistent] at hp
  | thunk _ => simp [VTy.Persistent, VTy.persistent] at hp
  | ref _ => simp [VTy.Persistent, VTy.persistent] at hp
  | imm _ _ => simp [VTy.Persistent, VTy.persistent] at hp
  | «mut» _ _ => simp [VTy.Persistent, VTy.persistent] at hp
  | fam _ => simp [VTy.Persistent, VTy.persistent] at hp
  | tensor A B =>
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      obtain ⟨v₁, v₂, ρ₁, ρ₂, -, hc, h₁, h₂⟩ := h
      rw [h₁.2 hp.1, h₂.2 hp.2] at hc
      exact eq_empty_of_compS_empty hc
  | sum A B =>
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      rcases h with ⟨v₁, -, h₁⟩ | ⟨v₂, -, h₂⟩
      · exact h₁.2 hp.1
      · exact h₂.2 hp.2
  | box _ A =>
      obtain ⟨α, -, hb, -⟩ := h
      exact hb.2 hp
  | mu A =>
      exact h.2.2.2 (by
        show (VTy.inst (.mu A) A).persistent = true
        rw [Inversions.persistent_inst_mu]; exact hp)

/-- **A consumed context, up to persistent slots, owns nothing** (Core's `gSepC_deadP`). -/
theorem gN_deadP₀ {δ : LSub} {Θ : LocTy} {n : Nat} : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ →
    ∀ {γ : List Val} {ρ : WRes}, gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; exact h
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h
      | cons v γ' => exact ih (γ := γ') (by simpa [gN₀] using h)
  | weaken hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h
      | cons v γ' =>
          simp only [gN₀, if_true] at h
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          rw [vN_empty_of_persistent₀ _ hT hv, ih hrest] at hc
          exact eq_empty_of_compS_empty hc

/-- **A consumed context's slots hold at every world and every lower index** (Core's
`semV_dead_closed`): its live slots are persistent, own nothing, and so are read at every
extension (`ExtR` at `∅` relates every two worlds) and lower index. -/
theorem gN_dead_any₀ {δ : LSub} {Θ : LocTy} {n : Nat} : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ →
    ∀ {γ : List Val} {ρ : WRes}, gN₀ (ℍ := ℍ) δ Θ Γ γ n ρ →
      ∀ (Θ' : LocTy) (k : Nat), k ≤ n → gN₀ (ℍ := ℍ) δ Θ' Γ γ k PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ _ Θ' k _; cases γ <;> rfl
  | cons _ ih =>
      intro γ ρ h Θ' k hk
      cases γ with
      | nil => rfl
      | cons v γ' =>
          simp only [gN₀] at h ⊢
          exact ih h Θ' k hk
  | weaken hT _ ih =>
      intro γ ρ h Θ' k hk
      cases γ with
      | nil => rfl
      | cons v γ' =>
          simp only [gN₀, if_true] at h ⊢
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          have h₁ := vN_empty_of_persistent₀ _ hT hv
          subst h₁
          have hE : Θ.ExtR Θ' PMap.empty :=
            ⟨fun _ _ _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e),
              fun _ _ hc => absurd hc (fun ⟨m, ψ, e, _⟩ => by simp at e)⟩
          exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
            vN_le₀ hk (vN_extR₀ _ δ n v _ hE hv), ih hrest Θ' k hk⟩

/-! ### A run whose table never resumes reads its tie only at its entry -/

/-- **The tie is read only at the entry**: a run at a location typing with more `imm` records,
the same families, from a list holding the extra records, is a run at the one with fewer. -/
theorem rwpG_tieEntry {Φ Φ' : LocFam} (hfam : Φ'.fam = Φ.fam) {ls : List SRec}
    (hI : ∀ x ∈ Φ'.imm, x ∈ Φ.imm ∨ x ∈ ls) {Q : PostG} {n : Nat} {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) Φ' Q n ls e ρ) : rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  obtain ⟨f', I'⟩ := Φ'
  obtain ⟨f, I⟩ := Φ
  simp only at hfam hI
  subst hfam
  intro ρf fρ ps μ hf hc hT htg hIt hl hfd j μ' e' hj hrun hfin
  have hIt' : ImmTieL I' ls := fun x hx => (hI x hx).elim (hIt x) id
  exact h ρf fρ ps μ hf hc hT htg hIt' hl hfd j μ' e' hj hrun hfin

/-- **A run at an abortive table reads its tie only at its entry**: the table never resumes, so
what the run owes at a stop does not mention the location typing. -/
theorem erwp_tieEntry {Φ Φ' : LocFam} (hfam : Φ'.fam = Φ.fam) {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (hI : ∀ x ∈ Φ'.imm, x ∈ Φ.imm ∨ x ∈ ls)
    (h : erwp (ℍ := ℍ) Φ' (opTableN T) Q n ls e ρ) : erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  rw [erwp_eq] at h ⊢
  refine rwpG_tieEntry hfam hI (rwpG_mono (fun k ls' t σ ht => ?_) h)
  rcases ht with ht | ⟨K, m, i, v, en, hp⟩ | ht
  · exact Or.inl ht
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (hab m i en hTe) (by rw [ha]; decide)
  · exact Or.inr (Or.inr ht)

/-! ### An unwinding row's table -/

/-- **An unwinding row's payload values lie in every stratum**: its payload types are free of
`'x` and outlive every lifetime (`Row.Unwind`), `'x` among them. -/
theorem vN_unwind_inStratum {S : Row} {x : LifeVar} (hS : S.Unwind x) {o : OpSig} (ho : o ∈ S)
    (δ : LSub) (α : Life) : ∀ (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
      vN₀ (ℍ := ℍ) o.A δ Θ n v ρ → ρ.InStratum α := by
  intro Θ n v ρ h
  rw [← vN_extend_of_not_free₀ (hS o ho).2.2.1 δ α] at h
  exact vN_outlives₀ (models_empty_any _) (interp_ext_self δ x α)
    ((hS o ho).2.2.2 LifeCtx.empty (.var x)) Θ n v ρ h

/-- An unwinding row's answer types are empty. -/
theorem unwind_B {S : Row} {x : LifeVar} (hS : S.Unwind x) {o : OpSig} (ho : o ∈ S) :
    o.B = .zero := OpSig.B_zero (hS o ho).1

/-- **Every entry of an unwinding row's table is abortive.** -/
theorem tabN_unwind_abort {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) :
    ∀ m i en, tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c m i = some en → en.abort = true := by
  intro m i en h
  obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
  exact (hS o ho).1

/-- **An unwinding row's table does not read `'x`, the record of a lend at `α`, nor its base.** -/
theorem tabN_unwind_eq {S : Row} {x : LifeVar} (hS : S.Unwind x) (R₁ R₂ : VTy) (δ : LSub)
    (Θ : LocTy) (r : FrameRec) (α : Life) (c : Loc → Option Life) :
    tabN₀ (ℍ := ℍ) (CTy.effOf S R₁) (δ.extend x α) (Θ.addImm (r, α)) c =
      tabN₀ (ℍ := ℍ) (CTy.effOf S R₂) δ Θ c := by
  induction S with
  | nil => rfl
  | cons o S ih =>
      have ho : o ∈ o :: S := List.mem_cons_self ..
      have hS' : Row.Unwind S x := fun o' ho' => hS o' (List.mem_cons_of_mem _ ho')
      have hA : vN₀ (ℍ := ℍ) o.A (δ.extend x α) (Θ.addImm (r, α)) = vN₀ (ℍ := ℍ) o.A δ Θ := by
        rw [vN_extend_of_not_free₀ (hS o ho).2.2.1 δ α]
        funext n v ρ
        have hρ := vN_unwind_inStratum hS ho δ α
        exact propext ⟨fun h => vN_extR₀ _ δ n v ρ
          (LocTy.extR_of_addImm Θ r (hρ _ n v ρ h)) h,
          fun h => vN_extR₀ _ δ n v ρ (LocTy.extR_addImm Θ r (hρ _ n v ρ h)) h⟩
      have hB := unwind_B hS ho
      simp only [CTy.effOf, tabN₀]
      rw [ih hS', hA, hB,
        entN_fin_congr (f := finN₀ (ℍ := ℍ) o.fin (δ.extend x α) (Θ.addImm (r, α)) c)
          (f' := finN₀ (ℍ := ℍ) o.fin δ Θ c) (fun hcap => by simp [capB, VTy.isZero] at hcap)]
      rfl

/-- **An unwinding row's table may be stopped at under an `imm` lend at any `α`**: its stops are
raises, whose payloads lie in every stratum. -/
theorem tabN_unwind_iLendOKR {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (α : Life) :
    (tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c).ILendOKR α where
  entry := fun m i en h ha => by
    rw [tabN_unwind_abort hS R δ Θ c m i en h] at ha; cases ha
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
    exact vN_unwind_inStratum hS ho δ α Θ k v ρ hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
    have hp' : vN₀ (ℍ := ℍ) o.B δ Θ k w ρ := hp.1
    rw [unwind_B hS ho] at hp'
    exact hp'.elim
  paExt := fun m i en h k ls₁ ls₂ v ρ _ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
    exact hp
  pbExt := fun m i en h k ls₁ ls₂ w ρ _ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
    exact hp

/-- An unwinding row's raises are at named operations. -/
theorem tabN_unwind_named {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) :
    ∀ m i en, tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c m i = some en → en.abort = true → m ≠ 0 := by
  intro m i en h _
  obtain ⟨o, ho, rfl, rfl⟩ := tabN_effOf_some h
  exact (hS o ho).2.1

/-! ### The finaliser at the lend's claim -/

/-- **The finaliser `λ_. d ℓ` consumes an `imm` lend's claim**: the cell owned again with the
content it was lent with, `d`'s judgment at `Ref A ⊸ 1` read at the world and an index below the
content's. -/
theorem fin_claimI {A : VTy} {d : Expr} (hdc : closedAt 0 d = true) {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.OK) {c : Loc → Option Life} {N : Nat}
    (hd : ∀ k, k ≤ N → ∀ ls, cN₀ (ℍ := ℍ) (.ret (.lolli (.ref A) .unit)) δ Θ c k ls d PMap.empty)
    {l : Loc} {w : Val} {σ : WRes} (hw : vN₀ (ℍ := ℍ) A δ Θ N w σ) {k : Nat} (hk : k ≤ N)
    {ls : List SRec} {ρ : WRes} (h : claimI l w σ k ρ) (hc : ConsistentX c ρ) :
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
    c k' le_rfl (Val.loc l) τ₂ τ hcτ
    ⟨l, w, σ, rfl, h, vN_le₀ (hk'.trans hk) hw⟩ hcτ'
  exact rwp_of_erwp_empty this

/-! ### `withbor (1)` at an unwinding row -/

/-- **`withbor (1)` at an unwinding row is a value of its type**: `withborU d` at
`Ref A ⊸ (∀'x ⊏ @Δ. Imm 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)`, `Σ` a `Row.Unwind x` row. Core's
`withbor1U_compatX`, step by step:

1. the source `ℓ ↦ own(w₀) ● σ₀`, the callback `f`, read at the run's world `Θ` (`vN_extR₀`);
2. `withborU d ℓ f` steps to the callback under the finaliser frame `then b. (ℓ, b) unwind d ℓ`;
3. the lend at a lifetime `α` below the bound, the content's stratum and the callback's
   (Core's `a₂ ⊓ m` at the Imm Frame's `⋔`), the record `p = (ℓ, w₀, σ₀, A, δ)`;
4. the callback's world `Θ + (p, α)`, an extension at the callback's resource
   (`LocTy.extR_addImm`, Core's `ext_add hadd hout₂`);
5. the borrow `ℓ ↦ imm({α}, w₀, σ₀)` a value of `Imm 'x A` at `δ['x ↦ α]` there: its payload
   observable at `A`, its witness the record;
6. the callback's run, at the world's view, is one at `Θ`'s (`erwp_tieEntry`), its table the
   lender's (`tabN_unwind_eq`);
7. the Imm Frame across the row's raises (`erwp_I_frameR`, Core's `ewpTS_I_frameU`), the
   callback's result `['x] B` back at `Θ` (`LocTy.extR_of_addImm`, Core's `ext_drop`);
8. the finaliser frame: at a return `(ℓ, b)`, at a raise `d ℓ` consumes the claim
   (`erwp_ubindRaise`, `fin_claimI`).

Premises: `hδ`, `hadm` (Core's `admWf_of_vScoped hsc₁ hδ`), `hfree₁`, `hfree₂`, `hS`, `hdc` are
the rule's; `hd` is the finaliser's judgment at the run's world and every lower index. -/
theorem withbor1U_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr} {δ : LSub}
    (hδ : Δ.Models δ) (hadm : AdmWf A δ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) (hdc : closedAt 0 d = true) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN₀ (ℍ := ℍ) (.ret (.lolli (.ref A) .unit)) δ Θ c k ls d PMap.empty) :
    vN₀ (ℍ := ℍ) (withbor1UTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  -- step 1
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := vN_le₀ hk' hu
  rw [cN_effOf₀]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.ref A) B) with hFo
  set T := tabN₀ (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
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
  -- the parts of the start are consistent with the view
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_right hcl (consistentX_left hc' hcon hv'') hvu
  -- step 3: the lend's lifetime and record
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨βP, hβP⟩ := ResU.exists_stratum σ₀
  set α : Life := ↓(βP ⊓ βf ⊓ γ) with hαdef
  have hαlt : α < βP ⊓ βf ⊓ γ := Life.down_sqsubset _
  have houtP : σ₀.InStratum α := hβP.mono (hαlt.le.trans (inf_le_left.trans inf_le_left))
  have houtb : ρf.InStratum α := hβf.mono (hαlt.le.trans (inf_le_left.trans inf_le_right))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  set p : FrameRec := ⟨l, w₀, σ₀, A, δ⟩ with hpdef
  -- the record's lineage
  have hvσ : ResU.Valid σ₀ := (ResU.Valid.split hcl hvu).2
  obtain ⟨-, eR, -, heR, -, -⟩ := hvσ
  obtain ⟨ds, hds⟩ := lineage_list (r := p) (vN_vShape₀ A δ Θ k' w₀ σ₀ hw₀) hadm heR
  -- step 4: the callback's world
  set Θ' := Θ.addImm (p, α) with hΘ'
  have hOK' : Θ'.OK := ⟨fun l' b F h => hΘ.1 l' b F h,
    let ⟨N, hN⟩ := hΘ.2; ⟨N, fun l' b h => hN l' b h⟩⟩
  set ρi : WRes := ResU.single l (CellU.immOf (LSet.singleton α) w₀ σ₀ houtP) with hρi
  set P : List SRec → Val → WProp := fun _ v ρ => vN₀ (ℍ := ℍ) A δ Θ k' v ρ with hP
  set Qb : PostN := fun k _ b ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k
    (Val.pair (Val.loc l) b) ρ with hQb
  -- steps 5–7: the Imm Frame
  have hI := erwp_I_frameR (Φ := Θ.view c) l A δ hadm w₀ P
    (fun _ ρ h => vN_vShape₀ A δ Θ k' w₀ ρ h) (fun _ _ _ _ h => h)
    (tabN_unwind_iLendOKR hS (.tensor (.ref A) B) δ Θ c α) (Q := Qb) (fun _ _ _ _ _ _ h => h)
    k' ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) σ₀ ρu ρf ρ'' houtP houtb hw₀
    hcl hc' ds hds (fun BI hBI => ?_)
  · -- step 8: the finaliser frame
    have hI' := erwp_mono_le (Tb' := opTableR T (fun j ρ => claimI l w₀ σ₀ j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [tabN_unwind_abort hS _ δ Θ c m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hI
    refine erwp_ubindRaise hΦ hTd
      (fun m i en h ha => by rw [tabN_unwind_abort hS _ δ Θ c m i en h] at ha; cases ha)
      (tabN_unwind_named hS _ δ Θ c)
      (fun m i en h k ls ls' v ρ _ hp => by
        obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
        exact hp)
      (NFv l) (DFv d l) (fun j ls' ρ hR => ?_) hQo (fun j ls' b ρ hq => ?_) k' ls _ ρ'' hI'
    · obtain ⟨hcl', hj⟩ := hR
      have hcρ : ConsistentX c ρ :=
        consistentX_compS hcl' (consistentX_of_top (ResU.inStratum_single_own _ l w₀) c) hcσ
      exact fin_claimI hdc hΘ (fun j hj ls => hd Θ hΘ c j (hj.trans (hk'.trans hk)) ls) hw₀ hj
        hcl' hcρ
    · refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.loc l) b) hq
  · -- step 5: the borrow at the callback's world
    have hvO : vO₀ (ℍ := ℍ) A δ' Θ' k' w₀ σ₀ := by
      rw [vO_extend_of_not_free₀ hfree₁]
      exact vO_extR₀ A δ k' w₀ σ₀ (LocTy.extR_addImm Θ p houtP) (vN_vO₀ A δ Θ k' w₀ σ₀ hw₀)
    have hcell : vN₀ (ℍ := ℍ) (.imm (.var x) A) δ' Θ' k' (Val.loc l) ρi := by
      refine ⟨α, interp_ext_self δ x α, ⟨l, LSet.singleton α, w₀, σ₀, houtP, rfl, rfl,
        le_refl _, hvO⟩, fun l₀ s₀ u₀ σ₁ h₀ e => ?_⟩
      obtain ⟨rfl, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨(p, α), List.mem_cons_self .., le_refl _, p, DescR.refl _, A, δ', TyEq.refl _ _,
        Or.inl ⟨p, List.mem_singleton_self _, rfl, rfl, fun y hy =>
          BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact hfree₁ hy)⟩⟩
    have hcBI : ConsistentX c BI := consistentX_compS hBI hcf
      (consistentX_allImm (fun m ψ e => by
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
        exact CellU.kind_immOf _ _ _ _) c)
    -- step 6: the callback's run
    have h1 := (hf Θ' (LocTy.extR_addImm Θ p houtb) hOK' c hcf
      (frameList p ds α ls)) α hLt
    have h2 := h1 c k' le_rfl (Val.loc l) ρi BI hBI hcell hcBI
    rw [cN_effOf₀, tabN_unwind_eq hS _ (.tensor (.ref A) B) δ Θ p α c] at h2
    have h3 := erwp_tieEntry (Φ := Θ.view c) (Φ' := Θ'.view c) rfl
      (tabN_unwind_abort hS _ δ Θ c) (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inr (List.mem_cons_self ..)
        · exact .inl hy) h2
    -- step 7: the result returns to the world without the record
    refine erwp_mono_le k' (fun j hj ls' b ρ' hb => ?_) (fun j _ ls' t Ψ Ψ' ρ hΨ h =>
      opTableN_local T j ls' t Ψ Ψ' ρ hΨ h) k' le_rfl _ _ BI h3
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨fun Y X hY hX σ Z hσ hZ => ?_, hst⟩
    subst hY
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w₀)) σ Z).mpr ⟨X, hX, hZ⟩
    have hbB' : vN₀ (ℍ := ℍ) B δ Θ j b ρ' := by
      rw [vN_extend_of_not_free₀ hfree₂] at hbB
      exact vN_extR₀ B δ j b ρ' (LocTy.extR_of_addImm Θ p hst) hbB
    exact ⟨Val.loc l, b, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w₀, σ, rfl, hWc, vN_le₀ hj hσ⟩,
      hbB'⟩

/-- **`withbor1U` at `SemJN₀`** (Core's `withbor1U_compatX`): the context owns nothing, the term
is the value `withborU d`, a value of its type at every `δ ⊨ Δ` (`withbor1U_sem`), the finaliser's
judgment read at the run's world and every lower index (`gN_dead_any₀`). -/
theorem withbor1U_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) (hdc : closedAt 0 d = true)
    (hd : SemJN₀ (ℍ := ℍ) Δ Γ d (.val (.lolli (.ref A) .unit))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [show substAll γ (withborUE d) = withborUE d from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine erwp_val (v := withborUV d) (withbor1U_sem hδ (admWf_of_vScoped hsc₁ hδ) hfree₁ hfree₂
    hS hdc Θ n (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any₀ hΓ hg Θ' k hk)
  rwa [show substAll γ d = d from psub_closedAt d γ hdc (Nat.zero_le 0)] at h

/-! ### `withbor (1)` at the pure row -/

/-- The pure row's table may be stopped at under any lend: it has no entry. -/
theorem empty_iLendOKR (α : Life) : OpTabN.empty.ILendOKR α where
  entry := fun _ _ _ h => by simp [OpTabN.empty] at h
  pa := fun _ _ _ h => by simp [OpTabN.empty] at h
  pb := fun _ _ _ h => by simp [OpTabN.empty] at h
  paExt := fun _ _ _ h => by simp [OpTabN.empty] at h
  pbExt := fun _ _ _ h => by simp [OpTabN.empty] at h

/-- `withbor`'s inner abstraction at the source `ℓ`: `λf. (ℓ, f () ℓ)`. -/
def withborAt (l : Loc) : Val :=
  Val.lam (.pair (.val (Val.loc l)) (.app (.app BoCa.v0 unit') (.val (Val.loc l))))

/-- `withbor` as a value. -/
def withborVal : Val := Val.lam (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1

theorem withborVal_eq : withborVal.1 = withbor := rfl

/-- **`withbor (1)` is a value of its type**: `withbor` at
`Ref A ⊸ (∀'x ⊏ @Δ. Imm 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. Core's `withbor1_compatX`, step by step,
at the pure row: the source read at the callback's world, the lend at a lifetime below the bound,
the content's stratum and the callback's, its record in the callback's world (Core's
`ext_add hadd hout₂`), the borrow a value of `Imm 'x A` there; `f ()` and the borrow's application
under the pair (Core's `wpTS_bind (.pairR ℓ □)`), framed beside the borrow; the result `['x] B`
back at the world without the record (`ext_drop`); the Imm Frame (`erwp_I_frameR`). -/
theorem withbor1_sem₀ {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hadm : AdmWf A δ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (Θ₀ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (axWithbor1Ty x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
  intro Θ₂ _ _ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := hu
  have hΦ₂ : (Θ₂.view c₂).Down := LocTy.view_down (by assumption : Θ₂.OK).1 c₂
  have hQ₂ : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ)
      (.lolli (.all x Δ.meetOfDom (.lolli (.imm (.var x) A) (.box (.var x) B)))
        (.tensor (.ref A) B)) δ Θ₂ k v ρ) := fun k _ v ρ h => vN_down₀ _ δ Θ₂ k v ρ h
  refine erwp_det hΦ₂ (opTableN_down OpTabN.empty_down) hQ₂
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) = (withborAt l).1 := by
    simp [Kont.plug, Expr.subst, Expr.shift, withborAt, BoCa.v0, BoCa.v1, unit', Val.loc,
      Val.lam, Expr.val, Val.unit]
  rw [e₁]
  refine erwp_val (v := withborAt l) ?_
  intro Θ' hE₃ hΘ' c _ ls' c' k' hk' f ρf ρ'' hc' hf hcon
  -- the source at the callback's world
  obtain ⟨l₁, w₀', σ₀', hl₁, hcl', hw₀'⟩ := vN_le₀ hk'
    (vN_extR₀ (.ref A) δ k _ ρu hE₃ ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩)
  obtain rfl : l = l₁ := by
    have := congrArg Subtype.val hl₁; simpa [Val.loc] using this
  have hΦ : (Θ'.view c').Down := LocTy.view_down hΘ'.1 c'
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.loc l)) (.app (.app BoCa.v0 unit') (.val (Val.loc l))))) =
      (Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Val.loc, Expr.val, Val.unit]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c' ρf := consistentX_right hc' hcon hv''
  -- the lend's lifetime and record
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨βP, hβP⟩ := ResU.exists_stratum σ₀'
  set α : Life := ↓(βP ⊓ βf ⊓ γ) with hαdef
  have hαlt : α < βP ⊓ βf ⊓ γ := Life.down_sqsubset _
  have houtP : σ₀'.InStratum α := hβP.mono (hαlt.le.trans (inf_le_left.trans inf_le_left))
  have houtb : ρf.InStratum α := hβf.mono (hαlt.le.trans (inf_le_left.trans inf_le_right))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  set p : FrameRec := ⟨l, w₀', σ₀', A, δ⟩ with hpdef
  have hvσ : ResU.Valid σ₀' := (ResU.Valid.split hcl' hvu).2
  obtain ⟨-, eR, -, heR, -, -⟩ := hvσ
  obtain ⟨ds, hds⟩ := lineage_list (r := p) (vN_vShape₀ A δ Θ' k' w₀' σ₀' hw₀') hadm heR
  set Θ'' := Θ'.addImm (p, α) with hΘ''
  have hOK'' : Θ''.OK := ⟨fun l' b F h => hΘ'.1 l' b F h,
    let ⟨N, hN⟩ := hΘ'.2; ⟨N, fun l' b h => hN l' b h⟩⟩
  have hΦi : (Θ''.view c').Down := LocTy.view_down hOK''.1 c'
  set ρi : WRes := ResU.single l (CellU.immOf (LSet.singleton α) w₀' σ₀' houtP) with hρi
  set P : List SRec → Val → WProp := fun _ v ρ => vN₀ (ℍ := ℍ) A δ Θ' k' v ρ with hP
  set Q : PostN := fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ with hQ
  have hIF := erwp_I_frameR (Φ := Θ'.view c') l A δ hadm w₀' P
    (fun _ ρ h => vN_vShape₀ A δ Θ' k' w₀' ρ h) (fun _ _ _ _ h => h)
    (Tb := OpTabN.empty) (empty_iLendOKR α)
    (Q := Q) (fun _ _ _ _ _ _ h => h) k' ls'
    ((Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug (.app (.val f) (.val Val.unit)))
    σ₀' ρu ρf ρ'' houtP houtb hw₀' hcl' hc' ds hds
    (fun BI hBI => ?_)
  · refine erwp_mono (fun _ _ _ _ h => h) (fun j ls₁ t Ψ Ψ' ρ hΨ h => ?_) k' ls' _ ρ'' hIF
    rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
  · -- the borrow at the callback's world
    have hvO : vO₀ (ℍ := ℍ) A δ' Θ'' k' w₀' σ₀' := by
      rw [vO_extend_of_not_free₀ hfree₁]
      exact vO_extR₀ A δ k' w₀' σ₀' (LocTy.extR_addImm Θ' p houtP) (vN_vO₀ A δ Θ' k' w₀' σ₀' hw₀')
    have hcell : vN₀ (ℍ := ℍ) (.imm (.var x) A) δ' Θ'' k' (Val.loc l) ρi := by
      refine ⟨α, interp_ext_self δ x α, ⟨l, LSet.singleton α, w₀', σ₀', houtP, rfl, rfl,
        le_refl _, hvO⟩, fun l₀ s₀ u₀ σ₁ h₀ e => ?_⟩
      obtain ⟨rfl, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨(p, α), List.mem_cons_self .., le_refl _, p, DescR.refl _, A, δ', TyEq.refl _ _,
        Or.inl ⟨p, List.mem_singleton_self _, rfl, rfl, fun y hy =>
          BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact hfree₁ hy)⟩⟩
    have hci : ConsistentX c' ρi := consistentX_allImm (fun m ψ e => by
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      exact CellU.kind_immOf _ _ _ _) c'
    -- the run, at the callback's world, read at the lender's view
    refine erwp_tieEntry (Φ := Θ'.view c') (Φ' := Θ''.view c') (T := OpTabN.empty) rfl
      (fun _ _ _ h => by simp [OpTabN.empty] at h)
      (fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hy
        · exact .inr (List.mem_cons_self ..)
        · exact .inl hy) (erwp_of_rwp ?_)
    refine rwp_bind hΦi _ ?_
    -- `f ()`, beside the borrow
    have hcb := (hf Θ'' (LocTy.extR_addImm Θ' p houtb) hOK'' c' hcf (frameList p ds α ls')) α hLt
    have hfr := rwp_frame (fun _ τ => τ = ρi) (fun _ _ _ _ h => h) hBI (rwp_of_erwp_empty hcb) rfl
    refine rwp_mono_le (fun j hj ls₂ g τ hg => ?_) (rwp_consistentXV hfr
      (consistentX_compS hBI hcf hci))
    obtain ⟨⟨τg, τi, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
    -- the borrow's application
    have happ := hgv Θ'' (LocTy.extR_refl _ _) hOK'' c' (consistentX_left hcτ hcτ' hvτ) ls₂
      c' j le_rfl (Val.loc l) ρi τ hcτ (vN_le₀ hj hcell) hcτ'
    show rwp (ℍ := ℍ) _ _ j ls₂ ((Kont.pairR (Val.loc l) Kont.hole).plug
      (.app (.val g) (.val (Val.loc l)))) τ
    refine rwp_bind hΦi _ ?_
    refine rwp_mono_le (fun j' hj' ls₃ b ρb hb => ?_) (rwp_of_erwp_empty happ)
    -- the pair, and the result back at the world without the record
    refine rwp_val (v := Val.pair (Val.loc l) b) ?_
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨fun Y X hY hX σ Z hσ hZ => ?_, hst⟩
    subst hY
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρb (ResU.single l (CellU.ownOf w₀')) σ Z).mpr ⟨X, hX, hZ⟩
    have hbB' : vN₀ (ℍ := ℍ) B δ Θ' j' b ρb := by
      rw [vN_extend_of_not_free₀ hfree₂] at hbB
      exact vN_extR₀ B δ j' b ρb (LocTy.extR_of_addImm Θ' p hst) hbB
    exact ⟨Val.loc l, b, Wc, ρb, rfl, ResU.CompS.comm hZ',
      ⟨l, w₀', σ, rfl, hWc, vN_le₀ (hj'.trans (hj.trans le_rfl)) hσ⟩, hbB'⟩

/-- **`withbor1` at `SemJN₀`** (Core's `withbor1_compatX`). -/
theorem withbor1_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemJN₀ (ℍ := ℍ) Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal) (withbor1_sem₀ hδ (admWf_of_vScoped hsc₁ hδ) hfree₁ hfree₂ Θ n)

/-! ### `withbor (2)` at an unwinding row -/

/-- **An answer at `0` is at no view**: a table's answers at `0` read alike at every view. -/
theorem ansN_zero (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    (fun k v ρ => vN₀ (ℍ := ℍ) .zero δ Θ k v ρ ∧ ConsistentX c ρ) = fun _ _ _ => False := by
  funext k v ρ
  exact propext ⟨fun h => h.1, False.elim⟩

/-- **An unwinding row's table does not read `'x`, a `mut` lend at a fresh `α`, the view, nor its
base.** -/
theorem tabN_unwind_eq_add {S : Row} {x : LifeVar} (hS : S.Unwind x) (R₁ R₂ : VTy) (δ : LSub)
    {Θ : LocTy} {α : Life} (hfr : Θ.Fresh α) (l : Loc) (F : Nat → Val → SPropS Loc Val α)
    (c₁ c₂ : Loc → Option Life) :
    tabN₀ (ℍ := ℍ) (CTy.effOf S R₁) (δ.extend x α) (Θ.add l α F) c₁ =
      tabN₀ (ℍ := ℍ) (CTy.effOf S R₂) δ Θ c₂ := by
  induction S with
  | nil => rfl
  | cons o S ih =>
      have ho : o ∈ o :: S := List.mem_cons_self ..
      have hS' : Row.Unwind S x := fun o' ho' => hS o' (List.mem_cons_of_mem _ ho')
      have hA : vN₀ (ℍ := ℍ) o.A (δ.extend x α) (Θ.add l α F) = vN₀ (ℍ := ℍ) o.A δ Θ := by
        rw [vN_extend_of_not_free₀ (hS o ho).2.2.1 δ α]
        funext n v ρ
        have hρ := vN_unwind_inStratum hS ho δ α
        exact propext ⟨fun h => vN_local₀ _ δ Θ l α F n v ρ (hρ _ n v ρ h) h,
          fun h => vN_extA₀ _ δ (LocTy.extA_add hfr l F) n v ρ h⟩
      have hB := unwind_B hS ho
      simp only [CTy.effOf, tabN₀]
      rw [ih hS', hA, hB,
        entN_fin_congr (f := finN₀ (ℍ := ℍ) o.fin (δ.extend x α) (Θ.add l α F) c₁)
          (f' := finN₀ (ℍ := ℍ) o.fin δ Θ c₂) (fun hcap => by simp [capB, VTy.isZero] at hcap),
        ansN_zero, ansN_zero]

/-- **An unwinding row's table may be stopped at under a `mut` lend at any `α`**: its stops are
raises, whose payloads lie in every stratum. -/
theorem tabN_unwind_lendOKR {S : Row} {x : LifeVar} (hS : S.Unwind x) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (α : Life) :
    (tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c).LendOKR α where
  entry := fun m i en h ha => by
    rw [tabN_unwind_abort hS R δ Θ c m i en h] at ha; cases ha
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
    exact vN_unwind_inStratum hS ho δ α Θ k v ρ hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
    have hp' : vN₀ (ℍ := ℍ) o.B δ Θ k w ρ := hp.1
    rw [unwind_B hS ho] at hp'
    exact hp'.elim

/-- **A body at an abortive table carries the view's consistency to its claim** (`erwp_claimX`'s
`raise` case): a run from a resource consistent with `c` returns consistent resources, and the
claim a `raise` carries is part of one. -/
theorem erwp_claimX_abort {Θ : LocTy} {c : Loc → Option Life} {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {R : Nat → WProp} {Q : PostN} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hc : ConsistentX c ρ)
    (h : erwp (ℍ := ℍ) (Θ.view c) (opTableR T R) Q n ls e ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableR T (claimX R c)) Q n ls e ρ := by
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with hv | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact Or.inl hv
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [hab m i en hTe]; decide)
  · obtain ⟨hpt, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    exact Or.inr (Or.inr ⟨K₁, m, i, v, en, pure_sep_mk hpt
      ⟨σ₁, ρR, hcσR, hpa, hR, consistentX_right hcσR hcσ hvσ⟩⟩)

/-- **`withbor (2)` at an unwinding row is a value of its type**: `withborU d` at
`Ref A ⊸ (∀'x ⊏ @Δ. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)`, `Σ` a `Row.Unwind x` row. Core's
`withbor2U_compatX`, step by step, as `withbor2S_compat₀` with the bound `Δ.meetOfDom` defined at
`δ ⊨ Δ` and the row's table abortive: the lend at a lifetime fresh for the world, below the bound,
`[TR]` 6.60's stratum at the side condition `Δ ⊢ A ⊒ @b` and the callback's; the callback at the
world with the lend (`LocTy.view_add`); the Mut Frame across the row's raises (`erwp_M_frameR`,
Core's `ewpTS_M_frameU`); the claim consistent with the view (`erwp_claimX_abort`); the finaliser
frame at a raise (`erwp_ubindRaise`, `fin_claimI` at the claim's content). -/
theorem withbor2U_sem {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {S : Row} {d : Expr} {δ : LSub}
    (hδ : Δ.Models δ) (hO : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hA : ¬ VFree x A)
    (hB : ¬ VFree x B) (hS : S.Unwind x) (hdc : closedAt 0 d = true) (Θ₀ : LocTy) (n : Nat)
    (hd : ∀ (Θ : LocTy), Θ.OK → ∀ c k, k ≤ n → ∀ ls,
      cN₀ (ℍ := ℍ) (.ret (.lolli (.ref A) .unit)) δ Θ c k ls d PMap.empty) :
    vN₀ (ℍ := ℍ) (withbor2UTy x Δ.meetOfDom A B S) δ Θ₀ n (withborUV d) PMap.empty := by
  intro Θ _ hΘ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := vN_le₀ hk' hu
  rw [cN_effOf₀]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.ref A) B) with hFo
  set T := tabN₀ (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
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
  have hunif : ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN₀ (ℍ := ℍ) A δ Θ' j u r →
      r.InStratum α :=
    vN_outlivesLe₀ hδ hβP hαP hOb
  have houtP : σ₀.InStratum α := hunif Θ k' w₀ σ₀ hw₀
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN₀ (ℍ := ℍ) A δ' = vN₀ (ℍ := ℍ) A δ := vN_extend_of_not_free₀ hA δ α
  have hBδ : vN₀ (ℍ := ℍ) B δ' = vN₀ (ℍ := ℍ) B δ := vN_extend_of_not_free₀ hB δ α
  set P : CPredL := fun Θ' j u r => vN₀ (ℍ := ℍ) A δ' Θ' j u r with hP
  set Fam : Nat → Val → SPropS Loc Val α := famL α P Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down₀ A δ' α Θ
  have hwit : Fam k' w₀ ⟨σ₀, houtP⟩ := (vN_above₀ A δ' Θ houtP).mpr (by rw [hAδ]; exact hw₀)
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
  set Qb : PostN := fun k _ b ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k
    (Val.pair (Val.loc l) b) ρ with hQb
  have hM := erwp_M_frameR (Φ := Θ.view c) (l := l) (A := α) (F := Fam) hFamD
    (tabN_unwind_lendOKR hS (.tensor (.ref A) B) δ Θ c α) (Q := Qb)
    k' k' le_rfl ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ ρu ρf ρ''
    houtP houtf (Fam k') (fun _ _ h => h) hwit hcl hc' (fun BM hBM => ?_)
  · -- the claim with the view's consistency, then the finaliser frame
    have hM' := erwp_claimX_abort (tabN_unwind_abort hS _ δ Θ c) hcon hM
    have hM'' := erwp_mono_le
      (Tb' := opTableR T (fun j ρ => claimX (claimR l α Fam) c j ρ ∧ j ≤ k')) k'
      (fun _ _ _ _ _ h => h) (fun j hj ls' t Ψ Ψ' ρ hΨ h => by
        rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
        · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp h
          exact absurd ha (by rw [tabN_unwind_abort hS _ δ Θ c m i en hTe]; decide)
        · obtain ⟨hp, τ, τR, hcτ, h₁, hR⟩ := pure_sep_iff.mp h
          exact Or.inr ⟨K, m, i, v, en, pure_sep_mk hp ⟨τ, τR, hcτ, h₁, hR, hj⟩⟩)
      k' le_rfl ls _ ρ'' hM'
    refine erwp_ubindRaise hΦ hTd
      (fun m i en h ha => by rw [tabN_unwind_abort hS _ δ Θ c m i en h] at ha; cases ha)
      (tabN_unwind_named hS _ δ Θ c)
      (fun m i en h k ls ls' v ρ _ hp => by
        obtain ⟨o, ho, -, rfl⟩ := tabN_effOf_some h
        exact hp)
      (NFv l) (DFv d l) (fun j ls' ρ hR => ?_) hQo (fun j ls' b ρ hq => ?_) k' ls _ ρ'' hM''
    · obtain ⟨⟨⟨w, σ, hσ, hF, hclm⟩, hcR⟩, hj⟩ := hR
      have hwσ : vN₀ (ℍ := ℍ) A δ Θ j w σ := by rw [← hAδ]; exact (vN_above₀ A δ' Θ hσ).mp hF
      exact fin_claimI hdc hΘ (fun j' hj' ls => hd Θ hΘ c j' (hj'.trans (hj.trans (hk'.trans hk))) ls)
        hwσ le_rfl hclm hcR
    · refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      exact erwp_val (v := Val.pair (Val.loc l) b) hq
  · -- the callback, at the lend's world and view, from the borrow
    rw [← hview]
    have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
    have hcell : vN₀ (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam k') hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P le_rfl houtP hwit,
        fun Θ'' j u r h => hunif Θ'' j u r (by rw [← hAδ]; exact h)⟩
    have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
      (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
    have h2 := h1 c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
    rw [cN_effOf₀, tabN_unwind_eq_add hS _ (.tensor (.ref A) B) δ hfr l Fam c' c] at h2
    refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN₀ (ℍ := ℍ) A δ Θ k w σ := by
      rw [← hAδ]; exact (vN_above₀ A δ' Θ hσ).mp hFσ
    have hbB' : vN₀ (ℍ := ℍ) B δ Θ k b ρ' :=
      vN_local₀ B δ Θ l α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
    exact ⟨Val.loc l, b, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩

/-- **`withbor2U` at `SemJN₀`** (Core's `withbor2U_compatX`), at an unwinding row and any `Δ`. -/
theorem withbor2U_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x) (hdc : closedAt 0 d = true)
    (hd : SemJN₀ (ℍ := ℍ) Δ Γ d (.val (.lolli (.ref A) .unit))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (withborUE d)) _
  rw [show substAll γ (withborUE d) = withborUE d from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine erwp_val (v := withborUV d) (withbor2U_sem hδ hside hfree₁ hfree₂ hS hdc Θ n
    (fun Θ' hΘ' c' k hk ls' => ?_))
  have h := hd δ γ Θ' c' k ls' PMap.empty hδ hΘ' (consistentX_empty c') hlw
    (gN_dead_any₀ hΓ hg Θ' k hk)
  rwa [show substAll γ d = d from psub_closedAt d γ hdc (Nat.zero_le 0)] at h

/-! ### `withbor (2)` at the pure row -/

/-- **`withbor (2)` is a value of its type**: `withbor` at
`Ref A ⊸ (∀'x ⊏ @Δ. Mut 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. Core's `withbor2_compatX`, step by step, at
the pure row: the source read at the callback's world; the lend at a lifetime fresh for the world,
below the bound, `[TR]` 6.60's stratum at the side condition and the callback's; the callback's
world `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧`; `f ()` and the borrow's application under the pair, framed beside
the borrow; the result `['x] B` back at the world without the lend (`vN_local₀`); the Mut Frame
(`erwp_M_frameR`, Core's `wpTS_M_frameX`). -/
theorem withbor2_sem₀ {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hO : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (Θ₀ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (axWithbor2Ty x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
  intro Θ₂ _ _ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := hu
  have hΦ₂ : (Θ₂.view c₂).Down := LocTy.view_down (by assumption : Θ₂.OK).1 c₂
  have hQ₂ : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ)
      (.lolli (.all x Δ.meetOfDom (.lolli (.mut (.var x) A) (.box (.var x) B)))
        (.tensor (.ref A) B)) δ Θ₂ k v ρ) := fun k _ v ρ h => vN_down₀ _ δ Θ₂ k v ρ h
  refine erwp_det hΦ₂ (opTableN_down OpTabN.empty_down) hQ₂
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) = (withborAt l).1 := by
    simp [Kont.plug, Expr.subst, Expr.shift, withborAt, BoCa.v0, BoCa.v1, unit', Val.loc,
      Val.lam, Expr.val, Val.unit]
  rw [e₁]
  refine erwp_val (v := withborAt l) ?_
  intro Θ' hE₃ hΘ' c _ ls' c' k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l₁, w₀', σ₀', hl₁, hcl', hw₀'⟩ := vN_le₀ hk'
    (vN_extR₀ (.ref A) δ k _ ρu hE₃ ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩)
  obtain rfl : l = l₁ := by
    have := congrArg Subtype.val hl₁; simpa [Val.loc] using this
  have hΦ : (Θ'.view c').Down := LocTy.view_down hΘ'.1 c'
  have hQo : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQo
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.loc l)) (.app (.app BoCa.v0 unit') (.val (Val.loc l))))) =
      (Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Val.loc, Expr.val, Val.unit]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c' ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c' σ₀' := consistentX_right hcl' (consistentX_left hc' hcon hv'') hvu
  have hko : (CellU.ownOf (Loc := Loc) w₀').kind ≠ Kind.imm := by simp
  have hown : ρu.get l = some (CellU.ownOf w₀') :=
    (ResU.CompS.get_left_of_ne_imm hcl' (ResU.single_get_self _ _) hko).2
  -- the lend's lifetime
  obtain ⟨γ, hγ⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨b, hdef, hOb⟩ := hO
  obtain ⟨βP, hβP⟩ : ∃ β : Life, b.interp δ = some β := hdef δ hδ
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ'.2 (↓(βP ⊓ βf ⊓ γ))
  have hαlt : α < βP ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαP : α < βP := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hunif : ∀ (Θ'' : LocTy) (j : Nat) (u : Val) (r : WRes), vN₀ (ℍ := ℍ) A δ Θ'' j u r →
      r.InStratum α :=
    vN_outlivesLe₀ hδ hβP hαP hOb
  have houtP : σ₀'.InStratum α := hunif Θ' k' w₀' σ₀' hw₀'
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ Δ.meetOfDom α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN₀ (ℍ := ℍ) A δ' = vN₀ (ℍ := ℍ) A δ := vN_extend_of_not_free₀ hA δ α
  have hBδ : vN₀ (ℍ := ℍ) B δ' = vN₀ (ℍ := ℍ) B δ := vN_extend_of_not_free₀ hB δ α
  set P : CPredL := fun Θ'' j u r => vN₀ (ℍ := ℍ) A δ' Θ'' j u r with hP
  set Fam : Nat → Val → SPropS Loc Val α := famL α P Θ' with hFam
  have hFamD : DownFam α Fam := vN_fam_down₀ A δ' α Θ'
  have hwit : Fam k' w₀' ⟨σ₀', houtP⟩ := (vN_above₀ A δ' Θ' houtP).mpr (by rw [hAδ]; exact hw₀')
  set Θ'' := Θ'.add l α Fam with hΘ''
  set c'' := setLife c' l α with hc''def
  have hOK'' : Θ''.OK := by
    obtain ⟨N, hN⟩ := hΘ'.2
    exact ⟨LocTy.down_add hΘ'.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ''.view c'' = (Θ'.view c').set l α Fam := LocTy.view_add Θ' c' l α Fam
  have hcf'' : ConsistentX c'' ρf :=
    consistentX_setLife hcf (exS_none_of_part hc' hv'' hown hko) α
  have hcσ' : ConsistentX c'' σ₀' :=
    consistentX_setLife hcσ (exS_none_of_part hcl' hvu (ResU.single_get_self _ _) hko) α
  set Q : PostN := fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.ref A) B) δ Θ' k v ρ with hQ
  have hMF := erwp_M_frameR (Φ := Θ'.view c') (l := l) (A := α) (F := Fam) hFamD
    (T := OpTabN.empty) ⟨fun _ _ _ h => by simp [OpTabN.empty] at h,
      fun _ _ _ h => by simp [OpTabN.empty] at h, fun _ _ _ h => by simp [OpTabN.empty] at h⟩
    (Q := Q) k' k' le_rfl ls'
    ((Kont.pairR (Val.loc l) (Kont.appL Kont.hole (Val.loc l))).plug (.app (.val f) (.val Val.unit)))
    w₀' σ₀' ρu ρf ρ'' houtP houtf (Fam k') (fun _ _ h => h) hwit hcl' hc' (fun BM hBM => ?_)
  · refine erwp_mono (fun _ _ _ _ h => h) (fun j ls₁ t Ψ Ψ' ρ hΨ h => ?_) k' ls' _ ρ'' hMF
    rcases h with ⟨K, m, i, v, en, h⟩ | ⟨K, m, i, v, en, h⟩
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
    · obtain ⟨⟨-, -, hTe, -⟩, -⟩ := pure_sep_iff.mp h; simp [OpTabN.empty] at hTe
  · -- the callback, at the lend's world and view, from the borrow
    rw [← hview]
    have hΦi : (Θ''.view c'').Down := LocTy.view_down hOK''.1 c''
    have hcell : vN₀ (ℍ := ℍ) (.mut (.var x) A) δ' Θ'' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀' σ₀' houtP (Fam k') hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ' l α P le_rfl houtP hwit,
        fun Θ₃ j u r h => hunif Θ₃ j u r (by rw [← hAδ]; exact h)⟩
    have hcm : ConsistentX c'' (ResU.single l (CellU.mutOf α w₀' σ₀' houtP (Fam k') hwit)) :=
      consistentX_single_mut hcσ' (by simp [hc''def, setLife])
    refine erwp_of_rwp (rwp_bind hΦi _ ?_)
    have hcb := (hf Θ'' ((LocTy.extA_add hfr l Fam).extR ρf) hOK'' c'' hcf'' ls') α hLt
    have hfr' := rwp_frame (fun _ τ => τ = ResU.single l (CellU.mutOf α w₀' σ₀' houtP (Fam k') hwit))
      (fun _ _ _ _ h => h) hBM (rwp_of_erwp_empty hcb) rfl
    refine rwp_mono_le (fun j hj ls₂ g τ hg => ?_) (rwp_consistentXV hfr'
      (consistentX_compS hBM hcf'' hcm))
    obtain ⟨⟨τg, τm, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
    have happ := hgv Θ'' (LocTy.extR_refl _ _) hOK'' c'' (consistentX_left hcτ hcτ' hvτ) ls₂
      c'' j le_rfl (Val.loc l) _ τ hcτ (vN_le₀ hj hcell) hcτ'
    show rwp (ℍ := ℍ) _ _ j ls₂ ((Kont.pairR (Val.loc l) Kont.hole).plug
      (.app (.val g) (.val (Val.loc l)))) τ
    refine rwp_bind hΦi _ ?_
    refine rwp_mono_le (fun j' hj' ls₃ b ρb hb => ?_) (rwp_of_erwp_empty happ)
    refine rwp_val (v := Val.pair (Val.loc l) b) ?_
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρb (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN₀ (ℍ := ℍ) A δ Θ' j' w σ := by
      rw [← hAδ]; exact (vN_above₀ A δ' Θ' hσ).mp hFσ
    have hbB' : vN₀ (ℍ := ℍ) B δ Θ' j' b ρb :=
      vN_local₀ B δ Θ' l α Fam j' b ρb hst (by rw [← hBδ]; exact hbB)
    exact ⟨Val.loc l, b, Wc, ρb, rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩

/-- **`withbor2` at `SemJN₀`** (Core's `withbor2_compatX`). -/
theorem withbor2_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) :
    SemJN₀ (ℍ := ℍ) Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal) (withbor2_sem₀ hδ hside hfree₁ hfree₂ Θ n)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
