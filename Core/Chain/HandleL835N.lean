import Core.Chain.HandleT835N

/-!
# `[handle-last]`: a clause that uses `κ` once, last  `[spec §14, §19, §27, §51]`

Core's `handleL_compatC` (`Core/DivHandleLast.lean`) at `SemJN₀`, its proof `ewp_handle_last` at
`erwp` (the last instance, `scope-831-interface.md` §10.5), each step Core's:

* `worksTy_atN₀`, `exitsTy_atN₀` (Core's `worksTy_at`, `exitsTy_at`): the works and the exits read
  at `vN₀`;
* `last_contN₀` (Core's `last_cont`): the finaliser frame's answer: `inl y` resumes `κ` at `y`,
  `inr z` cancels `κ` at the table of its cancel row under the exit's frame
  (`erwp_frame_plain_or`), then runs the exit at `z`;
* `erwp_handle_last₀` (Core's `ewp_handle_last`): `erwp_handle_le` with a clause running its work
  at its row under the finaliser frame (`erwp_frame_then`, its frame `κ`'s relation at the record
  list), `κ.2 ()` the finaliser; the clause pays its `β` step, so the work's run, the finaliser and
  the frame's answer are all below the stop's index, where `κ` is owed;
* `handleL_compatN₀` (Core's `handleL_compatC`).

As at `[handle]` with tail clauses (`Core/Chain/HandleT835N.lean`), the works and the exits are read
at the view from consistent resources: the payload at the handler's name (`erwp_consistentPA`), the
work's value across its resumptions (`erwp_consistentAns`), and the exit's argument, a part of
that value. `κ`'s cancel branch gets the table of the operation's own cancel row (Core's `lastTc`),
the entry's cancel obligation itself (`OpTabN.Sub`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal clauseAt capTag)

/-! ### The works and the exits -/

/-- **The works at `vN₀`** (Core's `worksTy_at`): a tuple of the works' type holds, at each
operation, the function `pickE j` steps to, at the empty resource. -/
theorem worksTy_atN₀ {S SW : Row} {R : VTy} {Xs : Nat → VTy} {δ : LSub} {Θ : LocTy} {k : Nat} :
    ∀ (E : List (Qual × VTy × VTy)) (j₀ : Nat) {vc : Val} {ρ : WRes},
      vN₀ (ℍ := ℍ) (worksTy S SW R Xs E j₀) δ Θ k vc ρ →
      ∀ j (h : j < E.length), ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vN₀ (ℍ := ℍ) (workTy S SW R (Xs (j₀ + j)) E[j]) δ Θ k g PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, j₀, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, ρ₁, ρ₂, rfl, -, hg, hr⟩ := h
      have he : ρ₁ = PMap.empty := vN_empty_of_persistent₀ _ (workTy_persistent S SW R _ o) hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            by simpa using he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := worksTy_atN₀ E (j₀ + 1) hr j (by simpa using hj)
          refine ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), ?_⟩
          rw [show j₀ + (j + 1) = j₀ + 1 + j by omega]
          simpa using hg'

/-- **The exits at `vN₀`** (Core's `exitsTy_at`), as the works. -/
theorem exitsTy_atN₀ {S : Row} {R : VTy} {Xs : Nat → VTy} {δ : LSub} {Θ : LocTy} {k : Nat} :
    ∀ (E : List (Qual × VTy × VTy)) (j₀ : Nat) {vc : Val} {ρ : WRes},
      vN₀ (ℍ := ℍ) (exitsTy S R Xs E j₀) δ Θ k vc ρ →
      ∀ j, j < E.length → ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vN₀ (ℍ := ℍ) (exitTy S R (Xs (j₀ + j))) δ Θ k g PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, j₀, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, ρ₁, ρ₂, rfl, -, hg, hr⟩ := h
      have he : ρ₁ = PMap.empty := vN_empty_of_persistent₀ (exitTy S R (Xs j₀)) rfl hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            by simpa using he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := exitsTy_atN₀ E (j₀ + 1) hr j (by simpa using hj)
          refine ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), ?_⟩
          rw [show j₀ + (j + 1) = j₀ + 1 + j by omega]
          simpa using hg'

/-- The steps of a clause at `(v, κ)` after its `β` step (Core's `lastClause_steps` without its
first step): to the work under the finaliser frame. -/
theorem lastClause_steps_body (j : Nat) (vc vn g v κ : Val)
    (hg : PureSteps (pickE j (.val vc)) (.val g)) :
    PureSteps (Expr.subst 0 (Val.pair v κ) (.letpair (.var 0)
      (thenE
        (.case (.var 0)
          (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.var 0))
          (.app (.val (.lam (.app (pickE j ((Expr.val vn).shift 6 0)) (.var 1))))
            (.app (.var 2) (.val (Val.inj₂ .unit)))))
        (.app (.var 1) (.val (Val.inj₂ .unit)))
        (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))))
      ((ubindK (lastN j κ vn) (lastD κ)).plug (.app (.val g) (.val v))) := by
  refine (PureSteps.head (fun μ => Head.letpair μ v κ _) rfl).trans ?_
  have e : ((Expr.subst 2 ((Val.pair v κ).shift 2 0) (thenE
      (.case (.var 0)
        (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.var 0))
        (.app (.val (.lam (.app (pickE j ((Expr.val vn).shift 6 0)) (.var 1))))
          (.app (.var 2) (.val (Val.inj₂ .unit)))))
      (.app (.var 1) (.val (Val.inj₂ .unit)))
      (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))).subst 0 (κ.shift 1 0)).subst 0 v =
      (ubindK (lastN j κ vn) (lastD κ)).plug (.app (pickE j (.val vc)) (.val v)) := by
    simp [thenE, pickE_subst, lastN, lastD, Kont.plug, subst_shift_succ, Val.pair, Val.lam,
      Val.inj₁, Val.inj₂, Val.unit, Val.prim, Expr.subst, Val.val_shift, Expr.shift_shift,
      Expr.shift_zero]
  rw [e]
  have := PureSteps.plug ((ubindK (lastN j κ vn) (lastD κ)).comp (.appL .hole v)) hg
  rw [Kont.plug_comp, Kont.plug_comp] at this
  exact this

/-- A non-abortive entry that is not `lin` is capturable. -/
theorem capB_of_entN {q : Qual} {B : VTy} (ha : (B.isZero && q != .lin) = false) (hq : q ≠ .lin) :
    capB q B = true := by
  simp only [Bool.and_eq_false_iff, bne_eq_false_iff_eq] at ha
  simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  rcases ha with ha | ha
  · exact ⟨hq, ha⟩
  · exact absurd ha hq

/-! ### The frame's answer -/

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life}

/-- **The finaliser frame's answer** (Core's `last_cont`): `inl y` resumes `κ` at `y`; `inr z`
cancels `κ`, at the table of its cancel row `G`, beside `z`, which the cancel leaves held (left
behind where `G` may raise or be captured, so `X` consumes there), and then runs the exit at `z`.
The answer is below the stop's index `K₀`, where `κ` is owed. -/
theorem last_contN₀ (hΘ : Θ.OK) {T' : OpTabN} (hT' : T'.Down) {G : CTy}
    (hGT : (tabN₀ (ℍ := ℍ) G δ Θ c).Le T')
    (hGu : ∀ n i o, Row.find G.rowOf n i = some o → o.q ≠ .unr)
    {X : VTy} (hXd : Row.Cancels G.rowOf → X.OwnFree) {Q : PostN} (hQ : Q.Down) {en : OpEntN}
    (hwr : ∀ ls ρ, en.wc ls ls ρ) (hq : en.q ≠ .lin) {B : VTy}
    (hPB : ∀ k ls w ρ, vN₀ (ℍ := ℍ) B δ Θ k w ρ → ConsistentX c ρ → en.PB k ls w ρ)
    {j : Nat} {vn nfv : Val} (hnf : PureSteps (pickE j (.val vn)) (.val nfv))
    {κ : Val} {K₀ k : Nat} (hk : k < K₀)
    (hX : ∀ k', k' ≤ k → ∀ ls z σ, vN₀ (ℍ := ℍ) X δ Θ k' z σ → ConsistentX c σ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN T') Q k' ls (.app (.val nfv) (.val z)) σ) {ls : List SRec} {v : Val} {ρ : WRes}
    (h : ((fun ρ => vN₀ (ℍ := ℍ) (.sum B X) δ Θ k v ρ ∧ ConsistentX c ρ) ⋆
      KapRelN (ℍ := ℍ) (Θ.view c) (opTableN T') Q en (some (tabN₀ (ℍ := ℍ) G δ Θ c)) K₀ ls κ) ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN T') Q k ls ((ubindK (lastN j κ vn) (lastD κ)).plug (.val v))
      ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  have hTd := opTableN_down hT'
  obtain ⟨σ₁, σ₂, hc, ⟨hv, hcv⟩, hk'⟩ := h
  rcases hv with ⟨y, rfl, hy⟩ | ⟨z, rfl, hz⟩
  · exact erwp_pureSteps hΦ hTd hQ (lastN_inl j κ vn y)
      ((hk'.2 ls (hwr ls σ₂) k hk).1 y σ₁ ρ (hPB _ _ _ _ hy hcv) (ResU.CompS.comm hc))
  · refine erwp_pureSteps hΦ hTd hQ (lastN_inr j κ vn z) ?_
    have hcan := (hk'.2 ls (hwr ls σ₂) k hk).2 hq _ rfl
    have hcan' := erwp_idxLe k k le_rfl ls _ σ₂ hcan
    refine erwp_frame_plain_or hΦ (tabN₀ (ℍ := ℍ) G δ Θ c) T' hGT (exitK j vn z)
      (exitK_plain j vn z).1 (exitK_plain j vn z).2
      (fun _ τ => vN₀ (ℍ := ℍ) X δ Θ k z τ ∧ ConsistentX c τ) (fun _ _ _ _ h => h)
      (fun m i en₁ hT₁ ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ =>
        (tabN_down G δ Θ hΘ.1 c).wcl m i en₁ hT₁ ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁)
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ _ Q ?_ k ls _ σ₂ hcan' σ₁ ρ ⟨hz, hcv⟩
      (ResU.CompS.comm hc)
    · rintro m i en₁ hT₁ ha₁ ls' τ ⟨hτ, -⟩
      obtain ⟨o, hf, rfl⟩ := tabN_rowOf_find hT₁
      refine vN_noOwn_of_ownFree₀ (hXd ⟨o, (Row.find_mem hf).1, ?_⟩) hτ
      simp only [entN, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha₁
      exact ha₁.2
    · rintro m i en₁ hT₁ hq₁
      obtain ⟨o, hf, rfl⟩ := tabN_rowOf_find hT₁
      exact absurd hq₁ (hGu m i o hf)
    · rintro m i en₁ hT₁ - hq₁ k' ls' K₁ ρ' τ ρ'' hcan₁ ⟨hτ, -⟩ hc'
      obtain ⟨o, hf, rfl⟩ := tabN_rowOf_find hT₁
      exact entN_plain hΦ _ (exitK_plain j vn z).1 ((exitK_plain j vn z).2 0)
        (vN_noOwn_of_ownFree₀ (hXd ⟨o, (Row.find_mem hf).1, hq₁⟩) hτ) o hcan₁ hc'
    · rintro k' ls' w τ ⟨τa, τb, hcab, ⟨hk'', hw⟩, ⟨hz', hcz'⟩⟩
      obtain ⟨rfl, rfl⟩ := hw
      rw [eq_of_compS_empty_left hcab]
      exact erwp_pureSteps hΦ hTd hQ (exitK_steps j vn z nfv hnf)
        (hX k' hk'' ls' z τb (vN_le₀ hk'' hz') hcz')

end

/-! ### The handler -/

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {S SW : Row}
  {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy} {n : UInt32} {A R : VTy}

/-- **A `[handle-last]` handler** (Core's `ewp_handle_last`): `erwp_handle_le` at the handled row's
table, its payloads at the handler's name read at the view (`erwp_consistentPA`), `κ`'s cancel
branch at the table of the operation's own cancel row. A clause pays its `β` step and runs its
work at its row under the finaliser frame (`erwp_frame_then`), whose finaliser `κ.2 ()` cancels
`κ` and whose answer is `last_contN₀`; the work's value is consistent with the view across its
resumptions (`erwp_consistentAns`). -/
theorem erwp_handle_last₀ (hΘ : Θ.OK) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hNZ : S.NZ) (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
    (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
    (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
    {vr vw vn : Val} {N : Nat}
    (hVr : vN₀ (ℍ := ℍ) (retTy S A R) δ Θ N vr PMap.empty)
    (hVw : vN₀ (ℍ := ℍ) (worksTy S SW R Xs E 0) δ Θ N vw PMap.empty)
    (hVn : vN₀ (ℍ := ℍ) (exitsTy S R Xs E 0) δ Θ N vn PMap.empty) {ls : List SRec} {e : Expr}
    {ρ : WRes}
    (h : erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ Θ c))
      (fun k _ v ρ => vN₀ (ℍ := ℍ) A δ Θ k v ρ) N ls e ρ) (hc : ConsistentX c ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c))
      (fun k _ v ρ => vN₀ (ℍ := ℍ) R δ Θ k v ρ) N ls (hndE (lastH n E vr vw vn) e) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  set Tin := tabN₀ (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ Θ c with hTin
  set Tout := tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c with hTout
  have hToutD : Tout.Down := tabN_down _ δ Θ hΘ.1 c
  have hQout : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) R δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
  have hTd := opTableN_down hToutD
  have h' := erwp_consistentPA (tabN_ansC _ δ Θ c) n N ls e ρ h hc
  refine erwp_handle_le hΦ N (Tin.withPA c n) Tout (OpTabN.withPA_down (tabN_down _ δ Θ hΘ.1 c))
    hToutD n (fun m i hm => by rw [OpTabN.withPA_ne _ hm, hTin, tabN_ofEff_ne A R δ Θ c hm])
    (qualsVal (E.map Prod.fst)) vr
    ⟨lastTuple E 0 (.val vw) (.val vn), isVal_lastTuple _ _ E 0⟩ _ _ hQout
    (fun i en hT _ => by
      obtain ⟨en₀, hT₀, rfl⟩ := OpTabN.withPA_self hT
      exact capTag_ofEffN hnS hlen i en₀ hT₀)
    (fun i => some (tabN₀ (ℍ := ℍ) (fs i.toNat) δ Θ c)) ?_ ?_ ?_ N le_rfl ls e ρ h'
  · -- `κ`'s cancel branch: the entry's own cancel obligation
    intro i en hT ha hq Tk hTk
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabN.withPA_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_self hnS hlen hT₀
    simp only [hji, Option.some.injEq] at hTk
    subst hTk
    exact ⟨_, entN_fin_of (PA := fun k v ρ => vN₀ (ℍ := ℍ) E[j].2.1 δ Θ k v ρ)
      (PB := fun k v ρ => vN₀ (ℍ := ℍ) E[j].2.2 δ Θ k v ρ ∧ ConsistentX c ρ)
      (capB_of_entN ha hq) (hFin j hj).1, fun _ _ _ h => h,
      tabN_down _ δ Θ hΘ.1 c⟩
  · -- `[ret]`: `h_ret` at the value, consistent with the view
    rintro k hk ls' v σ ⟨hv, hcv⟩
    obtain ⟨-, hr⟩ := hVr
    exact (cN_effOf₀ S R δ Θ c k ls' _ σ).mp (hr Θ (LocTy.extR_refl Θ _) hΘ c
      (consistentX_empty c) ls' c k hk v σ σ (compS_empty_left σ) hv hcv)
  · intro i en' hT
    obtain ⟨en, hT₀, rfl⟩ := OpTabN.withPA_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_self hnS hlen hT₀
    obtain ⟨g, hg, hVg⟩ := worksTy_atN₀ E 0 hVw j hj
    obtain ⟨nfv, hnf, hVnf⟩ := exitsTy_atN₀ E 0 hVn j hj
    rw [Nat.zero_add] at hVg hVnf
    refine ⟨⟨lastClause j (E[j].2.2.isZero && E[j].1 != .lin) (.val vw) (.val vn),
      isVal_lastClause _ _ _ _⟩, by rw [hji, clauseAt_lastTuple _ _ E 0 j hj]; simp,
      fun ha k hk ls' v κ σ hσ => ?_, fun ha k hk ls' v σ hσ => ?_⟩
    · -- the clause pays its `β` step, then runs its work under the finaliser frame
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = false := ha
      have hq := last_cancel hCancel hj ha'
      obtain ⟨-, hFS, -, hFth, hFP, hFX⟩ := hFin j hj
      simp only [workTy, ha'] at hVg
      show erwp (ℍ := ℍ) _ _ _ k ls' (.app (lastClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vw) (.val vn)) (.pair (.val v) κ.1)) σ
      rw [ha']
      obtain ⟨σa, σk, hck, ⟨hA', hcA⟩, hK⟩ := hσ
      simp only [hji] at hK
      cases k with
      | zero => exact erwp_zero
      | succ k₀ =>
      refine erwp_step (opTableN_local _) (e' := Expr.subst 0 (Val.pair v κ) _)
        (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl .hole) ?_
      refine erwp_pureSteps hΦ hTd hQout (lastClause_steps_body j vw vn g v κ hg) ?_
      -- the work's run at `Σ_W`, consistent with the view
      obtain ⟨-, hgr⟩ := hVg
      have hy := hgr Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_empty c) ls' c k₀ (by omega) v σa
        σa (compS_empty_left σa) (vN_down₀ _ δ Θ k₀ v σa hA') hcA
      have hy' := (cN_effOf₀ SW (.sum E[j].2.2 (Xs j)) δ Θ c k₀ ls' _ σa).mp hy
      have hy'' := erwp_consistentAns (tabN_ansC _ δ Θ c) k₀ k₀ le_rfl ls' _ σa hy' hcA
      rw [tabN_effOf_ret SW _ .unit] at hy''
      rw [hTout, tabN_effOf_ret S R .unit]
      refine erwp_frame_then hΘ.1 S SW (fs j).rowOf hNZ hSW hFS hFth hFP (lastN j κ vn) (lastD κ)
        (fun ls σ => KapRelN (ℍ := ℍ) (Θ.view c) (opTableN Tout)
          (fun k _ v ρ => vN₀ (ℍ := ℍ) R δ Θ k v ρ) (OpEntN.withPA c _)
          (some (tabN₀ (ℍ := ℍ) (fs j) δ Θ c)) (k₀ + 1) ls κ σ)
        (fun ls₁ ls₂ hs σ hF => KapRelN.extF rfl (extF_of_same hs σ) hF)
        (fun ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ hF => KapRelN.extF rfl (extF_right hc₁ he₁) hF)
        (fun hu => absurd hu hSu) (Qd := unitPost) (fun _ _ v ρ hv => ⟨hv.2, hv.1 ▸ noOwn_empty⟩)
        k₀ ?_ _ _ hQout ?_ k₀ le_rfl ls' _ σa hy'' σk σ hK hck
      · -- the finaliser `κ.2 ()` cancels `κ` at its cancel row's table
        intro k hk ls₁ ρ₁ hF
        refine erwp_pureSteps hΦ (opTableN_down (tabN_down _ δ Θ hΘ.1 c)) unitPost_down
          (lastD_steps κ) ?_
        rw [← tabN_rowOf]
        exact (hF.2 ls₁ (extF_refl ls₁ ρ₁) k (by omega)).2 hq _ rfl
      · -- the frame's answer
        rintro k hk ls₁ w τ ⟨τ₁, τ₂, hcτ, ⟨-, hw, hcw, -⟩, hF⟩
        rw [← tabN_effOf_ret S R .unit]
        refine last_contN₀ hΘ hToutD (by rw [tabN_rowOf]; exact tabN_le_of_rowLe hFS _ R δ Θ c)
          (fun _ _ _ hf => find_not_unr hFS hSu hf) hFX hQout (fun ls ρ => extF_refl ls ρ) hq
          ?_ hnf (Nat.lt_succ_of_le hk) ?_ ⟨τ₁, τ₂, hcτ, ⟨hw, hcw⟩, hF⟩
        · exact fun _ _ _ _ hw hcw => ⟨hw, hcw⟩
        intro k' hk' ls₂ z σz hz hcz
        obtain ⟨-, hnr⟩ := hVnf
        exact (cN_effOf₀ S R δ Θ c k' ls₂ _ σz).mp (hnr Θ (LocTy.extR_refl Θ _) hΘ c
          (consistentX_empty c) ls₂ c k' (by omega) z σz σz (compS_empty_left σz) hz hcz)
    · -- an abortive operation: the clause runs its work `w v` at the outer row
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = true := ha
      simp only [workTy, ha'] at hVg
      show erwp (ℍ := ℍ) _ _ _ k ls' (.app (lastClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vw) (.val vn)) (.val v)) σ
      rw [ha', lastClause_abort]
      refine erwp_pureSteps hΦ hTd hQout (tailClauseA_steps j vw g v hg) ?_
      obtain ⟨-, hgr⟩ := hVg
      obtain ⟨hA', hcA⟩ := hσ
      exact (cN_effOf₀ S R δ Θ c k ls' _ σ).mp (hgr Θ (LocTy.extR_refl Θ _) hΘ c
        (consistentX_empty c) ls' c k hk v σ σ (compS_empty_left σ) hA' hcA)

end

/-- **`[handle-last]`** (Core's `handleL_compatC`): `handle_n e with (h_ret, ws, nfs)`, the clauses
written out from the works `ws` and the exits `nfs` (`lastTuple`). The handler's values are read
off its run at the run's start (`erwp_val_post`), as Core reads them off `wpTS`; the handled
computation runs at its row's table from the part of the resource consistent with the view
(`gN_splitC₀`), and the handler is `erwp_handle_last₀`. A `Div` row is a row of the chain's table
(E13), so Core's split at `Row.divB S` has no counterpart, and neither do the rule's `n ≠ 0` and
`n ≠ Div`, which only that split and Core's `ewp_handle` read. -/
theorem handleL_compatN₀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Hr Hw Hn e : Expr} {S SW : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁)
    (hHw : Hw.ValFormIn Γ₁) (hHn : Hn.ValFormIn Γ₁)
    (hc : SemJN₀ (ℍ := ℍ) Δ Γ₁ (.pair Hr (.pair Hw Hn))
      (.val (.tensor (retTy S A R) (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0)))))
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hNZ : S.NZ) (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
    (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
    (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
    (he : SemJN₀ (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (lastTuple E 0 Hw Hn)) e)
      (.comp (CTy.effOf S R)) := by
  intro δ γ Θ c N ls ρ hδ hΘ hcρ hlw hg
  refine (cN_effOf₀ S R δ Θ c N ls _ ρ).mpr (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂, -, hc₂⟩ := gN_splitC₀ hsp hg hcρ hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hρ₁ : ρ₁ = PMap.empty := gN_deadP₀ hd hg₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ (.pair Hr (.pair Hw Hn))) :=
    isVal_psub_valFormIn hlw₁ (.pair hHr (.pair hHw hHn))
  have hH' : erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
      (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (retTy S A R)
        (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0))) δ Θ k v ρ) N ls
      (⟨substAll γ (.pair Hr (.pair Hw Hn)), hval⟩ : Val).1 PMap.empty :=
    hc δ γ Θ c N ls PMap.empty hδ hΘ (consistentX_empty c) hlw₁ hg₁
  have hE' := (cN_effOf₀ _ A δ Θ c N ls _ ρ₂).mp (he δ γ Θ c N ls ρ₂ hδ hΘ hc₂ hlw₂ hg₂)
  show erwp (ℍ := ℍ) _ _ _ N ls
    (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) (.pair Hr (lastTuple E 0 Hw Hn)) e)) ρ₂
  rw [psub_hndExpr]
  simp only [Expr.psub]
  rw [show Expr.psub 0 γ (lastTuple E 0 Hw Hn) = lastTuple E 0 (substAll γ Hw) (substAll γ Hn) from
    lastTuple_psub γ Hw Hn E 0]
  -- the handler's values, read off its run at the run's start
  rw [erwp_eq]
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ls', ρ', -, hv'⟩ := erwp_val_post (by omega) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg hI hl hfd
  obtain ⟨vr, vwn, σ₁, σ₂, hpair, -, hVr, hVwn⟩ := hv'
  have hσ₁ : σ₁ = PMap.empty := vN_empty_of_persistent₀ _ (retTy_persistent S A R) hVr
  subst hσ₁
  obtain ⟨vw, vn, τ₁, τ₂, hpair', -, hVw, hVn⟩ := hVwn
  have hτ₁ : τ₁ = PMap.empty := vN_empty_of_persistent₀ _ (worksTy_persistent S SW R Xs E 0) hVw
  have hτ₂ : τ₂ = PMap.empty := vN_empty_of_persistent₀ _ (exitsTy_persistent S R Xs E 0) hVn
  subst hτ₁ hτ₂
  have hHe : substAll γ (.pair Hr (.pair Hw Hn)) = (Val.pair vr vwn).1 :=
    congrArg Subtype.val hpair
  rw [hpair'] at hHe
  simp only [substAll, Expr.psub, Val.pair] at hHe
  obtain ⟨h₁, h₂⟩ := Expr.pair.inj hHe
  obtain ⟨h₃, h₄⟩ := Expr.pair.inj h₂
  have hH := erwp_handle_last₀ (fs := fs) hΘ hnS hlen hNZ hSW hSu hCancel hFin hVr hVw hVn hE' hc₂
  rw [erwp_eq] at hH
  rw [h₁, show substAll γ Hw = vw.1 from h₃, show substAll γ Hn = vn.1 from h₄] at hrun
  exact hH ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
