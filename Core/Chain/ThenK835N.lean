import Core.Chain.Goal791N

/-!
# `[then]`'s producers at `erwpK`, over a row's table at a world  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §9. `Then835N`'s five producers (`cfin_cancelN`, `cfin_runN`,
`then_cancelN`, `seq_raise_runN`, `erwp_frame_then`), each stated over the row-indexed table family
`tabF` at any reading of a world (`RowRd`), by the original's induction on the index and recursion
on the cancel row. Each original is proved again at one world (`*_of_K`); its text is the
original's.

What a world adds, each the K-reading of a step the original takes at one world:

* **the continuation is owed at the worlds the entry allows**, at the joint share of the stop and
  the frame the producer puts beside it; the entry's order passes to the stop's own part
  (`RowRd.OK.wkLeft`, the joint share valid, `rwpG_validK`);
* **what rides in the continuation is carried to the resumption world**: a kept error and a pending
  raise's payload by `RowRd.PayExt` (Core's `errOk_local`, the error carried along `Ext`), the
  finaliser's frame by `hFe` read along the stop's order;
* **the modes**: a finaliser's operations are read under the mode of the row it is typed at, and a
  cancel run it joins under a higher one (the cancel row's, `sub`), at which an entry owes at fewer
  worlds (`RowRd.OK.wk_anti`);
* **the worlds the runs are read at** (`Inv`): every world an entry owes at.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload cfinE ubindE errNext)

variable {ι M : Type} {R : RowRd ι M}

/-- **A kept error of a cancel row whose errors are persistent holds nothing**
(`errOkN_empty_of_pers`). -/
theorem errOkF_empty_of_pers (hR : R.OK) {μ : M} {x : ι} {F : CTy} (hF : F.FinPers) {k : Nat}
    {ls : List SRec} : ∀ {err : Option Val} {ρ : WRes},
      errOkK (tabF (ℍ := ℍ) R μ (CTy.effOf F.rowOf .unit) x) k ls err ρ → ρ = PMap.empty
  | none, _, h => h.1
  | some _, _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨-, hT, ha⟩, hA, -⟩ := pure_sep_iff.mp h
      obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
      have ha' : o.abort = true := by simpa [RowRd.ent, OpSig.abort] using ha
      exact hR.vrPers _ ((finPers_of_mem hF (Row.find_mem hf).1).1 ha') _ _ _ _ hA

/-! ### A finaliser under a cancel's `cfin` -/

/-- **A nested cancel past a running finaliser's `cfin`, at `erwpK`** (`cfin_cancelN`): a cancel
run at the cancel row `G` under the mode `μ`, under `cfin err` holding an error of `P`, is one at
any `G′ ≥ pend P G` that is not `⊤`, under any mode `μ′ ≥ μ`. The error rides in each stop's
continuation and is carried to the resumption world (`errOkF_ext`). -/
theorem cfin_cancelK (hR : R.OK) (hPE : R.PayExt) (P : Row) (err : Option Val)
    (G : CTy) :
    ∀ {G' : CTy} {μ μ' μP : M}, R.le μ μ' → PendLe P G G' → G'.isTop = false →
    ∀ n x, R.Inv x → ∀ ls e ρ, R.canc (ℍ := ℍ) (fun z => tabF (ℍ := ℍ) R μ G z) x n ls e ρ →
      ∀ σe ρ', errOkK (tabF (ℍ := ℍ) R μP (CTy.effOf P .unit) x) n ls err σe →
        (G.FinUnr → σe = PMap.empty) → ResU.CompS ρ σe ρ' →
        R.canc (ℍ := ℍ) (fun z => tabF (ℍ := ℍ) R μ' G' z) x n ls
          ((cfinK (cancelVal err)).plug e) ρ' := by
  intro G' μ μ' μP hμ hle hG'
  rw [PendLe, hG'] at hle
  obtain ⟨-, hGG, hPG⟩ := hle.resolve_left (by simp)
  have hL : ∀ z, (cancelTabK (R.fl z) (tabF (ℍ := ℍ) R μ G z)).Local :=
    fun z => cancelTabK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρ h σe ρ' he hu hc
  have hPD := erwpPostK_down (V := R.V x)
    (cancelTabK_downI (lo := R.fl x) (tabF_downI hR μ' G' x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  show erwpK (ℍ := ℍ) _ _ _ _ x n ls _ ρ'
  rw [erwpK_eq]
  refine rwpG_bind (hR.ΦDown x hx) (cfinK _) ?_
  have hfr := rwpG_validK (rwpG_frame (fun _ τ => τ = σe) (fun _ _ _ _ h => h) hc
    (erwpK_unfold_at hL le_rfl h) rfl)
  refine rwpG_mono_le (fun k hk ls' t τ ⟨⟨τ₁, τ₂, hcτ, hp, hτ₂⟩, hvτ⟩ => ?_) hfr
  subst hτ₂
  rcases hp with ⟨_, _, _, _, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₀, err', hs'⟩
  · exact hv.elim
  · -- an operation of the nested cancel's finaliser: the `cfin` joins its continuation
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu', f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hfo, rfl⟩ := tabF_rowOf_find hT
    obtain ⟨o', hf', hs, hfin⟩ := hGG m i o hfo
    have hT' : tabF (ℍ := ℍ) R μ' G' x m i = some (R.ent μ' m o.q o.A o.B
        (finF (ℍ := ℍ) R (R.sub μ' m) o'.fin) x) := by
      rw [tabF_rowOf]; exact tabF_find_sig hf' hs
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hvk' : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvτ).2
    have hKo : ((cfinK (cancelVal err)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    have ht' : (cfinK (cancelVal err)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((cfinK (cancelVal err)).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(cfinK (cancelVal err)).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
        ⟨ρa, ρk', hcσ', hA, fun hq => ?_, f, hf, fun y hy ls'' hext =>
          ⟨fun k' hk'' w τ₃ τ₄ hB hcτ' => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq' : o.q = .unr := hq
      rw [hu' hq', hu (finUnr_of_find hfo (Or.inl hq'))] at hk'
      exact eq_of_compS_empty_left hk'
    · have hy₀ : R.wk μ m x f y ρk :=
        hR.wkLeft μ m x f y ρk τ₂ ρk' hk' hvk' (hR.wk_anti μ μ' m x f y ρk' hμ hy)
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      have hey := errOkF_ext hPE (ResU.CompS.comm hk') hy (errOkF_le hR (ls' := ls'') hk he)
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont y hy₀ ls'' hwc).1 k' hk'' w τ₃ z hB hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y (hR.wkInv _ _ _ _ _ _ hy) ls'' _ z h₁ τ₂ τ₄
        (errOkF_le hR (by omega) hey) hu hcz
    · have hy₀ : R.wk μ m x f y ρk :=
        hR.wkLeft μ m x f y ρk τ₂ ρk' hk' hvk' (hR.wk_anti μ μ' m x f y ρk' hμ hy)
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      have hey := errOkF_ext hPE (ResU.CompS.comm hk') hy (errOkF_le hR (ls' := ls'') hk he)
      obtain ⟨hcap, hnT, rfl⟩ := entF_fin_cancel hP'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont y hy₀ ls'' hwc).2 hq _ (entF_fin_of hcap hoT)
      show R.canc (ℍ := ℍ) _ y k ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancelK hR hPE P err o.fin (hR.sub_mono μ μ' m hμ) hfin' hnT k y
        (hR.wkInv _ _ _ _ _ _ hy) ls'' _ ρk hcan τ₂ ρk' (errOkF_le hR le_rfl hey)
        (fun hu₁ => hu (finUnr_of_find hfo (Or.inr ⟨hcap, hu₁⟩))) hk'
  · -- the nested cancel's end passes the `cfin`: the earlier error wins
    obtain ⟨⟨rfl, hK₀⟩, τa, τb, hcab, he₀, hnb⟩ := pure_sep_iff.mp hs'
    refine rwpG_det (hR.ΦDown x hx) (hPD _)
      (fun hp => step1Only_plug (Head.cfcancel hp err err' K₀ hK₀) rfl .hole) ?_
    have hfin : ∀ hp, Final (ℍ := ℍ) hp (Kont.hole.plug (opE true (cancelVal (err.or err')))) :=
      final_opPlug (payloadName_cancelVal _) (by simp [OpFree, Kont.Catches])
    refine rwpG_here hfin (Or.inr (Or.inr ⟨.hole, err.or err', pure_sep_mk ⟨rfl, rfl⟩ ?_⟩))
    have hnτa : NoOwn τa := by
      cases err' with
      | none => rw [show τa = PMap.empty from he₀.1]; exact noOwn_empty
      | some _ =>
          obtain ⟨_, _, _, _, h⟩ := he₀
          exact (pure_sep_iff.mp h).2.2
    cases err with
    | some E =>
        refine ⟨τ₂, τ₁, ResU.CompS.comm hcτ, ?_, noOwn_compS hcab hnτa hnb⟩
        rw [tabF_rowOf]
        exact errOkF_of_sub hPG (errOkF_le hR hk he)
    | none =>
        have hτ₂ : τ₂ = PMap.empty := he.1
        subst hτ₂
        rw [eq_of_compS_empty_left (ResU.CompS.comm hcτ)]
        refine ⟨τa, τb, hcab, ?_, hnb⟩
        rw [tabF_rowOf] at he₀ ⊢
        exact errOkF_of_sub (fun n i o hf _ => by
          obtain ⟨o', hf', hs, -⟩ := hGG n i o hf; exact ⟨o', hf', hs⟩) he₀
termination_by sizeOf G
decreasing_by exact rowOf_fin_lt G (Row.find_mem hfo).1

/-- **A finaliser running under a cancel's `cfin`, at `erwpK`** (`cfin_runN`): `D` at the row `E`
under the mode `μD`, the cancel keeping an error of `P`, is a cancel run at any `T` that has `E`'s
operations, their cancel rows with `P`'s errors pending, and `P`'s errors, under any mode
`μ ≥ μD`. -/
theorem cfin_runK (hR : R.OK) (hPE : R.PayExt) (E P : Row) (err : Option Val)
    {T : CTy} {μD μ μP : M} (hμ : R.le μD μ)
    (hE : ∀ n i o, Row.find E n i = some o → ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → PendLe P o.fin o'.fin))
    (hP : ∀ n i o, Row.find P n i = some o → o.abort = true →
      ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o')
    (hNZ : ∀ n i o, Row.find E n i = some o → o.n ≠ 0)
    {Qd : ι → PostN} (hQd : ∀ y k ls v ρ, Qd y k ls v ρ → NoOwn ρ) :
    ∀ n x, R.Inv x → ∀ ls d ρ, erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μD (CTy.effOf E .unit) z)) Qd x n ls d ρ →
      ∀ σe ρ', errOkK (tabF (ℍ := ℍ) R μP (CTy.effOf P .unit) x) n ls err σe →
        (E.UnrD → σe = PMap.empty) → ResU.CompS ρ σe ρ' →
        R.canc (ℍ := ℍ) (fun z => tabF (ℍ := ℍ) R μ T z) x n ls
          (cfinE (cancelVal err) d) ρ' := by
  have hL : ∀ z, (opTableK (R.fl z) (tabF (ℍ := ℍ) R μD (CTy.effOf E .unit) z)).Local :=
    fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls d ρ h σe ρ' he hu hc
  have hPD := erwpPostK_down (V := R.V x)
    (cancelTabK_downI (lo := R.fl x) (tabF_downI hR μ T x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  show erwpK (ℍ := ℍ) _ _ _ _ x n ls ((cfinK (cancelVal err)).plug d) ρ'
  rw [erwpK_eq]
  refine rwpG_bind (hR.ΦDown x hx) (cfinK _) ?_
  have hfr := rwpG_validK (rwpG_frame (fun _ τ => τ = σe) (fun _ _ _ _ h => h) hc
    (erwpK_unfold_at hL le_rfl h) rfl)
  refine rwpG_mono_le (fun k hk ls' t τ ⟨⟨τ₁, τ₂, hcτ, hp, hτ₂⟩, hvτ⟩ => ?_) hfr
  subst hτ₂
  rcases hp with ⟨w, rfl, y, -, hw⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, j, w, en, hp⟩
  · -- the finaliser finished: the cancel goes on with its error
    refine rwpG_det (hR.ΦDown x hx) (hPD _)
      (fun hp => step1Only_plug (Head.cfret hp err w) rfl .hole) ?_
    have hfin : ∀ hp, Final (ℍ := ℍ) hp (Kont.hole.plug (opE true (cancelVal err))) :=
      final_opPlug (payloadName_cancelVal err) (by simp [OpFree, Kont.Catches])
    refine rwpG_here hfin (Or.inr (Or.inr ⟨.hole, err, pure_sep_mk ⟨rfl, rfl⟩
      ⟨τ₂, τ₁, ResU.CompS.comm hcτ, ?_, hQd _ _ _ _ _ hw⟩⟩))
    rw [tabF_rowOf]
    exact errOkF_of_sub hP (errOkF_le hR hk he)
  · -- an operation of the finaliser passes the dead region; the `cfin` joins its continuation
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu', f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hfo, rfl⟩ := tabF_effOf_some_find hTn
    obtain ⟨o', hf', hs, hfin⟩ := hE m i o hfo
    have hT' : tabF (ℍ := ℍ) R μ T x m i = some (R.ent μ m o.q o.A o.B
        (finF (ℍ := ℍ) R (R.sub μ m) o'.fin) x) := by
      rw [tabF_rowOf]; exact tabF_find_sig hf' hs
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hvk' : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvτ).2
    have hKo : ((cfinK (cancelVal err)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    have ht' : (cfinK (cancelVal err)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((cfinK (cancelVal err)).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(cfinK (cancelVal err)).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
        ⟨ρa, ρk', hcσ', hA, fun hq => ?_, f, hf, fun y hy ls'' hext =>
          ⟨fun k' hk'' w τ₃ τ₄ hB hcτ' => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq' : o.q = .unr := hq
      rw [hu' hq', hu (unr_of_find hfo (Or.inl hq'))] at hk'
      exact eq_of_compS_empty_left hk'
    · have hy₀ : R.wk μD m x f y ρk :=
        hR.wkLeft μD m x f y ρk τ₂ ρk' hk' hvk' (hR.wk_anti μD μ m x f y ρk' hμ hy)
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      have hey := errOkF_ext hPE (ResU.CompS.comm hk') hy (errOkF_le hR (ls' := ls'') hk he)
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont y hy₀ ls'' hwc).1 k' hk'' w τ₃ z hB hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y (hR.wkInv _ _ _ _ _ _ hy) ls'' _ z h₁ τ₂ τ₄
        (errOkF_le hR (by omega) hey) hu hcz
    · have hy₀ : R.wk μD m x f y ρk :=
        hR.wkLeft μD m x f y ρk τ₂ ρk' hk' hvk' (hR.wk_anti μD μ m x f y ρk' hμ hy)
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      have hey := errOkF_ext hPE (ResU.CompS.comm hk') hy (errOkF_le hR (ls' := ls'') hk he)
      obtain ⟨hcap, hnT, rfl⟩ := entF_fin_cancel hP'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont y hy₀ ls'' hwc).2 hq _ (entF_fin_of hcap hoT)
      show R.canc (ℍ := ℍ) _ y k ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancelK hR hPE P err o.fin (hR.sub_mono μD μ m hμ) hfin' hnT k y
        (hR.wkInv _ _ _ _ _ _ hy) ls'' _ ρk hcan τ₂ ρk' (errOkF_le hR le_rfl hey)
        (fun hu₁ => hu (unr_of_find hfo (Or.inr ⟨hcap, hu₁⟩))) hk'
  · -- a raise of the finaliser: the first error is kept, and the cancel goes on
    obtain ⟨⟨rfl, hK₁, hTm, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hfo, rfl⟩ := tabF_effOf_some_find hTm
    have hm : m ≠ 0 := by rw [← (Row.find_mem hfo).2.1]; exact hNZ m j o hfo
    refine rwpG_det (hR.ΦDown x hx) (hPD _)
      (fun hp => step1Only_plug (Head.cferr hp err m j w K₁ hm hK₁) rfl .hole) ?_
    have hfin : ∀ hp, Final (ℍ := ℍ) hp
        (Kont.hole.plug (opE true (cancelVal (errNext err m j w)))) :=
      final_opPlug (payloadName_cancelVal _) (by simp [OpFree, Kont.Catches])
    refine rwpG_here hfin (Or.inr (Or.inr ⟨.hole, errNext err m j w, pure_sep_mk ⟨rfl, rfl⟩ ?_⟩))
    have hnτ₁ : NoOwn τ₁ := noOwn_compS hcan hnA hnn
    cases err with
    | some E' =>
        refine ⟨τ₂, τ₁, ResU.CompS.comm hcτ, ?_, hnτ₁⟩
        rw [tabF_rowOf]
        exact errOkF_of_sub hP (errOkF_le hR hk he)
    | none =>
        have hτ₂ : τ₂ = PMap.empty := he.1
        subst hτ₂
        rw [eq_of_compS_empty_left (ResU.CompS.comm hcτ)]
        obtain ⟨o', hf', hs, -⟩ := hE m j o hfo
        refine ⟨ρa, ρn, hcan, ⟨m, j, w, R.ent μ m o.q o.A o.B
          (finF (ℍ := ℍ) R (R.sub μ m) o'.fin) x, pure_sep_mk ⟨rfl, ?_, ha⟩ ⟨hPA, hnA⟩⟩, hnn⟩
        rw [tabF_rowOf]; exact tabF_find_sig hf' hs

/-! ### A cancel run through the finaliser frame -/

/-- **A cancel run through a finaliser frame, at `erwpK`** (`then_cancelN`), by recursion on the
cancel row `F` below it and, inside, induction on the index. `D` is read under the mode `μD`, the
cancel run under `μ`, the result under any `μ′` above both. The frame `Fr`, read at a world, rides
in each stop's continuation and is carried to the resumption world along the stop's order, at the
floor the stop chose (`hFe`). -/
theorem then_cancelK (hR : R.OK) (hPE : R.PayExt) (E : Row)
    (hNZ : ∀ n i o, Row.find E n i = some o → o.n ≠ 0) (Nv Dv : Val)
    (Fr : ι → List SRec → WProp)
    (hFs : ∀ x ls ls', (∀ r, r ∈ ls' ↔ r ∈ ls) → ∀ ρ, Fr x ls ρ → Fr x ls' ρ)
    (hFe : ∀ μ' m x f y ls ls' ρ σ ρ', f ≤ R.fl x → ResU.CompS ρ σ ρ' → ResU.Valid ρ' →
      R.wk μ' m x f y ρ' → extF ls ls' ρ' → Fr x ls σ → Fr y ls' σ)
    {Qd : ι → PostN} (hQd : ∀ y k ls v ρ, Qd y k ls v ρ → NoOwn ρ) (N₀ : Nat) {μD : M}
    (hD : ∀ x, R.Inv x → ∀ k, k ≤ N₀ → ∀ ls ρ, Fr x ls ρ →
      erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μD (CTy.effOf E .unit) z)) Qd x k ls
        (.app (.val Dv) (.val .unit)) ρ)
    (F : CTy) : ∀ {T : CTy} {μ μ' : M}, R.le μD μ' → R.le μ μ' → ThenLe F E T →
      T.isTop = false → (T.FinUnr → ∀ x ls σ, Fr x ls σ → σ = PMap.empty) →
      (E.UnrD → F.FinPers) →
      ∀ n, n ≤ N₀ → ∀ x, R.Inv x → ∀ ls e ρ,
        R.canc (ℍ := ℍ) (fun z => tabF (ℍ := ℍ) R μ F z) x n ls e ρ →
        ∀ σ ρ', Fr x ls σ → ResU.CompS ρ σ ρ' →
          R.canc (ℍ := ℍ) (fun z => tabF (ℍ := ℍ) R μ' T z) x n ls
            ((ubindK Nv Dv).plug e) ρ' := by
  intro T μ μ' hDμ hμ hle hT hunr hpers
  rw [ThenLe, hT] at hle
  obtain ⟨-, hFT, hET⟩ := hle.resolve_left (by simp)
  have hL : ∀ z, (cancelTabK (R.fl z) (tabF (ℍ := ℍ) R μ F z)).Local :=
    fun z => cancelTabK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x hx ls e ρ h σ ρ' hF hc
  have hPD := erwpPostK_down (V := R.V x)
    (cancelTabK_downI (lo := R.fl x) (tabF_downI hR μ' T x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  show erwpK (ℍ := ℍ) _ _ _ _ x n ls _ ρ'
  rw [erwpK_eq]
  refine rwpG_bind (hR.ΦDown x hx) (ubindK Nv Dv) ?_
  have hfr := rwpG_validK (rwpG_frame (Fr x) (hFs x) hc (erwpK_unfold_at hL le_rfl h) hF)
  refine rwpG_mono_le (fun k hk ls' t τ ⟨⟨τ₁, τ₂, hcτ, hp, hF₂⟩, hvτ⟩ => ?_) hfr
  rcases hp with ⟨_, _, _, _, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₀, err, hs'⟩
  · exact hv.elim
  · -- an operation below the frame: the frame joins its continuation
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu', f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hfo, rfl⟩ := tabF_rowOf_find hTn
    obtain ⟨o', hf', hs, hfin⟩ := hFT m i o hfo
    have hT' : tabF (ℍ := ℍ) R μ' T x m i = some (R.ent μ' m o.q o.A o.B
        (finF (ℍ := ℍ) R (R.sub μ' m) o'.fin) x) := by
      rw [tabF_rowOf]; exact tabF_find_sig hf' hs
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hvk' : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvτ).2
    have hKo : ((ubindK Nv Dv).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    have ht' : (ubindK Nv Dv).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubindK Nv Dv).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubindK Nv Dv).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
        ⟨ρa, ρk', hcσ', hA, fun hq => ?_, f, hf, fun y hy ls'' hext =>
          ⟨fun k' hk'' w τ₃ τ₄ hB hcτ' => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq₀ : o.q = .unr := hq
      have hq' : o'.q = .unr := by rw [← hs.2.2.1]; exact hq₀
      rw [hu' hq₀, hunr (finUnr_of_find hf' (Or.inl hq')) x ls' τ₂ hF₂] at hk'
      exact eq_of_compS_empty_left hk'
    · have hy₀ : R.wk μ m x f y ρk :=
        hR.wkLeft μ m x f y ρk τ₂ ρk' hk' hvk' (hR.wk_anti μ μ' m x f y ρk' hμ hy)
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont y hy₀ ls'' hwc).1 k' hk'' w τ₃ z hB hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) (by omega) y (hR.wkInv _ _ _ _ _ _ hy) ls'' _ z h₁ τ₂ τ₄
        (hFe μ' m x f y ls' ls'' ρk τ₂ ρk' hf hk' hvk' hy hext hF₂) hcz
    · have hy₀ : R.wk μ m x f y ρk :=
        hR.wkLeft μ m x f y ρk τ₂ ρk' hk' hvk' (hR.wk_anti μ μ' m x f y ρk' hμ hy)
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨hcap, hnT, rfl⟩ := entF_fin_cancel hP'
      have hcap' : capB o'.q o'.B = true := hs.capB_eq ▸ hcap
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont y hy₀ ls'' hwc).2 hq _ (entF_fin_of hcap hoT)
      show R.canc (ℍ := ℍ) _ y k ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancelK hR hPE E hNZ Nv Dv Fr hFs hFe hQd N₀ hD o.fin
        (hR.le_trans _ _ _ hDμ (hR.le_sub μ' m)) (hR.sub_mono μ μ' m hμ) hfin' hnT
        (fun hu₁ => hunr (finUnr_of_find hf' (Or.inr ⟨hcap', hu₁⟩)))
        (fun hu₁ => (finPers_of_mem (hpers hu₁) (Row.find_mem hfo).1).2 hcap) k (by omega) y
        (hR.wkInv _ _ _ _ _ _ hy) ls'' _ ρk hcan τ₂ ρk'
        (hFe μ' m x f y ls' ls'' ρk τ₂ ρk' hf hk' hvk' hy hext hF₂) hk'
  · -- the cancel reaches the frame: `D` runs under `cfin`
    obtain ⟨⟨rfl, hK₀⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    refine rwpG_det (hR.ΦDown x hx) (hPD _)
      (fun hp => step1Only_plug (Head.ufinC hp Nv Dv err K₀ hK₀) rfl .hole) ?_
    obtain ⟨z, hz, hcz⟩ := compS_exch hcab hcτ
    refine erwpK_unfold_at (fun z => cancelTabK_local _ _) hk (erwpK_garbage hcz hnb ?_)
    rw [tabF_rowOf] at he
    exact cfin_runK hR hPE E F.rowOf err (T := T) (μP := μ) hDμ hET (fun n i o hf _ => by
        obtain ⟨o', hf', hs, -⟩ := hFT n i o hf; exact ⟨o', hf', hs⟩) hNZ hQd k x hx ls' _ τ₂
      (hD x hx k (by omega) ls' τ₂ hF₂) τa z he
      (fun hu => errOkF_empty_of_pers hR (hpers hu) he) (ResU.CompS.comm hz)
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem hfo).1

/-! ### The finaliser frame -/

/-- **A finaliser under ordinary unwinding, at `erwpK`** (`seq_raise_runN`): `D (); raise p`, `D`
at a row `E ≤ Σ`. The pending raise's payload rides in each stop of `D` and is carried to the
resumption world (`RowRd.PayExt`); at a cancel it is left behind (`entF_plain`). -/
theorem seq_raise_runK (hR : R.OK) (hPE : R.PayExt) (S E : Row) (hES : RowLe E S)
    {n i : UInt32} {v : Val} {o : OpSig} (hfo : Row.find S n i = some o) (ha : o.abort = true)
    {μ : M} {Qd : ι → PostN} (hQd : ∀ y k ls v ρ, Qd y k ls v ρ → v = .unit ∧ NoOwn ρ)
    {Q : ι → PostN} (hQ : ∀ y, (Q y).Down) :
    ∀ k x, R.Inv x → ∀ ls d ρ, erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf E .unit) z)) Qd x k ls d ρ →
      ∀ σp ρ', (R.vr o.A R.δ (R.Θ x) k v σp ∧ NoOwn σp) → (E.UnrD → σp = PMap.empty) →
        ResU.CompS ρ σp ρ' →
        erwpK (ℍ := ℍ) R.V R.Φ
          (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)) Q x k ls
          (.seq d (raiseE (.val (opPayload n i v)))) ρ' := by
  have hL : ∀ z, (opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf E .unit) z)).Local :=
    fun z => opTableK_local _ _
  have ha' : ∀ x, (R.ent μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o.fin) x).abort =
      true := fun x => by simpa [RowRd.ent, OpSig.abort] using ha
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x hx ls d ρ h σp ρ' hp hu hc
  have hPD := erwpPostK_down (V := R.V x)
    (opTableK_downI (lo := R.fl x) (tabF_downI hR μ (CTy.effOf S .unit) x)) (Q := Q) hQ
  have hTn : tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) x n i = some (R.ent μ n o.q o.A o.B
      (finF (ℍ := ℍ) R (R.sub μ n) o.fin) x) := by
    rw [tabF_effOf_find, hfo]; rfl
  show erwpK (ℍ := ℍ) _ _ _ _ x k ls ((seqRaiseK (opPayload n i v)).plug d) ρ'
  rw [erwpK_eq]
  refine rwpG_bind (hR.ΦDown x hx) (seqRaiseK (opPayload n i v)) ?_
  have hfr := rwpG_validK (rwpG_frame (fun _ τ => τ = σp) (fun _ _ _ _ h => h) hc
    (erwpK_unfold_at hL le_rfl h) rfl)
  refine rwpG_mono_le (fun k₁ hk₁ ls' t τ ⟨⟨τ₁, τ₂, hcτ, hq, hτ₂⟩, hvτ⟩ => ?_) hfr
  subst hτ₂
  have hp' : R.vr o.A R.δ (R.Θ x) k₁ v τ₂ ∧ NoOwn τ₂ := ⟨hR.vr_le hk₁ hp.1, hp.2⟩
  rcases hq with ⟨w, rfl, y, hy, hw⟩ | ⟨K₁, m, j, w, en₁, hq⟩ | ⟨K₁, m, j, w, en₁, hq⟩
  · -- the finaliser finished: the raise goes on
    rw [hR.Veq x y hy] at hw
    obtain ⟨rfl, hnw⟩ := hQd _ _ _ _ _ hw
    refine rwpG_det (hR.ΦDown x hx) (hPD _)
      (fun hp => step1Only_plug (Head.seq hp _) rfl .hole) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload n i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, n, i, v, _,
        pure_sep_mk ⟨rfl, rfl, hTn, ha' x⟩ ⟨τ₂, τ₁, ResU.CompS.comm hcτ, hp', hnw⟩⟩))
  · -- an operation of the finaliser: the pending raise joins its continuation
    obtain ⟨⟨rfl, hK₁, hTm, ha₁⟩, ρa, ρk, hcak, hA, hu', f, hf, hcont⟩ := pure_sep_iff.mp hq
    obtain ⟨o₁, hf₁, rfl⟩ := tabF_effOf_some_find hTm
    obtain ⟨o₁', -, hs, hT', hLe⟩ := tabF_rowLe_entry R (μ := μ) (x := x) hES hf₁
    obtain ⟨hLq, hLa, hLA, hLB, hLw, -, hLf⟩ := hLe
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hvk' : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvτ).2
    have hKo : ((seqRaiseK (opPayload n i v)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; rfl
    have ht' : (seqRaiseK (opPayload n i v)).plug (K₁.plug (performE (.val (opPayload m j w)))) =
        ((seqRaiseK (opPayload n i v)).comp K₁).plug (opE false (opPayload m j w)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m j w) hKo) (Or.inr (Or.inl
      ⟨(seqRaiseK (opPayload n i v)).comp K₁, m, j, w, _, pure_sep_mk ⟨rfl, hKo, hT',
        hLa ▸ ha₁⟩ ⟨ρa, ρk', hcσ', hLA ▸ hA, fun hq' => ?_, f, hf, fun y hy ls'' hext =>
          ⟨fun k' hk'' w' τ₃ τ₄ hB hcτ' => ?_, fun hq' P' hP' => ?_⟩⟩⟩))
    · rw [hu' (hLq.trans hq'), hu (unr_of_find hf₁ (Or.inl (hLq.trans hq')))] at hk'
      exact eq_of_compS_empty_left hk'
    · have hy₀ : R.wk μ m x f y ρk := hR.wkLeft μ m x f y ρk τ₂ ρk' hk' hvk' hy
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      have hpy : R.vr o.A R.δ (R.Θ y) k₁ v τ₂ :=
        hPE μ m x f y τ₂ ρk ρk' (ResU.CompS.comm hk') hy o.A k₁ v hp'.1
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont y hy₀ ls'' hwc).1 k' hk'' w' τ₃ z (hLB ▸ hB) hz
      simp only [erwpCK, show k' < k by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y (hR.wkInv _ _ _ _ _ _ hy) ls'' _ z h₁ τ₂ τ₄
        ⟨hR.vr_le (by omega) hpy, hp'.2⟩ hu hcz
    · have hy₀ : R.wk μ m x f y ρk := hR.wkLeft μ m x f y ρk τ₂ ρk' hk' hvk' hy
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk τ₂ ρk' hk' hext
      have hq₁ : (R.ent μ m o₁.q o₁.A o₁.B
          (finF (ℍ := ℍ) R (R.sub μ m) o₁.fin) x).q ≠ .lin := hLq ▸ hq'
      have hplain := entF_plain hR (seqRaiseK (opPayload n i v)) (seqRaiseK_hasHnd _)
        (seqRaiseK_catches _ 0) hp'.2 o₁ (hR.wkInv _ _ _ _ _ _ hy)
        (fun P₀ hP₀ => (hcont y hy₀ ls'' hwc).2 hq₁ P₀ hP₀) hk'
      exact finLeSK_apply (hLf ha₁ hq₁) hP' (fun P₀ hP₀ => hplain P₀ hP₀)
  · -- a raise of the finaliser supersedes the pending one
    obtain ⟨⟨rfl, hK₁, hTm, ha₁⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hq
    obtain ⟨o₁, hf₁, rfl⟩ := tabF_effOf_some_find hTm
    obtain ⟨o₁', -, hs, hT', hLe⟩ := tabF_rowLe_entry R (μ := μ) (x := x) hES hf₁
    obtain ⟨-, hLa, hLA, -, -, -, -⟩ := hLe
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcτ
    have hKo : ((seqRaiseK (opPayload n i v)).comp K₁).Catches m = false := by
      rw [catches_comp, hK₁]; rfl
    have ht' : (seqRaiseK (opPayload n i v)).plug (K₁.plug (raiseE (.val (opPayload m j w)))) =
        ((seqRaiseK (opPayload n i v)).comp K₁).plug (opE true (opPayload m j w)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m j w) hKo) (Or.inr (Or.inr
      ⟨(seqRaiseK (opPayload n i v)).comp K₁, m, j, w, _, pure_sep_mk ⟨rfl, hKo, hT',
        hLa ▸ ha₁⟩ ⟨ρa, z, hcz, ⟨hLA ▸ hPA, hnA⟩, noOwn_compS hz hnn hp'.2⟩⟩))

/-- **The finaliser frame around an effectful computation, at `erwpK`** (`erwp_frame_then`), at
the rows of `[then]`, every table under one mode `μ`. A stop of `M` keeps the frame in its
continuation, carried to the resumption world at the floor the stop chose (`hFe`); its cancel
passes the frame and fires `D` (`then_cancelK`, under the cancel row's mode). An abortive stop runs `D` first (`seq_raise_runK`).
A value is posted at the run's own world. -/
theorem erwpK_frame_then (hR : R.OK) (hPE : R.PayExt) (S SM SD : Row) (hNZ : S.NZ)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (Nv Dv : Val) (Fr : ι → List SRec → WProp)
    (hFs : ∀ x ls ls', (∀ r, r ∈ ls' ↔ r ∈ ls) → ∀ ρ, Fr x ls ρ → Fr x ls' ρ)
    (hFe : ∀ μ' m x f y ls ls' ρ σ ρ', f ≤ R.fl x → ResU.CompS ρ σ ρ' → ResU.Valid ρ' →
      R.wk μ' m x f y ρ' → extF ls ls' ρ' → Fr x ls σ → Fr y ls' σ)
    (hU : S.UnrD → ∀ x ls ρ, Fr x ls ρ → ρ = PMap.empty)
    {Qd : ι → PostN} (hQd : ∀ y k ls v ρ, Qd y k ls v ρ → v = .unit ∧ NoOwn ρ) (N₀ : Nat)
    {μ : M}
    (hD : ∀ x, R.Inv x → ∀ k, k ≤ N₀ → ∀ ls ρ, Fr x ls ρ →
      erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf SD .unit) z)) Qd x k ls
        (.app (.val Dv) (.val .unit)) ρ)
    (Q₁ Q : ι → PostN) (hQ : ∀ y, (Q y).Down)
    (hkv : ∀ x, R.Inv x → ∀ k, k ≤ N₀ → ∀ ls (v : Val) ρ, (Q₁ x k ls v ⋆ Fr x ls) ρ →
      erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)) Q x k ls
        ((ubindK Nv Dv).plug (.val v)) ρ) :
    ∀ n, n ≤ N₀ → ∀ x, R.Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) R.V R.Φ
        (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf SM .unit) z)) Q₁ x n ls e ρ →
      ∀ ρ₂ ρ', Fr x ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwpK (ℍ := ℍ) R.V R.Φ
          (fun z => opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)) Q x n ls
          ((ubindK Nv Dv).plug e) ρ' := by
  have hL : ∀ z, (opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf SM .unit) z)).Local :=
    fun z => opTableK_local _ _
  have hLS : ∀ z, (opTableK (R.fl z) (tabF (ℍ := ℍ) R μ (CTy.effOf S .unit) z)).Local :=
    fun z => opTableK_local _ _
  have hNZD : ∀ n i o, Row.find SD n i = some o → o.n ≠ 0 := by
    intro n i o hf
    obtain ⟨o', hf', hle⟩ := hDS n i o hf
    rw [hle.1.1]; exact hNZ o' (Row.find_mem hf').1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x hx ls e ρ h ρ₂ ρ' hF hc
  have hPD := erwpPostK_down (V := R.V x)
    (opTableK_downI (lo := R.fl x) (tabF_downI hR μ (CTy.effOf S .unit) x)) (Q := Q) hQ
  rw [erwpK_eq] at h ⊢
  refine rwpG_bind (hR.ΦDown x hx) (ubindK Nv Dv) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hcσ, hp, hF'⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (Fr x) (hFs x) hc h hF))
  rcases hp with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · rw [hR.Veq x y hy] at hv
    exact erwpK_unfold_at hLS hk (hkv x hx k (by omega) ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  · -- a `perform`: the frame joins the continuation's share; its cancel fires `D`
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hfo, rfl⟩ := tabF_effOf_some_find hTn
    obtain ⟨o', hf', hs, hT', hLe⟩ := tabF_rowLe_entry R (μ := μ) (x := x) hMS hfo
    obtain ⟨hLq, hLa, hLA, hLB, hLw, -, -⟩ := hLe
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    have hvk' : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvσ).2
    have hKo : ((ubindK Nv Dv).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    have ht' : (ubindK Nv Dv).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubindK Nv Dv).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubindK Nv Dv).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', hLa ▸ ha⟩
        ⟨ρa, ρk', hcσ', hLA ▸ hA, fun hq => ?_, f, hf, fun y hy ls'' hext =>
          ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq' : o.q = .unr := hLq.trans hq
      rw [hu hq', hU ⟨o', (Row.find_mem hf').1, Or.inl hq⟩ x ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · have hy₀ : R.wk μ m x f y ρk := hR.wkLeft μ m x f y ρk σ₂ ρk' hk' hvk' hy
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk σ₂ ρk' hk' hext
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont y hy₀ ls'' hwc).1 k' hk'' w τ₁ z (hLB ▸ hB) hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) (by omega) y (hR.wkInv _ _ _ _ _ _ hy) ls'' _ z h₁ σ₂ τ₂
        (hFe μ m x f y ls' ls'' ρk σ₂ ρk' hf hk' hvk' hy hext hF') hcz
    · have hy₀ : R.wk μ m x f y ρk := hR.wkLeft μ m x f y ρk σ₂ ρk' hk' hvk' hy
      have hwc : extF ls' ls'' ρk := extF_left ls' ls'' ρk σ₂ ρk' hk' hext
      obtain ⟨hcap', hnT, rfl⟩ := entF_fin_cancel hP'
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hth := hfin m i o o' hfo hf' hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hth
        exact (hth.resolve_left (by simp)).1
      have hcan := (hcont y hy₀ ls'' hwc).2 (hLq ▸ hq) _ (entF_fin_of hcap hoT)
      show R.canc (ℍ := ℍ) _ y k ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancelK hR hPE SD hNZD Nv Dv Fr hFs hFe
        (fun _ _ _ _ _ h => (hQd _ _ _ _ _ h).2) N₀ hD o.fin (hR.le_sub μ m)
        (hR.le_refl _) hth hnT (fun hu₁ => hU ⟨o', (Row.find_mem hf').1, Or.inr ⟨hcap', hu₁⟩⟩)
        (fun hu₁ => ((hP hu₁) o (Row.find_mem hfo).1).2 hcap) k (by omega) y
        (hR.wkInv _ _ _ _ _ _ hy) ls'' _ ρk hcan σ₂ ρk'
        (hFe μ m x f y ls' ls'' ρk σ₂ ρk' hf hk' hvk' hy hext hF') hk'
  · -- a `raise`: the finaliser runs, then the `raise` goes on
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hfo, rfl⟩ := tabF_effOf_some_find hTn
    obtain ⟨o', hf', hs, -, -⟩ := tabF_rowLe_entry R (μ := μ) (x := x) hMS hfo
    have hao : o.abort = true := by simpa [RowRd.ent, OpSig.abort] using ha
    have hn0 : m ≠ 0 := by
      rw [← (Row.find_mem hfo).2.1, hs.1]; exact hNZ o' (Row.find_mem hf').1
    refine rwpG_det (hR.ΦDown x hx) (hPD _)
      (fun hp => step1Only_plug (Head.ufin hp Nv Dv m i v K₁ hn0 hK₁) rfl .hole) ?_
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcσ
    obtain ⟨y, hy, hcy⟩ := compS_lcomm hz hcz
    refine erwpK_unfold_at hLS hk (erwpK_garbage (ResU.CompS.comm hcy) hn ?_)
    have hPA' : R.vr o'.A R.δ (R.Θ x) k v ρa := by rw [← hs.2.2.2.1]; exact hPA
    exact seq_raise_runK hR hPE S SD hDS hf' (by rw [← hs.abort_eq]; exact hao) hQd hQ k x hx ls'
      _ σ₂ (hD x hx k (by omega) ls' σ₂ hF') ρa y ⟨hPA', hnA⟩
      (fun hu => hR.vrPers _ (((hP hu) o (Row.find_mem hfo).1).1 hao) _ _ _ _ hPA)
      (ResU.CompS.comm hy)

/-! ### At the typed world -/

/-- **`[then]`'s frame along an entry's order at the typed world**: the context of `N` and `D`,
`𝒢⟦Γ⟧` at the stop's world and consistent with its view, at a part of a valid share at which the
lender's entry owes `y`, is that at `y` (`gN_extR` along `ExtR` at the part; the view from the
order, at the part, `consistentX_right`). This is `hFe` of `then_cancelK` and `erwpK_frame_then`
at `KW`. -/
theorem gNFrame_carryKW (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (N : Nat) :
    ∀ (μ : Unit) (m : UInt32) (x : KW) (f : Life) (y : KW) (ls ls' : List SRec)
      (ρ σ ρ' : WRes), ResU.CompS ρ σ ρ' → ResU.Valid ρ' → (rdN (ℍ := ℍ) δ).wk μ m x f y ρ' →
      extF ls ls' ρ' →
      (gN (ℍ := ℍ) δ x.Θ Γ γ N σ ∧ ConsistentX x.c σ) →
      gN (ℍ := ℍ) δ y.Θ Γ γ N σ ∧ ConsistentX y.c σ := by
  intro _ m x f y ls ls' ρ σ ρ' hc hv hy _ hF
  have hy' : x.Owed f y ρ' := hy
  exact ⟨gN_extR (hy'.1.extR.right hc) hF.1, consistentX_right hc hy'.2.2.1 hv⟩

/-- **The finaliser frame at `cN`'s tables** (`erwpK_frame_then` at `KW`): every table the row's
`tabN`, the reading's premises discharged (`rdN_ok`, `rdN_payExt`). What is left is
`erwp_frame_then`'s, read at every world whose location typing is downward closed, and the frame
carried along the order (`hFe`, which `gNFrame_carryKW` discharges for `[then]`'s context). -/
theorem erwpK_frame_then_tabKW {δ : LSub} (SS SM SD : Row) (hNZ : SS.NZ)
    (hMS : RowLe SM SS) (hDS : RowLe SD SS)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find SS n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (Nv Dv : Val) (Fr : KW → List SRec → WProp)
    (hFs : ∀ x ls ls', (∀ r, r ∈ ls' ↔ r ∈ ls) → ∀ ρ, Fr x ls ρ → Fr x ls' ρ)
    (hFe : ∀ (μ : Unit) m x f y ls ls' ρ σ ρ', f ≤ x.lo → ResU.CompS ρ σ ρ' → ResU.Valid ρ' →
      (rdN (ℍ := ℍ) δ).wk μ m x f y ρ' → extF ls ls' ρ' → Fr x ls σ → Fr y ls' σ)
    (hU : SS.UnrD → ∀ x ls ρ, Fr x ls ρ → ρ = PMap.empty)
    {Qd : KW → PostN} (hQd : ∀ y k ls v ρ, Qd y k ls v ρ → v = .unit ∧ NoOwn ρ) (N₀ : Nat)
    (hD : ∀ x : KW, x.Θ.Down → ∀ k, k ≤ N₀ → ∀ ls ρ, Fr x ls ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf SD .unit) δ z)) Qd x k ls
        (.app (.val Dv) (.val .unit)) ρ)
    (Q₁ Q : KW → PostN) (hQ : ∀ y, (Q y).Down)
    (hkv : ∀ x : KW, x.Θ.Down → ∀ k, k ≤ N₀ → ∀ ls (v : Val) ρ, (Q₁ x k ls v ⋆ Fr x ls) ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf SS .unit) δ z)) Q x k ls
        ((ubindK Nv Dv).plug (.val v)) ρ) :
    ∀ n, n ≤ N₀ → ∀ x : KW, x.Θ.Down → ∀ ls e ρ,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf SM .unit) δ z)) Q₁ x n ls e ρ →
      ∀ ρ₂ ρ', Fr x ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
          (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf SS .unit) δ z)) Q x n ls
          ((ubindK Nv Dv).plug e) ρ' := by
  simp only [tabN_eq] at hD hkv ⊢
  exact erwpK_frame_then (rdN_ok δ) (rdN_payExt δ) SS SM SD hNZ hMS hDS hfin hP Nv Dv Fr hFs
    hFe hU hQd N₀ hD Q₁ Q hQ hkv

/-! ### At one world -/

end BoCa.Fig16.LogRel.Core.Chain.SI

end
