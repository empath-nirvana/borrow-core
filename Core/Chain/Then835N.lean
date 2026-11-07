import Core.Chain.Iter835N

/-!
# `[then]` at `SemJN₀`: a finaliser that performs and raises  `[spec §19, §27]`

Interface entry E9 (`scope-831-interface.md`): Core's finaliser frame (`Core/EffFin.lean`), each
lemma at `erwp`, by induction on the index where Core inducts on `ewpTS`'s least fixed point:

* `errOkN_of_sub` (Core's `errOk_of_sub`): errors move along a first-match inclusion;
* `cfin_cancelN` (Core's `cfin_cancel`): a nested cancel past a running finaliser's `cfin`;
* `cfin_runN` (Core's `cfin_run`): a finaliser running under a cancel's `cfin`;
* `then_cancelN` (Core's `then_cancel`): a cancel run through the finaliser frame;
* `seq_raise_runN` (Core's `seq_raise_run`): a finaliser under ordinary unwinding;
* `erwp_frame_then` (Core's `ewp_frame_then_or`): the finaliser frame around an effectful
  computation;
* `then_compatN` (Core's `then_compatC`) and `thenDiv_compatN` (Core's `then_compatC_div`).

Two readings the chain adds, each where `erwp_frame_plain` adds it:

* **the index.** The finaliser `D` and the continuation `N` run at the index a stop or a value is
  reached at, below the index the frame (the context of `N` and `D`) is read at; every lemma here
  is owed up to that index `N₀`;
* **the view.** `N` and `D` are read at the run's view, from the frame beside a value or beside
  nothing, each consistent with it (the frame by `gN_splitC`, the value across `M`'s resumptions
  by `erwp_consistentAns`, the row's answers being read at the view).

A `Div` row is a row of the chain's table (E13), so Core's table beside the operation table (`Px`,
a tick at a row holding `Div`) and the erasure of the tick's key (`er`) have no counterpart:
`erwp_frame_then` is Core's `ewp_frame_then_or` at `Px = ∅`, `er = false`, and `[then]` at a row
holding `Div` is the same lemma (`thenDiv_compatN`).
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
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload cfinE ubindE errNext)

/-- A row's table at a key, rewritten along a signature: the entry of `o′` is `o`'s but for the
cancel row. -/
theorem tabN_find_sig {S : Row} {R : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life}
    {n i : UInt32} {o o' : OpSig} (hf : Row.find S n i = some o') (hs : o.Sig o') :
    tabN₀ (ℍ := ℍ) (CTy.effOf S R) δ Θ c n i = some (entN o.q o.B
      (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ)
      (finN₀ (ℍ := ℍ) o'.fin δ Θ c)) := by
  obtain ⟨-, -, hq, hA, hB, -⟩ := hs
  rw [tabN_effOf_find, hf, hq, hA, hB]; rfl

/-- **Errors move along a first-match inclusion of abortive operations** (Core's
`errOk_of_sub`). -/
theorem errOkN_of_sub {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {P P' : Row}
    (h : ∀ n i o, Row.find P n i = some o → o.abort = true →
      ∃ o', Row.find P' n i = some o' ∧ o.Sig o') {k : Nat} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes},
      errOkN (tabN₀ (ℍ := ℍ) (CTy.effOf P .unit) δ Θ c) k ls err ρ →
      errOkN (tabN₀ (ℍ := ℍ) (CTy.effOf P' .unit) δ Θ c) k ls err ρ
  | none, _, h => h
  | some _, _, ⟨m, j, w, en, h'⟩ => by
      obtain ⟨⟨h₁, hT, ha⟩, h₅⟩ := pure_sep_iff.mp h'
      obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
      have ha' : o.abort = true := by simpa [entN, OpSig.abort] using ha
      obtain ⟨o', hf', hs⟩ := h m j o hf ha'
      exact ⟨m, j, w, _, pure_sep_mk ⟨h₁, tabN_find_sig hf' hs, ha⟩ h₅⟩

/-- A cancel row's table is the table of its layers, at a key. -/
theorem tabN_rowOf_find {G : CTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {n i : UInt32}
    {en : OpEntN} (h : tabN₀ (ℍ := ℍ) G δ Θ c n i = some en) :
    ∃ o, Row.find G.rowOf n i = some o ∧ en = entN o.q o.B (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ) (finN₀ (ℍ := ℍ) o.fin δ Θ c) := by
  rw [tabN_rowOf] at h
  exact tabN_effOf_some_find h

/-- The cancel obligation of a capturable entry is the cancel run at its cancel row, which is not
`⊤`. -/
theorem entN_fin_cancel {q : Qual} {B : VTy} {PA PB : Nat → Val → WRes → Prop} {F : CTy}
    {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {P : Nat → List SRec → Expr → WProp}
    (hP : (entN q B PA PB (finN₀ (ℍ := ℍ) F δ Θ c)).fin = some P) :
    capB q B = true ∧ F.isTop = false ∧
      P = cancelOblN (ℍ := ℍ) (Θ.view c) (tabN₀ (ℍ := ℍ) F δ Θ c) := by
  simp only [entN] at hP
  split at hP
  · rename_i hcap
    rw [finN_eq_ite] at hP
    split at hP
    · cases hP
    · rename_i hT
      cases hP
      exact ⟨hcap, by simpa using hT, rfl⟩
  · cases hP

/-- The entry at a capturable key has the cancel obligation at its cancel row. -/
theorem entN_fin_of {q : Qual} {B : VTy} {PA PB : Nat → Val → WRes → Prop} {F : CTy}
    {δ : LSub} {Θ : LocTy} {c : Loc → Option Life}
    (hcap : capB q B = true) (hT : F.isTop = false) :
    (entN q B PA PB (finN₀ (ℍ := ℍ) F δ Θ c)).fin =
        some (cancelOblN (ℍ := ℍ) (Θ.view c) (tabN₀ (ℍ := ℍ) F δ Θ c)) := by
  simp only [entN, hcap, if_true, finN_eq_ite, hT, Bool.false_eq_true, if_false]

/-! ### A finaliser under a cancel's `cfin` -/

/-- **A nested cancel past a running finaliser's `cfin`** (Core's `cfin_cancel`): a cancel run at
the cancel row `G`, under `cfin err` holding an error of `P`, is one at any `G′ ≥ pend P G` that is
not `⊤`. At its end the kept error, the earlier, wins; its operations' nested cancels pass the same
`cfin`. The error holds nothing where `G` may stop at an unrestricted operation. -/
theorem cfin_cancelN {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life} (P : Row)
    (err : Option Val) (G : CTy) :
    ∀ {G' : CTy}, PendLe P G G' → G'.isTop = false →
    ∀ n ls e ρ, cancelOblN (ℍ := ℍ) (Θ.view c) (tabN₀ (ℍ := ℍ) G δ Θ c) n ls e ρ →
      ∀ σe ρ', errOkN (tabN₀ (ℍ := ℍ) (CTy.effOf P .unit) δ Θ c) n ls err σe →
        (G.FinUnr → σe = PMap.empty) → ResU.CompS ρ σe ρ' →
        cancelOblN (ℍ := ℍ) (Θ.view c) (tabN₀ (ℍ := ℍ) G' δ Θ c) n ls
          ((cfinK (cancelVal err)).plug e) ρ' := by
  intro G' hle hG'
  rw [PendLe, hG'] at hle
  obtain ⟨-, hGG, hPG⟩ := hle.resolve_left (by simp)
  have hΦ := LocTy.view_down hΘ c
  have hL := cancelTabN_local (tabN₀ (ℍ := ℍ) G δ Θ c)
  have hPD := erwpPost_down (cancelTabN_down (tabN_down G' δ Θ hΘ c)) falsePost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h σe ρ' he hu hc
  show erwp (ℍ := ℍ) _ _ _ _ _ _ _
  rw [erwp_eq]
  refine rwpG_bind hΦ (cfinK _) ?_
  have hfr := rwpG_frame (fun _ τ => τ = σe) (fun _ _ _ _ h => h) hc
    (erwp_unfold_at hL le_rfl h) rfl
  refine rwpG_mono_le (fun k hk ls' t τ ⟨τ₁, τ₂, hcτ, hp, hτ₂⟩ => ?_) hfr
  subst hτ₂
  rcases hp with ⟨_, _, hv⟩ | ⟨K₀, err', hs'⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact hv.elim
  · -- the nested cancel's end passes the `cfin`: the earlier error wins
    obtain ⟨⟨rfl, hK₀⟩, τa, τb, hcab, he₀, hnb⟩ := pure_sep_iff.mp hs'
    refine rwpG_det hΦ (hPD _)
      (fun μ => step1Only_plug (Head.cfcancel μ err err' K₀ hK₀) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal (err.or err')))) :=
      final_opPlug (payloadName_cancelVal _) (by simp [OpFree, Kont.Catches])
    refine rwpG_here hfin (Or.inr (Or.inl ⟨.hole, err.or err', pure_sep_mk ⟨rfl, rfl⟩ ?_⟩))
    have hnτa : NoOwn τa := by
      cases err' with
      | none => rw [show τa = PMap.empty from he₀.1]; exact noOwn_empty
      | some _ =>
          obtain ⟨_, _, _, _, h⟩ := he₀
          exact (pure_sep_iff.mp h).2.2
    cases err with
    | some E =>
        refine ⟨τ₂, τ₁, ResU.CompS.comm hcτ, ?_, noOwn_compS hcab hnτa hnb⟩
        rw [tabN_rowOf]
        exact errOkN_of_sub hPG (errOkN_tabN_le hk he)
    | none =>
        have hτ₂ : τ₂ = PMap.empty := he.1
        subst hτ₂
        rw [eq_of_compS_empty_left (ResU.CompS.comm hcτ)]
        refine ⟨τa, τb, hcab, ?_, hnb⟩
        rw [tabN_rowOf] at he₀ ⊢
        exact errOkN_of_sub (fun n i o hf _ => by
          obtain ⟨o', hf', hs, -⟩ := hGG n i o hf; exact ⟨o', hf', hs⟩) he₀
  · -- an operation of the nested cancel's finaliser: the `cfin` joins its continuation
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hp
    have hT₀ := hT
    obtain ⟨o, hf, rfl⟩ := tabN_rowOf_find hT
    obtain ⟨o', hf', hs, hfin⟩ := hGG m i o hf
    have hT' : tabN₀ (ℍ := ℍ) G' δ Θ c m i = some (entN o.q o.B
        (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
        (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ)
        (finN₀ (ℍ := ℍ) o'.fin δ Θ c)) := by
      rw [tabN_rowOf]; exact tabN_find_sig hf' hs
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hKo : ((cfinK (cancelVal err)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    have ht' : (cfinK (cancelVal err)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((cfinK (cancelVal err)).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨(cfinK (cancelVal err)).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
        ⟨ρa, ρk', hcσ', hA, fun hq => ?_, fun ls'' hext =>
          ⟨fun k' hk'' w τ₃ τ₄ hB hcτ' => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq' : o.q = .unr := hq
      rw [hu' hq', hu (finUnr_of_find hf (Or.inl hq'))] at hk'
      exact eq_of_compS_empty_left hk'
    · have hwc := (tabN_down G δ Θ hΘ c).wcl m i _ hT₀ ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont ls'' hwc).1 k' hk'' w τ₃ z hB hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) ls'' _ z h₁ τ₂ τ₄ (errOkN_tabN_le (by omega) he) hu hcz
    · have hwc := (tabN_down G δ Θ hΘ c).wcl m i _ hT₀ ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨hcap, hnT, rfl⟩ := entN_fin_cancel hP'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' hwc).2 hq _ (entN_fin_of hcap hoT)
      show cancelOblN (ℍ := ℍ) _ _ k ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancelN hΘ P err o.fin hfin' hnT k ls'' _ ρk hcan τ₂ ρk'
        (errOkN_tabN_le hk he) (fun hu₁ => hu (finUnr_of_find hf (Or.inr ⟨hcap, hu₁⟩))) hk'
termination_by sizeOf G
decreasing_by exact rowOf_fin_lt G (Row.find_mem hf).1

/-- **A finaliser running under a cancel's `cfin`** (Core's `cfin_run`): `D` at the row `E`, the
cancel keeping an error of `P`, is a cancel run at any `T` that has `E`'s operations, their cancel
rows with `P`'s errors pending, and `P`'s errors. `D`'s answer gives `[cfin-ret]`; its raise is kept
unless an error already is (`[cfin-raise]`, the first wins); its operation passes the dead region to
a live handler, and a cancel of that continuation passes the `cfin` (`cfin_cancelN`). The error holds
nothing where `E` may stop at an unrestricted operation. -/
theorem cfin_runN {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life} (E P : Row)
    (err : Option Val) {T : CTy}
    (hE : ∀ n i o, Row.find E n i = some o → ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → PendLe P o.fin o'.fin))
    (hP : ∀ n i o, Row.find P n i = some o → o.abort = true →
      ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o')
    (hNZ : ∀ n i o, Row.find E n i = some o → o.n ≠ 0)
    {Qd : PostN} (hQd : ∀ k ls v ρ, Qd k ls v ρ → NoOwn ρ) :
    ∀ n ls d ρ, erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf E .unit) δ Θ c)) Qd
        n ls d ρ →
      ∀ σe ρ', errOkN (tabN₀ (ℍ := ℍ) (CTy.effOf P .unit) δ Θ c) n ls err σe →
        (E.UnrD → σe = PMap.empty) → ResU.CompS ρ σe ρ' →
        cancelOblN (ℍ := ℍ) (Θ.view c) (tabN₀ (ℍ := ℍ) T δ Θ c) n ls
          (cfinE (cancelVal err) d) ρ' := by
  have hΦ := LocTy.view_down hΘ c
  have hL := opTableN_local (tabN₀ (ℍ := ℍ) (CTy.effOf E .unit) δ Θ c)
  have hPD := erwpPost_down (cancelTabN_down (tabN_down T δ Θ hΘ c)) falsePost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls d ρ h σe ρ' he hu hc
  show erwp (ℍ := ℍ) _ _ _ _ _ ((cfinK (cancelVal err)).plug d) _
  rw [erwp_eq]
  refine rwpG_bind hΦ (cfinK _) ?_
  have hfr := rwpG_frame (fun _ τ => τ = σe) (fun _ _ _ _ h => h) hc
    (erwp_unfold_at hL le_rfl h) rfl
  refine rwpG_mono_le (fun k hk ls' t τ ⟨τ₁, τ₂, hcτ, hp, hτ₂⟩ => ?_) hfr
  subst hτ₂
  rcases hp with ⟨w, rfl, hw⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, j, w, en, hp⟩
  · -- the finaliser finished: the cancel goes on with its error
    refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.cfret μ err w) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal err))) :=
      final_opPlug (payloadName_cancelVal err) (by simp [OpFree, Kont.Catches])
    refine rwpG_here hfin (Or.inr (Or.inl ⟨.hole, err, pure_sep_mk ⟨rfl, rfl⟩
      ⟨τ₂, τ₁, ResU.CompS.comm hcτ, ?_, hQd _ _ _ _ hw⟩⟩))
    rw [tabN_rowOf]
    exact errOkN_of_sub hP (errOkN_tabN_le hk he)
  · -- an operation of the finaliser passes the dead region; the `cfin` joins its continuation
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hp
    have hT₀ := hTn
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hTn
    obtain ⟨o', hf', hs, hfin⟩ := hE m i o hf
    have hT' : tabN₀ (ℍ := ℍ) T δ Θ c m i = some (entN o.q o.B
        (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
        (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ)
        (finN₀ (ℍ := ℍ) o'.fin δ Θ c)) := by
      rw [tabN_rowOf]; exact tabN_find_sig hf' hs
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hKo : ((cfinK (cancelVal err)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    have ht' : (cfinK (cancelVal err)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((cfinK (cancelVal err)).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨(cfinK (cancelVal err)).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
        ⟨ρa, ρk', hcσ', hA, fun hq => ?_, fun ls'' hext =>
          ⟨fun k' hk'' w τ₃ τ₄ hB hcτ' => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq' : o.q = .unr := hq
      rw [hu' hq', hu (unr_of_find hf (Or.inl hq'))] at hk'
      exact eq_of_compS_empty_left hk'
    · have hwc := (tabN_down _ δ Θ hΘ c).wcl m i _ hT₀ ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont ls'' hwc).1 k' hk'' w τ₃ z hB hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) ls'' _ z h₁ τ₂ τ₄ (errOkN_tabN_le (by omega) he) hu hcz
    · have hwc := (tabN_down _ δ Θ hΘ c).wcl m i _ hT₀ ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨hcap, hnT, rfl⟩ := entN_fin_cancel hP'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' hwc).2 hq _ (entN_fin_of hcap hoT)
      show cancelOblN (ℍ := ℍ) _ _ k ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancelN hΘ P err o.fin hfin' hnT k ls'' _ ρk hcan τ₂ ρk'
        (errOkN_tabN_le hk he) (fun hu₁ => hu (unr_of_find hf (Or.inr ⟨hcap, hu₁⟩))) hk'
  · -- a raise of the finaliser: the first error is kept, and the cancel goes on
    obtain ⟨⟨rfl, hK₁, hTm, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hTm
    have hm : m ≠ 0 := by rw [← (Row.find_mem hf).2.1]; exact hNZ m j o hf
    refine rwpG_det hΦ (hPD _)
      (fun μ => step1Only_plug (Head.cferr μ err m j w K₁ hm hK₁) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ
        (Kont.hole.plug (opE true (cancelVal (errNext err m j w)))) :=
      final_opPlug (payloadName_cancelVal _) (by simp [OpFree, Kont.Catches])
    refine rwpG_here hfin (Or.inr (Or.inl ⟨.hole, errNext err m j w, pure_sep_mk ⟨rfl, rfl⟩ ?_⟩))
    have hnτ₁ : NoOwn τ₁ := noOwn_compS hcan hnA hnn
    cases err with
    | some E' =>
        refine ⟨τ₂, τ₁, ResU.CompS.comm hcτ, ?_, hnτ₁⟩
        rw [tabN_rowOf]
        exact errOkN_of_sub hP (errOkN_tabN_le hk he)
    | none =>
        have hτ₂ : τ₂ = PMap.empty := he.1
        subst hτ₂
        rw [eq_of_compS_empty_left (ResU.CompS.comm hcτ)]
        obtain ⟨o', hf', hs, -⟩ := hE m j o hf
        refine ⟨ρa, ρn, hcan, ⟨m, j, w, entN o.q o.B (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
          (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ) (finN₀ (ℍ := ℍ) o'.fin δ Θ c),
          pure_sep_mk ⟨rfl, ?_, ha⟩ ⟨hPA, hnA⟩⟩, hnn⟩
        rw [tabN_rowOf]; exact tabN_find_sig hf' hs

/-- **A kept error of a cancel row whose errors are persistent holds nothing** (Core's
`errOk_empty_of_pers`). -/
theorem errOkN_empty_of_pers {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {F : CTy}
    (hF : F.FinPers) {k : Nat} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes},
      errOkN (tabN₀ (ℍ := ℍ) (CTy.effOf F.rowOf .unit) δ Θ c) k ls err ρ → ρ = PMap.empty
  | none, _, h => h.1
  | some _, _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨-, hT, ha⟩, hA, -⟩ := pure_sep_iff.mp h
      obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
      have ha' : o.abort = true := by simpa [entN, OpSig.abort] using ha
      exact vN_empty_of_persistent₀ _ ((finPers_of_mem hF (Row.find_mem hf).1).1 ha') hA

/-! ### A cancel run through the finaliser frame -/

/-- **A cancel run through a finaliser frame** (`ubind (N, D) [·]`, Core's `then_cancel`), by
recursion on the cancel row `F` below it and, inside, induction on the index: at the cancel's end
`[finalise-cancel]` runs `D` under `cfin` (`cfin_runN`), with `F`'s errors pending; at an operation
below `D`, the frame joins its continuation, whose own cancel passes the frame and fires `D` too.
So the run is at any `T ≥ F ⋈ E` that is not `⊤`. The frame `Fr`, which `D` consumes, holds nothing
where `T` may stop at an unrestricted operation; `F`'s errors hold nothing where `E` may. `D` is owed
up to the index `N₀`. The frame is read at the record list, as Core's is, and carried along the
continuations' `extF` (`hFe`). -/
theorem then_cancelN {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life} (E : Row)
    (hNZ : ∀ n i o, Row.find E n i = some o → o.n ≠ 0) (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, Fr ls ρ → Fr ls' ρ)
    (hFe : ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → extF ls ls' ρ' → Fr ls σ → Fr ls' σ)
    {Qd : PostN} (hQd : ∀ k ls v ρ, Qd k ls v ρ → NoOwn ρ) (N₀ : Nat)
    (hD : ∀ k, k ≤ N₀ → ∀ ls ρ, Fr ls ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf E .unit) δ Θ c)) Qd k ls
        (.app (.val Dv) (.val .unit)) ρ)
    (F : CTy) : ∀ {T : CTy}, ThenLe F E T → T.isTop = false →
      (T.FinUnr → ∀ ls σ, Fr ls σ → σ = PMap.empty) → (E.UnrD → F.FinPers) →
      ∀ n, n ≤ N₀ → ∀ ls e ρ, cancelOblN (ℍ := ℍ) (Θ.view c) (tabN₀ (ℍ := ℍ) F δ Θ c) n ls e ρ →
        ∀ σ ρ', Fr ls σ → ResU.CompS ρ σ ρ' →
          cancelOblN (ℍ := ℍ) (Θ.view c) (tabN₀ (ℍ := ℍ) T δ Θ c) n ls
            ((ubindK Nv Dv).plug e) ρ' := by
  intro T hle hT hunr hpers
  rw [ThenLe, hT] at hle
  obtain ⟨-, hFT, hET⟩ := hle.resolve_left (by simp)
  have hΦ := LocTy.view_down hΘ c
  have hL := cancelTabN_local (tabN₀ (ℍ := ℍ) F δ Θ c)
  have hPD := erwpPost_down (cancelTabN_down (tabN_down T δ Θ hΘ c)) falsePost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h σ ρ' hF hc
  show erwp (ℍ := ℍ) _ _ _ _ _ _ _
  rw [erwp_eq]
  refine rwpG_bind hΦ (ubindK Nv Dv) ?_
  have hfr := rwpG_frame Fr hFs hc (erwp_unfold_at hL le_rfl h) hF
  refine rwpG_mono_le (fun k hk ls' t τ ⟨τ₁, τ₂, hcτ, hp, hF₂⟩ => ?_) hfr
  rcases hp with ⟨_, _, hv⟩ | ⟨K₀, err, hs'⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact hv.elim
  · -- the cancel reaches the frame: `D` runs under `cfin`
    obtain ⟨⟨rfl, hK₀⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    refine rwpG_det hΦ (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ Nv Dv err K₀ hK₀) rfl .hole) ?_
    obtain ⟨z, hz, hcz⟩ := compS_exch hcab hcτ
    refine erwp_unfold_at (cancelTabN_local _) hk (erwp_garbage hcz hnb ?_)
    rw [tabN_rowOf] at he
    exact cfin_runN hΘ E F.rowOf err (T := T) hET (fun n i o hf _ => by
        obtain ⟨o', hf', hs, -⟩ := hFT n i o hf; exact ⟨o', hf', hs⟩) hNZ hQd k ls' _ τ₂
      (hD k (by omega) ls' τ₂ hF₂) τa z he (fun hu => errOkN_empty_of_pers (hpers hu) he)
      (ResU.CompS.comm hz)
  · -- an operation below the frame: the frame joins its continuation
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hp
    have hT₀ := hTn
    obtain ⟨o, hf, rfl⟩ := tabN_rowOf_find hTn
    obtain ⟨o', hf', hs, hfin⟩ := hFT m i o hf
    have hT' : tabN₀ (ℍ := ℍ) T δ Θ c m i = some (entN o.q o.B
        (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
        (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ)
        (finN₀ (ℍ := ℍ) o'.fin δ Θ c)) := by
      rw [tabN_rowOf]; exact tabN_find_sig hf' hs
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hKo : ((ubindK Nv Dv).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    have ht' : (ubindK Nv Dv).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubindK Nv Dv).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨(ubindK Nv Dv).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
        ⟨ρa, ρk', hcσ', hA, fun hq => ?_, fun ls'' hext =>
          ⟨fun k' hk'' w τ₃ τ₄ hB hcτ' => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq₀ : o.q = .unr := hq
      have hq' : o'.q = .unr := by rw [← hs.2.2.1]; exact hq₀
      rw [hu' hq₀, hunr (finUnr_of_find hf' (Or.inl hq')) ls' τ₂ hF₂] at hk'
      exact eq_of_compS_empty_left hk'
    · have hwc := (tabN_down F δ Θ hΘ c).wcl m i _ hT₀ ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont ls'' hwc).1 k' hk'' w τ₃ z hB hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) (by omega) ls'' _ z h₁ τ₂ τ₄ (hFe ls' ls'' ρk τ₂ ρk' hk' hext hF₂)
        hcz
    · have hwc := (tabN_down F δ Θ hΘ c).wcl m i _ hT₀ ls' ls'' ρk τ₂ ρk' hk' hext
      obtain ⟨hcap, hnT, rfl⟩ := entN_fin_cancel hP'
      have hcap' : capB o'.q o'.B = true := hs.capB_eq ▸ hcap
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' hwc).2 hq _ (entN_fin_of hcap hoT)
      show cancelOblN (ℍ := ℍ) _ _ k ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancelN hΘ E hNZ Nv Dv Fr hFs hFe hQd N₀ hD o.fin hfin' hnT
        (fun hu₁ => hunr (finUnr_of_find hf' (Or.inr ⟨hcap', hu₁⟩)))
        (fun hu₁ => (finPers_of_mem (hpers hu₁) (Row.find_mem hf).1).2 hcap) k (by omega) ls''
        _ ρk hcan τ₂ ρk' (hFe ls' ls'' ρk τ₂ ρk' hk' hext hF₂) hk'
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem hf).1

/-! ### The finaliser frame -/

/-- The entry `Σ′` has at the key of an operation of `Σ ≤ Σ′`, and the entries' order. -/
theorem tabN_rowLe_entry {S S' : Row} (hle : RowLe S S') {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {n i : UInt32} {o : OpSig} (hf : Row.find S n i = some o) :
    ∃ o', Row.find S' n i = some o' ∧ o.Sig o' ∧
      tabN₀ (ℍ := ℍ) (CTy.effOf S' .unit) δ Θ c n i = some (entN o'.q o'.B
        (fun k v ρ => vN₀ (ℍ := ℍ) o'.A δ Θ k v ρ)
        (fun k v ρ => vN₀ (ℍ := ℍ) o'.B δ Θ k v ρ ∧ ConsistentX c ρ)
        (finN₀ (ℍ := ℍ) o'.fin δ Θ c)) ∧
      (entN o.q o.B (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
        (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ)
        (finN₀ (ℍ := ℍ) o.fin δ Θ c)).Le (entN o'.q o'.B
        (fun k v ρ => vN₀ (ℍ := ℍ) o'.A δ Θ k v ρ)
        (fun k v ρ => vN₀ (ℍ := ℍ) o'.B δ Θ k v ρ ∧ ConsistentX c ρ)
        (finN₀ (ℍ := ℍ) o'.fin δ Θ c)) := by
  obtain ⟨o', hf', hs, hfl⟩ := hle n i o hf
  exact ⟨o', hf', hs, by rw [tabN_effOf_find, hf']; rfl, entN_le_of_leF hs fun hcap =>
    finN_mono δ Θ c o.fin (hfl (by simp [OpSig.finRead, hcap]))⟩

/-- **A finaliser under ordinary unwinding** (Core's `seq_raise_run`): `D (); raise p`, `D` at a
row `E ≤ Σ`, the pending raise's argument holding nothing where `E` may stop at an unrestricted
operation. `D`'s answer lets the raise go on; `D`'s raise supersedes it; `D`'s operation keeps it in
its continuation, whose cancel passes it as a plain frame (`entN_plain`). -/
theorem seq_raise_runN {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life} (S E : Row)
    (hES : RowLe E S) {n i : UInt32} {v : Val} {o : OpSig} (hfo : Row.find S n i = some o)
    (ha : o.abort = true) {Qd : PostN} (hQd : ∀ k ls v ρ, Qd k ls v ρ → v = .unit ∧ NoOwn ρ)
    {Q : PostN} (hQ : Q.Down) :
    ∀ k ls d ρ, erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf E .unit) δ Θ c)) Qd
        k ls d ρ →
      ∀ σp ρ', (vN₀ (ℍ := ℍ) o.A δ Θ k v σp ∧ NoOwn σp) → (E.UnrD → σp = PMap.empty) →
        ResU.CompS ρ σp ρ' →
        erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c)) Q k ls
          (.seq d (raiseE (.val (opPayload n i v)))) ρ' := by
  have hΦ := LocTy.view_down hΘ c
  have hL := opTableN_local (tabN₀ (ℍ := ℍ) (CTy.effOf E .unit) δ Θ c)
  have hLS := opTableN_local (tabN₀ (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c)
  have hPD := erwpPost_down (opTableN_down (tabN_down (CTy.effOf S .unit) δ Θ hΘ c)) hQ
  have hTn : tabN₀ (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c n i = some (entN o.q o.B
      (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ) (finN₀ (ℍ := ℍ) o.fin δ Θ c)) := by
    rw [tabN_effOf_find, hfo]; rfl
  have ha' : (entN o.q o.B (fun k v ρ => vN₀ (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN₀ (ℍ := ℍ) o.B δ Θ k v ρ ∧ ConsistentX c ρ)
      (finN₀ (ℍ := ℍ) o.fin δ Θ c)).abort = true := by simpa [entN, OpSig.abort] using ha
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ls d ρ h σp ρ' hp hu hc
  show erwp (ℍ := ℍ) _ _ _ _ _ ((seqRaiseK (opPayload n i v)).plug d) _
  rw [erwp_eq]
  refine rwpG_bind hΦ (seqRaiseK (opPayload n i v)) ?_
  have hfr := rwpG_frame (fun _ τ => τ = σp) (fun _ _ _ _ h => h) hc
    (erwp_unfold_at hL le_rfl h) rfl
  refine rwpG_mono_le (fun k₁ hk₁ ls' t τ ⟨τ₁, τ₂, hcτ, hq, hτ₂⟩ => ?_) hfr
  subst hτ₂
  have hp' : vN₀ (ℍ := ℍ) o.A δ Θ k₁ v τ₂ ∧ NoOwn τ₂ := ⟨vN_le₀ hk₁ hp.1, hp.2⟩
  rcases hq with ⟨w, rfl, hw⟩ | ⟨K₁, m, j, w, en₁, hq⟩ | ⟨K₁, m, j, w, en₁, hq⟩
  · -- the finaliser finished: the raise goes on
    obtain ⟨rfl, hnw⟩ := hQd _ _ _ _ hw
    refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload n i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, n, i, v, _,
        pure_sep_mk ⟨rfl, rfl, hTn, ha'⟩ ⟨τ₂, τ₁, ResU.CompS.comm hcτ, hp', hnw⟩⟩))
  · -- an operation of the finaliser: the pending raise joins its continuation
    obtain ⟨⟨rfl, hK₁, hTm, ha₁⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hq
    have hTm₀ := hTm
    obtain ⟨o₁, hf₁, rfl⟩ := tabN_effOf_some_find hTm
    obtain ⟨o₁', -, hs, hT', hLe⟩ := tabN_rowLe_entry (δ := δ) (Θ := Θ) (c := c) hES hf₁
    obtain ⟨hLq, hLa, hLA, hLB, hLw, hLf⟩ := hLe
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hKo : ((seqRaiseK (opPayload n i v)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; rfl
    have ht' : (seqRaiseK (opPayload n i v)).plug (K₁.plug (performE (.val (opPayload m j w)))) =
        ((seqRaiseK (opPayload n i v)).comp K₁).plug (opE false (opPayload m j w)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m j w) hKo) (Or.inr (Or.inl
      ⟨(seqRaiseK (opPayload n i v)).comp K₁, m, j, w, _, pure_sep_mk ⟨rfl, hKo, hT',
        hLa ▸ ha₁⟩ ⟨ρa, ρk', hcσ', hLA ▸ hA, fun hq' => ?_, fun ls'' hext =>
          ⟨fun k' hk'' w' τ₃ τ₄ hB hcτ' => ?_, fun hq' P' hP' => ?_⟩⟩⟩))
    · rw [hu' (hLq.trans hq'), hu (unr_of_find hf₁ (Or.inl (hLq.trans hq')))] at hk'
      exact eq_of_compS_empty_left hk'
    · have hwc := (tabN_down _ δ Θ hΘ c).wcl m j _ hTm₀ ls' ls'' ρk τ₂ ρk' hk' (hLw ▸ hext)
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont ls'' hwc).1 k' hk'' w' τ₃ z (hLB ▸ hB) hz
      simp only [erwpC, show k' < k by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) ls'' _ z h₁ τ₂ τ₄ ⟨vN_le₀ (by omega) hp'.1, hp'.2⟩ hu hcz
    · have hwc := (tabN_down _ δ Θ hΘ c).wcl m j _ hTm₀ ls' ls'' ρk τ₂ ρk' hk' (hLw ▸ hext)
      have hq₁ : (entN o₁.q o₁.B (fun k v ρ => vN₀ (ℍ := ℍ) o₁.A δ Θ k v ρ)
          (fun k v ρ => vN₀ (ℍ := ℍ) o₁.B δ Θ k v ρ ∧ ConsistentX c ρ)
          (finN₀ (ℍ := ℍ) o₁.fin δ Θ c)).q ≠ .lin := hLq ▸ hq'
      have hplain := entN_plain hΦ (seqRaiseK (opPayload n i v)) (seqRaiseK_hasHnd _)
        (seqRaiseK_catches _ 0) hp'.2 o₁ (fun P₀ hP₀ => (hcont ls'' hwc).2 hq₁ P₀ hP₀) hk'
      exact finLeSN_apply (hLf ha₁ hq₁) hP' (fun P₀ hP₀ => hplain P₀ hP₀)
  · -- a raise of the finaliser supersedes the pending one
    obtain ⟨⟨rfl, hK₁, hTm, ha₁⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hq
    obtain ⟨o₁, hf₁, rfl⟩ := tabN_effOf_some_find hTm
    obtain ⟨o₁', -, hs, hT', hLe⟩ := tabN_rowLe_entry (δ := δ) (Θ := Θ) (c := c) hES hf₁
    obtain ⟨-, hLa, hLA, -, -, -⟩ := hLe
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

/-- **The finaliser frame around an effectful computation** (`M then x. N unwind D`, Core's
`ewp_frame_then_or` with no table beside), at the rows of `[then]`: `M` at `Σ_M ≤ Σ`, `D` at
`Σ_D ≤ Σ`, each capturable operation's cancel row `Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`. A stop of `M` at an
operation keeps the frame in its continuation; its cancel passes the frame and fires `D`
(`then_cancelN`). An abortive stop runs `D` first (`[finalise]`, `seq_raise_runN`). The frame,
which `D` consumes, holds nothing where `Σ` may stop at an unrestricted operation; a pending error
holds nothing where `Σ_D` may. `D` and the continuation are owed up to the index `N₀`. The frame
is read at the record list, as Core's is, and carried along the continuations' `extF` (`hFe`). -/
theorem erwp_frame_then {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life}
    (S SM SD : Row) (hNZ : S.NZ) (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, Fr ls ρ → Fr ls' ρ)
    (hFe : ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → extF ls ls' ρ' → Fr ls σ → Fr ls' σ)
    (hU : S.UnrD → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    {Qd : PostN} (hQd : ∀ k ls v ρ, Qd k ls v ρ → v = .unit ∧ NoOwn ρ) (N₀ : Nat)
    (hD : ∀ k, k ≤ N₀ → ∀ ls ρ, Fr ls ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf SD .unit) δ Θ c)) Qd k ls
        (.app (.val Dv) (.val .unit)) ρ)
    (Q₁ Q : PostN) (hQ : Q.Down)
    (hkv : ∀ k, k ≤ N₀ → ∀ ls (v : Val) ρ, (Q₁ k ls v ⋆ Fr ls) ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c)) Q k ls
        ((ubindK Nv Dv).plug (.val v)) ρ) :
    ∀ n, n ≤ N₀ → ∀ ls e ρ,
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf SM .unit) δ Θ c)) Q₁ n ls e ρ →
      ∀ ρ₂ ρ', Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c)) Q n ls
          ((ubindK Nv Dv).plug e) ρ' := by
  have hΦ := LocTy.view_down hΘ c
  have hL := opTableN_local (tabN₀ (ℍ := ℍ) (CTy.effOf SM .unit) δ Θ c)
  have hLS := opTableN_local (tabN₀ (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c)
  have hPD := erwpPost_down (opTableN_down (tabN_down (CTy.effOf S .unit) δ Θ hΘ c)) hQ
  have hNZD : ∀ n i o, Row.find SD n i = some o → o.n ≠ 0 := by
    intro n i o hf
    obtain ⟨o', hf', hle⟩ := hDS n i o hf
    rw [hle.1.1]; exact hNZ o' (Row.find_mem hf').1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h ρ₂ ρ' hF hc
  rw [erwp_eq] at h ⊢
  refine rwpG_bind hΦ (ubindK Nv Dv) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hcσ, hp, hF'⟩ => ?_)
    (rwpG_frame Fr hFs hc h hF)
  rcases hp with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact erwp_unfold_at hLS hk (hkv k (by omega) ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  · -- a `perform`: the frame joins the continuation's share; its cancel fires `D`
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hTn₀ := hTn
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hTn
    obtain ⟨o', hf', hs, hT', hLe⟩ := tabN_rowLe_entry (δ := δ) (Θ := Θ) (c := c) hMS hf
    obtain ⟨hLq, hLa, hLA, hLB, hLw, -⟩ := hLe
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    have hKo : ((ubindK Nv Dv).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    have ht' : (ubindK Nv Dv).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubindK Nv Dv).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubindK Nv Dv).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT', hLa ▸ ha⟩
        ⟨ρa, ρk', hcσ', hLA ▸ hA, fun hq => ?_, fun ls'' hext =>
          ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_, fun hq P' hP' => ?_⟩⟩⟩))
    · have hq' : o.q = .unr := hLq.trans hq
      rw [hu hq', hU ⟨o', (Row.find_mem hf').1, Or.inl hq⟩ ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · have hwc := (tabN_down _ δ Θ hΘ c).wcl m i _ hTn₀ ls' ls'' ρk σ₂ ρk' hk' (hLw ▸ hext)
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont ls'' hwc).1 k' hk'' w τ₁ z (hLB ▸ hB) hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) (by omega) ls'' _ z h₁ σ₂ τ₂
        (hFe ls' ls'' ρk σ₂ ρk' hk' hext hF') hcz
    · have hwc := (tabN_down _ δ Θ hΘ c).wcl m i _ hTn₀ ls' ls'' ρk σ₂ ρk' hk' (hLw ▸ hext)
      obtain ⟨hcap', hnT, rfl⟩ := entN_fin_cancel hP'
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hth := hfin m i o o' hf hf' hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hth
        exact (hth.resolve_left (by simp)).1
      have hcan := (hcont ls'' hwc).2 (hLq ▸ hq) _ (entN_fin_of hcap hoT)
      show cancelOblN (ℍ := ℍ) _ _ k ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancelN hΘ SD hNZD Nv Dv Fr hFs hFe (fun _ _ _ _ h => (hQd _ _ _ _ h).2) N₀ hD
        o.fin hth hnT (fun hu₁ => hU ⟨o', (Row.find_mem hf').1, Or.inr ⟨hcap', hu₁⟩⟩)
        (fun hu₁ => ((hP hu₁) o (Row.find_mem hf).1).2 hcap) k (by omega) ls'' _ ρk hcan σ₂ ρk'
        (hFe ls' ls'' ρk σ₂ ρk' hk' hext hF') hk'
  · -- a `raise`: the finaliser runs, then the `raise` goes on
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hTn
    obtain ⟨o', hf', hs, -, -⟩ := tabN_rowLe_entry (δ := δ) (Θ := Θ) (c := c) hMS hf
    have hao : o.abort = true := by simpa [entN, OpSig.abort] using ha
    have hn0 : m ≠ 0 := by
      rw [← (Row.find_mem hf).2.1, hs.1]; exact hNZ o' (Row.find_mem hf').1
    refine rwpG_det hΦ (hPD _)
      (fun μ => step1Only_plug (Head.ufin μ Nv Dv m i v K₁ hn0 hK₁) rfl .hole) ?_
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcσ
    obtain ⟨y, hy, hcy⟩ := compS_lcomm hz hcz
    refine erwp_unfold_at hLS hk (erwp_garbage (ResU.CompS.comm hcy) hn ?_)
    have hPA' : vN₀ (ℍ := ℍ) o'.A δ Θ k v ρa := by rw [← hs.2.2.2.1]; exact hPA
    exact seq_raise_runN hΘ S SD hDS hf' (by rw [← hs.abort_eq]; exact hao) hQd hQ k ls' _ σ₂
      (hD k (by omega) ls' σ₂ hF') ρa y ⟨hPA', hnA⟩
      (fun hu => vN_empty_of_persistent₀ _ (((hP hu) o (Row.find_mem hf).1).1 hao) hPA)
      (ResU.CompS.comm hy)

/-! ### The rules -/

/-- **`[then]` at `SemJN₀`** (Core's `then_compatC`): `M then x. N unwind D` at `Σ`, `M` at
`Σ_M ≤ Σ`, the finaliser at `Σ_D ≤ Σ`, each capturable operation of `Σ_M` with
`Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`, the errors pending at the finaliser persistent where `Σ_D` has an
unrestricted operation. `erwp_frame_then` around `M`, the frame the context of `N` and `D`
consistent with the view; `M`'s value consistent with the view across its resumptions
(`erwp_consistentAns`), so `N` is read at the view from the value beside the frame. -/
theorem then_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy}
    {S SM SD : Row} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers)
    (hM : SemJN₀ (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf SM A)))
    (hN : SemJN₀ (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : SemJN₀ (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have hΦ := LocTy.view_down hΘ.1 c
  refine (cN_effOf₀ S B δ Θ c n ls _ ρ).mpr (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, hc₂⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hM' := (cN_effOf₀ SM A δ Θ c n ls _ ρ₁).mp (hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁)
  rw [tabN_effOf_ret SM A .unit] at hM'
  have hM'' := erwp_consistentAns (tabN_ansC _ δ Θ c) n n le_rfl ls _ ρ₁ hM' hc₁
  have hQd : ∀ (k : Nat) (ls : List SRec) (v : Val) (ρ : WRes),
      vN₀ (ℍ := ℍ) .unit δ Θ k v ρ → v = .unit ∧ NoOwn ρ := by
    rintro k ls' v σ ⟨rfl, rfl⟩
    exact ⟨rfl, noOwn_empty⟩
  -- the finaliser, from the frame
  have hD' : ∀ k, k ≤ n → ∀ ls' σ, (gN₀ (ℍ := ℍ) δ Θ Γ₂ γ n σ ∧ ConsistentX c σ) →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf SD .unit) δ Θ c))
        (fun k _ v ρ => vN₀ (ℍ := ℍ) .unit δ Θ k v ρ) k ls'
        (.app (.val (Val.lam (Expr.psub 1 γ D))) (.val .unit)) σ := by
    rintro k hk ls' σ ⟨hσ, hcσ⟩
    refine erwp_det hΦ (opTableN_down (tabN_down _ δ Θ hΘ.1 c))
      (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h)
      (fun μ => step1Only_plug (Head.beta μ (Expr.psub 1 γ D) Val.unit) rfl .hole) ?_
    rw [show Kont.hole.plug (Expr.subst 0 Val.unit (Expr.psub 1 γ D)) =
      substAll (Val.unit :: γ) D from (substAll_cons_psub Val.unit γ D).symm]
    exact (cN_effOf₀ SD .unit δ Θ c k ls' _ σ).mp
      (hD δ (Val.unit :: γ) Θ c k ls' σ hδ hΘ hcσ hlw₂ (gN_dead_cons .unit Val.unit (gN_le hk hσ)))
  -- the continuation, from the value beside the frame
  have hk : ∀ k, k ≤ n → ∀ ls' (v : Val) σ, ((fun (k : Nat) (_ : List SRec) (v : Val) (ρ : WRes) => k ≤ n ∧
      vN₀ (ℍ := ℍ) A δ Θ k v ρ ∧ ConsistentX c ρ ∧ ResU.Valid ρ) k ls' v ⋆
        fun σ => gN₀ (ℍ := ℍ) δ Θ Γ₂ γ n σ ∧ ConsistentX c σ) σ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN₀ (ℍ := ℍ) (CTy.effOf S .unit) δ Θ c))
        (fun k _ v ρ => vN₀ (ℍ := ℍ) B δ Θ k v ρ) k ls'
        ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug (.val v)) σ := by
    rintro k hk ls' v σ ⟨σ₁, σ₂, hcσ, ⟨-, hv, hcv, -⟩, hg₂', hc₂'⟩
    have hTd := opTableN_down (tabN_down (CTy.effOf S .unit) δ Θ hΘ.1 c)
    have hQ : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) B δ Θ k v ρ) :=
      fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h
    refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.uthen μ _ _ v) rfl .hole) ?_
    refine erwp_det hΦ hTd hQ
      (fun μ => step1Only_plug (Head.beta μ (Expr.psub 1 γ N) v) rfl .hole) ?_
    rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
      from (substAll_cons_psub v γ N).symm]
    have h₁ := (cN_effOf₀ S B δ Θ c k ls' _ σ).mp
      (hN δ (v :: γ) Θ c k ls' σ hδ hΘ (consistentX_compS hcσ hcv hc₂') hlw₂
        (gN_live_cons hcσ hv (gN_le hk hg₂')))
    rwa [tabN_effOf_ret S B .unit] at h₁
  change erwp (ℍ := ℍ) _ _ _ n ls
    ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug (substAll γ M)) ρ
  rw [tabN_effOf_ret S B .unit]
  exact erwp_frame_then hΘ.1 S SM SD hNZ hMS hDS hfin hP _ _
    (fun _ σ => gN₀ (ℍ := ℍ) δ Θ Γ₂ γ n σ ∧ ConsistentX c σ) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ h => h) (fun hu _ σ h => gN_persistent (hU hu) h.1) hQd n hD' _ _
    (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h) hk n le_rfl ls _ ρ₁ hM'' ρ₂ ρ ⟨hg₂, hc₂⟩ hcρ

/-- **`[then]` with a finaliser that may loop** (Core's `then_compatC_div`): `M`'s row has no
capturable operation (`hcap`), so `then_compatN`'s cancel-row record holds of no operation. A
`Div` row is a row of the chain's table (E13), so the finaliser's row holding `Div` reads as any
other row: Core's split of `[then]` at `cwp` (`cwp_then_div`) has no counterpart, and this is
`then_compatN`. -/
theorem thenDiv_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy}
    {S SM SD : Row} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hP : SD.UnrD → SM.PendPers) (hcap : ∀ o ∈ SM, capB o.q o.B = false)
    (hM : SemJN₀ (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf SM A)))
    (hN : SemJN₀ (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : SemJN₀ (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit))) :
    SemJN₀ (ℍ := ℍ) Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  then_compatN hsp hNZ hU hMS hDS (fun _ _ o _ hf _ h => by
    rw [hcap o (Row.find_mem hf).1] at h; cases h) hP hM hN hD

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
