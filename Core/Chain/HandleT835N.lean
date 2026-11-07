import Core.Chain.Then835N
import Core.DivHandleLast

/-!
# `[handle]` at clauses that resume `κ` in tail position  `[spec §14, §19]`

Core's `handleT_compatC` (`Core/DivHandle.lean`) at `SemJN₀`, its proof `ewp_handle_tail` at `erwp`
(the tail instance, `scope-831-interface.md` §10.5), each step Core's:

* `erwp_frame_plain_or` (Core's `ewp_frame_plain_or` with no table beside, by E13): a plain frame
  around a computation at a table `T` below the outer `T′`; the frame's conditions are read at `T`'s
  entries only;
* `tabN_ofEff_ne`, `tabN_ofEff_self`, `capTag_ofEffN` (Core's `Row.tab_ofEff_ne`,
  `Row.tab_ofEff_self`, `capTag_ofEff`): the split of the handled row's table;
* `ansesTy_atN₀` (Core's `ansesTy_at`): the answering functions read at `vN₀`;
* `erwp_handle_tail₀` (Core's `ewp_handle_tail`): `erwp_handle` with a clause running its answering
  function at its must-resume row under the resume frame `resK κ`; the clause's `β` step is paid
  (`erwp_step`), so the answering function's run returns below the stop's index, where `κ` is owed;
* `handleT_compatN₀` (Core's `handleT_compatC`).

Two readings the chain adds, each where `SemJN₀` reads a run at its view (D7):

* **the answers.** The answer `κ` is resumed at is the answering function's value, consistent with
  the view across that run's resumptions (`erwp_consistentAns`, `tabN_ansC`): the reading of
  §10.2 is met there;
* **the arguments.** An answering function and `h_ret` are typed code; `⊸` reads its argument at a
  view consistent with it. The handled run starts consistent with the view, so its stops and its
  value are (`rwpG_consistentXV`): `erwp_consistentPA` moves the run to the table whose entries of
  the handler's name carry that consistency in their payload (`OpTabN.withPA`), and
  `erwp_handle` reads the clauses there.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal clauseAt capTag)

/-! ### A plain frame from a table below -/

/-- **A plain frame around an effectful computation, from a table below** (Core's
`ewp_frame_plain_or` with no table beside: a `Div` row is a row of the chain's table, E13). The
computation runs at `T ≤ T′`; its stops are stops of `T′` with the frame in the continuation. The
frame's conditions are asked at `T`'s entries only. -/
theorem erwp_frame_plain_or {Φ : LocFam} (hΦ : Φ.Down) (T T' : OpTabN) (hTT : T.Le T')
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false)
    (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, Fr ls ρ → Fr ls' ρ)
    (hwl : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      en.wc ls ls' ρ)
    (hFe : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      Fr ls σ → Fr ls' σ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ k ls K₁ ρ σ ρ', cancelOKN en k ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOKN en k ls (K.comp K₁) ρ')
    (Q₁ Q : PostN)
    (hkv : ∀ k ls (v : Val) ρ, (Q₁ k ls v ⋆ Fr ls) ρ →
      erwp (ℍ := ℍ) Φ (opTableN T') Q k ls (K.plug v.1) ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q₁ n ls e ρ →
      ∀ ρ₂ ρ', Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwp (ℍ := ℍ) Φ (opTableN T') Q n ls (K.plug e) ρ' := by
  have hL' := opTableN_local T'
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h ρ₂ ρ' hF hc
  rw [erwp_eq] at h ⊢
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hcσ, hp, hF'⟩ => ?_)
    (rwpG_frame Fr hFs hc h hF)
  rcases hp with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact erwp_unfold_at hL' hk (hkv k ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  · -- a `perform`: the frame joins the continuation's share, at the entry above
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    obtain ⟨en', hT', hq, hab, hPA, hPB, hwc, hfl⟩ := hTT m i en hT
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', hab ▸ ha⟩ ⟨ρa, ρk', hcσ',
        hPA ▸ hA, fun hq' => ?_, fun ls'' he => ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' P hP => ?_⟩⟩⟩))
    · rw [hu (hq.trans hq'), hU m i en hT (hq.trans hq') ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · rw [← hwc] at he
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont ls'' (hwl m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).1 k' hk'' w τ₁ z
        (hPB ▸ hB) hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) ls'' _ z h₁ σ₂ τ₂ (hFe m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF') hcz
    · rw [← hwc] at he
      have hq'' : en.q ≠ .lin := hq ▸ hq'
      exact finLeSN_apply (hfl ha hq'') hP (fun P₀ hP₀ => hK m i en hT ha hq'' k ls'' K₁ ρk σ₂ ρk'
        (fun P₁ hP₁ => (hcont ls'' (hwl m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).2 hq'' P₁ hP₁)
        (hFe m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF') hk' P₀ hP₀)
  · -- a `raise`: the frame is left behind
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨ρn', hn', hcσ'⟩ := compS_reassoc hcan hcσ
    obtain ⟨en', hT', -, hab, hPA', -⟩ := hTT m i en hT
    have hKo : (K.comp K₁).Catches m = false := by rw [catches_comp, hC, hK₁]; rfl
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', hab ▸ ha⟩ ⟨ρa, ρn', hcσ',
        ⟨hPA' ▸ hPA, hnA⟩, noOwn_compS hn' hn (hW m i en hT ha ls' σ₂ hF')⟩⟩))

/-! ### The payloads at the handler's name, read at the view -/

/-- An entry whose payload is read at the view `c`. -/
def OpEntN.withPA (c : Loc → Option Life) (en : OpEntN) : OpEntN :=
  { en with PA := fun k ls v ρ => en.PA k ls v ρ ∧ ConsistentX c ρ }

/-- **The table whose entries of the name `n₀` read their payloads at the view `c`.** -/
def OpTabN.withPA (c : Loc → Option Life) (n₀ : UInt32) (T : OpTabN) : OpTabN :=
  fun m i => if m = n₀ then (T m i).map (OpEntN.withPA c) else T m i

theorem OpTabN.withPA_ne {c : Loc → Option Life} {n₀ m : UInt32} (T : OpTabN) (hm : m ≠ n₀)
    (i : UInt32) : T.withPA c n₀ m i = T m i := by
  simp [OpTabN.withPA, hm]

theorem OpTabN.withPA_self {c : Loc → Option Life} {n₀ : UInt32} {T : OpTabN} {i : UInt32}
    {en' : OpEntN} (h : T.withPA c n₀ n₀ i = some en') :
    ∃ en, T n₀ i = some en ∧ en' = en.withPA c := by
  simp only [OpTabN.withPA, if_true] at h
  obtain ⟨en, hT, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨en, hT, rfl⟩

/-- An entry of `T.withPA c n₀` is an entry of `T` with its payload read at `c`, or `T`'s own. -/
theorem OpTabN.withPA_some {c : Loc → Option Life} {n₀ : UInt32} {T : OpTabN} {m i : UInt32}
    {en : OpEntN} (h : T m i = some en) :
    ∃ en', T.withPA c n₀ m i = some en' ∧ en'.q = en.q ∧ en'.abort = en.abort ∧
      en'.PB = en.PB ∧ en'.fin = en.fin ∧ en'.wc = en.wc ∧
      ∀ k ls v ρ, en.PA k ls v ρ → ConsistentX c ρ → en'.PA k ls v ρ := by
  by_cases hm : m = n₀
  · subst hm
    exact ⟨en.withPA c, by simp [OpTabN.withPA, h], rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ _ h₁ h₂ => ⟨h₁, h₂⟩⟩
  · exact ⟨en, by rw [OpTabN.withPA_ne T hm, h], rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ h _ => h⟩

theorem OpTabN.withPA_down {c : Loc → Option Life} {n₀ : UInt32} {T : OpTabN} (hT : T.Down) :
    (T.withPA c n₀).Down where
  pa := fun m i en h k ls v ρ hp => by
    by_cases hm : m = n₀
    · subst hm
      obtain ⟨en₀, hT₀, rfl⟩ := OpTabN.withPA_self h
      exact ⟨hT.pa _ _ _ hT₀ k ls v ρ hp.1, hp.2⟩
    · rw [OpTabN.withPA_ne T hm] at h
      exact hT.pa _ _ _ h k ls v ρ hp
  fin := fun m i en P h hP k ls e ρ hp => by
    by_cases hm : m = n₀
    · subst hm
      obtain ⟨en₀, hT₀, rfl⟩ := OpTabN.withPA_self h
      exact hT.fin _ _ _ _ hT₀ hP k ls e ρ hp
    · rw [OpTabN.withPA_ne T hm] at h
      exact hT.fin _ _ _ _ h hP k ls e ρ hp
  wcl := fun m i en h => by
    by_cases hm : m = n₀
    · subst hm
      obtain ⟨en₀, hT₀, rfl⟩ := OpTabN.withPA_self h
      exact fun ls ls' ρ₁ ρ₂ ρ hc hw => hT.wcl _ _ _ hT₀ ls ls' ρ₁ ρ₂ ρ hc hw
    · rw [OpTabN.withPA_ne T hm] at h
      exact hT.wcl _ _ _ h

/-- **A run from a consistent resource, at a table whose answers are consistent, is a run at the
table whose payloads of the name `n₀` are read at the view**, returning consistent resources. The
stop's resource is consistent and valid (`rwpG_consistentXV`), so its payload is
(`consistentX_left`); a resumption starts from the share beside a consistent answer
(`consistentX_compS`), which the induction hypothesis reads. -/
theorem erwp_consistentPA {Φ : LocFam} {T : OpTabN} {c : Loc → Option Life} (hT : T.AnsC c)
    (n₀ : UInt32) {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ → ConsistentX c ρ →
      erwp (ℍ := ℍ) Φ (opTableN (T.withPA c n₀)) (fun k ls v ρ => Q k ls v ρ ∧ ConsistentX c ρ)
        n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h hc
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hcσ, hvσ⟩ => ?_) (rwpG_consistentXV h hc)
  rcases ht with ⟨v, hv, hq⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, hv, hq, hcσ⟩
  · obtain ⟨⟨h₁, h₂, hTe, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', hq, hab, hPB, hfin, hwc, hPA⟩ := OpTabN.withPA_some (c := c) (n₀ := n₀) hTe
    have hck := consistentX_right hcak hcσ hvσ
    refine Or.inr (Or.inl ⟨K, m, i, v, en', pure_sep_mk ⟨h₁, h₂, hTe', hab ▸ ha⟩ ⟨ρa, ρk, hcak,
      hPA _ _ _ _ hA (consistentX_left hcak hcσ hvσ), fun hq' => hu (hq ▸ hq'), fun ls'' he => ?_⟩⟩)
    rw [hwc] at he
    refine ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' P hP => ?_⟩
    · rw [hPB] at hB
      have h₁ := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
      exact ih k' (by omega) ls'' _ τ₂ h₁ (consistentX_compS hcτ hck (hT m i en hTe _ _ _ _ hB))
    · rw [hq] at hq'
      exact (hcont ls'' he).2 hq' P (hfin ▸ hP)
  · obtain ⟨⟨h₁, h₂, hTe, ha⟩, ρa, ρn, hcan, ⟨hPA₀, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab, -, -, -, hPA⟩ := OpTabN.withPA_some (c := c) (n₀ := n₀) hTe
    exact Or.inr (Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨h₁, h₂, hTe', hab ▸ ha⟩ ⟨ρa, ρn, hcan,
      ⟨hPA _ _ _ _ hPA₀ (consistentX_left hcan hcσ hvσ), hnA⟩, hnn⟩⟩)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal clauseAt capTag)

/-! ### The handled row's table -/

/-! ### The answering functions -/

/-- The steps of a tail clause at `(v, κ)` after its `β` step (Core's `tailClause_steps` without
its first step): to the resume of `κ` at `g v`. -/
theorem tailClause_steps_body (j : Nat) (vc g v κ : Val)
    (hg : PureSteps (pickE j (.val vc)) (.val g)) :
    PureSteps (Expr.subst 0 (Val.pair v κ) (.letpair (.var 0) (.app (.val (Val.lam resumeB))
        (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))))
      ((resK κ).plug (.app (.val g) (.val v))) := by
  refine (PureSteps.head (fun μ => Head.letpair μ v κ _) rfl).trans ?_
  have e : ((Expr.subst 2 ((Val.pair v κ).shift 2 0) (.app (.val (Val.lam resumeB))
      (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))).subst 0 (κ.shift 1 0)).subst 0 v =
      (resK κ).plug (.app (pickE j (.val vc)) (.val v)) := by
    simp [pickE_subst, resumeB, resK, Kont.plug, subst_shift_succ, Expr.subst, Val.val_shift,
      Expr.shift_shift, Expr.shift_zero]
  rw [e]
  have := PureSteps.plug ((resK κ).comp (.appL .hole v)) hg
  rw [Kont.plug_comp, Kont.plug_comp] at this
  exact this

/-! ### The handler -/

theorem extF_trans {ls ls' ls'' : List SRec} {ρ : WRes} (h₁ : extF ls ls' ρ)
    (h₂ : extF ls' ls'' ρ) : extF ls ls'' ρ :=
  fun r hr hrel => h₂ r (h₁ r hr hrel) hrel

/-- `KapRelN` at an entry resumed along `extF` is carried along `extF`. -/
theorem KapRelN.extF {Φ : LocFam} {Tb : TableN} {Q : PostN} {en : OpEntN} {Tc : Option OpTabN}
    {k : Nat} {κ : Val} (hwc : en.wc = extF) {ls ls' : List SRec} {ρ : WRes} (he : extF ls ls' ρ)
    (h : KapRelN (ℍ := ℍ) Φ Tb Q en Tc k ls κ ρ) : KapRelN (ℍ := ℍ) Φ Tb Q en Tc k ls' κ ρ :=
  ⟨h.1, fun ls'' he' => h.2 ls'' (by rw [hwc] at he' ⊢; exact extF_trans he he')⟩

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {S SN : Row}
  {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}

end

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
