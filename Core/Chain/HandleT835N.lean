import Core.Chain.Then835N
import Core.DivHandleLast

/-!
# `[handle]` at clauses that resume `κ` in tail position  `[spec §14, §19]`

Core's `handleT_compatC` (`Core/DivHandle.lean`) at `SemJN`, its proof `ewp_handle_tail` at `erwp`
(the tail instance, `scope-831-interface.md` §10.5), each step Core's:

* `erwp_frame_plain_or` (Core's `ewp_frame_plain_or` with no table beside, by E13): a plain frame
  around a computation at a table `T` below the outer `T′`; the frame's conditions are read at `T`'s
  entries only;
* `tabN_ofEff_ne`, `tabN_ofEff_self`, `capTag_ofEffN` (Core's `Row.tab_ofEff_ne`,
  `Row.tab_ofEff_self`, `capTag_ofEff`): the split of the handled row's table;
* `ansesTy_atN` (Core's `ansesTy_at`): the answering functions read at `vN`;
* `erwp_handle_tail` (Core's `ewp_handle_tail`): `erwp_handle` with a clause running its answering
  function at its must-resume row under the resume frame `resK κ`; the clause's `β` step is paid
  (`erwp_step`), so the answering function's run returns below the stop's index, where `κ` is owed;
* `handleT_compatN` (Core's `handleT_compatC`).

Two readings the chain adds, each where `SemJN` reads a run at its view (D7):

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

/-- An operation of another name in `Σ` extended by the handler's effect is `Σ`'s (Core's
`Row.tab_ofEff_ne`), at any answer types. -/
theorem tabN_ofEff_ne {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    (A R : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) {m i : UInt32} (hm : m ≠ n) :
    tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ Θ c m i =
      tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c m i := by
  rw [tabN_effOf_find, tabN_effOf_find, Row.find_append, Row.find_ofEff_ne n E 0 fs m i hm]
  rfl

/-- **An operation of the handler's name in `Σ` extended by the handler's effect is the effect's
`j`-th, at index `j`** (Core's `Row.tab_ofEff_self`). -/
theorem tabN_ofEff_self {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {A : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) {i : UInt32} {en : OpEntN}
    (hT : tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ Θ c n i = some en) :
    ∃ j, ∃ hj : j < E.length, i.toNat = j ∧ i = UInt32.ofNat (0 + j) ∧
      en = entN E[j].1 E[j].2.2 (fun k v ρ => vN (ℍ := ℍ) E[j].2.1 δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) E[j].2.2 δ Θ k v ρ ∧ ConsistentX c ρ) (finN (ℍ := ℍ) (fs j) δ Θ c) := by
  obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
  have hfo : Row.find (Row.ofEff n E 0 fs) n i = some o := by
    rw [Row.find_append] at hf
    cases h₁ : Row.find (Row.ofEff n E 0 fs) n i with
    | some o' => rw [h₁] at hf; exact hf
    | none =>
        rw [h₁] at hf
        obtain ⟨hm, hn, -⟩ := Row.find_mem hf
        exact absurd hn (hnS o hm)
  obtain ⟨-, j, hj, rfl, rfl⟩ := Row.find_ofEff n E 0 fs n _ o hfo
  have hjn : (UInt32.ofNat (0 + j)).toNat = j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  exact ⟨j, hj, hjn, rfl, rfl⟩

/-- **A handler records its effect's qualifiers** (Core's `capTag_ofEff`): the tag at each
operation's index is its qualifier's. -/
theorem capTag_ofEffN {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {A : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (i : UInt32) (en : OpEntN)
    (hT : tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ Θ c n i = some en) :
    capTag (qualsVal (E.map Prod.fst)).1 i.toNat = en.q.tag := by
  obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_self hnS hlen hT
  rw [hji, capTag_qualsVal _ j (by simpa using hj)]
  simp [entN]

/-! ### The answering functions -/

/-- **The answering functions at `vN`** (Core's `ansesTy_at`): a tuple of the answering functions'
type holds, at each operation, the function `pickE j` steps to, at the empty resource. -/
theorem ansesTy_atN {S SN : Row} {R : VTy} {δ : LSub} {Θ : LocTy} {k : Nat} :
    ∀ (E : List (Qual × VTy × VTy)) {vc : Val} {ρ : WRes},
      vN (ℍ := ℍ) (ansesTy S SN R E) δ Θ k vc ρ →
      ∀ j (h : j < E.length), ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vN (ℍ := ℍ) (ansTy S SN R E[j]) δ Θ k g PMap.empty
  | [], _, _, _, j, h => by simp at h
  | o :: E, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, ρ₁, ρ₂, rfl, -, hg, hr⟩ := h
      have he : ρ₁ = PMap.empty := vN_empty_of_persistent _ (ansTy_persistent S SN R o) hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := ansesTy_atN E hr j (by simpa using hj)
          exact ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), by simpa using hg'⟩

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

/-- The frame conditions at a row of must-resume operations (Core's `lin_conds`). -/
theorem lin_condsN {SN : Row} (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false) {B : VTy}
    {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {m i : UInt32} {en : OpEntN}
    (h : tabN (ℍ := ℍ) (CTy.effOf SN B) δ Θ c m i = some en) : en.q = .lin ∧ en.abort = false := by
  obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find h
  have ho := hLin o (Row.find_mem hf).1
  simp [entN, ho.1]

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {S SN : Row}
  {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}

/-- **A tail-resuming handler** (Core's `ewp_handle_tail`): `erwp_handle_le` at the handled row's
table, its payloads at the handler's name read at the view (`erwp_consistentPA`). A clause pays its
`β` step and runs its answering function at its must-resume row under the resume frame
(`erwp_frame_plain_or`, from `Σ_N` to `Σ`); the function's value, below the stop's index and
consistent with the view across its resumptions (`erwp_consistentAns`), is the answer `κ` is
resumed at. -/
theorem erwp_handle_tail (hΘ : Θ.OK) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    {vr vc : Val} {N : Nat}
    (hVr : vN (ℍ := ℍ) (retTy S A R) δ Θ N vr PMap.empty)
    (hVc : vN (ℍ := ℍ) (ansesTy S SN R E) δ Θ N vc PMap.empty) {ls : List SRec} {e : Expr}
    {ρ : WRes}
    (h : erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ Θ c))
      (fun k _ v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) N ls e ρ) (hc : ConsistentX c ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c))
      (fun k _ v ρ => vN (ℍ := ℍ) R δ Θ k v ρ) N ls (hndE (tailH n E vr vc) e) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  set Tin := tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ Θ c with hTin
  set Tout := tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c with hTout
  have hToutD : Tout.Down := tabN_down _ δ Θ hΘ.1 c
  have hQout : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) R δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  have hTd := opTableN_down hToutD
  have h' := erwp_consistentPA (tabN_ansC _ δ Θ c) n N ls e ρ h hc
  refine erwp_handle_le hΦ N (Tin.withPA c n) Tout (OpTabN.withPA_down (tabN_down _ δ Θ hΘ.1 c))
    hToutD n (fun m i hm => by rw [OpTabN.withPA_ne _ hm, hTin, tabN_ofEff_ne A R δ Θ c hm])
    (qualsVal (E.map Prod.fst)) vr ⟨tailTuple E 0 (.val vc), isVal_tailTuple _ E 0⟩ _ _ hQout
    (fun i en hT _ => by
      obtain ⟨en₀, hT₀, rfl⟩ := OpTabN.withPA_self hT
      exact capTag_ofEffN hnS hlen i en₀ hT₀)
    (fun _ => none) (fun _ _ _ _ _ _ h => by cases h) ?_ ?_ N le_rfl ls e ρ h'
  · -- `[ret]`: `h_ret` at the value, consistent with the view
    rintro k hk ls' v σ ⟨hv, hcv⟩
    obtain ⟨-, hr⟩ := hVr
    have h₁ := hr Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_empty c) ls' c k hk v σ σ
      (compS_empty_left σ) hv hcv
    exact (cN_effOf S R δ Θ c k ls' _ σ).mp h₁
  · intro i en' hT
    obtain ⟨en, hT₀, rfl⟩ := OpTabN.withPA_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_self hnS hlen hT₀
    obtain ⟨g, hg, hVg⟩ := ansesTy_atN E hVc j hj
    refine ⟨⟨tailClause j (E[j].2.2.isZero && E[j].1 != .lin) (.val vc), isVal_tailClause _ _ _⟩,
      by rw [hji, clauseAt_tailTuple _ E 0 j hj]; simp, fun ha k hk ls' v κ σ hσ => ?_,
      fun ha k hk ls' v σ hσ => ?_⟩
    · -- the clause pays its `β` step, then resumes `κ` with `g v` under the resume frame
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = false := ha
      simp only [ansTy, ha'] at hVg
      show erwp (ℍ := ℍ) _ _ _ k ls' (.app (tailClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vc)) (.pair (.val v) κ.1)) σ
      rw [ha']
      obtain ⟨σa, σk, hck, ⟨hA', hcA⟩, hK⟩ := hσ
      cases k with
      | zero => exact erwp_zero
      | succ k₀ =>
      refine erwp_step (opTableN_local _) (e' := Expr.subst 0 (Val.pair v κ) _)
        (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl .hole) ?_
      refine erwp_pureSteps hΦ hTd hQout (tailClause_steps_body j vc g v κ hg) ?_
      -- the answering function's run at `Σ_N`, consistent with the view
      obtain ⟨-, hgr⟩ := hVg
      have hy := hgr Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_empty c) ls' c k₀ (by omega) v σa
        σa (compS_empty_left σa) (vN_down _ δ Θ k₀ v σa hA') hcA
      have hy' := (cN_effOf SN E[j].2.2 δ Θ c k₀ ls' _ σa).mp hy
      have hy'' := erwp_consistentAns (tabN_ansC _ δ Θ c) k₀ k₀ le_rfl ls' _ σa hy' hcA
      refine erwp_frame_plain_or hΦ _ Tout (tabN_le_of_rowLe hSN _ R δ Θ c) (resK κ)
        (resK_plain κ).1 (resK_plain κ).2
        (fun ls σ => KapRelN (ℍ := ℍ) (Θ.view c) (opTableN Tout)
          (fun k _ v ρ => vN (ℍ := ℍ) R δ Θ k v ρ) (OpEntN.withPA c _) none (k₀ + 1) ls κ σ)
        (fun ls₁ ls₂ hs σ hF => KapRelN.extF rfl (extF_of_same hs σ) hF)
        (fun m i en₁ hT₁ ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ =>
          (tabN_down _ δ Θ hΘ.1 c).wcl m i en₁ hT₁ ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁)
        (fun m i en₁ hT₁ ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ hF => by
          obtain ⟨o, -, rfl⟩ := tabN_effOf_some_find hT₁
          exact KapRelN.extF rfl (extF_right hc₁ he₁) hF)
        (fun m i en₁ hT₁ ha₁ => absurd ha₁ (by simp [(lin_condsN hLin hT₁).2]))
        (fun m i en₁ hT₁ hq₁ => absurd hq₁ (by simp [(lin_condsN hLin hT₁).1]))
        (fun m i en₁ hT₁ _ hq₁ => absurd (lin_condsN hLin hT₁).1 hq₁)
        _ _ ?_ k₀ ls' _ σa hy'' σk σ hK hck
      rintro k'' ls'' w τ ⟨τ₁, τ₂, hcτ, ⟨hk'', hw, hcw, -⟩, hF⟩
      refine erwp_pureSteps hΦ hTd hQout (resK_steps κ w) ?_
      exact (hF.2 ls'' (extF_refl ls'' τ₂) k'' (by omega)).1 w τ₁ τ ⟨hw, hcw⟩
        (ResU.CompS.comm hcτ)
    · -- an abortive operation: the clause runs `g v`
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = true := ha
      simp only [ansTy, ha'] at hVg
      show erwp (ℍ := ℍ) _ _ _ k ls' (.app (tailClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vc)) (.val v)) σ
      rw [ha']
      refine erwp_pureSteps hΦ hTd hQout (tailClauseA_steps j vc g v hg) ?_
      obtain ⟨-, hgr⟩ := hVg
      obtain ⟨hA', hcA⟩ := hσ
      exact (cN_effOf S R δ Θ c k ls' _ σ).mp (hgr Θ (LocTy.extR_refl Θ _) hΘ c
        (consistentX_empty c) ls' c k hk v σ σ (compS_empty_left σ) hA' hcA)

end

/-- **`[handle]` at clauses that resume `κ` in tail position** (Core's `handleT_compatC`):
`handle_n e with (h_ret, gs)`, the clauses written out from the answering functions `gs`
(`tailTuple`). The handler's value is read off its run at the run's start (`erwp_val_post`), as
Core reads it off `wpTS`; the handled computation runs at its row's table from the part of the
resource consistent with the view (`gN_splitC`), and the handler is `erwp_handle_tail`. A `Div`
row is a row of the chain's table (E13), so Core's split at `Row.divB S` has no counterpart, and neither do the rule's `n ≠ 0` and
`n ≠ Div`, which only that split and Core's `ewp_handle` read. -/
theorem handleT_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Hr Hc e : Expr} {S SN : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
    (hc : SemJN (ℍ := ℍ) Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E))))
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)
      (.comp (CTy.effOf S R)) := by
  intro δ γ Θ c N ls ρ hδ hΘ hcρ hlw hg
  refine (cN_effOf S R δ Θ c N ls _ ρ).mpr (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂, -, hc₂⟩ := gN_splitC hsp hg hcρ hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hρ₁ : ρ₁ = PMap.empty := gN_deadP hd hg₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ (.pair Hr Hc)) := isVal_psub_valFormIn hlw₁ (.pair hHr hHc)
  have hH' : erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
      (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (retTy S A R) (ansesTy S SN R E)) δ Θ k v ρ) N ls
      (⟨substAll γ (.pair Hr Hc), hval⟩ : Val).1 PMap.empty :=
    hc δ γ Θ c N ls PMap.empty hδ hΘ (consistentX_empty c) hlw₁ hg₁
  have hE' := (cN_effOf _ A δ Θ c N ls _ ρ₂).mp (he δ γ Θ c N ls ρ₂ hδ hΘ hc₂ hlw₂ hg₂)
  show erwp (ℍ := ℍ) _ _ _ N ls
    (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)) ρ₂
  rw [psub_hndExpr]
  simp only [Expr.psub]
  rw [show Expr.psub 0 γ (tailTuple E 0 Hc) = tailTuple E 0 (substAll γ Hc) from
    tailTuple_psub γ Hc E 0]
  have hT₀ : (VTy.tensor (retTy S A R) (ansesTy S SN R E)).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]
    exact ⟨retTy_persistent S A R, ansesTy_persistent S SN R E⟩
  -- the handler's value, read off its run at the run's start
  rw [erwp_eq]
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ls', ρ', -, hv'⟩ := erwp_val_post (by omega) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg hI hl hfd
  obtain ⟨vr, vc, σ₁, σ₂, hpair, -, hVr, hVc⟩ := hv'
  have hσ₁ : σ₁ = PMap.empty := vN_empty_of_persistent _ (retTy_persistent S A R) hVr
  have hσ₂ : σ₂ = PMap.empty := vN_empty_of_persistent _ (ansesTy_persistent S SN R E) hVc
  subst hσ₁ hσ₂
  have hHe : substAll γ (.pair Hr Hc) = (Val.pair vr vc).1 := congrArg Subtype.val hpair
  simp only [substAll, Expr.psub, Val.pair] at hHe
  obtain ⟨h₁, h₂⟩ := Expr.pair.inj hHe
  have hH := erwp_handle_tail (fs := fs) hΘ hnS hlen hSN hLin hVr hVc hE' hc₂
  rw [erwp_eq] at hH
  rw [h₁, show substAll γ Hc = vc.1 from h₂] at hrun
  exact hH ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
