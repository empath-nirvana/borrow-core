import Core.EffFin
import Support.Model.Surgery
import Support.Model.Outlives
import Support.Model.Singletons

/-!
# Core — `[handle]` with a boxed continuation (BOXED-κ)  `[spec §28]`

A clause of `[handle]` receives its continuation bare, at `kTy Σ R q B F`; under BOXED-κ it
receives it boxed, `κ : [@d] K`. The relation reads `[@d] K` as `K` with its resource in
`Res_{δ(d)}`, so the rule needs the continuation's share at every stop of the handled computation in
`Res_{δ(d)}`.

**The stop lemma** (`ewp_stratify`, `stop_sem`). `opTableS α T` is `opTable T` with one more
conjunct at each non-abortive stop: the continuation's share is in `Res_α`. It is below `opTable T`
(`opTableS_le`, `ewpS_ewp`). No new invariant carries it: `wpG` carries `↭` from a run's start to its
end (`ResU.UpdV ρ π`), `↭` keeps `Res_α` (`ResU.updV_inStratum`), so a run started in `Res_α` ends in
`Res_α` (`wpG_inStratum`), and the share is a `●`-factor of the stop's resource. Across a
resumption the next run starts at the share and the answer, in `Res_α` when the answer is. At the
typing, the context's resource is in `Res_{δ(d)}` by `[]I`'s fold of 6.60 (`gSepC_outlives`), and an
answer of a type outliving `@d` is (`vC_outlives`).

**The rule** (`handle_compatCB`, `handleV_compatCB`). `clausesTyB Σ R d E fs` is `clausesTy` with
each capturing clause's `κ` at `[@d] K`. The premises are `[handle]`'s at `clausesTyB`, and two
about the handled computation `e : F_{E_n ⊕ Σ} A` under `Γ₂`:

* `Δ ⊨ Γ₂ ⊐ @d` (`CtxOutlives`, which holds `Δ ⊨ @d`);
* every non-abortive operation of `E_n ⊕ Σ`, handled or forwarded, has an answer type outliving
  `@d` (`Row.AnsOutlives`).

`ewp_handleS` is `ewp_handle` at the stratified table: the clause receives `κ`'s share in `Res_α`.
At a must-resume or cancellable operation `κ` also holds its cell, an `own` cell, which is in every
stratum.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Step1N performE raiseE opPayload
  cancelVal hndE ubindE ccatchE cfinE hndVal kappa clauseAt errNext capTag kappaAt kappaC
  kappaCBody kappaCell freeE stuckE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The stratified table -/

/-- `performStop` with the continuation's share in `Res_α`. -/
def performStopS (α : Life) (T : OpTab) : Table := fun ls t Φ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEnt) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆
        (en.PA ls v ⋆ fun ρ => contShare en ls K Φ ρ ∧ ρ.InStratum α)

/-- `opTable T` with every non-abortive stop's share in `Res_α`; the abortive stops as
`opTable`'s. -/
def opTableS (α : Life) (T : OpTab) : Table := fun ls t Φ =>
  BoLo.or (performStopS α T ls t Φ)
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
          T n i = some en ∧ en.abort = true⌝ ⋆
          ((fun ρ => en.PA ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ))

theorem opTableS_mono (α : Life) (T : OpTab) : (opTableS α T).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with ⟨K, n, i, v, en, hp⟩ | h
  · obtain ⟨hpure, ρa, ρk, hc, hA, ⟨hu, hk⟩, hs⟩ := pure_sep_iff.mp hp
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure
      ⟨ρa, ρk, hc, hA, ⟨hu, fun ls' he => ⟨fun w τ₁ τ₂ hB hc' => ?_, (hk ls' he).2⟩⟩, hs⟩⟩
    exact hΦ _ _ _ ((hk ls' he).1 w τ₁ τ₂ hB hc')
  · exact Or.inr h

/-- The stratified table is below the table. -/
theorem opTableS_le {α : Life} {T : OpTab} {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTableS α T ls t Φ ρ) :
    opTable T ls t Φ ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | h
  · obtain ⟨hpure, ρa, ρk, hc, hA, hcs, -⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA, hcs⟩⟩
  · exact Or.inr h

/-- `ewpTS` at the stratified table gives `ewpTS` at the table. -/
theorem ewpS_ewp {α : Life} {T : OpTab} {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : ewpTS ls e (opTableS α T) Q ρ) :
    ewpTS ls e (opTable T) Q ρ :=
  ewp_mono (opTable_mono T) (fun _ _ _ _ h => opTableS_le h) (fun _ _ _ h => h) h

/-! ### `Res_α` through a run -/

/-- `Res_α` is closed under `●`. -/
theorem inStratum_compS {α : Life} {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.InStratum α) (h₂ : ρ₂.InStratum α) : ρ.InStratum α :=
  BoLo.inStratum_comp (BoLo.compS_hC α) h h₁ h₂

/-- **A run started in `Res_α` ends in `Res_α`**: `wpG`'s `↭` from its start to its end, which
keeps `Res_α` (`ResU.updV_inStratum`), and the end resource a `●`-factor of `↭`'s right side. -/
theorem wpG_inStratum {α : Life} {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp}
    {ρ : WRes} (hρ : ρ.InStratum α) (h : wpG ls e Q ρ) :
    wpG ls e (fun ls' t σ => Q ls' t σ ∧ σ.InStratum α) ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h2 h3 h4 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15, ResU.CompS.inStratum_left a8 (ResU.updV_inStratum hρ a9)⟩

/-- The answers of a table's non-abortive operations lie in `Res_α`. -/
def OpTab.AnsIn (α : Life) (T : OpTab) : Prop :=
  ∀ n i en, T n i = some en → en.abort = false → ∀ ls w τ, en.PB ls w τ → τ.InStratum α

/-- **The stop lemma, semantically.** A computation in `ewpTS` at `opTable T`, started in `Res_α`,
at a table whose answers lie in `Res_α`, is in `ewpTS` at `opTableS α T`: at every stop of every
run, the continuation's share is in `Res_α`. -/
theorem ewp_stratify {α : Life} {T : OpTab} (hT : T.AnsIn α) {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ)
    (hρ : ρ.InStratum α) : ewpTS ls e (opTableS α T) Q ρ := by
  refine (ewp_ind (fun ls e ρ => ρ.InStratum α → ewpTS ls e (opTableS α T) Q ρ) ?_ h) hρ
  intro ls e ρ hs hρ
  refine ewp_fold (opTableS_mono α T) (wpG_mono ?_ (wpG_inStratum hρ hs))
  rintro ls' t σ ⟨hq, hσ⟩
  rcases hq with hv | hq
  · exact Or.inl hv
  rcases hq with ⟨K, n, i, v, en, hp⟩ | habt
  · obtain ⟨hpure, ρa, ρk, hc, hA, hu, hk⟩ := pure_sep_iff.mp hp
    have hρk : ρk.InStratum α := ResU.CompS.inStratum_right hc hσ
    refine Or.inr (Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure
      ⟨ρa, ρk, hc, hA, ⟨hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc' => ?_, (hk ls'' he).2⟩⟩, hρk⟩⟩)
    exact (hk ls'' he).1 w τ₁ τ₂ hB hc'
      (inStratum_compS hc' hρk (hT n i en hpure.2.2.1 hpure.2.2.2 ls'' w τ₁ hB))
  · exact Or.inr (Or.inr habt)

/-! ### The stop lemma at Core's typing -/

/-- `Δ ⊢ Σ ⊐ @d` at the answers: every non-abortive operation's answer type outlives `@d`. -/
def Row.AnsOutlives (Δ : LifeCtx) (d : Lifetime.Life) (S : Row) : Prop :=
  ∀ o ∈ S, o.abort = false → VOutlives Δ d o.B

/-- A row whose answer types outlive `@d` has its answers in `Res_{δ(d)}` (6.60, `vC_outlives`). -/
theorem Row.ansIn_of_ansOutlives {Δ : LifeCtx} {δ : LSub} {d : Lifetime.Life} {α : Life}
    {S : Row} (hδ : Δ.Models δ) (hd : d.interp δ = some α) (hS : Row.AnsOutlives Δ d S) :
    (Row.tab S δ).AnsIn α := by
  intro n i en hT ha ls w τ hB
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  exact vC_outlives hδ hd (hS o (Row.find_mem hf).1 ha) true ls w τ hB

/-- The stratified semantic judgment at `F_Σ A`: at every substitution and every interpretation of
`@d`, the computation is in `ewpTS` at the stratified table of `Σ` at `δ(d)`. -/
def SemCS (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (S : Row) (A : VTy) (d : Lifetime.Life) :
    Prop :=
  ∀ δ γ (ls : List SRec) ρ α, Δ.Models δ → d.interp δ = some α → gDenC ls δ Γ γ ρ →
    ewpTS ls (substAll γ M) (opTableS α (Row.tab S δ)) (fun ls v => vC true A ls δ v) ρ

/-- The stratified judgment gives the judgment, where `@d` is defined. -/
theorem SemCS.semC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (h : SemCS Δ Γ M S A d) (hd : Δ.Defines d) :
    SemC Δ Γ M (CTy.effOf S A) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨α, ha⟩ := hd δ hδ
  exact (cC_effOf_wp S A ls δ _ ρ).mpr (effWp_of_ewp (Row.keyNA_of_divB δ)
    (ewpS_ewp (h δ γ ls ρ α hδ ha hg)))

/-- **The stop lemma at `SemC`**, at a row that does not hold `Div`: `SemCS` is a least fixed
point, which a computation that ticks forever is not in. -/
theorem stop_sem {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (hSd : Row.divB S = false) (hM : SemC Δ Γ M (CTy.effOf S A))
    (hΓ : CtxOutlives Δ Γ d) (hS : Row.AnsOutlives Δ d S) : SemCS Δ Γ M S A d := by
  intro δ γ ls ρ α hδ hd hg
  exact ewp_stratify (Row.ansIn_of_ansOutlives hδ hd hS)
    ((cC_effOf S A ls δ _ ρ hSd).mp (hM δ γ ls ρ hδ hg))
    (gSepC_outlives hδ hd hΓ.2 (gDenC_iff.mp hg).2)

/-! ### The handler at the stratified table -/

/-- **`[handle]` at the stratified table**: `ewp_handle`, its inner computation in `ewpTS` at
`opTableS α Tin`, so the clause of a capturing operation receives `κ` in `Res_α`. The proof is
`ewp_handle`'s; at a must-resume or cancellable operation `κ`'s resource is the share and its cell,
an `own` cell. -/
theorem ewp_handleS (α : Life) (Tin Tout : OpTab) (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : List SRec → Val → WProp) (Tc : UInt32 → Option OpTab)
    (hq : ∀ i en, Tin n i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hTc : ∀ i en, Tin n i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelObl T₁) ∧ T₁.Le Tk)
    (hret : ∀ ls v ρ, Qin ls v ρ → ewpTS ls (.app (.val hr) (.val v)) (opTable Tout) Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ ls v (κ : Val) ρ,
        (en.PA ls v ⋆ fun ρ => KapRel Tout Qout en (Tc i) ls κ ρ ∧ ρ.InStratum α) ρ →
        ewpTS ls (.app (.val c) (.pair (.val v) κ.1)) (opTable Tout) Qout ρ) ∧
      (en.abort = true → ∀ ls v ρ, en.PA ls v ρ →
        ewpTS ls (.app (.val c) (.val v)) (opTable Tout) Qout ρ)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTableS α Tin) Qin ρ →
      ewpTS ls (hndE (hndVal n qs hr hs) e) (opTable Tout) Qout ρ := by
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ewpTS ls (hndE (hndVal n qs hr hs) e) (opTable Tout) Qout ρ) ?_ h
  intro ls e ρ hstep
  refine ewp_fold (opTable_mono Tout) (wpG_bind (hndK (hndVal n qs hr hs)) e ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_) hstep
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · -- `[ret]`
    exact wpG_head (fun μ => Head.hret μ n qs hr hs v) rfl _ _ σ
      (ewp_unfold (opTable_mono Tout) (hret _ _ _ hv))
  rcases ht with ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, ⟨hu, hcont⟩, hstr⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[op]` at the handler's name: the clause, with `κ` in `Res_α`
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      have hcan : ∀ ls'', Ext ls' ls'' ρk → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
          ewpTS ls'' (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))) (opTable Tk)
            (fun _ v => ⌜v = Val.unit⌝) ρk := by
        intro ls'' he hq' Tk hTk
        obtain ⟨T₁, hf, hle⟩ := hTc i en hT ha hq' Tk hTk
        exact ewp_ccatch hle ((hcont ls'' he).2 hq' _ hf)
      rw [hq i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine ewp_unfold (opTable_mono Tout) (hna ha ls' v
            ⟨kappa (hndVal m qs hr hs) K₁, by unfold kappa; exact .lam⟩ σ
            ⟨ρa, ρk, hcak, hA, ⟨?_, hstr⟩⟩)
          refine ⟨hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq' => ?_⟩⟩
          · exact ewp_kappa_resume (opTable_mono Tout) _ K₁ w
              ((hcont ls'' he).1 w τ₁ τ₂ hB hc)
          · exact fun Tk hTk => ewp_kappa_cancel (opTable_mono Tk) _ K₁ (hcan ls'' he hq' Tk hTk)
      | cancel | lin =>
          refine ewp_unfold (opTable_mono Tout) (ewp_kappaCell (opTable_mono Tout) _
            (hndVal m qs hr hs) K₁ (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ => ?_))
          obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
          have hy : y.InStratum α := by
            refine inStratum_compS hy₁ hstr ?_
            rw [hcell]
            exact ResU.inStratum_single_own α ℓ Val.unit
          refine hna ha ls' v ⟨_, isVal_kappaC _ ℓ (hndVal m qs hr hs) K₁⟩ σ₂
            ⟨ρa, y, hy₂, hA, ⟨?_, hy⟩⟩
          refine ⟨fun h' => (by rw [hqq] at h'; cases h'),
            fun ls'' he => ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' => ?_⟩⟩
          · obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
            exact ewp_kappaC_resume (opTable_mono Tout) _ ℓ _ K₁ w
              ⟨σ₁, z, ResU.CompS.comm hzτ, hcell, (hcont ls'' (Ext.left hy₁ he)).1 w τ₁ z hB hz⟩
          · first
              | exact absurd hqq hq'
              | exact fun Tk hTk => ewp_kappaC_cancel (opTable_mono Tk) ℓ _ K₁
                  ⟨σ₁, ρk, ResU.CompS.comm hy₁, hcell, hcan ls'' (Ext.left hy₁ he) hq' Tk hTk⟩
    · -- an operation of another name passes outward; its share's stratum is not needed
      refine wpG_here _ _ _ σ (Or.inr (Or.inl ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq => ?_⟩⟩⟩))
      · rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      · rw [Kont.plug_comp]; exact (hcont ls'' he).1 w τ₁ τ₂ hB hc
      · intro P hP
        show P ls'' (((hndK (hndVal n qs hr hs)).comp K₁).dead.plug _) ρk
        rw [dead_comp, dead_hndK]
        exact (hcont ls'' he).2 hq P hP
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[unwind]` at the handler's name: the clause; the continuation is dropped
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      refine wpG_garbage (wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hcτ, hq, hnτ⟩ => ⟨τ₁, τ₂, hcτ, hnτ, hq⟩)
        (wpG_frame (e := .app (.val c) (.val v)) (fun _ => fun τ => NoOwn τ)
          (fun _ _ _ h => h) σ ⟨ρa, ρn, hcan,
            ewp_unfold (opTable_mono Tout) (hab ha ls' v ρa hPA), hnn⟩))
    · -- an abortive operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inr ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))
      rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm

/-! ### The clauses' type with a boxed `κ` -/

/-- A clause's type with `κ` at `[@d] K`: `!U(A ⊗ [@d] K ⊸ F_Σ R)`, or `!U(A ⊸ F_Σ R)` at an
abortive operation (no `κ`). -/
def clauseTyB (S : Row) (R : VTy) (d : Lifetime.Life) (o : Qual × VTy × VTy)
    (F : CTy := .ret .unit) : VTy :=
  match o with
  | (q, A, B) => if (B.isZero && q != .lin) then .bang (.thunk (.arr A (CTy.effOf S R)))
      else .bang (.thunk (.arr (.tensor A (.box d (kTy S R q B F))) (CTy.effOf S R)))

/-- The clauses' type with boxed continuations: `clausesTy`'s tuple at `clauseTyB`. -/
def clausesTyB (S : Row) (R : VTy) (d : Lifetime.Life) (E : List (Qual × VTy × VTy))
    (fs : Nat → CTy := finsNil) : VTy :=
  match E with
  | [] => .unit
  | o :: E => .tensor (clauseTyB S R d o (fs 0)) (clausesTyB S R d E (fun j => fs (j + 1)))

theorem clausesTyB_at {S : Row} {R : VTy} {d : Lifetime.Life} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) {hs : Val} {ρ : WRes},
      vC true (clausesTyB S R d E fs) ls δ hs ρ →
      ∀ j (h : j < E.length), ∃ c, clauseAt hs.1 j = some c ∧
        vC true (clauseTyB S R d E[j] (fs j)) ls δ c PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, fs, hs, ρ, h, j, hj => by
      obtain ⟨c, rest, h⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, hc₁, hr⟩ := pure_sep_iff.mp h
      have hc₁' := hc₁
      obtain ⟨q, A, B⟩ := o
      have he : ρ₁ = PMap.empty := by
        simp only [clauseTyB] at hc₁'; split at hc₁' <;> exact hc₁'.1
      cases j with
      | zero =>
          refine ⟨c, ?_, he ▸ hc₁⟩
          simp [clauseAt, Val.pair, c.2]
      | succ j =>
          obtain ⟨c', hc', hv⟩ := clausesTyB_at E (fun j => fs (j + 1)) hr j (by simpa using hj)
          exact ⟨c', by simpa [clauseAt, Val.pair] using hc', by simpa using hv⟩

/-- The clauses hold nothing. -/
theorem clausesTyB_empty {S : Row} {R : VTy} {d : Lifetime.Life} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) {hs : Val} {ρ : WRes},
      vC true (clausesTyB S R d E fs) ls δ hs ρ → ρ = PMap.empty
  | [], _, _, _, h => h.1
  | (q, A, B) :: E, fs, hs, ρ, h => by
      obtain ⟨c, rest, h⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, hc₁, hr⟩ := pure_sep_iff.mp h
      have he : ρ₁ = PMap.empty := by
        simp only [clauseTyB] at hc₁; split at hc₁ <;> exact hc₁.1
      rw [he, clausesTyB_empty E (fun j => fs (j + 1)) hr] at hc
      exact eq_of_compS_empty_left hc

/-- The clauses' type is persistent: a tuple of `!` types. -/
theorem clausesTyB_persistent (S : Row) (R : VTy) (d : Lifetime.Life) :
    ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy), (clausesTyB S R d E fs).Persistent
  | [], _ => rfl
  | (q, A, B) :: E, fs => by
      have h := clausesTyB_persistent S R d E (fun j => fs (j + 1))
      simp only [VTy.Persistent] at h ⊢
      simp only [clausesTyB, VTy.persistent, Bool.and_eq_true, h, and_true]
      simp only [clauseTyB]
      split <;> rfl

/-! ### BOXED-κ -/

/-- **A handler at clause values, `κ` boxed at `@d`**: `ewp_handle_vals` at `clausesTyB`, the
handled computation in `ewpTS` at the stratified table at `α = δ(d)`. `κ`'s relation at `K` is
`vC_kTy_of_kapRel`'s; its share in `Res_α` makes it `[@d] K`. -/
theorem ewp_handle_valsB {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {A R : VTy} {d : Lifetime.Life} {α : Life} {δ : LSub} {ls₀ : List SRec} {vr vc : Val}
    (hd : d.interp δ = some α) (hS : Row.divB S = false) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
    (hVc : vC true (clausesTyB S R d E fs) ls₀ δ vc PMap.empty) {ls : List SRec} {e : Expr}
    {ρ : WRes}
    (he : ewpTS ls e (opTableS α (Row.tab (Row.ofEff n E 0 fs ++ S) δ))
      (fun ls v => vC true A ls δ v) ρ) :
    ewpTS ls (hndE (hndVal n (qualsVal (E.map Prod.fst)) vr vc) e) (opTable (Row.tab S δ))
      (fun ls v => vC true R ls δ v) ρ := by
  refine ewp_handleS α (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (Row.tab S δ) n hn0 ?_
    (qualsVal (E.map Prod.fst)) vr vc
    (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v)
    (fun i => cancelTabOf S (fs i.toNat) δ)
    (fun i en hT _ => capTag_ofEff hnS hlen i en hT) ?_ ?_ ?_ he
  · intro m i hm
    simp [Row.tab, Row.find_append, Row.find_ofEff_ne n E 0 fs m i hm]
  · intro i en hT ha hq Tk hTk
    obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
    have hcap := capB_of_ent ha hq
    rw [hji] at hTk
    simp only [cancelTabOf] at hTk
    split at hTk
    · cases hTk
    · rename_i hnT
      cases hTk
      refine ⟨Row.tab (fs j).rowOf δ, ?_, tab_le_cancelTab S (fs j) δ⟩
      rw [OpSig.ent_fin, if_pos hcap, finObl_eq]
      simp only [hnT, Bool.false_eq_true, if_false]
  · intro ls' v σ hv
    have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
    exact (cC_effOf S R ls' δ _ σ hS).mp hf
  · intro i en hT
    obtain ⟨j, hj, hji, hi, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
    obtain ⟨c, hcl, hVcl⟩ := clausesTyB_at E fs hVc j hj
    refine ⟨c, by rw [hji]; exact hcl, ?_, ?_⟩
    · intro hna ls' v κ σ hσ
      generalize hEj : E[j] = t at hVcl hna hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at hna
      simp only [clauseTyB, hna] at hVcl
      obtain ⟨σa, σk, hck, hA', hK, hσk⟩ := hσ
      rw [hji] at hK
      have hκ := vC_kTy_of_kapRel (S := S) (R := R) (B := B') (q := q) (F := fs j) A' n
        (UInt32.ofNat (0 + j)) hK
      have hκB : vC true (.box d (kTy S R q B' (fs j))) ls' δ κ σk := ⟨α, hd, hκ, hσk⟩
      have hf := (hVcl.2 ls' (ext_empty' ls₀ ls')) (Val.pair v κ) σ σ
        ⟨v, κ, pure_sep_mk rfl ⟨σa, σk, hck, hA', hκB⟩⟩ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ hS).mp hf
    · intro ha ls' v σ hσ
      generalize hEj : E[j] = t at hVcl ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [clauseTyB, ha] at hVcl
      have hf := (hVcl.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ hS).mp hf

/-- **BOXED-κ at variables** (`handle_compatC` with `κ : [@d] K`): the clauses at `clausesTyB`,
and the handled computation's context and answer types outliving `@d`. -/
theorem handle_compatCB {Δ : LifeCtx} {Γ Γ₁ Γ₂ Γr Γc : Ctx VTy} {e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy} {ir ic : Nat}
    {d : Lifetime.Life}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hsp₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTyB S R d E fs))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))
    (hΓd : CtxOutlives Δ Γ₂ d) (hSd : Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S)) :
    SemC Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (CTy.effOf S R) := by
  have hS := Row.divB_of_ofEff hnS hdv
  have heS := stop_sem hdv he hΓd hSd
  intro δ γ ls ρ hδ hg
  obtain ⟨α, hd⟩ := hΓd.1 δ hδ
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨ρr, ρcl, hcrc, hgr, hgc⟩ := gDenC_split hsp₁ hg₁
  obtain ⟨hlr, hsr⟩ := gDenC_iff.mp hgr
  obtain ⟨vr, hvr, hVr⟩ := gSepC_soloP hr (hr.lt_of_liveWithin hlr) hsr
  obtain ⟨hlc, hsc⟩ := gDenC_iff.mp hgc
  obtain ⟨vc, hvc, hVc⟩ := gSepC_soloP hc (hc.lt_of_liveWithin hlc) hsc
  have hρr : ρr = PMap.empty := hVr.1
  have hρc : ρcl = PMap.empty := clausesTyB_empty E fs hVc
  subst hρr hρc
  rw [eq_of_compS_empty_left hcrc] at hc12
  rw [eq_of_compS_empty_left hc12]
  have hsub : substAll γ (hndTerm n (E.map Prod.fst) ir ic e) =
      Expr.app (Expr.app (.val (.prim .hnd)) (.pair (.val (Val.i32 n))
        (.pair (.val (qualsVal (E.map Prod.fst))) (.pair (substAll γ (.var ir))
          (substAll γ (.var ic)))))) (substAll γ e) := by
    simp only [hndTerm, substAll, Expr.psub, Expr.val, Val.prim, Val.i32, psub_qualsVal]
  show cC _ ls δ (substAll γ (hndTerm n (E.map Prod.fst) ir ic e)) ρ₂
  rw [hsub, substAll_var_some hvr, substAll_var_some hvc]
  exact (cC_effOf S R ls δ _ ρ₂ hS).mpr (ewp_handle_valsB hd hS hn0 hnS hlen hVr hVc
    (heS δ γ ls ρ₂ α hδ hd hg₂))

/-- **BOXED-κ** (`handleV_compatC` with `κ : [@d] K`): `handle_n e with H`, `H` a value form over
persistent slots at `retTy Σ A R ⊗ clausesTyB Σ R d E fs`; `e` at `F_{E_n ⊕ Σ} A` under `Γ₂`, with
`Δ ⊨ Γ₂ ⊐ @d` and every non-abortive answer type of `E_n ⊕ Σ` outliving `@d`. -/
theorem handleV_compatCB {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    {d : Lifetime.Life}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
    (hc : SemV Δ Γ₁ H (.tensor (retTy S A R) (clausesTyB S R d E fs)))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))
    (hΓd : CtxOutlives Δ Γ₂ d) (hSd : Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S)) :
    SemC Δ Γ (hndExpr n (E.map Prod.fst) H e) (CTy.effOf S R) := by
  have hS := Row.divB_of_ofEff hnS hdv
  have heS := stop_sem hdv he hΓd hSd
  intro δ γ ls ρ hδ hg
  obtain ⟨α, hdα⟩ := hΓd.1 δ hδ
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨hlw₁, hs₁⟩ := gDenC_iff.mp hg₁
  have hρ₁ : ρ₁ = PMap.empty := gSepC_deadP hd hs₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ H) := isVal_psub_valFormIn hlw₁ hH
  have hH' := hc δ γ ls PMap.empty hδ hg₁
  have hE' := heS δ γ ls ρ₂ α hδ hdα hg₂
  show cC _ ls δ (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) H e)) ρ₂
  rw [psub_hndExpr]
  show cC _ ls δ (hndExpr n (E.map Prod.fst) (substAll γ H) (substAll γ e)) ρ₂
  refine (cC_effOf S R ls δ _ ρ₂ hS).mpr (ewp_fold (opTable_mono _) ?_)
  intro ρf fρ ps hf hcf hT htg Al k
  obtain ⟨ls', ρ', -, hv⟩ := wpTS_val_post (v := ⟨substAll γ H, hval⟩) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg
  have hT₀ : (VTy.tensor (retTy S A R) (clausesTyB S R d E fs)).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]
    exact ⟨retTy_persistent S A R, clausesTyB_persistent S R d E fs⟩
  have hρ' : ρ' = PMap.empty := vP_empty_of_persistent hT₀ hv
  subst hρ'
  obtain ⟨vr, vc, h⟩ := hv
  obtain ⟨hpair, σ₁, σ₂, -, hVr, hVc⟩ := pure_sep_iff.mp h
  have hσ₁ : σ₁ = PMap.empty := vP_empty_of_persistent (retTy_persistent S A R) hVr
  have hσ₂ : σ₂ = PMap.empty :=
    vP_empty_of_persistent (clausesTyB_persistent S R d E fs) hVc
  subst hσ₁ hσ₂
  have hHe : substAll γ H = (Val.pair vr vc).1 := congrArg Subtype.val hpair
  rw [hHe]
  exact ewp_unfold (opTable_mono _) (ewp_handle_valsB hdα hS hn0 hnS hlen hVr hVc hE')
    ρf fρ ps hf hcf hT htg Al k

end BoCa.Fig16.LogRel.Core

end
