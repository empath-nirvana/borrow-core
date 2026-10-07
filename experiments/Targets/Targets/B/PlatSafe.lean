import Targets.B.Adequacy

/-!
# System B — runs under a platform that answers part of the row

`platOK_of_ewp` reads Core's relation at a row the platform answers (`RowLe S P.ops`).  A run
under a platform that answers only part of the row goes on until it stops at an operation of the
row the platform does not answer: a raise, or a `perform` the platform lacks.  The platform's
operations must be the row's, at the row's types (`PlatAgree`), since an answer is read at the
type the row declares.

* `platSafe_of_ewp`: from a start in Core's relation, every run continues to an end in the
  postcondition or to a stop of the row the platform does not answer.  Induction on `ewpTS`'s least
  fixed point (`ewp_ind`), each segment to `wpG`'s end (`wpG_seg`) and each answer through the
  continuation's share (`answer_at_stop_agree`), as `platOK_of_ewp`.
* `safeDriveFrom_of_rel`: B2's drive from the drive phase, when the loop's row is below the step's
  and the platform answers the step's row.
* `DriveSafe`, `driveSafe_step`, `driveSafe_cont`: the drive from the drive phase under a
  platform that answers part of the row.

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The platform answers an operation of the row `S` only at the row's entry. -/
def PlatAgree (P : Platform) (S : Row) : Prop :=
  ∀ n i o o', Row.find S n i = some o → Row.find P.ops n i = some o' → o = o'

/-- A platform whose operations are the row's agrees with every row below. -/
theorem platAgree_of_le {P : Platform} {S T : Row}
    (hsub : ∀ n i o, Row.find P.ops n i = some o → Row.find S n i = some o) (hle : RowLe T S) :
    PlatAgree P T :=
  fun n i _ _ hT hP => Option.some.inj ((hle n i _ hT).symm.trans (hsub n i _ hP))

/-- **A stop the platform does not answer**, at an operation of the row `S`: an operation its
context leaves uncaught, `S` finds it, a raise exactly when the operation is abortive, and a raise
or a `perform` the platform lacks. -/
def UnansweredAt (P : Platform) (S : Row) (e : Expr) : Prop :=
  ∃ (r : Bool) (K : Kont) (n i : UInt32) (v : Val) (o : OpSig),
    e = K.plug (opE r (opPayload n i v)) ∧ OpFree r n K ∧ Row.find S n i = some o ∧
      o.abort = r ∧ (r = false → Row.find P.ops n i = none)

/-- A stop of a row is a stop of every larger row. -/
theorem unansweredAt_mono {P : Platform} {T S : Row} (hle : RowLe T S) {e : Expr}
    (h : UnansweredAt P T e) : UnansweredAt P S e := by
  obtain ⟨r, K, n, i, v, o, he, hK, hf, hab, hP⟩ := h
  exact ⟨r, K, n, i, v, o, he, hK, hle n i o hf, hab, hP⟩

section Plat
variable (P : Platform) (S : Row) (Q : List SRec → Val → WProp)

/-- **Every run under `P` from `e` continues to an end in `Q` or to a stop of `S` that `P` does not
answer**: from every frame that owns nothing and every platform state. -/
def PlatSafe (ls : List SRec) (e : Expr) (ρ : WRes) : Prop :=
  ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap) (s : P.St),
    NoOwn ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
    ResU.Lower fρ μ → ResU.UpdV PMap.empty fρ →
    ∀ c, PSteps (ℍ := ℍ) P ⟨μ, e, s⟩ c →
      ∃ c', PSteps (ℍ := ℍ) P c c' ∧ (PlatEnd P Q c' ∨ UnansweredAt P S c'.e)

end Plat

section Answer
variable {P : Platform} {Q : List SRec → Val → WProp}

/-- **The answer at a stop the platform answers**, at a platform that agrees with the row: the
operation is the platform's, its argument is data, and the continuation's share resumes `K` at
every answer of the operation's answer type, at the post's own resource. -/
theorem answer_at_stop_agree (hP : P.Respects) {S : Row} (hag : PlatAgree P S) {δ : LSub}
    {Φ : List SRec → Expr → WProp} {ls : List SRec} {K : Kont} {n i : UInt32} {v : Val}
    {ρ : WRes} {o : OpSig} (hfP : Row.find P.ops n i = some o)
    (h : opTable (Row.tab S δ) ls (K.plug (performE (.val (opPayload n i v)))) Φ ρ) :
    K.HasHnd n = false ∧ DataVal o.A v ∧ ∀ w, DataVal o.B w → Φ ls (K.plug (.val w)) ρ := by
  rcases h with ⟨K', n', i', v', en, hp⟩ | ⟨K', n', i', v', en, hp⟩
  · obtain ⟨⟨he, hK, hT, -⟩, ρ₁, ρ₂, hc, hA, hshare⟩ := pure_sep_iff.mp hp
    obtain ⟨hK', hpay⟩ := plug_perform_inj he
    obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
    subst hK'
    obtain ⟨oS, hfS, rfl⟩ := Row.tab_some hT
    obtain rfl := hag n i oS o hfS hfP
    have hm := (Row.find_mem hfP).1
    obtain ⟨hdA, hdB⟩ := hP.data oS hm
    obtain ⟨rfl, hv⟩ := (vC_data hdA).mp hA
    obtain rfl := eq_of_compS_empty_left hc
    refine ⟨hK, hv, fun w hw => ?_⟩
    exact (hshare.2 ls (Ext.refl ls ρ)).1 w PMap.empty ρ ((vC_data hdB).mpr ⟨rfl, hw⟩)
      (ResU.comp_empty_right ρ)
  · obtain ⟨⟨he, -⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd he (plug_perform_ne_raise K K' _ _)

end Answer

/-- A stop of the row's table at a `perform` the platform lacks, or at a raise, is a stop the
platform does not answer. -/
theorem unanswered_of_table {P : Platform} {S : Row} {δ : LSub} {Φ : List SRec → Expr → WProp}
    {ls : List SRec} {t : Expr} {ρ : WRes} (h : opTable (Row.tab S δ) ls t Φ ρ)
    (hna : ∀ (K : Kont) (n i : UInt32) (v : Val), t = K.plug (performE (.val (opPayload n i v))) →
      Row.find P.ops n i = none) :
    UnansweredAt P S t := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK, hT, hab⟩, -⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact ⟨false, K, n, i, v, o, rfl, hK, hf, hab, fun _ => hna K n i v rfl⟩
  · obtain ⟨⟨rfl, hK, hT, hab⟩, -⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact ⟨true, K, n, i, v, o, rfl, hK, hf, hab, fun h => absurd h (by simp)⟩

/-- **Every run under a platform that agrees with the row, from a program in the relation, ends in
its postcondition or at a stop of the row the platform does not answer.**  Induction on `ewpTS`'s
least fixed point: each segment continues to `wpG`'s end (`wpG_seg`); at a stop the platform
answers, the answer resumes `K` at a configuration of the induction hypothesis
(`answer_at_stop_agree`), framed by the segment's leftover (`seg_frame`). -/
theorem platSafe_of_ewp {P : Platform} {Q : List SRec → Val → WProp} (hP : P.Respects) {S : Row}
    (hag : PlatAgree P S) {δ : LSub} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS (ℍ := ℍ) ls e (opTable (Row.tab S δ)) Q ρ) : PlatSafe (ℍ := ℍ) P S Q ls e ρ := by
  refine ewp_ind (PlatSafe P S Q) ?_ h
  intro ls e ρ hw ρf fρ ps μ s hno hf hc hT htg hμ hU
  have hirr : ∀ ls' t ρ', (valPost Q ls' t ρ' ∨ opTable (Row.tab S δ) ls' t (PlatSafe P S Q) ρ') →
      ∀ μ₁ μ₂ e₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ e₂ := fun _ _ _ hp => post_irr hp
  -- a segment to its end, with the frame regrouped
  have hseg : ∀ {μ₁ : Heap} {e₁ : Expr}, Steps (ℍ := ℍ) μ e μ₁ e₁ →
      ∃ (t : Expr) (μ' : Heap) (ls' : List SRec) (ρ' z fρ'p : WRes) (ps' : List FrameRec),
        Steps (ℍ := ℍ) μ₁ e₁ μ' t ∧ NoOwn z ∧ ResU.Hash z ρ' ∧ ResU.CompS z ρ' fρ'p ∧
        TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧ ResU.Lower fρ'p μ' ∧
        ResU.UpdV PMap.empty fρ'p ∧
        (valPost Q ls' t ρ' ∨ opTable (Row.tab S δ) ls' t (PlatSafe P S Q) ρ') := by
    intro μ₁ e₁ hst
    obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ', ps', ls', -, h₂, h₃, h₅, h₆, h₇, h₈, h₉, h₁₀, hT', htg',
      -, -, hΦ⟩ := wpG_seg hw hirr hf hc hT htg hμ hst
    have hv : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h₆; exact ⟨σ, hσ⟩
    obtain ⟨z, hz, hzh, hzc, hzU⟩ := seg_frame hno hU hf hc h₂ h₃ h₅ h₈ h₉ h₁₀ hv
    exact ⟨t, μ', ls', ρ', z, fρ'p, ps', h₇, hz, hzh, hzc, hT', htg', h₆, hzU, hΦ⟩
  -- the end of a segment: a value in `Q`, a stop the platform does not answer, or an answer and
  -- the induction hypothesis from there
  have hend : ∀ {t : Expr} {μ' : Heap} {ls' : List SRec} {ρ' z fρ'p : WRes} {ps' : List FrameRec}
      (s' : P.St), NoOwn z → ResU.Hash z ρ' → ResU.CompS z ρ' fρ'p → TW fρ'p ps' (rsOf ls') →
      Tagged fρ'p ps' ls' → ResU.Lower fρ'p μ' → ResU.UpdV PMap.empty fρ'p →
      (valPost Q ls' t ρ' ∨ opTable (Row.tab S δ) ls' t (PlatSafe P S Q) ρ') →
      ∃ c', PSteps (ℍ := ℍ) P ⟨μ', t, s'⟩ c' ∧ (PlatEnd P Q c' ∨ UnansweredAt P S c'.e) := by
    intro t μ' ls' ρ' z fρ'p ps' s' hz hzh hzc hT' htg' h₆ hzU hΦ
    rcases hΦ with ⟨w, rfl, hQ⟩ | hop
    · exact ⟨_, .refl, .inl ⟨w, ls', ρ', z, fρ'p, ps', rfl, hQ, hz, hzh, hzc, hT', htg', h₆, hzU⟩⟩
    · by_cases hans : ∃ (K : Kont) (n i : UInt32) (v : Val) (o : OpSig),
          t = K.plug (performE (.val (opPayload n i v))) ∧ Row.find P.ops n i = some o
      · obtain ⟨K, n, i, v, o, rfl, hfP⟩ := hans
        obtain ⟨hK, hdA, hres⟩ := answer_at_stop_agree hP hag hfP hop
        have hm := (Row.find_mem hfP).1
        obtain ⟨w, s₁, hco₀⟩ := hP.total s' o v hm hdA
        have hdB : DataVal o.B w := hP.typed s' s₁ o v w hm hdA hco₀
        have hco : P.co s' n i v = some (w, s₁) := by
          rw [← (Row.find_mem hfP).2.1, ← (Row.find_mem hfP).2.2]; exact hco₀
        obtain ⟨c', hc', hend⟩ := hres w hdB z fρ'p ps' μ' s₁ hz hzh hzc hT' htg' h₆ hzU _ .refl
        exact ⟨c', .head (PStep.plat hK hfP hco) hc', hend⟩
      · refine ⟨_, .refl, .inr (unanswered_of_table hop fun K n i v ht => ?_)⟩
        cases hf : Row.find P.ops n i with
        | none => rfl
        | some o => exact absurd ⟨K, n, i, v, o, ht, hf⟩ hans
  intro c hcs
  rcases psteps_split hcs with ⟨hst, hss⟩ | ⟨μ₁, K, n, i, v, w, s₁, o, hst, hK, hfo, hco, hrest⟩
  · obtain ⟨cμ, ce, cs⟩ := c
    simp only at hst hss
    rw [hss]
    obtain ⟨t, μ', ls', ρ', z, fρ'p, ps', h₇, hz, hzh, hzc, hT', htg', h₆, hzU, hΦ⟩ := hseg hst
    obtain ⟨c', hc', hfin⟩ := hend s hz hzh hzc hT' htg' h₆ hzU hΦ
    exact ⟨c', (psteps_of_steps P s h₇).trans hc', hfin⟩
  · obtain ⟨t, μ', ls', ρ', z, fρ'p, ps', h₇, hz, hzh, hzc, hT', htg', h₆, hzU, hΦ⟩ := hseg hst
    cases h₇ with
    | more h _ => exact absurd h (opPlug_no_step (r := false) (payloadName_opPayload n i v) hK)
    | refl =>
        rcases hΦ with ⟨w', hw', -⟩ | hop
        · exact absurd hw' (plug_perform_ne_val K _ w')
        · obtain ⟨-, hdA, hres⟩ := answer_at_stop_agree hP hag hfo hop
          have hdB : DataVal o.B w := hP.typed s s₁ o v w (Row.find_mem hfo).1 hdA
            (by rw [(Row.find_mem hfo).2.1, (Row.find_mem hfo).2.2]; exact hco)
          exact hres w hdB z fρ'p ps' μ₁ s₁ hz hzh hzc hT' htg' h₆ hzU c hrest

/-- `PlatSafe` from the empty configuration. -/
theorem platSafe_init {P : Platform} {S : Row} {Q : List SRec → Val → WProp} {e : Expr}
    (h : PlatSafe (ℍ := ℍ) P S Q [] e PMap.empty) :
    ∀ c, PSteps (ℍ := ℍ) P (init P e) c →
      ∃ c', PSteps (ℍ := ℍ) P c c' ∧ (PlatEnd P Q c' ∨ UnansweredAt P S c'.e) :=
  h PMap.empty PMap.empty [] Adequacy.emptyMem P.s₀ noOwn_empty Fig16.LogRel.hash_empty
    (ResU.comp_empty_right _) TW.empty (fun x hx => absurd hx (by simp)) Fig16.BoLo.lower_empty
    ((ResU.updV_self_iff _).mpr Fig16.LogRel.valid_empty)

/-- From a start, under a platform that agrees with the row, every run continues to an end in `Q`
or to a stop the platform does not answer. -/
theorem platStart_safe {P : Platform} (hP : P.Respects) {T : Row} (hag : PlatAgree P T)
    {Q : List SRec → Val → WProp} {c₀ c : Conf P} (h₀ : PlatStart P T Q c₀)
    (hc : PSteps (ℍ := ℍ) P c₀ c) :
    ∃ c', PSteps (ℍ := ℍ) P c c' ∧ (PlatEnd P Q c' ∨ UnansweredAt P T c'.e) := by
  obtain ⟨ls, ρ, ρf, fρ, ps, hno, hf, hcm, hT, htg, hμ, hU, hw⟩ := h₀
  exact (platSafe_of_ewp hP hag hw) ρf fρ ps c₀.μ c₀.s hno hf hcm hT htg hμ hU c hc

/-! ### The drive from the drive phase -/

section Drive
variable {P : Platform} {S S₀ : Row} {A : VTy}

/-- **The drive's invariant from the drive phase**: the configuration is reached from a start of a
loop's step, at a row below the step's row `S`, its post the loop's at `S₀`. -/
def DriveSafe (P : Platform) (S S₀ : Row) (A : VTy) (rc : Conf P × Phase) : Prop :=
  rc.2 = .drive ∧ ∃ (T : Row) (c₀ : Conf P), RowLe T S ∧
    PlatStart P T (QStep S₀ A .unit) c₀ ∧ PSteps (ℍ := ℍ) P c₀ rc.1

/-- The drive's invariant at its start: the step in Core's relation at
`F_S(A ⊕ U(Loop_{S₀} A 1))`. -/
theorem driveSafe_init {M : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.sum A (.thunk (CTy.loopEff S₀ A .unit)))) [] LSub.empty M
      PMap.empty) :
    DriveSafe (ℍ := ℍ) P S S₀ A (init P M, .drive) :=
  ⟨rfl, S, init P M, fun _ _ _ hf => hf,
    platStart_init ((cC_effOf S _ [] LSub.empty M PMap.empty).mp h), .refl⟩

/-- **The invariant is kept by every step of the drive**, under a platform whose operations are the
step's row's: a step under the platform extends the run; `again` acts at `inr l`, an end of the
run (a value takes no step), and starts the next step at the loop's row (`platStart_inr`). -/
theorem driveSafe_step (hP : P.Respects)
    (hsub : ∀ n i o, Row.find P.ops n i = some o → Row.find S n i = some o) (hle : RowLe S₀ S)
    (hC : (CTy.loopEffBody S₀ A .unit).NuOk) {rc rc' : Conf P × Phase}
    (h : DriveSafe (ℍ := ℍ) P S S₀ A rc) (hs : RStep (ℍ := ℍ) P rc rc') :
    DriveSafe (ℍ := ℍ) P S S₀ A rc' := by
  obtain ⟨hph, T, c₀, hT, h₀, hr⟩ := h
  rcases rstep_cases hs with ⟨hp, hph'⟩ | ⟨hph', -⟩ | ⟨-, l, he, rfl⟩
  · exact ⟨hph'.trans hph, T, c₀, hT, h₀, hr.tail hp⟩
  · rw [hph] at hph'; cases hph'
  · obtain ⟨c', hc', hend | hun⟩ := platStart_safe hP (platAgree_of_le hsub hT) h₀ hr
    · obtain rfl := psteps_from_val he hc'
      exact ⟨rfl, S₀, _, hle, platStart_inr hC he hend, .refl⟩
    · obtain rfl := psteps_from_val he hc'
      obtain ⟨r, K, n, i, v, o, he', -⟩ := hun
      have hv : IsVal (K.plug (opE r (opPayload n i v))) := by rw [← he', he]; exact (Val.inj₂ l).2
      exact absurd (K.isVal_of_plug hv) (opE_not_isVal r _)

/-- **Every configuration of the drive goes on**: it continues, by steps under the platform, to an
end of a step (`inl a` or `inr l` in the loop's post) or to a stop of the step's row that the
platform does not answer. -/
theorem driveSafe_cont (hP : P.Respects)
    (hsub : ∀ n i o, Row.find P.ops n i = some o → Row.find S n i = some o)
    {rc : Conf P × Phase} (h : DriveSafe (ℍ := ℍ) P S S₀ A rc) :
    ∃ c', PSteps (ℍ := ℍ) P rc.1 c' ∧
      (PlatEnd P (QStep S₀ A .unit) c' ∨ UnansweredAt P S c'.e) := by
  obtain ⟨-, T, c₀, hT, h₀, hr⟩ := h
  obtain ⟨c', hc', hend | hun⟩ := platStart_safe hP (platAgree_of_le hsub hT) h₀ hr
  · exact ⟨c', hc', .inl hend⟩
  · exact ⟨c', hc', .inr (unansweredAt_mono hT hun)⟩

end Drive

/-- The drive's invariant at every configuration the drive reaches from its start. -/
theorem driveSafe_of_reach {P : Platform} (hP : P.Respects) {S S₀ : Row} {A : VTy}
    (hsub : ∀ n i o, Row.find P.ops n i = some o → Row.find S n i = some o) (hle : RowLe S₀ S)
    (hC : (CTy.loopEffBody S₀ A .unit).NuOk) {M : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.sum A (.thunk (CTy.loopEff S₀ A .unit)))) [] LSub.empty M
      PMap.empty)
    {rc : Conf P × Phase} (hr : Relation.ReflTransGen (RStep (ℍ := ℍ) P) (init P M, .drive) rc) :
    DriveSafe (ℍ := ℍ) P S S₀ A rc := by
  induction hr with
  | refl => exact driveSafe_init h
  | tail _ hs ih => exact driveSafe_step hP hsub hle hC ih hs

/-- A step's answer is `inl a` or `inr l`. -/
theorem inl_or_inr_of_qStep {S : Row} {A B : VTy} {ls : List SRec} {v : Val} {ρ : WRes}
    (h : QStep (ℍ := ℍ) S A B ls v ρ) : (∃ a, v = Val.inj₁ a) ∨ ∃ l, v = Val.inj₂ l := by
  rcases h with ⟨a, hp⟩ | ⟨l, hp⟩
  · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
    exact .inl ⟨a, rfl⟩
  · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
    exact .inr ⟨l, rfl⟩

/-- The drive's invariant is kept under a platform that answers the step's row: `again` acts at
`inr l`, an end of the run (`platStart_cont`), and starts the next step at the loop's row. -/
theorem driveSafe_step_le {P : Platform} (hP : P.Respects) {S S₀ : Row} {A : VTy}
    (hle : RowLe S P.ops) (hS₀ : RowLe S₀ S) (hC : (CTy.loopEffBody S₀ A .unit).NuOk)
    {rc rc' : Conf P × Phase} (h : DriveSafe (ℍ := ℍ) P S S₀ A rc)
    (hs : RStep (ℍ := ℍ) P rc rc') : DriveSafe (ℍ := ℍ) P S S₀ A rc' := by
  obtain ⟨hph, T, c₀, hT, h₀, hr⟩ := h
  rcases rstep_cases hs with ⟨hp, hph'⟩ | ⟨hph', -⟩ | ⟨-, l, he, rfl⟩
  · exact ⟨hph'.trans hph, T, c₀, hT, h₀, hr.tail hp⟩
  · rw [hph] at hph'; cases hph'
  · obtain ⟨c', hc', hend⟩ := platStart_cont hP (fun n i o hf => hle n i o (hT n i o hf)) h₀ hr
    obtain rfl := psteps_from_val he hc'
    exact ⟨rfl, S₀, _, hS₀, platStart_inr hC he hend, .refl⟩

/-- **B2's drive from the drive phase, at a step whose loop's row is below its own**: at a positive
loop body and a platform that answers the step's row, every finite prefix of the drive of a step in
Core's relation at `F_S(A ⊕ U(Loop_{S₀} A 1))` is safe, a finished drive at a data answer with the
memory empty. -/
theorem safeDriveFrom_of_rel {P : Platform} (hP : P.Respects) {S S₀ : Row} {A : VTy}
    (hle : RowLe S P.ops) (hS₀ : RowLe S₀ S) (hA : A.Data) (hC : (CTy.loopEffBody S₀ A .unit).NuOk)
    {M : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.sum A (.thunk (CTy.loopEff S₀ A .unit)))) [] LSub.empty M
      PMap.empty) :
    SafeDriveFrom (ℍ := ℍ) P A M := by
  intro rc hrc
  have hinv : DriveSafe (ℍ := ℍ) P S S₀ A rc := by
    induction hrc with
    | refl => exact driveSafe_init h
    | tail _ hs ih => exact driveSafe_step_le hP hle hS₀ hC ih hs
  obtain ⟨⟨μ, e, s⟩, ph⟩ := rc
  obtain ⟨hph, T, c₀, hT, h₀, hr⟩ := hinv
  simp only at hph
  subst hph
  obtain ⟨c', hc', hend⟩ := platStart_cont hP (fun n i o hf => hle n i o (hT n i o hf)) h₀ hr
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · obtain ⟨v, ls, ρ, -, -, -, he, hQ, -⟩ := id hend
    simp only at he
    subst he
    rcases hQ with ⟨a, hp⟩ | ⟨l, hp⟩
    · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
      exact Or.inl (finalDrive_of_inl hA rfl hend)
    · obtain ⟨rfl, -⟩ := pure_sep_iff.mp hp
      exact Or.inr ⟨_, .again⟩
  · exact Or.inr ⟨(c₁, .drive), .run h₁⟩

end Targets

end
