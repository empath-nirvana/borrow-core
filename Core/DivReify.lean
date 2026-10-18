import Core.DivFuel

/-!
# Core — `reify`  `[spec §14]`

    reify_res : !U(U(F_{tick, Σ}(B ⊕ R)) ⊸ F_Σ U(Loop_Σ B R))        res : !U(B ⊸ F_Σ R)

`reify_res t` makes a loop value of the computation `t ()`: it runs it to its first tick, or to its
end, and answers the loop there.  It is a deep handler of `Div`:

    reify_res t    ≜  (hnd_Div H (t ())) to x. case x { inl b → done b | inr L → L }
    h_ret v        =  case v { inl b → inl b | inr r → inr (closed r) }
    h_tick ((), κ) =  inr ⟨ next ↦ κ next,  close ↦ (κ close) to x. case x { inl b → res b
                                                                      | inr L → L.close } ⟩

* `done b` finishes at its first observation with `b`; closed, it hands back `res b`.  `res` is
  the residual of a result, read off its type (SPEC §14 *The residual*): what `B` holds with no
  destructor.  It is a closed term of the constant, typed at the empty context.
* `closed r` is the loop of a computation that ended with its residual: every *next* skips, and
  *close* hands `r` back.
* At a tick the handler answers the loop whose *next* resumes `κ` with *next*, which runs the
  next segment under the same handler and answers the next loop, and whose *close* resumes `κ`
  with *close*.  After a close the computation reaches a tick again or its end; at a tick, that
  loop's *close* is taken in turn.  `Closing` bounds those ticks.

`reify_compat`: for a computation of `cwp` at `𝒱⟦B ⊕ R⟧`, `reify` answers a value of
`𝒱⟦U(Loop_Σ B R)⟧` (`Core/NuRel.lean`), by coinduction with the candidate of the three loop
values.  Its observations are two lemmas by induction: a segment under the handler at *next*
(`reify_next`, on the segment's least fixed point), and a close (`reify_close`, on `Closing`'s).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappaC kappaCell kappaAt clauseAt capTag freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The loop values -/

/-- `closed`'s body under the loop itself (`1`) and the residual (`0`):
`λsel. case sel { next → inr (self r) | close → r }`. -/
def clB : Expr := .val (.lam (.case (.var 0) (.inj₂ (.app (.var 3) (.var 2))) (.var 2)))

theorem clB_closed : closedAt 2 clB = true := rfl

/-- `closed`, a closed value. -/
def clV : Val := selfV clB

/-- `closed r`, the loop that skips until it is closed and then hands back `r`. -/
def clLoop (r : Val) : Val :=
  ⟨(clB.subst 1 ((selfV clB).shift 1 0)).subst 0 r, by
    simp only [clB]; exact IsVal.subst (IsVal.subst .lam _ _) _ _⟩

/-- `done`'s body under `b` (`1`) and the observation (`0`). -/
def dlX (res : Val) : Expr :=
  .case (.var 0) (.inj₁ (.var 2)) (.app (.val res) (.var 2))

/-- `done b`: finishes at its first observation with `b`; closed, `res b`. -/
def doneLoop (res b : Val) : Val := .lam ((dlX res).subst 1 (b.shift 1 0))

/-- The close of a loop made at a tick: `λx. case x { inl b → res b | inr L → L.close }`. -/
def closeKV (res : Val) : Val :=
  .lam (.case (.var 0) (.app (.val res) (.var 0)) (.app (.var 0) (.val closeV)))

/-- The loop made at a tick, under `κ` (`1`) and the observation (`0`). -/
def tlX (res : Val) : Expr :=
  .case (.var 0)
    (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.val nextV))
    (.app (.val (closeKV res)) (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.val closeV)))

/-- The loop made at a tick, at the continuation `κ`. -/
def tickLoop (res κ : Val) : Val := .lam ((tlX res).subst 1 (κ.shift 1 0))

/-! ### The handler -/

/-- `h_ret = λv. case v { inl b → inl b | inr r → inr (closed r) }`. -/
def reifyR : Val := .lam (.case (.var 0) (.inj₁ (.var 0)) (.inj₂ (.app (.val clV) (.var 0))))

/-- The tick's clause `λ((), κ). inr (tickLoop κ)`. -/
def reifyC (res : Val) : Val := .lam (.letpair (.var 0) (.inj₂ (.val (.lam (tlX res)))))

/-- The handler value: the name `Div`, the tick linear. -/
def reifyH (res : Val) : Val :=
  hndVal divEff (qualsVal [.lin]) reifyR (Val.pair (reifyC res) .unit)

/-- `λx. case x { inl b → done b | inr L → L }`. -/
def rkV (res : Val) : Val := .lam (.case (.var 0) (.val (.lam (dlX res))) (.var 0))

/-- **`reify_res`**: `λt. rk (hnd_Div H (t ()))`.  `[spec §14]` -/
def reifyV (res : Val) : Val :=
  .lam (.app (.val (rkV res)) (hndE (reifyH res) (.app (.var 0) (.val .unit))))

/-- The frame of a close: `[·] to x. case x { inl b → res b | inr L → L.close }`. -/
def closeK (res : Val) : Kont := .appR (.val (closeKV res)) .hole

/-! ### The steps -/

section steps
variable (res : Val) (hres : closedAt 0 res.1 = true)

theorem clV_steps (r : Val) : PureSteps (.app (.val clV) (.val r)) (.val (clLoop r)) := by
  refine (selfV_steps_in clB_closed .hole r).trans ?_
  exact PureSteps.beta _ r

theorem clLoop_next (r : Val) :
    PureSteps (.app (.val (clLoop r)) (.val nextV)) (.val (Val.inj₂ (clLoop r))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  have hc : closedAt 0 (selfV clB).1 = true := selfV_closed clB_closed
  simp only [clB]
  simp [closed_subst hc, closed_shift hc, subst_shift_succ]
  exact PureSteps.plug (.inj₂ .hole) (clV_steps r)

theorem clLoop_close (r : Val) :
    PureSteps (.app (.val (clLoop r)) (.val closeV)) (.val r) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  have hc : closedAt 0 (selfV clB).1 = true := selfV_closed clB_closed
  simp only [clB]
  generalize selfV clB = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc, subst_shift_succ]
  exact .refl

include hres in
theorem doneLoop_next (b : Val) :
    PureSteps (.app (.val (doneLoop res b)) (.val nextV)) (.val (Val.inj₁ b)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  simp [dlX, closed_subst hres, closed_shift hres, subst_shift_succ]
  exact .refl

include hres in
theorem doneLoop_close (b : Val) :
    PureSteps (.app (.val (doneLoop res b)) (.val closeV)) (.app (.val res) (.val b)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  simp [dlX, closed_subst hres, closed_shift hres, subst_shift_succ]
  exact .refl

include hres in
theorem closeKV_inl (b : Val) :
    PureSteps (.app (.val (closeKV res)) (.val (Val.inj₁ b))) (.app (.val res) (.val b)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ b _ _) rfl).trans ?_
  simp [closed_subst hres, closed_shift hres, subst_shift_succ]
  exact .refl

include hres in
theorem closeKV_inr (L : Val) :
    PureSteps (.app (.val (closeKV res)) (.val (Val.inj₂ L))) (.app (.val L) (.val closeV)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ L _ _) rfl).trans ?_
  simp [closed_subst hres, closed_shift hres, subst_shift_succ, closeV]
  exact .refl

theorem closeKV_closed : closedAt 0 res.1 = true → closedAt 0 (closeKV res).1 = true := fun h => by
  simp [closeKV, closedAt, closedAt_mono _ h (Nat.zero_le _), closeV]

include hres in
theorem tickLoop_next (κ : Val) :
    PureSteps (.app (.val (tickLoop res κ)) (.val nextV))
      (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val nextV)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  have hk := closeKV_closed res hres
  simp [tlX, closed_subst hk, closed_shift hk, subst_shift_succ, nextV]
  exact .refl

include hres in
theorem tickLoop_close (κ : Val) :
    PureSteps (.app (.val (tickLoop res κ)) (.val closeV))
      ((closeK res).plug (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val closeV))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  have hk := closeKV_closed res hres
  simp [tlX, closeK, Kont.plug, closed_subst hk, closed_shift hk, subst_shift_succ, closeV]
  exact .refl

include hres in
theorem reifyC_steps (κ : Val) :
    PureSteps (.app (.val (reifyC res)) (.val (Val.pair .unit κ)))
      (.val (Val.inj₂ (tickLoop res κ))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ .unit κ _) rfl).trans ?_
  have hk := closeKV_closed res hres
  simp [tlX, tickLoop, closed_subst hk, closed_shift hk, subst_shift_succ, closeV, nextV]
  exact .refl

include hres in
theorem rkV_inl (b : Val) :
    PureSteps (.app (.val (rkV res)) (.val (Val.inj₁ b))) (.val (doneLoop res b)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ b _ _) rfl).trans ?_
  simp [dlX, doneLoop, closed_subst hres, closed_shift hres, subst_shift_succ]
  exact .refl

theorem rkV_inr (L : Val) :
    PureSteps (.app (.val (rkV res)) (.val (Val.inj₂ L))) (.val L) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ L _ _) rfl).trans ?_
  simp [subst_shift_succ]
  exact .refl

theorem reifyR_inl (b : Val) :
    PureSteps (.app (.val reifyR) (.val (Val.inj₁ b))) (.val (Val.inj₁ b)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ b _ _) rfl).trans ?_
  simp [subst_shift_succ]
  exact .refl

theorem reifyR_inr (r : Val) :
    PureSteps (.app (.val reifyR) (.val (Val.inj₂ r))) (.val (Val.inj₂ (clLoop r))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ r _ _) rfl).trans ?_
  have hc : closedAt 0 clV.1 = true := selfV_closed clB_closed
  simp [closed_subst hc, closed_shift hc, subst_shift_succ]
  exact PureSteps.plug (.inj₂ .hole) (clV_steps r)

end steps

/-! ### The relation at a row's layers -/

theorem effRetE_effOf (η : Option (Nat → TEnt)) (δ : LSub) : ∀ (S : Row) (A : VTy),
    effRetE η (CTy.effOf S A) δ = fun ls v => vCE η true A ls δ v
  | [], A => by simp [CTy.effOf, effRetE]
  | _ :: S, A => by simp only [CTy.effOf, effRetE]; exact effRetE_effOf η δ S A

/-- `cC_effOf` at one unfolding, at a row that does not hold `Div`. -/
theorem cB_effOf (η : Option (Nat → TEnt)) (S : Row) (hS : Row.divB S = false) (A : VTy)
    (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cB η (CTy.effOf S A) ls δ e ρ ↔
      ewpTS ls e (opTable (Row.tab S δ)) (fun ls v => vCE η true A ls δ v) ρ := by
  cases S with
  | nil =>
      have hT : Row.tab [] δ = OpTab.empty := by
        funext n i; simp [Row.tab, Row.find, OpTab.empty]
      rw [hT]
      show wpTS ls e _ ρ ↔ _
      constructor
      · intro h; exact ewp_of_wp (opTable_mono _) h
      · intro h
        exact ewp_bot.mp (ewp_mono (fun _ _ _ _ _ _ h => h)
          (fun _ _ _ _ h => (opTable_empty h).elim) (fun _ _ _ h => h) h)
  | cons o S =>
      have h := effTab_effOf δ (o :: S) A
      have hd := divAt_effOf (o :: S) A
      simp only [CTy.effOf, effTab] at h hd
      simp only [CTy.effOf, cB]
      rw [h, effRetE_effOf, hd, hS]
      rfl

/-- A type without the variable reads the same in `νX. C`'s environment. -/
theorem vCE_nuEnv_rename (C : CTy) (R : CPred) (δ : LSub) (b : Bool) (A : VTy)
    (ls : List SRec) : vCE (some (nuEnv C R)) b (A.rename Nat.succ) ls δ = vC b A ls δ := by
  rw [← vCE_envS_nuEnv (VTy.not_occ_rename_succ A) .unit δ C R b, ← vC_inst_envS,
    VTy.inst_rename_succ]

theorem nuAns_inl {C : CTy} {R : CPred} {δ : LSub} {A : VTy} {ls : List SRec} {b : Val}
    {ρ : WRes} (h : vC true A ls δ b ρ) :
    vCE (some (nuEnv C R)) true (.sum (A.rename Nat.succ) (.tvar 0)) ls δ (Val.inj₁ b) ρ :=
  Or.inl ⟨b, PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩,
    by rw [vCE_nuEnv_rename]; exact h⟩

theorem nuAns_inr {C : CTy} {R : CPred} {δ : LSub} {A : VTy} {ls : List SRec} {L : Val}
    {ρ : WRes} (h : thunkR R ls L ρ) :
    vCE (some (nuEnv C R)) true (.sum (A.rename Nat.succ) (.tvar 0)) ls δ (Val.inj₂ L) ρ :=
  Or.inr ⟨L, PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, rfl⟩, h⟩

theorem closeK_plain (res : Val) :
    (∀ n, (closeK res).HasHnd n = false) ∧ (∀ n, (closeK res).Catches n = false) :=
  ⟨fun n => by simp [closeK, Kont.HasHnd, closeKV], fun n => by simp [closeK, Kont.Catches, closeKV]⟩

theorem closeK_dead (res : Val) : (closeK res).dead = closeK res := by
  simp [closeK, Kont.dead, Kont.DeadFrame, closeKV]

/-! ### The candidate and its observations -/

section rel
variable {δ : LSub} {S : Row} (hS : ∀ o ∈ S, o.n ≠ divEff) {B R : VTy} (res : Val)
  (hres : closedAt 0 res.1 = true)
  (hresR : ∀ ls b ρ, vC true B ls δ b ρ →
    ewpTS ls (.app (.val res) (.val b)) (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ)

/-- The relation of the handled computation's answers, `𝒱⟦B ⊕ R⟧`. -/
abbrev mPost (δ : LSub) (B R : VTy) : List SRec → Val → WProp :=
  fun ls v => vC true (.sum B R) ls δ v

/-- **The candidate** for `Loop_Σ B R`: a loop made at a tick, whose cell it owns and whose
continuation is at every answer in `cwp` and in `Closing`; `done b`; `closed r`. -/
def candR (δ : LSub) (S : Row) (B R : VTy) (res : Val) : CPred := fun ls e ρ =>
  (∃ ℓ K₁ ρc ρk, e = .val (tickLoop res (kapV ℓ (reifyH res) K₁)) ∧ ResU.CompS ρc ρk ρ ∧
    ptoOwn ℓ .unit ρc ∧ ∀ ls', Ext ls ls' ρk → ∀ w : Val, w = nextV ∨ w = closeV →
      owe (Row.tab (tickSig :: S) δ) (mPost δ B R) (cwp (Row.tab (tickSig :: S) δ) (mPost δ B R)) ls'
        (K₁.plug (.val w)) ρk) ∨
  (∃ b, e = .val (doneLoop res b) ∧ vC true B ls δ b ρ) ∨
  (∃ r, e = .val (clLoop r) ∧ vC true R ls δ r ρ)

/-- A stop of the full row but the tick is one of the rest of the row. -/
theorem opTable_rest {ls : List SRec} {t : Expr} {Φ : List SRec → Expr → WProp} {ρ : WRes}
    (h : opTable (Row.tab (tickSig :: S) δ).erase0 ls t Φ ρ) : opTable (Row.tab S δ) ls t Φ ρ := by
  refine opTable_le (fun n i en h' => ⟨en, ?_, OpEnt.Le.refl en⟩) h
  unfold OpTab.erase0 at h'
  split at h'
  · cases h'
  · rwa [Row.tab_tick_ne S δ (by assumption)] at h'

include hS hres in
/-- **The *next* observation**: a segment of `cwp` under `reify`'s handler answers, at the
candidate, `inl b` or `inr` of a loop of the candidate.  By induction on the segment. -/
theorem reify_next {ls : List SRec} {x : Expr} {ρ : WRes}
    (h : cwp (Row.tab (tickSig :: S) δ) (mPost δ B R) ls x ρ) :
    ewpTS ls (hndE (reifyH res) x) (opTable (Row.tab S δ))
      (fun ls v => vCE (some (nuEnv (CTy.loopEffBody S B R) (candR δ S B R res))) true
        (.sum (B.rename Nat.succ) (.tvar 0)) ls δ v) ρ := by
  have hTd := Row.tab_without hS δ
  have hPC := Row.tab_plainCancel S δ
  have hM := opTable_mono (Row.tab S δ)
  refine ewp_ind (fun ls x ρ => ewpTS ls (hndE (reifyH res) x) (opTable (Row.tab S δ)) _ ρ) ?_
    (cwp_out h)
  intro ls x ρ hs
  refine ewp_fold hM (wpG_bind (hndK (reifyH res)) x ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · -- the end: `h_ret`
    refine ewp_unfold hM (ewp_step hM (fun μ => Step1N.head (Head.hret μ divEff _ _ _ v) rfl) _ _ σ ?_)
    rcases hv with ⟨b, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hb⟩ | ⟨r, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hr⟩
    · rw [eq_of_compS_empty_left hc]
      exact ewp_pureSteps hM (reifyR_inl b) _ _ σ₂ (ewp_val hM (nuAns_inl hb))
    · rw [eq_of_compS_empty_left hc]
      exact ewp_pureSteps hM (reifyR_inr r) _ _ σ₂ (ewp_val hM (nuAns_inr
        (fun ls'' he => Or.inr (Or.inr ⟨r, rfl, vC_local true R he hr⟩))))
  · -- another operation passes the handler
    exact wpG_here _ _ _ σ (Or.inr (hnd_fwd hTd hPC .hole (fun _ => rfl) (fun _ => rfl) rfl _ _ _
      (fun _ _ _ h => h) (opTable_rest ht)))
  · -- a tick: the loop made there
    obtain ⟨K₁, en, rfl, hK₁, hT0, ht', hcont⟩ :=
      tickStop_inv (Row.divOK_of_divB (Row.divB_tick S) δ) ht
    refine ewp_unfold hM (hnd_tick hM reifyR (reifyC res) .hole K₁ hK₁ fun ℓ σ₁ σ₂ hp hc => ?_)
    refine ewp_pureSteps hM (reifyC_steps res hres _) _ _ σ₂ (ewp_val hM (nuAns_inr ?_))
    intro ls'' he
    exact Or.inl ⟨ℓ, K₁, σ₁, σ, rfl, ResU.CompS.comm hc, hp, fun ls₃ he₃ w hw =>
      hcont ls₃ ((he.right (ResU.CompS.comm hc)).trans he₃) w hw⟩

include hS hres hresR in
/-- **The *close* observation**: a computation of `Closing` under `reify`'s handler and the
close frame hands back the residual.  By induction on `Closing`. -/
theorem reify_close {ls : List SRec} {x : Expr} {ρ : WRes}
    (h : Closing (Row.tab (tickSig :: S) δ) (mPost δ B R) ls x ρ) :
    ewpTS ls ((closeK res).plug (hndE (reifyH res) x)) (opTable (Row.tab S δ))
      (fun ls v => vC true R ls δ v) ρ := by
  have hTd := Row.tab_without hS δ
  have hPC := Row.tab_plainCancel S δ
  have hM := opTable_mono (Row.tab S δ)
  refine ewp_ind (fun ls x ρ => ewpTS ls ((closeK res).plug (hndE (reifyH res) x))
    (opTable (Row.tab S δ)) _ ρ) ?_ h
  intro ls x ρ hs
  have e : ∀ x, (closeK res).plug (hndE (reifyH res) x) =
      ((closeK res).comp (hndK (reifyH res))).plug x := fun x => by rw [Kont.plug_comp]; rfl
  rw [e]
  refine ewp_fold hM (wpG_bind _ x ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
  rw [← e]
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · refine ewp_unfold hM (ewp_step hM (fun μ => (Step1N.head (Head.hret μ divEff _ _ _ v) rfl).plug
      (closeK res)) _ _ σ ?_)
    rcases hv with ⟨b, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hb⟩ | ⟨r, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hr⟩
    · rw [eq_of_compS_empty_left hc]
      refine ewp_pureSteps hM (PureSteps.plug (closeK res) (reifyR_inl b)) _ _ σ₂ ?_
      exact ewp_pureSteps hM (closeKV_inl res hres b) _ _ σ₂ (hresR _ b σ₂ hb)
    · rw [eq_of_compS_empty_left hc]
      refine ewp_pureSteps hM (PureSteps.plug (closeK res) (reifyR_inr r)) _ _ σ₂ ?_
      refine ewp_pureSteps hM (closeKV_inr res hres _) _ _ σ₂ ?_
      exact ewp_pureSteps hM (clLoop_close r) _ _ σ₂ (ewp_val hM hr)
  rcases ht with hp | hr
  · obtain ⟨K₁, m, i, v, en, hp'⟩ := hp
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp'
    by_cases hk : m = divEff ∧ i = 0
    · -- a tick, answered *close*: the loop made there is closed in turn
      obtain ⟨rfl, rfl⟩ := hk
      rw [OpTab.closeAt_key, Row.tab_tick_key] at hT
      cases hT
      have ht := tickSig_isTick δ
      obtain ⟨rfl, rfl⟩ := (ht.2.2.1 ls' v ρa).mp hA
      rw [eq_of_compS_empty_left hcak]
      refine ewp_unfold hM (hnd_tick hM reifyR (reifyC res) (closeK res) K₁ hK₁
        fun ℓ σ₁ σ₂ hp hc => ?_)
      refine ewp_pureSteps hM (PureSteps.plug (closeK res) (reifyC_steps res hres _)) _ _ σ₂ ?_
      refine ewp_pureSteps hM (closeKV_inr res hres _) _ _ σ₂ ?_
      refine ewp_pureSteps hM (tickLoop_close res hres _) _ _ σ₂ ?_
      exact ewp_kappaC_resume_in hM _ false ℓ _ K₁ closeV
        ⟨σ₁, ρk, ResU.CompS.comm hc, hp, (hcont ls' (Ext.refl ls' ρk)).1 closeV PMap.empty ρk
          ⟨(ht.2.2.2 ls' closeV _).mpr ⟨Or.inr rfl, rfl⟩, rfl⟩ (ResU.comp_empty_right ρk)⟩
    · rw [OpTab.closeAt_ne hk, Row.tab_tick_ne S δ hk] at hT
      exact wpG_here _ _ _ σ (Or.inr (hnd_fwd hTd hPC (closeK res) (closeK_plain res).1
        (closeK_plain res).2 (closeK_dead res) _ _ _ (fun _ _ _ h => by rw [Kont.plug_comp]; exact h)
        (Or.inl ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, hcont⟩⟩)))
  · obtain ⟨K₁, m, i, v, en, hp'⟩ := hr
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp'
    by_cases hk : m = divEff ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      rw [OpTab.closeAt_key, Row.tab_tick_key] at hT
      cases hT
      exact absurd ha (by simp [OpEnt.closeOnly, OpSig.ent, OpSig.abort, tickSig, VTy.isZero])
    · rw [OpTab.closeAt_ne hk, Row.tab_tick_ne S δ hk] at hT
      exact wpG_here _ _ _ σ (Or.inr (hnd_fwd hTd hPC (closeK res) (closeK_plain res).1
        (closeK_plain res).2 (closeK_dead res) _ _ _ (fun _ _ _ h => by rw [Kont.plug_comp]; exact h)
        (Or.inr ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT, ha⟩ hrest⟩)))

include hS hres hresR in
/-- **The candidate is a post-fixed point** of `Loop_Σ B R`'s functor: each loop value's *next*
and *close* are one unfolding at the candidate. -/
theorem candR_post :
    (candR δ S B R res).Le (nuF (CTy.loopEffBody S B R) δ (candR δ S B R res)) := by
  have hM := opTable_mono (Row.tab S δ)
  have hSd := Row.divB_of_without hS
  intro ls e ρ h
  show cB _ (CTy.effOf S (.sum (B.rename Nat.succ) (.tvar 0))) ls δ (.app e (.val (Val.inj₁ .unit))) ρ ∧
    cB _ (CTy.effOf S (R.rename Nat.succ)) ls δ (.app e (.val (Val.inj₂ .unit))) ρ
  rw [cB_effOf _ S hSd, cB_effOf _ S hSd]
  have hR : (fun ls v => vCE (some (nuEnv (CTy.loopEffBody S B R) (candR δ S B R res))) true
      (R.rename Nat.succ) ls δ v) = fun ls v => vC true R ls δ v := by
    funext ls v; rw [vCE_nuEnv_rename]
  rw [hR]
  rcases h with ⟨ℓ, K₁, ρc, ρk, rfl, hc, hp, hk⟩ | ⟨b, rfl, hb⟩ | ⟨r, rfl, hr⟩
  · refine ⟨ewp_pureSteps hM (tickLoop_next res hres _) _ _ ρ ?_,
      ewp_pureSteps hM (tickLoop_close res hres _) _ _ ρ ?_⟩
    · exact ewp_kappaC_resume_in hM .hole false ℓ _ K₁ nextV ⟨ρc, ρk, hc, hp,
        reify_next hS res hres (hk ls (Ext.refl ls ρk) nextV (Or.inl rfl)).1⟩
    · exact ewp_kappaC_resume_in hM (closeK res) false ℓ _ K₁ closeV ⟨ρc, ρk, hc, hp,
        reify_close hS res hres hresR (hk ls (Ext.refl ls ρk) closeV (Or.inr rfl)).2⟩
  · exact ⟨ewp_pureSteps hM (doneLoop_next res hres b) _ _ ρ (ewp_val hM (nuAns_inl hb)),
      ewp_pureSteps hM (doneLoop_close res hres b) _ _ ρ (hresR ls b ρ hb)⟩
  · exact ⟨ewp_pureSteps hM (clLoop_next r) _ _ ρ (ewp_val hM (nuAns_inr
        (fun ls' he => Or.inr (Or.inr ⟨r, rfl, vC_local true R he hr⟩)))),
      ewp_pureSteps hM (clLoop_close r) _ _ ρ (ewp_val hM hr)⟩

include hS hres hresR in
/-- **`reify`'s compatibility**: for a computation of `cwp` at `𝒱⟦B ⊕ R⟧`, `reify` answers a
value of `𝒱⟦U(Loop_Σ B R)⟧`, by coinduction with `candR`.  `[spec §14]` -/
theorem reify_compat {ls : List SRec} {M : Expr} {ρ : WRes}
    (h : cwp (Row.tab (tickSig :: S) δ) (mPost δ B R) ls M ρ) :
    ewpTS ls (.app (.val (rkV res)) (hndE (reifyH res) M)) (opTable (Row.tab S δ))
      (fun ls v => vC true (.thunk (CTy.loopEff S B R)) ls δ v) ρ := by
  have hM := opTable_mono (Row.tab S δ)
  have hval : ∀ ls L ρ, (∀ ls', Ext ls ls' ρ → candR δ S B R res ls' (.val L) ρ) →
      vC true (.thunk (CTy.loopEff S B R)) ls δ L ρ :=
    fun ls L ρ hL ls' he _ => ⟨_, candR_post hS res hres hresR, hL ls' he⟩
  have hH : ∀ n, (Kont.appR (.val (rkV res)) .hole).HasHnd n = false := fun n => by
    simp [Kont.HasHnd, rkV]
  have hC : ∀ n, (Kont.appR (.val (rkV res)) .hole).Catches n = false := fun n => by
    simp [Kont.Catches, rkV]
  obtain ⟨hW, hU, hK⟩ := emp_conds (Row.tab_plainCancel S δ) _ hH hC
  show ewpTS ls ((Kont.appR (.val (rkV res)) .hole).plug (hndE (reifyH res) M)) _ _ ρ
  refine ewp_frame_plain _ _ hH hC (fun _ => emp) (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) hW hU hK _ _ ?_ (reify_next hS res hres h) (ρ₂ := PMap.empty)
    ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
  intro ls' v σ hσ
  rcases sep_emp_elim hσ with ⟨b, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hb⟩ | ⟨L, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hL⟩
  · rw [eq_of_compS_empty_left hc]
    rw [vCE_nuEnv_rename] at hb
    refine ewp_pureSteps hM (rkV_inl res hres b) _ _ σ₂ (ewp_val hM (hval _ _ _ fun ls'' he =>
      Or.inr (Or.inl ⟨b, rfl, vC_local true B he hb⟩)))
  · rw [eq_of_compS_empty_left hc]
    exact ewp_pureSteps hM (rkV_inr res L) _ _ σ₂ (ewp_val hM (hval _ _ _ hL))

end rel

/-! ### The constant -/

/-- The residual's type, `!U(B ⊸ F_Σ R)`.  `[spec §14]` -/
abbrev resTy (S : Row) (B R : VTy) : VTy := .bang (.thunk (.arr B (CTy.effOf S R)))

/-- `reify_res : !U(U(F_{tick, Σ}(B ⊕ R)) ⊸ F_Σ U(Loop_Σ B R))`.  `[spec §14]` -/
abbrev reifyTy (S : Row) (B R : VTy) : VTy :=
  .bang (.thunk (.arr (.thunk (CTy.effOf (tickSig :: S) (.sum B R)))
    (CTy.effOf S (.thunk (CTy.loopEff S B R)))))

/-- A closed value of a semantic judgment at the empty context is in the relation, at a list. -/
theorem semV_closed_val {Δ : LifeCtx} {v : Val} {A : VTy} (hv : SemV Δ [] (.val v) A)
    (hcl : closedAt 0 v.1 = true) {δ : LSub} (hδ : Δ.Models δ) :
    ∃ ls ρ, vC true A ls δ v ρ := by
  have h := hv δ [] [] PMap.empty hδ (gDenC_nil _ _)
  rw [show substAll [] (.val v) = .val v from psub_closedAt _ [] hcl (Nat.zero_le 0)] at h
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ls', ρ', -, hq⟩ := wpTS_val_post h Fig16.LogRel.hash_empty (ResU.comp_empty_right _)
    TW.empty htg
  exact ⟨ls', ρ', hq⟩

theorem rkV_closed {res : Val} (hres : closedAt 0 res.1 = true) : closedAt 0 (rkV res).1 = true := by
  simp [rkV, dlX, closedAt, closedAt_mono _ hres (Nat.zero_le _)]

theorem reifyH_closed {res : Val} (hres : closedAt 0 res.1 = true) :
    closedAt 0 (reifyH res).1 = true := by
  have hk := closeKV_closed res hres
  have hcl : closedAt 0 clV.1 = true := selfV_closed clB_closed
  simp [reifyH, hndVal, qualsVal, reifyR, reifyC, tlX, closedAt, Val.pair, Val.i32, Qual.tag,
    closedAt_mono _ hcl (Nat.zero_le _), closedAt_mono _ hk (Nat.zero_le _), nextV, closeV]

theorem reifyV_closed {res : Val} (hres : closedAt 0 res.1 = true) :
    closedAt 0 (reifyV res).1 = true := by
  simp [reifyV, closedAt, BoCa.BoLo.hndE, closedAt_mono _ (rkV_closed hres) (Nat.zero_le _),
    closedAt_mono _ (reifyH_closed hres) (Nat.zero_le _)]

/-- **`reify` is sound**: its answer is a loop value of `𝒱⟦U(Loop_Σ B R)⟧`.  `[spec §14]` -/
theorem reify_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {B R : VTy} {res : Val}
    (hS : ∀ o ∈ S, o.n ≠ divEff) (hres : closedAt 0 res.1 = true)
    (hR : SemV Δ [] (.val res) (resTy S B R)) (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (reifyV res)) (reifyTy S B R) := by
  refine sem_const hΓ (reifyV_closed hres) fun δ ls hδ => ⟨rfl, ?_⟩
  intro ls' _ t σ τ ht hcomp
  rw [eq_of_compS_empty_left hcomp]
  have hSd := Row.divB_of_without hS
  obtain ⟨lsr, ρr, hVr⟩ := semV_closed_val hR hres hδ
  obtain rfl : ρr = PMap.empty := hVr.1
  have hresR : ∀ ls b ρ, vC true B ls δ b ρ → ewpTS ls (.app (.val res) (.val b))
      (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ := by
    intro ls b ρ hb
    have hf := (hVr.2 ls (ext_empty' lsr ls)) b ρ ρ hb (compS_empty_left ρ)
    exact (cC_effOf S R ls δ _ ρ hSd).mp hf
  refine (cC_effOf S _ ls' δ _ σ hSd).mpr ?_
  have e : Expr.subst 0 t (.app (.val (rkV res)) (hndE (reifyH res) (.app (.var 0) (.val .unit)))) =
      .app (.val (rkV res)) (hndE (reifyH res) (.app (.val t) (.val .unit))) := by
    simp [BoCa.BoLo.hndE, closed_subst (rkV_closed hres), closed_subst (reifyH_closed hres)]
  refine ewp_step (opTable_mono _) (fun μ => Step1N.head (Head.beta μ _ t) rfl) ls' _ σ ?_
  rw [e]
  have hM := (cC_effOf_wp (tickSig :: S) _ ls' δ _ σ).mp (ht ls' (Ext.refl _ _))
  rw [Row.divB_tick] at hM
  exact reify_compat hS res hres hresR hM

end BoCa.Fig16.LogRel.Core

end
