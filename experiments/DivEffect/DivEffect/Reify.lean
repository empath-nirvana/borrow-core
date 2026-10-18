import DivEffect.Fuel

/-!
# DivEffect — `reify`  (§4.1, unknown 1, item 5)

`reify M` makes a loop value of a computation `M : F_{Σ, Div}(B ⊕ R)`: it runs `M` to its first
tick, or to its end, and answers the loop there.  It is a deep handler of `d`:

    reify M        ≜  (hnd_d H M) to x. case x { inl b → done b | inr L → L }
    h_ret v        =  case v { inl b → inl b | inr r → inr (closed r) }
    h_tick ((), κ) =  inr ⟨ next ↦ κ next,  close ↦ (κ close) to x. case x { inl b → res b
                                                                      | inr L → L.close } ⟩

* `done b` finishes at its first observation with `b`; closed, it hands back `res b`.  `res` is
  the residual of a result, read off its type (SPEC §14 *The residual*): what `B` holds with no
  destructor.
* `closed r` is the loop of a computation that ended with its residual: every *next* skips, and
  *close* hands `r` back.  It is the Z combinator's fixed point.
* At a tick the handler answers the loop whose *next* resumes `κ` with *next*, which runs the
  next segment under the same handler and answers the next loop, and whose *close* resumes `κ`
  with *close*.  After a close the computation reaches a tick again or its end; at a tick, that
  loop's *close* is taken in turn.  `Closing` bounds those ticks.

`reify_compat`: for `M` in `cwp` at `𝒱⟦B ⊕ R⟧`, `reify M` is in `ewpTS` at
`𝒱⟦U(Loop_Σ B R)⟧` (`Core/NuRel.lean`), by coinduction with the candidate of the three loop
values.  Its observations are two lemmas by induction: a segment under the handler at *next*
(`reify_next`, on the segment's least fixed point), and a close (`reify_close`, on `Closing`'s).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
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

/-- The handler value: the name `d`, the tick linear. -/
def reifyH (d : UInt32) (res : Val) : Val :=
  hndVal d (qualsVal [.lin]) reifyR (Val.pair (reifyC res) .unit)

/-- `λx. case x { inl b → done b | inr L → L }`. -/
def rkV (res : Val) : Val := .lam (.case (.var 0) (.val (.lam (dlX res))) (.var 0))

/-- **`reify M`.** -/
def reifyE (d : UInt32) (res : Val) (e : Expr) : Expr :=
  .app (.val (rkV res)) (hndE (reifyH d res) e)

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

include hres in
theorem tickLoop_next (κ : Val) :
    PureSteps (.app (.val (tickLoop res κ)) (.val nextV))
      (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val nextV)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  have hk : closedAt 0 (closeKV res).1 = true := by
    simp [closeKV, closedAt, closedAt_mono _ hres (Nat.zero_le _), closeV]
  simp [tlX, closed_subst hk, closed_shift hk, subst_shift_succ, nextV]
  exact .refl

include hres in
theorem tickLoop_close (κ : Val) :
    PureSteps (.app (.val (tickLoop res κ)) (.val closeV))
      ((closeK res).plug (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val closeV))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  have hk : closedAt 0 (closeKV res).1 = true := by
    simp [closeKV, closedAt, closedAt_mono _ hres (Nat.zero_le _), closeV]
  simp [tlX, closeK, Kont.plug, closed_subst hk, closed_shift hk, subst_shift_succ, closeV]
  exact .refl

include hres in
theorem reifyC_steps (κ : Val) :
    PureSteps (.app (.val (reifyC res)) (.val (Val.pair .unit κ)))
      (.val (Val.inj₂ (tickLoop res κ))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ .unit κ _) rfl).trans ?_
  have hk : closedAt 0 (closeKV res).1 = true := by
    simp [closeKV, closedAt, closedAt_mono _ hres (Nat.zero_le _), closeV]
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

/-- `cC_effOf` at one unfolding. -/
theorem cB_effOf (η : Option (Nat → TEnt)) (S : Row) (A : VTy) (ls : List SRec) (δ : LSub)
    (e : Expr) (ρ : WRes) :
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
      simp only [CTy.effOf, effTab] at h
      simp only [CTy.effOf, cB]
      rw [h, effRetE_effOf]

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
variable {δ : LSub} {d : UInt32} {S : Row} (hS : Row.Without S d) {B R : VTy} (res : Val)
  (hres : closedAt 0 res.1 = true)
  (hresR : ∀ ls b ρ, vC true B ls δ b ρ →
    ewpTS ls (.app (.val res) (.val b)) (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ)

/-- The relation of `M`'s answers, `𝒱⟦B ⊕ R⟧`. -/
abbrev mPost (δ : LSub) (B R : VTy) : List SRec → Val → WProp := fun ls v => vC true (.sum B R) ls δ v

/-- **The candidate** for `Loop_Σ B R`: a loop made at a tick, whose cell it owns and whose
continuation is at every answer in `cwp` and in `Closing`; `done b`; `closed r`. -/
def candR (δ : LSub) (d : UInt32) (S : Row) (B R : VTy) (res : Val) : CPred := fun ls e ρ =>
  (∃ ℓ K₁ ρc ρk, e = .val (tickLoop res (kapV ℓ (reifyH d res) K₁)) ∧ ResU.CompS ρc ρk ρ ∧
    ptoOwn ℓ .unit ρc ∧ ∀ ls', Ext ls ls' ρk → ∀ w : Val, w = nextV ∨ w = closeV →
      owe δ d (Row.tab S δ) (mPost δ B R) (cwp δ d (Row.tab S δ) (mPost δ B R)) ls'
        (K₁.plug (.val w)) ρk) ∨
  (∃ b, e = .val (doneLoop res b) ∧ vC true B ls δ b ρ) ∨
  (∃ r, e = .val (clLoop r) ∧ vC true R ls δ r ρ)

/-- The candidate holds at every extension. -/
theorem candR_ext {ls ls' : List SRec} {e : Expr} {ρ : WRes} (he : Ext ls ls' ρ)
    (h : candR δ d S B R res ls e ρ) : candR δ d S B R res ls' e ρ := by
  rcases h with ⟨ℓ, K₁, ρc, ρk, rfl, hc, hp, hk⟩ | ⟨b, rfl, hb⟩ | ⟨r, rfl, hr⟩
  · exact Or.inl ⟨ℓ, K₁, ρc, ρk, rfl, hc, hp, fun ls'' he' => hk ls'' ((he.right hc).trans he')⟩
  · exact Or.inr (Or.inl ⟨b, rfl, vC_local true B he hb⟩)
  · exact Or.inr (Or.inr ⟨r, rfl, vC_local true R he hr⟩)

include hS hres in
/-- **The *next* observation**: a segment of `cwp` under `reify`'s handler answers, at the
candidate, `inl b` or `inr` of a loop of the candidate.  By induction on the segment. -/
theorem reify_next (hPC : (Row.tab S δ).PlainCancel) {ls : List SRec} {x : Expr} {ρ : WRes}
    (h : cwp δ d (Row.tab S δ) (mPost δ B R) ls x ρ) :
    ewpTS ls (hndE (reifyH d res) x) (opTable (Row.tab S δ))
      (fun ls v => vCE (some (nuEnv (CTy.loopEffBody S B R) (candR δ d S B R res))) true
        (.sum (B.rename Nat.succ) (.tvar 0)) ls δ v) ρ := by
  have hTd := Row.tab_without hS δ
  have hM := opTable_mono (Row.tab S δ)
  refine ewp_ind (fun ls x ρ => ewpTS ls (hndE (reifyH d res) x) (opTable (Row.tab S δ)) _ ρ) ?_
    (cwp_out ls x ρ h)
  intro ls x ρ hs
  refine ewp_fold hM (wpG_bind (hndK (reifyH d res)) x ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · -- the end: `h_ret`
    refine ewp_unfold hM (ewp_step hM (fun μ => Step1N.head (Head.hret μ d _ _ _ v) rfl) _ _ σ ?_)
    rcases hv with ⟨b, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hb⟩ | ⟨r, σ₁, σ₂, hc, ⟨rfl, rfl⟩, hr⟩
    · rw [eq_of_compS_empty_left hc]
      exact ewp_pureSteps hM (reifyR_inl b) _ _ σ₂ (ewp_val hM (nuAns_inl hb))
    · rw [eq_of_compS_empty_left hc]
      exact ewp_pureSteps hM (reifyR_inr r) _ _ σ₂ (ewp_val hM (nuAns_inr
        (fun ls'' he => Or.inr (Or.inr ⟨r, rfl, vC_local true R he hr⟩))))
  · -- another operation passes the handler
    exact wpG_here _ _ _ σ (Or.inr (hnd_fwd hTd hPC .hole (fun _ => rfl) (fun _ => rfl) rfl _ _ _
      (fun _ _ _ h => h) ht))
  · -- a tick: the loop made there
    obtain ⟨K₁, n, i, v, en, hp'⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp'
    obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
    obtain ⟨rfl, rfl⟩ := hA
    rw [eq_of_compS_empty_left hcak]
    refine ewp_unfold hM (hnd_tick hM n reifyR (reifyC res) .hole K₁ hK₁ fun ℓ σ₁ σ₂ hp hc => ?_)
    refine ewp_pureSteps hM (reifyC_steps res hres _) _ _ σ₂ (ewp_val hM (nuAns_inr ?_))
    intro ls'' he
    refine Or.inl ⟨ℓ, K₁, σ₁, ρk, rfl, ResU.CompS.comm hc, hp, fun ls₃ he₃ w hw => ?_⟩
    have he' : Ext ls' ls₃ ρk := (he.right (ResU.CompS.comm hc)).trans he₃
    rcases hw with rfl | rfl
    · exact (hcont ls₃ he').1 nextV PMap.empty ρk
        (Or.inl ⟨.unit, ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩)
        (ResU.comp_empty_right ρk)
    · exact (hcont ls₃ he').1 closeV PMap.empty ρk (closeEnt_le δ n ls₃ closeV PMap.empty (vC_close.mpr ⟨rfl, rfl⟩))
        (ResU.comp_empty_right ρk)

include hS hres hresR in
/-- **The *close* observation**: a computation of `Closing` under `reify`'s handler and the
close frame hands back the residual.  By induction on `Closing`. -/
theorem reify_close (hPC : (Row.tab S δ).PlainCancel) {ls : List SRec} {x : Expr} {ρ : WRes}
    (h : Closing δ d (Row.tab S δ) (mPost δ B R) ls x ρ) :
    ewpTS ls ((closeK res).plug (hndE (reifyH d res) x)) (opTable (Row.tab S δ))
      (fun ls v => vC true R ls δ v) ρ := by
  have hTd := Row.tab_without hS δ
  have hM := opTable_mono (Row.tab S δ)
  refine ewp_ind (fun ls x ρ => ewpTS ls ((closeK res).plug (hndE (reifyH d res) x))
    (opTable (Row.tab S δ)) _ ρ) ?_ h
  intro ls x ρ hs
  have e : ∀ x, (closeK res).plug (hndE (reifyH d res) x) =
      ((closeK res).comp (hndK (reifyH d res))).plug x := fun x => by rw [Kont.plug_comp]; rfl
  rw [e]
  refine ewp_fold hM (wpG_bind _ x ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
  rw [← e]
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · refine ewp_unfold hM (ewp_step hM (fun μ => (Step1N.head (Head.hret μ d _ _ _ v) rfl).plug
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
    rcases ext_some hT with ⟨rfl, rfl, rfl⟩ | hT'
    · -- a tick, answered *close*: the loop made there is closed in turn
      obtain ⟨rfl, rfl⟩ := hA
      rw [eq_of_compS_empty_left hcak]
      refine ewp_unfold hM (hnd_tick hM m reifyR (reifyC res) (closeK res) K₁ hK₁
        fun ℓ σ₁ σ₂ hp hc => ?_)
      refine ewp_pureSteps hM (PureSteps.plug (closeK res) (reifyC_steps res hres _)) _ _ σ₂ ?_
      refine ewp_pureSteps hM (closeKV_inr res hres _) _ _ σ₂ ?_
      refine ewp_pureSteps hM (tickLoop_close res hres _) _ _ σ₂ ?_
      exact ewp_kappaC_resume_in hM _ false ℓ _ K₁ closeV
        ⟨σ₁, ρk, ResU.CompS.comm hc, hp, (hcont ls' (Ext.refl ls' ρk)).1 closeV PMap.empty ρk
          (vC_close.mpr ⟨rfl, rfl⟩) (ResU.comp_empty_right ρk)⟩
    · exact wpG_here _ _ _ σ (Or.inr (hnd_fwd hTd hPC (closeK res) (closeK_plain res).1
        (closeK_plain res).2 (closeK_dead res) _ _ _ (fun _ _ _ h => by rw [Kont.plug_comp]; exact h)
        (Or.inl ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT', ha⟩
          ⟨ρa, ρk, hcak, hA, hu, hcont⟩⟩)))
  · obtain ⟨K₁, m, i, v, en, hp'⟩ := hr
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp'
    rcases ext_some hT with ⟨rfl, rfl, rfl⟩ | hT'
    · exact absurd ha (by show ¬ (false = true); simp)
    · exact wpG_here _ _ _ σ (Or.inr (hnd_fwd hTd hPC (closeK res) (closeK_plain res).1
        (closeK_plain res).2 (closeK_dead res) _ _ _ (fun _ _ _ h => by rw [Kont.plug_comp]; exact h)
        (Or.inr ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT', ha⟩ hrest⟩)))

include hS hres hresR in
/-- **The candidate is a post-fixed point** of `Loop_Σ B R`'s functor: each loop value's *next*
and *close* are one unfolding at the candidate. -/
theorem candR_post (hPC : (Row.tab S δ).PlainCancel) :
    (candR δ d S B R res).Le (nuF (CTy.loopEffBody S B R) δ (candR δ d S B R res)) := by
  have hM := opTable_mono (Row.tab S δ)
  intro ls e ρ h
  show cB _ (CTy.effOf S (.sum (B.rename Nat.succ) (.tvar 0))) ls δ (.app e (.val (Val.inj₁ .unit))) ρ ∧
    cB _ (CTy.effOf S (R.rename Nat.succ)) ls δ (.app e (.val (Val.inj₂ .unit))) ρ
  rw [cB_effOf, cB_effOf]
  have hR : (fun ls v => vCE (some (nuEnv (CTy.loopEffBody S B R) (candR δ d S B R res))) true
      (R.rename Nat.succ) ls δ v) = fun ls v => vC true R ls δ v := by
    funext ls v; rw [vCE_nuEnv_rename]
  rw [hR]
  rcases h with ⟨ℓ, K₁, ρc, ρk, rfl, hc, hp, hk⟩ | ⟨b, rfl, hb⟩ | ⟨r, rfl, hr⟩
  · refine ⟨ewp_pureSteps hM (tickLoop_next res hres _) _ _ ρ ?_,
      ewp_pureSteps hM (tickLoop_close res hres _) _ _ ρ ?_⟩
    · exact ewp_kappaC_resume_in hM .hole false ℓ _ K₁ nextV ⟨ρc, ρk, hc, hp,
        reify_next hS res hres hPC (hk ls (Ext.refl ls ρk) nextV (Or.inl rfl)).1⟩
    · exact ewp_kappaC_resume_in hM (closeK res) false ℓ _ K₁ closeV ⟨ρc, ρk, hc, hp,
        reify_close hS res hres hresR hPC (hk ls (Ext.refl ls ρk) closeV (Or.inr rfl)).2⟩
  · exact ⟨ewp_pureSteps hM (doneLoop_next res hres b) _ _ ρ (ewp_val hM (nuAns_inl hb)),
      ewp_pureSteps hM (doneLoop_close res hres b) _ _ ρ (hresR ls b ρ hb)⟩
  · exact ⟨ewp_pureSteps hM (clLoop_next r) _ _ ρ (ewp_val hM (nuAns_inr
        (fun ls' he => Or.inr (Or.inr ⟨r, rfl, vC_local true R he hr⟩)))),
      ewp_pureSteps hM (clLoop_close r) _ _ ρ (ewp_val hM hr)⟩

include hS hres hresR in
/-- **`reify`'s compatibility** (§4.1 unknown 1 item 5): for `M` of `cwp` at `𝒱⟦B ⊕ R⟧`,
`reify M` answers a value of `𝒱⟦U(Loop_Σ B R)⟧`, by coinduction with `candR`. -/
theorem reify_compat (hPC : (Row.tab S δ).PlainCancel) {ls : List SRec} {M : Expr} {ρ : WRes}
    (h : cwp δ d (Row.tab S δ) (mPost δ B R) ls M ρ) :
    ewpTS ls (reifyE d res M) (opTable (Row.tab S δ))
      (fun ls v => vC true (.thunk (CTy.loopEff S B R)) ls δ v) ρ := by
  have hM := opTable_mono (Row.tab S δ)
  have hval : ∀ ls L ρ, (∀ ls', Ext ls ls' ρ → candR δ d S B R res ls' (.val L) ρ) →
      vC true (.thunk (CTy.loopEff S B R)) ls δ L ρ :=
    fun ls L ρ hL ls' he _ => ⟨_, candR_post hS res hres hresR hPC, hL ls' he⟩
  have hH : ∀ n, (Kont.appR (.val (rkV res)) .hole).HasHnd n = false := fun n => by
    simp [Kont.HasHnd, rkV]
  have hC : ∀ n, (Kont.appR (.val (rkV res)) .hole).Catches n = false := fun n => by
    simp [Kont.Catches, rkV]
  obtain ⟨hW, hU, hK⟩ := emp_conds hPC _ hH hC
  show ewpTS ls ((Kont.appR (.val (rkV res)) .hole).plug (hndE (reifyH d res) M)) _ _ ρ
  refine ewp_frame_plain _ _ hH hC (fun _ => emp) (fun _ _ _ _ h => h)
    (fun _ _ _ _ h => h) hW hU hK _ _ ?_ (reify_next hS res hres hPC h) (ρ₂ := PMap.empty)
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

end BoCa.Fig16.LogRel.Core.DivEffect

end
