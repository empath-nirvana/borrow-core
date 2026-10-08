import Targets.Instance.CellRuns

/-!
# The Instance — the unary laws (`A.UnaryLaws`, restated by D4) at our instance

**Algebraicity observing a finaliser's code fails as written at `J₁`** (`not_algLawCode_J₁`, at
the admissible context `ΞA`: `not_algLawCode_ΞA`), with `J₁`'s inner rows tied to the effect
context (decision R): D4 compares the two sides at a program's data answers, and that statement
compares each finaliser event `fire D` by the finaliser's code.  **Algebraicity as restated, a
finaliser's start observed but not its code, holds at the same configuration** (`algLaw_algAffProg`):
each side's complete runs answer `()` and show one finaliser's start (`obsFrom_algAffL`,
`obsFrom_algAffR`).  The witness `algAffProg` is typed by Core's kernel with every handler's and
operation's row tied to the context (`d_algAffProg`):

* a handler of `2` handles the affine `wait : 1 ↠ 1`; its clause raises `exn` to a handler outside,
  inside a finaliser frame whose finaliser cancels the clause's continuation `κ` and handles the
  cancel's row itself, so that the finaliser is at the pure row (`holdCancelCl`:
  `λ(a, k). raise exn then y. k.resume y unwind (handle_exn (k.cancel) with λ_. ())`);
* the two sides of the law, `(wait () to x. ret x) to y. ret ()` and
  `wait () to x. (ret x to y. ret ())`, are caught by that handler with continuations that frame
  the rest differently;
* the raise fires the finaliser, and the two runs show `fire D` at finalisers that differ as terms
  (`finE_D2_ne`), each mentioning the `κ` its side captured, at whatever location the allocation of
  `κ`'s cell picks (SPEC §25); both answer `()`.

The finaliser uses `κ` once, by its cancel branch, as an affine `κ` may be used; the clause's `then`
branch resumes it.  Option A's `[then]` (the finaliser at `F 1`) admits the finaliser because it
handles the cancel's raises inside itself.  So neither tying rows (D1, decision R) nor restricting
`unr` (decision 63; at an admissible context a tied row has no resuming `unr` operation) excludes
the witness.  Algebraicity is stated with a finaliser's start observed without its code (D4 read at
the trace's events, `A.EffectSystem.RunsAlikeStart`), the repair that adds no surface restriction;
the reading is pending the user's confirmation.  The alternative, keeping continuations out of
finalisers, is a surface rule and is not applied.

**The witness at an unrestricted continuation is outside the tied kernel.**  `algFireProg`
(`d_algFireProg`, Core's kernel) handles the name `5` at an `unr` operation where `ΞA` declares a
linear one: its handled row `R5` is not tied to `ΞA` (`not_rowAt_R5`), a tied `[handle]` of `5`
carries the tags of a prefix of `ΞA`'s qualifiers of `5`, never `[unr]` (`not_tied_hnd5_unr`), and
so Core's kernel with its inner rows tied to `ΞA` types `algFireProg` at no context and judgement
(`not_derAt_algFireProg`), and `J₁` at `ΞA` types it at no type (`not_der_algFireProg_J₁`).  The
inversion reads the program's two handlers through their `let`s (`derAt_withH`): `[let]`,
`[let-poly]` and the call-by-value application of the λ-value (`derAt_let`, `derAt_lam`), then
`[handle]` (`derAt_hnd`).

**The laws at the answering class** (`calm_tailClause`): a tail-resumptive clause
`λ(a, k). c a to b. k.resume b` whose code `c v` runs quietly to a value resumes `K` in place, so
the tail-resumptive law (`tailLaw_quiet`) and algebraicity inside such a handler (`algLaw_quiet`)
hold at every configuration a typed program reaches, by a join (`runsAlike_of_live_calm`).  At an
operation whose `κ` owns no cell the run is quiet (`quiet_tailClause`); at a linear or affine one
the catch allocates `κ`'s cell and the resume releases it (SPEC §25), and the run is quiet around
the cell at every location the allocation may pick (`cellQuiet_tailClause`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE hndVal kappa
  clauseAt capTag kappaAt kappaC kappaCBody kappaCell)
open Targets (CDerivesAt RowAt rowAt_nil rowAt_ofEff_append hndTags_of_rowAt derAt_let derAt_lam
  derAt_hnd)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg HeadChain lookRun lookEnd lookRun_sound closedAt_kappa
  closedAt_plug_iff kont_shift_closed)

/-! ### Typing with the inner rows tied -/

theorem rowLe_nil (S : Row) : RowLe [] S := fun _ _ _ h => by simp [Row.find] at h

/-- `exn : 1 ↠ 0` at the name `1`: the handlers' outer row in the witnesses below. -/
abbrev Sx : Row := Row.ofEff 1 Eab 0 ++ []

/-- `withH` in Core's kernel with its inner rows tied: one clause and the identity return clause,
the handled row tied to `Ξ`. -/
theorem d_withHAt {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {q : Qual}
    {B C : VTy} {n : UInt32} {cl e : Expr} (hAt : RowAt Ξ (Row.ofEff n [(q, B, C)] 0 ++ S))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hΓ : Ctx.Dead Γ)
    (hcl : CDerivesAt Ξ Δ Γ cl (.val (clauseTy S A (q, B, C))))
    (he : CDerivesAt Ξ Δ (⟨retTy S A A, false⟩ :: ⟨clausesTy S A [(q, B, C)], false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff n [(q, B, C)] 0 ++ S) A))) :
    CDerivesAt Ξ Δ Γ (withH n q cl e) (.comp (CTy.effOf S A)) := by
  refine .bind (deadSplit hΓ) (.ret (.tensorI (deadSplit hΓ) hcl (.unitI hΓ.toP))) ?_
  refine .bind (A := retTy S A A) (.right (deadSplit hΓ)) (.ret ?_) ?_
  · exact .bangThunkV (dead_noLive (Ctx.Dead.cons hΓ)) rfl
      (.lam (.effSub (S := []) (rowLe_nil _) (.ret (.var (.here (Ctx.Dead.cons hΓ).toP)))))
  exact .effHandle (E := [(q, B, C)]) hAt (.left (.left (deadSplit hΓ)))
    (.left (.right (deadSplit hΓ))) (.here (Ctx.Dead.cons hΓ).toP) (.there (.here hΓ.toP)) hn0
    hnS (by simp) he

/-- `λ_. ()`, the clause at `exn`, with its inner rows tied: it performs nothing. -/
theorem d_abortClAt {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ abortCl (.val (clauseTy S .unit (.aff, .unit, .zero))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) (rowLe_nil _) (.ret (.unitI (.drop rfl hΓ.toP)))))

/-! ### Algebraicity's witness: a finaliser holding an affine continuation -/

/-- `λ(a, k). raise (1, 0, ()) then y. k.resume y unwind (handle_1 (k (inj₂ ())) with (λ_. ()))`:
a clause that raises `exn` inside a finaliser frame whose finaliser cancels `k`, handling the
cancel's raises of `exn` itself. -/
def holdCancelCl : Expr :=
  .val (.lam (.letpair (.var 0)
    (thenE (.app (.app (.var 1) (.val (Val.inj₁ Val.unit))) (.var 0))
      (withH 1 .aff abortCl (.app (.var 3) (.val (Val.inj₂ Val.unit))))
      (raiseE (opArgE 1 0 (.val .unit))))))

/-- Algebraicity's left side at the name `2`: `(wait () to x. ret x) to y. ret ()`. -/
def algL2 : Expr := bindE (bindE (performE (opArgE 2 0 (.val .unit))) (.var 0)) (.val .unit)

/-- Its right side: `wait () to x. (ret x to y. ret ())`. -/
def algR2 : Expr := bindE (performE (opArgE 2 0 (.val .unit))) (bindE (.var 0) (.val .unit))

/-- **The witness**: `handle_1 (handle_2 algL2 with holdCancelCl) with (λ_. ())`. -/
def algAffProg : Expr := withH 1 .aff abortCl (withH 2 .aff holdCancelCl algL2)

/-- `wait : 1 ↠ 1`, affine, at the name `2`. -/
abbrev Ew : List (Qual × VTy × VTy) := [(.aff, .unit, .unit)]

/-- The row the handler of `2` handles. -/
abbrev R2 : Row := Row.ofEff 2 Ew 0 ++ Sx

/-- The clause's continuation's type: `U((1 ⊸ F_Sx 1) & F_Sx 1)`, affine. -/
abbrev kT : VTy := kTy Sx .unit .aff .unit

section AffTyping
variable {Ξ : EffCtx}

/-- **The finaliser**: `handle_1 (k (inj₂ ())) with (λ_. ())`, `k` at index `1` under the
finaliser's dead binder.  The cancel's row `Sx` is handled inside it, so it is at the pure row. -/
theorem d_holdD (h1 : Ξ 1 = Eab) {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {T : VTy} :
    CDerivesAt Ξ Δ (⟨.unit, false⟩ :: ⟨kT, true⟩ :: ⟨.unit, false⟩ :: ⟨T, false⟩ :: Γ)
      (withH 1 .aff abortCl (.app (.var 3) (.val (Val.inj₂ Val.unit)))) (.comp (.ret .unit)) := by
  have hk : Ctx.Dead (kill (⟨.unit, false⟩ :: ⟨kT, true⟩ :: ⟨.unit, false⟩ :: ⟨T, false⟩ :: Γ)) :=
    kill_dead _
  refine .bind (splitP_kill_left _) (.ret (.tensorI (deadSplit hk) (d_abortClAt (S := []) hk)
    (.unitI hk.toP))) ?_
  refine .bind (A := retTy [] .unit .unit) (.right (splitP_kill_left _)) (.ret ?_) ?_
  · exact .bangThunkV (dead_noLive (Ctx.Dead.cons hk)) rfl
      (.lam (.effSub (S := []) (rowLe_nil _) (.ret (.var (.here (Ctx.Dead.cons hk).toP)))))
  refine .effHandle (E := Eab) (S := []) (A := .unit) (R := .unit)
    (rowAt_ofEff_append h1 (by decide) (by simp) (rowAt_nil Ξ))
    (.left (.left (splitP_kill_left _))) (.left (.right (deadSplit hk)))
    (.here (Ctx.Dead.cons hk).toP) (.there (.here hk.toP)) (by decide) (by simp) (by simp) ?_
  exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf Sx .unit)) (CTy.effOf Sx .unit))
    (.there (.there (.there (.here (.cons (.cons hΓ.toP)))))))

/-- **The clause**, at the affine `1 ↠ 1` of a handler answering `F_Sx 1`: its raise at the row
`Sx`, tied; the `then` branch resumes `k`, the finaliser cancels it. -/
theorem d_holdCancelCl (h1 : Ξ 1 = Eab) {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ holdCancelCl (.val (clauseTy Sx .unit (.aff, .unit, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .effThen (A := .unit) (.right (.left (.dead (deadSplit hΓ)))) ?_ ?_
    (fun h => absurd h (by simp [Row.Unr, Row.ofEff])) ?_ ?_ (d_holdD h1 hΓ)
  · intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  · simp [Row.Uniq, Row.ofEff]
  · exact .effRaise (o := ⟨1, 0, .aff, .unit, .zero⟩)
      (rowAt_ofEff_append h1 (by decide) (by simp) (rowAt_nil Ξ)) rfl rfl .unit
      (.unitI (.cons (.drop rfl (.cons hΓ.toP))))
  · exact .app (.right (.left (.dead (.dead (deadSplit hΓ)))))
      (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf Sx .unit)) (CTy.effOf Sx .unit))
        (.there (.here (.cons (.cons hΓ.toP))))))
      (.here (.cons (.cons (.cons hΓ.toP))))

theorem rowAt_R2 (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) : RowAt Ξ R2 :=
  rowAt_ofEff_append h2 (by decide) (by simp)
    (rowAt_ofEff_append h1 (by decide) (by simp) (rowAt_nil Ξ))

theorem d_algL2 (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ algL2 (.comp (CTy.effOf R2 .unit)) := by
  refine .effLet (A := .unit) (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ) (fun _ => dead_noLive hΓ)
    ?_ ?_
  · refine .effLet (A := .unit) (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ)
      (fun _ => dead_noLive hΓ) (.effPerform (o := ⟨2, 0, .aff, .unit, .unit⟩) (rowAt_R2 h1 h2)
        rfl rfl (.unitI hΓ.toP)) ?_
    exact .effSub (S := []) (rowLe_nil _) (.ret (.var (.here hΓ.toP)))
  · exact .effSub (S := []) (rowLe_nil _) (.ret (.unitI (.drop rfl hΓ.toP)))

/-- **The witness is typed by Core's kernel with its inner rows tied**, at `F 1`, at every effect
context declaring `exn` at `1` and `wait` at `2`. -/
theorem d_algAffProg (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) :
    CDerivesAt Ξ LifeCtx.empty [] algAffProg (.comp (.ret .unit)) := by
  refine d_withHAt (S := []) (rowAt_ofEff_append h1 (by decide) (by simp) (rowAt_nil Ξ))
    (by decide) (by simp) .nil (d_abortClAt (S := []) .nil) ?_
  exact d_withHAt (S := Sx) (rowAt_R2 h1 h2) (by decide) (by simp [Row.ofEff]) (by cdead)
    (d_holdCancelCl h1 (by cdead)) (d_algL2 h1 h2 (by cdead))

end AffTyping

/-! ### The witness's runs -/

/-- The two handler frames, after the program's bindings. -/
def algAffK₀ : Kont :=
  (handleK 1 (qualsVal [.aff]).1 (.lam (.var 0)) [abortCl]).comp
    (handleK 2 (qualsVal [.aff]).1 (.lam (.var 0)) [holdCancelCl])

theorem algAff_c : lookEnd 4 algAffProg = algAffK₀.plug algL2 := by rfl

def H2E : Expr := hndValE 2 (qualsVal [.aff]).1 (.lam (.var 0)) [holdCancelCl]

theorem isVal_H2E : IsVal H2E :=
  .pair .prim (.pair (qualsVal [.aff]).2 (.pair .lam (.pair .lam .unit)))

/-- The handler value of `2`. -/
def H2V : Val := ⟨H2E, isVal_H2E⟩

/-- What lies between the handler of `2` and the operation, on each side. -/
def KL2 : Kont := .appR (.lam .unit) (.appR (.lam (.var 0)) .hole)

def KR2 : Kont := .appR (.lam (.app (.lam .unit) (.var 0))) .hole

def clV : Val := ⟨holdCancelCl, .lam⟩

def K1₀ : Kont := handleK 1 (qualsVal [.aff]).1 (.lam (.var 0)) [abortCl]

def raise1 : Expr := raiseE (opArgE 1 0 (.val .unit))

theorem not_isVal_raise1 : ¬ IsVal raise1 := fun h =>
  plug_raise_ne_val .hole (Val.pair (Val.i32 1) (Val.pair (Val.i32 0) Val.unit)) ⟨_, h⟩ rfl

/-- The context of the allocation of `κ`'s cell after the catch, on the side whose `κ` holds `K`. -/
def KA (K : Kont) : Kont :=
  K1₀.comp (.appR (.val clV) (.pairR Val.unit
    (.appR (.val (Val.lam (kappaCBody true 2 H2V K))) .hole)))

/-- The context of the release of `κ`'s cell, on the side whose `κ` holds `K`: the outer handler of
`1`, the raise after the finaliser, the finaliser's handler of `1`, and `κ`'s cancel after the
release. -/
def KF (K : Kont) : Kont :=
  K1₀.comp ((Kont.seq .hole raise1).comp (K1₀.comp (Kont.seq .hole
    (BoCa.BoLo.ccatchE (hndE H2V (K.plug (raiseE (.val (BoCa.BoLo.cancelVal (2 :: K.hndNames)
      none)))))))))

/-- The finaliser each side's frame holds, at the cell `ℓ`:
`λ_. handle_1 (κ (inj₂ ())) with (λ_. ())`, `κ` the side's continuation. -/
def DV (K : Kont) (ℓ : Loc) : Val :=
  Val.lam (withH 1 .aff abortCl (.app (kappaC true ℓ 2 H2V K) (.val (Val.inj₂ Val.unit))))

/-- The `then` branch each side's frame holds, at the cell `ℓ`: `λy. κ (inj₁ ()) y`. -/
def NV (K : Kont) (ℓ : Loc) : Val :=
  Val.lam (.app (.app (kappaC true ℓ 2 H2V K) (.val (Val.inj₁ Val.unit))) (.var 0))

/-- The catch, on each side: the next step allocates `κ`'s cell. -/
theorem algL2_hop : lookEnd 1 (algAffK₀.plug algL2) = (KA KL2).plug (allocE Val.unit) := by rfl

theorem algR2_hop : lookEnd 1 (algAffK₀.plug algR2) = (KA KR2).plug (allocE Val.unit) := by rfl

/-- From the cell `ℓ`'s allocation, the clause raises, the finaliser fires and cancels `κ`, up to
the release of `ℓ`. -/
theorem algL2_free (ℓ : Loc) : lookEnd 10 ((KA KL2).plug (.val (Val.loc ℓ))) =
    (KF KL2).plug (BoCa.BoLo.freeE (.val (Val.loc ℓ))) := by rfl

theorem algR2_free (ℓ : Loc) : lookEnd 10 ((KA KR2).plug (.val (Val.loc ℓ))) =
    (KF KR2).plug (BoCa.BoLo.freeE (.val (Val.loc ℓ))) := by rfl

/-- After the release, the cancel ends, the finaliser ends, the raise reaches the outer handler and
the program answers `()`. -/
theorem algL2_end : lookEnd 7 ((KF KL2).plug (.val Val.unit)) = .unit := by rfl

theorem algR2_end : lookEnd 7 ((KF KR2).plug (.val Val.unit)) = .unit := by rfl

/-- Each side's run from the cell's allocation, split at its one finaliser step. -/
theorem algL2_q (ℓ : Loc) : lookRun 10 ((KA KL2).plug (.val (Val.loc ℓ))) =
    (lookRun 10 ((KA KL2).plug (.val (Val.loc ℓ)))).take 3 ++
      (K1₀, ubindE (Val.pair (NV KL2 ℓ) (DV KL2 ℓ)) raise1,
        .seq (.app (.val (DV KL2 ℓ)) (.val .unit)) raise1) ::
      (lookRun 10 ((KA KL2).plug (.val (Val.loc ℓ)))).drop 4 := by rfl

theorem algR2_q (ℓ : Loc) : lookRun 10 ((KA KR2).plug (.val (Val.loc ℓ))) =
    (lookRun 10 ((KA KR2).plug (.val (Val.loc ℓ)))).take 3 ++
      (K1₀, ubindE (Val.pair (NV KR2 ℓ) (DV KR2 ℓ)) raise1,
        .seq (.app (.val (DV KR2 ℓ)) (.val .unit)) raise1) ::
      (lookRun 10 ((KA KR2).plug (.val (Val.loc ℓ)))).drop 4 := by rfl

/-- What tells the two finalisers apart: the right side's frame `□ to x. (ret x to y. ret ())`,
which the left side's continuation does not hold. -/
def algPat : Expr → Bool
  | .lam (.app (.lam .unit) (.var 0)) => true
  | _ => false

theorem finE_DL2_pat (ℓ : Loc) : occursIn algPat (finE (DV KL2 ℓ).1) = false := by rfl

theorem finE_DR2_pat (ℓ : Loc) : occursIn algPat (finE (DV KR2 ℓ).1) = true := by rfl

/-- **The two finalisers differ as terms**, at every pair of cells. -/
theorem finE_D2_ne (ℓ ℓ' : Loc) : finE (DV KL2 ℓ).1 ≠ finE (DV KR2 ℓ').1 := fun h => by
  have := finE_DL2_pat ℓ; rw [h, finE_DR2_pat] at this; cases this

section AlgW
variable (Ξ : EffCtx)

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- The label of the name `2`, where `Ξ` declares `wait : 1 ↠ 1` affine. -/
def labWait (h2 : Ξ 2 = Ew) : (orowAlg Ξ).Lab :=
  ⟨2, by decide, by rw [h2]; simp, by rw [h2]; simp⟩

theorem obs_hopL (R : (𝕁).Runner) (s : R.St) : (𝕁).obs (chainPath R Adequacy.emptyMem s
    (lookRun 1 (algAffK₀.plug algL2))) = [] := obs_chainPath (J := J₁) _ _ _ _ rfl

theorem obs_hopR (R : (𝕁).Runner) (s : R.St) : (𝕁).obs (chainPath R Adequacy.emptyMem s
    (lookRun 1 (algAffK₀.plug algR2))) = [] := obs_chainPath (J := J₁) _ _ _ _ rfl

theorem obs_endL (R : (𝕁).Runner) (s : R.St) : (𝕁).obs (chainPath R Adequacy.emptyMem s
    (lookRun 7 ((KF KL2).plug (.val Val.unit)))) = [] := obs_chainPath (J := J₁) _ _ _ _ rfl

theorem obs_endR (R : (𝕁).Runner) (s : R.St) : (𝕁).obs (chainPath R Adequacy.emptyMem s
    (lookRun 7 ((KF KR2).plug (.val Val.unit)))) = [] := obs_chainPath (J := J₁) _ _ _ _ rfl

theorem obs_midL (R : (𝕁).Runner) (μ : Heap) (s : R.St) (ℓ : Loc) : (𝕁).obs (chainPath R μ s
    (lookRun 10 ((KA KL2).plug (.val (Val.loc ℓ))))) = [.fire (finE (DV KL2 ℓ).1)] := by
  rw [algL2_q ℓ, obs_chainPath_one _ _ _ _ _ _ rfl rfl]
  simp only
  erw [labelOf_fire not_isVal_raise1]
  rfl

theorem obs_midR (R : (𝕁).Runner) (μ : Heap) (s : R.St) (ℓ : Loc) : (𝕁).obs (chainPath R μ s
    (lookRun 10 ((KA KR2).plug (.val (Val.loc ℓ))))) = [.fire (finE (DV KR2 ℓ).1)] := by
  rw [algR2_q ℓ, obs_chainPath_one _ _ _ _ _ _ rfl rfl]
  simp only
  erw [labelOf_fire not_isVal_raise1]
  rfl

/-- **Algebraicity observing a finaliser's code fails at `J₁`**, its inner rows tied to the effect
context.  `algAffProg`, typed by Core's kernel at `F 1` with every handler's and operation's row
tied to `Ξ`, reaches the law's left side under its two handlers.  The left side's complete run
allocates `κ`'s cell, fires `λ_. handle_1 (κ (inj₂ ())) with (λ_. ())` and answers `()`; every
complete run of the right side fires the finaliser that mentions its own `κ`, which holds the frame
`□ to x. (ret x to y. ret ())`, at whatever cell the allocation picks.  Kept as a record: the law as
restated holds at this configuration (`algLaw_algAffProg`). -/
theorem not_algLawCode_J₁ (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) : ¬ (𝕁).AlgLawCode := by
  intro hA
  have hRA := hA (labWait Ξ h2) 0 (𝕁).unitV ⟨OVTy.ofV .unit, OVTy.ofV .unit, .affine⟩ (.var 0)
    (.val .unit) (by show ((Ξ 2).map _)[0]? = _; rw [h2]; rfl) (by intro h; cases h)
  have hreach : (𝕁).RReach (𝕁).R₀ ((𝕁).rinit (𝕁).R₀ algAffProg)
      ((Adequacy.emptyMem, lookEnd 4 algAffProg), ()) :=
    rreach_of_chain (𝕁).R₀ (lookRun_sound (ℍ := ℍ) 4 algAffProg)
  have hder : (𝕁).der [] algAffProg ((𝕁).F (orowAlg Ξ).unit (OVTy.ofV .unit)) :=
    der_J₁_ret (by decide) (d_algAffProg h1 h2)
  have hfr : ∃ ℓ, (Adequacy.emptyMem : Heap) ℓ = none := ⟨0, rfl⟩
  -- the left side's run: the catch, the cell at `0`, the finaliser, the release, the answer
  have hopL := lookRun_sound (ℍ := ℍ) 1 (algAffK₀.plug algL2)
  rw [algL2_hop] at hopL
  have midL := lookRun_sound (ℍ := ℍ) 10 ((KA KL2).plug (.val (Val.loc 0)))
  rw [algL2_free] at midL
  have endL := lookRun_sound (ℍ := ℍ) 7 ((KF KL2).plug (.val Val.unit))
  rw [algL2_end] at endL
  have hfree : Head (ℍ := ℍ) (Adequacy.emptyMem.upd 0 Val.unit)
      (BoCa.BoLo.freeE (.val (Val.loc 0))) ((Adequacy.emptyMem.upd 0 Val.unit).del 0)
      (.val Val.unit) :=
    Head.free _ 0 Val.unit (Heap.upd_same _ _ _)
  have hL : (𝕁).ObsFrom (𝕁).R₀ ((Adequacy.emptyMem, algAffK₀.plug algL2), ()) (𝕁).unitV
      [.fire (finE (DV KL2 0).1)] := by
    refine (obsFrom_chain_obs_iff (𝕁).R₀ hopL _ _).2 ⟨[.fire (finE (DV KL2 0).1)], ?_, ?_⟩
    · erw [obs_hopL Ξ (𝕁).R₀]; rfl
    refine (obsFrom_alloc_ex_iff (𝕁).R₀ (KA KL2) Val.unit hfr _ _).2 ⟨0, rfl, ?_⟩
    refine (obsFrom_chain_obs_iff (𝕁).R₀ midL _ _).2 ⟨[], ?_, ?_⟩
    · erw [obs_midL Ξ (𝕁).R₀]; rfl
    refine (obsFrom_mstep_iff (𝕁).R₀ hfree rfl (by rw [labelOf_tau_of rfl]; rfl) _ _).2 ?_
    rw [del_upd_fresh rfl]
    have := obsFrom_of_chain (J := J₁) (Ξ := Ξ) (𝕁).R₀ (μ := Adequacy.emptyMem) (s := ()) endL
      .unit
    erw [obs_endL Ξ (𝕁).R₀] at this
    exact this
  have h := (hRA (𝕁).R₀ r₀_respects algAffProg _ (OVTy.ofV .unit)
    ((Adequacy.emptyMem, lookEnd 4 algAffProg), ()) algAffK₀ .unit hder hreach algAff_c _ _).mp
    (by rw [algAff_c]; exact hL)
  -- the right side's runs: the catch, a cell at some `ℓ`, then the finaliser's event
  have hopR := lookRun_sound (ℍ := ℍ) 1 (algAffK₀.plug algR2)
  rw [algR2_hop] at hopR
  obtain ⟨tr₁, htr₁, h₁⟩ := (obsFrom_chain_obs_iff (𝕁).R₀ hopR _ _).1 h
  obtain ⟨ℓ, -, h₂⟩ := (obsFrom_alloc_ex_iff (𝕁).R₀ (KA KR2) Val.unit hfr _ _).1 h₁
  have midR := lookRun_sound (ℍ := ℍ) 10 ((KA KR2).plug (.val (Val.loc ℓ)))
  rw [algR2_free] at midR
  obtain ⟨tr₂, htr₂, -⟩ := (obsFrom_chain_obs_iff (𝕁).R₀ midR _ _).1 h₂
  erw [obs_midR Ξ (𝕁).R₀] at htr₂
  erw [obs_hopR Ξ (𝕁).R₀, List.nil_append] at htr₁
  rw [← htr₁] at htr₂
  have := List.cons.inj htr₂
  injection this.1 with h'
  exact finE_D2_ne 0 ℓ h'

/-- **S4's cancel at a cell is not vacuous at `J₁`**: `algAffProg`'s run reaches, after the catch of
the affine `wait`, the cell's allocation and the finaliser's start, the finaliser's cancel of `κ` at
its cell, the memory holding the cell — a configuration at which every premise of
`CancelCellLaw` holds. -/
theorem cancelCell_algAffProg (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) :
    ∃ (c : Heap × Expr) (ℓ : Loc) (K₀ : Kont) (H : OVal × List OVal) (K : Kont),
      (𝕁).cellFree c ℓ ∧ (𝕁).Live ((𝕁).withCell c ℓ) ∧
      (𝕁).term ((𝕁).withCell c ℓ) =
        (𝕁).plug K₀ ((𝕁).cancel ((𝕁).captureAt .affine (labWait Ξ h2) H K ℓ)) := by
  have hℓ : (Adequacy.emptyMem : Heap) 0 = none := rfl
  have hreach : (𝕁).RReach (𝕁).R₀ ((𝕁).rinit (𝕁).R₀ algAffProg)
      ((Adequacy.emptyMem.upd 0 Val.unit, (K1₀.comp ((Kont.seq .hole raise1).comp K1₀)).plug
        (.app (kappaC true 0 2 H2V KL2) (.val (Val.inj₂ Val.unit)))), ()) := by
    have h₀ := rreach_of_chain (𝕁).R₀ (μ := Adequacy.emptyMem) (s := ())
      (lookRun_sound (ℍ := ℍ) 4 algAffProg)
    rw [algAff_c] at h₀
    have h₁ := rreach_of_chain (𝕁).R₀ (μ := Adequacy.emptyMem) (s := ())
      (lookRun_sound (ℍ := ℍ) 1 (algAffK₀.plug algL2))
    rw [algL2_hop] at h₁
    have hal : (𝕁).RStep (𝕁).R₀ ((Adequacy.emptyMem, (KA KL2).plug (allocE Val.unit)), ())
        (labelOf orowRF Ξ (allocE Val.unit))
        ((Adequacy.emptyMem.upd 0 Val.unit, (KA KL2).plug (.val (Val.loc 0))), ()) :=
      .mach (OStep.mach (Head.alloc _ Val.unit 0 hℓ))
    have h₂ := rreach_of_chain (𝕁).R₀ (μ := Adequacy.emptyMem.upd 0 Val.unit) (s := ())
      (lookRun_sound (ℍ := ℍ) 7 ((KA KL2).plug (.val (Val.loc 0))))
    have e : lookEnd 7 ((KA KL2).plug (.val (Val.loc 0))) =
        (K1₀.comp ((Kont.seq .hole raise1).comp K1₀)).plug
          (.app (kappaC true 0 2 H2V KL2) (.val (Val.inj₂ Val.unit))) := rfl
    rw [e] at h₂
    exact ((h₀.trans h₁).tail ⟨_, hal⟩).trans h₂
  refine ⟨(Adequacy.emptyMem, (K1₀.comp ((Kont.seq .hole raise1).comp K1₀)).plug
      (.app (kappaC true 0 2 H2V KL2) (.val (Val.inj₂ Val.unit)))), 0,
    K1₀.comp ((Kont.seq .hole raise1).comp K1₀), (⟨.lam (.var 0), .lam⟩, [⟨holdCancelCl, .lam⟩]),
    KL2, hℓ,
    ⟨algAffProg, _, (𝕁).R₀, (), r₀_respects, der_J₁_ret (by decide) (d_algAffProg h1 h2), hreach⟩, ?_⟩
  have hq : qsOf Ξ 2 = (qualsVal [.aff]).1 := by rw [qsOf, h2]; rfl
  show _ = (K1₀.comp ((Kont.seq .hole raise1).comp K1₀)).plug (cancelE (captureAtE
    (decide (A.OpClass.affine = .affine)) 0 2 (qsOf Ξ 2) (.lam (.var 0)) [holdCancelCl] KL2))
  rw [hq]
  unfold captureAtE
  rw [dif_pos (show IsVal (hndValE 2 (qualsVal [.aff]).1 (.lam (.var 0)) [holdCancelCl]) from
    isVal_H2E)]
  rfl

/-- **The complete runs of one side of the witness**, from its stretches: a chain from the side's
start to the allocation of `κ`'s cell, showing nothing; at each location, a chain from the cell to
its release, showing one finaliser's start; and a chain from the release's answer to `()`, showing
nothing.  Every complete run allocates the cell at some location the memory leaves free, shows that
location's finaliser start, and answers `()`. -/
theorem obsFrom_algSide (R : (𝕁).Runner) (s : R.St) {e : Expr} {K : Kont}
    {q₁ q₃ : List (Kont × Expr × Expr)} {q₂ : Loc → List (Kont × Expr × Expr)}
    (hop : HeadChain (ℍ := ℍ) e q₁ ((KA K).plug (allocE Val.unit)))
    (hq₁ : (𝕁).obs (chainPath R Adequacy.emptyMem s q₁) = [])
    (hmid : ∀ ℓ, HeadChain (ℍ := ℍ) ((KA K).plug (.val (Val.loc ℓ))) (q₂ ℓ)
      ((KF K).plug (BoCa.BoLo.freeE (.val (Val.loc ℓ)))))
    (hq₂ : ∀ ℓ, (𝕁).obs (chainPath R (Adequacy.emptyMem.upd ℓ Val.unit) s (q₂ ℓ)) =
      [.fire (finE (DV K ℓ).1)])
    (hend : HeadChain (ℍ := ℍ) ((KF K).plug (.val Val.unit)) q₃ .unit)
    (hq₃ : (𝕁).obs (chainPath R Adequacy.emptyMem s q₃) = []) (v : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((Adequacy.emptyMem, e), s) v tr ↔
      v.1 = Expr.unit ∧ ∃ ℓ, tr = [.fire (finE (DV K ℓ).1)] := by
  have hfr : ∃ ℓ, (Adequacy.emptyMem : Heap) ℓ = none := ⟨0, rfl⟩
  -- from the cell's release on: the release, the end, the answer
  have rel : ∀ ℓ tr', (𝕁).ObsFrom R ((Adequacy.emptyMem.upd ℓ Val.unit,
      (KF K).plug (BoCa.BoLo.freeE (.val (Val.loc ℓ)))), s) v tr' ↔ v.1 = Expr.unit ∧ tr' = [] := by
    intro ℓ tr'
    have hfree : Head (ℍ := ℍ) (Adequacy.emptyMem.upd ℓ Val.unit)
        (BoCa.BoLo.freeE (.val (Val.loc ℓ))) ((Adequacy.emptyMem.upd ℓ Val.unit).del ℓ)
        (.val Val.unit) :=
      Head.free _ ℓ Val.unit (Heap.upd_same _ _ _)
    refine (obsFrom_mstep_iff R hfree rfl (by rw [labelOf_tau_of rfl]; rfl) v tr').trans ?_
    rw [del_upd_fresh rfl]
    refine (obsFrom_chain_obs_iff R hend v tr').trans ?_
    rw [hq₃]
    constructor
    · rintro ⟨tr'', htr, h⟩
      obtain ⟨hv, h₀⟩ := (obsFrom_val_iff R Val.unit v tr'').1 h
      rw [htr, h₀]
      exact ⟨hv, rfl⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨[], rfl, (obsFrom_val_iff R Val.unit v []).2 ⟨hv, rfl⟩⟩
  refine (obsFrom_chain_obs_iff R hop v tr).trans ?_
  rw [hq₁]
  constructor
  · rintro ⟨tr₁, htr, h₁⟩
    obtain ⟨ℓ, -, h₂⟩ := (obsFrom_alloc_ex_iff R (KA K) Val.unit hfr v tr₁).1 h₁
    obtain ⟨tr₂, htr₂, h₃⟩ := (obsFrom_chain_obs_iff R (hmid ℓ) v tr₁).1 h₂
    obtain ⟨hv, h₄⟩ := (rel ℓ tr₂).1 h₃
    rw [hq₂ ℓ, h₄] at htr₂
    rw [htr, htr₂]
    exact ⟨hv, ℓ, rfl⟩
  · rintro ⟨hv, ℓ, rfl⟩
    refine ⟨[.fire (finE (DV K ℓ).1)], rfl, ?_⟩
    refine (obsFrom_alloc_ex_iff R (KA K) Val.unit hfr v _).2 ⟨ℓ, rfl, ?_⟩
    refine (obsFrom_chain_obs_iff R (hmid ℓ) v _).2 ⟨[], ?_, (rel ℓ []).2 ⟨hv, rfl⟩⟩
    rw [hq₂ ℓ]; rfl

/-- The complete runs of the witness's left side: the cell at some location `ℓ`, the finaliser
holding the left side's `κ` at `ℓ` started, the answer `()`. -/
theorem obsFrom_algAffL (R : (𝕁).Runner) (s : R.St) (v : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((Adequacy.emptyMem, algAffK₀.plug algL2), s) v tr ↔
      v.1 = Expr.unit ∧ ∃ ℓ, tr = [.fire (finE (DV KL2 ℓ).1)] := by
  have hop := lookRun_sound (ℍ := ℍ) 1 (algAffK₀.plug algL2)
  rw [algL2_hop] at hop
  have hend := lookRun_sound (ℍ := ℍ) 7 ((KF KL2).plug (.val Val.unit))
  rw [algL2_end] at hend
  refine obsFrom_algSide Ξ R s hop (obs_hopL Ξ R s) (fun ℓ => ?_) (fun ℓ => obs_midL Ξ R _ s ℓ)
    hend (obs_endL Ξ R s) v tr
  have hmid := lookRun_sound (ℍ := ℍ) 10 ((KA KL2).plug (.val (Val.loc ℓ)))
  rwa [algL2_free] at hmid

/-- The complete runs of the witness's right side: the same, the finaliser holding the right
side's `κ`. -/
theorem obsFrom_algAffR (R : (𝕁).Runner) (s : R.St) (v : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((Adequacy.emptyMem, algAffK₀.plug algR2), s) v tr ↔
      v.1 = Expr.unit ∧ ∃ ℓ, tr = [.fire (finE (DV KR2 ℓ).1)] := by
  have hop := lookRun_sound (ℍ := ℍ) 1 (algAffK₀.plug algR2)
  rw [algR2_hop] at hop
  have hend := lookRun_sound (ℍ := ℍ) 7 ((KF KR2).plug (.val Val.unit))
  rw [algR2_end] at hend
  refine obsFrom_algSide Ξ R s hop (obs_hopR Ξ R s) (fun ℓ => ?_) (fun ℓ => obs_midR Ξ R _ s ℓ)
    hend (obs_endR Ξ R s) v tr
  have hmid := lookRun_sound (ℍ := ℍ) 10 ((KA KR2).plug (.val (Val.loc ℓ)))
  rwa [algR2_free] at hmid

/-- **The witness is on the right side of algebraicity as restated**: at the configuration
`algAffProg` reaches with the law's left side under its two handlers (`not_algLawCode_J₁`'s), under
every runner, each side's complete runs answer `()` and show one finaliser's start, read without
its code.  The finalisers differ as terms (`finE_D2_ne`) and start at the same point of each run. -/
theorem algLaw_algAffProg (R : (𝕁).Runner) (s : R.St) (v : OVal)
    (tr : List (A.Ev (orowAlg Ξ).Lab OVal Unit)) :
    (𝕁).ObsStartFrom R ((Adequacy.emptyMem, algAffK₀.plug algL2), s) v tr ↔
      (𝕁).ObsStartFrom R ((Adequacy.emptyMem, algAffK₀.plug algR2), s) v tr := by
  have key : ∀ (K : Kont) (e : Expr), (∀ v tr, (𝕁).ObsFrom R ((Adequacy.emptyMem, e), s) v tr ↔
      v.1 = Expr.unit ∧ ∃ ℓ, tr = [.fire (finE (DV K ℓ).1)]) →
      ((𝕁).ObsStartFrom R ((Adequacy.emptyMem, e), s) v tr ↔ v.1 = Expr.unit ∧ tr = [.fire ()]) := by
    intro K e hK
    refine (𝕁).obsStartFrom_iff.trans ?_
    constructor
    · rintro ⟨tr₀, h₀, rfl⟩
      obtain ⟨hv, ℓ, rfl⟩ := (hK v tr₀).1 h₀
      exact ⟨hv, rfl⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨_, (hK v _).2 ⟨hv, 0, rfl⟩, rfl⟩
  exact (key KL2 _ (obsFrom_algAffL Ξ R s)).trans (key KR2 _ (obsFrom_algAffR Ξ R s)).symm

/-- **Algebraicity as restated reads `algAffProg`'s configuration, and holds there**: the program
is typed by `J₁` with its rows tied (at `F 1`), it reaches the law's left side under its two
handlers under every runner, and from there each side's complete runs show the same answers and
traces with a finaliser's start read without its code. -/
theorem algAffProg_start (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) :
    (𝕁).der [] algAffProg ((𝕁).F (orowAlg Ξ).unit (OVTy.ofV .unit)) ∧
    (𝕁).term (Adequacy.emptyMem, algAffK₀.plug algL2) = (𝕁).plug algAffK₀
      ((𝕁).bind ((𝕁).bind ((𝕁).perform (labWait Ξ h2) 0 (𝕁).unitV) (.var 0)) (.val .unit)) ∧
    (𝕁).term (Adequacy.emptyMem, algAffK₀.plug algR2) = (𝕁).plug algAffK₀
      ((𝕁).bind ((𝕁).perform (labWait Ξ h2) 0 (𝕁).unitV) ((𝕁).bind (.var 0) (.val .unit))) ∧
    (∀ R : (𝕁).Runner, (𝕁).RReach R ((𝕁).rinit R algAffProg)
      ((Adequacy.emptyMem, algAffK₀.plug algL2), R.s₀)) ∧
    ∀ (R : (𝕁).Runner) (s : R.St) (v : OVal) (tr : List (A.Ev (orowAlg Ξ).Lab OVal Unit)),
      (𝕁).ObsStartFrom R ((Adequacy.emptyMem, algAffK₀.plug algL2), s) v tr ↔
        (𝕁).ObsStartFrom R ((Adequacy.emptyMem, algAffK₀.plug algR2), s) v tr :=
  ⟨der_J₁_ret (by decide) (d_algAffProg h1 h2), rfl, rfl, fun R => by
    have h := rreach_of_chain R (μ := Adequacy.emptyMem) (s := R.s₀)
      (lookRun_sound (ℍ := ℍ) 4 algAffProg)
    rw [algAff_c] at h
    exact h, algLaw_algAffProg Ξ⟩

end AlgW

/-! ### The witness at an unrestricted continuation, outside the tied kernel -/

/-- `λ(a, k). raise (1, 0, ()) then y. () unwind ((λz. ()) k)`: a clause that raises `exn` inside
a finaliser frame whose finaliser holds `k`. -/
def holdRaiseCl : Expr :=
  .val (.lam (.letpair (.var 0)
    (thenE (.val .unit) (bindE (.var 1) (.val .unit)) (raiseE (opArgE 1 0 (.val .unit))))))

/-- Algebraicity's left side at the name `5`: `(tick () to x. ret x) to y. ret ()`. -/
def algL5 : Expr := bindE (bindE (performE (opArgE 5 0 (.val .unit))) (.var 0)) (.val .unit)

/-- `handle_1 (handle_5 algL5 with holdRaiseCl) with (λ_. ())`. -/
def algFireProg : Expr := withH 1 .aff abortCl (withH 5 .unr holdRaiseCl algL5)

/-- An `unr` operation `1 ↠ 1`: the handler of `5` reads `5`'s operation so. -/
abbrev Eu : List (Qual × VTy × VTy) := [(.unr, .unit, .unit)]

/-- The row `algFireProg`'s handler of `5` handles. -/
abbrev R5 : Row := Row.ofEff 5 Eu 0 ++ Sx

theorem d_holdRaiseCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ holdRaiseCl (.val (clauseTy Sx .unit (.unr, .unit, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .effThen (A := .unit) (.right (.left (.dead (deadSplit hΓ)))) ?_ ?_
    (fun h => absurd h (by simp [Row.Unr, Row.ofEff])) ?_ ?_ ?_
  · intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  · simp [Row.Uniq, Row.ofEff]
  · exact .effRaise (o := ⟨1, 0, .aff, .unit, .zero⟩) rfl rfl .unit
      (.unitI (.cons (.drop rfl (.cons hΓ.toP))))
  · exact .effSub (S := []) (rowLe_nil _)
      (.ret (.unitI (.drop rfl (.drop rfl (.cons (.cons hΓ.toP))))))
  · exact .bind (A := kTy Sx .unit .unr .unit) (.dead (.left (.dead (.dead (deadSplit hΓ)))))
      (.ret (.var (.there (.here (.cons (.cons hΓ.toP))))))
      (.ret (.unitI (.drop rfl (.cons (.cons (.cons (.cons hΓ.toP)))))))

theorem d_algL5 {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ algL5 (.comp (CTy.effOf R5 .unit)) := by
  refine .effLet (A := .unit) (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ) (fun _ => dead_noLive hΓ)
    ?_ ?_
  · refine .effLet (A := .unit) (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ)
      (fun _ => dead_noLive hΓ) (.effPerform (o := ⟨5, 0, .unr, .unit, .unit⟩) rfl rfl
        (.unitI hΓ.toP)) ?_
    exact .effSub (S := []) (rowLe_nil _) (.ret (.var (.here hΓ.toP)))
  · exact .effSub (S := []) (rowLe_nil _) (.ret (.unitI (.drop rfl hΓ.toP)))

/-- `withH` in Core's kernel: one clause and the identity return clause. -/
theorem d_withH {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {q : Qual} {B C : VTy}
    {n : UInt32} {cl e : Expr} (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hΓ : Ctx.Dead Γ)
    (hcl : CDerives Δ Γ cl (.val (clauseTy S A (q, B, C))))
    (he : CDerives Δ (⟨retTy S A A, false⟩ :: ⟨clausesTy S A [(q, B, C)], false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff n [(q, B, C)] 0 ++ S) A))) :
    CDerives Δ Γ (withH n q cl e) (.comp (CTy.effOf S A)) := by
  refine .bind (deadSplit hΓ) (.ret (.tensorI (deadSplit hΓ) hcl (.unitI hΓ.toP))) ?_
  refine .bind (A := retTy S A A) (.right (deadSplit hΓ)) (.ret ?_) ?_
  · exact .bangThunkV (dead_noLive (Ctx.Dead.cons hΓ)) rfl
      (.lam (.effSub (S := []) (rowLe_nil _) (.ret (.var (.here (Ctx.Dead.cons hΓ).toP)))))
  exact .effHandle (E := [(q, B, C)]) (.left (.left (deadSplit hΓ)))
    (.left (.right (deadSplit hΓ))) (.here (Ctx.Dead.cons hΓ).toP) (.there (.here hΓ.toP)) hn0
    hnS (by simp) he

/-- **Core's kernel types `algFireProg`**, at `F 1`, with its handler of `5` at `R5`. -/
theorem d_algFireProg : CDerives LifeCtx.empty [] algFireProg (.comp (.ret .unit)) := by
  refine d_withH (S := []) (by decide) (by simp) .nil (d_abortClNU nu_nil .nil).toCDerives ?_
  exact d_withH (S := Sx) (by decide) (by simp [Row.ofEff]) (by cdead) (d_holdRaiseCl (by cdead))
    (d_algL5 (by cdead))

/-- **`R5` is not tied to `ΞA`**: it finds the name `5`'s operation at `unr`, where `ΞA` declares
`tick : 1 ↠ 1` linear. -/
theorem not_rowAt_R5 : ¬ RowAt ΞA R5 := by
  intro h
  obtain ⟨-, -, hg⟩ := h 5 0 ⟨5, 0, .unr, .unit, .unit⟩ rfl
  simp [ΞA] at hg

/-- **A tied derivation of `withH n q cl e`**, `e` closed: the handler's tag `[q]` is a prefix of
`Ξ`'s qualifiers of `n`, and the handled body `e` is typed.  The two `let`s are inverted
(`derAt_let`; through the λ-value at a call-by-value application, `derAt_lam`; at `[let-poly]`, the
handler with the return clause in place), then the handler (`derAt_hnd`). -/
theorem derAt_withH {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {n : UInt32} {q : Qual}
    {cl e : Expr} {j : Jdg} (hcl : closedAt 0 e = true) (h : CDerivesAt Ξ Δ Γ (withH n q cl e) j) :
    [q] <+: (Ξ n).map Prod.fst ∧
      ∃ (Δ' : LifeCtx) (Γ' : Ctx VTy) (C : CTy), CDerivesAt Ξ Δ' Γ' e (.comp C) := by
  -- the handler, at any lifetime context
  have hnd : ∀ {Δ' : LifeCtx} {Γ' : Ctx VTy} {C : CTy} (H : Expr),
      CDerivesAt Ξ Δ' Γ' (.app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n)))
        (.pair (qualsVal [q]).1 H))) e) (.comp C) →
      [q] <+: (Ξ n).map Prod.fst ∧
        ∃ (Δ' : LifeCtx) (Γ' : Ctx VTy) (C : CTy), CDerivesAt Ξ Δ' Γ' e (.comp C) := by
    intro Δ' Γ' C H hH
    obtain ⟨hp, Γ'', C', he⟩ := derAt_hnd hH n _ H e rfl
    exact ⟨hp [q] rfl, Δ', Γ'', C', he⟩
  -- the inner `let` of the return clause, at any lifetime context
  have inner : ∀ {Δ' : LifeCtx} {Γ' : Ctx VTy} {C : CTy},
      CDerivesAt Ξ Δ' Γ' (bindE (.val (.lam (.var 0))) (hndTerm n [q] 0 1 e)) (.comp C) →
      [q] <+: (Ξ n).map Prod.fst ∧
        ∃ (Δ' : LifeCtx) (Γ' : Ctx VTy) (C : CTy), CDerivesAt Ξ Δ' Γ' e (.comp C) := by
    intro Δ' Γ' C h₁
    rcases derAt_let h₁ _ _ rfl with ⟨Γ₂, C₂, h₂⟩ | ⟨b, hb, Γ₂, C₂, h₂⟩ | ⟨Γ₂, j₂, h₂⟩
    · exact hnd _ h₂
    · simp only [Expr.val, Val.lam, Expr.lam.injEq] at hb
      subst hb
      rw [hndTerm_eq, subst_hndExpr, shift_hndExpr, subst_closedAt e _ hcl (le_refl _),
        shift_closedAt e 1 hcl (le_refl _)] at h₂
      exact hnd _ h₂
    · obtain ⟨Δ₃, Γ₃, C₃, h₃⟩ := derAt_lam h₂ _ _ _ rfl rfl
      exact hnd _ h₃
  rcases derAt_let h _ _ rfl with ⟨Γ₁, C₁, h₁⟩ | ⟨b, hb, -⟩ | ⟨Γ₁, j₁, h₁⟩
  · exact inner h₁
  · simp [Expr.val] at hb
  · obtain ⟨Δ₂, Γ₂, C₂, h₂⟩ := derAt_lam h₁ _ _ _ rfl rfl
    exact inner h₂

/-- **`algFireProg` has no derivation in Core's kernel with its inner rows tied to `ΞA`**: its inner
handler of `5` carries the tag `unr`, and a tied handler of `5` carries a prefix of `ΞA`'s
`[lin]`. -/
theorem not_derAt_algFireProg {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} :
    ¬ CDerivesAt ΞA Δ Γ algFireProg j := by
  intro h
  obtain ⟨-, Δ', Γ', C, h₁⟩ := derAt_withH (n := 1) (q := .aff) (cl := abortCl) (by rfl) h
  obtain ⟨hp, -⟩ := derAt_withH (n := 5) (q := .unr) (cl := holdRaiseCl) (by rfl) h₁
  rw [show (ΞA 5).map Prod.fst = [.lin] from rfl] at hp
  exact absurd (List.cons_prefix_cons.1 hp).1 (by decide)

/-- **`J₁` at `ΞA` types `algFireProg` at no type.** -/
theorem not_der_algFireProg_J₁ (C : OCTy) :
    ¬ (ourInst (ℍ := ℍ) orowRF ΞA J₁).der [] algFireProg C := by
  rintro ⟨-, ⟨Θ, hΘ, hd⟩ | ⟨-, M, he, -⟩⟩
  · exact not_derAt_algFireProg (coreClosedAt_J₁ ΞA hΘ hd)
  · simp [algFireProg, withH, bindE, driveE, driveMark] at he

/-- **No tied `[handle]` of `5` at `ΞA` carries the tag `unr`**: a tied handler's tags are a prefix
of `ΞA`'s qualifiers of `5`, `[lin]` (`hndTags_of_rowAt`). -/
theorem not_tied_hnd5_unr {E : List (Qual × VTy × VTy)} {S : Row}
    (hAt : RowAt ΞA (Row.ofEff 5 E 0 ++ S)) (hlen : E.length ≤ 2 ^ 32) :
    E.map Prod.fst ≠ [.unr] := by
  intro h
  have hp := hndTags_of_rowAt hAt hlen
  rw [h, show (ΞA 5).map Prod.fst = [.lin] from rfl] at hp
  exact absurd (List.cons_prefix_cons.1 hp).1 (by decide)

/-! ### The laws at the answering class -/

section Answering
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- A's tail-resumptive clause's body at our instance, `c a to b. k.resume b`, with `k` and `a`
the clause's pair. -/
def tailBody (c : Expr) : Expr := bindE (appE c (.var 1)) (resumeE (.var 1) (.var 0))

/-- A's tail-resumptive clause at our instance: `λ(a, k). c a to b. k.resume b`. -/
def tailOf (c : Expr) : Expr := .lam (.letpair (.var 0) (tailBody c))

theorem tailCl_val (c : OVal) : ((ourInst (ℍ := ℍ) RF Ξ J).tailCl c).1 = tailOf c.1 := rfl

theorem subst_closedE {e : Expr} (h : closedAt 0 e = true) (j : ℕ) (s : Val) : e.subst j s = e :=
  subst_closedAt e s h (Nat.zero_le j)

theorem tailBody_closedAt {c : Expr} (hc : closedAt 0 c = true) :
    closedAt 2 (tailBody c) = true := by
  have h1 : closedAt 3 (c.shift 1 0) = true := by
    rw [shift_closed0 hc]; exact closedAt_mono _ hc (by omega)
  simp [tailBody, bindE, appE, resumeE, closedAt, Expr.val, Val.lam, Expr.shift, h1]

theorem tailBody_subst2 {c : Expr} (hc : closedAt 0 c = true) (P : Val) :
    (tailBody c).subst 2 P = tailBody c :=
  subst_closedAt _ P (tailBody_closedAt hc) (le_refl _)

/-- The clause's `letpair`: `a` and `k` substituted, `c a to b. k.resume b` at the operation's
argument and continuation. -/
theorem tailBody_letpair {c κ : Expr} (hc : closedAt 0 c = true) (hκ : closedAt 0 κ = true)
    (hκv : IsVal κ) (v : Val) :
    ((tailBody c).subst 0 (Val.shift 1 0 ⟨κ, hκv⟩)).subst 0 v =
      bindE (appE c v.1) (resumeE κ (.var 0)) := by
  simp [tailBody, bindE, appE, resumeE, Expr.subst, Expr.shift, Expr.val, Val.lam, Val.shift,
    shift_closed0 hc, subst_closedE hc, shift_closed0 hκ, subst_closedE hκ]

theorem resume0_subst {κ : Expr} (hκ : closedAt 0 κ = true) (w : Val) :
    (resumeE κ (.var 0)).subst 0 w = resumeE κ w.1 := by
  simp [resumeE, Expr.subst, shift_closed0 hκ, subst_closedE hκ]

theorem isVal_kappa (n : UInt32) (H : Val) (K : Kont) : IsVal (kappa n H K) := by
  unfold kappa; exact .lam

/-- **The clause after the catch**: `λ(a, k). c a to b. k.resume b` applied to `(v, κ)` reaches
`κ (inj₁ ()) w` quietly when `c v` runs quietly to `w`: the clause's β-step and `letpair`, the code,
the bind, and `resume`'s β-step. -/
theorem quiet_tailBody {c v w : Val} (κ : Expr) (hκv : IsVal κ) (hc : closedAt 0 c.1 = true)
    (hκ : closedAt 0 κ = true) (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    Quiet (ℍ := ℍ) (.app (.val ⟨tailOf c.1, .lam⟩) (.pair (.val v) κ))
      (.app (.app κ (.val (Val.inj₁ .unit))) (.val w)) := by
  let κV : Val := ⟨κ, hκv⟩
  have h₂ := quiet_beta (ℍ := ℍ) .hole (.letpair (.var 0) (tailBody c.1)) (Val.pair v κV)
  simp only [Kont.plug, Expr.subst, if_pos, tailBody_subst2 hc] at h₂
  refine h₂.trans ?_
  have h₃ := quiet_letpair (ℍ := ℍ) .hole v κV (tailBody c.1)
  simp only [Kont.plug] at h₃
  rw [tailBody_letpair hc hκ hκv v] at h₃
  refine h₃.trans ?_
  have h₄ := ((quiet_appE (ℍ := ℍ) .hole c.1 v).trans hq).plug (bindK (resumeE κ (.var 0)))
  simp only [Kont.plug] at h₄
  refine h₄.trans ?_
  have h₅ := quiet_beta (ℍ := ℍ) .hole (resumeE κ (.var 0)) w
  simp only [Kont.plug] at h₅
  rw [resume0_subst hκ w] at h₅
  refine h₅.trans ?_
  have h₆ := quiet_resumeE (ℍ := ℍ) .hole κ w
  simp only [Kont.plug] at h₆
  exact h₆

/-- **A tail-resumptive clause whose code runs quietly resumes in place, at an operation whose
`κ` owns no cell**: `hnd H K[op (n, i, v)]` reaches `hnd H K[w]` quietly.  The steps: the catch,
the clause (`quiet_tailBody`), and `κ`'s four (`quiet_kappa_resume`). -/
theorem quiet_tailClause {n i : UInt32} {qs hr hs c v w : Val} {K : Kont}
    (hci : clauseAt hs.1 i.toNat = some ⟨tailOf c.1, .lam⟩) (hK : K.HasHnd n = false)
    (hu : kappaAt (capTag qs.1 i.toNat) n (hndVal n qs hr hs) K = kappa n (hndVal n qs hr hs) K)
    (hH : closedAt 0 (hndVal n qs hr hs).1 = true) (hKc : closedAt 0 (K.plug .unit) = true)
    (hc : closedAt 0 c.1 = true) (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    Quiet (ℍ := ℍ) (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))))
      (hndE (hndVal n qs hr hs) (K.plug (.val w))) := by
  have hκ : closedAt 0 (kappa n (hndVal n qs hr hs) K) = true := closedAt_kappa n hH hKc
  have h₁ := quiet_hop (ℍ := ℍ) .hole n i qs hr hs ⟨tailOf c.1, .lam⟩ v K hci hK hu
  simp only [Kont.plug] at h₁
  refine h₁.trans ?_
  refine (quiet_tailBody _ (isVal_kappa n _ K) hc hκ hq).trans ?_
  have h₇ := quiet_kappa_resume (ℍ := ℍ) .hole n (hndVal n qs hr hs) K w
  simpa [Kont.plug] using h₇

/-- **A tail-resumptive clause whose code runs quietly resumes in place, at an operation whose
`κ` owns a cell**: `hnd H K[op (n, i, v)]` reaches `hnd H K[w]` around the cell (SPEC §25).  The
catch and the allocation; at the cell's location `ℓ`, `κ`'s β-step at `ℓ`, the clause
(`quiet_tailBody`) and `κ`'s resume branch up to the release of `ℓ`; after it, the rest of the
resume branch (`kappaC_resume_parts`). -/
theorem cellQuiet_tailClause {n i : UInt32} {qs hr hs c v w : Val} {K : Kont} (aff : Bool)
    (hci : clauseAt hs.1 i.toNat = some ⟨tailOf c.1, .lam⟩) (hK : K.HasHnd n = false)
    (hcell : kappaAt (capTag qs.1 i.toNat) n (hndVal n qs hr hs) K =
      kappaCell aff n (hndVal n qs hr hs) K)
    (hH : closedAt 0 (hndVal n qs hr hs).1 = true) (hKc : closedAt 0 (K.plug .unit) = true)
    (hc : closedAt 0 c.1 = true) (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    CellQuiet (ℍ := ℍ) (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))))
      (hndE (hndVal n qs hr hs) (K.plug (.val w))) := by
  have hh : ∀ μ, Head (ℍ := ℍ) μ
      (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))) μ
      (.app (.val ⟨tailOf c.1, .lam⟩) (.pair (.val v) (kappaCell aff n (hndVal n qs hr hs) K))) := by
    intro μ
    have h := Head.hop (ℍ := ℍ) μ n i qs hr hs ⟨tailOf c.1, .lam⟩ v K hci hK
    rwa [hcell] at h
  refine ⟨.appR (.val ⟨tailOf c.1, .lam⟩) (.pairR v
    (.appR (.val (Val.lam (kappaCBody aff n (hndVal n qs hr hs) K))) .hole)),
    Quiet.head .hole hh rfl rfl, fun ℓ => ?_⟩
  refine ⟨Kont.appL (Kont.seq .hole (kResV (hndVal n qs hr hs) K)) w, ?_,
    (kappaC_resume_parts aff ℓ n _ K w).2⟩
  have hb := Quiet.head (ℍ := ℍ) (.appR (.val ⟨tailOf c.1, .lam⟩) (.pairR v .hole))
    (fun μ => Head.beta μ (kappaCBody aff n (hndVal n qs hr hs) K) (Val.loc ℓ)) rfl rfl
  rw [kappaCBody_subst] at hb
  refine hb.trans ?_
  have hκ := closedAt_kappaC aff ℓ n hH hKc
  refine (quiet_tailBody _ (isVal_kappaC aff ℓ n _ K) hc hκ hq).trans ?_
  exact (kappaC_resume_parts aff ℓ n _ K w).1

/-- **A tail-resumptive clause whose code runs quietly resumes in place, calmly**, at every
operation: quietly when its `κ` owns no cell, around the cell when it does. -/
theorem calm_tailClause {n i : UInt32} {qs hr hs c v w : Val} {K : Kont}
    (hci : clauseAt hs.1 i.toNat = some ⟨tailOf c.1, .lam⟩) (hK : K.HasHnd n = false)
    (hH : closedAt 0 (hndVal n qs hr hs).1 = true) (hKc : closedAt 0 (K.plug .unit) = true)
    (hc : closedAt 0 c.1 = true) (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    Calm (ℍ := ℍ) (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))))
      (hndE (hndVal n qs hr hs) (K.plug (.val w))) := by
  by_cases h0 : capTag qs.1 i.toNat = 0
  · exact (cellQuiet_tailClause false hci hK (by rw [kappaAt, if_pos h0]) hH hKc hc hq).calm
  by_cases h1 : capTag qs.1 i.toNat = 1
  · exact (cellQuiet_tailClause true hci hK (by rw [kappaAt, if_neg h0, if_pos h1]) hH hKc hc
      hq).calm
  exact (quiet_tailClause hci hK (by rw [kappaAt, if_neg h0, if_neg h1]) hH hKc hc hq).calm

/-- At a typing system whose reached configurations are closed, two terms run alike when, closed,
they have a common quiet reduct. -/
theorem runsAlike_of_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {t₁ t₂ : Expr}
    (h : closedAt 0 t₁ = true → ∃ t, Quiet (ℍ := ℍ) t₁ t ∧ Quiet (ℍ := ℍ) t₂ t) :
    (ourInst (ℍ := ℍ) RF Ξ J).RunsAlike t₁ t₂ := by
  intro R hR P ε A c K₀ hA hP hreach hterm
  have hlive : (ourInst (ℍ := ℍ) RF Ξ J).Live c.1 := ⟨P, _, R, c.2, hR, hP, hreach⟩
  have hcl := (hL c.1 hlive).1
  have hterm' : c.1.2 = K₀.plug t₁ := hterm
  rw [hterm'] at hcl
  obtain ⟨t, h₁, h₂⟩ := h (closedAt_plug_inv K₀ hcl)
  exact runsAlike_of_quiet h₁ h₂ R hR P ε A c K₀ hA hP hreach hterm

/-- What a closed handler frame around a closed context and an operation gives: the handler a
Core value, its clauses the handler's, the context and the argument closed. -/
theorem closed_handler_parts {n : UInt32} {qs : Val} {r : OVal} {cs : List OVal} {K : Kont}
    {x : Expr} (h : closedAt 0 ((handleK n qs.1 r.1 (cs.map Subtype.val)).plug (K.plug x)) = true) :
    ∃ (hr : IsVal r.1) (hcs : IsVal (clausesE (cs.map Subtype.val))),
      closedAt 0 (hndVal n qs ⟨r.1, hr⟩ ⟨_, hcs⟩).1 = true ∧ closedAt 0 (K.plug .unit) = true ∧
      closedAt 0 x = true := by
  rw [show (handleK n qs.1 r.1 (cs.map Subtype.val)).plug (K.plug x) =
    .app (.app (.prim .hnd) (hndValE n qs.1 r.1 (cs.map Subtype.val))) (K.plug x) from rfl] at h
  simp only [closedAt, Bool.and_eq_true] at h
  obtain ⟨⟨-, hH⟩, hKx⟩ := h
  rw [closedAt_plug_iff] at hKx
  simp only [Bool.and_eq_true] at hKx
  have hH' := hH
  simp only [hndValE, closedAt, Bool.and_eq_true, Bool.true_and] at hH'
  refine ⟨isVal_of_closed_oval r.2 hH'.2.1, isVal_clausesE _ ?_, hH, hKx.1, hKx.2⟩
  intro e he
  obtain ⟨cl, -, rfl⟩ := List.mem_map.1 he
  exact isVal_of_closed_oval cl.2 (closedAt_clausesE _ hH'.2.2 _ he)

/-- **The tail-resumptive law at the answering class.**  At a typing system whose reached
configurations are closed (`LiveOK`), a resuming operation caught by a handler whose clause is
`λ(a, k). c a to b. k.resume b`, with `c` closed and `c v` running quietly to a value, runs as the
code in place: both sides reach `hnd H K[w]` calmly (`calm_tailClause`) — quietly, or, at a linear
or affine operation, around `κ`'s cell, which the resume releases.  No hygiene premise is read:
quiet code performs nothing and allocates nothing. -/
theorem tailLaw_quiet (hL : LiveOK (ℍ := ℍ) RF Ξ J) {l : (RF.alg Ξ).Lab} {r : OVal}
    {cs : List OVal} {K : Kont} {i : ℕ} {v c : OVal} {w : Val} (hi : i < 2 ^ 32)
    (hK : (ourInst (ℍ := ℍ) RF Ξ J).catches K l = false)
    (hci : cs[i]? = some ((ourInst (ℍ := ℍ) RF Ξ J).tailCl c)) (hc : closedAt 0 c.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    (ourInst (ℍ := ℍ) RF Ξ J).RunsAlike
      ((ourInst (ℍ := ℍ) RF Ξ J).handle l ((ourInst (ℍ := ℍ) RF Ξ J).hnd r cs)
        ((ourInst (ℍ := ℍ) RF Ξ J).plug K ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v)))
      ((ourInst (ℍ := ℍ) RF Ξ J).handle l ((ourInst (ℍ := ℍ) RF Ξ J).hnd r cs)
        ((ourInst (ℍ := ℍ) RF Ξ J).plug K
          ((ourInst (ℍ := ℍ) RF Ξ J).app ((ourInst (ℍ := ℍ) RF Ξ J).force c) v))) := by
  refine runsAlike_of_live_calm hL fun hcl => ?_
  have hp := perform_eq (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (l := l) v hi
  change closedAt 0 ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
    (K.plug ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v))) = true at hcl
  rw [hp] at hcl
  obtain ⟨hr, hcs, hH, hKc, hx⟩ :=
    closed_handler_parts (qs := qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) hcl
  have hv : IsVal v.1 := by
    simp only [performE, opArgE, closedAt, Expr.val, Val.prim, Val.i32, Bool.true_and] at hx
    exact isVal_of_closed_oval v.2 hx
  have hi' : (UInt32.ofNat i).toNat = i := UInt32.toNat_ofNat_of_lt' hi
  have hcl' : clauseAt (clausesE (cs.map Subtype.val)) (UInt32.ofNat i).toNat =
      some ⟨tailOf c.1, .lam⟩ := by
    rw [hi']
    refine clauseAt_clausesE _ i .lam ?_
    rw [List.getElem?_map, hci]; rfl
  have hq' : Quiet (ℍ := ℍ) (.app c.1 (⟨v.1, hv⟩ : Val).1) (.val w) := hq
  have hT := calm_tailClause (n := RF.name Ξ l) (hr := ⟨r.1, hr⟩) (hs := ⟨_, hcs⟩)
    (c := ⟨c.1, isVal_of_closed_oval c.2 hc⟩) (v := ⟨v.1, hv⟩) (K := K) hcl' hK hH hKc hc hq'
  refine ⟨hndE (hndVal (RF.name Ξ l) (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) ⟨r.1, hr⟩ ⟨_, hcs⟩)
    (K.plug (.val w)), ?_, ?_⟩
  · show Calm (ℍ := ℍ) ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
      (K.plug ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v))) _
    rw [hp]; exact hT
  · have h₁ := ((quiet_appE (ℍ := ℍ) .hole c.1 ⟨v.1, hv⟩).trans hq').plug
      ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).comp K)
    simp only [Kont.plug_comp] at h₁
    exact h₁.calm

theorem hasHnd_bindK (N : Expr) (n : UInt32) : (bindK N).HasHnd n = false := by
  simp [bindK, Kont.HasHnd]

/-- **Algebraicity at the answering class.**  At a typing system whose reached configurations are
closed, inside a handler whose clause at the operation is `λ(a, k). c a to b. k.resume b`, with
`c` closed and `c v` running quietly to a value, `(op v to x. M) to y. N` and
`op v to x. (M to y. N)` both reach `hnd H K[M[w/x] to y. N]` calmly: each continuation is resumed
once, in place, at the same answer, and at a linear or affine operation each side's resume releases
its `κ`'s cell. -/
theorem algLaw_quiet (hL : LiveOK (ℍ := ℍ) RF Ξ J) {l : (RF.alg Ξ).Lab} {r : OVal}
    {cs : List OVal} {K : Kont} {i : ℕ} {v c : OVal} {w : Val} {M N : Expr} (hi : i < 2 ^ 32)
    (hK : (ourInst (ℍ := ℍ) RF Ξ J).catches K l = false)
    (hci : cs[i]? = some ((ourInst (ℍ := ℍ) RF Ξ J).tailCl c)) (hc : closedAt 0 c.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    (ourInst (ℍ := ℍ) RF Ξ J).RunsAlike
      ((ourInst (ℍ := ℍ) RF Ξ J).handle l ((ourInst (ℍ := ℍ) RF Ξ J).hnd r cs)
        ((ourInst (ℍ := ℍ) RF Ξ J).plug K ((ourInst (ℍ := ℍ) RF Ξ J).bind
          ((ourInst (ℍ := ℍ) RF Ξ J).bind ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) M) N)))
      ((ourInst (ℍ := ℍ) RF Ξ J).handle l ((ourInst (ℍ := ℍ) RF Ξ J).hnd r cs)
        ((ourInst (ℍ := ℍ) RF Ξ J).plug K ((ourInst (ℍ := ℍ) RF Ξ J).bind
          ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) ((ourInst (ℍ := ℍ) RF Ξ J).bind M N)))) := by
  refine runsAlike_of_live_calm hL fun hcl => ?_
  have hp := perform_eq (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (l := l) v hi
  let KL : Kont := (K.comp (bindK N)).comp (bindK M)
  let KR : Kont := K.comp (bindK (bindE M N))
  have eL : ∀ x, K.plug (bindE (bindE x M) N) = KL.plug x := fun x => by
    simp only [KL, Kont.plug_comp]; rfl
  have eR : ∀ x, K.plug (bindE x (bindE M N)) = KR.plug x := fun x => by
    simp only [KR, Kont.plug_comp]; rfl
  change closedAt 0 ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
    (K.plug (bindE (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) M) N))) = true at hcl
  rw [hp, eL] at hcl
  obtain ⟨hr, hcs, hH, hKc, hx⟩ :=
    closed_handler_parts (qs := qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) hcl
  have hv : IsVal v.1 := by
    simp only [performE, opArgE, closedAt, Expr.val, Val.prim, Val.i32, Bool.true_and] at hx
    exact isVal_of_closed_oval v.2 hx
  -- the parts of the contexts, closed
  have hKLc := hKc
  simp only [KL, Kont.plug_comp] at hKLc
  rw [closedAt_plug_iff 0 K] at hKLc
  simp only [bindK, Kont.plug, closedAt, Bool.and_eq_true] at hKLc
  obtain ⟨hK0, hN, hM, -⟩ := hKLc
  have hKRc : closedAt 0 (KR.plug .unit) = true := by
    simp only [KR, Kont.plug_comp]
    rw [closedAt_plug_iff 0 K]
    simp only [bindK, bindE, Kont.plug, closedAt, Expr.val, Val.lam, Bool.and_eq_true]
    exact ⟨hK0, ⟨closedAt_mono _ hN (by omega), hM⟩, trivial⟩
  have hi' : (UInt32.ofNat i).toNat = i := UInt32.toNat_ofNat_of_lt' hi
  have hcl' : clauseAt (clausesE (cs.map Subtype.val)) (UInt32.ofNat i).toNat =
      some ⟨tailOf c.1, .lam⟩ := by
    rw [hi']
    refine clauseAt_clausesE _ i .lam ?_
    rw [List.getElem?_map, hci]; rfl
  have hq' : Quiet (ℍ := ℍ) (.app c.1 (⟨v.1, hv⟩ : Val).1) (.val w) := hq
  have hKL : KL.HasHnd (RF.name Ξ l) = false := by
    simp only [KL, hasHnd_comp, hasHnd_bindK, Bool.or_false]; exact hK
  have hKR : KR.HasHnd (RF.name Ξ l) = false := by
    simp only [KR, hasHnd_comp, hasHnd_bindK, Bool.or_false]; exact hK
  have hTL := calm_tailClause (n := RF.name Ξ l) (hr := ⟨r.1, hr⟩) (hs := ⟨_, hcs⟩)
    (c := ⟨c.1, isVal_of_closed_oval c.2 hc⟩) (v := ⟨v.1, hv⟩) (K := KL) hcl' hKL hH hKc hc hq'
  have hTR := calm_tailClause (n := RF.name Ξ l) (hr := ⟨r.1, hr⟩) (hs := ⟨_, hcs⟩)
    (c := ⟨c.1, isVal_of_closed_oval c.2 hc⟩) (v := ⟨v.1, hv⟩) (K := KR) hcl' hKR hH hKRc hc hq'
  -- after the resume: `M[w/x] to y. N` on both sides
  let H : Val := hndVal (RF.name Ξ l) (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) ⟨r.1, hr⟩ ⟨_, hcs⟩
  have hβL := quiet_beta (ℍ := ℍ) ((Kont.appR (.app (.prim .hnd) H.1) .hole).comp
    (K.comp (bindK N))) M w
  have hβR := quiet_beta (ℍ := ℍ) ((Kont.appR (.app (.prim .hnd) H.1) .hole).comp K)
    (bindE M N) w
  have eN : (bindE M N).subst 0 w = bindE (M.subst 0 w) N := by
    simp only [bindE, Expr.subst, Expr.val, Val.lam]
    rw [subst_closedAt N _ hN (le_refl _)]
  rw [eN] at hβR
  refine ⟨hndE H (K.plug (bindE (M.subst 0 w) N)), ?_, ?_⟩
  · show Calm (ℍ := ℍ) ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
      (K.plug (bindE (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) M) N))) _
    rw [hp, eL]
    refine hTL.trans ?_
    simp only [Kont.plug_comp] at hβL
    rw [← eL]
    exact hβL.calm
  · show Calm (ℍ := ℍ) ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
      (K.plug (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) (bindE M N)))) _
    rw [hp, eR]
    refine hTR.trans ?_
    simp only [Kont.plug_comp] at hβR
    rw [← eR]
    exact hβR.calm

end Answering

/-- **Algebraicity observing a finaliser's code fails at `J₁` at an admissible effect context**,
`J₁`'s inner rows tied to it.  Kept as a record. -/
theorem not_algLawCode_ΞA :
    AdmEff ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF ΞA J₁).AlgLawCode :=
  ⟨admEff_ΞA, not_algLawCode_J₁ ΞA rfl rfl⟩

end Targets.Inst

end
