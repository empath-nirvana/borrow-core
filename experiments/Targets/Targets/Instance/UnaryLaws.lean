import Targets.Instance.Runs

/-!
# The Instance — the unary laws (`A.UnaryLaws`, restated by D4) at our instance

**Algebraicity fails as written at `J₁`** (`not_algLaw_J₁`, at the admissible context `ΞA`:
`not_algLaw_ΞA`).  D4 compares the two sides at a program's data answers; the trace still compares
each finaliser event `fire D` by the finaliser's code.  The witness `algFireProg`, typed by Core's
kernel:

* a handler of `5` is typed at an `unr` operation (`Eu`), so its clause's continuation `κ` is
  persistent, and the clause holds `κ` in a finaliser frame (`λ_. (λz. ()) κ`) while it raises
  `exn` to a handler outside (`holdRaiseCl`);
* the two sides of the law, `(tick () to x. ret x) to y. ret ()` and
  `tick () to x. (ret x to y. ret ())`, are caught by that handler with the continuations
  `□ to x. ret x` then `□ to y. ret ()` (left) and `□ to x. (ret x to y. ret ())` (right);
* the raise fires the finaliser, and the two runs show `fire ((λz. ()) κ₁)` and
  `fire ((λz. ()) κ₂)`, which differ as terms (`finE_DL_ne`), at the same data answer `()`.

What the witness reads: an inner handler at a resuming `unr` operation (multi-shot, decision 63;
`J₁`'s inner judgements are not tied to the effect context, TIER1-PLAN "Readings to confirm" 1), a
finaliser at `F 1` that holds that operation's persistent continuation, and the trace's `fire D`
carrying `D`'s code.  At a linear or affine continuation no finaliser at `F 1` can hold it: its
two branches are at the handler's outer row, and a frame inside a clause is unwound only by an
operation of that row.  Two repairs, the user's: observe a finaliser's start without its code
(D4's "observationally" read at the trace's events), or restrict `unr` (decision 63: "On friction,
restrict or remove the unr qualifier").  With `unr` restricted the law is not proved here: a proof
reads, at every reached finaliser frame, that the finaliser holds no captured continuation, which
is a run-time typing of configurations (route 8.2).

**The laws at the answering class** (`quiet_tailClause`): a tail-resumptive clause
`λ(a, k). c a to b. k.resume b` whose code `c v` runs quietly to a value resumes `K` in place, so
the tail-resumptive law (`tailLaw_quiet`) and algebraicity inside such a handler (`algLaw_quiet`)
hold at every configuration a typed program reaches, by a join (`runsAlike_of_quiet`).  `[Core
σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE hndVal kappa
  clauseAt)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg HeadChain lookRun lookEnd lookRun_sound closedAt_kappa
  closedAt_plug_iff kont_shift_closed)

/-! ### Algebraicity's witness: a finaliser holding a persistent continuation -/

/-- `λ(a, k). raise (1, 0, ()) then y. () unwind ((λz. ()) k)`: a clause that raises `exn` inside
a finaliser frame whose finaliser holds `k`. -/
def holdRaiseCl : Expr :=
  .val (.lam (.letpair (.var 0)
    (thenE (.val .unit) (bindE (.var 1) (.val .unit)) (raiseE (opArgE 1 0 (.val .unit))))))

/-- Algebraicity's left side at the name `5`: `(tick () to x. ret x) to y. ret ()`. -/
def algL5 : Expr := bindE (bindE (performE (opArgE 5 0 (.val .unit))) (.var 0)) (.val .unit)

/-- Its right side: `tick () to x. (ret x to y. ret ())`. -/
def algR5 : Expr := bindE (performE (opArgE 5 0 (.val .unit))) (bindE (.var 0) (.val .unit))

/-- **The witness**: `handle_1 (handle_5 algL5 with holdRaiseCl) with (λ_. ())`. -/
def algFireProg : Expr := withH 1 abortCl (withH 5 holdRaiseCl algL5)

/-- `exn : 1 ↠ 0` at the name `1`, the handler of `5`'s outer row. -/
abbrev Sx : Row := Row.ofEff 1 Eab 0 ++ []

/-- An `unr` operation `1 ↠ 1`: the handler of `5` reads `5`'s operation so. -/
abbrev Eu : List (Qual × VTy × VTy) := [(.unr, .unit, .unit)]

abbrev R5 : Row := Row.ofEff 5 Eu 0 ++ Sx

theorem rowLe_nil (S : Row) : RowLe [] S := fun _ _ _ h => by simp [Row.find] at h

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
    CDerives Δ Γ (withH n cl e) (.comp (CTy.effOf S A)) := by
  refine .bind (deadSplit hΓ) (.ret (.tensorI (deadSplit hΓ) hcl (.unitI hΓ.toP))) ?_
  refine .bind (A := retTy S A A) (.right (deadSplit hΓ)) (.ret ?_) ?_
  · exact .bangThunkV (dead_noLive (Ctx.Dead.cons hΓ)) rfl
      (.lam (.effSub (S := []) (rowLe_nil _) (.ret (.var (.here (Ctx.Dead.cons hΓ).toP)))))
  exact .effHandle (E := [(q, B, C)]) (.left (.left (deadSplit hΓ)))
    (.left (.right (deadSplit hΓ))) (.here (Ctx.Dead.cons hΓ).toP) (.there (.here hΓ.toP)) hn0
    hnS (by simp) he

/-- **The witness is typed by Core's kernel**, at `F 1`. -/
theorem d_algFireProg : CDerives LifeCtx.empty [] algFireProg (.comp (.ret .unit)) := by
  refine d_withH (S := []) (by decide) (by simp) .nil (d_abortClNU nu_nil .nil).toCDerives ?_
  exact d_withH (S := Sx) (by decide) (by simp [Row.ofEff]) (by cdead) (d_holdRaiseCl (by cdead))
    (d_algL5 (by cdead))

/-! ### The witness's runs -/

/-- The two handler frames, after the program's bindings. -/
def algK₀ : Kont :=
  (handleK 1 (.lam (.var 0)) [abortCl]).comp (handleK 5 (.lam (.var 0)) [holdRaiseCl])

theorem alg_c : lookEnd 4 algFireProg = algK₀.plug algL5 := by rfl

def H5E : Expr := hndValE 5 (.lam (.var 0)) [holdRaiseCl]

theorem isVal_H5E : IsVal H5E := .pair .prim (.pair .lam (.pair .lam .unit))

/-- What lies between the handler of `5` and the operation, on each side. -/
def KL5 : Kont := .appR (.lam .unit) (.appR (.lam (.var 0)) .hole)

def KR5 : Kont := .appR (.lam (.app (.lam .unit) (.var 0))) .hole

/-- The finaliser each side's frame holds: `λ_. (λz. ()) κ`, `κ` the side's continuation. -/
def DL5 : Val := Val.lam (bindE (kappa 5 ⟨H5E, isVal_H5E⟩ KL5) (.val .unit))

def DR5 : Val := Val.lam (bindE (kappa 5 ⟨H5E, isVal_H5E⟩ KR5) (.val .unit))

def raise1 : Expr := raiseE (opArgE 1 0 (.val .unit))

def K1₀ : Kont := handleK 1 (.lam (.var 0)) [abortCl]

/-- Each side's run, split at its one finaliser step. -/
theorem algL_q : lookRun 9 (algK₀.plug algL5) =
    (lookRun 9 (algK₀.plug algL5)).take 3 ++
      (K1₀, ubindE (Val.pair (Val.lam (.val .unit)) DL5) raise1,
        .seq (.app (.val DL5) (.val .unit)) raise1) :: (lookRun 9 (algK₀.plug algL5)).drop 4 := by
  rfl

theorem algR_q : lookRun 9 (algK₀.plug algR5) =
    (lookRun 9 (algK₀.plug algR5)).take 3 ++
      (K1₀, ubindE (Val.pair (Val.lam (.val .unit)) DR5) raise1,
        .seq (.app (.val DR5) (.val .unit)) raise1) :: (lookRun 9 (algK₀.plug algR5)).drop 4 := by
  rfl

theorem algL_end : lookEnd 9 (algK₀.plug algL5) = .unit := by rfl

theorem algR_end : lookEnd 9 (algK₀.plug algR5) = .unit := by rfl

theorem algL_chain : HeadChain (ℍ := ℍ) (algK₀.plug algL5) (lookRun 9 (algK₀.plug algL5)) .unit := by
  have := lookRun_sound (ℍ := ℍ) 9 (algK₀.plug algL5)
  rwa [algL_end] at this

theorem algR_chain : HeadChain (ℍ := ℍ) (algK₀.plug algR5) (lookRun 9 (algK₀.plug algR5)) .unit := by
  have := lookRun_sound (ℍ := ℍ) 9 (algK₀.plug algR5)
  rwa [algR_end] at this

/-- What tells the two finalisers apart: the right side's frame `□ to x. (ret x to y. ret ())`,
which the left side's continuation does not hold. -/
def algPat5 : Expr → Bool
  | .lam (.app (.lam .unit) (.var 0)) => true
  | _ => false

theorem finE_DL_pat : occursIn algPat5 (finE DL5.1) = false := by decide

theorem finE_DR_pat : occursIn algPat5 (finE DR5.1) = true := by decide

/-- **The two finalisers differ as terms.** -/
theorem finE_DL_ne : finE DL5.1 ≠ finE DR5.1 := fun h => by
  have := finE_DL_pat; rw [h, finE_DR_pat] at this; cases this

theorem not_isVal_raise1 : ¬ IsVal raise1 := fun h =>
  plug_raise_ne_val .hole (Val.pair (Val.i32 1) (Val.pair (Val.i32 0) Val.unit)) ⟨_, h⟩ rfl

section AlgW
variable (Ξ : EffCtx)

/-- The label of the name `5`, where `Ξ` declares `tick : 1 ↠ 1` there. -/
def lab5 (h5 : Ξ 5 = [(.lin, .unit, .unit)]) : (orowAlg Ξ).Lab :=
  ⟨5, by decide, by rw [h5]; simp, by rw [h5]; simp⟩

theorem obs_algL (μ : Heap) (s : (ourInst (ℍ := ℍ) orowRF Ξ J₁).R₀.St) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).obs (chainPath (ourInst (ℍ := ℍ) orowRF Ξ J₁).R₀ μ s
      (lookRun 9 (algK₀.plug algL5))) = [.fire (finE DL5.1)] := by
  rw [algL_q, obs_chainPath_one _ _ _ _ _ _ (by decide) (by decide)]
  simp only
  rw [labelOf_fire not_isVal_raise1]
  rfl

theorem obs_algR (μ : Heap) (s : (ourInst (ℍ := ℍ) orowRF Ξ J₁).R₀.St) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).obs (chainPath (ourInst (ℍ := ℍ) orowRF Ξ J₁).R₀ μ s
      (lookRun 9 (algK₀.plug algR5))) = [.fire (finE DR5.1)] := by
  rw [algR_q, obs_chainPath_one _ _ _ _ _ _ (by decide) (by decide)]
  simp only
  rw [labelOf_fire not_isVal_raise1]
  rfl

/-- **Algebraicity, as restated by D4, fails at `J₁`.**  `algFireProg`, typed by Core's kernel at
`F 1`, reaches the law's left side under its two handlers; the complete runs from there and from
the right side answer `()`, and show `fire ((λz. ()) κ₁)` and `fire ((λz. ()) κ₂)`: the finaliser
the handler of `5` holds mentions the continuation it caught, which the two sides frame
differently. -/
theorem not_algLaw_J₁ (h5 : Ξ 5 = [(.lin, .unit, .unit)]) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ J₁).AlgLaw := by
  intro hA
  let S := ourInst (ℍ := ℍ) orowRF Ξ J₁
  have hRA := hA (lab5 Ξ h5) 0 S.unitV ⟨OVTy.ofV .unit, OVTy.ofV .unit, .linear⟩ (.var 0)
    (.val .unit) (by show ((Ξ 5).map _)[0]? = _; rw [h5]; rfl) (by intro h; cases h)
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ algFireProg)
      ((Adequacy.emptyMem, lookEnd 4 algFireProg), ()) :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 4 algFireProg)
  have hder : S.der [] algFireProg (S.F (orowAlg Ξ).unit (OVTy.ofV .unit)) :=
    der_J₁_ret (by decide) d_algFireProg
  have hL := obsFrom_of_chain (J := J₁) S.R₀ (μ := Adequacy.emptyMem) (s := ()) algL_chain .unit
  erw [obs_algL] at hL
  have h := (hRA S.R₀ r₀_respects algFireProg _ (OVTy.ofV .unit)
    ((Adequacy.emptyMem, lookEnd 4 algFireProg), ()) algK₀ .unit hder hreach alg_c _ _).mp
    (by rw [alg_c]; exact hL)
  have htr := obsFrom_chain_trace (J := J₁) S.R₀ algR_chain .unit h
  erw [obs_algR] at htr
  have := List.cons.inj htr
  injection this.1 with h'
  exact finE_DL_ne h'

end AlgW


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

/-- **A tail-resumptive clause whose code runs quietly resumes in place**: `hnd H K[op (n, i, v)]`
reaches `hnd H K[w]` quietly when the clause of `i` is `λ(a, k). c a to b. k.resume b` and `c v`
runs quietly to `w`.  The steps: the catch, the clause's β-step and `letpair`, the code, the bind,
`resume`'s β-step, and `κ`'s four (`quiet_kappa_resume`). -/
theorem quiet_tailClause {n i : UInt32} {hr hs c v w : Val} {K : Kont}
    (hci : clauseAt hs.1 i.toNat = some ⟨tailOf c.1, .lam⟩) (hK : K.HasHnd n = false)
    (hH : closedAt 0 (hndVal n hr hs).1 = true) (hKc : closedAt 0 (K.plug .unit) = true)
    (hc : closedAt 0 c.1 = true) (hq : Quiet (ℍ := ℍ) (.app c.1 v.1) (.val w)) :
    Quiet (ℍ := ℍ) (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v)))))
      (hndE (hndVal n hr hs) (K.plug (.val w))) := by
  have hκ : closedAt 0 (kappa n (hndVal n hr hs) K) = true := closedAt_kappa n hH hKc
  let κV : Val := ⟨kappa n (hndVal n hr hs) K, isVal_kappa n _ K⟩
  have h₁ := quiet_hop (ℍ := ℍ) .hole n i hr hs ⟨tailOf c.1, .lam⟩ v K hci hK
  simp only [Kont.plug] at h₁
  refine h₁.trans ?_
  have h₂ := quiet_beta (ℍ := ℍ) .hole (.letpair (.var 0) (tailBody c.1)) (Val.pair v κV)
  simp only [Kont.plug, Expr.subst, if_pos, tailBody_subst2 hc] at h₂
  refine h₂.trans ?_
  have h₃ := quiet_letpair (ℍ := ℍ) .hole v κV (tailBody c.1)
  simp only [Kont.plug] at h₃
  rw [tailBody_letpair hc hκ (isVal_kappa n _ K) v] at h₃
  refine h₃.trans ?_
  have h₄ := ((quiet_appE (ℍ := ℍ) .hole c.1 v).trans hq).plug
    (bindK (resumeE (kappa n (hndVal n hr hs) K) (.var 0)))
  simp only [Kont.plug] at h₄
  refine h₄.trans ?_
  have h₅ := quiet_beta (ℍ := ℍ) .hole (resumeE (kappa n (hndVal n hr hs) K) (.var 0)) w
  simp only [Kont.plug] at h₅
  rw [resume0_subst hκ w] at h₅
  refine h₅.trans ?_
  have h₆ := quiet_resumeE (ℍ := ℍ) .hole (kappa n (hndVal n hr hs) K) w
  simp only [Kont.plug] at h₆
  refine h₆.trans ?_
  have h₇ := quiet_kappa_resume (ℍ := ℍ) .hole n (hndVal n hr hs) K w
  simpa [Kont.plug] using h₇

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
theorem closed_handler_parts {n : UInt32} {r : OVal} {cs : List OVal} {K : Kont} {x : Expr}
    (h : closedAt 0 ((handleK n r.1 (cs.map Subtype.val)).plug (K.plug x)) = true) :
    ∃ (hr : IsVal r.1) (hcs : IsVal (clausesE (cs.map Subtype.val))),
      closedAt 0 (hndVal n ⟨r.1, hr⟩ ⟨_, hcs⟩).1 = true ∧ closedAt 0 (K.plug .unit) = true ∧
      closedAt 0 x = true := by
  rw [show (handleK n r.1 (cs.map Subtype.val)).plug (K.plug x) =
    .app (.app (.prim .hnd) (hndValE n r.1 (cs.map Subtype.val))) (K.plug x) from rfl] at h
  simp only [closedAt, Bool.and_eq_true] at h
  obtain ⟨⟨-, hH⟩, hKx⟩ := h
  rw [closedAt_plug_iff] at hKx
  simp only [Bool.and_eq_true] at hKx
  have hH' := hH
  simp only [hndValE, closedAt, Bool.and_eq_true, Bool.true_and] at hH'
  refine ⟨isVal_of_closed_oval r.2 hH'.1, isVal_clausesE _ ?_, hH, hKx.1, hKx.2⟩
  intro e he
  obtain ⟨cl, -, rfl⟩ := List.mem_map.1 he
  exact isVal_of_closed_oval cl.2 (closedAt_clausesE _ hH'.2 _ he)

/-- **The tail-resumptive law at the answering class.**  At a typing system whose reached
configurations are closed (`LiveOK`), a resuming operation caught by a handler whose clause is
`λ(a, k). c a to b. k.resume b`, with `c` closed and `c v` running quietly to a value, runs as the
code in place: both sides reach `hnd H K[w]` quietly.  No hygiene premise is read: quiet code
performs nothing and allocates nothing. -/
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
  refine runsAlike_of_live hL fun hcl => ?_
  have hp := perform_eq (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (l := l) v hi
  change closedAt 0 ((handleK (RF.name Ξ l) r.1 (cs.map Subtype.val)).plug
    (K.plug ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v))) = true at hcl
  rw [hp] at hcl
  obtain ⟨hr, hcs, hH, hKc, hx⟩ := closed_handler_parts hcl
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
  have hT := quiet_tailClause (n := RF.name Ξ l) (hr := ⟨r.1, hr⟩) (hs := ⟨_, hcs⟩)
    (c := ⟨c.1, isVal_of_closed_oval c.2 hc⟩) (v := ⟨v.1, hv⟩) (K := K) hcl' hK hH hKc hc hq'
  refine ⟨hndE (hndVal (RF.name Ξ l) ⟨r.1, hr⟩ ⟨_, hcs⟩) (K.plug (.val w)), ?_, ?_⟩
  · show Quiet (ℍ := ℍ) ((handleK (RF.name Ξ l) r.1 (cs.map Subtype.val)).plug
      (K.plug ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v))) _
    rw [hp]; exact hT
  · have h₁ := ((quiet_appE (ℍ := ℍ) .hole c.1 ⟨v.1, hv⟩).trans hq').plug
      ((handleK (RF.name Ξ l) r.1 (cs.map Subtype.val)).comp K)
    simp only [Kont.plug_comp] at h₁
    exact h₁

theorem hasHnd_bindK (N : Expr) (n : UInt32) : (bindK N).HasHnd n = false := by
  simp [bindK, Kont.HasHnd]

/-- **Algebraicity at the answering class.**  At a typing system whose reached configurations are
closed, inside a handler whose clause at the operation is `λ(a, k). c a to b. k.resume b`, with
`c` closed and `c v` running quietly to a value, `(op v to x. M) to y. N` and
`op v to x. (M to y. N)` both reach `hnd H K[M[w/x] to y. N]` quietly: each continuation is resumed
once, in place, at the same answer. -/
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
  refine runsAlike_of_live hL fun hcl => ?_
  have hp := perform_eq (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (l := l) v hi
  let KL : Kont := (K.comp (bindK N)).comp (bindK M)
  let KR : Kont := K.comp (bindK (bindE M N))
  have eL : ∀ x, K.plug (bindE (bindE x M) N) = KL.plug x := fun x => by
    simp only [KL, Kont.plug_comp]; rfl
  have eR : ∀ x, K.plug (bindE x (bindE M N)) = KR.plug x := fun x => by
    simp only [KR, Kont.plug_comp]; rfl
  change closedAt 0 ((handleK (RF.name Ξ l) r.1 (cs.map Subtype.val)).plug
    (K.plug (bindE (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) M) N))) = true at hcl
  rw [hp, eL] at hcl
  obtain ⟨hr, hcs, hH, hKc, hx⟩ := closed_handler_parts hcl
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
  have hTL := quiet_tailClause (n := RF.name Ξ l) (hr := ⟨r.1, hr⟩) (hs := ⟨_, hcs⟩)
    (c := ⟨c.1, isVal_of_closed_oval c.2 hc⟩) (v := ⟨v.1, hv⟩) (K := KL) hcl' hKL hH hKc hc hq'
  have hTR := quiet_tailClause (n := RF.name Ξ l) (hr := ⟨r.1, hr⟩) (hs := ⟨_, hcs⟩)
    (c := ⟨c.1, isVal_of_closed_oval c.2 hc⟩) (v := ⟨v.1, hv⟩) (K := KR) hcl' hKR hH hKRc hc hq'
  -- after the resume: `M[w/x] to y. N` on both sides
  let H : Val := hndVal (RF.name Ξ l) ⟨r.1, hr⟩ ⟨_, hcs⟩
  have hβL := quiet_beta (ℍ := ℍ) ((Kont.appR (.app (.prim .hnd) H.1) .hole).comp
    (K.comp (bindK N))) M w
  have hβR := quiet_beta (ℍ := ℍ) ((Kont.appR (.app (.prim .hnd) H.1) .hole).comp K)
    (bindE M N) w
  have eN : (bindE M N).subst 0 w = bindE (M.subst 0 w) N := by
    simp only [bindE, Expr.subst, Expr.val, Val.lam]
    rw [subst_closedAt N _ hN (le_refl _)]
  rw [eN] at hβR
  refine ⟨hndE H (K.plug (bindE (M.subst 0 w) N)), ?_, ?_⟩
  · show Quiet (ℍ := ℍ) ((handleK (RF.name Ξ l) r.1 (cs.map Subtype.val)).plug
      (K.plug (bindE (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) M) N))) _
    rw [hp, eL]
    refine hTL.trans ?_
    simp only [Kont.plug_comp] at hβL
    rw [← eL]
    exact hβL
  · show Quiet (ℍ := ℍ) ((handleK (RF.name Ξ l) r.1 (cs.map Subtype.val)).plug
      (K.plug (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) (bindE M N)))) _
    rw [hp, eR]
    refine hTR.trans ?_
    simp only [Kont.plug_comp] at hβR
    rw [← eR]
    exact hβR

end Answering

/-- **Algebraicity fails at `J₁` at an admissible effect context.** -/
theorem not_algLaw_ΞA :
    AdmEff ΞA ∧ ¬ (ourInst (ℍ := ℍ) orowRF ΞA J₁).AlgLaw :=
  ⟨admEff_ΞA, not_algLaw_J₁ ΞA (by simp [ΞA])⟩

end Targets.Inst

end
