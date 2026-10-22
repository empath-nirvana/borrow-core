import Core.EffExamples
import Core.RecordPrograms
import Core.Dtor
import Core.DelayPrograms

/-!
# Core — the acceptance programs of effects in the kernel  `[spec §19]`

§19's six primary programs, each a closed `CDerives` derivation. Every run of each, under every
allocator, is safe and ends at the empty memory (`adequacyD`, `adequacyD_obs`); where the answer
type has one value, that value is what every run reaches.

| program | shows |
|---|---|
| `logOutside`, `failOutside` | (1) `Log` (answering) and `Fail` (abortive) in both orders: the log state kept beside the error, or finalised by the unwind |
| `nLogOutside`, `nFailOutside` | (1) again with `log` a native affine operation: rows, forwarding, a clause resuming `κ` |
| `logInBorrow` | (2) logging inside `borrow mut b`, the `Log` handler (a borrow of its state) outside |
| `reborrowRaise` | (3) `raise` inside a reborrow inside `borrow mut r`, `Fail` outside: both lends end, the buffer is freed, the error delivered |
| `tickProg n` | (4) `loop { log("tick") }`: `Loop_{Log} 0 1`, `n` observations each under `with_log`, then `close` |
| `takeProg n` | (5) `take n` cancels a producer holding a cell; the producer's finaliser frees it |
| `storeCancel` | (6) a handler stores `κ` in a cell, then cancels it; the captured cell is freed |
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE hndE hndVal opPayload kappa clauseAt
  ubindE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2)

/-! ### Adequacy at a persistent answer -/

/-- **Every run of a closed computation of a persistent type `A` continues to a value of `A` at
the empty memory**: `adequacyD` at data answers.  `[spec §13, §19]` -/
theorem adequacyD_obs {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem e μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧ ∃ ls, vP A ls LSub.empty v PMap.empty := by
  have hwp := fundamentalC h LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have he : substAll [] e = e := Adequacy.psub_nil 0 e
  rw [he] at hwp
  have hwp' : wpTS [] e (fun _ v => Fig16.BoLo.pure (∃ ls, vP A ls LSub.empty v PMap.empty))
      (PMap.empty : BoCa.Fig16.BoLo.WRes) :=
    wpTS_mono (fun ls v ρ hv => by
      have hρ := vP_empty_of_persistent hA hv
      subst hρ
      exact ⟨rfl, ls, hv⟩) _ hwp
  exact theorem32D e _ hwp' hs

/-- **Leak freedom at a persistent answer**: a run of a closed computation of a persistent type `A`
from the empty memory that reaches a value reaches it at the empty memory, and the value is in
`A`'s relation.  The memory holds every cell the run allocates, a continuation's capture cell
(§25) among them, so none is left at the end.  `adequacyD_val` at persistent answers.
`[spec §13, §19, §25]` -/
theorem leakFree_closed {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ₁ : Heap} {w : Val} (hs : Steps Adequacy.emptyMem e μ₁ (.val w)) :
    μ₁ = Adequacy.emptyMem ∧ ∃ ls, vP A ls LSub.empty w PMap.empty := by
  obtain ⟨v, hsteps, hv⟩ := adequacyD_obs hA h hs
  obtain ⟨h₁, rfl⟩ := steps_from_val hsteps
  exact ⟨h₁.symm, hv⟩

/-- A value of `0 ⊕ 1` is `inj₂ ()`. -/
theorem vP_zero_sum {ls : List SRec} {δ : LSub} {v : Val} {ρ : BoCa.Fig16.BoLo.WRes}
    (h : vP (.sum .zero .unit) ls δ v ρ) : v = Val.inj₂ Val.unit := by
  rcases h with ⟨w, h⟩ | ⟨w, h⟩
  · exact (pure_sep_iff.mp h).2.elim
  · obtain ⟨rfl, -, rfl⟩ := pure_sep_iff.mp h
    rfl

/-! ### The effect `Fail` and its handler -/

/-- `1 ⊕ 1`. -/
abbrev Flag : VTy := .sum .unit .unit

/-- `raise : 1 ↠^aff 0`, the operation `0` of the name `1`. -/
def failSig : OpSig := ⟨1, 0, .zero, .top, .unit, .zero, .ret .unit⟩

/-- The row `{Fail}`. -/
abbrev Sf : Row := [failSig]

/-- `Fail`'s operations. -/
abbrev Ef : List (Count × VTy × VTy) := [(.zero, .unit, .zero)]

theorem ofEff_Ef : Row.ofEff 1 Ef 0 ++ [] = Sf := rfl

/-- `raise ()`. -/
def raiseU : Expr := raiseE (opArgE 1 0 (.val .unit))

theorem d_raiseU {Δ : LifeCtx} {Γ : Ctx VTy} {B : VTy} {S : Row}
    (hf : Row.find S 1 0 = some failSig) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ raiseU (.comp (CTy.effOf S B)) :=
  .effRaise (o := failSig) hf rfl .unit (.unitI hΓ)

theorem Sf_unwind (x : LifeVar) : Sf.Unwind x := by
  intro o ho
  simp only [Sf, List.mem_singleton] at ho
  subst ho
  exact ⟨rfl, by decide, by simp [failSig, VFree], fun _ _ => .unit⟩

theorem Sf_not_unr : ¬ Sf.Unr := by
  rintro ⟨o, ho, h⟩
  simp only [Sf, List.mem_singleton] at ho
  subst ho
  cases h

/-- `to_result`'s answer clause `λx. inj₁ x`. -/
def hrR : Expr := .val (.lam (.inj₁ (.var 0)))

/-- `to_result`'s clauses: `raise`'s clause `λe. inj₂ e`. -/
def clsR : Expr := .pair (.val (.lam (.inj₂ (.var 0)))) (.val .unit)

/-- `handle_1 e with to_result`. -/
def toResult (e : Expr) : Expr := bindE clsR (bindE hrR (hndTerm 1 [.zero] 0 1 e))

theorem d_hrR {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ hrR (.val (retTy S A (.sum A .unit))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.sumI₁ (.var (.here hΓ.toP))))))

theorem d_clsR {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clsR (.val (clausesTy S (.sum A .unit) Ef)) :=
  .tensorI (deadSplit hΓ)
    (.bangThunkV (dead_noLive hΓ) rfl
      (.lam (.effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
        (.ret (.sumI₂ (.var (.here hΓ.toP)))))))
    (.unitI hΓ.toP)

/-- **`to_result`** in a context: `handle_1 e with (λx. inj₁ x, λe. inj₂ e) : F_Σ (A ⊕ 1)` for
`e : F_{Fail, Σ} A`. -/
theorem d_toResultG {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {e : Expr}
    (hS : ∀ o ∈ S, o.n ≠ 1) (hSd : Row.divB S = false)
    (he : CDerives Δ (⟨retTy S A (.sum A .unit), false⟩ :: ⟨clausesTy S (.sum A .unit) Ef, false⟩ :: Γ)
      e (.comp (CTy.effOf (Row.ofEff 1 Ef 0 ++ S) A))) :
    CDerives Δ Γ (toResult e) (.comp (CTy.effOf S (.sum A .unit))) := by
  refine .bind (split_kill Γ).toP (.ret (d_clsR (S := S) (A := A) (kill_dead Γ))) ?_
  refine .bind (.right (split_kill Γ).toP) (.ret (d_hrR (S := S) (A := A) (.cons (kill_dead Γ)))) ?_
  exact .effHandle (E := Ef) (.left (.left (split_kill Γ).toP))
    (.left (.right (deadSplit (kill_dead Γ)))) (.here (.cons (kill_dead Γ).toP))
    (.there (.here (kill_dead Γ).toP)) (by decide) hS (by simp)
    (by rw [Row.divB_ofEff_eq (by decide)]; exact hSd) he

/-- `to_result` at a closed computation. -/
theorem d_toResult {Δ : LifeCtx} {S : Row} {A : VTy} {e : Expr} (hS : ∀ o ∈ S, o.n ≠ 1)
    (hSd : Row.divB S = false)
    (he : CDerives Δ [⟨retTy S A (.sum A .unit), false⟩, ⟨clausesTy S (.sum A .unit) Ef, false⟩] e
      (.comp (CTy.effOf (Row.ofEff 1 Ef 0 ++ S) A))) :
    CDerives Δ [] (toResult e) (.comp (CTy.effOf S (.sum A .unit))) :=
  d_toResultG (Γ := []) hS hSd he

/-! ### Callbacks of the unwinding borrows -/

/-- An unwinding callback `thunk Λ. λx. body` at a fresh `'x ⊏ ⊓Δ`. -/
theorem callbackUW {Δ : LifeCtx} {Γ : Ctx VTy} {body : Expr} {x : LifeVar} {L B : VTy} {S : Row}
    (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ)
    (h : CDerives (Δ.extend x Δ.meetOfDom) (⟨L, true⟩ :: ⟨.unit, false⟩ :: Γ) body
      (.comp (CTy.effOf S (.box (.var x) B)))) :
    CDerives Δ Γ (.val (.lam (.val (.lam body)))) (.val (cbUTy x Δ.meetOfDom L B S)) :=
  .thunkV rfl (allI_fresh hΔ hx hΓ (.lam h))

theorem Ctx.Dead.drops {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Γ.Drops :=
  fun s hs hl => dead_noLive (P := fun s => s.ty.Drop) h s hs hl

/-! ### Program 1: `Log` and `Fail` in both nesting orders

`Log` is answering: its state is a cell `r : Ref Flag` (`inj₁ ()` until something is logged), its
handler a borrow of `r`, and `log m` a call on the capability `m : Mut 'x Flag` that writes
`inj₂ ()` (`withswap m set`). `Fail` is abortive: `raise : 1 ↠^aff 0`, handled by `to_result`.
The function body logs and raises:

    logRaise m = let (m, u) = withswap m set; u; forget m; raise ()

* **`Log` outside** (`logOutside`): `to_result` runs inside the borrow of `r` and catches the
  raise there; the borrow returns, and the program answers the log state beside the error,
  `(free r, inj₂ ())`. The logs are kept.
* **`Fail` outside** (`failOutside`): the raise crosses the borrow of `r`, by its unwinding
  form. The lend ends and `r`'s destructor frees the cell; `to_result` answers `inj₂ ()`, and the
  log state is gone. The logs are lost.

`logRaise`'s answer type is `0`, so in both orders the error is the only answer the types allow,
and every run delivers it at the empty memory (`logOutside_answers`, `failOutside_answers`). -/

/-- `log m; raise ()`, `m` at index `k`. -/
def logRaise (k : Nat) : Expr :=
  .letpair (app2 withswap (.var k) setG) (.seq (.var 0) (.seq (.app forget (.var 1)) raiseU))

/-- `logRaise 0` in a callback's context. -/
theorem d_logRaise0 {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {B : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.mut a Flag, true⟩ :: ⟨.unit, false⟩ :: Γ) (logRaise 0)
      (.comp (CTy.effOf Sf B)) := by
  refine .tensorE (.left (.dead (deadSplit hΓ)))
    (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine .unitE (.left (.right (.dead (.dead (deadSplit hΓ))))) (.var (by csolo)) ?_
  refine .unitE (.dead (.left (.dead (.dead (deadSplit hΓ)))))
    (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact d_raiseU rfl (by cdead)

/-- `logRaise 2` under `to_result`'s two bindings, in a callback's context. -/
theorem d_logRaise2 {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {B T₁ T₂ : VTy}
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨T₁, false⟩ :: ⟨T₂, false⟩ :: ⟨.mut a Flag, true⟩ :: ⟨.unit, false⟩ :: Γ)
      (logRaise 2) (.comp (CTy.effOf Sf B)) := by
  refine .tensorE (.dead (.dead (.left (.dead (deadSplit hΓ)))))
    (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine .unitE (.left (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
    (.var (by csolo)) ?_
  refine .unitE (.dead (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
    (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact d_raiseU rfl (by cdead)

/-! #### `Log` outside -/

/-- `Λ. λm. to_result (logRaise m) to res. res`. -/
def logInCb : Expr := .val (.lam (.val (.lam (bindE (toResult (logRaise 2)) (.var 0)))))

/-- A context whose only live slot is its head, of a data type, outlives every lifetime it
defines. -/
theorem outlives_head {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (ha : Δ.Defines a) (hA : VOutlives Δ a A) (hΓ : Ctx.Dead Γ) :
    CtxOutlives Δ (⟨A, true⟩ :: Γ) a := by
  refine ⟨ha, fun s hs hl => ?_⟩
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact hA
  · exact dead_noLive (P := fun s => VOutlives Δ a s.ty) hΓ s hs' hl

/-- **Program 1, `Log` outside `Fail`**:
`r ← alloc (inj₁ ()); let (r, res) = withbor r logInCb in (free r, res)`. -/
def logOutside : Expr :=
  bindE (.app alloc' (.inj₁ unit')) (.letpair (app2 withbor (.var 0) logInCb)
    (.pair (.app free' (.var 1)) (.var 0)))

theorem d_logInCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ logInCb (.val (.all 0 LifeCtx.empty.meetOfDom
      (.lolli (.mut (.var 0) Flag) (.box (.var 0) (.sum .zero .unit))))) := by
  refine callbackW ok_empty rfl hΓ (.ofRet ?_)
  refine .bind (.left (.dead (deadSplit hΓ)))
    (d_toResultG (S := []) (A := .zero) (by simp) rfl (d_logRaise2 hΓ)) ?_
  exact .ret (.boxI (.var (.here (.cons (.cons hΓ.toP))))
    (outlives_head (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (.cons (.cons hΓ))))

theorem d_logOutside :
    CDerives LifeCtx.empty [] logOutside (.comp (.ret (.tensor Flag (.sum .zero .unit)))) := by
  refine .bind (A := .ref Flag) .nil
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .ret (letW (appW (d_logInCb (by cdead)) (appW (.var (by csolo))
    (.withbor2 (A := Flag) (B := .sum .zero .unit) 0 (by cdead) rfl
      ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree])
      (by simp [VFree])))) ?_)
  exact pairW (appW (.var (by csolo)) (.free (by cdead))) (.var (by csolo))

/-- **`Log` outside: the log state is kept beside the error**: every run continues to
`(f, inj₂ ())` at the empty memory, `f` the log state. -/
theorem logOutside_answers {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem logOutside μ₁ e₁) :
    ∃ f, Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.pair f (Val.inj₂ Val.unit))) := by
  obtain ⟨v, hv, ls, hP⟩ := adequacyD_obs (by decide) d_logOutside hs
  obtain ⟨f, w, h⟩ := hP
  obtain ⟨rfl, ρ₁, ρ₂, -, -, hw⟩ := pure_sep_iff.mp h
  exact ⟨f, by rwa [vP_zero_sum hw] at hv⟩

/-! #### `Fail` outside -/

/-- The finaliser of `r : Ref Flag`: its destructor. -/
abbrev dFlag : Expr := dtorE (.ref Flag)

theorem dFlag_closed : closedAt 0 dFlag = true := by decide

/-- `Λ. λm. logRaise m`, at the unwinding row. -/
def logRaiseCb : Expr := .val (.lam (.val (.lam (logRaise 0))))

theorem d_logRaiseCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ logRaiseCb (.val (cbUTy 0 LifeCtx.empty.meetOfDom
      (.mut (.var 0) Flag) .zero Sf)) :=
  callbackUW ok_empty rfl hΓ (d_logRaise0 hΓ)

/-- The handled body: `r ← alloc (inj₁ ()); (r, z) ← withborU dFlag r logRaiseCb; absurd z`. -/
def failOutsideBody : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (bindE logRaiseCb
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0) (absurdE (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

/-- **Program 1, `Fail` outside `Log`**. -/
def failOutside : Expr := toResult failOutsideBody

theorem d_failOutsideBody :
    CDerives LifeCtx.empty [⟨retTy [] .zero (.sum .zero .unit), false⟩,
      ⟨clausesTy [] (.sum .zero .unit) Ef, false⟩] failOutsideBody
      (.comp (CTy.effOf Sf .zero)) := by
  refine .bind (A := .ref Flag) (.dead (.dead .nil))
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .bind (.right (.dead (.dead .nil))) (.ret (d_logRaiseCb (by cdead))) ?_
  refine .bind (.right (.right (.dead (.dead .nil))))
    (.ret (.withbor2U (A := Flag) (B := .zero) (S := Sf) 0 (by cdead) rfl
      ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree]) (by simp [VFree])
      (Sf_unwind 0) dFlag_closed (dtor_wf (.ref (.sum .unit .unit)) (by cdead)))) ?_
  refine .effLet (A := .tensor (.ref Flag) .zero) (.left (.left (.left (.dead (.dead .nil)))))
    (fun _ => Ctx.Dead.drops (by cdead)) (fun h => absurd h Sf_not_unr) ?_ ?_
  · refine .app (.left (.right (.left (.dead (.dead .nil))))) ?_ (.there (.here (by cdead)))
    exact .app (.left (.dead (.right (.dead (.dead .nil))))) (.force (.here (by cdead)))
      (.there (.there (.here (by cdead))))
  · refine .tensorE (.left (deadSplit (by cdead))) (.var (.here (by cdead))) ?_
    exact .zeroE (.left (.right (deadSplit (by cdead)))) (.var (.here (by cdead)))

theorem d_failOutside :
    CDerives LifeCtx.empty [] failOutside (.comp (.ret (.sum .zero .unit))) :=
  d_toResult (S := []) (by simp) rfl d_failOutsideBody

/-- **`Fail` outside: the log state is finalised and the error delivered**: every run, under
every allocator, continues to `inj₂ ()` at the empty memory. -/
theorem failOutside_answers {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem failOutside μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) := by
  obtain ⟨v, hv, ls, hP⟩ := adequacyD_obs (by decide) d_failOutside hs
  rwa [vP_zero_sum hP] at hv

/-! ### Program 3: raising inside a reborrow, `Fail` outside

    to_result {
      r ← alloc (inj₁ ());
      (r, z) ← withborU dFlag r (Λ. λm.
                 (m, z′) ← withborU forget m (Λ. λm₂. logRaise m₂);
                 absurd z′);
      absurd z }

`borrow mut r`, and inside it `borrow mut m` (a reborrow), whose callback raises. The unwind
passes both borrows innermost first: the reborrow's lend ends and its source `m` is finalised
(`forget`), then the outer lend ends and the owner's finaliser frees `r`. `to_result` receives the
error, and every run ends at `inj₂ ()` with the empty memory (`reborrowRaise_answers`). -/

/-- The inner callback, at `'y ⊏ 'x`. -/
def innerCb : Expr := .val (.lam (.val (.lam (logRaise 0))))

/-- The outer callback: reborrow `m`, the inner callback raising. -/
def outerCbBody : Expr :=
  bindE innerCb
    (bindE (withborUE forget)
      (.app (.val (.lam (.letpair (.var 0) (absurdE (.var 0)))))
        (.app (.app (.var 0) (.var 2)) (.var 1))))

def outerCb : Expr := .val (.lam (.val (.lam outerCbBody)))

/-- The handled body. -/
def reborrowRaiseBody : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (bindE outerCb
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0) (absurdE (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

/-- **Program 3.** -/
def reborrowRaise : Expr := toResult reborrowRaiseBody

theorem d_outerCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ outerCb (.val (cbUTy 0 LifeCtx.empty.meetOfDom
      (.mut (.var 0) Flag) .zero Sf)) := by
  refine callbackUW ok_empty rfl hΓ ?_
  refine .bind (.right (.dead (deadSplit hΓ)))
    (.ret (callbackUW (x := 1) (L := .mut (.var 1) Flag) (B := .zero) d1_ok rfl (.cons (.cons hΓ))
      (d_logRaise0 (.cons (.cons hΓ))))) ?_
  refine .bind (.right (.right (.dead (deadSplit hΓ))))
    (.ret (.withbor3U (a := .var 0) (A := Flag) (B := .zero) (S := Sf) (d := forget) 1 (by cdead)
      rfl (by simp [VFree]) (by simp [VFree]) (Sf_unwind 1) rfl (.forgetMut (by cdead)))) ?_
  refine .effLet (A := .tensor (.mut (.var 0) Flag) .zero)
    (.left (.left (.left (.dead (deadSplit hΓ)))))
    (fun _ => Ctx.Dead.drops (by cdead)) (fun h => absurd h Sf_not_unr) ?_ ?_
  · refine .app (.left (.right (.left (.dead (deadSplit hΓ))))) ?_ (.there (.here (by cdead)))
    exact .app (.left (.dead (.right (.dead (deadSplit hΓ))))) (.force (.here (by cdead)))
      (.there (.there (.here (by cdead))))
  · refine .tensorE (.left (deadSplit (by cdead))) (.var (.here (by cdead))) ?_
    exact .zeroE (.left (.right (deadSplit (by cdead)))) (.var (.here (by cdead)))

theorem d_reborrowRaiseBody :
    CDerives LifeCtx.empty [⟨retTy [] .zero (.sum .zero .unit), false⟩,
      ⟨clausesTy [] (.sum .zero .unit) Ef, false⟩] reborrowRaiseBody
      (.comp (CTy.effOf Sf .zero)) := by
  refine .bind (A := .ref Flag) (.dead (.dead .nil))
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .bind (.right (.dead (.dead .nil))) (.ret (d_outerCb (by cdead))) ?_
  refine .bind (.right (.right (.dead (.dead .nil))))
    (.ret (.withbor2U (A := Flag) (B := .zero) (S := Sf) 0 (by cdead) rfl
      ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree]) (by simp [VFree])
      (Sf_unwind 0) dFlag_closed (dtor_wf (.ref (.sum .unit .unit)) (by cdead)))) ?_
  refine .effLet (A := .tensor (.ref Flag) .zero) (.left (.left (.left (.dead (.dead .nil)))))
    (fun _ => Ctx.Dead.drops (by cdead)) (fun h => absurd h Sf_not_unr) ?_ ?_
  · refine .app (.left (.right (.left (.dead (.dead .nil))))) ?_ (.there (.here (by cdead)))
    exact .app (.left (.dead (.right (.dead (.dead .nil))))) (.force (.here (by cdead)))
      (.there (.there (.here (by cdead))))
  · refine .tensorE (.left (deadSplit (by cdead))) (.var (.here (by cdead))) ?_
    exact .zeroE (.left (.right (deadSplit (by cdead)))) (.var (.here (by cdead)))

theorem d_reborrowRaise :
    CDerives LifeCtx.empty [] reborrowRaise (.comp (.ret (.sum .zero .unit))) :=
  d_toResult (S := []) (by simp) rfl d_reborrowRaiseBody

/-- **Program 3: the buffer goes back to its owner, and the error is delivered**: every run,
under every allocator, continues to `inj₂ ()` at the empty memory. -/
theorem reborrowRaise_answers {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem reborrowRaise μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) := by
  obtain ⟨v, hv, ls, hP⟩ := adequacyD_obs (by decide) d_reborrowRaise hs
  rwa [vP_zero_sum hP] at hv


/-! ### Program 1 again, with `log` a native control operation

`log : 1 ↠^aff 1` of the name `2`, handled by `with_log`, which resumes `κ` and marks that a log
happened:

    with_log e = handle_2 e with (λx. (x, inj₁ ()),
                                  λ(v, κ). let (x, f) = κ.resume v in drop f; (x, inj₂ ()))

The body `log (); raise ()` runs at the row `{Fail, Log}`.

* **`Log` outside** (`nLogOutside = with_log (to_result body)`): `to_result` catches the raise
  inside `κ`'s resumption; `with_log` answers `(inj₂ (), f)`, its log flag kept.
* **`Fail` outside** (`nFailOutside = to_result (with_log body)`): the raise passes `with_log`'s
  frame and its clause's frame (forwarding: `raise` of the name `1` is not `with_log`'s), and
  `to_result` answers `inj₂ ()`: `with_log`'s answer, with its flag, is lost.

Both rows hold both names, in the two orders. -/

/-- `log : 1 ↠^aff 1`, the operation `0` of the name `2`. -/
def logSig : OpSig := ⟨2, 0, .opt, .top, .unit, .unit, .ret .unit⟩

/-- `Log`'s operations. -/
abbrev El : List (Count × VTy × VTy) := [(.opt, .unit, .unit)]

/-- `with_log`'s answer clause `λx. (x, inj₁ ())`. -/
def hrL : Expr := .val (.lam (.pair (.var 0) (.inj₁ unit')))

/-- `with_log`'s clause: resume `κ` at `v`, then mark. -/
def clL : Expr :=
  .val (.lam (.letpair (.var 0)
    (.app (.val (.lam (.letpair (.var 0) (.seq (dropB (.var 0)) (.pair (.var 1) (.inj₂ unit'))))))
      (.app (.app (.var 0) (.val (.inj₁ .unit))) (.var 1)))))

def clsL : Expr := .pair clL (.val .unit)

/-- `with_log e`. -/
def withLog (e : Expr) : Expr := bindE clsL (bindE hrL (hndTerm 2 [.opt] 0 1 e))

theorem d_hrL {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ hrL (.val (retTy S A (.tensor A Flag))) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
        (.sumI₁ (.unitI (.cons hΓ.toP)))))))

theorem d_clL {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clL (.val (clauseTy S (.tensor A Flag) (.opt, .unit, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .effLet (A := .tensor A Flag) (.left (.left (.dead (deadSplit hΓ))))
    (fun _ => Ctx.Dead.drops (by cdead)) (fun _ => dead_noLive (by cdead)) ?_ ?_
  · refine .app (.left (.right (.dead (deadSplit hΓ)))) ?_ (.there (.here (by cdead)))
    exact .proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S (.tensor A Flag))) (CTy.effOf S .unit))
      (.here (by cdead)))
  · refine .tensorE (.left (deadSplit (by cdead))) (.var (.here (by cdead))) ?_
    refine .unitE (.left (.right (deadSplit (by cdead))))
      (d_dropB (.var (by csolo)) (by cdead)) ?_
    exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (pairW (.var (by csolo)) (.sumI₂ (.unitI (by cdead)))))

theorem d_withLogG {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {e : Expr}
    (hS : ∀ o ∈ S, o.n ≠ 2) (hSd : Row.divB S = false)
    (he : CDerives Δ (⟨retTy S A (.tensor A Flag), false⟩ ::
      ⟨clausesTy S (.tensor A Flag) El, false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff 2 El 0 ++ S) A))) :
    CDerives Δ Γ (withLog e) (.comp (CTy.effOf S (.tensor A Flag))) := by
  refine .bind (split_kill Γ).toP
    (.ret (.tensorI (deadSplit (kill_dead Γ)) (d_clL (S := S) (A := A) (kill_dead Γ))
      (.unitI (kill_dead Γ).toP))) ?_
  refine .bind (.right (split_kill Γ).toP) (.ret (d_hrL (S := S) (A := A) (.cons (kill_dead Γ)))) ?_
  exact .effHandle (E := El) (.left (.left (split_kill Γ).toP))
    (.left (.right (deadSplit (kill_dead Γ)))) (.here (.cons (kill_dead Γ).toP))
    (.there (.here (kill_dead Γ).toP)) (by decide) hS (by simp)
    (by rw [Row.divB_ofEff_eq (by decide)]; exact hSd) he

/-- `log (); raise ()`. -/
def logThenRaise : Expr := .app (.val (.lam raiseU)) (performE (opArgE 2 0 (.val .unit)))

theorem d_logThenRaise {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {B : VTy}
    (hl : Row.find S 2 0 = some logSig) (hf : Row.find S 1 0 = some failSig)
    (hU : ¬ S.Unr) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ logThenRaise (.comp (CTy.effOf S B)) :=
  .effLet (A := .unit) (deadSplit hΓ) (fun _ => Ctx.Dead.drops hΓ) (fun h => absurd h hU)
    (.effPerform (o := logSig) hl rfl (.unitI hΓ.toP))
    (d_raiseU hf (.drop rfl hΓ.toP))

/-- **Program 1 with a native `log`, `Log` outside `Fail`.** -/
def nLogOutside : Expr := withLog (toResult logThenRaise)

/-- **Program 1 with a native `log`, `Fail` outside `Log`.** -/
def nFailOutside : Expr := toResult (withLog logThenRaise)

theorem d_nLogOutside :
    CDerives LifeCtx.empty [] nLogOutside (.comp (.ret (.tensor (.sum .zero .unit) Flag))) := by
  refine d_withLogG (Γ := []) (S := []) (by simp) rfl ?_
  refine d_toResultG (S := [logSig]) (A := .zero) (by simp [logSig]) rfl ?_
  exact d_logThenRaise rfl rfl
    (by simp [Row.Unr, Row.ofEff, logSig]) (by cdead)

theorem d_nFailOutside :
    CDerives LifeCtx.empty [] nFailOutside (.comp (.ret (.sum (.tensor .zero Flag) .unit))) := by
  refine d_toResult (S := []) (A := .tensor .zero Flag) (by simp) rfl ?_
  refine d_withLogG (S := [failSig]) (A := .zero) (by simp [failSig]) rfl ?_
  exact d_logThenRaise rfl rfl
    (by simp [Row.Unr, Row.ofEff, failSig]) (by cdead)

/-- **Native `log`, `Log` outside: the log flag is kept beside the error**: every run continues
to `(inj₂ (), f)` at the empty memory. -/
theorem nLogOutside_answers {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem nLogOutside μ₁ e₁) :
    ∃ f, Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.pair (Val.inj₂ Val.unit) f)) := by
  obtain ⟨v, hv, ls, hP⟩ := adequacyD_obs (by decide) d_nLogOutside hs
  obtain ⟨w, f, h⟩ := hP
  obtain ⟨rfl, ρ₁, ρ₂, -, hw, -⟩ := pure_sep_iff.mp h
  exact ⟨f, by rwa [vP_zero_sum hw] at hv⟩

/-- **Native `log`, `Fail` outside: `with_log`'s answer is lost and the error delivered**: every
run continues to `inj₂ ()` at the empty memory. -/
theorem nFailOutside_answers {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem nFailOutside μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) := by
  obtain ⟨v, hv, ls, hP⟩ := adequacyD_obs (by decide) d_nFailOutside hs
  rcases hP with ⟨w, h⟩ | ⟨w, h⟩
  · obtain ⟨-, a, b, h⟩ := pure_sep_iff.mp h
    obtain ⟨-, ρa, ρb, -, ha, -⟩ := pure_sep_iff.mp h
    exact ha.elim
  · obtain ⟨rfl, -, rfl⟩ := pure_sep_iff.mp h
    exact hv

/-! ### Program 2: logging inside a borrow, the `Log` handler outside

    s ← alloc (inj₁ ());  b ← alloc (inj₁ ());
    let (s, p) = withbor s (Λ. λl.                       -- the `Log` handler: a borrow of `s`
                   let q = withbor b (Λ. λm.             -- `borrow mut b`
                             log l; write m; forget l; forget m; ()) in q) in
    let (b, u) = p; u; (free s, free b)

`log` is answering: a call on the capability `l` that the inner borrow's callback captures, an
outer borrow that outlives the callback's lifetime. It needs no new rule (§19); the program is
typed by §3's rules and runs to the two cells' contents at the empty memory. -/

/-- A callback `thunk Λ. λx. body` at a fresh `'x ⊏ ⊓Δ` that captures `Γ`'s live slots, none of
which mentions `'x`. -/
theorem callbackCW {Δ : LifeCtx} {Γ : Ctx VTy} {body : Expr} {x : LifeVar} {A B : VTy}
    (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : CDerives (Δ.extend x Δ.meetOfDom) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.val B)) :
    CDerives Δ Γ (.val (.lam (.val (.lam body)))) (.val (.all x Δ.meetOfDom (.lolli A B))) :=
  .thunkV rfl (.allI (Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf Δ.entries))
    (fun _ _ h => hΔ.bound_mentions_false hx h) hΓx (.ret (.lamV h)))

/-- The inner callback's body: log through `l` (index 2), write through `m`, end both. -/
def innerLogBody : Expr :=
  .letpair (app2 withswap (.var 2) setG)
    (.seq (.var 0) (.letpair (app2 withswap (.var 2) setG)
      (.seq (.var 0) (.seq (.app forget (.var 3)) (.seq (.app forget (.var 1)) unit')))))

/-- The outer callback's body: borrow `b` (index 2), the inner callback capturing `l`. -/
def outerLogBody : Expr :=
  elet (app2 withbor (.var 2) (.val (.lam (.val (.lam innerLogBody))))) (.var 0)

/-- A live slot of a part of `Γ` is a slot of `Γ`. -/
theorem part_live₁ (e : Expr) : ∀ {i : Nat} {Γ : Ctx VTy} {s : Slot VTy},
    s ∈ (part e i Γ).1 → s.live = true → s ∈ Γ
  | _, [], _, h, _ => by simp [part] at h
  | i, ⟨T, true⟩ :: Γ, s, h, hl => by
      by_cases hocc : occ i e = true
      · simp only [part, hocc, if_true] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (part_live₁ e h hl)
      · simp only [part, hocc, if_false, Bool.false_eq_true] at h
        rcases List.mem_cons.mp h with rfl | h
        · simp at hl
        · exact List.mem_cons_of_mem _ (part_live₁ e h hl)
  | i, ⟨T, false⟩ :: Γ, s, h, hl => by
      simp only [part] at h
      rcases List.mem_cons.mp h with rfl | h
      · simp at hl
      · exact List.mem_cons_of_mem _ (part_live₁ e h hl)

/-- **Program 2.** -/
def logInBorrow : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (bindE (.app alloc' (.inj₁ unit'))
      (.letpair (app2 withbor (.var 1) (.val (.lam (.val (.lam outerLogBody)))))
        (.letpair (.var 0)
          (.seq (.var 0) (.pair (.app free' (.var 3)) (.app free' (.var 1)))))))

theorem d_innerLogBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives (D1.extend 1 D1.meetOfDom)
      (⟨.mut (.var 1) Flag, true⟩ :: ⟨.unit, false⟩ :: ⟨.mut (.var 0) Flag, true⟩ :: Γ)
      innerLogBody (.val (.box (.var 1) .unit)) := by
  refine letW (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine seqW (.var (by csolo)) ?_
  refine letW (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine seqW (.var (by csolo)) ?_
  refine seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  refine seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact .boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩

theorem d_outerLogBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives D1 (⟨.mut (.var 0) Flag, true⟩ :: ⟨.unit, false⟩ :: ⟨.ref Flag, true⟩ :: Γ)
      outerLogBody (.val (.box (.var 0) (.tensor (.ref Flag) .unit))) := by
  refine eletW (appW (callbackCW d1_ok rfl (fun s hs hl => ?_) (d_innerLogBody (by cdead)))
    (appW (.var (by csolo)) (.withbor2 (A := Flag) (B := .unit) 1 (by cdead) rfl
      ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree])
      (by simp [VFree])))) ?_
  · have hs' := part_live₁ _ (part_live₁ _ hs hl) hl
    simp only [List.mem_cons] at hs'
    rcases hs' with rfl | rfl | rfl | hs'
    · simp [VFree, Lifetime.Life.mentions]
    · simp at hl
    · simp [VFree]
    · exact (dead_noLive (P := fun _ => False) hΓ s hs' hl).elim
  · exact .boxI (.var (by csolo)) (outlives_head (LifeCtx.defines_of_wf rfl)
      (.tensor (.ref (outlives_of_dataB rfl)) .unit) (by cdead))

theorem d_logInBorrow :
    CDerives LifeCtx.empty [] logInBorrow (.comp (.ret (.tensor Flag Flag))) := by
  refine .bind (A := .ref Flag) .nil
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .bind (A := .ref Flag) (.right .nil)
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .ret (letW (appW (callbackCW ok_empty rfl (fun s hs hl => ?_)
    (d_outerLogBody (Γ := [⟨.ref Flag, false⟩]) (by cdead)))
    (appW (.var (by csolo)) (.withbor2 (A := Flag) (B := .tensor (.ref Flag) .unit) 0 (by cdead)
      rfl ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree])
      (by simp [VFree])))) ?_)
  · have hs' := part_live₁ _ (part_live₁ _ hs hl) hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl <;> simp [VFree]
  · refine letW (.var (by csolo)) ?_
    refine seqW (.var (by csolo)) ?_
    exact pairW (appW (.var (by csolo)) (.free (by cdead))) (appW (.var (by csolo)) (.free (by cdead)))

/-- **Program 2 runs**: every run, under every allocator, continues to the two cells' contents
at the empty memory. -/
theorem logInBorrow_runs {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem logInBorrow μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs (by decide) d_logInBorrow hs
  exact ⟨v, hv⟩

/-- The interpreter's run of program 2: the log cell and the buffer both written (`inj₂ ()`), and
no leak. -/
theorem logInBorrow_eval :
    (match eval logInBorrow with
      | .value ⟨.pair (.inj₂ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ### Program 4: `loop { log("tick") }`

`Loop_{Log} 0 1 = νX. F_{Log}(0 ⊕ U X) & F_{Log} 1`: a loop that never finishes, each observation
a finite effectful step that logs once. `tick = unfold step ()` with

    step s = ⟨log (); return inj₂ s, return s⟩,

and the driver installs `with_log` around each observation (`driveLog`): `n` observations, then
`close`. Every `tickProg n` is a closed computation of `F 1`, so every run of it, under every
allocator, is safe and ends at `()` with the empty memory (`tickProg_runs`). -/

/-- The loop's body. -/
abbrev TickC : CTy := CTy.loopEffBody [logSig] .zero .unit

theorem tickC_nuOk : TickC.NuOk :=
  CTy.loopEffBody_nuOk (by simp [logSig, VTy.Cl]) .zero .unit

/-- `step s = ⟨log (); return inj₂ s, return s⟩`. -/
def tickStep : Val :=
  .lam (withPair (.app (.val (.lam (.inj₂ (.var 3)))) (performE (opArgE 2 0 (.val .unit))))
    (.var 2))

theorem d_tickStep {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val tickStep) (.val (.bang (.thunk (.arr .unit (TickC.instT .unit))))) := by
  rw [CTy.loopEffBody_instT]
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI ?_ ?_))
  · refine .effLet (A := .unit) (.dead (.dead (.right (deadSplit hΓ))))
      (fun _ s hs hl => ?_) (fun h => by
        obtain ⟨o, ho, h⟩ := h; simp at ho; subst ho; cases h)
      (.effPerform (o := logSig) rfl rfl (.unitI (by cdead)))
      (.effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
        (.ret (.sumI₂ (.var (.skip rfl (.there (.there (.here hΓ.toP))))))))
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · simp at hl
    · simp at hl
    · exact .unit
    · exact (dead_noLive (P := fun _ => False) hΓ s hs hl).elim
  · exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.var (.there (.there (.here hΓ.toP)))))

/-- `d : U(Loop_{Log} 0 1) ⊢ driveLog n : F 1`: `n` observations, each under `with_log`, then
`close`. -/
def driveLog : ℕ → Expr
  | 0 => bindE (withLog (.app (.var 2) (.val (.inj₂ .unit))))
      (.letpair (.var 0) (.seq (.var 1) (dropB (.var 0))))
  | n + 1 => bindE (withLog (.app (.var 2) (.val (.inj₁ .unit))))
      (.letpair (.var 0) (.seq (dropB (.var 0)) (.case (.var 1) (absurdE (.var 0)) (driveLog n))))

theorem d_driveLog : ∀ (n : ℕ) {Γ : Ctx VTy}, Ctx.Dead Γ →
    CDerives LifeCtx.empty (⟨.thunk (.nu TickC), true⟩ :: Γ) (driveLog n) (.comp (.ret .unit))
  | 0, Γ, hΓ => by
      refine .bind (.left (deadSplit hΓ))
        (d_withLogG (S := []) (A := .unit) (by simp) rfl
          (.proj₂ (.nuOut tickC_nuOk (.force (.there (.there (.here hΓ.toP))))))) ?_
      refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (by cdead))) ?_
      exact .ret (seqW (.var (by csolo)) (d_dropB (.var (by csolo)) (by cdead)))
  | n + 1, Γ, hΓ => by
      refine .bind (.left (deadSplit hΓ))
        (d_withLogG (S := []) (A := .sum .zero (.thunk (.nu TickC))) (by simp) rfl
          (.proj₁ (.nuOut tickC_nuOk (.force (.there (.there (.here hΓ.toP))))))) ?_
      refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (by cdead))) ?_
      refine .unitE (.left (.right (.dead (.dead (deadSplit hΓ))))) (d_dropB (.var (by csolo)) (by cdead)) ?_
      exact .sumE (.dead (.left (.dead (.dead (deadSplit hΓ))))) (.var (by csolo))
        (.zeroE (.left (deadSplit (by cdead))) (.var (.here (by cdead))))
        (d_driveLog n (by cdead))

/-- **Program 4**: `s ← (); f ← unfold step; d ← ⟨(f s) π₁, (f s) π₂⟩; driveLog n`. -/
def tickProg (n : ℕ) : Expr :=
  bindE (.val .unit) (bindE (.app (.val (unfoldV TickC)) (.val tickStep))
    (bindE (withPair (.app (.app (.var 2) (.var 3)) (.val (.inj₁ .unit)))
        (.app (.app (.var 2) (.var 3)) (.val (.inj₂ .unit))))
      (driveLog n)))

theorem d_tickProg (n : ℕ) :
    CDerives LifeCtx.empty [] (tickProg n) (.comp (.ret .unit)) := by
  have d_fs : CDerives LifeCtx.empty (withCtx [⟨.thunk (.arr .unit (.nu TickC)), true⟩, ⟨.unit, true⟩])
      (.app (.var 2) (.var 3)) (.comp (.nu TickC)) :=
    .app (.dead (.dead (.left (.right .nil)))) (.force (.there (.there (.here (.cons .nil)))))
      (.there (.there (.there (.here .nil))))
  refine .bind .nil (.ret (.unitI .nil)) ?_
  refine .bind (.right .nil)
    (.ret (.bangE (.lolliE (deadSplit (.cons .nil)) (d_tickStep (.cons .nil))
      (.unfoldN TickC .unit tickC_nuOk (Ctx.Dead.cons Ctx.Dead.nil).toP)))) ?_
  refine .bind (.left (.left .nil))
    (.ret (.thunkV rfl (.nuIn tickC_nuOk (.withI (.proj₁ (.nuOut tickC_nuOk d_fs))
      (.proj₂ (.nuOut tickC_nuOk d_fs)))))) ?_
  exact d_driveLog n (.cons (.cons .nil))

/-- **Program 4 runs**: for every `n`, every run of `n` effectful observations and a close, under
every allocator, is safe and ends at `()` with the empty memory. -/
theorem tickProg_runs (n : ℕ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (tickProg n) μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  adequacyD (d_tickProg n) hs

/-! ### Program 5: `take(n)` stops a producer that holds a cell

`yield : 1 ↠^aff 1`, the operation `0` of the name `3`. The producer allocates a cell, yields
three times, and frees the cell, with a finaliser that frees it when the producer is cancelled:

    producer = r ← alloc (inj₁ ());
               (yield (); yield (); yield ()) then x. drop (free r); x unwind drop (free r)

`take n` handles `yield` with a counter, the state-passing answer `U(N ⊸ F(1 ⊕ 1))`: at each
`yield` it resumes `κ` with the count decreased, and at zero it cancels `κ`. Cancelling unwinds the
producer: the finaliser frees the cell. For every `n` the program is closed and typed, so every
run, under every allocator, ends at the empty memory (`takeProg_runs`): when `take` stops the
producer early, the cell it held is freed. -/

/-- `yield : 1 ↠^aff 1`. -/
def yieldSig : OpSig := ⟨3, 0, .opt, .top, .unit, .unit, .ret .unit⟩

/-- `Yield`'s operations. -/
abbrev Ey : List (Count × VTy × VTy) := [(.opt, .unit, .unit)]

/-- `yield ()`. -/
def yieldE : Expr := performE (opArgE 3 0 (.val .unit))

/-- The producer's body. -/
def producer : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (thenE (.seq (dropB (.app free' (.var 1))) (.var 0)) (dropB (.app free' (.var 1)))
      (.app (.val (.lam (.app (.val (.lam yieldE)) yieldE))) yieldE))

/-- `take`'s answer type, `U(N ⊸ F(1 ⊕ 1))`. -/
abbrev TakeR : VTy := .thunk (.arr natN (.ret Flag))

/-- `take`'s answer clause: `λx. return (λc. inj₁ x)`. -/
def hrT : Expr := .val (.lam (.val (.lam (.inj₁ (.var 1)))))

/-- `take`'s clause: `λ(v, κ). return (λc. case c {zero ⇒ κ.cancel; inj₂ () |
succ c′ ⇒ κ.resume v to g. g c′})`. -/
def clT : Expr :=
  .val (.lam (.letpair (.var 0) (.val (.lam (.case (.var 0)
    (bindE (.app (.var 2) (.val (.inj₂ .unit))) (.inj₂ unit'))
    (bindE (.app (.app (.var 2) (.val (.inj₁ .unit))) (.var 3)) (.app (.var 0) (.var 1))))))))

def clsT : Expr := .pair clT (.val .unit)

/-- **Program 5**: `take n producer`. -/
def takeProg (n : ℕ) : Expr :=
  bindE clsT (bindE hrT (bindE (hndTerm 3 [.opt] 0 1 producer)
    (bindE (.val (num n)) (.app (.var 1) (.var 0)))))

theorem d_yieldE {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ yieldE (.comp (CTy.effOf [yieldSig] .unit)) :=
  .effPerform (o := yieldSig) rfl rfl (.unitI hΓ)

theorem yield_not_unr : ¬ Row.Unr [yieldSig] := by
  rintro ⟨o, ho, h⟩; simp at ho; subst ho; cases h

theorem yield_not_unrD : ¬ Row.UnrD [yieldSig] := fun h =>
  yield_not_unr ((Row.unrD_iff_of_fin (by simp [yieldSig])).mp h)

theorem d_producer {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ producer (.comp (CTy.effOf [yieldSig] .unit)) := by
  refine .bind (A := .ref Flag) (deadSplit hΓ)
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine CDerives.effThenA (A := .unit) (.right (deadSplit hΓ)) (by simp [Row.NZ, yieldSig])
    (by simp [Row.Uniq]) (fun h => absurd h yield_not_unrD) ?_ ?_ ?_
  · refine .effLet (A := .unit) (deadSplit (Ctx.Dead.cons hΓ)) (fun _ => Ctx.Dead.drops (Ctx.Dead.cons hΓ))
      (fun h => absurd h yield_not_unr) (d_yieldE (Ctx.Dead.cons hΓ).toP) ?_
    exact .effLet (A := .unit) (.dup rfl (deadSplit (Ctx.Dead.cons hΓ)))
      (fun _ s hs hl => by
        rcases List.mem_cons.mp hs with rfl | hs
        · exact .unit
        · exact (dead_noLive (P := fun _ => False) (Ctx.Dead.cons hΓ) s hs hl).elim)
      (fun h => absurd h yield_not_unr) (d_yieldE (.drop rfl (Ctx.Dead.cons hΓ).toP))
      (d_yieldE (.drop rfl (.drop rfl (Ctx.Dead.cons hΓ).toP)))
  · refine .unitE (.right (.left (deadSplit hΓ)))
      (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead)) ?_
    exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h) (.ret (.var (by csolo)))
  · show CDerives _ _ _ (.comp (.ret .unit))
    exact .ret (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))

theorem natN_persistent : natN.Persistent := rfl

theorem d_hrT {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ hrT (.val (retTy [] .unit TakeR)) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret (.thunkV rfl (.lam (.ret (.sumI₁
    (.var (.skip natN_persistent (.here hΓ.toP)))))))))

theorem d_clT {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ clT (.val (clauseTy [] TakeR (.opt, .unit, .unit))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .ret (.thunkV rfl (.lam ?_))
  refine .sumE (.left (.right (.right (.dead (deadSplit hΓ)))))
    (.unroll (A := natBody) (.var (.here (by cdead)))) ?_ ?_
  · refine .bind (.right (.dead (.left (.right (.dead (deadSplit hΓ))))))
      (.proj₂ (.force (C := .amp (.arr .unit (CTy.effOf [] TakeR)) (CTy.effOf [] .unit))
        (.there (.there (.here (by cdead)))))) ?_
    exact .ret (.sumI₂ (.unitI (.drop rfl (.drop rfl (.cons (.cons (.drop rfl
      (.cons hΓ.toP))))))))
  · refine .bind (.right (.dead (.left (.left (.dead (deadSplit hΓ))))))
      (.app (.dead (.dead (.left (.right (.dead (deadSplit hΓ))))))
        (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] TakeR)) (CTy.effOf [] .unit))
          (.there (.there (.here (by cdead))))))
        (.there (.there (.there (.here (by cdead)))))) ?_
    exact .app (.left (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
      (.force (.here (by cdead))) (.there (.here (by cdead)))

theorem d_takeProg (n : ℕ) :
    CDerives LifeCtx.empty [] (takeProg n) (.comp (.ret Flag)) := by
  refine .bind .nil (.ret (.tensorI .nil (d_clT .nil) (.unitI .nil))) ?_
  refine .bind (.right .nil) (.ret (d_hrT (.cons .nil))) ?_
  refine .bind (.left (.left .nil))
    (.effHandle (S := []) (E := Ey) (n := 3) (A := .unit) (R := TakeR)
      (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
      (by decide) (by simp) (by simp) rfl (d_producer (Ctx.Dead.cons (Ctx.Dead.cons Ctx.Dead.nil)))) ?_
  refine .bind (.right (.dead (.dead .nil))) (.ret (d_num (by cdead) n)) ?_
  exact .app (.right (.left (.dead (.dead .nil)))) (.force (.there (.here (by cdead))))
    (.here (by cdead))

/-- **Program 5 runs**: for every `n`, every run of `take n producer`, under every allocator,
ends at the empty memory: when `take` cancels the producer, its finaliser freed the cell. -/
theorem takeProg_runs (n : ℕ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (takeProg n) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs (by decide) (d_takeProg n) hs
  exact ⟨v, hv⟩

/-! ### Program 6: cancelling a stored continuation

`susp : 1 ↠^aff 1`, the operation `0` of the name `4`. The performer holds a cell, with a
finaliser, and suspends once:

    performer = r ← alloc (inj₁ ()); susp () then x. drop (free r); x unwind drop (free r)

The handler stores `κ` in a cell, takes it back, and cancels it instead of resuming it:

    handle_4 performer with (λx. x, λ(v, κ). v; c ← alloc κ; κ′ ← free c; κ′.cancel)

Cancelling runs `κ`'s finaliser, which frees the performer's cell. The program is a closed
computation of `F 1`, so every run, under every allocator, ends at `()` with the empty memory
(`storeCancel_runs`). -/

/-- `susp : 1 ↠^aff 1`. -/
def suspSig : OpSig := ⟨4, 0, .opt, .top, .unit, .unit, .ret .unit⟩

/-- `Susp`'s operations. -/
abbrev Es : List (Count × VTy × VTy) := [(.opt, .unit, .unit)]

/-- The performer. -/
def performer : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (thenE (.seq (dropB (.app free' (.var 1))) (.var 0)) (dropB (.app free' (.var 1)))
      (performE (opArgE 4 0 (.val .unit))))

/-- The answer clause `λx. x`. -/
def hrS : Expr := .val (.lam (.var 0))

/-- The clause: store `κ`, take it back, cancel it. -/
def clS : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1)
    (bindE (.app alloc' (.var 0)) (bindE (.app free' (.var 0))
      (.app (.var 0) (.val (.inj₂ .unit))))))))

def clsS : Expr := .pair clS (.val .unit)

/-- **Program 6.** -/
def storeCancel : Expr := bindE clsS (bindE hrS (hndTerm 4 [.opt] 0 1 performer))

theorem susp_not_unr : ¬ Row.Unr [suspSig] := by
  rintro ⟨o, ho, h⟩; simp at ho; subst ho; cases h

theorem susp_not_unrD : ¬ Row.UnrD [suspSig] := fun h =>
  susp_not_unr ((Row.unrD_iff_of_fin (by simp [suspSig])).mp h)

theorem d_performer {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ performer (.comp (CTy.effOf [suspSig] .unit)) := by
  refine .bind (A := .ref Flag) (deadSplit hΓ)
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine CDerives.effThenA (A := .unit) (.right (deadSplit hΓ)) (by simp [Row.NZ, suspSig])
    (by simp [Row.Uniq]) (fun h => absurd h susp_not_unrD)
    (.effPerform (o := suspSig) rfl rfl (.unitI (Ctx.Dead.cons hΓ).toP)) ?_ ?_
  · refine .unitE (.right (.left (deadSplit hΓ)))
      (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead)) ?_
    exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h) (.ret (.var (by csolo)))
  · show CDerives _ _ _ (.comp (.ret .unit))
    exact .ret (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))

theorem d_hrS {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ hrS (.val (retTy [] .unit .unit)) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret (.var (.here hΓ.toP))))

theorem d_clS {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ clS (.val (clauseTy [] .unit (.opt, .unit, .unit))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .unitE (.right (.left (.dead (deadSplit hΓ)))) (.var (by csolo)) ?_
  refine .bind (.left (.dead (.dead (deadSplit hΓ))))
    (.ret (appW (.var (by csolo)) (.alloc (by cdead)))) ?_
  refine .bind (.left (.dead (.dead (.dead (deadSplit hΓ)))))
    (.ret (appW (.var (by csolo)) (.free (by cdead)))) ?_
  exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf [] .unit)) (CTy.effOf [] .unit))
    (.here (by cdead)))

theorem d_storeCancel : CDerives LifeCtx.empty [] storeCancel (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.tensorI .nil (d_clS .nil) (.unitI .nil))) ?_
  refine .bind (.right .nil) (.ret (d_hrS (.cons .nil))) ?_
  exact .effHandle (S := []) (E := Es) (n := 4) (A := .unit) (R := .unit)
    (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
    (by decide) (by simp) (by simp) rfl (d_performer (Ctx.Dead.cons (Ctx.Dead.cons Ctx.Dead.nil)))

/-- **Program 6 runs**: every run, under every allocator, ends at `()` with the empty memory:
the cancelled continuation's finaliser freed the cell it captured. -/
theorem storeCancel_runs {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem storeCancel μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  adequacyD d_storeCancel hs

/-! ### Program 4, as §19 states it: the `Log` state in the loop's state

`Loop 0 (Ref Flag)`: the loop's state is the log cell, and each observation logs by an answering
call, a borrow of the state:

    step s = ⟨let (s, u) = withbor s (Λ. λm. log m; forget m; ()) in u; inj₂ s, return s⟩

`tickAnsProg n` drives `n` observations (`driveE`), then frees the cell the loop closes with. -/

/-- The observation's callback: log through the borrow of the state. -/
def logCb : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) setG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))))

/-- `step s = ⟨log s; inj₂ s, return s⟩`. -/
def tickAnsStep : Val :=
  .lam (withPair (.letpair (app2 withbor (.var 2) logCb) (.seq (.var 0) (.inj₂ (.var 1))))
    (.var 2))

theorem d_logCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ logCb (.val (.all 0 LifeCtx.empty.meetOfDom
      (.lolli (.mut (.var 0) Flag) (.box (.var 0) .unit)))) := by
  refine callbackW ok_empty rfl hΓ ?_
  refine letW (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine seqW (.var (by csolo)) ?_
  refine seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact .boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩

theorem d_tickAnsStep {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val tickAnsStep)
      (.val (.bang (.thunk (.arr (.ref Flag) (.amp (.ret (.sum .zero (.ref Flag)))
        (.ret (.ref Flag))))))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI ?_ ?_))
  · refine .ret (letW (appW (d_logCb (by cdead)) (appW (.var (by csolo))
      (.withbor2 (A := Flag) (B := .unit) 0 (by cdead) rfl
        ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree])
        (by simp [VFree])))) ?_)
    exact seqW (.var (by csolo)) (.sumI₂ (.var (by csolo)))
  · exact .ret (.var (.there (.there (.here hΓ.toP))))

/-- **Program 4 (answering)**: `s ← alloc (inj₁ ()); f ← unfold step; d ← ⟨(f s) π₁, (f s) π₂⟩;
driveE n to r. case r {inj₁ z ⇒ absurd z | inj₂ s ⇒ free s}`. -/
def tickAnsProg (n : ℕ) : Expr :=
  bindE (.app alloc' (.inj₁ unit')) (bindE (.app (.val (unfoldV (CTy.loopBody .zero (.ref Flag))))
      (.val tickAnsStep))
    (bindE (withPair (.app (.app (.var 2) (.var 3)) (.val (.inj₁ .unit)))
        (.app (.app (.var 2) (.var 3)) (.val (.inj₂ .unit))))
      (bindE (driveE n) (.case (.var 0) (absurdE (.var 0)) (.app free' (.var 0))))))

theorem d_tickAnsProg (n : ℕ) :
    CDerives LifeCtx.empty [] (tickAnsProg n) (.comp (.ret Flag)) := by
  have d_fs : CDerives LifeCtx.empty
      (withCtx [⟨.thunk (.arr (.ref Flag) (.loop .zero (.ref Flag))), true⟩, ⟨.ref Flag, true⟩])
      (.app (.var 2) (.var 3)) (.comp (.loop .zero (.ref Flag))) :=
    .app (.dead (.dead (.left (.right .nil)))) (.force (.there (.there (.here (.cons .nil)))))
      (.there (.there (.there (.here .nil))))
  refine .bind (A := .ref Flag) .nil
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .bind (.right .nil)
    (.ret (.bangE (.lolliE (deadSplit (Ctx.Dead.cons Ctx.Dead.nil))
      (by rw [CTy.loopBody_instT .zero (.ref Flag) (.ref Flag)]
          exact d_tickAnsStep (Ctx.Dead.cons Ctx.Dead.nil))
      (.unfoldN (CTy.loopBody .zero (.ref Flag)) (.ref Flag) (CTy.loopBody_nuOk _ _)
        (Ctx.Dead.cons Ctx.Dead.nil).toP)))) ?_
  refine .bind (.left (.left .nil))
    (.ret (.thunkV rfl (.loopIn (.withI (.proj₁ (.loopOut d_fs)) (.proj₂ (.loopOut d_fs)))))) ?_
  refine .bind (.left (.dead (.dead .nil))) (d_driveL .zero (.ref Flag) n (by cdead)) ?_
  exact .sumE (.left (deadSplit (by cdead))) (.var (.here (by cdead)))
    (.zeroE (.left (deadSplit (by cdead))) (.var (.here (by cdead))))
    (.ret (appW (.var (by csolo)) (.free (by cdead))))

/-- **Program 4 (answering) runs**: for every `n`, every run, under every allocator, ends at the
empty memory with the log cell's contents. -/
theorem tickAnsProg_runs (n : ℕ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (tickAnsProg n) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs (by decide) (d_tickAnsProg n) hs
  exact ⟨v, hv⟩

/-- The interpreter's run of three observations: the log cell written (`inj₂ ()`), no leak. -/
theorem tickAnsProg_eval :
    (match eval (tickAnsProg 3) with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-! ### The interpreter's runs

`Support`'s executable interpreter (`eval`) with the capture steps of §19: each program's
observable answer and no leak. -/

/-- **Program 1, `Log` outside**: the log state is kept and records the log (`inj₂ ()`), beside
the error. -/
theorem logOutside_eval :
    (match eval logOutside with
      | .value ⟨.pair (.inj₂ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- **Program 1, `Fail` outside**: the error alone; the log state was freed by the unwind. -/
theorem failOutside_eval :
    (match eval failOutside with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **Program 1, native `log`, `Log` outside**: the error, and the log flag kept (`inj₂ ()`). -/
theorem nLogOutside_eval :
    (match eval nLogOutside with
      | .value ⟨.pair (.inj₂ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- **Program 1, native `log`, `Fail` outside**: the error alone. -/
theorem nFailOutside_eval :
    (match eval nFailOutside with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **Program 3**: the error, and no cell left. -/
theorem reborrowRaise_eval :
    (match eval reborrowRaise with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **Program 4**: three effectful observations and a close. -/
theorem tickProg_eval :
    (match eval (tickProg 3) with
      | .value ⟨.unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **Program 5**: `take 1` stops the producer (`inj₂ ()`); `take 5` lets it finish (`inj₁ ()`);
no cell left either way. -/
theorem takeProg_eval :
    (match eval (takeProg 1), eval (takeProg 5) with
      | .value ⟨.inj₂ .unit, _⟩ false, .value ⟨.inj₁ .unit, _⟩ false => true
      | _, _ => false) = true := by decide

/-- **Program 6**: the cancel answers `()`, and no cell left. -/
theorem storeCancel_eval :
    (match eval storeCancel with
      | .value ⟨.unit, _⟩ false => true
      | _ => false) = true := by decide

end BoCa.Fig16.LogRel.Core.EffPrograms

end
