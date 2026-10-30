import Core.EffCancelTyped
import Core.Run
import Core.Count
import Core.Weaken
import Core.LetCopy

/-!
# Core — the effect properties as programs  `[spec §19, §24–§27]`

Programs that exercise the properties the effect system is decided to have (§19 *Laws*). Each is a
closed term with a derivation tied to its effect context (`CDerivesAt ΞE`), read in `CDerives`
(`CDerivesAt.toCDerives`), and a run computed by `runM` from the empty memory to its answer at the
empty memory (`runM_val`). `ΞE` declares `exn : 1 ↠ 0` at the names `1` and `6`,
`wait : 1 ↠ 1` at `2` and `yield : bool ↠ 1` at `3`, all cancellable, and `log : bool ↠ 1` at `4`
and `tick : 1 ↠ 1` at `5`, linear. No abortive operation of it is unrestricted
(`noUnrExn_ΞE`), as at the effect context of every program the checker accepts.

| program | shows | answer |
|---|---|---|
| `hofTwoRows` (E1) | `hof` let-bound once (`[let-poly]`) and used at the pure row, at `exn`'s under `toResult`, and at `wait`'s under a handler that resumes `κ` at its cell; its callbacks `λ_. M` are `[λ-dead]`'s | `(tt, (inr (), tt))` |
| `sumGen` (E2d) | a consumer of a generator, let-bound once and used at `yield ⊙ ∅` and `yield ⊙ exn`; the raise passes its reinstalled handler | `(tt, inr ())` |
| `deepGen` (E4) | a deep handler: reinstalled at each resume, it catches both yields, its clause performing `tick` at each; a handler of `tick` counts them | `((), 2)` |
| `deepGenPlain` (E4) | the same deep handler under a handler of `tick` that resumes | `()` |
| `nestedLogOutside`, `nestedFailOutside` (E5) | a state-passing handler of the linear `log` and `toResult`, nested both ways: the log kept beside the error, or dropped with the handler the raise unwinds | `(inr (), tt)`, `inr ()` |
| `tunnel` (E6) | `fwrap`'s handler of `exnᵢ` passes the callback's raise of `exnₒ` to `toResult` | `inr ()` |
| `e7a`, `e7b`, `e7d` (E7) | `timeout` cancels a suspended body: the finalisers fire innermost first, and the first error is kept and re-raised at the canceller | `inr ()` |
| `e8b` (E8b) | an unwind fires a finaliser whose raise supersedes the pending one | `inl (inr ())` |
| `storedKResume`, `storedKCancel`, `storedKFin` (E9) | a clause answers a closure holding the cancellable `κ`, called after the handler has returned: it resumes `κ`, cancels it, or cancels it and its region's finaliser raises | `ff`, `tt`, `inr ()` |
| `timeoutProg` (E10) | `timeout` let-bound once: it cancels a body that waits, and passes a body's raise | `(ff, inr ())` |

The handlers are values (`hQ`, §24's `[handle]` at a value form) with one operation each
(`dAt_hQ`); a let-bound function's uses are typed each at its own row from `[let-poly]`'s premise,
the body with the function in place (`threeUses_subst`, `sumGenUses_subst`, `timeoutUses_subst`),
and that copy, the function replaced by the bound variable, is the let's body (`threeUses_unfill`,
`sumGenUses_unfill`, `timeoutUses_unfill`; `Core/LetCopy.lean`).
E5's state function and E9's closure hold a `bool` across a `[let]` at a row with `exn`, which
needs that row to have no unrestricted operation: `exn` is cancellable. The programs the backend compiles
are kernel programs (`Backend/Kernel.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Tier1Programs
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Steps hndE performE)
open BoCa.Lifetime (LifeCtx)
open BoCa.Fig16.LogRel.Core.CancelIntercept (hQ idV constC thenU raiseU performU timeoutH
  toResultH bodyF)
open BoCa.Fig16.LogRel.Core.Inversions (resumeE cancelE)

/-! ### Names, signatures and the effect context -/

/-- `bool`, `1 ⊕ 1`: `ff` is `inj₁ ()` and `tt` is `inj₂ ()`. -/
abbrev boolT : VTy := .sum .unit .unit

/-- `M V`, the argument first: `V to x. M x`. -/
def appE (M V : Expr) : Expr := .app (.lam (.app (M.shift 1 0) (.var 0))) V

/-- The effect context of the programs: `exn : 1 ↠ 0` cancellable at `1` and at `6`, `wait : 1 ↠ 1`
cancellable at `2`, `yield : bool ↠ 1` cancellable at `3`, `log : bool ↠ 1` must resume at `4`, and
`tick : 1 ↠ 1` linear at `5`. -/
def ΞE : EffCtx := fun n =>
  if n = 1 then [(.cancel, .unit, .zero)] else
  if n = 2 then [(.cancel, .unit, .unit)] else
  if n = 3 then [(.cancel, boolT, .unit)] else
  if n = 4 then [(.lin, boolT, .unit)] else
  if n = 5 then [(.lin, .unit, .unit)] else
  if n = 6 then [(.cancel, .unit, .zero)] else []

/-! ### The handlers the programs share -/

/-- The clause `op (_, k) ⇒ resume k ()`. -/
def resumeClV : Val := ⟨.lam (.letpair (.var 0) (resumeE (.var 0) .unit)), .lam⟩

/-- A handler of the name `n` at one operation of the qualifier `q`: `return x ⇒ x` and
`op (_, k) ⇒ resume k ()`. -/
def resumerH (n : UInt32) (q : Qual) : Val := hQ n q idV resumeClV

/-- `return x ⇒ λs. (x, s)`: a state-passing handler's answer clause. -/
def pairRetV : Val := ⟨.lam (.lam (.pair (.var 1) (.var 0))), .lam⟩

/-! ### Callbacks -/

/-- `λ_. return tt`. -/
def pureCbE : Expr := .lam (.inj₂ .unit)

/-- `λ_. raise exn ()`, `exn` of the name `n`. -/
def failCbE (n : UInt32) : Expr := .lam (raiseU n)

/-- `λ_. wait (); return tt`, `wait` of the name `n`. -/
def waitCbE (n : UInt32) : Expr := .lam (bindE (performU n) (.inj₂ .unit))

/-! ### E1: one function at two rows (`hof-two-rows`) -/

/-- `hof = λg. g ()`. -/
def hofE : Expr := .lam (appE (.var 0) .unit)

/-- `(f pureCb, toResult (f failCb), resumer (f waitCb))`, `f` the variable `0`. -/
def threeUses : Expr :=
  bindE (appE (.var 0) pureCbE)
    (bindE (hndE (toResultH 1 .cancel) (appE (.var 1) (failCbE 1)))
      (bindE (hndE (resumerH 2 .cancel) (appE (.var 2) (waitCbE 2)))
        (.pair (.var 2) (.pair (.var 1) (.var 0)))))

/-- **E1**: `let f = hof in (f pureCb, toResult (f failCb), resumer (f waitCb))`. -/
def hofTwoRows : Expr := bindE hofE threeUses

/-! ### E2d: a generator consumer polymorphic in the generator's other effects (`sum-gen`) -/

/-- `yield (x, k) ⇒ resume k () to r. case x of inl _ ⇒ r | inr _ ⇒ tt`. -/
def sgClV : Val :=
  ⟨.lam (.letpair (.var 0)
    (bindE (resumeE (.var 0) .unit) (.case (.var 2) (.var 1) (.inj₂ .unit)))), .lam⟩

/-- `sumGen`'s handler: `return _ ⇒ ff`, and `sgClV`. -/
def sgH : Val := hQ 3 .cancel (constC (Val.inj₁ Val.unit)) sgClV

/-- `sumGen = λgen. handle yield {…} (gen ())`. -/
def sumGenE : Expr := .lam (hndE sgH (appE (.var 0) .unit))

/-- `λ_. yield ff; yield tt`. -/
def gen1E : Expr :=
  .lam (bindE (performE (opArgE 3 0 (.inj₁ .unit))) (performE (opArgE 3 0 (.inj₂ .unit))))

/-- `λ_. yield ff; raise exn ()`. -/
def gen2E : Expr := .lam (bindE (performE (opArgE 3 0 (.inj₁ .unit))) (raiseU 1))

/-- `(s gen1, toResult (s gen2))`, `s` the variable `0`. -/
def sumGenUses : Expr :=
  bindE (appE (.var 0) gen1E)
    (bindE (hndE (toResultH 1 .cancel) (appE (.var 1) gen2E)) (.pair (.var 1) (.var 0)))

/-- **E2d**: `let s = sumGen in (s gen1, toResult (s gen2))`. -/
def sumGen : Expr := bindE sumGenE sumGenUses

/-! ### E4: a deep handler (`deep-gen`) -/

/-- `yield (_, k) ⇒ tick (); resume k ()`. -/
def tickingClV : Val :=
  ⟨.lam (.letpair (.var 0) (bindE (performU 5) (resumeE (.var 1) .unit))), .lam⟩

/-- `deepGen = handle yield {return _ ⇒ (); yield (_, k) ⇒ tick (); resume k ()} (yield tt;
yield ff)`. -/
def deepGenE : Expr :=
  hndE (hQ 3 .cancel (constC Val.unit) tickingClV)
    (bindE (performE (opArgE 3 0 (.inj₂ .unit))) (performE (opArgE 3 0 (.inj₁ .unit))))

/-- `tick (_, k) ⇒ λc. resume k () to g. g (c + 1)`: the count of ticks, a numeral. -/
def countClV : Val :=
  ⟨.lam (.letpair (.var 0)
    (.lam (bindE (resumeE (.var 1) .unit) (appE (.var 0) (.inj₂ (.var 1)))))), .lam⟩

/-- **E4**: `deepGen` under a handler of `tick` that counts, from `0`. -/
def deepGen : Expr :=
  bindE (hndE (hQ 5 .lin pairRetV countClV) deepGenE) (appE (.var 0) (num 0).1)

/-- **E4**, `deepGen` under a handler of `tick` that resumes. -/
def deepGenPlain : Expr := hndE (resumerH 5 .lin) deepGenE

/-! ### E5: nested handlers in both orders (`nested-log-outside`, `nested-fail-outside`) -/

/-- `log (b, k) ⇒ λs. resume k () to g. g b`. -/
def logClV : Val :=
  ⟨.lam (.letpair (.var 0) (.lam (bindE (resumeE (.var 1) .unit) (appE (.var 0) (.var 3))))),
    .lam⟩

/-- `withLog M = handle log {return x ⇒ λs. (x, s); log (b, k) ⇒ …} M to g. g ff`. -/
def withLogE (M : Expr) : Expr :=
  bindE (hndE (hQ 4 .lin pairRetV logClV) M) (appE (.var 0) (.inj₁ .unit))

/-- `log tt; raise exn ()`. -/
def body5E : Expr := bindE (performE (opArgE 4 0 (.inj₂ .unit))) (raiseU 1)

/-- **E5**, `withLog` outside `toResult`. -/
def nestedLogOutside : Expr := withLogE (hndE (toResultH 1 .cancel) body5E)

/-- **E5**, `toResult` outside `withLog`. -/
def nestedFailOutside : Expr := hndE (toResultH 1 .cancel) (withLogE body5E)

/-! ### E6: no accidental handling (`tunnel`) -/

/-- `fwrap = λg. handle exnᵢ {return x ⇒ x; raise _ ⇒ ff} (g ())`, `exnᵢ` of the name `6`.
-/
def fwrapE : Expr :=
  .lam (hndE (hQ 6 .cancel idV (constC (Val.inj₁ Val.unit))) (appE (.var 0) .unit))

/-- **E6**: `toResult (let f = fwrap in f (λ_. raise exnₒ ()))`, `exnₒ` of the name `1`. -/
def tunnel : Expr := hndE (toResultH 1 .cancel) (bindE fwrapE (appE (.var 0) (failCbE 1)))

/-! ### E7: abandoning a suspension (`e7a`, `e7b`, `e7d`) -/

/-- **E7a**: `timeout (body ())`, the finaliser `()`. -/
def e7a : Expr := hndE (timeoutH 2) (bodyF 2 .unit)

/-- **E7b**: `toResult (timeout (body (raise exnₒ ())))`. -/
def e7b : Expr := hndE (toResultH 1 .cancel) (hndE (timeoutH 2) (bodyF 2 (raiseU 1)))

/-- **E7d**: `toResult_a (toResult_b (timeout ((body (raise exn_a ())) then x. x unwind
raise exn_b ())))`, `exn_a` of the name `1` and `exn_b` of the name `6`. -/
def e7d : Expr :=
  hndE (toResultH 1 .cancel) (hndE (toResultH 6 .cancel)
    (hndE (timeoutH 2) (thenU (bodyF 2 (raiseU 1)) (raiseU 6))))

/-! ### E8b: unwinding through a finaliser that raises (`e8b`) -/

/-- **E8b**: `toResult_a (toResult_b ((raise exn_a ()) then x. x unwind raise exn_b ()))`. -/
def e8b : Expr := hndE (toResultH 1 .cancel) (hndE (toResultH 6 .cancel) (thenU (raiseU 1) (raiseU 6)))

/-! ### E9: a stored continuation (`stored-k-resume`, `stored-k-cancel`, `stored-k-fin`) -/

/-- `yield (x, k) ⇒ λc. case c of inl _ ⇒ cancel k; x | inr _ ⇒ resume k () to g.
g (inr ())`: the clause answers a closure holding `κ`. -/
def stashClV : Val :=
  ⟨.lam (.letpair (.var 0) (.lam (.case (.var 0)
    (bindE (cancelE (.var 2)) (.var 4))
    (bindE (resumeE (.var 2) .unit) (appE (.var 0) (.inj₂ .unit)))))), .lam⟩

/-- `stash`'s handler: `return _ ⇒ λc. ff`, and `stashClV`. -/
def stashH : Val := hQ 3 .cancel (constC (Val.lam (.inj₁ .unit))) stashClV

/-- `yield tt; yield ff`. -/
def gen9E : Expr :=
  bindE (performE (opArgE 3 0 (.inj₂ .unit))) (performE (opArgE 3 0 (.inj₁ .unit)))

/-- `stash M to g. g c`: the stored closure called after `stash` has returned. -/
def storedK (M c : Expr) : Expr := bindE (hndE stashH M) (appE (.var 0) c)

/-- **E9a**: the stored `κ` resumed. -/
def storedKResume : Expr := storedK gen9E (.inj₂ .unit)

/-- **E9b**: the stored `κ` cancelled. -/
def storedKCancel : Expr := storedK gen9E (.inj₁ .unit)

/-- **E9c**: the stored `κ` cancelled, its region's finaliser raising `exnₒ`, handled outside. -/
def storedKFin : Expr := hndE (toResultH 1 .cancel) (storedK (thenU gen9E (raiseU 1)) (.inj₁ .unit))

/-! ### E10: `timeout`, one function at two rows (`timeout`) -/

/-- `wait (_, k) ⇒ cancel k; return ff`. -/
def tmClV : Val := ⟨.lam (.letpair (.var 0) (bindE (cancelE (.var 0)) (.inj₁ .unit))), .lam⟩

/-- `timeout = λb. handle wait {return x ⇒ x; wait (_, k) ⇒ cancel k; return ff} (b ())`. -/
def timeoutRE : Expr := .lam (hndE (hQ 2 .cancel idV tmClV) (appE (.var 0) .unit))

/-- `(t waitCb, toResult (t failCb))`, `t` the variable `0`. -/
def timeoutUses : Expr :=
  bindE (appE (.var 0) (waitCbE 2))
    (bindE (hndE (toResultH 1 .cancel) (appE (.var 1) (failCbE 1))) (.pair (.var 1) (.var 0)))

/-- **E10**: `let t = timeout in (t waitCb, toResult (t failCb))`. -/
def timeoutProg : Expr := bindE timeoutRE timeoutUses

/-! ### Weakening a tied derivation -/

/-- **Weakening** of a tied derivation by consumed slots at the end, as `CDerives.append_dead`. -/
theorem _root_.BoCa.Fig16.LogRel.Core.CDerivesAt.append_dead {Ξ : EffCtx} {Γ' : Ctx VTy}
    (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : CDerivesAt Ξ Δ (Γ ++ Γ') e j := by
  induction h with
  | var hs => exact .var (soloP_append h' hs)
  | unitI hd => exact .unitI (deadP_append h' hd)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (splitP_append h' hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind (splitP_append h' hs) ihM ihN
  | force hs => exact .force (soloP_append h' hs)
  | lam _ ih => exact .lam ih
  | lamDead _ ih => exact .lamDead ih
  | app hs _ hx ih => exact .app (splitP_append h' hs) ih (soloP_append h' hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (splitP_append h' hs) ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE (splitP_append h' hs) ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact .sumE (splitP_append h' hs) ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (splitP_append h' hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx (live_append h' hΓx) ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih => exact .bangThunkF (banged_append h' hp) ih
  | bangThunkV hp hC _ ih => exact .bangThunkV (banged_append h' hp) hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang (deadP_append h' hΓ)
  | forgetBang hΓ => exact .forgetBang (deadP_append h' hΓ)
  | boxI _ hΓ ih => exact .boxI ih (ctxOutlives_append h' hΓ)
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc (deadP_append h' hΓ)
  | free hΓ => exact .free (deadP_append h' hΓ)
  | swap hΓ => exact .swap (deadP_append h' hΓ)
  | copy hΓ => exact .copy (deadP_append h' hΓ)
  | forgetImm hΓ => exact .forgetImm (deadP_append h' hΓ)
  | forgetMut hΓ => exact .forgetMut (deadP_append h' hΓ)
  | forgetUnk hΓ => exact .forgetUnk (deadP_append h' hΓ)
  | lit c hΓ => exact .lit c (deadP_append h' hΓ)
  | hostOp op hΓ => exact .hostOp op (deadP_append h' hΓ)
  | arrNew A hΓ => exact .arrNew A (deadP_append h' hΓ)
  | arrFree A hΓ => exact .arrFree A (deadP_append h' hΓ)
  | arrSize A hΓ => exact .arrSize A (deadP_append h' hΓ)
  | arrReplace A hΓ => exact .arrReplace A (deadP_append h' hΓ)
  | arrLen a A hΓ => exact .arrLen a A (deadP_append h' hΓ)
  | arrGet a A hΓ => exact .arrGet a A (deadP_append h' hΓ)
  | arrCopy a A hΓ => exact .arrCopy a A (deadP_append h' hΓ)
  | arrForget a A hΓ => exact .arrForget a A (deadP_append h' hΓ)
  | countFold S hΓ => exact .countFold S (deadP_append h' hΓ)
  | countTry S E hΓ => exact .countTry S E (deadP_append h' hΓ)
  | boundedFix A C hΓ => exact .boundedFix A C (deadP_append h' hΓ)
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ =>
      exact .sliceBorrowM x (deadP_append h' hΓ) hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ =>
      exact .sliceBorrowI x (deadP_append h' hΓ) hsc hA hB hf₁ hf₂
  | sliceGetM a A hΓ => exact .sliceGetM a A (deadP_append h' hΓ)
  | sliceLenM a A hΓ => exact .sliceLenM a A (deadP_append h' hΓ)
  | sliceSplitI a A hΓ => exact .sliceSplitI a A (deadP_append h' hΓ)
  | sliceSplitM a A hΓ => exact .sliceSplitM a A (deadP_append h' hΓ)
  | sliceEmptyI a A hΓ => exact .sliceEmptyI a A (deadP_append h' hΓ)
  | sliceEmptyM a A hΓ => exact .sliceEmptyM a A (deadP_append h' hΓ)
  | arrEmpty A hΓ => exact .arrEmpty A (deadP_append h' hΓ)
  | sliceReplaceM a A hΓ => exact .sliceReplaceM a A (deadP_append h' hΓ)
  | sliceSwapM a A hΓ => exact .sliceSwapM a A (deadP_append h' hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x (deadP_append h' hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ =>
      exact .withbor2 x (deadP_append h' hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x (deadP_append h' hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x (deadP_append h' hΓ) hx hf₁ hf₂
  | withswap hΓ => exact .withswap (deadP_append h' hΓ)
  | withbor1U x hΓ hx hsc hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor1U x (deadP_append h' hΓ) hx hsc hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ hx hside hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor2U x (deadP_append h' hΓ) hx hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ hx hf₁ hf₂ hS hdc _ ihd =>
      exact .withbor3U x (deadP_append h' hΓ) hx hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ hx hf₁ hf₂ hS => exact .withloadU x (deadP_append h' hΓ) hx hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact .sliceBorrowMU x (deadP_append h' hΓ) hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact .sliceBorrowIU x (deadP_append h' hΓ) hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact .lolliE (splitP_append h' hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      exact .foldImm F y c R (deadP_append h' hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R (deadP_append h' hΓ) hF hG
  | foldOwnG B₀ Rs hΓ hB => exact .foldOwnG B₀ Rs (deadP_append h' hΓ) hB
  | foldReuse F R hΓ hF hG => exact .foldReuse F R (deadP_append h' hΓ) hF hG
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | unfoldN C S hC hΓ => exact .unfoldN C S hC (deadP_append h' hΓ)
  | effSub hle _ ih => exact .effSub hle ih
  | effPerform hAt hf hna _ ih => exact .effPerform hAt hf hna ih
  | effRaise hAt hf ha hd _ ih => exact .effRaise hAt hf ha hd ih
  | effLet hs hW hU _ _ ihM ihN =>
      exact .effLet (splitP_append h' hs)
        (fun hw => live_append (P := fun s => s.ty.OwnFree) h' (hW hw))
        (fun hu => banged_append h' (hU hu)) ihM ihN
  | effThen hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact .effThen (splitP_append h' hs) hNZ hUq (fun hu => banged_append h' (hU hu))
        hMS hDS hfin hP hSD ihM ihN ihD
  | effHandleV hAt hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact .effHandleV hAt (splitP_append h' hs) (deadP_append h' hd) hH.append ihc hn0 hnS hlen
        hdv ihe
  | effHandleVB hAt hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact .effHandleVB hAt (splitP_append h' hs) (deadP_append h' hd) hH.append ihc hn0 hnS hlen
        hdv ihe (ctxOutlives_append h' hΓd) hSd
  | effHandleT hAt hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact .effHandleT hAt (splitP_append h' hs) (deadP_append h' hd) hHr.append hHc.append ihc
        hn0 hnd hnS hlen hSN hLin ihe
  | effHandleL hAt hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact .effHandleL hAt (splitP_append h' hs) (deadP_append h' hd) hHr.append hHw.append
        hHn.append ihc hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin ihe
  | iterate S St B R hAt hS hΓ => exact .iterate S St B R hAt hS (deadP_append h' hΓ)
  | divFuel S A hAt hS hΓ => exact .divFuel S A hAt hS (deadP_append h' hΓ)
  | reify S B R res hAt hS hcl hres hΓ _ => exact .reify S B R res hAt hS hcl hres (deadP_append h' hΓ)
  | letPoly b hcl hV _ _ ihN => exact .letPoly b hcl hV ihN

/-! ### Typing: calls, callbacks and one-operation handlers -/

section Kernel
variable {Ξ : EffCtx}

/-- A tied derivation of a term at the empty context, read at a consumed context. -/
theorem dAt_dead {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ [] e j) : CDerivesAt Ξ Δ Γ e j :=
  h.append_dead hΓ

/-- **A closed function applied**, `W V`: `V to x. W x`, `W` typed at the empty context. -/
theorem dAt_appE {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {W V : Expr} {T : VTy} {C : CTy}
    (hWc : closedAt 0 W = true) (hW : CDerivesAt Ξ Δ [] W (.comp (.arr T C)))
    (hV : CDerivesAt Ξ Δ Γ V (.val T)) : CDerivesAt Ξ Δ Γ (appE W V) (.comp C) := by
  unfold appE
  rw [shift_closedAt W 1 hWc (Nat.zero_le _)]
  exact .bind (deadSplit hΓ) (.ret hV)
    (.app (.right (deadSplit hΓ)) (hW.append_dead (Γ' := ⟨T, false⟩ :: Γ) (.cons hΓ))
      (.here hΓ.toP))

/-- **A function in the slot `0` applied**, `f V`, `V` at the rest of the context. -/
theorem dAt_callVar {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {T : VTy} {C : CTy} {V : Expr}
    (hV : CDerivesAt Ξ Δ (⟨.thunk (.arr T C), false⟩ :: Γ) V (.val T)) :
    CDerivesAt Ξ Δ (⟨.thunk (.arr T C), true⟩ :: Γ) (appE (.var 0) V) (.comp C) :=
  .bind (.right (deadSplit hΓ)) (.ret hV)
    (.app (.right (.left (deadSplit hΓ))) (.force (C := .arr T C) (.there (.here hΓ.toP)))
      (.here (.cons hΓ.toP)))

/-- **A callback `λ_. M`** at `U(1 ⊸ F_Σ B)`, `M` typed at the empty context (`[λ-dead]`). -/
theorem dAt_cb {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {M : Expr} {S : Row} {B : VTy}
    (h : CDerivesAt Ξ Δ [] M (.comp (CTy.effOf S B))) :
    CDerivesAt Ξ Δ Γ (.lam M) (.val (.thunk (.arr .unit (CTy.effOf S B)))) :=
  .thunkV rfl (.lamDead (h.append_dead (Γ' := ⟨.unit, false⟩ :: Γ) (.cons hΓ)))

/-- **A handler of one operation**, `hnd (n, (q, (h_ret, (c, ())))) M` at the row `S`: the
handler value at the consumed part `Γ₁` of the context, `M` at `n`'s row of cancel row `F` before
`S`. -/
theorem dAt_hQ {Δ : LifeCtx} {Γ Γ₁ : Ctx VTy} (hs : Ctx.SplitP Γ Γ₁ Γ)
    (hΓ₁ : Ctx.Dead Γ₁) {n : UInt32} {q : Qual} {A B : VTy} (hn : Ξ n = [(q, A, B)])
    (hn0 : n ≠ 0) {S : Row} (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ n) {F : CTy} {X R : VTy}
    {hr c : Val} {M : Expr} (hhr : CDerivesAt Ξ Δ [] (.val hr) (.val (retTy S X R)))
    (hc : CDerivesAt Ξ Δ [] (.val c) (.val (clauseTy S R (q, A, B) F)))
    (hM : CDerivesAt Ξ Δ Γ M
      (.comp (CTy.effOf (Row.ofEff n [(q, A, B)] 0 (fun _ => F) ++ S) X)))
    (hΞ : Ξ divEff = [] := by first | rfl | decide) :
    CDerivesAt Ξ Δ Γ (hndE (hQ n q hr c) M) (.comp (CTy.effOf S R)) := by
  show CDerivesAt Ξ Δ Γ (hndExpr n [q] (.pair (.val hr) (.pair (.val c) (.val Val.unit))) M) _
  have hAt := rowAt_ofEff_fs (fs' := fun _ => F) (rowAt_ofEff_append hn hn0 (by simp) hS)
  exact .effHandleV (E := [(q, A, B)]) (fs := fun _ => F) hAt hs hΓ₁.toP
    (.pair (.val _) (.pair (.val _) (.val _)))
    ((CDerivesAt.tensorI .nil hhr (.tensorI .nil hc (.unitI .nil))).append_dead hΓ₁)
    hn0 hnS (by simp) (Row.divB_of_rowAt hAt hΞ) hM

end Kernel

/-! ### The effect context's names -/

theorem ΞE_1 : ΞE 1 = [(.cancel, .unit, .zero)] := rfl
theorem ΞE_2 : ΞE 2 = [(.cancel, .unit, .unit)] := rfl
theorem ΞE_3 : ΞE 3 = [(.cancel, boolT, .unit)] := rfl
theorem ΞE_4 : ΞE 4 = [(.lin, boolT, .unit)] := rfl
theorem ΞE_5 : ΞE 5 = [(.lin, .unit, .unit)] := rfl
theorem ΞE_6 : ΞE 6 = [(.cancel, .unit, .zero)] := rfl

/-- **`ΞE` has no unrestricted abortive operation** (decision 63's restriction), as the effect
context of every program the checker accepts has (`checkProgram_tiedAt`). -/
theorem noUnrExn_ΞE : ΞE.NoUnrExn := by
  intro n p hp hq
  simp only [ΞE] at hp
  split_ifs at hp <;> simp_all

/-! ### E7 and E8b: finalisers that raise, at §27's cancel rows -/

section E7
open BoCa.Fig16.LogRel.Core.CancelIntercept (exnRow waitRow finExn find_ofEff_one find_wait
  rowLe_append_right rowLe_dup rowLe_ofEff_cons rowLe_of_find_eq thenLe_exn dAt_timeout
  dAt_toResult dAt_raiseU dAt_bodyF)

theorem rowAt_exn1 : RowAt ΞE (exnRow 1 .cancel ++ []) :=
  rowAt_ofEff_append ΞE_1 (by decide) (by simp) (rowAt_nil ΞE)

/-- **E7a is typed**: the finaliser returns, and `wait`'s cancel row is empty. -/
theorem dAt_e7a {Δ : LifeCtx} : CDerivesAt ΞE Δ [] e7a (.comp (.ret (.sum boolT .unit))) :=
  dAt_timeout ΞE_2 (by decide) (S := []) (rowAt_nil ΞE) (by simp) (X := boolT)
    (F := .ret .unit) rfl (RowLe.refl [])
    (dAt_bodyF ΞE_2 (by decide) (S := []) (SD := []) (F := .ret .unit)
      (by intro o ho; simp [Row.ofEff] at ho; subst ho; decide) (by simp [Row.Uniq, Row.ofEff])
      (RowLe.nil _) (ThenLe.nil _) (.ret (.unitI (.cons .nil))))

/-- **E7b is typed**: `wait`'s cancel row holds the finaliser's raise of `exnₒ`, whose handler is
live outside the `timeout`. -/
theorem dAt_e7b {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] e7b (.comp (.ret (.sum (.sum boolT .unit) .unit))) := by
  have hn : ∀ o ∈ exnRow 1 .cancel ++ [], o.n ≠ 2 := by
    intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  refine dAt_toResult ΞE_1 (by decide) (by decide) (S := []) (rowAt_nil ΞE) (by simp) ?_
  refine dAt_timeout ΞE_2 (by decide) rowAt_exn1 hn (X := boolT) (F := finExn 1 .cancel) rfl ?_ ?_
  · rw [CTy.rowOf_effOf, List.append_nil]
    exact rowLe_dup _
  · refine dAt_bodyF ΞE_2 (by decide) (S := exnRow 1 .cancel ++ []) (SD := exnRow 1 .cancel)
      ?_ (by simp [Row.Uniq, Row.ofEff]) ?_ (thenLe_exn 1 .cancel)
      (dAt_raiseU (.cons .nil) ΞE_1 (by decide) (by decide) .unit)
    · intro o ho
      simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at ho
      rcases ho with rfl | rfl <;> decide
    · rw [List.append_nil]
      exact rowLe_ofEff_cons _ _ (by rw [← List.append_nil (exnRow 1 .cancel)]; exact hn)

/-- `exn` at the name `n` is not capturable. -/
theorem not_capB_exnRow {n : UInt32} {o : OpSig} (ho : o ∈ exnRow n .cancel) :
    capB o.q o.B = false := by
  simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho
  rfl

/-- **E8b is typed**: the `[then]` at `exn_b`'s row before `exn_a`'s, its finaliser at `exn_b`'s
row (`Σ_D ≤ Σ`), handled by the inner `toResult`. -/
theorem dAt_e8b {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] e8b (.comp (.ret (.sum (.sum .unit .unit) .unit))) := by
  have hn : ∀ o ∈ exnRow 1 .cancel ++ [], o.n ≠ 6 := by
    intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  refine dAt_toResult ΞE_1 (by decide) (by decide) (S := []) (rowAt_nil ΞE) (by simp) ?_
  refine dAt_toResult ΞE_6 (by decide) (by decide) (S := exnRow 1 .cancel ++ []) rowAt_exn1 hn ?_
  show CDerivesAt ΞE Δ [] (thenE (.var 0) (raiseU 6) (raiseU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := exnRow 1 .cancel)
    (SD := exnRow 6 .cancel) .nil ?_ (by simp [Row.Uniq, Row.ofEff])
    (fun _ => fun _ h => absurd h List.not_mem_nil) ?_ (rowLe_append_right _ _) ?_ ?_ rfl
    (dAt_raiseU .nil ΞE_1 (by decide) (by decide) .unit)
    (.effSub (RowLe.nil _) (.ret (.var (.here .nil))))
    (dAt_raiseU (.cons .nil) ΞE_6 (by decide) (by decide) .unit)
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · exact (rowLe_append_right _ []).trans (rowLe_ofEff_cons _ _ hn)
  · intro n i o o' hf _ hc
    rw [not_capB_exnRow (Row.find_mem hf).1] at hc
    cases hc
  · intro _ o ho
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact ⟨fun _ => rfl, fun h => by simp [capB, VTy.isZero] at h⟩

/-- The cancel row of `wait` in E7d: the finalisers raise `exn_a` and `exn_b`. -/
abbrev finExn2 : CTy := CTy.effOf (exnRow 1 .cancel ++ exnRow 6 .cancel) .unit

/-- `exn_b`'s row before `exn_a`'s: the row of E7d's `timeout`. -/
abbrev rowBA : Row := exnRow 6 .cancel ++ (exnRow 1 .cancel ++ [])

/-- A row whose first entry's cancel row grows is below the row with the larger one. -/
theorem rowLe_cons_fin {n i : UInt32} {q : Qual} {A B : VTy} {F F' : CTy} (hF : FinLe F F')
    (T : Row) : RowLe (⟨n, i, q, A, B, F⟩ :: T) (⟨n, i, q, A, B, F'⟩ :: T) := by
  intro m j o hf
  unfold Row.find at hf ⊢
  rw [List.find?_cons] at hf ⊢
  by_cases hk : m = n ∧ j = i
  · rw [decide_eq_true hk] at hf ⊢
    cases hf
    exact ⟨_, rfl, OpSig.Sig.refl _, fun _ => hF⟩
  · rw [decide_eq_false hk] at hf ⊢
    exact ⟨o, hf, OpSig.LeF.refl o⟩

/-- **`{exn_a} ⋈ {exn_b} ≤ {exn_a, exn_b}`**: the outer `[then]`'s finaliser adds its raise to
the cancel row of `wait`. -/
theorem thenLe_finExn2 : ThenLe (finExn 1 .cancel) (exnRow 6 .cancel) finExn2 := by
  rw [ThenLe]
  refine .inr ⟨rfl, fun n i o hf => ?_, fun n i o hf => ?_⟩
  · rw [CTy.rowOf_effOf] at hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    exact ⟨_, by simp [CTy.rowOf_effOf, Row.ofEff, Row.find], OpSig.Sig.refl _,
      fun h => by simp [capB, VTy.isZero] at h⟩
  · obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    exact ⟨_, by simp [CTy.rowOf_effOf, Row.ofEff, Row.find], OpSig.Sig.refl _,
      fun h => by simp [capB, VTy.isZero] at h⟩

/-- **E7d is typed**: the inner `[then]` puts `exn_a` in `wait`'s cancel row and the outer one adds
`exn_b`; both are handled outside the `timeout`. -/
theorem dAt_e7d {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] e7d (.comp (.ret (.sum (.sum (.sum boolT .unit) .unit) .unit))) := by
  have hn6 : ∀ o ∈ exnRow 1 .cancel ++ [], o.n ≠ 6 := by
    intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  have hnBA : ∀ o ∈ rowBA, o.n ≠ 2 := by
    intro o ho
    simp only [rowBA, Row.ofEff, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  have hNZ : ∀ F : CTy, (waitRow 2 F ++ rowBA).NZ := by
    intro F o ho
    simp only [rowBA, Row.ofEff, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> simp
  have hUq : ∀ F : CTy, (waitRow 2 F ++ rowBA).Uniq := by
    intro F; simp [rowBA, Row.Uniq, Row.ofEff]
  have hSBA : RowAt ΞE rowBA := rowAt_ofEff_append ΞE_6 (by decide) (by simp) rowAt_exn1
  refine dAt_toResult ΞE_1 (by decide) (by decide) (S := []) (rowAt_nil ΞE) (by simp) ?_
  refine dAt_toResult ΞE_6 (by decide) (by decide) (S := exnRow 1 .cancel ++ []) rowAt_exn1 hn6 ?_
  refine dAt_timeout ΞE_2 (by decide) hSBA hnBA (X := boolT) (F := finExn2) rfl ?_ ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [CTy.rowOf_effOf] at ho
    simp only [rowBA, Row.ofEff, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl <;>
      exact ⟨_, by simp [Row.ofEff, Row.find], OpSig.LeF.refl _⟩
  -- the outer `[then]`, its finaliser `raise exn_b`
  show CDerivesAt ΞE Δ [] (thenE (.var 0) (raiseU 6) (bodyF 2 (raiseU 1))) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := boolT)
    (SM := waitRow 2 (finExn 1 .cancel) ++ rowBA) (SD := exnRow 6 .cancel) .nil (hNZ _) (hUq _)
    (fun _ => fun _ h => absurd h List.not_mem_nil) ?_ ?_ ?_ ?_ rfl ?_
    (.effSub (RowLe.nil _) (.ret (.var (.here .nil))))
    (dAt_raiseU (.cons .nil) ΞE_6 (by decide) (by decide) .unit)
  · -- `M`'s row is below the `[then]`'s: `wait`'s cancel row grows to hold `exn_b`
    show RowLe (⟨2, UInt32.ofNat 0, .cancel, .unit, .unit, finExn 1 .cancel⟩ :: rowBA)
      (⟨2, UInt32.ofNat 0, .cancel, .unit, .unit, finExn2⟩ :: rowBA)
    refine rowLe_cons_fin
      ((finLe_iff _ _).mpr (.inr ⟨rfl, RowLe.of_find fun n i o hf => ?_⟩)) rowBA
    rw [CTy.rowOf_effOf] at hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    simp [CTy.rowOf_effOf, Row.ofEff, Row.find]
  · -- the finaliser's row is below the `[then]`'s
    refine RowLe.of_find fun n i o hf => ?_
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    simp [Row.ofEff, Row.find]
  · -- `F ⋈ Σ_D ≤ Σ(wait).fin`
    intro n i o o' hf hf' hc
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [rowBA, Row.ofEff, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · have h' : Row.find (waitRow 2 finExn2 ++ rowBA) 2 0 = some o' := hf'
      rw [find_wait] at h'
      cases h'
      exact thenLe_finExn2
    · exact absurd hc (by simp [capB, VTy.isZero])
    · exact absurd hc (by simp [capB, VTy.isZero])
  · -- the finaliser's row has no unrestricted operation at any depth
    rintro ⟨o, ho, h⟩
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    simp [capB, VTy.isZero] at h
  · -- the inner `[then]`: `body (raise exn_a ())`
    refine dAt_bodyF ΞE_2 (by decide) (S := rowBA) (SD := exnRow 1 .cancel) (F := finExn 1 .cancel)
      (hNZ _) (hUq _) ?_ (thenLe_exn 1 .cancel)
      (dAt_raiseU (.cons .nil) ΞE_1 (by decide) (by decide) .unit)
    refine RowLe.of_find fun n i o hf => ?_
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    simp [rowBA, Row.ofEff, Row.find]

end E7

/-! ### Clauses the programs share -/

section Clauses
variable {Ξ : EffCtx}

/-- `return x ⇒ λs. (x, s)` at `!U(A ⊸ F_Σ U(X ⊸ F_Σ (A ⊗ X)))`. -/
theorem dAt_pairRet {Δ : LifeCtx} (S : Row) (A X : VTy) :
    CDerivesAt Ξ Δ [] (.val pairRetV)
      (.val (retTy S A (.thunk (.arr X (CTy.effOf S (.tensor A X)))))) :=
  .bangThunkV (dead_noLive .nil) rfl (.lam (.effSub (RowLe.nil S) (.ret (.thunkV rfl (.lam
    (.effSub (RowLe.nil S) (.ret (.tensorI (.right (.left .nil)) (.var (.there (.here .nil)))
      (.var (.here (.cons .nil)))))))))))

/-- `k (inj₁ ()) y`: a must-resume or cancellable `k` at the slot `1` resumed at `y` at the slot `0`. -/
theorem dAt_kResume {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {R B : VTy}
    {q : Qual} (hq : q ≠ .unr) :
    CDerivesAt Ξ Δ (⟨B, true⟩ :: ⟨kTy S R q B, true⟩ :: Γ)
      (.app (.app (.var 1) (.inj₁ .unit)) (.var 0)) (.comp (CTy.effOf S R)) := by
  cases q with
  | lin =>
      exact .app (.right (.left (deadSplit hΓ)))
        (.proj₁ (.force (C := .amp (.arr B (CTy.effOf S R)) .top) (.there (.here hΓ.toP))))
        (.here (.cons hΓ.toP))
  | cancel =>
      exact .app (.right (.left (deadSplit hΓ)))
        (.proj₁ (.force (C := .amp (.arr B (CTy.effOf S R)) (CTy.effOf S .unit))
          (.there (.here hΓ.toP))))
        (.here (.cons hΓ.toP))
  | unr => exact absurd rfl hq

/-- **The clause `op (_, k) ⇒ resume k ()`** at a resuming must-resume or cancellable operation `A ↠ 1`,
`A` persistent (the argument is dropped). -/
theorem dAt_resumeCl {Δ : LifeCtx} (S : Row) (R : VTy) {q : Qual} {A : VTy} (hq : q ≠ .unr)
    (hA : A.Persistent) :
    CDerivesAt Ξ Δ [] (.val resumeClV) (.val (clauseTy S R (q, A, .unit))) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive .nil) rfl (.lam (.tensorE (.left .nil) (.var (.here .nil)) ?_))
  refine .bind (.right (.left (.dead .nil))) (.ret (.unitI (.cons (.drop hA (.cons .nil))))) ?_
  exact dAt_kResume (Γ := [⟨A, false⟩, ⟨.tensor A (kTy S R q .unit), false⟩])
    (.cons (.cons .nil)) hq

end Clauses

/-! ### E6: no accidental handling -/

section E6
open BoCa.Fig16.LogRel.Core.CancelIntercept (exnRow rowLe_ofEff_cons rowLe_append_right
  dAt_toResult dAt_raiseU clauseTy_abortive d_idV d_constC_raise)

/-- **`fwrap` at the row `r`**, `r` without `exnᵢ`: its handler at `r`, the callback's row `r`
read below the handled row. -/
theorem dAt_fwrap {Δ : LifeCtx} {r : Row} (hr : RowAt ΞE r) (hnr : ∀ o ∈ r, o.n ≠ 6) :
    CDerivesAt ΞE Δ [] fwrapE
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf r boolT))) (CTy.effOf r boolT))) := by
  refine .lam (dAt_hQ (.right .nil) (.cons .nil) ΞE_6 (by decide) hr hnr (F := .ret .unit)
    (X := boolT) (CDerivesAt.ofEffFree (d_idV r boolT) rfl) ?_ ?_)
  · rw [clauseTy_abortive (by decide)]
    exact CDerivesAt.ofEffFree (d_constC_raise r (.sumI₁ (.unitI (.cons .nil)))) rfl
  · exact .effSub (rowLe_ofEff_cons _ _ hnr) (dAt_callVar .nil (.unitI (.cons .nil)))

/-- **E6 is typed**: `fwrap` let-bound and called at the row of `exnₒ`, which `toResult`
handles. -/
theorem dAt_tunnel {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] tunnel (.comp (.ret (.sum boolT .unit))) := by
  have hn6 : ∀ o ∈ exnRow 1 .cancel ++ [], o.n ≠ 6 := by
    intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  refine dAt_toResult ΞE_1 (by decide) (by decide) (S := []) (rowAt_nil ΞE) (by simp) ?_
  refine .bind .nil (.ret (.thunkV rfl (dAt_fwrap rowAt_exn1 hn6))) ?_
  exact dAt_callVar .nil (dAt_cb (.cons .nil)
    (.effSub (rowLe_append_right _ _) (dAt_raiseU .nil ΞE_1 (by decide) (by decide) boolT)))

end E6

/-! ### E5: nested handlers in both orders -/

section E5
open BoCa.Fig16.LogRel.Core.CancelIntercept (exnRow rowLe_ofEff_cons rowLe_append_right
  dAt_toResult dAt_raiseU)

/-- `withLog`'s answer at the row `S`: the state function `U(bool ⊸ F_Σ (A ⊗ bool))`. -/
abbrev logR (S : Row) (A : VTy) : VTy := .thunk (.arr boolT (CTy.effOf S (.tensor A boolT)))

/-- `log`'s row. -/
abbrev logRow : Row := Row.ofEff 4 [(.lin, boolT, .unit)] 0

/-- **`log (b, k) ⇒ λs. resume k () to g. g b`** at the row `S`: the state function holds the
linear `k` and `b`; its `[let]` holds `b` across the resume, so `S` has no `unr` operation. -/
theorem dAt_logCl {Δ : LifeCtx} (S : Row) (A : VTy) (hU : ¬ S.Unr) :
    CDerivesAt ΞE Δ [] (.val logClV) (.val (clauseTy S (logR S A) (.lin, boolT, .unit))) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive .nil) rfl (.lam (.tensorE (.left .nil) (.var (.here .nil)) ?_))
  refine .effSub (RowLe.nil S) (.ret (.thunkV rfl (.lam ?_)))
  refine .effLet (A := logR S A) (.left (.left (.right (.dead .nil)))) (fun _ => ?_)
    (fun h => absurd h hU) ?_ ?_
  · intro s hs hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · cases hl
    · cases hl
    · exact .sum .unit .unit
    · cases hl
  · refine .bind (.left (.right (.dead (.dead .nil))))
      (.ret (.unitI (.drop rfl (.cons (.cons (.cons .nil)))))) ?_
    exact .app (.right (.dead (.left (.dead (.dead .nil)))))
      (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S (logR S A))) .top)
        (.there (.there (.here (.cons (.cons .nil)))))))
      (.here (.cons (.cons (.cons (.cons .nil)))))
  · exact .bind (.right (.dead (.dead (.left (.dead .nil)))))
      (.ret (.var (.there (.there (.there (.here (.cons .nil)))))))
      (.app (.right (.left (.dead (.dead (.dead (.dead .nil))))))
        (.force (C := .arr boolT (CTy.effOf S (.tensor A boolT)))
          (.there (.here (.cons (.cons (.cons (.cons .nil)))))))
        (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))

/-- **`withLog M` at the row `S`**, `M` at `log`'s row before `S`. -/
theorem dAt_withLog {Δ : LifeCtx} {S : Row} (hS : RowAt ΞE S) (hnS : ∀ o ∈ S, o.n ≠ 4)
    (hU : ¬ S.Unr) {A : VTy} {M : Expr}
    (hM : CDerivesAt ΞE Δ [] M (.comp (CTy.effOf (logRow ++ S) A))) :
    CDerivesAt ΞE Δ [] (withLogE M) (.comp (CTy.effOf S (.tensor A boolT))) :=
  .effLet .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil)
    (dAt_hQ .nil .nil ΞE_4 (by decide) hS hnS (F := .ret .unit) (dAt_pairRet S A boolT)
      (dAt_logCl S A hU) hM)
    (dAt_callVar .nil (.sumI₁ (.unitI (.cons .nil))))

/-- `log tt; raise exn ()` at a row that finds `log` and holds `exn`. -/
theorem dAt_body5 {Δ : LifeCtx} {T : Row} (hT : RowAt ΞE T)
    (hf : Row.find T 4 0 = some ⟨4, 0, .lin, boolT, .unit, .ret .unit⟩)
    (hE : RowLe (exnRow 1 .cancel) T) :
    CDerivesAt ΞE Δ [] body5E (.comp (CTy.effOf T .unit)) :=
  .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil)
    (.effPerform (o := ⟨4, 0, .lin, boolT, .unit, .ret .unit⟩) hT hf rfl
      (.sumI₂ (.unitI .nil)))
    (.effSub hE (dAt_raiseU (.drop rfl .nil) ΞE_1 (by decide) (by decide) .unit))

theorem rowAt_log : RowAt ΞE (logRow ++ []) :=
  rowAt_ofEff_append ΞE_4 (by decide) (by simp) (rowAt_nil ΞE)

/-- **E5, `withLog` outside `toResult`, is typed** at the pure row. -/
theorem dAt_nestedLogOutside {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] nestedLogOutside (.comp (.ret (.tensor (.sum .unit .unit) boolT))) := by
  have hn : ∀ o ∈ logRow ++ [], o.n ≠ 1 := by
    intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  refine dAt_withLog (S := []) (rowAt_nil ΞE) (by simp)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil)
    (dAt_toResult ΞE_1 (by decide) (by decide) (S := logRow ++ []) rowAt_log hn ?_)
  exact dAt_body5 (rowAt_ofEff_append ΞE_1 (by decide) (by simp) rowAt_log)
    (by simp [Row.ofEff, Row.find]) (rowLe_append_right _ _)

/-- **E5, `toResult` outside `withLog`, is typed** at the pure row: `withLog` at `exn`'s row,
`exn` cancellable. -/
theorem dAt_nestedFailOutside {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] nestedFailOutside (.comp (.ret (.sum (.tensor .unit boolT) .unit))) := by
  have hn : ∀ o ∈ exnRow 1 .cancel ++ [], o.n ≠ 4 := by
    intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  refine dAt_toResult ΞE_1 (by decide) (by decide) (S := []) (rowAt_nil ΞE) (by simp) ?_
  refine dAt_withLog rowAt_exn1 hn ?_ ?_
  · rintro ⟨o, ho, hq⟩
    simp [Row.ofEff] at ho
    subst ho
    cases hq
  · exact dAt_body5 (rowAt_ofEff_append ΞE_4 (by decide) (by simp) rowAt_exn1)
      (by simp [Row.ofEff, Row.find])
      ((rowLe_append_right _ []).trans (rowLe_ofEff_cons _ _ hn))

end E5

/-! ### E9: a stored continuation -/

section E9
open BoCa.Fig16.LogRel.Core.CancelIntercept (exnRow finExn find_ofEff_one rowLe_ofEff_cons
  rowLe_append_right rowLe_dup thenLe_exn dAt_toResult dAt_raiseU)

/-- `stash`'s answer at the row `S`: a closure `U(bool ⊸ F_Σ bool)`. -/
abbrev stashR (S : Row) : VTy := .thunk (.arr boolT (CTy.effOf S boolT))

/-- `yield`'s row. -/
abbrev yieldRow : Row := Row.ofEff 3 [(.cancel, boolT, .unit)] 0

/-- `return _ ⇒ λc. ff` at the row `S`. -/
theorem dAt_stashRet {Δ : LifeCtx} (S : Row) :
    CDerivesAt ΞE Δ [] (.val (constC (Val.lam (.inj₁ .unit))))
      (.val (retTy S .unit (stashR S))) :=
  .bangThunkV (dead_noLive .nil) rfl (.lam (.effSub (RowLe.nil S) (.ret (.thunkV rfl (.lam
    (.effSub (RowLe.nil S) (.ret (.sumI₁ (.unitI (.drop rfl (.drop rfl .nil)))))))))))

/-- **`stash`'s clause** at the cancellable `bool ↠ 1` of cancel row `F`, at a row `S` with no `unr`
operation: the closure it answers holds `k` and `x`; its cancel branch is a `[let]` of `cancel k`,
whose `F_{F ⊕ S} 1` is read at `S`, holding `x` across it; its resume branch is a `[let]` of
`resume k ()`, applying the closure the resumed computation answers. -/
theorem dAt_stashCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {F : CTy}
    (hF : F.isTop = false) (hFS : RowLe (F.rowOf ++ S) S) (hU : ¬ S.Unr) :
    CDerivesAt ΞE Δ Γ (.val stashClV) (.val (clauseTy S (stashR S) (.cancel, boolT, .unit) F)) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_))
  -- `k` at `0`, `x` at `1`; the closure `λc. …`
  refine .effSub (RowLe.nil S) (.ret (.thunkV rfl (.lam ?_)))
  -- `c` at `0`, `k` at `1`, `x` at `2`
  refine .sumE (A := .unit) (B := .unit) (.left (.right (.right (.dead (deadSplit hΓ)))))
    (.var (.here (.cons (.cons (.cons hΓ.toP))))) ?_ ?_
  · -- `inl _ ⇒ cancel k; x`: `u` at `0`, `k` at `2`, `x` at `3`
    have hct : cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit := by simp [cancelTy, hF]
    refine .effLet (A := .unit) (.right (.dead (.left (.right (.dead (deadSplit hΓ))))))
      (fun _ => fun s hs hl => ?_) (fun hS => absurd hS hU) ?_ ?_
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | hs
      · exact .unit
      · cases hl
      · cases hl
      · exact .sum .unit .unit
      · cases hl
      · exact dead_noLive (P := fun s => s.ty.OwnFree) hΓ s hs hl
    · refine .effSub hFS ?_
      rw [← hct]
      exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S (stashR S))) (cancelTy S F))
        (.there (.there (.here (.cons (.cons hΓ.toP))))))
    · exact .effSub (RowLe.nil S) (.ret (.var (.skip rfl (.skip rfl (.there (.there
        (.here (.cons hΓ.toP))))))))
  · -- `inr _ ⇒ resume k () to g. g (inr ())`
    refine .effLet (A := stashR S) (.left (.dead (.left (.left (.dead (deadSplit hΓ))))))
      (fun _ => fun s hs hl => ?_) (fun hS => absurd hS hU) ?_ ?_
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | hs
      · cases hl
      · cases hl
      · cases hl
      · cases hl
      · cases hl
      · exact dead_noLive (P := fun s => s.ty.OwnFree) hΓ s hs hl
    · -- `resume k ()`: `() to y. k (inj₁ ()) y`
      refine .bind (.left (.dead (.right (.left (.dead (deadSplit hΓ))))))
        (.ret (.unitI (.drop rfl (.cons (.cons (.drop rfl (.cons hΓ.toP))))))) ?_
      show CDerivesAt ΞE Δ _ (.app (.app (.var 3) (.inj₁ .unit)) (.var 0)) _
      exact .app (.right (.dead (.dead (.left (.dead (.dead (deadSplit hΓ)))))))
        (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S (stashR S))) (cancelTy S F))
          (.there (.there (.there (.here (.cons (.cons hΓ.toP))))))))
        (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))
    · -- `g (inr ())`
      have hΓd : Ctx.Dead ([⟨.unit, false⟩, ⟨boolT, false⟩,
          ⟨kTy S (stashR S) .cancel .unit F, false⟩, ⟨boolT, false⟩,
          ⟨.tensor boolT (kTy S (stashR S) .cancel .unit F), false⟩] ++ Γ) :=
        .cons (.cons (.cons (.cons (.cons hΓ))))
      exact .bind (.right (deadSplit hΓd)) (.ret (.sumI₂ (.unitI (.cons hΓd.toP))))
        (.app (.right (.left (deadSplit hΓd))) (.force (C := .arr boolT (CTy.effOf S boolT))
          (.there (.here hΓd.toP))) (.here (.cons hΓd.toP)))

/-- **`stash M` at the row `S`**, `M` at `yield`'s row of cancel row `F` before `S`. -/
theorem dAt_stash {Δ : LifeCtx} {S : Row} (hS : RowAt ΞE S) (hnS : ∀ o ∈ S, o.n ≠ 3)
    {F : CTy} (hF : F.isTop = false) (hFS : RowLe (F.rowOf ++ S) S) (hU : ¬ S.Unr) {M : Expr}
    (hM : CDerivesAt ΞE Δ [] M
      (.comp (CTy.effOf (Row.ofEff 3 [(.cancel, boolT, .unit)] 0 (fun _ => F) ++ S) .unit))) :
    CDerivesAt ΞE Δ [] (hndE stashH M) (.comp (CTy.effOf S (stashR S))) :=
  dAt_hQ .nil .nil ΞE_3 (by decide) hS hnS (dAt_stashRet S) (dAt_stashCl .nil hF hFS hU) hM

theorem rowAt_yield : RowAt ΞE yieldRow :=
  rowAt_left (S' := []) (rowAt_ofEff_append ΞE_3 (by decide) (by simp) (rowAt_nil ΞE))

/-- `yield tt; yield ff` at `yield`'s row. -/
theorem dAt_gen9 {Δ : LifeCtx} : CDerivesAt ΞE Δ [] gen9E (.comp (CTy.effOf yieldRow .unit)) :=
  .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil)
    (.effPerform (o := ⟨3, 0, .cancel, boolT, .unit, .ret .unit⟩) rowAt_yield
      (by simp [Row.ofEff, Row.find]) rfl (.sumI₂ (.unitI .nil)))
    (.effPerform (o := ⟨3, 0, .cancel, boolT, .unit, .ret .unit⟩) rowAt_yield
      (by simp [Row.ofEff, Row.find]) rfl (.sumI₁ (.unitI (.drop rfl .nil))))

theorem not_unr_nil : ¬ Row.Unr ([] : Row) := fun ⟨_, h, _⟩ => absurd h List.not_mem_nil

/-- `stash gen to g. g c` at the pure row, `c` a boolean. -/
theorem dAt_storedK {Δ : LifeCtx} {c : Expr}
    (hc : CDerivesAt ΞE Δ [⟨stashR [], false⟩] c (.val boolT)) :
    CDerivesAt ΞE Δ [] (storedK gen9E c) (.comp (.ret boolT)) :=
  .bind (A := stashR []) .nil
    (dAt_stash (S := []) (rowAt_nil ΞE) (by simp) (F := .ret .unit) rfl (RowLe.refl [])
      not_unr_nil (.effSub (rowLe_append_right _ _) dAt_gen9))
    (dAt_callVar .nil hc)

/-- **E9a is typed**: the stored `κ` resumed. -/
theorem dAt_storedKResume {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] storedKResume (.comp (.ret boolT)) :=
  dAt_storedK (.sumI₂ (.unitI (.cons .nil)))

/-- **E9b is typed**: the stored `κ` cancelled. -/
theorem dAt_storedKCancel {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] storedKCancel (.comp (.ret boolT)) :=
  dAt_storedK (.sumI₁ (.unitI (.cons .nil)))

/-- **E9c is typed**, at a cancellable `exnₒ`: `yield`'s cancel row holds the finaliser's raise of
`exnₒ`, whose handler is live where the closure cancels `κ`. -/
theorem dAt_storedKFin {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] storedKFin (.comp (.ret (.sum boolT .unit))) := by
  have hn : ∀ o ∈ exnRow 1 .cancel ++ [], o.n ≠ 3 := by
    intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  have hU : ¬ (exnRow 1 .cancel ++ []).Unr := by
    rintro ⟨o, ho, hq⟩
    simp [Row.ofEff] at ho
    subst ho
    cases hq
  refine dAt_toResult ΞE_1 (by decide) (by decide) (S := []) (rowAt_nil ΞE) (by simp) ?_
  refine .effLet (A := stashR (exnRow 1 .cancel ++ [])) .nil
    (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
    ?_ (dAt_callVar .nil (.sumI₁ (.unitI (.cons .nil))))
  refine dAt_stash rowAt_exn1 hn (F := finExn 1 .cancel) rfl ?_ hU ?_
  · rw [CTy.rowOf_effOf, List.append_nil]
    exact rowLe_dup _
  -- `gen then x. x unwind raise exnₒ ()` at `yield`'s row of cancel row `{exnₒ}`
  show CDerivesAt ΞE Δ [] (thenE (.var 0) (raiseU 1) gen9E) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := yieldRow) (SD := exnRow 1 .cancel)
    .nil ?_ (by simp [Row.Uniq, Row.ofEff]) (fun _ => fun _ h => absurd h List.not_mem_nil)
    ?_ ?_ ?_ ?_ rfl dAt_gen9 (.effSub (RowLe.nil _) (.ret (.var (.here .nil))))
    (dAt_raiseU (.cons .nil) ΞE_1 (by decide) (by decide) .unit)
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · intro n i o hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    refine ⟨⟨3, 0, .cancel, boolT, .unit, finExn 1 .cancel⟩, by simp [Row.ofEff, Row.find],
      ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (.inr ⟨rfl, RowLe.nil _⟩)
  · exact (rowLe_append_right _ []).trans (rowLe_ofEff_cons _ _ hn)
  · intro n i o o' hf hf' _
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    simp [Row.ofEff, Row.find] at hf'
    subst hf'
    exact thenLe_exn 1 .cancel
  · rintro ⟨o, ho, h⟩
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    simp [capB, VTy.isZero] at h

end E9

/-! ### E4: a deep handler -/

section E4

/-- `tick`'s row. -/
abbrev tickRow : Row := Row.ofEff 5 [(.lin, .unit, .unit)] 0

/-- The counting handler's answer: `U(N ⊸ F (1 ⊗ N))`. -/
abbrev countR : VTy := .thunk (.arr natN (CTy.effOf [] (.tensor .unit natN)))

theorem rowAt_tick : RowAt ΞE (tickRow ++ []) :=
  rowAt_ofEff_append ΞE_5 (by decide) (by simp) (rowAt_nil ΞE)

/-- A row of one linear operation drops no continuation and copies none. -/
theorem not_cancels_tick : ¬ (tickRow ++ []).Cancels := by
  rintro ⟨o, ho, hq⟩
  simp [Row.ofEff] at ho
  subst ho
  exact hq rfl

theorem not_unr_tick : ¬ (tickRow ++ []).Unr := by
  rintro ⟨o, ho, hq⟩
  simp [Row.ofEff] at ho
  subst ho
  cases hq

/-- **`yield (_, k) ⇒ tick (); resume k ()`** at the cancellable `bool ↠ 1`, at `tick`'s row:
`tick ()` is a `[let]` at a row of one linear operation, so the continuation holding `k` is
neither dropped nor copied. -/
theorem dAt_tickingCl {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] (.val tickingClV)
      (.val (clauseTy (tickRow ++ []) .unit (.cancel, boolT, .unit))) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive .nil) rfl (.lam (.tensorE (.left .nil) (.var (.here .nil)) ?_))
  refine .effLet (.right (.left (.dead .nil))) (fun h => absurd h not_cancels_tick)
    (fun h => absurd h not_unr_tick)
    (.effPerform (o := ⟨5, 0, .lin, .unit, .unit, .ret .unit⟩) rowAt_tick
      (by simp [Row.ofEff, Row.find]) rfl (.unitI (.cons (.drop rfl (.cons .nil))))) ?_
  refine .bind (.left (.right (.dead (.dead .nil))))
    (.ret (.unitI (.drop rfl (.cons (.cons (.cons .nil)))))) ?_
  exact .app (.right (.dead (.left (.dead (.dead .nil)))))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf (tickRow ++ []) .unit))
      (CTy.effOf (tickRow ++ []) .unit)) (.there (.there (.here (.cons (.cons .nil)))))))
    (.here (.cons (.cons (.cons (.cons .nil)))))

/-- **`deepGen` at `tick`'s row**: the handler at `tick`'s row, the yields at `yield`'s row before
it. -/
theorem dAt_deepGenE {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] deepGenE (.comp (CTy.effOf (tickRow ++ []) .unit)) := by
  have hY : RowAt ΞE
      (Row.ofEff 3 [(.cancel, boolT, .unit)] 0 (fun _ => .ret .unit) ++ (tickRow ++ [])) :=
    rowAt_ofEff_append ΞE_3 (by decide) (by simp) rowAt_tick
  refine dAt_hQ .nil .nil ΞE_3 (by decide) rowAt_tick ?_ (F := .ret .unit) (X := .unit) ?_
    dAt_tickingCl ?_
  · intro o ho; simp [Row.ofEff] at ho; subst ho; decide
  · exact .bangThunkV (dead_noLive .nil) rfl
      (.lam (.effSub (RowLe.nil _) (.ret (.unitI (.drop rfl .nil)))))
  · exact .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil)
      (.effPerform (o := ⟨3, 0, .cancel, boolT, .unit, .ret .unit⟩) hY
        (by simp [Row.ofEff, Row.find]) rfl (.sumI₂ (.unitI .nil)))
      (.effPerform (o := ⟨3, 0, .cancel, boolT, .unit, .ret .unit⟩) hY
        (by simp [Row.ofEff, Row.find]) rfl (.sumI₁ (.unitI (.drop rfl .nil))))

/-- **`tick (_, k) ⇒ λc. resume k () to g. g (c + 1)`** at the linear `1 ↠ 1`, at the pure row:
the count is held across the resume. -/
theorem dAt_countCl {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] (.val countClV) (.val (clauseTy [] countR (.lin, .unit, .unit))) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive .nil) rfl (.lam (.tensorE (.left .nil) (.var (.here .nil)) ?_))
  refine .ret (.thunkV rfl (.lam ?_))
  -- `c` at `0`, `k` at `1`, `x` at `2`
  refine .bind (A := countR) (.right (.left (.left (.dead .nil)))) ?_ ?_
  · refine .bind (.dead (.right (.left (.dead .nil))))
      (.ret (.unitI (.cons (.cons (.drop rfl (.cons .nil)))))) ?_
    exact .app (.right (.dead (.left (.dead (.dead .nil)))))
      (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] countR)) .top)
        (.there (.there (.here (.cons (.cons .nil)))))))
      (.here (.cons (.cons (.cons (.cons .nil)))))
  · -- `g (inj₂ c)`: `g` at `0`, `c` at `1`
    refine .bind (.right (.left (.dead (.dead (.dead .nil)))))
      (.ret (.roll natBody_noMut natN_closed (.sumI₂ (.var (.there (.here (.cons (.cons (.cons
        .nil))))))))) ?_
    exact .app (.right (.left (.dead (.dead (.dead (.dead .nil))))))
      (.force (C := .arr natN (CTy.effOf [] (.tensor .unit natN)))
        (.there (.here (.cons (.cons (.cons (.cons .nil)))))))
      (.here (.cons (.cons (.cons (.cons (.cons .nil))))))

/-- **E4 is typed**: `deepGen` at `tick`'s row, under the counting handler of `tick`. -/
theorem dAt_deepGen {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] deepGen (.comp (.ret (.tensor .unit natN))) :=
  .bind .nil
    (dAt_hQ .nil .nil ΞE_5 (by decide) (S := []) (rowAt_nil ΞE) (by simp) (F := .ret .unit)
      (dAt_pairRet [] .unit natN) dAt_countCl dAt_deepGenE)
    (dAt_callVar .nil (CDerivesAt.ofEffFree (d_num (.cons .nil) 0) rfl))

/-- **E4 under a handler of `tick` that resumes is typed** at the pure row. -/
theorem dAt_deepGenPlain {Δ : LifeCtx} : CDerivesAt ΞE Δ [] deepGenPlain (.comp (.ret .unit)) :=
  dAt_hQ .nil .nil ΞE_5 (by decide) (S := []) (rowAt_nil ΞE) (by simp) (F := .ret .unit)
    (X := .unit) (CDerivesAt.ofEffFree (CancelIntercept.d_idV [] .unit) rfl)
    (dAt_resumeCl [] .unit (by decide) rfl) dAt_deepGenE

end E4

/-! ### E1, E2d and E10: one function at several rows (`[let-poly]`) -/

section Poly
open BoCa.Fig16.LogRel.Core.CancelIntercept (exnRow rowLe_ofEff_cons rowLe_append_right
  dAt_toResult dAt_raiseU d_idV)

/-- `wait`'s row. -/
abbrev waitRow0 : Row := Row.ofEff 2 [(.cancel, .unit, .unit)] 0

/-- `wait (); return tt` at a row that finds `wait`. -/
theorem dAt_waitBody {Δ : LifeCtx} {S : Row} (hS : RowAt ΞE S)
    (hf : Row.find S 2 0 = some ⟨2, 0, .cancel, .unit, .unit, .ret .unit⟩) :
    CDerivesAt ΞE Δ [] (bindE (performU 2) (.inj₂ .unit)) (.comp (CTy.effOf S boolT)) :=
  .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil)
    (.effPerform (o := ⟨2, 0, .cancel, .unit, .unit, .ret .unit⟩) hS hf rfl (.unitI .nil))
    (.effSub (RowLe.nil _) (.ret (.sumI₂ (.unitI (.drop rfl .nil)))))

theorem rowAt_wait : RowAt ΞE (waitRow0 ++ []) :=
  rowAt_ofEff_append ΞE_2 (by decide) (by simp) (rowAt_nil ΞE)

theorem names_exn1 {m : UInt32} (hm : m ≠ 1) : ∀ o ∈ exnRow 1 .cancel ++ [], o.n ≠ m := by
  intro o ho
  simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at ho
  subst ho
  exact Ne.symm hm

theorem not_unr_exn1 : ¬ (exnRow 1 .cancel ++ []).Unr := by
  rintro ⟨o, ho, hq⟩
  simp [Row.ofEff] at ho
  subst ho
  cases hq

/-! #### E1 -/

/-- **`hof` at the row `S`**: `U(1 ⊸ F_Σ B) ⊸ F_Σ B`. -/
theorem dAt_hof {Δ : LifeCtx} (S : Row) (B : VTy) :
    CDerivesAt ΞE Δ [] hofE
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf S B))) (CTy.effOf S B))) :=
  .lam (dAt_callVar .nil (.unitI (.cons .nil)))

/-- E1's body with `hof` in place of `f` at each use. -/
def threeUsesHof : Expr :=
  bindE (appE hofE pureCbE)
    (bindE (hndE (toResultH 1 .cancel) (appE hofE (failCbE 1)))
      (bindE (hndE (resumerH 2 .cancel) (appE hofE (waitCbE 2)))
        (.pair (.var 2) (.pair (.var 1) (.var 0)))))

/-- `[let-poly]`'s premise term for E1 is its body with `hof` at each use. -/
theorem threeUses_subst :
    (threeUses.subst 0 (Val.lam (appE (.var 0) .unit))).shift 1 0 = threeUsesHof := rfl

/-- E1's body is its copy, `hof` at each use, with `hof` replaced by the bound variable
(`Expr.unfill`). -/
theorem threeUses_unfill : threeUsesHof.unfill (appE (.var 0) .unit) 0 = threeUses := by decide

/-- **E1's body, `hof` at each use**: at the pure row, at `exn`'s row under `toResult`, and at
`wait`'s row under `resumer`. -/
theorem dAt_threeUsesHof {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [⟨.unit, false⟩] threeUsesHof
      (.comp (.ret (.tensor boolT (.tensor (.sum boolT .unit) boolT)))) := by
  have hΓ₀ : Ctx.Dead ([⟨.unit, false⟩] : Ctx VTy) := .cons .nil
  refine .bind (deadSplit hΓ₀) (dAt_appE hΓ₀ rfl (dAt_hof [] boolT)
    (dAt_cb hΓ₀ (.ret (.sumI₂ (.unitI .nil))))) ?_
  refine .bind (A := .sum boolT .unit) (.right (deadSplit hΓ₀)) ?_ ?_
  · refine dAt_dead (.cons hΓ₀) (dAt_toResult ΞE_1 (by decide) (by decide) (S := [])
      (rowAt_nil ΞE) (by simp) ?_)
    exact dAt_appE .nil rfl (dAt_hof _ boolT) (dAt_cb .nil
      (.effSub (rowLe_append_right _ _) (dAt_raiseU .nil ΞE_1 (by decide) (by decide) boolT)))
  refine .bind (A := boolT) (.right (.right (deadSplit hΓ₀))) ?_ ?_
  · refine dAt_dead (.cons (.cons hΓ₀)) (dAt_hQ .nil .nil ΞE_2 (by decide) (S := [])
      (rowAt_nil ΞE) (by simp) (F := .ret .unit) (X := boolT)
      (CDerivesAt.ofEffFree (d_idV [] boolT) rfl) (dAt_resumeCl [] boolT (by decide) rfl) ?_)
    exact dAt_appE .nil rfl (dAt_hof _ boolT)
      (dAt_cb .nil (dAt_waitBody rowAt_wait (by simp [Row.ofEff, Row.find])))
  exact .ret (.tensorI (.right (.right (.left (.dead .nil))))
    (.var (.there (.there (.here (.cons .nil)))))
    (.tensorI (.right (.left (.dead (.dead .nil)))) (.var (.there (.here (.cons (.cons .nil)))))
      (.var (.here (.cons (.cons (.cons .nil)))))))

/-- **E1 is typed** (`[let-poly]`): `hof` is let-bound once and used at three rows, the pure row,
`exn`'s and `wait`'s, each use at its own row. -/
theorem dAt_hofTwoRows {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] hofTwoRows
      (.comp (.ret (.tensor boolT (.tensor (.sum boolT .unit) boolT)))) := by
  refine .letPoly (appE (.var 0) .unit) rfl (dAt_hof [] boolT) ?_
  rw [threeUses_subst]
  exact dAt_threeUsesHof

/-! #### E2d -/

/-- `return _ ⇒ ff` at the row `S`. -/
theorem dAt_sgRet {Δ : LifeCtx} (S : Row) :
    CDerivesAt ΞE Δ [] (.val (constC (Val.inj₁ Val.unit))) (.val (retTy S .unit boolT)) :=
  .bangThunkV (dead_noLive .nil) rfl
    (.lam (.effSub (RowLe.nil S) (.ret (.sumI₁ (.unitI (.drop rfl .nil))))))

/-- **`sumGen`'s clause** at the row `S`: its `[let]` holds `x : bool` across the resume, so `S`
has no `unr` operation. -/
theorem dAt_sgCl {Δ : LifeCtx} (S : Row) (hU : ¬ S.Unr) :
    CDerivesAt ΞE Δ [] (.val sgClV) (.val (clauseTy S boolT (.cancel, boolT, .unit))) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive .nil) rfl (.lam (.tensorE (.left .nil) (.var (.here .nil)) ?_))
  refine .effLet (A := boolT) (.left (.right (.dead .nil))) (fun _ => ?_) (fun h => absurd h hU)
    ?_ ?_
  · intro s hs hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · cases hl
    · exact .sum .unit .unit
    · cases hl
  · refine .bind (.right (.dead (.dead .nil))) (.ret (.unitI (.cons (.cons (.cons .nil))))) ?_
    exact dAt_kResume
      (Γ := [⟨boolT, false⟩, ⟨.tensor boolT (kTy S boolT .cancel .unit), false⟩])
      (.cons (.cons .nil)) (q := .cancel) (by decide)
  · refine .sumE (.right (.dead (.left (.dead .nil))))
      (.var (.there (.there (.here (.cons .nil))))) ?_ ?_
    · exact .effSub (RowLe.nil S) (.ret (.var (.skip rfl (.here (.cons (.cons (.cons .nil)))))))
    · exact .effSub (RowLe.nil S)
        (.ret (.sumI₂ (.unitI (.drop rfl (.drop rfl (.cons (.cons (.cons .nil))))))))

/-- **`sumGen` at the row `r`**, `r` without `yield` and with no `unr` operation:
`U(1 ⊸ F_{yield ⊙ r} 1) ⊸ F_r bool`. -/
theorem dAt_sumGen {Δ : LifeCtx} {r : Row} (hr : RowAt ΞE r) (hnr : ∀ o ∈ r, o.n ≠ 3)
    (hU : ¬ r.Unr) :
    CDerivesAt ΞE Δ [] sumGenE
      (.comp (.arr
        (.thunk (.arr .unit (CTy.effOf (Row.ofEff 3 [(.cancel, boolT, .unit)] 0 ++ r) .unit)))
        (CTy.effOf r boolT))) :=
  .lam (dAt_hQ (.right .nil) (.cons .nil) ΞE_3 (by decide) hr hnr (F := .ret .unit) (X := .unit)
    (dAt_sgRet r) (dAt_sgCl r hU) (dAt_callVar .nil (.unitI (.cons .nil))))

/-- E2d's uses with `sumGen` in place of `s` at each. -/
def sumGenUsesW : Expr :=
  bindE (appE sumGenE gen1E)
    (bindE (hndE (toResultH 1 .cancel) (appE sumGenE gen2E)) (.pair (.var 1) (.var 0)))

theorem sumGenUses_subst :
    (sumGenUses.subst 0 (Val.lam (hndE sgH (appE (.var 0) .unit)))).shift 1 0 = sumGenUsesW := rfl

/-- E2d's body is its copy with `sumGen` replaced by the bound variable (`Expr.unfill`). -/
theorem sumGenUses_unfill :
    sumGenUsesW.unfill (hndE sgH (appE (.var 0) .unit)) 0 = sumGenUses := by decide

/-- **E2d's uses, `sumGen` at each**: at the pure row, and at `exn`'s row under `toResult`, the
generators at `yield ⊙` each. -/
theorem dAt_sumGenUsesW {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [⟨.unit, false⟩] sumGenUsesW
      (.comp (.ret (.tensor boolT (.sum boolT .unit)))) := by
  have hΓ₀ : Ctx.Dead ([⟨.unit, false⟩] : Ctx VTy) := .cons .nil
  have hY₀ : RowAt ΞE (Row.ofEff 3 [(.cancel, boolT, .unit)] 0 ++ []) :=
    rowAt_ofEff_append ΞE_3 (by decide) (by simp) (rowAt_nil ΞE)
  have hY₁ : RowAt ΞE (Row.ofEff 3 [(.cancel, boolT, .unit)] 0 ++ (exnRow 1 .cancel ++ [])) :=
    rowAt_ofEff_append ΞE_3 (by decide) (by simp) rowAt_exn1
  refine .bind (deadSplit hΓ₀) (dAt_appE hΓ₀ rfl
    (dAt_sumGen (rowAt_nil ΞE) (by simp) (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil))
    (dAt_cb hΓ₀ (.effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil)
      (.effPerform (o := ⟨3, 0, .cancel, boolT, .unit, .ret .unit⟩) hY₀
        (by simp [Row.ofEff, Row.find]) rfl (.sumI₁ (.unitI .nil)))
      (.effPerform (o := ⟨3, 0, .cancel, boolT, .unit, .ret .unit⟩) hY₀
        (by simp [Row.ofEff, Row.find]) rfl (.sumI₂ (.unitI (.drop rfl .nil))))))) ?_
  refine .bind (A := .sum boolT .unit) (.right (deadSplit hΓ₀)) ?_ ?_
  · refine dAt_dead (.cons hΓ₀) (dAt_toResult ΞE_1 (by decide) (by decide) (S := [])
      (rowAt_nil ΞE) (by simp) ?_)
    refine dAt_appE .nil rfl (dAt_sumGen rowAt_exn1 (names_exn1 (by decide)) not_unr_exn1)
      (dAt_cb .nil ?_)
    exact .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil)
      (.effPerform (o := ⟨3, 0, .cancel, boolT, .unit, .ret .unit⟩) hY₁
        (by simp [Row.ofEff, Row.find]) rfl (.sumI₁ (.unitI .nil)))
      (.effSub ((rowLe_append_right _ []).trans
          (rowLe_ofEff_cons _ _ (names_exn1 (by decide))))
        (dAt_raiseU (.drop rfl .nil) ΞE_1 (by decide) (by decide) .unit))
  exact .ret (.tensorI (.right (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
    (.var (.here (.cons (.cons .nil)))))

/-- **E2d is typed** (`[let-poly]`): `sumGen` is let-bound once and used at two rows, its
generators at `yield` before each. -/
theorem dAt_sumGenProg {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] sumGen (.comp (.ret (.tensor boolT (.sum boolT .unit)))) := by
  refine .letPoly (hndE sgH (appE (.var 0) .unit)) rfl
    (dAt_sumGen (rowAt_nil ΞE) (by simp) (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil)) ?_
  rw [sumGenUses_subst]
  exact dAt_sumGenUsesW

/-! #### E10 -/

/-- **`wait (_, k) ⇒ cancel k; return ff`** at the cancellable `1 ↠ 1`, at every row: the payload is
dropped with the cancel, so the `[let]`'s continuation holds nothing. -/
theorem dAt_tmCl {Δ : LifeCtx} (S : Row) :
    CDerivesAt ΞE Δ [] (.val tmClV) (.val (clauseTy S boolT (.cancel, .unit, .unit))) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive .nil) rfl (.lam (.tensorE (.left .nil) (.var (.here .nil)) ?_))
  refine .effLet (A := .unit) (.left (.left (.dead .nil))) (fun _ => fun s hs hl => ?_)
    (fun _ => fun s hs hl => ?_) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> cases hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> cases hl
  · exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S boolT)) (CTy.effOf S .unit))
      (.here (.drop rfl (.cons .nil))))
  · exact .effSub (RowLe.nil S) (.ret (.sumI₁ (.unitI (.drop rfl (.cons (.cons (.cons .nil)))))))

/-- **`timeout` at the row `r`**, `r` without `wait`: `U(1 ⊸ F_{wait ⊙ r} bool) ⊸ F_r bool`.
-/
theorem dAt_timeoutR {Δ : LifeCtx} {r : Row} (hr : RowAt ΞE r) (hnr : ∀ o ∈ r, o.n ≠ 2) :
    CDerivesAt ΞE Δ [] timeoutRE
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf (waitRow0 ++ r) boolT))) (CTy.effOf r boolT))) :=
  .lam (dAt_hQ (.right .nil) (.cons .nil) ΞE_2 (by decide) hr hnr (F := .ret .unit) (X := boolT)
    (CDerivesAt.ofEffFree (d_idV r boolT) rfl) (dAt_tmCl r)
    (dAt_callVar .nil (.unitI (.cons .nil))))

/-- E10's uses with `timeout` in place of `t` at each. -/
def timeoutUsesW : Expr :=
  bindE (appE timeoutRE (waitCbE 2))
    (bindE (hndE (toResultH 1 .cancel) (appE timeoutRE (failCbE 1))) (.pair (.var 1) (.var 0)))

theorem timeoutUses_subst :
    (timeoutUses.subst 0 (Val.lam (hndE (hQ 2 .cancel idV tmClV) (appE (.var 0) .unit)))).shift 1 0 =
      timeoutUsesW := rfl

/-- E10's body is its copy with `timeout` replaced by the bound variable (`Expr.unfill`). -/
theorem timeoutUses_unfill :
    timeoutUsesW.unfill (hndE (hQ 2 .cancel idV tmClV) (appE (.var 0) .unit)) 0 = timeoutUses := by
  decide

/-- **E10's uses, `timeout` at each**: around a body that waits, at the pure row; and around a
body that raises `exn`, at `exn`'s row under `toResult`, the raise passing `timeout`'s handler. -/
theorem dAt_timeoutUsesW {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [⟨.unit, false⟩] timeoutUsesW
      (.comp (.ret (.tensor boolT (.sum boolT .unit)))) := by
  have hΓ₀ : Ctx.Dead ([⟨.unit, false⟩] : Ctx VTy) := .cons .nil
  refine .bind (deadSplit hΓ₀) (dAt_appE hΓ₀ rfl (dAt_timeoutR (rowAt_nil ΞE) (by simp))
    (dAt_cb hΓ₀ (dAt_waitBody rowAt_wait (by simp [Row.ofEff, Row.find])))) ?_
  refine .bind (A := .sum boolT .unit) (.right (deadSplit hΓ₀)) ?_ ?_
  · refine dAt_dead (.cons hΓ₀) (dAt_toResult ΞE_1 (by decide) (by decide) (S := [])
      (rowAt_nil ΞE) (by simp) ?_)
    exact dAt_appE .nil rfl (dAt_timeoutR rowAt_exn1 (names_exn1 (by decide)))
      (dAt_cb .nil (.effSub ((rowLe_append_right _ []).trans
          (rowLe_ofEff_cons _ _ (names_exn1 (by decide))))
        (dAt_raiseU .nil ΞE_1 (by decide) (by decide) boolT)))
  exact .ret (.tensorI (.right (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
    (.var (.here (.cons (.cons .nil)))))

/-- **E10 is typed** (`[let-poly]`): `timeout` is let-bound once and used at two rows. -/
theorem dAt_timeoutProg {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] timeoutProg (.comp (.ret (.tensor boolT (.sum boolT .unit)))) := by
  refine .letPoly (hndE (hQ 2 .cancel idV tmClV) (appE (.var 0) .unit)) rfl
    (dAt_timeoutR (rowAt_nil ΞE) (by simp)) ?_
  rw [timeoutUses_subst]
  exact dAt_timeoutUsesW

end Poly

/-! ### The derivations, read in `CDerives` -/

/-- E1 (`hofTwoRows`). -/
theorem d_hofTwoRows {Δ : LifeCtx} :
    CDerives Δ [] hofTwoRows (.comp (.ret (.tensor boolT (.tensor (.sum boolT .unit) boolT)))) :=
  dAt_hofTwoRows.toCDerives

/-- E2d (`sumGen`). -/
theorem d_sumGen {Δ : LifeCtx} :
    CDerives Δ [] sumGen (.comp (.ret (.tensor boolT (.sum boolT .unit)))) :=
  dAt_sumGenProg.toCDerives

/-- E4 (`deepGen`). -/
theorem d_deepGen {Δ : LifeCtx} : CDerives Δ [] deepGen (.comp (.ret (.tensor .unit natN))) :=
  dAt_deepGen.toCDerives

/-- E4, `deepGen` under a handler of `tick` that resumes. -/
theorem d_deepGenPlain {Δ : LifeCtx} : CDerives Δ [] deepGenPlain (.comp (.ret .unit)) :=
  dAt_deepGenPlain.toCDerives

/-- E5, `withLog` outside `toResult`. -/
theorem d_nestedLogOutside {Δ : LifeCtx} :
    CDerives Δ [] nestedLogOutside (.comp (.ret (.tensor (.sum .unit .unit) boolT))) :=
  dAt_nestedLogOutside.toCDerives

/-- E5, `toResult` outside `withLog`. -/
theorem d_nestedFailOutside {Δ : LifeCtx} :
    CDerives Δ [] nestedFailOutside (.comp (.ret (.sum (.tensor .unit boolT) .unit))) :=
  dAt_nestedFailOutside.toCDerives

/-- E6 (`tunnel`). -/
theorem d_tunnel {Δ : LifeCtx} : CDerives Δ [] tunnel (.comp (.ret (.sum boolT .unit))) :=
  dAt_tunnel.toCDerives

/-- E7a. -/
theorem d_e7a {Δ : LifeCtx} : CDerives Δ [] e7a (.comp (.ret (.sum boolT .unit))) :=
  dAt_e7a.toCDerives

/-- E7b. -/
theorem d_e7b {Δ : LifeCtx} : CDerives Δ [] e7b (.comp (.ret (.sum (.sum boolT .unit) .unit))) :=
  dAt_e7b.toCDerives

/-- E7d. -/
theorem d_e7d {Δ : LifeCtx} :
    CDerives Δ [] e7d (.comp (.ret (.sum (.sum (.sum boolT .unit) .unit) .unit))) :=
  dAt_e7d.toCDerives

/-- E8b. -/
theorem d_e8b {Δ : LifeCtx} : CDerives Δ [] e8b (.comp (.ret (.sum (.sum .unit .unit) .unit))) :=
  dAt_e8b.toCDerives

/-- E9a. -/
theorem d_storedKResume {Δ : LifeCtx} : CDerives Δ [] storedKResume (.comp (.ret boolT)) :=
  dAt_storedKResume.toCDerives

/-- E9b. -/
theorem d_storedKCancel {Δ : LifeCtx} : CDerives Δ [] storedKCancel (.comp (.ret boolT)) :=
  dAt_storedKCancel.toCDerives

/-- E9c. -/
theorem d_storedKFin {Δ : LifeCtx} : CDerives Δ [] storedKFin (.comp (.ret (.sum boolT .unit))) :=
  dAt_storedKFin.toCDerives

/-- E10 (`timeoutProg`). -/
theorem d_timeoutProg {Δ : LifeCtx} :
    CDerives Δ [] timeoutProg (.comp (.ret (.tensor boolT (.sum boolT .unit)))) :=
  dAt_timeoutProg.toCDerives

/-! ### The runs

Each program's run, computed by `runM` from the empty memory and read as a run of Core's machine
(`runM_val`), ends at its answer at the empty memory: every capture cell the run allocates is
released. -/

/-- `tt`, `inj₂ ()`. -/
abbrev ttV : Val := Val.inj₂ Val.unit

/-- `ff`, `inj₁ ()`. -/
abbrev ffV : Val := Val.inj₁ Val.unit

/-- **E1 runs to `(tt, (inr (), tt))`**: the pure callback answers `tt`, the raise reaches
`toResult`, and `wait`'s continuation is resumed at its cell. -/
theorem hofTwoRows_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem hofTwoRows Adequacy.emptyMem
      (.val (Val.pair ttV (Val.pair (Val.inj₂ Val.unit) ttV))) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E2d runs to `(tt, inr ())`**: three catches of `yield`, the second inside the first's clause,
and the raise passing `sumGen`'s reinstalled handler to `toResult`. -/
theorem sumGen_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem sumGen Adequacy.emptyMem
      (.val (Val.pair ttV (Val.inj₂ Val.unit))) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E4 runs to `((), 2)`**: the deep handler catches both yields, its clause ticking at each, and
the counting handler counts two ticks. -/
theorem deepGen_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem deepGen Adequacy.emptyMem
      (.val (Val.pair Val.unit (num 2))) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E4 under a handler of `tick` that resumes runs to `()`**: both yields are caught, and each
`tick` is resumed at once. -/
theorem deepGenPlain_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem deepGenPlain Adequacy.emptyMem (.val Val.unit) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E5, `withLog` outside, runs to `(inr (), tt)`**: the log is kept beside the error. -/
theorem nestedLogOutside_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem nestedLogOutside Adequacy.emptyMem
      (.val (Val.pair (Val.inj₂ Val.unit) ttV)) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E5, `toResult` outside, runs to `inr ()`**: the raise passes `withLog`'s handler, which the
unwind drops with its state. -/
theorem nestedFailOutside_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem nestedFailOutside Adequacy.emptyMem
      (.val (Val.inj₂ Val.unit)) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E6 runs to `inr ()`**: the callback's raise of `exnₒ` passes `fwrap`'s handler of `exnᵢ`
and reaches `toResult`. -/
theorem tunnel_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem tunnel Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E7a runs to `inr ()`**: `timeout`'s clause cancels `κ`, whose finaliser returns. -/
theorem e7a_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem e7a Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E7b runs to `inr ()`**: the cancel fires the finaliser, keeps its raise of `exnₒ` and
re-raises it at the canceller, where `toResult` catches it. -/
theorem e7b_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem e7b Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E7d runs to `inr ()`**: the cancel fires both finalisers innermost first and keeps the first
error, `exn_a`, which `toResult` of `exn_a` catches. -/
theorem e7d_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem e7d Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E8b runs to `inl (inr ())`**: the unwind of `exn_a` fires the finaliser, whose raise of
`exn_b` supersedes it; `toResult` of `exn_b` catches it and `toResult` of `exn_a` returns. -/
theorem e8b_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem e8b Adequacy.emptyMem
      (.val (Val.inj₁ (Val.inj₂ Val.unit))) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E9a runs to `ff`**: the stored `κ` is resumed after `stash` has returned. -/
theorem storedKResume_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem storedKResume Adequacy.emptyMem (.val ffV) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E9b runs to `tt`**: the stored `κ` is cancelled after `stash` has returned. -/
theorem storedKCancel_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem storedKCancel Adequacy.emptyMem (.val ttV) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E9c runs to `inr ()`**: the stored `κ`'s cancel fires its region's finaliser, whose raise of
`exnₒ` is re-raised at the closure and caught by `toResult`. -/
theorem storedKFin_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem storedKFin Adequacy.emptyMem
      (.val (Val.inj₂ Val.unit)) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

/-- **E10 runs to `(ff, inr ())`**: `timeout` cancels the waiting body, and the raising body's raise
passes `timeout`'s handler to `toResult`. -/
theorem timeoutProg_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem timeoutProg Adequacy.emptyMem
      (.val (Val.pair ffV (Val.inj₂ Val.unit))) :=
  runM_val (k := 200) (m := []) (m' := []) rfl

end BoCa.Fig16.LogRel.Core.Tier1Programs

end
