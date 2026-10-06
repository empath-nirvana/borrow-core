import Core.Stdio
import Targets.Base.Typing
import Targets.Base.Machine

/-!
# Base — Core's cancellation and unwinding shapes (RESTRUCTURE §0, base; DESIGN §5 I3)

The shapes of Core's cancel run and unwind on complete runs
(`CancelRun`, `UnwindRun`, `CancelOrder`, `UnwindOrder`, `FinaliserOrder`), and the syntactic
no-interception property (`NoInterception`: typed terms hold no `ccatch`, no `cfin`, no handler
named `0`).  They mention no world.  A's S5 (`Targets/A/Soundness.lean`) is the run-based form at
every instance; these are the Instance's route to it at Core (RESTRUCTURE §4.1).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal hndE hndVal kappa
  ccatchE cfinE ubindE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- What a cancel answers at `ccatch`: `()`, or the kept error raised at the canceller. -/
def cancelAnswer : Option Val → Expr
  | none => .val .unit
  | some E => raiseE (.val E)

/-- A cancel run that fires the finalisers `fs`, innermost first: one `ufinC` per finaliser, its
`D ()` run under `cfin` to `cfret`/`cferr`, and at the end `ccatch` answering. -/
inductive CancelRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | caught {μ : Heap} {K : Kont} {Ns : List UInt32} {err : Option Val}
      (hK : K.Catches 0 = false) :
      CancelRun μ (ccatchE (K.plug (raiseE (.val (cancelVal Ns err))))) [] μ (cancelAnswer err)
  | fin {μ μ₁ μ₂ : Heap} {K₀ K : Kont} {Nv Dv : Val} {Ns : List UInt32} {err err' : Option Val}
      {fs : List Expr} {r : Expr} (hK : K.Catches 0 = false)
      (hD : Steps (ℍ := ℍ) μ (cfinE (cancelVal Ns err) (.app (.val Dv) (.val .unit))) μ₁
              (raiseE (.val (cancelVal Ns err'))))
      (hr : CancelRun μ₁ (ccatchE (K₀.plug (raiseE (.val (cancelVal Ns err'))))) fs μ₂ r) :
      CancelRun μ
        (ccatchE (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (cancelVal Ns err)))))))
        (Dv.1 :: fs) μ₂ r

/-- An unwind that fires the finalisers `fs`, innermost first: one `ufin` per finaliser, its
`D (); raise p` run until a raise is pending under a context `Kd` that catches nothing of it,
ending at a raise that the remaining frames do not catch.  If `D` returns, `Kd` is the hole and
the raise is `p`.  If `D` raises its own abortive operation, the raise is that one, and `Kd` holds
the `seq` frame (`_; raise p`, which catches nothing) and `D`'s own frames at the raise; no rule
reduces a raise under a `seq`, so the unwind goes on from `K₀ ∘ Kd`. -/
inductive UnwindRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | out {μ : Heap} {K : Kont} {m j : UInt32} {w : Val} (hK : K.Catches m = false) :
      UnwindRun μ (K.plug (raiseE (.val (opPayload m j w)))) [] μ
        (K.plug (raiseE (.val (opPayload m j w))))
  | fin {μ μ₁ μ₂ : Heap} {K₀ K Kd : Kont} {Nv Dv : Val} {n i m j : UInt32} {v w : Val}
      {fs : List Expr} {r : Expr} (hn : n ≠ 0) (hK : K.Catches n = false)
      (hD : Steps (ℍ := ℍ) μ (.seq (.app (.val Dv) (.val .unit)) (raiseE (.val (opPayload n i v))))
              μ₁ (Kd.plug (raiseE (.val (opPayload m j w)))))
      (hKd : Kd.Catches m = false)
      (hr : UnwindRun μ₁ ((K₀.comp Kd).plug (raiseE (.val (opPayload m j w)))) fs μ₂ r) :
      UnwindRun μ (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (opPayload n i v))))))
        (Dv.1 :: fs) μ₂ r

/-- `K` has no `ccatch` and no `cfin` frame. -/
def _root_.BoCa.BoLo.Kont.NoCtl : Kont → Prop
  | .hole => True
  | .appR f K => (f ≠ .prim .ccatch ∧ ∀ s, f ≠ .app (.prim .cfin) s) ∧ K.NoCtl
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCtl

/-- **I3.b, cancel**: in a typed program, every complete run of a continuation's cancel fires the
frozen finalisers once each, innermost first.  (The three administrative steps from
`κ (inj₂ ())` to `cancelOf n H K` are pure; the canceller's context `K₀` takes no part until
`ccatch` answers.) -/
def CancelOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ : Kont) n H K, Kont.NoCtl K →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (.app (kappa n H K) (.val (Val.inj₂ .unit)))) →
    ∀ μ₃ r, Steps (ℍ := ℍ) μ₁ (cancelOf n H K) μ₃ r →
      (r = .val .unit ∨ ∃ E, r = raiseE (.val E)) →
      CancelRun (ℍ := ℍ) μ₁ (cancelOf n H K) K.fins μ₃ r

/-- **I3.b, unwind**: every complete unwind through frames with no handler fires their finalisers
once each, innermost first. -/
def UnwindOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ K : Kont) n i v, K.hndNames = [] → Kont.NoCtl K → n ≠ 0 →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) →
    ∀ μ₂ (K' : Kont) m j w, K'.Catches m = false →
      Steps (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) μ₂
        (K'.plug (raiseE (.val (opPayload m j w)))) →
      UnwindRun (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) K.fins μ₂
        (K'.plug (raiseE (.val (opPayload m j w))))

/-- **I3.b.** -/
def FinaliserOrder (J : TypingJ) : Prop := CancelOrder (ℍ := ℍ) J ∧ UnwindOrder (ℍ := ℍ) J

/-- `.prim p` occurs in the term. -/
def _root_.BoCa.Expr.HasPrim (p : Prim) : Expr → Prop
  | .prim p' => p' = p
  | .var _ | .unit | .loc _ => False
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HasPrim p ∨ b.HasPrim p
  | .inj₁ a | .inj₂ a | .lam a => a.HasPrim p
  | .case a b c => a.HasPrim p ∨ b.HasPrim p ∨ c.HasPrim p

/-- Every occurrence of `.prim .hnd` is the function of
`.app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) _)` with `m ≠ 0`. -/
def _root_.BoCa.Expr.HndNamesNZ : Expr → Prop
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) r) => m ≠ 0 ∧ r.HndNamesNZ
  | .prim p => p ≠ .hnd
  | .var _ | .unit | .loc _ => True
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HndNamesNZ ∧ b.HndNamesNZ
  | .inj₁ a | .inj₂ a | .lam a => a.HndNamesNZ
  | .case a b c => a.HndNamesNZ ∧ b.HndNamesNZ ∧ c.HndNamesNZ

/-- **I3.c**: typed terms contain no `ccatch`, no `cfin`, and no handler named `0`. -/
def NoInterception (J : TypingJ) : Prop :=
  ∀ Θ Δ Γ e j, J Θ Δ Γ e j → ¬ e.HasPrim .ccatch ∧ ¬ e.HasPrim .cfin ∧ e.HndNamesNZ

end Targets

end
