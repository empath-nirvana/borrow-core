import Core.DelayPrograms
import Core.CommonList

/-!
# Core — programs over streams  `[spec §7]`

A stream is made by `unfoldS step s₀` and consumed by `next`s and a final `close`.  The
consumers are `CDerives` derivations, so each program is one closed derivation, run by
adequacy and by the interpreter, with no hand proof:

* `take_runs`: every closed `U(Stream 1)`, observed `n` times and closed, runs to `()` with no
  cell left.
* `takeCloseR n`: the unit stream over a cell `s : Ref 1` (`next` returns `((), s)`, `close`
  frees `s`), observed `n` times and closed; `()` with no cell left.
* `natsSum n`: the stream `0, 1, 2, …` over a numeral state (`next` duplicates the state by a
  `foldOwn`, returns one copy and the successor of the other; `close` frees it), its first `n`
  elements summed and the stream closed: `natsSum 3` returns `3` with no cell left.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (unitNoLeak)

/-! ### A stream from a step and a state -/

/-- `s₀ to s. unfoldS step to f. ⟨(f s) π₁, (f s) π₂⟩ to t. K`: the thunk
`⟨(f s) π₁, (f s) π₂⟩` is `unfoldS step s₀` as a value of `U(Stream A)`. -/
def progS (s₀ : Expr) (step : Val) (K : Expr) : Expr :=
  bindE s₀ (bindE (.app (.val unfoldSV) (.val step))
    (bindE (withPair (.app (.app (.var 2) (.var 3)) (.val (.inj₁ .unit)))
        (.app (.app (.var 2) (.var 3)) (.val (.inj₂ .unit))))
      K))

/-- `f : U(S ⊸ Stream A), s : S ⊢ (f s) πᵢ`, inside `withPair`'s two binders. -/
theorem d_fsS {A S : VTy} :
    CDerives LifeCtx.empty (withCtx [⟨.thunk (.arr S (.stream A)), true⟩, ⟨S, true⟩])
      (.app (.var 2) (.var 3)) (.comp (.stream A)) :=
  .app (.dead (.dead (.left (.right .nil)))) (.force (.there (.there (.here (.cons .nil)))))
    (.there (.there (.there (.here .nil))))

/-- `⟨(f s) π₁, (f s) π₂⟩ : U(Stream A)`. -/
theorem d_thunkFSS {A S : VTy} :
    CDerives LifeCtx.empty [⟨.thunk (.arr S (.stream A)), true⟩, ⟨S, true⟩]
      (withPair (.app (.app (.var 2) (.var 3)) (.val (.inj₁ .unit)))
        (.app (.app (.var 2) (.var 3)) (.val (.inj₂ .unit))))
      (.val (.thunk (.stream A))) :=
  .thunkV rfl (.streamIn (.withI (.proj₁ (.streamOut d_fsS)) (.proj₂ (.streamOut d_fsS))))

theorem d_progS {A S : VTy} {C : CTy} {s₀ K : Expr} {step : Val}
    (hs₀ : CDerives LifeCtx.empty [] s₀ (.val S))
    (hstep : CDerives LifeCtx.empty [⟨S, false⟩] (.val step)
      (.val (.bang (.thunk (stepSC A S)))))
    (hK : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ →
      CDerives LifeCtx.empty (⟨.thunk (.stream A), true⟩ :: Γ) K (.comp C)) :
    CDerives LifeCtx.empty [] (progS s₀ step K) (.comp C) :=
  .bind .nil (.ret hs₀)
    (.bind (.right .nil)
      (.ret (.bangE (.lolliE (deadSplit (.cons .nil)) hstep (.unfoldS A S (.cons .nil)))))
      (.bind (.left (.left .nil)) (.ret d_thunkFSS) (hK (.cons (.cons .nil)))))

/-! ### Observing `n` times, then closing -/

/-- `t : U(Stream 1)` (index 0) observed `n` times, then closed. -/
def takeE : ℕ → Expr
  | 0 => .app (.var 0) (.val (.inj₂ .unit))
  | n + 1 => bindE (.app (.var 0) (.val (.inj₁ .unit))) (.letpair (.var 0) (.seq (.var 1) (takeE n)))

theorem d_takeE : ∀ (n : ℕ) {Γ : Ctx VTy}, Ctx.Dead Γ →
    CDerives LifeCtx.empty (⟨.thunk (.stream .unit), true⟩ :: Γ) (takeE n) (.comp (.ret .unit))
  | 0, _, hΓ => .proj₂ (.streamOut (.force (.here hΓ)))
  | n + 1, _, hΓ =>
      .bind (.left (deadSplit hΓ)) (.proj₁ (.streamOut (.force (.here hΓ))))
        (.tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
          (.unitE (.right (.left (.dead (.dead (deadSplit hΓ))))) (.var (.there (.here (.cons (.cons hΓ)))))
            (d_takeE n (.cons (.cons (.cons hΓ))))))

/-- **Adequacy for `Stream 1`**: for a closed `e : U(Stream 1)` and every `n`, observing `n` times
then closing runs from the empty memory to `()` and the empty memory.  `[spec §7]` -/
theorem take_runs {e : Expr} (he : CDerives LifeCtx.empty [] e (.val (.thunk (.stream .unit))))
    (n : ℕ) :
    BoCa.BoLo.Steps Adequacy.emptyMem (bindE e (takeE n)) Adequacy.emptyMem (.val .unit) :=
  adequacyC (.bind .nil (.ret he) (d_takeE n .nil))

/-! ### The unit stream over a cell -/

/-- `λs. ⟨return ((), s), free s⟩ : Ref 1 ⊸ F(1 ⊗ Ref 1) & F 1`. -/
def stepR : Val :=
  .lam (withPair (.pair (.val .unit) (.var 2)) (.app (.val (.prim .free)) (.var 2)))

theorem d_stepR {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val stepR) (.val (.bang (.thunk (stepSC .unit (.ref .unit))))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI
    (.ret (.tensorI (.dead (.dead (.right (deadSplit hΓ))))
      (.unitI (.cons (.cons (.cons hΓ)))) (.var (.there (.there (.here hΓ))))))
    (.ret (.lolliE (.dead (.dead (.left (deadSplit hΓ)))) (.var (.there (.there (.here hΓ))))
      (.free (.cons (.cons (.cons hΓ))))))))

/-- Allocate the cell, unfold, observe `n` times, close. -/
def takeCloseR (n : ℕ) : Expr :=
  progS (.app (.val (.prim .alloc)) (.val .unit)) stepR (takeE n)

theorem d_takeCloseR (n : ℕ) :
    CDerives LifeCtx.empty [] (takeCloseR n) (.comp (.ret .unit)) :=
  d_progS (.lolliE .nil (.unitI .nil) (.alloc .nil)) (d_stepR (.cons .nil))
    (fun hΓ => d_takeE n hΓ)

theorem takeCloseR_runs (n : ℕ) :
    BoCa.BoLo.Steps Adequacy.emptyMem (takeCloseR n) Adequacy.emptyMem (.val .unit) :=
  adequacyC (d_takeCloseR n)

theorem takeCloseR_eval : unitNoLeak (eval (takeCloseR 3)) = true := by decide

/-! ### The numerals, summed -/

/-- `case r {inj₁ u. u; (0, 0) | inj₂ p. let (x, y) = p in (x + 1, y + 1)}`. -/
def dupAlgB : Expr :=
  .case (.var 0) (.seq (.var 0) (.pair (.inj₁ (.val .unit)) (.inj₁ (.val .unit))))
    (.letpair (.var 0) (.pair (.inj₂ (.var 1)) (.inj₂ (.var 0))))

def dupAlgV : Val := .lam dupAlgB

theorem d_dupAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val dupAlgV) (.val (algOTy natF (.tensor natN natN))) := by
  refine d_algO hΓ (.sumE (A := .unit) (B := .tensor natN natN) (.left (deadSplit hΓ))
    (.var (.here hΓ)) ?_ ?_)
  · exact .unitE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
      (.ret (.tensorI (deadSplit (.cons (.cons hΓ)))
        (.roll natBody_noMut natN_closed (.sumI₁ (.unitI (.cons (.cons hΓ)))))
        (.roll natBody_noMut natN_closed (.sumI₁ (.unitI (.cons (.cons hΓ)))))))
  · exact .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
      (.ret (.tensorI (.right (.left (.dead (.dead (deadSplit hΓ)))))
        (.roll natBody_noMut natN_closed (.sumI₂ (.var (.there (.here (.cons (.cons hΓ)))))))
        (.roll natBody_noMut natN_closed (.sumI₂ (.var (.here (.cons (.cons (.cons hΓ)))))))))

/-- `foldOwn dupAlg : N ⊸ F(N ⊗ N)`. -/
def dupE : Expr := .app (.val (foldOwnV natF)) (.val dupAlgV)

theorem d_dup {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ dupE (.val (.lolli natN (.tensor natN natN))) :=
  .bangE (.lolliE (deadSplit hΓ) (d_dupAlg hΓ)
    (.foldOwn natF (.tensor natN natN) hΓ ⟨trivial, trivial⟩ trivial))

/-- `λs. ⟨dup s to p. let (a, b) = p in return (a, b + 1), freeNat s⟩ :
N ⊸ F(N ⊗ N) & F 1`. -/
def stepN : Val :=
  .lam (withPair (bindE (.app dupE (.var 2)) (.letpair (.var 0) (.pair (.var 1) (.inj₂ (.var 0)))))
    (.app freeNatE (.var 2)))

theorem d_stepN {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val stepN) (.val (.bang (.thunk (stepSC natN natN)))) := by
  have D4 : Ctx.Dead (⟨.tensor natN natN, false⟩ :: ⟨.unit, false⟩ :: ⟨.sum .unit .unit, false⟩ ::
      ⟨natN, false⟩ :: Γ) := .cons (.cons (.cons (.cons hΓ)))
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI ?_ ?_))
  · refine .bind (.dead (.dead (.left (deadSplit hΓ))))
      (.ret (.lolliE (.dead (.dead (.left (deadSplit hΓ)))) (.var (.there (.there (.here hΓ))))
        (d_dup (.cons (.cons (.cons hΓ)))))) ?_
    exact .tensorE (.left (.dead (.dead (.dead (deadSplit hΓ))))) (.var (.here (.cons (.cons (.cons hΓ)))))
      (.ret (.tensorI (.right (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
        (.var (.there (.here D4)))
        (.roll natBody_noMut natN_closed (.sumI₂ (.var (.here (.cons D4)))))))
  · exact .ret (.lolliE (.dead (.dead (.left (deadSplit hΓ)))) (.var (.there (.there (.here hΓ))))
      (d_freeNat (.cons (.cons (.cons hΓ)))))

/-- `acc : N` (index 0), `t : U(Stream N)` (index 1): add the next `n` elements to `acc`, close. -/
def sumK : ℕ → Expr
  | 0 => bindE (.app (.var 1) (.val (.inj₂ .unit))) (.seq (.var 0) (.var 1))
  | n + 1 => bindE (.app (.var 1) (.val (.inj₁ .unit)))
      (.letpair (.var 0) (bindE (.app (.app addE (.var 1)) (.var 3)) (sumK n)))

theorem d_sumK : ∀ (n : ℕ) {Γ : Ctx VTy}, Ctx.Dead Γ →
    CDerives LifeCtx.empty (⟨natN, true⟩ :: ⟨.thunk (.stream natN), true⟩ :: Γ) (sumK n)
      (.comp (.ret natN))
  | 0, _, hΓ =>
      .bind (.right (.left (deadSplit hΓ))) (.proj₂ (.streamOut (.force (.there (.here hΓ)))))
        (.unitE (.left (.right (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
          (.ret (.var (.there (.here (.cons hΓ))))))
  | n + 1, _, hΓ =>
      .bind (.right (.left (deadSplit hΓ))) (.proj₁ (.streamOut (.force (.there (.here hΓ)))))
        (.tensorE (.left (.right (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
          (.bind (.right (.left (.dead (.left (.dead (deadSplit hΓ))))))
            (.ret (.lolliE (.dead (.right (.dead (.left (.dead (deadSplit hΓ))))))
              (.var (.there (.there (.there (.here (.cons hΓ))))))
              (.lolliE (.dead (.left (.dead (.dead (.dead (deadSplit hΓ))))))
                (.var (.there (.here (.cons (.cons (.cons hΓ))))))
                (d_add (.cons (.cons (.cons (.cons (.cons hΓ)))))))))
            (d_sumK n (.cons (.cons (.cons (.cons hΓ)))))))

/-- The numerals from `0`, the first `n` summed, the stream closed. -/
def natsSum (n : ℕ) : Expr := progS (.val (num 0)) stepN (bindE (.val (num 0)) (sumK n))

theorem d_natsSum (n : ℕ) : CDerives LifeCtx.empty [] (natsSum n) (.comp (.ret natN)) :=
  d_progS (d_num .nil 0) (d_stepN (.cons .nil))
    (fun hΓ => .bind (.right (deadSplit hΓ)) (.ret (d_num (.cons hΓ) 0)) (d_sumK n hΓ))

/-- **Adequacy at the summed stream**: from the empty memory to a numeral and the empty memory. -/
theorem natsSum_runs (n : ℕ) :
    ∃ k, BoCa.BoLo.Steps Adequacy.emptyMem (natsSum n) Adequacy.emptyMem (.val (num k)) := by
  have hwp : wpTS [] (natsSum n) (fun _ v => Fig16.BoLo.pure (∃ k, v = num k))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives (d_natsSum n))
    obtain ⟨rfl, k, rfl⟩ := vC_natN hv
    exact ⟨rfl, k, rfl⟩
  obtain ⟨v, hsteps, k, rfl⟩ := theorem32 (natsSum n) (fun v => ∃ k, v = num k) hwp
  exact ⟨k, hsteps⟩

set_option maxRecDepth 100000 in
/-- `0 + 1 + 2 = 3`, with no cell left. -/
theorem natsSum_eval : numNoLeak (eval (natsSum 3)) = some 3 := by decide

end BoCa.Fig16.LogRel.Core

end
