import Core.LetDtorFiles
import Core.DivPrograms

/-!
# Core — closing a loop early through its state's destructor  `[spec §14, §62]`

A loop is closed early by a resume of its `tick` with *close* (§14): `iterate`'s step
`(f s).1 to r. case r {inl b → inl b | inr s′ → tick () to n. case n {inl _ → iterate (f, s′) |
inr _ → (λq. inr q) ((f s′).2)}}` runs the step's second observation on the state. The paper's
translation gives every function value a second component that drops its context (`⟦λx.t⟧ ≝
⟨λx. π₁⟦t⟧, drop_ctx_Γ⟩`, `↓N = N & 1`); for a loop's step that component is the state's
destructor. So a step whose *close* is the state's destructor (`d_stepD`) closes the state through
the same destructor as the unwind does, and the loop's residual is `1`.

The residual rule (§14, §15: *close* hands back `R`) is not deleted by this: a destructor is the
residual at `R = 1`, the close that hands nothing back. A loop that must return its state, or a
lent capability, to its caller still needs `R`.

The closed program: a file is the loop's state; `div_fuel` closes the loop after `k` turns:

    with_fs (f ← alloc 7; df ← div_fuel; df (λ_. tick () to n. case n
                 { next → iterate (λs. ⟨inr s, drop_File s⟩, f)
                 | close → drop_File f to u. inr u }, k))
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LetDtor.Loop
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.LetDtor.Files
open BoCa.BoLo (Heap Steps Step1 Kont freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **A step whose *close* is the state's destructor.** For a first observation `N` over the state
`s` (at `2`, under `⟨·,·⟩`'s binders) and a destructor `λx. b : St ⊸ F_{Σ_D} 1` with `Σ_D ≤ Σ`,
`λs. ⟨N, (λx. b) s⟩ : !U(St ⊸ F_Σ(B ⊕ St) & F_Σ 1)`: `iterate`'s step at the residual `1`. -/
theorem d_stepD {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S SD : Row} {St B : VTy}
    {N b : Expr}
    (hN : CDerives Δ (withCtx (⟨St, true⟩ :: Γ)) N (.comp (CTy.effOf S (.sum B St))))
    (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr St (CTy.effOf SD .unit))))
    (hDS : RowLe SD S) :
    CDerives Δ Γ (.val (.lam (withPair N (.app (.val (.lam b)) (.var 2)))))
      (.val (iterStepTy S St B .unit)) := by
  refine .bangThunkV (banged_dead hΓ) rfl (.lam (.withI hN ?_))
  exact .effSub hDS (.app (split_kill _).toP (hb _ (kill_dead _))
    (.there (.there (.here hΓ.toP))))

/-! ### The loop over a file -/

/-- The loop's row: `{tick, close}`. -/
abbrev SL : Row := [tickSig, fcloseSig]

/-- The loop's answer: `I32 ⊕ 1`, a result or the residual `1`. -/
abbrev Ans : VTy := .sum I32 .unit

theorem SL_not_cancels : ¬ SL.Cancels := by
  rintro ⟨o, ho, hq⟩
  simp only [SL, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> exact hq rfl

theorem SD_le_SL : RowLe SD SL := by
  intro n i o h
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
  simp only [SD, List.mem_singleton] at hm
  subst hm
  exact ⟨fcloseSig, rfl, OpSig.LeF.refl _⟩

/-- The step `λs. ⟨inr s, drop_File s⟩`: go on with the same state, or close it. -/
def stepD : Val := .lam (withPair (.inj₂ (.var 2)) (.app (.val (.lam dFileB)) (.var 2)))

theorem d_stepFile {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val stepD) (.val (iterStepTy SL File I32 .unit)) :=
  d_stepD hΓ (.effSub (RowLe.nil SL) (.ret (.sumI₂ (.var (.there (.there (.here hΓ.toP)))))))
    d_dFile SD_le_SL

/-- The loop's body under its dead binder (`0`), the file at `1`:
`tick () to n. case n { next → it ← iterate; p ← (stepD, f); it p | close → drop_File f to u. inr u }`. -/
def loopBD : Expr :=
  .app (.val (.lam (.case (.var 0)
      (bindE (.val (.prim .iterate)) (bindE (.pair (.val stepD) (.var 4)) (.app (.var 1) (.var 0))))
      (bindE (.app (.val (.lam dFileB)) (.var 3)) (.inj₂ (.var 0))))))
    tickE

theorem d_loopBD {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.unit, false⟩ :: ⟨File, true⟩ :: Γ) loopBD (.comp (CTy.effOf SL Ans)) := by
  refine .effLet (A := nextTy) (.dead (.right (deadSplit hΓ))) (fun h => absurd h SL_not_cancels)
    (fun h => absurd h (Row.not_unr_of_not_cancels SL_not_cancels))
    (.effPerform (S := SL) (o := tickSig) rfl rfl rfl (.unitI (.cons (.cons hΓ.toP)))) ?_
  refine .sumE (.left (.dead (.right (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ.toP)))) ?_ ?_
  · -- *next*: `iterate (stepD, f)`
    refine .bind (.right (.dead (.dead (.right (deadSplit hΓ)))))
      (.ret (.bangE (.iterate SL File I32 .unit (Row.divB_tick _)
        (.cons (.cons (.cons (.cons hΓ.toP))))))) ?_
    refine .bind (.right (.right (.dead (.dead (.left (deadSplit hΓ))))))
      (.ret (.tensorI (.dead (.dead (.dead (.dead (.right (deadSplit hΓ))))))
        (d_stepFile (by cdead))
        (.var (.there (.there (.there (.there (.here hΓ.toP)))))))) ?_
    exact .app (.right (.left (.left (.dead (.dead (.dead (deadSplit hΓ)))))))
      (.force (C := .arr (.tensor (iterStepTy SL File I32 .unit) File) (CTy.effOf SL Ans))
        (.there (.here (.drop rfl (.cons (.cons (.cons hΓ.toP)))))))
      (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))
  · -- *close*: the file's destructor, the residual `1`
    refine .effLet (A := .unit) (.right (.dead (.dead (.left (deadSplit hΓ)))))
      (fun h => absurd h SL_not_cancels)
      (fun h => absurd h (Row.not_unr_of_not_cancels SL_not_cancels))
      (.effSub SD_le_SL (.app (split_kill _).toP (d_dFile _ (kill_dead _))
        (.there (.there (.there (.here hΓ.toP)))))) ?_
    exact .effSub (RowLe.nil SL) (.ret (.sumI₂ (.var (.here (.drop rfl (.cons (.cons (.cons
      hΓ.toP))))))))

theorem SD_noDiv : ∀ o ∈ SD, o.n ≠ divEff := by
  intro o ho
  simp only [SD, List.mem_singleton] at ho
  subst ho
  decide

/-- `f ← alloc 7; t ← (λ_. loopBD, k); df ← div_fuel; df t`. -/
def fileLoop (k : UInt32) : Expr :=
  bindE (.app (.val (.prim .alloc)) (.val (Val.i32 7)))
    (bindE (.pair (.val (.lam loopBD)) (.val (Val.i32 k)))
      (bindE (.val divFuelV) (.app (.var 0) (.var 1))))

theorem d_fileLoop {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (k : UInt32) :
    CDerives Δ Γ (fileLoop k) (.comp (CTy.effOf SD Ans)) := by
  refine .bind (A := File) (deadSplit hΓ)
    (.ret (appW (.lit (.i32 7) (by cdead)) (.alloc (by cdead)))) ?_
  refine .bind (A := .tensor (.thunk (.arr .unit (CTy.effOf SL Ans))) I32) (.left (deadSplit hΓ))
    (.ret (.tensorI (.left (deadSplit hΓ)) (.thunkV rfl (.lamDead (d_loopBD hΓ)))
      (.lit (.i32 k) (.cons hΓ.toP)))) ?_
  refine .bind (.right (.dead (deadSplit hΓ)))
    (.ret (.bangE (.divFuel SD Ans SD_noDiv (.cons (.cons hΓ.toP))))) ?_
  exact .app (.left (.right (.dead (deadSplit hΓ))))
    (.force (C := .arr (.tensor (.thunk (.arr .unit (CTy.effOf (tickSig :: SD) Ans))) I32)
      (CTy.effOf SD Ans)) (.here (.cons (.cons hΓ.toP))))
    (.there (.here (.cons hΓ.toP)))

/-- `with_fs (fileLoop k)`. -/
def loopProg (k : UInt32) : Expr := withFs (fileLoop k)

theorem d_loopProg (k : UInt32) : CDerives LifeCtx.empty [] (loopProg k) (.comp (.ret Ans)) := by
  refine d_withFsG (S := []) (A := Ans) (by simp) rfl ?_
  exact d_fileLoop (.cons (.cons .nil)) k

/-- **Resource safety on the early close**, at every budget. -/
theorem loopProg_safe (k : UInt32) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (loopProg k) μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) (d_loopProg k) hs

/-- The same loop under the recording `with_fs`. -/
def loopLog (k : UInt32) : Expr := withLogCell (withFsLog (fileLoop k))

/-- The run answers `(inr (), log)`: the loop closed, its residual `1`, no cell left. -/
def closedWithLog (e : Expr) (l : UInt32) : Bool :=
  match eval e with
  | .value ⟨.pair (.inj₂ .unit) (.prim (.lit (.i32 b))), _⟩ false => b == l
  | _ => false

/-- **Closed at the first tick**: the file's destructor closes descriptor `7`. -/
theorem loop_close0 : closedWithLog (loopLog 0) 7 = true := by decide

/-- **Closed after three turns, inside `iterate`**: the step's *close*, the same destructor. -/
theorem loop_close3 : closedWithLog (loopLog 3) 7 = true := by decide

end BoCa.Fig16.LogRel.Core.LetDtor.Loop

end
