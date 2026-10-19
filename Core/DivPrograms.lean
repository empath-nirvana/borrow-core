import Core.DivHandle
import Core.EffTier1Programs
import Core.Totality

/-!
# Core — `Div`: a loop that holds a cell, closed by `div_fuel`  `[spec §14]`

A loop whose state is a cell, closed by `div_fuel 3`, hands the cell back:

    prog  =  c ← alloc 0;
             p ← (λ_. tick () to n. case n { next → iterate (f, c) | close → inr c }, 3);
             df ← div_fuel;
             r ← df p;
             case r { inl b → b | inr c′ → free c′ }

    f c   =  ⟨ (c₁, x) ← swap c 0; (c₂, _) ← swap c₁ (x + 1); inr c₂,   c ⟩

The cell is the loop's state and its residual (`R = St = ref I32`).  The loop never finishes, so
`div_fuel 3` closes it: three answers *next* run three turns, and the close hands the cell back.
The program frees the cell and answers its content, the number of turns that ran.

* `dAt_divResidual`: a tied derivation at `ΞDiv`, the effect context of `Div` alone, with `iterate`
  and `div_fuel` at their rules.
* `divResidual_runs`: every run continues to a value (`total_every_run`).  `Backend/Kernel.lean`
  compiles it as `div-residual`; each stage prints `3` and `live 0`.
* `divFuel_every_run`: `div_fuel (t, k)` of any closed callback `t` at the row of `Div`, every
  run continues to a value.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivPrograms
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LifeCtx)

/-! ### The program -/

/-- The effect context of `Div` alone. -/
def ΞDiv : EffCtx := fun n => if n = divEff then [(.lin, .unit, nextTy)] else []

abbrev I : VTy := .int .w32
abbrev St : VTy := .ref I
abbrev Sg : Row := [tickSig]
/-- The loop's answer, `B ⊕ R` at `B = I32`, `R = ref I32`. -/
abbrev Ans : VTy := .sum I St

def i32E (n : UInt32) : Expr := .val (Val.i32 n)

/-- `x + 1`, at the variable `x`. -/
def succE (x : Nat) : Expr :=
  .app (.val (.prim (.host (.bin .w32 .add)))) (.pair (.var x) (i32E 1))

/-- The step's first observation, the cell `c` at `2` under `⟨·,·⟩`'s binders:
`(c₁, x) ← swap c 0; (c₂, _) ← swap c₁ (x + 1); inr c₂`. -/
def nextB : Expr :=
  .letpair (.app (.app swap (.var 2)) (i32E 0))
    (.letpair (.app (.app swap (.var 1)) (succE 0)) (.inj₂ (.var 1)))

/-- The step `λc. ⟨nextB, c⟩`. -/
def stepV : Val := .lam (withPair nextB (.var 2))

/-- The loop's body under its dead binder (`0`), the cell at `1`:
`tick () to n. case n { next → it ← iterate; p ← (f, c); it p | close → inr c }`. -/
def loopB : Expr :=
  .app (.val (.lam (.case (.var 0)
      (bindE (.val (.prim .iterate)) (bindE (.pair (.val stepV) (.var 4)) (.app (.var 1) (.var 0))))
      (.inj₂ (.var 3)))))
    tickE

/-- The end: `case r { inl b → b | inr c′ → free c′ }`. -/
def finB : Expr := .case (.var 0) (.var 0) (.app (.val (.prim .free)) (.var 0))

/-- **The program.** -/
def divResidual : Expr :=
  bindE (.app (.val (.prim .alloc)) (i32E 0))
    (bindE (.pair (.val (.lam loopB)) (i32E 3))
      (bindE (.val divFuelV)
        (bindE (.app (.var 0) (.var 1)) finB)))

/-! ### Its derivation -/

theorem rowAt_Sg : RowAt ΞDiv Sg := by
  intro n i o hf
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  simp only [List.mem_singleton] at hm
  subst hm
  refine ⟨by decide, by simp [ΞDiv, tickSig], ?_⟩
  simp [ΞDiv, tickSig]

theorem find_Sg : Row.find Sg tickSig.n tickSig.i = some tickSig := by
  simp [Row.find, List.find?, tickSig]

theorem int_persistent : (I : VTy).Persistent := rfl
theorem unit_persistent : (VTy.unit).Persistent := rfl

variable {Δ : LifeCtx}

/-- The step at `!U(St ⊸ F_{tick}(B ⊕ St) & F_{tick} R)`. -/
theorem dAt_stepV : CDerivesAt ΞDiv Δ [] (.val stepV) (.val (iterStepTy Sg St I St)) := by
  refine .bangThunkV (fun _ h => absurd h List.not_mem_nil) rfl (.lam (.withI ?_ ?_))
  · -- the first observation
    refine .tensorE (.dead (.dead (.left .nil)))
      (.lolliE (.dead (.dead (.right .nil))) (.lit (.i32 0) (.cons (.cons (.cons .nil))))
        (.lolliE (.dead (.dead (.left .nil))) (.var (.there (.there (.here .nil))))
          (.swap (A := I) (B := I) (.cons (.cons (.cons .nil)))))) ?_
    refine .tensorE (.left (.left (.dead (.dead (.dead .nil)))))
      (.lolliE (.left (.right (.dead (.dead (.dead .nil)))))
        (.lolliE (.left (.dead (.dead (.dead (.dead .nil)))))
          (.tensorI (.left (.dead (.dead (.dead (.dead .nil)))))
            (.var (.here (.cons (.cons (.cons (.cons .nil))))))
            (.lit (.i32 1) (.cons (.cons (.cons (.cons (.cons .nil)))))))
          (.bangE (.hostOp (.bin .w32 .add) (.cons (.cons (.cons (.cons (.cons .nil))))))))
        (.lolliE (.dead (.left (.dead (.dead (.dead .nil)))))
          (.var (.there (.here (.cons (.cons (.cons .nil))))))
          (.swap (A := I) (B := I) (.cons (.cons (.cons (.cons (.cons .nil))))))))
      ?_
    exact .effSub (RowLe.nil Sg) (.ret (.sumI₂ (.var (.skip int_persistent
      (.here (.cons (.cons (.cons (.cons (.cons .nil))))))))))
  · -- the residual
    exact .effSub (RowLe.nil Sg) (.ret (.var (.there (.there (.here .nil)))))

/-- The loop's body at `F_{tick}(B ⊕ R)`, the cell at `1`. -/
theorem dAt_loopB :
    CDerivesAt ΞDiv Δ [⟨.unit, false⟩, ⟨St, true⟩] loopB (.comp (CTy.effOf Sg Ans)) := by
  refine .effLet (A := nextTy) (.dead (.right .nil))
    (fun ⟨o, ho, hq⟩ => by simp [tickSig] at ho; subst ho; exact absurd rfl hq)
    (fun ⟨o, ho, hq⟩ => by simp [tickSig] at ho; subst ho; cases hq)
    (.effPerform (o := tickSig) rowAt_Sg find_Sg rfl (.unitI (.cons (.cons .nil)))) ?_
  refine .sumE (.left (.dead (.right .nil))) (.var (.here (.cons (.cons .nil)))) ?_ ?_
  · -- *next*: `iterate (f, c)`
    refine .bind (.right (.dead (.dead (.right .nil))))
      (.ret (.bangE (.iterate Sg St I St rowAt_Sg (Row.divB_tick [])
        (.cons (.cons (.cons (.cons .nil))))))) ?_
    refine .bind (.right (.right (.dead (.dead (.left .nil)))))
      (.ret (.tensorI (.dead (.dead (.dead (.dead (.right .nil)))))
        (dAt_stepV.append_dead (Γ' := [⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩, ⟨_, false⟩,
          ⟨_, false⟩]) (.cons (.cons (.cons (.cons (.cons .nil))))))
        (.var (.there (.there (.there (.there (.here .nil)))))))) ?_
    exact .app (.right (.left (.left (.dead (.dead (.dead .nil))))))
      (.force (C := .arr (.tensor (iterStepTy Sg St I St) St) (CTy.effOf Sg (.sum I St)))
        (.there (.here (.drop unit_persistent (.cons (.cons (.cons .nil)))))))
      (.here (.cons (.cons (.cons (.cons (.cons .nil))))))
  · -- *close*: `inr c`
    exact .effSub (RowLe.nil Sg) (.ret (.sumI₂ (.var (.skip unit_persistent
      (.there (.there (.here .nil)))))))

/-- **The program is typed, tied to `ΞDiv`**, at `F I32`. -/
theorem dAt_divResidual : CDerivesAt ΞDiv Δ [] divResidual (.comp (.ret I)) := by
  refine .bind .nil (.ret (.lolliE .nil (.lit (.i32 0) .nil) (.alloc (A := I) .nil))) ?_
  refine .bind (.left .nil)
    (.ret (.tensorI (.left .nil) (.thunkV rfl (.lamDead dAt_loopB)) (.lit (.i32 3) (.cons .nil))))
    ?_
  refine .bind (.right (.dead .nil))
    (.ret (.bangE (.divFuel [] Ans (by simpa using rowAt_Sg) (fun _ h => absurd h List.not_mem_nil)
      (.cons (.cons .nil))))) ?_
  refine .bind (.left (.left (.dead .nil)))
    (.app (.left (.right (.dead .nil)))
      (.force (C := .arr (.tensor (.thunk (.arr .unit (CTy.effOf (tickSig :: []) Ans))) I)
        (CTy.effOf [] Ans)) (.here (.cons (.cons .nil))))
      (.there (.here (.cons .nil)))) ?_
  refine .sumE (.left (.dead (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil)))))
    (.ret (.var (.here (.cons (.cons (.cons (.cons .nil))))))) ?_
  exact .ret (.lolliE (.left (.dead (.dead (.dead (.dead .nil)))))
    (.var (.here (.cons (.cons (.cons (.cons .nil))))))
    (.free (.cons (.cons (.cons (.cons (.cons .nil)))))))

theorem d_divResidual : CDerives LifeCtx.empty [] divResidual (.comp (.ret I)) :=
  dAt_divResidual.toCDerives

/-- **The program runs**: every run, under every allocator, continues to a value of `I32` (no run
is stuck, and none goes on forever).  `[spec §14]` -/
theorem divResidual_runs {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem divResidual μ₁ e₁) :
    ∃ (μ' : BoCa.BoLo.Heap) (v : Val), BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ μ' (.val v) :=
  total_every_run d_divResidual hs

/-! ### `div_fuel` of a closed computation at a row holding `Div` -/

/-- `df ← div_fuel; df (t, k)`. -/
def fuelRun (t : Expr) (k : UInt32) : Expr :=
  bindE (.pair t (i32E k)) (bindE (.val divFuelV) (.app (.var 0) (.var 1)))

/-- **`div_fuel` closes a computation that ticks**: for a closed callback `t` at the row of `Div`
alone and every budget `k`, every run of `div_fuel (t, k)` from the empty memory continues to a
value.  The relation at `t ()`'s row is `cwp` (`effWp`); `div_fuel`'s rule and the Fundamental
Property carry it to `F A`, and `total_every_run` reads it there.  `[spec §14]` -/
theorem divFuel_every_run {t : Expr} {A : VTy}
    (ht : CDerives LifeCtx.empty [] t (.val (.thunk (.arr .unit (CTy.effOf [tickSig] A)))))
    (k : UInt32) {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (fuelRun t k) μ₁ e₁) :
    ∃ (μ' : BoCa.BoLo.Heap) (v : Val), BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ μ' (.val v) := by
  have hd : CDerives LifeCtx.empty [] (fuelRun t k) (.comp (.ret A)) := by
    refine .bind .nil (.ret (.tensorI .nil ht (.lit (.i32 k) .nil))) ?_
    refine .bind (.right .nil)
      (.ret (.bangE (.divFuel [] A (fun _ h => absurd h List.not_mem_nil) (.cons .nil)))) ?_
    exact .app (.left (.right .nil))
      (.force (C := .arr (.tensor (.thunk (.arr .unit (CTy.effOf (tickSig :: []) A))) I)
        (CTy.effOf [] A)) (.here (.cons .nil)))
      (.there (.here .nil))
  exact total_every_run hd hs

end BoCa.Fig16.LogRel.Core.DivPrograms

end
