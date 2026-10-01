import SecondClass.Restated
import Core.Examples

/-!
# SecondClass — a recursion that uses an answering capability, typed

Probe P1 of `docs/second-class-and-system-c.md` at the judgment. In a context holding one live
capability `c : Mut @a I32` (an answering handler's state, lent as in SPEC §18), the program

    bounded_fix (step, (100, (c, ())))
    step = !λp. let (self, ca) = p; let (c, u) = ca;
                t ← withswap c (λs. (s, ()));  let (c, r) = t;          -- the operation
                case self { inj₁ _ ⇒ return (c, r) | inj₂ g ⇒ (unbang g) (c, r) }

runs the operation at every level and hands the capability back. The step is `!` code: it
captures nothing, and the capability reaches each level as a component of the argument,
`A = Mut @a I32 ⊗ 1` (`envStepTy`). `recLog_derives` types it at `F (Mut @a I32 ⊗ 1)`;
`recLog_sem` is its soundness by `fundamentalC`: in every world where `c` is a live `Mut`
borrow, the recursion runs safely and hands it back.

The clause `λs. (s, ())` answers `()` and leaves the state as it is; the typing does not depend
on what the clause computes. `probes/p1-rec-log.bc` is the same shape with a counting clause,
typed by the checker and run.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.SecondClass
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The capability: the handler's state, `Mut @a I32`. -/
abbrev Cap (a : Lifetime.Life) : VTy := .mut a (.int .w32)

/-- The argument of each level: the environment and the member's argument, `Cap ⊗ 1`. -/
abbrev Arg (a : Lifetime.Life) : VTy := .tensor (Cap a) .unit

/-- The answer: the environment handed back, `F (Cap ⊗ 1)`. -/
abbrev Ans (a : Lifetime.Life) : CTy := .ret (Arg a)

/-- The clause `λs. (s, ())`, at `I32 ⊸ I32 ⊗ 1`. -/
def clauseE : Expr := .val (.lam (.pair (.var 0) (.val .unit)))

/-- The operation on the capability `c` (de Bruijn `i`): `withswap c clause`. -/
def opE (i : Nat) : Expr := .app (.app withswap (.var i)) clauseE

/-- The step's body after the self-call is decided: `inj₁ _ ⇒ (c, r)`. -/
def spentE : Expr := .pair (.var 2) (.var 1)

/-- `inj₂ g ⇒ h ← unbang g; x ← (c, r); h x`. -/
def callE : Expr :=
  bindE (.var 0) (bindE (.pair (.var 3) (.var 2)) (.app (.var 1) (.var 0)))

/-- The step's code. -/
def stepE : Expr :=
  .val (.lam (.letpair (.var 0) (.letpair (.var 0)
    (bindE (opE 1) (.letpair (.var 0) (.case (.var 6) spentE callE))))))

/-- The program, open in the capability. -/
def recLogE : Expr :=
  bindE stepE (bindE (.val (.prim .boundedFix))
    (bindE (.pair (.var 1) (.pair (.val (Val.i32 100)) (.pair (.var 2) (.val .unit))))
      (.app (.var 1) (.var 0))))

theorem clauseE_derives {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clauseE (.val (.lolli (.int .w32) (.tensor (.int .w32) .unit))) :=
  .thunkV rfl (.lam (.ret (.tensorI (.left (deadSplit hΓ))
    (.var (.here hΓ.toP)) (.unitI (.cons hΓ.toP)))))


/-- The step's code is valid at `envStepTy (Cap a) 1 (Ans a)` at any dead context. -/
theorem stepE_derives {Δ : LifeCtx} {a : Lifetime.Life} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ stepE (.val (envStepTy (Cap a) .unit (Ans a))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  -- p
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  -- ca, self, p
  refine .tensorE (.left (.right (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ.toP)))) ?_
  -- u, c, ca, self, p
  refine .bind (A := .tensor (Cap a) .unit)
    (.right (.left (.dead (.right (.dead (deadSplit hΓ)))))) ?_ ?_
  · -- `withswap c clause`, at `c` (index 1)
    refine .ret (.lolliE (A := .lolli (.int .w32) (.tensor (.int .w32) .unit))
      (.dead (.right (.dead (.dead (.dead (deadSplit hΓ)))))) ?_ ?_)
    · exact clauseE_derives (.cons (.cons (.cons (.cons (.cons hΓ)))))
    · refine .lolliE (A := Cap a) (.dead (.left (.dead (.dead (.dead (deadSplit hΓ)))))) ?_ ?_
      · exact .var (.there (.here (.cons (.cons (.cons hΓ.toP)))))
      · exact .withswap (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))
  · -- t, u, c, ca, self, p
    have hD := hΓ.toP
    refine .tensorE (.left (.right (.dead (.dead (.right (.dead (deadSplit hΓ)))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons hD))))))) ?_
    -- r, c', t, u, c, ca, self, p
    refine .sumE (.right (.right (.dead (.right (.dead (.dead (.left (.dead (deadSplit hΓ)))))))))
      (.var (.there (.there (.there (.there (.there (.there (.here (.cons hD))))))))) ?_ ?_
    · -- e, r, c', t, u, c, ca, self, p: `(c', r)`
      refine .ret (.tensorI (.right (.right (.left (.dead (.right (.dead (.dead (.dead (.dead
        (deadSplit hΓ)))))))))) ?_ ?_)
      · exact .var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))
      · exact .var (.skip rfl (.here (.cons (.cons (.drop rfl (.cons (.cons (.cons (.cons hD)))))))))
    · -- g, r, c', t, u, c, ca, self, p
      refine .bind (A := .thunk (.arr (Arg a) (Ans a)))
        (.left (.right (.right (.dead (.right (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))))
        (.ret (.bangE (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))))) ?_
      -- h, g, r, c', t, u, c, ca, self, p
      refine .bind (A := Arg a)
        (.right (.dead (.left (.left (.dead (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))))
        (.ret (.tensorI (.dead (.dead (.right (.left (.dead (.dead (.dead (.dead (.dead (.dead
          (deadSplit hΓ)))))))))))
          (.var (.there (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))))
          (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))))))
        ?_
      -- x, h, g, r, c', t, u, c, ca, self, p
      exact .app (C := Ans a) (.right (.left (.dead (.dead (.dead (.dead (.right (.dead (.dead (.dead
        (.dead (deadSplit hΓ))))))))))))
        (.force (C := .arr (Arg a) (Ans a)) (.there (.here (.cons (.cons (.cons (.cons (.cons
          (.cons (.cons (.cons (.cons hD))))))))))))
        (.here (.cons (.cons (.cons (.cons (.cons (.drop rfl (.cons (.cons (.cons (.cons hD)))))))))))

/-- **Probe P1, typed.** The recursion runs the operation on the capability at every level and
hands it back: `c : Mut @a I32 ⊢ recLogE : F (Mut @a I32 ⊗ 1)`, at every `Δ` and `a`. -/
theorem recLog_derives {Δ : LifeCtx} {a : Lifetime.Life} :
    CDerives Δ [⟨Cap a, true⟩] recLogE (.comp (Ans a)) := by
  refine .bind (A := envStepTy (Cap a) .unit (Ans a)) (.right .nil)
    (.ret (stepE_derives (.cons .nil))) ?_
  refine .bind (A := .thunk (.arr (.tensor (envStepTy (Cap a) .unit (Ans a))
      (.tensor (.int .w32) (Arg a))) (Ans a)))
    (.right (.right .nil)) (.ret (.bangE (.boundedFix (Arg a) (Ans a) (.cons (.cons .nil))))) ?_
  refine .bind (A := .tensor (envStepTy (Cap a) .unit (Ans a)) (.tensor (.int .w32) (Arg a)))
    (.right (.left (.left .nil)))
    (.ret (.tensorI (.dead (.left (.right .nil)))
      (.var (.there (.here (.cons .nil))))
      (.tensorI (.dead (.dead (.right .nil))) (.lit (.i32 100) (.cons (.cons (.cons .nil))))
        (.tensorI (.dead (.dead (.left .nil))) (.var (.there (.there (.here .nil))))
          (.unitI (.cons (.cons (.cons .nil)))))))) ?_
  exact .app (.right (.left (.dead (.dead .nil))))
    (.force (C := .arr (.tensor (envStepTy (Cap a) .unit (Ans a)) (.tensor (.int .w32) (Arg a)))
      (Ans a)) (.there (.here (.cons (.cons .nil)))))
    (.here (.cons (.cons (.cons .nil))))

/-- **Probe P1 is sound**: in every world where the capability is a live borrow, the recursion
runs safely and answers the capability with `()` (`fundamentalC`). -/
theorem recLog_sem {Δ : LifeCtx} {a : Lifetime.Life} :
    SemC Δ [⟨Cap a, true⟩] recLogE (Ans a) :=
  fundamentalC recLog_derives

end BoCa.Fig16.LogRel.Core.SecondClass
