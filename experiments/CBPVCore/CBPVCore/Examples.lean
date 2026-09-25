import CBPVCore.Fundamental
import Paper.Examples.Programs

/-!
# CBPVCore — a resource program, typed in the CBPV judgment and run

`cImmBorrow` allocates a cell, borrows it immutably with `withbor` (form 1), loads through the
borrow with `withload`, and frees the cell:

    return alloc to a. return () to u. a u to r.
    return withbor to w. w r to g.
    return (thunk Λ. return (λb. return withload to wl. wl b to h.
                                 return (thunk Λ. return (λy. y)) to l. h l)) to f.
    g f to p. let (r′, t) = p in t; return free to fr. fr r′

`BoCa`'s `immBorrow` (`Paper/Examples/Programs.lean`) without its `copy`/`forget` pair, in
A-normal form.  `cImmBorrow_derives` types it at `F 1` in `CDerives`, and `cImmBorrow_runs` is its
`adequacyC` instance: from the empty memory it runs to `()` and the empty memory.
-/

namespace CBPVCore
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LSub LifeCtx LifeVar)
noncomputable section

/-! ### Context helpers -/

/-- `n` dead slots of type `1`. -/
def deadU : Nat → Ctx Ty
  | 0 => []
  | n + 1 => ⟨.unit, false⟩ :: deadU n

theorem deadU_dead : ∀ n, Ctx.Dead (deadU n)
  | 0 => .nil
  | n + 1 => .cons (deadU_dead n)

theorem liveEq_dead : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → LiveEq Γ (cbvCtx (deadU Γ.length))
  | _, .nil => .nil
  | _, .cons h => .dead (liveEq_dead h)

theorem deadSplit {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Ctx.Split Γ Γ Γ := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .dead ih

theorem dead_noLive {Γ : Ctx VTy} (h : Ctx.Dead Γ) {P : Slot VTy → Prop} :
    ∀ s ∈ Γ, s.live = true → P s := by
  induction h with
  | nil => intro s hs; cases hs
  | cons _ ih =>
      intro s hs hl
      cases hs with
      | head => exact absurd hl (by simp)
      | tail _ hs' => exact ih s hs' hl

/-! ### The program -/

/-- `M to x. N`, written `(λx. N) M`. -/
def bindE (M N : Expr) : Expr := .app (.val (.lam N)) M

/-- `Δ₁ = 'a ⊏ ⊓∅`, the context `withbor`'s callback runs in. -/
abbrev Δ₁ : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

/-- The loader's type, `∀'b ⊏ ⊓Δ₁. Imm̲ 'b 1 ⊸ ['b]['a]1`. -/
def loaderTy : Ty :=
  .all 1 Δ₁.meetOfDom (.lolli (Ty.immReborrow (.var 1) .unit) (.box (.var 1) (.box (.var 0) .unit)))

/-- The borrower's type, `∀'a ⊏ ⊓∅. Imm 'a 1 ⊸ ['a]1`. -/
def borrowerTy : Ty :=
  .all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) .unit) (.box (.var 0) .unit))

/-- `thunk Λ. return (λy. y)`. -/
def cLoader : Expr := .val (.lam (.val (.lam (.var 0))))

/-- `return withload to wl. wl b to h. return loader to l. h l`, at `b` = index 0. -/
def cBorrowBody : Expr :=
  bindE withload (bindE (.app (.var 0) (.var 1)) (bindE cLoader (.app (.var 1) (.var 0))))

/-- `thunk Λ. return (λb. body)`. -/
def cBorrower : Expr := .val (.lam (.val (.lam cBorrowBody)))

def cImmBorrow : Expr :=
  bindE (.val (.prim .alloc)) (bindE (.val .unit) (bindE (.app (.var 1) (.var 0))
    (bindE withbor (bindE (.app (.var 0) (.var 1))
      (bindE cBorrower (bindE (.app (.var 1) (.var 0))
        (.letpair (.var 0) (.seq (.var 0) (bindE (.val (.prim .free)) (.app (.var 0) (.var 2)))))))))))

/-! ### Its derivation -/

theorem d_loader {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) : CDerives Δ₁ Γ cLoader (.val (cbv loaderTy)) :=
  .thunkV rfl (.allI rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false (by decide) rfl hy)
    (dead_noLive hΓ)
    (.ret (.thunkV rfl (.lam (.ret
      (.boxI (Γ' := ⟨.unit, true⟩ :: ⟨.unit, false⟩ :: deadU Γ.length)
          (T := .box (.var 0) .unit) (.live (.dead (liveEq_dead hΓ)))
        (.boxI (Γ' := ⟨.unit, true⟩ :: ⟨.unit, false⟩ :: deadU Γ.length) (T := .unit)
          (.live (.dead (liveEq_dead hΓ))) (.var (.here (.cons hΓ)))
          (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (deadU_dead _))))
        (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (deadU_dead _)))))))))

theorem d_borrowBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ (⟨.imm (.var 0) .unit, true⟩ :: ⟨.unit, false⟩ :: Γ) cBorrowBody
      (.comp (.ret (.box (.var 0) .unit))) :=
  .bind (.right (.dead (deadSplit hΓ)))
    (.ret (.withload (a := .var 0) (T₁ := .unit) (T₂ := .box (.var 0) .unit) 1
      (.cons (.cons hΓ)) rfl nofun (by simp [LFree, Lifetime.Life.mentions])))
    (.bind (.left (.left (.dead (deadSplit hΓ))))
      (.app (.left (.right (.dead (deadSplit hΓ))))
        (.force (.here (.cons (.cons hΓ)))) (.there (.here (.cons hΓ))))
      (.bind (.right (.dead (.dead (.dead (deadSplit hΓ)))))
        (.ret (d_loader (.cons (.cons (.cons (.cons hΓ))))))
        (.app (.right (.left (.dead (.dead (.dead (deadSplit hΓ))))))
          (.force (.there (.here (.cons (.cons (.cons hΓ))))))
          (.here (.cons (.cons (.cons (.cons hΓ))))))))

theorem d_borrower {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ cBorrower (.val (cbv borrowerTy)) :=
  .thunkV rfl (.allI rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (dead_noLive hΓ) (.ret (.thunkV rfl (.lam (d_borrowBody hΓ)))))

theorem cImmBorrow_derives : CDerives LifeCtx.empty [] cImmBorrow (.comp (.ret .unit)) := by
  -- `return alloc to a`
  refine .bind .nil (.ret (.alloc (T := .unit) .nil)) ?_
  -- `return () to u`
  refine .bind (.right .nil) (.ret (.unitI (.cons .nil))) ?_
  -- `a u to r`
  refine .bind (.left (.left .nil))
    (.app (.right (.left .nil)) (.force (.there (.here .nil))) (.here (.cons .nil))) ?_
  -- `return withbor to w`
  refine .bind (.right (.dead (.dead .nil)))
    (.ret (.withbor1 (T₁ := .unit) (T₂ := .unit) 0 (by repeat constructor) rfl rfl nofun nofun)) ?_
  -- `w r to g`
  refine .bind (.left (.left (.dead (.dead .nil))))
    (.app (.left (.right (.dead (.dead .nil)))) (.force (.here (by repeat constructor)))
      (.there (.here (by repeat constructor)))) ?_
  -- `return borrower to f`
  refine .bind (.right (.dead (.dead (.dead (.dead .nil)))))
    (.ret (d_borrower (by repeat constructor))) ?_
  -- `g f to p`
  refine .bind (.left (.left (.dead (.dead (.dead (.dead .nil))))))
    (.app (.right (.left (.dead (.dead (.dead (.dead .nil))))))
      (.force (.there (.here (by repeat constructor)))) (.here (by repeat constructor))) ?_
  -- `let (r′, t) = p in`
  refine .tensorE (A := cbv (.ref .unit)) (B := .unit)
    (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))
    (.var (.here (by repeat constructor))) ?_
  -- `t;`
  refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
    (.var (.here (by repeat constructor))) ?_
  -- `return free to fr`
  refine .bind (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
    (.ret (.free (T := .unit) (by repeat constructor))) ?_
  -- `fr r′`
  exact .app (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.force (.here (by repeat constructor))) (.there (.there (.here (by repeat constructor))))

/-- **Adequacy** at a resource program: `cImmBorrow` runs from the empty memory to `()` and the
empty memory. -/
theorem cImmBorrow_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem cImmBorrow Adequacy.emptyMem (.val .unit) :=
  adequacyC cImmBorrow_derives

/-! ### A program through `!`

    return (thunk λx. return x : !U (1 ⊸ F 1)) to f.
    return copy to c. c f to p. let (f₂, f₁) = p in
    return forget to d. d f₂ to z. z;
    return f₁ to g. return () to u. g u

Promotion over the empty context, `copy` and `forget` at `!`, and dereliction. -/

/-- `U (1 ⊸ F 1)`. -/
abbrev idTy : VTy := .thunk (.arr .unit (.ret .unit))

def cBang : Expr :=
  bindE (.val (.lam (.var 0))) (bindE copy (bindE (.app (.var 0) (.var 1))
    (.letpair (.var 0) (bindE forget (bindE (.app (.var 0) (.var 1))
      (.seq (.var 0) (bindE (.var 3) (bindE (.val .unit) (.app (.var 1) (.var 0))))))))))

theorem cBang_derives : CDerives LifeCtx.empty [] cBang (.comp (.ret .unit)) := by
  -- `return (thunk λx. return x) to f`, promoted over `[]`
  refine .bind .nil (.ret (.bangThunkV (C := .arr .unit (.ret .unit)) (fun _ hs => by simp at hs) rfl
    (.lam (.ret (.var (.here .nil)))))) ?_
  -- `return copy to c`
  refine .bind (.right .nil) (.ret (.copyBang (A := idTy) (.cons .nil))) ?_
  -- `c f to p`
  refine .bind (.left (.left .nil))
    (.app (.left (.right .nil)) (.force (.here (.cons .nil))) (.there (.here .nil))) ?_
  -- `let (f₂, f₁) = p in`
  refine .tensorE (A := .bang idTy) (B := .bang idTy) (.left (.dead (.dead .nil)))
    (.var (.here (by repeat constructor))) ?_
  -- `return forget to d`
  refine .bind (.right (.right (.dead (.dead (.dead .nil)))))
    (.ret (.forgetBang (A := idTy) (by repeat constructor))) ?_
  -- `d f₂ to z`
  refine .bind (.left (.left (.right (.dead (.dead (.dead .nil))))))
    (.app (.left (.right (.dead (.dead (.dead (.dead .nil))))))
      (.force (.here (by repeat constructor))) (.there (.here (by repeat constructor)))) ?_
  -- `z;`
  refine .unitE (.left (.dead (.dead (.right (.dead (.dead (.dead .nil)))))))
    (.var (.here (by repeat constructor))) ?_
  -- `return f₁ to g`, by dereliction
  refine .bind (.dead (.dead (.dead (.left (.dead (.dead (.dead .nil)))))))
    (.ret (.bangE (.var (.there (.there (.there (.here (by repeat constructor)))))))) ?_
  -- `return () to u`
  refine .bind (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))
    (.ret (.unitI (by repeat constructor))) ?_
  -- `g u`
  exact .app (.right (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
    (.force (.there (.here (by repeat constructor)))) (.here (by repeat constructor))

theorem cBang_runs : BoCa.BoLo.Steps Adequacy.emptyMem cBang Adequacy.emptyMem (.val .unit) :=
  adequacyC cBang_derives

end
end CBPVCore
