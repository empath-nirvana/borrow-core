import Core.Fundamental
import Paper.Examples.Derivations

/-!
# Core — programs, typed in the CBPV judgment and run  `[spec §3]`

* `cImmBorrow`: `experiments/CBPVCore`'s program, re-derived in this judgment.
* `cBang`: a `!` value used twice and dropped, with no `copy` or `forget` (`[spec §10]`).
* `cRecBorrow`: an immutable borrow of a cell holding a record of methods
  `M = U (F 1 & F 1)`.  The borrower receives `Imm 'a M`, loads through it (`Imm̲ 'b M = Unk`)
  and forgets the view; after the borrow ends the cell is freed and a method is called:

      return (thunk ⟨return (), return ()⟩) to m.
      return alloc to a. a m to r.
      return withbor to w. w r to g.
      return (thunk Λ. return (λb. return withload to wl. wl b to h.
                                   return (thunk Λ. return (λy. return forget to fg.
                                                                 fg y to z. return z)) to l.
                                   h l)) to f.
      g f to p. let (r′, t) = p in t; return free to fr. fr r′ to m′. π₁ (force m′)

  `Imm @a M` has no preimage under the call-by-value translation, so `experiments/CBPVCore`'s
  relation gives it no inhabitant (`vC_imm_outside_image`) and its `withbor`/`withload` are
  not available at `M`.  Here the program derives at `F 1` (`cRecBorrow_derives`) and runs to
  `()` from the empty memory (`cRecBorrow_runs`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Context helpers -/

theorem deadSplit {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Ctx.SplitP Γ Γ Γ := by
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

/-- `Δ ⊨ Γ ⊐ @a` for a context with one live slot, at a type outliving `@a`. -/
theorem CtxOutlives.solo {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (ha : Δ.Defines a) (hA : VOutlives Δ a A) (h : Ctx.Dead Γ) :
    CtxOutlives Δ (⟨A, true⟩ :: Γ) a := by
  refine ⟨ha, ?_⟩
  intro s hs hl
  cases hs with
  | head => exact hA
  | tail _ hs' => exact dead_noLive (P := fun s => VOutlives Δ a s.ty) h s hs' hl

/-! ### `cImmBorrow` -/

/-- `Δ₁ = 'a ⊏ ⊓∅`, the context `withbor`'s callback runs in. -/
abbrev Δ₁ : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

/-- The loader's type, `∀'b ⊏ ⊓Δ₁. Imm̲ 'b A ⊸ ['b]['a]1`. -/
def loaderTy (A : VTy) : VTy :=
  .all 1 Δ₁.meetOfDom (.lolli (VTy.immReborrow (.var 1) A) (.box (.var 1) (.box (.var 0) .unit)))

/-- The borrower's type, `∀'a ⊏ ⊓∅. Imm 'a A ⊸ ['a]1`. -/
def borrowerTy (A : VTy) : VTy :=
  .all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) A) (.box (.var 0) .unit))

/-- `thunk Λ. return (λy. y)`. -/
def cLoader : Expr := .val (.lam (.val (.lam (.var 0))))

/-- `return withload to wl. wl b to h. return L to l. h l`, at `b` = index 0. -/
def borrowBody (L : Expr) : Expr :=
  bindE withload (bindE (.app (.var 0) (.var 1)) (bindE L (.app (.var 1) (.var 0))))

/-- `thunk Λ. return (λb. body)`. -/
def borrower (L : Expr) : Expr := .val (.lam (.val (.lam (borrowBody L))))

def cImmBorrow : Expr :=
  bindE (.val (.prim .alloc)) (bindE (.val .unit) (bindE (.app (.var 1) (.var 0))
    (bindE withbor (bindE (.app (.var 0) (.var 1))
      (bindE (borrower cLoader) (bindE (.app (.var 1) (.var 0))
        (.letpair (.var 0) (.seq (.var 0) (bindE (.val (.prim .free)) (.app (.var 0) (.var 2)))))))))))

theorem d_loader {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) : CDerives Δ₁ Γ cLoader (.val (loaderTy .unit)) :=
  .thunkV rfl (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false (by decide) rfl hy)
    (dead_noLive hΓ)
    (.ret (.thunkV rfl (.lam (.ret
      (.boxI
        (.boxI (.var (.here (.cons hΓ)))
          (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons hΓ)))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons hΓ))))))))

/-- The borrower's body, at payload `A`, from a loader `L` at `loaderTy A`. -/
theorem d_borrowBody {Γ : Ctx VTy} {A : VTy} {L : Expr} (hΓ : Ctx.Dead Γ)
    (hA : ¬ VFree 1 A)
    (hL : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' → CDerives Δ₁ Γ' L (.val (loaderTy A))) :
    CDerives Δ₁ (⟨.imm (.var 0) A, true⟩ :: ⟨.unit, false⟩ :: Γ) (borrowBody L)
      (.comp (.ret (.box (.var 0) .unit))) :=
  .bind (.right (.dead (deadSplit hΓ)))
    (.ret (.withload (a := .var 0) (A := A) (B := .box (.var 0) .unit) 1
      (.cons (.cons hΓ)) rfl hA (by simp [VFree, Lifetime.Life.mentions])))
    (.bind (.left (.left (.dead (deadSplit hΓ))))
      (.app (.left (.right (.dead (deadSplit hΓ))))
        (.force (.here (.cons (.cons hΓ)))) (.there (.here (.cons hΓ))))
      (.bind (.right (.dead (.dead (.dead (deadSplit hΓ)))))
        (.ret (hL (.cons (.cons (.cons (.cons hΓ))))))
        (.app (.right (.left (.dead (.dead (.dead (deadSplit hΓ))))))
          (.force (.there (.here (.cons (.cons (.cons hΓ))))))
          (.here (.cons (.cons (.cons (.cons hΓ))))))))

theorem d_borrower {Γ : Ctx VTy} {A : VTy} {L : Expr} (hΓ : Ctx.Dead Γ) (hA : ¬ VFree 1 A)
    (hL : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' → CDerives Δ₁ Γ' L (.val (loaderTy A))) :
    CDerives LifeCtx.empty Γ (borrower L) (.val (borrowerTy A)) :=
  .thunkV rfl (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (dead_noLive hΓ) (.ret (.thunkV rfl (.lam (d_borrowBody hΓ hA hL)))))

theorem cImmBorrow_derives : CDerives LifeCtx.empty [] cImmBorrow (.comp (.ret .unit)) := by
  -- `return alloc to a`
  refine .bind .nil (.ret (.alloc (A := .unit) .nil)) ?_
  -- `return () to u`
  refine .bind (.right .nil) (.ret (.unitI (.cons .nil))) ?_
  -- `a u to r`
  refine .bind (.left (.left .nil))
    (.app (.right (.left .nil)) (.force (.there (.here .nil))) (.here (.cons .nil))) ?_
  -- `return withbor to w`
  refine .bind (.right (.dead (.dead .nil)))
    (.ret (.withbor1 (A := .unit) (B := .unit) 0 (by repeat constructor) rfl
      (fun _ h => by simp [VFree] at h) (by simp [VFree]) (by simp [VFree]))) ?_
  -- `w r to g`
  refine .bind (.left (.left (.dead (.dead .nil))))
    (.app (.left (.right (.dead (.dead .nil)))) (.force (.here (by repeat constructor)))
      (.there (.here (by repeat constructor)))) ?_
  -- `return borrower to f`
  refine .bind (.right (.dead (.dead (.dead (.dead .nil)))))
    (.ret (d_borrower (by repeat constructor) (by simp [VFree]) d_loader)) ?_
  -- `g f to p`
  refine .bind (.left (.left (.dead (.dead (.dead (.dead .nil))))))
    (.app (.right (.left (.dead (.dead (.dead (.dead .nil))))))
      (.force (.there (.here (by repeat constructor)))) (.here (by repeat constructor))) ?_
  -- `let (r′, t) = p in`
  refine .tensorE (A := .ref .unit) (B := .unit)
    (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))
    (.var (.here (by repeat constructor))) ?_
  -- `t;`
  refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
    (.var (.here (by repeat constructor))) ?_
  -- `return free to fr`
  refine .bind (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
    (.ret (.free (A := .unit) (by repeat constructor))) ?_
  -- `fr r′`
  exact .app (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.force (.here (by repeat constructor))) (.there (.there (.here (by repeat constructor))))

theorem cImmBorrow_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem cImmBorrow Adequacy.emptyMem (.val .unit) :=
  adequacyC cImmBorrow_derives

/-! ### `cBang` -/

/-- `U (1 ⊸ F 1)`. -/
abbrev idTy : VTy := .thunk (.arr .unit (.ret .unit))

/-- `return !(thunk λx. x) to f. f to g₁. g₁ () to r. r; f to g₂. g₂ ()`: `f : !U(1 ⊸ F 1)` is
used twice with no `copy`, and is dropped at the last call with no `forget`.  `[spec §10]` -/
def cBang : Expr :=
  bindE (.val (.lam (.var 0))) (bindE (.var 0) (bindE (.val .unit) (bindE (.app (.var 1) (.var 0))
    (.seq (.var 0) (bindE (.var 3) (bindE (.val .unit) (.app (.var 1) (.var 0))))))))

theorem cBang_derives : CDerives LifeCtx.empty [] cBang (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.bangThunkV (C := .arr .unit (.ret .unit)) (fun _ hs => by simp at hs) rfl
    (.lam (.ret (.var (.here .nil)))))) ?_
  -- `f to g₁`: `f` goes to both sides.
  refine .bind (.dup rfl .nil) (.ret (.bangE (.var (.here .nil)))) ?_
  refine .bind (.right (.right .nil)) (.ret (.unitI (.cons (.cons .nil)))) ?_
  refine .bind (.left (.left (.right .nil)))
    (.app (.right (.left (.dead .nil))) (.force (.there (.here (.cons .nil))))
      (.here (.cons (.cons .nil)))) ?_
  refine .unitE (.left (.dead (.dead (.right .nil)))) (.var (.here (.cons (.cons (.cons .nil))))) ?_
  -- `f to g₂`: `f` goes to both sides again.
  refine .bind (.dead (.dead (.dead (.dup rfl .nil))))
    (.ret (.bangE (.var (.there (.there (.there (.here .nil))))))) ?_
  refine .bind (.right (.dead (.dead (.dead (.right .nil)))))
    (.ret (.unitI (.cons (.cons (.cons (.cons (.cons .nil))))))) ?_
  -- `g₂ ()`: `f` is dropped.
  exact .app (.right (.left (.dead (.dead (.dead (.left .nil))))))
    (.force (.there (.here (.cons (.cons (.cons (.drop rfl .nil)))))))
    (.here (.cons (.cons (.cons (.cons (.cons .nil))))))

theorem cBang_runs : BoCa.BoLo.Steps Adequacy.emptyMem cBang Adequacy.emptyMem (.val .unit) :=
  adequacyC cBang_derives

/-! ### `cRecBorrow`: a borrowed record of methods -/

/-- `M = U (F 1 & F 1)`, a record of two methods. -/
abbrev methodsTy : VTy := .thunk (.amp (.ret .unit) (.ret .unit))

/-- The loaded view of the record is `Unk`. -/
theorem immReborrow_methodsTy (b : Lifetime.Life) : methodsTy.immReborrow b = .unk := rfl

/-- `thunk ⟨return (), return ()⟩`. -/
def cMethods : Expr := withPair (.val .unit) (.val .unit)

/-- `thunk Λ. return (λy. return forget to fg. fg y to z. return z)`. -/
def cRecLoader : Expr :=
  .val (.lam (.val (.lam (bindE forget (bindE (.app (.var 0) (.var 1)) (.var 0))))))

def cRecBorrow : Expr :=
  bindE cMethods (bindE (.val (.prim .alloc)) (bindE (.app (.var 0) (.var 1))
    (bindE withbor (bindE (.app (.var 0) (.var 1))
      (bindE (borrower cRecLoader) (bindE (.app (.var 1) (.var 0))
        (.letpair (.var 0) (.seq (.var 0) (bindE (.val (.prim .free))
          (bindE (.app (.var 0) (.var 2)) (.app (.var 0) (.val (.inj₁ .unit)))))))))))))

theorem methodsTy_closed (x : LifeVar) : ¬ VFree x methodsTy := by
  simp [VFree, CFree]

theorem d_methods {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ cMethods (.val methodsTy) :=
  .thunkV rfl (.withI (.ret (.unitI (.cons (.cons hΓ)))) (.ret (.unitI (.cons (.cons hΓ)))))

/-- The loader at `M`: it receives `Imm̲ 'b M = Unk` and forgets it. -/
theorem d_recLoader {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ Γ cRecLoader (.val (loaderTy methodsTy)) :=
  .thunkV rfl (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false (by decide) rfl hy)
    (dead_noLive hΓ)
    (.ret (.thunkV rfl (.lam
      (.bind (.right (.dead (deadSplit hΓ))) (.ret (.forgetUnk (.cons (.cons hΓ))))
        (.bind (.left (.left (.dead (deadSplit hΓ))))
          (.app (.left (.right (.dead (deadSplit hΓ))))
            (.force (.here (.cons (.cons hΓ)))) (.there (.here (.cons hΓ))))
          (.ret (.boxI
            (.boxI (.var (.here (.cons (.cons (.cons hΓ)))))
              (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (.cons (.cons hΓ)))))
            (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit
              (.cons (.cons (.cons hΓ))))))))))))

theorem cRecBorrow_derives : CDerives LifeCtx.empty [] cRecBorrow (.comp (.ret .unit)) := by
  -- `return (thunk ⟨return (), return ()⟩) to m`
  refine .bind .nil (.ret (d_methods .nil)) ?_
  -- `return alloc to a`
  refine .bind (.right .nil) (.ret (.alloc (A := methodsTy) (.cons .nil))) ?_
  -- `a m to r`
  refine .bind (.left (.left .nil))
    (.app (.left (.right .nil)) (.force (.here (.cons .nil))) (.there (.here .nil))) ?_
  -- `return withbor to w`
  refine .bind (.right (.dead (.dead .nil)))
    (.ret (.withbor1 (A := methodsTy) (B := .unit) 0 (by repeat constructor) rfl
      (fun y h => absurd h (methodsTy_closed y)) (methodsTy_closed 0) (by simp [VFree]))) ?_
  -- `w r to g`
  refine .bind (.left (.left (.dead (.dead .nil))))
    (.app (.left (.right (.dead (.dead .nil)))) (.force (.here (by repeat constructor)))
      (.there (.here (by repeat constructor)))) ?_
  -- `return borrower to f`
  refine .bind (.right (.dead (.dead (.dead (.dead .nil)))))
    (.ret (d_borrower (by repeat constructor) (methodsTy_closed 1) d_recLoader)) ?_
  -- `g f to p`
  refine .bind (.left (.left (.dead (.dead (.dead (.dead .nil))))))
    (.app (.right (.left (.dead (.dead (.dead (.dead .nil))))))
      (.force (.there (.here (by repeat constructor)))) (.here (by repeat constructor))) ?_
  -- `let (r′, t) = p in`
  refine .tensorE (A := .ref methodsTy) (B := .unit)
    (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))
    (.var (.here (by repeat constructor))) ?_
  -- `t;`
  refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
    (.var (.here (by repeat constructor))) ?_
  -- `return free to fr`
  refine .bind (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
    (.ret (.free (A := methodsTy) (by repeat constructor))) ?_
  -- `fr r′ to m′`
  refine .bind (.left (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.app (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
      (.force (.here (by repeat constructor))) (.there (.there (.here (by repeat constructor)))))
    ?_
  -- `π₁ (force m′)`
  exact .proj₁ (.force (C := .amp (.ret .unit) (.ret .unit)) (.here (by repeat constructor)))

/-- **Adequacy** at the borrowed record: `cRecBorrow` runs from the empty memory to `()` and
the empty memory. -/
theorem cRecBorrow_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem cRecBorrow Adequacy.emptyMem (.val .unit) :=
  adequacyC cRecBorrow_derives

/-! ### `∀E` at a computation type that is not an `F`

    return (thunk Λ. λy. return y) to f.     f : U (∀'b ⊏ ⊓∅. ['b]1 ⊸ F 1)
    return () to u.                          u : ['a]1
    (force f) [] u

at `Δ₁ = 'a ⊏ ⊓∅`: the instance `[]` is at `C = ['b]1 ⊸ F 1`, and `C['a/'b] = ['a]1 ⊸ F 1`
types the application.  The program is open in `'a`, so adequacy does not apply; its semantic
judgment is `fundamentalC` of the derivation. -/

/-- `∀'b ⊏ ⊓∅. ['b]1 ⊸ F 1`. -/
abbrev polyC : CTy := .all 1 LifeCtx.empty.meetOfDom (.arr (.box (.var 1) .unit) (.ret .unit))

def cInst : Expr :=
  bindE (.val (.lam (.val (.lam (.var 0)))))
    (bindE (.val .unit) (.app (.app (.var 1) (.val .unit)) (.var 0)))

theorem cInst_derives : CDerives Δ₁ [] cInst (.comp (.ret .unit)) := by
  -- `return (thunk Λ. λy. return y) to f`
  refine .bind .nil (.ret (.thunkV (C := polyC) rfl
    (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false (Δ := Δ₁) (by decide) rfl hy)
      (fun _ hs => by simp at hs)
      (.lam (.ret (.boxE (.var (.here (.cons .nil))))))))) ?_
  -- `return () to u`, boxed at `'a`
  refine .bind (.right .nil) (.ret (.boxI (a := .var 0) (.unitI (.cons .nil))
    ⟨LifeCtx.defines_of_wf rfl, dead_noLive (P := fun s => VOutlives Δ₁ (.var 0) s.ty)
      (.cons .nil)⟩)) ?_
  -- `(force f) [] u`
  exact .app (.right (.left .nil))
    (.allE (a := .var 0) (.force (C := polyC) (.there (.here .nil))) (fun _ hδ => hδ 0 _ rfl))
    (.here (.cons .nil))

theorem cInst_sem : SemC Δ₁ [] cInst (.ret .unit) := fundamentalC cInst_derives

end BoCa.Fig16.LogRel.Core

end
