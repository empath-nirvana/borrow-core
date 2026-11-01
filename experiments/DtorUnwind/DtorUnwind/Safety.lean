import DtorUnwind.Files
import Core.EffMachine

/-!
# Resource safety

The paper's Theorem 12 reads resource safety of the resource CBPV off the translated term: the
translation is linear, and the linear calculus's free-list ends as it began (up to a permutation;
exactly, without `move`). Here the same reading is `adequacyD` at the derivation: `[let-dtor]` is a
`CDerives` derivation (no rule added), so every closed program it types is covered.

**`resourceSafety`.** For every closed `CDerives` program at a persistent answer, every run from
the empty memory, under every allocator:

1. continues to a value at the empty memory: every cell it allocated is freed;
2. never sticks; in particular, every `free ℓ` it reaches at an evaluation position finds `ℓ`
   allocated (`step1_free_iff`), and its step removes `ℓ`, so no cell is freed twice.

An allocation picks a location the memory does not hold (`step1_alloc_iff`) and a release removes
the one it frees, so (1) and (2) say each allocation is released exactly once. The exits are
the program's: a normal return, a raise caught by a handler (`to_result`), a cancel (a raise,
§29a), an early close of a loop (a resume with *close*, §14). Each is a run of a closed program.

**Order.** The order of the releases on the unwind is `drop_ctx`'s: last bound first
(`dropCtxE_some`). `fsRaise_order`/`fsReturn_order` run the file program with a `with_fs` that
records the descriptors it closes: `21`, `f₂` then `f₁`, on both exits. A program-wide LIFO
theorem needs the paper's ordered judgment (`⊢ₒ`, Fig. 4–5, Lemma 8, Theorem 9), which is not
transcribed: `CDerives` has exchange (`Ctx.SplitP` interleaves freely), the paper's `move`-ful
calculus, whose Theorem 10 gives the multiset statement (1).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (adequacyD_obs raiseU toResult)
open BoCa.Fig16.LogRel.Core.DtorUnwind.Files
open BoCa.BoLo (Heap Steps Step1 Kont freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Resource safety** of every closed program at a persistent answer: every run from the empty
memory continues to a value at the empty memory (every cell allocated is freed), and every
release it reaches finds its cell allocated (none is freed twice).  -/
theorem resourceSafety {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs hA h hs
  refine ⟨⟨v, hv⟩, fun K ℓ he => ?_⟩
  cases hv with
  | refl =>
      have hc : IsVal (K.plug (freeE (.val (Val.loc ℓ)))) := by rw [← he]; exact v.2
      have := K.isVal_of_plug hc
      cases this
  | more hst _ =>
      rw [he] at hst
      obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).mp hst
      exact ⟨u, hu⟩

/-- **The file program, error exit**: resource safety at `fs_prog (raise ())`. -/
theorem fsRaise_safe {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem fsRaise μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_fsRaise hs

/-- **The file program, normal exit.** -/
theorem fsReturn_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem fsReturn μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_fsReturn hs

/-! ### The order of the closes, by `eval`

The same body `twoFiles 4 M` under a `with_fs` whose `close` clause records the descriptor in a
log cell at location `0`, `log := log · 10 + n`, then resumes. -/

def litE (n : UInt32) : Expr := (Val.i32 n).1

def binE (o : BinOp) (a b : Expr) : Expr := .app (.val (.prim (.host (.bin .w32 o)))) (.pair a b)

def loadE (l : Expr) : Expr := .app (.val (.prim .load)) l

def storeE (l v : Expr) : Expr := .app (.app (.val (.prim .store)) l) v

/-- `λ(n, κ). log := log · 10 + n; κ.1 ()`. -/
def clFLog : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (storeE (.val (Val.loc 0))
        (binE .add (binE .mul (loadE (.val (Val.loc 0))) (litE 10)) (.var 1)))
      (.app (.app (.var 1) (.val (.inj₁ .unit))) (.val .unit)))))

/-- `with_fs` that records the closes. -/
def withFsLog (e : Expr) : Expr :=
  bindE (.pair clFLog (.val .unit)) (bindE hrF (hndTerm 4 [.lin] 0 1 e))

/-- `log ← alloc 0; r ← P; (r, free log)`. -/
def withLogCell (P : Expr) : Expr :=
  bindE (.app (.val (.prim .alloc)) (litE 0))
    (bindE P (.pair (.var 0) (.app (.val (.prim .free)) (.val (Val.loc 0)))))

/-- The run answers `(r, log)` with `log` the given number and no cell left. -/
def logIs (e : Expr) (l : UInt32) : Bool :=
  match eval e with
  | .value ⟨.pair _ (.prim (.lit (.i32 b))), _⟩ false => b == l
  | _ => false

def fsRaiseLog : Expr := withLogCell (toResult (withFsLog (twoFiles 4 raiseU)))
def fsReturnLog : Expr := withLogCell (toResult (withFsLog (twoFiles 4 (.val .unit))))

/-- **On the raise, `f₂` is closed before `f₁`**, and no cell is left. -/
theorem fsRaise_order : logIs fsRaiseLog 21 = true := by decide

/-- **On the normal exit, the same order.** -/
theorem fsReturn_order : logIs fsReturnLog 21 = true := by decide

end BoCa.Fig16.LogRel.Core.DtorUnwind

end
