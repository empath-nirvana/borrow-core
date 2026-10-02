import FnMut.Programs

/-!
# FnMut — a borrowed closure passed on, at any depth (requirement 2)

Under the borrow `'w` of the counter (`Counter.lean`), `M = Mut 'w ([@⊤] U(FnMut^⊤ I32 I32))`:

* `twiceV : !U(M ⊸ F(M ⊗ I32))` calls through the borrow twice;
* `reV : !U(M ⊸ F(M ⊗ I32))` reborrows it at a fresh `'v ⊏ 'w` (`withbor`'s third form,
  Rust's `&mut *m`) and calls through the reborrow, keeping `m`;
* `passF 0 = λm. reV m to (m, x). twiceV m to (m, y). (m, x + y)`, and
  `passF (n + 1) = λm. passF n m`: the borrow handed on through `n` more functions.

`d_passF` types `passF n` at every `n`, by induction: the borrowed closure is an ordinary value
of an ordinary type, so passing it on is application and nothing bounds the depth.
`passProg n` lends the counter to `passF n`; at `n = 3` the interpreter returns `3 + (4 + 6) =
13` with no cell left, so all three calls reached the one closure state through three functions
and a reborrow.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A closed derivation is one at every consumed context. -/
theorem weak0 {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ [] e j)
    (hΓ : Ctx.Dead Γ) : CDerives Δ Γ e j := by
  simpa using h.append_dead hΓ

/-- Call through `Mut` at the split by the argument. -/
theorem callMutW {Δ : LifeCtx} {Γ : Ctx VTy} {a c : Lifetime.Life} {A B : VTy} {i j : Nat}
    (hA : A.Cl 0) (hm : Ctx.SoloP (part (.var j) 0 Γ).2 i (.mut a (fnBox c A B)))
    (ha : Ctx.Solo (part (.var j) 0 Γ).1 j A) :
    CDerives Δ Γ (callMutE i j) (.val (.tensor (.mut a (fnBox c A B)) B)) :=
  d_callMut hA (part_split (.var j) 0 Γ).toP hm ha

/-- The borrowed counter. -/
abbrev MC : VTy := .mut (.var 1) PC

/-- A function on the borrowed counter, `!U(M ⊸ F(M ⊗ I32))`. -/
abbrev passTy : VTy := .bang (.lolli MC (.tensor MC .i32))

/-! ### Two calls through the borrow -/

def twiceV : Val :=
  .lam (elet (i32E 1) (.letpair (callMutE 1 0)
    (elet (i32E 2) (.letpair (callMutE 2 0) (.pair (.var 1) (addE (.var 3) (.var 0)))))))

theorem d_twice : CDerives Δ₂ [] (.val twiceV) (.val passTy) := by
  refine .bangThunkV (persistent_dead .nil) rfl (.lam (.ret ?_))
  refine bindP (d_i32 1 (by cdeadP)) ?_
  refine letP (callMutW (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csolo)) ?_
  refine bindP (d_i32 2 (by cdeadP)) ?_
  refine letP (callMutW (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csolo)) ?_
  exact pairP (.var (by csoloP)) (d_add (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP))

/-! ### A call through a reborrow -/

/-- `'v ⊏ ⊓Δ₂`. -/
abbrev Δ₃ : LifeCtx := Δ₂.extend 2 Δ₂.meetOfDom

/-- `Λ'v. λm'. 3 to a. callMut m' a to (m', x). forget m'; [x]`. -/
def reCb : Expr :=
  lam2 (elet (i32E 3) (.letpair (callMutE 1 0) (.seq (.app forget (.var 1)) (.var 0))))

theorem d_reCb : CDerives Δ₂ [] reCb
    (.val (.all 2 Δ₂.meetOfDom (.lolli (.mut (.var 2) PC) (.box (.var 2) .i32)))) := by
  refine callbackW rfl rfl .nil ?_
  refine bindP (d_i32 3 (by cdeadP)) ?_
  refine letP (callMutW (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csolo)) ?_
  exact seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
    (.boxI (.var (by csoloP)) (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide)))

/-- `λm. withbor m reCb`: `m` reborrowed for one call, and returned. -/
def reV : Val := .lam (.app (.app withbor (.var 0)) reCb)

theorem d_re : CDerives Δ₂ [] (.val reV) (.val passTy) := by
  refine .bangThunkV (persistent_dead .nil) rfl (.lam (.ret ?_))
  exact appW (weak0 d_reCb (by cdead)) (appW (.var (by csolo))
    (.withbor3 (a := .var 1) (A := PC) (B := .i32) 2 (by cdeadP) rfl (vfree_PC 2)
      (by simp [VFree])))

/-! ### Passing on -/

/-- `passF 0` composes the reborrowed call and the two direct ones; `passF (n + 1)` hands the
borrow to `passF n`. -/
def passF : ℕ → Val
  | 0 => .lam (.letpair (.app (.val reV) (.var 0))
      (.letpair (.app (.val twiceV) (.var 1)) (.pair (.var 1) (addE (.var 2) (.var 0)))))
  | n + 1 => .lam (.app (.val (passF n)) (.var 0))

theorem d_pass0 : CDerives Δ₂ [] (.val (passF 0)) (.val passTy) := by
  refine .bangThunkV (persistent_dead .nil) rfl (.lam (.ret ?_))
  refine letP (.lolliE (split_kill' _).toP (.var (by csoloP)) (.bangE (weak0 d_re (kill_dead _)))) ?_
  refine letP (.lolliE (split_kill' _).toP (.var (by csoloP))
    (.bangE (weak0 d_twice (kill_dead _)))) ?_
  exact pairP (.var (by csoloP)) (d_add (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP))

/-- **At every depth.**  `passF n` is typed for every `n`. -/
theorem d_passF : ∀ (n : ℕ) {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ₂ Γ (.val (passF n)) (.val passTy)
  | 0, _, hΓ => weak0 d_pass0 hΓ
  | n + 1, _, hΓ => .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret
      (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (.bangE (d_passF n (.cons hΓ))))))

/-! ### The program -/

/-- `Λ'w. λm. passF n m to (m, t). forget m; [t]`. -/
def passCb (n : ℕ) : Expr :=
  lam2 (.letpair (.app (.val (passF n)) (.var 0)) (.seq (.app forget (.var 1)) (.var 0)))

theorem d_passCb (n : ℕ) : CDerives Δ₁ [] (passCb n) (.val cntCbTy) := by
  refine callbackW rfl rfl .nil ?_
  refine .letpairV (.left (.dead .nil))
    (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil))) (.bangE (d_passF n (.cons (.cons .nil)))))
    ?_
  exact .seqV (.right (.left (.dead (.dead .nil))))
    (.lolliE (split_kill' _).toP (.var (.there (.here (.cons (.cons .nil)))))
      (.forgetMut (kill_dead _).toP))
    (.boxI (.var (.here (.cons (.cons (.cons .nil)))))
      (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide)))

/-- The counter lent to `passF n`. -/
def passProg (n : ℕ) : Expr := scopeProg (scopeBodyWith (passCb n))

theorem passProg_derives (n : ℕ) : CDerives LifeCtx.empty [] (passProg n) (.comp (.ret .i32)) :=
  d_scopeProg (d_scopeBodyWith (fun hΓ => weak0 (d_passCb n) hΓ) (.cons (.cons (.cons .nil))))

theorem passProg_runs (n : ℕ) :
    ∃ v, BoCa.BoLo.Steps Adequacy.emptyMem (passProg n) Adequacy.emptyMem (.val (Val.i32 v)) :=
  runs_i32 (passProg_derives n)

set_option maxRecDepth 100000 in
/-- Through three more functions: `3 + (4 + 6) = 13`, no cell left. -/
theorem passProg3_eval : i32NoLeak (eval (passProg 3)) = some 13 := by decide

end BoCa.Fig16.LogRel.Core

end
