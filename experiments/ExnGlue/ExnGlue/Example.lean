import ExnGlue.Translate

/-!
# ExnGlue — the hardest case as a closed program  `[spec §19]`

The program of `docs/new-core/scope-804.md` §4: an owned `o` outside a borrow, an owned `i`
allocated inside the borrow's callback, and a raise inside the callback, under a `try`:

    try_7 (o ← alloc 1; r ← alloc 2;
           (r', b) ← borrow r as m in (i ← alloc 3; raise_7 5);
           _ ← free r'; _ ← free o; return ())
    with (x. return x) (e. return ())

`hard_derives` is its source derivation, every premise discharged, so `SDerives`' premises are
satisfiable at the hard case (non-vacuity), and `hard_safe` is `sourceResourceSafety` at it.
-/

namespace ExnGlue
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

abbrev RI : VTy := .ref (.int .w32)

/-- The row of the program's `try`. -/
abbrev S0 : Row := exnRow 7 (.int .w32) []

/-- The program's exception operation. -/
abbrev op7 : OpSig := ⟨7, 0, .cancel, .int .w32, .zero, .ret .unit, false⟩

theorem S0_eq : S0 = [op7] := rfl

def litE (c : UInt32) : Expr := .val ⟨.prim (.lit (.i32 c)), .prim⟩
def allocE (V : Expr) : Expr := .app (.val (.prim .alloc)) V
def freeV (i : Nat) : Expr := .app (.val (.prim .free)) (.var i)

/-- The callback's context: `m : Imm 'x I32`, `Λ`'s dead slot, `r` and `o` consumed. -/
abbrev Γm : Ctx VTy := [⟨.imm (.var 0) (.int .w32), true⟩, ⟨.unit, false⟩, ⟨RI, false⟩, ⟨RI, false⟩]

/-- The callback: `i ← alloc 3; raise_7 5`. -/
def cbM : STm := .letv Γm (.ret (allocE (litE 3))) (.raise 7 (⟨RI, true⟩ :: Γm) (litE 5))

/-- The body under the `try`. -/
def body : STm :=
  .letv [] (.ret (allocE (litE 1)))
  (.letv [⟨RI, true⟩] (.ret (allocE (litE 2)))
  (.letv [⟨RI, false⟩, ⟨RI, true⟩] (.borrowI (.int .w32) 0 cbM)
  (.letp (.var 0)
  (.letv [⟨.unit, true⟩, ⟨RI, false⟩, ⟨.tensor RI .unit, false⟩, ⟨RI, false⟩, ⟨RI, true⟩]
    (.ret (freeV 1))
  (.letv [⟨.int .w32, true⟩, ⟨.unit, true⟩, ⟨RI, false⟩, ⟨.tensor RI .unit, false⟩, ⟨RI, false⟩,
      ⟨RI, false⟩] (.ret (freeV 5))
  (.ret (.val .unit)))))))

/-- The program. -/
def hard : STm := .tryCatch 7 (.ret (.var 0)) (.ret (.val .unit)) body

theorem S0_exn : ExnRow S0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro o ho; rw [S0_eq, List.mem_singleton] at ho
    subst ho; decide
  · rw [S0_eq]; simp [Row.Uniq]
  · intro o ho; rw [S0_eq, List.mem_singleton] at ho
    subst ho; exact ⟨rfl, rfl, rfl, .int .w32⟩

theorem S0_unwind : S0.Unwind 0 := by
  intro o ho; rw [S0_eq, List.mem_singleton] at ho
  subst ho
  exact ⟨by decide, by decide, by simp [VFree], fun _ _ => .int⟩

theorem d_alloc {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (c : UInt32) :
    CDerives Δ Γ (allocE (litE c)) (.val RI) :=
  .lolliE (deadSplit hΓ) (.lit (.i32 c) hΓ.toP) (.alloc hΓ.toP)

theorem cbM_derives :
    SDerives (LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom) Γm cbM S0 (.box (.var 0) .unit) := by
  refine .letv (.right (.dead (.dead (.dead .nil)))) rfl S0_exn ?_ (.ret (d_alloc (by cdead) 3)) ?_
  · intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> first | exact .imm | cases hl
  · refine .raise (o := op7)
      (.right (.right (.dead (.dead (.dead .nil))))) rfl S0_exn ?_ rfl
      (.lit (.i32 5) (by cdead))
    intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> first | exact .ref .int | exact .imm | cases hl

theorem body_derives : SDerives LifeCtx.empty [] body S0 .unit := by
  refine .letv .nil rfl S0_exn (fun _ h => by cases h) (.ret (d_alloc .nil 1)) ?_
  refine .letv (.right .nil) rfl S0_exn ?_ (.ret (d_alloc (by cdead) 2)) ?_
  · intro s hs hl; simp only [List.mem_singleton] at hs; subst hs; exact .ref .int
  refine .letv (A := .tensor RI .unit) (.left (.right .nil)) rfl S0_exn ?_ ?_ ?_
  · intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> exact .ref .int
  · refine .borrowI (B := .unit) 0 (.right (.dead .nil)) (.here (.cons .nil)) .int ok_empty rfl
      (fun y h => by simp [VFree] at h) (by simp [VFree]) (by simp [VFree]) S0_unwind ?_ cbM_derives
    intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> cases hl
  refine .letp (.left (.dead (.right .nil))) (.var (.here (.cons (.cons .nil)))) ?_
  refine .letv (.right (.left (.dead (.dead (.right .nil))))) rfl S0_exn ?_
    (.ret (.lolliE (split_kill' _).toP (.var (.there (.here (by cdead)))) (.free (by cdead)))) ?_
  · intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> first | exact .unit | exact .ref .int | cases hl
  refine .letv (.right (.right (.dead (.dead (.dead (.left .nil)))))) rfl S0_exn ?_
    (.ret (.lolliE (split_kill' _).toP
      (.var (.there (.there (.there (.there (.there (.here .nil))))))) (.free (by cdead)))) ?_
  · intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact .unit | exact .int | cases hl
  exact .ret (.unitI (.weaken rfl (.weaken rfl (.weaken rfl (.cons (.cons (.cons (.cons .nil))))))))

/-- **Non-vacuity at the hard case**: the program's source derivation, every premise discharged. -/
theorem hard_derives : SDerives LifeCtx.empty [] hard [] .unit :=
  .tryCatch .nil (fun _ h => by cases h) (by decide) (fun _ h => by cases h) S0_exn body_derives
    (.ret (.var (.here .nil))) (.ret (.unitI (.weaken rfl .nil)))

/-- **The hard case is resource safe**: every run of its translation from the empty memory
continues to a value at the empty memory, and every `free` it reaches finds its cell. -/
theorem hard_safe {ℍ : BoCa.Host} [BoCa.HostIs ℍ] {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (tr hard) μ₁ e₁) :
    (∃ v : Val, BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : BoCa.BoLo.Kont) (ℓ : Loc), e₁ = K.plug (BoCa.BoLo.freeE (.val (Val.loc ℓ))) →
      ∃ u, μ₁ ℓ = some u) :=
  sourceResourceSafety rfl hard_derives hs

/-- **The payload condition's scope**: a `try` whose payload owns a cell is not in the fragment
(route K: `[raise]`'s `hd`). -/
example : ¬ ExnRow (exnRow 7 RI []) := not_exnRow_ref 7 _ []

end ExnGlue
