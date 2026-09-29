import Frontend.Check.CrossCheck
import Core

/-!
# LoopBorrow — the instances, checked, run on every run, and interpreted

Six programs over the per-observation lend (`bc/`): the lender is part of the codata's state,
and each observation lends it for that observation only, so every observation's borrow is an
ordinary `withbor` inside one run.

* `lend-loop-imm.bc` — the core of `corpus/pending/borrow-across-loop.bc`: a table borrowed
  `imm` on every step of a loop (`lend_loop_imm`), read by `withload` and `array_get`. `100`.
* `lend-gen-mut.bc` — a generator lending a counter cell `mut` on every `next`
  (`lend_gen_mut`), pulled three times and closed; the cell comes back. `(18, 8)`.
* `lend-config-imm.bc` — a loop-invariant configuration `(step, limit)` borrowed `imm` by every
  iteration. `(12, 4)`.
* `lend-each-imm.bc` — a lending yield in push form: each observation lends one entry of an
  array to the consumer's body as a view `imm 'z i32`, a borrow that ends inside the
  observation. `100`.
* `zip-push-pull.bc` — that source zipped with an ordinary generator: the generator is pulled
  before the lend, and its element goes to the body with the view. `200`.
* `zip-push-push.bc` — two lending sources zipped: both arrays' owners are in the state, the two
  lends nest inside one observation, and the body sees both views at once. `300`.

Each file's `main` is checked by `bcc`'s checker in the kernel (`decide +kernel`); what the
checker returns is a `CDerives` derivation (`Frontend/Check/`, "Soundness"), at the empty
context and a closed `F T` (`…_shape`). So `fundamentalC` covers it (`…_sem`) and every run from
the empty memory continues to a value of `T` at the empty memory (`…_every_run`, by
`theorem32D`). The interpreter's answer, with no cell left, is `…_eval` (`decide +kernel`). The
parser runs at elaboration time (`bcc_program%`), as in `Frontend/Check/CrossCheck.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LoopBorrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx)
open Frontend.Check (mainOf)

/-! ### Outcomes -/

/-- An `i32` result with no cell left. -/
def outI32 : Outcome → Option UInt32
  | .value ⟨.prim (.lit (.i32 n)), _⟩ false => some n
  | _ => none

/-- An `i32 ⊗ i32` result with no cell left. -/
def outI32Pair : Outcome → Option (UInt32 × UInt32)
  | .value ⟨.pair (.prim (.lit (.i32 a))) (.prim (.lit (.i32 b))), _⟩ false => some (a, b)
  | _ => none

/-- The interpreter's fuel. -/
abbrev fuel : Nat := 100000

/-! ### Every run, at `i32` and `i32 ⊗ i32` -/

theorem every_run_i32 {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret (.int .w32))))
    {μ₁ : BoLo.Heap} {e₁ : Expr} (hs : BoLo.Steps Adequacy.emptyMem e μ₁ e₁) :
    ∃ n : UInt32, BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.i32 n)) := by
  have hwp : wpTS [] e (fun _ v => BoLo.pure (∃ n, v = Val.i32 n)) (PMap.empty : WRes) :=
    wpTS_mono (fun _ v ρ hv => by obtain ⟨rfl, n, rfl⟩ := hv; exact ⟨rfl, n, rfl⟩)
      PMap.empty (wp_of_derives h)
  obtain ⟨v, hsteps, n, rfl⟩ := theorem32D e (fun v => ∃ n, v = Val.i32 n) hwp hs
  exact ⟨n, hsteps⟩

theorem every_run_i32Pair {e : Expr}
    (h : CDerives LifeCtx.empty [] e (.comp (.ret (.tensor (.int .w32) (.int .w32)))))
    {μ₁ : BoLo.Heap} {e₁ : Expr} (hs : BoLo.Steps Adequacy.emptyMem e μ₁ e₁) :
    ∃ a b : UInt32,
      BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (.pair (Val.i32 a) (Val.i32 b))) := by
  have hwp : wpTS [] e
      (fun _ v => BoLo.pure (∃ a b : UInt32, v = .pair (Val.i32 a) (Val.i32 b)))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives h)
    obtain ⟨v₁, v₂, hs₁⟩ := hv
    obtain ⟨rfl, ρ₁, ρ₂, hc, ⟨e₁, a, rfl⟩, ⟨e₂, b, rfl⟩⟩ := pure_sep_iff.mp hs₁
    subst e₁; subst e₂
    exact ⟨eq_of_compS_empty_left hc, a, b, rfl⟩
  obtain ⟨v, hsteps, a, b, rfl⟩ :=
    theorem32D e (fun v => ∃ a b : UInt32, v = .pair (Val.i32 a) (Val.i32 b)) hwp hs
  exact ⟨a, b, hsteps⟩

/-! ### `lend-loop-imm.bc`: a table borrowed on every step of a loop -/

def loopImmP : Frontend.Program := bcc_program% "experiments/LoopBorrow/bc/lend-loop-imm.bc"

set_option maxRecDepth 100000 in
theorem loopImmP_checks : (mainOf loopImmP).isSome = true := by decide +kernel

def loopImm : Frontend.Check.Checked := (mainOf loopImmP).get loopImmP_checks

set_option maxRecDepth 100000 in
theorem loopImm_shape : loopImm.ctx = [] ∧ loopImm.C = .ret (.int .w32) := by decide +kernel

theorem loopImm_derives : CDerives LifeCtx.empty [] loopImm.e (.comp (.ret (.int .w32))) := by
  have h := loopImm.deriv
  rwa [loopImm_shape.1, loopImm_shape.2] at h

theorem loopImm_sem : SemC LifeCtx.empty [] loopImm.e (.ret (.int .w32)) :=
  fundamentalC loopImm_derives

/-- Every run continues to an `i32` at the empty memory. -/
theorem loopImm_every_run {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps Adequacy.emptyMem loopImm.e μ₁ e₁) :
    ∃ n : UInt32, BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.i32 n)) :=
  every_run_i32 loopImm_derives hs

set_option maxRecDepth 100000 in
/-- The interpreter: `100`, no cell left. -/
theorem loopImm_eval : outI32 (run wasmHost fuel Mem.empty loopImm.e) = some 100 := by
  decide +kernel

/-! ### `lend-gen-mut.bc`: a generator lending a cell `mut` on every `next` -/

def genMutP : Frontend.Program := bcc_program% "experiments/LoopBorrow/bc/lend-gen-mut.bc"

set_option maxRecDepth 100000 in
theorem genMutP_checks : (mainOf genMutP).isSome = true := by decide +kernel

def genMut : Frontend.Check.Checked := (mainOf genMutP).get genMutP_checks

set_option maxRecDepth 100000 in
theorem genMut_shape : genMut.ctx = [] ∧ genMut.C = .ret (.tensor (.int .w32) (.int .w32)) := by
  decide +kernel

theorem genMut_derives :
    CDerives LifeCtx.empty [] genMut.e (.comp (.ret (.tensor (.int .w32) (.int .w32)))) := by
  have h := genMut.deriv
  rwa [genMut_shape.1, genMut_shape.2] at h

theorem genMut_sem : SemC LifeCtx.empty [] genMut.e (.ret (.tensor (.int .w32) (.int .w32))) :=
  fundamentalC genMut_derives

/-- Every run continues to a pair of `i32`s at the empty memory. -/
theorem genMut_every_run {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps Adequacy.emptyMem genMut.e μ₁ e₁) :
    ∃ a b : UInt32,
      BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (.pair (Val.i32 a) (Val.i32 b))) :=
  every_run_i32Pair genMut_derives hs

set_option maxRecDepth 100000 in
/-- The interpreter: `(18, 8)`, no cell left. -/
theorem genMut_eval : outI32Pair (run wasmHost fuel Mem.empty genMut.e) = some (18, 8) := by
  decide +kernel

/-! ### `lend-config-imm.bc`: a configuration borrowed by every iteration -/

def configImmP : Frontend.Program := bcc_program% "experiments/LoopBorrow/bc/lend-config-imm.bc"

set_option maxRecDepth 100000 in
theorem configImmP_checks : (mainOf configImmP).isSome = true := by decide +kernel

def configImm : Frontend.Check.Checked := (mainOf configImmP).get configImmP_checks

set_option maxRecDepth 100000 in
theorem configImm_shape :
    configImm.ctx = [] ∧ configImm.C = .ret (.tensor (.int .w32) (.int .w32)) := by
  decide +kernel

theorem configImm_derives :
    CDerives LifeCtx.empty [] configImm.e (.comp (.ret (.tensor (.int .w32) (.int .w32)))) := by
  have h := configImm.deriv
  rwa [configImm_shape.1, configImm_shape.2] at h

theorem configImm_sem :
    SemC LifeCtx.empty [] configImm.e (.ret (.tensor (.int .w32) (.int .w32))) :=
  fundamentalC configImm_derives

/-- Every run continues to a pair of `i32`s at the empty memory. -/
theorem configImm_every_run {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps Adequacy.emptyMem configImm.e μ₁ e₁) :
    ∃ a b : UInt32,
      BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (.pair (Val.i32 a) (Val.i32 b))) :=
  every_run_i32Pair configImm_derives hs

set_option maxRecDepth 100000 in
/-- The interpreter: `(12, 4)`, no cell left. -/
theorem configImm_eval :
    outI32Pair (run wasmHost fuel Mem.empty configImm.e) = some (12, 4) := by
  decide +kernel

/-! ### `lend-each-imm.bc`: each element lent to the body as a view -/

def eachImmP : Frontend.Program := bcc_program% "experiments/LoopBorrow/bc/lend-each-imm.bc"

set_option maxRecDepth 100000 in
theorem eachImmP_checks : (mainOf eachImmP).isSome = true := by decide +kernel

def eachImm : Frontend.Check.Checked := (mainOf eachImmP).get eachImmP_checks

set_option maxRecDepth 100000 in
theorem eachImm_shape : eachImm.ctx = [] ∧ eachImm.C = .ret (.int .w32) := by decide +kernel

theorem eachImm_derives : CDerives LifeCtx.empty [] eachImm.e (.comp (.ret (.int .w32))) := by
  have h := eachImm.deriv
  rwa [eachImm_shape.1, eachImm_shape.2] at h

theorem eachImm_sem : SemC LifeCtx.empty [] eachImm.e (.ret (.int .w32)) :=
  fundamentalC eachImm_derives

/-- Every run continues to an `i32` at the empty memory. -/
theorem eachImm_every_run {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps Adequacy.emptyMem eachImm.e μ₁ e₁) :
    ∃ n : UInt32, BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.i32 n)) :=
  every_run_i32 eachImm_derives hs

set_option maxRecDepth 100000 in
/-- The interpreter: `100`, no cell left. -/
theorem eachImm_eval : outI32 (run wasmHost fuel Mem.empty eachImm.e) = some 100 := by
  decide +kernel

/-! ### `zip-push-pull.bc`: a lending source zipped with a generator -/

def zipPushPullP : Frontend.Program := bcc_program% "experiments/LoopBorrow/bc/zip-push-pull.bc"

set_option maxRecDepth 100000 in
theorem zipPushPullP_checks : (mainOf zipPushPullP).isSome = true := by decide +kernel

def zipPushPull : Frontend.Check.Checked := (mainOf zipPushPullP).get zipPushPullP_checks

set_option maxRecDepth 100000 in
theorem zipPushPull_shape : zipPushPull.ctx = [] ∧ zipPushPull.C = .ret (.int .w32) := by decide +kernel

theorem zipPushPull_derives : CDerives LifeCtx.empty [] zipPushPull.e (.comp (.ret (.int .w32))) := by
  have h := zipPushPull.deriv
  rwa [zipPushPull_shape.1, zipPushPull_shape.2] at h

theorem zipPushPull_sem : SemC LifeCtx.empty [] zipPushPull.e (.ret (.int .w32)) :=
  fundamentalC zipPushPull_derives

/-- Every run continues to an `i32` at the empty memory. -/
theorem zipPushPull_every_run {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps Adequacy.emptyMem zipPushPull.e μ₁ e₁) :
    ∃ n : UInt32, BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.i32 n)) :=
  every_run_i32 zipPushPull_derives hs

set_option maxRecDepth 100000 in
/-- The interpreter: `200`, no cell left. -/
theorem zipPushPull_eval : outI32 (run wasmHost fuel Mem.empty zipPushPull.e) = some 200 := by
  decide +kernel

/-! ### `zip-push-push.bc`: two lending sources, both elements borrowed at once -/

def zipPushPushP : Frontend.Program := bcc_program% "experiments/LoopBorrow/bc/zip-push-push.bc"

set_option maxRecDepth 100000 in
theorem zipPushPushP_checks : (mainOf zipPushPushP).isSome = true := by decide +kernel

def zipPushPush : Frontend.Check.Checked := (mainOf zipPushPushP).get zipPushPushP_checks

set_option maxRecDepth 100000 in
theorem zipPushPush_shape : zipPushPush.ctx = [] ∧ zipPushPush.C = .ret (.int .w32) := by decide +kernel

theorem zipPushPush_derives : CDerives LifeCtx.empty [] zipPushPush.e (.comp (.ret (.int .w32))) := by
  have h := zipPushPush.deriv
  rwa [zipPushPush_shape.1, zipPushPush_shape.2] at h

theorem zipPushPush_sem : SemC LifeCtx.empty [] zipPushPush.e (.ret (.int .w32)) :=
  fundamentalC zipPushPush_derives

/-- Every run continues to an `i32` at the empty memory. -/
theorem zipPushPush_every_run {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps Adequacy.emptyMem zipPushPush.e μ₁ e₁) :
    ∃ n : UInt32, BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.i32 n)) :=
  every_run_i32 zipPushPush_derives hs

set_option maxRecDepth 100000 in
/-- The interpreter: `300`, no cell left. -/
theorem zipPushPush_eval : outI32 (run wasmHost fuel Mem.empty zipPushPush.e) = some 300 := by
  decide +kernel

end BoCa.Fig16.LogRel.Core.LoopBorrow

end
