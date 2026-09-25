import Core.DelayPrograms
import Core.RecordPrograms
import Core.Family

/-!
# Core — programs over `I32`  `[spec §8]`

Each program is one closed `CDerives` derivation. It runs by adequacy at every host
(`*_runs`, parametric in `ℍ`), and by the interpreter at `wasmHost` (`*_eval`, kernel-checked
by `decide`). Each observable is one that a host ignoring an operand, swapping operands or
not wrapping could not produce.

* `sumToProg`: `fixD` over the state `(i, acc) : I32 ⊗ I32` from `(10, 0)`: `now acc` at
  `i = 0`, else `later (i - 1, acc + i)`. Observed: `55`.
* `sumListProg`: a list `μX. 1 ⊕ Ref (I32 ⊗ X)` of `[100, 20, 3]`, each node one block, summed
  inside an immutable borrow by `foldImm` (the algebra reads each payload by `withload`), then
  freed by `foldOwn`. Observed: `123`.
* `signProg`: `div_s` and `div_u` of `-7` by `2`, an overflowing `mul`, and `div_u` by zero.
  Observed: `(-3, 0x7FFFFFFC, 0x10000, error)`.

`I32` is persistent (§10), so its variables are copied and dropped implicitly. `partP` is the
context split that sends every persistent slot to both sides; the wrappers `appP`, `pairP`,
`letP`, `caseP` are the value-level rules at that split, and the tactics `cdeadP`, `csoloP` close
the leaves.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Splits that copy persistent slots -/

/-- The split of `Γ` at which `e` receives the live slots it mentions and the rest receives the
others, every persistent live slot going to both sides. -/
def partP (e : Expr) : Nat → Ctx VTy → Ctx VTy × Ctx VTy
  | _, [] => ([], [])
  | i, s :: Γ =>
      let p := partP e (i + 1) Γ
      if s.live then
        if s.ty.persistent then (⟨s.ty, true⟩ :: p.1, ⟨s.ty, true⟩ :: p.2)
        else if occ i e then (⟨s.ty, true⟩ :: p.1, ⟨s.ty, false⟩ :: p.2)
        else (⟨s.ty, false⟩ :: p.1, ⟨s.ty, true⟩ :: p.2)
      else (s :: p.1, s :: p.2)

theorem partP_split (e : Expr) :
    ∀ (i : Nat) (Γ : Ctx VTy), Ctx.SplitP Γ (partP e i Γ).1 (partP e i Γ).2
  | _, [] => .nil
  | i, ⟨T, true⟩ :: Γ => by
      cases hp : T.persistent
      · cases h : occ i e
        · simpa [partP, hp, h] using Ctx.SplitP.right (T := T) (partP_split e (i + 1) Γ)
        · simpa [partP, hp, h] using Ctx.SplitP.left (T := T) (partP_split e (i + 1) Γ)
      · simpa [partP, hp] using Ctx.SplitP.dup (T := T) hp (partP_split e (i + 1) Γ)
  | i, ⟨T, false⟩ :: Γ => .dead (partP_split e (i + 1) Γ)

section
variable {Δ : LifeCtx} {Γ : Ctx VTy}

theorem appP {f a : Expr} {A B : VTy} (ha : CDerives Δ (partP a 0 Γ).1 a (.val A))
    (hf : CDerives Δ (partP a 0 Γ).2 f (.val (.lolli A B))) : CDerives Δ Γ (.app f a) (.val B) :=
  .lolliE (partP_split a 0 Γ) ha hf

theorem pairP {e₁ e₂ : Expr} {A B : VTy} (h₁ : CDerives Δ (partP e₁ 0 Γ).1 e₁ (.val A))
    (h₂ : CDerives Δ (partP e₁ 0 Γ).2 e₂ (.val B)) :
    CDerives Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) :=
  .tensorI (partP_split e₁ 0 Γ) h₁ h₂

theorem letP {ep eb : Expr} {A B C : VTy}
    (hp : CDerives Δ (partP ep 0 Γ).1 ep (.val (.tensor A B)))
    (hb : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: (partP ep 0 Γ).2) eb (.val C)) :
    CDerives Δ Γ (.letpair ep eb) (.val C) :=
  .letpairV (partP_split ep 0 Γ) hp hb

theorem caseP {es e₁ e₂ : Expr} {A B C : VTy}
    (h₀ : CDerives Δ (partP es 0 Γ).1 es (.val (.sum A B)))
    (h₁ : CDerives Δ (⟨A, true⟩ :: (partP es 0 Γ).2) e₁ (.val C))
    (h₂ : CDerives Δ (⟨B, true⟩ :: (partP es 0 Γ).2) e₂ (.val C)) :
    CDerives Δ Γ (.case es e₁ e₂) (.val C) :=
  .caseV (partP_split es 0 Γ) h₀ h₁ h₂

theorem bindP {e b : Expr} {A C : VTy} (he : CDerives Δ (partP e 0 Γ).1 e (.val A))
    (hb : CDerives Δ (⟨A, true⟩ :: (partP e 0 Γ).2) b (.val C)) :
    CDerives Δ Γ (bindE e b) (.val C) :=
  .eletV (partP_split e 0 Γ) he hb

end

/-- `Γ` consumed, up to live persistent slots. -/
syntax "cdeadP" : tactic
macro_rules
  | `(tactic| cdeadP) => `(tactic| first | exact Ctx.DeadP.nil | exact Ctx.Dead.toP (by assumption) | (refine Ctx.DeadP.cons ?_; cdeadP) | (refine Ctx.DeadP.drop (by decide) ?_; cdeadP))

/-- `Γ = x : A`, up to live persistent slots elsewhere. -/
syntax "csoloP" : tactic
macro_rules
  | `(tactic| csoloP) => `(tactic| first | (refine Ctx.SoloP.here ?_; cdeadP) | (refine Ctx.SoloP.there ?_; csoloP) | (refine Ctx.SoloP.skip (by decide) ?_; csoloP))

/-! ### Terms -/

/-- `op a`: a host operation applied. -/
def hop (op : HostOp) (a : Expr) : Expr := .app (.val (.prim (.host op))) a

/-- The literal `i32[n]`. -/
def i32E (n : UInt32) : Expr := .val (Val.i32 n)

theorem d_hop {Δ : LifeCtx} {Γ : Ctx VTy} (op : HostOp) {a : Expr}
    (ha : CDerives Δ (partP a 0 Γ).1 a (.val (hostArg op)))
    (hΓ : Ctx.DeadP (partP a 0 Γ).2) : CDerives Δ Γ (hop op a) (.val (hostRes op)) :=
  appP ha (.bangE (.hostOp op hΓ))

theorem d_i32 {Δ : LifeCtx} {Γ : Ctx VTy} (n : UInt32) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (i32E n) (.val .i32) :=
  .lit (.i32 n) hΓ

/-- The integer an expression is, if it is a 32-bit literal. -/
def i32Of : Expr → Option UInt32
  | .prim (.lit (.i32 n)) => some n
  | _ => none

/-! ### (a) A `fixD` loop over `I32`: `1 + 2 + … + 10` -/

/-- The state `(i, acc)`. -/
abbrev sumS : VTy := .tensor .i32 .i32

/-- `next` at `(i, acc)`: `now acc` at `eqz i`, else `later (i - 1, acc + i)`. -/
def sumToNext : Expr :=
  .letpair (.var 2)
    (.case (hop (.eqz .w32) (.var 1))
      (.inj₂ (.pair (hop (.bin .w32 .sub) (.pair (.var 2) (i32E 1)))
        (hop (.bin .w32 .add) (.pair (.var 1) (.var 2)))))
      (.inj₁ (.var 1)))

/-- `λs. ⟨sumToNext, ()⟩ : I32 ⊗ I32 ⊸ F(I32 ⊕ I32 ⊗ I32) & F 1`; `close` drops the state. -/
def sumToStep : Val := .lam (withPair sumToNext (.val .unit))

theorem d_sumToStep :
    CDerives LifeCtx.empty [⟨sumS, false⟩] (.val sumToStep)
      (.val (.bang (.thunk (stepDC .i32 sumS)))) := by
  refine .bangThunkV (persistent_dead (.cons .nil)) rfl (.lam (.withI (.ret ?_) (.ret ?_)))
  · refine letP (A := .i32) (B := .i32) (.var (by csoloP)) ?_
    refine caseP (A := .unit) (B := .unit) (d_hop (.eqz .w32) (.var (by csoloP)) (by cdeadP)) ?_ ?_
    · refine .sumI₂ (pairP ?_ ?_)
      · exact d_hop (.bin .w32 .sub) (pairP (.var (by csoloP)) (d_i32 1 (by cdeadP))) (by cdeadP)
      · exact d_hop (.bin .w32 .add) (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP)
    · exact .sumI₁ (.var (by csoloP))
  · exact .unitI (by cdeadP)

/-- `fixD sumToStep (10, 0)`, driven at most twenty times. -/
def sumToProg : Expr := progD (.pair (i32E 10) (i32E 0)) sumToStep 20

theorem sumToProg_derives :
    CDerives LifeCtx.empty [] sumToProg (.comp (.ret (.sum .i32 .unit))) :=
  d_progD (.tensorI .nil (d_i32 10 .nil) (d_i32 0 .nil)) d_sumToStep 20

/-- **The loop runs at every host**: from the empty memory to `now n` for a 32-bit literal `n`,
or `closed`, and the empty memory. -/
theorem sumToProg_runs : ∃ v : Val,
    BoCa.BoLo.Steps Adequacy.emptyMem sumToProg Adequacy.emptyMem (.val v) ∧
      ((∃ n, v = .inj₁ (Val.i32 n)) ∨ v = .inj₂ .unit) := by
  have hwp : wpTS [] sumToProg
      (fun _ v => Fig16.BoLo.pure ((∃ n, v = .inj₁ (Val.i32 n)) ∨ v = .inj₂ .unit))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives sumToProg_derives)
    obtain ⟨rfl, ⟨a, rfl, ha⟩ | rfl⟩ := vC_sum_unit_pure (A := .i32) (fun h => h.1) hv
    · obtain ⟨-, n, rfl⟩ := ha
      exact ⟨rfl, Or.inl ⟨n, rfl⟩⟩
    · exact ⟨rfl, Or.inr rfl⟩
  exact theorem32 _ _ hwp

/-- A driven run's result when it ends with no cell left: `now n` or `closed`. -/
def intOutcome : Outcome → Option (Option UInt32)
  | .value ⟨.inj₁ e, _⟩ false => (i32Of e).map some
  | .value ⟨.inj₂ .unit, _⟩ false => some none
  | _ => none

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: `now 55`, no cell left. -/
theorem sumToProg_eval : intOutcome (eval sumToProg) = some (some 55) := by decide

/-! ### (b) A borrowed list of `I32`, summed by `foldImm` -/

/-- `1 ⊕ (Ref I32 ⊗ Ref X)`: the common list shape `μX. 1 ⊕ Ref (I32 ⊗ X)` with each node one
block (`CommonList.lean`), at `I32` payloads. -/
abbrev ilistF : FShape := .sum (.leaf .unit) (.tensor (.leaf (.ref .i32)) .refX)

abbrev ilistL : VTy := .mu ilistF.ty

theorem ilistF_WF : ilistF.WF := by simp [FShape.WF, VTy.Cl]

/-- The node at the closed list type: `I32 ⊗ L`. -/
abbrev nodeI : Shape := .node (.leaf .i32) (.leaf ilistL)

theorem ilistL_unroll : VTy.inst ilistL ilistF.ty = .sum .unit nodeI.refTy := rfl

/-- `inj₂ (allocS nodeI (n, t))`: a node, allocated as one block. -/
def consI (n t : Expr) : Expr := .inj₂ (.app (allocS nodeI) (.pair n t))

/-- A list of literals. -/
def buildI : List UInt32 → Expr
  | [] => .inj₁ (.val .unit)
  | n :: ns => consI (i32E n) (buildI ns)

theorem d_buildI {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ∀ ns, CDerives Δ Γ (buildI ns) (.val ilistL)
  | [] => .roll (FShape.noMut_ty ilistF_WF) (FShape.Cl_ty ilistF_WF) (.sumI₁ (.unitI hΓ))
  | n :: ns => .roll (FShape.noMut_ty ilistF_WF) (FShape.Cl_ty ilistF_WF)
      (.sumI₂ (.lolliE (deadSplit hΓ) (.tensorI (deadSplit hΓ) (d_i32 n hΓ) (d_buildI hΓ ns))
        (d_allocS nodeI hΓ)))

/-- `withload b (Λ. λv. v)`: the payload behind an `Imm` borrow of an `I32`. -/
def readI (b : Expr) : Expr := .app (.app withload b) (lam2 (.var 0))

/-- `case r {inj₁ u. 0 | inj₂ p. let (b, s) = p in add (readI b, s)}`: the algebra sees
`1 ⊕ (Imm 'y I32 ⊗ I32)`. -/
def sumIAlgB : Expr :=
  .case (.var 0) (i32E 0)
    (.letpair (.var 0) (hop (.bin .w32 .add) (.pair (readI (.var 1)) (.var 0))))

/-- The sum algebra, `!U(∀'y. 1 ⊕ (Imm 'y I32 ⊗ I32) ⊸ F I32)`. -/
def sumIAlgV : Val := .lam (.val (.lam sumIAlgB))

theorem ΔA_ok : ΔA.Ok := ok_empty.extend rfl rfl

theorem d_sumIAlg :
    CDerives LifeCtx.empty [⟨.lolli ilistL .unit, false⟩] (.val sumIAlgV)
      (.val (algTy ilistF 0 .i32)) := by
  refine d_algI (.cons .nil) (.ret ?_)
  refine caseP (A := .unit) (B := .tensor (.imm (.var 0) .i32) .i32) (.var (by csoloP))
    (d_i32 0 (by cdeadP)) ?_
  refine letP (A := .imm (.var 0) .i32) (B := .i32) (.var (by csoloP)) ?_
  refine d_hop (.bin .w32 .add) (pairP ?_ (.var (by csoloP))) (by cdeadP)
  exact appW
    (callbackW ΔA_ok (x := 1) rfl (by cdead)
      (.boxI (.var (by csoloP))
        (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
          (by cdead))))
    (appW (.var (by csoloP))
      (.withload (a := .var 0) (A := .i32) (B := .i32) 1 (by cdeadP) rfl (by simp [VFree])
        (by simp [VFree])))

/-- `foldImm sumIAlg`, the borrowed sum. -/
def sumIE : Expr := .app (.val (foldImmV ilistF)) (.val sumIAlgV)

theorem d_sumI : CDerives LifeCtx.empty [⟨.lolli ilistL .unit, false⟩] sumIE (.val (fTy ilistL .i32)) :=
  .lolliE (deadSplit (.cons .nil)) d_sumIAlg
    (.foldImm ilistF 0 LifeCtx.empty.meetOfDom .i32 (.cons .nil) ilistF_WF trivial
      (by simp [VFree, FShape.ty]) (by simp [VFree]) (fun _ _ => .int))

/-- `case r {inj₁ u. () | inj₂ p. let (rn, u) = p in free rn to n. ()}`: the payload and the
unit are dropped as persistent slots. -/
def freeIAlgB : Expr :=
  .case (.var 0) (.val .unit)
    (.letpair (.var 0) (bindE (.app (.val (.prim .free)) (.var 1)) (.val .unit)))

def freeIAlgV : Val := .lam freeIAlgB

theorem d_freeIAlg : CDerives LifeCtx.empty [] (.val freeIAlgV) (.val (algOTy ilistF .unit)) := by
  refine d_algO .nil (.ret ?_)
  refine caseP (A := .unit) (B := .tensor (.ref .i32) .unit) (.var (by csoloP))
    (.unitI (by cdeadP)) ?_
  refine letP (A := .ref .i32) (B := .unit) (.var (by csoloP)) ?_
  exact bindP (appP (.var (by csoloP)) (.free (by cdeadP))) (.unitI (by cdeadP))

/-- `foldOwn freeIAlg`. -/
def freeIE : Expr := .app (.val (foldOwnV ilistF)) (.val freeIAlgV)

theorem d_freeI : CDerives LifeCtx.empty [] freeIE (.val (.lolli ilistL .unit)) :=
  .bangE (.lolliE .nil d_freeIAlg (.foldOwn ilistF .unit .nil ilistF_WF trivial))

/-- Build `[100, 20, 3]` node by node as blocks, borrow it, sum it with `foldImm sumIAlg`, end
the borrow, free it with `foldOwn freeIAlg`. -/
def sumListProg : Expr := foldProg freeIE sumIE (buildI [100, 20, 3])

theorem sumListProg_derives : CDerives LifeCtx.empty [] sumListProg (.comp (.ret .i32)) :=
  d_foldProg d_freeI d_sumI (fun hΓ => d_buildI hΓ _)
    (fun _ => by simp [VFree, FShape.ty]) (fun _ => by simp [VFree]) (fun _ _ => .int) rfl

/-- **The borrowed sum runs at every host**: from the empty memory to a 32-bit literal and the
empty memory. -/
theorem sumListProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem sumListProg Adequacy.emptyMem (.val (Val.i32 n)) := by
  have hwp : wpTS [] sumListProg (fun _ v => Fig16.BoLo.pure (∃ n, v = Val.i32 n))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives sumListProg_derives)
    obtain ⟨rfl, n, rfl⟩ := hv
    exact ⟨rfl, n, rfl⟩
  obtain ⟨v, hsteps, n, rfl⟩ := theorem32 sumListProg (fun v => ∃ n, v = Val.i32 n) hwp
  exact ⟨n, hsteps⟩

/-- A run's 32-bit literal, when it ends with no cell left. -/
def i32NoLeak : Outcome → Option UInt32
  | .value v false => i32Of v.1
  | _ => none

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: `123`, no cell left. -/
theorem sumListProg_eval : i32NoLeak (eval sumListProg) = some 123 := by decide

/-! ### (c) Signedness, wrapping, and division by zero -/

/-- `case e {inj₁ x. x | inj₂ u. 0}`: a partial result, `0` on the error branch. -/
def orZero (e : Expr) : Expr := .case e (.var 0) (i32E 0)

/-- `case e {inj₁ x. false | inj₂ u. true}`: whether a partial operation took the error branch. -/
def isErr (e : Expr) : Expr := .case e (.inj₁ (.val .unit)) (.inj₂ (.val .unit))

/-- `-7` at 32 bits. -/
abbrev minus7 : UInt32 := 0xFFFFFFF9

/-- `(div_s (-7, 2) or 0, (div_u (-7, 2) or 0, (mul (0x10000, 0x10001), isErr (div_u (1, 0)))))`. -/
def signProg : Expr :=
  .pair (orZero (hop (.div .w32 .div_s) (.pair (i32E minus7) (i32E 2))))
    (.pair (orZero (hop (.div .w32 .div_u) (.pair (i32E minus7) (i32E 2))))
      (.pair (hop (.bin .w32 .mul) (.pair (i32E 0x10000) (i32E 0x10001)))
        (isErr (hop (.div .w32 .div_u) (.pair (i32E 1) (i32E 0))))))

/-- The result type `I32 ⊗ I32 ⊗ I32 ⊗ (1 ⊕ 1)`. -/
abbrev signT : VTy := .tensor .i32 (.tensor .i32 (.tensor .i32 .boolT))

theorem d_orZero {Γ : Ctx VTy} {e : Expr} (hΓ : Ctx.Dead Γ)
    (he : CDerives LifeCtx.empty Γ e (.val (.sum .i32 .unit))) :
    CDerives LifeCtx.empty Γ (orZero e) (.val .i32) :=
  .caseV (deadSplit hΓ) he (.var (.here hΓ.toP)) (d_i32 0 (.drop rfl hΓ.toP))

theorem d_isErr {Γ : Ctx VTy} {e : Expr} (hΓ : Ctx.Dead Γ)
    (he : CDerives LifeCtx.empty Γ e (.val (.sum .i32 .unit))) :
    CDerives LifeCtx.empty Γ (isErr e) (.val .boolT) :=
  .caseV (deadSplit hΓ) he (.sumI₁ (.unitI (.drop rfl hΓ.toP))) (.sumI₂ (.unitI (.drop rfl hΓ.toP)))

theorem d_div {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (o : DivOp) (a b : UInt32) :
    CDerives LifeCtx.empty Γ (hop (.div .w32 o) (.pair (i32E a) (i32E b))) (.val (.sum .i32 .unit)) :=
  .lolliE (deadSplit hΓ) (.tensorI (deadSplit hΓ) (d_i32 a hΓ.toP) (d_i32 b hΓ.toP))
    (.bangE (.hostOp (.div .w32 o) hΓ.toP))

theorem signProg_derives : CDerives LifeCtx.empty [] signProg (.comp (.ret signT)) :=
  .ret (.tensorI .nil (d_orZero .nil (d_div .nil .div_s _ _))
    (.tensorI .nil (d_orZero .nil (d_div .nil .div_u _ _))
      (.tensorI .nil
        (.lolliE .nil (.tensorI .nil (d_i32 _ .nil) (d_i32 _ .nil))
          (.bangE (.hostOp (.bin .w32 .mul) .nil)))
        (d_isErr .nil (d_div .nil .div_u _ _)))))

theorem vP_tensor_val {A B : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vP (.tensor A B) ls δ v ρ) :
    ∃ a b ρ₁ ρ₂, v = .pair a b ∧ vP A ls δ a ρ₁ ∧ vP B ls δ b ρ₂ := by
  obtain ⟨a, b, hk⟩ := h
  obtain ⟨he, ρ₁, ρ₂, -, h₁, h₂⟩ := pure_sep_iff.mp hk
  exact ⟨a, b, ρ₁, ρ₂, he, h₁, h₂⟩

/-- **The program runs at every host**: from the empty memory to three 32-bit literals and a
boolean, and the empty memory. -/
theorem signProg_runs : ∃ (a b c : UInt32) (t : Val),
    BoCa.BoLo.Steps Adequacy.emptyMem signProg Adequacy.emptyMem
      (.val (.pair (Val.i32 a) (.pair (Val.i32 b) (.pair (Val.i32 c) t)))) ∧
      (t = .inj₁ .unit ∨ t = .inj₂ .unit) := by
  have hwp : wpTS [] signProg (fun _ v => Fig16.BoLo.pure (∃ (a b c : UInt32) (t : Val),
      v = .pair (Val.i32 a) (.pair (Val.i32 b) (.pair (Val.i32 c) t)) ∧
        (t = .inj₁ .unit ∨ t = .inj₂ .unit))) (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ⟨vP_empty_of_persistent rfl hv, ?_⟩) PMap.empty
      (wp_of_derives signProg_derives)
    obtain ⟨x, y, _, _, rfl, ⟨_, a, rfl⟩, hy⟩ := vP_tensor_val hv
    obtain ⟨x', y', _, _, rfl, ⟨_, b, rfl⟩, hy'⟩ := vP_tensor_val hy
    obtain ⟨x'', t, _, _, rfl, ⟨_, c, rfl⟩, ht⟩ := vP_tensor_val hy'
    exact ⟨a, b, c, t, rfl, (vC_boolT ht).2⟩
  obtain ⟨v, hsteps, a, b, c, t, rfl, ht⟩ := theorem32 signProg _ hwp
  exact ⟨a, b, c, t, hsteps, ht⟩

/-- The result `(a, (b, (c, t)))` as three integers and a boolean, when the run ends with no
cell left. -/
def signOf : Outcome → Option (UInt32 × UInt32 × UInt32 × Bool)
  | .value ⟨.pair a (.pair b (.pair c t)), _⟩ false => do
      pure (← i32Of a, ← i32Of b, ← i32Of c, ← boolOf t)
  | _ => none

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: `div_s (-7) 2 = -3` and `div_u (-7) 2 = 0x7FFFFFFC` differ,
`0x10000 * 0x10001` wraps to `0x10000`, and `div_u 1 0` takes the error branch. -/
theorem signProg_eval :
    signOf (eval signProg) = some (0xFFFFFFFD, 0x7FFFFFFC, 0x10000, true) := by decide

end BoCa.Fig16.LogRel.Core
