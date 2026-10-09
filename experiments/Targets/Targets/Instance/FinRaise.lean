import Targets.Instance.J1
import Targets.A.NonVacuity

/-!
# The Instance — a finaliser that raises to its context is not typed (option A, decision D3)

Core's `[then]` types its finaliser at the pure row (SPEC §24, option A): a finaliser handles its
own raises, and none escapes it.  A's cancel and unwind policies (E7, E8) and its stored
continuation's cancel (E9c) are stated at programs whose finaliser raises an error to a handler
outside the finaliser: `e7b`, `e7c`, `e7d`, `e8b`, `e9c`.  `J₁`, Core's kernel with its inner rows
tied to the effect context, types none of them, at any context and judgement, so E7, E8 and E9 fail
as written at `J₁` at every effect context.

* `derAt_raise`: a tied derivation of `raise (n, (i, V))` is at a computation type whose row has the
  operation `(n, i)` (`CTy.HasOp`); `F 1` has none (`not_derAt_raise_ret`).
* `derAt_then`: a tied derivation of `M then x. N unwind D` types the finaliser `D` at `F 1`
  (`[then]` is the only rule whose conclusion's term is a finaliser frame).
* `derAt_let_arg`: a tied derivation of `(λx. N) M` types `M`, unless `M` is a λ-value, a variable
  or one of the arguments `()`, `inj₁ ()`, `inj₂ ()` of `∀E` and the projections.
* With `derAt_hnd` (`Targets/Instance/TiedKernel.lean`), each program's finaliser is read off its
  handlers and `let`s: `not_derAt_e7b` … `not_derAt_e9c`, and so `not_cancelPolicy_J₁`,
  `not_unwindPolicy_J₁`, `not_storedK_J₁`.

Each inversion is one induction on the derivation; a rule whose premise has the conclusion's term
carries the claim through, every other rule is told apart by its conclusion's term (`cdat_terms`).
`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)

/-! ### The operations of a computation type's row -/

/-- **The operation `(n, i)` is in a computation type's row**: a layer of `F_Σ` at the key `(n, i)`,
under `ν`'s observations as `ν`'s unrolling reads them. -/
def CTy.HasOp (n i : UInt32) : CTy → Prop
  | .eff n' i' _ _ _ _ C => (n' = n ∧ i' = i) ∨ CTy.HasOp n i C
  | .nu C => CTy.HasOp n i C
  | _ => False

theorem CTy.hasOp_instT (n i : UInt32) (S : VTy) :
    ∀ C : CTy, CTy.HasOp n i (CTy.instT S C) ↔ CTy.HasOp n i C
  | .ret _ | .amp _ _ | .arr _ _ | .top | .all _ _ _ | .nu _ => Iff.rfl
  | .eff n' i' q A B fin C => by
      simp only [CTy.instT, CTy.HasOp, CTy.hasOp_instT n i S C]

theorem CTy.hasOp_unroll (n i : UInt32) (C : CTy) :
    CTy.HasOp n i C.unroll ↔ CTy.HasOp n i C :=
  CTy.hasOp_instT n i _ C

/-- A row's returner has the operation `(n, i)` exactly when a layer of the row is at that key. -/
theorem CTy.hasOp_effOf (n i : UInt32) (A : VTy) :
    ∀ S : Row, CTy.HasOp n i (CTy.effOf S A) ↔ ∃ o ∈ S, o.n = n ∧ o.i = i
  | [] => by simp [CTy.effOf, CTy.HasOp]
  | o :: S => by
      simp only [CTy.effOf, CTy.HasOp, CTy.hasOp_effOf n i A S, List.mem_cons]
      constructor
      · rintro (h | ⟨o', ho', h⟩)
        · exact ⟨o, .inl rfl, h⟩
        · exact ⟨o', .inr ho', h⟩
      · rintro ⟨o', (rfl | ho'), h⟩
        · exact .inl h
        · exact .inr ⟨o', ho', h⟩

/-- A row has a layer at a key exactly when it finds an operation there. -/
theorem Row.find_isSome_iff {S : Row} {n i : UInt32} :
    (∃ o, Row.find S n i = some o) ↔ ∃ o ∈ S, o.n = n ∧ o.i = i := by
  constructor
  · rintro ⟨o, h⟩
    obtain ⟨hm, hn, hi⟩ := Row.find_mem h
    exact ⟨o, hm, hn, hi⟩
  · rintro ⟨o, hm, hn, hi⟩
    unfold Row.find
    have hs : (S.find? fun o => decide (n = o.n ∧ i = o.i)).isSome = true :=
      List.find?_isSome.mpr ⟨o, hm, decide_eq_true ⟨hn.symm, hi.symm⟩⟩
    exact Option.isSome_iff_exists.mp hs

/-- `[sub]` keeps the operations of the row. -/
theorem CTy.hasOp_of_rowLe {S S' : Row} (hle : RowLe S S') {n i : UInt32} (A : VTy)
    (h : CTy.HasOp n i (CTy.effOf S A)) : CTy.HasOp n i (CTy.effOf S' A) := by
  rw [CTy.hasOp_effOf] at h ⊢
  obtain ⟨o, hf⟩ := Row.find_isSome_iff.mpr h
  obtain ⟨o', hf', -⟩ := hle n i o hf
  exact Row.find_isSome_iff.mp ⟨o', hf'⟩

/-! ### Inversions of the tied kernel -/

section Inv
variable {Ξ : EffCtx}

/-- `raise` alone has no tied derivation. -/
theorem not_derAt_prim_raise {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : e ≠ .prim .raise := by
  induction h <;> intro he <;> cdat_terms
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he

theorem not_derAt_prim_raise' {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} :
    ¬ CDerivesAt Ξ Δ Γ (.prim .raise) j := fun h => not_derAt_prim_raise h rfl

/-- `ubind` alone has no tied derivation. -/
theorem not_derAt_prim_ubind {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : e ≠ .prim .ubind := by
  induction h <;> intro he <;> cdat_terms
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he

theorem not_derAt_prim_ubind' {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} :
    ¬ CDerivesAt Ξ Δ Γ (.prim .ubind) j := fun h => not_derAt_prim_ubind h rfl

/-- `ubind X` alone has no tied derivation. -/
theorem not_derAt_app_ubind {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ X, e ≠ .app (.prim .ubind) X := by
  induction h <;> intro X he <;> cdat_terms <;> (try simp_all [not_derAt_prim_ubind'])
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he

theorem not_derAt_app_ubind' {Δ : LifeCtx} {Γ : Ctx VTy} {X : Expr} {j : Jdg} :
    ¬ CDerivesAt Ξ Δ Γ (.app (.prim .ubind) X) j := fun h => not_derAt_app_ubind h X rfl

/-- **A tied derivation of `raise (n, (i, V))` is at a computation type whose row has `(n, i)`.** -/
theorem derAt_raise {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ (n i : UInt32) (V : Expr),
      e = BoCa.BoLo.raiseE (opArgE n i V) → ∃ C, j = .comp C ∧ CTy.HasOp n i C := by
  induction h <;> intro n i V he <;> cdat_terms <;>
    (try simp_all [not_derAt_prim_raise', CTy.HasOp])
  case force _ _ i' C _ =>
    rcases Inst.forceE_cases C (.var i') with h | h <;> rw [h] at he <;> simp at he
  case effSub _ _ _ S S' A hle _ ih =>
    exact CTy.hasOp_of_rowLe hle A ih
  case nuIn _ _ _ C _ _ ih =>
    exact (CTy.hasOp_unroll n i C).mp ih
  case nuOut _ _ _ C _ _ ih =>
    exact (CTy.hasOp_unroll n i C).mpr ih
  case effRaise _ _ _ S o B _ hf _ _ _ _ =>
    exact (CTy.hasOp_effOf _ _ B S).mpr ⟨o, (Row.find_mem hf).1, by simp_all⟩

/-- **No tied derivation types a raise at a pure returner.** -/
theorem not_derAt_raise_ret {Δ : LifeCtx} {Γ : Ctx VTy} {n i : UInt32} {V : Expr} {A : VTy} :
    ¬ CDerivesAt Ξ Δ Γ (BoCa.BoLo.raiseE (opArgE n i V)) (.comp (.ret A)) := by
  intro h
  obtain ⟨C, hC, hop⟩ := derAt_raise h n i V rfl
  cases hC
  exact hop

/-- **A tied derivation of a finaliser frame types its finaliser at `F 1`**: `[then]` is the only
rule whose conclusion's term is `M then x. N unwind D`. -/
theorem derAt_then {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ N D M, e = thenE N D M →
      ∃ Γ₂ : Ctx VTy, CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit)) := by
  induction h <;> intro N D M he <;> cdat_terms <;> (try simp_all [not_derAt_app_ubind'])
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he
  case effThen =>
    obtain ⟨⟨-, rfl⟩, -⟩ := he
    exact ⟨_, by assumption⟩

/-- **A tied derivation of a `let` `(λx. N) M` types `M`**, unless `M` is a λ-value (`[let-poly]`),
a variable (`[app]` at the λ-value) or the argument `()`, `inj₁ ()`, `inj₂ ()` of `∀E` and the
projections. -/
theorem derAt_let_arg {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : ∀ N M, e = .app (.lam N) M →
      (∃ b, M = .lam b) ∨ (∃ i, M = .var i) ∨ M = .unit ∨ M = .inj₁ .unit ∨ M = .inj₂ .unit ∨
        ∃ (Γ' : Ctx VTy) (j' : Jdg), CDerivesAt Ξ Δ Γ' M j' := by
  induction h <;> intro N M he <;> cdat_terms
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he
  case app he => exact .inr (.inl ⟨_, he.2.symm⟩)
  all_goals (obtain ⟨-, rfl⟩ := ‹_ ∧ _›; exact .inr (.inr (.inr (.inr (.inr ⟨_, _, by assumption⟩)))))

end Inv

end Targets

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesAt derAt_hnd derAt_then derAt_let_arg not_derAt_raise_ret)

/-! ### The programs whose finaliser raises to its context -/

section Programs
variable {Ξ : EffCtx}

/-- A tied derivation of a handler frame around `M` types `M`. -/
theorem derAt_handleK {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} {n : UInt32} {qs r : Expr}
    {cs : List Expr} {M : Expr} (h : CDerivesAt Ξ Δ Γ ((handleK n qs r cs).plug M) j) :
    ∃ (Γ' : Ctx VTy) (C : CTy), CDerivesAt Ξ Δ Γ' M (.comp C) :=
  (derAt_hnd h n qs (.pair r (clausesE cs)) M rfl).2

/-- A tied derivation of a finaliser frame `M then x. N unwind D` types `D`, under the frame's
binder, at `F 1`. -/
theorem derAt_thenK {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} {N D M : Expr}
    (h : CDerivesAt Ξ Δ Γ ((thenK N D).plug M) j) :
    ∃ Γ₂ : Ctx VTy, CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ₂) (D.shift 1 0) (.comp (.ret .unit)) :=
  derAt_then h N (D.shift 1 0) M rfl

/-- A raise at our instance, shifted past the finaliser's binder, is the raise. -/
theorem raise_shift {J : OurTyping orowRF} (l : (orowAlg Ξ).Lab) :
    ((ourInst (ℍ := ℍ) orowRF Ξ J).raise l 0 (ourInst (ℍ := ℍ) orowRF Ξ J).unitV).shift 1 0 =
      BoCa.BoLo.raiseE (opArgE l.1 (UInt32.ofNat 0) (.val .unit)) := by
  show Expr.shift 1 0 (if (0 : ℕ) < 2 ^ 32 then
      BoCa.BoLo.raiseE (opArgE l.1 (UInt32.ofNat 0) (.val .unit)) else opJunk true) = _
  rw [if_pos (by norm_num)]
  rfl

/-- **A finaliser frame whose finaliser raises at our instance has no tied derivation.** -/
theorem not_derAt_thenK_raise {J : OurTyping orowRF} {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg}
    {N M : Expr} (l : (orowAlg Ξ).Lab) :
    ¬ CDerivesAt Ξ Δ Γ ((thenK N ((ourInst (ℍ := ℍ) orowRF Ξ J).raise l 0
      (ourInst (ℍ := ℍ) orowRF Ξ J).unitV)).plug M) j := by
  intro h
  obtain ⟨Γ₂, hD⟩ := derAt_thenK h
  rw [raise_shift] at hD
  exact not_derAt_raise_ret hD

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- A closed program `J₁` types at our instance, not a driven one, is typed by the tied kernel. -/
theorem derAt_of_der_J₁ {e : Expr} {C : OCTy} (h : (𝕁).der [] e C) (hd : ∀ M, e ≠ driveE M) :
    ∃ C' : CTy, CDerivesAt Ξ LifeCtx.empty [] e (.comp C') := by
  obtain ⟨-, ⟨Θ, hΘ, hd'⟩ | ⟨-, M, he, -⟩⟩ := h
  · exact ⟨_, coreClosedAt_J₁ Ξ hΘ hd'⟩
  · exact absurd he (hd M)

theorem handleK_ne_drive (n : UInt32) (qs r : Expr) (cs : List Expr) (M M' : Expr) :
    (handleK n qs r cs).plug M ≠ driveE M' := by
  simp [driveE, driveMark, handleK, hndValE, Kont.plug]

theorem bindE_ne_drive (M N M' : Expr) : bindE M N ≠ driveE M' := by
  simp [driveE, driveMark, bindE, Expr.val, Val.lam]

/-- **`e7b` is not typed at `J₁`**: its finaliser raises `exnₒ` to the handler outside the
timeout, and `[then]` types a finaliser at `F 1` (option A). -/
theorem not_der_e7b_J₁ (lw lo : (orowAlg Ξ).Lab) (C : OCTy) : ¬ (𝕁).der [] ((𝕁).e7b lw lo) C := by
  intro h
  obtain ⟨C', hd⟩ := derAt_of_der_J₁ h (handleK_ne_drive _ _ _ _ _)
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  exact not_derAt_thenK_raise lo hd

/-- **`e7c` is not typed at `J₁`**: its finaliser raises `exnᵢ` to the handler inside the timeout. -/
theorem not_der_e7c_J₁ (lw li : (orowAlg Ξ).Lab) (C : OCTy) : ¬ (𝕁).der [] ((𝕁).e7c lw li) C := by
  intro h
  obtain ⟨C', hd⟩ := derAt_of_der_J₁ h (handleK_ne_drive _ _ _ _ _)
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  exact not_derAt_thenK_raise li hd

/-- **`e8b` is not typed at `J₁`**: its finaliser raises `exn_b` past the unwind of `exn_a`. -/
theorem not_der_e8b_J₁ (la lb : (orowAlg Ξ).Lab) (C : OCTy) : ¬ (𝕁).der [] ((𝕁).e8b la lb) C := by
  intro h
  obtain ⟨C', hd⟩ := derAt_of_der_J₁ h (handleK_ne_drive _ _ _ _ _)
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  exact not_derAt_thenK_raise lb hd

/-- **`e9c` is not typed at `J₁`**: the stored continuation's frame holds a finaliser that raises
`exnₒ`. -/
theorem not_der_e9c_J₁ (ly lo : (orowAlg Ξ).Lab) (C : OCTy) : ¬ (𝕁).der [] ((𝕁).e9c ly lo) C := by
  intro h
  obtain ⟨C', hd⟩ := derAt_of_der_J₁ h (handleK_ne_drive _ _ _ _ _)
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  rcases derAt_let_arg hd _ _ rfl with ⟨b, hb⟩ | ⟨i, hi⟩ | hu | hu | hu | ⟨_, _, hd⟩
  · simp [A.EffectSystem.stash, ourInst, handleK, Kont.plug] at hb
  · simp [A.EffectSystem.stash, ourInst, handleK, Kont.plug] at hi
  · simp [A.EffectSystem.stash, ourInst, handleK, Kont.plug] at hu
  · simp [A.EffectSystem.stash, ourInst, handleK, Kont.plug] at hu
  · simp [A.EffectSystem.stash, ourInst, handleK, Kont.plug] at hu
  obtain ⟨_, _, hd⟩ := derAt_handleK hd
  exact not_derAt_thenK_raise lo hd

/-- **E7 fails as written at `J₁`**, at every effect context: `e7b`'s finaliser raises to its
context. -/
theorem not_cancelPolicy_J₁ : ¬ (𝕁).CancelPolicy := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨lw, la, lb, rfl⟩ := A.EffectSystem.eq_three hls.1
  obtain ⟨-, -, h, -⟩ := hP _ hls lw la lb rfl
  exact not_der_e7b_J₁ lw la _ h

/-- **E8 fails as written at `J₁`**, at every effect context: `e8b`'s finaliser raises to its
context. -/
theorem not_unwindPolicy_J₁ : ¬ (𝕁).UnwindPolicy := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨la, lb, rfl⟩ := A.EffectSystem.eq_two hls.1
  obtain ⟨-, -, h, -⟩ := hP _ hls la lb rfl
  exact not_der_e8b_J₁ la lb _ h

/-- **E9 fails as written at `J₁`**, at every effect context: `e9c`'s finaliser raises to its
context. -/
theorem not_storedK_J₁ : ¬ (𝕁).StoredK := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨ly, lo, rfl⟩ := A.EffectSystem.eq_two hls.1
  obtain ⟨-, -, -, -, h, -⟩ := hP _ hls ly lo rfl
  exact not_der_e9c_J₁ ly lo _ h

/-- **A's (E) properties fail as written at `J₁`**, at every effect context: E7, E8 and E9 each
type a finaliser that raises to its context, which option A's `[then]` does not admit. -/
theorem not_eProps_J₁ : ¬ (𝕁).EProps :=
  fun h => not_cancelPolicy_J₁ h.2.2.2.2.2.2.1

end Programs

end Targets.Inst
