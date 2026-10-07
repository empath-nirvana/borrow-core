import Targets.Instance.Inversion
import Targets.A.NonVacuity
import Targets.Base.Support

/-!
# The Instance — checks on the route to `J₁` (TIER1-PLAN §2)

TIER1-PLAN §2 proves FL at `J₁` by elaborating each derivation of `J₁` into today's unr-free kernel
(`CDerivesNU`), each use of a row-`∀` entry a copy at its own instance, and then applying
`fundamentalC` unchanged.  These are the checks run before building `J₁`.

1. **The polymorphic let has no elaboration** (`not_elabClosed_of_letLaw`).  On a closed term the
   plan's elaboration copies nothing, so it says that a closed derivation of `J₁` at a `∀`-free
   type is a `CDerivesNU` derivation of the same term (`ElabClosed`).  The let law at a
   polymorphic value, and a body that reads the bound variable at two instances, type
   `(λx. ⟨x, x⟩) V` at `F(!U c₁) & F(!U c₂)`; no `CDerivesNU` derivation does (`not_der_letTwo`).
   So `J1Der.elab`, `letLaw_ourInst` and the rules the plan gives `J₁` cannot all hold.
2. **A-level handlers are not typed by today's `[handle]`** (`not_der_handle_tier1Open`).  Our
   instance's `handle` is the run-time frame, its clauses values; Core's `[handle]` types only
   `hndTerm n ir ic e`, its clauses variables (`not_der_handleK`).  So today's kernel at our
   instance types no program whose top former is a handler, and E4, E5, E6, E7 and E8 fail at
   `tier1Open` at every effect context (`not_deepHandler_tier1Open` and the four after it).  A
   typing system whose closed derivations elaborate fails E8 (`not_unwindPolicy_of_elabClosed`),
   and so fails tier 1 (`I.not_tier1_of_elabClosed`).
3. **S1's subeffecting ranges over every row of the algebra** (`not_subClosed_ourInst_tier1Open`).
   `SubClosed` asks a typed computation to be typed at every larger row, well formed or not.
   `[sub]` asks `Row.NU` of its target, and the algebra's rows include one with a resuming `unr`
   operation: `()` at the pure row is typed, at that row it is not (`not_der_unit_nonNU`).  The other
   three conjuncts of S1 hold (`rowAlgebra_noSub_ourInst`).
4. **The let law at today's kernel** (`letLaw_ourInst_tier1Open`): proved.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU RowForm EffCtx orowRF orowAlg ORow RowCtx RowEnv RowEq rowEq_refl)

/-- Every row variable at `anyCon`: the empty row is an admissible instance. -/
theorem models_anyCon_nil {Θ : RowCtx} (hΘ : ∀ p ∈ Θ, p.2 = anyCon) :
    Θ.Models (fun _ => []) := by
  intro ρ c hc
  have hc' : c = anyCon := hΘ _ hc
  subst hc'
  exact ⟨row_nu_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem models_append {Θ Θ' : RowCtx} {η : RowEnv} (h : (Θ ++ Θ').Models η) :
    Θ.Models η ∧ Θ'.Models η :=
  ⟨fun ρ c hc => h ρ c (List.mem_append_left _ hc), fun ρ c hc => h ρ c (List.mem_append_right _ hc)⟩

/-! ### 1. The polymorphic let has no elaboration -/

/-- **The plan's elaboration at closed judgements** (TIER1-PLAN §2's `J1Der.elab` at the empty
context, where no entry has copies, so that the elaborated term is the term itself): every closed
derivation of `J` at a `∀`-free judgement is, at every admissible instance, a `CDerivesNU`
derivation of the same term. -/
def ElabClosed {RF : RowForm} (J : OurTyping RF) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (e : Expr) (j : OJdg), J.der Θ Δ [] e j → j.RFree →
    ∀ η, Θ.Models η → CDerivesNU Δ [] e (j.den η)

/-- **The let law, a polymorphic value and a body that reads it at two instances leave no
elaboration.**  The plan's `J₁` gives the two typings this takes:
* `hV`: `λx. x` at `!U(∀ρ:any. 1 → F_ρ 1)` (`bangThunkV` over the empty context, then `[allR-I]`
  at `!U`);
* `hW`: `⟨x, x⟩`'s components read `x` by `[var]`, then `[allR-E]` at `!U` at the pure row and at
  `[o]`, then `[ret]`; `[&I]` pairs them (each component at the context `withCtx`, as Core's rule
  has it).

The let law then types the closed program `(λx. ⟨x, x⟩) (λx. x)` at `F(!U c₁) & F(!U c₂)`, and
`ElabClosed` would make it a `CDerivesNU` derivation, which `not_der_letTwo` refutes. -/
theorem not_elabClosed_of_letLaw {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} {b : Expr}
    {A : OVTy} {c₁ c₂ : CTy} (hr₁ : c₁.isRet = false) (hn₁ : ∀ C, c₁ ≠ .nu C)
    (hr₂ : c₂.isRet = false) (hn₂ : ∀ C, c₂ ≠ .nu C) (hne : c₁ ≠ c₂)
    (hL : (ourInst (ℍ := ℍ) RF Ξ J).LetLaw)
    (hV : (ourInst (ℍ := ℍ) RF Ξ J).derV [] ⟨.lam b, .lam⟩ A)
    (hW : (ourInst (ℍ := ℍ) RF Ξ J).der [A] (withPair (.var 2) (.var 2))
      (.amp (.ret (OVTy.ofV (.bang (.thunk c₁)))) (.ret (OVTy.ofV (.bang (.thunk c₂)))))) :
    ¬ ElabClosed J := by
  intro hE
  rcases hL [] _ A _ _ hV hW with ⟨Θ, hΘ, hd⟩ | ⟨-, M, he, -⟩
  · have hR : (OJdg.comp (.amp (.ret (OVTy.ofV (.bang (.thunk c₁))))
        (.ret (OVTy.ofV (.bang (.thunk c₂)))))).RFree :=
      ⟨OVTy.rFree_ofV _, OVTy.rFree_ofV _⟩
    have h := hE Θ _ _ _ hd hR (fun _ => []) (models_anyCon_nil hΘ)
    simp only [OJdg.den, OCTy.den, OVTy.den_ofV] at h
    exact not_der_letTwo hr₁ hn₁ hr₂ hn₂ hne h
  · change bindE (Expr.lam b) _ = _ at he
    simp [driveE, driveMark, bindE] at he

/-- The two instances of the check: `1 → F 1` and `1 → F_[o] 1`. -/
theorem not_elabClosed_of_letLaw_arr {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} {b : Expr}
    {A : OVTy} (o : OpSig) (hL : (ourInst (ℍ := ℍ) RF Ξ J).LetLaw)
    (hV : (ourInst (ℍ := ℍ) RF Ξ J).derV [] ⟨.lam b, .lam⟩ A)
    (hW : (ourInst (ℍ := ℍ) RF Ξ J).der [A] (withPair (.var 2) (.var 2))
      (.amp (.ret (OVTy.ofV (.bang (.thunk (.arr .unit (.ret .unit))))))
        (.ret (OVTy.ofV (.bang (.thunk (.arr .unit (CTy.effOf [o] .unit)))))))) :
    ¬ ElabClosed J :=
  not_elabClosed_of_letLaw rfl (fun _ h => by cases h) rfl (fun _ h => by cases h)
    (fun h => by simp [CTy.effOf] at h) hL hV hW

/-! ### 2. A-level handlers -/

/-- **Today's kernel types no A-level handler at our instance.** -/
theorem not_der_handle_tier1Open {Ξ : EffCtx} (Γ : List OVTy) (l : (orowAlg Ξ).Lab)
    (H : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Hnd) (M : Expr) (C : OCTy) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der Γ
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).handle l H M) C := by
  rintro (⟨Θ, hΘ, -, -, hd⟩ | ⟨-, M', he, -⟩)
  · exact not_der_handleK _ _ _ _ (hd (fun _ => []) (models_anyCon_nil hΘ))
  · change (handleK _ _ _).plug M = _ at he
    simp [driveE, driveMark, handleK, hndValE, Kont.plug] at he

/-- **A typing system whose closed derivations elaborate types no closed A-level handler**: the
elaborated derivation would be a `CDerivesNU` derivation of the run-time frame
(`not_der_handleK`). -/
theorem not_der_handle_of_elabClosed {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}
    (hE : ElabClosed J) (l : (RF.alg Ξ).Lab) (H : (ourInst (ℍ := ℍ) RF Ξ J).Hnd) (M : Expr)
    {C : OCTy} (hC : C.RFree) :
    ¬ (ourInst (ℍ := ℍ) RF Ξ J).der [] ((ourInst (ℍ := ℍ) RF Ξ J).handle l H M) C := by
  rintro (⟨Θ, hΘ, hd⟩ | ⟨-, M', he, -⟩)
  · exact not_der_handleK _ _ _ _ (hE Θ _ _ _ hd hC (fun _ => []) (models_anyCon_nil hΘ))
  · change (handleK _ _ _).plug M = _ at he
    simp [driveE, driveMark, handleK, hndValE, Kont.plug] at he

/-- **E8 fails at every typing system whose closed derivations elaborate** into today's kernel. -/
theorem not_unwindPolicy_of_elabClosed {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}
    (hE : ElabClosed J) : ¬ (ourInst (ℍ := ℍ) RF Ξ J).UnwindPolicy := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨la, lb, rfl⟩ := A.EffectSystem.eq_two hls.1
  exact not_der_handle_of_elabClosed hE _ _ _ (C := .effF _ (.sum .unit .unit)) ⟨trivial, trivial⟩
    (hP _ hls la lb rfl).1

section E
variable {Ξ : EffCtx}

/-- **E8 fails at today's kernel**: `e8a`'s top former is a handler. -/
theorem not_unwindPolicy_tier1Open : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).UnwindPolicy := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨la, lb, rfl⟩ := A.EffectSystem.eq_two hls.1
  exact not_der_handle_tier1Open _ _ _ _ _ (hP _ hls la lb rfl).1

/-- **E4 fails at today's kernel**: `deepGen`'s top former is a handler. -/
theorem not_deepHandler_tier1Open : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).DeepHandler := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨ly, lt, rfl⟩ := A.EffectSystem.eq_two hls.1
  exact not_der_handle_tier1Open _ _ _ _ _ (hP _ hls ly lt rfl).1

/-- **E5 fails at today's kernel**: `to_result (with_log …)`'s top former is a handler. -/
theorem not_nestedHandlers_tier1Open :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).NestedHandlers := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨llog, le, rfl⟩ := A.EffectSystem.eq_two hls.1
  exact not_der_handle_tier1Open _ _ _ _ _ (hP _ hls llog le rfl).2.2.1

/-- **E6 fails at today's kernel**: `tunnel`'s top former is a handler. -/
theorem not_tunnel_tier1Open : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Tunnel := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨li, lo, rfl⟩ := A.EffectSystem.eq_two hls.1
  obtain ⟨-, -, -, -, -, -, h, -⟩ := hP _ hls li lo rfl
  exact not_der_handle_tier1Open _ _ _ _ _ h

/-- **E7 fails at today's kernel**: `e7a`'s top former is a handler. -/
theorem not_cancelPolicy_tier1Open : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).CancelPolicy := by
  rintro ⟨⟨ls, hls⟩, hP⟩
  obtain ⟨lw, la, lb, rfl⟩ := A.EffectSystem.eq_three hls.1
  exact not_der_handle_tier1Open _ _ _ _ _ (hP _ hls lw la lb rfl).1

end E

/-! ### 3. S1 at our instance -/

section S1
variable {Ξ : EffCtx}

/-- A resuming `unr` operation: in no admissible effect context, but in rows of the algebra. -/
def unrOp : OpSig := ⟨1, 0, .unr, .unit, .unit⟩

theorem not_nu_unrOp : ¬ Row.NU [unrOp] := by
  intro h
  rcases h 1 0 unrOp (by simp [Row.find, unrOp]) with h | h <;>
    simp [OpSig.abort, unrOp, VTy.isZero] at h

/-- **S1's subeffecting, as written, fails at today's kernel.**  `SubClosed` ranges over every row
of the algebra.  `()` is typed at the pure row, and the pure row is below `[unrOp]`, whose operation
is a resuming `unr` one; `[sub]` asks `Row.NU` of its target, so `()` is not typed there. -/
theorem not_subClosed_ourInst_tier1Open : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).SubClosed := by
  intro hS
  have hd : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der [] (.unit)
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F (orowAlg Ξ).unit .unit) := by
    refine .inl ⟨[], by simp, fun _ h => absurd h List.not_mem_nil, trivial, fun η _ => ?_⟩
    exact CDerivesNU.ret (.unitI .nil)
  have hsub : (orowAlg Ξ).Sub (orowAlg Ξ).unit ⟨[unrOp], none⟩ :=
    ⟨⟨[unrOp], none⟩, ⟨[unrOp], none⟩, rfl, rfl, rowEq_refl _⟩
  rcases hS [] _ _ ⟨[unrOp], none⟩ .unit hd hsub with ⟨Θ, hΘ, -, -, hd'⟩ | ⟨-, M, he, -⟩
  · exact not_der_unit_nonNU (S := [unrOp] ++ []) not_nu_unrOp
      (hd' (fun _ => []) (models_anyCon_nil hΘ))
  · simp [driveE, driveMark] at he

/-- **S1, as written, fails at today's kernel.** -/
theorem not_rowAlgebra_ourInst_tier1Open : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).RowAlgebra :=
  fun h => not_subClosed_ourInst_tier1Open h.2.2.2

theorem row_nu_append {S S' : Row} (h : Row.NU S) (h' : Row.NU S') : Row.NU (S ++ S') := by
  intro n i o hf
  rw [Row.find_append] at hf
  cases hS : Row.find S n i with
  | none => rw [hS, Option.none_or] at hf; exact h' n i o hf
  | some o' => rw [hS, Option.some_or] at hf; cases hf; exact h n i o hS

/-- **Subeffecting at today's kernel, at a target row whose closed prefix is unr-free**: the
hypothesis `SubClosed` lacks.  A tail variable of the target is read at `anyCon`, which gives its
instances `Row.NU`; `[sub]` then applies at every instance. -/
theorem subClosed_nu_tier1Open {Γ : List OVTy} {e : Expr} {ε₁ ε₂ : ORow} {A : OVTy}
    (h : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der Γ e
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F ε₁ A))
    (hsub : (orowAlg Ξ).Sub ε₁ ε₂) (hNU : Row.NU ε₂.ops) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der Γ e ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F ε₂ A) := by
  have hle : ∀ η, RowLe (orowRF.den Ξ ε₁ η) (orowRF.den Ξ ε₂ η) :=
    rowLink_orowRF.sub Ξ ε₁ ε₂ hsub
  -- the target's tail, at `anyCon`
  let Θt : RowCtx := match ε₂.tail with | none => [] | some ρ => [(ρ, anyCon)]
  have hΘt : ∀ p ∈ Θt, p.2 = anyCon := by
    intro p hp
    simp only [Θt] at hp
    split at hp
    · exact absurd hp List.not_mem_nil
    · rw [List.mem_singleton] at hp; rw [hp]
  have hden : ∀ η, Θt.Models η → Row.NU (orowRF.den Ξ ε₂ η) := by
    intro η hη
    rw [orowRF_den]
    refine row_nu_append hNU ?_
    simp only [Θt] at hη
    split
    · exact row_nu_nil
    · rename_i ρ hρ
      rw [hρ] at hη
      exact (hη ρ anyCon (List.mem_singleton_self _)).1
  rcases h with ⟨Θ, hΘ, hRΓ, hRC, hd⟩ | ⟨hΓ, M, he, hL, Θ, hΘ, hRΓ, hRC, hd⟩
  · refine .inl ⟨Θ ++ Θt, fun p hp => ?_, hRΓ, hRC, fun η hη => ?_⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact hΘ p hp
      · exact hΘt p hp
    · obtain ⟨hη₁, hη₂⟩ := models_append hη
      exact CDerivesNU.effSub (hden η hη₂) (hle η) (hd η hη₁)
  · refine .inr ⟨hΓ, M, he, fun η => ?_, Θ ++ Θt, fun p hp => ?_, hRΓ, hRC, fun η hη => ?_⟩
    · obtain ⟨S, S₀, A₀, hS₀, hC⟩ := hL η
      have hC' : CTy.effOf (orowRF.den Ξ ε₁ η) (A.den η) = CTy.effOf S (.sum A₀ (.thunk (CTy.loopEff S₀ A₀ .unit))) := hC
      obtain ⟨rfl, hA⟩ := effOf_inj hC'
      refine ⟨orowRF.den Ξ ε₂ η, S₀, A₀, fun n i o hf => hle η n i o (hS₀ n i o hf), ?_⟩
      show CTy.effOf (orowRF.den Ξ ε₂ η) (A.den η) = _
      rw [hA]
    · rcases List.mem_append.mp hp with hp | hp
      · exact hΘ p hp
      · exact hΘt p hp
    · obtain ⟨hη₁, hη₂⟩ := models_append hη
      exact CDerivesNU.effSub (hden η hη₂) (hle η) (hd η hη₁)

/-- A signature's row finds each of its operations by index. -/
theorem find_ofEff_isSome (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k j : Nat) (i : UInt32),
    i.toNat = k + j → k + j < 2 ^ 32 → j < E.length → (Row.find (Row.ofEff n E k) n i).isSome
  | [], _, _, _, _, _, h => absurd h (by simp)
  | (q, A, B) :: E, k, 0, i, hi, hk, _ => by
      have hik : i = UInt32.ofNat k := by
        apply UInt32.toNat.inj
        rw [hi, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        rfl
      subst hik
      simp [Row.ofEff, Row.find]
  | (q, A, B) :: E, k, j + 1, i, hi, hk, hj => by
      have hne : i ≠ UInt32.ofNat k := by
        intro h
        rw [h, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at hi
        omega
      have ih := find_ofEff_isSome n E (k + 1) j i (by omega) (by omega)
        (by simp only [List.length_cons] at hj; omega)
      unfold Row.find at ih ⊢
      rw [Row.ofEff, List.find?_cons_of_neg (by simp [hne])]
      exact ih

/-- `has` at the minimal open-row form: the row's closed prefix has the operation. -/
theorem has_orow {J : OurTyping orowRF} {ε : ORow} {l : (orowAlg Ξ).Lab} {i : ℕ} :
    (ourInst (ℍ := ℍ) orowRF Ξ J).has ε l i ↔
      i < 2 ^ 32 ∧ Targets.Row.Has ε.ops l.1 (UInt32.ofNat i) := by
  constructor
  · rintro ⟨hi, h⟩
    refine ⟨hi, ?_⟩
    have h0 := h (fun _ => [])
    simp only [Targets.Row.Has, Row.find_append] at h0 ⊢
    cases ht : ε.tail <;> simp_all [Row.find]
  · rintro ⟨hi, h⟩
    refine ⟨hi, fun η => ?_⟩
    simp only [Targets.Row.Has, Row.find_append] at h ⊢
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
    simp [ho]

theorem has_iff_append {S S' : Row} {n i : UInt32} :
    Targets.Row.Has (S ++ S') n i ↔ Targets.Row.Has S n i ∨ Targets.Row.Has S' n i := by
  simp only [Targets.Row.Has, Row.find_append]
  cases Row.find S n i <;> simp

/-- **`RowSig` at the minimal open-row form**, at every typing system. -/
theorem rowSig_orow {J : OurTyping orowRF} : (ourInst (ℍ := ℍ) orowRF Ξ J).RowSig := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro (l : (orowAlg Ξ).Lab) (m : (orowAlg Ξ).Lab) i
    refine (has_orow (ε := ⟨Row.ofEff l.1 (Ξ l.1) 0, none⟩)).trans ?_
    have hsl : ((ourInst (ℍ := ℍ) orowRF Ξ J).sig l).length = (Ξ l.1).length := by
      unfold ourInst; simp
    rw [hsl]
    constructor
    · rintro ⟨hi, h⟩
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hm, j, hj, hij, -⟩ := Row.find_ofEff _ _ _ _ _ _ ho
      have hlen := l.2.2.2
      have : i = j := by
        have := congrArg UInt32.toNat hij
        rw [UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size] using hi), Nat.zero_add,
          UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at this
        exact this
      exact ⟨Subtype.ext hm, this ▸ hj⟩
    · rintro ⟨rfl, hi⟩
      have hlen := m.2.2.2
      refine ⟨by omega, ?_⟩
      exact find_ofEff_isSome m.1 (Ξ m.1) 0 i _
        (by rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]; omega) (by omega) hi
  · intro (l : (orowAlg Ξ).Lab) i h
    have h' := (has_orow (ε := ⟨[], none⟩)).mp h
    simp [Targets.Row.Has, Row.find] at h'
  · intro (ε₁ : ORow) (ε₂ : ORow) (ε : ORow) (l : (orowAlg Ξ).Lab) i hc
    refine has_orow.trans (Iff.trans ?_ (or_congr has_orow has_orow).symm)
    cases ht : ε₁.tail with
    | none =>
        change (orowAlg Ξ).comp ε₁ ε₂ = some ε at hc
        rw [orow_comp_none ht, Option.some.injEq] at hc
        subst hc
        simp only [has_iff_append]
        tauto
    | some ρ =>
        change (orowAlg Ξ).comp ε₁ ε₂ = some ε at hc
        rw [orow_comp_some ht] at hc
        split at hc
        · rename_i h₂
          cases hc
          rw [h₂.1]
          simp [Targets.Row.Has, Row.find]
        · cases hc
  · rintro (ε₁ : ORow) (ε₂ : ORow) (l : (orowAlg Ξ).Lab) i ⟨-, hr⟩
    refine has_orow.trans (Iff.trans ?_ has_orow.symm)
    simp only [Targets.Row.Has, hr _ _]
  · intro (α : RVar) (ε' : ORow) (ε : ORow) (l : (orowAlg Ξ).Lab) i h
    obtain ⟨hi, h⟩ := has_orow.mp h
    refine has_orow.mpr ⟨hi, ?_⟩
    show Targets.Row.Has (if ε.tail = some α then (⟨ε.ops ++ ε'.ops, ε'.tail⟩ : ORow) else ε).ops _ _
    split
    · exact has_iff_append.mpr (.inl h)
    · exact h
  · intro (α : RVar) (ε' : ORow) (ε : ORow) (l : (orowAlg Ξ).Lab) i h
    obtain ⟨hi, h⟩ := has_orow.mp h
    change Targets.Row.Has (if ε.tail = some α then (⟨ε.ops ++ ε'.ops, ε'.tail⟩ : ORow) else ε).ops _ _
      at h
    split at h
    · rcases has_iff_append.mp h with h | h
      · exact .inl (has_orow.mpr ⟨hi, h⟩)
      · exact .inr (has_orow.mpr ⟨hi, h⟩)
    · exact .inl (has_orow.mpr ⟨hi, h⟩)
  · intro (l : (orowAlg Ξ).Lab) h
    have := l.2.2.1
    change (Ξ l.1).map _ = [] at h
    simp only [List.map_eq_nil_iff] at h
    exact this h

/-- **S1 at our instance, `SubClosed` aside**: the algebra's laws, its safety and one signature
object. -/
theorem rowAlgebra_noSub_ourInst {J : OurTyping orowRF} :
    (ourInst (ℍ := ℍ) orowRF Ξ J).EA.Laws ∧ (ourInst (ℍ := ℍ) orowRF Ξ J).EA.Safe ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J).RowSig :=
  ⟨orowAlg_laws Ξ, orowAlg_safe Ξ, rowSig_orow⟩

end S1

/-! ### 4. The let law at today's kernel -/

theorem splitP_kill_left : ∀ Γ : Ctx VTy, Ctx.SplitP Γ (kill Γ) Γ
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .right (splitP_kill_left Γ)
  | ⟨_, false⟩ :: Γ => .dead (splitP_kill_left Γ)

/-- **The let law at today's kernel** (CBPV's `[let]` at a returned value): the closed value, typed
at the empty context, is weakened by the dead slots of the body's context (`append_dead`). -/
theorem letLaw_ourInst_tier1Open {Ξ : EffCtx} : (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).LetLaw := by
  intro Γ V A N C hV hN
  obtain ⟨Θ, hΘ, -, hRA, hVd⟩ := hV
  rcases hN with ⟨Θ', hΘ', hRΓ, hRC, hNd⟩ | ⟨h, -⟩
  · refine .inl ⟨Θ ++ Θ', fun p hp => ?_, fun s hs => hRΓ s (List.mem_cons_of_mem _ hs), hRC,
      fun η hη => ?_⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact hΘ p hp
      · exact hΘ' p hp
    · obtain ⟨hη₁, hη₂⟩ := models_append hη
      have hv : CDerivesNU LifeCtx.empty [] V.1 (.val (A.den η)) := hVd η hη₁
      have hn := hNd η hη₂
      exact CDerivesNU.bind (splitP_kill_left _) (.ret (hv.append_dead (kill_dead _))) hn
  · cases h

end Targets.Inst

end
