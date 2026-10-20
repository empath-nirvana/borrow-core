import Frontend.Check.CrossCheck
import Core.Steps

/-!
# DepSpike — a law about a function `bcc` checks, as a Lean theorem  (#625)

**Question.** Can a law about a function, as `bcc` elaborates and checks it (its erasure, not a
hand transcription), be stated as a Lean proposition about Core's machine and proved for every
argument, with no new machinery in `Core/`?

**Answer here: yes, for a straight-line function at a persistent type.**

* `laws.bc` declares `max : !(i32 * i32 => i32)` in the core syntax. `bcc_program%` embeds its
  AST and `max_erasure` shows, by kernel evaluation of the checker, that the checker accepts it
  at that type and erases it to `maxV` (as `Frontend/Check/CrossCheck.lean` does for §13.1).
* `max_runs`: every run of `max (a, b)` to a value, from any memory, ends at `i32[smax a b]` with
  the memory unchanged, and that run exists. It holds at every host that conforms to the
  language's integer operations (`Host.Conforms`), for every `a b : UInt32`.
* `max_comm`, `max_ge_left`: the laws `max(a, b) == max(b, a)` and `max(a, b) >= a`, read as
  statements about every run. `max_assoc` and `max_unit`: `max` and `i32[0x80000000]` are a
  monoid, the law a parallel reduction needs (#620); nested calls compose through
  `steps_plug_det`. The facts about `smax` are closed by `omega` through `toInt`.
  `bv_decide` closes them too, but its proofs depend on axioms it generates for native
  evaluation, outside `[propext, Classical.choice, Quot.sound]`, so it is not used.

What it needed beyond `Core/`: three inversion lemmas for single steps (`step1_host_inv`,
`step1_case_inv`, `step1_seq_inv`), each a few lines from `Head`'s cases, beside `Core.Steps`'
`step1_beta_inv` and `step1_letpair_inv`. `runM` does not take the host step, so the run is not
computed by `rfl`.

No `sorry`, no axiom: the `#print axioms` at the end of the file shows each result within
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace DepSpike

open BoCa
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Fig16.LogRel.Core (step1_top step1_beta_inv step1_letpair_inv steps_peel
  steps_from_val)
open Frontend.Check (defErasure)

/-! ### The function, as `bcc` checks it -/

/-- `laws.bc`, as the parser gives it. -/
def lawsProg : Frontend.Program := bcc_program% "experiments/DepSpike/DepSpike/laws.bc"

/-- `max`'s body under its `λ`: `let (a, b) = p; c <- lt_s (a, b); case c { _ -> a | _ -> b }`. -/
def maxB : Expr :=
  .letpair (.var 0)
    (.app (.lam (.case (.var 0) (.seq (.var 0) (.var 3)) (.seq (.var 0) (.var 2))))
      (.app (.prim (.host (.rel .w32 .lt_s))) (.pair (.var 1) (.var 0))))

/-- `max`'s erasure, a closed `λ`. -/
def maxV : Val := .lam maxB

set_option maxRecDepth 100000 in
/-- **The checker accepts `max` at `!(i32 ⊗ i32 ⊸ F i32)` and erases it to `maxV`.** -/
theorem max_erasure : defErasure lawsProg 0 = some maxV.1 := by
  decide +kernel

/-! ### Single steps -/

variable {ℍ : Host} [HostIs ℍ]

/-- The host step is the only step of `op v`. -/
theorem step1_host_inv {μ μ₁ : Heap} {op : HostOp} {v : Val} {e₁ : Expr}
    (h : Step1 (ℍ := ℍ) μ (.app (.prim (.host op)) v.1) μ₁ e₁) :
    ∃ r : Val, ℍ.call op v = some r ∧ μ₁ = μ ∧ e₁ = r.1 := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | appR f K =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.2 ▸ v.2)
    | appL K u =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.prim)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.app (.prim (.host op)) v.1 = E at hh
  cases hh with
  | host op' v' r hr =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, Expr.prim.injEq, Prim.host.injEq] at hE
      obtain ⟨rfl, hv⟩ := hE
      obtain rfl : v = v' := Subtype.ext hv
      exact ⟨r, hr, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE]

/-- `case v {b₁ | b₂}` steps only at an injection, to the branch at its payload. -/
theorem step1_case_inv {μ μ₁ : Heap} {v : Val} {b₁ b₂ e₁ : Expr}
    (h : Step1 (ℍ := ℍ) μ (.case v.1 b₁ b₂) μ₁ e₁) :
    μ₁ = μ ∧ ((∃ u : Val, v = .inj₁ u ∧ e₁ = b₁.subst 0 u) ∨
      (∃ u : Val, v = .inj₂ u ∧ e₁ = b₂.subst 0 u)) := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | case K u₁ u₂ =>
        simp only [Kont.plug, Expr.case.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ v.2)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.case v.1 b₁ b₂ = E at hh
  cases hh with
  | case₁ u _ _ =>
      simp only [Expr.case.injEq, Expr.val, Val.inj₁] at hE
      obtain ⟨hv, rfl, rfl⟩ := hE
      exact ⟨rfl, .inl ⟨u, Subtype.ext hv, rfl⟩⟩
  | case₂ u _ _ =>
      simp only [Expr.case.injEq, Expr.val, Val.inj₂] at hE
      obtain ⟨hv, rfl, rfl⟩ := hE
      exact ⟨rfl, .inr ⟨u, Subtype.ext hv, rfl⟩⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE]

/-- `(); e` steps only to `e`. -/
theorem step1_seq_inv {μ μ₁ : Heap} {e e₁ : Expr}
    (h : Step1 (ℍ := ℍ) μ (.seq .unit e) μ₁ e₁) : μ₁ = μ ∧ e₁ = e := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | seq K u =>
        simp only [Kont.plug, Expr.seq.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.unit)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.seq .unit e = E at hh
  cases hh with
  | seq => simp only [Expr.seq.injEq] at hE; obtain ⟨-, rfl⟩ := hE; exact ⟨rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE]

/-! ### The law's Lean side -/

/-- Signed `max` on the bits, as the language's `lt_s` reads them. -/
def smax (a b : UInt32) : UInt32 := if Prim.rel .lt_s a.toBitVec b.toBitVec then b else a

/-- The host's answer at `lt_s (a, b)`, at a conforming host. -/
theorem call_lt (hℍ : ℍ.Conforms) (a b : UInt32) :
    ℍ.call (.rel .w32 .lt_s) (Val.pair (.i32 a) (.i32 b)) =
      some (.bool (Prim.rel .lt_s a.toBitVec b.toBitVec)) := by
  simp [Host.call, Expr.args32?, Expr.arg32?, Expr.lit?, Val.i32, Val.pair, hℍ.rel32, wasmHost]

/-- The `case` `max` ends with, under the comparison's binder. -/
def maxCase (a b : UInt32) : Expr :=
  .case (.var 0) (.seq (.var 0) (Val.i32 a).1) (.seq (.var 0) (Val.i32 b).1)

/-- `max`'s last steps, from the comparison's answer `c`. -/
theorem maxCase_runs (a b : UInt32) (c : Bool) {μ₀ μ' : Heap} {w : Val} :
    Steps (ℍ := ℍ) μ₀ (.app (.lam (maxCase a b)) (Val.bool c).1) μ' w.1 ↔
      μ' = μ₀ ∧ w = .i32 (if c then b else a) := by
  have hsub : (maxCase a b).subst 0 (Val.bool c) =
      .case (Val.bool c).1 (.seq (.var 0) (Val.i32 a).1) (.seq (.var 0) (Val.i32 b).1) := by
    cases c <;> rfl
  constructor
  · intro hs
    have h1 := steps_peel hs (by simp [Val.bool])
      fun μ₁ e₁ h => step1_beta_inv h
    rw [hsub] at h1
    cases c with
    | false =>
        have h2 := steps_peel h1 (by simp) (e' := .seq .unit (Val.i32 a).1) (m := μ₀)
          fun μ₁ e₁ h => by
            obtain ⟨rfl, hc⟩ := step1_case_inv h
            rcases hc with ⟨u, hu, rfl⟩ | ⟨u, hu, -⟩
            · obtain rfl : u = .unit := by
                have := congrArg Subtype.val hu
                exact Subtype.ext (by simpa [Val.bool, Val.inj₁, Val.unit] using this.symm)
              exact ⟨rfl, rfl⟩
            · exact absurd (congrArg Subtype.val hu) (by simp [Val.bool, Val.inj₁, Val.inj₂])
        have h3 := steps_peel h2 (by simp) (e' := (Val.i32 a).1) (m := μ₀)
          fun μ₁ e₁ h => step1_seq_inv h
        obtain ⟨rfl, rfl⟩ := steps_from_val h3
        exact ⟨rfl, by simp⟩
    | true =>
        have h2 := steps_peel h1 (by simp) (e' := .seq .unit (Val.i32 b).1) (m := μ₀)
          fun μ₁ e₁ h => by
            obtain ⟨rfl, hc⟩ := step1_case_inv h
            rcases hc with ⟨u, hu, -⟩ | ⟨u, hu, rfl⟩
            · exact absurd (congrArg Subtype.val hu) (by simp [Val.bool, Val.inj₁, Val.inj₂])
            · obtain rfl : u = .unit := by
                have := congrArg Subtype.val hu
                exact Subtype.ext (by simpa [Val.bool, Val.inj₂, Val.unit] using this.symm)
              exact ⟨rfl, rfl⟩
        have h3 := steps_peel h2 (by simp) (e' := (Val.i32 b).1) (m := μ₀)
          fun μ₁ e₁ h => step1_seq_inv h
        obtain ⟨rfl, rfl⟩ := steps_from_val h3
        exact ⟨rfl, by simp⟩
  · rintro ⟨rfl, rfl⟩
    refine .more (Step1.head (.beta μ' (maxCase a b) (Val.bool c))) ?_
    rw [hsub]
    cases c with
    | false =>
        refine .more (Step1.head (.case₁ μ' .unit _ _)) ?_
        exact .more (Step1.head (.seq μ' (Val.i32 a).1)) (.refl _ _)
    | true =>
        refine .more (Step1.head (.case₂ μ' .unit _ _)) ?_
        exact .more (Step1.head (.seq μ' (Val.i32 b).1)) (.refl _ _)

/-- `max (a, b)`'s first three steps: β, `let (a, b)`, and the comparison at the host. -/
theorem max_first (hℍ : ℍ.Conforms) (a b : UInt32) {μ μ' : Heap} {w : Val} :
    Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 a) (.i32 b)).1) μ' w.1 ↔
      Steps (ℍ := ℍ) μ (.app (.lam (maxCase a b))
        (Val.bool (Prim.rel .lt_s a.toBitVec b.toBitVec)).1) μ' w.1 := by
  have e₁ : maxB.subst 0 (Val.pair (.i32 a) (.i32 b)) =
      .letpair (Val.pair (.i32 a) (.i32 b)).1
        (.app (.lam (.case (.var 0) (.seq (.var 0) (.var 3)) (.seq (.var 0) (.var 2))))
          (.app (.prim (.host (.rel .w32 .lt_s))) (.pair (.var 1) (.var 0)))) := rfl
  have e₂ : (((Expr.app (.lam (.case (.var 0) (.seq (.var 0) (.var 3)) (.seq (.var 0) (.var 2))))
          (.app (.prim (.host (.rel .w32 .lt_s))) (.pair (.var 1) (.var 0)))).subst 0
            ((Val.i32 b).shift 1 0)).subst 0 (Val.i32 a)) =
      .app (.lam (maxCase a b)) (.app (.prim (.host (.rel .w32 .lt_s)))
        (Val.pair (.i32 a) (.i32 b)).1) := rfl
  have hhost : ∀ μ₁ e₁, Step1 (ℍ := ℍ) μ (.app (.lam (maxCase a b))
        (.app (.prim (.host (.rel .w32 .lt_s))) (Val.pair (.i32 a) (.i32 b)).1)) μ₁ e₁ →
      μ₁ = μ ∧ e₁ = .app (.lam (maxCase a b))
        (Val.bool (Prim.rel .lt_s a.toBitVec b.toBitVec)).1 := by
    intro μ₁ e₁ h
    obtain ⟨e', rfl, h'⟩ := BoCa.Fig16.LogRel.Core.step1_plug_inv
      (.appR (.lam (maxCase a b)) .hole) (by simp [Kont.Plain]) (by simp [Val.pair, Val.i32])
      (e := .app (.prim (.host (.rel .w32 .lt_s))) (Val.pair (.i32 a) (.i32 b)).1) h
    obtain ⟨r, hr, rfl, rfl⟩ := step1_host_inv h'
    rw [call_lt hℍ] at hr
    cases hr
    exact ⟨rfl, rfl⟩
  have hhostStep : Step1 (ℍ := ℍ) μ (.app (.lam (maxCase a b))
        (.app (.prim (.host (.rel .w32 .lt_s))) (Val.pair (.i32 a) (.i32 b)).1)) μ
      (.app (.lam (maxCase a b)) (Val.bool (Prim.rel .lt_s a.toBitVec b.toBitVec)).1) :=
    ⟨.appR (.lam (maxCase a b)) .hole, _, _, rfl, rfl, .host μ _ _ _ (call_lt hℍ a b)⟩
  constructor
  · intro hs
    have h1 := steps_peel hs (by simp [maxV, Val.lam, Val.pair, Val.i32])
      fun μ₁ e₁ h => step1_beta_inv (b := maxB) h
    rw [e₁] at h1
    have h2 := steps_peel h1 (by simp) (m := μ)
      (e' := .app (.lam (maxCase a b)) (.app (.prim (.host (.rel .w32 .lt_s)))
        (Val.pair (.i32 a) (.i32 b)).1)) fun μ₁ e₁' h => by
          obtain ⟨v₁, v₂, hv, rfl, rfl⟩ := step1_letpair_inv h
          obtain ⟨rfl, rfl⟩ := BoCa.Fig16.LogRel.Core.valPair_inj (congrArg Subtype.val hv).symm
          exact ⟨rfl, e₂⟩
    exact steps_peel h2 (by simp [Val.pair, Val.i32]) hhost
  · intro hs
    refine .more (Step1.head (.beta μ maxB (Val.pair (.i32 a) (.i32 b)))) ?_
    rw [e₁]
    refine .more (Step1.head (.letpair μ (.i32 a) (.i32 b) _)) ?_
    rw [e₂]
    exact .more hhostStep hs

/-- **Every run of `max (a, b)` to a value ends at `smax a b`, at the memory it started from, and
there is such a run**, at every host conforming to the integer operations. -/
theorem max_runs (hℍ : ℍ.Conforms) (a b : UInt32) {μ μ' : Heap} {w : Val} :
    Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 a) (.i32 b)).1) μ' w.1 ↔
      μ' = μ ∧ w = .i32 (smax a b) := by
  rw [max_first hℍ, maxCase_runs]
  rfl

/-! ### The laws -/

/-- **`law max_comm: max(a, b) == max(b, a)`**: the two calls have the same runs. -/
theorem max_comm (hℍ : ℍ.Conforms) (a b : UInt32) {μ μ' : Heap} {w : Val} :
    Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 a) (.i32 b)).1) μ' w.1 ↔
      Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 b) (.i32 a)).1) μ' w.1 := by
  rw [max_runs hℍ, max_runs hℍ]
  have : smax a b = smax b a := by
    apply UInt32.toBitVec_inj.mp
    simp only [smax, Prim.rel]
    have hi : a.toBitVec.toInt = b.toBitVec.toInt → a.toBitVec = b.toBitVec :=
      BitVec.toInt_inj.mp
    by_cases h₁ : a.toBitVec.slt b.toBitVec <;> by_cases h₂ : b.toBitVec.slt a.toBitVec <;>
      simp only [h₁, h₂, if_true, if_false, Bool.false_eq_true] <;>
      simp only [BitVec.slt_iff_toInt_lt, Bool.not_eq_true, decide_eq_false_iff_not] at h₁ h₂ <;>
      first | rfl | omega | exact hi (by omega) | exact (hi (by omega)).symm
  rw [this]

/-- **`law max_ge_left: max(a, b) >= a`**, signed: every run's answer is at least `a`. -/
theorem max_ge_left (hℍ : ℍ.Conforms) (a b : UInt32) {μ μ' : Heap} {w : Val}
    (hs : Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 a) (.i32 b)).1) μ' w.1) :
    ∃ m, w = .i32 m ∧ a.toBitVec.sle m.toBitVec := by
  obtain ⟨-, rfl⟩ := (max_runs hℍ a b).mp hs
  refine ⟨_, rfl, ?_⟩
  simp only [smax, Prim.rel]
  by_cases h₁ : a.toBitVec.slt b.toBitVec <;>
    simp only [h₁, if_true, if_false, Bool.false_eq_true] <;>
    simp [BitVec.sle_iff_toInt_le, BitVec.slt_iff_toInt_lt] at h₁ ⊢ <;> omega

/-! ### A monoid law, as #620's parallel reduce asks for it -/

/-- A run of `K[e]`, `K` plain, where every run of `e` to a value ends at `r` and one does: the
runs of `K[e]` are those of `K[r]`. -/
theorem steps_plug_det (K : Kont) (hK : K.Plain = true) {μ μ' : Heap} {e : Expr} {r w : Val}
    (he : ∀ {μm : Heap} {v : Val}, Steps (ℍ := ℍ) μ e μm v.1 ↔ μm = μ ∧ v = r) :
    Steps (ℍ := ℍ) μ (K.plug e) μ' w.1 ↔ Steps (ℍ := ℍ) μ (K.plug r.1) μ' w.1 := by
  constructor
  · intro hs
    obtain ⟨μm, v, h₁, h₂⟩ :=
      BoCa.Fig16.LogRel.Core.steps_plug_inv K hK hs rfl rfl
    obtain ⟨rfl, rfl⟩ := he.mp h₁
    exact h₂
  · intro hs
    exact ((he.mpr ⟨rfl, rfl⟩).plug K).trans hs

/-- `max (max (a, b), c)`. -/
def maxL (a b c : UInt32) : Expr :=
  .app maxV.1 (.pair (.app maxV.1 (Val.pair (.i32 a) (.i32 b)).1) (Val.i32 c).1)

/-- `max (a, max (b, c))`. -/
def maxR (a b c : UInt32) : Expr :=
  .app maxV.1 (.pair (Val.i32 a).1 (.app maxV.1 (Val.pair (.i32 b) (.i32 c)).1))

/-- **`law max_assoc: max(max(a, b), c) == max(a, max(b, c))`**: the two terms have the same
runs. With `max_unit`, `max` and `i32[0x80000000]` are a monoid, the premise a parallel
reduction needs (#620). -/
theorem max_assoc (hℍ : ℍ.Conforms) (a b c : UInt32) {μ μ' : Heap} {w : Val} :
    Steps (ℍ := ℍ) μ (maxL a b c) μ' w.1 ↔ Steps (ℍ := ℍ) μ (maxR a b c) μ' w.1 := by
  have hL : Steps (ℍ := ℍ) μ (maxL a b c) μ' w.1 ↔
      Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 (smax a b)) (.i32 c)).1) μ' w.1 :=
    steps_plug_det (.appR maxV.1 (.pairL .hole (Val.i32 c).1)) (by simp [Kont.Plain, maxV, Val.lam])
      (fun {_ _} => max_runs hℍ a b)
  have hR : Steps (ℍ := ℍ) μ (maxR a b c) μ' w.1 ↔
      Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 a) (.i32 (smax b c))).1) μ' w.1 :=
    steps_plug_det (.appR maxV.1 (.pairR (.i32 a) .hole)) (by simp [Kont.Plain, maxV, Val.lam])
      (fun {_ _} => max_runs hℍ b c)
  rw [hL, hR, max_runs hℍ, max_runs hℍ]
  have : smax (smax a b) c = smax a (smax b c) := by
    apply UInt32.toBitVec_inj.mp
    simp only [smax, Prim.rel]
    have hi : ∀ x y : UInt32, x.toBitVec.toInt = y.toBitVec.toInt → x.toBitVec = y.toBitVec :=
      fun _ _ => BitVec.toInt_inj.mp
    by_cases h₁ : a.toBitVec.slt b.toBitVec <;> by_cases h₂ : b.toBitVec.slt c.toBitVec <;>
      by_cases h₃ : a.toBitVec.slt c.toBitVec <;>
      simp only [h₁, h₂, h₃, if_true, if_false, Bool.false_eq_true] <;>
      simp only [BitVec.slt_iff_toInt_lt, Bool.not_eq_true, decide_eq_false_iff_not,
        decide_eq_true_eq] at h₁ h₂ h₃ ⊢ <;>
      first | rfl | omega | exact hi _ _ (by omega)
  rw [this]

/-- **`law max_unit: max(i32[0x80000000], a) == a`**: the least signed `i32` is `max`'s unit. -/
theorem max_unit (hℍ : ℍ.Conforms) (a : UInt32) {μ μ' : Heap} {w : Val} :
    Steps (ℍ := ℍ) μ (.app maxV.1 (Val.pair (.i32 0x80000000) (.i32 a)).1) μ' w.1 ↔
      μ' = μ ∧ w = .i32 a := by
  rw [max_runs hℍ]
  have : smax 0x80000000 a = a := by
    apply UInt32.toBitVec_inj.mp
    simp only [smax, Prim.rel]
    by_cases h₁ : (0x80000000 : UInt32).toBitVec.slt a.toBitVec <;>
      simp only [h₁, if_true, if_false, Bool.false_eq_true]
    simp only [BitVec.slt_iff_toInt_lt, Bool.not_eq_true, decide_eq_false_iff_not] at h₁
    apply BitVec.toInt_inj.mp
    have hlo := BitVec.le_toInt a.toBitVec
    have : (0x80000000 : UInt32).toBitVec.toInt = -2147483648 := by decide
    omega
  rw [this]

end DepSpike

#print axioms DepSpike.max_erasure
#print axioms DepSpike.max_comm
#print axioms DepSpike.max_ge_left
#print axioms DepSpike.max_assoc
#print axioms DepSpike.max_unit
