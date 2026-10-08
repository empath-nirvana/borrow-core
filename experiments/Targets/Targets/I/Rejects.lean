import Targets.I.Programs
import Targets.Instance.TiedKernel
import Targets.Base.Closed

/-!
# The interaction — the rejections, at Core's kernel (decision AR)

`Rejects tier1` (`rejects_tier1`; at `J₁` through `Inst.j1_read`, `Targets/I/AcceptsRejects.lean`) is
four inversions of Core's kernel `CDerives`: AT05, AT06, AT08 and AT13 have no derivation, at any
context and any judgement.

**The same-term rules.**  Fourteen of Core's rules conclude with their premise's term: the value
rules `!E`, `[]I`, `[]E`, `⊑` at `Imm` and `Mut`, `μ`'s `roll` and `unroll`; `return`, its reading
back (`ofRet`), `[sub]`, `ν`'s two rules; and, at a λ-value, the two thunk rules.  Every other rule is
told apart by its conclusion's term.  So each inversion below is one induction on the derivation that
carries a *class* of judgements through the same-term rules (`JS`, `JR`):

* a value read at a type `T` is read at the views of `T` and at rows over them (`ValCls`): `!`, `[]`,
  `⊑` and `μ` change the type, `ν` and `[sub]` only the row;
* a computation type that is no row's, no `&` and no `ν` (`Rigid`: `⊸`, `∀`, `⊤`) is left by no
  same-term rule (`JR.rigid`), since `ν`'s rules are at `&`-trees only (`CTy.NuOk`).

**Views keep the head** (`VView.hnf`).  A view of `T` has `T`'s head (`Hnf`: boxes stripped, `μ`
unrolled), unless that head is `!` (dereliction reaches its content), `Imm` or `Mut` (`⊑` changes the
lifetime).  Persistence is a property of the head (`Hnf.persistent`).

**The inversions.**  A variable is read at a view of its live slot's type (`der_var`); a pair at the
views of a tensor of its parts' types (`der_pair`); `()` at `1`'s views over a consumed context, or at
`⊤` (`der_unit`); an application by `⊸E`, `[app]`, `[let]`, the polymorphic let, `∀E` or a
projection (`der_app`); a λ-value through the rule that types its body, or as one of the λ-constants
at its axiom's type (`der_lam`); `let (x, y)`, `;`, `then` and `handle` by their own rules
(`der_letpair`, `der_seq`, `der_then`, `der_hnd`); `alloc` at `A ⊸ Ref A`; a primitive by its own rule
only, and `load` has none (`der_prim`).  Every free variable of a typed term has a live slot
(`fv_live`), so a variable used on both sides of a split is persistent (`splitP_both`).

**The four programs.**
* **AT08** loads a cell (`load`), and Core has no rule for `load` (`not_der_load`): the program's
  clause applies it, so no derivation reaches it.
* **AT06**: the clause is in the handler's clause tuple, so at `clauseTy`, a `!U` type, typed over a
  persistent context; it uses the cell `c`, whose slot is a view of a `Ref`.
* **AT13**: the clause's continuation is at `kTy` at `lin`, a `U` of a `&`, and `forget` takes only a
  persistent argument, `!`, `Imm`, `Mut`, `Unk` or `ArrayImm`.
* **AT05**: the callback reaches `withborU dFlag`'s second argument.  Typed as a λ, `withborU dFlag`
  uses its first argument on both sides of its `then`, so that argument is persistent, while the cell
  is a `Ref`; typed by an unwinding constant, the callback is at `∀'x ⊏ @b. L ⊸ F_Σ(['x] B)` with `L`
  a borrow, and `λm. (m, m)` uses `m` twice.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Rej
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)
open BoCa.Programs (alloc' free')
open BoCa.Fig16.LogRel.Core.EffPrograms (dFlag)

/-! ### Views of a value type -/

/-- One value-level same-term step, at the types alone: `!E`, `[]I`, `[]E`, `⊑` at `Imm` and
`Mut`, `roll`, `unroll`. -/
inductive VS : VTy → VTy → Prop
  | bang (A : VTy) : VS (.bang A) A
  | boxI (a : Lifetime.Life) (A : VTy) : VS A (.box a A)
  | boxE (a : Lifetime.Life) (A : VTy) : VS (.box a A) A
  | immS (a b : Lifetime.Life) (A : VTy) : VS (.imm b A) (.imm a A)
  | mutS (a b : Lifetime.Life) (A : VTy) : VS (.mut b A) (.mut a A)
  | roll (A : VTy) : VS (VTy.inst (.mu A) A) (.mu A)
  | unroll (A : VTy) : VS (.mu A) (VTy.inst (.mu A) A)

/-- The views of a value type. -/
abbrev VView := Relation.ReflTransGen VS

/-- The head of a value type: boxes stripped and `μ` unrolled. -/
inductive Hnf : VTy → VTy → Prop
  | box {a : Lifetime.Life} {A h : VTy} : Hnf A h → Hnf (.box a A) h
  | mu {A h : VTy} : Hnf (VTy.inst (.mu A) A) h → Hnf (.mu A) h
  | base {T : VTy} : (∀ a A, T ≠ .box a A) → (∀ A, T ≠ .mu A) → Hnf T T

theorem Hnf.unique {T h h' : VTy} (hh : Hnf T h) (hh' : Hnf T h') : h = h' := by
  induction hh generalizing h' with
  | box _ ih => cases hh' with
    | box hh' => exact ih hh'
    | base hb _ => exact absurd rfl (hb _ _)
  | mu _ ih => cases hh' with
    | mu hh' => exact ih hh'
    | base _ hm => exact absurd rfl (hm _)
  | base hb hm => cases hh' with
    | box _ => exact absurd rfl (hb _ _)
    | mu _ => exact absurd rfl (hm _)
    | base _ _ => rfl

/-- The head of a type that is neither a box nor a `μ` is the type itself. -/
theorem Hnf.eq_self {T h : VTy} (hh : Hnf T h) (hb : ∀ a A, T ≠ .box a A) (hm : ∀ A, T ≠ .mu A) :
    h = T :=
  hh.unique (.base hb hm)

theorem hnf_self {T : VTy} (hb : ∀ a A, T ≠ .box a A) (hm : ∀ A, T ≠ .mu A) : Hnf T T := .base hb hm

/-- **Views keep the head**, unless the head is `!` (whose content is then viewed), `Imm` or `Mut`. -/
theorem VView.hnf {T T' h : VTy} (hv : VView T T') (hT : Hnf T h) :
    Hnf T' h ∨ (∃ A, h = .bang A ∧ VView A T') ∨ (∃ a A, h = .imm a A) ∨ (∃ a A, h = .mut a A) := by
  induction hv with
  | refl => exact .inl hT
  | tail _ hs ih =>
      rcases ih with h₁ | ⟨A, rfl, hA⟩ | hi | hm
      · cases hs with
        | bang A =>
            obtain rfl := h₁.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h)
            exact .inr (.inl ⟨_, rfl, .refl⟩)
        | boxI a A => exact .inl (.box h₁)
        | boxE a A => cases h₁ with
          | box h₁ => exact .inl h₁
          | base hb _ => exact absurd rfl (hb _ _)
        | immS a b A =>
            obtain rfl := h₁.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h)
            exact .inr (.inr (.inl ⟨b, A, rfl⟩))
        | mutS a b A =>
            obtain rfl := h₁.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h)
            exact .inr (.inr (.inr ⟨b, A, rfl⟩))
        | roll A => exact .inl (.mu h₁)
        | unroll A => cases h₁ with
          | mu h₁ => exact .inl h₁
          | base _ hm => exact absurd rfl (hm _)
      · exact .inr (.inl ⟨A, rfl, hA.tail hs⟩)
      · exact .inr (.inr (.inl hi))
      · exact .inr (.inr (.inr hm))

/-- A view of a type whose head is no `!`, `Imm` or `Mut` has that head. -/
theorem VView.hnf_of {T T' h : VTy} (hv : VView T T') (hT : Hnf T h) (hb : ∀ A, h ≠ .bang A)
    (hi : ∀ a A, h ≠ .imm a A) (hm : ∀ a A, h ≠ .mut a A) : Hnf T' h := by
  rcases hv.hnf hT with h' | ⟨A, rfl, -⟩ | ⟨a, A, rfl⟩ | ⟨a, A, rfl⟩
  · exact h'
  · exact absurd rfl (hb A)
  · exact absurd rfl (hi a A)
  · exact absurd rfl (hm a A)

/-- **Views of a type that is its own head, no `!`, `Imm`, `Mut`, are that type**, when they are
their own heads too. -/
theorem VView.eq_of_heads {T T' : VTy} (hv : VView T T') (hTb : ∀ a A, T ≠ .box a A)
    (hTm : ∀ A, T ≠ .mu A) (hb : ∀ A, T ≠ .bang A) (hi : ∀ a A, T ≠ .imm a A)
    (hmu : ∀ a A, T ≠ .mut a A) (hT'b : ∀ a A, T' ≠ .box a A) (hT'm : ∀ A, T' ≠ .mu A) :
    T' = T :=
  ((hv.hnf_of (hnf_self hTb hTm) hb hi hmu).eq_self hT'b hT'm).symm

/-! ### Persistence is a property of the head -/

theorem persistent_rename (r : Nat → Nat) : ∀ A : VTy, (A.rename r).persistent = A.persistent
  | .unit | .zero | .unk | .int _ | .opq _ | .tvar _ | .thunk _ => rfl
  | .tensor A B | .sum A B => by
      simp only [VTy.rename, VTy.persistent, persistent_rename r A, persistent_rename r B]
  | .ref _ | .imm _ _ | .mut _ _ | .fam _ | .bang _ => rfl
  | .box _ A => by simp only [VTy.rename, VTy.persistent, persistent_rename r A]
  | .mu A => by simp only [VTy.rename, VTy.persistent, persistent_rename _ A]

theorem persistent_subst_false : ∀ (A : VTy) (σ : Nat → VTy), A.persistent = false →
    (A.subst σ).persistent = false
  | .unit, _, h | .zero, _, h | .unk, _, h | .int _, _, h | .tvar _, _, h | .bang _, _, h => by
      simp [VTy.persistent] at h
  | .opq _, _, _ | .thunk _, _, _ | .ref _, _, _ | .imm _ _, _, _ | .mut _ _, _, _ | .fam _, _, _ =>
      rfl
  | .tensor A B, σ, h | .sum A B, σ, h => by
      simp only [VTy.persistent, Bool.and_eq_false_iff] at h
      simp only [VTy.subst, VTy.persistent, Bool.and_eq_false_iff]
      rcases h with h | h
      · exact .inl (persistent_subst_false A σ h)
      · exact .inr (persistent_subst_false B σ h)
  | .box _ A, σ, h => by
      simp only [VTy.persistent] at h
      simp only [VTy.subst, VTy.persistent]; exact persistent_subst_false A σ h
  | .mu A, σ, h => by
      simp only [VTy.persistent] at h
      simp only [VTy.subst, VTy.persistent]; exact persistent_subst_false A _ h

theorem persistent_subst_true : ∀ (A : VTy) (σ : Nat → VTy), A.persistent = true →
    (∀ n, (σ n).persistent = true) → (A.subst σ).persistent = true
  | .unit, _, _, _ | .zero, _, _, _ | .unk, _, _, _ | .int _, _, _, _ | .bang _, _, _, _ => rfl
  | .tvar n, σ, _, hσ => hσ n
  | .opq _, _, h, _ | .thunk _, _, h, _ | .ref _, _, h, _ | .imm _ _, _, h, _ | .mut _ _, _, h, _
  | .fam _, _, h, _ => by simp [VTy.persistent] at h
  | .tensor A B, σ, h, hσ | .sum A B, σ, h, hσ => by
      simp only [VTy.persistent, Bool.and_eq_true] at h
      simp only [VTy.subst, VTy.persistent, Bool.and_eq_true]
      exact ⟨persistent_subst_true A σ h.1 hσ, persistent_subst_true B σ h.2 hσ⟩
  | .box _ A, σ, h, hσ => by
      simp only [VTy.persistent] at h
      simp only [VTy.subst, VTy.persistent]; exact persistent_subst_true A σ h hσ
  | .mu A, σ, h, hσ => by
      simp only [VTy.persistent] at h
      simp only [VTy.subst, VTy.persistent]
      refine persistent_subst_true A _ h ?_
      intro n
      cases n with
      | zero => rfl
      | succ n => simp only [VTy.upS, VTy.scons, persistent_rename]; exact hσ n

/-- Unrolling a `μ` keeps its persistence. -/
theorem persistent_inst_mu (A : VTy) : (VTy.inst (.mu A) A).persistent = A.persistent := by
  cases hA : A.persistent with
  | false => exact persistent_subst_false A _ hA
  | true =>
      refine persistent_subst_true A _ hA ?_
      intro n
      cases n with
      | zero => simpa [VTy.scons, VTy.persistent] using hA
      | succ n => rfl

/-- **A type is persistent exactly when its head is.** -/
theorem Hnf.persistent {T h : VTy} (hh : Hnf T h) : T.persistent = h.persistent := by
  induction hh with
  | box _ ih => simpa [VTy.persistent] using ih
  | mu _ ih => rw [← ih, persistent_inst_mu]; rfl
  | base => rfl

/-! ### The same-term rules, at the judgements -/

/-- One same-term step of Core's rules, at the judgements alone: a value step, `return`, its reading
back (`ofRet`), `[sub]`, and `ν`'s two rules (at an `&`-tree, `CTy.NuOk`). -/
inductive JS : Jdg → Jdg → Prop
  | val {A B : VTy} : VS A B → JS (.val A) (.val B)
  | ret (A : VTy) : JS (.val A) (.comp (.ret A))
  | ofRet (A : VTy) : JS (.comp (.ret A)) (.val A)
  | effSub (S S' : Row) (A : VTy) : JS (.comp (CTy.effOf S A)) (.comp (CTy.effOf S' A))
  | nuIn (C : CTy) : C.NuOk → JS (.comp C.unroll) (.comp (.nu C))
  | nuOut (C : CTy) : C.NuOk → JS (.comp (.nu C)) (.comp C.unroll)

/-- The judgements the same-term rules reach. -/
abbrev JR := Relation.ReflTransGen JS

/-- An `&`-tree unrolls to an `&`. -/
theorem unroll_amp {C : CTy} (hC : C.NuOk) : ∃ C₁ C₂, C.unroll = .amp C₁ C₂ := by
  cases C <;> simp [CTy.NuOk] at hC
  exact ⟨_, _, rfl⟩

theorem effOf_ne_arr (S : Row) (Y A : VTy) (C : CTy) : CTy.effOf S Y ≠ .arr A C := by
  cases S <;> simp [CTy.effOf]

theorem effOf_ne_all (S : Row) (Y : VTy) x b (C : CTy) : CTy.effOf S Y ≠ .all x b C := by
  cases S <;> simp [CTy.effOf]

theorem effOf_ne_top (S : Row) (Y : VTy) : CTy.effOf S Y ≠ .top := by
  cases S <;> simp [CTy.effOf]

/-- The judgements a value of type `T` is read at: its views, and rows over its views. -/
def ValCls (T : VTy) : Jdg → Prop
  | .val Y => VView T Y
  | .comp D => ∃ S Y, D = CTy.effOf S Y ∧ VView T Y

theorem ValCls.refl (T : VTy) : ValCls T (.val T) := Relation.ReflTransGen.refl

theorem ValCls.row (S : Row) (T : VTy) : ValCls T (.comp (CTy.effOf S T)) := ⟨S, T, rfl, .refl⟩

theorem ValCls.step {T : VTy} {j j' : Jdg} (hs : JS j j') (h : ValCls T j) : ValCls T j' := by
  cases hs with
  | val hv => exact Relation.ReflTransGen.tail h hv
  | ret A => exact ⟨[], A, rfl, h⟩
  | ofRet A =>
      obtain ⟨S, Y, he, hY⟩ := h
      obtain ⟨-, rfl⟩ := Inst.effOf_inj (S := []) he
      exact hY
  | effSub S S' A =>
      obtain ⟨S₀, Y, he, hY⟩ := h
      obtain ⟨-, rfl⟩ := Inst.effOf_inj he
      exact ⟨S', _, rfl, hY⟩
  | nuIn C hC =>
      obtain ⟨S, Y, he, -⟩ := h
      obtain ⟨C₁, C₂, hu⟩ := unroll_amp hC
      exact absurd (hu.symm.trans he) (Inst.effOf_ne_amp S Y C₁ C₂).symm
  | nuOut C hC =>
      obtain ⟨S, Y, he, -⟩ := h
      exact absurd he.symm (Inst.effOf_ne_nu S Y C)

theorem ValCls.reach {T : VTy} {j j' : Jdg} (hr : JR j j') (h : ValCls T j) : ValCls T j' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- A computation type no same-term rule leaves: no row's, no `&`, no `ν`. -/
def Rigid (D : CTy) : Prop :=
  (∀ S A, D ≠ CTy.effOf S A) ∧ (∀ C₁ C₂, D ≠ .amp C₁ C₂) ∧ ∀ C, D ≠ .nu C

theorem rigid_arr (A : VTy) (C : CTy) : Rigid (.arr A C) := by
  refine ⟨fun S Y h => effOf_ne_arr S Y A C h.symm, fun _ _ h => ?_, fun _ h => ?_⟩ <;> cases h

theorem rigid_all (x : BoCa.Lifetime.LifeVar) (b : Lifetime.Life) (C : CTy) :
    Rigid (.all x b C) := by
  refine ⟨fun S Y h => effOf_ne_all S Y x b C h.symm, fun _ _ h => ?_, fun _ h => ?_⟩ <;> cases h

theorem rigid_top : Rigid .top := by
  refine ⟨fun S Y h => effOf_ne_top S Y h.symm, fun _ _ h => ?_, fun _ h => ?_⟩ <;> cases h

/-- No same-term rule leaves a rigid type. -/
theorem JS.not_rigid {D : CTy} {j : Jdg} (hs : JS (.comp D) j) (hD : Rigid D) : False := by
  obtain ⟨he, ha, hn⟩ := hD
  cases hs with
  | ofRet A => exact he [] A rfl
  | effSub S S' A => exact he S A rfl
  | nuIn C hC =>
      obtain ⟨C₁, C₂, hu⟩ := unroll_amp hC
      exact ha C₁ C₂ hu
  | nuOut C _ => exact hn C rfl

/-- **A rigid computation type is read at itself alone.** -/
theorem JR.rigid {D : CTy} {j : Jdg} (hr : JR (.comp D) j) (hD : Rigid D) : j = .comp D := by
  induction hr with
  | refl => rfl
  | tail _ hs ih => subst ih; exact (hs.not_rigid hD).elim

/-- A judgement reached from a computation type at a value: the computation type is a row's. -/
theorem JR.comp_val {D : CTy} {Y : VTy} (hr : JR (.comp D) (.val Y)) :
    ∃ S A, D = CTy.effOf S A := by
  -- the judgements reached from `.comp D`, while no row's type is met, are computation types
  -- that are no row's
  suffices h : ∀ j, JR (.comp D) j → (∃ S A, D = CTy.effOf S A) ∨
      ∃ D', j = .comp D' ∧ ∀ S A, D' ≠ CTy.effOf S A by
    rcases h _ hr with h | ⟨D', h, -⟩
    · exact h
    · cases h
  intro j hj
  by_cases hD : ∃ S A, D = CTy.effOf S A
  · exact .inl hD
  · simp only [not_exists] at hD
    refine .inr ?_
    induction hj with
    | refl => exact ⟨D, rfl, hD⟩
    | tail _ hs ih =>
        obtain ⟨D', rfl, hD'⟩ := ih
        cases hs with
        | ofRet A => exact absurd rfl (hD' [] A)
        | effSub S S' A => exact absurd rfl (hD' S A)
        | nuIn C hC =>
            refine ⟨_, rfl, fun S A h => Inst.effOf_ne_nu S A C h.symm⟩
        | nuOut C hC =>
            obtain ⟨C₁, C₂, hu⟩ := unroll_amp hC
            refine ⟨_, rfl, fun S A h => ?_⟩
            rw [hu] at h
            exact Inst.effOf_ne_amp S A C₁ C₂ h.symm

/-- An `&` or a `ν` is read at `&`s and `ν`s alone. -/
def AmpNu (D : CTy) : Prop := (∃ C₁ C₂, D = .amp C₁ C₂) ∨ ∃ C, D = .nu C

theorem JR.ampNu {D : CTy} {j : Jdg} (hr : JR (.comp D) j) (hD : AmpNu D) :
    ∃ D', j = .comp D' ∧ AmpNu D' := by
  induction hr with
  | refl => exact ⟨D, rfl, hD⟩
  | tail _ hs ih =>
      obtain ⟨D', rfl, hD'⟩ := ih
      cases hs with
      | ofRet A => rcases hD' with ⟨_, _, h⟩ | ⟨_, h⟩ <;> cases h
      | effSub S S' A =>
          rcases hD' with ⟨_, _, h⟩ | ⟨_, h⟩
          · exact absurd h (Inst.effOf_ne_amp _ _ _ _)
          · exact absurd h (Inst.effOf_ne_nu _ _ _)
      | nuIn C hC => exact ⟨_, rfl, .inr ⟨C, rfl⟩⟩
      | nuOut C hC => exact ⟨_, rfl, .inl (unroll_amp hC)⟩

/-! ### Contexts -/

/-- `Γ'`'s live slots are `Γ`'s, at the same types. -/
abbrev CtxLe (Γ' Γ : Ctx VTy) : Prop :=
  ∀ (k : Nat) (T : VTy), Γ'[k]? = some (⟨T, true⟩ : Slot VTy) → Γ[k]? = some ⟨T, true⟩

theorem CtxLe.refl (Γ : Ctx VTy) : CtxLe Γ Γ := fun _ _ h => h

theorem CtxLe.trans {Γ₁ Γ₂ Γ₃ : Ctx VTy} (h₁ : CtxLe Γ₁ Γ₂) (h₂ : CtxLe Γ₂ Γ₃) : CtxLe Γ₁ Γ₃ :=
  fun k T h => h₂ k T (h₁ k T h)

/-- A slot in front, live in the smaller context only where it is live in the larger. -/
theorem CtxLe.cons {Γ' Γ : Ctx VTy} (h : CtxLe Γ' Γ) {s s' : Slot VTy}
    (hs : s'.live = true → s' = s) : CtxLe (s' :: Γ') (s :: Γ) := by
  intro k T hk
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk ⊢
      subst hk
      exact (hs rfl).symm
  | succ k => simpa using h k T (by simpa using hk)

theorem CtxLe.cons_same {Γ' Γ : Ctx VTy} (h : CtxLe Γ' Γ) (s : Slot VTy) : CtxLe (s :: Γ') (s :: Γ) :=
  h.cons (fun _ => rfl)

theorem CtxLe.cons_dead {Γ' Γ : Ctx VTy} (h : CtxLe Γ' Γ) (T : VTy) (s : Slot VTy) :
    CtxLe (⟨T, false⟩ :: Γ') (s :: Γ) :=
  h.cons (fun h => by cases h)

theorem splitP_le_left {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) : CtxLe Γ₁ Γ := by
  induction h with
  | nil => exact CtxLe.refl _
  | left _ ih | dup _ _ ih => exact ih.cons_same _
  | right _ ih | dead _ ih => exact ih.cons_dead _ _

theorem splitP_le_right {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) : CtxLe Γ₂ Γ := by
  induction h with
  | nil => exact CtxLe.refl _
  | right _ ih | dup _ _ ih => exact ih.cons_same _
  | left _ ih | dead _ ih => exact ih.cons_dead _ _

/-- **A slot live on both sides of a split is persistent.** -/
theorem splitP_both {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    ∀ {k : Nat} {T T' : VTy}, Γ₁[k]? = some ⟨T, true⟩ → Γ₂[k]? = some ⟨T', true⟩ → T.Persistent := by
  induction h with
  | nil => intro k T T' h₁ _; simp at h₁
  | left _ ih =>
      intro k T T' h₁ h₂
      cases k with
      | zero => simp at h₂
      | succ k => exact ih (by simpa using h₁) (by simpa using h₂)
  | right _ ih =>
      intro k T T' h₁ h₂
      cases k with
      | zero => simp at h₁
      | succ k => exact ih (by simpa using h₁) (by simpa using h₂)
  | dead _ ih =>
      intro k T T' h₁ h₂
      cases k with
      | zero => simp at h₁
      | succ k => exact ih (by simpa using h₁) (by simpa using h₂)
  | dup hT _ ih =>
      intro k T T' h₁ h₂
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at h₁
          obtain ⟨rfl, -⟩ := h₁
          exact hT
      | succ k => exact ih (by simpa using h₁) (by simpa using h₂)

/-- A persistent context's live slots are `!`s. -/
theorem persistent_slot {Γ : Ctx VTy} (hp : Persistent Γ) {k : Nat} {T : VTy}
    (h : Γ[k]? = some ⟨T, true⟩) : ∃ A, T = .bang A := by
  obtain ⟨A, hA⟩ := hp _ (List.mem_of_getElem? h) rfl
  exact ⟨A, hA⟩

/-- A consumed context's live slots are persistent. -/
theorem deadP_slot {Γ : Ctx VTy} (hd : Ctx.DeadP Γ) :
    ∀ {k : Nat} {T : VTy}, Γ[k]? = some ⟨T, true⟩ → T.Persistent := by
  induction hd with
  | nil => intro k T h; simp at h
  | cons _ ih =>
      intro k T h
      cases k with
      | zero => simp at h
      | succ k => exact ih (by simpa using h)
  | drop hT _ ih =>
      intro k T h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact hT
      | succ k => exact ih (by simpa using h)

theorem soloP_le {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    Γ[i]? = some ⟨A, true⟩ := Inst.soloP_slot h

/-! ### Every free variable of a typed term has a live slot -/

/-- The variable `k` occurs free in the term. -/
def _root_.BoCa.Expr.HasVar : Nat → Expr → Prop
  | k, .var i => i = k
  | k, .pair a b | k, .seq a b | k, .app a b => a.HasVar k ∨ b.HasVar k
  | k, .inj₁ a | k, .inj₂ a => a.HasVar k
  | k, .lam b => b.HasVar (k + 1)
  | k, .letpair a b => a.HasVar k ∨ b.HasVar (k + 2)
  | k, .case a b c => a.HasVar k ∨ b.HasVar (k + 1) ∨ c.HasVar (k + 1)
  | _, .unit | _, .loc _ | _, .prim _ => False

/-- A term closed below `n` has its free variables below `n`. -/
theorem hasVar_lt : ∀ {e : Expr} {n k : Nat}, closedAt n e = true → e.HasVar k → k < n
  | .var i, n, k, h, hk => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.HasVar] at hk
      omega
  | .pair a b, n, k, h, hk | .seq a b, n, k, h, hk | .app a b, n, k, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      rcases hk with hk | hk
      · exact hasVar_lt h.1 hk
      · exact hasVar_lt h.2 hk
  | .inj₁ a, n, k, h, hk | .inj₂ a, n, k, h, hk => hasVar_lt (e := a) h hk
  | .lam b, n, k, h, hk => by
      have := hasVar_lt (e := b) (n := n + 1) h hk
      omega
  | .letpair a b, n, k, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      rcases hk with hk | hk
      · exact hasVar_lt h.1 hk
      · have := hasVar_lt h.2 hk; omega
  | .case a b c, n, k, h, hk => by
      simp only [closedAt, Bool.and_eq_true] at h
      rcases hk with hk | hk | hk
      · exact hasVar_lt h.1.1 hk
      · have := hasVar_lt h.1.2 hk; omega
      · have := hasVar_lt h.2 hk; omega
  | .unit, _, _, _, hk | .loc _, _, _, _, hk | .prim _, _, _, _, hk => hk.elim

/-- A closed term has no free variable. -/
theorem not_hasVar_closed {e : Expr} (h : closedAt 0 e = true) {k : Nat} : ¬ e.HasVar k :=
  fun hk => Nat.not_lt_zero _ (hasVar_lt h hk)

/-- **Filling a variable with a closed value keeps every other variable.** -/
theorem hasVar_fill {V : Val} (hV : closedAt 0 V.1 = true) :
    ∀ (N : Expr) (j m : Nat), m ≠ j → N.HasVar m → ((N.subst j V).shift 1 j).HasVar m
  | .var i, j, m, hmj, hk => by
      simp only [Expr.HasVar] at hk
      subst hk
      by_cases h3 : i > j
      · have h2 : ¬ (i = j) := by omega
        have h4 : ¬ (i - 1 < j) := by omega
        simp only [Expr.subst, if_neg h2, if_pos h3, Expr.shift, if_neg h4, Expr.HasVar]
        omega
      · have h2 : ¬ (i = j) := hmj
        have h4 : i < j := by omega
        simp only [Expr.subst, if_neg h2, if_neg h3, Expr.shift, if_pos h4, Expr.HasVar]
  | .pair a b, j, m, hmj, hk | .seq a b, j, m, hmj, hk | .app a b, j, m, hmj, hk => by
      simp only [Expr.subst, Expr.shift, Expr.HasVar] at hk ⊢
      rcases hk with hk | hk
      · exact .inl (hasVar_fill hV a j m hmj hk)
      · exact .inr (hasVar_fill hV b j m hmj hk)
  | .inj₁ a, j, m, hmj, hk | .inj₂ a, j, m, hmj, hk => by
      simp only [Expr.subst, Expr.shift, Expr.HasVar] at hk ⊢
      exact hasVar_fill hV a j m hmj hk
  | .lam b, j, m, hmj, hk => by
      simp only [Expr.subst, Expr.shift, Expr.HasVar, val_shift_closed hV] at hk ⊢
      exact hasVar_fill hV b (j + 1) (m + 1) (by omega) hk
  | .letpair a b, j, m, hmj, hk => by
      simp only [Expr.subst, Expr.shift, Expr.HasVar, val_shift_closed hV] at hk ⊢
      rcases hk with hk | hk
      · exact .inl (hasVar_fill hV a j m hmj hk)
      · exact .inr (hasVar_fill hV b (j + 2) (m + 2) (by omega) hk)
  | .case a b c, j, m, hmj, hk => by
      simp only [Expr.subst, Expr.shift, Expr.HasVar, val_shift_closed hV] at hk ⊢
      rcases hk with hk | hk | hk
      · exact .inl (hasVar_fill hV a j m hmj hk)
      · exact .inr (.inl (hasVar_fill hV b (j + 1) (m + 1) (by omega) hk))
      · exact .inr (.inr (hasVar_fill hV c (j + 1) (m + 1) (by omega) hk))
  | .unit, _, _, _, hk | .loc _, _, _, _, hk | .prim _, _, _, _, hk => hk.elim

theorem slot_succ {Γ : Ctx VTy} {s : Slot VTy} {k : Nat} {T : VTy}
    (h : (s :: Γ)[k + 1]? = some ⟨T, true⟩) : Γ[k]? = some ⟨T, true⟩ := by simpa using h

theorem slot_succ₂ {Γ : Ctx VTy} {s s' : Slot VTy} {k : Nat} {T : VTy}
    (h : (s :: s' :: Γ)[k + 2]? = some ⟨T, true⟩) : Γ[k]? = some ⟨T, true⟩ := by simpa using h

theorem qualsVal_noVar (qs : List Qual) {k : Nat} : ¬ (qualsVal qs).1.HasVar k :=
  not_hasVar_closed (closedAt_qualsVal 0 qs)

/-- **Every free variable of a typed term has a live slot.** -/
theorem fv_live {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ k, e.HasVar k → ∃ T, Γ[k]? = some ⟨T, true⟩ := by
  induction h with
  | var hs =>
      intro k hk; simp only [Expr.HasVar] at hk; subst hk; exact ⟨_, soloP_le hs⟩
  | force hs =>
      rename_i i C
      intro k hk
      rcases Inst.forceE_cases C (.var i) with hf | hf <;> rw [hf] at hk <;>
        simp only [Expr.HasVar, Expr.val, Val.unit, or_false] at hk <;> subst hk <;>
        exact ⟨_, soloP_le hs⟩
  | tensorI hs _ _ ih₁ ih₂ | unitE hs _ _ ih₁ ih₂ =>
      intro k hk
      rcases hk with hk | hk
      · obtain ⟨T, hT⟩ := ih₁ k hk; exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ih₂ k hk; exact ⟨T, splitP_le_right hs k T hT⟩
  | lolliE hs _ _ iha ihf =>
      intro k hk
      rcases hk with hk | hk
      · obtain ⟨T, hT⟩ := ihf k hk; exact ⟨T, splitP_le_right hs k T hT⟩
      · obtain ⟨T, hT⟩ := iha k hk; exact ⟨T, splitP_le_left hs k T hT⟩
  | sumI₁ _ ih | sumI₂ _ ih => exact ih
  | thunkF _ ih | lam _ ih | lamDead _ ih | allI _ _ _ _ ih | bangThunkF _ _ ih =>
      intro k hk; obtain ⟨T, hT⟩ := ih (k + 1) hk; exact ⟨T, slot_succ hT⟩
  | thunkV _ _ ih | ret _ ih | bangThunkV _ _ _ ih | bangE _ ih | boxI _ _ ih | boxE _ ih
  | immSub _ _ ih | mutSub _ _ ih | ofRet _ ih | roll _ _ _ ih | unroll _ ih | nuIn _ _ ih
  | nuOut _ _ ih | effSub _ _ ih => exact ih
  | proj₁ _ ih | proj₂ _ ih | allE _ _ ih | allEV _ _ ih =>
      intro k hk
      rcases hk with hk | hk
      · exact ih k hk
      · simp [Expr.HasVar, Expr.val, Val.inj₁, Val.inj₂, Val.unit] at hk
  | bind hs _ _ ihM ihN | effLet hs _ _ _ _ ihM ihN =>
      intro k hk
      rcases hk with hk | hk
      · obtain ⟨T, hT⟩ := ihN (k + 1) hk; exact ⟨T, splitP_le_right hs k T (slot_succ hT)⟩
      · obtain ⟨T, hT⟩ := ihM k hk; exact ⟨T, splitP_le_left hs k T hT⟩
  | app hs _ hx ihM =>
      intro k hk
      rcases hk with hk | hk
      · obtain ⟨T, hT⟩ := ihM k hk; exact ⟨T, splitP_le_left hs k T hT⟩
      · simp only [Expr.HasVar] at hk; subst hk
        exact ⟨_, splitP_le_right hs _ _ (soloP_le hx)⟩
  | withI _ _ ihM ihN =>
      intro k hk
      simp only [withPair, Expr.val, Val.lam, Expr.HasVar] at hk
      rcases hk with hk | (hk | hk) | (hk | hk)
      · omega
      · omega
      · obtain ⟨T, hT⟩ := ihM (k + 2) hk; exact ⟨T, slot_succ₂ hT⟩
      · omega
      · obtain ⟨T, hT⟩ := ihN (k + 2) hk; exact ⟨T, slot_succ₂ hT⟩
  | tensorE hs _ _ ihV ihM =>
      intro k hk
      rcases hk with hk | hk
      · obtain ⟨T, hT⟩ := ihV k hk; exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ihM (k + 2) hk; exact ⟨T, splitP_le_right hs k T (slot_succ₂ hT)⟩
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      intro k hk
      rcases hk with hk | hk | hk
      · obtain ⟨T, hT⟩ := ihV k hk; exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ih₁ (k + 1) hk; exact ⟨T, splitP_le_right hs k T (slot_succ hT)⟩
      · obtain ⟨T, hT⟩ := ih₂ (k + 1) hk; exact ⟨T, splitP_le_right hs k T (slot_succ hT)⟩
  | zeroE hs _ ihV =>
      intro k hk
      simp only [absurdE, Expr.HasVar] at hk
      rcases hk with hk | hk | hk
      · obtain ⟨T, hT⟩ := ihV k hk; exact ⟨T, splitP_le_left hs k T hT⟩
      · omega
      · omega
  | effPerform _ _ _ ih | effRaise _ _ _ _ ih =>
      intro k hk
      simp only [BoCa.BoLo.performE, BoCa.BoLo.raiseE, opArgE, Expr.val, Val.prim, Val.i32,
        Expr.HasVar, false_or] at hk
      exact ih k hk
  | effThen hs _ _ _ _ _ _ ihM ihN ihD =>
      intro k hk
      simp only [thenE, Expr.val, Val.prim, Val.lam, Expr.HasVar, false_or] at hk
      rcases hk with (hk | hk) | hk
      · obtain ⟨T, hT⟩ := ihN (k + 1) hk; exact ⟨T, splitP_le_right hs k T (slot_succ hT)⟩
      · obtain ⟨T, hT⟩ := ihD (k + 1) hk; exact ⟨T, splitP_le_right hs k T (slot_succ hT)⟩
      · obtain ⟨T, hT⟩ := ihM k hk; exact ⟨T, splitP_le_left hs k T hT⟩
  | effHandleV hs _ _ _ _ _ _ _ ihc ihe =>
      intro k hk
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.HasVar, false_or] at hk
      rcases hk with (hk | hk) | hk
      · exact absurd hk (qualsVal_noVar _)
      · obtain ⟨T, hT⟩ := ihc k hk; exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ihe k hk; exact ⟨T, splitP_le_right hs k T hT⟩
  | letPoly b hcl _ _ _ ihN =>
      intro k hk
      rcases hk with hk | hk
      · obtain ⟨T, hT⟩ := ihN (k + 1) (hasVar_fill hcl _ 0 (k + 1) (by omega) hk)
        exact ⟨T, slot_succ hT⟩
      · exact absurd hk (not_hasVar_closed hcl)
  | withbor1U _ _ _ _ _ _ _ hdc _ _ | withbor2U _ _ _ _ _ _ _ hdc _ _
  | withbor3U _ _ _ _ _ _ hdc _ _ | sliceBorrowMU _ _ _ _ _ _ _ hdc _ _
  | sliceBorrowIU _ _ _ _ _ _ _ _ hdc _ _ =>
      intro k hk; exact absurd hk (not_hasVar_closed (withborUE_closed hdc))
  | foldImm => intro k hk; exact absurd hk (not_hasVar_closed (foldImmV_closed _))
  | foldOwn => intro k hk; exact absurd hk (not_hasVar_closed (foldOwnV_closed _))
  | foldReuse => intro k hk; exact absurd hk (not_hasVar_closed (foldReuseV_closed _))
  | unfoldN => intro k hk; exact absurd hk (not_hasVar_closed (unfoldV_closed _))
  | _ => intro k hk; exact absurd hk (not_hasVar_closed (by rfl))

/-! ### Inversions -/

/-- The term constants of `CDerives`'s conclusions, unfolded to their head constructors, so that a
rule whose conclusion's term has another head is told apart. -/
macro "cd_terms" : tactic => `(tactic| (try simp_all [withPair, absurdE, copy, forget, swap,
    withbor, withload, withswap, sizeV, replaceV, arrLenV, copyV, forgetV, emptyFamV, swapV,
    Val.arr, withborUE, foldImmV, foldOwnV, foldReuseV, unfoldV, BoCa.BoLo.performE,
    BoCa.BoLo.raiseE, opArgE, thenE, hndTerm, hndExpr, Expr.val, Val.lam, Val.prim, Val.unit,
    Val.i32, lam2, elet, unit', v0, v1, v2, v3, load', store']))


/-- `force x` is `x` or `x ()`. -/
theorem forceE_var {C : CTy} {i : Nat} {e : Expr} (h : forceE C (.var i) = e) :
    e = .var i ∨ e = .app (.var i) .unit := by
  rcases Inst.forceE_cases C (.var i) with hf | hf <;> rw [hf] at h <;> subst h
  · exact .inl rfl
  · exact .inr rfl

/-- The same, at one hypothesis alone. -/
macro "cd_at " h:ident : tactic => `(tactic| (simp [withPair, absurdE, copy, forget, swap,
    withbor, withload, withswap, sizeV, replaceV, arrLenV, copyV, forgetV, emptyFamV, swapV,
    Val.arr, withborUE, foldImmV, foldOwnV, foldReuseV, unfoldV, BoCa.BoLo.performE,
    BoCa.BoLo.raiseE, opArgE, thenE, hndTerm, hndExpr, Expr.val, Val.lam, Val.prim, Val.unit,
    Val.i32, lam2, elet, unit', v0, v1, v2, v3, load', store'] at $h:ident))

/-- The primitives that have a rule of their own. -/
def PrimRule : Prim → Prop
  | .alloc | .free | .host _ | .lit _ | .tab | .drop | .idx | .count | .countTry | .boundedFix
  | .split => True
  | _ => False

/-- **A primitive is typed only by its own rule.** -/
theorem der_prim {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ p, e = .prim p → PrimRule p := by
  induction h <;> intro p he <;> cd_terms <;> (try subst he) <;> (try trivial)
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with hf | hf <;> rw [hf] at he <;> simp at he

/-- `load` has no rule. -/
theorem not_der_load {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ (.prim .load) j :=
  fun h => der_prim h .load rfl

/-- **A primitive with no rule of its own, applied, has no derivation**, but `perform` and `raise`
(`[perform]`, `[raise]`). -/
theorem not_der_app_prim {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ p X, e = .app (.prim p) X → ¬ PrimRule p → p ≠ .perform → p ≠ .raise → False := by
  induction h <;> intro p X he hp hpe hpr <;> cd_terms
  case force _ _ i C _ =>
    rcases Inst.forceE_cases C (.var i) with hf | hf <;> rw [hf] at he <;> simp at he
  all_goals exact hp (der_prim ‹CDerives _ _ (.prim p) _› p rfl)

/-! #### Variables, pairs, `()`, `alloc` -/

/-- The judgements a variable whose slot has type `T` is read at: the views of `T` and rows over
them; and, when `T` is `U C` with `C` no returner, `C` and what the same-term rules reach from it
(`force` at a type that is no `F`). -/
def VarCls (T : VTy) (j : Jdg) : Prop :=
  ValCls T j ∨ ∃ C, T = .thunk C ∧ C.isRet = false ∧ JR (.comp C) j

theorem VarCls.step {T : VTy} {j j' : Jdg} (hs : JS j j') (h : VarCls T j) : VarCls T j' := by
  rcases h with h | ⟨C, hT, hC, hr⟩
  · exact .inl (h.step hs)
  · exact .inr ⟨C, hT, hC, hr.tail hs⟩

/-- **A variable is read at a view of its live slot's type.** -/
theorem der_var {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ i, e = .var i → ∃ T, Γ[i]? = some ⟨T, true⟩ ∧ VarCls T j := by
  induction h with
  | var hs => intro i he; cases he; exact ⟨_, soloP_le hs, .inl (ValCls.refl _)⟩
  | force hs =>
      rename_i i' C
      intro i he
      cases C <;> simp only [forceE] at he <;> (try cases he) <;>
        exact ⟨_, soloP_le hs, .inr ⟨_, rfl, rfl, .refl⟩⟩
  | ret _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.ret _)⟩
  | ofRet _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.ofRet _)⟩
  | effSub _ _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.effSub _ _ _)⟩
  | nuIn hC _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.val (VS.unroll _))⟩
  | _ => intro i he; cd_terms

/-- **A pair is read at the views of a tensor of its parts' types**, or it is the empty family. -/
theorem der_pair {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ a b, e = .pair a b →
      (∃ Γ₁ Γ₂ A B, Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ a (.val A) ∧ CDerives Δ Γ₂ b (.val B) ∧
        ValCls (.tensor A B) j) ∨ Expr.pair a b = emptyFamV.1 := by
  induction h with
  | tensorI hs h₁ h₂ => intro a b he; cases he; exact .inl ⟨_, _, _, _, hs, h₁, h₂, ValCls.refl _⟩
  | sliceEmptyI => intro a b he; exact .inr he.symm
  | sliceEmptyM => intro a b he; exact .inr he.symm
  | ret _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.ret _)⟩
      · exact .inr h
  | ofRet _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.ofRet _)⟩
      · exact .inr h
  | effSub _ _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.effSub _ _ _)⟩
      · exact .inr h
  | nuIn hC _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.nuIn _ hC)⟩
      · exact .inr h
  | nuOut hC _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.nuOut _ hC)⟩
      · exact .inr h
  | bangE _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.val (VS.bang _))⟩
      · exact .inr h
  | boxI _ _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.val (VS.boxI _ _))⟩
      · exact .inr h
  | boxE _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.val (VS.boxE _ _))⟩
      · exact .inr h
  | immSub _ _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.val (VS.immS _ _ _))⟩
      · exact .inr h
  | mutSub _ _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.val (VS.mutS _ _ _))⟩
      · exact .inr h
  | roll _ _ _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.val (VS.roll _))⟩
      · exact .inr h
  | unroll _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.val (VS.unroll _))⟩
      · exact .inr h
  | force => intro a b he; rcases forceE_var he with h | h <;> cases h
  | _ => intro a b he; cd_terms

/-- **`()` is read at `1`'s views over a consumed context, or at `⊤`.** -/
theorem der_unit {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    e = .unit → (Ctx.DeadP Γ ∧ ValCls .unit j) ∨ JR (.comp .top) j := by
  induction h with
  | unitI hd => intro _; exact .inl ⟨hd, ValCls.refl _⟩
  | topI => intro _; exact .inr .refl
  | ret _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.ret _)⟩
      · exact .inr (hr.tail (JS.ret _))
  | ofRet _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.ofRet _)⟩
      · exact .inr (hr.tail (JS.ofRet _))
  | effSub _ _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.effSub _ _ _)⟩
      · exact .inr (hr.tail (JS.effSub _ _ _))
  | nuIn hC _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.nuIn _ hC)⟩
      · exact .inr (hr.tail (JS.nuIn _ hC))
  | nuOut hC _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.nuOut _ hC)⟩
      · exact .inr (hr.tail (JS.nuOut _ hC))
  | bangE _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.val (VS.bang _))⟩
      · exact .inr (hr.tail (JS.val (VS.bang _)))
  | boxI _ _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.val (VS.boxI _ _))⟩
      · exact .inr (hr.tail (JS.val (VS.boxI _ _)))
  | boxE _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.val (VS.boxE _ _))⟩
      · exact .inr (hr.tail (JS.val (VS.boxE _ _)))
  | immSub _ _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.val (VS.immS _ _ _))⟩
      · exact .inr (hr.tail (JS.val (VS.immS _ _ _)))
  | mutSub _ _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.val (VS.mutS _ _ _))⟩
      · exact .inr (hr.tail (JS.val (VS.mutS _ _ _)))
  | roll _ _ _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.val (VS.roll _))⟩
      · exact .inr (hr.tail (JS.val (VS.roll _)))
  | unroll _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.val (VS.unroll _))⟩
      · exact .inr (hr.tail (JS.val (VS.unroll _)))
  | force => intro he; rcases forceE_var he with h | h <;> cases h
  | _ => intro he; cd_terms

/-- **`alloc` is read at the views of `A ⊸ Ref A`.** -/
theorem der_prim_alloc {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    e = .prim .alloc → ∃ A, ValCls (.lolli A (.ref A)) j := by
  induction h with
  | alloc => intro _; exact ⟨_, ValCls.refl _⟩
  | ret _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.ret _)⟩
  | ofRet _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.ofRet _)⟩
  | effSub _ _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.effSub _ _ _)⟩
  | nuIn hC _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.nuIn _ hC)⟩
  | nuOut hC _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.nuOut _ hC)⟩
  | bangE _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.val (VS.bang _))⟩
  | boxI _ _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.val (VS.boxI _ _))⟩
  | boxE _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.val (VS.roll _))⟩
  | unroll _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.val (VS.unroll _))⟩
  | force => intro he; rcases forceE_var he with h | h <;> cases h
  | _ => intro he; cd_terms

/-! #### Applications -/

/-- The rules that conclude with an application `X Y`, at the judgement each gives. -/
def AppBase (Δ : LifeCtx) (Γ : Ctx VTy) (X Y : Expr) (j₀ : Jdg) : Prop :=
  -- `⊸E`
  (∃ Γ₁ Γ₂ A B, Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ Y (.val A) ∧
    CDerives Δ Γ₂ X (.val (.lolli A B)) ∧ j₀ = .val B) ∨
  -- `[app]`: the argument a variable
  (∃ Γ₁ Γ₂ i A C, Y = .var i ∧ Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ X (.comp (.arr A C)) ∧
    Ctx.SoloP Γ₂ i A ∧ j₀ = .comp C) ∨
  -- `[let]`, at the empty row or at a row
  (∃ N Γ₁ Γ₂ A S C, X = .lam N ∧ Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ Y (.comp (CTy.effOf S A)) ∧
    CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp C) ∧ j₀ = .comp C) ∨
  -- `[let-poly]`
  (∃ N b C, X = .lam N ∧ Y = .lam b ∧ closedAt 0 (Expr.lam b) = true ∧
    (∃ j', CDerives Δ [] (.lam b) j') ∧
    CDerives Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 (Val.lam b)).shift 1 0) (.comp C) ∧
    j₀ = .comp C) ∨
  -- `∀E`, at a computation and at a value
  (∃ x b C a, Y = .unit ∧ CDerives Δ Γ X (.comp (.all x b C)) ∧ j₀ = .comp (C.instLife x a)) ∨
  (∃ x b A a, Y = .unit ∧ CDerives Δ Γ X (.val (VTy.all x b A)) ∧ j₀ = .val (A.instLife x a)) ∨
  -- the projections
  (∃ C D, Y = .inj₁ .unit ∧ CDerives Δ Γ X (.comp (.amp C D)) ∧ j₀ = .comp C) ∨
  (∃ C D, Y = .inj₂ .unit ∧ CDerives Δ Γ X (.comp (.amp C D)) ∧ j₀ = .comp D) ∨
  -- `force` at a returner, and the effect forms
  (Y = .unit ∧ ∃ i, X = .var i) ∨
  X = .prim .perform ∨ X = .prim .raise ∨ (∃ Z, X = .app (.prim .ubind) Z) ∨
    (∃ Z, X = .app (.prim .hnd) Z)

/-- **An application is typed by a rule that concludes with one, then the same-term rules.** -/
theorem der_app {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ X Y, e = .app X Y → ∃ j₀, AppBase Δ Γ X Y j₀ ∧ JR j₀ j := by
  induction h with
  | lolliE hs ha hf =>
      intro X Y he; cases he
      exact ⟨_, .inl ⟨_, _, _, _, hs, ha, hf, rfl⟩, .refl⟩
  | app hs hM hx =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inl ⟨_, _, _, _, _, rfl, hs, hM, hx, rfl⟩), .refl⟩
  | bind hs hM hN =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inl ⟨_, _, _, _, [], _, rfl, hs, hM, hN, rfl⟩)), .refl⟩
  | effLet hs _ _ hM hN =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, hs, hM, hN, rfl⟩)), .refl⟩
  | letPoly b hcl hV hN =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl, hcl, ⟨_, hV⟩, hN, rfl⟩))), .refl⟩
  | allE hM _ =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, hM, rfl⟩)))), .refl⟩
  | allEV hM _ =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, rfl, hM, rfl⟩))))), .refl⟩
  | proj₁ hM =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, hM, rfl⟩)))))), .refl⟩
  | proj₂ hM =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, rfl, hM, rfl⟩))))))), .refl⟩
  | force =>
      intro X Y he
      rcases forceE_var he with h | h
      · cases h
      · cases h; exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inl ⟨rfl, _, rfl⟩)))))))), .refl⟩
  | effPerform =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))), .refl⟩
  | effRaise =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))))),
        .refl⟩
  | effThen =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inl ⟨_, rfl⟩))))))))))), .refl⟩
  | effHandleV =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr ⟨_, rfl⟩))))))))))), .refl⟩
  | ret _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub _ _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _)⟩
  | nuIn hC _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro X Y he; cd_terms

/-! #### `let (x, y)`, `;`, `then`, `handle` -/

/-- **A `let (x, y) = V in M` is `[⊗E]`'s**: `V` at a tensor, `M` under its two parts. -/
theorem der_letpair {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ V M, e = .letpair V M → ∃ Γ₁ Γ₂ A B j', Ctx.SplitP Γ Γ₁ Γ₂ ∧
      CDerives Δ Γ₁ V (.val (.tensor A B)) ∧ CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γ₂) M j' := by
  induction h with
  | tensorE hs hV hM => intro V M he; cases he; exact ⟨_, _, _, _, _, hs, hV, hM⟩
  | force => intro V M he; rcases forceE_var he with h | h <;> cases h
  | _ => intro V M he; cd_terms

/-- **A `V; M` is `[1E]`'s**: `V` at `1`, `M` typed. -/
theorem der_seq {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ V M, e = .seq V M → ∃ Γ₁ Γ₂ j', Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ V (.val .unit) ∧
      CDerives Δ Γ₂ M j' := by
  induction h with
  | unitE hs hV hM => intro V M he; cases he; exact ⟨_, _, _, hs, hV, hM⟩
  | force => intro V M he; rcases forceE_var he with h | h <;> cases h
  | _ => intro V M he; cd_terms

/-- **A `M then x. N unwind D` is `[then]`'s**: `M` and `N` on the two sides of a split. -/
theorem der_then {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ N D M, e = thenE N D M → ∃ Γ₁ Γ₂ A j₁ j₂, Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ M j₁ ∧
      CDerives Δ (⟨A, true⟩ :: Γ₂) N j₂ := by
  induction h with
  | effThen hs _ _ _ hM hN _ => intro N D M he; cases he; exact ⟨_, _, _, _, _, hs, hM, hN⟩
  | force => intro N D M he; rcases forceE_var he with h | h <;> simp [thenE] at h
  | lolliE _ _ hf =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hf _ _ rfl id (by decide) (by decide)).elim
  | app _ hM _ =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allEV hM _ =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | _ => intro N D M he; cd_terms

/-- **A handler term is `[handle]`'s**: its tags are its signature's, and the handler pair is typed
at the tensor of the return clause's type and the clauses', over a consumed context. -/
theorem der_hnd {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ (n : UInt32) (Q H M : Expr),
      e = .app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) (.pair Q H))) M →
      ∃ (Γ₁ Γ₂ : Ctx VTy) (S : Row) (E : List (Qual × VTy × VTy)) (A R : VTy), Ctx.SplitP Γ Γ₁ Γ₂ ∧
        Ctx.DeadP Γ₁ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
        CDerives Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E))) := by
  induction h with
  | effHandleV hs hd _ hc _ _ _ _ =>
      intro n Q H M he
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he
      obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := he
      exact ⟨_, _, _, _, _, _, hs, hd, rfl, hc⟩
  | force => intro n Q H M he; rcases forceE_var he with h | h <;> simp at h
  | lolliE _ _ hf =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hf _ _ rfl id (by decide) (by decide)).elim
  | app _ hM _ =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allEV hM _ =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | ret _ ih | ofRet _ ih | effSub _ _ ih | nuIn _ _ ih | nuOut _ _ ih | bangE _ ih | boxI _ _ ih
  | boxE _ ih | immSub _ _ ih | mutSub _ _ ih | roll _ _ _ ih | unroll _ ih => exact ih
  | _ => intro n Q H M he; cd_at he

/-! #### λ-values -/

/-- `forget`'s axioms (`forgetV` is `forget`): at `!A`, `Imm`, `Mut`, `Unk` and `ArrayImm`. -/
def ForgetTy (T : VTy) : Prop :=
  (∃ X, T = .thunk (.arr X (.ret .unit)) ∧
    ((∃ A, X = .bang A) ∨ (∃ a A, X = .imm a A) ∨ (∃ a A, X = .mut a A) ∨ X = .unk)) ∨
  (∃ a A, T = .bang (.thunk (.arr (.fam (.imm a A)) (.ret .unit))))

/-- The unwinding constants' types: `U(src ⊸ cb ⊸ F_Σ R)`, the callback's argument a borrow. -/
def WithborUTy (T : VTy) : Prop :=
  ∃ src x bnd L B S R, T = withborUTy src (cbUTy x bnd L B S) S R ∧ L.persistent = false

/-- The other λ-constants. -/
def OtherLam (e : Expr) : Prop :=
  e = copy ∨ e = swap ∨ e = withbor ∨ e = withload ∨ e = withswap ∨ e = sizeV.1 ∨
    e = replaceV.1 ∨ e = arrLenV.1 ∨ e = swapV.1 ∨ (∃ F, e = (foldImmV F).1) ∨
    (∃ F, e = (foldOwnV F).1) ∨ (∃ F, e = (foldReuseV F).1) ∨ (∃ C, e = (unfoldV C).1)

/-- A λ-constant, read at the views of its axiom's type. -/
def LamAx (e : Expr) (j : Jdg) : Prop :=
  (e = forget ∧ ∃ T, ForgetTy T ∧ ValCls T j) ∨
    (∃ d, e = withborUE d ∧ ∃ T, WithborUTy T ∧ ValCls T j) ∨ (OtherLam e ∧ ∃ T, ValCls T j)

theorem LamAx.step {e : Expr} {j j' : Jdg} (hs : JS j j') (h : LamAx e j) : LamAx e j' := by
  rcases h with ⟨he, T, hT, hc⟩ | ⟨d, he, T, hT, hc⟩ | ⟨he, T, hc⟩
  · exact .inl ⟨he, T, hT, hc.step hs⟩
  · exact .inr (.inl ⟨d, he, T, hT, hc.step hs⟩)
  · exact .inr (.inr ⟨he, T, hc.step hs⟩)

/-- A row's type is a returner. -/
theorem ValCls.comp_isRet {T : VTy} {C : CTy} (h : ValCls T (.comp C)) : C.isRet = true := by
  obtain ⟨S, Y, rfl, -⟩ := h
  exact Inst.effOf_isRet S Y

theorem LamAx.not_comp {e : Expr} {C : CTy} (h : LamAx e (.comp C)) : C.isRet = true := by
  rcases h with ⟨-, T, -, hc⟩ | ⟨-, -, T, -, hc⟩ | ⟨-, T, hc⟩ <;> exact hc.comp_isRet

/-- The judgements a λ-value whose body is typed at `D` is read at: `D` itself, the views of its
thunk, and, over a persistent context, the views of the thunk's `!`. -/
def LamCls (Γ : Ctx VTy) (D : CTy) (j : Jdg) : Prop :=
  j = .comp D ∨ ValCls (.thunk D) j ∨ (Persistent Γ ∧ ValCls (.bang (.thunk D)) j)

theorem LamCls.step {Γ : Ctx VTy} {D : CTy} {j j' : Jdg} (hs : JS j j') (h : LamCls Γ D j)
    (hD : Rigid D) : LamCls Γ D j' := by
  rcases h with rfl | hc | ⟨hp, hc⟩
  · exact (hs.not_rigid hD).elim
  · exact .inr (.inl (hc.step hs))
  · exact .inr (.inr ⟨hp, hc.step hs⟩)

theorem LamCls.thunkV {Γ : Ctx VTy} {D C : CTy} (h : LamCls Γ D (.comp C)) (hC : C.isRet = false) :
    LamCls Γ D (.val (.thunk C)) := by
  rcases h with h | hc | ⟨-, hc⟩
  · cases h; exact .inr (.inl (ValCls.refl _))
  · rw [hc.comp_isRet] at hC; cases hC
  · rw [hc.comp_isRet] at hC; cases hC

theorem LamCls.bangThunkV {Γ : Ctx VTy} {D C : CTy} (h : LamCls Γ D (.comp C))
    (hC : C.isRet = false) (hp : Persistent Γ) : LamCls Γ D (.val (.bang (.thunk C))) := by
  rcases h with h | hc | ⟨-, hc⟩
  · cases h; exact .inr (.inr ⟨hp, ValCls.refl _⟩)
  · rw [hc.comp_isRet] at hC; cases hC
  · rw [hc.comp_isRet] at hC; cases hC

/-- **How a λ-value is typed**: its body under a live binder (`[⊸I]`), under a dead binder at a
row's `1 ⊸` (`[λ-dead]`), under a dead binder at a `∀` (`[∀I]`) or at a returner (the thunk of
`F A`); as the pair `⟨M, N⟩`; or as a λ-constant. -/
def LamInv (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (j : Jdg) : Prop :=
  (∃ A D, CDerives Δ (⟨A, true⟩ :: Γ) M (.comp D) ∧ LamCls Γ (.arr A D) j) ∨
  (∃ S B, CDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (CTy.effOf S B)) ∧
    LamCls Γ (.arr .unit (CTy.effOf S B)) j) ∨
  (∃ x b Δ' S C, CDerives Δ' (⟨S, false⟩ :: Γ) M (.comp C) ∧ LamCls Γ (.all x b C) j) ∨
  (∃ A, CDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) ∧
    (ValCls (.thunk (.ret A)) j ∨ (Persistent Γ ∧ ValCls (.bang (.thunk (.ret A))) j))) ∨
  (∃ M₁ M₂, Expr.lam M = withPair M₁ M₂) ∨
  LamAx (.lam M) j

theorem LamInv.step {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {j j' : Jdg} (hs : JS j j')
    (h : LamInv Δ Γ M j) : LamInv Δ Γ M j' := by
  rcases h with ⟨A, D, hM, hc⟩ | ⟨S, B, hM, hc⟩ | ⟨x, b, Δ', S, C, hM, hc⟩ | ⟨A, hM, hc⟩ | hw | hx
  · exact .inl ⟨A, D, hM, hc.step hs (rigid_arr _ _)⟩
  · exact .inr (.inl ⟨S, B, hM, hc.step hs (rigid_arr _ _)⟩)
  · exact .inr (.inr (.inl ⟨x, b, Δ', S, C, hM, hc.step hs (rigid_all _ _ _)⟩))
  · rcases hc with hc | ⟨hp, hc⟩
    · exact .inr (.inr (.inr (.inl ⟨A, hM, .inl (hc.step hs)⟩)))
    · exact .inr (.inr (.inr (.inl ⟨A, hM, .inr ⟨hp, hc.step hs⟩⟩)))
  · exact .inr (.inr (.inr (.inr (.inl hw))))
  · exact .inr (.inr (.inr (.inr (.inr (hx.step hs)))))

theorem LamInv.thunkV {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : LamInv Δ Γ M (.comp C)) (hC : C.isRet = false) : LamInv Δ Γ M (.val (.thunk C)) := by
  rcases h with ⟨A, D, hM, hc⟩ | ⟨S, B, hM, hc⟩ | ⟨x, b, Δ', S, C', hM, hc⟩ | ⟨A, hM, hc⟩ | hw | hx
  · exact .inl ⟨A, D, hM, hc.thunkV hC⟩
  · exact .inr (.inl ⟨S, B, hM, hc.thunkV hC⟩)
  · exact .inr (.inr (.inl ⟨x, b, Δ', S, C', hM, hc.thunkV hC⟩))
  · rcases hc with hc | ⟨-, hc⟩ <;> (rw [hc.comp_isRet] at hC; cases hC)
  · exact .inr (.inr (.inr (.inr (.inl hw))))
  · rw [hx.not_comp] at hC; cases hC

theorem LamInv.bangThunkV {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : LamInv Δ Γ M (.comp C)) (hC : C.isRet = false) (hp : Persistent Γ) :
    LamInv Δ Γ M (.val (.bang (.thunk C))) := by
  rcases h with ⟨A, D, hM, hc⟩ | ⟨S, B, hM, hc⟩ | ⟨x, b, Δ', S, C', hM, hc⟩ | ⟨A, hM, hc⟩ | hw | hx
  · exact .inl ⟨A, D, hM, hc.bangThunkV hC hp⟩
  · exact .inr (.inl ⟨S, B, hM, hc.bangThunkV hC hp⟩)
  · exact .inr (.inr (.inl ⟨x, b, Δ', S, C', hM, hc.bangThunkV hC hp⟩))
  · rcases hc with hc | ⟨-, hc⟩ <;> (rw [hc.comp_isRet] at hC; cases hC)
  · exact .inr (.inr (.inr (.inr (.inl hw))))
  · rw [hx.not_comp] at hC; cases hC

theorem LamInv.ofAx {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {j : Jdg} (h : LamAx (.lam M) j) :
    LamInv Δ Γ M j :=
  .inr (.inr (.inr (.inr (.inr h))))

theorem lamAx_other {e : Expr} (h : OtherLam e) (T : VTy) : LamAx e (.val T) :=
  .inr (.inr ⟨h, T, ValCls.refl T⟩)

theorem lamAx_forget {T : VTy} (h : ForgetTy T) : LamAx forget (.val T) :=
  .inl ⟨rfl, T, h, ValCls.refl T⟩

theorem lamAx_withborU (d : Expr) {T : VTy} (h : WithborUTy T) : LamAx (withborUE d) (.val T) :=
  .inr (.inl ⟨d, rfl, T, h, ValCls.refl T⟩)

/-- **A λ-value is typed through the rule that types its body, or as a λ-constant.** -/
theorem der_lam {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ M, e = .lam M → LamInv Δ Γ M j := by
  induction h with
  | lam h => intro M he; cases he; exact .inl ⟨_, _, h, .inl rfl⟩
  | lamDead h => intro M he; cases he; exact .inr (.inl ⟨_, _, h, .inl rfl⟩)
  | allI _ _ _ h => intro M he; cases he; exact .inr (.inr (.inl ⟨_, _, _, _, _, h, .inl rfl⟩))
  | thunkF h => intro M he; cases he; exact .inr (.inr (.inr (.inl ⟨_, h, .inl (ValCls.refl _)⟩)))
  | bangThunkF hp h =>
      intro M he; cases he; exact .inr (.inr (.inr (.inl ⟨_, h, .inr ⟨hp, ValCls.refl _⟩⟩)))
  | thunkV hC _ ih => intro M he; exact (ih M he).thunkV hC
  | bangThunkV hp hC _ ih => intro M he; exact (ih M he).bangThunkV hC hp
  | withI => intro M he; exact .inr (.inr (.inr (.inr (.inl ⟨_, _, he.symm⟩))))
  | ret _ ih => intro M he; exact (ih M he).step (JS.ret _)
  | ofRet _ ih => intro M he; exact (ih M he).step (JS.ofRet _)
  | effSub _ _ ih => intro M he; exact (ih M he).step (JS.effSub _ _ _)
  | nuIn hC _ ih => intro M he; exact (ih M he).step (JS.nuIn _ hC)
  | nuOut hC _ ih => intro M he; exact (ih M he).step (JS.nuOut _ hC)
  | bangE _ ih => intro M he; exact (ih M he).step (JS.val (VS.bang _))
  | boxI _ _ ih => intro M he; exact (ih M he).step (JS.val (VS.boxI _ _))
  | boxE _ ih => intro M he; exact (ih M he).step (JS.val (VS.boxE _ _))
  | immSub _ _ ih => intro M he; exact (ih M he).step (JS.val (VS.immS _ _ _))
  | mutSub _ _ ih => intro M he; exact (ih M he).step (JS.val (VS.mutS _ _ _))
  | roll _ _ _ ih => intro M he; exact (ih M he).step (JS.val (VS.roll _))
  | unroll _ ih => intro M he; exact (ih M he).step (JS.val (VS.unroll _))
  | copyBang => intro M he; exact LamInv.ofAx (he ▸ lamAx_other (.inl rfl) _)
  | copy => intro M he; exact LamInv.ofAx (he ▸ lamAx_other (.inl rfl) _)
  | arrCopy => intro M he; exact LamInv.ofAx (he ▸ lamAx_other (.inl rfl) _)
  | swap => intro M he; exact LamInv.ofAx (he ▸ lamAx_other (.inr (.inl rfl)) _)
  | sliceBorrowM | sliceBorrowI | withbor1 | withbor2 | withbor3 =>
      intro M he; exact LamInv.ofAx (he ▸ lamAx_other (.inr (.inr (.inl rfl))) _)
  | withload | withloadU =>
      intro M he; exact LamInv.ofAx (he ▸ lamAx_other (.inr (.inr (.inr (.inl rfl)))) _)
  | withswap =>
      intro M he; exact LamInv.ofAx (he ▸ lamAx_other (.inr (.inr (.inr (.inr (.inl rfl))))) _)
  | arrSize | sliceLenM =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))) _)
  | arrReplace | sliceReplaceM =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))) _)
  | arrLen =>
      intro M he
      exact LamInv.ofAx
        (he ▸ lamAx_other (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))) _)
  | sliceSwapM =>
      intro M he
      exact LamInv.ofAx
        (he ▸ lamAx_other (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))) _)
  | foldImm =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))))) _)
  | foldOwn =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩))))))))))) _)
  | foldReuse =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))))))) _)
  | unfoldN =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, rfl⟩)))))))))))) _)
  | forgetBang => intro M he; exact LamInv.ofAx (he ▸ lamAx_forget (.inl ⟨_, rfl, .inl ⟨_, rfl⟩⟩))
  | forgetImm =>
      intro M he; exact LamInv.ofAx (he ▸ lamAx_forget (.inl ⟨_, rfl, .inr (.inl ⟨_, _, rfl⟩)⟩))
  | forgetMut =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_forget (.inl ⟨_, rfl, .inr (.inr (.inl ⟨_, _, rfl⟩))⟩))
  | forgetUnk =>
      intro M he; exact LamInv.ofAx (he ▸ lamAx_forget (.inl ⟨_, rfl, .inr (.inr (.inr rfl))⟩))
  | arrForget => intro M he; exact LamInv.ofAx (he ▸ lamAx_forget (.inr ⟨_, _, rfl⟩))
  | withbor1U x =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_withborU _ ⟨_, x, _, _, _, _, _, rfl, rfl⟩)
  | withbor2U x =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_withborU _ ⟨_, x, _, _, _, _, _, rfl, rfl⟩)
  | withbor3U x =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_withborU _ ⟨_, x, _, _, _, _, _, rfl, rfl⟩)
  | sliceBorrowMU x =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_withborU _ ⟨_, x, _, _, _, _, _, rfl, rfl⟩)
  | sliceBorrowIU x =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_withborU _ ⟨_, x, _, _, _, _, _, rfl, rfl⟩)
  | force => intro M he; rcases forceE_var he with h | h <;> cases h
  | _ => intro M he; cd_at he

/-! ### Reading the inversions -/

theorem vview_thunk {C₀ C : CTy} (h : VView (.thunk C₀) (.thunk C)) : C₀ = C := by
  have := h.eq_of_heads (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ h => by cases h)
  cases this; rfl

theorem not_vview_thunk_bang {C₀ : CTy} {X : VTy} (h : VView (.thunk C₀) (.bang X)) : False := by
  have := (h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)).eq_self
    (fun _ _ h => by cases h) (fun _ h => by cases h)
  cases this

theorem vview_bang_thunk {C₀ C : CTy} (h : VView (.bang (.thunk C₀)) (.thunk C)) : C₀ = C := by
  rcases h.hnf (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h)) with
    h' | ⟨A, hA, h'⟩ | ⟨a, A, h'⟩ | ⟨a, A, h'⟩
  · have := h'.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h); cases this
  · cases hA; exact vview_thunk h'
  · cases h'
  · cases h'

theorem vview_bang_bang {C₀ C : CTy} (h : VView (.bang (.thunk C₀)) (.bang (.thunk C))) :
    C₀ = C := by
  rcases h.hnf (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h)) with
    h' | ⟨A, hA, h'⟩ | ⟨a, A, h'⟩ | ⟨a, A, h'⟩
  · have := h'.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h); cases this; rfl
  · cases hA; exact (not_vview_thunk_bang h').elim
  · cases h'
  · cases h'

theorem vview_tensor {A B A' B' : VTy} (h : VView (.tensor A B) (.tensor A' B')) :
    A = A' ∧ B = B' := by
  have := h.eq_of_heads (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ h => by cases h)
  cases this; exact ⟨rfl, rfl⟩

/-- A λ-value read at a thunk was typed at that thunk's computation type. -/
theorem LamCls.val_thunk {Γ : Ctx VTy} {D C : CTy} (h : LamCls Γ D (.val (.thunk C))) : D = C := by
  rcases h with h | h | ⟨-, h⟩
  · cases h
  · exact vview_thunk h
  · exact vview_bang_thunk h

/-- A λ-value read at a `!` thunk was typed at that thunk's computation type, over a persistent
context. -/
theorem LamCls.val_bang {Γ : Ctx VTy} {D C : CTy} (h : LamCls Γ D (.val (.bang (.thunk C)))) :
    D = C ∧ Persistent Γ := by
  rcases h with h | h | ⟨hp, h⟩
  · cases h
  · exact (not_vview_thunk_bang h).elim
  · exact ⟨vview_bang_bang h, hp⟩

/-- A λ-value read at a rigid computation type was typed at it. -/
theorem LamCls.comp_rigid {Γ : Ctx VTy} {D C : CTy} (h : LamCls Γ D (.comp C)) (hC : Rigid C) :
    D = C := by
  rcases h with h | h | ⟨-, h⟩
  · cases h; rfl
  · obtain ⟨S, Y, rfl, -⟩ := h; exact (hC.1 S Y rfl).elim
  · obtain ⟨S, Y, rfl, -⟩ := h; exact (hC.1 S Y rfl).elim

/-- **A λ-value that is no λ-constant and no `⟨M, N⟩` has its body typed.** -/
theorem LamInv.body {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {j : Jdg} (h : LamInv Δ Γ M j)
    (hw : ∀ M₁ M₂, Expr.lam M ≠ withPair M₁ M₂) (hx : ¬ LamAx (.lam M) j) :
    ∃ Δ' Γ' j', CDerives Δ' Γ' M j' := by
  rcases h with ⟨A, D, hM, -⟩ | ⟨S, B, hM, -⟩ | ⟨x, b, Δ', S, C, hM, -⟩ | ⟨A, hM, -⟩ | ⟨M₁, M₂, h⟩ | h
  · exact ⟨_, _, _, hM⟩
  · exact ⟨_, _, _, hM⟩
  · exact ⟨_, _, _, hM⟩
  · exact ⟨_, _, _, hM⟩
  · exact (hw M₁ M₂ h).elim
  · exact (hx h).elim

/-- A term that is no λ-constant. -/
def NotConst (e : Expr) : Prop := e ≠ forget ∧ (∀ d, e ≠ withborUE d) ∧ ¬ OtherLam e

theorem NotConst.notAx {e : Expr} (h : NotConst e) (j : Jdg) : ¬ LamAx e j := by
  rintro (⟨he, -⟩ | ⟨d, he, -⟩ | ⟨he, -⟩)
  · exact h.1 he
  · exact h.2.1 d he
  · exact h.2.2 he

/-! ### Bindings -/

/-- **A `let` of a term that is no variable, λ-value, `()` or injection of `()`**: the term is typed
at a row over the slot's type, and the body under the slot. -/
theorem der_bind {Δ : LifeCtx} {Γ : Ctx VTy} {N M : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app (.lam N) M) j) (hMv : ∀ i, M ≠ .var i) (hMl : ∀ b, M ≠ .lam b)
    (hMu : M ≠ .unit) (hM₁ : M ≠ .inj₁ .unit) (hM₂ : M ≠ .inj₂ .unit)
    (hw : ∀ M₁ M₂, Expr.lam N ≠ withPair M₁ M₂) (hc : NotConst (.lam N)) :
    ∃ Γ₁ Γ' T b S j', CtxLe Γ₁ Γ ∧ CtxLe Γ' Γ ∧ CDerives Δ Γ₁ M (.comp (CTy.effOf S T)) ∧
      CDerives Δ (⟨T, b⟩ :: Γ') N j' := by
  obtain ⟨j₀, hb, -⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hM, hf, -⟩ | ⟨-, -, i, -, -, hi, -⟩ |
    ⟨N', Γ₁, Γ₂, A, S, C, hN, hs, hM, hN', -⟩ | ⟨-, b, -, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · rcases der_lam hf N rfl with ⟨A', D, hN, hcl⟩ | ⟨S', B', hN, hcl⟩ | ⟨_, _, _, _, _, _, hcl⟩ |
      ⟨_, _, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx
    · obtain ⟨rfl, -⟩ : A' = A ∧ D = .ret B := by
        have := hcl.val_thunk; cases this; exact ⟨rfl, rfl⟩
      exact ⟨Γ₁, Γ₂, A', true, [], _, splitP_le_left hs, splitP_le_right hs, .ret hM, hN⟩
    · have := hcl.val_thunk
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      exact ⟨Γ₁, Γ₂, .unit, false, [], _, splitP_le_left hs, splitP_le_right hs, .ret hM, hN⟩
    · have := hcl.val_thunk; cases this
    · rcases hcl with hcl | ⟨-, hcl⟩
      · have := vview_thunk hcl; cases this
      · have := vview_bang_thunk hcl; cases this
    · exact (hw M₁ M₂ hwp).elim
    · exact (hc.notAx _ hx).elim
  · exact (hMv i hi).elim
  · cases hN
    exact ⟨Γ₁, Γ₂, A, true, S, _, splitP_le_left hs, splitP_le_right hs, hM, hN'⟩
  · exact (hMl b hb).elim
  · exact (hMu hu).elim
  · exact (hMu hu).elim
  · exact (hM₁ hu).elim
  · exact (hM₂ hu).elim
  · exact (hMu hu).elim
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> cases hX

/-- **A `let` of a closed λ-value**: as `der_bind`, or the polymorphic let, the body with the value in
place under a dead slot. -/
theorem der_bindLam {Δ : LifeCtx} {Γ : Ctx VTy} {N b : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app (.lam N) (.lam b)) j)
    (hw : ∀ M₁ M₂, Expr.lam N ≠ withPair M₁ M₂) (hc : NotConst (.lam N)) :
    (∃ Γ₁ Γ' T b' S j', CtxLe Γ₁ Γ ∧ CtxLe Γ' Γ ∧ CDerives Δ Γ₁ (.lam b) (.comp (CTy.effOf S T)) ∧
      CDerives Δ (⟨T, b'⟩ :: Γ') N j') ∨
    ∃ j', CDerives Δ (⟨.unit, false⟩ :: Γ) ((N.subst 0 (Val.lam b)).shift 1 0) j' := by
  obtain ⟨j₀, hb, -⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hM, hf, -⟩ | ⟨-, -, i, -, -, hi, -⟩ |
    ⟨N', Γ₁, Γ₂, A, S, C, hN, hs, hM, hN', -⟩ | ⟨N', b', C, hN, hb', -, -, hN', -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · refine .inl ?_
    rcases der_lam hf N rfl with ⟨A', D, hN, hcl⟩ | ⟨S', B', hN, hcl⟩ | ⟨_, _, _, _, _, _, hcl⟩ |
      ⟨_, _, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx
    · obtain ⟨rfl, -⟩ : A' = A ∧ D = .ret B := by
        have := hcl.val_thunk; cases this; exact ⟨rfl, rfl⟩
      exact ⟨Γ₁, Γ₂, A', true, [], _, splitP_le_left hs, splitP_le_right hs, .ret hM, hN⟩
    · have := hcl.val_thunk
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      exact ⟨Γ₁, Γ₂, .unit, false, [], _, splitP_le_left hs, splitP_le_right hs, .ret hM, hN⟩
    · have := hcl.val_thunk; cases this
    · rcases hcl with hcl | ⟨-, hcl⟩
      · have := vview_thunk hcl; cases this
      · have := vview_bang_thunk hcl; cases this
    · exact (hw M₁ M₂ hwp).elim
    · exact (hc.notAx _ hx).elim
  · cases hi
  · cases hN
    exact .inl ⟨Γ₁, Γ₂, A, true, S, _, splitP_le_left hs, splitP_le_right hs, hM, hN'⟩
  · cases hN; cases hb'; exact .inr ⟨_, hN'⟩
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> cases hX

/-! ### AT08: `load` has no rule -/

/-- `load x` has no derivation. -/
theorem not_der_load_app {Δ : LifeCtx} {Γ : Ctx VTy} {X : Expr} {j : Jdg} :
    ¬ CDerives Δ Γ (.app (.prim .load) X) j :=
  fun h => not_der_app_prim h .load X rfl id (by decide) (by decide)

/-- AT08's clause, under its binder. -/
abbrev at08Body : Expr :=
  .letpair (.var 0)
    (bindE (.app alloc' (.var 0))
      (bindE (.app (.val (.prim .load)) (.var 0))
        (bindE (.app (.val (.prim .load)) (.var 1))
          (.seq (dropB (.app free' (.var 2)))
            (.seq (.app (.app (.var 1) (.val (.inj₁ .unit))) (.val .unit))
              (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit)))))))

/-- A term is no λ-constant, by unfolding. -/
macro "not_const" : tactic => `(tactic| (simp only [NotConst, OtherLam, forget, copy, swap, withbor,
    withload, withswap, sizeV, replaceV, arrLenV, swapV, foldImmV, foldOwnV, foldReuseV, unfoldV,
    withborUE, Expr.val, Val.lam, lam2, elet, unit', v0, v1, v2, v3, load', store', thenE, ne_eq,
    bindE, hndTerm, hndExpr, Val.unit, Val.prim, Val.i32, Val.inj₁, Val.inj₂, Val.pair, fooE,
    BoCa.BoLo.performE, opArgE, dropB, handleWith, free', alloc',
    Expr.lam.injEq, reduceCtorEq, not_false_eq_true, not_exists, not_or, forall_const, and_self,
    implies_true, and_true, true_and, exists_false, or_self, Expr.app.injEq, Expr.letpair.injEq,
    Expr.pair.injEq, Expr.seq.injEq, Expr.case.injEq, false_and, and_false]))

/-- A hypothesis that a term is one of the other λ-constants is refuted by unfolding. -/
macro "not_other " h:ident : tactic => `(tactic| (simp [OtherLam, copy, swap, withbor, withload,
    withswap, sizeV, replaceV, arrLenV, swapV, foldImmV, foldOwnV, foldReuseV, unfoldV, Expr.val,
    Val.lam, lam2, elet, unit', v0, v1, v2, v3, withborUE, thenE, load', store', Val.prim,
    Val.unit] at $h:ident))

/-- A term is no `⟨M, N⟩`, by unfolding. -/
macro "not_withPair" : tactic => `(tactic| (intro M₁ M₂ h; simp [withPair, Expr.val, Val.lam, bindE,
    hndTerm, hndExpr, Val.unit, Val.prim, Val.i32, Val.inj₁, Val.inj₂, Val.pair, fooE, dropB,
    BoCa.BoLo.performE, opArgE, handleWith, free', alloc'] at h))

/-- **AT08 has no derivation**: its clause loads a cell, and `load` has no rule. -/
theorem not_der_at08 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at08 j := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, hP, _⟩ := der_bind (M := .pair (.lam at08Body) .unit) h
    (fun i h => by cases h) (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (by not_withPair) (by not_const)
  rcases der_pair hP _ _ rfl with ⟨_, _, _, _, _, hCL, _, _⟩ | he
  · obtain ⟨_, _, _, hB⟩ := (der_lam hCL _ rfl).body (by not_withPair)
      (NotConst.notAx (by not_const) _)
    obtain ⟨_, _, _, _, _, _, _, hR₁⟩ := der_letpair hB _ _ rfl
    obtain ⟨_, _, _, _, _, _, _, _, _, hR₂⟩ := der_bind hR₁ (fun i h => by cases h)
      (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
      (by not_withPair) (by not_const)
    obtain ⟨_, _, _, _, _, _, _, _, hL, _⟩ := der_bind hR₂ (fun i h => by cases h)
      (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
      (by not_withPair) (by not_const)
    exact not_der_load_app hL
  · simp [emptyFamV, Val.arr] at he

/-! ### Helpers for the clause tuples -/

/-- A variable read at a value type: a view of its slot's type. -/
theorem VarCls.val {T Y : VTy} (h : VarCls T (.val Y)) : VView T Y := by
  rcases h with h | ⟨C, -, hC, hr⟩
  · exact h
  · obtain ⟨S, A, rfl⟩ := hr.comp_val
    rw [Inst.effOf_isRet] at hC; cases hC

/-- **A handler's clause tuple**: in `handle_n M with (X, x₁)`, the slot of `x₁` is live and its type
views to the clauses' type, whose signature carries the handler's tags. -/
theorem hnd_clauses {Δ : LifeCtx} {Γ : Ctx VTy} {n : UInt32} {qs : List Qual} {X M : Expr}
    {j : Jdg} (h : CDerives Δ Γ (hndExpr n qs (.pair X (.var 1)) M) j) :
    ∃ T S R E, Γ[1]? = some ⟨T, true⟩ ∧ VView T (clausesTy S R E) ∧ E.map Prod.fst = qs := by
  obtain ⟨Γ₁, Γ₂, S, E, A, R, hs, -, hQ, hH⟩ := der_hnd h n _ _ M rfl
  have hE : E.map Prod.fst = qs := (qualsVal_inj hQ).symm
  rcases der_pair hH X (.var 1) rfl with ⟨Γ₁₁, Γ₁₂, A', B', hs', -, hv, hc⟩ | he
  · obtain ⟨-, rfl⟩ := vview_tensor hc
    obtain ⟨T, hT, hcT⟩ := der_var hv 1 rfl
    exact ⟨T, S, R, E, splitP_le_left hs _ _ (splitP_le_right hs' _ _ hT), hcT.val, hE⟩
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he

/-- **A pair read at a row**: its first part is read at the first factor of a tensor whose views
reach the row's type. -/
theorem pair_row {Δ : LifeCtx} {Γ : Ctx VTy} {a b : Expr} {S : Row} {T : VTy}
    (h : CDerives Δ Γ (.pair a b) (.comp (CTy.effOf S T))) (hb : ∀ c, b ≠ .prim c) :
    ∃ Γ' A B, CtxLe Γ' Γ ∧ CDerives Δ Γ' a (.val A) ∧ VView (.tensor A B) T := by
  rcases der_pair h a b rfl with ⟨Γ₁, Γ₂, A, B, hs, ha, -, hc⟩ | he
  · obtain ⟨S', Y, he, hY⟩ := hc
    obtain ⟨-, rfl⟩ := Inst.effOf_inj he
    exact ⟨Γ₁, A, B, splitP_le_left hs, ha, hY⟩
  · simp only [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32, Expr.pair.injEq] at he
    exact (hb _ he.2).elim

/-- **A λ-value read at a `!` thunk of `P ⊸ D`, `P` no `1`**: its context is persistent, and its body
is typed under a live `P`. -/
theorem lam_bang {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {P : VTy} {D : CTy}
    (h : CDerives Δ Γ (.lam M) (.val (.bang (.thunk (.arr P D))))) (hP : P ≠ .unit)
    (hw : ∀ M₁ M₂, Expr.lam M ≠ withPair M₁ M₂) (hc : NotConst (.lam M)) :
    Persistent Γ ∧ CDerives Δ (⟨P, true⟩ :: Γ) M (.comp D) := by
  rcases der_lam h M rfl with ⟨A, D', hM, hcl⟩ | ⟨S, B, hM, hcl⟩ | ⟨x, b, Δ', S, C, hM, hcl⟩ |
    ⟨A, hM, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx
  · obtain ⟨he, hp⟩ := hcl.val_bang
    cases he
    exact ⟨hp, hM⟩
  · obtain ⟨he, -⟩ := hcl.val_bang
    simp only [CTy.arr.injEq] at he
    exact (hP he.1.symm).elim
  · obtain ⟨he, -⟩ := hcl.val_bang; cases he
  · rcases hcl with hcl | ⟨-, hcl⟩
    · exact (not_vview_thunk_bang hcl).elim
    · have := vview_bang_bang hcl; cases this
  · exact (hw M₁ M₂ hwp).elim
  · exact (hc.notAx _ hx).elim

/-! ### AT13: `forget κ` -/

/-- A type whose head is a thunk of an `&`: what `κ` is at `lin` and `aff`. -/
theorem kview {C₁ C₂ : CTy} {A : VTy} (h : VView (.thunk (.amp C₁ C₂)) A) :
    A.persistent = false ∧ Hnf A (.thunk (.amp C₁ C₂)) := by
  have hh := h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
  exact ⟨by rw [hh.persistent]; rfl, hh⟩

/-- A type with a thunk head is none of `forget`'s arguments, and no `1`. -/
theorem kview_not {C : CTy} {A : VTy} (h : Hnf A (.thunk C)) :
    (∀ X, A ≠ .bang X) ∧ (∀ a X, A ≠ .imm a X) ∧ (∀ a X, A ≠ .mut a X) ∧ A ≠ .unk ∧
      (∀ L, A ≠ .fam L) ∧ A ≠ .unit := by
  refine ⟨fun X hA => ?_, fun a X hA => ?_, fun a X hA => ?_, fun hA => ?_, fun L hA => ?_,
    fun hA => ?_⟩ <;> subst hA <;>
    have := h.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h) <;> cases this

/-- **`forget κ` has no derivation at `1`** when `κ`'s slot is a thunk of an `&` (`kTy` at `lin` and
`aff`): `forget`'s axioms take `!`, `Imm`, `Mut`, `Unk` and `ArrayImm`, and as a λ it drops its
argument only at a persistent type. -/
theorem not_forget_kappa {Δ : LifeCtx} {Γ : Ctx VTy} {C₁ C₂ : CTy}
    (h : CDerives Δ Γ (.app forget (.var 0)) (.val .unit))
    (hΓ : ∀ T, Γ[0]? = some ⟨T, true⟩ → T = .thunk (.amp C₁ C₂)) : False := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i, A, C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, Γ₁, Γ₂, A, S, C, hN, hs, hY, hU, rfl⟩ | ⟨N, b, C, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · -- `⊸E`: `forget` at `A ⊸ B`, `κ` at `A`
    obtain ⟨T, hT, hcT⟩ := der_var hY 0 rfl
    obtain rfl := hΓ T (splitP_le_left hs _ _ hT)
    obtain ⟨hAp, hAh⟩ := kview hcT.val
    obtain ⟨hb, hi, hm, hu, hfam, hun⟩ := kview_not hAh
    rcases der_lam hf .unit rfl with ⟨A', D, hM, hcl⟩ | ⟨S, B', hM, hcl⟩ |
      ⟨x, b, Δ', S, C, hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx
    · have := hcl.val_thunk
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rcases der_unit hM rfl with ⟨hd, -⟩ | hr'
      · have := deadP_slot hd (k := 0) rfl
        simp [VTy.Persistent, hAp] at this
      · have := hr'.rigid rigid_top; cases this
    · have := hcl.val_thunk
      simp only [CTy.arr.injEq] at this
      exact hun this.1.symm
    · have := hcl.val_thunk; cases this
    · rcases hcl with hcl | ⟨-, hcl⟩
      · have := vview_thunk hcl; cases this
      · have := vview_bang_thunk hcl; cases this
    · simp [withPair, Expr.val, Val.lam] at hwp
    · rcases hx with ⟨-, T₀, hT₀, hc₀⟩ | ⟨d, he, -⟩ | ⟨ho, -⟩
      · rcases hT₀ with ⟨X, rfl, hX⟩ | ⟨a, A', rfl⟩
        · have := vview_thunk hc₀
          simp only [CTy.arr.injEq] at this
          obtain ⟨rfl, -⟩ := this
          rcases hX with ⟨X', rfl⟩ | ⟨a, X', rfl⟩ | ⟨a, X', rfl⟩ | rfl
          · exact hb X' rfl
          · exact hi a X' rfl
          · exact hm a X' rfl
          · exact hu rfl
        · have := vview_bang_thunk hc₀
          simp only [CTy.arr.injEq] at this
          exact hfam _ this.1.symm
      · simp [withborUE, Expr.val, Val.lam] at he
      · simp only [OtherLam, copy, swap, withbor, withload, withswap, sizeV, replaceV, arrLenV, swapV,
          foldImmV, foldOwnV, foldReuseV, unfoldV, Expr.val, Val.lam, lam2, elet, unit', v0, v1, v2,
          v3, Expr.lam.injEq, reduceCtorEq, exists_false, or_self] at ho
  · -- `[app]`: `forget` at `κ ⊸ C`, typed at `κ`'s slot
    cases hi
    obtain rfl := hΓ A (splitP_le_right hs _ _ (soloP_le hx))
    obtain ⟨S', Y', rfl⟩ := hr.comp_val
    rcases der_lam hf .unit rfl with ⟨A', D, hM, hcl⟩ | ⟨S, B', hM, hcl⟩ |
      ⟨x, b, Δ', S, C, hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx'
    · have := hcl.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rcases der_unit hM rfl with ⟨hd, -⟩ | hr'
      · have := deadP_slot hd (k := 0) rfl
        simp [VTy.Persistent, VTy.persistent] at this
      · have := (hr'.rigid rigid_top)
        simp only [Jdg.comp.injEq] at this
        exact effOf_ne_top _ _ this
    · have := hcl.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      cases this.1
    · have := hcl.comp_rigid (rigid_arr _ _); cases this
    · rcases hcl with hcl | ⟨-, hcl⟩
      · obtain ⟨S, Y, he, -⟩ := hcl; exact effOf_ne_arr _ _ _ _ he.symm
      · obtain ⟨S, Y, he, -⟩ := hcl; exact effOf_ne_arr _ _ _ _ he.symm
    · simp [withPair, Expr.val, Val.lam] at hwp
    · have := hx'.not_comp; simp [CTy.isRet] at this
  · -- `[let]`: `κ` at a row over `A`, `()` under `A`
    simp only [forget, Expr.val, Val.lam, unit', Val.unit, Expr.lam.injEq] at hN
    subst hN
    obtain ⟨S', Y', rfl⟩ := hr.comp_val
    obtain ⟨T, hT, hcT⟩ := der_var hY 0 rfl
    obtain rfl := hΓ T (splitP_le_left hs _ _ hT)
    rcases der_unit hU rfl with ⟨hd, -⟩ | hr'
    · have hAp := deadP_slot hd (k := 0) rfl
      rcases hcT with ⟨S'', Y, he, hv⟩ | ⟨C', hC', -, hr''⟩
      · obtain ⟨-, rfl⟩ := Inst.effOf_inj he
        have := (kview hv).1
        simp [VTy.Persistent, this] at hAp
      · cases hC'
        obtain ⟨D', he, hD'⟩ := hr''.ampNu (.inl ⟨_, _, rfl⟩)
        simp only [Jdg.comp.injEq] at he
        rcases hD' with ⟨_, _, h'⟩ | ⟨_, h'⟩
        · exact Inst.effOf_ne_amp _ _ _ _ (he.trans h')
        · exact Inst.effOf_ne_nu _ _ _ (he.trans h')
    · have := hr'.rigid rigid_top
      simp only [Jdg.comp.injEq] at this
      exact effOf_ne_top _ _ this
  · cases hb
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> simp [forget, Expr.val, Val.lam] at hX

/-! ### The handler of the clause tuple `(cl, ())` -/

/-- **The clause tuple's type**: in `handleWith n q cl M` typed at any judgement, the tuple `(cl, ())`
is read at a row over a type viewing to `clausesTy S R E`, whose tags are `[q]`. -/
theorem handleWith_clause {Δ : LifeCtx} {Γ : Ctx VTy} {n : UInt32} {q : Qual} {cl M : Expr}
    {j : Jdg} (h : CDerives Δ Γ (handleWith n q cl M) j)
    (hcl' : ∀ b, Expr.pair cl .unit ≠ .lam b)
    (hNc : NotConst (.lam (bindE (.val (.lam (.var 0))) (hndTerm n [q] 0 1 M))))
    (hHc : NotConst (.lam (hndTerm n [q] 0 1 M)))
    (hM : ((M.subst 0 (Val.lam (.var 0))).shift 1 0) = M) :
    ∃ Γ₁ S₁ T₁ S R E, CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ (.pair cl .unit) (.comp (CTy.effOf S₁ T₁)) ∧
      VView T₁ (clausesTy S R E) ∧ E.map Prod.fst = [q] := by
  obtain ⟨Γ₁, Γ', T₁, b, S₁, j₁, hle₁, -, hP, hN₁⟩ := der_bind (M := .pair cl .unit) h
    (fun i h => by cases h) (fun b h => hcl' b h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (by not_withPair) hNc
  have hH : ∃ Γ₄ j₄ X, (∀ T, Γ₄[1]? = some ⟨T, true⟩ → T = T₁) ∧
      CDerives Δ Γ₄ (hndExpr n [q] (.pair X (.var 1)) M) j₄ := by
    rcases der_bindLam (N := hndTerm n [q] 0 1 M) (b := .var 0) hN₁ (by not_withPair) hHc with
      ⟨_, Γ'', T₀, b₀, _, j'', _, hle'', _, hH5⟩ | ⟨j'', hH5⟩
    · refine ⟨_, _, .var 0, fun T hT => ?_, hH5⟩
      have := hle'' 0 T (by simpa using hT)
      simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at this
      exact this.1.symm
    · refine ⟨⟨.unit, false⟩ :: ⟨T₁, b⟩ :: Γ', j'', .lam (.var 0), fun T hT => ?_, ?_⟩
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Slot.mk.injEq] at hT
        exact hT.1.symm
      · have he : ((hndTerm n [q] 0 1 M).subst 0 (Val.lam (.var 0))).shift 1 0 =
            hndExpr n [q] (.pair (.lam (.var 0)) (.var 1)) M := by
          simp only [hndTerm, hndExpr, Expr.subst, Expr.shift, hM]
          simp [qualsVal, Val.pair, Val.i32, Val.unit, Val.prim, Val.lam, Expr.subst, Expr.shift]
        rw [he] at hH5
        exact hH5
  obtain ⟨Γ₄, j₄, X, hslot, hH5⟩ := hH
  obtain ⟨T, S, R, E, hT, hv, hE⟩ := hnd_clauses hH5
  obtain rfl := hslot T hT
  exact ⟨Γ₁, S₁, T, S, R, E, hle₁, hP, hv, hE⟩

/-- The clause tuple's clause is read at the clause type of its handler's one operation: at a linear
operation, `!U(A ⊗ kTy ⊸ F_Σ R)`. -/
theorem clause_lin {Δ : LifeCtx} {Γ : Ctx VTy} {cl : Expr} {S₁ : Row} {T₁ : VTy} {S : Row}
    {R : VTy} {E : List (Qual × VTy × VTy)}
    (hP : CDerives Δ Γ (.pair cl .unit) (.comp (CTy.effOf S₁ T₁)))
    (hv : VView T₁ (clausesTy S R E)) (hE : E.map Prod.fst = [.lin]) :
    ∃ Γ' A₀ B₀, CtxLe Γ' Γ ∧ CDerives Δ Γ' cl
      (.val (.bang (.thunk (.arr (.tensor A₀ (.thunk (.amp (.arr B₀ (CTy.effOf S R)) .top)))
        (CTy.effOf S R))))) := by
  obtain ⟨⟨q, A₀, B₀⟩, rfl⟩ : ∃ e, E = [e] := by
    cases E with
    | nil => simp at hE
    | cons e E' =>
        cases E' with
        | nil => exact ⟨e, rfl⟩
        | cons => simp at hE
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE
  subst hE
  obtain ⟨Γ', A, B, hle, hcl, hv'⟩ := pair_row hP (fun c h => by cases h)
  obtain ⟨rfl, -⟩ := vview_tensor (hv'.trans hv)
  have hty : clauseTy S R (.lin, A₀, B₀) =
      .bang (.thunk (.arr (.tensor A₀ (.thunk (.amp (.arr B₀ (CTy.effOf S R)) .top)))
        (CTy.effOf S R))) := by
    simp [clauseTy, kTy]
  rw [hty] at hcl
  exact ⟨Γ', A₀, B₀, hle, hcl⟩

/-! ### AT13: `forget κ` -/

/-- AT13's clause: `λ(a, κ). forget κ; ()`. -/
abbrev at13Cl : Expr := .lam (.letpair (.var 0) (.seq (.app forget (.var 0)) unit'))

/-- **AT13 has no derivation**: the clause's `κ` is at `kTy` at `lin` (the clause tuple is
`[handle]`'s), and `forget κ` has no derivation there (`not_forget_kappa`). -/
theorem not_der_at13 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at13 j := by
  intro h
  obtain ⟨Γ₁, S₁, T₁, S, R, E, -, hP, hv, hE⟩ := handleWith_clause (cl := at13Cl) h
    (fun b h => by cases h) (by not_const) (by not_const) rfl
  obtain ⟨Γ_cl, A₀, B₀, -, hCL⟩ := clause_lin hP hv hE
  obtain ⟨-, hB⟩ := lam_bang hCL (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨Γ₆₁, Γ₆₂, A₆, B₆, j₆, hs₆, hV₆, hM₆⟩ := der_letpair hB _ _ rfl
  obtain ⟨T₆, hT₆, hc₆⟩ := der_var hV₆ 0 rfl
  have hT := splitP_le_left hs₆ 0 T₆ hT₆
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at hT
  subst hT
  obtain ⟨-, rfl⟩ := vview_tensor hc₆.val
  obtain ⟨Γ₇₁, Γ₇₂, j₇, hs₇, hF, -⟩ := der_seq hM₆ _ _ rfl
  refine not_forget_kappa (C₁ := .arr B₀ (CTy.effOf S R)) (C₂ := .top) hF (fun T hT => ?_)
  have := splitP_le_left hs₇ 0 T hT
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at this
  exact this.symm

/-! ### AT06: a clause captures the linear cell -/

/-- `alloc (inj₁ ())`, read at a row, is at a view of a `Ref`. -/
theorem alloc_row {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {T : VTy}
    (h : CDerives Δ Γ (.app alloc' (.inj₁ unit')) (.comp (CTy.effOf S T))) :
    ∃ A, VView (.ref A) T := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨-, -, i, -, -, hi, -⟩ |
    ⟨N, -, -, -, -, -, hN, -⟩ | ⟨N, b, C, hN, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨C, D, -, hX, rfl⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · obtain ⟨A₀, hc⟩ := der_prim_alloc hf rfl
    have := vview_thunk hc
    simp only [CTy.arr.injEq, CTy.ret.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨S', Y, he, hY'⟩ := (ValCls.refl (.ref A₀)).reach hr
    obtain ⟨-, rfl⟩ := Inst.effOf_inj he
    exact ⟨A₀, hY'⟩
  · cases hi
  · cases hN
  · cases hN
  · cases hu
  · cases hu
  · obtain ⟨A₀, S', Y, he, -⟩ := der_prim_alloc hX rfl
    exact (Inst.effOf_ne_amp _ _ _ _ he.symm).elim
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> cases hX

/-- A view of a `Ref` is no `!`. -/
theorem vview_ref_bang {A X : VTy} (h : VView (.ref A) (.bang X)) : False := by
  have := (h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)).eq_self
    (fun _ _ h => by cases h) (fun _ h => by cases h)
  cases this

/-- AT06's clause: `λ(a, κ). drop (free c); κ.resume ()`, `c` the cell bound outside. -/
abbrev at06Cl : Expr :=
  .lam (.letpair (.var 0) (.seq (dropB (.app free' (.var 3)))
    (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit))))

/-- AT06's handled body: `foo (); drop (free c)`. -/
abbrev at06Body : Expr := bindE fooE (dropB (.app free' (.var 3)))

/-- **AT06 has no derivation**: the clause is in `[handle]`'s clause tuple, so at a `!` type, typed
over a persistent context; it uses the cell `c`, whose slot is a view of a `Ref`. -/
theorem not_der_at06 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at06 j := by
  intro h
  obtain ⟨Γ₁, Γ', T_c, b_c, S, j', -, -, hA, hN⟩ := der_bind (M := .app alloc' (.inj₁ unit')) h
    (fun i h => by cases h) (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨A₀, hvc⟩ := alloc_row hA
  obtain ⟨Γ_p, S₁, T₁, S', R, E, hle_p, hP, hv, hE⟩ :=
    handleWith_clause (cl := at06Cl) (M := at06Body) hN (fun b h => by cases h) (by not_const)
      (by not_const) rfl
  obtain ⟨Γ_cl, A₁, B₁, hle_cl, hCL⟩ := clause_lin hP hv hE
  obtain ⟨hp, hB⟩ := lam_bang hCL (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨T, hT⟩ := fv_live hB 1 (by simp [Expr.HasVar, dropB, free', Expr.val, Val.prim, Val.inj₁,
    Val.unit])
  have hT' : Γ_cl[0]? = some ⟨T, true⟩ := by simpa using hT
  obtain ⟨X, rfl⟩ := persistent_slot hp hT'
  have := hle_p 0 _ (hle_cl 0 _ hT')
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at this
  obtain ⟨rfl, -⟩ := this
  exact vview_ref_bang hvc

/-! ### AT05: the callback uses its borrow twice -/

/-- A computation type that is no returner is rigid, an `&` or a `ν`. -/
theorem rigid_or_ampNu {C : CTy} (h : C.isRet = false) : Rigid C ∨ AmpNu C := by
  cases C with
  | ret A => simp [CTy.isRet] at h
  | eff n i q A B C => simp [CTy.isRet] at h
  | arr A C => exact .inl (rigid_arr A C)
  | all x b C => exact .inl (rigid_all x b C)
  | top => exact .inl rigid_top
  | amp C D => exact .inr (.inl ⟨C, D, rfl⟩)
  | nu C => exact .inr (.inr ⟨C, rfl⟩)

/-- A value class read at a value, or at a row over it. -/
theorem ValCls.at {T₀ T : VTy} {j : Jdg} (h : ValCls T₀ j) (hj : j = .val T ∨ ∃ S, j = .comp (CTy.effOf S T)) :
    VView T₀ T := by
  rcases hj with rfl | ⟨S, rfl⟩
  · exact h
  · obtain ⟨S', Y, he, hY⟩ := h
    obtain ⟨-, rfl⟩ := Inst.effOf_inj he
    exact hY

/-- `withborU`'s inner λ: `λf. (f [] r) then b. (r, b) unwind d r`. -/
abbrev wbInner (d : Expr) : Expr :=
  thenE (.pair (.var 2) (.var 0)) (.app d (.var 2)) (.app (.app (.var 0) (.val .unit)) (.var 1))

/-- **`withborU d`'s source is used on both sides of its `then`**: typed as a λ, its binder's slot is
persistent. -/
theorem then_src {Δ : LifeCtx} {Γ : Ctx VTy} {d : Expr} {j : Jdg}
    (h : CDerives Δ Γ (wbInner d) j) : ∃ T, Γ[1]? = some ⟨T, true⟩ ∧ T.Persistent := by
  obtain ⟨Γ₁, Γ₂, A, j₁, j₂, hs, hM, hN⟩ := der_then h _ _ _ rfl
  obtain ⟨T, hT⟩ := fv_live hM 1 (by simp [Expr.HasVar, Expr.val, Val.unit])
  obtain ⟨T', hT'⟩ := fv_live hN 2 (by simp [Expr.HasVar])
  exact ⟨T, splitP_le_left hs _ _ hT, splitP_both hs hT (by simpa using hT')⟩

/-- **`withborU d` typed as a λ** at `A ⊸ D`: `A` is persistent. -/
theorem wb_generic {Δ : LifeCtx} {Γ : Ctx VTy} {d : Expr} {A : VTy} {j : Jdg}
    (h : CDerives Δ (⟨A, true⟩ :: Γ) (.lam (wbInner d)) j) : A.Persistent := by
  have key : ∀ (s : Slot VTy) Δ' j', CDerives Δ' (s :: ⟨A, true⟩ :: Γ) (wbInner d) j' →
      A.Persistent := by
    intro s Δ' j' h'
    obtain ⟨T, hT, hp⟩ := then_src h'
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Slot.mk.injEq, and_true] at hT
    subst hT; exact hp
  rcases der_lam h _ rfl with ⟨A', D, hM, -⟩ | ⟨S, B, hM, -⟩ | ⟨x, b, Δ', S, C, hM, -⟩ |
    ⟨A', hM, -⟩ | ⟨M₁, M₂, hw⟩ | hx
  · exact key _ _ _ hM
  · exact key _ _ _ hM
  · exact key _ _ _ hM
  · exact key _ _ _ hM
  · simp [withPair, wbInner, thenE, Expr.val, Val.lam] at hw
  · rcases hx with ⟨he, -⟩ | ⟨d', he, -⟩ | ⟨ho, -⟩
    · simp [forget, wbInner, thenE, Expr.val, Val.lam, unit'] at he
    · simp [withborUE, wbInner, thenE, Expr.val, Val.lam] at he
    · simp only [wbInner] at ho; not_other ho

/-- **`withborU d`, read at a thunk of `A ⊸ C`** (at a value or at a row over it): as a λ, `A` is
persistent; as an unwinding constant, `A` is its source and `C` takes a callback whose argument is
a borrow. -/
theorem wb_view {Δ : LifeCtx} {Γ : Ctx VTy} {d : Expr} {j : Jdg} {T : VTy} {A : VTy} {C : CTy}
    (h : CDerives Δ Γ (withborUE d) j) (hj : j = .val T ∨ ∃ S, j = .comp (CTy.effOf S T))
    (hv : VView T (.thunk (.arr A C))) :
    A.Persistent ∨ ∃ x bnd L B S R, C = .arr (cbUTy x bnd L B S) (CTy.effOf S R) ∧
      L.persistent = false := by
  have hcls : ∀ D', Rigid D' → LamCls Γ D' j → D' = .arr A C := by
    intro D' hD hcl
    rcases hcl with rfl | hc | ⟨-, hc⟩
    · rcases hj with h' | ⟨S, h'⟩
      · cases h'
      · cases h'; exact (hD.1 _ _ rfl).elim
    · exact vview_thunk ((hc.at hj).trans hv)
    · exact vview_bang_thunk ((hc.at hj).trans hv)
  rcases der_lam h _ rfl with ⟨A', D, hM, hcl⟩ | ⟨S, B, hM, hcl⟩ | ⟨x, b, Δ', S, C', hM, hcl⟩ |
    ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hw⟩ | hx
  · have := hcls _ (rigid_arr _ _) hcl
    simp only [CTy.arr.injEq] at this
    obtain ⟨rfl, -⟩ := this
    exact .inl (wb_generic hM)
  · have := hcls _ (rigid_arr _ _) hcl
    simp only [CTy.arr.injEq] at this
    obtain ⟨rfl, -⟩ := this
    exact .inl rfl
  · have := hcls _ (rigid_all _ _ _) hcl; cases this
  · rcases hcl with hc | ⟨-, hc⟩
    · have := vview_thunk ((hc.at hj).trans hv); cases this
    · have := vview_bang_thunk ((hc.at hj).trans hv); cases this
  · simp [withPair, Expr.val, Val.lam] at hw
  · rcases hx with ⟨he, -⟩ | ⟨d', -, T₀, ⟨src, x, bnd, L, B, S, R, rfl, hL⟩, hc⟩ | ⟨ho, -⟩
    · simp [forget, Expr.val, Val.lam, unit'] at he
    · have := vview_thunk ((hc.at hj).trans hv)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact .inr ⟨x, bnd, L, B, S, R, rfl, hL⟩
    · not_other ho

/-- AT05's callback `Λ. λm. (m, m)`. -/
abbrev at05F : Expr := .lam (.lam (.pair (.var 0) (.var 0)))

/-- What AT05's innermost term knows of its context: the cell's slot (index `2`) is at a view of a
`Ref`; the slot of `w` (index `0`), when `w` is a variable, is at a type `withborU dFlag` is read at;
the slot of `f` (index `1`), when `f` is a variable, at a type the callback is read at. -/
structure At05Ctx (Γ : Ctx VTy) (W F : Expr) : Prop where
  c : ∀ T, Γ[2]? = some ⟨T, true⟩ → ∃ A, VView (.ref A) T
  w : W = .var 0 ∨ W = withborUE dFlag
  wt : W = .var 0 → ∀ T, Γ[0]? = some ⟨T, true⟩ →
    ∃ Δ Γ' S, CDerives Δ Γ' (withborUE dFlag) (.comp (CTy.effOf S T))
  f : F = .var 1 ∨ F = at05F
  ft : F = .var 1 → ∀ T, Γ[1]? = some ⟨T, true⟩ →
    ∃ Δ Γ' S, CDerives Δ Γ' at05F (.comp (CTy.effOf S T))

theorem At05Ctx.le {Γ Γ' : Ctx VTy} {W F : Expr} (h : At05Ctx Γ W F) (hle : CtxLe Γ' Γ) :
    At05Ctx Γ' W F :=
  ⟨fun T hT => h.c T (hle _ _ hT), h.w, fun hW T hT => h.wt hW T (hle _ _ hT), h.f,
    fun hF T hT => h.ft hF T (hle _ _ hT)⟩

/-- A view of a `Ref` is not persistent. -/
theorem vview_ref_np {A T : VTy} (h : VView (.ref A) T) : T.persistent = false := by
  have hh := h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
  rw [hh.persistent]; rfl

/-- A view of a `Ref` is no thunk. -/
theorem vview_ref_thunk {A : VTy} {C : CTy} (h : VView (.ref A) (.thunk C)) : False := by
  have := (h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)).eq_self
    (fun _ _ h => by cases h) (fun _ h => by cases h)
  cases this

/-- **`w c`, the source applied** (`W` the variable `w` or `withborU dFlag` itself): read only at
`cb ⊸ F_Σ R`, `cb` an unwinding callback type whose argument is a borrow.  As a λ, `withborU dFlag`
takes a persistent source and the cell is a `Ref`. -/
theorem at05_M {Δ : LifeCtx} {Γ : Ctx VTy} {W F : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app W (.var 2)) j) (hc : At05Ctx Γ W F) :
    ∃ x bnd L B S R, L.persistent = false ∧
      j = .comp (.arr (cbUTy x bnd L B S) (CTy.effOf S R)) := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i, A, C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, Γ₁, Γ₂, A, S, C, hN, hs, hY, hU, rfl⟩ | ⟨N, b, C, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · -- `⊸E`: the source at `A`, a view of the cell's `Ref`; `W` at `A ⊸ B`
    obtain ⟨T, hT, hcT⟩ := der_var hY 2 rfl
    obtain ⟨A₀, hv⟩ := hc.c T (splitP_le_left hs _ _ hT)
    have hAp := vview_ref_np (hv.trans hcT.val)
    rcases hc.w with rfl | rfl
    · obtain ⟨T_w, hTw, hcw⟩ := der_var hf 0 rfl
      obtain ⟨Δ', Γ', S', hW⟩ := hc.wt rfl T_w (splitP_le_right hs _ _ hTw)
      rcases wb_view hW (.inr ⟨S', rfl⟩) hcw.val with hp | ⟨_, _, _, _, _, _, he, _⟩
      · simp [VTy.Persistent, hAp] at hp
      · cases he
    · rcases wb_view hf (.inl rfl) .refl with hp | ⟨_, _, _, _, _, _, he, _⟩
      · simp [VTy.Persistent, hAp] at hp
      · cases he
  · -- `[app]`: the source at the cell's slot's type
    cases hi
    obtain ⟨A₀, hv⟩ := hc.c A (splitP_le_right hs _ _ (soloP_le hx))
    have hAp := vview_ref_np hv
    rcases hc.w with rfl | rfl
    · obtain ⟨T_w, hTw, hcw⟩ := der_var hf 0 rfl
      rcases hcw with ⟨S', Y, he, -⟩ | ⟨C_w, rfl, hCw, hr'⟩
      · exact (effOf_ne_arr _ _ _ _ he.symm).elim
      · obtain rfl : C_w = .arr A C := by
          rcases rigid_or_ampNu hCw with hR | hN
          · have := hr'.rigid hR; cases this; rfl
          · obtain ⟨D', he, hD'⟩ := hr'.ampNu hN
            cases he
            rcases hD' with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> cases h'
        obtain ⟨Δ', Γ', S', hW⟩ := hc.wt rfl _ (splitP_le_left hs _ _ hTw)
        rcases wb_view hW (.inr ⟨S', rfl⟩) .refl with hp | ⟨x, bnd, L, B, S'', R, rfl, hL⟩
        · simp [VTy.Persistent, hAp] at hp
        · have := hr.rigid (rigid_arr _ _)
          exact ⟨x, bnd, L, B, S'', R, hL, this⟩
    · rcases der_lam hf _ rfl with ⟨A', D, hM, hcl⟩ | ⟨S', B', hM, hcl⟩ |
        ⟨x, b, Δ', S', C', hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hw⟩ | hx'
      · have := hcl.comp_rigid (rigid_arr _ _)
        simp only [CTy.arr.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        have := wb_generic hM
        simp [VTy.Persistent, hAp] at this
      · have := hcl.comp_rigid (rigid_arr _ _)
        simp only [CTy.arr.injEq] at this
        obtain ⟨rfl, -⟩ := this
        simp [VTy.persistent] at hAp
      · have := hcl.comp_rigid (rigid_arr _ _); cases this
      · rcases hcl with hcl | ⟨-, hcl⟩
        · obtain ⟨S'', Y, he, -⟩ := hcl; exact (effOf_ne_arr _ _ _ _ he.symm).elim
        · obtain ⟨S'', Y, he, -⟩ := hcl; exact (effOf_ne_arr _ _ _ _ he.symm).elim
      · simp [withPair, Expr.val, Val.lam] at hw
      · have := hx'.not_comp; simp [CTy.isRet] at this
  · -- `[let]`: `W` is `withborU dFlag` itself, its source at a row over `A`
    rcases hc.w with rfl | rfl
    · cases hN
    · simp only [withborUE, Expr.val, Val.lam, Expr.lam.injEq] at hN
      subst hN
      obtain ⟨T, hT, hcT⟩ := der_var hY 2 rfl
      obtain ⟨A₀, hv⟩ := hc.c T (splitP_le_left hs _ _ hT)
      rcases hcT with ⟨S'', Y, he, hY'⟩ | ⟨C', rfl, -, -⟩
      · obtain ⟨-, rfl⟩ := Inst.effOf_inj he
        have hAp := vview_ref_np (hv.trans hY')
        have := wb_generic (d := dFlag) hU
        simp [VTy.Persistent, hAp] at this
      · exact (vview_ref_thunk hv).elim
  · cases hb
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hc.w with rfl | rfl <;>
      rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> simp [withborUE, Expr.val, Val.lam] at hX

/-- **The callback is read at no unwinding callback type**: under `∀'x`, `λm. (m, m)` at `L ⊸ …` uses
`m` on both sides of a split, so `L` is persistent, while it is a borrow. -/
theorem not_at05F_cb {Δ : LifeCtx} {Γ : Ctx VTy} {S S' : Row} {x : BoCa.Lifetime.LifeVar}
    {bnd : Lifetime.Life} {L B : VTy} (hL : L.persistent = false)
    (h : CDerives Δ Γ at05F (.comp (CTy.effOf S (cbUTy x bnd L B S')))) : False := by
  have hcb : ∀ D, Rigid D → LamCls Γ D (.comp (CTy.effOf S (cbUTy x bnd L B S'))) →
      D = .all x bnd (.arr L (CTy.effOf S' (.box (.var x) B))) := by
    intro D hD hcl
    rcases hcl with he | hcl | ⟨-, hcl⟩
    · cases he; exact (hD.1 _ _ rfl).elim
    · exact vview_thunk (hcl.at (.inr ⟨S, rfl⟩))
    · exact vview_bang_thunk (hcl.at (.inr ⟨S, rfl⟩))
  rcases der_lam h _ rfl with ⟨A', D, hM, hcl⟩ | ⟨S₀, B₀, hM, hcl⟩ |
    ⟨x', b', Δ', S₀, C', hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hw⟩ | hx
  · have := hcb _ (rigid_arr _ _) hcl; cases this
  · have := hcb _ (rigid_arr _ _) hcl; cases this
  · have := hcb _ (rigid_all _ _ _) hcl
    simp only [CTy.all.injEq] at this
    obtain ⟨-, -, rfl⟩ := this
    -- the inner λ, `λm. (m, m)`, at `L ⊸ …`
    rcases der_lam hM _ rfl with ⟨A'', D'', hM', hcl'⟩ | ⟨S₁, B₁, hM', hcl'⟩ |
      ⟨_, _, _, _, _, _, hcl'⟩ | ⟨_, _, hcl'⟩ | ⟨M₁, M₂, hw⟩ | hx'
    · have := hcl'.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rcases der_pair hM' _ _ rfl with ⟨Γ₁, Γ₂, A₁, A₂, hs, h₁, h₂, -⟩ | he
      · obtain ⟨T₁, hT₁, -⟩ := der_var h₁ 0 rfl
        obtain ⟨T₂, hT₂, -⟩ := der_var h₂ 0 rfl
        have hp := splitP_both hs hT₁ hT₂
        have := splitP_le_left hs 0 T₁ hT₁
        simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at this
        subst this
        simp [VTy.Persistent, hL] at hp
      · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
    · have := hcl'.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      simp [VTy.persistent] at hL
    · have := hcl'.comp_rigid (rigid_arr _ _); cases this
    · rcases hcl' with hcl' | ⟨-, hcl'⟩
      · obtain ⟨S'', Y, he, -⟩ := hcl'; exact effOf_ne_arr _ _ _ _ he.symm
      · obtain ⟨S'', Y, he, -⟩ := hcl'; exact effOf_ne_arr _ _ _ _ he.symm
    · simp [withPair, Expr.val, Val.lam] at hw
    · have := hx'.not_comp; simp [CTy.isRet] at this
  · rcases hcl with hcl | ⟨-, hcl⟩
    · have := vview_thunk (hcl.at (.inr ⟨S, rfl⟩)); cases this
    · have := vview_bang_thunk (hcl.at (.inr ⟨S, rfl⟩)); cases this
  · simp [withPair, Expr.val, Val.lam] at hw
  · rcases hx with ⟨he, -⟩ | ⟨d, he, -⟩ | ⟨ho, -⟩
    · simp [forget, Expr.val, Val.lam, unit'] at he
    · simp [withborUE, Expr.val, Val.lam, thenE] at he
    · not_other ho

/-- **`w c f` has no derivation**: `w c` is read only at `cb ⊸ F_Σ R` (`at05_M`), so `f`'s slot is
`cb`, at which the callback is read at no type (`not_at05F_cb`). -/
theorem at05_core {Δ : LifeCtx} {Γ : Ctx VTy} {W F : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app (.app W (.var 2)) F) j) (hc : At05Ctx Γ W F) : False := by
  obtain ⟨j₀, hb, -⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, -, hM, -⟩ | ⟨Γ₁, Γ₂, i, A, C, hi, hs, hM, hx, -⟩ |
    ⟨N, -, -, -, -, -, hN, -⟩ | ⟨N, b, C, hN, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := at05_M hM (hc.le (splitP_le_right hs))
    cases he
  · obtain ⟨x, bnd, L, B, S, R, hL, he⟩ := at05_M hM (hc.le (splitP_le_left hs))
    simp only [Jdg.comp.injEq, CTy.arr.injEq] at he
    obtain ⟨rfl, -⟩ := he
    rcases hc.f with rfl | rfl
    · cases hi
      obtain ⟨Δ', Γ', S', hf⟩ := hc.ft rfl _ (splitP_le_right hs _ _ (soloP_le hx))
      exact not_at05F_cb hL hf
    · cases hi
  · cases hN
  · cases hN
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.w with rfl | rfl <;>
      rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> simp [withborUE, Expr.val, Val.lam] at hX

/-- AT05's innermost term: `(c, r) ← w c f; (free c, r)`. -/
abbrev at05N₃ (W F : Expr) : Expr :=
  .app (.lam (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))) (.app (.app W (.var 2)) F)

theorem at05_eq : at05 = bindE (.app alloc' (.inj₁ unit'))
    (bindE at05F (bindE (withborUE dFlag) (at05N₃ (.var 0) (.var 1)))) := rfl

/-- **AT05 has no derivation**: through its three bindings (the cell, the callback, `withborU dFlag`,
each possibly the polymorphic let), `w c f` is typed in a context `At05Ctx` describes, and has no
derivation there (`at05_core`). -/
theorem not_der_at05 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at05 j := by
  intro h
  rw [at05_eq] at h
  -- `c ← alloc (inj₁ ())`
  obtain ⟨Γ₁, Γ', T_c, b_c, S, j₁, -, -, hA, hN₂⟩ := der_bind (M := .app alloc' (.inj₁ unit')) h
    (fun i h => by cases h) (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨A₀, hvc⟩ := alloc_row hA
  have hc0 : ∀ T, (⟨T_c, b_c⟩ :: Γ')[0]? = some ⟨T, true⟩ → ∃ A, VView (.ref A) T := by
    intro T hT
    simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT
    obtain ⟨rfl, -⟩ := hT
    exact ⟨A₀, hvc⟩
  -- `f ← Λ. λm. (m, m)`
  obtain ⟨Γ₂, j₂, F, hF, hF', hc1, hN₃⟩ : ∃ Γ₂ j₂ F, (F = .var 1 ∨ F = at05F) ∧
      (F = .var 1 → ∀ T, Γ₂[0]? = some ⟨T, true⟩ →
        ∃ Δ Γ' S, CDerives Δ Γ' at05F (.comp (CTy.effOf S T))) ∧
      (∀ T, Γ₂[1]? = some ⟨T, true⟩ → ∃ A, VView (.ref A) T) ∧
      CDerives Δ Γ₂ (bindE (withborUE dFlag) (at05N₃ (.var 0) F)) j₂ := by
    rcases der_bindLam (N := bindE (withborUE dFlag) (at05N₃ (.var 0) (.var 1)))
        (b := .lam (.pair (.var 0) (.var 0))) hN₂ (by not_withPair) (by not_const) with
      ⟨Γf, Γ₂', T_f, b_f, S_f, j', -, hle₂, hf, hN⟩ | ⟨j', hN⟩
    · refine ⟨_, _, .var 1, .inl rfl, fun _ T hT => ?_, fun T hT => ?_, hN⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT
        obtain ⟨rfl, -⟩ := hT
        exact ⟨_, _, _, hf⟩
      · exact hc0 T (hle₂ 0 T (by simpa using hT))
    · refine ⟨⟨.unit, false⟩ :: ⟨T_c, b_c⟩ :: Γ', j', at05F, .inr rfl, (fun h => by cases h),
        (fun T hT => hc0 T (by simpa using hT)), ?_⟩
      have e : ((bindE (withborUE dFlag) (at05N₃ (.var 0) (.var 1))).subst 0
          (Val.lam (.lam (.pair (.var 0) (.var 0))))).shift 1 0 =
          bindE (withborUE dFlag) (at05N₃ (.var 0) at05F) := by rfl
      rw [e] at hN
      exact hN
  -- `w ← withborU dFlag`
  obtain ⟨Γ₃, j₃, W, hctx, hN₄⟩ : ∃ Γ₃ j₃ W, At05Ctx Γ₃ W F ∧ CDerives Δ Γ₃ (at05N₃ W F) j₃ := by
    rcases der_bindLam (N := at05N₃ (.var 0) F) (b := .lam (wbInner dFlag)) hN₃ (by not_withPair)
        (by not_const) with
      ⟨Γw, Γ₃', T_w, b_w, S_w, j', -, hle₃, hw, hN⟩ | ⟨j', hN⟩
    · refine ⟨_, _, .var 0, ⟨fun T hT => ?_, .inl rfl, fun _ T hT => ?_, hF, fun hF1 T hT => ?_⟩,
        hN⟩
      · exact hc1 T (hle₃ 1 T (by simpa using hT))
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT
        obtain ⟨rfl, -⟩ := hT
        exact ⟨_, _, _, hw⟩
      · exact hF' hF1 T (hle₃ 0 T (by simpa using hT))
    · refine ⟨⟨.unit, false⟩ :: Γ₂, j', withborUE dFlag, ⟨(fun T hT => hc1 T (by simpa using hT)),
        .inr rfl,
        (fun h => by cases h), hF, (fun hF1 T hT => hF' hF1 T (by simpa using hT))⟩, ?_⟩
      have e : ((at05N₃ (.var 0) F).subst 0 (Val.lam (.lam (wbInner dFlag)))).shift 1 0 =
          at05N₃ (withborUE dFlag) F := by
        rcases hF with rfl | rfl <;> rfl
      rw [e] at hN
      exact hN
  -- `(c, r) ← w c f; …`
  obtain ⟨Γ₄, _, _, _, _, _, hle₄, _, hY, _⟩ := der_bind hN₄ (fun i h => by cases h)
    (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (by not_withPair) (by not_const)
  exact at05_core hY (hctx.le hle₄)

/-! ### `Rejects` at Core's kernel -/

/-- A closed program at tier 1 is a Core derivation at the empty context. -/
theorem tier1_closed {e : Expr} {C : CTy} (h : tier1.closed e C) :
    CDerives LifeCtx.empty [] e (.comp C) :=
  h (fun _ => []) (fun _ _ h => absurd h List.not_mem_nil)

/-- **The rejections at Core's kernel**: AT05, AT06, AT08 and AT13 have no type at all. -/
theorem rejects_tier1 : Rejects tier1 :=
  ⟨fun _ h => not_der_at05 (tier1_closed h), fun _ h => not_der_at06 (tier1_closed h),
    fun _ h => not_der_at08 (tier1_closed h), fun _ h => not_der_at13 (tier1_closed h)⟩

end Targets.Rej
