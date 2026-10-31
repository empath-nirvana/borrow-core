import Core.Closed
import Core.EffExamples

/-!
# Core — inversions of `CDerives`  `[spec §19]`

What a derivation of a term of a given shape must be.  Each inversion is one induction on the
derivation, which carries a *class* of judgements through the rules that conclude with their
premise's term (`JS`, `JR`) and tells every other rule apart by its conclusion's term.

**The same-term rules.**  The value rules `!E`, `[]I`, `[]E`, `⊑` at `Imm` and `Mut`, `μ`'s `roll`
and `unroll`; `return`, its reading back (`ofRet`), `[sub]` and `ν`'s two rules; and, at a λ-value,
the two thunk rules conclude with their premise's term.  So:

* a value read at a type `T` is read at the views of `T` and at rows over them (`ValCls`): `!`,
  `[]`, `⊑` and `μ` change the type, `ν` and `[sub]` only the row;
* a computation type that is no row's, no `&` and no `ν` (`Rigid`: `⊸`, `∀`, `⊤`) is left by no
  same-term rule (`JR.rigid`), since `ν`'s rules are at `&`-trees only (`CTy.NuOk`); an `&` is
  read at itself and at the `ν`s that unroll to it (`JR.amp`).

**Views keep the head** (`VView.hnf`).  A view of `T` has `T`'s head (`Hnf`: boxes stripped, `μ`
unrolled), unless that head is `!` (dereliction reaches its content), `Imm` or `Mut` (`⊑` changes
the lifetime).  Persistence is a property of the head (`Hnf.persistent`).

**The inversions.**  A variable is read at a view of its live slot's type (`der_var`); a pair at the
views of a tensor of its parts' types (`der_pair`); `inj₁ a` at the views of a sum, `a` typed in the
same context (`der_inj₁`); `()` at `1`'s views over a consumed context, or at `⊤` (`der_unit`); an
application by `⊸E`, `[app]`, `[let]`, `[let-poly]`, `∀E` or a projection (`der_app`); a λ-value
through the rule that types its body, or as one of the λ-constants at its axiom's type
(`der_lam`); `let (x, y)`, `;`, `then` and `handle` by their own rules (`der_letpair`, `der_seq`,
`der_then`, `der_hnd`; a handler's clause tuple at `clausesTyO`, `κ` bare by `[handle]` or boxed by
BOXED-κ, §28); `alloc` at `A ⊸ Ref A`; a primitive by its own rule only, and `load` has
none (`der_prim`); `swap` at `Ref A ⊸ B ⊸ Ref B ⊗ A` only, since its body loads its cell
(`der_swap`).  Every free variable of a typed term has a live slot (`fv_live`), so a variable used
on both sides of a split is persistent (`splitP_both`).

**The rows a computation is read at.**  `[handle]`, `[then]`, `[perform]`, `[raise]`, `[let]` and
`bind` are read with their premises at the judgement each concludes with, and the same-term rules'
path from there (`der_hndJ`, `der_thenJ`, `der_performJ`, `der_raiseJ`, `der_letJ`); those rules
only grow rows (`JR.rowLe`).  `κ`'s cancel branch, applied, is read at what they reach from its
type (`kappa_cancel_jr` at an unrestricted `κ`, `kcancel_jr_cancellable` at a cancellable one), and
at a row only when its cancel row is no `⊤` and below the row (`cancelTy_rowLe`).

**A continuation is used once.**  At a resuming must-resume or cancellable operation, a clause's `κ`
is at `kTy`, a thunk of an `&`, which is not persistent (`kTy_not_persistent`): a live slot of it is
neither dropped by a consumed context nor read on both sides of a split, and a must-resume `κ`'s
cancel is at `⊤` only (`der_cancel_lin`).  So no clause that drops `κ` (R1), resumes it twice (R2),
or cancels and then resumes it (R4) is typed at its clause type, and at a must-resume operation no
clause that cancels it (R3) (`refuses_R_clauses`).  The refusals are of `κ`'s use: at the same
clause types a clause that resumes `κ` once is typed, and a clause that cancels `κ` is typed at a
cancellable operation and refused at a must-resume one (`clauseRefusals_pinned`).  At an
unrestricted operation `κ` is `!`, and none of this applies.

**Cost** (`CLAUDE.md`, *Do not invert `CDerives` casually*).  A rule added to `CDerives` adds a case
to each inversion.  The case is closed by the rule's conclusion's term (`cd_terms`), unless the rule
concludes with its premise's term: then it is a step of `JS`, and each inversion that carries a
class takes it as an explicit case.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Inversions
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)
open BoCa.Programs (alloc' free')

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

/-- **Views keep the head**, unless the head is `!` (whose content is then viewed), `Imm` or
`Mut`. -/
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
back (`ofRet`), `[sub]` with its order on rows, and `ν`'s two rules (at an `&`-tree,
`CTy.NuOk`). -/
inductive JS : Jdg → Jdg → Prop
  | val {A B : VTy} : VS A B → JS (.val A) (.val B)
  | ret (A : VTy) : JS (.val A) (.comp (.ret A))
  | ofRet (A : VTy) : JS (.comp (.ret A)) (.val A)
  | effSub (S S' : Row) (A : VTy) : RowLe S S' → JS (.comp (CTy.effOf S A)) (.comp (CTy.effOf S' A))
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

theorem effOf_ne_nu (S : Row) (Y : VTy) (C : CTy) : CTy.effOf S Y ≠ .nu C := by
  cases S <;> simp [CTy.effOf]

theorem effOf_ne_amp (S : Row) (Y : VTy) (C D : CTy) : CTy.effOf S Y ≠ .amp C D := by
  cases S <;> simp [CTy.effOf]

/-- A row's type is a returner. -/
theorem effOf_isRet (S : Row) (Y : VTy) : (CTy.effOf S Y).isRet = true := by
  cases S <;> rfl

/-- A row's type determines the row and the answer. -/
theorem effOf_inj : ∀ {S S' : Row} {Y Y' : VTy}, CTy.effOf S Y = CTy.effOf S' Y' → S = S' ∧ Y = Y'
  | [], [], _, _, h => by simp only [CTy.effOf, CTy.ret.injEq] at h; exact ⟨rfl, h⟩
  | [], _ :: _, _, _, h => by simp [CTy.effOf] at h
  | _ :: _, [], _, _, h => by simp [CTy.effOf] at h
  | o :: S, o' :: S', _, _, h => by
      simp only [CTy.effOf, CTy.eff.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h8, h7⟩ := h
      obtain ⟨rfl, rfl⟩ := effOf_inj h7
      cases o; cases o'
      simp_all

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
      obtain ⟨-, rfl⟩ := effOf_inj (S := []) he
      exact hY
  | effSub S S' A _ =>
      obtain ⟨S₀, Y, he, hY⟩ := h
      obtain ⟨-, rfl⟩ := effOf_inj he
      exact ⟨S', _, rfl, hY⟩
  | nuIn C hC =>
      obtain ⟨S, Y, he, -⟩ := h
      obtain ⟨C₁, C₂, hu⟩ := unroll_amp hC
      exact absurd (hu.symm.trans he) (effOf_ne_amp S Y C₁ C₂).symm
  | nuOut C hC =>
      obtain ⟨S, Y, he, -⟩ := h
      exact absurd he.symm (effOf_ne_nu S Y C)

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
  | effSub S S' A _ => exact he S A rfl
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
        | effSub S S' A _ => exact absurd rfl (hD' S A)
        | nuIn C hC =>
            refine ⟨_, rfl, fun S A h => effOf_ne_nu S A C h.symm⟩
        | nuOut C hC =>
            obtain ⟨C₁, C₂, hu⟩ := unroll_amp hC
            refine ⟨_, rfl, fun S A h => ?_⟩
            rw [hu] at h
            exact effOf_ne_amp S A C₁ C₂ h.symm

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
      | effSub S S' A _ =>
          rcases hD' with ⟨_, _, h⟩ | ⟨_, h⟩
          · exact absurd h (effOf_ne_amp _ _ _ _)
          · exact absurd h (effOf_ne_nu _ _ _)
      | nuIn C hC => exact ⟨_, rfl, .inr ⟨C, rfl⟩⟩
      | nuOut C hC => exact ⟨_, rfl, .inl (unroll_amp hC)⟩

/-- The judgements an `&` is read at: itself, and the `ν`s that unroll to it. -/
def AmpCls (C₁ C₂ : CTy) (j : Jdg) : Prop :=
  j = .comp (.amp C₁ C₂) ∨ ∃ C, j = .comp (.nu C) ∧ C.unroll = .amp C₁ C₂

theorem AmpCls.step {C₁ C₂ : CTy} {j j' : Jdg} (hs : JS j j') (h : AmpCls C₁ C₂ j) :
    AmpCls C₁ C₂ j' := by
  cases hs with
  | val hv => rcases h with h | ⟨_, h, -⟩ <;> cases h
  | ret A => rcases h with h | ⟨_, h, -⟩ <;> cases h
  | ofRet A => rcases h with h | ⟨_, h, -⟩ <;> cases h
  | effSub S S' A _ =>
      rcases h with h | ⟨_, h, -⟩ <;> simp only [Jdg.comp.injEq] at h
      · exact absurd h (effOf_ne_amp _ _ _ _)
      · exact absurd h (effOf_ne_nu _ _ _)
  | nuIn C hC =>
      rcases h with h | ⟨C', h, -⟩ <;> simp only [Jdg.comp.injEq] at h
      · exact .inr ⟨C, rfl, h⟩
      · obtain ⟨D₁, D₂, hu⟩ := unroll_amp hC
        rw [hu] at h; cases h
  | nuOut C hC =>
      rcases h with h | ⟨C', h, hC'⟩ <;> simp only [Jdg.comp.injEq] at h
      · cases h
      · cases h; exact .inl (by rw [hC'])

/-- **An `&` is read at itself and at the `ν`s that unroll to it.** -/
theorem JR.amp {C₁ C₂ : CTy} {j : Jdg} (hr : JR (.comp (.amp C₁ C₂)) j) : AmpCls C₁ C₂ j := by
  induction hr with
  | refl => exact .inl rfl
  | tail _ hs ih => exact ih.step hs

/-- An `&` read at an `&` is read at itself. -/
theorem JR.amp_amp {C₁ C₂ D₁ D₂ : CTy} (hr : JR (.comp (.amp C₁ C₂)) (.comp (.amp D₁ D₂))) :
    D₁ = C₁ ∧ D₂ = C₂ := by
  rcases hr.amp with h | ⟨_, h, -⟩
  · simp only [Jdg.comp.injEq, CTy.amp.injEq] at h; exact h
  · cases h

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

theorem CtxLe.cons_same {Γ' Γ : Ctx VTy} (h : CtxLe Γ' Γ) (s : Slot VTy) :
    CtxLe (s :: Γ') (s :: Γ) :=
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
    ∀ {k : Nat} {T T' : VTy}, Γ₁[k]? = some ⟨T, true⟩ → Γ₂[k]? = some ⟨T', true⟩ →
      T.Persistent := by
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
theorem banged_slot {Γ : Ctx VTy} (hp : Ctx.Banged Γ) {k : Nat} {T : VTy}
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

/-- The variable of `SoloP` is a live slot at its type. -/
theorem soloP_le {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    Γ[i]? = some ⟨A, true⟩ := by
  induction h with
  | here _ => rfl
  | there _ ih => simpa using ih
  | skip _ _ ih => simpa using ih

/-! ### Every free variable of a typed term has a live slot -/

/-- `force e` is `e`, or `e ()` at a returner. -/
theorem forceE_cases (C : CTy) (e : Expr) :
    forceE C e = e ∨ forceE C e = .app e (.val .unit) := by
  cases C <;> simp [forceE]

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

/-- A variable of a shifted term past the shift's cutoff is one of the term's. -/
theorem hasVar_shift_inv (d : Nat) : ∀ (e : Expr) (c k : Nat), c ≤ k →
    (e.shift d c).HasVar (k + d) → e.HasVar k
  | .var i, c, k, hck, h => by
      simp only [Expr.shift] at h
      split at h <;> simp only [Expr.HasVar] at h ⊢ <;> omega
  | .pair a b, c, k, hck, h | .seq a b, c, k, hck, h | .app a b, c, k, hck, h => by
      simp only [Expr.shift, Expr.HasVar] at h ⊢
      exact h.imp (hasVar_shift_inv d a c k hck) (hasVar_shift_inv d b c k hck)
  | .inj₁ a, c, k, hck, h | .inj₂ a, c, k, hck, h => hasVar_shift_inv d a c k hck h
  | .lam b, c, k, hck, h => by
      simp only [Expr.shift, Expr.HasVar] at h ⊢
      exact hasVar_shift_inv d b (c + 1) (k + 1) (by omega) (by rwa [show k + 1 + d = k + d + 1 by omega])
  | .letpair a b, c, k, hck, h => by
      simp only [Expr.shift, Expr.HasVar] at h ⊢
      exact h.imp (hasVar_shift_inv d a c k hck)
        (fun h => hasVar_shift_inv d b (c + 2) (k + 2) (by omega) (by rwa [show k + 2 + d = k + d + 2 by omega]))
  | .case a b₁ b₂, c, k, hck, h => by
      simp only [Expr.shift, Expr.HasVar] at h ⊢
      exact h.imp (hasVar_shift_inv d a c k hck) (Or.imp
        (fun h => hasVar_shift_inv d b₁ (c + 1) (k + 1) (by omega) (by rwa [show k + 1 + d = k + d + 1 by omega]))
        (fun h => hasVar_shift_inv d b₂ (c + 1) (k + 1) (by omega) (by rwa [show k + 1 + d = k + d + 1 by omega])))
  | .unit, _, _, _, h | .loc _, _, _, _, h | .prim _, _, _, _, h => h.elim

theorem hasVar_pickE : ∀ (j : Nat) {t : Expr} {k : Nat}, (pickE j t).HasVar k → t.HasVar k
  | 0, t, k, h => by
      simp only [pickE, Expr.HasVar] at h
      exact h.resolve_right (by omega)
  | j + 1, t, k, h => by
      simp only [pickE, Expr.HasVar] at h
      exact h.resolve_right fun h' => by have := hasVar_pickE j h'; simp [Expr.HasVar] at this

/-- A variable of the clauses written out from `Hc` is one of `Hc`'s. -/
theorem hasVar_tailTuple {Hc : Expr} : ∀ (E : List (Qual × VTy × VTy)) (j k : Nat),
    (tailTuple E j Hc).HasVar k → Hc.HasVar k
  | [], _, _, h => by simp [tailTuple, Expr.HasVar, Val.unit] at h
  | (q, A, B) :: E, j, k, h => by
      simp only [tailTuple, Expr.HasVar] at h
      rcases h with h | h
      · unfold tailClause at h
        split at h
        · simp only [Expr.HasVar] at h
          rcases h with h | h
          · exact hasVar_shift_inv 1 Hc 0 k (Nat.zero_le _) (hasVar_pickE j h)
          · simp [Expr.HasVar] at h
        · simp only [Expr.HasVar, resumeB, Expr.val, Val.lam, Val.inj₁, Val.unit] at h
          rcases h with h | (h | h) | h | h
          · simp at h
          all_goals first
            | (simp at h)
            | exact hasVar_shift_inv 3 Hc 0 k (Nat.zero_le _)
                (by rw [show k + 3 = k + 1 + 2 by omega]; exact hasVar_pickE j h)
      · exact hasVar_tailTuple E (j + 1) k h

/-- A variable of the clauses written out from `Hw` and `Hn` is one of theirs. -/
theorem hasVar_lastTuple {Hw Hn : Expr} : ∀ (E : List (Qual × VTy × VTy)) (j k : Nat),
    (lastTuple E j Hw Hn).HasVar k → Hw.HasVar k ∨ Hn.HasVar k
  | [], _, _, h => by simp [lastTuple, Expr.HasVar, Val.unit] at h
  | (q, A, B) :: E, j, k, h => by
      simp only [lastTuple, Expr.HasVar] at h
      rcases h with h | h
      · unfold lastClause at h
        split at h
        · simp only [Expr.HasVar] at h
          rcases h with h | h
          · exact .inl (hasVar_shift_inv 1 Hw 0 k (Nat.zero_le _) (hasVar_pickE j h))
          · simp at h
        · simp only [Expr.HasVar, thenE, Expr.val, Val.lam, Val.prim, Val.inj₁, Val.inj₂,
            Val.unit] at h
          simp only [show k + 1 + 2 + 1 + 1 + 1 = k + 6 by omega,
            show k + 1 + 2 = k + 3 by omega] at h
          by_cases h₆ : (pickE j (Expr.shift 6 0 Hn)).HasVar (k + 6)
          · exact .inr (hasVar_shift_inv 6 Hn 0 k (Nat.zero_le _) (hasVar_pickE j h₆))
          · by_cases h₃ : (pickE j (Expr.shift 3 0 Hw)).HasVar (k + 3)
            · exact .inl (hasVar_shift_inv 3 Hw 0 k (Nat.zero_le _) (hasVar_pickE j h₃))
            · simp only [h₆, h₃] at h; exfalso; simp at h
      · exact hasVar_lastTuple E (j + 1) k h

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
      rcases forceE_cases C (.var i) with hf | hf <;> rw [hf] at hk <;>
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
  | effPerform _ _ _ _ ih | effRaise _ _ _ _ _ ih =>
      intro k hk
      simp only [BoCa.BoLo.performE, BoCa.BoLo.raiseE, opArgE, Expr.val, Val.prim, Val.i32,
        Expr.HasVar, false_or] at hk
      exact ih k hk
  | effThen hs _ _ _ _ _ _ _ _ _ _ _ ihM ihN ihD =>
      intro k hk
      simp only [thenE, Expr.val, Val.prim, Val.lam, Expr.HasVar, false_or] at hk
      rcases hk with (hk | hk) | hk
      · obtain ⟨T, hT⟩ := ihN (k + 1) hk; exact ⟨T, splitP_le_right hs k T (slot_succ hT)⟩
      · obtain ⟨T, hT⟩ := ihD (k + 1) hk; exact ⟨T, splitP_le_right hs k T (slot_succ hT)⟩
      · obtain ⟨T, hT⟩ := ihM k hk; exact ⟨T, splitP_le_left hs k T hT⟩
  | effHandleV hs _ _ _ _ _ _ _ _ ihc ihe | effHandleVB hs _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      intro k hk
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.HasVar, false_or] at hk
      rcases hk with (hk | hk) | hk
      · exact absurd hk (qualsVal_noVar _)
      · obtain ⟨T, hT⟩ := ihc k hk; exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ihe k hk; exact ⟨T, splitP_le_right hs k T hT⟩
  | effHandleT hs _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      intro k hk
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.HasVar, false_or] at hk
      rcases hk with (hk | hk | hk) | hk
      · exact absurd hk (qualsVal_noVar _)
      · obtain ⟨T, hT⟩ := ihc k (Or.inl hk); exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ihc k (Or.inr (hasVar_tailTuple _ 0 k hk))
        exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ihe k hk; exact ⟨T, splitP_le_right hs k T hT⟩
  | effHandleL hs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      intro k hk
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.HasVar, false_or] at hk
      rcases hk with (hk | hk | hk) | hk
      · exact absurd hk (qualsVal_noVar _)
      · obtain ⟨T, hT⟩ := ihc k (Or.inl hk); exact ⟨T, splitP_le_left hs k T hT⟩
      · rcases hasVar_lastTuple _ 0 k hk with hk' | hk'
        · obtain ⟨T, hT⟩ := ihc k (Or.inr (Or.inl hk')); exact ⟨T, splitP_le_left hs k T hT⟩
        · obtain ⟨T, hT⟩ := ihc k (Or.inr (Or.inr hk')); exact ⟨T, splitP_le_left hs k T hT⟩
      · obtain ⟨T, hT⟩ := ihe k hk; exact ⟨T, splitP_le_right hs k T hT⟩
  | divFuel => intro k hk; exact absurd hk (not_hasVar_closed divFuelV_closed)
  | reify _ _ _ _ _ hcl => intro k hk; exact absurd hk (not_hasVar_closed (reifyV_closed hcl))
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
  | foldOwnG => intro k hk; exact absurd hk (not_hasVar_closed (FoldP.foldOwnGV_closed _))
  | foldReuse => intro k hk; exact absurd hk (not_hasVar_closed (foldReuseV_closed _))
  | unfoldN => intro k hk; exact absurd hk (not_hasVar_closed (unfoldV_closed _))
  | _ => intro k hk; exact absurd hk (not_hasVar_closed (by rfl))

/-! ### Inversions -/

/-- The term constants of `CDerives`'s conclusions, unfolded to their head constructors, so that a
rule whose conclusion's term has another head is told apart. -/
macro "cd_terms" : tactic => `(tactic| (try simp_all [withPair, absurdE, copy, forget, swap,
    withbor, withload, withswap, sizeV, replaceV, arrLenV, copyV, forgetV, emptyFamV, swapV,
    Val.arr, withborUE, foldImmV, foldOwnV, FoldP.foldOwnGV, foldReuseV, unfoldV, divFuelV, reifyV, BoCa.BoLo.performE,
    BoCa.BoLo.raiseE, opArgE, awaitE, thenE, hndTerm, hndExpr, Expr.val, Val.lam, Val.prim, Val.unit,
    Val.i32, lam2, elet, unit', v0, v1, v2, v3, load', store', mintE, burnE]))

/-- `force x` is `x` or `x ()`. -/
theorem forceE_var {C : CTy} {i : Nat} {e : Expr} (h : forceE C (.var i) = e) :
    e = .var i ∨ e = .app (.var i) .unit := by
  rcases forceE_cases C (.var i) with hf | hf <;> rw [hf] at h <;> subst h
  · exact .inl rfl
  · exact .inr rfl

/-- The same, at one hypothesis alone. -/
macro "cd_at " h:ident : tactic => `(tactic| (simp [withPair, absurdE, copy, forget, swap,
    withbor, withload, withswap, sizeV, replaceV, arrLenV, copyV, forgetV, emptyFamV, swapV,
    Val.arr, withborUE, foldImmV, foldOwnV, FoldP.foldOwnGV, foldReuseV, unfoldV, divFuelV, reifyV, BoCa.BoLo.performE,
    BoCa.BoLo.raiseE, opArgE, awaitE, thenE, hndTerm, hndExpr, Expr.val, Val.lam, Val.prim, Val.unit,
    Val.i32, lam2, elet, unit', v0, v1, v2, v3, load', store', mintE, burnE] at $h:ident))

/-- The primitives that have a rule of their own. -/
def PrimRule : Prim → Prop
  | .alloc | .free | .host _ | .lit _ | .tab | .drop | .idx | .count | .countTry | .boundedFix
  | .split | .iterate => True
  | _ => False

/-- **A primitive is typed only by its own rule.** -/
theorem der_prim {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ p, e = .prim p → PrimRule p := by
  induction h <;> intro p he <;> cd_terms <;> (try subst he) <;> (try trivial)
  case force _ _ i C _ =>
    rcases forceE_cases C (.var i) with hf | hf <;> rw [hf] at he <;> simp at he

/-- `load` has no rule. -/
theorem not_der_load {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ (.prim .load) j :=
  fun h => der_prim h .load rfl

/-- **A primitive with no rule of its own, applied, has no derivation**, but `perform` and `raise`
(`[perform]`, `[raise]`). -/
theorem not_der_app_prim {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ p X, e = .app (.prim p) X → ¬ PrimRule p → p ≠ .perform → p ≠ .raise → False := by
  induction h <;> intro p X he hp hpe hpr <;> cd_terms
  case force _ _ i C _ =>
    rcases forceE_cases C (.var i) with hf | hf <;> rw [hf] at he <;> simp at he
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
  | effSub hle _ ih =>
      intro i he; obtain ⟨T, hT, hc⟩ := ih i he; exact ⟨T, hT, hc.step (JS.effSub _ _ _ hle)⟩
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
  | arrEmpty => intro a b he; exact .inr he.symm
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
  | effSub hle _ ih =>
      intro a b he
      rcases ih a b he with ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc⟩ | h
      · exact .inl ⟨Γ₁, Γ₂, A, B, hs, h₁, h₂, hc.step (JS.effSub _ _ _ hle)⟩
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

/-- **`inj₁ a` is read at the views of a sum**, `a` typed in the same context. -/
theorem der_inj₁ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ a, e = .inj₁ a → ∃ A B, CDerives Δ Γ a (.val A) ∧ ValCls (.sum A B) j := by
  induction h with
  | sumI₁ h => intro a he; cases he; exact ⟨_, _, h, ValCls.refl _⟩
  | ret _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he; exact ⟨A, B, ha, hc.step (JS.ret _)⟩
  | ofRet _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he; exact ⟨A, B, ha, hc.step (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he; exact ⟨A, B, ha, hc.step (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he; exact ⟨A, B, ha, hc.step (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro a he; obtain ⟨A, B, ha, hc⟩ := ih a he
      exact ⟨A, B, ha, hc.step (JS.val (VS.unroll _))⟩
  | force => intro a he; rcases forceE_var he with h | h <;> cases h
  | _ => intro a he; cd_terms

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
  | effSub hle _ ih =>
      intro he; rcases ih he with ⟨hd, hc⟩ | hr
      · exact .inl ⟨hd, hc.step (JS.effSub _ _ _ hle)⟩
      · exact .inr (hr.tail (JS.effSub _ _ _ hle))
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
  | effSub hle _ ih => intro he; obtain ⟨A, hc⟩ := ih he; exact ⟨A, hc.step (JS.effSub _ _ _ hle)⟩
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
    (∃ Z, X = .app (.prim .hnd) Z) ∨
  -- `[await-c]`
  (∃ n, X = .lam (.case (.var 0) (.var 0) (BoCa.BoLo.raiseE (opArgE n 1 (.var 0)))) ∧
    Y = BoCa.BoLo.performE (opArgE n 0 (.val .unit)) ∧ Ctx.Dead Γ)

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
  | effAwait hΓ =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        ⟨_, rfl, rfl, hΓ⟩)))))))))))), .refl⟩
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
  | effHandleV | effHandleVB | effHandleT | effHandleL =>
      intro X Y he; cases he
      exact ⟨_, .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inr (.inl ⟨_, rfl⟩)))))))))))), .refl⟩
  | ret _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro X Y he; obtain ⟨j₀, hb, hr⟩ := ih X Y he; exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
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

/-- **A `let (x, y) = V in M` is `[⊗E]`'s**: `V` at a tensor, `M` under its two parts, at a
computation type from which the same-term rules reach the `let`'s judgement. -/
theorem der_letpair {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ V M, e = .letpair V M → ∃ Γ₁ Γ₂ A B C, Ctx.SplitP Γ Γ₁ Γ₂ ∧
      CDerives Δ Γ₁ V (.val (.tensor A B)) ∧ CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γ₂) M (.comp C) ∧
      JR (.comp C) j := by
  induction h with
  | tensorE hs hV hM => intro V M he; cases he; exact ⟨_, _, _, _, _, hs, hV, hM, .refl⟩
  | ret _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, A, B, C, hs, hV, hM, hr.tail (JS.val (VS.unroll _))⟩
  | force => intro V M he; rcases forceE_var he with h | h <;> cases h
  | _ => intro V M he; cd_terms

/-- **A `V; M` is `[1E]`'s**: `V` at `1`, `M` at a computation type from which the same-term rules
reach the `;`'s judgement. -/
theorem der_seq {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ V M, e = .seq V M → ∃ Γ₁ Γ₂ C, Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ V (.val .unit) ∧
      CDerives Δ Γ₂ M (.comp C) ∧ JR (.comp C) j := by
  induction h with
  | unitE hs hV hM => intro V M he; cases he; exact ⟨_, _, _, hs, hV, hM, .refl⟩
  | ret _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro V M he; obtain ⟨Γ₁, Γ₂, C, hs, hV, hM, hr⟩ := ih V M he
      exact ⟨Γ₁, Γ₂, C, hs, hV, hM, hr.tail (JS.val (VS.unroll _))⟩
  | force => intro V M he; rcases forceE_var he with h | h <;> cases h
  | _ => intro V M he; cd_terms

/-- **A `M then x. N unwind D` is `[then]`'s**: `M` and `N` on the two sides of a split. -/
theorem der_then {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ N D M, e = thenE N D M → ∃ Γ₁ Γ₂ A j₁ j₂, Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ M j₁ ∧
      CDerives Δ (⟨A, true⟩ :: Γ₂) N j₂ := by
  induction h with
  | effThen hs _ _ _ _ _ _ _ _ hM hN _ => intro N D M he; cases he; exact ⟨_, _, _, _, _, hs, hM, hN⟩
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

/-- The clauses' type with each capturing clause's `κ` bare (`none`: `[handle]`) or boxed at `@d`
(`some d`: BOXED-κ, `[spec §28]`). -/
def clausesTyO (S : Row) (R : VTy) :
    Option Lifetime.Life → List (Qual × VTy × VTy) → (Nat → CTy) → VTy
  | none, E, fs => clausesTy S R E fs
  | some d, E, fs => clausesTyB S R d E fs

/-- A clause's type, `κ` bare or boxed. -/
def clauseTyO (S : Row) (R : VTy) : Option Lifetime.Life → Qual × VTy × VTy → CTy → VTy
  | none, o, F => clauseTy S R o F
  | some d, o, F => clauseTyB S R d o F

/-- `κ`'s type in a clause: `K`, or `[@d] K`. -/
def kBoxO : Option Lifetime.Life → VTy → VTy
  | none, K => K
  | some d, K => .box d K

theorem clausesTyO_nil (S : Row) (R : VTy) (ob : Option Lifetime.Life) (fs : Nat → CTy) :
    clausesTyO S R ob [] fs = .unit := by cases ob <;> rfl

theorem clausesTyO_cons (S : Row) (R : VTy) (ob : Option Lifetime.Life) (o : Qual × VTy × VTy)
    (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) :
    clausesTyO S R ob (o :: E) fs =
      .tensor (clauseTyO S R ob o (fs 0)) (clausesTyO S R ob E (fun j => fs (j + 1))) := by
  cases ob <;> rfl

/-- A capturing clause's type: `!U(A ⊗ κ ⊸ F_Σ R)`, `κ` at `kBoxO ob K`. -/
theorem clauseTyO_cap (S : Row) (R : VTy) (ob : Option Lifetime.Life) {q : Qual} {A B : VTy}
    (F : CTy) (hB : B.isZero = false) :
    clauseTyO S R ob (q, A, B) F =
      .bang (.thunk (.arr (.tensor A (kBoxO ob (kTy S R q B F))) (CTy.effOf S R))) := by
  cases ob <;> simp [clauseTyO, clauseTy, clauseTyB, kBoxO, hB]

/-- **A handler term is `[handle]`'s or BOXED-κ's**: its tags are its signature's, and the handler
pair is typed at the tensor of the return clause's type and the clauses', `κ` bare or boxed, over a
consumed context. -/
theorem der_hnd {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ (n : UInt32) (Q H M : Expr),
      e = .app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) (.pair Q H))) M →
      (∃ (Γ₁ Γ₂ : Ctx VTy) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) (A R : VTy)
        (ob : Option Lifetime.Life),
        Ctx.SplitP Γ Γ₁ Γ₂ ∧ Ctx.DeadP Γ₁ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
        CDerives Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTyO S R ob E fs)))) ∨
      (∃ (Γ₁ Γ₂ : Ctx VTy) (S SN : Row) (E : List (Qual × VTy × VTy)) (A R : VTy) (Hr Hc : Expr),
        Ctx.SplitP Γ Γ₁ Γ₂ ∧ Ctx.DeadP Γ₁ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
        H = .pair Hr (tailTuple E 0 Hc) ∧
        CDerives Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E)))) ∨
      (∃ (Γ₁ Γ₂ : Ctx VTy) (S SW : Row) (E : List (Qual × VTy × VTy)) (Xs : Nat → VTy) (A R : VTy)
        (Hr Hw Hn : Expr),
        Ctx.SplitP Γ Γ₁ Γ₂ ∧ Ctx.DeadP Γ₁ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
        H = .pair Hr (lastTuple E 0 Hw Hn) ∧
        CDerives Δ Γ₁ (.pair Hr (.pair Hw Hn))
          (.val (.tensor (retTy S A R) (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0))))) := by
  induction h with
  | effHandleV hs hd _ hc _ _ _ _ =>
      intro n Q H M he
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he
      obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := he
      exact .inl ⟨_, _, _, _, _, _, _, none, hs, hd, rfl, hc⟩
  | effHandleVB hs hd _ hc _ _ _ _ =>
      intro n Q H M he
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he
      obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := he
      exact .inl ⟨_, _, _, _, _, _, _, some _, hs, hd, rfl, hc⟩
  | effHandleT hs hd _ _ hc =>
      intro n Q H M he
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he
      obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := he
      exact .inr (.inl ⟨_, _, _, _, _, _, _, _, _, hs, hd, rfl, rfl, hc⟩)
  | effHandleL hs hd _ _ _ hc =>
      intro n Q H M he
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he
      obtain ⟨⟨-, -, rfl, rfl⟩, -⟩ := he
      exact .inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, hs, hd, rfl, rfl, hc⟩)
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
    (∃ F, e = (foldOwnV F).1) ∨ (∃ F, e = (foldReuseV F).1) ∨ (∃ C, e = (unfoldV C).1) ∨
    e = divFuelV.1 ∨ (∃ res, e = (reifyV res).1) ∨ (∃ B, e = (FoldP.foldOwnGV B).1) ∨
    e = mintE ∨ e = burnE

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
  exact effOf_isRet S Y

theorem LamAx.not_comp {e : Expr} {C : CTy} (h : LamAx e (.comp C)) : C.isRet = true := by
  rcases h with ⟨-, T, -, hc⟩ | ⟨-, -, T, -, hc⟩ | ⟨-, T, hc⟩ <;> exact hc.comp_isRet

/-- The judgements a λ-value whose body is typed at `D` is read at: `D` itself, the views of its
thunk, and, over a persistent context, the views of the thunk's `!`. -/
def LamCls (Γ : Ctx VTy) (D : CTy) (j : Jdg) : Prop :=
  j = .comp D ∨ ValCls (.thunk D) j ∨ (Ctx.Banged Γ ∧ ValCls (.bang (.thunk D)) j)

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
    (hC : C.isRet = false) (hp : Ctx.Banged Γ) : LamCls Γ D (.val (.bang (.thunk C))) := by
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
    (ValCls (.thunk (.ret A)) j ∨ (Ctx.Banged Γ ∧ ValCls (.bang (.thunk (.ret A))) j))) ∨
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
    (h : LamInv Δ Γ M (.comp C)) (hC : C.isRet = false) (hp : Ctx.Banged Γ) :
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

theorem otherLam_mint : OtherLam mintE := by simp [OtherLam]

theorem otherLam_burn : OtherLam burnE := by simp [OtherLam]

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
  | effSub hle _ ih => intro M he; exact (ih M he).step (JS.effSub _ _ _ hle)
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
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inl ⟨_, rfl⟩)))))))))))) _)
  | unfoldN =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inl ⟨_, rfl⟩))))))))))))) _)
  | divFuel =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inl rfl)))))))))))))) _)
  | reify =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inl ⟨_, rfl⟩))))))))))))))) _)
  | foldOwnG =>
      intro M he
      exact LamInv.ofAx (he ▸ lamAx_other
        (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
          (.inr (.inr (.inr (.inr (.inl ⟨_, rfl⟩)))))))))))))))) _)
  | tokMint => intro M he; exact LamInv.ofAx (he ▸ lamAx_other otherLam_mint _)
  | tokBurn => intro M he; exact LamInv.ofAx (he ▸ lamAx_other otherLam_burn _)
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

/-- A view of `κ`'s type, bare or boxed, at a thunk is at its thunk. -/
theorem vview_kBoxO_thunk {C₀ C : CTy} (ob : Option Lifetime.Life)
    (h : VView (kBoxO ob (.thunk C₀)) (.thunk C)) : C₀ = C := by
  cases ob with
  | none => exact vview_thunk h
  | some d =>
      have := (h.hnf_of (.box (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h)))
        (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)).eq_self
        (fun _ _ h => by cases h) (fun _ h => by cases h)
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
    D = C ∧ Ctx.Banged Γ := by
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
  rcases h with ⟨A, D, hM, -⟩ | ⟨S, B, hM, -⟩ | ⟨x, b, Δ', S, C, hM, -⟩ | ⟨A, hM, -⟩ |
    ⟨M₁, M₂, h⟩ | h
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

/-- **A `let` of a term that is no variable, λ-value, `()` or injection of `()`, split**: the term
is typed at a row over the slot's type in one part of a split, and the body under the slot in the
other. -/
theorem der_bind_split {Δ : LifeCtx} {Γ : Ctx VTy} {N M : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app (.lam N) M) j) (hMv : ∀ i, M ≠ .var i) (hMl : ∀ b, M ≠ .lam b)
    (hMu : M ≠ .unit) (hM₁ : M ≠ .inj₁ .unit) (hM₂ : M ≠ .inj₂ .unit)
    (hw : ∀ M₁ M₂, Expr.lam N ≠ withPair M₁ M₂) (hc : NotConst (.lam N)) :
    ∃ Γ₁ Γ₂ T b S j', Ctx.SplitP Γ Γ₁ Γ₂ ∧ CDerives Δ Γ₁ M (.comp (CTy.effOf S T)) ∧
      CDerives Δ (⟨T, b⟩ :: Γ₂) N j' := by
  obtain ⟨j₀, hb, -⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hM, hf, -⟩ | ⟨-, -, i, -, -, hi, -⟩ |
    ⟨N', Γ₁, Γ₂, A, S, C, hN, hs, hM, hN', -⟩ | ⟨-, b, -, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · rcases der_lam hf N rfl with ⟨A', D, hN, hcl⟩ | ⟨S', B', hN, hcl⟩ | ⟨_, _, _, _, _, _, hcl⟩ |
      ⟨_, _, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx
    · obtain ⟨rfl, -⟩ : A' = A ∧ D = .ret B := by
        have := hcl.val_thunk; cases this; exact ⟨rfl, rfl⟩
      exact ⟨Γ₁, Γ₂, A', true, [], _, hs, .ret hM, hN⟩
    · have := hcl.val_thunk
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      exact ⟨Γ₁, Γ₂, .unit, false, [], _, hs, .ret hM, hN⟩
    · have := hcl.val_thunk; cases this
    · rcases hcl with hcl | ⟨-, hcl⟩
      · have := vview_thunk hcl; cases this
      · have := vview_bang_thunk hcl; cases this
    · exact (hw M₁ M₂ hwp).elim
    · exact (hc.notAx _ hx).elim
  · exact (hMv i hi).elim
  · cases hN
    exact ⟨Γ₁, Γ₂, A, true, S, _, hs, hM, hN'⟩
  · exact (hMl b hb).elim
  · exact (hMu hu).elim
  · exact (hMu hu).elim
  · exact (hM₁ hu).elim
  · exact (hM₂ hu).elim
  · exact (hMu hu).elim
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨n, hX, hY, hΓ⟩
    any_goals cases hX
    -- `[await-c]`'s term: its `perform` at an unmarked cancellable operation of the same key,
    -- answering `1 ⊕ 1`, which `[perform]` admits, and its body at an unmarked abortive row.
    subst hY
    have hsp : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → Ctx.SplitP Γ Γ Γ := by
      intro Γ h; induction h with
      | nil => exact .nil
      | cons _ ih => exact .dead ih
    refine ⟨Γ, Γ, .sum .unit .unit, true, [⟨n, 0, .cancel, .unit, .sum .unit .unit, .ret .unit, false⟩],
      .comp (CTy.effOf [⟨n, 1, .cancel, .unit, .zero, .ret .unit, false⟩] .unit), hsp hΓ,
      .effPerform (o := ⟨n, 0, .cancel, .unit, .sum .unit .unit, .ret .unit, false⟩)
        (by simp [Row.find]) rfl rfl (.unitI hΓ.toP), ?_⟩
    refine .sumE (.left (hsp hΓ)) (.var (.here hΓ.toP))
      (.effSub (RowLe.nil _) (.ret (.var (.here (.cons hΓ.toP)))))
      (.effRaise (o := ⟨n, 1, .cancel, .unit, .zero, .ret .unit, false⟩) (by simp [Row.find]) rfl rfl .unit
        (.var (.here (.cons hΓ.toP))))

/-- **A `let` of a term that is no variable, λ-value, `()` or injection of `()`**: the term is typed
at a row over the slot's type, and the body under the slot. -/
theorem der_bind {Δ : LifeCtx} {Γ : Ctx VTy} {N M : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app (.lam N) M) j) (hMv : ∀ i, M ≠ .var i) (hMl : ∀ b, M ≠ .lam b)
    (hMu : M ≠ .unit) (hM₁ : M ≠ .inj₁ .unit) (hM₂ : M ≠ .inj₂ .unit)
    (hw : ∀ M₁ M₂, Expr.lam N ≠ withPair M₁ M₂) (hc : NotConst (.lam N)) :
    ∃ Γ₁ Γ' T b S j', CtxLe Γ₁ Γ ∧ CtxLe Γ' Γ ∧ CDerives Δ Γ₁ M (.comp (CTy.effOf S T)) ∧
      CDerives Δ (⟨T, b⟩ :: Γ') N j' := by
  obtain ⟨Γ₁, Γ₂, T, b, S, j', hs, hM, hN⟩ := der_bind_split h hMv hMl hMu hM₁ hM₂ hw hc
  exact ⟨Γ₁, Γ₂, T, b, S, j', splitP_le_left hs, splitP_le_right hs, hM, hN⟩

/-- **A `let` of a closed λ-value**: as `der_bind`, or the polymorphic let, the body with the value
in place under a dead slot. -/
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
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨_, hX₁, hX₂, -⟩ <;>
      first | cases hX | (cases hX₂; done) | (cases hX₁; done)

/-! ### `load` has no rule -/

/-- `load x` has no derivation. -/
theorem not_der_load_app {Δ : LifeCtx} {Γ : Ctx VTy} {X : Expr} {j : Jdg} :
    ¬ CDerives Δ Γ (.app (.prim .load) X) j :=
  fun h => not_der_app_prim h .load X rfl id (by decide) (by decide)

/-- A term is no λ-constant, by unfolding. -/
macro "not_const" : tactic => `(tactic| (simp only [NotConst, OtherLam, forget, copy, swap, withbor,
    withload, withswap, sizeV, replaceV, arrLenV, swapV, foldImmV, foldOwnV, FoldP.foldOwnGV, foldReuseV, unfoldV,
    withborUE, divFuelV, reifyV, rkV, BoCa.BoLo.hndE,
    Expr.val, Val.lam, lam2, elet, unit', v0, v1, v2, v3, load', store', thenE, ne_eq,
    bindE, hndTerm, hndExpr, Val.unit, Val.prim, Val.i32, Val.inj₁, Val.inj₂, Val.pair,
    BoCa.BoLo.performE, opArgE, free', alloc', mintE, burnE,
    Expr.lam.injEq, reduceCtorEq, not_false_eq_true, not_exists, not_or, forall_const, and_self,
    implies_true, and_true, true_and, exists_false, or_self, Expr.app.injEq, Expr.letpair.injEq,
    Expr.pair.injEq, Expr.seq.injEq, Expr.case.injEq, false_and, and_false]))

/-- A hypothesis that a term is one of the other λ-constants is refuted by unfolding. -/
macro "not_other " h:ident : tactic => `(tactic| (simp [OtherLam, copy, swap, withbor, withload,
    withswap, sizeV, replaceV, arrLenV, swapV, foldImmV, foldOwnV, FoldP.foldOwnGV, foldReuseV, unfoldV, Expr.val,
    divFuelV, reifyV, rkV, BoCa.BoLo.hndE, Val.lam, lam2, elet, unit', v0, v1, v2, v3, withborUE,
    thenE, load', store', Val.prim, mintE, burnE,
    Val.unit] at $h:ident))

/-- A term is no `⟨M, N⟩`, by unfolding. -/
macro "not_withPair" : tactic => `(tactic| (intro M₁ M₂ h; simp [withPair, Expr.val, Val.lam, bindE,
    hndTerm, hndExpr, Val.unit, Val.prim, Val.i32, Val.inj₁, Val.inj₂, Val.pair,
    BoCa.BoLo.performE, opArgE, free', alloc'] at h))

/-! ### `swap` is typed at its axiom alone -/

/-- `swap`'s body under its first binder: `λy₂. let y₁ = load x in store x y₂; (x, y₁)`. -/
abbrev swapBody₁ : Expr :=
  .lam (elet (.app load' v1) (.seq (.app (.app store' v2) v1) (.pair v2 v0)))

/-- `swap` written as a λ has the body `swapBody₁`. -/
theorem swap_lam {M : Expr} (h : Expr.lam M = swap) : M = swapBody₁ := by
  cases h; rfl

/-- `swap`'s innermost body loads the cell, and `load` has no rule. -/
theorem not_der_swapLet {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} :
    ¬ CDerives Δ Γ (elet (.app load' v1) (.seq (.app (.app store' v2) v1) (.pair v2 v0))) j := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, hL, _⟩ := der_bind h (fun i h => by cases h)
    (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (by not_withPair) (by not_const)
  exact not_der_load_app hL

/-- `swap`'s body under its first binder has no derivation. -/
theorem not_der_swapBody₁ {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ swapBody₁ j := by
  intro h
  obtain ⟨_, _, _, hB⟩ := (der_lam h _ rfl).body
    (fun M₁ M₂ h => by simp [withPair, elet, Expr.val, Val.lam] at h)
    (NotConst.notAx (by not_const) _)
  exact not_der_swapLet hB

/-- **`swap` is read at the views of its axiom's type** `Ref A ⊸ B ⊸ Ref B ⊗ A`: typed through its
body, it would load its cell. -/
theorem der_swap {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    e = swap → ∃ A B, ValCls (axSwapTy A B) j := by
  induction h with
  | swap => intro _; exact ⟨_, _, ValCls.refl _⟩
  | lam h => intro he; obtain rfl := swap_lam he; exact (not_der_swapBody₁ h).elim
  | lamDead h => intro he; obtain rfl := swap_lam he; exact (not_der_swapBody₁ h).elim
  | allI _ _ _ h => intro he; obtain rfl := swap_lam he; exact (not_der_swapBody₁ h).elim
  | thunkF h => intro he; obtain rfl := swap_lam he; exact (not_der_swapBody₁ h).elim
  | bangThunkF _ h => intro he; obtain rfl := swap_lam he; exact (not_der_swapBody₁ h).elim
  | thunkV hC _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; rw [hc.comp_isRet] at hC; cases hC
  | bangThunkV _ hC _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; rw [hc.comp_isRet] at hC; cases hC
  | ret _ ih => intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.ret _)⟩
  | ofRet _ ih => intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih => intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.nuIn _ hC)⟩
  | nuOut hC _ ih => intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.nuOut _ hC)⟩
  | bangE _ ih => intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro he; obtain ⟨A, B, hc⟩ := ih he; exact ⟨A, B, hc.step (JS.val (VS.unroll _))⟩
  | force => intro he; rcases forceE_var he with h | h <;> cases h
  | _ => intro he; cd_terms

/-- **`swap x`, `x` a variable, is `⊸E`'s**: `x` is read at `Ref A`, and `swap x` at the views of
`B ⊸ Ref B ⊗ A`. -/
theorem der_swap_var {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {j : Jdg}
    (h : CDerives Δ Γ (.app swap (.var i)) j) :
    ∃ Γ₁ A B, CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ (.var i) (.val (.ref A)) ∧
      ValCls (.lolli B (.tensor (.ref B) A)) j := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i', A, C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, Γ₁, Γ₂, A, S, C, hN, hs, hY, hN', rfl⟩ | ⟨N, b, C, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · obtain ⟨A', B', hc⟩ := der_swap hf rfl
    have := vview_thunk hc
    simp only [CTy.arr.injEq, CTy.ret.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨Γ₁, A', B', splitP_le_left hs, hY, (ValCls.refl _).reach hr⟩
  · obtain ⟨A', B', hc⟩ := der_swap hf rfl
    have := hc.comp_isRet
    simp [CTy.isRet] at this
  · obtain rfl := swap_lam hN.symm
    exact (not_der_swapBody₁ hN').elim
  · cases hb
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨_, hX₁, hX₂, -⟩ <;>
      first | cases hX | (cases hX₂; done) | (cases hX₁; done)

/-- **`swap x y`, `x` a variable and `y` no projection's index, is `⊸E`'s**: `x` is read at
`Ref A`, and `swap x y` at the views of `Ref B ⊗ A`. -/
theorem der_swap_app {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {Y : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app (.app swap (.var i)) Y) j) (hY₁ : Y ≠ .inj₁ .unit)
    (hY₂ : Y ≠ .inj₂ .unit) :
    ∃ Γ₁ A B, CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ (.var i) (.val (.ref A)) ∧
      ValCls (.tensor (.ref B) A) j := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i', A, C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, Γ₁, Γ₂, A, S, C, hN, -⟩ | ⟨N, b, C, hN, -⟩ |
    ⟨x, b, C, a, -, hf, rfl⟩ | ⟨x, b, A, a, -, hf, rfl⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ |
    ⟨-, i', hu⟩ | hX
  · obtain ⟨Γ₃, A', B', hle, hc, hcl⟩ := der_swap_var hf
    have := vview_thunk hcl
    simp only [CTy.arr.injEq, CTy.ret.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    exact ⟨Γ₃, A', B', hle.trans (splitP_le_right hs), hc, (ValCls.refl _).reach hr⟩
  · obtain ⟨_, _, _, -, -, hcl⟩ := der_swap_var hf
    have := hcl.comp_isRet
    simp [CTy.isRet] at this
  · cases hN
  · cases hN
  · obtain ⟨_, _, _, -, -, hcl⟩ := der_swap_var hf
    have := hcl.comp_isRet
    simp [CTy.isRet] at this
  · obtain ⟨_, _, _, -, -, hcl⟩ := der_swap_var hf
    have := vview_thunk hcl
    cases this
  · exact (hY₁ hu).elim
  · exact (hY₂ hu).elim
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨_, hX₁, hX₂, -⟩ <;>
      first | cases hX | (cases hX₂; done) | (cases hX₁; done)

/-! ### Helpers for the clause tuples -/

/-- A variable read at a value type: a view of its slot's type. -/
theorem VarCls.val {T Y : VTy} (h : VarCls T (.val Y)) : VView T Y := by
  rcases h with h | ⟨C, -, hC, hr⟩
  · exact h
  · obtain ⟨S, A, rfl⟩ := hr.comp_val
    rw [effOf_isRet] at hC; cases hC

/-- A list of qualifiers is told apart by its tags. -/
theorem qualsVal_inj : ∀ {qs qs' : List Qual}, (qualsVal qs).1 = (qualsVal qs').1 → qs = qs'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [qualsVal, Val.unit, Val.pair] at h
  | _ :: _, [], h => by simp [qualsVal, Val.unit, Val.pair] at h
  | q :: qs, q' :: qs', h => by
      simp only [qualsVal, Val.pair, Val.i32, Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq,
        IntLit.i32.injEq] at h
      obtain ⟨hq, hqs⟩ := h
      rw [qualsVal_inj hqs]
      cases q <;> cases q' <;> first | rfl | exact absurd hq (by decide)

/-- **A handler's clause tuple**: in `handle_n M with (X, x₁)`, the slot of `x₁` is live and its
type views to the clauses' type, `κ` bare or boxed, whose signature carries the handler's tags. -/
theorem hnd_clauses {Δ : LifeCtx} {Γ : Ctx VTy} {n : UInt32} {qs : List Qual} {X M : Expr}
    {j : Jdg} (h : CDerives Δ Γ (hndExpr n qs (.pair X (.var 1)) M) j) :
    ∃ T S R E fs ob, Γ[1]? = some ⟨T, true⟩ ∧ VView T (clausesTyO S R ob E fs) ∧
      E.map Prod.fst = qs := by
  obtain ⟨Γ₁, Γ₂, S, E, fs, A, R, ob, hs, -, hQ, hH⟩ | ⟨_, _, _, _, E, _, _, _, _, -, -, -, hH, -⟩ |
      ⟨_, _, _, _, E, _, _, _, _, _, _, -, -, -, hH, -⟩ := der_hnd h n _ _ M rfl
  rotate_left
  · simp only [Expr.pair.injEq] at hH
    cases E <;> simp [tailTuple, Val.unit] at hH
  · simp only [Expr.pair.injEq] at hH
    cases E <;> simp [lastTuple, Val.unit] at hH
  have hE : E.map Prod.fst = qs := (qualsVal_inj hQ).symm
  rcases der_pair hH X (.var 1) rfl with ⟨Γ₁₁, Γ₁₂, A', B', hs', -, hv, hc⟩ | he
  · obtain ⟨-, rfl⟩ := vview_tensor hc
    obtain ⟨T, hT, hcT⟩ := der_var hv 1 rfl
    exact ⟨T, S, R, E, fs, ob, splitP_le_left hs _ _ (splitP_le_right hs' _ _ hT), hcT.val, hE⟩
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he

/-- **A pair read at a row**: its first part is read at the first factor of a tensor whose views
reach the row's type. -/
theorem pair_row {Δ : LifeCtx} {Γ : Ctx VTy} {a b : Expr} {S : Row} {T : VTy}
    (h : CDerives Δ Γ (.pair a b) (.comp (CTy.effOf S T))) (hb : ∀ c, b ≠ .prim c) :
    ∃ Γ' A B, CtxLe Γ' Γ ∧ CDerives Δ Γ' a (.val A) ∧ VView (.tensor A B) T := by
  rcases der_pair h a b rfl with ⟨Γ₁, Γ₂, A, B, hs, ha, -, hc⟩ | he
  · obtain ⟨S', Y, he, hY⟩ := hc
    obtain ⟨-, rfl⟩ := effOf_inj he
    exact ⟨Γ₁, A, B, splitP_le_left hs, ha, hY⟩
  · simp only [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32, Expr.pair.injEq] at he
    exact (hb _ he.2).elim

/-- **A λ-value read at a `!` thunk of `P ⊸ D`, `P` no `1`**: its context is persistent, and its
body is typed under a live `P`. -/
theorem lam_bang {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {P : VTy} {D : CTy}
    (h : CDerives Δ Γ (.lam M) (.val (.bang (.thunk (.arr P D))))) (hP : P ≠ .unit)
    (hw : ∀ M₁ M₂, Expr.lam M ≠ withPair M₁ M₂) (hc : NotConst (.lam M)) :
    Ctx.Banged Γ ∧ CDerives Δ (⟨P, true⟩ :: Γ) M (.comp D) := by
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
theorem ValCls.at {T₀ T : VTy} {j : Jdg} (h : ValCls T₀ j)
    (hj : j = .val T ∨ ∃ S, j = .comp (CTy.effOf S T)) : VView T₀ T := by
  rcases hj with rfl | ⟨S, rfl⟩
  · exact h
  · obtain ⟨S', Y, he, hY⟩ := h
    obtain ⟨-, rfl⟩ := effOf_inj he
    exact hY

/-! ### The rows a computation is read at

`[handle]`, `[then]`, `[perform]`, `[raise]`, `[let]` and `bind` conclude at a row, and the
same-term rules read a computation at another row only by `[sub]`: they grow rows (`JR.rowLe`).
Each inversion below gives its rule's premises at the judgement the rule concludes with, and the
same-term rules' path from there to the judgement read. -/

/-- What a computation at `F_Σ Y` is read at through the same-term rules: a row above `Σ` over a
view of `Y`, or, with `Σ` below the empty row, a view of `Y`. -/
def RowCls (S : Row) (Y : VTy) : Jdg → Prop
  | .comp D => ∃ S' Y', D = CTy.effOf S' Y' ∧ RowLe S S' ∧ VView Y Y'
  | .val Y' => RowLe S [] ∧ VView Y Y'

theorem RowCls.step {S : Row} {Y : VTy} {j j' : Jdg} (hs : JS j j') (h : RowCls S Y j) :
    RowCls S Y j' := by
  cases hs with
  | val hv => exact ⟨h.1, h.2.tail hv⟩
  | ret A => exact ⟨[], A, rfl, h.1, h.2⟩
  | ofRet A =>
      obtain ⟨S', Y', he, hle, hY⟩ := h
      obtain ⟨rfl, rfl⟩ := effOf_inj (S := []) he
      exact ⟨hle, hY⟩
  | effSub S₀ S₁ A hle' =>
      obtain ⟨S', Y', he, hle, hY⟩ := h
      obtain ⟨rfl, rfl⟩ := effOf_inj he
      exact ⟨_, _, rfl, hle.trans hle', hY⟩
  | nuIn C hC =>
      obtain ⟨S', Y', he, -⟩ := h
      obtain ⟨C₁, C₂, hu⟩ := unroll_amp hC
      exact absurd (hu.symm.trans he) (effOf_ne_amp S' Y' C₁ C₂).symm
  | nuOut C hC =>
      obtain ⟨S', Y', he, -⟩ := h
      exact absurd he.symm (effOf_ne_nu S' Y' C)

theorem RowCls.reach {S : Row} {Y : VTy} {j j' : Jdg} (hr : JR j j') (h : RowCls S Y j) :
    RowCls S Y j' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **The same-term rules grow rows**: a computation at `F_Σ Y` read at `F_Σ′ Y′` has `Σ ≤ Σ′`. -/
theorem JR.rowLe {S S' : Row} {Y Y' : VTy}
    (hr : JR (.comp (CTy.effOf S Y)) (.comp (CTy.effOf S' Y'))) : RowLe S S' := by
  obtain ⟨S₁, Y₁, he, hle, -⟩ := RowCls.reach hr (S := S) (Y := Y) ⟨S, Y, rfl, RowLe.refl S, .refl⟩
  obtain ⟨rfl, -⟩ := effOf_inj he
  exact hle

/-- `[handle]`'s premises, at its conclusion `j₀`. -/
def HndBase (Δ : LifeCtx) (Γ : Ctx VTy) (n : UInt32) (Q H M : Expr) (j₀ : Jdg) : Prop :=
  (∃ (Γ₁ Γ₂ : Ctx VTy) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy)
    (cs : Nat → Bool) (A R : VTy) (ob : Option Lifetime.Life),
    Ctx.SplitP Γ Γ₁ Γ₂ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
    CDerives Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTyO S R ob E fs))) ∧
    CDerives Δ Γ₂ M (.comp (CTy.effOf (Row.ofEff n E 0 fs cs ++ S) A)) ∧
    (∀ o ∈ S, o.n ≠ n) ∧ j₀ = .comp (CTy.effOf S R)) ∨
  (∃ (Γ₁ Γ₂ : Ctx VTy) (S SN : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) (A R : VTy)
    (Hr Hc : Expr),
    Ctx.SplitP Γ Γ₁ Γ₂ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧ H = .pair Hr (tailTuple E 0 Hc) ∧
    CDerives Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E))) ∧
    CDerives Δ Γ₂ M (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) ∧
    (∀ o ∈ S, o.n ≠ n) ∧ j₀ = .comp (CTy.effOf S R)) ∨
  (∃ (Γ₁ Γ₂ : Ctx VTy) (S SW : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy)
    (Xs : Nat → VTy) (A R : VTy) (Hr Hw Hn : Expr),
    Ctx.SplitP Γ Γ₁ Γ₂ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
    H = .pair Hr (lastTuple E 0 Hw Hn) ∧
    CDerives Δ Γ₁ (.pair Hr (.pair Hw Hn))
      (.val (.tensor (retTy S A R) (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0)))) ∧
    CDerives Δ Γ₂ M (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) ∧
    (∀ o ∈ S, o.n ≠ n) ∧ j₀ = .comp (CTy.effOf S R))

/-- **A handler term is `[handle]`'s, then the same-term rules**: the handled body at the handler's
signature row before the outer row `Σ`, the clauses at `Σ`, and the term read at a row the
same-term rules reach from `Σ`. -/
theorem der_hndJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ (n : UInt32) (Q H M : Expr),
      e = .app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) (.pair Q H))) M →
      ∃ j₀, HndBase Δ Γ n Q H M j₀ ∧ JR j₀ j := by
  induction h with
  | effHandleV hs _ _ hc _ hnS _ _ he =>
      intro n Q H M he'
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he'
      obtain ⟨⟨-, hn, rfl, rfl⟩, rfl⟩ := he'
      simp only [Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hn
      subst hn
      exact ⟨_, .inl ⟨_, _, _, _, _, _, _, _, none, hs, rfl, hc, he, hnS, rfl⟩, .refl⟩
  | effHandleVB hs _ _ hc _ hnS _ _ he =>
      intro n Q H M he'
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he'
      obtain ⟨⟨-, hn, rfl, rfl⟩, rfl⟩ := he'
      simp only [Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hn
      subst hn
      exact ⟨_, .inl ⟨_, _, _, _, _, _, _, _, some _, hs, rfl, hc, he, hnS, rfl⟩, .refl⟩
  | effHandleT hs _ _ _ hc _ _ hnS _ _ _ he =>
      intro n Q H M he'
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he'
      obtain ⟨⟨-, hn, rfl, rfl⟩, rfl⟩ := he'
      simp only [Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hn
      subst hn
      exact ⟨_, .inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, hs, rfl, rfl, hc, he, hnS, rfl⟩), .refl⟩
  | effHandleL hs _ _ _ _ hc _ _ hnS _ _ _ _ _ _ he =>
      intro n Q H M he'
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he'
      obtain ⟨⟨-, hn, rfl, rfl⟩, rfl⟩ := he'
      simp only [Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hn
      subst hn
      exact ⟨_, .inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, hs, rfl, rfl, hc, he, hnS, rfl⟩),
        .refl⟩
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
  | ret _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro n Q H M he; cd_at he

/-- **A handler whose clause tuple is neither a tail-resuming handler's nor a `[handle-last]`
handler's** is `[handle]`'s at bare or boxed `κ`, then the same-term rules. -/
theorem der_hndJ₁ {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} {n : UInt32} {Q H M : Expr}
    (h : CDerives Δ Γ (.app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) (.pair Q H))) M) j)
    (hT : (∀ Hr E Hc, H ≠ .pair Hr (tailTuple E 0 Hc)) ∧
      ∀ Hr E Hw Hn, H ≠ .pair Hr (lastTuple E 0 Hw Hn)) :
    ∃ j₀, (∃ (Γ₁ Γ₂ : Ctx VTy) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy)
      (cs : Nat → Bool) (A R : VTy) (ob : Option Lifetime.Life),
      Ctx.SplitP Γ Γ₁ Γ₂ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
      CDerives Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTyO S R ob E fs))) ∧
      CDerives Δ Γ₂ M (.comp (CTy.effOf (Row.ofEff n E 0 fs cs ++ S) A)) ∧
      (∀ o ∈ S, o.n ≠ n) ∧ j₀ = .comp (CTy.effOf S R)) ∧ JR j₀ j := by
  obtain ⟨j₀, hb | ⟨_, _, _, _, E, _, _, _, Hr, Hc, -, -, hH, -⟩ |
    ⟨_, _, _, _, E, _, _, _, _, Hr, Hw, Hn, -, -, hH, -⟩, hr⟩ := der_hndJ h n Q H M rfl
  · exact ⟨j₀, hb, hr⟩
  · exact absurd hH (hT.1 Hr E Hc)
  · exact absurd hH (hT.2 Hr E Hw Hn)

/-- A clause tuple of named clauses is neither a tail-resuming handler's nor a `[handle-last]`
handler's, by unfolding. -/
macro "not_tail" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
    refine ⟨?_, ?_⟩
    · intro Hr E Hc h
      rcases E with _ | ⟨⟨q, A, B⟩, E⟩ <;>
        simp only [tailTuple, Expr.pair.injEq, Expr.val, reduceCtorEq, false_and, and_false] at h
      obtain ⟨-, h, -⟩ := h
      unfold tailClause at h
      split at h <;>
        simp [pickE, resumeB, Expr.val, Val.lam, Val.unit, Val.inj₁, Val.inj₂, $xs,*] at h
    · intro Hr E Hw Hn h
      rcases E with _ | ⟨⟨q, A, B⟩, E⟩ <;>
        simp only [lastTuple, Expr.pair.injEq, Expr.val, reduceCtorEq, false_and, and_false] at h
      obtain ⟨-, h, -⟩ := h
      unfold lastClause at h
      split at h <;>
        simp [pickE, thenE, Expr.val, Val.lam, Val.prim, Val.unit, Val.inj₁, Val.inj₂, $xs,*] at h))

/-- `[then]`'s premises, at its conclusion `j₀`. -/
def ThenBase (Δ : LifeCtx) (Γ : Ctx VTy) (D M : Expr) (j₀ : Jdg) : Prop :=
  ∃ (Γ₁ Γ₂ : Ctx VTy) (A B : VTy) (S SM SD : Row), Ctx.SplitP Γ Γ₁ Γ₂ ∧
    RowLe SM S ∧ RowLe SD S ∧
    (∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin) ∧
    CDerives Δ Γ₁ M (.comp (CTy.effOf SM A)) ∧
    CDerives Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit)) ∧
    j₀ = .comp (CTy.effOf S B)

/-- **A `M then x. N unwind D` is `[then]`'s, then the same-term rules**: `M` and the finaliser at
rows below the `[then]`'s, each capturable operation of `M`'s row recording the finaliser's row in
its cancel row (`ThenLe`). -/
theorem der_thenJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ N D M, e = thenE N D M → ∃ j₀, ThenBase Δ Γ D M j₀ ∧ JR j₀ j := by
  induction h with
  | effThen hs _ _ _ hMS hDS hfin _ _ hM _ hD _ _ _ =>
      intro N D M he; cases he
      exact ⟨_, ⟨_, _, _, _, _, _, _, hs, hMS, hDS,
        fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc), hM, hD, rfl⟩, .refl⟩
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
  | ret _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro N D M he; cd_terms

/-- `[perform]`'s premises, at its conclusion `j₀`. -/
def PerfBase (n i : UInt32) (j₀ : Jdg) : Prop :=
  ∃ (S : Row) (o : OpSig), Row.find S n i = some o ∧ o.abort = false ∧ o.rc = false ∧
    j₀ = .comp (CTy.effOf S o.B)

/-- **A `perform` is `[perform]`'s, then the same-term rules**: its row finds the operation. -/
theorem der_performJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ n i V, e = BoCa.BoLo.performE (opArgE n i V) → ∃ j₀, PerfBase n i j₀ ∧ JR j₀ j := by
  induction h with
  | effPerform hf hna hac _ =>
      intro n i V he
      simp only [BoCa.BoLo.performE, opArgE, Expr.val, Val.prim, Val.i32, Expr.app.injEq,
        Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at he
      obtain ⟨-, rfl, rfl, -⟩ := he
      exact ⟨_, ⟨_, _, hf, hna, hac, rfl⟩, .refl⟩
  | force => intro n i V he; rcases forceE_var he with h | h <;> cd_at h
  | lolliE _ _ hf =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hf _ rfl).elim
  | app _ hM _ =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allEV hM _ =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | ret _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro n i V he; cd_at he

/-- `[raise]`'s premises, at its conclusion `j₀`. -/
def RaiseBase (n i : UInt32) (j₀ : Jdg) : Prop :=
  ∃ (S : Row) (o : OpSig) (B : VTy), Row.find S n i = some o ∧ o.abort = true ∧ o.rc = false ∧
    j₀ = .comp (CTy.effOf S B)

/-- **A `raise` is `[raise]`'s, then the same-term rules**: its row finds the operation. -/
theorem der_raiseJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ n i V, e = BoCa.BoLo.raiseE (opArgE n i V) → ∃ j₀, RaiseBase n i j₀ ∧ JR j₀ j := by
  induction h with
  | effRaise hf ha hrc _ _ =>
      intro n i V he
      simp only [BoCa.BoLo.raiseE, opArgE, Expr.val, Val.prim, Val.i32, Expr.app.injEq,
        Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at he
      obtain ⟨-, rfl, rfl, -⟩ := he
      exact ⟨_, ⟨_, _, _, hf, ha, hrc, rfl⟩, .refl⟩
  | force => intro n i V he; rcases forceE_var he with h | h <;> cd_at h
  | lolliE _ _ hf =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hf _ rfl).elim
  | app _ hM _ =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allEV hM _ =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | ret _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro n i V he; cd_at he

/-- `bind`'s and `[let]`'s premise on the bound term, at the conclusion `j₀`: the bound term at a
row, and the conclusion at that row (`[let]`), or the bound term at the empty row (`bind`). -/
def LetBase (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (j₀ : Jdg) : Prop :=
  ∃ (Γ₁ : Ctx VTy) (S : Row) (A : VTy), CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ M (.comp (CTy.effOf S A)) ∧
    (S = [] ∨ ∃ B, j₀ = .comp (CTy.effOf S B))

/-- **A `M to x. N` whose bound term is no variable, λ-value, `()` or injection of `()`** is
`bind`'s or `[let]`'s, then the same-term rules; or `⊸E`'s, its bound term at a value
judgement. -/
theorem der_letJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ N M, e = .app (.lam N) M → (∀ i, M ≠ .var i) → (∀ b, M ≠ .lam b) → M ≠ .unit →
      M ≠ .inj₁ .unit → M ≠ .inj₂ .unit →
      (∀ n, N ≠ .case (.var 0) (.var 0) (BoCa.BoLo.raiseE (opArgE n 1 (.var 0)))) →
      (∃ j₀, LetBase Δ Γ M j₀ ∧ JR j₀ j) ∨ ∃ Γ₁ A, CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ M (.val A) := by
  induction h with
  | effAwait =>
      intro N M he _ _ _ _ _ hNa
      simp only [awaitE, Expr.app.injEq, Expr.val, Val.lam, Expr.lam.injEq] at he
      exact (hNa _ he.1.symm).elim
  | bind hs hM _ =>
      intro N M he _ _ _ _ _ _
      simp only [Expr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact .inl ⟨_, ⟨_, [], _, splitP_le_left hs, hM, .inl rfl⟩, .refl⟩
  | effLet hs _ _ hM _ =>
      intro N M he _ _ _ _ _ _
      simp only [Expr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact .inl ⟨_, ⟨_, _, _, splitP_le_left hs, hM, .inr ⟨_, rfl⟩⟩, .refl⟩
  | lolliE hs ha _ =>
      intro N M he _ _ _ _ _ _
      simp only [Expr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact .inr ⟨_, _, splitP_le_left hs, ha⟩
  | app _ _ _ =>
      intro N M he hv _ _ _ _ _
      simp only [Expr.app.injEq] at he
      exact (hv _ he.2.symm).elim
  | letPoly b _ _ _ =>
      intro N M he _ hl _ _ _ _
      simp only [Expr.app.injEq] at he
      exact (hl _ he.2.symm).elim
  | allE _ _ =>
      intro N M he _ _ hu _ _ _
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | allEV _ _ =>
      intro N M he _ _ hu _ _ _
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | proj₁ _ =>
      intro N M he _ _ _ hu _ _
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | proj₂ _ =>
      intro N M he _ _ _ _ hu _
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | force => intro N M he; rcases forceE_var he with h | h <;> simp at h
  | ret _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.ret _)⟩
      · exact .inr h
  | ofRet _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
      · exact .inr h
  | effSub hle _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
      · exact .inr h
  | nuIn hC _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
      · exact .inr h
  | nuOut hC _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
      · exact .inr h
  | bangE _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
      · exact .inr h
  | boxI _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
      · exact .inr h
  | boxE _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
      · exact .inr h
  | immSub _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
      · exact .inr h
  | mutSub _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
      · exact .inr h
  | roll _ _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
      · exact .inr h
  | unroll _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅ h₆
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ h₆ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
      · exact .inr h
  | _ => intro N M he; cd_at he

/-! ### `κ`'s cancel branch, applied -/

/-- A λ-value that is no constant and no pair of computations, read at `A ⊸ D` with `A` no `1`, is
`[⊸I]`'s. -/
theorem lam_arr {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {A : VTy} {D : CTy} {j : Jdg}
    (h : CDerives Δ Γ (.lam N) j) (hj : j = .comp (.arr A D) ∨ j = .val (.thunk (.arr A D)))
    (hA : A ≠ .unit) (hw : ∀ M₁ M₂, Expr.lam N ≠ withPair M₁ M₂) (hc : NotConst (.lam N)) :
    CDerives Δ (⟨A, true⟩ :: Γ) N (.comp D) := by
  have hcls : ∀ {D' : CTy} {Γ' : Ctx VTy}, LamCls Γ' D' j → D' = .arr A D := by
    intro D' Γ' h
    rcases hj with rfl | rfl
    · rcases h with h | h | ⟨-, h⟩
      · cases h; rfl
      · obtain ⟨S, Y, he, -⟩ := h; exact absurd he.symm (effOf_ne_arr S Y A D)
      · obtain ⟨S, Y, he, -⟩ := h; exact absurd he.symm (effOf_ne_arr S Y A D)
    · rcases h with h | h | ⟨-, h⟩
      · cases h
      · exact vview_thunk h
      · exact vview_bang_thunk h
  rcases der_lam h N rfl with ⟨A', D', hN, hl⟩ | ⟨S, B, -, hl⟩ | ⟨_, _, _, _, _, -, hl⟩ |
    ⟨A', -, hl⟩ | ⟨M₁, M₂, hwp⟩ | hx
  · cases hcls hl; exact hN
  · have := hcls hl
    simp only [CTy.arr.injEq] at this
    exact (hA this.1.symm).elim
  · cases hcls hl
  · rcases hj with rfl | rfl
    · rcases hl with ⟨S, Y, he, -⟩ | ⟨-, S, Y, he, -⟩ <;>
        exact absurd he.symm (effOf_ne_arr S Y A D)
    · rcases hl with hl | ⟨-, hl⟩
      · cases vview_thunk hl
      · cases vview_bang_thunk hl
  · exact (hw M₁ M₂ hwp).elim
  · exact (hc.notAx _ hx).elim

/-- A variable whose slot, in a context below `Γ`, is `Γ`'s slot `0`. -/
theorem varCls_of_le {Δ : LifeCtx} {Γ Γ' : Ctx VTy} {T : VTy} {j : Jdg}
    (hslot : Γ[0]? = some ⟨T, true⟩) (hle : CtxLe Γ' Γ) (h : CDerives Δ Γ' (.var 0) j) :
    VarCls T j := by
  obtain ⟨T', hT', hc⟩ := der_var h 0 rfl
  rw [hle 0 T' hT'] at hslot
  cases hslot
  exact hc

/-- No view of a `!` thunk is `1`. -/
theorem vview_bang_thunk_unit {C : CTy} (h : VView (.bang (.thunk C)) .unit) : False := by
  rcases h.hnf (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h)) with
    h' | ⟨A', hA, h'⟩ | ⟨a, A', h'⟩ | ⟨a, A', h'⟩
  · have := h'.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h); cases this
  · cases hA
    have := h'.eq_of_heads (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ h => by cases h)
    cases this
  · cases h'
  · cases h'

/-- **An unrestricted `κ`'s cancel branch, applied**: at a slot whose type is a view of
`!U(C₁ & C₂)`, `x (inj₂ ())` is read at what the same-term rules reach from `C₂`. -/
theorem kappa_cancel_jr {Δ : LifeCtx} {Γ : Ctx VTy} {C₁ C₂ : CTy} {T : VTy} {j : Jdg}
    (hT : VView (.bang (.thunk (.amp C₁ C₂))) T) (hslot : Γ[0]? = some ⟨T, true⟩)
    (h : CDerives Δ Γ (.app (.var 0) (.val (Val.inj₂ Val.unit))) j) : JR (.comp C₂) j := by
  obtain ⟨j₀, hb, hr⟩ := der_app h (.var 0) (.val (Val.inj₂ Val.unit)) rfl
  rcases hb with ⟨_, _, _, _, hs, -, hf, rfl⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, he, -⟩ |
    ⟨D₁, D₂, -, hX, rfl⟩ | ⟨he, -⟩ | he | he | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he, -⟩
  · rcases varCls_of_le hslot (splitP_le_right hs) hf with hc | ⟨C, rfl, -, hr'⟩
    · cases vview_bang_thunk (hT.trans hc)
    · cases vview_bang_thunk hT
      obtain ⟨S, A, he⟩ := JR.comp_val hr'
      exact absurd he (effOf_ne_amp S A C₁ C₂).symm
  all_goals first
    | (cases he)
    | skip
  · rcases varCls_of_le hslot (CtxLe.refl Γ) hX with hc | ⟨C, rfl, -, hr'⟩
    · obtain ⟨S, Y, he, -⟩ := hc
      exact absurd he.symm (effOf_ne_amp S Y D₁ D₂)
    · cases vview_bang_thunk hT
      obtain ⟨-, rfl⟩ := JR.amp_amp hr'
      exact hr

/-- **A cancellable `κ`'s cancel branch, applied**: at a slot of `U(C₁ & C₂)`, bare or boxed,
`x (inj₂ ())` is read at what the same-term rules reach from `C₂`. -/
theorem kcancel_jr_cancellable {Δ : LifeCtx} {Γ Γ' : Ctx VTy} {C₁ C₂ : CTy} {j : Jdg}
    {ob : Option Lifetime.Life}
    (hslot : Γ[0]? = some ⟨kBoxO ob (.thunk (.amp C₁ C₂)), true⟩) (hle : CtxLe Γ' Γ)
    (h : CDerives Δ Γ' (.app (.var 0) (.val (Val.inj₂ Val.unit))) j) : JR (.comp C₂) j := by
  obtain ⟨j₀, hb, hr⟩ := der_app h (.var 0) (.val (Val.inj₂ Val.unit)) rfl
  rcases hb with ⟨_, _, _, _, hs, -, hf, rfl⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, he, -⟩ |
    ⟨D₁, D₂, -, hX, rfl⟩ | ⟨he, -⟩ | he | he | ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he, -⟩
  · rcases varCls_of_le hslot (CtxLe.trans (splitP_le_right hs) hle) hf with hc | ⟨C, hT, -, hr'⟩
    · cases vview_kBoxO_thunk ob hc
    · rcases ob with _ | d <;> cases hT
      obtain ⟨S, A, he⟩ := JR.comp_val hr'
      exact absurd he (effOf_ne_amp S A C₁ C₂).symm
  all_goals first
    | (cases he)
    | skip
  · rcases varCls_of_le hslot hle hX with hc | ⟨C, hT, -, hr'⟩
    · obtain ⟨S, Y, he, -⟩ := hc
      exact absurd he.symm (effOf_ne_amp S Y D₁ D₂)
    · rcases ob with _ | d <;> cases hT
      obtain ⟨-, rfl⟩ := JR.amp_amp hr'
      exact hr

/-- **`κ`'s cancel read at a row**: the cancel row is no `⊤`, and its operations, ahead of the row,
are below the row. -/
theorem cancelTy_rowLe {S : Row} {F : CTy} {R : VTy}
    (h : JR (.comp (cancelTy S F)) (.comp (CTy.effOf S R))) :
    F.isTop = false ∧ RowLe (F.rowOf ++ S) S := by
  cases hF : F.isTop
  · rw [show cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit by simp [cancelTy, hF]] at h
    exact ⟨rfl, JR.rowLe h⟩
  · rw [show cancelTy S F = .top by simp [cancelTy, hF]] at h
    have := JR.rigid h rigid_top
    simp only [Jdg.comp.injEq] at this
    exact (effOf_ne_top S R this).elim

/-! ### A continuation is used once: the clauses R1–R4

S6's witnesses, as clauses of a handler's clause tuple: R1 drops `κ`, R2 resumes it twice, R3
cancels it, and R4 cancels and then resumes it. -/

/-- `resume k w`, in A-normal form: `w to y. k (inj₁ ()) y`. -/
def resumeE (k w : Expr) : Expr := .app (.lam (.app (.app (k.shift 1 0) (.inj₁ .unit)) (.var 0))) w

/-- `cancel k`: `k (inj₂ ())`. -/
def cancelE (k : Expr) : Expr := .app k (.inj₂ .unit)

/-- R1's clause `op (v, k) ⇒ return ff`: `κ` dropped. -/
def dropCl : Val := ⟨.lam (.letpair (.var 0) (.inj₁ .unit)), .lam⟩

/-- R2's body: `resume k () to _. resume k ()`. -/
def twiceBody : Expr := bindE (resumeE (.var 0) .unit) (resumeE (.var 1) .unit)

/-- R2's clause `op (v, k) ⇒ resume k () to _. resume k ()`: `κ` resumed twice. -/
def twiceCl : Val := ⟨.lam (.letpair (.var 0) twiceBody), .lam⟩

/-- R3's body: `cancel k to _. return ff`. -/
def cancelBody : Expr := bindE (cancelE (.var 0)) (.inj₁ .unit)

/-- R3's clause `op (v, k) ⇒ cancel k to _. return ff`: `κ` cancelled. -/
def cancelCl : Val := ⟨.lam (.letpair (.var 0) cancelBody), .lam⟩

/-- R4's body: `cancel k to _. resume k ()`. -/
def cancelResumeBody : Expr := bindE (cancelE (.var 0)) (resumeE (.var 1) .unit)

/-- R4's clause `op (v, k) ⇒ cancel k to _. resume k ()`: `κ` cancelled, then resumed. -/
def cancelResumeCl : Val := ⟨.lam (.letpair (.var 0) cancelResumeBody), .lam⟩

/-- At a resuming operation a clause is at `!U(A ⊗ kTy ⊸ F_Σ R)`. -/
theorem clauseTy_resuming {S : Row} {R : VTy} {q : Qual} {A B : VTy} {F : CTy}
    (h : (B.isZero && q != .lin) = false) :
    clauseTy S R (q, A, B) F =
      .bang (.thunk (.arr (.tensor A (kTy S R q B F)) (CTy.effOf S R))) := by
  simp [clauseTy, h]

/-- A must-resume or cancellable `κ` is linear: no persistent type. -/
theorem kTy_not_persistent {S : Row} {R : VTy} {q : Qual} {B : VTy} {F : CTy} (hq : q ≠ .unr) :
    ¬ (kTy S R q B F).Persistent := by
  cases q <;> simp_all [kTy, VTy.Persistent, VTy.persistent]

/-- **A clause `λp. let (v, k) = p in X` at a resuming operation's clause type** types `X` with
`k : kTy` live in slot `0` and `v : A` in slot `1`, at a computation type from which the same-term
rules reach the clause's row. -/
theorem der_clause_body {Δ : LifeCtx} {Γ : Ctx VTy} {X : Expr} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} {F : CTy} (hres : (B.isZero && q != .lin) = false)
    (hw : ∀ M₁ M₂, Expr.lam (.letpair (.var 0) X) ≠ withPair M₁ M₂)
    (hc : NotConst (.lam (.letpair (.var 0) X)))
    (h : CDerives Δ Γ (.lam (.letpair (.var 0) X)) (.val (clauseTy S R (q, A, B) F))) :
    ∃ Γb C, CDerives Δ (⟨kTy S R q B F, true⟩ :: ⟨A, true⟩ :: Γb) X (.comp C) ∧
      JR (.comp C) (.comp (CTy.effOf S R)) := by
  rw [clauseTy_resuming hres] at h
  obtain ⟨-, hb⟩ := lam_bang h (fun h => by cases h) hw hc
  obtain ⟨Γ₁, Γ₂, A', B', C, hs, hV, hX, hr⟩ := der_letpair hb _ _ rfl
  obtain ⟨T, hT, hcT⟩ := der_var hV 0 rfl
  have hT' := splitP_le_left hs 0 T hT
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at hT'
  subst hT'
  obtain ⟨rfl, rfl⟩ := vview_tensor hcT.val
  exact ⟨Γ₂, C, hX, hr⟩

/-- **A slot used on both sides of `M to x. N` is persistent.** -/
theorem k_twice {Δ : LifeCtx} {Γb : Ctx VTy} {K A : VTy} {N M : Expr} {j : Jdg}
    (h : CDerives Δ (⟨K, true⟩ :: ⟨A, true⟩ :: Γb) (.app (.lam N) M) j)
    (hMv : ∀ i, M ≠ .var i) (hMl : ∀ b, M ≠ .lam b) (hMu : M ≠ .unit) (hM₁ : M ≠ .inj₁ .unit)
    (hM₂ : M ≠ .inj₂ .unit) (hw : ∀ M₁ M₂, Expr.lam N ≠ withPair M₁ M₂) (hc : NotConst (.lam N))
    (hM0 : M.HasVar 0) (hN1 : N.HasVar 1) : K.Persistent := by
  obtain ⟨Γ₁, Γ₂, T, b, S, j', hs, hM, hN⟩ := der_bind_split h hMv hMl hMu hM₁ hM₂ hw hc
  obtain ⟨T₁, hT₁⟩ := fv_live hM 0 hM0
  obtain ⟨T₂, hT₂⟩ := fv_live hN 1 hN1
  have hp := splitP_both hs hT₁ (slot_succ hT₂)
  have hT := splitP_le_left hs 0 T₁ hT₁
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at hT
  subst hT
  exact hp

/-- **A must-resume `κ`'s cancel is at `⊤` only**: `κ (inj₂ ())` projects `κ`'s `&` onto its cancel
branch, `⊤` at a must-resume operation, and `κ` is no function of `⊸`. -/
theorem der_cancel_lin {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {S : Row} {R B : VTy} {F : CTy}
    {j : Jdg} (h : CDerives Δ Γ (cancelE (.var i)) j)
    (hi : ∀ T, Γ[i]? = some ⟨T, true⟩ → T = kTy S R .lin B F) : JR (.comp .top) j := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B', hs, -, hf, rfl⟩ | ⟨-, -, i', -, -, hi', -⟩ |
    ⟨N, -, -, -, -, -, hN, -⟩ | ⟨N, -, -, hN, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨C, D, -, hX, rfl⟩ | ⟨hu, -⟩ | hX
  · -- `⊸E`: `κ` read at `A ⊸ B'`, which no view of a thunk of an `&` is
    obtain ⟨T, hT, hcT⟩ := der_var hf i rfl
    obtain rfl := hi T (splitP_le_right hs _ _ hT)
    have := vview_thunk hcT.val
    cases this
  · cases hi'
  · cases hN
  · cases hN
  · cases hu
  · cases hu
  · cases hu
  · -- the second projection: `κ` read at `C & D`, so `D` is `⊤`
    obtain ⟨T, hT, hcT⟩ := der_var hX i rfl
    obtain rfl := hi T hT
    rcases hcT with ⟨S', Y, he, -⟩ | ⟨C₀, hC₀, -, hr'⟩
    · exact (effOf_ne_amp _ _ _ _ he.symm).elim
    · simp only [kTy, VTy.thunk.injEq] at hC₀
      subst hC₀
      obtain ⟨-, rfl⟩ := hr'.amp_amp
      exact hr
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ | ⟨_, hX₁, hX₂, -⟩ <;>
      first | cases hX | (cases hX₂; done) | (cases hX₁; done)

/-- **R1's clause is refused at a resuming must-resume or cancellable operation**: `return ff`
consumes its context, where the slot of `k : kTy` is live, and `kTy` is not persistent. -/
theorem refuses_dropClause {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} {F : CTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerives Δ Γ dropCl.1 (.val (clauseTy S R (q, A, B) F)) := by
  intro h
  obtain ⟨Γb, C, hX, -⟩ := der_clause_body (X := .inj₁ .unit) hres (by not_withPair)
    (by not_const) h
  obtain ⟨A₁, B₁, hu, -⟩ := der_inj₁ hX _ rfl
  rcases der_unit hu rfl with ⟨hd, -⟩ | hr
  · exact kTy_not_persistent hq (deadP_slot hd (k := 0) rfl)
  · obtain ⟨S', Y, he⟩ := hr.comp_val
    exact effOf_ne_top S' Y he.symm

/-- **R2's clause is refused at a resuming must-resume or cancellable operation**:
`resume k () to _. resume k ()` reads `k` on both sides of a bind, so its slot would be
persistent. -/
theorem refuses_twiceClause {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} {F : CTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerives Δ Γ twiceCl.1 (.val (clauseTy S R (q, A, B) F)) := by
  intro h
  obtain ⟨Γb, C, hX, -⟩ := der_clause_body (X := twiceBody) hres
    (by simp only [twiceBody, resumeE]; not_withPair)
    (by simp only [twiceBody, resumeE]; not_const) h
  exact kTy_not_persistent hq (k_twice hX (by simp [resumeE]) (by simp [resumeE])
    (by simp [resumeE]) (by simp [resumeE]) (by simp [resumeE])
    (by simp only [resumeE]; not_withPair) (by simp only [resumeE]; not_const)
    (by simp [resumeE, Expr.HasVar, Expr.shift]) (by simp [resumeE, Expr.HasVar, Expr.shift]))

/-- **R4's clause is refused at a resuming must-resume or cancellable operation**: `cancel k to _.
resume k ()` reads `k` on both sides of a bind. -/
theorem refuses_cancelResumeClause {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual}
    {A B : VTy} {F : CTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerives Δ Γ cancelResumeCl.1 (.val (clauseTy S R (q, A, B) F)) := by
  intro h
  obtain ⟨Γb, C, hX, -⟩ := der_clause_body (X := cancelResumeBody) hres
    (by simp only [cancelResumeBody, cancelE, resumeE]; not_withPair)
    (by simp only [cancelResumeBody, cancelE, resumeE]; not_const) h
  exact kTy_not_persistent hq (k_twice hX (by simp [cancelE]) (by simp [cancelE])
    (by simp [cancelE]) (by simp [cancelE]) (by simp [cancelE])
    (by simp only [resumeE]; not_withPair) (by simp only [resumeE]; not_const)
    (by simp [cancelE, Expr.HasVar]) (by simp [resumeE, Expr.HasVar, Expr.shift]))

/-- **R3's clause is refused at a must-resume operation**: a must-resume `κ`'s cancel is at `⊤` only
(`der_cancel_lin`), and a bind takes its computation at a row. -/
theorem refuses_cancelClause_lin {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {A B : VTy}
    {F : CTy} : ¬ CDerives Δ Γ cancelCl.1 (.val (clauseTy S R (.lin, A, B) F)) := by
  intro h
  obtain ⟨Γb, C, hX, -⟩ := der_clause_body (X := cancelBody) (by simp)
    (by simp only [cancelBody, cancelE]; not_withPair)
    (by simp only [cancelBody, cancelE]; not_const) h
  obtain ⟨Γ₁, Γ₂, T, b, S', j', hs, hM, -⟩ := der_bind_split hX (by simp [cancelE])
    (by simp [cancelE]) (by simp [cancelE]) (by simp [cancelE]) (by simp [cancelE])
    (by not_withPair) (by not_const)
  have hc := der_cancel_lin (S := S) (R := R) (B := B) (F := F) hM (fun T hT => by
    have := splitP_le_left hs 0 T hT
    simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at this
    exact this.symm)
  have := hc.rigid rigid_top
  simp only [Jdg.comp.injEq] at this
  exact effOf_ne_top _ _ this

/-- **The clause typing refuses R1–R4's clauses** at the classes S6's witnesses name: R1, R2 and R4
at every resuming must-resume or cancellable operation, R3 at every must-resume one, at every cancel
row. -/
theorem refuses_R_clauses {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {q : Qual} {A B : VTy}
    {F : CTy} (hq : q ≠ .unr) (hres : (B.isZero && q != .lin) = false) :
    ¬ CDerives Δ Γ dropCl.1 (.val (clauseTy S R (q, A, B) F)) ∧
    ¬ CDerives Δ Γ twiceCl.1 (.val (clauseTy S R (q, A, B) F)) ∧
    ¬ CDerives Δ Γ cancelCl.1 (.val (clauseTy S R (.lin, A, B) F)) ∧
    ¬ CDerives Δ Γ cancelResumeCl.1 (.val (clauseTy S R (q, A, B) F)) :=
  ⟨refuses_dropClause hq hres, refuses_twiceClause hq hres, refuses_cancelClause_lin,
    refuses_cancelResumeClause hq hres⟩

/-! ### The refusals pin `κ`'s use -/

open EffExamples in
/-- **A clause that cancels `κ` is refused at a must-resume operation**: `x; κ (inj₂ ())` answers at
`⊤`, and the clause at a row. -/
theorem refuses_clC_lin {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R : VTy} {A B : VTy} {F : CTy} :
    ¬ CDerives Δ Γ clC (.val (clauseTy S R (.lin, A, B) F)) := by
  intro h
  obtain ⟨Γb, C, hX, hr⟩ := der_clause_body (X := .seq (.var 1) (cancelE (.var 0))) (by simp)
    (by simp only [cancelE]; not_withPair) (by simp only [cancelE]; not_const) h
  obtain ⟨Γ₁, Γ₂, C', hs, -, hM, hr'⟩ := der_seq hX _ _ rfl
  have hc := der_cancel_lin (S := S) (R := R) (B := B) (F := F) hM (fun T hT => by
    have := splitP_le_right hs 0 T hT
    simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at this
    exact this.symm)
  have := JR.rigid ((hc.trans hr').trans hr) rigid_top
  simp only [Jdg.comp.injEq] at this
  exact effOf_ne_top _ _ this

open EffExamples in
/-- **The refusals are of `κ`'s use, not of the clauses' form.**  At the clause type of a
must-resume operation `1 ↠ 1`, a clause that resumes `κ` once is typed (`cl₀`) and R1–R4's clauses
are not; a clause that cancels `κ` (`clC`) is typed at a cancellable operation and refused at a
must-resume one. -/
theorem clauseRefusals_pinned :
    (CDerives LifeCtx.empty [] cl₀ (.val (clauseTy [] .unit (.lin, .unit, .unit))) ∧
      ¬ CDerives LifeCtx.empty [] dropCl.1 (.val (clauseTy [] .unit (.lin, .unit, .unit))) ∧
      ¬ CDerives LifeCtx.empty [] twiceCl.1 (.val (clauseTy [] .unit (.lin, .unit, .unit))) ∧
      ¬ CDerives LifeCtx.empty [] cancelCl.1 (.val (clauseTy [] .unit (.lin, .unit, .unit))) ∧
      ¬ CDerives LifeCtx.empty [] cancelResumeCl.1
        (.val (clauseTy [] .unit (.lin, .unit, .unit)))) ∧
    (CDerives LifeCtx.empty [] clC (.val (clauseTy [] .unit (.cancel, .unit, .unit))) ∧
      ¬ CDerives LifeCtx.empty [] clC (.val (clauseTy [] .unit (.lin, .unit, .unit)))) :=
  ⟨⟨cl₀_derives, refuses_dropClause (by simp) (by simp), refuses_twiceClause (by simp) (by simp),
      refuses_cancelClause_lin, refuses_cancelResumeClause (by simp) (by simp)⟩,
    clC_derives, refuses_clC_lin⟩

end BoCa.Fig16.LogRel.Core.Inversions

end
