import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.Statics.Contexts

/-!
# Support — Statics — Presupposed

`[about ours]`.  `Δ.Ok` (sufficient for `⊧ Δ`, `sat_of_ok`), `Ty.wfB`/`Ty.scopedB`
(`Δ ⊢ T`), `Ctx.ScopedB` (`Δ ⊢ Γ`) and `DerivesWf`, with the facts about lifetime
interpretation and fresh variables they need.  `DerivesWf` is p. 2's typing rules with
p. 2's `Δ ⊢ T` consulted at binders and eliminated types; the Fundamental Property takes
`⊧ Δ` (as `Δ.Ok`, sufficient) and `Δ ⊢ Γ` (`Ctx.ScopedB`) as hypotheses, which p. 2's
typing box does not print (`docs/adjudications.md` §C.26).
-/

noncomputable section

namespace BoCa.Lifetime.LSub

def empty : LSub := ⟨[]⟩

theorem find?_extend (δ : LSub) (x : LifeVar) (v : Nat) (y : LifeVar) :
    (δ.extend x v).find? y = if x = y then some v else δ.find? y := by
  simp [find?, extend, assocFind]

end BoCa.Lifetime.LSub

namespace BoCa.Lifetime

theorem Life.interp_join_some {δ : LSub} {a b : Life} {p q : Nat}
    (ha : a.interp δ = some p) (hb : b.interp δ = some q) :
    (Life.join a b).interp δ = some (SLife.join p q) := by
  simp [Life.interp, ha, hb]

theorem Life.interp_meet_some {δ : LSub} {a b : Life} {p q : Nat}
    (ha : a.interp δ = some p) (hb : b.interp δ = some q) :
    (Life.meet a b).interp δ = some (SLife.meet p q) := by
  simp [Life.interp, ha, hb]

end BoCa.Lifetime

namespace BoCa.Lifetime.LifeCtx

def empty : LifeCtx := ⟨[]⟩

theorem find?_extend (Δ : LifeCtx) (x : LifeVar) (u : Life) (y : LifeVar) :
    (Δ.extend x u).find? y = if x = y then some u else Δ.find? y := by
  simp [find?, extend, assocFind]

end BoCa.Lifetime.LifeCtx

namespace BoCa.Lifetime

theorem Life.interp_defined_of_wf {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) :
    ∀ {a : Life}, a.wf Δ = true → ∃ n, a.interp δ = some n := by
  intro a
  induction a with
  | var x =>
    intro h
    simp only [Life.wf] at h
    cases hu : Δ.find? x with
    | none => rw [hu] at h; simp at h
    | some u =>
      obtain ⟨m, _, hm, _, _⟩ := hδ x u hu
      exact ⟨m, hm⟩
  | top => intro _; exact ⟨SLife.top, rfl⟩
  | join a b iha ihb =>
    intro h
    simp only [Life.wf, Bool.and_eq_true] at h
    obtain ⟨p, hp⟩ := iha h.1
    obtain ⟨q, hq⟩ := ihb h.2
    exact ⟨SLife.join p q, Life.interp_join_some hp hq⟩
  | meet a b iha ihb =>
    intro h
    simp only [Life.wf, Bool.and_eq_true] at h
    obtain ⟨p, hp⟩ := iha h.1
    obtain ⟨q, hq⟩ := ihb h.2
    exact ⟨SLife.meet p q, Life.interp_meet_some hp hq⟩

/-- `Δ` is well-scoped: distinct binders, each bound closed under the strictly
    outer context. -/
def LifeCtx.Ok (Δ : LifeCtx) : Prop := okB Δ.entries = true

instance (Δ : LifeCtx) : Decidable Δ.Ok := inferInstanceAs (Decidable (_ = true))

/-- `⊨ Δ` survives the `∀` rule's binder.  `[TR]` p. 2 reads
`∆, ('a ⊏ @b) ⊢ T` under the same presupposition as its conclusion, and the
rule's other premise is `∆ ⊧ @b`; `okB`'s new entry asks those two against a
binder outside `dom(∆)`.
`[about ours: `LifeCtx.Ok` at [TR] p. 2's `∀` rule's extension]` -/
theorem LifeCtx.Ok.extend {Δ : LifeCtx} {x : LifeVar} {u : Life}
    (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hu : u.wf Δ = true) :
    (LifeCtx.extend Δ x u).Ok := by
  have hn : (assocFind x Δ.entries).isNone = true := by
    rw [show assocFind x Δ.entries = Δ.find? x from rfl, hx]; rfl
  show okB ((x, u) :: Δ.entries) = true
  rw [okB, hn, show (⟨Δ.entries⟩ : LifeCtx) = Δ from rfl, hu, hΔ]
  rfl

theorem Life.wf_mono {t : List (LifeVar × Life)} {x : LifeVar} {u : Life} :
    ∀ {a : Life}, a.wf ⟨t⟩ = true → a.wf ⟨(x, u) :: t⟩ = true := by
  intro a
  induction a with
  | var y =>
    intro h
    simp only [Life.wf, LifeCtx.find?, assocFind] at h ⊢
    by_cases hxy : x = y
    · simp [hxy]
    · rw [if_neg hxy]; exact h
  | top => intro _; rfl
  | join a b iha ihb =>
    intro h; simp only [Life.wf, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | meet a b iha ihb =>
    intro h; simp only [Life.wf, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩

/-- Inserting a binding for a different variable leaves a lookup unfound.
    `[about ours: `assocFind` under the `∀` rule's extension]` -/
theorem assocFind_none_insert {β : Type} {y x : LifeVar} {u : β} :
    ∀ {t₁ t₂ : List (LifeVar × β)}, x ≠ y → assocFind y (t₁ ++ t₂) = none →
      assocFind y (t₁ ++ (x, u) :: t₂) = none := by
  intro t₁
  induction t₁ with
  | nil => intro t₂ hxy h; simp only [List.nil_append, assocFind]; rw [if_neg hxy]; exact h
  | cons hd t ih =>
      intro t₂ hxy h
      simp only [List.cons_append, assocFind] at h ⊢
      by_cases hz : hd.1 = y
      · rw [if_pos hz] at h; exact absurd h (by simp)
      · rw [if_neg hz] at h ⊢; exact ih hxy h

/-- …and it leaves a found lookup found, whatever the variable.
    `[about ours: `assocFind` under the `∀` rule's extension]` -/
theorem assocFind_isSome_insert {β : Type} {y x : LifeVar} {u : β} :
    ∀ {t₁ t₂ : List (LifeVar × β)}, (assocFind y (t₁ ++ t₂)).isSome = true →
      (assocFind y (t₁ ++ (x, u) :: t₂)).isSome = true := by
  intro t₁
  induction t₁ with
  | nil =>
      intro t₂ h
      simp only [List.nil_append, assocFind] at h ⊢
      by_cases hxy : x = y
      · rw [if_pos hxy]; rfl
      · rw [if_neg hxy]; exact h
  | cons hd t ih =>
      intro t₂ h
      simp only [List.cons_append, assocFind] at h ⊢
      by_cases hz : hd.1 = y
      · rw [if_pos hz] at h ⊢; exact h
      · rw [if_neg hz] at h ⊢; exact ih h

/-- `Δ ⊨ @a` survives an insertion anywhere in the context: `Life.wf` asks only
    that each mentioned variable be bound, and an insertion binds more.
    `[about ours: `Life.wf` under the `∀` rule's extension]` -/
theorem Life.wf_insert {x : LifeVar} {u : Life} :
    ∀ {a : Life} {t₁ t₂ : List (LifeVar × Life)},
      a.wf ⟨t₁ ++ t₂⟩ = true → a.wf ⟨t₁ ++ (x, u) :: t₂⟩ = true := by
  intro a
  induction a with
  | var y => intro t₁ t₂ h; exact assocFind_isSome_insert (u := u) h
  | top => intro _ _ _; rfl
  | join a b iha ihb =>
      intro t₁ t₂ h; simp only [Life.wf, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | meet a b iha ihb =>
      intro t₁ t₂ h; simp only [Life.wf, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩

/-- In a well-scoped context every bound is closed under the whole context. -/
theorem okB_bound_wf : ∀ {t : List (LifeVar × Life)}, okB t = true →
    ∀ {y : LifeVar} {w : Life}, assocFind y t = some w → Life.wf ⟨t⟩ w = true := by
  intro t
  induction t with
  | nil => intro _ y w h; simp [assocFind] at h
  | cons e t ih =>
    obtain ⟨x, u⟩ := e
    intro hok y w h
    simp only [okB, Bool.and_eq_true] at hok
    simp only [assocFind] at h
    by_cases hxy : x = y
    · rw [if_pos hxy] at h
      have : w = u := (Option.some.inj h).symm
      subst this
      exact Life.wf_mono hok.1.2
    · rw [if_neg hxy] at h
      exact Life.wf_mono (ih hok.2 h)

/-- Interpretation is stable under extending `δ` with a variable the context
    does not bind. -/
theorem Life.interp_extend {t : List (LifeVar × Life)} {δ : LSub} {x : LifeVar}
    {v : Nat} (hx : assocFind x t = none) :
    ∀ {a : Life}, a.wf ⟨t⟩ = true → a.interp (δ.extend x v) = a.interp δ := by
  intro a
  induction a with
  | var y =>
    intro h
    simp only [Life.wf, LifeCtx.find?] at h
    have hne : x ≠ y := by
      intro he; subst he; rw [hx] at h; simp at h
    simp [Life.interp, LSub.find?_extend, hne]
  | top => intro _; rfl
  | join a b iha ihb =>
    intro h
    simp only [Life.wf, Bool.and_eq_true] at h
    simp [Life.interp, iha h.1, ihb h.2]
  | meet a b iha ihb =>
    intro h
    simp only [Life.wf, Bool.and_eq_true] at h
    simp [Life.interp, iha h.1, ihb h.2]

/-- The canonical substitution: give each variable a value one greater than
    (= a lifetime one shorter than) the interpretation of its bound.  Built
    outermost-first, which is why `LifeCtx.Ok` demands each bound be closed
    under the tail. -/
def canonList : List (LifeVar × Life) → LSub
  | []          => LSub.empty
  | (x, u) :: t => (canonList t).extend x ((Life.interp (canonList t) u).getD 0 + 1)

def LifeCtx.canonical (Δ : LifeCtx) : LSub := canonList Δ.entries

theorem canonList_dom : ∀ (t : List (LifeVar × Life)) (x : LifeVar),
    ((canonList t).find? x).isSome = (assocFind x t).isSome := by
  intro t
  induction t with
  | nil => intro x; simp [canonList, LSub.find?, LSub.empty, assocFind]
  | cons e t ih =>
    obtain ⟨y, u⟩ := e
    intro x
    simp only [canonList, assocFind, LSub.find?_extend]
    by_cases h : y = x <;> simp [h, ih x]

theorem Life.wf_canon {t : List (LifeVar × Life)} :
    ∀ {a : Life}, a.wf ⟨t⟩ = true → ∃ n, a.interp (canonList t) = some n := by
  intro a
  induction a with
  | var x =>
    intro h
    simp only [Life.wf, LifeCtx.find?] at h
    have hd := canonList_dom t x
    rw [h] at hd
    cases hv : (canonList t).find? x with
    | none => rw [hv] at hd; simp at hd
    | some n => exact ⟨n, by simp [Life.interp, hv]⟩
  | top => intro _; exact ⟨SLife.top, rfl⟩
  | join a b iha ihb =>
    intro h
    simp only [Life.wf, Bool.and_eq_true] at h
    obtain ⟨p, hp⟩ := iha h.1; obtain ⟨q, hq⟩ := ihb h.2
    exact ⟨SLife.join p q, Life.interp_join_some hp hq⟩
  | meet a b iha ihb =>
    intro h
    simp only [Life.wf, Bool.and_eq_true] at h
    obtain ⟨p, hp⟩ := iha h.1; obtain ⟨q, hq⟩ := ihb h.2
    exact ⟨SLife.meet p q, Life.interp_meet_some hp hq⟩

theorem canonList_models : ∀ {t : List (LifeVar × Life)}, okB t = true →
    LifeCtx.Models ⟨t⟩ (canonList t) := by
  intro t
  induction t with
  | nil => intro _ x u h; simp [LifeCtx.find?, assocFind] at h
  | cons e t ih =>
    obtain ⟨x, u⟩ := e
    intro hok y w hy
    simp only [okB, Bool.and_eq_true] at hok
    obtain ⟨⟨hnone, huwf⟩, hokt⟩ := hok
    have hxfresh : assocFind x t = none := Option.isNone_iff_eq_none.mp hnone
    have hstep : canonList ((x, u) :: t)
        = (canonList t).extend x ((Life.interp (canonList t) u).getD 0 + 1) := rfl
    simp only [LifeCtx.find?, assocFind] at hy
    by_cases hxy : x = y
    · -- the head binding
      rw [if_pos hxy] at hy
      have hwu : w = u := (Option.some.inj hy).symm
      subst hwu
      obtain ⟨k, hk⟩ := Life.wf_canon huwf
      refine ⟨k + 1, k, ?_, ?_, ?_⟩
      · rw [hstep, LSub.find?_extend, if_pos hxy, hk]; rfl
      · rw [hstep, Life.interp_extend hxfresh huwf, hk]
      · simp only [SLife.Lt]; omega
    · -- an inherited binding
      rw [if_neg hxy] at hy
      obtain ⟨m, n, hm, hn, hlt⟩ := ih hokt y w (by simpa [LifeCtx.find?] using hy)
      refine ⟨m, n, ?_, ?_, hlt⟩
      · rw [hstep, LSub.find?_extend, if_neg hxy, hm]
      · rw [hstep, Life.interp_extend hxfresh (okB_bound_wf hokt hy), hn]

theorem meetOfDomL_wf : ∀ (t : List (LifeVar × Life)),
    Life.wf ⟨t⟩ (meetOfDomL t) = true := by
  intro t
  induction t with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨x, u⟩ := e
    simp only [meetOfDomL, Life.wf, Bool.and_eq_true]
    refine ⟨?_, Life.wf_mono ih⟩
    simp [LifeCtx.find?, assocFind]

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- `Δ ⊢ T`, decided.  Nine of the ten constructors, as [TR] p. 2 prints
them; `Unk` has no rule there, so no type mentioning it passes.

Two clauses say more than `BoCa.WfTy` records.  The `∀` rule's premise is
`Δ, ('a ⊏ @b) ⊢ T`, an extension, so `'a ∉ dom(Δ)` is asked here (row 2.25).
`Δ ⊨ @a` is asked as `Life.wf`, which implies it and differs only at an
unsatisfiable `Δ`, which p. 2's box for `Δ ⊢ T` excludes by "Presumes ⊨ Δ"
(row 2.19).
`[about ours: the decidable sufficient condition for [TR] p. 2's `Δ ⊢ T`]` -/
def Ty.wfB : Ty → LifeCtx → Bool
  | .unit,         _ => true
  | .unk,          _ => false
  | .ref T,        Δ => T.wfB Δ
  | .sum    T₁ T₂, Δ => T₁.wfB Δ && T₂.wfB Δ
  | .tensor T₁ T₂, Δ => T₁.wfB Δ && T₂.wfB Δ
  | .lolli  T₁ T₂, Δ => T₁.wfB Δ && T₂.wfB Δ
  | .fn  T₁ T₂, Δ => T₁.wfB Δ && T₂.wfB Δ
  | .box a T,      Δ => a.wf Δ && T.wfB Δ
  | .imm a T,      Δ => a.wf Δ && T.wfB Δ
  | .mut a T,      Δ => a.wf Δ && T.wfB Δ
  | .all y b T,    Δ => (Δ.find? y).isNone && b.wf Δ && T.wfB (Δ.extend y b)

/-- `'x` is a binder of `T` — a `∀` former's own variable, at any depth (not
    `LFree`, which is about occurrences).  `Ty.wfB`'s `∀` clause asks the binder
    to be outside `dom(Δ)` (row 2.25), so an extension can collide with binders.
    `[about ours: the Barendregt side of `Ty.wfB`'s `∀` clause]` -/
def Ty.bindsB : Ty → LifeVar → Bool
  | .unit,         _ => false
  | .unk,          _ => false
  | .ref T,        x => T.bindsB x
  | .sum    T₁ T₂, x => T₁.bindsB x || T₂.bindsB x
  | .tensor T₁ T₂, x => T₁.bindsB x || T₂.bindsB x
  | .lolli  T₁ T₂, x => T₁.bindsB x || T₂.bindsB x
  | .fn  T₁ T₂, x => T₁.bindsB x || T₂.bindsB x
  | .box _ T,      x => T.bindsB x
  | .imm _ T,      x => T.bindsB x
  | .mut _ T,      x => T.bindsB x
  | .all y _ T,    x => (y == x) || T.bindsB x

/-- `T` is well-scoped in `Δ` — `Ty.wfB` except at `Unk`, which `Ty.wfB` refuses
    because [TR] p. 2 prints no formation rule for it, while p. 3's axiom table
    types `forget : Unk ⊸ 1` and `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` puts `Unk` inside
    `withload`'s type at every function payload.
    `[about ours: the scoping half of [TR] p. 2's `Δ ⊢ T`]` -/
def Ty.scopedB : Ty → LifeCtx → Bool
  | .unit,         _ => true
  | .unk,          _ => true
  | .ref T,        Δ => T.scopedB Δ
  | .sum    T₁ T₂, Δ => T₁.scopedB Δ && T₂.scopedB Δ
  | .tensor T₁ T₂, Δ => T₁.scopedB Δ && T₂.scopedB Δ
  | .lolli  T₁ T₂, Δ => T₁.scopedB Δ && T₂.scopedB Δ
  | .fn  T₁ T₂, Δ => T₁.scopedB Δ && T₂.scopedB Δ
  | .box a T,      Δ => a.wf Δ && T.scopedB Δ
  | .imm a T,      Δ => a.wf Δ && T.scopedB Δ
  | .mut a T,      Δ => a.wf Δ && T.scopedB Δ
  | .all y b T,    Δ => (Δ.find? y).isNone && b.wf Δ && T.scopedB (Δ.extend y b)

/-- A type `Δ ⊢ T` admits is scoped in `Δ`: the two differ only where `Ty.wfB`
    refuses `Unk` outright. -/
theorem Ty.scopedB_of_wfB : ∀ {T : Ty} {Δ : LifeCtx},
    T.wfB Δ = true → T.scopedB Δ = true := by
  intro T
  induction T with
  | unit => intro _ _; rfl
  | unk => intro _ _; rfl
  | ref T ih => intro Δ h; exact ih h
  | sum T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | lolli T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | fn T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ h.1, ih₂ h.2⟩
  | box a T ih =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2⟩
  | imm a T ih =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2⟩
  | «mut» a T ih =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2⟩
  | all y b T ih =>
      intro Δ h; simp only [Ty.wfB, Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, h.1.2⟩, ih h.2⟩

/-- Scoping survives an insertion the type does not bind. -/
theorem Ty.scopedB_insert (x : LifeVar) (u : Life) :
    ∀ (T : Ty) (t₁ t₂ : List (LifeVar × Life)),
      T.bindsB x = false → T.scopedB ⟨t₁ ++ t₂⟩ = true →
        T.scopedB ⟨t₁ ++ (x, u) :: t₂⟩ = true := by
  intro T
  induction T with
  | unit => intro _ _ _ _; rfl
  | unk => intro _ _ _ _; rfl
  | ref T ih => intro t₁ t₂ hb h; exact ih t₁ t₂ hb h
  | sum T₁ T₂ ih₁ ih₂ =>
      intro t₁ t₂ hb h
      simp only [Ty.bindsB, Bool.or_eq_false_iff] at hb
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ t₁ t₂ hb.1 h.1, ih₂ t₁ t₂ hb.2 h.2⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro t₁ t₂ hb h
      simp only [Ty.bindsB, Bool.or_eq_false_iff] at hb
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ t₁ t₂ hb.1 h.1, ih₂ t₁ t₂ hb.2 h.2⟩
  | lolli T₁ T₂ ih₁ ih₂ =>
      intro t₁ t₂ hb h
      simp only [Ty.bindsB, Bool.or_eq_false_iff] at hb
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ t₁ t₂ hb.1 h.1, ih₂ t₁ t₂ hb.2 h.2⟩
  | fn T₁ T₂ ih₁ ih₂ =>
      intro t₁ t₂ hb h
      simp only [Ty.bindsB, Bool.or_eq_false_iff] at hb
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ t₁ t₂ hb.1 h.1, ih₂ t₁ t₂ hb.2 h.2⟩
  | box a T ih =>
      intro t₁ t₂ hb h
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨Life.wf_insert h.1, ih t₁ t₂ hb h.2⟩
  | imm a T ih =>
      intro t₁ t₂ hb h
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨Life.wf_insert h.1, ih t₁ t₂ hb h.2⟩
  | «mut» a T ih =>
      intro t₁ t₂ hb h
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      exact ⟨Life.wf_insert h.1, ih t₁ t₂ hb h.2⟩
  | all y b T ih =>
      intro t₁ t₂ hb h
      simp only [Ty.bindsB, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hb
      simp only [Ty.scopedB, Bool.and_eq_true] at h ⊢
      refine ⟨⟨?_, Life.wf_insert h.1.2⟩, ?_⟩
      · rw [Option.isNone_iff_eq_none] at h ⊢
        exact assocFind_none_insert (u := u) (Ne.symm hb.1) h.1.1
      · exact ih ((y, b) :: t₁) t₂ hb.2 h.2

@[inherit_doc Ty.scopedB_insert]
theorem Ty.scopedB_extend {T : Ty} {Δ : LifeCtx} {x : LifeVar} {u : Life}
    (hb : T.bindsB x = false) (h : T.scopedB Δ = true) :
    T.scopedB (Δ.extend x u) = true :=
  Ty.scopedB_insert x u T [] Δ.entries hb h

end BoCa

namespace BoCa.Lifetime
open BoCa.Lifetime

/-- A lifetime `Δ` closes mentions no variable `Δ` does not bind.  This is
what [TR]'s Barendregt convention gets from `Δ ⊨ @b` at a binder taken fresh:
`'a ∉ dom(Δ)` and `Δ ⊨ @b` together say `@b` does not mention `'a`. -/
theorem Life.mentions_false_of_wf {Δ : LifeCtx} {x : LifeVar}
    (hx : Δ.find? x = none) : ∀ {a : Life}, a.wf Δ = true → a.mentions x = false := by
  intro a
  induction a with
  | var y =>
      intro h
      simp only [Life.wf] at h
      by_cases hxy : x = y
      · subst hxy; rw [hx] at h; simp at h
      · simp [Life.mentions, hxy]
  | top => intro _; rfl
  | join a b iha ihb =>
      intro h
      simp only [Life.wf, Bool.and_eq_true] at h
      simp [Life.mentions, iha h.1, ihb h.2]
  | meet a b iha ihb =>
      intro h
      simp only [Life.wf, Bool.and_eq_true] at h
      simp [Life.mentions, iha h.1, ihb h.2]

/-- In a well-scoped `Δ`, no bound mentions a variable `Δ` does not bind.
`AllISide`'s second conjunct, off `okB_bound_wf`. -/
theorem LifeCtx.Ok.bound_mentions_false {Δ : LifeCtx} {x : LifeVar} (hΔ : Δ.Ok)
    (hx : Δ.find? x = none) {y : LifeVar} {u : Life} (hy : Δ.find? y = some u) :
    u.mentions x = false :=
  Life.mentions_false_of_wf hx (okB_bound_wf hΔ hy)

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- `Δ ⊢ Γ` at the scoping half — `Ty.scopedB` at every live slot, a consumed slot being out
    of scope (convention L4).
    `[about ours: [TR] p. 2's `Δ ⊢ T` lifted to a positional context]` -/
def Ctx.ScopedB (Δ : LifeCtx) (Γ : Ctx Ty) : Prop :=
  ∀ s ∈ Γ, s.live = true → s.ty.scopedB Δ = true

/-- `Γ = Γ₁, Γ₂` keeps every slot's type and only turns liveness off, so each
    half asks a subset of what `Γ` asks. -/
theorem Ctx.ScopedB.split_left {Δ : LifeCtx} : ∀ {Γ Γ₁ Γ₂ : Ctx Ty},
    Ctx.Split Γ Γ₁ Γ₂ → Ctx.ScopedB Δ Γ → Ctx.ScopedB Δ Γ₁ := by
  intro Γ Γ₁ Γ₂ hs
  induction hs with
  | nil => intro _ s hm; exact absurd hm (by simp)
  | @left Γ' Γ₁' Γ₂' T _ ih =>
      intro h s hm hl
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact h ⟨T, true⟩ (by simp) rfl
      · exact ih (fun t ht => h t (by simp [ht])) s hm' hl
  | @right Γ' Γ₁' Γ₂' T _ ih =>
      intro h s hm hl
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd hl (by simp)
      · exact ih (fun t ht => h t (by simp [ht])) s hm' hl
  | @dead Γ' Γ₁' Γ₂' T _ ih =>
      intro h s hm hl
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd hl (by simp)
      · exact ih (fun t ht => h t (by simp [ht])) s hm' hl

@[inherit_doc Ctx.ScopedB.split_left]
theorem Ctx.ScopedB.split_right {Δ : LifeCtx} : ∀ {Γ Γ₁ Γ₂ : Ctx Ty},
    Ctx.Split Γ Γ₁ Γ₂ → Ctx.ScopedB Δ Γ → Ctx.ScopedB Δ Γ₂ := by
  intro Γ Γ₁ Γ₂ hs
  induction hs with
  | nil => intro _ s hm; exact absurd hm (by simp)
  | @left Γ' Γ₁' Γ₂' T _ ih =>
      intro h s hm hl
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd hl (by simp)
      · exact ih (fun t ht => h t (by simp [ht])) s hm' hl
  | @right Γ' Γ₁' Γ₂' T _ ih =>
      intro h s hm hl
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact h ⟨T, true⟩ (by simp) rfl
      · exact ih (fun t ht => h t (by simp [ht])) s hm' hl
  | @dead Γ' Γ₁' Γ₂' T _ ih =>
      intro h s hm hl
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd hl (by simp)
      · exact ih (fun t ht => h t (by simp [ht])) s hm' hl

/-- A binder's slot, at the type the rule binds. -/
theorem Ctx.ScopedB.cons {Δ : LifeCtx} {Γ : Ctx Ty} {T : Ty} {b : Bool}
    (hT : b = true → T.scopedB Δ = true) (h : Ctx.ScopedB Δ Γ) : Ctx.ScopedB Δ (⟨T, b⟩ :: Γ) := by
  intro s hm hl
  rcases List.mem_cons.mp hm with rfl | hm'
  · exact hT hl
  · exact h s hm' hl

/-- `Δ ⊢ Γ` survives the `∀` rule's extension, at a binder none of the live
    slots binds (`Ty.bindsB`). -/
theorem Ctx.ScopedB.extend {Δ : LifeCtx} {Γ : Ctx Ty} {x : LifeVar} {u : Life}
    (hb : ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false) (h : Ctx.ScopedB Δ Γ) :
    Ctx.ScopedB (LifeCtx.extend Δ x u) Γ :=
  fun s hm hl => Ty.scopedB_extend (hb s hm hl) (h s hm hl)

/-- `Δ ⊢ Γ` at `∀I`'s premise: the rule's new slot is consumed, and `Γ` moves
    across the extension. -/
theorem Ctx.ScopedB.allI {Δ : LifeCtx} {Γ : Ctx Ty} {x : LifeVar} {b : Life} {S : Ty}
    (hb : ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false) (h : Ctx.ScopedB Δ Γ) :
    Ctx.ScopedB (LifeCtx.extend Δ x b) (⟨S, false⟩ :: Γ) :=
  Ctx.ScopedB.cons (fun hl => absurd hl (by simp)) (Ctx.ScopedB.extend hb h)

/-- A split only turns liveness bits off, so each half asks no more of `γ` than
    the whole did. -/
theorem Ctx.Split.liveWithin {τ σ : Type} {Γ Γ₁ Γ₂ : Ctx τ}
    (h : Ctx.Split Γ Γ₁ Γ₂) {γ : List σ} (hg : Ctx.LiveWithin Γ γ) :
    Ctx.LiveWithin Γ₁ γ ∧ Ctx.LiveWithin Γ₂ γ := by
  induction h generalizing γ with
  | nil => simp
  | @left Γ' Γ₁' Γ₂' T _ ih => cases γ with
    | nil => exact absurd hg.1 (by simp)
    | cons v γ' => exact ⟨(ih hg).1, (ih hg).2⟩
  | @right Γ' Γ₁' Γ₂' T _ ih => cases γ with
    | nil => exact absurd hg.1 (by simp)
    | cons v γ' => exact ⟨(ih hg).1, (ih hg).2⟩
  | @dead Γ' Γ₁' Γ₂' T _ ih => cases γ with
    | nil => exact ⟨⟨by simp, (ih hg.2).1⟩, ⟨by simp, (ih hg.2).2⟩⟩
    | cons v γ' => exact ⟨(ih hg).1, (ih hg).2⟩

/-- `x : T`'s one live slot is inside `γ`. -/
theorem Ctx.Solo.lt_of_liveWithin {τ σ : Type} {Γ : Ctx τ} {i : Nat} {T : τ}
    (h : Ctx.Solo Γ i T) : ∀ {γ : List σ}, Ctx.LiveWithin Γ γ → i < γ.length := by
  induction h with
  | @here T Γ' _ => intro γ hg; cases γ with
    | nil => exact absurd hg.1 (by simp)
    | cons v γ' => simp
  | @there S T Γ' i' _ ih => intro γ hg; cases γ with
    | nil => exact absurd (ih hg.2) (by simp)
    | cons v γ' => simpa using ih hg

/-- `Ref T₁` is the argument and `Ref T₁ ⊗ T₂` the result, both outside the
    binder.  `[about ours: the scheme's metavariables, off its own type]` -/
theorem scopedB_axWithbor1Ty {Δ : LifeCtx} {x : LifeVar} {bnd : Life} {T₁ T₂ : Ty}
    (h : (axWithbor1Ty x bnd T₁ T₂).scopedB Δ = true) :
    T₁.scopedB Δ = true ∧ T₂.scopedB Δ = true := by
  simp only [axWithbor1Ty, Ty.scopedB, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.2.2⟩

@[inherit_doc scopedB_axWithbor1Ty]
theorem scopedB_axWithbor2Ty {Δ : LifeCtx} {x : LifeVar} {bnd : Life} {T₁ T₂ : Ty}
    (h : (axWithbor2Ty x bnd T₁ T₂).scopedB Δ = true) :
    T₁.scopedB Δ = true ∧ T₂.scopedB Δ = true := by
  simp only [axWithbor2Ty, Ty.scopedB, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.2.2⟩

/-- `Mut @a T₁` is the argument and `Mut @a T₁ ⊗ T₂` the result.
    `[about ours: the scheme's metavariables, off its own type]` -/
theorem scopedB_axWithbor3Ty {Δ : LifeCtx} {a : Life} {x : LifeVar} {bnd : Life} {T₁ T₂ : Ty}
    (h : (axWithbor3Ty a x bnd T₁ T₂).scopedB Δ = true) :
    T₁.scopedB Δ = true ∧ T₂.scopedB Δ = true := by
  simp only [axWithbor3Ty, Ty.scopedB, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2.2.2⟩

/-- `Imm @a T₁` is the argument and `T₂` the result.
    `[about ours: the scheme's metavariables, off its own type]` -/
theorem scopedB_axWithloadTy {Δ : LifeCtx} {a : Life} {x : LifeVar} {bnd : Life} {T₁ T₂ : Ty}
    (h : (axWithloadTy a x bnd T₁ T₂).scopedB Δ = true) :
    T₁.scopedB Δ = true ∧ T₂.scopedB Δ = true := by
  simp only [axWithloadTy, Ty.scopedB, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2.2⟩

inductive DerivesWf : LifeCtx → Ctx Ty → Expr → Ty → Prop where
  | var {Δ Γ i T} (h : Ctx.Solo Γ i T) : DerivesWf Δ Γ (.var i) T
  | unitI {Δ Γ} (h : Ctx.Dead Γ) : DerivesWf Δ Γ (.val .unit) .unit
  | unitE {Δ Γ Γ₁ Γ₂ e₁ e₂ T} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : DerivesWf Δ Γ₁ e₁ .unit) (h₂ : DerivesWf Δ Γ₂ e₂ T) :
      DerivesWf Δ Γ (.seq e₁ e₂) T
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : DerivesWf Δ Γ₁ e₁ T₁) (h₂ : DerivesWf Δ Γ₂ e₂ T₂) :
      DerivesWf Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂)
  /-- `⊗E`, with the eliminated type ranging over the types `Δ ⊢ T` admits;
      that is what puts `x₁ ∶ T₁, x₂ ∶ T₂` inside `Δ ⊢ Γ` at the premise. -/
  | tensorE {Δ Γ Γp Γb ep eb T₁ T₂ T} (hs : Ctx.Split Γ Γp Γb)
      (hwf : (Ty.tensor T₁ T₂).scopedB Δ = true)
      (hp : DerivesWf Δ Γp ep (.tensor T₁ T₂))
      (hb : DerivesWf Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: Γb) eb T) :
      DerivesWf Δ Γ (.letpair ep eb) T
  | sumI₁ {Δ Γ e T₁ T₂} (h : DerivesWf Δ Γ e T₁) :
      DerivesWf Δ Γ (.inj₁ e) (.sum T₁ T₂)
  | sumI₂ {Δ Γ e T₁ T₂} (h : DerivesWf Δ Γ e T₂) :
      DerivesWf Δ Γ (.inj₂ e) (.sum T₁ T₂)
  /-- `⊕E`, with the eliminated type ranging over the types `Δ ⊢ T` admits;
      that is what puts `x_b ∶ T_b` inside `Δ ⊢ Γ` at each branch. -/
  | sumE {Δ Γ Γs Γb es e₁ e₂ T₁ T₂ T} (hs : Ctx.Split Γ Γs Γb)
      (hwf : (Ty.sum T₁ T₂).scopedB Δ = true)
      (h₀ : DerivesWf Δ Γs es (.sum T₁ T₂))
      (h₁ : DerivesWf Δ (⟨T₁, true⟩ :: Γb) e₁ T)
      (h₂ : DerivesWf Δ (⟨T₂, true⟩ :: Γb) e₂ T) :
      DerivesWf Δ Γ (.case es e₁ e₂) T
  /-- `⊸I`, with the argument type ranging over the types `Δ ⊢ T` admits; that
      is what puts `x ∶ T₁` inside `Δ ⊢ Γ` at the premise. -/
  | lolliI {Δ Γ b T₁ T₂} (hwf : T₁.scopedB Δ = true)
      (h : DerivesWf Δ (⟨T₁, true⟩ :: Γ) b T₂) :
      DerivesWf Δ Γ (.val (.lam b)) (.lolli T₁ T₂)
  | lolliE {Δ Γ Γ₁ Γ₂ f a T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (ha : DerivesWf Δ Γ₁ a T₁) (hf : DerivesWf Δ Γ₂ f (.lolli T₁ T₂)) :
      DerivesWf Δ Γ (.app f a) T₂
  /-- `∀I`, with [TR] p. 2's `Δ ⊢ ∀('a ⊏ @b). T` supplying `Δ ⊧ @b` and the
      Barendregt side supplying the binder's freshness for `Γ`'s binders. -/
  | allI {Δ Γ x b S e T} (hx : Δ.find? x = none) (hb : b.wf Δ = true)
      (hnb : ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false)
      (h : DerivesWf (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) :
      DerivesWf Δ Γ (.val (.lam e)) (.all x b T)
  | allE {Δ Γ e x b T a} (h : DerivesWf Δ Γ e (.all x b T)) (hlt : Δ.EntailsLt a b) :
      DerivesWf Δ Γ (.app e (.val .unit)) (Ty.instLife x a T)
  | boxIctx {Δ Γ e T a} (h : DerivesWf Δ Γ e T) (hΓ : Ctx.Outlives Δ Γ a) :
      DerivesWf Δ Γ e (.box a T)
  | boxE {Δ Γ e T a} (h : DerivesWf Δ Γ e (.box a T)) : DerivesWf Δ Γ e T
  | immSub {Δ Γ e a b T} (h : DerivesWf Δ Γ e (.imm b T)) (hle : Δ.EntailsLe a b) :
      DerivesWf Δ Γ e (.imm a T)
  | mutSub {Δ Γ e a b T} (h : DerivesWf Δ Γ e (.mut b T)) (hle : Δ.EntailsLe a b) :
      DerivesWf Δ Γ e (.mut a T)
  | allocAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T))
  | freeAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ (.val (.prim .free)) (.lolli (.ref T) T)
  | swapAx {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ swap (axSwapTy T₁ T₂)
  | copyAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ copy (axCopyTy a T)
  | forgetImmAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ forget (axForgetImmTy a T)
  | forgetMutAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ forget (axForgetMutTy a T)
  | forgetUnkAx {Δ Γ} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ forget axForgetUnkTy
  /-- Form (1), with the table's metavariables ranging over the types
      `Δ ⊢ T` admits. -/
  | withbor1Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hwf : (axWithbor1Ty x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂)
  /-- Form (2), keeping the printed side condition beside it. -/
  | withbor2Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ Outlives Δ T₁ b)
      (hwf : (axWithbor2Ty x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂)
  | withbor3Ax {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hwf : (axWithbor3Ty a x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂)
  | withloadAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hwf : (axWithloadTy a x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂)
  | withswapAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ withswap (axWithswapTy a T₁ T₂)
  /-- `fnI`: a `λ` over a dead context captures nothing, so it is closed code.  `[spec §2]` -/
  | fnI {Δ Γ b T₁ T₂} (hΓ : Ctx.Dead Γ) (hwf : T₁.scopedB Δ = true)
      (h : DerivesWf Δ (⟨T₁, true⟩ :: Γ) b T₂) :
      DerivesWf Δ Γ (.val (.lam b)) (.fn T₁ T₂)
  /-- `fnE`: application.  `[spec §2]` -/
  | fnE {Δ Γ Γ₁ Γ₂ f a T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (ha : DerivesWf Δ Γ₁ a T₁) (hf : DerivesWf Δ Γ₂ f (.fn T₁ T₂)) :
      DerivesWf Δ Γ (.app f a) T₂
  /-- `copy : fn T₁ T₂ ⊸ fn T₁ T₂ ⊗ fn T₁ T₂`.  `[spec §2]` -/
  | copyFnAx {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ copy (.lolli (.fn T₁ T₂) (.tensor (.fn T₁ T₂) (.fn T₁ T₂)))
  /-- `forget : fn T₁ T₂ ⊸ 1`.  `[spec §2]` -/
  | forgetFnAx {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ forget (.lolli (.fn T₁ T₂) .unit)

end BoCa

end
