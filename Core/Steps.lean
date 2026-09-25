import Core.Fundamental
import Paper.Examples.Programs

/-!
# Core — runs through an evaluation context  `[spec §3]`

The machine's steps decompose uniquely: a step of `K[e]`, with `e` not a value, is a step of
`e` under `K` (`step1_plug_inv`), so a run of `K[e]` to a value first runs `e` to a value
(`steps_plug_inv`).  These are the facts a statement about *every* run of a term needs; the
`wp` development only ever builds runs, so the library does not state them.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.BoLo

/-- A value, at each of the forms a redex holds one in. -/
syntax "isv" : tactic
macro_rules
  | `(tactic| isv) => `(tactic| first
      | exact Subtype.property _ | exact IsVal.lam | exact IsVal.prim | exact IsVal.loc
      | exact IsVal.unit | exact IsVal.pair (Subtype.property _) (Subtype.property _)
      | exact IsVal.inj₁ (Subtype.property _) | exact IsVal.inj₂ (Subtype.property _)
      | exact IsVal.storeV IsVal.loc)

/-- A head redex is `K[e]` with `e` not a value only at `K = []`. -/
theorem head_plug {μ μ' : Heap} {E a' : Expr} (hh : Head μ E μ' a') :
    ∀ (K : Kont) {e : Expr}, ¬ IsVal e → E = K.plug e → K = .hole := by
  intro K e hnv hE
  cases K with
  | hole => rfl
  | pairL K e₂ => subst hE; cases hh
  | pairR v K => subst hE; cases hh
  | inj₁ K => subst hE; cases hh
  | inj₂ K => subst hE; cases hh
  | letpair K e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;> first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)
  | case K e₁ e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;> first | (simp at hE; done) | (injection hE with h1 h2 h3; rw [← h1]; isv)
  | seq K e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;> first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)
  | appR f K =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;> first | (simp at hE; done) | (injection hE with h1 h2; rw [← h2]; isv)
  | appL K v =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug] at hE <;> first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)

/-- Unique decomposition: `K[e] = K′[a]` with `a` a redex and `e` not a value puts `a` inside
`e`. -/
theorem plug_decomp {μ μ' : Heap} {a a' : Expr} (hh : Head μ a μ' a') (K : Kont) :
    ∀ (K' : Kont) {e : Expr}, ¬ IsVal e → K.plug e = K'.plug a →
      ∃ K'', e = K''.plug a ∧ K' = K.comp K'' := by
  have hna : ¬ IsVal a := hh.not_isVal
  induction K with
  | hole => intro K' e _ h; exact ⟨K', h, rfl⟩
  | pairL K e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.pairL K e₂) hnv h.symm) (by simp)
      | pairL K' e₂' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | pairR v K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (K.isVal_of_plug (h.1 ▸ v.2)) hnv
      | _ => simp [Kont.plug] at h
  | pairR v K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.pairR v K) hnv h.symm) (by simp)
      | pairL K' e₂' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (K'.isVal_of_plug (h.1 ▸ v.2)) hna
      | pairR v' K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.2
          have hv : v = v' := Subtype.ext h.1
          exact ⟨K'', h₁, by rw [h₂, hv]; rfl⟩
      | _ => simp [Kont.plug] at h
  | letpair K e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.letpair K e₂) hnv h.symm) (by simp)
      | letpair K' e₂' =>
          simp only [Kont.plug, Expr.letpair.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | case K e₁ e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.case K e₁ e₂) hnv h.symm) (by simp)
      | case K' e₁' e₂' =>
          simp only [Kont.plug, Expr.case.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2.1, h.2.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | seq K e₂ ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.seq K e₂) hnv h.symm) (by simp)
      | seq K' e₂' =>
          simp only [Kont.plug, Expr.seq.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          exact ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | inj₁ K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.inj₁ K) hnv h.symm) (by simp)
      | inj₁ K' =>
          simp only [Kont.plug, Expr.inj₁.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h
          exact ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h
  | inj₂ K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.inj₂ K) hnv h.symm) (by simp)
      | inj₂ K' =>
          simp only [Kont.plug, Expr.inj₂.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h
          exact ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h
  | appR f K ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.appR f K) hnv h.symm) (by simp)
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.2
          exact ⟨K'', h₁, by rw [h₂, h.1]; rfl⟩
      | appL K' v =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (K.isVal_of_plug (h.2 ▸ v.2)) hnv
      | _ => simp [Kont.plug] at h
  | appL K v ih =>
      intro K' e hnv h
      cases K' with
      | hole => exact absurd (head_plug hh (.appL K v) hnv h.symm) (by simp)
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (K'.isVal_of_plug (h.2 ▸ v.2)) hna
      | appL K' v' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          obtain ⟨K'', h₁, h₂⟩ := ih K' hnv h.1
          have hv : v = v' := Subtype.ext h.2
          exact ⟨K'', h₁, by rw [h₂, hv]; rfl⟩
      | _ => simp [Kont.plug] at h

/-- A step of `K[e]`, `e` not a value, is a step of `e` under `K`. -/
theorem step1_plug_inv {μ μ₁ : Heap} {e e₁ : Expr} (K : Kont) (hnv : ¬ IsVal e)
    (h : Step1 μ (K.plug e) μ₁ e₁) : ∃ e', e₁ = K.plug e' ∧ Step1 μ e μ₁ e' := by
  obtain ⟨K', a, a', hE, rfl, hh⟩ := h
  obtain ⟨K'', rfl, rfl⟩ := plug_decomp hh K K' hnv hE
  exact ⟨K''.plug a', Kont.plug_comp K K'' a', ⟨K'', a, a', rfl, rfl, hh⟩⟩

/-- A run of `K[e]` to a value runs `e` to a value first. -/
theorem steps_plug_inv (K : Kont) {μ μ' : Heap} {E E' : Expr} (hs : Steps μ E μ' E') :
    ∀ {e : Expr} {w : Val}, E = K.plug e → E' = w.1 →
      ∃ (μm : Heap) (v : Val), Steps μ e μm v.1 ∧ Steps μm (K.plug v.1) μ' w.1 := by
  induction hs with
  | refl μ E =>
      intro e w hE hw
      subst hE
      have hv : IsVal e := K.isVal_of_plug (hw ▸ w.2)
      exact ⟨μ, ⟨e, hv⟩, .refl _ _, hw ▸ .refl _ _⟩
  | more h t ih =>
      intro e w hE hw
      subst hE
      by_cases hv : IsVal e
      · exact ⟨_, ⟨e, hv⟩, .refl _ _, .more h (hw ▸ t)⟩
      · obtain ⟨e', rfl, h'⟩ := step1_plug_inv K hv h
        obtain ⟨μm, v, h₁, h₂⟩ := ih rfl hw
        exact ⟨μm, v, .more h' h₁, h₂⟩

/-- A run from a term whose every step is determined continues from the step's result. -/
theorem steps_peel {μ μ' m : Heap} {e e' : Expr} {w : Val} (hs : Steps μ e μ' w.1)
    (hnv : ¬ IsVal e) (hu : ∀ μ₁ e₁, Step1 μ e μ₁ e₁ → μ₁ = m ∧ e₁ = e') :
    Steps m e' μ' w.1 := by
  cases hs with
  | refl => exact absurd w.2 hnv
  | more h t => obtain ⟨rfl, rfl⟩ := hu _ _ h; exact t

/-- A run from a value is empty. -/
theorem steps_from_val {μ μ' : Heap} {v w : Val} (h : Steps μ v.1 μ' w.1) : μ' = μ ∧ w = v := by
  obtain ⟨h₁, h₂⟩ := steps_val_inv h
  exact ⟨h₁, Subtype.ext h₂⟩

/-- The only step of a redex all of whose parts are values is its head step. -/
theorem step1_top {μ μ₁ : Heap} {a e₁ : Expr} (h : Step1 μ a μ₁ e₁)
    (hsub : ∀ (K : Kont) (b : Expr), a = K.plug b → K ≠ .hole → IsVal b) : Head μ a μ₁ e₁ := by
  obtain ⟨K, b, b', rfl, rfl, hh⟩ := h
  by_cases hK : K = .hole
  · subst hK; exact hh
  · exact absurd (hsub K b rfl hK) hh.not_isVal

/-- `(λb) v` steps only to `b[v]`. -/
theorem step1_beta_inv {μ μ₁ : Heap} {b e₁ : Expr} {v : Val}
    (h : Step1 μ (.app (.lam b) v.1) μ₁ e₁) : μ₁ = μ ∧ e₁ = b.subst 0 v := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | appR f K =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.2 ▸ v.2)
    | appL K u =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.lam)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.app (.lam b) v.1 = E at hh
  cases hh with
  | beta b' v' =>
      simp only [Expr.app.injEq, Expr.val, Val.lam, Expr.lam.injEq] at hE
      obtain ⟨rfl, hv⟩ := hE
      have : v = v' := Subtype.ext hv
      subst this; exact ⟨rfl, rfl⟩
  | _ => simp_all

/-- `let (x, y) = v; b` steps only at a pair, to `b[v₁, v₂]`. -/
theorem step1_letpair_inv {μ μ₁ : Heap} {b e₁ : Expr} {v : Val}
    (h : Step1 μ (.letpair v.1 b) μ₁ e₁) :
    ∃ v₁ v₂ : Val, v = .pair v₁ v₂ ∧ μ₁ = μ ∧ e₁ = (b.subst 0 (v₂.shift 1 0)).subst 0 v₁ := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | letpair K u =>
        simp only [Kont.plug, Expr.letpair.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ v.2)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.letpair v.1 b = E at hh
  cases hh with
  | letpair v₁ v₂ b' =>
      simp only [Expr.letpair.injEq] at hE
      obtain ⟨hv, rfl⟩ := hE
      exact ⟨v₁, v₂, Subtype.ext hv, rfl, rfl⟩
  | _ => simp_all

/-- `f a b` with `f = λλX` and `a`, `b` values: every run continues from `X[a, b]`. -/
theorem steps_app2_lam2 {μ μ' : Heap} {X : Expr} {a b w : Val}
    (hs : Steps μ (BoCa.Programs.app2 (lam2 X) a.1 b.1) μ' w.1) :
    Steps μ ((X.subst 1 (a.shift 1 0)).subst 0 b) μ' w.1 := by
  obtain ⟨μm, v, h₁, h₂⟩ := steps_plug_inv (.appL .hole b) hs rfl rfl
  have h₁' := steps_peel (e' := Expr.lam (X.subst 1 (a.shift 1 0))) (m := μ) h₁
    (by simp [lam2])
    (fun μ₁ e₁ h => by
      have := step1_beta_inv (b := Expr.lam X) (v := a) h
      simpa [Expr.subst] using this)
  obtain ⟨rfl, rfl⟩ := steps_from_val (v := Val.lam (X.subst 1 (a.shift 1 0))) h₁'
  exact steps_peel h₂ (by simp [Kont.plug]) fun μ₁ e₁ h => step1_beta_inv h

/-- A run of `let (x, y) = e; b` to a value: `e` runs to a pair, then `b` runs at its parts. -/
theorem steps_letpair_inv {μ μ' : Heap} {e b : Expr} {w : Val}
    (hs : Steps μ (.letpair e b) μ' w.1) :
    ∃ (μm : Heap) (v₁ v₂ : Val), Steps μ e μm (Val.pair v₁ v₂).1 ∧
      Steps μm ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) μ' w.1 := by
  obtain ⟨μm, v, h₁, h₂⟩ := steps_plug_inv (.letpair .hole b) hs rfl rfl
  simp only [Kont.plug] at h₂
  generalize hE : Expr.letpair v.1 b = E at h₂
  cases h₂ with
  | refl => exact absurd (hE ▸ w.2) (by simp)
  | more h t =>
      subst hE
      obtain ⟨v₁, v₂, rfl, rfl, rfl⟩ := step1_letpair_inv h
      exact ⟨_, v₁, v₂, h₁, t⟩

/-- A run of `(v, e)` to a value runs `e` to a value `u`, and the result is `(v, u)`. -/
theorem steps_pairR_inv {μ μ' : Heap} {v : Val} {e : Expr} {w : Val}
    (hs : Steps μ (.pair v.1 e) μ' w.1) :
    ∃ u : Val, w = .pair v u ∧ ∃ μm : Heap, Steps μ e μm u.1 := by
  obtain ⟨μm, u, h₁, h₂⟩ := steps_plug_inv (.pairR v .hole) hs rfl rfl
  obtain ⟨-, rfl⟩ := steps_from_val (v := Val.pair v u) h₂
  exact ⟨u, rfl, μm, h₁⟩

/-- A run of `(e₁, e₂)` to a value runs `e₁`, then `e₂`. -/
theorem steps_pair_inv {μ μ' : Heap} {e₁ e₂ : Expr} {w : Val}
    (hs : Steps μ (.pair e₁ e₂) μ' w.1) :
    ∃ u₁ u₂ : Val, w = .pair u₁ u₂ ∧ ∃ μ₁ μ₂ : Heap, Steps μ e₁ μ₁ u₁.1 ∧ Steps μ₁ e₂ μ₂ u₂.1 := by
  obtain ⟨μm, u₁, h₁, h₂⟩ := steps_plug_inv (.pairL .hole e₂) hs rfl rfl
  obtain ⟨u₂, rfl, μ₂, h₃⟩ := steps_pairR_inv (v := u₁) h₂
  exact ⟨u₁, u₂, rfl, μm, μ₂, h₁, h₃⟩

/-- A run of `f a` with `a` a term: `a` runs to a value first. -/
theorem steps_appR_inv {μ μ' : Heap} {f a : Expr} {w : Val}
    (hs : Steps μ (.app f a) μ' w.1) :
    ∃ (μm : Heap) (v : Val), Steps μ a μm v.1 ∧ Steps μm (.app f v.1) μ' w.1 :=
  steps_plug_inv (.appR f .hole) hs rfl rfl

end BoCa.Fig16.LogRel.Core

end
