import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Statics.Contexts
import Support.Syntax.Terms

/-!
# Support — Dynamics — Machine

`[about ours]`.  The machines' plumbing: frame composition and the reflexive-transitive closure `→*` for both machines, and for `[TR]` §3's printed machine the inversion of its steps at `inj₁ e` and `e₁; e₂`, the saturated primitives, and the closed terms `alloc ()`, `free (alloc ())`, `inj₁ (free (alloc ()))` and `free (alloc ()); ()`.
-/

noncomputable section

namespace BoCa.TR3.Kont
open BoCa.BoLo (Heap)

/-- `K ∘ K'`, so that `(K ∘ K')[e] = K[K'[e]]`. -/
def comp : Kont → Kont → Kont
  | .hole,         K' => K'
  | .pairL K e₂,   K' => .pairL (comp K K') e₂
  | .pairR v K,    K' => .pairR v (comp K K')
  | .letpair K e₂, K' => .letpair (comp K K') e₂
  | .case K e₁ e₂, K' => .case (comp K K') e₁ e₂
  | .appR f K,     K' => .appR f (comp K K')
  | .appL K v,     K' => .appL (comp K K') v

theorem plug_comp (K K' : Kont) (e : Expr) : plug (comp K K') e = plug K (plug K' e) := by
  induction K with
  | hole => rfl
  | pairL K e₂ ih => simp only [comp, plug, ih]
  | pairR v K ih => simp only [comp, plug, ih]
  | letpair K e₂ ih => simp only [comp, plug, ih]
  | case K e₁ e₂ ih => simp only [comp, plug, ih]
  | appR f K ih => simp only [comp, plug, ih]
  | appL K v ih => simp only [comp, plug, ih]

end BoCa.TR3.Kont

namespace BoCa.TR3
open BoCa.BoLo (Heap)

/-- `→*`, the reflexive-transitive closure `[TR]` §6.7 writes `⟶*`. -/
inductive Steps : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : Steps μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1 μ e μ₁ e₁) (t : Steps μ₁ e₁ μ' e') : Steps μ e μ' e'

theorem Step1.head {μ μ' : Heap} {e e' : Expr} (h : Head μ e μ' e') : Step1 μ e μ' e' :=
  ⟨.hole, e, e', rfl, rfl, h⟩

theorem Steps.one {μ μ' : Heap} {e e' : Expr} (h : Step1 μ e μ' e') : Steps μ e μ' e' :=
  .more h (.refl _ _)

theorem Steps.trans {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
    (h₁ : Steps μ e μ₁ e₁) (h₂ : Steps μ₁ e₁ μ' e') : Steps μ e μ' e' := by
  induction h₁ with
  | refl => exact h₂
  | more h _ ih => exact .more h (ih h₂)

theorem Step1.plug {μ μ' : Heap} {e e' : Expr} (K : Kont) (h : Step1 μ e μ' e') :
    Step1 μ (K.plug e) μ' (K.plug e') := by
  obtain ⟨K', a, a', rfl, rfl, hh⟩ := h
  exact ⟨K.comp K', a, a', (Kont.plug_comp K K' a).symm ▸ rfl,
    (Kont.plug_comp K K' a').symm ▸ rfl, hh⟩

/-- Reduction is a congruence for the seven printed frames. -/
theorem Steps.plug {μ μ' : Heap} {e e' : Expr} (K : Kont) (h : Steps μ e μ' e') :
    Steps μ (K.plug e) μ' (K.plug e') := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more (h.plug K) ih

/-- A term with no step out of it goes nowhere. -/
theorem Steps.stuck {μ μ' : Heap} {e e' : Expr}
    (hs : ∀ ν e₁, ¬ Step1 μ e ν e₁) (h : Steps μ e μ' e') : μ' = μ ∧ e' = e := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | more h _ => exact absurd h (hs _ _)

/-- `inj₁ e` takes no step, for any `e`.
`[about ours: the printed `Kont` and `↦` box of `[TR]` pp. 3–4, at `[TR]`
p. 1's `inj₁ e`]` -/
theorem no_step_inj₁ {μ μ' : Heap} {e e' : Expr} : ¬ Step1 μ (.inj₁ e) μ' e' := by
  rintro ⟨K, a, a', hE, -, hh⟩
  cases K with
  | hole => rw [Kont.plug_hole] at hE; subst hE; cases hh
  | pairL K e₂ => simp [Kont.plug] at hE
  | pairR v K => simp [Kont.plug] at hE
  | letpair K e₂ => simp [Kont.plug] at hE
  | case K e₁ e₂ => simp [Kont.plug] at hE
  | appR f K => simp [Kont.plug] at hE
  | appL K v => simp [Kont.plug] at hE

/-- Inversion at a sequence: `1↦` at the root, or nothing.
`[about ours: the printed `Kont` and `1↦` of `[TR]` pp. 3–4, at `[TR]`
p. 1's `e₁;e₂`]` -/
theorem step_seq_inv {μ μ' : Heap} {e₁ e₂ e' : Expr} (h : Step1 μ (.seq e₁ e₂) μ' e') :
    e₁ = .val .unit ∧ μ' = μ ∧ e' = e₂ := by
  obtain ⟨K, x, x', hE, hE', hh⟩ := h
  cases K with
  | hole =>
      rw [Kont.plug_hole] at hE hE'
      subst hE
      cases hh
      exact ⟨rfl, rfl, hE'⟩
  | pairL K e => simp [Kont.plug] at hE
  | pairR v K => simp [Kont.plug] at hE
  | letpair K e => simp [Kont.plug] at hE
  | case K a b => simp [Kont.plug] at hE
  | appR f K => simp [Kont.plug] at hE
  | appL K v => simp [Kont.plug] at hE

/-- Anything but `()` on the left of a `;` is stuck. -/
theorem no_step_seq {μ μ' : Heap} {e₁ e₂ e' : Expr} (h₁ : e₁ ≠ .val .unit) :
    ¬ Step1 μ (.seq e₁ e₂) μ' e' :=
  fun h => h₁ (step_seq_inv h).1

/-- A sequence that cannot start never reaches a value. -/
theorem steps_seq_ne_val {μ μ' : Heap} {e₁ e₂ : Expr} {v : Val} (h₁ : e₁ ≠ .val .unit) :
    ¬ Steps μ (.seq e₁ e₂) μ' (.val v) := by
  intro h
  obtain ⟨-, he⟩ := Steps.stuck (fun _ _ => no_step_seq h₁) h
  exact not_isVal_seq (he ▸ Val.isVal v)

/-- `alloc v` steps, at any fresh `ℓ`.
`[about ours: `alloc↦` of `[TR]` p. 4, read at `[TR]` p. 1's `e₂ e₁`]` -/
theorem steps_alloc (μ : Heap) (v : Val) (ℓ : Loc) (h : μ ℓ = none) :
    Step1 μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd ℓ v) (.val (.loc ℓ)) :=
  Step1.head (Head.alloc μ v ℓ h)

/-- `store ℓ v` takes one step.
`[about ours: `store↦` of `[TR]` p. 4, read at `[TR]` p. 1's `e₂ e₁`]` -/
theorem steps_store (μ : Heap) (ℓ : Loc) (v w : Val) (h : μ ℓ = some w) :
    Step1 μ (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v))
      (μ.upd ℓ v) (.val .unit) :=
  Step1.head (Head.store μ ℓ v w h)

/-- `alloc ()`. -/
def wAlloc : Expr := .app (.val (.prim .alloc)) (.val .unit)

/-- `free (alloc ())` — a redex, not a value, and closed. -/
def wFreeAlloc : Expr := .app (.val (.prim .free)) wAlloc

/-- `inj₁ (free (alloc ()))` — a redex under `inj₁`. -/
def wInj : Expr := .inj₁ wFreeAlloc

/-- `(free (alloc ())); ()` — a redex left of `;`. -/
def wSeq : Expr := .seq wFreeAlloc (.val .unit)

/-- `Δ; • ⊢ alloc () : Ref 1`, by `⊸E` on the `alloc` axiom over `1I`. -/
theorem derives_wAlloc (Δ : BoCa.Lifetime.LifeCtx) :
    Derives Δ [] wAlloc (.ref .unit) :=
  .lolliE .nil (.unitI .nil) (.allocAx .nil)

/-- `Δ; • ⊢ free (alloc ()) : 1`. -/
theorem derives_wFreeAlloc (Δ : BoCa.Lifetime.LifeCtx) :
    Derives Δ [] wFreeAlloc .unit :=
  .lolliE .nil (derives_wAlloc Δ) (.freeAx .nil)

/-- The seven printed frames are seven of `BoLo.Kont`'s ten. -/
def Kont.toWp : Kont → BoCa.BoLo.Kont
  | .hole         => .hole
  | .pairL K e    => .pairL K.toWp e
  | .pairR v K    => .pairR v K.toWp
  | .letpair K e  => .letpair K.toWp e
  | .case K e₁ e₂ => .case K.toWp e₁ e₂
  | .appR f K     => .appR f K.toWp
  | .appL K v     => .appL K.toWp v

theorem Kont.plug_toWp (K : Kont) (e : Expr) : K.toWp.plug e = K.plug e := by
  induction K with
  | hole => rfl
  | pairL K e₂ ih => simp only [toWp, plug, BoCa.BoLo.Kont.plug, ih]
  | pairR v K ih => simp only [toWp, plug, BoCa.BoLo.Kont.plug, ih]
  | letpair K e₂ ih => simp only [toWp, plug, BoCa.BoLo.Kont.plug, ih]
  | case K e₁ e₂ ih => simp only [toWp, plug, BoCa.BoLo.Kont.plug, ih]
  | appR f K ih => simp only [toWp, plug, BoCa.BoLo.Kont.plug, ih]
  | appL K v ih => simp only [toWp, plug, BoCa.BoLo.Kont.plug, ih]

end BoCa.TR3

namespace BoCa.BoLo
open BoCa.Lifetime

/-- `↦*`. -/
inductive Steps : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : Steps μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1 μ e μ₁ e₁) (t : Steps μ₁ e₁ μ' e') : Steps μ e μ' e'

theorem Step1.head {μ μ' : Heap} {e e' : Expr} (h : Head μ e μ' e') : Step1 μ e μ' e' :=
  ⟨.hole, e, e', rfl, rfl, h⟩

theorem Steps.one {μ μ' : Heap} {e e' : Expr} (h : Step1 μ e μ' e') : Steps μ e μ' e' :=
  .more h (.refl _ _)

end BoCa.BoLo

namespace BoCa.TR3
open BoCa.BoLo (Heap)

/-- Each printed head rule is a run of `BoLo.Steps` — one step
each, `store↦` included. -/
theorem Head.toWp {μ μ' : Heap} {e e' : Expr} (h : Head μ e μ' e') :
    BoCa.BoLo.Steps μ e μ' e' := by
  cases h
  · exact .one (.head (.seq _ _))
  · exact .one (.head (.letpair _ _ _ _))
  · exact .one (.head (.case₁ _ _ _ _))
  · exact .one (.head (.case₂ _ _ _ _))
  · exact .one (.head (.beta _ _ _))
  · exact .one (.head (.alloc _ _ _ (by assumption)))
  · exact .one (.head (.free _ _ _ (by assumption)))
  · exact .one (.head (.load _ _ _ (by assumption)))
  · exact .one (.head (.store _ _ _ _ (by assumption)))

end BoCa.TR3

namespace BoCa.BoLo.Kont
open BoCa.Lifetime

/-- `K ∘ K'`, so that `K[K'[e]] = (K ∘ K')[e]`. -/
def comp : Kont → Kont → Kont
  | .hole,          K' => K'
  | .pairL K e₂,    K' => .pairL (comp K K') e₂
  | .pairR v K,     K' => .pairR v (comp K K')
  | .letpair K e₂,  K' => .letpair (comp K K') e₂
  | .case K e₁ e₂,  K' => .case (comp K K') e₁ e₂
  | .appR f K,      K' => .appR f (comp K K')
  | .appL K v,      K' => .appL (comp K K') v
  | .seq K e₂,      K' => .seq (comp K K') e₂
  | .inj₁ K,        K' => .inj₁ (comp K K')
  | .inj₂ K,        K' => .inj₂ (comp K K')

theorem plug_comp (K K' : Kont) (e : Expr) : plug (comp K K') e = plug K (plug K' e) := by
  induction K with
  | hole => rfl
  | pairL K e₂ ih => simp only [comp, plug, ih]
  | pairR v K ih => simp only [comp, plug, ih]
  | letpair K e₂ ih => simp only [comp, plug, ih]
  | case K e₁ e₂ ih => simp only [comp, plug, ih]
  | appR f K ih => simp only [comp, plug, ih]
  | appL K v ih => simp only [comp, plug, ih]
  | seq K e₂ ih => simp only [comp, plug, ih]
  | inj₁ K ih => simp only [comp, plug, ih]
  | inj₂ K ih => simp only [comp, plug, ih]

end BoCa.BoLo.Kont

namespace BoCa.BoLo
open BoCa.Lifetime

theorem Step1.plug {μ μ' : Heap} {e e' : Expr} (K : Kont) (h : Step1 μ e μ' e') :
    Step1 μ (K.plug e) μ' (K.plug e') := by
  obtain ⟨K', a, a', rfl, rfl, hh⟩ := h
  exact ⟨K.comp K', a, a', (Kont.plug_comp K K' a).symm ▸ rfl,
    (Kont.plug_comp K K' a').symm ▸ rfl, hh⟩

/-- Reduction is a congruence for every evaluation context. -/
theorem Steps.plug {μ μ' : Heap} {e e' : Expr} (K : Kont) (h : Steps μ e μ' e') :
    Steps μ (K.plug e) μ' (K.plug e') := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more (h.plug K) ih

end BoCa.BoLo

namespace BoCa.TR3
open BoCa.BoLo (Heap)

theorem Step1.toWp {μ μ' : Heap} {e e' : Expr} (h : Step1 μ e μ' e') :
    BoCa.BoLo.Steps μ e μ' e' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  rw [← Kont.plug_toWp, ← Kont.plug_toWp]
  exact BoCa.BoLo.Steps.plug K.toWp (Head.toWp hh)

end BoCa.TR3

namespace BoCa.BoLo
open BoCa.Lifetime

theorem Steps.trans {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
    (h₁ : Steps μ e μ₁ e₁) (h₂ : Steps μ₁ e₁ μ' e') : Steps μ e μ' e' := by
  induction h₁ with
  | refl => exact h₂
  | more h _ ih => exact .more h (ih h₂)

end BoCa.BoLo

namespace BoCa.TR3
open BoCa.BoLo (Heap)

/-- The printed `→*` is contained in `BoLo.Steps`.
`[about ours: the two machines, `[TR]` §3's and convention W2's]` -/
theorem Steps.toWp {μ μ' : Heap} {e e' : Expr} (h : Steps μ e μ' e') :
    BoCa.BoLo.Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact BoCa.BoLo.Steps.trans (Step1.toWp h) ih

end BoCa.TR3

namespace BoCa.BoLo
open BoCa.Lifetime

/-- A frame holds a value only when its hole does: every frame but the hole
    itself is a form whose value-hood is that of the sub-term in the hole, or is
    no value at all. -/
theorem Kont.isVal_of_plug : ∀ (K : Kont) {a : Expr}, IsVal (K.plug a) → IsVal a
  | .hole,         _, h => h
  | .pairL K _,    _, h => K.isVal_of_plug h.pair_left
  | .pairR _ K,    _, h => K.isVal_of_plug h.pair_right
  | .inj₁ K,       _, h => K.isVal_of_plug h.inj₁_inv
  | .inj₂ K,       _, h => K.isVal_of_plug h.inj₂_inv
  | .letpair _ _,  _, h => absurd h not_isVal_letpair
  | .case _ _ _,   _, h => absurd h not_isVal_case
  -- `e K` and `K v` are values only at `store v`, whose two parts are both
  -- values; either way the hole holds one.
  | .appR _ K,     _, h => K.isVal_of_plug h.app_arg
  | .appL K _,     _, h => K.isVal_of_plug (h.app_fun ▸ IsVal.prim)
  | .seq _ _,      _, h => absurd h not_isVal_seq

/-- No head reduction has a value on the left: every printed redex is a `let`,
    a `case`, a `;` or an application, and none of those is a `Val`. -/
theorem Head.not_isVal {μ μ' : Heap} {e e' : Expr} (h : Head μ e μ' e') : ¬ IsVal e := by
  cases h <;> intro hv <;> cases hv

/-- A value takes no step. -/
theorem no_step_val {μ μ' : Heap} {w : Val} {e' : Expr} : ¬ Step1 μ (.val w) μ' e' := by
  rintro ⟨K, a, a', hE, -, hh⟩
  exact hh.not_isVal (K.isVal_of_plug (hE ▸ w.2))

/-- …and the converse.  `wp(v){Q̂} ⊨ Q̂(v)` needs the run to be trivial, which it
    is because a value takes no step. -/
theorem steps_val_inv {μ μ' : Heap} {w : Val} {e' : Expr}
    (h : Steps μ (.val w) μ' e') : μ' = μ ∧ e' = .val w := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | more hs _ => exact absurd hs no_step_val

/-- `load ℓ`. -/
def eLoad (ℓ : Loc) : Expr := .app (.val (.prim .load)) (.val (.loc ℓ))

/-- `store ℓ v` — the saturated two-argument application. -/
def eStore (ℓ : Loc) (v : Val) : Expr :=
  .app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v)

end BoCa.BoLo

end
