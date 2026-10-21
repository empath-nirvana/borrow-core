import Core.FramesElab

/-!
# Core — frames: the run invariant and its composition lemmas  `[spec §47]`

`RetsG Q G t`: every run from `t` that reaches a value reaches one satisfying `Q`, and every run
that stops at an operation no handler in it holds is resumed, at every answer, into a term that
satisfies the invariant again or lies in `G`. At `G = ∅` and `Q = AnsQ π` it is `Rets`
(`rets_of_retsG`). `G` is a coinduction hypothesis: a div loop proves its invariant up to the states
it resumes into after a tick (`retsG_close`).

The composition lemmas are each about one form of term: a plain evaluation context (`retsG_plain`),
a finaliser frame `ubind` (`retsG_ubind`), a deterministic step (`retsG_step`), and the
unwinding forms, which never reach a value (`retsG_raise`, `retsG_seqRaise`, `retsG_cfin`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload ubindE cfinE cancelVal steps_val_inv no_step_val)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The accounting invariant -/

/-- The cells of a slot tuple, its drop flags erased: every injection removed. Two slot tuples
with the same cells hold the same cells at the same positions, each perhaps in another state. -/
def slotCells : Expr → Expr
  | .inj₁ e => slotCells e
  | .inj₂ e => slotCells e
  | .pair a b => .pair (slotCells a) (slotCells b)
  | e => e

/-- `π'` holds the cells of `π`, at the same positions. -/
def SameCells (π π' : Val) : Prop := slotCells π'.1 = slotCells π.1

/-- The answers that hand back the cells of `π`: `inl (π', a)` at the normal exit, `inr (π', e)`
at a local exit, `π'` holding the cells of `π`. -/
def AnsQ (π : Val) (w : Val) : Prop :=
  ∃ π' x : Val, SameCells π π' ∧ (w = Val.inj₁ (Val.pair π' x) ∨ w = Val.inj₂ (Val.pair π' x))

/-- One step of the accounting invariant `R` at `t`: every run from `t` that reaches a value
reaches an answer that hands back the cells of `π`, at the same positions, beside an exit tag;
and every run that stops at an operation no handler in it handles (a `Div` tick, an outer
handler's operation) is resumed, at every answer, into a term of `R`. A run that stops at a
`raise` leaves by §19's unwinding (`frame_unwind_leakfree`). -/
def RetsStep (π : Val) (R : Expr → Prop) (t : Expr) : Prop :=
  (∀ (μ μ' : Heap) (w : Val), Steps μ t μ' (.val w) → AnsQ π w) ∧
  (∀ (μ μ' : Heap) (K : Kont) (n i : UInt32) (v : Val),
    Steps μ t μ' (K.plug (performE (.val (opPayload n i v)))) → K.HasHnd n = false →
    ∀ w : Val, R (K.plug (.val w)))

/-- **The slots come back**, coinductively: `t` is in an invariant closed under `RetsStep`. It is
a greatest fixed point because a div loop stops at a tick at every turn, forever. A unary
property of machine runs at one value `π`; it reads no type and no resource. -/
def Rets (π : Val) (t : Expr) : Prop :=
  ∃ R : Expr → Prop, R t ∧ ∀ t', R t' → RetsStep π R t'

/-- A frame term hands back the cells of the slots it is given, whatever they are. -/
def Returns (e : Expr) : Prop := ∀ π : Val, Rets π (.app e (.val π))

/-- A block hands back the slots on every argument. -/
def FBlock.Returns (b : FBlock) : Prop := ∀ a : Val, Frames.Returns (.app (.val b.v) (.val a))

/-! ### The invariant up to a coinduction hypothesis -/

/-- A stop: `K[perform (n, (i, v))]` with no handler of `n` in `K`. -/
def perfAt (K : Kont) (n i : UInt32) (v : Val) : Expr := K.plug (performE (.val (opPayload n i v)))

/-- One step of the invariant: the values `Q`, the resumptions in `R`. -/
def StepQ (Q : Val → Prop) (R : Expr → Prop) (t : Expr) : Prop :=
  (∀ (μ μ' : Heap) (w : Val), Steps (ℍ := ℍ) μ t μ' (.val w) → Q w) ∧
  (∀ (μ μ' : Heap) (K : Kont) (n i : UInt32) (v : Val),
    Steps (ℍ := ℍ) μ t μ' (perfAt K n i v) → K.HasHnd n = false →
    ∀ w : Val, R (K.plug (.val w)))

/-- The invariant up to `G`. -/
def RetsG (Q : Val → Prop) (G : Expr → Prop) (t : Expr) : Prop :=
  ∃ R : Expr → Prop, R t ∧ ∀ t', R t' → StepQ (ℍ := ℍ) Q (fun s => R s ∨ G s) t'

theorem StepQ.mono {Q Q' : Val → Prop} {R R' : Expr → Prop} {t : Expr}
    (hQ : ∀ w, Q w → Q' w) (hR : ∀ s, R s → R' s) (h : StepQ (ℍ := ℍ) Q R t) :
    StepQ (ℍ := ℍ) Q' R' t :=
  ⟨fun μ μ' w hs => hQ w (h.1 μ μ' w hs), fun μ μ' K n i v hs hK w => hR _ (h.2 μ μ' K n i v hs hK w)⟩

theorem retsG_unfold {Q : Val → Prop} {G : Expr → Prop} {t : Expr} (h : RetsG (ℍ := ℍ) Q G t) :
    StepQ (ℍ := ℍ) Q (fun s => RetsG (ℍ := ℍ) Q G s ∨ G s) t := by
  obtain ⟨R, hR, hinv⟩ := h
  exact (hinv t hR).mono (fun _ h => h) (fun s hs => hs.elim (fun h => .inl ⟨R, h, hinv⟩) .inr)

/-- **Coinduction.** -/
theorem retsG_coind {Q : Val → Prop} {G : Expr → Prop} (P : Expr → Prop)
    (h : ∀ t, P t → StepQ (ℍ := ℍ) Q (fun s => P s ∨ RetsG (ℍ := ℍ) Q G s ∨ G s) t)
    {t : Expr} (ht : P t) : RetsG (ℍ := ℍ) Q G t := by
  refine ⟨fun s => P s ∨ RetsG (ℍ := ℍ) Q G s, .inl ht, ?_⟩
  rintro t' (hP | hG)
  · exact (h t' hP).mono (fun _ h => h) (fun s hs => by
      rcases hs with hs | hs | hs
      · exact .inl (.inl hs)
      · exact .inl (.inr hs)
      · exact .inr hs)
  · exact (retsG_unfold hG).mono (fun _ h => h) (fun s hs => hs.elim (fun h => .inl (.inr h)) .inr)

theorem retsG_mono {Q Q' : Val → Prop} {G G' : Expr → Prop} {t : Expr}
    (hQ : ∀ w, Q w → Q' w) (hG : ∀ s, G s → G' s) (h : RetsG (ℍ := ℍ) Q G t) :
    RetsG (ℍ := ℍ) Q' G' t := by
  obtain ⟨R, hR, hinv⟩ := h
  exact ⟨R, hR, fun t' h' => (hinv t' h').mono hQ (fun s hs => hs.imp id (hG s))⟩

/-- **Closing the coinduction**: an invariant up to `G`, where every term of `G` satisfies it up to
`G`, holds outright. -/
theorem retsG_close {Q : Val → Prop} {G : Expr → Prop}
    (hG : ∀ s, G s → RetsG (ℍ := ℍ) Q G s) {t : Expr} (h : RetsG (ℍ := ℍ) Q G t) :
    RetsG (ℍ := ℍ) Q (fun _ => False) t := by
  refine ⟨RetsG (ℍ := ℍ) Q G, h, fun t' h' => (retsG_unfold h').mono (fun _ h => h) ?_⟩
  intro s hs
  rcases hs with hs | hs
  · exact .inl hs
  · exact .inl (hG s hs)

/-- `Rets` is the invariant at `AnsQ π` with no coinduction hypothesis. -/
theorem rets_of_retsG {π : Val} {t : Expr} (h : RetsG (ℍ := ℍ) (AnsQ π) (fun _ => False) t) :
    Rets (ℍ := ℍ) π t := by
  obtain ⟨R, hR, hinv⟩ := h
  refine ⟨R, hR, fun t' h' => ⟨(hinv t' h').1, fun μ μ' K n i v hs hK w => ?_⟩⟩
  rcases (hinv t' h').2 μ μ' K n i v hs hK w with h | h
  · exact h
  · exact h.elim

theorem retsG_of_rets {π : Val} {t : Expr} {G : Expr → Prop} (h : Rets (ℍ := ℍ) π t) :
    RetsG (ℍ := ℍ) (AnsQ π) G t := by
  obtain ⟨R, hR, hinv⟩ := h
  exact ⟨R, hR, fun t' h' => ⟨(hinv t' h').1, fun μ μ' K n i v hs hK w =>
    .inl ((hinv t' h').2 μ μ' K n i v hs hK w)⟩⟩

/-! ### Basic forms -/

theorem retsG_true (G : Expr → Prop) (t : Expr) : RetsG (ℍ := ℍ) (fun _ => True) G t :=
  ⟨fun _ => True, trivial, fun _ _ => ⟨fun _ _ _ _ => trivial, fun _ _ _ _ _ _ _ _ _ => .inl trivial⟩⟩

theorem perfAt_not_val (K : Kont) (n i : UInt32) (v w : Val) : perfAt K n i v ≠ Expr.val w :=
  plug_perform_ne_val K _ w

/-- A value satisfies the invariant when it satisfies `Q`. -/
theorem retsG_val {Q : Val → Prop} {G : Expr → Prop} {w : Val} (h : Q w) :
    RetsG (ℍ := ℍ) Q G (.val w) := by
  refine retsG_coind (fun s => s = .val w) (fun t ht => ?_) rfl
  subst ht
  refine ⟨fun μ μ' w' hs => ?_, fun μ μ' K n i v hs _ => ?_⟩
  · obtain ⟨-, h'⟩ := steps_val_inv hs
    have : w' = w := Subtype.ext (by simpa using h')
    subst this; exact h
  · obtain ⟨-, h'⟩ := steps_val_inv hs
    exact absurd h' (perfAt_not_val K n i v w)

theorem isVal_eq {w : Val} {e : Expr} (h : Expr.val w = e) : IsVal e := by
  rw [← h]; exact w.2

/-- A run is empty or starts with a step. -/
theorem steps_cases {μ μ' : Heap} {e E : Expr} (h : Steps (ℍ := ℍ) μ e μ' E) :
    (μ' = μ ∧ E = e) ∨ ∃ μ₁ e₁, Step1 (ℍ := ℍ) μ e μ₁ e₁ ∧ Steps (ℍ := ℍ) μ₁ e₁ μ' E := by
  cases h with
  | refl => exact .inl ⟨rfl, rfl⟩
  | more h t => exact .inr ⟨_, _, h, t⟩

/-- A run from a term with no step is empty. -/
theorem steps_of_irred {μ μ' : Heap} {t E : Expr}
    (hirr : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ t μ₂ t₂) (hs : Steps (ℍ := ℍ) μ t μ' E) : μ' = μ ∧ E = t := by
  cases hs with
  | refl => exact ⟨rfl, rfl⟩
  | more h _ => exact absurd h (hirr _ _)

/-- A term with no step, not a value and not a stop satisfies every invariant. -/
theorem retsG_stuck {Q : Val → Prop} {G : Expr → Prop} {t : Expr}
    (hirr : ∀ μ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ t μ₂ t₂) (hnv : ¬ IsVal t)
    (hns : ∀ K n i v, t ≠ perfAt K n i v) : RetsG (ℍ := ℍ) Q G t := by
  refine retsG_coind (fun s => s = t) (fun t' ht => ?_) rfl
  subst ht
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K n i v hs _ => ?_⟩
  · obtain ⟨-, h⟩ := steps_of_irred (hirr μ) hs
    exact absurd (h ▸ w.2) hnv
  · obtain ⟨-, h⟩ := steps_of_irred (hirr μ) hs
    exact absurd h.symm (hns K n i v)

/-- A head redex is not a stop. -/
theorem head_not_perfAt {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') (K : Kont)
    (n i : UInt32) (v : Val) (hK : K.HasHnd n = false) : a ≠ perfAt K n i v := by
  intro e
  subst e
  exact head_not_opPlug (r := false) (p := opPayload n i v) (n := n) (payloadName_opPayload n i v)
    (by simpa [OpFree] using hK) (by simpa [opE, perfAt] using h)

/-- **A step**: a head redex all of whose steps lead to terms of the invariant. -/
theorem retsG_step {Q : Val → Prop} {G : Expr → Prop} {t : Expr}
    (hred : ∃ μ μ' t', Head (ℍ := ℍ) μ t μ' t')
    (h : ∀ μ μ₁ t₁, Step1 (ℍ := ℍ) μ t μ₁ t₁ → RetsG (ℍ := ℍ) Q G t₁) : RetsG (ℍ := ℍ) Q G t := by
  obtain ⟨μ₀, μ₀', t₀, h₀⟩ := hred
  refine retsG_coind (fun s => s = t) (fun t' ht => ?_) rfl
  subst ht
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K n i v hs hK w => ?_⟩
  · cases hs with
    | refl => exact absurd w.2 h₀.not_isVal
    | more h₁ t₁ => exact (retsG_unfold (h _ _ _ h₁)).1 _ _ _ t₁
  · cases hs with
    | refl => exact absurd rfl (head_not_perfAt h₀ K n i v hK)
    | more h₁ t₁ =>
        exact ((retsG_unfold (h _ _ _ h₁)).2 _ _ _ _ _ _ t₁ hK w).imp (fun h => .inr (.inl h))
          (fun h => .inr (.inr h)) |>.elim (fun h => h) (fun h => h)

/-! ### Contexts -/

theorem perform_not_isVal (p : Val) : ¬ IsVal (performE (.val p)) := by
  simpa [opE] using opE_not_isVal false p

theorem hasHnd_comp_right {n : UInt32} {K K' : Kont} (h : (K.comp K').HasHnd n = false) :
    K'.HasHnd n = false := by
  rw [hasHnd_comp] at h; simp_all

/-- A stop of `K[e']`, `e'` a non-value that `t'` reaches: the stop is one of `t'`'s, and its
resumption is `K` around a resumption of `t'`. -/
theorem stop_inside {Q₁ : Val → Prop} {G₁ : Expr → Prop} {K K_E : Kont} {t' e' : Expr}
    {μ μ' : Heap} {n i : UInt32} {v : Val} (ht : RetsG (ℍ := ℍ) Q₁ G₁ t')
    (hs : Steps (ℍ := ℍ) μ t' μ' e') (hnv : ¬ IsVal e')
    (he : K.plug e' = perfAt K_E n i v) (hK : K_E.HasHnd n = false) (w : Val) :
    ∃ t'', K_E.plug (.val w) = K.plug t'' ∧ (RetsG (ℍ := ℍ) Q₁ G₁ t'' ∨ G₁ t'') := by
  rcases plug_cmp K_E K (perform_not_isVal _) hnv he.symm with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · have hK'' := plug_primApp h₁.symm hnv
    subst hK''
    simp only [Kont.plug] at h₁
    subst h₁
    rw [Kont.comp_hole] at h₂
    subst h₂
    exact ⟨.val w, rfl, (retsG_unfold ht).2 μ μ' .hole n i v hs rfl w⟩
  · subst h₁ h₂
    exact ⟨K''.plug (.val w), Kont.plug_comp K K'' _,
      (retsG_unfold ht).2 μ μ' K'' n i v hs (hasHnd_comp_right hK) w⟩

/-- A stop takes no step. -/
theorem perfAt_irred {K : Kont} {n i : UInt32} {v : Val} (hK : K.HasHnd n = false) (μ : Heap) :
    ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ (perfAt K n i v) μ₂ t₂ := by
  rintro μ₂ t₂ ⟨K', a, a', he, -, hh⟩
  rcases plug_cmp K K' (perform_not_isVal _) hh.not_isVal he with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · have hK'' := plug_primApp h₁.symm hh.not_isVal
    subst hK''
    simp only [Kont.plug] at h₁
    subst h₁
    exact head_not_inertApp (p := .perform) trivial hh
  · subst h₁ h₂
    exact head_not_perfAt hh K'' n i v (hasHnd_comp_right hK) rfl

/-- **A stop**: a perform under a context with no handler of it, each resumption in the
invariant or in `G`. -/
theorem retsG_perform {Q : Val → Prop} {G : Expr → Prop} {K : Kont} {n i : UInt32} {v : Val}
    (hK : K.HasHnd n = false)
    (h : ∀ w, RetsG (ℍ := ℍ) Q G (K.plug (.val w)) ∨ G (K.plug (.val w))) :
    RetsG (ℍ := ℍ) Q G (perfAt K n i v) := by
  refine retsG_coind (fun s => s = perfAt K n i v) (fun t ht => ?_) rfl
  subst ht
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K' n' i' v' hs hK' w => ?_⟩
  · obtain ⟨-, h'⟩ := steps_of_irred (perfAt_irred hK μ) hs
    exact absurd h'.symm (perfAt_not_val K n i v w)
  · obtain ⟨-, h'⟩ := steps_of_irred (perfAt_irred hK μ) hs
    obtain ⟨hKK, hp⟩ := plug_perform_inj h'
    obtain ⟨rfl, -, -⟩ := opPayload_inj hp
    subst hKK
    exact (h w).elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))

/-- **A plain context.** `K[t]`, `K` with no catcher frame: `t`'s values continue in `K`, and
its stops resume under `K`. The coinduction hypothesis of `t` is `G` read under `K`. -/
theorem retsG_plain {Q₁ Q : Val → Prop} {G : Expr → Prop} {K : Kont} (hK : K.Plain = true)
    {t : Expr} (ht : RetsG (ℍ := ℍ) Q₁ (fun s => G (K.plug s)) t)
    (hk : ∀ v, Q₁ v → RetsG (ℍ := ℍ) Q G (K.plug (.val v))) :
    RetsG (ℍ := ℍ) Q G (K.plug t) := by
  refine retsG_coind (fun s => ∃ t', s = K.plug t' ∧ RetsG (ℍ := ℍ) Q₁ (fun s => G (K.plug s)) t')
    (fun s hs => ?_) ⟨t, rfl, ht⟩
  obtain ⟨t', rfl, ht'⟩ := hs
  have hval : ∀ μ μm (v : Val), Steps (ℍ := ℍ) μ t' μm (.val v) → RetsG (ℍ := ℍ) Q G (K.plug (.val v)) :=
    fun μ μm v h => hk v ((retsG_unfold ht').1 _ _ _ h)
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K_E n i v hs hKE w => ?_⟩
  · obtain ⟨μm, v, h₁, h₂⟩ := steps_plug_inv K hK hs rfl rfl
    exact (retsG_unfold (hval _ _ _ h₁)).1 _ _ _ h₂
  · -- the stop is inside `t'` (`stop_inside`), or after a value of it
    have inside : ∀ μ₁ e', Steps (ℍ := ℍ) μ t' μ₁ e' → ¬ IsVal e' → K.plug e' = perfAt K_E n i v →
        (∃ t', K_E.plug (.val w) = K.plug t' ∧ RetsG (ℍ := ℍ) Q₁ (fun s => G (K.plug s)) t') ∨
          RetsG (ℍ := ℍ) Q G (K_E.plug (.val w)) ∨ G (K_E.plug (.val w)) := by
      intro μ₁ e' h₁ hnv he
      obtain ⟨t'', he', h''⟩ := stop_inside ht' h₁ hnv he hKE w
      rcases h'' with h'' | h''
      · exact .inl ⟨t'', he', h''⟩
      · exact .inr (.inr (he' ▸ h''))
    rcases steps_plug_split K hs with ⟨e', he, h₁⟩ | ⟨μ₁, t₁, h₁, hirr, h₂⟩
    · by_cases hv : IsVal e'
      · have := (retsG_unfold (hval _ _ ⟨e', hv⟩ h₁)).2 μ' μ' K_E n i v (he ▸ .refl _ _) hKE w
        exact this.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
      · exact inside _ _ h₁ hv he.symm
    · by_cases hv : IsVal t₁
      · have := (retsG_unfold (hval _ _ ⟨t₁, hv⟩ h₁)).2 _ _ K_E n i v h₂ hKE w
        exact this.elim (fun h => .inr (.inl h)) (fun h => .inr (.inr h))
      · have hirr' : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ₁ (K.plug t₁) μ₂ t₂ := fun μ₂ t₂ hst => by
          obtain ⟨e', -, he'⟩ := step1_plug_inv K hK hv hst
          exact hirr _ _ he'
        obtain ⟨-, he⟩ := steps_of_irred hirr' h₂
        exact inside _ _ h₁ hv he.symm

/-! ### The unwinding forms never reach a value -/

/-- A step of `f t₁`, `t₁` a non-value with no step, is a head step. -/
theorem step1_appR_irred {μ μ₁ : Heap} {f t₁ E : Expr} (hnv : ¬ IsVal t₁)
    (hirr : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ t₁ μ₂ t₂) (h : Step1 (ℍ := ℍ) μ (.app f t₁) μ₁ E) :
    Head (ℍ := ℍ) μ (.app f t₁) μ₁ E := by
  obtain ⟨K', a, a', he, rfl, hh⟩ := h
  cases K' with
  | hole => simp only [Kont.plug] at he ⊢; subst he; exact hh
  | appR f' K'' =>
      simp only [Kont.plug, Expr.app.injEq] at he
      exact absurd ⟨K'', a, a', he.2, rfl, hh⟩ (hirr _ _)
  | appL K'' w =>
      simp only [Kont.plug, Expr.app.injEq] at he
      exact absurd (he.2 ▸ w.2) hnv
  | _ => simp [Kont.plug] at he

theorem raise_not_isVal (p : Val) : ¬ IsVal (raiseE (.val p)) := by
  simpa [opE] using opE_not_isVal true p

theorem raise_irred (p : Val) (μ : Heap) : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ (raiseE (.val p)) μ₂ t₂ := by
  rintro μ₂ t₂ ⟨K', a, a', he, -, hh⟩
  cases K' with
  | hole =>
      simp only [Kont.plug] at he; subst he
      exact head_not_inertApp (p := .raise) trivial hh
  | appR f' K'' =>
      simp only [Kont.plug, raiseE, Expr.app.injEq] at he
      exact hh.not_isVal (K''.isVal_of_plug (he.2 ▸ p.2))
  | appL K'' w =>
      simp only [Kont.plug, raiseE, Expr.app.injEq] at he
      exact hh.not_isVal (K''.isVal_of_plug (he.1 ▸ IsVal.prim))
  | _ => simp [Kont.plug, raiseE] at he

theorem raise_ne_perfAt (p : Val) (K : Kont) (n i : UInt32) (v : Val) :
    raiseE (.val p) ≠ perfAt K n i v := fun h =>
  plug_perform_ne_raise K .hole _ p (by simpa [perfAt] using h.symm)

theorem retsG_raise {Q : Val → Prop} {G : Expr → Prop} (p : Val) :
    RetsG (ℍ := ℍ) Q G (raiseE (.val p)) :=
  retsG_stuck (raise_irred p) (raise_not_isVal p) (raise_ne_perfAt p)

/-- `seq v X` steps only at `v = ()`, to `X`. -/
theorem step1_seq_inv {μ μ₁ : Heap} {v : Val} {X E : Expr}
    (h : Step1 (ℍ := ℍ) μ (.seq (.val v) X) μ₁ E) : v = .unit ∧ μ₁ = μ ∧ E = X := by
  obtain ⟨K', a, a', he, rfl, hh⟩ := h
  cases K' with
  | hole =>
      simp only [Kont.plug] at he ⊢; subst he
      generalize hE : Expr.seq (.val v) X = E at hh
      cases hh with
      | seq e =>
          simp only [Expr.seq.injEq] at hE
          obtain ⟨h1, h2⟩ := hE
          subst h2
          exact ⟨Subtype.ext h1, rfl, rfl⟩
      | _ => simp_all [BoCa.BoLo.hndE, ubindE, BoCa.BoLo.ccatchE, cfinE]
  | seq K'' e =>
      simp only [Kont.plug, Expr.seq.injEq] at he
      exact absurd (K''.isVal_of_plug (he.1 ▸ v.2)) hh.not_isVal
  | _ => simp [Kont.plug] at he

/-- `seq v X`, for a value `v`, satisfies what `X` does. -/
theorem retsG_seqv {Q : Val → Prop} {G : Expr → Prop} {v : Val} {X : Expr}
    (hX : RetsG (ℍ := ℍ) Q G X) : RetsG (ℍ := ℍ) Q G (.seq (.val v) X) := by
  refine retsG_coind (fun s => s = .seq (.val v) X) (fun t ht => ?_) rfl
  subst ht
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K n i u hs hK w => ?_⟩
  · rcases steps_cases hs with ⟨-, h⟩ | ⟨μ₁, e₁, h₁, t₁⟩
    · have hw := w.2
      rw [show (w.1 : Expr) = Expr.val w from rfl, h] at hw
      cases hw
    · obtain ⟨-, rfl, rfl⟩ := step1_seq_inv h₁
      exact (retsG_unfold hX).1 _ _ _ t₁
  · rcases steps_cases hs with ⟨-, h⟩ | ⟨μ₁, e₁, h₁, t₁⟩
    · exfalso
      cases K with
      | hole => simp [perfAt, Kont.plug, performE] at h
      | seq K' e =>
          simp only [perfAt, Kont.plug, Expr.seq.injEq] at h
          exact perform_not_isVal (opPayload n i u) (K'.isVal_of_plug (h.1 ▸ v.2))
      | _ => simp [perfAt, Kont.plug] at h
    · obtain ⟨-, rfl, rfl⟩ := step1_seq_inv h₁
      exact ((retsG_unfold hX).2 _ _ _ _ _ _ t₁ hK w).elim (fun h => .inr (.inl h))
        (fun h => .inr (.inr h))

/-- `seq t X`, for any `t`, satisfies what `X` does. -/
theorem retsG_seq {Q : Val → Prop} {G : Expr → Prop} {t X : Expr}
    (hX : RetsG (ℍ := ℍ) Q G X) : RetsG (ℍ := ℍ) Q G (.seq t X) :=
  retsG_plain (K := .seq .hole X) (by simp [Kont.Plain]) (retsG_true _ t)
    (fun _ _ => retsG_seqv hX)

/-! ### Catcher frames: `ubind` and `cfin` -/

/-- The frame `p x [·]` of a binary primitive. -/
abbrev app2K (p : Prim) (x : Val) : Kont := .appR (.app (.val (.prim p)) (.val x)) .hole

theorem app2K_plug (p : Prim) (x : Val) (e : Expr) :
    (app2K p x).plug e = .app (.app (.val (.prim p)) (.val x)) e := rfl

theorem app2K_hasHnd (p : Prim) (hp : p ≠ .hnd) (x : Val) (n : UInt32) :
    (app2K p x).HasHnd n = false := by
  cases p <;> simp_all [Kont.HasHnd, Expr.val, Val.prim]

/-- A step of `p x e`, `p` inert: a step of `e`, or the head step. -/
theorem step1_app2 {μ μ₁ : Heap} {p : Prim} {x : Val} {e E : Expr} (hp : p.Inert)
    (h : Step1 (ℍ := ℍ) μ (.app (.app (.val (.prim p)) (.val x)) e) μ₁ E) :
    (∃ e', E = .app (.app (.val (.prim p)) (.val x)) e' ∧ Step1 (ℍ := ℍ) μ e μ₁ e') ∨
      Head (ℍ := ℍ) μ (.app (.app (.val (.prim p)) (.val x)) e) μ₁ E := by
  obtain ⟨K', a, a', he, rfl, hh⟩ := h
  cases K' with
  | hole => simp only [Kont.plug] at he ⊢; subst he; exact .inr hh
  | appR f K₂ =>
      simp only [Kont.plug, Expr.app.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .inl ⟨_, rfl, ⟨K₂, a, a', rfl, rfl, hh⟩⟩
  | appL K₂ w =>
      simp only [Kont.plug, Expr.app.injEq] at he
      obtain ⟨he, -⟩ := he
      exfalso
      cases K₂ with
      | hole =>
          simp only [Kont.plug] at he; subst he
          exact head_not_inertApp hp hh
      | appR f K₃ =>
          simp only [Kont.plug, Expr.app.injEq] at he
          exact hh.not_isVal (K₃.isVal_of_plug (he.2 ▸ x.2))
      | appL K₃ w' =>
          simp only [Kont.plug, Expr.app.injEq] at he
          exact hh.not_isVal (K₃.isVal_of_plug (he.1 ▸ IsVal.prim))
      | _ => simp [Kont.plug] at he
  | _ => simp [Kont.plug] at he

/-- `p x v`, all values, is not a stop, `p` not `perform`. -/
theorem app2_ne_perfAt {p : Prim} (hp : p ≠ .perform) (x y : Val) (K : Kont) (n i : UInt32)
    (v : Val) : Expr.app (.app (.val (.prim p)) (.val x)) (.val y) ≠ perfAt K n i v := by
  intro he
  cases K with
  | hole => simp [perfAt, Kont.plug, performE] at he
  | appR f K₂ =>
      simp only [perfAt, Kont.plug, Expr.app.injEq] at he
      exact perform_not_isVal _ (K₂.isVal_of_plug (by rw [← he.2]; exact y.2))
  | appL K₂ w =>
      simp only [perfAt, Kont.plug, Expr.app.injEq] at he
      obtain ⟨he, -⟩ := he
      cases K₂ with
      | hole =>
          simp only [Kont.plug, performE, Expr.app.injEq] at he
          exact hp (by simpa [Expr.val, Val.prim] using he.1)
      | appR f K₃ =>
          simp only [Kont.plug, Expr.app.injEq] at he
          exact perform_not_isVal _ (K₃.isVal_of_plug (by rw [← he.2]; exact x.2))
      | appL K₃ w' =>
          simp only [Kont.plug, Expr.app.injEq] at he
          exact perform_not_isVal _ (K₃.isVal_of_plug (by rw [← he.1]; exact IsVal.prim))
      | _ => simp [Kont.plug] at he
  | _ => simp [perfAt, Kont.plug] at he

theorem app2_not_isVal (p : Prim) (x : Val) (e : Expr) :
    ¬ IsVal (Expr.app (.app (.val (.prim p)) (.val x)) e) := by
  intro h
  have := h.app_fun
  simp at this

/-- The head steps of `cfin s e`: each to a `raise`. -/
theorem head_cfin_inv {μ μ₁ : Heap} {s : Val} {e E : Expr}
    (h : Head (ℍ := ℍ) μ (cfinE s e) μ₁ E) : ∃ p, E = raiseE (.val p) := by
  generalize hE : cfinE s e = X at h
  cases h <;> first
    | exact ⟨_, rfl⟩
    | (exfalso; simp_all [cfinE, BoCa.BoLo.hndE, ubindE, BoCa.BoLo.ccatchE, Expr.val, Val.prim,
        Val.lam])

/-- **A cancel's finaliser frame never reaches a value**, and its stops resume inside it. -/
theorem retsG_cfin {Q : Val → Prop} {G : Expr → Prop} (s : Val) (t : Expr) :
    RetsG (ℍ := ℍ) Q G (cfinE s t) := by
  refine retsG_coind (fun x => ∃ t, x = cfinE s t) (fun x hx => ?_) ⟨t, rfl⟩
  obtain ⟨t, rfl⟩ := hx
  have hcf : (Prim.cfin).Inert := trivial
  -- every step of `cfin s v` is its head step, to a `raise`
  have hval : ∀ μ (v : Val) μ' E, Steps (ℍ := ℍ) μ (cfinE s (.val v)) μ' E →
      E = cfinE s (.val v) ∨ ∃ p, E = raiseE (.val p) := by
    intro μ v μ' E hs
    rcases steps_cases hs with ⟨-, rfl⟩ | ⟨μ₁, e₁, h₁, t₁⟩
    · exact .inl rfl
    · rcases step1_app2 hcf h₁ with ⟨e', -, he'⟩ | hh
      · exact absurd he' no_step_val
      · obtain ⟨p, rfl⟩ := head_cfin_inv hh
        exact .inr ⟨p, (steps_of_irred (raise_irred p μ₁) t₁).2⟩
  have hirr : ∀ μ₁ t₁, (∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ₁ t₁ μ₂ t₂) → ¬ IsVal t₁ →
      ∀ μ' E, Steps (ℍ := ℍ) μ₁ (cfinE s t₁) μ' E → E = cfinE s t₁ ∨ ∃ p, E = raiseE (.val p) := by
    intro μ₁ t₁ hirr hnv μ' E hs
    rcases steps_cases hs with ⟨-, rfl⟩ | ⟨μ₂, e₂, h₂, t₂⟩
    · exact .inl rfl
    · obtain ⟨p, rfl⟩ := head_cfin_inv (step1_appR_irred hnv hirr h₂)
      exact .inr ⟨p, (steps_of_irred (raise_irred p μ₂) t₂).2⟩
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K_E n i v hs hKE w => ?_⟩
  · rcases steps_plug_split (app2K .cfin s) hs with ⟨e', he, -⟩ | ⟨μ₁, t₁, h₁, hirr₁, h₂⟩
    · exact absurd (isVal_eq he) (app2_not_isVal .cfin s e')
    · by_cases hv : IsVal t₁
      · rcases hval _ ⟨t₁, hv⟩ _ _ h₂ with h | ⟨p, h⟩
        · exact absurd (isVal_eq h) (app2_not_isVal .cfin s _)
        · exact absurd (isVal_eq h) (raise_not_isVal p)
      · rcases hirr _ _ hirr₁ hv _ _ h₂ with h | ⟨p, h⟩
        · exact absurd (isVal_eq h) (app2_not_isVal .cfin s _)
        · exact absurd (isVal_eq h) (raise_not_isVal p)
  · rcases steps_plug_split (app2K .cfin s) hs with ⟨e', he, h₁⟩ | ⟨μ₁, t₁, h₁, hirr₁, h₂⟩
    · by_cases hv : IsVal e'
      · exact absurd he.symm (app2_ne_perfAt (by decide) s ⟨e', hv⟩ K_E n i v)
      · obtain ⟨t'', he', -⟩ := stop_inside (Q₁ := fun _ => True) (G₁ := fun _ => False)
          (retsG_true _ t) h₁ hv he.symm hKE w
        exact .inl ⟨t'', he'⟩
    · by_cases hv : IsVal t₁
      · rcases hval _ ⟨t₁, hv⟩ _ _ h₂ with h | ⟨p, h⟩
        · exact absurd h (app2_ne_perfAt (by decide) s ⟨t₁, hv⟩ K_E n i v).symm
        · exact absurd h.symm (raise_ne_perfAt p K_E n i v)
      · rcases hirr _ _ hirr₁ hv _ _ h₂ with h | ⟨p, h⟩
        · obtain ⟨t'', he', -⟩ := stop_inside (K := app2K .cfin s) (Q₁ := fun _ => True)
            (G₁ := fun _ => False) (retsG_true _ t) h₁ hv h.symm hKE w
          exact .inl ⟨t'', he'⟩
        · exact absurd h.symm (raise_ne_perfAt p K_E n i v)

/-- The head steps of `ubind (N, D) e`: `N v` at a value, the unwinding forms at a `raise`. -/
theorem head_ubind_inv {μ μ₁ : Heap} {N D : Val} {e E : Expr}
    (h : Head (ℍ := ℍ) μ (ubindE (Val.pair N D) e) μ₁ E) :
    (∃ v : Val, e = .val v ∧ μ₁ = μ ∧ E = .app (.val N) (.val v)) ∨
      (¬ IsVal e ∧ ((∃ p, E = .seq (.app (.val D) (.val .unit)) (raiseE (.val p))) ∨
        (∃ s, E = cfinE s (.app (.val D) (.val .unit))))) := by
  generalize hE : ubindE (Val.pair N D) e = X at h
  cases h with
  | uthen N' D' w =>
      simp only [ubindE, Expr.app.injEq, true_and] at hE
      obtain ⟨h1, h2⟩ := hE
      obtain ⟨rfl, rfl⟩ := valPair_inj (congrArg id h1)
      exact .inl ⟨w, h2, rfl, rfl⟩
  | ufin N' D' n i v K hn hK =>
      simp only [ubindE, Expr.app.injEq, true_and] at hE
      obtain ⟨h1, h2⟩ := hE
      obtain ⟨rfl, rfl⟩ := valPair_inj (congrArg id h1)
      refine .inr ⟨?_, .inl ⟨_, rfl⟩⟩
      rw [h2]; exact fun hv => raise_not_isVal _ (K.isVal_of_plug hv)
  | ufinC N' D' err K hK =>
      simp only [ubindE, Expr.app.injEq, true_and] at hE
      obtain ⟨h1, h2⟩ := hE
      obtain ⟨rfl, rfl⟩ := valPair_inj (congrArg id h1)
      refine .inr ⟨?_, .inr ⟨_, rfl⟩⟩
      rw [h2]; exact fun hv => raise_not_isVal _ (K.isVal_of_plug hv)
  | _ =>
      exfalso
      simp_all [ubindE, cfinE, BoCa.BoLo.hndE, BoCa.BoLo.ccatchE, Expr.val, Val.prim, Val.lam]

/-- **A finaliser frame.** `ubind (N, D) t`: `t`'s values continue in `N`; its stops resume under
the frame; its unwinding runs `D` and reaches no value, whatever `D` is. -/
theorem retsG_ubind {Q₁ Q : Val → Prop} {G : Expr → Prop} {N D : Val} {t : Expr}
    (ht : RetsG (ℍ := ℍ) Q₁ (fun s => G (ubindE (Val.pair N D) s)) t)
    (hN : ∀ v, Q₁ v → RetsG (ℍ := ℍ) Q G (.app (.val N) (.val v))) :
    RetsG (ℍ := ℍ) Q G (ubindE (Val.pair N D) t) := by
  set K := app2K .ubind (Val.pair N D) with hKdef
  have hub : (Prim.ubind).Inert := trivial
  refine retsG_coind (fun x => ∃ t', x = K.plug t' ∧
      RetsG (ℍ := ℍ) Q₁ (fun s => G (ubindE (Val.pair N D) s)) t') (fun x hx => ?_) ⟨t, rfl, ht⟩
  obtain ⟨t', rfl, ht'⟩ := hx
  -- the unwinding forms
  have hU : ∀ E, ((∃ p, E = .seq (.app (.val D) (.val .unit)) (raiseE (.val p))) ∨
      (∃ s, E = cfinE s (.app (.val D) (.val .unit)))) → RetsG (ℍ := ℍ) Q G E := by
    rintro E (⟨p, rfl⟩ | ⟨s, rfl⟩)
    · exact retsG_seq (retsG_raise p)
    · exact retsG_cfin s _
  have hval : ∀ μ (v : Val) μ' E, Steps (ℍ := ℍ) μ (K.plug (.val v)) μ' E →
      E = K.plug (.val v) ∨ Steps (ℍ := ℍ) μ (.app (.val N) (.val v)) μ' E := by
    intro μ v μ' E hs
    rcases steps_cases hs with ⟨-, rfl⟩ | ⟨μ₁, e₁, h₁, t₁⟩
    · exact .inl rfl
    · rcases step1_app2 hub h₁ with ⟨e', -, he'⟩ | hh
      · exact absurd he' no_step_val
      · rcases head_ubind_inv hh with ⟨v', hv', rfl, rfl⟩ | ⟨hnv, -⟩
        · have : v' = v := Subtype.ext (by simpa using hv'.symm)
          subst this; exact .inr t₁
        · exact absurd v.2 hnv
  have hirr : ∀ μ₁ t₁, (∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ₁ t₁ μ₂ t₂) → ¬ IsVal t₁ →
      ∀ μ' E, Steps (ℍ := ℍ) μ₁ (K.plug t₁) μ' E → E = K.plug t₁ ∨
        ∃ μ₂ E₂, RetsG (ℍ := ℍ) Q G E₂ ∧ Steps (ℍ := ℍ) μ₂ E₂ μ' E := by
    intro μ₁ t₁ hirr hnv μ' E hs
    rcases steps_cases hs with ⟨-, rfl⟩ | ⟨μ₂, e₂, h₂, t₂⟩
    · exact .inl rfl
    · rcases head_ubind_inv (step1_appR_irred hnv hirr h₂) with ⟨v, rfl, -, -⟩ | ⟨-, hu⟩
      · exact absurd v.2 hnv
      · exact .inr ⟨_, _, hU _ hu, t₂⟩
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K_E n i v hs hKE w => ?_⟩
  · rcases steps_plug_split K hs with ⟨e', he, -⟩ | ⟨μ₁, t₁, h₁, hirr₁, h₂⟩
    · exact absurd (isVal_eq he) (app2_not_isVal .ubind _ e')
    · by_cases hv : IsVal t₁
      · have hq := (retsG_unfold ht').1 _ _ ⟨t₁, hv⟩ h₁
        rcases hval _ ⟨t₁, hv⟩ _ _ h₂ with h | h
        · exact absurd (isVal_eq h) (app2_not_isVal .ubind _ _)
        · exact (retsG_unfold (hN _ hq)).1 _ _ _ h
      · rcases hirr _ _ hirr₁ hv _ _ h₂ with h | ⟨μ₂, E₂, hE₂, h⟩
        · exact absurd (isVal_eq h) (app2_not_isVal .ubind _ _)
        · exact (retsG_unfold hE₂).1 _ _ _ h
  · have inside : ∀ μ₁ e', Steps (ℍ := ℍ) μ t' μ₁ e' → ¬ IsVal e' → K.plug e' = perfAt K_E n i v →
        ((∃ t'', K_E.plug (.val w) = K.plug t'' ∧
          RetsG (ℍ := ℍ) Q₁ (fun s => G (ubindE (Val.pair N D) s)) t'') ∨
          RetsG (ℍ := ℍ) Q G (K_E.plug (.val w)) ∨ G (K_E.plug (.val w))) := by
      intro μ₁ e' h₁ hnv he
      obtain ⟨t'', he', h''⟩ := stop_inside (K := K) ht' h₁ hnv he hKE w
      rcases h'' with h'' | h''
      · exact .inl ⟨t'', he', h''⟩
      · exact .inr (.inr (he' ▸ h''))
    rcases steps_plug_split K hs with ⟨e', he, h₁⟩ | ⟨μ₁, t₁, h₁, hirr₁, h₂⟩
    · by_cases hv : IsVal e'
      · exact absurd he.symm (app2_ne_perfAt (by decide) _ ⟨e', hv⟩ K_E n i v)
      · exact inside _ _ h₁ hv he.symm
    · by_cases hv : IsVal t₁
      · have hq := (retsG_unfold ht').1 _ _ ⟨t₁, hv⟩ h₁
        rcases hval _ ⟨t₁, hv⟩ _ _ h₂ with h | h
        · exact absurd h (app2_ne_perfAt (by decide) _ ⟨t₁, hv⟩ K_E n i v).symm
        · exact ((retsG_unfold (hN _ hq)).2 _ _ _ _ _ _ h hKE w).elim (fun h => .inr (.inl h))
            (fun h => .inr (.inr h))
      · rcases hirr _ _ hirr₁ hv _ _ h₂ with h | ⟨μ₂, E₂, hE₂, h⟩
        · exact inside _ _ h₁ hv h.symm
        · exact ((retsG_unfold hE₂).2 _ _ _ _ _ _ h hKE w).elim (fun h => .inr (.inl h))
            (fun h => .inr (.inr h))

/-! ### Administrative steps -/

/-- A term with a step is no stop. -/
theorem step_not_perfAt {μ μ₁ : Heap} {t t₁ : Expr} (h : Step1 (ℍ := ℍ) μ t μ₁ t₁) (K : Kont)
    (n i : UInt32) (v : Val) (hK : K.HasHnd n = false) : t ≠ perfAt K n i v := by
  rintro rfl
  exact perfAt_irred hK μ _ _ h

/-- **A step**, at any term with a step, all of whose steps lead into the invariant. -/
theorem retsG_step' {Q : Val → Prop} {G : Expr → Prop} {t : Expr}
    (hex : ∃ μ μ₁ t₁, Step1 (ℍ := ℍ) μ t μ₁ t₁)
    (h : ∀ μ μ₁ t₁, Step1 (ℍ := ℍ) μ t μ₁ t₁ → RetsG (ℍ := ℍ) Q G t₁) : RetsG (ℍ := ℍ) Q G t := by
  obtain ⟨μ₀, μ₀', t₀, h₀⟩ := hex
  refine retsG_coind (fun s => s = t) (fun t' ht => ?_) rfl
  subst ht
  refine ⟨fun μ μ' w hs => ?_, fun μ μ' K n i v hs hK w => ?_⟩
  · rcases steps_cases hs with ⟨-, h'⟩ | ⟨μ₁, e₁, h₁, t₁⟩
    · subst h'; exact absurd h₀ no_step_val
    · exact (retsG_unfold (h _ _ _ h₁)).1 _ _ _ t₁
  · rcases steps_cases hs with ⟨-, h'⟩ | ⟨μ₁, e₁, h₁, t₁⟩
    · exact absurd h'.symm (step_not_perfAt h₀ K n i v hK)
    · exact ((retsG_unfold (h _ _ _ h₁)).2 _ _ _ _ _ _ t₁ hK w).elim (fun h => .inr (.inl h))
        (fun h => .inr (.inr h))

/-- **A deterministic redex in any context**: `K[e]` satisfies what `K[e']` does, `e ↦ e'` the
redex's only step. -/
theorem retsG_ctx_det {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {e e' : Expr}
    (h₀ : ∃ μ, Head (ℍ := ℍ) μ e μ e')
    (hdet : ∀ μ μ₁ e₁, Step1 (ℍ := ℍ) μ e μ₁ e₁ → μ₁ = μ ∧ e₁ = e')
    (h : RetsG (ℍ := ℍ) Q G (K.plug e')) : RetsG (ℍ := ℍ) Q G (K.plug e) := by
  obtain ⟨μ₀, h₀⟩ := h₀
  refine retsG_step' ⟨μ₀, μ₀, K.plug e', ⟨K, e, e', rfl, rfl, h₀⟩⟩ (fun μ μ₁ t₁ hst => ?_)
  obtain ⟨e₁, rfl, he₁⟩ := step1_plug_inv_active K .hole rfl h₀ hst
  obtain ⟨-, rfl⟩ := hdet _ _ _ he₁
  exact h

theorem retsG_beta {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {b : Expr} {v : Val}
    (h : RetsG (ℍ := ℍ) Q G (K.plug (b.subst 0 v))) :
    RetsG (ℍ := ℍ) Q G (K.plug (.app (.val (.lam b)) (.val v))) :=
  retsG_ctx_det K ⟨fun _ => none, Head.beta _ b v⟩
    (fun _ _ _ hst => step1_beta_inv (b := b) (v := v) hst) h

theorem retsG_letpair {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {b : Expr} {v₁ v₂ : Val}
    (h : RetsG (ℍ := ℍ) Q G (K.plug ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁))) :
    RetsG (ℍ := ℍ) Q G (K.plug (.letpair (.val (Val.pair v₁ v₂)) b)) := by
  refine retsG_ctx_det K ⟨fun _ => none, Head.letpair _ v₁ v₂ b⟩ (fun μ μ₁ e₁ hst => ?_) h
  obtain ⟨u₁, u₂, hu, rfl, rfl⟩ := step1_letpair_inv hst
  obtain ⟨rfl, rfl⟩ := valPair_inj (congrArg Subtype.val hu)
  exact ⟨rfl, rfl⟩

/-- `case v {…}` steps only to the branch of `v`. -/
theorem step1_case_inv {μ μ₁ : Heap} {v : Val} {e₁ e₂ E : Expr}
    (h : Step1 (ℍ := ℍ) μ (.case (.val v) e₁ e₂) μ₁ E) :
    μ₁ = μ ∧ ((∃ a, v = Val.inj₁ a ∧ E = e₁.subst 0 a) ∨ (∃ a, v = Val.inj₂ a ∧ E = e₂.subst 0 a)) := by
  obtain ⟨K', a, a', he, rfl, hh⟩ := h
  cases K' with
  | hole =>
      simp only [Kont.plug] at he ⊢; subst he
      generalize hE : Expr.case (.val v) e₁ e₂ = X at hh
      cases hh with
      | case₁ u f₁ f₂ =>
          simp only [Expr.case.injEq] at hE
          obtain ⟨h1, rfl, rfl⟩ := hE
          exact ⟨rfl, .inl ⟨u, Subtype.ext h1, rfl⟩⟩
      | case₂ u f₁ f₂ =>
          simp only [Expr.case.injEq] at hE
          obtain ⟨h1, rfl, rfl⟩ := hE
          exact ⟨rfl, .inr ⟨u, Subtype.ext h1, rfl⟩⟩
      | _ => simp_all [BoCa.BoLo.hndE, ubindE, BoCa.BoLo.ccatchE, cfinE]
  | case K₂ f₁ f₂ =>
      simp only [Kont.plug, Expr.case.injEq] at he
      exact absurd (K₂.isVal_of_plug (by rw [← he.1]; exact v.2)) hh.not_isVal
  | _ => simp [Kont.plug] at he

theorem retsG_case₁ {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {e₁ e₂ : Expr} {a : Val}
    (h : RetsG (ℍ := ℍ) Q G (K.plug (e₁.subst 0 a))) :
    RetsG (ℍ := ℍ) Q G (K.plug (.case (.val (Val.inj₁ a)) e₁ e₂)) := by
  refine retsG_ctx_det K ⟨fun _ => none, Head.case₁ _ a e₁ e₂⟩ (fun μ μ₁ e hst => ?_) h
  obtain ⟨rfl, ⟨u, hu, rfl⟩ | ⟨u, hu, -⟩⟩ := step1_case_inv hst
  · have : u = a := Subtype.ext (by simpa [Val.inj₁] using (congrArg Subtype.val hu).symm)
    subst this; exact ⟨rfl, rfl⟩
  · exact absurd (congrArg Subtype.val hu) (by simp [Val.inj₁, Val.inj₂])

theorem retsG_case₂ {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {e₁ e₂ : Expr} {a : Val}
    (h : RetsG (ℍ := ℍ) Q G (K.plug (e₂.subst 0 a))) :
    RetsG (ℍ := ℍ) Q G (K.plug (.case (.val (Val.inj₂ a)) e₁ e₂)) := by
  refine retsG_ctx_det K ⟨fun _ => none, Head.case₂ _ a e₁ e₂⟩ (fun μ μ₁ e hst => ?_) h
  obtain ⟨rfl, ⟨u, hu, -⟩ | ⟨u, hu, rfl⟩⟩ := step1_case_inv hst
  · exact absurd (congrArg Subtype.val hu) (by simp [Val.inj₁, Val.inj₂])
  · have : u = a := Subtype.ext (by simpa [Val.inj₂] using (congrArg Subtype.val hu).symm)
    subst this; exact ⟨rfl, rfl⟩

theorem retsG_seqU {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {X : Expr}
    (h : RetsG (ℍ := ℍ) Q G (K.plug X)) :
    RetsG (ℍ := ℍ) Q G (K.plug (.seq (.val .unit) X)) := by
  refine retsG_ctx_det K ⟨fun _ => none, Head.seq _ X⟩ (fun μ μ₁ e hst => ?_) h
  obtain ⟨-, rfl, rfl⟩ := step1_seq_inv hst
  exact ⟨rfl, rfl⟩

/-- `let (x, y) = v; b` at the top, any value `v`: at a pair what its body does; else stuck. -/
theorem retsG_letpairV {Q : Val → Prop} {G : Expr → Prop} {b : Expr} {v : Val}
    (h : ∀ v₁ v₂, v = Val.pair v₁ v₂ →
      RetsG (ℍ := ℍ) Q G ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁)) :
    RetsG (ℍ := ℍ) Q G (.letpair (.val v) b) := by
  by_cases hp : ∃ v₁ v₂, v = Val.pair v₁ v₂
  · obtain ⟨v₁, v₂, rfl⟩ := hp
    exact retsG_letpair .hole (h v₁ v₂ rfl)
  · refine retsG_stuck (fun μ μ₂ t₂ hst => ?_) (by intro h; cases h) (fun K n i u he => ?_)
    · obtain ⟨v₁, v₂, hv, -⟩ := step1_letpair_inv hst
      exact hp ⟨v₁, v₂, hv⟩
    · cases K with
      | letpair K₂ e =>
          simp only [perfAt, Kont.plug, Expr.letpair.injEq] at he
          exact perform_not_isVal _ (K₂.isVal_of_plug (by rw [← he.1]; exact v.2))
      | _ => simp [perfAt, Kont.plug, performE] at he

/-- `case v {…}` at the top, any value `v`. -/
theorem retsG_caseV {Q : Val → Prop} {G : Expr → Prop} {e₁ e₂ : Expr} {v : Val}
    (h₁ : ∀ a, v = Val.inj₁ a → RetsG (ℍ := ℍ) Q G (e₁.subst 0 a))
    (h₂ : ∀ a, v = Val.inj₂ a → RetsG (ℍ := ℍ) Q G (e₂.subst 0 a)) :
    RetsG (ℍ := ℍ) Q G (.case (.val v) e₁ e₂) := by
  by_cases hp : (∃ a, v = Val.inj₁ a) ∨ (∃ a, v = Val.inj₂ a)
  · rcases hp with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact retsG_case₁ .hole (h₁ a rfl)
    · exact retsG_case₂ .hole (h₂ a rfl)
  · refine retsG_stuck (fun μ μ₂ t₂ hst => ?_) (by intro h; cases h) (fun K n i u he => ?_)
    · obtain ⟨-, ⟨a, ha, -⟩ | ⟨a, ha, -⟩⟩ := step1_case_inv hst
      · exact hp (.inl ⟨a, ha⟩)
      · exact hp (.inr ⟨a, ha⟩)
    · cases K with
      | case K₂ f₁ f₂ =>
          simp only [perfAt, Kont.plug, Expr.case.injEq] at he
          exact perform_not_isVal _ (K₂.isVal_of_plug (by rw [← he.1]; exact v.2))
      | _ => simp [perfAt, Kont.plug, performE] at he

theorem pairV_inj {a b c d : Val} (h : Val.pair a b = Val.pair c d) : a = c ∧ b = d :=
  valPair_inj (congrArg Subtype.val h)

/-! ### Primitives at one argument -/

/-- `p v`, `p` not `perform`, is not a stop. -/
theorem app1_ne_perfAt {p : Prim} (hp : p ≠ .perform) (x : Val) (K : Kont) (n i : UInt32)
    (v : Val) : Expr.app (.val (.prim p)) (.val x) ≠ perfAt K n i v := by
  intro he
  cases K with
  | hole =>
      simp only [perfAt, Kont.plug, performE, Expr.app.injEq] at he
      exact hp (by simpa [Expr.val, Val.prim] using he.1)
  | appR f K₂ =>
      simp only [perfAt, Kont.plug, Expr.app.injEq] at he
      exact perform_not_isVal _ (K₂.isVal_of_plug (by rw [← he.2]; exact x.2))
  | appL K₂ w =>
      simp only [perfAt, Kont.plug, Expr.app.injEq] at he
      exact perform_not_isVal _ (K₂.isVal_of_plug (by rw [← he.1]; exact IsVal.prim))
  | _ => simp [perfAt, Kont.plug] at he

/-- A step of `p v`, all values, is its head step. -/
theorem step1_app1_head {μ μ₁ : Heap} {p : Prim} {x : Val} {E : Expr}
    (h : Step1 (ℍ := ℍ) μ (.app (.val (.prim p)) (.val x)) μ₁ E) :
    Head (ℍ := ℍ) μ (.app (.val (.prim p)) (.val x)) μ₁ E := by
  obtain ⟨K', a, a', he, rfl, hh⟩ := h
  cases K' with
  | hole => simp only [Kont.plug] at he ⊢; subst he; exact hh
  | appR f K₂ =>
      simp only [Kont.plug, Expr.app.injEq] at he
      exact absurd (K₂.isVal_of_plug (by rw [← he.2]; exact x.2)) hh.not_isVal
  | appL K₂ w =>
      simp only [Kont.plug, Expr.app.injEq] at he
      exact absurd (K₂.isVal_of_plug (by rw [← he.1]; exact IsVal.prim)) hh.not_isVal
  | _ => simp [Kont.plug] at he

/-- `count_try` steps only at `(f, (n, (i, s)))`, to `countTryNext f n i s`. -/
theorem step1_countTry_inv {μ μ₁ : Heap} {x : Val} {E : Expr}
    (h : Step1 (ℍ := ℍ) μ (.app (.val (.prim .countTry)) (.val x)) μ₁ E) :
    ∃ f n i s, x = Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)) ∧ μ₁ = μ ∧
      E = countTryNext f n i s := by
  have hh := step1_app1_head h
  generalize hE : Expr.app (.val (.prim .countTry)) (.val x) = X at hh
  cases hh with
  | countTry f n i s =>
      simp only [Expr.app.injEq, true_and] at hE
      exact ⟨f, n, i, s, Subtype.ext hE, rfl, rfl⟩
  | _ => exfalso; simp_all [BoCa.BoLo.hndE, ubindE, BoCa.BoLo.ccatchE, cfinE, Expr.val, Val.prim]

/-! ### The counted loop -/

/-- The answers of a counted loop: `inj₁` of a state in `P`, or `inj₂` of an exit in `X`. -/
def CountQ (P X : Val → Prop) (y : Val) : Prop :=
  (∃ s, y = Val.inj₁ s ∧ P s) ∨ (∃ x, y = Val.inj₂ x ∧ X x)

/-- **The counted loop keeps its invariant**: a step that maps states of `P` to `CountQ P X`
makes `count_try` answer `CountQ P X`, by induction on the turns left. -/
theorem retsG_countTry {G : Expr → Prop} {P X : Val → Prop} (f : Val) (n : UInt32)
    (hf : ∀ (i : UInt32) s, P s →
      RetsG (ℍ := ℍ) (CountQ P X) (fun _ => False) (.app (.val f) (.val (Val.pair (Val.i32 i) s)))) :
    ∀ (k : Nat) (i : UInt32) (s : Val), (arrLen n).toNat - i.toNat = k → P s →
      RetsG (ℍ := ℍ) (CountQ P X) G (.app (.val (.prim .countTry))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))))) := by
  intro k
  induction k with
  | zero =>
      intro i s hk hs
      refine retsG_step' ⟨fun _ => none, _, _, Step1.head (Head.countTry _ f n i s)⟩
        (fun μ μ₁ t₁ hst => ?_)
      obtain ⟨f', n', i', s', hx, -, rfl⟩ := step1_countTry_inv hst
      obtain ⟨hf', hx⟩ := pairV_inj hx
      obtain ⟨hn, hx⟩ := pairV_inj hx
      obtain ⟨hi, hs'⟩ := pairV_inj hx
      subst hf' hs'
      have hn' : n' = n := by simpa [Val.i32] using (congrArg Subtype.val hn).symm
      have hi' : i' = i := by simpa [Val.i32] using (congrArg Subtype.val hi).symm
      subst hn' hi'
      have hi : ¬ i' < arrLen n' := by rw [UInt32.lt_iff_toNat_lt]; omega
      unfold countTryNext
      rw [if_neg hi]
      exact retsG_val (.inl ⟨_, rfl, hs⟩)
  | succ k ih =>
      intro i s hk hs
      refine retsG_step' ⟨fun _ => none, _, _, Step1.head (Head.countTry _ f n i s)⟩
        (fun μ μ₁ t₁ hst => ?_)
      obtain ⟨f', n', i', s', hx, -, rfl⟩ := step1_countTry_inv hst
      obtain ⟨hf', hx⟩ := pairV_inj hx
      obtain ⟨hn, hx⟩ := pairV_inj hx
      obtain ⟨hi, hs'⟩ := pairV_inj hx
      subst hf' hs'
      have hn' : n' = n := by simpa [Val.i32] using (congrArg Subtype.val hn).symm
      have hi' : i' = i := by simpa [Val.i32] using (congrArg Subtype.val hi).symm
      subst hn' hi'
      have hlt : i' < arrLen n' := by rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n'
      have hi1 : (i' + 1).toNat = i'.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i'.toNat < (arrLen n').toNat := UInt32.lt_iff_toNat_lt.mp hlt
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      unfold countTryNext
      rw [if_pos hlt]
      refine retsG_plain (K := .case .hole _ _) rfl
        (retsG_mono (fun _ h => h) (fun _ (h : False) => h.elim) (hf i' s hs)) ?_
      rintro y (⟨s'', rfl, hs''⟩ | ⟨x, rfl, hx⟩)
      · refine retsG_case₁ .hole ?_
        simp only [Kont.plug]
        rw [countTry_cont_subst]
        exact ih (i' + 1) s'' (by omega) hs''
      · refine retsG_case₂ .hole ?_
        exact retsG_val (w := Val.inj₂ x) (.inr ⟨x, rfl, hx⟩)

/-- `count_try` at an argument that is not `(f, (n, (i, s)))` is stuck. -/
theorem retsG_countTry_stuck {Q : Val → Prop} {G : Expr → Prop} {x : Val}
    (hx : ¬ ∃ f n i s, x = Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s))) :
    RetsG (ℍ := ℍ) Q G (.app (.val (.prim .countTry)) (.val x)) := by
  refine retsG_stuck (fun μ μ₂ t₂ hst => ?_) ?_ (fun K n i v => app1_ne_perfAt (by decide) x K n i v)
  · obtain ⟨f, n, i, s, h, -⟩ := step1_countTry_inv hst
    exact hx ⟨f, n, i, s, h⟩
  · intro h; simp at h

/-! ### The div loop -/

/-- `iterate` steps only at a pair, to `iterNext`. -/
theorem step1_iterate_inv {μ μ₁ : Heap} {x : Val} {E : Expr}
    (h : Step1 (ℍ := ℍ) μ (.app (.val (.prim .iterate)) (.val x)) μ₁ E) :
    ∃ f s, x = Val.pair f s ∧ μ₁ = μ ∧ E = iterNext f s := by
  have hh := step1_app1_head h
  generalize hE : Expr.app (.val (.prim .iterate)) (.val x) = X at hh
  cases hh with
  | iterate f s =>
      simp only [Expr.app.injEq, true_and] at hE
      exact ⟨f, s, Subtype.ext hE, rfl, rfl⟩
  | _ => exfalso; simp_all [BoCa.BoLo.hndE, ubindE, BoCa.BoLo.ccatchE, cfinE, Expr.val, Val.prim]

/-- The answers of a turn: `inj₁` of a result in `X`, or `inj₂` of a next state in `P`. -/
def TurnQ (P X : Val → Prop) (y : Val) : Prop :=
  (∃ x, y = Val.inj₁ x ∧ X x) ∨ (∃ s, y = Val.inj₂ s ∧ P s)

/-- The answers of a div loop: `inj₁` of a result in `X`, or `inj₂` of a residual in `R`. -/
def IterQ (X R : Val → Prop) (y : Val) : Prop :=
  (∃ x, y = Val.inj₁ x ∧ X x) ∨ (∃ r, y = Val.inj₂ r ∧ R r)

/-- The states a div loop resumes into after a tick: the case on the tick's answer. -/
def TickG (f : Val) (P : Val → Prop) (t : Expr) : Prop :=
  ∃ s w, P s ∧ t = .app (.val (.lam ((iterTurn f).subst 1 (s.shift 1 0)))) (.val w)

theorem divEff_tick : tickE = perfAt .hole divEff 0 .unit := rfl

theorem subst_inrV (j : Nat) (s : Val) : Expr.subst j s inrV.1 = inrV.1 := by
  simp [inrV, Val.lam, Expr.subst]

theorem subst_closeV (j : Nat) (s : Val) : Expr.subst j s closeV.1 = closeV.1 := by
  simp [closeV, Val.inj₂, Val.unit, Expr.subst]

/-- **The div loop keeps its invariant**, coinductively: every turn answers `TurnQ P X`, and the
step's residual answers `R`, so the loop answers `IterQ X R` on every run, through its ticks. -/
theorem retsG_iterate {P X R : Val → Prop} (f : Val)
    (hturn : ∀ s, P s →
      RetsG (ℍ := ℍ) (TurnQ P X) (fun _ => False) (.app (.app (.val f) (.val s)) (.val nextV)))
    (hclose : ∀ s, P s →
      RetsG (ℍ := ℍ) R (fun _ => False) (.app (.app (.val f) (.val s)) (.val closeV)))
    {s : Val} (hs : P s) :
    RetsG (ℍ := ℍ) (IterQ X R) (fun _ => False) (.app (.val (.prim .iterate)) (.val (Val.pair f s))) := by
  -- one turn, up to the ticks it resumes into
  have hone : ∀ s, P s → RetsG (ℍ := ℍ) (IterQ X R) (TickG f P)
      (.app (.val (.prim .iterate)) (.val (Val.pair f s))) := by
    intro s hs
    refine retsG_step' ⟨fun _ => none, _, _, Step1.head (Head.iterate _ f s)⟩ (fun μ μ₁ t₁ hst => ?_)
    obtain ⟨f', s', hx, -, rfl⟩ := step1_iterate_inv hst
    obtain ⟨hf', hs'⟩ := pairV_inj hx
    subst hf' hs'
    unfold iterNext
    refine retsG_plain (K := .case .hole _ _) rfl
      (retsG_mono (fun _ h => h) (fun _ (h : False) => h.elim) (hturn s hs)) ?_
    rintro y (⟨x, rfl, hx⟩ | ⟨s'', rfl, hs''⟩)
    · refine retsG_case₁ .hole ?_
      exact retsG_val (w := Val.inj₁ x) (.inl ⟨x, rfl, hx⟩)
    · refine retsG_case₂ .hole ?_
      simp only [Kont.plug, Expr.subst, divEff_tick]
      change RetsG _ _ (perfAt (.appR (.val (.lam ((iterTurn f).subst 1 (s''.shift 1 0)))) .hole)
        divEff 0 .unit)
      refine retsG_perform (by simp [Kont.HasHnd, Expr.val, Val.lam]) (fun w => .inr ⟨s'', w, hs'', rfl⟩)
  -- a resumption after a tick
  have hres : ∀ t, TickG f P t → RetsG (ℍ := ℍ) (IterQ X R) (TickG f P) t := by
    rintro t ⟨s, w, hs, rfl⟩
    refine retsG_beta .hole ?_
    simp only [Kont.plug, iterTurn]
    simp [Expr.subst, Expr.val, subst_shift_succ, Expr.shift_shift]
    refine retsG_caseV (fun u _ => ?_) (fun u _ => ?_)
    · simp [Expr.subst, subst_shift_expr]
      exact hone s hs
    · simp only [subst_inrV, subst_closeV]
      simp only [Expr.subst, subst_shift_expr, subst_closeV]
      refine retsG_plain (K := .appR (.val inrV) .hole) rfl (Q₁ := R)
        (retsG_mono (fun _ h => h) (fun _ (h : False) => h.elim) (hclose s hs)) (fun r hr => ?_)
      refine retsG_beta .hole ?_
      simp only [Kont.plug, Expr.subst, if_true]
      exact retsG_val (w := Val.inj₂ r) (.inr ⟨r, rfl, hr⟩)
  exact retsG_close hres (hone s hs)

end BoCa.Fig16.LogRel.Core.Frames

end
