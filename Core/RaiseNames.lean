import Core.Tied

/-!
# Core — the names a run raises, and the errors a cancel keeps  `[spec §19]`

A cancel keeps the first error a finaliser of the cancelled region raised (`errNext`), in its
payload `cancelVal err` and in the `cfin` frame of each running finaliser.  `Expr.RaiseOK P` says
of a term that each raise and each cancel state in it is at the names `P`:

* `raise` occurs only applied to a literal-named payload `(m, r)`: `m` is a name in `P`, or the
  reserved `0` at a cancel's state;
* `cfin` occurs only applied to a cancel's state;
* a cancel's state keeps nothing, `(0, (0, inj₁ ()))`, or a raise `(m, (j, w))` of a name `m` in
  `P` (`CancelShape`).

No machine step breaks it, nor does a stored value (`raiseOK_step1`, `HeapRaiseOK`), when `0` is
not one of the names `P`.  A step builds a raise only from the raise it consumes or from the state
of the cancel it passes, and it builds a cancel state only from a raise of a nonzero name, which is
then in `P`, or from cancel states.  `κ`'s cancel branch raises a cancel that keeps nothing.

* **A tied term raises only its effect context's names** (`raiseOK_of_derivesAt`): `[raise]` finds
  its operation in a row tied to `Ξ` (decision R), whose names are `Ξ`'s (`EffCtx.Names`), and no
  rule types a `cfin`.  `rcE` decides it, soundly (`rcE_sound`), and every tied derivation's term
  passes `rcE` (`rcE_of_derivesAt`).
* **No run leaves them** (`raiseOK_reach`): every configuration a run of a tied term reaches from
  the empty memory, and every value its memory stores, is at `Ξ`'s names.
* **`CancelsNamed`** (`cancelsNamed_of_derivesAt`): at every configuration such a run reaches that
  cancels a continuation `κ`, `kappa H K` or `kappaC hasCancel ℓ H K` applied to `inj₂ ()`, every
  running finaliser's `cfin` frame of `K` keeps none or a raise of a name of `Ξ` (`KCfinNamed`).
  `κ`'s resume branch holds `K`, shifted past the branch's binders (`kraiseOK_of_kappa`,
  `kraiseOK_of_kappaC`), and a shift keeps the names its running finalisers keep
  (`kcfinNamed_of_shift`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal errVal errNext hndE
  hndVal kappa kappaC kappaAt kappaCell kappaCBody freeE stuckE ccatchE cfinE ubindE clauseAt)
open BoCa.Lifetime (LifeCtx)

/-! ### The predicate -/

section Defs
variable (P : UInt32 → Prop)

/-- **A cancel's state past its name**: nothing kept, `(0, inj₁ ())`, or a kept raise of a name in
`P`, `(0, inj₂ (m, (j, y)))`.  `[spec §19]` -/
def CancelShape (r : Expr) : Prop :=
  r = .pair (.prim (.lit (.i32 0))) (.inj₁ .unit) ∨
    ∃ m j y, r = .pair (.prim (.lit (.i32 0)))
      (.inj₂ (.pair (.prim (.lit (.i32 m))) (.pair (.prim (.lit (.i32 j))) y))) ∧ P m

/-- **What an application of `f` asks of its argument**: a `raise` asks for a literal-named payload
of a name in `P` or of a cancel; a `cfin` asks for a cancel's state. -/
def AppOK (f a : Expr) : Prop :=
  (f = .prim .raise →
      ∃ m r, a = .pair (.prim (.lit (.i32 m))) r ∧ (P m ∨ (m = 0 ∧ CancelShape P r))) ∧
    (f = .prim .cfin → ∃ r, a = .pair (.prim (.lit (.i32 0))) r ∧ CancelShape P r)

end Defs

/-- **Every raise and every cancel state of a term is at the names `P`**: `raise` and `cfin` occur
only as the function of an application, at the argument `AppOK` asks for.  `[spec §19]` -/
def _root_.BoCa.Expr.RaiseOK (P : UInt32 → Prop) : Expr → Prop
  | .app f a => (f = .prim .raise ∨ f = .prim .cfin ∨ f.RaiseOK P) ∧ a.RaiseOK P ∧ AppOK P f a
  | .prim p => p ≠ .raise ∧ p ≠ .cfin
  | .var _ | .unit | .loc _ => True
  | .pair a b | .seq a b | .letpair a b => a.RaiseOK P ∧ b.RaiseOK P
  | .inj₁ a | .inj₂ a | .lam a => a.RaiseOK P
  | .case a b c => a.RaiseOK P ∧ b.RaiseOK P ∧ c.RaiseOK P

/-- **A kept error at the names `P`**: none, or a raise `(m, (j, w))` of a name in `P` whose
argument is at `P` too. -/
def ErrOK (P : UInt32 → Prop) : Option Val → Prop
  | none => True
  | some E => ∃ m j w, E = opPayload m j w ∧ P m ∧ w.1.RaiseOK P

/-- Every stored value is at the names `P`.  `[spec §19]` -/
def HeapRaiseOK (P : UInt32 → Prop) (μ : Heap) : Prop := ∀ ℓ v, μ ℓ = some v → v.1.RaiseOK P

/-- `K` around a variable is at the names `P`. -/
def KRaiseOK (P : UInt32 → Prop) (K : Kont) : Prop := (K.plug (.var 0)).RaiseOK P

/-- **A term none of whose shapes `RaiseOK` reads at an argument**: an application, a sequence, a
`let`-pair, a `case` or a variable.  Every redex is one, and so is the variable `KRaiseOK` plugs. -/
def Plain : Expr → Prop
  | .app _ _ | .seq _ _ | .letpair _ _ | .case _ _ _ | .var _ => True
  | _ => False

section Lemmas
variable {P : UInt32 → Prop}

/-! ### Applications -/

theorem not_raiseOK_raise : ¬ (Expr.prim .raise).RaiseOK P := fun h => h.1 rfl

theorem not_raiseOK_cfin : ¬ (Expr.prim .cfin).RaiseOK P := fun h => h.2 rfl

theorem raiseOK_app {f a : Expr} : (Expr.app f a).RaiseOK P ↔
    (f = .prim .raise ∨ f = .prim .cfin ∨ f.RaiseOK P) ∧ a.RaiseOK P ∧ AppOK P f a := Iff.rfl

/-- An application whose function is neither `raise` nor `cfin` is at `P` exactly when its parts
are. -/
theorem raiseOK_app_of_ne {f a : Expr} (h₁ : f ≠ .prim .raise) (h₂ : f ≠ .prim .cfin) :
    (Expr.app f a).RaiseOK P ↔ f.RaiseOK P ∧ a.RaiseOK P := by
  rw [raiseOK_app]
  constructor
  · rintro ⟨hf | hf | hf, ha, -⟩
    · exact absurd hf h₁
    · exact absurd hf h₂
    · exact ⟨hf, ha⟩
  · rintro ⟨hf, ha⟩
    exact ⟨.inr (.inr hf), ha, fun h => absurd h h₁, fun h => absurd h h₂⟩

/-- An application of a primitive other than `raise` and `cfin` is at `P` exactly when its argument
is. -/
theorem raiseOK_primApp {p : Prim} (h₁ : p ≠ .raise) (h₂ : p ≠ .cfin) (a : Expr) :
    (Expr.app (.prim p) a).RaiseOK P ↔ a.RaiseOK P := by
  rw [raiseOK_app_of_ne (fun h => h₁ (Expr.prim.inj h)) (fun h => h₂ (Expr.prim.inj h))]
  exact ⟨fun h => h.2, fun h => ⟨⟨h₁, h₂⟩, h⟩⟩

theorem raiseOK_app_val {f a : Expr} (hf : f.RaiseOK P) (ha : a.RaiseOK P) :
    (Expr.app f a).RaiseOK P := by
  by_cases h₁ : f = .prim .raise
  · subst h₁; exact absurd hf not_raiseOK_raise
  by_cases h₂ : f = .prim .cfin
  · subst h₂; exact absurd hf not_raiseOK_cfin
  exact (raiseOK_app_of_ne h₁ h₂).2 ⟨hf, ha⟩

theorem raiseOK_app_inv {f a : Expr} (h₁ : f ≠ .prim .raise) (h₂ : f ≠ .prim .cfin)
    (h : (Expr.app f a).RaiseOK P) : f.RaiseOK P ∧ a.RaiseOK P :=
  (raiseOK_app_of_ne h₁ h₂).1 h

/-- The function of an application at the names `P`, a λ-value, is at `P`. -/
theorem raiseOK_app_lam_inv {b a : Expr} (h : (Expr.app (.lam b) a).RaiseOK P) :
    (Expr.lam b).RaiseOK P :=
  (raiseOK_app_inv (f := .lam b) (a := a) (fun h => (nomatch h)) (fun h => (nomatch h)) h).1

/-! ### Payloads and cancel states -/

theorem opPayload_val (n i : UInt32) (v : Val) :
    (opPayload n i v).1 = .pair (.prim (.lit (.i32 n))) (.pair (.prim (.lit (.i32 i))) v.1) := rfl

theorem raiseOK_prim_of {p : Prim} (h₁ : p ≠ .raise) (h₂ : p ≠ .cfin) :
    (Expr.prim p).RaiseOK P := ⟨h₁, h₂⟩

theorem raiseOK_lit (c : IntLit) : (Expr.prim (.lit c)).RaiseOK P := by
  show Prim.lit c ≠ .raise ∧ Prim.lit c ≠ .cfin
  exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem raiseOK_pairLit {c : IntLit} {r : Expr} :
    (Expr.pair (.prim (.lit c)) r).RaiseOK P ↔ r.RaiseOK P :=
  ⟨fun h => h.2, fun h => ⟨raiseOK_lit c, h⟩⟩

theorem raiseOK_opPayload {n i : UInt32} {v : Val} :
    (opPayload n i v).1.RaiseOK P ↔ v.1.RaiseOK P := by
  rw [opPayload_val, raiseOK_pairLit, raiseOK_pairLit]

/-- A raise is at `P` exactly when its payload is literal-named at a name in `P`, or a cancel at a
cancel's state, and the payload is at `P`. -/
theorem raiseOK_raiseE {p : Val} : (raiseE (.val p)).RaiseOK P ↔
    (∃ m r, p.1 = .pair (.prim (.lit (.i32 m))) r ∧ (P m ∨ (m = 0 ∧ CancelShape P r))) ∧
      p.1.RaiseOK P := by
  show (Expr.app (.prim .raise) p.1).RaiseOK P ↔ _
  rw [raiseOK_app]
  constructor
  · rintro ⟨-, hp, h, -⟩; exact ⟨h rfl, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨.inl rfl, hp, fun _ => h, fun h' => by cases h'⟩

/-- **A raise of a nonzero name is at `P`** exactly when the name is in `P` and its argument is at
`P`. -/
theorem raiseOK_raise_payload {n i : UInt32} {v : Val} (hn : n ≠ 0) :
    (raiseE (.val (opPayload n i v))).RaiseOK P ↔ P n ∧ v.1.RaiseOK P := by
  rw [raiseOK_raiseE, raiseOK_opPayload, opPayload_val]
  constructor
  · rintro ⟨⟨m, r, h, hm⟩, hv⟩
    simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rcases hm with hm | ⟨rfl, -⟩
    · exact ⟨hm, hv⟩
    · exact absurd rfl hn
  · rintro ⟨hn', hv⟩
    exact ⟨⟨n, _, rfl, .inl hn'⟩, hv⟩

theorem raiseOK_errVal {err : Option Val} :
    (errVal err).1.RaiseOK P ↔ ∀ E, err = some E → E.1.RaiseOK P := by
  cases err with
  | none =>
      simp only [errVal, Val.inj₁, Val.unit, Expr.RaiseOK, true_iff]
      intro E h; cases h
  | some E =>
      simp only [errVal, Val.inj₂, Expr.RaiseOK, Option.some.injEq]
      exact ⟨fun h E' hE => hE ▸ h, fun h => h E rfl⟩

/-- **A cancel's state past its name is the shape** exactly when it keeps nothing or a raise of a
name in `P`. -/
theorem cancelShape_errVal {err : Option Val} :
    CancelShape P (.pair (.prim (.lit (.i32 0))) (errVal err).1) ↔
      (err = none ∨ ∃ m j w, err = some (opPayload m j w) ∧ P m) := by
  cases err with
  | none =>
      simp only [errVal, Val.inj₁, Val.unit, true_or, iff_true]
      exact .inl rfl
  | some E =>
      simp only [errVal, Val.inj₂, reduceCtorEq, false_or, Option.some.injEq]
      constructor
      · rintro (h | ⟨m, j, y, h, hm⟩)
        · simp at h
        · simp only [Expr.pair.injEq, Expr.inj₂.injEq, true_and] at h
          have hy : IsVal y := by
            have hE := E.2
            rw [h] at hE
            cases hE with
            | pair _ h₂ => cases h₂ with
              | pair _ h₃ => exact h₃
          refine ⟨m, j, ⟨y, hy⟩, Subtype.ext h, hm⟩
      · rintro ⟨m, j, w, rfl, hm⟩
        exact .inr ⟨m, j, w.1, rfl, hm⟩

/-- **A kept error is at `P`** exactly when its cancel's state is the shape and at `P`. -/
theorem errOK_iff {err : Option Val} : ErrOK P err ↔
    CancelShape P (.pair (.prim (.lit (.i32 0))) (errVal err).1) ∧ (errVal err).1.RaiseOK P := by
  rw [cancelShape_errVal, raiseOK_errVal]
  cases err with
  | none => simp [ErrOK]
  | some E =>
      simp only [ErrOK, reduceCtorEq, false_or, Option.some.injEq]
      constructor
      · rintro ⟨m, j, w, rfl, hm, hw⟩
        exact ⟨⟨m, j, w, rfl, hm⟩, fun E' hE => hE ▸ raiseOK_opPayload.2 hw⟩
      · rintro ⟨⟨m, j, w, rfl, hm⟩, h⟩
        exact ⟨m, j, w, rfl, hm, raiseOK_opPayload.1 (h _ rfl)⟩

theorem cancelVal_val (err : Option Val) :
    (cancelVal err).1 = .pair (.prim (.lit (.i32 0)))
      (.pair (.prim (.lit (.i32 0))) (errVal err).1) := rfl

/-- **A cancel is at `P`**, its name `0` not one of `P`'s, exactly when the error it keeps is. -/
theorem raiseOK_raise_cancel (hP0 : ¬ P 0) {err : Option Val} :
    (raiseE (.val (cancelVal err))).RaiseOK P ↔ ErrOK P err := by
  rw [raiseOK_raiseE, errOK_iff, cancelVal_val, raiseOK_pairLit, raiseOK_pairLit]
  constructor
  · rintro ⟨⟨m, r, h, hm⟩, hv⟩
    simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hm with hm | ⟨-, hr⟩
    · exact absurd hm hP0
    · exact ⟨hr, hv⟩
  · rintro ⟨hr, hv⟩
    exact ⟨⟨0, _, rfl, .inr ⟨rfl, hr⟩⟩, hv⟩

/-- A cancel that keeps nothing is at every `P`. -/
theorem raiseOK_raise_cancel_none : (raiseE (.val (cancelVal none))).RaiseOK P := by
  rw [raiseOK_raiseE, cancelVal_val, raiseOK_pairLit, raiseOK_pairLit]
  exact ⟨⟨0, _, rfl, .inr ⟨rfl, .inl rfl⟩⟩, trivial⟩

/-- **A running finaliser's `cfin` frame is at `P`** exactly when the error its cancel keeps is and
the finaliser is. -/
theorem raiseOK_cfinE {err : Option Val} {e : Expr} :
    (cfinE (cancelVal err) e).RaiseOK P ↔ ErrOK P err ∧ e.RaiseOK P := by
  show (Expr.app (.app (.prim .cfin) (cancelVal err).1) e).RaiseOK P ↔ _
  rw [raiseOK_app_of_ne (f := .app (.prim .cfin) (cancelVal err).1) (a := e)
    (fun h => (nomatch h)) (fun h => (nomatch h)), raiseOK_app, errOK_iff,
    cancelVal_val, raiseOK_pairLit, raiseOK_pairLit]
  constructor
  · rintro ⟨⟨-, hv, -, h⟩, he⟩
    obtain ⟨r, hr, hs⟩ := h rfl
    simp only [Expr.pair.injEq, true_and] at hr
    subst hr
    exact ⟨⟨hs, hv⟩, he⟩
  · rintro ⟨⟨hs, hv⟩, he⟩
    exact ⟨⟨.inr (.inl rfl), hv, fun h => (nomatch h), fun _ => ⟨_, rfl, hs⟩⟩, he⟩

/-- A `cfin` frame at `P` holds a cancel's state that keeps nothing or a raise of a name in `P`. -/
theorem cfinFrame_named {err : Option Val}
    (h : (Expr.app (.prim .cfin) (cancelVal err).1).RaiseOK P) :
    err = none ∨ ∃ m j w, err = some (opPayload m j w) ∧ P m := by
  obtain ⟨-, -, -, h⟩ := h
  obtain ⟨r, hr, hs⟩ := h rfl
  rw [cancelVal_val] at hr
  simp only [Expr.pair.injEq, true_and] at hr
  subst hr
  exact cancelShape_errVal.1 hs

/-! ### Shifting and substitution -/

theorem shift_eq_prim {d c : ℕ} {p : Prim} : ∀ {e : Expr}, e.shift d c = .prim p → e = .prim p
  | .var i, h => by simp only [Expr.shift] at h; split at h <;> cases h
  | .prim _, h => h
  | .unit, h | .pair _ _, h | .inj₁ _, h | .inj₂ _, h | .lam _, h | .loc _, h | .seq _ _, h
  | .letpair _ _, h | .case _ _ _, h | .app _ _, h => by simp [Expr.shift] at h

theorem subst_eq_prim {j : ℕ} {s : Val} {p : Prim} :
    ∀ {e : Expr}, e.subst j s = .prim p → e = .prim p ∨ s.1 = .prim p
  | .var i, h => by
      simp only [Expr.subst] at h
      split at h
      · exact .inr h
      · split at h <;> cases h
  | .prim _, h => .inl h
  | .unit, h | .pair _ _, h | .inj₁ _, h | .inj₂ _, h | .lam _, h | .loc _, h | .seq _ _, h
  | .letpair _ _, h | .case _ _ _, h | .app _ _, h => by simp [Expr.subst] at h

theorem cancelShape_shift {r : Expr} (h : CancelShape P r) (d c : ℕ) :
    CancelShape P (r.shift d c) := by
  rcases h with rfl | ⟨m, j, y, rfl, hm⟩
  · exact .inl (by simp [Expr.shift])
  · exact .inr ⟨m, j, y.shift d c, by simp [Expr.shift], hm⟩

theorem cancelShape_subst {r : Expr} (h : CancelShape P r) (j : ℕ) (s : Val) :
    CancelShape P (r.subst j s) := by
  rcases h with rfl | ⟨m, i, y, rfl, hm⟩
  · exact .inl (by simp [Expr.subst])
  · exact .inr ⟨m, i, y.subst j s, by simp [Expr.subst], hm⟩

theorem appOK_shift {f a : Expr} (h : AppOK P f a) (d c : ℕ) :
    AppOK P (f.shift d c) (a.shift d c) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨m, r, rfl, hm⟩ := h.1 (shift_eq_prim hf)
    refine ⟨m, r.shift d c, by simp [Expr.shift], ?_⟩
    rcases hm with hm | ⟨rfl, hr⟩
    · exact .inl hm
    · exact .inr ⟨rfl, cancelShape_shift hr d c⟩
  · obtain ⟨r, rfl, hr⟩ := h.2 (shift_eq_prim hf)
    exact ⟨r.shift d c, by simp [Expr.shift], cancelShape_shift hr d c⟩

theorem appOK_subst {f a : Expr} (h : AppOK P f a) (j : ℕ) {s : Val} (hs : s.1.RaiseOK P) :
    AppOK P (f.subst j s) (a.subst j s) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · rcases subst_eq_prim hf with hf | hs'
    · obtain ⟨m, r, rfl, hm⟩ := h.1 hf
      refine ⟨m, r.subst j s, by simp [Expr.subst], ?_⟩
      rcases hm with hm | ⟨rfl, hr⟩
      · exact .inl hm
      · exact .inr ⟨rfl, cancelShape_subst hr j s⟩
    · rw [hs'] at hs; exact absurd hs not_raiseOK_raise
  · rcases subst_eq_prim hf with hf | hs'
    · obtain ⟨r, rfl, hr⟩ := h.2 hf
      exact ⟨r.subst j s, by simp [Expr.subst], cancelShape_subst hr j s⟩
    · rw [hs'] at hs; exact absurd hs not_raiseOK_cfin

theorem raiseOK_shift (d : ℕ) : ∀ (e : Expr) (c : ℕ), e.RaiseOK P → (e.shift d c).RaiseOK P := by
  intro e
  induction e with
  | var i => intro c _; simp only [Expr.shift]; split <;> trivial
  | unit => intro c h; exact h
  | loc ℓ => intro c h; exact h
  | prim p => intro c h; exact h
  | pair a b iha ihb => intro c h; exact ⟨iha c h.1, ihb c h.2⟩
  | inj₁ a ih => intro c h; exact ih c h
  | inj₂ a ih => intro c h; exact ih c h
  | lam a ih => intro c h; exact ih (c + 1) h
  | seq a b iha ihb => intro c h; exact ⟨iha c h.1, ihb c h.2⟩
  | letpair a b iha ihb => intro c h; exact ⟨iha c h.1, ihb (c + 2) h.2⟩
  | case a b e iha ihb ihe => intro c h; exact ⟨iha c h.1, ihb (c + 1) h.2.1, ihe (c + 1) h.2.2⟩
  | app f a ihf iha =>
      intro c h
      obtain ⟨hf, ha, hok⟩ := h
      refine ⟨?_, iha c ha, appOK_shift hok d c⟩
      rcases hf with rfl | rfl | hf
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (ihf c hf))

theorem raiseOK_val_shift {v : Val} (h : v.1.RaiseOK P) (d c : ℕ) : (v.shift d c).1.RaiseOK P :=
  raiseOK_shift d v.1 c h

theorem raiseOK_subst : ∀ (e : Expr) (j : ℕ) (s : Val), e.RaiseOK P → s.1.RaiseOK P →
    (e.subst j s).RaiseOK P := by
  intro e
  induction e with
  | var i =>
      intro j s _ hs
      simp only [Expr.subst]
      split
      · exact hs
      · split <;> trivial
  | unit => intro j s h _; exact h
  | loc ℓ => intro j s h _; exact h
  | prim p => intro j s h _; exact h
  | pair a b iha ihb => intro j s h hs; exact ⟨iha j s h.1 hs, ihb j s h.2 hs⟩
  | inj₁ a ih => intro j s h hs; exact ih j s h hs
  | inj₂ a ih => intro j s h hs; exact ih j s h hs
  | lam a ih => intro j s h hs; exact ih (j + 1) _ h (raiseOK_val_shift hs 1 0)
  | seq a b iha ihb => intro j s h hs; exact ⟨iha j s h.1 hs, ihb j s h.2 hs⟩
  | letpair a b iha ihb =>
      intro j s h hs; exact ⟨iha j s h.1 hs, ihb (j + 2) _ h.2 (raiseOK_val_shift hs 2 0)⟩
  | case a b e iha ihb ihe =>
      intro j s h hs
      exact ⟨iha j s h.1 hs, ihb (j + 1) _ h.2.1 (raiseOK_val_shift hs 1 0),
        ihe (j + 1) _ h.2.2 (raiseOK_val_shift hs 1 0)⟩
  | app f a ihf iha =>
      intro j s h hs
      obtain ⟨hf, ha, hok⟩ := h
      refine ⟨?_, iha j s ha hs, appOK_subst hok j hs⟩
      rcases hf with rfl | rfl | hf
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (ihf j s hf hs))

/-! ### Contexts -/

/-- A context around a term is a primitive only as the hole around that primitive. -/
theorem plug_eq_prim {K : Kont} {e : Expr} {p : Prim} (h : K.plug e = .prim p) :
    K = .hole ∧ e = .prim p := by
  cases K <;> simp_all [Kont.plug]

/-- Shifting a context around a term shifts the context and the term. -/
theorem _root_.BoCa.BoLo.Kont.plug_shift (d : ℕ) (K : Kont) : ∀ (c : ℕ) (x : Expr),
    (K.plug x).shift d c = (K.shift d c).plug (x.shift d c) := by
  induction K with
  | hole => intro c x; rfl
  | pairL K e ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | pairR v K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih, Val.val_shift]
  | letpair K e ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | case K e₁ e₂ ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | appR f K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | appL K v ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih, Val.val_shift]
  | seq K e ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | inj₁ K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]
  | inj₂ K ih => intro c x; simp only [Kont.plug, Kont.shift, Expr.shift, ih]

theorem plain_var (i : ℕ) : Plain (.var i) := trivial

theorem plug_ne_prim_of_plain {a : Expr} (ha : Plain a) {p : Prim} :
    ∀ {K : Kont}, K.plug a ≠ .prim p
  | .hole, h => by cases a <;> simp_all [Plain, Kont.plug]
  | .pairL _ _, h | .pairR _ _, h | .letpair _ _, h | .case _ _ _, h | .appR _ _, h
  | .appL _ _, h | .seq _ _, h | .inj₁ _, h | .inj₂ _, h => by simp [Kont.plug] at h

/-- A literal-named pair, read through a context at a plain term: `K = (lit m, K')`. -/
theorem plug_eq_pairLit {a : Expr} (ha : Plain a) {m : UInt32} {r : Expr} :
    ∀ {K : Kont}, K.plug a = .pair (.prim (.lit (.i32 m))) r →
      ∃ (v : Val) (K' : Kont), K = .pairR v K' ∧ v.1 = .prim (.lit (.i32 m)) ∧ r = K'.plug a
  | .hole, h => by cases a <;> simp_all [Plain, Kont.plug]
  | .pairL K' e, h => by
      simp only [Kont.plug, Expr.pair.injEq] at h
      exact absurd h.1 (plug_ne_prim_of_plain ha)
  | .pairR v K', h => by
      simp only [Kont.plug, Expr.pair.injEq] at h
      exact ⟨v, K', rfl, h.1, h.2.symm⟩
  | .letpair _ _, h | .case _ _ _, h | .appR _ _, h | .appL _ _, h | .seq _ _, h | .inj₁ _, h
  | .inj₂ _, h => by simp [Kont.plug] at h

theorem plug_eq_inj₂ {a : Expr} (ha : Plain a) {x : Expr} :
    ∀ {K : Kont}, K.plug a = .inj₂ x → ∃ K', K = .inj₂ K' ∧ x = K'.plug a
  | .hole, h => by cases a <;> simp_all [Plain, Kont.plug]
  | .inj₂ K', h => by simp only [Kont.plug, Expr.inj₂.injEq] at h; exact ⟨K', rfl, h.symm⟩
  | .pairL _ _, h | .pairR _ _, h | .letpair _ _, h | .case _ _ _, h | .appR _ _, h
  | .appL _ _, h | .seq _ _, h | .inj₁ _, h => by simp [Kont.plug] at h

theorem plug_ne_inj₁_unit {a : Expr} (ha : Plain a) : ∀ {K : Kont}, K.plug a ≠ .inj₁ .unit
  | .hole, h => by cases a <;> simp_all [Plain, Kont.plug]
  | .inj₁ K', h => by
      simp only [Kont.plug, Expr.inj₁.injEq] at h
      cases K' with
      | hole => cases a <;> simp_all [Plain, Kont.plug]
      | _ => simp [Kont.plug] at h
  | .pairL _ _, h | .pairR _ _, h | .letpair _ _, h | .case _ _ _, h | .appR _ _, h
  | .appL _ _, h | .seq _ _, h | .inj₂ _, h => by simp [Kont.plug] at h

/-- **A cancel's state, read through a context at a plain term**: the context's hole is in the kept
raise's argument, so every term plugged there gives the shape. -/
theorem cancelShape_plug {a : Expr} (ha : Plain a) {K : Kont} (h : CancelShape P (K.plug a))
    (b : Expr) : CancelShape P (K.plug b) := by
  rcases h with h | ⟨m, j, y, h, hm⟩
  · obtain ⟨v, K₁, rfl, hv, h₁⟩ := plug_eq_pairLit ha h
    exact absurd h₁.symm (plug_ne_inj₁_unit ha)
  · obtain ⟨v, K₁, rfl, hv, h₁⟩ := plug_eq_pairLit ha h
    obtain ⟨K₂, rfl, h₂⟩ := plug_eq_inj₂ ha h₁.symm
    obtain ⟨v₂, K₃, rfl, hv₂, h₃⟩ := plug_eq_pairLit ha h₂.symm
    obtain ⟨v₃, K₄, rfl, hv₃, rfl⟩ := plug_eq_pairLit ha h₃.symm
    refine .inr ⟨m, j, K₄.plug b, ?_, hm⟩
    simp only [Kont.plug, Expr.val, hv, hv₂, hv₃]

/-- **What an application asks of its argument, read through a context at a plain term**. -/
theorem appOK_plug {a : Expr} (ha : Plain a) {f : Expr} {K : Kont} (h : AppOK P f (K.plug a))
    (b : Expr) : AppOK P f (K.plug b) := by
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨m, r, hr, hm⟩ := h.1 hf
    obtain ⟨v, K', rfl, hv, rfl⟩ := plug_eq_pairLit ha hr
    refine ⟨m, K'.plug b, by simp [Kont.plug, Expr.val, hv], ?_⟩
    rcases hm with hm | ⟨rfl, hs⟩
    · exact .inl hm
    · exact .inr ⟨rfl, cancelShape_plug ha hs b⟩
  · obtain ⟨r, hr, hs⟩ := h.2 hf
    obtain ⟨v, K', rfl, hv, rfl⟩ := plug_eq_pairLit ha hr
    exact ⟨K'.plug b, by simp [Kont.plug, Expr.val, hv], cancelShape_plug ha hs b⟩

/-- **A context at the names `P` around a term at `P` is at `P`.** -/
theorem plug_raiseOK : ∀ (K : Kont) {a : Expr}, KRaiseOK P K → a.RaiseOK P →
    (K.plug a).RaiseOK P := by
  intro K
  induction K with
  | hole => intro a _ h; exact h
  | pairL K e ih =>
      intro a hK h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | pairR v K ih =>
      intro a hK h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at hK ⊢; exact ⟨hK.1, ih hK.2 h⟩
  | letpair K e ih =>
      intro a hK h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | case K e₁ e₂ ih =>
      intro a hK h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | seq K e ih =>
      intro a hK h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at hK ⊢; exact ⟨ih hK.1 h, hK.2⟩
  | inj₁ K ih => intro a hK h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at hK ⊢; exact ih hK h
  | inj₂ K ih => intro a hK h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at hK ⊢; exact ih hK h
  | appR f K ih =>
      intro a hK h
      simp only [KRaiseOK, Kont.plug] at hK ⊢
      obtain ⟨hf, hK, hok⟩ := hK
      exact ⟨hf, ih hK h, appOK_plug (plain_var 0) hok a⟩
  | appL K v ih =>
      intro a hK h
      simp only [KRaiseOK, Kont.plug] at hK ⊢
      obtain ⟨hf, hv, -⟩ := hK
      have hK : (K.plug (.var 0)).RaiseOK P := by
        rcases hf with hf | hf | hf
        · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
        · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
        · exact hf
      have hKa := ih hK h
      refine ⟨.inr (.inr hKa), hv, fun he => ?_, fun he => ?_⟩
      · obtain ⟨rfl, rfl⟩ := plug_eq_prim he
        exact absurd hKa not_raiseOK_raise
      · obtain ⟨rfl, rfl⟩ := plug_eq_prim he
        exact absurd hKa not_raiseOK_cfin

/-- **A term at `P` holds its context and a plain term it plugs at `P`.** -/
theorem plug_raiseOK_inv : ∀ (K : Kont) {a : Expr}, Plain a → (K.plug a).RaiseOK P →
    KRaiseOK P K ∧ a.RaiseOK P := by
  intro K
  induction K with
  | hole => intro a _ h; exact ⟨trivial, h⟩
  | pairL K e ih =>
      intro a ha h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | pairR v K ih =>
      intro a ha h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h ⊢
      exact ⟨⟨h.1, (ih ha h.2).1⟩, (ih ha h.2).2⟩
  | letpair K e ih =>
      intro a ha h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | case K e₁ e₂ ih =>
      intro a ha h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | seq K e ih =>
      intro a ha h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h ⊢
      exact ⟨⟨(ih ha h.1).1, h.2⟩, (ih ha h.1).2⟩
  | inj₁ K ih => intro a ha h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h ⊢; exact ih ha h
  | inj₂ K ih => intro a ha h; simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h ⊢; exact ih ha h
  | appR f K ih =>
      intro a ha h
      simp only [KRaiseOK, Kont.plug] at h ⊢
      obtain ⟨hf, hK, hok⟩ := h
      exact ⟨⟨hf, (ih ha hK).1, appOK_plug ha hok _⟩, (ih ha hK).2⟩
  | appL K v ih =>
      intro a ha h
      simp only [KRaiseOK, Kont.plug] at h ⊢
      obtain ⟨hf, hv, -⟩ := h
      have hK : (K.plug a).RaiseOK P := by
        rcases hf with hf | hf | hf
        · exact absurd hf (plug_ne_prim_of_plain ha)
        · exact absurd hf (plug_ne_prim_of_plain ha)
        · exact hf
      exact ⟨⟨.inr (.inr (ih ha hK).1), hv,
        fun he => absurd he (plug_ne_prim_of_plain (plain_var 0)),
        fun he => absurd he (plug_ne_prim_of_plain (plain_var 0))⟩, (ih ha hK).2⟩

theorem kraiseOK_hole : KRaiseOK P .hole := trivial

/-! ### Memories -/

theorem heapRaiseOK_upd {μ : Heap} (hμ : HeapRaiseOK P μ) (ℓ : Loc) {v : Val} (hv : v.1.RaiseOK P) :
    HeapRaiseOK P (μ.upd ℓ v) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h; subst h; exact hv
  · rw [Heap.upd_other hk] at h; exact hμ k w h

theorem heapRaiseOK_del {μ : Heap} (hμ : HeapRaiseOK P μ) (ℓ : Loc) : HeapRaiseOK P (μ.del ℓ) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h
  · rw [Heap.del_other hk] at h; exact hμ k w h

theorem heapRaiseOK_fill {μ : Heap} (hμ : HeapRaiseOK P μ) (ℓ : Loc) (n : ℕ) {v : Val}
    (hv : v.1.RaiseOK P) : HeapRaiseOK P (μ.fill ℓ n v) := by
  intro k w h
  simp only [Heap.fill] at h
  split at h
  · cases h; exact hv
  · exact hμ k w h

theorem heapRaiseOK_empty : HeapRaiseOK P Adequacy.emptyMem := fun _ _ h => by
  simp [Adequacy.emptyMem] at h

/-! ### Contexts shifted, and cancelled -/

theorem kraiseOK_shift {K : Kont} (hK : KRaiseOK P K) (d : ℕ) : KRaiseOK P (K.shift d 0) := by
  have h := raiseOK_shift d _ 0 hK
  rw [Kont.plug_shift] at h
  simp only [Expr.shift, Nat.not_lt_zero, if_false, zero_add] at h
  exact (plug_raiseOK_inv _ (plain_var d) h).1

/-- A cancel's state through a dead region: the hole stays in the kept raise's argument. -/
theorem cancelShape_dead {K : Kont} (h : CancelShape P (K.plug (.var 0))) :
    CancelShape P (K.dead.plug (.var 0)) := by
  have ha : Plain (.var 0) := plain_var 0
  rcases h with h | ⟨m, j, y, h, hm⟩
  · obtain ⟨v, K₁, rfl, hv, h₁⟩ := plug_eq_pairLit ha h
    exact absurd h₁.symm (plug_ne_inj₁_unit ha)
  · obtain ⟨v, K₁, rfl, hv, h₁⟩ := plug_eq_pairLit ha h
    obtain ⟨K₂, rfl, h₂⟩ := plug_eq_inj₂ ha h₁.symm
    obtain ⟨v₂, K₃, rfl, hv₂, h₃⟩ := plug_eq_pairLit ha h₂.symm
    obtain ⟨v₃, K₄, rfl, hv₃, rfl⟩ := plug_eq_pairLit ha h₃.symm
    refine .inr ⟨m, j, K₄.dead.plug (.var 0), ?_, hm⟩
    simp only [Kont.dead, Kont.plug, Expr.val, hv, hv₂, hv₃]

theorem appOK_dead {f : Expr} {K : Kont} (h : AppOK P f (K.plug (.var 0))) :
    AppOK P f (K.dead.plug (.var 0)) := by
  have ha : Plain (.var 0) := plain_var 0
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨m, r, hr, hm⟩ := h.1 hf
    obtain ⟨v, K', rfl, hv, rfl⟩ := plug_eq_pairLit ha hr
    refine ⟨m, K'.dead.plug (.var 0), by simp [Kont.dead, Kont.plug, Expr.val, hv], ?_⟩
    rcases hm with hm | ⟨rfl, hs⟩
    · exact .inl hm
    · exact .inr ⟨rfl, cancelShape_dead hs⟩
  · obtain ⟨r, hr, hs⟩ := h.2 hf
    obtain ⟨v, K', rfl, hv, rfl⟩ := plug_eq_pairLit ha hr
    exact ⟨K'.dead.plug (.var 0), by simp [Kont.dead, Kont.plug, Expr.val, hv], cancelShape_dead hs⟩

/-- **A dead region keeps a part of the region's frames**, at the names `P` when the region's
are. -/
theorem kraiseOK_dead : ∀ {K : Kont}, KRaiseOK P K → KRaiseOK P K.dead
  | .hole, h => h
  | .pairL K e, h => by
      simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h
      simp only [KRaiseOK, Kont.dead, Kont.plug, Expr.RaiseOK]; exact ⟨kraiseOK_dead h.1, h.2⟩
  | .pairR v K, h => by
      simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h
      simp only [KRaiseOK, Kont.dead, Kont.plug, Expr.RaiseOK]; exact ⟨h.1, kraiseOK_dead h.2⟩
  | .letpair K e, h => by
      simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h
      simp only [KRaiseOK, Kont.dead, Kont.plug, Expr.RaiseOK]; exact ⟨kraiseOK_dead h.1, h.2⟩
  | .case K e₁ e₂, h => by
      simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h
      simp only [KRaiseOK, Kont.dead, Kont.plug, Expr.RaiseOK]; exact ⟨kraiseOK_dead h.1, h.2⟩
  | .seq K e, h => by
      simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h
      simp only [KRaiseOK, Kont.dead, Kont.plug, Expr.RaiseOK]; exact ⟨kraiseOK_dead h.1, h.2⟩
  | .inj₁ K, h => by
      simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h
      simp only [KRaiseOK, Kont.dead, Kont.plug, Expr.RaiseOK]; exact kraiseOK_dead h
  | .inj₂ K, h => by
      simp only [KRaiseOK, Kont.plug, Expr.RaiseOK] at h
      simp only [KRaiseOK, Kont.dead, Kont.plug, Expr.RaiseOK]; exact kraiseOK_dead h
  | .appL K v, h => by
      simp only [KRaiseOK, Kont.plug] at h
      obtain ⟨hf, hv, -⟩ := h
      have hK : KRaiseOK P K := by
        rcases hf with hf | hf | hf
        · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
        · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
        · exact hf
      simp only [KRaiseOK, Kont.dead, Kont.plug]
      exact ⟨.inr (.inr (kraiseOK_dead hK)), hv,
        fun he => absurd he (plug_ne_prim_of_plain (plain_var 0)),
        fun he => absurd he (plug_ne_prim_of_plain (plain_var 0))⟩
  | .appR f K, h => by
      have h' := h
      simp only [KRaiseOK, Kont.plug] at h'
      obtain ⟨hf, hK, hok⟩ := h'
      simp only [Kont.dead]
      split
      · exact kraiseOK_dead hK
      · exact ⟨hf, kraiseOK_dead hK, appOK_dead hok⟩

/-! ### The terms a head step builds -/

theorem raiseOK_hndE {H : Val} {e : Expr} : (hndE H e).RaiseOK P ↔ H.1.RaiseOK P ∧ e.RaiseOK P := by
  show (Expr.app (.app (.prim .hnd) H.1) e).RaiseOK P ↔ _
  rw [raiseOK_app_of_ne (f := .app (.prim .hnd) H.1) (a := e) (fun h => (nomatch h))
    (fun h => (nomatch h)), raiseOK_primApp (by decide) (by decide)]

theorem raiseOK_ubindE {ND : Val} {e : Expr} :
    (ubindE ND e).RaiseOK P ↔ ND.1.RaiseOK P ∧ e.RaiseOK P := by
  show (Expr.app (.app (.prim .ubind) ND.1) e).RaiseOK P ↔ _
  rw [raiseOK_app_of_ne (f := .app (.prim .ubind) ND.1) (a := e) (fun h => (nomatch h))
    (fun h => (nomatch h)), raiseOK_primApp (by decide) (by decide)]

theorem raiseOK_ccatchE {e : Expr} : (ccatchE e).RaiseOK P ↔ e.RaiseOK P :=
  raiseOK_primApp (by decide) (by decide) e

theorem raiseOK_freeE {e : Expr} : (freeE e).RaiseOK P ↔ e.RaiseOK P :=
  raiseOK_primApp (by decide) (by decide) e

theorem raiseOK_performE {p : Val} : (performE (.val p)).RaiseOK P ↔ p.1.RaiseOK P :=
  raiseOK_primApp (by decide) (by decide) p.1

theorem raiseOK_stuckE : stuckE.RaiseOK P :=
  (raiseOK_app_of_ne (f := .unit) (a := .unit) (fun h => (nomatch h)) (fun h => (nomatch h))).2
    ⟨trivial, trivial⟩

theorem raiseOK_hndVal {n : UInt32} {qs hr hs : Val} :
    (hndVal n qs hr hs).1.RaiseOK P ↔ qs.1.RaiseOK P ∧ hr.1.RaiseOK P ∧ hs.1.RaiseOK P := by
  show (Expr.pair (.prim (.lit (.i32 n))) (.pair qs.1 (.pair hr.1 hs.1))).RaiseOK P ↔ _
  rw [raiseOK_pairLit]
  exact Iff.rfl

/-- κ at an unrestricted operation, at a handler and a context at `P`. -/
theorem raiseOK_kappa {H : Val} {K : Kont} (hH : H.1.RaiseOK P) (hK : KRaiseOK P K) :
    (kappa H K).RaiseOK P := by
  simp only [kappa, Expr.val, Val.lam, Expr.RaiseOK]
  refine ⟨trivial, ⟨trivial, ?_⟩, trivial, ?_⟩
  · exact raiseOK_hndE.2 ⟨raiseOK_val_shift hH 3 0, kraiseOK_shift hK 3⟩
  · exact raiseOK_ccatchE.2 (plug_raiseOK _ (kraiseOK_shift (kraiseOK_dead hK) 2)
      raiseOK_raise_cancel_none)

/-- κ at a must-resume or cancellable operation, before its cell, at a handler and a context at `P`. -/
theorem raiseOK_kappaCell {H : Val} {K : Kont} (hasCancel : Bool) (hH : H.1.RaiseOK P)
    (hK : KRaiseOK P K) : (kappaCell hasCancel H K).RaiseOK P := by
  simp only [kappaCell, kappaCBody, Expr.val, Val.lam, Val.prim, Val.unit]
  refine raiseOK_app_val ?_ ((raiseOK_primApp (by decide) (by decide) _).2 trivial)
  simp only [Expr.RaiseOK]
  refine ⟨trivial, ⟨trivial, raiseOK_freeE.2 trivial,
    raiseOK_hndE.2 ⟨raiseOK_val_shift hH 4 0, kraiseOK_shift hK 4⟩⟩, ?_⟩
  cases hasCancel
  · simp only [Bool.false_eq_true, if_false]; exact raiseOK_stuckE
  · simp only [if_true, Expr.RaiseOK]
    exact ⟨trivial, raiseOK_freeE.2 trivial, raiseOK_ccatchE.2 (plug_raiseOK _
      (kraiseOK_shift (kraiseOK_dead hK) 3) raiseOK_raise_cancel_none)⟩

theorem raiseOK_kappaAt {t : UInt32} {H : Val} {K : Kont} (hH : H.1.RaiseOK P) (hK : KRaiseOK P K) :
    (kappaAt t H K).RaiseOK P := by
  unfold kappaAt
  split
  · exact raiseOK_kappaCell false hH hK
  · split
    · exact raiseOK_kappaCell true hH hK
    · exact raiseOK_kappa hH hK

theorem raiseOK_clauseAt : ∀ (e : Expr) (i : ℕ) {c : Val}, clauseAt e i = some c →
    e.RaiseOK P → c.1.RaiseOK P
  | .pair c' _, 0, c, h, he => by
      simp only [clauseAt] at h
      split at h
      · cases h; exact he.1
      · cases h
  | .pair _ r, i + 1, c, h, he => raiseOK_clauseAt r i h he.2
  | .var _, _, _, h, _ | .unit, _, _, h, _ | .inj₁ _, _, _, h, _ | .inj₂ _, _, _, h, _
  | .lam _, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ | .seq _ _, _, _, h, _
  | .letpair _ _, _, _, h, _ | .case _ _ _, _, _, h, _ | .app _ _, _, _, h, _ => by
      simp [clauseAt] at h

theorem raiseOK_opt {o : Option Val} (h : ∀ v, o = some v → v.1.RaiseOK P) :
    (Val.opt o).1.RaiseOK P := by
  cases o with
  | none => exact trivial
  | some v => exact h v rfl

theorem raiseOK_bool (b : Bool) : (Val.bool b).1.RaiseOK P := by
  cases b <;> exact trivial

/-- A host's answer holds no raise. -/
theorem raiseOK_host (H : Host) (op : HostOp) {v r : Val} (h : H.call op v = some r) :
    r.1.RaiseOK P := by
  have hi32 : ∀ n, (Val.i32 n).1.RaiseOK P := fun n => raiseOK_lit _
  have hi64 : ∀ n, (Val.i64 n).1.RaiseOK P := fun n => raiseOK_lit _
  have hu8 : ∀ n, (Val.u8 n).1.RaiseOK P := fun n => raiseOK_lit _
  have hob : ∀ w n, (Val.ofBits w n).1.RaiseOK P := fun w _ => by cases w <;> exact raiseOK_lit _
  cases op with
  | bin w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi64 _
  | div w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h
        exact raiseOK_opt fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h
        exact raiseOK_opt fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi64 _
  | un w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | eqz w =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact raiseOK_bool _
      · obtain ⟨_, -, rfl⟩ := h; exact raiseOK_bool _
  | rel w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact raiseOK_bool _
      · obtain ⟨_, _, -, rfl⟩ := h; exact raiseOK_bool _
  | wrap =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | extend_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend32_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | wrap8 =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hu8 _
  | extend8_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | fbin f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, _, -, rfl⟩ := h; exact hob _ _
  | fun1 f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | frel f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, _, -, rfl⟩ := h; exact raiseOK_bool _
  | convert f i sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | trunc i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h
      exact raiseOK_opt fun v hv => by
        simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hob _ _
  | trunc_sat i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | demote =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob .f32 _
  | promote =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob .f64 _
  | reinterpret_i f =>
      cases f <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> obtain ⟨_, -, rfl⟩ := h
      · exact hi32 _
      · exact hi64 _
  | reinterpret_f f =>
      cases f <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> obtain ⟨_, -, rfl⟩ := h
      · exact hob .f32 _
      · exact hob .f64 _

theorem raiseOK_tabFill {f : Val} (hf : f.1.RaiseOK P) (ℓ : Loc) (n : UInt32) :
    ∀ i k, (tabFill f ℓ n i k).RaiseOK P
  | i, 0 => by
      show (Expr.pair (.loc ℓ) (.prim (.lit (.i32 n)))).RaiseOK P
      exact ⟨trivial, raiseOK_lit _⟩
  | i, k + 1 => by
      simp only [tabFill, Expr.RaiseOK]
      refine ⟨raiseOK_app_val (raiseOK_app_val ?_ ?_) (raiseOK_app_val hf (raiseOK_lit _)),
        raiseOK_tabFill hf ℓ n (i + 1) k⟩
      · exact raiseOK_prim_of (by decide) (by decide)
      · exact trivial

theorem raiseOK_dropFill {f : Val} (hf : f.1.RaiseOK P) (ℓ : Loc) :
    ∀ i k, (dropFill f ℓ i k).RaiseOK P
  | i, 0 => trivial
  | i, k + 1 => by
      simp only [dropFill, Expr.RaiseOK]
      refine ⟨raiseOK_app_val hf (raiseOK_app_val ?_ ?_), raiseOK_dropFill hf ℓ (i + 1) k⟩
      · exact raiseOK_prim_of (by decide) (by decide)
      · exact trivial

theorem raiseOK_arr (ℓ : Loc) (n : UInt32) : (Val.arr ℓ n).1.RaiseOK P :=
  ⟨trivial, raiseOK_lit _⟩

theorem plain_raise (p : Val) : Plain (raiseE (.val p)) := trivial

theorem plain_perform (p : Val) : Plain (performE (.val p)) := trivial

/-- A redex is plain. -/
theorem plain_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') : Plain a := by
  cases h <;> trivial

/-! ### No step leaves the names `P` -/

/-- **No head step leaves the names `P`**, nor stores a term that does, when `0` is not one of
them: a step raises only what it consumed, or the error a cancel keeps.  `[spec §19]` -/
theorem raiseOK_head (hP0 : ¬ P 0) {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a')
    (ha : a.RaiseOK P) (hμ : HeapRaiseOK P μ) : a'.RaiseOK P ∧ HeapRaiseOK P μ' := by
  cases h with
  | beta b v =>
      have := raiseOK_app_inv (f := .lam b) (fun h => (nomatch h)) (fun h => (nomatch h)) ha
      exact ⟨raiseOK_subst b 0 v this.1 this.2, hμ⟩
  | alloc v ℓ hℓ =>
      exact ⟨trivial, heapRaiseOK_upd hμ ℓ ((raiseOK_primApp (by decide) (by decide) _).1 ha)⟩
  | free ℓ v hv => exact ⟨hμ ℓ v hv, heapRaiseOK_del hμ ℓ⟩
  | load ℓ v hv => exact ⟨hμ ℓ v hv, hμ⟩
  | store ℓ v w hw =>
      have := raiseOK_app_inv (f := .app (.prim .store) (.loc ℓ)) (fun h => (nomatch h))
        (fun h => (nomatch h)) ha
      exact ⟨trivial, heapRaiseOK_upd hμ ℓ this.2⟩
  | seq e => exact ⟨ha.2, hμ⟩
  | letpair v₁ v₂ e =>
      have h1 : (Val.pair v₁ v₂).1.RaiseOK P := ha.1
      exact ⟨raiseOK_subst _ 0 v₁ (raiseOK_subst e 0 (v₂.shift 1 0) ha.2
        (raiseOK_val_shift h1.2 1 0)) h1.1, hμ⟩
  | case₁ v e₁ e₂ => exact ⟨raiseOK_subst e₁ 0 v ha.2.1 ha.1, hμ⟩
  | case₂ v e₁ e₂ => exact ⟨raiseOK_subst e₂ 0 v ha.2.2 ha.1, hμ⟩
  | host op v r hr => exact ⟨raiseOK_host ℍ op hr, hμ⟩
  | tab c f ℓ hℓ =>
      have h1 := (raiseOK_primApp (by decide) (by decide) _).1 ha
      exact ⟨raiseOK_tabFill h1.2 ℓ _ _ _, heapRaiseOK_fill hμ ℓ _ trivial⟩
  | idx ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [idxAns]; split
      · exact trivial
      · exact trivial
  | split ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [splitAns]; split
      · exact ⟨raiseOK_arr _ _, raiseOK_arr _ _⟩
      · exact raiseOK_arr _ _
  | drop f ℓ n =>
      have h1 := (raiseOK_primApp (by decide) (by decide) _).1 ha
      exact ⟨raiseOK_dropFill h1.1 ℓ _ _, hμ⟩
  | count f n i s' =>
      have h1 := (raiseOK_primApp (by decide) (by decide) _).1 ha
      have hf : f.1.RaiseOK P := h1.1
      have hs : s'.1.RaiseOK P := h1.2.2.2
      refine ⟨?_, hμ⟩
      simp only [countNext]; split
      · refine (raiseOK_primApp (by decide) (by decide) _).2 ⟨hf, raiseOK_lit _, raiseOK_lit _, ?_⟩
        exact raiseOK_app_val hf ⟨raiseOK_lit _, hs⟩
      · exact hs
  | countTry f n i s' =>
      have h1 := (raiseOK_primApp (by decide) (by decide) _).1 ha
      have hf : f.1.RaiseOK P := h1.1
      have hs : s'.1.RaiseOK P := h1.2.2.2
      refine ⟨?_, hμ⟩
      simp only [countTryNext]; split
      · refine ⟨raiseOK_app_val hf ⟨raiseOK_lit _, hs⟩, ?_, trivial⟩
        exact (raiseOK_primApp (by decide) (by decide) _).2
          ⟨raiseOK_val_shift hf 1 0, raiseOK_lit _, raiseOK_lit _, trivial⟩
      · exact hs
  | boundedFix s' k a =>
      have h1 := (raiseOK_primApp (by decide) (by decide) _).1 ha
      have hs : s'.1.RaiseOK P := h1.1
      have hk : a.1.RaiseOK P := h1.2.2
      refine ⟨raiseOK_app_val hs ⟨?_, hk⟩, hμ⟩
      simp only [fixSelf]; split
      · exact trivial
      · exact (raiseOK_primApp (by decide) (by decide) _).2
          ⟨raiseOK_val_shift hs 1 0, raiseOK_lit _, trivial⟩
  | iterate f s' =>
      have h1 := (raiseOK_primApp (by decide) (by decide) _).1 ha
      have hf : f.1.RaiseOK P := h1.1
      have hs : s'.1.RaiseOK P := h1.2
      have hf3 := raiseOK_val_shift hf 3 0
      have htick : tickE.RaiseOK P :=
        (raiseOK_primApp (by decide) (by decide) _).2 ⟨raiseOK_lit _, raiseOK_lit _, trivial⟩
      refine ⟨⟨raiseOK_app_val (raiseOK_app_val hf hs) trivial, trivial, raiseOK_app_val
        ⟨trivial, (raiseOK_primApp (by decide) (by decide) _).2 ⟨hf3, trivial⟩,
          raiseOK_app_val trivial (raiseOK_app_val (raiseOK_app_val hf3 trivial) trivial)⟩ htick⟩,
        hμ⟩
  | hret n qs hr hs w =>
      obtain ⟨hH, hw⟩ := raiseOK_hndE.1 ha
      exact ⟨raiseOK_app_val (raiseOK_hndVal.1 hH).2.1 hw, hμ⟩
  | hop n i qs hr hs c v K hc hK =>
      obtain ⟨hH, hb⟩ := raiseOK_hndE.1 ha
      obtain ⟨hKr, hp⟩ := plug_raiseOK_inv K (plain_perform _) hb
      have hv := raiseOK_opPayload.1 (raiseOK_performE.1 hp)
      have hc' := raiseOK_clauseAt hs.1 i.toNat hc (raiseOK_hndVal.1 hH).2.2
      exact ⟨raiseOK_app_val hc' ⟨hv, raiseOK_kappaAt hH hKr⟩, hμ⟩
  | hunwind n i qs hr hs c v K hc hK =>
      obtain ⟨hH, hb⟩ := raiseOK_hndE.1 ha
      obtain ⟨-, hp⟩ := plug_raiseOK_inv K (plain_raise _) hb
      have hv := raiseOK_opPayload.1 (raiseOK_raiseE.1 hp).2
      exact ⟨raiseOK_app_val (raiseOK_clauseAt hs.1 i.toNat hc (raiseOK_hndVal.1 hH).2.2) hv, hμ⟩
  | uthen N D w =>
      obtain ⟨hND, hw⟩ := raiseOK_ubindE.1 ha
      exact ⟨raiseOK_app_val hND.1 hw, hμ⟩
  | ufin N D n i v K hn hK =>
      obtain ⟨hND, hb⟩ := raiseOK_ubindE.1 ha
      obtain ⟨-, hp⟩ := plug_raiseOK_inv K (plain_raise _) hb
      exact ⟨⟨raiseOK_app_val hND.2 trivial, hp⟩, hμ⟩
  | ufinC N D err K hK =>
      obtain ⟨hND, hb⟩ := raiseOK_ubindE.1 ha
      obtain ⟨-, hp⟩ := plug_raiseOK_inv K (plain_raise _) hb
      exact ⟨raiseOK_cfinE.2 ⟨(raiseOK_raise_cancel hP0).1 hp, raiseOK_app_val hND.2 trivial⟩, hμ⟩
  | cfret err w =>
      exact ⟨(raiseOK_raise_cancel hP0).2 (raiseOK_cfinE.1 ha).1, hμ⟩
  | cferr err m j w K hm hK =>
      obtain ⟨herr, hb⟩ := raiseOK_cfinE.1 ha
      obtain ⟨-, hp⟩ := plug_raiseOK_inv K (plain_raise _) hb
      obtain ⟨hPm, hw⟩ := (raiseOK_raise_payload hm).1 hp
      refine ⟨(raiseOK_raise_cancel hP0).2 ?_, hμ⟩
      cases err with
      | some E => exact herr
      | none => exact ⟨m, j, w, rfl, hPm, hw⟩
  | cfcancel err err' K hK =>
      obtain ⟨herr, hb⟩ := raiseOK_cfinE.1 ha
      obtain ⟨-, hp⟩ := plug_raiseOK_inv K (plain_raise _) hb
      have herr' := (raiseOK_raise_cancel hP0).1 hp
      refine ⟨(raiseOK_raise_cancel hP0).2 ?_, hμ⟩
      cases err with
      | some E => exact herr
      | none => exact herr'
  | cancel K hK => exact ⟨trivial, hμ⟩
  | creraise E K hK =>
      obtain ⟨-, hp⟩ := plug_raiseOK_inv K (plain_raise _) (raiseOK_ccatchE.1 ha)
      obtain ⟨m, j, w, rfl, hPm, hw⟩ := (raiseOK_raise_cancel hP0).1 hp
      refine ⟨?_, hμ⟩
      by_cases hm0 : m = 0
      · subst hm0; exact absurd hPm hP0
      · exact (raiseOK_raise_payload hm0).2 ⟨hPm, hw⟩

/-- **No step leaves the names `P`**, nor stores a value that does, when `0` is not one of them.
`[spec §19]` -/
theorem raiseOK_step1 (hP0 : ¬ P 0) {μ μ' : Heap} {e e' : Expr} (h : Step1 (ℍ := ℍ) μ e μ' e')
    (he : e.RaiseOK P) (hμ : HeapRaiseOK P μ) : e'.RaiseOK P ∧ HeapRaiseOK P μ' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  obtain ⟨hK, ha⟩ := plug_raiseOK_inv K (plain_head hh) he
  obtain ⟨ha', hμ'⟩ := raiseOK_head hP0 hh ha hμ
  exact ⟨plug_raiseOK K hK ha', hμ'⟩

/-- **No run leaves the names `P`.**  `[spec §19]` -/
theorem raiseOK_steps (hP0 : ¬ P 0) {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e')
    (he : e.RaiseOK P) (hμ : HeapRaiseOK P μ) : e'.RaiseOK P ∧ HeapRaiseOK P μ' := by
  induction h with
  | refl => exact ⟨he, hμ⟩
  | more h₁ _ ih =>
      obtain ⟨he₁, hμ₁⟩ := raiseOK_step1 hP0 h₁ he hμ
      exact ih he₁ hμ₁

/-! ### The running finalisers of a context -/

/-- **Every running finaliser's `cfin` frame of `K` holds a cancel's state that keeps nothing or a
raise of a name in `P`.**  `[spec §19]` -/
def KCfinNamed (P : UInt32 → Prop) : Kont → Prop
  | .hole => True
  | .appR f K => (∀ e, f = .app (.prim .cfin) (cancelVal e).1 →
      e = none ∨ ∃ m j w, e = some (opPayload m j w) ∧ P m) ∧ KCfinNamed P K
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => KCfinNamed P K

/-- A context at the names `P` holds its running finalisers' kept errors at `P`. -/
theorem kcfinNamed_of_kraiseOK : ∀ {K : Kont}, KRaiseOK P K → KCfinNamed P K
  | .hole, _ => trivial
  | .pairL K _, h => kcfinNamed_of_kraiseOK (K := K) h.1
  | .pairR _ K, h => kcfinNamed_of_kraiseOK (K := K) h.2
  | .letpair K _, h => kcfinNamed_of_kraiseOK (K := K) h.1
  | .case K _ _, h => kcfinNamed_of_kraiseOK (K := K) h.1
  | .seq K _, h => kcfinNamed_of_kraiseOK (K := K) h.1
  | .inj₁ K, h => kcfinNamed_of_kraiseOK (K := K) h
  | .inj₂ K, h => kcfinNamed_of_kraiseOK (K := K) h
  | .appL K _, h => by
      obtain ⟨hf, -, -⟩ := h
      rcases hf with hf | hf | hf
      · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
      · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
      · exact kcfinNamed_of_kraiseOK (K := K) hf
  | .appR f K, h => by
      obtain ⟨hf, hK, -⟩ := h
      refine ⟨fun e he => ?_, kcfinNamed_of_kraiseOK hK⟩
      subst he
      rcases hf with hf | hf | hf
      · cases hf
      · cases hf
      · exact cfinFrame_named hf

/-- A shifted kept error keeps the name it had. -/
theorem errVal_shift_named {e : Option Val} {d c : ℕ}
    (h : ∀ E, e = some E → ∃ m j w, (E.shift d c) = opPayload m j w ∧ P m) :
    e = none ∨ ∃ m j w, e = some (opPayload m j w) ∧ P m := by
  cases e with
  | none => exact .inl rfl
  | some E =>
      obtain ⟨m, j, w, hE, hm⟩ := h E rfl
      have hE' := congrArg Subtype.val hE
      rw [Val.val_shift, opPayload_val] at hE'
      obtain ⟨E₀, hE₀⟩ := E
      cases E₀ with
      | pair a b =>
          simp only [Expr.shift, Expr.pair.injEq] at hE'
          obtain ⟨ha, hb⟩ := hE'
          cases a with
          | prim q =>
              simp only [Expr.shift, Expr.prim.injEq] at ha
              subst ha
              cases b with
              | pair b₁ y =>
                  simp only [Expr.shift, Expr.pair.injEq] at hb
                  obtain ⟨hb₁, -⟩ := hb
                  cases b₁ with
                  | prim q' =>
                      simp only [Expr.shift, Expr.prim.injEq] at hb₁
                      subst hb₁
                      have hy : IsVal y := by
                        cases hE₀ with
                        | pair _ h₂ => cases h₂ with
                          | pair _ h₃ => exact h₃
                      exact .inr ⟨m, j, ⟨y, hy⟩, rfl, hm⟩
                  | var i => simp only [Expr.shift] at hb₁; split at hb₁ <;> cases hb₁
                  | _ => simp [Expr.shift] at hb₁
              | var i => simp only [Expr.shift] at hb; split at hb <;> cases hb
              | _ => simp [Expr.shift] at hb
          | var i => simp only [Expr.shift] at ha; split at ha <;> cases ha
          | _ => simp [Expr.shift] at ha
      | var i => simp only [Expr.shift] at hE'; split at hE' <;> cases hE'
      | _ => simp [Expr.shift] at hE'

theorem cancelVal_shift (e : Option Val) (d c : ℕ) :
    (cancelVal e).1.shift d c = (cancelVal (e.map (Val.shift d c))).1 := by
  cases e <;> rfl

/-- **A shift keeps the names a context's running finalisers keep.** -/
theorem kcfinNamed_of_shift {d : ℕ} : ∀ {K : Kont} {c : ℕ}, KCfinNamed P (K.shift d c) →
    KCfinNamed P K
  | .hole, _, _ => trivial
  | .pairL K _, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .pairR _ K, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .letpair K _, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .case K _ _, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .appL K _, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .seq K _, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .inj₁ K, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .inj₂ K, c, h => kcfinNamed_of_shift (K := K) (c := c) h
  | .appR f K, c, h => by
      obtain ⟨hf, hK⟩ := h
      refine ⟨fun e he => ?_, kcfinNamed_of_shift hK⟩
      subst he
      have h₁ := hf (e.map (Val.shift d c)) (by
        show Expr.app ((Expr.prim .cfin).shift d c) ((cancelVal e).1.shift d c) = _
        rw [cancelVal_shift]; rfl)
      refine errVal_shift_named (d := d) (c := c) fun E hE => ?_
      subst hE
      rcases h₁ with h₁ | ⟨m, j, w, hw, hm⟩
      · cases h₁
      · simp only [Option.map_some, Option.some.injEq] at hw
        exact ⟨m, j, w, hw, hm⟩

/-- **κ at an unrestricted operation holds its context in its resume branch**, shifted past the
branch's binders. -/
theorem kraiseOK_of_kappa {H : Val} {K : Kont} (h : (kappa H K).RaiseOK P) :
    KRaiseOK P (K.shift 3 0) := by
  simp only [kappa, Expr.val, Val.lam, Expr.RaiseOK] at h
  exact (raiseOK_hndE.1 h.2.1.2).2

/-- κ at a must-resume or cancellable operation, at its cell, holds its context in its resume branch. -/
theorem kraiseOK_of_kappaC {hasCancel : Bool} {ℓ : Loc} {H : Val} {K : Kont}
    (h : (kappaC hasCancel ℓ H K).RaiseOK P) : KRaiseOK P (K.shift 3 0) := by
  simp only [kappaC, Expr.val, Val.lam, Expr.RaiseOK] at h
  exact (raiseOK_hndE.1 h.2.1.2.2).2

/-- **A cancel at the names `P` keeps its region's running finalisers' errors at `P`**: in a term at
`P` that cancels `κ`, `kappa H K` or `kappaC hasCancel ℓ H K` applied to `inj₂ ()`, every running
finaliser's `cfin` frame of `K` keeps none or a raise of a name in `P`.  `κ`'s resume branch holds
`K` shifted, and a shift keeps the names its running finalisers keep. -/
theorem kcfinNamed_of_cancel {e : Expr} (he : e.RaiseOK P) {K₀ : Kont} {H : Val} {K : Kont}
    (h₀ : e = K₀.plug (.app (kappa H K) (.val (Val.inj₂ .unit))) ∨
      ∃ hasCancel ℓ, e = K₀.plug (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₂ .unit)))) :
    KCfinNamed P K := by
  rcases h₀ with rfl | ⟨hasCancel, ℓ, rfl⟩
  · have hc := (plug_raiseOK_inv K₀ (a := .app (kappa H K) (.val (Val.inj₂ .unit))) trivial he).2
    exact kcfinNamed_of_shift (kcfinNamed_of_kraiseOK (kraiseOK_of_kappa (raiseOK_app_lam_inv hc)))
  · have hc := (plug_raiseOK_inv K₀ (a := .app (kappaC hasCancel ℓ H K) (.val (Val.inj₂ .unit))) trivial
      he).2
    exact kcfinNamed_of_shift (kcfinNamed_of_kraiseOK (kraiseOK_of_kappaC (raiseOK_app_lam_inv hc)))

end Lemmas

/-! ### Raises at the names `q` accepts, decided -/

/-- **Every raise of a term is at the names `q` accepts, and the term holds no `cfin`**, decided:
`raise` occurs only applied to a literal-named payload of a name `q` accepts. -/
def rcE (q : UInt32 → Bool) : Expr → Bool
  | .app (.prim .raise) (.pair (.prim (.lit (.i32 m))) r) => q m && rcE q r
  | .prim p => p != .raise && p != .cfin
  | .var _ | .unit | .loc _ => true
  | .pair a b | .seq a b | .letpair a b | .app a b => rcE q a && rcE q b
  | .inj₁ a | .inj₂ a | .lam a => rcE q a
  | .case a b c => rcE q a && rcE q b && rcE q c

/-- **`rcE` is sound**: a term it accepts is at the names `q` accepts. -/
theorem rcE_sound (q : UInt32 → Bool) (e : Expr) (h : rcE q e = true) :
    e.RaiseOK (fun m => q m = true) := by
  fun_induction rcE q e with
  | case1 m r ih =>
      simp only [Bool.and_eq_true] at h
      exact ⟨.inl rfl, ⟨raiseOK_lit _, ih h.2⟩, fun _ => ⟨m, r, rfl, .inl h.1⟩,
        fun h' => (nomatch h')⟩
  | case2 p =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact h
  | case3 => trivial
  | case4 => trivial
  | case5 => trivial
  | case6 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | case7 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | case8 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | case9 a b hab iha ihb =>
      simp only [Bool.and_eq_true] at h
      have ha := iha h.1
      refine raiseOK_app_val ha (ihb h.2)
  | case10 a iha => exact iha h
  | case11 a iha => exact iha h
  | case12 a iha => exact iha h
  | case13 a b c iha ihb ihc =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1.1, ihb h.1.2, ihc h.2⟩

section Decide
variable {q : UInt32 → Bool}

theorem rcE_app {a b : Expr} (ha : rcE q a = true) : rcE q (.app a b) = rcE q b := by
  rw [rcE.eq_9 q a b (fun m r h₁ _ => by subst h₁; simp [rcE] at ha)]
  simp [ha]

theorem rcE_qualsVal : ∀ qs : List Qual, rcE q (qualsVal qs).1 = true
  | [] => rfl
  | _ :: qs => by
      simp only [qualsVal, Val.pair, Val.i32, rcE, rcE_qualsVal qs, Bool.and_true]
      rfl

theorem rcE_travK : ∀ F : FShape, rcE q (travK F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travK, bindE, rcE, rcE_app, rcE_travK F, rcE_travK G]
  | .sum F G => by
      simp [travK, bindE, rcE, rcE_app, rcE_travK F, rcE_travK G]

theorem rcE_travO : ∀ F : FShape, rcE q (travO F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travO, bindE, rcE, rcE_app, rcE_travO F, rcE_travO G]
  | .sum F G => by
      simp [travO, bindE, rcE, rcE_app, rcE_travO F, rcE_travO G]

theorem rcE_travR : ∀ F : FShape, rcE q (travR F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travR, bindE, rcE, rcE_app, rcE_travR F, rcE_travR G]
  | .sum F G => by
      simp [travR, bindE, rcE, rcE_app, rcE_travR F, rcE_travR G]

theorem rcE_selfV {B : Expr} (hB : rcE q B = true) : rcE q (selfV B).1 = true := by
  simp [selfV, zX, rcE, hB]

theorem rcE_foldImmV (F : FShape) : rcE q (foldImmV F).1 = true := by
  have hB : rcE q (fB F) = true := by simp [fB, bindE, rcE, rcE_app, rcE_travK]
  simp [foldImmV, rcE, rcE_app, rcE_travK, rcE_selfV hB]

theorem rcE_foldOwnV (F : FShape) : rcE q (foldOwnV F).1 = true := by
  have hB : rcE q (fBO F) = true := by simp [fBO, bindE, rcE, rcE_app, rcE_travO]
  simp [foldOwnV, rcE, rcE_app, rcE_selfV hB]

theorem rcE_foldReuseV (F : FShape) : rcE q (foldReuseV F).1 = true := by
  have hB : rcE q (fBR F) = true := by simp [fBR, bindE, rcE, rcE_app, rcE_travR]
  simp [foldReuseV, rcE, rcE_app, rcE_selfV hB]

theorem rcE_tagE : ∀ (k : Nat) {e : Expr}, rcE q e = true → rcE q (FoldP.tagE k e) = true
  | 0, _, h => by simp [FoldP.tagE, rcE, h]
  | k + 1, _, h => by simp [FoldP.tagE, rcE, rcE_tagE k h]

theorem rcE_swap : rcE q swap = true := rfl

theorem rcE_stepV (k : Nat) {t : Val} (ht : rcE q t.1 = true) : rcE q (FoldP.stepV k t).1 = true := by
  simp [FoldP.stepV, FoldP.stepE, bindE, rcE, rcE_app, ht, rcE_swap,
    rcE_tagE k (e := .inj₂ (.pair (.var 8) (.var 0))) (by simp [rcE])]

theorem rcE_arrE (k : Nat) {f : Val} (hf : rcE q f.1 = true) : rcE q (FoldP.arrE k f) = true := by
  simp [FoldP.arrE, bindE, rcE, rcE_app, hf, FoldP.unitF, Val.i32,
    rcE_tagE k (e := .inj₁ .unit) (by simp [rcE])]

theorem rcE_tEG (ks : List FoldP.Bnd) (Bs : FoldP.Stack) :
    ∀ A : VTy, rcE q (FoldP.tE ks Bs A) = true
  | .tvar _ => by simp [FoldP.tE, FoldP.callE, rcE, rcE_tagE _ (e := .var 0) rfl]
  | .tensor A B => by
      simp only [FoldP.tE]; split
      · rfl
      · simp [FoldP.travOf, bindE, rcE, rcE_app, rcE_tEG ks Bs A, rcE_tEG ks Bs B]
  | .sum A B => by
      simp only [FoldP.tE]; split
      · rfl
      · simp [FoldP.travOf, bindE, rcE, rcE_app, rcE_tEG ks Bs A, rcE_tEG ks Bs B]
  | .ref S => by
      simp only [FoldP.tE]; split
      · rfl
      · simp [FoldP.travOf, bindE, rcE, rcE_app, rcE_tEG ks Bs S]
  | .fam (.ref S) => by
      simp only [FoldP.tE]; split
      · rfl
      · exact rcE_arrE _ (rcE_stepV _ (by simp [FoldP.travOf, rcE, rcE_tEG ks Bs S]))
  | .mu B => by
      simp only [FoldP.tE]; split
      · rfl
      · simp [FoldP.callE, rcE, rcE_tagE _ (e := .var 0) rfl]
  | .unit | .zero | .thunk _ | .imm _ _ | .mut _ _ | .box _ _ | .bang _ | .unk | .int _ | .opq _ => rfl
  | .fam .unit | .fam (.tensor _ _) | .fam .zero | .fam (.sum _ _) | .fam (.thunk _)
  | .fam (.imm _ _) | .fam (.mut _ _) | .fam (.box _ _) | .fam (.bang _) | .fam .unk
  | .fam (.tvar _) | .fam (.mu _) | .fam (.int _) | .fam (.fam _) | .fam (.opq _) => rfl

theorem rcE_travB (ks : List FoldP.Bnd) : ∀ k, rcE q (FoldP.travB ks k).1 = true
  | .mu [] => rfl
  | .mu (B :: Bs) => by simp [FoldP.travB, FoldP.trav, FoldP.travOf, rcE, rcE_tEG]
  | .arr _ _ => rfl

theorem rcE_projE : ∀ (n p : Nat) {e : Expr}, rcE q e = true → rcE q (FoldP.projE n p e) = true
  | 0, _, _, h => h
  | 1, _, _, h => h
  | _ + 2, 0, _, h => by simp [FoldP.projE, rcE, h]
  | n + 2, p + 1, _, h => by simp [FoldP.projE, rcE, h, rcE_projE (n + 1) p (e := .var 0) rfl]

theorem rcE_dsp (ks : List FoldP.Bnd) : ∀ (r : List FoldP.Bnd) (j p : Nat), rcE q (FoldP.dsp ks j p r) = true
  | [], _, _ => rfl
  | k :: r, j, p => by
      have hp : rcE q (FoldP.projV ks.length p).1 = true := by
        simp [FoldP.projV, rcE, rcE_projE _ p (e := .var 0) rfl]
      have hb : rcE q (FoldP.branch ks j p k) = true := by
        cases k with
        | arr => simp [FoldP.branch, rcE, rcE_app, hp]
        | mu b => simp [FoldP.branch, bindE, rcE, rcE_app, hp, rcE_travB]
      simp [FoldP.dsp, rcE, hb, rcE_dsp ks r]

theorem rcE_foldOwnGV (B₀ : VTy) : rcE q (FoldP.foldOwnGV B₀).1 = true := by
  have hB : rcE q (FoldP.fBG (FoldP.keys B₀)) = true := by simp [FoldP.fBG, rcE, rcE_dsp]
  simp [FoldP.foldOwnGV, FoldP.selfG, rcE, rcE_app, rcE_selfV hB, FoldP.tagE]

theorem rcE_mapV : ∀ A : VTy, rcE q (mapV A).1 = true
  | .tvar 0 => rfl
  | .tensor A B => by simp [mapV, rcE, rcE_app, rcE_mapV A, rcE_mapV B]
  | .sum A B => by simp [mapV, rcE, rcE_app, rcE_mapV A, rcE_mapV B]
  | .box _ A => rcE_mapV A
  | .tvar (_ + 1) | .unit | .zero | .thunk _ | .ref _ | .imm _ _ | .mut _ _
  | .bang _ | .unk | .mu _ | .int _ | .opq _ | .fam _ => rfl

theorem rcE_nodeV : ∀ C : CTy, rcE q (nodeV C).1 = true
  | .ret A => by simp [nodeV, bindE, rcE, rcE_app, rcE_mapV]
  | .amp C D => by simp [nodeV, rcE, rcE_app, rcE_nodeV C, rcE_nodeV D]
  | .eff _ _ _ _ _ _ C => by simp [nodeV, bindE, rcE, rcE_app, rcE_mapV]
  | .arr _ D => by simp [nodeV, rcE, rcE_app, rcE_nodeV D]
  | .top | .all _ _ _ | .nu _ => rfl

theorem rcE_unfoldV (C : CTy) : rcE q (unfoldV C).1 = true := by
  have hB : rcE q (fBN C) = true := by simp [fBN, rcE, rcE_app, rcE_nodeV]
  simp [unfoldV, rcE, rcE_app, rcE_selfV hB]

theorem rcE_forceE_var (C : CTy) (i : Nat) : rcE q (forceE C (.var i)) = true := by
  cases C <;> rfl

theorem rcE_withPair {M N : Expr} (hM : rcE q M = true) (hN : rcE q N = true) :
    rcE q (withPair M N) = true := by
  simp [withPair, rcE, hM, hN]

theorem rcE_withborUE {d : Expr} (hd : rcE q d = true) : rcE q (withborUE d) = true := by
  simp [withborUE, thenE, rcE, rcE_app, hd]

/-- Filling a variable with a closed λ-value makes no primitive. -/
theorem fill_prim_inv {b : Expr} (hc : closedAt 0 (Val.lam b).1 = true) {j : Nat} {p : Prim} :
    ∀ {x : Expr}, (x.subst j (Val.lam b)).shift 1 j = .prim p → x = .prim p
  | .var i, h => by
      simp only [Expr.subst] at h
      split_ifs at h with h₁ h₂
      · rw [shift_closedAt _ 1 hc (Nat.zero_le _)] at h; cases h
      · simp only [Expr.shift] at h; split_ifs at h
      · simp only [Expr.shift] at h; split_ifs at h
  | .prim _, h => h
  | .unit, h | .pair _ _, h | .inj₁ _, h | .inj₂ _, h | .lam _, h | .loc _, h | .seq _ _, h
  | .letpair _ _, h | .case _ _ _, h | .app _ _, h => by simp [Expr.subst, Expr.shift] at h

/-- Filling a variable with a closed λ-value makes no pair. -/
theorem fill_pair_inv {b : Expr} (hc : closedAt 0 (Val.lam b).1 = true) {j : Nat} {u w : Expr} :
    ∀ {x : Expr}, (x.subst j (Val.lam b)).shift 1 j = .pair u w →
      ∃ x₁ x₂, x = .pair x₁ x₂ ∧ (x₁.subst j (Val.lam b)).shift 1 j = u ∧
        (x₂.subst j (Val.lam b)).shift 1 j = w
  | .var i, h => by
      simp only [Expr.subst] at h
      split_ifs at h with h₁ h₂
      · rw [shift_closedAt _ 1 hc (Nat.zero_le _)] at h; cases h
      · simp only [Expr.shift] at h; split_ifs at h
      · simp only [Expr.shift] at h; split_ifs at h
  | .pair x₁ x₂, h => by
      simp only [Expr.subst, Expr.shift, Expr.pair.injEq] at h
      exact ⟨x₁, x₂, rfl, h.1, h.2⟩
  | .unit, h | .prim _, h | .inj₁ _, h | .inj₂ _, h | .lam _, h | .loc _, h | .seq _ _, h
  | .letpair _ _, h | .case _ _ _, h | .app _ _, h => by simp [Expr.subst, Expr.shift] at h

/-- **Filling a variable with a closed λ-value whose body passes `rcE` leaves `rcE` as it was**:
the λ-value is no primitive and no pair, so no raise is made or unmade. -/
theorem rcE_fill {b : Expr} (hb : rcE q b = true) (hc : closedAt 0 (Val.lam b).1 = true) :
    ∀ (N : Expr) (j : Nat), rcE q ((N.subst j (Val.lam b)).shift 1 j) = rcE q N
  | .var i, j => by
      have hv : rcE q (.var i) = true := rfl
      rw [hv]
      simp only [Expr.subst]
      split_ifs with h₁ h₂
      · rw [shift_closedAt _ 1 hc (Nat.zero_le _)]; exact hb
      · simp only [Expr.shift]; split_ifs <;> rfl
      · simp only [Expr.shift]; split_ifs <;> rfl
  | .unit, _ => rfl
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .pair a c, j => by
      simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j, rcE_fill hb hc c j]
  | .seq a c, j => by
      simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j, rcE_fill hb hc c j]
  | .letpair a c, j => by
      have hs : (Val.lam b).shift 2 0 = Val.lam b := val_shift_closed hc 2 0
      simp only [Expr.subst, Expr.shift, rcE, hs, rcE_fill hb hc a j, rcE_fill hb hc c (j + 2)]
  | .case a c e, j => by
      have hs : (Val.lam b).shift 1 0 = Val.lam b := val_shift_closed hc 1 0
      simp only [Expr.subst, Expr.shift, rcE, hs, rcE_fill hb hc a j, rcE_fill hb hc c (j + 1),
        rcE_fill hb hc e (j + 1)]
  | .inj₁ a, j => by simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j]
  | .inj₂ a, j => by simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j]
  | .lam a, j => by
      have hs : (Val.lam b).shift 1 0 = Val.lam b := val_shift_closed hc 1 0
      simp only [Expr.subst, Expr.shift, rcE, hs, rcE_fill hb hc a (j + 1)]
  | .app a c, j => by
      by_cases hp : ∃ m r, a = .prim .raise ∧ c = .pair (.prim (.lit (.i32 m))) r
      · obtain ⟨m, r, rfl, rfl⟩ := hp
        simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc r j]
      · have hq : ∀ (m : UInt32) (r : Expr), (a.subst j (Val.lam b)).shift 1 j = .prim .raise →
            (c.subst j (Val.lam b)).shift 1 j = .pair (.prim (.lit (.i32 m))) r → False := by
          intro m r ha hc'
          obtain ⟨x₁, x₂, rfl, h₁, -⟩ := fill_pair_inv hc hc'
          exact hp ⟨m, x₂, fill_prim_inv hc ha, by rw [fill_prim_inv hc h₁]⟩
        show rcE q (.app ((a.subst j (Val.lam b)).shift 1 j)
          ((c.subst j (Val.lam b)).shift 1 j)) = _
        rw [rcE.eq_9 q _ _ hq, rcE.eq_9 q a c (fun m r h₁ h₂ => hp ⟨m, r, h₁, h₂⟩),
          rcE_fill hb hc a j, rcE_fill hb hc c j]

theorem shift_prim_inv {d c : Nat} {p : Prim} : ∀ {x : Expr}, x.shift d c = .prim p → x = .prim p
  | .var i, h => by simp only [Expr.shift] at h; split_ifs at h
  | .prim _, h => h
  | .unit, h | .pair _ _, h | .inj₁ _, h | .inj₂ _, h | .lam _, h | .loc _, h | .seq _ _, h
  | .letpair _ _, h | .case _ _ _, h | .app _ _, h => by simp [Expr.shift] at h

theorem shift_pair_inv {d c : Nat} {u w : Expr} : ∀ {x : Expr}, x.shift d c = .pair u w →
    ∃ x₁ x₂, x = .pair x₁ x₂ ∧ x₁.shift d c = u ∧ x₂.shift d c = w
  | .var i, h => by simp only [Expr.shift] at h; split_ifs at h
  | .pair x₁ x₂, h => by
      simp only [Expr.shift, Expr.pair.injEq] at h
      exact ⟨x₁, x₂, rfl, h.1, h.2⟩
  | .unit, h | .prim _, h | .inj₁ _, h | .inj₂ _, h | .lam _, h | .loc _, h | .seq _ _, h
  | .letpair _ _, h | .case _ _ _, h | .app _ _, h => by simp [Expr.shift] at h

/-- **A shift leaves `rcE` as it was**: it makes and unmakes no raise. -/
theorem rcE_shift (d : Nat) : ∀ (N : Expr) (c : Nat), rcE q (N.shift d c) = rcE q N
  | .var i, c => by simp only [Expr.shift]; split_ifs <;> rfl
  | .unit, _ => rfl
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .pair a b, c => by simp only [Expr.shift, rcE, rcE_shift d a c, rcE_shift d b c]
  | .seq a b, c => by simp only [Expr.shift, rcE, rcE_shift d a c, rcE_shift d b c]
  | .letpair a b, c => by simp only [Expr.shift, rcE, rcE_shift d a c, rcE_shift d b (c + 2)]
  | .case a b e, c => by
      simp only [Expr.shift, rcE, rcE_shift d a c, rcE_shift d b (c + 1), rcE_shift d e (c + 1)]
  | .inj₁ a, c => by simp only [Expr.shift, rcE, rcE_shift d a c]
  | .inj₂ a, c => by simp only [Expr.shift, rcE, rcE_shift d a c]
  | .lam a, c => by simp only [Expr.shift, rcE, rcE_shift d a (c + 1)]
  | .app a b, c => by
      by_cases hp : ∃ m r, a = .prim .raise ∧ b = .pair (.prim (.lit (.i32 m))) r
      · obtain ⟨m, r, rfl, rfl⟩ := hp
        simp only [Expr.shift, rcE, rcE_shift d r c]
      · have hq : ∀ (m : UInt32) (r : Expr), a.shift d c = .prim .raise →
            b.shift d c = .pair (.prim (.lit (.i32 m))) r → False := by
          intro m r ha hb
          obtain ⟨x₁, x₂, rfl, h₁, -⟩ := shift_pair_inv hb
          exact hp ⟨m, x₂, shift_prim_inv ha, by rw [shift_prim_inv h₁]⟩
        show rcE q (.app (a.shift d c) (b.shift d c)) = _
        rw [rcE.eq_9 q _ _ hq, rcE.eq_9 q a b (fun m r h₁ h₂ => hp ⟨m, r, h₁, h₂⟩),
          rcE_shift d a c, rcE_shift d b c]

theorem rcE_pickE : ∀ (j : Nat) {t : Expr}, rcE q t = true → rcE q (pickE j t) = true
  | 0, t, h => by simp [pickE, rcE, h]
  | j + 1, t, h => by simp only [pickE, rcE, h, Bool.true_and]; exact rcE_pickE j rfl

theorem rcE_tailTuple {Hc : Expr} (h : rcE q Hc = true) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), rcE q (tailTuple E j Hc) = true
  | [], _ => rfl
  | (_, _, _) :: E, j => by
      simp only [tailTuple, rcE, rcE_tailTuple h E (j + 1), Bool.and_true]
      unfold tailClause
      split
      · have := rcE_pickE (q := q) j (t := Hc.shift 1 0) (by rw [rcE_shift]; exact h)
        show rcE q (.app (pickE j (Hc.shift 1 0)) (.var 0)) = true
        rw [rcE_app this]; rfl
      · have := rcE_pickE (q := q) j (t := Hc.shift 3 0) (by rw [rcE_shift]; exact h)
        simp [rcE, rcE_app this, resumeB, Val.lam]

theorem rcE_lastTuple {Hw Hn : Expr} (hw : rcE q Hw = true) (hn : rcE q Hn = true) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), rcE q (lastTuple E j Hw Hn) = true
  | [], _ => rfl
  | (_, _, _) :: E, j => by
      simp only [lastTuple, rcE, rcE_lastTuple hw hn E (j + 1), Bool.and_true]
      unfold lastClause
      split
      · have := rcE_pickE (q := q) j (t := Hw.shift 1 0) (by rw [rcE_shift]; exact hw)
        show rcE q (.app (pickE j (Hw.shift 1 0)) (.var 0)) = true
        rw [rcE_app this]; rfl
      · have h₃ := rcE_pickE (q := q) j (t := Hw.shift 3 0) (by rw [rcE_shift]; exact hw)
        have h₆ := rcE_pickE (q := q) j (t := Hn.shift 6 0) (by rw [rcE_shift]; exact hn)
        simp [rcE, thenE, rcE_app h₃, rcE_app h₆, Val.lam, Val.prim, Val.inj₁, Val.inj₂, Val.unit]

theorem rcE_reifyV {res : Val} (h : rcE q res.1 = true) : rcE q (reifyV res).1 = true := by
  simp [reifyV, rkV, dlX, reifyH, reifyR, reifyC, tlX, closeKV, clV, BoCa.BoLo.hndE,
    BoCa.BoLo.hndVal, rcE, rcE_app, rcE_qualsVal, rcE_selfV, clB, Val.pair, Val.i32, nextV,
    closeV, h]

theorem rcE_divFuelV : rcE q divFuelV.1 = true := by
  simp [divFuelV, fuelH, fuelR, fuelC, fuelBody, spentV, fuelStep, BoCa.BoLo.hndE,
    BoCa.BoLo.hndVal, rcE, rcE_qualsVal, Val.pair, Val.i32, nextV, closeV]

end Decide

/-! ### A tied term raises only its effect context's names -/

/-- **The names of an effect context**, decided: not the reserved `0`, declared (`Ξ m ≠ []`), with
at most `2³²` operations.  `[spec §19]` -/
def EffCtx.names (Ξ : EffCtx) (m : UInt32) : Bool :=
  decide (m ≠ 0 ∧ Ξ m ≠ [] ∧ (Ξ m).length ≤ 2 ^ 32)

/-- The names of `Ξ`, as the predicate `RaiseOK` reads.  `[spec §19]` -/
abbrev EffCtx.Names (Ξ : EffCtx) (m : UInt32) : Prop := Ξ.names m = true

/-- The reserved `0`, a cancel's name, is no name of an effect context. -/
theorem EffCtx.names_zero (Ξ : EffCtx) : ¬ Ξ.Names 0 := by simp [EffCtx.names]

/-- An operation a row tied to `Ξ` finds is of a name of `Ξ`. -/
theorem names_of_rowAt {Ξ : EffCtx} {S : Row} (h : RowAt Ξ S) {n i : UInt32} {o : OpSig}
    (hf : Row.find S n i = some o) : Ξ.names n = true := by
  obtain ⟨hn0, hlen, hget⟩ := h n i o hf
  have hne : Ξ n ≠ [] := by intro h0; rw [h0] at hget; simp at hget
  simp only [EffCtx.names, decide_eq_true_eq]
  exact ⟨hn0, hne, hlen⟩

/-- **A term a tied derivation types raises only its effect context's names, and holds no `cfin`**:
`[raise]` finds its operation in a row tied to `Ξ` (decision R).  `[spec §19]` -/
theorem rcE_of_derivesAt {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : rcE Ξ.names e = true := by
  induction h with
  | force => exact rcE_forceE_var _ _
  | withI _ _ ihM ihN => exact rcE_withPair ihM ihN
  | withbor1U _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | withbor2U _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | withbor3U _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | sliceBorrowMU _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | sliceBorrowIU _ _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | foldImm => exact rcE_foldImmV _
  | foldOwn => exact rcE_foldOwnV _
  | foldOwnG => exact rcE_foldOwnGV _
  | foldReuse => exact rcE_foldReuseV _
  | unfoldN => exact rcE_unfoldV _
  | lolliE _ _ _ iha ihf => rw [rcE_app ihf]; exact iha
  | @effRaise _ _ V S o _ hAt hf _ _ _ ih =>
      simp only [BoCa.BoLo.raiseE, opArgE, Expr.val, Val.prim, Val.i32, rcE, ih,
        names_of_rowAt hAt hf, Bool.and_true, Bool.true_and]
      rfl
  | effHandleV _ _ _ _ _ _ _ _ _ _ ihc ihe | effHandleVB _ _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      simp [hndExpr, Val.i32, rcE, rcE_app, rcE_qualsVal, ihc, ihe]
  | effHandleT _ _ _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      simp only [rcE, Bool.and_eq_true] at ihc
      simp [hndExpr, Val.i32, rcE, rcE_app, rcE_qualsVal, ihc.1, ihe, rcE_tailTuple ihc.2]
  | effHandleL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      simp only [rcE, Bool.and_eq_true] at ihc
      simp [hndExpr, Val.i32, rcE, rcE_app, rcE_qualsVal, ihc.1, ihe,
        rcE_lastTuple ihc.2.1 ihc.2.2]
  | reify _ _ _ _ _ _ _ _ _ ihres => exact rcE_reifyV ihres
  | divFuel => exact rcE_divFuelV
  | @letPoly _ _ N _ _ b hcl _ _ ihV ihN =>
      have hb : rcE Ξ.names b = true := ihV
      rw [rcE_fill hb hcl N 0] at ihN
      rw [rcE.eq_9 _ _ _ (fun m r h _ => by cases h)]
      simp [rcE, Expr.val, Val.lam, ihN, hb]
  | _ => first | rfl | simp_all [rcE, rcE_app, absurdE, thenE, performE, opArgE, Val.i32]

/-- **A tied term is at its effect context's names**: every raise and every cancel state in it is
at `Ξ`'s names, since `rcE` accepts it (`rcE_of_derivesAt`).  `[spec §19]` -/
theorem raiseOK_of_derivesAt {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : e.RaiseOK Ξ.Names :=
  rcE_sound _ e (rcE_of_derivesAt h)

/-! ### No run of a tied term leaves its effect context's names -/

/-- **No run of a tied term raises or keeps a name its effect context does not have**: every
configuration a run from the empty memory reaches is at `Ξ`'s names, and so is every value its
memory stores.  `[spec §19]` -/
theorem raiseOK_reach {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) {μ : Heap} {e' : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ e') :
    e'.RaiseOK Ξ.Names ∧ HeapRaiseOK Ξ.Names μ :=
  raiseOK_steps (Ξ.names_zero) hs (raiseOK_of_derivesAt h) heapRaiseOK_empty

/-- **`CancelsNamed P μ₀ e`**: at every configuration a run from `(μ₀, e)` reaches that cancels a
continuation `κ`, `kappa H K` or `kappaC hasCancel ℓ H K` (`κ` at its cell) applied to `inj₂ ()`, every
running finaliser's `cfin` frame of the cancelled region `K` keeps none or a raise of a name in
`P`.  A `cfin` frame keeps what a finaliser raised (`[cfin-raise]`) or what a cancel passing it
kept (`[cfin-cancel]`), so this is a whole-run fact about the names finalisers raise.
`[spec §19]` -/
def CancelsNamed (P : UInt32 → Prop) (μ₀ : Heap) (e : Expr) : Prop :=
  ∀ μ e', Steps (ℍ := ℍ) μ₀ e μ e' → ∀ (K₀ : Kont) (H : Val) (K : Kont),
    (e' = K₀.plug (.app (kappa H K) (.val (Val.inj₂ .unit))) ∨
      ∃ hasCancel ℓ, e' = K₀.plug (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₂ .unit)))) →
    KCfinNamed P K

/-- **`CancelsNamed` holds of every tied term, at its effect context's names**: every cancel its
runs reach from the empty memory is of a region whose running finalisers keep none or an error of a
name of `Ξ`.  The cancelling configuration is at `Ξ`'s names (`raiseOK_reach`), and `κ`'s resume
branch holds the region (`kcfinNamed_of_cancel`).  `[spec §19]` -/
theorem cancelsNamed_of_derivesAt {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : CancelsNamed (ℍ := ℍ) Ξ.Names Adequacy.emptyMem e :=
  fun _ _ hs _ _ _ h₀ => kcfinNamed_of_cancel (raiseOK_reach h hs).1 h₀

end BoCa.Fig16.LogRel.Core

end
