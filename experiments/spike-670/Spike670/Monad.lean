import Backend2.Convert

/-!
# #670 — reading the conversion's monad

`CM = StateT CState (Except String)`. A run that succeeds is read backwards through its binds
(`ok_bind`); the primitive actions say what they change (`ok_fresh`, `ok_readFact`, …).
-/

namespace Backend2.Spike670
open Backend2

/-- `omega` through `Var`, which it does not unfold. -/
macro "vomega" : tactic => `(tactic| (try dsimp only [Var] at *) <;> omega)

/-- The run of `m` at `s` succeeded with `a`, ending at `s'`. -/
abbrev Ok (m : CM α) (s : CState) (a : α) (s' : CState) : Prop := m s = .ok (a, s')

theorem ok_bind {x : CM α} {f : α → CM β} {s : CState} {b : β} {s'' : CState}
    (h : Ok (x >>= f) s b s'') : ∃ a s', Ok x s a s' ∧ Ok (f a) s' b s'' := by
  unfold Ok at h
  simp only [bind, StateT.bind] at h
  cases hx : x s with
  | error e => rw [hx] at h; cases h
  | ok r => rw [hx] at h; exact ⟨r.1, r.2, by simp [Ok, hx], h⟩

theorem ok_pure {a b : α} {s s' : CState} (h : Ok (pure a : CM α) s b s') : b = a ∧ s' = s := by
  unfold Ok at h
  simp only [pure, StateT.pure, Except.pure] at h
  cases h; exact ⟨rfl, rfl⟩

theorem ok_throw {e : String} {s s' : CState} {b : α} (h : Ok (throw e : CM α) s b s') : False := by
  unfold Ok at h
  simp [throw, throwThe, MonadExceptOf.throw, StateT.lift] at h

theorem ok_get {s s' : CState} {b : CState} (h : Ok (get : CM CState) s b s') : b = s ∧ s' = s := by
  unfold Ok at h
  simp [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem ok_modify {f : CState → CState} {s s' : CState} {b : PUnit}
    (h : Ok (modify f : CM PUnit) s b s') : s' = f s := by
  unfold Ok at h
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure] at h
  exact h.symm

theorem ok_modifyGet {f : CState → α × CState} {s s' : CState} {b : α}
    (h : Ok (modifyGet f : CM α) s b s') : (b, s') = f s := by
  unfold Ok at h
  simp [modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure] at h
  rw [← h]

/-- What the slice's actions keep: the counter does not go back, the machine set is fixed. -/
structure Grows (s s' : CState) : Prop where
  next : s.next ≤ s'.next
  mach : s'.mach = s.mach

theorem Grows.refl (s : CState) : Grows s s := ⟨le_refl _, rfl⟩
theorem Grows.trans {s₁ s₂ s₃ : CState} (a : Grows s₁ s₂) (b : Grows s₂ s₃) : Grows s₁ s₃ :=
  ⟨le_trans a.next b.next, b.mach.trans a.mach⟩

theorem ok_fresh {t : LTy} {s s' : CState} {x : Var} (h : Ok (fresh t) s x s') :
    x = s.next ∧ s'.next = s.next + 1 ∧ s'.mach = s.mach := by
  have := ok_modifyGet h
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  exact ⟨rfl, rfl, rfl⟩

theorem ok_tyOf {x : Var} {s s' : CState} {t : LTy} (h : Ok (tyOf x) s t s') : s' = s := by
  obtain ⟨a, s₁, h₁, h₂⟩ := ok_bind h
  obtain ⟨rfl, rfl⟩ := ok_get h₁
  split at h₂
  · exact (ok_pure h₂).2
  · exact (ok_throw h₂).elim

theorem ok_freshLike {x : Var} {s s' : CState} {y : Var} (h : Ok (freshLike x) s y s') :
    y = s.next ∧ s'.next = s.next + 1 ∧ s'.mach = s.mach := by
  obtain ⟨a, s₁, h₁, h₂⟩ := ok_bind h
  cases ok_tyOf h₁
  exact ok_fresh h₂

theorem ok_readFact {k : String} {s s' : CState} {b : PUnit} (h : Ok (readFact k) s b s') :
    s'.next = s.next ∧ s'.mach = s.mach := by
  have := ok_modify h
  subst this; exact ⟨rfl, rfl⟩

end Backend2.Spike670
