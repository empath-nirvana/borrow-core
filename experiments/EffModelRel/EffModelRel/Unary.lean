import EffModelRel.Own

/-!
# EffModelRel — the unary relation: what a value owns

`VS A θ O v`: the value `v` of type `A` owns the tokens `O`. `CS C θ ok O c`: running `c` with the
tokens `O`, performing operations only on the instances `ok` permits, is safe and leaves an
answer that owns what is left. `θ` interprets the levels of the rows in types: level `n` is the
instance `θ[n]`, with its effect. A thunk's body runs with its row's permissions; a function adds
its row's after taking its argument, and an instance abstraction adds the instance it receives.
A function's argument may own something only if the function performs nothing that may be
dropped or copied before it takes it (`ArgOK`).

**The key lemma is independence** (`VS.indep`): a value at a mode that admits weakening or
contraction owns nothing. So whatever a continuation that may be dropped or copied captures at
such a mode is free to drop or copy; only linear values own, and the typing keeps them out of
such continuations.
-/

namespace EffRel

variable {S : Sig}

namespace Mode
def join (m k : Mode) : Mode := ⟨m.w || k.w, m.c || k.c⟩
def meet (m k : Mode) : Mode := ⟨m.w && k.w, m.c && k.c⟩
/-- Neither rule: a continuation that is resumed exactly once. -/
def IsLin (m : Mode) : Prop := m.w = false ∧ m.c = false
end Mode

/-- The mode of a value type: the structural rules its values admit. -/
def VTy.mode : VTy S → Mode
  | .g _ => Mode.unr
  | .prod A B => A.mode.meet B.mode
  | .sum A B => A.mode.meet B.mode
  | .U m _ _ => m
  | .cap _ _ => Mode.lin
  | .strm _ _ => Mode.lin

/-! ## Permissions -/

namespace Ok
def bot : Ok S := fun _ _ => False
def union (a b : Ok S) : Ok S := fun i e => a i e ∨ b i e
/-- One more instance. -/
def add (a : Ok S) (i : Nat) (e : S.E) : Ok S := fun j e' => a j e' ∨ (j = i ∧ e' = e)
/-- Every instance but one. -/
def rem (a : Ok S) (i : Nat) (e : S.E) : Ok S := fun j e' => a j e' ∧ ¬ (j = i ∧ e' = e)
def le (a b : Ok S) : Prop := ∀ i e, a i e → b i e
/-- Everything permitted is linear: nothing performed may be dropped or copied. -/
def IsLin (a : Ok S) : Prop := ∀ i e, a i e → (S.bnd e).IsLin
/-- Nothing permitted may be copied. -/
def NoC (a : Ok S) : Prop := ∀ i e, a i e → (S.bnd e).c = false

theorem le_refl (a : Ok S) : a.le a := fun _ _ h => h
theorem le_trans {a b c : Ok S} (h₁ : a.le b) (h₂ : b.le c) : a.le c :=
  fun i e h => h₂ i e (h₁ i e h)
theorem le_union_l (a b : Ok S) : a.le (a.union b) := fun _ _ h => .inl h
theorem le_union_r (a b : Ok S) : b.le (a.union b) := fun _ _ h => .inr h
theorem bot_le (a : Ok S) : (Ok.bot).le a := fun _ _ h => h.elim
theorem le_add (a : Ok S) (i : Nat) (e : S.E) : a.le (a.add i e) := fun _ _ h => .inl h
theorem union_le {a b c : Ok S} (h₁ : a.le c) (h₂ : b.le c) : (a.union b).le c :=
  fun i e h => h.elim (h₁ i e) (h₂ i e)
theorem add_mono {a b : Ok S} (h : a.le b) (i : Nat) (e : S.E) : (a.add i e).le (b.add i e) :=
  fun _ _ h' => h'.imp (h _ _) id
theorem union_mono {a b c d : Ok S} (h₁ : a.le c) (h₂ : b.le d) : (a.union b).le (c.union d) :=
  fun _ _ h => h.imp (h₁ _ _) (h₂ _ _)
theorem IsLin.mono {a b : Ok S} (h : a.le b) (hb : b.IsLin) : a.IsLin := fun i e h' => hb i e (h i e h')
theorem bot_isLin : (Ok.bot (S := S)).IsLin := fun _ _ h => h.elim
end Ok

/-- The instances a row's levels name, by name and effect. -/
abbrev LEnv (S : Sig) := List (Nat × S.E)

/-- The permissions of a row: its instance levels, read in `θ`. -/
def Rw.ok (θ : LEnv S) (ρ : Rw) : Ok S := fun i e => ∃ p ∈ ρ.ent, θ[p.1]? = some (i, e)

/-- An argument may own something only if nothing before it is taken may be dropped or copied. -/
def ArgOK (ok : Ok S) (Oa : Own) : Prop := Oa = 0 ∨ ok.IsLin

/-- The pull of a stream: done with an answer, or an element and the rest. -/
def StrmLeafS (P : Own → Strm S X → Prop) (VA : Own → X → Prop) :
    Own → (X ⊕ (Int × Strm S X)) → Prop
  | O, .inl a => VA O a
  | O, .inr (_, s) => P O s

def StrmClosedS (VA : Own → X → Prop) (ok : Ok S) (P : Own → Strm S X → Prop) : Prop :=
  ∀ O p d, TS ok (StrmLeafS P VA) O p → TS ok (fun O' _ => O' = 0) O d → P O (.mk p d)

/-- A stream owns what its pull or its drop disposes of: the least predicate closed under one
unfolding. -/
def StrmS (VA : Own → X → Prop) (ok : Ok S) (O : Own) (s : Strm S X) : Prop :=
  ∀ P, StrmClosedS VA ok P → P O s

mutual
def VS : (A : VTy S) → LEnv S → Own → A.den → Prop
  | .g _, _, O, _ => O = 0
  | .prod A B, θ, O, p => ∃ O₁ O₂, O = O₁ + O₂ ∧ VS A θ O₁ p.1 ∧ VS B θ O₂ p.2
  | .sum A B, θ, O, x =>
      match (x : A.den ⊕ B.den) with
      | .inl a => VS A θ O a
      | .inr b => VS B θ O b
  | .U m b C, θ, O, c => (m.w = true ∨ m.c = true → O = 0) ∧ CS C θ (b.ok θ) O c
  | .cap e s, _, O, c => O = Own.one (.cap s) c.1 ∧ (S.A e → False) ∧
      ∀ o a st, TS Ok.bot (fun O' _ => O' = 0) 0 (c.2 o a st)
  | .strm b A, θ, O, s => StrmS (fun O a => VS A θ O a) (b.ok θ) O s

def CS : (C : CTy S) → LEnv S → Ok S → Own → C.den → Prop
  | .F A, θ, ok, O, t => TS ok (fun O' a => VS A θ O' a) O t
  | .arr A b C, θ, ok, O, f => ∀ Oa a, VS A θ Oa a → ArgOK ok Oa →
      CS C θ (ok.union (b.ok θ)) (O + Oa) (f a)
  | .wth C D, θ, ok, O, p => CS C θ ok O p.1 ∧ CS D θ ok O p.2
  | .pi e C, θ, ok, O, f => ∀ i, CS C θ (ok.add i e) O (f i)
end

/-! ## Independence: what admits weakening or contraction owns nothing -/

theorem VS.indep : (A : VTy S) → ∀ {θ : LEnv S} {O : Own} {v : A.den}, VS A θ O v →
    (A.mode.w = true ∨ A.mode.c = true) → O = 0
  | .g _, _, _, _, h, _ => by simpa [VS] using h
  | .prod A B, _, _, _, h, hm => by
      simp only [VS] at h
      obtain ⟨O₁, O₂, rfl, h₁, h₂⟩ := h
      simp only [VTy.mode, Mode.meet, Bool.and_eq_true] at hm
      have hA : A.mode.w = true ∨ A.mode.c = true := by rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
      have hB : B.mode.w = true ∨ B.mode.c = true := by rcases hm with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
      rw [VS.indep A h₁ hA, VS.indep B h₂ hB, Own.zero_add]
  | .sum A B, _, _, x, h, hm => by
      simp only [VTy.mode, Mode.meet, Bool.and_eq_true] at hm
      have hA : A.mode.w = true ∨ A.mode.c = true := by rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
      have hB : B.mode.w = true ∨ B.mode.c = true := by rcases hm with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
      rcases x with a | b
      · exact VS.indep A (by simpa [VS] using h) hA
      · exact VS.indep B (by simpa [VS] using h) hB
  | .U _ _ _, _, _, _, h, hm => by simp only [VS] at h; exact h.1 hm
  | .cap _ _, _, _, _, _, hm => by simp [VTy.mode, Mode.lin] at hm
  | .strm _ _, _, _, _, _, hm => by simp [VTy.mode, Mode.lin] at hm

end EffRel
