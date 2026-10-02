import EffModelRel.Own

/-!
# EffModelRel — the unary relation: what a value owns

`VS A O v`: the value `v` of type `A` owns the tokens `O`. `CS C bnd O c`: running `c` with the
tokens `O`, performing operations within `bnd`, is safe and leaves an answer that owns what is
left. A thunk's body runs within the thunk type's bound; a function's argument may own something
only if the function performs nothing that may be dropped or copied before it takes it
(`ArgOK`).

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
  | .res => Mode.unr
  | .strm _ _ => Mode.lin

/-- Bounds of the operations a tree performs, by instance and effect. -/
abbrev Bnd (S : Sig) := Nat → S.E → Mode

def Bnd.const (m : Mode) : Bnd S := fun _ _ => m
def Bnd.le (b b' : Bnd S) : Prop := ∀ i e, (b' i e).ge (b i e) = true
def Bnd.join (b : Bnd S) (m : Mode) : Bnd S := fun i e => (b i e).join m
/-- Every operation is linear. -/
def Bnd.IsLin (b : Bnd S) : Prop := ∀ i e, (b i e).IsLin

/-- An argument may own something only if nothing before it is taken may be dropped or copied. -/
def ArgOK (bnd : Bnd S) (Oa : Own) : Prop := Oa = 0 ∨ bnd.IsLin

/-- The pull of a stream: done with an answer, or an element and the rest. -/
def StrmLeafS (P : Own → Strm S X → Prop) (VA : Own → X → Prop) :
    Own → (X ⊕ (Int × Strm S X)) → Prop
  | O, .inl a => VA O a
  | O, .inr (_, s) => P O s

def StrmClosedS (VA : Own → X → Prop) (bnd : Bnd S) (P : Own → Strm S X → Prop) : Prop :=
  ∀ O p d, TS bnd (StrmLeafS P VA) O p → TS bnd (fun O' _ => O' = 0) O d → P O (.mk p d)

/-- A stream owns what its pull or its drop disposes of: the least predicate closed under one
unfolding. -/
def StrmS (VA : Own → X → Prop) (bnd : Bnd S) (O : Own) (s : Strm S X) : Prop :=
  ∀ P, StrmClosedS VA bnd P → P O s

mutual
def VS : (A : VTy S) → Own → A.den → Prop
  | .g _, O, _ => O = 0
  | .prod A B, O, p => ∃ O₁ O₂, O = O₁ + O₂ ∧ VS A O₁ p.1 ∧ VS B O₂ p.2
  | .sum A B, O, x =>
      match (x : A.den ⊕ B.den) with
      | .inl a => VS A O a
      | .inr b => VS B O b
  | .U m b C, O, c => (m.w = true ∨ m.c = true → O = 0) ∧ CS C (Bnd.const b.req) O c
  | .cap _ s, O, c => O = Own.one (.cap s) c.1 ∧
      ∀ o a st, TS (Bnd.const Mode.unr) (fun O' _ => O' = 0) 0 (c.2 o a st)
  | .res, O, _ => O = 0
  | .strm b A, O, s => StrmS (fun O a => VS A O a) (Bnd.const b.req) O s

def CS : (C : CTy S) → Bnd S → Own → C.den → Prop
  | .F A, bnd, O, t => TS bnd (fun O' a => VS A O' a) O t
  | .arr A b C, bnd, O, f => ∀ Oa a, VS A Oa a → ArgOK bnd Oa → CS C (bnd.join b.req) (O + Oa) (f a)
  | .wth C D, bnd, O, p => CS C bnd O p.1 ∧ CS D bnd O p.2
  | .pi _ C, bnd, O, f => ∀ i, CS C bnd O (f i)
end

/-! ## Independence: what admits weakening or contraction owns nothing -/

theorem VS.indep : (A : VTy S) → ∀ {O : Own} {v : A.den}, VS A O v →
    (A.mode.w = true ∨ A.mode.c = true) → O = 0
  | .g _, _, _, h, _ => by simpa [VS] using h
  | .prod A B, _, _, h, hm => by
      simp only [VS] at h
      obtain ⟨O₁, O₂, rfl, h₁, h₂⟩ := h
      simp only [VTy.mode, Mode.meet, Bool.and_eq_true] at hm
      have hA : A.mode.w = true ∨ A.mode.c = true := by rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
      have hB : B.mode.w = true ∨ B.mode.c = true := by rcases hm with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
      rw [VS.indep A h₁ hA, VS.indep B h₂ hB, Own.zero_add]
  | .sum A B, _, x, h, hm => by
      simp only [VTy.mode, Mode.meet, Bool.and_eq_true] at hm
      have hA : A.mode.w = true ∨ A.mode.c = true := by rcases hm with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
      have hB : B.mode.w = true ∨ B.mode.c = true := by rcases hm with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
      rcases x with a | b
      · exact VS.indep A (by simpa [VS] using h) hA
      · exact VS.indep B (by simpa [VS] using h) hB
  | .U _ _ _, _, _, h, hm => by simp only [VS] at h; exact h.1 hm
  | .cap _ _, _, _, _, hm => by simp [VTy.mode, Mode.lin] at hm
  | .res, _, _, h, _ => by simpa [VS] using h
  | .strm _ _, _, _, _, hm => by simp [VTy.mode, Mode.lin] at hm

end EffRel
