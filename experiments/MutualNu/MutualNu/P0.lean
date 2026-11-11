/-!
# MutualNu P0 — representation mechanics (#995, `km-plan.md` §2.2)

A miniature of Core's mutual `VTy`/`CTy` with the system former `nuSys m i Cs` and today's `ν`
as the pattern abbreviation `nu C := nuSys 0 0 C`. It checks, before the former changes in Core:

1. a shape match written against `nu` (with a fallthrough) compiles unchanged;
2. an exhaustive structural function needs a `nuSys` arm, and gets it with `m i` carried along;
3. the joint greatest fixed point's clause is definable inside the structural `vE`/`cC`/`cB`
   block through a spine helper `cBSys` that calls `cB` on strict subterms only, and `cBSys` at
   the last body is `cB` at that body by `rfl`;
4. a consume through a spine helper `consumeNu` is structural, and at `m = 0` it is the arm
   today's `consumeAt` has, by `rfl`.
-/

namespace MutualNu.P0

mutual
inductive VTy' where
  | unit
  | tensor (A B : VTy')
  | sum (A B : VTy')
  | thunk (C : CTy')
  | tvar (n : Nat)
inductive CTy' where
  | ret (A : VTy')
  | amp (C D : CTy')
  | top
  | nuSys (m i : Nat) (Cs : CTy')
end

deriving instance DecidableEq for VTy', CTy'

/-- Today's `νX. C`: the system of one equation. -/
@[match_pattern] abbrev CTy'.nu (C : CTy') : CTy' := .nuSys 0 0 C

/-! ### 1. A shape match against `nu`, as `Frontend/Check/Elab.lean` and `Backend2/Convert.lean`
have them -/

def isLoopShape : CTy' → Bool
  | .nu (.amp (.ret (.sum _ (.tvar 0))) (.ret _)) => true
  | _ => false

example : isLoopShape (.nu (.amp (.ret (.sum .unit (.tvar 0))) (.ret .unit))) = true := rfl
example : isLoopShape (.nuSys 1 0 (.amp (.ret (.sum .unit (.tvar 0))) (.ret .unit))) = false := rfl

/-- A shape match with `nu` and a value-type context, as `Consume.lean:162`. -/
def closeRes? : VTy' → Option VTy'
  | .thunk (.nu (.amp _ (.ret R))) => some R
  | _ => none

example : closeRes? (.thunk (.nu (.amp .top (.ret .unit)))) = some .unit := rfl

/-! ### 2. An exhaustive structural function: the `nuSys` arm carries `m i` -/

def CTy'.size : CTy' → Nat
  | .ret _ => 1
  | .amp C D => C.size + D.size + 1
  | .top => 1
  | .nuSys _ _ C => C.size + 1

-- An exhaustive function written with today's `.nu C` arm alone is refused: the missing cases
-- name `nuSys`, so the compiler lists every arm K-M.1 must touch.
/--
error: Missing cases:
(nuSys Nat.zero (Nat.succ _) _)
(nuSys (Nat.succ _) _ _)
-/
#guard_msgs in
def CTy'.sizeOld : CTy' → Nat
  | .ret _ => 1
  | .amp C D => C.sizeOld + D.sizeOld + 1
  | .top => 1
  | .nu C => C.sizeOld + 1

/-- A construction site written with `.nu` is the abbreviation. -/
example (C : CTy') : (CTy'.nu C).size = C.size + 1 := rfl

/-! ### The system's bodies -/

/-- The `j`-th body of the spine of `m + 1` bodies. -/
def CTy'.body : Nat → Nat → CTy' → CTy'
  | 0, _, C => C
  | _ + 1, 0, .amp C _ => C
  | m + 1, j + 1, .amp _ D => CTy'.body m j D
  | _ + 1, _, _ => .top

example (C : CTy') : C.body 0 0 = C := rfl

/-- A body's shape: a `&` of two trees (here any). -/
def CTy'.BodyShape : CTy' → Prop
  | .amp _ _ => True
  | _ => False

def CTy'.SysShape : Nat → CTy' → Prop
  | 0, C => C.BodyShape
  | m + 1, .amp C D => C.BodyShape ∧ CTy'.SysShape m D
  | _ + 1, _ => False

/-! ### 3. The relation: the joint greatest fixed point in the structural block -/

abbrev Pred := Nat → Prop
abbrev Env := Nat → Pred

/-- The environment of a system at the candidate tuple `Rs`: variable `j ≤ m` at `Rs j`. -/
def envS (m : Nat) (Rs : Nat → Pred) : Env := fun k => if k ≤ m then Rs k else fun _ => True

mutual
def vE : Option Env → VTy' → Nat → Prop
  | _, .unit, v => v = 0
  | η, .tensor A B, v => vE η A v ∧ vE η B (v + 1)
  | η, .sum A B, v => vE η A v ∨ vE η B (v + 1)
  | _, .thunk C, v => cC C v
  | none, .tvar _, _ => True
  | some η, .tvar n, v => η n v
  termination_by structural _ x => x
def cC : CTy' → Nat → Prop
  | .ret A, e => vE none A e
  | .amp C D, e => cC C e ∧ cC D (e + 1)
  | .top, _ => True
  | .nuSys m i Cs, e => Cs.SysShape m →
      ∃ Rs : Nat → Pred, cBSys (some (envS m Rs)) m Cs Rs 0 ∧ Rs i e
  termination_by structural x => x
/-- One unfolding of an observation tree. -/
def cB : Option Env → CTy' → Nat → Prop
  | η, .ret A, e => vE η A e
  | η, .amp C D, e => cB η C e ∧ cB η D (e + 1)
  | _, .top, _ => True
  | _, .nuSys _ _ _, _ => True
  termination_by structural _ x => x
/-- Each component of `Rs` from `j₀` on is below one unfolding of its body; the bodies are the
spine's, and `cB` is called on strict subterms only. -/
def cBSys : Option Env → Nat → CTy' → (Nat → Pred) → Nat → Prop
  | η, 0, .amp L R, Rs, j₀ => ∀ e, Rs j₀ e → cB η L e ∧ cB η R (e + 1)
  | η, m + 1, .amp (.amp L R) D, Rs, j₀ =>
      (∀ e, Rs j₀ e → cB η L e ∧ cB η R (e + 1)) ∧ cBSys η m D Rs (j₀ + 1)
  | _, _, _, _, _ => True
  termination_by structural _ _ x => x
end

/-- At the last body, `cBSys` is `cB` at it, by `rfl`. -/
example (η : Option Env) (L R : CTy') (Rs : Nat → Pred) (j : Nat) :
    cBSys η 0 (.amp L R) Rs j = ∀ e, Rs j e → cB η (.amp L R) e := rfl

/-- And in the spine, componentwise. -/
example (η : Option Env) (L R D : CTy') (Rs : Nat → Pred) (j m : Nat) :
    cBSys η (m + 1) (.amp (.amp L R) D) Rs j =
      ((∀ e, Rs j e → cB η (.amp L R) e) ∧ cBSys η m D Rs (j + 1)) := rfl

/-- `cBSys` is "every component below its body": the clause's meaning, by induction on the
spine. -/
theorem cBSys_iff (η : Option Env) (Rs : Nat → Pred) :
    ∀ (m : Nat) (Cs : CTy') (j₀ : Nat), Cs.SysShape m →
      (cBSys η m Cs Rs j₀ ↔ ∀ j, j ≤ m → ∀ e, Rs (j₀ + j) e → cB η (Cs.body m j) e)
  | 0, .amp L R, j₀, _ => by
      simp only [cBSys, CTy'.body, cB]
      constructor
      · intro h j hj e he; obtain rfl : j = 0 := by omega
        exact h e he
      · intro h e he; exact h 0 (Nat.le_refl 0) e he
  | m + 1, .amp (.amp L R) D, j₀, hS => by
      have ih := cBSys_iff η Rs m D (j₀ + 1) hS.2
      simp only [cBSys]
      constructor
      · rintro ⟨h0, hr⟩ j hj e he
        cases j with
        | zero => exact h0 e he
        | succ j =>
            have := (ih.mp hr) j (by omega) e (by rwa [show j₀ + (j + 1) = j₀ + 1 + j by omega] at he)
            simpa [CTy'.body] using this
      · intro h
        refine ⟨fun e he => h 0 (Nat.zero_le _) e he, ih.mpr fun j hj e he => ?_⟩
        have := h (j + 1) (by omega) e (by rwa [show j₀ + 1 + j = j₀ + (j + 1) by omega] at he)
        simpa [CTy'.body] using this
  | 0, .ret _, _, h | 0, .top, _, h | 0, .nuSys _ _ _, _, h => h.elim
  | _ + 1, .ret _, _, h | _ + 1, .top, _, h | _ + 1, .nuSys _ _ _, _, h => h.elim
  | _ + 1, .amp (.ret _) _, _, h | _ + 1, .amp .top _, _, h
  | _ + 1, .amp (.nuSys _ _ _) _, _, h => h.1.elim

/-- Today's clause at `m = 0`, propositionally: `∃ Rs` over a 1-tuple is `∃ R`. -/
theorem cC_nu_iff_old (C : CTy') (e : Nat) :
    cC (.nu C) e ↔ (C.SysShape 0 →
      ∃ R : Pred, (∀ e', R e' → cB (some (envS 0 fun _ => R)) C e') ∧ R e) := by
  cases C with
  | amp L R =>
      simp only [cC, cBSys, cB]
      constructor
      · intro h hS
        obtain ⟨Rs, hR, he⟩ := h hS
        refine ⟨Rs 0, fun e' h' => ?_, he⟩
        have hη : envS 0 Rs = envS 0 (fun _ => Rs 0) := by
          funext k; unfold envS; split <;> rename_i hk
          · obtain rfl : k = 0 := by omega
            rfl
          · rfl
        rw [← hη]; exact hR e' h'
      · intro h hS
        obtain ⟨R₀, hR, he⟩ := h hS
        exact ⟨fun _ => R₀, hR, he⟩
  | ret _ | top | nuSys _ _ _ => simp [cC, CTy'.SysShape, CTy'.BodyShape]

/-! ### 4. The consume through the spine -/

mutual
def consumeAt : VTy' → Nat
  | .unit => 0
  | .tensor A B => consumeAt A + consumeAt B
  | .sum A B => consumeAt A + consumeAt B
  | .thunk (.nuSys m i Cs) => consumeNu m i Cs
  | .thunk _ => 1
  | .tvar _ => 0
  termination_by structural x => x
/-- The consume of `U νᵢ`: close, then the residual of body `i`. -/
def consumeNu : Nat → Nat → CTy' → Nat
  | 0, _, .amp _ (.ret R) => consumeAt R + 1
  | _ + 1, 0, .amp (.amp _ (.ret R)) _ => consumeAt R + 1
  | m + 1, i + 1, .amp _ D => consumeNu m i D
  | _, _, _ => 1
  termination_by structural _ _ x => x
end

/-- At `m = 0` the consume is today's arm, by `rfl`. -/
example (C _R : CTy') (A : VTy') :
    consumeAt (.thunk (.nu (.amp C (.ret A)))) = consumeAt A + 1 := rfl

example (C₀ C₁ : CTy') (A : VTy') :
    consumeAt (.thunk (.nuSys 1 1 (.amp C₀ (.amp C₁ (.ret A))))) = consumeAt A + 1 := rfl

end MutualNu.P0
