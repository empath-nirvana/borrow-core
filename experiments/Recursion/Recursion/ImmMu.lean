import CBPVWorld.Types

/-!
# Recursion — P-Imm̲: the reborrow metafunction at `μ`

Pure syntax. `MTy` is CBPVWorld's `VTy` with type variables (`tvar`, de Bruijn) and `μ`.
`Imm̲ 'b` recurses through `⊗`, `⊕` and `[@a]`, and stops at `Ref`, `Mut`, `Imm` and `!`, keeping
the payload type. At `μX. T` the payloads kept by those four clauses must be the closed type
the cell holds, so `Imm̲` carries a *payload substitution* `pay`: a variable at a head position
stays a variable (it names the reborrowed `μ`), and inside a kept payload it is replaced by the
`μ`-type it stands for (`immG`).

* `immReborrow_unroll`: `Imm̲ 'b (T[μX.T/X]) = (Imm̲ᵡ 'b T)[Imm̲ 'b (μX.T)/Y]`, for every `T`
  with at most `X` free. It is the instance of `immG_subst`, proved by induction on the type,
  with `immG_rename` for the binder.
* `naive_ne`: the clause `Imm̲ 'b (μX.T) = μX. Imm̲ 'b T` with `Imm̲ 'b X = X` unrolls, at the boxed
  list `μX. 1 ⊕ (1 ⊗ Ref X)`, to a different type than `Imm̲ 'b (T[L/X])`.
* `toV_immReb`: on `μ`-free closed types `immReb` is CBPVWorld's `VTy.immReborrow`.
-/

namespace BoCa.Fig16.LogRel.CBPVWorld.Recursion
open BoCa
open BoCa.Fig16

/-- `VTy` with type variables and `μ`. `U C` is a leaf: `C` mentions no type variable. -/
inductive MTy where
  | unit
  | tensor (A B : MTy)
  | zero
  | sum (A B : MTy)
  | thunk (C : CTy)
  | ref (A : MTy)
  | imm (a : Lifetime.Life) (A : MTy)
  | «mut» (a : Lifetime.Life) (A : MTy)
  | box (a : Lifetime.Life) (A : MTy)
  | bang (A : MTy)
  | unk
  /-- A type variable, de Bruijn. -/
  | tvar (n : Nat)
  /-- `μX. A`, binding index 0 in `A`. -/
  | mu (A : MTy)

namespace MTy

/-! ### Renaming and substitution -/

def upR (r : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => r n + 1

def rename (r : Nat → Nat) : MTy → MTy
  | unit => unit
  | tensor A B => tensor (rename r A) (rename r B)
  | zero => zero
  | sum A B => sum (rename r A) (rename r B)
  | thunk C => thunk C
  | ref A => ref (rename r A)
  | imm a A => imm a (rename r A)
  | «mut» a A => «mut» a (rename r A)
  | box a A => box a (rename r A)
  | bang A => bang (rename r A)
  | unk => unk
  | tvar n => tvar (r n)
  | mu A => mu (rename (upR r) A)

/-- `x · f`: `0 ↦ x`, `n + 1 ↦ f n`. -/
def scons (x : MTy) (f : Nat → MTy) : Nat → MTy
  | 0 => x
  | n + 1 => f n

def upS (σ : Nat → MTy) : Nat → MTy := scons (tvar 0) (fun n => rename Nat.succ (σ n))

def subst (σ : Nat → MTy) : MTy → MTy
  | unit => unit
  | tensor A B => tensor (subst σ A) (subst σ B)
  | zero => zero
  | sum A B => sum (subst σ A) (subst σ B)
  | thunk C => thunk C
  | ref A => ref (subst σ A)
  | imm a A => imm a (subst σ A)
  | «mut» a A => «mut» a (subst σ A)
  | box a A => box a (subst σ A)
  | bang A => bang (subst σ A)
  | unk => unk
  | tvar n => σ n
  | mu A => mu (subst (upS σ) A)

/-- `T[S/X]`: index 0 to `S`, the others down by one. -/
def inst (S T : MTy) : MTy := subst (scons S tvar) T

theorem rename_rename : ∀ (A : MTy) (r r' : Nat → Nat),
    rename r (rename r' A) = rename (r ∘ r') A
  | unit, _, _ => rfl
  | tensor A B, r, r' => by simp [rename, rename_rename A, rename_rename B]
  | zero, _, _ => rfl
  | sum A B, r, r' => by simp [rename, rename_rename A, rename_rename B]
  | thunk _, _, _ => rfl
  | ref A, r, r' => by simp [rename, rename_rename A]
  | imm _ A, r, r' => by simp [rename, rename_rename A]
  | «mut» _ A, r, r' => by simp [rename, rename_rename A]
  | box _ A, r, r' => by simp [rename, rename_rename A]
  | bang A, r, r' => by simp [rename, rename_rename A]
  | unk, _, _ => rfl
  | tvar _, _, _ => rfl
  | mu A, r, r' => by
      simp only [rename, rename_rename A]
      congr 2
      funext n; cases n <;> rfl

theorem subst_rename : ∀ (A : MTy) (σ : Nat → MTy) (r : Nat → Nat),
    subst σ (rename r A) = subst (σ ∘ r) A
  | unit, _, _ => rfl
  | tensor A B, σ, r => by simp [rename, subst, subst_rename A, subst_rename B]
  | zero, _, _ => rfl
  | sum A B, σ, r => by simp [rename, subst, subst_rename A, subst_rename B]
  | thunk _, _, _ => rfl
  | ref A, σ, r => by simp [rename, subst, subst_rename A]
  | imm _ A, σ, r => by simp [rename, subst, subst_rename A]
  | «mut» _ A, σ, r => by simp [rename, subst, subst_rename A]
  | box _ A, σ, r => by simp [rename, subst, subst_rename A]
  | bang A, σ, r => by simp [rename, subst, subst_rename A]
  | unk, _, _ => rfl
  | tvar _, _, _ => rfl
  | mu A, σ, r => by
      simp only [rename, subst, subst_rename A]
      congr 2
      funext n; cases n <;> rfl

theorem rename_subst : ∀ (A : MTy) (r : Nat → Nat) (σ : Nat → MTy),
    rename r (subst σ A) = subst (fun n => rename r (σ n)) A
  | unit, _, _ => rfl
  | tensor A B, r, σ => by simp [rename, subst, rename_subst A, rename_subst B]
  | zero, _, _ => rfl
  | sum A B, r, σ => by simp [rename, subst, rename_subst A, rename_subst B]
  | thunk _, _, _ => rfl
  | ref A, r, σ => by simp [rename, subst, rename_subst A]
  | imm _ A, r, σ => by simp [rename, subst, rename_subst A]
  | «mut» _ A, r, σ => by simp [rename, subst, rename_subst A]
  | box _ A, r, σ => by simp [rename, subst, rename_subst A]
  | bang A, r, σ => by simp [rename, subst, rename_subst A]
  | unk, _, _ => rfl
  | tvar _, _, _ => rfl
  | mu A, r, σ => by
      simp only [rename, subst, rename_subst A]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n =>
          simp only [upS, scons, rename_rename]
          rfl

theorem subst_subst : ∀ (A : MTy) (σ τ : Nat → MTy),
    subst σ (subst τ A) = subst (fun n => subst σ (τ n)) A
  | unit, _, _ => rfl
  | tensor A B, σ, τ => by simp [subst, subst_subst A, subst_subst B]
  | zero, _, _ => rfl
  | sum A B, σ, τ => by simp [subst, subst_subst A, subst_subst B]
  | thunk _, _, _ => rfl
  | ref A, σ, τ => by simp [subst, subst_subst A]
  | imm _ A, σ, τ => by simp [subst, subst_subst A]
  | «mut» _ A, σ, τ => by simp [subst, subst_subst A]
  | box _ A, σ, τ => by simp [subst, subst_subst A]
  | bang A, σ, τ => by simp [subst, subst_subst A]
  | unk, _, _ => rfl
  | tvar _, _, _ => rfl
  | mu A, σ, τ => by
      simp only [subst, subst_subst A]
      congr 2
      funext n
      cases n with
      | zero => rfl
      | succ n =>
          simp only [upS, scons, subst_rename, rename_subst]
          rfl

/-! ### Closed types -/

/-- Every free variable of `A` is below `k`. -/
def Cl : Nat → MTy → Prop
  | _, unit => True
  | k, tensor A B => Cl k A ∧ Cl k B
  | _, zero => True
  | k, sum A B => Cl k A ∧ Cl k B
  | _, thunk _ => True
  | k, ref A => Cl k A
  | k, imm _ A => Cl k A
  | k, «mut» _ A => Cl k A
  | k, box _ A => Cl k A
  | k, bang A => Cl k A
  | _, unk => True
  | k, tvar n => n < k
  | k, mu A => Cl (k + 1) A

theorem Cl_rename : ∀ (A : MTy) {k k' : Nat} (r : Nat → Nat), Cl k A →
    (∀ n, n < k → r n < k') → Cl k' (rename r A)
  | unit, _, _, _, _, _ => trivial
  | tensor A B, _, _, r, h, hr => ⟨Cl_rename A r h.1 hr, Cl_rename B r h.2 hr⟩
  | zero, _, _, _, _, _ => trivial
  | sum A B, _, _, r, h, hr => ⟨Cl_rename A r h.1 hr, Cl_rename B r h.2 hr⟩
  | thunk _, _, _, _, _, _ => trivial
  | ref A, _, _, r, h, hr => Cl_rename A r h hr
  | imm _ A, _, _, r, h, hr => Cl_rename A r h hr
  | «mut» _ A, _, _, r, h, hr => Cl_rename A r h hr
  | box _ A, _, _, r, h, hr => Cl_rename A r h hr
  | bang A, _, _, r, h, hr => Cl_rename A r h hr
  | unk, _, _, _, _, _ => trivial
  | tvar n, _, _, _, h, hr => hr n h
  | mu A, _, _, r, h, hr => Cl_rename A (upR r) h (fun n hn => by
      cases n with
      | zero => exact Nat.succ_pos _
      | succ n => exact Nat.succ_lt_succ (hr n (Nat.lt_of_succ_lt_succ hn)))

theorem Cl_subst : ∀ (A : MTy) {k : Nat} (σ : Nat → MTy), (∀ n, Cl k (σ n)) →
    Cl k (subst σ A)
  | unit, _, _, _ => trivial
  | tensor A B, _, σ, h => ⟨Cl_subst A σ h, Cl_subst B σ h⟩
  | zero, _, _, _ => trivial
  | sum A B, _, σ, h => ⟨Cl_subst A σ h, Cl_subst B σ h⟩
  | thunk _, _, _, _ => trivial
  | ref A, _, σ, h => Cl_subst A σ h
  | imm _ A, _, σ, h => Cl_subst A σ h
  | «mut» _ A, _, σ, h => Cl_subst A σ h
  | box _ A, _, σ, h => Cl_subst A σ h
  | bang A, _, σ, h => Cl_subst A σ h
  | unk, _, _, _ => trivial
  | tvar n, _, _, h => h n
  | mu A, k, σ, h => Cl_subst A (upS σ) (fun n => by
      cases n with
      | zero => exact Nat.succ_pos k
      | succ n => exact Cl_rename (σ n) Nat.succ (h n) (fun _ hm => Nat.succ_lt_succ hm))

theorem rename_closed : ∀ (A : MTy) {k : Nat} (r : Nat → Nat), Cl k A →
    (∀ n, n < k → r n = n) → rename r A = A
  | unit, _, _, _, _ => rfl
  | tensor A B, _, r, h, hr => by simp [rename, rename_closed A r h.1 hr, rename_closed B r h.2 hr]
  | zero, _, _, _, _ => rfl
  | sum A B, _, r, h, hr => by simp [rename, rename_closed A r h.1 hr, rename_closed B r h.2 hr]
  | thunk _, _, _, _, _ => rfl
  | ref A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | imm _ A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | «mut» _ A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | box _ A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | bang A, _, r, h, hr => by simp [rename, rename_closed A r h hr]
  | unk, _, _, _, _ => rfl
  | tvar n, _, _, h, hr => by simp [rename, hr n h]
  | mu A, _, r, h, hr => by
      simp only [rename]
      rw [rename_closed A (upR r) h (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [upR, hr n (Nat.lt_of_succ_lt_succ hn)])]

theorem subst_closed : ∀ (A : MTy) {k : Nat} (σ : Nat → MTy), Cl k A →
    (∀ n, n < k → σ n = tvar n) → subst σ A = A
  | unit, _, _, _, _ => rfl
  | tensor A B, _, σ, h, hσ => by simp [subst, subst_closed A σ h.1 hσ, subst_closed B σ h.2 hσ]
  | zero, _, _, _, _ => rfl
  | sum A B, _, σ, h, hσ => by simp [subst, subst_closed A σ h.1 hσ, subst_closed B σ h.2 hσ]
  | thunk _, _, _, _, _ => rfl
  | ref A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | imm _ A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | «mut» _ A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | box _ A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | bang A, _, σ, h, hσ => by simp [subst, subst_closed A σ h hσ]
  | unk, _, _, _, _ => rfl
  | tvar n, _, _, h, hσ => hσ n h
  | mu A, _, σ, h, hσ => by
      simp only [subst]
      rw [subst_closed A (upS σ) h (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [upS, scons, hσ n (Nat.lt_of_succ_lt_succ hn), rename])]

/-- A closed type is fixed by every substitution. -/
theorem subst_closed0 {A : MTy} (h : Cl 0 A) (σ : Nat → MTy) : subst σ A = A :=
  subst_closed A σ h (fun _ hn => absurd hn (Nat.not_lt_zero _))

theorem rename_closed0 {A : MTy} (h : Cl 0 A) (r : Nat → Nat) : rename r A = A :=
  rename_closed A r h (fun _ hn => absurd hn (Nat.not_lt_zero _))

/-! ### `Imm̲` with a payload substitution -/

/-- `Imm̲ 'b` at `pay`: a head-position variable is kept; a payload kept by the `Ref`, `Imm`,
`Mut` or `!` clause has every variable replaced by the closed type it stands for (`pay`). At
`μX. A` the new variable stands for `μX. A` itself. -/
def immG (b : Lifetime.Life) (pay : Nat → MTy) : MTy → MTy
  | unit => unit
  | tensor A B => tensor (immG b pay A) (immG b pay B)
  | zero => zero
  | sum A B => sum (immG b pay A) (immG b pay B)
  | thunk _ => unk
  | ref A => imm b (subst pay A)
  | imm a A => imm a (subst pay A)
  | «mut» _ A => imm b (subst pay A)
  | box _ A => immG b pay A
  | bang A => bang (subst pay A)
  | unk => unk
  | tvar n => tvar n
  | mu A => mu (immG b (scons (subst pay (mu A)) pay) A)

/-- The default payload substitution, for closed types (never consulted). -/
abbrev dflt : Nat → MTy := fun _ => unit

/-- `Imm̲ 'b A` on closed types. -/
def immReb (b : Lifetime.Life) (A : MTy) : MTy := immG b dflt A

/-- `Imm̲ᵡ 'b T` for `μX. T`: head `X` stays the variable, payload `X` becomes `μX. T`. -/
def immX (b : Lifetime.Life) (T : MTy) : MTy := immG b (scons (mu T) dflt) T

section
variable (b : Lifetime.Life)

theorem scons_closed {x : MTy} {f : Nat → MTy} (hx : Cl 0 x) (hf : ∀ n, Cl 0 (f n)) :
    ∀ n, Cl 0 (scons x f n)
  | 0 => hx
  | n + 1 => hf n

/-- `Imm̲` commutes with renaming. -/
theorem immG_rename : ∀ (A : MTy) (pay : Nat → MTy) (r : Nat → Nat), (∀ n, Cl 0 (pay n)) →
    immG b pay (rename r A) = rename r (immG b (pay ∘ r) A)
  | unit, _, _, _ => rfl
  | tensor A B, pay, r, h => by
      simp [immG, rename, immG_rename A pay r h, immG_rename B pay r h]
  | zero, _, _, _ => rfl
  | sum A B, pay, r, h => by
      simp [immG, rename, immG_rename A pay r h, immG_rename B pay r h]
  | thunk _, _, _, _ => rfl
  | ref A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | imm _ A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | «mut» _ A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | box _ A, pay, r, h => by simp [immG, rename, immG_rename A pay r h]
  | bang A, pay, r, h => by
      simp only [immG, rename, subst_rename]
      rw [rename_closed0 (Cl_subst A (pay ∘ r) (fun n => h (r n)))]
  | unk, _, _, _ => rfl
  | tvar _, _, _, _ => rfl
  | mu A, pay, r, h => by
      have hc : Cl 0 (subst pay (mu (rename (upR r) A))) := Cl_subst _ pay h
      simp only [immG, rename]
      rw [immG_rename A _ (upR r) (scons_closed hc h)]
      congr 3
      funext n
      cases n with
      | zero =>
          show subst pay (mu (rename (upR r) A)) = subst (pay ∘ r) (mu A)
          rw [← subst_rename]; rfl
      | succ n => rfl

/-- **`Imm̲` commutes with substitution**, for a closed payload substitution. -/
theorem immG_subst : ∀ (A : MTy) (pay σ : Nat → MTy), (∀ n, Cl 0 (pay n)) →
    immG b pay (subst σ A)
      = subst (fun n => immG b pay (σ n)) (immG b (fun n => subst pay (σ n)) A)
  | unit, _, _, _ => rfl
  | tensor A B, pay, σ, h => by
      simp [immG, subst, immG_subst A pay σ h, immG_subst B pay σ h]
  | zero, _, _, _ => rfl
  | sum A B, pay, σ, h => by
      simp [immG, subst, immG_subst A pay σ h, immG_subst B pay σ h]
  | thunk _, _, _, _ => rfl
  | ref A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | imm _ A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | «mut» _ A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | box _ A, pay, σ, h => by simp [immG, subst, immG_subst A pay σ h]
  | bang A, pay, σ, h => by
      simp only [immG, subst]
      rw [subst_closed0 (Cl_subst A (fun n => subst pay (σ n)) (fun n => Cl_subst (σ n) pay h)),
        subst_subst]
  | unk, _, _, _ => rfl
  | tvar _, _, _, _ => rfl
  | mu A, pay, σ, h => by
      have hc : Cl 0 (subst pay (mu (subst (upS σ) A))) := Cl_subst _ pay h
      have h₁ := scons_closed hc h
      show mu (immG b (scons (subst pay (mu (subst (upS σ) A))) pay) (subst (upS σ) A))
        = mu (subst (upS (fun n => immG b pay (σ n)))
            (immG b (scons (subst (fun n => subst pay (σ n)) (mu A)) (fun n => subst pay (σ n))) A))
      rw [immG_subst A _ (upS σ) h₁]
      have e₁ : (fun n => subst (scons (subst pay (mu (subst (upS σ) A))) pay) (upS σ n))
          = scons (subst (fun n => subst pay (σ n)) (mu A)) (fun n => subst pay (σ n)) := by
        funext n
        cases n with
        | zero =>
            show subst pay (mu (subst (upS σ) A)) = _
            rw [show mu (subst (upS σ) A) = subst σ (mu A) from rfl, subst_subst]; rfl
        | succ n =>
            show subst _ (rename Nat.succ (σ n)) = subst pay (σ n)
            rw [subst_rename]; rfl
      have e₂ : (fun n => immG b (scons (subst pay (mu (subst (upS σ) A))) pay) (upS σ n))
          = upS (fun n => immG b pay (σ n)) := by
        funext n
        cases n with
        | zero => rfl
        | succ n =>
            show immG b _ (rename Nat.succ (σ n)) = rename Nat.succ (immG b pay (σ n))
            rw [immG_rename b (σ n) _ Nat.succ h₁]; rfl
      rw [e₁, e₂]

/-- **The unrolling law at `μ`.** `Imm̲ 'b (T[μX.T/X]) = (Imm̲ᵡ 'b T)[Imm̲ 'b (μX.T)/Y]`. -/
theorem immReborrow_unroll {T : MTy} (hT : Cl 1 T) :
    immReb b (inst (mu T) T) = inst (immReb b (mu T)) (immX b T) := by
  have hdf : ∀ n, Cl 0 (dflt n) := fun _ => trivial
  have hmu : Cl 0 (mu T) := hT
  rw [immReb, inst, immG_subst b T dflt _ hdf, inst, immX]
  have e₁ : (fun n => subst dflt (scons (mu T) tvar n)) = scons (mu T) dflt := by
    funext n; cases n with
    | zero => exact subst_closed0 hmu dflt
    | succ n => rfl
  have e₂ : (fun n => immG b dflt (scons (mu T) tvar n)) = scons (immReb b (mu T)) tvar := by
    funext n; cases n <;> rfl
  rw [e₁, e₂]

/-- `Imm̲ 'b (μX.T) = μY. Imm̲ᵡ 'b T` on a closed `μ`. -/
theorem immReb_mu {T : MTy} (hT : Cl 1 T) : immReb b (mu T) = mu (immX b T) := by
  simp only [immReb, immG, immX, subst_closed0 (show Cl 0 (mu T) from hT)]

end

/-! ### The naive clause differs -/

/-- `Imm̲ 'b (μX.T) = μX. Imm̲ 'b T` with `Imm̲ 'b X = X`, payloads kept as written. -/
def naive (b : Lifetime.Life) : MTy → MTy
  | unit => unit
  | tensor A B => tensor (naive b A) (naive b B)
  | zero => zero
  | sum A B => sum (naive b A) (naive b B)
  | thunk _ => unk
  | ref A => imm b A
  | imm a A => imm a A
  | «mut» _ A => imm b A
  | box _ A => naive b A
  | bang A => bang A
  | unk => unk
  | tvar n => tvar n
  | mu A => mu (naive b A)

/-- `1 ⊕ (1 ⊗ Ref X)`. -/
def listT : MTy := sum unit (tensor unit (ref (tvar 0)))

/-- The boxed list `L = μX. 1 ⊕ (1 ⊗ Ref X)`. -/
def listL : MTy := mu listT

theorem listT_closed : Cl 1 listT := ⟨trivial, trivial, Nat.zero_lt_one⟩

/-- `Imm̲ 'b (T[L/X]) = 1 ⊕ (1 ⊗ Imm 'b L)`: the borrow of the tail has payload `L`. -/
theorem immReb_unroll_list (b : Lifetime.Life) :
    immReb b (inst listL listT) = sum unit (tensor unit (imm b listL)) := rfl

/-- The guarded clause: `Imm̲ 'b L = μY. 1 ⊕ (1 ⊗ Imm 'b L)`, with `Y` vacuous. -/
theorem immReb_list (b : Lifetime.Life) :
    immReb b listL = mu (sum unit (tensor unit (imm b listL))) := rfl

/-- **The naive clause differs at the boxed list.** Its unrolling claims a tail borrow of the
reborrowed type `μX. 1 ⊕ (1 ⊗ Imm 'b X)`, where the cell holds an `L`. -/
theorem naive_ne (b : Lifetime.Life) :
    inst (naive b listL) (naive b listT) ≠ immReb b (inst listL listT) := by
  rw [immReb_unroll_list]
  intro h
  simp only [inst, naive, listL, listT, subst, sum.injEq, tensor.injEq, imm.injEq,
    true_and] at h
  cases h

/-- The guarded clause's unrolling is `Imm̲ 'b (T[L/X])`, by `immReborrow_unroll`. -/
theorem guarded_eq (b : Lifetime.Life) :
    inst (immReb b listL) (immX b listT) = immReb b (inst listL listT) :=
  (immReborrow_unroll b listT_closed).symm

/-- The inline tree `μX. 1 ⊕ (X ⊗ X)`: the two clauses agree. -/
theorem tree_agree (b : Lifetime.Life) :
    immReb b (mu (sum unit (tensor (tvar 0) (tvar 0))))
      = naive b (mu (sum unit (tensor (tvar 0) (tvar 0)))) := rfl

/-! ### Agreement with CBPVWorld's `Imm̲` on `μ`-free closed types -/

/-- The `μ`-free, variable-free types, read as `VTy`. -/
def toV : MTy → Option VTy
  | unit => some .unit
  | tensor A B => (toV A).bind fun a => (toV B).map fun b => .tensor a b
  | zero => some .zero
  | sum A B => (toV A).bind fun a => (toV B).map fun b => .sum a b
  | thunk C => some (.thunk C)
  | ref A => (toV A).map .ref
  | imm a A => (toV A).map (.imm a)
  | «mut» a A => (toV A).map (.mut a)
  | box a A => (toV A).map (.box a)
  | bang A => (toV A).map .bang
  | unk => some .unk
  | tvar _ => none
  | mu _ => none

theorem Cl_of_toV : ∀ {A : MTy} {V : VTy}, toV A = some V → Cl 0 A
  | unit, _, _ => trivial
  | tensor A B, _, h => by
      simp only [toV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, b, hb, -⟩ := h
      exact ⟨(Cl_of_toV ha : Cl 0 A), (Cl_of_toV hb : Cl 0 B)⟩
  | zero, _, _ => trivial
  | sum A B, _, h => by
      simp only [toV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, b, hb, -⟩ := h
      exact ⟨(Cl_of_toV ha : Cl 0 A), (Cl_of_toV hb : Cl 0 B)⟩
  | thunk _, _, _ => trivial
  | ref A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, -⟩ := h; exact (Cl_of_toV ha : Cl 0 A)
  | imm _ A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, -⟩ := h; exact (Cl_of_toV ha : Cl 0 A)
  | «mut» _ A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, -⟩ := h; exact (Cl_of_toV ha : Cl 0 A)
  | box _ A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, -⟩ := h; exact (Cl_of_toV ha : Cl 0 A)
  | bang A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, -⟩ := h; exact (Cl_of_toV ha : Cl 0 A)
  | unk, _, _ => trivial
  | tvar _, _, h => by simp [toV] at h
  | mu _, _, h => by simp [toV] at h

/-- On `μ`-free closed types, `immG` at any payload substitution is `VTy.immReborrow`. -/
theorem toV_immG (b : Lifetime.Life) (pay : Nat → MTy) :
    ∀ {A : MTy} {V : VTy}, toV A = some V → toV (immG b pay A) = some (V.immReborrow b)
  | unit, _, h => by cases h; rfl
  | tensor A B, _, h => by
      simp only [toV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, c, hc, rfl⟩ := h
      simp [immG, toV, toV_immG b pay ha, toV_immG b pay hc, VTy.immReborrow]
  | zero, _, h => by cases h; rfl
  | sum A B, _, h => by
      simp only [toV, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, c, hc, rfl⟩ := h
      simp [immG, toV, toV_immG b pay ha, toV_immG b pay hc, VTy.immReborrow]
  | thunk _, _, h => by cases h; rfl
  | ref A, _, h => by
      have hA := h
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp [immG, toV, subst_closed0 (Cl_of_toV ha), ha, VTy.immReborrow]
  | imm _ A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp [immG, toV, subst_closed0 (Cl_of_toV ha), ha, VTy.immReborrow]
  | «mut» _ A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp [immG, toV, subst_closed0 (Cl_of_toV ha), ha, VTy.immReborrow]
  | box _ A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp [immG, toV_immG b pay ha, VTy.immReborrow]
  | bang A, _, h => by
      simp only [toV, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp [immG, toV, subst_closed0 (Cl_of_toV ha), ha, VTy.immReborrow]
  | unk, _, h => by cases h; rfl
  | tvar _, _, h => by simp [toV] at h
  | mu _, _, h => by simp [toV] at h

/-- On `μ`-free closed types, `immReb` is CBPVWorld's `Imm̲`. -/
theorem toV_immReb (b : Lifetime.Life) {A : MTy} {V : VTy} (h : toV A = some V) :
    toV (immReb b A) = some (V.immReborrow b) :=
  toV_immG b dflt h

end MTy

end BoCa.Fig16.LogRel.CBPVWorld.Recursion
