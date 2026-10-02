import EffModelRel.Adequacy

/-!
# EffModelRel — renaming

Renaming of value and instance variables, and its semantics: a renamed term denotes the
original in the composed environments. The laws use it to weaken terms under binders.
-/

namespace EffRel

variable {S : Sig}

/-- A renaming of variables. -/
abbrev Ren {α : Type} (Γ Δ : List α) : Type := ∀ a, Var Γ a → Var Δ a

def Ren.id {α : Type} (Γ : List α) : Ren Γ Γ := fun _ x => x

def Ren.wk {α : Type} {Γ : List α} {b : α} : Ren Γ (b :: Γ) := fun _ x => .s x

def Ren.lift {α : Type} {Γ Δ : List α} {b : α} (r : Ren Γ Δ) : Ren (b :: Γ) (b :: Δ)
  | _, .z => .z
  | _, .s x => .s (r _ x)

/-- Exchange the two innermost variables. -/
def Ren.swap {α : Type} {Γ : List α} {a b : α} : Ren (a :: b :: Γ) (b :: a :: Γ)
  | _, .z => .s .z
  | _, .s .z => .z
  | _, .s (.s x) => .s (.s x)

mutual
def Val.ren (ri : Ren Ψ Ψ') (r : Ren Γ Δ) : Val S Ψ Γ A → Val S Ψ' Δ A
  | .var x => .var (r _ x)
  | .unit => .unit
  | .int n => .int n
  | .bool b => .bool b
  | .pair a b => .pair (a.ren ri r) (b.ren ri r)
  | .inl a => .inl (a.ren ri r)
  | .inr b => .inr (b.ren ri r)
  | .thunk m M => .thunk m (M.ren ri r)
  | .fold v => .fold (v.ren ri r)

def Cmp.ren (ri : Ren Ψ Ψ') (r : Ren Γ Δ) : Cmp S Ψ Γ C → Cmp S Ψ' Δ C
  | .ret v => .ret (v.ren ri r)
  | .bind M N => .bind (M.ren ri r) (N.ren ri r.lift)
  | .lam M => .lam (M.ren ri r.lift)
  | .app M v => .app (M.ren ri r) (v.ren ri r)
  | .force v => .force (v.ren ri r)
  | .rcd M N => .rcd (M.ren ri r) (N.ren ri r)
  | .prj1 M => .prj1 (M.ren ri r)
  | .prj2 M => .prj2 (M.ren ri r)
  | .split v M => .split (v.ren ri r) (M.ren ri r.lift.lift)
  | .case v M N => .case (v.ren ri r) (M.ren ri r.lift) (N.ren ri r.lift)
  | .ite v M N => .ite (v.ren ri r) (M.ren ri r) (N.ren ri r)
  | .absurd v => .absurd (v.ren ri r)
  | .prim p a b => .prim p (a.ren ri r) (b.ren ri r)
  | .emit v => .emit (v.ren ri r)
  | .op x o v M => .op (ri _ x) o (v.ren ri r) (M.ren ri r.lift)
  | .ab x a v => .ab (ri _ x) a (v.ren ri r)
  | .handle e b hr hop hab M => .handle e b (hr.ren ri r.lift) (fun o => (hop o).ren ri r.lift.lift)
      (fun a => (hab a).ren ri r.lift) (M.ren ri.lift r)
  | .handleAt x b hr hop hab M => .handleAt (ri _ x) b (hr.ren ri r.lift)
      (fun o => (hop o).ren ri r.lift.lift) (fun a => (hab a).ren ri r.lift) (M.ren ri r)
  | .nu e M => .nu e (M.ren ri.lift r)
  | .ieq x y => .ieq (ri _ x) (ri _ y)
  | .ilam M => .ilam (M.ren ri.lift r)
  | .iapp M x => .iapp (M.ren ri r) (ri _ x)
  | .newcap e s co v => .newcap e s co (v.ren ri r)
  | .getcap v => .getcap (v.ren ri r)
  | .lend v M => .lend (v.ren ri r) (M.ren ri.lift r)
  | .using ℓ M => .using ℓ (M.ren ri r.lift)
  | .use v => .use (v.ren ri r)
  | .unfold v => .unfold (v.ren ri r)
  | .bfix x a v n M => .bfix (ri _ x) a (v.ren ri r) n (M.ren ri r.lift)
end

/-- Weaken a computation by one value variable. -/
def Cmp.wk (M : Cmp S Ψ Γ C) : Cmp S Ψ (A :: Γ) C := M.ren (Ren.id Ψ) Ren.wk
def Val.wk (v : Val S Ψ Γ B) : Val S Ψ (A :: Γ) B := v.ren (Ren.id Ψ) Ren.wk
/-- Weaken a computation by one instance variable. -/
def Cmp.wkI (M : Cmp S Ψ Γ C) : Cmp S (e :: Ψ) Γ C := M.ren Ren.wk (Ren.id Γ)

/-! ## The semantics of renaming

A renamed term in an environment denotes the original term in the environment it induces. The
induced environments are given pointwise (`hη`, `hρ`), so no equation between environments is
ever rewritten. -/

theorem Env.lift_pt {A : VTy S} {r : Ren Γ Δ} {ρ : Env (S := S) Δ} {ρ₀ : Env Γ}
    (h : ∀ B x, ρ B (r B x) = ρ₀ B x) (a : A.den) :
    ∀ B x, (ρ.cons a) B (r.lift B x) = (ρ₀.cons a) B x := by
  intro B x; cases x with
  | z => rfl
  | s x => exact h _ x

theorem IEnv.lift_pt {e : S.E} {r : Ren Ψ Ψ'} {η : IEnv (S := S) Ψ'} {η₀ : IEnv Ψ}
    (h : ∀ e x, η e (r e x) = η₀ e x) (i : Nat) :
    ∀ e' x, (η.cons (e := e) i) e' (r.lift e' x) = (η₀.cons i) e' x := by
  intro e' x; cases x with
  | z => rfl
  | s x => exact h _ x

theorem iter_congr {X : Type} (n : Nat) {f g : X → X} (h : ∀ x, f x = g x) (x : X) :
    iter n f x = iter n g x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iter, ih, h]

mutual
theorem Val.den_ren (ri : Ren Ψ Ψ') (r : Ren Γ Δ) : (v : Val S Ψ Γ A) →
    ∀ (η : IEnv Ψ') (η₀ : IEnv Ψ) (ρ : Env Δ) (ρ₀ : Env Γ),
    (∀ e x, η e (ri e x) = η₀ e x) → (∀ B x, ρ B (r B x) = ρ₀ B x) →
    (v.ren ri r).den η ρ = v.den η₀ ρ₀
  | .var x, _, _, _, _, _, hρ => hρ _ x
  | .unit, _, _, _, _, _, _ => rfl
  | .int _, _, _, _, _, _, _ => rfl
  | .bool _, _, _, _, _, _, _ => rfl
  | .pair a b, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Val.ren, Val.den]
      rw [Val.den_ren ri r a η η₀ ρ ρ₀ hη hρ, Val.den_ren ri r b η η₀ ρ ρ₀ hη hρ]
  | .inl a, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Val.ren, Val.den]; rw [Val.den_ren ri r a η η₀ ρ ρ₀ hη hρ]
  | .inr b, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Val.ren, Val.den]; rw [Val.den_ren ri r b η η₀ ρ ρ₀ hη hρ]
  | .thunk _ M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Val.ren, Val.den]; exact Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ
  | .fold v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Val.ren, Val.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]

theorem Cmp.den_ren (ri : Ren Ψ Ψ') (r : Ren Γ Δ) : (M : Cmp S Ψ Γ C) →
    ∀ (η : IEnv Ψ') (η₀ : IEnv Ψ) (ρ : Env Δ) (ρ₀ : Env Γ),
    (∀ e x, η e (ri e x) = η₀ e x) → (∀ B x, ρ B (r B x) = ρ₀ B x) →
    (M.ren ri r).den η ρ = M.den η₀ ρ₀
  | .ret v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
  | .bind M N, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ]
      congr 1; funext a
      exact Cmp.den_ren ri r.lift N η η₀ _ _ hη (Env.lift_pt hρ a)
  | .lam M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; funext a
      exact Cmp.den_ren ri r.lift M η η₀ _ _ hη (Env.lift_pt hρ a)
  | .app M v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ, Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
  | .force v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; exact Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ
  | .rcd M N, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ, Cmp.den_ren ri r N η η₀ ρ ρ₀ hη hρ]
  | .prj1 M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ]
  | .prj2 M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ]
  | .split v M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
      exact Cmp.den_ren ri r.lift.lift M η η₀ _ _ hη (Env.lift_pt (Env.lift_pt hρ _) _)
  | .case v M N, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
      cases (v.den η₀ ρ₀ : _ ⊕ _) with
      | inl a => exact Cmp.den_ren ri r.lift M η η₀ _ _ hη (Env.lift_pt hρ a)
      | inr b => exact Cmp.den_ren ri r.lift N η η₀ _ _ hη (Env.lift_pt hρ b)
  | .ite v M N, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ, Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ,
        Cmp.den_ren ri r N η η₀ ρ ρ₀ hη hρ]
  | .absurd v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; exact (v.den η₀ ρ₀ : Empty).elim
  | .prim _ a b, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Val.den_ren ri r a η η₀ ρ ρ₀ hη hρ, Val.den_ren ri r b η η₀ ρ ρ₀ hη hρ]
  | .emit v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
  | .op x o v M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ, hη _ x]
      congr 1; funext y
      exact Cmp.den_ren ri r.lift M η η₀ _ _ hη (Env.lift_pt (A := .g _) hρ y)
  | .ab x a v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ, hη _ x]
  | .handle e _ hr hop hab M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      congr 1; funext i
      rw [Cmp.den_ren ri.lift r M _ _ ρ ρ₀ (IEnv.lift_pt hη i) hρ]
      congr 1
      · funext a; exact Cmp.den_ren ri r.lift hr η η₀ _ _ hη (Env.lift_pt hρ a)
      · funext o v k d
        exact Cmp.den_ren ri r.lift.lift (hop o) η η₀ _ _ hη (Env.lift_pt (Env.lift_pt hρ _) _)
      · funext a v; exact Cmp.den_ren ri r.lift (hab a) η η₀ _ _ hη (Env.lift_pt (A := .g _) hρ v)
  | .handleAt x _ hr hop hab M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ, hη _ x]
      congr 1
      · funext a; exact Cmp.den_ren ri r.lift hr η η₀ _ _ hη (Env.lift_pt hρ a)
      · funext o v k d
        exact Cmp.den_ren ri r.lift.lift (hop o) η η₀ _ _ hη (Env.lift_pt (Env.lift_pt hρ _) _)
      · funext a v; exact Cmp.den_ren ri r.lift (hab a) η η₀ _ _ hη (Env.lift_pt (A := .g _) hρ v)
  | .nu e M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      congr 1; funext i
      exact Cmp.den_ren ri.lift r M _ _ ρ ρ₀ (IEnv.lift_pt hη i) hρ
  | .ieq x y, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [hη _ x, hη _ y]
  | .ilam M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; funext i
      exact Cmp.den_ren ri.lift r M _ _ ρ ρ₀ (IEnv.lift_pt hη i) hρ
  | .iapp M x, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Cmp.den_ren ri r M η η₀ ρ ρ₀ hη hρ, hη _ x]
  | .newcap e s co v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
  | .getcap v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
  | .lend v M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
      congr 1; funext st; congr 1; funext i
      rw [Cmp.den_ren ri.lift r M _ _ ρ ρ₀ (IEnv.lift_pt hη i) hρ]
  | .using ℓ M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      congr 1; funext r'; congr 1; funext u
      exact congrArg (Tree.addFin ℓ r')
        (Cmp.den_ren ri r.lift M η η₀ _ _ hη (Env.lift_pt (A := .res) hρ (ℓ, r')))
  | .use v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
  | .unfold v, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]; rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ]
  | .bfix x a v n M, η, η₀, ρ, ρ₀, hη, hρ => by
      simp only [Cmp.ren, Cmp.den]
      rw [Val.den_ren ri r v η η₀ ρ ρ₀ hη hρ, hη _ x]
      exact iter_congr n (fun f => Cmp.den_ren ri r.lift M η η₀ _ _ hη
        (Env.lift_pt (A := .U Mode.unr _ _) hρ f)) _
end

theorem Cmp.den_wk {A : VTy S} (M : Cmp S Ψ Γ C) (η : IEnv Ψ) (ρ : Env Γ) (a : A.den) :
    (M.wk (A := A)).den η (ρ.cons a) = M.den η ρ :=
  Cmp.den_ren _ _ M _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

theorem Val.den_wk {A : VTy S} (v : Val S Ψ Γ B) (η : IEnv Ψ) (ρ : Env Γ) (a : A.den) :
    (v.wk (A := A)).den η (ρ.cons a) = v.den η ρ :=
  Val.den_ren _ _ v _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

theorem Cmp.den_wkI (M : Cmp S Ψ Γ C) (η : IEnv Ψ) (ρ : Env Γ) (i : Nat) :
    (M.wkI (e := e)).den (η.cons i) ρ = M.den η ρ :=
  Cmp.den_ren _ _ M _ _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

end EffRel
