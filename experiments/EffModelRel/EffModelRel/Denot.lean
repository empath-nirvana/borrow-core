import EffModelRel.Tree

/-!
# EffModelRel — the denotation

Every term denotes, by structural recursion on the term: there is nothing for evaluation to get
stuck on, and no fuel.

- An instance environment maps instance variables to names.
- `handle` allocates its instance with `ν`, then folds its body into the model of its clauses.
- A resuming clause receives the continuation as `kty`: the pair `⟨resume, cancel⟩` when the
  operation may drop it (`cancel` runs its destructors), else `resume`.
- `lend` reads the cell, runs the body against the comodel with a fresh instance, and writes
  the state back.
- `bfix` is the `n`-th iterate of its body from the exhausted computation.
-/

namespace EffRel

variable {S : Sig}

/-- Value environments. -/
abbrev Env (Γ : List (VTy S)) : Type := (A : VTy S) → Var Γ A → A.den

def Env.nil : Env (S := S) [] := fun _ x => nomatch x

def Env.cons (a : A.den) (ρ : Env Γ) : Env (A :: Γ)
  | _, .z => a
  | _, .s x => ρ _ x

/-- Instance environments: each instance variable names an instance. -/
abbrev IEnv (Ψ : List S.E) : Type := (e : S.E) → Var Ψ e → Nat

def IEnv.nil : IEnv (S := S) [] := fun _ x => nomatch x

def IEnv.cons (i : Nat) (η : IEnv (S := S) Ψ) : IEnv (e :: Ψ)
  | _, .z => i
  | _, .s x => η _ x

/-- `n`-fold iteration. -/
def iter {X : Type} : Nat → (X → X) → X → X
  | 0, _, x => x
  | n + 1, f, x => f (iter n f x)

/-- The continuation a resuming clause receives. -/
def mkK : (b : Bool) → (q : Mode) → (r : G) → (C : CTy S) → (r.den → C.den) → Tree S Unit →
    (ktyB b q r C).den
  | true, _, _, _, k, t => (k, t)
  | false, _, _, _, k, _ => k

mutual
def Val.den : Val S Ψ Γ A → IEnv Ψ → Env Γ → A.den
  | .var x, _, ρ => ρ _ x
  | .unit, _, _ => ()
  | .int n, _, _ => n
  | .bool b, _, _ => b
  | .pair a b, η, ρ => (a.den η ρ, b.den η ρ)
  | .inl a, η, ρ => .inl (a.den η ρ)
  | .inr b, η, ρ => .inr (b.den η ρ)
  | .thunk _ M, η, ρ => M.den η ρ
  | .fold v, η, ρ => Strm.mk (v.den η ρ).1 (v.den η ρ).2

def Cmp.den : {C : CTy S} → Cmp S Ψ Γ C → IEnv Ψ → Env Γ → C.den
  | _, .ret v, η, ρ => .ret (v.den η ρ)
  | C, .bind M N, η, ρ => (M.den η ρ).bindC C (fun a => N.den η (ρ.cons a))
  | _, .lam M, η, ρ => fun a => M.den η (ρ.cons a)
  | _, .app M v, η, ρ => M.den η ρ (v.den η ρ)
  | _, .force v, η, ρ => v.den η ρ
  | _, .rcd M N, η, ρ => (M.den η ρ, N.den η ρ)
  | _, .prj1 M, η, ρ => (M.den η ρ).1
  | _, .prj2 M, η, ρ => (M.den η ρ).2
  | _, .split v M, η, ρ => M.den η ((ρ.cons (v.den η ρ).1).cons (v.den η ρ).2)
  | _, .case v M N, η, ρ =>
      match v.den η ρ with
      | .inl a => M.den η (ρ.cons a)
      | .inr b => N.den η (ρ.cons b)
  | _, .ite v M N, η, ρ =>
      match (v.den η ρ : Bool) with
      | true => M.den η ρ
      | false => N.den η ρ
  | _, .absurd v, η, ρ => (v.den η ρ : Empty).elim
  | _, .prim p a b, η, ρ => .ret (p.eval (a.den η ρ) (b.den η ρ))
  | _, .emit v, η, ρ => .act (.out (v.den η ρ)) (fun _ => .ret ())
  | C, .op x o v M, η, ρ => C.opA (η _ x) _ o (v.den η ρ) (fun y => M.den η (ρ.cons y)) []
  | C, .ab x a v, η, ρ => C.abA (η _ x) _ a (v.den η ρ) []
  | C, .handle e hr hop hab M, η, ρ =>
      C.nuA (fun i => (M.den (η.cons i) ρ).hnd C i e (fun a => hr.den η (ρ.cons a))
        (fun o v k d => (hop o).den η ((ρ.cons (A := .g _) v).cons (mkK _ _ _ C k (dtorsT d))))
        (fun a v => (hab a).den η (ρ.cons (A := .g _) v)))
  | C, .handleAt (e := e) x hr hop hab M, η, ρ =>
      (M.den η ρ).hnd C (η _ x) e (fun a => hr.den η (ρ.cons a))
        (fun o v k d => (hop o).den η ((ρ.cons (A := .g _) v).cons (mkK _ _ _ C k (dtorsT d))))
        (fun a v => (hab a).den η (ρ.cons (A := .g _) v))
  | C, .nu _ M, η, ρ => C.nuA (fun i => M.den (η.cons i) ρ)
  | _, .ieq x y, η, _ => .ret (decide (η _ x = η _ y))
  | _, .ilam M, η, ρ => fun i => M.den (η.cons i) ρ
  | _, .iapp M x, η, ρ => M.den η ρ (η _ x)
  | _, .newcap _ s co v, η, ρ =>
      .nu (fun c => .act (.new c ⟨s, v.den η ρ⟩)
        (fun _ => .ret (c, fun o a st => (co o).den IEnv.nil ((Env.nil.cons (A := .g _) a).cons (A := .g _) st))))
  | _, .getcap (s := s) v, η, ρ => .act (.kill (v.den η ρ).1 s) .ret
  | _, .lend (e := e) (s := s) v M, η, ρ =>
      .act (.rd (v.den η ρ).1 s) (fun st =>
        .nu (fun i => (M.den (η.cons i) ρ).runL i e (v.den η ρ).1 s (v.den η ρ).2 st))
  | _, .using ℓ M, η, ρ =>
      .nu (fun r => .act (.acq ℓ r) (fun _ => (M.den η (ρ.cons (ℓ, r))).addFin ℓ r))
  | _, .use v, η, ρ => .act (.use (v.den η ρ).1 (v.den η ρ).2) (fun _ => .ret ())
  | _, .unfold v, η, ρ =>
      match v.den η ρ with
      | .mk p d => (p, d)
  | C, .bfix x a v n M, η, ρ =>
      iter n (fun f => M.den η (ρ.cons f)) (C.abA (η _ x) _ a (v.den η ρ) [])
end

end EffRel
