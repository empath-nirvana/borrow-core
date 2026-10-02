import EffModelRel.Moded

/-!
# EffModelRel — the moded judgement

Phase A's typing (`EffModel/Typing.lean`) on the intrinsic terms, with the three rule changes of
`docs/effects-tr` §2.5. `VM L v` and `CM L R M`: the term consumes the linear variables `L` and
performs on the instances of the row `R`. The checks:

- **grades**: a linear variable is consumed exactly once on every path (masks are disjoint where
  phase A adds uses, equal where it takes the hull);
- **independence** at every capture point: a thunk at a mode with weakening or contraction, the
  rest of a `to`, an argument waiting while its function performs, an operation's continuation,
  and a handler's clauses capture no linear variable unless nothing performed meanwhile may be
  dropped or copied;
- **rows**: the row declared on a thunk, a function, a stream or a continuation covers what it
  performs, and forcing performs that row;
- **scope**: an instance bound by `handle`, `nu`, `lend` or `using` appears in no type outside
  its binder (`VTy.Sc`), and not in the binder's row;
- `[handle]` checks the clauses' captures at the handler's **own resuming qualifiers** as well as
  at the row it forwards (`LH.Empty ∨ ∀ o, (S.q e o).IsLin`; `docs/effects-tr` §10.3);
- `[lend]` **consumes** the capability and answers it back; the row the body forwards is linear
  (`docs/effects-tr` §10.1, rule `[lend]`), and the capability's effect has no abortive operation;
- `[using]` binds an instance of `Res`; nothing it forwards may be copied
  (`docs/effects-tr` §10.2, rule `[using]`).
-/

namespace EffRel

variable {S : Sig}

def VTy.isLin (A : VTy S) : Bool := decide (A.mode = Mode.lin)

mutual
inductive VM : {Ψ : List S.E} → {Γ : List (VTy S)} → {A : VTy S} → VSet Γ → Val S Ψ Γ A → Prop
  | var {A : VTy S} (x : Var Γ A) :
      VM (Ψ := Ψ) (if A.isLin then VSet.single x else VSet.none) (.var x)
  | unit : VM (Ψ := Ψ) (Γ := Γ) VSet.none .unit
  | int (n : Int) : VM (Ψ := Ψ) (Γ := Γ) VSet.none (.int n)
  | bool (b : Bool) : VM (Ψ := Ψ) (Γ := Γ) VSet.none (.bool b)
  | pair {L₁ L₂ : VSet Γ} {a : Val S Ψ Γ A} {b : Val S Ψ Γ B} :
      VM L₁ a → VM L₂ b → L₁.Disj L₂ → VM (L₁.union L₂) (.pair a b)
  | inl {L : VSet Γ} {a : Val S Ψ Γ A} : VM L a → VM L (.inl (B := B) a)
  | inr {L : VSet Γ} {b : Val S Ψ Γ B} : VM L b → VM L (.inr (A := A) b)
  | thunk {L : VSet Γ} {R : Row S Ψ} {C : CTy S} {M : Cmp S Ψ Γ C} (m : Mode) (b : Rw) :
      CM L R M → (m.w = true ∨ m.c = true → L.Empty) → R.Sub (b.row Ψ) →
      VM L (.thunk (b := b) m M)
  | fold {L : VSet Γ} {b : Rw} {A : VTy S} {v : Val S Ψ Γ (.U Mode.lin b (A.strmBody b))} :
      VM L v → VM L (.fold v)

inductive CM : {Ψ : List S.E} → {Γ : List (VTy S)} → {C : CTy S} → VSet Γ → Row S Ψ →
    Cmp S Ψ Γ C → Prop
  | ret {L : VSet Γ} {v : Val S Ψ Γ A} : VM L v → CM L Row.none (.ret v)
  | bind {L₁ L₂ : VSet Γ} {R₁ R₂ : Row S Ψ} {M : Cmp S Ψ Γ (.F A)} {N : Cmp S Ψ (A :: Γ) C} :
      CM L₁ R₁ M → CM (VSet.cons A.isLin L₂) R₂ N → L₁.Disj L₂ → (L₂.Empty ∨ R₁.mode.IsLin) →
      A.Sc Ψ.length → CM (L₁.union L₂) (R₁.union R₂) (.bind M N)
  | lam {L : VSet Γ} {R : Row S Ψ} {b : Rw} {M : Cmp S Ψ (A :: Γ) C} :
      CM (VSet.cons A.isLin L) R M → R.Sub (b.row Ψ) → CM L Row.none (.lam (b := b) M)
  | app {L₁ L₂ : VSet Γ} {R : Row S Ψ} {b : Rw} {M : Cmp S Ψ Γ (.arr A b C)} {v : Val S Ψ Γ A} :
      CM L₁ R M → VM L₂ v → L₁.Disj L₂ → (L₂.Empty ∨ R.mode.IsLin) →
      (CTy.arr A b C).Sc Ψ.length → CM (L₁.union L₂) (R.union (b.row Ψ)) (.app M v)
  | force {L : VSet Γ} {m : Mode} {b : Rw} {v : Val S Ψ Γ (.U m b C)} :
      VM L v → b.Sc Ψ.length → CM L (b.row Ψ) (.force v)
  | rcd {L : VSet Γ} {R₁ R₂ : Row S Ψ} {M : Cmp S Ψ Γ C} {N : Cmp S Ψ Γ D} :
      CM L R₁ M → CM L R₂ N → CM L (R₁.union R₂) (.rcd M N)
  | prj1 {L : VSet Γ} {R : Row S Ψ} {M : Cmp S Ψ Γ (.wth C D)} :
      CM L R M → D.Sc Ψ.length → CM L R (.prj1 M)
  | prj2 {L : VSet Γ} {R : Row S Ψ} {M : Cmp S Ψ Γ (.wth C D)} :
      CM L R M → C.Sc Ψ.length → CM L R (.prj2 M)
  | split {L₁ L₂ : VSet Γ} {R : Row S Ψ} {v : Val S Ψ Γ (.prod A B)} {M : Cmp S Ψ (B :: A :: Γ) C} :
      VM L₁ v → CM (VSet.cons B.isLin (VSet.cons A.isLin L₂)) R M → L₁.Disj L₂ →
      A.Sc Ψ.length → B.Sc Ψ.length → CM (L₁.union L₂) R (.split v M)
  | case {L₁ L₂ : VSet Γ} {R₁ R₂ : Row S Ψ} {v : Val S Ψ Γ (.sum A B)} {M : Cmp S Ψ (A :: Γ) C}
      {N : Cmp S Ψ (B :: Γ) C} :
      VM L₁ v → CM (VSet.cons A.isLin L₂) R₁ M → CM (VSet.cons B.isLin L₂) R₂ N → L₁.Disj L₂ →
      A.Sc Ψ.length → B.Sc Ψ.length → CM (L₁.union L₂) (R₁.union R₂) (.case v M N)
  | ite {L₁ L₂ : VSet Γ} {R₁ R₂ : Row S Ψ} {v : Val S Ψ Γ (.g .bool)} {M N : Cmp S Ψ Γ C} :
      VM L₁ v → CM L₂ R₁ M → CM L₂ R₂ N → L₁.Disj L₂ → CM (L₁.union L₂) (R₁.union R₂) (.ite v M N)
  | absurd {L₁ L : VSet Γ} {v : Val S Ψ Γ (.g .void)} : VM L₁ v → CM L Row.none (.absurd (C := C) v)
  | primAdd {L₁ L₂ : VSet Γ} {a b : Val S Ψ Γ (.g .int)} :
      VM L₁ a → VM L₂ b → L₁.Disj L₂ → CM (L₁.union L₂) Row.none (.prim .add a b)
  | primSub {L₁ L₂ : VSet Γ} {a b : Val S Ψ Γ (.g .int)} :
      VM L₁ a → VM L₂ b → L₁.Disj L₂ → CM (L₁.union L₂) Row.none (.prim .sub a b)
  | primLt {L₁ L₂ : VSet Γ} {a b : Val S Ψ Γ (.g .int)} :
      VM L₁ a → VM L₂ b → L₁.Disj L₂ → CM (L₁.union L₂) Row.none (.prim .lt a b)
  | primEq {L₁ L₂ : VSet Γ} {a b : Val S Ψ Γ (.g .int)} :
      VM L₁ a → VM L₂ b → L₁.Disj L₂ → CM (L₁.union L₂) Row.none (.prim .eq a b)
  | emit {L : VSet Γ} {v : Val S Ψ Γ (.g .int)} : VM L v → CM L Row.none (.emit v)
  | op {L₁ L₂ : VSet Γ} {R : Row S Ψ} {e : S.E} (x : Var Ψ e) (o : S.O e)
      {v : Val S Ψ Γ (.g (S.arg e o))} {M : Cmp S Ψ (.g (S.res e o) :: Γ) C} :
      VM L₁ v → CM (VSet.cons false L₂) R M → L₁.Disj L₂ → (L₂.Empty ∨ (S.q e o).IsLin) →
      CM (L₁.union L₂) ((Row.inst x).union R) (.op x o v M)
  | ab {L : VSet Γ} {e : S.E} (x : Var Ψ e) (a : S.A e) {v : Val S Ψ Γ (.g (S.aarg e a))} :
      VM L v → CM L (Row.inst x) (.ab (C := C) x a v)
  | handle (e : S.E) (bk : Rw) {LB LH : VSet Γ} {RB : Row S (e :: Ψ)} {Rcl : Row S Ψ}
      {hr : Cmp S Ψ (A :: Γ) C}
      {hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) bk (S.res e o) C :: .g (S.arg e o) :: Γ) C}
      {hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C} {B : Cmp S (e :: Ψ) Γ (.F A)} :
      CM LB RB B →
      (Rr : Row S Ψ) → CM (VSet.cons A.isLin LH) Rr hr → Rr.Sub Rcl →
      (Ro : S.O e → Row S Ψ) →
      (∀ o, CM (VSet.cons (kty (S.q e o) bk (S.res e o) C).isLin (VSet.cons false VSet.none))
        (Ro o) (hop o)) → (∀ o, (Ro o).Sub Rcl) →
      (Ra : S.A e → Row S Ψ) → (∀ a, CM (VSet.cons false LH) (Ra a) (hab a)) →
      (∀ a, (Ra a).Sub Rcl) →
      LB.Disj LH → (LH.Empty ∨ ∀ o, (S.q e o).IsLin) → (LH.Empty ∨ RB.tail.mode.IsLin) →
      (RB.tail.union Rcl).Sub (bk.row Ψ) → bk.Sc Ψ.length → A.Sc Ψ.length →
      CM (LB.union LH) (RB.tail.union Rcl) (.handle e bk hr hop hab B)
  | handleAt {LB LH : VSet Γ} {RB Rcl : Row S Ψ} {e : S.E} (x : Var Ψ e) (bk : Rw)
      {hr : Cmp S Ψ (A :: Γ) C}
      {hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) bk (S.res e o) C :: .g (S.arg e o) :: Γ) C}
      {hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C} {B : Cmp S Ψ Γ (.F A)} :
      CM LB RB B →
      (Rr : Row S Ψ) → CM (VSet.cons A.isLin LH) Rr hr → Rr.Sub Rcl →
      (Ro : S.O e → Row S Ψ) →
      (∀ o, CM (VSet.cons (kty (S.q e o) bk (S.res e o) C).isLin (VSet.cons false VSet.none))
        (Ro o) (hop o)) → (∀ o, (Ro o).Sub Rcl) →
      (Ra : S.A e → Row S Ψ) → (∀ a, CM (VSet.cons false LH) (Ra a) (hab a)) →
      (∀ a, (Ra a).Sub Rcl) →
      LB.Disj LH → (LH.Empty ∨ ∀ o, (S.q e o).IsLin) → (LH.Empty ∨ RB.mode.IsLin) →
      (RB.union Rcl).Sub (bk.row Ψ) → bk.Sc Ψ.length → A.Sc Ψ.length →
      CM (LB.union LH) (RB.union Rcl) (.handleAt x bk hr hop hab B)
  | nu (e : S.E) {L : VSet Γ} {R : Row S (e :: Ψ)} {M : Cmp S (e :: Ψ) Γ C} :
      CM L R M → R.v e .z = false → CM L R.tail (.nu e M)
  | ieq {e e' : S.E} (x : Var Ψ e) (y : Var Ψ e') : CM (Γ := Γ) VSet.none Row.none (.ieq x y)
  | ilam {L : VSet Γ} {R : Row S (e :: Ψ)} {M : Cmp S (e :: Ψ) Γ C} :
      CM L R M → CM L R.tail (.ilam M)
  | iapp {L : VSet Γ} {R : Row S Ψ} {M : Cmp S Ψ Γ (.pi e C)} (x : Var Ψ e) :
      CM L R M → CM L (R.union (Row.inst x)) (.iapp M x)
  | newcap {L : VSet Γ} (e : S.E) (s : G)
      {co : (o : S.O e) → Cmp S [] [.g s, .g (S.arg e o)] (.F (coRes S e s o))}
      {v : Val S Ψ Γ (.g s)} :
      VM L v → (S.A e → False) → (Rc : S.O e → Row S []) → (∀ o, CM VSet.none (Rc o) (co o)) →
      CM L Row.none (.newcap e s co v)
  | getcap {L : VSet Γ} {e : S.E} {s : G} {v : Val S Ψ Γ (.cap e s)} :
      VM L v → CM L Row.none (.getcap v)
  | lend {L₁ L₂ : VSet Γ} {R : Row S (e :: Ψ)} {s : G} {v : Val S Ψ Γ (.cap e s)}
      {M : Cmp S (e :: Ψ) Γ (.F A)} :
      VM L₁ v → CM L₂ R M → L₁.Disj L₂ → R.tail.mode.IsLin →
      CM (L₁.union L₂) R.tail (.lend v M)
  | using {L : VSet Γ} {R : Row S (S.Res :: Ψ)} (ℓ : Nat) {M : Cmp S (S.Res :: Ψ) Γ (.F A)} :
      CM L R M → R.tail.mode.c = false → CM L R.tail (.using ℓ M)
  | unfold {L : VSet Γ} {b : Rw} {A : VTy S} {v : Val S Ψ Γ (.strm b A)} :
      VM L v → b.Sc Ψ.length → CM L (b.row Ψ) (.unfold v)
  | bfix {R : Row S Ψ} {e : S.E} {b : Rw} (x : Var Ψ e) (a : S.A e)
      {v : Val S Ψ Γ (.g (S.aarg e a))} (n : Nat) {M : Cmp S Ψ (.U Mode.unr b C :: Γ) C} :
      VM VSet.none v → CM (VSet.cons false VSet.none) R M → ((Row.inst x).union R).Sub (b.row Ψ) →
      b.Sc Ψ.length → CM VSet.none ((Row.inst x).union R) (.bfix x a v n M)
end

end EffRel
