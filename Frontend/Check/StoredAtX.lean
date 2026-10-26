import Frontend.Check.KindsSound
import Frontend.Check.StoredShape

/-!
# Frontend — Check — the `StoredAtX` grammar of a stored clause  `[spec §54]`

A clause the checker classifies `stored` (`classifyClause`) keeps its continuation `κ`. R5 (the
scope's §3.B) turns the node into the ν anamorphism when every stored clause uses `κ` only to
produce the observations of the ν-values it answers: **`κ` only at `X`**. That is a property of the
clause's typed term, which the checker decides at `[handle]` (`storedAtXB`) and records on the
node (`TInfo.sshape`), as it records the clause kinds (`classifyHandler`).

**The answer is `P`-shaped.** For `P = νX. C` (`U X` is the type variable `0` in `C`), the
clause's answer type `R` is `Rx[U P/X]` (`VTy.inst`) for a template `Rx` that is `X`, `X` boxed
(`[@d] U P`: the answer is the ν-value, *machine-shaped*), or an observation leaf of `C` (the
answer is an observation's answer, *observation-shaped*). In both cases the clause's answer is a
value at the template `Rx`, and the ν-introductions that use `κ` sit at its `X` positions
(`PShaped`).

**The grammar** (`SX`), with `κ` in the slot `k`:

```
M ::= p ; M  |  case W {M | M}  |  let (y, z) = W; M  |  let () = W; M  |  return V     (κ not in p, W;
                                                                                  p performs nothing)
V ::= any value not using κ  |  (V, V) (κ in one)  |  inl V  |  inr V  |  boxed V  |  I   (I at X)
I ::= thunkv nu_in T                                                   (T at P's C)
T ::= T & T  |  λa. T  |  O                                            (the observation tree of C)
O ::= any observation not using κ  |  p ; O  |  κ' <- return κ; O   (κ' the new κ; κ unused)
    | (force κ).1 w                    (tail: the observation's answer is the template's)
    | t <- (force κ).1 w; N             (κ unused in N; t only where the leaf's template is Rx)
    | (force κ).2
N ::= p ; N  |  case W {N | N}  |  let (y, z) = W; N  |  let () = W; N  |  return V'  (t not in p, W)
V' ::= any value not using t  |  t, where the template is Rx  |  (V', V')  |  inl V'  |  inr V'  |  boxed V'
```

`κ` occurs at most once on each observation's path: two introductions in one pair cannot both
use it, and the alternatives of a `&` and of a `case` are different paths. The argument `w` of a
resume is a variable (the typed term's `app` takes one), computed by the prefix `p`. The aliases
`κ' <- return κ` include the boxed `κ` taken out (`return (unbox κ)`, whose term is `κ`'s),
as `classifyClause`'s rebinding does.

`storedAtXB_sound`: a clause the decider accepts is in the grammar, at a `P`-shaped answer.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.ClauseKinds

/-! ### `P`-shaped answers -/

/-- The value types of the observation leaves of a `&`-tree: `F A`'s `A`, through the layers of
an effectful observation `F_Σ A` and the argument of `A ⊸ D`. -/
def leavesOf : CTy → List VTy
  | .ret A => [A]
  | .amp C D => leavesOf C ++ leavesOf D
  | .arr _ D => leavesOf D
  | .eff _ _ _ _ _ _ _ D => leavesOf D
  | _ => []

/-- The value type an observation answers: `F A`'s `A`, through an effectful observation's
layers. -/
def leafOf : CTy → Option VTy
  | .ret A => some A
  | .eff _ _ _ _ _ _ _ D => leafOf D
  | _ => none

/-- **`R` is `P`-shaped** for `P = νX. C`, at the template `Rx`: `R = Rx[U P/X]`, and `Rx` is `X`,
`X` boxed, or an observation leaf of `C`. -/
def PShaped (R : VTy) (C : CTy) (Rx : VTy) : Prop :=
  VTy.inst (.thunk (.nu C)) Rx = R ∧
    (Rx = .tvar 0 ∨ (∃ a, Rx = .box a (.tvar 0)) ∨ Rx ∈ leavesOf C)

/-! ### The grammar -/

/-- **A computation that performs nothing**: it answers at `F A`, or is subsumed from the empty
row (`[sub]` of a computation at `F_∅`). -/
def pureB : TExpr → Bool
  | .effSub _ _ S _ _ _ => S.isEmpty
  | t => match t.jdg with
    | .comp (.ret _) => true
    | _ => false

/-- A position of the grammar: a clause's body answering at a template; a value at a template;
an observation tree at a `&`-tree; an observation at a leaf template; the rest `N[t]` after a
bound resume, at the leaf template; a value of `N[t]`'s answer at a template. -/
inductive SPos where
  | body (τ : VTy)
  | val (τ : VTy)
  | tree (D : CTy)
  | leaf (L : VTy)
  | after (L : VTy)
  | valT (τ : VTy)
  deriving DecidableEq

instance : Inhabited SPos := ⟨.val .unit⟩



/-- **The `StoredAtX` grammar** at the codata body `C` and the template `Rx`: `SX C Rx p k t`,
the term `t` at the position `p`, with `κ` (at `.after`, `.valT`: the resumed answer `t`) in the
slot `k`. -/
inductive SX (C : CTy) (Rx : VTy) : SPos → Nat → TExpr → Prop where
  -- `M`
  | bodyRet {τ k i j A v} : SX C Rx (.val τ) k v → SX C Rx (.body τ) k (.ret i j A v)
  | bodySumE {τ k i j A B D u tV t₁ t₂} : mentions k tV.erase = false →
      SX C Rx (.body τ) (k + 1) t₁ → SX C Rx (.body τ) (k + 1) t₂ →
      SX C Rx (.body τ) k (.sumE i j A B D u tV t₁ t₂)
  | bodyTensorE {τ k i j A B D u tV tM} : mentions k tV.erase = false →
      SX C Rx (.body τ) (k + 2) tM → SX C Rx (.body τ) k (.tensorE i j A B D u tV tM)
  | bodyUnitE {τ k i j D u tV tM} : mentions k tV.erase = false →
      SX C Rx (.body τ) k tM → SX C Rx (.body τ) k (.unitE i j D u tV tM)
  | bodyBind {τ k i j A D u tM tN} : mentions k tM.erase = false → pureB tM = true →
      SX C Rx (.body τ) (k + 1) tN → SX C Rx (.body τ) k (.bind i j A D u tM tN)
  | bodyLet {τ k i j A B S u tM tN} : mentions k tM.erase = false → pureB tM = true →
      SX C Rx (.body τ) (k + 1) tN → SX C Rx (.body τ) k (.effLet i j A B S u tM tN)
  | bodySub {τ k i j S S' A t} : SX C Rx (.body τ) k t → SX C Rx (.body τ) k (.effSub i j S S' A t)
  -- `V`
  | valFree {τ k t} : mentions k t.erase = false → SX C Rx (.val τ) k t
  | valPair {A B k i j A' B' u v₁ v₂} : SX C Rx (.val A) k v₁ → SX C Rx (.val B) k v₂ →
      (mentions k v₁.erase = false ∨ mentions k v₂.erase = false) →
      SX C Rx (.val (.tensor A B)) k (.tensorI i j A' B' u v₁ v₂)
  | valInl {A B k i j A' B' v} : SX C Rx (.val A) k v →
      SX C Rx (.val (.sum A B)) k (.sumI₁ i j A' B' v)
  | valInr {A B k i j A' B' v} : SX C Rx (.val B) k v →
      SX C Rx (.val (.sum A B)) k (.sumI₂ i j A' B' v)
  | valBox {a τ k i j a' A v} : SX C Rx (.val τ) k v →
      SX C Rx (.val (.box a τ)) k (.boxI i j a' A v)
  | valIntro {k i j D i' j' t} : SX C Rx (.tree C) k t →
      SX C Rx (.val (.tvar 0)) k (.thunkV i j D (.nuIn i' j' C t))
  -- `T`
  | treeAmp {D₁ D₂ k i j E₁ E₂ t₁ t₂} : SX C Rx (.tree D₁) (k + 2) t₁ →
      SX C Rx (.tree D₂) (k + 2) t₂ → SX C Rx (.tree (.amp D₁ D₂)) k (.withI i j E₁ E₂ t₁ t₂)
  | treeArr {A D k i j A' E t} : SX C Rx (.tree D) (k + 1) t →
      SX C Rx (.tree (.arr A D)) k (.lam i j A' E t)
  | treeLeaf {D L k t} : leafOf D = some L → SX C Rx (.leaf L) k t → SX C Rx (.tree D) k t
  -- `O`
  | leafFree {L k t} : mentions k t.erase = false → SX C Rx (.leaf L) k t
  | leafBind {L k i j A D u tM tN} : mentions k tM.erase = false →
      SX C Rx (.leaf L) (k + 1) tN → SX C Rx (.leaf L) k (.bind i j A D u tM tN)
  | leafLet {L k i j A B S u tM tN} : mentions k tM.erase = false →
      SX C Rx (.leaf L) (k + 1) tN → SX C Rx (.leaf L) k (.effLet i j A B S u tM tN)
  | leafAlias {L k i j A D u tM tN} : tM.erase = .var k → mentions (k + 1) tN.erase = false →
      SX C Rx (.leaf L) 0 tN → SX C Rx (.leaf L) k (.bind i j A D u tM tN)
  | leafAliasLet {L k i j A B S u tM tN} : tM.erase = .var k → mentions (k + 1) tN.erase = false →
      SX C Rx (.leaf L) 0 tN → SX C Rx (.leaf L) k (.effLet i j A B S u tM tN)
  | leafResume {L k t} : resumeB k t = true → L = Rx → SX C Rx (.leaf L) k t
  | leafResumeTo {L k i j A D u tM tN} : resumeB k tM = true → mentions (k + 1) tN.erase = false →
      SX C Rx (.after L) 0 tN → SX C Rx (.leaf L) k (.bind i j A D u tM tN)
  | leafResumeLet {L k i j A B S u tM tN} : resumeB k tM = true →
      mentions (k + 1) tN.erase = false → SX C Rx (.after L) 0 tN →
      SX C Rx (.leaf L) k (.effLet i j A B S u tM tN)
  | leafClose {L k t} : cancelHeadB k t = true → SX C Rx (.leaf L) k t
  | leafSub {L k i j S S' A t} : SX C Rx (.leaf L) k t → SX C Rx (.leaf L) k (.effSub i j S S' A t)
  -- `N`
  | afterRet {L k i j A v} : SX C Rx (.valT L) k v → SX C Rx (.after L) k (.ret i j A v)
  | afterBind {L k i j A D u tM tN} : mentions k tM.erase = false →
      SX C Rx (.after L) (k + 1) tN → SX C Rx (.after L) k (.bind i j A D u tM tN)
  | afterLet {L k i j A B S u tM tN} : mentions k tM.erase = false →
      SX C Rx (.after L) (k + 1) tN → SX C Rx (.after L) k (.effLet i j A B S u tM tN)
  | afterSumE {L k i j A B D u tV t₁ t₂} : mentions k tV.erase = false →
      SX C Rx (.after L) (k + 1) t₁ → SX C Rx (.after L) (k + 1) t₂ →
      SX C Rx (.after L) k (.sumE i j A B D u tV t₁ t₂)
  | afterTensorE {L k i j A B D u tV tM} : mentions k tV.erase = false →
      SX C Rx (.after L) (k + 2) tM → SX C Rx (.after L) k (.tensorE i j A B D u tV tM)
  | afterUnitE {L k i j D u tV tM} : mentions k tV.erase = false →
      SX C Rx (.after L) k tM → SX C Rx (.after L) k (.unitE i j D u tV tM)
  | afterSub {L k i j S S' A t} : SX C Rx (.after L) k t →
      SX C Rx (.after L) k (.effSub i j S S' A t)
  -- `V'`
  | valTFree {τ k t} : mentions k t.erase = false → SX C Rx (.valT τ) k t
  | valTHole {k i j A} : SX C Rx (.valT Rx) k (.var i j k A)
  | valTPair {A B k i j A' B' u v₁ v₂} : SX C Rx (.valT A) k v₁ → SX C Rx (.valT B) k v₂ →
      SX C Rx (.valT (.tensor A B)) k (.tensorI i j A' B' u v₁ v₂)
  | valTInl {A B k i j A' B' v} : SX C Rx (.valT A) k v →
      SX C Rx (.valT (.sum A B)) k (.sumI₁ i j A' B' v)
  | valTInr {A B k i j A' B' v} : SX C Rx (.valT B) k v →
      SX C Rx (.valT (.sum A B)) k (.sumI₂ i j A' B' v)
  | valTBox {a τ k i j a' A v} : SX C Rx (.valT τ) k v →
      SX C Rx (.valT (.box a τ)) k (.boxI i j a' A v)

/-- The body `M` of a control clause `!thunkv λp. let (x, κ) = p; M`, `κ` in its slot `0` (as
`classifyClause` reads it). -/
def clauseBody? (c : TExpr) : Option TExpr :=
  match c.unUse with
  | .bangThunkV _ _ _ (.lam _ _ _ _ (.tensorE _ _ _ _ _ _ (.var _ _ 0 _) tM)) => some tM
  | _ => none

/-- **A stored clause is in the `StoredAtX` grammar** at `P = νX. C` and the template `Rx`: its
body, `κ` in the slot `0`, answers a value at `Rx`. -/
def StoredAtXC (C : CTy) (Rx : VTy) (c : TExpr) : Prop :=
  ∃ tM, clauseBody? c = some tM ∧ SX C Rx (.body Rx) 0 tM

/-- **`StoredAtX`**: the clause `c` of a handler answering `R` is in the grammar, at a codata type
its answer is shaped by. -/
def StoredAtX (R : VTy) (c : TExpr) : Prop :=
  ∃ C Rx, PShaped R C Rx ∧ StoredAtXC C Rx c

/-! ### The decider -/

/-- The position of an observation tree at `D`: an observation, at a leaf; a tree otherwise. -/
def treePos (D : CTy) : SPos :=
  match leafOf D with
  | some L => .leaf L
  | none => .tree D

theorem SX.ofTreePos {C : CTy} {Rx : VTy} {D : CTy} {k : Nat} {t : TExpr}
    (h : SX C Rx (treePos D) k t) : SX C Rx (.tree D) k t := by
  unfold treePos at h
  split at h
  · exact .treeLeaf (by assumption) h
  · exact h

/-- `SX`, decided by structural recursion on the term. -/
def sxB (C : CTy) (Rx : VTy) : SPos → Nat → TExpr → Bool
  -- `M`
  | .body τ, k, .ret _ _ _ v => sxB C Rx (.val τ) k v
  | .body τ, k, .sumE _ _ _ _ _ _ tV t₁ t₂ =>
      !mentions k tV.erase && sxB C Rx (.body τ) (k + 1) t₁ && sxB C Rx (.body τ) (k + 1) t₂
  | .body τ, k, .tensorE _ _ _ _ _ _ tV tM => !mentions k tV.erase && sxB C Rx (.body τ) (k + 2) tM
  | .body τ, k, .unitE _ _ _ _ tV tM => !mentions k tV.erase && sxB C Rx (.body τ) k tM
  | .body τ, k, .bind _ _ _ _ _ tM tN =>
      !mentions k tM.erase && pureB tM && sxB C Rx (.body τ) (k + 1) tN
  | .body τ, k, .effLet _ _ _ _ _ _ tM tN =>
      !mentions k tM.erase && pureB tM && sxB C Rx (.body τ) (k + 1) tN
  | .body τ, k, .effSub _ _ _ _ _ t => sxB C Rx (.body τ) k t
  | .body _, _, _ => false
  -- `V`
  | .val τ, k, t@(.tensorI _ _ _ _ _ v₁ v₂) =>
      !mentions k t.erase || match τ with
        | .tensor A B => sxB C Rx (.val A) k v₁ && sxB C Rx (.val B) k v₂ &&
            (!mentions k v₁.erase || !mentions k v₂.erase)
        | _ => false
  | .val τ, k, t@(.sumI₁ _ _ _ _ v) =>
      !mentions k t.erase || match τ with
        | .sum A _ => sxB C Rx (.val A) k v
        | _ => false
  | .val τ, k, t@(.sumI₂ _ _ _ _ v) =>
      !mentions k t.erase || match τ with
        | .sum _ B => sxB C Rx (.val B) k v
        | _ => false
  | .val τ, k, t@(.boxI _ _ _ _ v) =>
      !mentions k t.erase || match τ with
        | .box _ τ' => sxB C Rx (.val τ') k v
        | _ => false
  | .val τ, k, t@(.thunkV _ _ _ (.nuIn _ _ C' t')) =>
      !mentions k t.erase || (τ == .tvar 0 && C' == C && sxB C Rx (treePos C) k t')
  | .val _, k, t => !mentions k t.erase
  -- `T`
  | .tree D, k, .withI _ _ _ _ t₁ t₂ =>
      match D with
      | .amp D₁ D₂ => sxB C Rx (treePos D₁) (k + 2) t₁ && sxB C Rx (treePos D₂) (k + 2) t₂
      | _ => false
  | .tree D, k, .lam _ _ _ _ t' =>
      match D with
      | .arr _ D' => sxB C Rx (treePos D') (k + 1) t'
      | _ => false
  | .tree _, _, _ => false
  -- `O`
  | .leaf L, k, t@(.bind _ _ _ _ _ tM tN) =>
      !mentions k t.erase ||
      (!mentions k tM.erase && sxB C Rx (.leaf L) (k + 1) tN) ||
      (isVarB k tM.erase && !mentions (k + 1) tN.erase && sxB C Rx (.leaf L) 0 tN) ||
      (resumeB k tM && !mentions (k + 1) tN.erase && sxB C Rx (.after L) 0 tN) ||
      (resumeB k t && L == Rx) || cancelHeadB k t
  | .leaf L, k, t@(.effLet _ _ _ _ _ _ tM tN) =>
      !mentions k t.erase ||
      (!mentions k tM.erase && sxB C Rx (.leaf L) (k + 1) tN) ||
      (isVarB k tM.erase && !mentions (k + 1) tN.erase && sxB C Rx (.leaf L) 0 tN) ||
      (resumeB k tM && !mentions (k + 1) tN.erase && sxB C Rx (.after L) 0 tN) ||
      (resumeB k t && L == Rx) || cancelHeadB k t
  | .leaf L, k, t@(.effSub _ _ _ _ _ t') =>
      !mentions k t.erase || sxB C Rx (.leaf L) k t' || (resumeB k t && L == Rx) ||
        cancelHeadB k t
  | .leaf L, k, t => !mentions k t.erase || (resumeB k t && L == Rx) || cancelHeadB k t
  -- `N`
  | .after L, k, .ret _ _ _ v => sxB C Rx (.valT L) k v
  | .after L, k, .bind _ _ _ _ _ tM tN => !mentions k tM.erase && sxB C Rx (.after L) (k + 1) tN
  | .after L, k, .effLet _ _ _ _ _ _ tM tN =>
      !mentions k tM.erase && sxB C Rx (.after L) (k + 1) tN
  | .after L, k, .sumE _ _ _ _ _ _ tV t₁ t₂ =>
      !mentions k tV.erase && sxB C Rx (.after L) (k + 1) t₁ && sxB C Rx (.after L) (k + 1) t₂
  | .after L, k, .tensorE _ _ _ _ _ _ tV tM =>
      !mentions k tV.erase && sxB C Rx (.after L) (k + 2) tM
  | .after L, k, .unitE _ _ _ _ tV tM => !mentions k tV.erase && sxB C Rx (.after L) k tM
  | .after L, k, .effSub _ _ _ _ _ t => sxB C Rx (.after L) k t
  | .after _, _, _ => false
  -- `V'`
  | .valT τ, k, t@(.var _ _ i _) => !mentions k t.erase || (τ == Rx && i == k)
  | .valT τ, k, t@(.tensorI _ _ _ _ _ v₁ v₂) =>
      !mentions k t.erase || match τ with
        | .tensor A B => sxB C Rx (.valT A) k v₁ && sxB C Rx (.valT B) k v₂
        | _ => false
  | .valT τ, k, t@(.sumI₁ _ _ _ _ v) =>
      !mentions k t.erase || match τ with
        | .sum A _ => sxB C Rx (.valT A) k v
        | _ => false
  | .valT τ, k, t@(.sumI₂ _ _ _ _ v) =>
      !mentions k t.erase || match τ with
        | .sum _ B => sxB C Rx (.valT B) k v
        | _ => false
  | .valT τ, k, t@(.boxI _ _ _ _ v) =>
      !mentions k t.erase || match τ with
        | .box _ τ' => sxB C Rx (.valT τ') k v
        | _ => false
  | .valT _, k, t => !mentions k t.erase

theorem isVarB_eq {k : Nat} {e : Expr} (h : isVarB k e = true) : e = .var k := by
  unfold isVarB at h; split at h <;> simp_all

/-- **The decider is sound**: a term it accepts at a position is in the grammar there. -/
theorem sxB_sound (C : CTy) (Rx : VTy) (p : SPos) (k : Nat) (t : TExpr)
    (h : sxB C Rx p k t = true) : SX C Rx p k t := by
  fun_induction sxB C Rx p k t <;>
    (try simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
      Bool.false_eq_true] at h)
  all_goals repeat
    first
    | contradiction
    | (simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h)
    | (split at h)
  all_goals (try casesm* _ ∧ _, _ ∨ _)
  all_goals (try simp only [Bool.false_eq_true] at *)
  all_goals (try contradiction)
  all_goals (try subst_vars)
  all_goals first
    | exact .valFree ‹_›
    | exact .leafFree ‹_›
    | exact .valTFree ‹_›
    | exact .leafClose ‹_›
    | (apply SX.leafResume <;> first | assumption | rfl)
    | (apply SX.bodyRet <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.bodySumE <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.bodyTensorE <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.bodyUnitE <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.bodyBind <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.bodyLet <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.bodySub <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valPair <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valInl <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valInr <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valBox <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valIntro <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.treeAmp <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.treeArr <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafBind <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafLet <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafAlias <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafAliasLet <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafResume <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafResumeTo <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafResumeLet <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafClose <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.leafSub <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.afterRet <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.afterBind <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.afterLet <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.afterSumE <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.afterTensorE <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.afterUnitE <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.afterSub <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | apply SX.valTHole
    | (apply SX.valTPair <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valTInl <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valTInr <;> solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])
    | (apply SX.valTBox; solve_by_elim (maxDepth := 5) [isVarB_eq, SX.ofTreePos, Or.inl, Or.inr])

/-! ### The clause's answer, shaped by a codata type -/

/-- The bodies `C` of the codata types `U (νX. C)` an answer type holds at value level, outside
recursive types. -/
def nuCands : VTy → List CTy
  | .thunk (.nu C) => [C]
  | .tensor A B | .sum A B => nuCands A ++ nuCands B
  | .box _ A | .ref A | .imm _ A | .mut _ A | .bang A | .fam A => nuCands A
  | _ => []

/-- The templates an answer `R` may have at `C`: `X`, `X` boxed as `R` is, `C`'s observation
leaves. -/
def rxCands (R : VTy) (C : CTy) : List VTy :=
  .tvar 0 :: ((match R with
    | .box a _ => [.box a (.tvar 0)]
    | _ => []) ++ leavesOf C)

/-- The codata bodies and templates `R` is shaped by (`PShaped`), in order. -/
def pshapes (R : VTy) : List (CTy × VTy) :=
  (nuCands R).flatMap fun C =>
    ((rxCands R C).filter fun Rx => VTy.inst (.thunk (.nu C)) Rx == R).map (C, ·)

theorem mem_pshapes {R : VTy} {C : CTy} {Rx : VTy} (h : (C, Rx) ∈ pshapes R) : PShaped R C Rx := by
  simp only [pshapes, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq,
    Prod.mk.injEq] at h
  obtain ⟨C', _, Rx', ⟨hm, he⟩, rfl, rfl⟩ := h
  refine ⟨he, ?_⟩
  simp only [rxCands, List.mem_cons, List.mem_append] at hm
  rcases hm with hm | hm | hm
  · exact .inl hm
  · split at hm
    · simp only [List.mem_singleton] at hm; exact .inr (.inl ⟨_, hm⟩)
    · simp at hm
  · exact .inr (.inr hm)

/-- **The codata type and template a stored clause is in the grammar at**: the first `P`-shape of
the answer `R` (`pshapes`) at which the clause's body is (`sxB`). -/
def storedAt? (R : VTy) (c : TExpr) : Option (CTy × VTy) := do
  let tM ← clauseBody? c
  (pshapes R).find? fun (C, Rx) => sxB C Rx (.body Rx) 0 tM

theorem storedAt?_sound {R : VTy} {c : TExpr} {C : CTy} {Rx : VTy}
    (h : storedAt? R c = some (C, Rx)) : PShaped R C Rx ∧ StoredAtXC C Rx c := by
  unfold storedAt? at h
  cases hb : clauseBody? c with
  | none => simp [hb] at h
  | some tM =>
    simp only [hb, Option.bind_eq_bind, Option.bind_some] at h
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    exact ⟨mem_pshapes hm, tM, hb, sxB_sound C Rx _ 0 tM hp⟩

/-- **`StoredAtX`, decided** (the scope's `storedAtXB`): the clause `c` of a handler answering `R`
is in the grammar at a codata type its answer is shaped by. -/
def storedAtXB (R : VTy) (c : TExpr) : Bool := (storedAt? R c).isSome

/-- **`storedAtXB` is sound.** -/
theorem storedAtXB_sound {R : VTy} {c : TExpr} (h : storedAtXB R c = true) : StoredAtX R c := by
  unfold storedAtXB at h
  obtain ⟨⟨C, Rx⟩, hs⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨hP, hX⟩ := storedAt?_sound hs
  exact ⟨C, Rx, hP, hX⟩

/-! ### The record -/

/-- The variables free in `e` at or above the binder depth `d`, less `d`. -/
def fvsAt : Expr → Nat → List Nat
  | .var i, d => if d ≤ i then [i - d] else []
  | .unit, _ | .loc _, _ | .prim _, _ => []
  | .pair a b, d | .seq a b, d | .app a b, d => fvsAt a d ++ fvsAt b d
  | .inj₁ a, d | .inj₂ a, d => fvsAt a d
  | .lam b, d => fvsAt b (d + 1)
  | .letpair a b, d => fvsAt a d ++ fvsAt b (d + 2)
  | .case e a b, d => fvsAt e d ++ fvsAt a (d + 1) ++ fvsAt b (d + 1)

/-- The production an observation is in, `κ` in the slot `k`: through its prefixes and the
aliases of `κ`, a resume in tail position or bound, a close, or `κ`-free. -/
def obsOf : Nat → TExpr → SObs
  | k, t@(.bind _ _ _ _ _ tM tN) | k, t@(.effLet _ _ _ _ _ _ tM tN) =>
    if !mentions k t.erase then .free
    else if resumeB k t then .resume true
    else if cancelHeadB k t then .close
    else if resumeB k tM then .resume false
    else if isVarB k tM.erase then obsOf 0 tN
    else obsOf (k + 1) tN
  | k, t@(.effSub _ _ _ _ _ t') =>
    if !mentions k t.erase then .free
    else if resumeB k t then .resume true
    else if cancelHeadB k t then .close
    else obsOf k t'
  | k, t =>
    if !mentions k t.erase then .free
    else if resumeB k t then .resume true
    else .close

/-- The productions of the observations of a tree at `D`, in the tree's order. -/
def obsTree : CTy → Nat → TExpr → List SObs
  | .amp D₁ D₂, k, .withI _ _ _ _ t₁ t₂ => obsTree D₁ (k + 2) t₁ ++ obsTree D₂ (k + 2) t₂
  | .arr _ D, k, .lam _ _ _ _ t => obsTree D (k + 1) t
  | _, k, t => [obsOf k t]

/-- The ν-introductions of `C` at the `X` positions of a value at the template `τ`: each with its
path, its box, its captures (the slots below `e`, `κ` in `k` excepted), how many slots at or above
`e` (the clauses' context) it uses, and its observations. -/
def introsVal (C : CTy) : VTy → Nat → Nat → Option Lifetime.Life → List Nat → TExpr → List SIntro
  | .tvar 0, k, e, bx, path, t@(.thunkV _ _ _ (.nuIn _ _ C' t')) =>
    if C' == C then
      let fv := (fvsAt t.erase 0).eraseDups
      [{ path, boxed := bx, caps := fv.filter (fun i => i < e && i != k),
         env := (fv.filter (e ≤ ·)).length, obs := obsTree C k t' }]
    else []
  | .box a τ, k, e, _, path, .boxI _ _ _ _ v => introsVal C τ k e (some a) (path ++ [0]) v
  | .tensor A B, k, e, _, path, .tensorI _ _ _ _ _ v₁ v₂ =>
    introsVal C A k e none (path ++ [0]) v₁ ++ introsVal C B k e none (path ++ [1]) v₂
  | .sum A _, k, e, _, path, .sumI₁ _ _ _ _ v => introsVal C A k e none (path ++ [0]) v
  | .sum _ B, k, e, _, path, .sumI₂ _ _ _ _ v => introsVal C B k e none (path ++ [0]) v
  | _, _, _, _, _, _ => []

/-- The ν-introductions of a clause's body answering at the template `τ`, `κ` in the slot `k`,
the clauses' context from the slot `e`: through its prefixes and branches to the values it
answers. -/
def introsBody (C : CTy) (τ : VTy) : Nat → Nat → List Nat → TExpr → List SIntro
  | k, e, path, .ret _ _ _ v => introsVal C τ k e none (path ++ [0]) v
  | k, e, path, .sumE _ _ _ _ _ _ _ t₁ t₂ =>
    introsBody C τ (k + 1) (e + 1) (path ++ [1]) t₁ ++ introsBody C τ (k + 1) (e + 1) (path ++ [2]) t₂
  | k, e, path, .tensorE _ _ _ _ _ _ _ tM => introsBody C τ (k + 2) (e + 2) (path ++ [1]) tM
  | k, e, path, .unitE _ _ _ _ _ tM => introsBody C τ k e (path ++ [1]) tM
  | k, e, path, .bind _ _ _ _ _ _ tN | k, e, path, .effLet _ _ _ _ _ _ _ tN =>
    introsBody C τ (k + 1) (e + 1) (path ++ [1]) tN
  | k, e, path, .effSub _ _ _ _ _ t => introsBody C τ k e (path ++ [0]) t
  | _, _, _, _ => []

/-- **The record of a stored clause's derivation** (`TInfo.sshape`), where `storedAt?` finds one:
its codata body, template, shape and ν-introductions. In the body, `κ` is the slot `0`, `x` the
slot `1`, the clause's argument pair the slot `2`, and the clauses' context begins at the slot
`3`. -/
def sshapeOf (R : VTy) (c : TExpr) : Option SShape := do
  let (C, Rx) ← storedAt? R c
  let tM ← clauseBody? c
  let machine := match Rx with
    | .tvar 0 | .box _ (.tvar 0) => true
    | _ => false
  pure { C, Rx, machine, intros := introsBody C Rx 0 3 [] tM }

theorem sshapeOf_sound {R : VTy} {c : TExpr} {sh : SShape} (h : sshapeOf R c = some sh) :
    PShaped R sh.C sh.Rx ∧ StoredAtXC sh.C sh.Rx c := by
  unfold sshapeOf at h
  cases hs : storedAt? R c with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨C, Rx⟩ := p
    cases hb : clauseBody? c with
    | none => simp [hs, hb] at h
    | some tM =>
      simp only [hs, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact storedAt?_sound hs

/-- The clause of the operation `j` that a `handle` node's own pair `tH` holds (`clauseParts`). -/
def nodeClause (E : List (Count × VTy × VTy)) (tH : TExpr) (j : Nat) : Option TExpr :=
  let parts := match tH with
    | .tensorI _ _ _ _ _ _ tc => clauseParts E.length tc
    | _ => List.replicate E.length none
  (parts[j]?).join

theorem nodeClause_erase {E : List (Count × VTy × VTy)} {tH c : TExpr} {j : Nat}
    (h : nodeClause E tH j = some c) : clauseAt j tH.erase = some c.erase := by
  unfold nodeClause at h
  split at h
  · simp only [Option.join_eq_some_iff] at h
    simp only [TExpr.erase, clauseAt]
    exact clauseParts_erase _ _ _ _ h
  · simp only [Option.join_eq_some_iff] at h
    exact absurd h getElem?_replicate_none

/-- **The records a `handle` node's `TInfo.sshape` holds**: per operation, at a clause the
checker classifies `stored` (`ks`), its `StoredAtX` derivation (`sshapeOf`) at the node's answer
`R`; `none` otherwise. -/
def storedShapes (E : List (Count × VTy × VTy)) (R : VTy) (tH : TExpr) (ks : List HKind) :
    List (Option SShape) :=
  (List.range E.length).map fun j =>
    if (ks[j]?.map (·.kind)) == some .stored then (nodeClause E tH j).bind (sshapeOf R) else none

/-- **A record the checker writes is a derivation of the grammar** at the clause the node holds
for the operation, the clause its erasure runs (`clauseAt`), at a `P`-shaped answer. -/
theorem storedShapes_sound {E : List (Count × VTy × VTy)} {R : VTy} {tH : TExpr}
    {ks : List HKind} {j : Nat} {sh : SShape} (h : (storedShapes E R tH ks)[j]? = some (some sh)) :
    ∃ c, nodeClause E tH j = some c ∧ clauseAt j tH.erase = some c.erase ∧
      PShaped R sh.C sh.Rx ∧ StoredAtXC sh.C sh.Rx c := by
  simp only [storedShapes, List.getElem?_map] at h
  cases hr : (List.range E.length)[j]? with
  | none => simp [hr] at h
  | some j' =>
    have hj : j' = j := by
      rw [List.getElem?_eq_some_iff] at hr; obtain ⟨_, hr⟩ := hr; simpa using hr.symm
    subst hj
    simp only [hr, Option.map_some, Option.some.injEq] at h
    split at h
    · obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.1 h
      exact ⟨c, hc, nodeClause_erase hc, sshapeOf_sound hs⟩
    · cases h

end BoCa.Fig16.LogRel.Core.Check
