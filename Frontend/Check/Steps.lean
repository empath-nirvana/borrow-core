import Frontend.Check.Rules

/-!
# Frontend — Check — steps shared by the checker's cases

The checker's environment, the messages it reports, the deciders of fold shapes and
destructors, the implicit drops (SPEC §12), and the steps that combine checked premises through a
rule builder once its side conditions are decided: closing binders, splitting and merging
contexts, `boxed`, application to a variable, `<,>`, `case` and `Fun`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (Jdg FShape HasDtor toFShape isX0)

/-! ### Fold shapes and destructors, decided -/

/-- `FShape.WF`, decided. -/
def FShape.wfB : FShape → Bool
  | .leaf A => VTy.clB 0 A
  | .refX => true
  | .varX => true
  | .tensor F G => FShape.wfB F && FShape.wfB G
  | .sum F G => FShape.wfB F && FShape.wfB G

theorem FShape.wfB_sound : ∀ F : FShape, FShape.wfB F = true → F.WF
  | .leaf A, h => VTy.clB_sound 0 A h
  | .refX, _ => trivial
  | .varX, _ => trivial
  | .tensor F G, h => by
      simp only [FShape.wfB, Bool.and_eq_true] at h
      exact ⟨wfB_sound F h.1, wfB_sound G h.2⟩
  | .sum F G, h => by
      simp only [FShape.wfB, Bool.and_eq_true] at h
      exact ⟨wfB_sound F h.1, wfB_sound G h.2⟩

/-- `FShape.Guarded`, decided. -/
def FShape.guardedB : FShape → Bool
  | .varX => false
  | _ => true

theorem FShape.guardedB_sound : ∀ F : FShape, FShape.guardedB F = true → F.Guarded
  | .leaf _, _ => trivial
  | .refX, _ => trivial
  | .varX, h => by simp [FShape.guardedB] at h
  | .tensor _ _, _ => trivial
  | .sum _ _, _ => trivial

/-! ### Destructors (SPEC §12) -/

/-- `HasDtor`, decided: `dtorB false A` for `A`, and `dtorB true A` for `T[1/X]` at a `μ` body
`T = A` (`Ref X` and `X` become `1`), the same recursion as `dtorAt`. -/
def dtorB : Bool → CVTy → Bool
  | alg, .tensor A B => dtorB alg A && dtorB alg B
  | alg, .sum A B => dtorB alg A && dtorB alg B
  | alg, .ref A => (alg && isX0 A) || dtorB false A
  | alg, .tvar 0 => alg
  | _, .tvar (_ + 1) => false
  | _, .box _ A => dtorB false A
  | _, .mu A => FShape.wfB (toFShape A) && FShape.guardedB (toFShape A) && dtorB true A
  | _, .thunk (.amp _ (.ret .unit)) => true
  | _, .thunk (.nu (.amp C (.ret R))) =>
      CTy.nuOkB (.amp C (.ret R)) && VTy.clB 0 R && dtorB false R
  | _, .thunk _ => false
  | _, .unit | _, .zero | _, .int _ | _, .unk | _, .bang _ | _, .imm _ _ | _, .mut _ _ => true
  | _, .fam (.ref A) => dtorB false A
  | _, .fam (.imm _ _) => true
  | _, .fam (.mut _ _) => true
  | _, .fam _ => false
  | _, .opq _ => false

theorem dtorB_sound : ∀ (alg : Bool) (A : CVTy), dtorB alg A = true →
    HasDtor (cond alg ((toFShape A).resO .unit) A)
  | alg, .tensor A B, h => by
      simp only [dtorB, Bool.and_eq_true] at h
      have h₁ := dtorB_sound alg A h.1
      have h₂ := dtorB_sound alg B h.2
      cases alg <;> exact .tensor h₁ h₂
  | alg, .sum A B, h => by
      simp only [dtorB, Bool.and_eq_true] at h
      have h₁ := dtorB_sound alg A h.1
      have h₂ := dtorB_sound alg B h.2
      cases alg <;> exact .sum h₁ h₂
  | false, .ref A, h => .ref (dtorB_sound false A (by simpa [dtorB] using h))
  | true, .ref A, h => by
      by_cases hA : A = .tvar 0
      · subst hA; exact .unit
      · have hx : isX0 A = false := by
          cases A with
          | tvar n => cases n <;> simp_all [isX0]
          | _ => rfl
        have hl : toFShape (.ref A) = .leaf (.ref A) := by
          cases A with
          | tvar n => cases n <;> simp_all [toFShape]
          | _ => rfl
        simp only [dtorB, hx, Bool.true_and, Bool.false_or] at h
        simp only [cond, hl, FShape.resO]
        exact .ref (dtorB_sound false A h)
  | true, .tvar 0, _ => .unit
  | false, .tvar 0, h => by simp [dtorB] at h
  | _, .tvar (_ + 1), h => by simp [dtorB] at h
  | alg, .box _ A, h => by
      have := HasDtor.box (a := ‹_›) (dtorB_sound false A (by simpa [dtorB] using h))
      cases alg <;> exact this
  | alg, .mu A, h => by
      simp only [dtorB, Bool.and_eq_true] at h
      have := HasDtor.mu (FShape.wfB_sound _ h.1.1) (FShape.guardedB_sound _ h.1.2)
        (dtorB_sound true A h.2)
      cases alg <;> exact this
  | alg, .thunk (.amp _ (.ret .unit)), _ => by cases alg <;> exact .close
  | alg, .thunk (.nu (.amp C (.ret R))), h => by
      simp only [dtorB, Bool.and_eq_true] at h
      have := HasDtor.nu (CTy.nuOkB_sound _ h.1.1) (VTy.clB_sound 0 R h.1.2)
        (dtorB_sound false R h.2)
      cases alg <;> exact this
  | _, .thunk (.nu (.ret _)), h | _, .thunk (.nu (.arr _ _)), h | _, .thunk (.nu .top), h
  | _, .thunk (.nu (.all _ _ _)), h | _, .thunk (.nu (.nu _)), h
  | _, .thunk (.nu (.amp _ (.arr _ _))), h | _, .thunk (.nu (.amp _ (.amp _ _))), h
  | _, .thunk (.nu (.amp _ .top)), h | _, .thunk (.nu (.amp _ (.all _ _ _))), h
  | _, .thunk (.nu (.amp _ (.nu _))), h => by simp [dtorB] at h
  | _, .thunk (.ret _), h | _, .thunk (.arr _ _), h | _, .thunk .top, h
  | _, .thunk (.all _ _ _), h => by simp [dtorB] at h
  | _, .thunk (.amp _ (.ret (.tensor _ _))), h | _, .thunk (.amp _ (.ret .zero)), h
  | _, .thunk (.amp _ (.ret (.sum _ _))), h | _, .thunk (.amp _ (.ret (.thunk _))), h
  | _, .thunk (.amp _ (.ret (.ref _))), h | _, .thunk (.amp _ (.ret (.imm _ _))), h
  | _, .thunk (.amp _ (.ret (.mut _ _))), h | _, .thunk (.amp _ (.ret (.box _ _))), h
  | _, .thunk (.amp _ (.ret (.bang _))), h | _, .thunk (.amp _ (.ret .unk)), h
  | _, .thunk (.amp _ (.ret (.tvar _))), h | _, .thunk (.amp _ (.ret (.mu _))), h
  | _, .thunk (.amp _ (.ret (.int _))), h | _, .thunk (.amp _ (.ret (.fam _))), h
  | _, .thunk (.amp _ (.ret (.opq _))), h
  | _, .thunk (.amp _ (.arr _ _)), h
  | _, .thunk (.amp _ (.amp _ _)), h | _, .thunk (.amp _ .top), h
  | _, .thunk (.amp _ (.all _ _ _)), h | _, .thunk (.amp _ (.nu _)), h => by simp [dtorB] at h
  | alg, .unit, _ => by cases alg <;> exact .unit
  | alg, .zero, _ => by cases alg <;> exact .zero
  | alg, .int _, _ => by cases alg <;> exact .int
  | _, .opq _, h => by simp [dtorB] at h
  | alg, .unk, _ => by cases alg <;> exact .unk
  | alg, .bang _, _ => by cases alg <;> exact .bang
  | alg, .imm _ _, _ => by cases alg <;> exact .imm
  | alg, .mut _ _, _ => by cases alg <;> exact .mut
  | alg, .fam (.ref A), h => by
      have := HasDtor.array (dtorB_sound false A (by simpa [dtorB] using h))
      cases alg <;> exact this
  | alg, .fam (.imm _ _), _ => by cases alg <;> exact .arrayImm
  | alg, .fam (.mut _ _), _ => by cases alg <;> exact .arrayMut
  | _, .fam .unit, h | _, .fam (.tensor _ _), h | _, .fam .zero, h | _, .fam (.sum _ _), h
  | _, .fam (.thunk _), h | _, .fam (.box _ _), h
  | _, .fam (.bang _), h | _, .fam .unk, h | _, .fam (.tvar _), h | _, .fam (.mu _), h
  | _, .fam (.int _), h | _, .fam (.fam _), h => by simp [dtorB] at h

/-- `A` has a destructor. -/
def hasDtorB (A : CVTy) : Bool := dtorB false A

theorem hasDtorB_sound {A : CVTy} (h : hasDtorB A = true) : HasDtor A := dtorB_sound false A h


/-- What the checker knows at a point besides `Δ` and the slot types `T`: the declarations in
scope, the name of each slot (a dead binder has none), the lifetime names, a `def`'s type
parameters, and the slots **owed** to the current tail position (SPEC §12): variables with a
destructor that the computation being checked must consume on every path, the checker dropping
them where it does not. `own` is indexed like `vars`; a slot past its end is not owed. -/
structure Env where
  scope : Scope
  vars : List (Option String)
  lenv : List (String × LifeVar)
  tps : List (String × CVTy)
  own : List Bool
  /-- The number of extern slots, at the end of `vars` (SPEC §11). -/
  nExt : Nat
  /-- The current row (SPEC §19): the row of the returner chain `F_Σ B` the computation being
  checked has, set where a computation is checked against one; `none` in a value, where a
  computation is synthesized with no type expected. `[spec §19]` -/
  row : Option CRow
  /-- The typed values the slots are bound to by `x <- return V`, each at its slot's level (the
  number of slots below it): where `[handle]` reads its clauses (SPEC §19, *Clause kinds*). -/
  vals : List (Nat × BoCa.Fig16.LogRel.Core.Check.TExpr) := []

/-- The depth bound for elaborating a type. -/
def tyFuel : Nat := 65536

def Env.tyEnv (E : Env) (Δ : LifeCtx) : TyEnv := ⟨E.scope, Δ, Δ, E.lenv, [], [], E.tps, []⟩
def Env.elabV (E : Env) (Δ : LifeCtx) (A : VTy) : Except Error CVTy := Frontend.Check.elabV tyFuel (E.tyEnv Δ) A
def Env.elabC (E : Env) (Δ : LifeCtx) (C : CTy) : Except Error CCTy := Frontend.Check.elabC tyFuel (E.tyEnv Δ) C
def Env.elabS (E : Env) (Δ : LifeCtx) (σ : Shape) : Except Error CShape :=
  Frontend.Check.elabS tyFuel (E.tyEnv Δ) σ
def Env.elabL (E : Env) (Δ : LifeCtx) (a : Life) : Except Error CLife := elabLife Δ E.lenv a
def Env.elabRow (E : Env) (Δ : LifeCtx) (sp : Span) (r : Row) : Except Error CRow :=
  Frontend.Check.elabRow tyFuel (E.tyEnv Δ) sp r

/-- Types and lifetimes in messages, with the lifetime names in scope. -/
def Env.ppV (E : Env) (A : CVTy) : String := Frontend.Check.ppV E.lenv 0 0 A
def Env.ppC (E : Env) (C : CCTy) : String := Frontend.Check.ppC E.lenv 0 C
def Env.ppL (E : Env) (a : CLife) : String := ppLifeP E.lenv 1 a

/-! ### Rows  `[spec §19]` -/

/-- `C` as a returner chain `F_Σ A`: its row and answer. -/
def effRow? : CCTy → Option (CRow × CVTy)
  | .ret A => some ([], A)
  | .eff n i q A B fin C => (effRow? C).map fun (S, R) => (⟨n, i, q, A, B, fin⟩ :: S, R)
  | _ => none

/-- The environment of a computation checked against `C`: the row of `C` when it is a returner
chain.  `[spec §19]` -/
def Env.atC (E : Env) (C : CCTy) : Env :=
  match effRow? C with
  | some (S, _) => { E with row := some S }
  | none => E

/-- A value: nothing owed, and no row. -/
def Env.forVal (E : Env) : Env := { E with own := [], row := none }

def ppRow (E : Env) (S : CRow) : String :=
  "[" ++ ", ".intercalate (S.map fun o =>
    s!"{o.n}.{o.i} {qualStr o.q} {E.ppV o.A} ~> {E.ppV o.B}") ++ "]"

theorem Row.weak_of_unr {S : CRow} (h : S.Unr) : S.Weak := by
  obtain ⟨o, ho, hq⟩ := h
  exact ⟨o, ho, by rw [hq]; decide⟩

/-- The operation `k.i` of the current row, found as itself. -/
def findOp (E : Env) (sp : Span) (what : String) (k i : Nat) :
    Except Error (Σ S : CRow, {o : COpSig // BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o}) :=
  match E.row with
  | none => throw ⟨sp, s!"`{what}[{k}.{i}]` is not checked at a row: its type is not known " ++
      "to be `F[…] A`; ascribe the computation"⟩
  | some S =>
    if k < 2 ^ 32 ∧ i < 2 ^ 32 then
      match h : BoCa.Fig16.LogRel.Core.Row.find S (UInt32.ofNat k) (UInt32.ofNat i) with
      | some o =>
        have hm := BoCa.Fig16.LogRel.Core.Row.find_mem h
        pure ⟨S, o, by rw [hm.2.1, hm.2.2]; exact h⟩
      | none => throw ⟨sp, s!"the operation {k}.{i} is not in the row `{ppRow E S}`"⟩
    else throw ⟨sp, s!"the operation {k}.{i}: a name and an index are below 2^32"⟩

/-- `κ`'s type `kTy S R q B`, read back: the qualifier and the operation's answer. -/
def kRead : CVTy → Option (CQual × CVTy)
  | .thunk (.amp (.arr B _) .top) => some (.lin, B)
  | .thunk (.amp (.arr B _) _) => some (.aff, B)
  | .bang (.thunk (.amp (.arr B _) _)) => some (.unr, B)
  | _ => none

/-- The operations a clause's type may be the type of: a control operation `A ↠^q B` (its
argument `A ⊗ κ`), then an abortive one `A ↠^aff 0`. -/
def clauseCands : CVTy → List (CQual × CVTy × CVTy)
  | .bang (.thunk (.arr (.tensor A K) _)) =>
      (match kRead K with | some (q, B) => [(q, A, B)] | none => []) ++
        [(.aff, .tensor A K, .zero)]
  | .bang (.thunk (.arr A _)) => [(.aff, A, .zero)]
  | _ => []

/-- The first candidate whose clause type is `c`. -/
def firstClause (S : CRow) (R c : CVTy) :
    List (CQual × CVTy × CVTy) → Option {e // BoCa.Fig16.LogRel.Core.clauseTy S R e = c}
  | [] => none
  | e :: es => if h : BoCa.Fig16.LogRel.Core.clauseTy S R e = c then some ⟨e, h⟩
      else firstClause S R c es

/-- The operations `E` of a handler read back from the type of its clauses' tuple, with
`clausesTy S R E` that type. An abortive operation is read as affine: `aff` and `unr` give it
the same clause type. -/
def clausesRead (S : CRow) (R : CVTy) :
    (Tc : CVTy) → Option {E // BoCa.Fig16.LogRel.Core.clausesTy S R E = Tc}
  | .unit => some ⟨[], rfl⟩
  | .tensor c rest => do
    let ⟨e, he⟩ ← firstClause S R c (clauseCands c)
    let ⟨E, hE⟩ ← clausesRead S R rest
    pure ⟨e :: E, by subst he hE; rfl⟩
  | _ => none

/-- The operations a clause's type under BOXED-κ may be the type of (`[spec §28]`): a control
operation `A ↠^q B` (its argument `A ⊗ [@d] κ`), then an abortive one. -/
def clauseCandsB : CVTy → List (CQual × CVTy × CVTy)
  | .bang (.thunk (.arr (.tensor A (.box d K)) _)) =>
      (match kRead K with | some (q, B) => [(q, A, B)] | none => []) ++
        [(.aff, .tensor A (.box d K), .zero)]
  | .bang (.thunk (.arr A _)) => [(.aff, A, .zero)]
  | _ => []

/-- The first candidate whose clause type under BOXED-κ at `@d` is `c`. -/
def firstClauseB (S : CRow) (R : CVTy) (d : CLife) (c : CVTy) :
    List (CQual × CVTy × CVTy) → Option {e // BoCa.Fig16.LogRel.Core.clauseTyB S R d e = c}
  | [] => none
  | e :: es => if h : BoCa.Fig16.LogRel.Core.clauseTyB S R d e = c then some ⟨e, h⟩
      else firstClauseB S R d c es

/-- The operations `E` of a handler whose clauses receive `κ` boxed at `@d`, read back from the
type of its clauses' tuple, with `clausesTyB S R d E` that type.  `[spec §28]` -/
def clausesReadB (S : CRow) (R : CVTy) (d : CLife) :
    (Tc : CVTy) → Option {E // BoCa.Fig16.LogRel.Core.clausesTyB S R d E = Tc}
  | .unit => some ⟨[], rfl⟩
  | .tensor c rest => do
    let ⟨e, he⟩ ← firstClauseB S R d c (clauseCandsB c)
    let ⟨E, hE⟩ ← clausesReadB S R d rest
    pure ⟨e :: E, by subst he hE; rfl⟩
  | _ => none

/-- The lifetime a clause tuple's type boxes its continuations at: that of its first clause whose
argument is `A ⊗ [@d] κ`, `κ` a continuation's type. -/
def clausesBoxOf : CVTy → Option CLife
  | .tensor (.bang (.thunk (.arr (.tensor _ (.box d K)) _))) rest =>
      if (kRead K).isSome then some d else clausesBoxOf rest
  | .tensor _ rest => clausesBoxOf rest
  | _ => none

/-- A clause tuple's type read as BOXED-κ's: its boxing lifetime, and its operations. Where it reads,
the checker prefers it to `clausesRead`, which would read a clause `!U(A ⊗ [@d] κ ⊸ F_Σ R)` as an
abortive operation's.  `[spec §28]` -/
def clausesReadBoxed (S : CRow) (R : CVTy) (Tc : CVTy) :
    Option (Σ d : CLife, {E // BoCa.Fig16.LogRel.Core.clausesTyB S R d E = Tc}) := do
  let d ← clausesBoxOf Tc
  let r ← clausesReadB S R d Tc
  pure ⟨d, r⟩

/-- `h_ret`'s type `!U(A -o F_S R)` read back. -/
def retRead (Tr : CVTy) :
    Option (Σ' (S : CRow) (A R : CVTy), BoCa.Fig16.LogRel.Core.retTy S A R = Tr) :=
  match Tr with
  | .bang (.thunk (.arr A C)) =>
    match effRow? C with
    | some (S, R) =>
      if h : BoCa.Fig16.LogRel.Core.retTy S A R = .bang (.thunk (.arr A C)) then some ⟨S, A, R, h⟩ else none
    | none => none
  | _ => none

/-! ### Messages -/

def Env.slotName (E : Env) (i : Nat) : String :=
  match E.vars[i]? with
  | some (some x) => s!"`{x}`"
  | _ => "a hidden slot"

/-- The first slot both sides use whose type is not persistent. -/
def firstOverlap : List CVTy → List Bool → List Bool → Option Nat
  | A :: T, a :: as, b :: bs =>
      if a && b && !A.persistent then some 0 else (firstOverlap T as bs).map (· + 1)
  | _, _, _ => none

def Env.slotTy (E : Env) (T : List CVTy) (i : Nat) : String := (T[i]?.map E.ppV).getD "?"

def splitErr (E : Env) (T : List CVTy) (sp : Span) (u₁ u₂ : List Bool) : Error :=
  match firstOverlap T u₁ u₂ with
  | some i => ⟨sp, s!"{E.slotName i} is used twice here, and its type `{E.slotTy T i}` is not " ++
      "persistent"⟩
  | none => ⟨sp, "internal error: context split"⟩

/-- The first slot `a` uses that `b` neither uses nor absorbs. -/
def firstMissing : List Bool → List Bool → List Bool → Option Nat
  | a :: as, b :: bs, c :: cs => if a && !(b || c) then some 0 else (firstMissing as bs cs).map (· + 1)
  | _, _, _ => none

/-- Why slot `i` was not dropped where a path does not consume it. -/
def Env.notDropped (E : Env) (T : List CVTy) (i : Nat) : String :=
  match T[i]? with
  | some A => if hasDtorB A then "" else s!", and its type `{E.ppV A}` has no destructor"
  | none => ""

/-- The two parts of a `case` or a `<,>` do not consume the same variables. -/
def mergeErr (E : Env) (T : List CVTy) (sp : Span) (what₁ what₂ intro : String)
    (u₁ w₁ u₂ w₂ : List Bool) : Error :=
  match firstMissing u₁ u₂ w₂, firstMissing u₂ u₁ w₁ with
  | some i, _ => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₁} but not in {what₂}" ++
      E.notDropped T i⟩
  | _, some i => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₂} but not in {what₁}" ++
      E.notDropped T i⟩
  | _, _ => ⟨sp, "internal error: merge"⟩

/-- A binder's variable is neither consumed nor dropped when its scope closes. -/
def unconsumed (E : Env) (sp : Span) (x : String) (A : CVTy) (lin : Bool) : Error :=
  if lin then ⟨sp, s!"`{x}` is declared `linear` and is not consumed in its scope"⟩
  else if hasDtorB A then
    ⟨sp, s!"`{x}` is not consumed in its scope, and it cannot be dropped where its scope ends"⟩
  else ⟨sp, s!"`{x}` is not consumed in its scope, and its type `{E.ppV A}` has no destructor"⟩

def mismatch (sp : Span) (want got : String) : Error :=
  ⟨sp, s!"type mismatch: expected `{want}`, but this has type `{got}`"⟩

/-! ### Small steps shared by the cases -/

section
variable {Δ : LifeCtx} {T : List CVTy}

def convV (E : Env) (sp : Span) (A : CVTy) : (Σ B : CVTy, Res Δ T (.val B)) → Except Error (Res Δ T (.val A))
  | ⟨B, r⟩ => if h : B = A then pure (h ▸ r) else throw (mismatch sp (E.ppV A) (E.ppV B))

/-- A computation of `D` at `C`: equal, or `F_Σ′ A` within `F_Σ A` by `[sub]` (SPEC §19). -/
def convC (E : Env) (sp : Span) (C : CCTy) : (Σ D : CCTy, Res Δ T (.comp D)) → Except Error (Res Δ T (.comp C))
  | ⟨D, r⟩ =>
    if h : D = C then pure (h ▸ r) else
    match effRow? D, effRow? C with
    | some (S', A'), some (S, _) =>
      if hD : effOf S' A' = D then
        if hC : effOf S A' = C then
          if hle : rowLeB S' S = true then pure (hC ▸ rEffSub (at_ sp) hle (hD ▸ r))
          else throw ⟨sp, s!"type mismatch: expected `{E.ppC C}`, but this has type " ++
            s!"`{E.ppC D}`: its row `{ppRow E S'}` is not within `{ppRow E S}`"⟩
        else throw (mismatch sp (E.ppC C) (E.ppC D))
      else throw (mismatch sp (E.ppC C) (E.ppC D))
    | _, _ => throw (mismatch sp (E.ppC C) (E.ppC D))

def popL {A : CVTy} {P : List Bool → Prop} (E : Env) (sp : Span) (x : String) (F : Fam (A :: T) P)
    (lin : Bool := false) : Except Error (Fam T (fun L => P (true :: L))) :=
  match F.popLive with
  | some F' => pure F'
  | none => throw (unconsumed E sp x A lin)

def popD {A : CVTy} {P : List Bool → Prop} (sp : Span) (F : Fam (A :: T) P) :
    Except Error (Fam T (fun L => P (false :: L))) :=
  match F.popDead with
  | some F' => pure F'
  | none => throw ⟨sp, "internal error: a dead binder is used"⟩

def withPop {j : Jdg} {t : TExpr} {s : CRow} {p : Pins} (sp : Span)
    (F : Fam (withT T) (fun L => TTied p s Δ (mkCtx (withT T) L) t j)) :
    Except Error (Fam T (fun L => TTied p s Δ (BoCa.Fig16.LogRel.Core.withCtx (mkCtx T L)) t j)) :=
  match popWith F with
  | some F' => pure F'
  | none => throw ⟨sp, "internal error: a dead binder is used"⟩

end

/-- The variable bound in slot `i`, if `x` names one. -/
def lookupVar (x : String) : List (Option String) → Option Nat
  | [] => none
  | y :: ys => if y == some x then some 0 else (lookupVar x ys).map (· + 1)

/-- A slot that is not owed: a dead binder, or `linear`. -/
def Env.push (E : Env) (x : Option String) : Env := { E with vars := x :: E.vars, own := false :: E.own }

/-- The typed value the slot `i` is bound to, when it is bound by `x <- return V`. -/
def Env.valOf (E : Env) (i : Nat) : Option BoCa.Fig16.LogRel.Core.Check.TExpr :=
  if i < E.vars.length then (E.vals.find? (·.1 == E.vars.length - 1 - i)).map (·.2) else none

/-- Record the typed value of the slot pushed next, when its binding's head is `return V`; a
variable is its own binding's value. -/
def Env.bindVal (E : Env) (t : BoCa.Fig16.LogRel.Core.Check.TExpr) : Env :=
  let rec val? : BoCa.Fig16.LogRel.Core.Check.TExpr → Option BoCa.Fig16.LogRel.Core.Check.TExpr
    | .ret _ _ _ (.var _ _ i _) => E.valOf i
    | .ret _ _ _ v => some v
    | .effSub _ _ _ _ _ t => val? t
    | _ => none
  match val? t with
  | some v => { E with vals := (E.vars.length, v) :: E.vals }
  | none => E

/-- A binder's live slot `x : A`, owed to its scope when `A` has a destructor, is not persistent
and the binder is not `linear` (SPEC §12). -/
def Env.pushOwn (E : Env) (x : String) (A : CVTy) (lin : Bool := false) : Env :=
  { E with vars := some x :: E.vars, own := (!lin && !A.persistent && hasDtorB A) :: E.own }

/-- Nothing owed: a value, or a computation that is not in tail position. -/
def Env.clearOwn (E : Env) : Env := { E with own := [] }



/-- What is still owed after the slots `u` are consumed. -/
def Env.minus (E : Env) (u : List Bool) : Env := { E with own := andL E.own (u.map (! ·)) }

/-- The owed slots a computation mentions by name, where the name is not shadowed. -/
def Env.ownIn (E : Env) (p : String → Bool) : Env :=
  { E with own := (List.range E.own.length).map fun i =>
      E.own.getD i false && match E.vars[i]? with
        | some (some x) => lookupVar x E.vars == some i && p x
        | _ => false }

/-- The environment of a `def`'s body at a use: its own scope, no variables or lifetimes of the
use site but the persistent externs (the operations of SPEC §11, which carry no authority; a
capability is not persistent), its type parameters bound. -/
def Env.forDef (E : Env) (T : List CVTy) (d : DefInfo) (tps : List (String × CVTy)) : Env :=
  let n := E.vars.length
  let vars := (List.range n).map fun i =>
    if n ≤ i + E.nExt && (T[i]?.map (·.persistent)).getD false then E.vars.getD i none else none
  ⟨d.scope, vars, [], tps, [], E.nExt, none, []⟩

def inDef (x : String) (sp : Span) (e : Error) : Error :=
  { e with msg := s!"{e.msg}\n  in the body of `{x}`, used at {sp.start.render}" }

def thunkvLam : String :=
  "the body of `thunkv` must erase to a λ: `fun`, `Fun` or `<M, N>`, possibly under " ++
  "`delay_in`/`delay_out`/`stream_in`/`stream_out` or an ascription (syntax-core §6.4); " ++
  "eta-expand it"

def notBang (E : Env) (T : List CVTy) (sp : Span) : Option Nat → Error
  | some i => ⟨sp, s!"`!thunk` promotes only over `!` types, but {E.slotName i}, of type " ++
      s!"`{E.slotTy T i}`, is used inside"⟩
  | none => ⟨sp, thunkvLam⟩

section
variable {Δ : LifeCtx} {T : List CVTy}

/-! ### Drops (SPEC §12) -/

mutual
/-- `x` occurs free in a value-judged expression. -/
def mentionsV (x : String) : Val → Bool
  | .var _ y | .clone _ y => y == x
  | .defApp .. | .unit _ | .const .. | .sugar .. => false
  | .pair _ V W | .app _ V W => mentionsV x V || mentionsV x W
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => mentionsV x V
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => mentionsC x M
  | .lend _ y _ => y.name == x

/-- `x` occurs free in a computation. -/
def mentionsC (x : String) : Comp → Bool
  | .ret _ V | .absurd _ V => mentionsV x V
  | .bind _ y _ M N _ => mentionsC x M || (y.name != x && mentionsC x N)
  | .force _ y => y.name == x
  | .lam _ y _ M => y.name != x && mentionsC x M
  | .app _ M y => mentionsC x M || y.name == x
  | .with_ _ M N => mentionsC x M || mentionsC x N
  | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M | .nuOut _ M
  | .ascribe _ M _ => mentionsC x M
  | .top _ => false
  | .letUnit _ V M => mentionsV x V || mentionsC x M
  | .letPair _ y z V M => mentionsV x V || (y.name != x && z.name != x && mentionsC x M)
  | .case _ V y M z N => mentionsV x V || (y.name != x && mentionsC x M) ||
      (z.name != x && mentionsC x N)
  | .loop _ _ src V M N => mentionsV x V || (!src.bound.contains x && mentionsC x M) || mentionsC x N
  | .perform _ _ _ V | .abort _ _ _ V => mentionsV x V
  | .handle _ _ hr hc M => hr.name == x || hc.name == x || mentionsC x M
  | .unwind _ y _ M D N => mentionsC x M || mentionsC x D || (y.name != x && mentionsC x N)
  | .withbor2r _ _ _ _ _ _ p m M => p.name == x || (m.name != x && mentionsC x M)
end

/-- A path's terminal computation: every form except those that pass what is owed on to a tail
position (`x <- M; N`, `let`, `case`, `<M, N>`, `fun`, `Fun`, `nu_in`, an ascription). -/
def _root_.Frontend.Comp.terminal : Comp → Bool
  | .bind .. | .letUnit .. | .letPair .. | .case .. | .with_ .. | .lam .. | .lamL ..
  | .nuIn .. | .ascribe .. | .unwind .. => false
  | _ => true

/-- The slots to drop before a terminal computation: owed, and neither used nor absorbed by it. -/
def owedLeft : List Bool → List Bool → List Bool → Nat → List Nat
  | o :: os, u :: us, w :: ws, i => (if o && !u && !w then [i] else []) ++ owedLeft os us ws (i + 1)
  | _, _, _, _ => []

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- `dtorE A xᵢ; M` for the slot `i`. -/
def dropOne {C : CCTy} (sp : Span) (i : Nat) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  match hi : T[i]? with
  | some A =>
    if hA : hasDtorB A = true then
      if hE : (BoCa.Fig16.LogRel.Core.dtorE A).effFree = true then
        if hc : BoCa.Fig16.LogRel.Core.closedAt 0 (BoCa.Fig16.LogRel.Core.dtorE A) = true then
          if h : overlapOK T (oneL T i) r.F.u = true then
            pure (rDrop (at_ sp) (at_ sp) i A hi (hasDtorB_sound hA) hc hE r h)
          else throw ⟨sp, "internal error: a dropped slot is used"⟩
        else throw ⟨sp, "internal error: a destructor is not closed"⟩
      else throw ⟨sp, "internal error: a destructor performs or handles an operation"⟩
    else throw ⟨sp, "internal error: an owed slot has no destructor"⟩
  | none => throw ⟨sp, "internal error: an owed slot is out of range"⟩

/-- Drop what the terminal computation `r` leaves owed, the lowest index (the most recently
bound variable) first. -/
def dropOwed {C : CCTy} (E : Env) (sp : Span) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  (owedLeft E.own r.F.u r.F.w 0).foldr (fun i acc => do dropOne sp i (← acc)) (pure r)

end

/-- `boxed[@a] V`. -/
def boxIt {A : CVTy} (E : Env) (T : List CVTy) (sp : Span) (a : CLife) (r : Res Δ T (.val A)) :
    Except Error (Res Δ T (.val (.box a A))) :=
  if hwf : a.wf Δ = true then
    if hs : usedSat (outlivesB Δ a) T r.F.u = true then pure (rBoxI (at_ sp) a hwf r hs)
    else match firstBad (outlivesB Δ a) T r.F.u with
      | some i => throw ⟨sp, s!"`boxed[{E.ppL a}]`: {E.slotName i}, of type `{E.slotTy T i}`, " ++
          s!"is used inside, and it cannot be shown to outlive `{E.ppL a}`"⟩
      | none => throw ⟨sp, "internal error: boxed"⟩
  else throw ⟨sp, s!"`boxed[{E.ppL a}]`: the lifetime is not defined here"⟩

/-- `M x`. -/
def appIt {A : CVTy} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span) (x : Ident)
    (rM : Res Δ T (.comp (.arr A C))) : Except Error (Res Δ T (.comp C)) :=
  match lookupVar x.name E.vars with
  | none => throw ⟨x.span, s!"application `M x` takes a variable, and `{x.name}` is not one " ++
      "in scope; bind it first"⟩
  | some i =>
    if hi : T[i]? = some A then
      if h : overlapOK T rM.F.u (oneL T i) = true then pure (rApp { sp, name := x.name } rM i hi h)
      else throw (splitErr E T sp rM.F.u (oneL T i))
    else throw (mismatch x.span (E.ppV A) (E.slotTy T i))

/-- `<M, N>`: both components at the pair's context. -/
def withIt {C D : CCTy} (E : Env) (T : List CVTy) (sp : Span) (r₁ : Res Δ (withT T) (.comp C))
    (r₂ : Res Δ (withT T) (.comp D)) : Except Error (Res Δ T (.comp (.amp C D))) := do
  let F₁ ← withPop sp r₁.F
  let F₂ ← withPop sp r₂.F
  if s₁ : subL F₁.u (orL F₂.u F₂.w) = true then
    if s₂ : subL F₂.u (orL F₁.u F₁.w) = true then pure (rWith (at_ sp) r₁.t r₂.t (F₁.merge F₂ s₁ s₂))
    else throw (mergeErr E T sp "the first component" "the second" "in this `<M, N>`, "
      F₁.u F₁.w F₂.u F₂.w)
  else throw (mergeErr E T sp "the first component" "the second" "in this `<M, N>`, "
    F₁.u F₁.w F₂.u F₂.w)

/-- `case V { inl x -> M | inr y -> N }`: both arms at one context. -/
def caseIt {A B : CVTy} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span) (x y : Ident)
    (rV : Res Δ T (.val (.sum A B))) (r₁ : Res Δ (A :: T) (.comp C))
    (r₂ : Res Δ (B :: T) (.comp C)) : Except Error (Res Δ T (.comp C)) := do
  let F₁ ← popL E x.span x.name r₁.F
  let F₂ ← popL E y.span y.name r₂.F
  if s₁ : subL F₁.u (orL F₂.u F₂.w) = true then
    if s₂ : subL F₂.u (orL F₁.u F₁.w) = true then
      let F := F₁.merge F₂ s₁ s₂
      if h : overlapOK T rV.F.u F.u = true then pure (rSumE (at_ sp) rV F h)
      else throw (splitErr E T sp rV.F.u F.u)
    else throw (mergeErr E T sp "the `inl` arm" "the `inr` arm" "in this `case`, " F₁.u F₁.w F₂.u F₂.w)
  else throw (mergeErr E T sp "the `inl` arm" "the `inr` arm" "in this `case`, " F₁.u F₁.w F₂.u F₂.w)

/-- `Fun 'x < @b. M`. -/
def funIt {v : LifeVar} {bl : CLife} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span)
    (name : String) (rM : Res (Δ.extend v bl) (.unit :: T) (.comp C)) :
    Except Error (Res Δ T (.comp (.all v bl C))) := do
  if hbx : bl.mentions v = false then
    if hΔx : boundsAvoidB Δ v = true then
      let F ← popD sp rM.F
      if hs : usedSat (fun A => !vfreeB v A) T F.u = true then pure (rAllI (at_ sp) hbx hΔx F hs)
      else match firstBad (fun A => !vfreeB v A) T F.u with
        | some i => throw ⟨sp, s!"`Fun '{name}`: {E.slotName i}, of type `{E.slotTy T i}`, is " ++
            s!"used inside, and its type mentions `'{name}` ({ppLVar v})"⟩
        | none => throw ⟨sp, "internal error: Fun"⟩
    else throw ⟨sp, s!"`Fun '{name}`: its number {ppLVar v} occurs in a bound of the lifetime context"⟩
  else throw ⟨sp, s!"`Fun '{name}`: its bound mentions its own number {ppLVar v}"⟩

/-- `fun (x : 1) -> M` at `1 -o F_Σ B` whose body does not use `x`: `[λ-dead]`, the binder's
slot closed dead.  `[spec §26]` -/
def lamDeadIt (sp : Span) {S : CRow} {B : CVTy} (rM : Res Δ (.unit :: T) (.comp (effOf S B))) :
    Option (Res Δ T (.comp (.arr .unit (effOf S B)))) :=
  rM.F.popDead.map (rLamDead (at_ sp))

/-- `fun (x : A) -> M`, `M` checked under the binder's slot: `[λ-dead]` (SPEC §26) when `A` is `1`,
`M`'s type is a returner chain `F_Σ B` and `M` does not use `x`; `[λ]` otherwise, the binder's
slot closed live. -/
def lamIt {A : CVTy} {C : CCTy} (E : Env) (sp : Span) (x : Ident) (rM : Res Δ (A :: T) (.comp C)) :
    Except Error (Res Δ T (.comp (.arr A C))) :=
  match A, rM with
  | .unit, rM =>
    match effRow? C with
    | some (S, B) =>
      if hC : effOf S B = C then
        match lamDeadIt sp (hC ▸ rM) with
        | some r => pure (hC ▸ r)
        | none => rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
      else rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
    | none => rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
  | _, rM => rLam { sp, name := x.name } <$> popL E x.span x.name rM.F

/-! ### Effectful bindings  `[spec §19]` -/

/-- A computation at the row `S′`, at the row `S` by `[sub]`. -/
def liftRow (E : Env) (sp : Span) {S' : CRow} {A : CVTy} (S : CRow)
    (r : Res Δ T (.comp (effOf S' A))) : Except Error (Res Δ T (.comp (effOf S A))) :=
  if hle : rowLeB S' S = true then pure (rEffSub (at_ sp) hle r)
  else throw ⟨sp, s!"this computation performs the operations `{ppRow E S'}`, which are not " ++
    s!"within the row `{ppRow E S}` here"⟩

/-- A synthesized computation at the row `S`: a returner chain within it. -/
def atRow (E : Env) (sp : Span) (S : CRow) :
    (Σ C : CCTy, Res Δ T (.comp C)) → Except Error (Σ B : CVTy, Res Δ T (.comp (effOf S B)))
  | ⟨C, r⟩ =>
    match effRow? C with
    | some (S', B) =>
      if hC : effOf S' B = C then do pure ⟨B, ← liftRow E sp S (hC ▸ r)⟩
      else throw ⟨sp, "internal error: a returner chain"⟩
    | none => throw ⟨sp, s!"after a computation that performs operations, this must have a " ++
        s!"type `F[…] B`, but it has type `{E.ppC C}`"⟩

/-- The finaliser of an effectful binding: the destructors of the non-persistent slots `u` (the
slots the rest of the computation uses), under the binder's dead slot, at the pure row (SPEC §24:
a finaliser lets no raise escape). It runs when an abortive operation of the bound computation
stops the rest. SPEC §19's drop glue: `[then]`'s `D`, inserted as SPEC §12 inserts destructors. -/
def finalOf (E : Env) (sp : Span) (_S : CRow) (u : List Bool) :
    Except Error (Res Δ (.unit :: T) (.comp (effOf [] .unit))) := do
  let idx := (List.range T.length).filter fun i =>
    u.getD i false && !((T[i]?.map (·.persistent)).getD true)
  let r0 : Res Δ (.unit :: T) (.comp (.ret .unit)) := rRet (at_ sp) (rUnit (at_ sp))
  let r ← idx.foldlM (init := r0) fun r i => do
    match T[i]? with
    | some A =>
      if hasDtorB A then dropOne sp (i + 1) r
      else throw ⟨sp, s!"{E.slotName i}, of type `{E.ppV A}`, is live across a computation " ++
        "that may abort, and its type has no destructor: an abortive operation of the bound " ++
        "computation would abandon it"⟩
    | none => throw ⟨sp, "internal error: a slot is out of range"⟩
  pure r

/-- A marked scheme's derived node, over its checked term (SPEC §3). -/
def markIt {j : Jdg} (sp : Span) : SchemeMark → Res Δ T j → Except Error (Res Δ T j)
  | .litFn bs, r => match rLitFn (at_ sp) bs r with
    | some r' => pure r'
    | none => err sp "internal error: a string literal's table is not the scheme of its bytes"

/-- `[then]` at the row `S`: `N` (its binder closed) and the finaliser `D` at one context. -/
def thenIt (E : Env) (sp : Span) {S : CRow} {A B : CVTy} {tN : TExpr} {sN : CRow} {pN : Pins}
    (rM : Res Δ T (.comp (effOf S A)))
    (FN : Fam T (fun L => TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B))))
    (rD : Res Δ (.unit :: T) (.comp (effOf [] .unit))) :
    Except Error (Res Δ T (.comp (effOf S B))) := do
  if hNZ : Row.nzB S = true then
    if hUq : Row.uniqB S = true then
      let FD ← popD sp rD.F
      if s₁ : subL FN.u (orL FD.u FD.w) = true then
        if s₂ : subL FD.u (orL FN.u FN.w) = true then
          let F := FN.merge FD s₁ s₂
          let F' : Fam T (fun L => (TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B)) ∧
              TTied rD.pins rD.sigs Δ (mkCtx (.unit :: T) (false :: L)) rD.t
                (.comp (effOf [] .unit))) ∧
              (S.UnrD → BoCa.Fig16.LogRel.Core.Persistent (mkCtx T L))) ←
            if hu : Row.unrDB S = true then
              if hs : usedSat isBangB T F.u = true then
                pure ((F.restrict isBangB hs).map fun _ ⟨h, hp⟩ => ⟨h, fun _ => persistent_of hp⟩)
              else match firstBad isBangB T F.u with
                | some i => throw ⟨sp, s!"{E.slotName i}, of type `{E.slotTy T i}`, is used " ++
                    s!"after an operation of the row `{ppRow E S}`, which may resume more than " ++
                    "once: it must be a `!` type"⟩
                | none => throw ⟨sp, "internal error: an unrestricted row"⟩
            else pure (F.map fun _ h => ⟨h, fun hU => absurd (Row.unrDB_iff.mpr hU) (by simp [hu])⟩)
          if h : overlapOK T rM.F.u F'.u = true then
            pure (rEffThen (at_ sp) (Row.nzB_sound hNZ) (Row.uniqB_sound hUq) rM F' h)
          else throw (splitErr E T sp rM.F.u F'.u)
        else throw (mergeErr E T sp "the finaliser" "the rest" "after this computation, "
          FD.u FD.w FN.u FN.w)
      else throw (mergeErr E T sp "the rest" "the finaliser" "after this computation, "
        FN.u FN.w FD.u FD.w)
    else throw ⟨sp, s!"the row `{ppRow E S}` has an operation twice"⟩
  else throw ⟨sp, s!"the row `{ppRow E S}` has an operation of the reserved name 0"⟩

/-- `x <- M; N` whose head `M` performs operations, at the row `S` (SPEC §19). At a row with no
weakening, or when every slot `N` uses drops (and is `!` at an unrestricted row), `[let]`;
otherwise `[then]`, with the finaliser `finalOf`: the destructors of the slots `N` uses. -/
def effBind (E : Env) (sp : Span) (x : Ident) (lin : Bool) {S : CRow} {A B : CVTy}
    (rM : Res Δ T (.comp (effOf S A))) (rN : Res Δ (A :: T) (.comp (effOf S B))) :
    Except Error (Res Δ T (.comp (effOf S B))) := do
  let FN ← popL E x.span x.name rN.F lin
  if hw : Row.weakB S = true then
    let p : CVTy → Bool := fun A => dropB A && (!Row.unrB S || isBangB A)
    if hs : usedSat p T FN.u = true then
      let FN' := (FN.restrict p hs).map fun _ ⟨h, hp⟩ =>
        (⟨h, fun _ s hsm hl => dropB_sound _ (by
            have := hp s hsm hl
            simp only [p, Bool.and_eq_true] at this
            exact this.1),
          fun hU s hsm hl => isBangB_sound (by
            have := hp s hsm hl
            simp only [p, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
            rcases this.2 with h' | h'
            · exact absurd (Row.unrB_iff.mpr hU) (by simp [h'])
            · exact h')⟩ :
          TTied rN.pins rN.sigs Δ (mkCtx (A :: T) (true :: _)) rN.t (.comp (effOf S B)) ∧
            (S.Weak → (mkCtx T _).Drops) ∧ (S.Unr → BoCa.Fig16.LogRel.Core.Persistent (mkCtx T _)))
      if h : overlapOK T rM.F.u FN'.u = true then pure (rEffLet (at_ sp) rM FN' h)
      else throw (splitErr E T sp rM.F.u FN'.u)
    else
      let rD ← finalOf E sp S FN.u
      thenIt E sp rM FN rD
  else
    let FN' := FN.map fun _ h =>
      (⟨h, fun hW => absurd (Row.weakB_iff.mpr hW) (by simp [hw]),
        fun hU => absurd (Row.weakB_iff.mpr (Row.weak_of_unr hU)) (by simp [hw])⟩ :
        TTied rN.pins rN.sigs Δ (mkCtx (A :: T) (true :: _)) rN.t (.comp (effOf S B)) ∧
          (S.Weak → (mkCtx T _).Drops) ∧ (S.Unr → BoCa.Fig16.LogRel.Core.Persistent (mkCtx T _)))
    if h : overlapOK T rM.F.u FN'.u = true then pure (rEffLet (at_ sp) rM FN' h)
    else throw (splitErr E T sp rM.F.u FN'.u)

end

end Frontend.Check
