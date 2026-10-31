import Frontend.Check.Pin

/-!
# Frontend — Check — the derived copy at `imm`  `[spec §12, #746]`

`Imm @a A` and `[Imm @a A]` are linear with a **derived copy** (`DerivedCopy`, `Core/Classes.lean`):
the kernel's constant `copy` (`CDerives.copy`, at `axCopyTy`) or `array_copy` (`CDerives.arrCopy`,
under `bangE`) makes two of one. A second use of such a variable is its derived copy, which the
checker inserts, as it inserts a derived drop (SPEC §12); the split admits a slot both parts use
only at a persistent type.

**The rule** (`docs/scope/746-imm-copy.md` §1). At a node whose context the checker splits between
two parts, each variable both parts mention free whose slot is `DerivedCopy` (`derivedCopyB`) is
copied before the node:

    p <- return (copy xᵢ); let (x₁, x₂) = p; node

the first part checked where `x` names `x₁`, the second where it names `x₂` (`Env.copyAt`). `copyIt` builds it from the rule builders `rVar`, the constant's node, `rLolliE`,
`rRet`, `rTensorE` and `rBind`, so its erasure is `copy_derives`'s `copyE` (`copyIt_erase`) and its
derivations are the kernel's rules. The copy constant's node records the variable and that the
checker inserted it (`TInfo.inserted`), which `bcc copies` prints.

The parts are each checked once: the rule is decided from the syntax (`mentionsV`, `mentionsC`)
and the slot's type before the parts are checked.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (DerivedCopy copyC copyE bindE)

/-- `DerivedCopy`, decided. -/
def derivedCopyB : CVTy → Bool
  | .imm _ _ => true
  | .fam (.imm _ _) => true
  | _ => false

theorem derivedCopyB_iff (A : CVTy) : derivedCopyB A = true ↔ DerivedCopy A := by
  constructor
  · intro h
    match A, h with
    | .imm a B, _ => exact .imm a B
    | .fam (.imm a B), _ => exact .arrImm a B
  · intro h
    cases h <;> rfl

/-- The variables a split copies: each named, unshadowed variable both parts mention (`m₁`, `m₂`)
whose slot is `DerivedCopy`, outermost slot first. -/
def Env.copyVars (E : Env) (T : List CVTy) (m₁ m₂ : String → Bool) : List String :=
  go E.vars T 0 []
where
  /-- The slots from `i` on, innermost first: the slot's type is tested first, so the scans for
  shadowing and mentions run only at `DerivedCopy` slots. -/
  go : List (Option String) → List CVTy → Nat → List String → List String
    | some x :: vs, A :: As, i, acc =>
      go vs As (i + 1)
        (if derivedCopyB A && lookupVar x E.vars == some i && m₁ x && m₂ x then x :: acc else acc)
    | _ :: vs, _ :: As, i, acc => go vs As (i + 1) acc
    | _, _, _, acc => acc

/-- The environment of a copy's body, where the part sees copy `fst` (slot `1`) or the other
(slot `0`) as `x`: the copied slot `i` no longer owed, the pair's slot dead, the part's copy owed as
any binder's (`Env.pushOwn`) and the other copy hidden and not owed. -/
def Env.copyAt (E : Env) (T : List CVTy) (i : Nat) (x : String) (A : CVTy) (fst : Bool) : Env :=
  let E₀ := (E.minus (oneL T i)).push none
  let own := !A.persistent && hasDtorB A
  if fst then { E₀ with vars := none :: some x :: E₀.vars, own := false :: own :: E₀.own }
  else { E₀ with vars := some x :: none :: E₀.vars, own := own :: false :: E₀.own }

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- The copy constant at a `DerivedCopy` type `A`, as a value of `A ⊸ A ⊗ A`: `copy`, or
`unbang array_copy`. -/
def copyConst (info : TInfo) (A : CVTy) (h : derivedCopyB A = true) :
    Res Δ T (.val (.lolli A (.tensor A A))) :=
  match A, h with
  | .imm a B, _ =>
    ⟨.copy info (.val (.lolli (.imm a B) (.tensor (.imm a B) (.imm a B)))) a B, [], [],
      (Fam.dead T).map fun _ hd => TTied.ofAt fun _ => .copy hd⟩
  | .fam (.imm a B), _ =>
    rBangE info ⟨.arrCopy info (.val (BoCa.Fig16.LogRel.Core.arrCopyTy a B)) a B, [], [],
      (Fam.dead T).map fun _ hd => TTied.ofAt fun _ => .arrCopy a B hd⟩

/-- **The derived copy of slot `i`** around a computation `r` checked under the two copies and
the pair's slot: `p <- return (copyC A xᵢ); let (x₁, x₂) = p; r`, the shape of `copy_derives`.
`[spec §12]` -/
def copyIt (E : Env) (sp : Span) (x : String) (i : Nat) (A : CVTy) (hi : T[i]? = some A)
    (hc : derivedCopyB A = true) {C : CCTy}
    (r : Res Δ (A :: A :: .tensor A A :: T) (.comp C)) : Except Error (Res Δ T (.comp C)) := do
  let F₁ ← popL E sp x r.F
  let F₂ ← popL E sp x F₁
  let rP : Res Δ (.tensor A A :: T) (.val (.tensor A A)) := rVar (at_ sp) 0 (.tensor A A) rfl
  if hP : overlapOK (.tensor A A :: T) rP.F.u F₂.u = true then
    let rT := rTensorE (atB sp [x, x]) rP F₂ hP
    let FN ← popL E sp x rT.F
    let rx : Res Δ T (.val A) := rVar { sp, name := x } i A hi
    let rf : Res Δ T (.val (.lolli A (.tensor A A))) :=
      copyConst { sp, name := x, inserted := true } A hc
    if ha : overlapOK T rx.F.u rf.F.u = true then
      let rM := rRet (at_ sp) (rLolliE (at_ sp) rf rx ha)
      if h : overlapOK T rM.F.u FN.u = true then pure (rBind (atB sp [x]) rM FN h)
      else throw ⟨sp, "internal error: a derived copy's split"⟩
    else throw ⟨sp, "internal error: a derived copy's variable"⟩
  else throw ⟨sp, "internal error: a derived copy's pair"⟩

/-- **The inserted copy has `copy_derives`'s shape**: `copyIt`'s erasure is `copyE`'s, the kernel's
`copyC A` applied to `xᵢ` and its pair taken apart around the body. (`copyE` states the body as
`e.shift 1 2`, past the pair's slot; here the body is checked with that slot already in its
context.) -/
theorem copyIt_erase {E : Env} {sp : Span} {x : String} {i : Nat} {A : CVTy}
    {hi : T[i]? = some A} {hc : derivedCopyB A = true} {C : CCTy}
    {r : Res Δ (A :: A :: .tensor A A :: T) (.comp C)} {r' : Res Δ T (.comp C)}
    (h : copyIt E sp x i A hi hc r = .ok r') :
    r'.t.erase = bindE (.app (copyC A) (.var i)) (.letpair (.var 0) r.t.erase) := by
  unfold copyIt at h
  cases h₁ : popL E sp x r.F with
  | error e => simp [h₁, bind, Except.bind] at h
  | ok F₁ =>
    cases h₂ : popL E sp x F₁ with
    | error e => simp [h₁, h₂, bind, Except.bind] at h
    | ok F₂ =>
      simp only [h₁, h₂, bind, Except.bind] at h
      split at h
      · rename_i hP
        cases h₃ : popL E sp x (rTensorE (atB sp [x, x]) (rVar (at_ sp) 0 (.tensor A A) rfl) F₂ hP).F with
        | error e => simp [h₃] at h
        | ok FN =>
          simp only [h₃] at h
          split at h
          · split at h
            · simp only [pure, Except.pure, Except.ok.injEq] at h
              subst h
              match A, hc with
              | .imm a B, _ => rfl
              | .fam (.imm a B), _ => rfl
            · simp [throw, throwThe, MonadExceptOf.throw] at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `copyIt` where each copy is used or dropped by its part, an internal error otherwise (a copy
absorbed and never dropped). A part mentions `x` only
at `var` leaves, each a use its masks keep, so the rule fires exactly where the split would give
the slot to both parts: the trigger is the split's own masks, read before the parts are checked.
-/
def copyUsed (E : Env) (sp : Span) (x : String) (i : Nat) (A : CVTy) (hi : T[i]? = some A)
    (hc : derivedCopyB A = true) {C : CCTy}
    (r : Res Δ (A :: A :: .tensor A A :: T) (.comp C)) : Except Error (Res Δ T (.comp C)) :=
  if r.F.u.take 2 == [true, true] then copyIt E sp x i A hi hc r
  else throw ⟨sp, s!"internal error: a derived copy of `{x}` that a part mentions but does not use"⟩

end

/-- The derived copies the checker inserted in `t`, `none` past the depth `fuel`: each copy constant's
source, the variable it copies and that variable's type, read off the node (`TInfo.inserted`). -/
def _root_.BoCa.Fig16.LogRel.Core.Check.TExpr.insertedCopies : Nat → TExpr →
    Option (List (Span × String × CVTy))
  | 0, _ => none
  | f + 1, t => do
    let here := match t with
      | .copy i _ a A => if i.inserted then [(i.sp, i.name, (.imm a A : CVTy))] else []
      | .arrCopy i _ a A => if i.inserted then [(i.sp, i.name, (.fam (.imm a A) : CVTy))] else []
      | _ => []
    let ks ← t.children.mapM fun (_, k) => k.insertedCopies f
    pure (here ++ ks.flatten)

/-! ### Copies at a split, around a part checker -/

/-- **An inserted copy is at `Imm`**: a `copy` constant's node is typed only at `axCopyTy a A`, the
copy of `Imm @a A`, a `DerivedCopy` type. The checker inserts a copy only as this node (or
`array_copy`'s, `TDerivesP.arrCopy_at`), so it inserts none at a `mut` borrow, an owned value or a
declared type, whatever decides where it goes.  `[spec §12]` -/
theorem _root_.BoCa.Fig16.LogRel.Core.Check.TDerivesP.copy_at {Δ : LifeCtx} {Γ : BoCa.Ctx CVTy}
    {i : TInfo} {j : BoCa.Fig16.LogRel.Core.Jdg} {a : Lifetime.Life} {A : CVTy}
    {j' : BoCa.Fig16.LogRel.Core.Jdg} (h : TDerivesP Δ Γ (.copy i j a A) j') :
    j' = .val (BoCa.Fig16.LogRel.Core.axCopyTy a A) ∧ DerivedCopy (.imm a A) := by
  cases h
  exact ⟨rfl, .imm a A⟩

/-- **An inserted view copy is at `[Imm]`**: an `array_copy` constant's node is typed only at
`arrCopyTy a A`, the copy of `[Imm @a A]`, a `DerivedCopy` type.  `[spec §9, §12]` -/
theorem _root_.BoCa.Fig16.LogRel.Core.Check.TDerivesP.arrCopy_at {Δ : LifeCtx}
    {Γ : BoCa.Ctx CVTy} {i : TInfo} {j : BoCa.Fig16.LogRel.Core.Jdg} {a : Lifetime.Life} {A : CVTy}
    {j' : BoCa.Fig16.LogRel.Core.Jdg} (h : TDerivesP Δ Γ (.arrCopy i j a A) j') :
    j' = .val (BoCa.Fig16.LogRel.Core.arrCopyTy a A) ∧ DerivedCopy (.fam (.imm a A)) := by
  cases h
  exact ⟨rfl, .arrImm a A⟩

/-- An `Except Error` step in the checker's monad. -/
def liftExcept {m : Type → Type} [Monad m] [MonadExceptOf Error m] {α : Type} : Except Error α → m α
  | .ok a => pure a
  | .error e => throw e

/-- The copies of `xs` around `k`, which checks the node at the slots it is given, its first part
in the first environment and its second in the second. -/
def withCopies {m : Type → Type} [Monad m] [MonadExceptOf Error m] {Δ : LifeCtx} (sp : Span) :
    List String → Env → Env → (T : List CVTy) →
    (Env → Env → (T' : List CVTy) → m (Σ C : CCTy, Res Δ T' (.comp C))) →
    m (Σ C : CCTy, Res Δ T (.comp C))
  | [], E₁, E₂, T, k => k E₁ E₂ T
  | x :: xs, E₁, E₂, T, k =>
    match lookupVar x E₁.vars with
    | none => throw ⟨sp, s!"internal error: a derived copy of `{x}`, which is not in scope"⟩
    | some i =>
      match hi : T[i]? with
      | none => throw ⟨sp, "internal error: a derived copy's slot is out of range"⟩
      | some A =>
        if hc : derivedCopyB A = true then do
          let ⟨C, r⟩ ← withCopies sp xs (E₁.copyAt T i x A true) (E₂.copyAt T i x A false)
            (A :: A :: .tensor A A :: T) k
          pure ⟨C, ← liftExcept (copyUsed E₁ sp x i A hi hc r)⟩
        else throw ⟨sp, s!"internal error: a derived copy of `{x}`, which has none"⟩

/-- `withCopies` at a computation checked against `C`. -/
def withCopiesC {m : Type → Type} [Monad m] [MonadExceptOf Error m] {Δ : LifeCtx} (sp : Span) (xs : List String) (E : Env) (T : List CVTy) (C : CCTy)
    (k : Env → Env → (T' : List CVTy) → m (Res Δ T' (.comp C))) :
    m (Res Δ T (.comp C)) := do
  if xs.isEmpty then k E E T else
  let ⟨C', r⟩ ← withCopies sp xs E E T fun E₁ E₂ T' => do pure ⟨C, ← k E₁ E₂ T'⟩
  if h : C' = C then pure (h ▸ r) else throw ⟨sp, "internal error: a derived copy's type"⟩

/-- `withCopies` at a value: `run (copies; return V)`, by `ofRet`; the value as it is when nothing
is copied. -/
def withCopiesV {m : Type → Type} [Monad m] [MonadExceptOf Error m] {Δ : LifeCtx} (sp : Span) (xs : List String) (E : Env) (T : List CVTy)
    (k : Env → Env → (T' : List CVTy) → m (Σ A : CVTy, Res Δ T' (.val A))) :
    m (Σ A : CVTy, Res Δ T (.val A)) := do
  if xs.isEmpty then k E E T else
  let ⟨C, r⟩ ← withCopies sp xs E E T fun E₁ E₂ T' => do
    let ⟨A, r⟩ ← k E₁ E₂ T'
    pure ⟨.ret A, rRet (at_ sp) r⟩
  match C, r with
  | .ret A, r => pure ⟨A, rOfRet (at_ sp) r⟩
  | _, _ => throw ⟨sp, "internal error: a derived copy's value"⟩

/-- `withCopiesV` at a value checked against `A`. -/
def withCopiesVC {m : Type → Type} [Monad m] [MonadExceptOf Error m] {Δ : LifeCtx} (sp : Span) (xs : List String) (E : Env) (T : List CVTy) (A : CVTy)
    (k : Env → Env → (T' : List CVTy) → m (Res Δ T' (.val A))) :
    m (Res Δ T (.val A)) := do
  if xs.isEmpty then k E E T else
  let ⟨A', r⟩ ← withCopiesV sp xs E T fun E₁ E₂ T' => do pure ⟨A, ← k E₁ E₂ T'⟩
  if h : A' = A then pure (h ▸ r) else throw ⟨sp, "internal error: a derived copy's type"⟩

end Frontend.Check
