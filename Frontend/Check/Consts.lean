import Frontend.Check.Steps

/-!
# Frontend — Check — constants and derived forms

Each constant (syntax-core §8, §8a) is one `CDerives` constructor at a consumed context, and each
derived form (§9) one Lean theorem concluding a `CDerives` judgment; the brackets give every
argument, so nothing is searched. A binder argument (`withbor1['x, …]`, `fold_imm[F, 'y, …]`,
`withbor_s_mut[σ, 'c, T]`, `withbor_f2_*['c, 'a, 'b, …]`) is numbered by §3: `Δ.freshVar`, and
`withbor_f2`'s internal `'a`, `'b` are `Δ.freshVar` and `Δ.freshVar + 1`. Each side condition is
decided by a `Bool` function of `Frontend/Check/Decide.lean` and discharged by its soundness
lemma.

A fold's shape argument is a type with the recursive position `X`, decoded to an `FShape` by
§5's canonical `dec`: maximal closed leaves, then `ref X`, `X`, `*` and `+`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives Jdg VFree VOutlives FShape FD₁ mutM immM formerMut formerImm d_allocS
  d_freeS withborSM_wf withborSI_wf withborM2_wf withborI2_wf shortenE_wf FamSide cbTy2 famTy2
  plainV)

/-! ### Fold shapes -/

/-- §5's `dec`: a type in which `X` is the variable `0`, to its `FShape`. -/
def decF (sp : Span) : CVTy → Except Error FShape
  | .tensor A B =>
    if VTy.occB 0 (.tensor A B) = false then pure (.leaf (.tensor A B))
    else do pure (.tensor (← decF sp A) (← decF sp B))
  | .sum A B =>
    if VTy.occB 0 (.sum A B) = false then pure (.leaf (.sum A B))
    else do pure (.sum (← decF sp A) (← decF sp B))
  | .ref (.tvar 0) => pure .refX
  | .tvar 0 => pure .varX
  | A =>
    if VTy.occB 0 A = false then pure (.leaf A)
    else err sp (s!"`{ppV [] 1 0 A}` is not a fold shape: `X` may occur only as `X`, `ref X`, " ++
      "or under `*` and `+`")

/-- A fold's shape argument: elaborated with `X` bound, decoded, `WF` and `Guarded`. -/
def elabFShape (E : Env) (Δ : LifeCtx) (sp : Span) (F : VTy) :
    Except Error {G : FShape // G.WF ∧ G.Guarded} := do
  let A ← Frontend.Check.elabV tyFuel { E.tyEnv Δ with mu := ["X"] } F
  let G ← decF sp A
  if hw : FShape.wfB G = true then
    if hg : FShape.guardedB G = true then pure ⟨G, FShape.wfB_sound G hw, FShape.guardedB_sound G hg⟩
    else err sp "a fold shape must not be `X` itself"
  else err sp "a fold shape's leaves must be closed"

/-! ### Building a constant's result -/

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- A constant: its rule at every consumed context. -/
def cDead {A : CVTy} (e : CExpr) (h : ∀ {Γ}, BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ → CDerives Δ Γ e (.val A)) :
    Σ B : CVTy, Res Δ T (.val B) :=
  ⟨A, e, (Fam.dead T).map fun _ hd => h hd⟩

/-- A derived form stated at `Ctx.Dead`: every slot dead. -/
def cStrict {A : CVTy} (e : CExpr) (h : ∀ {Γ}, Ctx.Dead Γ → CDerives Δ Γ e (.val A)) :
    Σ B : CVTy, Res Δ T (.val B) :=
  ⟨A, e, (Fam.deadStrict T).map fun _ hd => h hd⟩

/-- `'x` fresh for `Δ` and free in neither `A` nor `B`. -/
def freshFor (sp : Span) (x : LifeVar) (A B : CVTy) :
    Except Error (PLift (Δ.find? x = none ∧ ¬ VFree x A ∧ ¬ VFree x B)) :=
  if hx : Δ.find? x = none then
    if h₁ : vfreeB x A = false then
      if h₂ : vfreeB x B = false then
        pure ⟨hx, not_vfree_of_vfreeB h₁, not_vfree_of_vfreeB h₂⟩
      else err sp s!"the binder {ppLVar x} occurs free in `{ppVTy B}`"
    else err sp s!"the binder {ppLVar x} occurs free in `{ppVTy A}`"
  else err sp s!"the binder {ppLVar x} is already bound"

/-- `Δ ⊨ @b` and `Δ ⊢ A ⊐ @b`: `withbor2`'s witness. -/
def outlivesWitness (sp : Span) (b : CLife) (A : CVTy) :
    Except Error (PLift (∃ b, Δ.Defines b ∧ VOutlives Δ b A)) :=
  if hw : b.wf Δ = true then
    if ho : outlivesB Δ b A = true then pure ⟨⟨b, defines_of_wf hw, outlivesB_sound Δ b A ho⟩⟩
    else err sp s!"cannot show that `{ppVTy A}` outlives `{ppLife b}`"
  else err sp s!"the lifetime `{ppLife b}` is not defined here"

def needB (sp : Span) (b : Bool) (msg : String) : Except Error (PLift (b = true)) :=
  if h : b = true then pure ⟨h⟩ else err sp msg

/-- `FamSide`: the freshness and renaming facts of `withbor_f2`, decided. -/
def famSide (sp : Span) (M : CLife → CVTy → CVTy) (c x y : LifeVar) (A B T' : CVTy) :
    Except Error (PLift (FamSide M Δ c x y A B T')) := do
  let ⟨hΔ⟩ ← needB sp (okB Δ.entries) "the lifetime context is not well scoped"
  let ⟨hx⟩ ← needB sp (Δ.find? x).isNone s!"{ppLVar x} is already bound"
  let ⟨hy⟩ ← needB sp (Δ.find? y).isNone s!"{ppLVar y} is already bound"
  let ⟨hxy⟩ ← needB sp (x != y) "the two internal borrows need distinct numbers"
  let free (z : LifeVar) (A : CVTy) : Except Error (PLift (¬ VFree z A)) := do
    let ⟨h⟩ ← needB sp (!vfreeB z A) s!"{ppLVar z} occurs free in `{ppVTy A}`"
    pure ⟨not_vfree_of_vfreeB (by simpa using h)⟩
  let ⟨hAx⟩ ← free x A
  let ⟨hBx⟩ ← free x B
  let ⟨hTx⟩ ← free x T'
  let ⟨hAy⟩ ← free y A
  let ⟨hBy⟩ ← free y B
  let ⟨hTy⟩ ← free y T'
  let ⟨hcbx⟩ ← free x (cbTy2 M c Δ.meetOfDom A B T')
  let ⟨hcby⟩ ← free y (cbTy2 M c Δ.meetOfDom A B T')
  if hinst : BoCa.Fig16.LogRel.Core.VTy.instLife c (.var y)
      (.lolli (famTy2 M (.var c) A B) (.box (.var c) T'))
      = .lolli (famTy2 M (.var y) A B) (.box (.var y) T') then
    pure ⟨⟨by simpa [LifeCtx.Ok] using hΔ, by simpa using hx, by simpa using hy,
      by simpa using hxy, hAx, hBx, hTx, hAy, hBy, hTy, hcbx, hcby, hinst⟩⟩
  else err sp "the callback's family is not generic in its lifetime"

/-- A shape all of whose leaves are plain. -/
def plainShape (sp : Span) (s : CShape) : Except Error (PLift (s.plain = true)) :=
  if h : s.plain = true then pure ⟨h⟩
  else err sp "a block borrow needs a shape whose leaves are plain (no lifetime, no `U`)"

/-! ### Constants -/

/-- The type and derivations of a constant or derived form (syntax-core §8, §8a, §9). -/
def synConst (E : Env) (Δ : LifeCtx) (T : List CVTy) (sp : Span) :
    Const → Except Error (Σ A : CVTy, Res Δ T (.val A))
  | .alloc A => do
      let A ← E.elabV Δ A
      pure (cDead _ fun hd => CDerives.alloc (A := A) hd)
  | .free A => do
      let A ← E.elabV Δ A
      pure (cDead _ fun hd => CDerives.free (A := A) hd)
  | .swap A B => do
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      pure (cDead _ fun hd => CDerives.swap (A := A) (B := B) hd)
  | .copy a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      pure (cDead _ fun hd => CDerives.copy (a := a) (A := A) hd)
  | .copyBang A => do
      let A ← E.elabV Δ A
      pure (cDead _ fun hd => CDerives.copyBang (A := A) hd)
  | .forgetImm a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      pure (cDead _ fun hd => CDerives.forgetImm (a := a) (A := A) hd)
  | .forgetMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      pure (cDead _ fun hd => CDerives.forgetMut (a := a) (A := A) hd)
  | .forgetUnk => pure (cDead _ fun hd => CDerives.forgetUnk hd)
  | .forgetBang A => do
      let A ← E.elabV Δ A
      pure (cDead _ fun hd => CDerives.forgetBang (A := A) hd)
  | .withbor1 _ A B => do
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hsc⟩ ← needB sp (scopedB Δ A) s!"`{ppVTy A}` mentions a lifetime not in scope"
      pure (cDead _ fun hd => CDerives.withbor1 x hd hx (scopedB_sound hsc) h₁ h₂)
  | .withbor2 _ b A B => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hside⟩ ← outlivesWitness sp b A
      pure (cDead _ fun hd => CDerives.withbor2 x hd hx hside h₁ h₂)
  | .withbor3 a _ A B => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      pure (cDead _ fun hd => CDerives.withbor3 (a := a) x hd hx h₁ h₂)
  | .withload a _ A B => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      pure (cDead _ fun hd => CDerives.withload (a := a) x hd hx h₁ h₂)
  | .withswap a A B => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      pure (cDead _ fun hd => CDerives.withswap (a := a) (A := A) (B := B) hd)
  | .foldImm F _ c R => do
      let ⟨G, hW, hG⟩ ← elabFShape E Δ sp F
      let c ← E.elabL Δ c
      let R ← E.elabV Δ R
      let y := Δ.freshVar
      let ⟨hyM⟩ ← needB sp (!vfreeB y (.mu G.ty)) s!"the binder {ppLVar y} occurs in the shape"
      let ⟨hyR⟩ ← needB sp (!vfreeB y R) s!"the binder {ppLVar y} occurs in `{ppVTy R}`"
      let ⟨hR⟩ ← needB sp (outlivesAllB R) (s!"`fold_imm`'s result `{ppVTy R}` must outlive " ++
        "every lifetime: no `U`, `unk`, `imm`, `mut` or `box`")
      pure (cDead _ fun hd => CDerives.foldImm G y c R hd hW hG
        (not_vfree_of_vfreeB (by simpa using hyM)) (not_vfree_of_vfreeB (by simpa using hyR))
        (outlivesAllB_sound R hR))
  | .foldOwn F R => do
      let ⟨G, hW, hG⟩ ← elabFShape E Δ sp F
      let R ← E.elabV Δ R
      pure (cDead _ fun hd => CDerives.foldOwn G R hd hW hG)
  | .foldReuse F R => do
      let ⟨G, hW, hG⟩ ← elabFShape E Δ sp F
      let R ← E.elabV Δ R
      pure (cDead _ fun hd => CDerives.foldReuse G R hd hW hG)
  | .fixd A S => do
      let A ← E.elabV Δ A
      let S ← E.elabV Δ S
      pure (cDead _ fun hd => CDerives.fixD A S hd)
  | .unfoldS A S => do
      let A ← E.elabV Δ A
      let S ← E.elabV Δ S
      pure (cDead _ fun hd => CDerives.unfoldS A S hd)
  | .lit c => pure (cDead _ fun hd => CDerives.lit c hd)
  | .host op => pure (cDead _ fun hd => CDerives.hostOp op hd)
  | .allocS σ => do
      let s ← E.elabS Δ σ
      pure (cStrict _ fun hd => d_allocS s hd)
  | .freeS σ => do
      let s ← E.elabS Δ σ
      pure (cStrict _ fun hd => d_freeS s hd)
  | .withborS m σ _ T' => do
      let s ← E.elabS Δ σ
      let T' ← E.elabV Δ T'
      let ⟨hσ⟩ ← plainShape sp s
      let ⟨hT⟩ ← needB sp (plainV T') s!"a block borrow's result `{ppVTy T'}` must be plain"
      let ⟨hΔ⟩ ← needB sp (okB Δ.entries) "the lifetime context is not well scoped"
      let c := Δ.freshVar
      let ⟨hc⟩ ← needB sp (Δ.find? c).isNone s!"{ppLVar c} is already bound"
      match m with
      | .mut => pure (cStrict _ fun hd =>
          withborSM_wf hσ c hT (by simpa [LifeCtx.Ok] using hΔ) (by simpa using hc) hd)
      | .imm => pure (cStrict _ fun hd =>
          withborSI_wf hσ c hT (by simpa [LifeCtx.Ok] using hΔ) (by simpa using hc) hd)
  | .withborF2Mut _ _ _ w A B T' => do
      let w ← E.elabL Δ w
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let T' ← E.elabV Δ T'
      let c := Δ.freshVar
      let x := Δ.freshVar
      let y := Δ.freshVar + 1
      let ⟨s⟩ ← famSide sp mutM c x y A B T'
      let ⟨hA⟩ ← outlivesWitness sp w A
      let ⟨hBo⟩ ← needB sp (outlivesB (FD₁ Δ x) (.var x) B)
        s!"`{ppVTy B}` must outlive the family's outer borrow"
      let ⟨hTo⟩ ← needB sp (outlivesB (FD₁ Δ x) (.var x) T')
        s!"`{ppVTy T'}` must outlive the family's outer borrow"
      pure (cStrict _ fun hd => withborM2_wf s hA (outlivesB_sound _ _ _ hBo)
        (outlivesB_sound _ _ _ hTo) hd)
  | .withborF2Imm _ _ _ A B T' => do
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let T' ← E.elabV Δ T'
      let c := Δ.freshVar
      let x := Δ.freshVar
      let y := Δ.freshVar + 1
      let ⟨s⟩ ← famSide sp immM c x y A B T'
      let ⟨hA⟩ ← needB sp (scopedB Δ A) s!"`{ppVTy A}` mentions a lifetime not in scope"
      let ⟨hB⟩ ← needB sp (scopedB Δ B) s!"`{ppVTy B}` mentions a lifetime not in scope"
      let ⟨hBo⟩ ← needB sp (outlivesB (FD₁ Δ x) (.var x) B)
        s!"`{ppVTy B}` must outlive the family's outer borrow"
      let ⟨hTo⟩ ← needB sp (outlivesB (FD₁ Δ x) (.var x) T')
        s!"`{ppVTy T'}` must outlive the family's outer borrow"
      pure (cStrict _ fun hd => withborI2_wf s (scopedB_sound hA) (scopedB_sound hB)
        (outlivesB_sound _ _ _ hBo) (outlivesB_sound _ _ _ hTo) hd)

/-- The lifetime of a family at a shape: the lifetime of its first leaf. -/
def famLife (M : Mode) : CShape → CVTy → Option CLife
  | .leaf _, .mut b _ => if M matches .mut then some b else none
  | .leaf _, .imm b _ => if M matches .imm then some b else none
  | .node s _, .tensor A _ => famLife M s A
  | _, _ => none

/-- `shortenE σ` applied to a checked family. -/
def shortenAt {A B : CVTy} {s : CShape} (r : Res Δ T (.val A))
    (h : ∀ {Γ e}, CDerives Δ Γ e (.val A) →
      CDerives Δ Γ (BoCa.Fig16.LogRel.Core.shortenE s e) (.val B)) : Res Δ T (.val B) :=
  ⟨BoCa.Fig16.LogRel.Core.shortenE s r.e, r.F.map fun _ hd => h hd⟩

/-- `shorten_mut[σ, @a] V` / `shorten_imm[σ, @a] V`: `V : fam m @b σ` with `Δ ⊨ @a ⊑ @b`. -/
def shortenIt {A : CVTy} (_E : Env) (T : List CVTy) (sp : Span) (m : Mode) (s : CShape)
    (a : CLife) (r : Res Δ T (.val A)) : Except Error (Σ B : CVTy, Res Δ T (.val B)) := do
  let ⟨hσ⟩ ← plainShape sp s
  let some b := famLife m s A
    | err sp s!"`shorten` needs a family of borrows over its shape, but the operand has type `{ppVTy A}`"
  let ⟨hle⟩ ← needB sp (leB Δ a b) s!"cannot show `{ppLife a}` ⊑ `{ppLife b}` from the lifetime context"
  match m with
  | .mut =>
    if h : A = s.famTy mutM b then
      pure ⟨_, shortenAt (h ▸ r) fun hd => shortenE_wf formerMut hσ hd (leB_sound hle)⟩
    else err sp s!"`shorten_mut` needs `fam mut @ σ`, but the operand has type `{ppVTy A}`"
  | .imm =>
    if h : A = s.famTy immM b then
      pure ⟨_, shortenAt (h ▸ r) fun hd => shortenE_wf formerImm hσ hd (leB_sound hle)⟩
    else err sp s!"`shorten_imm` needs `fam imm @ σ`, but the operand has type `{ppVTy A}`"

end

end Frontend.Check
