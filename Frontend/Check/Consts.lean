import Frontend.Check.Steps

/-!
# Frontend — Check — constants and derived forms

Each constant (syntax-core §8, §8a) is one `CDerives` constructor at a consumed context, and each
derived form (§9) one Lean theorem concluding a `CDerives` judgment; the brackets give every
argument, so nothing is searched. A constant holds no operation, so its derivation is tied at
every effect context (`TiedDer.ofCDerives`, decided by `Expr.effFree`). A binder argument
(`withbor1['x, …]`, `fold_imm[F, 'y, …]`, `withbor_s_mut[σ, 'c, T]`,
`withbor_f2_*['c, 'a, 'b, …]`) is numbered by §3: `Δ.freshVar`, and `withbor_f2`'s internal `'a`,
`'b` are `Δ.freshVar` and `Δ.freshVar + 1`. Each side condition is decided by a `Bool` function of
`Frontend/Check/Decide.lean` and discharged by its soundness lemma.

A fold's shape argument is a type with the recursive position `X`, decoded to an `FShape` by
§5's canonical `dec`: maximal closed leaves, then `ref X`, `X`, `*` and `+`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives CDerivesAt CDerivesP Jdg VFree VOutlives VOutlivesLe FShape FD₁ mutM immM
  d_allocS d_freeS withborSM_wf withborSI_wf withborM2_wf withborI2_wf FamSide cbTy2 famTy2
  plainV Consumable consumeE consume_wf withborUE withbor1UTy withbor2UTy withbor3UTy withloadUTy
  sliceBorrowMUTy sliceBorrowIUTy closedAt consumeE_closed consumeE_effFree)
open BoCa.Fig16.LogRel.Core (ConstKind rowAt_nil)

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

open BoCa.Fig16.LogRel.Core (fixDTy unfoldSTy unfoldTy ConstKind) in
/-- `fixD` (`CDerives.fixD`): the `unfold` constant at the delay type's body, at its type `fixDTy`. -/
theorem tFixD {Ξ : BoCa.Fig16.LogRel.Core.EffCtx} {Δ : LifeCtx} {Γ : Ctx CVTy} {i : TInfo} {A S : CVTy}
    (hΓ : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TDerivesAt Ξ Δ Γ (.constK i (.val (fixDTy A S)) (.unfoldN (BoCa.Fig16.LogRel.Core.CTy.delayBody A) S))
      (.val (fixDTy A S)) := by
  have h := TDerivesAt.constK (Ξ := Ξ) (Δ := Δ) (info := i)
    (.unfoldN (BoCa.Fig16.LogRel.Core.CTy.delayBody A) S) (BoCa.Fig16.LogRel.Core.rowAt_nil Ξ)
    ⟨BoCa.Fig16.LogRel.Core.CTy.delayBody_nuOk A, BoCa.Fig16.LogRel.Core.CTy.BindsFresh.of_hasAll rfl S⟩ hΓ
  simp only [ConstKind.ty] at h
  rwa [unfoldTy, BoCa.Fig16.LogRel.Core.CTy.delayBody_instT] at h

open BoCa.Fig16.LogRel.Core (fixDTy unfoldSTy unfoldTy ConstKind) in
/-- `unfoldS` (`CDerives.unfoldS`): the `unfold` constant at the stream type's body, at `unfoldSTy`. -/
theorem tUnfoldS {Ξ : BoCa.Fig16.LogRel.Core.EffCtx} {Δ : LifeCtx} {Γ : Ctx CVTy} {i : TInfo} {A S : CVTy}
    (hΓ : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TDerivesAt Ξ Δ Γ (.constK i (.val (unfoldSTy A S)) (.unfoldN (BoCa.Fig16.LogRel.Core.CTy.streamBody A) S))
      (.val (unfoldSTy A S)) := by
  have h := TDerivesAt.constK (Ξ := Ξ) (Δ := Δ) (info := i)
    (.unfoldN (BoCa.Fig16.LogRel.Core.CTy.streamBody A) S) (BoCa.Fig16.LogRel.Core.rowAt_nil Ξ)
    ⟨BoCa.Fig16.LogRel.Core.CTy.streamBody_nuOk A, BoCa.Fig16.LogRel.Core.CTy.BindsFresh.of_hasAll rfl S⟩ hΓ
  simp only [ConstKind.ty] at h
  rwa [unfoldTy, BoCa.Fig16.LogRel.Core.CTy.streamBody_instT] at h

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- A constant: its node `mk j` at its judgment `j`, by its rule at every consumed context, which
reads no row. -/
def cDead {A : CVTy} (mk : Jdg → TExpr)
    (h : ∀ {Γ}, BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ → ∀ Ξ, TDerivesAt Ξ Δ Γ (mk (.val A)) (.val A)) :
    Except Error (Σ B : CVTy, Res Δ T (.val B)) :=
  pure ⟨A, mk (.val A), [], [], (Fam.dead T).map fun _ hd => TTied.ofAt (h hd)⟩

/-- A kernel constant (`ConstKind`), its side condition established: its node at its type at
`⊓Δ`, by `constK` at every consumed context, which ties no row. -/
def cConst (sp : Span) (k : ConstKind) (hk : k.OK Δ) : Except Error (Σ B : CVTy, Res Δ T (.val B)) :=
  cDead (A := k.ty Δ.meetOfDom) (fun j => .constK (at_ sp) j k) fun hd Ξ => .constK k (rowAt_nil Ξ) hk hd

/-- A constant whose rule is stated at `Ctx.Dead`: every slot dead. -/
def cDeadStrict {A : CVTy} (mk : Jdg → TExpr)
    (h : ∀ {Γ}, Ctx.Dead Γ → ∀ Ξ, TDerivesAt Ξ Δ Γ (mk (.val A)) (.val A)) :
    Except Error (Σ B : CVTy, Res Δ T (.val B)) :=
  pure ⟨A, mk (.val A), [], [], (Fam.deadStrict T).map fun _ hd => TTied.ofAt (h hd)⟩

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

/-- `Δ ⊨ @b` and `Δ ⊢ A ⊒ @b`: `withbor2`'s witness.  `[spec §23]` -/
def outlivesWitness (sp : Span) (b : CLife) (A : CVTy) :
    Except Error (PLift (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)) :=
  if hw : b.wf Δ = true then
    if ho : outlivesLeB Δ b A = true then pure ⟨⟨b, defines_of_wf hw, outlivesLeB_sound Δ b A ho⟩⟩
    else err sp s!"cannot show that `{ppVTy A}` outlives `{ppLife b}`"
  else err sp s!"the lifetime `{ppLife b}` is not defined here"

def needB (sp : Span) (b : Bool) (msg : String) : Except Error (PLift (b = true)) :=
  if h : b = true then pure ⟨h⟩ else err sp msg

/-- A derived form performs or handles no operation, decided. -/
def effFreeD (sp : Span) (e : CExpr) : Except Error (PLift (e.effFree = true)) :=
  needB sp e.effFree "internal error: a derived form performs or handles an operation"

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

/-- The finaliser of an unwinding borrow: the consume of its source, closed.  `[spec §19]` -/
def finaliser (sp : Span) (src : CVTy) :
    Except Error (PLift (Consumable src ∧ closedAt 0 (consumeE src) = true ∧ (consumeE src).effFree = true)) :=
  if h : consumableB src = true then
    pure ⟨consumableB_sound h, consumeE_closed (consumableB_sound h), consumeE_effFree src⟩
  else err sp (s!"the source `{ppVTy src}` is not consumable, so it cannot be finalised when " ++
    "the callback aborts")

/-- The finaliser's node: the source's consume. -/
def finNode (sp : Span) (src : CVTy) : TExpr := .consume (at_ sp) (.val (.lolli src .unit)) src

/-- The row of an unwinding callback: `Row.Unwind`.  `[spec §19]` -/
def unwindRow (sp : Span) (x : LifeVar) (S : CRow) : Except Error (PLift (S.Unwind x)) :=
  if h : Row.unwindB S x = true then pure ⟨Row.unwindB_sound h⟩
  else err sp ("the row of an unwinding borrow's callback has only abortive operations, of " ++
    "names other than 0, whose arguments outlive every lifetime and do not mention its lifetime")

/-- A shape all of whose leaves are plain. -/
def plainShape (sp : Span) (s : CShape) : Except Error (PLift (s.plain = true)) :=
  if h : s.plain = true then pure ⟨h⟩
  else err sp "a block borrow needs a shape whose leaves are plain (no lifetime, no `U`)"

/-! ### Constants -/

/-- The unwinding borrows: each at a consumed context, its finaliser the consume of its
source.  `[spec §19]` -/
def synConstU (E : Env) (Δ : LifeCtx) (T : List CVTy) (sp : Span) :
    Const → Except Error (Σ A : CVTy, Res Δ T (.val A))
  | .withbor1U _ A B r => do
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hsc⟩ ← needB sp (scopedB Δ A) s!"`{ppVTy A}` mentions a lifetime not in scope"
      let ⟨hS⟩ ← unwindRow sp x S
      let ⟨hdt, hdc, hde⟩ ← finaliser sp (.ref A)
      (cDeadStrict (fun j => .withborUD (at_ sp) j A B S [] S .refImm x (finNode sp (.ref A))) fun hd _ =>
        .withborUD .refImm x hd.toP hx (scopedB_sound hsc) h₁ h₂ hS (BoCa.Fig16.LogRel.Core.RowLe.refl S) (BoCa.Fig16.LogRel.Core.RowLe.nil S) hS.divB
          (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil)
          (.consume hdt hdc hde hd))
  | .withbor2U _ b A B r => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hside⟩ ← outlivesWitness sp b A
      let ⟨hS⟩ ← unwindRow sp x S
      let ⟨hdt, hdc, hde⟩ ← finaliser sp (.ref A)
      (cDeadStrict (fun j => .withborUD (at_ sp) j A B S [] S .refMut x (finNode sp (.ref A))) fun hd _ =>
        .withborUD .refMut x hd.toP hx hside h₁ h₂ hS (BoCa.Fig16.LogRel.Core.RowLe.refl S) (BoCa.Fig16.LogRel.Core.RowLe.nil S) hS.divB
          (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil)
          (.consume hdt hdc hde hd))
  | .withlocalU _ b A B r => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hside⟩ ← outlivesWitness sp b A
      let ⟨hS⟩ ← unwindRow sp x S
      let ⟨hP⟩ ← needB sp A.persistent
        s!"the contents `{ppVTy A}` of an unwinding local are not persistent, so its unwind cannot drop them"
      (cDeadStrict (fun j => .withlocal (at_ sp) j (.unwind S S) A B x) fun hd _ =>
        .withlocal (.unwind S S) x hd
          ⟨⟨hx, hside, h₁, h₂⟩, hP, hS, BoCa.Fig16.LogRel.Core.RowLe.refl S, hS.divB⟩)
  | .withbor3U a _ A B r => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hS⟩ ← unwindRow sp x S
      let ⟨hdt, hdc, hde⟩ ← finaliser sp (.mut a A)
      (cDeadStrict (fun j => .withborUD (at_ sp) j A B S [] S (.reborrow a) x (finNode sp (.mut a A)))
          fun hd _ =>
        .withborUD (.reborrow a) x hd.toP hx trivial h₁ h₂ hS (BoCa.Fig16.LogRel.Core.RowLe.refl S) (BoCa.Fig16.LogRel.Core.RowLe.nil S) hS.divB
          (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil)
          (.consume hdt hdc hde hd))
  | .withloadU a _ A B r => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hS⟩ ← unwindRow sp x S
      (cConst sp (.withloadU a A B S x) ⟨hx, h₁, h₂, hS⟩)
  | .sliceBorrowMutU _ b A B r => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨_, h₁, h₂⟩⟩ ← freshFor (Δ := Δ) sp x A B
      let ⟨hA⟩ ← outlivesWitness sp b A
      let ⟨hB⟩ ← outlivesWitness sp b B
      let ⟨hS⟩ ← unwindRow sp x S
      let ⟨hdt, hdc, hde⟩ ← finaliser sp (.fam (.ref A))
      (cDeadStrict (fun j => .sliceBorrowMU (at_ sp) j A B S x (finNode sp (.fam (.ref A))))
        fun hd _ => .sliceBorrowMU x hd.toP hA hB h₁ h₂ hS
          (.consume hdt hdc hde hd))
  | .sliceBorrowImmU _ b A B r => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨_, h₁, h₂⟩⟩ ← freshFor (Δ := Δ) sp x A B
      let ⟨hsc⟩ ← needB sp (scopedB Δ A) s!"`{ppVTy A}` mentions a lifetime not in scope"
      let ⟨hA⟩ ← outlivesWitness sp b A
      let ⟨hB⟩ ← outlivesWitness sp b B
      let ⟨hS⟩ ← unwindRow sp x S
      let ⟨hdt, hdc, hde⟩ ← finaliser sp (.fam (.ref A))
      (cDeadStrict (fun j => .sliceBorrowIU (at_ sp) j A B S x (finNode sp (.fam (.ref A))))
        fun hd _ => .sliceBorrowIU x hd.toP (scopedB_sound hsc) hA hB h₁ h₂ hS
          (.consume hdt hdc hde hd))
  | _ => err sp "internal error: not an unwinding borrow"

/-! ### Unwinding borrows with a written finaliser  `[spec §78]` -/

/-- The node of an unwinding borrow whose finaliser `d` is written (SPEC §78), from `d`'s check at
`U(src ⊸ F_∅ 1)`: the rule's context is dead up to persistent slots, so every slot `d` uses is
persistent (`d` may name them, K1.3b).  [spec §78] -/
def finRes {src A : CVTy} (dsp : Span) (mk : TExpr → TExpr)
    (rd : Res Δ T (.val (.thunk (.arr src (effOf [] .unit)))))
    (h : ∀ {Γ}, BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ →
      TTied rd.pins rd.sigs Δ Γ rd.t (.val (.thunk (.arr src (effOf [] .unit)))) →
      TTied rd.pins rd.sigs Δ Γ (mk rd.t) (.val A)) :
    Except Error (Σ B : CVTy, Res Δ T (.val B)) :=
  if hs : usedSat BoCa.Fig16.LogRel.Core.VTy.persistent T rd.F.u = true then
    pure ⟨A, mk rd.t, rd.sigs, rd.pins,
      (rd.F.restrict BoCa.Fig16.LogRel.Core.VTy.persistent hs).map fun _ ⟨hd, hp⟩ =>
        h (deadP_of_live hp) hd⟩
  else err dsp ("the finaliser of an unwinding borrow holds a variable that is not persistent: " ++
    "it runs at the borrow's context, where only persistent variables are live")

/-- `withbor{1,2,3}u[…] unwind (d)` at `Σ_D = ∅`, `Σ_M = Σ` (SPEC §78, §19's rule): the source's
type, the callback's row, and the node given `d`'s check at the source at the empty row. The
premises are §19's, decided as for the consume finaliser (`synConstU`).  `[spec §78]` -/
def synConstFin (E : Env) (Δ : LifeCtx) (T : List CVTy) (sp dsp : Span) :
    Const → Except Error (Σ src : CVTy, CRow ×
      (Res Δ T (.val (.thunk (.arr src (effOf [] .unit)))) →
        Except Error (Σ A : CVTy, Res Δ T (.val A))))
  | .withbor1U _ A B r => do
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hsc⟩ ← needB sp (scopedB Δ A) s!"`{ppVTy A}` mentions a lifetime not in scope"
      let ⟨hS⟩ ← unwindRow sp x S
      pure ⟨.ref A, S, fun rd =>
        finRes dsp (fun td => .withborUD (at_ sp)
            (.val (BoCa.Fig16.LogRel.Core.LendUKind.refImm.ty x Δ.meetOfDom A B S S)) A B S [] S
            .refImm x td) rd
          fun hΓ h => TTied.withborUFin (at_ sp) .refImm x hΓ hx (scopedB_sound hsc) h₁ h₂ hS h⟩
  | .withbor2U _ b A B r => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hside⟩ ← outlivesWitness sp b A
      let ⟨hS⟩ ← unwindRow sp x S
      pure ⟨.ref A, S, fun rd =>
        finRes dsp (fun td => .withborUD (at_ sp)
            (.val (BoCa.Fig16.LogRel.Core.LendUKind.refMut.ty x Δ.meetOfDom A B S S)) A B S [] S
            .refMut x td) rd
          fun hΓ h => TTied.withborUFin (at_ sp) .refMut x hΓ hx hside h₁ h₂ hS h⟩
  | .withbor3U a _ A B r => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hS⟩ ← unwindRow sp x S
      pure ⟨.mut a A, S, fun rd =>
        finRes dsp (fun td => .withborUD (at_ sp)
            (.val ((BoCa.Fig16.LogRel.Core.LendUKind.reborrow a).ty x Δ.meetOfDom A B S S)) A B S []
            S (.reborrow a) x td) rd
          fun hΓ h => TTied.withborUFin (at_ sp) (.reborrow a) x hΓ hx trivial h₁ h₂ hS h⟩
  | _ => err sp "`unwind (d)` is the finaliser of `withbor1u`, `withbor2u` or `withbor3u` only"

/-- The type and derivations of a constant or derived form (syntax-core §8, §8a, §9). -/
def synConst (E : Env) (Δ : LifeCtx) (T : List CVTy) (sp : Span) :
    Const → Except Error (Σ A : CVTy, Res Δ T (.val A))
  | .alloc A => do
      let A ← E.elabV Δ A
      (cConst sp (.alloc A) trivial)
  | .free A => do
      let A ← E.elabV Δ A
      (cConst sp (.free A) trivial)
  | .swap A B => do
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      (cConst sp (.swap A B) trivial)
  | .copy a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.copy a A) trivial)
  | .copyBang A => do
      let A ← E.elabV Δ A
      (cConst sp (.copyBang A) trivial)
  | .releaseImm a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.releaseImm a A) trivial)
  | .releaseMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.releaseMut a A) trivial)
  | .releaseUnk => (cConst sp .releaseUnk trivial)
  | .tokMint => (cConst sp .tokMint trivial)
  | .tokBurn => (cConst sp .tokBurn trivial)
  | .releaseBang A => do
      let A ← E.elabV Δ A
      (cConst sp (.releaseBang A) trivial)
  | .withbor1 _ A B => do
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hsc⟩ ← needB sp (scopedB Δ A) s!"`{ppVTy A}` mentions a lifetime not in scope"
      (cConst sp (.withbor1 A B x) ⟨hx, (scopedB_sound hsc), h₁, h₂⟩)
  | .withbor2 _ b A B => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hside⟩ ← outlivesWitness sp b A
      (cConst sp (.withbor2 A B x) ⟨hx, hside, h₁, h₂⟩)
  | .withlocal _ b A B => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨hside⟩ ← outlivesWitness sp b A
      (cDeadStrict (fun j => .withlocal (at_ sp) j .plain A B x) fun hd _ =>
        .withlocal .plain x hd ⟨hx, hside, h₁, h₂⟩)
  | .withlocalLoop _ b A S B R => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let S ← E.elabV Δ S
      let B ← E.elabV Δ B
      let R ← E.elabV Δ R
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      let ⟨⟨_, h₃, h₄⟩⟩ ← freshFor (Δ := Δ) sp x S R
      let ⟨hside⟩ ← outlivesWitness sp b A
      (cDeadStrict (fun j => .withlocal (at_ sp) j (.loop A S B R) A B x) fun hd _ =>
        .withlocal (.loop A S B R) x hd ⟨⟨hx, hside, h₁, h₂⟩, h₃, h₄⟩)
  | .withbor3 a _ A B => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      (cConst sp (.withbor3 a A B x) ⟨hx, h₁, h₂⟩)
  | .withload a _ A B => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨hx, h₁, h₂⟩⟩ ← freshFor sp x A B
      (cConst sp (.withload a A B x) ⟨hx, h₁, h₂⟩)
  | .withswap a A B => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      (cConst sp (.withswap a A B) trivial)
  | .foldImm F _ c R => do
      let ⟨G, hW, hG⟩ ← elabFShape E Δ sp F
      let c ← E.elabL Δ c
      let R ← E.elabV Δ R
      let y := Δ.freshVar
      let ⟨hyM⟩ ← needB sp (!vfreeB y (.mu G.ty)) s!"the binder {ppLVar y} occurs in the shape"
      let ⟨hyR⟩ ← needB sp (!vfreeB y R) s!"the binder {ppLVar y} occurs in `{ppVTy R}`"
      let ⟨hR⟩ ← needB sp (outlivesAllB R) (s!"`fold_imm`'s result `{ppVTy R}` must outlive " ++
        "every lifetime: no `U`, `unk`, `imm`, `mut` or `box`")
      (cConst sp (.foldImm G y c R) ⟨hW, hG, (not_vfree_of_vfreeB (by simpa using hyM)), (not_vfree_of_vfreeB (by simpa using hyR)), (outlivesAllB_sound R hR)⟩)
  | .foldOwn F R => do
      let ⟨G, hW, hG⟩ ← elabFShape E Δ sp F
      let R ← E.elabV Δ R
      (cConst sp (.foldOwn G R) ⟨hW, hG⟩)
  | .foldReuse F R => do
      let ⟨G, hW, hG⟩ ← elabFShape E Δ sp F
      let R ← E.elabV Δ R
      (cConst sp (.foldReuse G R) ⟨hW, hG⟩)
  | .fixd A S => do
      let A ← E.elabV Δ A
      let S ← E.elabV Δ S
      (cDead (fun j => .constK (at_ sp) j (.unfoldN (BoCa.Fig16.LogRel.Core.CTy.delayBody A) S)) fun hd _ =>
        tFixD hd)
  | .unfoldS A S => do
      let A ← E.elabV Δ A
      let S ← E.elabV Δ S
      (cDead (fun j => .constK (at_ sp) j (.unfoldN (BoCa.Fig16.LogRel.Core.CTy.streamBody A) S)) fun hd _ =>
        tUnfoldS hd)
  | .unfold C S => do
      let C' ← E.elabC Δ C
      let S ← E.elabV Δ S
      match C' with
      | .nu B =>
        if hB : CTy.nuOkB B = true then
          if hS : CTy.bindsFreshB B S = true then
            (cConst sp (.unfoldN B S) ⟨(CTy.nuOkB_sound B hB), (CTy.bindsFreshB_sound B S hS)⟩)
          else err C.span s!"`unfold[C, S]` needs the state type `{E.ppV S}` to mention no lifetime bound by a `forall` observation of `{E.ppC C'}`"
        else err C.span s!"`unfold[C, S]` needs each observation of `{E.ppC C'}` to have `U X` only under `*` and `+`, and no `forall` observation to bind a lifetime free elsewhere in it"
      | _ => err C.span s!"`unfold[C, S]` needs a `nu` type, but `C` is `{E.ppC C'}`"
  | .lit c => (cConst sp (.lit c) trivial)
  | .host op => (cConst sp (.hostOp op) trivial)
  | .allocS σ => do
      let s ← E.elabS Δ σ
      let ⟨he⟩ ← effFreeD sp (BoCa.Fig16.LogRel.Core.allocS s)
      (cDeadStrict (fun j => .allocS (at_ sp) j s) fun hd _ => .allocS s he hd)
  | .freeS σ => do
      let s ← E.elabS Δ σ
      let ⟨he⟩ ← effFreeD sp (BoCa.Fig16.LogRel.Core.freeS s)
      (cDeadStrict (fun j => .freeS (at_ sp) j s) fun hd _ => .freeS s he hd)
  | .withborS m σ _ T' => do
      let s ← E.elabS Δ σ
      let T' ← E.elabV Δ T'
      let ⟨hσ⟩ ← plainShape sp s
      let ⟨hT⟩ ← needB sp (plainV T') s!"a block borrow's result `{ppVTy T'}` must be plain"
      let ⟨hΔ⟩ ← needB sp (okB Δ.entries) "the lifetime context is not well scoped"
      let c := Δ.freshVar
      let ⟨hc⟩ ← needB sp (Δ.find? c).isNone s!"{ppLVar c} is already bound"
      let ⟨hcl⟩ ← needB sp (closedAt 0 (BoCa.Fig16.LogRel.Core.withborS s)) "internal error: a block borrow is not closed"
      let ⟨he⟩ ← effFreeD sp (BoCa.Fig16.LogRel.Core.withborS s)
      match m with
      | .mut => (cDeadStrict (fun j => .withborSM (at_ sp) j s c T') fun hd _ =>
          .withborSM s c T' hσ hT (by simpa [LifeCtx.Ok] using hΔ) (by simpa using hc) hcl he hd)
      | .imm => (cDeadStrict (fun j => .withborSI (at_ sp) j s c T') fun hd _ =>
          .withborSI s c T' hσ hT (by simpa [LifeCtx.Ok] using hΔ) (by simpa using hc) hcl he hd)
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
      let ⟨he⟩ ← effFreeD sp BoCa.Fig16.LogRel.Core.withborF2
      (cDeadStrict (fun j => .withborF2M (at_ sp) j c x y A B T') fun hd _ =>
        .withborF2M s hA (outlivesB_sound _ _ _ hBo) (outlivesB_sound _ _ _ hTo) he hd)
  | .arrayNew A => do
      let A ← E.elabV Δ A
      (cConst sp (.arrNew A) trivial)
  | .arrayFree A => do
      let A ← E.elabV Δ A
      (cConst sp (.arrFree A) trivial)
  | .arraySize A => do
      let A ← E.elabV Δ A
      (cConst sp (.arrSize A) trivial)
  | .arrayReplace A => do
      let A ← E.elabV Δ A
      (cConst sp (.arrReplace A) trivial)
  | .arrayLen a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.arrLen a A) trivial)
  | .arrayGet a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.arrGet a A) trivial)
  | .arrayCopy a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.arrCopy a A) trivial)
  | .arrayRelease a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.arrRelease a A) trivial)
  | .countFold S => do
      let S ← E.elabV Δ S
      (cConst sp (.countFold S) trivial)
  | .countTry S T => do
      let S ← E.elabV Δ S
      let T ← E.elabV Δ T
      (cConst sp (.countTry S T) trivial)
  | .boundedFix A C => do
      let A ← E.elabV Δ A
      let C ← E.elabC Δ C
      (cConst sp (.boundedFix A C) trivial)
  | .sliceBorrowMut _ b A B => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨_, h₁, h₂⟩⟩ ← freshFor (Δ := Δ) sp x A B
      let ⟨hA⟩ ← outlivesWitness sp b A
      let ⟨hB⟩ ← outlivesWitness sp b B
      (cConst sp (.sliceBorrowM A B x) ⟨hA, hB, h₁, h₂⟩)
  | .sliceBorrowImm _ b A B => do
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      let B ← E.elabV Δ B
      let x := Δ.freshVar
      let ⟨⟨_, h₁, h₂⟩⟩ ← freshFor (Δ := Δ) sp x A B
      let ⟨hsc⟩ ← needB sp (scopedB Δ A) s!"`{ppVTy A}` mentions a lifetime not in scope"
      let ⟨hA⟩ ← outlivesWitness sp b A
      let ⟨hB⟩ ← outlivesWitness sp b B
      (cConst sp (.sliceBorrowI A B x) ⟨(scopedB_sound hsc), hA, hB, h₁, h₂⟩)
  | .sliceGetMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceGetM a A) trivial)
  | .sliceLenMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceLenM a A) trivial)
  | .sliceSplitImm a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceSplitI a A) trivial)
  | .sliceSplitMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceSplitM a A) trivial)
  | .sliceEmptyImm a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceEmptyI a A) trivial)
  | .sliceEmptyMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceEmptyM a A) trivial)
  | .arrayEmpty A => do
      let A ← E.elabV Δ A
      (cConst sp (.arrEmpty A) trivial)
  | .sliceReplaceMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceReplaceM a A) trivial)
  | .sliceSwapMut a A => do
      let a ← E.elabL Δ a
      let A ← E.elabV Δ A
      (cConst sp (.sliceSwapM a A) trivial)
  | .sliceCopyMut a b A => do
      let a ← E.elabL Δ a
      let b ← E.elabL Δ b
      let A ← E.elabV Δ A
      if hA : A.persistent = true then
        (cConst sp (.sliceCopyM a b A) hA)
      else err sp s!"`slice_copy_mut` copies values of a persistent type, and `{ppVTy A}` is not one"
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
      let ⟨he⟩ ← effFreeD sp BoCa.Fig16.LogRel.Core.withborF2
      (cDeadStrict (fun j => .withborF2I (at_ sp) j c x y A B T') fun hd _ =>
        .withborF2I s (scopedB_sound hA) (scopedB_sound hB) (outlivesB_sound _ _ _ hBo)
          (outlivesB_sound _ _ _ hTo) he hd)
  | c@(.withbor1U ..) | c@(.withbor2U ..) | c@(.withbor3U ..) | c@(.withloadU ..) | c@(.withlocalU ..)
  | c@(.sliceBorrowMutU ..) | c@(.sliceBorrowImmU ..) => synConstU E Δ T sp c

/-- The lifetime of a family at a shape: the lifetime of its first leaf. -/
def famLife (M : Mode) : CShape → CVTy → Option CLife
  | .leaf _, .mut b _ => if M matches .mut then some b else none
  | .leaf _, .imm b _ => if M matches .imm then some b else none
  | .node s _, .tensor A _ => famLife M s A
  | _, _ => none

/-- `shortenE σ` applied to a checked family, as typed nodes (`TTied.shortenT`). -/
def shortenAt {M : CLife → CVTy → CVTy} {leaf : TInfo → CLife → CLife → CVTy → TExpr → TExpr}
    (i : TInfo) {a b : CLife} {s : CShape} (r : Res Δ T (.val (s.famTy M b)))
    (sub : ∀ {p : Pins} {s : CRow} {Δ : LifeCtx} {Γ : Ctx CVTy} {t : TExpr} {a b : CLife} {A : CVTy},
      TTied p s Δ Γ t (.val (M b A)) → Δ.EntailsLe a b → TTied p s Δ Γ (leaf i a b A t) (.val (M a A)))
    (hle : Δ.EntailsLe a b) : Res Δ T (.val (s.famTy M a)) :=
  ⟨TTied.shortenT M leaf i a b s r.F.u r.t, r.sigs, r.pins,
    r.F.mapB fun _ hb hd => TTied.shorten i sub r.F.u (btw_usedLive r.F.hu hb) r.covers hd hle⟩

/-- `shorten_mut[σ, @a] V` / `shorten_imm[σ, @a] V`: `V : fam m @b σ` with `Δ ⊨ @a ⊑ @b`. -/
def shortenIt {A : CVTy} (_E : Env) (T : List CVTy) (sp : Span) (m : Mode) (s : CShape)
    (a : CLife) (r : Res Δ T (.val A)) : Except Error (Σ B : CVTy, Res Δ T (.val B)) := do
  let ⟨_⟩ ← plainShape sp s
  let some b := famLife m s A
    | err sp s!"`shorten` needs a family of borrows over its shape, but the operand has type `{ppVTy A}`"
  let ⟨hle⟩ ← needB sp (leB Δ a b) s!"cannot show `{ppLife a}` ⊑ `{ppLife b}` from the lifetime context"
  match m with
  | .mut =>
    match convVal (at_ sp) (s.famTy mutM b) ⟨A, r⟩ with
    | some r =>
      pure ⟨_, shortenAt (M := mutM)
        (leaf := fun i a b A t => .mutSub i (.val (.mut a A)) a b A t) (at_ sp) r
        (fun h' hle' => TTied.mutSub _ h' hle') (leB_sound hle)⟩
    | none => err sp s!"`shorten_mut` needs `fam mut @ σ`, but the operand has type `{ppVTy A}`"
  | .imm =>
    match convVal (at_ sp) (s.famTy immM b) ⟨A, r⟩ with
    | some r =>
      pure ⟨_, shortenAt (M := immM)
        (leaf := fun i a b A t => .immSub i (.val (.imm a A)) a b A t) (at_ sp) r
        (fun h' hle' => TTied.immSub _ h' hle') (leB_sound hle)⟩
    | none => err sp s!"`shorten_imm` needs `fam imm @ σ`, but the operand has type `{ppVTy A}`"

end

end Frontend.Check
