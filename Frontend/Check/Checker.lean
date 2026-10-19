import Frontend.Check.Pin
import Frontend.Check.Kinds

/-!
# Frontend — Check — the bidirectional checker

`synV`/`chkV` check a value-judged expression, synthesizing its type or against a given one;
`synC`/`chkC` do the same for computations (syntax-core §6, §11). Each case applies one rule
builder of `Frontend/Check/Rules.lean` (or `Consts.lean`) to the checked premises, so a success
is a `Res`: the erasure with its `CDerives` derivations. Names are resolved on the way: a
variable to its de Bruijn slot (§6.3), a lifetime name to its `LifeVar` (§3), a `def` to its
key's checked body, placed at the use (`useDef`, SPEC §3). Variables owed to the computation being checked (`Env.own`,
SPEC §12) are passed to its tail positions and dropped before each terminal computation that
leaves them unused (`dropOwed`).

The recursion is structural on a fuel argument that bounds the depth of the call tree;
running out is an error, not an assumption.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives Jdg)

/-- A handler of another name around a computation that may tick is typed only by the kernel's
tail-resuming rule, which the frontend does not elaborate to (decision 68). -/
def divHandleMsg : String :=
  "a handler around a computation that may tick (`Div`) is typed only when its clauses " ++
    "resume `κ` in tail"

/-! ### `def`s, checked once per key  `[spec §10]`

A `def` is checked once per key: the declaration, its type arguments, the lifetime context, and the
context `Tc` of externs it is checked at. A use whose context is `Tc` under more slots places the
checked body there (`rUse`), the slots between the externs and the use unused by the body and
absorbed where its absorption holds (`TExpr.absF`). The cache holds each key's checked body; it
is state threaded through the checker (`CheckM`), and an alternative that fails leaves it as it
was (`attempt`). -/

/-- A `def`'s body checked at a key. -/
structure DefEntry where
  decl : Nat
  targs : List CVTy
  Δ : LifeCtx
  Tc : List CVTy
  A : CVTy
  r : Res Δ Tc (.val A)
  ab : Option AbsF
  hab : ab = r.t.absF Δ

/-- The checked bodies of the program's `def`s, by key. -/
abbrev DefCache := List DefEntry

/-- The checker's monad: an error, or a result with the cache. -/
abbrev CheckM := StateT DefCache (Except Error)

/-- Run `x`; on an error, the cache as it was before. -/
def attempt {α : Type} (x : CheckM α) : CheckM (Except Error α) := fun c =>
  match x c with
  | .ok (a, c') => .ok (.ok a, c')
  | .error e => .ok (.error e, c)

/-- A key's checked body, found for a use at `T`: its context `Tc` is `T` with `m` slots dropped. -/
structure DefHit (Δ : LifeCtx) (T : List CVTy) where
  A : CVTy
  Tc : List CVTy
  m : Nat
  hT : T.drop m = Tc
  r : Res Δ Tc (.val A)
  ab : Option AbsF
  hab : ab = r.t.absF Δ

/-- The entry, when it is the key's at the use's context `T`. -/
def DefEntry.hit? (e : DefEntry) (decl : Nat) (targs : List CVTy) (Δ : LifeCtx) (T : List CVTy) :
    Option (DefHit Δ T) :=
  if e.decl == decl && e.targs == targs then
    if hΔ : e.Δ = Δ then
      if hT : T.drop (T.length - e.Tc.length) = e.Tc then
        some ⟨e.A, e.Tc, _, hT, hΔ ▸ e.r, e.ab, by subst hΔ; exact e.hab⟩
      else none
    else none
  else none

/-! ### The checker -/

set_option maxHeartbeats 400000 in
mutual

/-- Synthesize the type of a value-judged expression. -/
def synV : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Val →
    CheckM (Σ A : CVTy, Res Δ T (.val A))
  | 0, _, _, _, v => err v.span "expression nested too deeply"
  | n + 1, E, Δ, T, v => let E := E.forVal; match v with
    | .var sp x =>
      match lookupVar x E.vars with
      | some i =>
        match h : T[i]? with
        | some A => pure ⟨A, rVar { sp, name := x } i A h⟩
        | none => err sp "internal error: variable out of range"
      | none =>
        match E.scope.findDef x with
        | none =>
          if E.scope.hasExtern x then
            err sp (s!"the capability `{x}` is not in scope: a `def` may use only persistent " ++
              "externs; take the capability as an argument (SPEC §11)")
          else err sp s!"unknown variable `{x}`"
        | some d =>
          if d.params.isEmpty then useDef n E Δ T sp x d [] []
          else err sp s!"`{x}` takes {d.params.length} type argument(s): write `{x}[…]`"
    | .clone sp x =>
      -- `clone(x)`: the variable, its node recording the written copy (SPEC §10).
      match lookupVar x E.vars with
      | some i =>
        match h : T[i]? with
        | some A => pure ⟨A, rVar { sp, name := x, clone := true } i A h⟩
        | none => err sp "internal error: variable out of range"
      | none => synV n E Δ T (.var sp x)
    | .defApp sp x args =>
      match E.scope.findDef x with
      | none => err sp s!"unknown definition `{x}`"
      | some d =>
        if d.params.length = args.length then do
          let targs ← liftM (m := Except Error) (args.mapM (E.elabV Δ))
          useDef n E Δ T sp x d ((d.params.map (·.name)).zip targs) targs
        else err sp s!"`{x}` takes {d.params.length} type argument(s), not {args.length}"
    | .unit sp => pure ⟨.unit, rUnit (at_ sp)⟩
    | .pair sp V W => do
      let ⟨_, r₁⟩ ← synV n E Δ T V
      let ⟨_, r₂⟩ ← synV n E Δ T W
      if h : overlapOK T r₁.F.u r₂.F.u = true then pure ⟨_, rPair (at_ sp) r₁ r₂ h⟩
      else throw (splitErr E T sp r₁.F.u r₂.F.u)
    | .inl sp _ => err sp "the type of `inl V` cannot be synthesized: ascribe it, `(inl V : A + B)`"
    | .inr sp _ => err sp "the type of `inr V` cannot be synthesized: ascribe it, `(inr V : A + B)`"
    | .thunk sp M => do
      let ⟨C, r⟩ ← synC n (E.push none) Δ (.unit :: T) M
      match C, r with
      | .ret _, r => match rThunkF (at_ sp) r with
        | some r' => pure ⟨_, r'⟩
        | none => err sp "internal error: a dead binder is used"
      | C, _ => err sp s!"`thunk M` needs `M : F A`, but `M : {E.ppC C}`; use `thunkv`"
    | .thunkv sp N => do
      let ⟨C, r⟩ ← synC n E Δ T N
      if hC : C.isRet = false then
        match rThunkV (at_ sp) hC r with
        | some r' => pure ⟨_, r'⟩
        | none => err sp thunkvLam
      else err sp s!"`thunkv N` needs `N` not of type `F A`, but `N : {E.ppC C}`; use `thunk`"
    | .bangThunk sp M => do
      let ⟨C, r⟩ ← synC n (E.push none) Δ (.unit :: T) M
      match C, r with
      | .ret _, r => match rBangThunkF (at_ sp) r with
        | .ok r' => pure ⟨_, r'⟩
        | .error i => throw (notBang E T sp i)
      | C, _ => err sp s!"`!thunk M` needs `M : F A`, but `M : {E.ppC C}`; use `!thunkv`"
    | .bangThunkv sp N => do
      let ⟨C, r⟩ ← synC n E Δ T N
      if hC : C.isRet = false then
        match rBangThunkV (at_ sp) hC r with
        | .ok r' => pure ⟨_, r'⟩
        | .error i => throw (notBang E T sp i)
      else err sp s!"`!thunkv N` needs `N` not of type `F A`, but `N : {E.ppC C}`; use `!thunk`"
    | .unbang sp V => do
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .bang _, r => pure ⟨_, rBangE (at_ sp) r⟩
      | A, _ => err sp s!"`unbang V` needs `V : !A`, but `V : {E.ppV A}`"
    | .boxed sp a V => do
      let al ← E.elabL Δ a
      let ⟨_, r⟩ ← synV n E Δ T V
      pure ⟨_, ← boxIt E T sp al r⟩
    | .unbox sp V => do
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .box _ _, r => pure ⟨_, rBoxE (at_ sp) r⟩
      | A, _ => err sp s!"`unbox V` needs `V : box @ A`, but `V : {E.ppV A}`"
    | .sub sp V a => do
      let al ← E.elabL Δ a
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .imm b _, r =>
        if h : leB Δ al b = true then pure ⟨_, rImmSub (at_ sp) al h r⟩
        else err sp s!"cannot show `{E.ppL al}` ⊑ `{E.ppL b}` from the lifetime context"
      | .mut b _, r =>
        if h : leB Δ al b = true then pure ⟨_, rMutSub (at_ sp) al h r⟩
        else err sp s!"cannot show `{E.ppL al}` ⊑ `{E.ppL b}` from the lifetime context"
      | A, _ => err sp s!"`(V :> @)` needs `V : imm @ A` or `mut @ A`, but `V : {E.ppV A}`"
    | .roll sp _ => err sp "the type of `roll V` cannot be synthesized: ascribe it, `(roll V : mu X. A)`"
    | .unroll sp V => do
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .mu _, r => pure ⟨_, rUnroll (at_ sp) r⟩
      | A, _ => err sp s!"`unroll V` needs `V : mu X. A`, but `V : {E.ppV A}`"
    | .run sp M => do
      let ⟨C, r⟩ ← synC n E Δ T M
      match C, r with
      | .ret _, r => pure ⟨_, rOfRet (at_ sp) r⟩
      | C, _ => err sp s!"`run M` needs `M : F A`, but `M : {E.ppC C}`"
    | .app sp V W => do
      let ⟨A, rf⟩ ← synV n E Δ T V
      match A, rf with
      | .thunk (.arr A (.ret _)), rf => do
        let ra ← chkV n E Δ T W A
        if h : overlapOK T ra.F.u rf.F.u = true then pure ⟨_, rLolliE (at_ sp) rf ra h⟩
        else throw (splitErr E T sp ra.F.u rf.F.u)
      | A, _ => err V.span s!"this is applied, so it must have a type `A => B`, but it has type `{E.ppV A}`"
    | .inst sp V a => do
      let al ← E.elabL Δ a
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .thunk (.all _ b (.ret _)), r =>
        if h : ltB Δ al b = true then pure ⟨_, rAllEV (at_ sp) al h r⟩
        else err sp s!"cannot show `{E.ppL al}` ⊏ `{E.ppL b}` from the lifetime context"
      | A, _ => err V.span s!"this is instantiated, so it must have a type `all 'x < @. A`, but it has type `{E.ppV A}`"
    | .ascribe _ V A => do
      let A' ← E.elabV Δ A
      let r ← chkV n E Δ T V A'
      pure ⟨A', r⟩
    | .const sp c => synConst E Δ T sp c
    | .shorten sp m σ a V => do
      let s ← E.elabS Δ σ
      let al ← E.elabL Δ a
      let ⟨_, r⟩ ← synV n E Δ T V
      shortenIt E T sp m s al r
    | .lend sp x m => err sp (s!"`{if m == .mut then "&mut " else "&"}{x.name}` lends a place to " ++
        "one call: it may appear only in the head `M` of `y <- M; N` (SPEC §11)")
    | .sugar sp _ => err sp "internal error: a surface form was not elaborated before checking"
    | .mark sp k V => do
      let ⟨A, r⟩ ← synV n E Δ T V
      pure ⟨A, ← markIt sp k r⟩

/-- Check a value-judged expression against a type. -/
def chkV : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Val → (A : CVTy) →
    CheckM (Res Δ T (.val A))
  | 0, _, _, _, v, _ => err v.span "expression nested too deeply"
  | n + 1, E, Δ, T, v, A => let E := E.forVal; match v with
    | .pair sp V W =>
      match A with
      | .tensor A B => do
        let r₁ ← chkV n E Δ T V A
        let r₂ ← chkV n E Δ T W B
        if h : overlapOK T r₁.F.u r₂.F.u = true then pure (rPair (at_ sp) r₁ r₂ h)
        else throw (splitErr E T sp r₁.F.u r₂.F.u)
      | A => err sp s!"a pair is checked against `{E.ppV A}`, which is not a `*` type"
    | .inl sp V =>
      match A with
      | .sum A B => do pure (rInl (at_ sp) B (← chkV n E Δ T V A))
      | A => err sp s!"`inl V` is checked against `{E.ppV A}`, which is not a `+` type"
    | .inr sp V =>
      match A with
      | .sum A B => do pure (rInr (at_ sp) A (← chkV n E Δ T V B))
      | A => err sp s!"`inr V` is checked against `{E.ppV A}`, which is not a `+` type"
    | .thunk sp M =>
      match A with
      | .thunk (.ret A) => do
        let r ← chkC n (E.push none) Δ (.unit :: T) M (.ret A)
        match rThunkF (at_ sp) r with
        | some r' => pure r'
        | none => err sp "internal error: a dead binder is used"
      | A => err sp s!"`thunk M` is checked against `{E.ppV A}`, which is not `U (F A)`"
    | .thunkv sp N =>
      match A with
      | .thunk C =>
        if hC : C.isRet = false then do
          let r ← chkC n E Δ T N C
          match rThunkV (at_ sp) hC r with
          | some r' => pure r'
          | none => err sp thunkvLam
        else err sp s!"`thunkv N` is checked against `{E.ppV A}`: use `thunk` at `U (F A)`"
      | A => err sp s!"`thunkv N` is checked against `{E.ppV A}`, which is not a `U` type"
    | .bangThunk sp M =>
      match A with
      | .bang (.thunk (.ret A)) => do
        let r ← chkC n (E.push none) Δ (.unit :: T) M (.ret A)
        match rBangThunkF (at_ sp) r with
        | .ok r' => pure r'
        | .error i => throw (notBang E T sp i)
      | A => err sp s!"`!thunk M` is checked against `{E.ppV A}`, which is not `!U (F A)`"
    | .bangThunkv sp N =>
      match A with
      | .bang (.thunk C) =>
        if hC : C.isRet = false then do
          let r ← chkC n E Δ T N C
          match rBangThunkV (at_ sp) hC r with
          | .ok r' => pure r'
          | .error i => throw (notBang E T sp i)
        else err sp s!"`!thunkv N` is checked against `{E.ppV A}`: use `!thunk` at `!U (F A)`"
      | A => err sp s!"`!thunkv N` is checked against `{E.ppV A}`, which is not a `!U` type"
    | .unbang sp V => do pure (rBangE (at_ sp) (← chkV n E Δ T V (.bang A)))
    | .boxed sp a V =>
      match A with
      | .box b A => do
        let al ← E.elabL Δ a
        if hab : al = b then do
          let r ← chkV n E Δ T V A
          pure (hab ▸ (← boxIt E T sp al r))
        else err sp s!"`boxed[{E.ppL al}]` is checked against `box {E.ppL b} …`"
      | A => err sp s!"`boxed[@] V` is checked against `{E.ppV A}`, which is not a `box` type"
    | .roll sp V =>
      match A with
      | .mu A =>
        if hA : VTy.noMutB 0 A = true then
          if hc : VTy.clB 0 (.mu A) = true then do
            pure (rRoll (at_ sp) hA hc (← chkV n E Δ T V (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)))
          else err sp s!"`roll` at `{E.ppV (.mu A)}`, which is not closed"
        else err sp s!"`roll` at `{E.ppV (.mu A)}`, whose variable occurs under `mut`"
      | A => err sp s!"`roll V` is checked against `{E.ppV A}`, which is not a `mu` type"
    | .run sp M => do pure (rOfRet (at_ sp) (← chkC n E Δ T M (.ret A)))
    | .mark sp k V => do markIt sp k (← chkV n E Δ T V A)
    | v => do convV E v.span A (← synV n E Δ T v)

/-- Synthesize the type of a computation. -/
def synC : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Comp →
    CheckM (Σ C : CCTy, Res Δ T (.comp C))
  | 0, _, _, _, m => err m.span "expression nested too deeply"
  | n + 1, E, Δ, T, m =>
    if m.terminal && E.own.any id then do
      let ⟨C, r⟩ ← synC n E.clearOwn Δ T m
      pure ⟨C, ← dropOwed E m.span r⟩
    else match m with
    | .ret sp V => do
      let ⟨_, r⟩ ← synV n E Δ T V
      pure ⟨_, rRet (at_ sp) r⟩
    | .bind sp x oA M N lin => do
      let ⟨A, S', rM⟩ ← bindHead n (E.ownIn (mentionsC · M)) Δ T sp oA M
      match S', rM with
      | [], rM =>
        let ⟨C, rN⟩ ← synC n (((E.minus rM.F.u).bindVal rM.t).pushOwn x.name A lin) Δ (A :: T) N
        let FN ← popL E x.span x.name rN.F lin
        if h : overlapOK T rM.F.u FN.u = true then pure ⟨C, rBind (at_ sp) rM FN h⟩
        else throw (splitErr E T sp rM.F.u FN.u)
      | o :: os, rM =>
        -- The head performs operations (SPEC §19): the binding is at the current row.
        let S := E.row.getD (o :: os)
        let rM' ← liftRow E M.span S rM
        let ⟨_, rN⟩ ← atRow E N.span S
          (← synC n { (E.minus rM.F.u).pushOwn x.name A lin with row := some S } Δ (A :: T) N)
        pure ⟨_, ← effBind E sp x lin rM' rN⟩
    | .unwind sp x oA M D N => do
      let ⟨A, S', rM⟩ ← bindHead n (E.ownIn (mentionsC · M)) Δ T sp oA M
      let S := E.row.getD S'
      let rM' ← liftRow E M.span S rM
      let ⟨_, rN⟩ ← atRow E N.span S
        (← synC n { (E.minus rM.F.u).pushOwn x.name A with row := some S } Δ (A :: T) N)
      let rD ← chkC n ((E.minus rM.F.u).push none) Δ (.unit :: T) D
        (effOf [] .unit)
      let FN ← popL E x.span x.name rN.F
      pure ⟨_, ← thenIt E sp rM' FN rD⟩
    | .perform sp k i V => do
      let ⟨_, o, hf⟩ ← findOp E sp "perform" k i
      if hna : o.abort = false then
        let rV ← chkV n E Δ T V o.A
        pure ⟨_, rPerform (at_ sp) hf hna rV⟩
      else err sp s!"the operation {k}.{i} is abortive: write `abort[{k}.{i}]`"
    | .abort sp k i V => do
      let ⟨_, r⟩ ← abortIt n E Δ T sp k i V .zero
      pure ⟨_, r⟩
    | .handle sp k hr hc M => do
      let some ir := lookupVar hr.name E.vars
        | err hr.span s!"`{hr.name}` is not a variable in scope"
      let some ic := lookupVar hc.name E.vars
        | err hc.span s!"`{hc.name}` is not a variable in scope"
      match hTr : T[ir]?, hTc : T[ic]? with
      | some Tr, some Tc =>
        match retRead Tr with
        | none => err hr.span (s!"the answer clause `{hr.name}` must have a type " ++
            s!"`!U(A -o F[…] R)`, but it has type `{E.ppV Tr}`")
        | some ⟨S, A, R, hr'⟩ =>
          match clausesReadBoxed S R Tc, clausesRead S R Tc with
          | none, none => err hc.span (s!"the clauses `{hc.name}` must have the type of a " ++
              s!"handler's clauses at `F{ppRow E S} {E.ppV R}`, but they have type `{E.ppV Tc}`")
          | some ⟨d, Es, hc'⟩, _ =>
            -- BOXED-κ (SPEC §28): the clauses receive `κ` boxed at `@d`.
            if k < 2 ^ 32 ∧ k ≠ 0 then
              let nm := UInt32.ofNat k
              if hn0 : nm ≠ 0 then
                if hnS : ∀ o ∈ S, o.n ≠ nm then
                  if hlen : Es.length ≤ 2 ^ 32 then
                   if hdv : BoCa.Fig16.LogRel.Core.Row.divB
                       (BoCa.Fig16.LogRel.Core.Row.ofEff nm Es 0 ++ S) = false then
                    if hwf : d.wf Δ = true then
                      let Sh := BoCa.Fig16.LogRel.Core.Row.ofEff nm Es 0 ++ S
                      if hSd : ansOutlivesB Δ d Sh = true then
                        let rM ← chkC n E Δ T M (effOf Sh A)
                        if hso : usedSat (outlivesB Δ d) T rM.F.u = true then
                          if h₁ : overlapOK T (oneL T ir) (oneL T ic) = true then
                            if h₂ : overlapOK T (orL (oneL T ir) (oneL T ic)) rM.F.u = true then
                              pure ⟨_, rEffHandleB (at_ sp) { sp := hr.span, name := hr.name }
                                { sp := hc.span, name := hc.name } ir ic (classifyHandler Es (E.valOf ic)) (hr' ▸ hTr) (hc' ▸ hTc) hn0 hnS hlen hdv
                                hwf hSd rM hso h₁ h₂⟩
                            else throw (splitErr E T sp (orL (oneL T ir) (oneL T ic)) rM.F.u)
                          else throw (splitErr E T sp (oneL T ir) (oneL T ic))
                        else match firstBad (outlivesB Δ d) T rM.F.u with
                          | some i => err sp (s!"the clauses box `κ` at `{E.ppL d}`, so the " ++
                              s!"handled computation's context must outlive it: {E.slotName i}, " ++
                              s!"of type `{E.slotTy T i}`, is used inside, and it cannot be " ++
                              s!"shown to outlive `{E.ppL d}`")
                          | none => err sp "internal error: boxed continuation"
                      else match Sh.find? (fun o => !(o.abort || outlivesB Δ d o.B)) with
                        | some o => err sp (s!"the clauses box `κ` at `{E.ppL d}`, so every " ++
                            s!"operation the handled computation resumes at must answer a type " ++
                            s!"that outlives it: {o.n}.{o.i} answers `{E.ppV o.B}`, which cannot " ++
                            s!"be shown to outlive `{E.ppL d}`")
                        | none => err sp "internal error: boxed continuation"
                    else err hc.span s!"the clauses box `κ` at `{E.ppL d}`, which is not defined here"
                   else err sp divHandleMsg
                  else err sp "a handler has at most 2^32 operations"
                else err sp s!"the name {k} is already in the row `{ppRow E S}` of the handler's answer"
              else err sp "a handler's name is not 0"
            else err sp s!"a handler's name is between 1 and 2^32 - 1, not {k}"
          | none, some ⟨Es, hc'⟩ =>
            if k < 2 ^ 32 ∧ k ≠ 0 then
              let nm := UInt32.ofNat k
              if hn0 : nm ≠ 0 then
                if hnS : ∀ o ∈ S, o.n ≠ nm then
                  if hlen : Es.length ≤ 2 ^ 32 then
                   if hdv : BoCa.Fig16.LogRel.Core.Row.divB
                       (BoCa.Fig16.LogRel.Core.Row.ofEff nm Es 0 ++ S) = false then
                    let rM ← chkC n E Δ T M
                      (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff nm Es 0 ++ S) A)
                    if h₁ : overlapOK T (oneL T ir) (oneL T ic) = true then
                      if h₂ : overlapOK T (orL (oneL T ir) (oneL T ic)) rM.F.u = true then
                        pure ⟨_, rEffHandle (at_ sp) { sp := hr.span, name := hr.name }
                          { sp := hc.span, name := hc.name } ir ic (classifyHandler Es (E.valOf ic)) (hr' ▸ hTr) (hc' ▸ hTc) hn0 hnS hlen hdv
                          rM h₁ h₂⟩
                      else throw (splitErr E T sp (orL (oneL T ir) (oneL T ic)) rM.F.u)
                    else throw (splitErr E T sp (oneL T ir) (oneL T ic))
                   else err sp divHandleMsg
                  else err sp "a handler has at most 2^32 operations"
                else err sp s!"the name {k} is already in the row `{ppRow E S}` of the handler's answer"
              else err sp "a handler's name is not 0"
            else err sp s!"a handler's name is between 1 and 2^32 - 1, not {k}"
      | _, _ => err sp "internal error: variable out of range"
    | .force sp x =>
      match lookupVar x.name E.vars with
      | some i =>
        match h : T[i]? with
        | some (.thunk C) => pure ⟨C, rForce { sp, name := x.name } i C h⟩
        | some A => err sp s!"`force {x.name}` needs a `U` type, but `{x.name} : {E.ppV A}`"
        | none => err sp "internal error: variable out of range"
      | none => err x.span s!"`force` takes a variable, and `{x.name}` is not one in scope; bind it first"
    | .lam sp x A M => do
      let A' ← E.elabV Δ A
      let ⟨_, rM⟩ ← synC n (E.pushOwn x.name A') Δ (A' :: T) M
      pure ⟨_, ← lamIt E sp x rM⟩
    | .app sp M x => do
      let ⟨C, rM⟩ ← synC n E Δ T M
      match C, rM with
      | .arr _ _, rM => do pure ⟨_, ← appIt E T sp x rM⟩
      | C, _ => err M.span s!"this is applied, so it must have a type `A -o C`, but it has type `{E.ppC C}`"
    | .with_ sp M N => do
      let ⟨_, r₁⟩ ← synC n (E.push none |>.push none) Δ (withT T) M
      let ⟨_, r₂⟩ ← synC n (E.push none |>.push none) Δ (withT T) N
      pure ⟨_, ← withIt E T sp r₁ r₂⟩
    | .proj sp i M => do
      let ⟨C, r⟩ ← synC n E Δ T M
      match C, r with
      | .amp _ _, r => if i then pure ⟨_, rProj₁ (at_ sp) r⟩ else pure ⟨_, rProj₂ (at_ sp) r⟩
      | C, _ => err sp s!"a projection needs a `&` type, but this has type `{E.ppC C}`"
    | .top sp => pure ⟨.top, rTop (at_ sp)⟩
    | .letUnit sp V M => do
      let rV ← chkV n E Δ T V .unit
      let ⟨C, rM⟩ ← synC n (E.minus rV.F.u) Δ T M
      if h : overlapOK T rV.F.u rM.F.u = true then pure ⟨C, rUnitE (at_ sp) rV rM h⟩
      else throw (splitErr E T sp rV.F.u rM.F.u)
    | .letPair sp x y V M => do
      let ⟨A, rV⟩ ← synV n E Δ T V
      match A, rV with
      | .tensor A B, rV => do
        let ⟨C, rM⟩ ← synC n ((E.minus rV.F.u).pushOwn x.name A |>.pushOwn y.name B) Δ
          (B :: A :: T) M
        let F₁ ← popL E y.span y.name rM.F
        let F₂ ← popL E x.span x.name F₁
        if h : overlapOK T rV.F.u F₂.u = true then pure ⟨C, rTensorE (at_ sp) rV F₂ h⟩
        else throw (splitErr E T sp rV.F.u F₂.u)
      | A, _ => err V.span s!"`let (x, y) = V` needs a `*` type, but `V : {E.ppV A}`"
    | .case sp V x M y N => do
      let ⟨A, rV⟩ ← synV n E Δ T V
      match A, rV with
      | .sum A B, rV => do
        let E' := E.minus rV.F.u
        let ⟨C, r₁⟩ ← synC n (E'.pushOwn x.name A) Δ (A :: T) M
        let plain : CheckM (Σ C : CCTy, Res Δ T (.comp C)) := do
          let r₂ ← chkC n (E'.pushOwn y.name B) Δ (B :: T) N C
          pure ⟨_, ← caseIt E T sp x y rV r₁ r₂⟩
        match ← attempt plain, E.row with
        | .ok r, _ => pure r
        | .error e, some S@(_ :: _) =>
          -- Inside a computation at the row `S`: the arms at `F[S] B`, the first arm's value
          -- type `B`, or else the second's (the first may be an abort, of any type).
          let first : CheckM (Σ C : CCTy, Res Δ T (.comp C)) := do
            let ⟨B₁, r₁'⟩ ← atRow E M.span S ⟨C, r₁⟩
            let r₂ ← chkC n (E'.pushOwn y.name B) Δ (B :: T) N (effOf S B₁)
            pure ⟨_, ← caseIt E T sp x y rV r₁' r₂⟩
          match ← attempt first with
          | .ok r => pure r
          | .error _ =>
            let second : CheckM (Σ C : CCTy, Res Δ T (.comp C)) := do
              let ⟨B₂, r₂⟩ ← atRow E N.span S (← synC n (E'.pushOwn y.name B) Δ (B :: T) N)
              let r₁' ← chkC n (E'.pushOwn x.name A) Δ (A :: T) M (effOf S B₂)
              pure ⟨_, ← caseIt E T sp x y rV r₁' r₂⟩
            match ← attempt second with
            | .ok r => pure r
            | .error _ => throw e
        | .error e, _ => throw e
      | A, _ => err V.span s!"`case V` needs a `+` type, but `V : {E.ppV A}`"
    | .absurd sp _ => err sp "the type of `absurd V` cannot be synthesized: ascribe it, `(absurd V : C)`"
    | .loop sp _ src _ _ _ => err sp (s!"{src.what} is elaborated before checking, on the spine " ++
        "of a function's body or of `main` (SPEC §14)")
    | .lamL sp x b M => do
      let bl ← E.elabL Δ b
      let v := Δ.freshVar
      let ⟨_, rM⟩ ← synC n { E.push none with lenv := (x.name, v) :: E.lenv } (Δ.extend v bl)
        (.unit :: T) M
      pure ⟨_, ← funIt E T sp x.name rM⟩
    | .inst sp M a => do
      let al ← E.elabL Δ a
      let ⟨C, r⟩ ← synC n E Δ T M
      match C, r with
      | .all _ b _, r =>
        if h : ltB Δ al b = true then pure ⟨_, rAllE (at_ sp) al h r⟩
        else err sp s!"cannot show `{E.ppL al}` ⊏ `{E.ppL b}` from the lifetime context"
      | C, _ => err M.span s!"this is instantiated, so it must have a type `forall 'x < @. C`, but it has type `{E.ppC C}`"
    | .nuIn sp M => do
      let ⟨C, r⟩ ← synC n E Δ T M
      match (CTy.nuThunks C).find? (fun B => CTy.nuOkB B && decide (B.unroll = C)) with
      | some B =>
        if h : CTy.nuOkB B = true ∧ B.unroll = C then
          pure ⟨_, rNuIn (at_ sp) (CTy.nuOkB_sound B h.1) (h.2 ▸ r)⟩
        else err sp s!"`nu_in M` needs `M` at the unrolling of a `nu` type, but `M : {E.ppC C}`"
      | none => err sp s!"`nu_in M` needs `M` at the unrolling of a `nu` type, but `M : {E.ppC C}`"
    | .nuOut sp M => do
      let ⟨C, r⟩ ← synC n E Δ T M
      match C, r with
      | .nu B, r =>
        if h : CTy.nuOkB B = true then pure ⟨_, rNuOut (at_ sp) (CTy.nuOkB_sound B h) r⟩
        else err sp s!"`nu_out M` needs a positive `nu` type, but `M : {E.ppC (.nu B)}`"
      | C, _ => err sp s!"`nu_out M` needs `M` at a `nu` type, but `M : {E.ppC C}`"
    | .ascribe _ M C => do
      let C' ← E.elabC Δ C
      let r ← chkC n E Δ T M C'
      pure ⟨C', r⟩
    | .withbor2r sp x b A B r p m M => do
      -- R1, the relaxed lend (SPEC §29): its body sees the view alone.
      let bl ← E.elabL Δ b
      let A' ← E.elabV Δ A
      let B' ← E.elabV Δ B
      let S ← E.elabRow Δ sp r
      let v := Δ.freshVar
      let ⟨⟨hx, hT, hB⟩⟩ ← freshFor sp v A' B'
      let some i := lookupVar p.name E.vars
        | err p.span s!"`withbor2r` lends a variable, and `{p.name}` is not one in scope"
      match hi : T[i]? with
      | some (.ref A'') =>
        if hA : A'' = A' then
          if hwf : bl.wf Δ = true then
            if hbx : bl.mentions v = false then
              if hΔx : boundsAvoidB Δ v = true then
                let ⟨hside⟩ ← outlivesWitness sp bl A'
                if hS : Row.resumeOB S v = true then
                  if hBn : noThunkB B' = true then
                    let ⟨hdt, hdc, hde⟩ ← finaliser sp (.ref A')
                    let E' : Env :=
                      { E with vars := [], own := [], nExt := 0, lenv := (x.name, v) :: E.lenv,
                               row := some S, vals := [] }
                    let rM ← chkC n (E'.pushOwn m.name (.mut (.var v) A')) (Δ.extend v bl)
                      [.mut (.var v) A'] M (effOf S (.box (.var v) B'))
                    if hL : subL (allL [.mut (.var v) A']) (orL rM.F.u rM.F.w) = true then
                      if hM1 : BoCa.Fig16.LogRel.Core.closedAt 1 rM.e = true then
                        if hcb : BoCa.Fig16.LogRel.Core.closedAt 0 (BoCa.Fig16.LogRel.Core.lendCb rM.e).1 = true then
                          if h : overlapOK T (Fam.deadStrict T).u (oneL T i) = true then
                            pure ⟨_, rLendR (at_ sp) ⟨"R1", sp.start.line, sp.start.col⟩ v bl i (hA ▸ hi)
                              (defines_of_wf hwf) hx hbx (boundsAvoidB_sound hΔx) hT hB
                              (noThunkB_sound hBn) hside (Row.resumeOB_sound hS) hdt hdc hde rM hL hM1
                              hcb h⟩
                          else err sp "internal error: a relaxed lend's place"
                        else err sp "internal error: a relaxed lend's body is not closed"
                      else err sp "internal error: a relaxed lend's body is not closed"
                    else err sp s!"the view `{m.name}` of this relaxed lend is not consumed"
                  else err sp s!"a relaxed lend's result `{E.ppV B'}` holds a `U`: its value is read back after the lend is re-lent (R1, SPEC §29)"
                else err sp ("the row of a relaxed lend's body has only operations that resume " ++
                  "once (affine or linear), of names other than 0, answering `1` with the empty " ++
                  "cancel row, whose arguments are closed data with no `U` (R1, SPEC §29)")
              else err sp s!"`withbor2r`: its number {ppLVar v} occurs in a bound of the lifetime context"
            else err sp s!"`withbor2r`: its bound mentions its own number {ppLVar v}"
          else err sp s!"`withbor2r`: the bound `{E.ppL bl}` is not defined here"
        else throw (mismatch p.span (E.ppV (.ref A')) (E.ppV (.ref A'')))
      | some A'' => err p.span s!"`withbor2r` lends an owned cell `ref A`, but `{p.name} : {E.ppV A''}`"
      | none => err sp "internal error: variable out of range"

/-- The head `M` of `x <- M; N`, at a row: `[]` when it is pure (SPEC §19). `x : A <- M; N`
checks it at `F A`, or, at a row that has operations and when it does not check at `F A`, at
`F_Σ A`. -/
def bindHead : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Span → Option VTy → Comp →
    CheckM (Σ A : CVTy, Σ S : CRow, Res Δ T (.comp (effOf S A)))
  | 0, _, _, _, sp, _, _ => err sp "expression nested too deeply"
  | n + 1, E, Δ, T, _, some A, M => do
    let A' ← E.elabV Δ A
    match E.row with
    | some (o :: os) =>
      match ← attempt (chkC n E Δ T M (.ret A')) with
      | .ok r => pure ⟨A', [], r⟩
      | .error _ =>
        let r ← chkC n E Δ T M (effOf (o :: os) A')
        pure ⟨A', o :: os, r⟩
    | _ =>
      let r ← chkC n E Δ T M (.ret A')
      pure ⟨A', [], r⟩
  | n + 1, E, Δ, T, _, none, M => do
    let ⟨C, r⟩ ← synC n E Δ T M
    match effRow? C with
    | some (S, A) =>
      if h : effOf S A = C then pure ⟨A, S, h ▸ r⟩
      else err M.span "internal error: a returner chain"
    | none => err M.span s!"a bound computation must have a type `F A`, but this has type `{E.ppC C}`"

/-- `abort[k.i] V` at the answer `B`: an abortive operation of the current row (SPEC §19's abortive rule). -/
def abortIt : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Span → Nat → Nat → Val → (B : CVTy) →
    CheckM (Σ S : CRow, Res Δ T (.comp (effOf S B)))
  | 0, _, _, _, sp, _, _, _, _ => err sp "expression nested too deeply"
  | n + 1, E, Δ, T, sp, k, i, V, B => do
    let ⟨S, o, hf⟩ ← findOp E sp "abort" k i
    if ha : o.abort = true then
      if hd : dropB o.A = true then
        let rV ← chkV n E Δ T V o.A
        pure ⟨S, rRaise (at_ sp) B hf ha hd rV⟩
      else err sp s!"the argument of the abortive operation {k}.{i}, of type `{E.ppV o.A}`, does not drop"
    else err sp s!"the operation {k}.{i} is not abortive: write `perform[{k}.{i}]`"

/-- Check a computation against a type. -/
def chkC : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Comp → (C : CCTy) →
    CheckM (Res Δ T (.comp C))
  | 0, _, _, _, m, _ => err m.span "expression nested too deeply"
  | n + 1, E, Δ, T, m, C =>
    let E := E.atC C
    if m.terminal && E.own.any id then do
      let r ← chkC n E.clearOwn Δ T m C
      dropOwed E m.span r
    else match m with
    | .ret sp V =>
      match C with
      | .ret A => do pure (rRet (at_ sp) (← chkV n E Δ T V A))
      | C =>
        match effRow? C with
        | some (S, A) =>
          if hC : effOf S A = C then do
            let r : Res Δ T (.comp (effOf [] A)) := rRet (at_ sp) (← chkV n E Δ T V A)
            pure (hC ▸ rEffSub (at_ sp) (S := []) rfl r)
          else err sp "internal error: a returner chain"
        | none => err sp s!"`return V` is checked against `{E.ppC C}`, which is not an `F` type"
    | .bind sp x oA M N lin => do
      let ⟨A, S', rM⟩ ← bindHead n (E.ownIn (mentionsC · M)) Δ T sp oA M
      match S', rM with
      | [], rM =>
        let rN ← chkC n (((E.minus rM.F.u).bindVal rM.t).pushOwn x.name A lin) Δ (A :: T) N C
        let FN ← popL E x.span x.name rN.F lin
        if h : overlapOK T rM.F.u FN.u = true then pure (rBind (at_ sp) rM FN h)
        else throw (splitErr E T sp rM.F.u FN.u)
      | o :: os, rM =>
        -- The head performs operations (SPEC §19): the binding is at the row of `C`.
        match effRow? C with
        | some (S, B) =>
          if hC : effOf S B = C then do
            let rM' ← liftRow E M.span S rM
            let rN ← chkC n ((E.minus rM.F.u).pushOwn x.name A lin) Δ (A :: T) N (effOf S B)
            pure (hC ▸ (← effBind E sp x lin rM' rN))
          else err sp "internal error: a returner chain"
        | none => err sp (s!"the bound computation performs the operations " ++
            s!"`{ppRow E (o :: os)}`, so this must have a type `F[…] B`, but `{E.ppC C}` is expected")
    | .unwind sp x oA M D N =>
      match effRow? C with
      | some (S, B) =>
        if hC : effOf S B = C then do
          let ⟨A, _, rM⟩ ← bindHead n (E.ownIn (mentionsC · M)) Δ T sp oA M
          let rM' ← liftRow E M.span S rM
          let rN ← chkC n ((E.minus rM.F.u).pushOwn x.name A) Δ (A :: T) N (effOf S B)
          let rD ← chkC n ((E.minus rM.F.u).push none) Δ (.unit :: T) D
            (effOf [] .unit)
          let FN ← popL E x.span x.name rN.F
          pure (hC ▸ (← thenIt E sp rM' FN rD))
        else err sp "internal error: a returner chain"
      | none => err sp s!"`x <- M unwind (D); N` is checked against `{E.ppC C}`, which is not `F[…] B`"
    | .abort sp k i V =>
      match effRow? C with
      | some (_, B) => do
        let ⟨S', r⟩ ← abortIt n E Δ T sp k i V B
        if hC : effOf S' B = C then pure (hC ▸ r)
        else err sp s!"internal error: the row of `{E.ppC C}`"
      | none => err sp s!"`abort[{k}.{i}] V` is checked against `{E.ppC C}`, which is not `F[…] B`"
    | .lam sp x A M =>
      match C with
      | .arr A₀ C => do
        let A' ← E.elabV Δ A
        if hA : A' = A₀ then do
          let rM ← chkC n (E.pushOwn x.name A') Δ (A' :: T) M C
          pure (hA ▸ (← lamIt E sp x rM))
        else err A.span s!"the binder is annotated `{E.ppV A'}`, but the expected type is `{E.ppV A₀} -o …`"
      | C => err sp s!"`fun` is checked against `{E.ppC C}`, which is not a `-o` type"
    | .with_ sp M N =>
      match C with
      | .amp C D => do
        let r₁ ← chkC n (E.push none |>.push none) Δ (withT T) M C
        let r₂ ← chkC n (E.push none |>.push none) Δ (withT T) N D
        withIt E T sp r₁ r₂
      | C => err sp s!"`<M, N>` is checked against `{E.ppC C}`, which is not a `&` type"
    | .top sp =>
      match C with
      | .top => pure (rTop (at_ sp))
      | C => err sp s!"`<>` has type `top`, but `{E.ppC C}` is expected"
    | .letUnit sp V M => do
      let rV ← chkV n E Δ T V .unit
      let rM ← chkC n (E.minus rV.F.u) Δ T M C
      if h : overlapOK T rV.F.u rM.F.u = true then pure (rUnitE (at_ sp) rV rM h)
      else throw (splitErr E T sp rV.F.u rM.F.u)
    | .letPair sp x y V M => do
      let ⟨A, rV⟩ ← synV n E Δ T V
      match A, rV with
      | .tensor A B, rV => do
        let rM ← chkC n ((E.minus rV.F.u).pushOwn x.name A |>.pushOwn y.name B) Δ
          (B :: A :: T) M C
        let F₁ ← popL E y.span y.name rM.F
        let F₂ ← popL E x.span x.name F₁
        if h : overlapOK T rV.F.u F₂.u = true then pure (rTensorE (at_ sp) rV F₂ h)
        else throw (splitErr E T sp rV.F.u F₂.u)
      | A, _ => err V.span s!"`let (x, y) = V` needs a `*` type, but `V : {E.ppV A}`"
    | .case sp V x M y N => do
      let ⟨A, rV⟩ ← synV n E Δ T V
      match A, rV with
      | .sum A B, rV => do
        let E' := E.minus rV.F.u
        let r₁ ← chkC n (E'.pushOwn x.name A) Δ (A :: T) M C
        let r₂ ← chkC n (E'.pushOwn y.name B) Δ (B :: T) N C
        caseIt E T sp x y rV r₁ r₂
      | A, _ => err V.span s!"`case V` needs a `+` type, but `V : {E.ppV A}`"
    | .absurd sp V => do
      let rV ← chkV n E Δ T V .zero
      if h : overlapOK T rV.F.u (Fam.top T).u = true then pure (rZeroE (at_ sp) C rV h)
      else err sp "internal error: absurd"
    | .lamL sp x b M =>
      match C with
      | .all v b₀ C => do
        let bl ← E.elabL Δ b
        if hb : bl = b₀ then do
          let rM ← chkC n { E.push none with lenv := (x.name, v) :: E.lenv } (Δ.extend v bl)
            (.unit :: T) M C
          pure (hb ▸ (← funIt E T sp x.name rM))
        else err b.span s!"the bound is `{E.ppL bl}`, but the expected type has bound `{E.ppL b₀}`"
      | C => err sp s!"`Fun` is checked against `{E.ppC C}`, which is not a `forall` type"
    | .nuIn sp M =>
      match C with
      | .nu B =>
        if h : CTy.nuOkB B = true then do
          pure (rNuIn (at_ sp) (CTy.nuOkB_sound B h) (← chkC n E Δ T M B.unroll))
        else err sp s!"`nu_in M` is checked against `{E.ppC C}`, which is not a positive `nu` type"
      | C => err sp s!"`nu_in M` is checked against `{E.ppC C}`, which is not a `nu` type"
    | m => do convC E m.span C (← synC n E Δ T m)


/-- A use of the `def` `d`, named `x`, at the type arguments `targs` (`tps` binding its
parameters): its key's checked body, placed at the use. A body whose derivation cannot be placed at
a wider context (the relaxed rules, SPEC §29) is checked at the use itself. -/
def useDef : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Span → String → DefInfo →
    List (String × CVTy) → List CVTy → CheckM (Σ A : CVTy, Res Δ T (.val A))
  | 0, _, _, _, sp, _, _, _, _ => err sp "expression nested too deeply"
  | n + 1, E, Δ, T, sp, x, d, tps, targs => do
    let h ← match (← get).findSome? (·.hit? d.scope.upto targs Δ T) with
      | some h => pure h
      | none => do
        let m := T.length - E.nExt
        let E' := ({ E with vars := E.vars.drop m } : Env).forDef (T.drop m) d tps
        let A ← E'.elabV Δ d.ty
        let r ← tryCatch (chkV n E' Δ (T.drop m) d.body A) (fun e => throw (inDef x sp e))
        modify (⟨d.scope.upto, targs, Δ, T.drop m, A, r, r.t.absF Δ, rfl⟩ :: ·)
        pure (⟨A, T.drop m, m, rfl, r, r.t.absF Δ, rfl⟩ : DefHit Δ T)
    match h with
    | ⟨A, _, m, hT, r, some f, hab⟩ =>
      pure ⟨A, rUse { sp } x d.scope.upto targs m hT r f hab.symm⟩
    | ⟨A, _, _, _, _, none, _⟩ => do
      let r ← tryCatch (chkV n (E.forDef T d tps) Δ T d.body A) (fun e => throw (inDef x sp e))
      pure ⟨A, rUseAt { sp } x d.scope.upto targs r⟩

end

end Frontend.Check
