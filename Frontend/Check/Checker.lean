import Frontend.Check.Consts

/-!
# Frontend — Check — the bidirectional checker

`synV`/`chkV` check a value-judged expression, synthesizing its type or against a given one;
`synC`/`chkC` do the same for computations (syntax-core §6, §11). Each case applies one rule
builder of `Frontend/Check/Rules.lean` (or `Consts.lean`) to the checked premises, so a success
is a `Res`: the erasure with its `CDerives` derivations. Names are resolved on the way: a
variable to its de Bruijn slot (§6.3), a lifetime name to its `LifeVar` (§3), a `def` to its
body, re-checked at the use (§10). Variables owed to the computation being checked (`Env.own`,
SPEC §12) are passed to its tail positions and dropped before each terminal computation that
leaves them unused (`dropOwed`).

The recursion is structural on a fuel argument that bounds the depth of the call tree;
running out is an error, not an assumption.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives Jdg)

/-! ### The checker -/

mutual

/-- Synthesize the type of a value-judged expression. -/
def synV : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Val →
    Except Error (Σ A : CVTy, Res Δ T (.val A))
  | 0, _, _, _, v => err v.span "expression nested too deeply"
  | n + 1, E, Δ, T, v => let E := E.forVal; match v with
    | .var sp x =>
      match lookupVar x E.vars with
      | some i =>
        match h : T[i]? with
        | some A => pure ⟨A, rVar i A h⟩
        | none => err sp "internal error: variable out of range"
      | none =>
        match E.scope.findDef x with
        | none =>
          if E.scope.hasExtern x then
            err sp (s!"the capability `{x}` is not in scope: a `def` may use only persistent " ++
              "externs; take the capability as an argument (SPEC §11)")
          else err sp s!"unknown variable `{x}`"
        | some d =>
          if d.params.isEmpty then do
            let E' := E.forDef T d []
            let A ← E'.elabV Δ d.ty
            let r ← tryCatch (chkV n E' Δ T d.body A) (fun e => throw (inDef x sp e))
            pure ⟨A, r⟩
          else err sp s!"`{x}` takes {d.params.length} type argument(s): write `{x}[…]`"
    | .defApp sp x args =>
      match E.scope.findDef x with
      | none => err sp s!"unknown definition `{x}`"
      | some d =>
        if d.params.length = args.length then do
          let targs ← args.mapM (E.elabV Δ)
          let E' := E.forDef T d ((d.params.map (·.name)).zip targs)
          let A ← E'.elabV Δ d.ty
          let r ← tryCatch (chkV n E' Δ T d.body A) (fun e => throw (inDef x sp e))
          pure ⟨A, r⟩
        else err sp s!"`{x}` takes {d.params.length} type argument(s), not {args.length}"
    | .unit _ => pure ⟨.unit, rUnit⟩
    | .pair sp V W => do
      let ⟨_, r₁⟩ ← synV n E Δ T V
      let ⟨_, r₂⟩ ← synV n E Δ T W
      if h : overlapOK T r₁.F.u r₂.F.u = true then pure ⟨_, rPair r₁ r₂ h⟩
      else throw (splitErr E T sp r₁.F.u r₂.F.u)
    | .inl sp _ => err sp "the type of `inl V` cannot be synthesized: ascribe it, `(inl V : A + B)`"
    | .inr sp _ => err sp "the type of `inr V` cannot be synthesized: ascribe it, `(inr V : A + B)`"
    | .thunk sp M => do
      let ⟨C, r⟩ ← synC n (E.push none) Δ (.unit :: T) M
      match C, r with
      | .ret _, r => match rThunkF r with
        | some r' => pure ⟨_, r'⟩
        | none => err sp "internal error: a dead binder is used"
      | C, _ => err sp s!"`thunk M` needs `M : F A`, but `M : {E.ppC C}`; use `thunkv`"
    | .thunkv sp N => do
      let ⟨C, r⟩ ← synC n E Δ T N
      if hC : C.isRet = false then
        match rThunkV hC r with
        | some r' => pure ⟨_, r'⟩
        | none => err sp thunkvLam
      else err sp s!"`thunkv N` needs `N` not of type `F A`, but `N : {E.ppC C}`; use `thunk`"
    | .bangThunk sp M => do
      let ⟨C, r⟩ ← synC n (E.push none) Δ (.unit :: T) M
      match C, r with
      | .ret _, r => match rBangThunkF r with
        | .ok r' => pure ⟨_, r'⟩
        | .error i => throw (notBang E T sp i)
      | C, _ => err sp s!"`!thunk M` needs `M : F A`, but `M : {E.ppC C}`; use `!thunkv`"
    | .bangThunkv sp N => do
      let ⟨C, r⟩ ← synC n E Δ T N
      if hC : C.isRet = false then
        match rBangThunkV hC r with
        | .ok r' => pure ⟨_, r'⟩
        | .error i => throw (notBang E T sp i)
      else err sp s!"`!thunkv N` needs `N` not of type `F A`, but `N : {E.ppC C}`; use `!thunk`"
    | .unbang sp V => do
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .bang _, r => pure ⟨_, rBangE r⟩
      | A, _ => err sp s!"`unbang V` needs `V : !A`, but `V : {E.ppV A}`"
    | .boxed sp a V => do
      let al ← E.elabL Δ a
      let ⟨_, r⟩ ← synV n E Δ T V
      pure ⟨_, ← boxIt E T sp al r⟩
    | .unbox sp V => do
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .box _ _, r => pure ⟨_, rBoxE r⟩
      | A, _ => err sp s!"`unbox V` needs `V : box @ A`, but `V : {E.ppV A}`"
    | .sub sp V a => do
      let al ← E.elabL Δ a
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .imm b _, r =>
        if h : leB Δ al b = true then pure ⟨_, rImmSub al h r⟩
        else err sp s!"cannot show `{E.ppL al}` ⊑ `{E.ppL b}` from the lifetime context"
      | .mut b _, r =>
        if h : leB Δ al b = true then pure ⟨_, rMutSub al h r⟩
        else err sp s!"cannot show `{E.ppL al}` ⊑ `{E.ppL b}` from the lifetime context"
      | A, _ => err sp s!"`(V :> @)` needs `V : imm @ A` or `mut @ A`, but `V : {E.ppV A}`"
    | .roll sp _ => err sp "the type of `roll V` cannot be synthesized: ascribe it, `(roll V : mu X. A)`"
    | .unroll sp V => do
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .mu _, r => pure ⟨_, rUnroll r⟩
      | A, _ => err sp s!"`unroll V` needs `V : mu X. A`, but `V : {E.ppV A}`"
    | .run sp M => do
      let ⟨C, r⟩ ← synC n E Δ T M
      match C, r with
      | .ret _, r => pure ⟨_, rOfRet r⟩
      | C, _ => err sp s!"`run M` needs `M : F A`, but `M : {E.ppC C}`"
    | .app sp V W => do
      let ⟨A, rf⟩ ← synV n E Δ T V
      match A, rf with
      | .thunk (.arr A (.ret _)), rf => do
        let ra ← chkV n E Δ T W A
        if h : overlapOK T ra.F.u rf.F.u = true then pure ⟨_, rLolliE rf ra h⟩
        else throw (splitErr E T sp ra.F.u rf.F.u)
      | A, _ => err V.span s!"this is applied, so it must have a type `A => B`, but it has type `{E.ppV A}`"
    | .inst sp V a => do
      let al ← E.elabL Δ a
      let ⟨A, r⟩ ← synV n E Δ T V
      match A, r with
      | .thunk (.all _ b (.ret _)), r =>
        if h : ltB Δ al b = true then pure ⟨_, rAllEV al h r⟩
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

/-- Check a value-judged expression against a type. -/
def chkV : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Val → (A : CVTy) →
    Except Error (Res Δ T (.val A))
  | 0, _, _, _, v, _ => err v.span "expression nested too deeply"
  | n + 1, E, Δ, T, v, A => let E := E.forVal; match v with
    | .pair sp V W =>
      match A with
      | .tensor A B => do
        let r₁ ← chkV n E Δ T V A
        let r₂ ← chkV n E Δ T W B
        if h : overlapOK T r₁.F.u r₂.F.u = true then pure (rPair r₁ r₂ h)
        else throw (splitErr E T sp r₁.F.u r₂.F.u)
      | A => err sp s!"a pair is checked against `{E.ppV A}`, which is not a `*` type"
    | .inl sp V =>
      match A with
      | .sum A B => do pure (rInl B (← chkV n E Δ T V A))
      | A => err sp s!"`inl V` is checked against `{E.ppV A}`, which is not a `+` type"
    | .inr sp V =>
      match A with
      | .sum A B => do pure (rInr A (← chkV n E Δ T V B))
      | A => err sp s!"`inr V` is checked against `{E.ppV A}`, which is not a `+` type"
    | .thunk sp M =>
      match A with
      | .thunk (.ret A) => do
        let r ← chkC n (E.push none) Δ (.unit :: T) M (.ret A)
        match rThunkF r with
        | some r' => pure r'
        | none => err sp "internal error: a dead binder is used"
      | A => err sp s!"`thunk M` is checked against `{E.ppV A}`, which is not `U (F A)`"
    | .thunkv sp N =>
      match A with
      | .thunk C =>
        if hC : C.isRet = false then do
          let r ← chkC n E Δ T N C
          match rThunkV hC r with
          | some r' => pure r'
          | none => err sp thunkvLam
        else err sp s!"`thunkv N` is checked against `{E.ppV A}`: use `thunk` at `U (F A)`"
      | A => err sp s!"`thunkv N` is checked against `{E.ppV A}`, which is not a `U` type"
    | .bangThunk sp M =>
      match A with
      | .bang (.thunk (.ret A)) => do
        let r ← chkC n (E.push none) Δ (.unit :: T) M (.ret A)
        match rBangThunkF r with
        | .ok r' => pure r'
        | .error i => throw (notBang E T sp i)
      | A => err sp s!"`!thunk M` is checked against `{E.ppV A}`, which is not `!U (F A)`"
    | .bangThunkv sp N =>
      match A with
      | .bang (.thunk C) =>
        if hC : C.isRet = false then do
          let r ← chkC n E Δ T N C
          match rBangThunkV hC r with
          | .ok r' => pure r'
          | .error i => throw (notBang E T sp i)
        else err sp s!"`!thunkv N` is checked against `{E.ppV A}`: use `!thunk` at `!U (F A)`"
      | A => err sp s!"`!thunkv N` is checked against `{E.ppV A}`, which is not a `!U` type"
    | .unbang _ V => do pure (rBangE (← chkV n E Δ T V (.bang A)))
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
            pure (rRoll hA hc (← chkV n E Δ T V (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)))
          else err sp s!"`roll` at `{E.ppV (.mu A)}`, which is not closed"
        else err sp s!"`roll` at `{E.ppV (.mu A)}`, whose variable occurs under `mut`"
      | A => err sp s!"`roll V` is checked against `{E.ppV A}`, which is not a `mu` type"
    | .run _ M => do pure (rOfRet (← chkC n E Δ T M (.ret A)))
    | v => do convV E v.span A (← synV n E Δ T v)

/-- Synthesize the type of a computation. -/
def synC : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Comp →
    Except Error (Σ C : CCTy, Res Δ T (.comp C))
  | 0, _, _, _, m => err m.span "expression nested too deeply"
  | n + 1, E, Δ, T, m =>
    if m.terminal && E.own.any id then do
      let ⟨C, r⟩ ← synC n E.clearOwn Δ T m
      pure ⟨C, ← dropOwed E m.span r⟩
    else match m with
    | .ret _ V => do
      let ⟨_, r⟩ ← synV n E Δ T V
      pure ⟨_, rRet r⟩
    | .bind sp x oA M N lin => do
      let ⟨A, S', rM⟩ ← bindHead n (E.ownIn (mentionsC · M)) Δ T sp oA M
      match S', rM with
      | [], rM =>
        let ⟨C, rN⟩ ← synC n ((E.minus rM.F.u).pushOwn x.name A lin) Δ (A :: T) N
        let FN ← popL E x.span x.name rN.F lin
        if h : overlapOK T rM.F.u FN.u = true then pure ⟨C, rBind rM FN h⟩
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
        (effOf (BoCa.Fig16.LogRel.Core.Row.abortOnly S) .unit)
      let FN ← popL E x.span x.name rN.F
      pure ⟨_, ← thenIt E sp rM' FN rD⟩
    | .perform sp k i V => do
      let ⟨_, o, hf⟩ ← findOp E sp "perform" k i
      if hna : o.abort = false then
        let rV ← chkV n E Δ T V o.A
        pure ⟨_, rPerform hf hna rV⟩
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
          match clausesRead S R Tc with
          | none => err hc.span (s!"the clauses `{hc.name}` must have the type of a handler's " ++
              s!"clauses at `F{ppRow E S} {E.ppV R}`, but they have type `{E.ppV Tc}`")
          | some ⟨Es, hc'⟩ =>
            if k < 2 ^ 32 ∧ k ≠ 0 then
              let nm := UInt32.ofNat k
              if hn0 : nm ≠ 0 then
                if hnS : ∀ o ∈ S, o.n ≠ nm then
                  if hlen : Es.length ≤ 2 ^ 32 then
                    let rM ← chkC n E Δ T M
                      (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff nm Es 0 ++ S) A)
                    if h₁ : overlapOK T (oneL T ir) (oneL T ic) = true then
                      if h₂ : overlapOK T (orL (oneL T ir) (oneL T ic)) rM.F.u = true then
                        pure ⟨_, rEffHandle ir ic (hr' ▸ hTr) (hc' ▸ hTc) hn0 hnS hlen rM h₁ h₂⟩
                      else throw (splitErr E T sp (orL (oneL T ir) (oneL T ic)) rM.F.u)
                    else throw (splitErr E T sp (oneL T ir) (oneL T ic))
                  else err sp "a handler has at most 2^32 operations"
                else err sp s!"the name {k} is already in the row `{ppRow E S}` of the handler's answer"
              else err sp "a handler's name is not 0"
            else err sp s!"a handler's name is between 1 and 2^32 - 1, not {k}"
      | _, _ => err sp "internal error: variable out of range"
    | .force sp x =>
      match lookupVar x.name E.vars with
      | some i =>
        match h : T[i]? with
        | some (.thunk C) => pure ⟨C, rForce i C h⟩
        | some A => err sp s!"`force {x.name}` needs a `U` type, but `{x.name} : {E.ppV A}`"
        | none => err sp "internal error: variable out of range"
      | none => err x.span s!"`force` takes a variable, and `{x.name}` is not one in scope; bind it first"
    | .lam _ x A M => do
      let A' ← E.elabV Δ A
      let ⟨_, rM⟩ ← synC n (E.pushOwn x.name A') Δ (A' :: T) M
      let FM ← popL E x.span x.name rM.F
      pure ⟨_, rLam FM⟩
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
      | .amp _ _, r => if i then pure ⟨_, rProj₁ r⟩ else pure ⟨_, rProj₂ r⟩
      | C, _ => err sp s!"a projection needs a `&` type, but this has type `{E.ppC C}`"
    | .top _ => pure ⟨.top, rTop⟩
    | .letUnit sp V M => do
      let rV ← chkV n E Δ T V .unit
      let ⟨C, rM⟩ ← synC n (E.minus rV.F.u) Δ T M
      if h : overlapOK T rV.F.u rM.F.u = true then pure ⟨C, rUnitE rV rM h⟩
      else throw (splitErr E T sp rV.F.u rM.F.u)
    | .letPair sp x y V M => do
      let ⟨A, rV⟩ ← synV n E Δ T V
      match A, rV with
      | .tensor A B, rV => do
        let ⟨C, rM⟩ ← synC n ((E.minus rV.F.u).pushOwn x.name A |>.pushOwn y.name B) Δ
          (B :: A :: T) M
        let F₁ ← popL E y.span y.name rM.F
        let F₂ ← popL E x.span x.name F₁
        if h : overlapOK T rV.F.u F₂.u = true then pure ⟨C, rTensorE rV F₂ h⟩
        else throw (splitErr E T sp rV.F.u F₂.u)
      | A, _ => err V.span s!"`let (x, y) = V` needs a `*` type, but `V : {E.ppV A}`"
    | .case sp V x M y N => do
      let ⟨A, rV⟩ ← synV n E Δ T V
      match A, rV with
      | .sum A B, rV => do
        let E' := E.minus rV.F.u
        let ⟨C, r₁⟩ ← synC n (E'.pushOwn x.name A) Δ (A :: T) M
        let plain : Except Error (Σ C : CCTy, Res Δ T (.comp C)) := do
          let r₂ ← chkC n (E'.pushOwn y.name B) Δ (B :: T) N C
          pure ⟨_, ← caseIt E T sp x y rV r₁ r₂⟩
        match plain, E.row with
        | .ok r, _ => pure r
        | .error e, some S@(_ :: _) =>
          -- Inside a computation at the row `S`: the arms at `F[S] B`, the first arm's value
          -- type `B`, or else the second's (the first may be an abort, of any type).
          let first : Except Error (Σ C : CCTy, Res Δ T (.comp C)) := do
            let ⟨B₁, r₁'⟩ ← atRow E M.span S ⟨C, r₁⟩
            let r₂ ← chkC n (E'.pushOwn y.name B) Δ (B :: T) N (effOf S B₁)
            pure ⟨_, ← caseIt E T sp x y rV r₁' r₂⟩
          match first with
          | .ok r => pure r
          | .error _ =>
            let second : Except Error (Σ C : CCTy, Res Δ T (.comp C)) := do
              let ⟨B₂, r₂⟩ ← atRow E N.span S (← synC n (E'.pushOwn y.name B) Δ (B :: T) N)
              let r₁' ← chkC n (E'.pushOwn x.name A) Δ (A :: T) M (effOf S B₂)
              pure ⟨_, ← caseIt E T sp x y rV r₁' r₂⟩
            match second with
            | .ok r => pure r
            | .error _ => throw e
        | .error e, _ => throw e
      | A, _ => err V.span s!"`case V` needs a `+` type, but `V : {E.ppV A}`"
    | .absurd sp _ => err sp "the type of `absurd V` cannot be synthesized: ascribe it, `(absurd V : C)`"
    | .for_ sp _ _ _ _ => err sp ("`for` is elaborated before checking, on the spine of a " ++
        "function's body or of `main` (SPEC §14)")
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
        if h : ltB Δ al b = true then pure ⟨_, rAllE al h r⟩
        else err sp s!"cannot show `{E.ppL al}` ⊏ `{E.ppL b}` from the lifetime context"
      | C, _ => err M.span s!"this is instantiated, so it must have a type `forall 'x < @. C`, but it has type `{E.ppC C}`"
    | .nuIn sp M => do
      let ⟨C, r⟩ ← synC n E Δ T M
      match (CTy.nuThunks C).find? (fun B => CTy.nuOkB B && decide (B.unroll = C)) with
      | some B =>
        if h : CTy.nuOkB B = true ∧ B.unroll = C then
          pure ⟨_, rNuIn (CTy.nuOkB_sound B h.1) (h.2 ▸ r)⟩
        else err sp s!"`nu_in M` needs `M` at the unrolling of a `nu` type, but `M : {E.ppC C}`"
      | none => err sp s!"`nu_in M` needs `M` at the unrolling of a `nu` type, but `M : {E.ppC C}`"
    | .nuOut sp M => do
      let ⟨C, r⟩ ← synC n E Δ T M
      match C, r with
      | .nu B, r =>
        if h : CTy.nuOkB B = true then pure ⟨_, rNuOut (CTy.nuOkB_sound B h) r⟩
        else err sp s!"`nu_out M` needs a positive `nu` type, but `M : {E.ppC (.nu B)}`"
      | C, _ => err sp s!"`nu_out M` needs `M` at a `nu` type, but `M : {E.ppC C}`"
    | .ascribe _ M C => do
      let C' ← E.elabC Δ C
      let r ← chkC n E Δ T M C'
      pure ⟨C', r⟩

/-- The head `M` of `x <- M; N`, at a row: `[]` when it is pure (SPEC §19). `x : A <- M; N`
checks it at `F A`, or, at a row that has operations and when it does not check at `F A`, at
`F_Σ A`. -/
def bindHead : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Span → Option VTy → Comp →
    Except Error (Σ A : CVTy, Σ S : CRow, Res Δ T (.comp (effOf S A)))
  | 0, _, _, _, sp, _, _ => err sp "expression nested too deeply"
  | n + 1, E, Δ, T, _, some A, M => do
    let A' ← E.elabV Δ A
    match E.row with
    | some (o :: os) =>
      match chkC n E Δ T M (.ret A') with
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

/-- `abort[k.i] V` at the answer `B`: an abortive operation of the current row (`[raise]`). -/
def abortIt : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Span → Nat → Nat → Val → (B : CVTy) →
    Except Error (Σ S : CRow, Res Δ T (.comp (effOf S B)))
  | 0, _, _, _, sp, _, _, _, _ => err sp "expression nested too deeply"
  | n + 1, E, Δ, T, sp, k, i, V, B => do
    let ⟨S, o, hf⟩ ← findOp E sp "abort" k i
    if ha : o.abort = true then
      if hd : dropB o.A = true then
        let rV ← chkV n E Δ T V o.A
        pure ⟨S, rRaise B hf ha hd rV⟩
      else err sp s!"the argument of the abortive operation {k}.{i}, of type `{E.ppV o.A}`, does not drop"
    else err sp s!"the operation {k}.{i} is not abortive: write `perform[{k}.{i}]`"

/-- Check a computation against a type. -/
def chkC : Nat → Env → (Δ : LifeCtx) → (T : List CVTy) → Comp → (C : CCTy) →
    Except Error (Res Δ T (.comp C))
  | 0, _, _, _, m, _ => err m.span "expression nested too deeply"
  | n + 1, E, Δ, T, m, C =>
    let E := E.atC C
    if m.terminal && E.own.any id then do
      let r ← chkC n E.clearOwn Δ T m C
      dropOwed E m.span r
    else match m with
    | .ret sp V =>
      match C with
      | .ret A => do pure (rRet (← chkV n E Δ T V A))
      | C =>
        match effRow? C with
        | some (S, A) =>
          if hC : effOf S A = C then do
            let r : Res Δ T (.comp (effOf [] A)) := rRet (← chkV n E Δ T V A)
            pure (hC ▸ rEffSub (S := []) rfl r)
          else err sp "internal error: a returner chain"
        | none => err sp s!"`return V` is checked against `{E.ppC C}`, which is not an `F` type"
    | .bind sp x oA M N lin => do
      let ⟨A, S', rM⟩ ← bindHead n (E.ownIn (mentionsC · M)) Δ T sp oA M
      match S', rM with
      | [], rM =>
        let rN ← chkC n ((E.minus rM.F.u).pushOwn x.name A lin) Δ (A :: T) N C
        let FN ← popL E x.span x.name rN.F lin
        if h : overlapOK T rM.F.u FN.u = true then pure (rBind rM FN h)
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
            (effOf (BoCa.Fig16.LogRel.Core.Row.abortOnly S) .unit)
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
          let FM ← popL E x.span x.name rM.F
          pure (hA ▸ rLam FM)
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
      | .top => pure rTop
      | C => err sp s!"`<>` has type `top`, but `{E.ppC C}` is expected"
    | .letUnit sp V M => do
      let rV ← chkV n E Δ T V .unit
      let rM ← chkC n (E.minus rV.F.u) Δ T M C
      if h : overlapOK T rV.F.u rM.F.u = true then pure (rUnitE rV rM h)
      else throw (splitErr E T sp rV.F.u rM.F.u)
    | .letPair sp x y V M => do
      let ⟨A, rV⟩ ← synV n E Δ T V
      match A, rV with
      | .tensor A B, rV => do
        let rM ← chkC n ((E.minus rV.F.u).pushOwn x.name A |>.pushOwn y.name B) Δ
          (B :: A :: T) M C
        let F₁ ← popL E y.span y.name rM.F
        let F₂ ← popL E x.span x.name F₁
        if h : overlapOK T rV.F.u F₂.u = true then pure (rTensorE rV F₂ h)
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
      if h : overlapOK T rV.F.u (Fam.top T).u = true then pure (rZeroE C rV h)
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
          pure (rNuIn (CTy.nuOkB_sound B h) (← chkC n E Δ T M B.unroll))
        else err sp s!"`nu_in M` is checked against `{E.ppC C}`, which is not a positive `nu` type"
      | C => err sp s!"`nu_in M` is checked against `{E.ppC C}`, which is not a `nu` type"
    | m => do convC E m.span C (← synC n E Δ T m)

end

end Frontend.Check
