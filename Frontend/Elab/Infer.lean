import Frontend.Elab.Tir

/-!
# Frontend — Elab — inference  `[#54, docs/typed-elaboration.md §2.1]`

`inferV`/`inferC` type a term for the sugar (`TCx.tyV`, `Frontend/Elab/Meta.lean`), bidirectionally: a node checked against an
expected type has that type, and its children are given the expected types the checker's rule
gives them. A synthesized node's type comes from its children's types, by the rule's
conclusion. The environment is extended at each binder exactly as the checker extends it
(`Frontend/Check/Checker.lean`), so every type is a type of the checker, over the same variable
slots and lifetime numbering.

Where a type needs one of the core's substitutions (instantiating a lifetime, unrolling a `μ`
or a `ν`, shortening a family), inference asks the checker's own synthesis (`synV`, `synC`) for
it, on that node alone. The checker is not changed and its derivation is discarded: it is used
as a function from terms to types. A node inference cannot type has type `none`; nothing fails
here, since the checker checks the elaborated program in any case.

Every variable a node binds gets an identity, numbered in order through the program.
-/

namespace Frontend.Elab
open Frontend.Check
open BoCa BoCa.Lifetime

/-- The depth bound for inference, and for each question to the checker. -/
def inferFuel : Nat := 1 <<< 20

/-- Identities are numbered in order. -/
abbrev IM := StateM Nat

def fresh : IM Nat := modifyGet fun n => (n, n + 1)

def mkBinder (x : String) (A : Option CVTy) : IM Binder := do
  pure ⟨x, ← fresh, A⟩

def tyV : Option CVTy → Ty
  | some A => .val A
  | none => .none

def tyC : Option CCTy → Ty
  | some C => .comp C
  | none => .none

def Ty.v? : Ty → Option CVTy
  | .val A => some A
  | _ => Option.none

def Ty.c? : Ty → Option CCTy
  | .comp C => some C
  | _ => Option.none

/-- The checker's synthesis of a value's type. -/
def askV (E : Env) (Δ : LifeCtx) (T : List CVTy) (v : Val) : Option CVTy :=
  match (synV inferFuel E.clearOwn Δ T v).run' [] with
  | .ok ⟨A, _⟩ => some A
  | .error _ => none

/-- The checker's synthesis of a computation's type. -/
def askC (E : Env) (Δ : LifeCtx) (T : List CVTy) (M : Comp) : Option CCTy :=
  match (synC inferFuel E.clearOwn Δ T M).run' [] with
  | .ok ⟨C, _⟩ => some C
  | .error _ => none

/-- The type of a name: a variable's slot, or a `def` without type parameters. -/
def varTy (E : Env) (Δ : LifeCtx) (T : List CVTy) (x : String) : Option CVTy :=
  match lookupVar x E.vars with
  | some i => T[i]?
  | none => match E.scope.findDef x with
    | some d => if d.params.isEmpty then ((E.forDef T d []).elabV Δ d.ty).toOption else none
    | none => none

/-- The type of a `def` at type arguments. -/
def defAppTy (E : Env) (Δ : LifeCtx) (T : List CVTy) (x : String) (args : List VTy) :
    Option CVTy := do
  let d ← E.scope.findDef x
  if d.params.length != args.length then none
  let targs ← (args.mapM (E.elabV Δ)).toOption
  ((E.forDef T d ((d.params.map (·.name)).zip targs)).elabV Δ d.ty).toOption

/-- A slot's type, `1` when it is not known (a node whose type is not known). -/
def slot (A : Option CVTy) : CVTy := A.getD .unit

/-- A `&c` in a value, outside nested computations (`Parser`'s `Val.lends`). -/
def valLends : Val → Bool
  | .lend .. => true
  | .pair _ V W | .app _ V W => valLends V || valLends W
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => valLends V
  | _ => false

mutual
/-- The inference nodes of a value, checked against `exp` when it is given. -/
def inferV : Nat → Env → LifeCtx → List CVTy → Option CVTy → Val → IM TNode
  | 0, _, _, _, exp, v => pure (.mk (.val v) (tyV exp) [] [])
  | n + 1, E, Δ, T, exp, v => do
    -- A value performs no operation: its computations are at no row, as the checker has them.
    let E := { E with row := none }
    let node (A : Option CVTy) (ks : List TNode) : TNode := .mk (.val v) (tyV (exp <|> A)) [] ks
    match v with
    | .var _ x | .clone _ x => pure (node (varTy E Δ T x) [])
    | .defApp _ x args => pure (node (defAppTy E Δ T x args) [])
    | .unit _ => pure (node (some .unit) [])
    | .lend _ x _ => pure (node (varTy E Δ T x.name) [])
    | .sugar .. => pure (node none [])
    | .mark _ _ V => do
      let a ← inferV n E Δ T exp V
      pure (node a.ty.v? [a])
    | .const sp c =>
      pure (node (match synConst E Δ T sp c with | .ok ⟨A, _⟩ => some A | .error _ => none) [])
    | .pair _ V W => do
      let (ea, eb) := match exp with
        | some (.tensor A B) => (some A, some B)
        | _ => (none, none)
      let a ← inferV n E Δ T ea V
      let b ← inferV n E Δ T eb W
      pure (node (do pure (.tensor (← a.ty.v?) (← b.ty.v?))) [a, b])
    | .inl _ V => do
      let e := match exp with | some (.sum A _) => some A | _ => none
      pure (node none [← inferV n E Δ T e V])
    | .inr _ V => do
      let e := match exp with | some (.sum _ B) => some B | _ => none
      pure (node none [← inferV n E Δ T e V])
    | .thunk _ M => do
      let e := match exp with | some (.thunk (.ret A)) => some (.ret A) | _ => none
      let m ← inferC n (E.push none) Δ (.unit :: T) e M
      pure (node (m.ty.c?.map .thunk) [m])
    | .thunkv _ N => do
      let e := match exp with | some (.thunk C) => some C | _ => none
      let m ← inferC n E Δ T e N
      pure (node (m.ty.c?.map .thunk) [m])
    | .bangThunk _ M => do
      let e := match exp with | some (.bang (.thunk (.ret A))) => some (.ret A) | _ => none
      let m ← inferC n (E.push none) Δ (.unit :: T) e M
      pure (node (m.ty.c?.map (.bang ∘ .thunk)) [m])
    | .bangThunkv _ N => do
      let e := match exp with | some (.bang (.thunk C)) => some C | _ => none
      let m ← inferC n E Δ T e N
      pure (node (m.ty.c?.map (.bang ∘ .thunk)) [m])
    | .unbang _ V => do
      let a ← inferV n E Δ T (exp.map .bang) V
      pure (node (match a.ty.v? with | some (.bang A) => some A | _ => none) [a])
    | .boxed _ l V => do
      let e := match exp with | some (.box _ A) => some A | _ => none
      let a ← inferV n E Δ T e V
      pure (node (do pure (.box (← (E.elabL Δ l).toOption) (← a.ty.v?))) [a])
    | .unbox _ V => do
      let a ← inferV n E Δ T none V
      pure (node (match a.ty.v? with | some (.box _ A) => some A | _ => none) [a])
    | .sub _ V l => do
      let a ← inferV n E Δ T none V
      let al := (E.elabL Δ l).toOption
      pure (node (match a.ty.v?, al with
        | some (.imm _ A), some al => some (.imm al A)
        | some (.mut _ A), some al => some (.mut al A)
        | _, _ => none) [a])
    | .roll _ V => do
      let e := match exp with
        | some (.mu A) => some (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)
        | _ => none
      pure (node none [← inferV n E Δ T e V])
    | .unroll _ V => do
      let a ← inferV n E Δ T none V
      pure (node (askV E Δ T v) [a])
    | .run _ M => do
      let m ← inferC n E Δ T (exp.map .ret) M
      pure (node (match m.ty.c? with | some (.ret A) => some A | _ => none) [m])
    | .app _ V W => do
      let f ← inferV n E Δ T none V
      let (eW, res) := match f.ty.v? with
        | some (.thunk (.arr A (.ret B))) => (some A, some B)
        | _ => (none, none)
      let w ← inferV n E Δ T eW W
      pure (node res [f, w])
    | .inst _ V l => do
      let a ← inferV n E Δ T none V
      -- `V [@]` at `all 'x < @b. A`: `A` at `@`, read off `V`'s type (the checker's synthesis
      -- re-checks a `def`'s body at each use).
      let direct : Option CVTy := match a.ty.v?, (E.elabL Δ l).toOption with
        | some (.thunk (.all x _ (.ret A))), some al => some (A.instLife x al)
        | _, _ => none
      pure (node (direct <|> askV E Δ T v) [a])
    | .ascribe _ V A => do
      let A' := (E.elabV Δ A).toOption
      let a ← inferV n E Δ T A' V
      pure (node A' [a])
    | .shorten _ _ _ _ V => do
      let a ← inferV n E Δ T none V
      pure (node (askV E Δ T v) [a])

/-- The inference nodes of a computation, checked against `exp` when it is given. -/
def inferC : Nat → Env → LifeCtx → List CVTy → Option CCTy → Comp → IM TNode
  | 0, _, _, _, exp, m => pure (.mk (.comp m) (tyC exp) [] [])
  | n + 1, E, Δ, T, exp, m => do
    let E := match exp with
      | some C => E.atC C
      | none => E
    let node (C : Option CCTy) (ks : List TNode) (bs : List Binder := []) : TNode :=
      .mk (.comp m) (tyC (exp <|> C)) bs ks
    match m with
    | .ret _ V => do
      let e := match exp.bind effRow? with | some (_, A) => some A | _ => none
      let a ← inferV n E Δ T e V
      pure (node (a.ty.v?.map .ret) [a])
    | .bind _ x oA M N _ => do
      let A' := oA.bind fun A => (E.elabV Δ A).toOption
      let hd ← inferC n E Δ T (A'.map (effOf (E.row.getD []))) M
      let A := A' <|> (match hd.ty.c?.bind effRow? with | some (_, A) => some A | _ => none)
      -- A head that performs operations puts the rest at the row (SPEC §19).
      let E := match hd.ty.c?.bind effRow? with
        | some (o :: os, _) => if E.row.isNone then { E with row := some (o :: os) } else E
        | _ => E
      -- A head that lends a place hands it back first: `x` is the second component (SPEC §11).
      let headLends := match M with | .ret _ V => valLends V | _ => false
      let A := if oA.isSome || !headLends then A else match A with
        | some (.tensor _ B) => some B
        | _ => none
      let b ← mkBinder x.name A
      let rest ← inferC n (E.push (some x.name)) Δ (slot A :: T) exp N
      pure (node rest.ty.c? [hd, rest] [b])
    | .force _ x =>
      pure (node (match lookupVar x.name E.vars with
        | some i => match T[i]? with
          | some (.thunk C) => some C
          | _ => none
        | none => none) [])
    | .lam _ x A M => do
      let A' := (E.elabV Δ A).toOption
      let e := match exp with | some (.arr _ C) => some C | _ => none
      let b ← mkBinder x.name A'
      let body ← inferC n (E.push (some x.name)) Δ (slot A' :: T) e M
      pure (node (do pure (.arr (← A') (← body.ty.c?))) [body] [b])
    | .app _ M _ => do
      let f ← inferC n E Δ T none M
      pure (node (match f.ty.c? with | some (.arr _ C) => some C | _ => none) [f])
    | .with_ _ M N => do
      let (e₁, e₂) := match exp with
        | some (.amp C D) => (some C, some D)
        | _ => (none, none)
      let E' := E.push none |>.push none
      let a ← inferC n E' Δ (withT T) e₁ M
      let b ← inferC n E' Δ (withT T) e₂ N
      pure (node (do pure (.amp (← a.ty.c?) (← b.ty.c?))) [a, b])
    | .proj _ i M => do
      let a ← inferC n E Δ T none M
      pure (node (match a.ty.c? with
        | some (.amp C D) => some (if i then C else D)
        | _ => none) [a])
    | .top _ => pure (node (some .top) [])
    | .letUnit _ V M => do
      let a ← inferV n E Δ T (some .unit) V
      let body ← inferC n E Δ T exp M
      pure (node body.ty.c? [a, body])
    | .letPair _ x y V M => do
      let a ← inferV n E Δ T none V
      let (A, B) := match a.ty.v? with
        | some (.tensor A B) => (some A, some B)
        | _ => (none, none)
      let bx ← mkBinder x.name A
      let byy ← mkBinder y.name B
      let body ← inferC n (E.push (some x.name) |>.push (some y.name)) Δ
        (slot B :: slot A :: T) exp M
      pure (node body.ty.c? [a, body] [bx, byy])
    | .case _ V x M y N => do
      let a ← inferV n E Δ T none V
      let (A, B) := match a.ty.v? with
        | some (.sum A B) => (some A, some B)
        | _ => (none, none)
      let bx ← mkBinder x.name A
      let m₁ ← inferC n (E.push (some x.name)) Δ (slot A :: T) exp M
      -- At a row (SPEC §19), the second arm is at the row too: the first may be pure, or an abort.
      let lift (C : CCTy) : CCTy := match effRow? C, E.row with
        | some (_, A), some S@(_ :: _) => effOf S A
        | _, _ => C
      let C := exp <|> m₁.ty.c?.map lift
      let byy ← mkBinder y.name B
      let m₂ ← inferC n (E.push (some y.name)) Δ (slot B :: T) C N
      pure (node (C <|> m₂.ty.c?) [a, m₁, m₂] [bx, byy])
    | .absurd _ V => do
      let a ← inferV n E Δ T (some .zero) V
      pure (node none [a])
    | .lamL _ x b M => do
      let bl := (E.elabL Δ b).toOption
      let (v, e) := match exp with
        | some (.all v _ C) => (v, some C)
        | _ => (Δ.freshVar, none)
      let E' := { E.push none with lenv := (x.name, v) :: E.lenv }
      let body ← inferC n E' (Δ.extend v (bl.getD .top)) (.unit :: T) e M
      pure (node (do pure (.all v (← bl) (← body.ty.c?))) [body])
    | .inst _ M _ => do
      let a ← inferC n E Δ T none M
      pure (node (askC E Δ T m) [a])
    | .nuIn _ M => do
      let e := match exp with | some (.nu B) => some B.unroll | _ => none
      let a ← inferC n E Δ T e M
      pure (node (if exp.isSome then none else askC E Δ T m) [a])
    | .nuOut _ M => do
      let a ← inferC n E Δ T none M
      pure (node (askC E Δ T m) [a])
    | .ascribe _ M C => do
      let C' := (E.elabC Δ C).toOption
      let a ← inferC n E Δ T C' M
      pure (node C' [a])
    | .loop _ _ src V M N => do
      let a ← inferV n E Δ T none V
      match src.var? with
      | some x =>
        let bx ← mkBinder x.name none
        let body ← inferC n (E.push (some x.name)) Δ (.unit :: T) none M
        let rest ← inferC n E Δ T exp N
        pure (node none [a, body, rest] [bx])
      | none =>
        let body ← inferC n E Δ T none M
        let rest ← inferC n E Δ T exp N
        pure (node none [a, body, rest] [])
    | .perform sp k i V => do
      let o := (findOp E sp "perform" k i).toOption
      let a ← inferV n E Δ T (o.map (·.2.1.A)) V
      pure (node (o.map fun ⟨S, o, _⟩ => effOf S o.B) [a])
    | .abort sp k i V => do
      let o := (findOp E sp "abort" k i).toOption
      let a ← inferV n E Δ T (o.map (·.2.1.A)) V
      pure (node (o.map fun ⟨S, _, _⟩ => effOf S .zero) [a])
    | .handle _ k _ hr hc M => do
      let ar ← inferV n E Δ T none hr
      let ac ← inferV n E Δ T none hc
      let sig : Option (CRow × CVTy × CVTy × List (CCount × CVTy × CVTy)) := do
        let ⟨S, A, R, _⟩ ← retRead (← ar.ty.v?)
        let ⟨Es, _⟩ ← clausesRead S R (← ac.ty.v?)
        pure (S, A, R, Es)
      let e := sig.map fun (S, A, _, Es) =>
        effOf (BoCa.Fig16.LogRel.Core.Row.ofEff (UInt32.ofNat k) Es 0 ++ S) A
      let a ← inferC n E Δ T e M
      pure (node (sig.map fun (S, _, R, _) => effOf S R) [ar, ac, a])
    | .unwind _ x oA M D N => do
      let A' := oA.bind fun A => (E.elabV Δ A).toOption
      let hd ← inferC n E Δ T (A'.map (effOf (E.row.getD []))) M
      let hr := hd.ty.c?.bind effRow?
      let A := A' <|> hr.map (·.2)
      let S := E.row <|> hr.map (·.1)
      let E := { E with row := S }
      let b ← mkBinder x.name A
      let d ← inferC n (E.push none) Δ (.unit :: T)
        (S.map fun _ => effOf [] .unit) D
      let rest ← inferC n (E.push (some x.name)) Δ (slot A :: T) exp N
      pure (node rest.ty.c? [hd, d, rest] [b])
    | .withbor2r sp x b A B r _ m M => do
      -- R1 (SPEC §29): the body sees the view alone.
      let bl := (E.elabL Δ b).toOption.getD .top
      let A' := (E.elabV Δ A).toOption
      let B' := (E.elabV Δ B).toOption
      let S := (E.elabRow Δ sp r).toOption
      let v := Δ.freshVar
      let E' : Env := { E with vars := [some m.name], own := [false], nExt := 0,
                                lenv := (x.name, v) :: E.lenv, row := S }
      let bm ← mkBinder m.name (A'.map (.mut (.var v)))
      let body ← inferC n E' (Δ.extend v bl) [slot (A'.map (.mut (.var v)))]
        (do pure (effOf (← S) (.box (.var v) (← B')))) M
      pure (node (do pure (effOf (← S) (.tensor (.ref (← A')) (← B')))) [body] [bm])
end

/-! ### Externs -/

/-- The externs declared before index `upto`, in declaration order, elaborated as the checker
elaborates them (`Frontend.Check.externs`). -/
def externsBefore (ds : Array Decl) (upto : Nat) : List (String × CVTy) :=
  (List.range upto).foldl (init := []) fun acc k =>
    match (ds[k]? : Option Decl) with
    | some (.extern _ n A) =>
      match (⟨{ decls := ds, upto := k }, [], [], [], [], 0, none⟩ : Env).elabV LifeCtx.empty A with
      | .ok A' => acc ++ [(n.name, A')]
      | .error _ => acc
    | _ => acc

end Frontend.Elab
