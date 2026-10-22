import Frontend.Syntax

/-!
# Frontend — Elab — hygiene  `[#481]`

The elaboration moves code between scopes. A control handler's clauses are code of the handler's
declaration, and they run at each `with` of it: as closures built where the `with` is, or, when
every operation is abortive, after the handler in the scope of the `with` (SPEC §19). The
handler's parameters are bound there, around the body the user wrote. Generated code refers to
declarations by name (a clause function `h__op`, a copy `f__…`, a library function), in scopes
where the user's locals are. Names are not resolved before this happens: a lower-case name is
`Val.var` whether it is a local or a declaration (`Frontend/README.md`, choice 13). So a binder
moved into the user's scope can capture the user's variable of the same name, and a user's local
can capture a name the moved code means as a declaration.

This pass runs once, on every declaration after `include`s are expanded and before any other
elaboration, and establishes two facts that rule out both captures:

* **No local has the name of a declaration.** A local binder whose name is a top-level name of
  the program (a `def` or `fn`, an `extern`, an operation, a declaration of a
  library the elaboration may bring in), or contains `__` (the names of generated declarations,
  `clauseName`, `copyName`), is renamed in its scope to a fresh name. Every free name of code the
  elaboration moves into a user's scope is then a declaration, and no local there can capture it.
  The capabilities `stdin`, `stdout` and `stderr` are not renamed: they are passed and handed
  back by name (a function's capability parameter has the capability's name, SPEC §11), so a
  local of that name is the capability.
* **A control handler's code has fresh names.** Its parameters are bound at each `with` around
  the body the user wrote, and its clauses run in the scope of the `with` (or as closures built
  there), so every binder of the handler, its parameters, its clauses' parameters and the
  binders of their bodies, gets a name no user code mentions, `hy{n}c{h}_{x}` for the handler
  `h`. A user's variable is then never taken for one of the handler's, nor the other way round,
  by an elaboration that identifies variables by name (a loop's threaded variables, #493).

Renaming a bound variable consistently in its scope is α-conversion: the program means what it
did. A fresh name is `hy{n}_{x}`, `n` counting the renamings of one declaration, so the renaming
is a function of the declaration alone (`Sugar.elaborateS` compares declarations with the
program's to tell its own from a library's). Like every generated name (`io_…`, `fx_…`), the
prefix is a convention: the parser does not reserve it.
-/

namespace Frontend.Hygiene

/-- The renamings in force: a name as written and the name it has in the program. -/
abbrev Ren := List (String × String)

/-- The number of the next fresh name of the declaration, and what follows the number in its
fresh names: `c{h}` in the code of the control handler `h`, else nothing. -/
abbrev HM := StateM (Nat × String)

/-- What a binder named `x` is called in its scope. A binder of a name already renamed keeps
the new name: it shadows it as `x` shadowed `x`, and an assignment, elaborated as a binding of the
same name (`x = e` in a `let mut` scope, a handler's state at a resume), stays one. Otherwise a
fresh name when `force` holds or `x` is a declaration's name (`glob x`), else `x`. -/
def bind (glob : String → Bool) (ρ : Ren) (x : Ident) (force : Bool := false) : HM (Ident × Ren) :=
  match ρ.lookup x.name with
  | some y => pure ({ x with name := y }, ρ)
  | none =>
    if force || glob x.name then do
      let y ← modifyGet fun (n, sfx) => (s!"hy{n}{sfx}_{x.name}", (n + 1, sfx))
      pure (⟨y, x.span⟩, (x.name, y) :: ρ)
    else pure (x, ρ)

/-- A binder of each name in `xs`, in order, each in the scope of those before it. -/
def bindAll (glob : String → Bool) (ρ : Ren) (xs : List Ident) (force : Bool := false) :
    HM (List Ident × Ren) :=
  xs.foldlM (init := ([], ρ)) fun (acc, ρ) x => do
    let (x', ρ') ← bind glob ρ x force
    pure (acc ++ [x'], ρ')

/-- An occurrence of `x`. -/
def look (ρ : Ren) (x : String) : String := (ρ.lookup x).getD x

def lookI (ρ : Ren) (x : Ident) : Ident := { x with name := look ρ x.name }

mutual
/-- `V` with its binders renamed by `glob` and its occurrences by `ρ`, and the declarations its
explicit instances name (`defApp`) by `defs`. The sites `hndCtl`,
`forSite` and `pullSite` are made by `Frontend.Elab.Effects`, after this pass: only the variable
a `for`'s site threads is a name of the program in them. -/
def _root_.Frontend.Val.hygD (defs : Ren) (glob : String → Bool) (ρ : Ren) : Val → HM Val
  | .var sp x => pure (.var sp (look ρ x))
  | .clone sp x => pure (.clone sp (look ρ x))
  | .defApp sp n args => pure (.defApp sp ((defs.lookup n).getD n) args)
  | .unit sp => pure (.unit sp)
  | .pair sp V W => do pure (.pair sp (← V.hygD defs glob ρ) (← W.hygD defs glob ρ))
  | .inl sp V => do pure (.inl sp (← V.hygD defs glob ρ))
  | .inr sp V => do pure (.inr sp (← V.hygD defs glob ρ))
  | .thunk sp M => do pure (.thunk sp (← M.hygD defs glob ρ))
  | .thunkv sp M => do pure (.thunkv sp (← M.hygD defs glob ρ))
  | .bangThunk sp M => do pure (.bangThunk sp (← M.hygD defs glob ρ))
  | .bangThunkv sp M => do pure (.bangThunkv sp (← M.hygD defs glob ρ))
  | .unbang sp V => do pure (.unbang sp (← V.hygD defs glob ρ))
  | .boxed sp a V => do pure (.boxed sp a (← V.hygD defs glob ρ))
  | .unbox sp V => do pure (.unbox sp (← V.hygD defs glob ρ))
  | .sub sp V a => do pure (.sub sp (← V.hygD defs glob ρ) a)
  | .roll sp V => do pure (.roll sp (← V.hygD defs glob ρ))
  | .unroll sp V => do pure (.unroll sp (← V.hygD defs glob ρ))
  | .run sp M => do pure (.run sp (← M.hygD defs glob ρ))
  | .app sp V W => do pure (.app sp (← V.hygD defs glob ρ) (← W.hygD defs glob ρ))
  | .inst sp V a => do pure (.inst sp (← V.hygD defs glob ρ) a)
  | .ascribe sp V A => do pure (.ascribe sp (← V.hygD defs glob ρ) A)
  | .const sp c => pure (.const sp c)
  | .shorten sp m s a V => do pure (.shorten sp m s a (← V.hygD defs glob ρ))
  | .lend sp x m => pure (.lend sp (lookI ρ x) m)
  | .sugar sp (.forSite i) => pure (.sugar sp (.forSite { i with w := look ρ i.w }))
  | .sugar sp (.pullSite i) => pure (.sugar sp (.pullSite { i with w := look ρ i.w }))
  | .sugar sp s => pure (.sugar sp s)
  | .mark sp k V => do pure (.mark sp k (← V.hygD defs glob ρ))
  | .reify sp B R r V => do pure (.reify sp B R r (← V.hygD defs glob ρ))

/-- `M` with its binders renamed by `glob` and its occurrences by `ρ`. -/
def _root_.Frontend.Comp.hygD (defs : Ren) (glob : String → Bool) (ρ : Ren) : Comp → HM Comp
  | .ret sp V => do pure (.ret sp (← V.hygD defs glob ρ))
  | .bind sp x A M N lin => do
    let M' ← M.hygD defs glob ρ
    let (x', ρ') ← bind glob ρ x
    pure (.bind sp x' A M' (← N.hygD defs glob ρ') lin)
  | .force sp x => pure (.force sp (lookI ρ x))
  | .lam sp x A M => do
    let (x', ρ') ← bind glob ρ x
    pure (.lam sp x' A (← M.hygD defs glob ρ'))
  | .app sp M x => do pure (.app sp (← M.hygD defs glob ρ) (lookI ρ x))
  | .with_ sp M N => do pure (.with_ sp (← M.hygD defs glob ρ) (← N.hygD defs glob ρ))
  | .proj sp i M => do pure (.proj sp i (← M.hygD defs glob ρ))
  | .top sp => pure (.top sp)
  | .letUnit sp V M => do pure (.letUnit sp (← V.hygD defs glob ρ) (← M.hygD defs glob ρ))
  | .letPair sp x y V M => do
    let V' ← V.hygD defs glob ρ
    let (x', ρ₁) ← bind glob ρ x
    let (y', ρ₂) ← bind glob ρ₁ y
    pure (.letPair sp x' y' V' (← M.hygD defs glob ρ₂))
  | .case sp V x M y N => do
    let V' ← V.hygD defs glob ρ
    let (x', ρx) ← bind glob ρ x
    let M' ← M.hygD defs glob ρx
    let (y', ρy) ← bind glob ρ y
    pure (.case sp V' x' M' y' (← N.hygD defs glob ρy))
  | .absurd sp V => do pure (.absurd sp (← V.hygD defs glob ρ))
  | .lamL sp x b M => do pure (.lamL sp x b (← M.hygD defs glob ρ))
  | .inst sp M a => do pure (.inst sp (← M.hygD defs glob ρ) a)
  | .nuIn sp M => do pure (.nuIn sp (← M.hygD defs glob ρ))
  | .nuOut sp M => do pure (.nuOut sp (← M.hygD defs glob ρ))
  | .ascribe sp M C => do pure (.ascribe sp (← M.hygD defs glob ρ) C)
  | .loop sp ℓ (.each x) V M N => do
    let V' ← V.hygD defs glob ρ
    let (x', ρx) ← bind glob ρ x
    let M' ← M.hygD defs glob ρx
    pure (.loop sp ℓ (.each x') V' M' (← N.hygD defs glob ρ))
  | .loop sp ℓ src V M N => do
    let V' ← V.hygD defs glob ρ
    let M' ← M.hygD defs glob ρ
    pure (.loop sp ℓ src V' M' (← N.hygD defs glob ρ))
  | .perform sp n i V => do pure (.perform sp n i (← V.hygD defs glob ρ))
  | .abort sp n i V => do pure (.abort sp n i (← V.hygD defs glob ρ))
  | .handle sp n hf st hr hc M => do
    let hr' ← hr.hygD defs glob ρ
    let hc' ← hc.hygD defs glob ρ
    pure (.handle sp n hf st hr' hc' (← M.hygD defs glob ρ))
  | .unwind sp x A M D N => do
    let M' ← M.hygD defs glob ρ
    let D' ← D.hygD defs glob ρ
    let (x', ρx) ← bind glob ρ x
    pure (.unwind sp x' A M' D' (← N.hygD defs glob ρx))
  | .withbor2r sp x b A B r p m M => do
    let (m', ρm) ← bind glob ρ m
    pure (.withbor2r sp x b A B r (lookI ρ p) m' (← M.hygD defs glob ρm))
end

/-- `V` with its binders renamed by `glob` and its occurrences by `ρ`. -/
def _root_.Frontend.Val.hyg (glob : String → Bool) (ρ : Ren) (V : Val) : HM Val := V.hygD [] glob ρ

/-- `M` with its binders renamed by `glob` and its occurrences by `ρ`. -/
def _root_.Frontend.Comp.hyg (glob : String → Bool) (ρ : Ren) (M : Comp) : HM Comp := M.hygD [] glob ρ

/-- A clause, in the scope `ρ`: its parameters bind in its body. -/
def _root_.Frontend.Clause.hyg (glob : String → Bool) (ρ : Ren) (c : Clause) : HM Clause := do
  let (ps, ρ') ← bindAll glob ρ c.params
  pure { c with params := ps, body := ← c.body.hyg glob ρ' }

/-- A declaration with its locals renamed (the module comment): the locals named as a
declaration by `glob`, and a control handler's parameters. -/
def _root_.Frontend.Decl.hyg (glob : String → Bool) (d : Decl) : Decl :=
  (go d).run' (0, "")
where
  go : Decl → HM Decl
    | .def_ sp n ps A V mk => do pure (.def_ sp n ps A (← V.hyg glob []) mk)
    | .main sp C M => do pure (.main sp C (← M.hyg glob []))
    | .handler sp n st S e cs l => do
      let (st', ρ) ← bind glob [] st
      pure (.handler sp n st' S e (← cs.mapM (Clause.hyg glob ρ)) l)
    | .chandler sp h => do
      -- Every binder of the handler's code is renamed (the module comment).
      set (0, s!"c{h.name.name.replace "_" "U"}")
      let all : String → Bool := fun _ => true
      let (ps, ρ) ← bindAll all [] (h.params.map (·.1))
      let (rx, rA, rM) := h.ret
      let (rx', ρr) ← bind all ρ rx
      let rM' ← rM.hyg all ρr
      let cs ← h.clauses.mapM (Clause.hyg all ρ)
      pure (.chandler sp { h with params := ps.zip (h.params.map (·.2)), ret := (rx', rA, rM'),
                                  clauses := cs })
    | d => pure d

/-- A library's declaration with the library's declarations named in `ρ` renamed as `ρ` says, in
its own name and wherever it names them: the program declares those names itself, and its
declarations shadow the library's (SPEC §41, rule R1), whose own code keeps meaning its own. -/
def _root_.Frontend.Decl.renameDecls (ρ : Ren) (d : Decl) : Decl :=
  if ρ.isEmpty then d else
  let n' (n : Ident) : Ident := { n with name := look ρ n.name }
  match d with
  | .def_ sp n ps A V mk => .def_ sp (n' n) ps A ((V.hygD ρ (fun _ => false) ρ).run' (0, "")) mk
  | .extern sp n A => .extern sp (n' n) A
  | d => d

/-- The top-level names of value-level declarations: what a local must not be named. -/
def _root_.Frontend.Decl.globals : Decl → List String
  | .def_ _ n .. | .extern _ n _ => [n.name]
  | .effect _ _ _ ops => ops.map (·.name.name)
  | _ => []

/-- Whether a local named `x` is renamed, given the top-level names `gs`. -/
def isGlobal (gs : List String) (x : String) : Bool :=
  gs.contains x || dunder x.toList
where
  /-- Whether `__` occurs (structural, so that the kernel evaluates it, `Frontend/Check/CrossCheck.lean`). -/
  dunder : List Char → Bool
    | '_' :: '_' :: _ => true
    | _ :: cs => dunder cs
    | [] => false

/-- The name as the user wrote it, for messages: a fresh name `hy{n}_{x}` (`hy{n}c{h}_{x}`) is
shown as `x`. -/
def written (x : String) : String :=
  match x.splitOn "_" with
  | p :: rest@(_ :: _) =>
    let tl := (p.toList.drop 2)
    if p.startsWith "hy" && (tl.head?.map Char.isDigit).getD false && tl.all Char.isAlphanum then
      "_".intercalate rest
    else x
  | _ => x

end Frontend.Hygiene
