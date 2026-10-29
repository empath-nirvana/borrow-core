import Frontend.Elab.Subst
import Frontend.Lexer

/-!
# Frontend — Elab — data declarations  `[spec §42]`

The rules of SPEC §42's table that need only the declarations, not types: a `data` declaration
and its group to `type` and `shape` declarations (D1–D3), constructors and record literals (E1,
E2, E4), the declarations a field may be of (E5, E6), `match` compiled to a decision tree with
its exhaustiveness and redundancy reports (M1–M4), and a `fold` block's arms compiled as its
algebra, with a block reassembled from its cells in a `fold_reuse` arm (F1, F2, SPEC §60). The
parser holds the table and calls them; the typed rules, a field read and a field update the
declarations disagree on, and the fold a `fold` block is, are `Frontend/Sugar.lean`'s
(`fieldRead`, `resolveField`, `surfV`'s `fold` case).

Every rule elaborates into existing core terms: `⊗`, `⊕`, `μ` with `roll`/`unroll`, `ref` cells,
`alloc_s` and `free`, `case`, `let`, §6's folds, and the surface's `alloc(e)`, `free(e)`, `==` and
`modify`.
No rule decides an alias, a lend's extent or an escape.
-/

namespace Frontend.Data

/-! ### The table -/

/-- The `data` declarations in scope, in the order they are declared. A later declaration of a
name hides an earlier one. -/
abbrev Table := List DataDecl

/-- The declaration named `n`, the last one. -/
def Table.decl? (t : Table) (n : String) : Option DataDecl :=
  t.reverse.find? (·.name.name == n)

/-- The declaration of the constructor `c`, the last one, and the constructor's index. -/
def Table.con? (t : Table) (c : String) : Option (DataDecl × Nat) :=
  t.reverse.findSome? fun d => (d.cons.findIdx? (·.name.name == c)).map (d, ·)

/-- A type's head name and its type and lifetime arguments: `N[A, …]<'a, …>`. -/
def headOf : VTy → Option (String × List VTy × List Life)
  | .name _ n => some (n, [], [])
  | .app _ F A => (headOf F).map fun (n, As, ls) => (n, As ++ [A], ls)
  | .lapp _ F a => (headOf F).map fun (n, As, ls) => (n, As, ls ++ [a])
  | _ => none

mutual
/-- The type names `A` mentions. -/
def _root_.Frontend.VTy.tyNames : VTy → List String
  | .name _ n => [n]
  | .tensor _ A B | .sum _ A B | .lolli _ A B | .app _ A B => A.tyNames ++ B.tyNames
  | .ref _ A | .imm _ _ A | .mut _ _ A | .box _ _ A | .bang _ A | .view _ _ A | .array _ A
  | .arrayImm _ _ A | .arrayMut _ _ A | .lapp _ A _ | .all _ _ _ A => A.tyNames
  | .mu _ X A => A.tyNames.filter (· != X.name)
  | .sized _ D S A => D.tyNames ++ S.tyNames ++ A.tyNames
  | .thunk _ C => C.tyNames
  | .rowed _ F r => F.tyNames ++ r.tyNames
  | .block _ σ | .val _ σ | .fam _ _ _ σ => σ.tyNames
  | _ => []

def _root_.Frontend.CTy.tyNames : CTy → List String
  | .ret _ A | .delay _ A | .stream _ A => A.tyNames
  | .arr _ A C => A.tyNames ++ C.tyNames
  | .amp _ C D => C.tyNames ++ D.tyNames
  | .all _ _ _ C | .nu _ _ C => C.tyNames
  | .iter _ A R R' => A.tyNames ++ R.tyNames ++ R'.tyNames
  | .loop _ A B => A.tyNames ++ B.tyNames
  | .pull _ A B R => A.tyNames ++ B.tyNames ++ R.tyNames
  | .eff _ _ A => A.tyNames
  | _ => []

def _root_.Frontend.Shape.tyNames : Shape → List String
  | .leaf _ A => A.tyNames
  | .node _ σ τ => σ.tyNames ++ τ.tyNames
  | .name _ n => [n]
end

/-- `A` mentions one of the type names `ns`. -/
def mentions (ns : List String) (A : VTy) : Bool := A.tyNames.any ns.contains

/-- `A` mentions one of `ns` other than under a cell (`box A`, which is `ref A`). -/
def _root_.Frontend.VTy.bare (ns : List String) : VTy → Bool
  | .ref _ _ => false
  | .name _ n => ns.contains n
  | .tensor _ A B | .sum _ A B | .app _ A B => A.bare ns || B.bare ns
  | .lapp _ A _ => A.bare ns
  | A => mentions ns A

/-- The data declarations `d`'s fields name. -/
def _root_.Frontend.DataDecl.refs (t : Table) (d : DataDecl) : List String :=
  (d.cons.flatMap fun c => c.fields.flatMap (·.ty.tyNames)).eraseDups.filter fun n =>
    (t.decl? n).isSome

/-- The names reachable from `n` along the declarations' references, within `fuel` steps. -/
def reach (t : Table) : Nat → List String → List String → List String
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | k + 1, n :: todo, seen =>
    if seen.contains n then reach t k todo seen else
    let next := ((t.decl? n).map (·.refs t)).getD []
    reach t k (next ++ todo) (n :: seen)

/-- The names reachable from `n` in one or more steps. -/
def reachFrom (t : Table) (n : String) : List String :=
  let fuel := (t.length + 1) * (t.length + 1) * 4
  reach t fuel (((t.decl? n).map (·.refs t)).getD []) []

/-- `n`'s group: the declarations that reach it and that it reaches, `n` among them when it is
recursive, in the order they are declared. -/
def groupOf (t : Table) (n : String) : List String :=
  let fwd := reachFrom t n
  let g := t.filter fun d => (d.name.name == n && fwd.contains n) ||
    (fwd.contains d.name.name && (reachFrom t d.name.name).contains n)
  (g.map (·.name.name)).eraseDups

/-- The graph of the group `g` without `r` has no cycle: `r` lies on every cycle of `g`. -/
def onEveryCycle (t : Table) (g : List String) (r : String) : Bool :=
  let rest := t.filter fun d => g.contains d.name.name && d.name.name != r
  let t' : Table := rest.map fun d => { d with cons := d.cons.map fun c =>
    { c with fields := c.fields.map fun f => { f with ty := f.ty.subst [(r, .unit .none)] } } }
  rest.all fun d => !(reachFrom t' d.name.name).contains d.name.name

/-! ### Declarations: D1–D3 -/

/-- What the elaboration knows of a constructor. -/
structure CInfo where
  name : String
  idx : Nat
  fields : List DField
  /-- A block: allocated whole, one cell per field (SPEC §42, *Recursion*). -/
  block : Bool

/-- What the elaboration knows of a declaration: its group's root, whether its type is a `μ`
(it is the root of a recursive group), its constructors, and whether it has parameters. -/
structure Info where
  decl : DataDecl
  group : List String
  root : String
  rolls : Bool
  cons : List CInfo

def Info.mono (i : Info) : Bool := i.decl.tps.isEmpty && i.decl.lps.isEmpty

def Info.n (i : Info) : Nat := i.cons.length

/-- The shape name of a block. -/
def shapeName (n c : String) : String := s!"{n}_{c}"

/-- The group of `n`, its root, and whether it is recursive; refused when no member of a group
lies on every cycle (the single-root rule, SPEC §42), and when its members do not share their
parameters. -/
def groupInfo (t : Table) (d : DataDecl) : Except String (List String × String × Bool) := do
  let g := groupOf t d.name.name
  if g.isEmpty then return ([d.name.name], d.name.name, false)
  let some r := g.find? (onEveryCycle t g ·)
    | throw <| s!"the declarations {", ".intercalate (g.map (s!"`{·}`"))} are mutually recursive " ++
        "with no member on every cycle: not provided (the single-root rule)"
  for m in g do
    if let some e := t.decl? m then
      if e.tps.map (·.name) != d.tps.map (·.name) || e.lps.map (·.name) != d.lps.map (·.name) then
        throw <| s!"the mutually recursive declarations `{d.name.name}` and `{m}` have different " ++
          "parameters: not provided"
  pure (g, r, true)

/-- The constructors of `d` in its group `g` with root `r`: a block is a constructor of a
recursive declaration with a field in which the root occurs other than under `box`. -/
def consInfo (d : DataDecl) (rec_ : Bool) (r : String) : List CInfo :=
  d.cons.zipIdx.map fun (c, i) =>
    { name := c.name.name, idx := i, fields := c.fields,
      block := rec_ && c.fields.any (·.ty.bare [r]) }

/-- `info t n`: what the elaboration knows of the declaration `n`. -/
def info (t : Table) (n : String) : Except String Info := do
  let some d := t.decl? n | throw <| s!"no `data` declaration `{n}`"
  let (g, r, rec_) ← groupInfo t d
  pure { decl := d, group := g, root := r, rolls := rec_ && r == n, cons := consInfo d rec_ r }

/-- The right-nested `⊗` of `As`, `1` when there are none. -/
def tupleTy (sp : Span) : List VTy → VTy
  | [] => .unit sp
  | [A] => A
  | A :: As => .tensor sp A (tupleTy sp As)

/-- The right-nested `⊕` of `As`. -/
def sumTy (sp : Span) : List VTy → VTy
  | [] => .zero sp
  | [A] => A
  | A :: As => .sum sp A (sumTy sp As)

/-- A recursive occurrence of a member `m` of the group `g` is at `m`'s own parameters. -/
def regular (g : List String) (d : DataDecl) : VTy → Except String Unit
  | A => do
    let own : List VTy := d.tps.map fun p => .name .none p.name
    let rec go : Nat → VTy → Except String Unit
      | 0, _ => pure ()
      | k + 1, A => do
        match headOf A with
        | some (h, As, _) =>
          if g.contains h then
            unless As.map VTy.strip == own do
              throw <| s!"`{h}` occurs in its own declaration at other parameters than its own: a " ++
                "nested datatype is not provided"
          else for B in As do go k B
        | none => match A with
          | .tensor _ B C | .sum _ B C | .lolli _ B C => do go k B; go k C
          | .ref _ B | .bang _ B | .array _ B | .imm _ _ B | .mut _ _ B | .view _ _ B => go k B
          | _ => pure ()
    go 64 A

/-- `A` with each application `N[…]` of a name of `σ` replaced by its value: the group's members
occur at their own parameters (`regular`), so the arguments are dropped. -/
def substHeads (σ : TySubst) : Nat → VTy → VTy
  | 0, A => A
  | j + 1, A => match headOf A with
    | some (h, _, _) => match σ.lookup h with
      | some B => B
      | none => match A with
        | .app sp F B => .app sp (substHeads σ j F) (substHeads σ j B)
        | .lapp sp F a => .lapp sp (substHeads σ j F) a
        | A => A
    | none => match A with
      | .tensor sp B C => .tensor sp (substHeads σ j B) (substHeads σ j C)
      | .sum sp B C => .sum sp (substHeads σ j B) (substHeads σ j C)
      | .ref sp B => .ref sp (substHeads σ j B)
      | .bang sp B => .bang sp (substHeads σ j B)
      | .array sp B => .array sp (substHeads σ j B)
      | .lolli sp B C => .lolli sp (substHeads σ j B) (substHeads σ j C)
      | .imm sp a B => .imm sp a (substHeads σ j B)
      | .mut sp a B => .mut sp a (substHeads σ j B)
      | A => A

mutual
/-- The structure of the member `n` of the group `g` whose root is `root`, its fields' types
elaborated (`fieldTyOf`) and a block's fields cells. `toX` is the variable of the root's `μ`
when the structure is the root's body, where the root is that variable; elsewhere the root is
named. `fuel` bounds the substitution, which the single-root rule makes finite. -/
def structOf (t : Table) (g : List String) (root : String) (toX : Option String) :
    Nat → String → Except String VTy
  | 0, n => throw <| s!"internal error: the structure of `{n}`"
  | k + 1, n => do
    let some d := t.decl? n | throw <| s!"no `data` declaration `{n}`"
    let rec_ := g.length > 1 || (reachFrom t root).contains root
    let cis := consInfo d rec_ root
    let pays ← cis.mapM fun c => do
      let tys ← c.fields.mapM fun f => do
        regular g d f.ty
        let A ← fieldTyOf t g root toX k f.ty
        pure (if c.block then VTy.ref .none A else A)
      pure (tupleTy .none tys)
    pure (sumTy .none pays)

/-- A field's type with the members of the group substituted: the root by its name, or by the
variable `toX`; every other member by its structure. -/
def fieldTyOf (t : Table) (g : List String) (root : String) (toX : Option String) :
    Nat → VTy → Except String VTy
  | 0, A => pure A
  | k + 1, A => do
    let names := (A.tyNames.filter g.contains).eraseDups
    if names.isEmpty then return A
    let mut σ : TySubst := []
    for m in names do
      if m == root then
        σ := σ ++ [(m, .name .none (toX.getD root))]
      else σ := σ ++ [(m, ← structOf t g root toX k m)]
    pure (substHeads σ 64 A)
end

/-- `T` with each application of a non-recursive declaration of the table that holds the
variable `X` replaced by that declaration's structure at its arguments, so that `X` is visible to
§6's `FShape`. An application of a recursive declaration, or of an abbreviation the table does not
hold, around `X` is refused: a `μ` nested in a `μ` (B14). -/
def openX (t : Table) (X : String) : Nat → VTy → Except String VTy
  | 0, A => pure A
  | k + 1, A => do
    if !A.tyNames.contains X then return A
    match headOf A with
    | some (h, As, _) =>
      if h == X then return A
      let some d := t.decl? h
        | throw <| s!"the recursive type occurs under `{h}[…]`, which is not a `data` declaration: " ++
            "not provided"
      let (_, _, rec_) ← groupInfo t d
      if rec_ then
        throw <| s!"the recursive type occurs under `{h}`, which is recursive itself: a recursion " ++
          "nested in another is not provided (B14)"
      let S ← structOf t [h] h none 64 h
      let σ : TySubst := d.tps.map (·.name) |>.zip As
      openX t X k (S.subst σ)
    | none => match A with
      | .tensor sp B C => return .tensor sp (← openX t X k B) (← openX t X k C)
      | .sum sp B C => return .sum sp (← openX t X k B) (← openX t X k C)
      | .ref sp B => return .ref sp (← openX t X k B)
      | A => pure A

/-- `T` is in §6's `FShape` over `X`: built from `⊗`, `⊕`, closed leaves and `ref X`. -/
def fshape (X : String) : VTy → Bool
  | .tensor _ A B | .sum _ A B => fshape X A && fshape X B
  | .ref _ (.name _ _) => true
  | A => !A.tyNames.contains X

/-- A fresh type variable for `d`'s `μ`. -/
def muVar (d : DataDecl) (avoid : List String) : String :=
  let bad := avoid ++ d.tps.map (·.name)
  (["X", "Y", "Z", "R", "Rec"].find? (!bad.contains ·)).getD "XRec"

/-- The `type` and `shape` declarations of the group of `d`, when `d` is its first member in
declaration order (the others give none): the root first, then the other members in the order of
their dependencies, each a block's shape after its type when the declaration has no parameters
(SPEC §42, D1–D3).  `[spec §42]` -/
def typeDecls (t : Table) (sp : Span) (d : DataDecl) : Except Error (List Decl) := do
  let err {α} (m : String) : Except Error α := throw ⟨d.name.span, m⟩
  let (g, root, rec_) ← match groupInfo t d with
    | .ok r => pure r
    | .error m => err m
  if g.head? != some d.name.name then return []
  let members := t.filter (g.contains ·.name.name) |>.map (·.name.name) |>.eraseDups
  -- The root's structure, with `X` for the root and the other members substituted.
  let avoid := (t.flatMap fun e => e.cons.flatMap fun c => c.fields.flatMap (·.ty.tyNames)) ++
    t.map (·.name.name)
  let some rd := t.decl? root | err <| s!"internal error: the root `{root}`"
  let X := muVar rd avoid
  let mk (n : String) (A : VTy) : Decl :=
    match t.decl? n with
    | some e => .type sp e.name e.tps e.lps A
    | none => .type sp ⟨n, sp⟩ [] [] A
  -- Each block's fields: cells holding the recursive type only as `ref X`.
  let checkFields (n : String) : Except Error Unit := do
    let some e := t.decl? n | pure ()
    for c in consInfo e rec_ root do
      for (f, j) in c.fields.zipIdx do
        let A ← match fieldTyOf t g root (some X) 64 f.ty with
          | .ok A => pure A
          | .error m => err m
        let A ← match openX t X 64 A with
          | .ok A => pure A
          | .error m => err m
        let what := match f.name with
          | some x => s!"the field `{x.name}` of `{c.name}`"
          | none => s!"field {j + 1} of `{c.name}`"
        if c.block then
          unless (A matches .name _ _) || !A.tyNames.contains X do
            err <| s!"{what} holds `{root}` inside another type (`{ppTy f.ty}`): write `box` at " ++
              s!"the recursive type (`{ppTy (f.ty.subst [(root, .ref .none (.name .none root))])}`), " ++
              s!"or make the field `{root}` itself"
        else
          unless fshape X A do
            err <| s!"{what} holds `{root}` under a cell of another type (`{ppTy f.ty}`): write " ++
              s!"`box` directly at `{root}`"
  if rec_ then for m in members do checkFields m
  let rootS ← match structOf t g root (if rec_ then some X else none) 64 root with
    | .ok S => pure S
    | .error m => err m
  let rootS ← if rec_ then match openX t X 64 rootS with
      | .ok S => pure S
      | .error m => err m
    else pure rootS
  let rootT : VTy := if rec_ then .mu sp ⟨X, sp⟩ rootS else rootS
  let mut out : List Decl := [mk root rootT]
  -- The other members, each after the members it names.
  let mut done : List String := [root]
  for _ in members do
    for m in members do
      if done.contains m then continue
      let some e := t.decl? m | continue
      let deps := (e.refs t).filter fun x => members.contains x && x != m
      if deps.all done.contains then
        let S ← match structOf t [m] root none 64 m with
          | .ok S => pure S
          | .error msg => err msg
        out := out ++ [mk m S]
        done := done ++ [m]
  -- The blocks' shapes, at the declarations' named types.
  for m in members do
    let some e := t.decl? m | continue
    if !(e.tps.isEmpty && e.lps.isEmpty) then continue
    for c in consInfo e rec_ root do
      if !c.block then continue
      let leaves := c.fields.map fun f => Shape.leaf sp f.ty
      let rec node : List Shape → Shape
        | [] => .leaf sp (.unit sp)
        | [σ] => σ
        | σ :: σs => .node sp σ (node σs)
      out := out ++ [.shape sp ⟨shapeName m c.name, sp⟩ (node leaves)]
  pure out
where
  /-- A type as the messages write it. -/
  ppTy (A : VTy) : String := match headOf A with
    | some (h, [], _) => h
    | some (h, As, _) => s!"{h}[{", ".intercalate (As.map ppTy0)}]"
    | none => match A with
      | .ref _ B => s!"box {ppTy0 B}"
      | _ => "…"
  ppTy0 (A : VTy) : String := match headOf A with
    | some (h, [], _) => h
    | some (h, _, _) => s!"{h}[…]"
    | none => match A with
      | .ref _ (.name _ h) => s!"box {h}"
      | _ => "…"

/-! ### Constructors and record literals: E1, E2, E4 -/

/-- The right-nested tuple of `Vs`, `()` when there are none. -/
def tupleV (sp : Span) : List Val → Val
  | [] => .unit sp
  | [V] => V
  | V :: Vs => .pair sp V (tupleV sp Vs)

/-- The `i`th of `n` injections: `inl`, `inr (inl …)`, …, the last `inr^(n-1)`. -/
def injV (sp : Span) : Nat → Nat → Val → Val
  | 0, _, V => V
  | 1, _, V => V
  | _ + 2, 0, V => .inl sp V
  | n + 2, i + 1, V => .inr sp (injV sp (n + 1) i V)

/-- The type a constructor's value is ascribed: the declaration's name when it has no parameters. -/
def ascribed (sp : Span) (i : Info) (V : Val) : Val :=
  if i.mono then .ascribe sp V (.name sp i.decl.name.name) else V

/-- The value of the constructor `c` of `i` with the payload `P`: injected, and rolled when the
declaration is a `μ`. -/
def injectV (sp : Span) (i : Info) (c : CInfo) (P : Val) : Val :=
  let V := injV sp i.n c.idx P
  ascribed sp i (if i.rolls then .roll sp V else V)

/-- `C(e₁, …, eₖ)` (E1) and `box C(e₁, …, eₖ)` (E2): the constructor `c` applied to `args`.
A block is built with `box`; written without it, it is refused, asking for it (E3), except in an
arm of a `fold_reuse` block (`reuse`), where it is the block reassembled from the cells `args`,
which the kernel checks are cells (F2, SPEC §60).  `[spec §42, §60]` -/
def conVal (t : Table) (sp : Span) (c : String) (boxed : Bool) (args : List Val)
    (reuse : Bool := false) : Except Error Val := do
  let err {α} (m : String) : Except Error α := throw ⟨sp, m⟩
  let some (d, _) := t.con? c | err <| s!"no constructor `{c}` is declared"
  let i ← match info t d.name.name with
    | .ok i => pure i
    | .error m => err m
  let some ci := i.cons.find? (·.name == c) | err <| s!"internal error: the constructor `{c}`"
  let k := ci.fields.length
  unless args.length == k do
    err <| s!"`{c}` has {k} field{if k == 1 then "" else "s"}, but {args.length} " ++
      s!"{if args.length == 1 then "is" else "are"} given"
  if ci.block then
    unless boxed do
      if reuse then
        return injectV sp i ci (.app sp (.sugar sp (.cells c k)) (tupleV sp args))
      err <| s!"`{c}` builds a block, one cell per field: allocate it with `box {c}(…)`"
    let P : Val := if i.mono then
        .app sp (.const sp (.allocS (.name sp (shapeName i.decl.name.name c)))) (tupleV sp args)
      else tupleV sp (args.map fun a => .app sp (.sugar sp (.call "alloc")) a)
    return injectV sp i ci P
  let V := injectV sp i ci (tupleV sp args)
  if boxed then return .app sp (.sugar sp (.call "alloc")) V
  pure V

/-- A record literal `N { f: e, … }` (E4): the fields in the order the declaration has them. When
the written order differs, the values are bound in the written order first, in `run`.
`[spec §42]` -/
def recordVal (t : Table) (sp : Span) (n : String) (boxed : Bool) (fs : List (Ident × Val))
    (fresh : String → String) (reuse : Bool := false) : Except Error Val := do
  let err {α} (m : String) : Except Error α := throw ⟨sp, m⟩
  let some d := t.decl? n | err <| s!"no `data` declaration `{n}`"
  let [c] := d.cons | err <| s!"`{n}` has several constructors: a record literal builds one of a " ++
    "declaration with one"
  let names ← c.fields.mapM fun f => match f.name with
    | some x => pure x.name
    | none => err <| s!"`{n}`'s fields are not named: build it with `{c.name.name}(…)`"
  for (x, _) in fs do
    unless names.contains x.name do throw ⟨x.span, s!"`{n}` has no field `{x.name}`"⟩
    if (fs.filter (·.1.name == x.name)).length > 1 then
      throw ⟨x.span, s!"the field `{x.name}` is given twice"⟩
  for f in names do
    unless fs.any (·.1.name == f) do err <| s!"the field `{f}` of `{n}` is not given"
  if fs.map (·.1.name) == names then
    return ← conVal t sp c.name.name boxed (fs.map (·.2)) reuse
  -- In the written order, then in the declaration's.
  let vars := fs.map fun (x, _) => (x.name, fresh x.name)
  let body ← conVal t sp c.name.name boxed (names.map fun f => .var sp ((vars.lookup f).getD f)) reuse
  let M := fs.foldr (fun (x, V) M =>
    .bind sp ⟨(vars.lookup x.name).getD x.name, x.span⟩ none (.ret sp V) M false) (Comp.ret sp body)
  pure (.run sp M)

/-! ### Fields: E5, E6 -/

/-- The declarations in scope that a field `f` may be of: the one-constructor declarations with a
field so named (SPEC §42, *Fields*). A block's fields are cells, and are matched (`box`), not
read.  `[spec §42]` -/
def fieldCands (t : Table) (f : String) : Except String (List FieldCand) := do
  let mut found : List FieldCand := []
  let mut seen : List String := []
  for d in t.reverse do
    if seen.contains d.name.name then continue
    seen := seen ++ [d.name.name]
    let [c] := d.cons | continue
    let some j := c.fields.findIdx? (fun x => x.name.map (·.name) == some f) | continue
    let i ← info t d.name.name
    if i.cons.any (·.block) then
      throw <| s!"the field `{f}` of `{d.name.name}` is a block's cell: match the block (`box`)"
    let names := c.fields.map fun x => (x.name.map (·.name)).getD ""
    found := found ++ [FieldCand.mk d.name.name (d.tps.map (·.name)) names j i.rolls]
  if found.isEmpty then throw <| s!"no declaration has a field `{f}`"
  pure found

/-- The occurrences a record's `k` fields are bound to: `pre0`, `pre1`, …. -/
def fieldVars (pre : String) (k : Nat) : List String := (List.range k).map (s!"{pre}{·}")

/-- `let (x₀, (x₁, …)) = V; M`, the right-nested tuple taken apart. -/
def letTuple (sp : Span) (V : Val) : List String → Comp → (String → String) → Comp
  | [], M, _ => .letUnit sp V M
  | [x], M, _ => .bind sp ⟨x, sp⟩ none (.ret sp V) M false
  | [x, y], M, _ => .letPair sp ⟨x, sp⟩ ⟨y, sp⟩ V M
  | x :: xs, M, fresh =>
    let r := fresh x
    .letPair sp ⟨x, sp⟩ ⟨r, sp⟩ V (letTuple sp (.var sp r) xs M fresh)

/-! ### Patterns and match compilation: M1–M4

Maranget, *Compiling Pattern Matching to Good Decision Trees* (ML Workshop 2008), and *Warnings
for pattern matching* (JFP 17(3), 2007). -/

/-- A pattern of `match`. `free p` is internal: the content of a block's cell, which a `box`
pattern frees and matches with `p`. -/
inductive MPat where
  | wild (sp : Span)
  | var (x : Ident)
  /-- `(p₁, …, pₙ)`, `()` when `n = 0`. -/
  | tuple (sp : Span) (ps : List MPat)
  /-- `C(p, …)`, `box C(p, …)` (`box`). -/
  | con (sp : Span) (c : String) (box : Bool) (ps : List MPat)
  /-- An integer, byte or character literal, matched by `==`; `key` identifies it. -/
  | lit (sp : Span) (V : Val) (key : String)
  | bool (sp : Span) (b : Bool)
  | inj (sp : Span) (left : Bool) (p : MPat)
  | free (sp : Span) (p : MPat)
  deriving Inhabited

def MPat.span : MPat → Span
  | .wild sp | .tuple sp _ | .con sp _ _ _ | .lit sp _ _ | .bool sp _ | .inj sp _ _ | .free sp _ => sp
  | .var x => x.span

/-- A pattern that matches everything, a variable or `_`, possibly a cell's content. -/
def MPat.irrefutable : MPat → Bool
  | .wild _ | .var _ => true
  | .free _ p => p.irrefutable
  | _ => false

/-- A pattern written with no constructor, literal or `box`: `match`'s draft-0 form takes it. -/
def MPat.plain : MPat → Bool
  | .wild _ | .var _ => true
  | .tuple _ ps => go ps
  | _ => false
where
  go : List MPat → Bool
    | [] => true
    | p :: ps => p.plain && go ps

/-- The head of a pattern: a constructor of a declaration, a tuple of `k`, a literal, `true` or
`false`, `inl` or `inr`. -/
inductive Head where
  | con (decl : String) (i : Nat)
  | tuple (k : Nat)
  | lit (key : String)
  | bool (b : Bool)
  | inj (left : Bool)
  deriving DecidableEq, Inhabited

/-- The family a head belongs to: two heads of one column must be of one family. -/
def Head.family : Head → String
  | .con d _ => s!"data {d}"
  | .tuple k => s!"tuple {k}"
  | .lit _ => "literal"
  | .bool _ => "bool"
  | .inj _ => "sum"

/-- The heads of a family that complete it, each with its arity; `none` for literals. -/
def familySig (t : Table) : Head → Option (List (Head × Nat))
  | .con d _ => (t.decl? d).map fun e => e.cons.zipIdx.map fun (c, i) => (Head.con d i, c.fields.length)
  | .tuple k => some [(.tuple k, k)]
  | .lit _ => none
  | .bool _ => some [(.bool false, 0), (.bool true, 0)]
  | .inj _ => some [(.inj true, 1), (.inj false, 1)]

/-- A pattern's head and its sub-patterns; `none` for a variable or `_`. The constructor's
declaration is looked up in the table. -/
def MPat.head (t : Table) : MPat → Except Error (Option (Head × List MPat))
  | .wild _ | .var _ => pure none
  | .free _ p => MPat.head t p
  | .tuple _ ps => pure (some (.tuple ps.length, ps))
  | .con sp c b ps => do
    let some (d, i) := t.con? c | throw ⟨sp, s!"no constructor `{c}` is declared"⟩
    let k := (d.cons[i]?.map (·.fields.length)).getD 0
    unless ps.length == k do
      throw ⟨sp, s!"`{c}` has {k} field{if k == 1 then "" else "s"}, but the pattern gives {ps.length}"⟩
    if b then
      let block : Bool := match info t d.name.name with
        | .ok inf => ((inf.cons[i]?).map CInfo.block).getD false
        | .error _ => false
      unless block do
        throw ⟨sp, s!"`{c}` is not a block, so it holds no cells to free: match it without `box`"⟩
    let ps := if b then ps.map (fun p => MPat.free p.span p) else ps
    pure (some (.con d.name.name i, ps))
  | .lit _ _ key => pure (some (.lit key, []))
  | .bool _ b => pure (some (.bool b, []))
  | .inj _ l p => pure (some (.inj l, [p]))

/-- The specialisation of a row's first pattern `p` to the head `h` of arity `k`: its sub-patterns,
or `k` wildcards when it is irrefutable; `none` when it is another head. -/
def specRow (t : Table) (h : Head) (k : Nat) (p : MPat) : Except Error (Option (List MPat)) := do
  match ← p.head t with
  | none => pure (some ((List.range k).map fun _ => MPat.wild p.span))
  | some (h', ps) => pure (if h' == h then some ps else none)

/-- Whether the row `q` is useful after the rows `P` (Maranget 2007, `𝒰`): a value it matches that
none of `P` does, as a witness, one pattern per column; `none` when it is not useful. -/
def useful (t : Table) : Nat → List (List MPat) → List MPat → Except Error (Option (List MPat))
  | 0, _, _ => pure none
  | _ + 1, P, [] => pure (if P.isEmpty then some [] else none)
  | fuel + 1, P, q :: qs => do
    let sp := q.span
    match ← q.head t with
    | some (h, rs) =>
      let k := rs.length
      let P' ← P.filterMapM fun row => match row with
        | p :: ps => do pure ((← specRow t h k p).map (· ++ ps))
        | [] => pure none
      match ← useful t fuel P' (rs ++ qs) with
      | some w => pure (some (rebuild h k w))
      | none => pure none
    | none =>
      -- The heads the first column names.
      let heads ← P.filterMapM fun row => match row with
        | p :: _ => do pure ((← p.head t).map (·.1))
        | [] => pure none
      let fams := heads.map Head.family |>.eraseDups
      if fams.length > 1 then throw ⟨sp, "the patterns in one position are of different types"⟩
      let sig := heads.head?.bind (familySig t)
      let complete := match sig with
        | some s => s.all fun (h, _) => heads.contains h
        | none => false
      if complete then
        let some s := sig | pure none
        for (h, k) in s do
          let P' ← P.filterMapM fun row => match row with
            | p :: ps => do pure ((← specRow t h k p).map (· ++ ps))
            | [] => pure none
          if let some w ← useful t fuel P' ((List.range k).map (fun _ => MPat.wild sp) ++ qs) then
            return some (rebuild h k w)
        pure none
      else
        -- The default matrix: the rows whose first pattern is irrefutable.
        let D := P.filterMap fun row => match row with
          | p :: ps => if p.irrefutable then some ps else none
          | [] => none
        match ← useful t fuel D qs with
        | none => pure none
        | some w =>
          -- A head no row names, or `_` when there is none to name (a literal).
          let missing := sig.bind fun s => s.find? fun (h, _) => !heads.contains h
          match missing with
          | some (h, k) => pure (some (rebuild h k ((List.range k).map (fun _ => MPat.wild sp) ++ w)))
          | none => pure (some (MPat.wild sp :: w))
where
  rebuild (h : Head) (k : Nat) (w : List MPat) : List MPat :=
    let sp := Span.none
    let (args, rest) := (w.take k, w.drop k)
    let p : MPat := match h with
      | .con d i => .con sp (((t.decl? d).bind (·.cons[i]?)).map (·.name.name) |>.getD "?") false args
      | .tuple _ => .tuple sp args
      | .lit key => .lit sp (.unit sp) key
      | .bool b => .bool sp b
      | .inj l => .inj sp l (args.head?.getD (.wild sp))
    p :: rest

/-- A pattern as messages write it. -/
def MPat.render : Nat → MPat → String
  | 0, _ => "…"
  | _ + 1, .wild _ | _ + 1, .var _ => "_"
  | n + 1, .free _ p => MPat.render n p
  | n + 1, .tuple _ ps => "(" ++ ", ".intercalate (ps.map (MPat.render n)) ++ ")"
  | n + 1, .con _ c _ ps => if ps.isEmpty then c else c ++ "(" ++ ", ".intercalate (ps.map (MPat.render n)) ++ ")"
  | _ + 1, .lit _ _ key => key
  | _ + 1, .bool _ b => if b then "true" else "false"
  | n + 1, .inj _ l p => (if l then "inl " else "inr ") ++ MPat.render n p

/-- An arm's value rebuilt from its parts, for a variable that binds what an earlier column took
apart: a constructor's (its payload's components; a block's cells, so nothing is allocated), a
tuple's, `true`, `false`, an injection, or an occurrence. -/
inductive RB where
  | occ (x : String)
  | con (i : Nat) (n : Nat) (rolls : Bool) (asc : Option String) (args : List RB)
  | tuple (args : List RB)
  | bool (b : Bool)
  | inj (left : Bool) (a : RB)
  /-- `a` at the type of the occurrence `o` (`VSugar.like`): in a `fold` block, where the parts of
  the algebra's parameter are not the declarations' values. -/
  | like (o : String) (a : RB)
  deriving Inhabited

/-- `r` with the occurrence `x` replaced by `s`. -/
def RB.subst (x : String) (s : RB) : Nat → RB → RB
  | 0, r => r
  | _ + 1, .occ y => if y == x then s else .occ y
  | k + 1, .con i n r asc as => .con i n r asc (as.map (RB.subst x s k))
  | k + 1, .tuple as => .tuple (as.map (RB.subst x s k))
  | _ + 1, .bool b => .bool b
  | k + 1, .inj l a => .inj l (RB.subst x s k a)
  | k + 1, .like o a => .like o (RB.subst x s k a)

/-- The value `r` denotes. -/
def RB.toVal (sp : Span) : Nat → RB → Val
  | 0, _ => .unit sp
  | _ + 1, .occ x => .var sp x
  | k + 1, .con i n r asc as =>
    let V := injV sp n i (tupleV sp (as.map (RB.toVal sp k)))
    let V := if r then .roll sp V else V
    match asc with
    | some N => .ascribe sp V (.name sp N)
    | none => V
  | k + 1, .tuple as => tupleV sp (as.map (RB.toVal sp k))
  | _ + 1, .bool b => if b then .inr sp (.unit sp) else .inl sp (.unit sp)
  | k + 1, .inj l a => if l then .inl sp (RB.toVal sp k a) else .inr sp (RB.toVal sp k a)
  | k + 1, .like o a =>
    .app sp (.sugar sp (.like o)) (RB.toVal sp k a)

/-- A row of the clause matrix: its patterns, one per column, the variables bound so far to what
they match, and its arm. -/
structure Row where
  pats : List MPat
  binds : List (Ident × RB)
  arm : Nat
  deriving Inhabited

abbrev CM := StateT Nat (Except Error)

def freshOcc : CM String := modifyGet fun k => (s!"io_m{k}", k + 1)

/-- Every row's bindings with the occurrence `x` replaced by `r`: `x` was taken apart. -/
def substRows (x : String) (r : RB) (rows : List Row) : List Row :=
  rows.map fun row => { row with binds := row.binds.map fun (y, s) => (y, RB.subst x r 64 s) }

/-- The leftmost column whose first row's pattern tests something. -/
def testCol (row : Row) : Option Nat := row.pats.findIdx? (!·.irrefutable)

/-- An arm, reached with its variables bound: each `x <- return v`, in order. -/
def bindAll (sp : Span) : List (Ident × RB) → Comp → Comp
  | [], M => M
  | (x, r) :: bs, M => .bind sp x none (.ret sp (r.toVal sp 64)) (bindAll sp bs M) false

/-- `x <- return free(c); M`: a block's cell freed, its content bound. -/
def freeBind (sp : Span) (x : Ident) (c : String) (M : Comp) : Comp :=
  .bind sp x none (.ret sp (.app sp (.sugar sp (.call "free")) (.var sp c))) M false

/-- An occurrence of the generated code, and whether it is a block's cell. -/
abbrev Occ := String × Bool

/-- A `fold` block's arms, compiled as the algebra's (SPEC §60, F1): the fold `kind`, the
algebra's parameter `top`, an occurrence of the unrolled shape, and the root of the group folded.
Below a block of the group, a recursive field is the fold's result, not a cell. -/
structure FoldCx where
  kind : FoldKind
  top : String
  root : String

/-- The field `j` of the constructor `ci` of `i` is a recursive position of a block: the root of
the group, which a block's field may name only as itself (SPEC §42, *Recursion*). -/
def Info.recField (i : Info) (ci j : Nat) : Bool :=
  (((i.cons[ci]?).bind (·.fields[j]?)).map (·.ty.bare [i.root])).getD false

/-- The refusal of a pattern below a block's cell: in `fold_imm` the cell is read through its view. -/
def cellPatErr (fold? : Option FoldCx) : String :=
  if (fold?.map (·.kind)) == some .imm then
    "in `fold_imm` a block's field is the view of its cell, `imm 'y A`: bind it with a name, and " ++
      "read it with `*`"
  else "a pattern under a block's cell needs `box`: the block is freed and its fields' values matched"

/-- The decision tree of the clause matrix `rows` over the occurrences `cols` (Maranget 2008);
`arms` are the arms' bodies, and `info? d` what is known of the declaration `d`. In a `fold` block
(`fold?`) the root's constructor is tested on the algebra's parameter, which is unrolled already,
and nowhere else. -/
def compile (t : Table) (sp : Span) (arms : Array Comp) (info? : String → Option Info)
    (fold? : Option FoldCx := none) :
    Nat → List Row → List Occ → CM Comp
  | 0, _, _ => throw ⟨sp, "internal error: a match nested too deeply"⟩
  | fuel + 1, rows, cols => do
    let some row := rows.head? | throw ⟨sp, "internal error: a match with no arm left"⟩
    match testCol row with
    | none =>
      -- Every pattern of the first row matches: its arm, its variables bound, a `box`
      -- pattern's cells freed.
      let mut bs := row.binds
      let mut frees : List (Ident × String) := []
      for (p, (o, _)) in row.pats.zip cols do
        match p with
        | .var x => bs := bs ++ [(x, .occ o)]
        | .free _ (.var x) => frees := frees ++ [(x, o)]
        | .free fsp (.wild _) => frees := frees ++ [(⟨s!"{o}_d", fsp⟩, o)]
        | _ => pure ()
      let M := bindAll sp bs ((arms[row.arm]?).getD (.top sp))
      pure (frees.foldr (fun (x, o) M => freeBind sp x o M) M)
    | some j =>
      -- Column `j` first.
      let swap {α} [Inhabited α] (xs : List α) : List α :=
        match xs[j]? with
        | some a => a :: (xs.take j ++ xs.drop (j + 1))
        | none => xs
      let rows := rows.map fun r => { r with pats := swap r.pats }
      let cols := swap cols
      let (o, cell) := cols.head!
      let rest := cols.tail
      let p := rows.head!.pats.head!
      -- A cell's content tested (`box`): the cell freed first.
      if let .free fsp _ := p then
        let o' ← freshOcc
        let mut rows' : List Row := []
        for r in rows do
          match r.pats with
          | .free _ q :: ps => rows' := rows' ++ [{ r with pats := q :: ps }]
          | .wild s :: ps => rows' := rows' ++ [{ r with pats := .wild s :: ps }]
          | .var x :: _ =>
            throw ⟨x.span, s!"`{x.name}` binds a block's cell, which an arm before it frees " ++
              "(`box`): match it with `box` here too"⟩
          | q :: _ => throw ⟨q.span, cellPatErr fold?⟩
          | [] => pure ()
        let M ← compile t sp arms info? fold? fuel rows' ((o', false) :: rest)
        return freeBind fsp ⟨o', fsp⟩ o M
      if cell then throw ⟨p.span, cellPatErr fold?⟩
      let some (h, _) ← (p.head t : Except Error _) | throw ⟨sp, "internal error: a test"⟩
      match h with
      | .lit _ =>
        -- Literals, tested by `==` in the order they first appear, the default last.
        let mut seen : List String := []
        let mut tests : List (Val × List Row) := []
        for r in rows do
          let some q := r.pats.head? | continue
          let .lit _ V key := q | continue
          if seen.contains key then continue
          seen := seen ++ [key]
          let rs := rows.filterMap fun r' => match r'.pats with
            | .lit _ _ k' :: qs => if k' == key then some { r' with pats := qs } else none
            | .var x :: qs => some { r' with pats := qs, binds := r'.binds ++ [(x, .occ o)] }
            | .wild _ :: qs => some { r' with pats := qs }
            | _ => none
          tests := tests ++ [(V, rs)]
        let dflt := rows.filterMap fun r => match r.pats with
          | .var x :: qs => some { r with pats := qs, binds := r.binds ++ [(x, .occ o)] }
          | .wild _ :: qs => some { r with pats := qs }
          | _ => none
        let mut M ← compile t sp arms info? fold? fuel dflt rest
        for (V, rs) in tests.reverse do
          let S ← compile t sp arms info? fold? fuel rs rest
          let test : Val := .app sp (.sugar sp (.op .eq)) (.pair sp (.var sp o) V)
          M := .case sp test ⟨"io_else", sp⟩ M ⟨"io_then", sp⟩ S
        pure M
      | _ =>
        let some sig := familySig t h | throw ⟨sp, "internal error: a family"⟩
        -- The rows specialised to the head `h` of arity `k`, its parts at `subs`; a variable
        -- that binds the whole is bound to it rebuilt (`rb`).
        let branch (h : Head) (k : Nat) (subs : List Occ) (rb : RB) : CM Comp := do
          let rs ← rows.filterMapM fun r => do
            match r.pats with
            | q :: qs => match ← (q.head t : Except Error _) with
              | some (h', qs') => pure (if h' == h then some { r with pats := qs' ++ qs } else none)
              | none => pure (some { r with
                  pats := (List.range k).map (fun _ => MPat.wild sp) ++ qs,
                  binds := r.binds ++ (match q with
                    | .var x => [(x, RB.occ o)]
                    | _ => []) })
            | [] => pure none
          compile t sp arms info? fold? fuel (substRows o rb rs) (subs ++ rest)
        let fresh (n : Nat) (c : Bool) : CM (List Occ) :=
          (List.range n).mapM fun _ => do pure ((← freshOcc), c)
        match h with
        | .lit _ => throw ⟨sp, "internal error: a literal"⟩
        | .tuple k =>
          let subs ← fresh k false
          let M ← branch (.tuple k) k subs (.tuple (subs.map (.occ ·.1)))
          pure (letTuple sp (.var sp o) (subs.map (·.1)) M (· ++ "r"))
        | .bool _ =>
          let pf ← freshOcc
          let pt ← freshOcc
          let F ← branch (.bool false) 0 [] (.bool false)
          let T ← branch (.bool true) 0 [] (.bool true)
          pure (.case sp (.var sp o) ⟨pf, sp⟩ (.letUnit sp (.var sp pf) F) ⟨pt, sp⟩
            (.letUnit sp (.var sp pt) T))
        | .inj _ =>
          let pl ← freshOcc
          let pr ← freshOcc
          let like (r : RB) : RB := if fold?.isSome then .like o r else r
          let L ← branch (.inj true) 1 [(pl, false)] (like (.inj true (.occ pl)))
          let R ← branch (.inj false) 1 [(pr, false)] (like (.inj false (.occ pr)))
          pure (.case sp (.var sp o) ⟨pl, sp⟩ L ⟨pr, sp⟩ R)
        | .con d _ =>
          let some i := info? d | throw ⟨sp, s!"internal error: the declaration `{d}`"⟩
          -- In a `fold` block the parameter is the root unrolled, with the recursive positions
          -- folded: no other value of the root is in it, and its parts are not the declarations'
          -- values, so a variable that binds one is not ascribed.
          let inFold := fold?.isSome && i.group.contains ((fold?.map (·.root)).getD "")
          if let some fc := fold? then
            if i.rolls && d == fc.root && o != fc.top then
              throw ⟨p.span, s!"in a `{fc.kind.str}` block a recursive field is the fold's result on " ++
                s!"it, and matching the fold's result with a constructor of `{d}` is not provided: " ++
                "bind it with a name"⟩
          let rolls := i.rolls && !inFold
          let asc := if i.mono && !inFold then some d else none
          let scrut : Val := if rolls then .unroll sp (.var sp o) else .var sp o
          -- One arm per constructor, along the ⊕ spine; a block's parts are its cells, and in a
          -- `fold` block its recursive fields are the fold's results.
          let mut arms' : List (String × Comp) := []
          for (h', k) in sig do
            let .con _ ci := h' | continue
            let block := ((i.cons[ci]?).map (·.block)).getD false
            let cellAt (j : Nat) : Bool := block && !(inFold && i.recField ci j)
            -- The one constructor's payload of a declaration that is no `μ` is the scrutinee.
            let pv ← if sig.length == 1 && !i.rolls then pure o else freshOcc
            -- A payload of one field is the field itself.
            let subs ← if k == 1 then pure [(pv, cellAt 0)] else
              (List.range k).mapM fun j => do pure ((← freshOcc), cellAt j)
            let rb := RB.con ci i.n rolls asc (subs.map (.occ ·.1))
            -- In a `fold` block the rebuilt value is at the type of `o`, which only the typed pass
            -- knows.
            let rb := if fold?.isSome then RB.like o rb else rb
            let M ← branch h' k subs rb
            arms' := arms' ++ [(pv, if k == 1 then M else
              letTuple sp (.var sp pv) (subs.map (·.1)) M (· ++ "r"))]
          spine sp scrut arms'
where
  /-- `case` along the ⊕ spine of the payloads' arms, the scrutinee `V`. -/
  spine (sp : Span) (V : Val) : List (String × Comp) → CM Comp
    | [] => pure (.absurd sp V)
    | [(p, M)] => pure (match V with
      | .var _ x => if x == p then M else .bind sp ⟨p, sp⟩ none (.ret sp V) M false
      | V => .bind sp ⟨p, sp⟩ none (.ret sp V) M false)
    | [(p, M), (q, N)] => pure (.case sp V ⟨p, sp⟩ M ⟨q, sp⟩ N)
    | (p, M) :: arms => do
      let r ← freshOcc
      let N ← spine sp (.var sp r) arms
      pure (.case sp V ⟨p, sp⟩ M ⟨r, sp⟩ N)

/-- `match V { p₁ -> M₁ | … }` (M1), or over the columns `Vs` (M2): the arms checked
exhaustive and each reachable (M4), then compiled. `fresh` is the next number of a generated
name; the compiled computation, and the next number.  `[spec §42]` -/
def matchComp (t : Table) (sp : Span) (scruts : List Val) (arms : List (List MPat × Comp))
    (fresh : Nat) : Except Error (Comp × Nat) := do
  let fuel := 4096
  -- Reports first.
  let rows := arms.map (·.1)
  for (r, i) in rows.zipIdx do
    if (← useful t fuel (rows.take i) r).isNone then
      let rsp := (r.head?.map MPat.span).getD sp
      throw ⟨rsp, "this arm is never reached: the arms before it match everything it matches"⟩
  let wilds := scruts.map fun _ => MPat.wild sp
  if let some w ← useful t fuel rows wilds then
    let shown := match w with
      | [p] => p.render 16
      | ps => "(" ++ ", ".intercalate (ps.map (MPat.render 16)) ++ ")"
    throw ⟨sp, s!"this `match` is not exhaustive: `{shown}` is not matched"⟩
  let infoOf (d : String) : Option Info := (info t d).toOption
  -- Each scrutinee bound once to an occurrence.
  let go : CM Comp := do
    let mut cols : List Occ := []
    let mut pre : List (String × Val) := []
    for V in scruts do
      match V with
      | .var _ x => cols := cols ++ [(x, false)]
      | V =>
        let o ← freshOcc
        cols := cols ++ [(o, false)]
        pre := pre ++ [(o, V)]
    let rs : List Row := arms.zipIdx.map fun ((ps, _), i) => { pats := ps, binds := [], arm := i }
    let M ← compile t sp (arms.map (·.2)).toArray infoOf none fuel rs cols
    pure (pre.foldr (fun (o, V) M => .bind sp ⟨o, sp⟩ none (.ret sp V) M false) M)
  go.run fresh

/-! ### The `fold` block: F1 -/

/-- In a `fold` block over the group whose root is `root`, `box C(p, …)` of a block of the group
frees its cells and matches their values: the recursive fields are the fold's results, not cells,
and are matched as they are. `fold_imm` reads the block through views, and frees nothing. -/
def foldBox (t : Table) (k : FoldKind) (root : String) : Nat → MPat → Except Error MPat
  | 0, p => throw ⟨p.span, "internal error: a pattern nested too deeply"⟩
  | n + 1, p => match p with
    | .tuple sp ps => do pure (.tuple sp (← ps.mapM (foldBox t k root n)))
    | .inj sp l q => do pure (.inj sp l (← foldBox t k root n q))
    | .free sp q => do pure (.free sp (← foldBox t k root n q))
    | .con sp c b ps => do
      let ps ← ps.mapM (foldBox t k root n)
      if !b then return .con sp c b ps
      let some (d, ci) := t.con? c | throw ⟨sp, s!"no constructor `{c}` is declared"⟩
      let some i := (info t d.name.name).toOption | return .con sp c b ps
      unless i.group.contains root && ((i.cons[ci]?).map (·.block)).getD false do
        return .con sp c b ps
      if k == .imm then
        throw ⟨sp, s!"`fold_imm` reads `{c}` through the views of its cells, and frees nothing: " ++
          s!"match it without `box`"⟩
      unless ps.length == ((i.cons[ci]?).map (·.fields.length)).getD 0 do return .con sp c b ps
      pure (.con sp c false (ps.zipIdx.map fun (q, j) => if i.recField ci j then q else .free q.span q))
    | p => pure p

/-- A `fold` block's arms (SPEC §60, F1), compiled over the algebra's parameter `top`: the arms
checked exhaustive and each reachable (M4), then compiled as a `match` on the unrolled shape
whose recursive positions hold the fold's results (`FoldCx`). The group folded is the one whose
root the arms' constructors name, and that root must be what is folded: the single-root rule
makes it the one member that is a `μ`. With the compiled arms, the root's name and type
parameters, when the arms name it.  `[spec §60]` -/
def foldComp (t : Table) (sp : Span) (k : FoldKind) (top : String) (arms : List (MPat × Comp))
    (fresh : Nat) : Except Error ((Comp × Nat) × Option (String × List String)) := do
  let fuel := 4096
  let decl? := arms.findSome? fun (p, _) => match p with
    | .con csp c _ _ => some (csp, c)
    | _ => none
  let mut root : Option String := none
  if let some (csp, c) := decl? then
    let some (d, _) := t.con? c | throw ⟨csp, s!"no constructor `{c}` is declared"⟩
    let i ← match info t d.name.name with
      | .ok i => pure i
      | .error m => throw ⟨csp, m⟩
    unless i.rolls do
      if i.group.length > 1 || (reachFrom t i.root).contains i.root then
        throw ⟨csp, s!"`{k.str}` folds the root of a recursive group, and `{d.name.name}` is not its " ++
          s!"group's root `{i.root}` (the single-root rule): fold `{i.root}`"⟩
      throw ⟨csp, s!"`{d.name.name}` is not recursive, so it has no fold: match it"⟩
    root := some i.root
  let rootDecl := root.bind fun r => (t.decl? r).map fun e => (r, e.tps.map (·.name))
  let arms ← match root with
    | some r => arms.mapM fun (p, M) => do pure (← foldBox t k r 4096 p, M)
    | none => pure arms
  let rows := arms.map fun (p, _) => [p]
  for (r, i) in rows.zipIdx do
    if (← useful t fuel (rows.take i) r).isNone then
      let rsp := (r.head?.map MPat.span).getD sp
      throw ⟨rsp, "this arm is never reached: the arms before it match everything it matches"⟩
  if let some w ← useful t fuel rows [MPat.wild sp] then
    let shown := match w with
      | [p] => p.render 16
      | ps => "(" ++ ", ".intercalate (ps.map (MPat.render 16)) ++ ")"
    throw ⟨sp, s!"this `{k.str}` block is not exhaustive: `{shown}` is not matched"⟩
  let infoOf (d : String) : Option Info := (info t d).toOption
  let fc : Option FoldCx := root.map fun r => { kind := k, top, root := r }
  let rs : List Row := arms.zipIdx.map fun ((p, _), i) => { pats := [p], binds := [], arm := i }
  pure ((← (compile t sp (arms.map (·.2)).toArray infoOf fc fuel rs [(top, false)]).run fresh),
    rootDecl)

end Frontend.Data
