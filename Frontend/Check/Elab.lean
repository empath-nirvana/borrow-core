import Frontend.Lexer
import Core.BlockBorrow
import Frontend.Check.Fam

/-!
# Frontend — Check — elaborating types

Surface lifetimes, types and shapes (syntax-core §3–§5) to `Core`'s `Lifetime.Life`, `VTy`,
`CTy` and `Shape`, with a printer back to the surface syntax for messages.

* **Lifetime names** resolve lexically, innermost first. A binder (`forall 'x`, `all 'x`, and
  the `Fun`/constant binders of the checker) is numbered `Δ'.freshVar`, where `Δ'` is the
  lifetime context of the term at that point extended by the enclosing binders of the type
  being written (§3). `dom` is `Δ.meetOfDom` of the term's `Δ`.
* **`μ` variables** are de Bruijn indices. Entering a computation type (`U C`, `=>`, `all`)
  hides them: a type variable under `U` is rejected (§4). `mu X. A` must be closed and `X` must
  not occur under `mut` (`Cl`, `NoMut`, §4).
* **`type`/`shape` abbreviations** are elaborated at each use, as their own closed types, at the
  use's `Δ'` (so their binders are numbered where they are used) and in the declarations before
  them. A `def`'s type parameters are bound to already elaborated types.
* The built-in abbreviations expand to their Lean definitions: `A => B` is `VTy.lolli`,
  `all` is `VTy.all`, `block`/`val`/`fam` are `Shape.refTy`/`valTy`/`famTy`, `view` is
  `VTy.immReborrow`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check

abbrev CVTy := BoCa.Fig16.LogRel.Core.VTy
abbrev CCTy := BoCa.Fig16.LogRel.Core.CTy
abbrev CShape := BoCa.Fig16.LogRel.Core.Shape
abbrev CLife := BoCa.Lifetime.Life
abbrev CQual := BoCa.Fig16.LogRel.Core.Qual
abbrev CCount := BoCa.Fig16.LogRel.Core.Count
abbrev COpSig := BoCa.Fig16.LogRel.Core.OpSig
/-- A row of the kernel, `List OpSig`.  `[spec §19]` -/
abbrev CRow := BoCa.Fig16.LogRel.Core.Row

/-- `F_Σ A`: the row's operations over `F A`.  `[spec §19]` -/
abbrev effOf : CRow → CVTy → CCTy := BoCa.Fig16.LogRel.Core.CTy.effOf

/-- A count as a row writes it: `lin` at `1`, `aff` at `0` and `1?`. -/
def cntStr : CCount → String
  | .one => "lin"
  | .zero | .opt => "aff"

/-- `pull A B R = νX. F((A ⊗ U X) ⊕ (B ⊕ U X)) & F R`: a stored generator (SPEC §15). It is an
abbreviation of the frontend over `ν` (SPEC §7: a new codata shape is a new abbreviation), with no
counterpart in `Core/`. -/
def pullTy (A B R : CVTy) : CCTy :=
  .nu (.amp (.ret (.sum (.tensor (A.rename Nat.succ) (.tvar 0)) (.sum (B.rename Nat.succ) (.tvar 0))))
    (.ret (R.rename Nat.succ)))

/-- **The counts the checker gives a program's rows** (SPEC §53): the counts it inferred, by
operation `n.i` (`Frontend/Check/Grades.lean`); and, with `relax`, a `lin` entry read as `ctl`,
for the check that finds which handler forces a `linear ctl` operation above `1`. -/
structure CntTable where
  ops : List ((Nat × Nat) × CCount) := []
  relax : Bool := false
  deriving Inhabited

/-- The declarations visible at a point: those before index `upto`. -/
structure Scope where
  decls : Array Decl
  upto : Nat
  /-- The key of each `def` the elaboration generates (`DefKey`), read at its uses. -/
  keys : List DefKey := []
  /-- The counts the checker gives the rows (`CntTable`).  `[spec §53]` -/
  cnts : CntTable := {}

/-- **The kernel's count of the operation `n.i`, answering `B`, as a row writes it**
(SPEC §53): `lin` is `1`; `aff` is `1?`, or `0` at an answer `0`; `ctl` is the count inferred for
the operation (`Scope.cnts`), and where none is, as `aff`.  An operation whose count is inferred is
a handler site's (`SiteRec`), whose name only the elaboration writes: an `aff` entry of it is the
elaboration's own, a row it reads back from a type it computed before the count was inferred
(`TCx.surface`), and it reads the inferred count too. -/
def Scope.cntOf (sc : Scope) (n i : Nat) (q : Frontend.Qual) (B : CVTy) : CCount :=
  let weak : CCount := if B.isZero then .zero else .opt
  match q with
  | .lin => if sc.cnts.relax then (sc.cnts.ops.lookup (n, i)).getD weak else .one
  | .aff | .infer => (sc.cnts.ops.lookup (n, i)).getD weak

/-- A `type` declaration in scope: its type and lifetime parameters, body and own scope. -/
structure TypeInfo where
  tps : List Ident
  lps : List Ident
  body : VTy
  scope : Scope

/-- The latest `type` declaration named `n` in scope. -/
def Scope.findType (s : Scope) (n : String) : Option TypeInfo :=
  go s.upto
where
  go : Nat → Option TypeInfo
    | 0 => none
    | k + 1 => match s.decls[k]? with
      | some (.type _ m ps ls A) => if m.name == n then some ⟨ps, ls, A, { s with upto := k }⟩ else go k
      | _ => go k

/-- The latest `shape` declaration named `n` in scope, with its own scope. -/
def Scope.findShape (s : Scope) (n : String) : Option (Shape × Scope) :=
  go s.upto
where
  go : Nat → Option (Shape × Scope)
    | 0 => none
    | k + 1 => match s.decls[k]? with
      | some (.shape _ m σ) => if m.name == n then some (σ, { s with upto := k }) else go k
      | _ => go k

/-- A `def` in scope: its parameters, type, body and own scope. -/
structure DefInfo where
  params : List Ident
  ty : VTy
  body : Val
  scope : Scope

/-- The latest `def` named `n` in scope. -/
def Scope.findDef (s : Scope) (n : String) : Option DefInfo :=
  go s.upto
where
  go : Nat → Option DefInfo
    | 0 => none
    | k + 1 => match s.decls[k]? with
      | some (.def_ _ m ps A V _) => if m.name == n then some ⟨ps, A, V, { s with upto := k }⟩ else go k
      | _ => go k

/-- An `extern` named `n` is in scope. -/
def Scope.hasExtern (s : Scope) (n : String) : Bool :=
  (List.range s.upto).any fun k => match s.decls[k]? with
    | some (.extern _ m _) => m.name == n
    | _ => false

def err {α} (sp : Span) (msg : String) : Except Error α := throw ⟨sp, msg⟩

/-! ### Printing -/

def parenIf (b : Bool) (s : String) : String := if b then s!"({s})" else s

def ppLVar (x : LifeVar) : String := s!"'l{x}"

/-- A lifetime variable, by its source name if `nm` has one for it. -/
def ppLVarN (nm : List (String × LifeVar)) (x : LifeVar) : String :=
  match nm.find? (·.2 == x) with
  | some (n, _) => s!"'{n}"
  | none => ppLVar x

/-- A lifetime; `p > 0` parenthesizes a `/\\` or `\\/`. -/
def ppLifeP (nm : List (String × LifeVar)) (p : Nat) : CLife → String
  | .var x => ppLVarN nm x
  | .top => "top"
  | .meet a b => parenIf (p > 0) s!"{ppLifeP nm 1 a} /\\ {ppLifeP nm 0 b}"
  | .join a b => parenIf (p > 0) s!"{ppLifeP nm 1 a} \\/ {ppLifeP nm 0 b}"

def tvName (d : Nat) : String := if d == 0 then "X" else s!"X{d}"

mutual
/-- A value type in the surface syntax, at precedence `p` (syntax-core §4: `0` binders, `1`
`-o`/`=>`, `2` `&`, `3` `+`, `4` `*`, `5` prefix); `d` is the number of enclosing `μ`s, and
`nm` names lifetime variables. -/
def ppV (nm : List (String × LifeVar)) (d p : Nat) : CVTy → String
  | .unit => "1"
  | .zero => "0"
  | .tensor A B => parenIf (p > 4) s!"{ppV nm d 5 A} * {ppV nm d 4 B}"
  | .sum A B => parenIf (p > 3) s!"{ppV nm d 4 A} + {ppV nm d 3 B}"
  | .thunk (.arr A (.ret B)) => parenIf (p > 1) s!"{ppV nm d 2 A} => {ppV nm d 1 B}"
  | .thunk (.all x b (.ret A)) =>
      parenIf (p > 0) s!"all {ppLVar x} < {ppLifeP nm 1 b}. {ppV (nm.filter (·.2 != x)) d 0 A}"
  | .thunk C => parenIf (p > 5) s!"U {ppC nm 6 C}"
  | .ref A => parenIf (p > 5) s!"ref {ppV nm d 5 A}"
  | .imm a A => parenIf (p > 5) s!"imm {ppLifeP nm 1 a} {ppV nm d 5 A}"
  | .mut a A => parenIf (p > 5) s!"mut {ppLifeP nm 1 a} {ppV nm d 5 A}"
  | .box a A => parenIf (p > 5) s!"box {ppLifeP nm 1 a} {ppV nm d 5 A}"
  | .bang A => parenIf (p > 5) s!"!{ppV nm d 5 A}"
  | .unk => "unk"
  | .int .w32 => "i32"
  | .int .w64 => "i64"
  | .int .w8 => "u8"
  | .int .f32 => "f32"
  | .int .f64 => "f64"
  | .opq .input => "input"
  | .opq .output => "output"
  | .opq .clock => "clock"
  | .opq .args => "args"
  -- The variable of the `nu` around (`ppC`), which occurs only as `U X`.
  | .tvar n => if n < d then tvName (d - 1 - n) else if n == d then "U X" else s!"?{n}"
  | .mu A => parenIf (p > 0) s!"mu {tvName d}. {ppV nm (d + 1) 0 A}"
  | .fam (.ref A) => parenIf (p > 5) s!"array {ppV nm d 5 A}"
  | .fam (.imm a A) => parenIf (p > 5) s!"array_imm {ppLifeP nm 1 a} {ppV nm d 5 A}"
  | .fam (.mut a A) => parenIf (p > 5) s!"array_mut {ppLifeP nm 1 a} {ppV nm d 5 A}"
  | .fam L => parenIf (p > 5) s!"[{ppV nm d 0 L}]"
/-- A computation type in the surface syntax, at precedence `p`. -/
def ppC (nm : List (String × LifeVar)) (p : Nat) : CCTy → String
  | .ret A => parenIf (p > 5) s!"F {ppV nm 0 5 A}"
  | .arr A C => parenIf (p > 1) s!"{ppV nm 0 2 A} -o {ppC nm 1 C}"
  | .amp C D => parenIf (p > 2) s!"{ppC nm 3 C} & {ppC nm 2 D}"
  | .top => "top"
  | .all x b C =>
      parenIf (p > 0) s!"forall {ppLVar x} < {ppLifeP nm 1 b}. {ppC (nm.filter (·.2 != x)) 0 C}"
  | .nu (.amp (.ret (.sum A (.tvar 0))) (.ret .unit)) =>
      parenIf (p > 5) s!"delay {ppV nm 0 5 A}"
  | .nu (.amp (.ret (.tensor A (.tvar 0))) (.ret .unit)) =>
      parenIf (p > 5) s!"stream {ppV nm 0 5 A}"
  | .nu (.amp (.ret (.sum A (.tvar 0))) (.ret B)) =>
      parenIf (p > 5) s!"loop {ppV nm 0 6 A} {ppV nm 0 6 B}"
  | .nu (.amp (.ret (.sum (.tensor A (.tvar 0)) (.sum B (.tvar 0)))) (.ret R)) =>
      parenIf (p > 5) s!"pull {ppV nm 0 6 A} {ppV nm 0 6 B} {ppV nm 0 6 R}"
  | .nu (.amp (.ret (.sum (.tensor A (.tvar 0)) R)) (.ret R')) =>
      parenIf (p > 5) s!"iter {ppV nm 0 6 A} {ppV nm 0 6 R} {ppV nm 0 6 R'}"
  | .nu C => parenIf (p > 0) s!"nu {tvName 0}. {ppC nm 0 C}"
  | .eff n i q _ A B fin C =>
      let (es, r) := ppEff nm C
      parenIf (p > 5)
        s!"F[{", ".intercalate (s!"{n}.{i} {cntStr q} {ppV nm 0 0 A} ~> {ppV nm 0 0 B}" :: es)}] {r}"
/-- The entries of a row's layers `F_Σ`, and what is under them. -/
def ppEff (nm : List (String × LifeVar)) : CCTy → List String × String
  | .eff n i q _ A B fin C =>
      let (es, r) := ppEff nm C
      (s!"{n}.{i} {cntStr q} {ppV nm 0 0 A} ~> {ppV nm 0 0 B}" :: es, r)
  | .ret A => ([], ppV nm 0 6 A)
  | C => ([], ppC nm 6 C)
end

def ppLife (a : CLife) : String := ppLifeP [] 1 a
def ppVTy (A : CVTy) : String := ppV [] 0 0 A
def ppCTy (C : CCTy) : String := ppC [] 0 C

/-! ### Elaboration -/

/-- The context of a type being elaborated. -/
structure TyEnv where
  scope : Scope
  /-- The term's lifetime context: `dom` is its `meetOfDom`. -/
  Δ : LifeCtx
  /-- The numbering context: `Δ` extended by the enclosing binders of the type. -/
  Δn : LifeCtx
  lenv : List (String × LifeVar)
  /-- Visible `μ` variables, innermost first. -/
  mu : List String
  /-- `μ` variables hid by an enclosing `U`. -/
  hid : List String
  /-- A `def`'s type parameters, or a parameterised `type`'s. -/
  tps : List (String × CVTy)
  /-- A parameterised `type`'s lifetime parameters, bound to the use's lifetimes.  `[spec §7]` -/
  lsub : List (String × CLife) := []

/-- An abbreviation's body: its own scope, no names of the use site, the use's `Δ`. -/
def TyEnv.closedAt (E : TyEnv) (sc : Scope) : TyEnv :=
  { E with scope := sc, lenv := [], mu := [], hid := [], tps := [], lsub := [] }

def TyEnv.enterU (E : TyEnv) : TyEnv := { E with mu := [], hid := E.mu ++ E.hid }

/-- A lifetime, a name bound by `lenv` first and then by `lsub` (a parameterised `type`'s lifetime
parameters). -/
def elabLifeS (Δ : LifeCtx) (lenv : List (String × LifeVar)) (lsub : List (String × CLife)) :
    Frontend.Life → Except Error CLife
  | .var sp x => match lenv.lookup x with
    | some v => pure (.var v)
    | none => match lsub.lookup x with
      | some a => pure a
      | none => err sp s!"unbound lifetime variable '{x}"
  | .top _ => pure .top
  | .dom _ => pure Δ.meetOfDom
  | .meet _ a b => do pure (.meet (← elabLifeS Δ lenv lsub a) (← elabLifeS Δ lenv lsub b))
  | .join _ a b => do pure (.join (← elabLifeS Δ lenv lsub a) (← elabLifeS Δ lenv lsub b))

/-- A lifetime. -/
def elabLife (Δ : LifeCtx) (lenv : List (String × LifeVar)) : Frontend.Life → Except Error CLife :=
  elabLifeS Δ lenv []

/-- A lifetime of a type being elaborated. -/
def TyEnv.life (E : TyEnv) : Frontend.Life → Except Error CLife := elabLifeS E.Δ E.lenv E.lsub

/-- The head name of a curried application `N[A, …]<'a, …>`, its type arguments and its lifetime
arguments, in order. -/
def _root_.Frontend.VTy.spine : VTy → Option (String × List VTy × List Frontend.Life)
  | .name _ n => some (n, [], [])
  | .app _ G A => (G.spine).bind fun (n, As, ls) => if ls.isEmpty then some (n, As ++ [A], ls) else none
  | .lapp _ G a => (G.spine).map fun (n, As, ls) => (n, As, ls ++ [a])
  | _ => none

def indexOf? (x : String) : List String → Option Nat
  | [] => none
  | y :: ys => if x == y then some 0 else (indexOf? x ys).map (· + 1)

mutual
/-- A value type. `fuel` bounds the nesting of abbreviations. -/
def elabV : Nat → TyEnv → VTy → Except Error CVTy
  | 0, _, A => err A.span "type abbreviations nested too deeply"
  | n + 1, E, A => match A with
    | .unit _ => pure .unit
    | .zero _ => pure .zero
    | .tensor _ A B => do pure (.tensor (← elabV n E A) (← elabV n E B))
    | .sum _ A B => do pure (.sum (← elabV n E A) (← elabV n E B))
    | .thunk _ (.name sp X) =>
        match indexOf? ("U " ++ X) E.mu with
        | some i => pure (.tvar i)
        | none =>
          if E.hid.contains ("U " ++ X) then
            err sp s!"the `nu` variable `{X}` occurs under an inner `U`"
          else err sp s!"`U {X}`: `{X}` is not a `nu` variable in scope"
    | .thunk _ C => do pure (.thunk (← elabC n E.enterU C))
    | .ref _ A => do pure (.ref (← elabV n E A))
    | .imm _ a A => do pure (.imm (← E.life a) (← elabV n E A))
    | .mut _ a A => do pure (.mut (← E.life a) (← elabV n E A))
    | .box _ a A => do pure (.box (← E.life a) (← elabV n E A))
    | .bang _ A => do pure (.bang (← elabV n E A))
    | .unk _ => pure .unk
    | .int _ w => pure (.int w)
    | .handle _ k => pure (.opq (match k with
        | .input => .input
        | .output => .output
        | .clock => .clock
        | .args => .args))
    | .mu sp X A => do
        let B ← elabV n { E with mu := X.name :: E.mu } A
        -- A template's type, elaborated with its type parameters as placeholders to match a call
        -- against (`Frontend/Sugar.lean`), is checked at each instance instead.
        let pattern := E.tps.any fun (_, T) => match T with | .tvar i => i ≥ 2 ^ 24 | _ => false
        if VTy.clB 1 B = false && !pattern then
          err sp s!"`mu {X.name}. …` must be closed: it mentions an enclosing type variable"
        else if VTy.noMutB 0 B = false then
          err sp s!"in `mu {X.name}. …`, `{X.name}` occurs under `mut`"
        else pure (.mu B)
    | .name sp x =>
        match indexOf? x E.mu with
        | some i => pure (.tvar i)
        | none =>
          if E.hid.contains x then
            err sp s!"the type variable `{x}` occurs under `U` (inside a computation type)"
          else match E.tps.lookup x with
            -- Under the enclosing `μ`/`ν` binders: a template's placeholder is shifted past them,
            -- as `matchV` reads it; a closed type is unchanged.
            | some B => pure (B.rename (· + (E.mu.length + E.hid.length)))
            | none => match E.scope.findType x with
              | some ⟨[], [], B, sc⟩ => elabV n (E.closedAt sc) B
              | some ti => err sp (s!"`{x}` takes {ti.tps.length} type and {ti.lps.length} " ++
                  s!"lifetime arguments, written `{x}[…]<…>`")
              | none => err sp s!"unknown type `{x}`"
    | .lolli _ A B => do
        let E' := E.enterU
        pure (.thunk (.arr (← elabV n E' A) (.ret (← elabV n E' B))))
    | .all _ x b A => do
        let bl ← E.life b
        let v := E.Δn.freshVar
        let E' := { E.enterU with Δn := E.Δn.extend v bl, lenv := (x.name, v) :: E.lenv }
        pure (.thunk (.all v bl (.ret (← elabV n E' A))))
    | .block _ σ => do pure (← elabS n E σ).refTy
    | .val _ σ => do pure (← elabS n E σ).valTy
    | .fam _ m a σ => do
        let al ← E.life a
        let s ← elabS n E σ
        pure (match m with
          | .mut => s.famTy BoCa.Fig16.LogRel.Core.VTy.mut al
          | .imm => s.famTy BoCa.Fig16.LogRel.Core.VTy.imm al)
    | .view _ a A => do pure ((← elabV n E A).immReborrow (← E.life a))
    | .array _ A => do pure (.fam (.ref (← elabV n E A)))
    | .arrayImm _ a A => do pure (.fam (.imm (← E.life a) (← elabV n E A)))
    | .arrayMut _ a A => do pure (.fam (.mut (← E.life a) (← elabV n E A)))
    | .sized sp D S A => elabV n E (VTy.sizedExpand sp D S A)
    | .rowed sp _ _ =>
        err sp ("a function type with a provided row is the type of a computation parameter " ++
          "(SPEC §33): it is written on a parameter of a function")
    | A@(.app sp _ _) | A@(.lapp sp _ _) =>
        -- `N[A, …]<'a, …>`: the arguments elaborated at the use, then `N`'s body in its own scope
        -- with its parameters bound to them.  `[spec §7]`
        match A.spine with
        | none => err sp "only a parameterised `type` takes arguments `[…]<…>`"
        | some (x, As, ls) => match E.scope.findType x with
          | none => err sp s!"unknown type `{x}`"
          | some ⟨ps, lps, B, sc⟩ =>
            if ps.length != As.length || lps.length != ls.length then
              err sp (s!"`{x}` takes {ps.length} type and {lps.length} lifetime arguments, " ++
                s!"but has {As.length} and {ls.length}")
            else do
              let Bs ← As.mapM (elabV n E)
              let ms ← ls.mapM E.life
              let tps := (ps.map (·.name)).zip Bs
              let lsub := (lps.map (·.name)).zip ms
              elabV n { E.closedAt sc with tps, lsub } B
/-- A computation type. -/
def elabC : Nat → TyEnv → CTy → Except Error CCTy
  | 0, _, C => err C.span "type abbreviations nested too deeply"
  | n + 1, E, C => match C with
    | .ret _ A => do pure (.ret (← elabV n E A))
    | .arr _ A C => do pure (.arr (← elabV n E A) (← elabC n E C))
    | .amp _ C D => do pure (.amp (← elabC n E C) (← elabC n E D))
    | .top _ => pure .top
    | .all _ x b C => do
        let bl ← E.life b
        let v := E.Δn.freshVar
        let E' := { E with Δn := E.Δn.extend v bl, lenv := (x.name, v) :: E.lenv }
        pure (.all v bl (← elabC n E' C))
    | .nu sp X C => do
        let B ← elabC n { E.enterU with mu := ["U " ++ X.name] } C
        -- A template's type, elaborated with its type parameters as placeholders to match a call
        -- against, is checked at each instance instead (as `mu`'s closedness is).
        let pattern := E.tps.any fun (_, T) => match T with | .tvar i => i ≥ 2 ^ 24 | _ => false
        if CTy.nuOkB B || pattern then pure (.nu B)
        else err sp (s!"`nu {X.name}. C` needs `C` to be a `&` of observations `F A`, each " ++
          s!"possibly taking a closed argument `A -o …`, with `U {X.name}` only under `*`, `+` and `box`")
    | .name sp X => err sp s!"the `nu` variable `{X}` occurs only as `U {X}`"
    | .delay _ A => do pure (.delay (← elabV n E A))
    | .stream _ A => do pure (.stream (← elabV n E A))
    | .iter _ A R R' => do pure (.iter (← elabV n E A) (← elabV n E R) (← elabV n E R'))
    | .loop _ A B => do pure (.loop (← elabV n E A) (← elabV n E B))
    | .pull _ A B R => do pure (pullTy (← elabV n E A) (← elabV n E B) (← elabV n E R))
    | .eff sp r A => do
        let S ← elabRow n E sp r
        pure (BoCa.Fig16.LogRel.Core.CTy.effOf S (← elabV n E A))
/-- A row: each operation's name and index below `2^32`, each entry at its count
(`Scope.cntOf`).  `[spec §18, §19, §53]` -/
def elabRow : Nat → TyEnv → Span → Row → Except Error CRow
  | 0, _, sp, _ => err sp "type abbreviations nested too deeply"
  | n + 1, E, sp, r => match r with
    | .nil => pure []
    | .cons k i q A B r => do
        if k < 2 ^ 32 ∧ i < 2 ^ 32 then
          let A' ← elabV n E A
          let B' ← elabV n E B
          let o : COpSig := ⟨UInt32.ofNat k, UInt32.ofNat i, E.scope.cntOf k i q B', .top, A', B',
            .ret .unit⟩
          pure (o :: (← elabRow n E sp r))
        else err sp s!"the operation {k}.{i}: a name and an index are below 2^32"
/-- A shape. -/
def elabS : Nat → TyEnv → Shape → Except Error CShape
  | 0, _, σ => err σ.span "shape abbreviations nested too deeply"
  | n + 1, E, σ => match σ with
    | .leaf _ A => do pure (.leaf (← elabV n E A))
    | .node _ σ τ => do pure (.node (← elabS n E σ) (← elabS n E τ))
    | .name sp x => match E.scope.findShape x with
      | some (τ, sc) => elabS n (E.closedAt sc) τ
      | none => err sp s!"unknown shape `{x}`"
end

end Frontend.Check
