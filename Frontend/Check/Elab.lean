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

/-- The declarations visible at a point: those before index `upto`. -/
structure Scope where
  decls : Array Decl
  upto : Nat

/-- The latest `type` declaration named `n` in scope, with its own scope. -/
def Scope.findType (s : Scope) (n : String) : Option (VTy × Scope) :=
  go s.upto
where
  go : Nat → Option (VTy × Scope)
    | 0 => none
    | k + 1 => match s.decls[k]? with
      | some (.type _ m A) => if m.name == n then some (A, ⟨s.decls, k⟩) else go k
      | _ => go k

/-- The latest `shape` declaration named `n` in scope, with its own scope. -/
def Scope.findShape (s : Scope) (n : String) : Option (Shape × Scope) :=
  go s.upto
where
  go : Nat → Option (Shape × Scope)
    | 0 => none
    | k + 1 => match s.decls[k]? with
      | some (.shape _ m σ) => if m.name == n then some (σ, ⟨s.decls, k⟩) else go k
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
      | some (.def_ _ m ps A V) => if m.name == n then some ⟨ps, A, V, ⟨s.decls, k⟩⟩ else go k
      | _ => go k

def err {α} (sp : Span) (msg : String) : Except Error α := throw ⟨sp, msg⟩

/-! ### Printing -/

def ppLVar (x : LifeVar) : String := s!"'l{x}"

/-- A lifetime; `p > 0` parenthesizes a `/\\` or `\\/`. -/
def ppLifeP (p : Nat) : CLife → String
  | .var x => ppLVar x
  | .top => "top"
  | .meet a b => paren (p > 0) s!"{ppLifeP 1 a} /\\ {ppLifeP 0 b}"
  | .join a b => paren (p > 0) s!"{ppLifeP 1 a} \\/ {ppLifeP 0 b}"
where
  paren (b : Bool) (s : String) : String := if b then s!"({s})" else s

def ppLife (a : CLife) : String := ppLifeP 1 a

def tvName (d : Nat) : String := if d == 0 then "X" else s!"X{d}"

def parenIf (b : Bool) (s : String) : String := if b then s!"({s})" else s

mutual
/-- A value type in the surface syntax, at precedence `p` (syntax-core §4: `0` binders, `1`
`-o`/`=>`, `2` `&`, `3` `+`, `4` `*`, `5` prefix); `d` is the number of enclosing `μ`s. -/
def ppV (d p : Nat) : CVTy → String
  | .unit => "1"
  | .zero => "0"
  | .tensor A B => parenIf (p > 4) s!"{ppV d 5 A} * {ppV d 4 B}"
  | .sum A B => parenIf (p > 3) s!"{ppV d 4 A} + {ppV d 3 B}"
  | .thunk (.arr A (.ret B)) => parenIf (p > 1) s!"{ppV d 2 A} => {ppV d 1 B}"
  | .thunk (.all x b (.ret A)) => parenIf (p > 0) s!"all {ppLVar x} < {ppLife b}. {ppV d 0 A}"
  | .thunk C => parenIf (p > 5) s!"U {ppC 6 C}"
  | .ref A => parenIf (p > 5) s!"ref {ppV d 5 A}"
  | .imm a A => parenIf (p > 5) s!"imm {ppLife a} {ppV d 5 A}"
  | .mut a A => parenIf (p > 5) s!"mut {ppLife a} {ppV d 5 A}"
  | .box a A => parenIf (p > 5) s!"box {ppLife a} {ppV d 5 A}"
  | .bang A => parenIf (p > 5) s!"!{ppV d 5 A}"
  | .unk => "unk"
  | .int .w32 => "i32"
  | .int .w64 => "i64"
  | .tvar n => if n < d then tvName (d - 1 - n) else s!"?{n}"
  | .mu A => parenIf (p > 0) s!"mu {tvName d}. {ppV (d + 1) 0 A}"
/-- A computation type in the surface syntax, at precedence `p`. -/
def ppC (p : Nat) : CCTy → String
  | .ret A => parenIf (p > 5) s!"F {ppV 0 5 A}"
  | .arr A C => parenIf (p > 1) s!"{ppV 0 2 A} -o {ppC 1 C}"
  | .amp C D => parenIf (p > 2) s!"{ppC 3 C} & {ppC 2 D}"
  | .top => "top"
  | .all x b C => parenIf (p > 0) s!"forall {ppLVar x} < {ppLife b}. {ppC 0 C}"
  | .delay A => parenIf (p > 5) s!"delay {ppV 0 5 A}"
  | .stream A => parenIf (p > 5) s!"stream {ppV 0 5 A}"
end

def ppVTy (A : CVTy) : String := ppV 0 0 A
def ppCTy (C : CCTy) : String := ppC 0 C

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
  /-- A `def`'s type parameters. -/
  tps : List (String × CVTy)

/-- An abbreviation's body: its own scope, no names of the use site, the use's `Δ`. -/
def TyEnv.closedAt (E : TyEnv) (sc : Scope) : TyEnv :=
  { E with scope := sc, lenv := [], mu := [], hid := [], tps := [] }

def TyEnv.enterU (E : TyEnv) : TyEnv := { E with mu := [], hid := E.mu ++ E.hid }

/-- A lifetime. -/
def elabLife (Δ : LifeCtx) (lenv : List (String × LifeVar)) : Frontend.Life → Except Error CLife
  | .var sp x => match lenv.lookup x with
    | some v => pure (.var v)
    | none => err sp s!"unbound lifetime variable '{x}"
  | .top _ => pure .top
  | .dom _ => pure Δ.meetOfDom
  | .meet _ a b => do pure (.meet (← elabLife Δ lenv a) (← elabLife Δ lenv b))
  | .join _ a b => do pure (.join (← elabLife Δ lenv a) (← elabLife Δ lenv b))

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
    | .thunk _ C => do pure (.thunk (← elabC n E.enterU C))
    | .ref _ A => do pure (.ref (← elabV n E A))
    | .imm _ a A => do pure (.imm (← elabLife E.Δ E.lenv a) (← elabV n E A))
    | .mut _ a A => do pure (.mut (← elabLife E.Δ E.lenv a) (← elabV n E A))
    | .box _ a A => do pure (.box (← elabLife E.Δ E.lenv a) (← elabV n E A))
    | .bang _ A => do pure (.bang (← elabV n E A))
    | .unk _ => pure .unk
    | .int _ w => pure (.int w)
    | .mu sp X A => do
        let B ← elabV n { E with mu := X.name :: E.mu } A
        if VTy.clB 1 B = false then
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
            | some B => pure B
            | none => match E.scope.findType x with
              | some (B, sc) => elabV n (E.closedAt sc) B
              | none => err sp s!"unknown type `{x}`"
    | .lolli _ A B => do
        let E' := E.enterU
        pure (.thunk (.arr (← elabV n E' A) (.ret (← elabV n E' B))))
    | .all _ x b A => do
        let bl ← elabLife E.Δ E.lenv b
        let v := E.Δn.freshVar
        let E' := { E.enterU with Δn := E.Δn.extend v bl, lenv := (x.name, v) :: E.lenv }
        pure (.thunk (.all v bl (.ret (← elabV n E' A))))
    | .block _ σ => do pure (← elabS n E σ).refTy
    | .val _ σ => do pure (← elabS n E σ).valTy
    | .fam _ m a σ => do
        let al ← elabLife E.Δ E.lenv a
        let s ← elabS n E σ
        pure (match m with
          | .mut => s.famTy BoCa.Fig16.LogRel.Core.VTy.mut al
          | .imm => s.famTy BoCa.Fig16.LogRel.Core.VTy.imm al)
    | .view _ a A => do pure ((← elabV n E A).immReborrow (← elabLife E.Δ E.lenv a))
/-- A computation type. -/
def elabC : Nat → TyEnv → CTy → Except Error CCTy
  | 0, _, C => err C.span "type abbreviations nested too deeply"
  | n + 1, E, C => match C with
    | .ret _ A => do pure (.ret (← elabV n E A))
    | .arr _ A C => do pure (.arr (← elabV n E A) (← elabC n E C))
    | .amp _ C D => do pure (.amp (← elabC n E C) (← elabC n E D))
    | .top _ => pure .top
    | .all _ x b C => do
        let bl ← elabLife E.Δ E.lenv b
        let v := E.Δn.freshVar
        let E' := { E with Δn := E.Δn.extend v bl, lenv := (x.name, v) :: E.lenv }
        pure (.all v bl (← elabC n E' C))
    | .delay _ A => do pure (.delay (← elabV n E A))
    | .stream _ A => do pure (.stream (← elabV n E A))
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
