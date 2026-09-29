import Frontend.Elab.Infer

/-!
# Frontend — Elab — implicit deep copies  `[#108, docs/decisions.md 39]`

A persistent value may be used more than once (SPEC §10), and the compiled program keeps every
object owned by exactly one word: a variable used by two sequential parts of a term is copied for
all but the last (`Backend/README.md`, Memory discipline; `Backend/Clos/Convert.lean`). At a type
that holds recursive data the copy is deep: it allocates every node. No C or Rust programmer
writes that copy by accident, so it is not made by accident here either. Such a use is written
`clone(x)`, and a use that would copy without it is an error that points at it.

A copy at a type whose copy is its words (`i32`, `bool`, a pair of them) stays implicit.

**Which uses copy.** This follows closure conversion's ownership plan on the elaborated core,
node for node: the parts of a node run in sequence (a pair's halves, an application's argument
and then its function, a `bind`'s or `let`'s head and body, a `case`'s scrutinee and then its
arms), the two arms of a `case` and the two components of `<M, N>` are one part (only one runs),
and a variable free in a part and in a later part is copied for the earlier one. Every use of it
in the earlier part receives a copy on its path, so each must be written `clone(x)`.

**Recursive data** is a persistent type with a `μ` in it, also under `⊗`, `⊕`, `[@a]` and `!`
(`deepData`): the backend boxes a `μ`'s recursive fields, and its generated copy allocates each
one. A persistent closure (`!(A ⇒ B)`) is copied by copying what it captures, which its type does
not say; it is not checked here, and `bcc-counts` counts every deep copy a run makes.
-/

namespace Frontend.Elab
open Frontend.Check

/-- A persistent type that holds recursive data, whose copy allocates. -/
def deepData : CVTy → Bool
  | .mu _ => true
  | .tensor A B | .sum A B => deepData A || deepData B
  | .box _ A | .bang A => deepData A
  | _ => false

/-- A use of a local variable: its name, span and type. -/
structure Use where
  x : String
  sp : Span
  ty : Option CVTy

/-- The local variables in scope, innermost first, with their types. -/
abbrev Scope := List (String × Option CVTy)

def Scope.push (sc : Scope) (bs : List Binder) : Scope :=
  bs.foldl (fun sc b => (b.name, b.ty) :: sc) sc

/-- The binders of node `h` (its `bs`) that are in scope in its child `i`. -/
def Head.scopeOf (h : Head) (bs : List Binder) (i : Nat) : List Binder :=
  match h, i with
  | .comp (.bind ..), 1 | .comp (.lam ..), 0 | .comp (.letPair ..), 1 => bs
  | .comp (.case ..), 1 => bs.take 1
  | .comp (.case ..), 2 => bs.drop 1
  | .comp (.for_ ..), 1 => bs
  | _, _ => []

/-- The parts of node `h` that run in sequence, as groups of its children's indices, in the order
they run. A node with one group has no sequential parts. -/
def Head.parts : Head → List (List Nat)
  | .val (.pair ..) => [[0], [1]]
  -- `V W` evaluates the argument first (`Backend/Clos/Convert.lean`, `conv`).
  | .val (.app ..) => [[1], [0]]
  | .comp (.bind ..) | .comp (.letUnit ..) | .comp (.letPair ..) => [[0], [1]]
  | .comp (.case ..) => [[0], [1, 2]]
  | .comp (.for_ ..) => [[0], [1], [2]]
  | _ => []

mutual
/-- The uses of local variables free in a node, in order. -/
def TNode.uses : Nat → Scope → TNode → List Use
  | 0, _, _ => []
  | n + 1, sc, .mk h ty bs ks =>
    let own : List Use := match h with
      | .val (.var sp x) => match sc.lookup x with
        | some A => [⟨x, sp, ty.v? <|> A⟩]
        | none => []
      | .comp (.app sp _ x) => match sc.lookup x.name with
        | some A => [⟨x.name, sp, A⟩]
        | none => []
      | _ => []
    own ++ TNode.usesL n sc h bs 0 ks

def TNode.usesL : Nat → Scope → Head → List Binder → Nat → List TNode → List Use
  | _, _, _, _, _, [] => []
  | n, sc, h, bs, i, k :: ks =>
    ((TNode.uses n (sc.push (h.scopeOf bs i)) k).filter
      (!((h.scopeOf bs i).map (·.name)).contains ·.x)) ++ TNode.usesL n sc h bs (i + 1) ks
end

/-- The uses free in child `i` of node `h`, but those of the variables `h` binds there. -/
def TNode.kidUses (n : Nat) (sc : Scope) (h : Head) (bs : List Binder) (i : Nat) (k : TNode) :
    List Use :=
  let own := (h.scopeOf bs i).map (·.name)
  (TNode.uses n (sc.push (h.scopeOf bs i)) k).filter (!own.contains ·.x)

/-- The uses in the children `is` of a node. -/
def groupUses (n : Nat) (sc : Scope) (h : Head) (bs : List Binder) (ks : List TNode)
    (is : List Nat) : List Use :=
  is.flatMap fun i => match ks[i]? with
    | some k => TNode.kidUses n sc h bs i k
    | none => []

/-- The type of `x` among `us`. -/
def tyAmong (x : String) (us : List Use) : Option CVTy :=
  (us.find? (fun u => u.x == x && u.ty.isSome)).bind (·.ty)

/-- The uses of `earlier` that are copied because `later` uses the same variable at a type that
holds recursive data, with a use in `later` for each; the uses `marked` (written `clone(x)`)
excepted. -/
def copiedUses (sc : Scope) (marked : List Span) (earlier later : List Use) : List (Use × Use) :=
  earlier.filterMap fun u =>
    if marked.contains u.sp then none else
    match later.find? (·.x == u.x) with
    | some v =>
      let A := u.ty <|> v.ty <|> tyAmong u.x (earlier ++ later) <|> (sc.lookup u.x).join
      if (A.map fun A => A.persistent && deepData A).getD false then some (u, v) else none
    | none => none

/-- Every earlier use that is copied implicitly, with a later use of the same variable. -/
def TNode.copies : Nat → List Span → Scope → TNode → List (Use × Use)
  | 0, _, _, _ => []
  | n + 1, marked, sc, .mk h _ bs ks =>
    let groups := match h with
      -- `M x` evaluates the argument `x` first.
      | .comp (.app sp _ x) =>
        [(match sc.lookup x.name with
          | some A => [(⟨x.name, sp, A⟩ : Use)]
          | none => []), groupUses n sc h bs ks [0]]
      | _ => (h.parts.map (groupUses n sc h bs ks))
    let here := (List.range groups.length).flatMap fun i =>
      let later := (groups.drop (i + 1)).flatten
      copiedUses sc marked (groups.getD i []) later
    here ++ ((List.range ks.length).zip ks).flatMap fun (i, k) =>
      TNode.copies n marked (sc.push (h.scopeOf bs i)) k

/-- The error for the first implicit deep copy in a program's typed IR, if there is one. `marked`
are the spans of the uses written `clone(x)`. -/
def implicitCopy (t : TProgram) (marked : List Span) : Option Error := do
  let found := t.decls.flatMap fun d => match d.body? with
    | some b => b.copies inferFuel marked []
    | none => []
  let (u, v) ← found.head?
  let ty := (u.ty <|> v.ty).map ppVTy |>.getD "?"
  pure ⟨u.sp, s!"`{u.x}` is used again at {v.sp.start.render}, so this use copies it, and its " ++
    s!"type `{ty}` holds recursive data: the copy allocates every node. Write `clone({u.x})` " ++
    s!"to copy it here, or do not use `{u.x}` after this"⟩

end Frontend.Elab
