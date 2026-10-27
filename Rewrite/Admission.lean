import Rewrite.ReadBack
import Rewrite.R0
import Frontend.Check.StoredAtX
import Frontend.Check.EnvN

/-!
# Rewrite — R5's admission, report only  `[spec §54]`

**R5-0** (the R5 scope's §6): for every `handle` node with an operation R0 does not rewrite, the
form R5 gives it, decided from checked facts. Nothing is rewritten. Each node's form is

* `R5 opt`: a stored node (A1) where every other non-abortive operation is `tail` (A2), every
  stored clause is in the `StoredAtX` grammar (A3, the checker's record `TInfo.sshape`), its region
  is closed (A4), and no gap holds;
* `R5 fallback (A2|A3|A4: …)`: a stored node where A2, A3 or A4 fails and no gap holds;
* `left: <gap>`: a stored node at a gap of the scope's §3.C, every one that holds listed and the
  first its form: `lendR` (OQ1: such a node is left with its pin position, whatever else holds),
  then codata whose observations perform `n` (#691), answer types that differ at `n` in an open
  region (#692, A9), a `Div` region (A7), a state that does not outlive `d` (A6), a finaliser that
  performs; and a perform path that crosses another name's handler still in Backend2;
* `left: <sibling row>`: a node with no stored operation: `R3` (`once`), `R2`/`R2σ`
  (`resume-or-cancel`), `R1σ` (`tail+state`), `R1-ev` (a `[handle]` node whose operations are all
  `tail`), `R1` and `R2` at the tail-resuming and resume-or-cancel rules' nodes.

**The facts read**, all checked: the node's kind V/VB and `d`, its clause kinds `ks`
(`classifyHandler_sound`), its counts `E`, the `StoredAtX` records (`storedShapes_sound`), its use
masks (`Env_N`; A8, its persistence, is the rule's premise at every node of a checked term,
`TDerivesP.handleV_env_persistent` and `TDerivesP.handleVB_env_persistent`, and is not decided
here), the rows and types on the region's nodes,
its use keys, the masks of its splits, and the program's pins. No `HSite` or key string,
`Layouts`, `Flow` or `.expected` file is read.

**The region** (`Region(N)`): the handled computation and the instances it reaches by `use` whose
type holds `n`, each once, the handled computation of an inner node of `n` excluded. `regionScan`
reads it lexically: its points (the `perform`s of the node's stored operations), its other
performs of `n`, its `lendR`s (A5), its `Div` rows and `reify`/`iterate`/`div_fuel` (A7), whether
a finaliser that performs is in scope at a point, and the nodes of other names a point lies in
the handled computation of.

**The call walk** (`cw`) runs the region from the handled computation following its calls, with
the origin of each value it can follow (`Org`): a `use` instance, a code value and whether it is
closed, a pair, `bounded_fix` and a recursive group's self-reference, a primitive, an inner stored
node's answer. A `!`-parameter bound at the use to a closed `!` value is known, as R5-1
substitutes it. A `force` at a row holding `n` of any other value is an open region (A4). An
observation of codata whose observations perform `n` is #691; of an inner stored node's answer,
only if R5 leaves that node (R5-4 holds an admitted inner node's answer as its state). At each point the walk records the live slots (`Live_p`, the slots the later part
of each split it lies in uses, by the split's masks) and the calls in progress (its frames). A
call is suspending when a point is reached under it; a call that re-enters code in progress is a
cycle. The region is lexical (no suspending call), flat (the suspending calls a tree: each callee
one call site) or array (a callee with two suspending call sites, or a cycle). At VB, each slot of
the state, the live slots of a point or of a suspending call's frame and `Env_N`, must outlive `d`
(A6, `outlivesB`); an inner stored node's answer only if R5 leaves that node. The forms that
depend on other nodes' forms are read to a fixed point (`crossing`), each node matched by its id
(`numberHandles`), never by its span.

Every traversal is bounded by `fuel`, whose exhaustion is a hard error.
-/

namespace Rewrite
open Frontend (Span)
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count Jdg closedAt)
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo SShape SObs SIntro outlivesB Masks)
open BoCa.Fig16.LogRel.Core.ClauseKinds (HKind ClauseKind isAbortive)
open BoCa.Lifetime (LifeCtx)

/-! ### Rows and types -/

/-- A computation type performs `n`: a layer of `n`, through `⊸`, `∀` and `&`. -/
def ctyHas (n : UInt32) : CTy → Bool
  | .eff m _ _ _ _ _ _ D => m == n || ctyHas n D
  | .arr _ D | .all _ _ D => ctyHas n D
  | .amp C D => ctyHas n C || ctyHas n D
  | _ => false

/-- A value type holds a computation type that performs `n` (`ctyHas`), outside recursive and
codata types' bodies: the type of a `use` whose instance is in a region of `n`. -/
def vtyHas (n : UInt32) : VTy → Bool
  | .thunk C => ctyHasV n C
  | .tensor A B | .sum A B => vtyHas n A || vtyHas n B
  | .box _ A | .bang A | .ref A | .imm _ A | .mut _ A | .fam A => vtyHas n A
  | _ => false
where
  /-- `ctyHas`, through the value types of arguments and answers too. -/
  ctyHasV (n : UInt32) : CTy → Bool
    | .eff m _ _ _ _ _ _ D => m == n || ctyHasV n D
    | .arr A D => vtyHas n A || ctyHasV n D
    | .all _ _ D => ctyHasV n D
    | .amp C D => ctyHasV n C || ctyHasV n D
    | .ret A => vtyHas n A
    | _ => false

/-- A value type's head, for the reasons. -/
def vHead : VTy → String
  | .thunk _ => "U"
  | .bang _ => "!"
  | .box _ _ => "box"
  | .imm _ _ => "imm"
  | .mut _ _ => "mut"
  | .ref _ => "ref"
  | .tensor _ _ => "*"
  | .sum _ _ => "+"
  | .mu _ => "mu"
  | .fam _ => "fam"
  | .int _ => "int"
  | .unit => "1"
  | .zero => "0"
  | .unk => "unk"
  | .tvar _ => "var"
  | .opq _ => "opq"

/-- A fingerprint of a value type, for the call walk's memo. -/
def vfp : VTy → String
  | .tensor A B => s!"({vfp A}*{vfp B})"
  | .sum A B => s!"({vfp A}+{vfp B})"
  | .box _ A => s!"[{vfp A}]"
  | .bang A => s!"!{vfp A}"
  | .ref A => s!"r{vfp A}"
  | .imm _ A => s!"i{vfp A}"
  | .mut _ A => s!"m{vfp A}"
  | .fam A => s!"f{vfp A}"
  | .mu A => s!"mu{vfp A}"
  | .tvar k => s!"#{k}"
  | A => vHead A

def spStr (sp : Span) : String := sp.start.render

/-! ### Origins -/

/-- What a value is, as far as the walk follows it: a `def`'s instance (its declaration, type
arguments and body, at the use's context); a code value (`thunkv`, `!thunkv`, its span, whether
its term is closed, at its context); a pair; `bounded_fix`; another primitive; a recursive
group's self-reference, to its step; or unknown. -/
inductive Org where
  | unk
  | inst (decl : Nat) (targs : List VTy) (body : TExpr) (env : List Org) (tys : List (Option VTy))
      (Δ : LifeCtx)
  | code (sp : Span) (closed : Bool) (t : TExpr) (env : List Org) (tys : List (Option VTy))
      (Δ : LifeCtx)
  | tup (a b : Org)
  | fix
  | prim (what : String)
  | self (step : Org)
  /-- The answer of a `handle` node of another name with a stored operation (an inner node R5
  rewrites first, inside-out; R5-4 holds its ν-value as its state). -/
  | inner (id : String)

instance : Inhabited Org := ⟨.unk⟩

/-- The origin's identity, for the memo. -/
def Org.sig : Org → String
  | .unk => "?"
  | .inst d ts .. => s!"I{d}<{",".intercalate (ts.map vfp)}>"
  | .code sp c .. => s!"C{sp.start.render}-{sp.stop.render}{if c then "" else "~"}"
  | .tup a b => s!"({a.sig},{b.sig})"
  | .fix => "fix"
  | .prim w => s!"P{w}"
  | .self s => s!"S{s.sig}"
  | .inner id => s!"N{id}"

/-- Known code, as A4 reads it: an instance, a closed code value, a self-reference, a primitive. -/
def Org.known : Org → Bool
  | .inst .. | .self _ | .prim _ | .fix => true
  | .code _ c .. => c
  | _ => false

/-- The code origins a value holds, through its pairs. -/
def Org.codes : Org → List Org
  | .tup a b => a.codes ++ b.codes
  | o@(.inst ..) | o@(.code ..) => [o]
  | _ => []

/-- **The origin of a value**, at the origins `env`, types `tys` and lifetime context `Δ` of its
context's slots. -/
def vorg (env : List Org) (tys : List (Option VTy)) (Δ : LifeCtx) : Nat → TExpr → Org
  | 0, _ => .unk
  | f + 1, t => match t with
    | .var _ _ i _ => env.getD i .unk
    | .bangE _ _ _ v | .boxI _ _ _ _ v | .boxE _ _ _ _ v | .selfCall _ _ _ _ v | .immSub _ _ _ _ _ v
    | .mutSub _ _ _ _ _ v => vorg env tys Δ f v
    | .use _ _ _ decl targs _ b => .inst decl targs b env tys Δ
    | .bangThunkV i .. | .thunkV i .. | .thunkF i .. | .bangThunkF i .. =>
        .code i.sp (closedAt 0 t.erase) t env tys Δ
    | .tensorI _ _ _ _ _ a b => .tup (vorg env tys Δ f a) (vorg env tys Δ f b)
    | .boundedFix .. => .fix
    | .countFold .. => .prim "count_fold"
    | .countTry .. => .prim "count_try"
    | .iterate .. => .prim "iterate"
    | .divFuel .. => .prim "div_fuel"
    | .reify .. => .prim "reify"
    | .foldImm .. | .foldOwn .. | .foldReuse .. => .prim "fold"
    | .unfoldN .. => .prim "unfold"
    | _ => .unk

/-! ### Handle nodes -/

/-- A `handle` node of the checked program: its fields, and the origins, types and lifetime
context of its context's slots where the discovery met it. -/
structure HNode where
  /-- The node's id (`numberHandles`): its scope and its pre-order index there. -/
  id : String
  sp : Span
  n : UInt32
  /-- `V`, `VB`, `T` or `L`. -/
  kind : String
  d : Option BoCa.Lifetime.Life
  S : Row
  E : List (Count × VTy × VTy)
  A : VTy
  R : VTy
  ks : List HKind
  sshape : List (Option SShape)
  u : Option Masks
  te : TExpr
  env : List Org
  tys : List (Option VTy)
  Δ : LifeCtx

instance : Inhabited HNode :=
  ⟨{ id := "", sp := default, n := 0, kind := "", d := none, S := [], E := [], A := .unit, R := .unit,
     ks := [], sshape := [], u := none, te := .unitI default (.val .unit), env := [], tys := [],
     Δ := ⟨[]⟩ }⟩

/-- The types of the slots the binders of a node push for each of its children (`children`'s
scopes), the dead slots at `1`; `none` where the type is not on the node. -/
def pushTys : TExpr → List (List (Option VTy))
  | .thunkF .. | .lamDead .. | .bangThunkF .. | .allI .. => [[some .unit]]
  | .bind _ _ A _ _ _ _ => [[], [some A]]
  | .lam _ _ A _ _ => [[some A]]
  | .withI .. => [[some .unit, some .unit], [some .unit, some .unit]]
  | .tensorE _ _ A B _ _ _ _ => [[], [some B, some A]]
  | .sumE _ _ A B _ _ _ _ _ => [[], [some A], [some B]]
  | .effLet _ _ A _ _ _ _ _ => [[], [some A]]
  | .effThen _ _ A _ _ _ _ _ _ _ _ => [[], [some A], [some .unit]]
  | .letPoly .. => [[], [some .unit]]
  | .lendR .. => [[], [none]]
  | .lendLoopR .. => [[none], [none], []]
  | _ => []

/-- The origins the binders of a node push for each of its children, from the origin of the bound
computation where the node binds a `return V` (`[bind]`, `[let]`) or splits a pair (`[⊗E]`). -/
def pushOrgs (env : List Org) (tys : List (Option VTy)) (Δ : LifeCtx) (t : TExpr) :
    List (List Org) :=
  let retOrg : TExpr → Org := fun
    | .ret _ _ _ v => vorg env tys Δ fuel v
    | .effSub _ _ _ _ _ (.ret _ _ _ v) => vorg env tys Δ fuel v
    | _ => .unk
  match t with
  | .bind _ _ _ _ _ tM _ | .effLet _ _ _ _ _ _ tM _ => [[], [retOrg tM]]
  | .tensorE _ _ _ _ _ _ tV _ => match vorg env tys Δ fuel tV with
    | .tup a b => [[], [b, a]]
    | _ => [[], [.unk, .unk]]
  | .sumE _ _ _ _ _ _ tV _ _ => match vorg env tys Δ fuel tV with
    | o@(.self _) => [[], [.unk], [o]]
    | _ => [[], [.unk], [.unk]]
  | _ => []

/-- The context of a child: its scope applied to the node's origins, types and lifetime
context. -/
def childCtx (env : List Org) (tys : List (Option VTy)) (Δ : LifeCtx) (t : TExpr) (idx : Nat)
    (sc : BoCa.Fig16.LogRel.Core.Check.TScope) : List Org × List (Option VTy) × LifeCtx :=
  let pt := (pushTys t).getD idx []
  let po := (pushOrgs env tys Δ t).getD idx []
  let Δc : LifeCtx := match t with
    | .allI _ _ x b _ _ _ | .lendR _ _ x b _ _ _ _ _ => Δ.extend x b
    | _ => Δ
  match sc with
  | .push k =>
    let ty := (List.range k).map fun i => pt.getD i none
    let og := (List.range k).map fun i => po.getD i .unk
    (og ++ env, ty ++ tys, Δc)
  | .fresh k =>
    ((List.range k).map fun i => po.getD i .unk, (List.range k).map fun i => pt.getD i none, Δc)

/-- An instance key, as the walks deduplicate instances: the declaration and type arguments. -/
abbrev IKey := Nat × List VTy

/-- **The `handle` nodes of a checked program**, with where each is: `main`'s typed term and each
instance's body once, read lexically. -/
def discover : Nat → List Org → List (Option VTy) → LifeCtx → TExpr → List IKey × List HNode →
    Except String (List IKey × List HNode)
  | 0, _, _, _, _, _ => throw "R5 admission: a term nested too deeply to find its handle nodes"
  | f + 1, env, tys, Δ, t, (seen, acc) => do
    let here : List HNode := match t with
      | .effHandleV i _ S E _ n A R u ks _ _ _ te =>
          [⟨(handleIdOf? i).getD "", i.sp, n, "V", none, S, E, A, R, ks, i.sshape, some u, te, env, tys, Δ⟩]
      | .effHandleVB i _ S E _ n A R d u ks _ _ _ te =>
          [⟨(handleIdOf? i).getD "", i.sp, n, "VB", some d, S, E, A, R, ks, i.sshape, some u, te, env, tys, Δ⟩]
      | .effHandleT i _ S _ E _ n A R _ _ _ _ te =>
          [⟨(handleIdOf? i).getD "", i.sp, n, "T", none, S, E, A, R, E.map BoCa.Fig16.LogRel.Core.ClauseKinds.tailKind, [],
            none, te, env, tys, Δ⟩]
      | .effHandleL i _ S _ E _ _ n A R _ _ _ _ te =>
          [⟨(handleIdOf? i).getD "", i.sp, n, "L", none, S, E, A, R, E.map fun o =>
            ⟨o.1, if isAbortive o then .abortive else .resumeOrCancel false⟩, [], none, te, env,
            tys, Δ⟩]
      | _ => []
    let st := (seen, acc ++ here)
    match t with
    | .use _ _ _ decl targs _ b =>
      if seen.contains (decl, targs) then pure st
      else discover f env tys Δ b ((decl, targs) :: seen, acc ++ here)
    | _ =>
      t.children.zipIdx.foldlM (init := st) fun st ((sc, c), idx) =>
        let (env', tys', Δ') := childCtx env tys Δ t idx sc
        discover f env' tys' Δ' c st

/-- The sibling rows a node with no stored operation waits for, from its kind and kinds: `R1` at
the tail-resuming rule's node, `R2` at the resume-or-cancel rule's (§51); at a `[handle]` node,
`R3` (`once`), `R2` (`resume-or-cancel`), `R2σ` (with state), `R1σ` (`tail+state`), and `R1-ev`
when every operation is `tail`. A node whose every operation is abortive and that R0 does not
rewrite is R0's, left. -/
def siblingRows (kind : String) (ks : List HKind) : String :=
  if kind == "T" then "R1" else if kind == "L" then "R2" else
  if ks.all (·.kind == .abortive) then "R0 left" else
  let ks := (ks.filter fun k => k.kind != .abortive).map (·.kind)
  let rows := [("R3", ks.any fun k => match k with | .resumeOnce _ => true | _ => false),
    ("R2", ks.any (· == .resumeOrCancel false)), ("R2σ", ks.any (· == .resumeOrCancel true)),
    ("R1σ", ks.any (· == .tailState))]
  match rows.filter (·.2) with
  | [] => "R1-ev"
  | rs => ", ".intercalate (rs.map (·.1))

/-! ### The region, read lexically -/

/-- A node of another name around a point: its name and span; whether it has a stored operation
(then its form is its own admission's); otherwise the sibling row it waits for. -/
structure Crossed where
  m : UInt32
  id : String
  sp : Span
  stored : Bool
  row : String
  deriving Inhabited

/-- A point of the region: its span, its operation, the nodes of other names whose handled
computation it lies in (each with its span), and whether a finaliser that performs is in scope at
it. -/
structure LPoint where
  sp : Span
  j : Nat
  crossed : List Crossed
  finPerf : Bool

/-- What `regionScan` reads of a region. -/
structure Scan where
  points : List LPoint := []
  tails : Nat := 0
  lends : List Span := []
  divs : List String := []
  inner : Nat := 0
  seen : List IKey := []

/-- **The region of a node of `n`, read lexically**: its handled computation and the instance
bodies it reaches, each once; an inner node of `n`'s handled computation excluded. `jst` are the
node's stored operations, `crossed` the nodes of other names around the walk, `finPerf` whether a
finaliser that performs is in scope. -/
def regionScan (n : UInt32) (jst : List Nat) (ruled : List UInt32) :
    Nat → List Crossed → Bool → TExpr → Scan → Except String Scan
  | 0, _, _, _, _ => throw "R5 admission: a region nested too deeply to scan"
  | f + 1, crossed, finPerf, t, s => do
    let s := match t with
      | .effPerform i _ _ o _ =>
          if o.n == n then
            if jst.contains o.i.toNat then
              { s with points := s.points ++ [⟨i.sp, o.i.toNat, crossed, finPerf⟩] }
            else { s with tails := s.tails + 1 }
          else s
      | .lendR i .. | .lendLoopR i .. => { s with lends := s.lends ++ [i.sp] }
      | .reify i .. => { s with divs := s.divs ++ [s!"reify at {spStr i.sp}"] }
      | .iterate i .. => { s with divs := s.divs ++ [s!"iterate at {spStr i.sp}"] }
      | .divFuel i .. => { s with divs := s.divs ++ [s!"div_fuel at {spStr i.sp}"] }
      | .effLet i _ _ _ S _ _ _ | .effSub i _ S _ _ _ =>
          if rowHas BoCa.divEff S then { s with divs := s.divs ++ [s!"Div row at {spStr i.sp}"] }
          else s
      | _ => s
    match t with
    | .use _ jd _ decl targs _ b =>
      -- The region's static callees: the instances whose type holds `n`.
      let holds := match jd with
        | .val A => vtyHas n A
        | .comp C => vtyHas.ctyHasV n C
      if !holds || s.seen.contains (decl, targs) then pure s
      else regionScan n jst ruled f crossed finPerf b { s with seen := (decl, targs) :: s.seen }
    | .effHandleV i _ _ _ _ m _ _ _ _ _ _ tc te | .effHandleVB i _ _ _ _ m _ _ _ _ _ _ _ tc te
    | .effHandleT i _ _ _ _ _ m _ _ _ _ _ tc te | .effHandleL i _ _ _ _ _ _ m _ _ _ _ _ tc te =>
      let s ← regionScan n jst ruled f crossed finPerf tc s
      if m == n then pure { s with inner := s.inner + 1 }
      else
        let (kind, ks) := match t with
          | .effHandleV _ _ _ _ _ _ _ _ _ ks .. => ("V", ks)
          | .effHandleVB _ _ _ _ _ _ _ _ _ _ ks .. => ("VB", ks)
          | .effHandleT .. => ("T", [])
          | _ => ("L", [])
        let c : Crossed := { m, id := (handleIdOf? i).getD "", sp := i.sp, stored := ks.any (·.kind == .stored),
                             row := siblingRows kind ks }
        -- A node R0 rewrites is gone before R5 (its name is one of R0's).
        let crossed' := if ruled.contains m then crossed else crossed ++ [c]
        regionScan n jst ruled f crossed' finPerf te s
    | .effThen _ _ _ _ _ _ SD _ tM tN tD =>
      let perf := SD.any fun o => o.cnt != .zero
      let s ← regionScan n jst ruled f crossed (finPerf || perf) tM s
      let s ← regionScan n jst ruled f crossed finPerf tN s
      regionScan n jst ruled f crossed finPerf tD s
    | _ => t.children.foldlM (init := s) fun s (_, c) => regionScan n jst ruled f crossed finPerf c s

/-! ### The call walk -/

/-- An elimination applied to code: an argument (its origin and type), a projection of `&`, an
observation of codata (`nu_out`), a lifetime application. -/
inductive Elim where
  | arg (o : Org) (ty : Option VTy)
  | p1
  | p2
  | out
  | life

/-- A point the call walk reached: its span, its live slots' types, the lifetime context, and the
calls in progress (ids, innermost first). -/
structure CPoint where
  sp : Span
  live : List (Org × Option VTy)
  Δ : LifeCtx
  frames : List Nat

/-- A call the walk made into known code: its id, span, callee, the caller's live slots' types
and lifetime context, whether it re-enters code in progress (a cycle), and whether its walk was
the memo's. -/
structure CCall where
  id : Nat
  sp : Span
  callee : String
  live : List (Org × Option VTy)
  Δ : LifeCtx
  cyc : Bool
  memoOf : Option Nat

/-- The call walk's state. -/
structure CAcc where
  points : List CPoint := []
  calls : List CCall := []
  opens : List Span := []
  /-- Observations of codata whose observations perform `n`, of a value not R5's own (#691). -/
  codata : List Span := []
  /-- Those of an inner stored node's answer, with the node's id. -/
  codataIn : List (String × Span) := []
  /-- Walks done, by callee and arguments, with the call that did them. -/
  memo : List (String × Nat) := []
  /-- Calls in progress: id and walk key. -/
  stk : List (Nat × String) := []
  /-- Splits whose masks and context differ in length (the walk's types are then not read). -/
  mismatch : Nat := 0
  nextId : Nat := 0

abbrev CM := StateT CAcc (Except String)

/-- The walk's fixed data: the node's name and stored operations. -/
structure CCfg where
  n : UInt32
  jst : List Nat

/-- The slots a split's later part uses (`u.u₂`), with their origins and types, at the split's
context. -/
def laterLive (u : Masks) (env : List Org) (tys : List (Option VTy)) :
    CM (List (Org × Option VTy)) := do
  if u.ms.length != tys.length then
    modify fun s => { s with mismatch := s.mismatch + 1 }
  pure ((u.ms.zip (env.zip tys)).filterMap fun ((_, b), sl) => if b then some sl else none)

/-- The elimination chain of a computation: its head and the eliminations applied to it, the
first applied first. -/
def elimsOf (env : List Org) (tys : List (Option VTy)) : TExpr → List Elim → TExpr × List Elim
  | .app _ _ i _ _ _ tM, es => elimsOf env tys tM (.arg (env.getD i .unk) (tys.getD i none) :: es)
  | .proj₁ _ _ _ _ t, es => elimsOf env tys t (.p1 :: es)
  | .proj₂ _ _ _ _ t, es => elimsOf env tys t (.p2 :: es)
  | .nuOut _ _ _ t, es => elimsOf env tys t (.out :: es)
  | .allE _ _ _ _ _ _ t, es => elimsOf env tys t (.life :: es)
  | .effSub _ _ _ _ _ t, es => elimsOf env tys t es
  | t, es => (t, es)

/-- The computation a code value runs when forced, and what its wrapper pushes. -/
def codeBody : Nat → TExpr → Option (TExpr × Bool)
  | 0, _ => none
  | f + 1, t => match t with
    | .bangThunkV _ _ _ c | .thunkV _ _ _ c => some (c, false)
    | .thunkF _ _ _ c | .bangThunkF _ _ _ c => some (c, true)
    | .use _ _ _ _ _ _ b | .bangE _ _ _ b | .boxI _ _ _ _ b | .boxE _ _ _ _ b => codeBody f b
    | _ => none

mutual

/-- **The call walk** of a computation, at the origins, types and lifetime context of its
context's slots, `cur` the live slots of the body it is in; its answer's origin. -/
def cw (cfg : CCfg) : Nat → List Org → List (Option VTy) → LifeCtx → List (Org × Option VTy) → TExpr →
    CM Org
  | 0, _, _, _, _, _ => throw "R5 admission: a region nested too deeply to walk"
  | f + 1, env, tys, Δ, cur, t => do
    match t with
    | .ret _ _ _ v => pure (vorg env tys Δ fuel v)
    | .bind _ _ A _ u tM tN | .effLet _ _ A _ _ u tM tN => do
      let live ← laterLive u env tys
      let o ← cw cfg f env tys Δ (cur ++ live) tM
      cw cfg f (o :: env) (some A :: tys) Δ cur tN
    | .effThen _ _ A _ _ _ _ u tM tN tD => do
      let live ← laterLive u env tys
      let o ← cw cfg f env tys Δ (cur ++ live) tM
      let _ ← cw cfg f (.unk :: env) (some .unit :: tys) Δ cur tD
      cw cfg f (o :: env) (some A :: tys) Δ cur tN
    | .sumE _ _ A B _ _ tV t₁ t₂ => do
      let o := match vorg env tys Δ fuel tV with
        | o@(.self _) => o
        | _ => .unk
      let _ ← cw cfg f (.unk :: env) (some A :: tys) Δ cur t₁
      let _ ← cw cfg f (o :: env) (some B :: tys) Δ cur t₂
      pure .unk
    | .tensorE _ _ A B _ _ tV tM => do
      let (a, b) := match vorg env tys Δ fuel tV with
        | .tup a b => (a, b)
        | _ => (.unk, .unk)
      cw cfg f (b :: a :: env) (some B :: some A :: tys) Δ cur tM
    | .unitE _ _ _ _ _ tM => cw cfg f env tys Δ cur tM
    | .effPerform i _ _ o _ => do
      if o.n == cfg.n && cfg.jst.contains o.i.toNat then
        let st ← get
        set { st with points := st.points ++ [({ sp := i.sp, live := cur, Δ, frames := st.stk.map (fun (p : Nat × String) => p.1) } : CPoint)] }
      pure .unk
    | .lam _ _ A _ b => do let _ ← cw cfg f (.unk :: env) (some A :: tys) Δ cur b; pure .unk
    | .lamDead _ _ _ _ b => do let _ ← cw cfg f (.unk :: env) (some .unit :: tys) Δ cur b; pure .unk
    | .withI _ _ _ _ tM tN => do
      let e2 := .unk :: .unk :: env
      let t2 := some .unit :: some .unit :: tys
      let _ ← cw cfg f e2 t2 Δ cur tM
      let _ ← cw cfg f e2 t2 Δ cur tN
      pure .unk
    | .nuIn _ _ _ b => do let _ ← cw cfg f env tys Δ cur b; pure .unk
    | .allI _ _ x b _ _ tM => cw cfg f (.unk :: env) (some .unit :: tys) (Δ.extend x b) cur tM
    | .effHandleV _ _ _ _ _ m _ _ _ _ _ _ tc te | .effHandleVB _ _ _ _ _ m _ _ _ _ _ _ _ tc te
    | .effHandleT _ _ _ _ _ _ m _ _ _ _ _ tc te | .effHandleL _ _ _ _ _ _ _ m _ _ _ _ _ tc te => do
      -- The clauses run at the node's outer row: each is walked once, its arguments unknown.
      for c in (vorg env tys Δ fuel tc).codes do
        let _ ← call cfg f t.info.sp c [] cur
      if m == cfg.n then pure .unk else
        let _ ← cw cfg f env tys Δ cur te
        let hasSt : Bool := match t with
          | .effHandleV _ _ _ _ _ _ _ _ _ ks .. | .effHandleVB _ _ _ _ _ _ _ _ _ _ ks .. =>
            ks.any (·.kind == .stored)
          | _ => false
        pure (if hasSt then .inner ((handleIdOf? t.info).getD "") else .unk)
    | .lendR _ _ x b _ _ _ td tM => do
      let _ ← cw cfg f [] [] Δ [] td
      let _ ← cw cfg f [.unk] [none] (Δ.extend x b) [] tM
      pure .unk
    | .lendLoopR _ _ _ _ _ _ _ tN tK ts0 => do
      let _ ← cw cfg f [.unk] [none] Δ [] tN
      let _ ← cw cfg f [.unk] [none] Δ [] tK
      let _ ← cw cfg f [] [] Δ [] ts0
      pure .unk
    | .letPoly _ _ _ _ _ tN => cw cfg f (.unk :: env) (some .unit :: tys) Δ cur tN
    | .nilDead _ _ _ t' => cw cfg f [] [] Δ [] t'
    | .walk _ _ _ _ t' | .walkGet _ _ _ t' | .lendCell _ _ _ t' | .divLit _ _ _ _ t'
    | .litFn _ _ _ t' | .nuEta _ _ _ _ t' | .selfCall _ _ _ _ t' => cw cfg f env tys Δ cur t'
    | .app .. | .proj₁ .. | .proj₂ .. | .nuOut .. | .allE .. | .force .. | .effSub .. => do
      let (h, es) := elimsOf env tys t []
      match h with
      | .force i _ g C =>
        let o := env.getD g .unk
        if ctyHas cfg.n C && !o.known then
          modify fun s => { s with opens := s.opens ++ [i.sp] }
        -- An observation of codata whose observations perform `n` (#691). Of an inner node's
        -- answer, it is a gap only if R5 leaves that node (R5-4; `crossing` reads its form).
        match C, es.head? with
        | .nu D, some .out =>
          if ctyHas cfg.n D then
            match o with
            | .inner id => modify fun s => { s with codataIn := s.codataIn ++ [(id, i.sp)] }
            | _ => modify fun s => { s with codata := s.codata ++ [i.sp] }
        | _, _ => pure ()
        call cfg f i.sp o es cur
      | .lam .. | .lamDead .. | .withI .. | .nuIn .. | .allI .. =>
        apply cfg f env tys Δ cur h es
      | _ => cw cfg f env tys Δ cur h
    | _ => pure .unk

/-- Eliminations applied to code, at its context. -/
def apply (cfg : CCfg) : Nat → List Org → List (Option VTy) → LifeCtx → List (Org × Option VTy) →
    TExpr → List Elim → CM Org
  | 0, _, _, _, _, _, _ => throw "R5 admission: code nested too deeply to apply"
  | f + 1, env, tys, Δ, cur, c, es => do
    match es, c with
    | [], c => cw cfg f env tys Δ cur c
    | .arg o _ :: es, .lam _ _ A _ b => apply cfg f (o :: env) (some A :: tys) Δ cur b es
    | .arg o _ :: es, .lamDead _ _ _ _ b => apply cfg f (o :: env) (some .unit :: tys) Δ cur b es
    | .p1 :: es, .withI _ _ _ _ tM _ =>
      apply cfg f (.unk :: .unk :: env) (some .unit :: some .unit :: tys) Δ cur tM es
    | .p2 :: es, .withI _ _ _ _ _ tN =>
      apply cfg f (.unk :: .unk :: env) (some .unit :: some .unit :: tys) Δ cur tN es
    | .out :: es, .nuIn _ _ _ b => apply cfg f env tys Δ cur b es
    | .life :: es, .allI _ _ x b _ _ tM =>
      apply cfg f (.unk :: env) (some .unit :: tys) (Δ.extend x b) cur tM es
    | es, .effSub _ _ _ _ _ t => apply cfg f env tys Δ cur t es
    -- Code reached through the binding forms of its body: the eliminations wait for it.
    | es, .tensorE _ _ A B _ _ tV tM =>
      let (a, b) := match vorg env tys Δ fuel tV with
        | .tup a b => (a, b)
        | _ => (.unk, .unk)
      apply cfg f (b :: a :: env) (some B :: some A :: tys) Δ cur tM es
    | es, .unitE _ _ _ _ _ tM => apply cfg f env tys Δ cur tM es
    | es, .bind _ _ A _ _ tM tN | es, .effLet _ _ A _ _ _ tM tN => do
      let o ← cw cfg f env tys Δ cur tM
      apply cfg f (o :: env) (some A :: tys) Δ cur tN es
    | es, .sumE _ _ A B _ _ tV t₁ t₂ => do
      let o := match vorg env tys Δ fuel tV with
        | o@(.self _) => o
        | _ => .unk
      let _ ← apply cfg f (.unk :: env) (some A :: tys) Δ cur t₁ es
      apply cfg f (o :: env) (some B :: tys) Δ cur t₂ es
    | _, c => do let _ ← cw cfg f env tys Δ cur c; pure .unk

/-- **A call of a value** with eliminations, from a caller whose live slots are `cur`: known
code runs (once per callee and arguments, the memo's), a recursive group's self-reference and
`bounded_fix` run the step, a primitive runs the code it is given; an unknown value runs nothing
the walk can see. -/
def call (cfg : CCfg) : Nat → Span → Org → List Elim → List (Org × Option VTy) → CM Org
  | 0, _, _, _, _ => throw "R5 admission: calls nested too deeply to walk"
  | f + 1, sp, o, es, cur => do
    match o with
    | .inst _ _ body env tys Δ | .code _ _ body env tys Δ =>
      let some (c, dead) := codeBody fuel body | pure .unk
      let key := o.sig ++ "|" ++ ",".intercalate (es.map fun
        | .arg a _ => a.sig
        | .p1 => ".1"
        | .p2 => ".2"
        | .out => "out"
        | .life => "∀")
      let st ← get
      let id := st.nextId
      let cyc := st.stk.any (·.2 == key)
      let memo := st.memo.lookup key
      set { st with nextId := id + 1,
                    calls := st.calls ++ [({ id, sp, callee := o.sig, live := cur, Δ, cyc, memoOf := memo } : CCall)] }
      if cyc || memo.isSome then return .unk
      modify fun s => { s with stk := (id, key) :: s.stk, memo := (key, id) :: s.memo }
      let (env', tys') := if dead then (.unk :: env, some .unit :: tys) else (env, tys)
      let r ← apply cfg f env' tys' Δ [] c es
      modify fun s => { s with stk := s.stk.drop 1 }
      pure r
    | .self s =>
      match es with
      | .arg x ty :: es' => call cfg f sp s (.arg (.tup (.self s) x) ty :: es') cur
      | _ => pure .unk
    | .fix =>
      match es with
      | .arg (.tup s (.tup _ a)) ty :: es' => call cfg f sp s (.arg (.tup (.self s) a) ty :: es') cur
      | _ => pure .unk
    | .prim _ =>
      for a in es do
        match a with
        | .arg x _ =>
          for c in x.codes do
            let _ ← call cfg f sp c [] cur
        | _ => pure ()
      pure .unk
    | _ => pure .unk

end

/-! ### The admission -/

/-- What the admission reads of a node's region, and its form. -/
structure Admit where
  node : HNode
  /-- `R5 opt`, `R5 fallback (…)` or `left: …`. -/
  form : String
  /-- The region's points, and its other performs of `n`. -/
  points : Nat := 0
  tails : Nat := 0
  /-- Its `lendR`s, and the pins at them. -/
  lends : List Span := []
  pins : List String := []
  /-- The forces of an open region (A4). -/
  opens : List Span := []
  /-- `lexical`, `flat` or `array (…)`, and the number of suspending calls. -/
  shape : String := "-"
  suspending : Nat := 0
  /-- At VB, the `U`-typed slots of the state. -/
  uslots : Nat := 0
  /-- R0 forwards through the node: its outer row holds a name R0 rewrites (the coercion `ε`). -/
  eps : Bool := false
  /-- The nodes of other names a point lies inside. -/
  crossed : List Crossed := []
  /-- The slots of `Env_N`. -/
  envN : Nat := 0
  /-- Splits whose masks and context differ in length. -/
  mismatch : Nat := 0
  /-- The node's own gap or fallback, without the crossing conjunct; `none` when it is `opt`. -/
  own : Option String := none
  /-- The node has a stored operation (A1). -/
  stored : Bool := false
  /-- Inner nodes of its name in its handled computation. -/
  inner : Nat := 0
  /-- Every gap of the scope's §3.C that holds at the node, the first its form. -/
  gaps : List String := []
  /-- The observations of codata whose observations perform `n`. -/
  codata : List Span := []
  /-- The gaps that hold if R5 leaves an inner node: its id, and the gap. -/
  cond : List (String × String) := []

instance : Inhabited Admit := ⟨{ node := default, form := "" }⟩

/-- The node's stored operations (A1). -/
def storedOps (h : HNode) : List Nat :=
  (h.ks.zipIdx.filter fun (k, _) => k.kind == .stored).map (·.2)

/-- **A9**: every node of `n` with handled value type `A` and outer row `S` has one answer type. -/
def answerCoherent (all : List HNode) (h : HNode) : Bool :=
  (all.filter fun g => g.n == h.n && decide (g.A = h.A) && decide (g.S = h.S)).all fun g =>
    decide (g.R = h.R)

/-- **The admission of one node**, before the crossing conjunct (`crossing`), from its region's
scan and call walk. `ruled` are R0's names; `pins` the program's. -/
def admitNode (all : List HNode) (ruled : List UInt32) (pins : Frontend.Check.Pins) (h : HNode) :
    Except String Admit := do
  let jst := storedOps h
  if jst.isEmpty then
    return { node := h, form := s!"left: {siblingRows h.kind h.ks}" }
  let sc ← regionScan h.n jst ruled fuel [] false h.te {}
  let (_, ca) ← (cw ⟨h.n, jst⟩ fuel h.env h.tys h.Δ [] h.te).run {}
  -- Suspending calls: a point reached under them, or the memo's walk did.
  let under (id : Nat) : Bool := ca.points.any (·.frames.contains id)
  let reach (c : CCall) : Bool := under c.id || (c.memoOf.map under).getD false ||
    (c.cyc && ca.calls.any fun c' => c'.callee == c.callee && under c'.id)
  let susp := ca.calls.filter reach
  let shape :=
    if susp.isEmpty then "lexical"
    else if susp.any (·.cyc) then "array (recursive)"
    else if susp.any (fun c => (susp.filter (·.callee == c.callee)).length > 1) then "array (shared)"
    else "flat"
  -- `Env_N`: the slots the clauses use, at the node's context. A8, their persistence, is the
  -- rule's premise at every node of a checked term (`TDerivesP.handleV_env_persistent`,
  -- `TDerivesP.handleVB_env_persistent`); it is not decided here.
  let env : List (Org × Option VTy) := match h.u with
    | some u => (u.ms.zip (h.env.zip h.tys)).filterMap fun ((a, _), sl) => if a then some sl else none
    | none => []
  -- The slots of the state `Q_N`: the live slots of each point and of each suspending call's
  -- frame, and `Env_N`. An inner node's answer is held as its state when R5 admits that node
  -- (R5-4), so its slot is a gap only if R5 leaves it (`crossing` reads its form).
  let slots : List ((Org × Option VTy) × LifeCtx) :=
    (ca.points.flatMap fun p => p.live.map (·, p.Δ)) ++ (susp.flatMap fun c => c.live.map (·, c.Δ)) ++
      env.map (·, h.Δ)
  let innerOf : Org → Option String := fun
    | .inner id => some id
    | _ => none
  -- A6, at VB: every slot of the state outlives `d`.
  let bad : List ((Org × Option VTy) × LifeCtx) := match h.d with
    | none => []
    | some d => slots.filter fun ((_, ty), Δ) => match ty with
        | some A => !outlivesB Δ d A
        | none => true
  let slotName : Option VTy → String := fun
    | some A => vHead A
    | none => "?"
  let a6 : List String := (bad.filter fun ((o, _), _) => (innerOf o).isNone).map fun ((_, ty), _) =>
    slotName ty
  let a6In : List (String × String) := bad.filterMap fun ((o, ty), _) =>
    (innerOf o).map (·, s!"state does not outlive d (slot {slotName ty})")
  let slots := slots.filter fun ((o, _), _) => (innerOf o).isNone
  let uslots := match h.d with
    | none => 0
    | some _ => (slots.filter fun ((_, ty), _) => match ty with
        | some (.thunk _) => true
        | _ => false).length
  let pinsAt := sc.lends.filterMap fun sp =>
    (pins.find? fun p => p.line == sp.start.line && p.col == sp.start.col).map fun p =>
      s!"{p.rule} at {p.line}:{p.col}"
  let base : Admit :=
    { node := h
      form := ""
      points := sc.points.length
      tails := sc.tails
      lends := sc.lends
      pins := pinsAt
      opens := ca.opens
      shape := shape
      suspending := susp.length
      uslots := uslots
      eps := h.S.any (fun o => ruled.contains o.n)
      crossed := sc.points.flatMap (·.crossed)
      envN := env.length
      codata := ca.codata
      cond := (ca.codataIn.map fun (id, sp) => (id, s!"codata at row n (#691, at {spStr sp})")) ++ a6In
      mismatch := ca.mismatch
      stored := true
      inner := sc.inner }
  -- The gaps (left), every one that holds: `lendR` first (OQ1: a node whose region holds one is
  -- left with its pin position, whatever else holds), then the scope's §3.C order.
  let gaps : List String :=
    (sc.lends.head?.map fun sp => s!"lendR (T1, PinLaw.stop at {spStr sp})").toList ++
    (ca.codata.head?.map fun sp => s!"codata at row n (#691, at {spStr sp})").toList ++
    (if !ca.opens.isEmpty && !answerCoherent all h then ["answer types differ at n (#692)"] else []) ++
    (if h.n == BoCa.divEff || !sc.divs.isEmpty then
      [s!"div region ({", ".intercalate (if h.n == BoCa.divEff then ["the name is Div"] else sc.divs)})"]
     else []) ++
    (a6.head?.map fun x => s!"state does not outlive d (slot {x})").toList ++
    (if sc.points.any (·.finPerf) then ["a finaliser that performs"] else [])
  let base := { base with gaps := gaps }
  if let some g := gaps.head? then
    return { base with form := s!"left: {g}", own := some s!"left: {g}" }
  -- The fallback's conjuncts.
  let a2 := (h.ks.zipIdx.filter fun (k, _) =>
    k.kind != .abortive && k.kind != .stored && k.kind != .tail).map fun (k, j) =>
      s!"A2: in-clause {k.kind.tag} at {h.n}.{j}"
  let a3 := (jst.filter fun j => (h.sshape.getD j none).isNone).map fun j =>
    s!"A3: κ not at X at {h.n}.{j}"
  let a4 := (ca.opens.head?.map fun sp => s!"A4: open region, force at {spStr sp}").toList
  match a2 ++ a3 ++ a4 with
  | [] => return { base with form := "R5 opt", own := some "R5 opt" }
  | rs => return { base with form := s!"R5 fallback ({"; ".intercalate rs})",
                              own := some s!"R5 fallback ({"; ".intercalate rs})" }

/-- **The forms that depend on other nodes' forms**, read to a fixed point, each node matched by its
id (`numberHandles`):
* an inner stored node's answer, observed as codata whose observations perform `n` or held in a
  boxed state that it does not outlive, is a gap of the outer node only if R5 leaves the inner
  node (R5-4 holds an admitted inner node's answer as its state);
* **the crossing conjunct**: a stored node one of whose points lies in the handled computation of
  a node of another name that R0, R1 and R5 do not rewrite (a node with no stored operation, or a
  stored node left) is left, whole.

It starts from every node's own form and only leaves nodes, so it ends. -/
def crossing (as : List Admit) : List Admit := Id.run do
  let mut cur := as
  for _ in [0:as.length + 1] do
    let leftId : String → Bool := fun id =>
      match cur.find? (fun (a : Admit) => a.stored && a.node.id == id) with
      | some a => a.form.startsWith "left"
      | none => true
    -- A crossed node with no stored operation stays in Backend2 until its sibling row lands; a
    -- stored one, when its admission leaves it.
    let rewritten (c : Crossed) : Option String :=
      if !c.stored then some c.row else if leftId c.id then some "R5 left" else none
    let next := cur.map fun a =>
      if !a.stored || (a.own.map (·.startsWith "left")).getD false then a else
      match a.cond.find? (fun (id, _) => leftId id) with
      | some (_, g) => { a with form := s!"left: {g}", gaps := a.gaps ++ [g] }
      | none =>
      match a.crossed.findSome? fun c => (rewritten c).map (c.m, ·) with
      | some (m, row) => { a with form := s!"left: perform path crosses handler {m} ({row}, in Backend2)" }
      | none => { a with form := a.own.getD "R5 opt" }
    if next.map (·.form) == cur.map (·.form) then return next
    cur := next
  return cur

/-- **R5's admission of a checked program**: every `handle` node with an operation R0 does not
rewrite (`ruled` are R0's names), its form and what the admission read. -/
def admission (c : Frontend.Check.Checked) (ruled : List UInt32) : Except String (List Admit) := do
  let env0 : List Org := c.ctx.map fun _ => .unk
  let tys0 : List (Option VTy) := c.ctx.map fun s => some s.ty
  -- Every node given its id, so that nodes are matched by id, never by span.
  let t ← numberHandles c.t
  let (_, nodes) ← discover fuel env0 tys0 ⟨[]⟩ t ([], [])
  let ids := nodes.map (·.id)
  if ids.any (· == "") || ids.eraseDups.length != ids.length then
    throw "R5 admission: the numbering gives two handle nodes one id, or a node none"
  let nodes := nodes.filter fun h => !(h.E.all isAbortive)
  let as ← nodes.mapM (admitNode nodes ruled c.pins)
  pure (crossing as)

/-- **R5's admission of a checked program**, R0's names read from its keys (`r0Keys`). -/
def admissionOf (c : Frontend.Check.Checked) : Except String (List Admit) := do
  let keys ← r0Keys c fuel
  admission c (keys.filterMap fun (a, s) => if s == .rewritten then some a.n else none)

/-- **The compact form of an admission**, for the rewriter's line (`corpus/rewrite.expected`): the
node's position and name, then `opt`, `fallback(<conjuncts>)` or `left:<conjunct>`, the
conjunct by its tag (the detailed line, `bcc rewrite --admission`, gives its text). -/
def Admit.short (a : Admit) : String :=
  let f := a.form
  let tag : String :=
    if f == "R5 opt" then "opt"
    else if f.startsWith "R5 fallback (" then
      let cs := (((f.drop 13).dropEnd 1).toString.splitOn "; ").map fun c => (c.take 2).toString
      "fallback(" ++ ",".intercalate cs.eraseDups ++ ")"
    else if f.startsWith "left: lendR" then
      "left:lendR@" ++ ((a.lends.head?.map spStr).getD "?")
    else if f.startsWith "left: codata" then "left:#691"
    else if f.startsWith "left: answer types" then "left:#692"
    else if f.startsWith "left: div region" then "left:div"
    else if f.startsWith "left: state does not outlive" then "left:A6"
    else if f.startsWith "left: a finaliser" then "left:fin"
    else if f.startsWith "left: perform path crosses handler " then
      "left:crossing(" ++ (((f.drop 35).toString.splitOn " ").headD "?") ++ ")"
    else "left:" ++ ((f.drop 6).toString.replace ", " "+")
  s!"{spStr a.node.sp}/{a.node.n}={tag}"

/-- **R5's field of the rewriter's line**: each node's compact admission (`Admit.short`), in the
admission's order; empty at a program with no such node. -/
def admissionField (c : Frontend.Check.Checked) : Except String String := do
  let as ← admissionOf c
  pure (if as.isEmpty then "" else " R5 " ++ " ".intercalate (as.map Admit.short))

/-- The admission's detailed line for one node (`bcc rewrite --admission`). -/
def Admit.line (a : Admit) : String :=
  let h := a.node
  if !a.stored then s!"{spStr h.sp} {h.n} {h.kind} {a.form}" else
  let pins := if a.pins.isEmpty then "" else s!" pins [{", ".intercalate a.pins}]"
  let opens := if a.opens.isEmpty then "" else
    s!" opens [{", ".intercalate (a.opens.map spStr)}]"
  let mm := if a.mismatch == 0 then "" else s!" ctx-mismatch {a.mismatch}"
  let also := if a.gaps.length ≤ 1 then "" else s!" also [{"; ".intercalate (a.gaps.drop 1)}]"
  s!"{spStr h.sp} {h.n} {h.kind} {a.form} | points {a.points} tails {a.tails} shape {a.shape}" ++
    s!" suspending {a.suspending} env {a.envN} uslots {a.uslots} eps {if a.eps then "yes" else "no"}" ++
    s!" inner {a.inner}{pins}{opens}{also}{mm}"

end Rewrite
