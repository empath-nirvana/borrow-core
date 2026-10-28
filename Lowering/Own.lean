import Lowering.Rename
import Lowering.NoRelaxed

/-!
# Lowering — explicit ownership: `own`  `[spec §54]`

`own : TExpr → Expr` lowers a checked term into the low subset (`Lowering/Low.lean`): every copy
and every drop the kernel leaves implicit is written as a constant of the kernel, `copy` or
`forget`. It reads them off the typed term; it never counts a variable's occurrences.

The kernel leaves two operations implicit, both at a persistent slot (SPEC §10), whose value holds
no resource:

- **a copy** at a split (`Ctx.SplitP.dup`): a slot both parts of a node receive. The typed node
  records the parts' use masks (`TExpr.masks?`), and the slots both masks hold are exactly the
  slots the split gives to both parts, each live at a persistent type (`TDerivesP.copies`). `own`
  copies those (`copiesE`): `let (x₁, x₂) = copy x in …`, the first part reading `x₁` and the
  second `x₂` (`ren`).
- **a drop** at a leaf (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`): a live slot a leaf is given and does
  not use. `own` carries the node's live slots `L` down the term (`part`: a part receives the live
  slots its mask holds), drops at a split a live slot neither mask holds, and drops at a leaf every
  live slot but the one it reads (`leafE`), each by `forget x; …` (`dropE`).

Every other drop is already explicit: a value that owns a resource is consumed by the program,
through its destructor where the program drops it (`dtor`, `dtor_wf`). A binder the kernel types
dead, the `()` a thunk of `F A` or a `Λ` is forced with, is consumed by `(); …` (`seq`).

`own` lowers the nodes of the pure fragment (`pureT`): the CBPV rules, the value-level rules,
the coercions and the derived nodes, each node for node. A constant is its erasure, its context's
live slots dropped. The effect nodes (§19, `iterate`, `divFuel`, `reify`), the unwinding borrows,
`[let-poly]` and `[λ-dead]` are left as their erasures, and a term with a relaxed rule is left
whole: U3 and U4 lower them. `zeroE` is written `absurdL`, the low subset's `absurd`.
-/

namespace Lowering
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Check

/-! ### Live slots -/

/-- Whether slot `k` of `L` is live. -/
def lv (L : List Bool) (k : Nat) : Bool := L.getD k false

/-- The live slots of `L`, in order. -/
def liveIdx (L : List Bool) : List Nat := (List.range L.length).filter (lv L)

/-- The live slots of `L` a part receives: those its mask `u` holds. -/
def part (L : List Bool) (u : Nat → Bool) : List Bool :=
  (List.range L.length).map fun k => lv L k && u k

/-- A mask as a predicate on slots. -/
def mk (u : List Bool) (k : Nat) : Bool := u.getD k false

/-! ### Drops and copies -/

/-- `forget x; e`: the value at slot `k` dropped. -/
def dropE (k : Nat) (e : Expr) : Expr := .seq (.app forget (.var k)) e

/-- The values at the slots `ks` dropped, in order. -/
def dropsE (ks : List Nat) (e : Expr) : Expr := ks.foldr dropE e

/-- A leaf reading the slot `keep` (or none): every other live slot of `L` dropped. -/
def leafE (L : List Bool) (keep : Option Nat) (e : Expr) : Expr :=
  dropsE ((liveIdx L).filter fun k => some k != keep) e

/-- A node at a split, given the renamings of its two parts' variables. -/
abbrev Node := (Nat → Nat) → (Nat → Nat) → Expr

/-- After a copy of slot `k`: the first part reads `x₁` (`1`), every other slot moves past the
two new binders. -/
def cpL (k i : Nat) : Nat := if i = k then 1 else i + 2

/-- After a copy of slot `k`: the second part reads `x₂` (`0`). -/
def cpR (k i : Nat) : Nat := if i = k then 0 else i + 2

/-- The copies of the slots `ks` (at the offset `off` the copies before them have moved them by):
`let (x₁, x₂) = copy x in …` for each, the node's parts renamed to read their own copies. -/
def copiesE (off : Nat) : List Nat → Node → Expr
  | [], F => F id id
  | k :: ks, F => .letpair (.app copy (.var (k + off)))
      (copiesE (off + 2) ks fun r₁ r₂ => F (r₁ ∘ cpL (k + off)) (r₂ ∘ cpR (k + off)))

/-- **A node at a split**, at the live slots `L` and the parts' masks `u₁`, `u₂`: the live slots
neither part receives dropped, the slots both receive copied, then the node. -/
def splitE (L : List Bool) (u₁ u₂ : Nat → Bool) (F : Node) : Expr :=
  dropsE ((liveIdx L).filter fun k => !u₁ k && !u₂ k)
    (copiesE 0 ((liveIdx L).filter fun k => u₁ k && u₂ k) F)

/-- The mask of `M x`'s second part: its argument `x`, as its mask holds it. -/
def argMask (i : Nat) (u : List Bool) (k : Nat) : Bool := k == i && mk u k

/-! ### `own` -/

/-- **Explicit ownership**: the term at the live slots `L` of its context, every copy and every
drop written. -/
def ownAt : List Bool → TExpr → Expr
  | L, .var _ _ i _ => leafE L (some i) (.var i)
  | L, .unitI _ _ => leafE L none (.val .unit)
  | L, .tensorI _ _ _ _ u t₁ t₂ =>
      splitE L (mk u.u₁) (mk u.u₂) fun r₁ r₂ =>
        .pair (ren r₁ (ownAt (part L (mk u.u₁)) t₁)) (ren r₂ (ownAt (part L (mk u.u₂)) t₂))
  | L, .sumI₁ _ _ _ _ t => .inj₁ (ownAt L t)
  | L, .sumI₂ _ _ _ _ t => .inj₂ (ownAt L t)
  | L, .thunkF _ _ _ t => .lam (.seq (.var 0) (ownAt (false :: L) t))
  | L, .thunkV _ _ _ t => match ownAt L t with
      | .lam N => .lam N
      | _ => t.erase
  | L, .ret _ _ _ t => ownAt L t
  | L, .bind _ _ _ _ u tM tN =>
      splitE L (mk u.u₁) (mk u.u₂) fun r₁ r₂ =>
        .app (.lam (ren (liftR r₂) (ownAt (true :: part L (mk u.u₂)) tN)))
          (ren r₁ (ownAt (part L (mk u.u₁)) tM))
  | L, .force _ _ i C => leafE L (some i) (forceE C (.var i))
  | L, .lam _ _ _ _ t => .lam (ownAt (true :: L) t)
  | L, .app _ _ i _ _ u tM =>
      splitE L (mk u.u₁) (argMask i u.u₂) fun r₁ r₂ =>
        .app (ren r₁ (ownAt (part L (mk u.u₁)) tM)) (ren r₂ (.var i))
  | L, .withI _ _ _ _ tM tN =>
      withPair (ownAt (false :: false :: L) tM) (ownAt (false :: false :: L) tN)
  | L, .proj₁ _ _ _ _ t => .app (ownAt L t) (.val (.inj₁ .unit))
  | L, .proj₂ _ _ _ _ t => .app (ownAt L t) (.val (.inj₂ .unit))
  | L, .topI _ _ => leafE L none (.val .unit)
  | L, .unitE _ _ _ u tV tM =>
      splitE L (mk u.u₁) (mk u.u₂) fun r₁ r₂ =>
        .seq (ren r₁ (ownAt (part L (mk u.u₁)) tV)) (ren r₂ (ownAt (part L (mk u.u₂)) tM))
  | L, .tensorE _ _ _ _ _ u tV tM =>
      splitE L (mk u.u₁) (mk u.u₂) fun r₁ r₂ =>
        .letpair (ren r₁ (ownAt (part L (mk u.u₁)) tV))
          (ren (liftR (liftR r₂)) (ownAt (true :: true :: part L (mk u.u₂)) tM))
  | L, .sumE _ _ _ _ _ u tV t₁ t₂ =>
      splitE L (mk u.u₁) (mk u.u₂) fun r₁ r₂ =>
        .case (ren r₁ (ownAt (part L (mk u.u₁)) tV))
          (ren (liftR r₂) (ownAt (true :: part L (mk u.u₂)) t₁))
          (ren (liftR r₂) (ownAt (true :: part L (mk u.u₂)) t₂))
  | L, .zeroE _ _ _ u tV =>
      splitE L (mk u.u₁) (fun _ => false) fun r₁ _ =>
        absurdL (ren r₁ (ownAt (part L (mk u.u₁)) tV))
  | L, .allI _ _ _ _ _ _ t => .lam (.seq (.var 0) (ownAt (false :: L) t))
  | L, .allE _ _ _ _ _ _ t => .app (ownAt L t) (.val .unit)
  | L, .bangThunkF _ _ _ t => .lam (.seq (.var 0) (ownAt (false :: L) t))
  | L, .bangThunkV _ _ _ t => match ownAt L t with
      | .lam N => .lam N
      | _ => t.erase
  | L, .bangE _ _ _ t => ownAt L t
  | L, .boxI _ _ _ _ t => ownAt L t
  | L, .boxE _ _ _ _ t => ownAt L t
  | L, .immSub _ _ _ _ _ t => ownAt L t
  | L, .mutSub _ _ _ _ _ t => ownAt L t
  | L, .lolliE _ _ _ _ u ta tf =>
      splitE L (mk u.u₁) (mk u.u₂) fun r₁ r₂ =>
        .app (ren r₂ (ownAt (part L (mk u.u₂)) tf)) (ren r₁ (ownAt (part L (mk u.u₁)) ta))
  | L, .allEV _ _ _ _ _ _ t => .app (ownAt L t) (.val .unit)
  | L, .ofRet _ _ _ t => ownAt L t
  | L, .roll _ _ _ t => ownAt L t
  | L, .unroll _ _ _ t => ownAt L t
  | L, .nuIn _ _ _ t => ownAt L t
  | L, .nuOut _ _ _ t => ownAt L t
  | L, .litFn _ _ _ t => ownAt L t
  | L, .divLit _ _ _ _ t => ownAt L t
  | L, .walk _ _ _ _ t => ownAt L t
  | L, .walkGet _ _ _ t => ownAt L t
  | L, .selfCall _ _ _ _ t => ownAt L t
  | L, .lendCell _ _ _ t => ownAt L t
  | L, .nuEta _ _ _ _ t => ownAt L t
  | L, .lendScope _ _ _ t => ownAt L t
  | L, .litView _ _ t => ownAt L t
  | L, .unfoldStep _ _ t => ownAt L t
  | L, .use _ _ _ _ _ _ t => ownAt L t
  | L, t => if constNode t then leafE L none t.erase else t.erase

/-! ### The pure fragment -/

/-- **The pure fragment**: every node one `own` lowers node for node, and every constant free of
effect primitives (`effFreeB`). The effect nodes, the unwinding borrows, the relaxed rules and
`[let-poly]` are outside it. -/
def pureT : TExpr → Bool
  | .var .. | .unitI .. | .force .. | .topI .. => true
  | .tensorI _ _ _ _ _ t₁ t₂ | .bind _ _ _ _ _ t₁ t₂ | .withI _ _ _ _ t₁ t₂
  | .unitE _ _ _ _ t₁ t₂ | .tensorE _ _ _ _ _ _ t₁ t₂ | .lolliE _ _ _ _ _ t₁ t₂ =>
      pureT t₁ && pureT t₂
  | .sumE _ _ _ _ _ _ tV t₁ t₂ => pureT tV && pureT t₁ && pureT t₂
  | .sumI₁ _ _ _ _ t | .sumI₂ _ _ _ _ t | .thunkF _ _ _ t | .thunkV _ _ _ t | .ret _ _ _ t
  | .lam _ _ _ _ t | .app _ _ _ _ _ _ t | .proj₁ _ _ _ _ t | .proj₂ _ _ _ _ t | .zeroE _ _ _ _ t
  | .allI _ _ _ _ _ _ t | .allE _ _ _ _ _ _ t | .bangThunkF _ _ _ t | .bangThunkV _ _ _ t
  | .bangE _ _ _ t | .boxI _ _ _ _ t | .boxE _ _ _ _ t | .immSub _ _ _ _ _ t | .mutSub _ _ _ _ _ t
  | .allEV _ _ _ _ _ _ t | .ofRet _ _ _ t | .roll _ _ _ t | .unroll _ _ _ t | .nuIn _ _ _ t
  | .nuOut _ _ _ t | .litFn _ _ _ t | .divLit _ _ _ _ t | .walk _ _ _ _ t | .walkGet _ _ _ t
  | .selfCall _ _ _ _ t | .lendCell _ _ _ t | .nuEta _ _ _ _ t | .use _ _ _ _ _ _ t
  | .lendScope _ _ _ t | .litView _ _ t | .unfoldStep _ _ t => pureT t
  | t => constNode t && effFreeB t.erase

/-! ### Masks that agree with the leaves -/

/-- **The masks agree with the leaves**: along `own`'s flow of live slots, every variable a leaf
reads (`var`, `force`, `M x`'s argument) is live where it is read. Every typed term of the pure
fragment has it (`agreeAt_of_typed`, `Lowering/OwnLow.lean`): a split's masks cover its parts
(`Covers`). -/
def agreeAt : List Bool → TExpr → Bool
  | L, .var _ _ i _ => lv L i
  | L, .force _ _ i _ => lv L i
  | L, .tensorI _ _ _ _ u t₁ t₂ | L, .unitE _ _ _ u t₁ t₂ | L, .lolliE _ _ _ _ u t₁ t₂ =>
      agreeAt (part L (mk u.u₁)) t₁ && agreeAt (part L (mk u.u₂)) t₂
  | L, .bind _ _ _ _ u tM tN =>
      agreeAt (part L (mk u.u₁)) tM && agreeAt (true :: part L (mk u.u₂)) tN
  | L, .tensorE _ _ _ _ _ u tV tM =>
      agreeAt (part L (mk u.u₁)) tV && agreeAt (true :: true :: part L (mk u.u₂)) tM
  | L, .sumE _ _ _ _ _ u tV t₁ t₂ =>
      agreeAt (part L (mk u.u₁)) tV && agreeAt (true :: part L (mk u.u₂)) t₁ &&
        agreeAt (true :: part L (mk u.u₂)) t₂
  | L, .zeroE _ _ _ u tV => agreeAt (part L (mk u.u₁)) tV
  | L, .app _ _ i _ _ u tM => agreeAt (part L (mk u.u₁)) tM && lv L i && mk u.u₂ i
  | L, .withI _ _ _ _ tM tN =>
      agreeAt (false :: false :: L) tM && agreeAt (false :: false :: L) tN
  | L, .thunkF _ _ _ t | L, .allI _ _ _ _ _ _ t | L, .bangThunkF _ _ _ t => agreeAt (false :: L) t
  | L, .lam _ _ _ _ t => agreeAt (true :: L) t
  | L, .thunkV _ _ _ t | L, .bangThunkV _ _ _ t
  | L, .sumI₁ _ _ _ _ t | L, .sumI₂ _ _ _ _ t | L, .ret _ _ _ t | L, .proj₁ _ _ _ _ t
  | L, .proj₂ _ _ _ _ t | L, .allE _ _ _ _ _ _ t | L, .bangE _ _ _ t | L, .boxI _ _ _ _ t
  | L, .boxE _ _ _ _ t | L, .immSub _ _ _ _ _ t | L, .mutSub _ _ _ _ _ t
  | L, .allEV _ _ _ _ _ _ t | L, .ofRet _ _ _ t | L, .roll _ _ _ t | L, .unroll _ _ _ t
  | L, .nuIn _ _ _ t | L, .nuOut _ _ _ t | L, .litFn _ _ _ t | L, .divLit _ _ _ _ t
  | L, .walk _ _ _ _ t | L, .walkGet _ _ _ t | L, .selfCall _ _ _ _ t | L, .lendCell _ _ _ t
  | L, .nuEta _ _ _ _ t | L, .use _ _ _ _ _ _ t | L, .lendScope _ _ _ t | L, .litView _ _ t
  | L, .unfoldStep _ _ t => agreeAt L t
  | _, _ => true

/-- **`own`**: `main` at no live slot of its own (`[spec §54]`). A term that uses a relaxed rule
(SPEC §29) is left as its erasure: its relation rests on `PinLaw`, whose `PinStop` takes the
lend's callback as a `CDerivesP` derivation, which `own`'s output is not (U4). -/
def own (t : TExpr) : Expr := if relaxedFree t then ownAt [] t else t.erase

end Lowering
