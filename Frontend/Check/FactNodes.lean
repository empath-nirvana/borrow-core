import Frontend.Check.TShift

/-!
# Frontend — Check — the facts a backend reads off derived nodes  `[spec §57]`

Four facts the backend used to rebuild from its own IR (`docs/compiler.md` §10), each the premise
of a derived node's typed rule (`Frontend/Check/TDerives.lean`), so that a derivation fixes it:

* **A lend's kind** (`lendKindB`): a `lendCell` node's `m` is the kind of the borrow constant at
  the head of its term, `withbor2` (`mut`) or `withbor1` (`imm`). The erasure cannot say it:
  both erase to `withbor`.
* **A lent cell's release** (`lendScopeT`, `lendRelB`): a `lendScope` node is over the code that
  takes apart the pair a `lendCell` node answers; its `rel` says whether, on every path of that
  code, the owner (the pair's first component) is released by `free` where it is used, and used
  nowhere else (`relAt`). A `case` is two paths, each of which must release it.
* **A literal's view** (`litViewT`): a `litView` node is over the elaborator's scheme for
  `borrow imm "…" { v -> S }`: the literal's table tabulated into an array (`array_new`), the
  array lent as an `imm` family (`slice_borrow_imm`), and the array the lend hands back
  destroyed (`dtor`) before anything else. Between the tabulation and the destruction the array
  is reached only through the `imm` family.
* **`unfold step`** (`unfoldAppT`): an `unfoldStep` node is over the `unfoldN` constant applied to
  its step. A `bind` whose bound computation is one binds a variable to `unfold step`, which is
  what a `nuEta` node needs of its `f` (SPEC §45).

Each predicate is of the node's own typed term (or its erasure), and is kept by the moves of a
typed term to a wider context (`TExpr.shift`): the `_shift` lemmas, read by
`Frontend/Check/Weaken.lean`.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.ClauseKinds (mentions)

/-! ### Node shapes -/

/-- The node is the variable `k`. -/
def TExpr.isVarT (k : Nat) : TExpr → Bool
  | .var _ _ i _ => i == k
  | _ => false

/-- The node is a `lendCell` node. -/
def TExpr.isLendCell : TExpr → Bool
  | .lendCell .. => true
  | _ => false

/-- `return` of a `lendCell` node. -/
def retLendT : TExpr → Bool
  | .ret _ _ _ t => t.isLendCell
  | _ => false

/-- `[⊗E]` of the variable `0`. -/
def pairOf0T : TExpr → Bool
  | .tensorE _ _ _ _ _ _ tV _ => tV.isVarT 0
  | _ => false

/-- **A lent cell's scope**: `[⊗E]` of a `lendCell` node, or `[let]` of `return` of one whose body
is `[⊗E]` of its variable. -/
def lendScopeT : TExpr → Bool
  | .tensorE _ _ _ _ _ _ tV _ => tV.isLendCell
  | .bind _ _ _ _ _ tM tN => retLendT tM && pairOf0T tN
  | .effLet _ _ _ _ _ _ tM tN => retLendT tM && pairOf0T tN
  | _ => false

/-- The kind of a borrow constant's node: `mut` at `withbor2`, `imm` at `withbor1`, and their
unwinding forms. -/
def TExpr.lendKind? : TExpr → Option Bool
  | .withbor1 .. | .withbor1U .. => some false
  | .withbor2 .. | .withbor2U .. => some true
  | _ => none

/-- **A lend's kind**: the term is `C cell cb` with `C` a borrow constant of kind `m`. -/
def lendKindB (m : Bool) : TExpr → Bool
  | .lolliE _ _ _ _ _ _ (.lolliE _ _ _ _ _ _ h) => h.lendKind? == some m
  | _ => false

/-- `return` of `array_new` applied. -/
def tabT : TExpr → Bool
  | .ret _ _ _ (.lolliE _ _ _ _ _ _ (.bangE _ _ _ (.arrNew ..))) => true
  | _ => false

/-- `return` of `slice_borrow_imm` applied to the variable `0` and a callback. -/
def immLendT : TExpr → Bool
  | .ret _ _ _ (.lolliE _ _ _ _ _ _ (.lolliE _ _ _ _ _ x (.sliceBorrowI ..))) => x.isVarT 0
  | _ => false

/-- The destructor applied to the variable `1`. -/
def dtorOf1T : TExpr → Bool
  | .lolliE _ _ _ _ _ x (.dtor ..) => x.isVarT 1
  | _ => false

/-- The view's body: `a <- array_new …; r <- slice_borrow_imm a cb; let (a', v) = r;
dtor a'; …`. -/
def litBodyT : TExpr → Bool
  | .bind _ _ _ _ _ tA (.bind _ _ _ _ _ tL (.tensorE _ _ _ _ _ _ tP (.unitE _ _ _ _ tD _))) =>
      tabT tA && immLendT tL && tP.isVarT 0 && dtorOf1T tD
  | _ => false

/-- **A literal's view**: `p <- return lit; let (n, t) = p; …`, the body `litBodyT`. -/
def litViewT : TExpr → Bool
  | .ofRet _ _ _ (.bind _ _ _ _ _ _ (.tensorE _ _ _ _ _ _ tV tB)) => tV.isVarT 0 && litBodyT tB
  | _ => false

/-- The node is the `unfoldN` constant. -/
def TExpr.isUnfoldN : TExpr → Bool
  | .unfoldN .. => true
  | _ => false

/-- **`unfold step`**: the `unfoldN` constant applied, through `return`, `unbang` and `ofRet`. -/
def unfoldAppT : TExpr → Bool
  | .lolliE _ _ _ _ _ _ tf => tf.isUnfoldN
  | .ret _ _ _ t | .bangE _ _ _ t | .ofRet _ _ _ t => unfoldAppT t
  | _ => false

/-! ### A lent cell's release -/

/-- The slot `k`'s pair in a split's masks: whether each part uses it (`false` past their end). -/
def Masks.at (m : Masks) (k : Nat) : Bool × Bool := m.ms.getD k (false, false)

/-- The node releases a cell: `free`, or the destructor of a cell. -/
def TExpr.isRelease : TExpr → Bool
  | .free .. => true
  | .dtor _ _ (.ref _) => true
  | _ => false

/-- **The slot `k` is released on every path of the node**: each path passes it, by the masks of
its splits, to one part, until it is the operand of `free` or of a cell's destructor (`isRelease`);
a `case` passes it to both arms, each of which must release it. Any other use (a return, a call,
a capture, a field of a value) is not a release.  `[spec §57]` -/
def relT (k : Nat) : TExpr → Bool
  | .lolliE _ _ _ _ _ ta tf => ta.isVarT k && tf.isRelease
  | .ret _ _ _ t | .ofRet _ _ _ t | .effSub _ _ _ _ _ t | .lendScope _ _ _ t | .sumI₁ _ _ _ _ t
  | .sumI₂ _ _ _ _ t => relT k t
  | .bind _ _ _ _ u tM tN | .effLet _ _ _ _ _ u tM tN =>
    match u.at k with
    | (true, false) => relT k tM
    | (false, true) => relT (k + 1) tN
    | _ => false
  | .unitE _ _ _ u tV tM | .tensorI _ _ _ _ u tV tM =>
    match u.at k with
    | (true, false) => relT k tV
    | (false, true) => relT k tM
    | _ => false
  | .sumE _ _ _ _ _ u _ t₁ t₂ => u.at k == (false, true) && relT (k + 1) t₁ && relT (k + 1) t₂
  | .tensorE _ _ _ _ _ u _ tM => u.at k == (false, true) && relT (k + 2) tM
  | .effThen _ _ _ _ _ _ _ u tM tN tD =>
    match u.at k with
    | (true, false) => relT k tM
    | (false, true) => relT (k + 1) tN && relT (k + 1) tD
    | _ => false
  | _ => false

/-- **A lent cell's scope is released**: the code after a `lendScope` node's pair is taken apart
releases the owner, its slot `1` there, on every path (`relT`). -/
def lendRelT : TExpr → Bool
  | .tensorE _ _ _ _ _ _ _ tM => relT 1 tM
  | .bind _ _ _ _ _ _ tN | .effLet _ _ _ _ _ _ _ tN => match tN with
    | .tensorE _ _ _ _ _ _ _ tM => relT 1 tM
    | _ => false
  | _ => false

/-! ### Kept at a wider context -/

theorem TExpr.isVarT_shift {d c k : Nat} (hk : k < c) (t : TExpr) :
    (t.shift d c).isVarT k = t.isVarT k := by
  cases t <;> simp only [TExpr.shift, TExpr.isVarT]
  unfold sIdx; split <;> simp <;> omega

theorem TExpr.isLendCell_shift (d c : Nat) (t : TExpr) : (t.shift d c).isLendCell = t.isLendCell := by
  cases t <;> rfl

theorem TExpr.lendKind?_shift (d c : Nat) (t : TExpr) : (t.shift d c).lendKind? = t.lendKind? := by
  cases t <;> rfl

theorem retLendT_shift (d c : Nat) (t : TExpr) : retLendT (t.shift d c) = retLendT t := by
  cases t <;> simp only [TExpr.shift, retLendT, TExpr.isLendCell_shift]

theorem pairOf0T_shift {d c : Nat} (hc : 0 < c) (t : TExpr) : pairOf0T (t.shift d c) = pairOf0T t := by
  cases t <;> simp only [TExpr.shift, pairOf0T, TExpr.isVarT_shift hc]

theorem lendScopeT_shift (d c : Nat) (t : TExpr) : lendScopeT (t.shift d c) = lendScopeT t := by
  cases t <;> simp only [TExpr.shift, lendScopeT, TExpr.isLendCell_shift, retLendT_shift,
    pairOf0T_shift (Nat.succ_pos c)]

theorem lendKindB_shift (m : Bool) (d c : Nat) (t : TExpr) : lendKindB m (t.shift d c) = lendKindB m t := by
  cases t with
  | lolliE _ _ _ _ _ _ tf => cases tf <;> simp only [TExpr.shift, lendKindB, TExpr.lendKind?_shift]
  | _ => rfl

theorem tabT_shift (d c : Nat) (t : TExpr) : tabT (t.shift d c) = tabT t := by
  cases t with
  | ret _ _ _ t =>
    cases t with
    | lolliE _ _ _ _ _ _ tf =>
      cases tf with
      | bangE _ _ _ t => cases t <;> rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem immLendT_shift {d c : Nat} (hc : 0 < c) (t : TExpr) : immLendT (t.shift d c) = immLendT t := by
  cases t with
  | ret _ _ _ t =>
    cases t with
    | lolliE _ _ _ _ _ _ tf =>
      cases tf with
      | lolliE _ _ _ _ _ x h =>
        cases h <;> simp only [TExpr.shift, immLendT, TExpr.isVarT_shift hc]
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem dtorOf1T_shift {d c : Nat} (hc : 1 < c) (t : TExpr) : dtorOf1T (t.shift d c) = dtorOf1T t := by
  cases t with
  | lolliE _ _ _ _ _ x h => cases h <;> simp only [TExpr.shift, dtorOf1T, TExpr.isVarT_shift hc]
  | _ => rfl

theorem litBodyT_shift (d c : Nat) (t : TExpr) : litBodyT (t.shift d c) = litBodyT t := by
  cases t with
  | bind _ _ _ _ _ tA tN =>
    cases tN with
    | bind _ _ _ _ _ tL tR =>
      cases tR with
      | tensorE _ _ _ _ _ _ tP tU =>
        cases tU with
        | unitE _ _ _ _ tD _ =>
          simp only [TExpr.shift, litBodyT, tabT_shift, immLendT_shift (Nat.succ_pos c),
            TExpr.isVarT_shift (show 0 < c + 1 + 1 by omega),
            dtorOf1T_shift (show 1 < c + 1 + 1 + 2 by omega)]
        | _ => rfl
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem litViewT_shift (d c : Nat) (t : TExpr) : litViewT (t.shift d c) = litViewT t := by
  cases t with
  | ofRet _ _ _ t =>
    cases t with
    | bind _ _ _ _ _ _ tN =>
      cases tN with
      | tensorE _ _ _ _ _ _ tV tB =>
        simp only [TExpr.shift, litViewT, TExpr.isVarT_shift (Nat.succ_pos c), litBodyT_shift]
      | _ => rfl
    | _ => rfl
  | _ => rfl

theorem TExpr.isUnfoldN_shift (d c : Nat) (t : TExpr) : (t.shift d c).isUnfoldN = t.isUnfoldN := by
  cases t <;> rfl

theorem unfoldAppT_shift (d : Nat) (t : TExpr) : ∀ c, unfoldAppT (t.shift d c) = unfoldAppT t := by
  induction t <;> intro c <;> simp_all [TExpr.shift, unfoldAppT, TExpr.isUnfoldN_shift]

theorem insPair_getD {d : Nat} : ∀ (c k : Nat) (u : List (Bool × Bool)), k < c →
    (insPair d c u).getD k (false, false) = u.getD k (false, false)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | c + 1, 0, a :: u, _ => rfl
  | c + 1, k + 1, a :: u, h => by
    simp only [insPair, List.getD_cons_succ]; exact insPair_getD c k u (by omega)
  | c + 1, k, [], _ => by
    simp only [insPair, List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none,
      List.getElem?_replicate]
    split <;> rfl

theorem Masks.at_ins {d c k : Nat} (h : k < c) (u : Masks) : (u.ins d c).at k = u.at k := by
  simp only [Masks.at, Masks.ins]; exact insPair_getD c k u.ms h

theorem TExpr.isRelease_shift (d c : Nat) (t : TExpr) : (t.shift d c).isRelease = t.isRelease := by
  cases t <;> rfl

theorem relT_shift (d : Nat) (t : TExpr) : ∀ k c, k < c → relT k (t.shift d c) = relT k t := by
  induction t
  case lolliE _ _ _ _ _ ta tf _ _ =>
    intro k c h; simp only [TExpr.shift, relT, TExpr.isVarT_shift h, TExpr.isRelease_shift]
  case ret _ _ _ t ih | ofRet _ _ _ t ih | effSub _ _ _ _ _ t ih | lendScope _ _ _ t ih
    | sumI₁ _ _ _ _ t ih | sumI₂ _ _ _ _ t ih =>
    intro k c h; simp only [TExpr.shift, relT, ih k c h]
  case bind _ _ _ _ u tM tN ihM ihN | effLet _ _ _ _ _ u tM tN ihM ihN =>
    intro k c h
    simp only [TExpr.shift, relT, Masks.at_ins h, ihM k c h, ihN (k + 1) (c + 1) (by omega)]
  case unitE _ _ _ u tV tM ihV ihM | tensorI _ _ _ _ u tV tM ihV ihM =>
    intro k c h; simp only [TExpr.shift, relT, Masks.at_ins h, ihV k c h, ihM k c h]
  case sumE _ _ _ _ _ u tV t₁ t₂ _ ih₁ ih₂ =>
    intro k c h
    simp only [TExpr.shift, relT, Masks.at_ins h, ih₁ (k + 1) (c + 1) (by omega),
      ih₂ (k + 1) (c + 1) (by omega)]
  case tensorE _ _ _ _ _ u tV tM _ ihM =>
    intro k c h; simp only [TExpr.shift, relT, Masks.at_ins h, ihM (k + 2) (c + 2) (by omega)]
  case effThen _ _ _ _ _ _ _ u tM tN tD ihM ihN ihD =>
    intro k c h
    simp only [TExpr.shift, relT, Masks.at_ins h, ihM k c h, ihN (k + 1) (c + 1) (by omega),
      ihD (k + 1) (c + 1) (by omega)]
  all_goals intro k c h; rfl

theorem lendRelT_shift (d c : Nat) (t : TExpr) : lendRelT (t.shift d c) = lendRelT t := by
  cases t with
  | tensorE _ _ _ _ _ _ _ tM => simp only [TExpr.shift, lendRelT, relT_shift d tM 1 (c + 2) (by omega)]
  | bind _ _ _ _ _ _ tN | effLet _ _ _ _ _ _ _ tN =>
    cases tN with
    | tensorE _ _ _ _ _ _ _ tM =>
      simp only [TExpr.shift, lendRelT, relT_shift d tM 1 (c + 1 + 2) (by omega)]
    | _ => rfl
  | _ => rfl

end BoCa.Fig16.LogRel.Core.Check
