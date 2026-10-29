import Frontend.Check.TExpr
import Frontend.Check.Decide
import Core.InsertDead

/-!
# Frontend — Check — the typed term at a wider context  `[spec §3, §10]`

A `def`'s body is checked once per key, at the context of the persistent externs, and placed at
each use (`TExpr.use`). The use's context has more slots than the body's: the slots bound between
the externs and the use, which the body does not name. Two functions say what the body is at the
use:

* `TExpr.shift d c t` is `t` with `d` slots inserted at position `c` of its context: each
  variable at or past `c` moved past them, each use mask given `d` unused slots there
  (`Masks.ins`), as `Expr.shift` moves the erasure's (`Frontend/Check/Weaken.lean` proves the
  erasure of the shifted term is the shifted erasure).
* `TExpr.absF Δ t` is the body's **absorption**: a formula over a slot's type (`AbsF`) that says
  when an unused live slot of that type can be given to `t`'s derivation. It is read off the
  rules' premises on the context's live slots: a leaf drops a persistent slot (`Ctx.DeadP`,
  `Ctx.SoloP`), `⟨⟩` absorbs any (`topI`), a split gives the slot to either part, two premises at
  one context both take it, and a premise on every live slot (`Persistent`, `CtxOutlives`, `∀I`'s
  freshness, `[let]`'s drops) conjoins its condition. `none` is a node whose derivation cannot be
  placed at a wider context at all: the relaxed rules at their fixed contexts (SPEC §29).

`TDerivesAt.weaken` and `TDerivesP.weaken` (`Frontend/Check/Weaken.lean`) are the lemmas these
serve: a derivation of `t` is one of `t.shift` at the context with the slots inserted, when each
inserted live slot satisfies `t.absF`.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

/-! ### Absorption formulas -/

/-- The atom at a type. -/
def Atom.eval : Atom → VTy → Bool
  | .pers, A => A.persistent
  | .bang, A => isBangB A
  | .drop, A => dropB A
  | .nfree x, A => !vfreeB x A
  | .outl Δ a, A => outlivesB Δ a A

/-- The formula at a type. -/
def AbsF.eval (f : AbsF) (A : VTy) : Bool := f.any fun c => c.all fun a => a.eval A

/-- True. -/
def AbsF.tt : AbsF := [[]]

/-- False. -/
def AbsF.ff : AbsF := []

/-- One atom. -/
def AbsF.atom (a : Atom) : AbsF := [[a]]

/-- The clause `c'` holds where `c` does: every atom of `c'` is one of `c`. -/
def AbsF.within (c' c : List Atom) : Bool := c'.all (c.contains ·)

/-- A clause added to a disjunction: dropped when a clause within it is there, and dropping the
clauses it is within. -/
def AbsF.add (f : AbsF) (c : List Atom) : AbsF :=
  if f.any (AbsF.within · c) then f else c :: f.filter (fun d => !AbsF.within c d)

/-- The disjunction. -/
def AbsF.or (f g : AbsF) : AbsF := g.foldl AbsF.add f

/-- The conjunction, distributed. -/
def AbsF.and (f g : AbsF) : AbsF :=
  (f.flatMap fun c => g.map fun c' => c ++ c'.filter (!c.contains ·)).foldl AbsF.add []

theorem AbsF.eval_tt (A : VTy) : AbsF.tt.eval A = true := by simp [AbsF.tt, AbsF.eval]

theorem AbsF.eval_ff (A : VTy) : AbsF.ff.eval A = false := by simp [AbsF.ff, AbsF.eval]

theorem AbsF.eval_atom (a : Atom) (A : VTy) : (AbsF.atom a).eval A = a.eval A := by
  simp [AbsF.atom, AbsF.eval]

theorem AbsF.within_all {c' c : List Atom} {A : VTy} (h : AbsF.within c' c = true)
    (hc : (c.all fun a => a.eval A) = true) : (c'.all fun a => a.eval A) = true := by
  simp only [AbsF.within, List.all_eq_true, List.contains_iff_mem] at h hc ⊢
  exact fun a ha => hc a (h a ha)

theorem AbsF.eval_add (f : AbsF) (c : List Atom) (A : VTy) :
    (f.add c).eval A = (f.eval A || c.all fun a => a.eval A) := by
  unfold AbsF.add
  split
  · rename_i h
    obtain ⟨c', hc', hw⟩ := List.any_eq_true.mp h
    cases hcv : (c.all fun a => a.eval A)
    · simp
    · have : f.eval A = true := List.any_eq_true.mpr ⟨c', hc', AbsF.within_all hw hcv⟩
      simp [this]
  · simp only [AbsF.eval, List.any_cons]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, List.any_eq_true, List.mem_filter, Bool.not_eq_true']
    constructor
    · rintro (h | ⟨d, ⟨hd, _⟩, hdv⟩)
      · exact Or.inr h
      · exact Or.inl ⟨d, hd, hdv⟩
    · rintro (⟨d, hd, hdv⟩ | h)
      · by_cases hw : AbsF.within c d = true
        · exact Or.inl (AbsF.within_all hw hdv)
        · exact Or.inr ⟨d, ⟨hd, by simpa using hw⟩, hdv⟩
      · exact Or.inl h

theorem AbsF.eval_foldl_add (A : VTy) : ∀ (g f : AbsF),
    (g.foldl AbsF.add f).eval A = (f.eval A || g.any fun c => c.all fun a => a.eval A)
  | [], f => by simp
  | c :: g, f => by
      rw [List.foldl_cons, AbsF.eval_foldl_add A g, AbsF.eval_add, List.any_cons]
      cases f.eval A <;> cases (c.all fun a => a.eval A) <;> simp

theorem AbsF.eval_or (f g : AbsF) (A : VTy) : (f.or g).eval A = (f.eval A || g.eval A) := by
  unfold AbsF.or; rw [AbsF.eval_foldl_add]; rfl

theorem AbsF.eval_and (f g : AbsF) (A : VTy) : (f.and g).eval A = (f.eval A && g.eval A) := by
  unfold AbsF.and
  rw [AbsF.eval_foldl_add]
  simp only [AbsF.eval, List.any_nil, Bool.false_or]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_flatMap, List.mem_map, List.all_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨_, ⟨c, hc, c', hc', rfl⟩, h⟩
    refine ⟨⟨c, hc, fun a ha => h a (List.mem_append_left _ ha)⟩, ⟨c', hc', fun a ha => ?_⟩⟩
    by_cases hm : c.contains a = true
    · exact h a (List.mem_append_left _ (by simpa using hm))
    · exact h a (List.mem_append_right _ (List.mem_filter.mpr ⟨ha, by simpa using hm⟩))
  · rintro ⟨⟨c, hc, h⟩, ⟨c', hc', h'⟩⟩
    refine ⟨_, ⟨c, hc, c', hc', rfl⟩, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact h a ha
    · exact h' a (List.mem_filter.mp ha).1

/-- Both premises at one context take the slot. -/
def AbsF.andO : Option AbsF → Option AbsF → Option AbsF
  | some f, some g => some (f.and g)
  | _, _ => none

/-- Either part of a split takes the slot; each part is at a wider context. -/
def AbsF.orO : Option AbsF → Option AbsF → Option AbsF
  | some f, some g => some (f.or g)
  | _, _ => none

/-- A premise on every live slot of the conclusion's context, beside the rest. -/
def AbsF.withO (f : AbsF) : Option AbsF → Option AbsF
  | some g => some (f.and g)
  | none => none

/-! ### Shifting -/

/-- **The typed term at a wider context**: `d` slots inserted at position `c` of its context. A
child at a context of its own (`letPoly`'s value, the relaxed rules') is left as it is. -/
def TExpr.shift (d c : Nat) : TExpr → TExpr
  | .var i j k A => .var i j (sIdx d c k) A
  | .tensorI i j A B u t₁ t₂ => .tensorI i j A B (u.ins d c) (t₁.shift d c) (t₂.shift d c)
  | .sumI₁ i j A B t => .sumI₁ i j A B (t.shift d c)
  | .sumI₂ i j A B t => .sumI₂ i j A B (t.shift d c)
  | .thunkF i j A t => .thunkF i j A (t.shift d (c + 1))
  | .thunkV i j C t => .thunkV i j C (t.shift d c)
  | .ret i j A t => .ret i j A (t.shift d c)
  | .bind i j A C u tM tN => .bind i j A C (u.ins d c) (tM.shift d c) (tN.shift d (c + 1))
  | .force i j k C => .force i j (sIdx d c k) C
  | .lam i j A C t => .lam i j A C (t.shift d (c + 1))
  | .lamDead i j S B t => .lamDead i j S B (t.shift d (c + 1))
  | .app i j k A C u tM => .app i j (sIdx d c k) A C (u.ins d c) (tM.shift d c)
  | .withI i j C D tM tN => .withI i j C D (tM.shift d (c + 2)) (tN.shift d (c + 2))
  | .proj₁ i j C D t => .proj₁ i j C D (t.shift d c)
  | .proj₂ i j C D t => .proj₂ i j C D (t.shift d c)
  | .unitE i j C u tV tM => .unitE i j C (u.ins d c) (tV.shift d c) (tM.shift d c)
  | .tensorE i j A B C u tV tM =>
      .tensorE i j A B C (u.ins d c) (tV.shift d c) (tM.shift d (c + 2))
  | .sumE i j A B C u tV t₁ t₂ =>
      .sumE i j A B C (u.ins d c) (tV.shift d c) (t₁.shift d (c + 1)) (t₂.shift d (c + 1))
  | .zeroE i j C u tV => .zeroE i j C (u.ins d c) (tV.shift d c)
  | .allI i j x b S C t => .allI i j x b S C (t.shift d (c + 1))
  | .allE i j x b a C t => .allE i j x b a C (t.shift d c)
  | .bangThunkF i j A t => .bangThunkF i j A (t.shift d (c + 1))
  | .bangThunkV i j C t => .bangThunkV i j C (t.shift d c)
  | .bangE i j A t => .bangE i j A (t.shift d c)
  | .boxI i j a A t => .boxI i j a A (t.shift d c)
  | .boxE i j a A t => .boxE i j a A (t.shift d c)
  | .immSub i j a b A t => .immSub i j a b A (t.shift d c)
  | .mutSub i j a b A t => .mutSub i j a b A (t.shift d c)
  | .withbor1U i j A B S x td => .withbor1U i j A B S x (td.shift d c)
  | .withbor2U i j A B S x td => .withbor2U i j A B S x (td.shift d c)
  | .withbor3U i j a A B S x td => .withbor3U i j a A B S x (td.shift d c)
  | .sliceBorrowMU i j A B S x td => .sliceBorrowMU i j A B S x (td.shift d c)
  | .sliceBorrowIU i j A B S x td => .sliceBorrowIU i j A B S x (td.shift d c)
  | .lolliE i j A B u ta tf => .lolliE i j A B (u.ins d c) (ta.shift d c) (tf.shift d c)
  | .allEV i j x b a A t => .allEV i j x b a A (t.shift d c)
  | .ofRet i j A t => .ofRet i j A (t.shift d c)
  | .roll i j A t => .roll i j A (t.shift d c)
  | .unroll i j A t => .unroll i j A (t.shift d c)
  | .nuIn i j C t => .nuIn i j C (t.shift d c)
  | .nuOut i j C t => .nuOut i j C (t.shift d c)
  | .effSub i j S S' A t => .effSub i j S S' A (t.shift d c)
  | .effPerform i j S o t => .effPerform i j S o (t.shift d c)
  | .effRaise i j S o B t => .effRaise i j S o B (t.shift d c)
  | .effLet i j A B S u tM tN =>
      .effLet i j A B S (u.ins d c) (tM.shift d c) (tN.shift d (c + 1))
  | .effThen i j A B S SM SD u tM tN tD =>
      .effThen i j A B S SM SD (u.ins d c) (tM.shift d c) (tN.shift d (c + 1))
        (tD.shift d (c + 1))
  | .effHandleV i j S E fs n A R u ks st ins tc te =>
      .effHandleV i j S E fs n A R (u.ins d c) ks st ins (tc.shift d c) (te.shift d c)
  | .effHandleVB i j S E fs n A R a u ks st ins tc te =>
      .effHandleVB i j S E fs n A R a (u.ins d c) ks st ins (tc.shift d c) (te.shift d c)
  | .effHandleT i j S SN E fs n A R u st ins tc te =>
      .effHandleT i j S SN E fs n A R (u.ins d c) st ins (tc.shift d c) (te.shift d c)
  | .effHandleL i j S SW E fs Xs n A R u st ins tc te =>
      .effHandleL i j S SW E fs Xs n A R (u.ins d c) st ins (tc.shift d c) (te.shift d c)
  | .letPoly i j C j' tV tN => .letPoly i j C j' tV (tN.shift d (c + 1))
  | .use i j n k τ ab t => .use i j n k τ ab (t.shift d c)
  | .litFn i j bs t => .litFn i j bs (t.shift d c)
  | .divLit i j op k t => .divLit i j op k (t.shift d c)
  | .walk i j m r t => .walk i j m r (t.shift d c)
  | .walkGet i j m t => .walkGet i j m (t.shift d c)
  | .selfCall i j k n t => .selfCall i j k n (t.shift d c)
  | .lendCell i j m t => .lendCell i j m (t.shift d c)
  | .nuEta i j f s t => .nuEta i j (sIdx d c f) (s.map (sIdx d c)) (t.shift d c)
  | .lendScope i j r t => .lendScope i j r (t.shift d c)
  | .litView i j t => .litView i j (t.shift d c)
  | .unfoldStep i j t => .unfoldStep i j (t.shift d c)
  | t@(.unitI ..) => t
  | t@(.topI ..) => t
  | t@(.copyBang ..) => t
  | t@(.forgetBang ..) => t
  | t@(.alloc ..) => t
  | t@(.free ..) => t
  | t@(.swap ..) => t
  | t@(.copy ..) => t
  | t@(.forgetImm ..) => t
  | t@(.forgetMut ..) => t
  | t@(.forgetUnk ..) => t
  | t@(.lit ..) => t
  | t@(.hostOp ..) => t
  | t@(.arrNew ..) => t
  | t@(.arrFree ..) => t
  | t@(.arrSize ..) => t
  | t@(.arrReplace ..) => t
  | t@(.arrLen ..) => t
  | t@(.arrGet ..) => t
  | t@(.arrCopy ..) => t
  | t@(.arrForget ..) => t
  | t@(.countFold ..) => t
  | t@(.countTry ..) => t
  | t@(.boundedFix ..) => t
  | t@(.sliceBorrowM ..) => t
  | t@(.sliceBorrowI ..) => t
  | t@(.sliceGetM ..) => t
  | t@(.sliceLenM ..) => t
  | t@(.sliceSplitI ..) => t
  | t@(.sliceSplitM ..) => t
  | t@(.sliceEmptyI ..) => t
  | t@(.sliceEmptyM ..) => t
  | t@(.arrEmpty ..) => t
  | t@(.sliceReplaceM ..) => t
  | t@(.sliceSwapM ..) => t
  | t@(.withbor1 ..) => t
  | t@(.withbor2 ..) => t
  | t@(.withbor3 ..) => t
  | t@(.withload ..) => t
  | t@(.withswap ..) => t
  | t@(.withloadU ..) => t
  | t@(.foldImm ..) => t
  | t@(.foldOwn ..) => t
  | t@(.foldOwnG ..) => t
  | t@(.foldReuse ..) => t
  | t@(.unfoldN ..) => t
  | t@(.lendR ..) => t
  | t@(.iterate ..) => t
  | t@(.divFuel ..) => t
  | t@(.reify ..) => t
  | t@(.dtor ..) => t
  | t@(.allocS ..) => t
  | t@(.freeS ..) => t
  | t@(.withborSM ..) => t
  | t@(.withborSI ..) => t
  | t@(.withborF2M ..) => t
  | t@(.withborF2I ..) => t
  | t@(.lendLoopR ..) => t
  | t@(.nilDead ..) => t

/-! ### Absorption -/

/-- **A body's absorption**: when an unused live slot of a type can be given to its derivation,
under `Δ`. -/
def TExpr.absF (Δ : LifeCtx) : TExpr → Option AbsF
  | .tensorI _ _ _ _ _ t₁ t₂ => AbsF.orO (t₁.absF Δ) (t₂.absF Δ)
  | .sumI₁ _ _ _ _ t | .sumI₂ _ _ _ _ t | .thunkF _ _ _ t | .thunkV _ _ _ t | .ret _ _ _ t
  | .lam _ _ _ _ t | .lamDead _ _ _ _ t | .proj₁ _ _ _ _ t | .proj₂ _ _ _ _ t
  | .allE _ _ _ _ _ _ t | .bangE _ _ _ t | .boxE _ _ _ _ t | .immSub _ _ _ _ _ t
  | .mutSub _ _ _ _ _ t | .allEV _ _ _ _ _ _ t | .ofRet _ _ _ t | .roll _ _ _ t
  | .unroll _ _ _ t | .nuIn _ _ _ t | .nuOut _ _ _ t | .effSub _ _ _ _ _ t
  | .effPerform _ _ _ _ t | .effRaise _ _ _ _ _ t | .litFn _ _ _ t | .divLit _ _ _ _ t
  | .walk _ _ _ _ t | .walkGet _ _ _ t | .selfCall _ _ _ _ t | .lendCell _ _ _ t | .nuEta _ _ _ _ t
  | .lendScope _ _ _ t | .litView _ _ t | .unfoldStep _ _ t => t.absF Δ
  | .bind _ _ _ _ _ t₁ t₂ | .unitE _ _ _ _ t₁ t₂ | .tensorE _ _ _ _ _ _ t₁ t₂
  | .lolliE _ _ _ _ _ t₁ t₂ => AbsF.orO (t₁.absF Δ) (t₂.absF Δ)
  | .app _ _ _ _ _ _ tM => AbsF.orO (tM.absF Δ) (some (.atom .pers))
  | .withI _ _ _ _ tM tN => AbsF.andO (tM.absF Δ) (tN.absF Δ)
  | .sumE _ _ _ _ _ _ tV t₁ t₂ => AbsF.orO (tV.absF Δ) (AbsF.andO (t₁.absF Δ) (t₂.absF Δ))
  | .zeroE _ _ _ _ tV => AbsF.orO (tV.absF Δ) (some .tt)
  | .topI _ _ => some .tt
  | .allI _ _ x b _ _ t => AbsF.withO (.atom (.nfree x)) (t.absF (Δ.extend x b))
  | .bangThunkF _ _ _ t | .bangThunkV _ _ _ t => AbsF.withO (.atom .bang) (t.absF Δ)
  | .boxI _ _ a _ t => AbsF.withO (.atom (.outl Δ a)) (t.absF Δ)
  | .withbor1U _ _ _ _ _ _ td | .withbor2U _ _ _ _ _ _ td | .withbor3U _ _ _ _ _ _ _ td
  | .sliceBorrowMU _ _ _ _ _ _ td | .sliceBorrowIU _ _ _ _ _ _ td =>
      AbsF.withO (.atom .pers) (td.absF Δ)
  | .effLet _ _ _ _ S _ tM tN =>
      AbsF.orO (tM.absF Δ) (AbsF.withO (letCond S) (tN.absF Δ))
  | .effThen _ _ _ _ S _ _ _ tM tN tD =>
      AbsF.orO (tM.absF Δ) (AbsF.withO (if Row.unrDB S then .atom .bang else .tt)
        (AbsF.andO (tN.absF Δ) (tD.absF Δ)))
  | .effHandleV _ _ _ _ _ _ _ _ _ _ _ _ tc te =>
      AbsF.orO (AbsF.withO (.atom .pers) (tc.absF Δ)) (te.absF Δ)
  | .effHandleVB _ _ _ _ _ _ _ _ d _ _ _ _ tc te =>
      AbsF.orO (AbsF.withO (.atom .pers) (tc.absF Δ)) (AbsF.withO (.atom (.outl Δ d)) (te.absF Δ))
  | .lendR .. | .lendLoopR .. | .nilDead .. => none
  -- Not placed at a wider context: rules the checker does not apply (the tail-resumptive
  -- `[handle]` and `[handle-last]` of `Div`'s rows, and `[let-poly]`, whose copies are `use`
  -- nodes).
  | .effHandleT .. | .effHandleL .. | .letPoly .. => none
  | .dtor .. | .allocS .. | .freeS .. | .withborSM .. | .withborSI .. | .withborF2M ..
  | .withborF2I .. => some .ff
  | .use _ _ _ _ _ ab _ => ab
  | .var .. | .force .. | .unitI .. | .copyBang .. | .forgetBang .. | .alloc .. | .free ..
  | .swap .. | .copy .. | .forgetImm .. | .forgetMut .. | .forgetUnk .. | .lit .. | .hostOp ..
  | .arrNew .. | .arrFree .. | .arrSize .. | .arrReplace .. | .arrLen .. | .arrGet ..
  | .arrCopy .. | .arrForget .. | .countFold .. | .countTry .. | .boundedFix ..
  | .sliceBorrowM .. | .sliceBorrowI .. | .sliceGetM .. | .sliceLenM .. | .sliceSplitI ..
  | .sliceSplitM .. | .sliceEmptyI .. | .sliceEmptyM .. | .arrEmpty .. | .sliceReplaceM .. | .sliceSwapM ..
  | .withbor1 .. | .withbor2 .. | .withbor3 .. | .withload .. | .withswap .. | .withloadU ..
  | .foldImm .. | .foldOwn .. | .foldOwnG .. | .foldReuse .. | .unfoldN .. | .iterate .. | .divFuel ..
  | .reify .. =>
      some (.atom .pers)
where
  /-- `[let]`'s premise on the rest's live slots: they drop at a row with weakening, and are `!`
  at an unrestricted row. -/
  letCond (S : Row) : AbsF :=
    if Row.weakB S then (AbsF.atom .drop).and (if Row.unrB S then .atom .bang else .tt) else .tt

theorem TExpr.absF_shift (d : Nat) : ∀ (t : TExpr) (c : Nat) (Δ : LifeCtx),
    (t.shift d c).absF Δ = t.absF Δ := by
  intro t
  induction t <;> intro c Δ <;> simp only [TExpr.shift, TExpr.absF, *]

end BoCa.Fig16.LogRel.Core.Check
