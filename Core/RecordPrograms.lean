import Core.Splits
import Core.CommonList

/-!
# Core — programs: field access through borrows  `[spec §5]`

Closed programs, each a `CDerives` derivation at `1` run by `adequacyC`, and a kernel-checked
run of the interpreter; each `…Obs` variant returns what was read or written.

| program | shows |
|---|---|
| `readFields` | `Imm` borrow of a record: an unboxed field arrives as a copy, a `Ref` field as a view at the load's `'b` |
| `mutFields` | `Mut` borrow of a record: one field updated by `swapField`, the whole record moved out and back |
| `matchSome` | `Imm` borrow of a variant: `case` on the loaded image, the payload's cell read at `'b` |
| `bagProg` | a record with a list field `{n : N, items : L}` under `Mut`: `swapField` pushes a node |

The record `Pt = {flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)}` is `node (leaf B) (leaf (Ref B))`, the
variant `Opt = ⟨some : Ref (1 ⊕ 1) | none : 1⟩` is `node (leaf (Ref B)) (leaf 1)`, and the
bag is `node (leaf N) (leaf L)` with `L` the common list (`CommonList.lean`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2 unitNoLeak)

/-- `1 ⊕ 1`. -/
abbrev BB : VTy := .sum .unit .unit

/-- `case e {x ⇒ x ∣ y ⇒ y}`: a boolean consumed. -/
def dropB (e : Expr) : Expr := .case e (.var 0) (.var 0)

theorem d_dropB {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    (he : CDerives Δ (part e 0 Γ).1 e (.val BB)) (hΓ : Ctx.Dead (part e 0 Γ).2) :
    CDerives Δ Γ (dropB e) (.val .unit) :=
  caseW he (.var (.here hΓ)) (.var (.here hΓ))

/-- `'x ⊏ ⊓∅`, the context a top-level borrow's callback runs in. -/
abbrev D1 : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

theorem d1_ok : D1.Ok := by decide

/-! ### Reading fields through an immutable borrow

    let (r, p) = withbor (alloc {flag = inj₂ (), cell = alloc (inj₁ ())}) (Λ. λx.
                   let (x₁, x₂) = copy x;
                   let f = withload x₁ (Λ. λr. let y = r.flag in y);
                   let c = withload x₂ (Λ. λr. let v = r.cell in
                             let w = withload v (Λ. λz. z) in w);
                   (f, c));
    let (f, c) = p; drop f; drop c;
    let {flag, cell} = free r; drop flag; drop (free cell)

Each `withload` runs at a fresh `'b ⊏ 'a`, and its callback receives
`Imm̲ 'b {flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)} = {flag : 1 ⊕ 1, cell : Imm 'b (1 ⊕ 1)}`: the
unboxed field as a copy, the boxed field as a view at `'b`, read by a second `withload`. -/

/-- `{flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)}`. -/
abbrev Pt : Shape := .node (.leaf BB) (.leaf (.ref BB))

def mkPt : Expr := .pair (.inj₂ unit') (.app alloc' (.inj₁ unit'))

/-- The load of `cell`'s view, at `'c` = variable `2`. -/
def readCell : Expr := elet (app2 withload (.var 0) (.val (.lam (.val (.lam (.var 0)))))) (.var 0)

def readBody : Expr :=
  .letpair (.app copy (.var 0))
    (elet (loadField Pt [false] 1 (.var 1) (.var 0))
      (elet (loadField Pt [true] 1 (.var 1) readCell) (.pair (.var 1) (.var 0))))

def readBorrower : Expr := .val (.lam (.val (.lam readBody)))

/-- `let {flag, cell} = free r; drop flag; drop (free cell)`, with `r` at index `i`. -/
def freePt (i : Nat) : Expr :=
  recLet Pt (.app free' (.var i)) (.seq (dropB (.var 0)) (dropB (.app free' (.var 1))))

def readFields : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) readBorrower)
    (.letpair (.var 0) (.seq (dropB (.var 1)) (.seq (dropB (.var 0)) (freePt 3))))

/-- The same run, returning the pair read through the borrow. -/
def readFieldsObs : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) readBorrower) (.seq (freePt 1) (.var 0))

/-- The load's lifetime context `'b ⊏ ⊓D1`. -/
abbrev D1b : LifeCtx := D1.extend 1 D1.meetOfDom

theorem d_freePt {Γ : Ctx VTy} {i : Nat}
    (h : CDerives LifeCtx.empty (part (.app free' (.var i)) 0 Γ).1 (.app free' (.var i))
      (.val Pt.valTy))
    (hΓ : Ctx.Dead (part (.app free' (.var i)) 0 Γ).2) :
    CDerives LifeCtx.empty Γ (freePt i) (.val .unit) :=
  recEV Pt (part_split (.app free' (.var i)) 0 Γ) h
    (seqW (d_dropB (.var (by csolo)) (by cdead))
      (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead)))

/-- `readCell` at a load's body: the view `Imm 'b (1 ⊕ 1)` read at `'c ⊏ ⊓Δ`. -/
theorem d_readCell {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives D1b (⟨.imm (.var 1) BB, true⟩ :: Γ) readCell (.val (.box (.var 1) BB)) :=
  eletW
    (appW
      (callbackW (x := 2) (by decide) rfl (by cdead)
        (.boxI (.var (by csolo))
          (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (by cdead))))
      (appW (.var (by csolo))
        (.withload (a := .var 1) (A := BB) (B := BB) 2 (by cdead) rfl
          (by simp [VFree, Shape.valTy]) (by simp [VFree]))))
    (.boxI (.var (by csolo))
      (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (by cdead)))

theorem d_readBody :
    CDerives D1 [⟨.imm (.var 0) Pt.valTy, true⟩, ⟨.unit, false⟩] readBody
      (.val (.box (.var 0) (.tensor BB BB))) :=
  letW (A := .imm (.var 0) Pt.valTy) (B := .imm (.var 0) Pt.valTy)
    (appW (.var (by csolo)) (.copy (by cdead))) <|
  eletW
    (loadField_wf (a := .var 0) (B := BB) d1_ok (.var (by csolo)) rfl ⟨.sum .unit .unit, .imm⟩
      rfl (by simp [VFree, Shape.valTy]) (by simp [VFree])
      (.boxI (.var (by csolo)) (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide)))) <|
  eletW
    (loadField_wf (a := .var 0) (B := BB) d1_ok (.var (by csolo)) rfl ⟨.sum .unit .unit, .imm⟩
      rfl (by simp [VFree, Shape.valTy]) (by simp [VFree]) (d_readCell (by cdead)))
    (.boxI (pairW (.var (by csolo)) (.var (by csolo)))
      (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide)))

theorem d_readBorrower :
    CDerives LifeCtx.empty [] readBorrower
      (.val (.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.imm (.var 0) Pt.valTy) (.box (.var 0) (.tensor BB BB))))) :=
  callbackW ok_empty rfl .nil d_readBody

theorem d_readFields : CDerives LifeCtx.empty [] readFields (.val .unit) :=
  letW (A := .ref Pt.valTy) (B := .tensor BB BB)
    (appW d_readBorrower
      (appW (appW (pairW (.sumI₂ (.unitI (by cdead)))
          (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead))))
          (.alloc (by cdead)))
        (.withbor1 (A := Pt.valTy) (B := .tensor BB BB) 0 (by cdead) rfl
          (fun _ h => by simp [VFree, Shape.valTy] at h) (by simp [VFree, Shape.valTy]) (by simp [VFree])))) <|
  letW (A := BB) (B := BB) (.var (by csolo)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) <|
  d_freePt (appW (.var (by csolo)) (.free (by cdead))) (by cdead)

/-- The record is read through the borrow, and the program leaves no cell. -/
theorem readFields_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem readFields Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_readFields)

theorem readFields_eval : unitNoLeak (eval readFields) = true := by decide

/-- The pair read: `flag`'s copy `inj₂ ()` and `cell`'s contents `inj₁ ()`. -/
theorem readFieldsObs_eval :
    (match eval readFieldsObs with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ### Updating one field through a mutable borrow

    let (r, u) = withbor (alloc {flag = inj₂ (), cell = alloc (inj₁ ())}) (Λ. λm.
                   let (m₁, u₁) = swapField m flag flip;  u₁;
                   let (m₂, u₂) = swapField m₁ cell poke; u₂; forget m₂; ());
    u; let {flag, cell} = free r; drop flag; drop (free cell)

`withswap` moves the whole record out of its cell, the callback rebuilds it with one field
changed, and `withswap` stores it back.  The boxed `cell` is written through a `Mut 'c` of its
own cell, taken by `withbor` on the `Ref` the callback holds (`pokeG`). -/

/-- `λb. (case b {x ⇒ inj₂ x, y ⇒ inj₁ y}, ())`. -/
def flipG : Expr := .val (.lam (.pair (.case (.var 0) (.inj₂ (.var 0)) (.inj₁ (.var 0))) unit'))

/-- `λb. (inj₂ (), drop b)`. -/
def setG : Expr := .val (.lam (.pair (.inj₂ unit') (dropB (.var 0))))

/-- `λc. withbor c (Λ. λm. let (m′, u) = withswap m setG; u; forget m′; ())`. -/
def pokeG : Expr :=
  .val (.lam (app2 withbor (.var 0) (.val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) setG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit')))))))))

theorem d_flipG {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ flipG (.val (.lolli BB (.tensor BB .unit))) :=
  .lamV (pairW (caseW (.var (by csolo)) (.sumI₂ (.var (by csolo))) (.sumI₁ (.var (by csolo))))
    (.unitI (by cdead)))

theorem d_setG {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ setG (.val (.lolli BB (.tensor BB .unit))) :=
  .lamV (pairW (.sumI₂ (.unitI (by cdead))) (d_dropB (.var (by csolo)) (by cdead)))

theorem d_pokeG {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives D1 Γ pokeG (.val (.lolli (.ref BB) (.tensor (.ref BB) .unit))) :=
  .lamV <|
    appW
      (callbackW (x := 1) d1_ok rfl (by cdead) <|
        letW (A := .mut (.var 1) BB) (B := .unit)
          (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
        seqW (.var (by csolo)) <|
        seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
          (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩))
      (appW (.var (by csolo))
        (.withbor2 (A := BB) (B := .unit) 1 (by cdead) rfl
          ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ (by simp [VFree])
          (by simp [VFree])))

def mutBody : Expr :=
  .letpair (swapField Pt [false] (.var 0) flipG)
    (.seq (.var 0) (.letpair (swapField Pt [true] (.var 1) pokeG)
      (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))

def mutBorrower : Expr := .val (.lam (.val (.lam mutBody)))

def mutFields : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) mutBorrower) (.seq (.var 0) (freePt 1))

/-- The same run, returning the record's contents after the updates. -/
def mutFieldsObs : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) mutBorrower)
    (.seq (.var 0) (recLet Pt (.app free' (.var 1)) (.pair (.var 0) (.app free' (.var 1)))))

theorem d_mutBorrower :
    CDerives LifeCtx.empty [] mutBorrower
      (.val (.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.mut (.var 0) Pt.valTy) (.box (.var 0) .unit)))) :=
  callbackW ok_empty rfl .nil <|
    letW (A := .mut (.var 0) Pt.valTy) (B := .unit)
      (swapField_wf (.var (by csolo)) rfl (fun h => d_flipG h)) <|
    seqW (.var (by csolo)) <|
    letW (A := .mut (.var 0) Pt.valTy) (B := .unit)
      (swapField_wf (.var (by csolo)) rfl (fun h => d_pokeG h)) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

theorem d_mutFields : CDerives LifeCtx.empty [] mutFields (.val .unit) :=
  letW (A := .ref Pt.valTy) (B := .unit)
    (appW d_mutBorrower
      (appW (appW (pairW (.sumI₂ (.unitI (by cdead)))
          (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead))))
          (.alloc (by cdead)))
        (.withbor2 (A := Pt.valTy) (B := .unit) 0 (by cdead) rfl
          ⟨.top, LifeCtx.defines_of_wf rfl, .tensor (outlives_of_dataB rfl)
            (.ref (outlives_of_dataB rfl))⟩ (by simp [VFree, Shape.valTy]) (by simp [VFree])))) <|
  seqW (.var (by csolo)) <|
  d_freePt (appW (.var (by csolo)) (.free (by cdead))) (by cdead)

theorem mutFields_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem mutFields Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_mutFields)

theorem mutFields_eval : unitNoLeak (eval mutFields) = true := by decide

/-- After the two updates: `flag` flipped to `inj₁ ()`, `cell` holding `inj₂ ()`. -/
theorem mutFieldsObs_eval :
    (match eval mutFieldsObs with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ### Matching on a variant through an immutable borrow

    let (r, o) = withbor (alloc (some (alloc (inj₁ ())))) (Λ. λx.
                   let w = withload x (Λ. λv. case v {
                             some c ⇒ let w = withload c (Λ. λz. z) in w,
                             none u ⇒ u; inj₁ () }) in w);
    drop o; case (free r) {some c ⇒ drop (free c), none u ⇒ u}

`⟨some : Ref (1 ⊕ 1) | none : 1⟩` loaded at `'b` is `⟨some : Imm 'b (1 ⊕ 1) | none : 1⟩`. -/

/-- `⟨some : Ref (1 ⊕ 1) | none : 1⟩`. -/
abbrev Opt : Shape := .node (.leaf (.ref BB)) (.leaf .unit)

def noneBranch : Expr := .seq (.var 0) (.inj₁ unit')

def matchBorrower : Expr :=
  .val (.lam (.val (.lam (elet (loadCase (.var 0) (.node (.leaf readCell) (.leaf noneBranch)))
    (.var 0)))))

def freeOpt (i : Nat) : Expr := .case (.app free' (.var i)) (dropB (.app free' (.var 0))) (.var 0)

def someE : Expr := injAt [false] (.app alloc' (.inj₁ unit'))

def matchSome : Expr :=
  .letpair (app2 withbor (.app alloc' someE) matchBorrower) (.seq (dropB (.var 0)) (freeOpt 1))

/-- The same run, returning the value read in the `some` branch. -/
def matchSomeObs : Expr :=
  .letpair (app2 withbor (.app alloc' someE) matchBorrower) (.seq (freeOpt 1) (.var 0))

theorem d_matchBorrower :
    CDerives LifeCtx.empty [] matchBorrower
      (.val (.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.imm (.var 0) Opt.sumTy) (.box (.var 0) BB)))) :=
  callbackW ok_empty rfl .nil <|
    eletW
      (loadCase_wf (a := .var 0) (B := BB) (y := 1) (σ := Opt)
        (t := .node (.leaf readCell) (.leaf noneBranch)) d1_ok (.var (by csolo)) rfl
        (by simp [VFree, Shape.sumTy]) (by simp [VFree])
        (.node
          (.leaf (A := .imm (.var 1) BB) (.ret (d_readCell (by cdead))))
          (.leaf (A := .unit) (.ret (seqW (.var (by csolo))
            (.boxI (.sumI₁ (.unitI (by cdead))) ⟨LifeCtx.defines_of_wf rfl,
              dead_noLive (by cdead)⟩))))))
      (.boxI (.var (by csolo))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (by cdead)))

theorem d_matchSome : CDerives LifeCtx.empty [] matchSome (.val .unit) :=
  letW (A := .ref Opt.sumTy) (B := BB)
    (appW d_matchBorrower
      (appW (appW (injAt_wf Opt [false] rfl (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead))))
          (.alloc (by cdead)))
        (.withbor1 (A := Opt.sumTy) (B := BB) 0 (by cdead) rfl
          (fun _ h => by simp [VFree, Shape.sumTy] at h) (by simp [VFree, Shape.sumTy])
          (by simp [VFree])))) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) <|
  caseW (appW (.var (by csolo)) (.free (by cdead)))
    (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead)) (.var (by csolo))

theorem matchSome_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem matchSome Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_matchSome)

theorem matchSome_eval : unitNoLeak (eval matchSome) = true := by decide

/-- The `some` branch read the payload's contents, `inj₁ ()`. -/
theorem matchSomeObs_eval :
    (match eval matchSomeObs with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-! ### A record with a list field

    let (r, u) = withbor (alloc {n = 0, items = []}) (Λ. λm.
                   let (m′, t) = swapField m items (λl. (7 :: l, ())); t; forget m′; ());
    u; let {n, items} = free r; freeNat n; freeList items

The field `items : L` is the common list (`CommonList.lean`); `swapField` runs `consC` on it
through `Mut 'a {n : N, items : L}`. -/

/-- `{n : N, items : L}`. -/
abbrev Bag : Shape := .node (.leaf natN) (.leaf clistL)

/-- `λl. (7 :: l, ())`. -/
def pushG : Expr := .val (.lam (.pair (consC (.val (num 7)) (.var 0)) unit'))

theorem d_pushG {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ pushG (.val (.lolli clistL (.tensor clistL .unit))) :=
  .lamV (.tensorI (.left (deadSplit hΓ))
    (d_consC (.right (deadSplit hΓ)) (.left (deadSplit hΓ)) (.cons hΓ)
      (d_num (.cons hΓ) 7) (.var (.here hΓ)))
    (.unitI (.cons hΓ)))

def pushBorrower : Expr :=
  .val (.lam (.val (.lam (.letpair (swapField Bag [true] (.var 0) pushG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))))

def mkBag : Expr := .pair (.val (num 0)) nilC

/-- `let {n, items} = free r; freeNat n; freeList items`, with `r` at index `i`. -/
def freeBag (i : Nat) : Expr :=
  recLet Bag (.app free' (.var i)) (.seq (.app freeNatE (.var 0)) (.app freeCE (.var 1)))

def bagProg : Expr :=
  .letpair (app2 withbor (.app alloc' mkBag) pushBorrower) (.seq (.var 0) (freeBag 1))

/-- The same run, returning the list after the push, as a pure list. -/
def bagObs : Expr :=
  .letpair (app2 withbor (.app alloc' mkBag) pushBorrower)
    (.seq (.var 0) (recLet Bag (.app free' (.var 1))
      (.seq (.app freeNatE (.var 0)) (.app toPureCE (.var 1)))))

theorem d_pushBorrower :
    CDerives LifeCtx.empty [] pushBorrower
      (.val (.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.mut (.var 0) Bag.valTy) (.box (.var 0) .unit)))) :=
  callbackW ok_empty rfl .nil <|
    letW (A := .mut (.var 0) Bag.valTy) (B := .unit)
      (swapField_wf (.var (by csolo)) rfl (fun h => d_pushG h)) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

theorem d_bagProg : CDerives LifeCtx.empty [] bagProg (.val .unit) :=
  letW (A := .ref Bag.valTy) (B := .unit)
    (appW d_pushBorrower
      (appW (appW (pairW (d_num (by cdead) 0) (d_nilC (by cdead))) (.alloc (by cdead)))
        (.withbor2 (A := Bag.valTy) (B := .unit) 0 (by cdead) rfl
          ⟨.top, LifeCtx.defines_of_wf rfl, .tensor (natN_outlives _ _) (clistL_outlives _ _)⟩
          (by simp [VFree, Shape.valTy, natN, natBody, clistL, FShape.ty])
          (by simp [VFree])))) <|
  seqW (.var (by csolo)) <|
  recEV Bag (part_split (.app free' (.var 1)) 0 _) (appW (.var (by csolo)) (.free (by cdead)))
    (seqW (appW (.var (by csolo)) (d_freeNat (by cdead)))
      (appW (.var (by csolo)) (d_freeC (by cdead))))

theorem bagProg_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem bagProg Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_bagProg)

set_option maxRecDepth 100000 in
theorem bagProg_eval : unitNoLeak (eval bagProg) = true := by decide

set_option maxRecDepth 100000 in
/-- After the push the list is `[7]`, and no cell is left. -/
theorem bagObs_eval : pureNoLeak (eval bagObs) = some [7] := by decide

end BoCa.Fig16.LogRel.Core

end
