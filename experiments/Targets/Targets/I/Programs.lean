import Core.EffPrograms
import Targets.Base.RunProps
import Targets.Base.Programs

/-!
# The interaction — the composite programs (RESTRUCTURE §3.4)

The survey's programs that tier 2 must accept, as closed Core terms (D14: `at02`, `at04`, `at12`,
`at17`; and `genSelf`), with their interpreter runs checked (`Support`'s interpreter has no theorem
tying it to `Step1`, so these checks are evidence); the rejected programs AT05, AT06, AT07, AT08 and
AT13; `AcceptedAt`, `Tier2Programs`, `Rejects`, `RejectsAT07`.  `I1Prog`, `I2Prog`: I1 and I2 at
the program level.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag suspSig dFlag)
open BoCa.BoLo (performE)
open BoCa.Programs (alloc' free' app2)

/-- `Foo : 1 ↠^lin 1`, the operation `0` of the name `5`. -/
def fooSig : OpSig := ⟨5, 0, .lin, .unit, .unit, .ret .unit⟩

def fooE : Expr := performE (opArgE 5 0 (.val .unit))

/-- `Choose : 1 ↠^lin Flag`, the operation `0` of the name `6`. -/
def chooseSig : OpSig := ⟨6, 0, .lin, .unit, Flag, .ret .unit⟩

def chooseE : Expr := performE (opArgE 6 0 (.val .unit))

/-- `Susp : 1 ↠^aff 1` is `suspSig`, the name `4` (`Core/EffPrograms.lean`). -/
def suspE : Expr := performE (opArgE 4 0 (.val .unit))

/-- A handler of the name `n` with the identity answer clause and the one clause `cl`, its
operation's qualifier `q`. -/
def handleWith (n : UInt32) (q : Qual) (cl : Expr) (e : Expr) : Expr :=
  bindE (.pair cl (.val .unit)) (bindE (.val (.lam (.var 0))) (hndTerm n [q] 0 1 e))

/-- The clause that resumes with the argument. -/
def resumeArg : Expr :=
  .val (.lam (.letpair (.var 0) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.var 1))))

/-- The clause that resumes with `inj₁ ()`. -/
def resumeLeft : Expr :=
  .val (.lam (.letpair (.var 0)
    (.seq (.var 1) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val (.inj₁ .unit))))))

/-- The clause that cancels the continuation and answers `inj₂ ()`. -/
def cancelAns : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1)
    (bindE (.app (.var 0) (.val (.inj₂ .unit))) (.seq (.var 0) (.inj₂ unit'))))))

/-- The clause that stores the continuation in a cell, takes it back, and resumes it at `()`. -/
def storeResume : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1)
    (bindE (.app alloc' (.var 0)) (bindE (.app free' (.var 0))
      (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit)))))))

/-- `dupFlag : !U(Flag ⊸ F(Flag ⊗ Flag))`: the flag and a copy. -/
def dupFlag : Expr :=
  .val (.lam (.case (.var 0) (.seq (.var 0) (.pair (.inj₁ unit') (.inj₁ unit')))
                             (.seq (.var 0) (.pair (.inj₂ unit') (.inj₂ unit')))))

/-- Read the flag through `m` (index `i`): `let (m', b) = withswap m dupFlag in forget m'; b`. -/
def readThrough (i : Nat) : Expr :=
  .letpair (app2 withswap (.var i) dupFlag) (.seq (.app forget (.var 1)) (.var 0))

/-- Write `c` (index `j`) through `m` (index `i`), answering the old flag. -/
def writeThrough (i j : Nat) : Expr :=
  .letpair (app2 withswap (.var i) (.val (.lam (.pair (.var (j + 1)) (.var 0)))))
    (.seq (.app forget (.var 1)) (.var 0))

/-- A callback `Λ. λm. body`. -/
def cb (body : Expr) : Expr := .val (.lam (.val (.lam body)))

/-- Lend a fresh cell holding `init` to the closed callback `f` with `withborU dFlag`, then free
the cell and answer `f`'s result, in A-normal form:
`c ← alloc init; g ← f; w ← withborU dFlag; (c, r) ← w c g; dropB (free c); r`. -/
def lendCell (init : Expr) (f : Expr) : Expr :=
  bindE (.app alloc' init)
    (bindE f
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0) (.seq (dropB (.app free' (.var 1))) (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

/-- **AT02** (Yarrow's region example, one-shot): `m` held across `Foo`, then read. -/
def at02 : Expr := handleWith 5 .lin resumeArg
  (lendCell (.inj₁ unit') (cb (bindE fooE (.seq (.var 0) (readThrough 1)))))

/-- **AT04** (`v.push(do choose())`, one-shot): `Choose`'s answer written through `m`. -/
def at04 : Expr := handleWith 6 .lin resumeLeft
  (bindE (.app alloc' (.inj₂ unit'))
    (bindE (cb (bindE chooseE (writeThrough 1 0)))
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0)
            (bindE (.app free' (.var 1)) (.pair (.var 0) (.var 1))))))
          (.app (.app (.var 0) (.var 2)) (.var 1))))))

/-- **AT12** (`thread::scope` with the continuation dropped, single-threaded): the lend spans an
affine `Susp`; the handler cancels the continuation, and the lend's finaliser frees the cell
during the cancel. -/
def at12 : Expr := handleWith 4 .aff cancelAns
  (lendCell (.inj₁ unit') (cb (bindE suspE (.seq (.var 0) (readThrough 1)))))

/-- **AT17** (a lend across a perform in a movable first-class continuation): the handler moves the
continuation into a cell and back, then resumes it. -/
def at17 : Expr := handleWith 5 .lin storeResume
  (lendCell (.inj₁ unit') (cb (bindE fooE (.seq (.var 0) (readThrough 1)))))


end Targets

namespace Targets
open BoCa

/-- **AT02 runs**: the flag read through the lend after `Foo` resumes, and no cell left. -/
theorem at02_eval :
    (match eval at02 with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **AT04 runs**: the new content `inj₁ ()` (`Choose`'s answer, written through the lend) beside
the old `inj₂ ()`, and no cell left. -/
theorem at04_eval :
    (match eval at04 with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- **AT12 runs**: the handler cancels the continuation that holds the lend; the lend's finaliser
frees the cell during the cancel; the answer is `inj₂ ()`, and no cell left. -/
theorem at12_eval :
    (match eval at12 with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **AT17 runs**: the continuation holding the lend is moved into a cell and back, then resumed;
the answer is `inj₁ ()`, and no cell left. -/
theorem at17_eval :
    (match eval at17 with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag storeCancel)

/-- **I1 at the program level**: suspensions stored in a cell, moved, and then cancelled
(`storeCancel`) or resumed (`at17`). -/
def I1Prog (J : TypingJ) : Prop :=
  TypedSound (ℍ := ℍ) J storeCancel .unit ∧ TypedSound (ℍ := ℍ) J at17 Flag

/-- **I2 at the program level**: lends spanning a once-resuming operation (`at02`, `at04`) and an
affine one whose continuation is cancelled (`at12`). -/
def I2Prog (J : TypingJ) : Prop :=
  TypedSound (ℍ := ℍ) J at02 Flag ∧ TypedSound (ℍ := ℍ) J at04 (.tensor Flag Flag) ∧
  TypedSound (ℍ := ℍ) J at12 Flag

end Targets

/-! ### The tier-2 program a generator gives: it borrows its own state (RESTRUCTURE §3.4) -/

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag dFlag)
open BoCa.BoLo (performE)
open BoCa.Programs (alloc' free' app2)

/-- `Yield : Flag ↠^aff 1`, the operation `0` of the name `7`. -/
def yieldFlagE (v : Expr) : Expr := performE (opArgE 7 0 v)

/-- A handler of the name `n` with the return clause `r` and the one clause `cl`, its operation's
qualifier `q`. -/
def handleWithRet (n : UInt32) (q : Qual) (r cl : Expr) (e : Expr) : Expr :=
  bindE (.pair cl (.val .unit)) (bindE r (hndTerm n [q] 0 1 e))

/-- `yield (x, k) ⇒ resume k () to r. case x of inl _ ⇒ r | inr _ ⇒ tt`: the yielded flags, or-ed. -/
def orClause : Expr :=
  .val (.lam (.letpair (.var 0) (bindE (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit))
    (.case (.var 2) (.var 1) (.inj₂ unit')))))

/-- The generator's body, under the lend `m` of its state cell: read the flag through `m` (keeping
the lend), yield it, read it again, yield it. -/
def genBody : Expr :=
  .letpair (app2 withswap (.var 0) dupFlag)
    (bindE (yieldFlagE (.var 0))
      (.seq (.var 0)
        (.letpair (app2 withswap (.var 2) dupFlag) (.seq (.app forget (.var 1)) (yieldFlagE (.var 0))))))

/-- **A generator borrowing its own state** (`corpus/reject/gen-self-borrow.bc`): its state cell,
holding `tt`, is lent to the generator's body across two resumed yields, and read through the lend
before each; the handler or-s the yielded flags and answers `ff` when the generator returns.  The
lend here is `withbor` (2)'s (`Mut`, as `at02`'s); the design's `Imm` form (6.64, read by
`withload`) is RESTRUCTURE §Unresolved's. -/
def genSelf : Expr :=
  handleWithRet 7 .aff (.val (.lam (.inj₁ unit'))) orClause (lendCell (.inj₂ unit') (cb genBody))

/-- **`genSelf` runs**: the or of the yielded flags, `tt`, and no cell left. -/
theorem genSelf_eval :
    (match eval genSelf with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-! ### The rejections (the REJECT side, RESTRUCTURE §3.4) -/

/-- **AT05**: two `Mut 'h S` taken from one handler's state cell: the borrow form of an answering
handler whose body uses its capability `m` twice.  `Mut` has no copy rule. -/
def at05 : Expr := ansRun dFlag (.inj₁ unit') (.pair (.var 0) (.var 0))

/-- **AT06**: a clause that writes a place the suspended body uses: the clause captures the cell
`c`, which the body also releases.  Clauses are `!U`, so they capture only persistent values, and
`c` is linear. -/
def at06 : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (handleWith 5 .lin (.val (.lam (.letpair (.var 0) (.seq (dropB (.app free' (.var 3)))
        (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit))))))
      (bindE fooE (dropB (.app free' (.var 3)))))

/-- **AT08**: a continuation in a shared cell, read twice: the clause stores `κ` in a cell, loads
it twice and resumes both copies.  `kTy` at `lin` and `aff` is neither droppable nor persistent. -/
def at08 : Expr :=
  handleWith 5 .lin (.val (.lam (.letpair (.var 0)
    (bindE (.app alloc' (.var 0))
      (bindE (.app (.val (.prim .load)) (.var 0))
        (bindE (.app (.val (.prim .load)) (.var 1))
          (.seq (dropB (.app free' (.var 2)))
            (.seq (.app (.app (.var 1) (.val (.inj₁ .unit))) (.val .unit))
              (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit)))))))))) fooE

/-- **AT13**: `forget κ`: a `lin` or `aff` continuation has no weakening, and the `forget`
constants are at `Imm`, `Mut`, `!` and `Unk`; discard is an explicit cancel. -/
def at13 : Expr := handleWith 5 .lin (.val (.lam (.letpair (.var 0) (.seq (.app forget (.var 0)) unit')))) fooE

/-- **AT07**: a continuation capturing a lend of `x`, stored past `x`'s release, then resumed: the
handler answers `κ` itself (suspended inside the callback that reads through the lend), the program
frees `x`, and resumes `κ`, whose read then meets a freed cell. -/
def at07 : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (bindE (handleWithRet 5 .lin (.val (.lam (.var 0))) (.val (.lam (.letpair (.var 0) (.var 0))))
        (bindE (cb (bindE fooE (.seq (.var 0) (readThrough 1))))
          (bindE (withborUE dFlag) (.app (.app (.var 0) (.var 4)) (.var 1)))))
      (.seq (dropB (.app free' (.var 1))) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit))))

/-- **AT07 runs into a freed cell**: the interpreter stops at a use after free. -/
theorem at07_eval :
    (match eval at07 with
      | .stuck .useAfterFree => true
      | _ => false) = true := by decide

/-! ### Accepted, with an answer -/

/-- **Accepted at a typing system, with a computed answer**: typed at a data answer, every run
under the platform with no operation safe and terminating with the memory empty, and **some**
complete run answering `v` (stated on one run, so it rests on no machine lemma). -/
def AcceptedAt (J : TypingJ) (e : Expr) (A : VTy) (v : Val) : Prop :=
  J.closed e (.ret A) ∧ SafeRuns (ℍ := ℍ) Platform.none A e ∧ Terminates (ℍ := ℍ) Platform.none A e ∧
    ∃ cs c, PRun (ℍ := ℍ) Platform.none (init _ e :: cs) ∧ (init _ e :: cs).getLast? = some c ∧
      Final Platform.none A c ∧ c.e = .val v

/-- **The tier-2 programs, accepted with their answers** (at `c = .any`): the lends that span a
resuming or cancelled suspension.  `at04` stands in for the async read into a local buffer (the
lead-axis form passes the lend to the operation, which is OQ-56's, RESTRUCTURE §7 Q5). -/
def Tier2Programs (J : TypingJ) : Prop :=
  AcceptedAt (ℍ := ℍ) J at02 Flag (Val.inj₁ .unit) ∧
  AcceptedAt (ℍ := ℍ) J at04 (.tensor Flag Flag) (Val.pair (Val.inj₁ .unit) (Val.inj₂ .unit)) ∧
  AcceptedAt (ℍ := ℍ) J at12 Flag (Val.inj₂ .unit) ∧
  AcceptedAt (ℍ := ℍ) J at17 Flag (Val.inj₁ .unit) ∧
  AcceptedAt (ℍ := ℍ) J genSelf Flag (Val.inj₂ .unit)

/-- **The rejections that pin soundness, statically**: no type at all. -/
def Rejects (J : TypingJ) : Prop :=
  (∀ C, ¬ J.closed at05 C) ∧ (∀ C, ¬ J.closed at06 C) ∧ (∀ C, ¬ J.closed at08 C) ∧
    (∀ C, ¬ J.closed at13 C)

/-- **AT07's rejection, semantic** (a lemma derived from `Sound J`, to build): its run is stuck under
every platform, so a sound typing system does not type it at the types `Sound` covers (a data
answer on a row a respecting platform answers). -/
def RejectsAT07 (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (S : Row) (A : VTy), DivFree S A → RowLe S P.ops →
    ¬ J.closed at07 (CTy.effOf S A)

end Targets

end
