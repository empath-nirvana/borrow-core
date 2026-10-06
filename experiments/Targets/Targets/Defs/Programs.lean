import Core.EffPrograms
import Targets.Defs.Effects

/-!
# Targets — answering implementations and the acceptance terms (DESIGN §2, D13–D14)

* **D13.** An answering effect is implemented by a borrow, following HandlersAsBorrows and
  `Core/Handlers.lean`: the handler's state cell is lent as `Mut 'h S`, each operation is a
  `withswap` on the borrowed state, and the clause resumes once, in tail position, with no
  continuation reified (`ansRun`, `ansCall`).  The control form (decision 59: state passed to each
  clause and at each resume) is `ctlForm`.  Capability passing on the spine (`capPass`) relates
  the two on bodies whose operations of the name are performed on the spine.
* **D14.** The survey's programs that tier 2 must accept, as closed Core terms (`at02`, `at04`,
  `at12`, `at17`), with their interpreter runs checked (`Targets/Restricted/Acceptance.lean`).
-/

noncomputable section

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag suspSig dFlag)
open BoCa.BoLo (performE)
open BoCa.Programs (alloc' free' app2)

/-! ### D13. Answering implementations -/

/-- An answering implementation: the state type, the operations `A_j ↠^lin B_j`, and each
operation's code `co_j : !U(S ⊗ A_j ⊸ F(S ⊗ B_j))`, closed. -/
structure AnsImpl where
  S  : VTy
  E  : List (VTy × VTy)
  co : List Val

/-- The operation call on the borrowed state:
`λp. let (m, a) = p in withswap m (λs. co (s, a))`, answering `(m, b)`. -/
def ansCall (co : Val) : Val :=
  ⟨.lam (.letpair (.var 0)
     (app2 withswap (.var 1) (.val (.lam (.app (.val co) (.pair (.var 0) (.var 1))))))), .lam⟩

/-- `with h(s₀) { body }`:
`c ← alloc s₀; f ← (Λ. λm. body); w ← withborU d; (c, r) ← w c f; (free c, r)`, the finaliser `d`
releasing the source on an unwind (`withborUE`), in the A-normal form Core's typing reads (the
shape of `Core/EffPrograms.lean`'s `failOutsideBody`).  `body` is typed in `m :: Γ`; inside the
callback it sits under `m`, the `Λ`'s dead slot and the cell, so its variables of `Γ` are shifted
past the latter two. -/
def ansRun (d s₀ body : Expr) : Expr :=
  bindE (.app alloc' s₀)
    (bindE (.val (.lam (.val (.lam (body.shift 2 1)))))
      (bindE (withborUE d)
        (.app (.val (.lam (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

/-- The clause of `co`: `λ(a, κ). λs. let (s', b) = co (s, a) in κ.resume b to f. f s'`. -/
def ctlClause (co : Val) : Val :=
  ⟨.lam (.letpair (.var 0) (.lam
    (.letpair (.app (.val co) (.pair (.var 0) (.var 2)))
      (bindE (.app (.app (.var 3) (.val (Val.inj₁ .unit))) (.var 0)) (.app (.var 0) (.var 2)))))),
   .lam⟩

/-- The answer clause: `λr. λs. (s, r)`. -/
def ctlRet : Val := ⟨.lam (.lam (.pair (.var 0) (.var 1))), .lam⟩

/-- A right-nested tuple of clauses. -/
def clausesV : List Val → Val
  | [] => .unit
  | c :: cs => Val.pair c (clausesV cs)

/-- `(handle_n e with ctlRet, ctlClause co_j …) s₀`, `e` closed. -/
def ctlForm (n : UInt32) (impl : AnsImpl) (s₀ e : Expr) : Expr :=
  bindE (bindE (.val (clausesV (impl.co.map ctlClause))) (bindE (.val ctlRet) (hndTerm n 0 1 e)))
    (bindE s₀ (.app (.var 1) (.var 0)))

/-- `n` is not the name literal of any `perform`, `raise` or `hnd` in the term. -/
def _root_.BoCa.Expr.OpFree (n : UInt32) : Expr → Prop
  | .app (.prim p) (.pair (.prim (.lit (.i32 m))) r) =>
      ((p = .perform ∨ p = .raise ∨ p = .hnd) → m ≠ n) ∧ r.OpFree n
  | .pair a b | .seq a b | .letpair a b | .app a b => a.OpFree n ∧ b.OpFree n
  | .inj₁ a | .inj₂ a | .lam a => a.OpFree n
  | .case a b c => a.OpFree n ∧ b.OpFree n ∧ c.OpFree n
  | _ => True

/-- `(j, a)` when the term is `perform (n, (j, a))` with the literal name `n`. -/
def _root_.BoCa.Expr.performOf (n : UInt32) : Expr → Option (UInt32 × Expr)
  | .app (.prim .perform) (.pair (.prim (.lit (.i32 n'))) (.pair (.prim (.lit (.i32 j))) a)) =>
      if n' = n then some (j, a) else none
  | _ => none

/-- The size of a term, counting every node once and a variable as `1`, so that shifting keeps it
(`size_shift`). -/
def _root_.BoCa.Expr.size : Expr → Nat
  | .var _ | .unit | .loc _ | .prim _ => 1
  | .pair a b | .seq a b | .letpair a b | .app a b => a.size + b.size + 1
  | .inj₁ a | .inj₂ a | .lam a => a.size + 1
  | .case a b c => a.size + b.size + c.size + 1

theorem size_shift (d : Nat) : ∀ (e : Expr) (c : Nat), (e.shift d c).size = e.size
  | .var i, c => by unfold Expr.shift; split <;> rfl
  | .unit, _ | .loc _, _ | .prim _, _ => rfl
  | .pair a b, c | .seq a b, c | .app a b, c => by
      simp only [Expr.shift, Expr.size, size_shift d a c, size_shift d b c]
  | .letpair a b, c => by
      simp only [Expr.shift, Expr.size, size_shift d a c, size_shift d b (c + 2)]
  | .inj₁ a, c | .inj₂ a, c => by simp only [Expr.shift, Expr.size, size_shift d a c]
  | .lam a, c => by simp only [Expr.shift, Expr.size, size_shift d a (c + 1)]
  | .case a b e, c => by
      simp only [Expr.shift, Expr.size, size_shift d a c, size_shift d b (c + 1),
        size_shift d e (c + 1)]

open Classical in
/-- **Capability passing on the spine.**  `k` is the borrowed state's index.  A `let` of
`perform (n, j) a` becomes `let (m', b) = ansCall co_j (m, a) in …`, the rest reading `m'` (its
other variables shifted past `m'`); an `n`-free tail forgets `m` first.  Outside the class it is
`none`.  Well-founded on `Expr.size`, which `shift` keeps. -/
def capPass (n : UInt32) (cos : List Val) : Nat → Expr → Option Expr
  | k, .app (.lam e') M =>
      match M.performOf n with
      | some (j, a) =>
          if a.OpFree n then
            (cos[j.toNat]?).bind fun co => (capPass n cos 1 (e'.shift 1 1)).map fun body =>
              .letpair (.app (.val (ansCall co)) (.pair (.var k) a)) body
          else none
      | none => if M.OpFree n then (capPass n cos (k + 1) e').map fun b => .app (.lam b) M
                else none
  | k, .seq v e' => if v.OpFree n then (capPass n cos k e').map (.seq v) else none
  | k, .letpair v e' =>
      if v.OpFree n then (capPass n cos (k + 2) e').map (.letpair v) else none
  | k, .case v e₁ e₂ =>
      if v.OpFree n then
        (capPass n cos (k + 1) e₁).bind fun b₁ => (capPass n cos (k + 1) e₂).map (.case v b₁)
      else none
  | k, e => if e.OpFree n then some (.seq (.app forget (.var k)) e) else none
termination_by _ e => e.size
decreasing_by
  all_goals first
    | (rw [size_shift]; simp only [Expr.size]; omega)
    | (simp only [Expr.size]; omega)

/-! ### D14. The acceptance terms -/

/-- `Foo : 1 ↠^lin 1`, the operation `0` of the name `5`. -/
def fooSig : OpSig := ⟨5, 0, .lin, .unit, .unit⟩
def fooE : Expr := performE (opArgE 5 0 (.val .unit))
/-- `Choose : 1 ↠^lin Flag`, the operation `0` of the name `6`. -/
def chooseSig : OpSig := ⟨6, 0, .lin, .unit, Flag⟩
def chooseE : Expr := performE (opArgE 6 0 (.val .unit))
/-- `Susp : 1 ↠^aff 1` is `suspSig`, the name `4` (`Core/EffPrograms.lean`). -/
def suspE : Expr := performE (opArgE 4 0 (.val .unit))

/-- A handler of the name `n` with the identity answer clause and the one clause `cl`. -/
def handleWith (n : UInt32) (cl : Expr) (e : Expr) : Expr :=
  bindE (.pair cl (.val .unit)) (bindE (.val (.lam (.var 0))) (hndTerm n 0 1 e))
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
def at02 : Expr := handleWith 5 resumeArg
  (lendCell (.inj₁ unit') (cb (bindE fooE (.seq (.var 0) (readThrough 1)))))
/-- **AT04** (`v.push(do choose())`, one-shot): `Choose`'s answer written through `m`. -/
def at04 : Expr := handleWith 6 resumeLeft
  (bindE (.app alloc' (.inj₂ unit'))
    (bindE (cb (bindE chooseE (writeThrough 1 0)))
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0)
            (bindE (.app free' (.var 1)) (.pair (.var 0) (.var 1))))))
          (.app (.app (.var 0) (.var 2)) (.var 1))))))
/-- **AT12** (`thread::scope` with the continuation dropped, single-threaded): the lend spans an
affine `Susp`; the handler cancels the continuation, and the lend's finaliser frees the cell
during the cancel. -/
def at12 : Expr := handleWith 4 cancelAns
  (lendCell (.inj₁ unit') (cb (bindE suspE (.seq (.var 0) (readThrough 1)))))
/-- **AT17** (a lend across a perform in a movable first-class continuation): the handler moves the
continuation into a cell and back, then resumes it. -/
def at17 : Expr := handleWith 5 storeResume
  (lendCell (.inj₁ unit') (cb (bindE fooE (.seq (.var 0) (readThrough 1)))))

end Targets

end
