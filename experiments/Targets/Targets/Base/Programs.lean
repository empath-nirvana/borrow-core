import Core.EffPrograms
import Targets.Base.Rows

/-!
# Base — answering implementations (DESIGN §2, D13)

An answering effect is implemented by a borrow (HandlersAsBorrows,
`Core/Handlers.lean`): the handler's state cell is lent as `Mut 'h S`, each operation is a
`withswap` on the borrowed state, and the clause resumes once, in tail position (`ansRun`,
`ansCall`).  The control form (decision 59) is `ctlForm`; capability passing on the spine
(`capPass`) relates the two.  I's `I4a` and the Instance's binary laws read them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag suspSig dFlag)
open BoCa.BoLo (performE)
open BoCa.Programs (alloc' free' app2)

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

end Targets

end
