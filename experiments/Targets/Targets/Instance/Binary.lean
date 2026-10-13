import Core.Fundamental
import Targets.Base.Ctx
import Targets.Base.Programs

/-!
# The Instance — A₂ at our instance: the binary laws over Core, stated (RESTRUCTURE §1.7, §4.5)

Out of the first pass (U22: "optional and don't get pursued unless they become necessary for
safety").  T2: return, operation, forwarding, the tail-resumptive law, algebraicity, capture β
and η, hiding, fusion at a composite-handler parameter, Staton's ν/op law; T3: tunnelling,
representation independence, encapsulation.  They read base's `CtxEquiv`, `thunkF`, `AnsImpl`, `ctlForm` and
`clausesV`, and no I.

Literature: Plotkin–Pretnar, LMCS 2013 (Def. 4.2, Prop. 4.3, Def. 4.5); Zhang–Myers, POPL 2019
(Example 1, Thm 1, Thm 3).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal hndE hndVal kappa
  clauseAt)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `λ(a, k). c a to b. k.resume b`. -/
def tailClause (c : Val) : Val :=
  ⟨.lam (.letpair (.var 0) (bindE (.app (.val c) (.var 1))
     (.app (.app (.var 1) (.val (Val.inj₁ .unit))) (.var 0)))), .lam⟩

/-- `n` replaced by `n'` as the name literal of every `perform`, `raise` and `hnd` of the term. -/
def _root_.BoCa.Expr.renameOp (n n' : UInt32) : Expr → Expr
  | .app (.prim p) (.pair (.prim (.lit (.i32 m))) r) =>
      .app (.prim p) (.pair (.prim (.lit (.i32
        (if (p = .perform ∨ p = .raise ∨ p = .hnd) ∧ m = n then n' else m)))) (r.renameOp n n'))
  | .var i => .var i
  | .unit => .unit
  | .loc ℓ => .loc ℓ
  | .prim p => .prim p
  | .pair a b => .pair (a.renameOp n n') (b.renameOp n n')
  | .seq a b => .seq (a.renameOp n n') (b.renameOp n n')
  | .letpair a b => .letpair (a.renameOp n n') (b.renameOp n n')
  | .app a b => .app (a.renameOp n n') (b.renameOp n n')
  | .inj₁ a => .inj₁ (a.renameOp n n')
  | .inj₂ a => .inj₂ (a.renameOp n n')
  | .lam a => .lam (a.renameOp n n')
  | .case a b c => .case (a.renameOp n n') (b.renameOp n n') (c.renameOp n n')

def LawRet (J : TypingJ) (P : Platform) : Prop :=
  ∀ n hr hs (v : Val) S R, J.closed (hndE (hndVal n hr hs) (.val v)) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R) (thunkF (hndE (hndVal n hr hs) (.val v)))
      (thunkF (.app (.val hr) (.val v)))

def LawOp (J : TypingJ) (P : Platform) : Prop :=
  ∀ n i hr hs c (v : Val) (K : Kont) S R, K.HasHnd n = false → clauseAt hs.1 i.toNat = some c →
    J.closed (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R)
      (thunkF (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))))
      (thunkF (.app (.val c) (.pair (.val v) (kappa n (hndVal n hr hs) K))))

def LawFwd (J : TypingJ) (P : Platform) : Prop :=
  ∀ n m i hr hs (v : Val) (K : Kont) S R, m ≠ n → K.HasHnd m = false →
    J.closed (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload m i v))))) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R)
      (thunkF (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload m i v))))))
      (thunkF (bindE (performE (.val (opPayload m i v)))
        (hndE (hndVal n hr hs) ((K.shift 1 0).plug (.var 0)))))

def LawTail (J : TypingJ) (P : Platform) : Prop :=
  ∀ n i hr hs c (v : Val) (K : Kont) S R, K.HasHnd n = false →
    clauseAt hs.1 i.toNat = some (tailClause c) →
    J.closed (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R)
      (thunkF (hndE (hndVal n hr hs) (K.plug (performE (.val (opPayload n i v))))))
      (thunkF (hndE (hndVal n hr hs) (K.plug (.app (.val c) (.val v)))))

/-- Algebraicity: an operation commutes with the `let` it is sequenced in, at `lin`/`aff`. -/
def LawAlg (J : TypingJ) (P : Platform) : Prop :=
  ∀ n i (v : Val) (o : OpSig) M N S R, Row.find S n i = some o → o.abort = false → o.q ≠ .unr →
    J.closed (bindE (bindE (performE (.val (opPayload n i v))) M) N) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R)
      (thunkF (bindE (bindE (performE (.val (opPayload n i v))) M) N))
      (thunkF (bindE (performE (.val (opPayload n i v))) (bindE M (N.shift 1 1))))

/-- β for capture: resuming `κ` at `w` is the frozen computation at `w` under its handler. -/
def CapBeta (J : TypingJ) (P : Platform) : Prop :=
  ∀ n H K (w : Val) S R, J.closed (hndE H (K.plug (.val w))) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R)
      (thunkF (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)))
      (thunkF (hndE H (K.plug (.val w))))

/-- The forwarding clause of operation `j`, re-performed as `n'`:
`λ(a, k). perform (n', j) a to b. k.resume b`. -/
def fwdClause (n' : UInt32) (j : Nat) : Val :=
  ⟨.lam (.letpair (.var 0) (bindE (performE (opArgE n' (UInt32.ofNat j) (.var 1)))
     (.app (.app (.var 1) (.val (Val.inj₁ .unit))) (.var 0)))), .lam⟩

/-- The forwarding handler of `n`'s operations `E`, to `n'`. -/
def fwdH (n n' : UInt32) (E : List (Qual × VTy × VTy)) : Val :=
  hndVal n ⟨.lam (.var 0), .lam⟩ (clausesV ((List.range E.length).map (fwdClause n')))

/-- η for capture, up to renaming the name (`[handle]` forbids the handled name in the result row,
so `fwdH n n` is not typed; OQ-27's typing check). -/
def CapEta (J : TypingJ) (P : Platform) : Prop :=
  ∀ n n' E e S R, n ≠ n' → J.closed (hndE (fwdH n n' E) e) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R) (thunkF (hndE (fwdH n n' E) e)) (thunkF (e.renameOp n n'))

/-- **A simulation between two answering implementations** of one signature: related states and
one argument run, by each implementation's operation, to one answer and related next states.  A
syntactic hypothesis: runs of the machine, no binary relation. -/
def AnsSim (impl₁ impl₂ : AnsImpl) (Rel : Val → Val → Prop) : Prop :=
  impl₁.E = impl₂.E ∧ List.Forall₂ (fun (c₁ c₂ : Val) =>
    ∀ s₁ s₂ a, Rel s₁ s₂ → ∀ μ μ₁ t₁ b,
      Steps (ℍ := ℍ) μ (.app (.val c₁) (.val (Val.pair s₁ a))) μ₁ (.val (Val.pair t₁ b)) →
      ∃ μ₂ t₂, Steps (ℍ := ℍ) μ (.app (.val c₂) (.val (Val.pair s₂ a))) μ₂ (.val (Val.pair t₂ b)) ∧
        Rel t₁ t₂) impl₁.co impl₂.co

/-- The control form, its final state observed by `o`: `ctlForm … to (s, r). o s to w. (w, r)`. -/
def ctlObs (n : UInt32) (impl : AnsImpl) (s₀ e : Expr) (o : Val) : Expr :=
  bindE (ctlForm n impl s₀ e)
    (.letpair (.var 0) (bindE (.app (.val o) (.var 1)) (.pair (.var 0) (.var 1))))

/-- **Hiding** (the binary content of 6.66; I5's `AntiFrameW` is the unary half): two answering
handlers of one name whose states are related by a simulation, started at related states and
observed by observers that agree on related states, are contextually equivalent. -/
def Hiding (J : TypingJ) (P : Platform) : Prop :=
  ∀ (impl₁ impl₂ : AnsImpl) (Rel : Val → Val → Prop) (n : UInt32) (s₁ s₂ : Val) (e : Expr)
    (o₁ o₂ : Val) (S : Row) (R O : VTy),
    AnsSim (ℍ := ℍ) impl₁ impl₂ Rel → AnsSim (ℍ := ℍ) impl₂ impl₁ (flip Rel) → Rel s₁ s₂ →
    (∀ t₁ t₂ μ w, Rel t₁ t₂ →
      ((∃ μ', Steps (ℍ := ℍ) μ (.app (.val o₁) (.val t₁)) μ' (.val w)) ↔
       (∃ μ', Steps (ℍ := ℍ) μ (.app (.val o₂) (.val t₂)) μ' (.val w)))) →
    J.closed (ctlObs n impl₁ (.val s₁) e o₁) (CTy.effOf S (.tensor O R)) →
    J.closed (ctlObs n impl₂ (.val s₂) e o₂) (CTy.effOf S (.tensor O R)) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S (.tensor O R))
      (thunkF (ctlObs n impl₁ (.val s₁) e o₁)) (thunkF (ctlObs n impl₂ (.val s₂) e o₂))

/-- **Fusion**, at the composite-handler construction `fuse` (OQ-49), a parameter. -/
def LawFusion (J : TypingJ) (P : Platform) (fuse : Val → Val → Val) : Prop :=
  ∀ H₁ H₂ e S R, J.closed (hndE H₁ (hndE H₂ e)) (CTy.effOf S R) →
    J.closed (hndE (fuse H₁ H₂) e) (CTy.effOf S R) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S R) (thunkF (hndE H₁ (hndE H₂ e)))
      (thunkF (hndE (fuse H₁ H₂) e))

/-- **Staton's ν/op law** needs generative instances (OQ-14 (b)).  Under static names there is no
`ν`, and the law is `True`; it is restated if OQ-14 (b) is adopted. -/
def LawNuOp (_J : TypingJ) (_P : Platform) : Prop := True

/-- **T2.** -/
def Laws (J : TypingJ) (fuse : Val → Val → Val) : Prop :=
  ∀ P : Platform, P.Respects → LawRet (ℍ := ℍ) J P ∧ LawOp (ℍ := ℍ) J P ∧ LawFwd (ℍ := ℍ) J P ∧
    LawTail (ℍ := ℍ) J P ∧ LawAlg (ℍ := ℍ) J P ∧ CapBeta (ℍ := ℍ) J P ∧ CapEta (ℍ := ℍ) J P ∧
    Hiding (ℍ := ℍ) J P ∧ LawFusion (ℍ := ℍ) J P fuse ∧ LawNuOp J P


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (performE hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `f`'s type at the row `S`: `U(U(A ⊸ F_S B) ⊸ F_S R)`. -/
def hofTy (A B R : VTy) (S : Row) : VTy :=
  .thunk (.arr (.thunk (.arr A (CTy.effOf S B))) (CTy.effOf S R))

/-- No `hnd (n, …)` occurs in the term. -/
def _root_.BoCa.Expr.HndFree (n : UInt32) : Expr → Prop
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) r) => m ≠ n ∧ r.HndFree n
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HndFree n ∧ b.HndFree n
  | .inj₁ a | .inj₂ a | .lam a => a.HndFree n
  | .case a b c => a.HndFree n ∧ b.HndFree n ∧ c.HndFree n
  | _ => True

/-- **Tunnelling** (Zhang–Myers, Example 1).  `f` is typed once, polymorphic in its callback's row
`ρ`; the name `n` is fresh for `f`.  Handing `f` the pure `λa. c a` at `ρ := []` is equivalent to
handing it `λa. perform (n, 0) a` at `ρ := {n}` and handling `n` outside by a clause that answers
with `c`: even an `f` that handles effects of its own cannot intercept `n`. -/
def Tunnel (J : TypingJ) (P : Platform) : Prop :=
  ∀ (f c : Val) (ρ : RVar) (k : RowCon) (A B R : VTy) (n : UInt32),
    let op : OpSig := ⟨n, 0, .lin, A, B⟩
    n ≠ 0 → k.cls.Admits [] → k.cls.Admits [op] → k.adm op →
    J [(ρ, k)] LifeCtx.empty (fun _ => []) (.val f) (fun η => .val (hofTy A B R (η ρ))) →
    J.at LifeCtx.empty [] (.val c) (.val (.bang (.thunk (.arr A (.ret B))))) →
    (f.1).HndFree n →
    CtxEquiv (ℍ := ℍ) J P (.ret R)
      (thunkF (.app (.val f) (.val ⟨.lam (.app (.val c) (.var 0)), .lam⟩)))
      (thunkF (hndE (hndVal n ⟨.lam (.var 0), .lam⟩ (Val.pair (tailClause c) .unit))
        (.app (.val f) (.val ⟨.lam (performE (opArgE n 0 (.var 0))), .lam⟩))))

/-- **Representation independence**: T2's `Hiding`, at answering handlers, whose operations are the
only access to their states. -/
abbrev RepInd (J : TypingJ) (P : Platform) : Prop := Hiding (ℍ := ℍ) J P

/-- **Encapsulation**: two closed computations at a data answer, every effect of each handled
inside it, that every platform observes alike, are contextually equivalent. -/
def Encap (J : TypingJ) (P : Platform) : Prop :=
  ∀ e₁ e₂ A, A.Data → J.closed e₁ (.ret A) → J.closed e₂ (.ret A) →
    (∀ P' : Platform, P'.Respects → Obs (ℍ := ℍ) P' A e₁ = Obs (ℍ := ℍ) P' A e₂) →
    CtxEquiv (ℍ := ℍ) J P (.ret A) (thunkF e₁) (thunkF e₂)

/-- **T3.** -/
def Abstraction (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → Tunnel (ℍ := ℍ) J P ∧ RepInd (ℍ := ℍ) J P ∧ Encap (ℍ := ℍ) J P

end Targets

end
