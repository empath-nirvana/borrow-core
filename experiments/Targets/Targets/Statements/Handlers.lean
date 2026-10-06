import Targets.Statements.Interface

/-!
# Targets — P11, handler correctness (unary), and T2, the laws (binary) (DESIGN §6 P11, §3 T2)

**P11, World:** [W].  A handler means what its clauses say.  The unary parts are in the first
pass: the `[handle]` rule is sound at W (the handler is a model of its signature, and handling is
the induced map: initiality's existence half), and reduction is semantic identity (a pure head
step neither adds nor removes programs from `ewpW` at a protocol table).

**T2, World:** [prog], binary (contextual equivalence); the proof route goes through a binary
world [W₂].  The handler equations hold as contextual equivalences over the kernel: return,
operation, forwarding, the tail-resumptive law, algebraicity at linear and affine operations, the
capture laws β and η, hiding, fusion (at a composite-handler parameter, OQ-49), and Staton's ν/op
law (vacuous under static names, OQ-14).  **Out of the first pass** (user, 2026-10-02: "optional
and don't get pursued unless they become necessary for safety"); nothing is driven from it.

Literature: Plotkin–Pretnar, LMCS 2013 ("h(M) … is the unique homomorphism … from A+exc to M that
extends the map in1"; Def. 4.2, Prop. 4.3, Def. 4.5).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal hndE hndVal kappa
  clauseAt)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### P11 (unary) -/

/-- `handle_compatC` at W, at unr-free rows. -/
def HandleCompat (M : SemWorld) : Prop :=
  ∀ Δ Γ Γ₁ Γ₂ Γr Γc e S (E : List (Qual × VTy × VTy)) (n : UInt32) A R ir ic,
    Row.NU (Row.ofEff n E 0 ++ S) →
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.SplitP Γ₁ Γr Γc → Ctx.SoloP Γr ir (retTy S A R) →
    Ctx.SoloP Γc ic (clausesTy S R E) → n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    SemW₀ M Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A)) →
    SemW₀ M Δ Γ (hndTerm n ir ic e) (.comp (CTy.effOf S R))

/-- Reduction is semantic identity (unary): a pure, non-allocating head step neither adds nor
removes programs from `ewpW` at a protocol table. -/
def RedLaws (M : SemWorld) : Prop :=
  ∀ (K : Kont) a a' i (T : OpTabI (Idx M.Stk)) Q ρ, (∀ μ, Head (ℍ := ℍ) μ a μ a') →
    a.allocs = false →
    (ewpW (ℍ := ℍ) M i (K.plug a) (opTabW M T) Q ρ ↔ ewpW (ℍ := ℍ) M i (K.plug a') (opTabW M T) Q ρ)

/-- **P11** at W. -/
def P11 (M : SemWorld) : Prop := HandleCompat M ∧ RedLaws (ℍ := ℍ) M

/-! ### T2 (binary, out of the first pass) -/

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

end
