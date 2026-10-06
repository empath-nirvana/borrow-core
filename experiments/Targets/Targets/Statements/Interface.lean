import Targets.Statements.Device
import Targets.Defs.Programs
import Targets.Defs.Ctx

/-!
# Targets — the interaction interface I1–I5 (DESIGN §5)

**World:** [W], at the end state's `M`; I2's spanning typing rules, I3.b/I3.c and I4 are [prog].

* **I1** (`I1`): a suspension is a value of the resource world.  At a stop at a resuming
  operation, the share the stop owes its continuation, closed by the handler that catches the
  stop, is a value of `kTy`.
* **I2** (`I2`): capture and resume preserve the invariant, including lends that span the
  suspension.  A preservation statement at the two constructs: every configuration a run ends in
  arises, the frames suspended computations hold counted (`Arises`); the visible frames at a run's
  end are those at its entry (`StopVisible`); the continuation is resumed at every future index
  (`ShareResume`); [TR] 6.64 and 6.65 hold at W over `ewpW` with the lend quantified once at the
  callback's start (`FramesW`); and the six unwinding borrow constants are sound at the spanning
  rows (`SpanBorrows`).  Tier 2's typing pin is `Tier2Pinned`.  No conjunct mentions termination.
* **I3** (`I3`, `FinaliserOrder`, `NoInterception`): drop finalises exactly once.  The share's
  cancel conjunct at W with an option-neutral closing clause (`ShareCancel`); over complete runs,
  a cancel or an unwind fires the frozen finalisers once each, innermost first; no typed program
  can intercept a cancel.
* **I4** (`I4a`, `I4Typing`, `I4c`): answering effects are borrows.
* **I5** (`I5`): the unary capture laws β, hiding ([TR] 6.66 at W) and the frame.

The freeze binder (I2.c) is a target beside done: `Statements/Binder.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal hndE hndVal kappa
  ccatchE cfinE ubindE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ## I1. A suspension is a value of the resource world -/

/-- **I1.** -/
def I1 (M : SemWorld) : Prop :=
  ∀ (S : Row) (n : UInt32) (E : List (Qual × VTy × VTy)) (R : VTy) (δ : LSub) (hr hs : Val)
    (j : UInt32) (o : OpSig) (K : Kont) (i : Idx M.Stk) (ρ : WRes),
    n ≠ 0 → (∀ o' ∈ S, o'.n ≠ n) → Row.NU (Row.ofEff n E 0 ++ S) →
    Row.find (Row.ofEff n E 0) n j = some o → o.abort = false →
    M.share (rowTabW M (Row.ofEff n E 0 ++ S) δ) (entW M δ o) n i K
      (fun i' t => ewpW (ℍ := ℍ) M i' (hndE (hndVal n hr hs) t) (opTabW M (rowTabW M S δ))
        (fun i'' v => M.val true R i'' δ v)) ρ →
    M.val true (kTy S R o.q o.B) i δ ⟨kappa n (hndVal n hr hs) K, by unfold kappa; exact .lam⟩ ρ

/-! ## I2. Capture and resume preserve the invariant, including lends that span the suspension -/

/-- OQ-56's question: which operations a borrow callback's row may hold, given the context and the
lend's variable. -/
abbrev OpAdm := LifeCtx → LifeVar → OpSig → Prop

/-- OQ-56 (a), R-CLOSEDOP (`Row.Unwind`'s conditions): the operation's types are free of `'x` and
outlive every lifetime. -/
def admClosedOp : OpAdm := fun _ x o =>
  ¬ VFree x o.A ∧ ¬ VFree x o.B ∧ (∀ Δ a, VOutlives Δ a o.A) ∧ (∀ Δ a, VOutlives Δ a o.B)

/-- **The lower bound on `Adm`**: it admits at least what today's unwinding constants admit. -/
def AdmExtends (Adm : OpAdm) : Prop := ∀ Δ x o, admClosedOp Δ x o → Adm Δ x o

/-- A row a lend may span: every operation named, no resuming operation unrestricted, and every
operation admitted. -/
def RowSpan (Adm : OpAdm) (Δ : LifeCtx) (x : LifeVar) (S : Row) : Prop :=
  ∀ o ∈ S, o.n ≠ 0 ∧ (o.abort = true ∨ o.q ≠ .unr) ∧ Adm Δ x o

/-- The entries of a table of class `c` with no abortive entry: resuming, unr-free, and linear at
`.resumeOnce`; at `.abortive` there is no such entry, so the table is empty. -/
def OpTabI.Resuming {I : Type} (c : RowClass) (T : OpTabI I) : Prop :=
  ∀ n j en, T n j = some en → en.abort = false ∧ en.q ≠ .unr ∧ c ≠ .abortive ∧
    (c = .resumeOnce → en.q = .lin)

/-- **I2, capture**: every configuration W reaches is a tagged `TW` world over the visible and the
held frames and records. -/
def Arises (M : SemWorld) : Prop :=
  ∀ fρ ps i, M.Fam fρ ps i →
    ∃ ps₀ ls₀, (∀ p, p ∈ ps₀ ↔ p ∈ ps ∨ p ∈ (M.held i).1) ∧
      (∀ x, x ∈ ls₀ ↔ x ∈ i.1 ∨ x ∈ (M.held i).2) ∧
      TW fρ ps₀ (rsOf ls₀) ∧ Tagged fρ ps₀ ls₀

/-- **I2, the stop's role**: at every end of a run the visible frames and records are those at its
entry. -/
def StopVisible (M : SemWorld) : Prop :=
  ∀ ps i ps' i' t, M.Stop (ps, i) (ps', i') t →
    (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ i'.1 ↔ x ∈ i.1)

/-- **I2, resume**: `contShare`'s resume conjunct at W, at non-`unr` entries. -/
def ShareResume (M : SemWorld) : Prop :=
  ∀ T en n i K Φ ρ, M.share T en n i K Φ ρ → en.q ≠ .unr → ∀ i', M.Ext i i' ρ →
    ∀ w : Val, (en.PB i' w ─⋆ Φ i' (Kont.plug K (.val w))) ρ

/-- **6.65 at W at an abortive table** (`ewpTS_M_frameU` at W). -/
def MutFrameUW (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (β : Life), Tb.Abortive →
    (∀ i w σ, M.val true A i δ w σ → σ.InStratum β) →
    ∀ (v : Val) (e : Expr) (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp),
      Entails
        (ptoOwn l v ⋆ M.val true A i δ v ⋆
          fresh (fun α => ptoMutSW M l α i (fun i₀ => M.val true A i₀ δ) ─⋆
            wpGW (ℍ := ℍ) M i e (fun i'' t =>
              box α (all fun w => ptoOwn l w ─⋆ (M.val true A i'' δ w ─⋆ ewpPostW Tb Q i'' t)))))
        (ewpW (ℍ := ℍ) M i e Tb Q)

/-- **6.64 at W at an abortive table** (`ewpTS_I_frameU` at W). -/
def ImmFrameUW (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (v : Val) (e : Expr)
    (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp), Tb.Abortive → AdmWf A δ →
    (∀ i₁ i₂ t ρ, M.Ext i₁ i₂ ρ → ewpPostW Tb Q i₁ t ρ → ewpPostW Tb Q i₂ t ρ) →
    Entails
      (ptoOwn l v ⋆ M.val true A i δ v ⋆
        fresh (fun α ρ => ∀ ls', AddAt i.1 ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = A ∧ r.δ = δ) →
          (ptoImmSW M l α (ls', i.2) (fun i₀ => M.val true A i₀ δ) ─⋆
            wpGW (ℍ := ℍ) M (ls', i.2) e (fun i'' t =>
              box α (ptoOwn l v ─⋆ (M.val true A i'' δ v ─⋆ ewpPostW Tb Q i'' t)))) ρ))
      (ewpW (ℍ := ℍ) M i e Tb Q)

/-- **6.65 at W at a resuming table of class `c`, the lend quantified at the callback's start**
(GhostEnd's `O151AsStated` at W). -/
def MutFrameW (M : SemWorld) (c : RowClass) : Prop :=
  ∀ (T : OpTabI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (β : Life), T.Resuming c →
    (∀ i w σ, M.val true A i δ w σ → σ.InStratum β) →
    ∀ (v : Val) (e : Expr) (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp),
      Entails
        (ptoOwn l v ⋆ M.val true A i δ v ⋆
          fresh (fun α => ptoMutSW M l α i (fun i₀ => M.val true A i₀ δ) ─⋆
            ewpW (ℍ := ℍ) M i e (opTabW M T) (fun i'' v' =>
              box α (all fun w => ptoOwn l w ─⋆ (M.val true A i'' δ w ─⋆ Q i'' v')))))
        (ewpW (ℍ := ℍ) M i e (opTabW M T) Q)

/-- **6.64 at W at a resuming table of class `c`, the lend quantified at the callback's start.**
`hQ` and the table's stops carried along `M.Ext` are 6.64's `hQ` (`opTable_extR` at a resuming
table). -/
def ImmFrameW (M : SemWorld) (c : RowClass) : Prop :=
  ∀ (T : OpTabI (Idx M.Stk)) (l : Loc) (A : VTy) (δ : LSub) (v : Val) (e : Expr)
    (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp), T.Resuming c → AdmWf A δ →
    (∀ i₁ i₂ w ρ, M.Ext i₁ i₂ ρ → Q i₁ w ρ → Q i₂ w ρ) →
    (∀ i₁ i₂ t Φ ρ, M.Ext i₁ i₂ ρ → opTabW M T i₁ t Φ ρ → opTabW M T i₂ t Φ ρ) →
    Entails
      (ptoOwn l v ⋆ M.val true A i δ v ⋆
        fresh (fun α ρ => ∀ ls', AddAt i.1 ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = A ∧ r.δ = δ) →
          (ptoImmSW M l α (ls', i.2) (fun i₀ => M.val true A i₀ δ) ─⋆
            ewpW (ℍ := ℍ) M (ls', i.2) e (opTabW M T) (fun i'' v' =>
              box α (ptoOwn l v ─⋆ (M.val true A i'' δ v ─⋆ Q i'' v')))) ρ))
      (ewpW (ℍ := ℍ) M i e (opTabW M T) Q)

/-- The lend frames at W, at class `c`.  At `.abortive` the resuming tables are empty, and the
resuming conjuncts are 6.64 and 6.65 at a table with no stop. -/
def FramesW (M : SemWorld) (c : RowClass) : Prop :=
  ImmFrameUW (ℍ := ℍ) M ∧ MutFrameUW (ℍ := ℍ) M ∧ ImmFrameW (ℍ := ℍ) M c ∧
    MutFrameW (ℍ := ℍ) M c

/-! ### The spanning rules (tier 2's pin) and their semantic cases

Each is the `CDerives` constructor of an unwinding borrow constant with `hS : S.Unwind x` replaced
by `RowSpan Adm Δ x S`, at row families, its outlives side conditions read at `J.out`; the
semantic form adds `c.Admits S` and reads the outlives side conditions at `O`. -/

def SpanRule1 (J : TypingJ) (Adm : OpAdm) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (S : RowEnv → Row)
    (d : Expr) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η) ∧ VScoped Δ (A η) ∧ ¬ VFree x (A η) ∧ ¬ VFree x (B η) ∧
      RowSpan Adm Δ x (S η)) →
    Δ.find? x = none → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.ref (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (withbor1UTy x Δ.meetOfDom (A η) (B η) (S η)))

def SpanRule2 (J : TypingJ) (Adm : OpAdm) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (S : RowEnv → Row)
    (d : Expr) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η) ∧ (∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) ∧
      ¬ VFree x (A η) ∧ ¬ VFree x (B η) ∧ RowSpan Adm Δ x (S η)) →
    Δ.find? x = none → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.ref (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (withbor2UTy x Δ.meetOfDom (A η) (B η) (S η)))

def SpanRule3 (J : TypingJ) (Adm : OpAdm) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (a : Lifetime.Life) (A B : RowEnv → VTy)
    (S : RowEnv → Row) (d : Expr) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η) ∧ ¬ VFree x (A η) ∧ ¬ VFree x (B η) ∧
      RowSpan Adm Δ x (S η)) →
    Δ.find? x = none → closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.mut a (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (withbor3UTy a x Δ.meetOfDom (A η) (B η) (S η)))

def SpanRuleLoad (J : TypingJ) (Adm : OpAdm) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (a : Lifetime.Life) (A B : RowEnv → VTy)
    (S : RowEnv → Row) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η) ∧ ¬ VFree x (A η) ∧ ¬ VFree x (B η) ∧
      RowSpan Adm Δ x (S η)) →
    Δ.find? x = none →
    J Θ Δ Γ withload (fun η => .val (withloadUTy a x Δ.meetOfDom (A η) (B η) (S η)))

def SpanRuleSliceM (J : TypingJ) (Adm : OpAdm) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (S : RowEnv → Row)
    (d : Expr) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η) ∧ (∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) ∧
      (∃ b, Δ.Defines b ∧ J.out.le Δ b (B η)) ∧ ¬ VFree x (A η) ∧ ¬ VFree x (B η) ∧
      RowSpan Adm Δ x (S η)) →
    closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.array (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (sliceBorrowMUTy x Δ.meetOfDom (A η) (B η) (S η)))

def SpanRuleSliceI (J : TypingJ) (Adm : OpAdm) : Prop :=
  ∀ (Θ : RowCtx) (Δ : LifeCtx) (Γ : RowEnv → Ctx VTy) (A B : RowEnv → VTy) (S : RowEnv → Row)
    (d : Expr) (x : LifeVar),
    (∀ η, Θ.Models η → Ctx.DeadP (Γ η) ∧ VScoped Δ (A η) ∧
      (∃ b, Δ.Defines b ∧ J.out.le Δ b (A η)) ∧ (∃ b, Δ.Defines b ∧ J.out.le Δ b (B η)) ∧
      ¬ VFree x (A η) ∧ ¬ VFree x (B η) ∧ RowSpan Adm Δ x (S η)) →
    closedAt 0 d = true →
    J Θ Δ Γ d (fun η => .val (.lolli (.array (A η)) .unit)) →
    J Θ Δ Γ (withborUE d) (fun η => .val (sliceBorrowIUTy x Δ.meetOfDom (A η) (B η) (S η)))

/-- `withbor` (1)'s spanning case at W. -/
def SpanWithbor1 (M : SemWorld) (_O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → VScoped Δ A →
    ¬ VFree x A → ¬ VFree x B → RowSpan Adm Δ x S → c.Admits S → closedAt 0 d = true →
    SemW₀ M Δ Γ d (.val (.lolli (.ref A) .unit)) →
    SemW₀ M Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))

/-- `withbor` (2)'s spanning case at W: the premises in W's relation give the conclusion. -/
def SpanWithbor2 (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → (∃ b, Δ.Defines b ∧ O.le Δ b A) →
    ¬ VFree x A → ¬ VFree x B → RowSpan Adm Δ x S → c.Admits S → closedAt 0 d = true →
    SemW₀ M Δ Γ d (.val (.lolli (.ref A) .unit)) →
    SemW₀ M Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))

/-- `withbor` (3)'s spanning case at W. -/
def SpanWithbor3 (M : SemWorld) (_O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
    (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none →
    ¬ VFree x A → ¬ VFree x B → RowSpan Adm Δ x S → c.Admits S → closedAt 0 d = true →
    SemW₀ M Δ Γ d (.val (.lolli (.mut a A) .unit)) →
    SemW₀ M Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S))

/-- `withload`'s spanning case at W. -/
def SpanWithload (M : SemWorld) (_O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (S : Row) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none →
    ¬ VFree x A → ¬ VFree x B → RowSpan Adm Δ x S → c.Admits S →
    SemW₀ M Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S))

/-- `slice_borrow_mut`'s spanning case at W. -/
def SpanSliceM (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → (∃ b, Δ.Defines b ∧ O.le Δ b A) → (∃ b, Δ.Defines b ∧ O.le Δ b B) →
    ¬ VFree x A → ¬ VFree x B → RowSpan Adm Δ x S → c.Admits S → closedAt 0 d = true →
    SemW₀ M Δ Γ d (.val (.lolli (.array A) .unit)) →
    SemW₀ M Δ Γ (withborUE d) (.val (sliceBorrowMUTy x Δ.meetOfDom A B S))

/-- `slice_borrow_imm`'s spanning case at W. -/
def SpanSliceI (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → VScoped Δ A → (∃ b, Δ.Defines b ∧ O.le Δ b A) →
    (∃ b, Δ.Defines b ∧ O.le Δ b B) →
    ¬ VFree x A → ¬ VFree x B → RowSpan Adm Δ x S → c.Admits S → closedAt 0 d = true →
    SemW₀ M Δ Γ d (.val (.lolli (.array A) .unit)) →
    SemW₀ M Δ Γ (withborUE d) (.val (sliceBorrowIUTy x Δ.meetOfDom A B S))

/-- The six spanning typing rules. -/
def SpanRules (J : TypingJ) (Adm : OpAdm) : Prop :=
  SpanRule1 J Adm ∧ SpanRule2 J Adm ∧ SpanRule3 J Adm ∧ SpanRuleLoad J Adm ∧
  SpanRuleSliceM J Adm ∧ SpanRuleSliceI J Adm

/-- The six spanning cases at W. -/
def SpanBorrows (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  SpanWithbor1 M O Adm c ∧ SpanWithbor2 M O Adm c ∧ SpanWithbor3 M O Adm c ∧
  SpanWithload M O Adm c ∧ SpanSliceM M O Adm c ∧ SpanSliceI M O Adm c

/-- **Tier 2's pin**: the typing system holds the spanning rules at every row a lend may span, the
affine (cancellable) operations included. -/
def Tier2Pinned (J : TypingJ) (Adm : OpAdm) : Prop := SpanRules J Adm

/-- The tier-2 acceptance programs (D14). -/
def AcceptsTier2 (J : TypingJ) : Prop :=
  J.closed at02 (.ret EffPrograms.Flag) ∧
  J.closed at04 (.ret (.tensor EffPrograms.Flag EffPrograms.Flag)) ∧
  J.closed at12 (.ret EffPrograms.Flag) ∧ J.closed at17 (.ret EffPrograms.Flag)

/-- **I2**, at the outlives judgment `O`, the admissibility `Adm` and the class `c` of rows a lend
may span: capture, the stop's role, resume, the lend frames, and the spanning borrows. -/
def I2 (M : SemWorld) (O : OutJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  Arises M ∧ StopVisible M ∧ ShareResume M ∧ FramesW (ℍ := ℍ) M c ∧ SpanBorrows M O Adm c

/-! ## I3. Drop finalises exactly once -/

/-- **I3.a**: `contShare`'s cancel conjunct (`cancelOwed`) at W, at affine entries, with the
closing clause: the cancel's end holds nothing its start did not. -/
def ShareCancel (M : SemWorld) : Prop :=
  ∀ T en n i K Φ ρ, M.share T en n i K Φ ρ → en.q ≠ .lin → en.q ≠ .unr → ∀ i', M.Ext i i' ρ →
    ∀ N : List UInt32, n ∈ N → (∀ m ∈ K.hndNames, m ∈ N) →
      ewpW (ℍ := ℍ) M i' (Kont.plug K (raiseE (.val (cancelVal N none))))
        (cancelTabW T N (fun i'' => (∀ f ∈ (M.held i'').1, f ∈ (M.held i').1) ∧
                                    (∀ x ∈ (M.held i'').2, x ∈ (M.held i').2)))
        (fun _ _ _ => False) ρ

/-- **I3** at W. -/
def I3 (M : SemWorld) : Prop := ShareCancel (ℍ := ℍ) M

/-- What a cancel answers at `ccatch`: `()`, or the kept error raised at the canceller. -/
def cancelAnswer : Option Val → Expr
  | none => .val .unit
  | some E => raiseE (.val E)

/-- A cancel run that fires the finalisers `fs`, innermost first: one `ufinC` per finaliser, its
`D ()` run under `cfin` to `cfret`/`cferr`, and at the end `ccatch` answering. -/
inductive CancelRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | caught {μ : Heap} {K : Kont} {Ns : List UInt32} {err : Option Val}
      (hK : K.Catches 0 = false) :
      CancelRun μ (ccatchE (K.plug (raiseE (.val (cancelVal Ns err))))) [] μ (cancelAnswer err)
  | fin {μ μ₁ μ₂ : Heap} {K₀ K : Kont} {Nv Dv : Val} {Ns : List UInt32} {err err' : Option Val}
      {fs : List Expr} {r : Expr} (hK : K.Catches 0 = false)
      (hD : Steps (ℍ := ℍ) μ (cfinE (cancelVal Ns err) (.app (.val Dv) (.val .unit))) μ₁
              (raiseE (.val (cancelVal Ns err'))))
      (hr : CancelRun μ₁ (ccatchE (K₀.plug (raiseE (.val (cancelVal Ns err'))))) fs μ₂ r) :
      CancelRun μ
        (ccatchE (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (cancelVal Ns err)))))))
        (Dv.1 :: fs) μ₂ r

/-- An unwind that fires the finalisers `fs`, innermost first: one `ufin` per finaliser, its
`D (); raise p` run until a raise is pending under a context `Kd` that catches nothing of it,
ending at a raise that the remaining frames do not catch.  If `D` returns, `Kd` is the hole and
the raise is `p`.  If `D` raises its own abortive operation, the raise is that one, and `Kd` holds
the `seq` frame (`_; raise p`, which catches nothing) and `D`'s own frames at the raise; no rule
reduces a raise under a `seq`, so the unwind goes on from `K₀ ∘ Kd`. -/
inductive UnwindRun : Heap → Expr → List Expr → Heap → Expr → Prop
  | out {μ : Heap} {K : Kont} {m j : UInt32} {w : Val} (hK : K.Catches m = false) :
      UnwindRun μ (K.plug (raiseE (.val (opPayload m j w)))) [] μ
        (K.plug (raiseE (.val (opPayload m j w))))
  | fin {μ μ₁ μ₂ : Heap} {K₀ K Kd : Kont} {Nv Dv : Val} {n i m j : UInt32} {v w : Val}
      {fs : List Expr} {r : Expr} (hn : n ≠ 0) (hK : K.Catches n = false)
      (hD : Steps (ℍ := ℍ) μ (.seq (.app (.val Dv) (.val .unit)) (raiseE (.val (opPayload n i v))))
              μ₁ (Kd.plug (raiseE (.val (opPayload m j w)))))
      (hKd : Kd.Catches m = false)
      (hr : UnwindRun μ₁ ((K₀.comp Kd).plug (raiseE (.val (opPayload m j w)))) fs μ₂ r) :
      UnwindRun μ (K₀.plug (ubindE (Val.pair Nv Dv) (K.plug (raiseE (.val (opPayload n i v))))))
        (Dv.1 :: fs) μ₂ r

/-- `K` has no `ccatch` and no `cfin` frame. -/
def _root_.BoCa.BoLo.Kont.NoCtl : Kont → Prop
  | .hole => True
  | .appR f K => (f ≠ .prim .ccatch ∧ ∀ s, f ≠ .app (.prim .cfin) s) ∧ K.NoCtl
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoCtl

/-- **I3.b, cancel**: in a typed program, every complete run of a continuation's cancel fires the
frozen finalisers once each, innermost first.  (The three administrative steps from
`κ (inj₂ ())` to `cancelOf n H K` are pure; the canceller's context `K₀` takes no part until
`ccatch` answers.) -/
def CancelOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ : Kont) n H K, Kont.NoCtl K →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (.app (kappa n H K) (.val (Val.inj₂ .unit)))) →
    ∀ μ₃ r, Steps (ℍ := ℍ) μ₁ (cancelOf n H K) μ₃ r →
      (r = .val .unit ∨ ∃ E, r = raiseE (.val E)) →
      CancelRun (ℍ := ℍ) μ₁ (cancelOf n H K) K.fins μ₃ r

/-- **I3.b, unwind**: every complete unwind through frames with no handler fires their finalisers
once each, innermost first. -/
def UnwindOrder (J : TypingJ) : Prop :=
  ∀ e A, J.closed e (.ret A) → ∀ μ₁ (K₀ K : Kont) n i v, K.hndNames = [] → Kont.NoCtl K → n ≠ 0 →
    Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ (K₀.plug (K.plug (raiseE (.val (opPayload n i v))))) →
    ∀ μ₂ (K' : Kont) m j w, K'.Catches m = false →
      Steps (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) μ₂
        (K'.plug (raiseE (.val (opPayload m j w)))) →
      UnwindRun (ℍ := ℍ) μ₁ (K.plug (raiseE (.val (opPayload n i v)))) K.fins μ₂
        (K'.plug (raiseE (.val (opPayload m j w))))

/-- **I3.b.** -/
def FinaliserOrder (J : TypingJ) : Prop := CancelOrder (ℍ := ℍ) J ∧ UnwindOrder (ℍ := ℍ) J

/-- `.prim p` occurs in the term. -/
def _root_.BoCa.Expr.HasPrim (p : Prim) : Expr → Prop
  | .prim p' => p' = p
  | .var _ | .unit | .loc _ => False
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HasPrim p ∨ b.HasPrim p
  | .inj₁ a | .inj₂ a | .lam a => a.HasPrim p
  | .case a b c => a.HasPrim p ∨ b.HasPrim p ∨ c.HasPrim p

/-- Every occurrence of `.prim .hnd` is the function of
`.app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) _)` with `m ≠ 0`. -/
def _root_.BoCa.Expr.HndNamesNZ : Expr → Prop
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) r) => m ≠ 0 ∧ r.HndNamesNZ
  | .prim p => p ≠ .hnd
  | .var _ | .unit | .loc _ => True
  | .pair a b | .seq a b | .letpair a b | .app a b => a.HndNamesNZ ∧ b.HndNamesNZ
  | .inj₁ a | .inj₂ a | .lam a => a.HndNamesNZ
  | .case a b c => a.HndNamesNZ ∧ b.HndNamesNZ ∧ c.HndNamesNZ

/-- **I3.c**: typed terms contain no `ccatch`, no `cfin`, and no handler named `0`. -/
def NoInterception (J : TypingJ) : Prop :=
  ∀ Θ Δ Γ e j, J Θ Δ Γ e j → ¬ e.HasPrim .ccatch ∧ ¬ e.HasPrim .cfin ∧ e.HndNamesNZ

/-! ## I4. Answering effects are borrows -/

/-- The implementation's operations are typed: `co_j : !U(S ⊗ A_j ⊸ F(S ⊗ B_j))`. -/
def ImplTyped (J : TypingJ) (impl : AnsImpl) : Prop :=
  List.Forall₂ (fun (ab : VTy × VTy) c => J.at LifeCtx.empty [] (.val c)
    (.val (.bang (.thunk (.arr (.tensor impl.S ab.1) (.ret (.tensor impl.S ab.2))))))) impl.E impl.co

/-- **I4.a**: the borrow form of every typed answering body is typed by the borrow rules, at the
rows a lend may span.  `x` is fresh for `Δ`'s bounds and for `Γ`'s live types: these are
`CDerives.allI`'s premises `hΔx` and `hΓx`, which the callback `Λ. λm. body` of the borrow form
needs (DESIGN §Corrections C4). -/
def I4a (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (impl : AnsImpl) (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (S : Row) (d s₀ body : Expr)
    (B : VTy),
    ImplTyped J impl → Ctx.DeadP Γ → Δ.find? x = none →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → ¬ VFree x impl.S → ¬ VFree x B →
    (∃ b, Δ.Defines b ∧ J.out.le Δ b impl.S) → RowSpan Adm Δ x S → c.Admits S →
    closedAt 0 d = true →
    J.at Δ Γ s₀ (.val impl.S) → J.at Δ Γ d (.val (.lolli (.ref impl.S) .unit)) →
    J.at (Δ.extend x Δ.meetOfDom) (⟨.mut (.var x) impl.S, true⟩ :: Γ) body
      (.comp (CTy.effOf S (.box (.var x) B))) →
    J.at Δ Γ (ansRun d s₀ body) (.comp (CTy.effOf S (.tensor impl.S B)))

/-- **I4.c, typing half**: a typed control form of a closed body on the spine has a typed borrow
form, at the same answer, its row one a lend may span.  `R` is data, so the callback's answer
`['x] R` is the borrow rules'. -/
def I4Typing (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (impl : AnsImpl) (n : UInt32) (d s₀ e body : Expr) (S : Row) (R : VTy) (x : LifeVar),
    capPass n impl.co 0 (e.shift 1 0) = some body → R.Data → ImplTyped J impl →
    ¬ VFree x impl.S → (∃ b, LifeCtx.empty.Defines b ∧ J.out.le LifeCtx.empty b impl.S) →
    RowSpan Adm LifeCtx.empty x S → c.Admits S → closedAt 0 d = true →
    J.closed (ctlForm n impl s₀ e) (CTy.effOf S (.tensor impl.S R)) →
    J.at LifeCtx.empty [] d (.val (.lolli (.ref impl.S) .unit)) →
    J.closed (ansRun d s₀ body) (CTy.effOf S (.tensor impl.S R))

/-- **I4.c, equivalence** (binary): the control form and the borrow form are contextually
equivalent. -/
def I4c (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (impl : AnsImpl) (n : UInt32) (d s₀ e body : Expr) (S : Row)
    (R : VTy),
    capPass n impl.co 0 (e.shift 1 0) = some body →
    J.closed (ctlForm n impl s₀ e) (CTy.effOf S (.tensor impl.S R)) →
    J.closed (ansRun d s₀ body) (CTy.effOf S (.tensor impl.S R)) →
    CtxEquiv (ℍ := ℍ) J P (CTy.effOf S (.tensor impl.S R)) (thunkF (ctlForm n impl s₀ e))
      (thunkF (ansRun d s₀ body))

/-! ## I5. The capture laws β, η, hiding (unary halves) -/

/-- **I5.β**: resuming `κ` at `w` runs the frozen computation at `w` under the reinstalled
handler. -/
def I5beta (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) (n : UInt32) (H : Val) (K : Kont) (w : Val) i Q ρ,
    TableI.Mono Tb → ewpW (ℍ := ℍ) M i (hndE H (K.plug (.val w))) Tb Q ρ →
    ewpW (ℍ := ℍ) M i (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)) Tb Q ρ

/-- The view `ℓ ↦ M_α 𝒱⟦T⟧δ` at W. -/
def mutView (M : SemWorld) (ℓ : Loc) (α : Life) (T : VTy) (δ : LSub) (i : Idx M.Stk) : WProp :=
  ptoMutSW M ℓ α i (fun i₀ => M.val true T i₀ δ)

/-- One unfolding of the anti-framed computation (GhostEnd's `antiF` at W): from the content
handed out, run to an answer or a stop, handing the content back for the view; a stop owes the
view and the computation again. -/
def antiFW (M : SemWorld) (Tb : TableI (Idx M.Stk)) (ℓ : Loc) (α : Life) (T : VTy) (δ : LSub)
    (Q : Idx M.Stk → Val → WProp) (X : Idx M.Stk → Expr → WProp) :
    Idx M.Stk → Expr → WProp := fun i e =>
  all fun v => ptoOwn ℓ v ─⋆ (M.val true T i δ v ─⋆
    wpGW (ℍ := ℍ) M i e (fun i'' t => ex fun w => ptoOwn ℓ w ⋆ M.val true T i'' δ w ⋆
      (mutView M ℓ α T δ i'' ─⋆ fun ρ => valPostI Q i'' t ρ ∨
        Tb i'' t (fun i' e' => mutView M ℓ α T δ i' ⋆ X i' e') ρ)))

/-- The anti-framed computation: the least fixed point of `antiFW`. -/
def AntiRelendW (M : SemWorld) (Tb : TableI (Idx M.Stk)) (ℓ : Loc) (α : Life) (T : VTy)
    (δ : LSub) (Q : Idx M.Stk → Val → WProp) (i : Idx M.Stk) (e : Expr) : WProp :=
  fun ρ => ∀ X : Idx M.Stk → Expr → WProp,
    (∀ i e ρ, antiFW (ℍ := ℍ) M Tb ℓ α T δ Q X i e ρ → X i e ρ) → X i e ρ

/-- **I5.hiding**: [TR] 6.66 at W (GhostEnd's `ewpTS_M_antiFrameR` at W), the view at a lifetime
`α`. -/
def AntiFrameW (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) ℓ α T δ Q i e, TableI.Mono Tb →
    Entails (mutView M ℓ α T δ i ⋆ AntiRelendW (ℍ := ℍ) M Tb ℓ α T δ Q i e)
      (ewpW (ℍ := ℍ) M i e Tb Q)

/-- **I5.frame**: `ewp_frame_plain` at W, at tables with no `unr` entry.  Its stability premise is
`hFs` transcribed: Stop-related indices whose visible records agree give `Fr i ⊨ Fr i'`. -/
def FrameW (M : SemWorld) : Prop :=
  ∀ (T : OpTabI (Idx M.Stk)) (K : Kont), (∀ n, K.HasHnd n = false) →
    (∀ n, K.Catches n = false) → K.hndNames = [] → (∀ n j en, T n j = some en → en.q ≠ .unr) →
    ∀ (Fr : Idx M.Stk → WProp),
    (∀ ps i ps' i' t, M.Stop (ps, i) (ps', i') t → (∀ x, x ∈ i'.1 ↔ x ∈ i.1) →
       Entails (Fr i) (Fr i')) →
    (∀ i i' ρ, M.Ext i i' ρ → Fr i ρ → Fr i' ρ) →
    (∀ n j en, T n j = some en → (en.q ≠ .lin ∨ en.abort = true) → ∀ i ρ, Fr i ρ → NoOwn ρ) →
    ∀ (Q₁ Q : Idx M.Stk → Val → WProp),
      (∀ i v, Entails (Q₁ i v ⋆ Fr i) (ewpW (ℍ := ℍ) M i (K.plug (.val v)) (opTabW M T) Q)) →
      ∀ i e ρ, ewpW (ℍ := ℍ) M i e (opTabW M T) Q₁ ρ → ∀ ρ₂ ρ', Fr i ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpW (ℍ := ℍ) M i (K.plug e) (opTabW M T) Q ρ'

/-- **I5** at W. -/
def I5 (M : SemWorld) : Prop := I5beta (ℍ := ℍ) M ∧ AntiFrameW (ℍ := ℍ) M ∧ FrameW (ℍ := ℍ) M

end Targets

end
