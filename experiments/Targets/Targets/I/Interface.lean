import Core.Fundamental
import Targets.I.World
import Targets.I.Programs
import Targets.Base.CoreCancel
import Targets.Base.Ctx
import Targets.B.Guarantees

/-!
# The interaction — I1–I5, at the world (RESTRUCTURE §3.2; DESIGN §5)

* **I1** (`I1`): a suspension is a value of the resource world.
* **I2** (`I2`): capture and resume preserve the invariant.  Its `Arises` part is in done (I's
  `Interface`); `StopVisible`, `ShareResume`, `FramesW`, `SpanBorrows` are the proof device's
  (finding #5: they fix an option of OQ-8 or OQ-9).  The spanning rules (`SpanRules`) are `J₂`'s
  mechanism for the tier-2 programs.
* **I3** (`I3`, `ShareCancel`): the share's cancel at W.
* **I4** (`I4a`, `I4Typing`, `I4c`): answering effects are borrows.
* **I5** (`I5`): the unary capture laws β, hiding ([TR] 6.66 at W) and the frame.
* **P10** (`Exclusive`): every configuration W reaches is valid, counting what suspensions hold.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal hndE hndVal kappa
  ccatchE cfinE ubindE kappaC)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **I1**: the continuation's share and its cell give `κ` its type.  The rows are unr-free, so
the operation is linear or affine, and the `κ` its catch hands is `kappaC` at a fresh cell `ℓ`
(SPEC §25). -/
def I1 (M : SemWorld) : Prop :=
  ∀ (S : Row) (n : UInt32) (E : List (Qual × VTy × VTy)) (R : VTy) (δ : LSub) (qs hr hs : Val)
    (j : UInt32) (o : OpSig) (K : Kont) (i : Idx M.Stk) (ℓ : Loc) (ρk σ ρ : WRes),
    n ≠ 0 → (∀ o' ∈ S, o'.n ≠ n) → Row.NU (Row.ofEff n E 0 ++ S) →
    Row.find (Row.ofEff n E 0) n j = some o → o.abort = false →
    M.share (rowTabW M (Row.ofEff n E 0 ++ S) δ) (entW M δ o) n i K
      (fun i' t => ewpW (ℍ := ℍ) M i' (hndE (hndVal n qs hr hs) t) (opTabW M (rowTabW M S δ))
        (fun i'' v => M.val true R i'' δ v)) ρk →
    ptoOwn ℓ Val.unit σ → ResU.CompS ρk σ ρ →
    M.val true (kTy S R o.q o.B) i δ
      ⟨kappaC (o.q == .aff) ℓ (hndVal n qs hr hs) K, by unfold kappaC; exact .lam⟩ ρ

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

/-- **I3.a**: `contShare`'s cancel conjunct (`cancelOwed`) at W, at affine entries, with the
closing clause: the cancel of the dead region `K†` keeps no error, and its end holds nothing its
start did not. -/
def ShareCancel (M : SemWorld) : Prop :=
  ∀ T en n i K Φ ρ, M.share T en n i K Φ ρ → en.q ≠ .lin → en.q ≠ .unr → ∀ i', M.Ext i i' ρ →
    ewpW (ℍ := ℍ) M i' (Kont.plug K.dead (raiseE (.val (cancelVal none))))
      (cancelTabW (fun _ _ => none) (fun i'' => (∀ f ∈ (M.held i'').1, f ∈ (M.held i').1) ∧
                                  (∀ x ∈ (M.held i'').2, x ∈ (M.held i').2)))
      (fun _ _ _ => False) ρ

/-- **I3** at W. -/
def I3 (M : SemWorld) : Prop := ShareCancel (ℍ := ℍ) M

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

/-- **I4, the run correspondence** (D1.h2, unary): at a configuration that a typed closed program
at a data answer reaches under a platform that keeps its protocol, with the control form of a
typed answering body in the evaluation context `K₀`, the runs from it and from the same
configuration with the borrow form in `K₀` reach the same values.

The hypotheses are `I4Typing`'s on the two forms, without the two lifetime premises that only the
borrow form's typing reads, and with three more:
* **data state, data operations and a data answer of the body**;
* **`s₀` at a value judgement**, as `I4a` reads it: the control form runs `e` up to its first
  operation of `n` before it runs `s₀`, and the borrow form runs `s₀` first;
* **a data answer of the program**: a continuation captured across the form by an outer handler
  holds the control form's handler frame on one side and the borrow form's frames on the other,
  so an answer that returned it would differ as a term.

Values are compared, not traces: when the body raises past the borrow form's finaliser frame, that
finaliser fires, and the control form has no such frame. -/
def I4Runs (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  ∀ (impl : AnsImpl) (n : UInt32) (d s₀ e body : Expr) (S : Row) (R : VTy) (x : LifeVar),
    capPass n impl.co 0 (e.shift 1 0) = some body → impl.S.Data → R.Data →
    (∀ ab ∈ impl.E, ab.1.Data ∧ ab.2.Data) → ImplTyped J impl →
    RowSpan Adm LifeCtx.empty x S → c.Admits S → closedAt 0 d = true →
    J.at LifeCtx.empty [] s₀ (.val impl.S) →
    J.closed (ctlForm n impl s₀ e) (CTy.effOf S (.tensor impl.S R)) →
    J.at LifeCtx.empty [] d (.val (.lolli (.ref impl.S) .unit)) →
    ∀ (P : Platform), P.Respects →
    ∀ (e₀ : Expr) (S₀ : Row) (A : VTy) (cf : Conf P) (K₀ : Kont), A.Data →
      J.closed e₀ (CTy.effOf S₀ A) → PSteps (ℍ := ℍ) P (init P e₀) cf →
      cf.e = K₀.plug (ctlForm n impl s₀ e) →
      ∀ v : Val, (∃ c', PSteps (ℍ := ℍ) P cf c' ∧ c'.e = .val v) ↔
        (∃ c', PSteps (ℍ := ℍ) P ⟨cf.μ, K₀.plug (ansRun d s₀ body), cf.s⟩ c' ∧ c'.e = .val v)

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

/-- **I5.β**: resuming `κ` at `w` runs the frozen computation at `w` under the reinstalled
handler.  It is stated at an unrestricted operation's `κ`, which owns no cell; a linear or affine
`κ` frees its cell first (SPEC §25; at Core's world `ewp_kappaC_resume`). -/
def I5beta (M : SemWorld) : Prop :=
  ∀ (Tb : TableI (Idx M.Stk)) (H : Val) (K : Kont) (w : Val) i Q ρ,
    TableI.Mono Tb → ewpW (ℍ := ℍ) M i (hndE H (K.plug (.val w))) Tb Q ρ →
    ewpW (ℍ := ℍ) M i (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val w)) Tb Q ρ

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
    (∀ n, K.Catches n = false) → (∀ n j en, T n j = some en → en.q ≠ .unr) →
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

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core

/-- **P10.** -/
def Exclusive (M : SemWorld) : Prop :=
  ∀ fρ ps i, M.Fam fρ ps i → ResU.Valid fρ ∧
    ∃ ps₀ ls₀, (∀ p, p ∈ ps₀ ↔ p ∈ ps ∨ p ∈ (M.held i).1) ∧
      (∀ x, x ∈ ls₀ ↔ x ∈ i.1 ∨ x ∈ (M.held i).2) ∧ TI fρ ps₀ (rsOf ls₀)

end Targets

end
