import Core.Steps
import Core.Demonic

/-!
# Core — cancels: a dead region, and finalisers that raise and perform  `[spec §19]`

Runs of §19's cancel.  In each program a handler `1`, whose clause cancels its `κ` (`cancelC`),
catches `perform 1`; the continuation's region holds finaliser frames, and sometimes handlers.  The
cancel runs the region with its handler frames and its cancel delimiters removed (`Kont.dead`), so
a dead handler catches nothing, and a finaliser's raises and operations reach the nearest live
instance of their name.

* `prog`: the finaliser raises name `2`, handled only by a handler inside the region.  That handler
  is dead, so the error is kept, re-raised at the canceller, and no handler catches it: the run
  ends at `raise (2, (0, ()))`, a configuration with no step (`prog_run`, `prog_final`).  A typing
  of finalisers rejects it (SPEC §27, decision D3).
* `prog₃`: the finaliser raises `3`, which `H₃` handles outside the region (`prog₃_run`).
* `progOut`: `prog` under a live handler of `2` outside the region, which catches the error
  (`progOut_run`).
* `progRe`: the region re-enters the site `3` (a dead inner instance) under a live outer instance;
  the finaliser's raise of `3` propagates to the outer one (`progRe_run`).
* `progFinOp`: the finaliser performs `4`; the dead inner `4` does not catch it, the live outer `4`
  resumes it, and the cancel answers `()` (`progFinOp_run`).
* `progNC₁`: as `progFinOp`, but the outer `4` cancels the finaliser's continuation: that cancel
  passes the running finaliser's `cfin` (`[cfin-cancel]`) and ends at its own `ccatch`
  (`progNC₁_run`).
* `progDrop`, `progKeep`: a finaliser raises `2`, kept; a later finaliser performs `4`, whose
  unrestricted handler drops its continuation, and the kept error with it (`progDrop_run`), or
  resumes it, and the kept error reaches the live `2` (`progKeep_run`).

The handlers' operations are unrestricted (`qualsVal [.unr]`), so `κ` owns no cell (§25) and the
runs allocate nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CancelIntercept
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE performE ccatchE cfinE ubindE opPayload
  clauseAt kappa cancelVal errNext Alloc AStep1 AHead ARun)
open BoCa.Lifetime (LSub LifeCtx)

/-! ### Handlers, clauses and frames -/

/-- The identity. -/
def idV : Val := Val.lam (.var 0)

/-- The answer clause `λx. inj₁ x`. -/
def injlV : Val := Val.lam (.inj₁ (.var 0))

/-- The clause `λp. let (x, k) = p; k (inj₂ ())`: cancel `κ`. -/
def cancelC : Val := Val.lam (.letpair (.var 0) (.app (.var 0) (.val (Val.inj₂ Val.unit))))

/-- The clause `λp. let (x, k) = p; (k (inj₁ ())) x`: resume `κ` with the argument. -/
def resumeC : Val :=
  Val.lam (.letpair (.var 0) (.app (.app (.var 0) (.val (Val.inj₁ Val.unit))) (.var 1)))

/-- The clause `λ_. v`: answer `v`. -/
def constC (v : Val) : Val := Val.lam (.val v)

/-- The handler of name `n` with one unrestricted operation, the answer clause `hr` and the
clause `c`. -/
def hU (n : UInt32) (hr c : Val) : Val := hndVal n (qualsVal [.unr]) hr (Val.pair c Val.unit)

/-- `perform (m, (0, ()))`. -/
def performU (m : UInt32) : Expr := performE (.val (opPayload m 0 Val.unit))

/-- `raise (m, (0, ()))`. -/
def raiseU (m : UInt32) : Expr := raiseE (.val (opPayload m 0 Val.unit))

/-- The finaliser `λ_. D`. -/
def finV (D : Expr) : Val := Val.lam D

/-- `M then x. x unwind D`. -/
def thenU (M D : Expr) : Expr := ubindE (Val.pair idV (finV D)) M

/-- The frame `hnd H [·]` around `K`. -/
abbrev hF (H : Val) (K : Kont) : Kont := .appR (.app (.val (.prim .hnd)) (.val H)) K

/-- The frame `ubind (id, λ_. D) [·]` around `K`. -/
abbrev uF (D : Expr) (K : Kont) : Kont :=
  .appR (.app (.val (.prim .ubind)) (.val (Val.pair idV (finV D)))) K

/-- The frame `ccatch [·]` around `K`. -/
abbrev ccF (K : Kont) : Kont := .appR (.val (.prim .ccatch)) K

/-- The frame `cfin s [·]` around `K`. -/
abbrev cfF (s : Val) (K : Kont) : Kont := .appR (.app (.val (.prim .cfin)) (.val s)) K

theorem st (K' : Kont) {μ : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ a') :
    Step1 (ℍ := ℍ) μ (K'.plug a) μ (K'.plug a') :=
  ⟨K', a, a', rfl, rfl, h⟩

theorem hcl (c : Val) : clauseAt (Val.pair c Val.unit).1 (0 : UInt32).toNat = some c := by
  simp [clauseAt, Val.pair, c.2]

/-- `κ` at an unrestricted operation is `kappa`. -/
theorem isVal_kappa (H : Val) (K : Kont) : IsVal (kappa H K) := by unfold kappa; exact .lam

/-- A value shifted past a binder and substituted there is itself. -/
theorem subst_shift_one (s v : Val) : Expr.subst 0 s (Expr.shift 1 0 v.1) = v.1 := by
  rw [Expr.subst_shift 0 0 0 s v.1 (le_refl 0) (le_refl 0), Expr.shift_zero]

/-- Cancelling `κ` reaches the dead region's cancel, by three steps. -/
theorem kappa_cancel_steps (μ : Heap) (H : Val) (K : Kont) :
    Steps (ℍ := ℍ) μ (.app (kappa H K) (.val (Val.inj₂ .unit))) μ
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) := by
  refine .more (st .hole (Head.beta μ _ _)) ?_
  refine .more (st .hole (Head.case₂ μ Val.unit _ _)) ?_
  refine .more (st .hole (Head.seq μ _)) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact .refl _ _

/-- Resuming `κ` at `w` reaches `hnd H K[w]`, by four steps. -/
theorem kappa_resume_steps (μ : Heap) (H : Val) (K : Kont) (w : Val) :
    Steps (ℍ := ℍ) μ (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val w)) μ
      (hndE H (K.plug (.val w))) := by
  refine .more (st (.appL .hole w) (Head.beta μ _ _)) ?_
  refine .more (st (.appL .hole w) (Head.case₁ μ Val.unit _ _)) ?_
  refine .more (st (.appL .hole w) (Head.seq μ _)) ?_
  refine .more (st .hole (Head.beta μ _ w)) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact .refl _ _

/-- **A cancelling clause**: `hnd (n, H) K[perform (n, (0, ()))]`, `K` free of `n`, runs to the
cancel of the dead region `K†`. -/
theorem cancel_start (μ : Heap) (n : UInt32) (hr : Val) (K : Kont) (hK : K.HasHnd n = false) :
    Steps (ℍ := ℍ) μ (hndE (hU n hr cancelC) (K.plug (performU n))) μ
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) := by
  let κv : Val := ⟨kappa (hU n hr cancelC) K, isVal_kappa _ _⟩
  refine .more (st .hole (Head.hop μ n 0 (qualsVal [.unr]) hr (Val.pair cancelC Val.unit) cancelC
    Val.unit K (hcl cancelC) hK)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  show Steps μ (.app (Expr.subst 0 Val.unit (Expr.shift 1 0 κv.1)) (.val (Val.inj₂ Val.unit))) μ _
  rw [subst_shift_one]
  exact kappa_cancel_steps μ _ K

/-- **A resuming clause**: `hnd (n, H) K[perform (n, (0, ()))]`, `K` free of `n`, runs to
`hnd (n, H) K[()]`. -/
theorem resume_start (μ : Heap) (n : UInt32) (hr : Val) (K : Kont) (hK : K.HasHnd n = false) :
    Steps (ℍ := ℍ) μ (hndE (hU n hr resumeC) (K.plug (performU n))) μ
      (hndE (hU n hr resumeC) (K.plug (.val Val.unit))) := by
  let κv : Val := ⟨kappa (hU n hr resumeC) K, isVal_kappa _ _⟩
  refine .more (st .hole (Head.hop μ n 0 (qualsVal [.unr]) hr (Val.pair resumeC Val.unit) resumeC
    Val.unit K (hcl resumeC) hK)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  show Steps μ (.app (.app (Expr.subst 0 Val.unit (Expr.shift 1 0 κv.1))
    (.val (Val.inj₁ Val.unit))) (.val Val.unit)) μ _
  rw [subst_shift_one]
  exact kappa_resume_steps μ _ K Val.unit

/-- **A constant clause**: `hnd (n, H) K[perform (n, (0, ()))]`, `K` free of `n`, answers the
closed value `v`; the continuation is dropped. -/
theorem const_start (μ : Heap) (n : UInt32) (hr v : Val) (hv : ∀ s, Expr.subst 0 s v.1 = v.1)
    (K : Kont) (hK : K.HasHnd n = false) :
    Steps (ℍ := ℍ) μ (hndE (hU n hr (constC v)) (K.plug (performU n))) μ (.val v) := by
  refine .more (st .hole (Head.hop μ n 0 (qualsVal [.unr]) hr (Val.pair (constC v) Val.unit)
    (constC v) Val.unit K (hcl (constC v)) hK)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit ⟨_, isVal_kappa _ _⟩))) ?_
  show Steps μ (Expr.subst 0 _ v.1) μ _
  rw [hv]
  exact .refl _ _

/-- A finaliser frame catches a cancel: its finaliser runs under `cfin`. -/
theorem fin_cancel (μ : Heap) (D : Expr) (err : Option Val) :
    Steps (ℍ := ℍ) μ (ubindE (Val.pair idV (finV D)) (raiseE (.val (cancelVal err)))) μ
      (cfinE (cancelVal err) (D.subst 0 Val.unit)) := by
  refine .more (st .hole (Head.ufinC μ idV (finV D) err .hole rfl)) ?_
  refine .more (st (cfF (cancelVal err) .hole) (Head.beta μ D Val.unit)) ?_
  exact .refl _ _

/-! ### The programs -/

/-- Handler `1`: its clause cancels `κ`. -/
def H₁ : Val := hU 1 idV cancelC

/-- `hnd (2, H₂) [·]` inside the region: its clause answers `()`. -/
def H₂ : Val := hU 2 idV (constC Val.unit)

/-- Handler `3`'s clause answers `inj₂ ()`. -/
def c₃ : Val := constC (Val.inj₂ Val.unit)

def H₃ : Val := hU 3 idV c₃

/-- `K = hnd (2, H₂) (ubind (id, λ_. raise m) [·])`. -/
def K (m : UInt32) : Kont := hF H₂ (uF (raiseU m) .hole)

/-- `hnd (1, H₁) K[perform (1, (0, ()))]`. -/
def body (m : UInt32) : Expr := hndE H₁ ((K m).plug (performU 1))

/-- The finaliser raises `2`, a name handled only inside the region. -/
def prog : Expr := body 2

/-- The finaliser raises `3`, a name handled outside the region by `H₃`. -/
def prog₃ : Expr := hndE H₃ (body 3)

/-- The cancel of `body m`: the dead handler `2` is removed, the finaliser raises `m`, the error is
kept and re-raised at the canceller. -/
theorem body_run (m : UInt32) (hm : m ≠ 0) (μ : Heap) :
    Steps (ℍ := ℍ) μ (body m) μ (raiseU m) := by
  refine (cancel_start μ 1 idV (K m) rfl).trans ?_
  show Steps μ (ccatchE ((uF (raiseU m) .hole).plug (raiseE (.val (cancelVal none))))) μ _
  refine (Steps.plug (ccF .hole) (fin_cancel μ (raiseU m) none)).trans ?_
  refine .more (st (ccF .hole) (Head.cferr μ none m 0 Val.unit .hole hm rfl)) ?_
  refine .more (st .hole (Head.creraise μ (opPayload m 0 Val.unit) .hole rfl)) ?_
  exact .refl _ _

/-- A raise at the top of a term takes no step. -/
theorem raise_final {μ : Heap} (p : Val) : ∀ μ' e', ¬ Step1 (ℍ := ℍ) μ (raiseE (.val p)) μ' e' := by
  rintro μ' e' ⟨K', a, a', h, -, hh⟩
  rcases plug_cmp .hole K' (opE_not_isVal true p) hh.not_isVal h with ⟨K'', h₁, -⟩ | ⟨K'', h₁, h₂⟩
  · have h₁' : K''.plug a = .app (.val (.prim .raise)) (.val p) := h₁.symm
    obtain rfl := plug_primApp h₁' hh.not_isVal
    simp only [Kont.plug] at h₁'
    subst h₁'
    exact head_not_inertApp (p := .raise) trivial hh
  · obtain ⟨rfl, rfl⟩ := comp_eq_hole h₂.symm
    simp only [Kont.plug] at h₁
    subst h₁
    exact head_not_inertApp (p := .raise) trivial hh

/-- **`prog`**: the dead handler `2` catches nothing; the finaliser's error is kept and re-raised at
the canceller, where no handler catches it. -/
theorem prog_run (μ : Heap) : Steps (ℍ := ℍ) μ prog μ (raiseU 2) := body_run 2 (by decide) μ

/-- `prog`'s run ends at a configuration with no step. -/
theorem prog_final (μ : Heap) : ∀ μ' e', ¬ Step1 (ℍ := ℍ) μ (raiseU 2) μ' e' :=
  raise_final _

/-- **`prog₃`**: the error of name `3` is kept, re-raised at the canceller, and caught by `H₃`,
outside the region. -/
theorem prog₃_run (μ : Heap) : Steps (ℍ := ℍ) μ prog₃ μ (.val (Val.inj₂ Val.unit)) := by
  refine (Steps.plug (hF H₃ .hole) (body_run 3 (by decide) μ)).trans ?_
  refine .more (st .hole (Head.hunwind μ 3 0 (qualsVal [.unr]) idV (Val.pair c₃ Val.unit) c₃
    Val.unit .hole (hcl c₃) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- `hnd (2, H₂ₒ) prog`: a live handler of `2` outside the region. -/
def progOut : Expr := hndE (hU 2 injlV (constC (Val.inj₂ Val.unit))) prog

/-- **`progOut`**: the error of name `2`, handled inside the region by a dead instance, reaches
the live instance outside it. -/
theorem progOut_run (μ : Heap) : Steps (ℍ := ℍ) μ progOut μ (.val (Val.inj₂ Val.unit)) := by
  refine (Steps.plug (hF (hU 2 injlV (constC (Val.inj₂ Val.unit))) .hole) (prog_run μ)).trans ?_
  refine .more (st .hole (Head.hunwind μ 2 0 (qualsVal [.unr]) injlV
    (Val.pair (constC (Val.inj₂ Val.unit)) Val.unit) (constC (Val.inj₂ Val.unit)) Val.unit .hole
    (hcl _) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- `hnd (3, H₃ᵢ) [·]` inside the region: its clause answers `()`. -/
def H₃ᵢ : Val := hU 3 idV (constC Val.unit)

/-- `f = λ_. hnd (3, H₃ᵢ) (perform (1, (0, ())))`: a function that re-enters the site `3`. -/
def fRe : Val := Val.lam (hndE H₃ᵢ (performU 1))

/-- `P_re`: `hnd (3, H₃ₒ) (hnd (1, H₁) ((f ()) then x. x unwind raise 3))`. -/
def progRe : Expr :=
  hndE (hU 3 injlV c₃) (hndE H₁ (thenU (.app (.val fRe) (.val Val.unit)) (raiseU 3)))

/-- **`progRe`**: the region re-enters the site `3`; its instance there is dead, so the
finaliser's raise of `3` is kept, re-raised at the canceller, and caught by the live outer
instance. -/
theorem progRe_run (μ : Heap) : Steps (ℍ := ℍ) μ progRe μ (.val (Val.inj₂ Val.unit)) := by
  refine .more (st (hF (hU 3 injlV c₃) (hF H₁ (uF (raiseU 3) .hole)))
    (Head.beta μ _ Val.unit)) ?_
  show Steps μ ((hF (hU 3 injlV c₃) .hole).plug
    (hndE H₁ ((uF (raiseU 3) (hF H₃ᵢ .hole)).plug (performU 1)))) μ _
  refine (Steps.plug (hF (hU 3 injlV c₃) .hole)
    (cancel_start μ 1 idV (uF (raiseU 3) (hF H₃ᵢ .hole)) rfl)).trans ?_
  show Steps μ ((hF (hU 3 injlV c₃) (ccF .hole)).plug
    (ubindE (Val.pair idV (finV (raiseU 3))) (raiseE (.val (cancelVal none))))) μ _
  refine (Steps.plug (hF (hU 3 injlV c₃) (ccF .hole)) (fin_cancel μ (raiseU 3) none)).trans ?_
  refine .more (st (hF (hU 3 injlV c₃) (ccF .hole))
    (Head.cferr μ none 3 0 Val.unit .hole (by decide) rfl)) ?_
  refine .more (st (hF (hU 3 injlV c₃) .hole)
    (Head.creraise μ (opPayload 3 0 Val.unit) .hole rfl)) ?_
  refine .more (st .hole (Head.hunwind μ 3 0 (qualsVal [.unr]) injlV (Val.pair c₃ Val.unit) c₃
    Val.unit .hole (hcl c₃) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- `hnd (4, H₄ₒ) (hnd (1, H₁) (hnd (4, H₄ᵢ) ((perform 1) then x. x unwind perform 4)))`, with
`H₄ᵢ`'s clause answering `()` without resuming, and `H₄ₒ`'s answer clause `hr` and clause `c`. -/
def progFin (hr c : Val) : Expr :=
  hndE (hU 4 hr c) (hndE H₁ (hndE (hU 4 idV (constC Val.unit))
    (thenU (performU 1) (performU 4))))

/-- The finaliser performs `4` under the running cancel, and the live outer `4` resumes it. -/
def progFinOp : Expr := progFin injlV resumeC

/-- The live outer `4` cancels the finaliser's continuation. -/
def progNC₁ : Expr := progFin idV cancelC

/-- `progFin`'s cancel reaches the finaliser's `perform 4`: the dead inner `4` is removed. -/
theorem progFin_cancel (μ : Heap) (hr c : Val) :
    Steps (ℍ := ℍ) μ (progFin hr c) μ
      (hndE (hU 4 hr c) ((ccF (cfF (cancelVal none) .hole)).plug (performU 4))) := by
  refine (Steps.plug (hF (hU 4 hr c) .hole) (cancel_start μ 1 idV
    (hF (hU 4 idV (constC Val.unit)) (uF (performU 4) .hole)) rfl)).trans ?_
  show Steps μ ((hF (hU 4 hr c) (ccF .hole)).plug
    (ubindE (Val.pair idV (finV (performU 4))) (raiseE (.val (cancelVal none))))) μ _
  exact Steps.plug (hF (hU 4 hr c) (ccF .hole)) (fin_cancel μ (performU 4) none)

/-- **`progFinOp`**: the finaliser's operation passes the dead inner `4` and the cancel's
delimiter, the live outer `4` resumes it, the finaliser returns, and the cancel answers `()`. -/
theorem progFinOp_run (μ : Heap) : Steps (ℍ := ℍ) μ progFinOp μ (.val (Val.inj₁ Val.unit)) := by
  refine (progFin_cancel μ injlV resumeC).trans ?_
  refine (resume_start μ 4 injlV (ccF (cfF (cancelVal none) .hole)) rfl).trans ?_
  refine .more (st (hF (hU 4 injlV resumeC) (ccF .hole)) (Head.cfret μ none Val.unit)) ?_
  refine .more (st (hF (hU 4 injlV resumeC) .hole) (Head.cancel μ .hole rfl)) ?_
  refine .more (st .hole (Head.hret μ 4 (qualsVal [.unr]) injlV (Val.pair resumeC Val.unit)
    Val.unit)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- **`progNC₁`**: the outer `4` cancels the finaliser's continuation.  Its region is the running
finaliser's `cfin` and the first cancel's delimiter, which is dead: the new cancel passes the
`cfin` (`[cfin-cancel]`), keeps no error, and answers `()` at its own delimiter. -/
theorem progNC₁_run (μ : Heap) : Steps (ℍ := ℍ) μ progNC₁ μ (.val Val.unit) := by
  refine (progFin_cancel μ idV cancelC).trans ?_
  refine (cancel_start μ 4 idV (ccF (cfF (cancelVal none) .hole)) rfl).trans ?_
  show Steps μ ((ccF (cfF (cancelVal none) .hole)).plug (raiseE (.val (cancelVal none)))) μ _
  refine .more (st (ccF .hole) (Head.cfcancel μ none none .hole rfl)) ?_
  refine .more (st .hole (Head.cancel μ .hole rfl)) ?_
  exact .refl _ _

/-- `hnd (2, H₂ₒ) (hnd (4, H₄ₒ) (hnd (1, H₁) (((perform 1) then x. x unwind raise 2) then y. y
unwind perform 4)))`, with `H₂ₒ`'s clause answering `inj₂ ()`, and `H₄ₒ`'s answer clause
`λx. inj₁ x` and clause `c`. -/
def progKD (c : Val) : Expr :=
  hndE (hU 2 idV (constC (Val.inj₂ Val.unit))) (hndE (hU 4 injlV c)
    (hndE H₁ (thenU (thenU (performU 1) (raiseU 2)) (performU 4))))

/-- `H₄ₒ`'s clause answers `inj₁ ()` and drops its continuation. -/
def progDrop : Expr := progKD (constC (Val.inj₁ Val.unit))

/-- `H₄ₒ`'s clause resumes its continuation. -/
def progKeep : Expr := progKD resumeC

/-- `progKD`'s cancel: the inner finaliser's raise of `2` is kept, and the outer finaliser performs
`4` with the kept error in its `cfin`. -/
theorem progKD_cancel (μ : Heap) (c : Val) :
    Steps (ℍ := ℍ) μ (progKD c) μ
      ((hF (hU 2 idV (constC (Val.inj₂ Val.unit))) (hF (hU 4 injlV c) .hole)).plug
        ((ccF (cfF (cancelVal (some (opPayload 2 0 Val.unit))) .hole)).plug (performU 4))) := by
  let Ko : Kont := hF (hU 2 idV (constC (Val.inj₂ Val.unit))) (hF (hU 4 injlV c) .hole)
  refine (Steps.plug Ko (cancel_start μ 1 idV (uF (performU 4) (uF (raiseU 2) .hole)) rfl)).trans ?_
  show Steps μ ((Ko.comp (ccF (uF (performU 4) .hole))).plug
    (ubindE (Val.pair idV (finV (raiseU 2))) (raiseE (.val (cancelVal none))))) μ _
  refine (Steps.plug (Ko.comp (ccF (uF (performU 4) .hole))) (fin_cancel μ (raiseU 2) none)).trans ?_
  refine .more (st (Ko.comp (ccF (uF (performU 4) .hole)))
    (Head.cferr μ none 2 0 Val.unit .hole (by decide) rfl)) ?_
  show Steps μ ((Ko.comp (ccF .hole)).plug (ubindE (Val.pair idV (finV (performU 4)))
    (raiseE (.val (cancelVal (some (opPayload 2 0 Val.unit))))))) μ _
  exact Steps.plug (Ko.comp (ccF .hole)) (fin_cancel μ (performU 4) _)

/-- **`progDrop`**: `H₄ₒ`'s unrestricted clause drops the continuation that holds the kept error
`2`, so `H₂ₒ`'s clause never runs. -/
theorem progDrop_run (μ : Heap) : Steps (ℍ := ℍ) μ progDrop μ (.val (Val.inj₁ Val.unit)) := by
  refine (progKD_cancel μ _).trans ?_
  refine (Steps.plug (hF (hU 2 idV (constC (Val.inj₂ Val.unit))) .hole) (const_start μ 4 injlV
    (Val.inj₁ Val.unit) (fun _ => rfl) (ccF (cfF (cancelVal (some (opPayload 2 0 Val.unit))) .hole))
    rfl)).trans ?_
  refine .more (st .hole (Head.hret μ 2 (qualsVal [.unr]) idV
    (Val.pair (constC (Val.inj₂ Val.unit)) Val.unit) (Val.inj₁ Val.unit))) ?_
  refine .more (st .hole (Head.beta μ _ (Val.inj₁ Val.unit))) ?_
  exact .refl _ _

/-- **`progKeep`**: `H₄ₒ` resumes the finaliser; the finaliser returns, the cancel re-raises the
kept error `2` at the canceller, and the live `H₂ₒ` catches it. -/
theorem progKeep_run (μ : Heap) : Steps (ℍ := ℍ) μ progKeep μ (.val (Val.inj₂ Val.unit)) := by
  refine (progKD_cancel μ _).trans ?_
  refine (Steps.plug (hF (hU 2 idV (constC (Val.inj₂ Val.unit))) .hole) (resume_start μ 4 injlV
    (ccF (cfF (cancelVal (some (opPayload 2 0 Val.unit))) .hole)) rfl)).trans ?_
  refine .more (st (hF (hU 2 idV (constC (Val.inj₂ Val.unit)))
    (hF (hU 4 injlV resumeC) (ccF .hole))) (Head.cfret μ _ Val.unit)) ?_
  refine .more (st (hF (hU 2 idV (constC (Val.inj₂ Val.unit))) (hF (hU 4 injlV resumeC) .hole))
    (Head.creraise μ (opPayload 2 0 Val.unit) .hole rfl)) ?_
  refine .more (st .hole (Head.hunwind μ 2 0 (qualsVal [.unr]) idV
    (Val.pair (constC (Val.inj₂ Val.unit)) Val.unit) (constC (Val.inj₂ Val.unit)) Val.unit
    (hF (hU 4 injlV resumeC) .hole) (hcl _) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-! ### `[then]` with its finaliser at the abortive row

Before SPEC §24's option A, `[then]` typed its finaliser at the row's abortive operations.  That
rule relied on the by-name suppression: under a dead region its conclusion fails at `prog`'s
`[then]`, `perform 1 then x. x unwind raise 2` at the row `{2, 1}`.  Its premises hold, and the
conclusion asks the continuation of `perform 1` for a cancel run at the empty error table; that run
fires the finaliser, keeps the error `2`, and ends at `raise (0, (0, some 2))`, which the table does
not admit (`not_thenAbort_compatC`).  So `then_compatC` takes the finaliser at the pure row. -/

/-- `[then]`'s compatibility with its finaliser at the row's abortive operations: the rule before
SPEC §24's option A. -/
def ThenAbortCompat : Prop :=
  ∀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy} {S : Row},
    Ctx.SplitP Γ Γ₁ Γ₂ → S.NZ → S.Uniq → (S.Unr → Persistent Γ₂) →
    SemC (ℍ := ℍ) Δ Γ₁ M (CTy.effOf S A) → SemC (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B) →
    SemC (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf S.abortOnly .unit) →
    SemC (ℍ := ℍ) Δ Γ (thenE N D M) (CTy.effOf S B)

/-- The row of `prog`'s `[then]`: the abortive `2` and the affine `1`. -/
def S₁₂ : Row := [⟨2, 0, .aff, .unit, .zero⟩, ⟨1, 0, .aff, .unit, .unit⟩]

/-- `prog`'s `[then]`: `perform 1 then x. x unwind raise 2`. -/
def thenProg : Expr := thenE (.var 0) (raiseU 2) (performU 1)

theorem thenProg_eq : thenProg = (ubindK idV (finV (raiseU 2))).plug (performU 1) := rfl

theorem prog_eq_then : prog = hndE H₁ ((hF H₂ .hole).plug thenProg) := rfl

/-- The old rule's premises hold at `prog`'s `[then]`, by Core's rules, so it would relate the
`[then]` at the row `{2, 1}`. -/
theorem semC_thenProg (h : ThenAbortCompat (ℍ := ℍ)) :
    SemC (ℍ := ℍ) LifeCtx.empty [] thenProg (CTy.effOf S₁₂ .unit) := by
  have hM : CDerives LifeCtx.empty [] (performE (opArgE 1 0 (.val .unit)))
      (.comp (CTy.effOf S₁₂ .unit)) :=
    .effPerform (o := ⟨1, 0, .aff, .unit, .unit⟩) (by rfl) rfl (.unitI .nil)
  have hN : CDerives LifeCtx.empty [⟨.unit, true⟩] (.var 0) (.comp (CTy.effOf S₁₂ .unit)) :=
    .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h) (.ret (.var (.here .nil)))
  have hD : CDerives LifeCtx.empty [⟨.unit, false⟩] (raiseE (opArgE 2 0 (.val .unit)))
      (.comp (CTy.effOf S₁₂.abortOnly .unit)) :=
    .effRaise (o := ⟨2, 0, .aff, .unit, .zero⟩) (by rfl) rfl .unit (.unitI (.cons .nil))
  exact h .nil (by intro o ho; simp [S₁₂] at ho; rcases ho with rfl | rfl <;> decide)
    (by simp [Row.Uniq, S₁₂]) (fun _ s hs => absurd hs List.not_mem_nil)
    (fundamentalC hM) (fundamentalC hN) (fundamentalC hD)

/-- A redex at an evaluation position holds no cancel there that its context lets through. -/
theorem redex_ne_cancel {μ μ' : Heap} {a a' : Expr} (ha : Head (ℍ := ℍ) μ a μ' a') (K' K : Kont)
    (err : Option Val) (hK : K.Catches 0 = false) :
    K'.plug a ≠ K.plug (raiseE (.val (cancelVal err))) := fun h =>
  nested_op (r := true) (payloadName_cancelVal err) (by simpa [OpFree] using hK) ha
    (by simpa [opE] using h)

/-- The cancel run of `prog`'s `[then]`, from its start: the finaliser fires, raises `2`, and the
cancel keeps it.  Every run from the start ends at one of these four terms. -/
theorem thenCancel_runs {A : Alloc} {k k' : Nat} {μ μ' : Heap} {t : Expr}
    (h : ARun (ℍ := ℍ) A k μ ((ubindK idV (finV (raiseU 2))).plug
      (raiseE (.val (cancelVal none)))) k' μ' t) :
    t = (ubindK idV (finV (raiseU 2))).plug (raiseE (.val (cancelVal none))) ∨
    t = cfinE (cancelVal none) (.app (.val (Val.lam (raiseU 2))) (.val Val.unit)) ∨
    t = cfinE (cancelVal none) (raiseU 2) ∨
    t = raiseE (.val (cancelVal (some (opPayload 2 0 Val.unit)))) := by
  have s₀ : AStep1 (ℍ := ℍ) A k μ ((ubindK idV (finV (raiseU 2))).plug
      (raiseE (.val (cancelVal none)))) k μ
      (cfinE (cancelVal none) (.app (.val (Val.lam (raiseU 2))) (.val Val.unit))) :=
    ⟨.hole, _, _, rfl, rfl, AHead.det (Head.ufinC μ idV (finV (raiseU 2)) none .hole rfl) rfl⟩
  have s₁ : AStep1 (ℍ := ℍ) A k μ (cfinE (cancelVal none) (.app (.val (Val.lam (raiseU 2)))
      (.val Val.unit))) k μ (cfinE (cancelVal none) (raiseU 2)) :=
    ⟨cfF (cancelVal none) .hole, _, _, rfl, rfl, AHead.det (Head.beta μ (raiseU 2) Val.unit) rfl⟩
  have s₂ : AStep1 (ℍ := ℍ) A k μ (cfinE (cancelVal none) (raiseU 2)) k μ
      (raiseE (.val (cancelVal (some (opPayload 2 0 Val.unit))))) :=
    ⟨.hole, _, _, rfl, rfl, AHead.det (Head.cferr μ none 2 0 Val.unit .hole (by decide) rfl) rfl⟩
  cases h with
  | refl => exact .inl rfl
  | more s r =>
    obtain ⟨rfl, rfl, rfl⟩ := BoCa.BoLo.AStep1.deterministic s s₀
    cases r with
    | refl => exact .inr (.inl rfl)
    | more s r =>
      obtain ⟨rfl, rfl, rfl⟩ := BoCa.BoLo.AStep1.deterministic s s₁
      cases r with
      | refl => exact .inr (.inr (.inl rfl))
      | more s r =>
        obtain ⟨rfl, rfl, rfl⟩ := BoCa.BoLo.AStep1.deterministic s s₂
        cases r with
        | refl => exact .inr (.inr (.inr rfl))
        | more s _ => exact (raise_final _ _ _ (BoCa.BoLo.AStep1.toStep1 s)).elim

/-- **The old `[then]` rule fails under a dead region**: at `prog`'s `[then]` its premises hold,
and its conclusion asks the continuation of `perform 1` for a cancel run at the empty error table,
whose every run fires the finaliser and keeps the error `2`, a cancel the table does not admit. -/
theorem not_thenAbort_compatC : ¬ ThenAbortCompat (ℍ := ℍ) := by
  intro h
  have hs := semC_thenProg h LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have he : substAll [] thenProg = thenProg := Adequacy.psub_nil 0 _
  rw [he] at hs
  have hE := (cC_effOf S₁₂ .unit [] LSub.empty thenProg PMap.empty).mp hs
  have hW := ewp_unfold (opTable_mono _) hE
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', -, h₂, h₃, -, h₆, -, ⟨k', hrun⟩, -, -, -,
    hT', htg', -, -, hpost⟩ :=
    hW PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
      Alloc.leastFree 0
  -- `prog`'s `[then]` is a stop: it takes no step
  have ht : t = thenProg := by
    cases hrun with
    | refl => rfl
    | more s _ =>
        obtain ⟨K₁, a, a', hK₁, -, hh⟩ := BoCa.BoLo.AStep1.toStep1 s
        exact (nested_op (K₀ := ubindK idV (finV (raiseU 2))) (r := false)
          (payloadName_opPayload 1 0 Val.unit)
          (by simp [OpFree, Kont.HasHnd, Val.pair, Expr.val]) hh
          (by rw [← hK₁, thenProg_eq]; rfl)).elim
  subst ht
  rcases hpost with ⟨v, hv, -⟩ | hp
  · exact absurd (hv ▸ v.2 : IsVal thenProg) (by simp [thenProg, thenE])
  rcases hp with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  swap
  · obtain ⟨⟨hK, -⟩, -⟩ := pure_sep_iff.mp hp
    exact plug_perform_ne_raise _ _ _ _ (thenProg_eq.symm.trans hK)
  obtain ⟨⟨hK, -, hT, -⟩, ρa, ρk, hcak, hPA, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨rfl, hpay⟩ := plug_perform_inj (thenProg_eq.symm.trans hK)
  obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hpay
  have hen : en = OpSig.ent LSub.empty ⟨1, 0, .aff, .unit, .unit⟩ := by
    simp [Row.tab, Row.find, S₁₂] at hT; exact hT.symm
  subst hen
  have hρa : ρa = PMap.empty := hPA.1
  subst hρa
  have hρk : ρ' = ρk := eq_of_compS_empty_left hcak
  subst hρk
  have hρ' : fρ' = ρ' := eq_of_compS_empty_left h₂
  subst hρ'
  -- the continuation's cancel
  have hco := (hcont.2 ls' (ext_of_same (fun _ => Iff.rfl) _)).2 (by simp [OpSig.ent])
  have hco' : wpG ls' ((ubindK idV (finV (raiseU 2))).plug (raiseE (.val (cancelVal none))))
      (ewpPost (cancelTab OpTab.empty) fun _ _ _ => False) fρ' := by
    have := (ewp_abortive (cancelTab_abortive OpTab.empty)).mp hco
    rwa [dead_ubindK] at this
  obtain ⟨_, _, _, _, _, t, _, _, _, _, _, _, _, _, _, _, ⟨k'', hrun₂⟩, _, _, _, _, _, _, _, hpost₂⟩ :=
    hco' ρp fρ'p ps' h₃ (ResU.CompS.comm h₆) hT' htg' Alloc.leastFree 0
  rcases hpost₂ with ⟨_, _, hf⟩ | ⟨K', err, hc⟩
  · exact hf
  obtain ⟨⟨rfl, hK'⟩, _, _, -, herr, -⟩ := pure_sep_iff.mp hc
  have hnone : err = none := by
    cases err with
    | none => rfl
    | some _ =>
        obtain ⟨_, _, _, _, he⟩ := herr
        obtain ⟨⟨-, hTe, -⟩, -⟩ := pure_sep_iff.mp he
        simp [OpTab.empty] at hTe
  subst hnone
  rcases thenCancel_runs hrun₂ with h₀ | h₁ | h₂ | h₃
  · exact redex_ne_cancel (Head.ufinC (ℍ := ℍ) μ idV (finV (raiseU 2)) none .hole rfl) .hole K'
      none hK' h₀.symm
  · exact redex_ne_cancel (Head.beta (ℍ := ℍ) μ (raiseU 2) Val.unit) (cfF (cancelVal none) .hole)
      K' none hK' h₁.symm
  · exact redex_ne_cancel (Head.cferr (ℍ := ℍ) μ none 2 0 Val.unit .hole (by decide) rfl) .hole
      K' none hK' h₂.symm
  · obtain ⟨-, hp⟩ := plug_raise_inj (K := K') (K' := .hole) h₃
    have := cancelVal_inj hp
    simp at this

/-! ### The interpreter's runs

`Support`'s interpreter (`eval`) follows the machine on each program. -/

/-- `prog` stops at the raise of `2`, which no handler catches. -/
theorem prog_eval : (match eval prog with | .stuck .unhandled => true | _ => false) = true := by
  decide

theorem prog₃_eval :
    (match eval prog₃ with | .value ⟨.inj₂ .unit, _⟩ false => true | _ => false) = true := by
  decide

theorem progOut_eval :
    (match eval progOut with | .value ⟨.inj₂ .unit, _⟩ false => true | _ => false) = true := by
  decide

theorem progRe_eval :
    (match eval progRe with | .value ⟨.inj₂ .unit, _⟩ false => true | _ => false) = true := by
  decide

theorem progFinOp_eval :
    (match eval progFinOp with | .value ⟨.inj₁ .unit, _⟩ false => true | _ => false) = true := by
  decide

theorem progNC₁_eval :
    (match eval progNC₁ with | .value ⟨.unit, _⟩ false => true | _ => false) = true := by
  decide

theorem progDrop_eval :
    (match eval progDrop with | .value ⟨.inj₁ .unit, _⟩ false => true | _ => false) = true := by
  decide

theorem progKeep_eval :
    (match eval progKeep with | .value ⟨.inj₂ .unit, _⟩ false => true | _ => false) = true := by
  decide

end BoCa.Fig16.LogRel.Core.CancelIntercept
