import Core.EffCancel
import Core.EffMachine
import Core.Fundamental
import Core.Examples
import Core.Inversions
import Core.Tied

/-!
# Core — finalisers with effects, typed  `[spec §27]`

§19's cancel programs (`Core/EffCancel.lean`) at §27's typing.  Their handlers' operations are
unrestricted, so `κ`'s slot is `!U((1 ⊸ F_Σ R) & C)`, and the kernel reads a variable at a
computation type only from a `U` slot.  So a clause binds `κ` first, `(λk. k (inj₂ ())) κ`, and the
typed program is the untyped one with that clause (`cancelCT`, `resumeCT`); it runs as the untyped
one does, one β-step longer at each use of `κ`.

Each typed program is derived (`d_…`) and its run computed (`…_run`):

| program | cancel row of `perform 1`'s continuation | run |
|---|---|---|
| `progT` | `{2}`, typed at a row holding `2`, and at no row without `2` (`not_der_progT`) | a raise of `2` no handler catches |
| `progOutT` | `{2}`, the outer `2` live | `inj₂ ()` |
| `progOutTA` | `{2}` at a cancellable raise of `2` (tied, `Core/EffCancelRuns.lean`) | `inj₂ ()` |
| `cancelKeptT` | `{3}`, `H₃` outside | `inj₂ ()` |
| `progReT` | `{3}`: `f ()` at `{1}`, the region re-entering the site `3` | `inj₂ ()` |
| `progFinOpT` | `{4}`: the finaliser performs `4`, the outer `4` resumes it | `inj₁ ()` |
| `progNC₁T` | `{4}`: the outer `4` cancels the finaliser's continuation (`[cfin-cancel]`) | `()` |
| `progDropT` | `{2, 4⟨{2}⟩}`: the kept `2` pending at the second finaliser's `4` (`pend`); `H₄ₒ` drops `κ₄` | `inj₁ ()` |
| `progKeepT` | `{2, 4⟨{2}⟩}`; `H₄ₒ` resumes `κ₄`, and the kept `2` reaches `H₂ₒ` | `inj₂ ()` |

**The rejections (decision D3)**, each by inversion of `CDerives` (`Core/Inversions.lean`): the
program is read from the outside in, each step by its rule and then the rules that conclude with
their premise's term, which only grow rows (`JR.rowLe`).

* `progT` has no derivation at a row without `2` (`not_der_progT`): the `[then]` puts `2` in the
  cancel row of `1`, and `H₁`'s clause reads `κ`'s cancel branch, at `F_{{2} ⊕ Σ} 1`, at its own
  row `Σ`.
* `progNCrecT`, two finalisers that perform `4` under the handler of `4` that cancels, has no
  derivation at all (`not_der_progNCrecT`): the second finaliser is a leftover of the first one's
  cancel, so `⋈` puts `4` in the cancel row of the `4` in the cancel row of `1`, which the
  cancelling handler's clause row, its own outer row, cannot hold.  Its run ends at a `perform 4`
  outside every handler of `4` (`progNCrecT_run`, `progNCrecT_stuck`).
* E7c, `timeout (handle exnᵢ {…} (body (raise exnᵢ ())))`, has no derivation at a row without
  `exnᵢ` (`not_der_e7c`), and is typed at the row of `exnᵢ` (`dAt_e7c_lift`, `d_e7c_lift`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CancelIntercept
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE performE ccatchE cfinE ubindE opPayload
  clauseAt kappa cancelVal)
open BoCa.Lifetime (LSub LifeCtx)

/-! ### Clauses that bind `κ` first -/

/-- The clause `λp. let (x, k) = p; (λk'. k' (inj₂ ())) k`: cancel `κ`. -/
def cancelCT : Val :=
  Val.lam (.letpair (.var 0) (.app (.val (Val.lam (.app (.var 0) (.val (Val.inj₂ Val.unit)))))
    (.var 0)))

/-- The clause `λp. let (x, k) = p; (λk'. (k' (inj₁ ())) x) k`: resume `κ` with the argument. -/
def resumeCT : Val :=
  Val.lam (.letpair (.var 0) (.app (.val (Val.lam (.app (.app (.var 0) (.val (Val.inj₁ Val.unit)))
    (.var 2)))) (.var 0)))

/-- **A cancelling clause**: `hnd (n, H) K[perform (n, (0, ()))]`, `K` free of `n`, runs to the
cancel of the dead region `K†`. -/
theorem cancelT_start (μ : Heap) (n : UInt32) (hr : Val) (K : Kont) (hK : K.HasHnd n = false) :
    Steps (ℍ := ℍ) μ (hndE (hU n hr cancelCT) (K.plug (performU n))) μ
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) := by
  let κv : Val := ⟨kappa (hU n hr cancelCT) K, isVal_kappa _ _⟩
  refine .more (st .hole (Head.hop μ n 0 (qualsVal [.unr]) hr (Val.pair cancelCT Val.unit)
    cancelCT Val.unit K (hcl cancelCT) hK)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  show Steps μ (.app (.val (Val.lam (.app (.var 0) (.val (Val.inj₂ Val.unit)))))
    (Expr.subst 0 Val.unit (Expr.shift 1 0 κv.1))) μ _
  rw [subst_shift_one]
  refine .more (st .hole (Head.beta μ _ κv)) ?_
  exact kappa_cancel_steps μ _ K

/-- **A resuming clause**: `hnd (n, H) K[perform (n, (0, ()))]`, `K` free of `n`, runs to
`hnd (n, H) K[()]`. -/
theorem resumeT_start (μ : Heap) (n : UInt32) (hr : Val) (K : Kont) (hK : K.HasHnd n = false) :
    Steps (ℍ := ℍ) μ (hndE (hU n hr resumeCT) (K.plug (performU n))) μ
      (hndE (hU n hr resumeCT) (K.plug (.val Val.unit))) := by
  let κv : Val := ⟨kappa (hU n hr resumeCT) K, isVal_kappa _ _⟩
  refine .more (st .hole (Head.hop μ n 0 (qualsVal [.unr]) hr (Val.pair resumeCT Val.unit)
    resumeCT Val.unit K (hcl resumeCT) hK)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  show Steps μ (.app (.val (Val.lam (.app (.app (.var 0) (.val (Val.inj₁ Val.unit)))
    (.val Val.unit))))
    (Expr.subst 0 Val.unit (Expr.shift 1 0 κv.1))) μ _
  rw [subst_shift_one]
  refine .more (st .hole (Head.beta μ _ κv)) ?_
  exact kappa_resume_steps μ _ K Val.unit

/-! ### The programs -/

/-- Handler `1`: its clause cancels `κ`. -/
def H₁T : Val := hU 1 idV cancelCT

/-- `hnd (1, H₁T) K[perform (1, (0, ()))]`, `K = hnd (2, H₂) (ubind (id, λ_. raise m) [·])`. -/
def bodyT (m : UInt32) : Expr := hndE H₁T ((K m).plug (performU 1))

/-- The finaliser raises `2`, a name handled only inside the region. -/
def progT : Expr := bodyT 2

/-- `hnd (2, H₂ₒ) progT`: a live handler of `2` outside the region. -/
def progOutT : Expr := hndE (hU 2 injlV (constC (Val.inj₂ Val.unit))) progT

/-- The cancel of `bodyT m`: the dead handler `2` is removed, the finaliser raises `m`, the error is
kept and re-raised at the canceller. -/
theorem bodyT_run (m : UInt32) (hm : m ≠ 0) (μ : Heap) :
    Steps (ℍ := ℍ) μ (bodyT m) μ (raiseU m) := by
  refine (cancelT_start μ 1 idV (K m) rfl).trans ?_
  show Steps μ (ccatchE ((uF (raiseU m) .hole).plug (raiseE (.val (cancelVal none))))) μ _
  refine (Steps.plug (ccF .hole) (fin_cancel μ (raiseU m) none)).trans ?_
  refine .more (st (ccF .hole) (Head.cferr μ none m 0 Val.unit .hole hm rfl)) ?_
  refine .more (st .hole (Head.creraise μ (opPayload m 0 Val.unit) .hole rfl)) ?_
  exact .refl _ _

/-- **`progT`**: the dead handler `2` catches nothing; the finaliser's error is kept and re-raised
at the canceller, where no handler catches it. -/
theorem progT_run (μ : Heap) : Steps (ℍ := ℍ) μ progT μ (raiseU 2) := bodyT_run 2 (by decide) μ

/-- **`progOutT`**: the error of name `2`, handled inside the region by a dead instance, reaches
the live instance outside it. -/
theorem progOutT_run (μ : Heap) : Steps (ℍ := ℍ) μ progOutT μ (.val (Val.inj₂ Val.unit)) := by
  refine (Steps.plug (hF (hU 2 injlV (constC (Val.inj₂ Val.unit))) .hole) (progT_run μ)).trans ?_
  refine .more (st .hole (Head.hunwind μ 2 0 (qualsVal [.unr]) injlV
    (Val.pair (constC (Val.inj₂ Val.unit)) Val.unit) (constC (Val.inj₂ Val.unit)) Val.unit .hole
    (hcl _) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- A handler of the name `n` whose one operation is at the qualifier `q`, its answer clause `hr`
and its clause `c`.  At `q = unr` it is `hU n hr c`. -/
def hQ (n : UInt32) (q : Qual) (hr c : Val) : Val :=
  hndVal n (qualsVal [q]) hr (Val.pair c Val.unit)

/-- `progT`'s region with its handler of `2` at a cancellable operation:
`hnd (2, H₂) (ubind (id, λ_. raise m) [·])`, `H₂`'s tag `cancel`. -/
def KA (m : UInt32) : Kont := hF (hQ 2 .cancel idV (constC Val.unit)) (uF (raiseU m) .hole)

/-- `progT` with its raise of `2` cancellable: the region `KA 2`. -/
def progTA : Expr := hndE H₁T ((KA 2).plug (performU 1))

/-- `progOutT` with its raise of `2` cancellable: every handler of `2` has the tag `cancel`. -/
def progOutTA : Expr := hndE (hQ 2 .cancel injlV (constC (Val.inj₂ Val.unit))) progTA

/-- **`progOutTA`** runs as `progOutT`: a raise is caught whatever its handler's tag
(`[unwind]`), so the dead inner `2` catches nothing, the finaliser's error is kept, re-raised at the
canceller, and caught by the live outer `2`. -/
theorem progOutTA_run (μ : Heap) : Steps (ℍ := ℍ) μ progOutTA μ (.val (Val.inj₂ Val.unit)) := by
  let H₂ₒ : Val := hQ 2 .cancel injlV (constC (Val.inj₂ Val.unit))
  refine (Steps.plug (hF H₂ₒ .hole) (cancelT_start μ 1 idV (KA 2) rfl)).trans ?_
  show Steps μ ((hF H₂ₒ (ccF .hole)).plug
    (ubindE (Val.pair idV (finV (raiseU 2))) (raiseE (.val (cancelVal none))))) μ _
  refine (Steps.plug (hF H₂ₒ (ccF .hole)) (fin_cancel μ (raiseU 2) none)).trans ?_
  refine .more (st (hF H₂ₒ (ccF .hole)) (Head.cferr μ none 2 0 Val.unit .hole (by decide) rfl)) ?_
  refine .more (st (hF H₂ₒ .hole) (Head.creraise μ (opPayload 2 0 Val.unit) .hole rfl)) ?_
  refine .more (st .hole (Head.hunwind μ 2 0 (qualsVal [.cancel]) injlV
    (Val.pair (constC (Val.inj₂ Val.unit)) Val.unit) (constC (Val.inj₂ Val.unit)) Val.unit .hole
    (hcl _) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-! ### Typing -/

/-- The operation `0` of the name `n`, unrestricted and abortive: `raise : 1 ↠^unr 0`. -/
def rSig (n : UInt32) : OpSig := ⟨n, 0, .unr, .unit, .zero, .ret .unit, false⟩

/-- The operation `0` of the name `n`, unrestricted, `1 ↠ 1`, at the cancel row `F`. -/
def pSig (n : UInt32) (F : CTy) : OpSig := ⟨n, 0, .unr, .unit, .unit, F, false⟩

/-- The cancel row of a raise of `m`. -/
abbrev finR (m : UInt32) : CTy := CTy.effOf [rSig m] .unit

/-- The operation `0` of the name `n`, cancellable and abortive: `raise : 1 ↠^cancel 0`. -/
def rSigA (n : UInt32) : OpSig := ⟨n, 0, .cancel, .unit, .zero, .ret .unit, false⟩

/-- The cancel row of a cancellable raise of `m`. -/
abbrev finRA (m : UInt32) : CTy := CTy.effOf [rSigA m] .unit

/-- An abortive operation's clause type does not read its qualifier, at a cancellable or
unrestricted one: `!U(A ⊸ F_Σ R)`. -/
theorem clauseTy_abortive {S : Row} {R A : VTy} {q : Qual} {F : CTy} (hq : q ≠ .lin) :
    clauseTy S R (q, A, .zero) F = .bang (.thunk (.arr A (CTy.effOf S R))) := by
  cases q <;> simp_all [clauseTy, VTy.isZero]

theorem hndE_hU (n : UInt32) (hr c : Val) (e : Expr) :
    hndE (hU n hr c) e = hndExpr n [.unr] (.pair (.val hr) (.pair (.val c) (.val Val.unit))) e :=
  rfl

theorem ofEff_raise (n : UInt32) : Row.ofEff n [(.unr, .unit, .zero)] 0 finsNil = [rSig n] := rfl

theorem ofEff_op (n : UInt32) (F : CTy) :
    Row.ofEff n [(.unr, .unit, .unit)] 0 (fun _ => F) = [pSig n F] := rfl

/-- `λx. x : !U(A ⊸ F_Σ A)`, over a consumed context. -/
theorem d_idVΓ {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (A : VTy) :
    CDerives Δ Γ (.val idV) (.val (retTy S A A)) :=
  .bangThunkV (dead_noLive hΓ) rfl (.lam (.effSub (RowLe.nil S) (.ret (.var (.here hΓ.toP)))))

/-- `λx. x : !U(A ⊸ F_Σ A)`. -/
theorem d_idV {Δ : LifeCtx} (S : Row) (A : VTy) :
    CDerives Δ [] (.val idV) (.val (retTy S A A)) :=
  d_idVΓ .nil S A

/-- `λx. inj₁ x : !U(A ⊸ F_Σ (A ⊕ B))`. -/
theorem d_injlV {Δ : LifeCtx} (S : Row) (A B : VTy) :
    CDerives Δ [] (.val injlV) (.val (retTy S A (.sum A B))) :=
  .bangThunkV (dead_noLive .nil) rfl
    (.lam (.effSub (RowLe.nil S) (.ret (.sumI₁ (.var (.here .nil))))))

/-- An abortive operation's clause `λ_. v`, at `!U(1 ⊸ F_Σ R)`, over a consumed context. -/
theorem d_constC_raiseΓ {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) {R : VTy} {v : Val}
    (hv : CDerives Δ (⟨.unit, false⟩ :: Γ) (.val v) (.val R)) :
    CDerives Δ Γ (.val (constC v)) (.val (clauseTy S R (.unr, .unit, .zero) (.ret .unit))) :=
  .bangThunkV (dead_noLive hΓ) rfl (.lamDead (.effSub (RowLe.nil S) (.ret hv)))

/-- An abortive operation's clause `λ_. v`, at `!U(1 ⊸ F_Σ R)`. -/
theorem d_constC_raise {Δ : LifeCtx} (S : Row) {R : VTy} {v : Val}
    (hv : CDerives Δ [⟨.unit, false⟩] (.val v) (.val R)) :
    CDerives Δ [] (.val (constC v)) (.val (clauseTy S R (.unr, .unit, .zero) (.ret .unit))) :=
  d_constC_raiseΓ .nil S hv

/-- **The cancelling clause**, at the cancel row `F`: `κ (inj₂ ())` is at `F_{F ⊕ Σ} 1`, read at
the clause's row `Σ` by `[sub]` (D3's check). -/
theorem d_cancelCT {Δ : LifeCtx} {S : Row} {F : CTy} (hF : F.isTop = false)
    (hle : RowLe (F.rowOf ++ S) S) :
    CDerives Δ [] (.val cancelCT) (.val (clauseTy S .unit (.unr, .unit, .unit) F)) := by
  show CDerives Δ [] (.val cancelCT)
    (.val (.bang (.thunk (.arr (.tensor .unit (kTy S .unit .unr .unit F)) (CTy.effOf S .unit)))))
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  refine .tensorE (.left .nil) (.var (.here .nil)) ?_
  refine .bind (A := .thunk (.amp (.arr .unit (CTy.effOf S .unit)) (cancelTy S F)))
    (.left (.right (.dead .nil))) (.ret (.bangE (.var (.here (.cons (.cons .nil)))))) ?_
  have h₂ : CDerives Δ [⟨.thunk (.amp (.arr .unit (CTy.effOf S .unit)) (cancelTy S F)), true⟩,
      ⟨kTy S .unit .unr .unit F, false⟩, ⟨.unit, true⟩,
      ⟨.tensor .unit (kTy S .unit .unr .unit F), false⟩]
      (.app (.var 0) (.val (Val.inj₂ Val.unit))) (.comp (cancelTy S F)) :=
    .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S .unit)) (cancelTy S F))
      (.here (.cons (.drop rfl (.cons .nil)))))
  have hC : cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit := by simp [cancelTy, hF]
  refine .effSub hle ?_
  rw [← hC]
  exact h₂

/-- **The resuming clause**: `(κ (inj₁ ())) x`. -/
theorem d_resumeCT {Δ : LifeCtx} (S : Row) (R : VTy) (F : CTy) :
    CDerives Δ [] (.val resumeCT) (.val (clauseTy S R (.unr, .unit, .unit) F)) := by
  show CDerives Δ [] (.val resumeCT)
    (.val (.bang (.thunk (.arr (.tensor .unit (kTy S R .unr .unit F)) (CTy.effOf S R)))))
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  refine .tensorE (.left .nil) (.var (.here .nil)) ?_
  refine .bind (A := .thunk (.amp (.arr .unit (CTy.effOf S R)) (cancelTy S F)))
    (.left (.right (.dead .nil))) (.ret (.bangE (.var (.here (.cons (.cons .nil)))))) ?_
  exact .app (.left (.dead (.right (.dead .nil))))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S R)) (cancelTy S F))
      (.here (.cons (.cons (.cons .nil))))))
    (.there (.there (.here (.cons .nil))))

/-- **The `[then]` of `progT`**: `perform 1 then x. x unwind raise 2` at `{2, 1⟨{2}⟩}`.  The cancel
row of `perform 1`'s continuation holds the finaliser's raise (`F ⋈ {2} ≤ {2}`). -/
theorem d_then₂ {Δ : LifeCtx} :
    CDerives Δ [] ((uF (raiseU 2) .hole).plug (performU 1))
      (.comp (CTy.effOf [rSig 2, pSig 1 (finR 2)] .unit)) := by
  show CDerives Δ [] (thenE (.var 0) (raiseU 2) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 2]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finR 2) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit)) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSig 2) rfl rfl .unit (.unitI (.cons .nil))

/-- `hnd (2, H₂) [·]` around `progT`'s `[then]`, at the outer row `{1⟨{2}⟩}`: its name is not
there, and the `[then]`'s raise of `2` is its operation. -/
theorem d_inner₂ {Δ : LifeCtx} :
    CDerives Δ [] ((K 2).plug (performU 1)) (.comp (CTy.effOf [pSig 1 (finR 2)] .unit)) := by
  show CDerives Δ [] (hndExpr 2 [.unr] (.pair (.val idV) (.pair (.val (constC Val.unit))
    (.val Val.unit))) ((uF (raiseU 2) .hole).plug (performU 1))) _
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_constC_raise _ (.unitI (.cons .nil)))
      (.unitI .nil)))
    (by decide) (by simp [pSig]) (by simp) rfl d_then₂

/-- **`progT` is typed at a row holding `2`**: the cancel row of `perform 1`'s continuation is
`{2}`, and `H₁`'s clause reads `κ`'s cancel at `F_{{2} ⊕ Σ} 1` at its row `Σ = {2}`. -/
theorem d_progT {Δ : LifeCtx} : CDerives Δ [] progT (.comp (CTy.effOf [rSig 2] .unit)) := by
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    ((K 2).plug (performU 1))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 2)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) rfl ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [show (finR 2).rowOf ++ [rSig 2] = [rSig 2, rSig 2] from rfl] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
    subst ho
    exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · refine .effSub (RowLe.of_mem fun o ho => ?_) d_inner₂
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨pSig 1 (finR 2), rfl, OpSig.LeF.refl _⟩

/-- **`progOutT` is typed at `F (1 ⊕ 1)`**: the live outer `2` is `progT`'s row. -/
theorem d_progOutT {Δ : LifeCtx} : CDerives Δ [] progOutT (.comp (.ret (.sum .unit .unit))) := by
  show CDerives Δ [] (hndExpr 2 [.unr] (.pair (.val injlV)
    (.pair (.val (constC (Val.inj₂ Val.unit))) (.val Val.unit))) progT)
    (.comp (CTy.effOf [] (.sum .unit .unit)))
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_injlV _ .unit .unit)
      (.tensorI .nil (d_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil)))
    (by decide) (by simp) (by simp) rfl d_progT

/-! ### `progT` at no row without `2` (D3)

The inversion reads the program from the outside in, each step by its rule and then the same-term
rules, which only grow rows (`JR.rowLe`):

* `[handle] 1` (`der_hndJ`): the clause tuple at `clausesTyO Σ R ob E fs` (`κ` bare, or boxed by
  BOXED-κ, §28), the body at `F_{1⟨fs 0⟩, Σ} A`, and the program's row above `Σ`;
* `[handle] 2` (`der_hndJ`) and `[then]` (`der_thenJ`): `perform 1`'s row finds `1`
  (`der_performJ`) and the finaliser's row finds `2` (`der_raiseJ`), so the `[then]`'s premise
  `F ⋈ {2} ≤ Σ(1).fin` puts `2` in the cancel row of `1` at the `[then]`, and `[sub]` up to the body
  of `[handle] 1` keeps it there: `2` is in `fs 0`;
* the clause (`lam_bang`, `der_letpair`, `der_app`, `lam_arr`): `κ` is bound and its cancel branch
  applied, at `F_{fs 0 ⊕ Σ} 1` (`kappa_cancel_jr`), read at the clause's row `Σ` by the same-term
  rules: `Σ` holds `2`. -/

section Rejections
open BoCa.Fig16.LogRel.Core.Inversions

/-- **`cancelCT` reads `κ`'s cancel at its row**: at the clause type of an unrestricted operation
`A ↠ B`, `B` no `0`, at the cancel row `F`, the same-term rules reach the clause's `F_Σ R` from
`κ`'s cancel branch `cancelTy Σ F`. -/
theorem cancelCT_jr {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R A B : VTy} {F : CTy}
    {ob : Option Lifetime.Life} (hB : B.isZero = false)
    (h : CDerives Δ Γ (.val cancelCT) (.val (clauseTyO S R ob (.unr, A, B) F))) :
    JR (.comp (cancelTy S F)) (.comp (CTy.effOf S R)) := by
  rw [clauseTyO_cap S R ob F hB] at h
  obtain ⟨-, hb⟩ := lam_bang h (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨Γ₁, Γ₂, A', B', C, hs, hV, hB₂, hr⟩ := der_letpair hb _ _ rfl
  have hslotP : (⟨.tensor A (kBoxO ob (kTy S R .unr B F)), true⟩ :: Γ : Ctx VTy)[0]? =
      some ⟨.tensor A (kBoxO ob (kTy S R .unr B F)), true⟩ := rfl
  rcases varCls_of_le hslotP (splitP_le_left hs) hV with hc | ⟨_, hT, -, -⟩
  swap
  · cases hT
  obtain ⟨rfl, rfl⟩ := vview_tensor hc
  have hslotK : (⟨kBoxO ob (kTy S R .unr B F), true⟩ :: ⟨A, true⟩ :: Γ₂ : Ctx VTy)[0]? =
      some ⟨kBoxO ob (kTy S R .unr B F), true⟩ := rfl
  obtain ⟨j₁, hb₁, hr₁⟩ := der_app hB₂ _ _ rfl
  have hk : VView (.bang (.thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy S F))))
      (kBoxO ob (kTy S R .unr B F)) := by
    cases ob with
    | none => exact .refl
    | some d => exact .single (VS.boxI d _)
  refine Relation.ReflTransGen.trans (Relation.ReflTransGen.trans ?_ hr₁) hr
  rcases hb₁ with ⟨Γ₃, Γ₄, A₀, B₀, hs', hY, hX, rfl⟩ | ⟨Γ₃, Γ₄, i, A₀, C₀, hi, hs', hX, hx, rfl⟩ |
    ⟨N', Γ₃, Γ₄, A₀, S₀, C₀, hXe, hs', hM, hN, rfl⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ |
    ⟨_, _, _, _, he, -⟩ | ⟨_, _, he, -⟩ | ⟨_, _, he, -⟩ | ⟨he, -⟩ | he | he | ⟨_, he⟩ | ⟨_, he⟩
  · -- `⊸E`: the λ at a `⊸`, its body at `F B₀`
    rcases varCls_of_le hslotK (splitP_le_left hs') hY with hc | ⟨_, hT, -, -⟩
    swap
    · rcases ob with _ | d <;> cases hT
    have hA₀ : A₀ ≠ .unit := by rintro rfl; exact vview_bang_thunk_unit (hk.trans hc)
    have hN := lam_arr hX (.inr rfl) hA₀ (by not_withPair) (by not_const)
    exact (kappa_cancel_jr (hk.trans hc) rfl hN).tail (JS.ofRet _)
  · -- `[app]`: the argument at its slot's type
    cases hi
    have hA₀ := splitP_le_right hs' 0 A₀ (soloP_le hx)
    rw [hslotK] at hA₀
    cases hA₀
    have hN := lam_arr hX (.inl rfl) (fun h => by rcases ob with _ | d <;> cases h) (by not_withPair) (by not_const)
    exact kappa_cancel_jr hk rfl hN
  · -- `[let]`: the argument returned, its type a view of `κ`'s
    cases hXe
    rcases varCls_of_le hslotK (splitP_le_left hs') hM with ⟨S₁, Y₁, he, hc⟩ | ⟨_, hT, -, -⟩
    swap
    · rcases ob with _ | d <;> cases hT
    obtain ⟨-, rfl⟩ := effOf_inj he
    exact kappa_cancel_jr (hk.trans hc) rfl hN
  all_goals cases he

/-- A cancel row below another finds, at a key the lower one finds, an operation of the upper one,
unless the upper one is `⊤`. -/
theorem finLe_find {F F' : CTy} (h : FinLe F F') {n i : UInt32} {o : OpSig}
    (hf : Row.find F.rowOf n i = some o) :
    F'.isTop = true ∨ ∃ o', Row.find F'.rowOf n i = some o' := by
  rcases (finLe_iff F F').mp h with h | ⟨-, hle⟩
  · exact .inl h
  · obtain ⟨o', hf', -⟩ := hle n i o hf
    exact .inr ⟨o', hf'⟩

/-- `⊤` is below `⊤` alone. -/
theorem finLe_top_top {F F' : CTy} (h : FinLe F F') (hF : F.isTop = true) : F'.isTop = true := by
  rcases (finLe_iff F F').mp h with h | ⟨h, -⟩
  · exact h
  · rw [hF] at h; cases h

/-- **`progT` has no derivation at a row without `2`** (decision D3).  `[handle] 1`'s body holds
`hnd 2 (perform 1 then x. x unwind raise 2)`: the `[then]`'s premise puts `2` in the cancel row of
`1`, `fs 0`, which `[sub]` up to the body keeps; the clause applies `κ`'s cancel branch, at
`F_{fs 0 ⊕ Σ} 1`, and the same-term rules read it at the clause's row `Σ`, so `Σ` holds `2`, and so
does every row the program is read at.  `[spec §27]` -/
theorem not_der_progT {Δ : LifeCtx} {Γ : Ctx VTy} {S' : Row} {Y : VTy}
    (hS' : ∀ o ∈ S', o.n ≠ 2) : ¬ CDerives Δ Γ progT (.comp (CTy.effOf S' Y)) := by
  intro h
  -- `[handle] 1`
  obtain ⟨j₁, ⟨Γ₁, Γ₂, S, E, fs, A, R, _, -, hQ, hH, hM, -, rfl⟩, hr₁⟩ :=
    der_hndJ₁ (n := 1) (Q := (qualsVal [.unr]).1)
      (H := (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit))))
      (M := ((K 2).plug (performU 1))) h (by not_tail [cancelCT, constC])
  have hSS' : RowLe S S' := JR.rowLe hr₁
  have hE : [Qual.unr] = E.map Prod.fst := qualsVal_inj hQ
  obtain ⟨⟨q₁, A₁, B₁⟩, rfl⟩ : ∃ e, E = [e] := by
    rcases E with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE
    · exact ⟨e, rfl⟩
    · simp at hE
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE
  subst hE
  -- `[handle] 2`, then the `[then]`
  obtain ⟨j₂, ⟨Γ₃, Γ₄, S₂, E₂, fs₂, A₂, R₂, _, -, -, -, hM₂, -, rfl⟩, hr₂⟩ :=
    der_hndJ₁ (n := 2) (Q := (qualsVal [.unr]).1)
      (H := (.pair (.val idV) (.pair (.val (constC Val.unit)) (.val Val.unit))))
      (M := ((uF (raiseU 2) .hole).plug (performU 1))) hM (by not_tail [cancelCT, constC])
  have hS₂ : RowLe S₂ (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs ++ S) := JR.rowLe hr₂
  obtain ⟨j₃, ⟨Γ₅, Γ₆, A₃, B₃, S₃, SM, SD, -, hMS, -, hfin, hMp, hDr, rfl⟩, hr₃⟩ :=
    der_thenJ hM₂ (.var 0) (raiseU 2) (performU 1) rfl
  have hS₃ : RowLe S₃ (Row.ofEff 2 E₂ 0 fs₂ ++ S₂) := JR.rowLe hr₃
  -- `perform 1`'s row finds `1`, the finaliser's row finds `2`
  obtain ⟨j₄, ⟨S₄, oM₀, hf₄, ha₄, rfl⟩, hr₄⟩ := der_performJ hMp 1 0 (.val Val.unit) rfl
  obtain ⟨oM, hfM, hleM⟩ := JR.rowLe hr₄ 1 0 oM₀ hf₄
  obtain ⟨j₅, ⟨S₅, oD₀, B₅, hf₅, -, rfl⟩, hr₅⟩ := der_raiseJ hDr 2 0 (.val Val.unit) rfl
  obtain ⟨oD, hfD, -⟩ := JR.rowLe hr₅ 2 0 oD₀ hf₅
  -- `1` from the `[then]` up to `[handle] 1`'s body
  obtain ⟨o₃, hf₃, hle₃⟩ := hMS 1 0 oM hfM
  obtain ⟨o₄, hf₄', hle₄⟩ := hS₃ 1 0 o₃ hf₃
  rw [Row.find_append, Row.find_ofEff_ne 2 E₂ 0 fs₂ 1 0 (by decide), Option.none_or] at hf₄'
  obtain ⟨o₅, hf₅', hle₅⟩ := hS₂ 1 0 o₄ hf₄'
  rw [Row.find_append, show Row.find (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs) 1 0 =
    some ⟨1, 0, .unr, A₁, B₁, fs 0, false⟩ from rfl, Option.some_or] at hf₅'
  cases hf₅'
  have hsig : oM₀.Sig ⟨1, 0, .unr, A₁, B₁, fs 0, false⟩ :=
    hleM.1.trans (hle₃.1.trans (hle₄.1.trans hle₅.1))
  have hB₁ : B₁.isZero = false := by
    have := hsig.abort_eq
    rw [ha₄] at this
    simpa [OpSig.abort] using this.symm
  have hcap₀ : capB oM₀.q oM₀.B = true := by
    rw [hsig.capB_eq]; simp [capB, hB₁]
  have hcapM : capB oM.q oM.B = true := hleM.1.capB_eq ▸ hcap₀
  have hcap₃ : capB o₃.q o₃.B = true := hle₃.1.capB_eq ▸ hcapM
  have hcap₄ : capB o₄.q o₄.B = true := hle₄.1.capB_eq ▸ hcap₃
  -- `2` in the cancel row of `1`, or the cancel row `⊤`
  have h₃₄ : FinLe o₃.fin o₄.fin := hle₄.2 hcap₃
  have h₄₅ : FinLe o₄.fin (fs 0) := hle₅.2 hcap₄
  have hfs : (fs 0).isTop = true ∨ ∃ o₆, Row.find (fs 0).rowOf 2 0 = some o₆ := by
    have hT := hfin 1 0 oM o₃ hfM hf₃ hcapM
    rw [ThenLe] at hT
    rcases hT with hT | ⟨-, -, hT⟩
    · exact .inl (finLe_top_top h₄₅ (finLe_top_top h₃₄ hT))
    · obtain ⟨o', hf', -⟩ := hT 2 0 oD hfD
      rcases finLe_find h₃₄ hf' with h₄ | ⟨o'', hf''⟩
      · exact .inl (finLe_top_top h₄₅ h₄)
      · exact finLe_find h₄₅ hf''
  -- the clause reads `κ`'s cancel at its row
  rcases der_pair hH _ _ rfl with ⟨Γ₇, Γ₈, X₁, X₂, -, -, hcl, hc₁⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨-, rfl⟩ := vview_tensor hc₁
  rcases der_pair hcl _ _ rfl with ⟨Γ₉, Γ₁₀, X₃, X₄, -, hcan, -, hc₂⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  rw [clausesTyO_cons, clausesTyO_nil] at hc₂
  obtain ⟨rfl, -⟩ := vview_tensor hc₂
  have hjr := cancelCT_jr hB₁ hcan
  rcases hfs with htop | ⟨o₆, hf₆⟩
  · rw [show cancelTy S (fs 0) = .top by simp [cancelTy, htop]] at hjr
    have := JR.rigid hjr rigid_top
    simp only [Jdg.comp.injEq] at this
    exact effOf_ne_top S R this
  · have hnt : (fs 0).isTop = false := by
      cases ht : (fs 0).isTop
      · rfl
      · have : (fs 0).rowOf = [] := by
          cases hF : fs 0 <;> simp_all [CTy.isTop, CTy.rowOf]
        rw [this] at hf₆; simp [Row.find] at hf₆
    rw [show cancelTy S (fs 0) = CTy.effOf ((fs 0).rowOf ++ S) .unit by
      simp [cancelTy, hnt]] at hjr
    obtain ⟨o₇, hf₇, -⟩ := JR.rowLe hjr 2 0 o₆ (by rw [Row.find_append, hf₆]; rfl)
    obtain ⟨o₈, hf₈, -⟩ := hSS' 2 0 o₇ hf₇
    obtain ⟨hm₈, hn₈, -⟩ := Row.find_mem hf₈
    exact hS' o₈ hm₈ hn₈

/-- **`progT` has no derivation at `F A`**, the empty row's returner. -/
theorem not_der_progT_ret {Δ : LifeCtx} {Γ : Ctx VTy} {Y : VTy} :
    ¬ CDerives Δ Γ progT (.comp (.ret Y)) :=
  not_der_progT (S' := []) (fun _ h => absurd h List.not_mem_nil)

/-- **A cancelling clause tuple reads `κ`'s cancel at its row**: the handler pair
`(λx. x, (cancelCT, ()))` at `[handle]`'s type, its one operation unrestricted `A ↠ B` with `B` no
`0`. -/
theorem cancelPair_jr {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A R A₁ B₁ : VTy} {fs : Nat → CTy}
    {ob : Option Lifetime.Life} (hB₁ : B₁.isZero = false)
    (hH : CDerives Δ Γ (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
      (.val (.tensor (retTy S A R) (clausesTyO S R ob [(.unr, A₁, B₁)] fs)))) :
    JR (.comp (cancelTy S (fs 0))) (.comp (CTy.effOf S R)) := by
  rcases der_pair hH _ _ rfl with ⟨Γ₇, Γ₈, X₁, X₂, -, -, hcl, hc₁⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨-, rfl⟩ := vview_tensor hc₁
  rcases der_pair hcl _ _ rfl with ⟨Γ₉, Γ₁₀, X₃, X₄, -, hcan, -, hc₂⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  rw [clausesTyO_cons, clausesTyO_nil] at hc₂
  obtain ⟨rfl, -⟩ := vview_tensor hc₂
  exact cancelCT_jr hB₁ hcan

end Rejections

/-! ### A finaliser that performs -/

/-- `hnd (4, H₄ₒ) (hnd (1, H₁T) (hnd (4, H₄ᵢ) ((perform 1) then x. x unwind perform 4)))`, with
`H₄ᵢ`'s clause answering `()` without resuming, and `H₄ₒ`'s answer clause `hr` and clause `c`. -/
def progFinT (hr c : Val) : Expr :=
  hndE (hU 4 hr c) (hndE H₁T (hndE (hU 4 idV (constC Val.unit))
    (thenU (performU 1) (performU 4))))

/-- The finaliser performs `4` under the running cancel, and the live outer `4` resumes it. -/
def progFinOpT : Expr := progFinT injlV resumeCT

/-- The live outer `4` cancels the finaliser's continuation. -/
def progNC₁T : Expr := progFinT idV cancelCT

/-- `progFinT`'s cancel reaches the finaliser's `perform 4`: the dead inner `4` is removed. -/
theorem progFinT_cancel (μ : Heap) (hr c : Val) :
    Steps (ℍ := ℍ) μ (progFinT hr c) μ
      (hndE (hU 4 hr c) ((ccF (cfF (cancelVal none) .hole)).plug (performU 4))) := by
  refine (Steps.plug (hF (hU 4 hr c) .hole) (cancelT_start μ 1 idV
    (hF (hU 4 idV (constC Val.unit)) (uF (performU 4) .hole)) rfl)).trans ?_
  show Steps μ ((hF (hU 4 hr c) (ccF .hole)).plug
    (ubindE (Val.pair idV (finV (performU 4))) (raiseE (.val (cancelVal none))))) μ _
  exact Steps.plug (hF (hU 4 hr c) (ccF .hole)) (fin_cancel μ (performU 4) none)

/-- **`progFinOpT`**: the finaliser's operation passes the dead inner `4` and the cancel's
delimiter, the live outer `4` resumes it, the finaliser returns, and the cancel answers `()`. -/
theorem progFinOpT_run (μ : Heap) : Steps (ℍ := ℍ) μ progFinOpT μ (.val (Val.inj₁ Val.unit)) := by
  refine (progFinT_cancel μ injlV resumeCT).trans ?_
  refine (resumeT_start μ 4 injlV (ccF (cfF (cancelVal none) .hole)) rfl).trans ?_
  refine .more (st (hF (hU 4 injlV resumeCT) (ccF .hole)) (Head.cfret μ none Val.unit)) ?_
  refine .more (st (hF (hU 4 injlV resumeCT) .hole) (Head.cancel μ .hole rfl)) ?_
  refine .more (st .hole (Head.hret μ 4 (qualsVal [.unr]) injlV (Val.pair resumeCT Val.unit)
    Val.unit)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- **`progNC₁T`**: the outer `4` cancels the finaliser's continuation, which passes the running
finaliser's `cfin` (`[cfin-cancel]`), keeps no error, and answers `()` at its own delimiter. -/
theorem progNC₁T_run (μ : Heap) : Steps (ℍ := ℍ) μ progNC₁T μ (.val Val.unit) := by
  refine (progFinT_cancel μ idV cancelCT).trans ?_
  refine (cancelT_start μ 4 idV (ccF (cfF (cancelVal none) .hole)) rfl).trans ?_
  show Steps μ ((ccF (cfF (cancelVal none) .hole)).plug (raiseE (.val (cancelVal none)))) μ _
  refine .more (st (ccF .hole) (Head.cfcancel μ none none .hole rfl)) ?_
  refine .more (st .hole (Head.cancel μ .hole rfl)) ?_
  exact .refl _ _

/-- The cancel row of one operation `4`, at its own empty cancel row. -/
abbrev finP (m : UInt32) : CTy := CTy.effOf [pSig m (.ret .unit)] .unit

/-- A capturable operation's clause `λ_. v`, at `!U(1 ⊗ K ⊸ F_Σ R)`: its argument and `κ` drop. -/
theorem d_constC_op {Δ : LifeCtx} (S : Row) {R : VTy} {F : CTy} {v : Val}
    (hv : CDerives Δ [⟨.tensor .unit (kTy S R .unr .unit F), true⟩] (.val v) (.val R)) :
    CDerives Δ [] (.val (constC v)) (.val (clauseTy S R (.unr, .unit, .unit) F)) := by
  show CDerives Δ [] (.val (constC v))
    (.val (.bang (.thunk (.arr (.tensor .unit (kTy S R .unr .unit F)) (CTy.effOf S R)))))
  exact .bangThunkV (dead_noLive .nil) rfl (.lam (.effSub (RowLe.nil S) (.ret hv)))

/-- **The `[then]` of `progFinT`**: `perform 1 then x. x unwind perform 4` at `{4, 1⟨{4}⟩}`.  The
finaliser's operation `4` is in the cancel row of `1`, its own cancel row with no error pending. -/
theorem d_thenP {Δ : LifeCtx} :
    CDerives Δ [] (thenU (performU 1) (performU 4))
      (.comp (CTy.effOf [pSig 4 (.ret .unit), pSig 1 (finP 4)] .unit)) := by
  show CDerives Δ [] (thenE (.var 0) (performU 4) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [pSig 4 (.ret .unit)]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finP 4), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨pSig 4 (.ret .unit), rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finP 4) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    refine ⟨pSig 4 (.ret .unit), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    rw [PendLe]
    exact Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h,
      fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit)) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effPerform (o := pSig 4 (.ret .unit)) rfl rfl (.unitI (.cons .nil))

/-- `hnd (4, H₄ᵢ) [·]` around `progFinT`'s `[then]`, at the outer row `{1⟨{4}⟩}`. -/
theorem d_innerP {Δ : LifeCtx} :
    CDerives Δ [] (hndE (hU 4 idV (constC Val.unit)) (thenU (performU 1) (performU 4)))
      (.comp (CTy.effOf [pSig 1 (finP 4)] .unit)) := by
  show CDerives Δ [] (hndExpr 4 [.unr] (.pair (.val idV) (.pair (.val (constC Val.unit))
    (.val Val.unit))) (thenU (performU 1) (performU 4))) _
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)])
    (fs := fun _ => .ret .unit) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_constC_op _ (.unitI (.drop rfl .nil)))
      (.unitI .nil)))
    (by decide) (by simp [pSig]) (by simp) rfl d_thenP

/-- `hnd (1, H₁T) …` in `progFinT`, at the outer row `{4}`: `H₁`'s clause reads `κ`'s cancel at
`F_{{4} ⊕ {4}} 1` at `{4}`. -/
theorem d_midP {Δ : LifeCtx} :
    CDerives Δ [] (hndE H₁T (hndE (hU 4 idV (constC Val.unit)) (thenU (performU 1) (performU 4))))
      (.comp (CTy.effOf [pSig 4 (.ret .unit)] .unit)) := by
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    (hndE (hU 4 idV (constC Val.unit)) (thenU (performU 1) (performU 4)))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finP 4)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [pSig]) (by simp) rfl ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [show (finP 4).rowOf ++ [pSig 4 (.ret .unit)] = [pSig 4 (.ret .unit), pSig 4 (.ret .unit)]
      from rfl] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
    subst ho
    exact ⟨pSig 4 (.ret .unit), rfl, OpSig.LeF.refl _⟩
  · refine .effSub (RowLe.of_mem fun o ho => ?_) d_innerP
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨pSig 1 (finP 4), rfl, OpSig.LeF.refl _⟩

/-- **`progFinOpT` is typed at `F (1 ⊕ 1)`**: the finaliser performs `4`, whose live instance at
the cancel is the outer handler, which resumes it. -/
theorem d_progFinOpT {Δ : LifeCtx} : CDerives Δ [] progFinOpT (.comp (.ret (.sum .unit .unit))) := by
  show CDerives Δ [] (hndExpr 4 [.unr] (.pair (.val injlV) (.pair (.val resumeCT) (.val Val.unit)))
    (hndE H₁T (hndE (hU 4 idV (constC Val.unit)) (thenU (performU 1) (performU 4)))))
    (.comp (CTy.effOf [] (.sum .unit .unit)))
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)])
    (fs := fun _ => .ret .unit) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_injlV _ .unit .unit) (.tensorI .nil (d_resumeCT _ _ _) (.unitI .nil)))
    (by decide) (by simp) (by simp) rfl d_midP

/-- **`progNC₁T` is typed at `F 1`**: the outer `4` cancels the finaliser's continuation, whose
cancel row is empty. -/
theorem d_progNC₁T {Δ : LifeCtx} : CDerives Δ [] progNC₁T (.comp (.ret .unit)) := by
  show CDerives Δ [] (hndExpr 4 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    (hndE H₁T (hndE (hU 4 idV (constC Val.unit)) (thenU (performU 1) (performU 4)))))
    (.comp (CTy.effOf [] .unit))
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)])
    (fs := fun _ => .ret .unit) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit)
      (.tensorI .nil (d_cancelCT rfl (by simp [RowLe.refl, CTy.rowOf])) (.unitI .nil)))
    (by decide) (by simp) (by simp) rfl d_midP

/-! ### A kept error pending at a finaliser that performs -/

/-- `hnd (2, H₂ₒ) (hnd (4, H₄ₒ) (hnd (1, H₁T) (((perform 1) then x. x unwind raise 2) then y. y
unwind perform 4)))`, with `H₂ₒ`'s clause answering `inj₂ ()`, and `H₄ₒ`'s answer clause `λx. inj₁ x`
and clause `c`. -/
def progKDT (c : Val) : Expr :=
  hndE (hU 2 idV (constC (Val.inj₂ Val.unit))) (hndE (hU 4 injlV c)
    (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4))))

/-- `H₄ₒ`'s clause answers `inj₁ ()` and drops its continuation. -/
def progDropT : Expr := progKDT (constC (Val.inj₁ Val.unit))

/-- `H₄ₒ`'s clause resumes its continuation. -/
def progKeepT : Expr := progKDT resumeCT

/-- `progKDT`'s cancel: the inner finaliser's raise of `2` is kept, and the outer finaliser performs
`4` with the kept error in its `cfin`. -/
theorem progKDT_cancel (μ : Heap) (c : Val) :
    Steps (ℍ := ℍ) μ (progKDT c) μ
      ((hF (hU 2 idV (constC (Val.inj₂ Val.unit))) (hF (hU 4 injlV c) .hole)).plug
        ((ccF (cfF (cancelVal (some (opPayload 2 0 Val.unit))) .hole)).plug (performU 4))) := by
  let Ko : Kont := hF (hU 2 idV (constC (Val.inj₂ Val.unit))) (hF (hU 4 injlV c) .hole)
  refine (Steps.plug Ko (cancelT_start μ 1 idV (uF (performU 4) (uF (raiseU 2) .hole))
    rfl)).trans ?_
  show Steps μ ((Ko.comp (ccF (uF (performU 4) .hole))).plug
    (ubindE (Val.pair idV (finV (raiseU 2))) (raiseE (.val (cancelVal none))))) μ _
  refine (Steps.plug (Ko.comp (ccF (uF (performU 4) .hole))) (fin_cancel μ (raiseU 2) none)).trans ?_
  refine .more (st (Ko.comp (ccF (uF (performU 4) .hole)))
    (Head.cferr μ none 2 0 Val.unit .hole (by decide) rfl)) ?_
  show Steps μ ((Ko.comp (ccF .hole)).plug (ubindE (Val.pair idV (finV (performU 4)))
    (raiseE (.val (cancelVal (some (opPayload 2 0 Val.unit))))))) μ _
  exact Steps.plug (Ko.comp (ccF .hole)) (fin_cancel μ (performU 4) _)

/-- **`progDropT`**: `H₄ₒ`'s unrestricted clause drops the continuation that holds the kept error
`2`, so `H₂ₒ`'s clause never runs. -/
theorem progDropT_run (μ : Heap) : Steps (ℍ := ℍ) μ progDropT μ (.val (Val.inj₁ Val.unit)) := by
  refine (progKDT_cancel μ _).trans ?_
  refine (Steps.plug (hF (hU 2 idV (constC (Val.inj₂ Val.unit))) .hole) (const_start μ 4 injlV
    (Val.inj₁ Val.unit) (fun _ => rfl) (ccF (cfF (cancelVal (some (opPayload 2 0 Val.unit))) .hole))
    rfl)).trans ?_
  refine .more (st .hole (Head.hret μ 2 (qualsVal [.unr]) idV
    (Val.pair (constC (Val.inj₂ Val.unit)) Val.unit) (Val.inj₁ Val.unit))) ?_
  refine .more (st .hole (Head.beta μ _ (Val.inj₁ Val.unit))) ?_
  exact .refl _ _

/-- **`progKeepT`**: `H₄ₒ` resumes the finaliser; the finaliser returns, the cancel re-raises the
kept error `2` at the canceller, and the live `H₂ₒ` catches it. -/
theorem progKeepT_run (μ : Heap) : Steps (ℍ := ℍ) μ progKeepT μ (.val (Val.inj₂ Val.unit)) := by
  refine (progKDT_cancel μ _).trans ?_
  refine (Steps.plug (hF (hU 2 idV (constC (Val.inj₂ Val.unit))) .hole) (resumeT_start μ 4 injlV
    (ccF (cfF (cancelVal (some (opPayload 2 0 Val.unit))) .hole)) rfl)).trans ?_
  refine .more (st (hF (hU 2 idV (constC (Val.inj₂ Val.unit)))
    (hF (hU 4 injlV resumeCT) (ccF .hole))) (Head.cfret μ _ Val.unit)) ?_
  refine .more (st (hF (hU 2 idV (constC (Val.inj₂ Val.unit))) (hF (hU 4 injlV resumeCT) .hole))
    (Head.creraise μ (opPayload 2 0 Val.unit) .hole rfl)) ?_
  refine .more (st .hole (Head.hunwind μ 2 0 (qualsVal [.unr]) idV
    (Val.pair (constC (Val.inj₂ Val.unit)) Val.unit) (constC (Val.inj₂ Val.unit)) Val.unit
    (hF (hU 4 injlV resumeCT) .hole) (hcl _) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- The cancel row `{2, 4⟨{2}⟩}`: the raise of `2`, and the operation `4` with `2` pending in its own
cancel row. -/
abbrev finKD : CTy := CTy.effOf [rSig 2, pSig 4 (finR 2)] .unit

/-- **The inner `[then]` of `progKDT`**: `perform 1 then x. x unwind raise 2` at `{1⟨{2}⟩, 2}`. -/
theorem d_thenK₁ {Δ : LifeCtx} :
    CDerives Δ [] (thenU (performU 1) (raiseU 2))
      (.comp (CTy.effOf [pSig 1 (finR 2), rSig 2] .unit)) := by
  show CDerives Δ [] (thenE (.var 0) (raiseU 2) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 2]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finR 2) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit)) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSig 2) rfl rfl .unit (.unitI (.cons .nil))

/-- **The outer `[then]` of `progKDT`**: its finaliser performs `4` below the inner one's kept `2`,
so the cancel row of `1` holds `4` with `2` pending: `{2, 4⟨{2}⟩}` (`pend`). -/
theorem d_thenK₂ {Δ : LifeCtx} :
    CDerives Δ [] (thenU (thenU (performU 1) (raiseU 2)) (performU 4))
      (.comp (CTy.effOf [pSig 1 finKD, rSig 2, pSig 4 (finR 2)] .unit)) := by
  show CDerives Δ [] (thenE (.var 0) (performU 4) (thenU (performU 1) (raiseU 2))) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (finR 2), rSig 2])
    (SD := [pSig 4 (.ret .unit)]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl d_thenK₁ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · refine ⟨pSig 1 finKD, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
      refine (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.of_mem fun o ho => ?_⟩)
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at ho
      subst ho
      exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
    · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 4 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · intro n i o o' hf hf' hc
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    swap
    · simp [capB, rSig, VTy.isZero] at hc
    obtain rfl : o' = pSig 1 finKD := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => ?_, fun n i o h => ?_⟩
    · obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at hm
      subst hm
      exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
    · obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      simp only [List.mem_singleton] at hm
      subst hm
      refine ⟨pSig 4 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
      rw [PendLe]
      refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h,
        fun n i o h ha => ?_⟩
      obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at hm
      subst hm
      exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro _ o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · refine ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => ?_⟩
      exact ⟨fun _ => rfl, fun h => absurd h (by decide), trivial⟩
    · exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effPerform (o := pSig 4 (.ret .unit)) rfl rfl (.unitI (.cons .nil))

/-- `hnd (1, H₁T) …` in `progKDT`, at the outer row `{2, 4⟨{2}⟩}`: `H₁`'s clause reads `κ`'s cancel
at `F_{{2, 4⟨{2}⟩} ⊕ Σ} 1` at `Σ = {2, 4⟨{2}⟩}`. -/
theorem d_midK {Δ : LifeCtx} :
    CDerives Δ [] (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4)))
      (.comp (CTy.effOf [rSig 2, pSig 4 (finR 2)] .unit)) := by
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    (thenU (thenU (performU 1) (raiseU 2)) (performU 4))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finKD)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig, pSig]) (by simp) rfl d_thenK₂
  refine RowLe.of_mem fun o ho => ?_
  rw [show finKD.rowOf ++ [rSig 2, pSig 4 (finR 2)] =
    [rSig 2, pSig 4 (finR 2), rSig 2, pSig 4 (finR 2)] from rfl] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · exact ⟨pSig 4 (finR 2), rfl, OpSig.LeF.refl _⟩
  · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · exact ⟨pSig 4 (finR 2), rfl, OpSig.LeF.refl _⟩

/-- `progKDT c` at `F (1 ⊕ 1)`, for a clause `c` of `H₄ₒ` at the cancel row `{2}`. -/
theorem d_progKDT {Δ : LifeCtx} {c : Val}
    (hc : CDerives Δ [] (.val c)
      (.val (clauseTy [rSig 2] (.sum .unit .unit) (.unr, .unit, .unit) (finR 2)))) :
    CDerives Δ [] (progKDT c) (.comp (.ret (.sum .unit .unit))) := by
  show CDerives Δ [] (hndExpr 2 [.unr] (.pair (.val idV)
    (.pair (.val (constC (Val.inj₂ Val.unit))) (.val Val.unit)))
    (hndE (hU 4 injlV c) (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4)))))
    (.comp (CTy.effOf [] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ _)
      (.tensorI .nil (d_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil)))
    (by decide) (by simp) (by simp) rfl ?_
  show CDerives Δ [] (hndExpr 4 [.unr] (.pair (.val injlV) (.pair (.val c) (.val Val.unit)))
    (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4))))
    (.comp (CTy.effOf [rSig 2] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 2)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_injlV _ .unit .unit) (.tensorI .nil hc (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) rfl ?_
  refine .effSub (RowLe.of_mem fun o ho => ?_) d_midK
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · exact ⟨pSig 4 (finR 2), rfl, OpSig.LeF.refl _⟩

/-- **`progDropT` is typed at `F (1 ⊕ 1)`**: a finaliser may perform an operation whose
unrestricted clause discards its continuation (§27's *Open*: the kept error goes with it). -/
theorem d_progDropT {Δ : LifeCtx} : CDerives Δ [] progDropT (.comp (.ret (.sum .unit .unit))) :=
  d_progKDT (d_constC_op _ (.sumI₁ (.unitI (.drop rfl .nil))))

/-- **`progKeepT` is typed at `F (1 ⊕ 1)`**. -/
theorem d_progKeepT {Δ : LifeCtx} : CDerives Δ [] progKeepT (.comp (.ret (.sum .unit .unit))) :=
  d_progKDT (d_resumeCT _ _ _)

/-! ### The kept error caught outside the region -/

/-- `hnd (3, H₃) (bodyT 3)`, `H₃`'s answer clause `λx. inj₁ x` and its clause answering `inj₂ ()`:
the finaliser raises `3`, a name handled outside the region (the kernel shape `cancel-reraised`). -/
def cancelKeptT : Expr := hndE (hU 3 injlV c₃) (bodyT 3)

/-- **`cancelKeptT`**: the error of name `3` is kept, re-raised at the canceller, and caught by
`H₃`, outside the region. -/
theorem cancelKeptT_run (μ : Heap) : Steps (ℍ := ℍ) μ cancelKeptT μ (.val (Val.inj₂ Val.unit)) := by
  refine (Steps.plug (hF (hU 3 injlV c₃) .hole) (bodyT_run 3 (by decide) μ)).trans ?_
  refine .more (st .hole (Head.hunwind μ 3 0 (qualsVal [.unr]) injlV (Val.pair c₃ Val.unit) c₃
    Val.unit .hole (hcl c₃) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- **The `[then]` of `cancelKeptT`**: `perform 1 then x. x unwind raise 3` at `{2, 1⟨{3}⟩, 3}`. -/
theorem d_then₃ {Δ : LifeCtx} :
    CDerives Δ [] ((uF (raiseU 3) .hole).plug (performU 1))
      (.comp (CTy.effOf [rSig 2, pSig 1 (finR 3), rSig 3] .unit)) := by
  show CDerives Δ [] (thenE (.var 0) (raiseU 3) (performU 1)) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 3]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 3), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSig 3, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finR 3) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSig 3, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effPerform (o := pSig 1 (.ret .unit)) rfl rfl (.unitI .nil)
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSig 3) rfl rfl .unit (.unitI (.cons .nil))

/-- **`cancelKeptT` is typed at `F (1 ⊕ 1)`**: the cancel row of `1` is `{3}`, which `H₁`'s row
holds, and `H₃` handles it outside. -/
theorem d_cancelKeptT {Δ : LifeCtx} : CDerives Δ [] cancelKeptT (.comp (.ret (.sum .unit .unit))) := by
  show CDerives Δ [] (hndExpr 3 [.unr] (.pair (.val injlV) (.pair (.val c₃) (.val Val.unit)))
    (bodyT 3)) (.comp (CTy.effOf [] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_injlV _ .unit .unit)
      (.tensorI .nil (d_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil)))
    (by decide) (by simp) (by simp) rfl ?_
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    ((K 3).plug (performU 1))) (.comp (CTy.effOf [rSig 3] .unit))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 3)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) rfl ?_
  · refine RowLe.of_mem fun o ho => ?_
    rw [show (finR 3).rowOf ++ [rSig 3] = [rSig 3, rSig 3] from rfl] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
    subst ho
    exact ⟨rSig 3, rfl, OpSig.LeF.refl _⟩
  · show CDerives Δ [] (hndExpr 2 [.unr] (.pair (.val idV) (.pair (.val (constC Val.unit))
      (.val Val.unit))) ((uF (raiseU 3) .hole).plug (performU 1)))
      (.comp (CTy.effOf [pSig 1 (finR 3), rSig 3] .unit))
    exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
      .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
      (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_constC_raise _ (.unitI (.cons .nil)))
        (.unitI .nil)))
      (by decide) (by simp [rSig, pSig]) (by simp) rfl d_then₃

/-! ### A region that re-enters the site of a name -/

/-- `P_re`: `hnd (3, H₃ₒ) (hnd (1, H₁T) ((f ()) then x. x unwind raise 3))`, `f` re-entering the
site `3` (`fRe`). -/
def progReT : Expr :=
  hndE (hU 3 injlV c₃) (hndE H₁T (thenU (.app (.val fRe) (.val Val.unit)) (raiseU 3)))

/-- **`progReT`**: the region re-enters the site `3`; its instance there is dead, so the
finaliser's raise of `3` is kept, re-raised at the canceller, and caught by the live outer
instance. -/
theorem progReT_run (μ : Heap) : Steps (ℍ := ℍ) μ progReT μ (.val (Val.inj₂ Val.unit)) := by
  refine .more (st (hF (hU 3 injlV c₃) (hF H₁T (uF (raiseU 3) .hole)))
    (Head.beta μ _ Val.unit)) ?_
  show Steps μ ((hF (hU 3 injlV c₃) .hole).plug
    (hndE H₁T ((uF (raiseU 3) (hF H₃ᵢ .hole)).plug (performU 1)))) μ _
  refine (Steps.plug (hF (hU 3 injlV c₃) .hole)
    (cancelT_start μ 1 idV (uF (raiseU 3) (hF H₃ᵢ .hole)) rfl)).trans ?_
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

/-- `f ()` at `{1}`: `f`'s handler of `3` is at the row `{1}`, which lacks `3`. -/
theorem d_fRe {Δ : LifeCtx} :
    CDerives Δ [] (.app (.val fRe) (.val Val.unit)) (.comp (CTy.effOf [pSig 1 (.ret .unit)] .unit)) := by
  refine .bind (Γ₁ := []) (Γ₂ := []) .nil (.ret (.unitI .nil)) ?_
  show CDerives Δ [⟨.unit, true⟩] (hndExpr 3 [.unr] (.pair (.val idV)
    (.pair (.val (constC Val.unit)) (.val Val.unit))) (performU 1)) _
  exact .effHandleV (Γ₁ := [⟨.unit, false⟩]) (Γ₂ := [⟨.unit, true⟩]) (E := [(.unr, .unit, .zero)])
    (fs := finsNil) (.right .nil) (.cons .nil) (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI (.dead .nil) (d_idVΓ (.cons .nil) _ .unit)
      (.tensorI (.dead .nil) (d_constC_raiseΓ (.cons .nil) _ (.unitI (.cons (.cons .nil))))
        (.unitI (.cons .nil))))
    (by decide) (by simp [pSig]) (by simp) rfl
    (.effPerform (o := pSig 1 (.ret .unit)) rfl rfl (.unitI (.drop rfl .nil)))

/-- **The `[then]` of `progReT`**: `f () then x. x unwind raise 3` at `{1⟨{3}⟩, 3}`. -/
theorem d_thenRe {Δ : LifeCtx} :
    CDerives Δ [] (thenU (.app (.val fRe) (.val Val.unit)) (raiseU 3))
      (.comp (CTy.effOf [pSig 1 (finR 3), rSig 3] .unit)) := by
  show CDerives Δ [] (thenE (.var 0) (raiseU 3) (.app (.val fRe) (.val Val.unit))) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 3]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl d_fRe ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 3), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.nil _⟩)
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨rSig 3, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' _
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    obtain rfl : o' = pSig 1 (finR 3) := Option.some.inj (hf'.symm.trans rfl)
    rw [ThenLe]
    refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h, fun n i o h => ?_⟩
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rSig 3, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
  · intro _ o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, pSig, VTy.isZero] at h, fun _ => trivial⟩
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := rSig 3) rfl rfl .unit (.unitI (.cons .nil))

/-- **`progReT` is typed at `F (1 ⊕ 1)`**: `f ()` is at `{1}`, and the `[then]` gives `1` the cancel
row `{3}`, which `H₁`'s row holds. -/
theorem d_progReT {Δ : LifeCtx} : CDerives Δ [] progReT (.comp (.ret (.sum .unit .unit))) := by
  show CDerives Δ [] (hndExpr 3 [.unr] (.pair (.val injlV) (.pair (.val c₃) (.val Val.unit)))
    (hndE H₁T (thenU (.app (.val fRe) (.val Val.unit)) (raiseU 3))))
    (.comp (CTy.effOf [] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_injlV _ .unit .unit)
      (.tensorI .nil (d_constC_raise _ (.sumI₂ (.unitI (.cons .nil)))) (.unitI .nil)))
    (by decide) (by simp) (by simp) rfl ?_
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    (thenU (.app (.val fRe) (.val Val.unit)) (raiseU 3))) (.comp (CTy.effOf [rSig 3] .unit))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 3)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) rfl d_thenRe
  refine RowLe.of_mem fun o ho => ?_
  rw [show (finR 3).rowOf ++ [rSig 3] = [rSig 3, rSig 3] from rfl] at ho
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ho
  subst ho
  exact ⟨rSig 3, rfl, OpSig.LeF.refl _⟩

/-! ### Two finalisers that perform the cancelling operation -/

/-- `hnd (4, H₄ₒ) (hnd (1, H₁T) (hnd (4, H₄ᵢ) (((perform 1) then x. x unwind perform 4) then y. y
unwind perform 4)))`, `H₄ₒ` cancelling its continuation: both finalisers perform `4`, so the cancel
`H₄ₒ` runs reaches the second finaliser, whose `4` has no live instance. -/
def progNCrecT : Expr :=
  hndE (hU 4 idV cancelCT) (hndE H₁T (hndE (hU 4 idV (constC Val.unit))
    (thenU (thenU (performU 1) (performU 4)) (performU 4))))

/-- **`progNCrecT`'s run**: `H₁` cancels; the first finaliser performs `4`, which passes the dead
inner `4` to `H₄ₒ`; `H₄ₒ` cancels that continuation, whose region holds the second finaliser
(a leftover); the nested cancel passes the first finaliser's `cfin` (`[cfin-cancel]`) and fires it,
and it performs `4` outside every handler of `4`. -/
theorem progNCrecT_run (μ : Heap) :
    Steps (ℍ := ℍ) μ progNCrecT μ ((ccF (cfF (cancelVal none) .hole)).plug (performU 4)) := by
  let H₄ₒ : Val := hU 4 idV cancelCT
  refine (Steps.plug (hF H₄ₒ .hole) (cancelT_start μ 1 idV
    (hF (hU 4 idV (constC Val.unit)) (uF (performU 4) (uF (performU 4) .hole))) rfl)).trans ?_
  show Steps μ ((hF H₄ₒ (ccF (uF (performU 4) .hole))).plug
    (ubindE (Val.pair idV (finV (performU 4))) (raiseE (.val (cancelVal none))))) μ _
  refine (Steps.plug (hF H₄ₒ (ccF (uF (performU 4) .hole))) (fin_cancel μ (performU 4) none)).trans ?_
  show Steps μ (hndE H₄ₒ ((ccF (uF (performU 4) (cfF (cancelVal none) .hole))).plug (performU 4))) μ _
  refine (cancelT_start μ 4 idV (ccF (uF (performU 4) (cfF (cancelVal none) .hole))) rfl).trans ?_
  show Steps μ ((ccF (uF (performU 4) (cfF (cancelVal none) .hole))).plug
    (raiseE (.val (cancelVal none)))) μ _
  refine .more (st (ccF (uF (performU 4) .hole)) (Head.cfcancel μ none none .hole rfl)) ?_
  show Steps μ ((ccF .hole).plug
    (ubindE (Val.pair idV (finV (performU 4))) (raiseE (.val (cancelVal none))))) μ _
  exact Steps.plug (ccF .hole) (fin_cancel μ (performU 4) none)

/-- **`progNCrecT`'s run ends at an operation no handler catches**: the configuration
`progNCrecT_run` reaches, `ccatch (cfin ⊥ (perform 4))`, takes no step. -/
theorem progNCrecT_stuck {μ μ' : Heap} {e' : Expr} :
    ¬ Step1 (ℍ := ℍ) μ ((ccF (cfF (cancelVal none) .hole)).plug (performU 4)) μ' e' := by
  show ¬ Step1 μ ((ccF (cfF (cancelVal none) .hole)).plug (opE false (opPayload 4 0 Val.unit)))
    μ' e'
  exact opPlug_no_step (payloadName_opPayload 4 0 Val.unit) (by simp [OpFree, Kont.HasHnd])

section Rejections
open BoCa.Fig16.LogRel.Core.Inversions

/-- `G` is `⊤`, or finds an operation of `m`. -/
def FindsAt (m : UInt32) (G : CTy) : Prop := G.isTop = true ∨ ∃ y, Row.find G.rowOf m 0 = some y

/-- `G` is `⊤`, or finds a capturable operation of `m`. -/
def FindsCap (m : UInt32) (G : CTy) : Prop :=
  G.isTop = true ∨ ∃ x, Row.find G.rowOf m 0 = some x ∧ capB x.q x.B = true

/-- `G` is `⊤`, or finds a capturable operation of `m` whose own cancel row is `⊤` or finds `m`. -/
def FindsRec (m : UInt32) (G : CTy) : Prop :=
  G.isTop = true ∨ ∃ x, Row.find G.rowOf m 0 = some x ∧ capB x.q x.B = true ∧ FindsAt m x.fin

theorem FindsAt.mono {m : UInt32} {G G' : CTy} (h : FinLe G G') (hG : FindsAt m G) :
    FindsAt m G' := by
  rcases hG with hT | ⟨y, hy⟩
  · exact .inl (finLe_top_top h hT)
  · exact finLe_find h hy

theorem FindsCap.mono {m : UInt32} {G G' : CTy} (h : FinLe G G') (hG : FindsCap m G) :
    FindsCap m G' := by
  rcases hG with hT | ⟨x, hx, hc⟩
  · exact .inl (finLe_top_top h hT)
  · rcases (finLe_iff G G').mp h with h | ⟨-, hle⟩
    · exact .inl h
    · obtain ⟨x', hx', hle'⟩ := hle m 0 x hx
      exact .inr ⟨x', hx', hle'.1.capB_eq ▸ hc⟩

theorem FindsRec.mono {m : UInt32} {G G' : CTy} (h : FinLe G G') (hG : FindsRec m G) :
    FindsRec m G' := by
  rcases hG with hT | ⟨x, hx, hc, hx'⟩
  · exact .inl (finLe_top_top h hT)
  · rcases (finLe_iff G G').mp h with h | ⟨-, hle⟩
    · exact .inl h
    · obtain ⟨x', hx₁, hle'⟩ := hle m 0 x hx
      exact .inr ⟨x', hx₁, hle'.1.capB_eq ▸ hc, hx'.mono (hle'.2 hc)⟩

/-- **The finaliser below a cancel row**: a capturable operation of `m` in `E` puts one in
`F ⋈ E`. -/
theorem thenLe_findsCap {m : UInt32} {F T : CTy} {E : Row} (h : ThenLe F E T) {z : OpSig}
    (hz : Row.find E m 0 = some z) (hc : capB z.q z.B = true) : FindsCap m T := by
  rw [ThenLe] at h
  rcases h with h | ⟨-, -, hE⟩
  · exact .inl h
  · obtain ⟨z', hz', hs, -⟩ := hE m 0 z hz
    exact .inr ⟨z', hz', hs.capB_eq ▸ hc⟩

/-- **The leftover clause**: a capturable operation of `m` already in `F`, below a finaliser that
performs one of `m`, gets `m` in its own cancel row in `F ⋈ E`. -/
theorem thenLe_findsRec {m : UInt32} {F T : CTy} {E : Row} (h : ThenLe F E T) (hF : FindsCap m F)
    {z : OpSig} (hz : Row.find E m 0 = some z) : FindsRec m T := by
  rw [ThenLe] at h
  rcases h with h | ⟨hFt, hF', -⟩
  · exact .inl h
  · rcases hF with hT | ⟨x, hx, hc⟩
    · rw [hT] at hFt; cases hFt
    · obtain ⟨x', hx', hs, hle⟩ := hF' m 0 x hx
      refine .inr ⟨x', hx', hs.capB_eq ▸ hc, ?_⟩
      have h₂ := hle hc
      rw [ThenLe] at h₂
      rcases h₂ with h₂ | ⟨-, -, hE⟩
      · exact .inl h₂
      · obtain ⟨y, hy, -⟩ := hE m 0 z hz
        exact .inr ⟨y, hy⟩

/-- **`progNCrecT` has no derivation** (D3, the leftover clause): the first finaliser's `4` is in
the cancel row of `1`, and the second finaliser, which runs in the cancel of that `4`'s
continuation, puts `4` in its cancel row in turn; so `H₁`'s clause row holds a `4` whose cancel row
holds `4`, and so does the clause row of the outer handler of `4`, its own outer row, which lacks
`4`.  `[spec §27]` -/
theorem not_der_progNCrecT {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ progNCrecT j := by
  intro h
  -- the outer `[handle] 4`
  obtain ⟨j₀, ⟨Γa, Γb, S₀, E₀, fs₀, A₀', R₀, _, -, hQ₀, hH₀, hM₀, hnS₀, rfl⟩, -⟩ :=
    der_hndJ₁ (n := 4) (Q := (qualsVal [.unr]).1)
      (H := (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit))))
      (M := (hndE H₁T (hndE (hU 4 idV (constC Val.unit))
        (thenU (thenU (performU 1) (performU 4)) (performU 4))))) h (by not_tail [cancelCT, constC])
  have hE₀ : [Qual.unr] = E₀.map Prod.fst := qualsVal_inj hQ₀
  obtain ⟨⟨q₀, A₀, B₀⟩, rfl⟩ : ∃ e, E₀ = [e] := by
    rcases E₀ with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE₀
    · exact ⟨e, rfl⟩
    · simp at hE₀
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE₀
  subst hE₀
  -- `[handle] 1`
  obtain ⟨j₁, ⟨Γc, Γd, S₁, E₁, fs₁, A₁', R₁, _, -, hQ₁, hH₁, hM₁, -, rfl⟩, hr₁⟩ :=
    der_hndJ₁ (n := 1) (Q := (qualsVal [.unr]).1)
      (H := (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit))))
      (M := (hndE (hU 4 idV (constC Val.unit))
        (thenU (thenU (performU 1) (performU 4)) (performU 4)))) hM₀ (by not_tail [cancelCT, constC])
  have hS₁ : RowLe S₁ (Row.ofEff 4 [(.unr, A₀, B₀)] 0 fs₀ ++ S₀) := JR.rowLe hr₁
  have hE₁ : [Qual.unr] = E₁.map Prod.fst := qualsVal_inj hQ₁
  obtain ⟨⟨q₁, A₁, B₁⟩, rfl⟩ : ∃ e, E₁ = [e] := by
    rcases E₁ with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE₁
    · exact ⟨e, rfl⟩
    · simp at hE₁
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE₁
  subst hE₁
  -- the inner `[handle] 4`, then the two `[then]`s
  obtain ⟨j₂, ⟨Γe, Γf, S₂, E₂, fs₂, A₂, R₂, _, -, hQ₂, -, hM₂, -, rfl⟩, hr₂⟩ :=
    der_hndJ₁ (n := 4) (Q := (qualsVal [.unr]).1)
      (H := (.pair (.val idV) (.pair (.val (constC Val.unit)) (.val Val.unit))))
      (M := (thenU (thenU (performU 1) (performU 4)) (performU 4))) hM₁ (by not_tail [cancelCT, constC])
  have hS₂ : RowLe S₂ (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs₁ ++ S₁) := JR.rowLe hr₂
  have hE₂ : [Qual.unr] = E₂.map Prod.fst := qualsVal_inj hQ₂
  obtain ⟨⟨q₂, A₂', B₂'⟩, rfl⟩ : ∃ e, E₂ = [e] := by
    rcases E₂ with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE₂
    · exact ⟨e, rfl⟩
    · simp at hE₂
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE₂
  subst hE₂
  obtain ⟨j₃, ⟨Γg, Γh, A₃, B₃, S₃, SM₃, SD₃, -, hMS₃, -, hfin₃, hM₃, hD₃, rfl⟩, hr₃⟩ :=
    der_thenJ hM₂ (.var 0) (performU 4) (thenU (performU 1) (performU 4)) rfl
  have hS₃ : RowLe S₃ (Row.ofEff 4 [(.unr, A₂', B₂')] 0 fs₂ ++ S₂) := JR.rowLe hr₃
  obtain ⟨j₄, ⟨Γi, Γj, A₄, B₄, S₄, SM₄, SD₄, -, hMS₄, hDS₄, hfin₄, hM₄, hD₄, rfl⟩, hr₄⟩ :=
    der_thenJ hM₃ (.var 0) (performU 4) (performU 1) rfl
  have hS₄ : RowLe S₄ SM₃ := JR.rowLe hr₄
  -- the operations the three `perform`s find
  obtain ⟨j₅, ⟨S₅, oP₀, hf₅, ha₅, rfl⟩, hr₅⟩ := der_performJ hM₄ 1 0 (.val Val.unit) rfl
  obtain ⟨oP, hfP, hleP⟩ := JR.rowLe hr₅ 1 0 oP₀ hf₅
  obtain ⟨j₆, ⟨S₆, oD₀, hf₆, ha₆, rfl⟩, hr₆⟩ := der_performJ hD₄ 4 0 (.val Val.unit) rfl
  obtain ⟨oD, hfD, hleD⟩ := JR.rowLe hr₆ 4 0 oD₀ hf₆
  obtain ⟨j₇, ⟨S₇, oE₀, hf₇, ha₇, rfl⟩, hr₇⟩ := der_performJ hD₃ 4 0 (.val Val.unit) rfl
  obtain ⟨oE, hfE, -⟩ := JR.rowLe hr₇ 4 0 oE₀ hf₇
  -- `1` from `perform 1` up to `[handle] 1`'s body: unrestricted, its answer no `0`
  obtain ⟨o₄₁, hf₄₁, hle₄₁⟩ := hMS₄ 1 0 oP hfP
  obtain ⟨o₃₁, hf₃₁, hle₃₁⟩ := hS₄ 1 0 o₄₁ hf₄₁
  obtain ⟨o₂₁, hf₂₁, hle₂₁⟩ := hMS₃ 1 0 o₃₁ hf₃₁
  obtain ⟨o₂₁', hf₂₁', hle₂₁'⟩ := hS₃ 1 0 o₂₁ hf₂₁
  rw [Row.find_append, Row.find_ofEff_ne 4 _ 0 fs₂ 1 0 (by decide), Option.none_or] at hf₂₁'
  obtain ⟨o₁, hf₁, hle₁⟩ := hS₂ 1 0 o₂₁' hf₂₁'
  rw [Row.find_append, show Row.find (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs₁) 1 0 =
    some ⟨1, 0, .unr, A₁, B₁, fs₁ 0, false⟩ from rfl, Option.some_or] at hf₁
  cases hf₁
  have hsig₁ : oP₀.Sig ⟨1, 0, .unr, A₁, B₁, fs₁ 0, false⟩ :=
    hleP.1.trans (hle₄₁.1.trans (hle₃₁.1.trans (hle₂₁.1.trans (hle₂₁'.1.trans hle₁.1))))
  have hB₁ : B₁.isZero = false := by
    have := hsig₁.abort_eq
    rw [ha₅] at this
    simpa [OpSig.abort] using this.symm
  have hcap₁ : capB oP₀.q oP₀.B = true := by rw [hsig₁.capB_eq]; simp [capB, hB₁]
  have hcapP : capB oP.q oP.B = true := hleP.1.capB_eq ▸ hcap₁
  have hcap₄₁ : capB o₄₁.q o₄₁.B = true := hle₄₁.1.capB_eq ▸ hcapP
  have hcap₃₁ : capB o₃₁.q o₃₁.B = true := hle₃₁.1.capB_eq ▸ hcap₄₁
  have hcap₂₁ : capB o₂₁.q o₂₁.B = true := hle₂₁.1.capB_eq ▸ hcap₃₁
  have hcap₂₁' : capB o₂₁'.q o₂₁'.B = true := hle₂₁'.1.capB_eq ▸ hcap₂₁
  -- the first finaliser's `4`, up to the inner `[handle] 4`: unrestricted, its answer no `0`
  obtain ⟨d₄, hfd₄, hled₄⟩ := hDS₄ 4 0 oD hfD
  obtain ⟨d₃, hfd₃, hled₃⟩ := hS₄ 4 0 d₄ hfd₄
  obtain ⟨d₂, hfd₂, hled₂⟩ := hMS₃ 4 0 d₃ hfd₃
  obtain ⟨d₁, hfd₁, hled₁⟩ := hS₃ 4 0 d₂ hfd₂
  rw [Row.find_append, show Row.find (Row.ofEff 4 [(.unr, A₂', B₂')] 0 fs₂) 4 0 =
    some ⟨4, 0, .unr, A₂', B₂', fs₂ 0, false⟩ from rfl, Option.some_or] at hfd₁
  cases hfd₁
  have hsigD : oD₀.Sig ⟨4, 0, .unr, A₂', B₂', fs₂ 0, false⟩ :=
    hleD.1.trans (hled₄.1.trans (hled₃.1.trans (hled₂.1.trans hled₁.1)))
  have hB₂ : B₂'.isZero = false := by
    have := hsigD.abort_eq
    rw [ha₆] at this
    simpa [OpSig.abort] using this.symm
  have hcapD₀ : capB oD₀.q oD₀.B = true := by rw [hsigD.capB_eq]; simp [capB, hB₂]
  have hcapD : capB oD.q oD.B = true := hleD.1.capB_eq ▸ hcapD₀
  -- the first finaliser puts `4` in the cancel row of `1`; the second, a leftover of that `4`'s
  -- cancel, puts `4` in its cancel row in turn
  have h₄ : FindsCap 4 o₄₁.fin := thenLe_findsCap (hfin₄ 1 0 oP o₄₁ hfP hf₄₁ hcapP) hfD hcapD
  have h₃ : FindsCap 4 o₃₁.fin := h₄.mono (hle₃₁.2 hcap₄₁)
  have h₂ : FindsRec 4 o₂₁.fin := thenLe_findsRec (hfin₃ 1 0 o₃₁ o₂₁ hf₃₁ hf₂₁ hcap₃₁) h₃ hfE
  have h₁ : FindsRec 4 (fs₁ 0) := (h₂.mono (hle₂₁'.2 hcap₂₁)).mono (hle₁.2 hcap₂₁')
  -- `H₁`'s clause row holds a `4` whose cancel row holds `4`
  obtain ⟨hnt₁, hle₁'⟩ := cancelTy_rowLe (cancelPair_jr hB₁ hH₁)
  rcases h₁ with ht | ⟨x₁, hx₁, hcx₁, hfx₁⟩
  · rw [ht] at hnt₁; cases hnt₁
  obtain ⟨x₀, hx₀, hlex₀⟩ := hle₁' 4 0 x₁ (by rw [Row.find_append, hx₁]; rfl)
  have hfx₀ : FindsAt 4 x₀.fin := hfx₁.mono (hlex₀.2 hcx₁)
  have hcx₀ : capB x₀.q x₀.B = true := hlex₀.1.capB_eq ▸ hcx₁
  -- so does the outer handler of `4`'s clause row, its own outer row
  obtain ⟨y₀, hy₀, hley₀⟩ := hS₁ 4 0 x₀ hx₀
  rw [Row.find_append, show Row.find (Row.ofEff 4 [(.unr, A₀, B₀)] 0 fs₀) 4 0 =
    some ⟨4, 0, .unr, A₀, B₀, fs₀ 0, false⟩ from rfl, Option.some_or] at hy₀
  cases hy₀
  have hB₀ : B₀.isZero = false := by
    have := hley₀.1.capB_eq ▸ hcx₀
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
    exact this.2
  have hfs₀ : FindsAt 4 (fs₀ 0) := hfx₀.mono (hley₀.2 hcx₀)
  obtain ⟨hnt₀, hle₀⟩ := cancelTy_rowLe (cancelPair_jr hB₀ hH₀)
  rcases hfs₀ with ht | ⟨y, hy⟩
  · rw [ht] at hnt₀; cases hnt₀
  obtain ⟨z, hz, -⟩ := hle₀ 4 0 y (by rw [Row.find_append, hy]; rfl)
  obtain ⟨hmz, hnz, -⟩ := Row.find_mem hz
  exact hnS₀ z hmz hnz

end Rejections

/-! ### E7c: a finaliser's raise handled only inside the cancelled region (D3)

`e7c nw ni qi = timeout (handle exnᵢ {…} (body (raise exnᵢ ())))`.  `timeout` handles a cancellable
`wait : 1 ↠ 1` of the name `nw`, and its clause cancels `κ` (`timeoutCl`); the body performs `wait`
under a finaliser that raises `exnᵢ : 1 ↠ 0`, of the name `ni`, which `toResult` handles inside the
cancelled region.  `[then]` puts `exnᵢ` in `wait`'s cancel row, and the clause applies `κ`'s cancel
branch, at `F_{F ⊕ Σ} 1`, at its own row `Σ`: so `Σ` holds `exnᵢ`, and so does every row the program
is read at (`not_der_e7c`).  At the row of `exnᵢ` the program is typed (`dAt_e7c_lift`,
`d_e7c_lift`): its context then has an instance of `exnᵢ`, which the finaliser's raise reaches
(decision D1).  So the rejection is at the rows without `exnᵢ`, and at no other. -/

/-- `timeout`'s clause, `wait (_, k) ⇒ cancel k; return (inr ())`. -/
def timeoutCl : Val :=
  Val.lam (.letpair (.var 0) (bindE (Inversions.cancelE (.var 0)) (.inj₂ .unit)))

/-- `timeout`, the handler of a cancellable `wait : 1 ↠ 1` of the name `nw`: `return x ⇒ inl x`, and
`timeoutCl`. -/
def timeoutH (nw : UInt32) : Val := hQ nw .cancel injlV timeoutCl

/-- `toResult`, the handler of an abortive `exn : 1 ↠ 0` of the name `ne` at the qualifier `q`:
`return x ⇒ inl x`, `raise _ ⇒ inr ()`. -/
def toResultH (ne : UInt32) (q : Qual) : Val := hQ ne q injlV (constC (Val.inj₂ Val.unit))

/-- `(wait (); return tt) then x. x unwind D`, `wait` of the name `nw`. -/
def bodyF (nw : UInt32) (D : Expr) : Expr := thenU (bindE (performU nw) (.inj₂ .unit)) D

/-- **E7c**: `timeout (handle exnᵢ {…} (body (raise exnᵢ ())))`, `wait` of the name `nw`, and
`exnᵢ` of the name `ni` at the qualifier `qi`.  `[spec §27]` -/
def e7c (nw ni : UInt32) (qi : Qual) : Expr :=
  hndE (timeoutH nw) (hndE (toResultH ni qi) (bodyF nw (raiseU ni)))

section Rejections
open BoCa.Fig16.LogRel.Core.Inversions

/-- **`timeout`'s clause reads `κ`'s cancel at its row**: at the clause type of a cancellable
`A ↠ B`, `B` no `0`, at the cancel row `F`, the clause applies `κ`'s cancel branch, at
`cancelTy Σ F`, which the same-term rules read at the clause's row `Σ` or below: `F` is no `⊤`, and
`Σ` finds each operation `F` finds. -/
theorem timeoutCl_finds {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R A B : VTy} {F : CTy}
    {ob : Option Lifetime.Life} (hB : B.isZero = false)
    (h : CDerives Δ Γ (.val timeoutCl) (.val (clauseTyO S R ob (.cancel, A, B) F))) :
    F.isTop = false ∧ ∀ n i o, Row.find F.rowOf n i = some o → ∃ o', Row.find S n i = some o' := by
  rw [clauseTyO_cap S R ob F hB] at h
  obtain ⟨-, hb⟩ := lam_bang h (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨Γ₁, Γ₂, A', B', C, hs, hV, hB₂, hr⟩ := der_letpair hb _ _ rfl
  have hslotP : (⟨.tensor A (kBoxO ob (kTy S R .cancel B F)), true⟩ :: Γ : Ctx VTy)[0]? =
      some ⟨.tensor A (kBoxO ob (kTy S R .cancel B F)), true⟩ := rfl
  rcases varCls_of_le hslotP (splitP_le_left hs) hV with hc | ⟨_, hT, -, -⟩
  swap
  · cases hT
  obtain ⟨rfl, rfl⟩ := vview_tensor hc
  have hslotK : (⟨kBoxO ob (kTy S R .cancel B F), true⟩ :: ⟨A, true⟩ :: Γ₂ : Ctx VTy)[0]? =
      some ⟨kBoxO ob (.thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy S F))), true⟩ := rfl
  rcases der_letJ hB₂ (.inj₂ .unit) (cancelE (.var 0)) rfl (fun _ h => by cases h)
      (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) with
    ⟨j₁, ⟨Γ₃, S₅, X, hle₃, hM, hS₅⟩, hr₁⟩ | ⟨Γ₃, X, hle₃, hM⟩
  · -- `bind` or `[let]`: `cancel k` at a row below the clause's
    have hkj := kcancel_jr_cancellable hslotK hle₃ hM
    have hS₅S : RowLe S₅ S := by
      rcases hS₅ with rfl | ⟨B', rfl⟩
      · exact RowLe.nil S
      · exact JR.rowLe (hr₁.trans hr)
    cases hF : F.isTop
    · rw [show cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit by simp [cancelTy, hF]] at hkj
      have hle := (JR.rowLe hkj).trans hS₅S
      refine ⟨rfl, fun n i o hf => ?_⟩
      obtain ⟨o', hf', -⟩ := hle n i o (by rw [Row.find_append, hf]; rfl)
      exact ⟨o', hf'⟩
    · rw [show cancelTy S F = .top by simp [cancelTy, hF]] at hkj
      have := JR.rigid hkj rigid_top
      simp only [Jdg.comp.injEq] at this
      exact (effOf_ne_top S₅ X this).elim
  · -- `⊸E`: `cancel k` at a value judgement
    have hkj := kcancel_jr_cancellable hslotK hle₃ hM
    cases hF : F.isTop
    · rw [show cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit by simp [cancelTy, hF]] at hkj
      obtain ⟨hle, -⟩ := RowCls.reach hkj (S := F.rowOf ++ S) (Y := .unit)
        ⟨_, _, rfl, RowLe.refl _, .refl⟩
      refine ⟨rfl, fun n i o hf => ?_⟩
      obtain ⟨o', hf', -⟩ := hle n i o (by rw [Row.find_append, hf]; rfl)
      simp [Row.find] at hf'
    · rw [show cancelTy S F = .top by simp [cancelTy, hF]] at hkj
      have := JR.rigid hkj rigid_top
      cases this

/-- **`e7c` has no derivation at a row without `exnᵢ`** (decision D3).  `[handle] wait`'s body holds
`handle exnᵢ {…} (body (raise exnᵢ ()))`: the `[then]`'s premise puts `exnᵢ` in the cancel row of
`wait`, which `[sub]` up to the body keeps (cancel rows only grow); the `timeout` clause applies
`κ`'s cancel branch, at `F_{fs 0 ⊕ Σ} 1`, and the same-term rules read it at the clause's row `Σ`,
so `Σ` holds `exnᵢ`, and so does every row the program is read at.  `[spec §27]` -/
theorem not_der_e7c {Δ : LifeCtx} {Γ : Ctx VTy} {nw ni : UInt32} {qi : Qual} (hne : nw ≠ ni)
    {S' : Row} {Y : VTy} (hS' : ∀ o ∈ S', o.n ≠ ni) :
    ¬ CDerives Δ Γ (e7c nw ni qi) (.comp (CTy.effOf S' Y)) := by
  intro h
  -- `[handle] wait`
  obtain ⟨j₁, ⟨Γ₁, Γ₂, S, E, fs, A, R, _, -, hQ, hH, hM, -, rfl⟩, hr₁⟩ :=
    der_hndJ₁ (n := nw) (Q := (qualsVal [.cancel]).1)
      (H := (.pair (.val injlV) (.pair (.val timeoutCl) (.val Val.unit))))
      (M := (hndE (toResultH ni qi) (bodyF nw (raiseU ni)))) h (by not_tail [timeoutCl, constC, bindE, Inversions.cancelE])
  have hSS' : RowLe S S' := JR.rowLe hr₁
  have hE : [Qual.cancel] = E.map Prod.fst := qualsVal_inj hQ
  obtain ⟨⟨q₁, A₁, B₁⟩, rfl⟩ : ∃ e, E = [e] := by
    rcases E with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE
    · exact ⟨e, rfl⟩
    · simp at hE
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE
  subst hE
  -- `[handle] exnᵢ`, then the `[then]`
  obtain ⟨j₂, ⟨Γ₃, Γ₄, S₂, E₂, fs₂, A₂, R₂, _, -, -, -, hM₂, -, rfl⟩, hr₂⟩ :=
    der_hndJ₁ (n := ni) (Q := (qualsVal [qi]).1)
      (H := (.pair (.val injlV) (.pair (.val (constC (Val.inj₂ Val.unit))) (.val Val.unit))))
      (M := (bodyF nw (raiseU ni))) hM (by not_tail [timeoutCl, constC, bindE, Inversions.cancelE])
  have hS₂ : RowLe S₂ (Row.ofEff nw [(.cancel, A₁, B₁)] 0 fs ++ S) := JR.rowLe hr₂
  obtain ⟨j₃, ⟨Γ₅, Γ₆, A₃, B₃, S₃, SM, SD, -, hMS, -, hfin, hMp, hDr, rfl⟩, hr₃⟩ :=
    der_thenJ hM₂ (.var 0) (raiseU ni) (bindE (performU nw) (.inj₂ .unit)) rfl
  have hS₃ : RowLe S₃ (Row.ofEff ni E₂ 0 fs₂ ++ S₂) := JR.rowLe hr₃
  -- `wait ()`'s row finds `wait`, below the `[then]`'s `M`'s row
  obtain ⟨S₄, oM₀, hf₄, ha₄, hS₄M⟩ : ∃ (S₄ : Row) (oM₀ : OpSig), Row.find S₄ nw 0 = some oM₀ ∧
      oM₀.abort = false ∧ RowLe S₄ SM := by
    rcases der_letJ hMp (.inj₂ .unit) (performU nw) rfl (fun _ h => by cases h)
        (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h)
        (fun h => by cases h) with
      ⟨j₄, ⟨Γ₇, S₇, X₇, -, hP, hS₇⟩, hr₄⟩ | ⟨Γ₇, X₇, -, hP⟩
    · obtain ⟨j₅, ⟨S₅, oM₀, hf₅, ha₅, rfl⟩, hr₅⟩ := der_performJ hP nw 0 (.val Val.unit) rfl
      have h57 : RowLe S₅ S₇ := JR.rowLe hr₅
      rcases hS₇ with rfl | ⟨B₇, rfl⟩
      · obtain ⟨o', hf', -⟩ := h57 nw 0 oM₀ hf₅
        simp [Row.find] at hf'
      · exact ⟨S₅, oM₀, hf₅, ha₅, h57.trans (JR.rowLe hr₄)⟩
    · obtain ⟨j₅, ⟨S₅, oM₀, hf₅, -, rfl⟩, hr₅⟩ := der_performJ hP nw 0 (.val Val.unit) rfl
      obtain ⟨hle, -⟩ := RowCls.reach hr₅ (S := S₅) (Y := oM₀.B) ⟨_, _, rfl, RowLe.refl _, .refl⟩
      obtain ⟨o', hf', -⟩ := hle nw 0 oM₀ hf₅
      simp [Row.find] at hf'
  obtain ⟨oM, hfM, hleM⟩ := hS₄M nw 0 oM₀ hf₄
  -- the finaliser's row finds `exnᵢ`
  obtain ⟨j₆, ⟨S₆, oD₀, B₆, hf₆, -, rfl⟩, hr₆⟩ := der_raiseJ hDr ni 0 (.val Val.unit) rfl
  obtain ⟨oD, hfD, -⟩ := JR.rowLe hr₆ ni 0 oD₀ hf₆
  -- `wait` from the `[then]` up to `[handle] wait`'s body
  obtain ⟨o₃, hf₃, hle₃⟩ := hMS nw 0 oM hfM
  obtain ⟨o₄, hf₄', hle₄⟩ := hS₃ nw 0 o₃ hf₃
  rw [Row.find_append, Row.find_ofEff_ne ni E₂ 0 fs₂ nw 0 hne, Option.none_or] at hf₄'
  obtain ⟨o₅, hf₅', hle₅⟩ := hS₂ nw 0 o₄ hf₄'
  rw [Row.find_append, show Row.find (Row.ofEff nw [(.cancel, A₁, B₁)] 0 fs) nw 0 =
    some ⟨nw, 0, .cancel, A₁, B₁, fs 0, false⟩ by simp [Row.ofEff, Row.find], Option.some_or] at hf₅'
  cases hf₅'
  have hsig : oM₀.Sig ⟨nw, 0, .cancel, A₁, B₁, fs 0, false⟩ :=
    hleM.1.trans (hle₃.1.trans (hle₄.1.trans hle₅.1))
  have hB₁ : B₁.isZero = false := by
    have := hsig.abort_eq
    rw [ha₄] at this
    simpa [OpSig.abort] using this.symm
  have hcap₀ : capB oM₀.q oM₀.B = true := by
    rw [hsig.capB_eq]; simp [capB, hB₁]
  have hcapM : capB oM.q oM.B = true := hleM.1.capB_eq ▸ hcap₀
  have hcap₃ : capB o₃.q o₃.B = true := hle₃.1.capB_eq ▸ hcapM
  have hcap₄ : capB o₄.q o₄.B = true := hle₄.1.capB_eq ▸ hcap₃
  -- `exnᵢ` in the cancel row of `wait`, or that cancel row `⊤`
  have h₃₄ : FinLe o₃.fin o₄.fin := hle₄.2 hcap₃
  have h₄₅ : FinLe o₄.fin (fs 0) := hle₅.2 hcap₄
  have hfs : (fs 0).isTop = true ∨ ∃ o₆, Row.find (fs 0).rowOf ni 0 = some o₆ := by
    have hT := hfin nw 0 oM o₃ hfM hf₃ hcapM
    rw [ThenLe] at hT
    rcases hT with hT | ⟨-, -, hT⟩
    · exact .inl (finLe_top_top h₄₅ (finLe_top_top h₃₄ hT))
    · obtain ⟨o', hf', -⟩ := hT ni 0 oD hfD
      rcases finLe_find h₃₄ hf' with h₄ | ⟨o'', hf''⟩
      · exact .inl (finLe_top_top h₄₅ h₄)
      · exact finLe_find h₄₅ hf''
  -- the clause reads `κ`'s cancel at its row
  rcases der_pair hH _ _ rfl with ⟨Γ₇, Γ₈, X₁, X₂, -, -, hcl, hc₁⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨-, rfl⟩ := vview_tensor hc₁
  rcases der_pair hcl _ _ rfl with ⟨Γ₉, Γ₁₀, X₃, X₄, -, hcan, -, hc₂⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32, timeoutCl] at he
  rw [clausesTyO_cons, clausesTyO_nil] at hc₂
  obtain ⟨rfl, -⟩ := vview_tensor hc₂
  obtain ⟨hnt, hfS⟩ := timeoutCl_finds hB₁ hcan
  rcases hfs with htop | ⟨o₆, hf₆'⟩
  · rw [hnt] at htop; cases htop
  · obtain ⟨o₇, hf₇⟩ := hfS ni 0 o₆ hf₆'
    obtain ⟨o₈, hf₈, -⟩ := hSS' ni 0 o₇ hf₇
    obtain ⟨hm₈, hn₈, -⟩ := Row.find_mem hf₈
    exact hS' o₈ hm₈ hn₈

end Rejections

/-! #### `e7c` at the row of `exnᵢ` -/

/-- `exn`'s row: its one abortive operation `1 ↠ 0`, of the name `n` at the qualifier `q`. -/
abbrev exnRow (n : UInt32) (q : Qual) : Row := Row.ofEff n [(q, .unit, .zero)] 0

/-- `wait`'s row: its one cancellable operation `1 ↠ 1`, of the name `n`, at the cancel row `F`. -/
abbrev waitRow (n : UInt32) (F : CTy) : Row := Row.ofEff n [(.cancel, .unit, .unit)] 0 (fun _ => F)

/-- The cancel row of a raise of `exn`. -/
abbrev finExn (n : UInt32) (q : Qual) : CTy := CTy.effOf (exnRow n q) .unit

/-- A one-operation row finds its operation at its key alone. -/
theorem find_ofEff_one {n : UInt32} {e : Qual × VTy × VTy} {fs : Nat → CTy} {m i : UInt32}
    {o : OpSig} (h : Row.find (Row.ofEff n [e] 0 fs) m i = some o) :
    m = n ∧ i = 0 ∧ o = ⟨n, 0, e.1, e.2.1, e.2.2, fs 0, false⟩ := by
  obtain ⟨rfl, j, hj, rfl, rfl⟩ := Row.find_ofEff n [e] 0 fs m i o h
  obtain rfl : j = 0 := by simp at hj; omega
  exact ⟨rfl, rfl, rfl⟩

/-- `wait`'s operation, as the handled row of a `timeout` finds it. -/
theorem find_wait (nw : UInt32) (F : CTy) (S : Row) :
    Row.find (waitRow nw F ++ S) nw 0 = some ⟨nw, 0, .cancel, .unit, .unit, F, false⟩ := by
  simp [Row.ofEff, Row.find]

/-- A row is below itself followed by another. -/
theorem rowLe_append_right (S T : Row) : RowLe S (S ++ T) :=
  RowLe.of_find fun n i o hf => by rw [Row.find_append, hf, Option.some_or]

/-- A row followed by itself is below it. -/
theorem rowLe_dup (S : Row) : RowLe (S ++ S) S := by
  refine RowLe.of_find fun n i o hf => ?_
  rw [Row.find_append] at hf
  cases h : Row.find S n i with
  | none => rw [h] at hf; cases hf
  | some o' => rw [h, Option.some_or] at hf; rw [hf]

/-- A row of names other than `n` is below `n`'s signature row before it, at any cancel rows. -/
theorem rowLe_ofEff_cons {n : UInt32} (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) {T : Row}
    (hT : ∀ o ∈ T, o.n ≠ n) : RowLe T (Row.ofEff n E 0 fs ++ T) := by
  refine RowLe.of_find fun m i o hf => ?_
  rw [Row.find_append, Row.find_ofEff_ne n E 0 fs m i ?_, Option.none_or]
  · exact hf
  · obtain ⟨hm, rfl, -⟩ := Row.find_mem hf
    exact hT o hm

/-- Rows that find the same operation at every key are below each other. -/
theorem rowLe_of_find_eq {S S' : Row} (h : ∀ n i, Row.find S n i = Row.find S' n i) :
    RowLe S S' :=
  RowLe.of_find fun n i _ hf => (h n i) ▸ hf

/-- **A finaliser that raises `exn`**, below a continuation whose cancel row is empty, puts the
raise in that cancel row: `[] ⋈ exn ≤ {exn}`. -/
theorem thenLe_exn (n : UInt32) (q : Qual) : ThenLe (.ret .unit) (exnRow n q) (finExn n q) := by
  rw [ThenLe]
  refine .inr ⟨rfl, fun _ _ _ hf => by simp [CTy.rowOf, Row.find] at hf, fun m i o hf => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
  refine ⟨_, ?_, OpSig.Sig.refl _, fun hc => by simp [capB, VTy.isZero] at hc⟩
  rw [CTy.rowOf_effOf]
  exact hf

/-- **`timeout`'s clause** at a cancellable `1 ↠ 1` whose cancel row `F` holds operations of the
clause's row `S`: `κ`'s cancel at `F_{F ⊕ Σ} 1`, read at `Σ` (`[sub]`, D3's check). -/
theorem d_timeoutCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {X : VTy} {F : CTy}
    (hF : F.isTop = false) (hFS : RowLe (F.rowOf ++ S) S) :
    CDerives Δ Γ (.val timeoutCl) (.val (clauseTy S (.sum X .unit) (.cancel, .unit, .unit) F)) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .effLet (A := .unit) (.left (.left (.dead (deadSplit hΓ))))
    (fun _ => fun s hs hl => ?_) (fun _ => fun s hs hl => ?_) ?_ ?_
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · cases hl
    · cases hl
    · cases hl
    · exact dead_noLive (P := fun s => s.ty.OwnFree) hΓ s hs hl
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · cases hl
    · cases hl
    · cases hl
    · exact dead_noLive (P := fun s => ∃ A, s.ty = .bang A) hΓ s hs hl
  · have hct : cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit := by simp [cancelTy, hF]
    refine .effSub hFS ?_
    rw [← hct]
    exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S (.sum X .unit))) (cancelTy S F))
      (.here (.drop rfl (.cons hΓ.toP))))
  · exact .effSub (RowLe.nil S) (.ret (.sumI₂ (.unitI (.drop rfl (.cons (.cons (.cons hΓ.toP)))))))

section Tied
variable {Ξ : EffCtx}

/-- **`timeout M`**, tied: at the row `S`, `M` at `wait`'s row before `S`, `wait`'s cancel row `F`
holding operations of `S`. -/
theorem dAt_timeout {Δ : LifeCtx} {nw : UInt32} (hw : Ξ nw = [(.cancel, .unit, .unit)])
    (hnw : nw ≠ 0) {S : Row} (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ nw) {X : VTy} {F : CTy}
    (hF : F.isTop = false) (hFS : RowLe (F.rowOf ++ S) S) {M : Expr}
    (hM : CDerivesAt Ξ Δ [] M (.comp (CTy.effOf (waitRow nw F ++ S) X)))
    (hdv : Row.divB (waitRow nw F ++ S) = false := by div_free) :
    CDerivesAt Ξ Δ [] (hndE (timeoutH nw) M) (.comp (CTy.effOf S (.sum X .unit))) := by
  show CDerivesAt Ξ Δ [] (hndExpr nw [.cancel] (.pair (.val injlV) (.pair (.val timeoutCl)
    (.val Val.unit))) M) _
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.cancel, .unit, .unit)]) (fs := fun _ => F)
    (rowAt_ofEff_fs (rowAt_ofEff_append hw hnw (by simp) hS)) .nil .nil
    (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_injlV _ X .unit)
      (.tensorI .nil (d_timeoutCl .nil hF hFS) (.unitI .nil))) rfl)
    hnw hnS (by simp) hdv hM

/-- **`toResult M`**, tied: at the row `S`, `M` at `exn`'s row before `S`, `exn` cancellable or
unrestricted. -/
theorem dAt_toResult {Δ : LifeCtx} {ne : UInt32} {q : Qual} (he : Ξ ne = [(q, .unit, .zero)])
    (hne : ne ≠ 0) (hq : q ≠ .lin) {S : Row} (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ ne) {A : VTy}
    {M : Expr} (hM : CDerivesAt Ξ Δ [] M (.comp (CTy.effOf (exnRow ne q ++ S) A)))
    (hdv : Row.divB (exnRow ne q ++ S) = false := by div_free) :
    CDerivesAt Ξ Δ [] (hndE (toResultH ne q) M) (.comp (CTy.effOf S (.sum A .unit))) := by
  have hcl : CDerives Δ [] (.val (constC (Val.inj₂ Val.unit)))
      (.val (clauseTy S (.sum A .unit) (q, .unit, .zero))) := by
    rw [clauseTy_abortive hq]
    exact d_constC_raise S (.sumI₂ (.unitI (.cons .nil)))
  show CDerivesAt Ξ Δ [] (hndExpr ne [q] (.pair (.val injlV)
    (.pair (.val (constC (Val.inj₂ Val.unit))) (.val Val.unit))) M) _
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(q, .unit, .zero)]) (fs := finsNil)
    (rowAt_ofEff_append he hne (by simp) hS) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (CDerivesAt.ofEffFree (.tensorI .nil (d_injlV _ A .unit) (.tensorI .nil hcl (.unitI .nil)))
      rfl)
    hne hnS (by simp) hdv hM

/-- The raise of `exn`, tied, at its row. -/
theorem dAt_raiseU {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) {n : UInt32} {q : Qual}
    (hn : Ξ n = [(q, .unit, .zero)]) (hn0 : n ≠ 0) (hq : q ≠ .lin) (B : VTy) :
    CDerivesAt Ξ Δ Γ (raiseU n) (.comp (CTy.effOf (exnRow n q) B)) :=
  .effRaise (o := ⟨n, 0, q, .unit, .zero, .ret .unit, false⟩)
    (rowAt_left (S' := []) (rowAt_ofEff_append hn hn0 (by simp) (rowAt_nil Ξ)))
    (by simp [Row.ofEff, Row.find]) (by cases q <;> simp_all [OpSig.abort, VTy.isZero]) .unit
    (.unitI hΓ)

/-- **`(wait (); return tt) then x. x unwind D`**, tied, at the handled row `wait⟨F⟩ ⊙ S` of a
`timeout`: the finaliser at a row `SD` below it, and `F` above what the finaliser may do when
`wait`'s continuation is cancelled (`[] ⋈ SD ≤ F`). -/
theorem dAt_bodyF {Δ : LifeCtx} {nw : UInt32} (hw : Ξ nw = [(.cancel, .unit, .unit)]) (hnw : nw ≠ 0)
    {S SD : Row} {F : CTy} (hNZ : (waitRow nw F ++ S).NZ) (hUq : (waitRow nw F ++ S).Uniq)
    (hDS : RowLe SD (waitRow nw F ++ S)) (hfin : ThenLe (.ret .unit) SD F) {D : Expr}
    (hD : CDerivesAt Ξ Δ [⟨.unit, false⟩] D (.comp (CTy.effOf SD .unit)))
    (hSD : Row.divB SD = false := by div_free) :
    CDerivesAt Ξ Δ [] (bodyF nw D) (.comp (CTy.effOf (waitRow nw F ++ S) (.sum .unit .unit))) := by
  have hW : RowAt Ξ (Row.ofEff nw [(.cancel, .unit, .unit)] 0) :=
    rowAt_left (S' := []) (rowAt_ofEff_append hw hnw (by simp) (rowAt_nil Ξ))
  have hM : CDerivesAt Ξ Δ [] (bindE (performU nw) (.inj₂ .unit))
      (.comp (CTy.effOf (Row.ofEff nw [(.cancel, .unit, .unit)] 0) (.sum .unit .unit))) :=
    .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil)
      (.effPerform (o := ⟨nw, 0, .cancel, .unit, .unit, .ret .unit, false⟩) hW
        (by simp [Row.ofEff, Row.find]) rfl (.unitI .nil))
      (.effSub (RowLe.nil _) (.ret (.sumI₂ (.unitI (.drop rfl .nil)))))
  show CDerivesAt Ξ Δ [] (thenE (.var 0) D (bindE (performU nw) (.inj₂ .unit))) _
  refine .effThen (SM := Row.ofEff nw [(.cancel, .unit, .unit)] 0) (SD := SD) .nil hNZ hUq
    (fun _ => fun _ h => absurd h List.not_mem_nil) ?_ hDS ?_ ?_ hSD hM
    (.effSub (RowLe.nil _) (.ret (.var (.here .nil)))) hD
  · intro n i o hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    refine ⟨_, find_wait n F S, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    exact (finLe_iff _ _).mpr (.inr ⟨rfl, RowLe.nil _⟩)
  · intro n i o o' hf hf' _
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    rw [find_wait n F S] at hf'
    cases hf'
    exact hfin
  · intro _ o ho
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, VTy.isZero] at h, fun _ => trivial⟩

/-- **`e7c` at the row of `exnᵢ`, tied** (decision D1): the finaliser's raise reaches the context's
instance of `exnᵢ`, recorded in `wait`'s cancel row and live at the `timeout` clause's row.
`[spec §27]` -/
theorem dAt_e7c_lift {Δ : LifeCtx} {nw ni : UInt32} {qi : Qual}
    (hw : Ξ nw = [(.cancel, .unit, .unit)]) (hi : Ξ ni = [(qi, .unit, .zero)]) (hqi : qi ≠ .lin)
    (hnw : nw ≠ 0) (hni : ni ≠ 0) (hne : nw ≠ ni) :
    CDerivesAt Ξ Δ [] (e7c nw ni qi)
      (.comp (CTy.effOf (exnRow ni qi) (.sum (.sum (.sum .unit .unit) .unit) .unit))) := by
  have hSi : RowAt Ξ (exnRow ni qi) :=
    rowAt_left (S' := []) (rowAt_ofEff_append hi hni (by simp) (rowAt_nil Ξ))
  have hW : RowAt Ξ (waitRow nw (finExn ni qi)) :=
    rowAt_left (S' := []) (rowAt_ofEff_fs (rowAt_ofEff_append hw hnw (by simp) (rowAt_nil Ξ)))
  have hnSi : ∀ o ∈ exnRow ni qi, o.n ≠ nw := by
    intro o ho
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact Ne.symm hne
  have hnW : ∀ o ∈ waitRow nw (finExn ni qi), o.n ≠ ni := by
    intro o ho
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact hne
  -- `timeout` at the row of `exnᵢ`, `wait`'s cancel row holding it
  refine dAt_timeout hw hnw hSi hnSi (X := .sum (.sum .unit .unit) .unit) (F := finExn ni qi) rfl
    (by rw [CTy.rowOf_effOf]; exact rowLe_dup _) ?_
  -- `toResult` at `wait`'s row alone, read at the row of `exnᵢ` after it
  refine .effSub (rowLe_append_right _ _) (dAt_toResult hi hni hqi hW hnW ?_)
  -- the body at `wait`'s row before `exnᵢ`'s, read at `exnᵢ`'s before `wait`'s
  have hB := dAt_bodyF (Δ := Δ) hw hnw (S := exnRow ni qi) (SD := exnRow ni qi) (F := finExn ni qi)
    ?_ ?_
    (rowLe_ofEff_cons _ _ hnSi) (thenLe_exn ni qi) (dAt_raiseU (.cons .nil) hi hni hqi .unit)
  · refine .effSub (rowLe_of_find_eq fun n i => ?_) hB
    simp only [Row.find_append]
    by_cases hn : n = nw
    · subst hn
      rw [Row.find_ofEff_ne ni _ 0 _ _ i hne, Option.none_or, Option.or_none]
    · rw [Row.find_ofEff_ne nw _ 0 _ n i hn, Option.none_or, Option.or_none]
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact hnw
    · exact hni
  · simp [Row.Uniq, Row.ofEff, hne]

end Tied

/-- The effect context of `e7c`: `wait : 1 ↠ 1` cancellable at `nw`, and `exnᵢ : 1 ↠ 0` at the
qualifier `qi` at `ni`. -/
def Ξe7c (nw ni : UInt32) (qi : Qual) : EffCtx := fun n =>
  if n = nw then [(.cancel, .unit, .unit)] else if n = ni then [(qi, .unit, .zero)] else []

/-- At an `exnᵢ` that is not unrestricted, `e7c`'s effect context has no unrestricted abortive
operation (decision 63's restriction), as the context of every program the checker accepts has
(`checkProgram_tiedAt`). -/
theorem noUnrExn_Ξe7c {nw ni : UInt32} {qi : Qual} (hqi : qi ≠ .unr) :
    (Ξe7c nw ni qi).NoUnrExn := by
  intro n p hp hq
  unfold Ξe7c at hp
  split at hp
  · simp only [List.mem_singleton] at hp; subst hp; simp at hq
  · split at hp
    · simp only [List.mem_singleton] at hp; subst hp; exact absurd hq hqi
    · cases hp

/-- **`e7c` is typed at the row of `exnᵢ`** (decision D1), at a cancellable or unrestricted `exnᵢ`:
the rejection `not_der_e7c` is at the rows without `exnᵢ`, and at no other.  `[spec §27]` -/
theorem d_e7c_lift {Δ : LifeCtx} {nw ni : UInt32} {qi : Qual} (hqi : qi ≠ .lin) (hnw : nw ≠ 0)
    (hni : ni ≠ 0) (hne : nw ≠ ni) :
    CDerives Δ [] (e7c nw ni qi)
      (.comp (CTy.effOf (exnRow ni qi) (.sum (.sum (.sum .unit .unit) .unit) .unit))) :=
  (dAt_e7c_lift (Ξ := Ξe7c nw ni qi) (by simp [Ξe7c]) (by simp [Ξe7c, Ne.symm hne]) hqi hnw hni
    hne).toCDerives

end BoCa.Fig16.LogRel.Core.CancelIntercept
