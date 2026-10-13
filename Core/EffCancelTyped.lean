import Core.EffCancel
import Core.Fundamental
import Core.Examples

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
| `progT` | `{2}`, typed at a row holding `2` (at no row without `2`, by inversion: not yet a Core theorem) | a raise of `2` no handler catches |
| `progOutT` | `{2}`, the outer `2` live | `inj₂ ()` |
| `cancelKeptT` | `{3}`, `H₃` outside | `inj₂ ()` |
| `progReT` | `{3}`: `f ()` at `{1}`, the region re-entering the site `3` | `inj₂ ()` |
| `progFinOpT` | `{4}`: the finaliser performs `4`, the outer `4` resumes it | `inj₁ ()` |
| `progNC₁T` | `{4}`: the outer `4` cancels the finaliser's continuation (`[cfin-cancel]`) | `()` |
| `progDropT` | `{2, 4⟨{2}⟩}`: the kept `2` pending at the second finaliser's `4` (`pend`); `H₄ₒ` drops `κ₄` | `inj₁ ()` |
| `progKeepT` | `{2, 4⟨{2}⟩}`; `H₄ₒ` resumes `κ₄`, and the kept `2` reaches `H₂ₒ` | `inj₂ ()` |

`progNCrecT`, two finalisers that perform `4` under the handler of `4` that cancels, has no
derivation (the second finaliser is a leftover of the first one's cancel, `⋈`; the rejection is
not yet a Core theorem), and its run ends at a `perform 4` outside every handler of `4`
(`progNCrecT_run`).
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

/-! ### Typing -/

/-- The operation `0` of the name `n`, unrestricted and abortive: `raise : 1 ↠^unr 0`. -/
def rSig (n : UInt32) : OpSig := ⟨n, 0, .unr, .unit, .zero, .ret .unit⟩

/-- The operation `0` of the name `n`, unrestricted, `1 ↠ 1`, at the cancel row `F`. -/
def pSig (n : UInt32) (F : CTy) : OpSig := ⟨n, 0, .unr, .unit, .unit, F⟩

/-- The cancel row of a raise of `m`. -/
abbrev finR (m : UInt32) : CTy := CTy.effOf [rSig m] .unit

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
    (SD := [rSig 2]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
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
    exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
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
    (by decide) (by simp [pSig]) (by simp) d_then₂

/-- **`progT` is typed at a row holding `2`**: the cancel row of `perform 1`'s continuation is
`{2}`, and `H₁`'s clause reads `κ`'s cancel at `F_{{2} ⊕ Σ} 1` at its row `Σ = {2}`. -/
theorem d_progT {Δ : LifeCtx} : CDerives Δ [] progT (.comp (CTy.effOf [rSig 2] .unit)) := by
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    ((K 2).plug (performU 1))) _
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 2)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) ?_
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
    (by decide) (by simp) (by simp) d_progT

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
    (SD := [pSig 4 (.ret .unit)]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finP 4), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
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
    refine ⟨pSig 4 (.ret .unit), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
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
    (by decide) (by simp [pSig]) (by simp) d_thenP

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
    (by decide) (by simp [pSig]) (by simp) ?_
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
    (by decide) (by simp) (by simp) d_midP

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
    (by decide) (by simp) (by simp) d_midP

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
    (SD := [rSig 2]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
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
    exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
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
    (SD := [pSig 4 (.ret .unit)]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ d_thenK₁ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · refine ⟨pSig 1 finKD, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
      refine (finLe_iff _ _).mpr (Or.inr ⟨rfl, RowLe.of_mem fun o ho => ?_⟩)
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at ho
      subst ho
      exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
    · exact ⟨rSig 2, rfl, OpSig.LeF.refl _⟩
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 4 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
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
      exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
    · obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      simp only [List.mem_singleton] at hm
      subst hm
      refine ⟨pSig 4 (finR 2), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
      rw [PendLe]
      refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, pSig] at h,
        fun n i o h ha => ?_⟩
      obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      rw [show (pSig 1 (finR 2)).fin.rowOf = [rSig 2] from rfl, List.mem_singleton] at hm
      subst hm
      exact ⟨rSig 2, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
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
    (by decide) (by simp [rSig, pSig]) (by simp) d_thenK₂
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
    (by decide) (by simp) (by simp) ?_
  show CDerives Δ [] (hndExpr 4 [.unr] (.pair (.val injlV) (.pair (.val c) (.val Val.unit)))
    (hndE H₁T (thenU (thenU (performU 1) (raiseU 2)) (performU 4))))
    (.comp (CTy.effOf [rSig 2] (.sum .unit .unit)))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 2)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_injlV _ .unit .unit) (.tensorI .nil hc (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) ?_
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
    (SD := [rSig 3]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 3), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
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
    exact ⟨rSig 3, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
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
    (by decide) (by simp) (by simp) ?_
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    ((K 3).plug (performU 1))) (.comp (CTy.effOf [rSig 3] .unit))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 3)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) ?_
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
      (by decide) (by simp [rSig, pSig]) (by simp) d_then₃

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
    (by decide) (by simp [pSig]) (by simp)
    (.effPerform (o := pSig 1 (.ret .unit)) rfl rfl (.unitI (.drop rfl .nil)))

/-- **The `[then]` of `progReT`**: `f () then x. x unwind raise 3` at `{1⟨{3}⟩, 3}`. -/
theorem d_thenRe {Δ : LifeCtx} :
    CDerives Δ [] (thenU (.app (.val fRe) (.val Val.unit)) (raiseU 3))
      (.comp (CTy.effOf [pSig 1 (finR 3), rSig 3] .unit)) := by
  show CDerives Δ [] (thenE (.var 0) (raiseU 3) (.app (.val fRe) (.val Val.unit))) _
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [pSig 1 (.ret .unit)])
    (SD := [rSig 3]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ d_fRe ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, pSig]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    refine ⟨pSig 1 (finR 3), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
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
    exact ⟨rSig 3, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun hc => absurd hc (by decide)⟩
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
    (by decide) (by simp) (by simp) ?_
  show CDerives Δ [] (hndExpr 1 [.unr] (.pair (.val idV) (.pair (.val cancelCT) (.val Val.unit)))
    (thenU (.app (.val fRe) (.val Val.unit)) (raiseU 3))) (.comp (CTy.effOf [rSig 3] .unit))
  refine .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .unit)]) (fs := fun _ => finR 3)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_cancelCT rfl ?_) (.unitI .nil)))
    (by decide) (by simp [rSig]) (by simp) d_thenRe
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

end BoCa.Fig16.LogRel.Core.CancelIntercept
