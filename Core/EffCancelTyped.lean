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

* `progT`: the finaliser raises `2`, a name handled only inside the region.  It is typed at a row
  holding `2`, the cancel row of `perform 1`'s continuation `{2}` (`d_progT`), and at no row without
  `2` (`experiments/Targets`, `not_der_progT`); its run ends at a raise of `2` (`progT_run`).
* `progOutT`: `progT` under a live handler of `2`, typed at `F (1 ⊕ 1)` (`d_progOutT`); every run
  reaches `inj₂ ()` (`progOutT_run`).
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

/-- `λx. x : !U(A ⊸ F_Σ A)`. -/
theorem d_idV {Δ : LifeCtx} (S : Row) (A : VTy) :
    CDerives Δ [] (.val idV) (.val (retTy S A A)) :=
  .bangThunkV (dead_noLive .nil) rfl (.lam (.effSub (RowLe.nil S) (.ret (.var (.here .nil)))))

/-- `λx. inj₁ x : !U(A ⊸ F_Σ (A ⊕ B))`. -/
theorem d_injlV {Δ : LifeCtx} (S : Row) (A B : VTy) :
    CDerives Δ [] (.val injlV) (.val (retTy S A (.sum A B))) :=
  .bangThunkV (dead_noLive .nil) rfl
    (.lam (.effSub (RowLe.nil S) (.ret (.sumI₁ (.var (.here .nil))))))

/-- An abortive operation's clause `λ_. v`, at `!U(1 ⊸ F_Σ R)`. -/
theorem d_constC_raise {Δ : LifeCtx} (S : Row) {R : VTy} {v : Val}
    (hv : CDerives Δ [⟨.unit, false⟩] (.val v) (.val R)) :
    CDerives Δ [] (.val (constC v)) (.val (clauseTy S R (.unr, .unit, .zero) (.ret .unit))) :=
  .bangThunkV (dead_noLive .nil) rfl (.lamDead (.effSub (RowLe.nil S) (.ret hv)))

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

end BoCa.Fig16.LogRel.Core.CancelIntercept
