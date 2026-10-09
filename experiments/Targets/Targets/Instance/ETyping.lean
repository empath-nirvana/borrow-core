import Targets.Instance.ELabels
import Targets.Instance.FinRaise
import Targets.Instance.UnaryLaws
import Targets.Instance.ClauseRefusals

/-!
# The Instance — typing the (E) programs at `J₁`

Derivations of Core's kernel, its inner rows tied to the effect context (`CDerivesAt Ξ`), for the
pieces A's (E) programs are built from at our instance, and the step from such a derivation to our
instance's typing at `J₁`.

* **Callbacks** (`d_cbDead`): `λ_. M` at `U(1 ⊸ F_Σ B)` by SPEC §26's `[λ-dead]`, from `M` at the
  empty context, for every closed callback body a schema quantifies over.
* **Handlers** (`d_handleK`): our instance's handler frame is Core's `[handle]` at a value form
  (SPEC §24), at the context's signature of the handled name.
* **Polymorphic function types** (`polyTy`): `U(∀ρ:any. C)`, its instances `C` at each row tied to
  the context; a closed λ-value Core types at every instance is typed at `J₁` (`derV_poly_J₁`).
* **Closed programs** (`der_J₁_closed`): a closed program Core's tied kernel types at a closed row
  tied to the context is typed at `J₁`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont performE raiseE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil rowAt_ofEff_append CDerivesAt RVar RowEnv
  RowCtx RowCon)

/-! ### Rows -/

/-- A label's row: its operations at the signature the context declares. -/
def rowOf {Ξ : EffCtx} (l : (orowAlg Ξ).Lab) : Row := Row.ofEff l.1 (Ξ l.1) 0

theorem rowAt_rowOf {Ξ : EffCtx} (l : (orowAlg Ξ).Lab) : RowAt Ξ (rowOf l) :=
  Targets.ofEff_wf Ξ l.1 l.2.1 l.2.2.2

theorem rowAt_rowOf_append {Ξ : EffCtx} (l : (orowAlg Ξ).Lab) {S : Row} (hS : RowAt Ξ S) :
    RowAt Ξ (rowOf l ++ S) :=
  Targets.rowAt_append (rowAt_rowOf l) hS

/-- A row's names are its operations' names. -/
theorem mem_ofEff_n {n : UInt32} : ∀ {E : List (Qual × VTy × VTy)} {k : Nat} {o : OpSig},
    o ∈ Row.ofEff n E k → o.n = n
  | [], _, _, h => by simp [Row.ofEff] at h
  | (q, A, B) :: E, k, o, h => by
      simp only [Row.ofEff, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact mem_ofEff_n h

/-! ### Callbacks and handlers -/

section Kernel
variable {Ξ : EffCtx}

/-- **A callback `λ_. M`** at `U(1 ⊸ F_Σ B)`, from a closed `M` at `F_Σ B`, at every context of
dead slots (SPEC §26's `[λ-dead]`). -/
theorem d_cbDead {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {M : Expr} {S : Row} {B : VTy}
    (h : CDerivesAt Ξ Δ [] M (.comp (CTy.effOf S B))) :
    CDerivesAt Ξ Δ Γ (.lam M) (.val (.thunk (.arr .unit (CTy.effOf S B)))) :=
  .thunkV rfl (.lamDead (h.append_dead (Γ' := ⟨.unit, false⟩ :: Γ) (.cons hΓ)))

/-- **Our instance's handler frame is `[handle]` at a value form**: the handler value `(n, (qs,
(h_ret, hs)))`, closed, is typed at the dead copy of the context, and the body at the context. -/
theorem d_handleK {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A R : VTy} {n : UInt32} {r : Expr}
    {cs : List Expr} {M : Expr} (hAt : RowAt Ξ (Row.ofEff n (Ξ n) 0 ++ S)) (hn0 : n ≠ 0)
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : (Ξ n).length ≤ 2 ^ 32) (hv : IsVal (.pair r (clausesE cs)))
    (hc : CDerivesAt Ξ Δ (kill Γ) (.pair r (clausesE cs))
      (.val (.tensor (retTy S A R) (clausesTy S R (Ξ n)))))
    (he : CDerivesAt Ξ Δ Γ M (.comp (CTy.effOf (Row.ofEff n (Ξ n) 0 ++ S) A))) :
    CDerivesAt Ξ Δ Γ ((handleK n (qsOf Ξ n) r cs).plug M) (.comp (CTy.effOf S R)) :=
  .effHandleV hAt (splitP_kill_left Γ) (kill_dead Γ).toP (.val ⟨_, hv⟩) hc hn0 hnS hlen he

/-- A closed value at `!U(A ⊸ C)`: `λx. M` over a context of dead slots. -/
theorem d_lamBang {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {M : Expr} {A : VTy} {C : CTy}
    (h : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
    CDerivesAt Ξ Δ Γ (.lam M) (.val (.bang (.thunk (.arr A C)))) :=
  .bangThunkV (dead_noLive hΓ) rfl (.lam h)

/-- **A closed function applied to a value**, as our instance writes `f V`: `V to x. f x`, `f`
typed at an arrow at the empty context. -/
theorem d_appClosed {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {W V : Expr} {T : VTy} {C : CTy}
    (hWc : closedAt 0 W = true) (hW : CDerivesAt Ξ Δ [] W (.comp (.arr T C)))
    (hV : CDerivesAt Ξ Δ Γ V (.val T)) : CDerivesAt Ξ Δ Γ (appE W V) (.comp C) := by
  unfold appE
  rw [shift_closedAt W 1 hWc (Nat.zero_le _)]
  exact .bind (deadSplit hΓ) (.ret hV)
    (.app (.right (deadSplit hΓ)) (hW.append_dead (Γ' := ⟨T, false⟩ :: Γ) (.cons hΓ))
      (.here hΓ.toP))

/-- A handler frame at a label, at the signature `E` the context declares at its name. -/
theorem d_handleL {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A R : VTy} (l : (orowAlg Ξ).Lab)
    {E : List (Qual × VTy × VTy)} (hE : Ξ l.1 = E) {r : Expr} {cs : List Expr} {M : Expr}
    (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ l.1) (hv : IsVal (.pair r (clausesE cs)))
    (hc : CDerivesAt Ξ Δ (kill Γ) (.pair r (clausesE cs))
      (.val (.tensor (retTy S A R) (clausesTy S R E))))
    (he : CDerivesAt Ξ Δ Γ M (.comp (CTy.effOf (Row.ofEff l.1 E 0 ++ S) A))) :
    CDerivesAt Ξ Δ Γ ((handleK l.1 (qsOf Ξ l.1) r cs).plug M) (.comp (CTy.effOf S R)) := by
  rw [← hE] at hc he
  exact d_handleK (Targets.rowAt_append (rowAt_rowOf l) hS) l.2.1 hnS l.2.2.2 hv hc he

/-- An abortive clause's type: `!U(A ⊸ F_Σ R)`. -/
theorem clauseTy_abortive {S : Row} {R A : VTy} {q : Qual} (hq : q ≠ .lin) :
    clauseTy S R (q, A, .zero) = .bang (.thunk (.arr A (CTy.effOf S R))) := by
  simp only [clauseTy]
  rw [if_pos (by cases q <;> simp_all [VTy.isZero])]

/-! ### Operations and callbacks -/

/-- A label's signature row, at the signature the context declares there, before the empty row. -/
theorem rowAt_ofEff_lab (l : (orowAlg Ξ).Lab) {E : List (Qual × VTy × VTy)} (hE : Ξ l.1 = E) :
    RowAt Ξ (Row.ofEff l.1 E 0 ++ []) := by
  rw [← hE]; exact rowAt_rowOf_append l (rowAt_nil Ξ)

/-- The raise of a label's abortive `1 ↠ 0` at its row. -/
theorem d_raiseLab {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) (l : (orowAlg Ξ).Lab) {q : Qual}
    (hl : Ξ l.1 = [(q, .unit, .zero)]) (hq : q ≠ .lin) (B : VTy) :
    CDerivesAt Ξ Δ Γ (raiseE (opArgE l.1 0 .unit))
      (.comp (CTy.effOf (Row.ofEff l.1 [(q, .unit, .zero)] 0 ++ []) B)) :=
  .effRaise (o := ⟨l.1, 0, q, .unit, .zero, .ret .unit⟩) (rowAt_ofEff_lab l hl) (by simp [Row.ofEff, Row.find])
    (by cases q <;> simp_all [OpSig.abort, VTy.isZero]) .unit (.unitI hΓ)

/-- The perform of a label's resuming `A ↠ B` at its row. -/
theorem d_performLab {Δ : LifeCtx} {Γ : Ctx VTy} (l : (orowAlg Ξ).Lab) {q : Qual} {A B : VTy}
    (hl : Ξ l.1 = [(q, A, B)]) (hB : B.isZero = false) {V : Expr}
    (hV : CDerivesAt Ξ Δ Γ V (.val A)) :
    CDerivesAt Ξ Δ Γ (performE (opArgE l.1 0 V))
      (.comp (CTy.effOf (Row.ofEff l.1 [(q, A, B)] 0 ++ []) B)) :=
  .effPerform (o := ⟨l.1, 0, q, A, B, .ret .unit⟩) (rowAt_ofEff_lab l hl) (by simp [Row.ofEff, Row.find])
    (by simp [OpSig.abort, hB]) hV

/-! ### The handlers the (E) programs share -/

/-- `toResult`'s handler: `return x ⇒ inl x`, `raise _ ⇒ inr ()`. -/
def toResultH : Expr := .pair (.lam (.inj₁ (.var 0))) (clausesE [.lam (.inj₂ .unit)])

theorem isVal_toResultH : IsVal toResultH := .pair .lam (.pair .lam .unit)

/-- **`toResult`'s handler** at an abortive operation `1 ↠ 0` of an affine or unrestricted
qualifier, answering `A ⊕ 1` at the row `S`. -/
theorem d_toResultH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (A : VTy) {q : Qual}
    (hq : q ≠ .lin) :
    CDerivesAt Ξ Δ Γ toResultH
      (.val (.tensor (retTy S A (.sum A .unit)) (clausesTy S (.sum A .unit) [(q, .unit, .zero)]))) := by
  refine .tensorI (deadSplit hΓ) (d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.sumI₁
    (.var (.here hΓ.toP)))))) (.tensorI (deadSplit hΓ) ?_ (.unitI hΓ.toP))
  rw [clauseTy_abortive hq]
  exact d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.sumI₂ (.unitI (.drop rfl hΓ.toP)))))

/-- The clause `op (_, k) ⇒ resume k ()`. -/
def resumeClE : Expr := .lam (.letpair (.var 0) (resumeE (.var 0) .unit))

/-- `resumer`'s handler: `return x ⇒ x`, `op (_, k) ⇒ resume k ()`. -/
def resumerH : Expr := .pair (.lam (.var 0)) (clausesE [resumeClE])

theorem isVal_resumerH : IsVal resumerH := .pair .lam (.pair .lam .unit)

/-- `k (inj₁ ()) y`, the resume of a linear or affine continuation `k` at the slot `1` and the
answer `y` at the slot `0`. -/
theorem d_kResume {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {R B : VTy} {q : Qual}
    (hq : q ≠ .unr) :
    CDerivesAt Ξ Δ (⟨B, true⟩ :: ⟨kTy S R q B, true⟩ :: Γ)
      (.app (.app (.var 1) (.inj₁ .unit)) (.var 0)) (.comp (CTy.effOf S R)) := by
  cases q with
  | lin =>
      exact .app (.right (.left (deadSplit hΓ)))
        (.proj₁ (.force (C := .amp (.arr B (CTy.effOf S R)) .top) (.there (.here hΓ.toP))))
        (.here (.cons hΓ.toP))
  | aff =>
      exact .app (.right (.left (deadSplit hΓ)))
        (.proj₁ (.force (C := .amp (.arr B (CTy.effOf S R)) (CTy.effOf S .unit))
          (.there (.here hΓ.toP))))
        (.here (.cons hΓ.toP))
  | unr => exact absurd rfl hq

/-- **The clause `op (_, k) ⇒ resume k ()`** at a resuming operation `A ↠ 1` of a linear or affine
qualifier, `A` persistent (the argument is dropped). -/
theorem d_resumeCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (R : VTy) {q : Qual}
    {A : VTy} (hq : q ≠ .unr) (hA : A.Persistent) :
    CDerivesAt Ξ Δ Γ resumeClE (.val (clauseTy S R (q, A, .unit))) := by
  rw [clauseTy_resuming rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .bind (.right (.left (.dead (deadSplit hΓ)))) (.ret (.unitI (.cons (.drop hA
    (.cons hΓ.toP))))) ?_
  exact d_kResume (Γ := ⟨A, false⟩ :: ⟨.tensor A (kTy S R q .unit), false⟩ :: Γ)
    (.cons (.cons hΓ)) hq

/-- **`resumer`'s handler** at a resuming operation `A ↠ 1`, answering `R` at the row `S`. -/
theorem d_resumerH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (R : VTy) {q : Qual}
    {A : VTy} (hq : q ≠ .unr) (hA : A.Persistent) :
    CDerivesAt Ξ Δ Γ resumerH (.val (.tensor (retTy S R R) (clausesTy S R [(q, A, .unit)]))) :=
  .tensorI (deadSplit hΓ) (d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.var (.here hΓ.toP)))))
    (.tensorI (deadSplit hΓ) (d_resumeCl hΓ S R hq hA) (.unitI hΓ.toP))

end Kernel

/-! ### Polymorphic function types -/

/-- The row variable a polymorphic function type binds. -/
abbrev ρ₀ : RVar := 0

/-- `F_{S ⊙ ρ} A`: the returner at the closed row `S` before the row variable `ρ₀`. -/
def effAt (S : Row) (A : OVTy) : OCTy := .effF (fun η => S ++ η ρ₀) A

/-- `U(∀ρ:any. C)`. -/
def polyTy (C : OCTy) : OVTy := .thunk (.allR ρ₀ anyCon C)

theorem polyTy_isPoly (C : OCTy) : (polyTy C).isPoly = true := rfl

/-- A closed type's instance does not read the row environment. -/
theorem den_ofV_any (A : VTy) (η η' : RowEnv) : (OVTy.ofV A).den η = (OVTy.ofV A).den η' := by
  rw [OVTy.den_ofV, OVTy.den_ofV]

section Poly
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **A closed λ-value Core types at every instance of `∀ρ:any. C`** (at every unr-free row tied to
the context) is typed at `J₁` at `U(∀ρ:any. C)`. -/
theorem derV_poly_J₁ {b : Expr} {C : OCTy} (hC : C.RFree) (hnr : C.NotRet)
    (hcl : closedAt 0 (Expr.lam b) = true)
    (h : ∀ (r : Row) (η : RowEnv), Row.NU r → RowAt Ξ r →
      CDerivesAt Ξ LifeCtx.empty [] (.lam b) (.comp (C.den (Function.update η ρ₀ r)))) :
    (𝕁).derV [] ⟨.lam b, .lam⟩ (polyTy C) := by
  refine ⟨[], by simp, fun _ h => absurd h List.not_mem_nil, .inr ⟨rfl, hC, hnr⟩,
    fun η _ _ σ _ => ?_⟩
  simp only [J1CoreAt, polyTy_isPoly, if_true]
  refine ⟨b, fillS_closed σ (.lam b) 0 hcl, fun h => absurd h (by simp [polyTy, OVTy.isBang]),
    fun C' hC' => ?_⟩
  obtain ⟨r, ⟨hr, -⟩, hrt, rfl⟩ := hC'
  exact h r η hr hrt

/-- A data type at our instance is no loop sum. -/
theorem not_isLoopSum_data {ε : ORow} {A : VTy} (hA : ∀ A₀ L, A ≠ .sum A₀ (.thunk L)) :
    ¬ IsLoopSum ((𝕁).F ε (OVTy.ofV A)) := by
  intro h
  obtain ⟨S, S₀, A₀, -, -, he⟩ := h (fun _ => [])
  have he' : CTy.effOf (orowRF.den Ξ ε (fun _ => [])) ((OVTy.ofV A).den (fun _ => [])) =
      CTy.effOf S (.sum A₀ (.thunk (CTy.loopEff S₀ A₀ .unit))) := he
  obtain ⟨-, hA'⟩ := effOf_inj he'
  rw [OVTy.den_ofV] at hA'
  exact hA _ _ hA'

/-- A closed program typed at `J₁` at a returner of a data type: the row context of its
derivation, and Core's tied kernel typing it at every tied environment that row context admits. -/
theorem der_core_J₁ {M : Expr} {ε : ORow} {A : VTy} (hA : ∀ A₀ L, A ≠ .sum A₀ (.thunk L))
    (h : (𝕁).der [] M ((𝕁).F ε (OVTy.ofV A))) :
    ((𝕁).F ε (OVTy.ofV A)).TiedAt Ξ ∧ ∃ Θ : RowCtx, (∀ p ∈ Θ, p.2 = anyCon) ∧
      ∀ η, Θ.Models η → EnvAt Ξ η →
        CDerivesAt Ξ LifeCtx.empty [] M (.comp (CTy.effOf (orowRF.den Ξ ε η) A)) := by
  obtain ⟨hT, ⟨Θ, hΘ, hd⟩ | ⟨-, -, -, hL, -⟩⟩ := h
  · refine ⟨hT, Θ, hΘ, fun η hη hηΞ => ?_⟩
    have h' := hd.2.2 η hη hηΞ (fun _ => none) (closingAt_none (fun s hs => absurd hs List.not_mem_nil))
    rw [fillS_none] at h'
    have : ((𝕁).F ε (OVTy.ofV A)).den η = CTy.effOf (orowRF.den Ξ ε η) A := by
      show CTy.effOf _ ((OVTy.ofV A).den η) = _
      rw [OVTy.den_ofV]; rfl
    rw [← this]
    exact h'
  · exact absurd hL (not_isLoopSum_data hA)

/-- The one slot of a polymorphic function type is a slot `J₁` reads. -/
theorem slots_polyTy {C : OCTy} (hC : C.RFree) (hnr : C.NotRet) :
    ∀ s ∈ liveCtx [polyTy C], s.ty.J1OK := by
  intro s hs
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
  rw [List.mem_singleton.mp ha]
  exact .inr ⟨rfl, hC, hnr⟩

/-- A closing of one live polymorphic slot fills it with a closed λ-value Core types at every
instance of its type, and fills nothing else. -/
theorem closingAt_one {Δ : LifeCtx} {A : OVTy} (hA : A.isPoly = true) {η : RowEnv}
    {σ : ℕ → Option Val} (hσ : ClosingAt Ξ Δ (liveCtx [A]) η σ) :
    ∃ W : Val, σ 0 = some W ∧ (∀ i, σ (i + 1) = none) ∧ closedAt 0 W.1 = true ∧
      ∀ C', A.PolyInstAt Ξ η C' → CDerivesAt Ξ Δ [] (.val W) (.comp C') := by
  have hP : PolyAt (liveCtx [A]) 0 ⟨A, true⟩ := ⟨rfl, rfl, hA⟩
  obtain ⟨W, hW⟩ : ∃ W, σ 0 = some W := by
    cases h : σ 0 with
    | none => exact absurd hP ((hσ 0).1.mp h _)
    | some W => exact ⟨W, rfl⟩
  obtain ⟨b, -, hcl, hty⟩ := (hσ 0).2 _ W hP hW
  refine ⟨W, hW, fun i => (hσ (i + 1)).1.mpr fun s hs' => ?_, hcl, hty⟩
  have hs := hs'.1
  simp [liveCtx] at hs

/-- The use `f (λ_. M)` of the slot `f` with `f` filled by `W` and `M` closed. -/
theorem fillS_callPoly {σ : ℕ → Option Val} {W : Val} (hW : σ 0 = some W) {M : Expr}
    (hM : closedAt 0 M = true) :
    fillS σ 0 (appE (.var 0) (.lam M)) = .app (.lam (.app W.1 (.var 0))) (.lam M) := by
  have hM1 : closedAt 1 M = true := closedAt_of_zero hM 1
  simp [appE, fillS, Expr.shift, hW, fillS_closed σ M 1 hM1]

/-- **The use `f (λ_. M)` of a polymorphic slot `f`** at `J₁`, at the row `ε`, the callback's body
at the row `ε'`: typed when each instance of `f`'s type at `ε`'s reading takes a callback at
`ε'`'s reading and answers at `ε`'s.  The callback is `[λ-dead]`'s (SPEC §26); `f`'s closing is
read at that instance. -/
theorem der_callPoly_J₁ (hΞ : Ξ.NU) {Cp : OCTy} (hCp : Cp.RFree) (hnr : Cp.NotRet) {ε ε' : ORow}
    {A B : VTy} (hA : ∀ A₀ L, A ≠ .sum A₀ (.thunk L))
    (hinst : ∀ η, Cp.den (Function.update η ρ₀ (orowRF.den Ξ ε η)) =
      .arr (.thunk (.arr .unit (CTy.effOf (orowRF.den Ξ ε' η) A))) (CTy.effOf (orowRF.den Ξ ε η) B))
    {M : Expr} (hM : (𝕁).der [] M ((𝕁).F ε' (OVTy.ofV A)))
    (hT : ((𝕁).F ε (OVTy.ofV B)).TiedAt Ξ) :
    (𝕁).der [polyTy Cp] (appE (.var 0) (.lam M)) ((𝕁).F ε (OVTy.ofV B)) := by
  obtain ⟨-, Θ, hΘ, hMc⟩ := der_core_J₁ hA hM
  refine ⟨hT, .inl ⟨Θ, hΘ, slots_polyTy hCp hnr, OVTy.rFree_ofV B, fun η hη hηΞ σ hσ => ?_⟩⟩
  obtain ⟨W, hW, -, hWcl, hWty⟩ := closingAt_one (polyTy_isPoly Cp) hσ
  have hMη := hMc η hη hηΞ
  have hMcl : closedAt 0 M = true := by
    simpa using closedAt_of_derives hMη.toCDerives
  obtain ⟨S, A', hS, hSt⟩ := hT η hηΞ
  have hS' : CTy.effOf (orowRF.den Ξ ε η) ((OVTy.ofV B).den η) = CTy.effOf S A' := hS
  obtain ⟨rfl, -⟩ := effOf_inj hS'
  have hWi := hWty _ ⟨orowRF.den Ξ ε η, ⟨rowNU_of_rowAt hΞ hSt, fun _ _ => trivial⟩, hSt, rfl⟩
  rw [hinst] at hWi
  show CDerivesAt Ξ LifeCtx.empty (octxStrip η (liveCtx [polyTy Cp]))
    (fillS σ 0 (appE (.var 0) (.lam M))) (.comp (CTy.effOf (orowRF.den Ξ ε η) ((OVTy.ofV B).den η)))
  rw [fillS_callPoly hW hMcl, octxStrip_live_cons_poly η (polyTy_isPoly Cp) [], OVTy.den_ofV]
  refine .bind (Γ₁ := [⟨.unit, false⟩]) (Γ₂ := [⟨.unit, false⟩]) (.dead .nil)
    (.ret (d_cbDead (.cons .nil) hMη)) ?_
  exact .app (.right (.dead .nil))
    (hWi.append_dead (Γ' := [⟨_, false⟩, ⟨.unit, false⟩]) (.cons (.cons .nil)))
    (.here (Ctx.Dead.cons .nil).toP)

end Poly

end Targets.Inst

end
