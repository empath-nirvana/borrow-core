import Frontend.Check.Elab
import Core.Tied
import Core.PinFundamental

/-!
# Frontend — Check — tied derivations  `[spec §19]`

The checker builds every derivation tied to its program's effect context (decision R,
`Core/Tied.lean`). `TiedAt s Δ Γ e j` is a `CDerivesAt Ξ` derivation at every effect context `Ξ`
at which the list `s` is (`SigsAt`), `s` holding the rows the derivation reads at `[perform]`,
`[raise]` and `[handle]`. Each rule below applies one `CDerivesAt` constructor (or `CDerivesAt`'s
`effThenA`, `effHandle`) at every such `Ξ`, and its list is the union of its premises' lists with
the row it reads; a constant reads no row, and its `CDerives` derivation is tied by
`CDerivesAt.ofEffFree`.

`checkMain` (`Program.lean`) decides that `main`'s list gives each operation one signature, of a
nonzero name, and no unrestricted operation answering `0` (`sigsOkB`); the program's effect context
is the one the list gives (`effCtxOf`), at which `main`'s derivation is `CDerivesAt`
(`sigsAt_effCtxOf`), and whose abortive operations are cancellable (`noUnrExn_effCtxOf`).
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives CDerivesAt CDerivesP Jdg EffCtx RowAt SigsAt OpAt Ctx.Banged
  CtxOutlives HasDtor dtorE dropE dtor_wf rowAt_of_sigsAt)

/-- **A derivation tied at every effect context at which the list `s` is**: `s` holds the rows the
derivation reads at `[perform]`, `[raise]` and `[handle]`.  `[spec §19]` -/
def TiedAt (s : CRow) (Δ : LifeCtx) (Γ : Ctx CVTy) (e : BoCa.Expr) (j : Jdg) : Prop :=
  ∀ Ξ : EffCtx, SigsAt Ξ s → CDerivesAt Ξ Δ Γ e j

/-! ### Lists of operations -/

theorem sigsAt_union_left {Ξ : EffCtx} {s₁ s₂ : CRow} (h : SigsAt Ξ (s₁ ∪ s₂)) : SigsAt Ξ s₁ :=
  fun o ho => h o (List.mem_union_iff.mpr (.inl ho))

theorem sigsAt_union_right {Ξ : EffCtx} {s₁ s₂ : CRow} (h : SigsAt Ξ (s₁ ∪ s₂)) : SigsAt Ξ s₂ :=
  fun o ho => h o (List.mem_union_iff.mpr (.inr ho))

/-- A row the list holds is tied. -/
theorem rowAt_of_union_left {Ξ : EffCtx} {S s : CRow} (h : SigsAt Ξ (S ∪ s)) : RowAt Ξ S :=
  rowAt_of_sigsAt (sigsAt_union_left h)

namespace TiedAt
variable {Δ : LifeCtx} {Γ : Ctx CVTy}

/-! ### The rules -/

theorem var {i : Nat} {A : CVTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ i A) :
    TiedAt [] Δ Γ (.var i) (.val A) := fun _ _ => .var h

theorem unitI (h : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TiedAt [] Δ Γ (.val BoCa.Val.unit) (.val .unit) := fun _ _ => .unitI h

theorem topI : TiedAt [] Δ Γ (.val BoCa.Val.unit) (.comp .top) := fun _ _ => .topI

theorem force {i : Nat} {C : CCTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ i (.thunk C)) :
    TiedAt [] Δ Γ (BoCa.Fig16.LogRel.Core.forceE C (.var i)) (.comp C) := fun _ _ => .force h

theorem tensorI {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {e₁ e₂ : BoCa.Expr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : TiedAt s₁ Δ Γ₁ e₁ (.val A))
    (h₂ : TiedAt s₂ Δ Γ₂ e₂ (.val B)) : TiedAt (s₁ ∪ s₂) Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) :=
  fun Ξ h => .tensorI hs (h₁ Ξ (sigsAt_union_left h)) (h₂ Ξ (sigsAt_union_right h))

theorem sumI₁ {s : CRow} {e : BoCa.Expr} {A B : CVTy} (h : TiedAt s Δ Γ e (.val A)) :
    TiedAt s Δ Γ (.inj₁ e) (.val (.sum A B)) := fun Ξ hΞ => .sumI₁ (h Ξ hΞ)

theorem sumI₂ {s : CRow} {e : BoCa.Expr} {A B : CVTy} (h : TiedAt s Δ Γ e (.val B)) :
    TiedAt s Δ Γ (.inj₂ e) (.val (.sum A B)) := fun Ξ hΞ => .sumI₂ (h Ξ hΞ)

theorem thunkF {s : CRow} {M : BoCa.Expr} {A : CVTy}
    (h : TiedAt s Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    TiedAt s Δ Γ (.val (BoCa.Val.lam M)) (.val (.thunk (.ret A))) := fun Ξ hΞ => .thunkF (h Ξ hΞ)

theorem thunkV {s : CRow} {N : BoCa.Expr} {C : CCTy} (hC : C.isRet = false)
    (h : TiedAt s Δ Γ (.val (BoCa.Val.lam N)) (.comp C)) :
    TiedAt s Δ Γ (.val (BoCa.Val.lam N)) (.val (.thunk C)) := fun Ξ hΞ => .thunkV hC (h Ξ hΞ)

theorem ret {s : CRow} {V : BoCa.Expr} {A : CVTy} (h : TiedAt s Δ Γ V (.val A)) :
    TiedAt s Δ Γ V (.comp (.ret A)) := fun Ξ hΞ => .ret (h Ξ hΞ)

theorem bind {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N : BoCa.Expr} {A : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hM : TiedAt s₁ Δ Γ₁ M (.comp (.ret A)))
    (hN : TiedAt s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
    TiedAt (s₁ ∪ s₂) Δ Γ (.app (.val (BoCa.Val.lam N)) M) (.comp C) :=
  fun Ξ h => .bind hs (hM Ξ (sigsAt_union_left h)) (hN Ξ (sigsAt_union_right h))

theorem lam {s : CRow} {M : BoCa.Expr} {A : CVTy} {C : CCTy}
    (h : TiedAt s Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
    TiedAt s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.arr A C)) := fun Ξ hΞ => .lam (h Ξ hΞ)

/-- `[λ-dead]`: `λx. M : 1 ⊸ F_Σ B`, `x`'s slot dead.  `[spec §26]` -/
theorem lamDead {s : CRow} {M : BoCa.Expr} {S : CRow} {B : CVTy}
    (h : TiedAt s Δ (⟨.unit, false⟩ :: Γ) M (.comp (effOf S B))) :
    TiedAt s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.arr .unit (effOf S B))) :=
  fun Ξ hΞ => .lamDead (h Ξ hΞ)

theorem app {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M : BoCa.Expr} {i : Nat} {A : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hM : TiedAt s Δ Γ₁ M (.comp (.arr A C)))
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₂ i A) : TiedAt s Δ Γ (.app M (.var i)) (.comp C) :=
  fun Ξ hΞ => .app hs (hM Ξ hΞ) hx

theorem withI {s₁ s₂ : CRow} {M N : BoCa.Expr} {C D : CCTy}
    (hM : TiedAt s₁ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) M (.comp C))
    (hN : TiedAt s₂ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) N (.comp D)) :
    TiedAt (s₁ ∪ s₂) Δ Γ (BoCa.Fig16.LogRel.Core.withPair M N) (.comp (.amp C D)) :=
  fun Ξ h => .withI (hM Ξ (sigsAt_union_left h)) (hN Ξ (sigsAt_union_right h))

theorem proj₁ {s : CRow} {M : BoCa.Expr} {C D : CCTy} (h : TiedAt s Δ Γ M (.comp (.amp C D))) :
    TiedAt s Δ Γ (.app M (.val (BoCa.Val.inj₁ BoCa.Val.unit))) (.comp C) :=
  fun Ξ hΞ => .proj₁ (h Ξ hΞ)

theorem proj₂ {s : CRow} {M : BoCa.Expr} {C D : CCTy} (h : TiedAt s Δ Γ M (.comp (.amp C D))) :
    TiedAt s Δ Γ (.app M (.val (BoCa.Val.inj₂ BoCa.Val.unit))) (.comp D) :=
  fun Ξ hΞ => .proj₂ (h Ξ hΞ)

theorem unitE {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {V M : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hV : TiedAt s₁ Δ Γ₁ V (.val .unit))
    (hM : TiedAt s₂ Δ Γ₂ M (.comp C)) : TiedAt (s₁ ∪ s₂) Δ Γ (.seq V M) (.comp C) :=
  fun Ξ h => .unitE hs (hV Ξ (sigsAt_union_left h)) (hM Ξ (sigsAt_union_right h))

theorem tensorE {s₁ s₂ : CRow} {Γp Γb : Ctx CVTy} {V M : BoCa.Expr} {A B : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γp Γb) (hV : TiedAt s₁ Δ Γp V (.val (.tensor A B)))
    (hM : TiedAt s₂ Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
    TiedAt (s₁ ∪ s₂) Δ Γ (.letpair V M) (.comp C) :=
  fun Ξ h => .tensorE hs (hV Ξ (sigsAt_union_left h)) (hM Ξ (sigsAt_union_right h))

theorem sumE {s₁ s₂ s₃ : CRow} {Γs Γb : Ctx CVTy} {V M₁ M₂ : BoCa.Expr} {A B : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γs Γb) (hV : TiedAt s₁ Δ Γs V (.val (.sum A B)))
    (h₁ : TiedAt s₂ Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
    (h₂ : TiedAt s₃ Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
    TiedAt (s₁ ∪ (s₂ ∪ s₃)) Δ Γ (.case V M₁ M₂) (.comp C) :=
  fun Ξ h => .sumE hs (hV Ξ (sigsAt_union_left h))
    (h₁ Ξ (sigsAt_union_left (sigsAt_union_right h)))
    (h₂ Ξ (sigsAt_union_right (sigsAt_union_right h)))

theorem zeroE {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {V : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hV : TiedAt s Δ Γ₁ V (.val .zero)) :
    TiedAt s Δ Γ (BoCa.Fig16.LogRel.Core.absurdE V) (.comp C) := fun Ξ hΞ => .zeroE hs (hV Ξ hΞ)

theorem allI {s : CRow} {x : LifeVar} {b : CLife} {M : BoCa.Expr} {S : CVTy} {C : CCTy}
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ BoCa.Fig16.LogRel.Core.VFree x s.ty)
    (h : TiedAt s (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
    TiedAt s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.all x b C)) :=
  fun Ξ hΞ => .allI hbx hΔx hΓx (h Ξ hΞ)

theorem allE {s : CRow} {M : BoCa.Expr} {x : LifeVar} {b a : CLife} {C : CCTy}
    (h : TiedAt s Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
    TiedAt s Δ Γ (.app M (.val BoCa.Val.unit)) (.comp (C.instLife x a)) :=
  fun Ξ hΞ => .allE (h Ξ hΞ) hlt

theorem bangThunkF {s : CRow} {M : BoCa.Expr} {A : CVTy} (hp : Ctx.Banged Γ)
    (h : TiedAt s Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    TiedAt s Δ Γ (.val (BoCa.Val.lam M)) (.val (.bang (.thunk (.ret A)))) :=
  fun Ξ hΞ => .bangThunkF hp (h Ξ hΞ)

theorem bangThunkV {s : CRow} {N : BoCa.Expr} {C : CCTy} (hp : Ctx.Banged Γ)
    (hC : C.isRet = false) (h : TiedAt s Δ Γ (.val (BoCa.Val.lam N)) (.comp C)) :
    TiedAt s Δ Γ (.val (BoCa.Val.lam N)) (.val (.bang (.thunk C))) :=
  fun Ξ hΞ => .bangThunkV hp hC (h Ξ hΞ)

theorem bangE {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedAt s Δ Γ e (.val (.bang A))) :
    TiedAt s Δ Γ e (.val A) := fun Ξ hΞ => .bangE (h Ξ hΞ)

theorem boxI {s : CRow} {e : BoCa.Expr} {a : CLife} {A : CVTy} (h : TiedAt s Δ Γ e (.val A))
    (hΓ : CtxOutlives Δ Γ a) : TiedAt s Δ Γ e (.val (.box a A)) := fun Ξ hΞ => .boxI (h Ξ hΞ) hΓ

theorem boxE {s : CRow} {e : BoCa.Expr} {a : CLife} {A : CVTy}
    (h : TiedAt s Δ Γ e (.val (.box a A))) : TiedAt s Δ Γ e (.val A) := fun Ξ hΞ => .boxE (h Ξ hΞ)

theorem immSub {s : CRow} {e : BoCa.Expr} {a b : CLife} {A : CVTy}
    (h : TiedAt s Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
    TiedAt s Δ Γ e (.val (.imm a A)) := fun Ξ hΞ => .immSub (h Ξ hΞ) hle

theorem mutSub {s : CRow} {e : BoCa.Expr} {a b : CLife} {A : CVTy}
    (h : TiedAt s Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
    TiedAt s Δ Γ e (.val (.mut a A)) := fun Ξ hΞ => .mutSub (h Ξ hΞ) hle

theorem lolliE {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {f a : BoCa.Expr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (ha : TiedAt s₁ Δ Γ₁ a (.val A))
    (hf : TiedAt s₂ Δ Γ₂ f (.val (.lolli A B))) : TiedAt (s₁ ∪ s₂) Δ Γ (.app f a) (.val B) :=
  fun Ξ h => .lolliE hs (ha Ξ (sigsAt_union_left h)) (hf Ξ (sigsAt_union_right h))

theorem allEV {s : CRow} {e : BoCa.Expr} {x : LifeVar} {b a : CLife} {A : CVTy}
    (h : TiedAt s Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
    TiedAt s Δ Γ (.app e (.val BoCa.Val.unit)) (.val (A.instLife x a)) :=
  fun Ξ hΞ => .allEV (h Ξ hΞ) hlt

theorem ofRet {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedAt s Δ Γ e (.comp (.ret A))) :
    TiedAt s Δ Γ e (.val A) := fun Ξ hΞ => .ofRet (h Ξ hΞ)

theorem roll {s : CRow} {e : BoCa.Expr} {A : CVTy} (hA : A.NoMut 0)
    (hc : (BoCa.Fig16.LogRel.Core.VTy.mu A).Cl 0)
    (h : TiedAt s Δ Γ e (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A))) :
    TiedAt s Δ Γ e (.val (.mu A)) := fun Ξ hΞ => .roll hA hc (h Ξ hΞ)

theorem unroll {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedAt s Δ Γ e (.val (.mu A))) :
    TiedAt s Δ Γ e (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) :=
  fun Ξ hΞ => .unroll (h Ξ hΞ)

theorem nuIn {s : CRow} {e : BoCa.Expr} {C : CCTy} (hC : C.NuOk)
    (h : TiedAt s Δ Γ e (.comp C.unroll)) : TiedAt s Δ Γ e (.comp (.nu C)) :=
  fun Ξ hΞ => .nuIn hC (h Ξ hΞ)

theorem nuOut {s : CRow} {e : BoCa.Expr} {C : CCTy} (hC : C.NuOk)
    (h : TiedAt s Δ Γ e (.comp (.nu C))) : TiedAt s Δ Γ e (.comp C.unroll) :=
  fun Ξ hΞ => .nuOut hC (h Ξ hΞ)

/-! ### The effect rules -/

theorem effSub {s : CRow} {e : BoCa.Expr} {S S' : CRow} {A : CVTy}
    (hle : BoCa.Fig16.LogRel.Core.RowLe S S') (h : TiedAt s Δ Γ e (.comp (effOf S A))) :
    TiedAt s Δ Γ e (.comp (effOf S' A)) := fun Ξ hΞ => .effSub hle (h Ξ hΞ)

/-- `[perform]` reads its row. -/
theorem effPerform {s : CRow} {V : BoCa.Expr} {S : CRow} {o : COpSig}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (hna : o.abort = false)
    (hac : o.rc = false) (h : TiedAt s Δ Γ V (.val o.A)) :
    TiedAt (S ∪ s) Δ Γ (BoCa.BoLo.performE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i V))
      (.comp (effOf S o.B)) :=
  fun Ξ hΞ => .effPerform (rowAt_of_union_left hΞ) hf hna hac (h Ξ (sigsAt_union_right hΞ))

/-- `[raise]` reads its row. -/
theorem effRaise {s : CRow} {V : BoCa.Expr} {S : CRow} {o : COpSig} {B : CVTy}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hrc : o.rc = false) (hd : o.A.OwnFree) (h : TiedAt s Δ Γ V (.val o.A)) :
    TiedAt (S ∪ s) Δ Γ (BoCa.BoLo.raiseE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i V))
      (.comp (effOf S B)) :=
  fun Ξ hΞ => .effRaise (rowAt_of_union_left hΞ) hf ha hrc hd (h Ξ (sigsAt_union_right hΞ))

theorem effLet {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N : BoCa.Expr} {A B : CVTy} {S : CRow}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Cancels → Γ₂.OwnFree)
    (hU : S.Unr → Ctx.Banged Γ₂) (hM : TiedAt s₁ Δ Γ₁ M (.comp (effOf S A)))
    (hN : TiedAt s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp (effOf S B))) :
    TiedAt (s₁ ∪ s₂) Δ Γ (.app (.val (BoCa.Val.lam N)) M) (.comp (effOf S B)) :=
  fun Ξ h => .effLet hs hW hU (hM Ξ (sigsAt_union_left h)) (hN Ξ (sigsAt_union_right h))

theorem effThenA {s₁ s₂ s₃ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N D : BoCa.Expr} {A B : CVTy} {S : CRow}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq)
    (hU : S.UnrD → Ctx.Banged Γ₂) (hM : TiedAt s₁ Δ Γ₁ M (.comp (effOf S A)))
    (hN : TiedAt s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp (effOf S B)))
    (hD : TiedAt s₃ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    TiedAt (s₁ ∪ (s₂ ∪ s₃)) Δ Γ (BoCa.Fig16.LogRel.Core.thenE N D M) (.comp (effOf S B)) :=
  fun Ξ h => CDerivesAt.effThenA hs hNZ hUq hU (hM Ξ (sigsAt_union_left h))
    (hN Ξ (sigsAt_union_left (sigsAt_union_right h)))
    (hD Ξ (sigsAt_union_right (sigsAt_union_right h)))

/-- `[handle]` reads its handled row. -/
theorem effHandle {s : CRow} {Γ₁ Γ₂ Γr Γc : Ctx CVTy} {e : BoCa.Expr} {S : CRow}
    {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy} {ir ic : Nat}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hs₁ : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ₁ Γr Γc)
    (hr : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γr ir (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hc : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γc ic (BoCa.Fig16.LogRel.Core.clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (he : TiedAt s Δ Γ₂ e (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A))) :
    TiedAt ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ s) Δ Γ
      (BoCa.Fig16.LogRel.Core.hndTerm n (E.map Prod.fst) ir ic e) (.comp (effOf S R)) :=
  fun Ξ h => CDerivesAt.effHandle (rowAt_of_union_left h) hs hs₁ hr hc hn0 hnS hlen hdv
    (he Ξ (sigsAt_union_right h))

/-- BOXED-κ reads its handled row.  `[spec §28]` -/
theorem effHandleB {s : CRow} {Γ₁ Γ₂ Γr Γc : Ctx CVTy} {e : BoCa.Expr} {S : CRow}
    {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy} {ir ic : Nat} {d : CLife}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hs₁ : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ₁ Γr Γc)
    (hr : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γr ir (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hc : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γc ic (BoCa.Fig16.LogRel.Core.clausesTyB S R d E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (he : TiedAt s Δ Γ₂ e (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (hΓd : CtxOutlives Δ Γ₂ d)
    (hSd : BoCa.Fig16.LogRel.Core.Row.AnsOutlives Δ d (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S)) :
    TiedAt ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ s) Δ Γ
      (BoCa.Fig16.LogRel.Core.hndTerm n (E.map Prod.fst) ir ic e) (.comp (effOf S R)) :=
  fun Ξ h => CDerivesAt.effHandleB (rowAt_of_union_left h) hs hs₁ hr hc hn0 hnS hlen hdv
    (he Ξ (sigsAt_union_right h)) hΓd hSd

/-! ### Derived forms -/

/-- A derivation of a term with no operation reads no row. -/
theorem ofCDerives {e : BoCa.Expr} {j : Jdg} (h : CDerives Δ Γ e j) (he : e.effFree = true) :
    TiedAt [] Δ Γ e j := fun _ _ => CDerivesAt.ofEffFree h he

/-- `dtorE T xᵢ; e`, as `drop_derives`: `unitE` over the destructor applied to the slot.
`[spec §12]` -/
theorem drop {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {i : Nat} {T : CVTy} {e : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₁ i T) (hT : HasDtor T)
    (hE : (dtorE T).effFree = true) (h : TiedAt s Δ Γ₂ e (.comp C)) :
    TiedAt s Δ Γ (dropE T i e) (.comp C) :=
  fun Ξ hΞ => .unitE hs (.lolliE (BoCa.Fig16.LogRel.Core.split_kill' Γ₁).toP (.var hx)
    (CDerivesAt.ofEffFree (dtor_wf hT (BoCa.Fig16.LogRel.Core.kill_dead Γ₁)) hE)) (h Ξ hΞ)

end TiedAt

/-! ### Derivations the checker returns  `[spec §19, §29]`

The checker returns one derivation per term, and it is of `CDerives` exactly when no relaxed rule
(SPEC §29) was used. `TiedDer p s Δ Γ e j` is a `CDerivesP` derivation, and, when the list `p` of
the relaxed rules used is empty, a tied `CDerivesAt` one (`TiedAt`). Each rule below applies the
constructor of both, and its `p` is the concatenation of its premises'. -/

/-- A use of a relaxed rule (SPEC §29): the rule and where in the program it is used. -/
structure Pin where
  rule : String
  line : Nat
  col : Nat
  deriving DecidableEq, Repr

/-- The relaxed rules a derivation uses. -/
abbrev Pins := List Pin

/-- **A derivation the checker returns**: of `CDerivesP`, and tied (`TiedAt`) when it uses no
relaxed rule.  `[spec §19, §29]` -/
def TiedDer (p : Pins) (s : CRow) (Δ : LifeCtx) (Γ : Ctx CVTy) (e : BoCa.Expr) (j : Jdg) : Prop :=
  (p = [] → TiedAt s Δ Γ e j) ∧ CDerivesP Δ Γ e j

theorem nilL {a b : Pins} (h : a ++ b = []) : a = [] := (List.append_eq_nil_iff.1 h).1

theorem nilR {a b : Pins} (h : a ++ b = []) : b = [] := (List.append_eq_nil_iff.1 h).2

namespace TiedDer
variable {Δ : LifeCtx} {Γ : Ctx CVTy}

theorem var {i : Nat} {A : CVTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ i A) :
    TiedDer [] [] Δ Γ (.var i) (.val A) :=
  ⟨fun _ => TiedAt.var h,
    CDerivesP.var h⟩

theorem unitI (h : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TiedDer [] [] Δ Γ (.val BoCa.Val.unit) (.val .unit) :=
  ⟨fun _ => TiedAt.unitI h,
    CDerivesP.unitI h⟩

theorem topI : TiedDer [] [] Δ Γ (.val BoCa.Val.unit) (.comp .top) :=
  ⟨fun _ => TiedAt.topI ,
    CDerivesP.topI ⟩

theorem force {i : Nat} {C : CCTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ i (.thunk C)) :
    TiedDer [] [] Δ Γ (BoCa.Fig16.LogRel.Core.forceE C (.var i)) (.comp C) :=
  ⟨fun _ => TiedAt.force h,
    CDerivesP.force h⟩

theorem tensorI {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {e₁ e₂ : BoCa.Expr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : TiedDer p₁ s₁ Δ Γ₁ e₁ (.val A))
    (h₂ : TiedDer p₂ s₂ Δ Γ₂ e₂ (.val B)) : TiedDer (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) :=
  ⟨fun hn => TiedAt.tensorI hs (h₁.1 (nilL hn)) (h₂.1 (nilR hn)),
    CDerivesP.tensorI hs h₁.2 h₂.2⟩

theorem sumI₁ {p : Pins} {s : CRow} {e : BoCa.Expr} {A B : CVTy} (h : TiedDer p s Δ Γ e (.val A)) :
    TiedDer p s Δ Γ (.inj₁ e) (.val (.sum A B)) :=
  ⟨fun hn => TiedAt.sumI₁ (h.1 hn),
    CDerivesP.sumI₁ h.2⟩

theorem sumI₂ {p : Pins} {s : CRow} {e : BoCa.Expr} {A B : CVTy} (h : TiedDer p s Δ Γ e (.val B)) :
    TiedDer p s Δ Γ (.inj₂ e) (.val (.sum A B)) :=
  ⟨fun hn => TiedAt.sumI₂ (h.1 hn),
    CDerivesP.sumI₂ h.2⟩

theorem thunkF {p : Pins} {s : CRow} {M : BoCa.Expr} {A : CVTy}
    (h : TiedDer p s Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    TiedDer p s Δ Γ (.val (BoCa.Val.lam M)) (.val (.thunk (.ret A))) :=
  ⟨fun hn => TiedAt.thunkF (h.1 hn),
    CDerivesP.thunkF h.2⟩

theorem thunkV {p : Pins} {s : CRow} {N : BoCa.Expr} {C : CCTy} (hC : C.isRet = false)
    (h : TiedDer p s Δ Γ (.val (BoCa.Val.lam N)) (.comp C)) :
    TiedDer p s Δ Γ (.val (BoCa.Val.lam N)) (.val (.thunk C)) :=
  ⟨fun hn => TiedAt.thunkV hC (h.1 hn),
    CDerivesP.thunkV hC h.2⟩

theorem ret {p : Pins} {s : CRow} {V : BoCa.Expr} {A : CVTy} (h : TiedDer p s Δ Γ V (.val A)) :
    TiedDer p s Δ Γ V (.comp (.ret A)) :=
  ⟨fun hn => TiedAt.ret (h.1 hn),
    CDerivesP.ret h.2⟩

theorem bind {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N : BoCa.Expr} {A : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hM : TiedDer p₁ s₁ Δ Γ₁ M (.comp (.ret A)))
    (hN : TiedDer p₂ s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
    TiedDer (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.app (.val (BoCa.Val.lam N)) M) (.comp C) :=
  ⟨fun hn => TiedAt.bind hs (hM.1 (nilL hn)) (hN.1 (nilR hn)),
    CDerivesP.bind hs hM.2 hN.2⟩

theorem lam {p : Pins} {s : CRow} {M : BoCa.Expr} {A : CVTy} {C : CCTy}
    (h : TiedDer p s Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
    TiedDer p s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.arr A C)) :=
  ⟨fun hn => TiedAt.lam (h.1 hn),
    CDerivesP.lam h.2⟩

/-- `[λ-dead]`: `λx. M : 1 ⊸ F_Σ B`, `x`'s slot dead.  `[spec §26]` -/
theorem lamDead {p : Pins} {s : CRow} {M : BoCa.Expr} {S : CRow} {B : CVTy}
    (h : TiedDer p s Δ (⟨.unit, false⟩ :: Γ) M (.comp (effOf S B))) :
    TiedDer p s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.arr .unit (effOf S B))) :=
  ⟨fun hn => TiedAt.lamDead (h.1 hn),
    CDerivesP.lamDead h.2⟩

theorem app {p : Pins} {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M : BoCa.Expr} {i : Nat} {A : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hM : TiedDer p s Δ Γ₁ M (.comp (.arr A C)))
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₂ i A) : TiedDer p s Δ Γ (.app M (.var i)) (.comp C) :=
  ⟨fun hn => TiedAt.app hs (hM.1 hn) hx,
    CDerivesP.app hs hM.2 hx⟩

theorem withI {p₁ p₂ : Pins} {s₁ s₂ : CRow} {M N : BoCa.Expr} {C D : CCTy}
    (hM : TiedDer p₁ s₁ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) M (.comp C))
    (hN : TiedDer p₂ s₂ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) N (.comp D)) :
    TiedDer (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (BoCa.Fig16.LogRel.Core.withPair M N) (.comp (.amp C D)) :=
  ⟨fun hn => TiedAt.withI (hM.1 (nilL hn)) (hN.1 (nilR hn)),
    CDerivesP.withI hM.2 hN.2⟩

theorem proj₁ {p : Pins} {s : CRow} {M : BoCa.Expr} {C D : CCTy} (h : TiedDer p s Δ Γ M (.comp (.amp C D))) :
    TiedDer p s Δ Γ (.app M (.val (BoCa.Val.inj₁ BoCa.Val.unit))) (.comp C) :=
  ⟨fun hn => TiedAt.proj₁ (h.1 hn),
    CDerivesP.proj₁ h.2⟩

theorem proj₂ {p : Pins} {s : CRow} {M : BoCa.Expr} {C D : CCTy} (h : TiedDer p s Δ Γ M (.comp (.amp C D))) :
    TiedDer p s Δ Γ (.app M (.val (BoCa.Val.inj₂ BoCa.Val.unit))) (.comp D) :=
  ⟨fun hn => TiedAt.proj₂ (h.1 hn),
    CDerivesP.proj₂ h.2⟩

theorem unitE {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {V M : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hV : TiedDer p₁ s₁ Δ Γ₁ V (.val .unit))
    (hM : TiedDer p₂ s₂ Δ Γ₂ M (.comp C)) : TiedDer (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.seq V M) (.comp C) :=
  ⟨fun hn => TiedAt.unitE hs (hV.1 (nilL hn)) (hM.1 (nilR hn)),
    CDerivesP.unitE hs hV.2 hM.2⟩

theorem tensorE {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γp Γb : Ctx CVTy} {V M : BoCa.Expr} {A B : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γp Γb) (hV : TiedDer p₁ s₁ Δ Γp V (.val (.tensor A B)))
    (hM : TiedDer p₂ s₂ Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
    TiedDer (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.letpair V M) (.comp C) :=
  ⟨fun hn => TiedAt.tensorE hs (hV.1 (nilL hn)) (hM.1 (nilR hn)),
    CDerivesP.tensorE hs hV.2 hM.2⟩

theorem sumE {p₁ p₂ p₃ : Pins} {s₁ s₂ s₃ : CRow} {Γs Γb : Ctx CVTy} {V M₁ M₂ : BoCa.Expr} {A B : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γs Γb) (hV : TiedDer p₁ s₁ Δ Γs V (.val (.sum A B)))
    (h₁ : TiedDer p₂ s₂ Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
    (h₂ : TiedDer p₃ s₃ Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
    TiedDer (p₁ ++ (p₂ ++ p₃)) (s₁ ∪ (s₂ ∪ s₃)) Δ Γ (.case V M₁ M₂) (.comp C) :=
  ⟨fun hn => TiedAt.sumE hs (hV.1 (nilL hn)) (h₁.1 (nilL (nilR hn))) (h₂.1 (nilR (nilR hn))),
    CDerivesP.sumE hs hV.2 h₁.2 h₂.2⟩

theorem zeroE {p : Pins} {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {V : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hV : TiedDer p s Δ Γ₁ V (.val .zero)) :
    TiedDer p s Δ Γ (BoCa.Fig16.LogRel.Core.absurdE V) (.comp C) :=
  ⟨fun hn => TiedAt.zeroE hs (hV.1 hn),
    CDerivesP.zeroE hs hV.2⟩

theorem allI {p : Pins} {s : CRow} {x : LifeVar} {b : CLife} {M : BoCa.Expr} {S : CVTy} {C : CCTy}
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ BoCa.Fig16.LogRel.Core.VFree x s.ty)
    (h : TiedDer p s (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
    TiedDer p s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.all x b C)) :=
  ⟨fun hn => TiedAt.allI hbx hΔx hΓx (h.1 hn),
    CDerivesP.allI hbx hΔx hΓx h.2⟩

theorem allE {p : Pins} {s : CRow} {M : BoCa.Expr} {x : LifeVar} {b a : CLife} {C : CCTy}
    (h : TiedDer p s Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
    TiedDer p s Δ Γ (.app M (.val BoCa.Val.unit)) (.comp (C.instLife x a)) :=
  ⟨fun hn => TiedAt.allE (h.1 hn) hlt,
    CDerivesP.allE h.2 hlt⟩

theorem bangThunkF {p : Pins} {s : CRow} {M : BoCa.Expr} {A : CVTy} (hp : Ctx.Banged Γ)
    (h : TiedDer p s Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    TiedDer p s Δ Γ (.val (BoCa.Val.lam M)) (.val (.bang (.thunk (.ret A)))) :=
  ⟨fun hn => TiedAt.bangThunkF hp (h.1 hn),
    CDerivesP.bangThunkF hp h.2⟩

theorem bangThunkV {p : Pins} {s : CRow} {N : BoCa.Expr} {C : CCTy} (hp : Ctx.Banged Γ)
    (hC : C.isRet = false) (h : TiedDer p s Δ Γ (.val (BoCa.Val.lam N)) (.comp C)) :
    TiedDer p s Δ Γ (.val (BoCa.Val.lam N)) (.val (.bang (.thunk C))) :=
  ⟨fun hn => TiedAt.bangThunkV hp hC (h.1 hn),
    CDerivesP.bangThunkV hp hC h.2⟩

theorem bangE {p : Pins} {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedDer p s Δ Γ e (.val (.bang A))) :
    TiedDer p s Δ Γ e (.val A) :=
  ⟨fun hn => TiedAt.bangE (h.1 hn),
    CDerivesP.bangE h.2⟩

theorem boxI {p : Pins} {s : CRow} {e : BoCa.Expr} {a : CLife} {A : CVTy} (h : TiedDer p s Δ Γ e (.val A))
    (hΓ : CtxOutlives Δ Γ a) : TiedDer p s Δ Γ e (.val (.box a A)) :=
  ⟨fun hn => TiedAt.boxI (h.1 hn) hΓ,
    CDerivesP.boxI h.2 hΓ⟩

theorem boxE {p : Pins} {s : CRow} {e : BoCa.Expr} {a : CLife} {A : CVTy}
    (h : TiedDer p s Δ Γ e (.val (.box a A))) : TiedDer p s Δ Γ e (.val A) :=
  ⟨fun hn => TiedAt.boxE (h.1 hn),
    CDerivesP.boxE h.2⟩

theorem immSub {p : Pins} {s : CRow} {e : BoCa.Expr} {a b : CLife} {A : CVTy}
    (h : TiedDer p s Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
    TiedDer p s Δ Γ e (.val (.imm a A)) :=
  ⟨fun hn => TiedAt.immSub (h.1 hn) hle,
    CDerivesP.immSub h.2 hle⟩

theorem mutSub {p : Pins} {s : CRow} {e : BoCa.Expr} {a b : CLife} {A : CVTy}
    (h : TiedDer p s Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
    TiedDer p s Δ Γ e (.val (.mut a A)) :=
  ⟨fun hn => TiedAt.mutSub (h.1 hn) hle,
    CDerivesP.mutSub h.2 hle⟩

theorem lolliE {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {f a : BoCa.Expr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (ha : TiedDer p₁ s₁ Δ Γ₁ a (.val A))
    (hf : TiedDer p₂ s₂ Δ Γ₂ f (.val (.lolli A B))) : TiedDer (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.app f a) (.val B) :=
  ⟨fun hn => TiedAt.lolliE hs (ha.1 (nilL hn)) (hf.1 (nilR hn)),
    CDerivesP.lolliE hs ha.2 hf.2⟩

theorem allEV {p : Pins} {s : CRow} {e : BoCa.Expr} {x : LifeVar} {b a : CLife} {A : CVTy}
    (h : TiedDer p s Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
    TiedDer p s Δ Γ (.app e (.val BoCa.Val.unit)) (.val (A.instLife x a)) :=
  ⟨fun hn => TiedAt.allEV (h.1 hn) hlt,
    CDerivesP.allEV h.2 hlt⟩

theorem ofRet {p : Pins} {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedDer p s Δ Γ e (.comp (.ret A))) :
    TiedDer p s Δ Γ e (.val A) :=
  ⟨fun hn => TiedAt.ofRet (h.1 hn),
    CDerivesP.ofRet h.2⟩

theorem roll {p : Pins} {s : CRow} {e : BoCa.Expr} {A : CVTy} (hA : A.NoMut 0)
    (hc : (BoCa.Fig16.LogRel.Core.VTy.mu A).Cl 0)
    (h : TiedDer p s Δ Γ e (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A))) :
    TiedDer p s Δ Γ e (.val (.mu A)) :=
  ⟨fun hn => TiedAt.roll hA hc (h.1 hn),
    CDerivesP.roll hA hc h.2⟩

theorem unroll {p : Pins} {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedDer p s Δ Γ e (.val (.mu A))) :
    TiedDer p s Δ Γ e (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) :=
  ⟨fun hn => TiedAt.unroll (h.1 hn),
    CDerivesP.unroll h.2⟩

theorem nuIn {p : Pins} {s : CRow} {e : BoCa.Expr} {C : CCTy} (hC : C.NuOk)
    (h : TiedDer p s Δ Γ e (.comp C.unroll)) : TiedDer p s Δ Γ e (.comp (.nu C)) :=
  ⟨fun hn => TiedAt.nuIn hC (h.1 hn),
    CDerivesP.nuIn hC h.2⟩

theorem nuOut {p : Pins} {s : CRow} {e : BoCa.Expr} {C : CCTy} (hC : C.NuOk)
    (h : TiedDer p s Δ Γ e (.comp (.nu C))) : TiedDer p s Δ Γ e (.comp C.unroll) :=
  ⟨fun hn => TiedAt.nuOut hC (h.1 hn),
    CDerivesP.nuOut hC h.2⟩

theorem effSub {p : Pins} {s : CRow} {e : BoCa.Expr} {S S' : CRow} {A : CVTy}
    (hle : BoCa.Fig16.LogRel.Core.RowLe S S') (h : TiedDer p s Δ Γ e (.comp (effOf S A))) :
    TiedDer p s Δ Γ e (.comp (effOf S' A)) :=
  ⟨fun hn => TiedAt.effSub hle (h.1 hn),
    CDerivesP.effSub hle h.2⟩

/-- `[perform]` reads its row. -/
theorem effPerform {p : Pins} {s : CRow} {V : BoCa.Expr} {S : CRow} {o : COpSig}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (hna : o.abort = false)
    (hac : o.rc = false) (h : TiedDer p s Δ Γ V (.val o.A)) :
    TiedDer p (S ∪ s) Δ Γ (BoCa.BoLo.performE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i V))
      (.comp (effOf S o.B)) :=
  ⟨fun hn => TiedAt.effPerform hf hna hac (h.1 hn),
    CDerivesP.effPerform hf hna hac h.2⟩

/-- `[raise]` reads its row. -/
theorem effRaise {p : Pins} {s : CRow} {V : BoCa.Expr} {S : CRow} {o : COpSig} {B : CVTy}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hrc : o.rc = false) (hd : o.A.OwnFree) (h : TiedDer p s Δ Γ V (.val o.A)) :
    TiedDer p (S ∪ s) Δ Γ (BoCa.BoLo.raiseE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i V))
      (.comp (effOf S B)) :=
  ⟨fun hn => TiedAt.effRaise hf ha hrc hd (h.1 hn),
    CDerivesP.effRaise hf ha hrc hd h.2⟩

theorem effLet {p₁ p₂ : Pins} {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N : BoCa.Expr} {A B : CVTy} {S : CRow}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Cancels → Γ₂.OwnFree)
    (hU : S.Unr → Ctx.Banged Γ₂) (hM : TiedDer p₁ s₁ Δ Γ₁ M (.comp (effOf S A)))
    (hN : TiedDer p₂ s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp (effOf S B))) :
    TiedDer (p₁ ++ p₂) (s₁ ∪ s₂) Δ Γ (.app (.val (BoCa.Val.lam N)) M) (.comp (effOf S B)) :=
  ⟨fun hn => TiedAt.effLet hs hW hU (hM.1 (nilL hn)) (hN.1 (nilR hn)),
    CDerivesP.effLet hs hW hU hM.2 hN.2⟩

theorem effThenA {p₁ p₂ p₃ : Pins} {s₁ s₂ s₃ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N D : BoCa.Expr} {A B : CVTy} {S : CRow}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq)
    (hU : S.UnrD → Ctx.Banged Γ₂) (hM : TiedDer p₁ s₁ Δ Γ₁ M (.comp (effOf S A)))
    (hN : TiedDer p₂ s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp (effOf S B)))
    (hD : TiedDer p₃ s₃ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    TiedDer (p₁ ++ (p₂ ++ p₃)) (s₁ ∪ (s₂ ∪ s₃)) Δ Γ (BoCa.Fig16.LogRel.Core.thenE N D M) (.comp (effOf S B)) :=
  ⟨fun hn => TiedAt.effThenA hs hNZ hUq hU (hM.1 (nilL hn)) (hN.1 (nilL (nilR hn))) (hD.1 (nilR (nilR hn))),
    CDerivesP.effThenA hs hNZ hUq hU hM.2 hN.2 hD.2⟩

/-- `[handle]` reads its handled row. -/
theorem effHandle {p : Pins} {s : CRow} {Γ₁ Γ₂ Γr Γc : Ctx CVTy} {e : BoCa.Expr} {S : CRow}
    {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy} {ir ic : Nat}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hs₁ : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ₁ Γr Γc)
    (hr : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γr ir (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hc : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γc ic (BoCa.Fig16.LogRel.Core.clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (he : TiedDer p s Δ Γ₂ e (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A))) :
    TiedDer p ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ s) Δ Γ
      (BoCa.Fig16.LogRel.Core.hndTerm n (E.map Prod.fst) ir ic e) (.comp (effOf S R)) :=
  ⟨fun hn => TiedAt.effHandle hs hs₁ hr hc hn0 hnS hlen hdv (he.1 hn),
    CDerivesP.effHandle hs hs₁ hr hc hn0 hnS hlen hdv he.2⟩

/-- BOXED-κ reads its handled row.  `[spec §28]` -/
theorem effHandleB {p : Pins} {s : CRow} {Γ₁ Γ₂ Γr Γc : Ctx CVTy} {e : BoCa.Expr} {S : CRow}
    {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy} {ir ic : Nat} {d : CLife}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hs₁ : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ₁ Γr Γc)
    (hr : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γr ir (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hc : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γc ic (BoCa.Fig16.LogRel.Core.clausesTyB S R d E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (he : TiedDer p s Δ Γ₂ e (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (hΓd : CtxOutlives Δ Γ₂ d)
    (hSd : BoCa.Fig16.LogRel.Core.Row.AnsOutlives Δ d (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S)) :
    TiedDer p ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ s) Δ Γ
      (BoCa.Fig16.LogRel.Core.hndTerm n (E.map Prod.fst) ir ic e) (.comp (effOf S R)) := by
  refine ⟨fun hn => TiedAt.effHandleB hs hs₁ hr hc hn0 hnS hlen hdv (he.1 hn) hΓd hSd, ?_⟩
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleVB hs
    (hs₁.deadP (hr.deadP (BoCa.Fig16.LogRel.Core.retTy_persistent S A R))
      (hc.deadP (BoCa.Fig16.LogRel.Core.clausesTyB_persistent S R d E
        BoCa.Fig16.LogRel.Core.finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he.2
    hΓd hSd

/-- A derivation of a term with no operation reads no row and uses no relaxed rule. -/
theorem ofCDerives {e : BoCa.Expr} {j : Jdg} (h : CDerives Δ Γ e j) (he : e.effFree = true) :
    TiedDer [] [] Δ Γ e j := ⟨fun _ => TiedAt.ofCDerives h he, CDerivesP.ofC h⟩

/-- `dtorE T xᵢ; e`, as `drop_derives`.  `[spec §12]` -/
theorem drop {p : Pins} {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {i : Nat} {T : CVTy} {e : BoCa.Expr}
    {C : CCTy} (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₁ i T) (hT : HasDtor T)
    (hE : (dtorE T).effFree = true) (h : TiedDer p s Δ Γ₂ e (.comp C)) :
    TiedDer p s Δ Γ (dropE T i e) (.comp C) :=
  ⟨fun hn => TiedAt.drop hs hx hT hE (h.1 hn),
    .unitE hs (.lolliE (BoCa.Fig16.LogRel.Core.split_kill' Γ₁).toP (.var hx)
      (CDerivesP.ofC (dtor_wf hT (BoCa.Fig16.LogRel.Core.kill_dead Γ₁)))) h.2⟩

end TiedDer

/-- `⇓σ`, as `shortenE_wf`, at a borrow former `M` whose `⊑` rule is `sub`: a family moved to a
shorter lifetime, leaf by leaf.  `[spec §5]` -/
theorem shortenE_wfAt (M : CLife → CVTy → CVTy)
    (sub : ∀ {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx CVTy} {e : BoCa.Expr} {a b : CLife} {A : CVTy},
      CDerivesAt Ξ Δ Γ e (.val (M b A)) → Δ.EntailsLe a b → CDerivesAt Ξ Δ Γ e (.val (M a A))) :
    ∀ {σ : CShape} {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx CVTy} {e : BoCa.Expr} {a b : CLife},
    CDerivesAt Ξ Δ Γ e (.val (σ.famTy M b)) → Δ.EntailsLe a b →
    CDerivesAt Ξ Δ Γ (BoCa.Fig16.LogRel.Core.shortenE σ e) (.val (σ.famTy M a))
  | .leaf _, _, _, _, _, _, _, h, hle => sub h hle
  | .node s₁ s₂, _, _, Γ, _, _, _, h, hle =>
      .ofRet (.tensorE (BoCa.Fig16.LogRel.Core.split_kill' Γ).toP h (.ret (.tensorI
        (.right (.left (BoCa.Fig16.LogRel.Core.deadSplit (BoCa.Fig16.LogRel.Core.kill_dead Γ))))
        (shortenE_wfAt M sub (σ := s₁)
          (.var (.there (.here (BoCa.Fig16.LogRel.Core.kill_dead Γ)))) hle)
        (shortenE_wfAt M sub (σ := s₂)
          (.var (.here (.cons (BoCa.Fig16.LogRel.Core.kill_dead Γ)))) hle))))

/-- `⇓σ` in `CDerivesP`, as `shortenE_wfAt`.  `[spec §5, §29]` -/
theorem shortenE_wfP (M : CLife → CVTy → CVTy)
    (sub : ∀ {Δ : LifeCtx} {Γ : Ctx CVTy} {e : BoCa.Expr} {a b : CLife} {A : CVTy},
      CDerivesP Δ Γ e (.val (M b A)) → Δ.EntailsLe a b → CDerivesP Δ Γ e (.val (M a A))) :
    ∀ {σ : CShape} {Δ : LifeCtx} {Γ : Ctx CVTy} {e : BoCa.Expr} {a b : CLife},
    CDerivesP Δ Γ e (.val (σ.famTy M b)) → Δ.EntailsLe a b →
    CDerivesP Δ Γ (BoCa.Fig16.LogRel.Core.shortenE σ e) (.val (σ.famTy M a))
  | .leaf _, _, _, _, _, _, h, hle => sub h hle
  | .node s₁ s₂, _, Γ, _, _, _, h, hle =>
      .ofRet (.tensorE (BoCa.Fig16.LogRel.Core.split_kill' Γ).toP h (.ret (.tensorI
        (.right (.left (BoCa.Fig16.LogRel.Core.deadSplit (BoCa.Fig16.LogRel.Core.kill_dead Γ))))
        (shortenE_wfP M sub (σ := s₁)
          (.var (.there (.here (BoCa.Fig16.LogRel.Core.kill_dead Γ)))) hle)
        (shortenE_wfP M sub (σ := s₂)
          (.var (.here (.cons (BoCa.Fig16.LogRel.Core.kill_dead Γ)))) hle))))

/-! ### The program's effect context -/

/-- One past the largest index the list gives the name `n`, `0` when it gives none. -/
def idxBound (s : CRow) (n : UInt32) : Nat :=
  s.foldr (fun o k => if o.n = n then max k (o.i.toNat + 1) else k) 0

/-- **The effect context a list of operations gives**: the signature of `n` holds, at each index
below `idxBound s n`, the first entry of the list there, and `1 ↠^lin 1` at an index the list
gives none.  `[spec §19]` -/
def effCtxOf (s : CRow) : EffCtx := fun n =>
  (List.range (idxBound s n)).map fun i =>
    match s.find? (fun o => o.n == n && o.i.toNat == i) with
    | some o => (o.q, o.A, o.B)
    | none => (.lin, .unit, .unit)

/-- The list gives each operation one signature, of a nonzero name, and has no unrestricted
operation answering `0`, decided.  `[spec §18, §19]` -/
def sigsOkB (s : CRow) : Bool :=
  s.all fun o => o.n != 0 && !(o.q == .unr && o.B.isZero) &&
    s.all fun o' => !(o'.n == o.n && o'.i == o.i) || (o'.q == o.q && o'.A == o.A && o'.B == o.B)

theorem lt_idxBound {s : CRow} {o : COpSig} (ho : o ∈ s) : o.i.toNat < idxBound s o.n := by
  induction s with
  | nil => exact absurd ho List.not_mem_nil
  | cons p s ih =>
      simp only [idxBound, List.foldr_cons] at ih ⊢
      rcases List.mem_cons.mp ho with rfl | ho
      · simp only [if_true]; omega
      · split <;> have := ih ho <;> omega

theorem idxBound_le (s : CRow) (n : UInt32) : idxBound s n ≤ 2 ^ 32 := by
  induction s with
  | nil => simp [idxBound]
  | cons p s ih =>
      simp only [idxBound, List.foldr_cons] at ih ⊢
      have := p.i.toNat_lt
      split <;> omega

/-- **The list is at the effect context it gives**, when `sigsOkB` holds of it.  `[spec §19]` -/
theorem sigsAt_effCtxOf {s : CRow} (h : sigsOkB s = true) : SigsAt (effCtxOf s) s := by
  intro o ho
  have ho' := List.all_eq_true.mp h o ho
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at ho'
  obtain ⟨⟨hn0, -⟩, hall⟩ := ho'
  have hlt := lt_idxBound ho
  refine ⟨hn0, by
    simp only [effCtxOf, List.length_map, List.length_range]; exact idxBound_le s o.n, ?_⟩
  simp only [effCtxOf, List.getElem?_map, List.getElem?_range hlt, Option.map_some]
  obtain ⟨o', hf⟩ : ∃ o', s.find? (fun o' => o'.n == o.n && o'.i.toNat == o.i.toNat) = some o' :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨o, ho, by simp⟩)
  rw [hf]
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have hi : o'.i = o.i := UInt32.toNat.inj hp.2
  have hc := List.all_eq_true.mp hall o' (List.mem_of_find?_eq_some hf)
  simp only [hp.1, hi, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hq, hA⟩, hB⟩ := hc
  simp [hq, hA, hB]

/-- **The effect context the list gives has no unrestricted abortive operation**, when
`sigsOkB` holds of it.  `[spec §18, §19]` -/
theorem noUnrExn_effCtxOf {s : CRow} (h : sigsOkB s = true) : (effCtxOf s).NoUnrExn := by
  intro n p hp
  simp only [effCtxOf, List.mem_map, List.mem_range] at hp
  obtain ⟨i, -, rfl⟩ := hp
  split
  · rename_i o hf
    intro hq
    have ho := List.all_eq_true.mp h o (List.mem_of_find?_eq_some hf)
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at ho
    have h₂ := ho.1.2
    dsimp only at hq ⊢
    simpa [hq] using h₂
  · intro hq; cases hq

end Frontend.Check
