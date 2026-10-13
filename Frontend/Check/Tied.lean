import Frontend.Check.Elab
import Core.Tied

/-!
# Frontend — Check — tied derivations  `[spec §19]`

The checker builds every derivation tied to its program's effect context (decision R,
`Core/Tied.lean`). `TiedDer s Δ Γ e j` is a `CDerivesAt Ξ` derivation at every effect context `Ξ`
at which the list `s` is (`SigsAt`), `s` holding the rows the derivation reads at `[perform]`,
`[raise]` and `[handle]`. Each rule below applies one `CDerivesAt` constructor (or `CDerivesAt`'s
`effThenA`, `effHandle`) at every such `Ξ`, and its list is the union of its premises' lists with
the row it reads; a constant reads no row, and its `CDerives` derivation is tied by
`CDerivesAt.ofEffFree`.

`checkMain` (`Program.lean`) decides that `main`'s list gives each operation one signature, of a
nonzero name, and no unrestricted operation answering `0` (`sigsOkB`); the program's effect context
is the one the list gives (`effCtxOf`), at which `main`'s derivation is `CDerivesAt`
(`sigsAt_effCtxOf`), and whose abortive operations are affine (`noUnrExn_effCtxOf`).
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives CDerivesAt Jdg EffCtx RowAt SigsAt OpAt Persistent
  CtxOutlives HasDtor dtorE dropE dtor_wf rowAt_of_sigsAt)

/-- **A derivation tied at every effect context at which the list `s` is**: `s` holds the rows the
derivation reads at `[perform]`, `[raise]` and `[handle]`.  `[spec §19]` -/
def TiedDer (s : CRow) (Δ : LifeCtx) (Γ : Ctx CVTy) (e : BoCa.Expr) (j : Jdg) : Prop :=
  ∀ Ξ : EffCtx, SigsAt Ξ s → CDerivesAt Ξ Δ Γ e j

/-! ### Lists of operations -/

theorem sigsAt_union_left {Ξ : EffCtx} {s₁ s₂ : CRow} (h : SigsAt Ξ (s₁ ∪ s₂)) : SigsAt Ξ s₁ :=
  fun o ho => h o (List.mem_union_iff.mpr (.inl ho))

theorem sigsAt_union_right {Ξ : EffCtx} {s₁ s₂ : CRow} (h : SigsAt Ξ (s₁ ∪ s₂)) : SigsAt Ξ s₂ :=
  fun o ho => h o (List.mem_union_iff.mpr (.inr ho))

/-- A row the list holds is tied. -/
theorem rowAt_of_union_left {Ξ : EffCtx} {S s : CRow} (h : SigsAt Ξ (S ∪ s)) : RowAt Ξ S :=
  rowAt_of_sigsAt (sigsAt_union_left h)

namespace TiedDer
variable {Δ : LifeCtx} {Γ : Ctx CVTy}

/-! ### The rules -/

theorem var {i : Nat} {A : CVTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ i A) :
    TiedDer [] Δ Γ (.var i) (.val A) := fun _ _ => .var h

theorem unitI (h : BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ) :
    TiedDer [] Δ Γ (.val BoCa.Val.unit) (.val .unit) := fun _ _ => .unitI h

theorem topI : TiedDer [] Δ Γ (.val BoCa.Val.unit) (.comp .top) := fun _ _ => .topI

theorem force {i : Nat} {C : CCTy} (h : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ i (.thunk C)) :
    TiedDer [] Δ Γ (BoCa.Fig16.LogRel.Core.forceE C (.var i)) (.comp C) := fun _ _ => .force h

theorem tensorI {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {e₁ e₂ : BoCa.Expr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : TiedDer s₁ Δ Γ₁ e₁ (.val A))
    (h₂ : TiedDer s₂ Δ Γ₂ e₂ (.val B)) : TiedDer (s₁ ∪ s₂) Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) :=
  fun Ξ h => .tensorI hs (h₁ Ξ (sigsAt_union_left h)) (h₂ Ξ (sigsAt_union_right h))

theorem sumI₁ {s : CRow} {e : BoCa.Expr} {A B : CVTy} (h : TiedDer s Δ Γ e (.val A)) :
    TiedDer s Δ Γ (.inj₁ e) (.val (.sum A B)) := fun Ξ hΞ => .sumI₁ (h Ξ hΞ)

theorem sumI₂ {s : CRow} {e : BoCa.Expr} {A B : CVTy} (h : TiedDer s Δ Γ e (.val B)) :
    TiedDer s Δ Γ (.inj₂ e) (.val (.sum A B)) := fun Ξ hΞ => .sumI₂ (h Ξ hΞ)

theorem thunkF {s : CRow} {M : BoCa.Expr} {A : CVTy}
    (h : TiedDer s Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    TiedDer s Δ Γ (.val (BoCa.Val.lam M)) (.val (.thunk (.ret A))) := fun Ξ hΞ => .thunkF (h Ξ hΞ)

theorem thunkV {s : CRow} {N : BoCa.Expr} {C : CCTy} (hC : C.isRet = false)
    (h : TiedDer s Δ Γ (.val (BoCa.Val.lam N)) (.comp C)) :
    TiedDer s Δ Γ (.val (BoCa.Val.lam N)) (.val (.thunk C)) := fun Ξ hΞ => .thunkV hC (h Ξ hΞ)

theorem ret {s : CRow} {V : BoCa.Expr} {A : CVTy} (h : TiedDer s Δ Γ V (.val A)) :
    TiedDer s Δ Γ V (.comp (.ret A)) := fun Ξ hΞ => .ret (h Ξ hΞ)

theorem bind {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N : BoCa.Expr} {A : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hM : TiedDer s₁ Δ Γ₁ M (.comp (.ret A)))
    (hN : TiedDer s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp C)) :
    TiedDer (s₁ ∪ s₂) Δ Γ (.app (.val (BoCa.Val.lam N)) M) (.comp C) :=
  fun Ξ h => .bind hs (hM Ξ (sigsAt_union_left h)) (hN Ξ (sigsAt_union_right h))

theorem lam {s : CRow} {M : BoCa.Expr} {A : CVTy} {C : CCTy}
    (h : TiedDer s Δ (⟨A, true⟩ :: Γ) M (.comp C)) :
    TiedDer s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.arr A C)) := fun Ξ hΞ => .lam (h Ξ hΞ)

theorem app {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M : BoCa.Expr} {i : Nat} {A : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hM : TiedDer s Δ Γ₁ M (.comp (.arr A C)))
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₂ i A) : TiedDer s Δ Γ (.app M (.var i)) (.comp C) :=
  fun Ξ hΞ => .app hs (hM Ξ hΞ) hx

theorem withI {s₁ s₂ : CRow} {M N : BoCa.Expr} {C D : CCTy}
    (hM : TiedDer s₁ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) M (.comp C))
    (hN : TiedDer s₂ Δ (BoCa.Fig16.LogRel.Core.withCtx Γ) N (.comp D)) :
    TiedDer (s₁ ∪ s₂) Δ Γ (BoCa.Fig16.LogRel.Core.withPair M N) (.comp (.amp C D)) :=
  fun Ξ h => .withI (hM Ξ (sigsAt_union_left h)) (hN Ξ (sigsAt_union_right h))

theorem proj₁ {s : CRow} {M : BoCa.Expr} {C D : CCTy} (h : TiedDer s Δ Γ M (.comp (.amp C D))) :
    TiedDer s Δ Γ (.app M (.val (BoCa.Val.inj₁ BoCa.Val.unit))) (.comp C) :=
  fun Ξ hΞ => .proj₁ (h Ξ hΞ)

theorem proj₂ {s : CRow} {M : BoCa.Expr} {C D : CCTy} (h : TiedDer s Δ Γ M (.comp (.amp C D))) :
    TiedDer s Δ Γ (.app M (.val (BoCa.Val.inj₂ BoCa.Val.unit))) (.comp D) :=
  fun Ξ hΞ => .proj₂ (h Ξ hΞ)

theorem unitE {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {V M : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hV : TiedDer s₁ Δ Γ₁ V (.val .unit))
    (hM : TiedDer s₂ Δ Γ₂ M (.comp C)) : TiedDer (s₁ ∪ s₂) Δ Γ (.seq V M) (.comp C) :=
  fun Ξ h => .unitE hs (hV Ξ (sigsAt_union_left h)) (hM Ξ (sigsAt_union_right h))

theorem tensorE {s₁ s₂ : CRow} {Γp Γb : Ctx CVTy} {V M : BoCa.Expr} {A B : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γp Γb) (hV : TiedDer s₁ Δ Γp V (.val (.tensor A B)))
    (hM : TiedDer s₂ Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C)) :
    TiedDer (s₁ ∪ s₂) Δ Γ (.letpair V M) (.comp C) :=
  fun Ξ h => .tensorE hs (hV Ξ (sigsAt_union_left h)) (hM Ξ (sigsAt_union_right h))

theorem sumE {s₁ s₂ s₃ : CRow} {Γs Γb : Ctx CVTy} {V M₁ M₂ : BoCa.Expr} {A B : CVTy} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γs Γb) (hV : TiedDer s₁ Δ Γs V (.val (.sum A B)))
    (h₁ : TiedDer s₂ Δ (⟨A, true⟩ :: Γb) M₁ (.comp C))
    (h₂ : TiedDer s₃ Δ (⟨B, true⟩ :: Γb) M₂ (.comp C)) :
    TiedDer (s₁ ∪ (s₂ ∪ s₃)) Δ Γ (.case V M₁ M₂) (.comp C) :=
  fun Ξ h => .sumE hs (hV Ξ (sigsAt_union_left h))
    (h₁ Ξ (sigsAt_union_left (sigsAt_union_right h)))
    (h₂ Ξ (sigsAt_union_right (sigsAt_union_right h)))

theorem zeroE {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {V : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hV : TiedDer s Δ Γ₁ V (.val .zero)) :
    TiedDer s Δ Γ (BoCa.Fig16.LogRel.Core.absurdE V) (.comp C) := fun Ξ hΞ => .zeroE hs (hV Ξ hΞ)

theorem allI {s : CRow} {x : LifeVar} {b : CLife} {M : BoCa.Expr} {S : CVTy} {C : CCTy}
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ BoCa.Fig16.LogRel.Core.VFree x s.ty)
    (h : TiedDer s (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
    TiedDer s Δ Γ (.val (BoCa.Val.lam M)) (.comp (.all x b C)) :=
  fun Ξ hΞ => .allI hbx hΔx hΓx (h Ξ hΞ)

theorem allE {s : CRow} {M : BoCa.Expr} {x : LifeVar} {b a : CLife} {C : CCTy}
    (h : TiedDer s Δ Γ M (.comp (.all x b C))) (hlt : Δ.EntailsLt a b) :
    TiedDer s Δ Γ (.app M (.val BoCa.Val.unit)) (.comp (C.instLife x a)) :=
  fun Ξ hΞ => .allE (h Ξ hΞ) hlt

theorem bangThunkF {s : CRow} {M : BoCa.Expr} {A : CVTy} (hp : Persistent Γ)
    (h : TiedDer s Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A))) :
    TiedDer s Δ Γ (.val (BoCa.Val.lam M)) (.val (.bang (.thunk (.ret A)))) :=
  fun Ξ hΞ => .bangThunkF hp (h Ξ hΞ)

theorem bangThunkV {s : CRow} {N : BoCa.Expr} {C : CCTy} (hp : Persistent Γ)
    (hC : C.isRet = false) (h : TiedDer s Δ Γ (.val (BoCa.Val.lam N)) (.comp C)) :
    TiedDer s Δ Γ (.val (BoCa.Val.lam N)) (.val (.bang (.thunk C))) :=
  fun Ξ hΞ => .bangThunkV hp hC (h Ξ hΞ)

theorem bangE {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedDer s Δ Γ e (.val (.bang A))) :
    TiedDer s Δ Γ e (.val A) := fun Ξ hΞ => .bangE (h Ξ hΞ)

theorem boxI {s : CRow} {e : BoCa.Expr} {a : CLife} {A : CVTy} (h : TiedDer s Δ Γ e (.val A))
    (hΓ : CtxOutlives Δ Γ a) : TiedDer s Δ Γ e (.val (.box a A)) := fun Ξ hΞ => .boxI (h Ξ hΞ) hΓ

theorem boxE {s : CRow} {e : BoCa.Expr} {a : CLife} {A : CVTy}
    (h : TiedDer s Δ Γ e (.val (.box a A))) : TiedDer s Δ Γ e (.val A) := fun Ξ hΞ => .boxE (h Ξ hΞ)

theorem immSub {s : CRow} {e : BoCa.Expr} {a b : CLife} {A : CVTy}
    (h : TiedDer s Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
    TiedDer s Δ Γ e (.val (.imm a A)) := fun Ξ hΞ => .immSub (h Ξ hΞ) hle

theorem mutSub {s : CRow} {e : BoCa.Expr} {a b : CLife} {A : CVTy}
    (h : TiedDer s Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
    TiedDer s Δ Γ e (.val (.mut a A)) := fun Ξ hΞ => .mutSub (h Ξ hΞ) hle

theorem lolliE {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {f a : BoCa.Expr} {A B : CVTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (ha : TiedDer s₁ Δ Γ₁ a (.val A))
    (hf : TiedDer s₂ Δ Γ₂ f (.val (.lolli A B))) : TiedDer (s₁ ∪ s₂) Δ Γ (.app f a) (.val B) :=
  fun Ξ h => .lolliE hs (ha Ξ (sigsAt_union_left h)) (hf Ξ (sigsAt_union_right h))

theorem allEV {s : CRow} {e : BoCa.Expr} {x : LifeVar} {b a : CLife} {A : CVTy}
    (h : TiedDer s Δ Γ e (.val (.all x b A))) (hlt : Δ.EntailsLt a b) :
    TiedDer s Δ Γ (.app e (.val BoCa.Val.unit)) (.val (A.instLife x a)) :=
  fun Ξ hΞ => .allEV (h Ξ hΞ) hlt

theorem ofRet {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedDer s Δ Γ e (.comp (.ret A))) :
    TiedDer s Δ Γ e (.val A) := fun Ξ hΞ => .ofRet (h Ξ hΞ)

theorem roll {s : CRow} {e : BoCa.Expr} {A : CVTy} (hA : A.NoMut 0)
    (hc : (BoCa.Fig16.LogRel.Core.VTy.mu A).Cl 0)
    (h : TiedDer s Δ Γ e (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A))) :
    TiedDer s Δ Γ e (.val (.mu A)) := fun Ξ hΞ => .roll hA hc (h Ξ hΞ)

theorem unroll {s : CRow} {e : BoCa.Expr} {A : CVTy} (h : TiedDer s Δ Γ e (.val (.mu A))) :
    TiedDer s Δ Γ e (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) :=
  fun Ξ hΞ => .unroll (h Ξ hΞ)

theorem nuIn {s : CRow} {e : BoCa.Expr} {C : CCTy} (hC : C.NuOk)
    (h : TiedDer s Δ Γ e (.comp C.unroll)) : TiedDer s Δ Γ e (.comp (.nu C)) :=
  fun Ξ hΞ => .nuIn hC (h Ξ hΞ)

theorem nuOut {s : CRow} {e : BoCa.Expr} {C : CCTy} (hC : C.NuOk)
    (h : TiedDer s Δ Γ e (.comp (.nu C))) : TiedDer s Δ Γ e (.comp C.unroll) :=
  fun Ξ hΞ => .nuOut hC (h Ξ hΞ)

/-! ### The effect rules -/

theorem effSub {s : CRow} {e : BoCa.Expr} {S S' : CRow} {A : CVTy}
    (hle : BoCa.Fig16.LogRel.Core.RowLe S S') (h : TiedDer s Δ Γ e (.comp (effOf S A))) :
    TiedDer s Δ Γ e (.comp (effOf S' A)) := fun Ξ hΞ => .effSub hle (h Ξ hΞ)

/-- `[perform]` reads its row. -/
theorem effPerform {s : CRow} {V : BoCa.Expr} {S : CRow} {o : COpSig}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (hna : o.abort = false)
    (h : TiedDer s Δ Γ V (.val o.A)) :
    TiedDer (S ∪ s) Δ Γ (BoCa.BoLo.performE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i V))
      (.comp (effOf S o.B)) :=
  fun Ξ hΞ => .effPerform (rowAt_of_union_left hΞ) hf hna (h Ξ (sigsAt_union_right hΞ))

/-- `[raise]` reads its row. -/
theorem effRaise {s : CRow} {V : BoCa.Expr} {S : CRow} {o : COpSig} {B : CVTy}
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : o.A.Drop) (h : TiedDer s Δ Γ V (.val o.A)) :
    TiedDer (S ∪ s) Δ Γ (BoCa.BoLo.raiseE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i V))
      (.comp (effOf S B)) :=
  fun Ξ hΞ => .effRaise (rowAt_of_union_left hΞ) hf ha hd (h Ξ (sigsAt_union_right hΞ))

theorem effLet {s₁ s₂ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N : BoCa.Expr} {A B : CVTy} {S : CRow}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Weak → Γ₂.Drops)
    (hU : S.Unr → Persistent Γ₂) (hM : TiedDer s₁ Δ Γ₁ M (.comp (effOf S A)))
    (hN : TiedDer s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp (effOf S B))) :
    TiedDer (s₁ ∪ s₂) Δ Γ (.app (.val (BoCa.Val.lam N)) M) (.comp (effOf S B)) :=
  fun Ξ h => .effLet hs hW hU (hM Ξ (sigsAt_union_left h)) (hN Ξ (sigsAt_union_right h))

theorem effThenA {s₁ s₂ s₃ : CRow} {Γ₁ Γ₂ : Ctx CVTy} {M N D : BoCa.Expr} {A B : CVTy} {S : CRow}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq)
    (hU : S.UnrD → Persistent Γ₂) (hM : TiedDer s₁ Δ Γ₁ M (.comp (effOf S A)))
    (hN : TiedDer s₂ Δ (⟨A, true⟩ :: Γ₂) N (.comp (effOf S B)))
    (hD : TiedDer s₃ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    TiedDer (s₁ ∪ (s₂ ∪ s₃)) Δ Γ (BoCa.Fig16.LogRel.Core.thenE N D M) (.comp (effOf S B)) :=
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
    (he : TiedDer s Δ Γ₂ e (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A))) :
    TiedDer ((BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ s) Δ Γ
      (BoCa.Fig16.LogRel.Core.hndTerm n (E.map Prod.fst) ir ic e) (.comp (effOf S R)) :=
  fun Ξ h => CDerivesAt.effHandle (rowAt_of_union_left h) hs hs₁ hr hc hn0 hnS hlen
    (he Ξ (sigsAt_union_right h))

/-! ### Derived forms -/

/-- A derivation of a term with no operation reads no row. -/
theorem ofCDerives {e : BoCa.Expr} {j : Jdg} (h : CDerives Δ Γ e j) (he : e.effFree = true) :
    TiedDer [] Δ Γ e j := fun _ _ => CDerivesAt.ofEffFree h he

/-- `dtorE T xᵢ; e`, as `drop_derives`: `unitE` over the destructor applied to the slot.
`[spec §12]` -/
theorem drop {s : CRow} {Γ₁ Γ₂ : Ctx CVTy} {i : Nat} {T : CVTy} {e : BoCa.Expr} {C : CCTy}
    (hs : BoCa.Fig16.LogRel.Core.Ctx.SplitP Γ Γ₁ Γ₂)
    (hx : BoCa.Fig16.LogRel.Core.Ctx.SoloP Γ₁ i T) (hT : HasDtor T)
    (hE : (dtorE T).effFree = true) (h : TiedDer s Δ Γ₂ e (.comp C)) :
    TiedDer s Δ Γ (dropE T i e) (.comp C) :=
  fun Ξ hΞ => .unitE hs (.lolliE (BoCa.Fig16.LogRel.Core.split_kill' Γ₁).toP (.var hx)
    (CDerivesAt.ofEffFree (dtor_wf hT (BoCa.Fig16.LogRel.Core.kill_dead Γ₁)) hE)) (h Ξ hΞ)

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
