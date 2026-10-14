import Law2.Piece

/-!
# Law2 — the borrowers the piece judgment covers, as a fragment of Core's typing

`BComp`/`BVal` is a sub-judgment of Core's typing (`BComp.toCDerives`, `BVal.toCDerives`): the
derivations a borrower at a resuming row `S` builds from

* a computation Core's typing derives at `F A`, `A` frozen (reading none of the stack's variables,
  its values in `[top]`): any pure code, borrow constants and loads among it;
* `perform` at an operation of the row; `M to x. N`; `case`, `let (x, y) =`, `V; M` on values;
* closures that stop, `λx. M : U(A ⊸ F_S B)` and `!U(A ⊸ F_S B)`, and calling one;
* `bounded_fix` at the row, a closure that stops;
* the values the fragment's values are built from: variables, `()`, pairs, injections, frozen
  values, dereliction.

`BComp.toPJ` is the piece judgment for every derivation of the fragment, by one induction on it
(the compatibility lemmas of `Law2/Piece.lean`), and `piece_of_bcomp` is D16.1's piece for every
borrower of the fragment: (S1) at the fragment, with no case on the stack's depth and none on its
entries. The hard cases are its constructors: a frame holding a value computed before a stop
(`letE` over a frame of any re-lendable values), branches (`case`), loops (`boundedFix`, `call`),
closures that stop (`lamEff`, `bangLamEff`, `call`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

/-- The values of `A` lie above the stack's outermost lend, at every vector in nesting order. -/
def AboveAll (δ : LSub) (σ : LStack) (A : VTy) : Prop :=
  ∀ αs ls v ρ, αs.length = σ.length → List.IsChain (· < ·) αs →
    vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ → stratS αs ρ

/-- A persistent type's values hold nothing: they lie above every lend. -/
theorem aboveAll_of_persistent {δ : LSub} {σ : LStack} {A : VTy} (hA : A.Persistent) :
    AboveAll (ℍ := ℍ) δ σ A := fun _ _ _ _ _ _ h a _ => by
  rw [vP_empty_of_persistent hA h]; exact ResU.inStratum_empty a

mutual
/-- **The fragment's values**, at the stack `σ` and the row `S`. -/
inductive BVal (δ : LSub) (σ : LStack) (S : Row) : LifeCtx → Ctx VTy → Expr → VTy → Prop
  | var {Δ Γ i A} : Ctx.SoloP Γ i A → BVal δ σ S Δ Γ (.var i) A
  | unit {Δ Γ} : Ctx.DeadP Γ → BVal δ σ S Δ Γ (.val .unit) .unit
  | pair {Δ Γ Γ₁ Γ₂ e₁ e₂ A B} : Ctx.SplitP Γ Γ₁ Γ₂ → BVal δ σ S Δ Γ₁ e₁ A →
      BVal δ σ S Δ Γ₂ e₂ B → BVal δ σ S Δ Γ (.pair e₁ e₂) (.tensor A B)
  | inj₁ {Δ Γ e A B} : BVal δ σ S Δ Γ e A → BVal δ σ S Δ Γ (.inj₁ e) (.sum A B)
  | inj₂ {Δ Γ e A B} : BVal δ σ S Δ Γ e B → BVal δ σ S Δ Γ (.inj₂ e) (.sum A B)
  | frozen {Δ Γ V A} : CDerives Δ Γ V (.val A) → CtxNoEffT Γ → NoEffT A →
      (∀ en ∈ σ, ¬ VFree en.x A) → AboveAll (ℍ := ℍ) δ σ A → BVal δ σ S Δ Γ V A
  | lamEff {Δ Γ M A B} : BComp δ σ S Δ (⟨A, true⟩ :: Γ) M B →
      BVal δ σ S Δ Γ (.val (.lam M)) (.thunk (.arr A (CTy.effOf S B)))
  | bangLamEff {Δ Γ M A B} : Persistent Γ → BComp δ σ S Δ (⟨A, true⟩ :: Γ) M B →
      BVal δ σ S Δ Γ (.val (.lam M)) (.bang (.thunk (.arr A (CTy.effOf S B))))
  | boundedFix {Δ Γ A B} : Ctx.DeadP Γ →
      BVal δ σ S Δ Γ (.val (.prim .boundedFix)) (boundedFixTy A (CTy.effOf S B))
  | bangE {Δ Γ e A} : BVal δ σ S Δ Γ e (.bang A) → BVal δ σ S Δ Γ e A
/-- **The fragment's computations**, at the row `S` and the answer type given. -/
inductive BComp (δ : LSub) (σ : LStack) (S : Row) : LifeCtx → Ctx VTy → Expr → VTy → Prop
  | ret {Δ Γ V A} : BVal δ σ S Δ Γ V A → BComp δ σ S Δ Γ V A
  | pure {Δ Γ e A} : CDerives Δ Γ e (.comp (.ret A)) → CtxNoEffT Γ → NoEffT A →
      (∀ en ∈ σ, ¬ VFree en.x A) → AboveAll (ℍ := ℍ) δ σ A → BComp δ σ S Δ Γ e A
  | perform {Δ Γ V} {o : OpSig} : Row.find S o.n o.i = some o → o.abort = false →
      o.q = .lin → o.B = .unit → (∀ en ∈ σ, ¬ VFree en.x o.A) → (∀ Δ a, VOutlives Δ a o.A) →
      CDerives Δ Γ V (.val o.A) → CtxNoEffT Γ →
      BComp δ σ S Δ Γ (performE (opArgE o.n o.i V)) o.B
  | letE {Δ Γ Γ₁ Γ₂ M N A B} : Ctx.SplitP Γ Γ₁ Γ₂ → BComp δ σ S Δ Γ₁ M A →
      BComp δ σ S Δ (⟨A, true⟩ :: Γ₂) N B → BComp δ σ S Δ Γ (.app (.val (.lam N)) M) B
  | case {Δ Γ Γs Γb V M₁ M₂ A₁ A₂ B} : Ctx.SplitP Γ Γs Γb → BVal δ σ S Δ Γs V (.sum A₁ A₂) →
      BComp δ σ S Δ (⟨A₁, true⟩ :: Γb) M₁ B → BComp δ σ S Δ (⟨A₂, true⟩ :: Γb) M₂ B →
      BComp δ σ S Δ Γ (.case V M₁ M₂) B
  | letpair {Δ Γ Γp Γb V M A₁ A₂ B} : Ctx.SplitP Γ Γp Γb →
      BVal δ σ S Δ Γp V (.tensor A₁ A₂) →
      BComp δ σ S Δ (⟨A₂, true⟩ :: ⟨A₁, true⟩ :: Γb) M B → BComp δ σ S Δ Γ (.letpair V M) B
  | seq {Δ Γ Γ₁ Γ₂ V M B} : Ctx.SplitP Γ Γ₁ Γ₂ → BVal δ σ S Δ Γ₁ V .unit →
      BComp δ σ S Δ Γ₂ M B → BComp δ σ S Δ Γ (.seq V M) B
  | call {Δ Γ Γ₁ Γ₂ k j A B} : Ctx.SplitP Γ Γ₁ Γ₂ →
      Ctx.SoloP Γ₁ k (.thunk (.arr A (CTy.effOf S B))) → Ctx.SoloP Γ₂ j A →
      BComp δ σ S Δ Γ (.app (.var k) (.var j)) B
end

section
variable {δ : LSub} {σ : LStack} {S : Row}

/-! ### The fragment is Core's typing -/

mutual
theorem BVal.toCDerives {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy}
    (hlin : ∀ o ∈ S, o.q = .lin) : BVal (ℍ := ℍ) δ σ S Δ Γ V A → CDerives Δ Γ V (.val A)
  | .var h => .var h
  | .unit h => .unitI h
  | .pair hs h₁ h₂ => .tensorI hs (BVal.toCDerives hlin h₁) (BVal.toCDerives hlin h₂)
  | .inj₁ h => .sumI₁ (BVal.toCDerives hlin h)
  | .inj₂ h => .sumI₂ (BVal.toCDerives hlin h)
  | .frozen hd _ _ _ _ => hd
  | .lamEff hM => .thunkV rfl (.lam (BComp.toCDerives hlin hM))
  | .bangLamEff hp hM => .bangThunkV hp rfl (.lam (BComp.toCDerives hlin hM))
  | .boundedFix hΓ => .boundedFix _ _ hΓ
  | .bangE h => .bangE (BVal.toCDerives hlin h)
theorem BComp.toCDerives {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {B : VTy}
    (hlin : ∀ o ∈ S, o.q = .lin) :
    BComp (ℍ := ℍ) δ σ S Δ Γ e B → CDerives Δ Γ e (.comp (CTy.effOf S B))
  | .ret h => .effSub (RowLe.nil S) (.ret (BVal.toCDerives hlin h))
  | .pure hd _ _ _ _ => .effSub (RowLe.nil S) hd
  | .perform hf ha _ _ _ _ hd _ => .effPerform hf ha hd
  | .letE hs hM hN =>
      .effLet hs (fun ⟨o, ho, hq⟩ => absurd (hlin o ho) hq)
        (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (hlin o ho)) (by decide))
        (BComp.toCDerives hlin hM) (BComp.toCDerives hlin hN)
  | .case hs hV h₁ h₂ =>
      .sumE hs (BVal.toCDerives hlin hV) (BComp.toCDerives hlin h₁) (BComp.toCDerives hlin h₂)
  | .letpair hs hV hM => .tensorE hs (BVal.toCDerives hlin hV) (BComp.toCDerives hlin hM)
  | .seq hs hV hM => .unitE hs (BVal.toCDerives hlin hV) (BComp.toCDerives hlin hM)
  | .call hs hk hj => .app hs (.force hk) hj
end

/-! ### The piece judgment at every derivation of the fragment -/

theorem effTab_effOf_cons (o : OpSig) (S' : Row) (B : VTy) :
    effTab (.eff o.n o.i o.q o.A o.B o.fin (CTy.effOf S' B)) δ = Row.tab (o :: S') δ :=
  effTab_effOf δ (o :: S') B

/-- `pv_lamEff` at a nonempty row. -/
theorem pv_lamEff' (hS : S ≠ []) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A B : VTy}
    (hM : PJ (ℍ := ℍ) δ σ (Row.tab S δ) Δ (⟨A, true⟩ :: Γ) M (CTy.effOf S B)) :
    PV (ℍ := ℍ) δ σ Δ Γ (.val (.lam M)) (.thunk (.arr A (CTy.effOf S B))) := by
  obtain ⟨o, S', rfl⟩ := List.exists_cons_of_ne_nil hS
  exact pv_lamEff (effTab_effOf_cons o S' B).symm hM

/-- `pv_bangLamEff` at a nonempty row. -/
theorem pv_bangLamEff' (hS : S ≠ []) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A B : VTy}
    (hp : Persistent Γ)
    (hM : PJ (ℍ := ℍ) δ σ (Row.tab S δ) Δ (⟨A, true⟩ :: Γ) M (CTy.effOf S B)) :
    PV (ℍ := ℍ) δ σ Δ Γ (.val (.lam M)) (.bang (.thunk (.arr A (CTy.effOf S B)))) := by
  obtain ⟨o, S', rfl⟩ := List.exists_cons_of_ne_nil hS
  exact pv_bangLamEff (effTab_effOf_cons o S' B).symm hp hM

/-- `pv_boundedFix` at a nonempty row. -/
theorem pv_boundedFix' (hS : S ≠ []) {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy}
    (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ Δ Γ (.val (.prim .boundedFix)) (boundedFixTy A (CTy.effOf S B)) := by
  obtain ⟨o, S', rfl⟩ := List.exists_cons_of_ne_nil hS
  exact pv_boundedFix hΓ

/-- `pj_call` at a nonempty row. -/
theorem pj_call' (hS : S ≠ []) {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {k j : Nat} {A B : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hk : Ctx.SoloP Γ₁ k (.thunk (.arr A (CTy.effOf S B))))
    (hj : Ctx.SoloP Γ₂ j A) :
    PJ (ℍ := ℍ) δ σ (Row.tab S δ) Δ Γ (.app (.var k) (.var j)) (CTy.effOf S B) := by
  obtain ⟨o, S', rfl⟩ := List.exists_cons_of_ne_nil hS
  exact pj_call (effTab_effOf_cons o S' B).symm hsp hk hj

mutual
/-- **Every value of the fragment is re-lendable** (`PV`), by induction on its derivation. -/
theorem BVal.toPV (hS : S ≠ []) (hx : AllCross σ (Row.tab S δ))
    (hLR : LinResume (Row.tab S δ)) {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy} :
    BVal (ℍ := ℍ) δ σ S Δ Γ V A → PV (ℍ := ℍ) δ σ Δ Γ V A
  | .var h => pv_var h
  | .unit h => pv_unit h
  | .pair hs h₁ h₂ => pv_pair hs (BVal.toPV hS hx hLR h₁) (BVal.toPV hS hx hLR h₂)
  | .inj₁ h => pv_inj₁ (BVal.toPV hS hx hLR h)
  | .inj₂ h => pv_inj₂ (BVal.toPV hS hx hLR h)
  | .frozen hd hΓ hA hxA hz => pv_frozen hd hΓ hA hxA hz
  | .lamEff hM => pv_lamEff' hS (BComp.toPJ hS hx hLR hM)
  | .bangLamEff hp hM => pv_bangLamEff' hS hp (BComp.toPJ hS hx hLR hM)
  | .boundedFix hΓ => pv_boundedFix' hS hΓ
  | .bangE h => pv_bangE (BVal.toPV hS hx hLR h)
/-- **Every computation of the fragment is the piece** (`PJ`), by induction on its derivation. -/
theorem BComp.toPJ (hS : S ≠ []) (hx : AllCross σ (Row.tab S δ))
    (hLR : LinResume (Row.tab S δ)) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {B : VTy} :
    BComp (ℍ := ℍ) δ σ S Δ Γ e B →
      PJ (ℍ := ℍ) δ σ (Row.tab S δ) Δ Γ e (CTy.effOf S B)
  | .ret h => pj_of_pv (BVal.toPV hS hx hLR h)
  | .pure hd hΓ hA hxA hz => pj_pure hd hΓ hA hxA hz
  | .perform hf ha hq hoB hxA hAo hd hΓ => pj_perform rfl hx hf ha hq hoB hxA hAo hd hΓ
  | .letE hs hM hN => pj_let hLR hx hs (BComp.toPJ hS hx hLR hM) (BComp.toPJ hS hx hLR hN)
  | .case hs hV h₁ h₂ =>
      pj_case hs (BVal.toPV hS hx hLR hV) (BComp.toPJ hS hx hLR h₁) (BComp.toPJ hS hx hLR h₂)
  | .letpair hs hV hM => pj_letpair hs (BVal.toPV hS hx hLR hV) (BComp.toPJ hS hx hLR hM)
  | .seq hs hV hM => pj_seq hs (BVal.toPV hS hx hLR hV) (BComp.toPJ hS hx hLR hM)
  | .call hs hk hj => pj_call' hS hs hk hj
end

/-! ### (S1) at the fragment -/

/-- What a stop owes the lenders, from a share in `[top]`, at a vector of any length. -/
theorem ghostS_of_boxTop' : ∀ {σ : LStack} {αs : List Life}, List.IsChain (· < ·) αs →
    ∀ {ls : List SRec} {R : WProp} {ρ : WRes}, boxTop αs R ρ → ghostS δ σ αs ls R ρ
  | [], _, _, _, _, _, h => h.1
  | _ :: _, [], _, _, _, _, h => h.1
  | _ :: _, _ :: _, hc, _, _, _, h => ⟨ownWandE_pass h, stratS_head hc h.2⟩

/-- **(S1) at the fragment.** A borrower of the fragment at a resuming row, its context
re-lendable as each re-lend rebuilds it from the views (`hctx`), every re-lend modelling `Δ`, its
answer in `[top]` (`hQ`): D16.1's piece at its stack, holding nothing of its own. No case on the
stack's depth or on its entries; the hard cases are the fragment's constructors. -/
theorem piece_of_bcomp (hS : S ≠ []) (hx : AllCross σ (Row.tab S δ))
    (hLR : LinResume (Row.tab S δ)) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (hd : BComp (ℍ := ℍ) δ σ S Δ Γ M B) (hB : NoEffT B) {Qa : List SRec → Val → WProp}
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs → αs.length = σ.length →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    {ds : List Bool} {αi : List Life} {ls : List SRec} {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ρv, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ αs ls Γ γ ρg) :
    OpenS δ σ (Row.tab S δ) (cbQ δ σ Qa) σ.length ds αi [] ls (substAll γ M) PMap.empty := by
  refine openS_of_pj hx (BComp.toPJ hS hx hLR hd) (fun αs ls' v hch hlen ρ hq => ?_) hΔ hctx
  have hq' : RSlot (ℍ := ℍ) δ σ B αs ls' v ρ := by
    have := hq; simp only [QA] at this; rwa [rAns_effOf] at this
  exact ghostS_of_boxTop' hch (hQ αs ls' v ρ hch hlen (rslot_vC B hB hch hq'))

/-- **Law 2 at the fragment, at every mixed stack.** A borrower of the fragment at a resuming row,
holding a mixed stack of lends open across its stops, every operation crossing every lend, its
context re-lendable as each re-lend rebuilds it: beside the owners of the stack's lenders, it is
its `ewpTS`, the owners handed back with its answer. `fold_mixed` folds the lenders;
`piece_of_bcomp` is the piece. -/
theorem law2_frag (hS : S ≠ []) (hLR : LinResume (Row.tab S δ)) (hL : (Row.tab S δ).Local)
    {β : Life} (hσ : MixedStack σ) (hx : AllCross σ (Row.tab S δ))
    (hP : ∀ e ∈ σ, ∀ ls w ρ, vCE (ℍ := ℍ) none true e.T ls δ w ρ → ρ.InStratum β)
    (hadm : ∀ e ∈ σ, ∀ v, e.k = .imm v → AdmWf e.T δ)
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {ds : List Bool} {bs : List Life} (hds : ds.length = σ.length) (hbs : bs.length = σ.length)
    (hβ : ∀ a ∈ bs, a ≤ β) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (hd : BComp (ℍ := ℍ) δ σ S Δ Γ M B) (hB : NoEffT B) {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ls ρv, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ αs ls Γ γ ρg)
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs → αs.length = σ.length →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    (ls : List SRec) :
    Entails (ownersM (ℍ := ℍ) δ σ ls)
      (ewpTS (ℍ := ℍ) ls (substAll γ M) (opTable (Row.tab S δ)) (withOwnersM δ σ Qa)) :=
  fun ρo ho => fold_mixed hLR hL hσ hx hP hadm Qa hQa ds bs hds hbs hβ ls _ ρo PMap.empty ρo ho
    (fun ls₁ _ => piece_of_bcomp hS hx hLR hd hB hQ hΔ
      (fun αs ρv hlt hch hv => hctx αs ls₁ ρv hlt hch hv)) (ResU.comp_empty_right ρo)

end

end Law2

end
