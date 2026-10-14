import Law2.Handle

/-!
# Law2 — a fragment of Core's typing the piece judgment covers with no open step

`BComp`/`BVal` is a sub-judgment of Core's typing (`BComp.toCDerives`, `BVal.toCDerives`): the
derivations a borrower at a resuming row builds, the lenders' row `S₀` a parameter and the row a
derivation is at an index, from

* a computation Core's typing derives at `F A`, `A` frozen (reading none of the stack's variables,
  persistent or outliving every lifetime, `FrozenTy`): any pure code over a context free of `U`,
  borrow constants and loads among it;
* `perform` at an operation of the lenders' names (`perform`), or of a handler installed inside the
  borrower (`performIn`, its argument any value of the fragment);
* `M to x. N`; `case`, `let (x, y) =`, `V; M` on values;
* closures, `λx. M : U(A ⊸ F_S B)` and `!U(A ⊸ F_S B)`, and calling one;
* `bounded_fix` at the row;
* a handler installed inside the borrower (`handle`): `handle_n e with H`, `n` a name of
  neither the lenders' row nor the row outside, its operations linear; and resuming the
  continuation a clause is handed (`resume`);
* the values the fragment's values are built from: variables, `()`, pairs, injections, frozen
  values, dereliction.

`BComp.toPJ` is the piece judgment for every derivation of the fragment, by one induction on it
(the compatibility lemmas of `Law2/Piece.lean` and `pj_handle`), and `piece_of_bcomp` is D16.1's
piece for every borrower of the fragment at the lenders' row. Every derivation of Core's typing is
covered, rule by rule, by `Law2/Fundamental.lean`; the fragment is the part reached with no open
step, which `Law2/FragInstances.lean` instantiates.
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

/-- A type outliving every lifetime and reading none of the stack's variables: its values lie above
every lend (6.60 at a variable of the stack). -/
theorem aboveAll_of_outlives {δ : LSub} {σ : LStack} {A : VTy} (hAo : ∀ Δ a, VOutlives Δ a A)
    (hx : ∀ en ∈ σ, ¬ VFree en.x A) : AboveAll (ℍ := ℍ) δ σ A := by
  intro αs ls v ρ _ _ h
  rw [vC_extS_of_not_free true ls σ αs hx] at h
  cases σ with
  | nil => exact fun a ha => by simp_all
  | cons en σ' => exact stratS_of_outlives hAo (hx en (List.mem_cons_self ..)) h αs

/-- **A frozen type**, syntactically: persistent, or outliving every lifetime. -/
def FrozenTy (A : VTy) : Prop := A.Persistent ∨ ∀ Δ a, VOutlives Δ a A

/-- A frozen type reading none of the stack's variables lies above every lend. -/
theorem aboveAll_of_frozenTy {δ : LSub} {σ : LStack} {A : VTy} (hA : FrozenTy A)
    (hx : ∀ en ∈ σ, ¬ VFree en.x A) : AboveAll (ℍ := ℍ) δ σ A :=
  hA.elim aboveAll_of_persistent fun h => aboveAll_of_outlives h hx

mutual
/-- **The fragment's values**, at the stack `σ`, the lenders' row `S₀` and the row `S`. -/
inductive BVal (δ : LSub) (σ : LStack) (S₀ : Row) : Row → LifeCtx → Ctx VTy → Expr → VTy → Prop
  | var {S Δ Γ i A} : Ctx.SoloP Γ i A → BVal δ σ S₀ S Δ Γ (.var i) A
  | unit {S Δ Γ} : Ctx.DeadP Γ → BVal δ σ S₀ S Δ Γ (.val .unit) .unit
  | pair {S Δ Γ Γ₁ Γ₂ e₁ e₂ A B} : Ctx.SplitP Γ Γ₁ Γ₂ → BVal δ σ S₀ S Δ Γ₁ e₁ A →
      BVal δ σ S₀ S Δ Γ₂ e₂ B → BVal δ σ S₀ S Δ Γ (.pair e₁ e₂) (.tensor A B)
  | inj₁ {S Δ Γ e A B} : BVal δ σ S₀ S Δ Γ e A → BVal δ σ S₀ S Δ Γ (.inj₁ e) (.sum A B)
  | inj₂ {S Δ Γ e A B} : BVal δ σ S₀ S Δ Γ e B → BVal δ σ S₀ S Δ Γ (.inj₂ e) (.sum A B)
  | frozen {S Δ Γ V A} : CDerives Δ Γ V (.val A) → CtxNoThunk Γ → NoThunkT A →
      (∀ en ∈ σ, ¬ VFree en.x A) → FrozenTy A → BVal δ σ S₀ S Δ Γ V A
  | lamEff {S Δ Γ M A B} : BComp δ σ S₀ S Δ (⟨A, true⟩ :: Γ) M B →
      BVal δ σ S₀ S Δ Γ (.val (.lam M)) (.thunk (.arr A (CTy.effOf S B)))
  | bangLamEff {S Δ Γ M A B} : Persistent Γ → BComp δ σ S₀ S Δ (⟨A, true⟩ :: Γ) M B →
      BVal δ σ S₀ S Δ Γ (.val (.lam M)) (.bang (.thunk (.arr A (CTy.effOf S B))))
  | boundedFix {S Δ Γ A B} : Ctx.DeadP Γ →
      BVal δ σ S₀ S Δ Γ (.val (.prim .boundedFix)) (boundedFixTy A (CTy.effOf S B))
  | bangE {S Δ Γ e A} : BVal δ σ S₀ S Δ Γ e (.bang A) → BVal δ σ S₀ S Δ Γ e A
/-- **The fragment's computations**, at the row `S` and the answer type given. -/
inductive BComp (δ : LSub) (σ : LStack) (S₀ : Row) : Row → LifeCtx → Ctx VTy → Expr → VTy → Prop
  | ret {S Δ Γ V A} : BVal δ σ S₀ S Δ Γ V A → BComp δ σ S₀ S Δ Γ V A
  | pure {S Δ Γ e A} : CDerives Δ Γ e (.comp (.ret A)) → CtxNoThunk Γ → NoThunkT A →
      (∀ en ∈ σ, ¬ VFree en.x A) → FrozenTy A → BComp δ σ S₀ S Δ Γ e A
  | perform {S Δ Γ V} {o : OpSig} : Row.find S o.n o.i = some o →
      Row.find S₀ o.n o.i = some o → o.abort = false → o.q = .lin → o.B = .unit →
      (∀ en ∈ σ, ¬ VFree en.x o.A) → (∀ Δ a, VOutlives Δ a o.A) → NoThunkT o.A →
      CDerives Δ Γ V (.val o.A) → CtxNoThunk Γ →
      BComp δ σ S₀ S Δ Γ (performE (opArgE o.n o.i V)) o.B
  | performIn {S Δ Γ V} {o : OpSig} : Row.find S o.n o.i = some o → outN S₀ o.n = false →
      o.abort = false → BVal δ σ S₀ S Δ Γ V o.A →
      BComp δ σ S₀ S Δ Γ (performE (opArgE o.n o.i V)) o.B
  | letE {S Δ Γ Γ₁ Γ₂ M N A B} : Ctx.SplitP Γ Γ₁ Γ₂ → BComp δ σ S₀ S Δ Γ₁ M A →
      BComp δ σ S₀ S Δ (⟨A, true⟩ :: Γ₂) N B → BComp δ σ S₀ S Δ Γ (.app (.val (.lam N)) M) B
  | case {S Δ Γ Γs Γb V M₁ M₂ A₁ A₂ B} : Ctx.SplitP Γ Γs Γb →
      BVal δ σ S₀ S Δ Γs V (.sum A₁ A₂) →
      BComp δ σ S₀ S Δ (⟨A₁, true⟩ :: Γb) M₁ B → BComp δ σ S₀ S Δ (⟨A₂, true⟩ :: Γb) M₂ B →
      BComp δ σ S₀ S Δ Γ (.case V M₁ M₂) B
  | letpair {S Δ Γ Γp Γb V M A₁ A₂ B} : Ctx.SplitP Γ Γp Γb →
      BVal δ σ S₀ S Δ Γp V (.tensor A₁ A₂) →
      BComp δ σ S₀ S Δ (⟨A₂, true⟩ :: ⟨A₁, true⟩ :: Γb) M B →
      BComp δ σ S₀ S Δ Γ (.letpair V M) B
  | seq {S Δ Γ Γ₁ Γ₂ V M B} : Ctx.SplitP Γ Γ₁ Γ₂ → BVal δ σ S₀ S Δ Γ₁ V .unit →
      BComp δ σ S₀ S Δ Γ₂ M B → BComp δ σ S₀ S Δ Γ (.seq V M) B
  | call {S Δ Γ Γ₁ Γ₂ k j A B} : Ctx.SplitP Γ Γ₁ Γ₂ →
      Ctx.SoloP Γ₁ k (.thunk (.arr A (CTy.effOf S B))) → Ctx.SoloP Γ₂ j A →
      BComp δ σ S₀ S Δ Γ (.app (.var k) (.var j)) B
  | resume {S Δ Γ Γ₁ Γ₂ k j B C} : Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.SoloP Γ₁ k (kTy S C .lin B) →
      Ctx.SoloP Γ₂ j B →
      BComp δ σ S₀ S Δ Γ (.app (.app (.var k) (.val (.inj₁ .unit))) (.var j)) C
  | handle {S Δ Γ Γ₁ Γ₂ H e} {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} :
      Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.DeadP Γ₁ → H.ValFormIn Γ₁ →
      BVal δ σ S₀ S Δ Γ₁ H (.tensor (retTy S A R) (clausesTy S R E)) → n ≠ 0 →
      (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 → (∀ q ∈ E, q.1 = .lin) → outN S₀ n = false →
      BComp δ σ S₀ (Row.ofEff n E 0 ++ S) Δ Γ₂ e A →
      BComp δ σ S₀ S Δ Γ (hndExpr n (E.map Prod.fst) H e) R
end

section
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-! ### The fragment is Core's typing -/

/-- A handler's operations carry its effect's qualifiers. -/
theorem mem_ofEff_q {n : UInt32} : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy),
    ∀ o ∈ Row.ofEff n E k fs, ∃ q ∈ E, o.q = q.1
  | [], _, _, o, h => by simp [Row.ofEff] at h
  | (q, A, B) :: E, k, fs, o, h => by
      simp only [Row.ofEff, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨(q, A, B), List.mem_cons_self .., rfl⟩
      · obtain ⟨q', hq', he⟩ := mem_ofEff_q E (k + 1) _ o h
        exact ⟨q', List.mem_cons_of_mem _ hq', he⟩

theorem lin_ofEff_append {n : UInt32} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {S : Row}
    (hE : ∀ q ∈ E, q.1 = .lin) (hS : ∀ o ∈ S, o.q = .lin) :
    ∀ o ∈ Row.ofEff n E 0 fs ++ S, o.q = .lin := by
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · obtain ⟨q, hq, he⟩ := mem_ofEff_q E 0 _ o h
    rw [he]; exact hE q hq
  · exact hS o h

mutual
theorem BVal.toCDerives {S : Row} {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy}
    (hlin : ∀ o ∈ S, o.q = .lin) : BVal δ σ S₀ S Δ Γ V A → CDerives Δ Γ V (.val A)
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
theorem BComp.toCDerives {S : Row} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {B : VTy}
    (hlin : ∀ o ∈ S, o.q = .lin) :
    BComp δ σ S₀ S Δ Γ e B → CDerives Δ Γ e (.comp (CTy.effOf S B))
  | .ret h => .effSub (RowLe.nil S) (.ret (BVal.toCDerives hlin h))
  | .pure hd _ _ _ _ => .effSub (RowLe.nil S) hd
  | .perform hf _ ha _ _ _ _ _ hd _ => .effPerform hf ha hd
  | .performIn hf _ ha hV => .effPerform hf ha (BVal.toCDerives hlin hV)
  | .letE hs hM hN =>
      .effLet hs (fun ⟨o, ho, hq⟩ => absurd (hlin o ho) hq)
        (fun ⟨o, ho, hq⟩ => absurd (hq.symm.trans (hlin o ho)) (by decide))
        (BComp.toCDerives hlin hM) (BComp.toCDerives hlin hN)
  | .case hs hV h₁ h₂ =>
      .sumE hs (BVal.toCDerives hlin hV) (BComp.toCDerives hlin h₁) (BComp.toCDerives hlin h₂)
  | .letpair hs hV hM => .tensorE hs (BVal.toCDerives hlin hV) (BComp.toCDerives hlin hM)
  | .seq hs hV hM => .unitE hs (BVal.toCDerives hlin hV) (BComp.toCDerives hlin hM)
  | .call hs hk hj => .app hs (.force hk) hj
  | .resume hs hk hj => .app hs (.proj₁ (.force hk)) hj
  | .handle hs hd hH hc hn0 hnS hlen hE _ he =>
      .effHandleV hs hd hH (BVal.toCDerives hlin hc) hn0 hnS hlen
        (BComp.toCDerives (lin_ofEff_append hE hlin) he)
end

/-! ### The piece judgment at every derivation of the fragment -/

/-- A handler's operations are of its own name. -/
theorem outN_ofEff {n : UInt32} (hn : outN S₀ n = false) (E : List (Qual × VTy × VTy))
    (fs : Nat → CTy) : ∀ o ∈ Row.ofEff n E 0 fs, outN S₀ o.n = false := fun o ho => by
  rw [mem_ofEff_n E 0 fs o ho]; exact hn

mutual
/-- **Every value of the fragment is re-lendable** (`PV`), by induction on its derivation. -/
theorem BVal.toPV {S : Row} (hLR : RowLin S₀ S) {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr}
    {A : VTy} : BVal δ σ S₀ S Δ Γ V A → PV (ℍ := ℍ) δ σ S₀ Δ Γ V A
  | .var h => pv_var h
  | .unit h => pv_unit h
  | .pair hs h₁ h₂ => pv_pair hs (BVal.toPV hLR h₁) (BVal.toPV hLR h₂)
  | .inj₁ h => pv_inj₁ (BVal.toPV hLR h)
  | .inj₂ h => pv_inj₂ (BVal.toPV hLR h)
  | .frozen hd hΓ hA hxA hz => pv_frozen hd hΓ hA hxA (aboveAll_of_frozenTy hz hxA)
  | .lamEff hM => pv_lam (BComp.toPJ hLR hM)
  | .bangLamEff hp hM => pv_bangLam hp (BComp.toPJ hLR hM)
  | .boundedFix hΓ => pv_boundedFix hΓ
  | .bangE h => pv_bangE (BVal.toPV hLR h)
/-- **Every computation of the fragment is the piece** (`PJ`), by induction on its derivation. -/
theorem BComp.toPJ {S : Row} (hLR : RowLin S₀ S) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    {B : VTy} : BComp δ σ S₀ S Δ Γ e B → PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (CTy.effOf S B)
  | .ret h => pj_of_pv (BVal.toPV hLR h)
  | .pure hd hΓ hA hxA hz => pj_pure hd hΓ hA hxA (aboveAll_of_frozenTy hz hxA)
  | .perform hfS hf ha hq hoB hxA hAo hNT hd hΓ =>
      pj_perform hfS (outN_of_mem (Row.find_mem hf).1) ha hq hoB hxA hAo hNT
        (pv_frozen hd hΓ hNT hxA (aboveAll_of_outlives hAo hxA))
  | .performIn hf hout _ hV => pj_performIn hf hout (BVal.toPV hLR hV)
  | .letE hs hM hN => pj_let hLR hs (BComp.toPJ hLR hM) (BComp.toPJ hLR hN)
  | .case hs hV h₁ h₂ =>
      pj_case hs (BVal.toPV hLR hV) (BComp.toPJ hLR h₁) (BComp.toPJ hLR h₂)
  | .letpair hs hV hM => pj_letpair hs (BVal.toPV hLR hV) (BComp.toPJ hLR hM)
  | .seq hs hV hM => pj_seq hs (BVal.toPV hLR hV) (BComp.toPJ hLR hM)
  | .call hs hk hj => pj_call hs hk hj
  | .resume hs hk hj => pj_resume hs hk hj
  | .handle (E := E) hs hd hH hc _ hnS hlen hE hout he =>
      pj_handle (fs := finsNil) hs hd hH (BVal.toPV hLR hc) hout hnS hlen hE
        (BComp.toPJ (rowLin_append (outN_ofEff hout E finsNil) hLR) he)
end

/-! ### (S1) at the fragment -/

/-- What a stop owes the lenders, from a share in `[top]`, at a vector of any length. -/
theorem ghostS_of_boxTop' : ∀ {σ : LStack} {αs : List Life}, List.IsChain (· < ·) αs →
    ∀ {ls : List SRec} {R : WProp} {ρ : WRes}, boxTop αs R ρ → ghostS δ σ αs ls R ρ
  | [], _, _, _, _, _, h => h.1
  | _ :: _, [], _, _, _, _, h => h.1
  | _ :: _, _ :: _, hc, _, _, _, h => ⟨ownWandE_pass h, stratS_head hc h.2⟩

/-- **D16.1's piece from the piece judgment**, at the lenders' row: a borrower whose piece
judgment holds, its context re-lendable as each re-lend rebuilds it from the views (`hctx`), every
re-lend modelling `Δ`, its answer free of `U` and in `[top]` (`hQ`), holding nothing of its
own. -/
theorem piece_of_pj (hx : AllCross σ (Row.tab S₀ δ)) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr}
    {B : VTy} (hpj : PJ (ℍ := ℍ) δ σ S₀ Δ Γ M (CTy.effOf S₀ B)) (hB : NoThunkT B)
    {Qa : List SRec → Val → WProp}
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs → αs.length = σ.length →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    {ds : List Bool} {αi : List Life} {ls : List SRec} {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ρv, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρg) :
    OpenS δ σ (Row.tab S₀ δ) (cbQ δ σ Qa) σ.length ds αi [] ls (substAll γ M) PMap.empty :=
  openS_of_pj hx hpj (fun αs ls' v hch hlen ρ hq =>
    ghostS_of_boxTop' hch (hQ αs ls' v ρ hch hlen (rslot_vC B hB hch hq))) hΔ hctx

/-- **(S1) at the fragment.** A borrower of the fragment at the lenders' resuming row `S₀`, its
context re-lendable as each re-lend rebuilds it from the views (`hctx`), every re-lend modelling
`Δ`, its answer in `[top]` (`hQ`): D16.1's piece at its stack, holding nothing of its own. No case
on the stack's depth or on its entries; the hard cases are the fragment's constructors. -/
theorem piece_of_bcomp (hx : AllCross σ (Row.tab S₀ δ))
    (hLR : LinResume (Row.tab S₀ δ)) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (hd : BComp δ σ S₀ S₀ Δ Γ M B) (hB : NoThunkT B) {Qa : List SRec → Val → WProp}
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs → αs.length = σ.length →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    {ds : List Bool} {αi : List Life} {ls : List SRec} {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ρv, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρg) :
    OpenS δ σ (Row.tab S₀ δ) (cbQ δ σ Qa) σ.length ds αi [] ls (substAll γ M) PMap.empty :=
  piece_of_pj hx (BComp.toPJ (rowLin_self hLR) hd) hB hQ hΔ hctx

/-- **Law 2 from the piece judgment, at every mixed stack.** A borrower at a resuming row whose
piece judgment holds, holding a mixed stack of lends open across its stops, every operation of the
row crossing every lend, its context re-lendable as each re-lend rebuilds it: beside the owners of
the stack's lenders, it is its `ewpTS`, the owners handed back with its answer. `fold_mixed` folds
the lenders; `piece_of_pj` is the piece. -/
theorem law2_of_pj {S : Row} (hLR : LinResume (Row.tab S δ))
    (hL : (Row.tab S δ).Local) {β : Life} (hσ : MixedStack σ) (hx : AllCross σ (Row.tab S δ))
    (hP : ∀ e ∈ σ, ∀ ls w ρ, vCE (ℍ := ℍ) none true e.T ls δ w ρ → ρ.InStratum β)
    (hadm : ∀ e ∈ σ, ∀ v, e.k = .imm v → AdmWf e.T δ)
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {ds : List Bool} {bs : List Life} (hds : ds.length = σ.length) (hbs : bs.length = σ.length)
    (hβ : ∀ a ∈ bs, a ≤ β) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (hpj : PJ (ℍ := ℍ) δ σ S Δ Γ M (CTy.effOf S B)) (hB : NoThunkT B) {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ls ρv, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ S αs ls Γ γ ρg)
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs → αs.length = σ.length →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    (ls : List SRec) :
    Entails (ownersM (ℍ := ℍ) δ σ ls)
      (ewpTS (ℍ := ℍ) ls (substAll γ M) (opTable (Row.tab S δ)) (withOwnersM δ σ Qa)) :=
  fun ρo ho => fold_mixed hLR hL hσ hx hP hadm Qa hQa ds bs hds hbs hβ ls _ ρo PMap.empty ρo ho
    (fun ls₁ _ => piece_of_pj hx hpj hB hQ hΔ
      (fun αs ρv hlt hch hv => hctx αs ls₁ ρv hlt hch hv)) (ResU.comp_empty_right ρo)

/-- **Law 2 at the fragment, at every mixed stack**: `law2_of_pj` at the fragment's piece
judgment. -/
theorem law2_frag {S : Row} (hLR : LinResume (Row.tab S δ))
    (hL : (Row.tab S δ).Local) {β : Life} (hσ : MixedStack σ) (hx : AllCross σ (Row.tab S δ))
    (hP : ∀ e ∈ σ, ∀ ls w ρ, vCE (ℍ := ℍ) none true e.T ls δ w ρ → ρ.InStratum β)
    (hadm : ∀ e ∈ σ, ∀ v, e.k = .imm v → AdmWf e.T δ)
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {ds : List Bool} {bs : List Life} (hds : ds.length = σ.length) (hbs : bs.length = σ.length)
    (hβ : ∀ a ∈ bs, a ≤ β) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (hd : BComp δ σ S S Δ Γ M B) (hB : NoThunkT B) {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ls ρv, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ S αs ls Γ γ ρg)
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs → αs.length = σ.length →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    (ls : List SRec) :
    Entails (ownersM (ℍ := ℍ) δ σ ls)
      (ewpTS (ℍ := ℍ) ls (substAll γ M) (opTable (Row.tab S δ)) (withOwnersM δ σ Qa)) :=
  law2_of_pj hLR hL hσ hx hP hadm hQa hds hbs hβ (BComp.toPJ (rowLin_self hLR) hd) hB hΔ hctx hQ
    ls

end

end Law2

end
