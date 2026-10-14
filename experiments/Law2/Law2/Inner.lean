import Law2.Bridge

/-!
# Law2 — stops inside the borrower: the piece beside a handler installed inside it

A borrower may install a handler inside the region its lends span. An operation that handler
catches stops inside the borrower: it crosses no lend, so the stop drops no view. What the stop
hands the handler is the operation's argument and the continuation, and the handler's clause may
hold the continuation across later stops of the lenders' row, at which every view is dropped. So
the continuation is re-lendable as a closure that stops is (`RelendableS`): its share splits up
front into the views it holds and a part in `[top]` that, at every re-lend and on every answer
the operation admits, is the piece again.

* `InStop`, `bodyH`, `OpenH`: D16.1's piece with these stops beside the lenders' full-depth ones
  (`StopAt`). The relations of the operations caught inside are a parameter (`RI`); where none is
  caught the piece is D16.1's (`openS_of_openH`).
* `bodyH_bind`, `openH_bind`: the stacked bind at this piece. At a full-depth stop the frame
  freezes as in `Law2/Bridge.lean`; at a stop inside, the frame keeps its views and joins the
  continuation (`relendableS_sep`), since the continuation runs again either at the same lifetimes
  or at a re-lend of them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

/-- The argument and answer relations of an operation caught inside the borrower, read at the
stack's lifetimes. -/
abbrev InRel := (List Life → List SRec → Val → WProp) × (List Life → List SRec → Val → WProp)

section
variable {δ : LSub} {σ : LStack}

theorem relendableS_mono' {seen : List BoCa.Loc} {P P' : List Life → List SRec → WProp}
    (h : ∀ αs ls, Entails (P αs ls) (P' αs ls)) {αs : List Life} {ls : List SRec} :
    Entails (RelendableS δ seen σ P αs ls) (RelendableS δ seen σ P' αs ls) := by
  rintro ρ ⟨ds, ρz, ρn, hc, hn, hz, hth⟩
  exact ⟨ds, ρz, ρn, hc, hn, hz,
    fun ls' he αs' hr => wand_mono_right (h αs' ls') ρz (hth ls' he αs' hr)⟩

/-- `RelendableS` along re-lends of the current lifetimes only. -/
theorem relendableS_mono_rel {seen : List BoCa.Loc} {P P' : List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec}
    (h : ∀ αs' ls', ReLend αs' αs → Entails (P αs' ls') (P' αs' ls')) :
    Entails (RelendableS δ seen σ P αs ls) (RelendableS δ seen σ P' αs ls) := by
  rintro ρ ⟨ds, ρz, ρn, hc, hn, hz, hth⟩
  exact ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr =>
    wand_mono_right (h αs' ls' hr) ρz (hth ls' he αs' hr)⟩

end

/-! ### The piece -/

section
variable {δ : LSub} {σ : LStack} {To : OpTab} {RI : UInt32 → UInt32 → Option InRel}

/-- **A stop inside the borrower**: `perform (n, (i, v))` under a context free of a handler of
`n`, at an operation a handler installed inside the borrower catches (`RI n i = some P`). It
crosses no lend: no view is dropped. The argument is in `P.1`; the continuation's share is
re-lendable, and at every re-lend, on every answer in `P.2`, it is the piece at depth `0`. -/
def InStop (δ : LSub) (σ : LStack) (RI : UInt32 → UInt32 → Option InRel) (X : XT)
    (αs : List Life) (ls : List SRec) (t : Expr) : WProp :=
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (P : InRel) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ RI n i = some P⌝ ⋆
        (P.1 αs ls v ⋆ RelendableS δ [] σ (fun αs' ls' ρ => ∀ w,
          (P.2 αs' ls' w ─⋆ X 0 [] [] αs' ls' (K.plug (.val w))) ρ) αs ls)

/-- One run with the stack open at `αs`: an answer in `Q αs`, a stop of the lenders' row at the
full depth, or a stop inside the borrower. -/
def bodyH (δ : LSub) (σ : LStack) (To : OpTab) (RI : UInt32 → UInt32 → Option InRel)
    (Q : List Life → List SRec → Val → WProp) (X : XT) (αs : List Life) :
    List SRec → Expr → WProp :=
  fun ls e => wpG ls e fun ls'' t ρ =>
    valPost (Q αs) ls'' t ρ ∨ StopAt σ To X αs ls'' t ρ ∨ InStop δ σ RI X αs ls'' t ρ

/-- One unfolding, as `openFS`: the entries ended re-lent below the lifetimes they ended, the
share in `[top]` and handed the views its drops ask for. -/
def openFH (δ : LSub) (σ : LStack) (To : OpTab) (RI : UInt32 → UInt32 → Option InRel)
    (Q : List Life → List SRec → Val → WProp) (X : XT) : XT := fun k ds αi αo ls e ρ =>
  ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) (αi' ++ αo) →
    boxTop αi' (vwS δ [] (σ.take k) ds αi' ls ─⋆ bodyH δ σ To RI Q X (αi' ++ αo) ls e) ρ

/-- **The piece with stops inside**: the least fixed point of `openFH`, in `Prop` as `OpenS`. -/
def OpenH (δ : LSub) (σ : LStack) (To : OpTab) (RI : UInt32 → UInt32 → Option InRel)
    (Q : List Life → List SRec → Val → WProp) : XT := fun k ds αi αo ls e ρ =>
  ∀ X : XT, (∀ k ds αi αo ls e ρ, openFH δ σ To RI Q X k ds αi αo ls e ρ → X k ds αi αo ls e ρ) →
    X k ds αi αo ls e ρ

theorem StopAt.mono_full {X X' : XT} {αs : List Life}
    (hX : ∀ ds ls e ρ, X σ.length ds αs [] ls e ρ → X' σ.length ds αs [] ls e ρ)
    {ls : List SRec} {t : Expr} : Entails (StopAt σ To X αs ls t) (StopAt σ To X' αs ls t) := by
  rintro ρ ⟨ds, ρ₁, ρ₂, hc, hd, hb, hs⟩
  exact ⟨ds, ρ₁, ρ₂, hc, hd, opTable_mono _ _ _ _ _ _ (fun _ _ _ h => hX _ _ _ _ h) hb, hs⟩

theorem InStop.mono_rel {X X' : XT} {αs : List Life}
    (hX : ∀ αs' ls e ρ, ReLend αs' αs → X 0 [] [] αs' ls e ρ → X' 0 [] [] αs' ls e ρ)
    {ls : List SRec} {t : Expr} :
    Entails (InStop δ σ RI X αs ls t) (InStop δ σ RI X' αs ls t) := by
  rintro ρ ⟨K, n, i, v, P, h⟩
  obtain ⟨hp, ρa, ρk, hc, hA, hk⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, P, pure_sep_mk hp ⟨ρa, ρk, hc, hA,
    relendableS_mono_rel (P' := fun αs' ls' ρ => ∀ w,
        (P.2 αs' ls' w ─⋆ X' 0 [] [] αs' ls' (K.plug (.val w))) ρ)
      (fun αs' _ hr τ hτ w => wand_mono_right (fun _ h => hX _ _ _ _ hr h) τ (hτ w)) ρk hk⟩⟩

/-- `bodyH` along its answer and its continuations, at the indices a run reads them at. -/
theorem bodyH_mono' {Q Q' : List Life → List SRec → Val → WProp} {X X' : XT} {αs : List Life}
    (hQ : ∀ ls v, Entails (Q αs ls v) (Q' αs ls v))
    (hX : ∀ ds ls e ρ, X σ.length ds αs [] ls e ρ → X' σ.length ds αs [] ls e ρ)
    (hX₀ : ∀ αs' ls e ρ, ReLend αs' αs → X 0 [] [] αs' ls e ρ → X' 0 [] [] αs' ls e ρ)
    {ls : List SRec} {e : Expr} :
    Entails (bodyH δ σ To RI Q X αs ls e) (bodyH δ σ To RI Q' X' αs ls e) :=
  fun _ h => wpG_mono (fun _ _ _ hq => hq.imp (fun ⟨v, he, hv⟩ => ⟨v, he, hQ _ _ _ hv⟩)
    (Or.imp (StopAt.mono_full hX _) (InStop.mono_rel hX₀ _))) h

variable {Q : List Life → List SRec → Val → WProp}

theorem bodyH_mono {X X' : XT}
    (hX : ∀ k ds αi αo ls e ρ, X k ds αi αo ls e ρ → X' k ds αi αo ls e ρ) {αs : List Life}
    {ls : List SRec} {e : Expr} :
    Entails (bodyH δ σ To RI Q X αs ls e) (bodyH δ σ To RI Q X' αs ls e) :=
  bodyH_mono' (fun _ _ _ h => h) (fun _ _ _ _ h => hX _ _ _ _ _ _ _ h)
    (fun _ _ _ _ _ h => hX _ _ _ _ _ _ _ h)

/-- **Positivity**: the continuation variable occurs only positively in one unfolding. -/
theorem openFH_mono {X X' : XT}
    (hX : ∀ k ds αi αo ls e ρ, X k ds αi αo ls e ρ → X' k ds αi αo ls e ρ) {k : Nat}
    {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr} :
    Entails (openFH δ σ To RI Q X k ds αi αo ls e) (openFH δ σ To RI Q X' k ds αi αo ls e) :=
  fun _ h αi' h₁ h₂ => boxTop_mono (wand_mono_right (bodyH_mono hX)) _ (h αi' h₁ h₂)

theorem openH_fold {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : openFH δ σ To RI Q (OpenH δ σ To RI Q) k ds αi αo ls e ρ) :
    OpenH δ σ To RI Q k ds αi αo ls e ρ :=
  fun X hX => hX _ _ _ _ _ _ ρ (openFH_mono (fun _ _ _ _ _ _ _ h' => h' X hX) ρ h)

theorem openH_unfold {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : OpenH δ σ To RI Q k ds αi αo ls e ρ) :
    openFH δ σ To RI Q (OpenH δ σ To RI Q) k ds αi αo ls e ρ :=
  h (openFH δ σ To RI Q (OpenH δ σ To RI Q))
    (fun _ _ _ _ _ _ _ h' => openFH_mono (fun _ _ _ _ _ _ _ h'' => openH_fold h'') _ h')

/-- **At depth `0`** an unfolding re-lends nothing: it is one run at the lifetimes it keeps
open. -/
theorem openFH_zero {X : XT} {αo : List Life} {ls : List SRec} {e : Expr} {ρ : WRes} :
    openFH δ σ To RI Q X 0 [] [] αo ls e ρ ↔
      (List.IsChain (· < ·) αo → bodyH δ σ To RI Q X αo ls e ρ) := by
  have hv : vwS δ [] (σ.take 0) [] [] ls PMap.empty := by
    rw [List.take_zero]; exact ⟨rfl, trivial⟩
  constructor
  · intro h hch
    exact (h [] .nil hch).1 PMap.empty ρ hv (ResU.comp_empty_right ρ)
  · intro h αi' hlt hch
    obtain rfl : αi' = [] := List.forall₂_nil_right_iff.mp hlt
    refine ⟨fun w W hw hc => ?_, stratS_nil ρ⟩
    rw [List.take_zero] at hw
    obtain ⟨rfl, -⟩ := hw
    rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ)]
    exact h hch

theorem openH_zero_fold {αo : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : List.IsChain (· < ·) αo → bodyH δ σ To RI Q (OpenH δ σ To RI Q) αo ls e ρ) :
    OpenH δ σ To RI Q 0 [] [] αo ls e ρ :=
  openH_fold (openFH_zero.mpr h)

theorem openH_zero_unfold {αo : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenH δ σ To RI Q 0 [] [] αo ls e ρ) (hch : List.IsChain (· < ·) αo) :
    bodyH δ σ To RI Q (OpenH δ σ To RI Q) αo ls e ρ :=
  openFH_zero.mp (openH_unfold h) hch

/-- **With nothing caught inside, the piece is D16.1's**, when every operation of the lenders' row
crosses every entry: a full-depth stop is a stop of `OpenS` (`stopS_of_stopAt`). -/
theorem openS_of_openH (hx : AllCross σ To) (hRI : ∀ n i, RI n i = none) {ds : List Bool}
    {αi : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenH δ σ To RI Q σ.length ds αi [] ls e ρ) :
    OpenS δ σ To Q σ.length ds αi [] ls e ρ := by
  let Mot : XT := fun k ds αi αo ls e ρ => k = σ.length → αo = [] →
    OpenS δ σ To Q σ.length ds αi [] ls e ρ
  refine h Mot ?_ rfl rfl
  rintro k ds αi αo ls e ρ hF rfl rfl
  refine openS_fold fun αi' hlt hch => ?_
  have hFα := hF αi' hlt hch
  rw [List.append_nil] at hch hFα ⊢
  rw [List.take_length] at hFα ⊢
  refine ⟨fun w W hw hc => ?_, hFα.2⟩
  have hlen : αi'.length = σ.length := (vwS_length hw).2
  refine wpG_mono (fun ls'' t τ hq => ?_) (hFα.1 w W hw hc)
  rcases hq with hv | hs | hin
  · exact Or.inl hv
  · exact Or.inr (stopS_of_stopAt hx hlen hch
      (StopAt.mono_full (fun _ _ _ _ hM => hM rfl rfl) τ hs))
  · obtain ⟨K, n, i, v, P, hp⟩ := hin
    obtain ⟨⟨-, -, hP⟩, -⟩ := pure_sep_iff.mp hp
    rw [hRI] at hP; cases hP

end

/-! ### Bind at the piece -/

section bind
variable {δ : LSub} {σ : LStack} {To : OpTab} {RI : UInt32 → UInt32 → Option InRel}

/-- **Bind at one run.** `K` pure around a run at `αs`, the live frame `Fr αs` carried through it.
At an answer `K[v]` runs on at the same lifetimes (`hk`). The frame splits into views and a
frozen part (`hfz`), which thaws to the live frame at every re-lend (`hthaw`). At a full-depth
stop its views are dropped beside the piece's (`dropS_join`) and its frozen part joins every
continuation (`hX`); at a stop inside, the whole frame joins the continuation, re-lendable
(`relendableS_sep`, `hX₀`). -/
theorem bodyH_bind (hLR : LinResume To) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (Fr : List Life → List SRec → WProp) (Fz : List Life → List Bool → List SRec → WProp)
    (hFs : ∀ αs ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr αs ls) (Fr αs ls'))
    (hFe : ∀ αs d ls ls' ρ, Ext ls ls' ρ → Fz αs d ls ρ → Fz αs d ls' ρ)
    (hFo : ∀ αs d ls ρ, Fz αs d ls ρ → stratS αs ρ)
    {Q₁ Q : List Life → List SRec → Val → WProp} {X₁ X : XT} {αs : List Life}
    (hfz : ∀ ls ρ, Fr αs ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz αs d ls ρz ∧ vwS δ [] σ d αs ls ρn)
    (hthaw : ∀ αs' d ls ρz ρv ρ, ReLend αs' αs → Fz αs d ls ρz → vwS δ [] σ d αs' ls ρv →
      ResU.CompS ρz ρv ρ → Fr αs' ls ρ)
    (hX : ∀ d₁ d₂ ls e ρ₁ ρz ρ, MutDisj [] σ d₁ d₂ → d₁.length = σ.length →
      d₂.length = σ.length → X₁ σ.length d₁ αs [] ls e ρ₁ → Fz αs d₂ ls ρz →
      ResU.CompS ρ₁ ρz ρ → X σ.length (List.zipWith (· || ·) d₁ d₂) αs [] ls (K.plug e) ρ)
    (hX₀ : ∀ αs' ls e ρ₁ ρf ρ, ReLend αs' αs → X₁ 0 [] [] αs' ls e ρ₁ → Fr αs' ls ρf →
      ResU.CompS ρ₁ ρf ρ → X 0 [] [] αs' ls (K.plug e) ρ)
    (hk : ∀ ls v, Entails (Q₁ αs ls v ⋆ Fr αs ls) (bodyH δ σ To RI Q X αs ls (K.plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ₁ ρf ρ : WRes}
    (h : bodyH δ σ To RI Q₁ X₁ αs ls e ρ₁) (hf : Fr αs ls ρf) (hc : ResU.CompS ρ₁ ρf ρ) :
    bodyH δ σ To RI Q X αs ls (K.plug e) ρ := by
  refine wpG_garbage ?_
  refine wpG_bind K e ls _ ρ ?_
  refine wpG_mono (fun ls' t τ ht => ?_) (wpG_frame (Fr αs) (hFs αs ls) ρ ⟨ρ₁, ρf, hc, h, hf⟩)
  obtain ⟨τ₁, τ₂, hcτ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hs | hin
  · exact wpG_mono (fun _ _ τ' hq => ⟨τ', PMap.empty, ResU.comp_empty_right τ', noOwn_empty, hq⟩)
      (hk ls' v τ ⟨τ₁, τ₂, hcτ, hv, hF'⟩)
  · -- a full-depth stop: the frame's views are dropped, its frozen part joins the continuations
    refine wpG_here _ _ _ τ
      ⟨τ, PMap.empty, ResU.comp_empty_right τ, noOwn_empty, Or.inr (Or.inl ?_)⟩
    obtain ⟨d₂, ρz, ρn, hczn, hz, hvn⟩ := hfz ls' τ₂ hF'
    have hdn := dropS_of_vwS hvn
    have hl₂ : d₂.length = σ.length := dropS_length hdn
    obtain ⟨d₁, ρa, ρg, hca, hda, hb⟩ := hs
    have hl₁ : d₁.length = σ.length := dropS_length hda
    obtain ⟨ac, bd, hac, hbd, hρ⟩ := compS_four hca (ResU.CompS.comm hczn) hcτ
    obtain ⟨hdrop, hdisj⟩ := dropS_join hda hdn hac
    refine ⟨_, ac, bd, hρ, hdrop, ?_, fun a ha => (outlives_comp hbd a).mpr
      ⟨hb.2 a ha, hFo _ _ _ _ hz a ha⟩⟩
    exact opTable_frame hLR K hH (Fz αs d₂) (hFe αs d₂)
      (fun ls e ρ₁ ρz ρ h₁ h₂ h₃ => hX d₁ d₂ ls e ρ₁ ρz ρ hdisj hl₁ hl₂ h₁ h₂ h₃) hb.1 hz hbd
  · -- a stop inside: the frame keeps its views and joins the continuation
    refine wpG_here _ _ _ τ
      ⟨τ, PMap.empty, ResU.comp_empty_right τ, noOwn_empty, Or.inr (Or.inr ?_)⟩
    obtain ⟨K₁, n, i, v, P, hp⟩ := hin
    obtain ⟨⟨rfl, hK₁, hP⟩, ρa, ρk, hcak, hA, hkont⟩ := pure_sep_iff.mp hp
    have hFR : RelendableS δ [] σ (fun αs' ls'' => Fr αs' ls'') αs ls' τ₂ := by
      obtain ⟨d, ρz, ρn, hcz, hz, hn⟩ := hfz ls' τ₂ hF'
      exact ⟨d, ρz, ρn, hcz, hn, hFo _ _ _ _ hz, fun ls'' he αs' hr ρv υ hv hcv =>
        hthaw αs' d ls'' ρz ρv υ hr (hFe _ _ _ _ _ he hz) hv hcv⟩
    obtain ⟨ρk', hk', hcak'⟩ := compS_reassoc hcak hcτ
    refine ⟨K.comp K₁, n, i, v, P, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hP⟩
      ⟨ρa, ρk', hcak', hA, ?_⟩⟩
    · rw [hasHnd_comp, hH, hK₁]; rfl
    · refine relendableS_mono_rel (P' := fun αs' ls'' ρ => ∀ w,
          (P.2 αs' ls'' w ─⋆ X 0 [] [] αs' ls'' ((K.comp K₁).plug (.val w))) ρ)
        (fun αs' ls'' hr υ hυ w => ?_) ρk' (relendableS_sep ρk' ⟨ρk, τ₂, hk', hkont, hFR⟩)
      obtain ⟨υ₁, υ₂, hcυ, h₁, h₂⟩ := hυ
      intro υw υ' hw hcw
      obtain ⟨x, hx, hxυ⟩ := compS_exch hcυ hcw
      rw [Kont.plug_comp]
      exact hX₀ αs' ls'' _ x υ₂ υ' hr (h₁ w υw x hw hx) h₂ hxυ

/-- **Bind at the piece.** `K` pure around a piece, the frame frozen at its full-depth stops
(first conjunct) and live at its stops inside (second conjunct). By induction on the inner
piece's `OpenH`: at each unfolding the views go to the piece and the frame by their drops
(`vwS_split`), the frozen frame thaws at the re-lend (`hthaw`), and one run is `bodyH_bind`, whose
continuations are the two conjuncts again. No step reads the stack's length. -/
theorem openH_bind (hLR : LinResume To) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (Fr : List Life → List SRec → WProp) (Fz : List Life → List Bool → List SRec → WProp)
    (hFs : ∀ αs ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr αs ls) (Fr αs ls'))
    (hFe : ∀ αs d ls ls' ρ, Ext ls ls' ρ → Fz αs d ls ρ → Fz αs d ls' ρ)
    (hFo : ∀ αs d ls ρ, Fz αs d ls ρ → stratS αs ρ)
    (hfz : ∀ αs, αs.length = σ.length → List.IsChain (· < ·) αs → ∀ ls ρ, Fr αs ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz αs d ls ρz ∧ vwS δ [] σ d αs ls ρn)
    (hthaw : ∀ αs αs' d ls ρz ρv ρ, ReLend αs' αs → Fz αs d ls ρz →
      vwS δ [] σ d αs' ls ρv → ResU.CompS ρz ρv ρ → Fr αs' ls ρ)
    {Q₁ Q : List Life → List SRec → Val → WProp} {B : List Life}
    (hk : ∀ αs, List.Forall₂ (· ≤ ·) αs B → αs.length = σ.length → List.IsChain (· < ·) αs →
      ∀ ls v, Entails (Q₁ αs ls v ⋆ Fr αs ls)
        (bodyH δ σ To RI Q (OpenH δ σ To RI Q) αs ls (K.plug (.val v)))) :
    (∀ {d₁ d₂ : List Bool} {αi : List Life} {ls : List SRec} {e : Expr} {ρ₁ ρz ρ : WRes},
      MutDisj [] σ d₁ d₂ → d₁.length = σ.length → d₂.length = σ.length →
      List.Forall₂ (· ≤ ·) αi B → OpenH δ σ To RI Q₁ σ.length d₁ αi [] ls e ρ₁ →
      Fz αi d₂ ls ρz → ResU.CompS ρ₁ ρz ρ →
      OpenH δ σ To RI Q σ.length (List.zipWith (· || ·) d₁ d₂) αi [] ls (K.plug e) ρ) ∧
    (∀ {αo : List Life} {ls : List SRec} {e : Expr} {ρ₁ ρf ρ : WRes},
      αo.length = σ.length → List.Forall₂ (· ≤ ·) αo B →
      OpenH δ σ To RI Q₁ 0 [] [] αo ls e ρ₁ → Fr αo ls ρf → ResU.CompS ρ₁ ρf ρ →
      OpenH δ σ To RI Q 0 [] [] αo ls (K.plug e) ρ) := by
  let M₁ : XT := fun k d₁ αi αo ls e ρ₁ => k = σ.length → αo = [] →
    List.Forall₂ (· ≤ ·) αi B → ∀ d₂ ρz ρ, MutDisj [] σ d₁ d₂ → d₁.length = σ.length →
      d₂.length = σ.length → Fz αi d₂ ls ρz → ResU.CompS ρ₁ ρz ρ →
      OpenH δ σ To RI Q σ.length (List.zipWith (· || ·) d₁ d₂) αi [] ls (K.plug e) ρ
  let M₀ : XT := fun k d₁ αi αo ls e ρ₁ => k = 0 → d₁ = [] → αi = [] →
    αo.length = σ.length → List.Forall₂ (· ≤ ·) αo B → ∀ ρf ρ, Fr αo ls ρf →
      ResU.CompS ρ₁ ρf ρ → OpenH δ σ To RI Q 0 [] [] αo ls (K.plug e) ρ
  let Mot : XT := fun k d₁ αi αo ls e ρ₁ => M₁ k d₁ αi αo ls e ρ₁ ∧ M₀ k d₁ αi αo ls e ρ₁
  have run : ∀ αs, List.Forall₂ (· ≤ ·) αs B → αs.length = σ.length →
      List.IsChain (· < ·) αs → ∀ ls e ρ₁ ρf ρ, bodyH δ σ To RI Q₁ Mot αs ls e ρ₁ →
        Fr αs ls ρf → ResU.CompS ρ₁ ρf ρ →
          bodyH δ σ To RI Q (OpenH δ σ To RI Q) αs ls (K.plug e) ρ := by
    intro αs hB hlen hch ls e ρ₁ ρf ρ hb hf hc
    exact bodyH_bind hLR K hH Fr Fz hFs hFe hFo (hfz αs hlen hch)
      (fun αs' d ls ρz ρv ρ hr hz hv hc' => hthaw αs αs' d ls ρz ρv ρ hr hz hv hc')
      (fun d₁ d₂ ls e ρ₁ ρz ρ hd hl₁ hl₂ hM hz hc' => hM.1 rfl rfl hB d₂ ρz ρ hd hl₁ hl₂ hz hc')
      (fun αs' ls e ρ₁ ρf ρ hr hM hf' hc' => hM.2 rfl rfl rfl
        ((List.Forall₂.length_eq hr.1).trans hlen) (forall₂_le_trans hr.1 hB) ρf ρ hf' hc')
      (hk αs hB hlen hch) hb hf hc
  have key : ∀ k d₁ αi αo ls e ρ₁, openFH δ σ To RI Q₁ Mot k d₁ αi αo ls e ρ₁ →
      Mot k d₁ αi αo ls e ρ₁ := by
    intro k d₁ αi αo ls e ρ₁ hF
    refine ⟨?_, ?_⟩
    · rintro rfl rfl hB d₂ ρz ρ hd hl₁ hl₂ hz hc
      refine openH_fold fun αi' hlt hch => ?_
      rw [List.append_nil] at hch ⊢
      rw [List.take_length]
      have hFα := hF αi' hlt (by rw [List.append_nil]; exact hch)
      rw [List.take_length, List.append_nil] at hFα
      refine ⟨fun ρv W hv hcv => ?_, fun a ha => (outlives_comp hc a).mpr
        ⟨hFα.2 a ha, stratS_mono (reLend_of_lt hlt hch) (hFo _ _ _ _ hz) a ha⟩⟩
      have hlen : αi'.length = σ.length := (vwS_length hv).2
      obtain ⟨ρv₁, ρv₂, hcv₁₂, hv₁, hv₂⟩ := vwS_split hd hl₁ hl₂ hv
      obtain ⟨x, y, hxc, hy, hxy⟩ := compS_four hc hcv₁₂ hcv
      have hb := hFα.1 ρv₁ x hv₁ hxc
      have hfr := hthaw αi αi' d₂ ls ρz ρv₂ y (reLend_of_lt hlt hch) hz hv₂ hy
      have hB' : List.Forall₂ (· ≤ ·) αi' B :=
        forall₂_le_trans (hlt.imp fun _ _ => le_of_lt) hB
      exact run αi' hB' hlen hch ls e x y W hb hfr hxy
    · rintro rfl rfl rfl hlen hB ρf ρ hf hc
      exact openH_zero_fold fun hch =>
        run αo hB hlen hch ls e ρ₁ ρf ρ (openFH_zero.mp hF hch) hf hc
  exact ⟨fun hd hl₁ hl₂ hB h hz hc => (h Mot key).1 rfl rfl hB _ _ _ hd hl₁ hl₂ hz hc,
    fun hlen hB h hf hc => (h Mot key).2 rfl rfl rfl hlen hB _ _ hf hc⟩

end bind

end Law2

end
