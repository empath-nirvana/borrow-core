import GhostEnd.Values

/-!
# GhostEnd — typed borrowers whose frames carry the lend in values

`RBodyT` is `RBody` (`Typed.lean`) with three changes:

* its context is consistent with the lend table (`TabAt`), and so is its answer. Every run keeps
  the table (`wpTS_tabAt`), so a pure piece needs nothing more than its typing;
* whether a piece needs the view at the next lend is what its last stop dropped (`OpenD`), not a
  flag on its context;
* each lend is below the last.

The rules are `RBody`'s. `rbodyT_letF` takes `FrameThawsD` of the frame in place of
`FrameThaws`. `lok_thaws` discharges it for every frame of `LOk` slots: `m` itself, `m` threaded
through `⊗` and `⊕`, outer views weakened to `'x`, and values free of `'x` that outlive it. This
closes gap 1 of `RBodyOfTyped` for data. A frame holding a closure is the next file's subject.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A piece's answer: `𝒱⟦A⟧` at the lend it answers at, consistent with the table. -/
def ansT (x : LifeVar) (δ : LSub) (l : BoCa.Loc) (A : VTy) : Life → List SRec → Val → WProp :=
  fun α ls v ρ => vC true A ls (δ.extend x α) v ρ ∧ TabAt l α ρ

/-- **A borrower piece**, the table kept. At every lend `α ⊏ @bδ`, from `𝒢⟦Γ, m⟧` at
`δ[x ↦ α]` consistent with the table, a run with the lend open at `α` whose stops owe `OpenD`. -/
def RBodyT (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (S : Row)
    (Γ : Ctx VTy) (ml : Bool) (E : Expr) (A : VTy) : Prop :=
  ∀ (δ : LSub), Δ.Models δ → ∀ (β : Life), b.interp δ = some β →
    ∀ (l : BoCa.Loc) (α : Life), α ⊏ β →
    ∀ (ls : List SRec) (γ : List Val) (ρ : WRes), γ.length = Γ.length → TabAt l α ρ →
      gDenC ls (δ.extend x α) (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ →
      bodyAtD (opTable (Row.tab S δ)) l T δ (ansT x δ l A)
        (OpenD (opTable (Row.tab S δ)) l T δ (ansT x δ l A)) α ls
        (substAll (γ ++ [Val.loc l]) E) ρ

section
variable {Tb : Table} {l : BoCa.Loc} {T : VTy} {δ : LSub}

/-- `OpenD` is monotone in its answer. -/
theorem openD_mono_Q (hTb : Tb.Mono) {Q Q' : Life → List SRec → Val → WProp}
    (hQ : ∀ α ls v ρ, Q α ls v ρ → Q' α ls v ρ) {β : Life} {d : Bool} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : OpenD Tb l T δ Q β d ls e ρ) : OpenD Tb l T δ Q' β d ls e ρ := by
  refine openD_ind (fun β d ls e ρ => OpenD Tb l T δ Q' β d ls e ρ) (fun β d ls e ρ hF => ?_) h
  refine openD_fold hTb fun α hα => box_mono (wand_mono_right fun σ hw => ?_) ρ (hF α hα)
  exact wpG_mono (fun _ _ _ hq => hq.imp (fun ⟨v, hv, hq⟩ => ⟨v, hv, hQ α _ _ _ hq⟩) id) hw

end

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {S : Row}

/-- **A pure piece**, by `fundamentalC`'s semantic judgment at `δ[x ↦ α]`; the run keeps the
table (`wpTS_tabAt`). -/
theorem rbodyT_ret (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ : Ctx VTy} {ml : Bool} {E : Expr} {A : VTy}
    (h : SemC (Δ.extend x b) (Γ ++ [mSlot x T ml]) E (.ret A)) : RBodyT Δ x b T S Γ ml E A := by
  intro δ hδ β hβ l α hα ls γ ρ _ ht hg
  refine bodyAtD_of_wpTS (wpTS_mono (P := fun ls' v ρ' =>
    TabAt l α ρ' ∧ vC true A ls' (δ.extend x α) v ρ') (Q := ansT x δ l A α)
    (fun _ _ _ h' => ⟨h'.2, h'.1⟩) ρ ?_)
  exact wpTS_tabAt l α ls _ _ ht (h (δ.extend x α) _ ls ρ (models_extend hδ hbx hΔx hβ hα) hg)

/-- **`perform`**: the stop, dropping nothing. The argument is closed data, so its resource is in
`[α]`; the owner handed back goes to the continuation, which answers `()` at the next lend. -/
theorem rbodyT_perform (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hS : Row.Resume S x) {Γ : Ctx VTy} {V : Expr} {o : OpSig}
    (hf : Row.find S o.n o.i = some o)
    (h : SemV (Δ.extend x b) (Γ ++ [mSlot x T false]) V o.A) :
    RBodyT Δ x b T S Γ false (performE (opArgE o.n o.i V)) o.B := by
  intro δ hδ β hβ l α hα ls γ ρ _ _ hg
  obtain ⟨ha, -, hq, hoB, hAx, hAo⟩ := hS o (Row.find_mem hf).1
  have hTb := opTable_mono (Row.tab S δ)
  change wpG ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll (γ ++ [Val.loc l]) V)) _ ρ
  refine wpG_bind_pure _ _ ls _ ρ (wpTS_mono (fun ls' v σ hv => ?_) ρ
    (h (δ.extend x α) _ ls ρ (models_extend hδ hbx hΔx hβ hα) hg))
  have hv' : vC true o.A ls' δ v σ := by rw [vC_extend_of_not_free hAx] at hv; exact hv
  have hσ : σ.InStratum α := vC_outlives (Δ := LifeCtx.empty) (a := .var x) (models_empty_any _)
    (interp_ext_self δ x α) (hAo _ _) true ls' v σ hv
  refine wpG_here _ _ _ σ (Or.inr ⟨false, PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩,
    fun w ρa ρb hown hcab ρc ρd hTw hccd => ?_, hσ⟩)
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  refine Or.inl ⟨.hole, o.n, o.i, v, o.ent δ,
    pure_sep_mk ⟨rfl, rfl, by simp [Row.tab, hf], ha⟩ ⟨σ, s, hρs, hv', ?_⟩⟩
  refine ⟨fun hu => absurd (hq.symm.trans hu) (by decide),
    fun ls'' hext => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  have hBw' : vC true .unit ls'' δ w' τ₁ := by simpa [OpSig.ent, hoB] using hBw
  obtain ⟨rfl, rfl⟩ := hBw'
  have e : s = τ₂ := (ResU.CompS.functional hcτ (ResU.comp_empty_right s)).symm
  subst e
  refine ⟨s, PMap.empty, ResU.comp_empty_right s,
    ⟨w, ρa, ρc, hs, hown, vC_local true T (hext.right hs) hTw⟩, ?_⟩
  refine openD_fold hTb fun α' _ => ⟨fun ρv σ' hv₀ hc' => ?_, ResU.inStratum_empty α'⟩
  obtain ⟨rfl, -⟩ := hv₀
  obtain rfl := eq_of_compS_empty_left hc'
  refine wpG_here _ _ _ _ (Or.inl ⟨Val.unit, rfl, ?_, tabAt_empty l α'⟩)
  show vC true o.B ls'' (δ.extend x α') Val.unit PMap.empty
  rw [hoB]; exact ⟨rfl, rfl⟩

/-- **`M to z. N`.** `N`'s context is the frame `(λz. N) [·]` around `M`. It is carried through
`M`'s run, frozen at each of `M`'s stops and thawed at each later lend (`openD_bind`), as
`FrameThawsD` says. At `M`'s answer `N` runs at the lend `M` answered at. The view is passed to
whichever froze the lend's cell. -/
theorem rbodyT_letF (hS : Row.Resume S x) {Γ Γ₁ Γ₂ : Ctx VTy} {ml ml₁ ml₂ : Bool} {M N : Expr}
    {A₁ A : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γ₁ ++ [mSlot x T ml₁]) (Γ₂ ++ [mSlot x T ml₂]))
    (hl₁ : Γ₁.length = Γ.length) (hl₂ : Γ₂.length = Γ.length)
    (hsafe : FrameThawsD Δ x b T Γ₂ ml₂)
    (hM : RBodyT Δ x b T S Γ₁ ml₁ M A₁) (hN : RBodyT Δ x b T S (⟨A₁, true⟩ :: Γ₂) ml₂ N A) :
    RBodyT Δ x b T S Γ ml (.app (.val (.lam N)) M) A := by
  intro δ hδ β hβ l α hα ls γ ρ hlen ht hg
  have hLR := hS.linResume δ
  have hTb := opTable_mono (Row.tab S δ)
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
  have hlen₂ : γ.length = Γ₂.length := hlen.trans hl₂.symm
  obtain ⟨Fz, hFe, hFo, hfz, hth⟩ := hsafe δ hδ β hβ l γ hlen₂
  let K : Kont := .appR (.val (.lam (Expr.psub 1 (γ ++ [Val.loc l]) N))) .hole
  have hK : ∀ n, K.HasHnd n = false := fun n => by simp [K, Kont.HasHnd]
  let Fr : Life → List SRec → WProp := fun α' ls ρ =>
    TabAt l α' ρ ∧ gDenC ls (δ.extend x α') (Γ₂ ++ [mSlot x T ml₂]) (γ ++ [Val.loc l]) ρ
  have hFs : ∀ α' ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α' ls) (Fr α' ls') :=
    fun _ _ _ hs _ h => ⟨h.1, gDenC_same hs h.2⟩
  have hfz' : ∀ α', α' ⊏ β → ∀ ls ρ, Fr α' ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz α' d ls ρz ∧ dropC l d ρn :=
    fun α' hα' ls ρ h => hfz α' hα' ls ρ h.1 h.2
  have hthaw : ∀ β' α' d₂ ls ρv ρz ρ, α' ⊏ β' → β' ≤ β → vwD l T δ d₂ α' ls ρv →
      Fz β' d₂ ls ρz → ResU.CompS ρv ρz ρ → Fr α' ls ρ :=
    fun β' α' d₂ ls ρv ρz ρ hα' _ hv hz hc => hth β' α' d₂ ls ρv ρz ρ hα' hv hz hc
  have hk : ∀ α', α' ⊏ β → ∀ ls v, Entails (ansT x δ l A₁ α' ls v ⋆ Fr α' ls)
      (bodyAtD (opTable (Row.tab S δ)) l T δ (ansT x δ l A)
        (OpenD (opTable (Row.tab S δ)) l T δ (ansT x δ l A)) α' ls (K.plug (.val v))) := by
    rintro α' hα' ls' v σ ⟨σ₁, σ₂, hcσ, ⟨hv, hvt⟩, ⟨hft, hfr⟩⟩
    obtain ⟨hlw, hgs⟩ := gDenC_iff.mp hfr
    refine wpG_step (fun μ => Step1N.head (Head.beta μ _ v) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    exact hN δ hδ β hβ l α' hα' ls' (v :: γ) σ (by simp [hlen₂])
      ((tabAt_comp hcσ).mpr ⟨hvt, hft⟩) (gDenC_mk hlw ⟨σ₁, σ₂, hcσ, hv, hgs⟩)
  exact bodyAtD_bind hLR K hK Fr Fz hFs hFe hFo (hfz' α hα)
    (fun d₁ d₂ _ _ _ _ _ hnd hx hz hcτ =>
      openD_bind hLR K hK β Fr Fz hFs hFe hFo hfz' hthaw hk (le_of_lt hα) hnd hx hz hcτ)
    (hk α hα) (hM δ hδ β hβ l α hα ls γ ρ₁ (hlen.trans hl₁.symm) ht₁ hg₁) ⟨ht₂, hg₂⟩ hc

/-- `rbodyT_letF` at a frame of `LOk` slots. -/
theorem rbodyT_let (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false) (hT : ¬ VFree x T)
    (hS : Row.Resume S x) {Γ Γ₁ Γ₂ : Ctx VTy} {ml ml₁ ml₂ : Bool} {M N : Expr} {A₁ A : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γ₁ ++ [mSlot x T ml₁]) (Γ₂ ++ [mSlot x T ml₂]))
    (hl₁ : Γ₁.length = Γ.length) (hl₂ : Γ₂.length = Γ.length)
    (hok : ∀ s ∈ Γ₂, s.live = true → LOk Δ x b T s.ty)
    (hM : RBodyT Δ x b T S Γ₁ ml₁ M A₁) (hN : RBodyT Δ x b T S (⟨A₁, true⟩ :: Γ₂) ml₂ N A) :
    RBodyT Δ x b T S Γ ml (.app (.val (.lam N)) M) A :=
  rbodyT_letF hS hsp hl₁ hl₂ (lok_thaws hbx hΔx hT hok ml₂) hM hN

/-- **`case V {inj₁ z. M₁ | inj₂ z. M₂}`**: `V` runs pure, keeping the table, and the branch taken
runs at the same lend. -/
theorem rbodyT_case (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ Γs Γb : Ctx VTy} {ml mls mlb : Bool} {V M₁ M₂ : Expr} {A B C : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γs ++ [mSlot x T mls]) (Γb ++ [mSlot x T mlb]))
    (hlb : Γb.length = Γ.length)
    (hV : SemV (Δ.extend x b) (Γs ++ [mSlot x T mls]) V (.sum A B))
    (h₁ : RBodyT Δ x b T S (⟨A, true⟩ :: Γb) mlb M₁ C)
    (h₂ : RBodyT Δ x b T S (⟨B, true⟩ :: Γb) mlb M₂ C) :
    RBodyT Δ x b T S Γ ml (.case V M₁ M₂) C := by
  intro δ hδ β hβ l α hα ls γ ρ hlen ht hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
  have hδα := models_extend hδ hbx hΔx hβ hα
  have hlenb : γ.length = Γb.length := hlen.trans hlb.symm
  refine wpG_bind_frame (.case .hole (Expr.psub 1 (γ ++ [Val.loc l]) M₁)
    (Expr.psub 1 (γ ++ [Val.loc l]) M₂)) _ ls
    (fun ls' v ρ => TabAt l α ρ ∧ vC true (.sum A B) ls' (δ.extend x α) v ρ)
    (fun ls' ρ => TabAt l α ρ ∧
      gDenC ls' (δ.extend x α) (Γb ++ [mSlot x T mlb]) (γ ++ [Val.loc l]) ρ) _
    (fun _ hs _ h => ⟨h.1, gDenC_same hs h.2⟩) ?_ ρ
    ⟨ρ₁, ρ₂, hc, wpTS_tabAt l α ls _ _ ht₁ (hV (δ.extend x α) _ ls ρ₁ hδα hg₁), ht₂, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, ⟨hst, hsum⟩, ⟨hft, hg₂'⟩⟩
  obtain ⟨hlw, hgs⟩ := gDenC_iff.mp hg₂'
  have htσ : TabAt l α σ := (tabAt_comp hcσ).mpr ⟨hst, hft⟩
  rcases hsum with ⟨w, hs⟩ | ⟨w, hs⟩
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    refine wpG_step (fun μ => Step1N.head (Head.case₁ μ w _ _) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    exact h₁ δ hδ β hβ l α hα ls' (w :: γ) σ (by simp [hlenb]) htσ
      (gDenC_mk hlw ⟨σ₁, σ₂, hcσ, hw, hgs⟩)
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    refine wpG_step (fun μ => Step1N.head (Head.case₂ μ w _ _) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    exact h₂ δ hδ β hβ l α hα ls' (w :: γ) σ (by simp [hlenb]) htσ
      (gDenC_mk hlw ⟨σ₁, σ₂, hcσ, hw, hgs⟩)

/-- **`V; M`** for `V : 1`: `V` runs pure, keeping the table, and `M` runs at the same lend. -/
theorem rbodyT_seq (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ Γ₁ Γ₂ : Ctx VTy} {ml ml₁ ml₂ : Bool} {V M : Expr} {A : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γ₁ ++ [mSlot x T ml₁]) (Γ₂ ++ [mSlot x T ml₂]))
    (hl₂ : Γ₂.length = Γ.length)
    (hV : SemV (Δ.extend x b) (Γ₁ ++ [mSlot x T ml₁]) V .unit)
    (hM : RBodyT Δ x b T S Γ₂ ml₂ M A) :
    RBodyT Δ x b T S Γ ml (.seq V M) A := by
  intro δ hδ β hβ l α hα ls γ ρ hlen ht hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
  have hδα := models_extend hδ hbx hΔx hβ hα
  refine wpG_bind_frame (.seq .hole (substAll (γ ++ [Val.loc l]) M)) _ ls
    (fun ls' v ρ => TabAt l α ρ ∧ vC true .unit ls' (δ.extend x α) v ρ)
    (fun ls' ρ => TabAt l α ρ ∧
      gDenC ls' (δ.extend x α) (Γ₂ ++ [mSlot x T ml₂]) (γ ++ [Val.loc l]) ρ) _
    (fun _ hs _ h => ⟨h.1, gDenC_same hs h.2⟩) ?_ ρ
    ⟨ρ₁, ρ₂, hc, wpTS_tabAt l α ls _ _ ht₁ (hV (δ.extend x α) _ ls ρ₁ hδα hg₁), ht₂, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, ⟨-, hu⟩, ⟨hft, hg₂'⟩⟩
  obtain ⟨rfl, rfl⟩ := hu
  obtain rfl := eq_of_compS_empty_left hcσ
  refine wpG_step (fun μ => Step1N.head (Head.seq μ _) rfl) ls' _ _ ?_
  exact hM δ hδ β hβ l α hα ls' γ _ (hlen.trans hl₂.symm) hft hg₂'

/-! ### The whole borrower -/

/-- A whole borrower `M`, `m` its only variable: at the first lend it is handed the view. -/
theorem openD_of_rbodyT (hT : ¬ VFree x T) {A : VTy} {M : Expr}
    {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (h : RBodyT Δ x b T S [] true M A) (l : BoCa.Loc) (ls : List SRec) :
    OpenD (opTable (Row.tab S δ)) l T δ (ansT x δ l A) β true ls (substAll [Val.loc l] M)
      PMap.empty :=
  openD_fold (opTable_mono _) fun α hα => ⟨fun ρm σ hm hc => by
    obtain rfl := eq_of_compS_empty_left hc
    exact h δ hδ β hβ l α hα ls [] _ rfl (tabAt_view hm)
      (gDenC_mk trivial (sep_emp_iff.mpr (mutView hT hm))),
    ResU.inStratum_empty α⟩

/-- A piece answering `['x] B` hands the owner back at its answer: it is `Relend`. -/
theorem relend_of_openD_box {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {B : VTy}
    (hB : ¬ VFree x B) {δ : LSub} {β : Life} {d : Bool} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenD Tb l T δ (ansT x δ l (.box (.var x) B)) β d ls e ρ) :
    Relend Tb l T δ (finPost l T B δ) ls e ρ := by
  refine relend_of_openD hTb (openD_mono_Q hTb ?_ h)
  rintro α ls' v ρ ⟨hv, -⟩
  obtain ⟨α', hα', hBr, hout⟩ := hv
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  refine ⟨fun w ρa ρb ha hcab ρc ρd hc hccd => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  exact ⟨s, ρ, ResU.CompS.comm hρs, ⟨w, ρa, ρc, hs, ha, hc⟩,
    by rwa [vC_extend_of_not_free hB] at hBr⟩

/-- **A borrower is re-lendable**, its frames carrying the lend in values. -/
theorem relend_of_rbodyT (hT : ¬ VFree x T) {B : VTy} (hB : ¬ VFree x B) {M : Expr}
    {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (h : RBodyT Δ x b T S [] true M (.box (.var x) B)) (l : BoCa.Loc) (ls : List SRec) :
    Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
      PMap.empty :=
  relend_of_openD_box (opTable_mono _) hB (openD_of_rbodyT hT hδ hβ h l ls)

/-- **O15.1's resume half for every borrower `RBodyT` reads.** -/
theorem withbor_of_rbodyT {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (hT : ¬ VFree x T) {B : VTy} (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    (hSd : Row.divB S = false) {M : Expr} (hM : closedAt 1 M = true)
    (h : RBodyT Δ x b T S [] true M (.box (.var x) B)) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (cC (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ hSd).mpr ?_
  exact withbor_relend (Row.tab S δ) (Row.tab_plainCancel S δ) hP _ v
    (relend_lam2 (opTable_mono _) hM (relend_of_rbodyT hT hB hδ hβ h l ls)) ρ hρ

end

/-! ### The general case, reduced -/

/-- **Not derived.** The fundamental lemma for `RBodyT`. -/
def RBodyTOfTyped : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (S : Row) (Γ : Ctx VTy)
    (ml : Bool) (E : Expr) (A : VTy),
    Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) → ¬ VFree x T → Row.Resume S x →
    CDerives (Δ.extend x b) (Γ ++ [mSlot x T ml]) E (.comp (CTy.effOf S A)) →
    RBodyT Δ x b T S Γ ml E A

/-- **`RelendOfTyped` from `RBodyTOfTyped`**, at a defined bound. -/
theorem relendOfTyped_of_rbodyTOfTyped (H : RBodyTOfTyped) :
    ∀ (Δ : LifeCtx) (δ : LSub) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (S : Row)
      (M : Expr), Δ.Models δ → (∃ β, b.interp δ = some β) → Δ.find? x = none →
      b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
      ¬ VFree x T → ¬ VFree x B → Row.Resume S x →
      CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
        (.comp (CTy.effOf S (.box (.var x) B))) →
      ∀ (l : BoCa.Loc) (ls : List SRec),
        Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
          PMap.empty := by
  intro Δ δ x b T B S M hδ ⟨β, hβ⟩ hx hbx hΔx hT hB hS hD l ls
  exact relend_of_rbodyT hT hB hδ hβ (H Δ x b T S [] true M _ hx hbx hΔx hT hS hD) l ls

end GhostEnd
