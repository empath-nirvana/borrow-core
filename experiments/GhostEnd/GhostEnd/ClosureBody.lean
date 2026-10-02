import GhostEnd.Closures

/-!
# GhostEnd — borrowers over typed contexts: closures held across a stop

`RBodyC` is `RBodyT` (`TypedD.lean`) with its context read as typed values (`TVG`, the kernel
invariant at the values the borrower holds) in place of `𝒢⟦Γ⟧`. A frame spanning a stop then
freezes and thaws by `tvg_freeze` and `tvg_thaw`, whatever it holds: the borrow, pairs and sums
of typed values, data outliving `'x`, and closures over typed environments, which are
re-derived at each lend from their own typings (`tv_sound`). No `LOk` or `StopSafe` premise is
needed at a frame.

The answer relation `Ans` is a parameter: a piece whose answer a later frame holds answers a
typed value (`ansTV`); any other answers in the relation (`ansT`).

* `rbodyC_ret`: a pure piece, by `fundamentalC`, from the context's relation (`tv_sound`);
* `rbodyC_thunk`: `thunk M`, a closure over the whole context, typed by its derivation;
* `rbodyC_perform`: the stop, answering `()`;
* `rbodyC_let`: `M to z. N`, the frame frozen and thawed as typed values;
* `relend_of_rbodyC`, `withbor_of_rbodyC`: the whole borrower.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {δ : LSub} {l : BoCa.Loc}

mutual
/-- A live typed value has dropped nothing. -/
theorem tv_live_flag : ∀ {fz α A ls v d ρ}, TV Δ x b T δ l fz α A ls v d ρ → fz = false →
    d = false
  | _, _, _, _, _, _, _, .atomL _ _, _ => rfl
  | _, _, _, _, _, _, _, .atomF _ _, hf => absurd hf (by decide)
  | _, _, _, _, _, _, _, .pair h₁ h₂ _ _, hf => by
      rw [tv_live_flag h₁ hf, tv_live_flag h₂ hf]; rfl
  | _, _, _, _, _, _, _, .inl h, hf => tv_live_flag h hf
  | _, _, _, _, _, _, _, .inr h, hf => tv_live_flag h hf
  | _, _, _, _, _, _, _, .cloF _ h, hf => tvg_live_flag h hf
  | _, _, _, _, _, _, _, .cloV _ _ h, hf => tvg_live_flag h hf
  | _, _, _, _, _, _, _, .const _, _ => rfl
theorem tvg_live_flag : ∀ {fz α Γ γ ls d ρ}, TVG Δ x b T δ l fz α Γ γ ls d ρ → fz = false →
    d = false
  | _, _, _, _, _, _, _, .nil, _ => rfl
  | _, _, _, _, _, _, _, .dead h, hf => tvg_live_flag h hf
  | _, _, _, _, _, _, _, .live h₁ h₂ _ _, hf => by
      rw [tv_live_flag h₁ hf, tvg_live_flag h₂ hf]; rfl
end

/-- **A typed context splits** as the kernel's context split does. A persistent slot goes to
both sides: its resource is empty (`vP_empty_of_persistent` at `tv_sound`). -/
theorem tvg_split {α : Life} (hδα : (Δ.extend x b).Models (δ.extend x α)) {ls : List SRec} :
    ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → ∀ {γ : List Val} {d : Bool} {ρ : WRes},
      TVG Δ x b T δ l false α Γ γ ls d ρ →
      ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ TVG Δ x b T δ l false α Γ₁ γ ls false ρ₁ ∧
        TVG Δ x b T δ l false α Γ₂ γ ls false ρ₂ := by
  intro Γ Γ₁ Γ₂ hsp
  induction hsp with
  | nil =>
      intro γ d ρ h
      cases h
      exact ⟨PMap.empty, PMap.empty, compS_empty_left _, .nil, .nil⟩
  | left _ ih =>
      intro γ d ρ h
      cases h with
      | live h₁ h₂ _ hc =>
          obtain ⟨σ₁, σ₂, hcσ, g₁, g₂⟩ := ih h₂
          obtain ⟨y, hy, hcy⟩ := compS_reassoc' hcσ hc
          have e₁ := tv_live_flag h₁ rfl
          subst e₁
          exact ⟨y, σ₂, hcy, .live h₁ g₁ (by simp) hy, .dead g₂⟩
  | right _ ih =>
      intro γ d ρ h
      cases h with
      | live h₁ h₂ _ hc =>
          obtain ⟨σ₁, σ₂, hcσ, g₁, g₂⟩ := ih h₂
          obtain ⟨y, hy, hcy⟩ := compS_lcomm hcσ hc
          have e₁ := tv_live_flag h₁ rfl
          subst e₁
          exact ⟨σ₁, y, hcy, .dead g₁, .live h₁ g₂ (by simp) hy⟩
  | dead _ ih =>
      intro γ d ρ h
      cases h with
      | dead h =>
          obtain ⟨σ₁, σ₂, hcσ, g₁, g₂⟩ := ih h
          exact ⟨σ₁, σ₂, hcσ, .dead g₁, .dead g₂⟩
  | dup hT _ ih =>
      intro γ d ρ h
      cases h with
      | live h₁ h₂ _ hc =>
          have e₁ := tv_live_flag h₁ rfl
          subst e₁
          obtain rfl : _ = PMap.empty := vP_empty_of_persistent hT ((tv_sound hδα).1 h₁ rfl rfl)
          obtain rfl := eq_of_compS_empty_left hc
          obtain ⟨σ₁, σ₂, hcσ, g₁, g₂⟩ := ih h₂
          exact ⟨σ₁, σ₂, hcσ, .live h₁ g₁ (by simp) (compS_empty_left σ₁),
            .live h₁ g₂ (by simp) (compS_empty_left σ₂)⟩

end

/-- A piece's answer as a typed value, consistent with the table. -/
def ansTV (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (A : VTy) :
    LSub → BoCa.Loc → Life → List SRec → Val → WProp :=
  fun δ l α ls v ρ => TV Δ x b T δ l false α A ls v false ρ ∧ TabAt l α ρ

/-- A piece's answer in the relation, consistent with the table. -/
def ansRC (x : LifeVar) (A : VTy) : LSub → BoCa.Loc → Life → List SRec → Val → WProp :=
  fun δ l => ansT x δ l A

/-- **A borrower piece over a typed context.** At every lend `α ⊏ @bδ`, from a context of typed
values consistent with the table, a run with the lend open at `α` answering in `Ans`. -/
def RBodyC (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (S : Row)
    (Γ : Ctx VTy) (ml : Bool) (E : Expr)
    (Ans : LSub → BoCa.Loc → Life → List SRec → Val → WProp) : Prop :=
  ∀ (δ : LSub), Δ.Models δ → ∀ (β : Life), b.interp δ = some β →
    ∀ (l : BoCa.Loc) (α : Life), α ⊏ β →
    ∀ (ls : List SRec) (γ : List Val) (ρ : WRes), TabAt l α ρ →
      TVG Δ x b T δ l false α (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ls false ρ →
      bodyAtD (opTable (Row.tab S δ)) l T δ (Ans δ l)
        (OpenD (opTable (Row.tab S δ)) l T δ (Ans δ l)) α ls
        (substAll (γ ++ [Val.loc l]) E) ρ

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {S : Row}

/-- **A pure piece**, by `fundamentalC` at `δ[x ↦ α]` from the context's relation. -/
theorem rbodyC_ret (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ : Ctx VTy} {ml : Bool} {E : Expr} {A : VTy}
    (h : SemC (Δ.extend x b) (Γ ++ [mSlot x T ml]) E (.ret A)) :
    RBodyC Δ x b T S Γ ml E (ansRC x A) := by
  intro δ hδ β hβ l α hα ls γ ρ ht hg
  have hδα := models_extend hδ hbx hΔx hβ hα
  refine bodyAtD_of_wpTS (wpTS_mono (P := fun ls' v ρ' =>
    TabAt l α ρ' ∧ vC true A ls' (δ.extend x α) v ρ') (Q := ansT x δ l A α)
    (fun _ _ _ h' => ⟨h'.2, h'.1⟩) ρ ?_)
  exact wpTS_tabAt l α ls _ _ ht (h (δ.extend x α) _ ls ρ hδα ((tv_sound hδα).2 hg rfl rfl))

/-- **`thunk M`**: a closure over the whole context, typed by its derivation. It answers at once,
a typed value holding the context's resource, the borrow among it if `m` is live. -/
theorem rbodyC_thunk {Γ : Ctx VTy} {ml : Bool} {M : Expr} {A : VTy}
    (hD : CDerives (Δ.extend x b) (⟨.unit, false⟩ :: (Γ ++ [mSlot x T ml])) M (.comp (.ret A))) :
    RBodyC Δ x b T S Γ ml (.val (.lam M)) (ansTV Δ x b T (.thunk (.ret A))) := by
  intro δ hδ β hβ l α hα ls γ ρ ht hg
  change wpG ls (.val (Val.lam (Expr.psub 1 (γ ++ [Val.loc l]) M))) _ ρ
  exact wpG_here _ _ _ ρ (Or.inl ⟨_, rfl, TV.cloF hD hg, ht⟩)

/-- **`perform`**: the stop, dropping nothing; the continuation answers `()`, a typed value. -/
theorem rbodyC_perform (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hS : Row.Resume S x) {Γ : Ctx VTy} {V : Expr} {o : OpSig}
    (hf : Row.find S o.n o.i = some o)
    (h : SemV (Δ.extend x b) (Γ ++ [mSlot x T false]) V o.A) :
    RBodyC Δ x b T S Γ false (performE (opArgE o.n o.i V)) (ansTV Δ x b T o.B) := by
  intro δ hδ β hβ l α hα ls γ ρ _ hg
  have hδα := models_extend hδ hbx hΔx hβ hα
  obtain ⟨ha, -, hq, hoB, hAx, hAo⟩ := hS o (Row.find_mem hf).1
  have hTb := opTable_mono (Row.tab S δ)
  change wpG ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll (γ ++ [Val.loc l]) V)) _ ρ
  refine wpG_bind_pure _ _ ls _ ρ (wpTS_mono (fun ls' v σ hv => ?_) ρ
    (h (δ.extend x α) _ ls ρ hδα ((tv_sound hδα).2 hg rfl rfl)))
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
  rw [hoB]
  exact TV.atomL (Or.inr ⟨by simp [VFree], .unit⟩) ⟨rfl, rfl⟩

/-- **`M to z. N`**, the frame a typed context. It is frozen at each of `M`'s stops
(`tvg_freeze`) and thawed at each later lend (`tvg_thaw`), every closure it holds re-derived
there. At `M`'s answer, a typed value, `N` runs at the lend `M` answered at. -/
theorem rbodyC_let (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false) (hT : ¬ VFree x T)
    (hS : Row.Resume S x) {Γ Γ₁ Γ₂ : Ctx VTy} {ml ml₁ ml₂ : Bool} {M N : Expr} {A₁ : VTy}
    {Ans : LSub → BoCa.Loc → Life → List SRec → Val → WProp}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γ₁ ++ [mSlot x T ml₁]) (Γ₂ ++ [mSlot x T ml₂]))
    (hM : RBodyC Δ x b T S Γ₁ ml₁ M (ansTV Δ x b T A₁))
    (hN : RBodyC Δ x b T S (⟨A₁, true⟩ :: Γ₂) ml₂ N Ans) :
    RBodyC Δ x b T S Γ ml (.app (.val (.lam N)) M) Ans := by
  intro δ hδ β hβ l α hα ls γ ρ ht hg
  have hLR := hS.linResume δ
  have hδα := models_extend hδ hbx hΔx hβ hα
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := tvg_split hδα hsp hg
  obtain ⟨ht₁, ht₂⟩ := (tabAt_comp hc).mp ht
  let K : Kont := .appR (.val (.lam (Expr.psub 1 (γ ++ [Val.loc l]) N))) .hole
  have hK : ∀ n, K.HasHnd n = false := fun n => by simp [K, Kont.HasHnd]
  let Γf := Γ₂ ++ [mSlot x T ml₂]
  let γf := γ ++ [Val.loc l]
  let Fr : Life → List SRec → WProp := fun α' ls ρ =>
    TabAt l α' ρ ∧ TVG Δ x b T δ l false α' Γf γf ls false ρ
  let Fz : Life → Bool → List SRec → WProp := fun α' d ls ρ =>
    TVG Δ x b T δ l true α' Γf γf ls d ρ
  have hFs : ∀ α' ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α' ls) (Fr α' ls') :=
    fun _ _ _ hs _ h => ⟨h.1, tvg_local (ext_of_same hs _) h.2⟩
  have hFe : ∀ α' d ls ls' ρ, Ext ls ls' ρ → Fz α' d ls ρ → Fz α' d ls' ρ :=
    fun _ _ _ _ _ he h => tvg_local he h
  have hFo : ∀ α' d ls ρ, Fz α' d ls ρ → ρ.InStratum α' :=
    fun _ _ _ _ h => tvg_inStratum h rfl
  have hfz : ∀ α', α' ⊏ β → ∀ ls ρ, Fr α' ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz α' d ls ρz ∧ dropC l d ρn :=
    fun α' hα' ls ρ h => by
      obtain ⟨d, ρz, ρn, hc, hz, hn⟩ :=
        tvg_freeze hT (models_extend hδ hbx hΔx hβ hα') h.2 rfl rfl h.1
      exact ⟨d, ρz, ρn, hc, hz, dropC_of_vwD hn⟩
  have hthaw : ∀ β' α' d₂ ls ρv ρz ρ, α' ⊏ β' → β' ≤ β → vwD l T δ d₂ α' ls ρv →
      Fz β' d₂ ls ρz → ResU.CompS ρv ρz ρ → Fr α' ls ρ := by
    intro β' α' d₂ ls ρv ρz ρ hα' _ hv hz hc
    obtain ⟨h', ht'⟩ := tvg_thaw hT (le_of_lt hα') hz rfl rfl ρv ρ hv (ResU.CompS.comm hc)
    exact ⟨ht', h'⟩
  have hk : ∀ α', α' ⊏ β → ∀ ls v, Entails (ansTV Δ x b T A₁ δ l α' ls v ⋆ Fr α' ls)
      (bodyAtD (opTable (Row.tab S δ)) l T δ (Ans δ l)
        (OpenD (opTable (Row.tab S δ)) l T δ (Ans δ l)) α' ls (K.plug (.val v))) := by
    rintro α' hα' ls' v σ ⟨σ₁, σ₂, hcσ, ⟨hv, hvt⟩, ⟨hft, hfr⟩⟩
    refine wpG_step (fun μ => Step1N.head (Head.beta μ _ v) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    exact hN δ hδ β hβ l α' hα' ls' (v :: γ) σ ((tabAt_comp hcσ).mpr ⟨hvt, hft⟩)
      (.live hv hfr (by simp) hcσ)
  exact bodyAtD_bind hLR K hK Fr Fz hFs hFe hFo (hfz α hα)
    (fun d₁ d₂ _ _ _ _ _ hnd hx hz hcτ =>
      openD_bind hLR K hK β Fr Fz hFs hFe hFo hfz hthaw hk (le_of_lt hα) hnd hx hz hcτ)
    (hk α hα) (hM δ hδ β hβ l α hα ls γ ρ₁ ht₁ hg₁) ⟨ht₂, hg₂⟩ hc

/-! ### The whole borrower -/

/-- A whole borrower `M`, `m` its only variable: at the first lend it is handed the view. -/
theorem openD_of_rbodyC (hT : ¬ VFree x T) {M : Expr}
    {Ans : LSub → BoCa.Loc → Life → List SRec → Val → WProp}
    {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (h : RBodyC Δ x b T S [] true M Ans) (l : BoCa.Loc) (ls : List SRec) :
    OpenD (opTable (Row.tab S δ)) l T δ (Ans δ l) β true ls (substAll [Val.loc l] M)
      PMap.empty :=
  openD_fold (opTable_mono _) fun α hα => ⟨fun ρm σ hm hc => by
    obtain rfl := eq_of_compS_empty_left hc
    exact h δ hδ β hβ l α hα ls [] _ (tabAt_view hm)
      (.live (.atomL (Or.inl rfl) (mutView hT hm)) .nil (by simp) (ResU.comp_empty_right _)),
    ResU.inStratum_empty α⟩

/-- **A borrower over typed contexts is re-lendable.** -/
theorem relend_of_rbodyC (hT : ¬ VFree x T) {B : VTy} (hB : ¬ VFree x B) {M : Expr}
    {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (h : RBodyC Δ x b T S [] true M (ansRC x (.box (.var x) B))) (l : BoCa.Loc) (ls : List SRec) :
    Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
      PMap.empty :=
  relend_of_openD_box (opTable_mono _) hB (openD_of_rbodyC hT hδ hβ h l ls)

/-- **O15.1's resume half for every borrower `RBodyC` reads.** -/
theorem withbor_of_rbodyC {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (hT : ¬ VFree x T) {B : VTy} (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    {M : Expr} (hM : closedAt 1 M = true)
    (h : RBodyC Δ x b T S [] true M (ansRC x (.box (.var x) B))) (l : BoCa.Loc) (v : Val)
    (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (cC (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ).mpr ?_
  exact withbor_relend (Row.tab S δ) hP _ v
    (relend_lam2 (opTable_mono _) hM (relend_of_rbodyC hT hB hδ hβ h l ls)) ρ hρ

end

end GhostEnd
