import Law2.Straight

/-!
# Law2 — the bridge: a run whose stops are the table's, at any stop context, is D16.1's piece

GhostEnd's stacked piece `OpenS` (D16.1) reads a borrower holding a stack `σ` of lends open across
its stops: at every re-lend of the stack, handed the views made afresh, it runs to an answer or to a
stop at which every view is dropped, the lenders are owed `ghostS`, and the continuation is the
piece again at the lifetimes just ended. `openS_of_run` and `openS_yield_ds` (`Law2/Straight.lean`)
build it for one stop context, `.seq .hole rest`, with the stop the run's first configuration.

* `openS_of_stops`: **the general form.** At every re-lend the run reaches an answer, or a stop of
  the table (`opTable`, at whatever context `K` the run reached, `K` free of a handler of the
  operation's name) whose share is the views it drops beside a part in `[top]`, each continuation
  owed the piece again. `openS_of_run_stops` (no stop) and `openS_yield_stops` (a run of no steps
  stopping at `.seq .hole rest`) derive `openS_of_run` and `openS_yield_ds` from it. The piece
  judgment does not go through it: `piece_of_pj` reaches D16.1's piece through `openS_of_pj`,
  `openS_of_openH` and `openH_bind` (`Law2/Inner.lean`, `Law2/Piece.lean`).
* `stopAt_of_perform`: a stop of the kernel's table at an operation of the row is a stop of the
  piece.
* `dropE_join`, `dropS_join`: what two parts drop at a stop joins, entry by entry; the stacked bind
  (`Law2/Inner.lean`) joins a frame's drops to its inner piece's with them.
* `relend_of_openS₁`: at one `mut` entry the piece is GhostEnd's single-lend `Relend`.
* `relend_not_emb`: why the bridge reads re-lends directly rather than through re-makings.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

section
variable {δ : LSub} {Tab : OpTab}

/-- **A stop of the piece, at the full depth.** The views the stop drops, beside a share in
`[top]` that the table admits, owing every continuation `X` at the drops and the lifetimes just
ended. -/
def StopAt (σ : LStack) (Tab : OpTab) (X : XT) (αs : List Life) (ls : List SRec)
    (t : Expr) : WProp :=
  ex fun ds => dropS [] σ ds ⋆
    boxTop αs (opTable Tab ls t fun ls' e' => X σ.length ds αs [] ls' e')

theorem StopAt.mono {σ : LStack} {X X' : XT}
    (hX : ∀ k ds αi αo ls e ρ, X k ds αi αo ls e ρ → X' k ds αi αo ls e ρ) {αs : List Life}
    {ls : List SRec} {t : Expr} : Entails (StopAt σ Tab X αs ls t) (StopAt σ Tab X' αs ls t) := by
  rintro ρ ⟨ds, ρ₁, ρ₂, hc, hd, hb, hs⟩
  exact ⟨ds, ρ₁, ρ₂, hc, hd, opTable_mono _ _ _ _ _ _ (fun _ _ _ h => hX _ _ _ _ _ _ _ h) hb, hs⟩

/-- **A stop at the full depth is a stop of the piece**, when every operation crosses every
entry: the owners handed back are passed on (`ghostS_of_boxTop`). -/
theorem stopS_of_stopAt {σ : LStack} (hx : AllCross σ Tab) {X : XT} {αs : List Life}
    (hlen : αs.length = σ.length) (hch : List.IsChain (· < ·) αs) {ls : List SRec} {t : Expr}
    {ρ : WRes} (h : StopAt σ Tab X αs ls t ρ) : stopS δ σ Tab X αs ls t ρ := by
  obtain ⟨ds, ρ₁, ρ₂, hc, hd, hb⟩ := h
  exact stopS_of_full hx hlen hd (ghostS_of_boxTop hlen hch hb) hc

/-- **The bridge.** A run that, at every re-lend below `αi` and handed the views, reaches an
answer in `Q` or a stop at the full depth (`StopAt`), at any stop context, every continuation the
piece again, is D16.1's piece, its own share `ρ` in `[top]` at every re-lend. -/
theorem openS_of_stops {σ : LStack} (hx : AllCross σ Tab) {Q : List Life → List SRec → Val → WProp}
    {ds : List Bool} {αi : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (hz : ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) αi' → stratS αi' ρ)
    (h : ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) αi' →
      ∀ w W, vwS δ [] σ ds αi' ls w → ResU.CompS ρ w W →
        wpG ls e (fun ls'' t τ => valPost (Q αi') ls'' t τ ∨
          StopAt σ Tab (OpenS δ σ Tab Q) αi' ls'' t τ) W) :
    OpenS δ σ Tab Q σ.length ds αi [] ls e ρ := by
  refine openS_fold fun αi' hlt hch => ?_
  rw [List.append_nil] at hch ⊢
  refine ⟨fun w W hw hc => ?_, hz αi' hlt hch⟩
  rw [List.take_length] at hw
  have hlen := (vwS_length hw).2
  exact wpG_mono (fun ls'' t τ hq => hq.imp id (stopS_of_stopAt hx hlen hch))
    (h αi' hlt hch w W hw hc)

/-- **A stop of the kernel's table is a stop of the piece.** At an operation of the table, a
`perform` under a context free of a handler of its name: the argument in the entry's relation and
the continuation's share, owing the piece at every answer the entry admits, the whole beside the
dropped views and in `[top]`. -/
theorem stopAt_of_perform {σ : LStack} {X : XT} {αs : List Life} {ls : List SRec}
    {K : Kont} {n i : UInt32} {y : Val} {en : OpEnt} (hK : K.HasHnd n = false)
    (hT : Tab n i = some en) (ha : en.abort = false) {ds : List Bool} {ρd ρa ρk ρs ρ : WRes}
    (hd : dropS [] σ ds ρd) (hy : en.PA ls y ρa)
    (hk : contShare en ls K (fun ls' e' => X σ.length ds αs [] ls' e') ρk)
    (hcs : ResU.CompS ρa ρk ρs) (hstr : stratS αs ρs) (hc : ResU.CompS ρd ρs ρ) :
    StopAt σ Tab X αs ls (K.plug (performE (.val (opPayload n i y)))) ρ :=
  ⟨ds, ρd, ρs, hc, hd, Or.inl ⟨K, n, i, y, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩
    ⟨ρa, ρk, hcs, hy, hk⟩⟩, hstr⟩

/-- **`openS_of_run` from `openS_of_stops`**: a run with no stop. -/
theorem openS_of_run_stops {σ : LStack} (hx : AllCross σ Tab) {Qa : List SRec → Val → WProp}
    {ds : List Bool} {E : Expr} (hE : RunsAt (ℍ := ℍ) δ σ ds Qa E) (αi : List Life)
    (ls : List SRec) : OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls E PMap.empty := by
  refine openS_of_stops hx (fun _ _ _ a _ => ResU.inStratum_empty a)
    fun αi' hlt hch w W hw hc => ?_
  rw [eq_of_compS_empty_left hc]
  have hlen := (vwS_length hw).2
  exact wpG_mono (fun ls'' t ρ hq => by
    obtain ⟨v, hv, hb⟩ := hq
    exact Or.inl ⟨v, hv, ghostS_of_boxTop hlen hch hb⟩)
    ((wpTS_iff_wpG _ _ _ _).mp (hE αi' ls hlen hch (lt_top_of_forall₂ hlt) w hw))

/-- **`openS_yield_ds` from `openS_of_stops`**: a run of no steps, stopping at `.seq .hole rest`,
every view dropped; the continuation, after the `;` step, is the piece again. -/
theorem openS_yield_stops {σ : LStack} (hx : AllCross σ Tab) {n i : UInt32} {en : OpEnt}
    (hTn : Tab n i = some en) (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {Qa : List SRec → Val → WProp} {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    {ds : List Bool}
    (h : ∀ ls αi, OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls rest PMap.empty)
    (αi : List Life) (ls : List SRec) :
    OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls (yieldSeq n i y rest) PMap.empty := by
  refine openS_of_stops hx (fun _ _ _ a _ => ResU.inStratum_empty a)
    fun αi' hlt hch w W hw hc => ?_
  rw [eq_of_compS_empty_left hc]
  refine wpG_here ls _ _ w (Or.inr ?_)
  refine stopAt_of_perform (K := .seq .hole rest) rfl hTn ha (dropS_of_vwS hw) (hy ls) ?_
    (ResU.comp_empty_right _) (fun a _ => ResU.inStratum_empty a) (ResU.comp_empty_right w)
  refine ⟨fun _ => rfl, fun ls' _ => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  rw [eq_of_compS_empty_left hcτ]
  exact openS_step (fun μ => Step1N.head (Head.seq μ rest) rfl) (h ls' αi')

end

/-! ### Drops joined across two parts -/

section bind
variable {δ : LSub} {Tab : OpTab}

/-- **The drops of one entry join.** At most one is a `mut` cell; two `imm` cells are one
(`[TR]` 6.43). -/
theorem dropE_join {e : LEnt} {d₁ d₂ : Bool} {a₁ a₂ a : WRes} (h₁ : dropE e d₁ a₁)
    (h₂ : dropE e d₂ a₂) (hc : ResU.CompS a₁ a₂ a) :
    dropE e (d₁ || d₂) a ∧ (e.k = .mut → ¬ (d₁ = true ∧ d₂ = true)) := by
  cases d₁ with
  | false =>
      obtain ⟨rfl, -⟩ := h₁
      rw [eq_of_compS_empty_left hc]
      exact ⟨by simpa using h₂, fun _ h => by simp at h⟩
  | true =>
      cases d₂ with
      | false =>
          obtain ⟨rfl, -⟩ := h₂
          rw [ResU.CompS.functional hc (ResU.comp_empty_right a₁)]
          exact ⟨by simpa using h₁, fun _ h => by simp at h⟩
      | true =>
          obtain ⟨ψ₁, rfl, hk₁⟩ := h₁
          obtain ⟨ψ₂, rfl, hk₂⟩ := h₂
          rcases ResU.Comp.get hc e.l with ⟨e₁, -, -⟩ | ⟨_, -, e₂, -⟩ | ⟨_, e₁, -, -⟩ |
              ⟨ψ₁', ψ₂', ψ, e₁, e₂, -, hψ⟩
          · rw [ResU.single_get_self] at e₁; exact absurd e₁ (by simp)
          · rw [ResU.single_get_self] at e₂; exact absurd e₂ (by simp)
          · rw [ResU.single_get_self] at e₁; exact absurd e₁ (by simp)
          · rw [ResU.single_get_self] at e₁ e₂
            cases Option.some.inj e₁; cases Option.some.inj e₂
            obtain ⟨s₁, s₂, v, χ, k₁, k₂, k₃, f₁, f₂, -⟩ := hψ
            subst f₁ f₂
            obtain ⟨l, x, T, k, cr⟩ := e
            cases k with
            | «mut» => simp at hk₁
            | imm u =>
                exact ⟨⟨_, ResU.CompS.functional hc (ResU.compS_single_imm l s₁ s₂ v χ k₁ k₂ k₃),
                  by simp⟩, fun h => by cases h⟩

/-- **What a stop drops joins across two parts**, entry by entry: at most one `mut` cell at each
entry (`MutDisj`), two `imm` cells one. -/
theorem dropS_join : ∀ {seen : List BoCa.Loc} {σ : LStack} {d₁ d₂ : List Bool} {ρ₁ ρ₂ ρ : WRes},
    dropS seen σ d₁ ρ₁ → dropS seen σ d₂ ρ₂ → ResU.CompS ρ₁ ρ₂ ρ →
      dropS seen σ (List.zipWith (· || ·) d₁ d₂) ρ ∧ MutDisj seen σ d₁ d₂
  | _, [], [], [], _, _, _, h₁, h₂, hc => by
      obtain ⟨rfl, -⟩ := h₁; obtain ⟨rfl, -⟩ := h₂
      rw [eq_of_compS_empty_left hc]; exact ⟨⟨rfl, trivial⟩, trivial⟩
  | seen, e :: σ, a :: d₁, b :: d₂, _, _, _, ⟨a₁, r₁, hc₁, ha₁, hr₁⟩, ⟨a₂, r₂, hc₂, ha₂, hr₂⟩,
      hc => by
      obtain ⟨ac, bd, hac, hbd, hρ⟩ := compS_four hc₁ hc₂ hc
      obtain ⟨hv, hdisj⟩ := dropS_join hr₁ hr₂ hbd
      obtain ⟨hj, hm⟩ := dropE_join ha₁ ha₂ hac
      refine ⟨⟨ac, bd, hρ, ?_, hv⟩, hm, hdisj⟩
      rw [vis_or]; exact hj
  | _, [], [], _ :: _, _, _, _, _, h, _ => h.elim
  | _, [], _ :: _, _, _, _, _, h, _, _ => h.elim
  | _, _ :: _, [], _, _, _, _, h, _, _ => h.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, h, _ => h.elim

/-- A re-lend strictly below is a re-lend. -/
theorem reLend_of_lt {αs' αs : List Life} (hlt : List.Forall₂ (· < ·) αs' αs)
    (hch : List.IsChain (· < ·) αs') : ReLend αs' αs :=
  ⟨hlt.imp fun _ _ => le_of_lt, hch⟩

end bind

/-! ### At one `mut` entry: GhostEnd's single-lend callback -/

section one
variable {δ : LSub} {Tab : OpTab}

/-- **D16.1's piece at one `mut` entry is GhostEnd's re-lendable callback** (`Relend`): at each
lend `Relend` hands the view, which the piece takes if its drop flag asks for it and leaves as
garbage otherwise; at a stop the dropped view is garbage and the owner handed back joins the
continuation (`opTable_frame`), which is the piece again with its bound the lend just ended. -/
theorem relend_of_openS₁ (hLR : LinResume Tab) {l : BoCa.Loc} {x : LifeVar} {T : VTy}
    {cr : UInt32 → Bool} (hx : AllCross [⟨l, x, T, .mut, cr⟩] Tab)
    {Qa Q₀ : List SRec → Val → WProp}
    (hQ : ∀ ls v, Entails (owner l T δ ls ⋆ Qa ls v) (Q₀ ls v))
    {d : Bool} {β : Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenS δ [⟨l, x, T, .mut, cr⟩] Tab (cbQ δ [⟨l, x, T, .mut, cr⟩] Qa) 1 [d] [β] [] ls e ρ) :
    Relend (opTable Tab) l T δ Q₀ ls e ρ := by
  have hTb := opTable_mono Tab
  let en : LEnt := ⟨l, x, T, .mut, cr⟩
  let Mot : XT := fun k ds αi αo ls e ρ => k = 1 → αo = [] → ∀ d β, ds = [d] → αi = [β] →
    Relend (opTable Tab) l T δ Q₀ ls e ρ
  refine h Mot ?_ rfl rfl d β rfl rfl
  rintro k ds αi αo ls e ρ hF rfl rfl d β rfl rfl
  refine relend_fold hTb ⟨β, fun α hα => ?_⟩
  have hFα := hF [α] (.cons hα .nil) (List.isChain_singleton α)
  simp only [List.append_nil] at hFα
  refine ⟨fun ρm σ hm hcm => ?_, hFα.2 α (by simp)⟩
  -- the view, fed to the piece or left as garbage
  have hb : wpG ls e (fun ls'' t => (fun τ => NoOwn τ) ⋆ fun τ =>
      valPost (cbQ δ [en] Qa [α]) ls'' t τ ∨ stopS δ [en] Tab Mot [α] ls'' t τ) σ := by
    cases d with
    | true =>
        have hv : vwS δ [] [en] [true] [α] ls ρm :=
          ⟨ρm, PMap.empty, ResU.comp_empty_right ρm, by simpa [vis, vwE] using hm, ⟨rfl, trivial⟩⟩
        exact wpG_mono (fun _ _ τ hq => ⟨PMap.empty, τ, compS_empty_left τ, noOwn_empty, hq⟩)
          (hFα.1 ρm σ hv hcm)
    | false =>
        have hv : vwS δ [] [en] [false] [α] ls PMap.empty :=
          ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
            by simp [vis, vwE]; exact ⟨rfl, trivial⟩,
            ⟨rfl, trivial⟩⟩
        have hb₀ := hFα.1 PMap.empty ρ hv (ResU.comp_empty_right ρ)
        exact wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hc, hq, hn⟩ => ⟨τ₂, τ₁, ResU.CompS.comm hc, hn, hq⟩)
          (wpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ h => h) σ
            ⟨ρ, ρm, hcm, hb₀, noOwn_ptoMutS hm⟩)
  refine wpG_garbage (wpG_mono (fun ls'' t τ hq => ?_) hb)
  obtain ⟨τn, τq, hcτ, hn, hq⟩ := hq
  rcases hq with ⟨v, rfl, hv⟩ | hs
  · -- an answer: the owner handed back beside `Qa`
    refine ⟨τq, τn, ResU.CompS.comm hcτ, hn,
      fun w ρa ρb ha hcab ρc ρd hc hccd => Or.inl ⟨v, rfl, ?_⟩,
      hv.2⟩
    obtain ⟨o, r, hcor, ho, hr⟩ := hv.1 w ρa ρb ha hcab ρc ρd hc hccd
    exact hQ ls'' v ρd ⟨o, r, hcor, ho, hr.1⟩
  · rcases stopS_full hx rfl hs with ⟨ds', hl', ρ₁, ρ₂, hc₁₂, hd, hg⟩ | ⟨ρ₁, ρ₂, hc₁₂, hno, hg⟩
    · -- a stop: the dropped view joins the garbage; the owner joins the continuation
      obtain ⟨d', rfl⟩ : ∃ d', ds' = [d'] := by
        match ds', hl' with
        | [d'], _ => exact ⟨d', rfl⟩
      obtain ⟨g, hg', hcg⟩ := compS_reassoc' hc₁₂ hcτ
      refine ⟨ρ₂, g, ResU.CompS.comm hcg, noOwn_compS hg' hn (dropS_noOwn hd),
        fun w ρa ρb ha hcab ρc ρd hc hccd => Or.inr ?_, hg.2⟩
      obtain ⟨o, r, hcor, ho, hr⟩ := hg.1 w ρa ρb ha hcab ρc ρd hc hccd
      exact opTable_frame hLR .hole (fun _ => rfl) (owner l T δ)
        (fun _ _ _ he h => owner_local he h)
        (fun _ _ _ ρz _ hM hoz hc' => ⟨ρz, _, ResU.CompS.comm hc', hoz,
          hM rfl rfl d' α rfl rfl⟩) hr.1 ho (ResU.CompS.comm hcor)
    · -- a stop no lender admits owes nothing it can produce
      obtain ⟨g, hg', hcg⟩ := compS_lcomm hc₁₂ hcτ
      refine ⟨ρ₁, g, hcg, noOwn_compS hg' hn hno,
        fun w ρa ρb ha hcab ρc ρd hc hccd => ?_, hg.2⟩
      obtain ⟨o, r, hcor, ho, hr⟩ := hg.1 w ρa ρb ha hcab ρc ρd hc hccd
      exact hr.1.elim

end one

/-! ### Why the bridge reads re-lends directly -/

/-- **A re-lend no re-stratification realizes.** D16.1's piece is unfolded at every re-lend: each
lifetime below the one it replaces, the vector in nesting order. On `Life = ℕᵒᵈ` such a re-lend
may close a gap: `[7, 6]` re-lends `[5, 3]` (innermost first), and no order embedding fixing a
cut maps `5 ↦ 7` and `3 ↦ 6`, since `4` would have to land strictly between `7` and `6`. So a
hypothesis read through `Restrat.Emb` (`KappaRelends`) does not reach every re-lend the piece
asks for; the bridge is stated at the re-lent readings themselves (`RunsAt`, `StopAt`). -/
theorem relend_not_emb :
    List.Forall₂ (· < ·) [OrderDual.toDual 7, OrderDual.toDual 6]
        [(OrderDual.toDual 5 : Life), OrderDual.toDual 3] ∧
      List.IsChain (· < ·) [(OrderDual.toDual 7 : Life), OrderDual.toDual 6] ∧
      ¬ ∃ (c : Life) (θ : Restrat.Emb c),
        θ (OrderDual.toDual 5) = OrderDual.toDual 7 ∧
          θ (OrderDual.toDual 3) = OrderDual.toDual 6 := by
  refine ⟨.cons (by decide) (.cons (by decide) .nil), by decide, ?_⟩
  rintro ⟨c, θ, h5, h3⟩
  have h₁ : θ (OrderDual.toDual 5) < θ (OrderDual.toDual 4) := θ.strictMono (by decide)
  have h₂ : θ (OrderDual.toDual 4) < θ (OrderDual.toDual 3) := θ.strictMono (by decide)
  rw [h5] at h₁
  rw [h3] at h₂
  have a₁ : OrderDual.ofDual (θ (OrderDual.toDual 4)) < 7 := h₁
  have a₂ : 6 < OrderDual.ofDual (θ (OrderDual.toDual 4)) := h₂
  omega

end Law2

end
