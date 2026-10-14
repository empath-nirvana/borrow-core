import Law2.Straight

/-!
# Law2 — the bridge: a run whose stops are the table's, at any stop context, is D16.1's piece

GhostEnd's stacked piece `OpenS` (D16.1) reads a borrower holding a stack `σ` of lends open across
its stops: at every re-lend of the stack, handed the views made afresh, it runs to an answer or to a
stop at which every view is dropped, the lenders are owed `ghostS`, and the continuation is the
piece again at the lifetimes just ended. `openS_of_run` and `openS_yield_ds` built it for one stop
context, `.seq .hole rest`, with the stop the run's first configuration.

* `openS_of_stops`: **the general form.** At every re-lend the run reaches an answer, or a stop of
  the table (`opTable`, at whatever context `K` the run reached, `K` free of a handler of the
  operation's name) whose share is the views it drops beside a part in `[top]`, each continuation
  owed the piece again. `openS_of_run` is the case with no stop; `openS_yield_ds` the case whose run
  is empty and whose stop context is `.seq .hole rest`.
* `openS_kstop`: a stop of the kernel's table at an operation of the row is a stop of the piece.
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

end

/-! ### Bind: a pure context around a piece, a frame frozen at each stop and thawed at each
re-lend -/

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

/-- A part in `[top]` joins the share a lender's exit hands its owner back to. -/
theorem ownWandE_frame {e : LEnt} {ls : List SRec} {αs : List Life} {R F : WProp}
    {ρ₁ ρ₂ ρ : WRes} (h : ownWandE δ e ls (ownerE δ e ls ⋆ boxTop αs R) ρ₁) (hF : F ρ₂)
    (hs : stratS αs ρ₂) (hc : ResU.CompS ρ₁ ρ₂ ρ) :
    ownWandE δ e ls (ownerE δ e ls ⋆ boxTop αs (R ⋆ F)) ρ := by
  have key : ∀ {ρa ρb : WRes}, ResU.CompS ρ ρa ρb → ∀ {ρc ρd : WRes}, ResU.CompS ρb ρc ρd →
      (∀ {y z : WRes}, ResU.CompS ρ₁ ρa y → ResU.CompS y ρc z →
        (ownerE δ e ls ⋆ boxTop αs R) z) →
      (ownerE δ e ls ⋆ boxTop αs (R ⋆ F)) ρd := by
    intro ρa ρb hab ρc ρd hcd hk
    obtain ⟨y, hy, hyb⟩ := compS_exch hc hab
    obtain ⟨z, hz, hzd⟩ := compS_exch hyb hcd
    obtain ⟨o, r, hcor, ho, hr⟩ := hk hy hz
    obtain ⟨rr, hrr, hord⟩ := compS_reassoc hcor hzd
    exact ⟨o, rr, hord, ho, ⟨r, ρ₂, hrr, hr.1, hF⟩,
      fun a ha => (outlives_comp hrr a).mpr ⟨hr.2 a ha, hs a ha⟩⟩
  obtain ⟨l, x, T, k, cr⟩ := e
  cases k with
  | «mut» =>
      intro w ρa ρb ha hab ρc ρd hv hcd
      exact key hab hcd fun hy hz => h w ρa _ ha hy ρc _ hv hz
  | imm u =>
      intro ρa ρb ha hab ρc ρd hv hcd
      exact key hab hcd fun hy hz => h ρa _ ha hy ρc _ hv hz

/-- **A part in `[top]` joins what a stop owes the lenders**: inside every lender's exit, beside
the share the outermost owes. -/
theorem ghostS_frame : ∀ {σ : LStack} {αs : List Life}, αs.length = σ.length →
    List.IsChain (· < ·) αs → ∀ {ls : List SRec} {R F : WProp} {ρ₁ ρ₂ ρ : WRes},
      ghostS δ σ αs ls R ρ₁ → F ρ₂ → stratS αs ρ₂ → ResU.CompS ρ₁ ρ₂ ρ →
        ghostS δ σ αs ls (R ⋆ F) ρ
  | [], [], _, _, _, _, _, ρ₁, ρ₂, _, h, hF, _, hc => ⟨ρ₁, ρ₂, hc, h, hF⟩
  | _ :: _, _ :: _, _, hch, _, _, _, _, _, _, h, hF, hs, hc =>
      ⟨ownWandE_frame h.1 hF hs hc, (outlives_comp hc _).mpr ⟨h.2, stratS_head hch hs⟩⟩

variable {σ : LStack}

/-- **Bind at one run, at the stack.** `K` pure around a run at `αs`, the live frame `Fr αs`
carried through it. At an answer `K[v]` runs on at the same lifetimes (`hk`). At a stop the frame
freezes (`hfz`): a part `Fz αs d` in `[top]`, beside the views it drops; the piece's drops and the
frame's join (`dropS_join`), and the frozen frame joins every continuation (`hX`). -/
theorem bodyS_bind (hLR : LinResume Tab) (hx : AllCross σ Tab) (K : Kont)
    (hH : ∀ n, K.HasHnd n = false)
    (Fr : List Life → List SRec → WProp) (Fz : List Life → List Bool → List SRec → WProp)
    (hFs : ∀ αs ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr αs ls) (Fr αs ls'))
    (hFe : ∀ αs d ls ls' ρ, Ext ls ls' ρ → Fz αs d ls ρ → Fz αs d ls' ρ)
    (hFo : ∀ αs d ls ρ, Fz αs d ls ρ → stratS αs ρ)
    {Q₁ Q : List Life → List SRec → Val → WProp} {X₁ X : XT}
    {αs : List Life} (hlen : αs.length = σ.length) (hch : List.IsChain (· < ·) αs)
    (hfz : ∀ ls ρ, Fr αs ls ρ → ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz αs d ls ρz ∧ dropS [] σ d ρn)
    (hX : ∀ d₁ d₂ ls e ρ₁ ρz ρ, MutDisj [] σ d₁ d₂ → d₁.length = σ.length →
      d₂.length = σ.length → X₁ σ.length d₁ αs [] ls e ρ₁ → Fz αs d₂ ls ρz →
      ResU.CompS ρ₁ ρz ρ → X σ.length (List.zipWith (· || ·) d₁ d₂) αs [] ls (K.plug e) ρ)
    (hk : ∀ ls v, Entails (Q₁ αs ls v ⋆ Fr αs ls) (bodyS δ σ Tab Q X αs ls (K.plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ₁ ρf ρ : WRes}
    (h : bodyS δ σ Tab Q₁ X₁ αs ls e ρ₁) (hf : Fr αs ls ρf) (hc : ResU.CompS ρ₁ ρf ρ) :
    bodyS δ σ Tab Q X αs ls (K.plug e) ρ := by
  refine wpG_garbage ?_
  refine wpG_bind K e ls _ ρ ?_
  refine wpG_mono (fun ls' t τ ht => ?_) (wpG_frame (Fr αs) (hFs αs ls) ρ ⟨ρ₁, ρf, hc, h, hf⟩)
  obtain ⟨τ₁, τ₂, hcτ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hs
  · exact wpG_mono (fun _ _ τ' hq => ⟨τ', PMap.empty, ResU.comp_empty_right τ', noOwn_empty, hq⟩)
      (hk ls' v τ ⟨τ₁, τ₂, hcτ, hv, hF'⟩)
  refine wpG_here _ _ _ τ ?_
  obtain ⟨d₂, ρz, ρn, hczn, hz, hdn⟩ := hfz ls' τ₂ hF'
  have hl₂ : d₂.length = σ.length := dropS_length hdn
  rcases stopS_full hx hlen hs with ⟨d₁, hl₁, ρa, ρg, hca, hda, hg⟩ | ⟨ρg, ρa, hca, hno, hg⟩
  · -- a stop at the full depth: the drops join, the frozen frame joins the continuations
    obtain ⟨ac, bd, hac, hbd, hρ⟩ := compS_four hca (ResU.CompS.comm hczn) hcτ
    obtain ⟨hdrop, hdisj⟩ := dropS_join hda hdn hac
    have hgz := ghostS_frame hlen hch hg hz (hFo _ _ _ _ hz) hbd
    refine ⟨τ, PMap.empty, ResU.comp_empty_right τ, noOwn_empty, Or.inr
      (stopS_of_full hx hlen hdrop (ghostS_mono (fun υ hυ => ?_) _ _ _ bd hgz) hρ)⟩
    obtain ⟨υ₁, υ₂, hcυ, hR, hFz⟩ := hυ
    exact opTable_frame hLR K hH (Fz αs d₂) (hFe αs d₂)
      (fun ls e ρ₁ ρz ρ h₁ h₂ h₃ => hX d₁ d₂ ls e ρ₁ ρz ρ hdisj hl₁ hl₂ h₁ h₂ h₃) hR hFz hcυ
  · -- a stop no lender admits: it owes nothing it can produce; its garbage is dropped
    obtain ⟨y, hy, hyτ⟩ := compS_exch hca hcτ
    obtain ⟨ab, hab, haby⟩ := compS_reassoc' hczn hy
    have hgz := ghostS_frame hlen hch hg hz (hFo _ _ _ _ hz) hab
    refine ⟨y, ρa, hyτ, hno, Or.inr (stopS_of_full hx hlen hdn
      (ghostS_mono (fun υ hυ => ?_) _ _ _ ab hgz) (ResU.CompS.comm haby))⟩
    obtain ⟨υ₁, υ₂, -, hR, -⟩ := hυ
    exact hR.elim

/-- A re-lend strictly below is a re-lend. -/
theorem reLend_of_lt {αs' αs : List Life} (hlt : List.Forall₂ (· < ·) αs' αs)
    (hch : List.IsChain (· < ·) αs') : ReLend αs' αs :=
  ⟨hlt.imp fun _ _ => le_of_lt, hch⟩

/-- **Bind, at the stack.** A pure context `K` around a piece, the frozen frame `Fz αi d₂` beside
it. At each unfolding the views go to the piece and to the frame by their drops (`vwS_split`), the
frozen frame thaws to the live frame at the re-lend (`hthaw`), and one run is `bodyS_bind`. By
induction on the piece's `OpenS`: its stops' continuations are the piece again, at the lifetimes
just ended, and the frame frozen at them. No step reads the stack's length. -/
theorem openS_bind (hLR : LinResume Tab) (hx : AllCross σ Tab) (K : Kont)
    (hH : ∀ n, K.HasHnd n = false)
    (Fr : List Life → List SRec → WProp) (Fz : List Life → List Bool → List SRec → WProp)
    (hFs : ∀ αs ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr αs ls) (Fr αs ls'))
    (hFe : ∀ αs d ls ls' ρ, Ext ls ls' ρ → Fz αs d ls ρ → Fz αs d ls' ρ)
    (hFo : ∀ αs d ls ρ, Fz αs d ls ρ → stratS αs ρ)
    (hfz : ∀ αs, αs.length = σ.length → List.IsChain (· < ·) αs → ∀ ls ρ, Fr αs ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz αs d ls ρz ∧ dropS [] σ d ρn)
    (hthaw : ∀ αs αs' d ls ρz ρv ρ, List.Forall₂ (· < ·) αs' αs →
      List.IsChain (· < ·) αs' → Fz αs d ls ρz → vwS δ [] σ d αs' ls ρv →
      ResU.CompS ρz ρv ρ → Fr αs' ls ρ)
    {Q₁ Q : List Life → List SRec → Val → WProp} {B : List Life}
    (hk : ∀ αs, List.Forall₂ (· ≤ ·) αs B → αs.length = σ.length → List.IsChain (· < ·) αs →
      ∀ ls v, Entails (Q₁ αs ls v ⋆ Fr αs ls)
        (bodyS δ σ Tab Q (OpenS δ σ Tab Q) αs ls (K.plug (.val v))))
    {d₁ d₂ : List Bool} (hd : MutDisj [] σ d₁ d₂) (hl₁ : d₁.length = σ.length)
    (hl₂ : d₂.length = σ.length) {αi : List Life} (hB : List.Forall₂ (· ≤ ·) αi B)
    {ls : List SRec} {e : Expr} {ρ₁ ρz ρ : WRes}
    (h : OpenS δ σ Tab Q₁ σ.length d₁ αi [] ls e ρ₁) (hz : Fz αi d₂ ls ρz)
    (hc : ResU.CompS ρ₁ ρz ρ) :
    OpenS δ σ Tab Q σ.length (List.zipWith (· || ·) d₁ d₂) αi [] ls (K.plug e) ρ := by
  let Mot : XT := fun k d₁ αi αo ls e ρ₁ => k = σ.length → αo = [] →
    List.Forall₂ (· ≤ ·) αi B → ∀ d₂ ρz ρ,
    MutDisj [] σ d₁ d₂ → d₁.length = σ.length → d₂.length = σ.length → Fz αi d₂ ls ρz →
      ResU.CompS ρ₁ ρz ρ → OpenS δ σ Tab Q σ.length (List.zipWith (· || ·) d₁ d₂) αi [] ls
        (K.plug e) ρ
  refine h Mot ?_ rfl rfl hB d₂ ρz ρ hd hl₁ hl₂ hz hc
  rintro k d₁ αi αo ls e ρ₁ hF rfl rfl hB d₂ ρz ρ hd hl₁ hl₂ hz hc
  refine openS_fold fun αi' hlt hch => ?_
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
  have hfr := hthaw αi αi' d₂ ls ρz ρv₂ y hlt hch hz hv₂ hy
  have hB' : List.Forall₂ (· ≤ ·) αi' B := forall₂_le_trans (hlt.imp fun _ _ => le_of_lt) hB
  exact bodyS_bind hLR hx K hH Fr Fz hFs hFe hFo hlen hch (hfz αi' hlen hch)
    (fun d₁ d₂ ls e ρ₁ ρz ρ hd' hl₁' hl₂' hM hz' hc' =>
      hM rfl rfl hB' d₂ ρz ρ hd' hl₁' hl₂' hz' hc')
    (hk αi' hB' hlen hch) hb hfr hxy

end bind

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
        θ (OrderDual.toDual 5) = OrderDual.toDual 7 ∧ θ (OrderDual.toDual 3) = OrderDual.toDual 6 := by
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
