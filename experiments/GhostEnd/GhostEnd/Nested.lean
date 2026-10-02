import GhostEnd.Body
import GhostEnd.Frames
import GhostEnd.Instance

/-!
# GhostEnd — a nested lend spanning a stop (#268, item 3)

Inside a borrower holding `m : Mut 'x T` at `ℓ`, the reborrow `withbor m (Λ. λn. N)` (`withbor3`,
`[TR]` 6.174) lends `ℓ` again: 6.66 unfolds the outer view `ℓ ↦ M_{α₁}` to its content, and 6.65
lends that content at a fresh `α₂ ⊏ α₁`. When `N` stops, both lends are open.

**At the stop**, in nesting order from the inside out:

1. the inner lend is ghost-ended: its view is dropped, and 6.65's exit hands the owner
   `ℓ ↦ w ⋆ 𝒱⟦T⟧(w)` back to the anti-frame;
2. 6.66's exit refolds it into the outer view `ℓ ↦ M_{α₁}`;
3. the outer lend is ghost-ended: the outer view is dropped, and the outer 6.65 hands its own
   owner back to the outer lender.

**At the resumption**, from the outside in:

1. the outer lender re-lends at a fresh `α₁′` (`ewpTS_M_frameR`);
2. 6.66 unfolds the outer's **new** view `ℓ ↦ M_{α₁′}`;
3. 6.65 lends the content at a fresh `α₂′ ⊏ α₁′`.

The refold of step 2 is 6.66 under the outer's new witness, applied once per resumption. The
anti-frame never refolds at a lifetime that has ended: the old-lifetime refold is the route
`refoldKripke_false` refutes, and `ewpTS_M_antiFrameR`'s continuation, which is owed the view at
the *same* `α`, is not used here.

**The ordering constraint.** `nestF` hands the inner piece every `α₂ ⊏ α₁`, where `α₁` is the
outer lend current at that unfolding. That is the bound `withbor3`'s type gives the callback,
`∀'y ⊏ ⊓Δ` with `'x ∈ Δ`, read at the outer's current assignment. 6.65's H4 then chooses the
inner lifetime below it (`wpG_M_frameX` takes the `⋔` bound as its `γ`). The inner piece's stop
share is in `[α₁]`: the frozen frames of the inner borrower outlive the outer lend, which is the
stop condition README step 3c names.

`nested_relend` is the commutation lemma: a nested piece is re-lendable for the outer lend
(`Relend`). `nested_spans` composes it with `ewpTS_M_frameR`. `nest_yield` and `nest_ret` build a
nested piece, and `nested_spans_yield` discharges every hypothesis on a reborrow whose callback
yields once with both lends open.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

section
variable {l : BoCa.Loc} {T : VTy} {δ : LSub}

/-- The owner is Kripke along `Ext`. -/
theorem owner_local {ls ls' : List SRec} {ρ : WRes} (he : Ext ls ls' ρ)
    (h : owner l T δ ls ρ) : owner l T δ ls' ρ := by
  obtain ⟨w, ρ₁, ρ₂, hc, ho, hv⟩ := h
  exact ⟨w, ρ₁, ρ₂, hc, ho, vC_local true T (he.right hc) hv⟩

/-- **A stop keeps an owner beside it in its continuation**, at a linear resuming table. -/
theorem opTable_absorb {Tab : OpTab} (hLR : LinResume Tab) {ls : List SRec} {t : Expr}
    {X : List SRec → Expr → WProp} {ρ₁ ρo ρ : WRes} (h : opTable Tab ls t X ρ₁)
    (ho : owner l T δ ls ρo) (hc : ResU.CompS ρ₁ ρo ρ) :
    opTable Tab ls t (fun ls' e' => owner l T δ ls' ⋆ X ls' e') ρ :=
  opTable_frame hLR .hole (fun _ => rfl) (owner l T δ) (fun _ _ _ he h => owner_local he h)
    (fun _ _ _ _ _ hx hz hc' => ⟨_, _, ResU.CompS.comm hc', hz, hx⟩) h ho hc

end

/-- `∀w. ℓ ↦ w ─⋆ 𝒱⟦T⟧(w) ─⋆ R`: what a share owes once the owner is handed back. -/
def ownWand (l : BoCa.Loc) (T : VTy) (δ : LSub) (ls : List SRec) (R : WProp) : WProp :=
  all fun w => ptoOwn l w ─⋆ (vC true T ls δ w ─⋆ R)

theorem ownWand_mono {l : BoCa.Loc} {T : VTy} {δ : LSub} {ls : List SRec} {R R' : WProp}
    (h : Entails R R') : Entails (ownWand l T δ ls R) (ownWand l T δ ls R') :=
  fun _ hw w ρa ρb ha hc ρc ρd hv hc' => h ρd (hw w ρa ρb ha hc ρc ρd hv hc')

/-- **One unfolding of a nested piece at the outer lend `α₁`.** Lent at every `α₂ ⊏ α₁`, the
piece runs; with the inner owner handed back, it returns that owner beside a share in `[α₁]`:
an answer in `Qa`, or a stop the table admits, owing `X`. -/
def nestF (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Qa : List SRec → Val → WProp)
    (X : List SRec → Expr → WProp) (α₁ : Life) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ α₂, α₂ ⊏ α₁ → box α₂ (viewP l T δ α₂ ls ─⋆
    wpG ls e (fun ls'' t => box α₂ (ownWand l T δ ls''
      (owner l T δ ls'' ⋆ box α₁ (fun σ => valPost Qa ls'' t σ ∨ Tb ls'' t X σ))))) ρ

/-- A nested piece at every outer lend the outer lender chooses fresh. -/
def nestRF (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Qa : List SRec → Val → WProp)
    (X : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  fun ls e => fresh fun α₁ => nestF Tb l T δ Qa X α₁ ls e

/-- **The nested piece**: the least fixed point of `nestRF`. A stop owes its continuation the next
unfolding, at the next outer lend and below it. -/
def NestRelend (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Qa : List SRec → Val → WProp)
    (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X : List SRec → Expr → WProp, (∀ ls e ρ, nestRF Tb l T δ Qa X ls e ρ → X ls e ρ) → X ls e ρ

section
variable {Tb : Table} {l : BoCa.Loc} {T : VTy} {δ : LSub} {Qa : List SRec → Val → WProp}

theorem nestRF_mono (hTb : Tb.Mono) {X X' : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ, X ls e ρ → X' ls e ρ) {ls : List SRec} {e : Expr} :
    Entails (nestRF Tb l T δ Qa X ls e) (nestRF Tb l T δ Qa X' ls e) := by
  rintro ρ ⟨γ, hγ⟩
  refine ⟨γ, fun α₁ hα₁ => ⟨fun α₂ hα₂ => ?_, (hγ α₁ hα₁).2⟩⟩
  refine box_mono (wand_mono_right fun _ hw => wpG_mono (fun ls'' t σ hb => ?_) hw) ρ
    ((hγ α₁ hα₁).1 α₂ hα₂)
  refine box_mono (ownWand_mono fun τ ⟨τ₁, τ₂, hcτ, ho, hs⟩ => ⟨τ₁, τ₂, hcτ, ho, ?_⟩) σ hb
  rcases hs.1 with hq | hq
  · exact ⟨Or.inl hq, hs.2⟩
  · exact ⟨Or.inr (hTb _ _ _ _ _ hX hq), hs.2⟩

theorem nestRelend_fold (hTb : Tb.Mono) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : nestRF Tb l T δ Qa (NestRelend Tb l T δ Qa) ls e ρ) : NestRelend Tb l T δ Qa ls e ρ :=
  fun X hX => hX ls e ρ (nestRF_mono hTb (fun _ _ _ h' => h' X hX) ρ h)

theorem nestRelend_unfold (hTb : Tb.Mono) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : NestRelend Tb l T δ Qa ls e ρ) : nestRF Tb l T δ Qa (NestRelend Tb l T δ Qa) ls e ρ :=
  h (fun ls e ρ => nestRF Tb l T δ Qa (NestRelend Tb l T δ Qa) ls e ρ)
    (fun _ _ _ h' => nestRF_mono hTb (fun _ _ _ h'' => nestRelend_fold hTb h'') _ h')

/-- A nested piece is closed under a pure step in front. -/
theorem nestRelend_step (hTb : Tb.Mono) {ls : List SRec} {e e' : Expr}
    (hs : ∀ μ : Heap, Step1N μ e μ e') {ρ : WRes} (h : NestRelend Tb l T δ Qa ls e' ρ) :
    NestRelend Tb l T δ Qa ls e ρ := by
  refine nestRelend_fold hTb ?_
  obtain ⟨γ, hγ⟩ := nestRelend_unfold hTb h
  exact ⟨γ, fun α₁ hα₁ => ⟨fun α₂ hα₂ =>
    box_mono (wand_mono_right (wpG_step hs ls _)) ρ ((hγ α₁ hα₁).1 α₂ hα₂), (hγ α₁ hα₁).2⟩⟩

/-- **A nested piece at an answer**: the inner view is left behind, and the inner owner handed
back is returned beside the answer. -/
theorem nest_val (hTb : Tb.Mono) {u : Val} (hu : ∀ ls, Qa ls u PMap.empty) (ls : List SRec) :
    NestRelend Tb l T δ Qa ls (.val u) PMap.empty := by
  refine nestRelend_fold hTb ⟨⊤, fun α₁ _ => ⟨fun α₂ _ => ⟨fun ρm ρ' hm hc => ?_,
    ResU.inStratum_empty α₂⟩, ResU.inStratum_empty α₁⟩⟩
  rw [eq_of_compS_empty_left hc]
  refine wpG_garbage (wpG_here ls _ _ ρm ⟨PMap.empty, ρm, compS_empty_left ρm,
    noOwn_ptoMutS hm, ?_, ResU.inStratum_empty α₂⟩)
  intro w ρa ρb ha hcab ρc ρd hv hccd
  rw [eq_of_compS_empty_left hcab] at hccd
  exact ⟨ρd, PMap.empty, ResU.comp_empty_right ρd, ⟨w, ρa, ρc, hccd, ha, hv⟩,
    Or.inl ⟨u, rfl, hu ls⟩, ResU.inStratum_empty α₁⟩

end

/-- **The commutation lemma.** A nested piece is re-lendable for the outer lend. At each outer
lend `α₁`, 6.66 unfolds the view the outer lender has just handed out, at `α₁` itself, and 6.65
lends its content at the inner `α₂ ⊏ α₁` the piece accepts. At a return or a stop the inner
6.65's exit hands the owner back, 6.66's exit refolds it into `ℓ ↦ M_{α₁}`, and that view is left
behind (it owns nothing), so the outer share is in `[α₁]`. At a stop the outer owner the outer
6.65 hands back joins the continuation (`opTable_absorb`), and the continuation is again a nested
piece. By induction on `NestRelend`; `wpG_M_antiFrameX` and `wpG_M_frameX` are applied as
printed at each unfolding. -/
theorem nested_relend (Tab : OpTab) (hLR : LinResume Tab) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (β : Life) (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β)
    (Qa : List SRec → Val → WProp) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : NestRelend (opTable Tab) l T δ Qa ls e ρ) :
    Relend (opTable Tab) l T δ (fun ls v => owner l T δ ls ⋆ Qa ls v) ls e ρ := by
  let Qo : List SRec → Val → WProp := fun ls v => owner l T δ ls ⋆ Qa ls v
  refine h (fun ls e ρ => Relend (opTable Tab) l T δ Qo ls e ρ) ?_
  intro ls e ρ hF
  refine relend_fold (opTable_mono Tab) ?_
  obtain ⟨γ, hγ⟩ := hF
  refine ⟨γ, fun α₁ hα₁ => ⟨fun ρm ρ' hm hc => ?_, (hγ α₁ hα₁).2⟩⟩
  have hN := (hγ α₁ hα₁).1
  -- the outer postcondition, and the same with the outer view beside it, left as garbage
  let Out : List SRec → Expr → WProp := fun ls'' t => box α₁ (ownWand l T δ ls''
    (fun σ => valPost Qo ls'' t σ ∨
      opTable Tab ls'' t (fun ls' e' => owner l T δ ls' ⋆ Relend (opTable Tab) l T δ Qo ls' e') σ))
  let Φ : List SRec → Expr → WProp := fun ls'' t σ =>
    ∃ σ₁ σ₂, ResU.CompS σ₁ σ₂ σ ∧ NoOwn σ₂ ∧ Out ls'' t σ₁
  refine wpG_garbage (Q := Out) (wpG_M_antiFrameX l α₁ T δ e ls Φ ρ'
    ⟨ρm, ρ, ResU.CompS.comm hc, hm, ?_⟩)
  -- 6.66's callback: the content handed out, 6.65 lends it at `α₂ ⊏ α₁`
  intro v ρa ρb ha hcab ρc ρd hv hccd
  obtain ⟨σ, hcσ, hcd⟩ := compS_reassoc (ResU.CompS.comm hcab) hccd
  refine wpG_M_frameX l T δ β hP v e ls _ ρd
    ⟨ρa, σ, hcd, ha, ρc, ρ, ResU.CompS.comm hcσ, hv, α₁, fun α₂ hα₂ => ?_⟩
  refine box_mono (wand_mono_right fun _ hw => wpG_mono (fun ls'' t τ hb => ?_) hw) ρ (hN α₂ hα₂)
  refine box_mono (ownWand_mono fun τ' hs => ?_) τ hb
  -- the inner owner, back from 6.65's exit, goes to 6.66's exit; the rest owes the outer
  obtain ⟨τo, τs, hcτ, ⟨w, τ₁, τ₂, hc₁₂, hown, hvw⟩, hS⟩ := hs
  obtain ⟨τ₂s, hc₂s, hc₁⟩ := compS_reassoc hc₁₂ hcτ
  refine ⟨w, τ₁, τ₂s, hc₁, hown, τ₂, τs, hc₂s, hvw,
    fun σv σ' hv' hcv => ⟨τs, σv, hcv, noOwn_ptoMutS hv', ?_⟩⟩
  refine ⟨fun w' π₁ π₂ hπ₁ hcπ π₃ π₄ hπ₃ hcπ' => ?_, hS.2⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcπ hcπ'
  rcases hS.1 with ⟨u, rfl, hq⟩ | hq
  · exact Or.inl ⟨u, rfl, s, τs, ResU.CompS.comm hρs, ⟨w', π₁, π₃, hs, hπ₁, hπ₃⟩, hq⟩
  · exact Or.inr (opTable_absorb hLR hq ⟨w', π₁, π₃, hs, hπ₁, hπ₃⟩ hρs)

/-- **A nested lend spanning stops, at the outer lender.** The outer owner beside a nested piece
gives the piece's `ewpTS`: `nested_relend`, then `ewpTS_M_frameR`. -/
theorem nested_spans (Tab : OpTab) (hLR : LinResume Tab) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (β : Life) (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β)
    (Qa : List SRec → Val → WProp) (ls : List SRec) (e : Expr) :
    Entails (owner l T δ ls ⋆ NestRelend (opTable Tab) l T δ Qa ls e)
      (ewpTS ls e (opTable Tab) (fun ls v => owner l T δ ls ⋆ Qa ls v)) := by
  rintro ρ ⟨ρo, ρr, hc, ho, hr⟩
  exact ewpTS_M_frameR (opTable Tab) (opTable_mono Tab) l T δ β hP _ ls e ρ
    ⟨ρo, ρr, hc, ho, nested_relend Tab hLR l T δ β hP Qa hr⟩

/-- **A nested piece at a yield.** The inner view is dropped (the inner lend's ghost end), the
inner owner is handed back beside the stop, and the continuation is a nested piece again. The
yield is linear and resuming. -/
theorem nest_yield (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en)
    (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {l : BoCa.Loc} {T : VTy} {δ : LSub} {Qa : List SRec → Val → WProp}
    {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    (h : ∀ ls, NestRelend (opTable Tab) l T δ Qa ls rest PMap.empty) (ls : List SRec) :
    NestRelend (opTable Tab) l T δ Qa ls (yieldSeq n i y rest) PMap.empty := by
  refine nestRelend_fold (opTable_mono Tab) ⟨⊤, fun α₁ _ => ⟨fun α₂ _ => ⟨fun ρm ρ' hm hc => ?_,
    ResU.inStratum_empty α₂⟩, ResU.inStratum_empty α₁⟩⟩
  rw [eq_of_compS_empty_left hc]
  refine freeze_at ρm ⟨ρm, PMap.empty, ResU.comp_empty_right ρm, hm, ?_,
    ResU.inStratum_empty α₂⟩
  intro w ρa ρb hown hcab ρc ρd hv hccd
  rw [eq_of_compS_empty_left hcab] at hccd
  refine ⟨ρd, PMap.empty, ResU.comp_empty_right ρd, ⟨w, ρa, ρc, hccd, hown, hv⟩,
    Or.inr (Or.inl ⟨.seq .hole rest, n, i, y, en, pure_sep_mk ⟨rfl, rfl, hTn, ha⟩
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, hy ls, ?_⟩⟩), ResU.inStratum_empty α₁⟩
  refine ⟨fun _ => rfl, fun ls' _ => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  rw [eq_of_compS_empty_left hcτ]
  exact nestRelend_step (opTable_mono Tab) (fun μ => Step1N.head (Head.seq μ rest) rfl) (h ls')

open GhostEnd.Instance in
/-- **Every hypothesis discharged.** A reborrow callback that yields once with both lends open,
then returns `()`, at the row `{yield : I32 ↠ 1}`: the outer owner beside the nested piece gives
its `ewpTS`. At the yield the inner lend is ghost-ended, the outer view refolded and dropped, and
the outer lend ghost-ended; at the resumption the outer re-lends at a fresh `α₁′`, 6.66 unfolds
the new view, and 6.65 re-lends below it. -/
theorem nested_spans_yield (δ : LSub) (l : BoCa.Loc) (ls : List SRec) :
    Entails (owner l .unit δ ls)
      (ewpTS ls (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.val .unit))
        (opTable (Row.tab [yieldOp] δ)) (fun ls v => owner l .unit δ ls ⋆ ⌜v = Val.unit⌝)) := by
  have hLR : LinResume (Row.tab [yieldOp] δ) := by
    intro n i en hT
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    obtain ⟨hm, -, -⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rfl, rfl⟩
  intro ρ ho
  refine nested_spans _ hLR l .unit δ ⊤ (fun _ _ σ h => by rw [h.1]; exact ResU.inStratum_empty _)
    _ ls _ ρ ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ho, ?_⟩
  refine nest_yield (Row.tab [yieldOp] δ) (en := yieldOp.ent δ)
    (by simp [Row.tab, Row.find, yieldOp]) rfl rfl ?_ (fun ls => ⟨rfl, 1, rfl⟩)
    (fun ls => nest_val (opTable_mono _) (fun _ => ⟨rfl, rfl⟩) ls) ls
  intro ls w σ h
  simp only [OpSig.ent, yieldOp] at h
  exact ⟨h.2, h.1⟩

end GhostEnd
