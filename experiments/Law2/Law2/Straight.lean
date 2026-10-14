import Law2.Mixed

/-!
# Law2 — straight-line borrowers at every mixed stack

A borrower that holds a mixed stack `σ` of lends open across its stops is D16.1's piece at `σ`
(`OpenS`). This file builds the piece for the straight-line borrowers — `yield y₁; …; yield yₙ; E`
with `E` stop-free — from one hypothesis on `E`, the continuation after the last stop: **at every
re-lend of the stack, handed the views the re-lend makes afresh, `E` runs to an answer in
`[top]`** (`RunsAt`). That is the suspended continuation re-lent: the property `KappaRelends`
states for one re-making, read at the stack's re-lends.

* `openS_of_run`: a stop-free continuation that runs at every re-lend is the piece.
* `openS_yield_ds`: a yield in front, every lend ghost-ended and re-lent (`openS_yield_any` at the
  stop's own drop flags).
* `openS_chain`: the straight-line borrower is the piece, by induction on its yields.
* `runsAt_of_typed`: **a continuation Core's typing derives runs at every re-lend**, when its
  context is rebuilt from the views at each re-lend: the fundamental property at the re-lent
  reading `extS δ σ αs`. This is `kappa_relend`'s argument at the stack's readings.
* `law2_straight`: the borrower beside the owners of the stack's lenders is its `ewpTS`
  (`fold_mixed`), at every mixed stack, every depth.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

section
variable {δ : LSub} {Tab : OpTab}

/-- **The continuation runs at every re-lend**: at every lifetime vector of the stack in nesting
order, handed the views its drop flags ask for, `E` runs to an answer in `[top]`. -/
def RunsAt (δ : LSub) (σ : LStack) (ds : List Bool) (Qa : List SRec → Val → WProp)
    (E : Expr) : Prop :=
  ∀ (αs : List Life) (ls : List SRec), αs.length = σ.length → List.IsChain (· < ·) αs →
    (∀ a ∈ αs, a < ⊤) → ∀ ρv, vwS δ [] σ ds αs ls ρv →
      wpTS (ℍ := ℍ) ls E (fun ls'' v => boxTop αs (Qa ls'' v)) ρv

/-- A re-lend is strictly below `⊤`: each lifetime is below the one it replaces. -/
theorem lt_top_of_forall₂ : ∀ {a b : List Life}, List.Forall₂ (· < ·) a b → ∀ x ∈ a, x < ⊤
  | _, _, .nil, _, hx => by simp at hx
  | _, _, .cons h hs, x, hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact lt_of_lt_of_le h le_top
      · exact lt_top_of_forall₂ hs x hx

/-- **A stop-free continuation that runs at every re-lend is D16.1's piece**, holding nothing of
its own: at each unfolding it is handed the views afresh. -/
theorem openS_of_run {σ : LStack} {Qa : List SRec → Val → WProp} {ds : List Bool} {E : Expr}
    (hE : RunsAt (ℍ := ℍ) δ σ ds Qa E) (αi : List Life) (ls : List SRec) :
    OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls E PMap.empty := by
  refine openS_fold fun αi' hlt hch => ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
  rw [List.append_nil] at hch ⊢
  rw [eq_of_compS_empty_left hc]
  rw [List.take_length] at hw
  have hlen := (vwS_length hw).2
  have h := (wpTS_iff_wpG _ _ _ _).mp (hE αi' ls hlen hch (lt_top_of_forall₂ hlt) w hw)
  exact wpG_mono (fun ls'' t ρ hq => by
    obtain ⟨v, hv, hb⟩ := hq
    exact Or.inl ⟨v, hv, ghostS_of_boxTop hlen hch hb⟩) h

/-- **A yield in front of the piece, at the stop's own drop flags.** Every view is dropped (every
lend ghost-ended), and the continuation is the piece again at the next re-lend. -/
theorem openS_yield_ds {σ : LStack} (hx : AllCross σ Tab) {n i : UInt32} {en : OpEnt}
    (hTn : Tab n i = some en) (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {Qa : List SRec → Val → WProp} {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    {ds : List Bool}
    (h : ∀ ls αi, OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls rest PMap.empty)
    (αi : List Life) (ls : List SRec) :
    OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls (yieldSeq n i y rest) PMap.empty := by
  refine openS_fold fun αi' _ hch => ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
  rw [List.append_nil] at hch ⊢
  rw [eq_of_compS_empty_left hc]
  rw [List.take_length] at hw
  have hlen := (vwS_length hw).2
  refine wpG_here ls _ _ w (Or.inr (stopS_of_full hx hlen (dropS_of_vwS hw)
    (ghostS_of_boxTop hlen hch ⟨?_, fun a _ => ResU.inStratum_empty a⟩)
    (ResU.comp_empty_right w)))
  refine Or.inl ⟨.seq .hole rest, n, i, y, en, pure_sep_mk ⟨rfl, rfl, hTn, ha⟩
    ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, hy ls, ?_⟩⟩
  refine ⟨fun _ => rfl, fun ls' _ => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  rw [eq_of_compS_empty_left hcτ]
  exact openS_step (fun μ => Step1N.head (Head.seq μ rest) rfl) (h ls' αi')

/-- **The straight-line borrower is D16.1's piece**: yields at a linear resuming operation every
entry crosses, then a continuation that runs at every re-lend. Induction on the yields. -/
theorem openS_chain {σ : LStack} (hx : AllCross σ Tab) {n i : UInt32} {en : OpEnt}
    (hTn : Tab n i = some en) (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {Qa : List SRec → Val → WProp} {ds : List Bool} {E : Expr}
    (hE : RunsAt (ℍ := ℍ) δ σ ds Qa E) :
    ∀ ys : List Val, (∀ y ∈ ys, ∀ ls, en.PA ls y PMap.empty) → ∀ (αi : List Life) (ls : List SRec),
      OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls (chain n i ys E) PMap.empty
  | [], _, αi, ls => openS_of_run hE αi ls
  | y :: ys, hys, αi, ls =>
      openS_yield_ds hx hTn ha hq hPB (hys y (List.mem_cons_self ..))
        (fun ls' αi' => openS_chain hx hTn ha hq hPB hE ys
          (fun y' hy' => hys y' (List.mem_cons_of_mem _ hy')) αi' ls') αi ls

/-- **A continuation Core's typing derives runs at every re-lend**, when at each re-lend its
context is rebuilt from the views handed (`hctx`) and its answer is in `[top]` (`hQ`): the
fundamental property at the re-lent reading `extS δ σ αs`. Views the context does not hold are
dropped as garbage (`wpTS_frame_noOwn`). -/
theorem runsAt_of_typed {σ : LStack} {ds : List Bool} {Qa : List SRec → Val → WProp}
    {Δ : LifeCtx} {Γ : Ctx VTy} {E : Expr} {B : VTy} (hd : CDerives Δ Γ E (.comp (.ret B)))
    {γ : List Val}
    (hctx : ∀ (αs : List Life) (ls : List SRec), αs.length = σ.length →
      List.IsChain (· < ·) αs → (∀ a ∈ αs, a < ⊤) → ∀ ρv, vwS δ [] σ ds αs ls ρv →
        Δ.Models (extS δ σ αs) ∧ ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧
          gDenC (ℍ := ℍ) ls (extS δ σ αs) Γ γ ρg)
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ) :
    RunsAt (ℍ := ℍ) δ σ ds Qa (substAll γ E) := by
  intro αs ls hlen hch htop ρv hv
  obtain ⟨hδ, ρg, ρd, hc, hno, hg⟩ := hctx αs ls hlen hch htop ρv hv
  have hS : SemC Δ Γ E (.ret B) := fundamentalC (ℍ := ℍ) hd
  have hrun : wpTS ls (substAll γ E) (fun ls'' => vCE (ℍ := ℍ) none true B ls'' (extS δ σ αs)) ρg :=
    hS (extS δ σ αs) γ ls ρg hδ hg
  refine wpTS_frame_noOwn (R := fun ρ => NoOwn ρ) (fun _ h => h) ls _ _ ρv
    ⟨ρd, ρg, ResU.CompS.comm hc, hno, ?_⟩
  exact wpTS_mono (fun ls'' v ρ h => hQ αs ls'' v ρ hch h) ρg hrun

/-- **Law 2 for straight-line borrowers, at every mixed stack.** A borrower `yield y₁; …;
yield yₙ; E` holding a mixed stack `σ` of lends open across its yields, every yield at a linear
resuming operation crossing every entry, whose continuation `E` runs at every re-lend, is, beside
the owners of the stack's lenders, its `ewpTS`, answering with those owners. One induction on the
yields (`openS_chain`) and one on the stack (`fold_mixed`); no case on the depth. -/
theorem law2_straight (hLR : LinResume Tab) (hL : Tab.Local) {β : Life} {σ : LStack}
    (hσ : MixedStack σ) (hx : AllCross σ Tab)
    (hP : ∀ e ∈ σ, ∀ ls w ρ, vCE (ℍ := ℍ) none true e.T ls δ w ρ → ρ.InStratum β)
    (hadm : ∀ e ∈ σ, ∀ v, e.k = .imm v → AdmWf e.T δ)
    {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en) (ha : en.abort = false)
    (hq : en.q = .lin) (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {ds : List Bool} {E : Expr} (hE : RunsAt (ℍ := ℍ) δ σ ds Qa E)
    {ys : List Val} (hys : ∀ y ∈ ys, ∀ ls, en.PA ls y PMap.empty)
    {bs : List Life} (hd : ds.length = σ.length) (hb : bs.length = σ.length)
    (hβ : ∀ a ∈ bs, a ≤ β) (ls : List SRec) {ρo : WRes} (ho : ownersM (ℍ := ℍ) δ σ ls ρo) :
    ewpTS (ℍ := ℍ) ls (chain n i ys E) (opTable Tab) (withOwnersM δ σ Qa) ρo :=
  fold_mixed hLR hL hσ hx hP hadm Qa hQa ds bs hd hb hβ ls _ ρo PMap.empty ρo ho
    (fun ls₁ _ => openS_chain hx hTn ha hq hPB hE ys hys bs ls₁) (ResU.comp_empty_right ρo)

end

end Law2

end
