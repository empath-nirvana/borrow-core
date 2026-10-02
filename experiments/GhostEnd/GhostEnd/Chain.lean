import GhostEnd.Freeze
import Core.Fundamental
import Core.FoldImm
import Support.LogicalRelation.Adequacy

/-!
# GhostEnd — a borrower whose lend spans its yields

A borrower that keeps the borrow `m : Mut 'x T` live across a run of `yield`s:

    λm. perform yield y₁; … ; perform yield yₙ; N_f

where `N_f` uses `m` and is typed by the CBPV judgment. The yields reach an enclosing handler with
the lend open, which is O15.1's shape.

**Freeze.** At each yield the borrower's view `ℓ ↦ M_α` is dropped into the leftover `ρ⁺`. It is
a single `mut` cell, so it owns nothing. The variable still holds the location `ℓ`, as a value of
the stopped term. What remains of the share is the frame's other values, whose types outlive
`'x`, so it is in `[α]` by 6.60. The frame then takes the owner back by 6.65's exit
(`ewpTS_M_frameR`). Nothing runs.

**Resume.** The frame lends `ℓ` again at a fresh `α′`. The borrower's variable is in
`𝒱⟦Mut 'x T⟧_{δ[x ↦ α′]}` at once, because that relation is the location together with the cell
`ℓ ↦ M_{α′}` (`mutView`). The rest of the borrower is re-derived, not transported: `N_f`'s typing
holds at every `δ ∈ ⟦Δ, x ⊏ b⟧` (`fundamentalC`), and it is instantiated at `δ[x ↦ α′]`. The
other values do not mention `'x`, so their relation at `δ[x ↦ α′]` is their relation at `δ`.

* `relend_fin`: `N_f` from its typing, at every fresh lifetime, with the frame's other values.
* `relend_yield`: a yield, re-lending afresh at its resumption.
* `relend_chainΓ`, `relend_chain`: the whole borrower, by induction on its yields.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `perform (n, (i, y)); e`. -/
def yieldSeq (n i : UInt32) (y : Val) (e : Expr) : Expr :=
  .seq (performE (.val (opPayload n i y))) e

/-- `perform yield y₁; …; perform yield yₙ; e`. -/
def chain (n i : UInt32) : List Val → Expr → Expr
  | [], e => e
  | y :: ys, e => yieldSeq n i y (chain n i ys e)

/-- What the borrower hands back: the owner, and the answer at `B`. -/
def finPost (l : BoCa.Loc) (T B : VTy) (δ : LSub) (ls : List SRec) (r : Val) : WProp :=
  owner l T δ ls ⋆ vC true B ls δ r

/-- **The borrower's variable after a re-lend.** `𝒱⟦Mut 'x T⟧_{δ[x ↦ α]}(ℓ)` is the location and
the cell `ℓ ↦ M_α 𝒱⟦T⟧`. So the cell the frame lends at `α` puts the variable that still holds `ℓ`
in the relation at `δ[x ↦ α]`, whatever lifetime it was lent at before. -/
theorem mutView {x : LifeVar} {T : VTy} (hT : ¬ VFree x T) {l : BoCa.Loc} {α : Life}
    {ls : List SRec} {δ : LSub} {ρ : WRes}
    (h : ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρ) :
    vC true (.mut (.var x) T) ls (δ.extend x α) (.loc l) ρ := by
  refine ⟨α, interp_ext_self δ x α, l, pure_sep_mk rfl ?_⟩
  have e : (fun ls₀ => vC true T ls₀ (δ.extend x α)) = (fun ls₀ => vC true T ls₀ δ) :=
    funext fun ls₀ => vC_extend_of_not_free hT true ls₀ δ α
  show ptoMutS l α ls (fun ls₀ => vC true T ls₀ (δ.extend x α)) ρ
  rw [e]; exact h

/-- `δ[x ↦ α] ∈ ⟦Δ, x ⊏ b⟧` for `α ⊏ @bδ`, as `allI_compatX` builds it. -/
theorem models_extend {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β) {α : Life} (hlt : α ⊏ β) :
    (Δ.extend x b).Models (δ.extend x α) := by
  intro y u hy
  rw [LifeCtx.find?_extend] at hy
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl] at hy
    obtain rfl := Option.some.inj hy
    exact ⟨α, β, find?_extend_self δ x α,
      by rw [interp_extend_of_not_mentions hbx]; exact hβ, hlt⟩
  · rw [if_neg hxy] at hy
    obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
    exact ⟨m, k, by rw [find?_extend_ne δ α hxy]; exact hm,
      by rw [interp_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩

/-! ### Frames holding other values

The borrower's frames may hold values besides `m`. Their types do not mention `'x` and outlive it
(`Δ, x ⊏ b ⊢ Γ′ ⊐ 'x`). At a freeze they stay in the share, which is in `[α]` by 6.60
(`gSepC_outlives`). At a resumption they are in `𝒢⟦Γ′⟧` at the new assignment as they stand:
`𝒱⟦A⟧_{δ[x ↦ α′]} = 𝒱⟦A⟧_δ` when `'x ∉ A` (`vC_extend_of_not_free`), carried along `Ext`
(`gDenC_local`). Only `m` is re-lent. -/

/-- The frame's values at `δ` sit in `Res_α` for every `α ⊏ @bδ`, by 6.60 at `δ[x ↦ α]`. -/
theorem frame_outlives {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β) {Γ' : Ctx VTy}
    (hΓx : ∀ s ∈ Γ', s.live = true → ¬ VFree x s.ty)
    (hΓo : ∀ s ∈ Γ', s.live = true → VOutlives (Δ.extend x b) (.var x) s.ty)
    {ls : List SRec} {γ' : List Val} {ρ : WRes} (h : gSepC ls δ Γ' γ' ρ) {α : Life} (hα : α ⊏ β) :
    ρ.InStratum α := by
  have heq : gSepC ls δ Γ' γ' = gSepC ls (δ.extend x α) Γ' γ' :=
    gSepC_congr fun s hs hl => (vC_extend_of_not_free (hΓx s hs hl) true ls δ α).symm
  rw [heq] at h
  exact gSepC_outlives (models_extend hδ hbx hΔx hβ hα) (interp_ext_self δ x α) hΓo h

/-- **The borrower's last segment, re-derived at every lend.** `N_f` is typed at `m, Γ′` under
`Δ, x ⊏ b`. Its typing holds at `δ[x ↦ α]` for every `α ⊏ @bδ`. There `m` is the view lent at
`α` and the frame's values `γ′` stand as they are. It runs to an answer in `[α] 𝒱⟦B⟧`, and its
share hands the owner back. -/
theorem relend_fin {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B) {Γ' : Ctx VTy}
    (hΓx : ∀ s ∈ Γ', s.live = true → ¬ VFree x s.ty)
    (hΓo : ∀ s ∈ Γ', s.live = true → VOutlives (Δ.extend x b) (.var x) s.ty) {Nf : Expr}
    (hN : SemC (Δ.extend x b) (⟨.mut (.var x) T, true⟩ :: Γ') Nf (.ret (.box (.var x) B)))
    (Tb : Table) (hTb : Tb.Mono) (l : BoCa.Loc) (ls : List SRec) (γ' : List Val) (ργ : WRes)
    (hγ : gDenC ls δ Γ' γ' ργ) :
    Relend Tb l T δ (finPost l T B δ) ls (substAll (Val.loc l :: γ') Nf) ργ := by
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hγ
  refine relend_fold hTb ⟨β, fun α hα => ⟨fun ρm ρ₂ hm hc => ?_,
    frame_outlives hδ hbx hΔx hβ hΓx hΓo hgs hα⟩⟩
  have heq : gSepC ls δ Γ' γ' = gSepC ls (δ.extend x α) Γ' γ' :=
    gSepC_congr fun s hs hl => (vC_extend_of_not_free (hΓx s hs hl) true ls δ α).symm
  have hg : gDenC ls (δ.extend x α) (⟨.mut (.var x) T, true⟩ :: Γ') (Val.loc l :: γ') ρ₂ :=
    gDenC_mk (by simpa using hlen)
      ⟨ρm, ργ, ResU.CompS.comm hc, mutView hT hm, by rw [← heq]; exact hgs⟩
  have hw := hN (δ.extend x α) (Val.loc l :: γ') ls ρ₂ (models_extend hδ hbx hΔx hβ hα) hg
  refine wpG_mono (fun ls'' t σ ht => ?_) ((wpTS_iff_wpG _ _ _ _).mp hw)
  obtain ⟨r, rfl, hr⟩ := ht
  obtain ⟨α', hα', hBr, hout⟩ := hr
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  refine ⟨fun w ρa ρb ha hcab ρc ρd hc' hccd => Or.inl ⟨r, rfl, ?_⟩, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  exact ⟨s, σ, ResU.CompS.comm hρs, ⟨w, ρa, ρc, hs, ha, hc'⟩,
    by rwa [vC_extend_of_not_free hB] at hBr⟩

/-- **A yield with the lend open.** The borrower's view is dropped (`freeze_at`). The frame `Fr`
beside it (Kripke along `Ext`, in `Res_α` below a bound) stays in the share, which is therefore in
`[α]`. The owner the frame hands back goes to the continuation, and at the resumption the rest is
re-lendable again (`h`). The yield is linear, so its continuation is never cancelled. Cancelling
one would have to dispose of the owner, and the bare frame cannot. -/
theorem relend_yield (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en)
    (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {l : BoCa.Loc} {T : VTy} {δ : LSub} {Q : List SRec → Val → WProp}
    (Fr : List SRec → WProp) (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    {β : Life} (hFo : ∀ ls ρ, Fr ls ρ → ∀ α, α ⊏ β → ρ.InStratum α)
    {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    (h : ∀ ls ρ, Fr ls ρ → Relend (opTable Tab) l T δ Q ls rest ρ) (ls : List SRec)
    (ργ : WRes) (hF : Fr ls ργ) :
    Relend (opTable Tab) l T δ Q ls (yieldSeq n i y rest) ργ := by
  refine relend_fold (opTable_mono Tab)
    ⟨β, fun α hα => ⟨fun ρm ρ₂ hm hc => ?_, hFo ls ργ hF α hα⟩⟩
  refine freeze_at ρ₂ ⟨ρm, ργ, ResU.CompS.comm hc, hm, ?_⟩
  refine ⟨fun w ρa ρb hown hcab ρc ρd hv hccd => Or.inr (Or.inl ⟨.seq .hole rest, n, i, y, en,
    pure_sep_mk ⟨rfl, rfl, hTn, ha⟩ ⟨PMap.empty, ρd, compS_empty_left ρd, hy ls, ?_⟩⟩),
    hFo ls ργ hF α hα⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  unfold contShare
  refine ⟨fun hu => absurd (hq.symm.trans hu) (by decide),
    fun ls' hext => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  obtain rfl : τ₂ = ρd := ResU.CompS.functional hcτ (ResU.comp_empty_right ρd)
  refine ⟨s, ργ, ResU.CompS.comm hρs,
    ⟨w, ρa, ρc, hs, hown, vC_local true T ((hext.right hρs).right hs) hv⟩, ?_⟩
  exact relend_step (opTable_mono Tab) (fun μ => Step1N.head (Head.seq μ rest) rfl)
    (h ls' ργ (hFe ls ls' ργ (hext.left hρs) hF))

/-- **The whole borrower is re-lendable, its frame values carried**, by induction on its yields. -/
theorem relend_chainΓ {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B) {Γ' : Ctx VTy}
    (hΓx : ∀ s ∈ Γ', s.live = true → ¬ VFree x s.ty)
    (hΓo : ∀ s ∈ Γ', s.live = true → VOutlives (Δ.extend x b) (.var x) s.ty) {Nf : Expr}
    (hN : SemC (Δ.extend x b) (⟨.mut (.var x) T, true⟩ :: Γ') Nf (.ret (.box (.var x) B)))
    (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en)
    (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    (l : BoCa.Loc) (γ' : List Val) : ∀ (ys : List Val), (∀ y ∈ ys, ∀ ls, en.PA ls y PMap.empty) →
      ∀ ls ργ, gDenC ls δ Γ' γ' ργ → Relend (opTable Tab) l T δ (finPost l T B δ) ls
        (chain n i ys (substAll (Val.loc l :: γ') Nf)) ργ
  | [], _, ls, ργ, hγ =>
      relend_fin hδ hbx hΔx hβ hT hB hΓx hΓo hN _ (opTable_mono Tab) l ls γ' ργ hγ
  | y :: ys, hys, ls, ργ, hγ =>
      relend_yield Tab hTn ha hq hPB (fun ls => gDenC ls δ Γ' γ')
        (fun _ _ _ he h => gDenC_local he h)
        (fun _ _ h _ hα => frame_outlives hδ hbx hΔx hβ hΓx hΓo (gDenC_iff.mp h).2 hα)
        (hys y List.mem_cons_self)
        (relend_chainΓ hδ hbx hΔx hβ hT hB hΓx hΓo hN Tab hTn ha hq hPB l γ' ys
          (fun y' hy' => hys y' (List.mem_cons_of_mem _ hy'))) ls ργ hγ

/-- **The whole borrower is re-lendable**, `m` its only value: `relend_chainΓ` at `Γ′ = ∅`. -/
theorem relend_chain {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B) {Nf : Expr}
    (hN : SemC (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.ret (.box (.var x) B)))
    (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en)
    (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    (l : BoCa.Loc) (ys : List Val) (hys : ∀ y ∈ ys, ∀ ls, en.PA ls y PMap.empty)
    (ls : List SRec) :
    Relend (opTable Tab) l T δ (finPost l T B δ) ls
      (chain n i ys (substAll [Val.loc l] Nf)) PMap.empty :=
  relend_chainΓ (Γ' := []) hδ hbx hΔx hβ hT hB (fun _ h => absurd h (by simp))
    (fun _ h => absurd h (by simp)) hN Tab hTn ha hq hPB l [] ys hys ls PMap.empty
    (gDenC_nil ls δ)

end GhostEnd
