import Core.Chain.Frame835N
import Core.Chain.SI.LoopN

/-!
# The loop at `erwp`, answered *next* or *close*  `[spec §14]`

Interface entry E14 (`scope-831-interface.md`). Core's `cwp_iterate` (`Core/DivIterate.lean`) is
a coinduction up to `cwp` whose candidate holds the loop after a *next* and whose close path is
`inr ((f s′).2)` (`cwp_closePath`, `closing_iterate`). A `Div` row is a row of the chain's table
(E13), so the loop is `erwp_iterate`'s induction on the index (`SI/LoopN.lean`), with the tick's
answer read as Core's: *next* goes round again, below the index the tick is at; *close* runs the
close path `inr ((f s′).2)`, the close observation bound under `inr` (`erwp_bind`, the context
closed by `tabN_ctxClosed`).

`tabN_ctxClosed` is E5's `CtxClosed` at a row's table: a context with no handler that catches no
cancel carries the cancel obligations (`cancelOblN_plain₀`, Core's `plain_cancel₀`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-- The close observation `(f s).2`. -/
abbrev obsCN (f s : Val) : Expr := .app (.app (.val f) (.val s)) (.val closeV)

/-- `inr [·]`, the close path's context. -/
abbrev inrK : Kont := .appR (.val inrV) .hole

theorem inrK_plain : (∀ m, inrK.HasHnd m = false) ∧ (∀ m, inrK.Catches m = false) :=
  ⟨fun m => by simp [inrK, Kont.HasHnd, inrV], fun m => by simp [inrK, Kont.Catches, inrV]⟩

/-- **The loop rule at `erwp`, its tick answered *next* or *close*** (Core's `cwp_iterate`, E14).
A turn ends at `inl x` (done, in `QL`) or `inr s′` (in the invariant); then the tick: at *next*
the loop goes round at `s′`, below the tick's index; at *close* the close observation at `s′`
runs under `inr`, its answer `r` giving `QL` at `inr r` (`hQLR`). -/
theorem erwp_iterateC {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    {f : Val} (hK : T.CtxClosed (iterK f)) (hKi : T.CtxClosed inrK) {QL QR : PostN}
    (hQL : QL.Down) (hf : closedAt 0 f.1 = true) {I : Val → WProp} {en : OpEntN}
    (htick : T divEff 0 = some en) (hab : en.abort = false) (hq : en.q = .lin)
    (hta : ∀ k ls, en.PA k ls Val.unit PMap.empty)
    (htb : ∀ k ls w (ρ : WRes), en.PB k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty)
    (hIc : ∀ s ρ, I s ρ → closedAt 0 s.1 = true)
    (hturn : ∀ k s ls ρ, I s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (turnPostN I QL) k ls
        (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ k s ls ρ, I s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QR k ls (obsCN f s) ρ)
    (hQLR : ∀ k ls r ρ, QR k ls r ρ → QL k ls (Val.inj₂ r) ρ) :
    ∀ n s ls ρ, I s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QL n ls (iterateE f s) ρ := by
  have hD := opTableN_down hTD
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s ls ρ hI
  refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.iterate μ f s) rfl .hole) ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq]
  refine erwp_bind_le hΦ (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches]) hK n ?_ n le_rfl
    ls _ ρ (hturn n s ls ρ hI)
  rintro k ls' v σ hk (⟨x, rfl, hx⟩ | ⟨s', rfl, hs'⟩)
  · refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.case₁ μ x _ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₁ x) hx
  · refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.case₂ μ s' _ _) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterK_case₂]
    refine erwp_perform _ (by simp [Kont.HasHnd]) htick hab hq (compS_empty_left σ) (hta k ls')
      (fun ls'' _ k' hk' w σB XB hB hXB => ?_)
    obtain ⟨hw, rfl⟩ := htb k' ls'' w σB hB
    obtain rfl : XB = σ := ResU.CompS.functional hXB (ResU.comp_empty_right σ)
    refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterTurn_subst hf (hIc s' XB hs')]
    rcases hw with rfl | rfl
    · -- *next*: round again
      refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
      simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
        subst_closedAt _ _ (hIc s' XB hs') (Nat.zero_le _)]
      exact ih k' (by omega) s' ls'' XB hs'
    · -- *close*: the close path, `inr ((f s′).2)`
      refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
      simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
        subst_closedAt _ _ (hIc s' XB hs') (Nat.zero_le _)]
      change erwp (ℍ := ℍ) Φ (opTableN T) QL k' ls'' (inrK.plug (obsCN f s')) XB
      refine erwp_bind hΦ inrK inrK_plain.1 inrK_plain.2 hKi (fun k₁ ls₁ r ρ₁ hr => ?_) k' ls''
        _ XB (hclose k' s' ls'' XB hs')
      refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
      simp only [Kont.plug_hole]
      exact erwp_val (v := Val.inj₂ r) (hQLR k₁ ls₁ r ρ₁ hr)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Kont)

/-- **E5: a row's table is closed under a plain context** (`OpTabN.CtxClosed`): a context with no
handler that catches no cancel carries every cancel obligation of the table
(`cancelOblN_plain₀`). -/
theorem tabN_ctxClosed {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} (hΦ : (Θ.view c).Down)
    (G : CTy) (K : Kont) (hH : ∀ m, K.HasHnd m = false) (hC : K.Catches 0 = false) :
    (tabN (ℍ := ℍ) G δ Θ c).CtxClosed K := by
  intro m i en P hT hP k ls K' x ρ h
  rw [tabN_rowOf] at hT
  obtain ⟨o, -, rfl⟩ := tabN_effOf_some_find hT
  simp only [entN] at hP
  split at hP
  · rw [finN_eq] at hP
    split at hP
    · cases hP
    · cases hP
      rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
      exact cancelOblN_plain₀ hΦ K hH hC o.fin h
  · cases hP

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
