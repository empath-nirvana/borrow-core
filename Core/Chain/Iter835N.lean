import Core.Chain.Fuel835N
import Core.DivIterate

/-!
# `iterate` at `SemJN`  `[spec §14]`

Core's `iterate_compatX` (`Core/DivIterate.lean`) reads the step `f` at `!U(S ⊸ F_Σ(B ⊕ S) & F_Σ R)`
and runs `cwp_iterate` with the invariant `𝒱⟦S⟧` on the state. A `Div` row is a row of the
chain's table (E13), so the loop is E14's induction on the index (`erwp_iterateC`), with two
readings the chain adds:

* **the invariant is read at the index.** `𝒱⟦S⟧` is step-indexed: the state a turn answers at the
  index `k` is the next turn's below the tick, at `k′ < k`, by downward closure. The step itself is
  owed at every index up to the one `iterate` is applied at (`⊸`'s clause), so the turns are owed
  up to that index (`erwp_iterateCI`'s `N`);
* **the state is consistent with the loop's view.** The step is applied at the loop's view, and
  `⊸`'s clause reads that view consistent with the argument; the state a turn answers is consistent
  with it (`erwp_consistentAns`, the row's answers read at the view, `tabN_ansC`).

The tick's answer is either *next*, which goes round again (Core's `turnK_next`), or *close*, which
runs the close path `inr ((f s′).2)` (Core's `turnK_close`, `inrV_steps`). Core's `PureSteps`
read these steps at any `f` and `s′`, so `erwp_iterateCI` asks no closedness of them.

* `erwp_iterateCI`: E14 at an invariant read at the index, up to an index `N`;
* `tickB_sig`: a row holding `Div` finds `tick`'s signature at `Div`'s key;
* `iterate_compatN`: the constant at `SemJN` (Core's `iterate_compatX`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-- The turn's postcondition at the index, its invariant read at the index: done at `inl x`, in
`Q_L`, or going on at `inr s′`, in the invariant at the index the turn ends at. -/
def turnPostNI (I : Nat → Val → WProp) (QL : PostN) : PostN := fun k ls v ρ =>
  (∃ x, v = Val.inj₁ x ∧ QL k ls (Val.inj₁ x) ρ) ∨ (∃ s', v = Val.inj₂ s' ∧ I k s' ρ)

/-- **E14 at an invariant read at the index** (Core's `cwp_iterate`): a turn ends at `inl x` (done)
or `inr s′`, the invariant at the index it ends at; then the tick: at *next* the loop goes round
again below the tick's index, the invariant read there by its downward closure; at *close* the close
path `inr ((f s′).2)` runs. The turns and the close paths are owed up to the index `N`. -/
theorem erwp_iterateCI {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    {f : Val} (hK : T.CtxClosed (iterK f)) (hKi : T.CtxClosed inrK) {QL QR : PostN}
    (hQL : QL.Down) {I : Nat → Val → WProp}
    (hIle : ∀ k k' s ρ, k' ≤ k → I k s ρ → I k' s ρ) {en : OpEntN}
    (htick : T divEff 0 = some en) (hab : en.abort = false) (hq : en.q = .lin)
    (hta : ∀ k ls, en.PA k ls Val.unit PMap.empty)
    (htb : ∀ k ls w (ρ : WRes), en.PB k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty)
    (N : Nat)
    (hturn : ∀ k, k ≤ N → ∀ s ls ρ, I k s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (turnPostNI I QL) k ls
        (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ k, k ≤ N → ∀ s ls ρ, I k s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) QR k ls (obsCN f s) ρ)
    (hQLR : ∀ k ls r ρ, QR k ls r ρ → QL k ls (Val.inj₂ r) ρ) :
    ∀ n, n ≤ N → ∀ s ls ρ, I n s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QL n ls (iterateE f s) ρ := by
  have hD := opTableN_down hTD
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN s ls ρ hI
  refine erwp_det hΦ hD hQL (fun μ => step1Only_plug (Head.iterate μ f s) rfl .hole) ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq]
  refine erwp_bind_le hΦ (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches]) hK n ?_ n le_rfl
    ls _ ρ (hturn n hnN s ls ρ hI)
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
    have hs'' := hIle k k' s' XB (by omega) hs'
    rcases hw with rfl | rfl
    · -- *next*: round again
      refine erwp_pureSteps hΦ hD hQL (BoCa.Fig16.LogRel.Core.turnK_next f s') ?_
      exact ih k' (by omega) (by omega) s' ls'' XB hs''
    · -- *close*: the close path, `inr ((f s′).2)`
      refine erwp_pureSteps hΦ hD hQL (BoCa.Fig16.LogRel.Core.turnK_close f s') ?_
      change erwp (ℍ := ℍ) Φ (opTableN T) QL k' ls'' (inrK.plug (obsCN f s')) XB
      refine erwp_bind hΦ inrK inrK_plain.1 inrK_plain.2 hKi (fun k₁ ls₁ r ρ₁ hr => ?_) k' ls''
        _ XB (hclose k' (by omega) s' ls'' XB hs'')
      refine erwp_pureSteps hΦ hD hQL (BoCa.Fig16.LogRel.Core.inrV_steps r) ?_
      exact erwp_val (v := Val.inj₂ r) (hQLR k₁ ls₁ r ρ₁ hr)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

/-- **`tick`'s signature**: `1 ↠^lin Next`. -/
theorem tickB_sig {q : Qual} {A B : VTy} (h : tickB q A B = true) :
    q = .lin ∧ A = .unit ∧ B = nextTy := by
  simp only [tickB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, hA⟩, hB⟩ := h
  cases A <;> simp [VTy.isUnitB] at hA
  cases B <;> simp [VTy.isNextB] at hB
  rename_i B₁ B₂
  cases B₁ <;> cases B₂ <;> simp [VTy.isUnitB] at hB
  exact ⟨rfl, rfl, rfl⟩

/-- **`iterate` is sound at `SemJN`**, at a row holding `Div` (Core's `iterate_compatX`): the step
`f` and the state `s` from the argument; the step read at the loop's own world and view
(`LocTy.extR_refl`, its resource empty); E14 at the invariant `𝒱⟦S⟧ ∧ ConsistentX`, read at the
index (`erwp_iterateCI`), the turn's answer consistent with the view (`erwp_consistentAns`), the
tick the row's `tick` (`Row.divB_find`). -/
theorem iterate_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {Sg : Row} {St B R : VTy}
    (hS : Row.divB Sg = true) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .iterate)) (.val (iterTy Sg St B R)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.val (.prim .iterate))) PMap.empty
  rw [show substAll γ (.val (.prim .iterate)) = .val (.prim .iterate) from
    psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  refine erwp_val (v := Val.prim .iterate) ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k hk v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨f, s, σf, σs, rfl, hcfs, ⟨rfl, hf⟩, hs⟩ := hv
  obtain rfl := eq_of_compS_empty_left hcfs
  have hΦ := LocTy.view_down hΘ'.1 c''
  have hTd := tabN_down (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ Θ' hΘ'.1 c''
  refine (cN_effOf Sg (.sum B R) δ Θ' c'' k ls' _ _).mpr ?_
  -- the row's `tick`
  obtain ⟨o, hfo, hto⟩ := Row.divB_find hS
  obtain ⟨hoq, hoA, hoB⟩ := tickB_sig hto
  have htick : tabN (ℍ := ℍ) (CTy.effOf Sg (.sum B R)) δ Θ' c'' divEff 0 = some (entN o.q o.B
      (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ' k v ρ)
      (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ' k v ρ ∧ ConsistentX c'' ρ)
      (finN (ℍ := ℍ) o.fin δ Θ' c'')) := by
    rw [tabN_effOf_find, hfo]; rfl
  -- the step, at the loop's world and view
  have hstep : ∀ j, j ≤ k → ∀ s' ls₁ ρ₁, vN (ℍ := ℍ) St δ Θ' j s' ρ₁ → ConsistentX c'' ρ₁ →
      cN (ℍ := ℍ) (.amp (CTy.effOf Sg (.sum B St)) (CTy.effOf Sg R)) δ Θ' c'' j ls₁
        (.app (.val f) (.val s')) ρ₁ := by
    intro j hj s' ls₁ ρ₁ hs' hc'
    exact hf Θ' (LocTy.extR_refl Θ' _) hΘ' c'' (consistentX_empty c'') ls₁ c'' j hj s' ρ₁ ρ₁
      (compS_empty_left ρ₁) hs' hc'
  let I : Nat → Val → WProp := fun j s' ρ₁ => vN (ℍ := ℍ) St δ Θ' j s' ρ₁ ∧ ConsistentX c'' ρ₁
  refine erwp_iterateCI (I := I) (QL := fun k _ v ρ => vN (ℍ := ℍ) (.sum B R) δ Θ' k v ρ)
    (QR := fun k _ v ρ => vN (ℍ := ℍ) R δ Θ' k v ρ) hΦ hTd
    (tabN_ctxClosed hΦ _ _ (fun m => by simp [iterK, Kont.HasHnd]) (by simp [iterK, Kont.Catches]))
    (tabN_ctxClosed hΦ _ _ inrK_plain.1 (inrK_plain.2 0))
    (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun j j' s' ρ₁ hj ⟨h₁, h₂⟩ => ⟨vN_le hj h₁, h₂⟩) htick
    (by simp [entN, hoq])
    hoq (fun j _ => by rw [hoA]; exact ⟨rfl, rfl⟩)
    (fun j _ w ρ₁ hB => by
      have hB' : vN (ℍ := ℍ) o.B δ Θ' j w ρ₁ := hB.1
      rw [hoB] at hB'
      rcases hB' with ⟨v₁, rfl, rfl, rfl⟩ | ⟨v₂, rfl, rfl, rfl⟩
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr rfl, rfl⟩)
    k ?_ ?_ (fun _ _ r _ h => Or.inr ⟨r, rfl, h⟩) k le_rfl s ls' _ ⟨hs, hcon⟩
  · -- a turn: `(f s′).1`, its answer consistent with the view
    rintro j hj s' ls₁ ρ₁ ⟨hs', hc'⟩
    have h₁ := (cN_effOf Sg (.sum B St) δ Θ' c'' j ls₁ _ _).mp (hstep j hj s' ls₁ ρ₁ hs' hc').1
    rw [tabN_effOf_ret Sg (.sum B St) (.sum B R)] at h₁
    have h₂ := erwp_consistentAns (tabN_ansC _ δ Θ' c'') j j le_rfl ls₁ _ ρ₁ h₁ hc'
    refine erwp_mono (fun k₁ ls₂ v₁ ρ₂ hq => ?_) (opTableN_local _) j ls₁ _ ρ₁ h₂
    obtain ⟨-, hq, hcq, -⟩ := hq
    rcases hq with ⟨x, rfl, hx⟩ | ⟨s'', rfl, hs''⟩
    · exact Or.inl ⟨x, rfl, Or.inl ⟨x, rfl, hx⟩⟩
    · exact Or.inr ⟨s'', rfl, hs'', hcq⟩
  · -- the close path's observation `(f s′).2`
    rintro j hj s' ls₁ ρ₁ ⟨hs', hc'⟩
    have h₂ := (cN_effOf Sg R δ Θ' c'' j ls₁ _ _).mp (hstep j hj s' ls₁ ρ₁ hs' hc').2
    rw [tabN_effOf_ret Sg R (.sum B R)] at h₂
    exact h₂

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
