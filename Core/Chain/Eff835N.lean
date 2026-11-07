import Core.Chain.Stop835N

/-!
# `[sub]`, `[perform]` and `[raise]` at `SemJN₀`  `[spec §19, §27]`

Core's `sub_compatC`, `perform_compatC` and `raise_compatC` (`Core/EffFin.lean`), step by step, at
the chain relation, over the interface entries they reach for (`scope-831-interface.md` E3, E5,
E6, E7):

* **E3** (Core's `effWp_sub`, `finObl_mono`, `cancelObl_le`): a row's table at a key is the entry
  of the operation `Row.find` finds there (`tabN_effOf_find`); a cancel row's obligation is the
  cancel run at its layers' table, or none at `⊤` (`finN_eq_ite`); a cancel run is monotone in its
  table (`cancelOblN_le`); so the obligation grows with the cancel row (`finN_mono`, along
  `FinLe`, by Core's recursion on the cancel row) and the table with the row (`tabN_le_of_rowLe`);
* **E5** (Core's `ewp_bind_pure_frame`): a computation that never stops, framed, in front of an
  `erwp` at any table (`rwp_frame`, `erwp_bindR`). A value's judgment is `erwp` at the empty table,
  a run that never stops (`rwp_of_erwp_empty`);
* **E6** (Core's `ewp_perform_here`, `ent_start`, `cancelObl_start`): a `perform` stops at once;
  the cancel run of the empty region is in every cancel obligation of a row's entry;
* **E7** (Core's `ewp_raise_here`): a `raise` stops at once, at an argument owning nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload)

/-! ### A cancel run is monotone in its table -/

/-- A stop of `cancelTabN T` is one of `cancelTabN T′` when `T ≤ T′` (Core's `cancelTab`
monotonicity under `OpTab.Le`, which `cancelObl_le` reads). -/
theorem cancelTabN_le {T T' : OpTabN} (hT : T.Le T') :
    ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      cancelTabN T k ls t Ψ ρ → cancelTabN T' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases cancelTabN_local T k ls t Ψ Ψ' ρ hΨ h with ⟨K, err, hs⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨hpure, τa, τb, hc, he, hnb⟩ := pure_sep_iff.mp hs
    refine Or.inl ⟨K, err, pure_sep_mk hpure ⟨τa, τb, hc, ?_, hnb⟩⟩
    cases err with
    | none => exact he
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨⟨h₁, hTe, ha⟩, hPA, hnA⟩ := pure_sep_iff.mp he
        obtain ⟨en', hTe', hle⟩ := hT _ _ _ hTe
        exact ⟨m, j, w, en', pure_sep_mk ⟨h₁, hTe', hle.2.1 ▸ ha⟩ ⟨hle.2.2.1 ▸ hPA, hnA⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', h₃', hq, hab, hPA, hPB, hwc, hfl⟩ := hT n i en h₃
    refine Or.inr ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩ ⟨ρa, ρk, hc, hPA ▸ hA,
      fun hu' => hu (hq.trans hu'), fun ls' he => ?_⟩⟩
    rw [← hwc] at he
    refine ⟨fun k' hk' w => hPB ▸ (hcont ls' he).1 k' hk' w, fun hq' P hP => ?_⟩
    exact finLeSN_apply (hfl h₄ (hq ▸ hq')) hP (fun P₀ hP₀ => (hcont ls' he).2 (hq ▸ hq') P₀ hP₀)

/-- **A cancel obligation is monotone in its table** (Core's `cancelObl_le`). -/
theorem cancelOblN_le {Φ : LocFam} {T T' : OpTabN} (hT : T.Le T') {k : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : cancelOblN (ℍ := ℍ) Φ T k ls e ρ) :
    cancelOblN (ℍ := ℍ) Φ T' k ls e ρ :=
  erwp_mono (fun _ _ _ _ h => h) (cancelTabN_le hT) k ls e ρ h

/-- **The cancel run of the empty region** (Core's `cancelObl_start`): it ends at once, keeping no
error. -/
theorem cancelOblN_start (Φ : LocFam) (T : OpTabN) (k : Nat) (ls : List SRec) :
    cancelOblN (ℍ := ℍ) Φ T k ls (raiseE (.val (cancelVal none))) PMap.empty := by
  show erwp (ℍ := ℍ) Φ (cancelTabN T) _ k ls _ _
  rw [erwp_eq]
  refine rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_cancelVal none)
    (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inl ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩, noOwn_empty⟩⟩))

/-! ### Stops at once and pure prefixes -/

/-- **A pure prefix in front of an `erwp`, framing `R` through its run** (Core's
`ewp_bind_pure_frame`): a run that never stops (`rwp`), the frame carried by `rwp_frame`, then
the context at any table (`erwp_bindR`). -/
theorem erwp_bind_pure_frame {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) (K : Kont)
    (e : Expr) (ls : List SRec) (P : PostN) (R : List SRec → WProp) {Q : PostN}
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ)
    (h : ∀ k ls' (v : Val) ρ, (P k ls' v ⋆ R ls') ρ →
      erwp (ℍ := ℍ) Φ Tb Q k ls' (K.plug v.1) ρ)
    {n : Nat} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hw : rwp (ℍ := ℍ) Φ P n ls e ρ₁)
    (hR₂ : R ls ρ₂) : erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug e) ρ :=
  erwp_bindR hΦ hL K (rwp_mono (fun k ls' v ρ hp => h k ls' v ρ hp) (rwp_frame R hR hc hw hR₂))

/-- **A `perform` stops at once** (Core's `ewp_perform_here`): its continuation, the hole, answers
`Q` at every answer in `PB`, and its cancel run, of the empty region, holds at the entry's cancel
obligation (`hfin`). -/
theorem erwp_perform_here {Φ : LocFam} {T : OpTabN} {n i : UInt32} {en : OpEntN}
    (hT : T n i = some en) (ha : en.abort = false)
    (hfin : ∀ k ls, cancelOKN en k ls .hole PMap.empty) {Q : PostN}
    (hQ : ∀ k ls' w ρ, en.PB k ls' w ρ → Q k ls' w ρ) {k : Nat} {ls : List SRec} {v : Val}
    {ρ : WRes} (h : en.PA k ls v ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (performE (.val (opPayload n i v))) ρ := by
  rw [erwp_eq]
  refine rwpG_here (final_opPlug (K := .hole) (r := false) (payloadName_opPayload n i v)
    (by simp [OpFree, Kont.HasHnd])) (Or.inr (Or.inl
      ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, fun _ => rfl, fun ls' _ =>
          ⟨fun k' hk' w σ₁ σ₂ hB hc => ?_, fun _ => hfin k ls'⟩⟩⟩))
  rw [eq_of_compS_empty_left hc]
  simp only [erwpC, hk', if_true]
  exact erwp_val (hQ _ _ _ _ hB)

/-- **A `raise` stops at once, at an argument that holds nothing owned** (Core's
`ewp_raise_here`). -/
theorem erwp_raise_here {Φ : LocFam} {T : OpTabN} {n i : UInt32} {en : OpEntN}
    (hT : T n i = some en) (ha : en.abort = true) {Q : PostN} {k : Nat} {ls : List SRec}
    {v : Val} {ρ : WRes} (h : en.PA k ls v ρ) (hn : NoOwn ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (raiseE (.val (opPayload n i v))) ρ := by
  rw [erwp_eq]
  exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload n i v)
    (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr
      ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨h, hn⟩, noOwn_empty⟩⟩))

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
