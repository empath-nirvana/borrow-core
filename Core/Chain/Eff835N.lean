import Core.Chain.Stop835N

/-!
# `[sub]`, `[perform]` and `[raise]` at `SemJN`  `[spec §19, §27]`

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

/-! ### A row's table -/

/-- **A row's table at a key is the entry of the operation the row finds there** (Core's
`Row.tab`, read through `Row.tab_find`/`Row.tab_some`). -/
theorem tabN_effOf_find (S : Row) (R : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life)
    (n i : UInt32) :
    tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c n i = (Row.find S n i).map (fun o =>
      entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ) (finN (ℍ := ℍ) o.fin δ Θ c)) := by
  induction S with
  | nil => simp [CTy.effOf, tabN, OpTabN.empty, Row.find]
  | cons o S ih =>
      show extTabN o.n o.i _ (tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c) n i = _
      unfold extTabN Row.find
      by_cases h : n = o.n ∧ i = o.i
      · simp only [if_pos h, List.find?_cons, decide_eq_true h, Option.map_some]
      · simp only [if_neg h, List.find?_cons, decide_eq_false h]
        exact ih

/-- **An entry of a row's table is the entry of an operation the row finds.** -/
theorem tabN_effOf_some_find {S : Row} {R : VTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life}
    {n i : UInt32} {en : OpEntN} (h : tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c n i = some en) :
    ∃ o, Row.find S n i = some o ∧ en = entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ) (finN (ℍ := ℍ) o.fin δ Θ c) := by
  rw [tabN_effOf_find] at h
  obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨o, hf, rfl⟩

/-- The table of a cancel row is the table of its layers. -/
theorem tabN_rowOf (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    ∀ F : CTy, tabN (ℍ := ℍ) F δ Θ c = tabN (ℍ := ℍ) (CTy.effOf F.rowOf .unit) δ Θ c
  | .eff m i q A B fin rc C => by
      simp only [CTy.rowOf, CTy.effOf, tabN]
      rw [tabN_rowOf δ Θ c C]
  | .ret _ => by simp [CTy.rowOf, CTy.effOf, tabN]
  | .arr _ _ => by simp [CTy.rowOf, CTy.effOf, tabN]
  | .amp _ _ => by simp [CTy.rowOf, CTy.effOf, tabN]
  | .top => by simp [CTy.rowOf, CTy.effOf, tabN]
  | .all _ _ _ => by simp [CTy.rowOf, CTy.effOf, tabN]
  | .nu _ => by simp [CTy.rowOf, CTy.effOf, tabN]

/-- **A cancel row's obligation** (Core's `finObl_eq`): none at `⊤`; otherwise the cancel run at
the row's table, read at the view. -/
theorem finN_eq_ite (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (F : CTy) :
    finN (ℍ := ℍ) F δ Θ c =
      if F.isTop then none else some (cancelOblN (ℍ := ℍ) (Θ.view c) (tabN (ℍ := ℍ) F δ Θ c)) := by
  cases F <;> simp [finN, tabN, CTy.isTop]

/-- The entry of an operation at its key. -/
theorem entN_le_of_leF {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {o o' : OpSig}
    (hs : o.Sig o')
    (hfin : capB o.q o.B = true → FinLeSN (finN (ℍ := ℍ) o.fin δ Θ c) (finN (ℍ := ℍ) o'.fin δ Θ c)) :
    (entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ) (finN (ℍ := ℍ) o.fin δ Θ c)).Le
      (entN o'.q o'.B (fun k v ρ => vN (ℍ := ℍ) o'.A δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) o'.B δ Θ k v ρ) (finN (ℍ := ℍ) o'.fin δ Θ c)) := by
  obtain ⟨-, -, hq, hA, hB, -⟩ := hs
  refine ⟨hq, by simp [entN, hq, hB], by simp [entN, hA], by simp [entN, hB], rfl,
    fun ha hq' => ?_⟩
  have hcap : capB o.q o.B = true := by
    simp only [entN, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at ha hq'
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
    rcases ha with ha | ha
    · exact ⟨hq', by simpa using ha⟩
    · exact absurd ha hq'
  simp only [entN, hcap, if_true, ← hq, ← hB]
  exact hfin hcap

/-- **A cancel row's obligation grows with the row** (Core's `finObl_mono`), along `FinLe`, by
Core's recursion on the cancel row. -/
theorem finN_mono (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (F : CTy) :
    ∀ {F' : CTy}, FinLe F F' → FinLeSN (finN (ℍ := ℍ) F δ Θ c) (finN (ℍ := ℍ) F' δ Θ c) := by
  intro F' h
  rw [finLe_iff] at h
  rw [finN_eq_ite δ Θ c F, finN_eq_ite δ Θ c F']
  rcases h with h | ⟨hF, h⟩
  · simp only [h, if_true]; exact trivial
  · cases hF' : F'.isTop
    · simp only [hF, Bool.false_eq_true, if_false, FinLeSN]
      intro k ls e ρ hc
      refine cancelOblN_le ?_ hc
      rw [tabN_rowOf δ Θ c F, tabN_rowOf δ Θ c F']
      intro n i en hT
      obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
      obtain ⟨o', hf', hs, hle⟩ := h n i o hf
      refine ⟨_, by rw [tabN_effOf_find, hf']; rfl, entN_le_of_leF hs fun hcap => ?_⟩
      exact finN_mono δ Θ c o.fin (hle (by simp [OpSig.finRead, hcap]))
    · simp only [if_true]; exact trivial
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- **E3: the table grows with the row** (Core's `effWp_sub`'s table step): `Σ ⊆ Σ′` gives
`OpTabN.Le` of their tables, at every answer type, world and view. -/
theorem tabN_le_of_rowLe {S S' : Row} (hle : RowLe S S') (R R' : VTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) :
    (tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c).Le (tabN (ℍ := ℍ) (CTy.effOf S' R') δ Θ c) := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
  obtain ⟨o', hf', hs, hfl⟩ := hle n i o hf
  exact ⟨_, by rw [tabN_effOf_find, hf']; rfl, entN_le_of_leF hs fun hcap =>
    finN_mono δ Θ c o.fin (hfl (by simp [OpSig.finRead, hcap]))⟩

/-- **`erwp` at a row grows with the row** (Core's `effWp_sub`). -/
theorem erwp_rowLe {S S' : Row} (hle : RowLe S S') {A : VTy} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cN (ℍ := ℍ) (CTy.effOf S A) δ Θ c n ls e ρ) : cN (ℍ := ℍ) (CTy.effOf S' A) δ Θ c n ls e ρ :=
  (cN_effOf S' A δ Θ c n ls e ρ).mpr (erwp_tabLe (tabN_le_of_rowLe hle A A δ Θ c) n ls e ρ
    ((cN_effOf S A δ Θ c n ls e ρ).mp h))

/-- **E6: an entry's cancel obligation holds of the empty region** (Core's `ent_start`). -/
theorem entN_start (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (o : OpSig) (k : Nat)
    (ls : List SRec) :
    cancelOKN (entN o.q o.B (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ)
      (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ) (finN (ℍ := ℍ) o.fin δ Θ c)) k ls .hole
      PMap.empty := by
  intro P hP
  simp only [entN] at hP
  split at hP
  · rw [finN_eq_ite] at hP
    split at hP
    · cases hP
    · cases hP; exact cancelOblN_start _ _ k ls
  · cases hP

/-! ### Values owning nothing -/

/-- **A value of an own-free type owns nothing** (Core's `vC_noOwn_of_ownFree`). -/
theorem vN_noOwn_of_ownFree {A : VTy} (hA : A.OwnFree) :
    ∀ {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}, vN (ℍ := ℍ) A δ Θ n v ρ → NoOwn ρ := by
  induction hA with
  | unit => intro δ Θ n v ρ h; rw [h.2]; exact noOwn_empty
  | zero => intro δ Θ n v ρ h; exact h.elim
  | int w => intro δ Θ n v ρ h; rw [h.2]; exact noOwn_empty
  | unk => intro δ Θ n v ρ h; rw [show ρ = PMap.empty from h]; exact noOwn_empty
  | opq k hk =>
      intro δ Θ n v ρ h
      rcases Opaque.rel_cases h with ⟨-, rfl, -⟩ | ⟨rfl, -⟩
      · exact noOwn_empty
      · exact absurd hk Opaque.tok_not_host
  | bang A => intro δ Θ n v ρ h; rw [h.1]; exact noOwn_empty
  | imm a A =>
      rintro δ Θ n v ρ ⟨β, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩
      exact ResU.restrict_single_other (by simp)
  | «mut» a A =>
      rintro δ Θ n v ρ ⟨β, -, b, -, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩
      exact ResU.restrict_single_other (by simp)
  | tensor _ _ ihA ihB =>
      rintro δ Θ n v ρ ⟨v₁, v₂, ρ₁, ρ₂, -, hc, h₁, h₂⟩
      exact noOwn_compS hc (ihA h₁) (ihB h₂)
  | sum _ _ ihA ihB =>
      rintro δ Θ n v ρ (⟨v₁, -, h₁⟩ | ⟨v₂, -, h₂⟩)
      · exact ihA h₁
      · exact ihB h₂

/-! ### The rules -/

/-- **`[sub]`** (Core's `sub_compatC`): a row may grow, its entries' cancel rows with it. -/
theorem sub_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (hle : RowLe S S') (h : SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S A))) :
    SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.effOf S' A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  exact erwp_rowLe hle (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

/-- **`[perform]`**, at any cancel row (Core's `perform_compatC`): the argument's run never
stops, and the operation stops at once at its entry. -/
theorem perform_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hna : o.abort = false)
    (h : SemJN (ℍ := ℍ) Δ Γ V (.val o.A)) :
    SemJN (ℍ := ℍ) Δ Γ (performE (opArgE o.n o.i V)) (.comp (CTy.effOf S o.B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine (cN_effOf S o.B δ Θ c n ls _ ρ).mpr ?_
  change erwp (ℍ := ℍ) _ _ _ n ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) ρ
  refine erwp_bind_pure_frame (LocTy.view_down hΘ.1 c) (opTableN_local _) _ _ ls
    (fun k _ v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ) (fun _ => BoLo.emp) (fun _ _ _ _ h => h) ?_
    (ResU.comp_empty_right ρ) (rwp_of_erwp_empty (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)) ⟨rfl, trivial⟩
  rintro k ls' v σ ⟨σ₁, σ₂, hc', hv, rfl, -⟩
  rw [ResU.CompS.functional hc' (ResU.comp_empty_right σ₁)]
  have hT : tabN (ℍ := ℍ) (CTy.effOf S o.B) δ Θ c o.n o.i = some (entN o.q o.B
      (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ) (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ)
      (finN (ℍ := ℍ) o.fin δ Θ c)) := by
    rw [tabN_effOf_find, hf]; rfl
  exact erwp_perform_here hT (by simpa [entN, OpSig.abort] using hna)
    (entN_start δ Θ c o) (fun _ _ _ _ h => h) hv

/-- **`[raise]`**: an abortive operation, at any answer type, its argument owning nothing (Core's
`raise_compatC`). -/
theorem raise_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig} {B : VTy}
    (hf : Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : ∀ δ Θ n v ρ, vN (ℍ := ℍ) o.A δ Θ n v ρ → NoOwn ρ)
    (h : SemJN (ℍ := ℍ) Δ Γ V (.val o.A)) :
    SemJN (ℍ := ℍ) Δ Γ (raiseE (opArgE o.n o.i V)) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine (cN_effOf S B δ Θ c n ls _ ρ).mpr ?_
  change erwp (ℍ := ℍ) _ _ _ n ls ((Kont.appR (.val (.prim .raise))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) ρ
  refine erwp_bind_pure_frame (LocTy.view_down hΘ.1 c) (opTableN_local _) _ _ ls
    (fun k _ v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ) (fun _ => BoLo.emp) (fun _ _ _ _ h => h) ?_
    (ResU.comp_empty_right ρ) (rwp_of_erwp_empty (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)) ⟨rfl, trivial⟩
  rintro k ls' v σ ⟨σ₁, σ₂, hc', hv, rfl, -⟩
  rw [ResU.CompS.functional hc' (ResU.comp_empty_right σ₁)]
  have hT : tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c o.n o.i = some (entN o.q o.B
      (fun k v ρ => vN (ℍ := ℍ) o.A δ Θ k v ρ) (fun k v ρ => vN (ℍ := ℍ) o.B δ Θ k v ρ)
      (finN (ℍ := ℍ) o.fin δ Θ c)) := by
    rw [tabN_effOf_find, hf]; rfl
  exact erwp_raise_here hT (by simpa [entN, OpSig.abort] using ha) hv (hd _ _ _ _ _ hv)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
