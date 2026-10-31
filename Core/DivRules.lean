import Core.EffRules

/-!
# Core — `Div`: a frame around a segment, bind and `[sub]` at `cwp`  `[spec §14, §19]`

A row's table `T` holds `Div` when its entry at `(divEff, 0)` is `tick`'s (`OpEnt.IsTick`);
`OpTab.DivOK T` says that the entry, if any, is.

* **A plain frame around a computation of `cwp`, one segment** (`cwpF_frame`): the segment is
  `ewp_frame_plain_or` at the table beside it, the tick's; a tick inside the frame owes the frame
  around its continuation, which is in the candidate `Y`, and in `Closing` by
  `ewp_frame_plain` at the closing table.
* **Bind** (`cwp_bind`): by coinduction up to `cwp`, the candidate the frame around a
  computation of `cwp`, one segment at a time.
* **`[sub]`** (`cwp_sub`): the row grows.
* **`tick ()`** (`cwp_tick`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The tick's entry -/

theorem _root_.BoCa.BoLo.Kont.comp_hole (K : Kont) : K.comp .hole = K := by
  induction K <;> simp_all [BoCa.BoLo.Kont.comp]

theorem compS_empty_eq {ρ ρ' : WRes} (h : ResU.CompS ρ PMap.empty ρ') : ρ' = ρ :=
  ResU.CompS.functional h (ResU.comp_empty_right ρ)

theorem sep_emp_elim {P : WProp} {ρ : WRes} (h : (P ⋆ emp) ρ) : P ρ := by
  obtain ⟨σ₁, σ₂, hc, hp, ⟨rfl, -⟩⟩ := h
  rw [compS_empty_eq hc]; exact hp

/-- `tick`'s entry: must resume, not abortive, `1 ↠ Next`. -/
def OpEnt.IsTick (en : OpEnt) : Prop :=
  en.q = .lin ∧ en.abort = false ∧ (∀ ls v ρ, en.PA ls v ρ ↔ v = .unit ∧ ρ = PMap.empty) ∧
    ∀ ls w ρ, en.PB ls w ρ ↔ (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty

/-- The entry at `Div`'s key, if any, is `tick`'s. -/
def OpTab.DivOK (T : OpTab) : Prop := ∀ en, T divEff 0 = some en → en.IsTick

theorem OpTab.DivOK.keyNA {T : OpTab} (h : T.DivOK) : T.KeyNA := fun en hT => (h en hT).2.1

theorem OpTab.divOK_of_none {T : OpTab} (h : T divEff 0 = none) : T.DivOK :=
  fun en hT => by rw [h] at hT; cases hT

/-- `𝒱⟦1⟧`: `()` at the empty resource. -/
theorem vC_unit_iff {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    vC true .unit ls δ v ρ ↔ v = .unit ∧ ρ = PMap.empty :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- `𝒱⟦Next⟧`: *next* or *close*, at the empty resource. -/
theorem vC_next_iff {ls : List SRec} {δ : LSub} {w : Val} {ρ : WRes} :
    vC true nextTy ls δ w ρ ↔ (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty := by
  constructor
  · rintro (⟨v, ρ₁, ρ₂, hc, ⟨rfl, rfl⟩, hu⟩ | ⟨v, ρ₁, ρ₂, hc, ⟨rfl, rfl⟩, hu⟩)
    · obtain ⟨rfl, rfl⟩ := hu
      exact ⟨Or.inl rfl, eq_of_compS_empty_left hc⟩
    · obtain ⟨rfl, rfl⟩ := hu
      exact ⟨Or.inr rfl, eq_of_compS_empty_left hc⟩
  · rintro ⟨rfl | rfl, rfl⟩
    · exact Or.inl ⟨.unit, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨.unit, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- `tick`'s signature gives `tick`'s entry. -/
theorem OpSig.isTick_ent {o : OpSig} (δ : LSub) (h : tickB o.q o.A o.B = true) :
    (o.ent δ).IsTick := by
  obtain ⟨n, i, q, A, B, fin, rc⟩ := o
  simp only [tickB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, hA⟩, hB⟩ := h
  cases A <;> simp [VTy.isUnitB] at hA
  cases B <;> simp [VTy.isNextB] at hB
  rename_i B₁ B₂
  cases B₁ <;> cases B₂ <;> simp [VTy.isUnitB] at hB
  exact ⟨rfl, rfl, fun ls _ _ => vC_unit_iff (ls := ls) (δ := δ),
    fun ls _ _ => vC_next_iff (ls := ls) (δ := δ)⟩

/-- **A row holds `Div`** exactly when the operation it finds at `Div`'s key is `tick`. -/
theorem Row.divB_iff {S : Row} :
    Row.divB S = true ↔ ∃ o, Row.find S divEff 0 = some o ∧ tickB o.q o.A o.B = true := by
  induction S with
  | nil => simp [Row.divB, CTy.effOf, CTy.divAt, Row.find]
  | cons o S ih =>
      simp only [Row.divB, CTy.effOf, CTy.divAt]
      by_cases hk : o.n = divEff ∧ o.i = 0
      · rw [if_pos hk]
        have hf : Row.find (o :: S) divEff 0 = some o := by
          simp [Row.find, List.find?, hk.1.symm, hk.2.symm]
        rw [hf]
        exact ⟨fun h => ⟨o, rfl, h⟩, fun ⟨o', ho', h⟩ => by cases ho'; exact h⟩
      · rw [if_neg hk]
        have hf : Row.find (o :: S) divEff 0 = Row.find S divEff 0 := by
          have : decide (divEff = o.n ∧ (0 : UInt32) = o.i) = false := by
            simp only [decide_eq_false_iff_not]
            rintro ⟨h₁, h₂⟩; exact hk ⟨h₁.symm, h₂.symm⟩
          simp only [Row.find, List.find?, this]
        rw [hf, ← ih, Row.divB, divAt_effOf]

theorem Row.divB_find {S : Row} (h : Row.divB S = true) :
    ∃ o, Row.find S divEff 0 = some o ∧ tickB o.q o.A o.B = true := Row.divB_iff.mp h

/-- A row that holds `Div` has `tick`'s entry at `Div`'s key. -/
theorem Row.divOK_of_divB {S : Row} (h : Row.divB S = true) (δ : LSub) :
    (Row.tab S δ).DivOK := by
  obtain ⟨o, hf, ho⟩ := Row.divB_find h
  intro en hT
  simp only [Row.tab, hf, Option.map_some] at hT
  cases hT
  exact OpSig.isTick_ent δ ho

/-- A row whose operation at `Div`'s key is not `tick` does not hold `Div`. -/
theorem Row.divB_false_of_find {S : Row} (h : ∀ o, Row.find S divEff 0 = some o →
    tickB o.q o.A o.B = false) : Row.divB S = false := by
  cases hd : Row.divB S with
  | false => rfl
  | true =>
      obtain ⟨o, hf, ho⟩ := Row.divB_find hd
      rw [h o hf] at ho; cases ho

/-- A row none of whose operations has `tick`'s signature does not hold `Div`. -/
theorem Row.divB_of_noTick {S : Row} (h : ∀ o ∈ S, tickB o.q o.A o.B = false) :
    Row.divB S = false :=
  Row.divB_false_of_find fun o hf => h o (Row.find_mem hf).1

/-- `Row.divB S = false`, at a row read off by its operations' signatures. -/
macro "div_free" : tactic => `(tactic| first
  | decide
  | exact Row.divB_of_noTick (by
      simp (config := { decide := true }) [Row.ofEff, tickB, VTy.isUnitB, VTy.isNextB]))

/-- A row of abortive operations does not hold `Div`. -/
theorem Row.divB_of_abort {S : Row} (h : ∀ o ∈ S, o.abort = true) : Row.divB S = false := by
  refine Row.divB_false_of_find fun o hf => ?_
  have ha := h o (Row.find_mem hf).1
  obtain ⟨n, i, q, A, B, fin, rc⟩ := o
  simp only [OpSig.abort, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
  simp [tickB, ha.2]

/-- A row whose operations found at `Div`'s key are abortive does not hold `Div`. -/
theorem Row.divB_of_find_abort {S : Row} (h : ∀ n i o, Row.find S n i = some o → o.abort = true) :
    Row.divB S = false := by
  refine Row.divB_false_of_find fun o hf => ?_
  have ha := h _ _ o hf
  obtain ⟨n, i, q, A, B, fin, rc⟩ := o
  simp only [OpSig.abort, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
  simp [tickB, ha.2]

/-- A row without `Div`'s name does not hold `Div`. -/
theorem Row.divB_of_without {S : Row} (h : ∀ o ∈ S, o.n ≠ divEff) : Row.divB S = false := by
  refine Row.divB_false_of_find fun o hf => ?_
  obtain ⟨hm, hn, -⟩ := Row.find_mem hf
  exact absurd hn (h o hm)

/-! ### The tick's stop -/

/-- The tick's stop, unpacked: `tick ()` under `K`, its continuation owed at *next* and *close*. -/
theorem tickStop_inv {T : OpTab} (hT : T.DivOK)
    {Φ : List SRec → Expr → WProp} {ls : List SRec} {t : Expr} {ρ : WRes}
    (h : performStop T.only0 ls t Φ ρ) :
    ∃ (K : Kont) (en : OpEnt), t = K.plug tickE ∧ K.HasHnd divEff = false ∧ T divEff 0 = some en ∧ en.IsTick ∧
      ∀ ls', Ext ls ls' ρ → ∀ w, w = nextV ∨ w = closeV → Φ ls' (K.plug (.val w)) ρ := by
  obtain ⟨K, n, i, v, en, hp⟩ := h
  obtain ⟨⟨rfl, hK, hTn, ha⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨rfl, rfl, hT0⟩ := OpTab.only0_some hTn
  have ht := hT en hT0
  obtain ⟨rfl, rfl⟩ := (ht.2.2.1 ls v ρa).mp hA
  obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
  refine ⟨K, en, rfl, hK, hT0, ht, fun ls' he w hw => ?_⟩
  exact (hcont ls' he).1 w PMap.empty ρ ((ht.2.2.2 ls' w _).mpr ⟨hw, rfl⟩)
    (ResU.comp_empty_right ρ)

/-- **A tick in a frame `K`**, as a stop: it owes `K` at each answer. -/
theorem tickStop_mk {T : OpTab} {en : OpEnt} (hT : T divEff 0 = some en) (ht : en.IsTick)
    {Φ : List SRec → Expr → WProp} (K : Kont) (hK : K.HasHnd divEff = false) {ls : List SRec}
    {ρ : WRes}
    (h : ∀ ls', Ext ls ls' ρ → ∀ w : Val, w = nextV ∨ w = closeV → Φ ls' (K.plug (.val w)) ρ) :
    performStop T.only0 ls (K.plug tickE) Φ ρ := by
  refine ⟨K, divEff, 0, .unit, en, pure_sep_mk ⟨rfl, hK, by rw [OpTab.only0_key]; exact hT,
    ht.2.1⟩ ⟨PMap.empty, ρ, compS_empty_left ρ, (ht.2.2.1 ls .unit _).mpr ⟨rfl, rfl⟩, ?_, ?_⟩⟩
  · intro hq; rw [ht.1] at hq; cases hq
  · refine fun ls' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq => absurd ht.1 hq⟩
    obtain ⟨hw, rfl⟩ := (ht.2.2.2 ls' w τ₁).mp hB
    rw [compS_empty_eq hc]
    exact h ls' he w hw

/-- The tick's stop under a frame `K` with no handler of `Div`: the frame joins the
continuation. -/
theorem tickStop_frame {T : OpTab} (hT : T.DivOK) {Φ Ψ : List SRec → Expr → WProp} (K : Kont)
    (hK : K.HasHnd divEff = false) {ls : List SRec} {t : Expr} {ρ : WRes}
    (hΦ : ∀ ls' e, Ext ls ls' ρ → Φ ls' e ρ → Ψ ls' (K.plug e) ρ)
    (h : performStop T.only0 ls t Φ ρ) : performStop T.only0 ls (K.plug t) Ψ ρ := by
  obtain ⟨K₁, en, rfl, hK₁, hT0, ht, hcont⟩ := tickStop_inv hT h
  rw [← Kont.plug_comp]
  refine tickStop_mk hT0 ht (K.comp K₁) (by rw [hasHnd_comp, hK, hK₁]; rfl) fun ls' he w hw => ?_
  rw [Kont.plug_comp]
  exact hΦ ls' _ he (hcont ls' he w hw)

/-- **`tick ()`**, at the empty resource: its continuation, the hole, answers *next* or
*close*.  `[spec §14]` -/
theorem cwp_tick {T : OpTab} (hT : T.DivOK) {en : OpEnt} (hT0 : T divEff 0 = some en)
    {Q : List SRec → Val → WProp} (hQ : ∀ ls w, w = nextV ∨ w = closeV → Q ls w PMap.empty)
    (ls : List SRec) : cwp T Q ls tickE PMap.empty := by
  have ht := hT en hT0
  refine cwp_roll (ewp_fold (divTab_mono _ _ _) (wpG_here _ _ _ _ (Or.inr (Or.inr ?_))))
  refine tickStop_mk (K := .hole) hT0 ht rfl fun ls' _ w hw => ⟨?_, ?_⟩
  · exact cwp_of_ewp hT.keyNA (ewp_val (opTable_mono _) (hQ ls' w hw))
  · exact ewp_val (opTable_mono _) (hQ ls' w hw)

/-! ### A plain frame -/

theorem OpTab.le_erase0 {T T' : OpTab} (h : T.Le T') : T.erase0.Le T'.erase0 := by
  intro n i en hT
  unfold OpTab.erase0 at hT ⊢
  split at hT
  · cases hT
  · rw [if_neg (by assumption)]; exact h n i en hT

theorem OpTab.le_only0 {T T' : OpTab} (h : T.Le T') : T.only0.Le T'.only0 := by
  intro n i en hT
  unfold OpTab.only0 at hT ⊢
  split at hT
  · rw [if_pos (by assumption)]; exact h n i en hT
  · cases hT

theorem OpTab.le_closeAt {T T' : OpTab} (h : T.Le T') : T.closeAt.Le T'.closeAt := by
  intro n i en hT
  unfold OpTab.closeAt at hT ⊢
  split at hT
  · rw [if_pos (by assumption)]
    cases hT₀ : T n i with
    | none => rw [hT₀] at hT; cases hT
    | some en₀ =>
        rw [hT₀] at hT; cases hT
        obtain ⟨en', hT', hle⟩ := h n i en₀ hT₀
        refine ⟨en'.closeOnly, by rw [hT']; rfl, hle.1, hle.2.1, hle.2.2.1, ?_, hle.2.2.2.2⟩
        show (fun ls w ρ => en₀.PB ls w ρ ∧ w = closeV) = fun ls w ρ => en'.PB ls w ρ ∧ w = closeV
        rw [hle.2.2.2.1]
  · rw [if_neg (by assumption)]; exact h n i en hT


/-- The frame conditions at `T` give those at the table without `Div`'s key. -/
theorem frame_conds_erase0 {T : OpTab} {Fr : List SRec → WProp} {K : Kont}
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ') :
    (∀ n i en, T.erase0 n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ) ∧
    (∀ n i en, T.erase0 n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty) ∧
    (∀ n i en, T.erase0 n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ') := by
  have h : ∀ {n i en}, T.erase0 n i = some en → T n i = some en := fun {n i en} h => by
    unfold OpTab.erase0 at h; split at h
    · cases h
    · exact h
  exact ⟨fun n i en hT => hW n i en (h hT), fun n i en hT => hU n i en (h hT),
    fun n i en hT => hK n i en (h hT)⟩

/-- The frame conditions at `T` give those at the closing table. -/
theorem frame_conds_closeAt {T : OpTab} {Fr : List SRec → WProp} {K : Kont}
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ') :
    (∀ n i en, T.closeAt n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ) ∧
    (∀ n i en, T.closeAt n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty) ∧
    (∀ n i en, T.closeAt n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ') := by
  have h : ∀ {n i en}, T.closeAt n i = some en → ∃ en', T n i = some en' ∧
      en.q = en'.q ∧ en.abort = en'.abort ∧ en.fin = en'.fin := fun {n i en} h => by
    unfold OpTab.closeAt at h; split at h
    · cases hT : T n i with
      | none => rw [hT] at h; cases h
      | some en' => rw [hT] at h; cases h; exact ⟨en', rfl, rfl, rfl, rfl⟩
    · exact ⟨en, h, rfl, rfl, rfl⟩
  refine ⟨fun n i en hT ha => ?_, fun n i en hT hq => ?_, fun n i en hT ha hq => ?_⟩
  · obtain ⟨en', h', -, hab, -⟩ := h hT; exact hW n i en' h' (hab ▸ ha)
  · obtain ⟨en', h', hq', -, -⟩ := h hT; exact hU n i en' h' (hq' ▸ hq)
  · obtain ⟨en', h', hq', hab, hf⟩ := h hT
    intro ls K₁ ρ σ ρ' hc hF hcs P hP
    exact hK n i en' h' (hab ▸ ha) (hq' ▸ hq) ls K₁ ρ σ ρ' (fun P' hP' => hc P' (hf ▸ hP')) hF hcs
      P (hf ▸ hP)

/-- **A plain frame around a computation of `Closing`**: `ewp_frame_plain_or` at the closing
tables, the row growing from `T` to `T′`. -/
theorem closing_frame {T T' : OpTab} (hTT : T.Le T') (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (Q₁ Q : List SRec → Val → WProp)
    (hkc : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (Closing T' Q ls (K.plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : Closing T Q₁ ls e ρ) {ρ₂ ρ' : WRes}
    (hF : Fr ls ρ₂) (hc : ResU.CompS ρ ρ₂ ρ') : Closing T' Q ls (K.plug e) ρ' := by
  obtain ⟨hWc, hUc, hKc⟩ := frame_conds_closeAt (K := K) hW hU hK
  exact (ewp_orBot (opTable_mono _)).mp (ewp_frame_plain_or _ _ (OpTab.le_closeAt hTT) Table.bot
    Table.bot Table.bot_const.mono K hH hC Fr hFs hFe hWc hUc hKc (fun _ _ _ _ _ _ _ h => h.elim)
    Q₁ Q (fun ls v σ hσ => (ewp_orBot (opTable_mono _)).mpr (hkc ls v σ hσ))
    ((ewp_orBot (opTable_mono _)).mpr h) hF hc)

/-- **A plain frame around a computation of `cwp`, one segment**, the row growing from `T` to
`T′`, at any target candidate `Y` that holds the frame around every computation of `cwp` (`hY`).
`[spec §14]` -/
theorem cwpF_frame {T T' : OpTab} (hT : T.DivOK) (hT' : T'.DivOK) (hTT : T.Le T') (K : Kont)
    (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (Q₁ Q : List SRec → Val → WProp) (Y : List SRec → Expr → WProp)
    (hY : ∀ ls e ρ ρ₂ ρ', cwp T Q₁ ls e ρ → Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
      Y ls (K.plug e) ρ')
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwpF T' Q Y ls (K.plug (.val v))))
    (hkc : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (Closing T' Q ls (K.plug (.val v)))) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cwp T Q₁ ls e ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' → cwpF T' Q Y ls (K.plug e) ρ' := by
  obtain ⟨hWe, hUe, hKe⟩ := frame_conds_erase0 (K := K) hW hU hK
  intro ls e ρ he ρ₂ ρ' hF hc
  refine ewp_frame_plain_or T.erase0 T'.erase0 (OpTab.le_erase0 hTT) _ _
    (Table.Const.mono fun _ _ _ _ _ h => h) K hH hC Fr hFs hFe hWe hUe hKe ?_ Q₁ Q hk
    (cwp_out he) hF hc
  intro ls' t Φ Φ' σ₁ σ₂ σ hp hF' hcσ
  obtain ⟨K₁, en, rfl, hK₁, hT0, ht, hcont⟩ := tickStop_inv hT hp
  obtain ⟨en', hT0', -⟩ := hTT _ _ _ hT0
  rw [← Kont.plug_comp]
  refine tickStop_mk hT0' (hT' en' hT0') (K.comp K₁) (by rw [hasHnd_comp, hH, hK₁]; rfl)
    fun ls'' he w hw => ?_
  have ho := hcont ls'' (he.left hcσ) w hw
  have hF'' := hFe ls' ls'' σ₂ (he.right hcσ) hF'
  rw [Kont.plug_comp]
  exact ⟨hY _ _ _ σ₂ σ ho.1 hF'' hcσ,
    closing_frame hTT K hH hC Fr hFs hFe hW hU hK Q₁ Q hkc ho.2 hF'' hcσ⟩

/-- `Closing` of a computation of `cwp`: a segment's ticks owe `Closing`, so answered *close* at
every tick, it ends. -/
theorem closing_of_cwpF {T : OpTab} {Q : List SRec → Val → WProp}
    {W : List SRec → Expr → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cwpF T Q W ls e ρ) : Closing T Q ls e ρ := by
  refine ewp_ind (fun ls e ρ => Closing T Q ls e ρ) ?_ h
  intro ls e ρ hs
  refine ewp_fold (opTable_mono _) (wpG_mono (fun ls' t σ ht => ?_) hs)
  rcases ht with hv | ht | ht
  · exact Or.inl hv
  · -- a stop of the row but the tick
    refine Or.inr (opTable_le (fun n i en hT => ⟨en, ?_, OpEnt.Le.refl en⟩) ht)
    unfold OpTab.erase0 at hT; unfold OpTab.closeAt
    split at hT
    · cases hT
    · rw [if_neg (by assumption)]; exact hT
  · -- a tick: its continuation is in `Closing` at *close*
    obtain ⟨K, n, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨rfl, rfl, hT0⟩ := OpTab.only0_some hT
    refine Or.inr (Or.inl ⟨K, divEff, 0, v, en.closeOnly, pure_sep_mk ⟨rfl, hK,
      by rw [OpTab.closeAt_key, hT0]; rfl, ha⟩ ⟨ρa, ρk, hcak, hA, hu, fun ls'' he =>
        ⟨fun w τ₁ τ₂ hB hc => ((hcont ls'' he).1 w τ₁ τ₂ hB.1 hc).2, (hcont ls'' he).2⟩⟩⟩)

theorem closing_of_cwp {T : OpTab} {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : cwp T Q ls e ρ) : Closing T Q ls e ρ :=
  closing_of_cwpF (cwp_out h)

/-! ### Bind -/

/-- **`[let]` and bind at `cwp`.**  A plain frame `K` with `Fr` around a computation of `cwp` at
`Q₁`, every answer of which the frame continues at `cwp` at `Q`, is at `cwp` at `Q`: by
coinduction up to `cwp`, the candidate the frame around a computation of `cwp`, one segment at a
time (`cwpF_frame`).  `[spec §14, §19]` -/
theorem cwp_bind {T : OpTab} (hT : T.DivOK) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwp T Q ls (K.plug (.val v)))) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cwp T Q₁ ls e ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' → cwp T Q ls (K.plug e) ρ' := by
  let W : List SRec → Expr → WProp := fun ls x ρ' => ∃ e ρ ρ₂, x = K.plug e ∧
    cwp T Q₁ ls e ρ ∧ Fr ls ρ₂ ∧ ResU.CompS ρ ρ₂ ρ'
  have hW' : ∀ ls x ρ, W ls x ρ →
      cwpF T Q (fun ls e ρ => W ls e ρ ∨ cwp T Q ls e ρ) ls x ρ := by
    rintro ls x ρ' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩
    exact cwpF_frame hT hT (OpTab.Le.refl T) K hH hC Fr hFs hFe hW hU hK Q₁ Q _
      (fun ls e ρ ρ₂ ρ' he hF hc => Or.inl ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩)
      (fun ls v σ hσ => cwpF_mono (fun _ _ _ h => Or.inr h) (cwp_out (hk ls v σ hσ)))
      (fun ls v σ hσ => closing_of_cwp (hk ls v σ hσ)) he hF hc
  intro ls e ρ he ρ₂ ρ' hF hc
  exact cwp_coind_up hW' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩

/-- **Bind at `cwp`, the frame's table above the computation's.** `cwp_bind` with the computation
at `T` and its frame at `T' ≥ T`: `cwpF_frame` at the two tables, by the same coinduction.
`[spec §14, §19]` -/
theorem cwp_bind_le {T T' : OpTab} (hT : T.DivOK) (hT' : T'.DivOK) (hTT : T.Le T') (K : Kont)
    (hH : ∀ n, K.HasHnd n = false)
    (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ')
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwp T' Q ls (K.plug (.val v)))) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cwp T Q₁ ls e ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' → cwp T' Q ls (K.plug e) ρ' := by
  let W : List SRec → Expr → WProp := fun ls x ρ' => ∃ e ρ ρ₂, x = K.plug e ∧
    cwp T Q₁ ls e ρ ∧ Fr ls ρ₂ ∧ ResU.CompS ρ ρ₂ ρ'
  have hW' : ∀ ls x ρ, W ls x ρ →
      cwpF T' Q (fun ls e ρ => W ls e ρ ∨ cwp T' Q ls e ρ) ls x ρ := by
    rintro ls x ρ' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩
    exact cwpF_frame hT hT' hTT K hH hC Fr hFs hFe hW hU hK Q₁ Q _
      (fun ls e ρ ρ₂ ρ' he hF hc => Or.inl ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩)
      (fun ls v σ hσ => cwpF_mono (fun _ _ _ h => Or.inr h) (cwp_out (hk ls v σ hσ)))
      (fun ls v σ hσ => closing_of_cwp (hk ls v σ hσ)) he hF hc
  intro ls e ρ he ρ₂ ρ' hF hc
  exact cwp_coind_up hW' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩

/-! ### `[sub]` -/

theorem closing_sub {T T' : OpTab} (h : T.Le T') {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hc : Closing T Q ls e ρ) : Closing T' Q ls e ρ :=
  ewp_sub (OpTab.le_closeAt h) hc

/-- **`[sub]` at `cwp`**: the row grows.  `[spec §14, §19]` -/
theorem cwp_sub {T T' : OpTab} (h : T.Le T') {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hc : cwp T Q ls e ρ) : cwp T' Q ls e ρ := by
  refine cwp_coind (W := cwp T Q) (fun ls e ρ hc => ?_) hc
  refine ewp_mono (divTab_mono _ _ _) (fun ls t Φ σ hd => ?_) (fun _ _ _ h => h) (cwp_out hc)
  rcases hd with hd | hd
  · exact Or.inl (opTable_le (OpTab.le_erase0 h) hd)
  · exact Or.inr (performStop_le (OpTab.le_only0 h)
      (performStop_mono _ _ _ _ _ σ (fun ls e ρ hw => ⟨hw.1, closing_sub h hw.2⟩) hd))

/-! ### A row's table without the tick -/

/-- The table, without `Div`'s key when `er`. -/
def OpTab.eraseIf : Bool → OpTab → OpTab
  | true, T => T.erase0
  | false, T => T

theorem OpTab.eraseIf_some {er : Bool} {T : OpTab} {n i : UInt32} {en : OpEnt}
    (h : T.eraseIf er n i = some en) :
    T n i = some en ∧ (er = true → ¬ (n = divEff ∧ i = 0)) := by
  cases er
  · exact ⟨h, fun h => by cases h⟩
  · simp only [OpTab.eraseIf, OpTab.erase0] at h
    split at h
    · cases h
    · exact ⟨h, fun _ => by assumption⟩

theorem OpTab.eraseIf_of {er : Bool} {T : OpTab} {n i : UInt32} {en : OpEnt} (h : T n i = some en)
    (hk : er = true → ¬ (n = divEff ∧ i = 0)) : T.eraseIf er n i = some en := by
  cases er
  · exact h
  · simp only [OpTab.eraseIf]; rw [OpTab.erase0_ne (hk rfl)]; exact h

end BoCa.Fig16.LogRel.Core

end
