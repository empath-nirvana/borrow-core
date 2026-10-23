import Core.EffWp

/-!
# Core — `Div`: the greatest fixed point's rules  `[spec §14, §19]`

The relation at a row that holds `Div` (`cwp`, `Core/DivDefs.lean`): monotonicity, coinduction,
and the facts every rule needs at every computation type, at `effWp`: a pure step in front, a
pure prefix in front, and the postcondition growing.  A computation of the least fixed point is in
the greatest (`cwp_of_ewp`), and at a table without `Div`'s key the two agree (`cwp_none`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Kont Step1N)
open BoCa.Lifetime (LSub)

/-! ### Rows that hold `Div` -/

theorem CTy.divAt_instT (S : VTy) : ∀ D : CTy, (D.instT S).divAt = D.divAt
  | .eff n i q _ A B fin D => by
      simp only [CTy.instT, CTy.divAt, CTy.divAt_instT S D]
  | .ret _ | .amp _ _ | .arr _ _ | .top | .all _ _ _ | .nu _ => by
      simp [CTy.instT, CTy.divAt]

/-! ### Two tables -/

theorem orTab_mono {A B : Table} (hA : A.Mono) (hB : B.Mono) : (orTab A B).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with h | h
  · exact Or.inl (hA ls t Φ Φ' ρ hΦ h)
  · exact Or.inr (hB ls t Φ Φ' ρ hΦ h)

theorem Table.Const.mono {Px : Table} (h : Table.Const Px) : Px.Mono :=
  fun ls t Φ Φ' ρ _ hp => h ls t Φ Φ' ρ hp

theorem Table.bot_const : Table.Const Table.bot := fun _ _ _ _ _ h => h

/-- **A table with the empty one beside it is the table.** -/
theorem ewp_orBot {Tb : Table} (hTb : Tb.Mono) {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} : ewpTS ls e (orTab Tb Table.bot) Q ρ ↔ ewpTS ls e Tb Q ρ :=
  ⟨ewp_mono hTb (fun _ _ _ _ h => h.elim id False.elim) (fun _ _ _ h => h),
   ewp_mono (orTab_mono hTb Table.bot_const.mono) (fun _ _ _ _ h => Or.inl h) (fun _ _ _ h => h)⟩

/-! ### The tables -/

theorem OpTab.erase0_key (T : OpTab) : T.erase0 divEff 0 = none := by
  simp [OpTab.erase0]

theorem OpTab.erase0_ne {T : OpTab} {n i : UInt32} (h : ¬ (n = divEff ∧ i = 0)) :
    T.erase0 n i = T n i := by
  simp [OpTab.erase0, h]

theorem OpTab.only0_some {T : OpTab} {n i : UInt32} {en : OpEnt} (h : T.only0 n i = some en) :
    n = divEff ∧ i = 0 ∧ T divEff 0 = some en := by
  unfold OpTab.only0 at h
  by_cases hk : n = divEff ∧ i = 0
  · rw [if_pos hk] at h; obtain ⟨rfl, rfl⟩ := hk; exact ⟨rfl, rfl, h⟩
  · rw [if_neg hk] at h; cases h

theorem OpTab.only0_key (T : OpTab) : T.only0 divEff 0 = T divEff 0 := by
  simp [OpTab.only0]

theorem OpTab.closeAt_key (T : OpTab) : T.closeAt divEff 0 = (T divEff 0).map OpEnt.closeOnly := by
  simp [OpTab.closeAt]

theorem OpTab.closeAt_ne {T : OpTab} {n i : UInt32} (h : ¬ (n = divEff ∧ i = 0)) :
    T.closeAt n i = T n i := by
  simp [OpTab.closeAt, h]

/-- A table with nothing at `Div`'s key is its own erasure. -/
theorem OpTab.erase0_none {T : OpTab} (h : T divEff 0 = none) : T.erase0 = T := by
  funext n i
  unfold OpTab.erase0
  by_cases hk : n = divEff ∧ i = 0
  · rw [if_pos hk]; obtain ⟨rfl, rfl⟩ := hk; exact h.symm
  · rw [if_neg hk]

/-- A table with nothing at `Div`'s key has no tick. -/
theorem OpTab.only0_none {T : OpTab} (h : T divEff 0 = none) (n i : UInt32) : T.only0 n i = none := by
  unfold OpTab.only0
  by_cases hk : n = divEff ∧ i = 0
  · rw [if_pos hk]; obtain ⟨rfl, rfl⟩ := hk; exact h
  · rw [if_neg hk]

theorem OpTab.closeAt_none {T : OpTab} (h : T divEff 0 = none) : T.closeAt = T := by
  funext n i
  unfold OpTab.closeAt
  by_cases hk : n = divEff ∧ i = 0
  · rw [if_pos hk]; obtain ⟨rfl, rfl⟩ := hk; rw [h]; rfl
  · rw [if_neg hk]

/-- A stop at an empty table is impossible. -/
theorem performStop_none {T : OpTab} (h : ∀ n i, T n i = none) {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} : ¬ performStop T ls t Φ ρ := by
  rintro ⟨K, n, i, v, en, hp⟩
  obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp
  rw [h] at hT; cases hT

/-! ### Monotonicity -/

theorem divTab_mono (T : OpTab) (Q : List SRec → Val → WProp) (W : List SRec → Expr → WProp) :
    (divTab T Q W).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with h | h
  · exact Or.inl (opTable_mono _ ls t Φ Φ' ρ hΦ h)
  · exact Or.inr h

theorem divTab_le {T : OpTab} {Q Q' : List SRec → Val → WProp} {W W' : List SRec → Expr → WProp}
    (hW : ∀ ls e ρ, W ls e ρ → W' ls e ρ)
    (hC : ∀ ls e ρ, Closing T Q ls e ρ → Closing T Q' ls e ρ)
    {ls : List SRec} {t : Expr} {Φ : List SRec → Expr → WProp} {ρ : WRes}
    (h : divTab T Q W ls t Φ ρ) : divTab T Q' W' ls t Φ ρ := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (performStop_mono _ ls t _ _ ρ (fun ls e ρ hw => ⟨hW ls e ρ hw.1, hC ls e ρ hw.2⟩) h)

theorem closing_mono {T : OpTab} {Q Q' : List SRec → Val → WProp}
    (hQ : ∀ ls v ρ, Q ls v ρ → Q' ls v ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Closing T Q ls e ρ) : Closing T Q' ls e ρ :=
  ewp_mono (opTable_mono _) (fun _ _ _ _ h => h) hQ h

theorem cwpF_mono {T : OpTab} {Q : List SRec → Val → WProp} {W W' : List SRec → Expr → WProp}
    (h : ∀ ls e ρ, W ls e ρ → W' ls e ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (hw : cwpF T Q W ls e ρ) : cwpF T Q W' ls e ρ :=
  ewp_mono (divTab_mono T Q W') (fun _ _ _ _ hd => divTab_le h (fun _ _ _ h => h) hd)
    (fun _ _ _ hq => hq) hw

/-! ### The greatest fixed point -/

/-- **Coinduction.** -/
theorem cwp_coind {T : OpTab} {Q : List SRec → Val → WProp} {W : List SRec → Expr → WProp}
    (hW : ∀ ls e ρ, W ls e ρ → cwpF T Q W ls e ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (hw : W ls e ρ) : cwp T Q ls e ρ :=
  ⟨W, hW, hw⟩

theorem cwp_out {T : OpTab} {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cwp T Q ls e ρ) : cwpF T Q (cwp T Q) ls e ρ := by
  obtain ⟨W, hW, hw⟩ := h
  exact cwpF_mono (fun _ _ _ h => cwp_coind hW h) (hW _ _ _ hw)

theorem cwp_roll {T : OpTab} {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cwpF T Q (cwp T Q) ls e ρ) : cwp T Q ls e ρ :=
  cwp_coind (W := cwpF T Q (cwp T Q)) (fun _ _ _ h => cwpF_mono (fun _ _ _ h => cwp_out h) h) h

/-- **Coinduction up to `cwp`**: a candidate need only reach `W ∪ cwp`. -/
theorem cwp_coind_up {T : OpTab} {Q : List SRec → Val → WProp} {W : List SRec → Expr → WProp}
    (hW : ∀ ls e ρ, W ls e ρ → cwpF T Q (fun ls e ρ => W ls e ρ ∨ cwp T Q ls e ρ) ls e ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (hw : W ls e ρ) : cwp T Q ls e ρ := by
  refine cwp_coind (W := fun ls e ρ => W ls e ρ ∨ cwp T Q ls e ρ) ?_ (Or.inl hw)
  rintro ls e ρ (hw | hc)
  · exact hW ls e ρ hw
  · exact cwpF_mono (fun _ _ _ h => Or.inr h) (cwp_out hc)

/-- The postcondition grows. -/
theorem cwp_post {T : OpTab} {Q Q' : List SRec → Val → WProp}
    (hQ : ∀ ls v ρ, Q ls v ρ → Q' ls v ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cwp T Q ls e ρ) : cwp T Q' ls e ρ := by
  refine cwp_coind (W := cwp T Q) (fun ls e ρ h => ?_) h
  exact ewp_mono (divTab_mono _ _ _) (fun _ _ _ _ hd => divTab_le (fun _ _ _ h => h)
    (fun _ _ _ h => closing_mono hQ h) hd) hQ (cwp_out h)

/-! ### Steps and pure prefixes -/

/-- A pure step in front. -/
theorem cwp_step {T : OpTab} {Q : List SRec → Val → WProp} {e e' : Expr}
    (h : ∀ μ : Heap, Step1N μ e μ e') {ls : List SRec} {ρ : WRes} (h' : cwp T Q ls e' ρ) :
    cwp T Q ls e ρ :=
  cwp_roll (ewp_step (divTab_mono _ _ _) h ls Q ρ (cwp_out h'))

/-- A pure prefix in front, framing `R` through its run. -/
theorem cwp_bind_pure_frame {T : OpTab} {Q : List SRec → Val → WProp} (K : Kont) (e : Expr)
    (ls : List SRec) (P : List SRec → Val → WProp) (R : List SRec → WProp)
    (hR : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls'))
    (h : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails ((P ls' v) ⋆ R ls') (cwp T Q ls' (K.plug (.val v)))) :
    Entails ((wpTS ls e P) ⋆ R ls) (cwp T Q ls (K.plug e)) :=
  fun ρ h' => cwp_roll (ewp_bind_pure_frame (divTab_mono _ _ _) K e ls P R Q hR
    (fun ls' hls v σ hσ => cwp_out (h ls' hls v σ hσ)) ρ h')

/-! ### The least fixed point is in the greatest -/

/-- The entry at `Div`'s key, if any, is not abortive. -/
def OpTab.KeyNA (T : OpTab) : Prop := ∀ en, T divEff 0 = some en → en.abort = false

/-- An entry answered at fewer answers owes less. -/
theorem performStop_closeAt {T : OpTab} {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : performStop T ls t Φ ρ) :
    performStop T.closeAt ls t Φ ρ := by
  obtain ⟨K, n, i, v, en, hp⟩ := h
  obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
  by_cases hk : n = divEff ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := hk
    refine ⟨K, divEff, 0, v, en.closeOnly, pure_sep_mk ⟨rfl, hK, by rw [OpTab.closeAt_key, hT]; rfl,
      ha⟩ ⟨ρa, ρk, hc, hA, hu, fun ls' he => ⟨fun w τ₁ τ₂ hB hcτ =>
        (hcont ls' he).1 w τ₁ τ₂ hB.1 hcτ, (hcont ls' he).2⟩⟩⟩
  · exact ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, by rw [OpTab.closeAt_ne hk]; exact hT, ha⟩
      ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩

theorem opTable_closeAt {T : OpTab} {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTable T ls t Φ ρ) :
    opTable T.closeAt ls t Φ ρ := by
  rcases h with h | ⟨K, n, i, v, en, hp⟩
  · exact Or.inl (performStop_closeAt h)
  · obtain ⟨⟨rfl, hK, hT, ha⟩, hr⟩ := pure_sep_iff.mp hp
    by_cases hk : n = divEff ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      exact Or.inr ⟨K, divEff, 0, v, en.closeOnly, pure_sep_mk ⟨rfl, hK,
        by rw [OpTab.closeAt_key, hT]; rfl, ha⟩ hr⟩
    · exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, by rw [OpTab.closeAt_ne hk]; exact hT,
        ha⟩ hr⟩

/-- **A computation of the least fixed point is in `Closing`**: it ends whatever the ticks are
answered. -/
theorem closing_of_ewp {T : OpTab} {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ) : Closing T Q ls e ρ :=
  ewp_mono (opTable_mono _) (fun _ _ _ _ h => opTable_closeAt h) (fun _ _ _ h => h) h

/-- A stop of the row is a stop of a segment, the tick owing the least fixed point. -/
theorem divTab_of_opTable {T : OpTab} (hT : T.KeyNA) {Q : List SRec → Val → WProp}
    {W : List SRec → Expr → WProp} {ls : List SRec} {t : Expr} {Φ : List SRec → Expr → WProp}
    {ρ : WRes} (hΦ : ∀ ls e ρ, Φ ls e ρ → owe T Q W ls e ρ) (h : opTable T ls t Φ ρ) :
    divTab T Q W ls t Φ ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK, hTn, ha⟩, hr⟩ := pure_sep_iff.mp hp
    by_cases hk : n = divEff ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      refine Or.inr (performStop_mono _ _ _ _ _ ρ hΦ ⟨K, divEff, 0, v, en,
        pure_sep_mk ⟨rfl, hK, by rw [OpTab.only0_key]; exact hTn, ha⟩ hr⟩)
    · exact Or.inl (Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, by
        rw [OpTab.erase0_ne hk]; exact hTn, ha⟩ hr⟩)
  · obtain ⟨⟨rfl, hK, hTn, ha⟩, hr⟩ := pure_sep_iff.mp hp
    by_cases hk : n = divEff ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      rw [hT en hTn] at ha; cases ha
    · exact Or.inl (Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, by
        rw [OpTab.erase0_ne hk]; exact hTn, ha⟩ hr⟩)

/-- **The least fixed point is in the greatest.**  `[spec §14]` -/
theorem cwp_of_ewp {T : OpTab} (hT : T.KeyNA) {Q : List SRec → Val → WProp} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ) : cwp T Q ls e ρ := by
  refine cwp_coind (W := fun ls e ρ => ewpTS ls e (opTable T) Q ρ) (fun ls e ρ h => ?_) h
  refine (ewp_ind (fun ls e ρ => cwpF T Q (fun ls e ρ => ewpTS ls e (opTable T) Q ρ) ls e ρ ∧
    ewpTS ls e (opTable T) Q ρ) (fun ls e ρ hs => ⟨?_, ?_⟩) h).1
  · refine ewp_fold (divTab_mono _ _ _) (wpG_mono (fun ls' t σ ht => ?_) hs)
    rcases ht with hv | ht
    · exact Or.inl hv
    · exact Or.inr (divTab_mono _ _ _ ls' t _ _ σ (fun _ _ _ h => h.1)
        (divTab_of_opTable hT (fun _ _ _ h => ⟨h.2, closing_of_ewp h.2⟩) ht))
  · exact ewp_fold (opTable_mono _) (ewpStep_mono (opTable_mono _) (fun _ _ _ h => h.2) hs)

/-- **At a table without `Div`'s key, the greatest fixed point is the least.**  `[spec §14]` -/
theorem cwp_none {T : OpTab} (hT : T divEff 0 = none) {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes} :
    cwp T Q ls e ρ ↔ ewpTS ls e (opTable T) Q ρ := by
  constructor
  · intro h
    refine ewp_mono (opTable_mono _) (fun ls t Φ σ hd => ?_) (fun _ _ _ h => h) (cwp_out h)
    rcases hd with hd | hd
    · rw [OpTab.erase0_none hT] at hd; exact hd
    · exact (performStop_none (OpTab.only0_none hT) hd).elim
  · exact cwp_of_ewp (fun en h => by rw [hT] at h; cases h)

/-! ### At `effWp` -/

theorem effWp_step {b : Bool} {T : OpTab} {Q : List SRec → Val → WProp} {e e' : Expr}
    (h : ∀ μ : Heap, Step1N μ e μ e') (ls : List SRec) :
    Entails (effWp b T Q ls e') (effWp b T Q ls e) := by
  cases b
  · exact ewp_step (opTable_mono T) h ls Q
  · exact fun ρ h' => cwp_step h h'

theorem effWp_bind_pure_frame {b : Bool} {T : OpTab} {Q : List SRec → Val → WProp} (K : Kont)
    (e : Expr) (ls : List SRec) (P : List SRec → Val → WProp) (R : List SRec → WProp)
    (hR : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls'))
    (h : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails ((P ls' v) ⋆ R ls') (effWp b T Q ls' (K.plug (.val v)))) :
    Entails ((wpTS ls e P) ⋆ R ls) (effWp b T Q ls (K.plug e)) := by
  cases b
  · exact ewp_bind_pure_frame (opTable_mono T) K e ls P R Q hR h
  · exact cwp_bind_pure_frame K e ls P R hR h

theorem effWp_post {b : Bool} {T : OpTab} {Q Q' : List SRec → Val → WProp}
    (hQ : ∀ ls v ρ, Q ls v ρ → Q' ls v ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : effWp b T Q ls e ρ) : effWp b T Q' ls e ρ := by
  cases b
  · exact ewp_mono (opTable_mono T) (fun _ _ _ _ h => h) hQ h
  · exact cwp_post hQ h

/-- `effWp` at a value. -/
theorem effWp_val {b : Bool} {T : OpTab} (hT : b = true → T.KeyNA)
    {Q : List SRec → Val → WProp} {ls : List SRec} {v : Val} {ρ : WRes} (h : Q ls v ρ) :
    effWp b T Q ls (.val v) ρ := by
  cases b
  · exact ewp_val (opTable_mono T) h
  · exact cwp_of_ewp (hT rfl) (ewp_val (opTable_mono T) h)

/-- A computation of the least fixed point is at `effWp`, `Div` or not. -/
theorem effWp_of_ewp {b : Bool} {T : OpTab} (hT : b = true → T.KeyNA)
    {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (opTable T) Q ρ) : effWp b T Q ls e ρ := by
  cases b
  · exact h
  · exact cwp_of_ewp (hT rfl) h

end BoCa.Fig16.LogRel.Core

end
