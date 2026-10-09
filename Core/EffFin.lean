import Core.EffRules

/-!
# Core — finalisers with effects: cancel rows  `[spec §27]`

A finaliser may raise to live handlers and perform their operations (SPEC §27, decisions D2 and D3
of 2026-10-08).  What it may do during a cancel is recorded in the row entry of the operation that
captures the continuation, the entry's **cancel row** (`CTy.eff`'s `fin`), and checked where the
continuation's cancel is used: `κ`'s cancel branch is at `cancelTy Σ F`, and `[sub]` to the
canceller's row asks that row to hold what `F` holds.

* The cancel-row order `FinLe`, and the row order `RowLe` with it, by first match: `[sub]`.
* `ThenLe F E T`, written `F ⋈ E ≤ T`: the cancel row `T` of a continuation captured below a
  finaliser of row `E`, whose cancel row below the finaliser is `F`.  `F`'s operations, their cancel
  rows `⋈ E` (the finaliser runs in every nested cancel below it); `E`'s operations, with `F`'s
  errors pending in their cancel rows at every depth (`PendLe`: the running finaliser's `cfin` holds
  them).
* The semantics of a cancel row, by induction on it: `finObl` is `cancelObl` of the row's table
  (`finObl_eq`), monotone (`finObl_mono`), closed under plain contexts (`plain_cancel₀`), beside a
  frame holding nothing owned, which the run leaves behind at its first stop (`cancel_frame_drop`,
  `ent_plain`), under a running finaliser's `cfin` (`cfin_cancel`, `cfin_run`), and under a
  finaliser frame (`then_cancel`).
* `[then]`'s unrestricted premise is read at every depth of the cancel rows (`Row.UnrD`): the
  finaliser frame runs in the cancels below it.
* The compatibility of `[sub]`, `[perform]`, `[raise]`, `[let]`, `[then]` and `[handle]`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Step1N performE raiseE opPayload
  cancelVal hndE ubindE ccatchE cfinE hndVal kappa clauseAt errNext capTag kappaAt kappaC
  kappaCBody kappaCell freeE stuckE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Cancel rows as rows -/

/-- A layer's cancel row is smaller than the cancel row it is a layer of. -/
theorem rowOf_fin_lt : ∀ (F : CTy) {o : OpSig}, o ∈ F.rowOf → sizeOf o.fin < sizeOf F
  | .eff n i q A B f C, o, h => by
      simp only [CTy.rowOf, List.mem_cons] at h
      rcases h with rfl | h
      · simp; omega
      · have := rowOf_fin_lt C h; simp; omega
  | .ret _, _, h | .arr _ _, _, h | .amp _ _, _, h | .top, _, h | .all _ _ _, _, h
  | .nu _, _, h => by simp [CTy.rowOf] at h

/-- A cancel row's table is the table of its layers. -/
theorem effTab_rowOf (δ : LSub) : ∀ F : CTy, effTab F δ = Row.tab F.rowOf δ
  | .eff n i q A B f C => by
      funext n' i'
      simp only [effTab, OpTab.ext, CTy.rowOf, effTab_rowOf δ C]
      by_cases h : n' = n ∧ i' = i
      · simp [h, Row.tab, Row.find, List.find?, OpSig.ent, OpSig.abort]
      · rw [if_neg h]
        simp [Row.tab, Row.find, List.find?, h]
  | .ret _ | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => by
      funext n i; simp [effTab, OpTab.empty, CTy.rowOf, Row.tab, Row.find]

/-- **A cancel row's obligation**: none at `⊤`, otherwise the cancel run at its layers' table. -/
theorem finObl_eq (δ : LSub) (F : CTy) :
    finObl F δ = if F.isTop then none else some (cancelObl (Row.tab F.rowOf δ)) := by
  cases F with
  | top => rfl
  | eff n i q A B f C =>
      have h := effTab_rowOf δ (.eff n i q A B f C)
      simp only [effTab] at h
      simp only [finObl, CTy.isTop, Bool.false_eq_true, if_false, h]
  | ret _ | arr _ _ | amp _ _ | all _ _ _ | nu _ =>
      have h : Row.tab ([] : Row) δ = OpTab.empty := by
        funext n i; simp [Row.tab, Row.find, OpTab.empty]
      simp [finObl, CTy.isTop, CTy.rowOf, h]

/-- An operation's entry reads its cancel row at a capturable operation only. -/
theorem OpSig.ent_fin (δ : LSub) (o : OpSig) :
    (o.ent δ).fin = if capB o.q o.B then finObl o.fin δ else none := rfl

/-- A capturable entry: not abortive, not linear. -/
theorem capB_of_ent {δ : LSub} {o : OpSig} (ha : (o.ent δ).abort = false) (hq : (o.ent δ).q ≠ .lin) :
    capB o.q o.B = true := by
  simp only [OpSig.ent, OpSig.abort, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at ha hq
  simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  rcases ha with ha | ha
  · exact ⟨hq, ha⟩
  · exact absurd ha hq

theorem not_lin_of_capB {q : Qual} {B : VTy} (h : capB q B = true) : q ≠ .lin := by
  simp only [capB, Bool.and_eq_true, bne_iff_ne] at h; exact h.1

theorem abort_false_of_capB {o : OpSig} (h : capB o.q o.B = true) : o.abort = false := by
  simp only [capB, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at h
  simp [OpSig.abort, h.2]

/-- The operations are one: name, index, qualifier, argument and answer types. -/
def OpSig.Sig (o o' : OpSig) : Prop :=
  o.n = o'.n ∧ o.i = o'.i ∧ o.q = o'.q ∧ o.A = o'.A ∧ o.B = o'.B

theorem OpSig.Sig.refl (o : OpSig) : o.Sig o := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem OpSig.Sig.trans {o o' o'' : OpSig} (h : o.Sig o') (h' : o'.Sig o'') : o.Sig o'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.1.trans h'.2.2.2.1,
    h.2.2.2.2.trans h'.2.2.2.2⟩

theorem OpSig.Sig.capB_eq {o o' : OpSig} (h : o.Sig o') : capB o.q o.B = capB o'.q o'.B := by
  rw [h.2.2.1, h.2.2.2.2]

theorem OpSig.Sig.abort_eq {o o' : OpSig} (h : o.Sig o') : o.abort = o'.abort := by
  simp only [OpSig.abort, h.2.2.1, h.2.2.2.2]

/-! ### The cancel-row order -/

/-- **The cancel-row order**: `F ≤ ⊤`; otherwise `F` is not `⊤` and each operation it finds is
the one `F′` finds at its key, with, at a capturable operation, a cancel row below `F′`'s.
`[spec §27]` -/
def FinLe (F F' : CTy) : Prop :=
  F'.isTop = true ∨ (F.isTop = false ∧ ∀ n i o, Row.find F.rowOf n i = some o →
    ∃ o', Row.find F'.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → FinLe o.fin o'.fin))
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- `o ≤ o′`: the same operation, its cancel row grown at a capturable operation.
`[spec §27]` -/
def OpSig.LeF (o o' : OpSig) : Prop := o.Sig o' ∧ (capB o.q o.B = true → FinLe o.fin o'.fin)

/-- **`Σ ⊆ Σ′` as rows** (`[sub]`): every operation `Σ` finds is below the one `Σ′` finds at its
key; an entry's cancel row may only grow.  `[spec §19, §27]` -/
def RowLe (S S' : Row) : Prop :=
  ∀ n i o, Row.find S n i = some o → ∃ o', Row.find S' n i = some o' ∧ o.LeF o'

theorem finLe_iff (F F' : CTy) :
    FinLe F F' ↔ F'.isTop = true ∨ (F.isTop = false ∧ RowLe F.rowOf F'.rowOf) := by
  rw [FinLe]; rfl

theorem FinLe.top (F : CTy) : FinLe F .top := by rw [FinLe]; exact Or.inl rfl

theorem FinLe.refl (F : CTy) : FinLe F F := by
  rw [FinLe]
  cases hT : F.isTop
  · refine Or.inr ⟨rfl, fun n i o hf => ⟨o, hf, OpSig.Sig.refl o, fun _ => FinLe.refl o.fin⟩⟩
  · exact Or.inl rfl
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

theorem FinLe.trans (F : CTy) : ∀ {F' F'' : CTy}, FinLe F F' → FinLe F' F'' → FinLe F F'' := by
  intro F' F'' h h'
  rw [FinLe] at h h' ⊢
  rcases h' with h' | ⟨hF', h'⟩
  · exact Or.inl h'
  rcases h with h | ⟨hF, h⟩
  · rw [h] at hF'; cases hF'
  refine Or.inr ⟨hF, fun n i o hf => ?_⟩
  obtain ⟨o', hf', hs, hle⟩ := h n i o hf
  obtain ⟨o'', hf'', hs', hle'⟩ := h' n i o' hf'
  exact ⟨o'', hf'', hs.trans hs', fun hc =>
    FinLe.trans o.fin (hle hc) (hle' (hs.capB_eq ▸ hc))⟩
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

theorem OpSig.LeF.refl (o : OpSig) : o.LeF o := ⟨OpSig.Sig.refl o, fun _ => FinLe.refl o.fin⟩

theorem OpSig.LeF.trans {o o' o'' : OpSig} (h : o.LeF o') (h' : o'.LeF o'') : o.LeF o'' :=
  ⟨h.1.trans h'.1, fun hc => FinLe.trans o.fin (h.2 hc) (h'.2 (h.1.capB_eq ▸ hc))⟩

theorem RowLe.refl (S : Row) : RowLe S S := fun _ _ o hf => ⟨o, hf, OpSig.LeF.refl o⟩

theorem RowLe.trans {S S' S'' : Row} (h : RowLe S S') (h' : RowLe S' S'') : RowLe S S'' := by
  intro n i o hf
  obtain ⟨o', hf', hle⟩ := h n i o hf
  obtain ⟨o'', hf'', hle'⟩ := h' n i o' hf'
  exact ⟨o'', hf'', hle.trans hle'⟩

/-- Inclusion of rows, each operation found as it is, is below in the row order. -/
theorem RowLe.of_find {S S' : Row} (h : ∀ n i o, Row.find S n i = some o → Row.find S' n i = some o) :
    RowLe S S' := fun n i o hf => ⟨o, h n i o hf, OpSig.LeF.refl o⟩

/-- The empty row is below every row. -/
theorem RowLe.nil (S : Row) : RowLe [] S := fun _ _ _ h => by simp [Row.find] at h

/-- An operation a row finds is the same operation in a larger row. -/
theorem RowLe.sig {S S' : Row} (h : RowLe S S') {n i : UInt32} {o : OpSig}
    (hf : Row.find S n i = some o) : ∃ o', Row.find S' n i = some o' ∧ o.Sig o' := by
  obtain ⟨o', hf', hle⟩ := h n i o hf
  exact ⟨o', hf', hle.1⟩

/-! ### The obligation of a cancel row -/

/-- The cancel run of the empty region holds at every entry's cancel obligation. -/
theorem ent_start (δ : LSub) (o : OpSig) (ls : List SRec) :
    cancelOK (o.ent δ) ls .hole PMap.empty := by
  intro P hP
  rw [OpSig.ent_fin] at hP
  split at hP
  · rw [finObl_eq] at hP
    split at hP
    · cases hP
    · cases hP; exact cancelObl_start _ ls
  · cases hP

/-- An entry's table entry at its key. -/
theorem Row.tab_find {S : Row} {δ : LSub} {n i : UInt32} {o : OpSig} (h : Row.find S n i = some o) :
    Row.tab S δ n i = some (o.ent δ) := by
  simp [Row.tab, h]

/-- **A cancel row's obligation grows with the row.**  `[spec §27]` -/
theorem finObl_mono (δ : LSub) (F : CTy) :
    ∀ {F' : CTy}, FinLe F F' → FinLeS (finObl F δ) (finObl F' δ) := by
  intro F' h
  rw [finLe_iff] at h
  rw [finObl_eq δ F, finObl_eq δ F']
  rcases h with h | ⟨hF, h⟩
  · simp only [h, if_true]; exact trivial
  · cases hF' : F'.isTop
    · simp only [hF, Bool.false_eq_true, if_false, FinLeS]
      intro ls e ρ hc
      refine cancelObl_le ?_ hc
      intro n i en hT
      obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
      obtain ⟨o', hf', hs, hle⟩ := h n i o hf
      refine ⟨o'.ent δ, Row.tab_find hf', hs.2.2.1, hs.abort_eq, ?_, ?_, fun ha hq => ?_⟩
      · simp only [OpSig.ent, hs.2.2.2.1]
      · simp only [OpSig.ent, hs.2.2.2.2]
      · have hc := capB_of_ent ha hq
        rw [OpSig.ent_fin, OpSig.ent_fin, if_pos hc, if_pos (hs.capB_eq ▸ hc)]
        exact finObl_mono δ o.fin (hle hc)
    · simp only [if_true]; exact trivial
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem hf).1

/-- The entries of one operation, not capturable, at two cancel rows are one entry. -/
theorem OpSig.ent_eq_of_sig (δ : LSub) {o o' : OpSig} (h : o.Sig o') (hc : capB o.q o.B = false) :
    o.ent δ = o'.ent δ := by
  have hc' : capB o'.q o'.B = false := h.capB_eq ▸ hc
  simp only [OpSig.ent, OpSig.abort, hc', h.2.2.1, h.2.2.2.1, h.2.2.2.2, Bool.false_eq_true,
    if_false]

/-- An operation's entry grows with the operation. -/
theorem OpSig.ent_le (δ : LSub) {o o' : OpSig} (h : o.LeF o') : (o.ent δ).Le (o'.ent δ) := by
  refine ⟨h.1.2.2.1, h.1.abort_eq, ?_, ?_, fun ha hq => ?_⟩
  · simp only [OpSig.ent, h.1.2.2.2.1]
  · simp only [OpSig.ent, h.1.2.2.2.2]
  · have hc := capB_of_ent ha hq
    rw [OpSig.ent_fin, OpSig.ent_fin, if_pos hc, if_pos (h.1.capB_eq ▸ hc)]
    exact finObl_mono δ o.fin (h.2 hc)

/-- **A row's table grows with the row** (`[sub]`).  `[spec §19, §27]` -/
theorem Row.tab_le {S S' : Row} (δ : LSub) (h : RowLe S S') : (Row.tab S δ).Le (Row.tab S' δ) := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨o', hf', hle⟩ := h n i o hf
  exact ⟨o'.ent δ, Row.tab_find hf', OpSig.ent_le δ hle⟩

theorem finUnr_of_mem : ∀ {G : CTy} {o : OpSig}, o ∈ G.rowOf →
    (o.q = .unr ∨ (capB o.q o.B = true ∧ o.fin.FinUnr)) → G.FinUnr
  | .eff n i q A B f C, o, ho, h => by
      simp only [CTy.rowOf, List.mem_cons] at ho
      rcases ho with rfl | ho
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (finUnr_of_mem ho h))
  | .ret _, _, ho, _ | .arr _ _, _, ho, _ | .amp _ _, _, ho, _ | .top, _, ho, _
  | .all _ _ _, _, ho, _ | .nu _, _, ho, _ => by simp [CTy.rowOf] at ho

/-- A capturable entry of a row's table, its obligation the cancel run at its cancel row's table. -/
theorem ent_fin_some {δ : LSub} {o : OpSig} {P : List SRec → Expr → WProp}
    (h : (o.ent δ).fin = some P) :
    capB o.q o.B = true ∧ o.fin.isTop = false ∧ P = cancelObl (Row.tab o.fin.rowOf δ) := by
  rw [OpSig.ent_fin] at h
  split at h
  · rename_i hc
    rw [finObl_eq] at h
    split at h
    · cases h
    · rename_i hT
      cases h
      exact ⟨hc, by simpa using hT, rfl⟩
  · cases h

/-- **A cancel run under a plain context**, at a cancel row's table, beside no frame:
`cancel_frame`, the nested cancels carried through the context by the induction on the row.
`[spec §27]` -/
theorem plain_cancel₀ (δ : LSub) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : K.Catches 0 = false) (G : CTy) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cancelObl (Row.tab G.rowOf δ) ls e ρ →
      cancelObl (Row.tab G.rowOf δ) ls (K.plug e) ρ := by
  intro ls e ρ h
  refine cancel_frame K hH hC (OpTab.Le.refl _) noOwn_empty (fun _ _ _ _ _ _ => rfl) ?_ h
    (ResU.comp_empty_right ρ)
  intro n i en hT ha hq ls₁ K₁ ρ₁ ρ₁' hcan hc₁ P hP
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨hcap, -, rfl⟩ := ent_fin_some hP
  obtain rfl := eq_of_compS_empty_left (ResU.CompS.comm hc₁)
  show cancelObl _ ls₁ ((K.comp K₁).dead.plug _) _
  rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
  exact plain_cancel₀ δ K hH hC o.fin (hcan _ hP)
termination_by sizeOf G
decreasing_by exact rowOf_fin_lt G (Row.find_mem hf).1

/-- A row's table carries its cancel obligations through a plain context with no frame. -/
theorem Row.tab_plainCancel (S : Row) (δ : LSub) : (Row.tab S δ).PlainCancel := by
  intro n i en hT _ _ K hH hC ls K₁ ρ hcan P hP
  obtain ⟨o, -, rfl⟩ := Row.tab_some hT
  obtain ⟨-, -, rfl⟩ := ent_fin_some hP
  show cancelObl _ ls ((K.comp K₁).dead.plug _) ρ
  rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
  exact plain_cancel₀ δ K hH hC o.fin (hcan _ hP)

/-- **A frame left behind by a cancel run under a plain context**: the frame `σ`, holding nothing
owned, is garbage at the run's first stop (`wpG_garbage`), and the run goes on under `K` beside no
frame, the nested cancels carried through `K` by `T.PlainCancel`.  The context's own code never
runs in a cancel, so nothing of the frame is needed after the first stop.  `[spec §27]` -/
theorem cancel_frame_drop {T T' : OpTab} (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : K.Catches 0 = false) (hT : T.Le T') (hPC : T.PlainCancel) {σ : WRes} (hσ : NoOwn σ)
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (cancelTab T) (fun _ _ _ => False) ρ) {ρ' : WRes} (hc : ResU.CompS ρ σ ρ') :
    ewpTS ls (K.plug e) (cancelTab T') (fun _ _ _ => False) ρ' := by
  have h₀ : ∀ {ls₀ : List SRec} {e₀ : Expr} {ρ₀ : WRes},
      ewpTS ls₀ e₀ (cancelTab T) (fun _ _ _ => False) ρ₀ →
      ewpTS ls₀ (K.plug e₀) (cancelTab T') (fun _ _ _ => False) ρ₀ := fun h' =>
    cancel_frame K hH hC hT noOwn_empty (fun _ _ _ _ _ _ => rfl)
      (fun n i en hT₁ ha hq ls₁ K₁ ρ₁ ρ₁' hcan hc₁ => by
        obtain rfl := eq_of_compS_empty_left (ResU.CompS.comm hc₁)
        exact hPC n i en hT₁ ha hq K hH hC ls₁ K₁ _ hcan) h' (ResU.comp_empty_right _)
  refine ewp_fold (cancelTab_mono T') (wpG_bind K e ls _ ρ' (wpG_garbage ?_))
  have h₁ := wpG_frame (e := e) (fun _ τ => τ = σ) (fun _ _ _ h => h) ρ'
    ⟨ρ, σ, hc, ewp_unfold (cancelTab_mono T) h, rfl⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hp, rfl⟩ := ht
  exact ⟨τ₁, τ₂, hcτ, hσ,
    ewp_unfold (cancelTab_mono T') (h₀ (ewp_fold (cancelTab_mono T) (wpG_here _ _ _ τ₁ hp)))⟩

/-- **An entry's cancel obligation under a plain context, beside a frame holding nothing owned**:
the frame is left behind (`cancel_frame_drop`).  `[spec §27]` -/
theorem ent_plain (δ : LSub) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : K.Catches 0 = false) {σ : WRes} (hσ : NoOwn σ) (o : OpSig) {ls : List SRec} {K₁ : Kont}
    {ρ ρ' : WRes} (hcan : cancelOK (o.ent δ) ls K₁ ρ) (hc : ResU.CompS ρ σ ρ') :
    cancelOK (o.ent δ) ls (K.comp K₁) ρ' := by
  intro P hP
  obtain ⟨-, -, rfl⟩ := ent_fin_some hP
  show cancelObl _ ls ((K.comp K₁).dead.plug _) ρ'
  rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
  exact cancel_frame_drop K hH hC (OpTab.Le.refl _) (Row.tab_plainCancel o.fin.rowOf δ) hσ
    (hcan _ hP) hc

/-! ### Finalisers in a cancel: `pend` and `⋈` -/

/-- **`pend P G ≤ G′`**: each operation `G` finds is the one `G′` finds at its key, a capturable
one's cancel row gaining, at every depth, the errors `P` may keep (the abortive operations it
finds); and those errors are `G′`'s.  A running finaliser's `cfin` holds such an error while a
nested cancel of its continuation runs.  `pend P ⊤ = ⊤`.  `[spec §27]` -/
def PendLe (P : Row) (G G' : CTy) : Prop :=
  G'.isTop = true ∨ (G.isTop = false ∧
    (∀ n i o, Row.find G.rowOf n i = some o → ∃ o', Row.find G'.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → PendLe P o.fin o'.fin)) ∧
    (∀ n i o, Row.find P n i = some o → o.abort = true →
      ∃ o', Row.find G'.rowOf n i = some o' ∧ o.Sig o'))
termination_by sizeOf G
decreasing_by exact rowOf_fin_lt G (Row.find_mem (by assumption)).1

/-- **`F ⋈ E ≤ T`**: `T` is above the cancel row of a continuation captured below a finaliser of
the row `E`, whose cancel row below the finaliser is `F`.  Each operation `F` finds is the one `T`
finds at its key, a capturable one's cancel row `⋈ E` (a nested cancel below the finaliser fires it
too); each operation `E` finds is `T`'s, a capturable one's cancel row with `F`'s errors pending
(`PendLe`).  `⊤ ⋈ E = ⊤`.  `[spec §27]` -/
def ThenLe (F : CTy) (E : Row) (T : CTy) : Prop :=
  T.isTop = true ∨ (F.isTop = false ∧
    (∀ n i o, Row.find F.rowOf n i = some o → ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → ThenLe o.fin E o'.fin)) ∧
    (∀ n i o, Row.find E n i = some o → ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → PendLe F.rowOf o.fin o'.fin)))
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- With no finaliser effects, `F ⋈ ∅ ≤ F`: `[then]` at option A (SPEC §24) is an instance. -/
theorem ThenLe.nil (F : CTy) : ThenLe F [] F := by
  rw [ThenLe]
  cases hT : F.isTop
  · exact Or.inr ⟨rfl, fun n i o hf => ⟨o, hf, OpSig.Sig.refl o, fun _ => ThenLe.nil o.fin⟩,
      fun n i o hf => by simp [Row.find] at hf⟩
  · exact Or.inl rfl
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- The errors a cancel row may keep, at every depth, have persistent arguments.  `[spec §27]` -/
def CTy.FinPers : CTy → Prop
  | .eff _ _ q A B f C => ((B.isZero && q != .lin) = true → A.Persistent) ∧
      (capB q B = true → f.FinPers) ∧ C.FinPers
  | _ => True

/-- The errors that may be pending at a finaliser below which the row `Σ` runs have persistent
arguments: `Σ`'s abortive operations (a pending `raise`), and those of its capturable operations'
cancel rows at every depth (a cancel's kept error).  `[spec §27]` -/
def Row.PendPers (S : Row) : Prop :=
  ∀ o ∈ S, (o.abort = true → o.A.Persistent) ∧ (capB o.q o.B = true → o.fin.FinPers)

theorem finPers_of_mem : ∀ {F : CTy} {o : OpSig}, F.FinPers → o ∈ F.rowOf →
    (o.abort = true → o.A.Persistent) ∧ (capB o.q o.B = true → o.fin.FinPers)
  | .eff n i q A B f C, o, h, ho => by
      simp only [CTy.rowOf, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨h.1, h.2.1⟩
      · exact finPers_of_mem h.2.2 ho
  | .ret _, _, _, ho | .arr _ _, _, _, ho | .amp _ _, _, _, ho | .top, _, _, ho
  | .all _ _ _, _, _, ho | .nu _, _, _, ho => by simp [CTy.rowOf] at ho

/-- A kept error of a cancel row whose errors are persistent holds nothing. -/
theorem errOk_empty_of_pers {δ : LSub} {F : CTy} (hF : F.FinPers) {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOk (Row.tab F.rowOf δ) ls err ρ → ρ = PMap.empty
  | none, _, h => h.1
  | some _, _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨-, hT, ha⟩, hA, -⟩ := pure_sep_iff.mp h
      obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
      exact vP_empty_of_persistent ((finPers_of_mem hF (Row.find_mem hf).1).1 ha) hA

/-- Errors move along a first-match inclusion of abortive operations. -/
theorem errOk_of_sub {δ : LSub} {P P' : Row}
    (h : ∀ n i o, Row.find P n i = some o → o.abort = true →
      ∃ o', Row.find P' n i = some o' ∧ o.Sig o') {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOk (Row.tab P δ) ls err ρ → errOk (Row.tab P' δ) ls err ρ
  | none, _, h => h
  | some _, _, ⟨m, j, w, en, h'⟩ => by
      obtain ⟨⟨h₁, hT, ha⟩, h₅⟩ := pure_sep_iff.mp h'
      obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
      obtain ⟨o', hf', hs⟩ := h m j o hf ha
      refine ⟨m, j, w, o'.ent δ, pure_sep_mk ⟨h₁, Row.tab_find hf', ?_⟩ ?_⟩
      · show o'.abort = true; rw [← hs.abort_eq]; exact ha
      · simpa only [OpSig.ent, hs.2.2.2.1] using h₅

/-- A first-match inclusion with the same operations is one of abortive operations. -/
theorem sub_of_sig {S S' : Row}
    (h : ∀ n i o, Row.find S n i = some o → ∃ o', Row.find S' n i = some o' ∧ o.Sig o' ∧ True) :
    ∀ n i o, Row.find S n i = some o → o.abort = true →
      ∃ o', Row.find S' n i = some o' ∧ o.Sig o' := by
  intro n i o hf _
  obtain ⟨o', hf', hs, -⟩ := h n i o hf
  exact ⟨o', hf', hs⟩

theorem finUnr_of_find {G : CTy} {n i : UInt32} {o : OpSig} (hf : Row.find G.rowOf n i = some o)
    (h : o.q = .unr ∨ (capB o.q o.B = true ∧ o.fin.FinUnr)) : G.FinUnr :=
  finUnr_of_mem (Row.find_mem hf).1 h

/-- **A nested cancel past a running finaliser's `cfin`** (`[cfin-cancel]`): a cancel run at the
cancel row `G`, under `cfin err` holding an error of `P`, is one at any `G′ ≥ pend P G` that is not
`⊤`.  At its end the kept error, the earlier, wins; its operations' nested cancels pass the same
`cfin`.  The error holds nothing where `G` may stop at an unrestricted operation.  `[spec §27]` -/
theorem cfin_cancel (δ : LSub) (P : Row) (err : Option Val) (G : CTy) :
    ∀ {G' : CTy}, PendLe P G G' → G'.isTop = false →
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cancelObl (Row.tab G.rowOf δ) ls e ρ →
      ∀ {σe ρ' : WRes}, errOk (Row.tab P δ) ls err σe → (G.FinUnr → σe = PMap.empty) →
        ResU.CompS ρ σe ρ' →
        cancelObl (Row.tab G'.rowOf δ) ls ((cfinK (cancelVal err)).plug e) ρ' := by
  intro G' hle hG'
  rw [PendLe, hG'] at hle
  obtain ⟨-, hGG, hPG⟩ := hle.resolve_left (by simp)
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {σe ρ' : WRes}, errOk (Row.tab P δ) ls err σe →
    (G.FinUnr → σe = PMap.empty) → ResU.CompS ρ σe ρ' →
    cancelObl (Row.tab G'.rowOf δ) ls ((cfinK (cancelVal err)).plug e) ρ') ?_ h
  intro ls e ρ hs σe ρ' he hu hc
  refine ewp_fold (cancelTab_mono _) (wpG_bind (cfinK (cancelVal err)) e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) (fun ls τ => τ = σe ∧ errOk (Row.tab P δ) ls err τ)
    (fun ls' hs' τ h => ⟨h.1, errOk_local (Row.tab_local P δ) (ext_of_same hs' τ) h.2⟩) ρ'
    ⟨ρ, σe, hc, hs, rfl, he⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hp, rfl, he'⟩ := ht
  rcases hp with ⟨_, _, hv⟩ | hp
  · exact hv.elim
  rcases hp with ⟨K₀, err', hs'⟩ | ⟨K₁, n, i, v, en, hp⟩
  · -- the nested cancel's end passes the `cfin`: the earlier error wins
    obtain ⟨⟨rfl, hK₀⟩, τa, τb, hcab, he₀, hnb⟩ := pure_sep_iff.mp hs'
    refine wpG_head (fun μ => Head.cfcancel μ err err' K₀ hK₀) rfl _ _ τ ?_
    refine wpG_here _ _ _ τ (Or.inr (Or.inl ⟨.hole, err.or err', pure_sep_mk ⟨rfl, rfl⟩ ?_⟩))
    have hnτa : NoOwn τa := by
      cases err' with
      | none => rw [he₀.1]; exact noOwn_empty
      | some _ =>
          obtain ⟨_, _, _, _, h⟩ := he₀
          exact (pure_sep_iff.mp h).2.2
    cases err with
    | some E =>
        exact ⟨τ₂, τ₁, ResU.CompS.comm hcτ, errOk_of_sub hPG he', noOwn_compS hcab hnτa hnb⟩
    | none =>
        have hτ₂ : τ₂ = PMap.empty := he'.1
        subst hτ₂
        rw [eq_of_compS_empty_left (ResU.CompS.comm hcτ)]
        exact ⟨τa, τb, hcab, errOk_of_sub (sub_of_sig fun n i o hf => by
          obtain ⟨o', hf', hs, -⟩ := hGG n i o hf; exact ⟨o', hf', hs, trivial⟩) he₀, hnb⟩
  · -- an operation of the nested cancel's finaliser: the `cfin` joins its continuation
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    obtain ⟨o', hf', hs, hfin⟩ := hGG n i o hf
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    refine wpG_here _ _ _ τ (Or.inr (Or.inr ⟨(cfinK (cancelVal err)).comp K₁, n, i, v, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, Row.tab_find hf',
        (show o'.abort = false by rw [← hs.abort_eq]; exact ha)⟩
        ⟨ρa, ρk', hcσ', by simpa only [OpSig.ent, hs.2.2.2.1] using hA, ?_⟩⟩))
    · rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    refine ⟨fun hq => ?_, fun ls'' hext => ⟨fun w τ₃ τ₄ hB hcτ' => ?_, fun hq => ?_⟩⟩
    · have hq' : o.q = .unr := by simpa only [OpSig.ent, hs.2.2.1] using hq
      rw [hu' hq', hu (finUnr_of_find hf (Or.inl hq'))] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      rw [Kont.plug_comp]
      have hB' : (o.ent δ).PB ls'' w τ₃ := by simpa only [OpSig.ent, hs.2.2.2.2] using hB
      exact (hcont ls'' (hext.left hk')).1 w τ₃ z hB' hz
        (errOk_local (Row.tab_local P δ) (hext.right hk') he') hu hcz
    · intro Q hQ
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hq₀ : (o.ent δ).q ≠ .lin := not_lin_of_capB hcap
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' (hext.left hk')).2 hq₀ (cancelObl (Row.tab o.fin.rowOf δ)) (by
        rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancel δ P err o.fin hfin' hnT hcan
        (errOk_local (Row.tab_local P δ) (hext.right hk') he')
        (fun hu₁ => hu (finUnr_of_find hf (Or.inr ⟨hcap, hu₁⟩))) hk'
termination_by sizeOf G
decreasing_by exact rowOf_fin_lt G (Row.find_mem hf).1

theorem unr_of_find {E : Row} {n i : UInt32} {o : OpSig} (hf : Row.find E n i = some o)
    (h : o.q = .unr ∨ (capB o.q o.B = true ∧ o.fin.FinUnr)) : E.UnrD :=
  ⟨o, (Row.find_mem hf).1, h⟩

/-- **A finaliser running under a cancel's `cfin`**: `D` at the row `E`, the cancel keeping an error
of `P`, is a cancel run at any `T` that has `E`'s operations, their cancel rows with
`P`'s errors pending, and `P`'s errors.  `D`'s answer gives `[cfin-ret]`; its raise is kept unless an
error already is (`[cfin-raise]`, the first wins); its operation passes the dead region to a live
handler, and a cancel of that continuation passes the `cfin` (`cfin_cancel`).  The error holds
nothing where `E` may stop at an unrestricted operation.  `[spec §27]` -/
theorem cfin_run (δ : LSub) (E P : Row) (err : Option Val) {T : CTy}
    (hE : ∀ n i o, Row.find E n i = some o → ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → PendLe P o.fin o'.fin))
    (hP : ∀ n i o, Row.find P n i = some o → o.abort = true →
      ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o')
    (hNZ : ∀ n i o, Row.find E n i = some o → o.n ≠ 0)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → NoOwn ρ) :
    ∀ {ls : List SRec} {d : Expr} {ρ : WRes}, ewpTS ls d (opTable (Row.tab E δ)) Qd ρ →
      ∀ {σe ρ' : WRes}, errOk (Row.tab P δ) ls err σe → (E.UnrD → σe = PMap.empty) →
        ResU.CompS ρ σe ρ' → cancelObl (Row.tab T.rowOf δ) ls (cfinE (cancelVal err) d) ρ' := by
  intro ls d ρ h
  refine ewp_ind (fun ls d ρ => ∀ {σe ρ' : WRes}, errOk (Row.tab P δ) ls err σe →
    (E.UnrD → σe = PMap.empty) → ResU.CompS ρ σe ρ' →
    cancelObl (Row.tab T.rowOf δ) ls (cfinE (cancelVal err) d) ρ') ?_ h
  intro ls d ρ hs σe ρ' he hu hc
  refine ewp_fold (cancelTab_mono _) (wpG_bind (cfinK (cancelVal err)) d ls _ ρ' ?_)
  have h₁ := wpG_frame (e := d) (fun ls τ => τ = σe ∧ errOk (Row.tab P δ) ls err τ)
    (fun ls' hs' τ h => ⟨h.1, errOk_local (Row.tab_local P δ) (ext_of_same hs' τ) h.2⟩) ρ'
    ⟨ρ, σe, hc, hs, rfl, he⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hp, rfl, he'⟩ := ht
  rcases hp with ⟨w, rfl, hw⟩ | hp
  · -- the finaliser finished: the cancel goes on with its error
    refine wpG_head (fun μ => Head.cfret μ err w) rfl _ _ τ ?_
    exact wpG_here _ _ _ τ (Or.inr (Or.inl ⟨.hole, err, pure_sep_mk ⟨rfl, rfl⟩
      ⟨τ₂, τ₁, ResU.CompS.comm hcτ, errOk_of_sub hP he', hQd _ _ _ hw⟩⟩))
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, m, j, w, en, hp⟩
  · -- an operation of the finaliser passes the dead region; the `cfin` joins its continuation
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn
    obtain ⟨o', hf', hs, hfin⟩ := hE n i o hf
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    refine wpG_here _ _ _ τ (Or.inr (Or.inr ⟨(cfinK (cancelVal err)).comp K₁, n, i, v, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, Row.tab_find hf',
        (show o'.abort = false by rw [← hs.abort_eq]; exact ha)⟩
        ⟨ρa, ρk', hcσ', by simpa only [OpSig.ent, hs.2.2.2.1] using hA, ?_⟩⟩))
    · rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    refine ⟨fun hq => ?_, fun ls'' hext => ⟨fun w τ₃ τ₄ hB hcτ' => ?_, fun hq => ?_⟩⟩
    · have hq' : o.q = .unr := by simpa only [OpSig.ent, hs.2.2.1] using hq
      rw [hu' hq', hu (unr_of_find hf (Or.inl hq'))] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      rw [Kont.plug_comp]
      have hB' : (o.ent δ).PB ls'' w τ₃ := by simpa only [OpSig.ent, hs.2.2.2.2] using hB
      exact (hcont ls'' (hext.left hk')).1 w τ₃ z hB' hz
        (errOk_local (Row.tab_local P δ) (hext.right hk') he') hu hcz
    · intro Q hQ
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' (hext.left hk')).2 (not_lin_of_capB hcap)
        (cancelObl (Row.tab o.fin.rowOf δ)) (by rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancel δ P err o.fin hfin' hnT hcan
        (errOk_local (Row.tab_local P δ) (hext.right hk') he')
        (fun hu₁ => hu (unr_of_find hf (Or.inr ⟨hcap, hu₁⟩))) hk'
  · -- a raise of the finaliser: the first error is kept, and the cancel goes on
    obtain ⟨⟨rfl, hK₁, hTm, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTm
    have hm : m ≠ 0 := by rw [← (Row.find_mem hf).2.1]; exact hNZ m j o hf
    refine wpG_head (fun μ => Head.cferr μ err m j w K₁ hm hK₁) rfl _ _ τ ?_
    refine wpG_here _ _ _ τ (Or.inr (Or.inl ⟨.hole, errNext err m j w, pure_sep_mk ⟨rfl, rfl⟩ ?_⟩))
    have hnτ₁ : NoOwn τ₁ := noOwn_compS hcan hnA hnn
    cases err with
    | some E' => exact ⟨τ₂, τ₁, ResU.CompS.comm hcτ, errOk_of_sub hP he', hnτ₁⟩
    | none =>
        have hτ₂ : τ₂ = PMap.empty := he'.1
        subst hτ₂
        rw [eq_of_compS_empty_left (ResU.CompS.comm hcτ)]
        obtain ⟨o', hf', hs, -⟩ := hE m j o hf
        refine ⟨ρa, ρn, hcan, ⟨m, j, w, o'.ent δ, pure_sep_mk ⟨rfl, Row.tab_find hf', ?_⟩ ?_⟩, hnn⟩
        · show o'.abort = true; rw [← hs.abort_eq]; exact ha
        · exact ⟨by simpa only [OpSig.ent, hs.2.2.2.1] using hPA, hnA⟩

/-- **A cancel run through a finaliser frame** (`ubind (N, D) [·]`), by induction on the cancel row
`F` below it: at the cancel's end `[finalise-cancel]` runs `D` under `cfin` (`cfin_run`), with `F`'s
errors pending; at an operation below `D`, the frame joins its continuation, whose own cancel passes
the frame and fires `D` too.  So the run is at any `T ≥ F ⋈ E` that is not `⊤`.  The frame `Fr`,
which `D` consumes, holds nothing where `T` may stop at an unrestricted operation; `F`'s errors hold
nothing where `E` may.  `[spec §27]` -/
theorem then_cancel (δ : LSub) (E : Row) (hNZ : ∀ n i o, Row.find E n i = some o → o.n ≠ 0)
    (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls)
      (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable (Row.tab E δ)) Qd))
    (F : CTy) : ∀ {T : CTy}, ThenLe F E T → T.isTop = false →
      (T.FinUnr → ∀ ls σ, Fr ls σ → σ = PMap.empty) → (E.UnrD → F.FinPers) →
      ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cancelObl (Row.tab F.rowOf δ) ls e ρ →
        ∀ {σ ρ' : WRes}, Fr ls σ → ResU.CompS ρ σ ρ' →
          cancelObl (Row.tab T.rowOf δ) ls ((ubindK Nv Dv).plug e) ρ' := by
  intro T hle hT hunr hpers
  rw [ThenLe, hT] at hle
  obtain ⟨-, hFT, hET⟩ := hle.resolve_left (by simp)
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {σ ρ' : WRes}, Fr ls σ → ResU.CompS ρ σ ρ' →
    cancelObl (Row.tab T.rowOf δ) ls ((ubindK Nv Dv).plug e) ρ') ?_ h
  intro ls e ρ hs σ ρ' hF hc
  refine ewp_fold (cancelTab_mono _) (wpG_bind (ubindK Nv Dv) e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ' ⟨ρ, σ, hc, hs, hF⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hp, hF'⟩ := ht
  rcases hp with ⟨_, _, hv⟩ | hp
  · exact hv.elim
  rcases hp with ⟨K₀, err, hs'⟩ | ⟨K₁, n, i, v, en, hp⟩
  · -- the cancel reaches the frame: `D` runs under `cfin`
    obtain ⟨⟨rfl, hK₀⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    refine wpG_head (fun μ => Head.ufinC μ Nv Dv err K₀ hK₀) rfl _ _ τ (ewp_unfold
      (cancelTab_mono _) ?_)
    obtain ⟨z, hz, hcz⟩ := compS_exch hcab hcτ
    refine ewp_absorb (cancelTab_mono _) ?_ hnb hcz
    refine cfin_run δ E F.rowOf err hET (fun n i o hf _ => by
        obtain ⟨o', hf', hs, -⟩ := hFT n i o hf; exact ⟨o', hf', hs⟩) hNZ hQd
      (hD ls' τ₂ hF') he (fun hu => errOk_empty_of_pers (hpers hu) he) (ResU.CompS.comm hz)
  · -- an operation below the frame: the frame joins its continuation
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn
    obtain ⟨o', hf', hs, hfin⟩ := hFT n i o hf
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    refine wpG_here _ _ _ τ (Or.inr (Or.inr ⟨(ubindK Nv Dv).comp K₁, n, i, v, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, Row.tab_find hf',
        (show o'.abort = false by rw [← hs.abort_eq]; exact ha)⟩
        ⟨ρa, ρk', hcσ', by simpa only [OpSig.ent, hs.2.2.2.1] using hA, ?_⟩⟩))
    · rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    refine ⟨fun hq => ?_, fun ls'' hext => ⟨fun w τ₃ τ₄ hB hcτ' => ?_, fun hq => ?_⟩⟩
    · have hq' : o'.q = .unr := by simpa only [OpSig.ent] using hq
      have hq₀ : o.q = .unr := by rw [hs.2.2.1]; exact hq'
      rw [hu' hq₀, hunr (finUnr_of_find hf' (Or.inl hq')) ls' τ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      rw [Kont.plug_comp]
      have hB' : (o.ent δ).PB ls'' w τ₃ := by simpa only [OpSig.ent, hs.2.2.2.2] using hB
      exact (hcont ls'' (hext.left hk')).1 w τ₃ z hB' hz (hFe ls' ls'' τ₂ (hext.right hk') hF') hcz
    · intro Q hQ
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' (hext.left hk')).2 (not_lin_of_capB hcap)
        (cancelObl (Row.tab o.fin.rowOf δ)) (by rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancel δ E hNZ Nv Dv Fr hFs hFe hQd hD o.fin hfin' hnT
        (fun hu₁ => hunr (finUnr_of_find hf' (Or.inr ⟨hcap', hu₁⟩)))
        (fun hu₁ => (finPers_of_mem (hpers hu₁) (Row.find_mem hf).1).2 hcap) hcan
        (hFe ls' ls'' τ₂ (hext.right hk') hF') hk'
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem hf).1

/-- The empty row's table is the empty table. -/
theorem Row.tab_nil (δ : LSub) : Row.tab ([] : Row) δ = OpTab.empty := by
  funext n i; simp [Row.tab, Row.find, OpTab.empty]

/-- **A cancel run at the empty cancel row through a pure finaliser's frame**: `then_cancel` at
`F = T = F 1` and `E = ∅`. -/
theorem cancel_then_nil (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls)
      (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable OpTab.empty) Qd))
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cancelObl OpTab.empty ls e ρ) {σ ρ' : WRes}
    (hσ : Fr ls σ) (hc : ResU.CompS ρ σ ρ') :
    cancelObl OpTab.empty ls ((ubindK Nv Dv).plug e) ρ' := by
  have hT := Row.tab_nil LSub.empty
  have h' : cancelObl (Row.tab (CTy.ret .unit).rowOf LSub.empty) ls e ρ := by
    simp only [CTy.rowOf, hT]; exact h
  have := then_cancel LSub.empty [] (fun _ _ _ h => by simp [Row.find] at h) Nv Dv Fr hFs hFe hQd
    (fun ls => by rw [hT]; exact hD ls) (.ret .unit) (ThenLe.nil _) rfl (fun h => h.elim)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) h' hσ hc
  simpa only [CTy.rowOf, hT] using this

/-! ### The finaliser frame -/

/-- The frame `[·]; raise p` of a finaliser running under ordinary unwinding. -/
abbrev seqRaiseK (p : Val) : Kont := .seq .hole (raiseE (.val p))

theorem seqRaiseK_hasHnd (p : Val) (n : UInt32) : (seqRaiseK p).HasHnd n = false := rfl

theorem seqRaiseK_catches (p : Val) (n : UInt32) : (seqRaiseK p).Catches n = false := rfl

/-- **A finaliser under ordinary unwinding**: `D (); raise p`, `D` at a row `E ≤ Σ`, the pending
raise's argument holding nothing where `E` may stop at an unrestricted operation.  `D`'s answer lets
the raise go on; `D`'s raise supersedes it; `D`'s operation keeps it in its continuation, whose
cancel passes it as a plain frame (`ent_plain`).  `[spec §19, §27]` -/
theorem seq_raise_run (δ : LSub) (S E : Row) (hES : RowLe E S) {n i : UInt32} {v : Val}
    {en : OpEnt} (hTn : Row.tab S δ n i = some en) (ha : en.abort = true)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    {Q : List SRec → Val → WProp} :
    ∀ {ls : List SRec} {d : Expr} {ρ : WRes}, ewpTS ls d (opTable (Row.tab E δ)) Qd ρ →
      ∀ {σp ρ' : WRes}, (en.PA ls v σp ∧ NoOwn σp) → (E.UnrD → σp = PMap.empty) →
        ResU.CompS ρ σp ρ' →
        ewpTS ls (.seq d (raiseE (.val (opPayload n i v)))) (opTable (Row.tab S δ)) Q ρ' := by
  intro ls d ρ h
  refine ewp_ind (fun ls d ρ => ∀ {σp ρ' : WRes}, (en.PA ls v σp ∧ NoOwn σp) →
    (E.UnrD → σp = PMap.empty) → ResU.CompS ρ σp ρ' →
    ewpTS ls (.seq d (raiseE (.val (opPayload n i v)))) (opTable (Row.tab S δ)) Q ρ') ?_ h
  intro ls d ρ hs σp ρ' hp hu hc
  refine ewp_fold (opTable_mono _) (wpG_bind (seqRaiseK (opPayload n i v)) d ls _ ρ' ?_)
  have h₁ := wpG_frame (e := d) (fun ls τ => τ = σp ∧ en.PA ls v τ ∧ NoOwn τ)
    (fun ls' hs' τ h => ⟨h.1, (Row.tab_local S δ n i en hTn _ ls' v τ (ext_of_same hs' τ)).1 h.2.1,
      h.2.2⟩) ρ' ⟨ρ, σp, hc, hs, rfl, hp⟩
  refine wpG_mono (fun ls' t τ ht => ?_) h₁
  obtain ⟨τ₁, τ₂, hcτ, hq, rfl, hp'⟩ := ht
  rcases hq with ⟨w, rfl, hw⟩ | hq
  · -- the finaliser finished: the raise goes on
    obtain ⟨rfl, hnw⟩ := hQd _ _ _ hw
    refine wpG_head (fun μ => Head.seq μ _) rfl _ _ τ ?_
    exact wpG_here _ _ _ τ (Or.inr (Or.inr ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hTn, ha⟩
      ⟨τ₂, τ₁, ResU.CompS.comm hcτ, hp', hnw⟩⟩))
  refine wpG_here _ _ _ τ (Or.inr ?_)
  rcases hq with ⟨K₁, m, j, w, en₁, hq⟩ | ⟨K₁, m, j, w, en₁, hq⟩
  · -- an operation of the finaliser: the pending raise joins its continuation
    obtain ⟨⟨rfl, hK₁, hTm, ha₁⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hq
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTm
    obtain ⟨o', hf', hle⟩ := hES m j o hf
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    refine Or.inl ⟨(seqRaiseK (opPayload n i v)).comp K₁, m, j, w, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, Row.tab_find hf',
        (show o'.abort = false by rw [← hle.1.abort_eq]; exact ha₁)⟩
        ⟨ρa, ρk', hcσ', by simpa only [OpSig.ent, hle.1.2.2.2.1] using hA, ?_⟩⟩
    · rw [hasHnd_comp, hK₁]; rfl
    refine contShare_le (OpSig.ent_le δ hle) ha₁ ⟨fun hq => ?_, fun ls'' hext =>
      ⟨fun w' τ₃ τ₄ hB hcτ' => ?_, fun hq => ?_⟩⟩
    · rw [hu' hq, hu (unr_of_find hf (Or.inl hq))] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      rw [Kont.plug_comp]
      exact (hcont ls'' (hext.left hk')).1 w' τ₃ z hB hz
        ⟨(Row.tab_local S δ n i en hTn _ ls'' v τ₂ (hext.right hk')).1 hp'.1, hp'.2⟩ hu hcz
    · exact ent_plain δ (seqRaiseK (opPayload n i v)) (seqRaiseK_hasHnd _) (seqRaiseK_catches _ 0)
        hp'.2 o ((hcont ls'' (hext.left hk')).2 hq) hk'
  · -- a raise of the finaliser supersedes the pending one
    obtain ⟨⟨rfl, hK₁, hTm, ha₁⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hq
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTm
    obtain ⟨o', hf', hle⟩ := hES m j o hf
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcτ
    refine Or.inr ⟨(seqRaiseK (opPayload n i v)).comp K₁, m, j, w, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, Row.tab_find hf',
        (show o'.abort = true by rw [← hle.1.abort_eq]; exact ha₁)⟩
        ⟨ρa, z, hcz, ⟨by simpa only [OpSig.ent, hle.1.2.2.2.1] using hPA, hnA⟩,
          noOwn_compS hz hnn hp'.2⟩⟩
    rw [catches_comp, hK₁]; rfl

/-- **The finaliser frame around an effectful computation** (`M then x. N unwind D`), at the rows
of `[then]` (SPEC §27): `M` at `Σ_M ≤ Σ`, `D` at `Σ_D ≤ Σ`, each capturable operation's cancel row
`Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`.  A stop of `M` at an operation keeps the frame in its continuation;
its cancel passes the frame and fires `D` (`then_cancel`).  An abortive stop runs `D` first
(`[finalise]`, `seq_raise_run`).  The frame, which `D` consumes, holds nothing where `Σ` may stop at
an unrestricted operation; a pending error holds nothing where `Σ_D` may.  `[spec §19, §27]` -/
theorem ewp_frame_then (δ : LSub) (S SM SD : Row) (hNZ : S.NZ) (hMS : RowLe SM S)
    (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hU : S.UnrD → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls)
      (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable (Row.tab SD δ)) Qd))
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls)
      (ewpTS ls ((ubindK Nv Dv).plug (.val v)) (opTable (Row.tab S δ)) Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTable (Row.tab SM δ)) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls ((ubindK Nv Dv).plug e) (opTable (Row.tab S δ)) Q ρ' := by
  have hNZD : ∀ n i o, Row.find SD n i = some o → o.n ≠ 0 := by
    intro n i o hf
    obtain ⟨o', hf', hle⟩ := hDS n i o hf
    rw [hle.1.1]; exact hNZ o' (Row.find_mem hf').1
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls ((ubindK Nv Dv).plug e) (opTable (Row.tab S δ)) Q ρ') ?_ h
  intro ls e ρ hs ρ₂ ρ' hF hc
  refine ewp_fold (opTable_mono _) (wpG_bind (ubindK Nv Dv) e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ' ⟨ρ, ρ₂, hc, hs, hF⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp
  · exact ewp_unfold (opTable_mono _) (hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · -- a `perform`: the frame joins the continuation's share; its cancel fires `D`
    refine wpG_here _ _ _ σ (Or.inr ?_)
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn
    obtain ⟨o', hf', hle⟩ := hMS n i o hf
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    refine Or.inl ⟨(ubindK Nv Dv).comp K₁, n, i, v, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, Row.tab_find hf',
        (show o'.abort = false by rw [← hle.1.abort_eq]; exact ha)⟩
      ⟨ρa, ρk', hcσ', by simpa only [OpSig.ent, hle.1.2.2.2.1] using hA, ?_,
        fun ls'' he => ⟨?_, fun hq => ?_⟩⟩⟩
    · rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]
    · intro hq
      have hq' : o.q = .unr := by rw [hle.1.2.2.1]; exact hq
      rw [hu hq', hU ⟨o', (Row.find_mem hf').1, Or.inl hq⟩ ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · intro w τ₁ τ₂ hB hcτ
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      rw [Kont.plug_comp]
      have hB' : (o.ent δ).PB ls'' w τ₁ := by simpa only [OpSig.ent, hle.1.2.2.2.2] using hB
      exact (hcont ls'' (he.left hk')).1 w τ₁ z hB' hz (hFe ls' ls'' σ₂ (he.right hk') hF') hcz
    · intro Q' hQ'
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ'
      have hcap : capB o.q o.B = true := hle.1.capB_eq ▸ hcap'
      have hth := hfin n i o o' hf hf' hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hth
        exact (hth.resolve_left (by simp)).1
      have hcan := (hcont ls'' (he.left hk')).2 (not_lin_of_capB hcap)
        (cancelObl (Row.tab o.fin.rowOf δ)) (by rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancel δ SD hNZD Nv Dv Fr hFs hFe (fun _ _ _ h => (hQd _ _ _ h).2) hD o.fin hth hnT
        (fun hu₁ => hU ⟨o', (Row.find_mem hf').1, Or.inr ⟨hcap', hu₁⟩⟩)
        (fun hu₁ => ((hP hu₁) o (Row.find_mem hf).1).2 hcap) hcan
        (hFe ls' ls'' σ₂ (he.right hk') hF') hk'
  · -- a `raise`: the finaliser runs, then the `raise` goes on
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn
    obtain ⟨o', hf', hle⟩ := hMS n i o hf
    have hn0 : n ≠ 0 := by
      rw [← (Row.find_mem hf).2.1, hle.1.1]; exact hNZ o' (Row.find_mem hf').1
    refine wpG_head (fun μ => Head.ufin μ Nv Dv n i v K₁ hn0 hK₁) rfl _ _ σ (ewp_unfold
      (opTable_mono _) ?_)
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcσ
    obtain ⟨y, hy, hcy⟩ := compS_lcomm hz hcz
    refine ewp_absorb (opTable_mono _) ?_ hn (ResU.CompS.comm hcy)
    have hPA' : (o'.ent δ).PA ls' v ρa := by simpa only [OpSig.ent, hle.1.2.2.2.1] using hPA
    exact seq_raise_run δ S SD hDS (Row.tab_find hf')
      (show o'.abort = true by rw [← hle.1.abort_eq]; exact ha) hQd (hD ls' σ₂ hF') ⟨hPA', hnA⟩
      (fun hu => vP_empty_of_persistent (((hP hu) o (Row.find_mem hf).1).1 ha) hPA)
      (ResU.CompS.comm hy)

/-! ### Compatibility of `[sub]`, `[perform]`, `[raise]`, `[let]` and `[then]` -/

/-- `[sub]`: a row may grow, its entries' cancel rows with it.  `[spec §19, §27]` -/
theorem sub_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (hle : RowLe S S') (h : SemC Δ Γ e (CTy.effOf S A)) : SemC Δ Γ e (CTy.effOf S' A) := by
  intro δ γ ls ρ hδ hg
  exact (cC_effOf S' A ls δ _ ρ).mpr (ewp_sub (Row.tab_le δ hle)
    ((cC_effOf S A ls δ _ ρ).mp (h δ γ ls ρ hδ hg)))

/-- `[perform]`, at any cancel row.  `[spec §19, §27]` -/
theorem perform_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hna : o.abort = false) (h : SemV Δ Γ V o.A) :
    SemC Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) := by
  intro δ γ ls ρ hδ hg
  refine (cC_effOf S o.B ls δ _ ρ).mpr ?_
  change ewpTS ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ _ ρ
  refine ewp_bind_pure_frame (opTable_mono _) _ _ ls (fun ls v => vC true o.A ls δ v)
    (fun _ => emp) _ (fun _ _ _ h => h) ?_ ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h δ γ ls ρ hδ hg, ⟨rfl, trivial⟩⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hc, hv, rfl, -⟩
  rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
  exact ewp_perform_here (en := o.ent δ) (Row.tab_find hf) hna (ent_start δ o) (fun _ _ _ h => h) hv

/-- `[raise]`: an abortive operation, at any answer type, its argument holding nothing owned.
`[spec §19]` -/
theorem raise_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig} {B : VTy}
    (hf : Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : ∀ ls δ v ρ, vC true o.A ls δ v ρ → NoOwn ρ) (h : SemV Δ Γ V o.A) :
    SemC Δ Γ (raiseE (opArgE o.n o.i V)) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  refine (cC_effOf S B ls δ _ ρ).mpr ?_
  change ewpTS ls ((Kont.appR (.val (.prim .raise))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ _ ρ
  refine ewp_bind_pure_frame (opTable_mono _) _ _ ls (fun ls v => vC true o.A ls δ v)
    (fun _ => emp) _ (fun _ _ _ h => h) ?_ ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h δ γ ls ρ hδ hg, ⟨rfl, trivial⟩⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hc, hv, rfl, -⟩
  rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
  exact ewp_raise_here (en := o.ent δ) (Row.tab_find hf) ha hv (hd _ _ _ _ hv)

/-- `[let]` at a row: `M to x. N`, the context of `N` dropping at a row with weakening and
persistent at an unrestricted row.  A cancel passing the frame leaves it behind
(`ent_plain`).  `[spec §19, §27]` -/
theorem let_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
    (hM : SemC Δ Γ₁ M (CTy.effOf S A)) (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B)) :
    SemC Δ Γ (.app (.val (.lam N)) M) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine (cC_effOf S B ls δ _ ρ).mpr ?_
  refine ewp_frame_plain (Row.tab S δ) (.appR (.val (.lam (Expr.psub 1 γ N))) .hole)
    (fun n => by simp [Kont.HasHnd]) (fun n => by simp [Kont.Catches])
    (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
    (fun _ _ _ he h => gDenC_local he h) ?_ ?_ ?_ (fun ls v => vC true A ls δ v) _ ?_
    ((cC_effOf S A ls δ _ ρ₁).mp (hM δ γ ls ρ₁ hδ hg₁)) hg₂ hc
  · intro n i en hT ha ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_noOwn (hW ⟨o, (Row.find_mem hf).1, OpSig.weak_of_ent (Or.inr ha)⟩) h
  · intro n i en hT hq ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · intro n i en hT ha hq ls' K₁ ρ' σ ρ'' hcan hσ hc'
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact ent_plain δ _ (fun n => by simp [Kont.HasHnd]) (by simp [Kont.Catches])
      (gDenC_noOwn (hW ⟨o, (Row.find_mem hf).1, OpSig.weak_of_ent (Or.inl hq)⟩) hσ) o hcan hc'
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ σ ?_
    rw [← substAll_cons_psub]
    exact (cC_effOf S B ls' δ _ σ).mp
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))

/-- **`[then]`**, SPEC §27: `M then x. N unwind D` at `Σ`, `M` at `Σ_M ≤ Σ`, the finaliser at
`Σ_D ≤ Σ`, and each capturable operation of `Σ_M` with `Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`; the errors
pending at the finaliser persistent where `Σ_D` has an unrestricted operation.  `[spec §19, §27]` -/
theorem then_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy}
    {S SM SD : Row} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Persistent Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers)
    (hM : SemC Δ Γ₁ M (CTy.effOf SM A)) (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B))
    (hD : SemC Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf SD .unit)) :
    SemC Δ Γ (thenE N D M) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine (cC_effOf S B ls δ _ ρ).mpr ?_
  change ewpTS ls ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug
    (substAll γ M)) _ _ ρ
  refine ewp_frame_then δ S SM SD hNZ hMS hDS hfin hP _ _
    (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
    (fun _ _ _ he h => gDenC_local he h)
    (fun hu _ _ h => gDenC_persistent (hU hu) h) (Qd := fun ls v => vC true .unit ls δ v) ?_ ?_
    (fun ls v => vC true A ls δ v) _ ?_
    ((cC_effOf SM A ls δ _ ρ₁).mp (hM δ γ ls ρ₁ hδ hg₁)) hg₂ hc
  · intro ls' v σ h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, noOwn_empty⟩
  · intro ls' σ h
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ D) Val.unit) rfl) ls' _ σ ?_
    rw [← substAll_cons_psub]
    exact (cC_effOf SD .unit ls' δ _ σ).mp
      (hD δ (Val.unit :: γ) ls' σ hδ (gDenC_dead_cons .unit Val.unit h))
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.uthen μ _ _ v) rfl) ls' _ σ ?_
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ σ ?_
    rw [← substAll_cons_psub]
    exact (cC_effOf S B ls' δ _ σ).mp
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))

/-! ### Compatibility of `[handle]` -/

/-- The table of `κ`'s cancel branch at an operation whose cancel row is `F`, at a handler whose
outer row is `Σ`: none at `⊤`, otherwise that of `F_{F ⊕ Σ} 1` (`cancelTy`).  `[spec §27]` -/
def cancelTabOf (S : Row) (F : CTy) (δ : LSub) : Option OpTab :=
  if F.isTop then none else some (Row.tab (F.rowOf ++ S) δ)

/-- `κ`'s relation gives `κ`'s type, its cancel branch at the operation's cancel row. -/
theorem vC_kTy_of_kapRel {S : Row} {R B : VTy} {q : Qual} {F : CTy} {δ : LSub} {ls : List SRec}
    {κ : Val} {ρ : WRes} (A : VTy) (n i : UInt32)
    (h : KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v)
      (OpSig.ent δ ⟨n, i, q, A, B, F⟩) (cancelTabOf S F δ) ls κ ρ) :
    vC true (kTy S R q B F) ls δ κ ρ := by
  obtain ⟨hu, hk⟩ := h
  have hres : ∀ ls', Ext ls ls' ρ →
      cC (.arr B (CTy.effOf S R)) ls' δ (.app κ.1 (.val (Val.inj₁ .unit))) ρ := by
    intro ls' he w σ₁ σ₂ hB hc
    exact (cC_effOf S R ls' δ _ σ₂).mpr ((hk ls' he).1 w σ₁ σ₂ hB hc)
  have hcan : q ≠ .lin → ∀ ls', Ext ls ls' ρ →
      cC (cancelTy S F) ls' δ (.app κ.1 (.val (Val.inj₂ .unit))) ρ := by
    intro hq ls' he
    unfold cancelTy
    cases hT : F.isTop
    · simp only [Bool.false_eq_true, if_false]
      refine (cC_effOf _ .unit ls' δ _ ρ).mpr ((hk ls' he).2 hq _ ?_)
      simp [cancelTabOf, hT]
    · simp only [if_true]; trivial
  cases q with
  | lin => exact fun ls' he => ⟨hres ls' he, trivial⟩
  | aff => exact fun ls' he => ⟨hres ls' he, hcan (by simp) ls' he⟩
  | unr => exact ⟨hu rfl, fun ls' he => ⟨hres ls' he, hcan (by simp) ls' he⟩⟩

/-- A cancel row's table is below that of `κ`'s cancel branch. -/
theorem tab_le_cancelTab (S : Row) (F : CTy) (δ : LSub) :
    (Row.tab F.rowOf δ).Le (Row.tab (F.rowOf ++ S) δ) :=
  Row.tab_le δ (RowLe.of_find fun n i o hf => by rw [Row.find_append, hf, Option.some_or])

/-- **A handler at clause values**: the answer clause and the clauses related at `∅`, at one list
(at a `!` type the relation at one list gives it at every list, `ext_empty'`), and the handled
computation at `Σ` extended by the handler's name, which `Σ` does not hold, the `j`-th operation at
the cancel row `fs j`.  The handler's tags are its effect's qualifiers; `κ`'s cancel branch is at
`cancelTy Σ (fs j)`.  `[spec §19, §25, §27]` -/
theorem ewp_handle_vals {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {A R : VTy} {δ : LSub} {ls₀ : List SRec} {vr vc : Val} (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
    (hVc : vC true (clausesTy S R E fs) ls₀ δ vc PMap.empty) {ls : List SRec} {e : Expr}
    {ρ : WRes}
    (he : ewpTS ls e (opTable (Row.tab (Row.ofEff n E 0 fs ++ S) δ))
      (fun ls v => vC true A ls δ v) ρ) :
    ewpTS ls (hndE (hndVal n (qualsVal (E.map Prod.fst)) vr vc) e) (opTable (Row.tab S δ))
      (fun ls v => vC true R ls δ v) ρ := by
  refine ewp_handle (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (Row.tab S δ) n hn0 ?_
    (qualsVal (E.map Prod.fst)) vr vc
    (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v)
    (fun i => cancelTabOf S (fs i.toNat) δ)
    (fun i en hT _ => capTag_ofEff hnS hlen i en hT) ?_ ?_ ?_ he
  · intro m i hm
    simp [Row.tab, Row.find_append, Row.find_ofEff_ne n E 0 fs m i hm]
  · intro i en hT ha hq Tk hTk
    obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
    have hcap := capB_of_ent ha hq
    rw [hji] at hTk
    simp only [cancelTabOf] at hTk
    split at hTk
    · cases hTk
    · rename_i hnT
      cases hTk
      refine ⟨Row.tab (fs j).rowOf δ, ?_, tab_le_cancelTab S (fs j) δ⟩
      rw [OpSig.ent_fin, if_pos hcap, finObl_eq]
      simp only [hnT, Bool.false_eq_true, if_false]
  · intro ls' v σ hv
    have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
    exact (cC_effOf S R ls' δ _ σ).mp hf
  · intro i en hT
    obtain ⟨j, hj, hji, hi, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
    obtain ⟨c, hcl, hVcl⟩ := clausesTy_at E fs hVc j hj
    refine ⟨c, by rw [hji]; exact hcl, ?_, ?_⟩
    · intro hna ls' v κ σ hσ
      generalize hEj : E[j] = t at hVcl hna hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at hna
      simp only [clauseTy, hna] at hVcl
      obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
      rw [hji] at hK
      have hκ := vC_kTy_of_kapRel (S := S) (R := R) (B := B') (q := q) (F := fs j) A' n
        (UInt32.ofNat (0 + j)) hK
      have hf := (hVcl.2 ls' (ext_empty' ls₀ ls')) (Val.pair v κ) σ σ
        ⟨v, κ, pure_sep_mk rfl ⟨σa, σk, hck, hA', hκ⟩⟩ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ).mp hf
    · intro ha ls' v σ hσ
      generalize hEj : E[j] = t at hVcl ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [clauseTy, ha] at hVcl
      have hf := (hVcl.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ).mp hf

/-- `[handle]`: the clauses and `h_ret` at `Σ`, the handled computation at `Σ` extended by the
handler's name, which `Σ` does not hold, its operations at the cancel rows `fs`.
`[spec §19, §27]` -/
theorem handle_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ Γr Γc : Ctx VTy} {e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy} {ir ic : Nat}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hsp₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E fs))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) :
    SemC Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (CTy.effOf S R) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨ρr, ρcl, hcrc, hgr, hgc⟩ := gDenC_split hsp₁ hg₁
  obtain ⟨hlr, hsr⟩ := gDenC_iff.mp hgr
  obtain ⟨vr, hvr, hVr⟩ := gSepC_soloP hr (hr.lt_of_liveWithin hlr) hsr
  obtain ⟨hlc, hsc⟩ := gDenC_iff.mp hgc
  obtain ⟨vc, hvc, hVc⟩ := gSepC_soloP hc (hc.lt_of_liveWithin hlc) hsc
  have hρr : ρr = PMap.empty := hVr.1
  have hρc : ρcl = PMap.empty := clausesTy_empty E fs hVc
  subst hρr hρc
  rw [eq_of_compS_empty_left hcrc] at hc12
  rw [eq_of_compS_empty_left hc12]
  have hsub : substAll γ (hndTerm n (E.map Prod.fst) ir ic e) =
      Expr.app (Expr.app (.val (.prim .hnd)) (.pair (.val (Val.i32 n))
        (.pair (.val (qualsVal (E.map Prod.fst))) (.pair (substAll γ (.var ir))
          (substAll γ (.var ic)))))) (substAll γ e) := by
    simp only [hndTerm, substAll, Expr.psub, Expr.val, Val.prim, Val.i32, psub_qualsVal]
  show cC _ ls δ (substAll γ (hndTerm n (E.map Prod.fst) ir ic e)) ρ₂
  rw [hsub, substAll_var_some hvr, substAll_var_some hvc]
  exact (cC_effOf S R ls δ _ ρ₂).mpr (ewp_handle_vals hn0 hnS hlen hVr hVc
    ((cC_effOf _ A ls δ _ ρ₂).mp (he δ γ ls ρ₂ hδ hg₂)))

/-- **The general `[handle]`**: `handle_n e with H`, `H` a value form over a context whose live
slots are persistent, typed at the answer clause's and the clauses' types, the `j`-th clause's `κ`
at the cancel row `fs j`; the handled computation at `Σ` extended by the handler's name, its
operations at those cancel rows.  `H` closes to a value; its relation is read off `wpTS` at that
value under the frame the run starts in (`wpTS_val_post`), and the handler is `ewp_handle_vals`.
`[spec §24, §27]` -/
theorem handleV_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {H e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hH : H.ValFormIn Γ₁)
    (hc : SemV Δ Γ₁ H (.tensor (retTy S A R) (clausesTy S R E fs)))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) :
    SemC Δ Γ (hndExpr n (E.map Prod.fst) H e) (CTy.effOf S R) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨hlw₁, hs₁⟩ := gDenC_iff.mp hg₁
  have hρ₁ : ρ₁ = PMap.empty := gSepC_deadP hd hs₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ H) := isVal_psub_valFormIn hlw₁ hH
  have hH' := hc δ γ ls PMap.empty hδ hg₁
  have hE' := (cC_effOf _ A ls δ _ ρ₂).mp (he δ γ ls ρ₂ hδ hg₂)
  show cC _ ls δ (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) H e)) ρ₂
  rw [psub_hndExpr]
  show cC _ ls δ (hndExpr n (E.map Prod.fst) (substAll γ H) (substAll γ e)) ρ₂
  refine (cC_effOf S R ls δ _ ρ₂).mpr (ewp_fold (opTable_mono _) ?_)
  intro ρf fρ ps hf hcf hT htg Al k
  obtain ⟨ls', ρ', -, hv⟩ := wpTS_val_post (v := ⟨substAll γ H, hval⟩) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg
  have hT₀ : (VTy.tensor (retTy S A R) (clausesTy S R E fs)).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]
    exact ⟨retTy_persistent S A R, clausesTy_persistent S R E fs⟩
  have hρ' : ρ' = PMap.empty := vP_empty_of_persistent hT₀ hv
  subst hρ'
  obtain ⟨vr, vc, h⟩ := hv
  obtain ⟨hpair, σ₁, σ₂, -, hVr, hVc⟩ := pure_sep_iff.mp h
  have hσ₁ : σ₁ = PMap.empty := vP_empty_of_persistent (retTy_persistent S A R) hVr
  have hσ₂ : σ₂ = PMap.empty := vP_empty_of_persistent (clausesTy_persistent S R E fs) hVc
  subst hσ₁ hσ₂
  have hHe : substAll γ H = (Val.pair vr vc).1 := congrArg Subtype.val hpair
  rw [hHe]
  exact ewp_unfold (opTable_mono _) (ewp_handle_vals hn0 hnS hlen hVr hVc hE')
    ρf fρ ps hf hcf hT htg Al k

end BoCa.Fig16.LogRel.Core

end
