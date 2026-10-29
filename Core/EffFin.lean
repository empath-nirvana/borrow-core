import Core.EffRules
import Core.DivRules

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
  | .eff n i q A B f cg C, o, h => by
      simp only [CTy.rowOf, List.mem_cons] at h
      rcases h with rfl | h
      · simp; omega
      · have := rowOf_fin_lt C h; simp; omega
  | .ret _, _, h | .arr _ _, _, h | .amp _ _, _, h | .top, _, h | .all _ _ _, _, h
  | .nu _, _, h => by simp [CTy.rowOf] at h

/-- A cancel row's table is the table of its layers. -/
theorem effTab_rowOf (δ : LSub) : ∀ F : CTy, effTab F δ = Row.tab F.rowOf δ
  | .eff n i q A B f cg C => by
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
  | eff n i q A B f cg C =>
      have h := effTab_rowOf δ (.eff n i q A B f cg C)
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
      (capB o.q o.B = true → FinLe o.fin o'.fin) ∧ (o.call = true → o'.call = true))
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- `o ≤ o′`: the same operation, its cancel row grown at a capturable operation, and graded
where `o` is: grading only weakens what a stop owes.  `[spec §27, §63]` -/
def OpSig.LeF (o o' : OpSig) : Prop :=
  o.Sig o' ∧ (capB o.q o.B = true → FinLe o.fin o'.fin) ∧ (o.call = true → o'.call = true)

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
  · refine Or.inr ⟨rfl, fun n i o hf => ⟨o, hf, OpSig.Sig.refl o, fun _ => FinLe.refl o.fin, id⟩⟩
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
  obtain ⟨o', hf', hs, hle, hg⟩ := h n i o hf
  obtain ⟨o'', hf'', hs', hle', hg'⟩ := h' n i o' hf'
  exact ⟨o'', hf'', hs.trans hs', fun hc =>
    FinLe.trans o.fin (hle hc) (hle' (hs.capB_eq ▸ hc)), fun hc => hg' (hg hc)⟩
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

theorem OpSig.LeF.refl (o : OpSig) : o.LeF o := ⟨OpSig.Sig.refl o, fun _ => FinLe.refl o.fin, id⟩

theorem OpSig.LeF.trans {o o' o'' : OpSig} (h : o.LeF o') (h' : o'.LeF o'') : o.LeF o'' :=
  ⟨h.1.trans h'.1, fun hc => FinLe.trans o.fin (h.2.1 hc) (h'.2.1 (h.1.capB_eq ▸ hc)),
    fun hc => h'.2.2 (h.2.2 hc)⟩

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

/-- A row is below another when each of its operations is below the one the other finds at its
key. -/
theorem RowLe.of_mem {S S' : Row}
    (h : ∀ o ∈ S, ∃ o', Row.find S' o.n o.i = some o' ∧ o.LeF o') : RowLe S S' := by
  intro n i o hf
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  exact h o hm

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
      obtain ⟨o', hf', hs, hle, hg⟩ := h n i o hf
      refine ⟨o'.ent δ, Row.tab_find hf', hs.2.2.1, hs.abort_eq, ?_, ?_, fun ha hq => ?_, hg⟩
      · simp only [OpSig.ent, hs.2.2.2.1]
      · simp only [OpSig.ent, hs.2.2.2.2]
      · have hc := capB_of_ent ha hq
        rw [OpSig.ent_fin, OpSig.ent_fin, if_pos hc, if_pos (hs.capB_eq ▸ hc)]
        exact finObl_mono δ o.fin (hle hc)
    · simp only [if_true]; exact trivial
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem hf).1

/-- The entries of one operation, not capturable, at two cancel rows are one entry. -/
theorem OpSig.ent_eq_of_sig (δ : LSub) {o o' : OpSig} (h : o.Sig o') (hc : capB o.q o.B = false)
    (hg : o.call = o'.call) : o.ent δ = o'.ent δ := by
  have hc' : capB o'.q o'.B = false := h.capB_eq ▸ hc
  simp only [OpSig.ent, OpSig.abort, hc', h.2.2.1, h.2.2.2.1, h.2.2.2.2, hg, Bool.false_eq_true,
    if_false]

/-- An operation's entry grows with the operation. -/
theorem OpSig.ent_le (δ : LSub) {o o' : OpSig} (h : o.LeF o') : (o.ent δ).Le (o'.ent δ) := by
  refine ⟨h.1.2.2.1, h.1.abort_eq, ?_, ?_, fun ha hq => ?_, h.2.2⟩
  · simp only [OpSig.ent, h.1.2.2.2.1]
  · simp only [OpSig.ent, h.1.2.2.2.2]
  · have hc := capB_of_ent ha hq
    rw [OpSig.ent_fin, OpSig.ent_fin, if_pos hc, if_pos (h.1.capB_eq ▸ hc)]
    exact finObl_mono δ o.fin (h.2.1 hc)

/-- **A row's table grows with the row** (`[sub]`).  `[spec §19, §27]` -/
theorem Row.tab_le {S S' : Row} (δ : LSub) (h : RowLe S S') : (Row.tab S δ).Le (Row.tab S' δ) := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨o', hf', hle⟩ := h n i o hf
  exact ⟨o'.ent δ, Row.tab_find hf', OpSig.ent_le δ hle⟩

theorem finUnr_of_mem : ∀ {G : CTy} {o : OpSig}, o ∈ G.rowOf →
    (o.q = .unr ∨ (capB o.q o.B = true ∧ o.fin.FinUnr)) → G.FinUnr
  | .eff n i q A B f cg C, o, ho, h => by
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
      (capB o.q o.B = true → PendLe P o.fin o'.fin) ∧ (o.call = true → o'.call = true)) ∧
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
      (capB o.q o.B = true → ThenLe o.fin E o'.fin) ∧ (o.call = true → o'.call = true)) ∧
    (∀ n i o, Row.find E n i = some o → ∃ o', Row.find T.rowOf n i = some o' ∧ o.Sig o' ∧
      (capB o.q o.B = true → PendLe F.rowOf o.fin o'.fin) ∧ (o.call = true → o'.call = true)))
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- With no finaliser effects, `F ⋈ ∅ ≤ F`: `[then]` at option A (SPEC §24) is an instance. -/
theorem ThenLe.nil (F : CTy) : ThenLe F [] F := by
  rw [ThenLe]
  cases hT : F.isTop
  · exact Or.inr ⟨rfl, fun n i o hf => ⟨o, hf, OpSig.Sig.refl o, fun _ => ThenLe.nil o.fin, id⟩,
      fun n i o hf => by simp [Row.find] at hf⟩
  · exact Or.inl rfl
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- The errors a cancel row may keep, at every depth, have persistent arguments.  `[spec §27]` -/
def CTy.FinPers : CTy → Prop
  | .eff _ _ q A B f _ C => ((B.isZero && q != .lin) = true → A.Persistent) ∧
      (capB q B = true → f.FinPers) ∧ C.FinPers
  | _ => True

/-- The errors that may be pending at a finaliser below which the row `Σ` runs have persistent
arguments: `Σ`'s abortive operations (a pending `raise`), and those of its capturable operations'
cancel rows at every depth (a cancel's kept error).  `[spec §27]` -/
def Row.PendPers (S : Row) : Prop :=
  ∀ o ∈ S, (o.abort = true → o.A.Persistent) ∧ (capB o.q o.B = true → o.fin.FinPers)

theorem finPers_of_mem : ∀ {F : CTy} {o : OpSig}, F.FinPers → o ∈ F.rowOf →
    (o.abort = true → o.A.Persistent) ∧ (capB o.q o.B = true → o.fin.FinPers)
  | .eff n i q A B f cg C, o, h, ho => by
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
    obtain ⟨o', hf', hs, hfin, hgr⟩ := hGG n i o hf
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
      exact (hcont ls'' ((hext.left hk').of_le hgr)).1 w τ₃ z hB' hz
        (errOk_local (Row.tab_local P δ) (hext.right hk').ext he') hu hcz
    · intro Q hQ
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hq₀ : (o.ent δ).q ≠ .lin := not_lin_of_capB hcap
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' ((hext.left hk').of_le hgr)).2 hq₀ (cancelObl (Row.tab o.fin.rowOf δ)) (by
        rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancel δ P err o.fin hfin' hnT hcan
        (errOk_local (Row.tab_local P δ) (hext.right hk').ext he')
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
      (capB o.q o.B = true → PendLe P o.fin o'.fin) ∧ (o.call = true → o'.call = true))
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
    obtain ⟨o', hf', hs, hfin, hgr⟩ := hE n i o hf
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
      exact (hcont ls'' ((hext.left hk').of_le hgr)).1 w τ₃ z hB' hz
        (errOk_local (Row.tab_local P δ) (hext.right hk').ext he') hu hcz
    · intro Q hQ
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [PendLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' ((hext.left hk').of_le hgr)).2 (not_lin_of_capB hcap)
        (cancelObl (Row.tab o.fin.rowOf δ)) (by rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((cfinK (cancelVal err)).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_cfinK, Kont.plug_comp]
      exact cfin_cancel δ P err o.fin hfin' hnT hcan
        (errOk_local (Row.tab_local P δ) (hext.right hk').ext he')
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
        obtain ⟨o', hf', hs, -, -⟩ := hFT n i o hf; exact ⟨o', hf', hs⟩) hNZ hQd
      (hD ls' τ₂ hF') he (fun hu => errOk_empty_of_pers (hpers hu) he) (ResU.CompS.comm hz)
  · -- an operation below the frame: the frame joins its continuation
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu', hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn
    obtain ⟨o', hf', hs, hfin, hgr⟩ := hFT n i o hf
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
      exact (hcont ls'' ((hext.left hk').of_le hgr)).1 w τ₃ z hB' hz (hFe ls' ls'' τ₂ (hext.right hk').ext hF') hcz
    · intro Q hQ
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ
      have hcap : capB o.q o.B = true := hs.capB_eq ▸ hcap'
      have hfin' := hfin hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hfin'
        exact (hfin'.resolve_left (by simp)).1
      have hcan := (hcont ls'' ((hext.left hk').of_le hgr)).2 (not_lin_of_capB hcap)
        (cancelObl (Row.tab o.fin.rowOf δ)) (by rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancel δ E hNZ Nv Dv Fr hFs hFe hQd hD o.fin hfin' hnT
        (fun hu₁ => hunr (finUnr_of_find hf' (Or.inr ⟨hcap', hu₁⟩)))
        (fun hu₁ => (finPers_of_mem (hpers hu₁) (Row.find_mem hf).1).2 hcap) hcan
        (hFe ls' ls'' τ₂ (hext.right hk').ext hF') hk'
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
theorem seq_raise_run (δ : LSub) (S E : Row) (hES : RowLe E S) (er : Bool)
    (hEk : er = true → Row.find E divEff 0 = none) {n i : UInt32} {v : Val}
    {en : OpEnt} (hTn : OpTab.eraseIf er (Row.tab S δ) n i = some en) (ha : en.abort = true)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    {Q : List SRec → Val → WProp} :
    ∀ {ls : List SRec} {d : Expr} {ρ : WRes}, ewpTS ls d (opTable (Row.tab E δ)) Qd ρ →
      ∀ {σp ρ' : WRes}, (en.PA ls v σp ∧ NoOwn σp) → (E.UnrD → σp = PMap.empty) →
        ResU.CompS ρ σp ρ' →
        ewpTS ls (.seq d (raiseE (.val (opPayload n i v)))) (opTable (OpTab.eraseIf er (Row.tab S δ))) Q ρ' := by
  intro ls d ρ h
  refine ewp_ind (fun ls d ρ => ∀ {σp ρ' : WRes}, (en.PA ls v σp ∧ NoOwn σp) →
    (E.UnrD → σp = PMap.empty) → ResU.CompS ρ σp ρ' →
    ewpTS ls (.seq d (raiseE (.val (opPayload n i v)))) (opTable (OpTab.eraseIf er (Row.tab S δ))) Q ρ') ?_ h
  intro ls d ρ hs σp ρ' hp hu hc
  refine ewp_fold (opTable_mono _) (wpG_bind (seqRaiseK (opPayload n i v)) d ls _ ρ' ?_)
  have h₁ := wpG_frame (e := d) (fun ls τ => τ = σp ∧ en.PA ls v τ ∧ NoOwn τ)
    (fun ls' hs' τ h => ⟨h.1, (Row.tab_local S δ n i en (OpTab.eraseIf_some hTn).1 _ ls' v τ (ext_of_same hs' τ)).1 h.2.1,
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
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, OpTab.eraseIf_of (Row.tab_find hf')
        (fun her ⟨hm, hj⟩ => by subst hm hj; rw [hEk her] at hf; cases hf),
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
        ⟨(Row.tab_local S δ n i en (OpTab.eraseIf_some hTn).1 _ ls'' v τ₂ (hext.right hk').ext).1 hp'.1, hp'.2⟩ hu hcz
    · exact ent_plain δ (seqRaiseK (opPayload n i v)) (seqRaiseK_hasHnd _) (seqRaiseK_catches _ 0)
        hp'.2 o ((hcont ls'' (hext.left hk')).2 hq) hk'
  · -- a raise of the finaliser supersedes the pending one
    obtain ⟨⟨rfl, hK₁, hTm, ha₁⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hq
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTm
    obtain ⟨o', hf', hle⟩ := hES m j o hf
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcτ
    refine Or.inr ⟨(seqRaiseK (opPayload n i v)).comp K₁, m, j, w, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, OpTab.eraseIf_of (Row.tab_find hf')
        (fun her ⟨hm, hj⟩ => by subst hm hj; rw [hEk her] at hf; cases hf),
        (show o'.abort = true by rw [← hle.1.abort_eq]; exact ha₁)⟩
        ⟨ρa, z, hcz, ⟨by simpa only [OpSig.ent, hle.1.2.2.2.1] using hPA, hnA⟩,
          noOwn_compS hz hnn hp'.2⟩⟩
    rw [catches_comp, hK₁]; rfl

/-- **The finaliser frame around an effectful computation** (`M then x. N unwind D`), at the rows
of `[then]` (SPEC §27): `M` at `Σ_M ≤ Σ`, `D` at `Σ_D ≤ Σ`, each capturable operation's cancel row
`Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`.  A stop of `M` at an operation keeps the frame in its continuation;
its cancel passes the frame and fires `D` (`then_cancel`).  An abortive stop runs `D` first
(`[finalise]`, `seq_raise_run`).  The frame, which `D` consumes, holds nothing where `Σ` may stop at
an unrestricted operation; a pending error holds nothing where `Σ_D` may.  At `opTable Σ_M` with a
table `Px` beside it whose stops owe nothing to the least fixed point, the frame joins `Px`'s stops
as `hPx` says: a tick at a row holding `Div` (`cwp_then`).  `[spec §14, §19, §27]` -/
theorem ewp_frame_then_or (δ : LSub) (S SM SD : Row) (hNZ : S.NZ) (hMS : RowLe SM S)
    (hDS : RowLe SD S) (er : Bool) (hSD : er = true → Row.find SD divEff 0 = none)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (Nv Dv : Val) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr ls) (Fr ls'))
    (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    (hU : S.UnrD → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls)
      (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable (Row.tab SD δ)) Qd))
    (Px Px' : Table) (hPx' : Px'.Mono)
    (hPx : ∀ ls t Φ Φ' σ₁ σ₂ σ, Px ls t Φ σ₁ → Fr ls σ₂ → ResU.CompS σ₁ σ₂ σ →
      Px' ls ((ubindK Nv Dv).plug t) Φ' σ)
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls)
      (ewpTS ls ((ubindK Nv Dv).plug (.val v)) (orTab (opTable (OpTab.eraseIf er (Row.tab S δ))) Px') Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (orTab (opTable (OpTab.eraseIf er (Row.tab SM δ))) Px) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls ((ubindK Nv Dv).plug e) (orTab (opTable (OpTab.eraseIf er (Row.tab S δ))) Px') Q ρ' := by
  have hM := orTab_mono (opTable_mono (OpTab.eraseIf er (Row.tab S δ))) hPx'
  have hNZD : ∀ n i o, Row.find SD n i = some o → o.n ≠ 0 := by
    intro n i o hf
    obtain ⟨o', hf', hle⟩ := hDS n i o hf
    rw [hle.1.1]; exact hNZ o' (Row.find_mem hf').1
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls ((ubindK Nv Dv).plug e) (orTab (opTable (OpTab.eraseIf er (Row.tab S δ))) Px') Q ρ') ?_ h
  intro ls e ρ hs ρ₂ ρ' hF hc
  refine ewp_fold hM (wpG_bind (ubindK Nv Dv) e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (hFs ls) ρ' ⟨ρ, ρ₂, hc, hs, hF⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp | hp
  · exact ewp_unfold hM (hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  swap
  · -- a stop of the table beside: the frame joins it
    exact wpG_here _ _ _ σ (Or.inr (Or.inr (hPx ls' t _ _ σ₁ σ₂ σ hp hF' hcσ)))
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · -- a `perform`: the frame joins the continuation's share; its cancel fires `D`
    refine wpG_here _ _ _ σ (Or.inr (Or.inl ?_))
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hTn₀, hkn⟩ := OpTab.eraseIf_some hTn
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn₀
    obtain ⟨o', hf', hle⟩ := hMS n i o hf
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    refine Or.inl ⟨(ubindK Nv Dv).comp K₁, n, i, v, o'.ent δ,
      pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, OpTab.eraseIf_of (Row.tab_find hf') hkn,
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
      exact (hcont ls'' ((he.left hk').of_le hle.2.2)).1 w τ₁ z hB' hz
        (hFe ls' ls'' σ₂ (he.right hk').ext hF') hcz
    · intro Q' hQ'
      obtain ⟨hcap', hnT, rfl⟩ := ent_fin_some hQ'
      have hcap : capB o.q o.B = true := hle.1.capB_eq ▸ hcap'
      have hth := hfin n i o o' hf hf' hcap
      have hoT : o.fin.isTop = false := by
        rw [ThenLe, hnT] at hth
        exact (hth.resolve_left (by simp)).1
      have hcan := (hcont ls'' ((he.left hk').of_le hle.2.2)).2 (not_lin_of_capB hcap)
        (cancelObl (Row.tab o.fin.rowOf δ)) (by rw [OpSig.ent_fin, if_pos hcap, finObl_eq, hoT]; rfl)
      show cancelObl _ ls'' (((ubindK Nv Dv).comp K₁).dead.plug _) ρk'
      rw [dead_comp, dead_ubindK, Kont.plug_comp]
      exact then_cancel δ SD hNZD Nv Dv Fr hFs hFe (fun _ _ _ h => (hQd _ _ _ h).2) hD o.fin hth hnT
        (fun hu₁ => hU ⟨o', (Row.find_mem hf').1, Or.inr ⟨hcap', hu₁⟩⟩)
        (fun hu₁ => ((hP hu₁) o (Row.find_mem hf).1).2 hcap) hcan
        (hFe ls' ls'' σ₂ (he.right hk').ext hF') hk'
  · -- a `raise`: the finaliser runs, then the `raise` goes on
    obtain ⟨⟨rfl, hK₁, hTn, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨hTn₀, hkn⟩ := OpTab.eraseIf_some hTn
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hTn₀
    obtain ⟨o', hf', hle⟩ := hMS n i o hf
    have hn0 : n ≠ 0 := by
      rw [← (Row.find_mem hf).2.1, hle.1.1]; exact hNZ o' (Row.find_mem hf').1
    refine wpG_head (fun μ => Head.ufin μ Nv Dv n i v K₁ hn0 hK₁) rfl _ _ σ (ewp_unfold
      hM ?_)
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcan hcσ
    obtain ⟨y, hy, hcy⟩ := compS_lcomm hz hcz
    refine ewp_absorb hM ?_ hn (ResU.CompS.comm hcy)
    have hPA' : (o'.ent δ).PA ls' v ρa := by simpa only [OpSig.ent, hle.1.2.2.2.1] using hPA
    refine ewp_mono hM (fun _ _ _ _ h => Or.inl h) (fun _ _ _ h => h) ?_
    exact seq_raise_run δ S SD hDS er hSD (OpTab.eraseIf_of (Row.tab_find hf') hkn)
      (show o'.abort = true by rw [← hle.1.abort_eq]; exact ha) hQd (hD ls' σ₂ hF') ⟨hPA', hnA⟩
      (fun hu => vP_empty_of_persistent (((hP hu) o (Row.find_mem hf).1).1 ha) hPA)
      (ResU.CompS.comm hy)

/-- **The finaliser frame around an effectful computation** (`ewp_frame_then_or` with nothing
beside the tables).  `[spec §19, §27]` -/
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
  intro ls e ρ h ρ₂ ρ' hF hc
  exact (ewp_orBot (opTable_mono _)).mp (ewp_frame_then_or δ S SM SD hNZ hMS hDS false
    (fun h => by cases h) hfin hP Nv Dv Fr
    hFs hFe hU hQd hD Table.bot Table.bot Table.bot_const.mono (fun _ _ _ _ _ _ _ h => h.elim) Q₁ Q
    (fun ls v σ hσ => (ewp_orBot (opTable_mono _)).mpr (hk ls v σ hσ))
    ((ewp_orBot (opTable_mono _)).mpr h) hF hc)

/-! ### Rows that hold `Div` -/

/-- A row holding `Div` holds it after growing (`[sub]` keeps the operation at each key).
`[spec §14]` -/
theorem Row.divB_le {S S' : Row} (hle : RowLe S S') (h : Row.divB S = true) :
    Row.divB S' = true := by
  obtain ⟨o, hf, ho⟩ := Row.divB_find h
  obtain ⟨o', hf', hs, -⟩ := hle _ _ _ hf
  refine Row.divB_iff.mpr ⟨o', hf', ?_⟩
  rw [← hs.2.2.1, ← hs.2.2.2.1, ← hs.2.2.2.2]
  exact ho

/-- Below a row holding `Div`, a row's operation at `Div`'s key is `tick`, if it has one. -/
theorem Row.divOK_of_le {S S' : Row} (hle : RowLe S S') (h : Row.divB S' = true) (δ : LSub) :
    (Row.tab S δ).DivOK := by
  intro en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨o', hf', hs, -⟩ := hle _ _ _ hf
  obtain ⟨o'', hf'', ho⟩ := Row.divB_find h
  rw [hf''] at hf'; cases hf'
  refine OpSig.isTick_ent δ ?_
  rw [hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2]; exact ho

/-- Below a row holding `Div`, a row that does not hold it has nothing at `Div`'s key. -/
theorem Row.find_key_none {S S' : Row} (hle : RowLe S S') (h : Row.divB S' = true)
    (hS : Row.divB S = false) : Row.find S divEff 0 = none := by
  cases hf : Row.find S divEff 0 with
  | none => rfl
  | some o =>
      exfalso
      obtain ⟨o', hf', hs, -⟩ := hle _ _ _ hf
      obtain ⟨o'', hf'', ho⟩ := Row.divB_find h
      rw [hf''] at hf'; cases hf'
      have : Row.divB S = true := Row.divB_iff.mpr ⟨o, hf, by
        rw [hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2]; exact ho⟩
      rw [hS] at this; cases this

theorem Row.keyNA_of_divB {S : Row} (δ : LSub) : Row.divB S = true → (Row.tab S δ).KeyNA :=
  fun h => (Row.divOK_of_divB h δ).keyNA

/-- **The relation at a row grows with the row** (`[sub]`), `Div` or not.  `[spec §14, §19]` -/
theorem effWp_sub {S S' : Row} (hle : RowLe S S') {δ : LSub} {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : effWp (Row.divB S) (Row.tab S δ) Q ls e ρ) :
    effWp (Row.divB S') (Row.tab S' δ) Q ls e ρ := by
  cases hS : Row.divB S <;> cases hS' : Row.divB S' <;> rw [hS] at h
  · exact ewp_sub (Row.tab_le δ hle) h
  · exact cwp_of_ewp (Row.keyNA_of_divB δ hS') (ewp_sub (Row.tab_le δ hle) h)
  · rw [Row.divB_le hle hS] at hS'; cases hS'
  · exact cwp_sub (Row.tab_le δ hle) h

/-! ### Grading only weakens -/

/-- `o` at the grade: call-graded.  `[spec §63]` -/
def OpSig.grade (o : OpSig) : OpSig := { o with call := true }

theorem OpSig.LeF.grade (o : OpSig) : o.LeF o.grade :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => FinLe.refl o.fin, fun _ => rfl⟩

/-- `Σ` with each operation `g` picks call-graded.  `[spec §63]` -/
def Row.gradeAt (g : OpSig → Bool) (S : Row) : Row := S.map fun o => if g o then o.grade else o

theorem Row.find_gradeAt (g : OpSig → Bool) (S : Row) (n i : UInt32) :
    Row.find (Row.gradeAt g S) n i = (Row.find S n i).map fun o => if g o then o.grade else o := by
  have hp : ((fun o => decide (n = o.n ∧ i = o.i)) ∘ fun o => if g o then o.grade else o) =
      fun o => decide (n = o.n ∧ i = o.i) := by
    funext o; simp only [Function.comp]; split <;> rfl
  unfold Row.find Row.gradeAt
  rw [List.find?_map, hp]

/-- **A row is below every grading of it** (`[sub]` grades).  `[spec §63]` -/
theorem rowLe_gradeAt (g : OpSig → Bool) (S : Row) : RowLe S (Row.gradeAt g S) := by
  intro n i o hf
  refine ⟨_, by rw [Row.find_gradeAt, hf]; rfl, ?_⟩
  show o.LeF (if g o then o.grade else o)
  split
  · exact OpSig.LeF.grade o
  · exact OpSig.LeF.refl o

/-- **Conservativity: grading only weakens.**  Every computation in the relation at a row is in
the relation at every grading of it.  `[spec §63]` -/
theorem effWp_gradeAt (g : OpSig → Bool) {S : Row} {δ : LSub} {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : effWp (Row.divB S) (Row.tab S δ) Q ls e ρ) :
    effWp (Row.divB (Row.gradeAt g S)) (Row.tab (Row.gradeAt g S) δ) Q ls e ρ :=
  effWp_sub (rowLe_gradeAt g S) h

/-- A stack of layers holds `Div` as its row does. -/
theorem CTy.divB_rowOf : ∀ C : CTy, Row.divB C.rowOf = C.divAt
  | .eff n i q A B fin cg C => by
      simp only [CTy.rowOf, Row.divB, CTy.effOf, CTy.divAt]
      rw [show (CTy.effOf C.rowOf .unit).divAt = Row.divB C.rowOf from rfl, CTy.divB_rowOf C]
  | .ret _ | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => rfl

/-! ### `Closing` at a row -/

/-- `tick` answered *close* only, at the grade `c`: `tick : 1 ↠ 0 ⊕ 1`.  `[spec §14, §63]` -/
def closeSig (c : Bool) : OpSig := ⟨divEff, 0, .lin, .unit, .sum .zero .unit, .ret .unit, c⟩

/-- The grade of the row's `tick`, `false` where it has none.  `[spec §63]` -/
def Row.divCall (S : Row) : Bool := ((Row.find S divEff 0).map OpSig.call).getD false

theorem Row.divCall_of_find {S : Row} {o : OpSig} (hf : Row.find S divEff 0 = some o) :
    S.divCall = o.call := by simp [Row.divCall, hf]

/-- A row's `tick` is graded in a larger row where it is graded. -/
theorem Row.divCall_le {S S' : Row} (hle : RowLe S S') (h : S.divCall = true) :
    S'.divCall = true := by
  unfold Row.divCall at h
  cases hf : Row.find S divEff 0 with
  | none => rw [hf] at h; cases h
  | some o =>
      rw [hf] at h
      obtain ⟨o', hf', hle'⟩ := hle _ _ o hf
      rw [Row.divCall_of_find hf']; exact hle'.2.2 h

/-- `tick`'s entry answered *close* only is the closing signature's, at its grade. -/
theorem closeSig_ent {en : OpEnt} (ht : en.IsTick) (δ : LSub) :
    en.closeOnly.Le ((closeSig en.call).ent δ) ∧ ((closeSig en.call).ent δ).Le en.closeOnly := by
  have hPA : en.PA = fun ls v => vC true .unit ls δ v := by
    funext ls v ρ; exact propext ((ht.2.2.1 ls v ρ).trans vC_unit_iff.symm)
  have hPB : en.closeOnly.PB = fun ls v => vC true (.sum .zero .unit) ls δ v := by
    funext ls w ρ
    refine propext ⟨fun ⟨hb, hw⟩ => ?_, fun h => ?_⟩
    · obtain ⟨-, rfl⟩ := (ht.2.2.2 ls w ρ).mp hb
      subst hw
      exact Or.inr ⟨.unit, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
    · rcases h with ⟨v, ρ₁, ρ₂, hc, ⟨rfl, -⟩, hz⟩ | ⟨v, ρ₁, ρ₂, hc, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
      · exact hz.elim
      · exact ⟨(ht.2.2.2 ls _ _).mpr ⟨Or.inr rfl, eq_of_compS_empty_left hc⟩, rfl⟩
  have hq : en.closeOnly.q = ((closeSig en.call).ent δ).q := ht.1
  have ha : en.closeOnly.abort = ((closeSig en.call).ent δ).abort := ht.2.1
  have hA : en.closeOnly.PA = ((closeSig en.call).ent δ).PA := hPA
  have hB : en.closeOnly.PB = ((closeSig en.call).ent δ).PB := hPB
  exact ⟨⟨hq, ha, hA, hB, fun _ h => absurd ht.1 h, id⟩,
    ⟨hq.symm, ha.symm, hA.symm, hB.symm, fun _ h => absurd rfl h, id⟩⟩

theorem find_closeSig (c : Bool) (S : Row) (n i : UInt32) :
    Row.find (closeSig c :: S) n i = if n = divEff ∧ i = 0 then some (closeSig c)
      else Row.find S n i := by
  by_cases h : n = divEff ∧ i = 0
  · rw [if_pos h]; simp [Row.find, List.find?, closeSig, h]
  · rw [if_neg h]
    have : decide (n = (closeSig c).n ∧ i = (closeSig c).i) = false := by
      simp only [closeSig]; exact decide_eq_false h
    simp [Row.find, List.find?, this]

/-- **`Closing` at a row is `ewpTS` at the row with the closing signature in front.** -/
theorem closing_to_row {S : Row} {δ : LSub} (hT : (Row.tab S δ).DivOK)
    {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Closing (Row.tab S δ) Q ls e ρ) :
    ewpTS ls e (opTable (Row.tab (closeSig S.divCall :: S) δ)) Q ρ := by
  refine ewp_sub (fun n i en hT' => ?_) h
  unfold OpTab.closeAt at hT'
  by_cases hk : n = divEff ∧ i = 0
  · rw [if_pos hk] at hT'
    obtain ⟨rfl, rfl⟩ := hk
    cases h₀ : Row.tab S δ divEff 0 with
    | none => rw [h₀] at hT'; cases hT'
    | some en₀ =>
        rw [h₀] at hT'; cases hT'
        obtain ⟨o₀, hf₀, rfl⟩ := Row.tab_some h₀
        have hc : S.divCall = (o₀.ent δ).call := Row.divCall_of_find hf₀
        rw [hc]
        exact ⟨(closeSig (o₀.ent δ).call).ent δ,
          Row.tab_find (by rw [find_closeSig, if_pos ⟨rfl, rfl⟩]), (closeSig_ent (hT _ h₀) δ).1⟩
  · rw [if_neg hk] at hT'
    exact ⟨en, by simp only [Row.tab, find_closeSig, if_neg hk]; exact hT', OpEnt.Le.refl en⟩

theorem closing_of_row {S : Row} {δ : LSub} {en₀ : OpEnt} (h₀ : Row.tab S δ divEff 0 = some en₀)
    (ht : en₀.IsTick) {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (opTable (Row.tab (closeSig S.divCall :: S) δ)) Q ρ) :
    Closing (Row.tab S δ) Q ls e ρ := by
  refine ewp_sub (fun n i en hT' => ?_) h
  by_cases hk : n = divEff ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := hk
    simp only [Row.tab, find_closeSig, if_pos (And.intro rfl rfl), Option.map_some] at hT'
    cases hT'
    obtain ⟨o₀, hf₀, rfl⟩ := Row.tab_some h₀
    have hc : S.divCall = (o₀.ent δ).call := Row.divCall_of_find hf₀
    rw [hc]
    exact ⟨(o₀.ent δ).closeOnly, by rw [OpTab.closeAt_key, h₀]; rfl, (closeSig_ent ht δ).2⟩
  · simp only [Row.tab, find_closeSig, if_neg hk] at hT'
    exact ⟨en, by rw [OpTab.closeAt_ne hk]; exact hT', OpEnt.Le.refl en⟩

theorem divEff_ne_zero : divEff ≠ 0 := by decide

/-! ### `[then]` at a row holding `Div` -/

section
variable {δ : LSub} {S SM SD : Row} (hSd : Row.divB S = true) (hSDd : Row.divB SD = false)
  (hNZ : S.NZ) (hMS : RowLe SM S) (hDS : RowLe SD S)
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

include hSd hSDd hNZ hMS hDS hfin hP hFs hFe hU hQd hD in
/-- **`Closing` under the finaliser frame**: Core's `ewp_frame_then` at the rows with the closing
signature in front. -/
theorem closing_then
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (Closing (Row.tab S δ) Q ls ((ubindK Nv Dv).plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : Closing (Row.tab SM δ) Q₁ ls e ρ)
    {ρ₂ ρ' : WRes} (hF : Fr ls ρ₂) (hc : ResU.CompS ρ ρ₂ ρ') :
    Closing (Row.tab S δ) Q ls ((ubindK Nv Dv).plug e) ρ' := by
  obtain ⟨o, hf, ho⟩ := Row.divB_find hSd
  have h₀ : Row.tab S δ divEff 0 = some (o.ent δ) := Row.tab_find hf
  have ht := OpSig.isTick_ent δ ho
  have hDk := Row.find_key_none hDS hSd hSDd
  refine closing_of_row h₀ ht ?_
  refine ewp_frame_then δ (closeSig S.divCall :: S) (closeSig SM.divCall :: SM) SD ?_ ?_ ?_ ?_ ?_
    Nv Dv Fr hFs hFe ?_ hQd hD
    Q₁ Q (fun ls v σ hσ => closing_to_row (Row.divOK_of_divB hSd δ) (hk ls v σ hσ))
    (closing_to_row (Row.divOK_of_le hMS hSd δ) h) hF hc
  · intro o' ho'
    simp only [List.mem_cons] at ho'
    rcases ho' with rfl | ho'
    · exact divEff_ne_zero
    · exact hNZ o' ho'
  · intro n i o' hf'
    rw [find_closeSig] at hf' ⊢
    split at hf'
    · rw [if_pos (by assumption)]; cases hf'
      exact ⟨_, rfl, OpSig.Sig.refl _, fun h => absurd h (by simp [capB, closeSig, OpSig.abort, VTy.isZero]), Row.divCall_le hMS⟩
    · rw [if_neg (by assumption)]; exact hMS n i o' hf'
  · intro n i o' hf'
    rw [find_closeSig]
    by_cases hk : n = divEff ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk; rw [hDk] at hf'; cases hf'
    · rw [if_neg hk]; exact hDS n i o' hf'
  · intro n i o₁ o₂ hf₁ hf₂ hcap
    rw [find_closeSig] at hf₁ hf₂
    split at hf₁
    · cases hf₁; exact absurd hcap (by simp [capB, closeSig, OpSig.abort, VTy.isZero])
    · rw [if_neg (by assumption)] at hf₂; exact hfin n i o₁ o₂ hf₁ hf₂ hcap
  · intro hu o' ho'
    simp only [List.mem_cons] at ho'
    rcases ho' with rfl | ho'
    · exact ⟨fun h => absurd h (by simp [capB, closeSig, OpSig.abort, VTy.isZero]), fun h => absurd h (by simp [capB, closeSig, OpSig.abort, VTy.isZero])⟩
    · exact hP hu o' ho'
  · rintro ⟨o', ho', hu⟩
    simp only [List.mem_cons] at ho'
    rcases ho' with rfl | ho'
    · rcases hu with hu | ⟨hcap, -⟩
      · cases hu
      · exact absurd hcap (by simp [capB, closeSig, OpSig.abort, VTy.isZero])
    · exact hU ⟨o', ho', hu⟩

include hSd hSDd hNZ hMS hDS hfin hP hFs hFe hU hQd hD in
/-- **A finaliser frame around a computation of `cwp`, one segment**, at any target candidate `Y`
that holds the frame around every computation of `cwp` (`hY`): the segment is
`ewp_frame_then_or` at the tables without the tick; a tick inside the frame owes the frame around
its continuation, in `Y` and, by `closing_then`, in `Closing`.  `N` is read only through `hk`, so
its answer may land in `Y` itself.  `cwpF_frame` at the finaliser frame.  `[spec §14, §19, §27]` -/
theorem cwpF_frame_then (Y : List SRec → Expr → WProp)
    (hY : ∀ ls e ρ ρ₂ ρ', cwp (Row.tab SM δ) Q₁ ls e ρ → Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
      Y ls ((ubindK Nv Dv).plug e) ρ')
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwpF (Row.tab S δ) Q Y ls ((ubindK Nv Dv).plug (.val v))))
    (hkc : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (Closing (Row.tab S δ) Q ls ((ubindK Nv Dv).plug (.val v)))) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cwp (Row.tab SM δ) Q₁ ls e ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        cwpF (Row.tab S δ) Q Y ls ((ubindK Nv Dv).plug e) ρ' := by
  have hTM := Row.divOK_of_le hMS hSd δ
  have hDk := Row.find_key_none hDS hSd hSDd
  intro ls e ρ he ρ₂ ρ' hF hc
  refine ewp_frame_then_or δ S SM SD hNZ hMS hDS true (fun _ => hDk) hfin hP Nv Dv Fr hFs hFe hU
    hQd hD _ _ (Table.Const.mono fun _ _ _ _ _ h => h) ?_ Q₁ Q hk (cwp_out he) hF hc
  intro ls' t Φ Φ' σ₁ σ₂ σ hp hF' hcσ
  obtain ⟨K₁, en, rfl, hK₁, hT0, ht, hcont⟩ := tickStop_inv hTM hp
  obtain ⟨o, hf, ho⟩ := Row.divB_find hSd
  have h₀ : Row.tab S δ divEff 0 = some (o.ent δ) := Row.tab_find hf
  rw [← Kont.plug_comp]
  refine tickStop_mk h₀ (OpSig.isTick_ent δ ho) ((ubindK Nv Dv).comp K₁)
    (by rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val, Val.pair]) fun ls'' he w hw => ?_
  have hgr : en.call = true → (o.ent δ).call = true := by
    obtain ⟨oM, hfM, rfl⟩ := Row.tab_some hT0
    obtain ⟨o', hf', hle'⟩ := hMS _ _ oM hfM
    rw [hf] at hf'; cases hf'
    exact hle'.2.2
  have ho' := hcont ls'' ((he.left hcσ).of_le hgr) w hw
  have hF'' := hFe ls' ls'' σ₂ (he.right hcσ).ext hF'
  rw [Kont.plug_comp]
  exact ⟨hY _ _ _ σ₂ σ ho'.1 hF'' hcσ,
    closing_then hSd hSDd hNZ hMS hDS hfin hP Nv Dv Fr hFs hFe hU hQd hD Q₁ Q hkc ho'.2 hF'' hcσ⟩

include hSd hSDd hNZ hMS hDS hfin hP hFs hFe hU hQd hD in
/-- **`[then]` at `cwp`**, by coinduction up to `cwp`, the candidate the finaliser frame around a
computation of `cwp`, one segment at a time (`cwpF_frame_then`).  `[spec §14, §19, §27]` -/
theorem cwp_then
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (cwp (Row.tab S δ) Q ls ((ubindK Nv Dv).plug (.val v))))
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cwp (Row.tab SM δ) Q₁ ls e ρ)
    {ρ₂ ρ' : WRes} (hF : Fr ls ρ₂) (hc : ResU.CompS ρ ρ₂ ρ') :
    cwp (Row.tab S δ) Q ls ((ubindK Nv Dv).plug e) ρ' := by
  let W : List SRec → Expr → WProp := fun ls x ρ' => ∃ e ρ ρ₂, x = (ubindK Nv Dv).plug e ∧
    cwp (Row.tab SM δ) Q₁ ls e ρ ∧ Fr ls ρ₂ ∧ ResU.CompS ρ ρ₂ ρ'
  have hW' : ∀ ls x ρ, W ls x ρ →
      cwpF (Row.tab S δ) Q (fun ls e ρ => W ls e ρ ∨ cwp (Row.tab S δ) Q ls e ρ) ls x ρ := by
    rintro ls x ρ' ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩
    exact cwpF_frame_then hSd hSDd hNZ hMS hDS hfin hP Nv Dv Fr hFs hFe hU hQd hD Q₁ Q _
      (fun ls e ρ ρ₂ ρ' he hF hc => Or.inl ⟨e, ρ, ρ₂, rfl, he, hF, hc⟩)
      (fun ls v σ hσ => cwpF_mono (fun _ _ _ h => Or.inr h) (cwp_out (hk ls v σ hσ)))
      (fun ls v σ hσ => closing_of_cwp (hk ls v σ hσ)) he hF hc
  exact cwp_coind_up hW' ⟨e, ρ, ρ₂, rfl, h, hF, hc⟩

end

/-! ### Compatibility of `[sub]`, `[perform]`, `[raise]`, `[let]` and `[then]` -/

/-- `[sub]`: a row may grow, its entries' cancel rows with it; a row that holds `Div` holds it
after growing.  `[spec §14, §19, §27]` -/
theorem sub_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (hle : RowLe S S') (h : SemC Δ Γ e (CTy.effOf S A)) : SemC Δ Γ e (CTy.effOf S' A) := by
  intro δ γ ls ρ hδ hg
  exact (cC_effOf_wp S' A ls δ _ ρ).mpr (effWp_sub hle
    ((cC_effOf_wp S A ls δ _ ρ).mp (h δ γ ls ρ hδ hg)))

/-- `[perform]`, at any cancel row: the operation stops at once, so it is in the least fixed
point, and in the greatest where the row holds `Div` (`cwp_of_ewp`).  `[spec §14, §19, §27]` -/
theorem perform_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hna : o.abort = false) (h : SemV Δ Γ V o.A) :
    SemC Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) := by
  intro δ γ ls ρ hδ hg
  refine (cC_effOf_wp S o.B ls δ _ ρ).mpr (effWp_of_ewp (Row.keyNA_of_divB δ) ?_)
  change ewpTS ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ _ ρ
  refine ewp_bind_pure_frame (opTable_mono _) _ _ ls (fun ls v => vC true o.A ls δ v)
    (fun _ => emp) _ (fun _ _ _ h => h) ?_ ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h δ γ ls ρ hδ hg, ⟨rfl, trivial⟩⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hc, hv, rfl, -⟩
  rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
  exact ewp_perform_here (en := o.ent δ) (Row.tab_find hf) hna (ent_start δ o) (fun _ _ _ h => h) hv

/-- `[raise]`: an abortive operation, at any answer type, its argument holding nothing owned.
`[spec §14, §19]` -/
theorem raise_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig} {B : VTy}
    (hf : Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : ∀ ls δ v ρ, vC true o.A ls δ v ρ → NoOwn ρ) (h : SemV Δ Γ V o.A) :
    SemC Δ Γ (raiseE (opArgE o.n o.i V)) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  refine (cC_effOf_wp S B ls δ _ ρ).mpr (effWp_of_ewp (Row.keyNA_of_divB δ) ?_)
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
(`ent_plain`).  At a row holding `Div`, bind at `cwp` (`cwp_bind`).  `[spec §14, §19, §27]` -/
theorem let_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
    (hM : SemC Δ Γ₁ M (CTy.effOf S A)) (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B)) :
    SemC Δ Γ (.app (.val (.lam N)) M) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  have hW' : ∀ n i en, Row.tab S δ n i = some en → en.abort = true →
      ∀ ls ρ, gDenC ls δ Γ₂ γ ρ → NoOwn ρ := by
    intro n i en hT ha ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_noOwn (hW ⟨o, (Row.find_mem hf).1, OpSig.weak_of_ent (Or.inr ha)⟩) h
  have hU' : ∀ n i en, Row.tab S δ n i = some en → en.q = .unr →
      ∀ ls ρ, gDenC ls δ Γ₂ γ ρ → ρ = PMap.empty := by
    intro n i en hT hq ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  have hK' : ∀ n i en, Row.tab S δ n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → gDenC ls δ Γ₂ γ σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls ((Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).comp K₁) ρ' := by
    intro n i en hT ha hq ls' K₁ ρ' σ ρ'' hcan hσ hc'
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact ent_plain δ _ (fun n => by simp [Kont.HasHnd]) (by simp [Kont.Catches])
      (gDenC_noOwn (hW ⟨o, (Row.find_mem hf).1, OpSig.weak_of_ent (Or.inl hq)⟩) hσ) o hcan hc'
  have hk : ∀ ls' v, Entails ((fun ls v => vC true A ls δ v) ls' v ⋆ gDenC ls' δ Γ₂ γ)
      (effWp (Row.divB S) (Row.tab S δ) (fun ls v => vC true B ls δ v) ls'
        ((Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).plug (.val v))) := by
    rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine effWp_step (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' σ ?_
    rw [← substAll_cons_psub]
    exact (cC_effOf_wp S B ls' δ _ σ).mp
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))
  have hM' := (cC_effOf_wp S A ls δ _ ρ₁).mp (hM δ γ ls ρ₁ hδ hg₁)
  refine (cC_effOf_wp S B ls δ _ ρ).mpr ?_
  cases hS : Row.divB S <;> rw [hS] at hM' hk
  · exact ewp_frame_plain (Row.tab S δ) (.appR (.val (.lam (Expr.psub 1 γ N))) .hole)
      (fun n => by simp [Kont.HasHnd]) (fun n => by simp [Kont.Catches])
      (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
      (fun _ _ _ he h => gDenC_local he h) hW' hU' hK' (fun ls v => vC true A ls δ v) _ hk
      hM' hg₂ hc
  · exact cwp_bind (Row.divOK_of_divB hS δ) (.appR (.val (.lam (Expr.psub 1 γ N))) .hole)
      (fun n => by simp [Kont.HasHnd]) (fun n => by simp [Kont.Catches])
      (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
      (fun _ _ _ he h => gDenC_local he h) hW' hU' hK' (fun ls v => vC true A ls δ v) _ hk
      hM' hg₂ hc

/-- **`[then]`**, SPEC §27: `M then x. N unwind D` at `Σ`, `M` at `Σ_M ≤ Σ`, the finaliser at
`Σ_D ≤ Σ`, and each capturable operation of `Σ_M` with `Σ(o).fin ≥ Σ_M(o).fin ⋈ Σ_D`; the errors
pending at the finaliser persistent where `Σ_D` has an unrestricted operation.  The finaliser's
row does not hold `Div` (`hSD`): a finaliser does not tick.  At a row holding `Div`, `[then]` at
`cwp` (`cwp_then`).  `[spec §14, §19, §27]` -/
theorem then_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy}
    {S SM SD : Row} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Persistent Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (hSD : Row.divB SD = false)
    (hM : SemC Δ Γ₁ M (CTy.effOf SM A)) (hN : SemC Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B))
    (hD : SemC Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf SD .unit)) :
    SemC Δ Γ (thenE N D M) (CTy.effOf S B) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  have hQd : ∀ ls v ρ, (fun ls v => vC true .unit ls δ v) ls v ρ → v = .unit ∧ NoOwn ρ := by
    intro ls' v σ h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, noOwn_empty⟩
  have hD' : ∀ ls, Entails (gDenC ls δ Γ₂ γ) (ewpTS ls (.app (.val (Val.lam (Expr.psub 1 γ D)))
      (.val .unit)) (opTable (Row.tab SD δ)) (fun ls v => vC true .unit ls δ v)) := by
    intro ls' σ h
    refine ewp_step (opTable_mono _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ D) Val.unit) rfl) ls' _ σ ?_
    rw [← substAll_cons_psub]
    exact (cC_effOf SD .unit ls' δ _ σ hSD).mp
      (hD δ (Val.unit :: γ) ls' σ hδ (gDenC_dead_cons .unit Val.unit h))
  have hk : ∀ ls' v, Entails ((fun ls v => vC true A ls δ v) ls' v ⋆ gDenC ls' δ Γ₂ γ)
      (effWp (Row.divB S) (Row.tab S δ) (fun ls v => vC true B ls δ v) ls'
        ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug (.val v))) := by
    rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine effWp_step (fun μ => Step1N.head (Head.uthen μ _ _ v) rfl) ls' σ ?_
    refine effWp_step (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' σ ?_
    rw [← substAll_cons_psub]
    exact (cC_effOf_wp S B ls' δ _ σ).mp
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))
  have hM' := (cC_effOf_wp SM A ls δ _ ρ₁).mp (hM δ γ ls ρ₁ hδ hg₁)
  refine (cC_effOf_wp S B ls δ _ ρ).mpr ?_
  change effWp _ _ _ ls ((ubindK (Val.lam (Expr.psub 1 γ N)) (Val.lam (Expr.psub 1 γ D))).plug
    (substAll γ M)) ρ
  cases hS : Row.divB S <;> rw [hS] at hk
  · have hSM : Row.divB SM = false := by
      cases h' : Row.divB SM
      · rfl
      · rw [Row.divB_le hMS h'] at hS; cases hS
    rw [hSM] at hM'
    exact ewp_frame_then δ S SM SD hNZ hMS hDS hfin hP _ _
      (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
      (fun _ _ _ he h => gDenC_local he h)
      (fun hu _ _ h => gDenC_persistent (hU hu) h) hQd hD' (fun ls v => vC true A ls δ v) _ hk
      hM' hg₂ hc
  · have hM'' : cwp (Row.tab SM δ) (fun ls v => vC true A ls δ v) ls (substAll γ M) ρ₁ := by
      cases hSM : Row.divB SM <;> rw [hSM] at hM'
      · exact cwp_of_ewp (Row.divOK_of_le hMS hS δ).keyNA hM'
      · exact hM'
    exact cwp_then hS hSD hNZ hMS hDS hfin hP _ _
      (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
      (fun _ _ _ he h => gDenC_local he h)
      (fun hu _ _ h => gDenC_persistent (hU hu) h) hQd hD' (fun ls v => vC true A ls δ v) _ hk
      hM'' hg₂ hc

/-- A handled row that does not hold `Div`, around a row without the handler's name: the outer
row does not hold it either. -/
theorem Row.divB_of_ofEff {S : Row} {n : UInt32} {E : List (Qual × VTy × VTy)} {k : Nat}
    {fs : Nat → CTy} (hnS : ∀ o ∈ S, o.n ≠ n) (h : Row.divB (Row.ofEff n E k fs ++ S) = false) :
    Row.divB S = false := by
  cases hd : Row.divB S with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨o, hf, ho⟩ := Row.divB_find hd
      obtain ⟨hm, hon, -⟩ := Row.find_mem hf
      have hne : divEff ≠ n := fun h' => hnS o hm (hon.trans h')
      have : Row.divB (Row.ofEff n E k fs ++ S) = true := Row.divB_iff.mpr ⟨o, by
        rw [Row.find_append, Row.find_ofEff_ne n E k fs _ _ hne]; exact hf, ho⟩
      rw [h] at this; cases this

/-! ### Compatibility of `[handle]` -/

/-- The table of `κ`'s cancel branch at an operation whose cancel row is `F`, at a handler whose
outer row is `Σ`: none at `⊤`, otherwise that of `F_{F ⊕ Σ} 1` (`cancelTy`).  `[spec §27]` -/
def cancelTabOf (S : Row) (F : CTy) (δ : LSub) : Option OpTab :=
  if F.isTop then none else some (Row.tab (F.rowOf ++ S) δ)

/-- `κ`'s relation gives `κ`'s type, its cancel branch at the operation's cancel row. -/
theorem vC_kTy_of_kapRel {S : Row} {R B : VTy} {q : Qual} {F : CTy} {δ : LSub} {ls : List SRec}
    {κ : Val} {ρ : WRes} (A : VTy) (n i : UInt32)
    (h : KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v)
      (OpSig.ent δ ⟨n, i, q, A, B, F, false⟩) (cancelTabOf S F δ) ls κ ρ) :
    vC true (kTy S R q B F) ls δ κ ρ := by
  obtain ⟨hu, hk⟩ := h
  have hres : ∀ ls', Ext ls ls' ρ →
      cC (.arr B (CTy.effOf S R)) ls' δ (.app κ.1 (.val (Val.inj₁ .unit))) ρ := by
    intro ls' he w σ₁ σ₂ hB hc
    exact (cC_effOf_wp S R ls' δ _ σ₂).mpr (effWp_of_ewp (Row.keyNA_of_divB δ)
      ((hk ls' he).1 w σ₁ σ₂ hB hc))
  have hcan : q ≠ .lin → ∀ ls', Ext ls ls' ρ →
      cC (cancelTy S F) ls' δ (.app κ.1 (.val (Val.inj₂ .unit))) ρ := by
    intro hq ls' he
    unfold cancelTy
    cases hT : F.isTop
    · simp only [Bool.false_eq_true, if_false]
      refine (cC_effOf_wp _ .unit ls' δ _ ρ).mpr (effWp_of_ewp (Row.keyNA_of_divB δ)
        ((hk ls' he).2 hq _ ?_))
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
    {A R : VTy} {δ : LSub} {ls₀ : List SRec} {vr vc : Val} (hS : Row.divB S = false)
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
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
    exact (cC_effOf S R ls' δ _ σ hS).mp hf
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
      exact (cC_effOf S R ls' δ _ σ hS).mp hf
    · intro ha ls' v σ hσ
      generalize hEj : E[j] = t at hVcl ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [clauseTy, ha] at hVcl
      have hf := (hVcl.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ hS).mp hf

/-- `[handle]`: the clauses and `h_ret` at `Σ`, the handled computation at `Σ` extended by the
handler's name, which `Σ` does not hold, its operations at the cancel rows `fs`.
`[spec §19, §27]` -/
theorem handle_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ Γr Γc : Ctx VTy} {e : Expr} {S : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy} {ir ic : Nat}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hsp₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E fs))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) :
    SemC Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (CTy.effOf S R) := by
  have hS := Row.divB_of_ofEff hnS hdv
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
  exact (cC_effOf S R ls δ _ ρ₂ hS).mpr (ewp_handle_vals hS hn0 hnS hlen hVr hVc
    ((cC_effOf _ A ls δ _ ρ₂ hdv).mp (he δ γ ls ρ₂ hδ hg₂)))

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
    (hdv : Row.divB (Row.ofEff n E 0 fs ++ S) = false)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) :
    SemC Δ Γ (hndExpr n (E.map Prod.fst) H e) (CTy.effOf S R) := by
  have hS := Row.divB_of_ofEff hnS hdv
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨hlw₁, hs₁⟩ := gDenC_iff.mp hg₁
  have hρ₁ : ρ₁ = PMap.empty := gSepC_deadP hd hs₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ H) := isVal_psub_valFormIn hlw₁ hH
  have hH' := hc δ γ ls PMap.empty hδ hg₁
  have hE' := (cC_effOf _ A ls δ _ ρ₂ hdv).mp (he δ γ ls ρ₂ hδ hg₂)
  show cC _ ls δ (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) H e)) ρ₂
  rw [psub_hndExpr]
  show cC _ ls δ (hndExpr n (E.map Prod.fst) (substAll γ H) (substAll γ e)) ρ₂
  refine (cC_effOf S R ls δ _ ρ₂ hS).mpr (ewp_fold (opTable_mono _) ?_)
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
  exact ewp_unfold (opTable_mono _) (ewp_handle_vals hS hn0 hnS hlen hVr hVc hE')
    ρf fρ ps hf hcf hT htg Al k

end BoCa.Fig16.LogRel.Core

end
