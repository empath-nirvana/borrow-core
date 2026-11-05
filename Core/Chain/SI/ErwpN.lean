import Core.Chain.SI.RwpG

/-!
# The effectful `wp` at the step index over Core's worlds: `erwp`

`ewpTS ls e Π Q` (`Core/EffDefs.lean`) is the least fixed point of `wpG` at the postcondition
"a value in `Q`, or a stop the table `Π` allows, owing its continuations `ewpTS`". Stage 1's `ewp`
(`SI/Ewp.lean`) replaces the least fixed point by the step index: a stop's continuation is owed at
every later index. `erwp` is the two together: `rwpG` (`wpG` at the index) at the postcondition
"a value in `Q`, or a stop the table allows at the index `k` the run left, owing its continuations
`erwp` at every `k′ < k`". The recursion is on the index, so no fixed point is taken, and a
handler is proved by induction on the index (`erwp_handle`), as stage 1's `ewp_handle`.

The tables are `Core`'s with an index: `OpEntN` is `OpEnt` with `PA`, `PB` and the cancel
obligation read at an index; the continuation's share (`contShareN`) is owed at every answer in
`PB` at every `k′ < k`, the step-indexed `−∗` of stage 1.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

/-! ### Tables at the index -/

/-- `OpEnt` at the step index. -/
structure OpEntN where
  q : Qual
  abort : Bool
  PA : Nat → List SRec → Val → WProp
  PB : Nat → List SRec → Val → WProp
  fin : Option (Nat → List SRec → Expr → WProp)
  /-- The worlds the continuation may be resumed at: `ls′` from the stop's `ls`, at the
  continuation's share. `Ext` is `contShare`'s; an operation performed under a live lend has
  `extF` (`SI/ExtF.lean`), which every lend's fold keeps. -/
  wc : List SRec → List SRec → WRes → Prop

abbrev OpTabN := UInt32 → UInt32 → Option OpEntN

/-- What a stop owes, at every index and list. -/
abbrev ContN := Nat → List SRec → Expr → WProp

/-- A protocol table at the index: the stop at `t`, at the index `k`, owing `Ψ`. -/
abbrev TableN := Nat → List SRec → Expr → ContN → WProp

/-- `cancelOK` at the index. -/
def cancelOKN (en : OpEntN) (k : Nat) (ls : List SRec) (K : Kont) : WProp := fun ρ =>
  ∀ P, en.fin = some P → P k ls (K.dead.plug (raiseE (.val (cancelVal none)))) ρ

/-- `contShare` at the index: resumed at every answer in `PB` at every `k′ < k`, at every world
the entry's `wc` allows. -/
def contShareN (en : OpEntN) (k : Nat) (ls : List SRec) (K : Kont) (Ψ : ContN) : WProp :=
  fun ρ =>
    (en.q = .unr → ρ = PMap.empty) ∧
    ∀ ls', en.wc ls ls' ρ →
      (∀ k', k' < k → ∀ w : Val, (en.PB k' ls' w ─⋆ Ψ k' ls' (K.plug (.val w))) ρ) ∧
      (en.q ≠ .lin → cancelOKN en k ls' K ρ)

/-- `performStop` at the index. -/
def performStopN (T : OpTabN) : TableN := fun k ls t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntN) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆ (en.PA k ls v ⋆ contShareN en k ls K Ψ)

/-- An abortive stop at the index (`opTable`'s second disjunct). -/
def raiseStopN (T : OpTabN) : TableN := fun k ls t _ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntN) =>
      ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
        T n i = some en ∧ en.abort = true⌝ ⋆
        ((fun ρ => en.PA k ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ)

/-- `opTable` at the index. -/
def opTableN (T : OpTabN) : TableN := fun k ls t Ψ =>
  BoLo.or (performStopN T k ls t Ψ) (raiseStopN T k ls t Ψ)

/-- A table reads what is owed only below the index it stops at. -/
def TableN.Local (Tb : TableN) : Prop :=
  ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
    Tb k ls t Ψ ρ → Tb k ls t Ψ' ρ

/-- A table is downward closed in its index. -/
def TableN.Down (Tb : TableN) : Prop :=
  ∀ k ls t Ψ ρ, Tb (k + 1) ls t Ψ ρ → Tb k ls t Ψ ρ

/-- An operation table's predicates read at the current index are downward closed. -/
structure OpTabN.Down (T : OpTabN) : Prop where
  pa : ∀ n i en, T n i = some en → ∀ k ls v ρ, en.PA (k + 1) ls v ρ → en.PA k ls v ρ
  fin : ∀ n i en P, T n i = some en → en.fin = some P → ∀ k ls e ρ, P (k + 1) ls e ρ → P k ls e ρ
  /-- The world condition passes to a part of the share (`Ext.left`). -/
  wcl : ∀ n i en, T n i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
    en.wc ls ls' ρ → en.wc ls ls' ρ₁

theorem opTableN_local (T : OpTabN) : (opTableN T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, fun ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont ls' he).2⟩⟩⟩
  · exact Or.inr h

theorem opTableN_down {T : OpTabN} (hT : T.Down) : (opTableN T).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, hu, fun ls' he =>
      ⟨fun k' hk => (hcont ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP _ _ _ _ ((hcont ls' he).2 hq P hP)⟩⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρn, hc, ⟨hA, hnA⟩, hnn⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩
      ⟨ρa, ρn, hc, ⟨hT.pa _ _ _ h₃ _ _ _ _ hA, hnA⟩, hnn⟩⟩

/-! ### The relation -/

/-- A value in `Q`, or a stop the table allows. -/
def erwpPost (Tb : TableN) (Q : PostN) (Ψ : ContN) : PostG :=
  fun k ls t => BoLo.or (valPostN Q k ls t) (Tb k ls t Ψ)

/-- **The effectful `wp` at the step index.** -/
def erwp (Φ : LocFam) (Tb : TableN) (Q : PostN) : Nat → List SRec → Expr → WProp
  | n, ls, e => rwpG (ℍ := ℍ) Φ (erwpPost Tb Q (fun k' ls' e' =>
      if _h : k' < n then erwp Φ Tb Q k' ls' e' else fun _ => False)) n ls e
termination_by n => n

/-- What `erwp` at `N` owes below it. -/
def erwpC (Φ : LocFam) (Tb : TableN) (Q : PostN) (N : Nat) : ContN := fun k' ls' e' =>
  if k' < N then erwp (ℍ := ℍ) Φ Tb Q k' ls' e' else fun _ => False

theorem erwp_eq (Φ : LocFam) (Tb : TableN) (Q : PostN) (n : Nat) (ls : List SRec) (e : Expr) :
    erwp (ℍ := ℍ) Φ Tb Q n ls e =
      rwpG (ℍ := ℍ) Φ (erwpPost Tb Q (erwpC (ℍ := ℍ) Φ Tb Q n)) n ls e := by
  rw [erwp]
  congr 1

/-- `rwpG_mono` reading the postcondition at the indices the runs leave, `≤ n`. -/
theorem rwpG_mono_le {Φ : LocFam} {P Q : PostG} {n : Nat}
    (hPQ : ∀ k, k ≤ n → ∀ ls t ρ, P k ls t ρ → Q k ls t ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ P n ls e ρ) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    hPQ _ (by omega) _ _ _ h₁₃⟩

/-- `erwp` at `n`, its continuations read at any `N ≥ n`. -/
theorem erwp_unfold_at {Φ : LocFam} {Tb : TableN} (hTb : Tb.Local) {Q : PostN} {n N : Nat}
    (hnN : n ≤ N) {ls : List SRec} {e : Expr} {ρ : WRes} (h : erwp (ℍ := ℍ) Φ Tb Q n ls e ρ) :
    rwpG (ℍ := ℍ) Φ (erwpPost Tb Q (erwpC (ℍ := ℍ) Φ Tb Q N)) n ls e ρ := by
  rw [erwp_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb k ls' t _ _ ρ' (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

/-- …and back. -/
theorem erwp_fold_at {Φ : LocFam} {Tb : TableN} (hTb : Tb.Local) {Q : PostN} {n N : Nat}
    (hnN : n ≤ N) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) Φ (erwpPost Tb Q (erwpC (ℍ := ℍ) Φ Tb Q N)) n ls e ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp_eq]
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb k ls' t _ _ ρ' (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

/-! ### Steps, values and downward closure -/

/-- At the index `0` every run is cut. -/
theorem rwpG_zero {Φ : LocFam} {Q : PostG} {ls : List SRec} {e : Expr} {ρ : WRes} :
    rwpG (ℍ := ℍ) Φ Q 0 ls e ρ := by
  intro _ _ _ _ _ _ _ _ _ _ j _ _ hj
  omega

theorem erwp_zero {Φ : LocFam} {Tb : TableN} {Q : PostN} {ls : List SRec} {e : Expr}
    {ρ : WRes} : erwp (ℍ := ℍ) Φ Tb Q 0 ls e ρ := by
  rw [erwp_eq]; exact rwpG_zero

/-- **A step that is its configuration's only one, for free**: the run from `e` is one step and
a run from `e′`, which `rwpG` at `n` covers at a higher index left. -/
theorem rwpG_det {Φ : LocFam} (hΦ : Φ.Down) {Q : PostG} (hQ : Q.Down) {n : Nat}
    {ls : List SRec} {e e' : Expr} {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : rwpG (ℍ := ℍ) Φ Q n ls e' ρ) : rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet _).1 (hfin _ e')
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ hs
      exact (h ρf fρ ps _ hf hc hT htg hl hfd j' μ' E (by omega) t hfin).mono hΦ (by omega)
        (fun _ _ x => hQ.le (by omega) _ _ _ x)

/-- `erwp`'s postcondition is downward closed. -/
theorem erwpPost_down {Tb : TableN} (hTb : Tb.Down) {Q : PostN} (hQ : Q.Down) (Ψ : ContN) :
    (erwpPost Tb Q Ψ).Down := by
  intro k ls t ρ h
  rcases h with ⟨v, hv, hq⟩ | h
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ hq⟩
  · exact Or.inr (hTb _ _ _ _ _ h)

/-- **`erwp` is downward closed.** -/
theorem erwp_le {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTb : Tb.Local) (hTd : Tb.Down)
    {Q : PostN} (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ Tb Q n ls e ρ) : erwp (ℍ := ℍ) Φ Tb Q m ls e ρ :=
  erwp_fold_at hTb hmn (rwpG_le hΦ (erwpPost_down hTd hQ _) hmn (erwp_unfold_at hTb le_rfl h))

/-- A deterministic step in front of an `erwp`, for free. -/
theorem erwp_det {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTd : Tb.Down) {Q : PostN}
    (hQ : Q.Down) {n : Nat} {ls : List SRec} {e e' : Expr} {ρ : WRes}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : erwp (ℍ := ℍ) Φ Tb Q n ls e' ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp_eq] at h ⊢
  exact rwpG_det hΦ (erwpPost_down hTd hQ _) hdet h

/-- A value in the postcondition. -/
theorem erwp_val {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec} {v : Val}
    {ρ : WRes} (h : Q n ls v ρ) : erwp (ℍ := ℍ) Φ Tb Q n ls v.1 ρ := by
  rw [erwp_eq]
  exact rwpG_here (fun μ => final_val μ v) (Or.inl ⟨v, rfl, h⟩)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
