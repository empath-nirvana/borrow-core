import Core.Chain.SI.Capture
import Core.Chain.SI.HandleN

/-!
# `erwp` with no garbage: `erwp0`

`rwpG0` is `rwpG` (`SI/RwpG.lean`) with the post-configuration's garbage `ρ⁺` fixed to `∅`: every
cell a run holds at its end is in the postcondition's resource. Every other conjunct, `↭` among
them, is `rwpG`'s. `rwpG_of_rwpG0` reads `rwpG0` as `rwpG` at `ρ⁺ = ∅`, so `[TR]` 6.29, 6.38 and
6.39 apply to its post-configurations verbatim.

A lend whose body runs across stops ends, in `SI/CaptureScope.lean`, in a segment other than the
one that opened it, so the lender reads the borrowed run's post-configuration at the end of each
segment and keeps the resources the run holds there; a body at `erwp0` leaves nothing behind
that the lender would not see.

`crwpG_of_rwpG0_frame` runs an `rwpG0` computation under a resource `R` the caller keeps beside
it (the lender's copy of the borrow), and reads `↭` of the whole by 6.48 (`updVN_frame`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-- `EndOKG` with no garbage. -/
def EndOKG0 (Φ : LocFam) (Q : PostG) (k : Nat) (ls : List SRec) (ρ ρf : WRes)
    (ps : List FrameRec) (μ' : Heap) (t : Expr) : Prop :=
  ∃ (ρ' fρ' : WRes) (ps' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Lower fρ' μ' ∧ UpdVN Φ k ρ ρ' ∧
    TWNC fρ' ps' (rsOf ls') ∧ Tagged fρ' ps' ls' ∧
    (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q k ls' t ρ'

/-- **`rwpG` with no garbage.** -/
def rwpG0 (Φ : LocFam) (Q : PostG) (n : Nat) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TWNC fρ ps (rsOf ls) → Tagged fρ ps ls →
    ImmTieL Φ.imm ls → ResU.Lower fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' → Final (ℍ := ℍ) μ' e' →
      EndOKG0 Φ Q (n - j) ls ρ ρf ps μ' e'

theorem EndOKG0.toG {Φ : LocFam} {Q : PostG} {k : Nat} {ls : List SRec} {ρ ρf : WRes}
    {ps : List FrameRec} {μ' : Heap} {t : Expr} (h : EndOKG0 Φ Q k ls ρ ρf ps μ' t) :
    EndOKG Φ Q k ls ρ ρf ps μ' t := by
  obtain ⟨ρ', fρ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h
  have hv : ResU.Valid fρ' := by obtain ⟨σ, hσ, -⟩ := h₃; exact ⟨σ, hσ⟩
  exact ⟨ρ', PMap.empty, fρ', fρ', ρ', ps', ls', h₁, h₂,
    ResU.hash_symm (ResU.hash_empty_right hv), ResU.comp_empty_right _, h₃,
    ResU.comp_empty_right _, h₄, noOwn_empty, h₅, h₆, h₇, h₈, h₉⟩

/-- `rwpG0` is `rwpG` at `ρ⁺ = ∅`. -/
theorem rwpG_of_rwpG0 {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwpG0 (ℍ := ℍ) Φ Q n ls e ρ) : rwpG (ℍ := ℍ) Φ Q n ls e ρ :=
  fun ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin =>
    (h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin).toG

theorem EndOKG0.mono {Φ : LocFam} {P Q : PostG} {k k' : Nat} (hΦ : Φ.Down) (hk : k' ≤ k)
    {t : Expr} (hPQ : ∀ ls ρ, P k ls t ρ → Q k' ls t ρ) {ls : List SRec} {ρ ρf : WRes}
    {ps : List FrameRec} {μ' : Heap} (h : EndOKG0 Φ P k ls ρ ρf ps μ' t) :
    EndOKG0 Φ Q k' ls ρ ρf ps μ' t := by
  obtain ⟨ρ', fρ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := h
  exact ⟨ρ', fρ', ps', ls', h₁, h₂, h₃, h₄.down hΦ hk, h₅, h₆, h₇, h₈, hPQ _ _ h₉⟩

theorem rwpG0_mono_le {Φ : LocFam} {P Q : PostG} {n : Nat}
    (hPQ : ∀ k, k ≤ n → ∀ ls t ρ, P k ls t ρ → Q k ls t ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : rwpG0 (ℍ := ℍ) Φ P n ls e ρ) :
    rwpG0 (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', fρ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ :=
    h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', fρ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, hPQ _ (by omega) _ _ _ h₉⟩

theorem rwpG0_here {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (hfin : ∀ μ, Final (ℍ := ℍ) μ e) (h : Q n ls e ρ) : rwpG0 (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun _
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  exact ⟨ρ, fρ, ps, ls, ResU.hash_symm hf, hc, hl, UpdVN.refl Φ _ (hash_valid hf).2, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, by simpa using h⟩

theorem rwpG0_det {Φ : LocFam} (hΦ : Φ.Down) {Q : PostG} (hQ : Q.Down) {n : Nat}
    {ls : List SRec} {e e' : Expr} {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : rwpG0 (ℍ := ℍ) Φ Q n ls e' ρ) : rwpG0 (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet _).1 (hfin _ e')
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ hs
      exact (h ρf fρ ps _ hf hc hT htg hI hl hfd j' μ' E (by omega) t hfin).mono hΦ (by omega)
        (fun _ _ x => hQ.le (by omega) _ _ _ x)

/-! ### The effectful relation -/

/-- **`erwp` with no garbage.** -/
def erwp0 (Φ : LocFam) (Tb : TableN) (Q : PostN) : Nat → List SRec → Expr → WProp
  | n, ls, e => rwpG0 (ℍ := ℍ) Φ (erwpPost Tb Q (fun k' ls' e' =>
      if _h : k' < n then erwp0 Φ Tb Q k' ls' e' else fun _ => False)) n ls e
termination_by n => n

/-- What `erwp0` at `N` owes below it. -/
def erwp0C (Φ : LocFam) (Tb : TableN) (Q : PostN) (N : Nat) : ContN := fun k' ls' e' =>
  if k' < N then erwp0 (ℍ := ℍ) Φ Tb Q k' ls' e' else fun _ => False

theorem erwp0_eq (Φ : LocFam) (Tb : TableN) (Q : PostN) (n : Nat) (ls : List SRec) (e : Expr) :
    erwp0 (ℍ := ℍ) Φ Tb Q n ls e =
      rwpG0 (ℍ := ℍ) Φ (erwpPost Tb Q (erwp0C (ℍ := ℍ) Φ Tb Q n)) n ls e := by
  rw [erwp0]
  congr 1

theorem erwp0_unfold_at {Φ : LocFam} {Tb : TableN} (hTb : Tb.Local) {Q : PostN} {n N : Nat}
    (hnN : n ≤ N) {ls : List SRec} {e : Expr} {ρ : WRes} (h : erwp0 (ℍ := ℍ) Φ Tb Q n ls e ρ) :
    rwpG0 (ℍ := ℍ) Φ (erwpPost Tb Q (erwp0C (ℍ := ℍ) Φ Tb Q N)) n ls e ρ := by
  rw [erwp0_eq] at h
  refine rwpG0_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb k ls' t _ _ ρ' (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwp0C, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem erwp0_fold_at {Φ : LocFam} {Tb : TableN} (hTb : Tb.Local) {Q : PostN} {n N : Nat}
    (hnN : n ≤ N) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwpG0 (ℍ := ℍ) Φ (erwpPost Tb Q (erwp0C (ℍ := ℍ) Φ Tb Q N)) n ls e ρ) :
    erwp0 (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp0_eq]
  refine rwpG0_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb k ls' t _ _ ρ' (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwp0C, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem erwp0_val {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec} {v : Val}
    {ρ : WRes} (h : Q n ls v ρ) : erwp0 (ℍ := ℍ) Φ Tb Q n ls v.1 ρ := by
  rw [erwp0_eq]
  exact rwpG0_here (fun μ => final_val μ v) (Or.inl ⟨v, rfl, h⟩)

theorem erwp0_det {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTd : Tb.Down) {Q : PostN}
    (hQ : Q.Down) {n : Nat} {ls : List SRec} {e e' : Expr} {ρ : WRes}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : erwp0 (ℍ := ℍ) Φ Tb Q n ls e' ρ) :
    erwp0 (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp0_eq] at h ⊢
  exact rwpG0_det hΦ (erwpPost_down hTd hQ _) hdet h

/-- **A stop at a must-resume operation**, at `erwp0`. -/
theorem erwp0_perform {Φ : LocFam} {T : OpTabN} {Q : PostN} (K : Kont) {m i : UInt32} {v : Val}
    {en : OpEntN} (hK : K.HasHnd m = false) (hT : T m i = some en) (ha : en.abort = false)
    (hq : en.q = .lin) {n : Nat} {ls : List SRec} {ρa ρk ρ : WRes} (hc : ResU.CompS ρa ρk ρ)
    (hA : en.PA n ls v ρa)
    (hk : ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB k' ls' w ─⋆ erwp0 (ℍ := ℍ) Φ (opTableN T) Q k' ls' (K.plug (.val w))) ρk) :
    erwp0 (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwp0_eq]
  refine rwpG0_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr (Or.inl
    ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk, hc, hA,
      fun hu => absurd (hq.symm.trans hu) (by simp), fun ls' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
        fun hq' => absurd hq hq'⟩⟩⟩))
  simp only [erwp0C, hk', if_true]
  exact hk ls' he k' hk' w τ₁ τ₂ hB hcτ

/-! ### Under a kept resource, at `crwpG` -/

/-- **An `rwpG0` run under a resource the caller keeps beside it.** The run of `e` from `ρ_in`,
the caller holding `R` too: at every final term the run's resource `π` in `Q`, the whole
`π ● R`, and `ρ_in ● R ↭ π ● R` (6.48). The records and list members are kept. -/
theorem crwpG_of_rwpG0_frame {Φ : LocFam} (hΦI : Φ.imm = []) {F : WRes → Prop} {Q : PostG}
    {n : Nat} {ls : List SRec} {O : List FrameRec} {e : Expr} {ρin R ρo : WRes}
    (h : rwpG0 (ℍ := ℍ) Φ Q n ls e ρin) (hc : ResU.CompS ρin R ρo) :
    crwpG (ℍ := ℍ) F (fun k ls' O' t ρ' => O' = O ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧
      ∃ π, Q k ls' t π ∧ ResU.CompS π R ρ' ∧ UpdVN Φ k ρo ρ') n ls O e ρo := by
  intro ρf fρ ps psF μ _ hf hcf hS hT htg hl hfd j μ' e' hj hrun hfin
  have hI : ImmTieL Φ.imm ls := ImmTieL.of_nil hΦI ls
  -- the inner run's frame: `ρ_f ● R`
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf R ρin).mp ⟨ρo, ResU.CompS.comm hc, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hc) hcf
  cases ResU.CompS.functional hy' hy
  obtain ⟨π, fρ', ps', ls', g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉⟩ :=
    h y fρ ps μ hy₁ hyfρ hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  have hvW : ResU.Valid fρ' := by obtain ⟨σ, hσ, -⟩ := g₃; exact ⟨σ, hσ⟩
  have hRπ : ResU.Hash R π := by
    obtain ⟨-, hR⟩ := ResU.Hash.split hy (ResU.hash_symm g₁)
    exact hR
  have hRin : ResU.Hash R ρin := ResU.hash_symm ⟨hc.1, ρo, hc, (hash_valid hf).2⟩
  refine ⟨W, fρ', ps', O, ls', ⟨(ResU.CompS.comm hfW).1, fρ', ResU.CompS.comm hfW, hvW⟩, hfW,
    g₃, ⟨fun p => (g₇ p).trans (hS.1 p), hS.2⟩, g₅, g₆, rfl, g₈, π, g₉, ResU.CompS.comm hW, ?_⟩
  exact updVN_frame (ResU.CompS.comm hc) hW hRin hRπ g₄

end BoCa.Fig16.LogRel.Core.Chain.SI

end
