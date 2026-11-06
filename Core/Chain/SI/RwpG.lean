import Core.Chain.SI.HeapN
import Core.EffMachine

/-!
# `rwp` ending at any final term: `rwpG`

`wpG` (`Core/EffDefs.lean`) is `wpTS` with its run ending at any term and the postcondition over
that term; `ewpTS` is the least fixed point of `wpG` with the postcondition "a value in `Q`, or a
stop the table allows". `rwpG` is `wpG` at the step index, cut at runs as `rwp` is: every run of
`j < n` steps that reaches a configuration with no step meets the post-configuration there, at
`n − j`. A value and a stop (`perform`/`raise` under a context that does not catch it,
`opPlug_no_step`) are such configurations; at any other one the postcondition is `False` in every
use, which is safety.

`rwp_iff_rwpG`: `rwp` is `rwpG` at a postcondition over values, so `rwp`'s rules hold at
`rwpG` for value postconditions. `rwpG_bind`, `rwpG_frame` and `rwpG_step` are `rwp_bind`,
`rwp_frame` and a pure step at any final term: the proofs never inspect the term the run ends
at, as `wpG_bind`'s does not.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-- A configuration with no step. -/
def Final (μ : Heap) (e : Expr) : Prop := ∀ μ' e', ¬ Step1 (ℍ := ℍ) μ e μ' e'

/-- A postcondition over terms, at a step index. -/
abbrev PostG : Type := Nat → List SRec → Expr → WProp

/-- `EndOK` at a term. -/
def EndOKG (Φ : LocFam) (Q : PostG) (k : Nat) (ls : List SRec) (ρ ρf : WRes)
    (ps : List FrameRec) (μ' : Heap) (t : Expr) : Prop :=
  ∃ (ρ' ρp fρ' fρ'p π : WRes) (ps' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
    ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
    ResU.CompS ρ' ρp π ∧ UpdVN Φ k ρ π ∧ NoOwn ρp ∧
    TWNC fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
    (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q k ls' t ρ'

/-- **`wpG` at the step index.** -/
def rwpG (Φ : LocFam) (Q : PostG) (n : Nat) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TWNC fρ ps (rsOf ls) → Tagged fρ ps ls →
    ImmTieL Φ.imm ls → ResU.Lower fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' → Final (ℍ := ℍ) μ' e' →
      EndOKG Φ Q (n - j) ls ρ ρf ps μ' e'

/-- The postcondition over terms that admits only values. -/
def valPostN (Q : PostN) : PostG := fun k ls t ρ => ∃ v : Val, t = v.1 ∧ Q k ls v ρ

/-! ### `rwp` is `rwpG` at a value postcondition -/

theorem final_val (μ : Heap) (v : Val) : Final (ℍ := ℍ) μ v.1 :=
  fun _ _ h => BoLo.no_step_val h

theorem EndOK.toG {Φ : LocFam} {Q : PostN} {k : Nat} {ls : List SRec} {ρ ρf : WRes}
    {ps : List FrameRec} {μ' : Heap} {v : Val} (h : EndOK Φ Q k ls ρ ρf ps μ' v) :
    EndOKG Φ (valPostN Q) k ls ρ ρf ps μ' v.1 := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    v, rfl, h₁₃⟩

theorem EndOKG.ofVal {Φ : LocFam} {Q : PostN} {k : Nat} {ls : List SRec} {ρ ρf : WRes}
    {ps : List FrameRec} {μ' : Heap} {v : Val}
    (h : EndOKG Φ (valPostN Q) k ls ρ ρf ps μ' v.1) : EndOK Φ Q k ls ρ ρf ps μ' v := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    w, hw, h₁₃⟩ := h
  obtain rfl : v = w := Subtype.ext hw
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩

/-- **`rwp` is `rwpG` at a postcondition over values.** -/
theorem rwp_iff_rwpG {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} : rwp (ℍ := ℍ) Φ Q n ls e ρ ↔ rwpG (ℍ := ℍ) Φ (valPostN Q) n ls e ρ := by
  classical
  constructor
  · intro h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
    obtain ⟨hval, hprog⟩ := h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
    by_cases hv : IsVal e'
    · exact (hval ⟨e', hv⟩ rfl).toG
    · obtain ⟨μ'', e'', hs⟩ := hprog hv
      exact absurd hs (hfin μ'' e'')
  · intro h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
    refine ⟨fun v hv => ?_, fun hnv => ?_⟩
    · subst hv
      exact (h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' v.1 hj hrun (final_val μ' v)).ofVal
    · by_contra hno
      have hfin : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hno ⟨μ'', e'', hs⟩
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, w, hw, -⟩ :=
        h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
      exact hnv (hw ▸ w.2)

/-! ### Downward closure and monotonicity -/

/-- A postcondition over terms is downward closed. -/
def PostG.Down (Q : PostG) : Prop := ∀ n ls t ρ, Q (n + 1) ls t ρ → Q n ls t ρ

theorem PostG.Down.le {Q : PostG} (hQ : Q.Down) {m k : Nat} (h : m ≤ k) :
    ∀ ls t ρ, Q k ls t ρ → Q m ls t ρ := by
  induction h with
  | refl => exact fun _ _ _ x => x
  | step _ ih => exact fun ls t ρ x => ih ls t ρ (hQ _ _ _ _ x)

theorem EndOKG.mono {Φ : LocFam} {P Q : PostG} {k k' : Nat} (hΦ : Φ.Down) (hk : k' ≤ k)
    {t : Expr} (hPQ : ∀ ls ρ, P k ls t ρ → Q k' ls t ρ) {ls : List SRec} {ρ ρf : WRes}
    {ps : List FrameRec} {μ' : Heap} (h : EndOKG Φ P k ls ρ ρf ps μ' t) :
    EndOKG Φ Q k' ls ρ ρf ps μ' t := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇.down hΦ hk, h₈, h₉, h₁₀,
    h₁₁, h₁₂, hPQ _ _ h₁₃⟩

/-- **`rwpG` is downward closed.** -/
theorem rwpG_le {Φ : LocFam} (hΦ : Φ.Down) {Q : PostG} (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) :
    rwpG (ℍ := ℍ) Φ Q m ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  exact (h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' (by omega) hrun hfin).mono hΦ (by omega)
    (fun _ _ x => hQ.le (by omega) _ _ _ x)

theorem rwpG_mono {Φ : LocFam} {P Q : PostG} (hPQ : ∀ n ls t ρ, P n ls t ρ → Q n ls t ρ)
    {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ P n ls e ρ) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    hPQ _ _ _ _ h₁₃⟩

/-- **A final term in the postcondition** (`wpG_here` at the index): a term with no step at any
memory. -/
theorem rwpG_here {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (hfin : ∀ μ, Final (ℍ := ℍ) μ e) (h : Q n ls e ρ) : rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun _
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  have hvρ : ResU.Valid ρ := (hash_valid hf).2
  refine ⟨ρ, PMap.empty, fρ, fρ, ρ, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), ResU.comp_empty_right _, hl,
    ResU.comp_empty_right _, UpdVN.refl Φ _ hvρ, noOwn_empty, hT, htg, fun _ => Iff.rfl,
    fun _ => Iff.rfl, ?_⟩
  simpa using h

/-- **One step that is its configuration's only one at every memory, and keeps the memory**:
the index pays for it. -/
theorem rwpG_step {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e e' : Expr} {ρ : WRes}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : rwpG (ℍ := ℍ) Φ Q n ls e' ρ) :
    rwpG (ℍ := ℍ) Φ Q (n + 1) ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet μ).1 (hfin μ e')
  | @more j' μ μ₁ μ' e e₁ E hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet μ).2 _ _ hs
      have := h ρf fρ ps _ hf hc hT htg hI hl hfd j' μ' E (by omega) t hfin
      rwa [show n + 1 - (j' + 1) = n - j' by omega]

/-! ### Bind -/

/-- `rwp_compose` at any final term. -/
theorem rwpG_compose {Φ : LocFam} (hΦ : Φ.Down) {Q : PostG} (K : Kont) {k₁ : Nat}
    {ls : List SRec} (hI : ImmTieL Φ.imm ls) {ρ ρf : WRes} {ps : List FrameRec} {μ₁ : Heap} {t : Expr}
    (hend : EndOKG Φ (fun k ls' t => rwpG (ℍ := ℍ) Φ Q k ls' (K.plug t)) k₁ ls ρ ρf ps μ₁ t)
    (hfd₁ : FinDom μ₁) {j₂ : Nat} {μ' : Heap} {E : Expr} (hj : j₂ < k₁)
    (hrun : StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E) (hfin : Final (ℍ := ℍ) μ' E) :
    EndOKG Φ Q (k₁ - j₂) ls ρ ρf ps μ' E := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₆, h₇, h₉, hA, hB, hT', htg', hps',
    hls', hC⟩ := hend
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  obtain ⟨ρ'', ρpp, Y'', Y''p, π'', ps'', ls'', k₁', k₂, k₃, k₆, k₇, k₉, kA, kB, kT, ktg, kps,
    kls, kC⟩ := hC z fρ'p ps' μ₁ hz hzY hT' htg' (hI.perm hls') h₇ hfd₁ j₂ μ' E hj hrun hfin
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hfz (ResU.hash_symm k₁')
  obtain ⟨F, hF, hFp⟩ := compS_exch hfz k₂
  obtain ⟨ZZ, hZZ, hZF⟩ := (hash_shift ρpp ρp F).mp ⟨Y'', ResU.CompS.comm hFp, k₃⟩
  have hZZ' : ResU.CompS ρp ρpp ZZ := ResU.CompS.comm hZZ
  obtain ⟨ZZ₀, hZZ₀, hFZ₀⟩ := compS_reassoc hFp k₆
  have hFZ : ResU.CompS F ZZ Y''p := by
    rwa [ResU.CompS.functional hZZ₀ hZZ'] at hFZ₀
  obtain ⟨-, hpρ'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hfz k₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm k₃)
  obtain ⟨π₀, hπ₀, hpπ₀⟩ := (hash_shift ρp ρ'' ρpp).mpr ⟨d, hd, hdp⟩
  have hpπ : ResU.Hash ρp π'' := by rwa [ResU.CompS.functional hπ₀ k₉] at hpπ₀
  obtain ⟨Yn, hYn, -⟩ := hpπ.2
  obtain ⟨ZZ₁, hZZ₁, hρ''Z₀⟩ := compS_lcomm k₉ hYn
  have hρ''Z : ResU.CompS ρ'' ZZ Yn := by
    rwa [ResU.CompS.functional hZZ₁ hZZ'] at hρ''Z₀
  refine ⟨ρ'', ZZ, F, Y''p, Yn, ps'', ls'', ResU.hash_symm hfρ'', hF, hZF, hFZ, k₇, hρ''Z,
    ?_, noOwn_compS hZZ' hB kB, kT, ktg, fun p => (kps p).trans (hps' p),
    fun x => (kls x).trans (hls' x), kC⟩
  exact UpdVN.trans hΦ (Nat.sub_le k₁ j₂) hA
    (updVN_frame (ResU.CompS.comm h₉) hYn (ResU.hash_symm hpρ') hpπ kA)

/-- **Bind at any final term** (`wpG_bind` at the index): a run of `e` to a final term `t`, then
the continuation from `K[t]`. -/
theorem rwpG_bind {Φ : LocFam} (hΦ : Φ.Down) {Q : PostG} (K : Kont) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (hw : rwpG (ℍ := ℍ) Φ (fun k ls' t => rwpG (ℍ := ℍ) Φ Q k ls' (K.plug t)) n ls e ρ) :
    rwpG (ℍ := ℍ) Φ Q n ls (K.plug e) ρ := by
  classical
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' E hj hrun hfin
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · -- the run stayed inside `K`: `e'` is final, since a step of it is one of `K[e']`
    have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    have h := rwpG_compose hΦ K hI (hw ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun' hfin')
      (fd_stepsN hrun' hfd) (j₂ := 0) (by omega) (.refl _ _) hfin
    simpa using h
  · have h := rwpG_compose hΦ K hI
      (hw ρf fρ ps μ hf hc hT htg hI hl hfd j₁ μ₁ t (by omega) hrun₁ hirr)
      (fd_stepsN hrun₁ hfd) (j₂ := j₂) (by omega) hrun₂ hfin
    rwa [show n - j₁ - j₂ = n - j by omega] at h

/-! ### The frame -/

/-- **The frame at any final term** (`rwp_frame`, `wpG_ramify` with a frame that holds at every
index). -/
theorem rwpG_frame {Φ : LocFam} {P : PostG} (R : List SRec → WProp)
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ₁ ρ₂ ρ : WRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hwp : rwpG (ℍ := ℍ) Φ P n ls e ρ₁) (hR₂ : R ls ρ₂) :
    rwpG (ℍ := ℍ) Φ (fun k ls' t => P k ls' t ⋆ R ls') n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  obtain ⟨ρ', ρp, Y', Y'p, π', ps', ls', g₁, g₂, g₃, g₆, g₇, g₉, gA, gB, gT, gtg, gps,
    gls, gC⟩ := hwp y fρ ps μ hy₁ hyfρ hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  obtain ⟨W₀, hW₀, hWf₀⟩ := (hash_shift ρ' ρ₂ ρf).mp ⟨y, ResU.CompS.comm hy, g₁⟩
  have hWf : ResU.Hash W ρf := by
    rwa [ResU.CompS.functional (ResU.CompS.comm hW₀) hW] at hWf₀
  obtain ⟨-, hWp⟩ := ResU.Hash.split hfW (ResU.hash_symm g₃)
  obtain ⟨πW, hπW, h₂π₀⟩ := (hash_shift ρ₂ ρ' ρp).mpr ⟨W, hW, hWp⟩
  have h₂π : ResU.Hash ρ₂ π' := by rwa [ResU.CompS.functional hπW g₉] at h₂π₀
  obtain ⟨πn, hπn, -⟩ := h₂π.2
  obtain ⟨Wn, hWn, hWπ₀⟩ := compS_reassoc' g₉ hπn
  have hWπ : ResU.CompS W ρp πn := by
    rwa [ResU.CompS.functional hWn hW] at hWπ₀
  refine ⟨W, ρp, Y', Y'p, πn, ps', ls', hWf, hfW, g₃, g₆, g₇, hWπ, ?_, gB, gT, gtg, gps,
    gls, ρ', ρ₂, ResU.CompS.comm hW, gC, hR ls ls' gls ρ₂ hR₂⟩
  exact updVN_frame (ResU.CompS.comm hcρ) hπn
    ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, (hash_valid hf).2⟩ h₂π gA

/-! ### Safety -/

/-- **Safety at any final term**: a closed term in `rwpG` at the empty world at every index,
whose postcondition holds only at values, never gets stuck. -/
theorem rwpG_safe {Φ : LocFam} (hΦI : ImmTieL Φ.imm []) {Q : PostG} {e : Expr}
    (hQ : ∀ k ls t ρ, Q k ls t ρ → IsVal t)
    (hall : ∀ n, rwpG (ℍ := ℍ) Φ Q n [] e (PMap.empty : WRes)) {j : Nat} {μ' : Heap} {e' : Expr}
    (hrun : StepsN (ℍ := ℍ) j (fun _ => none) e μ' e') :
    IsVal e' ∨ ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'' := by
  classical
  by_cases hs : ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e''
  · exact .inr hs
  · have hfin : Final (ℍ := ℍ) μ' e' := fun μ'' e'' h => hs ⟨μ'', e'', h⟩
    have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
    have h := hall (j + 1) PMap.empty PMap.empty [] (fun _ => none)
      Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TWNC.empty htg hΦI Fig16.BoLo.lower_empty
      fd_empty j μ' e' (by omega) hrun hfin
    obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, hq⟩ := h
    exact .inl (hQ _ _ _ _ hq)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
