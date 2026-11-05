import Core.Chain.SI.UpdN
import Core.Chain.SI.Frag
import Core.Chain.SI.TWNC
import Core.Wp

/-!
# Stage 2, step 2 (part): the step-indexed `wp` over Core's typed worlds

`rwp Φ Q n ls e ρ`: `wpTS` (`Core/World.lean`, `[TR]` p. 6's `wp`, row 5.33's repair) cut at the
step index `n`, as Ahmed's expression relation cuts a run: under every frame `ρ_f # ρ` whose
completion `ρ_f ● ρ` is a tagged `TWNC` world lowering to the memory `μ`, every run of `j < n`
steps either ends at a value, and then the printed post-configuration exists (`EndOK`, `wpTS`'s
conjuncts verbatim, with `ρ ↭ₙ₋ⱼ ρ′ ● ρ⁺` (`UpdVN`) for `ρ ↭ ρ′ ● ρ⁺` and the postcondition at
`n − j`), or the term it reached steps again.

The forced change is the run's quantifier: `wpTS` asks for one terminating run under every
allocator; at an index, every run shorter than the index is safe, and one that returns meets the
post-configuration. The post-configuration is checked where the printed `wp` checks it, at the
value, so a rule that opens a `mut` cell for a run and closes it at the end (`[TR]` 6.66) keeps
the printed proof's shape: nothing in between is asked to be a `↭`-image of the start.

`rwp_bind` is `[TR]` 6.135 by the printed proof (`wpTS_bind`): the continuation is instantiated at
the frame `ρ_f ● ρ⁺`, and the two updates are composed by `updVN_frame` (6.48) and `UpdVN.trans`
(6.49) down the index. `rwp_frame` is 6.146 with a frame that holds at every index
(`wpTS_ramify`), again through `updVN_frame`.

`Φ` is a parameter of a run. The Mut Frame (`[TR]` 6.65) proves the borrowed run at
`Φ[ℓ ↦ (A, F)]` and the lender's run at `Φ` (`rwp_M_frame`); the Mut Anti-Frame (6.66) writes the
cell back at the member of the index left (`rwp_M_antiFrame`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont)

/-! ### Runs of a counted length -/

/-- `j` machine steps. -/
inductive StepsN : Nat → Heap → Expr → Heap → Expr → Prop
  | refl (μ : Heap) (e : Expr) : StepsN 0 μ e μ e
  | more {j : Nat} {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1 (ℍ := ℍ) μ e μ₁ e₁) (t : StepsN j μ₁ e₁ μ' e') : StepsN (j + 1) μ e μ' e'

theorem fd_stepsN {j : Nat} {μ μ' : Heap} {e e' : Expr} (h : StepsN (ℍ := ℍ) j μ e μ' e')
    (hf : FinDom μ) : FinDom μ' := by
  induction h with
  | refl => exact hf
  | more h _ ih => exact ih (fd_step1 h hf)

/-- **Run splitting, counted** (`steps_plug_split`): a run of `K[e]` is `K` around a run of `e`,
or a run of `e` to a term that takes no step followed by a run from `K` around it. -/
theorem stepsN_plug_split (K : Kont) {j : Nat} {μ μ' : Heap} {e E : Expr}
    (hs : StepsN (ℍ := ℍ) j μ (K.plug e) μ' E) :
    (∃ e', E = K.plug e' ∧ StepsN (ℍ := ℍ) j μ e μ' e') ∨
    ∃ j₁ j₂ μ₁ t, j₁ + j₂ = j ∧ StepsN (ℍ := ℍ) j₁ μ e μ₁ t ∧
      (∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ₁ t μ₂ t₂) ∧ StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E := by
  generalize hE : K.plug e = E₀ at hs
  induction hs generalizing e with
  | refl μ E₀ => exact .inl ⟨e, hE.symm, .refl _ _⟩
  | @more j μ μ₁ μ' E₀ E₁ E' h t ih =>
      subst hE
      by_cases hst : ∃ μ₂ t₂, Step1 (ℍ := ℍ) μ e μ₂ t₂
      · obtain ⟨μ₂, t₂, h₂⟩ := hst
        obtain ⟨e', rfl, he'⟩ := step1_plug_of_step K h₂ h
        rcases ih rfl with ⟨e'', rfl, hs''⟩ | ⟨j₁, j₂, μ₃, t₃, hj, hs₃, hirr, hrest⟩
        · exact .inl ⟨e'', rfl, .more he' hs''⟩
        · exact .inr ⟨j₁ + 1, j₂, μ₃, t₃, by omega, .more he' hs₃, hirr, hrest⟩
      · simp only [not_exists] at hst
        exact .inr ⟨0, j + 1, μ, e, by omega, .refl _ _, hst, .more h t⟩

/-! ### The relation -/

/-- A postcondition at a step index, over the returned list. -/
abbrev PostN : Type := Nat → List SRec → Val → WProp

/-- `wpTS`'s post-configuration for a run of `ρ` under the frame `ρ_f` that returned `v` at the
memory `μ′`, at the index `k` left: every conjunct `wpTS` asks after its run, with `UpdVN Φ k`
for `↭` and `Q k`. -/
def EndOK (Φ : LocFam) (Q : PostN) (k : Nat) (ls : List SRec) (ρ ρf : WRes)
    (ps : List FrameRec) (μ' : Heap) (v : Val) : Prop :=
  ∃ (ρ' ρp fρ' fρ'p π : WRes) (ps' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
    ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
    ResU.CompS ρ' ρp π ∧ UpdVN Φ k ρ π ∧ NoOwn ρp ∧
    TWNC fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
    (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q k ls' v ρ'

/-- **The step-indexed `wp` at a tagged typed world.** -/
def rwp (Φ : LocFam) (Q : PostN) (n : Nat) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TWNC fρ ps (rsOf ls) → Tagged fρ ps ls →
    ResU.Lower fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' →
      (∀ v : Val, e' = v.1 → EndOK Φ Q (n - j) ls ρ ρf ps μ' v) ∧
      (¬ IsVal e' → ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'')

/-! ### Downward closure and monotonicity -/

/-- `UpdN` at an index gives it at every lower one. -/
theorem UpdN.down {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {ρ₁ ρ₂ : WRes}
    (h : UpdN Φ n ρ₁ ρ₂) : UpdN Φ n' ρ₁ ρ₂ := by
  have hr : ∀ l (ψ ψ' : CellU Loc Val), MutStep Φ n l ψ ψ' → MutStep Φ n' l ψ ψ' :=
    fun l ψ ψ' hs => hs.trans hΦ hn (MutStep.refl hs.2.1)
  refine ⟨h.1, fun l ψ hg hk => ?_, fun l ψ' hg hk => ?_⟩
  · obtain ⟨ψ', h', hs⟩ := h.2.1 l ψ hg hk
    exact ⟨ψ', h', hr l ψ ψ' hs⟩
  · obtain ⟨ψ, h', hs⟩ := h.2.2 l ψ' hg hk
    exact ⟨ψ, h', hr l ψ ψ' hs⟩

theorem UpdVN.down {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {ρ₁ ρ₂ : WRes}
    (h : UpdVN Φ n ρ₁ ρ₂) : UpdVN Φ n' ρ₁ ρ₂ :=
  ⟨h.1.down hΦ hn, h.2⟩

/-- A postcondition is downward closed. -/
def PostN.Down (Q : PostN) : Prop := ∀ n ls v ρ, Q (n + 1) ls v ρ → Q n ls v ρ

theorem PostN.Down.le {Q : PostN} (hQ : Q.Down) {m k : Nat} (h : m ≤ k) :
    ∀ ls v ρ, Q k ls v ρ → Q m ls v ρ := by
  induction h with
  | refl => exact fun _ _ _ x => x
  | step _ ih => exact fun ls v ρ x => ih ls v ρ (hQ _ _ _ _ x)

theorem EndOK.mono {Φ : LocFam} {P Q : PostN} {k k' : Nat} (hΦ : Φ.Down) (hk : k' ≤ k)
    (hPQ : ∀ ls v ρ, P k ls v ρ → Q k' ls v ρ) {ls : List SRec} {ρ ρf : WRes}
    {ps : List FrameRec} {μ' : Heap} {v : Val} (h : EndOK Φ P k ls ρ ρf ps μ' v) :
    EndOK Φ Q k' ls ρ ρf ps μ' v := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇.down hΦ hk, h₈, h₉, h₁₀,
    h₁₁, h₁₂, hPQ _ _ _ h₁₃⟩

/-- **`rwp` is downward closed.** -/
theorem rwp_le {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : rwp (ℍ := ℍ) Φ Q n ls e ρ) :
    rwp (ℍ := ℍ) Φ Q m ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun
  obtain ⟨hval, hprog⟩ := h ρf fρ ps μ hf hc hT htg hl hfd j μ' e' (by omega) hrun
  exact ⟨fun v hv => (hval v hv).mono hΦ (by omega) (fun _ _ _ x => hQ.le (by omega) _ _ _ x),
    hprog⟩

theorem rwp_mono {Φ : LocFam} {P Q : PostN} (hPQ : ∀ n ls v ρ, P n ls v ρ → Q n ls v ρ)
    {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes} (h : rwp (ℍ := ℍ) Φ P n ls e ρ) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun
  obtain ⟨hval, hprog⟩ := h ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun
  refine ⟨fun v hv => ?_, hprog⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := hval v hv
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    hPQ _ _ _ _ h₁₃⟩

/-- A value in the postcondition. -/
theorem rwp_val {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {v : Val}
    {ρ : WRes} (h : Q n ls v ρ) : rwp (ℍ := ℍ) Φ Q n ls v.1 ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun
  cases hrun with
  | more hs _ => exact absurd hs BoLo.no_step_val
  | refl =>
  refine ⟨fun w hw => ?_, fun hnv => absurd v.2 hnv⟩
  have hw' : w = v := Subtype.ext hw.symm
  subst hw'
  have hvρ : ResU.Valid ρ := (hash_valid hf).2
  refine ⟨ρ, PMap.empty, fρ, fρ, ρ, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), ResU.comp_empty_right _, hl,
    ResU.comp_empty_right _, UpdVN.refl Φ _ hvρ, noOwn_empty, hT, htg, fun _ => Iff.rfl,
    fun _ => Iff.rfl, ?_⟩
  simpa using h

/-! ### Bind: `[TR]` 6.135 by the printed proof -/

/-- The second half of bind: the continuation's `rwp`, held at the first run's end, instantiated
at the frame `ρ_f ● ρ⁺` (`wpTS_bind`'s H8), and the two post-configurations composed: the
updates by `updVN_frame` (6.48) and `UpdVN.trans` (6.49). -/
theorem rwp_compose {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (K : Kont) {k₁ : Nat}
    {ls : List SRec} {ρ ρf : WRes} {ps : List FrameRec} {μ₁ : Heap} {w : Val}
    (hend : EndOK Φ (fun k ls' v => rwp (ℍ := ℍ) Φ Q k ls' (K.plug v.1)) k₁ ls ρ ρf ps μ₁ w)
    (hfd₁ : FinDom μ₁) {j₂ : Nat} {μ' : Heap} {E : Expr} (hj : j₂ < k₁)
    (hrun : StepsN (ℍ := ℍ) j₂ μ₁ (K.plug w.1) μ' E) :
    (∀ v : Val, E = v.1 → EndOK Φ Q (k₁ - j₂) ls ρ ρf ps μ' v) ∧
      (¬ IsVal E → ∃ μ'' e'', Step1 (ℍ := ℍ) μ' E μ'' e'') := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₆, h₇, h₉, hA, hB, hT', htg', hps',
    hls', hC⟩ := hend
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  obtain ⟨hval, hprog⟩ := hC z fρ'p ps' μ₁ hz hzY hT' htg' h₇ hfd₁ j₂ μ' E hj hrun
  refine ⟨fun v hv => ?_, hprog⟩
  obtain ⟨ρ'', ρpp, Y'', Y''p, π'', ps'', ls'', k₁', k₂, k₃, k₆, k₇, k₉, kA, kB, kT, ktg, kps,
    kls, kC⟩ := hval v hv
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

/-- **Bind** (`[TR]` 6.135 at `rwp`). -/
theorem rwp_bind {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (K : Kont) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (hw : rwp (ℍ := ℍ) Φ (fun k ls' v => rwp (ℍ := ℍ) Φ Q k ls' (K.plug v.1)) n ls e ρ) :
    rwp (ℍ := ℍ) Φ Q n ls (K.plug e) ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' E hj hrun
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · obtain ⟨hval, hprog⟩ := hw ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun'
    by_cases he' : IsVal e'
    · have h := rwp_compose hΦ K (w := ⟨e', he'⟩) (hval ⟨e', he'⟩ rfl) (fd_stepsN hrun' hfd)
        (j₂ := 0) (by omega) (.refl _ _)
      exact ⟨fun v hv => by simpa using h.1 v hv, h.2⟩
    · refine ⟨fun v hv => absurd (K.isVal_of_plug (hv ▸ v.2)) he', fun _ => ?_⟩
      obtain ⟨μ'', e'', hs⟩ := hprog he'
      exact ⟨μ'', K.plug e'', hs.plug K⟩
  · obtain ⟨hval, hprog⟩ := hw ρf fρ ps μ hf hc hT htg hl hfd j₁ μ₁ t (by omega) hrun₁
    have ht : IsVal t := by
      by_contra hn
      obtain ⟨μ₂, t₂, hs⟩ := hprog hn
      exact hirr μ₂ t₂ hs
    have h := rwp_compose hΦ K (w := ⟨t, ht⟩) (hval ⟨t, ht⟩ rfl) (fd_stepsN hrun₁ hfd)
      (j₂ := j₂) (by omega) hrun₂
    have hidx : n - j₁ - j₂ = n - j := by omega
    rw [hidx] at h
    exact h

/-! ### The frame -/

/-- **The frame** (`[TR]` 6.146 with a frame `R` that holds at every index and is carried to a
list with the same members): `wpTS_ramify`'s proof, with `updVN_frame` where it has
`updV_frame`. -/
theorem rwp_frame {Φ : LocFam} {P : PostN} (R : List SRec → WProp)
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ₁ ρ₂ ρ : WRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hwp : rwp (ℍ := ℍ) Φ P n ls e ρ₁) (hR₂ : R ls ρ₂) :
    rwp (ℍ := ℍ) Φ (fun k ls' v => P k ls' v ⋆ R ls') n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  obtain ⟨hval, hprog⟩ := hwp y fρ ps μ hy₁ hyfρ hT htg hl hfd j μ' e' hj hrun
  refine ⟨fun v hv => ?_, hprog⟩
  obtain ⟨ρ', ρp, Y', Y'p, π', ps', ls', g₁, g₂, g₃, g₆, g₇, g₉, gA, gB, gT, gtg, gps,
    gls, gC⟩ := hval v hv
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

/-! ### Safety of a closed run -/

/-- **Safety**: a closed term in `rwp` at the empty world at every index never gets stuck: every
configuration it reaches is a value or steps. -/
theorem rwp_safe {Φ : LocFam} {Q : PostN} {e : Expr}
    (hall : ∀ n, rwp (ℍ := ℍ) Φ Q n [] e (PMap.empty : WRes)) {j : Nat} {μ' : Heap} {e' : Expr}
    (hrun : StepsN (ℍ := ℍ) j (fun _ => none) e μ' e') :
    IsVal e' ∨ ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'' := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨-, hprog⟩ := hall (j + 1) PMap.empty PMap.empty [] (fun _ => none)
    Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TWNC.empty htg Fig16.BoLo.lower_empty
    fd_empty j μ' e' (by omega) hrun
  by_cases hv : IsVal e'
  · exact .inl hv
  · exact .inr (hprog hv)

/-! ### Mut Anti-Frame (`[TR]` 6.66) at the step index

`wpTS_M_antiFrameX`'s proof with the cell's member stepped at the write: the callback runs on
`ρ_a ● ℓ ↦ own(v) ● ρ_v` and ends, at the index `k` left, with `ℓ ↦ own(w) ● ρ′_v ● R`, `ρ′_v` in
`F k`; the cell is written back at the member `F k` (not the stored `F j`: the content is known at
`k`, `StepGap`), and `ρ ↭ₖ R ● ℓ ↦ mut(β, w, ρ′_v, F k) ● ρ⁺` by `six28N` where the printed proof
has `ResU.six28`. Everything else is the printed proof's. -/

/-- The callback's postcondition: the cell's content handed back, at the index's member, and the
borrow it is folded into handed on. -/
def AFPost (l : Loc) (β : Life) (F : Nat → Val → SPropS Loc Val β) (Q : PostN) : PostN :=
  fun k ls' v' ρ' => ∃ (w : Val) (σ' : WRes) (h' : σ'.InStratum β) (hw' : F k w ⟨σ', h'⟩)
    (R rest : WRes), ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρ' ∧
    ResU.CompS σ' R rest ∧
    ∀ X, ResU.CompS R (ResU.single l (CellU.mutOf β w σ' h' (F k) hw')) X → Q k ls' v' X

/-- **Mut Anti-Frame at the step index.** -/
theorem rwp_M_antiFrame {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {Q : PostN} {n : Nat}
    {ls : List SRec} {e : Expr} {v : Val} {σP : WRes} {hstr : σP.InStratum β} {j : Nat}
    {hwit : F j v ⟨σP, hstr⟩} {ρa ρ : WRes}
    (hsplit : ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ)
    (hA : ∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
      rwp (ℍ := ℍ) Φ (AFPost l β F Q) n ls e X) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  classical
  intro ρf sρ ps μ hH2 hsρ hT htg hlow hfd jr μ' e' hj hrun
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  obtain ⟨hvm, hva⟩ := ResU.Valid.split hsplit hvρ
  obtain ⟨W, hW⟩ := ResU.compS_own_of_valid_mut hvm
  have hmaH : ResU.Hash (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa :=
    ⟨hsplit.1, ρ, hsplit, hvρ⟩
  have haW : ResU.Hash ρa W := (ResU.six24 hW).mp (ResU.hash_symm hmaH)
  have hvW : ResU.Valid W := by
    obtain ⟨-, s, hs, hv⟩ := haW; exact (ResU.Valid.split hs hv).2
  obtain ⟨hmf, haf⟩ := ResU.Hash.split hsplit (ResU.hash_symm hH2)
  have hfW : ResU.Hash ρf W := (ResU.six24 hW).mp (ResU.hash_symm hmf)
  obtain ⟨X, hX⟩ := (ResU.compS_defined_iff ρa W).mpr haW.1
  have hfX : ResU.Hash ρf X := ResU.hash_of_pairwise (ResU.hash_symm haf) haW hfW hX
  have hwpX := hA W X hW hX
  obtain ⟨fρ, h4, hvfρ⟩ := hfX.2
  -- the frame `ρ_f ● ρ_a` the first memory is read over
  obtain ⟨FA, hFA⟩ := (ResU.compS_defined_iff ρf ρa).mpr (ResU.hash_symm haf).1
  obtain ⟨FA₁, hFA₁, hFAmc⟩ :=
    (ResU.CompS.assoc ρf ρa (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) sρ).mp
      ⟨ρ, ResU.CompS.comm hsplit, hsρ⟩
  obtain rfl : FA = FA₁ := ResU.CompS.functional hFA hFA₁
  obtain ⟨FA₂, hFA₂, hFAWc⟩ := (ResU.CompS.assoc ρf ρa W fρ).mp ⟨X, hX, h4⟩
  obtain rfl : FA = FA₂ := ResU.CompS.functional hFA hFA₂
  have hFAm : ResU.Hash FA (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) :=
    ResU.hash_symm (ResU.hash_of_pairwise hmf (ResU.hash_symm haf) hmaH hFA)
  have hFAW : ResU.Hash FA W :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hfW) (ResU.hash_symm haf)
      (ResU.hash_symm haW) hFA)
  -- entry: `TWNC.mutUnfold`, and the same memory (6.25 under a frame)
  have hTin : TWNC fρ ps (rsOf ls) :=
    TWNC.mutUnfold hT (ResU.CompS.comm hFAmc) (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) (ResU.CompS.comm hFAmc) a).mp
      ha) htg
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hFAmc hFAm hFAWc hFAW).mp hlow
  obtain ⟨hval, hprog⟩ := hwpX ρf fρ ps μ hfX h4 hTin htgin hlowin hfd jr μ' e' hj hrun
  refine ⟨fun v' hv' => ?_, hprog⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps'', ls'', h1, h2, h3, h6, h7, h9, h10, h11, hT'', htg'',
    hps'', hls'', h12⟩ := hval v' hv'
  obtain ⟨w, σ', h', hw', ρb, rest, hcr, hcr2, hb⟩ := h12
  -- the content handed back, written into the cell at the member `F k`
  obtain ⟨W'', hW''₁, hW''₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf w)) σ' ρb ρ').mp ⟨rest, hcr2, hcr⟩
  have hW'' : ResU.CompS σ' (ResU.single l (CellU.ownOf w)) W'' := ResU.CompS.comm hW''₁
  have hvρ' : ResU.Valid ρ' := by
    obtain ⟨-, s, hs, hv⟩ := h1; exact (ResU.Valid.split hs hv).1
  have hvW'' : ResU.Valid W'' := (ResU.Valid.split hW''₂ hvρ').1
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    ResU.valid_single_mut_of_wit hW'' hvW''
  -- the compatibility results for the borrowed resource after the run
  have hW''b : ResU.Hash W'' ρb := ⟨hW''₂.1, ρ', hW''₂, hvρ'⟩
  have hbm'' : ResU.Hash ρb (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''b)
  obtain ⟨RB, hRB⟩ := (ResU.compS_defined_iff ρb
    (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw'))).mpr hbm''.1
  obtain ⟨hfp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hW''p, hbp⟩ := ResU.Hash.split hW''₂ hρ'p
  obtain ⟨hW''f, hbf⟩ := ResU.Hash.split hW''₂ h1
  have hpm'' : ResU.Hash ρp (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''p)
  have hfm'' : ResU.Hash ρf (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''f)
  have hfRB : ResU.Hash ρf RB :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbm'' hfm'' hRB
  obtain ⟨FRB, hFRB⟩ := (ResU.compS_defined_iff ρf RB).mpr hfRB.1
  obtain ⟨BP, hBP⟩ := (ResU.compS_defined_iff ρb ρp).mpr hbp.1
  have hpRB : ResU.Hash ρp RB :=
    ResU.hash_of_pairwise (ResU.hash_symm hbp) hbm'' hpm'' hRB
  have hpFRB : ResU.Hash ρp FRB :=
    ResU.hash_of_pairwise (ResU.hash_symm hfp) hfRB hpRB hFRB
  obtain ⟨FRBp, hFRBp⟩ := (ResU.compS_defined_iff FRB ρp).mpr (ResU.hash_symm hpFRB).1
  obtain ⟨π', hπ'⟩ := (ResU.compS_defined_iff RB ρp).mpr (ResU.hash_symm hpRB).1
  obtain ⟨FW, hFW, hFWb⟩ := (ResU.CompS.assoc ρf W'' ρb fρ').mp ⟨ρ', hW''₂, h2⟩
  obtain ⟨BP₁, hBP₁, hFWBP⟩ := (ResU.CompS.assoc FW ρb ρp fρ'p).mpr ⟨fρ', hFWb, h6⟩
  obtain rfl : BP = BP₁ := ResU.CompS.functional hBP hBP₁
  obtain ⟨WBP, hWBP, hfWBP⟩ := (ResU.CompS.assoc ρf W'' BP fρ'p).mpr ⟨FW, hFW, hFWBP⟩
  obtain ⟨FB, hFB, hFBW⟩ :=
    (ResU.CompS.assoc ρf BP W'' fρ'p).mp ⟨WBP, ResU.CompS.comm hWBP, hfWBP⟩
  obtain ⟨π'₁, hπ'₁, hfπ'⟩ := (ResU.CompS.assoc ρf RB ρp FRBp).mpr ⟨FRB, hFRB, hFRBp⟩
  obtain rfl : π' = π'₁ := ResU.CompS.functional hπ' hπ'₁
  obtain ⟨MP, hMP, hbMP⟩ := (ResU.CompS.assoc ρb (ResU.single l
    (CellU.mutOf β w σ' h' (F (n - jr)) hw')) ρp π').mpr ⟨RB, hRB, hπ'⟩
  obtain ⟨BP₂, hBP₂, hBPm⟩ := (ResU.CompS.assoc ρb ρp
    (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) π').mp
      ⟨MP, ResU.CompS.comm hMP, hbMP⟩
  obtain rfl : BP = BP₂ := ResU.CompS.functional hBP hBP₂
  obtain ⟨FB₁, hFB₁, hFBm⟩ :=
    (ResU.CompS.assoc ρf BP (ResU.single l
      (CellU.mutOf β w σ' h' (F (n - jr)) hw')) FRBp).mp ⟨π', hBPm, hfπ'⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  have hfBP : ResU.Hash ρf BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbp hfp hBP
  have hmBP : ResU.Hash (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbm'') hbp
      (ResU.hash_symm hpm'') hBP
  have hFBm' : ResU.Hash FB (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    ResU.hash_symm (ResU.hash_of_pairwise
      (ResU.hash_symm hfm'') hfBP hmBP hFB)
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hFBW' : ResU.Hash FB W'' := ⟨hFBW.1, fρ'p, hFBW, hvfρ'p⟩
  -- the second memory, by 6.25 under a frame
  have hmem₂ : ResU.Lower FRBp μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFBm hFBm' hFBW hFBW').mpr h7
  -- `ρ ↭ₖ ρ_b ● ρ''_m ● ρ_p`, by 6.28 at the index with the stepped member
  obtain ⟨BPW, hBPW₁, hBPW₂⟩ := (ResU.CompS.assoc W'' ρb ρp π).mpr ⟨ρ', hW''₂, h9⟩
  obtain rfl : BP = BPW := ResU.CompS.functional hBP hBPW₁
  have hvπ' : ResU.Valid π' := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hpRB
    exact ResU.CompS.functional hs hπ' ▸ hv
  have hupd : UpdN Φ (n - jr) ρ π' :=
    six28N hΦ hF le_rfl hW hW'' (ResU.CompS.comm hsplit) hBPm hX (ResU.CompS.comm hBPW₂)
      hvρ hvπ' h10.2.1 h10.2.2 h10.1
  -- exit: `TWNC.mutFold`
  have hvFRBp : ResU.Valid FRBp := by obtain ⟨σ, hσ, -⟩ := hmem₂; exact ⟨σ, hσ⟩
  have hTout : TWNC FRBp ps'' (rsOf ls'') :=
    TWNC.mutFold hT'' hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) hvFRBp
  have htgout : Tagged FRBp ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) a).mpr ha) htg''
  exact ⟨RB, ρp, FRB, FRBp, π', ps'', ls'', ResU.hash_symm hfRB, hFRB, hpFRB, hFRBp, hmem₂,
    hπ', ⟨hupd, hvρ, hvπ'⟩, h11, hTout, htgout, hps'', hls'', hb RB hRB⟩

/-! ### Mut Frame (`[TR]` 6.65) at the step index

The lender's side. The borrow is created at a lifetime `A` and a family `F` over `Res_A` that
`Φ` takes on at `ℓ` for the inner run (`Φ′ = Φ[ℓ ↦ (A, F)]`; outside the run `ℓ` is owned, so no
`mut` cell of the outer resources is at `ℓ`). The stored member is `F j`, `j ≥ n`. At the end
`[TR]` 6.27 finds the borrow still at the top level, now with a predicate `UpdVN` relates to
`F j` (`six27N`), so its content is in `F k` at the index `k` left (`predStep_read`): the lender
reads back what `F k` allows, and `ρ ↭ₖ ρ′ ● …` by 6.28's left-to-right half at the index
(`six28N_fwd`). -/

/-- `UpdN` keeps the strata: `ResU.updV_inStratum`, the `mut` clause read through `MutStep`'s
equal lifetimes. -/
theorem updVN_inStratum {Φ : LocFam} {k : Nat} {ρ ρ' : WRes} {α : Life}
    (hd : ρ.InStratum α) (hu : UpdVN Φ k ρ ρ') : ρ'.InStratum α := by
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hσα : σ.InStratum α := BoLo.flat_inStratum hσ hd
  refine BoLo.flat_inStratum_inv hσ' ?_
  intro m χ hχ
  rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hgg⟩ := (hu.1.1 m s w ξ hξ).mpr ⟨σ', hσ', hχ⟩
    cases ResU.Flat.functional hτ hσ
    exact hσα m _ hgg
  · obtain ⟨ψ, ⟨τ, hτ, hgg⟩, hs⟩ := hu.1.2.2 m _ ⟨σ', hσ', hχ⟩ rfl
    cases ResU.Flat.functional hτ hσ
    have hat : ψ.at = b := hs.2.2.1
    have := hσα m ψ hgg
    rcases CellU.rep ψ with ⟨w', rfl⟩ | ⟨s', w', ξ', hξ', rfl⟩ | ⟨b', w', ξ', hξ', P', hP', rfl⟩
    · exact absurd hs.1 (by simp)
    · exact absurd hs.1 (by simp)
    · simp only [CellU.at_mutOf] at hat
      subst hat
      exact this

/-- **`[TR]` 6.27 at the step index**: if `@ρ ⊐ α` and `ρ ● ℓ ↦ mut(α, v, ρ_v, P̂) ↭ₖ ρ′`, then
`ρ′ = ρ′/ℓ ● ℓ ↦ mut(α, v′, ρ′_v, P̂′)` with `P̂′` related to `P̂` by the step. The printed proof,
with the `mut` clause's `MutStep` for the printed `P̂`. -/
theorem six27N {Φ : LocFam} {k : Nat} {l : Loc} {α : Life} {v : Val} {ρ ρv M ρ' : WRes}
    {h : ResU.InStratum α ρv} {P : Val → SPropS Loc Val α} {hw : P v ⟨ρv, h⟩}
    (hout : ResU.InStratum α ρ)
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf α v ρv h P hw)) M)
    (hu : UpdVN Φ k M ρ') :
    ∃ (v' : Val) (χ : WRes) (h' : ResU.InStratum α χ) (P' : Val → SPropS Loc Val α)
      (hw' : P' v' ⟨χ, h'⟩),
      MutStep Φ k l (CellU.mutOf α v ρv h P hw) (CellU.mutOf α v' χ h' P' hw') ∧
      ResU.CompS (ρ'.del l) (ResU.single l (CellU.mutOf α v' χ h' P' hw')) ρ' := by
  classical
  have hkm : (CellU.mutOf α v ρv h P hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hMl : M.get l = some (CellU.mutOf α v ρv h P hw) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hM)
      (ResU.single_get_self _ _) hkm).2
  have hσl : σ.get l = some (CellU.mutOf α v ρv h P hw) :=
    ResU.flat_get_of_ne_imm hσ hMl hkm
  obtain ⟨ψ', hfa', hs⟩ := hu.1.2.1 l _ ⟨σ, hσ, hσl⟩ rfl
  rcases CellU.rep ψ' with ⟨u, rfl⟩ | ⟨s', u, τ, m, rfl⟩ | ⟨b', v', χ, h', P', hw', rfl⟩
  · exact absurd hs.2.1 (by simp)
  · exact absurd hs.2.1 (by simp)
  have hb' : α = b' := hs.2.2.1
  subst hb'
  have hflat := (ResU.flatAt_iff hσ' _ _).mp hfa'
  have hdM : M.InStratum (↓α) :=
    BoLo.inStratum_comp (BoLo.compS_hC (↓α)) hM
      (fun m ψ e => CellU.InStratum.mono (le_of_lt (Life.down_sqsubset α)) (hout m ψ e))
      (ResU.inStratum_single l ((CellU.inStratum_mutOf (↓α) α v ρv h P hw).mpr
        (Life.down_sqsubset α)))
  have hd' : ρ'.InStratum (↓α) := updVN_inStratum hdM hu
  have hρ'l : ρ'.get l ≠ none := by
    intro hnone
    have hcon := ResU.flat_inStratum_at hσ' hd'
      (fun φ e => absurd (hnone ▸ e) (by simp)) hflat
    rw [CellU.inStratum_mutOf] at hcon
    exact absurd hcon (lt_irrefl _)
  obtain ⟨φ, hφ⟩ : ∃ φ, ρ'.get l = some φ := by
    cases hg : ρ'.get l with
    | none => exact absurd hg hρ'l
    | some φ => exact ⟨φ, rfl⟩
  obtain ⟨χ₀, hχ₀, hk₀, -, -⟩ := ResU.Flat.get hσ' hφ
  rw [hflat] at hχ₀
  obtain rfl : χ₀ = CellU.mutOf α v' χ h' P' hw' := (Option.some.inj hχ₀).symm
  have hkφ : φ.kind ≠ Kind.imm := by
    rw [← hk₀, CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hgg : σ'.get l = some φ := ResU.flat_get_of_ne_imm hσ' hφ hkφ
  rw [hflat] at hgg
  obtain rfl : φ = CellU.mutOf α v' χ h' P' hw' := (Option.some.inj hgg).symm
  exact ⟨v', χ, h', P', hw', hs, ResU.del_compS hφ⟩

/-- `Φ′` agrees with `Φ` off `ℓ`. -/
def LocFam.AgreeOff (Φ Φ' : LocFam) (l : Loc) : Prop := ∀ x, x ≠ l → Φ' x = Φ x

theorem mutStep_agree {Φ Φ' : LocFam} {n : Nat} {x : Loc} (he : Φ' x = Φ x)
    {ψ ψ' : CellU Loc Val} (h : MutStep Φ' n x ψ ψ') : MutStep Φ n x ψ ψ' := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun hn => h.2.2.2.1 (he.trans hn), fun b F hF => ?_⟩
  exact h.2.2.2.2 b F (he.trans hF)

/-- **`[TR]` 6.28, left to right, at the step index**: an update of the `mut` side at `Φ′` is an
update of the `own` side at `Φ`, `Φ′` agreeing with `Φ` off `ℓ`. Off `ℓ` as printed; at `ℓ` the
`own` side has no borrow. -/
theorem six28N_fwd {Φ Φ' : LocFam} (hag : Φ.AgreeOff Φ' l) {k : Nat} {b : Life}
    {v v' : Val} {ρ ρ' ρv ρv' W W' M M' O O' : WRes}
    {hs : ResU.InStratum b ρv} {hs' : ResU.InStratum b ρv'}
    {P P' : Val → SPropS Loc Val b} {hw : P v ⟨ρv, hs⟩} {hw' : P' v' ⟨ρv', hs'⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hW' : ResU.CompS ρv' (ResU.single l (CellU.ownOf v')) W')
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf b v ρv hs P hw)) M)
    (hM' : ResU.CompS ρ' (ResU.single l (CellU.mutOf b v' ρv' hs' P' hw')) M')
    (hO : ResU.CompS ρ W O) (hO' : ResU.CompS ρ' W' O')
    (hvM : ResU.Valid M) (hvM' : ResU.Valid M')
    (hvO : ResU.Valid O) (hvO' : ResU.Valid O')
    (h : UpdN Φ' k M M') : UpdN Φ k O O' := by
  classical
  obtain ⟨σM, hσM⟩ := hvM
  obtain ⟨σM', hσM'⟩ := hvM'
  obtain ⟨σO, hσO⟩ := hvO
  obtain ⟨σO', hσO'⟩ := hvO'
  obtain ⟨hoff, -, hOl⟩ := ResU.flat_mut_own_agree_off hW hM hO hσM hσO
  obtain ⟨hoff', -, hOl'⟩ := ResU.flat_mut_own_agree_off hW' hM' hO' hσM' hσO'
  refine updN_of_flat hσO hσO' (fun x => ?_)
  by_cases hx : x = l
  · subst hx
    rw [hOl, hOl']
    refine ⟨fun s w χ hh => ⟨fun e => ?_, fun e => ?_⟩, fun ψ e hk => ?_, fun ψ e hk => ?_⟩
    · exact absurd (Option.some.inj e) CellU.ownOf_ne_immOf
    · exact absurd (Option.some.inj e) CellU.ownOf_ne_immOf
    · cases e; simp at hk
    · cases e; simp at hk
  · rw [hoff x hx, hoff' x hx]
    obtain ⟨hi, hf, hb⟩ := cellUpdN_of_updN h hσM hσM' x
    refine ⟨hi, fun ψ e hk => ?_, fun ψ e hk => ?_⟩
    · obtain ⟨ψ', e', hs⟩ := hf ψ e hk
      exact ⟨ψ', e', mutStep_agree (hag x hx) hs⟩
    · obtain ⟨ψ₀, e', hs⟩ := hb ψ e hk
      exact ⟨ψ₀, e', mutStep_agree (hag x hx) hs⟩

/-- `Φ[ℓ ↦ (A, F)]`. -/
def LocFam.set (Φ : LocFam) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) : LocFam :=
  fun x => if x = l then some ⟨A, F⟩ else Φ x

theorem LocFam.set_down {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) : (Φ.set l A F).Down := by
  intro x b G hx
  by_cases h : x = l
  · subst h
    simp only [LocFam.set] at hx
    cases hx
    exact hF
  · simp only [LocFam.set, if_neg h] at hx
    exact hΦ x b G hx

theorem LocFam.set_agree (Φ : LocFam) (l : Loc) (A : Life)
    (F : Nat → Val → SPropS Loc Val A) : Φ.AgreeOff (Φ.set l A F) l :=
  fun x hx => by simp [LocFam.set, hx]

/-- The lender's postcondition for the borrowed run: the result outlives `A`, and handed the
cell back at `w` with content in `F k`, `Q`. -/
def MFPost (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) (Q : PostN) : PostN :=
  fun k ls' v' ρ' => ρ'.InStratum A ∧
    ∀ w Y, ResU.CompS ρ' (ResU.single l (CellU.ownOf w)) Y →
      ∀ σ, (∃ hσ : σ.InStratum A, F k w ⟨σ, hσ⟩) → ∀ Z, ResU.CompS Y σ Z → Q k ls' v' Z

/-- **Mut Frame at the step index.** `ℓ ↦ v ⋆ ρ_P ⋆ ρ_b`, `ρ_P` the content in `F j`, `j ≥ n`,
lent at `A` for a run proved at `Φ[ℓ ↦ (A, F)]` from the borrow: the run is in `rwp` at `Φ`. -/
theorem rwp_M_frame {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {Q : PostN} {n j : Nat}
    (hjn : n ≤ j) {ls : List SRec} {e : Expr} {v : Val} {ρP ρlP ρb ρ : WRes}
    (houtP : ρP.InStratum A) (houtb : ρb.InStratum A) (hwit : F j v ⟨ρP, houtP⟩)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hA : ∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP (F j) hwit)) BM →
      rwp (ℍ := ℍ) (Φ.set l A F) (MFPost l A F Q) n ls e BM) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  classical
  intro ρf sρ ps μ hH3 hsρ hT htg hlow hfd jr μ' e' hj hrun
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set ρm : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.mutOf A v ρP houtP (F j) hwit) with hρm
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- H12-H17: the compatibility block
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρm := (ResU.six24 hlPcell).mpr hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρm :=
    (ResU.six24 hlPcell).mpr (ResU.hash_symm hlPf)
  obtain ⟨BM, hBM⟩ := (ResU.compS_defined_iff ρb ρm).mpr hH13.1
  have hH17 : ResU.Hash ρf BM :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBM
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBm⟩ := (ResU.CompS.assoc ρf ρb ρm fρ).mp ⟨BM, hBM, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- entry: `TWNC.mutFold`, and the same memory (6.25 under a frame)
  have hTin : TWNC fρ ps (rsOf ls) :=
    TWNC.mutFold hT hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) a).mpr ha) htg
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBM : ResU.Valid BM := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvmm : ResU.Valid ρm := (ResU.Valid.split hBM hvBM).2
  have hFBmH : ResU.Hash FB ρm :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_mut_own hlPcell hvmm hvlP hFBm hFBmH hFBl hFBlH).mpr hlow
  -- H18: the borrowed run, at `Φ[ℓ ↦ (A, F)]`
  obtain ⟨hval, hprog⟩ :=
    hA BM hBM ρf fρ ps μ hH17 h4 hTin htgin hlowin hfd jr μ' e' hj hrun
  refine ⟨fun v' hv' => ?_, hprog⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps'', ls'', h1, h2, h3, h6, h7, h9, h10, h11, hT'', htg'',
    hps'', hls'', h12⟩ := hval v' hv'
  -- H24 and H25: unfolding `[α]`
  obtain ⟨houtρ', hwand'⟩ := h12
  -- H26: 6.27 at the index -- the borrow is still at the top level of `ρ′ ● ρ⁺`
  obtain ⟨v'', χ, hχ, P'', hwit'', hstep, hsplit''⟩ := six27N houtb hBM h10
  have hπl : π.get l = some (CellU.mutOf A v'' χ hχ P'' hwit'') := by
    rw [ResU.Comp.get_of_left_none hsplit'' (ResU.del_get_self _ _)]
    exact ResU.single_get_self _ _
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hwit'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨hρ'ln, hppl⟩ :
      ρ'.get l = none ∧ ρp.get l = some (CellU.mutOf A v'' χ hχ P'' hwit'') := by
    rcases ResU.CompS.get_split_of_ne_imm h9 hπl hkm'' with ⟨hg, -⟩ | ⟨hg, hp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    · exact ⟨hg, hp⟩
  have hpd : ResU.CompS (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) ρp := ResU.del_compS hppl
  obtain ⟨RPD, hRPD, hRPDm⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) π).mp ⟨ρp, hpd, h9⟩
  have hvπ : ResU.Valid π := h10.2.2
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) :=
    (ResU.Valid.split hRPDm hvπ).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  have hRPDmH : ResU.Hash RPD (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) :=
    ⟨hRPDm.1, π, hRPDm, hvπ⟩
  have hH27 : ResU.Hash RPD W'' := (ResU.six24 hW'').mp hRPDmH
  obtain ⟨hfρ', hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρ')
  obtain ⟨hρ'PD, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'W'', hPDW''⟩ := ResU.Hash.split hRPD hH27
  have hfm'' : ResU.Hash ρf W'' :=
    (ResU.six24 hW'').mp (ResU.hash_symm (ResU.Hash.split hpd (ResU.hash_symm hfρ')).2)
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ' W'').mpr hρ'W''.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm h1) hρ'W'' hfm'' hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (ρp.del l) R :=
    ResU.hash_of_pairwise hρ'PD hρ'W'' hPDW'' hR
  have hPDFR : ResU.Hash (ρp.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ := (ResU.compS_defined_iff FR (ρp.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ := (ResU.compS_defined_iff R (ρp.del l)).mpr (ResU.hash_symm hPDR).1
  -- H33: the second memory, by 6.25 under a frame (6.8)
  obtain ⟨FP, hFP, hFPm⟩ := (ResU.CompS.assoc fρ' (ρp.del l)
    (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) fρ'p).mp ⟨ρp, hpd, h6⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (ρp.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ' W'' (ρp.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨RPD₁, hRPD₁, hRPDW⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l) W'' RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : RPD = RPD₁ := ResU.CompS.functional hRPD hRPD₁
  obtain ⟨FPD, hFPD, hFPDW⟩ :=
    (ResU.CompS.assoc ρf RPD W'' FRP).mp ⟨RP, hRPDW, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ' (ρp.del l) FP).mpr ⟨fρ', h2, hFP⟩
  obtain rfl : RPD = FP₁ := ResU.CompS.functional hRPD hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hvW'' : ResU.Valid W'' := by
    obtain ⟨-, s, hs, hv⟩ := hH27; exact (ResU.Valid.split hs hv).2
  have hFPmH : ResU.Hash FP (ResU.single l (CellU.mutOf A v'' χ hχ P'' hwit'')) :=
    ⟨hFPm.1, fρ'p, hFPm, hvfρ'p⟩
  have hFPWH : ResU.Hash FP W'' := ⟨hFPDW.1, FRP, hFPDW, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFPm hFPmH hFPDW hFPWH).mp h7
  -- H34: `ρ ↭ₖ ρ′ ● ρ''_v ● ℓ ↦ own(v'') ● ρ⁺/ℓ`, by 6.28 at the index
  have hvRP : ResU.Valid RP := by
    obtain ⟨-, s, hs, hv⟩ := hH27
    exact ResU.CompS.functional hs hRPDW ▸ hv
  have hupd : UpdN Φ (n - jr) ρ RP :=
    six28N_fwd (Φ.set_agree l A F) hlPcell hW'' hBM hRPDm (ResU.CompS.comm hcρ) hRPDW
      hvBM hvπ hvρ hvRP h10.1
  have hno : BoLo.NoOwn (ρp.del l) := by
    refine PMap.ext fun x => ?_
    cases hgg : ((ρp.del l).restrict Kind.own).get x with
    | none => simp
    | some ψ =>
        exfalso
        obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
        by_cases hx : x = l
        · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
        · rw [ResU.del_get_ne _ hx] at hdd
          have hcc : (ρp.restrict Kind.own).get x = some ψ :=
            ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
          rw [h11] at hcc
          simp at hcc
  -- exit: `TWNC.mutUnfold`
  have hTout : TWNC FRP ps'' (rsOf ls'') :=
    TWNC.mutUnfold hT'' (ResU.CompS.comm hFPm) (ResU.CompS.comm hW'')
      (ResU.CompS.comm hFPDW) hvFRP
  have htgout : Tagged FRP ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW'') (ResU.CompS.comm hFPDW) (ResU.CompS.comm hFPm) a).mp
      ha) htg''
  -- H35: the lender's read-back, the content in `F k` by the step from `F j`
  have hFl : Φ.set l A F l = some ⟨A, F⟩ := by simp [LocFam.set]
  have hχv : SPropS.toU (F (n - jr) v'') χ :=
    predStep_read (LocFam.set_down hΦ hF) hFl (k := j) (by omega)
      (fun u r hp => (mpred_mutOf u r).mp hp) hstep.2.2.2 v'' χ
      ((mpred_mutOf v'' χ).mpr ⟨hχ, hwit''⟩)
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
  have hQ := hwand' v'' y hy₁ χ hχv R hy₂
  exact ⟨R, ρp.del l, FR, FRP, RP, ps'', ls'', ResU.hash_symm hfR, hFR, hPDFR, hFRP, hmem₂,
    hRP, ⟨hupd, hvρ, hvRP⟩, hno, hTout, htgout, hps'', hls'', hQ⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
