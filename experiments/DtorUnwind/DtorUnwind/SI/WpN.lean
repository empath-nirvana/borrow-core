import DtorUnwind.SI.UpdN
import DtorUnwind.SI.Frag
import Core.Wp

/-!
# Stage 2, step 2 (part): the step-indexed `wp` over Core's typed worlds

`swp Φ Q n ls e ρ`: `wpTS` (`Core/World.lean`, `[TR]` p. 6's `wp`, row 5.33's repair) read one
machine step at a time and cut at the step index `n`, as `ewp` (`SI/Ewp.lean`) reads LinearActris's
`WP₀`. Under every frame `ρ_f # ρ` whose completion `ρ_f ● ρ` is a tagged `TW` world lowering to
the memory `μ`, the term steps, and every step lands at a configuration `ρ_f ● ρ′ ● ρ⁺` that is
again a tagged `TW` world lowering to the new memory, with `ρ ↭ₙ ρ′ ● ρ⁺` (`UpdVN`), `ρ⁺` owning
nothing, the same frames and list members, and `swp` at `n − 1` for the rest at `ρ′`. A value is
in `Q`. Every conjunct but the step and the index is `wpTS`'s, verbatim.

`wpTS`'s `wp-bind` (`[TR]` 6.135) composes two whole runs with 6.48 and 6.49; one step at a time,
bind is the context rule (`swp_bind`) and the update is the step's own. The frame (`[TR]` 6.146's
ramification with a frame that holds at every index, `swp_frame`) is where 6.48 is consumed:
`ρ₁ ● ρ₂ ↭ₙ ρ′ ● ρ₂ ● ρ⁺` from `ρ₁ ↭ₙ ρ′ ● ρ⁺`, by `updVN_frame` exactly as `wpTS_ramify` uses
`updV_frame`.

`Φ` is fixed through a run here. A rule that creates a `mut` borrow (`[TR]` 6.65) has to extend it
at the borrowed location; not done.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont)

/-- A postcondition at a step index, over the returned list. -/
abbrev PostN : Type := Nat → List SRec → Val → WProp

/-- **The step-indexed `wp` at a tagged typed world.** -/
def swp (Φ : LocFam) (Q : PostN) : Nat → List SRec → Expr → WProp
  | 0, _, _ => fun _ => True
  | n + 1, ls, e => fun ρ =>
    (∃ v : Val, e = v.1 ∧ Q (n + 1) ls v ρ) ∨
    (¬ IsVal e ∧ ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → FinDom μ →
      (∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e') ∧
      ∀ μ' e', Step1 (ℍ := ℍ) μ e μ' e' →
        ∃ (ρ' ρp fρ' fρ'p π : WRes) (ps' : List FrameRec) (ls' : List SRec),
          ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
          ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
          ResU.CompS ρ' ρp π ∧ UpdVN Φ n ρ π ∧ NoOwn ρp ∧
          TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
          (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧
          swp Φ Q n ls' e' ρ')

section
variable {Φ : LocFam} {Q : PostN}

theorem swp_zero (ls : List SRec) (e : Expr) (ρ : WRes) : swp (ℍ := ℍ) Φ Q 0 ls e ρ := by
  simp [swp]

theorem swp_succ {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes} :
    swp (ℍ := ℍ) Φ Q (n + 1) ls e ρ ↔
    ((∃ v : Val, e = v.1 ∧ Q (n + 1) ls v ρ) ∨
    (¬ IsVal e ∧ ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → FinDom μ →
      (∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e') ∧
      ∀ μ' e', Step1 (ℍ := ℍ) μ e μ' e' →
        ∃ (ρ' ρp fρ' fρ'p π : WRes) (ps' : List FrameRec) (ls' : List SRec),
          ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
          ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
          ResU.CompS ρ' ρp π ∧ UpdVN Φ n ρ π ∧ NoOwn ρp ∧
          TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
          (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧
          swp (ℍ := ℍ) Φ Q n ls' e' ρ')) := by
  rw [swp]

/-- A value in the postcondition. -/
theorem swp_val {n : Nat} {ls : List SRec} {v : Val} {ρ : WRes} (h : Q n ls v ρ) :
    swp (ℍ := ℍ) Φ Q n ls v.1 ρ := by
  cases n with
  | zero => exact swp_zero _ _ _
  | succ n => exact swp_succ.2 (.inl ⟨v, rfl, h⟩)

/-- A value's `swp` is its postcondition. -/
theorem swp_val_inv {n : Nat} {ls : List SRec} {v : Val} {ρ : WRes}
    (h : swp (ℍ := ℍ) Φ Q (n + 1) ls v.1 ρ) : Q (n + 1) ls v ρ := by
  rcases swp_succ.1 h with ⟨w, hw, hq⟩ | ⟨hnv, -⟩
  · rwa [Subtype.ext hw]
  · exact absurd v.2 hnv

end

/-! ### Downward closure -/

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

/-- **`swp` is downward closed.** -/
theorem swp_down {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) :
    ∀ n ls e ρ, swp (ℍ := ℍ) Φ Q (n + 1) ls e ρ → swp (ℍ := ℍ) Φ Q n ls e ρ := by
  intro n
  induction n with
  | zero => intro ls e ρ _; exact swp_zero _ _ _
  | succ n ih =>
      intro ls e ρ h
      rcases swp_succ.1 h with ⟨v, hv, hq⟩ | ⟨hnv, hst⟩
      · exact swp_succ.2 (.inl ⟨v, hv, hQ _ _ _ _ hq⟩)
      · refine swp_succ.2 (.inr ⟨hnv, fun ρf fρ ps μ hf hc hT htg hl hfd => ?_⟩)
        obtain ⟨hred, hpres⟩ := hst ρf fρ ps μ hf hc hT htg hl hfd
        refine ⟨hred, fun μ' e' h' => ?_⟩
        obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁,
          h₁₂, h₁₃⟩ := hpres μ' e' h'
        exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆,
          h₇.down hΦ (Nat.le_succ n), h₈, h₉, h₁₀, h₁₁, h₁₂, ih _ _ _ h₁₃⟩

/-! ### Monotonicity and bind -/

theorem swp_mono {Φ : LocFam} {P Q : PostN} (hPQ : ∀ n ls v ρ, P n ls v ρ → Q n ls v ρ) :
    ∀ n ls e ρ, swp (ℍ := ℍ) Φ P n ls e ρ → swp (ℍ := ℍ) Φ Q n ls e ρ := by
  intro n
  induction n with
  | zero => intro ls e ρ _; exact swp_zero _ _ _
  | succ n ih =>
      intro ls e ρ h
      rcases swp_succ.1 h with ⟨v, hv, hq⟩ | ⟨hnv, hst⟩
      · exact swp_succ.2 (.inl ⟨v, hv, hPQ _ _ _ _ hq⟩)
      · refine swp_succ.2 (.inr ⟨hnv, fun ρf fρ ps μ hf hc hT htg hl hfd => ?_⟩)
        obtain ⟨hred, hpres⟩ := hst ρf fρ ps μ hf hc hT htg hl hfd
        refine ⟨hred, fun μ' e' h' => ?_⟩
        obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁,
          h₁₂, h₁₃⟩ := hpres μ' e' h'
        exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁,
          h₁₂, ih _ _ _ h₁₃⟩

/-- **Bind** (`[TR]` 6.135, one step at a time): `e` runs under `K`; at each value it returns,
`K[v]` goes on at the list and index reached. -/
theorem swp_bind {Φ : LocFam} {Q : PostN} (K : Kont) :
    ∀ n ls e ρ, swp (ℍ := ℍ) Φ (fun k ls' v => swp (ℍ := ℍ) Φ Q k ls' (K.plug v.1)) n ls e ρ →
      swp (ℍ := ℍ) Φ Q n ls (K.plug e) ρ := by
  intro n
  induction n with
  | zero => intro ls e ρ _; exact swp_zero _ _ _
  | succ n ih =>
      intro ls e ρ h
      rcases swp_succ.1 h with ⟨v, rfl, hq⟩ | ⟨hnv, hst⟩
      · exact hq
      · have hnv' : ¬ IsVal (K.plug e) := fun hv => hnv (K.isVal_of_plug hv)
        refine swp_succ.2 (.inr ⟨hnv', fun ρf fρ ps μ hf hc hT htg hl hfd => ?_⟩)
        obtain ⟨⟨μ₁, e₁, hred⟩, hpres⟩ := hst ρf fρ ps μ hf hc hT htg hl hfd
        refine ⟨⟨μ₁, K.plug e₁, hred.plug K⟩, fun μ' E hE => ?_⟩
        obtain ⟨e', rfl, he'⟩ := step1_plug_of_step K hred hE
        obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁,
          h₁₂, h₁₃⟩ := hpres μ' e' he'
        exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁,
          h₁₂, ih _ _ _ h₁₃⟩

/-! ### The frame: `[TR]` 6.48's consumer -/

/-- **The frame** (`[TR]` 6.146 with a frame `R` that holds at every index and is carried to a
list with the same members): `wpTS_ramify`'s proof one step at a time, with `updVN_frame` where
it has `updV_frame`. -/
theorem swp_frame {Φ : LocFam} {P : PostN} (R : List SRec → WProp)
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ) :
    ∀ n ls e ρ₁ ρ₂ ρ, ResU.CompS ρ₁ ρ₂ ρ → swp (ℍ := ℍ) Φ P n ls e ρ₁ → R ls ρ₂ →
      swp (ℍ := ℍ) Φ (fun k ls' v => P k ls' v ⋆ R ls') n ls e ρ := by
  intro n
  induction n with
  | zero => intro ls e ρ₁ ρ₂ ρ _ _ _; exact swp_zero _ _ _
  | succ n ih =>
      intro ls e ρ₁ ρ₂ ρ hcρ hwp hR₂
      rcases swp_succ.1 hwp with ⟨v, hv, hq⟩ | ⟨hnv, hst⟩
      · exact swp_succ.2 (.inl ⟨v, hv, ρ₁, ρ₂, hcρ, hq, hR₂⟩)
      · refine swp_succ.2 (.inr ⟨hnv, fun ρf fρ ps μ hf hc hT htg hl hfd => ?_⟩)
        obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
        obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
        cases ResU.CompS.functional hy' hy
        obtain ⟨hred, hpres⟩ := hst y fρ ps μ hy₁ hyfρ hT htg hl hfd
        refine ⟨hred, fun μ' e' h' => ?_⟩
        obtain ⟨ρ', ρp, Y', Y'p, π', ps', ls', g₁, g₂, g₃, g₆, g₇, g₉, gA, gB, gT, gtg, gps,
          gls, gC⟩ := hpres μ' e' h'
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
          gls, ih ls' e' ρ' ρ₂ W (ResU.CompS.comm hW) gC (hR ls ls' gls ρ₂ hR₂)⟩
        exact updVN_frame (ResU.CompS.comm hcρ) hπn
          ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, (hash_valid hf).2⟩ h₂π gA

/-! ### Safety of a closed run -/

/-- A configuration `swp` covers at index `n`: the memory lowers a tagged `TW` world
`ρ_f ● ρ` at the empty list, and `ρ` is in `swp` at `n`. -/
def SwpConf (Φ : LocFam) (Q : PostN) (n : Nat) (μ : Heap) (e : Expr) : Prop :=
  ∃ (ρf ρ fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
    TW fρ ps (rsOf []) ∧ Tagged fρ ps [] ∧ ResU.Lower fρ μ ∧ FinDom μ ∧
    swp (ℍ := ℍ) Φ Q n [] e ρ

/-- One step keeps the configuration covered, one index down; the garbage joins the frame. -/
theorem swpConf_step {Φ : LocFam} {Q : PostN} {n : Nat} {μ μ' : Heap} {e e' : Expr}
    (h : SwpConf (ℍ := ℍ) Φ Q (n + 1) μ e) (hs : Step1 (ℍ := ℍ) μ e μ' e') :
    SwpConf (ℍ := ℍ) Φ Q n μ' e' := by
  obtain ⟨ρf, ρ, fρ, ps, hf, hc, hT, htg, hl, hfd, hw⟩ := h
  rcases swp_succ.1 hw with ⟨v, rfl, -⟩ | ⟨-, hst⟩
  · exact absurd hs (BoLo.no_step_val (w := v))
  obtain ⟨-, hpres⟩ := hst ρf fρ ps μ hf hc hT htg hl hfd
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₆, h₇, -, -, -, hT', htg', -, hls',
    hw'⟩ := hpres μ' e' hs
  have hnil : ls' = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    simpa using (hls' x).mp hx
  subst hnil
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by
    rwa [ResU.CompS.functional hz₀ (ResU.CompS.comm hzp)] at hY
  exact ⟨z, ρ', fρ'p, ps', hz, hzY, hT', htg', h₇, fd_step1 hs hfd, hw'⟩

/-- A run keeps a configuration covered at every index. -/
theorem swpConf_steps {Φ : LocFam} {Q : PostN} {μ₁ μ' : Heap} {e₁ e' : Expr}
    (hs : BoLo.Steps (ℍ := ℍ) μ₁ e₁ μ' e') :
    (∀ n, SwpConf (ℍ := ℍ) Φ Q n μ₁ e₁) → ∀ n, SwpConf (ℍ := ℍ) Φ Q n μ' e' := by
  induction hs with
  | refl => exact id
  | more h t ih => exact fun hc => ih (fun n => swpConf_step (hc (n + 1)) h)

/-- **Safety**: a closed term in `swp` at the empty world at every index never gets stuck: every
configuration it reaches is a value or steps. -/
theorem swp_safe {Φ : LocFam} {Q : PostN} {e : Expr}
    (hall : ∀ n, swp (ℍ := ℍ) Φ Q n [] e (PMap.empty : WRes)) :
    ∀ μ' e', BoLo.Steps (ℍ := ℍ) (fun _ => none) e μ' e' →
      IsVal e' ∨ ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'' := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  have h₀ : ∀ n, SwpConf (ℍ := ℍ) Φ Q n (fun _ => none) e := fun n =>
    ⟨PMap.empty, PMap.empty, PMap.empty, [], Fig16.LogRel.hash_empty,
      ResU.comp_empty_right _, TW.empty, htg, Fig16.BoLo.lower_empty, fd_empty, hall n⟩
  intro μ' e' hs
  have hall' := swpConf_steps hs h₀
  obtain ⟨ρf, ρ, fρ, ps, hf, hc, hT, htg', hl, hfd, hw⟩ := hall' 1
  rcases swp_succ.1 hw with ⟨v, rfl, -⟩ | ⟨-, hst⟩
  · exact .inl v.2
  · exact .inr (hst ρf fρ ps μ' hf hc hT htg' hl hfd).1

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end
