import WorldW.Wp

/-!
# WorldW — Core is the `τ = σ = []` instance (DESIGN §1.9)

**World: the W-draft at `τ = []`, compared with Core's relation (`σ = []`).**

* `wpGW_nil`: at `τ = τ′ = []` and `σ = []`, `wpGW` is `wpG` (`Core/EffDefs.lean:27`). `Close []`
  is the identity, `CompatW []` is `#`, `StopW` is conjunct (40), and the selection premise is
  vacuous.
* `ewpTS_ewpW`: every Core `ewpTS` at `opTable T` is an `ewpW []` at `opTableW T`, at every `σ`,
  whose stops hand nothing open.

So every Core result is a result about `ewpW []`. The converse is T1 for tier-1 programs, which is
Unit 3's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem close_nil_iff {ρ ρc : WRes} : Close [] ρ ρc ↔ ρc = ρ :=
  ⟨closePre_nil_inv, fun h => h ▸ .nil _ _⟩

/-- `CompatW []` is `#`. -/
theorem compatW_nil_iff {ρf ρ : WRes} : CompatW [] ρf ρ ↔ ResU.Hash ρf ρ := by
  constructor
  · intro h; exact (h ρ (.nil _ _)).1
  · intro h ρc hρc
    rw [close_nil_iff] at hρc; subst hρc
    exact ⟨h, fun X hX => ⟨X, .nil _ _, hX⟩⟩

theorem holds_nil (ρ : WRes) : Holds [] ρ := ⟨ρ, .nil _ _⟩

/-- `#` of the frame with the final resource, and of the leftover with the borrower's part: both
are parts of the valid final configuration. -/
theorem hash_of_final {ρf ρ' ρp fρ' fρ'p π : WRes} (h₂ : ResU.CompS ρf ρ' fρ')
    (h₅ : ResU.CompS fρ' ρp fρ'p) (hv : ResU.Valid fρ'p) (h₈ : ResU.CompS ρ' ρp π) :
    ResU.Hash ρf π ∧ ResU.Hash ρp ρ' ∧ ResU.Valid ρ' := by
  obtain ⟨x, hx, hxc⟩ := compS_reassoc h₂ h₅
  cases ResU.CompS.functional hx h₈
  have hvπ : ResU.Valid π := (ResU.Valid.split hxc hv).2
  exact ⟨⟨hxc.1, fρ'p, hxc, hv⟩, ⟨(ResU.CompS.comm h₈).1, π, ResU.CompS.comm h₈, hvπ⟩,
    (ResU.Valid.split h₈ hvπ).1⟩

theorem lower_valid {ρ : WRes} {μ : BoCa.BoLo.Heap} (h : ResU.Lower ρ μ) : ResU.Valid ρ := by
  obtain ⟨σ, hσ, -⟩ := h; exact ⟨σ, hσ⟩

/-- **`wpG` gives `wpGW []` at every `σ`**, with a postcondition that may use the validity of the
final resource. -/
theorem wpGW_nil_of_wpG {σ : List OEnt} {ls : List SRec} {e : Expr}
    {Q : List SRec → Expr → WProp} {Q' : List OEnt → List SRec → Expr → WProp}
    (hQ : ∀ ls' t ρ', ResU.Valid ρ' → Q ls' t ρ' → Q' [] ls' t ρ') {ρ : WRes}
    (h : wpG ls e Q ρ) : wpGW [] σ ls e Q' ρ := by
  intro ρf fρ ps h1 _ h3 h4 h5 _ A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h3 h4 h5 A k
  obtain ⟨hfπ, hpρ', hvρ'⟩ := hash_of_final a2 a5 (lower_valid a6) a8
  refine ⟨ρ', ρp, fρ', fρ'p, π, ρ, π, t, μ, μ', ps', ls', [], a1, a2, a3, a4, a5, a6, a7, a8,
    .nil _ _, .nil _ _, a9, a10, a11, a12, ⟨fun _ => ⟨rfl, fun p => ?_, fun x => ?_⟩,
      fun _ => ⟨fun p => ?_, fun x => ?_, fun _ h => absurd h List.not_mem_nil,
        compatW_nil_iff.mpr hfπ, compatW_nil_iff.mpr hpρ'⟩⟩, hQ _ _ _ hvρ' a15⟩
  · simp [immRecs, a13 p]
  · simp [a14 x]
  · simp [immRecs, a13 p]
  · simp [a14 x]

/-- **`wpGW_nil`**: at `τ = τ′ = []` and `σ = []`, `wpGW` is `wpG`. -/
theorem wpGW_nil {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} {ρ : WRes} :
    wpGW [] [] ls e (fun τ' ls' t ρ => τ' = [] ∧ Q ls' t ρ) ρ ↔ wpG ls e Q ρ := by
  constructor
  · intro h ρf fρ ps h1 h3 h4 h5 A k
    obtain ⟨ρ', ρp, fρ', fρ'p, π, ρc, πc, t, μ, μ', ps', ls', τ', a1, a2, a3, a4, a5, a6, a7,
      a8, a9, a10, a11, a12, a13, a14, a15, ⟨rfl, a16⟩⟩ :=
      h ρf fρ ps h1 (compatW_nil_iff.mpr h1) h3 h4 h5 (fun _ h => absurd h List.not_mem_nil) A k
    rw [close_nil_iff] at a9 a10
    subst ρc; subst πc
    have hps : ∀ p, p ∈ ps' ↔ p ∈ ps := by
      intro p
      by_cases ht : ∃ v : Val, t = .val v
      · rw [(a15.1 ht).2.1 p]; simp [immRecs]
      · rw [(a15.2 ht).1 p]; simp [immRecs]
    have hls : ∀ x, x ∈ ls' ↔ x ∈ ls := by
      intro x
      by_cases ht : ∃ v : Val, t = .val v
      · rw [(a15.1 ht).2.2 x]; simp
      · rw [(a15.2 ht).2.1 x]; simp
    exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a11, a12,
      a13, a14, hps, hls, a16⟩
  · exact wpGW_nil_of_wpG (fun _ _ _ _ h => ⟨rfl, h⟩)

/-- A cancel run of Core is a cancel run at `W` with nothing open, the owner `emp`. -/
theorem ewpTS_cancel_ewpW {T : OpTab} {N : List UInt32} {σ : List OEnt} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : ewpTS ls e (cancelTab T N) (fun _ _ _ => False) ρ) :
    ewpW [] σ ls e (withOwnerW (cancelTabW T N) (fun _ => emp)) (fun _ _ _ => False) ρ := by
  refine ewpW_fold (withOwnerW_mono (cancelTabW_mono T N) _) ?_
  refine wpGW_nil_of_wpG (fun ls' t ρ' _ hq => ?_) ((ewp_abortive (cancelTab_abortive T N)).mp h)
  rcases hq with ⟨v, -, hf⟩ | hq
  · exact absurd hf id
  · exact Or.inr ⟨ρ', PMap.empty, ResU.comp_empty_right ρ', ⟨rfl, hq⟩, rfl, trivial⟩

/-- **`ewpTS_ewpW`**: a Core `ewpTS` at `opTable T` is an `ewpW []` at `opTableW T`, at every `σ`. -/
theorem ewpTS_ewpW {T : OpTab} {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ) :
    ∀ σ, ewpW [] σ ls e (opTableW T) Q ρ := by
  refine ewp_ind (fun ls e ρ => ∀ σ, ewpW [] σ ls e (opTableW T) Q ρ) ?_ h
  intro ls e ρ hstep σ
  refine ewpW_fold (opTabW_mono T _) (wpGW_nil_of_wpG (fun ls' t ρ' hv hq => ?_) hstep)
  rcases hq with ⟨v, rfl, hv'⟩ | hq
  · exact Or.inl ⟨v, rfl, rfl, hv'⟩
  rcases hq with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨hpure, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    refine Or.inr (Or.inl ⟨K, n, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hc, hA,
      ⟨fun hq => ⟨hu hq, rfl⟩, fun ls'' he => ⟨fun w ρ₁ ρ₂ hB hc' => ?_, fun hq N hN hK => ?_⟩⟩,
      holds_nil ρk, compatW_nil_iff.mpr ⟨hc.1, ρ', hc, hv⟩⟩⟩)
    · exact (hcont ls'' he).1 w ρ₁ ρ₂ hB hc' σ
    · exact ewpTS_cancel_ewpW ((hcont ls'' he).2 hq N hN hK)
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hr⟩ := pure_sep_iff.mp hp
    exact Or.inr (Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄, rfl⟩
      ⟨ρ', PMap.empty, ResU.comp_empty_right ρ', hr, rfl, trivial⟩⟩)

end WorldW

end
