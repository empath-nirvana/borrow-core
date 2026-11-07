import Core.Chain.Rules834N
import Core.Chain.HandleS835N

/-!
# `[let]` at a row: the consistency a continuation is resumed at  `[spec §14, §19, §27]`

Core's `let_compatC` (`Core/EffFin.lean`) is `ewp_frame_plain` around `M`, the frame the context of
`N`, with `ent_plain` carrying a cancel through the frame. At the chain the same proof reaches one
more fact: `N`'s judgment is read at the run's view `c`, so the resource it starts from, `M`'s
value beside the frame, must be consistent with `c` (`SemJN`'s `ConsistentX`). The frame is (the
context's part, `gN_splitC`). `M`'s value is too when its run never stops (`rwp_consistentXV`, as
`bind_compatN` reads it); across a stop it is the continuation's share beside the answer the stop
was resumed at, and a row's table reads its answers at the view (`tabN`'s `ConsistentX c`), as
`SemJN` reads the resource a run starts from and `⊸` the argument's composite.

* `OpTabN.AnsC c T`: the answers of every entry of `T` are consistent with `c`.
* `erwp_consistentAns`: a run from a resource consistent with `c`, at a table whose answers are,
  returns consistent resources at every value it reaches, resumptions included (by induction on
  the index: at a stop the share is a part of a consistent valid resource, `consistentX_right`;
  the resumed composite is consistent by `consistentX_compS`). Its post also carries the index
  bound and validity, which the frame's context reads (`gN_le`).
* `erwp_idxLe`: a run's values are reached at indices up to its own, across its resumptions: the
  index bound the frame's context is read at when the bound value owns nothing.

`LetKW835N` reads `[let]` and `[await]` at `SemJN` (`let_compatN`, `let_compatN_persist`,
`await_compatN`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

/-- **The answers of a table are consistent with the view `c`.** -/
def OpTabN.AnsC (c : Loc → Option Life) (T : OpTabN) : Prop :=
  ∀ m i en, T m i = some en → ∀ k ls w ρ, en.PB k ls w ρ → ConsistentX c ρ

/-- **A run from a consistent resource, at a table whose answers are consistent, returns
consistent resources**, at every value it reaches across its resumptions, at an index up to `N`,
and valid. At a stop the share is a part of the stop's resource, consistent and valid
(`rwpG_consistentXV`, `consistentX_right`); a resumption starts from the share beside a
consistent answer (`consistentX_compS`), which the induction hypothesis reads. -/
theorem erwp_consistentAns {Φ : LocFam} {T : OpTabN} {c : Loc → Option Life} (hT : T.AnsC c)
    {Q : PostN} (N : Nat) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ → ConsistentX c ρ →
      erwp (ℍ := ℍ) Φ (opTableN T)
        (fun k ls v ρ => k ≤ N ∧ Q k ls v ρ ∧ ConsistentX c ρ ∧ ResU.Valid ρ) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h hc
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hcσ, hvσ⟩ => ?_) (rwpG_consistentXV h hc)
  rcases ht with ⟨v, hv, hq⟩ | ⟨K, m, i, v, en, hp⟩ | hr
  · exact Or.inl ⟨v, hv, by omega, hq, hcσ, hvσ⟩
  · obtain ⟨hpure, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hck := consistentX_right hcak hcσ hvσ
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hcak, hA, hu,
      fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, (hcont ls'' he).2⟩⟩⟩)
    have h₁ := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
    exact ih k' (by omega) (by omega) ls'' _ τ₂ h₁
      (consistentX_compS hcτ hck (hT m i en hpure.2.2.1 _ _ _ _ hB))
  · exact Or.inr (Or.inr hr)

/-- **A run's values are reached at indices up to its own**, across its resumptions. -/
theorem erwp_idxLe {Φ : LocFam} {T : OpTabN} {Q : PostN} (N : Nat) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (fun k ls v ρ => k ≤ N ∧ Q k ls v ρ) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, hq⟩ | ⟨K, m, i, v, en, hp⟩ | hr
  · exact Or.inl ⟨v, hv, by omega, hq⟩
  · obtain ⟨hpure, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hcak, hA, hu,
      fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, (hcont ls'' he).2⟩⟩⟩)
    have h₁ := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpC, show k' < n by omega, if_true] at h₁ ⊢
    exact ih k' (by omega) (by omega) ls'' _ τ₂ h₁
  · exact Or.inr (Or.inr hr)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
