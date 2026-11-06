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
was resumed at, and `tabN`'s answers are `vN B δ Θ` at any resource, consistent or not.

* `OpTabN.AnsC c T`: the answers of every entry of `T` are consistent with `c`.
* `erwp_consistentAns`: a run from a resource consistent with `c`, at a table whose answers are,
  returns consistent resources at every value it reaches, resumptions included (by induction on
  the index: at a stop the share is a part of a consistent valid resource, `consistentX_right`;
  the resumed composite is consistent by `consistentX_compS`). Its post also carries the index
  bound and validity, which the frame's context reads (`gN_le`).
* `let_compatN_ansC`: Core's `let_compatC`, step for step (`erwp_frame_plain`, `entN_plain`,
  `gN_noOwn`, `gN_persistent`), at a row whose table's answers are consistent with every view.
  `hAns` is a premise Core's rule does not have; `let_compatN` (without it) is not derived.
* `tabN_ansC_of_persistent`: `hAns` holds at a row whose answers are persistent types (their
  values own nothing, `vN_empty_of_persistent`).
* `let_compatN_persist`: the same proof binding a persistent type, with no premise on the answers:
  the bound value owns nothing, so `N` starts from the frame's resource (`erwp_idxLe` gives the
  index bound the frame's context is read at).
* `await_compatN`: Core's `await_compatC`, `[perform]`, `[case]`, `[sub]` and `[raise]` under
  `let_compatN_persist`, the answer at `1 + 1`.
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

/-- A row's table does not read the answer type. -/
theorem tabN_effOf_ret (S : Row) (A B : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    tabN (ℍ := ℍ) (CTy.effOf S A) δ Θ c = tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c := by
  induction S with
  | nil => simp [CTy.effOf, tabN]
  | cons o S ih => simp only [CTy.effOf, tabN]; rw [ih]

/-- **The answers of a row whose answer types are persistent are consistent with every view**:
their values own nothing (`vN_empty_of_persistent`). -/
theorem tabN_ansC_of_persistent {S : Row} (hS : ∀ o ∈ S, o.B.Persistent) (R : VTy) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) : (tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c).AnsC c := by
  intro m i en hT k ls w ρ hB
  obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
  have hB' : vN (ℍ := ℍ) o.B δ Θ k w ρ := hB
  rw [vN_empty_of_persistent _ (hS o (Row.find_mem hf).1) hB']
  exact consistentX_empty c

/-- **`[let]` at a row whose answers are consistent with the view** (Core's `let_compatC`):
`ewp_frame_plain` around `M` with the context of `N` as the frame, its cancels carried by
`ent_plain`, left behind owning nothing where the row cancels (`hW`), empty at an unrestricted
row (`hU`). `M`'s value is consistent with the run's view across its resumptions
(`erwp_consistentAns`), which is what `hAns` is read for: `N`'s judgment is at that view. Core's
rule has no `hAns`. -/
theorem let_compatN_ansC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Cancels → Γ₂.OwnFree) (hU : S.Unr → Ctx.Banged Γ₂)
    (hAns : ∀ δ Θ c, (tabN (ℍ := ℍ) (CTy.effOf S B) δ Θ c).AnsC c)
    (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    SemJN (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have hΦ := LocTy.view_down hΘ.1 c
  refine (cN_effOf S B δ Θ c n ls _ ρ).mpr (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, hc₂⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hM' := (cN_effOf S A δ Θ c n ls _ ρ₁).mp (hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁)
  rw [tabN_effOf_ret S A B] at hM'
  have hM'' := erwp_consistentAns (hAns δ Θ c) n n le_rfl ls _ ρ₁ hM' hc₁
  have hK : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).HasHnd m = false :=
    fun _ => by simp [Kont.HasHnd]
  have hC : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).Catches m = false :=
    fun _ => by simp [Kont.Catches]
  change erwp (ℍ := ℍ) _ _ _ n ls
    ((Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).plug (substAll γ M)) ρ
  refine erwp_frame_plain hΦ _ _ hK hC
    (fun _ σ => gN (ℍ := ℍ) δ Θ Γ₂ γ n σ ∧ ConsistentX c σ) (fun _ _ _ _ h => h)
    (fun m i en hT ls ls' ρ σ ρ' hc' he =>
      (tabN_down _ δ Θ hΘ.1 c).wcl m i en hT ls ls' ρ σ ρ' hc' he)
    (fun _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ _ _ ?_ n ls _ ρ₁ hM'' ρ₂ ρ ⟨hg₂, hc₂⟩ hcρ
  · rintro m i en hT ha ls' σ ⟨h, -⟩
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
    refine gN_noOwn (hW ⟨o, (Row.find_mem hf).1, ?_⟩) h
    simp only [entN, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
    exact ha.2
  · rintro m i en hT hq ls' σ ⟨h, -⟩
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
    exact gN_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · rintro m i en hT ha hq k ls' K₁ ρ' σ ρ'' hcan ⟨hσ, -⟩ hc'
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
    exact entN_plain hΦ _ hK (hC 0) (gN_noOwn (hW ⟨o, (Row.find_mem hf).1, hq⟩) hσ) o hcan hc'
  · rintro k ls' v σ ⟨σ₁, σ₂, hcσ, ⟨hkn, hv, hcv, -⟩, hg₂', hc₂'⟩
    refine (cN_effOf S B δ Θ c k ls' _ σ).mp ?_
    refine cN_head (CTy.effOf S B) δ Θ hΘ.1 c k ls' σ .hole _ _
      (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
      from (substAll_cons_psub v γ N).symm]
    exact hN δ (v :: γ) Θ c k ls' σ hδ hΘ (consistentX_compS hcσ hcv hc₂') hlw₂
      (gN_live_cons hcσ hv (gN_le hkn hg₂'))

/-- **`[let]` binding a persistent type** (Core's `let_compatC`, the bound value owning nothing):
`M`'s value holds `∅`, so the resource `N` starts from is the frame's, consistent with the view
from the start; no premise on the row's answers is read. -/
theorem let_compatN_persist {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Cancels → Γ₂.OwnFree) (hU : S.Unr → Ctx.Banged Γ₂)
    (hA : A.Persistent)
    (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    SemJN (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  have hΦ := LocTy.view_down hΘ.1 c
  refine (cN_effOf S B δ Θ c n ls _ ρ).mpr (erwp_of_valid fun hv => ?_)
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, hc₂⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hM' := (cN_effOf S A δ Θ c n ls _ ρ₁).mp (hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁)
  rw [tabN_effOf_ret S A B] at hM'
  have hM'' := erwp_idxLe n n le_rfl ls _ ρ₁ hM'
  have hK : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).HasHnd m = false :=
    fun _ => by simp [Kont.HasHnd]
  have hC : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).Catches m = false :=
    fun _ => by simp [Kont.Catches]
  change erwp (ℍ := ℍ) _ _ _ n ls
    ((Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).plug (substAll γ M)) ρ
  refine erwp_frame_plain hΦ _ _ hK hC
    (fun _ σ => gN (ℍ := ℍ) δ Θ Γ₂ γ n σ ∧ ConsistentX c σ) (fun _ _ _ _ h => h)
    (fun m i en hT ls ls' ρ σ ρ' hc' he =>
      (tabN_down _ δ Θ hΘ.1 c).wcl m i en hT ls ls' ρ σ ρ' hc' he)
    (fun _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ _ _ ?_ n ls _ ρ₁ hM'' ρ₂ ρ ⟨hg₂, hc₂⟩ hcρ
  · rintro m i en hT ha ls' σ ⟨h, -⟩
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
    refine gN_noOwn (hW ⟨o, (Row.find_mem hf).1, ?_⟩) h
    simp only [entN, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
    exact ha.2
  · rintro m i en hT hq ls' σ ⟨h, -⟩
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
    exact gN_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · rintro m i en hT ha hq k ls' K₁ ρ' σ ρ'' hcan ⟨hσ, -⟩ hc'
    obtain ⟨o, hf, rfl⟩ := tabN_effOf_some_find hT
    exact entN_plain hΦ _ hK (hC 0) (gN_noOwn (hW ⟨o, (Row.find_mem hf).1, hq⟩) hσ) o hcan hc'
  · rintro k ls' v σ ⟨σ₁, σ₂, hcσ, ⟨hkn, hv⟩, hg₂', hc₂'⟩
    obtain rfl := vN_empty_of_persistent _ hA hv
    rw [eq_of_compS_empty_left hcσ]
    refine (cN_effOf S B δ Θ c k ls' _ σ₂).mp ?_
    refine cN_head (CTy.effOf S B) δ Θ hΘ.1 c k ls' σ₂ .hole _ _
      (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
      from (substAll_cons_psub v γ N).symm]
    exact hN δ (v :: γ) Θ c k ls' σ₂ hδ hΘ hc₂' hlw₂
      (gN_live_cons (compS_empty_left σ₂) hv (gN_le hkn hg₂'))

theorem noNuSpine_effOf (S : Row) (R : VTy) : noNuSpine (CTy.effOf S R) := by
  cases S <;> trivial

/-- **`[await-c]` at `SemJN`** (Core's `await_compatC`): `[perform]` of the cancellable `a`, then
a `case` whose `inl` arm returns and whose `inr` arm raises the cancel target `c`, each by its own
compatibility lemma, under `[let]`. The bound answer is at `1 + 1`, persistent, so the `[let]` is
`let_compatN_persist`. -/
theorem await_compatN {Δ : LifeCtx} {S : Row} {n : UInt32} {a c : OpSig}
    (hfa : Row.find S n 0 = some a) (ha : a.Cancellable) (haA : a.A = .unit)
    (hfc : Row.find S n 1 = some c) (hc : c.CancelTarget) :
    SemJN (ℍ := ℍ) Δ [] (awaitE n) (.comp (CTy.effOf S .unit)) := by
  obtain ⟨-, han, hai⟩ := Row.find_mem hfa
  obtain ⟨-, hcn, hci⟩ := Row.find_mem hfc
  obtain ⟨-, hq, hB⟩ := ha
  obtain ⟨-, hcab, hcA⟩ := hc
  have hna : a.abort = false := by simp [OpSig.abort, hq]
  have hunit : SemJN (ℍ := ℍ) Δ [] (.val .unit) (.val a.A) := by
    rw [haA]
    intro δ γ Θ c' n' ls ρ _ _ _ _ hg
    obtain rfl : ρ = PMap.empty := hg
    exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩
  have hP : SemJN (ℍ := ℍ) Δ [] (performE (opArgE n 0 (.val .unit)))
      (.comp (CTy.effOf S (.sum .unit .unit))) := by
    have h := perform_compatN (Δ := Δ) (Γ := []) (V := .val .unit) (o := a)
      (by rw [han, hai]; exact hfa) hna hunit
    rw [han, hai, hB] at h; exact h
  have h₁ : SemJN (ℍ := ℍ) Δ [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩] (.var 0)
      (.comp (CTy.effOf S .unit)) :=
    sub_compatN (S := []) (RowLe.nil S) (var_compatN (.here (.cons .nil)))
  have h₂ : SemJN (ℍ := ℍ) Δ [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩]
      (raiseE (opArgE n 1 (.var 0))) (.comp (CTy.effOf S .unit)) := by
    have h := raise_compatN (Δ := Δ) (Γ := [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩])
      (V := .var 0) (o := c) (B := .unit) (by rw [hcn, hci]; exact hfc) hcab
      (fun _ _ _ _ _ h => vN_noOwn_of_ownFree (by rw [hcA]; exact .unit) h)
      (by rw [hcA]; exact var_compatN (.here (.cons .nil)))
    rw [hcn, hci] at h; exact h
  exact let_compatN_persist .nil (fun _ s hs => absurd hs List.not_mem_nil)
    (fun _ s hs => absurd hs List.not_mem_nil) (by decide) hP
    (sumE_compatN (noNuSpine_effOf S .unit) (.left .nil) (var_compatN (.here .nil)) h₁ h₂)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
