import Core.Chain.ConstKW835N
import Core.Chain.HandleT835N
import Core.Chain.HandleTK835N

/-!
# `[handle]` at clauses that resume `κ` in tail position, at the typed world  `[spec §14, §19]`

`HandleT835N`'s handler at `cN`: `erwp_handle_tail` at `erwpK` and `handleT_compatN` at `SemJN`,
each step `erwp_handle_tail₀`'s, at the relation at `KW`.

* `erwpK_postPA`: the pre-pass. The handled run's stops are consistent with the view of their
  world, and their worlds valid (`rwpG_consistentXV`, `KW.Owed`); a stop at the handler's name
  records that in its payload, and owes its continuation also at the worlds at its location typing
  and view at a floor no higher (`KW.owed_of_post`, from the share's consistency at the stop).
* `erwpK_frame_plain_orI`: the plain frame around a run at a table below, read at the worlds an
  invariant holds at, the frame moved along a stop's order at the floor the stop chose.
* `erwp_handle_tail`: `erwpK_handle_leI` at the pre-passed table. A clause pays its `β` step, then
  runs its answering function at its must-resume row from the floor `f` the handled stop chose
  (`erwpK_flr_tabN`), under the resume frame. Every world that run reaches is owed at `f` from
  the clause's world, at the frame's share (`KW.Owed.floor_le`, `KW.Owed.trans`), so `κ` is
  resumed at the world the function's value is posted at.
* `handleT_compatN`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

variable {ι : Type}

/-- **A paid deterministic step in front of an `erwpK`** (`erwp_step`). -/
theorem erwpK_step {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} {n : Nat} {ls : List SRec} {e e' : Expr}
    {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e' ρ) : erwpK (ℍ := ℍ) V Φ Tb Q x (n + 1) ls e ρ :=
  erwpK_fold_at hL le_rfl (rwpG_step hdet (erwpK_unfold_at hL (Nat.le_succ n) h))

/-! ### The payloads at the handler's name, read at the view and the world -/

/-- An entry whose payload is read at the view `c` with `I` holding, owing its continuation also
at the worlds `P` allows. -/
def OpEntK.withPAP (c : Loc → Option Life) (I : Prop) (P : ι → Prop) (en : OpEntK ι) :
    OpEntK ι :=
  { en with PA := fun k ls v ρ => en.PA k ls v ρ ∧ ConsistentX c ρ ∧ I,
            wk := fun f y ρ => en.wk f y ρ ∨ P y }

/-- **The table whose entries of the name `n₀` are `OpEntK.withPAP`.** -/
def OpTabK.withPAP (c : Loc → Option Life) (I : Prop) (P : ι → Prop) (n₀ : UInt32)
    (T : OpTabK ι) : OpTabK ι :=
  fun m i => if m = n₀ then (T m i).map (OpEntK.withPAP c I P) else T m i

section
variable {c : Loc → Option Life} {I : Prop} {P : ι → Prop} {n₀ : UInt32}

theorem OpTabK.withPAP_ne (T : OpTabK ι) {m : UInt32} (hm : m ≠ n₀) (i : UInt32) :
    T.withPAP c I P n₀ m i = T m i := by
  simp [OpTabK.withPAP, hm]

theorem OpTabK.withPAP_self {T : OpTabK ι} {i : UInt32} {en' : OpEntK ι}
    (h : T.withPAP c I P n₀ n₀ i = some en') : ∃ en, T n₀ i = some en ∧ en' = en.withPAP c I P := by
  simp only [OpTabK.withPAP, if_true] at h
  obtain ⟨en, hT, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨en, hT, rfl⟩

/-- An entry of `T.withPAP` is an entry of `T`, its payload read further, owing also at `P`. -/
theorem OpTabK.withPAP_inv {T : OpTabK ι} {m i : UInt32} {en' : OpEntK ι}
    (h : T.withPAP c I P n₀ m i = some en') :
    ∃ en, T m i = some en ∧ en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PB = en.PB ∧
      en'.fin = en.fin ∧ en'.wc = en.wc ∧ (∀ k ls v ρ, en'.PA k ls v ρ → en.PA k ls v ρ) ∧
      ∀ f y ρ, en'.wk f y ρ → en.wk f y ρ ∨ P y := by
  by_cases hm : m = n₀
  · subst hm
    obtain ⟨en, hT, rfl⟩ := OpTabK.withPAP_self h
    exact ⟨en, hT, rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ h => h.1, fun _ _ _ h => h⟩
  · rw [OpTabK.withPAP_ne T hm] at h
    exact ⟨en', h, rfl, rfl, rfl, rfl, rfl, fun _ _ _ _ h => h, fun _ _ _ h => Or.inl h⟩

/-- An entry of `T` has its `T.withPAP` entry, where `I` holds. -/
theorem OpTabK.withPAP_some {T : OpTabK ι} {m i : UInt32} {en : OpEntK ι} (h : T m i = some en)
    (hI : I) :
    ∃ en', T.withPAP c I P n₀ m i = some en' ∧ en'.q = en.q ∧ en'.abort = en.abort ∧
      en'.PB = en.PB ∧ en'.fin = en.fin ∧ en'.wc = en.wc ∧
      (∀ f y ρ, en'.wk f y ρ → en.wk f y ρ ∨ P y) ∧
      ∀ k ls v ρ, en.PA k ls v ρ → ConsistentX c ρ → en'.PA k ls v ρ := by
  by_cases hm : m = n₀
  · subst hm
    exact ⟨en.withPAP c I P, by simp [OpTabK.withPAP, h], rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ h => h, fun _ _ _ _ h₁ h₂ => ⟨h₁, h₂, hI⟩⟩
  · exact ⟨en, by rw [OpTabK.withPAP_ne T hm, h], rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ h => Or.inl h, fun _ _ _ _ h _ => h⟩

theorem OpTabK.withPAP_downAt {Inv : ι → Prop} {T : OpTabK ι} (hT : T.DownAt Inv) :
    (T.withPAP c I P n₀).DownAt Inv where
  pa := fun m i en h k ls v ρ hp => by
    by_cases hm : m = n₀
    · subst hm
      obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self h
      exact ⟨hT.pa _ _ _ hT₀ k ls v ρ hp.1, hp.2⟩
    · rw [OpTabK.withPAP_ne T hm] at h
      exact hT.pa _ _ _ h k ls v ρ hp
  fin := fun m i en P' h hP y hy k ls e ρ hp => by
    obtain ⟨en₀, hT₀, -, -, -, hfin, -⟩ := OpTabK.withPAP_inv h
    exact hT.fin _ _ _ _ hT₀ (hfin ▸ hP) y hy k ls e ρ hp

end

/-- **The handled run, its stops at the handler's name read at their world** (`erwpK_consistentPA`
with a world invariant and more worlds owed): from a resource consistent with the view of a world
`I` holds at, at a table whose answers are consistent with the resumption world's view and whose
entries owe only worlds `I` holds at, the run's values are consistent and posted at worlds `I`
holds at; a stop at `n₀` records the payload's consistency and `I` at its world, and owes its
continuation also at the worlds `P` allows: at such a world, the stop's share being consistent
with the view of its own world, the entry owes it there (`hPw`). -/
theorem erwpK_postPA {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life}
    {T : ι → OpTabK ι} {c : ι → Loc → Option Life} {I : ι → Prop} {P : ι → ι → Prop}
    (hT : ∀ x m i en, T x m i = some en → ∀ y k ls w ρ, en.PB y k ls w ρ → ConsistentX (c y) ρ)
    (hwkc : ∀ x m i en, T x m i = some en → ∀ f y ρ, en.wk f y ρ → ConsistentX (c x) ρ →
      ConsistentX (c y) ρ)
    (hwkI : ∀ x m i en, T x m i = some en → ∀ f y ρ, en.wk f y ρ → I y)
    (hPw : ∀ x m i en, T x m i = some en → ∀ f, f ≤ fl x → ∀ y ρ, P x y →
      ConsistentX (c x) ρ → I x → en.wk f y ρ)
    (hVc : ∀ x y, V x y → c y = c x) (hVI : ∀ x y, V x y → I x → I y) (n₀ : UInt32)
    {Q : ι → PostN} :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls e ρ →
      ConsistentX (c x) ρ → I x →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) ((T z).withPAP (c z) (I z) (P z) n₀))
        (fun y k ls v ρ => (Q y k ls v ρ ∧ ConsistentX (c y) ρ) ∧ I y) x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h hc hI
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hcσ, hvσ⟩ => ?_) (rwpG_consistentXV h hc)
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, hv, y, hy, ⟨hq, (hVc x y hy).symm ▸ hcσ⟩, hVI x y hy hI⟩
  · obtain ⟨⟨h₁, h₂, hTe, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', hq, hab, hPB, hfin, hwc, hwk, hPA⟩ :=
      OpTabK.withPAP_some (c := c x) (P := P x) (n₀ := n₀) hTe hI
    have hck := consistentX_right hcak hcσ hvσ
    refine Or.inr (Or.inl ⟨K, m, i, v, en', pure_sep_mk ⟨h₁, h₂, hTe', hab ▸ ha⟩ ⟨ρa, ρk, hcak,
      hPA _ _ _ _ hA (consistentX_left hcak hcσ hvσ), fun hq' => hu (hq ▸ hq'), f, hf,
        fun y hy ls'' he => ?_⟩⟩)
    have hy' : en.wk f y ρk :=
      (hwk f y ρk hy).elim id (fun hP => hPw x m i en hTe f hf y ρk hP hck hI)
    rw [hwc] at he
    refine ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' P' hP' => ?_⟩
    · rw [hPB] at hB
      have h₁ := (hcont y hy' ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      exact ih k' (by omega) y ls'' _ τ₂ h₁
        (consistentX_compS hcτ (hwkc x m i en hTe f y ρk hy' hck) (hT x m i en hTe _ _ _ _ _ hB))
        (hwkI x m i en hTe f y ρk hy')
    · rw [hq] at hq'
      exact (hcont y hy' ls'' he).2 hq' P' (hfin ▸ hP')
  · obtain ⟨⟨h₁, h₂, hTe, ha⟩, ρa, ρn, hcan, ⟨hPA₀, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab, -, -, -, -, hPA⟩ :=
      OpTabK.withPAP_some (c := c x) (P := P x) (n₀ := n₀) hTe hI
    exact Or.inr (Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨h₁, h₂, hTe', hab ▸ ha⟩ ⟨ρa, ρn, hcan,
      ⟨hPA _ _ _ _ hPA₀ (consistentX_left hcan hcσ hvσ), hnA⟩, hnn⟩⟩)

/-! ### The plain frame below a wider table, at an invariant -/

/-- **A plain frame around a computation at a table below the outer one, at the worlds `Inv` holds
at** (`erwpK_frame_plain_or` read as `erwpK_frame_plainI` reads `erwpK_frame_plain`): the run
starts at such a world, the post order keeps `Inv`, and every world an entry of the inner table owes
at is one. The frame is read again at the resumption world at the floor the stop chose, no higher
than the run's. -/
theorem erwpK_frame_plain_orI {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) (hVI : ∀ x y, V x y → Inv x → Inv y) {fl : ι → Life}
    {T T' : ι → OpTabK ι} (hTT : ∀ x, (T x).Le (T' x))
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T' y)).Le (opTableK (fl x) (T' x)))
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false)
    (Fr : ι → List SRec → WProp)
    (hFs : ∀ x ls ls', (∀ a, a ∈ ls' ↔ a ∈ ls) → ∀ ρ, Fr x ls ρ → Fr x ls' ρ)
    (hFV : ∀ x y, V x y → ∀ ls ρ, Fr x ls ρ → Fr y ls ρ)
    (hwkI : ∀ x n i en, T x n i = some en → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hwl : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → en.wc ls ls' ρ)
    (hkl : ∀ x n i en, T x n i = some en → ∀ f y ρ σ ρ', ResU.CompS ρ σ ρ' → ResU.Valid ρ' →
      en.wk f y ρ' → en.wk f y ρ)
    (hFe : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → Fr x ls σ → Fr x ls' σ)
    (hFk : ∀ x n i en, T x n i = some en → ∀ f, f ≤ fl x → ∀ y ls ρ σ ρ', ResU.CompS ρ σ ρ' →
      ResU.Valid ρ' → en.wk f y ρ' → Fr x ls σ → Fr y ls σ)
    (hW : ∀ x n i en, T x n i = some en → en.abort = true → ∀ ls ρ, Fr x ls ρ → NoOwn ρ)
    (hU : ∀ x n i en, T x n i = some en → en.q = .unr → ∀ ls ρ, Fr x ls ρ → ρ = PMap.empty)
    (hK : ∀ x n i en, T x n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ y k ls K₁ ρ σ ρ', cancelOKK en y k ls K₁ ρ → Fr y ls σ → ResU.CompS ρ σ ρ' →
        cancelOKK en y k ls (K.comp K₁) ρ')
    (Q₁ Q : ι → PostN)
    (hkv : ∀ y, Inv y → ∀ k ls (v : Val) ρ, (Q₁ y k ls v ⋆ Fr y ls) ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T' z)) Q y k ls (K.plug v.1) ρ) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q₁ x n ls e ρ →
      ∀ ρ₂ ρ', Fr x ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T' z)) Q x n ls (K.plug e) ρ' := by
  have hL' : ∀ z, (opTableK (fl z) (T' z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρ h ρ₂ ρ' hF hc
  rw [erwpK_eq] at h ⊢
  refine rwpG_bind (hΦ x hx) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hcσ, hp, hF'⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (Fr x) (hFs x) hc h hF))
  rcases hp with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact erwpK_shift hVt hΦV hTV hL' hy hk
      (hkv y (hVI x y hy hx) k ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFV x y hy ls' σ₂ hF'⟩)
  · -- a `perform`: the frame joins the continuation's share, at the entry above
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    have hvk : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvσ).2
    obtain ⟨en', hT', hq, hab, hPA, hPB, hwc, hwk, hfl⟩ := hTT x m i en hT
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', hab ▸ ha⟩ ⟨ρa, ρk', hcσ',
        hPA ▸ hA, fun hq' => ?_, f, hf, fun y hy ls'' he =>
          ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_, fun hq' P hP => ?_⟩⟩⟩))
    · rw [hu (hq.trans hq'), hU x m i en hT (hq.trans hq') ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · rw [← hwc] at he
      have hy₀ := hwk f y ρk' hy
      have hyk := hkl x m i en hT f y ρk σ₂ ρk' hk' hvk hy₀
      have hFy := hFk x m i en hT f hf y ls'' ρk σ₂ ρk' hk' hvk hy₀
        (hFe x m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF')
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont y hyk ls'' (hwl x m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).1 k' hk'' w τ₁ z
        (hPB ▸ hB) hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y (hwkI x m i en hT f y ρk hyk) ls'' _ z h₁ σ₂ τ₂ hFy hcz
    · rw [← hwc] at he
      have hq'' : en.q ≠ .lin := hq ▸ hq'
      have hy₀ := hwk f y ρk' hy
      have hyk := hkl x m i en hT f y ρk σ₂ ρk' hk' hvk hy₀
      have hFy := hFk x m i en hT f hf y ls'' ρk σ₂ ρk' hk' hvk hy₀
        (hFe x m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF')
      exact finLeSK_apply (hfl ha hq'') hP (fun P₀ hP₀ => hK x m i en hT ha hq'' y k ls'' K₁ ρk
        σ₂ ρk' (fun P₁ hP₁ => (hcont y hyk ls'' (hwl x m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).2
          hq'' P₁ hP₁) hFy hk' P₀ hP₀)
  · -- a `raise`: the frame is left behind
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨ρn', hn', hcσ'⟩ := compS_reassoc hcan hcσ
    obtain ⟨en', hT', -, hab, hPA', -⟩ := hTT x m i en hT
    have hKo : (K.comp K₁).Catches m = false := by rw [catches_comp, hC, hK₁]; rfl
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', hab ▸ ha⟩ ⟨ρa, ρn', hcσ',
        ⟨hPA' ▸ hPA, hnA⟩, noOwn_compS hn' hn (hW x m i en hT ha ls' σ₂ hF')⟩⟩))

/-! ### The orders across floors -/

/-- **`KW.Owed` at a floor is `KW.Owed` at every floor above it**: less of the world above is
kept. -/
theorem KW.Owed.floor_le {x y : KW} {f₁ f : Life} {ρ : WRes} (h : x.Owed f₁ y ρ) (hf : f₁ ≤ f) :
    x.Owed f y ρ :=
  ⟨h.1.mono hf, h.2.1, h.2.2.1, h.2.2.2.1, fun g hg hx => h.2.2.2.2 g (le_trans hf hg) hx⟩

/-- **A world owed from a world at the same location typing and view, at a floor no higher, is
owed from it.** -/
theorem KW.Owed.of_post {x x₁ y : KW} {f : Life} {ρ : WRes} (hx : x.Post x₁)
    (h : x₁.Owed f y ρ) : x.Owed f y ρ := by
  obtain ⟨hΘ, -, hlo⟩ := hx
  refine ⟨hΘ ▸ h.1, h.2.1, h.2.2.1, le_trans h.2.2.2.1 hlo, fun g hg hgx => ?_⟩
  exact h.2.2.2.2 g hg (hΘ ▸ hgx)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal clauseAt capTag)

/-! ### The handled row's table -/

/-- `cN`'s table is the family's at `rdN`, entry for entry. -/
theorem tabF_of_tabN {F : CTy} {δ : LSub} {x : KW} {m i : UInt32} {en : OpEntK KW}
    (h : tabN (ℍ := ℍ) F δ x m i = some en) : tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () F x m i = some en := by
  rwa [tabN_eq] at h

/-- An operation of another name in `Σ` extended by the handler's effect is `Σ`'s
(`tabN_ofEff_ne`), at the typed world. -/
theorem tabN_ofEff_neK {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    (A R : VTy) (δ : LSub) (x : KW) {m i : UInt32} (hm : m ≠ n) :
    tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ x m i =
      tabN (ℍ := ℍ) (CTy.effOf S R) δ x m i := by
  rw [tabN_eq, tabN_eq, tabF_effOf_find, tabF_effOf_find, Row.find_append,
    Row.find_ofEff_ne n E 0 fs m i hm]
  rfl

/-- **An operation of the handler's name is the effect's `j`-th, at index `j`**
(`tabN_ofEff_self`), at the typed world. -/
theorem tabN_ofEff_selfK {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {A : VTy} {δ : LSub} {x : KW} (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    {i : UInt32} {en : OpEntK KW}
    (hT : tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ x n i = some en) :
    ∃ j, ∃ hj : j < E.length, i.toNat = j ∧ i = UInt32.ofNat (0 + j) ∧
      en = (rdN (ℍ := ℍ) δ).ent () n E[j].1 E[j].2.1 E[j].2.2
        (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (fs j)) x := by
  obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find (tabF_of_tabN hT)
  have hfo : Row.find (Row.ofEff n E 0 fs) n i = some o := by
    rw [Row.find_append] at hf
    cases h₁ : Row.find (Row.ofEff n E 0 fs) n i with
    | some o' => rw [h₁] at hf; exact hf
    | none =>
        rw [h₁] at hf
        obtain ⟨hm, hn, -⟩ := Row.find_mem hf
        exact absurd hn (hnS o hm)
  obtain ⟨-, j, hj, rfl, rfl⟩ := Row.find_ofEff n E 0 fs n _ o hfo
  have hjn : (UInt32.ofNat (0 + j)).toNat = j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  exact ⟨j, hj, hjn, rfl, rfl⟩

/-- **A handler records its effect's qualifiers** (`capTag_ofEffN`), at the typed world. -/
theorem capTag_ofEffK {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    {A : VTy} {δ : LSub} {x : KW} (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (i : UInt32) (en : OpEntK KW)
    (hT : tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ x n i = some en) :
    capTag (qualsVal (E.map Prod.fst)).1 i.toNat = en.q.tag := by
  obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_selfK hnS hlen hT
  rw [hji, capTag_qualsVal _ j (by simpa using hj)]
  simp [RowRd.ent]

/-- The frame conditions at a row of must-resume operations (`lin_condsN`), at the typed world. -/
theorem lin_condsK {SN : Row} (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false) {B : VTy}
    {δ : LSub} {x : KW} {m i : UInt32} {en : OpEntK KW}
    (h : tabN (ℍ := ℍ) (CTy.effOf SN B) δ x m i = some en) : en.q = .lin ∧ en.abort = false := by
  obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find (tabF_of_tabN h)
  have ho := hLin o (Row.find_mem hf).1
  simp [RowRd.ent, ho.1]

/-- An entry of `cN`'s table owes only worlds whose location typing is `OK`, whose view its share
is consistent with, along `ExtR` (`tabF_wkC`). -/
theorem tabN_wkC (δ : LSub) (G : CTy) (x : KW) (m i : UInt32) (en : OpEntK KW)
    (hT : tabN (ℍ := ℍ) G δ x m i = some en) (f : Life) (y : KW) (ρ : WRes)
    (hy : en.wk f y ρ) : x.Owed f y ρ := by
  obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT)
  exact hy

/-! ### The answering functions -/

/-- **The answering functions at `vN`** (`ansesTy_atN₀`). -/
theorem ansesTy_atN {S SN : Row} {R : VTy} {δ : LSub} {Θ : LocTy} {k : Nat} :
    ∀ (E : List (Qual × VTy × VTy)) {vc : Val} {ρ : WRes},
      vN (ℍ := ℍ) (ansesTy S SN R E) δ Θ k vc ρ →
      ∀ j (h : j < E.length), ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vN (ℍ := ℍ) (ansTy S SN R E[j]) δ Θ k g PMap.empty
  | [], _, _, _, j, h => by simp at h
  | o :: E, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, ρ₁, ρ₂, rfl, -, hg, hr⟩ := h
      have he : ρ₁ = PMap.empty := vN_empty_of_persistent _ (ansTy_persistent S SN R o) hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := ansesTy_atN E hr j (by simpa using hj)
          exact ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), by simpa using hg'⟩

/-! ### The handler -/

/-- The worlds a handled stop also owes its continuation at: the stop's location typing and view,
at a floor no higher, valid. -/
def postOK (x y : KW) : Prop := x.Post y ∧ y.Θ.OK

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {S SN : Row}
  {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}

/-- **A tail-resuming handler at the typed world** (`erwp_handle_tail₀`): `erwpK_handle_leI` at
the handled row's table pre-passed by `erwpK_postPA`. A clause pays its `β` step and runs its
answering function at its must-resume row, from the floor `f` the handled stop chose
(`erwpK_flr_tabN`), under the resume frame (`erwpK_frame_plain_orI`, from `Σ_N` to `Σ`). The
frame is `κ`'s relation, with the world reached owed from the clause's at `f` at the frame's share:
at the start by `postOK`, and across each of the function's stops, taken at a floor no higher than
`f`, by `KW.Owed.floor_le` and `KW.Owed.trans`. The function's value, consistent with the view of
the world it is posted at (`erwpK_consistentAns`), is the answer `κ` is resumed at there. -/
theorem erwp_handle_tail (hΘ : Θ.OK) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    {vr vc : Val} {N : Nat}
    (hVr : vN (ℍ := ℍ) (retTy S A R) δ Θ N vr PMap.empty)
    (hVc : vN (ℍ := ℍ) (ansesTy S SN R E) δ Θ N vc PMap.empty) {lo : Life} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ z))
      (fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) ⟨Θ, c, lo⟩ N ls e ρ)
    (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S R) δ z))
      (fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) ⟨Θ, c, lo⟩ N ls (hndE (tailH n E vr vc) e) ρ := by
  set Tin : KW → OpTabK KW := fun z =>
    tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ z with hTin
  set Tout : KW → OpTabK KW := fun z => tabN (ℍ := ℍ) (CTy.effOf S R) δ z with hTout
  have hQout : ∀ z : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) :=
    fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  have hVt : ∀ x y z : KW, KW.PostK x y → KW.PostK y z → KW.PostK x z :=
    fun _ _ _ (h₁ : _ = _) (h₂ : _ = _) => h₂.trans h₁
  have h' := erwpK_postPA (ℍ := ℍ) (V := KW.PostK) (fl := fun z : KW => z.lo) (T := Tin)
    (c := fun z : KW => z.c) (I := fun z : KW => z.Θ.OK) (P := postOK)
    (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en (tabF_of_tabN hT) y k ls w ρ hB)
    (fun x m i en hT f y ρ hy _ => (tabN_wkC δ _ x m i en hT f y ρ hy).2.2.1)
    (fun x m i en hT f y ρ hy => (tabN_wkC δ _ x m i en hT f y ρ hy).2.1)
    (fun x m i en hT f _ y ρ hP hcx hx => by
      obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT)
      exact KW.owed_of_post hP.1 hx f hcx)
    (fun x y (h : y = x) => by rw [h]) (fun x y (h : y = x) hx => h ▸ hx) n N ⟨Θ, c, lo⟩ ls e ρ
    h hc hΘ
  refine erwpK_handle_leI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
    (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo) hVt
    (fun z hz => LocTy.view_down hz.1 z.c) (fun x y (h : y = x) => by rw [h]) N
    (fun z => (Tin z).withPAP z.c z.Θ.OK (postOK z) n) Tout
    (fun x _ => OpTabK.withPAP_downAt ⟨(tabN_downI_OK _ δ x).pa, (tabN_downI_OK _ δ x).fin⟩)
    (fun x _ => opTableK_downI (tabN_downI_OK _ δ x))
    (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
    n (fun x m i hm => by rw [OpTabK.withPAP_ne _ hm]; exact tabN_ofEff_neK A R δ x hm)
    (qualsVal (E.map Prod.fst)) vr ⟨tailTuple E 0 (.val vc), isVal_tailTuple _ E 0⟩ _ _ hQout
    ?_ ?_ ?_ (fun _ => none) (fun _ _ _ _ _ _ _ h => by cases h) KW.postK_refl ?_
    (fun _ _ h => by cases h) ?_ ?_ N le_rfl ⟨Θ, c, lo⟩ hΘ ls e ρ h'
  · intro x i en hT _
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    exact capTag_ofEffK hnS hlen i en₀ hT₀
  · intro x m i en hT ls₁ ls₂ ρ₁ ρ₂ ρ₀ hc₁ he
    obtain ⟨en₀, hT₀, -, -, -, -, hwc, -⟩ := OpTabK.withPAP_inv hT
    rw [hwc] at he ⊢
    exact tabF_wcl (tabF_of_tabN hT₀) hc₁ he
  · intro x i en hT _ f y ρ₁ ρ₂ ρ₀ hc₁ hv₁ hy
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    exact hy.imp (tabF_wkLeft (rdN_ok δ) (tabF_of_tabN hT₀) hc₁ hv₁) id
  · intro x m i en hT _ f y ρ₁ hy
    obtain ⟨en₀, hT₀, -, -, -, -, -, -, hwk⟩ := OpTabK.withPAP_inv hT
    rcases hwk f y ρ₁ hy with hy' | hy'
    · exact (tabN_wkC δ _ x m i en₀ hT₀ f y ρ₁ hy').2.1
    · exact hy'.2
  · -- `[ret]`: `h_ret` at the value, at the world it is posted at
    rintro x k hk ls' v σ ⟨⟨hv, hcv⟩, hxOK⟩
    obtain ⟨-, hr⟩ := vN_extR (retTy S A R) δ N vr PMap.empty (LocTy.extR_empty Θ x.Θ) hVr
    exact (cN_effOf S R δ x.Θ x.c k ls' _ σ).mp (hr x.Θ (LocTy.extR_refl _ _) hxOK x.c
      (consistentX_empty _) ls' x.c k hk v σ σ (compS_empty_left σ) hv hcv) x.lo
  · intro x i en' hT
    obtain ⟨en, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_selfK hnS hlen hT₀
    obtain ⟨g, hg, hVg⟩ := ansesTy_atN E
      (vN_extR (ansesTy S SN R E) δ N vc PMap.empty (LocTy.extR_empty Θ x.Θ) hVc) j hj
    refine ⟨⟨tailClause j (E[j].2.2.isZero && E[j].1 != .lin) (.val vc), isVal_tailClause _ _ _⟩,
      by rw [hji, clauseAt_tailTuple _ E 0 j hj]; simp, fun ha k hk ls' v κ σ hσ => ?_,
      fun ha k hk ls' v σ hσ => ?_⟩
    · -- the clause pays its `β` step, then resumes `κ` with `g v` under the resume frame
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = false := ha
      simp only [ansTy, ha'] at hVg
      show erwpK (ℍ := ℍ) _ _ _ _ x k ls' (.app (tailClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vc)) (.pair (.val v) κ.1)) σ
      rw [ha']
      obtain ⟨σa, σk, hck, ⟨hA', hcA, hxOK⟩, hu, f, hf, hκ⟩ := hσ
      cases k with
      | zero => exact erwpK_zero
      | succ k₀ =>
      refine erwpK_step (fun _ => opTableK_local _ _) (e' := Expr.subst 0 (Val.pair v κ) _)
        (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl .hole) ?_
      -- the rest runs from the floor the handled stop chose
      refine erwpK_flr_tabN (F := CTy.effOf S R) (δ := δ) f
        (Q := fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) (fun _ _ _ _ _ h => h) k₀ x ls' _ σ ?_
      have hx'OK : (x.flr f).Θ.OK := hxOK
      have hΦ' : ((x.flr f).Θ.view (x.flr f).c).Down := LocTy.view_down hxOK.1 x.c
      have hTd' : (opTableK (x.flr f).lo (Tout (x.flr f))).Down :=
        opTableK_downI (tabN_downI_OK _ δ _)
      refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x.flr f) hΦ' hTd' hQout
        (tailClause_steps_body j vc g v κ hg) ?_
      -- the answering function's run at `Σ_N`, consistent with the view
      obtain ⟨-, hgr⟩ := hVg
      have hy := hgr x.Θ (LocTy.extR_refl _ _) hxOK x.c (consistentX_empty _) ls' x.c k₀
        (by omega) v σa σa (compS_empty_left σa) (vN_down _ δ x.Θ k₀ v σa hA') hcA
      have hy' := (cN_effOf SN E[j].2.2 δ x.Θ x.c k₀ ls' _ σa).mp hy (x.flr f).lo
      have hy'' := erwpK_consistentAns (c := fun z : KW => z.c)
        (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en (tabF_of_tabN hT) y k ls w ρ hB)
        (fun x m i en hT f y ρ hy _ => (tabN_wkC δ _ x m i en hT f y ρ hy).2.2.1)
        (fun x y (h : y = x) => by rw [h]) k₀ k₀ le_rfl (x.flr f) ls' _ σa hy' hcA
      -- the frame: `κ`'s relation, the world reached owed from the clause's at `f`
      set en₁ := ((rdN (ℍ := ℍ) δ).ent () n E[j].1 E[j].2.1 E[j].2.2
        (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (fs j)) x).withPAP x.c x.Θ.OK (postOK x) with hen₁
      set Fr : KW → List SRec → WProp := fun y ls₁ τ => y.lo ≤ f ∧ en₁.wk f y τ ∧
        ∀ y', en₁.wk f y' τ → ∀ ls₂, en₁.wc ls₁ ls₂ τ → ∀ k', k' < k₀ + 1 →
          (∀ w : Val, (en₁.PB y' k' ls₂ w ─⋆ erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
            (fun z => opTableK z.lo (Tout z)) (fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) y' k'
            ls₂ (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) τ) ∧
          (en₁.q ≠ .lin → ∀ Tk, (none : Option (KW → OpTabK KW)) = some Tk →
            erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c) (fun z => opTableK z.lo (Tk z))
              (fun _ => unitPost) y' k' ls₂ (.app κ.1 (.val (Val.inj₂ .unit))) τ) with hFr
      have hFext : ∀ y ls₁ ls₂ τ, extF ls₁ ls₂ τ → Fr y ls₁ τ → Fr y ls₂ τ := by
        rintro y ls₁ ls₂ τ he ⟨hlo, hwk, hk'⟩
        exact ⟨hlo, hwk, fun y' hy' ls₃ he' => hk' y' hy' ls₃ (extF_trans he he')⟩
      refine erwpK_frame_plain_orI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
        (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo) hVt
        (fun z hz => LocTy.view_down hz.1 z.c) (fun x y (h : y = x) => by rw [h])
        (fun x y (h : y = x) hx => h ▸ hx)
        (T := fun z => tabN (ℍ := ℍ) (CTy.effOf SN E[j].2.2) δ z) (T' := Tout)
        (fun z => by
          have h := tabF_le_of_rowLe (ℍ := ℍ) (rdN (ℍ := ℍ) δ) hSN () E[j].2.2 R z
          rw [← tabN_eq, ← tabN_eq] at h; exact h)
        (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
        (resK κ) (resK_plain κ).1 (resK_plain κ).2 Fr
        (fun _ ls₁ ls₂ hs τ hF => hFext _ ls₁ ls₂ τ (extF_of_same hs τ) hF)
        (fun x y (h : y = x) _ _ hF => h ▸ hF)
        (fun x m i en hT f y ρ hy => (tabN_wkC δ _ x m i en hT f y ρ hy).2.1)
        (fun x m i en hT ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ => tabF_wcl (tabF_of_tabN hT) hc₁ he₁)
        (fun x m i en hT f y ρ₁ σ₁ ρ₁' hc₁ hv₁ hy =>
          tabF_wkLeft (rdN_ok δ) (tabF_of_tabN hT) hc₁ hv₁ hy)
        (fun x m i en hT ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ hF => by
          obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT)
          exact hFext x ls₁ ls₂ σ₁ (extF_right hc₁ he₁) hF)
        ?_ (fun _ m i en₂ hT₂ ha₂ => absurd ha₂ (by simp [(lin_condsK hLin hT₂).2]))
        (fun _ m i en₂ hT₂ hq₂ => absurd hq₂ (by simp [(lin_condsK hLin hT₂).1]))
        (fun _ m i en₂ hT₂ _ hq₂ => absurd (lin_condsK hLin hT₂).1 hq₂)
        _ _ ?_ k₀ (x.flr f) hx'OK ls' _ σa hy'' σk σ ⟨min_le_right _ _, Or.inr ⟨⟨rfl, rfl,
          min_le_left _ _⟩, hxOK⟩, hκ⟩ hck
      · -- the frame across a stop of the function, at a floor no higher than `f`
        rintro x₁ m i en₂ hT₂ f₁ hf₁ y ls₁ ρ₁ τ ρ₁' hc₁ hv₁ hy ⟨hlo, hwk, hk'⟩
        have hy₁ : x₁.Owed f₁ y ρ₁' := tabN_wkC δ _ x₁ m i en₂ hT₂ f₁ y ρ₁' hy
        have hyτ : x₁.Owed f y τ :=
          (hy₁.left (ResU.CompS.comm hc₁) hv₁).floor_le (le_trans hf₁ hlo)
        refine ⟨le_trans hy₁.2.2.2.1 hlo, Or.inl ?_, hk'⟩
        rcases hwk with hw | ⟨hpost, -⟩
        · exact KW.Owed.trans hw hyτ
        · exact KW.Owed.of_post hpost hyτ
      · -- the function's value resumes `κ` at the world it is posted at
        rintro y - k' ls₁ w τ ⟨τ₁, τ₂, hcτ, ⟨hk'', hw, hcw, -⟩, -, hwk, hk'⟩
        refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := y)
          (LocTy.view_down (show y.Θ.OK from ?_).1 y.c) (opTableK_downI (tabN_downI_OK _ δ _))
          hQout (resK_steps κ w) ?_
        · rcases hwk with hw' | hw'
          · exact hw'.2.1
          · exact hw'.2
        exact (hk' y hwk ls₁ (extF_refl ls₁ τ₂) k' (by omega)).1 w τ₁ τ ⟨hw, hcw⟩
          (ResU.CompS.comm hcτ)
    · -- an abortive operation: the clause runs `g v`
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = true := ha
      simp only [ansTy, ha'] at hVg
      show erwpK (ℍ := ℍ) _ _ _ _ x k ls' (.app (tailClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vc)) (.val v)) σ
      rw [ha']
      obtain ⟨hA', hcA, hxOK⟩ := hσ
      refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x)
        (LocTy.view_down hxOK.1 x.c) (opTableK_downI (tabN_downI_OK _ δ _)) hQout
        (tailClauseA_steps j vc g v hg) ?_
      obtain ⟨-, hgr⟩ := hVg
      exact (cN_effOf S R δ x.Θ x.c k ls' _ σ).mp (hgr x.Θ (LocTy.extR_refl _ _) hxOK x.c
        (consistentX_empty _) ls' x.c k hk v σ σ (compS_empty_left σ) hA' hcA) x.lo

end

/-- **`[handle]` at clauses that resume `κ` in tail position, at `SemJN`** (`handleT_compatN₀`):
the handler's value is read off its run at the run's start (`erwp_val_post`); the handled
computation runs at its row's table from the part of the resource consistent with the view
(`gN_splitC`), at every floor, and the handler is `erwp_handle_tail`. -/
theorem handleT_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Hr Hc e : Expr} {S SN : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
    (hc : SemJN (ℍ := ℍ) Δ Γ₁ (.pair Hr Hc) (.val (.tensor (retTy S A R) (ansesTy S SN R E))))
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)
      (.comp (CTy.effOf S R)) := by
  intro δ γ Θ c N ls ρ hδ hΘ hcρ hlw hg
  refine (cN_effOf S R δ Θ c N ls _ ρ).mpr fun lo => erwpK_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂, -, hc₂⟩ := gN_splitC hsp hg hcρ hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hρ₁ : ρ₁ = PMap.empty := gN_deadP hd hg₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ (.pair Hr Hc)) := isVal_psub_valFormIn hlw₁ (.pair hHr hHc)
  have hH' : erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
      (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (retTy S A R) (ansesTy S SN R E)) δ Θ k v ρ) N ls
      (⟨substAll γ (.pair Hr Hc), hval⟩ : Val).1 PMap.empty :=
    erwp_of_cN_ret (hc δ γ Θ c N ls PMap.empty hδ hΘ (consistentX_empty c) hlw₁ hg₁)
  have hE' := (cN_effOf _ A δ Θ c N ls _ ρ₂).mp (he δ γ Θ c N ls ρ₂ hδ hΘ hc₂ hlw₂ hg₂) lo
  show erwpK (ℍ := ℍ) _ _ _ _ _ N ls
    (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)) ρ₂
  rw [psub_hndExpr]
  simp only [Expr.psub]
  rw [show Expr.psub 0 γ (tailTuple E 0 Hc) = tailTuple E 0 (substAll γ Hc) from
    tailTuple_psub γ Hc E 0]
  -- the handler's value, read off its run at the run's start
  rw [erwpK_eq]
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ls', ρ', -, hv'⟩ := erwp_val_post (by omega) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg hI hl hfd
  obtain ⟨vr, vc, σ₁, σ₂, hpair, -, hVr, hVc⟩ := hv'
  have hσ₁ : σ₁ = PMap.empty := vN_empty_of_persistent _ (retTy_persistent S A R) hVr
  have hσ₂ : σ₂ = PMap.empty := vN_empty_of_persistent _ (ansesTy_persistent S SN R E) hVc
  subst hσ₁ hσ₂
  have hHe : substAll γ (.pair Hr Hc) = (Val.pair vr vc).1 := congrArg Subtype.val hpair
  simp only [substAll, Expr.psub, Val.pair] at hHe
  obtain ⟨h₁, h₂⟩ := Expr.pair.inj hHe
  have hH := erwp_handle_tail (fs := fs) hΘ hnS hlen hSN hLin hVr hVc hE' hc₂
  rw [erwpK_eq] at hH
  rw [h₁, show substAll γ Hc = vc.1 from h₂] at hrun
  exact hH ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
