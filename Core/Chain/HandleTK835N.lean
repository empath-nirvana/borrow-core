import Core.Chain.HandleT835N
import Core.Chain.HandleK835N
import Core.Chain.MechK835N3

/-!
# The tail handler's producers at `erwpK`  `[spec §14, §19]`

`HandleT835N.lean`'s three stop producers restated over a world index:

* `erwpK_frame_plain_or` (`erwp_frame_plain_or`): a plain frame around a computation at a table
  `T` below the outer `T′` (`OpTabK.Le`); the stop is at `T′`'s entry, whose order allows no more
  worlds than `T`'s; the frame's conditions are read at `T`'s entries, the order at a part of the
  joint share, the joint share valid;
* `erwpK_consistentPA` (`erwp_consistentPA`): the payloads of the handler's name read at the view
  of the stop's world; a resumption starts from the share beside an answer consistent with the
  resumption world's view, the share consistent there along the entry's order (`hwkc`);
* `KapRelK.extF` (`KapRelN.extF`).

Each `erwp` statement is proved again at one world (`*_of_K`); its text is the original's.
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

/-! ### The plain frame below a wider table -/

/-- **A plain frame around a computation at a table below the outer one, at `erwpK`**
(`erwp_frame_plain_or`). At a stop the frame joins the continuation's share, at `T′`'s entry; the
worlds that entry owes the continuation at are ones `T`'s entry owes it at (`OpTabK.Le`), read at
the run's own share (`hkl`); the frame is read again at the resumption world (`hFk`). -/
theorem erwpK_frame_plain_or {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {T T' : ι → OpTabK ι} (hTT : ∀ x, (T x).Le (T' x))
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T' y)).Le (opTableK (fl x) (T' x)))
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false)
    (Fr : ι → List SRec → WProp)
    (hFs : ∀ x ls ls', (∀ a, a ∈ ls' ↔ a ∈ ls) → ∀ ρ, Fr x ls ρ → Fr x ls' ρ)
    (hFV : ∀ x y, V x y → ∀ ls ρ, Fr x ls ρ → Fr y ls ρ)
    (hwl : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → en.wc ls ls' ρ)
    (hkl : ∀ x n i en, T x n i = some en → ∀ f y ρ σ ρ', ResU.CompS ρ σ ρ' → ResU.Valid ρ' →
      en.wk f y ρ' → en.wk f y ρ)
    (hFe : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → Fr x ls σ → Fr x ls' σ)
    (hFk : ∀ x n i en, T x n i = some en → ∀ f y ls ρ σ ρ', ResU.CompS ρ σ ρ' →
      ResU.Valid ρ' → en.wk f y ρ' → Fr x ls σ → Fr y ls σ)
    (hW : ∀ x n i en, T x n i = some en → en.abort = true → ∀ ls ρ, Fr x ls ρ → NoOwn ρ)
    (hU : ∀ x n i en, T x n i = some en → en.q = .unr → ∀ ls ρ, Fr x ls ρ → ρ = PMap.empty)
    (hK : ∀ x n i en, T x n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ y k ls K₁ ρ σ ρ', cancelOKK en y k ls K₁ ρ → Fr y ls σ → ResU.CompS ρ σ ρ' →
        cancelOKK en y k ls (K.comp K₁) ρ')
    (Q₁ Q : ι → PostN)
    (hkv : ∀ y k ls (v : Val) ρ, (Q₁ y k ls v ⋆ Fr y ls) ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T' z)) Q y k ls (K.plug v.1) ρ) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q₁ x n ls e ρ →
      ∀ ρ₂ ρ', Fr x ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T' z)) Q x n ls (K.plug e) ρ' := by
  have hL' : ∀ z, (opTableK (fl z) (T' z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h ρ₂ ρ' hF hc
  rw [erwpK_eq] at h ⊢
  refine rwpG_bind (hΦ x) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hcσ, hp, hF'⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (Fr x) (hFs x) hc h hF))
  rcases hp with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact erwpK_shift hVt hΦV hTV hL' hy hk
      (hkv y k ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFV x y hy ls' σ₂ hF'⟩)
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
      have hFy := hFk x m i en hT f y ls'' ρk σ₂ ρk' hk' hvk hy₀
        (hFe x m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF')
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont y hyk ls'' (hwl x m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).1 k' hk'' w τ₁ z
        (hPB ▸ hB) hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y ls'' _ z h₁ σ₂ τ₂ hFy hcz
    · rw [← hwc] at he
      have hq'' : en.q ≠ .lin := hq ▸ hq'
      have hy₀ := hwk f y ρk' hy
      have hyk := hkl x m i en hT f y ρk σ₂ ρk' hk' hvk hy₀
      have hFy := hFk x m i en hT f y ls'' ρk σ₂ ρk' hk' hvk hy₀
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

/-- `erwp_frame_plain_or` from `erwpK_frame_plain_or`. -/
theorem erwp_frame_plain_or_of_K {Φ : LocFam} (hΦ : Φ.Down) (T T' : OpTabN) (hTT : T.Le T')
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false)
    (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, Fr ls ρ → Fr ls' ρ)
    (hwl : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      en.wc ls ls' ρ)
    (hFe : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      Fr ls σ → Fr ls' σ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ k ls K₁ ρ σ ρ', cancelOKN en k ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOKN en k ls (K.comp K₁) ρ')
    (Q₁ Q : PostN)
    (hkv : ∀ k ls (v : Val) ρ, (Q₁ k ls v ⋆ Fr ls) ρ →
      erwp (ℍ := ℍ) Φ (opTableN T') Q k ls (K.plug v.1) ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q₁ n ls e ρ →
      ∀ ρ₂ ρ', Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwp (ℍ := ℍ) Φ (opTableN T') Q n ls (K.plug e) ρ' := by
  intro n ls e ρ h ρ₂ ρ' hF hc
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_frame_plain_or (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (T' := fun _ => liftTabK T') (fun _ => hTT.liftK)
    (fun _ _ _ _ _ _ _ _ h => h) K hH hC (fun _ => Fr) (fun _ => hFs) (fun _ _ _ _ _ h => h)
    ?_ ?_ ?_ (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ (fun _ => Q₁) (fun _ => Q) ?_
    n () ls e ρ h ρ₂ ρ' hF hc
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hwl m i en₀ h₀
  · intro _ m i en h₁ _ _ _ _ _ _ _ _
    obtain ⟨en₀, -, rfl⟩ := liftTabK_some h₁
    trivial
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hFe m i en₀ h₀
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hW m i en₀ h₀
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hU m i en₀ h₀
  · intro _ m i en h₁ ha hq _ k ls₁ K₁ ρ₁ σ ρ₁' hcan hF₁ hc₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact (cancelOKK_liftEntK en₀ k ls₁ _ ρ₁').mpr (hK m i en₀ h₀ ha hq k ls₁ K₁ ρ₁ σ ρ₁'
      ((cancelOKK_liftEntK en₀ k ls₁ K₁ ρ₁).mp hcan) hF₁ hc₁)
  · intro _ k ls₁ v ρ₁ h₁
    have := hkv k ls₁ v ρ₁ h₁
    rw [erwp_opTableN_eq_erwpK 0] at this
    exact this

/-! ### The payloads at the handler's name, read at the view -/

/-- `OpEntN.withPA` over a world index. -/
def OpEntK.withPA (c : Loc → Option Life) (en : OpEntK ι) : OpEntK ι :=
  { en with PA := fun k ls v ρ => en.PA k ls v ρ ∧ ConsistentX c ρ }

/-- `OpTabN.withPA` over a world index. -/
def OpTabK.withPA (c : Loc → Option Life) (n₀ : UInt32) (T : OpTabK ι) : OpTabK ι :=
  fun m i => if m = n₀ then (T m i).map (OpEntK.withPA c) else T m i

theorem OpTabK.withPA_some {c : Loc → Option Life} {n₀ : UInt32} {T : OpTabK ι} {m i : UInt32}
    {en : OpEntK ι} (h : T m i = some en) :
    ∃ en', T.withPA c n₀ m i = some en' ∧ en'.q = en.q ∧ en'.abort = en.abort ∧
      en'.PB = en.PB ∧ en'.fin = en.fin ∧ en'.wc = en.wc ∧ en'.wk = en.wk ∧
      ∀ k ls v ρ, en.PA k ls v ρ → ConsistentX c ρ → en'.PA k ls v ρ := by
  by_cases hm : m = n₀
  · subst hm
    exact ⟨en.withPA c, by simp [OpTabK.withPA, h], rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ _ h₁ h₂ => ⟨h₁, h₂⟩⟩
  · exact ⟨en, by simp [OpTabK.withPA, hm, h], rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ _ _ h _ => h⟩

theorem liftTabK_withPA (c : Loc → Option Life) (n₀ : UInt32) (T : OpTabN) :
    liftTabK (T.withPA c n₀) = (liftTabK T).withPA c n₀ := by
  funext m i
  by_cases hm : m = n₀
  · subst hm
    cases h : T m i with
    | none => simp [liftTabK, OpTabN.withPA, OpTabK.withPA, h]
    | some en =>
        simp only [liftTabK, OpTabN.withPA, OpTabK.withPA, h, if_true, Option.map_some]
        rfl
  · simp [liftTabK, OpTabN.withPA, OpTabK.withPA, hm]

/-- **A run from a resource consistent with its world's view, at a table whose answers are
consistent with the resumption world's view, is a run at the table whose payloads of the name `n₀`
are read at the stop's world's view, at `erwpK`** (`erwp_consistentPA`). -/
theorem erwpK_consistentPA {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life}
    {T : ι → OpTabK ι} {c : ι → Loc → Option Life}
    (hT : ∀ x m i en, T x m i = some en → ∀ y k ls w ρ, en.PB y k ls w ρ → ConsistentX (c y) ρ)
    (hwkc : ∀ x m i en, T x m i = some en → ∀ f y ρ, en.wk f y ρ → ConsistentX (c x) ρ →
      ConsistentX (c y) ρ)
    (hVc : ∀ x y, V x y → c y = c x) (n₀ : UInt32) {Q : ι → PostN} :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls e ρ →
      ConsistentX (c x) ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) ((T z).withPA (c z) n₀))
        (fun y k ls v ρ => Q y k ls v ρ ∧ ConsistentX (c y) ρ) x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h hc
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hcσ, hvσ⟩ => ?_) (rwpG_consistentXV h hc)
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, hv, y, hy, hq, (hVc x y hy).symm ▸ hcσ⟩
  · obtain ⟨⟨h₁, h₂, hTe, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', hq, hab, hPB, hfin, hwc, hwk, hPA⟩ :=
      OpTabK.withPA_some (c := c x) (n₀ := n₀) hTe
    have hck := consistentX_right hcak hcσ hvσ
    refine Or.inr (Or.inl ⟨K, m, i, v, en', pure_sep_mk ⟨h₁, h₂, hTe', hab ▸ ha⟩ ⟨ρa, ρk, hcak,
      hPA _ _ _ _ hA (consistentX_left hcak hcσ hvσ), fun hq' => hu (hq ▸ hq'), f, hf,
        fun y hy ls'' he => ?_⟩⟩)
    rw [hwc] at he
    rw [hwk] at hy
    refine ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' P hP => ?_⟩
    · rw [hPB] at hB
      have h₁ := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      exact ih k' (by omega) y ls'' _ τ₂ h₁
        (consistentX_compS hcτ (hwkc x m i en hTe f y ρk hy hck) (hT x m i en hTe _ _ _ _ _ hB))
    · rw [hq] at hq'
      exact (hcont y hy ls'' he).2 hq' P (hfin ▸ hP)
  · obtain ⟨⟨h₁, h₂, hTe, ha⟩, ρa, ρn, hcan, ⟨hPA₀, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab, -, -, -, -, hPA⟩ := OpTabK.withPA_some (c := c x) (n₀ := n₀) hTe
    exact Or.inr (Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨h₁, h₂, hTe', hab ▸ ha⟩ ⟨ρa, ρn, hcan,
      ⟨hPA _ _ _ _ hPA₀ (consistentX_left hcan hcσ hvσ), hnA⟩, hnn⟩⟩)

/-- `erwp_consistentPA` from `erwpK_consistentPA`. -/
theorem erwp_consistentPA_of_K {Φ : LocFam} {T : OpTabN} {c : Loc → Option Life}
    (hT : T.AnsC c) (n₀ : UInt32) {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ → ConsistentX c ρ →
      erwp (ℍ := ℍ) Φ (opTableN (T.withPA c n₀)) (fun k ls v ρ => Q k ls v ρ ∧ ConsistentX c ρ)
        n ls e ρ := by
  intro n ls e ρ h hc
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  rw [liftTabK_withPA]
  refine erwpK_consistentPA (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (c := fun _ => c) (Q := fun _ => Q) ?_
    (fun _ _ _ _ _ _ _ _ _ h => h) (fun _ _ _ => rfl) n₀ n () ls e ρ h hc
  intro _ m i en h₁ _ k ls' w ρ' hB
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
  exact hT m i en₀ h₀ k ls' w ρ' hB

/-! ### `κ` along `extF` -/

/-- `KapRelN.extF` at `erwpK`: the Kripke stop at an entry resumed along `extF` is carried along
`extF`. -/
theorem KapRelK.extF {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {Tb : ι → TableK ι}
    {Q : ι → PostN} {en : OpEntK ι} {lo : Life} {Tc : Option (ι → OpTabK ι)} {k : Nat}
    {κ : Val} (hwc : en.wc = extF) {ls ls' : List SRec} {ρ : WRes} (he : extF ls ls' ρ)
    (h : KapRelK (ℍ := ℍ) V Φ fl Tb Q en lo Tc k ls κ ρ) :
    KapRelK (ℍ := ℍ) V Φ fl Tb Q en lo Tc k ls' κ ρ := by
  obtain ⟨hu, f, hf, h'⟩ := h
  exact ⟨hu, f, hf, fun y hy ls'' he' => h' y hy ls'' (by
    rw [hwc] at he' ⊢; exact extF_trans he he')⟩

/-- `KapRelN` at any table is `KapRelK` at one world, at any floor. -/
theorem kapRelK_liftTb_iff (lo : Life) (Φ : LocFam) (Tb : TableN) (Q : PostN) (en : OpEntN)
    (Tc : Option OpTabN) (k : Nat) (ls : List SRec) (κ : Val) (ρ : WRes) :
    KapRelK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => lo) (fun _ => liftTb Tb)
        (fun _ => Q) (liftEntK en) lo (Tc.map (fun T _ => liftTabK T)) k ls κ ρ ↔
      KapRelN (ℍ := ℍ) Φ Tb Q en Tc k ls κ ρ := by
  constructor
  · rintro ⟨hu, f, -, h⟩
    refine ⟨hu, fun ls' he k' hk' => ⟨fun w σ₁ σ₂ hB hc => ?_, fun hq Tk hTk => ?_⟩⟩
    · have := (h () trivial ls' he k' hk').1 w σ₁ σ₂ hB hc
      rw [erwp_eq_erwpK]; exact this
    · have := (h () trivial ls' he k' hk').2 hq (fun _ => liftTabK Tk) (by rw [hTk]; rfl)
      rw [erwp_opTableN_eq_erwpK lo]; exact this
  · rintro ⟨hu, h⟩
    refine ⟨hu, lo, le_rfl, fun _ _ ls' he k' hk' => ⟨fun w σ₁ σ₂ hB hc => ?_,
      fun hq Tk hTk => ?_⟩⟩
    · have := (h ls' he k' hk').1 w σ₁ σ₂ hB hc
      rw [erwp_eq_erwpK] at this; exact this
    · cases Tc with
      | none => cases hTk
      | some T₀ =>
          cases Option.some.inj hTk
          have := (h ls' he k' hk').2 hq T₀ rfl
          rw [erwp_opTableN_eq_erwpK lo] at this; exact this

/-- `KapRelN.extF` from `KapRelK.extF`. -/
theorem KapRelN.extF_of_K {Φ : LocFam} {Tb : TableN} {Q : PostN} {en : OpEntN}
    {Tc : Option OpTabN} {k : Nat} {κ : Val} (hwc : en.wc = extF) {ls ls' : List SRec} {ρ : WRes}
    (he : extF ls ls' ρ) (h : KapRelN (ℍ := ℍ) Φ Tb Q en Tc k ls κ ρ) :
    KapRelN (ℍ := ℍ) Φ Tb Q en Tc k ls' κ ρ :=
  (kapRelK_liftTb_iff 0 Φ Tb Q en Tc k ls' κ ρ).mp
    (KapRelK.extF (en := liftEntK en) hwc he ((kapRelK_liftTb_iff 0 Φ Tb Q en Tc k ls κ ρ).mpr h))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
