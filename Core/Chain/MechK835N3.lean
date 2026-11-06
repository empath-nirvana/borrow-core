import Core.Chain.MechK835N
import Core.Chain.Frame835N
import Core.Chain.Let835N
import Core.Chain.Stop835N

/-!
# The mechanical stop producers at `erwpK`: a cancel run under a plain context, and what a run's
values keep  `[spec §19, §27, §62]`

`docs/new-core/scope-835-kripke-stop.md` §2, class M, continued from `MechK835N.lean`. Each `erwp`
statement is proved again at one world (`*_of_K`); its text is the original's.

The view a run's resources stay consistent with is read at a world (`c y`): at a stop the share is
consistent with the view of every world the entry owes the continuation at (`hwkc`), and along the
post order the view is the same (`hVc`). At one world both hold of the one view.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

variable {ι : Type}

/-- **A cancel run under a plain context, beside a frame, at `erwpK`** (`cancelOblN_frame`): the
cancel's end leaves the context and the frame behind; a stop keeps both in its continuation's
share, so the entry's list order and world order pass to a part of the share (`hwl`, `hwk`), and
its own cancel carries through `K` at the resumption world (`hK`). -/
theorem cancelOblNK_frame {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {T : ι → OpTabK ι} (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (hC : K.Catches 0 = false) {σ : WRes} (hσ : NoOwn σ)
    (hU : ∀ x n i en, T x n i = some en → en.abort = false → en.q = .unr → σ = PMap.empty)
    (hwl : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → en.wc ls ls' ρ)
    (hwk : ∀ x n i en, T x n i = some en → ∀ f y ρ ρ', ResU.CompS ρ σ ρ' →
      en.wk f y ρ' → en.wk f y ρ)
    (hK : ∀ x n i en, T x n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ y k ls K₁ ρ ρ', cancelOKK en y k ls K₁ ρ → ResU.CompS ρ σ ρ' →
        cancelOKK en y k ls (K.comp K₁) ρ') :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z)) (fun _ _ _ _ _ => False)
        x n ls e ρ → ∀ ρ', ResU.CompS ρ σ ρ' →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z)) (fun _ _ _ _ _ => False) x n ls
        (K.plug e) ρ' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h ρ' hc
  rw [erwpK_eq] at h ⊢
  refine rwpG_bind (hΦ x) K ?_
  refine rwpG_mono_le (fun k hk ls' t τ ⟨τ₁, τ₂, hcτ, hp, hτ₂⟩ => ?_)
    (rwpG_frame (fun _ τ => τ = σ) (fun _ _ _ _ h => h) hc h rfl)
  subst hτ₂
  rcases hp with ⟨_, _, _, _, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hs'⟩
  · exact hv.elim
  · -- an operation: the context and the frame join its continuation
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcτ
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT₁, ha⟩ ⟨ρa, ρk', hcσ', hA,
        fun hq => ?_, f, hf, fun y hy ls'' he =>
          ⟨fun k' hk'' w τa' τb' hB hcτ' => ?_, fun hq P hP => ?_⟩⟩⟩))
    · rw [hu hq, hU x m i en hT₁ ha hq] at hk'
      exact eq_of_compS_empty_left hk'
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ'
      have h₁ := (hcont y (hwk x m i en hT₁ f y ρk ρk' hk' hy) ls''
        (hwl x m i en hT₁ ls' ls'' ρk ρk' hk' he)).1 k' hk'' w τa' z hB hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y ls'' _ z h₁ τb' hcz
    · exact hK x m i en hT₁ ha hq y k ls'' K₁ ρk ρk'
        (fun P hP => (hcont y (hwk x m i en hT₁ f y ρk ρk' hk' hy) ls''
          (hwl x m i en hT₁ ls' ls'' ρk ρk' hk' he)).2 hq P hP) hk' P hP
  · -- the cancel's end: the context and the frame are left behind
    obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    have hKo : (K.comp K').Catches 0 = false := by rw [catches_comp, hC, hK']; rfl
    have ht' : K.plug (K'.plug (raiseE (.val (cancelVal err)))) =
        (K.comp K').plug (opE true (cancelVal err)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    obtain ⟨z, hz, hcz⟩ := compS_reassoc hcab hcτ
    exact rwpG_here (final_opPlug (payloadName_cancelVal err) hKo) (Or.inr (Or.inr
      ⟨K.comp K', err, pure_sep_mk ⟨rfl, hKo⟩ ⟨τa, z, hcz, he, noOwn_compS hz hnb hσ⟩⟩))

/-- `cancelOblN_frame` from `cancelOblNK_frame`. -/
theorem cancelOblN_frame_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (hC : K.Catches 0 = false) {σ : WRes} (hσ : NoOwn σ)
    (hU : ∀ n i en, T n i = some en → en.abort = false → en.q = .unr → σ = PMap.empty)
    (hwl : ∀ n i en, T n i = some en → ∀ ls ls' ρ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      en.wc ls ls' ρ)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ k ls K₁ ρ ρ', cancelOKN en k ls K₁ ρ → ResU.CompS ρ σ ρ' →
        cancelOKN en k ls (K.comp K₁) ρ') :
    ∀ n ls e ρ, cancelOblN (ℍ := ℍ) Φ T n ls e ρ → ∀ ρ', ResU.CompS ρ σ ρ' →
      cancelOblN (ℍ := ℍ) Φ T n ls (K.plug e) ρ' := by
  intro n ls e ρ h ρ' hc
  have h' : erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls e ρ := h
  show erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls (K.plug e) ρ'
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 T) Φ _] at h' ⊢
  refine cancelOblNK_frame (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fun _ => hΦ)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) K hH hC hσ ?_ ?_ ?_ ?_ n () ls e ρ h' ρ' hc
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hU m i en₀ h₀
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hwl m i en₀ h₀
  · intro _ m i en h₁ _ _ _ _ _ _
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    trivial
  · intro _ m i en h₁ ha hq _ k ls₁ K₁ ρ₁ ρ₁' hcan hc₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact (cancelOKK_liftEntK en₀ k ls₁ _ ρ₁').mpr (hK m i en₀ h₀ ha hq k ls₁ K₁ ρ₁ ρ₁'
      ((cancelOKK_liftEntK en₀ k ls₁ K₁ ρ₁).mp hcan) hc₁)

/-- **A run from a resource consistent with its world's view, at a table whose answers are
consistent with the resumption world's view, returns consistent resources, at `erwpK`**
(`erwp_consistentAns`): at an index up to `N`, valid, and consistent with the view of the world
each value is posted at. -/
theorem erwpK_consistentAns {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life}
    {T : ι → OpTabK ι} {c : ι → Loc → Option Life}
    (hT : ∀ x m i en, T x m i = some en → ∀ y k ls w ρ, en.PB y k ls w ρ → ConsistentX (c y) ρ)
    (hwkc : ∀ x m i en, T x m i = some en → ∀ f y ρ, en.wk f y ρ → ConsistentX (c x) ρ →
      ConsistentX (c y) ρ)
    (hVc : ∀ x y, V x y → c y = c x) {Q : ι → PostN} (N : Nat) :
    ∀ n, n ≤ N → ∀ x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls e ρ →
      ConsistentX (c x) ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z))
        (fun y k ls v ρ => k ≤ N ∧ Q y k ls v ρ ∧ ConsistentX (c y) ρ ∧ ResU.Valid ρ) x n ls e
        ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x ls e ρ h hc
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hcσ, hvσ⟩ => ?_) (rwpG_consistentXV h hc)
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ⟨K, m, i, v, en, hp⟩ | hr
  · exact Or.inl ⟨v, hv, y, hy, by omega, hq, (hVc x y hy).symm ▸ hcσ, hvσ⟩
  · obtain ⟨hpure, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hck := consistentX_right hcak hcσ hvσ
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hcak, hA, hu, f, hf,
      fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, (hcont y hy ls'' he).2⟩⟩⟩)
    have h₁ := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
    exact ih k' (by omega) (by omega) y ls'' _ τ₂ h₁
      (consistentX_compS hcτ (hwkc x m i en hpure.2.2.1 f y ρk hy hck)
        (hT x m i en hpure.2.2.1 _ _ _ _ _ hB))
  · exact Or.inr (Or.inr hr)

/-- `erwp_consistentAns` from `erwpK_consistentAns`. -/
theorem erwp_consistentAns_of_K {Φ : LocFam} {T : OpTabN} {c : Loc → Option Life}
    (hT : T.AnsC c)
    {Q : PostN} (N : Nat) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ → ConsistentX c ρ →
      erwp (ℍ := ℍ) Φ (opTableN T)
        (fun k ls v ρ => k ≤ N ∧ Q k ls v ρ ∧ ConsistentX c ρ ∧ ResU.Valid ρ) n ls e ρ := by
  intro n hn ls e ρ h hc
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_consistentAns (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (c := fun _ => c) (Q := fun _ => Q) ?_
    (fun _ _ _ _ _ _ _ _ _ h => h) (fun _ _ _ => rfl) N n hn () ls e ρ h hc
  intro _ m i en h₁ _ k ls' w ρ' hB
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
  exact hT m i en₀ h₀ k ls' w ρ' hB

/-- **A run's values are reached at indices up to its own, at `erwpK`** (`erwp_idxLe`), across
its resumptions at every world. -/
theorem erwpK_idxLe {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {T : ι → OpTabK ι}
    {Q : ι → PostN} (N : Nat) :
    ∀ n, n ≤ N → ∀ x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) (fun y k ls v ρ => k ≤ N ∧ Q y k ls v ρ)
        x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x ls e ρ h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ⟨K, m, i, v, en, hp⟩ | hr
  · exact Or.inl ⟨v, hv, y, hy, by omega, hq⟩
  · obtain ⟨hpure, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk hpure ⟨ρa, ρk, hcak, hA, hu, f, hf,
      fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, (hcont y hy ls'' he).2⟩⟩⟩)
    have h₁ := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
    exact ih k' (by omega) (by omega) y ls'' _ τ₂ h₁
  · exact Or.inr (Or.inr hr)

/-- `erwp_idxLe` from `erwpK_idxLe`. -/
theorem erwp_idxLe_of_K {Φ : LocFam} {T : OpTabN} {Q : PostN} (N : Nat) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (fun k ls v ρ => k ≤ N ∧ Q k ls v ρ) n ls e ρ := by
  intro n hn ls e ρ h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  exact erwpK_idxLe (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (Q := fun _ => Q) N n hn () ls e ρ h

/-! ### The stratified table -/

/-- `performStopNS` at the Kripke stop: the continuation's share in `Res_α`. -/
def performStopKS (lo α : Life) (T : OpTabK ι) : TableK ι := fun k ls t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntK ι) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆
        (en.PA k ls v ⋆ fun ρ => contShareK en lo k ls K Ψ ρ ∧ ρ.InStratum α)

/-- `opTableNS` at the floor bound `lo`. -/
def opTableKS (lo α : Life) (T : OpTabK ι) : TableK ι := fun k ls t Ψ =>
  BoLo.or (performStopKS lo α T k ls t Ψ) (raiseStopK T k ls t Ψ)

theorem opTableKS_lift (lo α : Life) (T : OpTabN) (k : Nat) (ls : List SRec) (t : Expr)
    (Ψ : ContK Unit) (ρ : WRes) :
    opTableKS lo α (liftTabK T) k ls t Ψ ρ ↔ liftTb (opTableNS α T) k ls t Ψ ρ := by
  refine or_congr ?_ (raiseStopK_lift T k ls t Ψ ρ)
  constructor
  · rintro ⟨K, n, i, v, en, h⟩
    obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hcs, hs⟩ := pure_sep_iff.mp h
    obtain ⟨en₀, he₀, rfl⟩ := liftTabK_some h₃
    exact ⟨K, n, i, v, en₀, pure_sep_mk ⟨h₁, h₂, he₀, h₄⟩
      ⟨ρa, ρk, hc, hA, (contShareK_liftEntK en₀ lo k ls K Ψ ρk).mp hcs, hs⟩⟩
  · rintro ⟨K, n, i, v, en, h⟩
    obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hcs, hs⟩ := pure_sep_iff.mp h
    exact ⟨K, n, i, v, liftEntK en, pure_sep_mk ⟨h₁, h₂, liftTabK_of_some h₃, h₄⟩
      ⟨ρa, ρk, hc, hA, (contShareK_liftEntK en lo k ls K Ψ ρk).mpr hcs, hs⟩⟩

/-- **The stop lemma at `erwpK`** (`erwp_stratify`): a computation started in `Res_α`, at a table
whose answers lie in `Res_α` at every world, is at the stratified table: at every stop of every
run, the continuation's share is in `Res_α`. -/
theorem erwpK_stratify {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {α : Life}
    {T : ι → OpTabK ι}
    (hT : ∀ x n i en, T x n i = some en → en.abort = false → ∀ y k ls w τ, en.PB y k ls w τ →
      τ.InStratum α) {Q : ι → PostN} :
    ∀ n x ls e ρ, ρ.InStratum α →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableKS (fl z) α (T z)) Q x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ hρ h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨ht, hσ⟩ => ?_) (rwpG_inStratum hρ h)
  rcases ht with hv | ⟨K, m, i, v, en, hp⟩ | hr
  · exact Or.inl hv
  · obtain ⟨hpure, ρa, ρk, hc, hA, hu, f, hf, hk'⟩ := pure_sep_iff.mp hp
    have hρk : ρk.InStratum α := ResU.CompS.inStratum_right hc hσ
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk hpure
      ⟨ρa, ρk, hc, hA, ⟨hu, f, hf, fun y hy ls'' he =>
        ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_, (hk' y hy ls'' he).2⟩⟩, hρk⟩⟩)
    have h₁ := (hk' y hy ls'' he).1 k' hk'' w τ₁ τ₂ hB hcτ
    simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
    exact ih k' (by omega) y _ _ _
      (inStratum_compS hcτ hρk (hT x m i en hpure.2.2.1 hpure.2.2.2 y k' ls'' w τ₁ hB)) h₁
  · exact Or.inr (Or.inr hr)

/-- `erwp_stratify` from `erwpK_stratify`. -/
theorem erwp_stratify_of_K {Φ : LocFam} {α : Life} {T : OpTabN} (hT : T.AnsIn α) {Q : PostN} :
    ∀ n ls e ρ, ρ.InStratum α → erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableNS α T) Q n ls e ρ := by
  intro n ls e ρ hρ h
  rw [erwp_opTableN_eq_erwpK 0] at h
  rw [erwp_eq_erwpK_of (opTableKS_lift 0 α T) Φ _]
  refine erwpK_stratify (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (Q := fun _ => Q) ?_ n () ls e ρ hρ h
  intro _ m i en h₁ ha _ k ls' w τ hB
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
  exact hT m i en₀ h₀ ha k ls' w τ hB

/-! ### The loop rule -/

/-- **The loop rule at `erwpK`** (`erwp_iterate`), for a tick the runtime always answers *next*.
The invariant is read at a world: a turn's value is posted at the world its run chose, where the
loop goes on; the tick's stop chooses the table's floor and the loop resumes at every world the
tick's entry owes (`hIk`). -/
theorem erwpK_iterate {V : ι → ι → Prop} (hV : ∀ y, V y y)
    (hVt : ∀ x y z, V x y → V y z → V x z) {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life} {T : ι → OpTabK ι}
    (hTD : ∀ x, (T x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    {f : Val} (hK : ∀ x, (T x).CtxClosed (iterK f)) {QL : ι → PostN} (hQL : ∀ y, (QL y).Down)
    (hf : closedAt 0 f.1 = true) {I : ι → Val → WProp}
    (htick : ∀ x, ∃ en, T x divEff 0 = some en ∧ en.abort = false ∧ en.q = .lin ∧
      (∀ k ls, en.PA k ls Val.unit PMap.empty) ∧
      (∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → w = nextV ∧ ρ = PMap.empty) ∧
      ∀ fl' y s ρ, en.wk fl' y ρ → I x s ρ → I y s ρ)
    (hIc : ∀ x s ρ, I x s ρ → closedAt 0 s.1 = true)
    (hturn : ∀ y k s ls ρ, I y s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) (fun z => turnPostN (I z) (QL z)) y k
        ls (.app (.app (.val f) (.val s)) (.val nextV)) ρ) :
    ∀ n x s ls ρ, I x s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QL x n ls (iterateE f s) ρ := by
  have hD : ∀ x, (opTableK (fl x) (T x)).Down := fun x => opTableK_down (hTD x)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x s ls ρ hI
  refine erwpK_det (hΦ x) (hD x) hQL (fun μ => step1Only_plug (Head.iterate μ f s) rfl .hole) ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq]
  refine erwpK_bind_le hVt hΦ hΦV hTV (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches]) hK n ?_ n le_rfl x ls _ ρ (hturn x n s ls ρ hI)
  rintro y k ls' v σ hk (⟨x', rfl, hx⟩ | ⟨s', rfl, hs'⟩)
  · refine erwpK_det (hΦ y) (hD y) hQL (fun μ => step1Only_plug (Head.case₁ μ x' _ _) rfl .hole) ?_
    exact erwpK_val (v := Val.inj₁ x') (hV y) hx
  · refine erwpK_det (hΦ y) (hD y) hQL (fun μ => step1Only_plug (Head.case₂ μ s' _ _) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterK_case₂]
    obtain ⟨en, htk, hab, hq, hta, htb, hIk⟩ := htick y
    refine erwpK_perform _ (by simp [Kont.HasHnd]) htk hab hq (compS_empty_left σ) (hta k ls')
      (fl y) le_rfl (fun y' hy' ls'' _ k' hk' w σB XB hB hXB => ?_)
    obtain ⟨rfl, rfl⟩ := htb y' k' ls'' w σB hB
    obtain rfl : XB = σ := ResU.CompS.functional hXB (ResU.comp_empty_right σ)
    have hs'' : I y' s' XB := hIk (fl y) y' s' XB hy' hs'
    refine erwpK_det (hΦ y') (hD y') hQL
      (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterTurn_subst hf (hIc y' s' XB hs'')]
    refine erwpK_det (hΦ y') (hD y') hQL
      (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
    simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
      subst_closedAt _ _ (hIc y' s' XB hs'') (Nat.zero_le _)]
    exact ih k' (by omega) y' s' ls'' XB hs''

/-- `erwp_iterate` from `erwpK_iterate`. -/
theorem erwp_iterate_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    {f : Val} (hK : T.CtxClosed (iterK f)) {QL : PostN} (hQL : QL.Down)
    (hf : closedAt 0 f.1 = true) {I : Val → WProp} {en : OpEntN}
    (htick : T divEff 0 = some en) (hab : en.abort = false) (hq : en.q = .lin)
    (hta : ∀ k ls, en.PA k ls Val.unit PMap.empty)
    (htb : ∀ k ls w (ρ : WRes), en.PB k ls w ρ → w = nextV ∧ ρ = PMap.empty)
    (hIc : ∀ s ρ, I s ρ → closedAt 0 s.1 = true)
    (hturn : ∀ k s ls ρ, I s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (turnPostN I QL) k ls
        (.app (.app (.val f) (.val s)) (.val nextV)) ρ) :
    ∀ n s ls ρ, I s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QL n ls (iterateE f s) ρ := by
  intro n s ls ρ hI
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_iterate (ℍ := ℍ) (V := fun _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (fun _ => hTD.liftK)
    (fun _ _ _ _ _ _ _ _ h => h) (fun _ => liftTabK_ctxClosed hK) (QL := fun _ => QL)
    (fun _ => hQL) hf (I := fun _ => I)
    (fun _ => ⟨liftEntK en, liftTabK_of_some htick, hab, hq, hta,
      fun _ k ls w ρ hB => htb k ls w ρ hB, fun _ _ _ _ _ h => h⟩)
    (fun _ => hIc) ?_ n () s ls ρ hI
  intro y k s' ls' ρ' hI'
  have h := hturn k s' ls' ρ' hI'
  rw [erwp_opTableN_eq_erwpK 0] at h
  exact h

end BoCa.Fig16.LogRel.Core.Chain.SI

end
