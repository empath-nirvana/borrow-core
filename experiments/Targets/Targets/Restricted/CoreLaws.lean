import Targets.Restricted.Transport
import Targets.Restricted.Typing
import Targets.Statements.Interface
import Targets.Statements.Conservativity
import Targets.Statements.Lifetimes
import Targets.Statements.Exclusivity
import Targets.Statements.Handlers

/-!
# Targets — the laws, the proof device and the other properties at Core σ=[] (DESIGN §9)

Each result here is a conjunct of the end state taken at `coreW`/`tier1`, from Core's own
lemmas through the transports:

* `WLaws coreW` but `AdequateEvery`: `SliceShape` (by `Iff.rfl`), `Mono` (`vC_local`), `ExtPre`
  (`Ext.refl`, `Ext.trans`), `EffInterp` (`cC_effOf`), `FamEmpty` (`TW.empty`), `DataVals`
  (`vC_data`, below), `ShareMono` (`contShare`'s monotonicity), `RelLaws` (`vCE`'s clauses,
  `cC_nu_iff`, `vC_unfold`);
* `FL coreW tier1` (`fundamentalC`);
* `LifetimeSound coreW OutJ.core` (`vC_outlives`, `vC_outlivesLe`);
* `Exclusive coreW` (`TW.valid`, `TW.inv`);
* `HandleCompat coreW` (`handle_compatC`);
* `WBCore` (`wpG`'s conjunct), `ConservativeWB coreW`, `Conservative coreW` (`vC_local`);
* `AdmExtends admClosedOp`; `rowSpan_abortive_iff_unwind`.

`vC_data` is new: a value of a closed data type is data and holds nothing.  Its forward half is
`vC_ind` (Core's induction principle for the relation, the μ case at the unrolling); its backward
half is induction on `DataVal` with `vC_roll`.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Data types -/

theorem dataB_rename : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → ∀ {k' : Nat} (r : Nat → Nat),
    (∀ n, n < k → r n < k') → VTy.DataB k' (A.rename r) := by
  intro k A h
  induction h with
  | unit k => intro _ _ _; exact .unit _
  | zero k => intro _ _ _; exact .zero _
  | int k w => intro _ _ _; exact .int _ _
  | tvar hn => intro _ r hr; exact .tvar (hr _ hn)
  | tensor _ _ ihA ihB => intro _ r hr; exact .tensor (ihA r hr) (ihB r hr)
  | sum _ _ ihA ihB => intro _ r hr; exact .sum (ihA r hr) (ihB r hr)
  | mu _ ih =>
      intro k' r hr
      refine .mu (ih (VTy.upR r) fun n hn => ?_)
      cases n with
      | zero => show 0 < k' + 1; omega
      | succ n => show r n + 1 < k' + 1; have := hr n (by omega); omega

theorem dataB_subst : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → ∀ {j : Nat} (σ : Nat → VTy),
    (∀ n, n < k → VTy.DataB j (σ n)) → VTy.DataB j (A.subst σ) := by
  intro k A h
  induction h with
  | unit k => intro _ _ _; exact .unit _
  | zero k => intro _ _ _; exact .zero _
  | int k w => intro _ _ _; exact .int _ _
  | tvar hn => intro _ σ hσ; exact hσ _ hn
  | tensor _ _ ihA ihB => intro _ σ hσ; exact .tensor (ihA σ hσ) (ihB σ hσ)
  | sum _ _ ihA ihB => intro _ σ hσ; exact .sum (ihA σ hσ) (ihB σ hσ)
  | mu _ ih =>
      intro j σ hσ
      refine .mu (ih (VTy.upS σ) fun n hn => ?_)
      cases n with
      | zero => exact .tvar (by omega)
      | succ n =>
          exact dataB_rename (hσ n (by omega)) Nat.succ (fun m hm => by omega)

/-- The unrolling of a closed data `μ` is data. -/
theorem data_inst {A : VTy} (h : (VTy.mu A).Data) : (VTy.inst (.mu A) A).Data := by
  cases h with
  | mu hA =>
      refine dataB_subst hA _ fun n hn => ?_
      cases n with
      | zero => exact .mu hA
      | succ n => omega

theorem dataB_cl : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → A.Cl k := by
  intro k A h
  induction h with
  | unit | zero | int => trivial
  | tvar hn => exact hn
  | tensor _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | sum _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | mu _ ih => exact ih

theorem dataB_noMut : ∀ {k : Nat} {A : VTy}, VTy.DataB k A → ∀ n, A.NoMut n := by
  intro k A h
  induction h with
  | unit | zero | int => intro _; trivial
  | tvar _ => intro _; trivial
  | tensor _ _ ihA ihB => intro n; exact ⟨ihA n, ihB n⟩
  | sum _ _ ihA ihB => intro n; exact ⟨ihA n, ihB n⟩
  | mu _ ih => intro n; exact ih (n + 1)

/-- A value of a closed data type is data, and holds nothing. -/
theorem vC_data_mp {δ : LSub} : ∀ (b : Bool) (A : VTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vCE (ℍ := ℍ) none b A ls δ v ρ → A.Data → ρ = PMap.empty ∧ DataVal A v := by
  refine vC_ind δ (fun _ A _ v ρ => A.Data → ρ = PMap.empty ∧ DataVal A v) ?_
  intro b T ls v ρ hF hT
  cases T with
  | unit =>
      obtain ⟨rfl, rfl⟩ := hF
      exact ⟨rfl, .unit⟩
  | int w =>
      obtain ⟨rfl, hv⟩ := hF
      exact ⟨rfl, .int hv⟩
  | tensor A B =>
      cases hT with
      | tensor hA hB =>
          obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, ⟨rfl, rfl⟩, ρ₁, ρ₂, hc', ⟨-, h₁⟩, ⟨-, h₂⟩⟩ := hF
          obtain ⟨rfl, hd₁⟩ := h₁ hA
          obtain ⟨rfl, hd₂⟩ := h₂ hB
          rw [← eq_of_compS_empty_left hc', ← eq_of_compS_empty_left hc]
          exact ⟨rfl, .pair hd₁ hd₂⟩
  | sum A B =>
      cases hT with
      | sum hA hB =>
          rcases hF with ⟨v₁, ρ₀, ρ₁, hc, ⟨rfl, rfl⟩, ⟨-, h₁⟩⟩ | ⟨v₂, ρ₀, ρ₂, hc, ⟨rfl, rfl⟩, ⟨-, h₂⟩⟩
          · obtain ⟨rfl, hd⟩ := h₁ hA
            rw [← eq_of_compS_empty_left hc]
            exact ⟨rfl, .inj₁ hd⟩
          · obtain ⟨rfl, hd⟩ := h₂ hB
            rw [← eq_of_compS_empty_left hc]
            exact ⟨rfl, .inj₂ hd⟩
  | zero => exact hF.elim
  | tvar n => exact hF.elim
  | mu A =>
      obtain ⟨-, -, -, h⟩ := hF
      obtain ⟨rfl, hd⟩ := h (data_inst hT)
      exact ⟨rfl, .roll hd⟩
  | thunk _ | ref _ | imm _ _ | «mut» _ _ | box _ _ | bang _ | unk | opq _ | fam _ =>
      cases hT

/-- Data values are in the relation at the empty resource. -/
theorem vC_of_dataVal {δ : LSub} {ls : List SRec} :
    ∀ {A : VTy} {v : Val}, DataVal A v → A.Data → ∀ b, vCE (ℍ := ℍ) none b A ls δ v PMap.empty := by
  intro A v h
  induction h with
  | unit => intro _ _; exact ⟨rfl, rfl⟩
  | int hv => intro _ _; exact ⟨rfl, hv⟩
  | pair _ _ ih₁ ih₂ =>
      intro hT b
      cases hT with
      | tensor hA hB =>
          exact ⟨_, _, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩,
            PMap.empty, PMap.empty, ResU.comp_empty_right _, ih₁ hA b, ih₂ hB b⟩
  | inj₁ _ ih =>
      intro hT b
      cases hT with
      | sum hA _ => exact Or.inl ⟨_, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ih hA b⟩
  | inj₂ _ ih =>
      intro hT b
      cases hT with
      | sum _ hB => exact Or.inr ⟨_, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ih hB b⟩
  | roll _ ih =>
      intro hT b
      cases hT with
      | mu hA => exact vC_roll (dataB_noMut hA 0) (dataB_cl (.mu hA)) (ih (data_inst (.mu hA)) b)

/-- **`vC_data`**: at a closed data type, the relation is exactly data at the empty resource. -/
theorem vC_data {A : VTy} (hA : A.Data) {b : Bool} {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes} : vCE (ℍ := ℍ) none b A ls δ v ρ ↔ ρ = PMap.empty ∧ DataVal A v :=
  ⟨fun h => vC_data_mp b A ls v ρ h hA, fun ⟨hρ, hv⟩ => hρ ▸ vC_of_dataVal hv hA b⟩

/-! ### The laws at `coreW` -/

theorem sliceShape_core : SliceShape (coreW (ℍ := ℍ)) :=
  ⟨fun _ => rfl, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
    fun _ => rfl⟩

theorem mono_core : Mono (coreW (ℍ := ℍ)) :=
  fun b A _ _ _ _ _ he h => vC_local b A he h

theorem extPre_core : ExtPre (coreW (ℍ := ℍ)) :=
  ⟨fun i ρ => Ext.refl i.1 ρ, fun _ _ _ _ h₁ h₂ => Ext.trans h₁ h₂⟩

theorem effInterp_core : EffInterp (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro S R i δ e ρ _
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core, opTabW_core_down, rowTabW_core]
  exact cC_effOf S R ls δ e ρ

theorem famEmpty_core : FamEmpty (coreW (ℍ := ℍ)) :=
  ⟨TW.empty, fun _ hx => absurd hx (by simp)⟩

theorem dataVals_core : DataVals (coreW (ℍ := ℍ)) :=
  fun _ _ _ _ _ _ hA => vC_data hA

theorem shareMono_core : ShareMono (coreW (ℍ := ℍ)) := by
  intro T en n i K Φ Φ' ρ _ hΦ h
  obtain ⟨hu, hk⟩ := h
  exact ⟨hu, fun ls' he => ⟨fun w σ₁ σ₂ hB hc => hΦ _ _ _ ((hk ls' he).1 w σ₁ σ₂ hB hc),
    (hk ls' he).2⟩⟩

theorem relElim_core : RelElim (coreW (ℍ := ℍ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C i δ v ρ h
    exact h i.1 (Ext.refl i.1 ρ)
  · intro A C i δ e ρ h
    exact h
  · intro C D i δ e ρ h
    exact h
  · intro x b C i δ e ρ h α hα
    exact h α PMap.empty ρ ⟨rfl, hα⟩ (ResU.comp_empty_right ρ)
  · intro C i δ e ρ hC h
    exact (cC_nu_iff hC i.1 δ e ρ).mp h
  · intro b A i δ v ρ h
    exact (vC_unfold h).2.2

theorem relShape_core : RelShape (coreW (ℍ := ℍ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b i δ v ρ h
    exact ⟨h.2, h.1⟩
  · intro b i δ v ρ h
    exact h
  · intro b A B i δ v ρ h
    obtain ⟨v₁, v₂, h⟩ := h
    obtain ⟨hv, h⟩ := pure_sep_iff.mp h
    exact ⟨v₁, v₂, hv, h⟩
  · intro b A B i δ v ρ h
    rcases h with ⟨w, h⟩ | ⟨w, h⟩
    · obtain ⟨hv, h⟩ := pure_sep_iff.mp h
      exact Or.inl ⟨w, hv, h⟩
    · obtain ⟨hv, h⟩ := pure_sep_iff.mp h
      exact Or.inr ⟨w, hv, h⟩
  · intro b A i δ v ρ h
    obtain ⟨ℓ, v', h⟩ := h
    obtain ⟨hv, h⟩ := pure_sep_iff.mp h
    exact ⟨ℓ, v', hv, h⟩
  · intro b A i δ v ρ h
    exact h
  · intro b a A i δ v ρ h
    exact h
  · intro b a A i δ v ρ h
    rcases i with ⟨ls, ⟨⟩⟩
    exact h
  · intro b a A i δ v ρ h
    rcases i with ⟨ls, ⟨⟩⟩
    obtain ⟨α, hα, ℓ, h⟩ := h
    obtain ⟨hv, hp⟩ := pure_sep_iff.mp h
    refine ⟨α, hα, ℓ, pure_sep_mk hv ?_⟩
    have e := ptoMutSW_core (ℍ := ℍ) ℓ α ls (fun ls₀ => vCE none true A ls₀ δ)
    exact e ▸ hp
  · intro b L i δ v ρ h
    obtain ⟨ℓ, c, h⟩ := h
    obtain ⟨⟨hv, hc⟩, hs⟩ := pure_sep_iff.mp h
    exact ⟨ℓ, c, hv, hc, hs⟩
  · intro b i δ v ρ h
    exact h.1
  · intro b w i δ v ρ h
    exact ⟨h.2, h.1⟩
  · intro b k i δ v ρ h
    exact ⟨h.2, h.1⟩
  · intro b n i δ v ρ h
    exact h

theorem relLaws_core : RelLaws (coreW (ℍ := ℍ)) := ⟨relElim_core, relShape_core⟩

/-! ### The proof device at `coreW` -/

/-- **`FL coreW tier1`**: `fundamentalC` at every admissible instance. -/
theorem fl_core_tier1 : FL (coreW (ℍ := ℍ)) tier1 :=
  fun _ _ _ _ _ h η hη => semW₀_core.mpr (fundamentalC (h η hη))

/-- `FL coreW tier1NU`: the unr-free fragment, through `CDerivesNU.toCDerives`. -/
theorem fl_core_tier1NU : FL (coreW (ℍ := ℍ)) tier1NU :=
  fun _ _ _ _ _ h η hη => semW₀_core.mpr (fundamentalC (h η hη).toCDerives)

/-! ### I2's first three conjuncts, P9, P10, P11, P14 at `coreW` -/

theorem arises_core : Arises (coreW (ℍ := ℍ)) := by
  intro fρ ps i h
  obtain ⟨hT, htg⟩ := h
  exact ⟨ps, i.1, fun p => by simp, fun x => by simp, hT, htg⟩

theorem stopVisible_core : StopVisible (coreW (ℍ := ℍ)) :=
  fun _ _ _ _ _ h => h

theorem shareResume_core : ShareResume (coreW (ℍ := ℍ)) := by
  intro T en n i K Φ ρ h _ i' he w
  rcases i' with ⟨ls', ⟨⟩⟩
  exact (h.2 ls' he).1 w

theorem exclusive_core : Exclusive (coreW (ℍ := ℍ)) := by
  intro fρ ps i h
  obtain ⟨hT, -⟩ := h
  exact ⟨TW.valid hT, ps, i.1, fun p => by simp, fun x => by simp, TW.inv hT⟩

theorem lifetimeSound_core : LifetimeSound (coreW (ℍ := ℍ)) OutJ.core :=
  ⟨fun _ _ _ _ _ b i v ρ hδ ha hT h => vC_outlives hδ ha hT b i.1 v ρ h,
   fun _ _ _ _ _ b i v ρ hδ ha hT h => vC_outlivesLe hδ ha hT b i.1 v ρ h⟩

theorem handleCompat_core : HandleCompat (coreW (ℍ := ℍ)) := by
  intro Δ Γ Γ₁ Γ₂ Γr Γc e S E n A R ir ic _ hs hs₁ hr hc hn0 hnS hlen he
  exact semW₀_core.mpr (handle_compatC hs hs₁ hr hc hn0 hnS hlen (semW₀_core.mp he))

theorem wbCore : WBCore (ℍ := ℍ) := by
  intro ls e Q ρ h ρf fρ ps hf hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, hT',
    htg', hps, hls, hQ⟩ := h ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, hT',
    htg', hps, hls, hQ, hls⟩

theorem conservative_core : Conservative (ℍ := ℍ) (coreW (ℍ := ℍ)) :=
  fun b A _ _ _ _ h _ he => vC_local b A he h

theorem conservativeWB_core : ConservativeWB (ℍ := ℍ) (coreW (ℍ := ℍ)) :=
  fun b A _ _ _ _ _ h _ he => vC_local b A he h

/-! ### OQ-56 (a): R-CLOSEDOP -/

theorem admExtends_closedOp : AdmExtends admClosedOp := fun _ _ _ h => h

/-- R-CLOSEDOP at abortive rows is `Row.Unwind`. -/
theorem rowSpan_abortive_iff_unwind {Δ : LifeCtx} {x : LifeVar} {S : Row} :
    RowSpan admClosedOp Δ x S ∧ RowClass.abortive.Admits S ↔ S.Unwind x := by
  constructor
  · rintro ⟨hs, ha⟩ o ho
    obtain ⟨hn, -, hA, -, hO, -⟩ := hs o ho
    exact ⟨ha o ho, hn, hA, hO⟩
  · intro h
    refine ⟨fun o ho => ?_, fun o ho => (h o ho).1⟩
    obtain ⟨ha, hn, hA, hO⟩ := h o ho
    have hB := OpSig.B_zero ha
    refine ⟨hn, Or.inl ha, hA, by rw [hB]; exact id, hO, fun _ _ => by rw [hB]; exact .zero⟩

end Targets

end
