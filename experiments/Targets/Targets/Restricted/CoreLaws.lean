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

**The run-end relation** (FIX-RUN-END §2.2, §2.3).

* `wpGW_of_wpG_nil` [generic]: at every world meeting `SliceShape`, a `wpG` run is a `wpGW` run at
  the nil index that ends on the nil slice.  It reads the `Fam` pin both ways and the `←` halves of
  the `Stop` and `Upd` pins.
* Where `Upd` is Core's at every index [generic], the run-end laws and the printed route's forms
  of `↭`'s lemmas hold, each from Core's lemma, as Core's proof reads it: `updRefl_of_core` (6.47,
  `ResU.updV_self_iff`), `updOwn_of_core` (the own-cell step, `updV_compS_own`),
  `updSeq_of_core` (6.48 then 6.49, `updV_frame` and `ResU.UpdV.trans`, `wpG_bind`'s last step),
  `updReclaim_of_core` (`reclaim`), `updFrame_of_core` (6.48, `updV_frame`),
  `updOutlives_of_core` (6.50, `updV_outlives`), `updMutBack_of_core` (6.27, 6.28),
  `updImmBack_of_core` (`six38_steps_one_two`, 6.38, 6.39), `updLendBack_of_core`.
* At `coreW` (`coreW_upd`, by `Iff.rfl`): `updRefl_core`, `updOwn_core`, `updSeq_core`,
  `updReclaim_core`, `updFrame_core`, `updOutlives_core`, `updLendBack_core`.
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
    fun _ _ _ _ _ => Iff.rfl, fun _ => rfl⟩

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

/-! ### The run-end relation (FIX-RUN-END §2.2, §2.3) -/

/-- `coreW`'s run-end relation is Core's `↭` at every index. -/
theorem coreW_upd : ∀ (i i' : Idx Unit) (ρ ρ' π : WRes),
    (coreW (ℍ := ℍ)).Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π := fun _ _ _ _ _ => Iff.rfl

/-- **The embedding, run by run** (DESIGN §4.2's reading of "vC/cC are the σ = [] instance"): at
every world whose nil slice is Core's, a `wpG` run is a `wpGW` run at the nil index that ends on
the nil slice.  It reads the `Fam` pin in both directions (the start's configuration is Core's,
the end's is W's) and the `←` halves of the `Stop` and `Upd` pins. -/
theorem wpGW_of_wpG_nil {M : SemWorld} (hS : SliceShape M) (ls : List SRec) (e : Expr)
    (Q : Idx M.Stk → Expr → WProp) (ρ : WRes)
    (h : wpG (ℍ := ℍ) ls e (fun ls' t => Q (ls', M.nil) t) ρ) :
    wpGW (ℍ := ℍ) M (ls, M.nil) e Q ρ := by
  intro ρf fρ ps hf hc hF A k
  obtain ⟨hT, htg⟩ := (hS.2.1 fρ ps ls).mp hF
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', (ls', M.nil), a1, a2, a3, a4, a5, a6, a7, a8,
    (hS.2.2.2.2.1 ls ls' ρ ρ' π).mpr a9, a10, (hS.2.1 fρ'p ps' ls').mpr ⟨a11, a12⟩,
    (hS.2.2.2.1 ps ls ps' ls' t).mpr ⟨a13, a14⟩, a15⟩

/-- 6.47 (`ResU.updV_self_iff`), as `wpG_here` reads it, where `Upd` is Core's at every index. -/
theorem updRefl_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdRefl M :=
  fun _ _ ρ _ _ hf _ _ => (hC _ _ _ _ _).mpr ((ResU.updV_self_iff ρ).mpr (hash_valid hf).2)

/-- The own-cell step (`updV_compS_own`), as the alloc and free rules read it, where `Upd` is
Core's at every index. -/
theorem updOwn_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdOwn M :=
  ⟨fun _ _ _ _ _ _ _ _ hf _ _ ho hf₁ =>
    (hC _ _ _ _ _).mpr (updV_compS_own ho (hash_valid hf).2 (hash_valid hf₁).2),
   fun _ _ _ _ _ _ _ _ hf₁ _ _ ho =>
    (hC _ _ _ _ _).mpr (updV_compS_own ho (ResU.Valid.split ho (hash_valid hf₁).2).1
      (hash_valid hf₁).2).symm⟩

/-- 6.48 then 6.49, as `wpG_bind`'s last step composes two runs (`Core/EffWp.lean:910-911`),
where `Upd` is Core's at every index. -/
theorem updSeq_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdSeq M := by
  intro i i₁ i₂ ρ ρ'₁ ρp₁ π₁ ρ'₂ π₂ π hu₁ hc₁ hu₂ hH hc
  have h₁ := (hC _ _ _ _ _).mp hu₁
  have h₂ := (hC _ _ _ _ _).mp hu₂
  have hvπ : ResU.Valid π := by
    obtain ⟨w, hw, hvw⟩ := hH.2
    rwa [ResU.CompS.functional hw hc] at hvw
  have hc₁' : ResU.CompS ρp₁ ρ'₁ π₁ := ResU.CompS.comm hc₁
  exact (hC _ _ _ _ _).mpr (ResU.UpdV.trans h₁
    (updV_frame hc₁' hc ⟨hc₁'.1, _, hc₁', h₁.2.2⟩ ⟨hc.1, _, hc, hvπ⟩ h₂))

/-- `reclaim`, at `theorem32D`'s end, where `Upd` is Core's at every index. -/
theorem updReclaim_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdReclaim M :=
  fun _ π hu hno => reclaim π ((hC _ _ _ _ _).mp hu) hno

/-- 6.48 (`updV_frame`), as `wpG_ramify` reads it, where `Upd` is Core's at every index. -/
theorem updFrame_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdFrame M :=
  fun _ _ _ _ _ _ _ _ _ hu hc hh hπ hhπ _ =>
    (hC _ _ _ _ _).mpr (updV_frame hc hπ hh hhπ ((hC _ _ _ _ _).mp hu))

/-- 6.50 (`updV_outlives`), as `wpTS_box` reads it, where `Upd` is Core's at every index. -/
theorem updOutlives_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdOutlives M :=
  fun _ _ _ _ _ _ ho hu => updV_outlives ho ((hC _ _ _ _ _).mp hu)

/-- 6.27 then 6.28 (`ResU.six27`, `ResU.six28`), as `wpG_M_frameX` reads them, where `Upd` is
Core's at every index. -/
theorem updMutBack_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdMutBack M := by
  intro i i' l α v ρv ρb BM ρ' π h P hw hout hBM hu
  have hu' := (hC _ _ _ _ _).mp hu
  obtain ⟨v', χ, h', hw', hsplit⟩ := ResU.six27 hout hBM hu'
  refine ⟨v', χ, h', hw', hsplit, fun W W' O O' ρ'' hW hW' hO hO' _ hvO hvO' => ?_⟩
  exact (hC _ _ _ _ _).mpr
    ⟨(ResU.six28 hW hW' hBM hsplit hO hO' hu'.2.1 hu'.2.2 hvO hvO').mp hu'.1, hvO, hvO'⟩

/-- 6.29, 6.38 and 6.39 (`ResU.six38_steps_one_two`, `ResU.six38`, `ResU.six39`), as
`wpG_I_frameX` reads them, where `Upd` is Core's at every index. -/
theorem updImmBack_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdImmBack M := by
  intro i i' l α v ρv ρb W BI ρ' ρp π h hW hH hout hout' hpp hno hBI hc hu
  have hu' := (hC _ _ _ _ _).mp hu
  obtain ⟨hGsplit, -, hGc⟩ := ResU.six38_steps_one_two hW hH hpp hout hout' hBI hc hu'
  obtain ⟨G₀, hG₀, hH28⟩ := ResU.six38 hW hH hpp hout hout' hno hBI hc hu'
  obtain rfl : π.del l = G₀ := ResU.CompS.functional hGsplit hG₀
  refine ⟨hGc, hH28, fun O O' ρ'' hO hO' _ => ?_⟩
  obtain ⟨w, w', hw, hw', hupd⟩ := ResU.six39 (ResU.CompS.comm hW) hH hH28 hBI hGc hu'
  rw [ResU.CompS.functional hO hw, ResU.CompS.functional hO' hw']
  exact (hC _ _ _ _ _).mpr hupd

/-- The lend comes back, for both frame rules, where `Upd` is Core's at every index. -/
theorem updLendBack_of_core {M : SemWorld}
    (hC : ∀ i i' ρ ρ' π, M.Upd i i' ρ ρ' π ↔ ResU.UpdV ρ π) : UpdLendBack M :=
  ⟨updMutBack_of_core hC, updImmBack_of_core hC⟩

theorem updRefl_core : UpdRefl (coreW (ℍ := ℍ)) := updRefl_of_core coreW_upd
theorem updOwn_core : UpdOwn (coreW (ℍ := ℍ)) := updOwn_of_core coreW_upd
theorem updSeq_core : UpdSeq (coreW (ℍ := ℍ)) := updSeq_of_core coreW_upd
theorem updReclaim_core : UpdReclaim (coreW (ℍ := ℍ)) := updReclaim_of_core coreW_upd
theorem updFrame_core : UpdFrame (coreW (ℍ := ℍ)) := updFrame_of_core coreW_upd
theorem updOutlives_core : UpdOutlives (coreW (ℍ := ℍ)) := updOutlives_of_core coreW_upd
theorem updLendBack_core : UpdLendBack (coreW (ℍ := ℍ)) := updLendBack_of_core coreW_upd

end Targets

end
