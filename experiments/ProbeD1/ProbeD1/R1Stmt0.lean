import ProbeD1.R1Box

/-!
# ProbeD1 — statement 0 at `vRLM` (`R1MONO.md` §4)

* **At a data type `vRLM` is Core's** (`vRLMDataE`, `vRLMData`): by induction on `DataB`, the two
  least fixed points at `μ` compared in both directions, each closed by the induction hypothesis
  at the body; W's candidate is a predicate at one index, Core's joint over the mode and the list,
  and a data body reads its variable at the mode and list it is read at (`EnvCore`).
* **The nil slice** (`nilSoundRetM`): `nilSoundRet`'s proof at `vRLM`.
* **`[force]`** (`forceRowM`): at `binder0` (block stacks at `cbpv` and `binder` are not derived;
  `LEDGER.md` §11.3), the `U` clause at the identity (`relendJ_id` at
  `binder0`, the reflexive re-lend and future otherwise), the views handed back as they were.
* **The callbacks at `σ·y`** (`callbackExtMutM_own`, `callbackExtImmM_own`): at a placement whose
  `∀` clause makes the own lend, the `U` clause at the identity, the own-lend conjunct at the
  revised own lend, the `⊸` clause at the pushed stack. At the 6.64 callback the force is at the
  extended list, the guard's views carried along `Ext` (`placeViewsL_ext`: a nested cell lies above
  the top cell it sits in).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView rowTab
  bodyS OpenS)

/-! ### At a data type `vRLM` is Core's -/

/-- **`EnvCoreNone`.** -/
theorem envCoreNone : EnvCoreNone :=
  fun _ => ⟨fun _ => rfl, fun _ _ _ => Iff.rfl⟩

theorem tClose_eq_subst (η : Option (Nat → TEnt)) (A : VTy) :
    tClose η A = A.subst (fun n => (tEnv η n).ty) := tClose_eq η A

/-- The two environments close a type alike when their types agree. -/
theorem wClose_tClose {η : Option (Nat → WEnt)} {ηc : Option (Nat → TEnt)}
    (h : ∀ n, (wEnv η n).ty = (tEnv ηc n).ty) (A : VTy) : wClose η A = tClose ηc A := by
  rw [wClose_eq, tClose_eq]
  congr 1
  funext n
  exact h n

/-- **`VRLMDataE`**, pointwise. -/
theorem vRLM_dataE (p : Placement) : ∀ {k : Nat} {A : VTy}, VTy.DataB k A →
    ∀ (η : Option (Nat → WEnt)) (ηc : Option (Nat → TEnt)) (σ : LStack) (δ : LSub)
      (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
      EnvCore η ηc ls →
      (vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ ↔ vCE ηc true A ls (extS δ σ αs) v ρ)
  | _, _, .unit _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, .zero _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, .int _ _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, @VTy.DataB.tvar _ n _, η, ηc, _, _, _, ls, v, ρ, hE => hE.2 n v ρ
  | _, _, .tensor hA hB, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
          (vRLM_dataE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mp h₁,
          (vRLM_dataE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mp h₂⟩
      · rintro ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
          (vRLM_dataE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mpr h₁,
          (vRLM_dataE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mpr h₂⟩
  | _, _, .sum hA hB, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro (⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩)
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, (vRLM_dataE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mp h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, (vRLM_dataE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mp h₂⟩
      · rintro (⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩)
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, (vRLM_dataE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mpr h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, (vRLM_dataE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mpr h₂⟩
  | _, _, @VTy.DataB.mu _ A hA, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      have hM : wClose η (.mu A) = tClose ηc (.mu A) := wClose_tClose hE.1 (.mu A)
      constructor
      · rintro ⟨hnm, hcl, hlfp⟩
        refine ⟨hnm, hM ▸ hcl, fun P hP => ?_⟩
        refine hlfp (fun v ρ => P true ls v ρ) (fun v' ρ' h' => hP true ls v' ρ' ?_)
        refine (vRLM_dataE p hA _ (some (VTy.scons ⟨tClose ηc (.mu A), P⟩ (tEnv ηc))) σ δ αs ls
          v' ρ' ⟨fun n => ?_, fun n v'' ρ'' => ?_⟩).mp h'
        · cases n with
          | zero => exact hM
          | succ n => exact hE.1 n
        · cases n with
          | zero => exact Iff.rfl
          | succ n =>
              show (wEnv η n).P v'' ρ'' ↔ (tEnv ηc n).P true ls v'' ρ''
              rw [← wEnvP_eq, ← tEnvP_eq]; exact hE.2 n v'' ρ''
      · rintro ⟨hnm, hcl, hlfp⟩
        refine ⟨hnm, hM ▸ hcl, fun Q hQ => ?_⟩
        refine hlfp (fun b ls' v ρ => b = true → ls' = ls → Q v ρ)
          (fun b' ls' v' ρ' h' hb hls => ?_) rfl rfl
        subst hb hls
        refine hQ v' ρ' ((vRLM_dataE p hA (some (VTy.scons ⟨wClose η (.mu A), Q⟩ (wEnv η))) _ σ δ αs
          ls' v' ρ' ⟨fun n => ?_, fun n v'' ρ'' => ?_⟩).mpr h')
        · cases n with
          | zero => exact hM
          | succ n => exact hE.1 n
        · cases n with
          | zero => exact ⟨fun h _ _ => h, fun h => h rfl rfl⟩
          | succ n =>
              show (wEnv η n).P v'' ρ'' ↔ (tEnv ηc n).P true ls' v'' ρ''
              rw [← wEnvP_eq, ← tEnvP_eq]; exact hE.2 n v'' ρ''

/-- **`VRLMDataE`.** -/
theorem vRLMDataE : VRLMDataE (ℍ := ℍ) := by
  intro p k A hA η ηc σ δ αs ls v hE
  funext ρ
  exact propext (vRLM_dataE p hA η ηc σ δ αs ls v ρ hE)

/-- **`VRLMDataOfE`.** -/
theorem vRLMDataOfE : VRLMDataOfE (ℍ := ℍ) :=
  fun hE p σ δ αs A hA ls v => hE p 0 A hA none none σ δ αs ls v (envCoreNone ls)

theorem vRLMData : VRLMData (ℍ := ℍ) := vRLMDataOfE vRLMDataE

/-! ### The nil slice at a data answer -/

/-- The answer relation of `F_Σ A` at `σ = []` and a data `A` is the kernel's, at `vRLM`. -/
theorem effRetM_nil_data (p : Placement) (δ : LSub) {A : VTy} (hA : A.Data) :
    ∀ (S : Row) (ls : List SRec) (v : Val),
      effRetM (ℍ := ℍ) p [] δ (CTy.effOf S A) [] ls v = Core.effRet (CTy.effOf S A) δ ls v
  | [], ls, v => by
      show vRLM p none [] δ A [] ls v = vC true A ls δ v
      exact vRLMData p [] δ [] A hA ls v
  | o :: S, ls, v => by
      show effRetM p [] δ (CTy.effOf S A) [] ls v = Core.effRet (CTy.effOf S A) δ ls v
      exact effRetM_nil_data p δ hA S ls v

/-- **`NilSoundRetM`**: `nilSoundRet`'s proof at `vRLM`. -/
theorem nilSoundRetM (p : Placement) : NilSoundRetM (ℍ := ℍ) p := by
  intro δ S A ls e ρ hA h
  cases S with
  | nil =>
      show wpTS ls e (fun ls'' => vCE none true A ls'' δ) ρ
      have h' : wpTS ls e (fun ls'' v => vRLM p none [] δ A [] ls'' v) ρ := h
      simpa only [vRLMData p [] δ [] A hA, show extS δ [] [] = δ from rfl] using h'
  | cons o S =>
      show ewpTS ls e (opTable (rowTab o.n o.i o.q o.A o.B (CTy.effOf S A) δ))
        (Core.effRet (CTy.effOf S A) δ) ρ
      have hQ : ∀ ls v ρ, effRetM p [] δ (CTy.effOf S A) [] ls v ρ ↔
          Core.effRet (CTy.effOf S A) δ ls v ρ := fun ls v ρ => by
        rw [effRetM_nil_data p δ hA S ls v]
      refine (GhostEnd.bodyS_nil_iff (δ := δ) hQ).mp ?_
      have h' : cRLM p [] δ (.eff o.n o.i o.q o.A o.B (CTy.effOf S A)) [] ls e ρ := h
      unfold cRLM at h'
      split at h'
      · exact bodySF_bodyS (fun _ _ _ _ _ _ _ h'' => openSF_openS h'') _ h'
      · exact h'

/-- **`Statement0SharedM`**: the relation-independent lemmas (`statement0Shared`'s), the revised
futures at a part (`futPartI`), the nil slice at `vRLM`. -/
theorem statement0SharedM : Statement0SharedM (ℍ := ℍ) :=
  ⟨extPreW, futPartI, futAvoidsTrans, openSFBridge, nilSoundRetM⟩

/-! ### Persistent slots and a solo slot at `vRLM` -/

/-- **At a persistent type `vRLM` holds only at `∅`**, under an environment whose candidates do:
`μ` by its fixed point at the candidate "held at `∅`". -/
theorem vRLM_empty_of_persistent (p : Placement) : ∀ (A : VTy), A.Persistent →
    ∀ (η : Option (Nat → WEnt)), (∀ n v ρ, wEnvP η n v ρ → ρ = PMap.empty) →
    ∀ {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes},
      vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ → ρ = PMap.empty := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ _ _ _ _ _ _ _ h; exact h.1
  | zero => intro _ _ _ _ _ _ _ _ _ h; exact h.elim
  | unk => intro _ _ _ _ _ _ _ _ _ h; exact h.1
  | int w => intro _ _ _ _ _ _ _ _ _ h; exact h.1
  | tvar n => intro _ η hη _ _ _ _ v ρ h; exact hη n v ρ h
  | bang A _ => intro _ _ _ _ _ _ _ _ _ h; exact h.1
  | tensor A B ihA ihB =>
      intro hp η hη σ δ αs ls v ρ h
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      rw [ihA hp.1 η hη h₁, ihB hp.2 η hη h₂] at hc
      exact eq_empty_of_compS_empty hc
  | sum A B ihA ihB =>
      intro hp η hη σ δ αs ls v ρ h
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
      · exact ihA hp.1 η hη (pure_sep_iff.mp hs).2
      · exact ihB hp.2 η hη (pure_sep_iff.mp hs).2
  | box a A ih =>
      intro hp η hη σ δ αs ls v ρ h
      obtain ⟨α, -, hb, -⟩ := h
      exact ih hp η hη hb
  | mu A ih =>
      intro hp η hη σ δ αs ls v ρ h
      obtain ⟨-, -, hlfp⟩ := h
      refine hlfp (fun _ ρ => ρ = PMap.empty) (fun v' ρ' h' => ih hp _ ?_ h')
      intro n v'' ρ'' hn
      cases n with
      | zero => exact hn
      | succ n => exact hη n v'' ρ'' (by rw [wEnvP_eq]; exact hn)
  | thunk _ => intro hp; exact absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | ref _ _ => intro hp; exact absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | imm _ _ _ => intro hp; exact absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | «mut» _ _ _ => intro hp; exact absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | fam _ _ => intro hp; exact absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | opq _ => intro hp; exact absurd hp (by simp [VTy.Persistent, VTy.persistent])

section ctx
variable {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec}

theorem gSepRLM_cons_persistent {T : VTy} (hT : T.Persistent) {Γ : Ctx VTy} {v : Val}
    {γ : List Val} {ρ : WRes} (h : gSepRLM (ℍ := ℍ) p σ δ αs ls (⟨T, true⟩ :: Γ) (v :: γ) ρ) :
    vRLM (ℍ := ℍ) p none σ δ T αs ls v PMap.empty ∧ gSepRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ := by
  obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
  obtain rfl := vRLM_empty_of_persistent p T hT none (fun _ _ _ h => h.elim) hv
  rw [eq_of_compS_empty_left hc]
  exact ⟨hv, hrest⟩

/-- A consumed context, up to persistent slots, holds nothing, at `vRLM`. -/
theorem gSepRLM_deadP : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → ∀ {γ : List Val} {ρ : WRes},
    gSepRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; cases γ <;> exact h.1
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (γ := γ') h
  | drop hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (gSepRLM_cons_persistent hT h).2

/-- **A solo slot's context is the slot's value**, at `vRLM`. -/
theorem gSepRLM_soloP : ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.SoloP Γ i T →
    ∀ {γ : List Val} {ρ : WRes}, i < γ.length → gSepRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ →
      ∃ v, γ[i]? = some v ∧ vRLM (ℍ := ℍ) p none σ δ T αs ls v ρ := by
  intro Γ i T hs
  induction hs with
  | here hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [gSepRLM_deadP hdead hrest] at hc
          rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
          exact ⟨v, rfl, hv⟩
  | there _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨w, hw, hv⟩ := ih (γ := γ') (by simpa using hlen) hg
          exact ⟨w, by simpa using hw, hv⟩
  | skip hS _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨w, hw, hv⟩ :=
            ih (γ := γ') (by simpa using hlen) (gSepRLM_cons_persistent hS hg).2
          exact ⟨w, by simpa using hw, hv⟩

end ctx

/-! ### The guard's views along `Ext` -/

/-- **A cell at any depth lies above a top-level borrow cell it sits in**: each witness is strictly
above its cell (`CellU.wit_inStratum_at`). -/
theorem deepAt_above {ρ : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : DeepAt ρ l ψ)
    (hk : ψ.kind ≠ Kind.own) : ∃ b, CellIn ρ b ∧ b ≤ ψ.at := by
  induction h with
  | top e => exact ⟨_, ⟨_, _, e, hk, le_rfl⟩, le_rfl⟩
  | @wit ρ m l φ ψ em _ ih =>
      obtain ⟨b', ⟨m', ψ', hψ', hk', hle'⟩, hb'⟩ := ih hk
      have hφk : φ.kind ≠ Kind.own := by
        intro hown
        cases φ with
        | own v => simp [CellU.wit] at hψ'
        | imm i => exact absurd hown (by simp [CellU.kind])
        | «mut» mm => exact absurd hown (by simp [CellU.kind])
      have hlt : φ.at < ψ'.at := lt_at_of_inStratum (CellU.wit_inStratum_at φ m' ψ' hψ') hk'
      exact ⟨φ.at, ⟨m, φ, em, hφk, le_rfl⟩, le_trans (le_of_lt hlt) (le_trans hle' hb')⟩

/-- A view reads its list only through the members strictly longer-lived than its cell. -/
theorem vwEW_list_congr_above {s : LSub} {e : LEnt} {α : Life} {ls ls' : List SRec}
    {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (hl : ∀ x : SRec, ψ.at < x.2 → (x ∈ ls ↔ x ∈ ls'))
    (h : vwEW s e true α ls (ResU.single l ψ)) : vwEW s e true α ls' (ResU.single l ψ) := by
  refine ⟨?_, h.2⟩
  obtain ⟨el, ex, eT, ek, ecr⟩ := e
  cases ek with
  | «mut» =>
      obtain ⟨b, u, σ₀, hσ₀, Q, hw, ls₀, hα, hρ, hQ, hls₀, hsupp⟩ := h.1
      have hψ : ψ = CellU.mutOf b u σ₀ hσ₀ Q hw := by
        have := congrArg (fun r => PMap.get r l) hρ
        simp only [ResU.single_get_self] at this
        by_cases hll : l = el
        · subst hll; rw [ResU.single_get_self] at this; exact Option.some.inj this
        · rw [ResU.single_get_ne _ hll] at this; exact absurd this (by simp)
      refine ⟨b, u, σ₀, hσ₀, Q, hw, ls₀, hα, hρ, hQ, fun x => ?_, hsupp⟩
      rw [hls₀ x]
      exact and_congr_left fun hx => hl x (by rw [hψ]; exact hx)
  | imm v =>
      obtain ⟨S, u, σ₀, hσ₀, ls₀, hρ, hP, hα, hls₀⟩ := h.1
      have hψ : ψ = CellU.immOf S u σ₀ hσ₀ := by
        have := congrArg (fun r => PMap.get r l) hρ
        simp only [ResU.single_get_self] at this
        by_cases hll : l = el
        · subst hll; rw [ResU.single_get_self] at this; exact Option.some.inj this
        · rw [ResU.single_get_ne _ hll] at this; exact absurd this (by simp)
      refine ⟨S, u, σ₀, hσ₀, ls₀, hρ, hP, hα, fun x => ?_⟩
      rw [hls₀ x]
      exact and_congr_left fun hx => hl x (by rw [hψ, CellU.at_immOf]; exact hx)

/-- **The guard's views along `Ext`**: every cell the guard reads lies above a top-level borrow
cell (`deepAt_above`), and `Ext` fixes the records strictly longer-lived than such a cell. -/
theorem placeViewsL_ext {s : LSub} {σ : LStack} {αs : List Life} {ls ls' : List SRec}
    {ρ : WRes} (he : Ext ls ls' ρ) (h : PlaceViewsL s σ αs ls ρ) :
    PlaceViewsL s σ αs ls' ρ := by
  have key : ∀ l ψ, DeepAt ρ l ψ → ψ.kind ≠ Kind.own →
      ∀ x : SRec, ψ.at < x.2 → (x ∈ ls ↔ x ∈ ls') := by
    intro l ψ hd hk x hx
    obtain ⟨b, hb, hle⟩ := deepAt_above hd hk
    exact he.2 b hb x (lt_of_le_of_lt hle hx)
  refine ⟨fun l ψ hx ho e α hi => ?_, fun l ψ hd ho hlm => ?_⟩
  · exact vwEW_list_congr_above (key l ψ hx.toDeepAt ho) (h.1 l ψ hx ho e α hi)
  · obtain ⟨e, α, hm, hel, hv⟩ := h.2 l ψ hd ho hlm
    exact ⟨e, α, hm, hel, vwEW_list_congr_above (key l ψ hd ho) hv⟩

/-! ### `[force]` -/

theorem vRLM_thunk_eq (p : Placement) (η : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (C : CTy)
    (αs : List Life) (ls : List SRec) (f : Val) :
    vRLM (ℍ := ℍ) p η σ δ (.thunk C) αs ls f =
      guardPV (extS δ σ αs) σ αs ls (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRLM p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendJ δ σ (fun δ' αs' ls' => cRLM p σ δ' C αs' ls' (forceE C (.val f))) αs ls) := by
  rw [vRLM]

/-- **The `U` clause at the identity, at an extension keeping the tags**: at `binder0` the
instantiation `none` at the extended list, the views read there (`vwSW_local`,
`placeViewsL_ext`); at the other placements the reflexive re-lend and future. -/
theorem force_UMR (p : Placement) {σ : LStack} {δ : LSub} {C : CTy} {αs : List Life}
    {ls ls' : List SRec} {f : Val} {ρ : WRes} (hok : (p.uFut || p.uOwn) = true → ReLend αs αs)
    (hro : RecsOutside αs ls')
    (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ) (he : Ext ls ls' ρ)
    (hkt : KeepsT ls ls' ρ) (h : vRLM (ℍ := ℍ) p none σ δ (.thunk C) αs ls f ρ) :
    cRLM (ℍ := ℍ) p σ δ C αs ls' (forceE C (.val f)) ρ := by
  rw [vRLM_thunk_eq] at h
  have h' := h ht hpv
  split at h'
  · obtain ⟨ds, ρz, ρn, hcomp, hn, -, H⟩ := h'
    exact (H ls' (he.left hcomp) αs (hok (by assumption)) σ αs (futQ_refl _ δ ρz _)
      (futAvoids_self C σ)).1 ρn ρ (GhostEnd.vwS_local (he.right hcomp) hn) hcomp
  · obtain ⟨ds, ρz, ρn, hcomp, hn, -, H⟩ := h'
    have hl : Inst.life none αs = αs := Inst.life_none αs
    have := H none (fun c θ h => by cases h) ls' (he.left hcomp) (hkt.left hcomp)
      (keepsS_of_keepsT (hkt.right hcomp)) (by rw [hl]; exact hro) ρn ρ
      (by rw [hl]; exact ⟨vwSW_local (he.right hcomp) hn.1, placeViewsL_ext (he.right hcomp) hn.2⟩)
      hcomp
    rwa [hl] at this

/-- `force_UMR` at a stack in shape, where the reflexive re-lend holds. -/
theorem force_UM (p : Placement) {σ : LStack} {δ : LSub} {C : CTy} {αs : List Life}
    {ls ls' : List SRec} {f : Val} {ρ : WRes} (hok : StackOK σ αs) (hro : RecsOutside αs ls')
    (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ) (he : Ext ls ls' ρ)
    (hkt : KeepsT ls ls' ρ) (h : vRLM (ℍ := ℍ) p none σ δ (.thunk C) αs ls f ρ) :
    cRLM (ℍ := ℍ) p σ δ C αs ls' (forceE C (.val f)) ρ :=
  force_UMR p (fun _ => GhostEnd.reLend_refl hok.2.1) hro ht hpv he hkt h

/-- **`ForceRowM`, at every placement whose `U` clause reads the identity instantiation**
(`binder0`): there the identity is read at every stack, blocks admitted. A placement whose `U`
clause reads `ReLend` (`cbpv`, `binder`) reads the reflexive re-lend, which a block stack's
non-strict chain is not. -/
theorem forceRowM (p : Placement) (hp : (p.uFut || p.uOwn) = false) : ForceRowM (ℍ := ℍ) p := by
  intro Δ Γ i C hsolo _ _ δ σ αs ls γ ρ _ _ _ _ _ hro _ ht hpv hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  obtain ⟨v, hv, hval⟩ := gSepRLM_soloP hsolo (hsolo.lt_of_liveWithin hlw) hgs
  show cRLM p σ δ C αs ls (substAll γ (forceE C (.var i))) ρ
  rw [substAll_forceE' hv]
  exact force_UMR p (fun h => absurd h (by rw [hp]; decide)) hro ht hpv (Ext.refl ls ρ)
    (keepsT_refl ls ρ) hval

/-! ### The callbacks at `σ·y` -/

/-- The own lend at the stack itself, at `vRLM`. -/
theorem all_ownM {p : Placement} (hp : p.allOwn = true) {σ : LStack} {δ : LSub} {y : LifeVar}
    {c : Lifetime.Life} {C' : CTy} {αs : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cRLM (ℍ := ℍ) p σ δ (.all y c C') αs ls e ρ) {en : LEnt} {α : Life}
    (hpush : OwnPushM δ (.all y c C') ρ (σ, αs) en α) (hro : RecsOutside (α :: αs) ls)
    (hsf : SubFresh δ α) (ht : TabAtS (en :: σ) (α :: αs) ρ)
    (hpv : PlaceViewsL (extS (δ.extend y α) (en :: σ) (α :: αs)) (en :: σ) (α :: αs) ls ρ) :
    cRLM (ℍ := ℍ) p (en :: σ) (δ.extend y α) C' (α :: αs) ls (.app e (.val .unit)) ρ :=
  (h ls σ αs (extQ_refl _ ls ρ) (by unfold FutQI; split <;> first | exact .refl | rfl)
    (futAvoids_self _ σ)).2.1 hp en α hpush hro hsf ht hpv

/-- `⊸` at the stack itself, at `vRLM`. -/
theorem arr_appM {p : Placement} {σ : LStack} {δ : LSub} {A : VTy} {D : CTy} {αs : List Life}
    {ls : List SRec} {e : Expr} {w : Val} {ρf ρv ρ : WRes}
    (h : cRLM (ℍ := ℍ) p σ δ (.arr A D) αs ls e ρf) (hw : vRLM (ℍ := ℍ) p none σ δ A αs ls w ρv)
    (hc : ResU.CompS ρf ρv ρ) (ht : TabAtS σ αs ρ)
    (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ) :
    cRLM (ℍ := ℍ) p σ δ D αs ls (.app e (.val w)) ρ :=
  h ls σ αs (extQ_refl _ ls ρf) (by unfold FutQI; split <;> first | exact .refl | rfl)
    (futAvoids_self _ σ) w ρv ρ hw hc ht hpv

/-- **The 6.65 callback at `σ·y`, at a placement whose `∀` clause makes the own lend.** -/
theorem callbackExtMutM_own (p : Placement) (hp : p.allOwn = true) :
    CallbackExtMutM (ℍ := ℍ) p := by
  intro σ δ y c T D αs ls f w ρf e α ρv ρ hfree hok _ hro _ hex hk heT hy hown hlt hro' hsf htf
    hpvf hf hw hc ht hpv
  have hall := force_UM p hok hro htf hpvf (Ext.refl ls ρf) (keepsT_refl ls ρf) hf
  have hpush : OwnPushM δ (.all y c (.arr (.mut (.var y) T) D)) ρf (σ, αs) e α :=
    ⟨⟨y, c, _, rfl, hex, fun h => hy (by simpa [CTy.binders] using h), hown, hlt,
      fun A D' h => by
        obtain ⟨rfl, rfl⟩ : A = .mut (.var y) T ∧ D' = D := by simpa using h.symm
        exact ⟨rfl, by rw [hk]; trivial, heT⟩⟩,
      fun y' hy' => by
        rw [heT] at hy'
        exact Or.inr ⟨fun h => hfree (h ▸ hy'), Or.inl (Or.inr hy')⟩,
      by rw [hex, heT]; exact hfree⟩
  exact arr_appM (all_ownM hp hall hpush hro' hsf (tabAtS_left hc ht) (placeViewsL_left hc hpv))
    hw hc ht hpv

/-- **The 6.64 callback at `σ·y`, at a placement whose `∀` clause makes the own lend**: the force at
the extended list (`force_UM`, the views carried along `Ext`). -/
theorem callbackExtImmM_own (p : Placement) (hp : p.allOwn = true) :
    CallbackExtImmM (ℍ := ℍ) p := by
  intro σ δ y c T D αs ls ls' f w ρf e u α ρv ρ hfree hok _ _ _ hex hk heT hy hown hlt hro' hsf
    htf hpvf he hkt hf hw hc ht hpv
  have hro'' : RecsOutside αs ls' := fun a ha => hro' a (List.mem_cons_of_mem _ ha)
  have hall := force_UM p hok hro'' htf hpvf he hkt hf
  have hpush : OwnPushM δ (.all y c (.arr (.imm (.var y) T) D)) ρf (σ, αs) e α :=
    ⟨⟨y, c, _, rfl, hex, fun h => hy (by simpa [CTy.binders] using h), hown, hlt,
      fun A D' h => by
        obtain ⟨rfl, rfl⟩ : A = .imm (.var y) T ∧ D' = D := by simpa using h.symm
        exact ⟨rfl, by rw [hk]; trivial, heT⟩⟩,
      fun y' hy' => by
        rw [heT] at hy'
        exact Or.inr ⟨fun h => hfree (h ▸ hy'), Or.inl (Or.inr hy')⟩,
      by rw [hex, heT]; exact hfree⟩
  exact arr_appM (all_ownM hp hall hpush hro' hsf (tabAtS_left hc ht) (placeViewsL_left hc hpv))
    hw hc ht hpv


theorem callbackExtMutM_binder0 : CallbackExtMutM (ℍ := ℍ) .binder0 := callbackExtMutM_own _ rfl
theorem callbackExtImmM_binder0 : CallbackExtImmM (ℍ := ℍ) .binder0 := callbackExtImmM_own _ rfl
theorem callbackExtMutM_binder : CallbackExtMutM (ℍ := ℍ) .binder := callbackExtMutM_own _ rfl
theorem callbackExtImmM_binder : CallbackExtImmM (ℍ := ℍ) .binder := callbackExtImmM_own _ rfl

/-! ### Statement 0 at `binder0` -/

/-- **`Statement0MBesideMono0`**: every fact of statement 0 beside monotonicity holds at `binder0`
at `vRLM`: the shared lemmas at the revised futures, the callbacks at `σ·y`, `[force]`, and the
`U` side at every context (R1 closed, `statement0UFullM`). -/
theorem statement0MBesideMono0 : Statement0MBesideMono0 (ℍ := ℍ) :=
  ⟨statement0SharedM, callbackExtMutM_binder0, callbackExtImmM_binder0, forceRowM .binder0 rfl,
    statement0UFullM⟩

/-- **`Statement0M binder0` as stated is refuted**, with the three unrestricted monotonicity
statements it bundles (`monoUnrestrictedRefuted0`), at a configuration not shown to arise: a fact
about the bundle's statements, not `binder0`'s status. -/
theorem not_statement0M_binder0 : ¬ Statement0M (ℍ := ℍ) .binder0 :=
  fun h => notMonoOwnGM0 h.1

/-- **Statement 0 at `binder0` read at its consumers reduces to its `[allI]` row**: every other
conjunct is proved. -/
theorem statement0MAtConsumers0_iff :
    Statement0MAtConsumers0 (ℍ := ℍ) ↔ AllIRowM (ℍ := ℍ) .binder0 :=
  ⟨fun h => h.2.2, fun h => ⟨statement0MBesideMono0, monoExtM0, h⟩⟩

end ProbeD1

end
