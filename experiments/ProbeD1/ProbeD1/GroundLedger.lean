import ProbeD1.NxRecon
import Core.Demonic
import Core.Embedding

/-!
# ProbeD1 — the grounding ledger's theorems (`GROUND.md` §2.9, `LEDGER.md`)

Each draft definition with a Core counterpart is set against it in `LEDGER.md`; this file holds the
theorems the ledger cites where it says two definitions agree, or one is inside the other. Every
row the ledger marks *planned* that is not proved here is a `def … : Prop` here with no proof.

* **The draft is Core at first-order judgements, at every stack.** At a flat type the draft value
  relation is Core's (`vRLMFlat`, G1: `vRLM_dataE`'s induction widened by `Unk`, opaque types,
  `[@a]`, `Ref`, a persistent non-thunk and `[L]`). At a first-order argument it is inside Core's
  (`vRLMFOArg`, G2: the leaves' first conjunct is Core's leaf). At a first-order computation type
  Core's computation relation is inside the draft's (`coreSubWComp`, G4: `binder0` reads no future
  and no instantiation at `⊸`, `&` and `F`, and `guardPV` only adds hypotheses). So Core's own
  derivation gives the draft's semantic judgement at every first-order judgement, at every index
  (`coreToSemSM`, G5). `gRestrict` places G1 and G2 under the two agreement statements the draft
  already has (`WInsideCoreM`, `CoreInsideWM`).
* **A closed first-order value at every index** (`coreValToW`, G5v): a value Core relates at every
  reading at the empty resource, at a thunk or persistent thunk of a first-order computation type,
  is the draft's at every index: the `U` clause asks the forced value at each instantiated
  reading, where Core's fact holds on its own, and the box asks the same at each box world.
  Core's semantic judgement of a value at a dead context gives that fact through `wpTS`'s
  post-configuration at the empty frame (`vC_of_wpTS_val_empty`), so a syntactic value Core derives
  at a dead context is the draft's at every index (`coreToSemSMConst`, G5c).
* **The same at the empty stack** (G3 `vRLMNilTy`, G4′ `coreSubWNil`, G5′ `coreToSemSMNil`): at
  `[]` the leaves are Core's, and Core's thunks are the draft's, for every semantic value: the
  empty stack has only the identity instantiation (`vRLMThunkNil`).
* **The empty-stack judgement and the floor** (G6): `SemSMNil`, its derivation from `SemSM`
  (`semSMNilOfSemSM`), and the floor's two statements `DraftFL`, `DraftFLNil`, stated, not claimed.
* **The unfoldings** (G7, G7′): the guard, the `U` clause, `⊸` and `∀` at the empty stack; the
  data leaves, `⊤` and `ν`, `&`, `effRetM` and `gRLM` at every stack; `SemIdxM` at the empty
  stack.
* **Arising, typing, adequacy** (G8–G11): the revised arising set's worlds are tagged `TW` worlds
  and every tagged `TW` world arises at the empty stack; `CDerivesNU` programs are `ProbeRules`
  programs; the draft's acceptance at the empty stack at `F 1` gives adequacy; the pointwise table
  fails at `innerView`; the revised arising set is inside the first.
* **The rows** (§2.6): `fundamentalC`'s constructors read at `SemSM .binder0`, the ones the suite
  names, as statements.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView)

/-! ### The type classes -/

/-- **Types at which the draft relation is Core's at every stack**, `k` variables bound: Core's
`VTy.DataB` with `Unk`, opaque types, `[@a]`, `Ref`, a persistent non-thunk and `[L]` added. -/
inductive FlatB : Nat → VTy → Prop
  | unit (k : Nat) : FlatB k .unit
  | zero (k : Nat) : FlatB k .zero
  | unk (k : Nat) : FlatB k .unk
  | int (k : Nat) (w : Width) : FlatB k (.int w)
  | opq (k : Nat) (o : Opaque) : FlatB k (.opq o)
  | tvar {k n : Nat} : n < k → FlatB k (.tvar n)
  | tensor {k : Nat} {A B : VTy} : FlatB k A → FlatB k B → FlatB k (.tensor A B)
  | sum {k : Nat} {A B : VTy} : FlatB k A → FlatB k B → FlatB k (.sum A B)
  | box {k : Nat} {a : Lifetime.Life} {A : VTy} : FlatB k A → FlatB k (.box a A)
  | ref {k : Nat} {A : VTy} : FlatB k A → FlatB k (.ref A)
  | bang {k : Nat} {A : VTy} : (∀ C, A ≠ .thunk C) → FlatB k A → FlatB k (.bang A)
  | fam {k : Nat} {L : VTy} : FlatB k L → FlatB k (.fam L)
  | mu {k : Nat} {A : VTy} : FlatB (k + 1) A → FlatB k (.mu A)

/-- A closed flat type. -/
def FlatTy (A : VTy) : Prop := FlatB 0 A

/-- **First-order arguments**: the draft relation is inside Core's at every stack. -/
inductive FOArg : VTy → Prop
  | flat {A : VTy} : FlatTy A → FOArg A
  | mut (a : Lifetime.Life) (T : VTy) : FOArg (.mut a T)
  | imm (a : Lifetime.Life) (T : VTy) : FOArg (.imm a T)
  | tensor {A B : VTy} : FOArg A → FOArg B → FOArg (.tensor A B)
  | sum {A B : VTy} : FOArg A → FOArg B → FOArg (.sum A B)
  | box {a : Lifetime.Life} {A : VTy} : FOArg A → FOArg (.box a A)
  | ref {A : VTy} : FOArg A → FOArg (.ref A)
  | fam {L : VTy} : FOArg L → FOArg (.fam L)

/-- **First-order computation types** with no lifetime `∀` and no row. -/
inductive FOComp : CTy → Prop
  | ret {B : VTy} : FlatTy B → FOComp (.ret B)
  | arr {A : VTy} {C : CTy} : FOArg A → FOComp C → FOComp (.arr A C)
  | amp {C D : CTy} : FOComp C → FOComp D → FOComp (.amp C D)
  | top : FOComp .top
  | nu (C : CTy) : FOComp (.nu C)

/-- Every live slot is a first-order argument. -/
def CtxFO (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → FOArg s.ty

/-- **Types of first-order constants**: a thunk, or a persistent thunk, of a first-order
computation type. -/
inductive FOConstTy : VTy → Prop
  | thunk {C : CTy} : FOComp C → FOConstTy (.thunk C)
  | bang {C : CTy} : FOComp C → FOConstTy (.bang (.thunk C))

/-! ### G1: at a flat type the draft relation is Core's, at every stack -/

/-- **G1.** At a flat type the draft relation is Core's, at every stack (`VRLMData` widened). -/
def VRLMFlat : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (A : VTy), FlatTy A →
    ∀ (ls : List SRec) (v : Val),
      vRLM (ℍ := ℍ) p none σ δ A αs ls v = vC true A ls (extS δ σ αs) v

/-- **G1 under an environment**, pointwise: `vRLM_dataE`'s induction with the cases `Unk`, opaque,
`[@a]`, `Ref`, a persistent non-thunk and `[L]` added, each one clause shape on each side. -/
theorem vRLM_flatE (p : Placement) : ∀ {k : Nat} {A : VTy}, FlatB k A →
    ∀ (η : Option (Nat → WEnt)) (ηc : Option (Nat → TEnt)) (σ : LStack) (δ : LSub)
      (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
      EnvCore η ηc ls →
      (vRLM (ℍ := ℍ) p η σ δ A αs ls v ρ ↔ vCE ηc true A ls (extS δ σ αs) v ρ)
  | _, _, .unit _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, .zero _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, .unk _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, .int _ _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, .opq _ _, _, _, _, _, _, _, _, _, _ => Iff.rfl
  | _, _, @FlatB.tvar _ n _, η, ηc, _, _, _, ls, v, ρ, hE => hE.2 n v ρ
  | _, _, .tensor hA hB, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
          (vRLM_flatE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mp h₁,
          (vRLM_flatE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mp h₂⟩
      · rintro ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
          (vRLM_flatE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mpr h₁,
          (vRLM_flatE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mpr h₂⟩
  | _, _, .sum hA hB, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro (⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩)
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, (vRLM_flatE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mp h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, (vRLM_flatE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mp h₂⟩
      · rintro (⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩)
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, (vRLM_flatE p hA η ηc σ δ αs ls v₁ ρ₁ hE).mpr h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, (vRLM_flatE p hB η ηc σ δ αs ls v₂ ρ₂ hE).mpr h₂⟩
  | _, _, .box hA, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro ⟨α, ha, hP, hout⟩
        exact ⟨α, ha, (vRLM_flatE p hA η ηc σ δ αs ls v ρ hE).mp hP, hout⟩
      · rintro ⟨α, ha, hP, hout⟩
        exact ⟨α, ha, (vRLM_flatE p hA η ηc σ δ αs ls v ρ hE).mpr hP, hout⟩
  | _, _, .ref hA, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩
        exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
          (vRLM_flatE p hA η ηc σ δ αs ls v' ρ₂ hE).mp h₂⟩
      · rintro ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩
        exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
          (vRLM_flatE p hA η ηc σ δ αs ls v' ρ₂ hE).mpr h₂⟩
  | _, _, .bang hnt hA, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro ⟨h0, hv, -⟩
        exact ⟨h0, (vRLM_flatE p hA η ηc σ δ αs ls v ρ hE).mp hv⟩
      · rintro ⟨h0, hv⟩
        exact ⟨h0, (vRLM_flatE p hA η ηc σ δ αs ls v ρ hE).mpr hv, pBox_of_not_thunk hnt⟩
  | _, _, .fam hL, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      constructor
      · rintro ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩
        exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m ρ' h =>
          (vRLM_flatE p hL η ηc σ δ αs ls (.loc m) ρ' hE).mp h) hs⟩
      · rintro ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩
        exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m ρ' h =>
          (vRLM_flatE p hL η ηc σ δ αs ls (.loc m) ρ' hE).mpr h) hs⟩
  | _, _, @FlatB.mu _ A hA, η, ηc, σ, δ, αs, ls, v, ρ, hE => by
      have hM : wClose η (.mu A) = tClose ηc (.mu A) := wClose_tClose hE.1 (.mu A)
      constructor
      · rintro ⟨hnm, hcl, hlfp⟩
        refine ⟨hnm, hM ▸ hcl, fun P hP => ?_⟩
        refine hlfp (fun v ρ => P true ls v ρ) (fun v' ρ' h' => hP true ls v' ρ' ?_)
        refine (vRLM_flatE p hA _ (some (VTy.scons ⟨tClose ηc (.mu A), P⟩ (tEnv ηc))) σ δ αs ls
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
        refine hQ v' ρ' ((vRLM_flatE p hA (some (VTy.scons ⟨wClose η (.mu A), Q⟩ (wEnv η))) _ σ δ αs
          ls' v' ρ' ⟨fun n => ?_, fun n v'' ρ'' => ?_⟩).mpr h')
        · cases n with
          | zero => exact hM
          | succ n => exact hE.1 n
        · cases n with
          | zero => exact ⟨fun h _ _ => h, fun h => h rfl rfl⟩
          | succ n =>
              show (wEnv η n).P v'' ρ'' ↔ (tEnv ηc n).P true ls' v'' ρ''
              rw [← wEnvP_eq, ← tEnvP_eq]; exact hE.2 n v'' ρ''

/-- **G1** (`VRLMFlat`). -/
theorem vRLMFlat : VRLMFlat (ℍ := ℍ) := by
  intro p σ δ αs A hA ls v
  funext ρ
  exact propext (vRLM_flatE p hA none none σ δ αs ls v ρ (envCoreNone ls))

/-! ### G2: at a first-order argument the draft relation is inside Core's -/

/-- **G2.** At a first-order argument type the draft relation is inside Core's. -/
def VRLMFOArg : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (A : VTy), FOArg A →
    ∀ (ls : List SRec) (v : Val) (ρ : WRes),
      vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vC true A ls (extS δ σ αs) v ρ

theorem vRLM_foArg (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) :
    ∀ {A : VTy}, FOArg A → ∀ (ls : List SRec) (v : Val) (ρ : WRes),
      vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vC true A ls (extS δ σ αs) v ρ
  | _, .flat hA, ls, v, ρ, h =>
      (vRLM_flatE p hA none none σ δ αs ls v ρ (envCoreNone ls)).mp h
  | _, .mut _ _, _, _, _, h => h.1
  | _, .imm _ _, _, _, _, h => h.1
  | _, .tensor hA hB, ls, _, _, ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ =>
      ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', vRLM_foArg p σ δ αs hA ls v₁ ρ₁ h₁,
        vRLM_foArg p σ δ αs hB ls v₂ ρ₂ h₂⟩
  | _, .sum hA _, ls, _, _, Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ =>
      Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vRLM_foArg p σ δ αs hA ls v₁ ρ₁ h₁⟩
  | _, .sum _ hB, ls, _, _, Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩ =>
      Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vRLM_foArg p σ δ αs hB ls v₂ ρ₂ h₂⟩
  | _, .box hA, ls, v, ρ, ⟨α, ha, hP, hout⟩ =>
      ⟨α, ha, vRLM_foArg p σ δ αs hA ls v ρ hP, hout⟩
  | _, .ref hA, ls, _, _, ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ =>
      ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, vRLM_foArg p σ δ αs hA ls v' ρ₂ h₂⟩
  | _, .fam hL, ls, _, _, ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ =>
      ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m ρ' h =>
        vRLM_foArg p σ δ αs hL ls (.loc m) ρ' h) hs⟩

/-- **G2** (`VRLMFOArg`). -/
theorem vRLMFOArg : VRLMFOArg (ℍ := ℍ) :=
  fun p σ δ αs _ hA ls v ρ h => vRLM_foArg p σ δ αs hA ls v ρ h

/-! ### C14: the context relation, given its slots -/

/-- **C14: `gRLM` is Core's `gDenC` given the live slots' clauses, and inside it given
containment** (G5's route reads the second half, with G2 at each first-order slot). -/
def GRLMOfSlots : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (Γ : Ctx VTy),
    ((∀ s ∈ Γ, s.live = true → ∀ v, vRLM (ℍ := ℍ) p none σ δ s.ty αs ls v =
        vC true s.ty ls (extS δ σ αs) v) →
      ∀ γ, gRLM (ℍ := ℍ) p σ δ αs ls Γ γ = gDenC ls (extS δ σ αs) Γ γ) ∧
    ((∀ s ∈ Γ, s.live = true → ∀ v ρ, vRLM (ℍ := ℍ) p none σ δ s.ty αs ls v ρ →
        vC true s.ty ls (extS δ σ αs) v ρ) →
      ∀ γ ρ, gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gDenC ls (extS δ σ αs) Γ γ ρ)

theorem gSepRLM_eq_gSepC {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life}
    {ls : List SRec} : ∀ (Γ : Ctx VTy), (∀ s ∈ Γ, s.live = true → ∀ v,
      vRLM (ℍ := ℍ) p none σ δ s.ty αs ls v = vC true s.ty ls (extS δ σ αs) v) →
    ∀ γ, gSepRLM (ℍ := ℍ) p σ δ αs ls Γ γ = gSepC ls (extS δ σ αs) Γ γ
  | [], _, γ => by cases γ <;> rfl
  | _ :: _, _, [] => rfl
  | s :: Γ, h, v :: γ => by
      have ih := gSepRLM_eq_gSepC Γ (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')) γ
      by_cases hl : s.live = true
      · simp only [gSepRLM, gSepC, hl, if_true]
        rw [h s List.mem_cons_self hl v, ih]
      · simp only [gSepRLM, gSepC, hl]
        exact ih

theorem gSepRLM_to_gSepC {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life}
    {ls : List SRec} : ∀ (Γ : Ctx VTy), (∀ s ∈ Γ, s.live = true → ∀ v ρ,
      vRLM (ℍ := ℍ) p none σ δ s.ty αs ls v ρ → vC true s.ty ls (extS δ σ αs) v ρ) →
    ∀ γ ρ, gSepRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gSepC ls (extS δ σ αs) Γ γ ρ
  | [], _, γ, _, h => by cases γ <;> exact h
  | _ :: _, _, [], _, h => h
  | s :: Γ, h, v :: γ, ρ, hg => by
      have ih := gSepRLM_to_gSepC Γ (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')) γ
      by_cases hl : s.live = true
      · simp only [gSepRLM, gSepC, hl, if_true] at hg ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := hg
        exact ⟨ρ₁, ρ₂, hc, h s List.mem_cons_self hl v ρ₁ h₁, ih ρ₂ h₂⟩
      · simp only [gSepRLM, gSepC, hl] at hg ⊢
        exact ih ρ hg

/-- **C14** (`GRLMOfSlots`). -/
theorem gRLMOfSlots : GRLMOfSlots (ℍ := ℍ) := by
  intro p σ δ αs ls Γ
  refine ⟨fun h γ => ?_, fun h γ ρ hg => ?_⟩
  · show (⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLM p σ δ αs ls Γ γ) = (⌜Ctx.LiveWithin Γ γ⌝ ⋆ _)
    rw [gSepRLM_eq_gSepC Γ h γ]
  · obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
    exact gDenC_mk hlw (gSepRLM_to_gSepC Γ h γ ρ hgs)

/-- A context of first-order slots: the draft's context relation is inside Core's. -/
theorem gRLM_to_gDenC_FO {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life}
    {ls : List SRec} {Γ : Ctx VTy} (hΓ : CtxFO Γ) {γ : List Val} {ρ : WRes}
    (hg : gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ) : gDenC ls (extS δ σ αs) Γ γ ρ :=
  (gRLMOfSlots (ℍ := ℍ) p σ δ αs ls Γ).2
    (fun s hs hl v ρ' h => vRLM_foArg p σ δ αs (hΓ s hs hl) ls v ρ' h) γ ρ hg

/-! ### G4: at a first-order computation type, Core's relation is inside the draft's -/

/-- **G4.** At a first-order computation type, Core's relation is inside the draft's, at every
stack. -/
def CoreSubWComp : Prop :=
  ∀ (C : CTy), FOComp C → ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec)
    (e : Expr) (ρ : WRes),
    cC C ls (extS δ σ αs) e ρ → cRLM (ℍ := ℍ) .binder0 σ δ C αs ls e ρ

/-- **`binder0`'s `⊸` clause, unfolded**: no future and no record extension, the guard at the stack
itself. -/
theorem cRLM_arr_binder0 {σ : LStack} {δ : LSub} {A : VTy} {C : CTy} {αs : List Life}
    {ls : List SRec} {e : Expr} {ρ : WRes} :
    cRLM (ℍ := ℍ) .binder0 σ δ (.arr A C) αs ls e ρ ↔
      ∀ v, (vRLM (ℍ := ℍ) .binder0 none σ δ A αs ls v ─⋆
        guardPV (extS δ σ αs) σ αs ls (cRLM (ℍ := ℍ) .binder0 σ δ C αs ls (.app e (.val v)))) ρ := by
  constructor
  · intro h v
    exact h ls σ αs (extQ_refl _ ls ρ) (by unfold FutQI; split <;> first | exact .refl | rfl)
      (futAvoids_self _ σ) v
  · intro h ls' σ' αs' hE hF _ v
    have hE' : ls' = ls := by simpa [ExtQ, Placement.bindFut] using hE
    have hF' : (σ', αs') = (σ, αs) := by simpa [FutQI, Placement.bindFut] using hF
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hF'
    subst hE'
    exact h v

theorem coreSubWComp_go : ∀ {C : CTy}, FOComp C → ∀ (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) (e : Expr) (ρ : WRes),
    cC C ls (extS δ σ αs) e ρ → cRLM (ℍ := ℍ) .binder0 σ δ C αs ls e ρ
  | _, .ret hB, σ, δ, αs, _, _, ρ, h =>
      wpTS_mono (fun ls' v ρ' hv =>
        (vRLM_flatE .binder0 hB none none σ δ αs ls' v ρ' (envCoreNone ls')).mpr hv) ρ h
  | _, .arr hA hC, σ, δ, αs, ls, _, _, h =>
      cRLM_arr_binder0.mpr fun v ρ₁ ρ₂ hv hc _ _ =>
        coreSubWComp_go hC σ δ αs ls _ ρ₂ (h v ρ₁ ρ₂ (vRLM_foArg .binder0 σ δ αs hA ls v ρ₁ hv) hc)
  | _, .amp hC hD, σ, δ, αs, ls, _, ρ, h =>
      ⟨coreSubWComp_go hC σ δ αs ls _ ρ h.1, coreSubWComp_go hD σ δ αs ls _ ρ h.2⟩
  | _, .top, _, _, _, _, _, _, _ => trivial
  | _, .nu _, _, _, _, _, _, _, h => h

/-- **G4** (`CoreSubWComp`). -/
theorem coreSubWComp : CoreSubWComp (ℍ := ℍ) :=
  fun _ hC σ δ αs ls e ρ h => coreSubWComp_go hC σ δ αs ls e ρ h

/-! ### G5: the floor at first-order judgements -/

/-- **G5. The floor at first-order judgements**: Core's derivation gives the draft's semantic
judgement at every index. -/
def CoreToSemSM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CtxFO Γ → FOComp (jdgCty j) →
    CDerives Δ Γ e j → SemSM (ℍ := ℍ) .binder0 Δ Γ e j

/-- `fundamentalC` at the judgement's computation type. -/
theorem semC_jdgCty {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    SemC Δ Γ e (jdgCty j) := by
  have hJ := fundamentalC h
  cases j with
  | val A => exact hJ
  | comp C => exact hJ

/-- **G5** (`CoreToSemSM`): at the index, `gRLM` gives `gDenC` at the stack's reading (G2 at each
slot), and `Δ`'s models hold there; `fundamentalC` gives `cC` there, and G4 gives `cRLM`. No
instantiation is read. -/
theorem coreToSemSM : CoreToSemSM (ℍ := ℍ) := by
  intro Δ Γ e j hΓ hC h _ _ δ σ αs ls γ ρ _ _ _ _ hMod _ _ _ _ hg
  exact coreSubWComp_go hC σ δ αs ls _ ρ
    (semC_jdgCty h (extS δ σ αs) γ ls ρ hMod (gRLM_to_gDenC_FO hΓ hg))

/-! ### `GRestrict`: G1 and G2 as restrictions of the two stated agreement facts -/

/-- `WInsideCoreM` at the types `P` admits. -/
def WInsideCoreMOn (p : Placement) (P : VTy → Prop) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    P A → StackOK σ αs → TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ → vC true A ls (extS δ σ αs) v ρ

/-- `CoreInsideWM` at the types `P` admits. -/
def CoreInsideWMOn (p : Placement) (P : VTy → Prop) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (A : VTy) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    P A → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vC true A ls (extS δ σ αs) v ρ → vRLM (ℍ := ℍ) p none σ δ A αs ls v ρ

/-- **G1 and G2 restrict the two stated agreement facts**: at every type the restricted forms are
`WInsideCoreM` and `CoreInsideWM`; G2 gives the first at first-order arguments and G1 the second
at flat types, the index hypotheses unused. -/
def GRestrict : Prop :=
  (∀ p, WInsideCoreMOn (ℍ := ℍ) p (fun _ => True) ↔ WInsideCoreM (ℍ := ℍ) p) ∧
  (∀ p, CoreInsideWMOn (ℍ := ℍ) p (fun _ => True) ↔ CoreInsideWM (ℍ := ℍ) p) ∧
  (VRLMFOArg (ℍ := ℍ) → ∀ p, WInsideCoreMOn (ℍ := ℍ) p FOArg) ∧
  (VRLMFlat (ℍ := ℍ) → ∀ p, WInsideCoreMOn (ℍ := ℍ) p FlatTy ∧ CoreInsideWMOn (ℍ := ℍ) p FlatTy)

/-- **`GRestrict`.** -/
theorem gRestrict : GRestrict (ℍ := ℍ) := by
  refine ⟨fun p => ⟨fun h σ δ A αs ls v ρ => h σ δ A αs ls v ρ trivial,
      fun h σ δ A αs ls v ρ _ => h σ δ A αs ls v ρ⟩,
    fun p => ⟨fun h σ δ A αs ls v ρ => h σ δ A αs ls v ρ trivial,
      fun h σ δ A αs ls v ρ _ => h σ δ A αs ls v ρ⟩,
    fun hG p σ δ A αs ls v ρ hA _ _ _ hv => hG p σ δ αs A hA ls v ρ hv,
    fun hG p => ⟨fun σ δ A αs ls v ρ hA _ _ _ hv => ?_, fun σ δ A αs ls v ρ hA _ _ _ _ _ hv => ?_⟩⟩
  · rw [hG p σ δ αs A hA ls v] at hv; exact hv
  · rw [hG p σ δ αs A hA ls v]; exact hv

/-! ### G5v, G5c: first-order values at every index -/

/-- A substitution keeps a value a value. -/
theorem isVal_psub (k : Nat) (γ : List Val) : ∀ {e : Expr}, IsVal e → IsVal (Expr.psub k γ e)
  | _, .unit => .unit
  | _, .pair h₁ h₂ => .pair (isVal_psub k γ h₁) (isVal_psub k γ h₂)
  | _, .inj₁ h => .inj₁ (isVal_psub k γ h)
  | _, .inj₂ h => .inj₂ (isVal_psub k γ h)
  | _, .lam => .lam
  | _, .loc => .loc
  | _, .prim => .prim
  | _, .storeV h => .storeV (isVal_psub k γ h)

/-- A run under an allocator from a value is empty. -/
theorem aRun_from_val {A : BoCa.BoLo.Alloc} {w : Val} :
    ∀ {k k' : Nat} {μ μ' : BoCa.BoLo.Heap} {e e' : Expr},
    BoCa.BoLo.ARun (ℍ := ℍ) A k μ e k' μ' e' → e = Expr.val w → μ' = μ ∧ e' = e
  | _, _, _, _, _, _, .refl _ _ _, _ => ⟨rfl, rfl⟩
  | _, _, _, _, _, _, .more hs _, he => absurd (he ▸ hs.toStep1) BoCa.BoLo.no_step_val

/-- **`wpTS` at a value, from the empty list and the empty resource, gives its postcondition
there**: at the empty frame the run is empty, so the post-world lowers to the empty heap; its
flattening holds no cell, so neither does the post-resource, and the list has no member. -/
theorem post_of_wpTS_val_empty {w : Val} {Q : List SRec → Val → WProp}
    (h : wpTS [] (.val w) Q PMap.empty) : Q [] w PMap.empty := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', -, h₂, -, h₅, h₆, h₇, ⟨k', hrun⟩, -, -, -, -,
    -, -, hls, hC⟩ := h PMap.empty PMap.empty [] BoCa.Fig16.LogRel.hash_empty
      (ResU.comp_empty_right _) TW.empty (fun x hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨hμ, hv⟩ := aRun_from_val hrun rfl
  have hvw : v = w := Subtype.ext hv
  subst hvw hμ
  have hls' : ls' = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    simpa using (hls x).mp hx
  subst hls'
  -- the empty frame lowers to the empty heap
  obtain ⟨σ₀, hσ₀, hm₀⟩ := h₅
  have hσ₀e : σ₀ = PMap.empty := ResU.Flat.functional hσ₀ BoCa.Fig16.BoLo.flat_empty
  subst hσ₀e
  -- so the post-world's flattening holds no cell, and neither does the post-world
  obtain ⟨σ₁, hσ₁, hm₁⟩ := h₇
  have hW : fρ'p = PMap.empty := by
    apply PMap.ext
    intro l
    rw [PMap.empty_get]
    cases e : fρ'p.get l with
    | none => rfl
    | some ψ =>
        obtain ⟨χ, hχ, -⟩ := ResU.Flat.get hσ₁ e
        have := hm₁ l
        rw [hm₀ l, PMap.empty_get, hχ] at this
        exact absurd this (by simp)
  subst hW
  have hf : fρ' = ρ' := eq_of_compS_empty_left h₂
  subst hf
  have hρ' : fρ' = PMap.empty := eq_empty_of_compS_left h₆
  subst hρ'
  exact hC

/-- `RelendJ` at the empty resource, from its body at every instantiation of the stack at the
empty resource (`relendJ_emp` read at the instantiations only). -/
theorem relendJ_emp_inst {δ : LSub} {σ : LStack} {P : LSub → List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} (hl : αs.length = σ.length)
    (hP : ∀ ι, InstAt αs ι → ∀ ls', P (ι.sub δ) (ι.life αs) ls' PMap.empty) :
    RelendJ δ σ P αs ls PMap.empty := by
  refine ⟨σ.map fun _ => false, PMap.empty, PMap.empty, ResU.comp_empty_right _,
    ⟨vwSW_false hl, placeViewsL_empty⟩, stratS_empty αs,
    fun ι hat ls' _ _ _ _ ρv τ hv hcv => ?_⟩
  rw [vwSW_false_inv hv.1] at hcv
  rw [eq_empty_of_compS_empty hcv]
  exact hP ι hat ls'

/-- **A thunk of a first-order computation type over nothing is the draft's at every index whose
reading models `Δ`**, from Core's computation relation at every reading modelling `Δ`: the `U`
clause asks the forced value at each instantiated reading, which models `Δ` (`instModels`), and G4
reads Core's fact there. -/
theorem thunk_W_of_core {Δ : LifeCtx} {C : CTy} (hC : FOComp C) {f : Val}
    (hcore : ∀ (s : LSub) (ls : List SRec), Δ.Models s → cC C ls s (forceE C (.val f)) PMap.empty)
    {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec} (hl : αs.length = σ.length)
    (hMod : Δ.Models (extS δ σ αs)) :
    vRLM (ℍ := ℍ) .binder0 none σ δ (.thunk C) αs ls f PMap.empty := by
  rw [vRLM_thunk0]
  intro _ _
  exact relendJ_emp_inst hl fun ι _ ls' =>
    coreSubWComp_go hC σ (ι.sub δ) (ι.life αs) ls' _ _
      (hcore _ ls' (instModels Δ δ σ αs ι hMod))

/-- **G5v. A closed value Core relates at every reading, at a first-order constant type, is the
draft's at every index**: the same route for a value Core proves by hand (`freeAll_vC`). -/
def CoreValToW : Prop :=
  ∀ (A : VTy) (v : Val), FOConstTy A →
    (∀ (δ : LSub) (ls : List SRec), vC true A ls δ v PMap.empty) →
    ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec), StackOK σ αs →
      vRLM (ℍ := ℍ) .binder0 none σ δ A αs ls v PMap.empty

/-- The empty lifetime context is modelled by every reading. -/
theorem models_empty (s : LSub) : LifeCtx.empty.Models s := models_empty_any s

/-- A box sequence keeps a stack's length in step with its lifetimes. -/
theorem boxSteps_length {δ : LSub} {ls : List SRec} {s s' : Stk}
    (h : Relation.ReflTransGen (BoxStep δ ls) s s') (hl : s.2.length = s.1.length) :
    s'.2.length = s'.1.length := by
  obtain ⟨τ, αt, hlt, h₁, h₂⟩ := boxSteps_append h
  rw [h₁, h₂, List.length_append, List.length_append, hlt, hl]

/-- **G5v** (`CoreValToW`). -/
theorem coreValToW : CoreValToW (ℍ := ℍ) := by
  intro A v hA hv σ δ αs ls hok
  have hth : ∀ {C : CTy}, FOComp C → (∀ δ ls, vC true (.thunk C) ls δ v PMap.empty) →
      ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec), αs.length = σ.length →
        vRLM (ℍ := ℍ) .binder0 none σ δ (.thunk C) αs ls v PMap.empty :=
    fun hC hv' σ δ αs ls hl => thunk_W_of_core (Δ := LifeCtx.empty) hC
      (fun s ls' _ => hv' s ls' ls' (Ext.refl ls' _)) hl (models_empty _)
  cases hA with
  | thunk hC => exact hth hC hv σ δ αs ls hok.1
  | bang hC =>
      refine ⟨rfl, hth hC (fun δ ls => (hv δ ls).2) σ δ αs ls hok.1, ?_⟩
      intro ι _ ls' _ σ' αs' hst
      exact hth hC (fun δ ls => (hv δ ls).2) σ' (ι.sub δ) αs' ls'
        (boxSteps_length hst (by simpa [Inst.life_length] using hok.1))

/-- A dead context holds nothing, at Core's relation, at every reading. -/
theorem gSepC_dead {ls : List SRec} {s : LSub} : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ (γ : List Val),
    gSepC ls s Γ γ PMap.empty
  | _, .nil, γ => by cases γ <;> exact ⟨rfl, trivial⟩
  | _, .cons _, [] => ⟨rfl, trivial⟩
  | _, .cons h, _ :: γ => gSepC_dead h γ

/-- **G5c. First-order constants at every index**: a syntactic value Core derives at a dead
context, at a first-order constant type, is the draft's there at every index. Stated at a context
with no live slot (`Ctx.Dead`): a live persistent slot would be read at each instantiated reading
through the thaw, which this statement does not need. -/
def CoreToSemSMConst : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (v : Val) (A : VTy), Ctx.Dead Γ → FOConstTy A →
    CDerives Δ Γ (.val v) (.val A) → SemSM (ℍ := ℍ) .binder0 Δ Γ (.val v) (.val A)

/-- **G5c** (`CoreToSemSMConst`): Core's judgement at each reading modelling `Δ`, at the empty list
and resource, gives the value's relation there (`post_of_wpTS_val_empty`); the `U` clause reads it
at each instantiated reading (`thunk_W_of_core`), and the box at each box world, whose reading
models `Δ` (`boxIdx_steps`). -/
theorem coreToSemSMConst : CoreToSemSMConst (ℍ := ℍ) := by
  intro Δ Γ v A hΓ hA h _ _ δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso _ _ hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  have hρ : ρ = PMap.empty := gSepRLM_deadP hΓ.toP hgs
  subst hρ
  have hv : IsVal (substAll γ v.1) := isVal_psub 0 γ v.2
  have hcore : ∀ s, Δ.Models s → vC true A [] s ⟨substAll γ v.1, hv⟩ PMap.empty := fun s hs =>
    post_of_wpTS_val_empty (w := ⟨substAll γ v.1, hv⟩)
      (semC_jdgCty h s γ [] PMap.empty hs (gDenC_mk hlw (gSepC_dead hΓ γ)))
  show wpTS ls (substAll γ v.1) _ PMap.empty
  refine wpTS_val ls ⟨substAll γ v.1, hv⟩ _ _ ?_
  have hth : ∀ {C : CTy}, FOComp C → (∀ s, Δ.Models s →
      vC true (.thunk C) [] s ⟨substAll γ v.1, hv⟩ PMap.empty) →
      ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec), αs.length = σ.length →
        Δ.Models (extS δ σ αs) →
        vRLM (ℍ := ℍ) .binder0 none σ δ (.thunk C) αs ls ⟨substAll γ v.1, hv⟩ PMap.empty :=
    fun hC hv' σ δ αs ls hl hm => thunk_W_of_core hC
      (fun s ls' hs => hv' s hs ls' (ext_empty' [] ls')) hl hm
  cases hA with
  | thunk hC => exact hth hC hcore σ δ αs ls hok.1 hMod
  | bang hC =>
      refine ⟨rfl, hth hC (fun s hs => (hcore s hs).2) σ δ αs ls hok.1 hMod, ?_⟩
      intro ι hat ls' hro' σ' αs' hst
      have hidx₀ := boxIdx_of_index hok hob hJ.1 hMod hro hso
      have hidx := boxIdx_steps (subDom_inst ι hSD) hst (boxIdx_inst hidx₀ hro')
      exact hth hC (fun s hs => (hcore s hs).2) σ' (ι.sub δ) αs' ls' hidx.ok.1 hidx.md

/-! ### G7: the empty-stack unfoldings -/

/-- At the empty stack the guard asks nothing. -/
def GuardPVNil : Prop :=
  ∀ (s : LSub) (ls : List SRec) (P : WProp) (ρ : WRes), guardPV s [] [] ls P ρ ↔ P ρ

theorem guardPV_nil_iff {s : LSub} {ls : List SRec} {P : WProp} {ρ : WRes} :
    guardPV s [] [] ls P ρ ↔ P ρ :=
  ⟨fun h => h ⟨fun a ha => by simp at ha, fun a ha => by simp at ha⟩ (pvlNil s ls ρ),
    fun h _ _ => h⟩

theorem guardPVNil : GuardPVNil := fun _ _ _ _ => guardPV_nil_iff

/-- At the empty stack the `U` clause is Core's with `KeepsT` added: the only instantiation of `[]`
is the identity (`instAt_nil_eq`), and no view is dropped. -/
def RelendJNil : Prop :=
  ∀ (δ : LSub) (P : LSub → List Life → List SRec → WProp) (ls : List SRec) (ρ : WRes),
    RelendJ δ [] P [] ls ρ ↔ ∀ ls', Ext ls ls' ρ → KeepsT ls ls' ρ → P δ [] ls' ρ

theorem relendJ_nil_iff {δ : LSub} {P : LSub → List Life → List SRec → WProp} {ls : List SRec}
    {ρ : WRes} : RelendJ δ [] P [] ls ρ ↔ ∀ ls', Ext ls ls' ρ → KeepsT ls ls' ρ → P δ [] ls' ρ := by
  constructor
  · rintro ⟨ds, ρz, ρn, hc, hn, -, H⟩ ls' hE hK
    cases ds with
    | nil =>
        have hn0 : ρn = PMap.empty := hn.1.1
        subst hn0
        have hz : ρ = ρz := ResU.CompS.functional hc (ResU.comp_empty_right ρz)
        subst hz
        exact H none (fun c θ h => by cases h) ls' hE hK
          (fun x _ hr => absurd hr not_rel_empty) (fun a ha => by simp [Inst.life] at ha) PMap.empty ρ
          ⟨⟨rfl, trivial⟩, placeViewsL_empty⟩ (ResU.comp_empty_right ρ)
    | cons d ds => exact hn.1.elim
  · intro h
    refine ⟨[], ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨⟨rfl, trivial⟩, placeViewsL_empty⟩,
      fun a ha => by simp at ha, fun ι hat ls' hE hK _ _ ρv τ hv hc => ?_⟩
    obtain rfl := instAt_nil_eq hat
    have hv0 : ρv = PMap.empty := hv.1.1
    subst hv0
    have hτ : τ = ρ := ResU.CompS.functional hc (ResU.comp_empty_right ρ)
    subst hτ
    exact h ls' hE hK

theorem relendJNil : RelendJNil := fun _ _ _ _ => relendJ_nil_iff

/-- At the empty stack a thunk is read at every extension keeping the tags. -/
def VRLMThunkNil : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (f : Val) (ρ : WRes),
    vRLM (ℍ := ℍ) .binder0 none [] δ (.thunk C) [] ls f ρ ↔
      ∀ ls', Ext ls ls' ρ → KeepsT ls ls' ρ →
        cRLM (ℍ := ℍ) .binder0 [] δ C [] ls' (forceE C (.val f)) ρ

theorem vRLM_thunk_nil_iff {δ : LSub} {C : CTy} {ls : List SRec} {f : Val} {ρ : WRes} :
    vRLM (ℍ := ℍ) .binder0 none [] δ (.thunk C) [] ls f ρ ↔
      ∀ ls', Ext ls ls' ρ → KeepsT ls ls' ρ →
        cRLM (ℍ := ℍ) .binder0 [] δ C [] ls' (forceE C (.val f)) ρ := by
  rw [vRLM_thunk0]
  exact guardPV_nil_iff.trans relendJ_nil_iff

theorem vRLMThunkNil : VRLMThunkNil (ℍ := ℍ) := fun _ _ _ _ _ => vRLM_thunk_nil_iff

/-- At the empty stack `⊸` is Core's clause at the draft's components. -/
def CRLMArrNil : Prop :=
  ∀ (δ : LSub) (A : VTy) (C : CTy) (ls : List SRec) (e : Expr) (ρ : WRes),
    cRLM (ℍ := ℍ) .binder0 [] δ (.arr A C) [] ls e ρ ↔
      ∀ v, (vRLM (ℍ := ℍ) .binder0 none [] δ A [] ls v ─⋆
        cRLM (ℍ := ℍ) .binder0 [] δ C [] ls (.app e (.val v))) ρ

theorem wand_guardPV_nil {s : LSub} {ls : List SRec} {P Q : WProp} {ρ : WRes} :
    (P ─⋆ guardPV s [] [] ls Q) ρ ↔ (P ─⋆ Q) ρ :=
  ⟨fun h ρ₁ ρ₂ hp hc => guardPV_nil_iff.mp (h ρ₁ ρ₂ hp hc),
    fun h ρ₁ ρ₂ hp hc => guardPV_nil_iff.mpr (h ρ₁ ρ₂ hp hc)⟩

theorem cRLMArrNil : CRLMArrNil (ℍ := ℍ) := by
  intro δ A C ls e ρ
  rw [cRLM_arr_binder0]
  exact forall_congr' fun v => wand_guardPV_nil

/-- **`binder0`'s `∀` clause, unfolded**: no future and no record extension; the instances in
scope, each under the guard at the stack, and the own pushes, each under the guard at the pushed
stack. -/
theorem cRLM_all_binder0 {σ : LStack} {δ : LSub} {x : LifeVar} {c : Lifetime.Life} {C : CTy}
    {αs : List Life} {ls : List SRec} {e : Expr} {ρ : WRes} :
    cRLM (ℍ := ℍ) .binder0 σ δ (.all x c C) αs ls e ρ ↔
      (∀ α, (⌜LtLife (extS δ σ αs) c α ∧ InScope (extS δ σ αs) α⌝ ─⋆
          guardPV (extS (δ.extend x α) σ αs) σ αs ls
            (cRLM (ℍ := ℍ) .binder0 σ (δ.extend x α) C αs ls (.app e (.val .unit)))) ρ) ∧
      ∀ (en : LEnt) (α : Life), OwnPushM δ (.all x c C) ρ (σ, αs) en α →
        RecsOutside (α :: αs) ls → SubFresh δ α →
        guardPV (extS (δ.extend x α) (en :: σ) (α :: αs)) (en :: σ) (α :: αs) ls
          (cRLM (ℍ := ℍ) .binder0 (en :: σ) (δ.extend x α) C (α :: αs) ls
            (.app e (.val .unit))) ρ := by
  constructor
  · intro h
    have h' := h ls σ αs (extQ_refl _ ls ρ) (by unfold FutQI; split <;> first | exact .refl | rfl)
      (futAvoids_self _ σ)
    exact ⟨h'.1, h'.2 rfl⟩
  · intro h ls' σ' αs' hE hF _
    have hE' : ls' = ls := by simpa [ExtQ, Placement.bindFut] using hE
    have hF' : (σ', αs') = (σ, αs) := by simpa [FutQI, Placement.bindFut] using hF
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hF'
    subst hE'
    exact ⟨h.1, fun _ => h.2⟩

/-- At the empty stack `∀` reads the instances in scope and the own pushes. -/
def CRLMAllNil : Prop :=
  ∀ (δ : LSub) (x : LifeVar) (c : Lifetime.Life) (C : CTy) (ls : List SRec) (e : Expr)
    (ρ : WRes),
    cRLM (ℍ := ℍ) .binder0 [] δ (.all x c C) [] ls e ρ ↔
      (∀ α, (⌜LtLife δ c α ∧ InScope δ α⌝ ─⋆
          cRLM (ℍ := ℍ) .binder0 [] (δ.extend x α) C [] ls (.app e (.val .unit))) ρ) ∧
      ∀ (en : LEnt) (α : Life), OwnPushM δ (.all x c C) ρ ([], []) en α →
        RecsOutside [α] ls → SubFresh δ α →
        guardPV (extS (δ.extend x α) [en] [α]) [en] [α] ls
          (cRLM (ℍ := ℍ) .binder0 [en] (δ.extend x α) C [α] ls (.app e (.val .unit))) ρ

theorem cRLMAllNil : CRLMAllNil (ℍ := ℍ) := by
  intro δ x c C ls e ρ
  rw [cRLM_all_binder0]
  exact and_congr (forall_congr' fun α => wand_guardPV_nil) Iff.rfl

/-- **At the top level a polymorphic value is checked by its own pushes alone**: no instance is in
scope at the empty reading (`inScope_top_none`). -/
def CRLMAllTop : Prop :=
  ∀ (x : LifeVar) (c : Lifetime.Life) (C : CTy) (ls : List SRec) (e : Expr) (ρ : WRes),
    cRLM (ℍ := ℍ) .binder0 [] (⟨[]⟩ : LSub) (.all x c C) [] ls e ρ ↔
      ∀ (en : LEnt) (α : Life), OwnPushM (⟨[]⟩ : LSub) (.all x c C) ρ ([], []) en α →
        RecsOutside [α] ls → SubFresh (⟨[]⟩ : LSub) α →
        guardPV (extS ((⟨[]⟩ : LSub).extend x α) [en] [α]) [en] [α] ls
          (cRLM (ℍ := ℍ) .binder0 [en] ((⟨[]⟩ : LSub).extend x α) C [α] ls
            (.app e (.val .unit))) ρ

theorem cRLMAllTop : CRLMAllTop (ℍ := ℍ) := by
  intro x c C ls e ρ
  rw [cRLMAllNil]
  exact ⟨fun h => h.2, fun h => ⟨fun α ρ₁ _ hp _ => absurd hp.2.2 (inScope_top_none α), h⟩⟩

/-- **C13: `effRetM` is Core's `effRet` given the answer's clause**, at a row `F_Σ A`. With G1 at a
flat `A`, it is unconditional there. -/
def EffRetMOfAns : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (S : Row) (A : VTy),
    (∀ ls v, vRLM (ℍ := ℍ) p none σ δ A αs ls v = vC true A ls (extS δ σ αs) v) →
    effRetM (ℍ := ℍ) p σ δ (CTy.effOf S A) αs = Core.effRet (CTy.effOf S A) (extS δ σ αs)

theorem effRetM_of_ans (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (A : VTy)
    (h : ∀ ls v, vRLM (ℍ := ℍ) p none σ δ A αs ls v = vC true A ls (extS δ σ αs) v) :
    ∀ (S : Row), effRetM (ℍ := ℍ) p σ δ (CTy.effOf S A) αs =
      Core.effRet (CTy.effOf S A) (extS δ σ αs)
  | [] => by
      funext ls v
      show vRLM p none σ δ A αs ls v = vC true A ls (extS δ σ αs) v
      exact h ls v
  | o :: S => by
      show effRetM p σ δ (CTy.effOf S A) αs = Core.effRet (CTy.effOf S A) (extS δ σ αs)
      exact effRetM_of_ans p σ δ αs A h S

theorem effRetMOfAns : EffRetMOfAns (ℍ := ℍ) :=
  fun p σ δ αs S A h => effRetM_of_ans p σ δ αs A h S

/-- **At the empty stack and a flat answer, the draft's computation relation at every row is
Core's** (`nilSoundRetM` one way; `bodyS_nil_iff` both). -/
def CRLMRetNil : Prop :=
  ∀ (δ : LSub) (S : Row) (A : VTy) (ls : List SRec) (e : Expr) (ρ : WRes), FlatTy A →
    (cRLM (ℍ := ℍ) .binder0 [] δ (CTy.effOf S A) [] ls e ρ ↔ cC (CTy.effOf S A) ls δ e ρ)

theorem cRLMRetNil : CRLMRetNil (ℍ := ℍ) := by
  intro δ S A ls e ρ hA
  have hG : ∀ ls v, vRLM (ℍ := ℍ) .binder0 none [] δ A [] ls v = vC true A ls δ v :=
    fun ls v => vRLMFlat .binder0 [] δ [] A hA ls v
  cases S with
  | nil =>
      show wpTS ls e (fun ls'' v => vRLM .binder0 none [] δ A [] ls'' v) ρ ↔
        wpTS ls e (fun ls'' => vCE none true A ls'' δ) ρ
      simp only [hG]
  | cons o S =>
      show GhostEnd.bodyS δ [] (GhostEnd.rowTab o.n o.i o.q o.A o.B (CTy.effOf S A) δ)
          (fun αs' ls v => effRetM .binder0 [] δ (CTy.effOf S A) αs' ls v)
          (GhostEnd.OpenS δ [] (GhostEnd.rowTab o.n o.i o.q o.A o.B (CTy.effOf S A) δ)
            (fun αs' ls v => effRetM .binder0 [] δ (CTy.effOf S A) αs' ls v)) [] ls e ρ ↔
        ewpTS ls e (opTable (GhostEnd.rowTab o.n o.i o.q o.A o.B (CTy.effOf S A) δ))
          (Core.effRet (CTy.effOf S A) δ) ρ
      exact GhostEnd.bodyS_nil_iff fun ls v ρ => by
        rw [effRetM_of_ans .binder0 [] δ [] A hG S]; exact Iff.rfl

/-- **C8: at a flat answer `F` is Core's clause**, at every stack (G1 under `wpTS`). -/
def CRLMRetFlat : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (B : VTy), FlatTy B → ∀ (ls : List SRec) (e : Expr),
    cRLM (ℍ := ℍ) .binder0 σ δ (.ret B) αs ls e = cC (.ret B) ls (extS δ σ αs) e

theorem cRLMRetFlat : CRLMRetFlat (ℍ := ℍ) := by
  intro σ δ αs B hB ls e
  show wpTS ls e (fun ls'' v => vRLM .binder0 none σ δ B αs ls'' v) =
    wpTS ls e (fun ls'' => vCE none true B ls'' (extS δ σ αs))
  simp only [vRLMFlat .binder0 σ δ αs B hB]

/-! ### G3, G4′, G5′: the empty stack -/

/-- Types at which the draft relation at the empty stack is Core's. -/
inductive NilTy : VTy → Prop
  | flat {A : VTy} : FlatTy A → NilTy A
  | mut (a : Lifetime.Life) (T : VTy) : NilTy (.mut a T)
  | imm (a : Lifetime.Life) (T : VTy) : NilTy (.imm a T)
  | tensor {A B : VTy} : NilTy A → NilTy B → NilTy (.tensor A B)
  | sum {A B : VTy} : NilTy A → NilTy B → NilTy (.sum A B)
  | box {a : Lifetime.Life} {A : VTy} : NilTy A → NilTy (.box a A)
  | ref {A : VTy} : NilTy A → NilTy (.ref A)
  | fam {L : VTy} : NilTy L → NilTy (.fam L)

mutual
/-- Value types at which Core's relation at the empty stack is inside the draft's. -/
inductive NilVal : VTy → Prop
  | ty {A : VTy} : NilTy A → NilVal A
  | thunk {C : CTy} : NilComp C → NilVal (.thunk C)
  | tensor {A B : VTy} : NilVal A → NilVal B → NilVal (.tensor A B)
/-- Computation types at which Core's relation at the empty stack is inside the draft's. -/
inductive NilComp : CTy → Prop
  | ret {B : VTy} : NilVal B → NilComp (.ret B)
  | arr {A : VTy} {C : CTy} : NilTy A → NilComp C → NilComp (.arr A C)
  | amp {C D : CTy} : NilComp C → NilComp D → NilComp (.amp C D)
  | top : NilComp .top
  | nu (C : CTy) : NilComp (.nu C)
end

/-- Every live slot is a `NilTy` type. -/
def CtxNil (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → NilTy s.ty

/-- **G3.** -/
def VRLMNilTy : Prop :=
  ∀ (p : Placement) (δ : LSub) (A : VTy), NilTy A → ∀ (ls : List SRec) (v : Val),
    vRLM (ℍ := ℍ) p none [] δ A [] ls v = vC true A ls δ v

/-- At the empty stack no place is lent, so `CohS` holds of every view. -/
theorem cohS_nil (s : LSub) (A : VTy) (v : Val) (ρ : WRes) : CohS [] [] s A v ρ :=
  fun _ _ _ _ h => by simp [innerAt] at h

/-- At the empty stack no lifetime is internal, so `RetainedPay` holds of every leaf. -/
theorem retainedPay_nil (s : LSub) (T : VTy) (v : Val) : RetainedPay [] [] s T v :=
  fun _ _ _ _ _ _ _ ⟨_, hc, _⟩ => by simp [cutOf] at hc

theorem vRLM_nilTy (p : Placement) (δ : LSub) : ∀ {A : VTy}, NilTy A →
    ∀ (ls : List SRec) (v : Val) (ρ : WRes),
      vRLM (ℍ := ℍ) p none [] δ A [] ls v ρ ↔ vC true A ls δ v ρ
  | _, .flat hA, ls, v, ρ => vRLM_flatE p hA none none [] δ [] ls v ρ (envCoreNone ls)
  | _, .mut _ _, _, _, _ =>
      ⟨fun h => h.1, fun h => ⟨h, cohS_nil _ _ _ _, retainedPay_nil _ _ _⟩⟩
  | _, .imm _ _, _, _, _ =>
      ⟨fun h => h.1, fun h => ⟨h, cohS_nil _ _ _ _, retainedPay_nil _ _ _⟩⟩
  | _, .tensor hA hB, ls, v, ρ => by
      constructor
      · rintro ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', (vRLM_nilTy p δ hA ls v₁ ρ₁).mp h₁,
          (vRLM_nilTy p δ hB ls v₂ ρ₂).mp h₂⟩
      · rintro ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩
        exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', (vRLM_nilTy p δ hA ls v₁ ρ₁).mpr h₁,
          (vRLM_nilTy p δ hB ls v₂ ρ₂).mpr h₂⟩
  | _, .sum hA hB, ls, v, ρ => by
      constructor
      · rintro (⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩)
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, (vRLM_nilTy p δ hA ls v₁ ρ₁).mp h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, (vRLM_nilTy p δ hB ls v₂ ρ₂).mp h₂⟩
      · rintro (⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩)
        · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, (vRLM_nilTy p δ hA ls v₁ ρ₁).mpr h₁⟩
        · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, (vRLM_nilTy p δ hB ls v₂ ρ₂).mpr h₂⟩
  | _, .box hA, ls, v, ρ => by
      constructor
      · rintro ⟨α, ha, hP, hout⟩
        exact ⟨α, ha, (vRLM_nilTy p δ hA ls v ρ).mp hP, hout⟩
      · rintro ⟨α, ha, hP, hout⟩
        exact ⟨α, ha, (vRLM_nilTy p δ hA ls v ρ).mpr hP, hout⟩
  | _, .ref hA, ls, _, _ => by
      constructor
      · rintro ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩
        exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, (vRLM_nilTy p δ hA ls v' ρ₂).mp h₂⟩
      · rintro ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩
        exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, (vRLM_nilTy p δ hA ls v' ρ₂).mpr h₂⟩
  | _, .fam hL, ls, _, _ => by
      constructor
      · rintro ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩
        exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m ρ' h =>
          (vRLM_nilTy p δ hL ls (.loc m) ρ').mp h) hs⟩
      · rintro ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩
        exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp, sepRange_mono' (fun m ρ' h =>
          (vRLM_nilTy p δ hL ls (.loc m) ρ').mpr h) hs⟩

/-- **G3** (`VRLMNilTy`). -/
theorem vRLMNilTy : VRLMNilTy (ℍ := ℍ) := by
  intro p δ A hA ls v
  funext ρ
  exact propext (vRLM_nilTy p δ hA ls v ρ)

/-- **G4′.** Core inside the draft at the empty stack, thunks included. -/
def CoreSubWNil : Prop :=
  (∀ (B : VTy), NilVal B → ∀ (δ : LSub) (ls : List SRec) (v : Val) (ρ : WRes),
      vC true B ls δ v ρ → vRLM (ℍ := ℍ) .binder0 none [] δ B [] ls v ρ) ∧
  ∀ (C : CTy), NilComp C → ∀ (δ : LSub) (ls : List SRec) (e : Expr) (ρ : WRes),
      cC C ls δ e ρ → cRLM (ℍ := ℍ) .binder0 [] δ C [] ls e ρ

mutual
theorem coreSubWNilV : ∀ {B : VTy}, NilVal B → ∀ (δ : LSub) (ls : List SRec) (v : Val)
    (ρ : WRes), vC true B ls δ v ρ → vRLM (ℍ := ℍ) .binder0 none [] δ B [] ls v ρ
  | _, .ty hA, δ, ls, v, ρ, h => (vRLM_nilTy .binder0 δ hA ls v ρ).mpr h
  | _, .thunk hC, δ, _, _, ρ, h =>
      vRLM_thunk_nil_iff.mpr fun ls' hE _ => coreSubWNilC hC δ ls' _ ρ (h ls' hE)
  | _, .tensor hA hB, δ, ls, _, _, ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ =>
      ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', coreSubWNilV hA δ ls v₁ ρ₁ h₁,
        coreSubWNilV hB δ ls v₂ ρ₂ h₂⟩
theorem coreSubWNilC : ∀ {C : CTy}, NilComp C → ∀ (δ : LSub) (ls : List SRec) (e : Expr)
    (ρ : WRes), cC C ls δ e ρ → cRLM (ℍ := ℍ) .binder0 [] δ C [] ls e ρ
  | _, .ret hB, δ, _, _, ρ, h => wpTS_mono (fun ls' v ρ' hv => coreSubWNilV hB δ ls' v ρ' hv) ρ h
  | _, .arr hA hC, δ, ls, _, _, h =>
      cRLM_arr_binder0.mpr fun v ρ₁ ρ₂ hv hc _ _ =>
        coreSubWNilC hC δ ls _ ρ₂ (h v ρ₁ ρ₂ ((vRLM_nilTy .binder0 δ hA ls v ρ₁).mp hv) hc)
  | _, .amp hC hD, δ, ls, _, ρ, h => ⟨coreSubWNilC hC δ ls _ ρ h.1, coreSubWNilC hD δ ls _ ρ h.2⟩
  | _, .top, _, _, _, _, _ => trivial
  | _, .nu _, _, _, _, _, h => h
end

/-- **G4′** (`CoreSubWNil`). -/
theorem coreSubWNil : CoreSubWNil (ℍ := ℍ) :=
  ⟨fun _ hB δ ls v ρ h => coreSubWNilV hB δ ls v ρ h,
    fun _ hC δ ls e ρ h => coreSubWNilC hC δ ls e ρ h⟩

/-! ### G6: the empty-stack judgement and the floor's statement -/

/-- **The draft's semantic judgement at the empty stack.** At `[]` the index hypotheses
`StackOK`, `OuterBelowTop`, `StackJM`, `RecsOutside`, `SubOutside`, `TabAtS` and `PlaceViewsL`
hold of every index, and `extS δ [] [] = δ`. -/
def SemSMNil (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (ls : List SRec) (γ : List Val) (ρ : WRes),
    SubDom δ Δ → Δ.Models δ → gRLM (ℍ := ℍ) p [] δ [] ls Γ γ ρ →
      cRLM (ℍ := ℍ) p [] δ (jdgCty j) [] ls (substAll γ e) ρ

def SemSMNilOfSemSM : Prop :=
  ∀ (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    SemSM (ℍ := ℍ) p Δ Γ e j → SemSMNil (ℍ := ℍ) p Δ Γ e j

theorem stackOK_nil : StackOK [] [] := ⟨rfl, List.isChain_nil, List.nodup_nil⟩

theorem stackJ_nil (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) : StackJ [] [] δ Δ Γ C :=
  ⟨List.nodup_nil, fun _ he => absurd he List.not_mem_nil,
    fun _ he => absurd he List.not_mem_nil⟩

theorem stackJM_nil (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) : StackJM [] [] δ Δ Γ C :=
  ⟨stackJ_nil δ Δ Γ C, fun _ he => absurd he List.not_mem_nil⟩

theorem subOutside_nil (δ : LSub) : SubOutside [] [] δ :=
  fun _ _ h => absurd h (by simp)

theorem tabAtS_nil (ρ : WRes) : TabAtS [] [] ρ :=
  ⟨fun a ha => by simp at ha, fun a ha => by simp at ha⟩

theorem semSMNilOfSemSM : SemSMNilOfSemSM (ℍ := ℍ) := by
  intro p Δ Γ e j h hBL hSc δ ls γ ρ hSD hMod hg
  exact h hBL hSc δ [] [] ls γ ρ stackOK_nil (fun _ ho => by simp at ho)
    (stackJM_nil δ Δ Γ _) hSD hMod (fun _ ha => by simp at ha) (subOutside_nil δ)
    (tabAtS_nil ρ) (pvlNil _ ls ρ) hg

/-- **The floor**: the draft's fundamental lemma for Core's rules. Stated, not claimed. -/
def DraftFL : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    CDerives Δ Γ e j → SemSM (ℍ := ℍ) .binder0 Δ Γ e j

/-- **The floor's own statement at the empty stack.** Stated, not claimed. -/
def DraftFLNil : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    CDerives Δ Γ e j → SemSMNil (ℍ := ℍ) .binder0 Δ Γ e j

/-- **G5′.** The floor at the empty stack at first-order judgements, constants included. -/
def CoreToSemSMNil : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CtxNil Γ → NilComp (jdgCty j) →
    CDerives Δ Γ e j → SemSMNil (ℍ := ℍ) .binder0 Δ Γ e j

/-- **G5′** (`CoreToSemSMNil`): the context's slots are Core's at `[]` (G3), `fundamentalC` gives
Core's judgement, and G4′ gives the draft's. -/
theorem coreToSemSMNil : CoreToSemSMNil (ℍ := ℍ) := by
  intro Δ Γ e j hΓ hC h _ _ δ ls γ ρ _ hMod hg
  refine coreSubWNilC hC δ ls _ ρ (semC_jdgCty h δ γ ls ρ hMod ?_)
  exact (gRLMOfSlots (ℍ := ℍ) .binder0 [] δ [] ls Γ).2
    (fun s hs hl v ρ' h' => (vRLM_nilTy .binder0 δ (hΓ s hs hl) ls v ρ').mp h') γ ρ hg

/-- **`SemSM`'s index at the empty stack** (W12) is Core's hypothesis on the reading, with
`BindersLow`, `Scoped` and `SubDom`. -/
def SemIdxMNil : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (ls : List SRec) (ρ : WRes),
    SemIdxM Δ Γ C δ [] [] ls ρ ↔ BindersLow Γ C ∧ Scoped Δ Γ C ∧ SubDom δ Δ ∧ Δ.Models δ

theorem semIdxMNil : SemIdxMNil := by
  intro Δ Γ C δ ls ρ
  constructor
  · rintro ⟨hBL, hSc, -, -, -, hSD, hMod, -⟩
    exact ⟨hBL, hSc, hSD, hMod⟩
  · rintro ⟨hBL, hSc, hSD, hMod⟩
    exact ⟨hBL, hSc, stackOK_nil, fun _ ho => by simp at ho, stackJ_nil δ Δ Γ C, hSD, hMod,
      fun _ ha => by simp at ha, subOutside_nil δ, tabAtS_nil ρ, pvlNil _ ls ρ⟩

/-- **The `!` clause at the empty stack**, the box unfolded to every box sequence from `([], [])`:
the only instantiation of `[]` is the identity. -/
def VRLMBangNil : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (v : Val) (ρ : WRes),
    vRLM (ℍ := ℍ) .binder0 none [] δ (.bang (.thunk C)) [] ls v ρ ↔
      ρ = PMap.empty ∧ vRLM (ℍ := ℍ) .binder0 none [] δ (.thunk C) [] ls v ρ ∧
      ∀ (ls' : List SRec) (σ' : LStack) (αs' : List Life),
        Relation.ReflTransGen (BoxStep δ ls') ([], []) (σ', αs') →
        vRLM (ℍ := ℍ) .binder0 none σ' δ (.thunk C) αs' ls' v PMap.empty

theorem vRLMBangNil : VRLMBangNil (ℍ := ℍ) := by
  intro δ C ls v ρ
  constructor
  · rintro ⟨h0, hv, hbox⟩
    exact ⟨h0, hv, fun ls' σ' αs' hst =>
      hbox none (fun c θ h => by cases h) ls' (fun _ ha => by simp [Inst.life] at ha) σ' αs' hst⟩
  · rintro ⟨h0, hv, hbox⟩
    refine ⟨h0, hv, fun ι hat ls' _ σ' αs' hst => ?_⟩
    obtain rfl := instAt_nil_eq hat
    exact hbox ls' σ' αs' hst

/-- **`KeepsT` keeps the records** (`Keeps` at the records): a record kept with its tag is kept. -/
def KeepsTKeeps : Prop :=
  ∀ (ls ls' : List SRec) (ρ : WRes), KeepsT ls ls' ρ → Keeps (rsOf ls) (rsOf ls') ρ

theorem keepsTKeeps : KeepsTKeeps := by
  intro ls ls' ρ h r hr hrel
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact List.mem_map.mpr ⟨x, h x hx hrel, rfl⟩

/-! ### G7′: the clause unfoldings at every stack -/

/-- **C7: the data leaves' clause is Core's**, at every stack: `vRLM`'s last clause at `1`, `0`,
`Unk`, an integer and an opaque type. -/
def VRLMLeafDefault : Prop :=
  ∀ (p : Placement) (η : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (αs : List Life)
    (ls : List SRec) (v : Val) (A : VTy),
    (A = .unit ∨ A = .zero ∨ A = .unk ∨ (∃ w, A = .int w) ∨ ∃ o, A = .opq o) →
    vRLM (ℍ := ℍ) p η σ δ A αs ls v = vC true A ls (extS δ σ αs) v

theorem vRLMLeafDefault : VRLMLeafDefault (ℍ := ℍ) := by
  intro p η σ δ αs ls v A hA
  rcases hA with rfl | rfl | rfl | ⟨w, rfl⟩ | ⟨o, rfl⟩ <;> rfl

/-- **C11: `⊤` and `ν` are Core's clauses**, at every stack. -/
def CRLMTopNuEq : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (e : Expr),
    cRLM (ℍ := ℍ) p σ δ .top αs ls e = cC .top ls (extS δ σ αs) e ∧
    ∀ C : CTy, cRLM (ℍ := ℍ) p σ δ (.nu C) αs ls e = cC (.nu C) ls (extS δ σ αs) e

theorem cRLMTopNuEq : CRLMTopNuEq (ℍ := ℍ) := fun _ _ _ _ _ _ => ⟨rfl, fun _ => rfl⟩

/-- **C11: `&` is Core's clause given its components.** -/
def CRLMAmpOfComp : Prop :=
  ∀ (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (C D : CTy),
    (∀ e, cRLM (ℍ := ℍ) p σ δ C αs ls e = cC C ls (extS δ σ αs) e) →
    (∀ e, cRLM (ℍ := ℍ) p σ δ D αs ls e = cC D ls (extS δ σ αs) e) →
    ∀ e, cRLM (ℍ := ℍ) p σ δ (.amp C D) αs ls e = cC (.amp C D) ls (extS δ σ αs) e

theorem cRLMAmpOfComp : CRLMAmpOfComp (ℍ := ℍ) := by
  intro p σ δ αs ls C D hC hD e
  funext ρ
  show (cRLM p σ δ C αs ls _ ρ ∧ cRLM p σ δ D αs ls _ ρ) =
    (cC C ls (extS δ σ αs) _ ρ ∧ cC D ls (extS δ σ αs) _ ρ)
  rw [hC, hD]

/-! ### G8–G11: arising, typing, adequacy -/

/-- **The revised arising set's worlds are tagged `TW` worlds.** -/
def ArisesITW : Prop :=
  ∀ c : Cfg, ArisesI (ℍ := ℍ) c → TW c.fρ c.ps (rsOf c.ls) ∧ Tagged c.fρ c.ps c.ls

theorem arisesITW : ArisesITW (ℍ := ℍ) := by
  intro c h
  refine ArisesI.rec
    (motive_1 := fun c _ => TW c.fρ c.ps (rsOf c.ls) ∧ Tagged c.fρ c.ps c.ls)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    ?nil ?run ?part ?lendMut ?lendImm ?hide (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) h
  case nil =>
    intro fρ ρf ρ ps ls htw htg _ _
    exact ⟨htw, htg⟩
  case run =>
    intro c c' Δ Γ e₀ j γ t _ _ _ hR _ _
    obtain ⟨-, -, A, k, k', μ, μ', ρp, fρ', π, -, -, -, -, -, -, -, -, -, -, htw, htg, -⟩ := hR
    exact ⟨htw, htg⟩
  case part =>
    intro c ρ₁ ρ₂ ρf' _ _ _ _ ih
    exact ih
  case lendMut =>
    intro c c' e _ hL ih
    obtain ⟨⟨-, -, hps, hls, -, -, -, α, v, ρp, X, ρc, Z, hstr, P, hw, -, -, -, h₁, -, h₂, h₃,
      hv, -, -, -, htg, -⟩, -⟩ := hL
    refine ⟨?_, htg⟩
    rw [hps, hls]
    exact TW.mutFold ih.1 h₁ h₂ h₃ hv
  case lendImm =>
    intro c c' e _ hL ih
    obtain ⟨⟨-, -, -, -, α, v, R, X, ρc, Z, δ, h, ds, -, -, -, -, hadm, h₁, -, h₂, hsh, h₃, hv,
      hds, hps, hrs, -, -, -, htg⟩, -⟩ := hL
    refine ⟨?_, htg⟩
    rw [hps, hrs]
    exact TW.immFrame e.T δ h ih.1 hadm h₁ h₂ hsh h₃ hv hds
  case hide =>
    intro c N _ ih
    exact ih

/-- **Every tagged `TW` world arises at the empty stack** (`ArisesI.nil`, named for the ledger). -/
def ArisesINilOfTW : Prop :=
  ∀ (fρ ρf ρ : WRes) (ps : List FrameRec) (ls : List SRec), TW fρ ps (rsOf ls) →
    Tagged fρ ps ls → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    ArisesI (ℍ := ℍ) ⟨fρ, ρf, ρ, ps, ls, [], []⟩

theorem arisesINilOfTW : ArisesINilOfTW (ℍ := ℍ) :=
  fun _ _ _ _ _ htw htg hh hc => ArisesI.nil htw htg hh hc

/-- **A `CDerivesNU` program is a `ProbeRules` program.** -/
def ProbeRulesOfNU : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg),
    Targets.CDerivesNU Δ Γ e j → ProbeRules Δ Γ e j

theorem probeRulesOfNU : ProbeRulesOfNU := fun _ _ _ _ h => probeRules_of_nu h

/-- **The draft's acceptance at the empty stack at `F 1` gives adequacy**: every run of the
program from the empty memory continues to `()` at the empty memory. -/
def AdequacyNilM : Prop :=
  ∀ (e : Expr), BindersLow [] (CTy.ret .unit) → Scoped LifeCtx.empty [] (CTy.ret .unit) →
    SemSMNil (ℍ := ℍ) .binder0 LifeCtx.empty [] e (.comp (.ret .unit)) →
    ∀ {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}, BoCa.BoLo.Steps Adequacy.emptyMem e μ₁ e₁ →
      BoCa.BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val .unit)

/-- **`AdequacyNilM`**: `adequacyD`'s proof with the draft's judgement at the empty stack in place
of `fundamentalC`; at `1` the draft's answer is Core's (G1). -/
theorem adequacyNilM : AdequacyNilM (ℍ := ℍ) := by
  intro e hBL hSc h μ₁ e₁ hs
  have hwp := h hBL hSc LSub.empty [] [] PMap.empty (fun y hy => absurd rfl hy)
    Adequacy.models_empty (pure_sep_mk (by simp [Ctx.LiveWithin]) ⟨rfl, trivial⟩)
  have hwp' : wpTS [] e (fun _ v => BoCa.Fig16.BoLo.pure (v = Val.unit)) (PMap.empty : WRes) := by
    have he : substAll [] e = e := Adequacy.psub_nil 0 e
    have h' : wpTS [] (substAll [] e)
        (fun ls'' v => vRLM (ℍ := ℍ) .binder0 none [] LSub.empty .unit [] ls'' v) PMap.empty := hwp
    rw [he] at h'
    exact h'
  obtain ⟨v, hsteps, rfl⟩ := theorem32D e (· = Val.unit) hwp' hs
  exact hsteps

/-- **The pointwise reading of the table fails at `innerView`**: a `TW` world (`tw_innerView`)
whose part fails the table at `[x]` (`not_tabAtS_innerView`), at a configuration not in `Arises`
(`wpG_below_not_arises`). A fact about the pointwise statement (DESIGN §5.2, §11). -/
def NotTabOfTWPointwise : Prop := ¬ TabOfTWPointwise

theorem notTabOfTWPointwise : NotTabOfTWPointwise := by
  intro h
  let e : LEnt := ⟨1, 0, .unit, .mut, fun _ => true⟩
  have hk : (0 : BoCa.Loc) ≠ e.l := by decide
  have hlt : lifeN 2 ⊏ lifeN 1 := by decide
  refine GhostEnd.not_tabAtS_innerView (e := e) hk hlt ?_
  refine h (GhostEnd.innerView 0 (lifeN 2)) PMap.empty (GhostEnd.innerView 0 (lifeN 2)) [] []
    [e] [lifeN 1] (GhostEnd.tw_innerView 0 (lifeN 2)) (fun x hx => absurd hx List.not_mem_nil)
    ⟨rfl, List.isChain_singleton _, List.nodup_singleton _⟩
    (fun e' he' u hu => by
      obtain rfl := List.mem_singleton.mp he'
      cases hu)
    (ResU.hash_symm (ResU.hash_empty_right (GhostEnd.valid_innerView 0 (lifeN 2))))
    (compS_empty_left _) ?_
  intro m ψ hm _
  refine Or.inr ?_
  have : m = 0 := by
    by_contra hne
    simp [GhostEnd.innerView, ResU.single_get_ne _ hne] at hm
  subst this
  simp [e]

/-- **The revised arising set is inside the first**: `ArisesI`'s transitions are `Arises`'s with
stronger lends (`LendMutI`, `LendImmI`), and its values are `ArisesV`'s. -/
def ArisesIArises : Prop :=
  (∀ c : Cfg, ArisesI (ℍ := ℍ) c → Arises (ℍ := ℍ) c) ∧
  ∀ (c : Cfg) (v : Val) (A : VTy), ArisesVI (ℍ := ℍ) c v A → ArisesV (ℍ := ℍ) c v A

theorem arisesIArises : ArisesIArises (ℍ := ℍ) := by
  have key : ∀ c, ArisesI (ℍ := ℍ) c → Arises (ℍ := ℍ) c := by
    intro c h
    refine ArisesI.rec (motive_1 := fun c _ => Arises (ℍ := ℍ) c)
      (motive_2 := fun c v A _ => ArisesV (ℍ := ℍ) c v A)
      (motive_3 := fun c Γ γ _ => ArisesCtx (ℍ := ℍ) c Γ γ)
      ?nil ?run ?part ?lendMut ?lendImm ?hide ?ret ?view ?cnil ?cdead ?clive h
    case nil => intro fρ ρf ρ ps ls htw htg hh hc; exact Arises.nil htw htg hh hc
    case run => intro c c' Δ Γ e₀ j γ t _ hD _ hR ih ihC; exact Arises.run ih hD ihC hR
    case part => intro c ρ₁ ρ₂ ρf' _ h₁ h₂ h₃ ih; exact Arises.part ih h₁ h₂ h₃
    case lendMut => intro c c' e _ hL ih; exact Arises.lendMut ih hL.1
    case lendImm => intro c c' e _ hL ih; exact Arises.lendImm ih hL.1
    case hide => intro c N _ ih; exact Arises.hide N ih
    case ret => intro c c' Δ Γ e₀ j S A γ v _ hD hj _ hR ih ihC; exact ArisesV.ret ih hD hj ihC hR
    case view =>
      intro c c' e ψ ρc ρf' _ hL h₁ h₂ ih
      exact ArisesV.view ih (hL.imp (fun h => h.1) (fun h => h.1)) h₁ h₂
    case cnil => intro c h; exact ArisesCtx.nil h
    case cdead => intro c s Γ w γ hs _ ih; exact ArisesCtx.dead hs ih
    case clive =>
      intro c s Γ w γ ρ₁ ρ₂ ρf₁ ρf₂ hs h₁ h₂ h₃ _ _ ihV ihC
      exact ArisesCtx.live hs h₁ h₂ h₃ ihV ihC
  refine ⟨key, fun c v A h => ?_⟩
  refine ArisesVI.rec (motive_1 := fun c _ => Arises (ℍ := ℍ) c)
    (motive_2 := fun c v A _ => ArisesV (ℍ := ℍ) c v A)
    (motive_3 := fun c Γ γ _ => ArisesCtx (ℍ := ℍ) c Γ γ)
    ?nil ?run ?part ?lendMut ?lendImm ?hide ?ret ?view ?cnil ?cdead ?clive h
  case nil => intro fρ ρf ρ ps ls htw htg hh hc; exact Arises.nil htw htg hh hc
  case run => intro c c' Δ Γ e₀ j γ t _ hD _ hR ih ihC; exact Arises.run ih hD ihC hR
  case part => intro c ρ₁ ρ₂ ρf' _ h₁ h₂ h₃ ih; exact Arises.part ih h₁ h₂ h₃
  case lendMut => intro c c' e _ hL ih; exact Arises.lendMut ih hL.1
  case lendImm => intro c c' e _ hL ih; exact Arises.lendImm ih hL.1
  case hide => intro c N _ ih; exact Arises.hide N ih
  case ret => intro c c' Δ Γ e₀ j S A γ v _ hD hj _ hR ih ihC; exact ArisesV.ret ih hD hj ihC hR
  case view =>
    intro c c' e ψ ρc ρf' _ hL h₁ h₂ ih
    exact ArisesV.view ih (hL.imp (fun h => h.1) (fun h => h.1)) h₁ h₂
  case cnil => intro c h; exact ArisesCtx.nil h
  case cdead => intro c s Γ w γ hs _ ih; exact ArisesCtx.dead hs ih
  case clive =>
    intro c s Γ w γ ρ₁ ρ₂ ρf₁ ρf₂ hs h₁ h₂ h₃ _ _ ihV ihC
    exact ArisesCtx.live hs h₁ h₂ h₃ ihV ihC

/-- **G12. The floor at BoLo's image**: a BoLo derivation, embedded (`embed`,
`Core/Embedding.lean`), is the draft's at every index. Stated, not attempted. -/
def DraftFLEmbed : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), DerivesWf Δ Γ e T → Δ.Ok →
    Ctx.ScopedB Δ Γ → SemSM (ℍ := ℍ) .binder0 Δ (cbvCtx Γ) e (.val (cbv T))

/-! ### The rows against `fundamentalC` (§2.6)

Each is its `CDerives` constructor's statement at `SemSM .binder0`. None is proved here; the
suite (`GroundRegress.lean`) names them as the missing lemmas of its entries. A row's route may
need, as named hypotheses, `BindersLow` and `Scoped` facts of its premises' types that its
conclusion's do not give [unchecked: which rows need them]. -/

/-- `[var]` at `SemSM`. -/
def VarRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (i : Nat) (A : VTy),
    Ctx.SoloP Γ i A → SemSM (ℍ := ℍ) .binder0 Δ Γ (.var i) (.val A)

/-- `[1I]` at `SemSM`. -/
def UnitIRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy), Ctx.DeadP Γ → SemSM (ℍ := ℍ) .binder0 Δ Γ (.val .unit) (.val .unit)

/-- `[⊗I]` at `SemSM`. -/
def TensorIRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (e₁ e₂ : Expr) (A B : VTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ e₁ (.val A) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ₂ e₂ (.val B) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.pair e₁ e₂) (.val (.tensor A B))

/-- `[⊕I₁]` at `SemSM`. -/
def SumI₁RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A B : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A) → SemSM (ℍ := ℍ) .binder0 Δ Γ (.inj₁ e) (.val (.sum A B))

/-- `[⊕I₂]` at `SemSM`. -/
def SumI₂RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A B : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val B) → SemSM (ℍ := ℍ) .binder0 Δ Γ (.inj₂ e) (.val (.sum A B))

/-- `[lam]` at `SemSM`. -/
def LamRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy) (C : CTy),
    SemSM (ℍ := ℍ) .binder0 Δ (⟨A, true⟩ :: Γ) M (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam M)) (.comp (.arr A C))

/-- `[app]` at `SemSM`. -/
def AppRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M : Expr) (i : Nat) (A : VTy) (C : CTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ M (.comp (.arr A C)) →
    Ctx.SoloP Γ₂ i A → SemSM (ℍ := ℍ) .binder0 Δ Γ (.app M (.var i)) (.comp C)

/-- `[bind]` at `SemSM`. -/
def BindRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M N : Expr) (A : VTy) (C : CTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ M (.comp (.ret A)) →
    SemSM (ℍ := ℍ) .binder0 Δ (⟨A, true⟩ :: Γ₂) N (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app (.val (.lam N)) M) (.comp C)

/-- `[&I]` at `SemSM`. -/
def WithIRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M N : Expr) (C D : CTy),
    SemSM (ℍ := ℍ) .binder0 Δ (withCtx Γ) M (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ (withCtx Γ) N (.comp D) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (withPair M N) (.comp (.amp C D))

/-- `[&E₁]` at `SemSM`. -/
def Proj₁RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (C D : CTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ M (.comp (.amp C D)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app M (.val (.inj₁ .unit))) (.comp C)

/-- `[&E₂]` at `SemSM`. -/
def Proj₂RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (C D : CTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ M (.comp (.amp C D)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app M (.val (.inj₂ .unit))) (.comp D)

/-- `[1E]` at `SemSM`. -/
def UnitERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (V M : Expr) (C : CTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ V (.val .unit) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ₂ M (.comp C) → SemSM (ℍ := ℍ) .binder0 Δ Γ (.seq V M) (.comp C)

/-- `[⊗E]` (`letpair`) at `SemSM`. -/
def LetPairRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γp Γb : Ctx VTy) (V M : Expr) (A B : VTy) (C : CTy),
    Ctx.SplitP Γ Γp Γb → SemSM (ℍ := ℍ) .binder0 Δ Γp V (.val (.tensor A B)) →
    SemSM (ℍ := ℍ) .binder0 Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.letpair V M) (.comp C)

/-- `[⊕E]` at `SemSM`. -/
def SumERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γs Γb : Ctx VTy) (V M₁ M₂ : Expr) (A B : VTy) (C : CTy),
    Ctx.SplitP Γ Γs Γb → SemSM (ℍ := ℍ) .binder0 Δ Γs V (.val (.sum A B)) →
    SemSM (ℍ := ℍ) .binder0 Δ (⟨A, true⟩ :: Γb) M₁ (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ (⟨B, true⟩ :: Γb) M₂ (.comp C) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.case V M₁ M₂) (.comp C)

/-- `[∀E]` at `SemSM`. -/
def AllERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (x : LifeVar) (b a : Lifetime.Life) (C : CTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ M (.comp (.all x b C)) → Δ.EntailsLt a b →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app M (.val .unit)) (.comp (C.instLife x a))

/-- `[∀E]` call-by-value (`allEV`) at `SemSM`. -/
def AllEVRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (x : LifeVar) (b a : Lifetime.Life) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (VTy.all x b A)) → Δ.EntailsLt a b →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app e (.val .unit)) (.val (A.instLife x a))

/-- `[!E]` (dereliction) at `SemSM`. -/
def BangERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.bang A)) → SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A)

/-- `[⊸E]` call-by-value (`lolliE`) at `SemSM`. -/
def LolliERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (f a : Expr) (A B : VTy),
    Ctx.SplitP Γ Γ₁ Γ₂ → SemSM (ℍ := ℍ) .binder0 Δ Γ₁ a (.val A) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ₂ f (.val (.lolli A B)) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.app f a) (.val B)

/-- `[]I` at `SemSM`. -/
def BoxIRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (a : Lifetime.Life) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A) → CtxOutlives Δ Γ a →
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.box a A))

/-- `[]E` at `SemSM`. -/
def BoxERowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (a : Lifetime.Life) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.box a A)) → SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val A)

/-- `⊑imm` at `SemSM`. -/
def ImmSubRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (a b : Lifetime.Life) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.imm b A)) → Δ.EntailsLe a b →
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.imm a A))

/-- `⊑mut` at `SemSM`. -/
def MutSubRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (a b : Lifetime.Life) (A : VTy),
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.mut b A)) → Δ.EntailsLe a b →
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.val (.mut a A))

/-- `alloc` at every payload at `SemSM` (G5c covers first-order payloads). -/
def AllocRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.prim .alloc)) (.val (.lolli A (.ref A)))

/-- `free` at every payload at `SemSM` (G5c covers first-order payloads). -/
def FreeRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.prim .free)) (.val (.lolli (.ref A) A))

/-- `swap` at `SemSM`. `swap` is curried: its first answer is a thunk, so it is no first-order
constant type and G5c does not cover it. -/
def SwapRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ swap (.val (axSwapTy A B))

/-- `copy` at `Imm` at `SemSM`: its answer holds `Imm` leaves, which owe `CohS` and `RetainedPay`
at the index. -/
def CopyRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ copy (.val (axCopyTy a A))

/-- `withbor` (1) at `SemSM`, at every index (`withbor1_compatX`'s statement). -/
def Withbor1RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → Δ.find? x = none →
    VScoped Δ A → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withbor (.val (axWithbor1Ty x Δ.meetOfDom A B))

/-- `withbor` (2) at `SemSM`. -/
def Withbor2RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → Δ.find? x = none →
    (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withbor (.val (axWithbor2Ty x Δ.meetOfDom A B))

/-- `withbor` (3), the reborrow of a `Mut`, at `SemSM`. -/
def Withbor3RowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ →
    Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withbor (.val (axWithbor3Ty a x Δ.meetOfDom A B))

/-- `withload` at `SemSM`, at every index (`withload_compatX`'s statement). -/
def WithloadRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withload (.val (axWithloadTy a x Δ.meetOfDom A B))

/-- `withload` at its unwinding type at the empty row, at `SemSM`. -/
def WithloadURowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B []))

/-- `withswap` at `SemSM`. -/
def WithswapRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withswap (.val (axWithswapTy a A B))

/-- `foldImm` at `SemSM`. -/
def FoldImmRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (F : FShape) (y : LifeVar) (c : Lifetime.Life) (R : VTy),
    Ctx.DeadP Γ → F.WF → F.Guarded → ¬ VFree y (.mu F.ty) → ¬ VFree y R →
    (∀ Δ' a, VOutlives Δ' a R) →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (foldImmV F)) (.val (.lolli (algTy F y R) (foldTy F y c R)))

/-- `foldOwn` at `SemSM`. -/
def FoldOwnRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (F : FShape) (R : VTy), Ctx.DeadP Γ → F.WF → F.Guarded →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (foldOwnV F)) (.val (.lolli (algOTy F R) (foldOTy F R)))

/-- `foldReuse` at `SemSM`. -/
def FoldReuseRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (F : FShape) (R : VTy), Ctx.DeadP Γ → F.WF → F.Guarded →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (foldReuseV F)) (.val (.lolli (algRTy F R) (foldOTy F R)))

/-- `unfold` (coiteration) at `SemSM`. -/
def UnfoldNRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (S : VTy), C.NuOk → Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S))

/-- `[νI]` at `SemSM`. -/
def NuInRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy), C.NuOk →
    SemSM (ℍ := ℍ) .binder0 Δ Γ e (.comp C.unroll) → SemSM (ℍ := ℍ) .binder0 Δ Γ e (.comp (.nu C))

/-- `array_new` at `SemSM`. -/
def ArrNewRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.prim .tab)) (.val (arrNewTy A))

/-- `array_free` at `SemSM`. -/
def ArrFreeRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.prim .drop)) (.val (arrFreeTy A))

/-- `array_get` at `SemSM`: its answer holds an `Imm` leaf. -/
def ArrGetRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.prim .idx)) (.val (arrGetTy a A))

/-- `count_fold` at `SemSM`. -/
def CountFoldRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (S : VTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.prim .count)) (.val (countFoldTy S))

/-- `bounded_fix` at `SemSM`. -/
def BoundedFixRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A : VTy) (C : CTy), Ctx.DeadP Γ →
    SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.prim .boundedFix)) (.val (boundedFixTy A C))

/-- `slice_borrow_imm` at `SemSM`. -/
def SliceBorrowIRowM : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → VScoped Δ A →
    (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) → (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) →
    ¬ VFree x A → ¬ VFree x B →
    SemSM (ℍ := ℍ) .binder0 Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B))

end ProbeD1

end
