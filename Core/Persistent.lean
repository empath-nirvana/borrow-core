import Paper.S4_LogicalRelation.Definitions
import Support.Model.Notation
import Support.Model.Propositions
import Support.Model.UpdateFrame
import Support.Statics.Contexts
import Core.Relation

/-!
# Core — persistent slots  `[spec §10]`

A value type is persistent when the relation holds its values only at the empty resource
(`vP_empty_of_persistent`).  A live slot of persistent type may be duplicated by a context
split (`Ctx.SplitP.dup`) and dropped by a leaf that asks for a consumed context
(`Ctx.DeadP.drop`, `Ctx.SoloP.skip`): its resource is `∅`, and `∅ = ∅ ⋆ ∅`.

`Ctx.SplitP`, `Ctx.DeadP` and `Ctx.SoloP` extend `Ctx.Split`, `Ctx.Dead` and `Ctx.Solo` by those
constructors (`Ctx.Split.toP`, `Ctx.Dead.toP`, `Ctx.Solo.toP`).  The context relation respects
each of them: `gSepC_splitP`, `gSepC_deadP`, `gSepC_soloP`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A value type whose values hold no resource: `1`, `0`, `Unk`, `I32`, `I64`, `!A`, and `⊗`,
`⊕`, `[@a]` and `μ` over persistent types, with a type variable persistent (it stands, under its
`μ`, for a persistent type).  `U C`, `Ref A`, `Imm @a A` and `Mut @a A` are not.
`[spec §10, §8]` -/
def VTy.persistent : VTy → Bool
  | .unit => true
  | .zero => true
  | .unk => true
  | .int _ => true
  | .bang _ => true
  | .tvar _ => true
  | .tensor A B => A.persistent && B.persistent
  | .sum A B => A.persistent && B.persistent
  | .box _ A => A.persistent
  | .mu A => A.persistent
  | .thunk _ => false
  | .ref _ => false
  | .imm _ _ => false
  | .mut _ _ => false

/-- `A` is persistent.  `[spec §10]` -/
abbrev VTy.Persistent (A : VTy) : Prop := A.persistent = true

/-- Two empty resources compose only to the empty resource. -/
theorem eq_empty_of_compS_empty {ρ : WRes} (h : ResU.CompS PMap.empty PMap.empty ρ) :
    ρ = PMap.empty :=
  eq_of_compS_empty_left h

/-- At a persistent type, under an environment whose candidates hold only at `∅`, the relation
holds only at `∅`, in both modes.  At `μX. A` the least fixed point is below the candidate
"the resource is `∅`", which is closed under `A`'s clause.  `[spec §10]` -/
theorem vCE_empty_of_persistent : ∀ (A : VTy) {η : Option (Nat → TEnt)},
    (∀ n b ls v ρ, (tEnv η n).P b ls v ρ → ρ = PMap.empty) → A.Persistent →
    ∀ {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
      vCE η b A ls δ v ρ → ρ = PMap.empty
  | .unit, _, _, _, _, _, _, _, _, h => h.1
  | .zero, _, _, _, _, _, _, _, _, h => h.elim
  | .unk, _, _, _, _, _, _, _, _, h => h.1
  | .int _, _, _, _, _, _, _, _, _, h => h.1
  | .bang _, _, _, _, _, _, _, _, _, h => h.1
  | .tvar n, η, hη, _, b, ls, _, v, ρ, h => by
      cases η with
      | none => exact h.elim
      | some η => exact hη n b ls v ρ h
  | .tensor A B, η, hη, hp, b, ls, δ, v, ρ, h => by
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hq, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      rw [hq.1] at hc
      rw [vCE_empty_of_persistent A hη hp.1 h₁, vCE_empty_of_persistent B hη hp.2 h₂] at hc'
      rw [eq_empty_of_compS_empty hc'] at hc
      exact eq_empty_of_compS_empty hc
  | .sum A B, η, hη, hp, b, ls, δ, v, ρ, h => by
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hq, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hq, h₂⟩
      · rw [hq.1, vCE_empty_of_persistent A hη hp.1 h₁] at hc
        exact eq_empty_of_compS_empty hc
      · rw [hq.1, vCE_empty_of_persistent B hη hp.2 h₂] at hc
        exact eq_empty_of_compS_empty hc
  | .box _ A, η, hη, hp, b, ls, δ, v, ρ, h => by
      obtain ⟨α, -, hb, -⟩ := h
      exact vCE_empty_of_persistent A hη hp hb
  | .mu A, η, hη, hp, b, ls, δ, v, ρ, h => by
      refine h.2.2 (fun _ _ _ ρ => ρ = PMap.empty) ?_
      intro b' ls' v' ρ' h'
      refine vCE_empty_of_persistent A ?_ hp h'
      intro n b'' ls'' v'' ρ'' hn
      cases n with
      | zero => exact hn
      | succ n => exact hη n b'' ls'' v'' ρ'' hn

/-- At a persistent type the program's relation holds only at `∅`.  `[spec §10]` -/
theorem vP_empty_of_persistent {A : VTy} (hA : A.Persistent) {ls : List SRec} {δ : LSub}
    {v : Val} {ρ : WRes} (h : vP A ls δ v ρ) : ρ = PMap.empty :=
  vCE_empty_of_persistent A (η := none) (fun _ _ _ _ _ h => h.elim) hA h

/-! ### The context relations -/

/-- `Γ = Γ₁, Γ₂` with a live slot of persistent type allowed on both sides.  `[spec §10]` -/
inductive Ctx.SplitP : Ctx VTy → Ctx VTy → Ctx VTy → Prop where
  | nil : Ctx.SplitP [] [] []
  | left {Γ Γ₁ Γ₂ : Ctx VTy} {T : VTy} : Ctx.SplitP Γ Γ₁ Γ₂ →
      Ctx.SplitP (⟨T, true⟩ :: Γ) (⟨T, true⟩ :: Γ₁) (⟨T, false⟩ :: Γ₂)
  | right {Γ Γ₁ Γ₂ : Ctx VTy} {T : VTy} : Ctx.SplitP Γ Γ₁ Γ₂ →
      Ctx.SplitP (⟨T, true⟩ :: Γ) (⟨T, false⟩ :: Γ₁) (⟨T, true⟩ :: Γ₂)
  | dead {Γ Γ₁ Γ₂ : Ctx VTy} {T : VTy} : Ctx.SplitP Γ Γ₁ Γ₂ →
      Ctx.SplitP (⟨T, false⟩ :: Γ) (⟨T, false⟩ :: Γ₁) (⟨T, false⟩ :: Γ₂)
  /-- A persistent slot goes to both sides. -/
  | dup {Γ Γ₁ Γ₂ : Ctx VTy} {T : VTy} (hT : T.Persistent) : Ctx.SplitP Γ Γ₁ Γ₂ →
      Ctx.SplitP (⟨T, true⟩ :: Γ) (⟨T, true⟩ :: Γ₁) (⟨T, true⟩ :: Γ₂)

/-- A consumed context, up to live slots of persistent type.  `[spec §10]` -/
inductive Ctx.DeadP : Ctx VTy → Prop where
  | nil : Ctx.DeadP []
  | cons {T : VTy} {Γ : Ctx VTy} : Ctx.DeadP Γ → Ctx.DeadP (⟨T, false⟩ :: Γ)
  /-- A persistent slot is dropped. -/
  | drop {T : VTy} {Γ : Ctx VTy} (hT : T.Persistent) : Ctx.DeadP Γ → Ctx.DeadP (⟨T, true⟩ :: Γ)

/-- `Γ = x : T`, up to live slots of persistent type elsewhere.  `[spec §10]` -/
inductive Ctx.SoloP : Ctx VTy → Nat → VTy → Prop where
  | here {T : VTy} {Γ : Ctx VTy} : Ctx.DeadP Γ → Ctx.SoloP (⟨T, true⟩ :: Γ) 0 T
  | there {S T : VTy} {Γ : Ctx VTy} {i : Nat} : Ctx.SoloP Γ i T →
      Ctx.SoloP (⟨S, false⟩ :: Γ) (i + 1) T
  /-- A persistent slot before the variable is dropped. -/
  | skip {S T : VTy} {Γ : Ctx VTy} {i : Nat} (hS : S.Persistent) : Ctx.SoloP Γ i T →
      Ctx.SoloP (⟨S, true⟩ :: Γ) (i + 1) T

theorem _root_.BoCa.Ctx.Split.toP : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.Split Γ Γ₁ Γ₂ → Ctx.SplitP Γ Γ₁ Γ₂
  | _, _, _, .nil => .nil
  | _, _, _, .left h => .left h.toP
  | _, _, _, .right h => .right h.toP
  | _, _, _, .dead h => .dead h.toP

theorem _root_.BoCa.Ctx.Dead.toP : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → Ctx.DeadP Γ
  | _, .nil => .nil
  | _, .cons h => .cons h.toP

theorem _root_.BoCa.Ctx.Solo.toP : ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.Solo Γ i T → Ctx.SoloP Γ i T
  | _, _, _, .here h => .here h.toP
  | _, _, _, .there h => .there h.toP

/-- A derivation written with `Ctx.Split`, `Ctx.Dead` or `Ctx.Solo` is read at the extended
relation. -/
instance {Γ Γ₁ Γ₂ : Ctx VTy} : Coe (Ctx.Split Γ Γ₁ Γ₂) (Ctx.SplitP Γ Γ₁ Γ₂) := ⟨Ctx.Split.toP⟩
instance {Γ : Ctx VTy} : Coe (Ctx.Dead Γ) (Ctx.DeadP Γ) := ⟨Ctx.Dead.toP⟩
instance {Γ : Ctx VTy} {i : Nat} {T : VTy} : Coe (Ctx.Solo Γ i T) (Ctx.SoloP Γ i T) :=
  ⟨Ctx.Solo.toP⟩

/-- A split only turns liveness bits off. -/
theorem Ctx.SplitP.liveWithin {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) {γ : List Val}
    (hg : Ctx.LiveWithin Γ γ) : Ctx.LiveWithin Γ₁ γ ∧ Ctx.LiveWithin Γ₂ γ := by
  induction h generalizing γ with
  | nil => simp
  | left _ ih | right _ ih | dup _ _ ih => cases γ with
    | nil => exact absurd hg.1 (by simp)
    | cons v γ' => exact ⟨(ih hg).1, (ih hg).2⟩
  | dead _ ih => cases γ with
    | nil => exact ⟨⟨by simp, (ih hg.2).1⟩, ⟨by simp, (ih hg.2).2⟩⟩
    | cons v γ' => exact ⟨(ih hg).1, (ih hg).2⟩

theorem Ctx.SoloP.lt_of_liveWithin {Γ : Ctx VTy} {i : Nat} {T : VTy} (h : Ctx.SoloP Γ i T) :
    ∀ {γ : List Val}, Ctx.LiveWithin Γ γ → i < γ.length := by
  induction h with
  | here _ => intro γ hg; cases γ with
    | nil => exact absurd hg.1 (by simp)
    | cons v γ' => simp
  | there _ ih => intro γ hg; cases γ with
    | nil => exact absurd (ih hg.2) (by simp)
    | cons v γ' => simpa using ih hg
  | skip _ _ ih => intro γ hg; cases γ with
    | nil => exact absurd hg.1 (by simp)
    | cons v γ' => simpa using ih hg

/-! ### The context relation at the extended splits -/

/-- A persistent live slot holds only at `∅`. -/
theorem gSepC_cons_persistent {ls : List SRec} {δ : LSub} {T : VTy} (hT : T.Persistent)
    {Γ : Ctx VTy} {v : Val} {γ : List Val} {ρ : WRes}
    (h : gSepC ls δ (⟨T, true⟩ :: Γ) (v :: γ) ρ) :
    vP T ls δ v PMap.empty ∧ gSepC ls δ Γ γ ρ := by
  obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
  obtain rfl := vP_empty_of_persistent hT hv
  rw [eq_of_compS_empty_left hc]
  exact ⟨hv, hrest⟩

/-- A consumed context, up to persistent slots, contributes nothing.  `[spec §10]` -/
theorem gSepC_deadP {ls : List SRec} {δ : LSub} : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ →
    ∀ {γ : List Val} {ρ : WRes}, gSepC ls δ Γ γ ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; exact h.1
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (γ := γ') h
  | drop hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (gSepC_cons_persistent hT h).2

/-- `ID`'s context, up to persistent slots.  `[spec §10]` -/
theorem gSepC_soloP {ls : List SRec} {δ : LSub} : ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy},
    Ctx.SoloP Γ i T → ∀ {γ : List Val} {ρ : WRes}, i < γ.length → gSepC ls δ Γ γ ρ →
      ∃ v, γ[i]? = some v ∧ vP T ls δ v ρ := by
  intro Γ i T hs
  induction hs with
  | here hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [gSepC_deadP hdead hrest] at hc
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
            ih (γ := γ') (by simpa using hlen) (gSepC_cons_persistent hS hg).2
          exact ⟨w, by simpa using hw, hv⟩

/-- `Γ = Γ₁, Γ₂` splits the resource; a persistent slot, at `∅`, goes to both sides.
`[spec §10]` -/
theorem gSepC_splitP {ls : List SRec} {δ : LSub} : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ →
    ∀ {γ : List Val} {ρ : WRes}, gSepC ls δ Γ γ ρ →
      (gSepC ls δ Γ₁ γ ⋆ gSepC ls δ Γ₂ γ) ρ := by
  intro Γ Γ₁ Γ₂ hsp
  induction hsp with
  | nil =>
      intro γ ρ h
      refine ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ?_⟩
      cases γ <;> exact ⟨rfl, trivial⟩
  | left _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hcσ hc
          exact ⟨x, σ₂, hxρ, ⟨ρ₁, σ₁, hx, hv, h₁⟩, h₂⟩
  | right _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_lcomm hcσ hc
          exact ⟨σ₁, x, hxρ, h₁, ⟨ρ₁, σ₂, hx, hv, h₂⟩⟩
  | dead _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' => exact ih (γ := γ') h
  | dup hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨hv, hrest⟩ := gSepC_cons_persistent hT h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          exact ⟨σ₁, σ₂, hcσ, ⟨PMap.empty, σ₁, compS_empty_left σ₁, hv, h₁⟩,
            ⟨PMap.empty, σ₂, compS_empty_left σ₂, hv, h₂⟩⟩

end BoCa.Fig16.LogRel.Core

end
