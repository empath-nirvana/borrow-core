import Core.TreeGoal791
import Core.TreeConsumeInst
import Support.Model.Tree.World.Ops

/-!
# T-X: the decisive test for a `mut` lend on the tree (RQ1, research branch `rq1-tree`)

Test configurations only; neither candidate of `Core/TreeGoal791.lean` §6 is built. One world:
the chain tree, the store typing `1 : unit`, and the cell `1` lent `mut` at `{1}` and folded
(`TWNT.alloc` then `TWNT.mutFold`): the world is the borrower's token `1 ↦ mut({1}, (), ∅, ⟦unit⟧)`
alone, no records, the memory `1 ↦ ()` (`tx_token_world`).

* **B2, candidate B's hand-back** (`TokenBackT`): refuted at this world (`tx_not_tokenBackT`). A run
  holding the token, at a frame holding nothing, ends at `()` holding nothing: the end world is the
  frame's re-reading, empty, but the memory still holds `1` (`endT_drop_frees`).
* **A5/A6, candidate A's adequacy at an ended `mut` island**: the token left as garbage at no
  records. `ReclaimT` (A6, A5's content) is refuted at this world (`tx_not_reclaimT`): the garbage is
  own-free, the records are `[]`, and it is not empty. The run that leaves it
  (`tx_twpG_ends_token_live`) meets A5's premise on the postcondition (nothing read, no records, no
  list) while the memory holds `1`: `twpG_ends_record_live`'s configuration with no record at all,
  so A5's guard `O = []` does not exclude it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Goal791.TX
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)

/-- The store typing `1 : unit`. -/
abbrev ΘU : CodeTy := fun l => if l = 1 then some KTy.unit else none

/-- The chain tree at `ΘU`. -/
abbrev wU : TWd := ⟨chainP, ΘU, tmplT _ ΘU⟩

/-- The memory `1 ↦ ()`. -/
abbrev μ₁ : Heap := BoCa.BoLo.Heap.upd (fun _ => none) 1 BoCa.Val.unit

/-- The token: `1 ↦ mut({1}, (), ∅, ⟦unit⟧)`. -/
abbrev tok : TRes wU.K :=
  ResUT.single 1 (CellUT.mutOf (TSet.single 1) BoCa.Val.unit PMap.empty
    (emptyT_inStratum _) (tyPred (KTy.unit.interp ΘU) wU.K (TSet.single 1)) ⟨rfl, rfl⟩)

theorem tx_noOwn : NoOwnT tok := fun l ψ e => by
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  simp [CellUT.mutOf, CellUT.kind]

theorem tx_tok_get : ∃ ψ, tok.get 1 = some ψ ∧ ψ.kind = Kind.mut :=
  ⟨_, ResUT.single_get_self _ _, by simp [CellUT.mutOf, CellUT.kind]⟩

/-- **The world of the folded `mut` lend**: the token alone, no records, memory `1 ↦ ()`. -/
theorem tx_token_world : RecInv wU tok [] [] ∧ WInv wU tok μ₁ := by
  have hR0 : RecInv wU (PMap.empty : TRes wU.K) [] [] := ⟨.empty, fun _ hx => by simp at hx⟩
  have hI0 : WInv wU (PMap.empty : TRes wU.K) (fun _ => none) :=
    ⟨fun _ _ e => by simp at e, lower_emptyT⟩
  have hW' : ResUT.CompS (PMap.empty : TRes wU.K)
      (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) :=
    ResUT.CompS.comm (ResUT.compS_empty_right _)
  obtain ⟨hR', hI'⟩ := recWInv_alloc hR0 hI0 rfl hW'
  obtain ⟨fρ', hc', hI'', -⟩ := mutLend_world (w := wU) (s := TSet.single 1) (l := 1) (A := KTy.unit) (v := BoCa.Val.unit)
    (hΘ := (by simp [ΘU] : ΘU 1 = some KTy.unit)) (emptyT_inStratum _) (⟨rfl, rfl⟩ :
      (KTy.unit.interp ΘU).P wU.K BoCa.Val.unit PMap.empty) hW' hW' hI'
  obtain rfl := ResUT.CompS.functional hc' (ResUT.CompS.comm (ResUT.compS_empty_right _))
  refine ⟨⟨TWNT.mutFold hR'.1 (ResUT.compS_empty_right _) (ResUT.compS_empty_right _)
    (ResUT.compS_empty_right _) hI''.valid, fun _ hx => by simp at hx⟩, hI''⟩

theorem tx_finDom : FinDom μ₁ :=
  ⟨[1], fun l hl => by
    by_cases e : l = 1
    · simp [e]
    · exact absurd (BoCa.BoLo.Heap.upd_other e) hl⟩

/-- **B2 refuted**: `TokenBackT` fails at the token world. -/
theorem tx_not_tokenBackT : ¬ TokenBackT (ℍ := ℍ) := by
  intro hT
  obtain ⟨hR, hI⟩ := tx_token_world
  have h := hT (fun _ ρf => ρf = PMap.empty) (fun _ _ _ _ _ ρ' => ρ' = PMap.empty) 1 wU [] []
    (.val Val.unit) 1 tok (fun _ _ _ _ _ _ x => x) tx_tok_get
  have hc : ResUT.CompS (PMap.empty : TRes wU.K) tok tok :=
    ResUT.CompS.comm (ResUT.compS_empty_right _)
  have hS : SplitT ([] : List (FrameRecT wU.K)) [] [] :=
    ⟨fun p => by simp, fun p hp => by simp at hp⟩
  have hE := h wU tok PMap.empty tok [] [] [] [] μ₁ (TWd.Ext.refl _ _) (RR.refl hI.1)
    List.Forall₂.nil List.Forall₂.nil rfl ⟨hc.1, _, hc, hI.valid⟩ hc hS hR hI tx_finDom 0 _ _
    (by omega) (.refl _ _) (LogRel.Core.final_val _ Val.unit)
  have := endT_drop_frees (l := 1) (fun _ _ _ _ _ _ x => x) valid_emptyT
    (noneAt_empty _) hE
  simp at this

/-- **A6 refuted**: own-free garbage at no records need not be empty. -/
theorem tx_not_reclaimT : ¬ ReclaimT := by
  intro hR6
  obtain ⟨hR, hI⟩ := tx_token_world
  have e := hR6 wU tok tok PMap.empty μ₁ tx_noOwn
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) hR hI
  obtain ⟨ψ, hψ, -⟩ := tx_tok_get
  rw [e] at hψ
  simp at hψ

/-! ### The token left as garbage -/

theorem tx_noOwn_compS {K : WCactus} {a b c : TRes K} (h : ResUT.CompS a b c) (ha : NoOwnT a)
    (hb : NoOwnT b) : NoOwnT c := by
  intro l ψ e
  rcases ResUT.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, -, -, f, hC⟩
  · rw [f] at e; cases e
  · rw [f] at e; cases e; exact ha l _ f₁
  · rw [f] at e; cases e; exact hb l _ f₂
  · rw [f] at e; cases e
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, -, -, rfl⟩ := hC
    simp

theorem tx_noOwn_rr {Θ : LocTy} {K K' : WCactus} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ')
    (hn : NoOwnT ρ) : NoOwnT ρ' := by
  intro l ψ' e
  obtain ⟨ψ, e₀, hr⟩ := h.get_some' e
  rw [hr.kind]
  exact hn l ψ e₀

/-- **A run ends at an ended `mut` island leaving the token as garbage**: from the token, `()`
ends reading nothing, owning no records, at the empty list (A5's premise on the postcondition),
while its memory, its start memory, holds `1` (`tx_token_world`). -/
theorem tx_twpG_ends_token_live (F : TFrame) (n : Nat) :
    twpG (ℍ := ℍ) F (fun _ _ ls O _ ρ => ρ = PMap.empty ∧ O = [] ∧ ls = []) n wU [] []
      (.val Val.unit) tok := by
  intro g ρg hg hc
  refine twp_here (fun μ => LogRel.Core.final_val μ Val.unit) fun w₀ ρ₀ ls₀ O₀ _ hr hl hO => ?_
  cases hl
  cases hO
  exact ⟨PMap.empty, ρ₀, ResUT.CompS.comm (ResUT.compS_empty_right _),
    tx_noOwn_rr hr (tx_noOwn_compS hc tx_noOwn hg), rfl, rfl, rfl⟩

end BoCa.Fig16.Tree.Wp.Goal791.TX

end
