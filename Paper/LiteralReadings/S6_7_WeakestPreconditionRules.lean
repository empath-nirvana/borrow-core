import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_7_WeakestPreconditionRules.Lemmas
import Support.Dynamics.Machine
import Support.Dynamics.PrintedWp
import Support.Model.CellFacts
import Support.Model.Composition
import Support.Model.Empty
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.ReborrowFrame
import Support.Model.Singletons
import Support.Model.Update
import Support.Model.WalkSplitting
import Support.Syntax.Terms

/-!
# Literal readings — [TR] §6.7

* 6.135 (`wp-bind`) over `[TR]` §3's printed machine (§12.42, D6): the closed,
  well-typed terms `inj₁ (free (alloc ()))` and `free (alloc ()); ()` are stuck
  there, `TR3.wp` does not hold at such a term, and `TR3.wp` is strictly below the
  library's `wp`;
* 6.150 (`↺ rule`): the entailment without the hypothesis `RebEscrow`, measured at
  the configuration `DeepReborrow`, and that configuration outside `RebEscrow`
  (§12.57).

Nothing depends on this file.
-/

noncomputable section

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-!
### Lemma 6.135 (wp-bind) — literal reading

The record is in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean`.
-/
/-- `inj₁ (free (alloc ()))`, typed at `1 ⊕ T` by `derives_wInj`, takes no step and
never reaches a value.
`[about ours: the printed `Kont` of `[TR]` p. 3, at `[TR]` p. 1's `inj₁ e`]` -/
theorem stuck_wInj (μ : Heap) :
    (∀ μ' e', ¬ Step1 μ wInj μ' e') ∧ ∀ (μ' : Heap) (v : Val), ¬ Steps μ wInj μ' (.val v) :=
  ⟨fun _ _ => no_step_inj₁, fun _ v h => by
    obtain ⟨-, he⟩ := Steps.stuck (fun _ _ => no_step_inj₁) h
    exact absurd (IsVal.inj₁_inv (he ▸ Val.isVal v)) (by simp [wFreeAlloc])⟩

/-! Lemma 6.135 (wp-bind), literal reading, continued. -/
/-- `(free (alloc ())); ()`, typed at `1` by `derives_wSeq`, takes no step and never
reaches a value.
`[about ours: the printed `Kont` of `[TR]` p. 3, at `[TR]` p. 1's `e₁;e₂`]` -/
theorem stuck_wSeq (μ : Heap) :
    (∀ μ' e', ¬ Step1 μ wSeq μ' e') ∧ ∀ (μ' : Heap) (v : Val), ¬ Steps μ wSeq μ' (.val v) :=
  ⟨fun _ _ => no_step_seq (by simp [wFreeAlloc]),
   fun _ _ => steps_seq_ne_val (by simp [wFreeAlloc])⟩

/-! Lemma 6.135 (wp-bind), literal reading, continued. -/
/-- `wp(inj₁ e)` does not hold whenever `e` is not a value.
`[about ours: `[TR]` p. 6's row over the printed machine, at p. 1's
`inj₁ e`]` -/
theorem wp_inj₁_false {ρ ρf : WRes} (hf : ResU.Hash ρf ρ) (e : Expr)
    (he : ¬ IsVal e) (Q : Val → WProp) : ¬ wp (.inj₁ e) Q ρ := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h₈, _, _, _, _⟩ := h ρf hf
  obtain ⟨-, hv⟩ := Steps.stuck (fun _ _ => no_step_inj₁) h₈
  exact he (IsVal.inj₁_inv (hv ▸ Val.isVal _))

/-! Lemma 6.135 (wp-bind), literal reading, continued. -/
/-- `wp(e₁; e₂)` does not hold whenever `e₁` is not literally `()`.
`[about ours: `[TR]` p. 6's row over the printed machine, at p. 1's
`e₁;e₂`]` -/
theorem wp_seq_false {ρ ρf : WRes} (hf : ResU.Hash ρf ρ) {e₁ : Expr} (e₂ : Expr)
    (h₁ : e₁ ≠ .val .unit) (Q : Val → WProp) : ¬ wp (.seq e₁ e₂) Q ρ := by
  intro h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h₈, _, _, _, _⟩ := h ρf hf
  exact steps_seq_ne_val h₁ h₈

/-! Lemma 6.135 (wp-bind), literal reading, continued. -/
/-- An owned cell, with `∅` as an admissible frame, at which `wp wSeq` does not hold.
`[about ours: an inhabited instance of the refutations]` -/
theorem wp_stuck_false_nonvacuous (l : BoCa.Loc) (w : Val) (Q : Val → WProp) :
    ¬ wp wSeq Q (ResU.single l (CellU.ownOf w)) := by
  refine wp_seq_false
    (ResU.hash_symm (ResU.hash_empty_right (ResU.valid_single_own l w))) _ ?_ Q
  simp [wFreeAlloc]

/-! Lemma 6.135 (wp-bind), literal reading, continued. -/
/-- `wp_le_fig16` is strict: at `inj₁ (free ℓ)` and an owned cell, the library's `wp`
holds and `TR3.wp` does not.
`[about ours: the two `wp`s, over the two machines]` -/
theorem wp_lt_fig16 (l : BoCa.Loc) :
    Fig16.BoLo.wp (.inj₁ (.app (.val (.prim .free)) (.val (.loc l))))
        (fun _ => top) (ResU.single l (CellU.ownOf .unit)) ∧
    ¬ wp (.inj₁ (.app (.val (.prim .free)) (.val (.loc l))))
        (fun _ => top) (ResU.single l (CellU.ownOf .unit)) := by
  constructor
  · refine Fig16.BoLo.wp_bind (.inj₁ .hole) _ _ _ ?_
    refine Fig16.BoLo.wp_free l .unit _ _ ⟨_, PMap.empty,
      ResU.comp_empty_right _, rfl, ?_⟩
    -- `inj₁ ()` is a value, so `wp-val` applies.
    exact Fig16.BoLo.wp_val (.inj₁ .unit) _ _ trivial
  · exact wp_inj₁_false
      (ResU.hash_symm (ResU.hash_empty_right (ResU.valid_single_own l .unit)))
      (.app (.val (.prim .free)) (.val (.loc l)))
      (fun hv => Prim.noConfusion (Expr.prim.inj hv.app_fun)) _

end BoCa.TR3

namespace BoCa.DeepReborrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-! `[about ours]` -/
def 𝓋 : BoCa.Val := BoCa.Val.unit

def mk2 (a b : Nat) (x y : CellU Nat BoCa.Val) : ResU Nat BoCa.Val where
  get := fun l => if l = a then some x else if l = b then some y else none
  finite := by
    refine ⟨[a, b], fun l h => ?_⟩
    by_cases e : l = a
    · exact List.mem_cons.mpr (Or.inl e)
    · by_cases f : l = b
      · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr f))
      · exfalso; apply h
        show (if l = a then some x else if l = b then some y else none) = none
        rw [if_neg e, if_neg f]

theorem mk2_a {a b : Nat} (x y : CellU Nat BoCa.Val) : (mk2 a b x y).get a = some x := by
  show (if a = a then some x else _) = some x; rw [if_pos rfl]

theorem mk2_b {a b : Nat} (x y : CellU Nat BoCa.Val) (h : b ≠ a) :
    (mk2 a b x y).get b = some y := by
  show (if b = a then some x else if b = b then some y else none) = some y
  rw [if_neg h, if_pos rfl]

theorem mk2_ne {a b l : Nat} (x y : CellU Nat BoCa.Val) (ha : l ≠ a) (hb : l ≠ b) :
    (mk2 a b x y).get l = none := by
  show (if l = a then some x else if l = b then some y else none) = none
  rw [if_neg ha, if_neg hb]

def mk3 (a b c : Nat) (x y z : CellU Nat BoCa.Val) : ResU Nat BoCa.Val where
  get := fun l =>
    if l = a then some x else if l = b then some y else if l = c then some z else none
  finite := by
    refine ⟨[a, b, c], fun l h => ?_⟩
    by_cases e : l = a
    · exact List.mem_cons.mpr (Or.inl e)
    · by_cases f : l = b
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl f)))
      · by_cases g : l = c
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr g))))
        · exfalso; apply h
          show (if l = a then some x else if l = b then some y else if l = c then some z
            else none) = none
          rw [if_neg e, if_neg f, if_neg g]

theorem mk3_a {a b c : Nat} (x y z : CellU Nat BoCa.Val) : (mk3 a b c x y z).get a = some x := by
  show (if a = a then some x else _) = some x; rw [if_pos rfl]

theorem mk3_b {a b c : Nat} (x y z : CellU Nat BoCa.Val) (h : b ≠ a) :
    (mk3 a b c x y z).get b = some y := by
  show (if b = a then some x else if b = b then some y else _) = some y
  rw [if_neg h, if_pos rfl]

theorem mk3_c {a b c : Nat} (x y z : CellU Nat BoCa.Val) (ha : c ≠ a) (hb : c ≠ b) :
    (mk3 a b c x y z).get c = some z := by
  show (if c = a then some x else if c = b then some y else if c = c then some z else none)
    = some z
  rw [if_neg ha, if_neg hb, if_pos rfl]

theorem mk3_ne {a b c l : Nat} (x y z : CellU Nat BoCa.Val) (ha : l ≠ a) (hb : l ≠ b) (hc : l ≠ c) :
    (mk3 a b c x y z).get l = none := by
  show (if l = a then some x else if l = b then some y else if l = c then some z else none) = none
  rw [if_neg ha, if_neg hb, if_neg hc]

end BoCa.DeepReborrow

namespace BoCa.DeepReborrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
variable (α β : Life) (v u w : BoCa.Val)

/-- The payload `ρ″ = 0 ↦ own(v) ⊎ 1 ↦ own(u)`. -/
def rho2 : ResU Nat BoCa.Val := mk2 0 1 (CellU.ownOf v) (CellU.ownOf u)

theorem rho2_0 : (rho2 v u).get 0 = some (CellU.ownOf v) := mk2_a _ _

theorem rho2_1 : (rho2 v u).get 1 = some (CellU.ownOf u) := mk2_b _ _ (by decide)

theorem rho2_ne {l : Nat} (h0 : l ≠ 0) (h1 : l ≠ 1) : (rho2 v u).get l = none :=
  mk2_ne _ _ h0 h1

theorem rho2_stratum (γ : Life) : (rho2 v u).InStratum γ := by
  intro l ψ e
  by_cases e0 : l = 0
  · subst e0; rw [rho2_0] at e; cases e; exact trivial
  · by_cases e1 : l = 1
    · subst e1; rw [rho2_1] at e; cases e; exact trivial
    · rw [rho2_ne _ _ e0 e1] at e; cases e

def cellF : CellU Nat BoCa.Val :=
  CellU.immOf (LSet.singleton β) v PMap.empty (by intro l ψ e; cases e)

def cellB : CellU Nat BoCa.Val :=
  CellU.immOf (LSet.singleton α) w (rho2 v u) (rho2_stratum v u _)

theorem cellF_kind : (cellF β v).kind = Kind.imm := rfl

theorem cellB_kind : (cellB α v u w).kind = Kind.imm := rfl

theorem cellF_wit : (cellF β v).wit = PMap.empty := CellU.wit_immOf _ _ _ _

theorem cellB_wit : (cellB α v u w).wit = rho2 v u := CellU.wit_immOf _ _ _ _

/-- The composite state `ρ_f ● (borrow cell)`. -/
def comp : ResU Nat BoCa.Val := mk2 0 2 (cellF β v) (cellB α v u w)

theorem comp_0 : (comp α β v u w).get 0 = some (cellF β v) := mk2_a _ _

theorem comp_2 : (comp α β v u w).get 2 = some (cellB α v u w) := mk2_b _ _ (by decide)

theorem comp_ne {l : Nat} (h0 : l ≠ 0) (h2 : l ≠ 2) : (comp α β v u w).get l = none :=
  mk2_ne _ _ h0 h2

theorem exR_empty : ExR (PMap.empty : ResU Nat BoCa.Val) PMap.empty := by
  refine ExW.mk (w := []) (b := PMap.empty) (nm := PMap.empty) ?_ ExWits.nil
    BigComp.nil ?_ (ResU.comp_empty_right _)
  · exact ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp),
      by rintro ⟨ψ, e, -⟩; cases e⟩⟩
  · rw [restrict_empty, restrict_empty]; exact ResU.comp_empty_right _

theorem rho2_restrict_own : ResU.restrict (rho2 v u) Kind.own = rho2 v u := by
  refine PMap.ext fun l => ?_
  by_cases e0 : l = 0
  · subst e0
    rw [ResU.restrict_get_some (k := Kind.own) (rho2_0 v u) (CellU.kind_ownOf v), rho2_0]
  · by_cases e1 : l = 1
    · subst e1
      rw [ResU.restrict_get_some (k := Kind.own) (rho2_1 v u) (CellU.kind_ownOf u), rho2_1]
    · rw [ResU.restrict_get_none (rho2_ne v u e0 e1), rho2_ne v u e0 e1]

theorem rho2_restrict_mut : ResU.restrict (rho2 v u) Kind.mut = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  by_cases e0 : l = 0
  · subst e0; exact ResU.restrict_get_ne (rho2_0 v u) (by rw [CellU.kind_ownOf]; decide)
  · by_cases e1 : l = 1
    · subst e1; exact ResU.restrict_get_ne (rho2_1 v u) (by rw [CellU.kind_ownOf]; decide)
    · exact ResU.restrict_get_none (rho2_ne v u e0 e1)

theorem rho2_restrict_imm : ResU.restrict (rho2 v u) Kind.imm = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  by_cases e0 : l = 0
  · subst e0; exact ResU.restrict_get_ne (rho2_0 v u) (by rw [CellU.kind_ownOf]; decide)
  · by_cases e1 : l = 1
    · subst e1; exact ResU.restrict_get_ne (rho2_1 v u) (by rw [CellU.kind_ownOf]; decide)
    · exact ResU.restrict_get_none (rho2_ne v u e0 e1)

theorem rho2_sites_mut : ResU.Sites (rho2 v u) Kind.mut [] := by
  refine ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), ?_⟩⟩
  rintro ⟨ψ, hg, hk⟩
  by_cases e0 : l = 0
  · subst e0; rw [rho2_0] at hg; cases hg; rw [CellU.kind_ownOf] at hk; exact Kind.noConfusion hk
  · by_cases e1 : l = 1
    · subst e1; rw [rho2_1] at hg; cases hg; rw [CellU.kind_ownOf] at hk; exact Kind.noConfusion hk
    · rw [rho2_ne v u e0 e1] at hg; cases hg

theorem rho2_sites_imm : ResU.Sites (rho2 v u) Kind.imm [] := by
  refine ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), ?_⟩⟩
  rintro ⟨ψ, hg, hk⟩
  by_cases e0 : l = 0
  · subst e0; rw [rho2_0] at hg; cases hg; rw [CellU.kind_ownOf] at hk; exact Kind.noConfusion hk
  · by_cases e1 : l = 1
    · subst e1; rw [rho2_1] at hg; cases hg; rw [CellU.kind_ownOf] at hk; exact Kind.noConfusion hk
    · rw [rho2_ne v u e0 e1] at hg; cases hg

theorem exR_rho2 : ExR (rho2 v u) (rho2 v u) := by
  refine ExW.mk (w := []) (b := PMap.empty) (nm := rho2 v u)
    (rho2_sites_mut v u) ExWits.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [rho2_restrict_own, rho2_restrict_mut]
  exact ResU.comp_empty_right _

theorem agW_rho2 : AgW (rho2 v u) (PMap.empty : ResU Nat BoCa.Val) := by
  refine AgW.mk (wm := []) (wi := []) (a := PMap.empty) (bm := PMap.empty)
    (bi := PMap.empty) (rho2_sites_mut v u) (rho2_sites_imm v u)
    AgWitsM.nil AgWitsI.nil BigComp.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [rho2_restrict_imm]; exact ResU.comp_empty_right _

theorem comp_restrict_own : ResU.restrict (comp α β v u w) Kind.own = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  by_cases e0 : l = 0
  · subst e0; exact ResU.restrict_get_ne (comp_0 α β v u w) (by rw [cellF_kind]; decide)
  · by_cases e2 : l = 2
    · subst e2; exact ResU.restrict_get_ne (comp_2 α β v u w) (by rw [cellB_kind]; decide)
    · exact ResU.restrict_get_none (comp_ne α β v u w e0 e2)

theorem comp_restrict_mut : ResU.restrict (comp α β v u w) Kind.mut = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  by_cases e0 : l = 0
  · subst e0; exact ResU.restrict_get_ne (comp_0 α β v u w) (by rw [cellF_kind]; decide)
  · by_cases e2 : l = 2
    · subst e2; exact ResU.restrict_get_ne (comp_2 α β v u w) (by rw [cellB_kind]; decide)
    · exact ResU.restrict_get_none (comp_ne α β v u w e0 e2)

theorem comp_restrict_imm : ResU.restrict (comp α β v u w) Kind.imm = comp α β v u w := by
  refine PMap.ext fun l => ?_
  by_cases e0 : l = 0
  · subst e0
    rw [ResU.restrict_get_some (comp_0 α β v u w) (cellF_kind β v), comp_0]
  · by_cases e2 : l = 2
    · subst e2
      rw [ResU.restrict_get_some (comp_2 α β v u w) (cellB_kind α v u w), comp_2]
    · rw [ResU.restrict_get_none (comp_ne α β v u w e0 e2), comp_ne α β v u w e0 e2]

theorem comp_sites_mut : ResU.Sites (comp α β v u w) Kind.mut [] := by
  refine ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), ?_⟩⟩
  rintro ⟨ψ, hg, hk⟩
  by_cases e0 : l = 0
  · subst e0; rw [comp_0] at hg; cases hg; rw [cellF_kind] at hk; exact Kind.noConfusion hk
  · by_cases e2 : l = 2
    · subst e2; rw [comp_2] at hg; cases hg; rw [cellB_kind] at hk; exact Kind.noConfusion hk
    · rw [comp_ne α β v u w e0 e2] at hg; cases hg

theorem comp_sites_imm : ResU.Sites (comp α β v u w) Kind.imm [0, 2] := by
  refine ⟨by decide, fun l => ⟨fun h => ?_, fun ⟨ψ, hg, hk⟩ => ?_⟩⟩
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨cellF β v, comp_0 α β v u w, cellF_kind β v⟩
    · cases List.mem_singleton.mp h
      exact ⟨cellB α v u w, comp_2 α β v u w, cellB_kind α v u w⟩
  · by_cases e0 : l = 0
    · exact e0 ▸ List.mem_cons.mpr (Or.inl rfl)
    · by_cases e2 : l = 2
      · exact e2 ▸ List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))
      · rw [comp_ne α β v u w e0 e2] at hg; cases hg

theorem exS_comp : ExS (comp α β v u w) PMap.empty := by
  refine ExW.mk (w := []) (b := PMap.empty) (nm := PMap.empty)
    (comp_sites_mut α β v u w) ExWits.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [comp_restrict_own, comp_restrict_mut]
  exact ResU.comp_empty_right _

theorem agWitsI_comp : AgWitsI (comp α β v u w) [(0, PMap.empty), (2, rho2 v u)] := by
  refine AgWitsI.cons (cellF β v) (comp_0 α β v u w) (cellF_kind β v)
    PMap.empty PMap.empty ?_ ?_ (ResU.comp_empty_right _) ?_
  · rw [cellF_wit]; exact exR_empty
  · rw [cellF_wit]; exact agW_empty
  refine AgWitsI.cons (cellB α v u w) (comp_2 α β v u w) (cellB_kind α v u w)
    (rho2 v u) PMap.empty ?_ ?_ (ResU.comp_empty_right _) AgWitsI.nil
  · rw [cellB_wit]; exact exR_rho2 v u
  · rw [cellB_wit]; exact agW_rho2 v u

theorem bigComp_bi : BigComp CellU.CompatR CellU.CompR [PMap.empty, rho2 v u] (rho2 v u) :=
  BigComp.cons (BigComp.cons BigComp.nil (ResU.comp_empty_right _)) (ResU.comp_empty_left _)

def sigma : ResU Nat BoCa.Val := mk3 0 1 2 (cellF β v) (CellU.ownOf u) (cellB α v u w)

theorem sigma_0 : (sigma α β v u w).get 0 = some (cellF β v) := mk3_a _ _ _

theorem sigma_1 : (sigma α β v u w).get 1 = some (CellU.ownOf u) := mk3_b _ _ _ (by decide)

theorem sigma_2 : (sigma α β v u w).get 2 = some (cellB α v u w) :=
  mk3_c _ _ _ (by decide) (by decide)

theorem sigma_ne {l : Nat} (h0 : l ≠ 0) (h1 : l ≠ 1) (h2 : l ≠ 2) :
    (sigma α β v u w).get l = none := mk3_ne _ _ _ h0 h1 h2

theorem agW_comp : AgW (comp α β v u w) (sigma α β v u w) := by
  refine AgW.mk (wm := []) (wi := [(0, PMap.empty), (2, rho2 v u)])
    (a := comp α β v u w) (bm := PMap.empty) (bi := rho2 v u)
    (comp_sites_mut α β v u w) (comp_sites_imm α β v u w)
    AgWitsM.nil (agWitsI_comp α β v u w) BigComp.nil (bigComp_bi v u) ?_ ?_
  · rw [comp_restrict_imm]; exact ResU.comp_empty_right _
  · refine ⟨?_, fun l => ?_⟩
    · intro l ψ₁ ψ₂ e₁ e₂
      by_cases e0 : l = 0
      · subst e0
        rw [comp_0] at e₁; rw [rho2_0] at e₂; cases e₁; cases e₂
        exact ⟨_, CellU.CompR.immOwn (LSet.singleton β) v PMap.empty (by intro l ψ e; cases e)⟩
      · by_cases e2 : l = 2
        · subst e2; rw [rho2_ne v u (by decide) (by decide)] at e₂; cases e₂
        · rw [comp_ne α β v u w e0 e2] at e₁; cases e₁
    · by_cases e0 : l = 0
      · subst e0
        rw [comp_0, rho2_0, sigma_0]
        exact ⟨cellF β v, rfl,
          CellU.CompR.immOwn (LSet.singleton β) v PMap.empty (by intro l ψ e; cases e)⟩
      · by_cases e1 : l = 1
        · subst e1
          rw [comp_ne α β v u w (by decide) (by decide), rho2_1, sigma_1]; exact rfl
        · by_cases e2 : l = 2
          · subst e2
            rw [comp_2, rho2_ne v u (by decide) (by decide), sigma_2]; exact rfl
          · rw [comp_ne α β v u w e0 e2, rho2_ne v u e0 e1, sigma_ne α β v u w e0 e1 e2]
            exact rfl

theorem flat_composite : ResU.Flat (comp α β v u w) (sigma α β v u w) :=
  ⟨PMap.empty, sigma α β v u w, exS_comp α β v u w, agW_comp α β v u w,
    ResU.comp_empty_left _⟩

/-- The configuration's composite is valid. -/
theorem Valid_composite : ResU.Valid (comp α β v u w) :=
  ⟨_, flat_composite α β v u w⟩

/-- `ρ_f ● (borrow cell) = comp`, borrow cell first, as the `↺` rule's LHS needs. -/
theorem bcell_frame_comp :
    ResU.CompS (ResU.single 2 (cellB α v u w)) (ResU.single 0 (cellF β v))
      (comp α β v u w) := by
  refine ⟨ResU.Compat.of_disjoint (fun l => ?_), fun l => ?_⟩
  · by_cases e2 : l = 2
    · subst e2; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ e2)
  · by_cases e0 : l = 0
    · subst e0
      rw [ResU.single_get_ne _ (by decide : (0:Nat) ≠ 2), ResU.single_get_self, comp_0]
      exact rfl
    · by_cases e2 : l = 2
      · subst e2
        rw [ResU.single_get_self, ResU.single_get_ne _ (by decide : (2:Nat) ≠ 0), comp_2]
        exact rfl
      · rw [ResU.single_get_ne _ e2, ResU.single_get_ne _ e0, comp_ne α β v u w e0 e2]
        exact rfl

def witU : ResU Nat BoCa.Val := ResU.single 1 (CellU.ownOf u)

theorem witU_stratum (γ : Life) : (witU u).InStratum γ := by
  intro l ψ e; obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; exact trivial

/-- `rebA β = 0 ↦ imm({β}, v, 1↦own(u))` — the deep reborrow A. -/
def rebA : ResU Nat BoCa.Val :=
  ResU.single 0 (CellU.immOf (LSet.singleton β) v (witU u) (witU_stratum u _))

theorem rebA_0 : (rebA β v u).get 0 =
    some (CellU.immOf (LSet.singleton β) v (witU u) (witU_stratum u _)) :=
  ResU.single_get_self _ _

end BoCa.DeepReborrow

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps)

/-!
### Theorem 6.150 (↺ rule) — literal reading

The record is in `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean`.
-/
/-- `ρ″ = 0↦own(𝓋) ⊎ 1↦own(𝓋)` reborrows at `β` to `rebA β = 0↦imm({β}, 𝓋, 1↦own(𝓋))`,
while `ag(comp)` carries `0↦imm({β}, 𝓋, ∅)`; the witnesses differ, which
`Fig16.EscrowAgree` forbids.
`[about ours: the `DeepReborrow` witness measured against this rule's added
hypothesis]` -/
theorem deepReborrow_not_rebEscrow (b : Life) :
    ResU.Reb b (BoCa.DeepReborrow.rho2 BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋)
        (BoCa.DeepReborrow.rebA b BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋) →
    ¬ ∀ r a : WRes, AgW r a →
        EscrowAgree (BoCa.DeepReborrow.rho2 BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋)
          (BoCa.DeepReborrow.rebA b BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋) a := by
  intro _ h
  have hwit := h _ _ (BoCa.DeepReborrow.agW_comp ⊤ b BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋)
    0 BoCa.DeepReborrow.𝓋 _ _ (BoCa.DeepReborrow.rho2_0 _ _)
    (BoCa.DeepReborrow.rebA_0 b BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋)
    (BoCa.DeepReborrow.sigma_0 ⊤ b BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋 BoCa.DeepReborrow.𝓋)
    (by rw [CellU.kind_immOf]; exact fun c => Kind.noConfusion c)
    (by rw [BoCa.DeepReborrow.cellF_kind]; exact fun c => Kind.noConfusion c)
  rw [BoCa.DeepReborrow.cellF_wit, CellU.wit_immOf] at hwit
  have hg : (PMap.empty : WRes).get 1 = (BoCa.DeepReborrow.witU BoCa.DeepReborrow.𝓋).get 1 := by
    rw [hwit]
  rw [PMap.empty_get, show (BoCa.DeepReborrow.witU BoCa.DeepReborrow.𝓋).get 1
      = some (CellU.ownOf BoCa.DeepReborrow.𝓋) from ResU.single_get_self _ _] at hg
  exact absurd hg (by simp)

end BoCa.Fig16.BoLo

namespace BoCa.DeepReborrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
variable (α β : Life) (v u w : BoCa.Val)

/-! `[about ours]` -/
/-- The shallow `0↦imm(s, x, ∅)` and the deep `rebA β = 0↦imm({β}, v, 1↦own(u))`
are incompatible: their witnesses differ. -/
theorem noCompat (b : Life) (x : BoCa.Val) (c : Life) :
    ¬ ResU.CompatS (ResU.single 0 (cellF b x)) (rebA c v u) := by
  intro hc
  -- `cellF b x` and `rebA c`'s cell are both `single 0 (immOf …)`
  have hw : (PMap.empty : ResU Nat BoCa.Val) = witU u :=
    (ResU.compatS_single_imm_inv (s := LSet.singleton b) (t := LSet.singleton c)
      (v₁ := x) (v₂ := v) (ρ₁ := PMap.empty) (ρ₂ := witU u) hc).2
  have hg : (PMap.empty : ResU Nat BoCa.Val).get 1 = (witU u).get 1 := by rw [hw]
  rw [PMap.empty_get,
    show (witU u).get 1 = some (CellU.ownOf u) from ResU.single_get_self _ _] at hg
  exact absurd hg (by simp)

theorem rho2_del_0 : (rho2 v u).del 0 = witU u := by
  refine PMap.ext fun l => ?_
  by_cases e0 : l = 0
  · subst e0; rw [ResU.del_get_self]; rw [show (witU u).get 0 = none from
      ResU.single_get_ne _ (by decide)]
  · by_cases e1 : l = 1
    · subst e1
      rw [ResU.del_get_ne _ e0, rho2_1, show (witU u).get 1 = some (CellU.ownOf u) from
        ResU.single_get_self _ _]
    · rw [ResU.del_get_ne _ e0, rho2_ne v u e0 e1,
        show (witU u).get l = none from ResU.single_get_ne _ e1]

end BoCa.DeepReborrow

namespace BoCa.DeepReborrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem mem_single {ρ p : ResU Nat BoCa.Val} {l : Nat}
    (hm : (l, p) ∈ [((0 : Nat), ρ)]) : l = 0 ∧ p = ρ := by
  have he := List.mem_singleton.mp hm
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

end BoCa.DeepReborrow

namespace BoCa.DeepReborrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
variable (α β : Life) (v u w : BoCa.Val)

/-- `ρ″ = 0↦own(v) ⊎ 1↦own(u)` reborrows at any `β ⊏ ⊤` to `rebA β`, by the `own`
clause of `reb_β` with witness `π(0)/0 = 1↦own(u)`. -/
theorem reb_rho2_rebA (hβ : (⊤ : Life) ⊐ β) :
    ResU.Reb β (rho2 v u) (rebA β v u) := by
  refine ⟨rho2_stratum v u β,
    [(0, rho2 v u)], rho2 v u, ResU.dom_single _ _, BigComp.single _,
    ResU.Le.refl _, ?_⟩
  intro l p hm
  obtain ⟨rfl, rfl⟩ := mem_single hm
  refine ⟨⟨_, rho2_0 v u⟩, ?_, ?_, ?_⟩
  · intro x e
    rw [rho2_0] at e
    have hx : v = x := by injection Option.some.inj e
    cases hx
    refine ⟨?_, ?_⟩
    · rw [rho2_del_0]; exact witU_stratum u _
    · -- `(rebA β).get 0 = imm({β}, v, ρ″/0)`, and `ρ″/0 = witU u`
      rw [rebA_0]
      exact congrArg some (CellU.immOf_congr rfl rfl (rho2_del_0 v u).symm _ _)
  · intro b x χ hb P hw e
    rw [rho2_0] at e
    exact absurd (Option.some.inj e) CellU.ownOf_ne_mutOf
  · intro s x χ h e
    rw [rho2_0] at e
    exact absurd (Option.some.inj e) CellU.ownOf_ne_immOf

end BoCa.DeepReborrow

namespace BoCa.DeepReborrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem plug_var {K : Kont} {a : Expr} {i : Nat} (h : K.plug a = Expr.var i) :
    K = Kont.hole ∧ a = Expr.var i := by
  cases K <;> simp_all [Kont.plug]

theorem head_not_var {μ μ' : Heap} {i : Nat} {e' : Expr} :
    ¬ Head μ (Expr.var i) μ' e' := by intro h; cases h

theorem step1_not_var {μ μ' : Heap} {i : Nat} {e' : Expr} :
    ¬ Step1 μ (Expr.var i) μ' e' := by
  rintro ⟨K, a, a', hplug, -, hhead⟩
  obtain ⟨rfl, rfl⟩ := plug_var hplug.symm
  exact head_not_var hhead

theorem steps_var {μ μ' : Heap} {i : Nat} {e' : Expr}
    (h : Steps μ (Expr.var i) μ' e') : e' = Expr.var i := by
  cases h with
  | refl => rfl
  | more hstep _ => exact absurd hstep step1_not_var

theorem var_ne_val (i : Nat) (x : BoCa.Val) : Expr.var i ≠ Expr.val x := by
  intro h; have : IsVal (Expr.var i) := h ▸ x.2; cases this

theorem hash_empty_of_valid {ρ : WRes} (hv : ResU.Valid ρ) :
    ResU.Hash (PMap.empty) ρ :=
  ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), ρ, compS_empty_left ρ, hv⟩

/-- A bare variable has no `wp` at any valid resource. -/
theorem no_wp_var {i : Nat} (Q : Val → WProp) {ρ : WRes} (hv : ResU.Valid ρ) :
    ¬ wp (Expr.var i) Q ρ := by
  intro hwp
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, x, μ, μ', _, _, _, _, _, _, _, hsteps, _, _, _, _⟩ :=
    hwp PMap.empty (hash_empty_of_valid hv)
  exact var_ne_val i x (steps_var hsteps).symm

/-- `P` of the `↺`-rule instance: the only witness is the deep reborrow. -/
def Pfam : Life → Val → WProp := fun b _ => (fun ρ => ρ = rebA b 𝓋 𝓋)

/-- `Q` of the instance; the wand is vacuous. -/
def Qpost : Val → WProp := fun _ => emp

/-- The LHS of the `↺` rule holds at `comp`. -/
theorem lhs_holds :
    (ptoImm 2 (⊤ : Life) (fun v_ => fresh fun b => reborrow b (Pfam b v_)) ⋆
      (fresh fun b => all fun v_ =>
        Pfam b v_ ─⋆ wp (Expr.var 0) (fun v'' => box b (Qpost v''))))
      (comp ⊤ ⊤ 𝓋 𝓋 𝓋) := by
  refine ⟨ResU.single 2 (cellB ⊤ 𝓋 𝓋 𝓋), ResU.single 0 (cellF ⊤ 𝓋),
    bcell_frame_comp ⊤ ⊤ 𝓋 𝓋 𝓋, ?_, ?_⟩
  · -- conjunct 1: the borrow cell, whose payload reborrows deeply
    refine ⟨LSet.singleton ⊤, 𝓋, rho2 𝓋 𝓋, rho2_stratum 𝓋 𝓋 _, rfl, ?_, le_refl _⟩
    -- `fresh b. ↺b (Pfam b 𝓋)` at `ρ″`
    refine ⟨⊤, fun a ha => ⟨⟨rebA a 𝓋 𝓋, reb_rho2_rebA a 𝓋 𝓋 ha, rfl⟩, ?_⟩⟩
    exact rho2_stratum 𝓋 𝓋 a
  · -- conjunct 2: the shallow view; the wand is vacuous
    refine ⟨⊤, fun a ha => ⟨fun v_ r_a r_b hP hcomp => ?_, ?_⟩⟩
    · -- `hP : r_a = rebA a 𝓋 𝓋`, and `rebA a` is incompatible with the shallow cell
      subst hP
      exact absurd hcomp.1 (noCompat 𝓋 𝓋 ⊤ 𝓋 a)
    · -- Outlives (single 0 (cellF ⊤ 𝓋)) a
      intro k ψ e
      by_cases hk : k = 0
      · subst hk; rw [ResU.single_get_self] at e
        cases Option.some.inj e; exact ha
      · rw [ResU.single_get_ne _ hk] at e; exact absurd e (by simp)

end BoCa.DeepReborrow

namespace BoCa.DeepReborrow
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
variable (α β : Life) (v u w : BoCa.Val)

/-! Theorem 6.150 (↺ rule), literal reading, continued. -/
/-- `[TR]` 6.150's entailment without `RebEscrow`, at `comp`: the LHS holds
(`lhs_holds`) and the RHS does not (`no_wp_var`, `Valid_composite`).  §12.57.
`[about ours: our `↺` row without `RebEscrow`, at one resource our `✓` admits]` -/
theorem wp_reborrow_unreconciled_at_split_view :
    ¬ Entails
        (ptoImm 2 (⊤ : Life) (fun v_ => fresh fun b => reborrow b (Pfam b v_)) ⋆
          (fresh fun b => all fun v_ =>
            Pfam b v_ ─⋆ wp (Expr.var 0) (fun v'' => box b (Qpost v''))))
        (wp (Expr.var 0) Qpost) := by
  intro hent
  exact no_wp_var Qpost (Valid_composite ⊤ ⊤ 𝓋 𝓋 𝓋) (hent _ lhs_holds)

end BoCa.DeepReborrow

end
