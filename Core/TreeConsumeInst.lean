import Core.TreeConsume
import Core.TreeHeap

/-!
# A closed instance of T4c  `[spec §62]`

`twp_lendEnd_after_framed_consume` (T4c, `Core/TreeConsume.lean`) at the #793 configuration, every
hypothesis discharged (`twp_lendEnd_after_framed_consume_inst`). The lender at `wE` holds the lend
cell of `ℓ = 1` and one more copy (`viewRes_dup`), owns the lend's record, and runs alone (the
empty frame, `FEmpty`). The callee is `twp_admits_consume_view`'s run. The continuation `hrest`
is `[ ]`, proved at every expression the callee may end at: a run owning one `own` cell, alone,
with no records, ends at every final state it reaches (`twp_own_any`). Its end world owns the
final memory (`ownWorldT`), built cell by cell by `TWNT.alloc`; `↭` ignores `own` cells
(`updX_compS_own`, `updX_compS_own_back`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

/-- The empty resource is valid. -/
theorem valid_emptyT {K : WCactus} : ResUT.Valid (PMap.empty : TRes K) := by
  obtain ⟨τ, hτ, -⟩ := (lower_emptyT : ResUT.Lower (PMap.empty : TRes K) (fun _ => none))
  exact ⟨τ, hτ⟩

/-- A re-read `own` singleton is itself. -/
theorem rr_single_ownT {K K' : WCactus} {Θ : LocTy} {l : BoCa.Loc} {v : BoCa.Val} {ρ' : TRes K'}
    (h : RR Θ (ResUT.single l (CellUT.ownOf (K := K) v)) ρ') :
    ρ' = ResUT.single l (CellUT.ownOf v) := by
  obtain ⟨ψ', rfl, hr⟩ := RR.of_sng h
  cases hr; rfl

/-- **The world owning a memory with finitely many cells**, at any world's tree, codes and
template choice: reached from `∅` by `TWNT.alloc`, covered, its lowering the memory, and `∅ ↭` it
at every mask (`updX_compS_own`). -/
theorem ownWorldT_of_list (w : TWd) (E : BoCa.Loc → Prop) :
    ∀ (d : List BoCa.Loc) (μ : Heap), (∀ x, μ x ≠ none → x ∈ d) →
      ∃ W : TRes w.K, TWNT w.K w.Θ w.tc W [] [] ∧ ResUT.Lower W μ ∧ CovR (sem w.Θ) w.K W ∧
        UpdX (sem w.Θ) E E (PMap.empty : TRes w.K) W
  | [], μ, hd => by
      have hμ : μ = fun _ => none := by
        funext x
        by_contra h
        exact absurd (hd x h) List.not_mem_nil
      subst hμ
      exact ⟨PMap.empty, TWNT.empty, lower_emptyT, fun _ _ e => by simp at e,
        UpdX.of_rr (WCactus.Ext.refl _) E valid_emptyT RR.empty⟩
  | a :: d, μ, hd => by
      classical
      have hd' : ∀ x, μ.del a x ≠ none → x ∈ d := by
        intro x h
        by_cases hx : x = a
        · subst hx; rw [BoCa.BoLo.Heap.del_same] at h; exact absurd rfl h
        · rw [BoCa.BoLo.Heap.del_other hx] at h
          rcases List.mem_cons.1 (hd x h) with h' | h'
          · exact absurd h' hx
          · exact h'
      obtain ⟨W, hT, hlow, hcov, hu⟩ := ownWorldT_of_list w E d (μ.del a) hd'
      cases hμa : μ a with
      | none =>
          have : μ.del a = μ := by
            funext x
            by_cases hx : x = a
            · subst hx; rw [BoCa.BoLo.Heap.del_same, hμa]
            · rw [BoCa.BoLo.Heap.del_other hx]
          rw [this] at hlow
          exact ⟨W, hT, hlow, hcov, hu⟩
      | some v =>
          have hda : μ.del a a = none := BoCa.BoLo.Heap.del_same _ _
          obtain ⟨σ, hσ, hval⟩ := hlow
          have hσa : σ.get a = none := by
            have := hval a; rw [hda] at this
            revert this; cases σ.get a <;> simp
          have hWa : W.get a = none := get_eq_none_of_flatT hσ hσa
          obtain ⟨W', hW'⟩ := (ResUT.compS_defined_iff W (ResUT.single a (CellUT.ownOf v))).mpr
            (compatS_single_of_get_noneT hWa)
          have hlow' : ResUT.Lower W' ((μ.del a).upd a v) :=
            lower_compS_ownT hW' ⟨σ, hσ, hval⟩ hda
          have hv : ResUT.Valid W := ⟨σ, hσ⟩
          have hv' : ResUT.Valid W' := by obtain ⟨τ, hτ, -⟩ := hlow'; exact ⟨τ, hτ⟩
          have hup : (μ.del a).upd a v = μ := by
            funext x
            by_cases hx : x = a
            · subst hx; rw [BoCa.BoLo.Heap.upd_same, hμa]
            · rw [BoCa.BoLo.Heap.upd_other hx, BoCa.BoLo.Heap.del_other hx]
          rw [hup] at hlow'
          exact ⟨W', TWNT.alloc hT ⟨σ, hσ, hval⟩ hda hW' hv', hlow', covR_compS_own hW' hcov,
            UpdX.trans (WCactus.Ext.refl _) hu (updX_compS_own hW' hv hv' hcov)⟩

/-- The empty frame: a run alone. -/
def FEmpty : TFrame := fun _ ρf => ρf = PMap.empty

theorem FEmpty.mono : FEmpty.Mono := by
  rintro w w' ρ ρ' - hr rfl
  exact RR.of_empty hr

/-- The postcondition every end meets. -/
def QTrue : TPost := fun _ _ _ _ _ _ => True

/-- **A run owning one `own` cell, alone and with no records, ends at every final state it
reaches**, whatever the expression. Its start world holds that cell only, so it has no records
proper (`leInv_view`: a record's location is in `ag` of the world, and `ag(ℓ ↦ own(v)) = ∅`) and
no tagged records (`TaggedT`). The end world owns the final memory (`ownWorldT_of_list`); `↭`
ignores `own` cells. -/
theorem twp_own_any (k : Nat) (w : TWd) (ls : List (SRecT w.K)) (t : Expr) (l : BoCa.Loc)
    (v : BoCa.Val) :
    twp (ℍ := ℍ) FEmpty QTrue k w ls [] t (ResUT.single l (CellUT.ownOf v)) := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hh hc hS hR hI hfd j μ' e' hj hrun hfin
  have hρf : ρf = PMap.empty := hFρ
  subst hρf
  obtain rfl := rr_single_ownT hr
  obtain rfl : fρ = ResUT.single l (CellUT.ownOf v) :=
    ResUT.CompS.functional hc (ResUT.CompS.comm (ResUT.compS_empty_right _))
  cases hO
  have hps : ps = [] := by
    cases ps with
    | nil => rfl
    | cons q ps' =>
        obtain ⟨ψ, eψ⟩ := leInv_view hR.1 List.mem_cons_self PMap.empty (AgWT.single_own l v)
        simp at eψ
  subst hps
  have hpsF : psF = [] := by
    cases psF with
    | nil => rfl
    | cons q _ => exact absurd ((hS.1 q).mpr (Or.inr List.mem_cons_self)) (by simp)
  subst hpsF
  have hls : ls₀ = [] := by
    cases ls₀ with
    | nil => rfl
    | cons x _ =>
        obtain ⟨p, hp, -⟩ := hR.2 x List.mem_cons_self
        simp at hp
  subst hls
  obtain ⟨d, hd⟩ := fd_stepsN hrun hfd
  obtain ⟨W, hT, hlow, hcov, hu⟩ :=
    ownWorldT_of_list w₀ (recMask ([] : List (FrameRecT w₀.K))) d μ' hd
  have hv : ResUT.Valid W := by obtain ⟨τ, hτ, -⟩ := hlow; exact ⟨τ, hτ⟩
  have hback : UpdX (sem w₀.Θ) (recMask ([] : List (FrameRecT w₀.K)))
      (recMask ([] : List (FrameRecT w₀.K))) (ResUT.single l (CellUT.ownOf v))
      (PMap.empty : TRes w₀.K) :=
    updX_compS_own_back (ResUT.CompS.comm (ResUT.compS_empty_right _)) valid_emptyT
      (ResUT.valid_single_own l v) (fun _ _ e => by simp at e)
  exact ⟨w₀, PMap.empty, W, W, [], [], [], [], TWd.Ext.refl _ _, RR.empty, List.Forall₂.nil,
    ResUT.hash_empty_right hv, ResUT.CompS.comm (ResUT.compS_empty_right W),
    ⟨fun p => by simp, fun p hp => by cases hp⟩, ⟨hT, fun _ hx => by simp at hx⟩,
    ⟨hcov, hlow⟩, trivial, (UpdX.trans (WCactus.Ext.refl _) hback hu).toA hv,
    noneAt_empty _, InvKeptA.refl _ _ _⟩

/-- **T4c, closed** (`twp_lendEnd_after_framed_consume` at the #793 configuration, every
hypothesis discharged): at `wE`, the lender holds the lend cell of `ℓ = 1` and one more copy
(`viewRes_dup`), owns the lend's record and runs alone. The callee, run from the copy alone, gives
it up (`twp_admits_consume_view`'s run); the lend ends; the continuation `[ ]` is
`twp_own_any` at the own cell the lend hands back, at every expression the callee may end at. -/
theorem twp_lendEnd_after_framed_consume_inst (n : Nat) :
    twp (ℍ := ℍ) FEmpty QTrue n wE lsOne [lendRec 1] (Kont.plug .hole (.val .unit))
      (viewRes (lfE 1) 1) :=
  twp_lendEnd_after_framed_consume (F := FEmpty) FEmpty.mono (Q := QTrue) Kont.hole
    (O := []) (Z := PMap.empty) (ρ₁ := viewRes (lfE 1) 1) (ρ₂ := viewRes (lfE 1) 1) (l := 1)
    (α := lfE 1)
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) (viewRes_dup _ _)
    (fun x ψ e => by
      obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
      exact Cov.immOf_iff.mpr fun m ψ h => by simp at h)
    (fun r hr => by cases hr) valid_emptyT (noneAt_empty _)
    (fun _ _ h => by rw [show _ = _ from h]; exact noneAt_empty _) (by simp)
    (twp_here (fun μ => LogRel.Core.final_val μ Val.unit) fun _ _ _ _ _ hr _ hO => by
      cases hO
      exact ⟨rfl, RR.of_empty hr⟩)
    (fun k w' ls' O' t Z' ρ' _ hZr hOr hρ' _ => by
      obtain rfl := RR.of_empty hZr
      cases hOr
      obtain rfl : ρ' = ResUT.single 1 (CellUT.ownOf BoCa.Val.unit) :=
        ResUT.CompS.functional hρ' (ResUT.CompS.comm (ResUT.compS_empty_right _))
      exact twp_own_any k w' ls' (Kont.plug .hole t) 1 BoCa.Val.unit)

/-- **The instance is not vacuous**: at the start configuration of `twp_refuses_lendEnd_live_copy`
(the lend of `ℓ = 1` opened from the empty world, `recWInv_lendStep`), run alone, the lender's run
of `()` reaches an end `EndT` admits, at every host. -/
theorem twp_lendEnd_after_framed_consume_inst_ends (ℍ' : BoCa.Host) [BoCa.HostIs ℍ'] :
    EndT QTrue 0 wE (viewRes (lfE 1) 1) [lendRec 1] PMap.empty []
      (BoCa.BoLo.Heap.upd (fun _ => none : Heap) 1 BoCa.Val.unit) (.val .unit) := by
  obtain ⟨W₁, hW₁, hR₁, hI₁⟩ := recWInv_lendStep (lfE 1) (recInv_empty chainP)
    (winv_empty chainP) (l := 1) rfl
  obtain rfl : W₁ = viewRes (lfE 1) 1 :=
    ResUT.CompS.functional (ResUT.CompS.comm hW₁) (ResUT.compS_empty_right _)
  have hfd : FinDom (BoCa.BoLo.Heap.upd (fun _ => none : Heap) 1 BoCa.Val.unit) :=
    ⟨[1], fun l hl => by
      by_cases e : l = 1
      · simp [e]
      · exact absurd (BoCa.BoLo.Heap.upd_other e) hl⟩
  have hS : SplitT [lendRec (K := wE.K) 1] [lendRec 1] [] :=
    ⟨fun p => by simp, fun p _ q hq => by simp at hq⟩
  have hc : ResUT.CompS (PMap.empty : TRes wE.K) (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) :=
    ResUT.CompS.comm (ResUT.compS_empty_right _)
  exact twp_lendEnd_after_framed_consume_inst (ℍ := ℍ') 1 wE (viewRes (lfE 1) 1) PMap.empty
    (viewRes (lfE 1) 1) lsOne [lendRec 1] [lendRec 1] [] _ (TWd.Ext.refl _ _) rr_view
    (.cons ⟨lendRec_rr 1, rfl⟩ .nil) (.cons (lendRec_rr 1) .nil) rfl
    ⟨G.Compat.of_disjoint (fun _ => Or.inl rfl), _, hc, hI₁.valid⟩ hc hS hR₁ hI₁ hfd 0 _ _
    (by omega) (.refl _ _) (LogRel.Core.final_val _ Val.unit)

end BoCa.Fig16.Tree.Wp

end
