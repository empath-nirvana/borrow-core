import Core.TreeBorrowEdges
import Core.TreeHandle

/-!
# Consuming a copy of a shared view at `twp`  `[spec §62]`

Can a run give up one copy of a shared `imm` view, ending without it and without returning it?
`twp` has no garbage `ρ⁺` (departure D4: row 5.33's `ρ ↭ ρ′ ● ρ⁺` read as `ρ ↭ ρ′`). `EndT`'s `↭`
is `UpdA` (`docs/new-core/scope-806.md`, design (b) along the walks): an unmasked `imm` cell of
the start is kept, or absorbed by the end world. Where a copy can be held elsewhere:

* **The run holds another copy: admitted, at no cost** (`twp_consume_view_held`). An `imm` copy
  composes with itself to itself (`viewRes_dup`), so the run's resource with the extra copy is the
  resource without it (`consume_view_held`).

* **Another part holds a copy: admitted** (T1, `twp_consume_view_framed`), at every frame
  condition implying that the frame holds a copy (`HoldsCopy`; it gives the flattening-level
  `HoldsView` of the scope, `HoldsCopy.holdsView`). The world is unchanged
  (`consume_view_world`), and the given-up copy is absorbed by the end world. A callee proved at
  its own copy (T2, `twp_frame_callee_consume`) and a spawned task (T3, `twp_child_consume`) are
  T1 at their frame conditions strengthened by `HoldsCopy` (design choice D-1). The #793
  configuration is admitted (`twp_admits_consume_view`).

* **No other copy: refused** (`twp_refuses_last_copy`, without reading `↭`): the end world is
  empty and fails `RecInv` (`leInv_view`).

**The hardest case (T4).** A given-up copy takes nothing with it (T4a): T1 runs from `Z` in the
same world. A lend does not end while another part holds a live copy (T4b,
`twp_refuses_lendEnd_live_copy`, without reading `↭`). Once every live copy is back, a lend ends
after a callee gave its copy up under the lender's frame, by `twp_lendEnd` as it stands (T4c,
`twp_lendEnd_after_framed_consume`).

A copy kept in the world as garbage, as row 5.33's `ρ⁺` is kept, sits in the lender's frame at its
end and fails `twp_lendEnd`'s frame condition (`not_noneAt_view`). A `mut` cell has no second copy
(`not_compS_single_self`): no part absorbs it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Kont)

section Carrier
variable {K : WCactus}

/-! ### The carrier: copies of a view, and cells with one holder -/

/-- The flattening of a lone view is the view. -/
theorem flat_viewRes {β : Life} {l : BoCa.Loc} {σ : TRes K} (h : ResUT.Flat (viewRes β l) σ) :
    σ.get l = some (viewCell β) := by
  obtain ⟨τ, hτ, hc⟩ := flat_compS_view (ResUT.CompS.comm (ResUT.compS_empty_right (viewRes β l)))
    flat_empty (ρ := PMap.empty) (σ := PMap.empty) (by simp)
  obtain rfl := ResUT.Flat.functional h hτ
  obtain rfl := ResUT.CompS.functional hc
    (ResUT.CompS.comm (ResUT.compS_empty_right (viewRes β l)))
  exact ResUT.single_get_self _ _

/-- The flattening of the empty resource is empty. -/
theorem flat_empty_get {σ : TRes K} (h : ResUT.Flat (PMap.empty : TRes K) σ) (l : BoCa.Loc) :
    σ.get l = none := by
  obtain rfl := ResUT.Flat.functional h flat_empty
  simp

/-- **A resource holding a copy of a view absorbs another.** -/
theorem absorb_view {Y ρf : TRes K} {β : Life} {l : BoCa.Loc}
    (hY : ResUT.CompS Y (viewRes β l) ρf) : ResUT.CompS ρf (viewRes β l) ρf := by
  obtain ⟨x, hx, hxv⟩ := (ResUT.CompS.assoc Y (viewRes β l) (viewRes β l) ρf).mp
    ⟨viewRes β l, viewRes_dup β l, hY⟩
  obtain rfl := ResUT.CompS.functional hx hY
  exact hxv

/-- **Consuming a copy the frame also holds leaves the world as it was.** The frame `ρf` holds a
copy of the view (`Y ● v`), the run holds `Z ● v`, the world is `ρf ● (Z ● v)`; then the world is
`ρf ● Z`. -/
theorem consume_view_world {Y Z ρf ρ₀ fρ : TRes K} {β : Life} {l : BoCa.Loc}
    (hY : ResUT.CompS Y (viewRes β l) ρf) (hZ : ResUT.CompS Z (viewRes β l) ρ₀)
    (hc : ResUT.CompS ρf ρ₀ fρ) : ResUT.CompS ρf Z fρ := by
  obtain ⟨X, hX, hXv⟩ := (ResUT.CompS.assoc ρf Z (viewRes β l) fρ).mp ⟨ρ₀, hZ, hc⟩
  obtain ⟨y, hy, hZy⟩ := (ResUT.CompS.assoc Z ρf (viewRes β l) fρ).mpr
    ⟨X, ResUT.CompS.comm hX, hXv⟩
  obtain rfl := ResUT.CompS.functional hy (absorb_view hY)
  exact ResUT.CompS.comm hZy

/-- **Consuming a copy the run also holds is the identity**: a resource holding a copy of a view,
beside another copy, is itself. -/
theorem consume_view_held {Y A ρ : TRes K} {β : Life} {l : BoCa.Loc}
    (hY : ResUT.CompS Y (viewRes β l) A) (hA : ResUT.CompS A (viewRes β l) ρ) : ρ = A :=
  ResUT.CompS.functional hA (absorb_view hY)

/-- **A cell other than an `imm` cell has one holder**: two resources holding it at one
location do not compose. -/
theorem not_compS_single_self {l : BoCa.Loc} {ψ : TCell K} (hk : ψ.kind ≠ Kind.imm)
    {x : TRes K} : ¬ ResUT.CompS (ResUT.single l ψ) (ResUT.single l ψ) x := by
  intro h
  rcases ResUT.Comp.get h l with ⟨f, -, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
  · simp at f
  · simp at f
  · simp at f
  · rw [ResUT.single_get_self] at f₁
    cases f₁
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, -, -⟩ := hC
    exact hk (by rw [e₁]; rfl)

/-- **A frame holding a copy of the view fails `twp_lendEnd`'s frame condition** (`hF`, nothing at
`ℓ`). A copy kept in the world as garbage beside the lender, as row 5.33's `ρ⁺` is kept, is such a
frame for the lender's end. -/
theorem not_noneAt_view {β : Life} {l : BoCa.Loc} : ¬ NoneAt (· = l) (viewRes (K := K) β l) := by
  intro h
  obtain ⟨σ, hσ⟩ := valid_view (K := K) β l
  have := h σ hσ l rfl
  rw [flat_viewRes hσ] at this
  cases this

/-- **An open record's lent location is in the world**: the last copy of a lend cell cannot leave
a world meeting `RecInv` while the record is a record proper. -/
theorem recInv_lend_holds_view {w : TWd} {W : TRes w.K} {ps : List (FrameRecT w.K)}
    {ls : List (SRecT w.K)} (hR : RecInv w W ps ls) {l : BoCa.Loc} (hp : lendRec l ∈ ps)
    (hv : ResUT.Valid W) : ∃ a ψ, AgWT W a ∧ a.get l = some ψ := by
  obtain ⟨a, ha⟩ := agW_of_valid hv
  obtain ⟨ψ, eψ⟩ := leInv_view hR.1 hp a ha
  exact ⟨a, ψ, ha, eψ⟩

end Carrier

/-! ### `↭` keeps an unmasked `imm` cell -/

/-- **`↭` refuses an end that has given up an unmasked view.** A run from a lone view to the empty
resource, the view's location masked on neither side, is not related by `UpdX`. -/
theorem updX_consume_view_false {K K' : WCactus} {Θ : LocTy} {E E' : BoCa.Loc → Prop} {β : Life}
    {l : BoCa.Loc} (hE : ¬ E l)
    (h : UpdX Θ E E' (viewRes (K := K) β l) (PMap.empty : TRes K')) : False := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  obtain ⟨-, ψ', e', -⟩ := (hx l).1 _ (flat_viewRes hσ) (by simp [viewCell, CellUT.kind_immOf])
    hE
  rw [flat_empty_get hσ'] at e'
  cases e'

/-! ### A copy the run also holds -/

/-- **`twp` admits consuming a copy of a view the run holds another copy of**, under every frame
condition and postcondition: the two resources are one (`consume_view_held`). No lend's end reads
the consumed copy, so `twp_lendEnd` is used as it stands: a later end still needs every copy held
anywhere back. -/
theorem twp_consume_view_held {F : TFrame} {Q : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {Y A ρ : TRes w.K} {β : Life}
    {l : BoCa.Loc} (hY : ResUT.CompS Y (viewRes β l) A) (hA : ResUT.CompS A (viewRes β l) ρ)
    (h : twp (ℍ := ℍ) F Q n w ls O e A) : twp (ℍ := ℍ) F Q n w ls O e ρ := by
  rw [consume_view_held hY hA]; exact h

/-! ### The configuration -/

/-- The run's postcondition: it ends owning no record and holding nothing. -/
def QGiveUp : TPost := fun _ _ _ O _ ρ => O = [] ∧ ρ = PMap.empty

/-- The tagged list of the one lend. -/
abbrev lsOne : List (SRecT wE.K) := [(lendRec 1, lfE 1)]

/-! ### A copy another part holds: the run gives its copy up (T1) -/

/-- **The frame holds a copy of the view**: `ρf = Y ● v`. A frame condition implying it is what a
consume at `twp` reads: someone outside the run holds the borrow. -/
def HoldsCopy {K : WCactus} (β : Life) (l : BoCa.Loc) (ρf : TRes K) : Prop :=
  ∃ Y, ResUT.CompS Y (viewRes β l) ρf

/-- A frame holding a copy absorbs the view at its flattening: `HoldsCopy` gives `HoldsView`. -/
theorem HoldsCopy.holdsView {K : WCactus} {Θ : LocTy} {β : Life} {l : BoCa.Loc} {ρf : TRes K}
    (h : HoldsCopy β l ρf) (hv : ResUT.Valid ρf) :
    ∃ τ χ, ResUT.Flat ρf τ ∧ τ.get l = some χ ∧ CellAbs Θ (viewCell (K := K) β) χ := by
  obtain ⟨Y, hY⟩ := h
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨σY, σv, -, hσv, hcomp⟩ := BoLo.flat_compR hY hτ
  obtain ⟨χ, eχ, hle⟩ := compR_get_imm hcomp (Or.inr (flat_viewRes hσv))
    (CellUT.kind_immOf _ _ _ _)
  obtain ⟨k₁, k₂, e, w, s, t, hs, ht, hst⟩ := hle
  exact ⟨τ, χ, hτ, eχ, k₁, k₂, e, by rw [w]; exact RR.empty, s, t, hs, ht, hst⟩

/-- A view holds no `mut` cell, at any depth. -/
theorem viewRes_no_mut {K : WCactus} {β : Life} {l y : BoCa.Loc} {φ : TCell K}
    (h : CellAt (viewRes β l) y φ) : φ.kind ≠ Kind.mut := by
  cases h with
  | top e =>
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      simp [viewCell, CellUT.kind_immOf]
  | nest e h' =>
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      cases h' with
      | top e' => simp [viewCell, CellUT.wit_immOf] at e'
      | nest e' _ => simp [viewCell, CellUT.wit_immOf] at e'

/-- Every re-typing agrees on a view. -/
theorem agreeOn_view {K : WCactus} (Θ Θ' : CodeTy) (β : Life) (l : BoCa.Loc) :
    AgreeOn Θ Θ' (viewRes (K := K) β l) := by
  intro y hy
  cases hy with
  | top e =>
      obtain ⟨-, h⟩ := ResUT.single_get_eq_some e
      simp [viewCell, CellUT.immOf] at h
  | deep e h =>
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      cases h with
      | top e' => simp [viewCell, CellUT.wit_immOf] at e'
      | deep e' _ => simp [viewCell, CellUT.wit_immOf] at e'

/-- **The view given up, the rest kept, at one world**: `UpdA` from `Z ● v` to `Z` beside the
world `ρf ● Z`, the world holding a copy. `UpdA.frame` with the run giving `v` up to the world
(absorbed, `compR_get_imm`) and `Z` framed. -/
theorem updA_consume_view {K : WCactus} {Θ : LocTy} {E : BoCa.Loc → Prop} {Z ρ ρf X fρ : TRes K}
    {β : Life} {l : BoCa.Loc} (hZ : ResUT.CompS Z (viewRes β l) ρ) (hcov : CovR Θ K Z)
    (hv : ResUT.Valid ρ) (hXv : ResUT.CompS X (viewRes β l) fρ)
    (hw : ResUT.CompS ρf Z fρ) (hfv : ResUT.Valid fρ) {W : TRes K} (hW : MutOne W)
    (hs : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ)
    (hs' : ∀ y φ, CellAt Z y φ → φ.kind = Kind.mut → CellAt W y φ) :
    UpdA Θ E E ρ Z fρ := by
  have hrun : UpdA Θ E E (viewRes (K := K) β l) (PMap.empty : TRes K) fρ := by
    obtain ⟨σ, hσ⟩ := valid_view (K := K) β l
    obtain ⟨τw, hτw⟩ := hfv
    obtain ⟨σX, σv, -, hσv, hcomp⟩ := BoLo.flat_compR hXv hτw
    obtain rfl := ResUT.Flat.functional hσ hσv
    refine ⟨σ, PMap.empty, τw, hσ, flat_empty, hτw, fun x => ⟨fun ψ e hk hE => ?_,
      fun ψ' e => by simp at e⟩⟩
    obtain ⟨σ₀, hσ₀, hc₀⟩ := flat_compS_view (ResUT.CompS.comm (ResUT.compS_empty_right
      (viewRes (K := K) β l))) flat_empty (ρ := PMap.empty) (σ := PMap.empty) (by simp)
    obtain rfl := ResUT.Flat.functional hσ hσ₀
    obtain rfl := ResUT.CompS.functional hc₀
      (ResUT.CompS.comm (ResUT.compS_empty_right (viewRes β l)))
    have hxl : x = l := by
      by_contra hne
      rw [viewRes, ResUT.single_get_ne _ hne] at e
      cases e
    subst hxl
    rw [viewRes, ResUT.single_get_self] at e
    cases e
    obtain ⟨χ, eχ, hle⟩ := compR_get_imm hcomp (Or.inr (ResUT.single_get_self _ _))
      (CellUT.kind_immOf _ _ _ _)
    obtain ⟨k₁, k₂, e', w', s, t, hs₀, ht, hst⟩ := hle
    exact ⟨hE, Or.inr (Or.inl ⟨χ, eχ, k₁, k₂, e', by rw [w']; exact RR.empty, s, t, hs₀, ht,
      hst⟩)⟩
  exact UpdA.frame (WCactus.Ext.refl K) hrun (RR.refl hcov) (ResUT.CompS.comm hZ)
    (ResUT.CompS.comm (ResUT.compS_empty_right Z)) hv hw
    (NoneAt.of_false (fun x hx => by unfold MaskDiff at hx; tauto) _) hW hs hW hs'

/-- **(T1) A run gives up a copy of a view another part holds** (design (b),
`docs/new-core/scope-806.md`): from `Z ● v`, under every frame meeting `F`, when every such frame
holds a copy (`HoldsCopy`), `twp` from `Z` gives `twp` from `Z ● v`. The world is unchanged
(`consume_view_world`): the run continues from `Z` beside the same frame in the same world. The
end relates `Z ● v` to the end along the walks: `v` given up to the world, `Z` framed
(`updA_consume_view`), then the run from `Z` (`UpdA.trans`, the world growing by `UpdA.grow`).
`hcov`, as in `twp_frame`: the resource is covered at its world, so that its parts have
re-readings at every extension. -/
theorem twp_consume_view_framed {F : TFrame} {Q : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {Z ρ : TRes w.K} {β : Life}
    {l : BoCa.Loc} (hZ : ResUT.CompS Z (viewRes β l) ρ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hF : ∀ w' ρf, F w' ρf → HoldsCopy β l ρf) (h : twp (ℍ := ℍ) F Q n w ls O e Z) :
    twp (ℍ := ℍ) F Q n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hFρ hf hc hS hR hI hfd j μ' e' hj hrun hfin
  obtain ⟨Z₀, v₀, hZr, hvr, hZ₀⟩ := RR.split_retype hE.1 hZ hcov hE.2 hr
  obtain rfl := rr_view_eq hvr
  obtain ⟨Y, hY⟩ := hF w₀ ρf hFρ
  have hcZ : ResUT.CompS ρf Z₀ fρ := consume_view_world hY hZ₀ hc
  obtain ⟨X, hX, hXv⟩ := (ResUT.CompS.assoc ρf Z₀ (viewRes β l) fρ).mp ⟨ρ₀, hZ₀, hc⟩
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    h w₀ Z₀ ρf fρ ls₀ O₀ ps psF μ (hE.of_compS_left hZ) hZr hl hO hFρ (hash_of_inv hcZ hI) hcZ
      hS hR hI hfd j μ' e' hj hrun hfin
  have hsub₀ : ∀ y φ, CellAt ρ₀ y φ → φ.kind = Kind.mut → CellAt fρ y φ :=
    fun _ _ h k => h.of_compS_right hc (kind_mut_ne_imm k)
  have hsubZ : ∀ y φ, CellAt Z₀ y φ → φ.kind = Kind.mut → CellAt fρ y φ :=
    fun _ _ h k => h.of_compS_right hcZ (kind_mut_ne_imm k)
  have hstep : UpdA (sem w₀.Θ) (recMask O₀) (recMask O₀) ρ₀ Z₀ fρ :=
    updA_consume_view hZ₀ (cov_of_comp hcZ hI) (cov_valid hc hI) hXv hcZ hI.valid
      (TWNT.mutOne hR.1) hsub₀ hsubZ
  refine ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈,
    UpdA.trans (WCactus.Ext.refl _) g₀.1 hstep g₉ (TWNT.mutOne hR.1) hsub₀ (TWNT.mutOne hR.1)
      hsubZ (recMaskClosed w₀ fρ ρf Z₀ ps O₀ psF ls₀ hR hcZ hS) (UpdA.grow g₀.1 g₉ g₁ hcZ g₄ g₁₀),
    g₁₀, g₁₁.frame hZ₀ (TWNT.mutOne hR.1) (fun _ _ h k => absurd k (viewRes_no_mut h))
      (agreeOn_view _ _ β l)⟩

/-- **(T2) A callee proved at its own copy gives it up**, the caller's copy outside its run:
`twp_consume_view_framed` at the callee's frame condition `F₁`. A caller framing a copy around
the callee (`twp_frame`, `R` holding `Y ● v`) discharges `hF₁` through `twp_frame`'s obligation:
`ρf ● (Y₀ ● v)` holds a copy (`holdsCopy_compS`). -/
theorem twp_frame_callee_consume {F₁ : TFrame} {Q : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {β : Life} {l : BoCa.Loc}
    (hF₁ : ∀ w' ρf, F₁ w' ρf → HoldsCopy β l ρf)
    (h : twp (ℍ := ℍ) F₁ Q n w ls O e PMap.empty) :
    twp (ℍ := ℍ) F₁ Q n w ls O e (viewRes β l) :=
  twp_consume_view_framed (ResUT.CompS.comm (ResUT.compS_empty_right _))
    (fun x ψ e => by
      obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
      exact Cov.immOf_iff.mpr fun m ψ h => by simp at h) hF₁ h

/-- A part holding a copy makes the composite hold one. -/
theorem holdsCopy_compS {K : WCactus} {β : Life} {l : BoCa.Loc} {a b c : TRes K}
    (hb : HoldsCopy β l b) (hc : ResUT.CompS a b c) : HoldsCopy β l c := by
  obtain ⟨Y, hY⟩ := hb
  obtain ⟨x, hx, hxv⟩ := (ResUT.CompS.assoc a Y (viewRes β l) c).mp ⟨b, hY, hc⟩
  exact ⟨x, hxv⟩

/-- **(T3) A spawned task gives up a copy its parent holds**: `twp_consume_view_framed` at the
child's frame condition, `fdMask` at the empty mask (`enSpawn`'s `Fe`) strengthened by
`HoldsCopy` (design choice D-1). -/
theorem twp_child_consume {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {β : Life} {l : BoCa.Loc}
    (h : twp (ℍ := ℍ) (fun w' ρf => fdMask (fun _ => False) w' ρf ∧ HoldsCopy β l ρf) Q n w ls O
      e PMap.empty) :
    twp (ℍ := ℍ) (fun w' ρf => fdMask (fun _ => False) w' ρf ∧ HoldsCopy β l ρf) Q n w ls O e
      (viewRes β l) :=
  twp_frame_callee_consume (fun _ _ h => h.2) h

/-- **The #793 callee configuration is admitted**: at the chain tree with the lend of `ℓ = 1`
open, the frame holding a copy and owning the record, the run gives its copy up and ends owning
nothing and holding nothing (`QGiveUp`), at the trivial frame condition strengthened by
`HoldsCopy`. -/
theorem twp_admits_consume_view (n : Nat) :
    twp (ℍ := ℍ) (fun _ ρf => HoldsCopy (lfE 1) 1 ρf) QGiveUp n wE lsOne [] (.val .unit)
      (viewRes (lfE 1) 1) :=
  twp_frame_callee_consume (fun _ _ h => h)
    (twp_here (fun μ => LogRel.Core.final_val μ Val.unit) fun _ _ _ _ _ hr _ hO => by
      cases hO
      exact ⟨rfl, RR.of_empty hr⟩)

/-- The configuration's frame meets the admitted condition. -/
theorem holdsCopy_view : HoldsCopy (K := wE.K) (lfE 1) 1 (viewRes (lfE 1) 1) :=
  ⟨_, viewRes_dup _ _⟩

/-! ### The last copy, and a lend's end while a copy is held -/

/-- **The last copy cannot be consumed, whatever `↭` says**: the frame owns the record and holds
nothing, the run holds the only copy. The end world is empty and fails `RecInv` (`leInv_view`).
`EndT`'s `↭` clause is not read. -/
theorem twp_refuses_last_copy (F : TFrame) (hF : F wE PMap.empty) :
    ¬ twp (ℍ := ℍ) F QGiveUp 1 wE lsOne [] (.val .unit) (viewRes (lfE 1) 1) := by
  intro h
  obtain ⟨W₁, hW₁, hR₁, hI₁⟩ := recWInv_lendStep (lfE 1) (recInv_empty chainP)
    (winv_empty chainP) (l := 1) rfl
  obtain rfl : W₁ = viewRes (lfE 1) 1 :=
    ResUT.CompS.functional (ResUT.CompS.comm hW₁) (ResUT.compS_empty_right _)
  have hc : ResUT.CompS (PMap.empty : TRes wE.K) (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) :=
    ResUT.CompS.comm (ResUT.compS_empty_right _)
  have hfd : FinDom (BoCa.BoLo.Heap.upd (fun _ => none : Heap) 1 BoCa.Val.unit) :=
    ⟨[1], fun l hl => by
      by_cases e : l = 1
      · simp [e]
      · exact absurd (BoCa.BoLo.Heap.upd_other e) hl⟩
  have hS : SplitT [lendRec (K := wE.K) 1] [] [lendRec 1] :=
    ⟨fun p => by simp, fun p hp => by simp at hp⟩
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, hrf, hpsF, -, hc', hS', hR', -, ⟨-, hρ'⟩,
      -, -, -⟩ :=
    h wE (viewRes (lfE 1) 1) PMap.empty (viewRes (lfE 1) 1) lsOne [] [lendRec 1] [lendRec 1] _
      (TWd.Ext.refl _ _) rr_view (.cons ⟨lendRec_rr 1, rfl⟩ .nil) .nil hF
      ⟨hc.1, _, hc, hI₁.valid⟩ hc hS hR₁ hI₁ hfd 0 _ _ (by omega) (.refl _ _)
      (LogRel.Core.final_val _ Val.unit)
  subst hρ'
  obtain rfl := RR.of_empty hrf
  obtain rfl := ResUT.CompS.functional hc' (ResUT.compS_empty_right _)
  obtain _ | ⟨hpp, -⟩ := hpsF
  rename_i p' _
  have hp' : p' ∈ ps' := (hS'.1 p').mpr (Or.inr List.mem_cons_self)
  obtain ⟨ψ, eψ⟩ := leInv_view hR'.1 hp' PMap.empty agW_empty
  simp at eψ

/-- The lender's postcondition: it ends holding `ℓ ↦ own(())`. -/
def QOwnBack : TPost := fun _ _ _ _ _ ρ => ρ = ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)

/-- **A lend does not end while another part holds a live copy**: the lender holds the lend cell
and owns the record, the frame holds a copy; no run ends holding `ℓ ↦ own(())`. The end world
would compose the frame's copy with `own` at `ℓ`. `EndT`'s `↭` clause is not read (T4b). -/
theorem twp_refuses_lendEnd_live_copy (F : TFrame) (hF : F wE (viewRes (lfE 1) 1)) :
    ¬ twp (ℍ := ℍ) F QOwnBack 1 wE lsOne [lendRec 1] (.val .unit) (viewRes (lfE 1) 1) := by
  intro h
  obtain ⟨W₁, hW₁, hR₁, hI₁⟩ := recWInv_lendStep (lfE 1) (recInv_empty chainP)
    (winv_empty chainP) (l := 1) rfl
  obtain rfl : W₁ = viewRes (lfE 1) 1 :=
    ResUT.CompS.functional (ResUT.CompS.comm hW₁) (ResUT.compS_empty_right _)
  have hdup := viewRes_dup (K := wE.K) (lfE 1) 1
  have hfd : FinDom (BoCa.BoLo.Heap.upd (fun _ => none : Heap) 1 BoCa.Val.unit) :=
    ⟨[1], fun l hl => by
      by_cases e : l = 1
      · simp [e]
      · exact absurd (BoCa.BoLo.Heap.upd_other e) hl⟩
  have hS : SplitT [lendRec (K := wE.K) 1] [lendRec 1] [] :=
    ⟨fun p => by simp, fun p _ q hq => by simp at hq⟩
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, hrf, -, -, hc', -, -, -, hρ', -, -, -⟩ :=
    h wE (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) lsOne [lendRec 1]
      [lendRec 1] [] _ (TWd.Ext.refl _ _) rr_view (.cons ⟨lendRec_rr 1, rfl⟩ .nil)
      (.cons (lendRec_rr 1) .nil) hF ⟨hdup.1, _, hdup, hI₁.valid⟩ hdup hS hR₁ hI₁ hfd 0 _ _
      (by omega) (.refl _ _) (LogRel.Core.final_val _ Val.unit)
  have hρ'' : ρ' = ResUT.single 1 (CellUT.ownOf BoCa.Val.unit) := hρ'
  subst hρ''
  obtain rfl := rr_view_eq hrf
  rcases ResUT.Comp.get hc' 1 with ⟨f, -, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
      ⟨χ₁, χ₂, χ, -, f₂, -, hC⟩
  · simp [viewRes] at f
  · simp at f
  · simp [viewRes] at f
  · rw [ResUT.single_get_self] at f₂
    cases f₂
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, -, e₂, -⟩ := hC
    exact absurd (congrArg CellUT.kind e₂) (by simp [CellUT.ownOf, CellUT.kind, CellUT.immOf])

/-- The run's postcondition when it keeps its copy: it ends owning no record and holding the view. -/
def QKeep : TPost := fun _ w _ O _ ρ => O = [] ∧ ρ = viewRes (K := w.K) (lfE 1) 1

/-- **The same run keeping its copy is admitted**, at every frame condition and index: the
refusal above is the consume, not the configuration. -/
theorem twp_admits_keep_view (F : TFrame) (n : Nat) :
    twp (ℍ := ℍ) F QKeep n wE lsOne [] (.val .unit) (viewRes (lfE 1) 1) :=
  twp_here (fun μ => LogRel.Core.final_val μ Val.unit) fun _ _ _ _ _ hr _ hO => by
    cases hO
    exact ⟨rfl, rr_view_eq hr⟩

/-! ### An ordinary call, a lend's end, a spawned task -/

/-- **A callee consuming its copy under `twp_bind`, the caller holding another.** `twp_bind` hands
the callee's run `e` the whole resource `ρ`: the caller's continuation is the run's postcondition,
not its frame, so the caller's copy (in `A`) is in the callee's run beside the callee's, and the
consume is `twp_consume_view_held`. Here the callee's body after its consume is the value `()`, and
the continuation `K[()]` runs from `A` (re-read to wherever the callee ends, `twp_kripke`). -/
theorem twp_bind_callee_consume {F : TFrame} (hFm : F.Mono) {Q : TPost} (K : Kont) {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {Y A ρ : TRes w.K} {β : Life}
    {l : BoCa.Loc} (hY : ResUT.CompS Y (viewRes β l) A) (hA : ResUT.CompS A (viewRes β l) ρ)
    (hK : twp (ℍ := ℍ) F Q n w ls O (K.plug (.val .unit)) A) :
    twp (ℍ := ℍ) F Q n w ls O (K.plug (.val .unit)) ρ :=
  twp_bind hFm K (twp_consume_view_held hY hA
    (twp_here (fun μ => LogRel.Core.final_val μ Val.unit)
      fun _ _ _ _ hE hr hl hO => twp_kripke hE hr hl hO hK))

/-- **A lend's end after the callback consumed one of two copies it held.** The lender holds the
lend cell beside `Z` (`ρ₁`) and one more copy (`ρ₂ = ρ₁ ● v`); it consumes the extra copy
(`twp_consume_view_held`) and ends the lend (`twp_lendEnd`, as it stands). Nothing of the consumed
copy is left for the end's frame condition to meet. -/
theorem twp_lendEnd_after_consume {F : TFrame} {Q : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {Z ρ ρ₁ ρ₂ : TRes w.K}
    {l : BoCa.Loc} {α : Life}
    (hρ₁ : ResUT.CompS Z (viewRes α l) ρ₁) (hρ₂ : ResUT.CompS ρ₁ (viewRes α l) ρ₂)
    (hρ : ResUT.CompS Z (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ)
    (hvZ : ResUT.Valid Z) (hZ : NoneAt (· = l) Z)
    (hF : ∀ w' ρf, F w' ρf → NoneAt (· = l) ρf) (hO : lendRec l ∉ O)
    (hls : ∀ x ∈ ls, x.1 ≠ lendRec l) (h : twp (ℍ := ℍ) F Q n w ls O e ρ) :
    twp (ℍ := ℍ) F Q n w ((lendRec l, α) :: ls) (lendRec l :: O) e ρ₂ :=
  twp_consume_view_held hρ₁ hρ₂ <| twp_lendEnd hρ₁ hρ hvZ hZ hF
    (fun x => by simp) hO
    (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr hx)
    (fun x hx => List.mem_cons_of_mem _ hx) hls h

/-- A record re-read from the lend's record is the lend's record. -/
theorem lendRec_rr_fwd {K K' : WCactus} {Θ' : CodeTy} {l : BoCa.Loc} {r : FrameRecT K'}
    (h : RecRR Θ' (lendRec (K := K) l) r) : r = lendRec l := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hR : r.R = PMap.empty := RR.of_empty h₄
  cases r
  simp_all [lendRec]

/-- The lender's frame across a callee: its resource re-read from `ρ₁` at `w`, its records the
lend's and `O` re-read. -/
def LenderAt (w : TWd) (ρ₁ : TRes w.K) (O : List (FrameRecT w.K)) (l : BoCa.Loc) : TRProp :=
  fun w' O' b => ∃ O'' : List (FrameRecT w'.K), O' = lendRec l :: O'' ∧ w.Ext w' ρ₁ ∧
    RRw (w := w) (w' := w') ρ₁ b ∧ RecsRR w'.Θ O O''

theorem LenderAt.mono {w : TWd} {ρ₁ : TRes w.K} {O : List (FrameRecT w.K)} {l : BoCa.Loc} :
    (LenderAt w ρ₁ O l).Mono := by
  rintro w₁ w₂ O₁ O₂ b₁ b₂ hE hr hO ⟨O'', rfl, hE₁, hr₁, hO₁⟩
  obtain _ | ⟨hp, hO'⟩ := hO
  rename_i p O₃
  obtain rfl := lendRec_rr_fwd hp
  exact ⟨O₃, rfl, hE₁.trans hr₁ hE, RRw.trans hE.1 hr₁ hr, hO₁.trans hE.1 hO'⟩

/-- **(T4c) The hardest case: a lend ends after a callee gave its copy up under the lender's
frame.** The lender holds `Z ● v` (its lend cell `v`) and one more copy `v`, owns the lend's record
and `O`. A callee run from the copy alone gives it up (T2: the lender's frame, `Z ● v` re-read,
holds a copy), ending owning nothing and holding nothing (`QGiveUp`), beside the lender's frame
(`twp_frame`, `LenderAt`). The lend then ends by `twp_lendEnd` as it stands, at the world the
callee ended at: its frame condition `hF` (no other part holds anything at `ℓ`) is the
condition that every live copy is back. The continuation `hrest` runs from the own cell beside
`Z` re-read. -/
theorem twp_lendEnd_after_framed_consume {F : TFrame} (hFm : F.Mono) {Q : TPost} (K : Kont)
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr}
    {Z ρ₁ ρ₂ : TRes w.K} {l : BoCa.Loc} {α : Life}
    (hρ₁ : ResUT.CompS Z (viewRes α l) ρ₁) (hρ₂ : ResUT.CompS (viewRes α l) ρ₁ ρ₂)
    (hcov : CovR (sem w.Θ) w.K ρ₂) (hOcov : ∀ r ∈ O, CovR (sem w.Θ) w.K r.R)
    (hvZ : ResUT.Valid Z) (hZ : NoneAt (· = l) Z)
    (hF : ∀ w' ρf, F w' ρf → NoneAt (· = l) ρf) (hO : lendRec l ∉ O)
    (hcallee : twp (ℍ := ℍ) (fun _ ρf => HoldsCopy α l ρf) QGiveUp n w ls [] e PMap.empty)
    (hrest : ∀ k (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t
      (Z' ρ' : TRes w'.K), w.Ext w' Z → RRw (w := w) (w' := w') Z Z' → RecsRR w'.Θ O O' →
      ResUT.CompS Z' (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ' →
      (∀ x ∈ ls', x.1 ≠ lendRec l) → twp (ℍ := ℍ) F Q k w' ls' O' (K.plug t) ρ') :
    twp (ℍ := ℍ) F Q n w ls (lendRec l :: O) (K.plug e) ρ₂ := by
  classical
  have hcov₁ : CovR (sem w.Θ) w.K ρ₁ := hcov.of_compS_right hρ₂
  have hR₁ : LenderAt w ρ₁ O l w (lendRec l :: O) ρ₁ :=
    ⟨O, rfl, TWd.Ext.refl _ _, RR.refl hcov₁, RecsRR.refl hOcov⟩
  have hfr := twp_frame (ℍ := ℍ) (F := F) (F₁ := fun _ ρf => HoldsCopy α l ρf) (P := QGiveUp)
    (R := LenderAt w ρ₁ O l) LenderAt.mono (O₁ := []) (O₂ := lendRec l :: O)
    (fun _ hp => by cases hp) hρ₂ hcov
    (fun (w₀ : TWd) (ρf ρ₂₀ y : TRes w₀.K) hE hr _ hy => by
      obtain ⟨Z₀, v₀, -, hv₀, hZ₀⟩ := RR.split_retype hE.1 hρ₁ hcov₁ hE.2 hr
      obtain rfl := rr_view_eq hv₀
      exact holdsCopy_compS ⟨Z₀, hZ₀⟩ hy)
    (twp_frame_callee_consume (fun _ _ h => h) hcallee) hR₁
  refine twp_bind hFm K (twp_mono (fun k w' ls' O' t ρ' hp => ?_) hfr)
  obtain ⟨O₁', O₂', a, b, hOe, hab, ⟨rfl, rfl⟩, O'', rfl, hE, hr, hOr⟩ := hp
  obtain rfl : ρ' = b :=
    ResUT.CompS.functional hab (ResUT.CompS.comm (ResUT.compS_empty_right b))
  simp only [List.nil_append] at hOe
  subst hOe
  obtain ⟨Z', v', hZr, hvr, hZ'⟩ := RR.split_retype hE.1 hρ₁ hcov₁ hE.2 hr
  obtain rfl := rr_view_eq hvr
  have hvZ' : ResUT.Valid Z' := by
    obtain ⟨σ, hσ⟩ := hvZ
    obtain ⟨σ', hσ', -⟩ := ResUT.Flat.rrLs hE.1 hσ hZr
    exact ⟨σ', hσ'⟩
  have hZl : NoneAt (· = l) Z' := NoneAt.rr hE.1 hvZ hZr hZ
  have hZ'l : Z'.get l = none := by
    obtain ⟨σ, hσ⟩ := hvZ'
    exact get_eq_none_of_flatT hσ (hZl σ hσ l rfl)
  obtain ⟨ρo, hρo⟩ := (ResUT.compS_defined_iff Z' (ResUT.single l (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT hZ'l)
  have hO'' : lendRec l ∉ O'' := fun hm => by
    obtain ⟨r, hr', hrr⟩ := forall₂_mem_right hOr hm
    exact hO (lendRec_rr_eq hrr ▸ hr')
  exact twp_lendEnd hZ' hρo hvZ' hZl hF (fun x => by simp) hO''
    (ls₁ := ls'.filter (fun x => x.1 ≠ lendRec l))
    (fun x hx => by
      by_cases h : x.1 = lendRec l
      · exact Or.inl h
      · exact Or.inr (List.mem_filter.mpr ⟨hx, by simpa using h⟩))
    (fun x hx => (List.mem_filter.mp hx).1)
    (fun x hx => by simpa using (List.mem_filter.mp hx).2)
    (hrest k w' _ O'' t Z' ρo (hE.of_compS_left hρ₁) hZr hOr hρo
      (fun x hx => by simpa using (List.mem_filter.mp hx).2))

/-- The configuration's frame meets a spawned child's frame condition at the empty mask
(`enSpawn`'s `Fe`). -/
theorem fdMask_false_view : fdMask (fun _ => False) wE (viewRes (lfE 1) 1) :=
  ⟨valid_view _ _, fun _ _ _ h => h.elim⟩

/-- The configuration's frame meets the child's admitted condition. -/
theorem child_cond_view :
    fdMask (fun _ => False) wE (viewRes (lfE 1) 1) ∧ HoldsCopy (K := wE.K) (lfE 1) 1
      (viewRes (lfE 1) 1) :=
  ⟨fdMask_false_view, holdsCopy_view⟩

/-! ### A given-up `imm` cell beside a framed `mut` cell (`imm ○ mut`), admitted along the walks

The configuration of the retired `not_xoptWFrameAt`
(`git show a66b0538:Support/Model/Tree/World/UpdXW.lean`, lines 140–186). -/

section FrameAt

/-- The run's copy `x = imm({β}, (), ∅)` at `ℓ = 1`, at the graft cactus (`K₁`, where `α < β`). -/
abbrev xF : TCell K₁ := viewCell βL

/-- The framed `mut` cell `y = mut({β}, (), ∅, ⊤)`: the value and witness of `x` (`○` clause (5)). -/
def yF : TCell K₁ :=
  CellUT.mutOf (TSet.single βL) BoCa.Val.unit PMap.empty (ResUT.inStratum_empty _) (fun _ _ => True)
    trivial

/-- `ℓ ↦ y`, at the stratum of `{α}`. -/
theorem single_yF_inStratum : (ResUT.single 1 yF).InStratum (TSet.single αL) :=
  ResUT.inStratum_single 1 fun x hx z hz => by
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hz]
    exact K₁_lt

/-- The frame's ancestor `ζ = imm({α}, (), ℓ ↦ y)` at `n = 2`. -/
def ζF : TCell K₁ :=
  CellUT.immOf (TSet.single αL) BoCa.Val.unit (ResUT.single 1 yF) single_yF_inStratum

/-- The start composite: the frame's `n ↦ ζ` beside the run's copy `ℓ ↦ x`. -/
def acF : TRes K₁ := PMap.pair 2 ζF 1 xF

theorem acF_comp : ResUT.CompS (ResUT.single 2 ζF) (viewRes βL 1) acF :=
  G.comp_sng_sng (by decide) _ _

/-- The location typing covering `ℓ` with the trivial type. -/
def ΘF : LocTy := fun _ => some ⟨fun _ _ _ => True⟩

theorem cov_cF : CovR ΘF K₁ (ResUT.single 2 ζF) := by
  intro l ψ e
  obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
  refine Cov.immOf_iff.mpr fun m φ h => ?_
  obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some h
  exact Cov.mut _ _ _ rfl (fun _ _ => ⟨fun _ => trivial, fun _ => trivial⟩)
    (fun k φ h => absurd (show yF.wit.get k = some φ from h) (by rw [yF, CellUT.wit_mutOf]; simp))

/-- The only `mut` cell at depth of the start composite is `y`. -/
theorem acF_mut {l : BoCa.Loc} {φ : TCell K₁} (h : CellAt acF l φ) (hk : φ.kind = Kind.mut) :
    φ = yF := by
  cases h with
  | top e =>
      simp only [acF, PMap.pair_get] at e
      split_ifs at e <;> cases e <;> simp [ζF, xF, viewCell] at hk
  | nest e h' =>
      simp only [acF, PMap.pair_get] at e
      split_ifs at e <;> cases e
      · simp only [ζF, CellUT.wit_immOf] at h'
        cases h' with
        | top e' => obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'; rfl
        | nest e' h'' =>
            obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
            simp only [yF, CellUT.wit_mutOf] at h''
            cases h'' with
            | top e'' => simp at e''
            | nest e'' _ => simp at e''
      · simp only [xF, viewCell, CellUT.wit_immOf] at h'
        cases h' with
        | top e' => simp at e'
        | nest e' _ => simp at e'

theorem acF_mutOne : MutOne acF :=
  fun _ _ _ h₁ h₂ k₁ k₂ => (acF_mut h₁ k₁).trans (acF_mut h₂ k₂).symm

/-- `ex(ℓ ↦ y)_○ = ℓ ↦ y`. -/
theorem exR_single_yF : ExRT (ResUT.single 1 yF) (ResUT.single 1 yF) := by
  refine G.ExW.mk (w := [(1, PMap.empty)]) (b := PMap.empty) (nm := ResUT.single 1 yF)
    (G.sites_sng _ 1 yF _ rfl)
    (G.ExWits.cons yF (by simp) rfl (by simp only [yF, CellUT.wit_mutOf]; exact exW_empty)
      G.ExWits.nil) (G.BigComp.cons G.BigComp.nil (G.comp_empty_right _)) ?_
    (G.comp_empty_right _)
  rw [ResUT.restrict_single_other (k := Kind.own) (fun e => Kind.noConfusion e),
    ResUT.restrict_single_self (k := Kind.mut) rfl]
  exact G.comp_empty_left _

/-- `ag(ℓ ↦ y) = ∅`. -/
theorem ag_single_yF : AgWT (ResUT.single 1 yF) PMap.empty := by
  refine G.AgW.mk (wm := [(1, PMap.empty)]) (wi := []) (a := PMap.empty) (bm := PMap.empty)
    (bi := PMap.empty) (G.sites_sng _ 1 yF _ rfl)
    (ResUT.sites_single_other (fun e => Kind.noConfusion e))
    (G.AgWitsM.cons yF (by simp) rfl (by simp only [yF, CellUT.wit_mutOf]; exact agW_empty)
      G.AgWitsM.nil) G.AgWitsI.nil (G.BigComp.cons G.BigComp.nil (G.comp_empty_right _))
    G.BigComp.nil ?_ (G.comp_empty_right _)
  rw [ResUT.restrict_single_other (k := Kind.imm) (fun e => Kind.noConfusion e)]
  exact G.comp_empty_right _

open Classical in
theorem sites_acF_imm : G.Sites CellUT.kind acF Kind.imm [2, 1] := by
  refine ⟨by simp, fun l => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, acF, PMap.pair_get]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨ζF, by simp, rfl⟩
    · exact ⟨xF, by simp, rfl⟩
  · rintro ⟨ψ, e, -⟩
    by_cases h₂ : l = 2
    · exact Or.inl h₂
    · by_cases h₁ : l = 1
      · exact Or.inr h₁
      · simp [h₂, h₁] at e

open Classical in
theorem sites_acF_mut : G.Sites CellUT.kind acF Kind.mut [] := by
  refine ⟨by simp, fun l => ?_⟩
  simp only [List.not_mem_nil, false_iff, acF, PMap.pair_get]
  rintro ⟨ψ, e, hk⟩
  split_ifs at e <;> cases e <;> simp [ζF, xF, viewCell] at hk

/-- **`✓` of the start composite**: `⦇n ↦ ζ, ℓ ↦ x⦈ = {n ↦ ζ, ℓ ↦ x ○ y}`. -/
theorem acF_valid : ResUT.Valid acF := by
  have hR : ResUT.CompatR (G.restrict CellUT.kind acF Kind.imm) (ResUT.single 1 yF) := by
    intro l ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e₂
    have e := (ResUT.restrict_eq_some.mp e₁).1
    simp only [acF, PMap.pair_get] at e
    simp at e
    subst e
    exact ⟨_, CellUT.CompR.immMut (TSet.single βL) BoCa.Val.unit PMap.empty _ (TSet.single βL)
      (ResUT.inStratum_empty _) (fun _ _ => True) trivial⟩
  obtain ⟨σ, hσ⟩ := (ResUT.compR_defined_iff _ _).mpr hR
  have hAg : AgWT acF σ := by
    refine G.AgW.mk (wm := []) (wi := [(2, ResUT.single 1 yF), (1, PMap.empty)])
      sites_acF_mut sites_acF_imm G.AgWitsM.nil ?_ G.BigComp.nil
      (G.BigComp.cons (G.BigComp.cons G.BigComp.nil (G.comp_empty_right _))
        (G.comp_empty_right _)) (G.comp_empty_right _) hσ
    refine G.AgWitsI.cons ζF (by simp [acF, PMap.pair_get]) rfl (ResUT.single 1 yF) PMap.empty
      (by simp only [ζF, CellUT.wit_immOf]; exact exR_single_yF)
      (by simp only [ζF, CellUT.wit_immOf]; exact ag_single_yF) (G.comp_empty_right _) ?_
    refine G.AgWitsI.cons xF (by simp [acF, PMap.pair_get]) rfl PMap.empty PMap.empty
      (by simp only [xF, viewCell, CellUT.wit_immOf]; exact exW_empty)
      (by simp only [xF, viewCell, CellUT.wit_immOf]; exact agW_empty) (G.comp_empty_right _)
      G.AgWitsI.nil
  exact ⟨σ, PMap.empty, σ, exST_all_imm (fun l ψ e => by
    simp only [acF, PMap.pair_get] at e
    split_ifs at e <;> cases e <;> rfl), hAg, ResUT.comp_empty_left _⟩

/-- **`UpdA` admits a given-up `imm` cell beside a framed `mut` cell** (`docs/new-core/scope-806.md`
§4; the configuration of the retired `not_xoptWFrameAt`), at
resources. The run gives up its copy `x` at `ℓ`, the end world (the start composite, the frame
keeping `x`'s copy) absorbing it; the framed part `n ↦ ζ` holds `y = mut(…)` at `ℓ` beneath its
`imm` ancestor `ζ`. The start composite reads `x ○ y = x` at `ℓ`, the end reads `y`: no relation
between the two cells at `ℓ` alone accepts that, and `UpdA` accounts for `y` by `ζ`. Masks empty. -/
theorem updA_admits_frameAt :
    UpdA ΘF (fun _ => False) (fun _ => False) acF (ResUT.single 2 ζF) acF :=
  updA_consume_view acF_comp cov_cF acF_valid acF_comp (ResUT.CompS.comm acF_comp) acF_valid
    acF_mutOne (fun _ _ h _ => h) (fun _ _ h k => h.of_compS_left acF_comp (kind_mut_ne_imm k))

end FrameAt

end BoCa.Fig16.Tree.Wp

end
