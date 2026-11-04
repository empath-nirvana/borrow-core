import Core.TreeBorrowEdges
import Core.TreeHandle

/-!
# Consuming a copy of a shared view at `twp`  `[spec §62]`

Can a run give up one copy of a shared `imm` view, ending without it and without returning it?
`twp` has no garbage `ρ⁺` (departure D4: row 5.33's `ρ ↭ ρ′ ● ρ⁺` read as `ρ ↭ ρ′`). Three
places a copy can be held elsewhere, three answers:

* **The run holds another copy: admitted, at no cost** (`twp_consume_view_held`). An `imm` copy
  composes with itself to itself (`viewRes_dup`), so a resource holding a copy absorbs another
  (`absorb_view`) and the run's resource with the extra copy is the resource without it
  (`consume_view_held`). Nothing changes in the world, so `twp_lendEnd` is used as it stands: an
  end still needs every copy anywhere else back, and a task still holding a live copy keeps the
  lend open.

* **Only the frame holds another copy: refused** (`twp_refuses_consume_view`). The configuration:
  on the chain tree, one lend of `ℓ = 1` at `α = 1` (`recWInv_lendStep`); the frame owns the
  record and holds a copy of the lend cell; the run holds the other copy (`viewRes_dup`), owns no
  record, and is the value `()`. Its postcondition asks that it end owning nothing and holding
  nothing. No `twp` at index `1` meets it: `EndT`'s `↭` (`UpdX`) keeps every unmasked `imm` cell
  of the start's flattening in the end's (`updX_consume_view_false`), and the run owns no record, so
  `ℓ` is unmasked. The same run keeping its copy is admitted (`twp_admits_keep_view`). The world
  would not change here either (`consume_view_world`): the refusal is `↭`'s, not the invariants'.

* **No other copy: the world keeps it** (`recInv_lend_holds_view`): while the record is open its
  lent location is in the world's aliasable walk, so the last copy cannot leave a world meeting
  `RecInv`.

A copy kept in the world as garbage, as row 5.33's `ρ⁺` is kept, sits in the lender's frame at its
end and fails `twp_lendEnd`'s frame condition (`not_noneAt_view`).

**Three positions of an ordinary consume.** Under `twp_bind` the callee's run is handed the whole
resource, the caller's copy included, so a callee consuming its copy is admitted
(`twp_bind_callee_consume`). A callee proved at its own copy alone, the caller's outside its run
(`twp_frame`), is refused (`twp_frame_callee_refused`). A lend's callback consuming one of two
copies it holds ends the lend through `twp_lendEnd` as it stands (`twp_lendEnd_after_consume`). A
spawned task is its own run, its parent's copy in its frame: refused (`twp_child_refused`).

A `mut` cell has no second copy (`not_compS_single_self`): no part absorbs it, so consuming one
always changes the world.
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

/-- **A task holding one copy of a shared view cannot consume it at `twp`.** At the chain tree,
with the lend of `ℓ = 1` at `α = 1` open, the frame owning its record and holding a copy, the run
holding the other copy and owning no record, no `twp` at a frame condition `F` the frame meets runs
`()` to an end owning nothing and holding nothing. -/
theorem twp_refuses_consume_view_at (F : TFrame) (hF : F wE (viewRes (lfE 1) 1)) :
    ¬ twp (ℍ := ℍ) F QGiveUp 1 wE lsOne [] (.val .unit) (viewRes (lfE 1) 1) := by
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
  have hS : SplitT [lendRec (K := wE.K) 1] [] [lendRec 1] :=
    ⟨fun p => by simp, fun p hp => by simp at hp⟩
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', -, -, -, -, -, -, -, -, ⟨hO', hρ'⟩, hu, -, -⟩ :=
    h wE (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) (viewRes (lfE 1) 1) lsOne [] [lendRec 1]
      [lendRec 1] _ (TWd.Ext.refl _ _) rr_view (.cons ⟨lendRec_rr 1, rfl⟩ .nil) .nil hF
      ⟨hdup.1, _, hdup, hI₁.valid⟩ hdup hS hR₁ hI₁ hfd 0 _ _ (by omega) (.refl _ _)
      (LogRel.Core.final_val _ Val.unit)
  subst hρ'
  exact updX_consume_view_false (by simp [recMask]) hu

/-- `twp_refuses_consume_view_at` at the trivial frame condition. -/
theorem twp_refuses_consume_view :
    ¬ twp (ℍ := ℍ) (fun _ _ => True) QGiveUp 1 wE lsOne [] (.val .unit) (viewRes (lfE 1) 1) :=
  twp_refuses_consume_view_at _ trivial

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

/-- **A callee proved at its own copy alone cannot consume it** when the caller's copy is outside
its run (`twp_frame`'s `R`, or the frame), at every frame condition the configuration's frame
meets. `twp_refuses_consume_view_at`, restated for a callee's frame condition `F₁`. -/
theorem twp_frame_callee_refused (F₁ : TFrame) (hF₁ : F₁ wE (viewRes (lfE 1) 1)) :
    ¬ twp (ℍ := ℍ) F₁ QGiveUp 1 wE lsOne [] (.val .unit) (viewRes (lfE 1) 1) :=
  twp_refuses_consume_view_at F₁ hF₁

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

/-- The configuration's frame meets a spawned child's frame condition at the empty mask
(`enSpawn`'s `Fe`). -/
theorem fdMask_false_view : fdMask (fun _ => False) wE (viewRes (lfE 1) 1) :=
  ⟨valid_view _ _, fun _ _ _ h => h.elim⟩

/-- **A spawned task holding a copy its parent also holds cannot consume it**: the task is its own
run, and the parent's copy is outside it, in its frame. At the child's frame condition
(`fdMask` at the empty mask). -/
theorem twp_child_refused :
    ¬ twp (ℍ := ℍ) (fdMask (fun _ => False)) QGiveUp 1 wE lsOne [] (.val .unit)
      (viewRes (lfE 1) 1) :=
  twp_refuses_consume_view_at _ fdMask_false_view

end BoCa.Fig16.Tree.Wp

end
