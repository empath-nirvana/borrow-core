import Paper
import Support

/-!
# Views — no run returns a view it did not start with

A question about the printed system, not a transcription: given `x : Imm @a (Ref T)`, is there a
view of the pointee at the same lifetime `@a`, as Rust's `&'a Box<T> → &'a T`?  `[TR]` p. 3 types
the only read through a borrow, `withload`, with the pointee at a fresh `'b ⊏ ⊓Δ`
(`Imm̲ 'b (Ref T) ≜ Imm 'b T`), inside a callback whose result is `['b] T₂`.  This file shows that
the model of `[TR]` §§4–5 excludes such a view on its own: no expression whatever returns it.

* `upd_imm_of_top`: if `ρ ↭ π` and `π` holds a top-level `imm` cell at `m`, then `⦇ρ⦈(m)` is an
  `imm` cell with the same value and witness.  This is the right-to-left half of `↭`'s `imm`
  clause (`[TR]` p. 5; `[CONF]` Fig. 18b clause (1), p. 415:22, read as `docs/adjudications.md`
  §12.39 reads it).
* `wp_view_preexists`: so every view a run returns (a top-level `imm` cell of its `ρ′`) was
  already an `imm` cell of `⦇ρ⦈`, for the `ρ` the run started at.  It needs only `[TR]` p. 6's
  `wp` conjunct `ρ ↭ ρ′ ● ρ⁺`, at the frame `ρ_f = ∅`.
* `no_view_of_pointee`: at `ρ = ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))`, a member of
  `𝒱⟦Imm @a (Ref 1)⟧δ(ℓ)`, no expression `e` satisfies `wp e {𝒱⟦Imm @b 1⟧δ′}`, at any `@b` and
  `δ′`.  `⦇ρ⦈` holds one `imm` cell, at `ℓ`, whose value is `ℓ₁ ≠ ()`; at `ℓ₁` it holds
  `own(())`.
* `no_closed_projection`: `𝒱⟦Imm @a (Ref 1) ⊸ Imm @b 1⟧δ` has no member at `∅`.
* `frame_view_excluded`: `[TR]` 6.38 read at a 6.64 frame whose borrow is the whole resource:
  a resource `ℓ ↦ imm({α}, v, ρv)` updates to holds no cell at any location `ρv` owns.
* `mut_view_excluded`: the `mut` clause of `↭` likewise excludes a new `mut` cell at a location
  the witness of a `mut` borrow owns.

The nested-borrow clause `Imm̲ 'b (Imm @a T) ≜ Imm @a T` is the contrast: there the inner view is
already an `imm` cell of `⦇ρ⦈`, `wp_view_preexists` does not exclude returning it, and [CONF]
p. 415:9 derives `load : Imm a T ⊸ T` for every `T` with `Imm̲ 'b T = T`.

`[about ours]`: an extension, not a transcription.  It uses the library's definitions unchanged.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.MintProbe
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel

/-! ### The two clauses of `Imm̲` at a pointer and at a nested borrow

`[TR]` p. 3 and `[CONF]` Fig. 8: `Imm̲ 'b (Ref T) ≜ Imm 'b T` and `Imm̲ 'b (Imm @a T) ≜ Imm @a T`.
A load through an owned pointer gives a borrow at the load's fresh `'b`; a load of a nested
borrow gives it back at its own lifetime. -/

theorem immReborrow_ref (b : Lifetime.Life) (T : Ty) : (Ty.ref T).immReborrow b = .imm b T := rfl

theorem immReborrow_imm (a b : Lifetime.Life) (T : Ty) :
    (Ty.imm a T).immReborrow b = .imm a T := rfl

/-! ### `↭` keeps the `imm` cells of the flattening -/

/-- Where the left operand of a `●` has no cell, the composite has the right operand's. -/
theorem comp_get_of_left_none {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} (e : ρ₁.get l = none) : ρ.get l = ρ₂.get l := by
  rcases ResU.Comp.get h l with ⟨-, e₂, e⟩ | ⟨ψ, e₁, -, -⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, -, -, -⟩
  · rw [e, e₂]
  · rw [e] at e₁; cases e₁
  · rw [e, e₂]
  · rw [e] at e₁; cases e₁

/-- An `imm` cell of the left operand of a `●` is in the composite, over the same value and
witness. -/
theorem compS_get_imm_left {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {ψ : CellU Loc Val} (e : ρ₁.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [f₁] at e; cases e
  · rw [f₁] at e; cases Option.some.inj e; exact ⟨_, f, hk, rfl, rfl⟩
  · rw [f₁] at e; cases e
  · rw [f₁] at e
    cases Option.some.inj e
    exact ⟨χ, f, CellU.CompS.kind hC, (CellU.CompS.erase hC).1, (CellU.CompS.wit hC).1⟩

/-- A top-level `imm` cell of `π` is an `imm` cell of `⦇π⦈`, over the same value and
witness. -/
theorem flat_imm_of_top {π σ : WRes} (hσ : π.Flat σ) {m : Loc} {ψ : CellU Loc Val}
    (e : π.get m = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, σ.get m = some χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  obtain ⟨ex, a, hex, ha, hc⟩ := hσ
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgW.get_imm ha e hk
  have hexm : ex.get m = none := by
    cases e' : ex.get m with
    | none => rfl
    | some ζ =>
        have hζ : ζ.kind ≠ Kind.imm := ExS.immFree hex m ζ e'
        have := ResU.CompatS.right_eq_none hc.1 e' hζ
        rw [eχ] at this; cases this
  exact ⟨χ, (comp_get_of_left_none hc hexm).trans eχ, kχ, rχ, wχ⟩

/-- **`↭` creates no `imm` cell.**  If `ρ ↭ π`, every top-level `imm` cell of `π` is an `imm`
cell of `⦇ρ⦈`, over the same value and witness: the right-to-left half of `↭`'s `imm` clause,
*"`⦇ρ₁⦈(ℓ) = imm(ᾱ, v, ρ) ⇔ ⦇ρ₂⦈(ℓ) = imm(ᾱ, v, ρ)`"* ([CONF] Fig. 18b, clause (1)). -/
theorem upd_imm_of_top {ρ π : WRes} (hupd : ResU.UpdV ρ π) {m : Loc} {ψ : CellU Loc Val}
    (hπ : π.get m = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.FlatAt m χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  obtain ⟨⟨himm, -⟩, -, ⟨σπ, hσπ⟩⟩ := hupd
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := flat_imm_of_top hσπ hπ hk
  obtain ⟨t, ht, hχ⟩ := CellU.imm_eta kχ
  rw [hχ] at eχ
  refine ⟨_, (himm m t χ.erase χ.wit ht).mpr ⟨σπ, hσπ, eχ⟩, rfl, ?_, ?_⟩
  · rw [CellU.erase_immOf]; exact rχ
  · rw [CellU.wit_immOf]; exact wχ

/-- **A run returns no view it did not start with.**  If `wp e {Q̂}` holds at a valid `ρ`, some
run ends at a `ρ′` with `Q̂(v)(ρ′)` whose every top-level `imm` cell is an `imm` cell of `⦇ρ⦈`,
over the same value and witness.  Only `[TR]` p. 6's conjunct `ρ ↭ ρ′ ● ρ⁺` is used, at the
frame `ρ_f = ∅`. -/
theorem wp_view_preexists {e : Expr} {Q : Val → WProp} {ρ : WRes} (hρ : ResU.Valid ρ)
    (hwp : wp e Q ρ) :
    ∃ v ρ', Q v ρ' ∧ ∀ (m : Loc) (ψ : CellU Loc Val), ρ'.get m = some ψ → ψ.kind = Kind.imm →
      ∃ χ, ρ.FlatAt m χ ∧ χ.kind = Kind.imm ∧ χ.erase = ψ.erase ∧ χ.wit = ψ.wit := by
  obtain ⟨ρ', ρp, -, -, -, π, v, -, -, -, -, -, -, -, -, -, -, hc, hupd, -, hQ⟩ :=
    hwp PMap.empty (ResU.hash_symm (ResU.hash_empty_right hρ))
  refine ⟨v, ρ', hQ, fun m ψ e hk => ?_⟩
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := compS_get_imm_left hc e hk
  obtain ⟨χ', h', k', r', w'⟩ := upd_imm_of_top hupd eχ kχ
  exact ⟨χ', h', k', r'.trans rχ, w'.trans wχ⟩

/-! ### The configuration: a borrow of a pointer to `()` -/

theorem single_own_inStratum (l : Loc) (v : Val) (β : Life) :
    (ResU.single l (CellU.ownOf v) : WRes).InStratum β := fun _ ψ e => by
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; trivial

/-- `ℓ₁ ↦ own(())`, the pointee. -/
abbrev pointee (l₁ : Loc) : WRes := ResU.single l₁ (CellU.ownOf Val.unit)

/-- `ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))`: `[TR]` 6.64's `ρᵢ` for the cell `ℓ ↦ ℓ₁` at the payload
`𝒱⟦Ref 1⟧`. -/
abbrev ptrBorrow (α : Life) (l l₁ : Loc) : WRes :=
  ResU.single l (CellU.immOf (LSet.singleton α) (Val.loc l₁) (pointee l₁)
    (single_own_inStratum _ _ _))

/-- `ℓ₁ ↦ own(()) ● ℓ ↦ own(ℓ₁)` is defined and valid: the memory before the borrow. -/
theorem owned_valid {l l₁ : Loc} (hne : l ≠ l₁) :
    ∃ W, ResU.CompS (pointee l₁) (ResU.single l (CellU.ownOf (Val.loc l₁))) W ∧
      ResU.Valid W := by
  have hl : (pointee l₁).get l = none := ResU.single_get_ne _ hne
  obtain ⟨W, hW⟩ := (ResU.compS_defined_iff _ _).mpr
    (compatS_single_of_get_none (ψ := CellU.ownOf (Val.loc l₁)) hl)
  have hμ : ResU.Lower (pointee l₁) (fun k => ((pointee l₁).get k).map CellU.erase) :=
    ⟨_, ResU.flat_single_own l₁ Val.unit, fun _ => rfl⟩
  obtain ⟨-, -, hh, -⟩ := hash_compS_own (compS_empty_left _) hμ (by simp [hl]) hW
  exact ⟨W, hW, (hash_valid hh).2⟩

/-- `✓ ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))`, by `[TR]` 6.34 at `ρ = ∅`. -/
theorem ptrBorrow_valid (α : Life) {l l₁ : Loc} (hne : l ≠ l₁) :
    ResU.Valid (ptrBorrow α l l₁) := by
  obtain ⟨W, hW, hv⟩ := owned_valid hne
  exact (hash_valid (ResU.six34 hW (ResU.hash_symm (ResU.hash_empty_right hv)))).2

/-- `𝒱⟦Ref 1⟧δ(ℓ₁)(ℓ₁ ↦ own(()))`. -/
theorem vDen_ref_unit (δ : Lifetime.LSub) (l₁ : Loc) :
    vDen (.ref .unit) δ (Val.loc l₁) (pointee l₁) :=
  ⟨l₁, Val.unit, PMap.empty, _, compS_empty_left _, ⟨rfl, rfl⟩, _, PMap.empty,
    ResU.comp_empty_right _, rfl, ⟨rfl, rfl⟩⟩

/-- The configuration is in the type: `𝒱⟦Imm @a (Ref 1)⟧δ(ℓ)(ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(())))`
at `@aδ = α`. -/
theorem ptrBorrow_vDen {a : Lifetime.Life} {δ : Lifetime.LSub} {α : Life}
    (ha : a.interp δ = some α) (l l₁ : Loc) :
    vDen (.imm a (.ref .unit)) δ (Val.loc l) (ptrBorrow α l l₁) :=
  ⟨α, ha, l, PMap.empty, _, compS_empty_left _, ⟨rfl, rfl⟩,
    LSet.singleton α, Val.loc l₁, pointee l₁, _, rfl, vDen_ref_unit δ l₁, le_rfl⟩

/-- `⦇ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))⦈` holds one `imm` cell, at `ℓ`, with value `ℓ₁`. -/
theorem ptrBorrow_flat_imm {α : Life} {l l₁ m : Loc} {χ : CellU Loc Val}
    (hf : (ptrBorrow α l l₁).FlatAt m χ) (hk : χ.kind = Kind.imm) :
    m = l ∧ χ.erase = Val.loc l₁ := by
  obtain ⟨σ, ⟨ex, a, hex, ha, hc⟩, eσ⟩ := hf
  -- the `imm` cell is in the aliasable walk
  have ham : ∃ ζ, a.get m = some ζ ∧ ζ.kind = Kind.imm := by
    rcases (ResU.CompS.imm_site_iff hc m).mp ⟨χ, eσ, hk⟩ with ⟨ζ, e, k⟩ | h
    · exact absurd k (ExS.immFree hex m ζ e)
    · exact h
  obtain ⟨e', a', p, hex', hag', hp, hpa⟩ := AgW.single_imm_inv ha
  cases ExR.functional hex' (ExW.single_own _ _)
  cases AgW.functional hag' (AgW.single_own _ _)
  cases ResU.CompR.functional hp (ResU.comp_empty_right _)
  have hml : m = l := by
    obtain ⟨ζ, eζ, kζ⟩ := ham
    rcases ResU.Comp.get hpa m with ⟨-, -, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
        ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
    · rw [f] at eζ; cases eζ
    · exact (ResU.single_get_eq_some f₁).1
    · rw [f] at eζ
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some f₂
      cases Option.some.inj eζ; cases kζ
    · exact (ResU.single_get_eq_some f₁).1
  subst hml
  obtain ⟨ζ, eζ, kζ, rζ, -⟩ := AgW.get_imm ha (ResU.single_get_self _ _) rfl
  have hexl : ex.get m = none := by
    cases e : ex.get m with
    | none => rfl
    | some ξ =>
        have := ResU.CompatS.right_eq_none hc.1 e (ExS.immFree hex m ξ e)
        rw [eζ] at this; cases this
  rw [comp_get_of_left_none hc hexl, eζ] at eσ
  cases Option.some.inj eσ
  exact ⟨rfl, rζ⟩

/-! ### No view of the pointee -/

/-- **No expression returns a view of the pointee.**  From `ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))`,
a member of `𝒱⟦Imm @a (Ref 1)⟧δ(ℓ)`, no `e` satisfies `wp e {𝒱⟦Imm @b 1⟧δ′}`, at any `@b` and
`δ′`, `@b = @a` included.  A view returned has value `()`; the one `imm` cell of `⦇ρ⦈` holds
`ℓ₁`. -/
theorem no_view_of_pointee {α : Life} {l l₁ : Loc} (hne : l ≠ l₁) (e : Expr)
    (b : Lifetime.Life) (δ' : Lifetime.LSub) :
    ¬ wp e (vDen (.imm b .unit) δ') (ptrBorrow α l l₁) := by
  intro hwp
  obtain ⟨v, ρ', hQ, hall⟩ := wp_view_preexists (ptrBorrow_valid α hne) hwp
  obtain ⟨α', -, m, ρa, ρb, hc, ⟨rfl, -⟩, s, w, σ, hs, rfl, ⟨-, hw⟩, -⟩ := hQ
  cases eq_of_compS_empty_left hc
  obtain ⟨χ, hf, kχ, rχ, -⟩ := hall m _ (ResU.single_get_self _ _) rfl
  obtain ⟨-, hv⟩ := ptrBorrow_flat_imm hf kχ
  rw [hv, CellU.erase_immOf, hw] at rχ
  exact absurd (congrArg Subtype.val rχ) (by simp [Val.loc, Val.unit])

/-- **No resource-free same-lifetime projection.**  `𝒱⟦Imm @a (Ref 1) ⊸ Imm @b 1⟧δ` has no member
at `∅`, at any `@b`, `@b = @a` included. -/
theorem no_closed_projection {a b : Lifetime.Life} {δ : Lifetime.LSub} {α : Life}
    (ha : a.interp δ = some α) (f : Val) :
    ¬ vDen (.lolli (.imm a (.ref .unit)) (.imm b .unit)) δ f PMap.empty := by
  intro h
  exact no_view_of_pointee (α := α) (l := 1) (l₁ := 0) (by decide) _ b δ
    (h (Val.loc 1) _ _ (ptrBorrow_vDen ha 1 0) (compS_empty_left _))

/-! ### `[TR]` 6.38 at a frame, and the `mut` clause -/

/-- `[TR]` 6.38 at a frame whose borrow is the whole resource: if `ℓ ↦ imm({α}, v, ρv)` updates
to an own-free `π`, then `π` has no cell at any location `ρv` owns.  The frame's end (6.64's
G5, through 6.38's G1) puts `own` cells back at those locations. -/
theorem frame_view_excluded {α : Life} {l m : Loc} {v u : Val} {ρv W π : WRes}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (hvW : ResU.Valid W)
    (hupd : ResU.UpdV (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) π)
    (hno : NoOwn π) (hm : ρv.get m = some (CellU.ownOf u))
    {ψ : CellU Loc Val} (hψ : π.get m = some ψ) : False := by
  obtain ⟨G, hG, hGW⟩ := ResU.six38 (ρ := PMap.empty) (ρ' := PMap.empty) hW
    (ResU.hash_symm (ResU.hash_empty_right hvW)) (ResU.hash_symm (ResU.hash_empty_right hupd.2.2))
    (ResU.inStratum_empty α) (ResU.inStratum_empty α) hno (compS_empty_left _)
    (compS_empty_left _) hupd
  cases eq_of_compS_empty_left hG
  have hml : m ≠ l := by
    rintro rfl
    have := ResU.CompatS.right_eq_none hW.1 hm (by simp)
    rw [ResU.single_get_self] at this
    cases this
  have hWm : W.get m = some (CellU.ownOf u) :=
    (ResU.CompS.get_left_of_ne_imm hW hm (by simp)).2
  have hGm := ResU.CompatS.right_eq_none (ResU.CompatS.symm hGW.1) hWm (by simp)
  rw [ResU.del_get_ne _ hml, hψ] at hGm
  cases hGm

/-- 6.38 at the configuration: `ℓ ↦ imm({α}, ℓ₁, ℓ₁ ↦ own(()))` updates to no own-free resource
with a cell at `ℓ₁`.  Every hypothesis of `frame_view_excluded` is discharged. -/
theorem ptrBorrow_frame_excluded {α : Life} {l l₁ : Loc} (hne : l ≠ l₁) {π : WRes}
    (hupd : ResU.UpdV (ptrBorrow α l l₁) π) (hno : NoOwn π) {ψ : CellU Loc Val}
    (hψ : π.get l₁ = some ψ) : False := by
  obtain ⟨W, hW, hv⟩ := owned_valid hne
  exact frame_view_excluded hW hv hupd hno (ResU.single_get_self _ _) hψ

/-- **`↭`'s `mut` clause creates no `mut` cell at a location a `mut` witness owns.**  No `π`
that `ℓ ↦ mut(b, v, ρw, P̂)` updates to, with `ρw(m) = own(u)`, holds a `mut` cell at `m`, at any
lifetime and predicate: `⦇ℓ ↦ mut(b, v, ρw, P̂)⦈(m) = own(u)`, `ex` walking the `mut` witness. -/
theorem mut_view_excluded {l m : Loc} {b b₁ : Life} {v u u₁ : Val} {ρw χ₁ : WRes}
    {hstr : ρw.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρw, hstr⟩}
    {h₁ : χ₁.InStratum b₁} {P₁ : Val → SPropS Loc Val b₁} {hw₁ : P₁ u₁ ⟨χ₁, h₁⟩}
    (hwm : ρw.get m = some (CellU.ownOf u)) {π : WRes}
    (hupd : ResU.UpdV (ResU.single l (CellU.mutOf b v ρw hstr P hw)) π)
    (hπ : π.get m = some (CellU.mutOf b₁ u₁ χ₁ h₁ P₁ hw₁)) : False := by
  obtain ⟨⟨-, hmut⟩, -, ⟨σπ, ex, a, hex, ha, hc⟩⟩ := hupd
  have hexm := ExS.get_of_ne_imm hex hπ (by simp)
  have hσm := (ResU.CompS.get_left_of_ne_imm hc hexm (by simp)).2
  obtain ⟨u₂, χ₂, h₂, hw₂, σ', ⟨ex', a', hex', ha', hc'⟩, e'⟩ :=
    (hmut m b₁ P₁).mpr ⟨u₁, χ₁, h₁, hw₁, σπ, ⟨ex, a, hex, ha, hc⟩, hσm⟩
  have hpath : LogRel.Typed.XPath (ResU.single l (CellU.mutOf b v ρw hstr P hw)) [l] ρw := by
    have := LogRel.Typed.XPath.cons (p := [])
      (ResU.single_get_self l (CellU.mutOf b v ρw hstr P hw)) (by simp) (LogRel.Typed.XPath.nil _)
    simpa using this
  have hown := LogRel.Typed.xpath_ex hex' hpath hwm (by simp)
  rw [(ResU.CompS.get_left_of_ne_imm hc' hown (by simp)).2] at e'
  cases e'

end BoCa.MintProbe

end
