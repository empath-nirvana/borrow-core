import Paper
import Support

/-!
# Views — minting `imm` cells over an owned resource

`[TR]` 6.64 (Imm Frame) runs its body at `ρ_b ● ρᵢ`, `ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`, where the
caller owned `ℓ ↦ own(v) ● ρ_P̂(v)`.  Its proof spends four facts about the one cell `ρᵢ` against
the owned resource `W = ρ_P̂(v) ● ℓ ↦ own(v)`: 6.34 (`ρ # W ⇒ ρ # ρᵢ`), 6.26 with 6.8 (`ρᵢ` and
`W` lower to one memory under a frame), 6.29 with 6.38 (`ρᵢ` is a top-level cell after the run,
and what is left is compatible with `W`), and 6.39 (`↭` carried from `ρᵢ` back to `W`).

This file states those four facts for a resource `Y` of several `imm` cells at one lifetime
`α`, every one of which sits on an `own` cell of `ex(O)` for an owned `O`:

* `Mint α O Y`: `Y`'s cells are `imm({α}, u, w)`, each on an `own(u)` cell of `ex(O)`, and
  `ag(Y) = Y ○ ex(O)_○ ○ ag(O)` — `Y`'s witnesses are walks `O` already makes.
* `mint_single`: `ρᵢ` is a mint over `W` (the shape 6.64 uses).
* `Mint.flat`: for `Z # O`, `⦇Z ● Y⦈` is `⦇Z ● O⦈` with `Y`'s cells in place of the `own`
  cells under them (6.34 and 6.26 together).
* `Mint.hash`, `Mint.lower_iff`, `Mint.upd`: 6.34, 6.26/6.8 and 6.39 for `Y`.
* `Mint.top`: 6.29 for `Y`.
* `Mint.post_hash`: 6.38 for `Y`.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.MintProbe
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- `c` is a cell a view `ψ` may sit on: `own` of `ψ`'s value (`[TR]` 6.64's cell), or a `mut`
cell over `ψ`'s value and witness (the target of a frozen `Mut`, theory's derived-views §8).
`[about ours]` -/
def Base (ψ c : CellU Loc Val) : Prop :=
  c = CellU.ownOf ψ.erase ∨ (c.kind = Kind.mut ∧ c.erase = ψ.erase ∧ c.wit = ψ.wit)

theorem Base.ne_imm {ψ c : CellU Loc Val} (h : Base ψ c) : c.kind ≠ Kind.imm := by
  rcases h with rfl | ⟨k, -, -⟩
  · simp
  · rw [k]; exact fun e => Kind.noConfusion e

theorem Base.erase_eq {ψ c : CellU Loc Val} (h : Base ψ c) : c.erase = ψ.erase := by
  rcases h with rfl | ⟨-, e, -⟩
  · simp
  · exact e

/-- A view absorbs the cell it sits on: `ψ ○ c = ψ`. -/
theorem Base.absorb {ψ c : CellU Loc Val} (h : Base ψ c) (hk : ψ.kind = Kind.imm) :
    CellU.CompR ψ c ψ := by
  rcases h with rfl | ⟨k, e, w⟩
  · exact CellU.compR_own_right_of_erase rfl
  · rcases CellU.rep c with ⟨u, rfl⟩ | ⟨s', u, χ, h', rfl⟩ | ⟨b, u, χ, hb, P, hP, rfl⟩
    · simp at k
    · simp at k
    · simp only [CellU.erase_mutOf, CellU.wit_mutOf] at e w
      obtain ⟨s, hs, hψ⟩ := CellU.imm_eta hk
      have hs' : χ.InStratum s.join := by rw [w]; exact hs
      have hψ' : ψ = CellU.immOf s u χ hs' :=
        hψ.trans (CellU.immOf_congr rfl e.symm w.symm hs hs')
      rw [hψ']
      exact CellU.CompR.immMut s u χ hs' b hb P hP

/-- `Y` mints `imm` cells at `α` over the owned `O`: every cell of `Y` is `imm({α}, u, w)` and
sits on an `own(u)` cell of `ex(O)`, and `ag(Y) = Y ○ (ex(O)_○ ○ ag(O))`.
`[about ours: the facts 6.64's proof uses of its `ρᵢ`, at several cells]` -/
structure Mint (α : Life) (O Y : WRes) : Prop where
  cell : ∀ m ψ, Y.get m = some ψ →
    ∃ (u : Val) (w : WRes) (h : w.InStratum (LSet.singleton α).join),
      ψ = CellU.immOf (LSet.singleton α) u w h
  own : ∀ eO, ExS O eO → ∀ m ψ, Y.get m = some ψ → ∃ c, eO.get m = some c ∧ Base ψ c
  ag : ∀ eO aO aY, ExS O eO → AgW O aO → AgW Y aY →
    ∃ p, ResU.CompR eO aO p ∧ ResU.CompR Y p aY
  agDef : ∃ aY, AgW Y aY

namespace Mint

variable {α : Life} {O Y : WRes}

theorem kind (h : Mint α O Y) {m : Loc} {ψ : CellU Loc Val} (e : Y.get m = some ψ) :
    ψ.kind = Kind.imm := by
  obtain ⟨u, w, hw, rfl⟩ := h.cell m ψ e; rfl

theorem exS (h : Mint α O Y) : ExS Y PMap.empty :=
  ExW.empty_of_all_imm (fun _ _ e => h.kind e)

end Mint

/-! ### The normal form of `⦇Z ● Y⦈` -/

/-- Over `○`, an `imm` cell absorbs the `own` cell beneath it. -/
theorem compR_imm_own_absorb {Y B : WRes}
    (hY : ∀ m ψ, Y.get m = some ψ →
      ψ.kind = Kind.imm ∧ ∃ c, B.get m = some c ∧ Base ψ c) :
    ∃ C, ResU.CompR Y B C ∧ (∀ m, Y.get m = none → C.get m = B.get m) ∧
      (∀ m ψ, Y.get m = some ψ → C.get m = some ψ) := by
  have hcR : ResU.CompatR Y B := by
    intro m ψ₁ ψ₂ e₁ e₂
    obtain ⟨hk, c, hB, hbase⟩ := hY m ψ₁ e₁
    rw [hB] at e₂; cases Option.some.inj e₂
    exact ⟨ψ₁, hbase.absorb hk⟩
  obtain ⟨C, hC⟩ := (ResU.compR_defined_iff Y B).mpr hcR
  refine ⟨C, hC, fun m e => ResU.Comp.get_of_left_none hC e, fun m ψ e => ?_⟩
  obtain ⟨hk, c, hB, hbase⟩ := hY m ψ e
  rcases ResU.Comp.get hC m with ⟨f, -, -⟩ | ⟨χ, f₁, f₂, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hc⟩
  · rw [f] at e; cases e
  · rw [hB] at f₂; cases f₂
  · rw [f₁] at e; cases e
  · rw [e] at f₁; cases Option.some.inj f₁
    rw [hB] at f₂; cases Option.some.inj f₂
    exact f.trans (congrArg some (CellU.CompR.functional hc (hbase.absorb hk)))

/-- `⦇Z ● Y⦈` for `Z # O`: `⦇Z ● O⦈` with each `own` cell under `Y` replaced by `Y`'s cell —
`[TR]` 6.34's display (`⦇ρ ● ρᵢ⦈ = ex(ρ)_● ● (ρᵢ ○ ⦇ρ_v⦈_○ ○ ag(ρ))`) at several cells.
`[about ours: 6.34's and 6.26's step at a mint]` -/
theorem Mint.flat (hM : Mint α O Y) {Z ZO : WRes} (hZO : ResU.CompS Z O ZO) {σ : WRes}
    (hσ : ResU.Flat ZO σ) :
    ∃ ZY σ', ResU.CompS Z Y ZY ∧ ResU.Flat ZY σ' ∧
      (∀ m, Y.get m = none → σ'.get m = σ.get m) ∧
      (∀ m ψ, Y.get m = some ψ → σ'.get m = some ψ ∧
        ∃ c, σ.get m = some c ∧ Base ψ c ∧ ∀ eO, ExS O eO → eO.get m = some c) := by
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩ :=
    (ResU.Flat.split hZO).mp hσ
  have himm₁ : e₁.ImmFree := ExS.immFree he₁
  have himm₂ : e₂.ImmFree := ExS.immFree he₂
  have himm : e.ImmFree := ResU.ImmFree.compS hec himm₁ himm₂
  -- `e₂ ▸◂ a` and `e₁ ▸◂ e₂ ● a`
  obtain ⟨B, hB, hσB⟩ := (ResU.CompS.assoc e₁ e₂ a σ).mpr ⟨e, hec, hc⟩
  have he₂a : ResU.CompatS e₂ a := hB.1
  have hdisj₂ := ResU.CompatS.disjoint_of_immFree himm₂ he₂a
  -- `e₂ ● a = a₁ ○ p`, `p = e₂ ○ a₂`
  have hBR : ResU.CompR e₂ a B := ResU.CompS.toCompR hB
  obtain ⟨p, hp, hpB⟩ :=
    (ResU.CompR.assoc e₂ a₂ a₁ B).mp ⟨a, ResU.CompR.comm hac, hBR⟩
  -- `ag(Y)`
  obtain ⟨aY, haY⟩ := hM.agDef
  obtain ⟨p', hp', hYp⟩ := hM.ag e₂ a₂ aY he₂ ha₂ haY
  rw [ResU.CompR.functional hp' hp] at hYp
  -- `Y`'s cells sit on `own` cells of `B`
  have hYB : ∀ m ψ, Y.get m = some ψ →
      ψ.kind = Kind.imm ∧ ∃ c, B.get m = some c ∧ Base ψ c := by
    intro m ψ e
    obtain ⟨c, he₂m, hbase⟩ := hM.own e₂ he₂ m ψ e
    refine ⟨hM.kind e, c, ?_, hbase⟩
    rcases hdisj₂ m with h | h
    · rw [h] at he₂m; cases he₂m
    · exact (ResU.Comp.get_of_right_none hB h).trans he₂m
  obtain ⟨C, hC, hCoff, hCon⟩ := compR_imm_own_absorb hYB
  -- `ag(Z ● Y) = a₁ ○ aY = C`
  have haC : ResU.CompR a₁ aY C := by
    -- `Y ○ (p ○ a₁) = C`, regrouped
    obtain ⟨x, hx, hxC⟩ := (ResU.CompR.assoc Y p a₁ C).mp ⟨B, hpB, hC⟩
    obtain rfl : x = aY := ResU.CompR.functional hx hYp
    exact ResU.CompR.comm hxC
  -- `e₁ ▸◂ C`
  have hBdom : ∀ m, B.get m = none ↔ C.get m = none := by
    intro m
    constructor
    · intro h
      cases eY : Y.get m with
      | none => rw [hCoff m eY]; exact h
      | some ψ => obtain ⟨-, c, hc, -⟩ := hYB m ψ eY; rw [hc] at h; cases h
    · intro h
      cases eY : Y.get m with
      | none => rw [← hCoff m eY]; exact h
      | some ψ => rw [hCon m ψ eY] at h; cases h
  have he₁C : ResU.CompatS e₁ C := ResU.Compat.of_disjoint (fun m => by
    rcases ResU.CompatS.disjoint_of_immFree himm₁ hσB.1 m with h | h
    · exact Or.inl h
    · exact Or.inr ((hBdom m).mp h))
  obtain ⟨σ', hσ'⟩ := (ResU.compS_defined_iff e₁ C).mpr he₁C
  -- `Z ● Y`
  have hZY : ResU.CompatS Z Y := ResU.Compat.of_disjoint (fun m => by
    cases eY : Y.get m with
    | none => exact Or.inr rfl
    | some ψ =>
      refine Or.inl ?_
      cases eZ : Z.get m with
      | none => rfl
      | some ζ =>
        exfalso
        obtain ⟨-, c, hBm, hbase⟩ := hYB m ψ eY
        have he₁m : e₁.get m = none := by
          rcases ResU.CompatS.disjoint_of_immFree himm₁ hσB.1 m with h | h
          · exact h
          · rw [h] at hBm; cases hBm
        have hσm : σ.get m = some c :=
          (ResU.Comp.get_of_left_none hσB he₁m).trans hBm
        -- `Z(m)` reaches `⦇Z ● O⦈(m) = c`, not `imm`, so it is in `ex(Z)`
        obtain ⟨χ, hχ, hkχ, -⟩ := ResU.CompS.get_left hZO eZ
        obtain ⟨χ', hχ', hkχ', -, -⟩ := ResU.Flat.get hσ hχ
        rw [hσm] at hχ'; cases Option.some.inj hχ'
        have hk' : ζ.kind ≠ Kind.imm := by
          rw [← hkχ, ← hkχ']; exact hbase.ne_imm
        rw [ExS.get_of_ne_imm he₁ eZ hk'] at he₁m; cases he₁m)
  obtain ⟨ZY, hZY'⟩ := (ResU.compS_defined_iff Z Y).mpr hZY
  have hex : ExS ZY e₁ := (ExS.split hZY').mpr ⟨e₁, PMap.empty, he₁, hM.exS,
    ResU.comp_empty_right e₁⟩
  have hag : AgW ZY C := (AgW.split hZY').mpr ⟨a₁, aY, ha₁, haY, haC⟩
  refine ⟨ZY, σ', hZY', ⟨e₁, C, hex, hag, hσ'⟩, fun m eY => ?_, fun m ψ eY => ?_⟩
  · rcases ResU.CompatS.disjoint_of_immFree himm₁ hσB.1 m with h | h
    · rw [ResU.Comp.get_of_left_none hσ' h, ResU.Comp.get_of_left_none hσB h, hCoff m eY]
    · rw [ResU.Comp.get_of_right_none hσB h,
        ResU.Comp.get_of_right_none hσ' ((hBdom m).mp h)]
  · obtain ⟨-, c, hBm, hbase⟩ := hYB m ψ eY
    have he₁m : e₁.get m = none := by
      rcases ResU.CompatS.disjoint_of_immFree himm₁ hσB.1 m with h | h
      · exact h
      · rw [h] at hBm; cases hBm
    refine ⟨(ResU.Comp.get_of_left_none hσ' he₁m).trans (hCon m ψ eY), c,
      (ResU.Comp.get_of_left_none hσB he₁m).trans hBm, hbase, fun eO heO => ?_⟩
    obtain ⟨c', he₂m, -⟩ := hM.own e₂ he₂ m ψ eY
    have hc' : c' = c := by
      rcases hdisj₂ m with h | h
      · rw [h] at he₂m; cases he₂m
      · exact Option.some.inj (he₂m.symm.trans ((ResU.Comp.get_of_right_none hB h).symm.trans hBm))
    rw [ExS.functional heO he₂, he₂m, hc']

/-- `[TR]` 6.34 at a mint: `Z # O ⇒ Z # Y`. -/
theorem Mint.hash (hM : Mint α O Y) {Z : WRes} (h : ResU.Hash Z O) : ResU.Hash Z Y := by
  obtain ⟨-, ZO, hZO, σ, hσ⟩ := h
  obtain ⟨ZY, σ', hZY, hσ', -, -⟩ := hM.flat hZO hσ
  exact ⟨hZY.1, ZY, hZY, σ', hσ'⟩

/-- `[TR]` 6.26 with 6.8 at a mint: under a frame `F # O`, `F ● Y` and `F ● O` lower to the
same memory. -/
theorem Mint.lower_iff (hM : Mint α O Y) {F FO FY : WRes} (hFO : ResU.CompS F O FO)
    (hvFO : ResU.Valid FO) (hFY : ResU.CompS F Y FY) (w : Loc → Option Val) :
    ResU.Lower FY w ↔ ResU.Lower FO w := by
  obtain ⟨σ, hσ⟩ := hvFO
  obtain ⟨FY', σ', hFY', hσ', hoff, hon⟩ := hM.flat hFO hσ
  obtain rfl : FY' = FY := ResU.CompS.functional hFY' hFY
  have herase : ∀ l, (σ'.get l).map CellU.erase = (σ.get l).map CellU.erase := by
    intro l
    cases eY : Y.get l with
    | none => rw [hoff l eY]
    | some ψ =>
        obtain ⟨h₁, c, h₂, hbase, -⟩ := hon l ψ eY
        rw [h₁, h₂]
        exact congrArg some hbase.erase_eq.symm
  constructor
  · rintro ⟨τ, hτ, hw⟩
    obtain rfl : τ = σ' := ResU.Flat.functional hτ hσ'
    exact ⟨σ, hσ, fun l => (hw l).trans (herase l)⟩
  · rintro ⟨τ, hτ, hw⟩
    obtain rfl : τ = σ := ResU.Flat.functional hτ hσ
    exact ⟨σ', hσ', fun l => (hw l).trans (herase l).symm⟩

/-- `[TR]` 6.39 at a mint: `Z ● Y ↭ Z′ ● Y` gives `Z ● O ↭ Z′ ● O`, for `Z, Z′ # O`. -/
theorem Mint.upd (hM : Mint α O Y) {Z Z' ZO Z'O ZY Z'Y : WRes}
    (hZO : ResU.CompS Z O ZO) (hvZO : ResU.Valid ZO)
    (hZ'O : ResU.CompS Z' O Z'O) (hvZ'O : ResU.Valid Z'O)
    (hZY : ResU.CompS Z Y ZY) (hZ'Y : ResU.CompS Z' Y Z'Y) (hupd : ResU.UpdV ZY Z'Y) :
    ResU.UpdV ZO Z'O := by
  obtain ⟨σ, hσ⟩ := hvZO
  obtain ⟨τ, hτ⟩ := hvZ'O
  obtain ⟨ZY₁, σ', hZY₁, hσ', hoff, hon⟩ := hM.flat hZO hσ
  obtain ⟨Z'Y₁, τ', hZ'Y₁, hτ', hoff', hon'⟩ := hM.flat hZ'O hτ
  obtain rfl : ZY₁ = ZY := ResU.CompS.functional hZY₁ hZY
  obtain rfl : Z'Y₁ = Z'Y := ResU.CompS.functional hZ'Y₁ hZ'Y
  obtain ⟨⟨hI, hMu⟩, -, -⟩ := hupd
  refine ⟨⟨fun l s v χ h => ?_, fun l b P => ?_⟩, ⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
  · rw [ResU.flatAt_iff hσ, ResU.flatAt_iff hτ]
    have hl := hI l s v χ h
    rw [ResU.flatAt_iff hσ', ResU.flatAt_iff hτ'] at hl
    cases eY : Y.get l with
    | none => rw [← hoff l eY, ← hoff' l eY]; exact hl
    | some ψ =>
        obtain ⟨-, c, hc, -, hcO⟩ := hon l ψ eY
        obtain ⟨-, c', hc', -, hcO'⟩ := hon' l ψ eY
        obtain ⟨e₁, e₂, -, -, -, -, -, he₂, -⟩ := (ResU.Flat.split hZO).mp hσ
        have hcc : c = c' := Option.some.inj ((hcO e₂ he₂).symm.trans (hcO' e₂ he₂))
        rw [hc, hc', hcc]
  · have hl := hMu l b P
    simp only [ResU.flatAt_iff hσ', ResU.flatAt_iff hτ'] at hl
    simp only [ResU.flatAt_iff hσ, ResU.flatAt_iff hτ]
    cases eY : Y.get l with
    | none => rw [← hoff l eY, ← hoff' l eY]; exact hl
    | some ψ =>
        obtain ⟨-, c, hc, -, hcO⟩ := hon l ψ eY
        obtain ⟨-, c', hc', -, hcO'⟩ := hon' l ψ eY
        obtain ⟨e₁, e₂, -, -, -, -, -, he₂, -⟩ := (ResU.Flat.split hZO).mp hσ
        have hcc : c = c' := Option.some.inj ((hcO e₂ he₂).symm.trans (hcO' e₂ he₂))
        rw [hc, hc', hcc]

/-! ### After the run: `[TR]` 6.29 and 6.38 at a mint -/

/-- `⦇π⦈` after a run from `Z ● Y` (`Z, O ∈ Res_α`): `Y`'s cells are there as they were, and
every other cell is in `Res_α` — `[TR]` 6.29's *"all borrows in `⦇ρ′⦈` other than `ρᵢ` must be
disjoint from `α`"*, at several cells. -/
theorem Mint.post_flat (hM : Mint α O Y) {Z ZO ZY π τ : WRes} (hZα : Z.InStratum α)
    (hOα : O.InStratum α) (hZO : ResU.CompS Z O ZO) (hvZO : ResU.Valid ZO)
    (hZY : ResU.CompS Z Y ZY) (hupd : ResU.UpdV ZY π) (hτ : ResU.Flat π τ) :
    (∀ m ψ, Y.get m = some ψ → τ.get m = some ψ) ∧
      (∀ m, Y.get m = none → ∀ φ, τ.get m = some φ → φ.InStratum α) := by
  obtain ⟨σ, hσ⟩ := hvZO
  obtain ⟨ZY₁, σ', hZY₁, hσ', hoff, hon⟩ := hM.flat hZO hσ
  obtain rfl : ZY₁ = ZY := ResU.CompS.functional hZY₁ hZY
  have hσα : σ.InStratum α := BoLo.flat_inStratum hσ (ResU.CompS.inStratum hZO hZα hOα)
  obtain ⟨⟨hI, hMu⟩, -, -⟩ := hupd
  refine ⟨fun m ψ eY => ?_, fun m eY φ hφ => ?_⟩
  · obtain ⟨u, w, hw, rfl⟩ := hM.cell m ψ eY
    exact (ResU.flatAt_iff hτ _ _).mp
      ((hI m _ u w hw).mp ((ResU.flatAt_iff hσ' _ _).mpr (hon m _ eY).1))
  · rcases CellU.rep φ with ⟨u, rfl⟩ | ⟨t, u, χ, hh, rfl⟩ | ⟨b, u, χ, hh, P, hw, rfl⟩
    · exact trivial
    · have h' : σ'.get m = some (CellU.immOf t u χ hh) :=
        (ResU.flatAt_iff hσ' _ _).mp ((hI m t u χ hh).mpr ((ResU.flatAt_iff hτ _ _).mpr hφ))
      rw [hoff m eY] at h'
      exact hσα m _ h'
    · obtain ⟨u', χ', h', hw', hfa⟩ := (hMu m b P).mpr ⟨u, χ, hh, hw, (ResU.flatAt_iff hτ _ _).mpr hφ⟩
      have h'' := (ResU.flatAt_iff hσ' _ _).mp hfa
      rw [hoff m eY] at h''
      exact (hσα m _ h'' : b ⊐ α)

/-- No top-level cell of `π` is shorter than `α`. -/
theorem Mint.post_not_shorter (hM : Mint α O Y) {π τ : WRes} (hτ : ResU.Flat π τ)
    (hon : ∀ m ψ, Y.get m = some ψ → τ.get m = some ψ)
    (hoff : ∀ m, Y.get m = none → ∀ φ, τ.get m = some φ → φ.InStratum α) :
    ∀ m φ, π.get m = some φ → ¬ (φ.at < α) := by
  intro m φ e
  rcases CellU.rep φ with ⟨u, rfl⟩ | ⟨t, u, χ, hh, rfl⟩ | ⟨b, u, χ, hh, P, hw, rfl⟩
  · simp only [CellU.at_ownOf]; exact not_lt_of_ge (Life.top_sqsubseteq α)
  · obtain ⟨ζ, hζ, hkζ, -, -⟩ := ResU.Flat.get hτ e
    obtain ⟨s, hs, heta⟩ := CellU.imm_eta (by rw [hkζ]; rfl)
    have hζ' : τ.get m = some (CellU.immOf s ζ.erase ζ.wit hs) := hζ.trans (congrArg some heta)
    have hsub : ∀ x, t.mem x → s.mem x := fun x hx => ResU.Flat.get_ls_imm hτ e hζ' hx
    simp only [CellU.at_immOf]
    cases eY : Y.get m with
    | none =>
        have hst : s.meet ⊐ α := hoff m eY _ hζ'
        exact not_lt_of_ge (le_trans (le_of_lt hst) (s.meet_least _ (hsub _ t.meet_mem)))
    | some ψ =>
        obtain ⟨u', w, hw, rfl⟩ := hM.cell m ψ eY
        rw [hon m _ eY] at hζ'
        obtain ⟨hs', -, -⟩ := CellU.immOf_inj (Option.some.inj hζ')
        have hm : s.mem t.meet := hsub _ t.meet_mem
        rw [← hs'] at hm
        have : t.meet = α := hm
        rw [this]; exact lt_irrefl α
  · have hτm := ResU.flat_get_of_ne_imm hτ e (by simp)
    cases eY : Y.get m with
    | none =>
        have : b ⊐ α := hoff m eY _ hτm
        simp only [CellU.at_mutOf]; exact not_lt_of_gt this
    | some ψ =>
        obtain ⟨u', w, hw', rfl⟩ := hM.cell m ψ eY
        rw [hon m _ eY] at hτm
        exact absurd (Option.some.inj hτm) (by simp [CellU.immOf, CellU.mutOf])

/-- `[TR]` 6.29 at a mint: after a run from `Z ● Y`, every cell of `Y` is a top-level cell of
`π`, unchanged. -/
theorem Mint.top (hM : Mint α O Y) {Z ZO ZY π : WRes} (hZα : Z.InStratum α)
    (hOα : O.InStratum α) (hZO : ResU.CompS Z O ZO) (hvZO : ResU.Valid ZO)
    (hZY : ResU.CompS Z Y ZY) (hupd : ResU.UpdV ZY π) :
    ∀ m ψ, Y.get m = some ψ → π.get m = some ψ := by
  obtain ⟨τ, hτ⟩ := hupd.2.2
  obtain ⟨hon, hoff⟩ := hM.post_flat hZα hOα hZO hvZO hZY hupd hτ
  have hnb := hM.post_not_shorter hτ hon hoff
  intro m ψ eY
  obtain ⟨u, w, hw, rfl⟩ := hM.cell m ψ eY
  obtain ⟨φ, t, hφ, ht, hmem⟩ := ResU.flat_imm_at_top_of_no_shorter hτ (hon m _ eY)
    (CellU.lsOf_immOf _ _ _ _) rfl hnb
  have hkφ : φ.kind = Kind.imm := CellU.kind_of_lsOf ht
  obtain ⟨s, hs, heta⟩ := CellU.imm_eta hkφ
  have hφ' : π.get m = some (CellU.immOf s φ.erase φ.wit hs) := hφ.trans (congrArg some heta)
  have hsub : ∀ x, s.mem x → (LSet.singleton α).mem x := fun x hx =>
    ResU.Flat.get_ls_imm hτ hφ' (hon m _ eY) hx
  obtain ⟨χ, hχ, -, heχ, hwχ⟩ := ResU.Flat.get hτ hφ
  rw [hon m _ eY] at hχ
  cases Option.some.inj hχ
  have hseq : s = LSet.singleton α := by
    obtain ⟨y, hy⟩ := LSet.nonempty s
    have hyα : y = α := hsub y hy
    refine LSet.ext (fun x => ⟨fun hx => hsub x hx, fun hx => ?_⟩)
    have : x = α := hx
    rw [this, ← hyα]; exact hy
  rw [hφ']
  exact congrArg some (CellU.immOf_congr hseq heχ.symm (by rw [← hwχ]; simp) hs hw)

/-- `ρ⁺ = ρ⁺ \ dom(Y) ● Y` when `ρ⁺` holds `Y`'s cells. -/
theorem delDom_split {ρp Y : WRes} (h : ∀ m ψ, Y.get m = some ψ → ρp.get m = some ψ) :
    ResU.CompS (ρp.delDom Y) Y ρp := by
  refine ⟨ResU.Compat.of_disjoint (fun m => ?_), fun m => ?_⟩
  · cases eY : Y.get m with
    | none => exact Or.inr rfl
    | some ψ => exact Or.inl (ResU.delDom_get_of_some eY)
  · cases eY : Y.get m with
    | none =>
        show OptComp CellU.CompS ((ρp.delDom Y).get m) none (ρp.get m)
        rw [ResU.delDom_get_of_none eY]
        cases ρp.get m <;> rfl
    | some ψ =>
        show OptComp CellU.CompS ((ρp.delDom Y).get m) (some ψ) (ρp.get m)
        rw [ResU.delDom_get_of_some eY, h m ψ eY]
        rfl

/-- After the run, a top-level cell of `π` off `Y`'s cells is in `Res_α`. -/
theorem post_top_off {α : Life} {Y π τ : WRes} (hτ : ResU.Flat π τ)
    (hoff : ∀ m, Y.get m = none → ∀ φ, τ.get m = some φ → φ.InStratum α) :
    ∀ m, Y.get m = none → ∀ φ, π.get m = some φ → φ.InStratum α := by
  intro m eY φ e
  rcases CellU.rep φ with ⟨u, rfl⟩ | ⟨t, u, χ, hh, rfl⟩ | ⟨b, u, χ, hh, P, hw, rfl⟩
  · exact trivial
  · obtain ⟨ζ, hζ, hkζ, -, -⟩ := ResU.Flat.get hτ e
    obtain ⟨s, hs, heta⟩ := CellU.imm_eta (by rw [hkζ]; rfl)
    have hζ' : τ.get m = some (CellU.immOf s ζ.erase ζ.wit hs) := hζ.trans (congrArg some heta)
    have hst : s.meet ⊐ α := hoff m eY _ hζ'
    exact lt_of_lt_of_le hst (s.meet_least _ (ResU.Flat.get_ls_imm hτ e hζ' t.meet_mem))
  · exact hoff m eY _ (ResU.flat_get_of_ne_imm hτ e (by simp))

/-- `[TR]` 6.38 at a mint: after a run from `Z ● Y` to `ρ′ ● ρ⁺`, with `Z, O ∈ Res_α` and
`ρ′ ∈ Res_α`, `ρ′ ● ρ⁺ \ dom(Y)` is compatible with `O`, and `ρ′ ● ρ⁺ = (ρ′ ● ρ⁺ \ dom(Y)) ● Y`.
The printed proof's ancestor step is kept: a location of `ex(O)` in the aliasable walk of
`ρ′ ● ρ⁺ \ dom(Y)` sits beneath an `imm` cell there, which `↭` carries back to `⦇Z ● O⦈`, where
it is `Z`'s or `O`'s and its walk avoids `ex(O)`.  `[about ours: 6.38's proof at a mint]` -/
theorem Mint.post_hash (hM : Mint α O Y) {Z ZO ZY ρ' ρp π : WRes} (hZα : Z.InStratum α)
    (hOα : O.InStratum α) (hZO : ResU.CompS Z O ZO) (hvZO : ResU.Valid ZO)
    (hZY : ResU.CompS Z Y ZY) (hpp : ResU.CompS ρ' ρp π) (hρ'α : ρ'.InStratum α)
    (hupd : ResU.UpdV ZY π) :
    ∃ G, ResU.CompS (ρp.delDom Y) Y ρp ∧ ResU.CompS ρ' (ρp.delDom Y) G ∧
      ResU.CompS G Y π ∧ ResU.Hash G O := by
  classical
  have hTop := hM.top hZα hOα hZO hvZO hZY hupd
  obtain ⟨τ, hτ⟩ := hupd.2.2
  obtain ⟨hon, hoff⟩ := hM.post_flat hZα hOα hZO hvZO hZY hupd hτ
  have hTopOff := post_top_off hτ hoff
  -- `ρ′` holds no cell of `Y`'s
  have hρ'Y : ∀ m ψ, Y.get m = some ψ → ρ'.get m = none := by
    intro m ψ eY
    cases e' : ρ'.get m with
    | none => rfl
    | some ζ =>
        exfalso
        obtain ⟨u, w, hw, rfl⟩ := hM.cell m ψ eY
        have hπm := hTop m _ eY
        obtain ⟨χ, hχ, hkχ, -⟩ := ResU.CompS.get_left hpp e'
        rw [hπm] at hχ; cases Option.some.inj hχ
        have hkζ : ζ.kind = Kind.imm := by rw [← hkχ]; rfl
        obtain ⟨s, hs, heta⟩ := CellU.imm_eta hkζ
        have e'' : ρ'.get m = some (CellU.immOf s ζ.erase ζ.wit hs) :=
          e'.trans (congrArg some heta)
        have hmem : (LSet.singleton α).mem s.meet :=
          ResU.CompR.get_ls_imm (ResU.CompS.toCompR hpp) e'' hπm s.meet_mem
        have hsα : s.meet = α := hmem
        have := hρ'α m _ e''
        rw [CellU.inStratum_immOf, hsα] at this
        exact lt_irrefl α this
  have hpY : ∀ m ψ, Y.get m = some ψ → ρp.get m = some ψ := fun m ψ eY =>
    (ResU.Comp.get_of_left_none hpp (hρ'Y m ψ eY)).symm.trans (hTop m ψ eY)
  have hpd : ResU.CompS (ρp.delDom Y) Y ρp := delDom_split hpY
  obtain ⟨G, hG, hGY⟩ := (ResU.CompS.assoc ρ' (ρp.delDom Y) Y π).mp ⟨ρp, hpd, hpp⟩
  refine ⟨G, hpd, hG, hGY, ?_⟩
  -- `G ∈ Res_α`
  have hGπ : ∀ m, Y.get m = none → G.get m = π.get m := fun m eY =>
    (ResU.Comp.get_of_right_none hGY eY).symm
  have hGnone : ∀ m ψ, Y.get m = some ψ → G.get m = none := fun m ψ eY =>
    (ResU.Comp.eq_none_iff hG m).mpr ⟨hρ'Y m ψ eY, ResU.delDom_get_of_some eY⟩
  have hGα : G.InStratum α := by
    intro m φ e
    cases eY : Y.get m with
    | none => exact hTopOff m eY φ ((hGπ m eY).symm.trans e)
    | some ψ => rw [hGnone m ψ eY] at e; cases e
  -- the walks
  obtain ⟨σ, hσ⟩ := hvZO
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩ :=
    (ResU.Flat.split hZO).mp hσ
  obtain ⟨eG, eY, eπ, aG, aY, aπ, heG, heY, heπ, haG, haY, haπ, hcπ⟩ :=
    (ResU.Flat.split hGY).mp hτ
  obtain rfl : eY = PMap.empty := ExS.functional heY hM.exS
  obtain rfl : eG = eπ := ResU.eq_of_comp_empty_right heπ
  obtain ⟨p, hp, hYp⟩ := hM.ag e₂ a₂ aY he₂ ha₂ haY
  have himm₁ : e₁.ImmFree := ExS.immFree he₁
  have himm₂ : e₂.ImmFree := ExS.immFree he₂
  have himmE : e.ImmFree := ResU.ImmFree.compS hec himm₁ himm₂
  have himmG : eG.ImmFree := ExS.immFree heG
  -- F1: `ex(O)` avoids `ag(Z)` and `ag(O)`
  have hF1 : ∀ m, e₂.get m = none ∨ (a₁.get m = none ∧ a₂.get m = none) := by
    intro m
    rcases ResU.CompatS.disjoint_of_immFree himmE hc.1 m with h | h
    · exact Or.inl ((ResU.Comp.eq_none_iff hec m).mp h).2
    · exact Or.inr ((ResU.Comp.eq_none_iff hac m).mp h)
  -- `⦇G⦈` and `⦇G⦈ ∈ Res_α`
  have hvG : ResU.Valid G := (ResU.Valid.split hGY ⟨τ, hτ⟩).1
  obtain ⟨σG, eG', aG', heG', haG', hσGc⟩ := hvG
  obtain rfl : eG = eG' := ExS.functional heG heG'
  obtain rfl : aG = aG' := AgW.functional haG haG'
  have hσG : ResU.Flat G σG := ⟨eG, aG, heG, haG, hσGc⟩
  have hσGα : σG.InStratum α := BoLo.flat_inStratum hσG hGα
  obtain ⟨σG₁, σY, hσG₁, hσY, hCompR⟩ := BoLo.flat_compR hGY hτ
  obtain rfl : σG = σG₁ := ResU.Flat.functional hσG hσG₁
  -- F4: an `imm` cell of `⦇G⦈` is, over its witness, one of `ag(Z)` or of `ag(O)`
  have hF4 : ∀ m ψ, σG.get m = some ψ → ψ.kind = Kind.imm →
      (∃ φ, a₁.get m = some φ ∧ φ.kind = Kind.imm ∧ φ.wit = ψ.wit) ∨
        (∃ φ, a₂.get m = some φ ∧ φ.kind = Kind.imm ∧ φ.wit = ψ.wit) := by
    intro m ψ hψ hk
    obtain ⟨χ₀, hχ₀, hkχ₀, -, hwχ₀⟩ := ResU.CompR.get_imm_left hCompR hψ hk
    obtain ⟨s₀, hs₀, heta₀⟩ := CellU.imm_eta hkχ₀
    have hχ₀' : τ.get m = some (CellU.immOf s₀ χ₀.erase χ₀.wit hs₀) :=
      hχ₀.trans (congrArg some heta₀)
    obtain ⟨ZY₁, σ', hZY₁, hσ', hoffσ, honσ⟩ := hM.flat hZO hσ
    obtain rfl : ZY₁ = ZY := ResU.CompS.functional hZY₁ hZY
    have hupdm : σ'.get m = some (CellU.immOf s₀ χ₀.erase χ₀.wit hs₀) :=
      (ResU.flatAt_iff hσ' m _).mp
        ((hupd.1.1 m s₀ χ₀.erase χ₀.wit hs₀).mpr ⟨τ, hτ, hχ₀'⟩)
    cases eYm : Y.get m with
    | some ψY =>
        exfalso
        obtain ⟨u, w, hw, rfl⟩ := hM.cell m ψY eYm
        rw [(honσ m _ eYm).1] at hupdm
        obtain ⟨hs₀e, -, -⟩ := CellU.immOf_inj (Option.some.inj hupdm)
        obtain ⟨sψ, hsψ, hetaψ⟩ := CellU.imm_eta hk
        have hψ' : σG.get m = some (CellU.immOf sψ ψ.erase ψ.wit hsψ) :=
          hψ.trans (congrArg some hetaψ)
        have hmem : s₀.mem sψ.meet :=
          ResU.CompR.get_ls_imm hCompR hψ' hχ₀' sψ.meet_mem
        rw [← hs₀e] at hmem
        have hα' : sψ.meet = α := hmem
        have := hσGα m _ hψ'
        rw [CellU.inStratum_immOf, hα'] at this
        exact lt_irrefl α this
    | none =>
        rw [hoffσ m eYm] at hupdm
        have ham : a.get m = some (CellU.immOf s₀ χ₀.erase χ₀.wit hs₀) :=
          ResU.ag_eq_flat_at_imm ((ExS.split hZO).mpr ⟨e₁, e₂, he₁, he₂, hec⟩) hc hupdm
            (CellU.kind_immOf _ _ _ _)
        rcases ResU.CompR.imm_source hac ham with ⟨s₂, h₂, hg₂⟩ | ⟨s₃, h₃, hg₃⟩
        · exact Or.inl ⟨_, hg₂, CellU.kind_immOf _ _ _ _, by rw [CellU.wit_immOf]; exact hwχ₀⟩
        · exact Or.inr ⟨_, hg₃, CellU.kind_immOf _ _ _ _, by rw [CellU.wit_immOf]; exact hwχ₀⟩
  -- the ancestor step: `ex(O)` avoids `ag(G)`
  have hkey : ∀ m, e₂.get m = none ∨ aG.get m = none := by
    intro m
    cases hmW : e₂.get m with
    | none => exact Or.inl rfl
    | some ψW =>
      cases hmG : aG.get m with
      | none => exact Or.inr rfl
      | some ψG =>
        exfalso
        have hno : a₁.get m = none ∧ a₂.get m = none := by
          rcases hF1 m with h | h
          · rw [h] at hmW; cases hmW
          · exact h
        rcases AgW.dom_split haG hσG hmG with
          ⟨φ, hφ, hkφ⟩ | ⟨m', χc, f, hm', hkχ, hf, hsf⟩
        · rcases hF4 m φ hφ hkφ with ⟨φ', hφ', -, -⟩ | ⟨φ', hφ', -, -⟩
          · rw [hno.1] at hφ'; cases hφ'
          · rw [hno.2] at hφ'; cases hφ'
        · have hσGm' : σG.get m' = some χc :=
            ResU.CompS.get_right_of_immFree hσGc himmG hm'
          rcases hF4 m' χc hσGm' hkχ with ⟨φ', hφ', hkφ', hwφ'⟩ | ⟨φ', hφ', hkφ', hwφ'⟩
          · obtain ⟨s', hs', heta'⟩ := CellU.imm_eta hkφ'
            obtain ⟨ev₀, av₀, p₀, z₀, hev₀, hav₀, hcp₀, hz₀⟩ :=
              AgW.flat_imm_wit_le ha₁ m' s' φ'.erase φ'.wit hs'
                (hφ'.trans (congrArg some heta'))
            obtain rfl : f = p₀ :=
              ResU.FlatR.functional (by rw [hwφ']; exact hf)
                ⟨av₀, ev₀, hav₀, hev₀, ResU.CompR.comm hcp₀⟩
            rw [((ResU.Comp.eq_none_iff hz₀ m).mp hno.1).1] at hsf; cases hsf
          · obtain ⟨s', hs', heta'⟩ := CellU.imm_eta hkφ'
            obtain ⟨ev₀, av₀, p₀, z₀, hev₀, hav₀, hcp₀, hz₀⟩ :=
              AgW.flat_imm_wit_le ha₂ m' s' φ'.erase φ'.wit hs'
                (hφ'.trans (congrArg some heta'))
            obtain rfl : f = p₀ :=
              ResU.FlatR.functional (by rw [hwφ']; exact hf)
                ⟨av₀, ev₀, hav₀, hev₀, ResU.CompR.comm hcp₀⟩
            rw [((ResU.Comp.eq_none_iff hz₀ m).mp hno.2).1] at hsf; cases hsf
  -- `ag(G) ○ ag(O)`, a factor of `ag(π)` regrouped
  obtain ⟨YE, hYE, hYEa⟩ := (ResU.CompR.assoc Y e₂ a₂ aY).mp ⟨p, hp, hYp⟩
  obtain ⟨A, hA, hAπ⟩ := (ResU.CompR.assoc aG a₂ YE aπ).mp
    ⟨aY, ResU.CompR.comm hYEa, haπ⟩
  have himmG' : eG.restrict Kind.imm = PMap.empty := (ResU.restrict_imm_empty_iff eG).mpr himmG
  obtain ⟨hcA, hcYE⟩ := ResU.CompatS.of_compR_left himmG' hAπ hcπ.1
  obtain ⟨-, hce₂⟩ := ResU.CompatS.of_compR_left himmG' hYE hcYE
  have hce₂aG : ResU.CompatS e₂ aG := ResU.Compat.of_disjoint hkey
  have hce₂a₂ : ResU.CompatS e₂ a₂ := ResU.Compat.of_disjoint (fun m => by
    rcases hF1 m with h | h
    · exact Or.inl h
    · exact Or.inr h.2)
  have hce₂A : ResU.CompatS e₂ A := ResU.six37 hce₂aG hce₂a₂ hA
  obtain ⟨E, hE⟩ := (ResU.compS_defined_iff eG e₂).mpr hce₂
  have hcEA : ResU.CompatS E A := ResU.Compat.of_disjoint (fun m => by
    rcases ResU.CompatS.disjoint_of_immFree himmG hcA m with h' | h'
    · rcases ResU.CompatS.disjoint_of_immFree himm₂ hce₂A m with h'' | h''
      · exact Or.inl ((ResU.Comp.eq_none_iff hE m).mpr ⟨h', h''⟩)
      · exact Or.inr h''
    · exact Or.inr h')
  obtain ⟨σGO, hσGO⟩ := (ResU.compS_defined_iff E A).mpr hcEA
  -- `G ▸◂ O`
  have hGO : ResU.CompatS G O := by
    intro m ψ₁ ψ₂ hg₁ hg₂
    by_cases hk₂ : ψ₂.kind = Kind.imm
    · obtain ⟨χ₂, hχ₂, hkχ₂, heχ₂, hwχ₂⟩ := AgW.get_imm ha₂ hg₂ hk₂
      by_cases hk₁ : ψ₁.kind = Kind.imm
      · obtain ⟨χ₁, hχ₁, hkχ₁, heχ₁, hwχ₁⟩ := AgW.get_imm haG hg₁ hk₁
        obtain ⟨ξ, hξ⟩ := hA.1 m χ₁ χ₂ hχ₁ hχ₂
        obtain ⟨-, he₁', hw₁'⟩ := CellU.CompR.imm_left hξ hkχ₁
        obtain ⟨-, he₂', hw₂'⟩ := CellU.CompR.imm_left (CellU.CompR.comm hξ) hkχ₂
        exact CellU.compatS_iff.mpr ⟨hk₁, hk₂,
          heχ₁.symm.trans (he₁'.symm.trans (he₂'.trans heχ₂)),
          hwχ₁.symm.trans (hw₁'.symm.trans (hw₂'.trans hwχ₂))⟩
      · exfalso
        have hex₁ := ExS.get_of_ne_imm heG hg₁ hk₁
        obtain ⟨χ, hχ, hkχ, -, -⟩ := ResU.CompR.get_imm_right hA hχ₂ hkχ₂
        rcases ResU.CompatS.disjoint_of_immFree himmG hcA m with h | h
        · rw [h] at hex₁; cases hex₁
        · rw [h] at hχ; cases hχ
    · exfalso
      have hex : e₂.get m = some ψ₂ := ExS.get_of_ne_imm he₂ hg₂ hk₂
      by_cases hk₁ : ψ₁.kind = Kind.imm
      · obtain ⟨χ₁, hχ₁, -, -, -⟩ := AgW.get_imm haG hg₁ hk₁
        rcases hkey m with h | h
        · rw [h] at hex; cases hex
        · rw [h] at hχ₁; cases hχ₁
      · have hex₁ := ExS.get_of_ne_imm heG hg₁ hk₁
        rcases ResU.CompatS.disjoint_of_immFree himmG hce₂ m with h | h
        · rw [h] at hex₁; cases hex₁
        · rw [h] at hex; cases hex
  obtain ⟨X, hX⟩ := (ResU.compS_defined_iff G O).mpr hGO
  exact ⟨hGO, X, hX, σGO, (ResU.Flat.split hX).mpr
    ⟨eG, e₂, E, aG, a₂, A, heG, he₂, hE, haG, ha₂, hA, hσGO⟩⟩

/-! ### Building a mint: 6.64's cell, then one view at a time -/

/-- `ℓ ↦ imm(ψ) ○ ℓ ↦ own(ψ.erase) = ℓ ↦ imm(ψ)`. -/
theorem compR_single_imm_own {l : Loc} {ψ : CellU Loc Val} (_hk : ψ.kind = Kind.imm) :
    ResU.CompR (ResU.single l ψ) (ResU.single l (CellU.ownOf ψ.erase)) (ResU.single l ψ) := by
  classical
  refine ResU.Comp.of_pointwise (fun _ _ ψ hc => ⟨ψ, hc⟩) (fun m => ?_)
  by_cases hm : m = l
  · subst hm
    rw [ResU.single_get_self, ResU.single_get_self]
    exact ⟨ψ, rfl, CellU.compR_own_right_of_erase rfl⟩
  · rw [ResU.single_get_ne _ hm, ResU.single_get_ne _ hm]
    rfl

/-- `[TR]` 6.64's `ρᵢ = ℓ ↦ imm({α}, v, ρ_v)` is a mint over `ρ_v ● ℓ ↦ own(v)`. -/
theorem mint_single {α : Life} {l : Loc} {v : Val} {ρv W : WRes}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (hvW : ResU.Valid W) :
    Mint α W (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) := by
  refine ⟨fun m ψ e => ?_, fun eO heO m ψ e => ?_, fun eO aO aY heO haO haY => ?_, ?_⟩
  · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
    exact ⟨v, ρv, hv, rfl⟩
  · obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
    obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hW).mp heO
    obtain rfl := ExS.functional he₂ (ExW.single_own m v)
    have h₂ : (ResU.single m (CellU.ownOf v)).get m = some (CellU.ownOf v) :=
      ResU.single_get_self _ _
    exact ⟨_, (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hec) h₂ (by simp)).2, Or.inl rfl⟩
  · obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hW).mp heO
    obtain rfl := ExS.functional he₂ (ExW.single_own l v)
    obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgW.split hW).mp haO
    obtain rfl := AgW.functional ha₂ (AgW.single_own l v)
    have ha₁O : a₁ = aO := ResU.eq_of_comp_empty_right hac
    rw [ha₁O] at ha₁
    obtain ⟨ev, av, p₀, hev, hav, hp₀, hH⟩ := AgW.single_imm_inv haY
    rw [ExR.functional hev (ExS.toExR he₁), AgW.functional hav ha₁] at hp₀
    -- `p = ex(W) ○ ag(W) = ℓ ↦ own(v) ○ p₀`
    obtain ⟨σ, eW, aW, heW, haW, hcW⟩ := hvW
    rw [ExS.functional heW heO, AgW.functional haW haO] at hcW
    have hpR : ResU.CompR eO aO σ := ResU.CompS.toCompR hcW
    have hecR : ResU.CompR e₁ (ResU.single l (CellU.ownOf v)) eO := ResU.CompS.toCompR hec
    obtain ⟨x, hx, hxσ⟩ := (ResU.CompR.assoc (ResU.single l (CellU.ownOf v)) e₁ aO σ).mpr
      ⟨eO, ResU.CompR.comm hecR, hpR⟩
    rw [ResU.CompR.functional hx hp₀] at hxσ
    refine ⟨σ, hpR, ?_⟩
    -- `H ○ (L ○ p₀) = (H ○ L) ○ p₀ = H ○ p₀`
    have hHL := compR_single_imm_own (l := l)
      (ψ := CellU.immOf (LSet.singleton α) v ρv hv) rfl
    obtain ⟨y, hy, hyY⟩ := (ResU.CompR.assoc _ (ResU.single l (CellU.ownOf v)) p₀ aY).mpr
      ⟨_, hHL, hH⟩
    rw [ResU.CompR.functional hy hxσ] at hyY
    exact hyY
  · obtain ⟨-, ρ₀, hρ₀, σ, e, a, he, ha, hc⟩ :=
      ResU.six34 (s := LSet.singleton α) (hs := hv) hW
        (ResU.hash_symm (ResU.hash_empty_right hvW))
    have h₀ := ResU.eq_of_comp_empty_left hρ₀
    subst h₀
    exact ⟨a, ha⟩

/-- A `○`-factor of a composite that is `own(u)` at `m` is `own(u)` or absent there. -/
theorem compR_factor_own {a b c : WRes} (h : ResU.CompR a b c) {m : Loc} {u : Val}
    (hc : c.get m = some (CellU.ownOf u)) :
    a.get m = none ∨ a.get m = some (CellU.ownOf u) := by
  rcases ResU.Comp.get h m with ⟨f, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · exact Or.inl f
  · rw [hc] at f; cases Option.some.inj f; exact Or.inr f₁
  · exact Or.inl f₁
  · rw [hc] at f; cases Option.some.inj f
    have hk : χ₁.kind = Kind.own := by
      by_contra hne
      exact (CellU.CompR.nonown_left hC hne).1 rfl
    rw [f₁, CellU.eq_ownOf_of_kind hk, ← CellU.CompR.erase_left hC]
    exact Or.inr rfl

/-- The flattening `⦇O⦈` of a valid `O`, at `○`, carries `ex(O)`'s `own` cells. -/
theorem flat_own_of_ex {O σ eO : WRes} (hσ : ResU.Flat O σ) (heO : ExS O eO) {m : Loc} {u : Val}
    (h : eO.get m = some (CellU.ownOf u)) : σ.get m = some (CellU.ownOf u) := by
  obtain ⟨e, a, he, ha, hc⟩ := hσ
  rw [ExS.functional he heO] at hc
  exact (ResU.CompS.get_left_of_ne_imm hc h (by simp)).2

/-- The flattening carries every cell of `ex(O)`. -/
theorem flat_of_ex_cell {O σ eO : WRes} (hσ : ResU.Flat O σ) (heO : ExS O eO) {m : Loc}
    {c : CellU Loc Val} (h : eO.get m = some c) : σ.get m = some c := by
  obtain ⟨e, a, he, ha, hc⟩ := hσ
  rw [ExS.functional he heO] at hc
  exact (ResU.CompS.get_left_of_ne_imm hc h (ExS.immFree heO m c h)).2

/-- `⦇w⦈_○` is a `○`-factor of `⦇O⦈` when `w ≤ O`. -/
theorem flatR_le_of_le {w O σ : WRes} (hwO : ResU.Le w O) (hσ : ResU.Flat O σ)
    {f : WRes} (hf : ResU.FlatR w f) : ∃ z, ResU.CompR f z σ := by
  obtain ⟨r, hr⟩ := hwO
  obtain ⟨eO, aO, heO, haO, hcO⟩ := hσ
  obtain ⟨ew, er, hew, her, hec⟩ := (ExS.split hr).mp heO
  obtain ⟨aw, ar, haw, har, hac⟩ := (AgW.split hr).mp haO
  obtain ⟨a', e', ha', he', hf'⟩ := hf
  rw [AgW.functional ha' haw, ExR.functional he' (ExS.toExR hew)] at hf'
  obtain ⟨S₁, S₂, h₁, h₂, h₃⟩ := (ResU.CompR.exchange₄ ew er aw ar σ).mp
    ⟨eO, aO, ResU.CompS.toCompR hec, hac, ResU.CompS.toCompR hcO⟩
  rw [ResU.CompR.functional h₁ (ResU.CompR.comm hf')] at h₃
  exact ⟨S₂, h₃⟩

/-- A `○`-factor of a composite with a non-`imm` cell `M` at `m` holds, there, nothing or a
non-`imm` cell over `M`'s value, which is `mut` only over `M`'s witness when `M` is `mut`. -/
theorem compR_factor_nonimm {a b c : WRes} (h : ResU.CompR a b c) {m : Loc}
    {M : CellU Loc Val} (hk : M.kind ≠ Kind.imm) (hc : c.get m = some M) :
    a.get m = none ∨ ∃ ψ, a.get m = some ψ ∧ ψ.kind ≠ Kind.imm ∧ ψ.erase = M.erase ∧
      (ψ.kind = Kind.mut → M.kind = Kind.mut ∧ ψ.wit = M.wit) := by
  rcases ResU.Comp.get h m with ⟨f, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · exact Or.inl f
  · rw [hc] at f
    have hχ : χ = M := (Option.some.inj f).symm
    rw [hχ] at f₁
    exact Or.inr ⟨M, f₁, hk, rfl, fun k => ⟨k, rfl⟩⟩
  · exact Or.inl f₁
  · rw [hc] at f
    have hχ : χ = M := (Option.some.inj f).symm
    rw [hχ] at hC
    refine Or.inr ⟨χ₁, f₁, fun k₁ => hk ?_, (CellU.CompR.erase hC).2.symm, fun k₁ => ?_⟩
    · exact (CellU.CompR.imm_left hC k₁).1
    · cases hC with
      | same => exact ⟨k₁, rfl⟩
      | strict k =>
          have := (CellU.CompatS.kinds k).1
          rw [k₁] at this; cases this
      | mutMut a b v ρ ha hb P Q hP hQ => exact ⟨by simp, by simp⟩
      | mutOwn => exact ⟨k₁, rfl⟩
      | ownMut => simp at k₁
      | immOwn => simp at k₁
      | ownImm => simp at k₁
      | immMut => simp at k₁
      | mutImm => simp at hk

/-- A factor cell over a base cell's value (and witness, if `mut`) is a base cell too. -/
theorem base_of_factor {ψ b₀ c : CellU Loc Val} (hb : Base ψ b₀) (hk : c.kind ≠ Kind.imm)
    (he : c.erase = b₀.erase) (hw : c.kind = Kind.mut → b₀.kind = Kind.mut ∧ c.wit = b₀.wit) :
    Base ψ c := by
  rcases CellU.rep c with ⟨u, rfl⟩ | ⟨s, u, χ, h', rfl⟩ | ⟨b, u, χ, h', P, hP, rfl⟩
  · left
    have hu : u = b₀.erase := by simpa using he
    rw [hu.trans hb.erase_eq]
  · simp at hk
  · obtain ⟨k₀, hw₀⟩ := hw (by simp)
    rcases hb with rfl | ⟨-, e₀, w₀⟩
    · simp at k₀
    · exact Or.inr ⟨by simp, he.trans e₀, hw₀.trans w₀⟩

/-- **One more view, over any base cell.**  Adding to a mint `Y` over `O` the view
`m ↦ imm({α}, u, w)` of a cell `b₀` of `ex(O)` it may sit on (`Base`: `own(u)`, or a `mut` cell
over `u` and `w`) that `Y` does not hold, whose witness's walk is a `○`-factor of `⦇O⦈`, gives a
mint. -/
theorem Mint.addBase (hM : Mint α O Y) (hvO : ResU.Valid O) {m : Loc} {u : Val} {w : WRes}
    {h : w.InStratum (LSet.singleton α).join} {b₀ : CellU Loc Val}
    (hbase : Base (CellU.immOf (LSet.singleton α) u w h) b₀)
    (hm : ∀ eO, ExS O eO → eO.get m = some b₀) (hYm : Y.get m = none)
    {σw : WRes} (hfw : ResU.FlatR w σw) (hfac : ∀ σ, ResU.Flat O σ → ∃ z, ResU.CompR σw z σ) :
    ∃ Y', ResU.CompS Y (ResU.single m (CellU.immOf (LSet.singleton α) u w h)) Y' ∧
      Mint α O Y' := by
  classical
  set c := ResU.single m (CellU.immOf (LSet.singleton α) u w h) with hcdef
  have hYc : ResU.CompatS Y c := ResU.Compat.of_disjoint (fun m' => by
    by_cases hm' : m' = m
    · exact Or.inl (hm' ▸ hYm)
    · exact Or.inr (ResU.single_get_ne _ hm'))
  obtain ⟨Y', hY'⟩ := (ResU.compS_defined_iff Y c).mpr hYc
  -- `⦇O⦈`, the `p` of every clause
  obtain ⟨σ, hσ⟩ := hvO
  obtain ⟨eO₀, aO₀, heO₀, haO₀, hcO₀⟩ := hσ
  have hσR : ResU.CompR eO₀ aO₀ σ := ResU.CompS.toCompR hcO₀
  have hσflat : ResU.Flat O σ := ⟨eO₀, aO₀, heO₀, haO₀, hcO₀⟩
  -- `⦇w⦈_○`, a factor of `σ`
  obtain ⟨z, hz⟩ := hfac σ hσflat
  have hσσw : ResU.CompR σw σ σ := ResU.CompR.absorb hz
  -- the cells of `Y′`
  have hcell : ∀ m' ψ, Y'.get m' = some ψ →
      (Y.get m' = some ψ) ∨ (m' = m ∧ ψ = CellU.immOf (LSet.singleton α) u w h) := by
    intro m' ψ e
    rcases ResU.Comp.get hY' m' with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, f₂, f, -⟩
    · rw [f] at e; cases e
    · rw [f] at e; cases Option.some.inj e; exact Or.inl f₁
    · rw [f] at e; cases Option.some.inj e
      obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some f₂; exact Or.inr ⟨rfl, rfl⟩
    · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some f₂; rw [hYm] at f₁; cases f₁
  have hY'own : ∀ m' ψ, Y'.get m' = some ψ →
      ψ.kind = Kind.imm ∧ ∃ c, σ.get m' = some c ∧ Base ψ c := by
    intro m' ψ e
    rcases hcell m' ψ e with h' | ⟨rfl, rfl⟩
    · obtain ⟨c, hc, hbase⟩ := hM.own eO₀ heO₀ m' ψ h'
      exact ⟨hM.kind h', c, flat_of_ex_cell hσflat heO₀ hc, hbase⟩
    · exact ⟨rfl, _, flat_of_ex_cell hσflat heO₀ (hm eO₀ heO₀), hbase⟩
  -- `aY`, `ac` and `aY ○ ac`
  obtain ⟨aY, haY⟩ := hM.agDef
  obtain ⟨p₁, hp₁, hYp₁⟩ := hM.ag eO₀ aO₀ aY heO₀ haO₀ haY
  rw [ResU.CompR.functional hp₁ hσR] at hYp₁
  have hcσw : ResU.CompatR c σw := by
    intro m' ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₁
    have hσm := flat_of_ex_cell hσflat heO₀ (hm eO₀ heO₀)
    rcases compR_factor_nonimm hσσw hbase.ne_imm hσm with h' | ⟨ψ, hψ, hkψ, heψ, hwψ⟩
    · rw [h'] at e₂; cases e₂
    · rw [hψ] at e₂; cases Option.some.inj e₂
      exact ⟨_, (base_of_factor hbase hkψ heψ hwψ).absorb rfl⟩
  obtain ⟨ac, hac⟩ := (ResU.compR_defined_iff c σw).mpr hcσw
  have hagc : AgW c ac := AgW.single_imm hfw hac
  obtain ⟨C', hC', -, -⟩ := compR_imm_own_absorb hY'own
  have hYcR : ResU.CompR Y c Y' := ResU.CompS.toCompR hY'
  obtain ⟨A, B, hA, hB, hAB⟩ := (ResU.CompR.exchange₄ Y σ c σw C').mpr
    ⟨Y', σ, hYcR, ResU.CompR.comm hσσw, hC'⟩
  rw [ResU.CompR.functional hA hYp₁, ResU.CompR.functional hB hac] at hAB
  have hagY' : AgW Y' C' := (AgW.split hY').mpr ⟨aY, ac, haY, hagc, hAB⟩
  refine ⟨Y', hY', ⟨fun m' ψ e => ?_, fun eO heO m' ψ e => ?_, fun eO aO aY' heO haO haY' => ?_,
    ⟨C', hagY'⟩⟩⟩
  · rcases hcell m' ψ e with h' | ⟨rfl, rfl⟩
    · exact hM.cell m' ψ h'
    · exact ⟨u, w, h, rfl⟩
  · rcases hcell m' ψ e with h' | ⟨rfl, rfl⟩
    · exact hM.own eO heO m' ψ h'
    · exact ⟨_, hm eO heO, hbase⟩
  · rw [ExS.functional heO heO₀, AgW.functional haO haO₀, AgW.functional haY' hagY']
    exact ⟨σ, hσR, hC'⟩

/-- `Mint.addBase` at an `own(u)` cell: `[TR]` 6.64's lineage. -/
theorem Mint.add (hM : Mint α O Y) (hvO : ResU.Valid O) {m : Loc} {u : Val} {w : WRes}
    {h : w.InStratum (LSet.singleton α).join}
    (hm : ∀ eO, ExS O eO → eO.get m = some (CellU.ownOf u)) (hYm : Y.get m = none)
    {σw : WRes} (hfw : ResU.FlatR w σw) (hfac : ∀ σ, ResU.Flat O σ → ∃ z, ResU.CompR σw z σ) :
    ∃ Y', ResU.CompS Y (ResU.single m (CellU.immOf (LSet.singleton α) u w h)) Y' ∧
      Mint α O Y' :=
  hM.addBase hvO (Or.inl rfl) hm hYm hfw hfac

/-- **The second base case: a view over a `mut` cell's value.**  The target of a frozen
`Mut`: the view `m ↦ imm({α}, u, w)` sits on `mut(b, u, w, P̂)` in `ex(O)`, with the `mut`
cell's own witness. -/
theorem Mint.addMut (hM : Mint α O Y) (hvO : ResU.Valid O) {m : Loc} {u : Val} {w : WRes}
    {h : w.InStratum (LSet.singleton α).join} {b : Life} {hb : w.InStratum b}
    {P : Val → SPropS Loc Val b} {hP : P u ⟨w, hb⟩}
    (hm : ∀ eO, ExS O eO → eO.get m = some (CellU.mutOf b u w hb P hP)) (hYm : Y.get m = none)
    {σw : WRes} (hfw : ResU.FlatR w σw) (hfac : ∀ σ, ResU.Flat O σ → ∃ z, ResU.CompR σw z σ) :
    ∃ Y', ResU.CompS Y (ResU.single m (CellU.immOf (LSet.singleton α) u w h)) Y' ∧
      Mint α O Y' :=
  hM.addBase hvO (Or.inr ⟨by simp, by simp, by simp⟩) hm hYm hfw hfac

/-- `Mint.add` at a witness `w ≤ O`, the form 6.64's lineage uses. -/
theorem Mint.add_le (hM : Mint α O Y) (hvO : ResU.Valid O) {m : Loc} {u : Val} {w : WRes}
    {h : w.InStratum (LSet.singleton α).join}
    (hm : ∀ eO, ExS O eO → eO.get m = some (CellU.ownOf u)) (hYm : Y.get m = none)
    (hwO : ResU.Le w O) :
    ∃ Y', ResU.CompS Y (ResU.single m (CellU.immOf (LSet.singleton α) u w h)) Y' ∧
      Mint α O Y' := by
  obtain ⟨σ, hσ⟩ := hvO
  have hvw : ResU.Valid w := by
    obtain ⟨r, hr⟩ := hwO; exact (ResU.Valid.split hr ⟨σ, hσ⟩).1
  obtain ⟨σw, hσw⟩ := hvw
  have hfw : ResU.FlatR w σw := ResU.six33 hσw
  exact hM.add ⟨σ, hσ⟩ hm hYm hfw (fun σ' hσ' => flatR_le_of_le hwO hσ' hfw)

/-! ### What `↭` keeps under an `imm` cell -/

/-- **Frozen under an `imm` ancestor.**  If `ρ ↭ π` and `⦇ρ⦈` holds an `imm` cell over the
witness `w`, every cell of `w`'s walk `⦇w⦈_○` is still there in `⦇π⦈`, with its value: what an
`imm` cell reaches through owned pointers is frozen by every run, at every valid resource.
This is RustBelt's persistence of a sharing predicate, and it is `[TR]` p. 5's `↭` clause (1)
with the ancestor accounting of 6.48's proof (`ResU.flat_imm_wit_factor`).  The views a mint
adds are `imm` cells over such walks. -/
theorem frozen_under_imm {ρ π σ τ : WRes} (hupd : ResU.UpdV ρ π) (hσ : ResU.Flat ρ σ)
    (hτ : ResU.Flat π τ) {l : Loc} {s : LSet} {v : Val} {w : WRes} {h : w.InStratum s.join}
    (hc : σ.get l = some (CellU.immOf s v w h)) {f : WRes} (hf : ResU.FlatR w f) {m : Loc}
    {ψ : CellU Loc Val} (hm : f.get m = some ψ) :
    ∃ χ, τ.get m = some χ ∧ χ.erase = ψ.erase := by
  have hτl : τ.get l = some (CellU.immOf s v w h) :=
    (ResU.flatAt_iff hτ _ _).mp ((hupd.1.1 l s v w h).mp ((ResU.flatAt_iff hσ _ _).mpr hc))
  obtain ⟨eπ, aπ, heπ, haπ, hcπ⟩ := hτ
  obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ :=
    ResU.flat_imm_wit_factor heπ haπ hcπ hτl
  obtain rfl : f = p := ResU.FlatR.functional hf ⟨av, ev, hav, hev, ResU.CompR.comm hp⟩
  obtain ⟨χ, eχ, heχ⟩ : ∃ χ, aπ.get m = some χ ∧ χ.erase = ψ.erase := by
    rcases ResU.Comp.get hz m with ⟨g, -, -⟩ | ⟨χ, g₁, -, g⟩ | ⟨χ, g₁, -, -⟩ |
        ⟨χ₁, χ₂, χ, g₁, -, g, hC⟩
    · rw [g] at hm; cases hm
    · rw [g₁] at hm; cases Option.some.inj hm; exact ⟨_, g, rfl⟩
    · rw [g₁] at hm; cases hm
    · rw [g₁] at hm; cases Option.some.inj hm; exact ⟨_, g, CellU.CompR.erase_left hC⟩
  have heπm : eπ.get m = none := by
    cases e : eπ.get m with
    | none => rfl
    | some ξ =>
        have := ResU.CompatS.right_eq_none hcπ.1 e (ExS.immFree heπ m ξ e)
        rw [eχ] at this; cases this
  exact ⟨χ, (ResU.Comp.get_of_left_none hcπ heπm).trans eχ, heχ⟩

end BoCa.MintProbe

end
