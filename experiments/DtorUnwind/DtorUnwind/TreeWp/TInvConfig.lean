import DtorUnwind.TreeWp.FdEscCactus
import DtorUnwind.TreeWp.TInvBase

/-!
# `TIT` at a world with a record and a reborrow

`cactusT_config`'s world (`TreeWp/FdEscCactus.lean`): `ℓ ↦ imm({α}, loc m, m ↦ own(()))`, the
record `(ℓ, loc m, m ↦ own(()), ref 1)` proper and in the lineage list, and the record's
canonical image `m ↦ imm({β}, (), ∅)` at `β ⊏ α`. `twnt_config` makes it a `TWNT` world;
`tit_config` shows it satisfies `TIT`. The record's one chain is `m` from `(ref 1, loc m)`
(`chain_recE`); the view at `m` is the image, typed at `1` over `∅`, the escrow with `m`
removed; no cell of the world is `mut` at any depth.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-- The record's chains: `m` from `(ref 1, loc m)`, with no step. -/
theorem chain_recE {K : WCactus} {m : BoCa.Loc} {p : Option BoCa.Loc} {x : BoCa.Loc}
    {S : KTy} {u : BoCa.Val}
    (h : ChainT (escR (K := K) m) (KTy.ref KTy.unit) (BoCa.Val.loc m) p x S u) :
    p = none ∧ x = m ∧ S = KTy.unit ∧ u = BoCa.Val.unit := by
  cases h with
  | one hr e =>
      cases hr
      rw [escR, ResUT.single_get_self] at e
      cases e; exact ⟨rfl, rfl, rfl, rfl⟩
  | step hr e hc =>
      cases hr
      rw [escR, ResUT.single_get_self] at e
      cases e
      cases hc with
      | one hr' _ => cases hr'
      | step hr' _ _ => cases hr'

/-- Every cell of the configuration's world is `imm` over a witness of `own` cells. -/
theorem config_cells {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) {x : BoCa.Loc}
    {ψ : TCell KC} (e : W.get x = some ψ) :
    ψ.kind = Kind.imm ∧ ∀ y (χ : TCell KC), ψ.wit.get y = some χ → χ.kind = Kind.own := by
  rcases compS_back hW e with ⟨ψ₀, e₀, k₀, w₀⟩ | ⟨ψ₀, e₀, k₀, w₀⟩
  · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
    refine ⟨k₀.symm.trans (CellUT.kind_immOf _ _ _ _), fun y χ ey => ?_⟩
    have ew : (lendCell (K := KC) αC mC).wit = escR mC := CellUT.wit_immOf _ _ _ _
    rw [← w₀, ew, escR] at ey
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some ey
    rfl
  · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
    refine ⟨k₀.symm.trans (CellUT.kind_immOf _ _ _ _), fun y χ ey => ?_⟩
    have ew : (viewCell (K := KC) βC).wit = PMap.empty := CellUT.wit_immOf _ _ _ _
    rw [← w₀, ew] at ey
    simp at ey

/-- The configuration's world holds cells at `ℓ` and `m` only, at any depth. -/
theorem config_dom {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) {x : BoCa.Loc}
    {ψ : TCell KC} (h : CellAt W x ψ) (hx : x ≠ ℓC) (hm : x ≠ mC) : False := by
  have top : ∀ {y} {χ : TCell KC}, W.get y = some χ → y = ℓC ∨ y = mC := by
    intro y χ e
    rcases compS_back hW e with ⟨ψ₀, e₀, -⟩ | ⟨ψ₀, e₀, -⟩
    · exact .inl (ResUT.single_get_eq_some e₀).1
    · exact .inr (ResUT.single_get_eq_some e₀).1
  cases h with
  | top e => rcases top e with rfl | rfl <;> simp_all
  | nest e hc =>
      have hown := (config_cells hW e).2
      cases hc with
      | top e' =>
          rcases compS_back hW e with ⟨ψ₀, e₀, -, w₀⟩ | ⟨ψ₀, e₀, -, w₀⟩
          · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
            have ew : (lendCell (K := KC) αC mC).wit = escR mC := CellUT.wit_immOf _ _ _ _
            rw [← w₀, ew, escR] at e'
            exact hm (ResUT.single_get_eq_some e').1
          · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
            have ew : (viewCell (K := KC) βC).wit = PMap.empty := CellUT.wit_immOf _ _ _ _
            rw [← w₀, ew] at e'
            simp at e'
      | nest e' hc' =>
          rename_i y χ₁
          have hk := hown _ _ e'
          rcases CellUT.rep' χ₁ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, _, v, χ, hb, P, hP, rfl⟩
          · rw [CellUT.wit_ownOf] at hc'
            exact CellAt.not_empty hc'
          · simp at hk
          · simp [CellUT.mutOf, CellUT.kind] at hk

/-- No `mut` cell at any depth in the configuration's world. -/
theorem config_noMut {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) (x : BoCa.Loc) :
    ¬ MutAtT W x := by
  intro h
  cases h with
  | top e hk =>
      rw [(config_cells hW e).1] at hk; cases hk
  | nest e _ hw =>
      have hown := (config_cells hW e).2
      cases hw with
      | top e' hk' => rw [hown _ _ e'] at hk'; cases hk'
      | nest e' hk' _ => exact hk' (hown _ _ e')

/-- **`TIT` at the configuration**: the `TWNT` world of `twnt_config` with its record proper and
in the lineage list, after the reborrow at `β ⊏ α`, satisfies every clause of `TIT`. -/
theorem tit_config (Θ : CodeTy) {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) :
    TIT KC Θ W [recE ℓC mC] [recE ℓC mC] := by
  have hag := fun {a : TRes KC} (ha : AgWT W a) => ag_config hW ha
  have hR : (recE (K := KC) ℓC mC).R = escR mC := rfl
  refine ⟨⟨?deep, ?own, ?uniq, ?typed, ?jat, ?jdeep⟩, ?le, ?psu, ?notR, ?nest, ?nm, ?desc, ?cov⟩
  case deep =>
    intro r hr p x S u hc a ha ψ e hk
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := chain_recE hc
    rw [(hag ha).2] at e; cases Option.some.inj e
    have ew : (viewCell (K := KC) βC).wit = PMap.empty := CellUT.wit_immOf _ _ _ _
    refine ⟨CellUT.kind_immOf _ _ _ _, ?_, ?_, fun _ => ?_, fun l₀ h => by cases h⟩
    · rw [ew]; exact ⟨rfl, rfl⟩
    · intro m' w hw; rw [ew] at hw; simp at hw
    · exact ⟨escR mC, ResUT.Le.refl _, ⟨_, ResUT.single_get_self _ _⟩, by rw [ew, escR_del]⟩
  case own =>
    intro r hr x u e a ha
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨rfl, -⟩ := ResUT.single_get_eq_some e
    exact ⟨_, (hag ha).2⟩
  case uniq =>
    intro r₁ h₁ r₂ h₂ _ _ _ _ _
    simp only [List.mem_singleton] at h₁ h₂; rw [h₁, h₂]
  case typed =>
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact escR_typed Θ mC
  case jat =>
    intro r hr _
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨βC, viewRes βC mC, view_reb βC mC, view_typed Θ βC mC,
      ⟨_, (agW_of_valid (valid_view βC mC)).choose_spec⟩, ?_⟩
    intro S x u hroot a ha ψ e _
    obtain ⟨hp, -⟩ := hroot
    cases hp
    rw [(hag ha).2] at e; cases Option.some.inj e
    exact ⟨_, ResUT.single_get_self _ _, rfl⟩
  case jdeep =>
    intro r hr p₀ l₀ S₀ u₀ _ hex
    simp only [List.mem_singleton] at hr; subst hr
    obtain ⟨x, S, u, hc, -⟩ := hex
    cases (chain_recE hc).1
  case le =>
    intro r hr a ha
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, (hag ha).1, CellUT.kind_immOf _ _ _ _, rfl, CellUT.wit_immOf _ _ _ _⟩
  case psu =>
    intro r₁ h₁ r₂ h₂ _
    simp only [List.mem_singleton] at h₁ h₂; rw [h₁, h₂]
  case notR =>
    intro r hr r' hr' u e
    simp only [List.mem_singleton] at hr hr'; subst hr; subst hr'
    change (escR (K := KC) mC).get ℓC = _ at e
    rw [escR, ResUT.single_get_ne _ ℓC_ne_mC] at e; cases e
  case nest =>
    intro r hr l₀ x S u hc
    simp only [List.mem_singleton] at hr; subst hr
    cases (chain_recE hc).1
  case nm =>
    exact ⟨fun _ _ => config_noMut hW _, fun _ _ _ _ _ => config_noMut hW _⟩
  case desc =>
    intro x
    simp only [List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨_, rfl, ⟨[], .nil _⟩⟩
    · rintro ⟨p, rfl, q, hq⟩
      cases hq with
      | nil => rfl
      | cons hs _ =>
          rename_i d _ _
          exact absurd ⟨_, List.cons_ne_nil _ _, LinPathT.cons hs (LinPathT.nil d)⟩
            (recE_no_desc ℓC mC d)
  case cov =>
    intro a ha x ψ e _
    by_cases hx : x = ℓC
    · subst hx
      rw [(hag ha).1] at e; cases Option.some.inj e
      exact .inl ⟨_, List.mem_singleton_self _, rfl, rfl, CellUT.wit_immOf _ _ _ _⟩
    · by_cases hm : x = mC
      · subst hm
        exact .inr ⟨_, List.mem_singleton_self _, none, KTy.unit, BoCa.Val.unit,
          .one (.ref _ _) (ResUT.single_get_self _ _)⟩
      · exfalso
        obtain ⟨ψ₀, hc, -⟩ := agW_cellAt ha x ψ e (by rw [‹ψ.kind = Kind.imm›]; simp)
        exact config_dom hW hc hx hm

/-- **`TIT` holds at a reachable world with a record and a reborrow**: `twnt_config`'s world. -/
theorem tit_twnt_config (Θ : CodeTy) :
    ∃ W, ResUT.CompS parentRes childRes W ∧
      TWNT KC Θ (tmplT KC Θ) W [recE ℓC mC] [recE ℓC mC] ∧
      TIT KC Θ W [recE ℓC mC] [recE ℓC mC] := by
  obtain ⟨W, hW, hT⟩ := twnt_config (K := KC) Θ βC_lt_αC ℓC_ne_mC
  exact ⟨W, hW, hT, tit_config Θ hW⟩

end BoCa.Fig16.Tree.Wp

end
