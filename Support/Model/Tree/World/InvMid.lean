import Support.Model.Tree.World.InvBase

/-!
# Exclusive paths and lineages over the tree carrier

`[spec §62]`. `Core/Invariant.lean`'s paths through `mut` witnesses (`XPath`, `xpath_unique`,
`xpath_ex`), the lifting of a cell through `○` (`Lifts`), a lineage's exclusive part (`ExIn`,
`LeInvW`, `TI.exIn`, `TI.leInvW`), and the framed world's exclusive part (`frame_ex`,
`frame_new_root'`), over the tree carrier with records at codes.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus} {Θ : CodeTy}

theorem ag_none_of_top {W a : TRes K} (hv : ResUT.Valid W) (ha : AgWT W a) {m : BoCa.Loc}
    {φ : TCell K} (e : W.get m = some φ) (hk : φ.kind ≠ Kind.imm) : a.get m = none := by
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  cases e' : a.get m with
  | none => rfl
  | some ζ =>
      rw [AgWT.functional haW ha] at hc
      exact (ex_ag_disjoint ⟨σ, eW, a, heW, ha, hc⟩ heW ha (ExST.get_of_ne_imm heW e hk) e').elim

inductive XPath : TRes K → List BoCa.Loc → TRes K → Prop
  | nil (ρ : TRes K) : XPath ρ [] ρ
  | cons {ρ σ : TRes K} {m : BoCa.Loc} {ψ : TCell K} {p : List BoCa.Loc} :
      ρ.get m = some ψ → ψ.kind = Kind.mut → XPath ψ.wit p σ → XPath ρ (m :: p) σ

/-- A non-`imm` cell of a member of a `●`-fold is the fold's. -/
theorem bigComp_get_of_ne_imm {L : List (TRes K)} {b : TRes K}
    (hb : BigCompT CellUT.CompatS CellUT.CompS L b) {τ : TRes K} (hτ : τ ∈ L) {x : BoCa.Loc}
    {ζ : TCell K} (e : τ.get x = some ζ) (hk : ζ.kind ≠ Kind.imm) : b.get x = some ζ := by
  obtain ⟨z, hz⟩ := BigCompT.mem_factor hSS ResUT.compLawsS hb τ hτ
  exact (ResUT.CompS.get_left_of_ne_imm hz e hk).2

/-- Two entries of a `●`-fold at different sites carry no non-`imm` cell at one location. -/
theorem bigComp_two {x : BoCa.Loc} :
    ∀ {w : List (BoCa.Loc × TRes K)} {b : TRes K}, BigCompT CellUT.CompatS CellUT.CompS (w.map Prod.snd) b →
      ∀ {q₁ q₂ : BoCa.Loc × TRes K}, q₁ ∈ w → q₂ ∈ w → q₁.1 ≠ q₂.1 →
      ∀ {ζ₁ ζ₂ : TCell K}, q₁.2.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm →
      q₂.2.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm → False
  | [], _, _, _, _, h₁, _, _, _, _, _, _, _, _ => absurd h₁ (by simp)
  | a :: w, b, hb, q₁, q₂, h₁, h₂, hne, ζ₁, ζ₂, e₁, k₁, e₂, k₂ => by
      cases hb with
      | cons hrest hc =>
          rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
          · exact hne rfl
          · have := bigComp_get_of_ne_imm hrest (List.mem_map.mpr ⟨_, h₂', rfl⟩) e₂ k₂
            rw [ResUT.CompatS.right_eq_none hc.1 e₁ k₁] at this; cases this
          · have := bigComp_get_of_ne_imm hrest (List.mem_map.mpr ⟨_, h₁', rfl⟩) e₁ k₁
            rw [ResUT.CompatS.right_eq_none hc.1 e₂ k₂] at this; cases this
          · exact bigComp_two hrest h₁' h₂' hne e₁ k₁ e₂ k₂

/-- A non-`imm` cell reached through `mut` witnesses is a cell of `ex(ρ)_●`. -/
theorem xpath_ex {ρ e : TRes K} (h : ExST ρ e) :
    ∀ {p : List BoCa.Loc} {σ : TRes K}, XPath ρ p σ → ∀ {x : BoCa.Loc} {ζ : TCell K},
      σ.get x = some ζ → ζ.kind ≠ Kind.imm → e.get x = some ζ := by
  refine G.ExW.rec (motive_1 := fun ρ e _ => ∀ {p : List BoCa.Loc} {σ : TRes K}, XPath ρ p σ →
      ∀ {x : BoCa.Loc} {ζ : TCell K}, σ.get x = some ζ → ζ.kind ≠ Kind.imm → e.get x = some ζ)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ ψ : TCell K, ρ.get q.1 = some ψ →
      ∀ {p : List BoCa.Loc} {σ : TRes K}, XPath ψ.wit p σ →
      ∀ {x : BoCa.Loc} {ζ : TCell K}, σ.get x = some ζ → ζ.kind ≠ Kind.imm → q.2.get x = some ζ)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ σ nm b w hs hw hb hnm hσ ih p τ hp x ζ ex kx
    cases hp with
    | nil => exact ExST.get_of_ne_imm (G.ExW.mk hs hw hb hnm hσ) ex kx
    | @cons _ _ m ψ q em km hq =>
        obtain ⟨pr, hpr, hpr1⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, em, km⟩)
        have e₁ := ih pr hpr ψ (hpr1 ▸ em) hq ex kx
        have e₂ := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨pr, hpr, rfl⟩) e₁ kx
        exact (ResUT.CompS.get_right_of_ne_imm hσ e₂ kx).2
  case nil => intro ρ q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ e l w ψ hψ hk he hw ihe ihw q hq ψ' eψ' p σ hp x ζ ex kx
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [hψ] at eψ'; cases Option.some.inj eψ'
      exact ihe hp ex kx
    · exact ihw q hq ψ' eψ' hp ex kx

/-- …at one path only. -/
theorem xpath_unique {ρ e : TRes K} (h : ExST ρ e) :
    ∀ {p₁ : List BoCa.Loc} {σ₁ : TRes K}, XPath ρ p₁ σ₁ → ∀ {p₂ : List BoCa.Loc} {σ₂ : TRes K},
      XPath ρ p₂ σ₂ → ∀ {x : BoCa.Loc} {ζ₁ ζ₂ : TCell K},
      σ₁.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm → σ₂.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm →
      p₁ = p₂ := by
  refine G.ExW.rec (motive_1 := fun ρ e _ => ∀ {p₁ : List BoCa.Loc} {σ₁ : TRes K}, XPath ρ p₁ σ₁ →
      ∀ {p₂ : List BoCa.Loc} {σ₂ : TRes K}, XPath ρ p₂ σ₂ → ∀ {x : BoCa.Loc} {ζ₁ ζ₂ : TCell K},
      σ₁.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm → σ₂.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm →
      p₁ = p₂)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∃ ψ : TCell K, ρ.get q.1 = some ψ ∧
      ExST ψ.wit q.2 ∧ ∀ {p₁ : List BoCa.Loc} {σ₁ : TRes K}, XPath ψ.wit p₁ σ₁ →
      ∀ {p₂ : List BoCa.Loc} {σ₂ : TRes K}, XPath ψ.wit p₂ σ₂ → ∀ {x : BoCa.Loc} {ζ₁ ζ₂ : TCell K},
      σ₁.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm → σ₂.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm →
      p₁ = p₂)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ σ nm b w hs hw hb hnm hσ ih p₁ σ₁ h₁ p₂ σ₂ h₂ x ζ₁ ζ₂ e₁ k₁ e₂ k₂
    -- a path through `mut` site `m` puts `x` in `b`
    have viaB : ∀ {m : BoCa.Loc} {ψ : TCell K} {q : List BoCa.Loc} {τ : TRes K} {ζ : TCell K},
        ρ.get m = some ψ → ψ.kind = Kind.mut → XPath ψ.wit q τ → τ.get x = some ζ →
        ζ.kind ≠ Kind.imm → ∃ pr ∈ w, pr.1 = m ∧ pr.2.get x = some ζ := by
      intro m ψ q τ ζ em km hq eτ kτ
      obtain ⟨pr, hpr, hpr1⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, em, km⟩)
      obtain ⟨ψ', eψ', hex, -⟩ := ih pr hpr
      rw [hpr1, em] at eψ'; cases Option.some.inj eψ'
      exact ⟨pr, hpr, hpr1, xpath_ex hex hq eτ kτ⟩
    have topNone : ∀ {ζ : TCell K}, ρ.get x = some ζ → ζ.kind ≠ Kind.imm →
        b.get x = none := by
      intro ζ eρ kρ
      have enm : nm.get x = some ζ := by
        cases hkk : ζ.kind with
        | own => exact (ResUT.CompS.get_left_of_ne_imm hnm (ResUT.restrict_get_some eρ hkk) kρ).2
        | imm => exact absurd hkk kρ
        | «mut» => exact (ResUT.CompS.get_right_of_ne_imm hnm (ResUT.restrict_get_some eρ hkk) kρ).2
      exact ResUT.CompatS.right_eq_none hσ.1 enm kρ
    cases h₁ with
    | nil =>
        cases h₂ with
        | nil => rfl
        | cons em km hq =>
            obtain ⟨pr, hpr, -, epr⟩ := viaB em km hq e₂ k₂
            have := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨pr, hpr, rfl⟩) epr k₂
            rw [topNone e₁ k₁] at this; cases this
    | @cons _ _ m₁ ψ₁ q₁ em₁ km₁ hq₁ =>
        cases h₂ with
        | nil =>
            obtain ⟨pr, hpr, -, epr⟩ := viaB em₁ km₁ hq₁ e₁ k₁
            have := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨pr, hpr, rfl⟩) epr k₁
            rw [topNone e₂ k₂] at this; cases this
        | @cons _ _ m₂ ψ₂ q₂ em₂ km₂ hq₂ =>
            obtain ⟨pr₁, hpr₁, hm₁, epr₁⟩ := viaB em₁ km₁ hq₁ e₁ k₁
            obtain ⟨pr₂, hpr₂, hm₂, epr₂⟩ := viaB em₂ km₂ hq₂ e₂ k₂
            by_cases hm : m₁ = m₂
            · subst hm
              rw [em₁] at em₂; cases Option.some.inj em₂
              have hpp : pr₁ = pr₂ :=
                List.inj_on_of_nodup_map hs.1 hpr₁ hpr₂ (hm₁.trans hm₂.symm)
              subst hpp
              obtain ⟨ψ', eψ', -, ihu⟩ := ih pr₁ hpr₁
              rw [hm₁, em₁] at eψ'; cases Option.some.inj eψ'
              rw [ihu hq₁ hq₂ e₁ k₁ e₂ k₂]
            · exact (bigComp_two hb hpr₁ hpr₂ (by rw [hm₁, hm₂]; exact hm) epr₁ k₁ epr₂ k₂).elim
  case nil => intro ρ q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨ψ, hψ, he, ihe⟩
    · exact ihw q hq

theorem not_mutAt_ex_own_aux {x : BoCa.Loc} {u : BoCa.Val} {ρ : TRes K} (h : MutAtT ρ x) :
    ∀ {eρ aρ : TRes K}, ExST ρ eρ → AgWT ρ aρ → eρ.get x = some (CellUT.ownOf u) →
      aρ.get x = none → False := by
  induction h with
  | top e hk =>
      intro eρ aρ he _ ho _
      rw [ExST.get_of_ne_imm he e (by rw [hk]; simp)] at ho
      cases Option.some.inj ho; exact absurd hk (by simp)
  | @nest ρ x m ψ e hk hmw ih =>
      intro eρ aρ he ha ho hn
      cases hkk : ψ.kind with
      | own => exact hk hkk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le ha e hkk
          rcases mutAt_walk_dom hmw hRR ResUT.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            rw [hn] at h2; cases h2
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            rw [hn] at h2; cases h2
      | «mut» =>
          obtain ⟨av, z, hav, hz⟩ := AgWT.mut_wit_le ha e hkk
          cases he with
          | mk hs hw hb hnm hσ =>
              rename_i nm b w
              obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, e, hkk⟩)
              obtain ⟨ψ', hψ', hex'⟩ := ExWitsT.mem hw q hq
              rw [hq₁, e] at hψ'
              cases Option.some.inj hψ'
              have avn : av.get x = none := by
                cases eav : av.get x with
                | none => rfl
                | some ζ =>
                    obtain ⟨_, h1⟩ := comp_some hz eav
                    rw [hn] at h1; cases h1
              rcases mutAt_walk_dom hmw hSS ResUT.compLawsS hex' hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
              · have kζ : ζ.kind ≠ Kind.imm := ExST.immFree hex' x ζ hζ
                have eb := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨q, hq, rfl⟩) hζ kζ
                have eσ := (ResUT.CompS.get_right_of_ne_imm hσ eb kζ).2
                rw [ho] at eσ; cases Option.some.inj eσ
                exact ih hex' hav hζ avn
              · rw [avn] at hζ; cases hζ

/-- An `own` cell of `ex(W)_●` is borrowed mutably nowhere in `W`.  `not_mutAt_top_own`
at every depth `ex` descends to. -/
theorem not_mutAt_ex_own {W e : TRes K} (hv : ResUT.Valid W) (he : ExST W e) {x : BoCa.Loc} {u : BoCa.Val}
    (hx : e.get x = some (CellUT.ownOf u)) : ¬ MutAtT W x := by
  intro hm
  obtain ⟨a, ha⟩ := agW_of_valid hv
  have hn : a.get x = none := by
    cases e' : a.get x with
    | none => rfl
    | some ζ => exact (ex_ag_disjoint hv he ha hx e').elim
  exact not_mutAt_ex_own_aux hm he ha hx hn

/-- `○` keeps the value of either operand, and the witness and non-`own`ness of a non-`own`
operand. -/
theorem CellUT.CompR.lift_full {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ψ.erase = ψ₁.erase ∧ (ψ₁.kind ≠ Kind.own → ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) := by
  cases h with
  | same => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | strict k =>
      obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := CellUT.compS_spec _ _ k
      rw [e₃, e₁]
      exact ⟨by simp, fun _ => ⟨by simp, by simp⟩⟩
  | mutMut => exact ⟨by simp, fun _ => ⟨by simp, by simp⟩⟩
  | mutOwn => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | ownMut => exact ⟨by simp, fun hk => absurd (by simp) hk⟩
  | immOwn => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | ownImm => exact ⟨by simp, fun hk => absurd (by simp) hk⟩
  | immMut => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | mutImm => exact ⟨by simp, fun _ => ⟨by simp, by simp⟩⟩

/-- `Lifts e a`: every cell of `e` has one in `a` at its location, over its value, and a
non-`own` one over its witness.  `[about ours: "is a `○`-part of", pointwise]` -/
def Lifts (e a : TRes K) : Prop :=
  ∀ x (ψ : TCell K), e.get x = some ψ → ∃ ζ : TCell K, a.get x = some ζ ∧
    ζ.erase = ψ.erase ∧ (ψ.kind ≠ Kind.own → ζ.kind ≠ Kind.own ∧ ζ.wit = ψ.wit)

theorem Lifts.trans {e b a : TRes K} (h₁ : Lifts e b) (h₂ : Lifts b a) : Lifts e a := by
  intro x ψ ex
  obtain ⟨ζ, eζ, rζ, wζ⟩ := h₁ x ψ ex
  obtain ⟨ξ, eξ, rξ, wξ⟩ := h₂ x ζ eζ
  refine ⟨ξ, eξ, rξ.trans rζ, fun hk => ?_⟩
  obtain ⟨k₁, w₁⟩ := wζ hk
  obtain ⟨k₂, w₂⟩ := wξ k₁
  exact ⟨k₂, w₂.trans w₁⟩

theorem lifts_left {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) : Lifts a₁ a := by
  intro x ψ e
  rcases ResUT.Comp.get h x with ⟨e₁, -, -⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, e₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, e₁, -, e', hC⟩
  · rw [e] at e₁; cases e₁
  · rw [e] at e₁; cases Option.some.inj e₁; exact ⟨_, e', rfl, fun hk => ⟨hk, rfl⟩⟩
  · rw [e] at e₁; cases e₁
  · rw [e] at e₁; cases Option.some.inj e₁
    exact ⟨χ, e', (CellUT.CompR.lift_full hC).1, (CellUT.CompR.lift_full hC).2⟩

theorem lifts_right {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) : Lifts a₂ a :=
  lifts_left (ResUT.CompR.comm h)

/-- `ex(ρ)_○` of a `mut` witness of `ρ` is a `○`-part of `ex(ρ)_○`. -/
theorem exR_mut_wit {ρ e : TRes K} (h : ExRT ρ e) {m : BoCa.Loc} {ψ : TCell K}
    (em : ρ.get m = some ψ) (km : ψ.kind = Kind.mut) : ∃ e', ExRT ψ.wit e' ∧ Lifts e' e := by
  cases h with
  | mk hs hw hb hnm hσ =>
      obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, em, km⟩)
      obtain ⟨ψ', hψ', hex'⟩ := ExWitsT.mem hw q hq
      rw [hq₁, em] at hψ'
      cases Option.some.inj hψ'
      obtain ⟨z, hz⟩ := BigCompT.mem_factor hRR ResUT.compLawsR hb q.2
        (List.mem_map.mpr ⟨q, hq, rfl⟩)
      exact ⟨q.2, hex', (lifts_left hz).trans (lifts_right hσ)⟩

/-- A non-`imm` cell of `ρ` is in `ex(ρ)_○`, over its value, and over its witness if not
`own` (`ExRT.get_of_ne_imm`, as `Lifts`). -/
theorem exR_cell {ρ e : TRes K} (h : ExRT ρ e) {x : BoCa.Loc} {ψ : TCell K}
    (ex : ρ.get x = some ψ) (hk : ψ.kind ≠ Kind.imm) : ∃ ζ : TCell K, e.get x = some ζ ∧
      ζ.erase = ψ.erase ∧ (ψ.kind ≠ Kind.own → ζ.kind ≠ Kind.own ∧ ζ.wit = ψ.wit) := by
  obtain ⟨χ, eχ, rχ, wχ⟩ := ExRT.get_of_ne_imm h ex hk
  exact ⟨χ, eχ, rχ, fun hk' => ⟨(wχ hk').2, (wχ hk').1⟩⟩
theorem DescRT.refl (r : FrameRecT K) : DescRT r r := ⟨[], LinPathT.nil r⟩

theorem LinPathT.snoc {r d : FrameRecT K} {p : List BoCa.Loc} (h : LinPathT r p d) {e : FrameRecT K}
    (he : SubRecT d e) : LinPathT r (p ++ [e.le]) e := by
  induction h with
  | nil r => exact LinPathT.cons he (LinPathT.nil e)
  | cons hs _ ih => exact LinPathT.cons hs (ih he)

theorem DescRT.sub {r d e : FrameRecT K} (h : DescRT r d) (he : SubRecT d e) : DescRT r e := by
  obtain ⟨p, hp⟩ := h
  exact ⟨_, hp.snoc he⟩

theorem LinPathT.xpath {r d : FrameRecT K} {p : List BoCa.Loc} (h : LinPathT r p d) : XPath r.R p d.R := by
  induction h with
  | nil r => exact XPath.nil _
  | @cons r d e p hs _ ih =>
      obtain ⟨-, ζ, eζ, kζ, -, wζ⟩ := hs
      exact XPath.cons eζ kζ (wζ ▸ ih)

theorem LinPathT.inv_nil {r e : FrameRecT K} (h : LinPathT r [] e) : e = r := by
  generalize hq : ([] : List BoCa.Loc) = q at h
  cases h with
  | nil => rfl
  | cons _ _ => cases hq

theorem LinPathT.inv_cons {r e : FrameRecT K} {m : BoCa.Loc} {p : List BoCa.Loc} (h : LinPathT r (m :: p) e) :
    ∃ d, SubRecT r d ∧ d.le = m ∧ LinPathT d p e := by
  generalize hq : m :: p = q at h
  cases h with
  | nil => cases hq
  | cons hs t =>
      injection hq with h₁ h₂
      subst h₁; subst h₂
      exact ⟨_, hs, rfl, t⟩
/-- `ex(σ)_○` is a `○`-part of every `ag(W)`.  `[about ours]` -/
def ExIn (W σ : TRes K) : Prop := ∀ a, AgWT W a → ∃ e, ExRT σ e ∧ Lifts e a

/-- `ag(W)` holds a non-`own` cell at `m` over value `u` and witness `χ`.  `[about ours]` -/
def NVAt (W : TRes K) (m : BoCa.Loc) (u : BoCa.Val) (χ : TRes K) : Prop :=
  ∀ a, AgWT W a → ∃ ψ : TCell K, a.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.erase = u ∧
    ψ.wit = χ

/-- An `imm` cell of every `ag(W)` over witness `R` puts `ex(R)_○` in `ag(W)`. -/
theorem exIn_of_imm {W R : TRes K} {le : BoCa.Loc}
    (h : ∀ a, AgWT W a → ∃ ψ : TCell K, a.get le = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.wit = R) :
    ExIn W R := by
  intro a ha
  obtain ⟨ψ, e, k, w⟩ := h a ha
  obtain ⟨s, hs, hψ⟩ := CellUT.imm_eta k
  rw [hψ] at e
  obtain ⟨ev, av, p, z, hev, -, hp, hz⟩ := AgWT.flat_imm_wit_le ha _ _ _ _ _ e
  rw [w] at hev
  exact ⟨ev, hev, (lifts_left hp).trans (lifts_left hz)⟩

/-- A `mut` cell of an escrow in `ag(W)` is in `ag(W)`, and so is its witness's `ex`. -/
theorem exIn_mut {W σ : TRes K} (h : ExIn W σ) {m : BoCa.Loc} {ζ : TCell K}
    (em : σ.get m = some ζ) (km : ζ.kind = Kind.mut) :
    ExIn W ζ.wit ∧ NVAt W m ζ.erase ζ.wit := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨e, he, hl⟩ := h a ha
    obtain ⟨e', he', hl'⟩ := exR_mut_wit he em km
    exact ⟨e', he', hl'.trans hl⟩
  · obtain ⟨e, he, hl⟩ := h a ha
    obtain ⟨χ, eχ, rχ, wχ⟩ := exR_cell he em (by rw [km]; simp)
    obtain ⟨ψ, eψ, rψ, wψ⟩ := hl m χ eχ
    obtain ⟨k₁, w₁⟩ := wχ (by rw [km]; simp)
    obtain ⟨k₂, w₂⟩ := wψ k₁
    exact ⟨ψ, eψ, k₂, rψ.trans rχ, w₂.trans w₁⟩

theorem exIn_support {W σ : TRes K} (h : ExIn W σ) {x : BoCa.Loc} {ζ : TCell K}
    (ex : σ.get x = some ζ) (hk : ζ.kind ≠ Kind.imm) : ∀ a, AgWT W a → ∃ ξ, a.get x = some ξ := by
  intro a ha
  obtain ⟨e, he, hl⟩ := h a ha
  obtain ⟨χ, eχ, -⟩ := exR_cell he ex hk
  obtain ⟨ψ, eψ, -⟩ := hl x χ eχ
  exact ⟨ψ, eψ⟩

/-- Along a lineage from a record whose `ex` is in `ag(W)`: every member's `ex` is too,
and every proper member's location carries a non-`own` cell over its value and witness. -/
theorem exIn_path {W : TRes K} {r d : FrameRecT K} {p : List BoCa.Loc} (h : LinPathT r p d) :
    ExIn W r.R → ExIn W d.R ∧ (p ≠ [] → NVAt W d.le d.v d.R) := by
  induction h with
  | nil r => exact fun hr => ⟨hr, fun hp => absurd rfl hp⟩
  | @cons r d e p hs t ih =>
      intro hr
      obtain ⟨-, ζ, eζ, kζ, rζ, wζ⟩ := hs
      obtain ⟨hd, hnv⟩ := exIn_mut hr eζ kζ
      rw [wζ] at hd hnv; rw [rζ] at hnv
      obtain ⟨he, hne⟩ := ih hd
      refine ⟨he, fun _ => ?_⟩
      cases t with
      | nil => exact hnv
      | cons _ _ => exact hne (by simp)

/-- The weakened `LeInv`: every record's location carries a non-`own` cell of `ag(W)` over
the recorded value and escrow.  `[about ours: an invariant of the typed world]` -/
def LeInvW (W : TRes K) (rs : List (FrameRecT K)) : Prop :=
  ∀ r ∈ rs, ∀ a, AgWT W a → ∃ ψ : TCell K, a.get r.le = some ψ ∧ ψ.kind ≠ Kind.own ∧
    ψ.erase = r.v ∧ ψ.wit = r.R

/-- `LeInv` at the records proper gives `ExIn` and `LeInvW` at every lineage member. -/
theorem lineage_of_leInv {W : TRes K} {ps : List (FrameRecT K)} (hl : LeInvT W ps) {p : FrameRecT K}
    (hp : p ∈ ps) {d : FrameRecT K} (hd : DescRT p d) :
    ExIn W d.R ∧ ∀ a, AgWT W a → ∃ ψ : TCell K, a.get d.le = some ψ ∧
      ψ.kind ≠ Kind.own ∧ ψ.erase = d.v ∧ ψ.wit = d.R := by
  obtain ⟨q, hq⟩ := hd
  have hex : ExIn W p.R :=
    exIn_of_imm (fun a ha => by
      obtain ⟨ψ, e, k, -, w⟩ := hl p hp a ha
      exact ⟨ψ, e, k, w⟩)
  obtain ⟨hdR, hnv⟩ := exIn_path hq hex
  refine ⟨hdR, ?_⟩
  cases hq with
  | nil =>
      intro a ha
      obtain ⟨ψ, e, k, r, w⟩ := hl p hp a ha
      exact ⟨ψ, e, by rw [k]; simp, r, w⟩
  | cons _ _ => exact hnv (by simp)
theorem TI.leInvW {W : TRes K} {ps rs : List (FrameRecT K)} (h : TIT K Θ W ps rs) : LeInvW W rs := by
  intro r hr
  obtain ⟨p, hp, hd⟩ := (h.2.2.2.2.2.2.1 r).mp hr
  exact (lineage_of_leInv h.2.1 hp hd).2

theorem TI.exIn {W : TRes K} {ps rs : List (FrameRecT K)} (h : TIT K Θ W ps rs) {r : FrameRecT K}
    (hr : r ∈ rs) : ExIn W r.R := by
  obtain ⟨p, hp, hd⟩ := (h.2.2.2.2.2.2.1 r).mp hr
  exact (lineage_of_leInv h.2.1 hp hd).1

/-- The frame's escrow sits in `ex(W)_●` unchanged, and not at `ℓ`. -/
theorem frame_ex {W X Z R eW : TRes K} {l : BoCa.Loc} {v : BoCa.Val}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (heW : ExST W eW) :
    ∃ eR, ExST R eR ∧ (∀ x (ζ : TCell K), eR.get x = some ζ → ζ.kind ≠ Kind.imm →
      eW.get x = some ζ) ∧ eR.get l = none := by
  obtain ⟨eX, eZ, heX, -, heXZ⟩ := (ExST.split hW).mp heW
  obtain ⟨eo, eR, heo, heR, heoR⟩ := (ExST.split hX).mp heX
  rw [ExST.functional heo (ExWT.single_own l v)] at heoR
  refine ⟨eR, heR, fun x ζ e k => ?_, ?_⟩
  · exact (ResUT.CompS.get_left_of_ne_imm heXZ (ResUT.CompS.get_right_of_ne_imm heoR e k).2 k).2
  · exact ResUT.CompatS.right_eq_none heoR.1 (ResUT.single_get_self _ _) (by simp)

/-- Under `immFrame`, an `own` cell of `ex(R)_●` carries no view of `ag(W′)`. -/
theorem frame_new_root' {W X Z R W' a' : TRes K} {l : BoCa.Loc} {v : BoCa.Val} {α : Life}
    {h : R.InStratum (TSet.single α)}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W')
    (hv : ResUT.Valid W) {m : BoCa.Loc} {u : BoCa.Val}
    (heRm : ∀ eR, ExST R eR → eR.get m = some (CellUT.ownOf u)) (hml : m ≠ l)
    (ha' : AgWT W' a') :
    (∃ ζ, a'.get m = some ζ) ∧
    (∀ ψ, a'.get m = some ψ → ψ.kind ≠ Kind.own → False) ∧
    (∀ aW, AgWT W aW → aW.get m = none) := by
  obtain ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hrz, heR, hup, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  have heRm' := heRm eR heR
  obtain ⟨ζW, hζW⟩ := hup m _ heRm'
  have hnone : aW.get m = none := by
    cases e : aW.get m with
    | none => rfl
    | some ζ => exact (ex_ag_disjoint hv heW haW hζW e).elim
  refine ⟨?_, fun ψ e hk => ?_, fun aW' haW' => by rw [AgWT.functional haW' haW]; exact hnone⟩
  · obtain ⟨_, e₁⟩ := comp_some hpc heRm'
    obtain ⟨_, e₂⟩ := comp_some_r hcp e₁
    exact comp_some hcz e₂
  · rcases back_view hcz e hk with ⟨ψ₁, e₁, k₁, -⟩ | ⟨ψ₁, e₁, -, -⟩
    · rcases back_view hcp e₁ k₁ with ⟨ψ₂, e₂, -, -⟩ | ⟨ψ₂, e₂, k₂, -⟩
      · exact hml (ResUT.single_get_eq_some e₂).1
      · rcases back_view hpc e₂ k₂ with ⟨ψ₃, e₃, k₃, -⟩ | ⟨ψ₃, e₃, -, -⟩
        · rw [heRm'] at e₃; cases e₃; exact k₃ (by simp)
        · obtain ⟨_, e₄⟩ := comp_some hrz e₃
          rw [hnone] at e₄; cases e₄
    · obtain ⟨_, e₄⟩ := comp_some_r hrz e₁
      rw [hnone] at e₄; cases e₄

/-- The last step of a nonempty lineage path. -/
theorem LinPathT.last {r d : FrameRecT K} {p : List BoCa.Loc} (h : LinPathT r p d) (hp : p ≠ []) :
    ∃ d', DescRT r d' ∧ SubRecT d' d := by
  induction h with
  | nil r => exact absurd rfl hp
  | @cons r d₁ e q hs t ih =>
      cases t with
      | nil => exact ⟨r, DescRT.refl r, hs⟩
      | @cons _ d₂ _ q' hs' t' =>
          obtain ⟨d', ⟨q'', hq''⟩, hd'⟩ := ih (by simp)
          exact ⟨d', ⟨_, LinPathT.cons hs hq''⟩, hd'⟩

theorem DescRT.cases {r d : FrameRecT K} (h : DescRT r d) : d = r ∨ DescT r d := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => exact Or.inl hp.inv_nil
  | cons m q => exact Or.inr ⟨_, by simp, hp⟩

end BoCa.Fig16.Tree.Wp

end
