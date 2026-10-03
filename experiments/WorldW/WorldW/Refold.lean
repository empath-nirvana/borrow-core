import WorldW.Defs

/-!
# WorldW — refold sequences (the machinery behind F-CLOSE)

**World: the W-draft.** These are facts about our closure `Close` (DESIGN §1.2), not about
OQ-9 (a) and not about a printed lemma.

`Close`'s 6.64, 6.65 and 6.150 steps are functions of their input. Its anti step (6.66's refold)
chooses a split `ρ_P̂`. Two closures of one resource therefore differ only in the splits of their
anti steps. The coherence argument (DESIGN §2, F-CLOSE) keeps track of that difference by one
invariant: at every point of two chains over one list, both states are *refolds* of one common
unfolded resource `U`, by refold lists of the same shape (place, lifetime, predicate) and
possibly different splits.

* `Refolds U A π`: `π` is `U` with the refolds `A` applied in order (each a `CloseEAnti` step).
* Each non-anti step of a chain lifts through the pending refolds to a step on `U`
  (`refolds_replace` for 6.64 and 6.65, `refolds_sub` for 6.150), because the splits cannot hold
  what the step consumes: an `own` cell excludes every other cell at its place (6.24), and the
  pin keeps the reborrow's image out of the splits.
* A 6.65 step at the place of a pending refold undoes that refold (`refolds_unfold`).
* `refolds_flat`: a refold changes the flattening only at its own place (6.28's comparison,
  `ResU.flat_mut_own_agree_off`). So the two final states have one flattening off the pending
  places, and `mut(β, v, _, P̂)` with the same `β`, `v`, `P̂` at them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Pointwise facts about `●` -/

/-- A composition is its pointwise graph: the guard follows from the cells' compositions. -/
theorem compS_of_pointwise {a b c : WRes}
    (h : ∀ l, OptComp CellU.CompS (a.get l) (b.get l) (c.get l)) : ResU.CompS a b c := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, h⟩
  have hl := h l
  rw [e₁, e₂] at hl
  obtain ⟨ψ, -, hc⟩ := hl
  exact CellU.CompS.compat hc

/-- A non-`imm` cell of one operand excludes the other operand at its place. -/
theorem compS_left_none_of_right {a b c : WRes} (h : ResU.CompS a b c) {m : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hb : b.get m = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    a.get m = none := by
  cases ha : a.get m with
  | none => rfl
  | some φ => exact absurd (h.1 m φ ψ ha hb).kinds.2 hk

theorem compS_right_none_of_left {a b c : WRes} (h : ResU.CompS a b c) {m : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (ha : a.get m = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    b.get m = none :=
  compS_left_none_of_right (ResU.CompS.comm h) ha hk

/-- `ρ/m` passes through a composition whose other operand is undefined at `m`. -/
theorem compS_del_right {a b c : WRes} (h : ResU.CompS a b c) {m : BoCa.Loc}
    (ha : a.get m = none) : ResU.CompS a (b.del m) (c.del m) := by
  classical
  refine compS_of_pointwise fun l => ?_
  by_cases hl : l = m
  · subst hl
    rw [ha, ResU.del_get_self, ResU.del_get_self]
    rfl
  · rw [ResU.del_get_ne _ hl, ResU.del_get_ne _ hl]
    exact h.2 l

/-- The composite at a place where the left operand is undefined. -/
theorem compS_get_right {a b c : WRes} (h : ResU.CompS a b c) {m : BoCa.Loc}
    (ha : a.get m = none) : c.get m = b.get m :=
  ResU.Comp.get_of_left_none h ha

theorem compS_get_left {a b c : WRes} (h : ResU.CompS a b c) {m : BoCa.Loc}
    (hb : b.get m = none) : c.get m = a.get m :=
  ResU.Comp.get_of_right_none h hb

/-- The composite carries an operand's non-`imm` cell. -/
theorem compS_get_of_right_nonimm {a b c : WRes} (h : ResU.CompS a b c) {m : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hb : b.get m = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    c.get m = some ψ := by
  rw [compS_get_right h (compS_left_none_of_right h hb hk), hb]

theorem compS_get_of_left_nonimm {a b c : WRes} (h : ResU.CompS a b c) {m : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (ha : a.get m = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    c.get m = some ψ :=
  compS_get_of_right_nonimm (ResU.CompS.comm h) ha hk

/-- A singleton at `l` is undefined off `l`. -/
theorem single_get_none {l m : BoCa.Loc} (ψ : CellU BoCa.Loc Val) (h : m ≠ l) :
    (ResU.single l ψ).get m = none :=
  ResU.single_get_ne ψ h

/-- A composite with a non-`imm` singleton is defined at the singleton's place with its cell. -/
theorem compS_single_nonimm_get {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} {b c : WRes}
    (h : ResU.CompS (ResU.single l ψ) b c) (hk : ψ.kind ≠ Kind.imm) : c.get l = some ψ :=
  compS_get_of_left_nonimm h (ResU.single_get_self l ψ) hk

theorem kind_ownOf_ne (v : Val) : (CellU.ownOf (Loc := BoCa.Loc) v).kind ≠ Kind.imm := by
  simp

theorem kind_mutOf_ne {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS BoCa.Loc Val b} {hw : P v ⟨χ, h⟩} :
    (CellU.mutOf b v χ h P hw).kind ≠ Kind.imm := by
  rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c

/-! ### The anti step -/

/-- **The refold keeps validity backwards** (`[TR]` 6.24): the unfolded input of a refold is
valid when its output is. -/
theorem closeEAnti_valid_left {l : BoCa.Loc} {β : Life} {P : Val → SPropS BoCa.Loc Val β}
    {ρP π π' : WRes} (h : CloseEAnti l β P ρP π π') : ResU.Valid π := by
  obtain ⟨v, hs, hw, X, rest, hX, hπ, hπ', hv'⟩ := h
  have hH : ResU.Hash rest (ResU.single l (CellU.mutOf β v ρP hs P hw)) :=
    ⟨(ResU.CompS.comm hπ').1, π', ResU.CompS.comm hπ', hv'⟩
  have hX' : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) X := ResU.CompS.comm hX
  obtain ⟨-, c, hc, hvc⟩ := (ResU.six24 hX').mp hH
  rwa [ResU.CompS.functional (ResU.CompS.comm hc) hπ] at hvc

/-- **One anti step changes `⦇·⦈` at its place only**, whatever split it chose:
`ResU.flat_mut_own_agree_off` (`Paper/S6_2_NonStandardLemmas/Lemmas.lean:679`) read at
`CloseEAnti`. -/
theorem closeE_anti_flat {l : BoCa.Loc} {β : Life} {P : Val → SPropS BoCa.Loc Val β}
    {ρP π π' F G : WRes} :
    CloseEAnti l β P ρP π π' → ResU.Flat π' F → ResU.Flat π G →
    (∀ m, m ≠ l → F.get m = G.get m) ∧
    ∃ v χ h hw, F.get l = some (CellU.mutOf β v χ h P hw) ∧ G.get l = some (CellU.ownOf v) := by
  rintro ⟨v, hs, hw, X, rest, hX, hπ, hπ', -⟩ hF hG
  have hX' : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) X := ResU.CompS.comm hX
  obtain ⟨hoff, hFl, hGl⟩ :=
    ResU.flat_mut_own_agree_off hX' (ResU.CompS.comm hπ') (ResU.CompS.comm hπ) hF hG
  exact ⟨fun m hm => (hoff m hm).symm, v, ρP, hs, hw, hFl, hGl⟩

/-! ### Refold sequences -/

/-- A refold: place, lifetime, predicate, and the split it chose. -/
structure Fold where
  l : BoCa.Loc
  β : Life
  P : Val → SPropS BoCa.Loc Val β
  ρP : WRes

/-- A refold's shape: everything but the split. -/
structure Shape where
  l : BoCa.Loc
  β : Life
  P : Val → SPropS BoCa.Loc Val β

def Fold.shape (f : Fold) : Shape := ⟨f.l, f.β, f.P⟩

/-- `π` is `U` with the refolds `A` applied in order. -/
inductive Refolds : WRes → List Fold → WRes → Prop
  | nil (U : WRes) : Refolds U [] U
  | cons {U x π : WRes} {f : Fold} {A : List Fold} :
      CloseEAnti f.l f.β f.P f.ρP U x → Refolds x A π → Refolds U (f :: A) π

theorem refolds_nil_iff {U π : WRes} : Refolds U [] π ↔ π = U := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil _

theorem refolds_cons_iff {U π : WRes} {f : Fold} {A : List Fold} :
    Refolds U (f :: A) π ↔ ∃ x, CloseEAnti f.l f.β f.P f.ρP U x ∧ Refolds x A π := by
  constructor
  · intro h; cases h with | cons h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨x, h₁, h₂⟩; exact .cons h₁ h₂

theorem refolds_append {A B : List Fold} {U π : WRes} :
    Refolds U (A ++ B) π ↔ ∃ x, Refolds U A x ∧ Refolds x B π := by
  induction A generalizing U with
  | nil =>
      simp only [List.nil_append]
      exact ⟨fun h => ⟨U, .nil U, h⟩,
        fun ⟨x, hx, h⟩ => by rw [refolds_nil_iff] at hx; subst hx; exact h⟩
  | cons f A ih =>
      simp only [List.cons_append, refolds_cons_iff]
      constructor
      · rintro ⟨x, h₁, h₂⟩
        obtain ⟨y, hy, hπ⟩ := ih.mp h₂
        exact ⟨y, ⟨x, h₁, hy⟩, hπ⟩
      · rintro ⟨y, ⟨x, h₁, hy⟩, hπ⟩
        exact ⟨x, h₁, ih.mpr ⟨y, hy, hπ⟩⟩

theorem refolds_snoc {U x y : WRes} {A : List Fold} {f : Fold} (h : Refolds U A x)
    (hf : CloseEAnti f.l f.β f.P f.ρP x y) : Refolds U (A ++ [f]) y :=
  refolds_append.mpr ⟨x, h, .cons hf (.nil y)⟩

/-- **The start of a refold sequence is valid when its end is** (6.24 at each step). -/
theorem refolds_valid_start : ∀ {A : List Fold} {U π : WRes}, Refolds U A π →
    ResU.Valid π → ResU.Valid U
  | [], _, _, h, hv => by rw [refolds_nil_iff] at h; subst h; exact hv
  | _ :: _, _, _, h, _ => by
      obtain ⟨x, h₁, -⟩ := refolds_cons_iff.mp h
      exact closeEAnti_valid_left h₁

/-- The intermediate states of a refold sequence are valid: each is a refold's output, or the
start. -/
theorem refolds_valid_end : ∀ {A : List Fold} {U π : WRes}, Refolds U A π →
    ResU.Valid U → ResU.Valid π
  | [], _, _, h, hv => by rw [refolds_nil_iff] at h; subst h; exact hv
  | _ :: _, _, _, h, _ => by
      obtain ⟨x, h₁, h₂⟩ := refolds_cons_iff.mp h
      obtain ⟨_, _, _, _, _, _, _, _, hvx⟩ := h₁
      exact refolds_valid_end h₂ hvx

/-! ### Lifting a 6.64 or 6.65 step through pending refolds -/

/-- **A step that replaces a top-level cell at `m` by `X` lifts through refolds away from `m`.**
`X` holds an `own` cell at `m` (6.64's `ℓ ↦ own(v) ● R`, 6.65's `ℓ ↦ own(v″) ● χ`), so no split
can hold anything at `m` (6.24: the unfolded `own` cell excludes every other cell at its place),
and the refolds replay over the replaced resource with the same splits. -/
theorem refolds_replace {m : BoCa.Loc} {c : CellU BoCa.Loc Val} {X : WRes} {v₀ : Val}
    (hX : X.get m = some (CellU.ownOf v₀)) :
    ∀ {A : List Fold} {U π π' : WRes}, (∀ f ∈ A, f.l ≠ m) → Refolds U A π →
    π.get m = some c → ResU.CompS (π.del m) X π' → ResU.Valid π' →
    ∃ U', U.get m = some c ∧ ResU.CompS (U.del m) X U' ∧ Refolds U' A π' := by
  intro A
  induction A with
  | nil =>
      intro U π π' _ h hc hπ' _
      rw [refolds_nil_iff] at h; subst h
      exact ⟨π', hc, hπ', .nil π'⟩
  | cons f A ih =>
      intro U π π' hA h hc hπ' hv
      obtain ⟨x, hf, hA'⟩ := refolds_cons_iff.mp h
      obtain ⟨x', hxm, hx', hrx⟩ :=
        ih (fun g hg => hA g (List.mem_cons_of_mem _ hg)) hA' hc hπ' hv
      have hvx' : ResU.Valid x' := refolds_valid_start hrx hv
      obtain ⟨w, hs, hw, Y, rest, hY, hU, hx, -⟩ := hf
      have hlm : f.l ≠ m := hA f List.mem_cons_self
      have hml : (ResU.single f.l (CellU.mutOf f.β w f.ρP hs f.P hw)).get m = none :=
        single_get_none _ (Ne.symm hlm)
      have hrest : rest.get m = some c := by rw [← compS_get_right hx hml]; exact hxm
      have hxd := compS_del_right hx hml
      obtain ⟨rest', hr', hx'2⟩ := compS_reassoc hxd hx'
      have hH : ResU.Hash rest' (ResU.single f.l (CellU.mutOf f.β w f.ρP hs f.P hw)) :=
        ⟨(ResU.CompS.comm hx'2).1, x', ResU.CompS.comm hx'2, hvx'⟩
      have hY' : ResU.CompS f.ρP (ResU.single f.l (CellU.ownOf w)) Y := ResU.CompS.comm hY
      obtain ⟨-, U', hU', -⟩ := (ResU.six24 hY').mp hH
      have hr'm : rest'.get m = some (CellU.ownOf v₀) := by
        rw [compS_get_right hr' (ResU.del_get_self _ _)]; exact hX
      have hYm : Y.get m = none := compS_right_none_of_left hU' hr'm (kind_ownOf_ne v₀)
      refine ⟨U', ?_, ?_, .cons ⟨w, hs, hw, Y, rest', hY, ResU.CompS.comm hU', hx'2, hvx'⟩ hrx⟩
      · rw [compS_get_right hU hYm]; exact hrest
      · have hUd := compS_del_right hU hYm
        obtain ⟨ab, hab, hU'2⟩ := compS_reassoc' hr' (ResU.CompS.comm hU')
        rwa [ResU.CompS.functional hab hUd] at hU'2

/-! ### Structure of refold sequences -/

/-- A refold's input holds the unfolded `own` cell at its place. -/
theorem closeEAnti_get_own {l : BoCa.Loc} {β : Life} {P : Val → SPropS BoCa.Loc Val β}
    {ρP π π' : WRes} (h : CloseEAnti l β P ρP π π') : ∃ v, π.get l = some (CellU.ownOf v) := by
  obtain ⟨v, -, -, X, rest, hX, hπ, -, -⟩ := h
  exact ⟨v, compS_get_of_left_nonimm hπ (compS_single_nonimm_get hX (kind_ownOf_ne v))
    (kind_ownOf_ne v)⟩

/-- A refold's output holds its `mut` cell at its place. -/
theorem closeEAnti_get_mut {l : BoCa.Loc} {β : Life} {P : Val → SPropS BoCa.Loc Val β}
    {ρP π π' : WRes} (h : CloseEAnti l β P ρP π π') :
    ∃ v hs hw, π'.get l = some (CellU.mutOf β v ρP hs P hw) := by
  obtain ⟨v, hs, hw, X, rest, -, -, hπ', -⟩ := h
  exact ⟨v, hs, hw, compS_single_nonimm_get hπ' kind_mutOf_ne⟩

/-- **Refolds create no `own` cell**: a top-level `own` cell of a refold sequence's end is one of
its start, at no refold's place. -/
theorem refolds_own : ∀ {A : List Fold} {U π : WRes}, Refolds U A π →
    ∀ {m : BoCa.Loc} {v : Val}, π.get m = some (CellU.ownOf v) →
    U.get m = some (CellU.ownOf v) ∧ ∀ f ∈ A, f.l ≠ m
  | [], _, _, h, _, _, hm => by
      rw [refolds_nil_iff] at h; subst h; exact ⟨hm, fun _ h => absurd h List.not_mem_nil⟩
  | f :: A, U, π, h, m, v, hm => by
      obtain ⟨x, hf, hA⟩ := refolds_cons_iff.mp h
      obtain ⟨hxm, hAm⟩ := refolds_own hA hm
      obtain ⟨w, hs, hw, Y, rest, hY, hU, hx, -⟩ := hf
      have hlm : f.l ≠ m := by
        rintro rfl
        rw [compS_single_nonimm_get hx kind_mutOf_ne] at hxm
        exact CellU.ownOf_ne_mutOf (Option.some.inj hxm).symm
      have hml : (ResU.single f.l (CellU.mutOf f.β w f.ρP hs f.P hw)).get m = none :=
        single_get_none _ (Ne.symm hlm)
      have hrest : rest.get m = some (CellU.ownOf v) := by
        rw [← compS_get_right hx hml]; exact hxm
      refine ⟨compS_get_of_right_nonimm hU hrest (kind_ownOf_ne v), fun g hg => ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hlm
      · exact hAm g hg

/-- **The places of a refold sequence are distinct**: a refold consumes the start's `own` cell at
its place, and refolds create no `own` cell. -/
theorem refolds_nodup : ∀ {A : List Fold} {U π : WRes}, Refolds U A π → (A.map Fold.l).Nodup
  | [], _, _, _ => List.nodup_nil
  | f :: A, U, π, h => by
      obtain ⟨x, hf, hA⟩ := refolds_cons_iff.mp h
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, refolds_nodup hA⟩
      obtain ⟨g, hg, hgl⟩ := List.mem_map.mp hmem
      obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hg
      obtain ⟨y, hy, hy'⟩ := refolds_append.mp hA
      obtain ⟨z, hgz, -⟩ := refolds_cons_iff.mp hy'
      obtain ⟨v, hv⟩ := closeEAnti_get_own hgz
      obtain ⟨hxv, -⟩ := refolds_own hy hv
      obtain ⟨w, hs, hw, hxl⟩ := closeEAnti_get_mut hf
      rw [hgl, hxl] at hxv
      exact CellU.ownOf_ne_mutOf (Option.some.inj hxv).symm

/-! ### A 6.65 step at a pending refold's place undoes it -/

/-- `ℓ ↦ ψ ● r` with `r` undefined at `ℓ`, read back: `r` is the composite without `ℓ`. -/
theorem del_of_compS_single {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} {r y : WRes}
    (h : ResU.CompS (ResU.single l ψ) r y) (hr : r.get l = none) : y.del l = r := by
  classical
  refine PMap.ext fun m => ?_
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self, hr]
  · rw [ResU.del_get_ne _ hm, compS_get_right h (single_get_none _ hm)]

theorem eraseP_eq_of_split {A₁ A₂ : List Fold} {f : Fold} {m : BoCa.Loc} (hf : f.l = m)
    (h₁ : ∀ g ∈ A₁, g.l ≠ m) (h₂ : ∀ g ∈ A₂, g.l ≠ m) :
    (A₁ ++ f :: A₂).filter (fun g => g.l != m) = A₁ ++ A₂ := by
  rw [List.filter_append, List.filter_cons]
  have e₁ : A₁.filter (fun g => g.l != m) = A₁ :=
    List.filter_eq_self.mpr (fun g hg => by simpa using h₁ g hg)
  have e₂ : A₂.filter (fun g => g.l != m) = A₂ :=
    List.filter_eq_self.mpr (fun g hg => by simpa using h₂ g hg)
  simp [e₁, e₂, hf]

/-- **The unfold.** A 6.65 step at the place of a pending refold, whose cell is at the top of the
end, gives the refold sequence without that refold: the split comes back to the top level. -/
theorem refolds_unfold {A : List Fold} {U π π' : WRes} {m : BoCa.Loc} {α : Life} {v : Val}
    {χ : WRes} {h : χ.InStratum α} {Q : Val → SPropS BoCa.Loc Val α} {hw : Q v ⟨χ, h⟩}
    {X : WRes} (hrf : Refolds U A π) (hmem : ∃ f ∈ A, f.l = m)
    (hπ : π.get m = some (CellU.mutOf α v χ h Q hw))
    (hX : ResU.CompS (ResU.single m (CellU.ownOf v)) χ X)
    (hπ' : ResU.CompS (π.del m) X π') (hv : ResU.Valid π') :
    Refolds U (A.filter (fun g => g.l != m)) π' := by
  obtain ⟨f, hf, hfl⟩ := hmem
  obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hf
  have hnd := refolds_nodup hrf
  rw [List.map_append, List.map_cons, List.nodup_append] at hnd
  obtain ⟨-, hnd₂, hdisj⟩ := hnd
  have h₁ : ∀ g ∈ A₁, g.l ≠ m := fun g hg e =>
    hdisj _ (List.mem_map_of_mem (f := Fold.l) hg) _ List.mem_cons_self (e.trans hfl.symm)
  have h₂ : ∀ g ∈ A₂, g.l ≠ m := fun g hg e =>
    (List.nodup_cons.mp hnd₂).1 (by rw [hfl, ← e]; exact List.mem_map_of_mem (f := Fold.l) hg)
  rw [eraseP_eq_of_split hfl h₁ h₂]
  obtain ⟨x, hU₁, hx⟩ := refolds_append.mp hrf
  obtain ⟨y, hfy, hy⟩ := refolds_cons_iff.mp hx
  have hXm : X.get m = some (CellU.ownOf v) := compS_single_nonimm_get hX (kind_ownOf_ne v)
  obtain ⟨y', hym, hy', hry⟩ := refolds_replace hXm h₂ hy hπ hπ' hv
  obtain ⟨l, β, P, ρP⟩ := f
  simp only at hfl
  subst hfl
  obtain ⟨w, hs, hw', Y, rest, hY, hxY, hyr, -⟩ := hfy
  rw [compS_single_nonimm_get hyr kind_mutOf_ne] at hym
  have he := Option.some.inj hym
  obtain rfl : β = α := CellU.mutOf_at he
  obtain ⟨rfl, rfl, -⟩ := CellU.mutOf_inj he
  have hrl : rest.get l = none := compS_right_none_of_left hyr (ResU.single_get_self _ _)
    kind_mutOf_ne
  rw [del_of_compS_single hyr hrl, ResU.CompS.functional hX hY] at hy'
  rw [ResU.CompS.functional (ResU.CompS.comm hy') hxY] at hry
  exact refolds_append.mpr ⟨x, hU₁, hry⟩

/-! ### Definition 6.3's `⊟`, pointwise -/

/-- `ρ′` lies under `ρ` at its `imm` cells, same value and witness, lifetime set contained:
`ResU.sub_of_le`'s hypothesis. -/
def SubLe (ρ' ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (s' : LSet) (v : Val) (w : WRes) (h' : w.InStratum s'.join),
    ρ'.get l = some (CellU.immOf s' v w h') →
    ∃ (s : LSet) (h : w.InStratum s.join), ρ.get l = some (CellU.immOf s v w h) ∧
      ∀ x, s'.mem x → s.mem x

theorem kind_of_exclPart_empty {ρ : WRes} (h : ρ.exclPart = PMap.empty) {m : BoCa.Loc}
    {ξ : CellU BoCa.Loc Val} (hm : ρ.get m = some ξ) : ξ.kind = Kind.imm := by
  by_contra hk
  have hx : ρ.exclPart.get m = some ξ := ResU.exclPart_eq_some.mpr ⟨hm, hk⟩
  rw [h] at hx; exact absurd hx (by simp)

/-- Two `imm` cells composed: the left one is over the right one's value and witness, and the
composite's set is the union. -/
theorem cellCompS_imm_right {ψ ψ₀ : CellU BoCa.Loc Val} {s' : LSet} {v : Val} {w : WRes}
    {h' : w.InStratum s'.join} (hc : CellU.CompS ψ (CellU.immOf s' v w h') ψ₀) :
    ∃ (t : LSet) (ht : w.InStratum t.join) (ht' : w.InStratum (t ∪ s').join),
      ψ = CellU.immOf t v w ht ∧ ψ₀ = CellU.immOf (t ∪ s') v w ht' := by
  obtain ⟨s₁, s₂, v', w', k₁, k₂, k₃, e₁, e₂, e₃⟩ := hc
  obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₂.symm
  exact ⟨s₁, k₁, k₃, e₁, e₃⟩

theorem subLe_of_le {ρ' ρ : WRes} (hle : ResU.Le ρ' ρ) :
    SubLe ρ' ρ := by
  intro l s' v w h' hl
  obtain ⟨T, hT⟩ := hle
  rcases ResU.Comp.get hT l with ⟨e₁, -, -⟩ | ⟨ψ, e₁, -, e⟩ | ⟨ψ, e₁, -, -⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hc⟩
  · rw [hl] at e₁; exact absurd e₁ (by simp)
  · rw [hl] at e₁; cases Option.some.inj e₁
    exact ⟨s', h', e, fun x hx => hx⟩
  · rw [hl] at e₁; exact absurd e₁ (by simp)
  · rw [hl] at e₁; cases Option.some.inj e₁
    obtain ⟨t, ht, ht', rfl, rfl⟩ := cellCompS_imm_right (CellU.CompS.comm hc)
    exact ⟨t ∪ s', ht', e, fun x hx => Or.inr hx⟩

/-- Definition 6.3's `⊟` at a location the subtrahend covers. -/
theorem subKeep_at {ρ ρ' χ : WRes} (hsk : ResU.SubKeep ρ ρ' χ) {m : BoCa.Loc} {s s' : LSet}
    {v : Val} {w : WRes} {h : w.InStratum s.join} {h' : w.InStratum s'.join}
    (hm : ρ.get m = some (CellU.immOf s v w h)) (hm' : ρ'.get m = some (CellU.immOf s' v w h')) :
    (LSet.DiffEmpty s s' → χ.get m = none) ∧
    (∀ u : LSet, LSet.Diff s s' u → ¬ LSet.DiffEmpty s s' →
      ∃ hu : w.InStratum u.join, χ.get m = some (CellU.immOf u v w hu)) := by
  obtain ⟨ρ'', -, -, -, hcl, hχ⟩ := hsk
  have hex : ρ.exclPart.get m = none := by
    cases e : ρ.exclPart.get m with
    | none => rfl
    | some ξ =>
        obtain ⟨g1, g2⟩ := ResU.exclPart_eq_some.mp e
        rw [hm] at g1; cases Option.some.inj g1
        exact absurd (CellU.kind_immOf _ _ _ _) g2
  rw [compS_get_right hχ hex]
  exact hcl m s s' v w h h' hm hm'

/-- What `⊟` leaves at a covered location has none of the subtrahend's lifetimes there. -/
theorem subKeep_disj {ρ ρ' χ : WRes} (hsk : ResU.SubKeep ρ ρ' χ) (hle : SubLe ρ' ρ)
    {m : BoCa.Loc} {s' : LSet} {v : Val} {w : WRes} {h' : w.InStratum s'.join}
    (hm' : ρ'.get m = some (CellU.immOf s' v w h')) {ψ : CellU BoCa.Loc Val}
    (hψ : χ.get m = some ψ) {t : LSet} (ht : ψ.lsOf = some t) : ∀ x, t.mem x → ¬ s'.mem x := by
  classical
  obtain ⟨s, h, hm, -⟩ := hle m s' v w h' hm'
  obtain ⟨hA, hB⟩ := subKeep_at hsk hm hm'
  by_cases hd : LSet.DiffEmpty s s'
  · rw [hA hd] at hψ; exact absurd hψ (by simp)
  · obtain ⟨u, hu⟩ := LSet.exists_diff hd
    obtain ⟨hu', hχ⟩ := hB u hu hd
    rw [hχ] at hψ; cases Option.some.inj hψ
    simp only [CellU.lsOf_immOf, Option.some.injEq] at ht
    subst ht
    intro x hx
    exact ((hu x).mp hx).2

/-- **`⊟` characterised by `●`**: a resource that composes with the subtrahend back to `ρ`, and
keeps none of the subtrahend's lifetimes at its locations, is `ρ ⊟ ρ′`. -/
theorem subKeep_of_compS {ρ ρ' χ : WRes} (hex : ρ'.exclPart = PMap.empty) (hle : SubLe ρ' ρ)
    (hc : ResU.CompS χ ρ' ρ)
    (hdisj : ∀ (m : BoCa.Loc) (s' : LSet) (v : Val) (w : WRes) (h' : w.InStratum s'.join),
      ρ'.get m = some (CellU.immOf s' v w h') → ∀ ψ, χ.get m = some ψ →
      ∀ t, ψ.lsOf = some t → ∀ x, t.mem x → ¬ s'.mem x) :
    ResU.SubKeep ρ ρ' χ := by
  classical
  obtain ⟨ψ', hsk, hc'⟩ := ResU.sub_of_le hex hle
  suffices e : χ = ψ' by rw [e]; exact hsk
  refine PMap.ext fun m => ?_
  cases hm' : ρ'.get m with
  | none => rw [← compS_get_left hc hm', ← compS_get_left hc' hm']
  | some ξ =>
      obtain ⟨s', hs', heta⟩ := CellU.imm_eta (kind_of_exclPart_empty hex hm')
      have hm'' : ρ'.get m = some (CellU.immOf s' ξ.erase ξ.wit hs') :=
        hm'.trans (congrArg some heta)
      obtain ⟨s, h, hm, hsub⟩ := hle m s' _ _ hs' hm''
      obtain ⟨hA, hB⟩ := subKeep_at hsk hm hm''
      -- what `χ` holds at `m`
      have hχm : χ.get m = none ∧ s = s' ∨
          ∃ (t : LSet) (ht : ξ.wit.InStratum t.join), χ.get m = some (CellU.immOf t ξ.erase ξ.wit ht)
            ∧ t ∪ s' = s := by
        rcases ResU.Comp.get hc m with ⟨-, e₂, -⟩ | ⟨ψ, -, e₂, -⟩ | ⟨ψ, e₁, e₂, e⟩ |
            ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hcc⟩
        · rw [hm''] at e₂; exact absurd e₂ (by simp)
        · rw [hm''] at e₂; exact absurd e₂ (by simp)
        · rw [hm''] at e₂; cases Option.some.inj e₂
          rw [hm] at e
          exact Or.inl ⟨e₁, (CellU.immOf_inj (Option.some.inj e).symm).1.symm⟩
        · rw [hm''] at e₂; cases Option.some.inj e₂
          obtain ⟨t, ht, ht', rfl, rfl⟩ := cellCompS_imm_right hcc
          rw [hm] at e
          exact Or.inr ⟨t, ht, e₁, (CellU.immOf_inj (Option.some.inj e).symm).1⟩
      by_cases hd : LSet.DiffEmpty s s'
      · rw [hA hd]
        rcases hχm with ⟨e, -⟩ | ⟨t, ht, e, hts⟩
        · exact e
        · exfalso
          have hj := hdisj m s' _ _ hs' hm'' _ e t rfl t.join t.join_mem
          exact hj (hd _ (hts ▸ Or.inl t.join_mem))
      · obtain ⟨u, hu⟩ := LSet.exists_diff hd
        obtain ⟨hu', hψ'⟩ := hB u hu hd
        rw [hψ']
        rcases hχm with ⟨-, rfl⟩ | ⟨t, ht, e, hts⟩
        · exact absurd (fun x hx => hx) hd
        · rw [e]
          refine congrArg some (CellU.immOf_congr ?_ rfl rfl ht hu')
          refine LSet.ext fun x => ⟨fun hx => (hu x).mpr ⟨hts ▸ Or.inl hx,
            hdisj m s' _ _ hs' hm'' _ e t rfl x hx⟩, fun hx => ?_⟩
          obtain ⟨hxs, hxs'⟩ := (hu x).mp hx
          rw [← hts] at hxs
          rcases hxs with hxs | hxs
          · exact hxs
          · exact absurd hxs hxs'

/-- A lifetime of a composite `imm` cell is a lifetime of one of its parts. -/
theorem compS_lsOf_mem {a b c : WRes} (hc : ResU.CompS a b c) {m : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hψ : c.get m = some ψ) {t : LSet} (ht : ψ.lsOf = some t) {x : Life}
    (hx : t.mem x) :
    (∃ ψa ta, a.get m = some ψa ∧ ψa.lsOf = some ta ∧ ta.mem x) ∨
    (∃ ψb tb, b.get m = some ψb ∧ ψb.lsOf = some tb ∧ tb.mem x) := by
  rcases ResU.Comp.get hc m with ⟨-, -, e⟩ | ⟨φ, e₁, -, e⟩ | ⟨φ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, φ, e₁, e₂, e, hcc⟩
  · rw [hψ] at e; exact absurd e (by simp)
  · rw [hψ] at e; cases Option.some.inj e; exact Or.inl ⟨_, t, e₁, ht, hx⟩
  · rw [hψ] at e; cases Option.some.inj e; exact Or.inr ⟨_, t, e₂, ht, hx⟩
  · rw [hψ] at e; cases Option.some.inj e
    obtain ⟨s₁, s₂, v, w, k₁, k₂, k₃, rfl, rfl, rfl⟩ := hcc
    simp only [CellU.lsOf_immOf, Option.some.injEq] at ht
    subst ht
    rcases hx with hx | hx
    · exact Or.inl ⟨_, s₁, e₁, rfl, hx⟩
    · exact Or.inr ⟨_, s₂, e₂, rfl, hx⟩

/-- An `imm`-only resource under a refold's output lies under the part beside the `mut` cell. -/
theorem le_rest_of_le {img rest x : WRes} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (hk : ψ.kind ≠ Kind.imm) (hx : ResU.CompS (ResU.single l ψ) rest x)
    (hex : img.exclPart = PMap.empty) (hle : ResU.Le img x) :
    ResU.Le img rest ∧ img.get l = none := by
  classical
  obtain ⟨T, hT⟩ := hle
  have hxl : x.get l = some ψ := compS_single_nonimm_get hx hk
  have himgl : img.get l = none := by
    cases e : img.get l with
    | none => rfl
    | some ξ =>
        exfalso
        have hk' := kind_of_exclPart_empty hex e
        rcases ResU.Comp.get hT l with ⟨e₁, -, -⟩ | ⟨φ, e₁, -, e'⟩ | ⟨φ, e₁, -, -⟩ |
            ⟨ψ₁, ψ₂, φ, e₁, e₂, e', hcc⟩
        · rw [e] at e₁; exact absurd e₁ (by simp)
        · rw [e] at e₁; cases Option.some.inj e₁
          rw [hxl] at e'; cases Option.some.inj e'; exact hk hk'
        · rw [e] at e₁; exact absurd e₁ (by simp)
        · rw [hxl] at e'; cases Option.some.inj e'; exact hk (CellU.CompS.kind hcc)
  have hrl : rest.get l = none :=
    compS_right_none_of_left hx (ResU.single_get_self l ψ) hk
  refine ⟨⟨T.del l, compS_of_pointwise fun k => ?_⟩, himgl⟩
  by_cases hkl : k = l
  · subst hkl
    rw [himgl, ResU.del_get_self, hrl]; rfl
  · rw [ResU.del_get_ne _ hkl, ← compS_get_right hx (single_get_none _ hkl)]
    exact hT.2 k

/-- A reborrow image's cells, restricted to the source's exclusive locations, are at `{β}`. -/
theorem reb_img_single {β : Life} {σR χ : WRes} (hreb : ResU.Reb β σR χ) {m : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hm : (χ.restrictDom σR.exclPart).get m = some ψ) :
    ∃ v w h, ψ = CellU.immOf (LSet.singleton β) v w h := by
  have hχ := ResU.restrictDom_get_inv hm
  cases e : σR.exclPart.get m with
  | none => rw [ResU.restrictDom_get_of_none e] at hm; exact absurd hm (by simp)
  | some φ =>
      obtain ⟨hφ, hk⟩ := ResU.exclPart_eq_some.mp e
      obtain ⟨v, w, hw, hψ, -, -⟩ := ResU.reb_src hreb hχ hφ hk
      exact ⟨v, w, hw, hψ⟩

/-! ### Lifting a 6.150 step through pending refolds -/

/-- **The reborrow's exit lifts through pinned refolds.** The image's cells are `imm` at `{β}`,
and the pin keeps every pending split free of `imm` cells at `β`. So `⊟` subtracts the image from
the part beside each refold, and the refolds replay over `U ⊟ image` with the same splits. -/
theorem refolds_sub {img : WRes} {β : Life} (hex : img.exclPart = PMap.empty)
    (himg : ∀ m ψ, img.get m = some ψ → ∃ v w h, ψ = CellU.immOf (LSet.singleton β) v w h) :
    ∀ {A : List Fold} {U π π' : WRes},
    (∀ f ∈ A, ∀ m ψ, f.ρP.get m = some ψ → ¬ CellU.ImmAt ψ β) →
    Refolds U A π → ResU.Le img π → ResU.SubKeep π img π' → ResU.Valid π' →
    ∃ U', ResU.Le img U ∧ ResU.SubKeep U img U' ∧ Refolds U' A π' := by
  intro A
  induction A with
  | nil =>
      intro U π π' _ h hle hsk _
      rw [refolds_nil_iff] at h; subst h
      exact ⟨π', hle, hsk, .nil π'⟩
  | cons f A ih =>
      intro U π π' hpin h hle hsk hv
      obtain ⟨x, hf, hA'⟩ := refolds_cons_iff.mp h
      obtain ⟨x', hlex, hskx, hrx⟩ :=
        ih (fun g hg => hpin g (List.mem_cons_of_mem _ hg)) hA' hle hsk hv
      have hvx' : ResU.Valid x' := refolds_valid_start hrx hv
      obtain ⟨w, hs, hw, Y, rest, hY, hU, hx, -⟩ := hf
      obtain ⟨hler, himgl⟩ := le_rest_of_le kind_mutOf_ne hx hex hlex
      obtain ⟨rest', hskr, hcr⟩ := ResU.sub_of_le hex (subLe_of_le hler)
      obtain ⟨U', hU'1, hU'2⟩ := compS_reassoc' hcr hU
      obtain ⟨x'', hx''1, hx''2⟩ := compS_reassoc' hcr hx
      have hleU : ResU.Le img U := ResU.Le.trans hler ⟨Y, ResU.CompS.comm hU⟩
      -- the image's places are off the refold's place
      have hoff : ∀ m ψ, img.get m = some ψ → m ≠ f.l := by
        rintro m ψ e rfl; rw [himgl] at e; exact absurd e (by simp)
      -- what `rest′` keeps at an image place has no `β`
      have hdr : ∀ (m : BoCa.Loc) (s' : LSet) (v : Val) (w' : WRes) (h' : w'.InStratum s'.join),
          img.get m = some (CellU.immOf s' v w' h') → ∀ ψ, rest'.get m = some ψ →
          ∀ t, ψ.lsOf = some t → ∀ x, t.mem x → ¬ s'.mem x :=
        fun m s' v w' h' e ψ hψ t ht =>
          subKeep_disj hskr (subLe_of_le hler) e hψ ht
      -- `x″ = x ⊟ image`
      have hskx'' : ResU.SubKeep x img x'' := by
        refine subKeep_of_compS hex (subLe_of_le hlex) hx''2 ?_
        intro m s' v w' h' e ψ hψ t ht
        have hml := hoff m _ e
        rw [compS_get_right hx''1 (single_get_none _ hml)] at hψ
        exact hdr m s' v w' h' e ψ hψ t ht
      have hxx : x'' = x' :=
        ResU.SubKeep.functional (subLe_of_le hlex) hskx'' hskx
      subst hxx
      -- `U′ = U ⊟ image`
      have hskU : ResU.SubKeep U img U' := by
        refine subKeep_of_compS hex (subLe_of_le hleU) hU'2 ?_
        intro m s' v w' h' e ψ hψ t ht x hx
        obtain ⟨vv, ww, hh, heq⟩ := himg m _ e
        obtain ⟨rfl, -, -⟩ := CellU.immOf_inj heq
        have hml := hoff m _ e
        rcases compS_lsOf_mem hU'1 hψ ht hx with ⟨ψa, ta, ha, hta, hxa⟩ | ⟨ψb, tb, hb, htb, hxb⟩
        · -- a lifetime of the split
          have hYm : (ResU.single f.l (CellU.ownOf w)).get m = none := single_get_none _ hml
          rw [compS_get_right hY hYm] at ha
          intro hxs
          have hxβ : x = β := hxs
          subst hxβ
          exact hpin f List.mem_cons_self m ψa ha ⟨ta, hta, hxa⟩
        · exact hdr m _ v w' h' e ψb hb tb htb x hxb
      exact ⟨U', hleU, hskU,
        .cons ⟨w, hs, hw, Y, rest', hY, hU'1, hx''1, hvx'⟩ hrx⟩

/-! ### The flattening of a refold sequence -/

/-- **A refold sequence changes `⦇·⦈` at its places only** (`closeE_anti_flat` at each step).
At each place the end carries the refold's `mut(β, v, ρ_P̂, P̂)`, `v` the start's `own` value
there. -/
theorem refolds_flat : ∀ {A : List Fold} {U π : WRes}, Refolds U A π → ResU.Valid U →
    ∀ {FU Fπ : WRes}, ResU.Flat U FU → ResU.Flat π Fπ →
    (∀ m, (∀ f ∈ A, f.l ≠ m) → Fπ.get m = FU.get m) ∧
    (∀ f ∈ A, ∃ v χ h hw, Fπ.get f.l = some (CellU.mutOf f.β v χ h f.P hw) ∧
      FU.get f.l = some (CellU.ownOf v))
  | [], _, _, h, _, FU, Fπ, hFU, hFπ => by
      rw [refolds_nil_iff] at h; subst h
      have e : Fπ = FU := ResU.Flat.functional hFπ hFU
      subst e
      exact ⟨fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | f :: A, U, π, h, hvU, FU, Fπ, hFU, hFπ => by
      have hnd := refolds_nodup h
      obtain ⟨x, hf, hA⟩ := refolds_cons_iff.mp h
      have hvx : ResU.Valid x := by obtain ⟨_, _, _, _, _, _, _, _, hv⟩ := hf; exact hv
      obtain ⟨Fx, hFx⟩ := hvx
      obtain ⟨hoff, v, χ, hχ, hw, hFxl, hFUl⟩ := closeE_anti_flat hf hFx hFU
      obtain ⟨ih₁, ih₂⟩ := refolds_flat hA ⟨Fx, hFx⟩ hFx hFπ
      have hfl : ∀ g ∈ A, g.l ≠ f.l := fun g hg e =>
        (List.nodup_cons.mp (by simpa using hnd)).1 (e ▸ List.mem_map_of_mem (f := Fold.l) hg)
      refine ⟨fun m hm => ?_, fun g hg => ?_⟩
      · rw [ih₁ m (fun g hg => hm g (List.mem_cons_of_mem _ hg))]
        exact hoff m (fun e => hm f List.mem_cons_self e.symm)
      · rcases List.mem_cons.mp hg with rfl | hg
        · refine ⟨v, χ, hχ, hw, ?_, hFUl⟩
          rw [ih₁ g.l (fun g' hg' => hfl g' hg')]
          exact hFxl
        · obtain ⟨v', χ', h', hw', hπg, hxg⟩ := ih₂ g hg
          refine ⟨v', χ', h', hw', hπg, ?_⟩
          rw [← hoff g.l (hfl g hg)]
          exact hxg

end WorldW

end
