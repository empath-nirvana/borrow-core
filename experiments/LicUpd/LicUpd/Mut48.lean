import LicUpd.MutMask

/-!
# LicUpd — 6.48's `mut` half under growth, with the typed-world premise

K8 (`MutMask.lean`) shows that 6.48's `mut` half fails under growth over all resources: a new
image masks a frame's frozen `mut` cell (`mut ○ imm = imm`).

`NoNewImmUnderMut F ρ π` is the premise that excludes it. Where `F`'s flattening holds a `mut`
cell, the run adds no `imm` cell that its start did not have. In a typed world it follows from
`TI`'s `NoMut` and `Coverage`: the run's new images sit at record-owned locations, where no
`mut` cell exists. That derivation is the library unit's, and is not done here.

`updMutG_frame` proves 6.48's `mut` half under growth from that premise. It reads `↭`'s `mut`
clause pointwise, location by location:
- the clause lets value and witness change, so no ancestor transfer is needed;
- check 1's walk lemma (a `mut` cell beneath an image is beneath its `DerLt` parent) is not
  used. The one cell fact needed is `compR_mut_pair`.

`updVG_frame` is 6.48 under growth, combining it with `updImmG_frame`.
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- 6.48's premise under growth: where `F`'s flattening holds a `mut` cell, every `imm` cell of
`π`'s flattening has an `imm` cell of `ρ`'s at the same location. -/
def NoNewImmUnderMut (F ρ π : WRes) : Prop :=
  ∀ (n : Loc) (ψ : CellU Loc Val) (σF : WRes), ResU.Flat F σF → σF.get n = some ψ →
    ψ.kind = Kind.mut → ∀ c, π.FlatAt n c → c.kind = Kind.imm →
      ∃ c', ρ.FlatAt n c' ∧ c'.kind = Kind.imm

/-- `σ` holds a `mut(b, _, _, P̂)` cell at `n`. -/
def HasMut (σ : WRes) (n : Loc) (b : Life) (P : Val → SPropS Loc Val b) : Prop :=
  ∃ (v : Val) (χ : WRes) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
    σ.get n = some (CellU.mutOf b v χ h P hw)

/-! ### Walk facts -/

theorem ex_none_of_ag {ρ e a σ : WRes} (he : ExS ρ e) (hc : ResU.CompS e a σ) {n : Loc}
    {ψ : CellU Loc Val} (hg : a.get n = some ψ) : e.get n = none := by
  cases f : e.get n with
  | none => rfl
  | some ξ => exact absurd (CellU.CompatS.kinds (hc.1 n ξ ψ f hg)).1 (ExS.immFree he n ξ f)

theorem flat_of_ag {ρ e a σ : WRes} (he : ExS ρ e) (hc : ResU.CompS e a σ) {n : Loc}
    {ψ : CellU Loc Val} (hg : a.get n = some ψ) : σ.get n = some ψ :=
  comp_get_right hc (ex_none_of_ag he hc hg) hg

theorem flat_of_ex {ρ e a σ : WRes} (he : ExS ρ e) (hc : ResU.CompS e a σ) {n : Loc}
    {ψ : CellU Loc Val} (hg : e.get n = some ψ) : σ.get n = some ψ ∧ a.get n = none :=
  ⟨(ResU.CompS.get_left_of_ne_imm hc hg (ExS.immFree he n ψ hg)).2,
    (ResU.CompS.get_left_of_ne_imm hc hg (ExS.immFree he n ψ hg)).1⟩

theorem comp_none_parts {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {n : Loc} (e : ρ.get n = none) :
    ρ₁.get n = none ∧ ρ₂.get n = none := by
  rcases ResU.Comp.get h n with ⟨f₁, f₂, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, -, -, f⟩ |
      ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
  · exact ⟨f₁, f₂⟩
  · rw [e] at f; cases f
  · rw [e] at f; cases f
  · rw [e] at f; cases f

theorem comp_some_left {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) {n : Loc} {ψ : CellU Loc Val} (e : ρ₁.get n = some ψ) :
    ∃ r, ρ.get n = some r := by
  rcases ResU.Comp.get h n with ⟨f₁, -, -⟩ | ⟨r, -, -, f⟩ | ⟨r, f₁, -, -⟩ |
      ⟨-, -, r, -, -, f, -⟩
  · rw [e] at f₁; cases f₁
  · exact ⟨r, f⟩
  · rw [e] at f₁; cases f₁
  · exact ⟨r, f⟩

/-! ### One cell fact -/

/-- Composing one cell with two `mut` cells of the same lifetime and predicate gives results
that carry a `mut(b₀, _, _, P̂₀)` together or not at all. -/
theorem compR_mut_pair {ψ₁ ψ ψ' : CellU Loc Val} {b : Life} {P : Val → SPropS Loc Val b}
    {v v' : Val} {χ χ' : WRes} {h : χ.InStratum b} {h' : χ'.InStratum b}
    {hw : P v ⟨χ, h⟩} {hw' : P v' ⟨χ', h'⟩}
    (hc : CellU.CompR ψ₁ (CellU.mutOf b v χ h P hw) ψ)
    (hc' : CellU.CompR ψ₁ (CellU.mutOf b v' χ' h' P hw') ψ')
    {b₀ : Life} {P₀ : Val → SPropS Loc Val b₀}
    (hm : ∃ (v₀ : Val) (χ₀ : WRes) (h₀ : χ₀.InStratum b₀) (hw₀ : P₀ v₀ ⟨χ₀, h₀⟩),
      ψ = CellU.mutOf b₀ v₀ χ₀ h₀ P₀ hw₀) :
    ∃ (v₀ : Val) (χ₀ : WRes) (h₀ : χ₀.InStratum b₀) (hw₀ : P₀ v₀ ⟨χ₀, h₀⟩),
      ψ' = CellU.mutOf b₀ v₀ χ₀ h₀ P₀ hw₀ := by
  obtain ⟨v₀, χ₀, h₀, hw₀, rfl⟩ := hm
  rcases CellU.rep ψ₁ with ⟨u, rfl⟩ | ⟨s₁, u, ρ₁, h₁, rfl⟩ | ⟨b₁, u, ρ₁, h₁, P₁, hw₁, rfl⟩
  · -- `own(u) ○ mut = mut`: the composites are the `mut` operands
    have hu : u = v := by simpa using (CellU.CompR.erase hc).1
    have hu' : u = v' := by simpa using (CellU.CompR.erase hc').1
    subst hu
    subst hu'
    have e := CellU.CompR.functional hc (CellU.CompR.ownMut _ _ _ _ _ _)
    have e' := CellU.CompR.functional hc' (CellU.CompR.ownMut _ _ _ _ _ _)
    have hb := CellU.mutOf_at e
    subst hb
    obtain ⟨-, -, hP⟩ := CellU.mutOf_inj e
    subst hP
    exact ⟨u, χ', h', hw', e'⟩
  · -- `imm ○ mut = imm`: no `mut` composite
    have hk := (CellU.CompR.imm_left hc (CellU.kind_immOf _ _ _ _)).1
    simp at hk
  · -- `mut ○ mut`: both operands share `ψ₁`'s value and witness, so they are one cell
    have hv : u = v := by simpa using (CellU.CompR.erase hc).1
    have hv' : u = v' := by simpa using (CellU.CompR.erase hc').1
    have hχ : ρ₁ = χ := by simpa using CellU.CompR.wit hc (by simp) (by simp)
    have hχ' : ρ₁ = χ' := by simpa using CellU.CompR.wit hc' (by simp) (by simp)
    subst hv
    subst hv'
    subst hχ
    subst hχ'
    exact ⟨v₀, χ₀, h₀, hw₀, (CellU.CompR.functional hc hc').symm⟩

/-! ### 6.48's `mut` half -/

/-- **6.48's `mut` half under growth**, with the typed-world premise. -/
theorem updMutG_frame {F ρ π X Z : WRes} (hm : ResU.UpdMut ρ π) (hg : UpdImmG ρ π)
    (hprem : NoNewImmUnderMut F ρ π) (hX : ResU.CompS F ρ X) (hZ : ResU.CompS F π Z)
    (hvX : ResU.Valid X) (hvZ : ResU.Valid Z) : ResU.UpdMut X Z := by
  obtain ⟨σX, hσX⟩ := hvX
  obtain ⟨σZ, hσZ⟩ := hvZ
  obtain ⟨σF, hσF⟩ := (ResU.Valid.split hX ⟨σX, hσX⟩).1
  obtain ⟨σρ, hσρ⟩ := (ResU.Valid.split hX ⟨σX, hσX⟩).2
  obtain ⟨σπ, hσπ⟩ := (ResU.Valid.split hZ ⟨σZ, hσZ⟩).2
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩ :=
    (ResU.Flat.split hX).mp hσX
  obtain ⟨e₁', e₃, e', a₁', a₃, a', he₁', he₃, hec', ha₁', ha₃, hac', hc'⟩ :=
    (ResU.Flat.split hZ).mp hσZ
  rw [ExS.functional he₁' he₁] at hec'
  rw [AgW.functional ha₁' ha₁] at hac'
  have heX : ExS X e := (ExS.split hX).mpr ⟨e₁, e₂, he₁, he₂, hec⟩
  have heZ : ExS Z e' := (ExS.split hZ).mpr ⟨e₁, e₃, he₁, he₃, hec'⟩
  -- the parts' flattenings, at the walks above
  have hcF : ResU.CompS e₁ a₁ σF := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hσF
    rwa [ExS.functional hx he₁, AgW.functional hy ha₁] at hxy
  have hcρ : ResU.CompS e₂ a₂ σρ := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hσρ
    rwa [ExS.functional hx he₂, AgW.functional hy ha₂] at hxy
  have hcπ : ResU.CompS e₃ a₃ σπ := by
    obtain ⟨x, y, hx, hy, hxy⟩ := hσπ
    rwa [ExS.functional hx he₃, AgW.functional hy ha₃] at hxy
  -- `↭`'s `mut` clause at the flattenings
  have mρπ : ∀ n b P, HasMut σρ n b P → HasMut σπ n b P := by
    rintro n b P ⟨v, χ, h, hw, e0⟩
    obtain ⟨v', χ', h', hw', σ', hσ', e''⟩ := (hm n b P).mp ⟨v, χ, h, hw, σρ, hσρ, e0⟩
    rw [ResU.Flat.functional hσ' hσπ] at e''
    exact ⟨v', χ', h', hw', e''⟩
  have mπρ : ∀ n b P, HasMut σπ n b P → HasMut σρ n b P := by
    rintro n b P ⟨v, χ, h, hw, e0⟩
    obtain ⟨v', χ', h', hw', σ', hσ', e''⟩ := (hm n b P).mpr ⟨v, χ, h, hw, σπ, hσπ, e0⟩
    rw [ResU.Flat.functional hσ' hσρ] at e''
    exact ⟨v', χ', h', hw', e''⟩
  -- an `imm` cell of `ρ` at `n` grows into `π` at `n`
  have growπ : ∀ n (c : CellU Loc Val), σρ.get n = some c → c.kind = Kind.imm →
      ∃ c', σπ.get n = some c' ∧ c'.kind = Kind.imm := by
    intro n c e0 k
    obtain ⟨s, hs, hc0⟩ := CellU.imm_eta k
    rw [hc0] at e0
    obtain ⟨s', h', -, σ', hσ', e''⟩ := hg.1 n s c.erase c.wit hs ⟨σρ, hσρ, e0⟩
    rw [ResU.Flat.functional hσ' hσπ] at e''
    exact ⟨_, e'', CellU.kind_immOf _ _ _ _⟩
  -- the reverse: π has no `mut` at `n` where ρ has none
  refine fun n b P => ⟨?_, ?_⟩
  · -- `X` → `Z`
    rintro ⟨v, χ, hχ, hw, σ, hσ, eX⟩
    rw [ResU.Flat.functional hσ hσX] at eX
    have hk : (CellU.mutOf b v χ hχ P hw).kind ≠ Kind.imm := by simp
    suffices H : HasMut σZ n b P by
      obtain ⟨v', χ', h', hw', e0⟩ := H
      exact ⟨v', χ', h', hw', σZ, hσZ, e0⟩
    rcases ResU.CompS.get_split_of_ne_imm hc eX hk with ⟨fe, fa⟩ | ⟨fe, fa⟩
    · rcases ResU.CompS.get_split_of_ne_imm hec fe hk with ⟨f1, f2⟩ | ⟨f1, f2⟩
      · -- `ex(F)` holds it
        have := (ResU.CompS.get_left_of_ne_imm hec' f1 hk).2
        exact ⟨v, χ, hχ, hw, (flat_of_ex heZ hc' this).1⟩
      · -- `ex(ρ)` holds it
        obtain ⟨v', χ', h', hw', eπ⟩ := mρπ n b P ⟨v, χ, hχ, hw, (flat_of_ex he₂ hcρ f2).1⟩
        rcases ResU.CompS.get_split_of_ne_imm hcπ eπ (by simp) with ⟨g3, -⟩ | ⟨g3, g3a⟩
        · exact ⟨v', χ', h', hw', (flat_of_ex heZ hc' (comp_get_right hec' f1 g3)).1⟩
        · have ha1 : a₁.get n = none := (comp_none_parts hac fa).1
          exact ⟨v', χ', h', hw', flat_of_ag heZ hc' (comp_get_right hac' ha1 g3a)⟩
    · obtain ⟨fe1, fe2⟩ := comp_none_parts hec fe
      rcases ResU.Comp.get hac n with ⟨-, -, g⟩ | ⟨ψ, g1, g2, g⟩ | ⟨ψ, g1, g2, g⟩ |
          ⟨ψ₁, ψ₂, ψ, g1, g2, g, hcc⟩
      · rw [fa] at g; cases g
      · -- `ag(F)` holds it, `ρ` is silent: by the premise, so is `π` up to `own`
        rw [fa] at g
        cases Option.some.inj g
        have hρn : σρ.get n = none := comp_get_none hcρ fe2 g2
        have hFn : σF.get n = some (CellU.mutOf b v χ hχ P hw) := flat_of_ag he₁ hcF g1
        have ha' : a'.get n = some (CellU.mutOf b v χ hχ P hw) := by
          cases g3 : a₃.get n with
          | none => exact comp_get_left hac' g1 g3
          | some ψ₃ =>
              have hπ3 : σπ.get n = some ψ₃ := flat_of_ag he₃ hcπ g3
              rcases CellU.rep ψ₃ with ⟨u, rfl⟩ | ⟨s₃, u, ρ₃, h₃, rfl⟩ |
                  ⟨b₃, u, ρ₃, h₃, P₃, hw₃, rfl⟩
              · obtain ⟨r, er, hr⟩ := comp_get_both hac' g1 g3
                rw [er, CellU.compR_own_kind_right hr rfl]
              · obtain ⟨c', ⟨σ', hσ', e''⟩, -⟩ := hprem n _ σF hσF hFn (by simp) _
                  ⟨σπ, hσπ, hπ3⟩ (CellU.kind_immOf _ _ _ _)
                rw [ResU.Flat.functional hσ' hσρ, hρn] at e''
                cases e''
              · obtain ⟨_, _, _, _, e''⟩ := mπρ n b₃ P₃ ⟨u, ρ₃, h₃, hw₃, hπ3⟩
                rw [hρn] at e''
                cases e''
        exact ⟨v, χ, hχ, hw, flat_of_ag heZ hc' ha'⟩
      · -- `ag(ρ)` holds it
        rw [fa] at g
        cases Option.some.inj g
        obtain ⟨v', χ', h', hw', eπ⟩ := mρπ n b P ⟨v, χ, hχ, hw, flat_of_ag he₂ hcρ g2⟩
        rcases ResU.CompS.get_split_of_ne_imm hcπ eπ (by simp) with ⟨g3, -⟩ | ⟨g3, g3a⟩
        · exact ⟨v', χ', h', hw', (flat_of_ex heZ hc' (comp_get_right hec' fe1 g3)).1⟩
        · exact ⟨v', χ', h', hw', flat_of_ag heZ hc' (comp_get_right hac' g1 g3a)⟩
      · -- both walks hold a cell
        rw [fa] at g
        cases Option.some.inj g
        rcases CellU.rep ψ₂ with ⟨u, rfl⟩ | ⟨s₂, u, ρ₂, h₂, rfl⟩ |
            ⟨b₂, u, ρ₂, h₂, P₂, hw₂, rfl⟩
        · -- `ψ₁ ○ own = ψ₁`, so `ag(F)` holds the `mut` cell
          have hψ₁ : (CellU.mutOf b v χ hχ P hw) = ψ₁ := CellU.compR_own_kind_right hcc rfl
          subst hψ₁
          have hρn : σρ.get n = some (CellU.ownOf u) := flat_of_ag he₂ hcρ g2
          have hFn : σF.get n = some (CellU.mutOf b v χ hχ P hw) := flat_of_ag he₁ hcF g1
          have ha' : a'.get n = some (CellU.mutOf b v χ hχ P hw) := by
            cases g3 : a₃.get n with
            | none => exact comp_get_left hac' g1 g3
            | some ψ₃ =>
                have hπ3 : σπ.get n = some ψ₃ := flat_of_ag he₃ hcπ g3
                rcases CellU.rep ψ₃ with ⟨u', rfl⟩ | ⟨s₃, u', ρ₃, h₃, rfl⟩ |
                    ⟨b₃, u', ρ₃, h₃, P₃, hw₃, rfl⟩
                · obtain ⟨r, er, hr⟩ := comp_get_both hac' g1 g3
                  rw [er, CellU.compR_own_kind_right hr rfl]
                · obtain ⟨c', ⟨σ', hσ', e''⟩, kc'⟩ := hprem n _ σF hσF hFn (by simp) _
                    ⟨σπ, hσπ, hπ3⟩ (CellU.kind_immOf _ _ _ _)
                  rw [ResU.Flat.functional hσ' hσρ, hρn] at e''
                  cases Option.some.inj e''
                  simp at kc'
                · obtain ⟨_, _, _, _, e''⟩ := mπρ n b₃ P₃ ⟨u', ρ₃, h₃, hw₃, hπ3⟩
                  rw [hρn] at e''
                  exact absurd (Option.some.inj e'') CellU.ownOf_ne_mutOf
          exact ⟨v, χ, hχ, hw, flat_of_ag heZ hc' ha'⟩
        · -- `ψ₁ ○ imm` is `imm`
          have hk' := (CellU.CompR.imm_left (CellU.CompR.comm hcc) (CellU.kind_immOf _ _ _ _)).1
          simp at hk'
        · -- `ψ₁ ○ mut`: `π` holds a `mut` cell of the same lifetime and predicate there
          obtain ⟨v', χ', h', hw', eπ⟩ := mρπ n b₂ P₂ ⟨u, ρ₂, h₂, hw₂, flat_of_ag he₂ hcρ g2⟩
          have g3 : a₃.get n = some (CellU.mutOf b₂ v' χ' h' P₂ hw') := by
            rcases ResU.CompS.get_split_of_ne_imm hcπ eπ (by simp) with ⟨g3, -⟩ | ⟨-, g3a⟩
            · -- an `ex(π)` cell would meet `ag(F)`'s at `n` in `⦇Z⦈`
              obtain ⟨r, hr⟩ := comp_some_left hac' g1
              have h0 := ex_none_of_ag heZ hc' hr
              rw [comp_get_right hec' fe1 g3] at h0
              cases h0
            · exact g3a
          obtain ⟨r, er, hr⟩ := comp_get_both hac' g1 g3
          obtain ⟨v₀, χ₀, h₀, hw₀, hr0⟩ :=
            compR_mut_pair hcc hr ⟨v, χ, hχ, hw, rfl⟩
          exact ⟨v₀, χ₀, h₀, hw₀, flat_of_ag heZ hc' (er.trans (congrArg some hr0))⟩
  · -- `Z` → `X`
    rintro ⟨v, χ, hχ, hw, σ, hσ, eZ⟩
    rw [ResU.Flat.functional hσ hσZ] at eZ
    have hk : (CellU.mutOf b v χ hχ P hw).kind ≠ Kind.imm := by simp
    suffices H : HasMut σX n b P by
      obtain ⟨v', χ', h', hw', e0⟩ := H
      exact ⟨v', χ', h', hw', σX, hσX, e0⟩
    rcases ResU.CompS.get_split_of_ne_imm hc' eZ hk with ⟨fe, fa⟩ | ⟨fe, fa⟩
    · rcases ResU.CompS.get_split_of_ne_imm hec' fe hk with ⟨f1, f3⟩ | ⟨f1, f3⟩
      · -- `ex(F)` holds it
        have := (ResU.CompS.get_left_of_ne_imm hec f1 hk).2
        exact ⟨v, χ, hχ, hw, (flat_of_ex heX hc this).1⟩
      · -- `ex(π)` holds it
        obtain ⟨v', χ', h', hw', eρ⟩ := mπρ n b P ⟨v, χ, hχ, hw, (flat_of_ex he₃ hcπ f3).1⟩
        rcases ResU.CompS.get_split_of_ne_imm hcρ eρ (by simp) with ⟨g2, -⟩ | ⟨g2, g2a⟩
        · exact ⟨v', χ', h', hw', (flat_of_ex heX hc (comp_get_right hec f1 g2)).1⟩
        · have ha1 : a₁.get n = none := (comp_none_parts hac' fa).1
          exact ⟨v', χ', h', hw', flat_of_ag heX hc (comp_get_right hac ha1 g2a)⟩
    · obtain ⟨fe1, fe3⟩ := comp_none_parts hec' fe
      -- where `a₂` holds no `mut` and no `imm` cell, `ψ₁`'s composite with it is `ψ₁`
      have keepF : ∀ (m : CellU Loc Val), a₁.get n = some m → m.kind = Kind.mut →
          (∀ ψ₃, a₃.get n = some ψ₃ → ψ₃.kind = Kind.own) → a.get n = some m := by
        intro m g1 km h3
        cases g2 : a₂.get n with
        | none => exact comp_get_left hac g1 g2
        | some ψ₂ =>
            rcases CellU.rep ψ₂ with ⟨u, rfl⟩ | ⟨s₂, u, ρ₂, h₂, rfl⟩ |
                ⟨b₂, u, ρ₂, h₂, P₂, hw₂, rfl⟩
            · obtain ⟨r, er, hr⟩ := comp_get_both hac g1 g2
              rw [er, CellU.compR_own_kind_right hr rfl]
            · obtain ⟨c', e'', kc'⟩ :=
                growπ n _ (flat_of_ag he₂ hcρ g2) (CellU.kind_immOf _ _ _ _)
              obtain ⟨t, ht, hct⟩ := CellU.imm_eta kc'
              have g3 : a₃.get n = some c' := ResU.ag_eq_flat_at_imm he₃ hcπ e'' kc'
              have := h3 c' g3
              rw [kc'] at this
              cases this
            · obtain ⟨v', χ', h', hw', eπ⟩ :=
                mρπ n b₂ P₂ ⟨u, ρ₂, h₂, hw₂, flat_of_ag he₂ hcρ g2⟩
              rcases ResU.CompS.get_split_of_ne_imm hcπ eπ (by simp) with ⟨g3, -⟩ | ⟨-, g3a⟩
              · rw [fe3] at g3; cases g3
              · have := h3 _ g3a
                simp at this
      rcases ResU.Comp.get hac' n with ⟨-, -, g⟩ | ⟨ψ, g1, g3, g⟩ | ⟨ψ, g1, g3, g⟩ |
          ⟨ψ₁, ψ₃, ψ, g1, g3, g, hcc⟩
      · rw [fa] at g; cases g
      · -- `ag(F)` holds it and `π` is silent
        rw [fa] at g
        cases Option.some.inj g
        have ha := keepF _ g1 (by simp) (fun ψ₃ e3 => by rw [g3] at e3; cases e3)
        exact ⟨v, χ, hχ, hw, flat_of_ag heX hc ha⟩
      · -- `ag(π)` holds it
        rw [fa] at g
        cases Option.some.inj g
        obtain ⟨v', χ', h', hw', eρ⟩ := mπρ n b P ⟨v, χ, hχ, hw, flat_of_ag he₃ hcπ g3⟩
        rcases ResU.CompS.get_split_of_ne_imm hcρ eρ (by simp) with ⟨g2, -⟩ | ⟨-, g2a⟩
        · exact ⟨v', χ', h', hw', (flat_of_ex heX hc (comp_get_right hec fe1 g2)).1⟩
        · exact ⟨v', χ', h', hw', flat_of_ag heX hc (comp_get_right hac g1 g2a)⟩
      · rw [fa] at g
        cases Option.some.inj g
        rcases CellU.rep ψ₃ with ⟨u, rfl⟩ | ⟨s₃, u, ρ₃, h₃, rfl⟩ |
            ⟨b₃, u, ρ₃, h₃, P₃, hw₃, rfl⟩
        · -- `ψ₁ ○ own = ψ₁`
          have hψ₁ : (CellU.mutOf b v χ hχ P hw) = ψ₁ := CellU.compR_own_kind_right hcc rfl
          subst hψ₁
          have ha := keepF _ g1 (by simp)
            (fun ψ₃ e3 => by rw [g3] at e3; cases Option.some.inj e3; rfl)
          exact ⟨v, χ, hχ, hw, flat_of_ag heX hc ha⟩
        · have hk' := (CellU.CompR.imm_left (CellU.CompR.comm hcc) (CellU.kind_immOf _ _ _ _)).1
          simp at hk'
        · obtain ⟨v', χ', h', hw', eρ⟩ :=
            mπρ n b₃ P₃ ⟨u, ρ₃, h₃, hw₃, flat_of_ag he₃ hcπ g3⟩
          obtain ⟨r0, hr0⟩ := comp_some_left hac g1
          have he0 : e.get n = none := ex_none_of_ag heX hc hr0
          have fe2 : e₂.get n = none := (comp_none_parts hec he0).2
          have g2 : a₂.get n = some (CellU.mutOf b₃ v' χ' h' P₃ hw') := by
            rcases ResU.CompS.get_split_of_ne_imm hcρ eρ (by simp) with ⟨g2, -⟩ | ⟨-, g2a⟩
            · rw [fe2] at g2; cases g2
            · exact g2a
          obtain ⟨r, er, hr⟩ := comp_get_both hac g1 g2
          obtain ⟨v₀, χ₀, h₀, hw₀, hr1⟩ := compR_mut_pair hcc hr ⟨v, χ, hχ, hw, rfl⟩
          exact ⟨v₀, χ₀, h₀, hw₀, flat_of_ag heX hc (er.trans (congrArg some hr1))⟩

/-- **6.48 under growth**, with the typed-world premise. -/
theorem updVG_frame {F ρ π X Z : WRes} (h : UpdVG ρ π) (hprem : NoNewImmUnderMut F ρ π)
    (hX : ResU.CompS F ρ X) (hZ : ResU.CompS F π Z) (hvX : ResU.Valid X)
    (hvZ : ResU.Valid Z) : UpdVG X Z :=
  ⟨⟨updImmG_frame h.1.1 hX hZ hvX hvZ, updMutG_frame h.1.2 h.1.1 hprem hX hZ hvX hvZ⟩, hvX, hvZ⟩

end BoCa.Fig16.LicUpd

end
