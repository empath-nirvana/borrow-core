import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Ancestors
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.Lifetimes
import Support.Model.Prelude
import Support.Model.Singletons
import Support.Model.WalkSplitting

/-!
# Support — Model — Subtraction

`[about ours]`.  Definition 6.3's `⊟`: lifetime-set difference, and `⊟` inhabited, total and a term at `SubKeep`.
-/

noncomputable section

namespace BoCa.Fig16

theorem LSet.diff_join_le {s t u : LSet} (h : LSet.Diff s t u) : u.join ≤ s.join :=
  s.join_greatest _ ((h u.join).mp u.join_mem).1

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `ᾱ ∖ β̄ ⊆ ᾱ`, so a witness at `⊔ᾱ` is a witness at `⊔(ᾱ ∖ β̄)`. -/
theorem LSet.diff_inStratum {s t u : LSet} (h : LSet.Diff s t u)
    {ρ : ResU Loc Val} (hρ : ρ.InStratum s.join) : ρ.InStratum u.join :=
  fun l ψ e => by
    have hs := hρ l ψ e
    cases ψ
    · exact trivial
    · exact lt_of_le_of_lt (LSet.diff_join_le h) hs
    · exact lt_of_le_of_lt (LSet.diff_join_le h) hs

end BoCa.Fig16

namespace BoCa.Fig16

/-- Whenever the difference is nonempty it is an `LSet`. -/
theorem LSet.exists_diff {s t : LSet} (h : ¬ LSet.DiffEmpty s t) :
    ∃ u : LSet, LSet.Diff s t u := by
  have hne : ∃ x, s.mem x ∧ ¬ t.mem x :=
    Classical.byContradiction fun hc =>
      h (fun x hx => Classical.byContradiction fun ht => hc ⟨x, hx, ht⟩)
  obtain ⟨x₀, hx₀, ht₀⟩ := hne
  obtain ⟨m, hm, hub⟩ :=
    LSet.exists_greatest (fun y => s.mem y ∧ ¬ t.mem y) s.meet ⟨x₀, hx₀, ht₀⟩
      (fun y hy => s.meet_least y hy.1)
  obtain ⟨lo, hlo, hlo'⟩ :=
    LSet.exists_least (fun y => s.mem y ∧ ¬ t.mem y) m ⟨m, hm, Nat.le_refl m⟩
  exact ⟨⟨fun y => s.mem y ∧ ¬ t.mem y, lo, m, hlo, hm, hlo', hub⟩, fun _ => Iff.rfl⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- Every `ρ ⊟ ρ′` on the paragraph's reading (§12.58) is one on the bullets'
reading. -/
theorem ResU.SubKeep.toSub {ρ ρ' χ : ResU Loc Val} (h : ResU.SubKeep ρ ρ' χ) :
    ResU.Sub ρ ρ' χ := by
  obtain ⟨ρ'', h1, h2, h3, h4, h5⟩ := h
  exact ⟨ρ'', h1, h2, fun l hd he => by rw [h3 l hd he]; exact hd, h4, h5⟩

end BoCa.Fig16

namespace BoCa.Fig16

/-- `ᾱ ∖ β̄` is determined by `ᾱ` and `β̄`. -/
theorem LSet.Diff.functional {s t u u' : LSet} (h : LSet.Diff s t u)
    (h' : LSet.Diff s t u') : u = u' :=
  LSet.ext fun x => (h x).trans (h' x).symm

/-- `(ᾱ ∖ β̄) ∪ β̄ = ᾱ` when `β̄ ⊆ ᾱ` — the printed *"removing the lifetimes of
borrows from `ρ′`, but keeping the lifetimes only in `ρ`"*, read back. -/
theorem LSet.diff_union {s t u : LSet} (h : LSet.Diff s t u)
    (ht : ∀ x, t.mem x → s.mem x) : u.union t = s := by
  classical
  refine LSet.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rcases hx with hx | hx
    · exact ((h x).mp hx).1
    · exact ht x hx
  · by_cases hxt : t.mem x
    · exact Or.inr hxt
    · exact Or.inl ((h x).mpr ⟨hx, hxt⟩)

/-- `ᾱ ∖ β̄ = ∅` with `β̄ ⊆ ᾱ` says `ᾱ = β̄`. -/
theorem LSet.eq_of_diffEmpty {s t : LSet} (h : LSet.DiffEmpty s t)
    (ht : ∀ x, t.mem x → s.mem x) : s = t :=
  LSet.ext fun x => ⟨h x, ht x⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `ρ|own,mut` at a location, read back. -/
theorem ResU.exclPart_eq_some {ρ : ResU Loc Val} {l : Loc} {ψ : CellU Loc Val} :
    ρ.exclPart.get l = some ψ ↔ (ρ.get l = some ψ ∧ ψ.kind ≠ Kind.imm) := by
  rw [show ρ.exclPart = ρ.restrictOn (fun k => !(k == Kind.imm)) from rfl,
    ResU.restrictOn_eq_some]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩

/-- `ρ = ρ|own,mut ● ρ|imm` — a cell's tag is `imm` or it is not. -/
theorem ResU.exclPart_restrict_compS (ρ : ResU Loc Val) :
    ResU.CompS ρ.exclPart (ρ.restrict Kind.imm) ρ := by
  have hcase : ∀ l, (ρ.exclPart.get l = ρ.get l ∧ (ρ.restrict Kind.imm).get l = none) ∨
      (ρ.exclPart.get l = none ∧ (ρ.restrict Kind.imm).get l = ρ.get l) := by
    intro l
    cases e : ρ.get l with
    | none =>
        have h1 : ρ.exclPart.get l = none := by
          cases f : ρ.exclPart.get l with
          | none => rfl
          | some ζ => rw [(ResU.exclPart_eq_some.mp f).1] at e; exact absurd e (by simp)
        exact Or.inl ⟨h1, ResU.restrict_get_none e⟩
    | some ζ =>
        by_cases hk : ζ.kind = Kind.imm
        · have h1 : ρ.exclPart.get l = none := by
            cases f : ρ.exclPart.get l with
            | none => rfl
            | some ξ =>
                obtain ⟨g1, g2⟩ := ResU.exclPart_eq_some.mp f
                rw [e] at g1
                cases Option.some.inj g1
                exact absurd hk g2
          exact Or.inr ⟨h1, ResU.restrict_get_some e hk⟩
        · exact Or.inl ⟨ResU.exclPart_eq_some.mpr ⟨e, hk⟩,
            ResU.restrict_get_ne e hk⟩
  refine ⟨ResU.Compat.of_disjoint (fun l => ?_), fun l => ?_⟩
  · rcases hcase l with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  · show OptComp CellU.CompS (ρ.exclPart.get l) ((ρ.restrict Kind.imm).get l) (ρ.get l)
    rcases hcase l with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂] <;>
      cases ρ.get l with
      | none => rfl
      | some ζ => rfl

open Classical in
/-- `ψ` with the lifetimes of `t̄` removed.
`[about ours: `[TR]` Definition 6.3's fourth bullet, as a function on cells]` -/
noncomputable def CellU.subLS (ζ : CellU Loc Val) (t : LSet) : Option (CellU Loc Val) :=
  match ζ with
  | .imm i =>
      if h : LSet.DiffEmpty i.ls t then none
      else some (CellU.immOf (LSet.exists_diff h).choose i.v i.res
        (LSet.diff_inStratum (LSet.exists_diff h).choose_spec i.ρ.toU_inStratum))
  | _ => none

open Classical in
theorem CellU.subLS_of_diffEmpty {s t : LSet} {v : Val} {χ : ResU Loc Val}
    {h : χ.InStratum s.join} (hd : LSet.DiffEmpty s t) :
    (CellU.immOf s v χ h).subLS t = none := by
  show (if _ : LSet.DiffEmpty s t then none else _) = none
  rw [dif_pos hd]

open Classical in
theorem CellU.subLS_of_diff {s t u : LSet} {v : Val} {χ : ResU Loc Val}
    {h : χ.InStratum s.join} (hu : LSet.Diff s t u) (hd : ¬ LSet.DiffEmpty s t) :
    ∃ hu' : χ.InStratum u.join,
      (CellU.immOf s v χ h).subLS t = some (CellU.immOf u v χ hu') := by
  refine ⟨LSet.diff_inStratum hu h, ?_⟩
  show (if _ : LSet.DiffEmpty s t then none else _) = _
  rw [dif_neg hd]
  refine congrArg some ?_
  refine CellU.immOf_congr (LSet.Diff.functional (LSet.exists_diff hd).choose_spec hu)
    rfl ?_ _ _
  exact CellU.wit_immOf s v χ h

/-- `ρ″` — Definition 6.3's witness, pointwise: `ρ|imm` off `dom(ρ′)`, and on it
the cell with `ρ′`'s lifetimes removed.
`[about ours: `[TR]` Definition 6.3's `ρ″`, as a construction]` -/
noncomputable def ResU.subWitness (ρ ρ' : ResU Loc Val) : ResU Loc Val where
  get := fun l =>
    ((ρ.restrict Kind.imm).get l).bind fun ζ =>
      match (ρ'.get l).bind CellU.lsOf with
      | none => some ζ
      | some t => ζ.subLS t
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show ((ρ.restrict Kind.imm).get l).bind _ = none
    rw [ResU.restrict_get_none e]
    rfl

theorem ResU.subWitness_of_none {ρ ρ' : ResU Loc Val} {l : Loc}
    (h : ρ'.get l = none) :
    (ρ.subWitness ρ').get l = (ρ.restrict Kind.imm).get l := by
  show ((ρ.restrict Kind.imm).get l).bind _ = _
  rw [h]
  cases (ρ.restrict Kind.imm).get l with
  | none => rfl
  | some ζ => rfl

theorem ResU.subWitness_of_imm {ρ ρ' : ResU Loc Val} {l : Loc} {s t : LSet}
    {v : Val} {χ : ResU Loc Val} {h : χ.InStratum s.join} {ξ : CellU Loc Val}
    (hρ : (ρ.restrict Kind.imm).get l = some (CellU.immOf s v χ h))
    (hρ' : ρ'.get l = some ξ) (hls : CellU.lsOf ξ = some t) :
    (ρ.subWitness ρ').get l = (CellU.immOf s v χ h).subLS t := by
  show ((ρ.restrict Kind.imm).get l).bind _ = _
  rw [hρ, hρ']
  show (match CellU.lsOf ξ with | none => _ | some t => _) = _
  rw [hls]

theorem ResU.subWitness_dom {ρ ρ' : ResU Loc Val} {l : Loc} {ζ : CellU Loc Val}
    (h : (ρ.subWitness ρ').get l = some ζ) :
    ∃ φ, (ρ.restrict Kind.imm).get l = some φ := by
  cases e : (ρ.restrict Kind.imm).get l with
  | some φ => exact ⟨φ, rfl⟩
  | none =>
      exfalso
      have : (ρ.subWitness ρ').get l = none := by
        show ((ρ.restrict Kind.imm).get l).bind _ = none
        rw [e]; rfl
      rw [this] at h; exact absurd h (by simp)

/-- If `ρ′` carries `imm` cells only and, at every location it covers, `ρ`
carries an `imm` cell over the same value and witness whose lifetime set contains
`ρ′`'s, then `ρ ⊟ ρ′` is defined and composes with `ρ′` back to `ρ`.
`[about ours: `[TR]` Definition 6.3 inhabited at a general subtrahend; `⊟` and
`●` appear as their graphs (G4)]` -/
theorem ResU.sub_of_le {ρ ρ' : ResU Loc Val}
    (hexcl : ρ'.exclPart = PMap.empty)
    (hle : ∀ (l : Loc) (s' : LSet) (v : Val) (χ : ResU Loc Val)
        (h' : χ.InStratum s'.join), ρ'.get l = some (CellU.immOf s' v χ h') →
        ∃ (s : LSet) (h : χ.InStratum s.join),
          ρ.get l = some (CellU.immOf s v χ h) ∧ ∀ x, s'.mem x → s.mem x) :
    ∃ ψ, ResU.SubKeep ρ ρ' ψ ∧ ResU.CompS ψ ρ' ρ := by
  classical
  have hpair : ∀ l ξ, ρ'.get l = some ξ →
      ∃ (s' s : LSet) (v : Val) (χ : ResU Loc Val)
        (h' : χ.InStratum s'.join) (h : χ.InStratum s.join),
        ρ'.get l = some (CellU.immOf s' v χ h') ∧
        ρ.get l = some (CellU.immOf s v χ h) ∧
        CellU.lsOf ξ = some s' ∧ (∀ x, s'.mem x → s.mem x) := by
    intro l ξ hξ
    have hk : ξ.kind = Kind.imm := by
      by_contra hk
      have hx : ρ'.exclPart.get l = some ξ := ResU.exclPart_eq_some.mpr ⟨hξ, hk⟩
      rw [hexcl] at hx; exact absurd hx (by simp)
    obtain ⟨s', hs', heta⟩ := CellU.imm_eta hk
    obtain ⟨s, h, hρ, hsub⟩ := hle l s' ξ.erase ξ.wit hs' (hξ.trans (congrArg some heta))
    exact ⟨s', s, ξ.erase, ξ.wit, hs', h, hξ.trans (congrArg some heta), hρ,
      by rw [heta]; rfl, hsub⟩
  have hloc : ∀ l, OptComp CellU.CompS ((ρ.subWitness ρ').get l) (ρ'.get l)
      ((ρ.restrict Kind.imm).get l) := by
    intro l
    cases hξ : ρ'.get l with
    | none =>
        rw [ResU.subWitness_of_none hξ]
        cases (ρ.restrict Kind.imm).get l with
        | none => rfl
        | some ζ => rfl
    | some ξ =>
        obtain ⟨s', s, v, χ, h', h, hρ'l, hρl, hlsξ, hsub⟩ := hpair l ξ hξ
        have hρi : (ρ.restrict Kind.imm).get l = some (CellU.immOf s v χ h) :=
          ResU.restrict_get_some hρl (CellU.kind_immOf _ _ _ _)
        have hξeq : ξ = CellU.immOf s' v χ h' := Option.some.inj (hξ.symm.trans hρ'l)
        by_cases hd : LSet.DiffEmpty s s'
        · have hss : s = s' := LSet.eq_of_diffEmpty hd hsub
          rw [ResU.subWitness_of_imm hρi hξ hlsξ, CellU.subLS_of_diffEmpty hd, hρi,
            hξeq]
          show some (CellU.immOf s v χ h) = some (CellU.immOf s' v χ h')
          exact congrArg some (CellU.immOf_congr hss rfl rfl h h')
        · obtain ⟨u, hu⟩ := LSet.exists_diff hd
          obtain ⟨hu', hsub'⟩ := CellU.subLS_of_diff (v := v) (χ := χ) (h := h) hu hd
          rw [ResU.subWitness_of_imm hρi hξ hlsξ, hsub', hρi, hξeq]
          refine ⟨CellU.immOf s v χ h, rfl, u, s', v, χ, hu', h',
            ResU.InStratum.sup hu' h', rfl, rfl, ?_⟩
          exact CellU.immOf_congr (LSet.diff_union hu hsub).symm rfl rfl h _
  have hLe : ResU.CompS (ρ.subWitness ρ') ρ' (ρ.restrict Kind.imm) := by
    refine ⟨fun l ζ ξ e₁ e₂ => ?_, hloc⟩
    have hp := hloc l
    rw [e₁, e₂] at hp
    obtain ⟨ω, -, hC⟩ := hp
    exact CellU.CompS.compat hC
  have hdom : ∀ m, (ρ.restrict Kind.imm).get m ≠ none → ρ'.get m = none →
      (ρ.subWitness ρ').get m = (ρ.restrict Kind.imm).get m :=
    fun m _ h₂ => ResU.subWitness_of_none h₂
  have hclause : ResU.SubClause ρ ρ' (ρ.subWitness ρ') := by
    intro m s s' w ρi h h' e e'
    have hρi : (ρ.restrict Kind.imm).get m = some (CellU.immOf s w ρi h) :=
      ResU.restrict_get_some e (CellU.kind_immOf _ _ _ _)
    have hls : CellU.lsOf (CellU.immOf s' w ρi h') = some s' := rfl
    refine ⟨fun hd => ?_, fun u hu hd => ?_⟩
    · rw [ResU.subWitness_of_imm hρi e' hls]; exact CellU.subLS_of_diffEmpty hd
    · obtain ⟨hu', hsub'⟩ := CellU.subLS_of_diff (v := w) (χ := ρi) (h := h) hu hd
      exact ⟨hu', by rw [ResU.subWitness_of_imm hρi e' hls, hsub']⟩
  have hsplit := ResU.exclPart_restrict_compS ρ
  have hdisj2 : ResU.CompatS ρ.exclPart (ρ.subWitness ρ') :=
    ResU.Compat.of_disjoint (fun m => by
      cases f : ρ.exclPart.get m with
      | none => exact Or.inl rfl
      | some ζ =>
          refine Or.inr ?_
          cases g : (ρ.subWitness ρ').get m with
          | none => rfl
          | some ξ =>
              obtain ⟨φ, hφ⟩ := ResU.subWitness_dom g
              obtain ⟨g1, g2⟩ := ResU.exclPart_eq_some.mp f
              obtain ⟨k1, k2⟩ := ResU.restrict_eq_some.mp hφ
              rw [g1] at k1
              cases Option.some.inj k1
              exact absurd k2 g2)
  obtain ⟨ψ, hψ⟩ := (ResU.compS_defined_iff _ _).mpr hdisj2
  refine ⟨ψ, ⟨ρ.subWitness ρ', hexcl, ⟨_, hLe⟩, hdom, hclause, hψ⟩, ?_⟩
  obtain ⟨y, hy, hyc⟩ :=
    (ResU.CompS.assoc ρ.exclPart (ρ.subWitness ρ') ρ' ρ).mp ⟨_, hLe, hsplit⟩
  rwa [ResU.CompS.functional hy hψ] at hyc

/-- `⊟` is single-valued on the paragraph's reading, under `ResU.sub_of_le`'s
hypothesis (which `[TR]` 6.52's H1 establishes).
`[about ours]` -/
theorem ResU.SubKeep.functional {ρ ρ' χ χ' : ResU Loc Val}
    (hle : ∀ (l : Loc) (s' : LSet) (v : Val) (w : ResU Loc Val)
        (h' : w.InStratum s'.join), ρ'.get l = some (CellU.immOf s' v w h') →
        ∃ (s : LSet) (h : w.InStratum s.join),
          ρ.get l = some (CellU.immOf s v w h) ∧ ∀ x, s'.mem x → s.mem x)
    (h₁ : ResU.SubKeep ρ ρ' χ) (h₂ : ResU.SubKeep ρ ρ' χ') : χ = χ' := by
  classical
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ := h₁
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5⟩ := h₂
  have hnone : ∀ (c : ResU Loc Val), ResU.Le c (ρ.restrict Kind.imm) →
      ∀ l, (ρ.restrict Kind.imm).get l = none → c.get l = none := by
    rintro c ⟨τ, hτ⟩ l hl
    exact ((ResU.Comp.eq_none_iff hτ l).mp hl).1
  have hab : a = b := by
    refine PMap.ext fun l => ?_
    cases hi : (ρ.restrict Kind.imm).get l with
    | none => rw [hnone a ha2 l hi, hnone b hb2 l hi]
    | some φ =>
        have hine : (ρ.restrict Kind.imm).get l ≠ none := by rw [hi]; simp
        cases hξ : ρ'.get l with
        | none => rw [ha3 l hine hξ, hb3 l hine hξ]
        | some ξ =>
            have hk : ξ.kind = Kind.imm := by
              by_contra hk
              have hx : ρ'.exclPart.get l = some ξ :=
                ResU.exclPart_eq_some.mpr ⟨hξ, hk⟩
              rw [ha1] at hx; exact absurd hx (by simp)
            obtain ⟨s', hs', heta⟩ := CellU.imm_eta hk
            obtain ⟨s, h, hρl, hsub⟩ :=
              hle l s' ξ.erase ξ.wit hs' (hξ.trans (congrArg some heta))
            have hρ'l : ρ'.get l = some (CellU.immOf s' ξ.erase ξ.wit hs') :=
              hξ.trans (congrArg some heta)
            have hA := ha4 l s s' ξ.erase ξ.wit h hs' hρl hρ'l
            have hB := hb4 l s s' ξ.erase ξ.wit h hs' hρl hρ'l
            by_cases hd : LSet.DiffEmpty s s'
            · rw [hA.1 hd, hB.1 hd]
            · obtain ⟨u, hu⟩ := LSet.exists_diff hd
              obtain ⟨huA, hgA⟩ := hA.2 u hu hd
              obtain ⟨huB, hgB⟩ := hB.2 u hu hd
              rw [hgA, hgB]
  exact ResU.CompS.functional ha5 (hab ▸ hb5)

/-- `[TR]` 6.52's `ρ = (ρ ⊟ ρ′) ● ρ′` holds of every `χ` that `ResU.SubKeep`
admits.
`[about ours: `[TR]` 6.52's equation at any `ResU.SubKeep`]` -/
theorem ResU.SubKeep.compS {ρ ρ' χ : ResU Loc Val}
    (hle : ∀ (l : Loc) (s' : LSet) (v : Val) (w : ResU Loc Val)
        (h' : w.InStratum s'.join), ρ'.get l = some (CellU.immOf s' v w h') →
        ∃ (s : LSet) (h : w.InStratum s.join),
          ρ.get l = some (CellU.immOf s v w h) ∧ ∀ x, s'.mem x → s.mem x)
    (h : ResU.SubKeep ρ ρ' χ) : ResU.CompS χ ρ' ρ := by
  obtain ⟨ψ, hψ, hcomp⟩ := ResU.sub_of_le h.choose_spec.1 hle
  rwa [ResU.SubKeep.functional hle h hψ]

end BoCa.Fig16

end
