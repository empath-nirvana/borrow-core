import Core.Relation
import Core.Chain.SI.ExtF

/-!
# Core's `Imm` clause and the chain's resume order: a configuration  `[spec §62]`

Core's `Imm` clause (`vCE`'s `imm` case, `Core/Relation.lean`) reads the record list: the cell is
coherent with a record (`CohE (rsOf ls)`), and its payload is read at `ls₀`, the records longer-lived
than the cell (`ptoImmS`). Core's `Mut` clause stores its payload read at the records longer-lived
than the cell (`ptoMutS`'s `ofS Q = P ls₀`). So with `Imm` in Core's shape, a `Mut` cell whose
payload holds an `imm` borrow stores a predicate that reads the list. Core keeps that predicate
fixed along its Kripke order `Ext`, whose second clause keeps exactly the records longer-lived than
every borrow cell of the resource (`vC_local`).

The chain resumes a continuation stopped under a live lend at every list `extF` admits
(`OpEntN.wc`, `entN`; `Core/Chain/SI/ExtF.lean`), which keeps the records the share's views name
and has no lifetime clause. The configuration:
a value of Core's `Mut 'x (Imm 'y 1)` at `ls` is not one at a list `ls'` with `extF ls ls' ρ`, where
`ls'` adds a record longer-lived than the cell (`coreMutImm_not_extF`). Core's `Ext` excludes `ls'`;
`extF` admits it.

This is the step a resumed `Mut` value's re-reading takes (`withbor3S_compat₀`'s step 13, the
resealed cell a `Mut @a A` value at the run's last list; `chain-interpretation.md` §5, D2). It is the step's
configuration, not the constant's: no run of `ConstN (.w3 …)` ending at `ls'` is built.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ImmShape791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Lifetime (LSub LifeVar)

/-- The record of an `imm` lend of `()` held at `m`. -/
def recU (m : Loc) : FrameRec := ⟨m, Val.unit, PMap.empty, .unit, LSub.empty⟩

/-- `m ↦ imm({c}, (), ∅)`. -/
def immU (m : Loc) (c : Life) : WRes :=
  ResU.single m (CellU.immOf (LSet.singleton c) Val.unit PMap.empty (ResU.inStratum_empty _))

/-- Core's `𝒱⟦Imm 'y 1⟧δ` at a list. -/
abbrev PImm (y : LifeVar) (δ : LSub) : List SRec → Val → WProp :=
  fun ls₀ => vCE (ℍ := ℍ) none true (.imm (.var y) .unit) ls₀ δ

theorem cohE_unit_of_mem {rs : List FrameRec} {m : Loc} {δ : LSub} (h : recU m ∈ rs) :
    CohE rs m .unit δ :=
  ⟨.unit, δ, trivial, Or.inl ⟨recU m, h, rfl, rfl, fun _ hv => by cases hv⟩⟩

theorem not_cohE_unit {m m' : Loc} (hm : m' ≠ m) {δ : LSub} :
    ¬ CohE [recU m] m' .unit δ := by
  rintro ⟨S₀, δ₀, he, hc⟩
  cases S₀ <;> simp [TyEq] at he
  rcases hc with ⟨r, hr, hle, -⟩ | ⟨r, hr, p, u, hch, -⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact hm hle
  · simp only [List.mem_singleton] at hr; subst hr
    cases hch with
    | one hp _ => cases hp
    | step hp _ _ => cases hp

/-- The `imm` cell at `m` is a value of Core's `Imm 'y 1` at every list holding its record above
`c`. -/
theorem pImm_of {y : LifeVar} {δ : LSub} {c : Life} (hy : δ.find? y = some c) {m : Loc}
    {ls : List SRec} (h : recU m ∈ rsOf ls) : PImm (ℍ := ℍ) y δ ls (Val.loc m) (immU m c) := by
  refine ⟨c, hy, m, pure_sep_mk ⟨rfl, cohE_unit_of_mem h⟩ ?_⟩
  refine ⟨LSet.singleton c, Val.unit, PMap.empty, ResU.inStratum_empty _,
    ls.filter (fun x => decide (c < x.2)), rfl, ⟨rfl, rfl⟩, le_refl _, fun x => by
      simp [List.mem_filter, LSet.singleton, Life.Sqsupset]⟩

/-- Every value of Core's `Imm 'y 1` lies in `Res_b` for `b ⊏ δ('y)`. -/
theorem pImm_inStratum {y : LifeVar} {δ : LSub} {b c : Life} (hy : δ.find? y = some c)
    (hbc : b < c) {ls : List SRec} {v : Val} {ρ : WRes} (h : PImm (ℍ := ℍ) y δ ls v ρ) :
    ρ.InStratum b := by
  obtain ⟨α, hα, ℓ, hs⟩ := h
  have hαc : α = c := Option.some.inj (hα.symm.trans hy)
  subst hαc
  obtain ⟨-, s, u, σ, hσ, ls₀, rfl, -, hle, -⟩ := pure_sep_iff.mp hs
  exact ResU.inStratum_single ℓ (show b < s.meet from lt_of_lt_of_le hbc hle)

/-- The stored predicate of a `mut` cell holding Core's `Imm 'y 1` at `ls`. -/
def famImm (y : LifeVar) (δ : LSub) (b : Life) (ls : List SRec) : Val → SPropS Loc Val b :=
  fun v r => PImm (ℍ := ℍ) y δ ls v r.1

theorem ofS_famImm {y : LifeVar} {δ : LSub} {b c : Life} (hy : δ.find? y = some c)
    (hbc : b < c) (ls : List SRec) : ofS (famImm (ℍ := ℍ) y δ b ls) = PImm (ℍ := ℍ) y δ ls := by
  funext v ρ
  exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨pImm_inStratum hy hbc h, h⟩⟩

/-- `ℓ ↦ mut(b, m, m ↦ imm({c}, (), ∅))`, storing `𝒱⟦Imm 'y 1⟧` read at `ls`. -/
def mutImm (y : LifeVar) (δ : LSub) {b c : Life} (hy : δ.find? y = some c) (hbc : b < c)
    (ℓ m : Loc) (ls : List SRec) (hm : recU m ∈ rsOf ls) : WRes :=
  ResU.single ℓ (CellU.mutOf b (Val.loc m) (immU m c)
    (ResU.inStratum_single m (show b < c from hbc)) (famImm (ℍ := ℍ) y δ b ls) (pImm_of hy hm))

/-- **Core's `Mut 'x (Imm 'y 1)` is not stable along `extF`.** With `δ('x) = b < δ('y) = c`, two
records `recU m`, `recU m'` (`m ≠ m'`) at a lifetime `t ⊐ b`, `ls = [(recU m, t)]` and
`ls' = ls ++ [(recU m', t)]`: the cell `ℓ ↦ mut(b, m, m ↦ imm({c}, (), ∅))` is a value of Core's
`Mut 'x (Imm 'y 1)` at `ls`; `extF ls ls'` holds at it; `Ext ls ls'` does not (the cell is a borrow
at `b` and `ls'` adds a record longer-lived than `b`); and it is not a value at `ls'`, since the
predicate the cell stores is `𝒱⟦Imm 'y 1⟧` at `ls`, which differs from the one at `ls'` at the
`imm` cell at `m'`. -/
theorem coreMutImm_not_extF (x y : LifeVar) (δ : LSub) {b c t : Life}
    (hx : δ.find? x = some b) (hy : δ.find? y = some c) (hbc : b < c) (hbt : b < t)
    (ℓ m m' : Loc) (hm : m' ≠ m) :
    let ls : List SRec := [(recU m, t)]
    let ls' : List SRec := [(recU m, t), (recU m', t)]
    ∃ ρ : WRes, vCE (ℍ := ℍ) none true (.mut (.var x) (.imm (.var y) .unit)) ls δ (Val.loc ℓ) ρ ∧
      extF ls ls' ρ ∧ ¬ Ext ls ls' ρ ∧
      ¬ vCE (ℍ := ℍ) none true (.mut (.var x) (.imm (.var y) .unit)) ls' δ (Val.loc ℓ) ρ := by
  intro ls ls'
  have hmls : recU m ∈ rsOf ls := by simp [ls, rsOf]
  refine ⟨mutImm (ℍ := ℍ) y δ hy hbc ℓ m ls hmls, ?_, ?_, ?_, ?_⟩
  · -- a value at `ls`: the cell stores `𝒱⟦Imm 'y 1⟧` at `ls₀ = ls`
    refine ⟨b, hx, ℓ, pure_sep_mk rfl ?_⟩
    refine ⟨b, Val.loc m, immU m c, ResU.inStratum_single m (show b < c from hbc),
      famImm (ℍ := ℍ) y δ b ls, pImm_of hy hmls, ls, le_refl _, rfl, ofS_famImm hy hbc ls, ?_,
      fun _ _ _ h => pImm_inStratum hy hbc h⟩
    intro z
    simp only [ls, List.mem_singleton, Life.Sqsupset]
    exact ⟨fun h => ⟨h, by rw [h]; exact hbt⟩, fun h => h.1⟩
  · -- `extF`: `ls ⊆ ls'`
    intro r hr _
    simp only [ls, ls', rsOf, List.map, List.mem_cons] at hr ⊢
    exact Or.inl (by simpa using hr)
  · -- not `Ext`: `ls'` adds `(recU m', t)`, `t ⊐ b`, at a borrow cell at `b`
    rintro ⟨-, hE⟩
    have hcell : CellIn (mutImm (ℍ := ℍ) y δ hy hbc ℓ m ls hmls) b :=
      ⟨ℓ, _, ResU.single_get_self _ _, CellU.kind_mutOf_ne_own, le_refl _⟩
    have := (hE b hcell (recU m', t) hbt).mpr (by simp [ls'])
    simp only [ls, List.mem_singleton, Prod.mk.injEq] at this
    exact hm (congrArg FrameRec.le this.1)
  · -- not a value at `ls'`: the stored predicate is the one at `ls`
    rintro ⟨α, hα, ℓ', hs⟩
    have hαb : α = b := Option.some.inj (hα.symm.trans hx)
    subst hαb
    obtain ⟨hℓ, b', u, σ, hσ, Q, hw, ls₀, -, hρ, hQ, hls₀, -⟩ := pure_sep_iff.mp hs
    have hℓℓ : ℓ' = ℓ := by cases hℓ; rfl
    subst hℓℓ
    have hget := congrArg (fun ρ : WRes => ρ.get ℓ') hρ
    simp only [mutImm, ResU.single_get_self, Option.some.injEq] at hget
    have hbb : α = b' := CellU.mutOf_at hget
    subst hbb
    obtain ⟨-, -, hQQ⟩ := CellU.mutOf_inj hget
    -- `ofS Q` is `𝒱⟦Imm 'y 1⟧` at `ls` and at `ls₀`
    have hP : PImm (ℍ := ℍ) y δ ls = PImm (ℍ := ℍ) y δ ls₀ := by
      rw [← ofS_famImm hy hbc ls, hQQ]; exact hQ
    have hin : recU m' ∈ rsOf ls₀ :=
      List.mem_map.mpr ⟨(recU m', t), (hls₀ _).mpr ⟨by simp [ls'], hbt⟩, rfl⟩
    have h₁ : PImm (ℍ := ℍ) y δ ls₀ (Val.loc m') (immU m' c) := pImm_of hy hin
    rw [← hP] at h₁
    obtain ⟨c', hc', ℓ₁, hs₁⟩ := h₁
    obtain ⟨⟨hℓ₁, hcoh⟩, -⟩ := pure_sep_iff.mp hs₁
    cases hℓ₁
    exact not_cohE_unit hm (by simpa [ls, rsOf, tClose] using hcoh)

/-- `coreMutImm_not_extF` at `δ = ['x ↦ 2, 'y ↦ 1]` (`2 ⊏ 1` in `Life = ℕᵒᵈ`), records at `1`, and
the locations `0`, `1`, `2`: every hypothesis discharged. -/
theorem coreMutImm_not_extF_inst :
    let δ : LSub := (LSub.empty.extend 0 2).extend 1 1
    let ls : List SRec := [(recU 1, (1 : Life))]
    let ls' : List SRec := [(recU 1, (1 : Life)), (recU 2, (1 : Life))]
    ∃ ρ : WRes, vCE (ℍ := ℍ) none true (.mut (.var 0) (.imm (.var 1) .unit)) ls δ (Val.loc 0) ρ ∧
      extF ls ls' ρ ∧ ¬ Ext ls ls' ρ ∧
      ¬ vCE (ℍ := ℍ) none true (.mut (.var 0) (.imm (.var 1) .unit)) ls' δ (Val.loc 0) ρ :=
  coreMutImm_not_extF 0 1 _ (b := (2 : ℕ)) (c := (1 : ℕ)) (t := (1 : ℕ))
    rfl rfl (by decide) (by decide) 0 1 2 (by decide)

end BoCa.Fig16.LogRel.Core.Chain.SI.ImmShape791N

end

