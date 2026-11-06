import Core.Chain.SI.MutWorld
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Ancestors
import Support.Model.UpdateFrame

/-!
# `↭` at a step index, tested on `[TR]` 6.48

## Where `UpdMutSI` (`SI/MutWorld.lean`) does not carry `[TR]` 6.48's proof

`[TR]` 6.48's proof, at the aliasable walk, `mut ○ mut` bullet: *"two `mut` cells
`mut(α, v, ρᵢ, P̂)`, `mut(β, v, ρᵢ, Q̂)`, where the update gives `ag(ρ₃)(ℓ) = mut(β, _, _, Q̂)` …
so both composites are `mut(α ⊓ β, v, ρᵢ, P̂ ∧ Q̂)`"*. At a step index the update gives
`ag(ρ₃)(ℓ) = mut(β, _, _, Q̂′)` with `Q̂′` the stepped member, so the composites are `P̂ ∧ Q̂` and
`P̂ ∧ Q̂′`. `UpdMutSI` speaks only of cells whose predicate *is* a member `F k` of the location's
family; the composite `P̂ ∧ F k` can be a member while `P̂ ∧ F k′` is no member at all
(`MutMutMemberStep`, refuted by `not_mutMutMemberStep`). So `UpdMutSI`'s conclusion fails at the
`○`-composite the printed step builds. The clause has a second defect: it bounds the new member
only from above (`k′ ≤ k`), so a lender reading the cell back at its own index `n` learns nothing
unless `n ≤ k′`, which the clause does not record.

## The forced change, named

`↭`'s `mut ⇔ mut` clause (`ResU.UpdMut`, row 5.27) fixes `β` and `P̂`. At a step index it becomes
`UpdMutN Φ n`: `β` fixed, and the predicate related by `PredStep Φ n ℓ`:

* at a location `Φ` does not cover, `P̂′ = P̂` (the printed clause; `updMutN_none_iff`);
* at a location `Φ ℓ = (b, F)`, every `(v, r)` in `P̂′` is in `P̂` or in `F n`.

`PredStep` is reflexive, transitive down the index (`predStep_trans`), and a congruence for `○`'s
`∧` (`compR_stepN`), which is what the printed `mut ○ mut` step needs. A write at `m ≥ n` of a
member meets it (`mutStep_write`). A lender who left `F k`, `k ≥ n`, reads back `F n`
(`predStep_read`). The clause is directional, so both directions of the printed `⇔` are kept as
two implications (`UpdMutN`'s two conjuncts).

`[TR]` 6.48 at `UpdVN Φ n`: `updVN_frame`, by the printed proof: the three cases at `ℓ`, the
aliasable case through the immutable ancestor (`agMutCarry`, the printed sentence *"by the
definition of `ag`, there must exist `ℓ′, ρ′` …"* with the predicate from the update), and the
`mut ○ mut` composite by `compR_stepN`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### `UpdMutSI` against the printed `mut ○ mut` step -/

/-- The printed `mut ○ mut` step read at `UpdMutSI`: when `P̂ ∧ F k` is a member of the family,
`P̂ ∧ F k′` (`k′ ≤ k`, the stepped member) is a member no higher. Stated extensionally; a cell
equation implies it. -/
def MutMutMemberStep : Prop :=
  ∀ (b : Life) (F : Nat → Val → SPropS Loc Val b), DownFam b F →
    ∀ (H : Val → SPropS Loc Val b) (k k' j : Nat), k' ≤ k →
      (∀ v r, SPropS.conj H (F k) v r ↔ SPropS.embed (F j) v r) →
      ∃ j', j' ≤ j ∧ ∀ v r, SPropS.conj H (F k') v r ↔ SPropS.embed (F j') v r

/-- The family `F k u ≜ u ∉ {loc 0, …, loc (k−1)}`. -/
private def avoidF (b : Life) : Nat → Val → SPropS Loc Val b :=
  fun k u _ => ∀ i, i < k → u ≠ Val.loc i

private theorem loc_ne {i j : Nat} (h : i ≠ j) : Val.loc i ≠ Val.loc j := by
  intro e
  apply h
  have := congrArg Subtype.val e
  simpa [Val.loc] using this

/-- **`UpdMutSI` does not carry the printed `mut ○ mut` step.** `P̂ ≜ F 7 ∪ {loc 4}`:
`P̂ ∧ F 7 = F 7`, and `P̂ ∧ F 3 = F 7 ∪ {loc 4}` is no member: a member holding `loc 4` is `F j′`
with `j′ ≤ 4`, which holds `loc 5`. -/
theorem not_mutMutMemberStep : ¬ MutMutMemberStep := by
  intro H
  have hdown : DownFam 0 (avoidF 0) := fun k u r h i hi => h i (by omega)
  let P : Val → SPropS Loc Val 0 := fun u r => avoidF 0 7 u r ∨ u = Val.loc 4
  have hb : (0 : Life) ⊓ 0 = 0 := Life.meet_self 0
  obtain ⟨j', hj', hiff⟩ := H 0 (avoidF 0) hdown P 7 3 7 (by omega) (by
    intro v r
    simp only [SPropS.conj, SPropS.embed]
    constructor
    · rintro ⟨-, ⟨h, hf⟩⟩; exact ⟨h, hf⟩
    · rintro ⟨h, hf⟩; exact ⟨⟨h, .inl hf⟩, ⟨h, hf⟩⟩)
  let r₀ : ResS Loc Val ((0 : Life) ⊓ 0) :=
    ⟨PMap.empty, fun _ _ h => by simp [PMap.empty] at h⟩
  have h0 : r₀.val.InStratum (0 : Life) := fun _ _ h => by simp [r₀, PMap.empty] at h
  -- `loc 4` is in `P̂ ∧ F 3`, so `j′ ≤ 4`
  have h4 : SPropS.conj P (avoidF 0 3) (Val.loc 4) r₀ :=
    ⟨⟨h0, .inr rfl⟩, ⟨h0, fun i hi => loc_ne (by omega)⟩⟩
  obtain ⟨_, hj4⟩ := (hiff _ _).mp h4
  have hj'4 : j' ≤ 4 := by
    by_contra hc
    exact hj4 4 (by omega) rfl
  -- `loc 5` is in `F j′`, and not in `P̂`
  have h5 : SPropS.embed (avoidF 0 j') (Val.loc 5) r₀ := ⟨h0, fun i hi => loc_ne (by omega)⟩
  obtain ⟨⟨_, hP5⟩, _⟩ := (hiff _ _).mpr h5
  rcases hP5 with hP5 | hP5
  · exact hP5 5 (by omega) rfl
  · exact loc_ne (by omega : (5 : Nat) ≠ 4) hP5

/-! ### The index-relative clause -/

/-- Ahmed's location typing at BoLo's strata: a location's stratum and payload family (`fam`,
read by `↭` at `mut` cells), and the `imm` records the world holds, each with the lifetime it was
lent at (`imm`, read only by the relation's entry tie `ImmTieL`). A location typing is applied
as its `fam`. -/
structure LocFam where
  fam : Loc → Option (Σ b : Life, Nat → Val → SPropS Loc Val b)
  imm : List SRec := []

instance : CoeFun LocFam (fun _ => Loc → Option (Σ b : Life, Nat → Val → SPropS Loc Val b)) :=
  ⟨LocFam.fam⟩

/-- The location typing with no entries. -/
def LocFam.empty : LocFam := ⟨fun _ => Option.none, []⟩

@[simp] theorem LocFam.empty_apply (l : Loc) : LocFam.empty l = Option.none := rfl

@[simp] theorem LocFam.empty_imm : LocFam.empty.imm = [] := rfl

@[simp] theorem LocFam.mk_apply (f : Loc → Option (Σ b : Life, Nat → Val → SPropS Loc Val b))
    (I : List SRec) (l : Loc) : (LocFam.mk f I) l = f l := rfl

theorem LocFam.ext' {Φ Φ' : LocFam} (h : ∀ l, Φ l = Φ' l) (hI : Φ.imm = Φ'.imm) : Φ = Φ' := by
  cases Φ; cases Φ'
  simp only at hI
  subst hI
  congr
  funext l
  exact h l

/-- **The relation's entry tie**: every `imm` record of the location typing, with the lifetime it
was lent at, is a record of the run's list. `ImmTie`'s list form: it reads no resource, so a run
keeps it (its lists keep their members) and a run at a list extending the caller's keeps it. The
lifetime is what puts a record's tag (`Tagged`) at the world's lifetime for it. -/
def ImmTieL (I : List SRec) (ls : List SRec) : Prop := ∀ x ∈ I, x ∈ ls

theorem ImmTieL.nil (ls : List SRec) : ImmTieL [] ls := fun _ h => absurd h (by simp)

theorem ImmTieL.of_nil {I : List SRec} (h : I = []) (ls : List SRec) : ImmTieL I ls := by
  subst h; exact ImmTieL.nil ls

theorem ImmTieL.perm {I ls ls' : List SRec} (h : ImmTieL I ls) (hls : ∀ x, x ∈ ls' ↔ x ∈ ls) :
    ImmTieL I ls' := fun x hx => (hls x).mpr (h x hx)

theorem ImmTieL.mono {I I' ls : List SRec} (h : ImmTieL I' ls) (hI : ∀ x ∈ I, x ∈ I') :
    ImmTieL I ls := fun x hx => h x (hI x hx)

theorem ImmTieL.of_sub {I ls ls' : List SRec} (h : ImmTieL I ls)
    (hs : ∀ x ∈ ls, x ∈ ls') : ImmTieL I ls' := fun x hx => hs _ (h x hx)

theorem ImmTieL.cons {I ls : List SRec} (h : ImmTieL I ls) (y : SRec) : ImmTieL I (y :: ls) :=
  fun x hx => List.mem_cons_of_mem _ (h x hx)

/-- The tie's records are records of the list. -/
theorem ImmTieL.rsOf {I ls : List SRec} (h : ImmTieL I ls) {x : SRec} (hx : x ∈ I) :
    x.1 ∈ rsOf ls :=
  List.mem_map_of_mem (h x hx)

/-- Every family `Φ` assigns is downward closed. -/
def LocFam.Down (Φ : LocFam) : Prop :=
  ∀ l b F, Φ l = some ⟨b, F⟩ → DownFam b F

/-- The stored predicate of a `mut` cell, on `Res` (`MutU.pred`); empty at other cells. -/
def cellPred : CellU Loc Val → Val → WRes → Prop
  | .mut m => m.pred
  | _ => fun _ _ => False

/-- A downward-closed family is antitone in the index. -/
theorem DownFam.le {b : Life} {F : Nat → Val → SPropS Loc Val b} (hd : DownFam b F)
    {m k : Nat} (h : m ≤ k) : ∀ v r, F k v r → F m v r := by
  induction h with
  | refl => exact fun _ _ x => x
  | step _ ih => exact fun v r x => ih v r (hd _ _ _ x)

/-- **The index-relative relation between a `mut` cell's predicates across `↭`.** At a location
`Φ` does not cover, the printed equality. At `Φ ℓ = (b, F)`, the new predicate holds only where
the old one does or where `F n` does. -/
def PredStep (Φ : LocFam) (n : Nat) (l : Loc) (p p' : Val → WRes → Prop) : Prop :=
  (Φ l = none → p = p') ∧
  ∀ b F, Φ l = some ⟨b, F⟩ → ∀ v r, p' v r → p v r ∨ SPropS.toU (F n v) r

/-- Two `mut` cells at one `β`, their predicates related by `PredStep`; value and witness free,
as in the printed clause. -/
def MutStep (Φ : LocFam) (n : Nat) (l : Loc) (ψ ψ' : CellU Loc Val) : Prop :=
  ψ.kind = Kind.mut ∧ ψ'.kind = Kind.mut ∧ ψ.at = ψ'.at ∧ PredStep Φ n l (cellPred ψ) (cellPred ψ')

/-- **`↭`'s `mut` clause at the step index `n`.** Both directions of the printed `⇔`. -/
def UpdMutN (Φ : LocFam) (n : Nat) (ρ₁ ρ₂ : WRes) : Prop :=
  (∀ l ψ, ρ₁.FlatAt l ψ → ψ.kind = Kind.mut → ∃ ψ', ρ₂.FlatAt l ψ' ∧ MutStep Φ n l ψ ψ') ∧
  (∀ l ψ', ρ₂.FlatAt l ψ' → ψ'.kind = Kind.mut → ∃ ψ, ρ₁.FlatAt l ψ ∧ MutStep Φ n l ψ ψ')

/-- `↭` at the step index `n`: the printed `imm` clause and `UpdMutN`. -/
def UpdN (Φ : LocFam) (n : Nat) (ρ₁ ρ₂ : WRes) : Prop := ResU.UpdImm ρ₁ ρ₂ ∧ UpdMutN Φ n ρ₁ ρ₂

/-- `UpdN`, guarded by `✓ρ₁ ∧ ✓ρ₂` as `[TR]` p. 5 prints `↭`. -/
def UpdVN (Φ : LocFam) (n : Nat) (ρ₁ ρ₂ : WRes) : Prop := UpdN Φ n ρ₁ ρ₂ ∧ ρ₁.Valid ∧ ρ₂.Valid

/-! ### `PredStep` and `MutStep` -/

theorem PredStep.refl (Φ : LocFam) (n : Nat) (l : Loc) (p : Val → WRes → Prop) :
    PredStep Φ n l p p :=
  ⟨fun _ => rfl, fun _ _ _ _ _ h => .inl h⟩

/-- Transitive down the index. -/
theorem predStep_trans {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {l : Loc}
    {p p' p'' : Val → WRes → Prop} (h₁ : PredStep Φ n l p p') (h₂ : PredStep Φ n' l p' p'') :
    PredStep Φ n' l p p'' := by
  refine ⟨fun h => (h₁.1 h).trans (h₂.1 h), fun b F hF v r h => ?_⟩
  rcases h₂.2 b F hF v r h with h' | h'
  · rcases h₁.2 b F hF v r h' with h'' | ⟨hs, h''⟩
    · exact .inl h''
    · exact .inr ⟨hs, (hΦ l b F hF).le hn v _ h''⟩
  · exact .inr h'

/-- **The lender's read-back**: a cell that held `F k`, `k ≥ n`, holds after a step at `n` only
what `F n` allows. -/
theorem predStep_read {Φ : LocFam} (hΦ : Φ.Down) {n : Nat} {l : Loc} {b : Life}
    {F : Nat → Val → SPropS Loc Val b} (hF : Φ l = some ⟨b, F⟩) {k : Nat} (hk : n ≤ k)
    {p p' : Val → WRes → Prop} (hp : ∀ v r, p v r → SPropS.toU (F k v) r)
    (h : PredStep Φ n l p p') : ∀ v r, p' v r → SPropS.toU (F n v) r := by
  intro v r h'
  rcases h.2 b F hF v r h' with h'' | h''
  · obtain ⟨hs, hk'⟩ := hp v r h''
    exact ⟨hs, (hΦ l b F hF).le hk v _ hk'⟩
  · exact h''

theorem MutStep.refl {Φ : LocFam} {n : Nat} {l : Loc} {ψ : CellU Loc Val}
    (hk : ψ.kind = Kind.mut) : MutStep Φ n l ψ ψ :=
  ⟨hk, hk, rfl, PredStep.refl _ _ _ _⟩

theorem MutStep.trans {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {l : Loc}
    {ψ ψ' ψ'' : CellU Loc Val} (h₁ : MutStep Φ n l ψ ψ') (h₂ : MutStep Φ n' l ψ' ψ'') :
    MutStep Φ n' l ψ ψ'' :=
  ⟨h₁.1, h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, predStep_trans hΦ hn h₁.2.2.2 h₂.2.2.2⟩

/-- The stored predicate of `mutOf b v χ h P hw`, on `Res`. -/
theorem mpred_mutOf {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, h⟩} (u : Val) (r : WRes) :
    cellPred (CellU.mutOf b v χ h P hw) u r ↔ SPropS.toU (P u) r := by
  show (∃ h' : r.InStratum b, P u (ResU.toStratum r h').toS) ↔ _
  constructor
  · rintro ⟨h', hp⟩
    refine ⟨h', ?_⟩
    rwa [show (ResU.toStratum r h').toS = ⟨r, h'⟩ from ResS.toS_toStratum ⟨r, h'⟩ h'] at hp
  · rintro ⟨h', hp⟩
    refine ⟨h', ?_⟩
    rwa [show (ResU.toStratum r h').toS = ⟨r, h'⟩ from ResS.toS_toStratum ⟨r, h'⟩ h']

/-- **A write of a lower member meets the clause**: a `Φ`-cell holding `F k` replaced by one
holding `F m`, `n ≤ m`. -/
theorem mutStep_write {Φ : LocFam} (hΦ : Φ.Down) {n : Nat} {l : Loc} {b : Life}
    {F : Nat → Val → SPropS Loc Val b} (hF : Φ l = some ⟨b, F⟩) {k m : Nat} (hm : n ≤ m)
    {v u : Val} {χ σ : WRes} {h : χ.InStratum b} {hσ : σ.InStratum b}
    {hw : F k v ⟨χ, h⟩} {hu : F m u ⟨σ, hσ⟩} :
    MutStep Φ n l (CellU.mutOf b v χ h (F k) hw) (CellU.mutOf b u σ hσ (F m) hu) := by
  refine ⟨rfl, rfl, rfl, fun hn => absurd (hF.symm.trans hn) (by simp),
    fun b' F' hF' v' r h' => ?_⟩
  rw [hF] at hF'
  cases hF'
  obtain ⟨hs, hp⟩ := (mpred_mutOf v' r).mp h'
  exact .inr ⟨hs, (hΦ l b F hF).le hm v' _ hp⟩

/-! ### Reflexivity, transitivity, and the printed clause where `Φ` is empty -/

theorem UpdMutN.refl (Φ : LocFam) (n : Nat) (ρ : WRes) : UpdMutN Φ n ρ ρ :=
  ⟨fun _ ψ h hk => ⟨ψ, h, MutStep.refl hk⟩, fun _ ψ h hk => ⟨ψ, h, MutStep.refl hk⟩⟩

theorem UpdN.refl (Φ : LocFam) (n : Nat) (ρ : WRes) : UpdN Φ n ρ ρ :=
  ⟨fun _ _ _ _ _ => Iff.rfl, UpdMutN.refl Φ n ρ⟩

theorem UpdVN.refl (Φ : LocFam) (n : Nat) {ρ : WRes} (h : ρ.Valid) : UpdVN Φ n ρ ρ :=
  ⟨UpdN.refl Φ n ρ, h, h⟩

/-- `[TR]` 6.49 at the step index, down the index. -/
theorem UpdN.trans {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {ρ₁ ρ₂ ρ₃ : WRes}
    (h₁ : UpdN Φ n ρ₁ ρ₂) (h₂ : UpdN Φ n' ρ₂ ρ₃) : UpdN Φ n' ρ₁ ρ₃ := by
  refine ⟨fun l s v χ hs => (h₁.1 l s v χ hs).trans (h₂.1 l s v χ hs), ?_, ?_⟩
  · intro l ψ h hk
    obtain ⟨ψ', h', hs₁⟩ := h₁.2.1 l ψ h hk
    obtain ⟨ψ'', h'', hs₂⟩ := h₂.2.1 l ψ' h' hs₁.2.1
    exact ⟨ψ'', h'', hs₁.trans hΦ hn hs₂⟩
  · intro l ψ'' h hk
    obtain ⟨ψ', h', hs₂⟩ := h₂.2.2 l ψ'' h hk
    obtain ⟨ψ, h₀, hs₁⟩ := h₁.2.2 l ψ' h' hs₂.1
    exact ⟨ψ, h₀, hs₁.trans hΦ hn hs₂⟩

theorem UpdVN.trans {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {ρ₁ ρ₂ ρ₃ : WRes}
    (h₁ : UpdVN Φ n ρ₁ ρ₂) (h₂ : UpdVN Φ n' ρ₂ ρ₃) : UpdVN Φ n' ρ₁ ρ₃ :=
  ⟨h₁.1.trans hΦ hn h₂.1, h₁.2.1, h₂.2.2⟩

/-- Two `mut` cells at one `β` with one stored predicate present the same `(β, P̂)`. -/
private theorem isMutSig_of_mpred {ψ ψ' : CellU Loc Val} (hk' : ψ'.kind = Kind.mut)
    (hat : ψ.at = ψ'.at) (hp : cellPred ψ = cellPred ψ') {b : Life}
    {P : Val → SPropS Loc Val b} (h : IsMutSig ψ b P) : IsMutSig ψ' b P := by
  obtain ⟨v, χ, hh, hw, rfl⟩ := h
  rcases CellU.rep ψ' with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
  · simp at hk'
  · simp at hk'
  · have hc : b = c := hat
    subst hc
    have hPQ : P = Q := by
      funext w r
      have e := congrFun (congrFun hp w) r.val
      apply propext
      constructor
      · intro x
        have hx : cellPred (CellU.mutOf b v χ hh P hw) w r.val := (mpred_mutOf w r.val).mpr
          ⟨r.property, x⟩
        rw [e] at hx
        obtain ⟨_, y⟩ := (mpred_mutOf w r.val).mp hx
        exact y
      · intro x
        have hx : cellPred (CellU.mutOf b u τ m Q k) w r.val := (mpred_mutOf w r.val).mpr
          ⟨r.property, x⟩
        rw [← e] at hx
        obtain ⟨_, y⟩ := (mpred_mutOf w r.val).mp hx
        exact y
    subst hPQ
    exact ⟨u, τ, m, k, rfl⟩

/-- **Conservativity**: where `Φ` covers no location, `UpdMutN` is the printed clause. -/
theorem updMutN_none_iff {Φ : LocFam} (hΦ : ∀ l, Φ l = none) (n : Nat) (ρ₁ ρ₂ : WRes) :
    UpdMutN Φ n ρ₁ ρ₂ ↔ ResU.UpdMut ρ₁ ρ₂ := by
  constructor
  · rintro ⟨hf, hb⟩ l b P
    constructor
    · rintro ⟨v, χ, hh, hw, hg⟩
      obtain ⟨ψ', h', hk, hk', hat, hp⟩ := hf l _ hg rfl
      obtain ⟨v', χ', hh', hw', rfl⟩ :=
        isMutSig_of_mpred hk' hat (hp.1 (hΦ l)) ⟨v, χ, hh, hw, rfl⟩
      exact ⟨v', χ', hh', hw', h'⟩
    · rintro ⟨v, χ, hh, hw, hg⟩
      obtain ⟨ψ, h', hk, hk', hat, hp⟩ := hb l _ hg rfl
      obtain ⟨v', χ', hh', hw', rfl⟩ :=
        isMutSig_of_mpred hk hat.symm (hp.1 (hΦ l)).symm ⟨v, χ, hh, hw, rfl⟩
      exact ⟨v', χ', hh', hw', h'⟩
  · intro h
    refine ⟨fun l ψ hg hk => ?_, fun l ψ hg hk => ?_⟩
    · rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
      · simp at hk
      · simp at hk
      · obtain ⟨v', χ', hh', hw', h'⟩ := (h l c Q).mp ⟨u, τ, m, k, hg⟩
        refine ⟨_, h', rfl, rfl, rfl, fun _ => ?_, fun b F hF => by rw [hΦ l] at hF; cases hF⟩
        funext w r
        exact propext ((mpred_mutOf w r).trans (mpred_mutOf w r).symm)
    · rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
      · simp at hk
      · simp at hk
      · obtain ⟨v', χ', hh', hw', h'⟩ := (h l c Q).mpr ⟨u, τ, m, k, hg⟩
        refine ⟨_, h', rfl, rfl, rfl, fun _ => ?_, fun b F hF => by rw [hΦ l] at hF; cases hF⟩
        funext w r
        exact propext ((mpred_mutOf w r).trans (mpred_mutOf w r).symm)


/-! ### `↭` at one location of two flattenings -/

/-- `UpdN`'s two clauses at one location of the two flattenings (`CellUpd` at the index). -/
def CellUpdN (Φ : LocFam) (n : Nat) (l : Loc) (o o' : Option (CellU Loc Val)) : Prop :=
  (∀ (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
      o = some (CellU.immOf s v χ h) ↔ o' = some (CellU.immOf s v χ h)) ∧
  (∀ ψ, o = some ψ → ψ.kind = Kind.mut → ∃ ψ', o' = some ψ' ∧ MutStep Φ n l ψ ψ') ∧
  (∀ ψ', o' = some ψ' → ψ'.kind = Kind.mut → ∃ ψ, o = some ψ ∧ MutStep Φ n l ψ ψ')

theorem CellUpdN.refl (Φ : LocFam) (n : Nat) (l : Loc) (o : Option (CellU Loc Val)) :
    CellUpdN Φ n l o o :=
  ⟨fun _ _ _ _ => Iff.rfl, fun ψ h hk => ⟨ψ, h, MutStep.refl hk⟩,
    fun ψ h hk => ⟨ψ, h, MutStep.refl hk⟩⟩

theorem cellUpdN_of_updN {Φ : LocFam} {n : Nat} {ρ₁ ρ₂ σ₁ σ₂ : WRes} (h : UpdN Φ n ρ₁ ρ₂)
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂) (l : Loc) :
    CellUpdN Φ n l (σ₁.get l) (σ₂.get l) := by
  refine ⟨fun s v χ hh => ?_, fun ψ hψ hk => ?_, fun ψ' hψ hk => ?_⟩
  · rw [← ResU.flatAt_iff h₁, ← ResU.flatAt_iff h₂]
    exact h.1 l s v χ hh
  · obtain ⟨ψ', h', hs⟩ := h.2.1 l ψ ((ResU.flatAt_iff h₁ _ _).mpr hψ) hk
    exact ⟨ψ', (ResU.flatAt_iff h₂ _ _).mp h', hs⟩
  · obtain ⟨ψ, h', hs⟩ := h.2.2 l ψ' ((ResU.flatAt_iff h₂ _ _).mpr hψ) hk
    exact ⟨ψ, (ResU.flatAt_iff h₁ _ _).mp h', hs⟩

/-- `UpdN` read off a pair of flattenings (`ResU.upd_of_flat` at the index). -/
theorem updN_of_flat {Φ : LocFam} {n : Nat} {ρ₁ ρ₂ σ₁ σ₂ : WRes} (h₁ : ResU.Flat ρ₁ σ₁)
    (h₂ : ResU.Flat ρ₂ σ₂) (hc : ∀ l, CellUpdN Φ n l (σ₁.get l) (σ₂.get l)) :
    UpdN Φ n ρ₁ ρ₂ := by
  refine ⟨fun l s v χ hh => ?_, fun l ψ hψ hk => ?_, fun l ψ' hψ hk => ?_⟩
  · rw [ResU.flatAt_iff h₁, ResU.flatAt_iff h₂]
    exact (hc l).1 s v χ hh
  · obtain ⟨ψ', h', hs⟩ := (hc l).2.1 ψ ((ResU.flatAt_iff h₁ _ _).mp hψ) hk
    exact ⟨ψ', (ResU.flatAt_iff h₂ _ _).mpr h', hs⟩
  · obtain ⟨ψ, h', hs⟩ := (hc l).2.2 ψ' ((ResU.flatAt_iff h₂ _ _).mp hψ) hk
    exact ⟨ψ, (ResU.flatAt_iff h₁ _ _).mpr h', hs⟩

/-! ### The immutable ancestor, through the `imm` clause alone

`ResU.upd_ag_imm_wit_factor` and `ResU.upd_ag_nonimm_transfer` read only `↭`'s `imm` clause;
here they take it alone, so they serve `UpdN`. -/

theorem updImm_symm {ρ₁ ρ₂ : WRes} (h : ResU.UpdImm ρ₁ ρ₂) : ResU.UpdImm ρ₂ ρ₁ :=
  fun l s v χ hs => (h l s v χ hs).symm

/-- `ResU.upd_ag_imm_wit_factor` at the `imm` clause. -/
theorem updImm_ag_imm_wit_factor {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : ResU.UpdImm ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {m : Loc} {s : LSet} {u : Val} {χ : WRes} {hh : χ.InStratum s.join}
    (hg : a₂.get m = some (CellU.immOf s u χ hh)) :
    ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a₃ := by
  have hex : e₂.get m = none := by
    cases f : e₂.get m with
    | none => rfl
    | some ξ =>
        exact absurd (CellU.CompatS.kinds (hc₂.1 m ξ _ f hg)).1 (ExS.immFree he₂ m ξ f)
  have hσ₂ : σ₂.get m = some (CellU.immOf s u χ hh) := by
    rcases ResU.Comp.get hc₂ m with ⟨-, f₂, -⟩ | ⟨ζ, -, f₂, -⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
    · rw [hg] at f₂; exact absurd f₂ (by simp)
    · rw [hg] at f₂; exact absurd f₂ (by simp)
    · exact f.trans (congrArg some (Option.some.inj (f₂.symm.trans hg)))
    · rw [hex] at f₁; exact absurd f₁ (by simp)
  have hσ₃ : σ₃.get m = some (CellU.immOf s u χ hh) :=
    (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ m _).mp
      ((h m s u χ hh).mp ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ m _).mpr hσ₂))
  exact ResU.flat_imm_wit_factor he₃ ha₃ hc₃ hσ₃

/-- `ResU.upd_ag_nonimm_transfer` at the `imm` clause. -/
theorem updImm_ag_nonimm_transfer {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : ResU.UpdImm ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} {φ : CellU Loc Val} (hg : a₂.get n = some φ)
    (hk : φ.kind ≠ Kind.imm) :
    ∃ (χ ev av p z : WRes) (ξ : CellU Loc Val),
      ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a₃ ∧
      p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
      ξ.wit = φ.wit ∧ ξ.erase = φ.erase := by
  obtain ⟨m, s, u, χ, hh, ev, av, p, ξ, hm, hev, hav, hp, hpn, hξk, hξw, hξe⟩ :=
    AgW.nonimm_beneath_imm ha₂ n φ hg hk
  obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ :=
    updImm_ag_imm_wit_factor h he₂ ha₂ hc₂ he₃ ha₃ hc₃ hm
  rw [ExR.functional hev' hev, AgW.functional hav' hav] at hp'
  rw [ResU.CompR.functional hp' hp] at hz
  exact ⟨χ, ev, av, p, z, ξ, hev, hav, hp, hz, hpn, hξk, hξw, hξe⟩

/-- An `own` cell has the empty witness. -/
private theorem wit_own (ψ : CellU Loc Val) (hk : ψ.kind = Kind.own) :
    ψ.wit = (PMap.empty : WRes) := by
  rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
  · simp
  · simp at hk
  · simp at hk

/-- What a `○`-factorisation carries over: the value always, the witness whenever the factor's
own cell is not `own`. -/
private theorem factor_carry {n : Loc} (p z a : WRes) (ξ ζ : CellU Loc Val)
    (hC : ResU.CompR p z a) (hp : p.get n = some ξ) (ha : a.get n = some ζ)
    (hζo : ζ.kind ≠ Kind.own) :
    ζ.erase = ξ.erase ∧ (ξ.kind ≠ Kind.own → ζ.wit = ξ.wit) := by
  rcases ResU.Comp.get hC n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, f, hcc⟩
  · rw [hp] at f₁
    exact absurd f₁ (by simp)
  · have e₁ : ξ = ψ := Option.some.inj (hp.symm.trans f₁)
    have e₂ : ζ = ψ := Option.some.inj (ha.symm.trans f)
    rw [e₁, e₂]
    exact ⟨rfl, fun _ => rfl⟩
  · rw [hp] at f₁
    exact absurd f₁ (by simp)
  · have e₁ : ξ = ψ₁ := Option.some.inj (hp.symm.trans f₁)
    have e₂ : ζ = ψ := Option.some.inj (ha.symm.trans f)
    subst e₁
    subst e₂
    refine ⟨(CellU.CompR.erase hcc).2, fun hξo => ?_⟩
    rcases CellU.CompR.wit_of_ne_own hcc hζo with ⟨-, e⟩ | ⟨k₂, e⟩
    · exact e
    · exact e.trans (CellU.CompR.wit hcc hξo k₂).symm

/-- **The ancestor step at the index** (`[TR]` 6.48's proof, *"by the definition of `ag`, there
must exist `ℓ′, ρ′` …, which implies `ag(ρ₃)(ℓ) = mut(β, v, ρᵢ, Q̂)`"*): a `mut` cell `φ` of
`ag(ρ₂)` whose flattening at `ρ₃` is a `mut` cell `ψ′` (the update's), is `ag(ρ₃)`'s cell there,
at `φ`'s value and witness. The predicate is the one the update gives. -/
theorem agMutCarry {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : ResU.UpdImm ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {x : Loc} {φ ψ' : CellU Loc Val} (hg : a₂.get x = some φ) (hk : φ.kind = Kind.mut)
    (hσ₃ : σ₃.get x = some ψ') (hk' : ψ'.kind = Kind.mut) :
    a₃.get x = some ψ' ∧ ψ'.erase = φ.erase ∧ ψ'.wit = φ.wit := by
  have hφk : φ.kind ≠ Kind.imm := by rw [hk]; simp
  have hφo : φ.kind ≠ Kind.own := by rw [hk]; simp
  have hψk : ψ'.kind ≠ Kind.imm := by rw [hk']; simp
  have hψo : ψ'.kind ≠ Kind.own := by rw [hk']; simp
  -- the ancestor step, left to right
  obtain ⟨κ, ev, av, p, z, ξ, -, -, -, hz, hpn, hξk, hξw, hξe⟩ :=
    updImm_ag_nonimm_transfer h he₂ ha₂ hc₂ he₃ ha₃ hc₃ hg hφk
  have hocc : ∃ ζ, a₃.get x = some ζ := by
    rcases ResU.Comp.get hz x with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
    · rw [hpn] at f₁
      exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
    · rw [hpn] at f₁
      exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
  obtain ⟨ζ, hζ⟩ := hocc
  -- `ag(ρ₃)(x)` is `⦇ρ₃⦈(x)`: `ex(ρ₃)_●` is `imm`-free and `ag(ρ₃)` is occupied
  have he₃n : e₃.get x = none := by
    cases f : e₃.get x with
    | none => rfl
    | some ξ' =>
        have hk₀ := (CellU.CompatS.kinds (hc₃.1 x ξ' ζ f hζ)).1
        exact absurd hk₀ (ExS.immFree he₃ x ξ' f)
  have ha₃n : a₃.get x = σ₃.get x := by
    rcases ResU.Comp.get hc₃ x with ⟨-, f₂, -⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
        ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
    · rw [hζ] at f₂
      exact absurd f₂ (by simp)
    · rw [he₃n] at f₁
      exact absurd f₁ (by simp)
    · rw [f₂, f]
    · rw [he₃n] at f₁
      exact absurd f₁ (by simp)
  have hgt : a₃.get x = some ψ' := ha₃n.trans hσ₃
  obtain ⟨heL, hwL⟩ := factor_carry p z a₃ ξ ψ' hz hpn hgt hψo
  refine ⟨hgt, heL.trans hξe, ?_⟩
  -- the witness, from whichever side's trace has a cell that is not `own`
  by_cases hξo : ξ.kind = Kind.own
  · have hχe : φ.wit = (PMap.empty : WRes) := hξw.symm.trans (wit_own ξ hξo)
    obtain ⟨κ', ev', av', p', z', ξ', -, -, -, hz', hpn', hξk', hξw', hξe'⟩ :=
      updImm_ag_nonimm_transfer (updImm_symm h) he₃ ha₃ hc₃ he₂ ha₂ hc₂ hgt hψk
    obtain ⟨-, hwR⟩ := factor_carry p' z' a₂ ξ' φ hz' hpn' hg hφo
    by_cases hξo' : ξ'.kind = Kind.own
    · rw [hχe, ← hξw', wit_own ξ' hξo']
    · exact ((hwR hξo').trans hξw').symm
  · exact (hwL hξo).trans hξw

/-- An `imm` cell of `ag(ρ₂)` is `ag(ρ₃)`'s cell: the `imm` clause pins it (the `imm` branch of
`ResU.upd_ag_eq_of_ne_own`). -/
theorem updImm_ag_imm_eq {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : ResU.UpdImm ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} {ψ : CellU Loc Val} (hg : a₂.get n = some ψ) (hk : ψ.kind = Kind.imm) :
    a₃.get n = some ψ := by
  obtain ⟨s, hs, hψ⟩ := CellU.imm_eta hk
  rw [hψ] at hg ⊢
  have hex : e₂.get n = none := by
    cases f : e₂.get n with
    | none => rfl
    | some ξ =>
        exact absurd (CellU.CompatS.kinds (hc₂.1 n ξ _ f hg)).1 (ExS.immFree he₂ n ξ f)
  have hσ₂ : σ₂.get n = some (CellU.immOf s ψ.erase ψ.wit hs) := by
    rcases ResU.Comp.get hc₂ n with ⟨-, f₂, -⟩ | ⟨ζ, f₁, -, -⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
    · rw [hg] at f₂; exact absurd f₂ (by simp)
    · rw [hex] at f₁; exact absurd f₁ (by simp)
    · exact f.trans (congrArg some (Option.some.inj (f₂.symm.trans hg)))
    · rw [hex] at f₁; exact absurd f₁ (by simp)
  have hσ₃ : σ₃.get n = some (CellU.immOf s ψ.erase ψ.wit hs) :=
    (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ n _).mp
      ((h n s _ _ hs).mp ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ n _).mpr hσ₂))
  exact ResU.ag_eq_flat_at_imm he₃ hc₃ hσ₃ (CellU.kind_immOf _ _ _ _)

/-- `ag(ρ₂)` and `ag(ρ₃)` at a cell that is not `own`: the same `imm` cell, or `mut` cells over one
value and witness whose predicates the update relates (`ResU.upd_ag_eq_of_ne_own` at the index). -/
theorem updN_ag_ne_own {Φ : LocFam} {k : Nat} {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdN Φ k ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} {ψ : CellU Loc Val} (hg : a₂.get n = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ', a₃.get n = some ψ' ∧
      (ψ' = ψ ∨ (MutStep Φ k n ψ ψ' ∧ ψ'.erase = ψ.erase ∧ ψ'.wit = ψ.wit)) := by
  by_cases hi : ψ.kind = Kind.imm
  · exact ⟨ψ, updImm_ag_imm_eq h.1 he₂ ha₂ hc₂ he₃ ha₃ hc₃ hg hi, .inl rfl⟩
  · have hm : ψ.kind = Kind.mut := by
      revert hk hi; cases ψ.kind <;> simp
    have hσ₂ : σ₂.get n = some ψ := ResU.flat_eq_ag_at he₂ hc₂ hg hi
    obtain ⟨ψ', h', hs⟩ := h.2.1 n ψ ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ _ _).mpr hσ₂) hm
    have hσ₃ : σ₃.get n = some ψ' := (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ _ _).mp h'
    obtain ⟨ha, he, hw⟩ := agMutCarry h.1 he₂ ha₂ hc₂ he₃ ha₃ hc₃ hg hm hσ₃ hs.2.1
    exact ⟨ψ', ha, .inr ⟨hs, he, hw⟩⟩

/-- At an `own` cell of `ag(ρ₂)`, `ag(ρ₃)` carries an `own` cell or nothing
(`ResU.upd_ag_own_or_none` at the index; the printed `⇔`'s right-to-left half). -/
theorem updN_ag_own_or_none {Φ : LocFam} {k : Nat} {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdN Φ k ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} (hg : ∀ ψ, a₂.get n = some ψ → ψ.kind = Kind.own) :
    ∀ φ, a₃.get n = some φ → φ.kind = Kind.own := by
  intro φ hφ
  by_contra hko
  by_cases hi : φ.kind = Kind.imm
  · have := updImm_ag_imm_eq (updImm_symm h.1) he₃ ha₃ hc₃ he₂ ha₂ hc₂ hφ hi
    exact hko (by rw [← hg φ this])
  · have hm : φ.kind = Kind.mut := by
      revert hko hi; cases φ.kind <;> simp
    have hσ₃ : σ₃.get n = some φ := ResU.flat_eq_ag_at he₃ hc₃ hφ hi
    obtain ⟨ψ, h', hs⟩ := h.2.2 n φ ((ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ _ _).mpr hσ₃) hm
    have hσ₂ : σ₂.get n = some ψ := (ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ _ _).mp h'
    obtain ⟨ha, -, -⟩ :=
      agMutCarry (updImm_symm h.1) he₃ ha₃ hc₃ he₂ ha₂ hc₂ hφ hm hσ₂ hs.1
    have := hg ψ ha
    rw [hs.1] at this
    cases this

/-! ### `○` respects the step: the printed `mut ○ mut` composite -/

/-- The stored predicate of the `mut ○ mut` composite `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`. -/
theorem cellPred_conj {a b : Life} {v : Val} {χ : WRes} {ha : χ.InStratum a}
    {hb : χ.InStratum b} {P : Val → SPropS Loc Val a} {Q : Val → SPropS Loc Val b}
    {hP : P v ⟨χ, ha⟩} {hQ : Q v ⟨χ, hb⟩} (w : Val) (r : WRes) :
    cellPred (CellU.mutOf (a ⊓ b) v χ ha.inf_left (SPropS.conj P Q)
        (SPropS.conj_holds ha hb hP hQ)) w r ↔
      (r.InStratum (a ⊓ b) ∧ SPropS.toU (P w) r ∧ SPropS.toU (Q w) r) := by
  rw [mpred_mutOf]
  constructor
  · rintro ⟨h, hp, hq⟩; exact ⟨h, hp, hq⟩
  · rintro ⟨h, hp, hq⟩; exact ⟨h, hp, hq⟩

/-- `ω ○ (imm …) = ω`-style facts: an `imm` cell absorbs a `mut` one. -/
private theorem compR_imm_mut {A ψ c : CellU Loc Val} (hA : A.kind = Kind.imm)
    (hψ : ψ.kind = Kind.mut) (h : CellU.CompR A ψ c) : c = A := by
  rcases h.inv with ⟨e, rfl⟩ | ⟨k, rfl⟩ | ⟨a, b, v, ρ, ha, hb, P, Q, hP, hQ, e1, e2, rfl⟩ |
      ⟨rfl, k1, k2⟩ | ⟨rfl, k1, k2⟩ | ⟨rfl, k1, k2⟩ | ⟨rfl, k1, k2⟩
  · rfl
  · exact absurd (CellU.CompatS.kinds k).2 (by rw [hψ]; simp)
  · rw [e1] at hA; simp at hA
  · rfl
  · rw [hA] at k1; cases k1
  · rfl
  · rw [hA] at k1; cases k1

/-- **`○` with a fixed left factor respects the step.** `A ○ ψ` and `A ○ ψ′`, `ψ, ψ′` `mut` cells
over one value and witness whose predicates `PredStep` relates: the composites are related by
`↭`'s clauses at the index. At `A` a `mut` cell this is the printed `mut ○ mut` step with
`P̂ ∧ Q̂` and `P̂ ∧ Q̂′`. -/
theorem compR_stepN {Φ : LocFam} {k : Nat} {l : Loc} {A ψ ψ' c c' : CellU Loc Val}
    (hc : CellU.CompR A ψ c) (hc' : CellU.CompR A ψ' c') (hs : MutStep Φ k l ψ ψ')
    (he : ψ'.erase = ψ.erase) (hw : ψ'.wit = ψ.wit) : CellUpdN Φ k l (some c) (some c') := by
  -- `ψ` and `ψ'` as `mutOf`s over one value and witness
  rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨b, v, χ, hb, Q, hQ, rfl⟩
  · exact absurd hs.1 (by simp)
  · exact absurd hs.1 (by simp)
  rcases CellU.rep ψ' with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨b', v', χ', hb', Q', hQ', rfl⟩
  · exact absurd hs.2.1 (by simp)
  · exact absurd hs.2.1 (by simp)
  have hbb : b = b' := hs.2.2.1
  subst hbb
  simp only [CellU.erase_mutOf] at he
  simp only [CellU.wit_mutOf] at hw
  subst he
  subst hw
  -- `A`
  rcases CellU.rep A with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨a, u, τ, ha, P, hP, rfl⟩
  · -- `own`: the composites are the operands
    rw [CellU.compR_own_left hc, CellU.compR_own_left hc']
    refine ⟨fun s w χ₀ h₀ => ⟨fun e => ?_, fun e => ?_⟩, fun φ e hk => ?_, fun φ e hk => ?_⟩
    · exact absurd (Option.some.inj e).symm CellU.immOf_ne_mutOf
    · exact absurd (Option.some.inj e).symm CellU.immOf_ne_mutOf
    · cases e; exact ⟨_, rfl, hs⟩
    · cases e; exact ⟨_, rfl, hs⟩
  · -- `imm`: both composites are `A`
    rw [compR_imm_mut (by simp) (by simp) hc, compR_imm_mut (by simp) (by simp) hc']
    exact CellUpdN.refl _ _ _ _
  · -- `mut`: clause (3) on each side
    have hu : u = v' := by
      have := (CellU.CompR.erase hc).1; simpa using this
    have hτ : τ = χ' := by
      have := CellU.CompR.wit hc (by simp) (by simp); simpa using this
    subst hu
    subst hτ
    rw [CellU.CompR.functional hc (CellU.CompR.mutMut a b u τ ha hb P Q hP hQ),
      CellU.CompR.functional hc' (CellU.CompR.mutMut a b u τ ha hb' P Q' hP hQ')]
    have hst : MutStep Φ k l
        (CellU.mutOf (a ⊓ b) u τ ha.inf_left (SPropS.conj P Q) (SPropS.conj_holds ha hb hP hQ))
        (CellU.mutOf (a ⊓ b) u τ ha.inf_left (SPropS.conj P Q')
          (SPropS.conj_holds ha hb' hP hQ')) := by
      refine ⟨rfl, rfl, rfl, fun hn => ?_, fun b₀ F hF w r h' => ?_⟩
      · have e := hs.2.2.2.1 hn
        funext w r
        apply propext
        rw [cellPred_conj (hb := hb) (hP := hP) (hQ := hQ),
          cellPred_conj (hb := hb') (hP := hP) (hQ := hQ')]
        have e' : SPropS.toU (Q w) r ↔ SPropS.toU (Q' w) r := by
          rw [← mpred_mutOf (hw := hQ) w r, ← mpred_mutOf (hw := hQ') w r, e]
        rw [e']
      · obtain ⟨hr, hp, hq'⟩ := (cellPred_conj (hb := hb') (hP := hP) (hQ := hQ') w r).mp h'
        rcases hs.2.2.2.2 b₀ F hF w r ((mpred_mutOf (hw := hQ') w r).mpr hq') with hq | hF'
        · exact .inl ((cellPred_conj (hb := hb) (hP := hP) (hQ := hQ) w r).mpr
            ⟨hr, hp, (mpred_mutOf (hw := hQ) w r).mp hq⟩)
        · exact .inr hF'
    refine ⟨fun s w χ₀ h₀ => ⟨fun e => ?_, fun e => ?_⟩, fun φ e hk => ?_, fun φ e hk => ?_⟩
    · exact absurd (Option.some.inj e).symm CellU.immOf_ne_mutOf
    · exact absurd (Option.some.inj e).symm CellU.immOf_ne_mutOf
    · cases e; exact ⟨_, rfl, hst⟩
    · cases e; exact ⟨_, rfl, hst⟩

/-! ### `[TR]` 6.48 at the step index -/

/-- **`[TR]` Lemma 6.48 at the step index**: if `ρ₁ # ρ₂`, `ρ₁ # ρ₃` and `ρ₂ ↭ₖ ρ₃`, then
`ρ₁ ● ρ₂ ↭ₖ ρ₁ ● ρ₃`. The printed proof (`BoLo.updV_frame`), with `UpdMutN` in place of the
printed `mut` clause: the same three cases at `ℓ`; at the aliasable walk the `imm` ancestor carries
the cell (`agMutCarry`), and the `mut ○ mut` composites `P̂ ∧ Q̂`, `P̂ ∧ Q̂′` are related by
`compR_stepN` where the printed proof has them equal. -/
theorem updVN_frame {Φ : LocFam} {k : Nat} {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : WRes}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₂ : ResU.Hash ρ₁ ρ₂) (hh₃ : ResU.Hash ρ₁ ρ₃)
    (h : UpdVN Φ k ρ₂ ρ₃) : UpdVN Φ k ρ₁₂ ρ₁₃ := by
  classical
  obtain ⟨τ₁₂, hτ₁₂⟩ := hash_valid_comp hh₂ h₁₂
  obtain ⟨τ₁₃, hτ₁₃⟩ := hash_valid_comp hh₃ h₁₃
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hτ⟩ :=
    (ResU.Flat.split h₁₂).mp hτ₁₂
  obtain ⟨e₁', e₃, e', a₁', a₃, a', he₁', he₃, hec', ha₁', ha₃, hac', hτ'⟩ :=
    (ResU.Flat.split h₁₃).mp hτ₁₃
  rw [ExS.functional he₁' he₁] at hec'
  rw [AgW.functional ha₁' ha₁] at hac'
  obtain ⟨σ₂, x₂, y₂, hx₂, hy₂, hc₂⟩ := h.2.1
  rw [ExS.functional hx₂ he₂, AgW.functional hy₂ ha₂] at hc₂
  obtain ⟨σ₃, x₃, y₃, hx₃, hy₃, hc₃⟩ := h.2.2
  rw [ExS.functional hx₃ he₃, AgW.functional hy₃ ha₃] at hc₃
  have hfS : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc BoCa.Val,
      CellU.CompS ψ₁ ψ₂ ψ → CellU.CompS ψ₁ ψ₂ ψ' → ψ = ψ' :=
    fun _ _ _ _ p q => CellU.CompS.functional p q
  have hfR : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc BoCa.Val,
      CellU.CompR ψ₁ ψ₂ ψ → CellU.CompR ψ₁ ψ₂ ψ' → ψ = ψ' :=
    fun _ _ _ _ p q => CellU.CompR.functional p q
  -- 6.36: the exclusive walks are `imm`-free, so the three domains are disjoint
  have hdE : ∀ n, e₁.get n = none ∨ e₂.get n = none :=
    ResU.CompatS.disjoint_of_immFree (ExS.immFree he₁) hec.1
  have hdE' : ∀ n, e₁.get n = none ∨ e₃.get n = none :=
    ResU.CompatS.disjoint_of_immFree (ExS.immFree he₁) hec'.1
  have hdA : ∀ n, e.get n = none ∨ a.get n = none :=
    ResU.CompatS.disjoint_of_immFree
      (ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)) hτ.1
  have hdA' : ∀ n, e'.get n = none ∨ a'.get n = none :=
    ResU.CompatS.disjoint_of_immFree
      (ResU.ImmFree.compS hec' (ExS.immFree he₁) (ExS.immFree he₃)) hτ'.1
  have hcell : ∀ n, CellUpdN Φ k n (τ₁₂.get n) (τ₁₃.get n) := by
    intro n
    by_cases hE1 : e₁.get n = none
    · by_cases hA1 : a₁.get n = none
      · -- `ρ₁` is silent in both walks: each composite is the operand's own flattening
        have hEn : e.get n = e₂.get n := by
          rcases ResU.Comp.get hec n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
        have hAn : a.get n = a₂.get n := by
          rcases ResU.Comp.get hac n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
        have hEn' : e'.get n = e₃.get n := by
          rcases ResU.Comp.get hec' n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
        have hAn' : a'.get n = a₃.get n := by
          rcases ResU.Comp.get hac' n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
        have hL : τ₁₂.get n = σ₂.get n := by
          refine OptComp.functional hfS ?_ (hc₂.2 n)
          rw [← hEn, ← hAn]; exact hτ.2 n
        have hR : τ₁₃.get n = σ₃.get n := by
          refine OptComp.functional hfS ?_ (hc₃.2 n)
          rw [← hEn', ← hAn']; exact hτ'.2 n
        rw [hL, hR]
        exact cellUpdN_of_updN h.1 ⟨e₂, a₂, he₂, ha₂, hc₂⟩ ⟨e₃, a₃, he₃, ha₃, hc₃⟩ n
      · -- `ag(ρ₁)` is occupied: both composites are the aliasable ones
        have hAne : a.get n ≠ none := by
          rcases ResU.Comp.get hac n with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
        have hAne' : a'.get n ≠ none := by
          rcases ResU.Comp.get hac' n with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
        have hEnone : e.get n = none := (hdA n).resolve_right hAne
        have hEnone' : e'.get n = none := (hdA' n).resolve_right hAne'
        have hL : τ₁₂.get n = a.get n := by
          have h0 := hτ.2 n
          rw [hEnone] at h0
          cases hh : a.get n with
          | none => rw [hh] at h0; exact h0
          | some ψ => rw [hh] at h0; exact h0
        have hR : τ₁₃.get n = a'.get n := by
          have h0 := hτ'.2 n
          rw [hEnone'] at h0
          cases hh : a'.get n with
          | none => rw [hh] at h0; exact h0
          | some ψ => rw [hh] at h0; exact h0
        rw [hL, hR]
        -- the two aliasable walks agree at `n`, or both carry an `own`
        by_cases hk : ∀ ψ, a₂.get n = some ψ → ψ.kind = Kind.own
        · have hk' := updN_ag_own_or_none h.1 he₂ ha₂ hc₂ he₃ ha₃ hc₃ hk
          -- an `own` contributes nothing, so both composites are `ag(ρ₁)(n)`
          obtain ⟨ζ, hζ⟩ : ∃ ζ, a₁.get n = some ζ := by
            cases f : a₁.get n with
            | none => exact absurd f hA1
            | some ζ => exact ⟨ζ, rfl⟩
          have hone : ∀ (b c : ResU BoCa.Loc BoCa.Val),
              ResU.CompR a₁ b c → (∀ ψ, b.get n = some ψ → ψ.kind = Kind.own) →
              c.get n = some ζ := by
            intro b c hcc hb
            rcases ResU.Comp.get hcc n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
                ⟨ψ₁, ψ₂, ψ, f₁, f₂, f, hC⟩
            · rw [hζ] at f₁; exact absurd f₁ (by simp)
            · rw [f, ← hζ, f₁]
            · rw [hζ] at f₁; exact absurd f₁ (by simp)
            · rw [f, show ψ = ψ₁ from CellU.compR_own_kind_right hC (hb ψ₂ f₂),
                ← hζ, f₁]
          rw [hone a₂ a hac hk, hone a₃ a' hac' hk']
          exact CellUpdN.refl _ _ _ _
        · -- a cell that is not `own`: the ancestor step gives the same cell
          obtain ⟨ψ, hψ, hψk⟩ : ∃ ψ, a₂.get n = some ψ ∧ ψ.kind ≠ Kind.own := by
            by_contra hcon
            exact hk (fun ψ e => by
              by_contra hko
              exact hcon ⟨ψ, e, hko⟩)
          obtain ⟨ψ', hψ', hrel⟩ := updN_ag_ne_own h.1 he₂ ha₂ hc₂ he₃ ha₃ hc₃ hψ hψk
          rcases hrel with rfl | ⟨hst, hse, hsw⟩
          · have heq : a.get n = a'.get n := by
              refine OptComp.functional hfR (hac.2 n) ?_
              rw [hψ, ← hψ']; exact hac'.2 n
            rw [heq]
            exact CellUpdN.refl _ _ _ _
          · -- the printed `mut ○ mut` step, at `P̂ ∧ Q̂` and `P̂ ∧ Q̂′`
            obtain ⟨ζ, hζ⟩ : ∃ ζ, a₁.get n = some ζ := by
              cases f : a₁.get n with
              | none => exact absurd f hA1
              | some ζ => exact ⟨ζ, rfl⟩
            have g := hac.2 n
            have g' := hac'.2 n
            rw [hζ, hψ] at g
            rw [hζ, hψ'] at g'
            obtain ⟨c, hcn, hcc⟩ := g
            obtain ⟨c', hcn', hcc'⟩ := g'
            rw [hcn, hcn']
            exact compR_stepN hcc hcc' hst hse hsw
    · -- `ex(ρ₁)` is occupied: both composites are `ex(ρ₁)(n)`
      obtain ⟨ζ, hζ⟩ : ∃ ζ, e₁.get n = some ζ := by
        cases f : e₁.get n with
        | none => exact absurd f hE1
        | some ζ => exact ⟨ζ, rfl⟩
      have hstep : ∀ (x ex ax cx tx : ResU BoCa.Loc BoCa.Val),
          ResU.CompS e₁ x ex → ResU.CompR a₁ ax cx → ResU.CompS ex cx tx →
          (∀ m, ex.get m = none ∨ cx.get m = none) →
          (∀ m, e₁.get m = none ∨ x.get m = none) → tx.get n = some ζ := by
        intro x ex ax cx tx hxe hxa hxt hdd hde
        have hexn : ex.get n = some ζ := by
          rcases ResU.Comp.get hxe n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
          · rw [hζ] at f₁; exact absurd f₁ (by simp)
          · rw [f, ← hζ, f₁]
          · rw [hζ] at f₁; exact absurd f₁ (by simp)
          · rcases hde n with c | c
            · rw [hζ] at c; exact absurd c (by simp)
            · rw [c] at f₂; exact absurd f₂ (by simp)
        have hcxn : cx.get n = none := (hdd n).resolve_left (by rw [hexn]; simp)
        rcases ResU.Comp.get hxt n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
            ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
        · rw [hexn] at f₁; exact absurd f₁ (by simp)
        · rw [f, ← hexn, f₁]
        · rw [hexn] at f₁; exact absurd f₁ (by simp)
        · rw [hcxn] at f₂; exact absurd f₂ (by simp)
      rw [hstep e₂ e a₂ a τ₁₂ hec hac hτ hdA hdE,
        hstep e₃ e' a₃ a' τ₁₃ hec' hac' hτ' hdA' hdE']
      exact CellUpdN.refl _ _ _ _
  exact ⟨updN_of_flat hτ₁₂ hτ₁₃ hcell, ⟨τ₁₂, hτ₁₂⟩, ⟨τ₁₃, hτ₁₃⟩⟩

/-! ### The anti-frame's write at the step index: `[TR]` 6.28 with a stepped member

`wpTS_M_antiFrameX` (`Core/FrameRules.lean`) writes the value the callback hands back into the
cell's *stored* predicate (`ptoMutX_write (Q := Qs)`) and gets `ρ ↭ π′` from `[TR]` 6.28's
right-to-left half (`ResU.six28`), whose two `mut` cells share `P̂`. At a step index the value is
known at the index the callback ends at, `m`, not at the stored member's (`StepGap`); the write
stores `F m`, and 6.28's right-to-left half holds at `UpdN` with the two cells at `F j` and
`F m`, `k ≤ m`: `six28N`. -/

/-- **`[TR]` 6.28, right to left, at the step index**: `ρ ● ℓ ↦ own(v) ● ρ_v ↭ₖ
ρ′ ● ℓ ↦ own(v′) ● ρ′_v` gives `ρ ● ℓ ↦ mut(β, v, ρ_v, F j) ↭ₖ ρ′ ● ℓ ↦ mut(β, v′, ρ′_v, F m)`
when `ℓ` follows `F` and `k ≤ m`. The printed proof's string of iffs, off `ℓ` as printed, at `ℓ`
by `mutStep_write`. -/
theorem six28N {Φ : LocFam} (hΦ : Φ.Down) {k : Nat} {l : Loc} {b : Life}
    {G : Nat → Val → SPropS Loc Val b} (hG : Φ l = some ⟨b, G⟩) {j m : Nat} (hm : k ≤ m)
    {v v' : Val} {ρ ρ' ρv ρv' W W' M M' O O' : WRes}
    {hs : ResU.InStratum b ρv} {hs' : ResU.InStratum b ρv'}
    {hw : G j v ⟨ρv, hs⟩} {hw' : G m v' ⟨ρv', hs'⟩}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W)
    (hW' : ResU.CompS ρv' (ResU.single l (CellU.ownOf v')) W')
    (hM : ResU.CompS ρ (ResU.single l (CellU.mutOf b v ρv hs (G j) hw)) M)
    (hM' : ResU.CompS ρ' (ResU.single l (CellU.mutOf b v' ρv' hs' (G m) hw')) M')
    (hO : ResU.CompS ρ W O) (hO' : ResU.CompS ρ' W' O')
    (hvM : ResU.Valid M) (hvM' : ResU.Valid M')
    (hvO : ResU.Valid O) (hvO' : ResU.Valid O')
    (h : UpdN Φ k O O') : UpdN Φ k M M' := by
  classical
  obtain ⟨σM, hσM⟩ := hvM
  obtain ⟨σM', hσM'⟩ := hvM'
  obtain ⟨σO, hσO⟩ := hvO
  obtain ⟨σO', hσO'⟩ := hvO'
  obtain ⟨hoff, hMl, -⟩ := ResU.flat_mut_own_agree_off hW hM hO hσM hσO
  obtain ⟨hoff', hMl', -⟩ := ResU.flat_mut_own_agree_off hW' hM' hO' hσM' hσO'
  refine updN_of_flat hσM hσM' (fun x => ?_)
  by_cases hx : x = l
  · subst hx
    rw [hMl, hMl']
    refine ⟨fun s w χ hh => ⟨fun e => ?_, fun e => ?_⟩, fun ψ e _ => ?_, fun ψ e _ => ?_⟩
    · exact absurd (Option.some.inj e) CellU.immOf_ne_mutOf.symm
    · exact absurd (Option.some.inj e) CellU.immOf_ne_mutOf.symm
    · cases e; exact ⟨_, rfl, mutStep_write hΦ hG hm⟩
    · cases e; exact ⟨_, rfl, mutStep_write hΦ hG hm⟩
  · rw [← hoff x hx, ← hoff' x hx]
    exact cellUpdN_of_updN h hσO hσO' x

end BoCa.Fig16.LogRel.Core.Chain.SI

end
