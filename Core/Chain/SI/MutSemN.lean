import Core.Chain.SI.LendProg

/-!
# Unknown 2: `Mut` in `𝒱` at the step index

## The concern

The location typing `Φ` (`LocFam`, `SI/WpN.lean`) fixes a location's family `F` when a frame lends it
(`rwp_M_frame` at `Φ[ℓ ↦ (A, F)]`). If `𝒱ₖ⟦A⟧` depended on `Φ`, a value written into the cell
inside the borrowed run, at an extended `Φ′ ⊇ Φ`, could lie in `𝒱ₖ⟦A⟧(Φ′)` and not in the family
fixed at the lend. Ahmed's answer is a recursive world: families as functions of `Φ` at lower
indices.

## The definition, and why no recursive world is needed

BoLo's `mut` cell stores its predicate in the resource (`CellU.mutOf β v χ P`), and the
predicate is over `Res_β`: the circularity Ahmed's store typing has is broken by the lifetime
stratification, not by the index. The index enters only in which member of a family a cell
holds. So `𝒱ₖ⟦Mut @a A⟧` is defined without `Φ`:

    𝒱ₖ⟦Mut @a A⟧(v, ρ) ≜ ∃ ℓ w χ j. k ≤ j ∧ v = ℓ ∧ ρ = ℓ ↦ mut(a, w, χ, 𝒱ⱼ⟦A⟧|_{Res_a})

the cell holds the member `j ≥ k` of the payload type's own family `λj. 𝒱ⱼ⟦A⟧` (`vMut`). A
semantic type is an index-downward-closed predicate on values and resources (`SemT`), its
family at a stratum is `SemT.fam`, and `Φ` is a parameter of runs only. A thunk's `𝒱` quantifies
over every `Φ′` (`vThunk`), so it does not depend on the ambient `Φ` either.

`Φ` is then a plain function into families that do not mention `Φ`: there is no circularity
for a recursive world to resolve.

## What is proved

* `vMut` is downward closed, and is a `SemT` for every `SemT` payload, so `Mut @a (Mut @b A)` is
  `vMut a (vMut b τ)`; `vThunk` is downward closed (`erwp_le`).
* Monotonicity under world extension: `𝒱` does not mention `Φ`; the relation is monotone in it:
  `UpdN.extΦ`, `rwpG_extΦ`, `erwp_extΦ` (a step at `Φ` is a step at every `Φ′ ⊇ Φ`).
* The frames at a semantic payload: `rwp_M_frame_sem` (6.65 lends the cell at `τ.fam A`; the
  borrowed run holds a `vMut A τ` value, `lend_vMut`; the lender reads back `τ` at the index
  left) and `rwp_M_antiFrame_sem` (6.66 re-seals the cell as a `vMut A τ` value at the index
  left).
* Obs 2's case: a value written into the cell inside the borrowed run, at any `Φ′`, lies in the
  family fixed at the lend whenever it lies in `τ` (`written_in_family`), for `τ = vMut b σ` and
  for a thunk.
* The stratification, explicitly: a `Mut @b` value can be lent inside a cell lent at `A₀` only
  when `A₀ ⊏ b` (`vMut_inStratum`); a value whose cell is shorter-lived than `A₀` is refused at
  the write-back (`vMut_not_inStratum`). Both are the printed side conditions (`ρ_P ∈ Res_A`), not
  index facts: the index and the lifetimes do not interact.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-! ### Semantic types at the index -/

/-- A semantic type at the step index: downward closed in the index. -/
structure SemT where
  P : Nat → Val → WRes → Prop
  down : ∀ k v ρ, P (k + 1) v ρ → P k v ρ

theorem SemT.le (τ : SemT) {m k : Nat} (h : m ≤ k) : ∀ v ρ, τ.P k v ρ → τ.P m v ρ := by
  induction h with
  | refl => exact fun _ _ x => x
  | step _ ih => exact fun v ρ x => ih v ρ (τ.down _ v ρ x)

/-- A semantic type's family over `Res_A`: what a cell lent at `A` stores members of. -/
def SemT.fam (τ : SemT) (A : Life) : Nat → Val → SPropS Loc Val A := fun k v r => τ.P k v r.1

theorem SemT.fam_down (τ : SemT) (A : Life) : DownFam A (τ.fam A) :=
  fun k v r h => τ.down k v r.1 h

/-- **`𝒱ₖ⟦Mut @a τ⟧`**: a location whose `mut` cell at `a` holds the member `j ≥ k` of `τ`'s
family. -/
def vMutP (a : Life) (τ : SemT) (k : Nat) (v : Val) (ρ : WRes) : Prop :=
  ∃ (l : Loc) (w : Val) (χ : WRes) (hχ : χ.InStratum a) (j : Nat) (hw : τ.fam a j w ⟨χ, hχ⟩),
    k ≤ j ∧ v = Val.loc l ∧ ρ = ResU.single l (CellU.mutOf a w χ hχ (τ.fam a j) hw)

/-- `Mut @a τ` as a semantic type: downward closed. -/
def vMut (a : Life) (τ : SemT) : SemT where
  P := vMutP a τ
  down := fun _ _ _ ⟨l, w, χ, hχ, j, hw, hkj, hv, hρ⟩ => ⟨l, w, χ, hχ, j, hw, by omega, hv, hρ⟩

/-- `Φ` types every top-level `mut` cell of `ρ` with a family the cell's predicate is a member
of: what a computation holding `ρ` needs of the location typing it runs at, to open those
cells (6.66 at the index asks `Φ ℓ = (β, F)` with the cell at a member of `F`). -/
def Covers (Φ : LocFam) (ρ : WRes) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.mut →
    ∃ F : Nat → Val → SPropS Loc Val ψ.at, Φ l = some ⟨ψ.at, F⟩ ∧
      ∃ j, ∀ v r, cellPred ψ v r ↔ SPropS.toU (F j v) r

/-- **`𝒱ₖ⟦U C⟧`** for a computation relation `C Φ k v ρ` downward closed in `k`: `C` at every
location typing that covers the thunk's resource. -/
def vThunk (C : LocFam → Nat → Val → WRes → Prop)
    (hC : ∀ Φ, Φ.Down → ∀ k v ρ, C Φ (k + 1) v ρ → C Φ k v ρ) : SemT where
  P := fun k v ρ => ∀ Φ', Φ'.Down → Covers Φ' ρ → C Φ' k v ρ
  down := fun k v ρ h Φ' hΦ' hc => hC Φ' hΦ' k v ρ (h Φ' hΦ' hc)

/-- The thunk of a computation at `erwp`: forced, in `erwp` at the table `T` and `Q`. -/
def vThunkE (T : OpTabN) (hT : T.Down) (Q : PostN) (hQ : Q.Down) : SemT :=
  vThunk (fun Φ k v ρ => erwp (ℍ := ℍ) Φ (opTableN T) Q k [] (.app (.val v) (.val .unit)) ρ)
    (fun _ hΦ _ _ _ h => erwp_le hΦ (opTableN_local T) (opTableN_down hT) hQ (Nat.le_succ _) h)

/-- `Mut @a (Mut @b τ)`. -/
abbrev vMutMut (a b : Life) (τ : SemT) : SemT := vMut a (vMut b τ)

/-! ### The stratification -/

/-- **A `Mut @b` value lies in `Res_{A₀}` exactly when `A₀ ⊏ b`**: the condition under which it
can be the content of a cell lent at `A₀` (6.65's `ρ_P ∈ Res_A`). -/
theorem vMut_inStratum {b A₀ : Life} {τ : SemT} {k : Nat} {v : Val} {ρ : WRes}
    (h : (vMut b τ).P k v ρ) (hb : A₀ < b) : ρ.InStratum A₀ := by
  obtain ⟨l, w, χ, hχ, j, hw, -, -, rfl⟩ := h
  exact ResU.inStratum_single l ((CellU.inStratum_mutOf A₀ b w χ hχ _ hw).mpr hb)

/-- …and a `Mut @b` value with `b ⊑ A₀` is not in `Res_{A₀}`: a borrow shorter than the lend
cannot be written into the lent cell. -/
theorem vMut_not_inStratum {b A₀ : Life} {τ : SemT} {k : Nat} {v : Val} {ρ : WRes}
    (h : (vMut b τ).P k v ρ) (hb : b ≤ A₀) : ¬ ρ.InStratum A₀ := by
  obtain ⟨l, w, χ, hχ, j, hw, -, -, rfl⟩ := h
  intro hs
  have := hs l _ (ResU.single_get_self _ _)
  rw [CellU.inStratum_mutOf] at this
  exact absurd (lt_of_lt_of_le this hb) (lt_irrefl _)

/-! ### Monotonicity under world extension -/

/-- `Φ′` extends `Φ`: every location `Φ` types, `Φ′` types alike. -/
def LocFam.Ext (Φ Φ' : LocFam) : Prop := ∀ l x, Φ l = some x → Φ' l = some x

theorem LocFam.ext_set {Φ : LocFam} {l : Loc} (hl : Φ l = none) (A : Life)
    (F : Nat → Val → SPropS Loc Val A) : Φ.Ext (Φ.set l A F) := by
  intro x y hx
  by_cases h : x = l
  · subst h; rw [hl] at hx; cases hx
  · simp [LocFam.set, h, hx]

theorem PredStep.extΦ {Φ Φ' : LocFam} (hE : Φ.Ext Φ') {n : Nat} {l : Loc}
    {p p' : Val → WRes → Prop} (h : PredStep Φ n l p p') : PredStep Φ' n l p p' := by
  refine ⟨fun h' => ?_, fun b F hF v r hp => ?_⟩
  · cases hl : Φ l with
    | none => exact h.1 hl
    | some x => rw [hE l x hl] at h'; cases h'
  · cases hl : Φ l with
    | none => exact .inl ((h.1 hl) ▸ hp)
    | some x =>
        have := hE l x hl
        rw [hF] at this
        cases this
        exact h.2 b F hl v r hp

theorem MutStep.extΦ {Φ Φ' : LocFam} (hE : Φ.Ext Φ') {n : Nat} {l : Loc}
    {ψ ψ' : CellU Loc Val} (h : MutStep Φ n l ψ ψ') : MutStep Φ' n l ψ ψ' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.extΦ hE⟩

/-- **`↭` at `Φ` is `↭` at every extension of `Φ`.** -/
theorem UpdVN.extΦ {Φ Φ' : LocFam} (hE : Φ.Ext Φ') {n : Nat} {ρ₁ ρ₂ : WRes}
    (h : UpdVN Φ n ρ₁ ρ₂) : UpdVN Φ' n ρ₁ ρ₂ := by
  refine ⟨⟨h.1.1, fun l ψ hg hk => ?_, fun l ψ' hg hk => ?_⟩, h.2⟩
  · obtain ⟨ψ', h', hs⟩ := h.1.2.1 l ψ hg hk
    exact ⟨ψ', h', hs.extΦ hE⟩
  · obtain ⟨ψ, h', hs⟩ := h.1.2.2 l ψ' hg hk
    exact ⟨ψ, h', hs.extΦ hE⟩

/-- Covering is kept by world extension. -/
theorem Covers.extΦ {Φ Φ' : LocFam} (hE : Φ.Ext Φ') {ρ : WRes} (h : Covers Φ ρ) :
    Covers Φ' ρ := fun l ψ hg hk => by
  obtain ⟨F, hF, hj⟩ := h l ψ hg hk
  exact ⟨F, hE l _ hF, hj⟩

/-- The `imm` records of `Φ` are among `Φ′`'s. -/
def LocFam.ImmLe (Φ Φ' : LocFam) : Prop := ∀ x ∈ Φ.imm, x ∈ Φ'.imm

theorem LocFam.immLe_set (Φ : LocFam) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) :
    Φ.ImmLe (Φ.set l A F) := fun _ h => h

theorem rwpG_extΦ {Φ Φ' : LocFam} (hE : Φ.Ext Φ') (hEI : Φ.ImmLe Φ') {Q : PostG} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) : rwpG (ℍ := ℍ) Φ' Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hc hT htg (hI.mono hEI) hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇.extΦ hE, h₈, h₉, h₁₀, h₁₁,
    h₁₂, h₁₃⟩

/-- **The relation is monotone under world extension**, stops and their continuations
included (by induction on the index). -/
theorem erwp_extΦ {Φ Φ' : LocFam} (hE : Φ.Ext Φ') (hEI : Φ.ImmLe Φ') {Tb : TableN} (hL : Tb.Local) {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ Tb Q n ls e ρ → erwp (ℍ := ℍ) Φ' Tb Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  rw [erwp_eq] at h ⊢
  refine rwpG_extΦ hE hEI (rwpG_mono_le (fun k hk ls' t σ ht => ?_) h)
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hL k ls' t _ _ σ (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) _ _ _ hΨ

/-! ### The frames at a semantic payload -/

/-- **6.65 at a semantic payload.** The cell holds a `τ` value at `n`; it is lent at `A` with
`τ`'s family; the lender reads back a `τ` value at the index left. -/
theorem rwp_M_frame_sem {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {A : Life} (τ : SemT) {Q : PostN}
    {n : Nat} {ls : List SRec} {e : Expr} {v : Val} {ρP ρlP ρb ρ : WRes}
    (houtP : ρP.InStratum A) (houtb : ρb.InStratum A) (hv : τ.P n v ρP)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hA : ∀ BM, ResU.CompS ρb
        (ResU.single l (CellU.mutOf A v ρP houtP (τ.fam A n) (show τ.fam A n v ⟨ρP, houtP⟩ from hv)))
        BM →
      rwp (ℍ := ℍ) (Φ.set l A (τ.fam A)) (MFPost l A (τ.fam A) Q) n ls e BM) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ :=
  rwp_M_frame hΦ (τ.fam_down A) le_rfl houtP houtb hv hclP hcρ hA

/-- The borrow 6.65 hands the borrowed run is a `Mut @A τ` value at `n`. -/
theorem lend_vMut {l : Loc} {A : Life} (τ : SemT) {n : Nat} {v : Val} {ρP : WRes}
    (houtP : ρP.InStratum A) (hv : τ.P n v ρP) :
    (vMut A τ).P n (Val.loc l)
      (ResU.single l (CellU.mutOf A v ρP houtP (τ.fam A n) (show τ.fam A n v ⟨ρP, houtP⟩ from hv))) :=
  ⟨l, v, ρP, houtP, n, hv, le_rfl, rfl, rfl⟩

/-- **6.66 at a semantic payload**: a `Mut @A τ` value at a location `Φ` types with `τ`'s family
is opened; the run hands back a `τ` value at the index left, and the cell is re-sealed as a
`Mut @A τ` value there. -/
theorem rwp_M_antiFrame_sem {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {A : Life} (τ : SemT)
    (hF : Φ l = some ⟨A, τ.fam A⟩) {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr}
    {ρm ρa ρ : WRes} (hm : (vMut A τ).P n (Val.loc l) ρm) (hsplit : ResU.CompS ρm ρa ρ)
    (hA : ∀ (v : Val) (σP : WRes), τ.P n v σP → ∀ W X,
      ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
      rwp (ℍ := ℍ) Φ (fun k ls' v' ρ' => ∃ (w : Val) (σ' : WRes) (_ : σ'.InStratum A),
        τ.P k w σ' ∧ ∃ R rest, ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρ' ∧
          ResU.CompS σ' R rest ∧
          ∀ X ρm', (vMut A τ).P k (Val.loc l) ρm' → ResU.CompS R ρm' X → Q k ls' v' X)
        n ls e X) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  obtain ⟨l', w, χ, hχ, j, hw, hnj, hl, rfl⟩ := hm
  obtain rfl : l = l' := by
    have := congrArg Subtype.val hl
    simpa [Val.loc] using this
  refine rwp_M_antiFrame hΦ hF hsplit (fun W X hW hX => ?_)
  refine rwp_mono (fun k ls' v' ρ' h => ?_) (hA w χ (τ.le hnj w χ hw) W X hW hX)
  obtain ⟨w', σ', h', hw', R, rest, h₁, h₂, hQ⟩ := h
  exact ⟨w', σ', h', hw', R, rest, h₁, h₂, fun X hX =>
    hQ X _ ⟨l, w', σ', h', k, hw', le_rfl, rfl, rfl⟩ hX⟩

/-! ### Obs 2's case: a write inside the borrowed run lies in the fixed family -/

/-- **A value written into a cell lent at `A₀` inside the borrowed run, at any location typing
`Φ′`, lies in the family fixed at the lend whenever it lies in `τ` at the index** — `τ`'s `𝒱`
does not mention `Φ′`. -/
theorem written_in_family (τ : SemT) (A₀ : Life) {k : Nat} {w : Val} {σ : WRes}
    (hσ : σ.InStratum A₀) (h : τ.P k w σ) : τ.fam A₀ k w ⟨σ, hσ⟩ := h

/-- For `Mut @a (Mut @b τ)`: the written value is a `Mut @b τ` value; it is in `Res_{A₀}` when
`A₀ ⊏ b`, and then in the family fixed at the lend. -/
theorem written_mutMut {b A₀ : Life} (τ : SemT) (hb : A₀ < b) {k : Nat} {w : Val} {σ : WRes}
    (h : (vMut b τ).P k w σ) :
    ∃ hσ : σ.InStratum A₀, (vMut b τ).fam A₀ k w ⟨σ, hσ⟩ :=
  ⟨vMut_inStratum h hb, h⟩

/-- For a thunk: the written thunk, owning a resource in `Res_{A₀}`, is in the family fixed at
the lend, whatever `Φ′` the write happens at. -/
theorem written_thunk (T : OpTabN) (hT : T.Down) (Q : PostN) (hQ : Q.Down) (A₀ : Life)
    {k : Nat} {w : Val} {σ : WRes} (hσ : σ.InStratum A₀)
    (h : ∀ Φ', Φ'.Down → Covers Φ' σ →
      erwp (ℍ := ℍ) Φ' (opTableN T) Q k [] (.app (.val w) (.val .unit)) σ) :
    (vThunkE (ℍ := ℍ) T hT Q hQ).fam A₀ k w ⟨σ, hσ⟩ := h

/-- **The Mut Frame for `Mut @a (Mut @b τ)`**: a cell holding a `Mut @b τ` value, lent at
`A₀ ⊏ b`; the lender reads back a `Mut @b τ` value. -/
theorem rwp_M_frame_mutMut {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {A₀ b : Life} (hb : A₀ < b)
    (τ : SemT) {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {v : Val} {ρP ρlP ρb ρ : WRes}
    (houtb : ρb.InStratum A₀) (hv : (vMut b τ).P n v ρP)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hA : ∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A₀ v ρP (vMut_inStratum hv hb)
        ((vMut b τ).fam A₀ n) (show (vMut b τ).fam A₀ n v ⟨ρP, vMut_inStratum hv hb⟩ from hv)))
        BM →
      rwp (ℍ := ℍ) (Φ.set l A₀ ((vMut b τ).fam A₀)) (MFPost l A₀ ((vMut b τ).fam A₀) Q) n ls e BM) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ :=
  rwp_M_frame_sem hΦ (vMut b τ) (vMut_inStratum hv hb) houtb hv hclP hcρ hA

/-- **The Mut Frame for a thunk payload.** -/
theorem rwp_M_frame_thunk {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {A₀ : Life} (T : OpTabN)
    (hT : T.Down) (Qt : PostN) (hQt : Qt.Down) {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr}
    {v : Val} {ρP ρlP ρb ρ : WRes} (houtP : ρP.InStratum A₀) (houtb : ρb.InStratum A₀)
    (hv : (vThunkE (ℍ := ℍ) T hT Qt hQt).P n v ρP)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (hA : ∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A₀ v ρP houtP
        ((vThunkE (ℍ := ℍ) T hT Qt hQt).fam A₀ n)
        (show (vThunkE (ℍ := ℍ) T hT Qt hQt).fam A₀ n v ⟨ρP, houtP⟩ from hv))) BM →
      rwp (ℍ := ℍ) (Φ.set l A₀ ((vThunkE (ℍ := ℍ) T hT Qt hQt).fam A₀))
        (MFPost l A₀ ((vThunkE (ℍ := ℍ) T hT Qt hQt).fam A₀) Q) n ls e BM) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ :=
  rwp_M_frame_sem hΦ (vThunkE (ℍ := ℍ) T hT Qt hQt) houtP houtb hv hclP hcρ hA

end BoCa.Fig16.LogRel.Core.Chain.SI

end
