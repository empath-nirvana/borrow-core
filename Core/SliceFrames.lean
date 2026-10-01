import Core.Arrays
import Core.FrameRules
import Core.EffWp

/-!
# Core — frames over a family of places  `[spec §9]`

The model's side of `slice_borrow` (`Core/Slices.lean`). A family of places `I` is read as the
iterated separating conjunction of its leaves, `sepList P [ℓ₁, …, ℓ_k] = P ℓ₁ ⋆ … ⋆ P ℓ_k`; an
array's range `[ℓ, ℓ + n)` is the instance `rangeLocs ℓ n` (`sepRange_eq_sepList`).

- `wpTS_M_frameList`: one Mut Frame (`[TR]` 6.65, `wpTS_M_frameX`) per place of a finite list,
  around one expression, by induction on the list; `wpTS_M_frameFam` at an array's range.
- `wpTS_I_frameList`: the same with Imm Frame (`[TR]` 6.64, `wpTS_I_frameX`), each frame adding
  its record, the leaves stable along `Ext` (`immLeaf_ext`); `wpTS_I_frameFam`.
- `vP_fam_split`, `vP_fam_join`: a family at every leaf predicate splits at a run-time index
  and joins back; `sepList_partition` splits a list of places along any predicate.

Frame `j` picks its own lifetime `α_j`, each strictly below the one before, and the callback
receives every leaf at the innermost: `ptoMutS`/`ptoImmS` are antitone in the lifetime
(6.118, 6.114). Frame `j`'s postcondition sits under `[α_j]` while the callback returns a
resource known to be in `Res_{α_n}` only; the premises `Φ ⊨ [β′]Φ` and `𝒱⟦T⟧ ⊨ [β]𝒱⟦T⟧`
supply the missing strata, every `α_j` chosen below `β` and `β′`. At `Imm`, 6.64 wants an
`Ext`-stable postcondition, so the induction runs at the stable `⊛ 𝒱⟦Ref T⟧ ⋆ Φ` and weakens
after.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The indexed tensor over a finite list of places -/

/-- `⊛_{ℓ ∈ ls} P ℓ`. -/
def sepList (P : Loc → WProp) : List Loc → WProp
  | [] => emp
  | ℓ :: ls => sep (P ℓ) (sepList P ls)

/-- `[ℓ, ℓ + 1, …, ℓ + n − 1]`. -/
def rangeLocs : Loc → Nat → List Loc
  | _, 0 => []
  | ℓ, n + 1 => ℓ :: rangeLocs (ℓ + 1) n

/-- An array's relation is the indexed tensor over its range. -/
theorem sepRange_eq_sepList (P : Loc → WProp) : ∀ (ℓ : Loc) (n : Nat),
    sepRange P ℓ n = sepList P (rangeLocs ℓ n)
  | _, 0 => rfl
  | ℓ, n + 1 => by
      show sep (P ℓ) (sepRange P (ℓ + 1) n) = sep (P ℓ) (sepList P (rangeLocs (ℓ + 1) n))
      rw [sepRange_eq_sepList P (ℓ + 1) n]

theorem rangeLocs_append : ∀ (ℓ : Loc) (i k : Nat),
    rangeLocs ℓ (i + k) = rangeLocs ℓ i ++ rangeLocs (ℓ + i) k
  | ℓ, 0, k => by simp [rangeLocs]
  | ℓ, i + 1, k => by
      rw [show i + 1 + k = (i + k) + 1 by omega]
      simp only [rangeLocs, List.cons_append]
      rw [rangeLocs_append (ℓ + 1) i k, show ℓ + 1 + i = ℓ + (i + 1) by ring]

/-- A split of the index set is a split of the tensor. -/
theorem sepList_append {P : Loc → WProp} :
    ∀ (l₁ l₂ : List Loc) (ρ : WRes),
      sepList P (l₁ ++ l₂) ρ ↔ (sepList P l₁ ⋆ sepList P l₂) ρ
  | [], l₂, ρ => by
      constructor
      · intro h; exact ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, trivial⟩, h⟩
      · rintro ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, h⟩
        rw [eq_of_compS_empty_left hc] at *; exact h
  | ℓ :: l₁, l₂, ρ => by
      constructor
      · rintro ⟨ρa, ρb, hc, ha, hb⟩
        obtain ⟨ρ₁, ρ₂, hc', h₁, h₂⟩ := (sepList_append l₁ l₂ ρb).mp hb
        obtain ⟨x, hx, hρ⟩ := compS_reassoc' hc' hc
        exact ⟨x, ρ₂, hρ, ⟨ρa, ρ₁, hx, ha, h₁⟩, h₂⟩
      · rintro ⟨ρ₁, ρ₂, hc, ⟨ρa, ρb, hab, ha, hb⟩, h₂⟩
        obtain ⟨x, hx, hρ⟩ := compS_reassoc hab hc
        exact ⟨ρa, x, hρ, ha, (sepList_append l₁ l₂ x).mpr ⟨ρb, ρ₂, hx, hb, h₂⟩⟩

/-- The order of the index set does not matter. -/
theorem sepList_perm {P : Loc → WProp} {l₁ l₂ : List Loc} (hp : l₁.Perm l₂) :
    ∀ ρ, sepList P l₁ ρ → sepList P l₂ ρ := by
  induction hp with
  | nil => exact fun _ h => h
  | cons x _ ih =>
      rintro ρ ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
      exact ⟨ρ₁, ρ₂, hc, h₁, ih ρ₂ h₂⟩
  | swap x y l =>
      rintro ρ ⟨ρ₁, ρ₂, hc, h₁, ρ₃, ρ₄, hc', h₃, h₄⟩
      obtain ⟨z, hz, hρ⟩ := compS_lcomm hc' hc
      exact ⟨ρ₃, z, hρ, h₃, ρ₁, ρ₄, hz, h₁, h₄⟩
  | trans _ _ ih₁ ih₂ => exact fun ρ h => ih₂ ρ (ih₁ ρ h)

/-- A property closed under `●` and holding at `∅` holds of a tensor whose leaves have it. -/
theorem sepList_closed {R : WRes → Prop} (h0 : R PMap.empty)
    (hc : ∀ ρ₁ ρ₂ ρ, ResU.CompS ρ₁ ρ₂ ρ → R ρ₁ → R ρ₂ → R ρ) {P : Loc → WProp}
    (hP : ∀ m ρ, P m ρ → R ρ) : ∀ {l : List Loc} {ρ : WRes}, sepList P l ρ → R ρ
  | [], _, ⟨rfl, _⟩ => h0
  | _ :: _, _, ⟨_, _, hcρ, h₁, h₂⟩ => hc _ _ _ hcρ (hP _ _ h₁) (sepList_closed h0 hc hP h₂)

/-- Leafwise entailment under a property inherited by parts. -/
theorem sepList_mono_down {R : WRes → Prop}
    (hR : ∀ a₁ a₂ a, ResU.CompS a₁ a₂ a → R a → R a₁ ∧ R a₂) {P Q : Loc → WProp}
    (h : ∀ m σ, R σ → P m σ → Q m σ) :
    ∀ {l : List Loc} {ρ : WRes}, R ρ → sepList P l ρ → sepList Q l ρ
  | [], _, _, hP => hP
  | _ :: _, _, hρ, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ =>
      ⟨ρ₁, ρ₂, hc, h _ _ (hR _ _ _ hc hρ).1 h₁, sepList_mono_down hR h (hR _ _ _ hc hρ).2 h₂⟩

theorem sepList_mono' {P Q : Loc → WProp} (h : ∀ m ρ, P m ρ → Q m ρ) {l : List Loc}
    {ρ : WRes} (hP : sepList P l ρ) : sepList Q l ρ :=
  sepList_mono_down (R := fun _ => True) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
    (fun m σ _ h' => h m σ h') trivial hP

/-! ### The Mut Frame over a family of places -/

/-- An owned leaf `ℓ ↦ v ⋆ 𝒱⟦T ℓ⟧(v)`, its type chosen by its place: a struct's field. -/
abbrev ownLeafH (T : Loc → VTy) (ls : List SRec) (δ : LSub) : Loc → WProp :=
  fun m => vP (.ref (T m)) ls δ (.loc m)

/-- A `mut` leaf at `α`, its type chosen by its place. -/
abbrev mutLeafH (T : Loc → VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp :=
  fun m => ptoMutS m α ls (fun ls₀ => vC true (T m) ls₀ δ)

/-- An owned leaf of one type, the leaf of `Array T`. -/
abbrev ownLeaf (T : VTy) (ls : List SRec) (δ : LSub) : Loc → WProp := ownLeafH (fun _ => T) ls δ

/-- A `mut` leaf of one type, the leaf of `[Mut 'c T]` at `'c ↦ α`. -/
abbrev mutLeaf (T : VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp :=
  mutLeafH (fun _ => T) ls δ α

/-- A property of resources closed under `●` and holding at `∅`: membership in `Res_α`. -/
theorem outlives_compS_closed (α : Life) :
    ∀ ρ₁ ρ₂ ρ : WRes, ResU.CompS ρ₁ ρ₂ ρ → BoLo.Outlives ρ₁ α → BoLo.Outlives ρ₂ α →
      BoLo.Outlives ρ α :=
  fun _ _ _ hc h₁ h₂ => (BoLo.outlives_comp hc α).mpr ⟨h₁, h₂⟩

/-- An owned leaf is in `Res_α` when its payload's relation is. -/
theorem ownLeaf_outlives {T : Loc → VTy} {δ : LSub} {β α : Life} (hαβ : α ⊑ β)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) {ls : List SRec} {m : Loc}
    {ρ : WRes} (h : ownLeafH T ls δ m ρ) : BoLo.Outlives ρ α := by
  obtain ⟨ℓ', w, hk⟩ := h
  obtain ⟨-, c, p, hcp, hc, hp⟩ := pure_sep_iff.mp hk
  refine (BoLo.outlives_comp hcp α).mpr ⟨?_, ?_⟩
  · rw [hc]; exact ResU.inStratum_single_own α ℓ' w
  · exact BoLo.Outlives.mono hαβ (hP m ls w p hp)

/-- A family of owned leaves is in `Res_α`. -/
theorem ownList_outlives {T : Loc → VTy} {δ : LSub} {β α : Life} (hαβ : α ⊑ β)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) {ls : List SRec} {I : List Loc}
    {ρ : WRes} (h : sepList (ownLeafH T ls δ) I ρ) : BoLo.Outlives ρ α :=
  sepList_closed (ResU.inStratum_empty α) (outlives_compS_closed α)
    (fun _ _ h => ownLeaf_outlives hαβ hP h) h

/-- **One Mut Frame per place, around one expression**, the run ending at any final term.  The
leaves may differ in type. -/
theorem wpG_M_frameList (T : Loc → VTy) (δ : LSub) (β : Life)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) (e : Expr) (ls : List SRec)
    (Φ : List SRec → Expr → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β') :
    ∀ (I : List Loc) (Q : List SRec → Expr → WProp),
      (∀ ls' v, Entails (sepList (ownLeafH T ls' δ) I ⋆ Φ ls' v) (Q ls' v)) →
      Entails
        (sepList (ownLeafH T ls δ) I ⋆
          fresh (fun α => sepList (mutLeafH T ls δ α) I ─⋆ wpG ls e Φ))
        (wpG ls e Q)
  | [], Q, hQ => by
      rintro ρ ⟨ρo, ρH, hc, ⟨rfl, -⟩, γH, hH⟩
      rw [eq_of_compS_empty_left hc]
      obtain ⟨hw, -⟩ := hH (↓γH) (Life.down_sqsubset γH)
      have hwp := hw PMap.empty ρH ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH)
      exact wpG_mono (fun ls' v σ h => hQ ls' v σ
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h⟩) hwp
  | ℓ :: I, Q, hQ => by
      rintro ρ ⟨ρo, ρH, hc, ⟨ρ0, ρr, hc0, hleaf, hrest⟩, γH, hH⟩
      obtain ⟨ℓ', v, hk⟩ := hleaf
      obtain ⟨hl, c, p, hcp, hcell, hpv⟩ := pure_sep_iff.mp hk
      have hℓ : ℓ' = ℓ := by
        have := congrArg Subtype.val hl; simpa using this.symm
      subst hℓ
      -- `ρ = c ● (p ● (ρr ● ρH))`
      obtain ⟨F, hF, hρ⟩ := compS_reassoc hc0 hc
      obtain ⟨G, hG, hρ'⟩ := compS_reassoc hcp hρ
      refine wpG_M_frameX ℓ' (T ℓ') δ β (hP ℓ') v e ls Q ρ ⟨c, G, hρ', hcell, p, F, hG, hpv, ?_⟩
      -- the outer frame's lifetime `α₁`, below `@F`, `β′` and `β`
      obtain ⟨aF, haF⟩ := F.exists_atLife
      refine ⟨aF ⊓ β' ⊓ β, fun α₁ hα₁ => ⟨?_, outlives_of_atLife haF
        (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_left))⟩⟩
      have hα₁β' : α₁ ⊑ β' := le_of_lt (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_right))
      have hα₁β : α₁ ⊑ β := le_of_lt (lt_of_lt_of_le hα₁ inf_le_right)
      intro ρm ρ' hm hcm
      -- `ρ′ = ρr ● (ρH ● ρm)`
      obtain ⟨R, hR, hρ''⟩ := compS_reassoc hF hcm
      -- the remaining places, framed by the induction hypothesis
      refine wpG_M_frameList T δ β hP e ls Φ β' hΦ I _ ?_ ρ'
        ⟨ρr, R, hρ'', hrest, ?_⟩
      · -- the outer frame's postcondition from the inner ones'
        intro ls' v' σ ⟨σo, σΦ, hσ, ho, hφ⟩
        refine ⟨?_, (BoLo.outlives_comp hσ α₁).mpr
          ⟨ownList_outlives hα₁β hP ho, BoLo.Outlives.mono hα₁β' (hΦ ls' v' σΦ hφ)⟩⟩
        intro w c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp₁
        -- the returned leaf `c₁ ● p₁`, beside the rest and `Φ`
        obtain ⟨cp, hcp', hp₂⟩ := compS_reassoc hcc hcp₁
        obtain ⟨oc, hoc, hp₂'⟩ := compS_exch hσ hp₂
        exact hQ ls' v' p₂ ⟨oc, σΦ, hp₂', ⟨cp, σo, ResU.CompS.comm hoc,
          ⟨ℓ', w, pure_sep_mk rfl ⟨c₁, p₁, hcp', hc₁, hp₁⟩⟩, ho⟩, hφ⟩
      · -- the inner frames' lifetime `α₂`, below `@R`, `α₁` and the callback's bound
        obtain ⟨aR, haR⟩ := R.exists_atLife
        refine ⟨aR ⊓ α₁ ⊓ γH, fun α₂ hα₂ => ⟨?_, outlives_of_atLife haR
          (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_left))⟩⟩
        have hα₂α₁ : α₂ ⊑ α₁ :=
          le_of_lt (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_right))
        have hα₂H : α₂ ⊏ γH := lt_of_lt_of_le hα₂ inf_le_right
        intro ρm₂ ρ₃ hm₂ hcm₂
        -- the outer leaf, shortened to `α₂` (6.118), heads the family
        obtain ⟨X, hX, hρ₃⟩ := compS_reassoc hR hcm₂
        exact (hH α₂ hα₂H).1 X ρ₃ ⟨ρm, ρm₂, hX, ptoMutS_antitone hα₂α₁ hm, hm₂⟩ hρ₃

/-- **One Mut Frame per place, around one expression**: `wpG_M_frameList` at postconditions over
values.  The leaves may differ in type. -/
theorem wpTS_M_frameList (T : Loc → VTy) (δ : LSub) (β : Life)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) (e : Expr) (ls : List SRec)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (I : List Loc) (Q : List SRec → Val → WProp)
    (hQ : ∀ ls' v, Entails (sepList (ownLeafH T ls' δ) I ⋆ Φ ls' v) (Q ls' v)) :
    Entails
      (sepList (ownLeafH T ls δ) I ⋆
        fresh (fun α => sepList (mutLeafH T ls δ α) I ─⋆ wpTS ls e Φ))
      (wpTS ls e Q) := by
  rintro ρ ⟨ρo, ρH, hc, ho, γH, hH⟩
  refine (wpTS_iff_wpG ls e Q ρ).mpr (wpG_M_frameList T δ β hP e ls (valPost Φ) β'
    (fun ls t ρ ⟨v, _, hv⟩ => hΦ ls v ρ hv) I (valPost Q) ?_ ρ
    ⟨ρo, ρH, hc, ho, γH, fun α hα => ⟨fun σ₁ σ₂ hm hcm =>
      (wpTS_iff_wpG ls e Φ σ₂).mp ((hH α hα).1 σ₁ σ₂ hm hcm), (hH α hα).2⟩⟩)
  rintro ls' t σ ⟨σo, σΦ, hσ, ho', v, rfl, hφ⟩
  exact ⟨v, rfl, hQ ls' v σ ⟨σo, σΦ, hσ, ho', hφ⟩⟩

/-- A range of owned leaves is in `Res_α`. -/
theorem ownRange_outlives {T : VTy} {δ : LSub} {β α : Life} (hαβ : α ⊑ β)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) {ls : List SRec} {ℓ : Loc} {n : Nat}
    {ρ : WRes} (h : sepRange (ownLeaf T ls δ) ℓ n ρ) : BoLo.Outlives ρ α := by
  rw [sepRange_eq_sepList] at h; exact ownList_outlives (T := fun _ => T) hαβ (fun _ => hP) h

/-- **`n` Mut Frames around one expression**, the run ending at any final term: the family is an owned array's range. -/
theorem wpG_M_frameFam (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (e : Expr) (ls : List SRec)
    (Φ : List SRec → Expr → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (n : Nat) (ℓ : Loc) (Q : List SRec → Expr → WProp)
    (hQ : ∀ ls' v, Entails (sepRange (ownLeaf T ls' δ) ℓ n ⋆ Φ ls' v) (Q ls' v)) :
    Entails
      (sepRange (ownLeaf T ls δ) ℓ n ⋆
        fresh (fun α => sepRange (mutLeaf T ls δ α) ℓ n ─⋆ wpG ls e Φ))
      (wpG ls e Q) := by
  simp only [sepRange_eq_sepList] at hQ ⊢
  exact wpG_M_frameList (fun _ => T) δ β (fun _ => hP) e ls Φ β' hΦ _ Q hQ

/-- **`n` Mut Frames around one expression**: the family is an owned array's range. -/
theorem wpTS_M_frameFam (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (e : Expr) (ls : List SRec)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (n : Nat) (ℓ : Loc) (Q : List SRec → Val → WProp)
    (hQ : ∀ ls' v, Entails (sepRange (ownLeaf T ls' δ) ℓ n ⋆ Φ ls' v) (Q ls' v)) :
    Entails
      (sepRange (ownLeaf T ls δ) ℓ n ⋆
        fresh (fun α => sepRange (mutLeaf T ls δ α) ℓ n ─⋆ wpTS ls e Φ))
      (wpTS ls e Q) := by
  simp only [sepRange_eq_sepList] at hQ ⊢
  exact wpTS_M_frameList (fun _ => T) δ β (fun _ => hP) e ls Φ β' hΦ _ Q hQ

/-! ### The Imm Frame over a family of places -/

/-- An `imm` leaf at `α`, its type chosen by its place, with the record its frame made. -/
def immLeafH (T : Loc → VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp := fun m ρ =>
  (∃ r ∈ rsOf ls, r.le = m ∧ r.T = T m ∧ r.δ = δ) ∧
    ptoImmS m α ls (fun ls₀ => vC true (T m) ls₀ δ) ρ

/-- An `imm` leaf of one type. -/
abbrev immLeaf (T : VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp :=
  immLeafH (fun _ => T) ls δ α

/-- `[TR]` 6.114 (`I ⊒`) at a leaf. -/
theorem immLeaf_antitone {T : Loc → VTy} {ls : List SRec} {δ : LSub} {α β : Life} (h : β ⊑ α)
    {m : Loc} {ρ : WRes} (hl : immLeafH T ls δ α m ρ) : immLeafH T ls δ β m ρ :=
  ⟨hl.1, ptoImmS_antitone h hl.2⟩

/-- A leaf and its record are stable along `Ext`. -/
theorem immLeaf_ext {T : Loc → VTy} {ls ls' : List SRec} {δ : LSub} {α : Life} {m : Loc}
    {ρ : WRes} (hk : Ext ls ls' ρ) (hl : immLeafH T ls δ α m ρ) : immLeafH T ls' δ α m ρ := by
  obtain ⟨⟨r, hr, hle, hT, hδ⟩, s, u, σ, hs, ls₀, hρ, hP, hαs, hls₀⟩ := hl
  subst hρ
  have hcell : CellIn (ResU.single m (CellU.immOf s u σ hs)) s.meet :=
    CellIn.single (by simp)
  have hrel : Rel r (ResU.single m (CellU.immOf s u σ hs)) :=
    ⟨m, _, ResU.single_get_self _ _, CellU.kind_immOf _ _ _ _, Or.inl hle.symm⟩
  refine ⟨⟨r, hk.1 r hr hrel, hle, hT, hδ⟩, s, u, σ, hs, ls₀, rfl, hP, hαs, fun x => ?_⟩
  rw [hls₀ x]
  exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mp hx, hb⟩,
         fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mpr hx, hb⟩⟩

/-- A family of leaves stable along `Ext` is. -/
theorem sepList_ext {P : List SRec → Loc → WProp}
    (hP : ∀ ls ls' m ρ, Ext ls ls' ρ → P ls m ρ → P ls' m ρ) {ls ls' : List SRec}
    {I : List Loc} {ρ : WRes} (hk : Ext ls ls' ρ) (h : sepList (P ls) I ρ) : sepList (P ls') I ρ :=
  sepList_mono_down (R := fun σ => Ext ls ls' σ)
    (fun _ _ _ hc hk' => ⟨hk'.left hc, hk'.right hc⟩) (fun m σ hkσ hm => hP _ _ m σ hkσ hm) hk h

theorem ownList_ext {T : Loc → VTy} {δ : LSub} {ls ls' : List SRec} {I : List Loc}
    {ρ : WRes} (hk : Ext ls ls' ρ) (h : sepList (ownLeafH T ls δ) I ρ) :
    sepList (ownLeafH T ls' δ) I ρ :=
  sepList_ext (P := fun ls => ownLeafH T ls δ) (fun _ _ _ _ hk' h => vC_local true _ hk' h) hk h

/-- **One Imm Frame per place, around one expression**, the run ending at any final term.  The
leaves may differ in type. -/
theorem wpG_I_frameList (T : Loc → VTy) (δ : LSub) (β : Life)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) (hadm : ∀ m, AdmWf (T m) δ)
    (e : Expr)
    (Φ : List SRec → Expr → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (hΦext : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Φ ls₁ w ρ → Φ ls₂ w ρ) :
    ∀ (I : List Loc) (ls : List SRec),
      Entails
        (sepList (ownLeafH T ls δ) I ⋆
          fresh (fun α ρ => ∀ ls', Ext ls ls' ρ →
            (sepList (immLeafH T ls' δ α) I ─⋆ wpG ls' e Φ) ρ))
        (wpG ls e (fun ls' v => sepList (ownLeafH T ls' δ) I ⋆ Φ ls' v))
  | [], ls => by
      rintro ρ ⟨ρo, ρH, hc, ⟨rfl, -⟩, γH, hH⟩
      rw [eq_of_compS_empty_left hc]
      obtain ⟨hw, -⟩ := hH (↓γH) (Life.down_sqsubset γH)
      have hwp := hw ls (Ext.refl _ _) PMap.empty ρH ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH)
      exact wpG_mono (fun ls' v σ h =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h⟩) hwp
  | ℓ :: I, ls => by
      rintro ρ ⟨ρo, ρH, hc, ⟨ρ0, ρr, hc0, hleaf, hrest⟩, γH, hH⟩
      obtain ⟨ℓ', v, hk⟩ := hleaf
      obtain ⟨hl, c, p, hcp, hcell, hpv⟩ := pure_sep_iff.mp hk
      have hℓ : ℓ' = ℓ := by
        have := congrArg Subtype.val hl; simpa using this.symm
      subst hℓ
      obtain ⟨F, hF, hρ⟩ := compS_reassoc hc0 hc
      obtain ⟨G, hG, hρ'⟩ := compS_reassoc hcp hρ
      -- 6.64's postcondition is stable along `Ext`
      have hQext : ∀ ls₁ ls₂ w σ, Ext ls₁ ls₂ σ →
          (sepList (ownLeafH T ls₁ δ) (ℓ' :: I) ⋆ Φ ls₁ w) σ →
          (sepList (ownLeafH T ls₂ δ) (ℓ' :: I) ⋆ Φ ls₂ w) σ := by
        rintro ls₁ ls₂ w σ hk ⟨σo, σΦ, hσ, ho, hφ⟩
        exact ⟨σo, σΦ, hσ, ownList_ext (hk.left hσ) ho, hΦext _ _ _ _ (hk.right hσ) hφ⟩
      refine wpG_I_frameX ℓ' (T ℓ') δ (hadm ℓ') v e ls _ hQext ρ
        ⟨c, G, hρ', hcell, p, F, hG, hpv, ?_⟩
      obtain ⟨aF, haF⟩ := F.exists_atLife
      have houtF : ∀ α₁, α₁ ⊏ aF ⊓ β' ⊓ β → F.InStratum α₁ := fun α₁ hα₁ =>
        outlives_of_atLife haF (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_left))
      refine ⟨aF ⊓ β' ⊓ β, fun α₁ hα₁ => ⟨?_, houtF α₁ hα₁⟩⟩
      have hα₁β' : α₁ ⊑ β' := le_of_lt (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_right))
      have hα₁β : α₁ ⊑ β := le_of_lt (lt_of_lt_of_le hα₁ inf_le_right)
      intro ls₁ hadd hrec ρm ρ' hm hcm
      have hkF : Ext ls ls₁ F := ext_add hadd (houtF α₁ hα₁)
      obtain ⟨R, hR, hρ''⟩ := compS_reassoc hF hcm
      refine wpG_mono (Q' := fun ls'' v' => box α₁ (ptoOwn ℓ' v ─⋆
          (vC true (T ℓ') ls'' δ v ─⋆ (sepList (ownLeafH T ls'' δ) (ℓ' :: I) ⋆ Φ ls'' v'))))
        ?_ (wpG_I_frameList T δ β hP hadm e Φ β' hΦ hΦext I ls₁ ρ'
          ⟨ρr, R, hρ'', ownList_ext (hkF.left hF) hrest, ?_⟩)
      · -- the outer frame's postcondition from the inner ones'
        intro ls' v' σ ⟨σo, σΦ, hσ, ho, hφ⟩
        refine ⟨?_, (BoLo.outlives_comp hσ α₁).mpr
          ⟨ownList_outlives hα₁β hP ho, BoLo.Outlives.mono hα₁β' (hΦ ls' v' σΦ hφ)⟩⟩
        intro c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp₁
        obtain ⟨cp, hcp', hp₂⟩ := compS_reassoc hcc hcp₁
        obtain ⟨oc, hoc, hp₂'⟩ := compS_exch hσ hp₂
        exact ⟨oc, σΦ, hp₂', ⟨cp, σo, ResU.CompS.comm hoc,
          ⟨ℓ', v, pure_sep_mk rfl ⟨c₁, p₁, hcp', hc₁, hp₁⟩⟩, ho⟩, hφ⟩
      · -- the inner frames' lifetime `α₂`, below `@R`, `α₁` and the callback's bound
        obtain ⟨aR, haR⟩ := R.exists_atLife
        refine ⟨aR ⊓ α₁ ⊓ γH, fun α₂ hα₂ => ⟨?_, outlives_of_atLife haR
          (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_left))⟩⟩
        have hα₂α₁ : α₂ ⊑ α₁ :=
          le_of_lt (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_right))
        have hα₂H : α₂ ⊏ γH := lt_of_lt_of_le hα₂ inf_le_right
        intro ls' hext ρm₂ ρ₃ hm₂ hcm₂
        -- the callback's list is `Ext`-above the original at the outer hypothesis' resource
        have hkH : Ext ls ls' ρH := (hkF.right hF).trans (hext.left hR)
        -- the outer leaf, at `α₂` and at `ls′`, heads the family
        have hlead : immLeafH T ls' δ α₂ ℓ' ρm :=
          immLeaf_ext (hext.right hR) (immLeaf_antitone hα₂α₁ ⟨hrec, hm⟩)
        obtain ⟨X, hX, hρ₃⟩ := compS_reassoc hR hcm₂
        exact (hH α₂ hα₂H).1 ls' hkH X ρ₃ ⟨ρm, ρm₂, hX, hlead, hm₂⟩ hρ₃

/-- **One Imm Frame per place, around one expression**: `wpG_I_frameList` at postconditions over
values.  The leaves may differ in type. -/
theorem wpTS_I_frameList (T : Loc → VTy) (δ : LSub) (β : Life)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) (hadm : ∀ m, AdmWf (T m) δ)
    (e : Expr)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (hΦext : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Φ ls₁ w ρ → Φ ls₂ w ρ) (I : List Loc)
    (ls : List SRec) :
    Entails
      (sepList (ownLeafH T ls δ) I ⋆
        fresh (fun α ρ => ∀ ls', Ext ls ls' ρ →
          (sepList (immLeafH T ls' δ α) I ─⋆ wpTS ls' e Φ) ρ))
      (wpTS ls e (fun ls' v => sepList (ownLeafH T ls' δ) I ⋆ Φ ls' v)) := by
  rintro ρ ⟨ρo, ρH, hc, ho, γH, hH⟩
  refine (wpTS_iff_wpG ls e _ ρ).mpr (wpG_mono (fun ls' t σ ht => ?_)
    (wpG_I_frameList T δ β hP hadm e (valPost Φ) β' (fun ls t ρ ⟨v, _, hv⟩ => hΦ ls v ρ hv)
      (fun ls₁ ls₂ t ρ hk ⟨v, ht, hv⟩ => ⟨v, ht, hΦext ls₁ ls₂ v ρ hk hv⟩) I ls ρ
      ⟨ρo, ρH, hc, ho, γH, fun α hα => ⟨fun ls' hk σ₁ σ₂ hm hcm =>
        (wpTS_iff_wpG ls' e Φ σ₂).mp ((hH α hα).1 ls' hk σ₁ σ₂ hm hcm), (hH α hα).2⟩⟩))
  obtain ⟨σo, σΦ, hσ, ho', v, rfl, hφ⟩ := ht
  exact ⟨v, rfl, σo, σΦ, hσ, ho', hφ⟩

/-- **`n` Imm Frames around one expression**, the run ending at any final term: the family is an owned array's range. -/
theorem wpG_I_frameFam (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (hadm : AdmWf T δ) (e : Expr)
    (Φ : List SRec → Expr → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (hΦext : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Φ ls₁ w ρ → Φ ls₂ w ρ)
    (n : Nat) (ℓ : Loc) (ls : List SRec) :
    Entails
      (sepRange (ownLeaf T ls δ) ℓ n ⋆
        fresh (fun α ρ => ∀ ls', Ext ls ls' ρ →
          (sepRange (immLeaf T ls' δ α) ℓ n ─⋆ wpG ls' e Φ) ρ))
      (wpG ls e (fun ls' v => sepRange (ownLeaf T ls' δ) ℓ n ⋆ Φ ls' v)) := by
  simp only [sepRange_eq_sepList]
  exact wpG_I_frameList (fun _ => T) δ β (fun _ => hP) (fun _ => hadm) e Φ β' hΦ hΦext _ ls

/-- **`n` Imm Frames around one expression**: the family is an owned array's range. -/
theorem wpTS_I_frameFam (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (hadm : AdmWf T δ) (e : Expr)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (hΦext : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Φ ls₁ w ρ → Φ ls₂ w ρ)
    (n : Nat) (ℓ : Loc) (ls : List SRec) :
    Entails
      (sepRange (ownLeaf T ls δ) ℓ n ⋆
        fresh (fun α ρ => ∀ ls', Ext ls ls' ρ →
          (sepRange (immLeaf T ls' δ α) ℓ n ─⋆ wpTS ls' e Φ) ρ))
      (wpTS ls e (fun ls' v => sepRange (ownLeaf T ls' δ) ℓ n ⋆ Φ ls' v)) := by
  simp only [sepRange_eq_sepList]
  exact wpTS_I_frameList (fun _ => T) δ β (fun _ => hP) (fun _ => hadm) e Φ β' hΦ hΦext _ ls

/-! ### Splitting a family -/

theorem uint32_sub_toNat {n i : UInt32} (hi : i ≤ n) : (n - i).toNat = n.toNat - i.toNat :=
  UInt32.toNat_sub_of_le n i hi

/-- **K3's content**: a family splits at a run-time index `i ≤ n`, at every leaf. -/
theorem vP_fam_split {L : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc} {n i : UInt32}
    {ρ : WRes} (hv : vP (.fam L) ls δ (Val.arr ℓ n) ρ) (hi : i ≤ n) :
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vP (.fam L) ls δ (Val.arr ℓ i) ρ₁ ∧
      vP (.fam L) ls δ (Val.arr (ℓ + i.toNat) (n - i)) ρ₂ := by
  obtain ⟨ℓ', n', he, hn, hs⟩ := vP_fam_iff.mp hv
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  have hin : i.toNat ≤ n.toNat := UInt32.le_iff_toNat_le.mp hi
  rw [show n.toNat = i.toNat + (n.toNat - i.toNat) by omega] at hs
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := sepRange_split hs
  refine ⟨ρ₁, ρ₂, hc, vP_fam_mk (by omega) h₁, vP_fam_mk (by rw [uint32_sub_toNat hi]; omega) ?_⟩
  rwa [uint32_sub_toNat hi]

/-- Two adjacent families at the same leaves are one. -/
theorem vP_fam_join {L : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc} {i k : UInt32}
    {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (h₁ : vP (.fam L) ls δ (Val.arr ℓ i) ρ₁)
    (h₂ : vP (.fam L) ls δ (Val.arr (ℓ + i.toNat) k) ρ₂)
    (hik : i.toNat + k.toNat < 2 ^ 31) :
    vP (.fam L) ls δ (Val.arr ℓ (i + k)) ρ := by
  obtain ⟨ℓ₁, n₁, he₁, -, hs₁⟩ := vP_fam_iff.mp h₁
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he₁
  obtain ⟨ℓ₂, n₂, he₂, -, hs₂⟩ := vP_fam_iff.mp h₂
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he₂
  have hsum : (i + k).toNat = i.toNat + k.toNat := by
    rw [UInt32.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  refine vP_fam_mk (by omega) ?_
  rw [hsum]
  exact sepRange_append hc hs₁ hs₂

/-- **Any partition of a finite index set** splits the family. -/
theorem sepList_partition {P : Loc → WProp} (p : Loc → Bool) (I : List Loc) {ρ : WRes}
    (h : sepList P I ρ) : (sepList P (I.filter p) ⋆ sepList P (I.filter (fun m => !p m))) ρ :=
  (sepList_append _ _ ρ).mp (sepList_perm (List.filter_append_perm p I).symm ρ h)

/-- The parts of a partition compose back. -/
theorem sepList_unpartition {P : Loc → WProp} (p : Loc → Bool) (I : List Loc) {ρ : WRes}
    (h : (sepList P (I.filter p) ⋆ sepList P (I.filter (fun m => !p m))) ρ) : sepList P I ρ :=
  sepList_perm (List.filter_append_perm p I) ρ ((sepList_append _ _ ρ).mpr h)

end BoCa.Fig16.LogRel.Core

end
