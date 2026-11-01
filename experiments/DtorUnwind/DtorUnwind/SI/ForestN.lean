import DtorUnwind.SI.StopFrameN
import DtorUnwind.SI.RebResumeN

/-!
# Spike #770: one stack of frame records per suspended computation

**New design, not a transcription.** `TW` (`Core/World.lean`) and `TI` (`Core/Invariant.lean`)
read their record lists only through membership (`immEnd` removes any member, not the head), and
every `TI` invariant is stated per record lineage (`LeInv`, `NestLife`, `ChainInv`, `NoMut`,
`Coverage`). The record lists are already sets. The single-stack reading sits elsewhere:

1. `TW.reb`'s `StratumLe W β`, `TW.rebDeep`'s and `TW.rebEnd`'s `W.InStratum β`: premises over
   every lifetime of the whole world, read in `frameLife_reb_like` and `ti_endReb`. `TWN`
   (`SI/TWN.lean`) already reads them per record lineage.
2. `Ext`'s second clause (`Core/FrameRecords.lean`): every tag longer than a borrow cell of the
   share is kept. It compares the share's cells with every tag of the one list, by lifetime.
3. `wpTS`/`rwpG`'s post-configuration: the records and tags a run ends at are the ones it began
   at, and `ρ ↭ π`. A run that stops is accounted as one that returns.
4. `OpEntN.wc = sameW` (`SI/StopFrameN.lean`), forced by 2 once 3 has folded the lend.

## What this file adds

* `not_extFoldTransfer`: the precise reason for `sameW`. `Ext` at the folded share (`ℓ ↦ own`)
  does not give `Ext` at the share the continuation really holds (`ℓ ↦ mut(A, …)`): a tag
  longer than `A` can be added.
* `Stack`, `TFof`: a forest world is one typed world over the records of every stack, each stack
  tagged on its own. With one stack it is exactly the given typed world and tagging
  (`tfOf_single`). Round 7's configuration is a forest world (`round7_forest`).
* `ExtK A`: `Ext` at the share a continuation carries with its stack's lend at `A`
  (`extK_iff_ext_cell`: exactly `Ext` at the share with the `mut` cell at `A` added).
* `erwp_M_frameK`: `erwp_M_frame` with `wc = ExtK B`, `B ⊑ A`, in place of `sameW`.
* `extK_add`: a resumer that opens a frame of its own at a lifetime `α ⊑ A` and resumes inside
  it meets `ExtK A`, and `sameW` fails there (`not_sameW_add`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### Site 2: `Ext` read at a folded share -/

/-- `Ext` at a folded cell `ℓ ↦ own(v)` gives `Ext` at the cell `ℓ ↦ mut(A, v, ∅, ⊤)` it folds:
the step `erwp_M_frame` would need with `wc = Ext` in place of `sameW`. -/
def ExtFoldTransfer : Prop :=
  ∀ (ls ls' : List SRec) (l : Loc) (A : Life) (v : Val),
    Ext ls ls' (ResU.single l (CellU.ownOf v)) → Ext ls ls' (ResU.single l (shortCell A v))

/-- A record, for the configurations below. -/
def rec₀ : FrameRec := ⟨0, Val.unit, PMap.empty, .unit, ⟨[]⟩⟩

theorem ext_single_own (ls ls' : List SRec) (l : Loc) (v : Val) :
    Ext ls ls' (ResU.single l (CellU.ownOf v)) := by
  refine ⟨fun r _ ⟨m, ψ, e, k, _⟩ => ?_, fun b ⟨m, ψ, e, k, _⟩ => ?_⟩
  · obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
    simp at k
  · obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
    simp at k

/-- **Refuted.** At `ls = []`, `ls′ = [(r₀, 0)]` and `A = 1` (shorter than `0`), the folded share
has no borrow cell, so `Ext` holds; the carried share has the cell at `A`, and the added tag is
longer than `A`. -/
theorem not_extFoldTransfer : ¬ ExtFoldTransfer := by
  intro h
  have hx := (h [] [(rec₀, OrderDual.toDual 0)] 0 (OrderDual.toDual 1) Val.unit
    (ext_single_own _ _ _ _)).2 (OrderDual.toDual 1)
    ⟨0, _, ResU.single_get_self _ _, fun c => Kind.noConfusion c, le_refl (OrderDual.toDual 1 : Life)⟩
    (rec₀, OrderDual.toDual 0) (show (OrderDual.toDual 1 : Life) < OrderDual.toDual 0 from by
      show (0 : ℕ) < 1; omega)
  simp at hx

/-! ### The forest world -/

/-- A stack: the records proper and tags of one computation, running or stored in a
continuation, and the lifetimes of the `mut` lends it holds open. -/
structure Stack where
  ps : List FrameRec
  ls : List SRec
  lends : List Life

/-- Every stack's records proper. -/
def Forest.ps (F : List Stack) : List FrameRec := F.flatMap Stack.ps

/-- Every stack's tags. -/
def Forest.ls (F : List Stack) : List SRec := F.flatMap Stack.ls

/-- **The forest world over a typed-world family.** One typed world over the records of every
stack, the shared world `W` and its aggregate `ag(W)`; each stack tagged on its own. -/
def TFof (Typed : WRes → List FrameRec → List FrameRec → Prop) (W : WRes) (F : List Stack) :
    Prop :=
  Typed W (Forest.ps F) (rsOf (Forest.ls F)) ∧ ∀ s ∈ F, Tagged W s.ps s.ls

/-- **Conservativity.** One stack is the given typed world and its tagging, for every family:
`TW`, `TWN`, `TWNC`. -/
theorem tfOf_single (Typed : WRes → List FrameRec → List FrameRec → Prop) (W : WRes)
    (ps : List FrameRec) (ls : List SRec) (lends : List Life) :
    TFof Typed W [⟨ps, ls, lends⟩] ↔ Typed W ps (rsOf ls) ∧ Tagged W ps ls := by
  simp [TFof, Forest.ps, Forest.ls]

theorem tfOf_single_tw (W : WRes) (ps : List FrameRec) (ls : List SRec) :
    TFof TW W [⟨ps, ls, []⟩] ↔ TW W ps (rsOf ls) ∧ Tagged W ps ls :=
  tfOf_single TW W ps ls []

theorem tfOf_single_twnc (W : WRes) (ps : List FrameRec) (ls : List SRec) :
    TFof TWNC W [⟨ps, ls, []⟩] ↔ TWNC W ps (rsOf ls) ∧ Tagged W ps ls :=
  tfOf_single TWNC W ps ls []

/-- Per-stack tags tag the union. -/
theorem tagged_forest {W : WRes} {F : List Stack} (h : ∀ s ∈ F, Tagged W s.ps s.ls) :
    Tagged W (Forest.ps F) (Forest.ls F) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := List.mem_flatMap.mp hx
  obtain ⟨p, hp, hd, hf⟩ := h s hs x hxs
  exact ⟨p, List.mem_flatMap.mpr ⟨s, hs, hp⟩, hd, hf⟩

/-- **Round 7's configuration is a forest world.** From a typed, tagged world: the
continuation's stack at its records and tags, and the handler's stack holding its own lend at any
`A′`, over the world with the handler's cell `ℓ ↦ mut(A′, v, ∅, ⊤)`, which is in no `Res_{A′}`. -/
theorem round7_forest {W : WRes} {ps : List FrameRec} {ls : List SRec} {μ : Heap} {l : Loc}
    (hT : TWN W ps (rsOf ls)) (htg : Tagged W ps ls) (hL : ResU.Lower W μ) (hμ : μ l = none)
    (v : Val) (A' : Life) (lendsκ : List Life) :
    ∃ W', ResU.CompS W (ResU.single l (shortCell A' v)) W' ∧
      TFof TWN W' [⟨ps, ls, lendsκ⟩, ⟨[], [], [A']⟩] ∧ ¬ W'.InStratum A' := by
  obtain ⟨W', hc, hT', htg', -, hA⟩ := resume_frame_short hT htg hL hμ v A'
  refine ⟨W', hc, ⟨by simpa [Forest.ps, Forest.ls] using hT', fun s hs => ?_⟩, hA⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact htg'
  · intro x hx; cases hx

/-! ### `Ext` at the stack a continuation carries -/

/-- **`Ext` at a continuation's stack**: `Ext` at the share, and every tag longer than the
stack's `mut` lend at `A` kept. -/
def ExtK (A : Life) : List SRec → List SRec → WRes → Prop := fun ls ls' ρ =>
  Ext ls ls' ρ ∧ ∀ x : SRec, x.2 ⊐ A → (x ∈ ls ↔ x ∈ ls')

/-- `ExtK` over a stack: one clause per open lend. -/
def ExtS (s : Stack) : List SRec → List SRec → WRes → Prop := fun ls ls' ρ =>
  Ext ls ls' ρ ∧ ∀ A ∈ s.lends, ∀ x : SRec, x.2 ⊐ A → (x ∈ ls ↔ x ∈ ls')

theorem extS_single (A : Life) (ls ls' : List SRec) (ρ : WRes) :
    ExtS ⟨[], [], [A]⟩ ls ls' ρ ↔ ExtK A ls ls' ρ := by
  simp [ExtS, ExtK]

theorem extK_of_same {A : Life} {ls ls' : List SRec} (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (ρ : WRes) :
    ExtK A ls ls' ρ :=
  ⟨ext_of_same h ρ, fun x _ => (h x).symm⟩

theorem extK_left {A : Life} : ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
    ExtK A ls ls' ρ → ExtK A ls ls' ρ₁ :=
  fun _ _ _ _ _ hc h => ⟨h.1.left hc, h.2⟩

/-- A shorter stack lifetime asks more. -/
theorem extK_mono {A B : Life} (hBA : B ⊑ A) {ls ls' : List SRec} {ρ : WRes}
    (h : ExtK B ls ls' ρ) : ExtK A ls ls' ρ :=
  ⟨h.1, fun x hx => h.2 x (lt_of_le_of_lt hBA hx)⟩

/-- **`ExtK A` is `Ext` at the carried share.** At a share `ρ` missing `ℓ`, `ExtK A` is `Ext` at
`ρ ● ℓ ↦ mut(A, v, ∅, ⊤)`: the continuation's share with its stack's lend. -/
theorem extK_iff_ext_cell {A : Life} {ls ls' : List SRec} {ρ ρ' : WRes} {l : Loc} {v : Val}
    (hl : ρ.get l = none) (hc : ResU.CompS ρ (ResU.single l (shortCell A v)) ρ') :
    ExtK A ls ls' ρ ↔ Ext ls ls' ρ' := by
  have hk : (shortCell A v).kind ≠ Kind.imm := by
    exact fun c => Kind.noConfusion c
  have hl' : ρ'.get l = some (shortCell A v) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc) (ResU.single_get_self _ _) hk).2
  have hne : ∀ m, m ≠ l → ρ'.get m = ρ.get m := fun m hm =>
    ResU.Comp.get_of_right_none hc (ResU.single_get_ne _ hm)
  constructor
  · rintro ⟨⟨hK, hC⟩, hA⟩
    refine ⟨fun r hr ⟨m, ψ, e, k, hm⟩ => ?_, fun b ⟨m, ψ, e, k, hb⟩ x hx => ?_⟩
    · by_cases hml : m = l
      · subst hml; rw [hl'] at e; cases Option.some.inj e
        exact absurd k hk
      · exact hK r hr ⟨m, ψ, (hne m hml) ▸ e, k, hm⟩
    · by_cases hml : m = l
      · subst hml; rw [hl'] at e; cases Option.some.inj e
        exact hA x (lt_of_le_of_lt hb hx)
      · exact hC b ⟨m, ψ, (hne m hml) ▸ e, k, hb⟩ x hx
  · intro h
    refine ⟨h.left hc, fun x hx => h.2 A ⟨l, _, hl', fun c => Kind.noConfusion c, le_refl A⟩ x hx⟩

/-- **A resumer's own frame.** Adding tags at a lifetime `α ⊑ A`, at a share in `Res_α`, is
`ExtK A`: a handler that opens a frame of its own below the continuation's lend and resumes
inside it. -/
theorem extK_add {A α : Life} (hαA : α ⊑ A) {ls ls' : List SRec} (h : AddAt ls ls' α)
    {ρ : WRes} (hρ : ρ.InStratum α) : ExtK A ls ls' ρ := by
  refine ⟨ext_add h hρ, fun x hx => ⟨h.1 x, fun h' => ?_⟩⟩
  by_contra hn
  have e := h.2 x h' hn
  rw [e] at hx
  exact absurd (lt_of_le_of_lt hαA hx) (lt_irrefl _)

/-- …where `sameW` fails as soon as a tag is added. -/
theorem not_sameW_add {ls ls' : List SRec} {x : SRec} (hx : x ∈ ls') (hn : x ∉ ls) (ρ : WRes) :
    ¬ sameW ls ls' ρ := fun h => hn ((h x).mp hx)

/-! ### The Mut Frame across stops at `ExtK` -/

/-- **The carried stack's `ExtK` passes from the lender's share to the borrowed continuation's.**
The borrowed share `ρk` is part of `Z`, whose cell at `ℓ` is the lend at `A`; the lender's share
is `Z/ℓ ● W″`. A borrow cell of `ρk` other than `ℓ` is one of the lender's share; the one at `ℓ`
is at `A`, where `ExtK B`, `B ⊑ A`, keeps every longer tag. -/
theorem extK_unfold {A B : Life} (hBA : B ⊑ A) {ls ls' : List SRec} {ρk ρp Z ρkL W'' : WRes}
    {l : Loc} {ψ : CellU Loc Val} (hZ : ResU.CompS ρk ρp Z) (hZl : Z.get l = some ψ)
    (hψ : ψ.kind ≠ Kind.imm) (hat : ψ.at = A) (hkL : ResU.CompS (Z.del l) W'' ρkL)
    (h : ExtK B ls ls' ρkL) : ExtK B ls ls' ρk := by
  refine ⟨⟨fun r hr hrel => ?_, fun b hb x hx => ?_⟩, h.2⟩
  · obtain ⟨m, φ, e, k, hm⟩ := hrel.of_compS_left hZ
    have hml : m ≠ l := by rintro rfl; rw [hZl] at e; cases Option.some.inj e; exact hψ k
    exact h.1.1 r hr (Rel.of_compS_left hkL ⟨m, φ, by rw [ResU.del_get_ne _ hml]; exact e, k, hm⟩)
  · obtain ⟨m, φ, e, k, hm⟩ := hb.of_left hZ
    by_cases hml : m = l
    · subst hml; rw [hZl] at e; cases Option.some.inj e
      exact h.2 x (lt_of_le_of_lt (hBA.trans (hat ▸ hm)) hx)
    · exact h.1.2 b (CellIn.of_left hkL ⟨m, φ, by rw [ResU.del_get_ne _ hml]; exact e, k, hm⟩) x hx

/-- `LendOK` with the continuation's world condition `ExtK B` at some `B ⊑ A`, in place of
`sameW`. -/
structure OpTabN.LendOKK (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin ∧
    ∃ B, B ⊑ A ∧ en.wc = ExtK B
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

/-- **Mut Frame at `erwp`, across stops, with the continuation resumed at `ExtK`.**
`erwp_M_frame`'s proof, with the one step that read `sameW` (the borrowed continuation's world
condition from the lender's) taken by `extK_unfold`. -/
theorem erwp_M_frameK {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOKK A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwp_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, B, hBA, hwc⟩ := hT.entry m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc ρa ρk ρp X).mpr ⟨ρ', hcak, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Z.del l) W'' Y).mpr ⟨_, hD, hY⟩
    have hdZd : (Z.del l).InStratum (↓A) :=
      ResU.CompS.inStratum_left hZd (ResU.CompS.inStratum_right haZ hdX)
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hdB : ρbB.InStratum (↓A) :=
      inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
    refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
      (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
    -- the borrowed continuation's world condition, from the lender's: `extK_unfold`
    have he' : en.wc ls' ls'' ρk := by
      rw [hwc] at he ⊢
      exact extK_unfold hBA hZ hZl hkm'' (by simp) hkL he
    obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
    obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
        ⟨s1, ResU.CompS.comm hs1, hZds1⟩
    obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
    obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
    obtain ⟨Xk, hXk, hXkp⟩ := (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
    have hc := (hcont ls'' he').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkp hnoρp hc
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end
