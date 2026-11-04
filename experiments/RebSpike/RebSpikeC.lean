import RebSpike

/-!
# Spike (#791, second): each record carries its own template

Throwaway. `RebSpike.lean` showed `twp`'s start world carries an arbitrary global template choice
`w.tc`, and at `tc0` the open lend `recE ℓ m` admits no reborrow (`no_reb_tc0`). Here the choice
is per record, and fixed by the rule that opens the lend:

* **`RecC`**: a record (`FrameRecT`) and its template `C`, a typed image of the escrow
  (`TmplSpecT`), fixed by `TWC.immFrame` (for the record and every lineage member it adds).
* **`RecRRC`**: `RecRR`, and the template re-read (`RR`).
* **`TWC`**: `TWNT`'s constructors over `RecC` lists, with no choice index. `reb`'s image is the
  record's own template re-taken at `β` (`canonC r β = relResT r.R β r.C`). `immEnd` keeps the
  surviving records' templates. `reread` re-reads every record with its template.
  `rebDeep`/`rebEndDeep` are left out: a chain view's template needs its own per-record field
  (not designed here).

What is shown:

* `TWC.inv`: every `TWC` world satisfies `TIT` at its records' bases, by the library's `tit_*`
  lemmas unchanged (`TWNT.inv` never reads the canonicity premise).
* `TWC.tmpl`: every record's template is a typed image, at every world (kept by re-reading,
  `tmplSpec_rr`).
* `reb_anyStart`: at **every** `TWC` world holding the open lend of `recE ℓ m`, the reborrow
  at `β` applies with image `m ↦ imm({β}, (), ∅)`; the template premises are discharged from the
  record alone. `config_C_tc0`: at `config_tc0`'s world `⟨P, Θ, tc0⟩` the lend meets the new
  record invariant and so does the reborrowed world.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp.RebSpike
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp

variable {K K' : WCactus}

/-! ### Records with their templates -/

/-- A record and its template. -/
structure RecC (K : WCactus) where
  b : FrameRecT K
  C : TRes K

/-- The records of a list, without templates. -/
abbrev bs (rs : List (RecC K)) : List (FrameRecT K) := rs.map RecC.b

/-- A record re-read with its template. -/
def RecRRC (Θ' : CodeTy) (r : RecC K) (r' : RecC K') : Prop :=
  RecRR Θ' r.b r'.b ∧ RR (sem Θ') r.C r'.C

/-- **The canonical image of a record at `β`**: its own template re-taken at `β`. -/
def canonC (r : RecC K) (β : Life) : TRes K := relResT r.b.R β r.C

/-- The template is a typed image of the escrow. -/
abbrev TmplOK (Θ : CodeTy) (r : RecC K) : Prop := TmplSpecT K Θ r.b.R r.b.T r.b.v r.C

/-! ### The typed world with per-record templates -/

/-- **`TWNT` with each record's template in the record.** No choice index. -/
inductive TWC : (K : WCactus) → CodeTy → TRes K → List (RecC K) → List (RecC K) → Prop
  | empty {K : WCactus} {Θ : CodeTy} : TWC K Θ PMap.empty [] []
  | alloc {K : WCactus} {Θ : CodeTy} {W W' : TRes K} {ps rs : List (RecC K)}
      {μ : BoCa.Loc → Option BoCa.Val} {l : BoCa.Loc} {v : BoCa.Val} :
      TWC K Θ W ps rs → ResUT.Lower W μ → μ l = none →
      ResUT.CompS W (ResUT.single l (CellUT.ownOf v)) W' → ResUT.Valid W' → TWC K Θ W' ps rs
  /-- The opening rule fixes the template of the record and of each lineage member it adds. -/
  | immFrame {K : WCactus} {Θ : CodeTy} {W X Z R W' C : TRes K} {ps rs ds : List (RecC K)}
      {l : BoCa.Loc} {v : BoCa.Val} {α : Life} (T : KTy) (h : R.InStratum (TSet.single α)) :
      TWC K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X →
      ResUT.CompS X Z W → (T.interp Θ).P K v R →
      ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W' →
      ResUT.Valid W' → (∀ d, d ∈ bs ds ↔ DescT ⟨l, v, R, T⟩ d) →
      TmplSpecT K Θ R T v C → (∀ d ∈ ds, TmplOK Θ d) →
      TWC K Θ W' (⟨⟨l, v, R, T⟩, C⟩ :: ps) (⟨⟨l, v, R, T⟩, C⟩ :: (ds ++ rs))
  /-- The image is the record's own template re-taken at `β`. -/
  | reb {K : WCactus} {Θ : CodeTy} {W W' c : TRes K} {ps rs : List (RecC K)}
      (r : RecC K) {le : BoCa.Loc} {s : TSet} {β : Life} {hs : r.b.R.InStratum s} :
      TWC K Θ W ps rs → r ∈ rs → W.get le = some (CellUT.immOf s r.b.v r.b.R hs) →
      ResUT.Reb β r.b.R c → ((r.b.T.immReborrow β).interp Θ).P K r.b.v c →
      RebRecLeT K W (bs ps) r.b.R β → c = canonC r β → ResUT.CompS W c W' → ResUT.Valid W' →
      TWC K Θ W' ps rs
  | mutFold {K : WCactus} {Θ : CodeTy} {W X Z ρ W' : TRes K} {ps rs : List (RecC K)}
      {l : BoCa.Loc} {v : BoCa.Val} {b : TSet} [Fact (K.Anti b)] {hstr : ρ.InStratum b}
      {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρ, hstr⟩} :
      TWC K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X →
      ResUT.CompS X Z W → ResUT.CompS (ResUT.single l (CellUT.mutOf b v ρ hstr P hw)) Z W' →
      ResUT.Valid W' → TWC K Θ W' ps rs
  | mutUnfold {K : WCactus} {Θ : CodeTy} {W X Z ρ W' : TRes K} {ps rs : List (RecC K)}
      {l : BoCa.Loc} {v : BoCa.Val} {b : TSet} [Fact (K.Anti b)] {hstr : ρ.InStratum b}
      {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρ, hstr⟩} :
      TWC K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.mutOf b v ρ hstr P hw)) Z W →
      ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X → ResUT.CompS X Z W' →
      ResUT.Valid W' → TWC K Θ W' ps rs
  | free {K : WCactus} {Θ : CodeTy} {W W' : TRes K} {ps rs : List (RecC K)} {l : BoCa.Loc}
      {v : BoCa.Val} :
      TWC K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v)) W' W →
      ResUT.Valid W' → TWC K Θ W' ps rs
  | store {K : WCactus} {Θ : CodeTy} {W Z W' : TRes K} {ps rs : List (RecC K)}
      {l : BoCa.Loc} {v₁ v₂ : BoCa.Val} :
      TWC K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v₁)) Z W →
      ResUT.CompS (ResUT.single l (CellUT.ownOf v₂)) Z W' → ResUT.Valid W' →
      TWC K Θ W' ps rs
  /-- The surviving records keep their templates. -/
  | immEnd {K : WCactus} {Θ : CodeTy} {W Y X' W' : TRes K} {ps rs ps' rs' : List (RecC K)}
      (r : RecC K) {s : TSet} {hs : r.b.R.InStratum s} :
      TWC K Θ W ps rs → r ∈ ps →
      ResUT.CompS (ResUT.single r.b.le (CellUT.immOf s r.b.v r.b.R hs)) Y W →
      ResUT.CompS (ResUT.single r.b.le (CellUT.ownOf r.b.v)) r.b.R X' → ResUT.CompS X' Y W' →
      ResUT.Valid W' → (∀ x, x ∈ bs ps' ↔ (x ∈ bs ps ∧ x ≠ r.b)) →
      (∀ d, d ∈ bs rs' ↔ ∃ p ∈ bs ps', DescRT p d) → (∀ q ∈ ps', q ∈ ps) →
      (∀ q ∈ rs', q ∈ rs) → TWC K Θ W' ps' rs'
  | rebEnd {K : WCactus} {Θ : CodeTy} {W W' c : TRes K} {ps rs : List (RecC K)}
      (r : RecC K) {le : BoCa.Loc} {s : TSet} {β : Life} {hs : r.b.R.InStratum s} :
      TWC K Θ W ps rs → r ∈ rs → W'.get le = some (CellUT.immOf s r.b.v r.b.R hs) →
      ResUT.Reb β r.b.R c → ResUT.CompS W' (c.restrictDom r.b.R.exclPart) W →
      RebEndRecT K W' (bs rs) r.b.R β → TWC K Θ W' ps rs
  /-- The tree grows: the world and every record, template included, re-read. -/
  | reread {K K' : WCactus} {Θ Θ' : CodeTy} {W : TRes K} {W' : TRes K'}
      {ps rs : List (RecC K)} {ps' rs' : List (RecC K')} :
      TWC K Θ W ps rs → K.Ext K' → AgreeOn Θ Θ' W → RR (sem Θ') W W' →
      List.Forall₂ (RecRRC Θ') ps ps' → List.Forall₂ (RecRRC Θ') rs rs' →
      TWC K' Θ' W' ps' rs'

theorem forall₂_map {α β α' β' : Type} {R : α → β → Prop} {S : α' → β' → Prop} {f : α → α'}
    {g : β → β'} (hfg : ∀ a b, R a b → S (f a) (g b)) {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : List.Forall₂ S (xs.map f) (ys.map g) := by
  induction h with
  | nil => exact .nil
  | cons hxy _ ih => exact .cons (hfg _ _ hxy) ih

theorem TWC.valid {K : WCactus} {Θ : CodeTy} {W : TRes K} {ps rs : List (RecC K)}
    (h : TWC K Θ W ps rs) : ResUT.Valid W := by
  induction h with
  | empty => exact ⟨PMap.empty, ⟨PMap.empty, PMap.empty, exW_empty, agW_empty,
      G.comp_empty_right _⟩⟩
  | alloc _ _ _ _ hv _ => exact hv
  | immFrame _ _ _ _ _ _ _ hv _ _ _ _ => exact hv
  | reb _ _ _ _ _ _ _ _ _ hv _ => exact hv
  | mutFold _ _ _ _ hv _ => exact hv
  | mutUnfold _ _ _ _ hv _ => exact hv
  | free _ _ hv _ => exact hv
  | store _ _ _ hv _ => exact hv
  | immEnd _ _ _ _ _ _ hv _ _ _ _ _ => exact hv
  | rebEnd _ _ _ _ _ hW _ ih => exact (ResUT.Valid.split hW ih).1
  | reread _ _ _ hr _ _ ih => exact WitRel.ResUT.Valid.sim ih hr.rsim

/-! ### The invariant: the library's, at the bases -/

theorem mem_bs {rs : List (RecC K)} {r : RecC K} (h : r ∈ rs) : r.b ∈ bs rs :=
  List.mem_map_of_mem h

/-- **Every `TWC` world satisfies `TIT` at its records' bases**: `TWNT.inv`'s induction, each case
by the same `tit_*` lemma. -/
theorem TWC.inv {K : WCactus} {Θ : CodeTy} {W : TRes K} {ps rs : List (RecC K)}
    (h : TWC K Θ W ps rs) : TIT K Θ W (bs ps) (bs rs) := by
  induction h with
  | empty => exact tit_empty _
  | alloc _ _ _ hW _ ih => exact tit_alloc hW ih
  | @immFrame K Θ W X Z R W' C ps rs ds l v α T hα hW₀ hX hW hden hW' hv hds _ _ ih =>
      have := tit_frame (ds := bs ds) hW₀.valid hX hW hden hW' hv hds ih
      simpa [bs, List.map_append] using this
  | reb r hW₀ hr hle hreb hden _ _ hW hv ih =>
      exact tit_reb (r₀ := r.b) hW₀.valid (mem_bs hr) hle hreb hden hW hv ih
  | mutFold hW₀ hX hW hW' _ ih => exact tit_mutFold hW₀.valid hX hW hW' ih
  | mutUnfold _ hW hX hW' _ ih => exact tit_mutUnfold hW hX hW' ih
  | free _ hW _ ih => exact tit_free hW ih
  | store _ hW hW' _ ih => exact tit_store hW hW' ih
  | immEnd r hW₀ hr hc hX' hW' hv hps hrs _ _ ih =>
      exact tit_end (r := r.b) hW₀.valid (mem_bs hr) hc hX' hW' hv hps hrs ih
  | rebEnd r hW₀ hr hle hreb hW hβ ih =>
      exact tit_endReb hW₀.valid hle hreb hW hβ
        (fun r' hr' u hu => ih.2.2.2.1 r' hr' r.b (mem_bs hr) u hu) ih
  | reread hT hE hag hW hps hrs ih =>
      exact tit_reread hT.valid hE hag hW (forall₂_map (fun _ _ h => h.1) hps)
        (forall₂_map (fun _ _ h => h.1) hrs) ih

/-! ### Every template is a typed image -/

/-- **A typed image re-read is a typed image** of the re-read escrow: `TIT`'s `JointAt` case of
`tit_reread`, at the given re-reading of the image. -/
theorem tmplSpec_rr {Θ Θ' : CodeTy} (hE : K.Ext K') {R c : TRes K} {R' c' : TRes K'} {T : KTy}
    {v : BoCa.Val} (h : TmplSpecT K Θ R T v c) (hcR : CovR (sem Θ) K R) (hag : AgreeOn Θ Θ' R)
    (hR : RR (sem Θ') R R') (hc : RR (sem Θ') c c') : TmplSpecT K' Θ' R' T v c' := by
  obtain ⟨β, hreb, hP, ⟨A, hA⟩, -⟩ := h
  obtain ⟨hcc, hcag⟩ := reb_cov_agree hreb hcR hag
  obtain ⟨A', hA', -⟩ := walk_fwd hc hA
  exact ⟨β, reb_rr hE hreb hcR hag hR hc, interp_retype _ hE v _ _ hcc hc hcag hP, ⟨A', hA'⟩,
    hc.cov⟩

theorem forall₂_mem_rightC {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y :=
  forall₂_mem_right h hy

/-- **Every record's template is a typed image of its escrow**, at every `TWC` world. -/
theorem TWC.tmpl {K : WCactus} {Θ : CodeTy} {W : TRes K} {ps rs : List (RecC K)}
    (h : TWC K Θ W ps rs) : (∀ r ∈ ps, TmplOK Θ r) ∧ (∀ r ∈ rs, TmplOK Θ r) := by
  induction h with
  | empty => exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | alloc _ _ _ _ _ ih => exact ih
  | immFrame T hα _ _ _ _ _ _ _ hC hds ih =>
      refine ⟨fun r hr => ?_, fun r hr => ?_⟩
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact hC
        · exact ih.1 r hr
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact hC
        · rcases List.mem_append.mp hr with hr | hr
          · exact hds r hr
          · exact ih.2 r hr
  | reb _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | mutFold _ _ _ _ _ ih => exact ih
  | mutUnfold _ _ _ _ _ ih => exact ih
  | free _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | immEnd _ _ _ _ _ _ _ _ _ hps' hrs' ih =>
      exact ⟨fun r hr => ih.1 r (hps' r hr), fun r hr => ih.2 r (hrs' r hr)⟩
  | rebEnd _ _ _ _ _ _ _ ih => exact ih
  | @reread K K' Θ Θ' W W' ps rs ps' rs' hT hE hag hW hps hrs ih =>
      have hTI := hT.inv
      have hv := hT.valid
      have hps_rs : ∀ r ∈ ps, r.b ∈ bs rs := fun r hr =>
        (hTI.2.2.2.2.2.2.1 r.b).mpr ⟨r.b, mem_bs hr, [], .nil _⟩
      have key : ∀ r : RecC K, r.b ∈ bs rs → TmplOK Θ r → ∀ r' : RecC K', RecRRC Θ' r r' →
          TmplOK Θ' r' := by
        intro r hrb hok r' hrr
        obtain ⟨hle, hv', hT', hR⟩ := hrr.1
        have hcR : CovR (sem Θ) K r.b.R := interp_cov r.b.T (hTI.1.2.2.2.1 r.b hrb)
        have hagR : AgreeOn Θ Θ' r.b.R := hTI.agree_recs hv hag hrb
        have := tmplSpec_rr hE hok hcR hagR hR hrr.2
        unfold TmplOK; rw [hv', hT']; exact this
      refine ⟨fun r' hr' => ?_, fun r' hr' => ?_⟩
      · obtain ⟨r, hr, hrr⟩ := forall₂_mem_right hps hr'
        exact key r (hps_rs r hr) (ih.1 r hr) r' hrr
      · obtain ⟨r, hr, hrr⟩ := forall₂_mem_right hrs hr'
        exact key r (mem_bs hr) (ih.2 r hr) r' hrr

/-! ### The open lend of `recE ℓ m`: its canonical image at any template -/

/-- **Any typed image of `recE`'s escrow, re-taken at `β`, is `m ↦ imm({β}, (), ∅)`**:
`canonT_view`'s proof, at an arbitrary template in place of the `Classical` one. -/
theorem canon_recE {Θ : CodeTy} {m : BoCa.Loc} {C : TRes K}
    (hC : TmplSpecT K Θ (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m) C) (β : Life) :
    relResT (escR m) β C = viewRes β m := by
  obtain ⟨β₀, -, ⟨m', i, hv, htm, -, hiv, hir⟩, -, -⟩ := hC
  cases hv
  refine PMap.ext fun x => ?_
  rw [relResT_get, htm, PMap.sng_get, viewRes, PMap.sng_get]
  by_cases hx : x = m
  · subst hx
    simp only [if_true, Option.map_some]
    congr 1
    unfold relCellT
    have hw : (CellUT.imm i : TCell K).wit = PMap.empty := hir
    rw [dif_pos ⟨rfl, ⟨_, ResUT.single_get_self _ _, by simp⟩, by
      rw [hw]; exact emptyT_inStratum _⟩]
    exact CellUT.immOf_congr rfl hiv hw _ _
  · simp [hx]

/-- **The reborrow applies at every world holding the open lend.** At any `TWC` world (any
history: re-readings, other lends, other reborrows) with a record whose base is `recE ℓ m` and
its lend cell at `le`, the reborrow at `β` with image `m ↦ imm({β}, (), ∅)` is a `TWC` step. Its
remaining premises are the reborrow rule's own and read no template: `β` below the frames whose
lineage it reaches (`RebRecLeT`), and `✓` of the composite. -/
theorem reb_anyStart {Θ : CodeTy} {W W' : TRes K} {ps rs : List (RecC K)}
    (hT : TWC K Θ W ps rs) {r : RecC K} (hr : r ∈ rs) {l m le : BoCa.Loc}
    (hb : r.b = recE l m) {s : TSet} {hs : r.b.R.InStratum s}
    (hle : W.get le = some (CellUT.immOf s r.b.v r.b.R hs)) {β : Life}
    (hβ : RebRecLeT K W (bs ps) r.b.R β) (hW : ResUT.CompS W (viewRes β m) W')
    (hv : ResUT.Valid W') : TWC K Θ W' ps rs := by
  have hok := hT.tmpl.2 r hr
  have hcanon : canonC r β = viewRes β m := by
    unfold canonC; unfold TmplOK at hok; rw [hb] at hok ⊢; exact canon_recE hok β
  refine TWC.reb r hT hr hle ?_ ?_ hβ hcanon.symm hW hv
  · rw [hb]; exact view_reb β m
  · rw [hb]; exact view_typed Θ β m

/-- **Two reborrows of one record share witnesses** wherever both hold a cell: both are its one
template re-taken (`relResT` keeps every witness). -/
theorem canonC_wit {r : RecC K} {β β' : Life} {x : BoCa.Loc} {ψ ψ' : TCell K}
    (e : (canonC r β).get x = some ψ) (e' : (canonC r β').get x = some ψ') : ψ.wit = ψ'.wit := by
  rw [canonC, relResT_get] at e e'
  obtain ⟨ζ, eζ, rfl⟩ := Option.map_eq_some_iff.mp e
  obtain ⟨ζ', eζ', rfl⟩ := Option.map_eq_some_iff.mp e'
  rw [eζ] at eζ'; cases Option.some.inj eζ'
  rw [(relCellT_props _ _ _ _).2.1, (relCellT_props _ _ _ _).2.1]

/-! ### Cells and images at the configurations -/

theorem reb_empty (β : Life) : ResUT.Reb β (PMap.empty : TRes K) PMap.empty :=
  ⟨emptyT_inStratum _, [], PMap.empty, ⟨List.nodup_nil, fun x => by simp⟩, .nil,
    ⟨PMap.empty, ResUT.compS_empty_right _⟩, fun _ _ h => by cases h⟩

/-- `∅` is a typed image of the empty escrow at `unit`: an empty lend's template. -/
theorem tmpl_empty (Θ : CodeTy) (β : Life) :
    TmplSpecT K Θ PMap.empty KTy.unit BoCa.Val.unit PMap.empty :=
  ⟨β, reb_empty β, ⟨rfl, rfl⟩, ⟨_, BoCa.Fig16.Tree.agW_empty⟩, fun _ _ e => by simp at e⟩

/-- `m ↦ imm({α}, (), ∅)` is a typed image of `recE`'s escrow: the template the opening rule
fixes for `recE ℓ m`. -/
theorem tmpl_view (Θ : CodeTy) (α : Life) (m : BoCa.Loc) :
    TmplSpecT K Θ (escR m) (KTy.ref KTy.unit) (BoCa.Val.loc m) (viewRes α m) :=
  ⟨α, view_reb α m, view_typed Θ α m, agW_of_valid (valid_view α m), view_cov Θ α m⟩

/-- A view of `m` at a lifetime set: `m ↦ imm(s, (), ∅)`. -/
def viewCellS (s : TSet) : TCell K :=
  CellUT.immOf s BoCa.Val.unit PMap.empty (emptyT_inStratum _)

abbrev viewResS (s : TSet) (m : BoCa.Loc) : TRes K := ResUT.single m (viewCellS s)

theorem viewRes_eq (β : Life) (m : BoCa.Loc) :
    viewRes (K := K) β m = viewResS (TSet.single β) m := rfl

theorem ag_viewS {s : TSet} {m : BoCa.Loc} {a : TRes K} (h : AgWT (viewResS s m) a) :
    a = viewResS s m := by
  obtain ⟨e, a', p, he, ha', hp, hc⟩ := AgWT.single_imm_inv (χ := PMap.empty) h
  obtain rfl : e = PMap.empty :=
    ExRT.functional he (ExWT.empty_of_all_imm (fun _ _ e => by simp at e))
  obtain rfl : a' = PMap.empty := AgWT.functional ha' BoCa.Fig16.Tree.agW_empty
  obtain rfl : PMap.empty = p := ResUT.eq_of_comp_empty_right hp
  exact (ResUT.eq_of_comp_empty_right hc).symm

theorem valid_viewS (s : TSet) (m : BoCa.Loc) : ResUT.Valid (viewResS (K := K) s m) :=
  valid_single_imm (emptyT_inStratum _) (ResUT.comp_empty_left _) (ResUT.valid_single_own m _)

/-- Two views of `m` compose to the view at the union: they share the witness `∅`. -/
theorem viewS_comp (s t : TSet) (m : BoCa.Loc) :
    ResUT.CompS (viewResS (K := K) s m) (viewResS t m) (viewResS (s ∪ t) m) :=
  ResUT.compS_single_imm m s t BoCa.Val.unit PMap.empty (emptyT_inStratum _)
    (emptyT_inStratum _) (emptyT_inStratum _)

/-- `ag(ℓ ↦ imm({α}, loc m, R))` holds nothing off `ℓ` and `m`. -/
theorem ag_lend_none {α : Life} {l m : BoCa.Loc} {a : TRes K}
    (h : AgWT (ResUT.single l (lendCell α m)) a) {x : BoCa.Loc} (hxl : x ≠ l) (hxm : x ≠ m) :
    a.get x = none := by
  obtain ⟨e, a', p, he, ha', hp, hc⟩ := AgWT.single_imm_inv h
  obtain rfl : e = escR m := ExRT.functional he (ExWT.single_own m _)
  obtain rfl : a' = PMap.empty := AgWT.functional ha' (AgWT.single_own m _)
  obtain rfl : escR m = p := ResUT.eq_of_comp_empty_right hp
  have h₂ : (escR (K := K) m).get x = none := ResUT.single_get_ne _ hxm
  rcases ResUT.Comp.get hc x with ⟨-, -, f⟩ | ⟨χ, f₁, -, -⟩ | ⟨χ, -, f₂, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
  · exact f
  · rw [ResUT.single_get_ne _ hxl] at f₁; cases f₁
  · rw [h₂] at f₂; cases f₂
  · rw [ResUT.single_get_ne _ hxl] at f₁; cases f₁

/-- **The lend beside a view of its escrow**: `ℓ ↦ imm({α}, loc m, R) ● m ↦ imm(s, (), ∅)` is
valid, with `ex = ∅` and `ag` the lend cell at `ℓ`, the view at `m`, nothing else
(`valid_W4` at any lifetime set). -/
theorem lend_viewS {α : Life} {s : TSet} {l m : BoCa.Loc} (hlm : l ≠ m) {W : TRes K}
    (hv3 : ResUT.Valid (lendW (K := K) α l m))
    (hW : ResUT.CompS (lendW α l m) (viewResS s m) W) :
    ∃ a, ResUT.Flat W a ∧ AgWT W a ∧ a.get l = some (lendCell α m) ∧
      a.get m = some (viewCellS s) ∧ ∀ x, x ≠ l → x ≠ m → a.get x = none := by
  obtain ⟨a₃, ha₃⟩ := agW_of_valid hv3
  obtain ⟨ac, hac⟩ := agW_of_valid (valid_viewS (K := K) s m)
  obtain rfl := ag_viewS hac
  have hm₃ := (ag_lend hlm ha₃).2
  have hcR : ResUT.CompatR a₃ (viewResS s m) := by
    intro x ψ₁ ψ₂ e₁ e₂
    obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e₂
    rw [hm₃] at e₁; cases e₁
    exact ⟨_, CellUT.CompR.ownImm _ _ _ _⟩
  obtain ⟨a, ha⟩ := (ResUT.compR_defined_iff _ _).mpr hcR
  have hag : AgWT W a := (AgWT.split hW).mpr ⟨_, _, ha₃, hac, ha⟩
  have hex : ExST W PMap.empty := exST_all_imm fun x ψ e => by
    rcases compS_back hW e with ⟨χ, eχ, kχ, -⟩ | ⟨χ, eχ, kχ, -⟩ <;>
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some eχ
      rw [← kχ]; exact CellUT.kind_immOf _ _ _ _
  refine ⟨a, ⟨PMap.empty, a, hex, hag, ResUT.comp_empty_left _⟩, hag,
    (ResUT.Comp.get_of_right_none ha (ResUT.single_get_ne _ hlm)).trans (ag_lend hlm ha₃).1,
    ?_, fun x hxl hxm => ?_⟩
  · rcases ResUT.Comp.get ha m with ⟨-, f, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
        ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
    · rw [ResUT.single_get_self] at f; cases f
    · rw [ResUT.single_get_self] at f; cases f
    · rw [hm₃] at f; cases f
    · rw [hm₃] at f₁; cases f₁
      rw [ResUT.single_get_self] at f₂; cases f₂
      rw [f, CellUT.CompR.functional hC (CellUT.CompR.ownImm _ _ _ _)]; rfl
  · exact ResUT.Comp.get_of_left_none ha (ag_lend_none ha₃ hxl hxm) |>.trans
      (ResUT.single_get_ne _ hxm)

theorem descRT_recE' {l m : BoCa.Loc} {d : FrameRecT K} (h : DescRT (recE l m) d) :
    d = recE l m := descRT_recE h

/-- `recE`'s frame is at `α` in any world whose aliasable walk holds the lend cell at `ℓ` and a
view at `m` no longer than `α`. -/
theorem frameLife_of_ag {W : TRes K} {α : Life} {s : TSet} {l m : BoCa.Loc}
    (hs : ∀ x ∈ s.set, K.le x α)
    (hag : ∀ a, AgWT W a → a.get l = some (lendCell α m) ∧ a.get m = some (viewCellS s)) :
    FrameLifeT K W (recE l m) α := by
  refine ⟨fun a ha ζ t eζ ht y hy => ?_, fun a ha m' hm' ψ t eψ ht x hx => ?_⟩
  · rw [show (recE (K := K) l m).le = l from rfl, (hag a ha).1] at eζ
    cases eζ
    erw [CellUT.lsOfI_immOf, Option.some.injEq] at ht
    subst ht
    simpa using hy
  · obtain ⟨d, hd, ζ, eζ, -⟩ := hm'
    obtain rfl := descRT_recE hd
    obtain ⟨rfl, -⟩ := ResUT.single_get_eq_some eζ
    rw [(hag a ha).2] at eψ
    cases eψ
    erw [CellUT.lsOfI_immOf, Option.some.injEq] at ht
    subst ht
    exact hs x hx

/-- `RebRecLe` at `recE` and records with no lineage location, read off the frame lifetime. -/
theorem rebRecLe_of {W : TRes K} {α β : Life} {l m : BoCa.Loc} {ps : List (FrameRecT K)}
    (hps : ∀ p ∈ ps, p = recE l m ∨ ∀ x, ¬ LinLocT p x) (hβ : K.le β α)
    (hl : ∀ a, AgWT W a → a.get l = some (lendCell α m)) (hv : ResUT.Valid W) :
    RebRecLeT K W ps (escR m) β := by
  rintro p hp α' hfl ⟨x, hx, -⟩
  rcases hps p hp with rfl | hno
  · obtain ⟨a, ha⟩ := agW_of_valid hv
    have := hfl.1 a ha _ _ (hl a ha) (CellUT.lsOfI_immOf _ _ _ _) α (by simp)
    subst this; exact hβ
  · exact (hno x hx).elim

/-! ### The record invariant with per-record templates -/

/-- A tagged list of records with templates. -/
abbrev rsOfC (ls : List (RecC K × Life)) : List (RecC K) := ls.map Prod.fst

abbrev lsOfC (ls : List (RecC K × Life)) : List (SRecT K) := ls.map fun x => (x.1.b, x.2)

/-- **`RecInv` with per-record templates**: `TWC` at the world's tree and code typing, tagged. It
reads no template choice of the world. -/
def RecInvC (w : TWd) (fρ : TRes w.K) (ps : List (RecC w.K)) (ls : List (RecC w.K × Life)) :
    Prop :=
  TWC w.K w.Θ fρ ps (rsOfC ls) ∧ TaggedT w.K fρ (bs ps) (lsOfC ls)

/-- `RecInvC` does not read the world's choice. -/
theorem recInvC_tc_irrel {w : TWd} (tc : TChoice w.K) {fρ : TRes w.K} {ps : List (RecC w.K)}
    {ls : List (RecC w.K × Life)} : RecInvC w fρ ps ls ↔ RecInvC (withTc w tc) fρ ps ls :=
  Iff.rfl

/-- `A`'s record: `recE ℓ m` with the template `m ↦ imm({α}, (), ∅)`. -/
def recA (α : Life) (l m : BoCa.Loc) : RecC K := ⟨recE l m, viewRes α m⟩

/-- **The lend is a `TWC` world**: `twnt_lend` with the template fixed by `immFrame`. -/
theorem twc_lend (Θ : CodeTy) (α : Life) {l m : BoCa.Loc} (hlm : l ≠ m) :
    TWC K Θ (lendW α l m) [recA α l m] [recA α l m] ∧ ResUT.Valid (lendW (K := K) α l m) := by
  have h1 : TWC K Θ (escR m) [] [] :=
    .alloc (μ := fun _ => none) .empty ⟨_, flat_empty, fun x => by simp⟩ rfl
      (ResUT.comp_empty_left _) (ResUT.valid_single_own m _)
  obtain ⟨W2, hW2⟩ := single_compS (K := K) hlm.symm (CellUT.ownOf BoCa.Val.unit)
    (CellUT.ownOf (BoCa.Val.loc m))
  have hv2 := valid_two_own (K := K) BoCa.Val.unit (BoCa.Val.loc m) hW2
  have h2 : TWC K Θ W2 [] [] :=
    .alloc (μ := fun x => if x = m then some BoCa.Val.unit else none) h1
      ⟨_, ResUT.flat_single_own m _, fun x => by
        rw [PMap.sng_get]; by_cases hx : x = m <;> simp [hx]⟩ (if_neg hlm) hW2 hv2.1
  have hv3 : ResUT.Valid (lendW (K := K) α l m) := valid_single_imm _ hW2 hv2.1
  refine ⟨?_, hv3⟩
  exact TWC.immFrame (W := W2) (X := W2) (Z := PMap.empty) (R := escR m) (ds := [])
    (KTy.ref KTy.unit) (own_inStratum (TSet.single α) m BoCa.Val.unit) h2 (ResUT.CompS.comm hW2)
    (ResUT.compS_empty_right _) (escR_typed Θ m) (ResUT.compS_empty_right _) hv3
    (fun d => ⟨fun h => by simp at h, fun h => (recE_no_desc l m d h).elim⟩)
    (tmpl_view Θ α m) (fun d h => by simp at h)

/-- **At `config_tc0`'s world the lend meets `RecInvC`, and so does the reborrowed world.** The
world `⟨P, Θ, tc0⟩` and the lend `ℓ ↦ imm({α}, loc m, m ↦ own(()))` of `RebSpike.config_tc0`,
where `TWNT.reb` cannot fire. With the template in the record, the reborrow at any `β ≤ α` is a
step: `ℓ ↦ imm({α}, loc m, R) ● m ↦ imm({β}, (), ∅)` meets `RecInvC` at the same world. -/
theorem config_C_tc0 (P : ParentFn) (Θ : CodeTy) {α β : Life} {l m : BoCa.Loc} (hlm : l ≠ m)
    (hβα : (WCactus.ofParent P).le β α) :
    let w : TWd := ⟨P, Θ, tc0⟩
    RecInvC w (lendW α l m) [recA α l m] [(recA α l m, α)] ∧
      ∃ W', ResUT.CompS (lendW (K := w.K) α l m) (viewRes β m) W' ∧
        RecInvC w W' [recA α l m] [(recA α l m, α)] := by
  intro w
  obtain ⟨hT, hv⟩ := twc_lend (K := w.K) Θ α hlm
  refine ⟨⟨hT, fun x hx => ?_⟩, ?_⟩
  · simp only [lsOfC, List.map_cons, List.map_nil, List.mem_singleton] at hx
    subst hx
    exact ⟨recE l m, List.mem_cons_self, ⟨[], .nil _⟩, frameLife_lend α hlm⟩
  obtain ⟨W', hW'⟩ := single_compS (K := w.K) hlm (lendCell α m) (viewCell β)
  obtain ⟨a, -, ha, hal, ham, -⟩ := lend_viewS (s := TSet.single β) hlm hv hW'
  have hv' : ResUT.Valid W' := valid_W4 hlm hv hW'
  have hagW : ∀ a', AgWT W' a' → a'.get l = some (lendCell α m) ∧
      a'.get m = some (viewCellS (TSet.single β)) := fun a' ha' => by
    obtain rfl := AgWT.functional ha' ha; exact ⟨hal, ham⟩
  have hT' : TWC w.K w.Θ W' [recA α l m] [recA α l m] :=
    reb_anyStart hT List.mem_cons_self (le := l) (s := TSet.single α)
      (hs := own_inStratum _ _ _) rfl (ResUT.single_get_self _ _)
      (rebRecLe_of (fun p hp => by simp at hp; exact Or.inl hp) hβα
        (fun a' ha' => (ag_lend hlm ha').1) hv) hW' hv'
  refine ⟨W', hW', hT', fun x hx => ?_⟩
  simp only [lsOfC, List.map_cons, List.map_nil, List.mem_singleton] at hx
  subst hx
  exact ⟨recE l m, List.mem_cons_self, ⟨[], .nil _⟩,
    frameLife_of_ag (fun x hx => by simp at hx; subst hx; exact hβα) hagW⟩

/-! ### Canonical images across a re-reading -/

/-- **The record's template re-takes at `β` at the old tree** wherever it re-takes at all: every
`imm` template cell over a non-`imm` escrow cell has its witness in `Res_{β}`. A scope premise of
`canonC_rr`: re-reading keeps `Res_{β}` (`RR.inStratum`) but need not reflect it. It holds when the
template's witnesses are `∅`, as at `recE` (`retakes_recA`). -/
def Retakes (r : RecC K) (β : Life) : Prop :=
  ∀ x (ψ : TCell K), r.C.get x = some ψ → ψ.kind = Kind.imm →
    (∃ ζ : TCell K, r.b.R.get x = some ζ ∧ ζ.kind ≠ Kind.imm) → ψ.wit.InStratum (TSet.single β)

theorem retakes_recA (α β : Life) (l m : BoCa.Loc) : Retakes (recA (K := K) α l m) β := by
  intro x ψ e _ _
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  change (viewCell (K := K) α).wit.InStratum _
  rw [viewCell, CellUT.wit_immOf]; exact emptyT_inStratum _

/-- **A canonical image re-read is the canonical image of the re-read record**: the record's
template is re-read with it (`RecRRC`), and re-taking at `β` commutes with re-reading. -/
theorem canonC_rr {Θ' : CodeTy} (hE : K.Ext K') {r : RecC K} {r' : RecC K'}
    (hrr : RecRRC Θ' r r') {β : Life} (hret : Retakes r β) :
    RR (sem Θ') (canonC r β) (canonC r' β) := by
  obtain ⟨⟨-, -, -, hR⟩, hC⟩ := hrr
  refine ⟨fun x => ?_, fun x ψ ψ' e e' => ?_⟩
  · rw [canonC, canonC, relResT_get, relResT_get]
    simp only [Option.map_eq_none_iff]
    exact hC.1 x
  · rw [canonC, relResT_get] at e
    rw [canonC, relResT_get] at e'
    obtain ⟨ζ, eζ, rfl⟩ := Option.map_eq_some_iff.mp e
    obtain ⟨ζ', eζ', rfl⟩ := Option.map_eq_some_iff.mp e'
    have hz := hC.2 x ζ ζ' eζ eζ'
    have hk := hz.kind
    have hRk : (∃ χ : TCell K, r.b.R.get x = some χ ∧ χ.kind ≠ Kind.imm) ↔
        (∃ χ : TCell K', r'.b.R.get x = some χ ∧ χ.kind ≠ Kind.imm) := by
      constructor
      · rintro ⟨χ, eχ, kχ⟩
        obtain ⟨χ', eχ', hχ⟩ := hR.get_some eχ
        exact ⟨χ', eχ', by rw [hχ.kind]; exact kχ⟩
      · rintro ⟨χ', eχ', kχ'⟩
        obtain ⟨χ, eχ, hχ⟩ := hR.get_some' eχ'
        exact ⟨χ, eχ, by rw [← hχ.kind]; exact kχ'⟩
    unfold relCellT
    by_cases h : ζ.kind = Kind.imm ∧ (∃ χ : TCell K, r.b.R.get x = some χ ∧ χ.kind ≠ Kind.imm) ∧
        ζ.wit.InStratum (TSet.single β)
    · have h' : ζ'.kind = Kind.imm ∧ (∃ χ : TCell K', r'.b.R.get x = some χ ∧ χ.kind ≠ Kind.imm) ∧
          ζ'.wit.InStratum (TSet.single β) :=
        ⟨hk.trans h.1, hRk.mp h.2.1, hz.wit.inStratum hE h.2.2⟩
      rw [dif_pos h, dif_pos h']
      have he := hz.erase
      rw [he]
      exact RC.immOf_of _ _ hz.wit
    · have h' : ¬ (ζ'.kind = Kind.imm ∧
          (∃ χ : TCell K', r'.b.R.get x = some χ ∧ χ.kind ≠ Kind.imm) ∧
          ζ'.wit.InStratum (TSet.single β)) := by
        rintro ⟨k', hR', -⟩
        have k : ζ.kind = Kind.imm := hk.symm.trans k'
        exact h ⟨k, hRk.mpr hR', hret x ζ eζ k (hRk.mpr hR')⟩
      rw [dif_neg h, dif_neg h']
      exact hz

/-- **`KeepRel` with templates**: every record of the stop list the share reads has its
re-reading, template included, in the resume list. -/
def KeepRelC {K K' : WCactus} (Θ' : CodeTy) (ls : List (RecC K × Life))
    (ls' : List (RecC K' × Life)) (ρ : TRes K) : Prop :=
  ∀ r ∈ rsOfC ls, RelFT r.b ρ → ∃ r' ∈ rsOfC ls', RecRRC Θ' r r'

/-- **Through `KeepRelC` alone, a held reborrow is canonical at the resume list**: the re-read of
the stop record's canonical image is the canonical image of a record of the resume list. -/
theorem keepRelC_canon {Θ' : CodeTy} (hE : K.Ext K') {ls : List (RecC K × Life)}
    {ls' : List (RecC K' × Life)} {ρ : TRes K} (hk : KeepRelC Θ' ls ls' ρ) {r : RecC K}
    (hr : r ∈ rsOfC ls) (hrel : RelFT r.b ρ) {β : Life} (hret : Retakes r β) :
    ∃ r' ∈ rsOfC ls', RecRRC Θ' r r' ∧ RR (sem Θ') (canonC r β) (canonC r' β) := by
  obtain ⟨r', hr', hrr⟩ := hk r hr hrel
  exact ⟨r', hr', hrr, canonC_rr hE hrr hret⟩

/-! ### Across a park -/

/-- `B`'s record: an empty lend of `ℓ_B`, template `∅`. -/
def recB (lB : BoCa.Loc) : RecC K := ⟨lendRec lB, PMap.empty⟩

theorem rr_lendW {Θ : LocTy} {α : Life} {l m : BoCa.Loc} :
    RR Θ (lendW (K := K) α l m) (lendW (K := K') α l m) := by
  classical
  refine ⟨fun x => ?_, fun x ψ ψ' e e' => ?_⟩
  · by_cases hx : x = l
    · subst hx; simp
    · simp [ResUT.single_get_ne _ hx]
  · obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
    exact RC.immOf_of _ _ rr_own

theorem rr_viewS {Θ : LocTy} {s : TSet} {m : BoCa.Loc} :
    RR Θ (viewResS (K := K) s m) (viewResS (K := K') s m) := by
  classical
  refine ⟨fun x => ?_, fun x ψ ψ' e e' => ?_⟩
  · by_cases hx : x = m
    · subst hx; simp
    · simp [ResUT.single_get_ne _ hx]
  · obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
    exact RC.immOf_of _ _ RR.empty

theorem recA_rr (Θ' : CodeTy) (α : Life) (l m : BoCa.Loc) :
    RecRRC Θ' (recA (K := K) α l m) (recA (K := K') α l m) :=
  ⟨⟨rfl, rfl, rfl, rr_own⟩, rr_view⟩

theorem recB_rr (Θ' : CodeTy) (lB : BoCa.Loc) :
    RecRRC Θ' (recB (K := K) lB) (recB (K := K') lB) :=
  ⟨lendRec_rr lB, RR.empty⟩

/-- `a ● b ● c` regrouped as `a ● c ● b`. -/
theorem swap_compS {a b c x y : TRes K} (h₁ : ResUT.CompS a b x) (h₂ : ResUT.CompS x c y) :
    ∃ z, ResUT.CompS a c z ∧ ResUT.CompS z b y := by
  obtain ⟨x', hbc, hax'⟩ := (ResUT.CompS.assoc a b c y).mpr ⟨x, h₁, h₂⟩
  exact (ResUT.CompS.assoc a c b y).mp ⟨x', ResUT.CompS.comm hbc, hax'⟩

/-- **The lend beside a view, and a fresh `own` cell beside both**: the composite `W ● ℓ_B ↦ own(())`
exists, is valid, and lowers. -/
theorem lend_viewS_own {α : Life} {s : TSet} {l m lB : BoCa.Loc} (hlm : l ≠ m) (hlB : lB ≠ l)
    (hmB : lB ≠ m) {W : TRes K} (hv3 : ResUT.Valid (lendW (K := K) α l m))
    (hW : ResUT.CompS (lendW α l m) (viewResS s m) W) :
    ∃ (μ : BoCa.Loc → Option BoCa.Val) (Wo : TRes K), ResUT.Lower W μ ∧ μ lB = none ∧
      ResUT.CompS W (ResUT.single lB (CellUT.ownOf BoCa.Val.unit)) Wo ∧ ResUT.Valid Wo ∧
      ResUT.Valid W ∧ (∀ a, AgWT W a → a.get l = some (lendCell α m)) := by
  obtain ⟨a, hf, ha, hal, -, hnone⟩ := lend_viewS hlm hv3 hW
  have hlow : ResUT.Lower W (fun x => (a.get x).map CellUT.erase) := ⟨a, hf, fun _ => rfl⟩
  have hμ : (fun x => (a.get x).map CellUT.erase) lB = none := by
    simp only [hnone lB hlB hmB, Option.map_none]
  obtain ⟨Wo, hWo⟩ := (ResUT.compS_defined_iff W (ResUT.single lB (CellUT.ownOf BoCa.Val.unit))).mpr
    (compatS_single_of_get_noneT (get_eq_none_of_flatT hf (hnone lB hlB hmB)))
  have hlo := lower_compS_ownT hWo hlow hμ
  obtain ⟨τ, hτ, -⟩ := id hlo
  exact ⟨_, Wo, hlow, hμ, hWo, ⟨τ, hτ⟩, ⟨a, hf⟩, fun a' ha' => by
    obtain rfl := AgWT.functional ha' ha; exact hal⟩

/-- The share `m ↦ imm(s, (), ∅)` freezes `m` and nothing else. -/
theorem frz_viewS {s : TSet} {m x : BoCa.Loc} (h : FrzT (viewResS (K := K) s m) x) : x = m := by
  cases h with
  | imm e _ => exact (ResUT.single_get_eq_some e).1
  | inImm e _ hd =>
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      have hw : (viewCellS (K := K) s).wit = PMap.empty := by
        simp [viewCellS, CellUT.wit_immOf]
      rw [hw] at hd
      cases hd with
      | top e => simp at e
      | wit e _ _ => simp at e
  | inMut e k _ =>
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      simp [viewCellS, CellUT.kind_immOf] at k

/-- **`A` holds two reborrows of its lend across a park; `B` ends a lend of its own; `A` resumes
and reborrows again.** At the tree `K`: `A`'s lend of `ℓ ↦ own(loc m)` (escrow `m ↦ own(())`,
template fixed at opening), `A`'s reborrows at `β₁` and `β₂`, then `B`'s lend of `ℓ_B` (empty
escrow), open. `A` parks: the tree grows to `K′`, every cell and record re-read (`TWC.reread`).
`B` ends its lend (`TWC.immEnd`). At the end:

* `A`'s record is in the end list, its re-reading with the template (`KeepRelC` from the park
  list to the end list at `A`'s share);
* `A`'s held share `m ↦ imm({β₁} ∪ {β₂}, (), ∅)`, re-read, is the composite of the end record's
  canonical images at `β₁` and `β₂`;
* `A` reborrows at `β₃` at the end world, with the end record's canonical image, and the result
  is a `TWC` world.

Every premise is about the tree, lifetimes and distinct locations; none is about `A`'s
resumption. -/
theorem park_config (Θ : CodeTy) (hE : K.Ext K') {α αB β₁ β₂ β₃ : Life}
    (h₁ : K.le β₁ α) (h₂ : K.le β₂ α) (h₃ : K'.le β₃ α) {l m lB : BoCa.Loc}
    (hlm : l ≠ m) (hlB : lB ≠ l) (hmB : lB ≠ m) :
    let s₂ : TSet := TSet.single β₁ ∪ TSet.single β₂
    ∃ (W6 : TRes K) (W6' W7 W8 : TRes K'),
      -- before the park
      TWC K Θ W6 [recB lB, recA α l m] [recB lB, recA α l m] ∧
      ResUT.CompS (canonC (recA (K := K) α l m) β₁) (canonC (recA α l m) β₂) (viewResS s₂ m) ∧
      RelFT (recA (K := K) α l m).b (viewResS s₂ m) ∧
      -- the park: the tree grows
      RR (sem Θ) W6 W6' ∧ TWC K' Θ W6' [recB lB, recA α l m] [recB lB, recA α l m] ∧
      -- `B` ends its lend
      TWC K' Θ W7 [recA α l m] [recA α l m] ∧
      KeepRelC Θ [(recB (K := K) lB, αB), (recA α l m, α)] [(recA (K := K') α l m, α)]
        (viewResS s₂ m) ∧
      -- `A` resumes: its share re-read is the end record's canonical images
      RR (sem Θ) (viewResS (K := K) s₂ m) (viewResS (K := K') s₂ m) ∧
      ResUT.CompS (canonC (recA (K := K') α l m) β₁) (canonC (recA α l m) β₂) (viewResS s₂ m) ∧
      -- and reborrows again
      ResUT.CompS W7 (canonC (recA (K := K') α l m) β₃) W8 ∧
      TWC K' Θ W8 [recA α l m] [recA α l m] := by
  intro s₂
  -- `A`'s lend and two reborrows, at `K`
  obtain ⟨hT3, hv3⟩ := twc_lend (K := K) Θ α hlm
  obtain ⟨W4, hW4⟩ := single_compS (K := K) hlm (lendCell α m) (viewCell β₁)
  have hv4 : ResUT.Valid W4 := valid_W4 hlm hv3 hW4
  have hT4 : TWC K Θ W4 [recA α l m] [recA α l m] :=
    reb_anyStart hT3 List.mem_cons_self (le := l) (s := TSet.single α)
      (hs := own_inStratum _ _ _) rfl (ResUT.single_get_self _ _)
      (rebRecLe_of (fun p hp => by simp at hp; exact Or.inl hp) h₁
        (fun a' ha' => (ag_lend hlm ha').1) hv3) hW4 hv4
  obtain ⟨W5, hW5⟩ := single_compS (K := K) hlm (lendCell α m) (viewCellS s₂)
  have hW45 : ResUT.CompS W4 (viewRes β₂ m) W5 := by
    obtain ⟨y, hy, hyW⟩ := (ResUT.CompS.assoc _ _ _ W5).mp
      ⟨_, viewS_comp (K := K) (TSet.single β₁) (TSet.single β₂) m, hW5⟩
    rw [ResUT.CompS.functional hy hW4] at hyW; exact hyW
  obtain ⟨μ5, W5o, hlow5, hμ5, hW5o, hv5o, hv5, hag5⟩ := lend_viewS_own hlm hlB hmB hv3 hW5
  have hag4 : ∀ a, AgWT W4 a → a.get l = some (lendCell α m) := by
    obtain ⟨a, -, ha, hal, -⟩ := lend_viewS (s := TSet.single β₁) hlm hv3 hW4
    intro a' ha'; obtain rfl := AgWT.functional ha' ha; exact hal
  have hle4 : W4.get l = some (lendCell α m) :=
    (ResUT.Comp.get_of_right_none hW4 (ResUT.single_get_ne _ hlm)).trans
      (ResUT.single_get_self _ _)
  have hT5 : TWC K Θ W5 [recA α l m] [recA α l m] :=
    reb_anyStart hT4 List.mem_cons_self (le := l) (s := TSet.single α)
      (hs := own_inStratum _ _ _) rfl hle4
      (rebRecLe_of (fun p hp => by simp at hp; exact Or.inl hp) h₂ hag4 hv4) hW45 hv5
  -- `B` allocates `ℓ_B` and lends it
  have hT5o : TWC K Θ W5o [recA α l m] [recA α l m] := .alloc hT5 hlow5 hμ5 hW5o hv5o
  have hsB : ResUT.InStratum (TSet.single αB) (PMap.empty : TRes K) := emptyT_inStratum _
  obtain ⟨-, W6, hW6, hv6⟩ := ResUT.six34 (ρ := W5) (ρv := PMap.empty) (hs := hsB)
    (ResUT.comp_empty_left _) (ResUT.Hash.of_compS hW5o hv5o)
  have hT6 : TWC K Θ W6 [recB lB, recA α l m] [recB lB, recA α l m] :=
    TWC.immFrame (W := W5o) (X := ResUT.single lB (CellUT.ownOf BoCa.Val.unit)) (Z := W5)
      (R := PMap.empty) (ds := []) (C := PMap.empty) KTy.unit hsB hT5o
      (ResUT.compS_empty_right _) (ResUT.CompS.comm hW5o) ⟨rfl, rfl⟩ (ResUT.CompS.comm hW6) hv6
      (fun d => ⟨fun h => by simp at h, fun h => (emptyRec_no_desc lB _ _ d h).elim⟩)
      (tmpl_empty Θ αB) (fun d h => by simp at h)
  -- `A`'s share, and its record
  have hshare : ResUT.CompS (canonC (recA (K := K) α l m) β₁) (canonC (recA α l m) β₂)
      (viewResS s₂ m) := by
    change ResUT.CompS (relResT (escR m) β₁ (viewRes α m)) (relResT (escR m) β₂ (viewRes α m)) _
    rw [canon_recE (tmpl_view Θ α m), canon_recE (tmpl_view Θ α m)]
    exact viewS_comp _ _ m
  have hreads : RelFT (recA (K := K) α l m).b (viewResS s₂ m) :=
    ⟨m, FrzT.imm (ResUT.single_get_self _ _) (CellUT.kind_immOf _ _ _ _),
      Or.inr ⟨none, KTy.unit, BoCa.Val.unit, ChainT.one (RefPosT.ref KTy.unit m)
        (ResUT.single_get_self _ _)⟩⟩
  -- the park: re-read at `K'`
  obtain ⟨W5', hW5', hr5⟩ := RR.compS (rr_lendW (K' := K') (Θ := sem Θ)) rr_viewS hW5
  obtain ⟨W6', hW6', hr6⟩ := RR.compS hr5 (rr_view (K' := K')) hW6
  have hT6' : TWC K' Θ W6' [recB lB, recA α l m] [recB lB, recA α l m] :=
    TWC.reread hT6 hE (AgreeOn.refl Θ W6) hr6
      (.cons (recB_rr Θ lB) (.cons (recA_rr Θ α l m) .nil))
      (.cons (recB_rr Θ lB) (.cons (recA_rr Θ α l m) .nil))
  -- `B` ends its lend at `K'`
  obtain ⟨W7, hW7, hr7⟩ := RR.compS hr5 (rr_own (K' := K')) hW5o
  have hv7 : ResUT.Valid W7 := WitRel.ResUT.Valid.sim hv5o hr7.rsim
  have hne : (recA (K := K') α l m).b ≠ (recB lB).b := fun h => hlB (congrArg FrameRecT.le h).symm
  have hT7 : TWC K' Θ W7 [recA α l m] [recA α l m] := by
    refine TWC.immEnd (recB lB) (s := TSet.single αB) (hs := emptyT_inStratum _) hT6'
      List.mem_cons_self (ResUT.CompS.comm hW6') (ResUT.compS_empty_right _)
      (ResUT.CompS.comm hW7) hv7 (fun x => ?_) (fun d => ?_) (fun q hq => ?_) (fun q hq => ?_)
    · simp only [bs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro rfl; exact ⟨Or.inr rfl, hne⟩
      · rintro ⟨h | h, h'⟩
        · exact (h' h).elim
        · exact h
    · constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨_, List.mem_cons_self, DescRT.refl _⟩
        · cases h
      · rintro ⟨p, hp, hd⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · rw [descRT_recE hd]; exact List.mem_cons_self
        · cases hp
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · cases hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · cases hq
  have hkeep : KeepRelC Θ [(recB (K := K) lB, αB), (recA α l m, α)] [(recA (K := K') α l m, α)]
      (viewResS s₂ m) := by
    intro r hr hrel
    simp only [rsOfC, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- `B`'s record is not read by `A`'s share: its lent location is `ℓ_B`, not in the share
      exfalso
      obtain ⟨x, hf, hx⟩ := hrel
      · rcases hx with rfl | ⟨p, S, u, hc⟩
        · exact hmB (frz_viewS hf)
        · cases hc with
          | one _ e => simp [recB, lendRec] at e
          | step _ e _ => simp [recB, lendRec] at e
    · exact ⟨recA α l m, List.mem_cons_self, recA_rr Θ α l m⟩
  -- `A` resumes at `W7` and reborrows at `β₃`
  have hok := hT7.tmpl.2 _ List.mem_cons_self
  have hcanon : ∀ β, canonC (recA (K := K') α l m) β = viewRes β m := fun β => by
    unfold canonC; exact canon_recE hok β
  have hshare' : ResUT.CompS (canonC (recA (K := K') α l m) β₁) (canonC (recA α l m) β₂)
      (viewResS s₂ m) := by
    rw [hcanon, hcanon]; exact viewS_comp _ _ m
  have hv3' : ResUT.Valid (lendW (K := K') α l m) := (twc_lend (K := K') Θ α hlm).2
  have hle7 : W7.get l = some (lendCell α m) :=
    (ResUT.Comp.get_of_right_none hW7 (ResUT.single_get_ne _ hlB.symm)).trans
      ((ResUT.Comp.get_of_right_none hW5' (ResUT.single_get_ne _ hlm)).trans
        (ResUT.single_get_self _ _))
  obtain ⟨a5', -, ha5', hal5', -⟩ := lend_viewS (s := s₂) hlm hv3' hW5'
  have hag7 : ∀ a, AgWT W7 a → a.get l = some (lendCell α m) := by
    intro a ha
    obtain rfl := AgWT.functional ha (ag_compS_own hW7 ha5'); exact hal5'
  obtain ⟨V8, hV8⟩ := single_compS (K := K') hlm (lendCell α m) (viewCellS (s₂ ∪ TSet.single β₃))
  have hW5V8 : ResUT.CompS W5' (viewRes β₃ m) V8 := by
    obtain ⟨y, hy, hyW⟩ := (ResUT.CompS.assoc _ _ _ V8).mp
      ⟨_, viewS_comp (K := K') s₂ (TSet.single β₃) m, hV8⟩
    rw [ResUT.CompS.functional hy hW5'] at hyW; exact hyW
  obtain ⟨μ8, W8, -, -, hW8o, hv8, -, -⟩ := lend_viewS_own hlm hlB hmB hv3' hV8
  have hW78 : ResUT.CompS W7 (viewRes β₃ m) W8 := by
    obtain ⟨z, hz, hzW⟩ := swap_compS hW5V8 hW8o
    rw [ResUT.CompS.functional hz hW7] at hzW; exact hzW
  have hT8 : TWC K' Θ W8 [recA α l m] [recA α l m] :=
    reb_anyStart hT7 List.mem_cons_self (le := l) (s := TSet.single α)
      (hs := own_inStratum _ _ _) rfl hle7
      (rebRecLe_of (fun p hp => by simp at hp; exact Or.inl hp) h₃ hag7 hv7) hW78 hv8
  exact ⟨W6, W6', W7, W8, hT6, hshare, hreads, hr6, hT6', hT7, hkeep, rr_viewS, hshare',
    by rw [hcanon]; exact hW78, hT8⟩

end BoCa.Fig16.Tree.Wp.RebSpike

end
