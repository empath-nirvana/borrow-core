import Core.Chain.SI.TWN

/-!
# Canonical images: one witness choice per record

**New design, not a transcription.** A reborrow's image `χ ∈ reb_β(ρ′)` fixes, at every `own`
cell of the escrow, a witness: a piece of the escrow below the root. When the payload holds a
thunk (or an opaque or a type variable standing for one) under a `ref`, the shape leaves that
piece free (`reb_witness_choice`), and two images of one escrow may be incompatible.

Here the choice is made once per record, not per reborrow. `tmpl r` is one typed image of the
record's escrow (`TmplSpec`), chosen with `Classical.choose`; the image at `β` is `canon r β`, the
template re-taken at `β` (`relRes`, which changes lifetimes and keeps every witness). `TWNC` is
`TWN` with `reb`'s image required to be `canon r β`. Every other constructor is `TWN`'s.

The invariant this buys is global, not pointwise: every view of `ag(W)` at a root of a record
carries the template's witness there (`TemplAt`, `TWNC.templ`). It is proved by induction on
`TWNC` from the transfer lemmas `TI`'s proof uses at each step (`reb_like_back`,
`frame_transfer`, `end_back`, `lift_view`). From it, the canonical image at any `β` agrees with
every typed world holding the record (`canon_escrowAgree`), whatever the world did while the image
was folded: the re-entry's agreement (`rebReentryAgreeC`), the step
`not_rebReentryAgreeN` refutes for `TWN`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)

/-- A typed image of a record's escrow at some lifetime: what `TW.reb` asks of an image, with
`ag` defined. -/
def TmplSpec (r : FrameRec) (c : WRes) : Prop :=
  ∃ (β : Life) (x : LifeVar), ¬ VFree x r.T ∧ ResU.Reb β r.R c ∧
    vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c ∧ ∃ A, AgW c A

open Classical in
/-- **The record's template**: one typed image of its escrow, fixed for the record. -/
def tmpl (r : FrameRec) : WRes :=
  if h : ∃ c, TmplSpec r c then Classical.choose h else PMap.empty

theorem tmpl_spec {r : FrameRec} (h : ∃ c, TmplSpec r c) : TmplSpec r (tmpl r) := by
  unfold tmpl; rw [dif_pos h]; exact Classical.choose_spec h

/-- **The canonical image at `β`**: the template re-taken at `β`. -/
def canon (r : FrameRec) (β : Life) : WRes := relRes r.R β (tmpl r)

/-- A cell of the canonical image carries the template's witness. -/
theorem canon_get {r : FrameRec} {β : Life} {m : Loc} {ψ : CellU Loc Val}
    (e : (canon r β).get m = some ψ) :
    ∃ ζ, (tmpl r).get m = some ζ ∧ ψ.wit = ζ.wit := by
  rw [canon, relRes_get] at e
  obtain ⟨ζ, eζ, rfl⟩ := Option.map_eq_some_iff.mp e
  exact ⟨ζ, eζ, (relCell_props r.R β m ζ).2.1⟩

/-- Two canonical images of one record carry the same witness at every location both hold. -/
theorem canon_wit {r : FrameRec} {β β' : Life} {m : Loc} {ψ ψ' : CellU Loc Val}
    (e : (canon r β).get m = some ψ) (e' : (canon r β').get m = some ψ') : ψ.wit = ψ'.wit := by
  obtain ⟨ζ, eζ, w⟩ := canon_get e
  obtain ⟨ζ', eζ', w'⟩ := canon_get e'
  rw [eζ] at eζ'; cases Option.some.inj eζ'
  exact w.trans w'.symm

/-- The canonical image is an image at every `β` the escrow lies above. -/
theorem canon_reb {r : FrameRec} {β : Life} (hS : TmplSpec r (tmpl r)) (hRβ : r.R.InStratum β) :
    ResU.Reb β r.R (canon r β) := by
  obtain ⟨β₀, -, -, hreb, -⟩ := hS
  exact relabel_reb hRβ hreb

/-- A typed image of a chain view's escrow `w₀` (the view at a position of type `S₀` holding
`u₀`), with `ag` defined: what `TW.rebDeep` asks of an image. -/
def TmplSpecD (r : FrameRec) (S₀ : VTy) (u₀ : Val) (w₀ c : WRes) : Prop :=
  ∃ (β : Life) (x : LifeVar), ¬ VFree x S₀ ∧ ResU.Reb β w₀ c ∧
    vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ c ∧ ∃ A, AgW c A

open Classical in
/-- **A chain view's template**: one typed image of the view's escrow, fixed for the record,
the position's type and value, and the escrow. -/
def tmplD (r : FrameRec) (S₀ : VTy) (u₀ : Val) (w₀ : WRes) : WRes :=
  if h : ∃ c, TmplSpecD r S₀ u₀ w₀ c then Classical.choose h else PMap.empty

theorem tmplD_spec {r : FrameRec} {S₀ : VTy} {u₀ : Val} {w₀ : WRes}
    (h : ∃ c, TmplSpecD r S₀ u₀ w₀ c) : TmplSpecD r S₀ u₀ w₀ (tmplD r S₀ u₀ w₀) := by
  unfold tmplD; rw [dif_pos h]; exact Classical.choose_spec h

/-- **The canonical image of a chain view at `β`**: the view's template re-taken at `β`. -/
def canonD (r : FrameRec) (S₀ : VTy) (u₀ : Val) (w₀ : WRes) (β : Life) : WRes :=
  relRes w₀ β (tmplD r S₀ u₀ w₀)

theorem canonD_get {r : FrameRec} {S₀ : VTy} {u₀ : Val} {w₀ : WRes} {β : Life} {m : Loc}
    {ψ : CellU Loc Val} (e : (canonD r S₀ u₀ w₀ β).get m = some ψ) :
    ∃ ζ, (tmplD r S₀ u₀ w₀).get m = some ζ ∧ ψ.wit = ζ.wit := by
  rw [canonD, relRes_get] at e
  obtain ⟨ζ, eζ, rfl⟩ := Option.map_eq_some_iff.mp e
  exact ⟨ζ, eζ, (relCell_props w₀ β m ζ).2.1⟩

/-- The typed world with canonical images: `TWN` with `reb`'s image required to be
`canon r β` and `rebDeep`'s `canonD r S₀ u₀ w₀ β`.  `[about ours: new design beside TWN; experiments/ChainProbes/ChainProbes/CanonN.lean's header]` -/
inductive TWNC : WRes → List FrameRec → List FrameRec → Prop
  | empty : TWNC PMap.empty [] []
  | alloc {W W' : WRes} {ps rs : List FrameRec} {μ : BoCa.BoLo.Heap} {l : Loc} {v : Val} :
      TWNC W ps rs → ResU.Lower W μ → μ l = none →
      ResU.CompS W (ResU.single l (CellU.ownOf v)) W' → ResU.Valid W' → TWNC W' ps rs
  | immFrame {W X Z R W' : WRes} {ps rs ds : List FrameRec} {l : Loc} {v : Val} {α : Life}
      (T : VTy) (δ : BoCa.Lifetime.LSub) (h : R.InStratum (LSet.singleton α).join) :
      TWNC W ps rs → AdmWf T δ → ResU.CompS (ResU.single l (CellU.ownOf v)) R X →
      ResU.CompS X Z W → vShape T δ v R →
      ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W' →
      ResU.Valid W' → (∀ d, d ∈ ds ↔ Desc ⟨l, v, R, T, δ⟩ d) →
      TWNC W' (⟨l, v, R, T, δ⟩ :: ps) (⟨l, v, R, T, δ⟩ :: (ds ++ rs))
  | reb {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} (x : LifeVar) :
      TWNC W ps rs → r ∈ rs → W.get le = some (CellU.immOf s r.v r.R hs) →
      ¬ VFree x r.T → ResU.Reb β r.R c →
      vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
      RebRecLe W ps r.R β → c = canon r β → ResU.CompS W c W' → ResU.Valid W' → TWNC W' ps rs
  | rebDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc} {l₀ : Loc}
      {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join} {β : Life}
      (x : LifeVar) :
      TWNC W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ¬ VFree x S₀ → ResU.Reb β w₀ c →
      vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ c →
      RebCellLe W l₀ β → RebRecLe W ps w₀ β → c = canonD r S₀ u₀ w₀ β →
      ResU.CompS W c W' → ResU.Valid W' → TWNC W' ps rs
  | mutFold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TWNC W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W →
      ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W' → ResU.Valid W' →
      TWNC W' ps rs
  | mutUnfold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TWNC W ps rs → ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W' → ResU.Valid W' →
      TWNC W' ps rs
  | free {W W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} :
      TWNC W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) W' W → ResU.Valid W' →
      TWNC W' ps rs
  | store {W Z W' : WRes} {ps rs : List FrameRec} {l : Loc} {v₁ v₂ : Val} :
      TWNC W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v₁)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v₂)) Z W' → ResU.Valid W' → TWNC W' ps rs
  | immEnd {W Y X' W' : WRes} {ps rs ps' rs' : List FrameRec} (r : FrameRec) {s : LSet}
      {hs : r.R.InStratum s.join} :
      TWNC W ps rs → r ∈ ps → ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) Y W →
      ResU.CompS (ResU.single r.le (CellU.ownOf r.v)) r.R X' → ResU.CompS X' Y W' →
      ResU.Valid W' → (∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r)) →
      (∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescR p d) → TWNC W' ps' rs'
  | rebEnd {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} :
      TWNC W ps rs → r ∈ rs → W'.get le = some (CellU.immOf s r.v r.R hs) →
      ResU.Reb β r.R c → ResU.CompS W' (c.restrictDom r.R.exclPart) W →
      RebEndRec W' rs r.R β → TWNC W' ps rs
  | rebEndDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc}
      {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
      {β : Life} :
      TWNC W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W'.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ResU.Reb β w₀ c →
      ResU.CompS W' (c.restrictDom w₀.exclPart) W → RebEndRec W' rs w₀ β → TWNC W' ps rs

/-- Every `TWNC` world is a `TWN` world: `TWN`'s invariants (`TI`, `LinLife`, `ProperRoot`)
hold of it. -/
theorem TWNC.toN {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) : TWN W ps rs := by
  induction h with
  | empty => exact .empty
  | alloc _ hL hμ hW hv ih => exact .alloc ih hL hμ hW hv
  | immFrame T δ hα _ hadm hX hW hden hW' hv hds ih =>
      exact .immFrame T δ hα ih hadm hX hW hden hW' hv hds
  | reb r x _ hr hle hx hreb hden hβ _ hW hv ih =>
      exact .reb r x ih hr hle hx hreb hden hβ hW hv
  | rebDeep r x _ hr hch hcell hx hreb hden hβc hrec _ hW hv ih =>
      exact .rebDeep r x ih hr hch hcell hx hreb hden hβc hrec hW hv
  | mutFold _ hX hW hW' hv ih => exact .mutFold ih hX hW hW' hv
  | mutUnfold _ hW hX hW' hv ih => exact .mutUnfold ih hW hX hW' hv
  | free _ hW hv ih => exact .free ih hW hv
  | store _ hW hW' hv ih => exact .store ih hW hW' hv
  | immEnd r _ hr hc hX' hW' hv hps hrs ih => exact .immEnd r ih hr hc hX' hW' hv hps hrs
  | rebEnd r _ hr hle hreb hW hβ ih => exact .rebEnd r ih hr hle hreb hW hβ
  | rebEndDeep r _ hr hch hle hreb hW hβ ih => exact .rebEndDeep r ih hr hch hle hreb hW hβ

theorem TWNC.valid {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) : ResU.Valid W :=
  h.toN.valid

theorem TWNC.inv {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) : TI W ps rs := h.toN.inv

theorem TWNC.linLife {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) : LinLife W ps :=
  h.toN.linLife

theorem TWNC.properRoot {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) : ProperRoot ps :=
  h.toN.properRoot

/-- **The template invariant.** Every view of `ag(W)` at a root of the record carries the
template's witness there. -/
def TemplAt (W : WRes) (r : FrameRec) : Prop :=
  ∀ S l u, Root r S l u → ∀ a, AgW W a → ∀ ψ : CellU Loc Val, a.get l = some ψ →
    ψ.kind ≠ Kind.own → ∃ ζ, (tmpl r).get l = some ζ ∧ ψ.wit = ζ.wit

/-- `TemplAt` passes along a step whose views at the record's roots come back from the old world
with their witnesses. -/
theorem templAt_of_back {W W' : WRes} {r : FrameRec} (h : TemplAt W r)
    (back : ∀ S l u, Root r S l u → ∀ a', AgW W' a' →
      ∀ ψ : CellU Loc Val, a'.get l = some ψ → ψ.kind ≠ Kind.own →
      ∃ a, AgW W a ∧ ∃ ψ₀ : CellU Loc Val, a.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧
        ψ.wit = ψ₀.wit) : TemplAt W' r := by
  intro S l u hR a' ha' ψ e hk
  obtain ⟨a, ha, ψ₀, e₀, k₀, w₀⟩ := back S l u hR a' ha' ψ e hk
  obtain ⟨ζ, eζ, wζ⟩ := h S l u hR a ha ψ₀ e₀ k₀
  exact ⟨ζ, eζ, w₀.trans wζ⟩

theorem templAt_of_ag {W W' : WRes} {r : FrameRec} (t : ∀ a, AgW W' a → AgW W a)
    (h : TemplAt W r) : TemplAt W' r :=
  templAt_of_back h fun _ _ _ _ a' ha' ψ e hk => ⟨a', t a' ha', ψ, e, hk, rfl⟩

/-- `TemplAt` at the record of a new Imm Frame: no root has a view. -/
theorem templAt_frame {W X Z R W' : WRes} {ps rs ds : List FrameRec} {l : Loc} {v : Val}
    {α : Life} {T : VTy} {δ : BoCa.Lifetime.LSub} {hα : R.InStratum (LSet.singleton α).join}
    (hvW : ResU.Valid W)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R hα)) Z W')
    (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, R, T, δ⟩ d) (hTI : TI W ps rs)
    (hT : ∀ r ∈ rs, TemplAt W r) :
    ∀ r ∈ (⟨l, v, R, T, δ⟩ :: (ds ++ rs) : List FrameRec), TemplAt W' r := by
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW
  obtain ⟨eR, heR, -, hRl⟩ := frame_ex hX hW heW
  intro x hx
  have hcases : DescR ⟨l, v, R, T, δ⟩ x ∨ x ∈ rs := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl (DescR.refl _)
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p, -, hp⟩ := (hds x).mp hx; exact Or.inl ⟨p, hp⟩
      · exact Or.inr hx
  rcases hcases with ⟨p, hp⟩ | hx
  · intro S m u hR a ha ψ e hk
    have hex : ∀ eR', ExS R eR' → eR'.get m = some (CellU.ownOf u) := fun eR' heR' =>
      xpath_ex heR' hp.xpath hR.2 (by simp)
    have hml : m ≠ l := by
      rintro rfl; rw [hex eR heR] at hRl; cases hRl
    exact ((frame_new_root' hX hW hW' hvW hex hml ha).2.1 ψ e hk).elim
  · refine templAt_of_back (hT x hx) fun _ m u hm a' ha' ψ e hk => ?_
    obtain ⟨aW₁, haW₁, ψ₀, e₀, k₀, w₀⟩ :=
      frame_transfer hX hW hW' hvW (hTI.1.2.1 x hx m u hm.2) ha' e hk
    exact ⟨aW₁, haW₁, ψ₀, e₀, k₀, w₀⟩

/-- **`TWNC` keeps the template invariant at every record.** -/
theorem TWNC.templ {W : WRes} {ps rs : List FrameRec} (h : TWNC W ps rs) :
    ∀ r ∈ rs, TemplAt W r := by
  induction h with
  | empty => intro r hr; exact absurd hr (by simp)
  | alloc _ _ _ hW _ ih => exact fun r hr => templAt_of_ag (fun a ha => alloc_ag hW ha) (ih r hr)
  | immFrame T δ hα hW₀ hadm hX hW hden hW' hv hds ih =>
      exact templAt_frame hW₀.toN.valid hX hW hW' hds hW₀.toN.inv ih
  | @reb W W' c ps rs r₀ le s β hs x hW₀ hr₀ hle hx hreb hden hβ hc hW hv ih =>
      intro r hr
      have hTI := hW₀.toN.inv
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      refine fun S m u hR a ha ψ e hk => ?_
      rcases reb_like_back hle hreb hW haW ha e hk with ⟨ψ₀, e₀, k₀, w₀⟩ |
          ⟨u₀, q, hq, hown, hcl, hw⟩
      · obtain ⟨ζ, eζ, wζ⟩ := ih r hr S m u hR aW haW ψ₀ e₀ k₀
        exact ⟨ζ, eζ, w₀.trans wζ⟩
      · have e₁ : r = r₀ := hTI.1.2.2.1 r hr r₀ hr₀ m u u₀ hR.2 hown
        subst e₁ hc
        obtain ⟨ζ, eζ, wζ⟩ := canon_get hcl
        rw [CellU.wit_immOf] at wζ
        exact ⟨ζ, eζ, hw.trans wζ⟩
  | @rebDeep W W' c ps rs r₀ p₀ l₀ S₀ u₀ s w₀ hs β x hW₀ hr₀ hch₀ hcell hx hreb hden hβ _ _ hW
      hv ih =>
      intro r hr
      have hTI := hW₀.toN.inv
      obtain ⟨⟨h1, -, h3, h4, -, -⟩, -⟩ := hTI
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      have hR₀ := (h4 r₀ hr₀).1
      obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm haW hcell (CellU.kind_immOf _ _ _ _)
      rw [CellU.wit_immOf] at wχ
      obtain ⟨-, hw₀den, hw₀own, -, -⟩ :=
        h1 r₀ hr₀ p₀ l₀ S₀ u₀ hch₀ aW haW χ eχ (by rw [kχ]; simp)
      rw [wχ] at hw₀den hw₀own
      refine templAt_of_back (ih r hr) fun S m u hm a' ha' ψ e hk => ?_
      rcases reb_like_back hcell hreb hW haW ha' e hk with ⟨ψ₀, e₀, k₀, w₀'⟩ |
          ⟨u', q, hq, hown, hcl, -⟩
      · exact ⟨aW, haW, ψ₀, e₀, k₀, w₀'⟩
      · exfalso
        have e₂ : r = r₀ := h3 r hr r₀ hr₀ m _ _ hm.2 (hw₀own m _ hown)
        subst e₂
        obtain ⟨ζ, eζ, hpos⟩ := image_dom S₀ hden hw₀den hcl
        rw [hown] at eζ; cases Option.some.inj eζ
        obtain ⟨S', hS'⟩ := hpos rfl
        have hcS := hch₀.snoc hS' (hw₀own m u' hown)
        exact absurd (chain_unique_rec hR₀ (Chain.one hm.1 hm.2) hcS).1 (by simp)
  | mutFold hW₀ hX hW hW' _ ih =>
      exact fun r hr => templAt_of_ag (fun a ha => (mut_fold_ag hX hW hW' a).mpr ha) (ih r hr)
  | mutUnfold hW₀ hW hX hW' _ ih =>
      exact fun r hr => templAt_of_ag (fun a ha => (mut_fold_ag hX hW' hW a).mp ha) (ih r hr)
  | free hW₀ hW _ ih =>
      exact fun r hr => templAt_of_ag (fun a ha => (own_cell_ag hW a).mpr ha) (ih r hr)
  | store hW₀ hW hW' _ ih =>
      exact fun r hr => templAt_of_ag
        (fun a ha => (own_cell_ag hW a).mpr ((own_cell_ag hW' a).mp ha)) (ih r hr)
  | @immEnd W Y X' W' ps rs ps' rs' r₀ s hs hW₀ hr₀ hc hX' hW' hv hps hrs ih =>
      intro r hr
      have hTI := hW₀.toN.inv
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      have hrR : r ∈ rs := by
        obtain ⟨p, hp, hpd⟩ := (hrs r).mp hr
        exact (hTI.2.2.2.2.2.2.1 r).mpr ⟨p, ((hps p).mp hp).1, hpd⟩
      exact templAt_of_back (ih r hrR) fun _ m u hm a' ha' ψ e hk =>
        ⟨aW, haW, end_back hc hX' hW' haW ha' e hk⟩
  | rebEnd r₀ hW₀ hr₀ hle hreb hW hβ ih =>
      intro r hr
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      refine templAt_of_back (ih r hr) fun _ m u hm a' ha' ψ e hk => ?_
      obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
      rw [AgW.functional ha'' ha'] at hcomp
      obtain ⟨ψ₀, e₀, k₀, w₀⟩ := lift_view hcomp e hk
      exact ⟨aW, haW, ψ₀, e₀, k₀, w₀.symm⟩
  | rebEndDeep r₀ hW₀ hr₀ hch hle hreb hW hβ ih =>
      intro r hr
      obtain ⟨aW, haW⟩ := agW_of_valid hW₀.toN.valid
      refine templAt_of_back (ih r hr) fun _ m u hm a' ha' ψ e hk => ?_
      obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
      rw [AgW.functional ha'' ha'] at hcomp
      obtain ⟨ψ₀, e₀, k₀, w₀⟩ := lift_view hcomp e hk
      exact ⟨aW, haW, ψ₀, e₀, k₀, w₀.symm⟩

/-- **The canonical image agrees with every typed world holding the record.** At every `β`, the
views of `ag(W)` at the escrow's `own` cells carry the canonical image's witnesses (the input
`[TR]` 6.55 asks for). -/
theorem canon_escrowAgree {W : WRes} {ps rs : List FrameRec} {r : FrameRec}
    (hT : TWNC W ps rs) (hr : r ∈ rs) (hS : TmplSpec r (tmpl r)) (β : Life) :
    ∀ a, AgW W a → EscrowAgree r.R (canon r β) a := by
  intro a ha l v ψ ψf hown hψ hψf _ hkf
  obtain ⟨ζ, eζ, wζ⟩ := canon_get hψ
  obtain ⟨β₀, x₀, -, -, hden₀, -⟩ := hS
  have hR₀ := (hT.toN.inv.1.2.2.2.1 r hr).1
  obtain ⟨ζ', eζ', hpos⟩ := image_dom r.T hden₀ hR₀ eζ
  rw [hown] at eζ'; cases Option.some.inj eζ'
  obtain ⟨S, hS'⟩ := hpos rfl
  obtain ⟨ζ'', eζ'', w''⟩ := hT.templ r hr S l v ⟨hS', hown⟩ a ha ψf hψf hkf
  rw [eζ] at eζ''; cases Option.some.inj eζ''
  exact w''.trans wζ.symm

/-- **The re-entry's agreement at canonical images**: `RebReentryAgreeN` with `TWNC` for `TWN`
and the first entry's image the canonical one. The first entry's world is not read: the
agreement holds at every typed world holding the record. -/
def RebReentryAgreeC : Prop :=
  ∀ (W₀ W : WRes) (ps₀ ps : List FrameRec) (ls ls' : List SRec) (r : FrameRec) (s : LSet)
    (hs : r.R.InStratum s.join) (β : Life) (x : LifeVar),
    TWNC W₀ ps₀ (rsOf ls) → Tagged W₀ ps₀ ls → W₀.InStratum β → r ∈ rsOf ls →
    W₀.get r.le = some (CellU.immOf s r.v r.R hs) →
    ResU.Reb β r.R (canon r β) → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v (canon r β) →
    (∃ c, TmplSpec r c) → (∀ a, AgW W₀ a → EscrowAgree r.R (canon r β) a) →
    TWNC W ps (rsOf ls') → Tagged W ps ls' → (∀ y, y ∈ ls' ↔ y ∈ ls) →
    W.get r.le = some (CellU.immOf s r.v r.R hs) →
    ∀ a, AgW W a → EscrowAgree r.R (canon r β) a

theorem rebReentryAgreeC : RebReentryAgreeC := by
  intro _ W _ ps ls ls' r _ _ β _ _ _ _ hr _ _ _ hex _ hT _ hls _
  have hr' : r ∈ rsOf ls' := by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨y, (hls y).mpr hy, rfl⟩
  exact canon_escrowAgree hT hr' (tmpl_spec hex) β

end BoCa.Fig16.LogRel.Core.Chain.SI

end
