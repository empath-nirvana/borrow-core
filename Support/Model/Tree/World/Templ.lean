import Support.Model.Tree.World.TInv

/-!
# Templates carried along a re-reading

`SI/TWNC.lean`'s template invariant (`TemplAt`: every view at a root of a record carries the
record's template's witness there; `TemplDAt`: the same at a chain view's children) reads one
template per record. Over the tree a template is a typed image read at the current tree; when the
tree grows the world and every record are re-read (`TWNT.reread`). A template chosen anew at the
grown tree (`tmplT` at `(K′, Θ′)`) need not be the re-reading of the one chosen before: nothing
here shows a template determined by its specification (`TmplSpecT` reads the image's witnesses
only through `≤` and the code, and `●` composes `imm` cells at different lifetime sets).

Here the template is a **choice** carried by the typed world (`TChoice`, one function for record
templates and chain-view templates, `tmplT`'s and `tmplDT`'s argument order; `TWNT`'s index, in
`TreeWp/Records.lean`) and re-read along the re-reading: at `TWNT.reread`, the choice at the grown
tree takes each used argument's re-read to the re-read of its old template (`TcCarried`). The re-reading of a world is a function (`RR.func`), and
the aliasable walk of the re-read world is the re-read of the walk (`AgW.sim`), so

* `templAt_reread`: `TemplAt` holds after a re-reading at each re-read record;
* `templDAt_reread`: the same for `TemplDAt`;
* `TWNT.templ_reread`: both, at every record of `TWNT.reread`'s re-read list;
* `tcCarried_refl`: where nothing grows, the old choice is carried (the identity);
* `tcCarried_exists`: a carried choice exists when the used arguments' templates have re-readings
  and no two used arguments with distinct templates re-read to one (`TcCoherent`; it holds when the
  re-reading is injective on used escrows, `tcCoherent_of_inj`).

At `tc = tmplT K Θ`, `canonTc` and `canonDTc` are `canonT` and `canonDT` (`canonTc_tmplT`,
`canonDTc_tmplT`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-- At the `Classical` choice of the current tree, `canonTc` is `canonT`. -/
theorem canonTc_tmplT (Θ : CodeTy) (r : FrameRecT K) (β : Life) :
    canonTc (tmplT K Θ) r β = canonT K Θ r β := rfl

/-- At the `Classical` choice of the current tree, `canonDTc` is `canonDT`. -/
theorem canonDTc_tmplT (Θ : CodeTy) (S₀ : KTy) (u₀ : BoCa.Val) (w₀ : TRes K) (β : Life) :
    canonDTc (tmplT K Θ) S₀ u₀ w₀ β = canonDT K Θ S₀ u₀ w₀ β := rfl

/-- **`TemplAt` at a choice.** Every view of `ag(W)` at a root of `r` carries the witness of `r`'s
template there. -/
def TemplAtT (tc : TChoice K) (W : TRes K) (r : FrameRecT K) : Prop :=
  ∀ S l u, RootT r S l u → ∀ a, AgWT W a → ∀ ψ : TCell K, a.get l = some ψ →
    ψ.kind ≠ Kind.own → ∃ ζ, (tc r.R r.T r.v).get l = some ζ ∧ ψ.wit = ζ.wit

/-- **`TemplDAt` at a choice.** Every view of `ag(W)` at a child of a chain position carries the
witness of the template of the view at the position. -/
def TemplDAtT (tc : TChoice K) (W : TRes K) (r : FrameRecT K) : Prop :=
  ∀ p₀ l₀ S₀ u₀, ChainT r.R r.T r.v p₀ l₀ S₀ u₀ → ∀ m S u, ChainT r.R r.T r.v (some l₀) m S u →
    ∀ a, AgWT W a → ∀ ψ₀ ψ : TCell K, a.get l₀ = some ψ₀ → ψ₀.kind ≠ Kind.own →
      a.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ, (tc ψ₀.wit S₀ u₀).get m = some ζ ∧ ψ.wit = ζ.wit

/-! ### What a re-reading keeps -/

theorem RC.own_inv {Θ : LocTy} {l : BoCa.Loc} {ψ : TCell K} {u : BoCa.Val}
    (h : RC Θ (K' := K') l ψ (CellUT.ownOf u)) : ψ = CellUT.ownOf u := by
  cases h; rfl

/-- An `own` cell of the re-read resource is one of the old. -/
theorem RR.own_back {Θ : LocTy} {ρ : TRes K} {ρ' : TRes K'} (h : RR Θ ρ ρ') {l : BoCa.Loc}
    {u : BoCa.Val} (e : ρ'.get l = some (CellUT.ownOf u)) : ρ.get l = some (CellUT.ownOf u) := by
  obtain ⟨ψ, eψ, hr⟩ := h.get_some' e
  rw [eψ, RC.own_inv hr]

/-- A chain of the re-read escrow is a chain of the old. -/
theorem ChainT.rr_back {Θ : LocTy} {R : TRes K} {R' : TRes K'} (h : RR Θ R R') {T : KTy}
    {v : BoCa.Val} {p : Option BoCa.Loc} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val}
    (hc : ChainT R' T v p l S u) : ChainT R T v p l S u := by
  induction hc with
  | one hp e => exact .one hp (RR.own_back h e)
  | step hp e _ ih => exact .step hp (RR.own_back h e) ih

theorem RootT.rr_back {Θ' : CodeTy} {r : FrameRecT K} {r' : FrameRecT K'} (h : RecRR Θ' r r')
    {S : KTy} {l : BoCa.Loc} {u : BoCa.Val} (hr : RootT r' S l u) : RootT r S l u := by
  obtain ⟨-, hv, hT, hR⟩ := h
  obtain ⟨hp, e⟩ := hr
  rw [hv, hT] at hp
  exact ⟨hp, RR.own_back hR e⟩

/-- **The aliasable walk of a re-read world is the re-read of the walk**, cell by cell: a view of
the re-read world is the re-read of a view of the old one, its witness re-read. -/
theorem agW_rr_back {Θ : LocTy} {W : TRes K} {W' : TRes K'} (hv : ResUT.Valid W) (h : RR Θ W W')
    {a' : TRes K'} (ha' : AgWT W' a') :
    ∃ a, AgWT W a ∧ ∀ l (ψ' : TCell K'), a'.get l = some ψ' →
      ∃ ψ : TCell K, a.get l = some ψ ∧ ψ'.kind = ψ.kind ∧ RR Θ ψ.wit ψ'.wit := by
  obtain ⟨a, ha⟩ := agW_of_valid hv
  obtain ⟨σ', hσ', hs⟩ := WitRel.AgW.sim (W := rrRel Θ K K') ha W' h.rsim
  obtain rfl := AgWT.functional hσ' ha'
  refine ⟨a, ha, fun l ψ' e => ?_⟩
  have hl := hs l
  rw [e] at hl
  cases ea : a.get l with
  | none => rw [ea] at hl; cases hl
  | some ψ =>
      rw [ea] at hl
      cases hl with
      | some hsim => exact ⟨ψ, rfl, hsim.1, hsim.2.2⟩

/-! ### The invariants across a re-reading -/

/-- **`TemplAt` across a re-reading.** -/
theorem templAt_reread {Θ' : CodeTy} {tc : TChoice K} {tc' : TChoice K'} {W : TRes K}
    {W' : TRes K'} {r : FrameRecT K} {r' : FrameRecT K'} (hv : ResUT.Valid W)
    (hW : RR (sem Θ') W W') (hr : RecRR Θ' r r')
    (htc : RR (sem Θ') (tc r.R r.T r.v) (tc' r'.R r'.T r'.v)) (h : TemplAtT tc W r) :
    TemplAtT tc' W' r' := by
  intro S l u hroot a' ha' ψ' e hk
  obtain ⟨a, ha, back⟩ := agW_rr_back hv hW ha'
  obtain ⟨ψ, eψ, kψ, wψ⟩ := back l ψ' e
  obtain ⟨ζ, eζ, wζ⟩ := h S l u (hroot.rr_back hr) a ha ψ eψ (kψ ▸ hk)
  obtain ⟨ζ', eζ', hζ⟩ := htc.get_some eζ
  refine ⟨ζ', eζ', ?_⟩
  rw [wζ] at wψ
  exact RR.func wψ hζ.wit

/-- **`TemplDAt` across a re-reading.** -/
theorem templDAt_reread {Θ' : CodeTy} {tc : TChoice K} {tc' : TChoice K'} {W : TRes K}
    {W' : TRes K'} {rs : List (FrameRecT K)} {r : FrameRecT K} {r' : FrameRecT K'}
    (hv : ResUT.Valid W) (hW : RR (sem Θ') W W') (hr : RecRR Θ' r r') (hrs : r ∈ rs)
    (htc : TcCarried Θ' W rs tc tc') (h : TemplDAtT tc W r) : TemplDAtT tc' W' r' := by
  obtain ⟨-, hv', hT, hR⟩ := hr
  intro p₀ l₀ S₀ u₀ hc₀ m S u hc a' ha' ψ₀' ψ' e₀ k₀ e k
  rw [hv', hT] at hc₀ hc
  have hc₀' := hc₀.rr_back hR
  obtain ⟨a, ha, back⟩ := agW_rr_back hv hW ha'
  obtain ⟨ψ₀, eψ₀, kψ₀, wψ₀⟩ := back l₀ ψ₀' e₀
  obtain ⟨ψ, eψ, kψ, wψ⟩ := back m ψ' e
  obtain ⟨ζ, eζ, wζ⟩ := h p₀ l₀ S₀ u₀ hc₀' m S u (hc.rr_back hR) a ha ψ₀ ψ eψ₀ (kψ₀ ▸ k₀) eψ
    (kψ ▸ k)
  have hused : UsedT W rs ψ₀.wit S₀ u₀ :=
    Or.inr ⟨r, hrs, p₀, l₀, hc₀', a, ha, ψ₀, eψ₀, kψ₀ ▸ k₀, rfl⟩
  obtain ⟨ζ', eζ', hζ⟩ := (htc _ _ _ hused _ wψ₀).get_some eζ
  refine ⟨ζ', eζ', ?_⟩
  rw [wζ] at wψ
  exact RR.func wψ hζ.wit

/-- `TcCarried` gives the record's template premise of `templAt_reread`. -/
theorem TcCarried.rec {Θ' : CodeTy} {tc : TChoice K} {tc' : TChoice K'} {W : TRes K}
    {rs : List (FrameRecT K)} (htc : TcCarried Θ' W rs tc tc') {r : FrameRecT K} (hr : r ∈ rs)
    {r' : FrameRecT K'} (hrr : RecRR Θ' r r') :
    RR (sem Θ') (tc r.R r.T r.v) (tc' r'.R r'.T r'.v) := by
  obtain ⟨-, hv, hT, hR⟩ := hrr
  rw [hv, hT]
  exact htc _ _ _ (Or.inl ⟨r, hr, rfl, rfl, rfl⟩) _ hR

/-! ### Where nothing grows; existence -/

/-- **Where nothing grows the choice is carried unchanged**: at `K′ = K`, `Θ′ = Θ`, a used
argument's re-read is itself (a covered resource re-reads to itself, `RR.refl`, and re-reading is
a function), and so is its template when covered. -/
theorem tcCarried_refl {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {rs : List (FrameRecT K)}
    (hcovU : ∀ R T v, UsedT W rs R T v → CovR (sem Θ) K R)
    (hcovT : ∀ R T v, UsedT W rs R T v → CovR (sem Θ) K (tc R T v)) :
    TcCarried (K' := K) Θ W rs tc tc := by
  intro R T v hu R' hR
  obtain rfl : R = R' := RR.func (RR.refl (hcovU R T v hu)) hR
  exact RR.refl (hcovT R T v hu)

/-- **Coherence**: two used arguments at one code and value whose escrows re-read to one escrow
have templates that re-read to one template. -/
def TcCoherent (Θ' : CodeTy) (W : TRes K) (rs : List (FrameRecT K)) (tc : TChoice K) : Prop :=
  ∀ R₁ R₂ T v, UsedT W rs R₁ T v → UsedT W rs R₂ T v → ∀ R' : TRes K',
    RR (sem Θ') R₁ R' → RR (sem Θ') R₂ R' → ∀ c₁ c₂ : TRes K',
    RR (sem Θ') (tc R₁ T v) c₁ → RR (sem Θ') (tc R₂ T v) c₂ → c₁ = c₂

/-- Coherence holds when the re-reading is injective on used escrows. -/
theorem tcCoherent_of_inj {Θ' : CodeTy} {W : TRes K} {rs : List (FrameRecT K)} {tc : TChoice K}
    (hinj : ∀ R₁ R₂ T v, UsedT W rs R₁ T v → UsedT W rs R₂ T v → ∀ R' : TRes K',
      RR (sem Θ') R₁ R' → RR (sem Θ') R₂ R' → R₁ = R₂) :
    TcCoherent (K' := K') Θ' W rs tc := by
  intro R₁ R₂ T v h₁ h₂ R' e₁ e₂ c₁ c₂ f₁ f₂
  obtain rfl := hinj R₁ R₂ T v h₁ h₂ R' e₁ e₂
  exact RR.func f₁ f₂

open Classical in
/-- **A carried choice exists** when each used template has a re-reading and the choice is
coherent. Off the used arguments' re-reads the new choice is the `Classical` one at the grown
tree. -/
theorem tcCarried_exists {Θ' Θ'' : CodeTy} {tc : TChoice K} {W : TRes K}
    {rs : List (FrameRecT K)}
    (hex : ∀ R T v, UsedT W rs R T v → ∃ c : TRes K', RR (sem Θ') (tc R T v) c)
    (hcoh : TcCoherent (K' := K') Θ' W rs tc) :
    ∃ tc' : TChoice K', TcCarried Θ' W rs tc tc' := by
  let pre : TRes K' → KTy → BoCa.Val → Prop := fun R' T v =>
    ∃ R, UsedT W rs R T v ∧ RR (sem Θ') R R'
  let tc' : TChoice K' := fun R' T v =>
    if h : pre R' T v then (hex _ T v h.choose_spec.1).choose else tmplT K' Θ'' R' T v
  refine ⟨tc', fun R T v hu R' hR => ?_⟩
  have hp : pre R' T v := ⟨R, hu, hR⟩
  have e : tc' R' T v = (hex _ T v hp.choose_spec.1).choose := dif_pos hp
  rw [e]
  obtain ⟨c, hc⟩ := hex R T v hu
  have := hcoh _ _ T v hp.choose_spec.1 hu R' hp.choose_spec.2 hR _ c
    (hex _ T v hp.choose_spec.1).choose_spec hc
  rw [this]; exact hc


/-- **The template invariants across `TWNT.reread`**: given them at every record of the old
list, they hold at every record of the re-read list. -/
theorem TWNT.templ_reread {Θ' : CodeTy} {tc : TChoice K} {tc' : TChoice K'} {W : TRes K}
    {W' : TRes K'} {rs : List (FrameRecT K)} {rs' : List (FrameRecT K')} (hv : ResUT.Valid W)
    (hW : RR (sem Θ') W W') (hrs : List.Forall₂ (RecRR Θ') rs rs')
    (htc : TcCarried Θ' W rs tc tc')
    (hT : ∀ r ∈ rs, TemplAtT tc W r) (hD : ∀ r ∈ rs, TemplDAtT tc W r) :
    (∀ r' ∈ rs', TemplAtT tc' W' r') ∧ (∀ r' ∈ rs', TemplDAtT tc' W' r') := by
  refine ⟨fun r' hr' => ?_, fun r' hr' => ?_⟩
  · obtain ⟨r, hr, hrr⟩ := forall₂_mem_right hrs hr'
    exact templAt_reread hv hW hrr (htc.rec hr hrr) (hT r hr)
  · obtain ⟨r, hr, hrr⟩ := forall₂_mem_right hrs hr'
    exact templDAt_reread hv hW hrr hr htc (hD r hr)

end BoCa.Fig16.Tree.Wp

end
