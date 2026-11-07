import Support.Model.Tree.World.FlatLs
import Support.Model.Tree.World.Records
import Support.Model.Tree.Port.UpdateFrame

/-!
# Row 5.27's `↭` read across a re-reading, masked at a run's own records

`[spec §62]`. `[TR]` p. 6's `wp` (row 5.33) asks of a run from `ρ` to `ρ′` that `ρ ↭ ρ′ ● ρ⁺`, and
row 5.27's `↭` (`ResUT.UpdV`, `Tree/Port/Cells.lean`) reads the two flattenings at every location:

> `ρ₁ ↭ ρ₂` iff `✓ρ₁`, `✓ρ₂`, and for all `ℓ`: `⦇ρ₁⦈(ℓ) = imm(ᾱ, v, ρ) ⇔ ⦇ρ₂⦈(ℓ) = imm(ᾱ, v, ρ)`,
> and `⦇ρ₁⦈(ℓ) = mut(β, _, _, P̂) ⇔ ⦇ρ₂⦈(ℓ) = mut(β, _, _, P̂)`.

Over the tree world a run starts at a world `w₀` and ends at an extension `w′`, so `ρ` and `ρ′`
are resources of two carriers. `UpdX` reads `↭` across the re-reading from `K` to `K′`: an `imm`
cell of the one flattening is an `imm` cell of the other with the same lifetime set and value and
the re-read witness, and a `mut` cell of the one is a `mut` cell of the other with the re-read
`β̄` (`XCell`). At the identity re-reading its `imm` clause is row 5.27's (`updX_refl_imm`), and
`UpdV` gives it (`UpdX.of_updV`).

**The masks.** A run that leaves a lend it opened open at a stop turns an `own` cell into the lend
cell `ℓ ↦ imm(…)` and hands out views of the escrow, and a run that ends such a lend turns them
back. `↭` refuses both (`lend_open_needs_mask`). Each side of `UpdX` is masked at a set of
locations (`E`, `E′`): there it reads nothing. A run's masks are the lent locations and escrow
locations of the records it owns at its start and at its end (`recMask`), and nothing else.

**A `mut` cell's invariant** is not a clause of `UpdX`: it is determined by the location typing.
In a world with one `mut` cell per location at any depth (`MutOne`, kept by `TWNT`), every `mut`
cell of the flattening is a stored cell, and a covered stored cell's `P̂` is its location's code
read at the world on `Res_β̄` (`flat_mut_inv`, `World/UpdXInv.lean`). So row 5.27's "same `P̂`"
is "the same code at `ℓ` on both sides" (`InvKept`), and with `UpdX`'s `β̄` clause it gives the
printed `mut` clause with `P̂` re-read as `RC.mut` re-reads it (`UpdX.inv`); at the identity
re-reading it is the printed clause (`updX_refl_mut`).

What is proved of it: re-reading is an update (`UpdX.of_rr`) and updates compose (`UpdX.trans`).
The frame step `EndT` reads is `UpdA.frame` (`World/UpdAFrame.lean`), along the walks.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' K'' : WCactus}

/-! ### Locations a resource holds nothing at -/

/-- Locations no flattening of `a` holds. -/
def NoneAt (P : BoCa.Loc → Prop) (a : TRes K) : Prop :=
  ∀ τ, ResUT.Flat a τ → ∀ x, P x → τ.get x = none

/-- The locations `FdEsc` reads: the lent location and the escrow's exclusive part. -/
def escLocs (l : BoCa.Loc) (R : TRes K) (x : BoCa.Loc) : Prop :=
  x = l ∨ ∃ eR, ExST R eR ∧ (eR.get x).isSome

theorem NoneAt.mono {P P' : BoCa.Loc → Prop} (hP : ∀ x, P' x → P x) {a : TRes K}
    (h : NoneAt P a) : NoneAt P' a :=
  fun τ hτ x hx => h τ hτ x (hP x hx)

/-- **Re-reading keeps the locations a flattening holds.** -/
theorem NoneAt.rr {Θ : LocTy} (hE : K.Ext K') {P : BoCa.Loc → Prop} {a : TRes K} {a' : TRes K'}
    (hv : ResUT.Valid a) (hr : RR Θ a a') (h : NoneAt P a) : NoneAt P a' := by
  intro τ' hτ' x hx
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨σ', hσ', hs⟩ := ResUT.Flat.rrLs hE hτ hr
  obtain rfl := ResUT.Flat.functional hσ' hτ'
  have hl := hs x
  rw [h τ hτ x hx] at hl
  revert hl
  cases σ'.get x with
  | none => intro _; rfl
  | some _ => intro hl; cases hl

/-- **A part of a valid composite holds nothing where the composite holds nothing.** -/
theorem NoneAt.of_compS_left {P : BoCa.Loc → Prop} {a b c : TRes K} (hc : ResUT.CompS a b c)
    (hv : ResUT.Valid c) (h : NoneAt P c) : NoneAt P a := by
  intro τa hτa x hx
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨σ₁, σ₂, h₁, h₂, hσ⟩ := BoLo.flat_compR hc hτ
  obtain rfl := ResUT.Flat.functional h₁ hτa
  have hp := hσ.2 x
  rw [h τ hτ x hx] at hp
  revert hp
  cases σ₁.get x <;> cases σ₂.get x <;> simp [G.OptComp]

theorem NoneAt.of_compS_right {P : BoCa.Loc → Prop} {a b c : TRes K} (hc : ResUT.CompS a b c)
    (hv : ResUT.Valid c) (h : NoneAt P c) : NoneAt P b :=
  NoneAt.of_compS_left (ResUT.CompS.comm hc) hv h

/-! ### The cells `↭` compares -/

/-- **The cells `↭` compares, across a re-reading**: the tag kept, the lifetime set re-read
(`rlsOf`: an `imm` cell's kept, a `mut` cell's `β̄` read as `min_{K′} β̄`), and of an `imm` cell
the value kept and the witness re-read. -/
def XCell (Θ : LocTy) (ψ : TCell K) (ψ' : TCell K') : Prop :=
  ψ'.kind = ψ.kind ∧ ψ'.lsOf = rlsOf K' ψ.kind ψ.lsOf ∧
    (ψ.kind = Kind.imm → ψ'.erase = ψ.erase ∧ RR Θ ψ.wit ψ'.wit)

/-- `↭` at one location of the two flattenings, each side masked by a proposition. -/
def XOpt (Θ : LocTy) (E E' : Prop) (o : Option (TCell K)) (o' : Option (TCell K')) : Prop :=
  (∀ ψ, o = some ψ → ψ.kind ≠ Kind.own → ¬ E → ¬ E' ∧ ∃ ψ', o' = some ψ' ∧ XCell Θ ψ ψ') ∧
  (∀ ψ', o' = some ψ' → ψ'.kind ≠ Kind.own → ¬ E' → ¬ E ∧ ∃ ψ, o = some ψ ∧ XCell Θ ψ ψ')

/-- **`ρ ↭ ρ′` across a re-reading at `Θ`, masked at `E` and `E′`.** Both sides valid (each has a
flattening), and the two flattenings related by `XOpt` at every location.

**Departure (D1, `docs/new-core/scope-781.md` §8).** Row 5.27/5.33's `↭` is masked at the run's
own records' lent and escrow locations (`recMask`) and read across the re-reading `w₀ → w′`. A lend
left open at a stop turns `own` into the lend cell and hands out the escrow's views
(`lend_open_admitted`); without the mask that end is refused (`lend_open_needs_mask`). Unmasked
locations read row 5.27's `imm` clause exactly (`updX_refl_imm`), and printed `UpdV` gives `UpdX`
(`UpdX.of_updV`). The printed technique not built: `↭` unmasked across a lend left open, as 6.39
uses it. -/
def UpdX (Θ : LocTy) (E E' : BoCa.Loc → Prop) (ρ : TRes K) (ρ' : TRes K') : Prop :=
  ∃ σ σ', ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ ∀ l, XOpt Θ (E l) (E' l) (σ.get l) (σ'.get l)

theorem LsSim.xcell {Θ : LocTy} {ψ : TCell K} {ψ' : TCell K'} (h : LsSim Θ ψ' ψ) :
    XCell Θ ψ ψ' :=
  ⟨h.1, h.2.2.2, fun _ => ⟨h.2.1, h.2.2.1⟩⟩

theorem XCell.trans {Θ₁ Θ₂ : LocTy} (hE : K'.Ext K'') {ψ : TCell K} {ψ' : TCell K'}
    {ψ'' : TCell K''} (h : XCell Θ₁ ψ ψ') (h' : XCell Θ₂ ψ' ψ'') : XCell Θ₂ ψ ψ'' := by
  refine ⟨h'.1.trans h.1, ?_, fun hk => ?_⟩
  · rw [h'.2.1, h.1, h.2.1]
    cases ψ.kind <;> cases ψ.lsOf <;> simp [rlsOf, WCactus.minS_minS hE]
  · obtain ⟨e₁, r₁⟩ := h.2.2 hk
    obtain ⟨e₂, r₂⟩ := h'.2.2 (h.1.trans hk)
    exact ⟨e₂.trans e₁, RR.trans_retype hE r₁ r₂⟩

/-! ### Re-reading is an update -/

/-- **A re-reading is an update**, at any masks equal on the two sides. -/
theorem UpdX.of_rr {Θ : LocTy} (hE : K.Ext K') (E : BoCa.Loc → Prop) {ρ : TRes K}
    {ρ' : TRes K'} (hv : ResUT.Valid ρ) (hr : RR Θ ρ ρ') : UpdX Θ E E ρ ρ' := by
  obtain ⟨σ, hσ⟩ := hv
  obtain ⟨σ', hσ', hs⟩ := ResUT.Flat.rrLs hE hσ hr
  refine ⟨σ, σ', hσ, hσ', fun l => ⟨fun ψ e _ hE₀ => ⟨hE₀, ?_⟩, fun ψ' e _ hE₀ => ⟨hE₀, ?_⟩⟩⟩
  · have hl := hs l
    rw [e] at hl
    revert hl
    cases σ'.get l with
    | none => intro hl; cases hl
    | some ψ' => intro hl; cases hl with | some h => exact ⟨ψ', rfl, LsSim.xcell h⟩
  · have hl := hs l
    rw [e] at hl
    revert hl
    cases σ.get l with
    | none => intro hl; cases hl
    | some ψ => intro hl; cases hl with | some h => exact ⟨ψ, rfl, LsSim.xcell h⟩

/-! ### Updates compose -/

theorem XOpt.trans {Θ₁ Θ₂ : LocTy} (hE : K'.Ext K'') {E E' E'' : Prop} {o : Option (TCell K)}
    {o' : Option (TCell K')} {o'' : Option (TCell K'')} (h : XOpt Θ₁ E E' o o')
    (h' : XOpt Θ₂ E' E'' o' o'') : XOpt Θ₂ E E'' o o'' := by
  refine ⟨fun ψ e hk hE₀ => ?_, fun ψ'' e hk hE₀ => ?_⟩
  · obtain ⟨hE₁, ψ', e', hx⟩ := h.1 ψ e hk hE₀
    obtain ⟨hE₂, ψ'', e'', hx'⟩ := h'.1 ψ' e' (hx.1 ▸ hk) hE₁
    exact ⟨hE₂, ψ'', e'', hx.trans hE hx'⟩
  · obtain ⟨hE₁, ψ', e', hx'⟩ := h'.2 ψ'' e hk hE₀
    obtain ⟨hE₂, ψ, e₀, hx⟩ := h.2 ψ' e' (fun c => hk (hx'.1.trans c)) hE₁
    exact ⟨hE₂, ψ, e₀, hx.trans hE hx'⟩

/-- **Updates compose**, along an extension, the middle masks matching. -/
theorem UpdX.trans {Θ₁ Θ₂ : LocTy} (hE : K'.Ext K'') {E E' E'' : BoCa.Loc → Prop}
    {ρ : TRes K} {ρ' : TRes K'} {ρ'' : TRes K''} (h : UpdX Θ₁ E E' ρ ρ')
    (h' : UpdX Θ₂ E' E'' ρ' ρ'') : UpdX Θ₂ E E'' ρ ρ'' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  obtain ⟨τ', σ'', hτ', hσ'', hx'⟩ := h'
  obtain rfl := ResUT.Flat.functional hσ' hτ'
  exact ⟨σ, σ'', hσ, hσ'', fun l => (hx l).trans hE (hx' l)⟩

/-- **Masking a location on both sides keeps an update.** -/
theorem UpdX.widen {Θ : LocTy} {E E' : BoCa.Loc → Prop} (F : BoCa.Loc → Prop) {ρ : TRes K}
    {ρ' : TRes K'} (h : UpdX Θ E E' ρ ρ') :
    UpdX Θ (fun l => E l ∨ F l) (fun l => E' l ∨ F l) ρ ρ' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  refine ⟨σ, σ', hσ, hσ', fun l => ⟨fun ψ e hk hE₀ => ?_, fun ψ' e hk hE₀ => ?_⟩⟩
  · obtain ⟨h₁, ψ', e', hc⟩ := (hx l).1 ψ e hk (fun c => hE₀ (Or.inl c))
    exact ⟨fun c => c.elim h₁ (fun f => hE₀ (Or.inr f)), ψ', e', hc⟩
  · obtain ⟨h₁, ψ, e₀, hc⟩ := (hx l).2 ψ' e hk (fun c => hE₀ (Or.inl c))
    exact ⟨fun c => c.elim h₁ (fun f => hE₀ (Or.inr f)), ψ, e₀, hc⟩

/-- The masks may be replaced by equal ones. -/
theorem UpdX.congr {Θ : LocTy} {E E' F F' : BoCa.Loc → Prop} (hF : ∀ l, F l ↔ E l)
    (hF' : ∀ l, F' l ↔ E' l) {ρ : TRes K} {ρ' : TRes K'} (h : UpdX Θ E E' ρ ρ') :
    UpdX Θ F F' ρ ρ' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  refine ⟨σ, σ', hσ, hσ', fun l => ⟨fun ψ e hk hE₀ => ?_, fun ψ' e hk hE₀ => ?_⟩⟩
  · obtain ⟨h₁, rest⟩ := (hx l).1 ψ e hk (fun c => hE₀ ((hF l).mpr c))
    exact ⟨fun c => h₁ ((hF' l).mp c), rest⟩
  · obtain ⟨h₁, rest⟩ := (hx l).2 ψ' e hk (fun c => hE₀ ((hF' l).mpr c))
    exact ⟨fun c => h₁ ((hF l).mp c), rest⟩

/-! ### `○` with an `own` operand -/

/-- `ψ₁ ○ ψ₂` with `ψ₁` an `own` cell and the composite not: the composite is `ψ₂`. -/
theorem CellUT.CompR.eq_right_of_own {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    (h₁ : ψ₁.kind = Kind.own) (hk : ψ.kind ≠ Kind.own) : ψ = ψ₂ := by
  rcases h.inv with ⟨rfl, rfl⟩ | ⟨k, -⟩ | ⟨s, t, _, _, v, ρ, hs, ht, P, Q, hP, hQ, rfl, -, -⟩ |
      ⟨rfl, -, k₁⟩ | ⟨rfl, -, -⟩ | ⟨-, k₁, -⟩ | ⟨-, k₁, -⟩
  · exact absurd h₁ hk
  · exact absurd h₁ (by rw [(CellUT.CompatS.kinds k).1]; exact fun c => Kind.noConfusion c)
  · exact absurd h₁ (by simp)
  · exact absurd h₁ k₁
  · rfl
  · rw [h₁] at k₁; cases k₁
  · rw [h₁] at k₁; cases k₁

/-! ### The masks of a run -/

/-- **The locations of a resource's exclusive part**, read off its cells: an `own` or `mut` cell's
location, and those of a `mut` cell's witness. The domain of `ex(ρ)` wherever `ex(ρ)` is defined
(`ExDom.of_exST`); unlike it, kept and reflected by re-reading (`ExDom.rr_iff`). -/
inductive ExDom : TRes K → BoCa.Loc → Prop where
  | top {ρ : TRes K} {x : BoCa.Loc} {ψ : TCell K} (e : ρ.get x = some ψ)
      (hk : ψ.kind ≠ Kind.imm) : ExDom ρ x
  | deep {ρ : TRes K} {x y : BoCa.Loc} {ψ : TCell K} (e : ρ.get y = some ψ)
      (hk : ψ.kind = Kind.mut) (h : ExDom ψ.wit x) : ExDom ρ x

theorem ExDom.rr {Θ : LocTy} {ρ : TRes K} {x : BoCa.Loc} (h : ExDom ρ x) :
    ∀ {ρ' : TRes K'}, RR Θ ρ ρ' → ExDom ρ' x := by
  induction h with
  | top e hk =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      exact .top e' (by rw [hc.kind]; exact hk)
  | deep e hk _ ih =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      exact .deep e' (by rw [hc.kind]; exact hk) (ih hc.wit)

theorem ExDom.rr_back {Θ : LocTy} {ρ' : TRes K'} {x : BoCa.Loc} (h : ExDom ρ' x) :
    ∀ {ρ : TRes K}, RR Θ ρ ρ' → ExDom ρ x := by
  induction h with
  | top e hk =>
      intro ρ hr
      obtain ⟨ψ, e₀, hc⟩ := hr.get_some' e
      exact .top e₀ (by rw [← hc.kind]; exact hk)
  | deep e hk _ ih =>
      intro ρ hr
      obtain ⟨ψ, e₀, hc⟩ := hr.get_some' e
      exact .deep e₀ (by rw [← hc.kind]; exact hk) (ih hc.wit)

theorem ExDom.rr_iff {Θ : LocTy} {ρ : TRes K} {ρ' : TRes K'} (hr : RR Θ ρ ρ') (x : BoCa.Loc) :
    ExDom ρ x ↔ ExDom ρ' x :=
  ⟨fun h => h.rr hr, fun h => h.rr_back hr⟩

/-- **The masks of a run owning the records `O`**: each record's lent location and the
locations of its escrow's exclusive part. -/
def recMask (O : List (FrameRecT K)) (x : BoCa.Loc) : Prop :=
  ∃ p ∈ O, x = p.le ∨ ExDom p.R x

/-- Where exactly one of two masks holds. -/
def MaskDiff (E E' : BoCa.Loc → Prop) (x : BoCa.Loc) : Prop := (E x ∧ ¬ E' x) ∨ (E' x ∧ ¬ E x)

theorem recMask_rr {Θ' : CodeTy} {O : List (FrameRecT K)} {O' : List (FrameRecT K')}
    (h : List.Forall₂ (RecRR Θ') O O') (x : BoCa.Loc) : recMask O x ↔ recMask O' x := by
  induction h with
  | nil => simp [recMask]
  | cons hr _ ih =>
      simp only [recMask, List.mem_cons, exists_eq_or_imp] at ih ⊢
      rw [ih, hr.1, ExDom.rr_iff hr.2.2.2 x]

theorem recMask_append {O₁ O₂ : List (FrameRecT K)} (x : BoCa.Loc) :
    recMask (O₁ ++ O₂) x ↔ recMask O₁ x ∨ recMask O₂ x := by
  simp only [recMask, List.mem_append]
  constructor
  · rintro ⟨p, hp | hp, h⟩
    · exact Or.inl ⟨p, hp, h⟩
    · exact Or.inr ⟨p, hp, h⟩
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · exact ⟨p, Or.inl hp, h⟩
    · exact ⟨p, Or.inr hp, h⟩

theorem NoneAt.or {P Q : BoCa.Loc → Prop} {a : TRes K} (hP : NoneAt P a) (hQ : NoneAt Q a) :
    NoneAt (fun x => P x ∨ Q x) a :=
  fun τ hτ x hx => hx.elim (hP τ hτ x) (hQ τ hτ x)

theorem NoneAt.of_false {P : BoCa.Loc → Prop} (h : ∀ x, ¬ P x) (a : TRes K) : NoneAt P a :=
  fun _ _ x hx => absurd hx (h x)

/-- Where only one of the outer masks holds, only one of the inner or of the second holds. -/
theorem maskDiff_trans {E₀ E₁ E₂ : BoCa.Loc → Prop} (x : BoCa.Loc) (h : MaskDiff E₀ E₂ x) :
    MaskDiff E₀ E₁ x ∨ MaskDiff E₁ E₂ x := by
  unfold MaskDiff at *
  by_cases h₁ : E₁ x <;> tauto

/-! ### Against row 5.27 -/

/-- A flattening of a covered world is related to itself (its witnesses covered). -/
theorem flat_lsSim_self {Θ : LocTy} {ρ σ : TRes K} (hc : CovR Θ K ρ) (hσ : ResUT.Flat ρ σ) :
    LsRSim (K' := K) Θ σ σ := by
  obtain ⟨σ', hσ', hs⟩ := ResUT.Flat.rrLs (WCactus.Ext.refl K) hσ (RR.refl hc)
  obtain rfl := ResUT.Flat.functional hσ' hσ
  exact hs

/-- **Row 5.27 gives `UpdX` at the identity re-reading**, any masks equal on the two sides. -/
theorem UpdX.of_updV {Θ : LocTy} (E : BoCa.Loc → Prop) {ρ ρ' : TRes K} (hc : CovR Θ K ρ)
    (hc' : CovR Θ K ρ') (h : ResUT.UpdV ρ ρ') : UpdX (K' := K) Θ E E ρ ρ' := by
  obtain ⟨hu, ⟨σ, hσ⟩, ⟨σ', hσ'⟩⟩ := h
  have hs := flat_lsSim_self hc hσ
  have hs' := flat_lsSim_self hc' hσ'
  have self : ∀ {τ : TRes K} (_ : LsRSim (K' := K) Θ τ τ) {l : BoCa.Loc} {ψ : TCell K},
      τ.get l = some ψ → LsSim (K' := K) Θ ψ ψ := fun hτ l ψ e => by
    have := hτ l; rw [e] at this; cases this with | some h => exact h
  refine ⟨σ, σ', hσ, hσ', fun l => ⟨fun ψ e hk hE₀ => ⟨hE₀, ?_⟩, fun ψ' e hk hE₀ => ⟨hE₀, ?_⟩⟩⟩
  · rcases CellUT.rep' ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, _, v, χ, hh, P, hw, rfl⟩
    · exact absurd rfl hk
    · have := (hu.1 l s v χ hh).mp ((ResUT.flatAt_iff hσ _ _).mpr e)
      exact ⟨_, (ResUT.flatAt_iff hσ' _ _).mp this, LsSim.xcell (self hs e)⟩
    · obtain ⟨v', χ', hh', hw', hg⟩ := (hu.2 l b P).mp ⟨v, χ, hh, hw, (ResUT.flatAt_iff hσ _ _).mpr e⟩
      refine ⟨_, (ResUT.flatAt_iff hσ' _ _).mp hg, rfl, ?_, fun c => by simp at c⟩
      simp [rlsOf, K.minS_of_anti (Fact.out : K.Anti b)]
  · rcases CellUT.rep' ψ' with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, _, v, χ, hh, P, hw, rfl⟩
    · exact absurd rfl hk
    · have := (hu.1 l s v χ hh).mpr ((ResUT.flatAt_iff hσ' _ _).mpr e)
      exact ⟨_, (ResUT.flatAt_iff hσ _ _).mp this, LsSim.xcell (self hs' e)⟩
    · obtain ⟨v', χ', hh', hw', hg⟩ :=
        (hu.2 l b P).mpr ⟨v, χ, hh, hw, (ResUT.flatAt_iff hσ' _ _).mpr e⟩
      refine ⟨_, (ResUT.flatAt_iff hσ _ _).mp hg, rfl, ?_, fun c => by simp at c⟩
      simp [rlsOf, K.minS_of_anti (Fact.out : K.Anti b)]

/-- An `imm` cell is determined by its lifetime set, value and witness. -/
theorem imm_eq_of {ψ : TCell K} (hk : ψ.kind = Kind.imm) {s : TSet} {v : BoCa.Val} {χ : TRes K}
    (hh : χ.InStratum s) (hs : ψ.lsOf = some s) (hv : ψ.erase = v) (hw : ψ.wit = χ) :
    ψ = CellUT.immOf s v χ hh := by
  rcases CellUT.rep' ψ with ⟨u, rfl⟩ | ⟨t, u, ξ, hξ, rfl⟩ | ⟨b, _, u, ξ, hξ, P, hP, rfl⟩
  · simp at hk
  · simp at hs hv hw
    subst hs; subst hv; subst hw; rfl
  · simp at hk

/-- **At the identity re-reading, `UpdX`'s `imm` clause is row 5.27's**, at every location
neither side masks. -/
theorem updX_refl_imm {Θ : LocTy} {E E' : BoCa.Loc → Prop} {ρ ρ' : TRes K} (hc : CovR Θ K ρ)
    (hc' : CovR Θ K ρ') (h : UpdX (K' := K) Θ E E' ρ ρ') {l : BoCa.Loc} (hl : ¬ E l)
    (hl' : ¬ E' l) (s : TSet) (v : BoCa.Val) (χ : TRes K) (hh : χ.InStratum s) :
    ρ.FlatAt l (CellUT.immOf s v χ hh) ↔ ρ'.FlatAt l (CellUT.immOf s v χ hh) := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  have hs := flat_lsSim_self hc hσ
  have hs' := flat_lsSim_self hc' hσ'
  have self : ∀ {τ : TRes K} (_ : LsRSim (K' := K) Θ τ τ) {ψ : TCell K},
      τ.get l = some ψ → RR Θ ψ.wit ψ.wit := fun hτ ψ e => by
    have := hτ l; rw [e] at this; cases this with | some h => exact h.2.2.1
  rw [ResUT.flatAt_iff hσ, ResUT.flatAt_iff hσ']
  constructor
  · intro e
    obtain ⟨-, ψ', e', hxc⟩ := (hx l).1 _ e (by simp) hl
    obtain ⟨hv, hr⟩ := hxc.2.2 rfl
    rw [e', imm_eq_of (v := v) (by rw [hxc.1]; rfl) hh (by rw [hxc.2.1]; rfl) (by simpa using hv)
      (RR.func hr (by simpa using self hs e))]
  · intro e
    obtain ⟨-, ψ, e₀, hxc⟩ := (hx l).2 _ e (by simp) hl'
    have hk : ψ.kind = Kind.imm := by rw [← hxc.1]; rfl
    obtain ⟨hv, hr⟩ := hxc.2.2 hk
    have hls : ψ.lsOf = some s := by
      have := hxc.2.1; rw [hk] at this; simpa [rlsOf] using this.symm
    rw [e₀, imm_eq_of (v := v) hk hh hls (by simpa using hv.symm)
      (RR.func (self hs e₀) (by simpa using hr))]

end BoCa.Fig16.Tree.Wp

end
