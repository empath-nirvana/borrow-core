import GhostEnd.Kernel

/-!
# GhostEnd — a pure piece handed a closure that stops holding the lend (#264)

## What `TW`'s records carry (item 1)

`TW W ps rs` (`Core/World.lean`) is a family of *worlds*: the resources reached from `∅` by the
operations the printed proofs perform. Its records are `FrameRec`s `⟨le, v, R, T, δ⟩`, the
payloads 6.64 moved into an `Imm` frame, typed by `vShape T δ v R`. Three facts decide item 1:

* `vShape` is `True` at every `U C` (`record_shape_thunk`). A record at a thunk type admits every
  value: it carries a type, and neither a derivation nor a semantic reading of the code.
* The heap's own cells are untyped: `alloc` takes any value (`tw_heap_any`), a closure over
  untyped code included.
* `TW` mentions no term. `KernelInvariant` (`Kernel.lean`) is about the *answer* of a pure run,
  `wpTS`'s `v`, which `TW` does not constrain: `wpTS` asks `TW` of the configuration before and
  after the run, and the answer only of `Q`.

So `KernelInvariant` is not an instance of `TW`'s preservation, and no strengthening of `TW`'s
records supplies it: a closure a pure run answers is in the term, not in any record.
Recording the program's relation at `U` in a record is excluded for the reason `TW`'s docstring
gives: `wpTS` has `TW` to the left of an arrow, so a `TW` premise at `vC (U C)` is a negative
occurrence. What would supply `KernelInvariant` is an invariant of the machine's configurations
(term and continuation), not of worlds: every value in a configuration reached from a typed term
over typed values is a typed value (`TV`). That is subject reduction for the kernel's machine
over `TV` values, with atoms in the relation. I have not derived it and have not verified that
any obstruction is real.

## A pure piece handed a lend-aware closure (item 2)

At a resumption the continuation is re-run at a fresh lend `α′ ⊏ α`. Its code is re-derived from
its typing at `δ[x ↦ α′]`. Its frames' *values* are not code: each must be read at `α′`, with the
fresh view in place of the dropped cell. For a frame `Γ` this is `FrameThawsD` (`Values.lean`),
the premise of `[let]` in `RBodyT`. Every route meets it.

**Route (c), re-lendability in the continuation relation.** `KapRelR` is the continuation
relation with the re-lend: at every later lend `α′ ⊏ α`, handed the view if the stop dropped the
cell, resumption lands in the relation at `α′`. It is positive (`kapRelR_mono`): the continuation
predicate occurs only right of `─⋆` and under `∀`, so the `ewp` it induces is a least fixed
point of a monotone operator, and the answer relation is indexed by the lend, not recursive.
The code of `map`'s frames and of `f`'s body is re-derived at `δ[x ↦ α′]` from their typings, as
the route says.

The step (c) does not supply is the thaw of a frame **value** of a `U` type known only through the
ordinary relation. `frameThawsD_thunk_iff` states it exactly: for a frame whose one live slot is
`U C`, `FrameThawsD` holds iff `URelend C`, the thaw of every value of `vC (U C)` at the lend
`α` into `vC (U C)` at `α′` with the fresh view. What is proved about `URelend`:

* a value holding no cell at `α`, of a type free of `'x`, thaws at once (`uThaw_free`): the
  relation does not read `'x` and the resource does not change;
* a typed value thaws by re-derivation (`uThaw_tv`: `tv_freeze`, `tv_thaw`, `tv_sound`).

The case left is a `U` value of the ordinary relation that holds the lend's cell, or whose type
mentions `'x`. It arises: `capture_hides_lend` is a closure of the `'x`-free type `U(F 1)` holding
the cell, and a pure `h f c` that calls a yielding `c` first holds `f` in its frame across `c`'s
stop. There `vC (U C)` at `δ[x ↦ α]` is all that is known, and `ptoMutS ℓ α` does not hold of a
cell at `α′ ⊏ α`, so reading `f` at `α′` is a fresh-lend naturality of `wpTS` at `U`
(`Restrat`'s `WpNatural`, open). I have not derived `URelend` and have not verified that any
obstruction is real.

So (c) closes the case exactly when the frames' values are typed values: when a pure piece's
frames hold `TV` values, which is `KernelInvariant` extended from answers to frames. Item 1 and
item 2 meet at that one invariant.

**Route (a), a bridge.** The same step: a pure piece passes `f`'s stops through, but its own frame
values are re-lent at each resumption. Not derived; the obstruction is not verified.

**Route (b), the relation re-lendable by construction.** `vRL`/`cRL` give `U C` the re-lend in its
own clause: the frozen part, handed the view at any `α′ ⊑ α`, is in `cRL C` at `α′`. That clause
is `URelend`'s conclusion by definition, and `CloL` is its instance at `U(1 → F_S B)`
(`cloL_of_vRL`).

**The T15 tripwire.** Not reached. `vRL`/`cRL` are defined by structural recursion on the type:
the relation at `U C` refers to `cRL C`, which refers to `vRL A` negatively at `A → C` and to
`vRL B` at `F B`, all strictly smaller types. No predicate is defined in terms of itself at the
same type, so there is no domain equation `X ≅ (X → …)` of `no_negative_domain`'s shape. The
shape #262 named is an *inductive* `TV` whose closure case carries its body's borrower reading:
there `TV` would occur negatively in its own constructor, at the arguments' types, inside a
predicate indexed by contexts rather than defined by recursion on types. `CloL` and `KapRelR` are
not recursive at all. The second place T15 can return, a cell whose witness holds a closure over
the cell itself, stays excluded by the strict stratum (`ptoMutS`'s `σ ∈ Res_b`).

The cost of (b) is the fundamental lemma at `vRL`/`cRL`: every compatibility lemma proved again
at the new relation. That is work, not an unknown, and it is not attempted here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Item 1: what `TW`'s records carry -/

/-- **A record at a thunk type admits every value.** `vShape (U C)` is `True`: a `TW` record
carries the type, not the code. -/
theorem record_shape_thunk (C : CTy) (δ : LSub) (v : Val) (ρ : WRes) :
    vShape (.thunk C) δ v ρ := trivial

/-- **The heap is untyped in `TW`.** An own cell holding any value is a `TW` world. -/
theorem tw_heap_any (l : BoCa.Loc) (v : Val) : TW (ResU.single l (CellU.ownOf v)) [] [] :=
  .alloc (μ := fun _ => none) .empty lower_empty rfl (compS_empty_left _)
    (ResU.valid_single_own l v)

/-! ### Route (c): the re-lendable continuation relation -/

/-- **Route (c)'s continuation relation.** The share is in `Res_α` beside the dropped cell. At
every extension of the list, at every later lend `α′ ⊏ α`, handed the answer and, if the stop
dropped the cell, the fresh view, the resumed continuation is in `X α′`. -/
def KapRelR (l : BoCa.Loc) (T : VTy) (δ : LSub) (PB : List SRec → Val → WProp)
    (X : Life → List SRec → Expr → WProp) (α : Life) (d : Bool) (ls : List SRec) (K : Kont) :
    WProp := fun ρ =>
  ρ.InStratum α ∧ ∀ ls', Ext ls ls' ρ → ∀ α', α' ⊏ α → ∀ w : Val,
    ((PB ls' w ⋆ vwD l T δ d α' ls') ─⋆ X α' ls' (K.plug (.val w))) ρ

/-- **Positivity of route (c).** `KapRelR` is monotone in the continuation predicate. -/
theorem kapRelR_mono {l : BoCa.Loc} {T : VTy} {δ : LSub} {PB : List SRec → Val → WProp}
    {X X' : Life → List SRec → Expr → WProp} (hX : ∀ α ls e ρ, X α ls e ρ → X' α ls e ρ)
    {α : Life} {d : Bool} {ls : List SRec} {K : Kont} {ρ : WRes}
    (h : KapRelR l T δ PB X α d ls K ρ) : KapRelR l T δ PB X' α d ls K ρ :=
  ⟨h.1, fun ls' he α' hα' w =>
    wand_mono_right (fun σ hσ => hX α' ls' _ σ hσ) ρ (h.2 ls' he α' hα' w)⟩

/-! ### The frame thaw, at a `U` slot -/

/-- **The thaw of a `U` value known through the ordinary relation.** A value of `vC (U C)` at the
lend `α`, consistent with the table, splits into the cell it drops and a part in `Res_α` that,
handed the fresh view at every later lend `α′ ⊏ α`, is a value of `vC (U C)` at `α′`. -/
def URelend (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (C : CTy) : Prop :=
  ∀ (δ : LSub), Δ.Models δ → ∀ (β : Life), b.interp δ = some β →
    ∀ (l : BoCa.Loc) (f : Val) (α : Life), α ⊏ β → ∀ (ls : List SRec) (ρ : WRes),
      TabAt l α ρ → vC true (.thunk C) ls (δ.extend x α) f ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ dropC l d ρn ∧ ρz.InStratum α ∧
        ∀ ls', Ext ls ls' ρz → ∀ α', α' ⊏ α → ∀ ρv ρ', vwD l T δ d α' ls' ρv →
          ResU.CompS ρv ρz ρ' → TabAt l α' ρ' ∧ vC true (.thunk C) ls' (δ.extend x α') f ρ'

/-- A frame of one live `U C` slot, `m` dead, holds `f`'s relation. -/
theorem gDen_thunk_iff {x : LifeVar} {T : VTy} {C : CTy} {ls : List SRec} {δ : LSub} {f : Val}
    {l : BoCa.Loc} {ρ : WRes} :
    gDenC ls δ ([⟨.thunk C, true⟩] ++ [mSlot x T false]) ([f] ++ [Val.loc l]) ρ ↔
      vC true (.thunk C) ls δ f ρ := by
  rw [gDenC_iff]
  have hlw := liveWithin_append [⟨.thunk C, true⟩] (mSlot x T false) [f] (Val.loc l) rfl
  have e : gSepC ls δ ([⟨.thunk C, true⟩] ++ [mSlot x T false]) ([f] ++ [Val.loc l]) =
      (vC true (.thunk C) ls δ f ⋆ emp) := by
    simp [gSepC]
  rw [e]
  exact ⟨fun h => sep_emp_iff.mp h.2, fun h => ⟨hlw, sep_emp_iff.mpr h⟩⟩

/-- **The step route (c) needs, exactly.** A frame whose one live slot is `U C` thaws at every
re-lend iff every value of `vC (U C)` does. -/
theorem frameThawsD_thunk_iff {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy}
    {C : CTy} : FrameThawsD Δ x b T [⟨.thunk C, true⟩] false ↔ URelend Δ x b T C := by
  constructor
  · intro H δ hδ β hβ l f α hα ls ρ ht hv
    obtain ⟨Fz, hFe, hFo, hfz, hth⟩ := H δ hδ β hβ l [f] rfl
    obtain ⟨d, ρz, ρn, hc, hz, hn⟩ := hfz α hα ls ρ ht (gDen_thunk_iff.mpr hv)
    refine ⟨d, ρz, ρn, hc, hn, hFo α d ls ρz hz, fun ls' he α' hα' ρv ρ' hvw hc' => ?_⟩
    obtain ⟨ht', hg⟩ := hth α α' d ls' ρv ρz ρ' hα' hvw (hFe α d ls ls' ρz he hz) hc'
    exact ⟨ht', gDen_thunk_iff.mp hg⟩
  · intro H δ hδ β hβ l γ hlen
    obtain ⟨f, rfl⟩ : ∃ f, γ = [f] := by
      match γ, hlen with
      | [f], _ => exact ⟨f, rfl⟩
    refine ⟨fun α d ls ρz => ρz.InStratum α ∧ ∀ ls', Ext ls ls' ρz → ∀ α', α' ⊏ α →
        ∀ ρv ρ', vwD l T δ d α' ls' ρv → ResU.CompS ρv ρz ρ' →
          TabAt l α' ρ' ∧ vC true (.thunk C) ls' (δ.extend x α') f ρ',
      fun α d ls ls' ρ he h => ⟨h.1, fun ls'' he' => h.2 ls'' (he.trans he')⟩,
      fun α d ls ρ h => h.1, ?_, ?_⟩
    · intro α hα ls ρ ht hg
      obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ :=
        H δ hδ β hβ l f α hα ls ρ ht (gDen_thunk_iff.mp hg)
      exact ⟨d, ρz, ρn, hc, ⟨hz, hth⟩, hn⟩
    · intro α α' d ls ρv ρz ρ hα' hv hz hc
      obtain ⟨ht, hf⟩ := hz.2 ls (Ext.refl ls ρz) α' hα' ρv ρ hv hc
      exact ⟨ht, gDen_thunk_iff.mpr hf⟩

/-- **A `U` value holding no cell at the lend, of a type free of `'x`, thaws at once.** Nothing
is dropped, the resource is unchanged, and the relation does not read `'x`. -/
theorem uThaw_free {x : LifeVar} {C : CTy} (hC : ¬ VFree x (.thunk C)) {l : BoCa.Loc}
    {T : VTy} {δ : LSub} {f : Val} {α α' : Life} (hα' : α' ≤ α) {ls : List SRec} {ρ ρ' : WRes}
    (hz : ρ.InStratum α) (hv : vC true (.thunk C) ls (δ.extend x α) f ρ) {ρv : WRes}
    (hvw : vwD l T δ false α' ls ρv) (hc : ResU.CompS ρv ρ ρ') :
    TabAt l α' ρ' ∧ vC true (.thunk C) ls (δ.extend x α') f ρ' := by
  obtain ⟨rfl, -⟩ := hvw
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨tabAt_mono hα' (tabAt_of_inStratum hz), ?_⟩
  rw [vC_extend_of_not_free hC] at hv ⊢
  exact hv

/-- **A typed `U` value thaws by re-derivation.** It is frozen by `tv_freeze`, thawed by
`tv_thaw`, and re-derived at the fresh lend by `tv_sound`. -/
theorem uThaw_tv {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy}
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x T) {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    {l : BoCa.Loc} {C : CTy} {f : Val} {α : Life} (hα : α ⊏ β) {ls : List SRec} {ρ : WRes}
    (ht : TabAt l α ρ) (hv : TV Δ x b T δ l false α (.thunk C) ls f false ρ) :
    ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ dropC l d ρn ∧ ρz.InStratum α ∧
      ∀ ls', Ext ls ls' ρz → ∀ α', α' ⊏ α → ∀ ρv ρ', vwD l T δ d α' ls' ρv →
        ResU.CompS ρv ρz ρ' → TabAt l α' ρ' ∧ vC true (.thunk C) ls' (δ.extend x α') f ρ' := by
  obtain ⟨d, ρz, ρn, hc, hz, hn⟩ :=
    tv_freeze hT (models_extend hδ hbx hΔx hβ hα) hv rfl rfl ht
  refine ⟨d, ρz, ρn, hc, dropC_of_vwD hn, tv_inStratum hz rfl,
    fun ls' he α' hα' ρv ρ' hvw hc' => ?_⟩
  obtain ⟨h', ht'⟩ :=
    tv_thaw hT (le_of_lt hα') (tv_local he hz) rfl rfl ρv ρ' hvw (ResU.CompS.comm hc')
  exact ⟨ht', (tv_sound (models_extend hδ hbx hΔx hβ (lt_trans hα' hα))).1 h' rfl rfl⟩

/-! ### Route (b): the relation re-lendable by construction, and positivity -/

mutual
/-- **Route (b)'s value relation** at the lend `x ↦ α` of `ℓ`, every computation at the row `S`.
At `U C` the value splits into the cell it drops and a part in `Res_α` that, at every extension
and every later lend `α′ ⊑ α`, handed the view if it dropped the cell, is in `cRL C` at `α′`.
At `⊗` componentwise; at every other type the ordinary relation at `δ[x ↦ α]`. Defined by
structural recursion on the type. -/
def vRL (S : Row) (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) :
    VTy → Life → List SRec → Val → WProp
  | .thunk C, α, ls, f => fun ρ => ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ vwD l T δ d α ls ρn ∧
      ρz.InStratum α ∧ ∀ ls', Ext ls ls' ρz → ∀ α', α' ≤ α →
        (vwD l T δ d α' ls' ─⋆ cRL S x T δ l C α' ls' (forceE C (.val f))) ρz
  | .tensor A B, α, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRL S x T δ l A α ls v₁ ⋆ vRL S x T δ l B α ls v₂
  | A, α, ls, v => vC true A ls (δ.extend x α) v
/-- **Route (b)'s computation relation.** At `F B` a borrower piece at the lend, its answers in
`vRL B` and its stops owing `OpenD`; at `A → C` every argument in `vRL A`. -/
def cRL (S : Row) (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) :
    CTy → Life → List SRec → Expr → WProp
  | .ret B, α, ls, e => bodyAtD (opTable (Row.tab S δ)) l T δ
      (fun α' ls' v => vRL S x T δ l B α' ls' v)
      (OpenD (opTable (Row.tab S δ)) l T δ (fun α' ls' v => vRL S x T δ l B α' ls' v)) α ls e
  | .arr A C, α, ls, e => fun ρ =>
      ∀ v, (vRL S x T δ l A α ls v ─⋆ cRL S x T δ l C α ls (.app e (.val v))) ρ
  | _, _, _, _ => fun _ => True
end

/-- **`CloL` is route (b)'s `U` clause** at `U(1 → F_S B)`: the frozen part of a `vRL` value of
that type, read below `β`, is a `CloL` closure answering in `vRL B`. -/
theorem cloL_of_vRL {S : Row} {x : LifeVar} {T : VTy} {δ : LSub} {l : BoCa.Loc} {B : VTy}
    {β α : Life} {ls : List SRec} {f : Val} {d : Bool} {ρz : WRes} (hz : ρz.InStratum α)
    (h : ∀ ls', Ext ls ls' ρz → ∀ α', α' ≤ α →
      (vwD l T δ d α' ls' ─⋆ cRL S x T δ l (.arr .unit (.ret B)) α' ls'
        (forceE (.arr .unit (.ret B)) (.val f))) ρz) :
    CloL S δ l T (fun α' ls' v => vRL S x T δ l B α' ls' v) β α d ls f ρz := by
  refine ⟨hz, fun ls' he α' hle _ ρv σ hv hc => ?_⟩
  have hcall := h ls' he α' hle ρv σ hv hc Val.unit PMap.empty σ
    (show vC true .unit ls' (δ.extend x α') Val.unit PMap.empty from ⟨rfl, rfl⟩)
    (ResU.comp_empty_right σ)
  exact hcall

end GhostEnd
