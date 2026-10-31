import Spike743.NaturalK2
import GhostEnd.Drop

/-!
# Spike743 — round P2: `PinStop` at `mut`, a row without `Div`, against `LifeNatural`

`PinStopD` is `PinStop` (`Core/PinLaw.lean`) with the row's `Div` excluded (`Row.divB S = false`),
so the conclusion is `ewpTS` at the row's table (`cC_effOf`).

## What is proved

* `NaturalK2.not_lifeNatural`: round P's `LifeNatural` does not hold, at an arising configuration
  (`NaturalK2.k2_arising`). So everything derived from it is vacuous, `pinLaw_of_natural`
  included, and `PinStopD` follows from it only by `False.elim`. That is not the question, and
  no theorem here derives `PinStopD` that way.
* `pinStopD_of_relendO`: `PinStopD` from `RelendOfTypedO`, GhostEnd's resumption premise
  (`Relend` at `opTableO`) for every `CDerivesP` callback, through `withborR_compat`
  (`ewpTS_M_frameR`, `ewp_then_owner`). `RelendOfTypedO` implies `PinStopD` without using any
  naturality; it is the route's reduction, not progress on the principle.
* `LifeNaturalV`: `LifeNatural` with the shifted share read by the context at the new assignment
  (`gDenC ls' δ' Γ γ ρ'`), the premise that excludes the K2. `lifeNaturalV_of_fundamental`:
  it follows from the fundamental property of `CDerivesP` (`FundamentalP`), the configuration's
  own derivation at `δ'`. So once the K2 is excluded this way, the principle has no content
  beyond `FundamentalP`; everything else the lend needs is in the premises.
* `relend_of_naturalV`, `fundamentalC_of_framesV`, `pinLaw_of_naturalV`: round P's derivations,
  re-derived from `LifeNaturalV` (its `LendFrame`/`LoopFrame` at `LifeNaturalV`).
* `nonvacuous`: at `NaturalK2`'s arising configuration, a real shift (`'x` from `2` to `3`) at
  which every premise of `LifeNaturalV` holds, and its conclusion.

## The missing clauses (named, not proved)

* `FundamentalP`: the callback's `SemC`. `PinStopD`'s callback is any `CDerivesP` derivation,
  which may hold every relaxed rule (`lendLoopR` included), so its relation is the whole
  `fundamentalC_pin` induction. Uniform in depth (a nested lend is a case of the inner
  derivation).
* `StopTyped`: an arising configuration runs at its row's table with every resuming stop an
  arising configuration (`opTableA`): semantic subject reduction to a stop, `ArisingStopsTyped`
  and `gDenC` at the stop. Outside `LifeNatural`: `Arising` is its premise, and its conclusion is
  a `cC`, whose stops carry the continuation's share only under a wand. Uniform in depth; stated
  over every segment.
* `RebuildAt`: at the re-lend, the stopped segment's context holds at `δ[x ↦ α′]` over the rest
  (in `Res_α`) and the re-lent cell. Uniform in depth as stated; a proof would go by the value
  forms that hold the view (data, closures as `tv_thaw`, captured continuations), not by depth.
* `StopsWF`: the resumption order on typed configurations is well-founded. `Relend` is a least
  fixed point; `LifeNatural` (and `FundamentalP`) give each resumed continuation a fresh `ewpTS`
  derivation at the new lifetime, which is not a sub-derivation of the old one, so an induction
  on the callback's `ewpTS` has no hypothesis at the re-lent continuation. A lifetime-free
  measure would supply one. Not derived from `LifeNatural`, whose conclusion is a whole `cC`.

The exact goal left is `RelendOfTypedO`; `pinStopD_of_relendO` closes `PinStopD` from it. That
the four clauses give `RelendOfTypedO` is the intended use, not proved here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.Natural2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Heap Steps performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Spike743.Natural
open GhostEnd (Relend relendF opTableO owner finPost)

/-! ### The target -/

/-- **`PinStopD`**: `PinStop` at its first case, a row without `Div`. -/
def PinStopD : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (d M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B →
    (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T) →
    Row.ResumeO S x → Row.divB S = false →
    closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
    closedAt 0 d = true → SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit) →
    CDerivesP (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δ [⟨.ref T, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor (.ref T) B))

/-- `PinStop` gives `PinStopD`. -/
theorem pinStopD_of_pinStop (h : PinStop (ℍ := ℍ)) : PinStopD (ℍ := ℍ) :=
  fun Δ x b T B d M S hb hx hbx hΔx hT hB hBn hside hS _ hM1 hcb hdc hd hM =>
    h Δ x b T B d M S hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc hd hM

/-! ### The route's reduction: GhostEnd's resumption premise -/

/-- **The resumption premise, for every typed callback.** The callback of a `PinStopD` lend, at
every `δ ⊨ Δ`, every list and every place, is re-lendable at the unwinding frame's table
(`Relend` at `opTableO`): at each stop the lend ends and the owner is handed back, and the
continuation is lent again at a fresh lifetime. This is what `withborR_compat` asks; it implies
`PinStopD` without naturality (`pinStopD_of_relendO`). -/
def RelendOfTypedO : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B →
    Row.ResumeO S x → Row.divB S = false → closedAt 1 M = true →
    CDerivesP (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    ∀ (δ : LSub), Δ.Models δ → ∀ (l : BoCa.Loc) (ls : List SRec),
      Relend (opTableO (Row.tab S δ) l T δ) l T δ (finPost l T B δ) ls
        (substAll [Val.loc l] M) PMap.empty

/-- **`PinStopD` from the resumption premise**, by `withborR_compat`: 6.65 at a resuming table
re-applied at each resumption (`ewpTS_M_frameR`), the unwinding frame disposing of the owner at a
cancel (`ewp_then_owner`), `d` the finaliser. -/
theorem pinStopD_of_relendO (H : RelendOfTypedO (ℍ := ℍ)) : PinStopD (ℍ := ℍ) := by
  intro Δ x b T B d M S hb hx hbx hΔx hT hB hBn hside hS hSd hM1 hcb hdc hd hM δ γ ls ρ hδ hg
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  cases γ with
  | nil => exact absurd hlen (by simp [Ctx.LiveWithin])
  | cons vr γ' =>
    obtain ⟨ρ₁, ρ₂, hc, hv, hρ₂, -⟩ := hgs
    subst hρ₂
    obtain rfl : ρ = ρ₁ := ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)
    obtain ⟨ℓ, v', hs⟩ := hv
    obtain ⟨rfl, hrest⟩ := pure_sep_iff.mp hs
    have hsub : substAll (Val.loc ℓ :: γ')
        (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
        = .app (.app (.val (withborUV d)) (.val (.loc ℓ))) (.val (lendCb M)) := by
      have hw : Expr.psub 0 (Val.loc ℓ :: γ') (withborUV d).1 = (withborUV d).1 :=
        psub_closedAt _ _ (withborUE_closed hdc) le_rfl
      have hc' : Expr.psub 0 (Val.loc ℓ :: γ') (lendCb M).1 = (lendCb M).1 :=
        psub_closedAt _ _ hcb le_rfl
      show Expr.psub 0 _ _ = _
      simp only [Expr.psub]
      rw [show Expr.val (withborUV d) = (withborUV d).1 from rfl, hw,
        show Expr.val (lendCb M) = (lendCb M).1 from rfl, hc']
      simp [Val.shift_zero, Expr.val]
    rw [hsub]
    obtain ⟨b', hdef, hO⟩ := hside
    obtain ⟨β', hb'⟩ := hdef δ hδ
    have hP : ∀ ls' w σ', vC true T ls' δ w σ' → σ'.InStratum (Life.down β') :=
      fun ls' w σ' h => vC_outlivesLe hδ hb' hO true ls' w σ' h _ (Life.down_sqsubset β')
    have hd' : ∀ ls', wpTS ls' d (fun ls'' => vP (.lolli (.ref T) .unit) ls'' δ) PMap.empty := by
      intro ls'
      have h := hd δ [] ls' PMap.empty hδ (gDenC_nil ls' δ)
      rwa [show substAll [] d = d from BoCa.Adequacy.psub_nil 0 d] at h
    refine (cC_effOf S _ ls δ _ ρ hSd).mpr ?_
    have hRA : GhostEnd.ResumeAff (Row.tab S δ) := by
      intro n i en hTn
      obtain ⟨o', hf', rfl⟩ := Row.tab_some hTn
      obtain ⟨ha, hq, -⟩ := hS o' (Row.find_mem hf').1
      exact ⟨ha, hq⟩
    have hFin : ∀ o ∈ S, o.fin = .ret .unit := fun o ho => (hS o ho).2.2.1
    exact GhostEnd.withborR_compat (Row.tab S δ) hRA (GhostEnd.finNil_tab hFin δ) hdc hP hd'
      (lendCb M) ℓ v' ls
      (GhostEnd.relend_lam2 (GhostEnd.opTableO_mono _ _ _ _) hM1
        (H Δ x b T B M S hb hx hbx hΔx hT hB hBn hS hSd hM1 hM δ hδ ℓ ls)) ρ hrest

/-! ### The principle, with the K2 excluded -/

/-- **The fundamental property of `CDerivesP`**, as a `Prop`. `fundamentalC_pin` proves it from
`PinLaw`. -/
def FundamentalP : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerivesP Δ Γ e j → SemJ (ℍ := ℍ) Δ Γ e j

/-- **`LifeNaturalV`**: `LifeNatural`, with the shifted share read by the configuration's own
context at the new assignment and list. `NaturalK2` is excluded by this premise: its shifted
share `ℓ ↦ mut(2, …)` is not in `𝒢⟦x : Mut 'x 1⟧` at `'x ↦ 1` (`k2_not_gDenC`). -/
def LifeNaturalV : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (C : CTy) (γ : List Val) (δ δ' : LSub)
    (ls ls' : List SRec) (W : VTy) (w : Val) (ρr ρv ρv' ρ ρ' : WRes),
    Arising Δ Γ E C γ δ ls ρ → Δ.Models δ' → RegionShift δ δ' ls ls' ρr → Ext ls ls' ρr →
    ResU.CompS ρr ρv ρ → ResU.CompS ρr ρv' ρ' → SameMemory ρv ρv' →
    vC true W ls δ w ρv → vC true W ls' δ' w ρv' →
    gDenC ls' δ' Γ γ ρ' →
    cC (ℍ := ℍ) C ls δ (substAll γ E) ρ → cC (ℍ := ℍ) C ls' δ' (substAll γ E) ρ'

/-- **`LifeNaturalV` is the fundamental property at the new assignment.** The configuration's
segment is typed (`Arising`), `δ′` models its context, and the shifted share is in its context's
relation there; so the segment's own derivation gives the conclusion. Nothing of the shift is
used. -/
theorem lifeNaturalV_of_fundamental (hF : FundamentalP (ℍ := ℍ)) : LifeNaturalV (ℍ := ℍ) :=
  fun _ _ _ _ γ _ δ' _ ls' _ _ _ _ _ _ ρ' hA hδ' _ _ _ _ _ _ _ hg _ =>
    hF _ _ _ _ hA.1 δ' γ ls' ρ' hδ' hg

/-- The K2's shifted share is not in the context's relation at the new assignment. -/
theorem k2_not_gDenC :
    ¬ gDenC [] NaturalK2.δ₁ [⟨NaturalK2.A, true⟩] [Val.loc NaturalK2.ℓ] NaturalK2.ρα := by
  intro hg
  obtain ⟨-, ρ₁, ρ₂, hc, hv, hρ₂, -⟩ := gDenC_iff.mp hg
  subst hρ₂
  obtain rfl : NaturalK2.ρα = ρ₁ := ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)
  refine NaturalK2.k2_fails (ℍ := ℍ) ?_
  rw [NaturalK2.subst_var0]
  exact wpTS_val [] _ _ _ hv

/-- **`relend_of_natural` from `LifeNaturalV`**: the single-lend re-lend, with the stop's context
read at the re-lend (`hg'`), the premise `LifeNaturalV` adds. -/
theorem relend_of_naturalV (hN : LifeNaturalV (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {E : Expr}
    {C : CTy} {γ : List Val} {δ : LSub} {x : LifeVar} {α α' : Life} {ls ls' : List SRec}
    {W : VTy} {w : Val} {ρr ρv ρv' ρ ρ' : WRes}
    (hA : Arising Δ Γ E C γ (δ.extend x α) ls ρ) (hδ' : Δ.Models (δ.extend x α'))
    (hα : ∀ r ∈ ls, α ≤ r.2) (hα' : ∀ r ∈ ls', α' ≤ r.2) (hrα : ρr.InStratum α)
    (hrα' : ρr.InStratum α') (hext : Ext ls ls' ρr)
    (hc : ResU.CompS ρr ρv ρ) (hc' : ResU.CompS ρr ρv' ρ') (hm : SameMemory ρv ρv')
    (hv : vC true W ls (δ.extend x α) w ρv) (hv' : vC true W ls' (δ.extend x α') w ρv')
    (hg' : gDenC ls' (δ.extend x α') Γ γ ρ')
    (h : cC (ℍ := ℍ) C ls (δ.extend x α) (substAll γ E) ρ) :
    cC (ℍ := ℍ) C ls' (δ.extend x α') (substAll γ E) ρ' := by
  refine hN Δ Γ E C γ _ _ ls ls' W w ρr ρv ρv' ρ ρ' hA hδ' (fun y hy => ?_) hext hc hc' hm hv hv'
    hg' h
  by_cases hxy : x = y
  · subst hxy
    exact ⟨α, α', find?_extend_self _ _ _, find?_extend_self _ _ _, hα, hα', hrα, hrα'⟩
  · exact absurd (by rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]) hy

/-! ### The missing clauses -/

/-- A stopped continuation's share, as `contShare`, that is also an arising configuration at
every resumption: `K` is a typed segment closed by arising values, and resumed at an answer at an
`Ext`-extension, the share with the answer's is in the segment's context relation, part of a
tagged typed world. -/
def contShareA (Δ : LifeCtx) (C : CTy) (δ : LSub) (en : OpEnt) (ls : List SRec) (K : Kont)
    (Φ : List SRec → Expr → WProp) : WProp := fun ρ =>
  contShare en ls K Φ ρ ∧
  ∃ (Γ' : Ctx VTy) (E' : Expr) (Bh : VTy) (γ' : List Val), GhostEnd.SegOf K E' γ' ∧
    ∀ ls', Ext ls ls' ρ → ∀ (w : Val) (σ ρ'' : WRes), en.PB ls' w σ → ResU.CompS σ ρ ρ'' →
      Arising Δ (⟨Bh, true⟩ :: Γ') E' C (w :: γ') δ ls' ρ''

/-- `opTable`, its resuming stops carrying `contShareA`. -/
def opTableA (Δ : LifeCtx) (C : CTy) (δ : LSub) (T : OpTab) : Table := fun ls t Φ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
          T n i = some en ∧ en.abort = false⌝ ⋆ (en.PA ls v ⋆ contShareA Δ C δ en ls K Φ))
    (opTable T ls t Φ)

/-- **Missing clause: the stops are typed (semantic subject reduction to a stop).** An arising
configuration at a row without `Div` runs at the row's table with every resuming stop an arising
configuration (`opTableA`). This is `ArisingStopsTyped` with its semantic half: `cC`'s stops carry
their continuation's share only under a wand, never in a context relation. -/
def StopTyped : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (S : Row) (A : VTy) (γ : List Val) (δ : LSub)
    (ls : List SRec) (ρ : WRes),
    Arising Δ Γ E (CTy.effOf S A) γ δ ls ρ → Row.divB S = false →
    ewpTS ls (substAll γ E) (opTableA Δ (CTy.effOf S A) δ (Row.tab S δ))
      (fun ls' v => vC true A ls' δ v) ρ

/-- **Missing clause: the stopped context at the re-lend.** At a stop of a callback lent at `'x`,
the context of the stopped segment, read at `δ[x ↦ α′]` and the resumption list, holds at the
rest and the re-lent cell `ℓ ↦ M_{α′} 𝒱⟦T⟧`: every value of the stopped frames that holds the
view is in the relation at the new lifetime. -/
def RebuildAt : Prop :=
  ∀ (Γ : Ctx VTy) (γ : List Val) (δ : LSub) (x : LifeVar) (α α' : Life)
    (T : VTy) (l : BoCa.Loc) (ls ls' : List SRec) (ρr ρv ρ ρv' : WRes),
    gDenC ls (δ.extend x α) Γ γ ρ → ResU.CompS ρr ρv ρ → ρr.InStratum α →
    ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρv →
    ptoMutS l α' ls' (fun ls₀ => vC true T ls₀ δ) ρv' → Ext ls ls' ρr →
    ∃ ρ', ResU.CompS ρr ρv' ρ' ∧ gDenC ls' (δ.extend x α') Γ γ ρ'

/-- One resumption: from `e`, at a heap some tagged typed world lowers to, a run reaches a stop
`K[perform p]`, and `e′` is `K` resumed at `w`. -/
def ResumeStep (e' e : Expr) : Prop :=
  ∃ (μ μ' : Heap) (W : WRes) (ps rs : List FrameRec) (K : Kont) (p w : Val),
    TW W ps rs ∧ ResU.Lower W μ ∧
    Steps (ℍ := ℍ) μ e μ' (K.plug (performE (.val p))) ∧ e' = K.plug (.val w)

/-- **Missing clause: the resumptions of a typed configuration are well-founded.** A
lifetime-free measure for building `Relend`, the least fixed point, one fresh derivation per
resumption: the segment's computation is accessible for the resumption order. Stated at a row
without `Div`. Not derived, and I have not checked that it holds at every heap a typed world
lowers to; a form restricted to the worlds the run's own shares complete may be the one the
route can use. -/
def StopsWF : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (S : Row) (A : VTy) (γ : List Val) (δ : LSub)
    (ls : List SRec) (ρ : WRes), Arising Δ Γ E (CTy.effOf S A) γ δ ls ρ → Row.divB S = false →
    Acc (ResumeStep (ℍ := ℍ)) (substAll γ E)

/-! ### (i) A non-vacuous instance, with a real shift -/

/-- `innerView` at every lend lifetime no longer than its cell's. -/
theorem innerView_ptoMutS_le (k : Loc) {α αy : Life} (hle : α ≤ αy) (ls : List SRec)
    (δ' : LSub) : ptoMutS k α ls (fun ls₀ => vC true .unit ls₀ δ') (innerView k αy) := by
  refine ⟨αy, Val.unit, PMap.empty, ResU.inStratum_empty αy, unitQ αy, unitQ_holds αy,
    ls.filter (fun r => decide (r.2 ⊐ αy)), hle, rfl, ?_, ?_, ?_⟩
  · funext v ρ
    apply propext
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      exact ⟨by obtain ⟨rfl, -⟩ := h; exact ResU.inStratum_empty αy, h⟩
  · intro r; simp [List.mem_filter]
  · rintro ls' u' σ' ⟨rfl, -⟩; exact ResU.inStratum_empty αy

/-- `['x ↦ 3, 'c ↦ 2]`: `'x` moved to a shorter-lived lifetime. -/
def δ₂ : LSub := ⟨[(0, 3), (1, 2)]⟩

theorem vC_A_δ₂ : vC true NaturalK2.A [] δ₂ (.loc NaturalK2.ℓ) NaturalK2.ρα :=
  ⟨NaturalK2.L 3, rfl, NaturalK2.ℓ, pure_sep_mk rfl
    (innerView_ptoMutS_le NaturalK2.ℓ (show (2 : ℕ) ≤ 3 by decide) [] δ₂)⟩

/-- **(i) `LifeNaturalV`'s premises and conclusion at a real shift.** At `NaturalK2`'s arising
configuration, `'x` moves from `2` to `3`, the view is the configuration's variable at its own
type `Mut 'x 1` and keeps its cell: every premise of `LifeNaturalV` (so of `LifeNatural`, its
last premise dropped) holds, and so does the conclusion. -/
theorem nonvacuous :
    Arising ⟨[]⟩ [⟨NaturalK2.A, true⟩] (.var 0) (.ret NaturalK2.A) [Val.loc NaturalK2.ℓ]
      NaturalK2.δ₀ [] NaturalK2.ρα ∧
    (⟨[]⟩ : LifeCtx).Models δ₂ ∧ RegionShift NaturalK2.δ₀ δ₂ [] [] PMap.empty ∧
    δ₂.find? 0 ≠ NaturalK2.δ₀.find? 0 ∧
    Ext [] [] PMap.empty ∧ ResU.CompS PMap.empty NaturalK2.ρα NaturalK2.ρα ∧
    SameMemory NaturalK2.ρα NaturalK2.ρα ∧
    vC true NaturalK2.A [] NaturalK2.δ₀ (.loc NaturalK2.ℓ) NaturalK2.ρα ∧
    vC true NaturalK2.A [] δ₂ (.loc NaturalK2.ℓ) NaturalK2.ρα ∧
    gDenC [] δ₂ [⟨NaturalK2.A, true⟩] [Val.loc NaturalK2.ℓ] NaturalK2.ρα ∧
    cC (ℍ := ℍ) (.ret NaturalK2.A) [] NaturalK2.δ₀
      (substAll [Val.loc NaturalK2.ℓ] (.var 0)) NaturalK2.ρα ∧
    cC (ℍ := ℍ) (.ret NaturalK2.A) [] δ₂
      (substAll [Val.loc NaturalK2.ℓ] (.var 0)) NaturalK2.ρα := by
  refine ⟨NaturalK2.k2_arising, NaturalK2.models_empty δ₂, ?_, by decide, ext_refl [] _,
    ResU.comp_empty_left _, fun _ => Iff.rfl, NaturalK2.vC_view NaturalK2.δ₀_x [], vC_A_δ₂,
    gDenC_mk (by simp [Ctx.LiveWithin])
      ⟨NaturalK2.ρα, PMap.empty, ResU.comp_empty_right _, vC_A_δ₂, rfl, trivial⟩, ?_, ?_⟩
  · intro y hy
    by_cases h : y = 0
    · subst h
      exact ⟨NaturalK2.L 2, NaturalK2.L 3, rfl, rfl, fun _ h => absurd h (by simp),
        fun _ h => absurd h (by simp), ResU.inStratum_empty _, ResU.inStratum_empty _⟩
    · exfalso; apply hy
      simp [NaturalK2.δ₀, δ₂, LSub.find?, Lifetime.assocFind, Ne.symm h]
  · rw [NaturalK2.subst_var0]; exact wpTS_val [] _ _ _ (NaturalK2.vC_view NaturalK2.δ₀_x [])
  · rw [NaturalK2.subst_var0]; exact wpTS_val [] _ _ _ vC_A_δ₂

/-! ### Round P's derivations, re-derived from `LifeNaturalV` -/

/-- **`LendFrame` at `LifeNaturalV`** (round P's clause, the premise replaced).
Given `LifeNatural`, a relaxed lend whose callback is typed (`CDerivesP`, so its stops are
arising) and in the relation (`SemC`) is in the relation. This is 6.65/6.64 at a resuming table:
the lend ended at each stop, lent again at a fresh lifetime at the resumption (`LifeNatural`'s
re-lend), the place returned at the end or at a cancel. Uniform in depth (a nested lend is in the
callback's `SemC`) and in the holder (none is mentioned). -/
def LendFrameV : Prop :=
  LifeNaturalV (ℍ := ℍ) →
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (P V B : VTy) (Δb : LifeCtx) (tk : Bool)
    (d M : Expr) (S : Row),
    LendForm Δ x b P V B Δb tk →
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x B → NoThunkT B → RowOf tk S x →
    closedAt 1 M = true → closedAt 0 (lendCb M).1 = true → closedAt 0 d = true →
    SemV (ℍ := ℍ) Δ [] d (.lolli P .unit) →
    CDerivesP Δb [⟨V, true⟩] M (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δb [⟨V, true⟩] M (CTy.effOf S (.box (.var x) B)) →
    SemC (ℍ := ℍ) Δ [⟨P, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor P B))

/-- **`LoopFrame` at `LifeNaturalV`** (round P's clause, the premise replaced). Given `LifeNatural`, the
per-observation `imm` lend whose steps and first state are typed and in the relation is in the
relation at `U(Loop (Ref A ⊗ B) (Ref A ⊗ R))`. One observation is `Spike743.r2_next_obs`
(`ewpTS_I_frameR`); across observations it is the state invariant re-lent at each fresh `'x`. -/
def LoopFrameV : Prop :=
  LifeNaturalV (ℍ := ℍ) →
  ∀ (Δ : LifeCtx) (x : LifeVar) (A S B R : VTy) (N K s0 : Expr),
    Δ.find? x = none → Δ.meetOfDom.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x A → ¬ VFree x B → ¬ VFree x R → NoThunkT B → NoThunkT R → VScoped Δ A →
    closedAt 1 N = true → closedAt 1 K = true → closedAt 0 s0 = true →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.comp (.ret (.sum B S))) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.comp (.ret R)) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [] s0 (.val S) →
    SemC (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.ret (.sum B S)) →
    SemC (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.ret R) →
    SemV (ℍ := ℍ) (Δ.extend x Δ.meetOfDom) [] s0 S →
    SemC (ℍ := ℍ) Δ [⟨.ref A, true⟩] (lendLoopApp A B R N K s0)
      (CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R))

/-! ### Depth: the fundamental property from the frames -/

/-- **The Fundamental Property from `LifeNatural` and the two frames.** `fundamentalC_pin`'s
induction, case for case; each relaxed rule's case is a frame at the induction hypothesis of its
callback (and steps). A relaxed lend nested in another at any depth is a case of the inner
derivation: no clause is per depth. -/
theorem fundamentalC_of_framesV (hN : LifeNaturalV (ℍ := ℍ)) (hF : LendFrameV (ℍ := ℍ))
    (hL : LoopFrameV (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    {j : Jdg} (h : CDerivesP Δ Γ e j) : SemJ (ℍ := ℍ) Δ Γ e j := by
  induction h with
  | var h => exact var_compatC h
  | unitI h => exact unitI_compatC h
  | tensorI hs _ _ ih₁ ih₂ => exact tensorI_compatC hs ih₁ ih₂
  | sumI₁ _ ih => exact sumI₁_compatC ih
  | sumI₂ _ ih => exact sumI₂_compatC ih
  | thunkF _ ih => exact thunkF_compatC ih
  | thunkV hC _ ih => exact thunkV_compatC hC ih
  | ret _ ih => exact ret_compatC ih
  | bind hs _ _ ihM ihN => exact bind_compatC hs ihM ihN
  | force h => exact force_compatC h
  | lam _ ih => exact lam_compatC ih
  | lamDead _ ih => exact lamDead_compatC ih
  | app hs _ hx ih => exact app_compatC hs ih hx
  | withI _ _ ihM ihN => exact withI_compatC ihM ihN
  | proj₁ _ ih => exact proj₁_compatC ih
  | proj₂ _ ih => exact proj₂_compatC ih
  | topI => exact topI_compatC
  | unitE hs _ _ ihV ihM => exact unitE_compatC hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact tensorE_compatC hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact sumE_compatC hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact zeroE_compatC hs ihV
  | allI hbx hΔx hΓx _ ih =>
      exact allI_compatC hbx hΔx hΓx ((semC_liveEq (.dead (LiveEq.refl _))).mp ih)
  | allE _ hlt ih => exact allE_compatC ih hlt
  | bangThunkF hp _ ih => exact bangThunkF_compatC hp ih
  | bangThunkV hp hC _ ih => exact bangThunkV_compatC hp hC ih
  | bangE _ ih => exact bangE_compatC ih
  | copyBang hΓ => exact copyBang_compatC hΓ
  | forgetBang hΓ => exact forgetBang_compatC hΓ
  | boxI _ hΓ ih => exact boxI_compatC ih hΓ
  | boxE _ ih => exact boxE_compatC ih
  | immSub _ hle ih => exact immSub_compatC ih hle
  | mutSub _ hle ih => exact mutSub_compatC ih hle
  | alloc hΓ => exact alloc_compatX hΓ
  | free hΓ => exact free_compatX hΓ
  | swap hΓ => exact swap_compatX hΓ
  | copy hΓ => exact copy_compatX hΓ
  | forgetImm hΓ => exact forgetImm_compatX hΓ
  | forgetMut hΓ => exact forgetMut_compatX hΓ
  | forgetUnk hΓ => exact forgetUnk_compatX hΓ
  | lit c hΓ => exact lit_compatX c hΓ
  | tokMint hΓ => exact tokMint_compatX hΓ
  | tokBurn hΓ => exact tokBurn_compatX hΓ
  | hostOp op hΓ => exact hostOp_compatX op hΓ
  | arrNew _ hΓ => exact arrNew_compatX hΓ
  | arrFree _ hΓ => exact arrFree_compatX hΓ
  | arrSize _ hΓ => exact arrSize_compatX hΓ
  | arrReplace _ hΓ => exact arrReplace_compatX hΓ
  | arrLen _ _ hΓ => exact arrLen_compatX hΓ
  | arrGet _ _ hΓ => exact arrGet_compatX hΓ
  | arrCopy _ _ hΓ => exact arrCopy_compatX hΓ
  | arrForget _ _ hΓ => exact arrForget_compatX hΓ
  | countFold _ hΓ => exact countFold_compatX hΓ
  | countTry _ _ hΓ => exact countTry_compatX hΓ
  | boundedFix _ _ hΓ => exact boundedFix_compatX hΓ
  | iterate _ _ _ _ hS hΓ => exact iterate_compatX hS hΓ
  | divFuel _ _ hS hΓ => exact divFuel_compatX hS hΓ
  | reify _ _ _ _ hS hcl _ hΓ ihres => exact reify_compatX hS hcl ihres hΓ
  | sliceBorrowM x hΓ hA hB hf₁ hf₂ => exact sliceBorrowM_compatX x hΓ hA hB hf₁ hf₂
  | sliceBorrowI x hΓ hsc hA hB hf₁ hf₂ => exact sliceBorrowI_compatX x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM _ _ hΓ => exact sliceGetM_compatX hΓ
  | sliceLenM _ _ hΓ => exact sliceLenM_compatX hΓ
  | sliceSplitI _ _ hΓ => exact sliceSplitI_compatX hΓ
  | sliceSplitM _ _ hΓ => exact sliceSplitM_compatX hΓ
  | sliceEmptyI _ _ hΓ => exact sliceEmptyI_compatX hΓ
  | sliceEmptyM _ _ hΓ => exact sliceEmptyM_compatX hΓ
  | arrEmpty _ hΓ => exact arrEmpty_compatX hΓ
  | sliceReplaceM _ _ hΓ => exact sliceReplaceM_compatX hΓ
  | sliceSwapM _ _ hΓ => exact sliceSwapM_compatX hΓ
  | withbor1 x hΓ hx hsc₁ hf₁ hf₂ => exact withbor1_compatX x hΓ hx hsc₁ hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact withbor2_compatX x hΓ hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact withbor3_compatX x hΓ hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact withload_compatX x hΓ hx hf₁ hf₂
  | withswap hΓ => exact withswap_compatX hΓ
  | withbor1U x hΓ _ hsc₁ hf₁ hf₂ hS hdc _ ihd => exact withbor1U_compatX x hΓ hsc₁ hf₁ hf₂ hS hdc ihd
  | withbor2U x hΓ _ hside hf₁ hf₂ hS hdc _ ihd =>
      exact withbor2U_compatX x hΓ hside hf₁ hf₂ hS hdc ihd
  | withbor3U x hΓ _ hf₁ hf₂ hS hdc _ ihd => exact withbor3U_compatX x hΓ hf₁ hf₂ hS hdc ihd
  | withloadU x hΓ _ hf₁ hf₂ hS => exact withloadU_compatX x hΓ hf₁ hf₂ hS
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowMU_compatX x hΓ hA hB hf₁ hf₂ hS hdc ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS hdc _ ihd =>
      exact sliceBorrowIU_compatX x hΓ hsc hA hB hf₁ hf₂ hS hdc ihd
  | lolliE hs _ _ iha ihf => exact lolliE_compatX hs iha ihf
  | allEV _ hlt ih => exact allE_compatX ih hlt
  | ofRet _ ih => exact ih
  | roll hA hc _ ih => exact roll_compatX hA hc ih
  | unroll _ ih => exact unroll_compatX ih
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact foldImm_compatX F hF hG y c R hΓ hyM hyR hR
  | foldOwn F R hΓ hF hG => exact foldOwn_compatX F hF hG R hΓ
  | foldReuse F R hΓ hF hG => exact foldReuse_compatX F hF hG R hΓ
  | foldOwnG B₀ Rs hΓ hB => exact FoldP.foldOwnG_compatX B₀ hB Rs hΓ
  | nuIn hC _ ih => exact nuIn_compatX hC ih
  | nuOut hC _ ih => exact nuOut_compatX hC ih
  | unfoldN C S hC hΓ => exact unfold_compatX hC S hΓ
  | effSub hle _ ih => exact sub_compatC hle ih
  | effPerform hf hna _ ih => exact perform_compatC hf hna ih
  | effRaise hf ha hd _ ih => exact raise_compatC hf ha (fun _ _ _ _ h => vC_noOwn_of_ownFree hd h) ih
  | effLet hs hW hU _ _ ihM ihN => exact let_compatC hs hW hU ihM ihN
  | effThen hs hNZ _ hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact then_compatC hs hNZ hU hMS hDS hfin hP hSD ihM ihN ihD
  | effHandleV hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact handleV_compatC hs hd hH ihc hn0 hnS hlen hdv ihe
  | effHandleVB hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact handleV_compatCB hs hd hH ihc hn0 hnS hlen hdv ihe hΓd hSd
  | effHandleT hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact handleT_compatC hs hd hHr hHc ihc hn0 hnd hnS hlen hSN hLin ihe
  | effHandleL hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact handleL_compatC hs hd hHr hHw hHn ihc hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin ihe
  | letPoly b hcl _ _ _ ihN => exact letPoly_compatC (Val.lam b) hcl ihN
  | lendR hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF hN _ _ _ _ _ _ _ _ _ _ _ (.ref false hT (by simpa [LendSide] using hside))
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS.toT) hM1 hcb hdc ihd
        (by simpa [lendView] using hM) (by simpa [lendView, SemJ] using ihM)
  | lendRI hb hx hbx hΔx hT hB hBn hsc hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF hN _ _ _ _ _ _ _ _ _ _ _ (.ref true hT (by simpa [LendSide] using hsc))
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS.toT) hM1 hcb hdc ihd
        (by simpa [lendView] using hM) (by simpa [lendView, SemJ] using ihM)
  | lendRF hb hx hbx hΔx hA hB hBn hsideA hsideB hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF hN _ _ _ _ _ _ _ _ _ _ _ (.fam hA hsideA hsideB)
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc ihd hM ihM
  | lendRT k hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF hN _ _ _ _ _ _ _ _ _ _ _ (.ref k hT hside)
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc ihd hM ihM
  | lendRH k y hb hx hbx hΔx hy hΔy hT hB hyT hyB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF hN _ _ _ _ _ _ _ _ _ _ _ (.hold k y hT hyT hyB hside hy hΔy)
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS) hM1 hcb hdc ihd hM ihM
  | lendLoopR hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0 ihN ihK ihs0 =>
      exact hL hN _ _ _ _ _ _ _ _ _ hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0
        ihN ihK ihs0
  | @nilDead _ _ _ j hΓ _ ih => cases j <;> exact semC_dead .nil hΓ ih

/-! ### Each field from `LifeNatural` -/

section FieldsV
variable (hN : LifeNaturalV (ℍ := ℍ)) (hF : LendFrameV (ℍ := ℍ)) (hL : LoopFrameV (ℍ := ℍ))
include hN hF hL

/-- **W-tick from `LifeNatural`** (and `LendFrameV` at `ref k`). -/
theorem field_of_natural_tickV : PinStopTick (ℍ := ℍ) :=
  fun Δ x b T B d M S k hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc hd hM =>
    hF hN _ _ _ _ _ _ _ _ _ _ _ (.ref k hT hside) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_framesV hN hF hL hM)

/-- **R1 from `LifeNatural`**: W-tick at `k = false` (`Round3.pinStop_of_tick`). -/
theorem field_of_natural_stopV : PinStop (ℍ := ℍ) :=
  Spike743.Round3.pinStop_of_tick (field_of_natural_tickV hN hF hL)

/-- **W-imm from `LifeNatural`**: W-tick at `k = true` (`Round3.pinStopImm_of_tick`). -/
theorem field_of_natural_stopImmV : PinStopImm (ℍ := ℍ) :=
  Spike743.Round3.pinStopImm_of_tick (field_of_natural_tickV hN hF hL)

/-- **W-nest from `LifeNatural`** (and `LendFrameV` at `fam`). -/
theorem field_of_natural_nestV : PinNest (ℍ := ℍ) :=
  fun Δ x b A B d M S hb hx hbx hΔx hA hB hBn hsideA hsideB hS hM1 hcb hdc hd hM =>
    hF hN _ _ _ _ _ _ _ _ _ _ _ (.fam hA hsideA hsideB) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_framesV hN hF hL hM)

/-- **W-hold from `LifeNatural`** (and `LendFrameV` at `hold k y`). -/
theorem field_of_natural_holdV : PinStopHold (ℍ := ℍ) :=
  fun Δ x y b T B d M S k hb hx hbx hΔx hy hΔy hT hB hyT hyB hBn hside hS hM1 hcb hdc hd hM =>
    hF hN _ _ _ _ _ _ _ _ _ _ _ (.hold k y hT hyT hyB hside hy hΔy) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_framesV hN hF hL hM)

/-- **R2 from `LifeNatural`** (and `LoopFrameV`). -/
theorem field_of_natural_loopV : PinLoop (ℍ := ℍ) :=
  fun Δ x A S B R N K s0 hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0 =>
    hL hN Δ x A S B R N K s0 hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0
      (fundamentalC_of_framesV hN hF hL hN') (fundamentalC_of_framesV hN hF hL hK)
      (fundamentalC_of_framesV hN hF hL hs0)

/-- **`PinLaw` from `LifeNatural`** and the two frames. -/
theorem pinLaw_of_naturalV : PinLaw (ℍ := ℍ) where
  stop := field_of_natural_stopV hN hF hL
  loop := field_of_natural_loopV hN hF hL
  stopImm := field_of_natural_stopImmV hN hF hL
  nest := field_of_natural_nestV hN hF hL
  tick := field_of_natural_tickV hN hF hL
  hold := field_of_natural_holdV hN hF hL

end FieldsV

end Spike743.Natural2

end
