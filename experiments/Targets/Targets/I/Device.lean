import Targets.I.Interface
import Targets.B.Conservativity

/-!
# The interaction — the laws at the world, and the proof device (RESTRUCTURE §3.3, §3.6, §3.7)

The interaction's laws at the world, and P11.

* In done (I's `Bounds`, `Targets/I/Combined.lean`): `SliceShapeI`, `EffInterp` ("opTable is the
  interpretation", read through the fixed `ewpW` and the field `share`), `ShareMono`,
  `AdequateEvery`.  Each is neutral to OQ-8 and OQ-9.
* In the device, beside done (finding #5): `Mono`, `EmbedsNil`, and `Device`'s other conjuncts.
* `SliceShape` (the whole nil-slice pin) is `SliceShapeB ∧ SliceShapeI` (`sliceShape_iff`);
  `WLaws` bundles the device's laws.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The nil slice, structurally**: at σ = [] nothing is held, the configurations, the order, the
stop and the run-end relation are Core's, and a stored payload is read at σ = []. -/
def SliceShape (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔
     (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)) ∧
  (∀ ls ls' ρ ρ' π, M.Upd (ls, M.nil) (ls', M.nil) ρ ρ' π ↔ ResU.UpdV ρ π) ∧
  (∀ b, M.payStk b M.nil = M.nil)

/-- **Mono**: Kripke monotonicity of the value relation, in both modes. -/
def Mono (M : SemWorld) : Prop :=
  ∀ b A i i' δ v ρ, M.Ext i i' ρ → M.val b A i δ v ρ → M.val b A i' δ v ρ

/-- **EffInterp**: an unr-free row is read through its protocol ("opTable is the
interpretation"). -/
def EffInterp (M : SemWorld) : Prop :=
  ∀ S R i δ e ρ, Row.NU S → (M.comp (CTy.effOf S R) i δ e ρ ↔
    ewpW (ℍ := ℍ) M i e (opTabW M (rowTabW M S δ)) (fun j v => M.val true R j δ v) ρ)

/-- The share is monotone in what it owes, at non-`unr` entries. -/
def ShareMono (M : SemWorld) : Prop :=
  ∀ T en n i K (Φ Φ' : Idx M.Stk → Expr → WProp) ρ, en.q ≠ .unr →
    (∀ i e ρ, Φ i e ρ → Φ' i e ρ) → M.share T en n i K Φ ρ → M.share T en n i K Φ' ρ

/-- **Adequacy from every index**: from every configuration W reaches, every run of a computation
in W's relation at an unr-free row continues to a value or to a stop of the row. -/
def AdequateEvery (M : SemWorld) : Prop :=
  ∀ (i : Idx M.Stk) (fρ ρf ρ : WRes) (ps : List FrameRec) (μ : Heap) (S : Row) (A : VTy)
    (δ : LSub) (e : Expr), Row.NU S →
    M.Fam fρ ps i → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → ResU.Lower fρ μ →
    M.comp (CTy.effOf S A) i δ e ρ →
    ∀ μ₁ e₁, Steps (ℍ := ℍ) μ e μ₁ e₁ →
      ∃ μ₂ e₂, Steps (ℍ := ℍ) μ₁ e₁ μ₂ e₂ ∧ (IsVal e₂ ∨ StopsIn S e₂)

/-- **The laws every W satisfies.** -/
def WLaws (M : SemWorld) : Prop :=
  SliceShape M ∧ Mono M ∧ ExtPre M ∧ EffInterp (ℍ := ℍ) M ∧ FamEmpty M ∧ DataVals M ∧
  ShareMono M ∧ RelLaws M ∧ AdequateEvery (ℍ := ℍ) M

/-- What `Mono` needs at `U` when the future-world quantifier sits at the binder clauses
(OQ-8). -/
def EwpMono (M : SemWorld) : Prop :=
  ∀ i i' e Tb Q ρ, TableI.Mono Tb → M.Ext i i' ρ → ewpW (ℍ := ℍ) M i e Tb Q ρ →
    ewpW (ℍ := ℍ) M i' e Tb Q ρ


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal hndE hndVal kappa
  clauseAt)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `handle_compatC` at W, at unr-free rows. -/
def HandleCompat (M : SemWorld) : Prop :=
  ∀ Δ Γ Γ₁ Γ₂ Γr Γc e S (E : List (Qual × VTy × VTy)) (n : UInt32) A R ir ic,
    Row.NU (Row.ofEff n E 0 ++ S) →
    Ctx.SplitP Γ Γ₁ Γ₂ → Ctx.SplitP Γ₁ Γr Γc → Ctx.SoloP Γr ir (retTy S A R) →
    Ctx.SoloP Γc ic (clausesTy S R E) → n ≠ 0 → (∀ o ∈ S, o.n ≠ n) → E.length ≤ 2 ^ 32 →
    SemW₀ M Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A)) →
    SemW₀ M Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R))

/-- Reduction is semantic identity (unary): a pure, non-allocating head step neither adds nor
removes programs from `ewpW` at a protocol table. -/
def RedLaws (M : SemWorld) : Prop :=
  ∀ (K : Kont) a a' i (T : OpTabI (Idx M.Stk)) Q ρ, (∀ μ, Head (ℍ := ℍ) μ a μ a') →
    a.allocs = false →
    (ewpW (ℍ := ℍ) M i (K.plug a) (opTabW M T) Q ρ ↔ ewpW (ℍ := ℍ) M i (K.plug a') (opTabW M T) Q ρ)

/-- **P11** at W. -/
def P11 (M : SemWorld) : Prop := HandleCompat M ∧ RedLaws (ℍ := ℍ) M


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The nil slice, the interaction's fields**: at σ = [] nothing is held and the stop is R-T1
(FIX-RUN-END §2.2).  With `B.SliceShapeB` it is `SliceShape`. -/
def SliceShapeI (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔
     (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls))

/-- `SliceShape` is `SliceShapeB` with `SliceShapeI`. -/
theorem sliceShape_iff (M : SemWorld) : SliceShape M ↔ B.SliceShapeB M ∧ SliceShapeI M :=
  ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨⟨h2, h3, h5, h6⟩, ⟨h1, h4⟩⟩,
   fun ⟨⟨h2, h3, h5, h6⟩, ⟨h1, h4⟩⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

/-- **Core's relation embeds into W at the nil index, at row-abortive types**, in both modes.  Beside
done, in the device (RESTRUCTURE §3.6): under any clause set that puts a future-world quantifier in
a value clause, `M.val` at a thunk or arrow type at the nil index already ranges over every W-future
of nil, so this asks Core's value to be valid at indices whose stack is not nil, which is
`ConservativeWB`'s content there; it has not been checked against every OQ-8 clause set. -/
def EmbedsNil (M : SemWorld) : Prop :=
  ∀ b A ls δ v ρ, A.AbortRows → vCE (ℍ := ℍ) none b A ls δ v ρ → M.val b A (ls, M.nil) δ v ρ

/-- **The proof device, beside done**: a route to the world conjuncts of done, at Core's placement
of the future-world quantifier.  W meets it when its proof follows the printed route.  Each
conjunct fixes an option of OQ-8 or OQ-9, or is rule-shaped at W (finding #5, RESTRUCTURE §3.6), so
none is in done. -/
def Device (M : SemWorld) (J : TypingJ) (Adm : OpAdm) (c : RowClass) : Prop :=
  Mono M ∧ ShareResume M ∧ ShareCancel (ℍ := ℍ) M ∧ StopVisible M ∧ FramesW (ℍ := ℍ) M c ∧
    SpanBorrows M J.out Adm c ∧ I1 (ℍ := ℍ) M ∧ I5 (ℍ := ℍ) M ∧ P11 (ℍ := ℍ) M ∧
    ConservativeWB (ℍ := ℍ) M ∧ EmbedsNil (ℍ := ℍ) M


end Targets

end
