import Spike743.Natural2
import GhostEnd.ClosureBody
import GhostEnd.RLCompat

/-!
# Spike743 — round P3: `StopTyped` and `RebuildAt` at `PinStop`'s first case

Round P2 (`Natural2.lean`) reduced `PinStopD` to `RelendOfTypedO` and named four clauses. This
file checks clauses 2 (`StopTyped`) and 3 (`RebuildAt`).

## Q1, route 1: the typed borrowers of GhostEnd

`RBody`, `RBodyT` and `RBodyC` are semantic judgments with one proved lemma per rule. A borrower
they read is re-lendable (`relend_of_rbodyC`), with its own measure (the least fixed point
`OpenD` and the typing derivation): the route does not go through `StopTyped`, `RebuildAt` or
`StopsWF`. It replaces them. The frame thaw is `tvg_thaw` and each stop's segment is typed by
construction (`rbodyC_let`).

The judgments are stated at `Row.Resume` (every operation linear) and `opTable`;
`RelendOfTypedO` is at `Row.ResumeO` (affine operations admitted) and `opTableO`. At a linear
row the two tables agree on what a callback owes (`opTable_le_opTableO`), so `Relend` carries over
(`relend_tab`). `relendOfTypedOLin_of_rbodyC` is the route's result: `RelendOfTypedO` at every
linear `ResumeO` row, from the fundamental lemma for `RBodyC` at `CDerivesP` (`RBodyCOfTypedP`).
`RBodyCOfTypedP` is not derived. The rule cases with a proved `RBody*` lemma are the pure pieces
(`rbodyC_ret`, its `SemC` premise from `fundamentalC` at `CDerives` and from the fundamental
property at `CDerivesP`), `thunk`, `[perform]`, `[let]`, `1E` and `+E` (`RBodyT`), `[lam]` and
`[app]` at an effectful arrow (`cloL_of_rbodyC`, `cloL_call`), and `bounded_fix`
(`open_boundedFix`). Without one: `⊗E`, `effSub`, `∀E` at a row, `[then]`, the four `[handle]`
rules, the unwinding lends at a row (`withbor*U`, `sliceBorrow*U`), and the relaxed lends
themselves (`lendR`, `lendRI`, `lendRF`, `lendRT`, `lendRH`), a lend inside the callback that
spans the callback's stop; and a pure piece handed a `CloL` closure.

## Q1, route 2: arising read semantically

* `ArisingF`: the configuration is in the relation at its own assignment. Preserved to every stop
  by construction (`arisingF_stop`: `ewp_unfold` at the row's table). The K2 of round P2 is inside
  it (`k2_arisingF`), and `LifeNatural` over it is refuted by the same witness
  (`not_lifeNaturalF`).
* `ArisingS`: `Arising` with the typing replaced by the semantic judgment `SemC`. `LifeNaturalV`
  over it holds with no hypothesis (`lifeNaturalS`), and the K2 is excluded by the premise
  `gDenC ls′ δ′ Γ γ ρ′` (`Natural2.k2_not_gDenC`). Its preservation to a stop is `StopTypedS`:
  the stop's continuation a `SegOf` segment of a semantically typed term. Not derived.

## Q2: `RebuildAt`

* `not_rebuildAt`: `RebuildAt` as stated does not hold. The context reads the view at a
  variable `'c` other than the lend's `'x` with the same lifetime: the shape of round P2's K2, at
  a re-lend below the old lifetime (`α′ = 3 ≤ α = 2`). Nothing ties `Γ` to the lend. The
  configuration is not shown arising.
* `RebuildAtTV`, proved (`rebuildAtTV`): the stopped context read as typed values (`TVG`, every
  slot the lend's view or a value free of `'x` outliving it, closures typed by their `CDerives`
  derivations), frozen at the stop (`tvg_freeze`), Kripke along `Ext` (`tvg_local`), thawed at
  every re-lend `α′ ≤ α` (`tvg_thaw`) and read back in the relation (`tv_sound`).
  `rebuildAtTV_closure` instantiates it at a closure capturing the view.
* `thunkF_config_excluded`: the configuration of `thunkF_RL_fails_below_at` has no view cell of
  the lend and its cell is below the lend, so it meets no hypothesis of `RebuildAt`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.Natural3
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Heap performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Spike743.Natural Spike743.Natural2
open GhostEnd (Relend relendF relendG opTableO owner finPost RBodyC ansRC TV TVG TabAt vwD)

/-! ## Q1, route 1 -/

/-- `relendG` is monotone in its table. -/
theorem relendG_tab {Tb Tb' : Table} (hT : ∀ ls t Φ ρ, Tb ls t Φ ρ → Tb' ls t Φ ρ)
    {l : BoCa.Loc} {T : VTy} {δ : LSub} {Q : List SRec → Val → WProp}
    {Φ : List SRec → Expr → WProp} {ls : List SRec} {e : Expr} :
    Entails (relendG Tb l T δ Q Φ ls e) (relendG Tb' l T δ Q Φ ls e) := by
  refine GhostEnd.fresh_mono fun α => GhostEnd.wand_mono_right fun _ hw =>
    wpG_mono (fun ls'' t σ hb => ?_) hw
  refine ⟨fun w ρ₁ ρ₂ h₁ hc₁ ρ₃ ρ₄ h₃ hc₃ => ?_, hb.2⟩
  rcases hb.1 w ρ₁ ρ₂ h₁ hc₁ ρ₃ ρ₄ h₃ hc₃ with hq | hq
  · exact Or.inl hq
  · exact Or.inr (hT _ _ _ _ hq)

/-- `Relend` is monotone in its table. -/
theorem relend_tab {Tb Tb' : Table} (hTb' : Tb'.Mono)
    (hT : ∀ ls t Φ ρ, Tb ls t Φ ρ → Tb' ls t Φ ρ) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Relend Tb l T δ Q ls e ρ) : Relend Tb' l T δ Q ls e ρ :=
  h (Relend Tb' l T δ Q) fun _ _ _ h' => GhostEnd.relend_fold hTb' (relendG_tab hT _ h')

/-- **At a linear row the unwinding frame's table admits every stop the row's table does.** A
linear stop owes no cancel, so `opTableO`'s cancel half is vacuous; the row has no abortive
operation, so `opTable`'s raise half is empty. -/
theorem opTable_le_opTableO {S : Row} {δ : LSub} (hlin : ∀ o ∈ S, o.q = .lin)
    (hna : ∀ o ∈ S, o.abort = false) (l : BoCa.Loc) (T : VTy) (δ' : LSub) :
    ∀ ls t Φ ρ, opTable (Row.tab S δ) ls t Φ ρ → opTableO (Row.tab S δ) l T δ' ls t Φ ρ := by
  intro ls t Φ ρ h
  rcases h with h | h
  · obtain ⟨K, n, i, v, en, h⟩ := h
    obtain ⟨hp, ρ₁, ρ₂, hc, hA, hk⟩ := pure_sep_iff.mp h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hp.2.2.1
    have hq : (o.ent δ).q = .lin := hlin o (Row.find_mem hf).1
    exact ⟨K, n, i, v, o.ent δ, pure_sep_mk hp
      ⟨ρ₁, ρ₂, hc, hA, fun ls' he => ⟨(hk.2 ls' he).1, fun hq' => absurd hq hq'⟩⟩⟩
  · obtain ⟨K, n, i, v, en, h⟩ := h
    obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    have : o.abort = false := hna o (Row.find_mem hf).1
    exact absurd ha (by simp [OpSig.ent, this])

/-- A `ResumeO` row all of whose operations are linear is a `Resume` row. -/
theorem resume_of_resumeO_lin {S : Row} {x : LifeVar} (hS : Row.ResumeO S x)
    (hlin : ∀ o ∈ S, o.q = .lin) : GhostEnd.Row.Resume S x := fun o ho =>
  let h := hS o ho
  ⟨h.1, h.2.2.2.2.1, hlin o ho, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- **`RelendOfTypedO` at the linear `ResumeO` rows.** -/
def RelendOfTypedOLin : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B →
    Row.ResumeO S x → (∀ o ∈ S, o.q = .lin) → Row.divB S = false → closedAt 1 M = true →
    CDerivesP (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    ∀ (δ : LSub), Δ.Models δ → ∀ (l : BoCa.Loc) (ls : List SRec),
      Relend (opTableO (Row.tab S δ) l T δ) l T δ (finPost l T B δ) ls
        (substAll [Val.loc l] M) PMap.empty

/-- **Route 1's missing clause: the fundamental lemma for `RBodyC` at `CDerivesP`.** Every
`PinStopD` callback at a linear row is a borrower `RBodyC` reads. Not derived. -/
def RBodyCOfTypedP : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B →
    Row.ResumeO S x → (∀ o ∈ S, o.q = .lin) → Row.divB S = false → closedAt 1 M = true →
    CDerivesP (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    RBodyC Δ x b T S [] true M (ansRC x (.box (.var x) B))

/-- **Route 1 at linear rows**: `RelendOfTypedO` from the fundamental lemma for `RBodyC`, by
`relend_of_rbodyC` and the linear table bridge. No `StopTyped`, `RebuildAt` or `StopsWF`. -/
theorem relendOfTypedOLin_of_rbodyC (H : RBodyCOfTypedP) : RelendOfTypedOLin := by
  intro Δ x b T B M S hb hx hbx hΔx hT hB hBn hS hlin hSd hM1 hM δ hδ l ls
  obtain ⟨β, hβ⟩ := hb δ hδ
  have hR := resume_of_resumeO_lin hS hlin
  exact relend_tab (GhostEnd.opTableO_mono _ _ _ _)
    (opTable_le_opTableO hlin (fun o ho => (hS o ho).1) l T δ)
    (GhostEnd.relend_of_rbodyC hT hB hδ hβ
      (H Δ x b T B M S hb hx hbx hΔx hT hB hBn hS hlin hSd hM1 hM) l ls)

/-! ## Q1, route 2 -/

/-- **Arising, read in the relation at the configuration's own assignment.** -/
def ArisingF (C : CTy) (δ : LSub) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  cC (ℍ := ℍ) C ls δ e ρ ∧ WorldArises ls ρ

/-- **`ArisingF` is preserved to every stop, by construction.** At a row without `Div`, a run of
an `ArisingF` configuration reaches a value in the relation, or a stop of the row's table whose
continuation, resumed at every extension and answer, is in the relation at the same `δ`. Every
step leaves a tagged typed world (`wpG`'s own conjuncts). -/
theorem arisingF_stop {S : Row} {A : VTy} {δ : LSub} {ls : List SRec} {e : Expr} {ρ : WRes}
    (hS : Row.divB S = false) (h : ArisingF (ℍ := ℍ) (CTy.effOf S A) δ ls e ρ) :
    wpG ls e (fun ls' t ρ' => valPost (fun ls v => vC true A ls δ v) ls' t ρ' ∨
      opTable (Row.tab S δ) ls' t (fun ls'' e'' => cC (ℍ := ℍ) (CTy.effOf S A) ls'' δ e'') ρ')
      ρ := by
  have hu := ewp_unfold (opTable_mono _) ((cC_effOf S A ls δ e ρ hS).mp h.1)
  refine wpG_mono (fun ls' t ρ' hq => hq.imp id fun hp => opTable_mono _ ls' t _ _ ρ' ?_ hp) hu
  intro ls'' e'' ρ'' h''
  exact (cC_effOf S A ls'' δ e'' ρ'' hS).mpr h''

/-- `LifeNatural` with `Arising` read as `ArisingF`. -/
def LifeNaturalF : Prop :=
  ∀ (Δ : LifeCtx) (E : Expr) (C : CTy) (γ : List Val) (δ δ' : LSub)
    (ls ls' : List SRec) (W : VTy) (w : Val) (ρr ρv ρv' ρ ρ' : WRes),
    ArisingF (ℍ := ℍ) C δ ls (substAll γ E) ρ → Δ.Models δ' → RegionShift δ δ' ls ls' ρr →
    Ext ls ls' ρr → ResU.CompS ρr ρv ρ → ResU.CompS ρr ρv' ρ' → SameMemory ρv ρv' →
    vC true W ls δ w ρv → vC true W ls' δ' w ρv' →
    cC (ℍ := ℍ) C ls' δ' (substAll γ E) ρ'

/-- The K2 is `ArisingF`. -/
theorem k2_arisingF :
    ArisingF (ℍ := ℍ) (.ret NaturalK2.A) NaturalK2.δ₀ [] (substAll [Val.loc NaturalK2.ℓ] (.var 0))
      NaturalK2.ρα :=
  ⟨(NaturalK2.k2_hyps (ℍ := ℍ)).2.2.2.2.2.2.2.2.2, NaturalK2.worldArises_ρα⟩

/-- **The semantic arising preserved by construction keeps the K2**: `LifeNaturalF` fails at it. -/
theorem not_lifeNaturalF : ¬ LifeNaturalF (ℍ := ℍ) := by
  intro hN
  obtain ⟨-, hδ', hsh, hext, hc, hc', hm, hv, hv', -⟩ := NaturalK2.k2_hyps (ℍ := ℍ)
  exact NaturalK2.k2_fails (hN _ (.var 0) _ [Val.loc NaturalK2.ℓ] NaturalK2.δ₀ NaturalK2.δ₁ [] []
    NaturalK2.W (.loc NaturalK2.ℓ) PMap.empty NaturalK2.ρα NaturalK2.ρα NaturalK2.ρα NaturalK2.ρα
    k2_arisingF hδ' hsh hext hc hc' hm hv hv')

/-- **Arising, the typing read semantically**: `Arising` with `CDerivesP` replaced by `SemC` and
the environment's typing dropped. -/
def ArisingS (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (C : CTy) (γ : List Val) (δ : LSub)
    (ls : List SRec) (ρ : WRes) : Prop :=
  SemC (ℍ := ℍ) Δ Γ E C ∧ Δ.Models δ ∧ gDenC ls δ Γ γ ρ ∧ WorldArises ls ρ

/-- An arising configuration is `ArisingS`, given the fundamental property. -/
theorem arisingS_of_arising (hF : FundamentalP (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {E : Expr}
    {C : CTy} {γ : List Val} {δ : LSub} {ls : List SRec} {ρ : WRes}
    (h : Arising Δ Γ E C γ δ ls ρ) : ArisingS (ℍ := ℍ) Δ Γ E C γ δ ls ρ :=
  ⟨hF _ _ _ _ h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- `LifeNaturalV` over `ArisingS`. -/
def LifeNaturalS : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (C : CTy) (γ : List Val) (δ δ' : LSub)
    (ls ls' : List SRec) (W : VTy) (w : Val) (ρr ρv ρv' ρ ρ' : WRes),
    ArisingS (ℍ := ℍ) Δ Γ E C γ δ ls ρ → Δ.Models δ' → RegionShift δ δ' ls ls' ρr →
    Ext ls ls' ρr → ResU.CompS ρr ρv ρ → ResU.CompS ρr ρv' ρ' → SameMemory ρv ρv' →
    vC true W ls δ w ρv → vC true W ls' δ' w ρv' → gDenC ls' δ' Γ γ ρ' →
    cC (ℍ := ℍ) C ls δ (substAll γ E) ρ → cC (ℍ := ℍ) C ls' δ' (substAll γ E) ρ'

/-- **`LifeNaturalS` holds**, from the semantic judgment `ArisingS` carries. -/
theorem lifeNaturalS : LifeNaturalS (ℍ := ℍ) :=
  fun _ _ _ _ γ _ δ' _ ls' _ _ _ _ _ _ ρ' hA hδ' _ _ _ _ _ _ _ hg _ => hA.1 δ' γ ls' ρ' hδ' hg

/-- `opTable` with each resuming stop's continuation an `ArisingS` segment. -/
def opTableS (Δ : LifeCtx) (C : CTy) (δ : LSub) (T : OpTab) : Table := fun ls t Φ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
          T n i = some en ∧ en.abort = false⌝ ⋆ (en.PA ls v ⋆ fun ρ =>
          contShare en ls K Φ ρ ∧
          ∃ (Γ' : Ctx VTy) (E' : Expr) (Bh : VTy) (γ' : List Val), GhostEnd.SegOf K E' γ' ∧
            ∀ ls', Ext ls ls' ρ → ∀ (w : Val) (σ ρ'' : WRes), en.PB ls' w σ →
              ResU.CompS σ ρ ρ'' → ArisingS (ℍ := ℍ) Δ (⟨Bh, true⟩ :: Γ') E' C (w :: γ') δ ls' ρ''))
    (opTable T ls t Φ)

/-- **Route 2's missing clause: semantic subject reduction to a stop.** An `ArisingS`
configuration at a row without `Div` runs at the row's table with each resuming stop's
continuation an `ArisingS` segment. `StopTyped` with `SemC` in place of `CDerivesP`. Not
derived. -/
def StopTypedS : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (S : Row) (A : VTy) (γ : List Val) (δ : LSub)
    (ls : List SRec) (ρ : WRes),
    ArisingS (ℍ := ℍ) Δ Γ E (CTy.effOf S A) γ δ ls ρ → Row.divB S = false →
    ewpTS ls (substAll γ E) (opTableS (ℍ := ℍ) Δ (CTy.effOf S A) δ (Row.tab S δ))
      (fun ls' v => vC true A ls' δ v) ρ

/-! ## Q2 -/

/-- The assignment `δ₀[x ↦ α]` reads `'c` at `2`. -/
theorem find_c (α : Life) : (NaturalK2.δ₀.extend 0 α).find? 1 = some (NaturalK2.L 2) := by
  rw [find?_extend_ne _ _ (show (0 : LifeVar) ≠ 1 by decide)]; rfl

/-- **`RebuildAt` as stated does not hold.** The context `c : Mut 'c 1` reads the lend's view at
`'c`, whose lifetime is `'x`'s, `2`. The lend moves `'x` to `3`, below the old lifetime, and
the re-lent cell is at `3`; `Mut 'c 1` at `2` needs a cell at a lifetime `⊒ 2`. Every hypothesis
holds, including `α′ ≤ α` and the rest in `Res_{α′}`, which `RebuildAt` does not ask. -/
theorem not_rebuildAt : ¬ RebuildAt := by
  intro H
  let P : List SRec → Val → WProp := fun ls₀ => vC true .unit ls₀ NaturalK2.δ₀
  have hg : gDenC [] (NaturalK2.δ₀.extend 0 (NaturalK2.L 2)) [⟨NaturalK2.W, true⟩]
      [Val.loc NaturalK2.ℓ] NaturalK2.ρα :=
    gDenC_mk (by simp [Ctx.LiveWithin])
      ⟨NaturalK2.ρα, PMap.empty, ResU.comp_empty_right _, NaturalK2.vC_view (find_c _) [], rfl,
        trivial⟩
  obtain ⟨ρ', hc', hg'⟩ := H [⟨NaturalK2.W, true⟩] [Val.loc NaturalK2.ℓ] NaturalK2.δ₀ 0
    (NaturalK2.L 2) (NaturalK2.L 3) .unit NaturalK2.ℓ [] [] PMap.empty NaturalK2.ρα NaturalK2.ρα
    (innerView NaturalK2.ℓ (NaturalK2.L 3)) hg (ResU.comp_empty_left _)
    (ResU.inStratum_empty _) (innerView_ptoMutS NaturalK2.ℓ _ [] _)
    (innerView_ptoMutS NaturalK2.ℓ _ [] _) (ext_refl [] _)
  obtain rfl := ResU.CompS.functional hc' (ResU.comp_empty_left _)
  obtain ⟨-, ρ₁, ρ₂, hc, hv, hρ₂, -⟩ := gDenC_iff.mp hg'
  subst hρ₂
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)
  obtain ⟨α₀, hα₀, ℓ₀, hs⟩ := hv
  rw [Lifetime.Life.interp_var, find_c] at hα₀
  obtain rfl : NaturalK2.L 2 = α₀ := Option.some.inj hα₀
  obtain ⟨hl, b, u, σ, hσ, Q, hw, ls₀, hle, he, -⟩ := pure_sep_iff.mp hs
  have hℓ : ℓ₀ = NaturalK2.ℓ := by cases hl; rfl
  subst hℓ
  have h1 := ResU.single_get_self NaturalK2.ℓ (CellU.mutOf b u σ hσ Q hw)
  rw [← he] at h1
  have h2 := ResU.single_get_self NaturalK2.ℓ (CellU.mutOf (NaturalK2.L 3) Val.unit PMap.empty
    (ResU.inStratum_empty _) (unitQ _) (unitQ_holds _))
  rw [show ResU.single NaturalK2.ℓ _ = innerView NaturalK2.ℓ (NaturalK2.L 3) from rfl, h1] at h2
  have hb : b = NaturalK2.L 3 := CellU.mutOf_at (Option.some.inj h2)
  subst hb
  exact absurd (show (3 : ℕ) ≤ 2 from hle) (by omega)

/-- **`RebuildAt` over typed values.** The stopped context read as typed values at the lend `α`
(`TVG`): slots the lend's view or free of `'x` and outliving it, pairs and sums of them, closures
typed by their `CDerives` derivations over such environments. It freezes at the stop into a part
in `Res_α` and the view it drops (`tvg_freeze`); at every re-lend `α′ ≤ α`, every list the frozen
part admits, and the view handed at `α′` if one was dropped, it is the context in the relation at
`δ[x ↦ α′]` (`tvg_local`, `tvg_thaw`, `tv_sound`), consistent with the table. Two changes from
`RebuildAt`, each a reason: the context is typed values (`not_rebuildAt` is a context not tied to
the lend), and the split is the freeze's (a cell of `ℓ` longer-lived than `α` is not dropped). -/
def RebuildAtTV : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (δ : LSub) (l : BoCa.Loc)
    (α : Life) (Γ : Ctx VTy) (γ : List Val) (ls : List SRec) (ρ : WRes),
    ¬ VFree x T → (Δ.extend x b).Models (δ.extend x α) →
    TVG Δ x b T δ l false α Γ γ ls false ρ → TabAt l α ρ →
    ∃ (d : Bool) (ρz ρn : WRes), ResU.CompS ρz ρn ρ ∧ vwD l T δ d α ls ρn ∧ ρz.InStratum α ∧
      ∀ (α' : Life) (ls' : List SRec) (ρv' ρ' : WRes), α' ≤ α →
        (Δ.extend x b).Models (δ.extend x α') → Ext ls ls' ρz → vwD l T δ d α' ls' ρv' →
        ResU.CompS ρz ρv' ρ' → gDenC ls' (δ.extend x α') Γ γ ρ' ∧ TabAt l α' ρ'

/-- **`RebuildAtTV` holds.** -/
theorem rebuildAtTV : RebuildAtTV := by
  intro Δ x b T δ l α Γ γ ls ρ hT hδα hg ht
  obtain ⟨d, ρz, ρn, hc, hz, hn⟩ := GhostEnd.tvg_freeze hT hδα hg rfl rfl ht
  refine ⟨d, ρz, ρn, hc, hn, GhostEnd.tvg_inStratum hz rfl, ?_⟩
  intro α' ls' ρv' ρ' hle hδ' he hv hc'
  obtain ⟨h', ht'⟩ := GhostEnd.tvg_thaw hT hle (GhostEnd.tvg_local he hz) rfl rfl ρv' ρ' hv hc'
  exact ⟨(GhostEnd.tv_sound hδ').2 h' rfl rfl, ht'⟩

/-- The callback's context `x ⊏ ⊤`, at `x = 0`. -/
abbrev Δc : LifeCtx := LifeCtx.empty.extend 0 .top

theorem Δc_models {α : Life} (hα : α ⊏ (Lifetime.SLife.top : Life)) :
    Δc.Models (LSub.empty.extend 0 α) :=
  GhostEnd.models_extend (models_empty_any _) rfl
    (fun _ _ h => by simp [LifeCtx.find?, LifeCtx.empty, Lifetime.assocFind] at h) rfl hα

/-- `thunk (return m)` closed by `m := ℓ`: a closure capturing the view. -/
def cloView (l : BoCa.Loc) : Val := Val.lam (Expr.psub 1 [Val.loc l] (.var 1))

/-- **A closure capturing the view is rebuilt at every re-lend.** The context
`f : U(F (Mut 'x 1))`, `f` the closure `thunk (return m)` over the view `ℓ ↦ M_α 𝒱⟦1⟧`, typed
at `x ⊏ ⊤`: at every `α′ ≤ α` below `⊤`, the frozen part with the view handed at `α′` is the
context in the relation at `[x ↦ α′]`. -/
theorem rebuildAtTV_closure (l : BoCa.Loc) {α : Life} (hα : α ⊏ (Lifetime.SLife.top : Life))
    (ls : List SRec) {ρ : WRes}
    (hm : ptoMutS l α ls (fun ls₀ => vC true .unit ls₀ LSub.empty) ρ) :
    ∃ (d : Bool) (ρz ρn : WRes), ResU.CompS ρz ρn ρ ∧ vwD l .unit LSub.empty d α ls ρn ∧
      ρz.InStratum α ∧
      ∀ (α' : Life) (ls' : List SRec) (ρv' ρ' : WRes), α' ≤ α →
        Ext ls ls' ρz → vwD l .unit LSub.empty d α' ls' ρv' → ResU.CompS ρz ρv' ρ' →
        gDenC ls' (LSub.empty.extend 0 α') [⟨.thunk (.ret (.mut (.var 0) .unit)), true⟩]
          [cloView l] ρ' := by
  have hT : ¬ VFree 0 VTy.unit := by simp [VFree]
  have hD : CDerives Δc [⟨.unit, false⟩, ⟨.mut (.var 0) .unit, true⟩] (.var 1)
      (.comp (.ret (.mut (.var 0) .unit))) := .ret (.var (.there (.here .nil)))
  have hg : TVG LifeCtx.empty 0 .top .unit LSub.empty l false α
      [⟨.thunk (.ret (.mut (.var 0) .unit)), true⟩] [cloView l] ls false ρ :=
    .live (.cloF (Γf := [⟨.mut (.var 0) .unit, true⟩]) (γf := [Val.loc l]) hD
      (.live (.atomL (Or.inl rfl) (GhostEnd.mutView hT hm)) .nil (by simp)
        (ResU.comp_empty_right _))) .nil (by simp) (ResU.comp_empty_right _)
  obtain ⟨d, ρz, ρn, hc, hn, hz, hk⟩ :=
    rebuildAtTV _ _ _ _ _ _ _ _ _ _ _ hT (Δc_models hα) hg (GhostEnd.tabAt_view hm)
  refine ⟨d, ρz, ρn, hc, hn, hz, fun α' ls' ρv' ρ' hle he hv' hc' => ?_⟩
  exact (hk α' ls' ρv' ρ' hle (Δc_models (lt_of_le_of_lt hle hα)) he hv' hc').1

/-- **The configuration of `thunkF_RL_fails_below_at` meets no hypothesis of `RebuildAt`.** Its
resource `innerView 1 2` holds no cell of the lend's location `0`, so it has no split off a view
`ptoMutS 0 α`; and its cell, at `2`, is below the lend `1`, so it is not in `Res_1`. -/
theorem thunkF_config_excluded (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    (¬ ∃ ρr ρv, ResU.CompS ρr ρv (innerView 1 (NaturalK2.L 2)) ∧ ptoMutS 0 α ls P ρv) ∧
      ¬ (innerView 1 (NaturalK2.L 2)).InStratum (NaturalK2.L 1) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ρr, ρv, hc, b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩
    have hk : (CellU.mutOf b u σ hσ Q hw).kind ≠ Kind.imm := by
      rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
    have h0 := (ResU.CompS.get_right_of_ne_imm hc (ResU.single_get_self _ _) hk).2
    rw [show innerView 1 (NaturalK2.L 2) = ResU.single 1 _ from rfl,
      ResU.single_get_ne _ (show (0 : BoCa.Loc) ≠ 1 by decide)] at h0
    cases h0
  · have := h 1 _ (ResU.single_get_self _ _)
    exact lt_asymm (show NaturalK2.L 2 < NaturalK2.L 1 from
      OrderDual.toDual_lt_toDual.mpr (by decide)) this

end Spike743.Natural3

end
