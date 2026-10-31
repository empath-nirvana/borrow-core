import Core.PinFundamental
import Spike743.Round3
import GhostEnd.Segment
import Restrat.Fixed
import LoopBorrow.Dormant

/-!
# Spike743 — round P: `LifeNatural`, one principle behind every `PinLaw` field

Every field of `PinLaw` is argued the same way: at a stop the lend is ended (ghost end), at the
resumption the place is lent again at a fresh lifetime, and the suspended code is claimed to be
in the relation still. The last step is a re-assignment of lifetimes. `LifeNatural` states it
once, over Core's relation (`cC`/`vC`), at the configurations typed programs reach.

## The statement

* **Arising** (`Arising`). A configuration is a typed segment `E` (a `CDerivesP` derivation)
  closed by arising values `γ` (`AEnv`: first-order data, values typed in `CDerivesP` over arising
  values, captured continuations whose segment is typed), at a substitution modelling its
  lifetime context, with the share in `𝒢⟦Γ⟧` and a frame making it a tagged typed world
  (`WorldArises`, the worlds `wpTS`'s frame quantifier ranges over: `TW` is the family of worlds
  typed programs reach, closed under the steps runs take). A stopped continuation is such a
  segment (`GhostEnd.SegOf`); that every stop of an arising run is one is
  `ArisingStopsTyped`, named, not proved.
* **The shift** (`RegionShift`). `δ'` re-assigns the variables of the lend region: wherever `δ`
  and `δ'` differ, both bind the variable, the old lifetime no longer than every record of the
  old list and the new no longer than every record of the new list, and every borrow cell of the
  rest of the share strictly longer-lived than both. `δ'` models the same lifetime context.
* **`LifeNatural`.** At an arising configuration whose share is `ρr ● ρv`, `ρv` the resource of a
  value `w : W` read at `δ`, the computation is still in the relation at `δ'`, at any list `ls'`
  the rest admits (`Ext ls ls' ρr`), with `ρv` replaced by any `ρv'` in `𝒱⟦W⟧` at `δ'` and `ls'`.

No clause mentions a depth, a number of lends or a type former: `C`, `W` and the segment are
arbitrary, and every variable that moves moves at once.

## What forced each refinement of `WpNatural`

`Restrat.Open.WpNatural` moves a whole configuration by the image action of a re-stratification.
At Core's relation four witnesses bear on that:

* `mut_not_natural`: the image of a `mut` cell stores the image of its invariant, which is not
  `𝒱⟦T⟧` at the moved substitution. Its configuration is typed (`return x`,
  `x : Mut 'a (Imm 'b 1)`). So `LifeNatural` does not transport the moved part of the share: `ρv'`
  is any resource of `𝒱⟦W⟧` at `δ'`, the cell the re-lend builds (`GhostEnd.relent_holds`), and the
  rest `ρr` is not moved (`rest_fixed`: every re-stratification whose cut lies below the rest's
  cells is the identity on it).
* `refoldKripke_false`, `refold_fails_at_consumer_frame`, `ext_adds_record`,
  `Round4.ext_adds_record_below_cell`: the list a holder resumes at may hold records above the
  lend's old lifetime, which no `Ext`-extension of the stopped share admits. So the list is not
  moved either: `ls'` is any list the *rest* admits, and the new lifetime is below all of it
  (`consumer_frame_in_scope`, `stored_record_in_scope`).
* `coreAllNotNatural` / `not_coreThawTop` (`origin/targets`): Core's `∀` reads the room between
  lifetimes, at a `Λ` returning a pre-existing view at its bound lifetime. So arising is typed:
  a value is arising only as typed code builds it.
* `thunkF_RL_fails_below_at`: a closure over an inner view below the lend fails the single-lend
  re-lendable relation. So the shift moves every variable that differs at once, and the inner view
  is part of `ρv`; `LifeNatural`'s conclusion holds there at every new lifetime
  (`thunk_inner_relent`).

## What is derived from it

`fundamentalC_of_frames`: every `CDerivesP` derivation is sound given `LifeNatural`, `LendFrame` and
`LoopFrame`, by `fundamentalC_pin`'s induction with the six relaxed cases taken from the frames at
the induction hypothesis of the callback. So nesting adds no clause: a lend inside a lend is the
inner derivation's case. `field_of_natural_*` and `pinLaw_of_natural` read the six fields off it.

`LendFrame` and `LoopFrame` are the named missing clauses: the lender's frame across resumptions at
one level, for the `withborUV` forms (`LendForm`: `mut`/`imm` at `Ref T`, the nursery scope, the
family at an array) and for the per-observation lend. They are stated with `LifeNatural` as a
premise and with the callback's relation (`SemC`) for its derivation; neither mentions a depth or a
holder. The Lean derivations here do not check that their proofs use `LifeNatural` only at the
re-lend: that is the structure of `GhostEnd.withbor_relend` (`Relend` is the continuation re-lent at
a fresh lifetime) and of `Spike743.r2_next_obs`.

Nothing here proves `LifeNatural`, `LendFrame` or `LoopFrame`. `LifeNatural` as stated does not
hold (`Spike743.NaturalK2.not_lifeNatural`): `W` is not tied to the context `Γ`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743.Natural
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Heap)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Arising -/

/-- The share `ρ` at the list `ls` is part of a tagged typed world: some frame completes it to a
`TW` world at the list's records, tagged by the list. These are the worlds `wpTS`'s frame
quantifier ranges over. -/
def WorldArises (ls : List SRec) (ρ : WRes) : Prop :=
  ∃ (ρf fρ : WRes) (ps : List FrameRec),
    ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls

/-- First-order data: no `λ` anywhere in the value. -/
inductive IsData : Expr → Prop
  | unit : IsData .unit
  | loc {l : Loc} : IsData (.loc l)
  | prim {p : Prim} : IsData (.prim p)
  | pair {a b : Expr} : IsData a → IsData b → IsData (.pair a b)
  | inj₁ {a : Expr} : IsData a → IsData (.inj₁ a)
  | inj₂ {a : Expr} : IsData a → IsData (.inj₂ a)
  | storeV {a : Expr} : IsData a → IsData (.app (.prim .store) a)

mutual
/-- **An arising value**: what typed code builds. First-order data; a value term typed in
`CDerivesP`, closed by arising values (closures among them); or a continuation `κ` the `[op]` step
captures (`kappa`, `kappaC`) whose handler is arising and whose segment is typed and closed by
arising values. -/
inductive AVal : Val → Prop
  | data {v : Val} : IsData v.1 → AVal v
  | typed {Δ : LifeCtx} {Γ : Ctx VTy} {u : Expr} {A : VTy} {γ : List Val} {v : Val} :
      CDerivesP Δ Γ u (.val A) → AEnv γ → substAll γ u = v.1 → AVal v
  | kont {Δ : LifeCtx} {Γ : Ctx VTy} {E : Expr} {B : VTy} {C : CTy} {γ : List Val}
      {H : Val} {K : Kont} {v : Val} :
      CDerivesP Δ (⟨B, true⟩ :: Γ) E (.comp C) → GhostEnd.SegOf K E γ → AEnv γ → AVal H →
      (v.1 = BoCa.BoLo.kappa H K ∨ ∃ (c : Bool) (l : Loc), v.1 = BoCa.BoLo.kappaC c l H K) →
      AVal v
/-- An environment of arising values. -/
inductive AEnv : List Val → Prop
  | nil : AEnv []
  | cons {v : Val} {γ : List Val} : AVal v → AEnv γ → AEnv (v :: γ)
end

/-- **An arising configuration**: the typed segment `Δ; Γ ⊢ E : C` closed by the arising values
`γ`, at `δ ⊨ Δ`, with the share `ρ` in `𝒢⟦Γ⟧(ls)δ(γ)` and part of a tagged typed world. -/
def Arising (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (C : CTy) (γ : List Val) (δ : LSub)
    (ls : List SRec) (ρ : WRes) : Prop :=
  CDerivesP Δ Γ E (.comp C) ∧ AEnv γ ∧ Δ.Models δ ∧ gDenC ls δ Γ γ ρ ∧ WorldArises ls ρ

/-- **The closure step, named.** A run of a typed program closed by arising values that reaches a
stop `K[perform p]` reaches it at a typed segment: `K` is `E′` closed by arising values. This is
subject reduction to a stop; it is what makes `Arising` closed under the steps runs take. Not
proved here. -/
def ArisingStopsTyped : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (C : CTy) (γ : List Val) (μ μ' : Heap) (K : Kont)
    (p : Val),
    CDerivesP Δ Γ E (.comp C) → AEnv γ →
    BoCa.BoLo.Steps (ℍ := ℍ) μ (substAll γ E) μ' (K.plug (BoCa.BoLo.performE (.val p))) →
    ∃ (Δ' : LifeCtx) (Γ' : Ctx VTy) (E' : Expr) (B : VTy) (C' : CTy) (γ' : List Val),
      CDerivesP Δ' (⟨B, true⟩ :: Γ') E' (.comp C') ∧ GhostEnd.SegOf K E' γ' ∧ AEnv γ'

/-! ### The shift and the principle -/

/-- **`δ′` shifts the lend region of `δ`.** Wherever the two differ, both bind the variable; its
old lifetime is no longer than every record of `ls`, its new one no longer than every record of
`ls′`, and every borrow cell of the rest `ρr` is strictly longer-lived than both. -/
def RegionShift (δ δ' : LSub) (ls ls' : List SRec) (ρr : WRes) : Prop :=
  ∀ y, δ'.find? y ≠ δ.find? y → ∃ a a' : Life,
    δ.find? y = some a ∧ δ'.find? y = some a' ∧
    (∀ r ∈ ls, a ≤ r.2) ∧ (∀ r ∈ ls', a' ≤ r.2) ∧ ρr.InStratum a ∧ ρr.InStratum a'

/-- Two resources lower to the same memories: a shift moves lifetimes, not memory. -/
def SameMemory (ρ ρ' : WRes) : Prop := ∀ μ, ResU.Lower ρ μ ↔ ResU.Lower ρ' μ

/-- **`LifeNatural`.** Core's relation is invariant under shifting the lend region at arising
configurations: the computation of an arising configuration whose share is `ρr ● ρv`, `ρv` the
resource of `w : W` at `δ`, is in the relation at a shift `δ′` of `δ` that models the same
context, at every list `ls′` the rest admits, with `ρv` replaced by any resource of `𝒱⟦W⟧` at `δ′`
and `ls′` over the same memory. -/
def LifeNatural : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (E : Expr) (C : CTy) (γ : List Val) (δ δ' : LSub)
    (ls ls' : List SRec) (W : VTy) (w : Val) (ρr ρv ρv' ρ ρ' : WRes),
    Arising Δ Γ E C γ δ ls ρ → Δ.Models δ' → RegionShift δ δ' ls ls' ρr → Ext ls ls' ρr →
    ResU.CompS ρr ρv ρ → ResU.CompS ρr ρv' ρ' → SameMemory ρv ρv' →
    vC true W ls δ w ρv → vC true W ls' δ' w ρv' →
    cC (ℍ := ℍ) C ls δ (substAll γ E) ρ → cC (ℍ := ℍ) C ls' δ' (substAll γ E) ρ'

/-! ### Proved constructs -/

/-- `Ext` is reflexive. -/
theorem ext_refl (ls : List SRec) (ρ : WRes) : Ext ls ls ρ :=
  ⟨fun _ h _ => h, fun _ _ _ _ => Iff.rfl⟩

/-- The identity is a shift. -/
theorem regionShift_refl (δ : LSub) (ls : List SRec) (ρr : WRes) :
    RegionShift δ δ ls ls ρr := fun _ h => absurd rfl h

/-- **The statement's hypotheses are consistent**: at the identity shift, the same list and the
same view resource, `LifeNatural`'s conclusion is its hypothesis. -/
theorem lifeNatural_refl {C : CTy} {ls : List SRec} {δ : LSub} {e : Expr} {ρr ρv ρ ρ' : WRes}
    (hc : ResU.CompS ρr ρv ρ) (hc' : ResU.CompS ρr ρv ρ') (h : cC (ℍ := ℍ) C ls δ e ρ) :
    cC (ℍ := ℍ) C ls δ e ρ' := by
  rwa [ResU.CompS.functional hc' hc]

/-- **A shift of variables the type does not mention** is invisible to the relation at the same
list and the same view resource (`cC_congr`). -/
theorem lifeNatural_unmentioned {C : CTy} {ls : List SRec} {δ δ' : LSub} {e : Expr}
    {ρ : WRes} (hC : ∀ y, CFree y C → δ.find? y = δ'.find? y)
    (h : cC (ℍ := ℍ) C ls δ e ρ) : cC (ℍ := ℍ) C ls δ' e ρ := by
  rwa [← cC_congr C hC ls]

/-- **A re-stratification moves the substitution and fixes the rest.** For `e : Emb c`, the shift
`f ∘ δ` models every context `δ` models (`Restrat.Emb.models_mapN_iff`), and every share whose
cells are strictly longer-lived than the cut is its own image (`Restrat.Emb.relRU_of_inStratum`).
So `LifeNatural`'s conclusion configuration is the image of its hypothesis configuration on the
substitution and the rest; only the view is rebuilt and the list grown. -/
theorem rest_fixed {c : Life} (e : Restrat.Emb c) (Δ : LifeCtx) (δ : LSub) (ρr : WRes)
    (hr : ρr.InStratum c) (hδ : Δ.Models δ) :
    Δ.Models (Restrat.LSub.mapN e.toNat δ) ∧ e.relRU ρr = ρr :=
  ⟨(e.models_mapN_iff Δ δ).mpr hδ, e.relRU_of_inStratum hr⟩

/-- **The single-lend re-lend, from `LifeNatural`.** At a stop of a callback lent at `α` (the
variable `x`), the suspended configuration, its view `ρv` at `α` and its rest `ρr` strictly above
`α`, is in the relation at every later list the rest admits, lent again at every `α′` no longer
than that list's records and below the rest, with any view `ρv′` there over the same memory. This
is the premise `GhostEnd.relendF` asks of a resumed continuation (the owner handed back, the
callback lent afresh): `LifeNatural` at the shift `δ[x ↦ α] ↦ δ[x ↦ α′]`. -/
theorem relend_of_natural (hN : LifeNatural (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy} {E : Expr}
    {C : CTy} {γ : List Val} {δ : LSub} {x : LifeVar} {α α' : Life} {ls ls' : List SRec}
    {W : VTy} {w : Val} {ρr ρv ρv' ρ ρ' : WRes}
    (hA : Arising Δ Γ E C γ (δ.extend x α) ls ρ) (hδ' : Δ.Models (δ.extend x α'))
    (hα : ∀ r ∈ ls, α ≤ r.2) (hα' : ∀ r ∈ ls', α' ≤ r.2) (hrα : ρr.InStratum α)
    (hrα' : ρr.InStratum α') (hext : Ext ls ls' ρr)
    (hc : ResU.CompS ρr ρv ρ) (hc' : ResU.CompS ρr ρv' ρ') (hm : SameMemory ρv ρv')
    (hv : vC true W ls (δ.extend x α) w ρv) (hv' : vC true W ls' (δ.extend x α') w ρv')
    (h : cC (ℍ := ℍ) C ls (δ.extend x α) (substAll γ E) ρ) :
    cC (ℍ := ℍ) C ls' (δ.extend x α') (substAll γ E) ρ' := by
  refine hN Δ Γ E C γ _ _ ls ls' W w ρr ρv ρv' ρ ρ' hA hδ' (fun y hy => ?_) hext hc hc' hm hv hv' h
  by_cases hxy : x = y
  · subst hxy
    exact ⟨α, α', find?_extend_self _ _ _, find?_extend_self _ _ _, hα, hα', hrα, hrα'⟩
  · exact absurd (by rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]) hy

/-! ### The refutations, read against `LifeNatural` -/

/-- **`refold_fails_at_consumer_frame`, in scope.** The consumer's list `[(r, γ)]` is the list of a
tagged typed world holding the lender (`WorldArises`). It is admitted by the rest of the stopped
share, the owner `ℓ ↦ own(w)` (`LifeNatural`'s premise `Ext ls ls' ρr`), and by no state holding
the lend folded at `α ⊏ γ` (`RefoldKripke`'s demand). `LifeNatural` re-lends below `γ`; it does
not refold at `α`. -/
theorem consumer_frame_in_scope (l l' : Loc) (hl : l' ≠ l) (w : Val) (δ : LSub) :
    ∃ r : FrameRec,
      WorldArises [(r, OrderDual.toDual 1)] (ResU.single l (CellU.ownOf w)) ∧
      Ext [] [(r, OrderDual.toDual 1)] (ResU.single l (CellU.ownOf w)) ∧
      ¬ Ext [] [(r, OrderDual.toDual 1)] (LoopBorrow.mutCell l (OrderDual.toDual 2) w) := by
  obtain ⟨-, -, ρf, fρ, r, hH, hc, hT, htg, he, hne⟩ :=
    LoopBorrow.refold_fails_at_consumer_frame l l' hl w δ
  exact ⟨r, ⟨ρf, fρ, [r], hH, hc, hT, htg⟩, he, hne⟩

/-- **`ext_adds_record`, `ext_adds_record_below_cell`, in scope.** Whatever record a holder adds,
at whatever lifetime `β`, the rest of a stopped share with no borrow cell admits the list, and a
new lifetime no longer than `β` is no longer than every record of it: `RegionShift`'s premise on
the new list holds at `β` itself. -/
theorem stored_record_in_scope (r : FrameRec) (β : Life) :
    Ext [] [(r, β)] PMap.empty ∧ ∀ x ∈ ([(r, β)] : List SRec), β ≤ x.2 := by
  refine ⟨⟨fun r' hr' _ => by simp [rsOf] at hr', fun b hb => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨m, ψ, hg, -, -⟩ := hb
    simp [PMap.empty] at hg
  · rw [List.mem_singleton] at hx
    subst hx
    exact le_rfl

/-- `𝒱⟦1⟧` as a stored predicate at `b`. -/
def unitQ (b : Life) : Val → SPropS Loc Val b :=
  fun v => SPropU.toS b (BoLo.pure (v = Val.unit))

theorem unitQ_holds (b : Life) : unitQ b Val.unit ⟨PMap.empty, ResU.inStratum_empty b⟩ :=
  ⟨rfl, rfl⟩

/-- An inner lend's view `k ↦ M_{αy} 𝒱⟦1⟧` (`GhostEnd.innerView`). -/
def innerView (k : Loc) (αy : Life) : WRes :=
  ResU.single k (CellU.mutOf αy Val.unit PMap.empty (ResU.inStratum_empty αy) (unitQ αy)
    (unitQ_holds αy))

theorem innerView_ptoMutS (k : Loc) (αy : Life) (ls : List SRec) (δ' : LSub) :
    ptoMutS k αy ls (fun ls₀ => vC true .unit ls₀ δ') (innerView k αy) := by
  refine ⟨αy, Val.unit, PMap.empty, ResU.inStratum_empty αy, unitQ αy, unitQ_holds αy,
    ls.filter (fun r => decide (r.2 ⊐ αy)), le_rfl, rfl, ?_, ?_, ?_⟩
  · funext v ρ
    apply propext
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      exact ⟨by obtain ⟨rfl, -⟩ := h; exact ResU.inStratum_empty αy, h⟩
  · intro r; simp [List.mem_filter]
  · rintro ls' u' σ' ⟨rfl, -⟩; exact ResU.inStratum_empty αy

/-- The closure `thunk (return n)` over the inner view `n = k`, closed: `λ_. k`. -/
def thunkK (k : Loc) : Val := ⟨.lam (.loc k), .lam⟩

/-- **`thunkF_RL_fails_below_at`, in scope: the conclusion holds at every re-lend.** The closure
`λ_. n` over an inner view `n : Mut 'y 1` is in Core's relation at `U(F(Mut 'y 1))` with the view
cell at whatever lifetime `δ` gives `'y`, at every list. So at the configuration where the
single-lend re-lendable relation fails, `LifeNatural`'s conclusion holds for every shift that
moves `'y` (with the cell in `ρv`, rebuilt at the new lifetime). -/
theorem thunk_inner_relent (k : Loc) (y : LifeVar) (δ : LSub) (αy : Life)
    (hy : δ.find? y = some αy) (ls : List SRec) :
    cC (ℍ := ℍ) (.ret (.thunk (.ret (.mut (.var y) .unit)))) ls δ (.val (thunkK k))
      (innerView k αy) := by
  refine wpTS_val ls _ _ _ ?_
  intro ls' _
  show wpTS ls' (.app (.val (thunkK k)) (.val Val.unit)) _ _
  refine wpTS_head (e' := .val ⟨.loc k, .loc⟩) (fun μ => ?_) rfl ls' _ _ ?_
  · exact BoCa.BoLo.Head.beta μ (.loc k) Val.unit
  · refine wpTS_val ls' _ _ _ ⟨αy, ?_, k, pure_sep_mk rfl (innerView_ptoMutS k αy ls' δ)⟩
    rw [Lifetime.Life.interp_var, hy]; rfl

/-! ### The missing clauses -/

/-- The lend forms of the relaxed `withborUV` rules: the place's type `P`, the view `V` the
callback is typed at, the answer `B`, the callback's lifetime context `Δb`, and whether its row may
hold `tick`, the cancel path's `await` and escaping errors (`Row.ResumeOE`) or not
(`Row.ResumeO`). `ref k`: `lendRT` (and `lendR`, `lendRI`);
`hold k y`: `lendRH`; `fam`: `lendRF`. -/
inductive LendForm (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) :
    VTy → VTy → VTy → LifeCtx → Bool → Prop
  | ref (k : Bool) {T B : VTy} : ¬ VFree x T → LendSide k Δ T →
      LendForm Δ x b (.ref T) (lendView k x T) B (Δ.extend x b) true
  | hold (k : Bool) (y : LifeVar) {T B : VTy} : ¬ VFree x T → ¬ VFree y T → ¬ VFree y B →
      LendSide k Δ T → (Δ.extend x b).find? y = none →
      (∀ z u, (Δ.extend x b).find? z = some u → u.mentions y = false) →
      LendForm Δ x b (.ref T) (lendView k x T) B ((Δ.extend x b).extend y (.var x)) true
  | fam {A B : VTy} : ¬ VFree x A → (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' A) →
      (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' B) →
      LendForm Δ x b (.array A) (VTy.sliceMut (.var x) A) B (Δ.extend x b) false

/-- The row a lend form admits. -/
def RowOf (tk : Bool) (S : Row) (x : LifeVar) : Prop :=
  if tk then Row.ResumeOE S x else Row.ResumeO S x

/-- **Missing clause: the lender's frame across resumptions, one level, every `withborUV` form.**
Given `LifeNatural`, a relaxed lend whose callback is typed (`CDerivesP`, so its stops are
arising) and in the relation (`SemC`) is in the relation. This is 6.65/6.64 at a resuming table:
the lend ended at each stop, lent again at a fresh lifetime at the resumption (`LifeNatural`'s
re-lend), the place returned at the end or at a cancel. Uniform in depth (a nested lend is in the
callback's `SemC`) and in the holder (none is mentioned). -/
def LendFrame : Prop :=
  LifeNatural (ℍ := ℍ) →
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

/-- **Missing clause: the per-observation lend's frame (R2).** Given `LifeNatural`, the
per-observation `imm` lend whose steps and first state are typed and in the relation is in the
relation at `U(Loop (Ref A ⊗ B) (Ref A ⊗ R))`. One observation is `Spike743.r2_next_obs`
(`ewpTS_I_frameR`); across observations it is the state invariant re-lent at each fresh `'x`. -/
def LoopFrame : Prop :=
  LifeNatural (ℍ := ℍ) →
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
theorem fundamentalC_of_frames (hN : LifeNatural (ℍ := ℍ)) (hF : LendFrame (ℍ := ℍ))
    (hL : LoopFrame (ℍ := ℍ)) (hFin : PinFin (ℍ := ℍ)) {Δ : LifeCtx} {Γ : Ctx VTy}
    {e : Expr} {j : Jdg} (h : CDerivesP Δ Γ e j) : SemJ (ℍ := ℍ) Δ Γ e j := by
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
  | effPerform hf hna _ _ ih => exact perform_compatC hf hna ih
  | effAwait hΓ hfa ha haA hfc hc hcA => exact semC_dead .nil hΓ (await_compatC hfa ha haA hfc hc hcA)
  | effRaise hf ha hd _ ih => exact raise_compatC hf ha (fun _ _ _ _ h => vC_noOwn_of_ownFree hd h) ih
  | effLet hs hW hU _ _ ihM ihN => exact let_compatC hs hW hU ihM ihN
  | effThen hs hNZ _ hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact then_compatC hs hNZ hU hMS hDS (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂
        (by simp [OpSig.finRead, hc])) hP hSD ihM ihN ihD
  | effThenDiv hs hNZ _ hU hMS hDS hfin hP hcap _ _ _ ihM ihN ihD =>
      exact hFin _ _ _ _ _ _ _ _ _ _ _ _ hs hNZ hU hMS hDS hfin hP hcap ihM ihN ihD
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
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS.toE) hM1 hcb hdc ihd
        (by simpa [lendView] using hM) (by simpa [lendView, SemJ] using ihM)
  | lendRI hb hx hbx hΔx hT hB hBn hsc hS hM1 hcb hdc _ hM ihd ihM =>
      exact hF hN _ _ _ _ _ _ _ _ _ _ _ (.ref true hT (by simpa [LendSide] using hsc))
        hb hx hbx hΔx hB hBn (by simpa [RowOf] using hS.toCE.toE) hM1 hcb hdc ihd
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

section Fields
variable (hN : LifeNatural (ℍ := ℍ)) (hF : LendFrame (ℍ := ℍ)) (hL : LoopFrame (ℍ := ℍ))
  (hFin : PinFin (ℍ := ℍ))
include hN hF hL hFin

/-- **W-tick from `LifeNatural`** (and `LendFrame` at `ref k`). -/
theorem field_of_natural_tick : PinStopTick (ℍ := ℍ) :=
  fun Δ x b T B d M S k hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc hd hM =>
    hF hN _ _ _ _ _ _ _ _ _ _ _ (.ref k hT hside) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_frames hN hF hL hFin hM)

/-- **R1 from `LifeNatural`**: W-tick at `k = false` (`Round3.pinStop_of_tick`). -/
theorem field_of_natural_stop : PinStop (ℍ := ℍ) :=
  Spike743.Round3.pinStop_of_tick (field_of_natural_tick hN hF hL hFin)

/-- **W-imm from `LifeNatural`**: W-tick at `k = true` (`Round3.pinStopImm_of_tick`). -/
theorem field_of_natural_stopImm : PinStopImm (ℍ := ℍ) :=
  Spike743.Round3.pinStopImm_of_tick (field_of_natural_tick hN hF hL hFin)

/-- **W-nest from `LifeNatural`** (and `LendFrame` at `fam`). -/
theorem field_of_natural_nest : PinNest (ℍ := ℍ) :=
  fun Δ x b A B d M S hb hx hbx hΔx hA hB hBn hsideA hsideB hS hM1 hcb hdc hd hM =>
    hF hN _ _ _ _ _ _ _ _ _ _ _ (.fam hA hsideA hsideB) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_frames hN hF hL hFin hM)

/-- **W-hold from `LifeNatural`** (and `LendFrame` at `hold k y`). -/
theorem field_of_natural_hold : PinStopHold (ℍ := ℍ) :=
  fun Δ x y b T B d M S k hb hx hbx hΔx hy hΔy hT hB hyT hyB hBn hside hS hM1 hcb hdc hd hM =>
    hF hN _ _ _ _ _ _ _ _ _ _ _ (.hold k y hT hyT hyB hside hy hΔy) hb hx hbx hΔx hB hBn
      (by simpa [RowOf] using hS) hM1 hcb hdc hd hM (fundamentalC_of_frames hN hF hL hFin hM)

/-- **R2 from `LifeNatural`** (and `LoopFrame`). -/
theorem field_of_natural_loop : PinLoop (ℍ := ℍ) :=
  fun Δ x A S B R N K s0 hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0 =>
    hL hN Δ x A S B R N K s0 hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN' hK hs0
      (fundamentalC_of_frames hN hF hL hFin hN') (fundamentalC_of_frames hN hF hL hFin hK)
      (fundamentalC_of_frames hN hF hL hFin hs0)

/-- **`PinLaw` from `LifeNatural`** and the two frames. -/
theorem pinLaw_of_natural : PinLaw (ℍ := ℍ) where
  stop := field_of_natural_stop hN hF hL hFin
  loop := field_of_natural_loop hN hF hL hFin
  stopImm := field_of_natural_stopImm hN hF hL hFin
  nest := field_of_natural_nest hN hF hL hFin
  tick := field_of_natural_tick hN hF hL hFin
  hold := field_of_natural_hold hN hF hL hFin
  fin := hFin

end Fields

end Spike743.Natural

end
