import GhostEnd.StackStep
import Core.Demonic

/-!
# GhostEnd — GFP at a non-empty stack, against D16.1's `∀` and `⊸` clauses (#279)

GFP (D16.2) is stated in `Stacked.lean` at D16.1. This file shows that, as stated, it does not
hold at the stack `[x]` (`not_gfpAt_below`, `not_gfp`), on a two-rule derivation (`allI` over
`lam`), every hypothesis of `GFPAt` discharged.

## The configuration

`Δ = x ⊏ ⊤`, `σ = [x]` (a `mut` lend at the variable `x`), the lend at `α = 1`, the empty
context and resource. The term is `Λ. λn. return (thunk (return n))` at
`∀'y ⊏ ⊓Δ. Mut 'y 1 ⊸ F (U (F (Mut 'y 1)))`, the shape of a borrow callback's type.

1. D16.1's `∀` clause instantiates `'y` at every lifetime below `⊓Δ`, and `⊓Δ` is `x`'s, so `'y`
   may be `3 ⊏ 1`, below the stack.
2. Its `⊸` clause hands the function every argument in `vRL_σ (Mut 'y 1)`, read at the kernel's
   relation: among them the inner view `k ↦ M_3` (`innerView`), with no table guard.
3. The answer is a `U` value. Its clause (`RelendableS`) asks its resource, apart from the
   stack's own views, to lie strictly above the outermost lend, so in `Res_2`.
4. Forcing it needs a `mut` cell at `k` at a lifetime `⊒ 3`. The answer's resource is a part,
   in `Res_2`, of a `↭`-update of the inner view, so its flattening has no `mut` cell at `k`
   (`no_flat_mut_of_part`), and neither does the flattening of any `↭`-update of it.

The refutation runs the configuration: the first run from the inner view's typed world
(`tw_innerView`), the second from that run's final world.

## What it measures

At `σ = [x]` the view `k ↦ M_3` arises only from a lend opened inside `x`'s borrower, a
`withbor` whose callback is a value of a type of this shape. D16.1 reads that value at `σ`, with
`'y` a plain variable, and never at `σ·y`: no clause of D16.1 extends the stack. §16.4's proof
sketch applies the induction hypothesis to the callback's premise at `σ·y`; in `CDerives` the
borrow operations are constants, and their callbacks reach them as values.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head ARun)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The inner view in the model -/

/-- The inner view is its own flattening: a `mut` cell with an empty payload. -/
theorem flat_innerView (k : BoCa.Loc) (αy : Life) :
    ResU.Flat (innerView k αy) (innerView k αy) :=
  ⟨innerView k αy, PMap.empty, ExW.single_mut BoLo.exW_empty (ResU.comp_empty_right _),
    AgW.single_mut BoLo.agW_empty, ResU.comp_empty_right _⟩

theorem valid_innerView (k : BoCa.Loc) (αy : Life) : ResU.Valid (innerView k αy) :=
  ⟨_, flat_innerView k αy⟩

/-- **What a resource composed into a run's update of the inner view can flatten to.** Let
`π₁` be a `↭`-update of the inner view `k ↦ M_{αy}`, and `ρ′` a part of `π₁` lying in `Res_a`
for some `a ⊐ αy`. Then `⦇ρ′⦈` holds no `mut` cell at `k`.

Every top-level borrow cell of `π₁` sits in `⦇π₁⦈` at its own location with its own kind, and
`↭` makes `⦇π₁⦈` agree with the inner view on borrow cells, so any borrow cell of `ρ′` would be
the inner view itself, at `αy`, which `Res_a` excludes. A `ρ′` with no borrow cell is in every
stratum, so its flattening is too, and a `mut` cell at `b` is not in `Res_b`. -/
theorem no_flat_mut_of_part {k : BoCa.Loc} {αy a : Life} (hya : αy < a) {ρ' ρp π₁ : WRes}
    (hU : ResU.UpdV (innerView k αy) π₁) (hc : ResU.CompS ρ' ρp π₁) (ha : ρ'.InStratum a)
    {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b} {Q : Val → SPropS Loc Val b}
    {hw : Q v ⟨χ, h⟩} (hf : ρ'.FlatAt k (CellU.mutOf b v χ h Q hw)) : False := by
  by_cases hb : ∃ m ψ, ρ'.get m = some ψ ∧ ψ.kind ≠ Kind.own
  · obtain ⟨m, ψ, hg, hk⟩ := hb
    obtain ⟨σ₁, hσ₁⟩ := hU.2.2
    by_cases hi : ψ.kind = Kind.imm
    · have himm : ∃ ψ₁, π₁.get m = some ψ₁ ∧ ψ₁.kind = Kind.imm := by
        rcases ResU.Comp.get hc m with ⟨e, -, -⟩ | ⟨ψ', e₁, -, e⟩ | ⟨ψ', e₁, -, -⟩ |
            ⟨ψ₁', ψ₂', ψ', e₁, -, e, hC⟩
        · rw [hg] at e; cases e
        · rw [hg] at e₁; cases e₁; exact ⟨ψ, e, hi⟩
        · rw [hg] at e₁; cases e₁
        · obtain ⟨s₁, s₂, w, ρ, h₁, h₂, h₃, -, -, rfl⟩ := hC
          exact ⟨_, e, CellU.kind_immOf _ _ _ _⟩
      obtain ⟨ψ₁, e₁, k₁⟩ := himm
      obtain ⟨ex, ag, hex, hag, hcs⟩ := hσ₁
      obtain ⟨χ', hχ', hkχ, -⟩ := BoLo.agW_get_at hag e₁ k₁
      have hσm : σ₁.get m = some χ' :=
        ResU.CompS.get_right_of_immFree hcs (ExS.immFree hex) hχ'
      rcases CellU.rep χ' with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b', w, ξ, hξ, P, hP, rfl⟩
      · simp at hkχ
      · obtain ⟨τ, hτ, hgg⟩ := (hU.1.1 m s w ξ hξ).mpr ⟨σ₁, ⟨ex, ag, hex, hag, hcs⟩, hσm⟩
        rw [ResU.Flat.functional hτ (flat_innerView k αy)] at hgg
        obtain ⟨-, he⟩ := ResU.single_get_eq_some hgg
        have := congrArg CellU.kind he
        simp at this
      · simp at hkχ
    · rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b', w, ξ, hξ, P, hP, rfl⟩
      · simp at hk
      · simp at hi
      · have e₁ := (ResU.CompS.get_left_of_ne_imm hc hg hi).2
        have hσm := ResU.flat_get_of_ne_imm hσ₁ e₁ hi
        obtain ⟨w₀, ξ₀, hξ₀, hP₀, τ, hτ, hgg⟩ :=
          (hU.1.2 m b' P).mpr ⟨w, ξ, hξ, hP, ⟨σ₁, hσ₁, hσm⟩⟩
        rw [ResU.Flat.functional hτ (flat_innerView k αy)] at hgg
        obtain ⟨-, he⟩ := ResU.single_get_eq_some hgg
        have hb' : αy = b' := (by simpa using congrArg CellU.at he : b' = αy).symm
        have hab : a < b' := ha m _ hg
        exact absurd (hb' ▸ hya) (not_lt.mpr (le_of_lt hab))
  · push Not at hb
    have hall : ∀ α, ρ'.InStratum α := fun α m ψ hg => by
      have hk := hb m ψ hg
      rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b', w, ξ, hξ, P, hP, rfl⟩
      · trivial
      · simp at hk
      · simp at hk
    obtain ⟨σ', hσ', hget⟩ := hf
    exact lt_irrefl b (flat_inStratum hσ' (hall b) k _ hget)

/-- The inner view is a typed world with no record: `ℓ ↦ own(())` allocated, then folded into
`ℓ ↦ M_{αy}` (`TW.alloc`, `TW.mutFold`). -/
theorem tw_innerView (k : BoCa.Loc) (αy : Life) : TW (innerView k αy) [] [] :=
  TW.mutFold (X := ResU.single k (CellU.ownOf Val.unit)) (Z := PMap.empty)
    (TW.alloc (μ := fun _ => none) TW.empty BoLo.lower_empty rfl (ResU.comp_empty_left _)
      (ResU.valid_single_own k Val.unit))
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (valid_innerView k αy)

/-- A run from a value to a value takes no step. -/
theorem aRun_val_val {A : BoCa.BoLo.Alloc} {i j : Nat} {μ μ' : Heap} {u w : Val}
    (h : ARun (ℍ := ℍ) A i μ (.val u) j μ' (.val w)) : w = u := by
  generalize hE : (Expr.val u) = E at h
  cases h with
  | refl => exact (Val.ext hE).symm
  | more s _ => subst hE; exact (BoCa.BoLo.no_step_val s.toStep1).elim

/-! ### The configuration -/

/-- The stack entry: a `mut` lend of the place `0` at the variable `0`, of payload `1`. -/
def e₀ : LEnt := ⟨0, 0, .unit, .mut, fun _ => true⟩

/-- `Mut 'y 1`, `'y` the variable `1`, which `innerCtx 0 1` puts below the stack's `'x`. -/
abbrev belowA : VTy := .mut (.var 1) .unit

/-- `Mut 'y 1 ⊸ F (U (F (Mut 'y 1)))`. -/
abbrev belowC : CTy := .arr belowA (.ret (.thunk (.ret belowA)))

/-- `λn. return (thunk (return n))`. -/
abbrev belowE : Expr := .val (.lam (.val (.lam (.var 1))))

/-- `x ⊏ ⊤`: the stack's variable alone. -/
abbrev Δ₀ : LifeCtx := LifeCtx.empty.extend 0 .top

/-- `Λ. λn. return (thunk (return n))`. -/
abbrev allBelowE : Expr := .val (.lam belowE)

/-- `∀'y ⊏ ⊓Δ. Mut 'y 1 ⊸ F (U (F (Mut 'y 1)))`: the shape of a borrow callback's type, the bound
`withbor`'s type gives (`axWithbor2Ty x Δ.meetOfDom`). -/
abbrev allBelowC : CTy := .all 1 Δ₀.meetOfDom belowC

theorem below_derives : CDerives (innerCtx 0 1) [⟨.unit, false⟩] belowE (.comp belowC) :=
  .lam (.ret (.thunkF (.ret (.var (.there (.here (.cons .nil)))))))

theorem allBelow_derives : CDerives Δ₀ [] allBelowE (.comp allBelowC) :=
  .allI (by decide) (fun y u h => by
      rw [LifeCtx.find?_extend] at h
      by_cases h0 : (0 : LifeVar) = y
      · rw [if_pos h0] at h; cases h; rfl
      · rw [if_neg h0] at h
        exact absurd h (by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind]))
    (fun _ h => absurd h (by simp)) below_derives

/-- `λn. return (thunk (return n))` applied to `ℓ` steps to the closure `λ_. ℓ`. -/
theorem below_beta (A : BoCa.BoLo.Alloc) (μ : Heap) (k : BoCa.Loc) :
    ARun (ℍ := ℍ) A 0 μ (.app belowE (.val (.loc k))) 0 μ
      (.val (.lam (.val (.loc k)))) :=
  ARun.one (Step1N.head (Head.beta μ _ (Val.loc k)) rfl)

/-- `(Λ. λn. return (thunk (return n))) [] ℓ` steps to the closure `λ_. ℓ`. -/
theorem allBelow_beta (A : BoCa.BoLo.Alloc) (μ : Heap) (k : BoCa.Loc) :
    ARun (ℍ := ℍ) A 0 μ (.app (.app allBelowE (.val .unit)) (.val (.loc k))) 0 μ
      (.val (.lam (.val (.loc k)))) :=
  ARun.cons (Step1N.plug (Kont.appL .hole (Val.loc k))
    (Step1N.head (Head.beta μ belowE Val.unit) rfl)) (below_beta A μ k)

/-- Forcing `λ_. ℓ` steps to `ℓ`. -/
theorem force_beta (A : BoCa.BoLo.Alloc) (μ : Heap) (k : BoCa.Loc) :
    ARun (ℍ := ℍ) A 0 μ (forceE (.ret belowA) (.val (.lam (.val (.loc k))))) 0 μ
      (.val (.loc k)) :=
  ARun.one (Step1N.head (Head.beta μ _ Val.unit) rfl)

/-- **GFP does not hold at a one-entry stack.** `σ = [x]`, `Δ = x ⊏ ⊤`, the closed derivation of
`Λ. λn. return (thunk (return n))` at `∀'y ⊏ ⊓Δ. Mut 'y 1 ⊸ F (U (F (Mut 'y 1)))`. Every
hypothesis of `GFPAt [x]` holds: the stack is well formed, `x ↦ 1` models `Δ`, and the empty
resource satisfies the table and the empty context. The `∀` clause is taken at `'y ↦ 3`, the `⊸`
clause at the inner view `k ↦ M_3`; the answer's `U` clause puts its resource in `Res_2`, and
forcing it then needs a `mut` cell at `k` that no run from `Res_2` has. -/
theorem not_gfpAt_below : ¬ GFPAt [e₀] := by
  intro hG
  let αy : Life := OrderDual.toDual 3
  let α : Life := OrderDual.toDual 1
  let a : Life := OrderDual.toDual 2
  let k : BoCa.Loc := 1
  let δ : LSub := LSub.empty.extend 1 αy
  have hα : α ⊏ (Lifetime.SLife.top : Life) := show (0 : ℕ) < 1 from by decide
  have hαy : αy ⊏ α := show (1 : ℕ) < 3 from by decide
  have hya : αy < a := show (2 : ℕ) < 3 from by decide
  have haα : a < α := show (1 : ℕ) < 2 from by decide
  have hWF : LStack.WF [e₀] Δ₀ := by
    refine ⟨fun e he => ?_, by simp [e₀]⟩
    simp only [List.mem_singleton] at he
    subst he
    exact ⟨.top, by
      show Δ₀.find? 0 = some .top
      rw [LifeCtx.find?_extend, if_pos rfl]⟩
  have hmeet : Δ₀.meetOfDom.interp (extS LSub.empty [e₀] [α]) = some α := by
    show some (Lifetime.SLife.meet α Lifetime.SLife.top) = some α
    exact congrArg some (Nat.max_eq_left (Nat.zero_le _))
  have hmod : Δ₀.Models (extS LSub.empty [e₀] [α]) := by
    intro z u hz
    rw [LifeCtx.find?_extend] at hz
    by_cases h0 : (0 : LifeVar) = z
    · subst h0
      rw [if_pos rfl] at hz
      cases hz
      exact ⟨α, Lifetime.SLife.top, find?_extend_self _ _ _, rfl, hα⟩
    · rw [if_neg h0] at hz
      exact absurd hz (by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind])
  have hT : TabAtS [e₀] [α] PMap.empty :=
    ⟨fun _ _ => ResU.inStratum_empty _,
      fun _ _ m ψ _ hg => absurd (hg.symm.trans (PMap.empty_get m)) (by simp)⟩
  have hg : gRLs [e₀] LSub.empty [α] [] [] [] PMap.empty := pure_sep_mk trivial ⟨rfl, trivial⟩
  have h := hG _ _ _ _ allBelow_derives hWF LSub.empty [α] rfl (List.isChain_singleton _) hmod
    [] [] _ hT hg
  rw [show substAll [] allBelowE = allBelowE from Adequacy.psub_nil 0 _] at h
  -- D16.1's `∀` clause, at a lifetime below the stack's lend
  have h0 := h αy PMap.empty PMap.empty ⟨rfl, α, hmeet, hαy⟩ (ResU.comp_empty_left _)
  -- the argument: the inner view, below the stack's lend
  have hslot : vRLs [e₀] δ belowA [α] [] (.loc k) (innerView k αy) := by
    show vC true belowA [] ((δ.extend 0 α)) (.loc k) (innerView k αy)
    refine ⟨αy, ?_, k, pure_sep_mk rfl (innerView_ptoMutS k αy [] _)⟩
    rw [Lifetime.Life.interp_var, find?_extend_ne _ _ (by decide), find?_extend_self]; rfl
  have h1 := h0 (.loc k) (innerView k αy) (innerView k αy) hslot (ResU.comp_empty_left _)
  -- the first run, from the empty frame and the inner view's typed world
  obtain ⟨ρ', ρp, fρ', fρ'p, π₁, w, μ, μ', ps', ls', -, hC1, hH2, -, hC2, -, ⟨k', hrun⟩,
      hC3, hU1, -, hTW, hTag, -, hls, hQ⟩ :=
    h1 PMap.empty (innerView k αy) []
      (ResU.hash_symm (ResU.hash_empty_right (valid_innerView k αy)))
      (ResU.comp_empty_left _) (tw_innerView k αy) (fun x hx => absurd hx (by simp))
      BoCa.BoLo.Alloc.leastFree 0
  obtain rfl : w = Val.lam (.val (.loc k)) := aRun_val_val ((allBelow_beta _ μ k).rest hrun)
  obtain rfl : ls' = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    simpa using (hls x).mp hx
  -- the answer's `U` clause: the views dropped, the rest strictly above the lend
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := hQ
  have hρ'a : ρ'.InStratum a :=
    (outlives_comp hc a).mpr ⟨(hz α rfl).mono (le_of_lt haα),
      vwS_inStratum hn a fun α' h' => by
        simp only [List.mem_singleton] at h'; subst h'; exact haα⟩
  have h2 := hth [] (Ext.refl [] ρz) [α] (reLend_refl (List.isChain_singleton α)) ρn ρ' hn hc
  -- the second run: the force, from the first run's final world
  obtain rfl : fρ' = ρ' := ResU.CompS.functional hC1 (ResU.comp_empty_left ρ')
  have h2' := h2 ρp fρ'p ps' hH2 hC2.comm hTW hTag BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨ρ'', ρp₂, -, -, π₂, w₂, μ₂, μ₂', ps₂, ls₂, -, -, -, -, -, -, ⟨k₂, hrun₂⟩, hC4, hU2,
      -, -, -, -, -, hQ2⟩ := h2'
  have hw₂ : w₂ = Val.loc k := aRun_val_val ((force_beta _ μ₂ k).rest hrun₂)
  rw [hw₂] at hQ2
  -- the answer needs a `mut` cell at `k`
  obtain ⟨α₀, -, ℓ, hp⟩ := hQ2
  obtain ⟨hv, b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := pure_sep_iff.mp hp
  have hℓ : ℓ = k := by
    have h' := congrArg Subtype.val hv
    simp only [Val.loc, Expr.loc.injEq] at h'
    exact h'.symm
  subst hℓ
  have hk : (CellU.mutOf b u σ hσ Q hw).kind ≠ Kind.imm := by simp
  have hπ := (ResU.CompS.get_left_of_ne_imm hC4 (ResU.single_get_self _ _) hk).2
  obtain ⟨σ₂, hσ₂⟩ := hU2.2.2
  obtain ⟨v', χ', h', hw', hflat⟩ :=
    (hU2.1.2 _ b Q).mpr ⟨u, σ, hσ, hw, ⟨σ₂, hσ₂, ResU.flat_get_of_ne_imm hσ₂ hπ hk⟩⟩
  exact no_flat_mut_of_part hya hU1 hC3 hρ'a hflat

/-- **GFP (D16.2), as stated at D16.1, does not hold**: it fails at `[x]`. -/
theorem not_gfp : ¬ GFP := fun h => not_gfpAt_below (h [e₀])

end GhostEnd
