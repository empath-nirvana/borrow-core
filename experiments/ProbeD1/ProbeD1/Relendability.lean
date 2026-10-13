import ProbeD1.Thunk

/-!
# ProbeD1 — the two needs of the `U` introductions, settled at `binder0`

The `U` introductions at `binder0` (`thunkFRow_binder0_at` and its three siblings, `Thunk.lean`)
take two things beyond the premise: the thaw of the row's context (`CtxRelendableAt`) and `Δ`'s
models at every re-lend of the stack (`SemSR`). This file asks of each whether the configuration
that breaks it is reached.

## The context's thaw

* **The global hypothesis is false** (`not_ctxRelendable_binder0`). The configuration `k`: one
  `mut` entry lending the place `0` at `'0`, its payload type `Unk`; the context `r : Mut '0 1`
  holding the cell `0 ↦ mut(α, (), ∅, 𝒱⟦1⟧)` at the entry's own lifetime `α`. The table admits the
  cell (it is at a stack place, in stratum `↓α`), the context is related at it, and no split of
  `RelendableS` places it: it is not the entry's view (`𝒱⟦Unk⟧ ≠ 𝒱⟦1⟧`, `k_not_relendableS`), and
  it is not strictly above the outermost lend.
* **Restricting to the row's context and `SemS`'s index does not exclude it**
  (`not_ctxRelendableAt_k`): `k` meets every hypothesis `SemS` puts on the index at
  `Δ = '0 ⊏ ⊤` (`k_index`: the stack in shape and admitted by every judgement over `kΓ`, the
  substitution's domain, the models, the table).
* **The world arises in `TW`** (`k_world_TW`): `alloc`, then `mutFold`, tagged at the empty list.
  **The stack and the context are reached by `binder0`'s own clauses** (`k_reached`): the closed
  term `Λ'0. λr. thunk (return r)` is derived at `∀'0 ⊏ ⊤. Mut '0 1 ⊸ F (U (F (Mut '0 1)))`; the
  `∀` clause at `binder0` owes the body at every own lend `OwnPush` admits, and `k`'s entry is one
  (`OwnOK` does not tie the entry's payload type or place to the argument); at the pushed stack the
  `⊸` clause owes it at every related argument under the table, and `r = 0` at `k`'s cell is one.
  At `k`'s resource the `U` clause fails for every closure (`k_thunk_not_vRL`). Whether the closed
  term's own clause fails, through `wpTS`'s update of the answer's resource, is not derived, and
  `ThunkFRow binder0` is not refuted.
* **What excludes `k` from a run is the lend's step, not `TW`.** `TW` does not see the stack.
  `PlaceViews` (every `mut` cell at a stack place is the innermost lending entry's view) fails at
  `k` (`not_placeViews_k`); a 6.65 lend opens with it at its own place (`lendMut_placeView`), and
  `↭` keeps a `mut` cell's lifetime and predicate (`ResU.UpdMut`). That it holds at every
  `Arises` configuration is not proved. `TabAtS` does not carry it, which is why `SemS`'s index
  admits `k`, and `OwnPush` does not carry it, which is why `binder0`'s `∀` clause reaches `k`.

So `CtxRelendableAt` is a real condition on the context. It is proved at `Γ = []` and at a `U`
slot (`ctxRelendableAt_nil`, `ctxRelendableAt_thunk`), so the four rows are not vacuous there
(`thunkFRow_binder0_nil`, `thunkFRow_binder0_thunk`). It is not proved at the contexts
`PlaceViews` restricts to.

## `Δ`'s models at a re-lend

* **What the rows need** is `ReLendModels`: every re-lend of the stack models `Δ`. It is `SemSR`'s
  added hypothesis, and `SemS` does not give it (`models_reLend_fails`).
* **A sufficient condition** is `BoundsStackFree`: no bound of `Δ` mentions a stack variable
  (`reLendModels_of_boundsStackFree`). Re-lending lowers only the stack's lifetimes, so it keeps
  every bound that does not read them.
* **Typing reaches the failing configuration** (`q2_reached`): `Λ'0. Λ'1 ⊏ '0. thunk (return ())`
  is derived closed, its `U` introduction at `Δ = '0 ⊏ ⊤, '1 ⊏ '0`; at `binder0` the outer `∀`
  pushes the own lend of `'0` (`OwnPush`) and the inner `∀` instantiates `'1` below it (`LtLife`
  at the pushed stack). At that index `Δ` holds, `BoundsStackFree` fails, and the re-lend of `'0`
  to `'1`'s lifetime, which the `U` clause quantifies over, breaks `'1 ⊏ '0`, so `ReLendModels`
  fails there. The premise's `SemS` is not available at that re-lend. Whether the `U` clause
  fails there for some body is not derived.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS RelendableS unitQ
  unitQ_holds innerView innerView_ptoMutS)

/-! ### The configuration `k` -/

/-- `k`'s lifetime. -/
abbrev kα : Life := OrderDual.toDual 1

/-- `k`'s entry: the place `0` lent at `'0`, the payload type `Unk`. -/
abbrev kEnt : LEnt := ⟨0, 0, .unk, .mut, fun _ => true⟩

abbrev kσ : LStack := [kEnt]

/-- The callback's context after `λr`: `r : Mut '0 1`, the `∀`'s slot dead. -/
abbrev kΓ : Ctx VTy := [⟨.mut (.var 0) .unit, true⟩, ⟨.unit, false⟩]

abbrev kγ : List Val := [.loc 0, .unit]

abbrev kΔ : LifeCtx := LifeCtx.empty.extend 0 .top

abbrev kδ : LSub := ⟨[]⟩

/-- `0 ↦ mut(α, (), ∅, 𝒱⟦1⟧)`. -/
abbrev kCell : CellU BoCa.Loc Val :=
  CellU.mutOf kα Val.unit PMap.empty (ResU.inStratum_empty kα) (unitQ kα) (unitQ_holds kα)

abbrev kρ : WRes := innerView 0 kα

/-- A `mut` cell's stored predicate, read on the union. -/
def mutPred : CellU BoCa.Loc Val → Val → SPropU BoCa.Loc Val
  | .mut m => fun v ρ => ∃ h : ρ.InStratum m.β, m.P v (ResS.toRes ⟨ρ, h⟩)
  | _ => fun _ _ => False

theorem mutPred_mutOf {b : Life} {u : Val} {χ : WRes} {h : χ.InStratum b}
    {Q : Val → SPropS BoCa.Loc Val b} {hw : Q u ⟨χ, h⟩} :
    mutPred (CellU.mutOf b u χ h Q hw) = ofS Q := by
  funext v ρ
  simp only [mutPred, CellU.mutOf, ofS, SPropS.toU, ResS.toS_toRes]

theorem kρ_get : kρ.get 0 = some kCell := ResU.single_get_self _ _

theorem loc_ne_unit : (Val.loc 0 : Val) ≠ Val.unit := by
  intro h
  have := congrArg Subtype.val h
  simp [Val.loc, Val.unit] at this

/-- **`k`'s cell is in no split `RelendableS` admits**, whatever the predicate re-lent: the views
of `kσ` at `kα` are `𝒱⟦Unk⟧`'s cell or nothing, and the part above the outermost lend is strictly
above `kα`. -/
theorem k_not_relendableS (δ : LSub) (ls : List SRec) (P : List Life → List SRec → WProp) :
    ¬ RelendableS δ [] kσ P [kα] ls kρ := by
  rintro ⟨ds, ρz, ρn, hc, hn, hz, -⟩
  match ds, hn with
  | [], hn => exact hn.elim
  | _ :: _ :: _, hn =>
      obtain ⟨_, _, _, _, h⟩ := hn
      exact h.elim
  | [false], hn =>
      obtain ⟨ρ₁, ρ₂, hc', ⟨rfl, -⟩, ⟨rfl, -⟩⟩ := hn
      obtain rfl := eq_empty_of_compS_empty hc'
      obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right ρz)
      exact lt_irrefl kα (hz kα rfl 0 kCell kρ_get)
  | [true], hn =>
      obtain ⟨ρ₁, ρ₂, hc', hv, ⟨rfl, -⟩⟩ := hn
      obtain ⟨b, u, χ, hχ, Q, hw, ls₀, -, rfl, hQ, -, -⟩ := hv
      obtain rfl := ResU.CompS.functional hc' (ResU.comp_empty_right _)
      have hk : (CellU.mutOf b u χ hχ Q hw).kind ≠ Kind.imm := by simp
      have hg := (ResU.CompS.get_right_of_ne_imm hc (ResU.single_get_self _ _) hk).2
      rw [kρ_get] at hg
      have hP := congrArg mutPred (Option.some.inj hg)
      rw [mutPred_mutOf, mutPred_mutOf, hQ] at hP
      have h₁ : ofS (unitQ kα) (Val.loc 0) PMap.empty := by
        rw [hP]; exact ⟨rfl, trivial⟩
      obtain ⟨-, -, h₂⟩ := h₁
      exact loc_ne_unit h₂

/-- The leaf `r : Mut '0 1` at `k`'s cell. -/
theorem k_slot (p : Placement) (δ : LSub) (ls : List SRec) :
    vRL p kσ δ (.mut (.var 0) .unit) [kα] ls (.loc 0) kρ :=
  ⟨kα, rfl, 0, pure_sep_mk rfl (innerView_ptoMutS 0 kα ls _)⟩

theorem k_gRL (p : Placement) (δ : LSub) (ls : List SRec) : gRL p kσ δ [kα] ls kΓ kγ kρ :=
  pure_sep_mk trivial ⟨kρ, PMap.empty, ResU.comp_empty_right _, k_slot p δ ls, rfl, trivial⟩

theorem k_tab : TabAtS kσ [kα] kρ := by
  refine ⟨fun a ha => ?_, fun a _ k ψ hk e => ?_⟩
  · obtain rfl : a = kα := (Option.some.inj ha).symm
    intro l ψ e
    obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
    exact GhostEnd.down_lt kα
  · exact absurd (ResU.single_get_eq_some e).1 (fun h => hk (by simp [h]))

theorem k_stackOK : StackOK kσ [kα] := ⟨rfl, List.isChain_singleton _, List.nodup_singleton _⟩

theorem kΔ_models (δ : LSub) : kΔ.Models (extS δ kσ [kα]) := by
  intro x u hx
  rw [LifeCtx.find?_extend] at hx
  by_cases h0 : (0 : LifeVar) = x
  · subst h0
    rw [if_pos rfl] at hx
    cases hx
    exact ⟨1, 0, rfl, rfl, by simp [Lifetime.SLife.Lt]⟩
  · rw [if_neg h0] at hx
    exact absurd hx (by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind])

/-- **`k` meets every hypothesis `SemS` puts on the index** at `Δ = '0 ⊏ ⊤`, at every judgement
over `kΓ`: the stack in shape and admitted, the substitution's domain, the models, the table, and
the context related. -/
theorem k_index (p : Placement) (ls : List SRec) :
    StackOK kσ [kα] ∧ (∀ C, StackJ kσ [kα] kδ kΔ kΓ C) ∧ SubDom kδ kΔ ∧
      kΔ.Models (extS kδ kσ [kα]) ∧ TabAtS kσ [kα] kρ ∧ gRL p kσ kδ [kα] ls kΓ kγ kρ := by
  refine ⟨k_stackOK, fun C => ⟨List.nodup_singleton _, ?_, ?_⟩, fun y hy => absurd rfl hy,
    kΔ_models kδ, k_tab, k_gRL p kδ ls⟩
  · intro e he y hy
    rw [List.mem_singleton.mp he] at hy
    exact absurd hy (by simp [VFree])
  · intro e he
    rw [List.mem_singleton.mp he]
    exact Or.inl ⟨.top, rfl⟩

/-- **The thaw of the row's context is a real condition**: it fails at `kΓ`, at `'0 ⊏ ⊤`. -/
theorem not_ctxRelendableAt_k (p : Placement) : ¬ CtxRelendableAt (ℍ := ℍ) p kΔ kΓ := by
  intro h
  obtain ⟨hok, -, hSD, hM, ht, hg⟩ := k_index (ℍ := ℍ) p []
  exact k_not_relendableS kδ [] _ (h kδ kσ [kα] [] kγ kρ hok hSD hM ht hg)

/-- **`CtxRelendable binder0` is false.** The four rows taking it (before `CtxRelendableAt`) were
vacuous. -/
theorem not_ctxRelendable_binder0 : ¬ CtxRelendable (ℍ := ℍ) .binder0 :=
  fun h => not_ctxRelendableAt_k .binder0 (ctxRelendableAt_of h kΔ kΓ)

/-- At `k` the `U` clause fails for every closure, at `binder0` (its `U` clause is
`RelendableS`). -/
theorem k_thunk_not_vRL (δ : LSub) (C : CTy) (ls : List SRec) (f : Val) :
    ¬ vRL (ℍ := ℍ) .binder0 kσ δ (.thunk C) [kα] ls f kρ := by
  intro h
  rw [vRL_thunk_eq, if_neg (by decide)] at h
  exact k_not_relendableS δ ls _ (h k_tab)

/-! ### `k` arises: its world in `TW`, its stack and value by `binder0`'s own clauses -/

/-- **`k`'s world is a `TW` world**: `alloc` the place, then `mutFold` it at `kα` with the
predicate `𝒱⟦1⟧`. -/
theorem k_world_TW : TW kρ [] [] := by
  have h₁ : TW (ResU.single 0 (CellU.ownOf Val.unit)) [] [] :=
    TW.alloc TW.empty lower_empty rfl (ResU.comp_empty_left _) (ResU.valid_single_own _ _)
  exact TW.mutFold (ρ := PMap.empty) (Z := PMap.empty) (hw := unitQ_holds kα) h₁
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) (ResU.comp_empty_right _)
    (ResU.valid_single_mut_of_wit (ResU.comp_empty_left _) (ResU.valid_single_own _ _))

theorem k_world_tagged : Tagged kρ [] [] := fun _ hx => absurd hx List.not_mem_nil

/-- The callback's type: `∀'0 ⊏ ⊤. Mut '0 1 ⊸ F (U (F (Mut '0 1)))`. -/
abbrev kC : CTy := .all 0 .top (.arr (.mut (.var 0) .unit) (.ret (.thunk (.ret (.mut (.var 0) .unit)))))

/-- **`k` is reached by `binder0`'s own clauses from a closed derived term.** The term
`Λ'0. λr. thunk (return r)` is derived closed at `kC`. Read at `[]`, the `∀` clause at `binder0`
(`allOwn`) owes the body at every own lend `OwnPush` admits: `k`'s entry is one. At the pushed
stack the `⊸` clause owes it at every argument related there under the table: `r = 0` at `k`'s
cell is one, and the table holds. The world is `TW`'s, tagged. -/
theorem k_reached (ls : List SRec) :
    CDerives LifeCtx.empty [] (.val (.lam (.val (.lam (.val (.lam (.var 1))))))) (.comp kC) ∧
      OwnPush kδ kC PMap.empty ([], []) kEnt kα ∧
      vRL (ℍ := ℍ) .binder0 kσ (kδ.extend 0 kα) (.mut (.var 0) .unit) [kα] ls (.loc 0) kρ ∧
      TabAtS kσ [kα] kρ ∧ TW kρ [] [] ∧ Tagged kρ [] [] := by
  refine ⟨?_, ⟨0, .top, _, rfl, rfl, by simp [CTy.binders, VTy.binders], ?_, ?_⟩,
    k_slot _ _ ls, k_tab, k_world_TW, k_world_tagged⟩
  · refine .allI (S := .unit) rfl (fun y u h => by simp [LifeCtx.empty, LifeCtx.find?,
      Lifetime.assocFind] at h) (fun s hs => absurd hs List.not_mem_nil) (.lam (.ret (.thunkF
      (.ret (.var (.there (.here (.cons .nil))))))))
  · exact ⟨List.isChain_singleton _, ResU.inStratum_empty _, List.not_mem_nil,
      List.not_mem_nil, fun y hy => absurd hy (by simp [VFree])⟩
  · exact ⟨Lifetime.SLife.top, rfl,
      show OrderDual.toDual (1 : ℕ) < OrderDual.toDual 0 from by decide⟩

/-! ### What excludes `k` from a run: the lend's view at its place -/

/-- A `mut` cell is an entry's view: its stored predicate is `𝒱⟦T⟧` at some list and substitution,
`T` the entry's payload type. -/
def PlaceView (e : LEnt) (ψ : CellU BoCa.Loc Val) : Prop :=
  ∃ (δ' : LSub) (ls₀ : List SRec), mutPred ψ = fun v => vC true e.T ls₀ δ' v

/-- **Every `mut` cell at a stack place is the view of the innermost entry lending that place.**
`TabAtS` asks only the stratum of a cell at a stack place; this asks what it stores. A 6.65 lend
opens with it at its own place (`lendMut_placeView`), and `↭` keeps a `mut` cell's lifetime and
predicate (`ResU.UpdMut`). That it holds at every `Arises` configuration is not proved. -/
def PlaceViews (σ : LStack) (ρ : WRes) : Prop :=
  ∀ (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get l = some ψ → ψ.kind = Kind.mut →
    ∀ e, σ.find? (fun e => decide (e.l = l)) = some e → e.k = .mut → PlaceView e ψ

theorem placeView_of_viewP {e : LEnt} {δ : LSub} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : GhostEnd.viewP e.l e.T δ α ls ρ) : ∃ ψ, ρ = ResU.single e.l ψ ∧ PlaceView e ψ := by
  obtain ⟨b, u, χ, hχ, Q, hw, ls₀, -, rfl, hQ, -, -⟩ := h
  exact ⟨_, rfl, δ, ls₀, by rw [mutPred_mutOf, hQ]⟩

/-- **A 6.65 lend opens with its view at its place**: the cell `LendMut` puts at the entry's place
in the callback's resource is the entry's view. -/
theorem lendMut_placeView {c c' : Cfg} {e : LEnt} (h : LendMut c c' e) :
    ∃ ψ, c'.ρ.get e.l = some ψ ∧ PlaceView e ψ := by
  obtain ⟨hk, -, -, -, -, -, -, α, v, ρp, X, ρc, Z, hstr, P, hw, -, -, -, -, -, -, -, -, hc, -,
    -, -, δ, hv⟩ := h
  obtain ⟨l, x, T, kd, cr⟩ := e
  cases hk
  obtain ⟨ψ, he, hψ⟩ := placeView_of_viewP hv
  have hg := ResU.CompS.get_left_of_ne_imm hc (ResU.single_get_self _ _) (by simp)
  refine ⟨_, hg.2, ?_⟩
  have : ResU.single l (CellU.mutOf α v ρp hstr P hw) = ResU.single l ψ := he
  have e₁ := ResU.single_get_self l (CellU.mutOf α v ρp hstr P hw)
  rw [this, ResU.single_get_self] at e₁
  rw [Option.some.inj e₁] at hψ
  exact hψ

/-- **`k` breaks `PlaceViews`**: its cell at the entry's place stores `𝒱⟦1⟧`, the entry's payload
type is `Unk`. -/
theorem not_placeViews_k : ¬ PlaceViews kσ kρ := by
  intro h
  obtain ⟨δ', ls₀, hP⟩ := h 0 kCell kρ_get (by simp) kEnt rfl rfl
  rw [mutPred_mutOf] at hP
  have h₁ : ofS (unitQ kα) (Val.loc 0) PMap.empty := by
    rw [hP]; exact ⟨rfl, trivial⟩
  obtain ⟨-, -, h₂⟩ := h₁
  exact loc_ne_unit h₂

/-! ### The thaw where it holds: `Γ = []` and a `U` slot -/

/-- The views of a stack with every flag off hold at `∅`. -/
theorem vwS_off (δ : LSub) (ls : List SRec) : ∀ (seen : List BoCa.Loc) (σ : LStack)
    (αs : List Life), αs.length = σ.length →
    vwS δ seen σ (σ.map fun _ => false) αs ls PMap.empty
  | _, [], [], _ => ⟨rfl, trivial⟩
  | seen, e :: σ, _ :: αs, h =>
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_left _, ⟨rfl, trivial⟩,
        vwS_off δ ls (e.l :: seen) σ αs (by simpa using h)⟩
  | _, [], _ :: _, h => absurd h (by simp)
  | _, _ :: _, [], h => absurd h (by simp)

/-- …and only there. -/
theorem vwS_off_eq (δ : LSub) (ls : List SRec) : ∀ (seen : List BoCa.Loc) (σ : LStack)
    (αs : List Life) (ρ : WRes), vwS δ seen σ (σ.map fun _ => false) αs ls ρ → ρ = PMap.empty
  | _, [], [], _, h => h.1
  | seen, e :: σ, _ :: αs, ρ, h => by
      obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, h₂⟩ := h
      rw [vwS_off_eq δ ls (e.l :: seen) σ αs ρ₂ h₂] at hc
      exact eq_empty_of_compS_empty hc
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

/-- **The thaw holds at the empty context**, every placement: nothing held, every flag off. -/
theorem ctxRelendableAt_nil (p : Placement) (Δ : LifeCtx) : CtxRelendableAt (ℍ := ℍ) p Δ [] := by
  intro δ σ αs ls γ ρ hok _ _ _ hg
  obtain ⟨hlw, hρ, -⟩ := pure_sep_iff.mp hg
  subst hρ
  refine ⟨σ.map fun _ => false, PMap.empty, PMap.empty, ResU.comp_empty_left _,
    vwS_off δ ls [] σ αs hok.1, fun a _ => ResU.inStratum_empty a,
    fun ls' _ αs' _ ρv τ hv hc => ?_⟩
  rw [vwS_off_eq δ ls' [] σ αs' ρv hv] at hc
  rw [eq_empty_of_compS_empty hc]
  exact pure_sep_mk hlw ⟨rfl, trivial⟩

/-- **The thaw holds at a `U` slot**, at `binder0`: the slot's own `U` clause is the split, and
re-lent it is the slot's `U` clause at the re-lend (`thawRelend`'s argument). -/
theorem ctxRelendableAt_thunk (Δ : LifeCtx) (C : CTy) :
    CtxRelendableAt (ℍ := ℍ) .binder0 Δ [⟨.thunk C, true⟩] := by
  intro δ σ αs ls γ ρ _ _ _ ht hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  match γ, hlw, hgs with
  | [], hlw, _ => exact absurd rfl hlw.1
  | f :: γ', hlw, hgs =>
      obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hgs
      have hρ₂ : ρ₂ = PMap.empty := hrest.1
      subst hρ₂
      obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)
      rw [vRL_thunk_eq, if_neg (by decide)] at hv
      obtain ⟨ds, ρz, ρn, hc₁, hn, hz, H⟩ := hv ht
      refine ⟨ds, ρz, ρn, hc₁, hn, hz, fun ls' he αs' hr ρv τ hv' hcv => ?_⟩
      refine pure_sep_mk hlw ⟨τ, PMap.empty, ResU.comp_empty_right _, ?_, rfl, trivial⟩
      rw [vRL_thunk_eq]
      intro _
      rw [if_neg (by decide)]
      exact ⟨ds, ρz, ρv, hcv, hv', GhostEnd.stratS_mono hr hz,
        fun ls'' he' αs'' hr' => H ls'' (he.trans he') αs'' (GhostEnd.reLend_trans hr' hr)⟩

/-- **`ThunkFRow` at `binder0` holds outright at the empty context**, at the configurations whose
re-lends keep `Δ`'s models: the per-row hypothesis is met there. -/
theorem thunkFRow_binder0_nil (Δ : LifeCtx) (M : Expr) (A : VTy)
    (hM : SemS (ℍ := ℍ) .binder0 Δ [⟨.unit, false⟩] M (.comp (.ret A))) :
    SemSR (ℍ := ℍ) .binder0 Δ [] (.val (.lam M)) (.val (.thunk (.ret A))) :=
  thunkFRow_binder0_at Δ [] M A (ctxRelendableAt_nil .binder0 Δ) hM

/-- **`ThunkFRow` at `binder0` holds outright at a `U` slot**, at the configurations whose re-lends
keep `Δ`'s models. -/
theorem thunkFRow_binder0_thunk (Δ : LifeCtx) (C : CTy) (M : Expr) (A : VTy)
    (hM : SemS (ℍ := ℍ) .binder0 Δ [⟨.unit, false⟩, ⟨.thunk C, true⟩] M (.comp (.ret A))) :
    SemSR (ℍ := ℍ) .binder0 Δ [⟨.thunk C, true⟩] (.val (.lam M)) (.val (.thunk (.ret A))) :=
  thunkFRow_binder0_at Δ _ M A (ctxRelendableAt_thunk Δ C) hM

/-! ### `Δ`'s models at a re-lend -/

/-- **What the `U` rows need of the models**: every re-lend of the stack models `Δ` (`SemSR`'s
added hypothesis). -/
def ReLendModels (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) : Prop :=
  ∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')

/-- **No bound of `Δ` reads the stack**: a sufficient condition for `ReLendModels`. -/
def BoundsStackFree (Δ : LifeCtx) (σ : LStack) : Prop :=
  ∀ y u, Δ.find? y = some u → ∀ e ∈ σ, u.mentions e.x = false

/-- A re-lend lowers each of the stack's lifetimes, and so each variable's reading. -/
theorem extS_find_reLend (δ : LSub) : ∀ (σ : LStack) {αs αs' : List Life},
    List.Forall₂ (· ≤ ·) αs' αs → ∀ (y : LifeVar) (m : ℕ), (extS δ σ αs).find? y = some m →
      ∃ m', (extS δ σ αs').find? y = some m' ∧ m ≤ m'
  | [], _, _, _, y, m, h => ⟨m, h, le_rfl⟩
  | _ :: _, _, _, .nil, y, m, h => ⟨m, h, le_rfl⟩
  | e :: σ, a :: αs, a' :: αs', .cons hle hr, y, m, h => by
      simp only [extS] at h ⊢
      by_cases hy : e.x = y
      · subst hy
        rw [find?_extend_self] at h ⊢
        cases h
        exact ⟨a', rfl, hle⟩
      · rw [find?_extend_ne _ _ hy] at h ⊢
        exact extS_find_reLend δ σ hr y m h

/-- **`BoundsStackFree` gives `ReLendModels`**: a re-lend lowers only the stack's lifetimes, which
no bound reads, and lowering the bounded side keeps `⊏`. -/
theorem reLendModels_of_boundsStackFree {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life}
    (hb : BoundsStackFree Δ σ) (hM : Δ.Models (extS δ σ αs)) : ReLendModels Δ δ σ αs := by
  intro αs' hr x u hx
  obtain ⟨m, n, hm, hn, hlt⟩ := hM x u hx
  obtain ⟨m', hm', hle⟩ := extS_find_reLend δ σ hr.1 x m hm
  refine ⟨m', n, hm', ?_, lt_of_lt_of_le hlt hle⟩
  rw [← hn]
  refine interp_congr u fun z hz => ?_
  have hz' : z ∉ σ.map LEnt.x := by
    intro hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    rw [hb x u hx e he] at hz
    exact absurd hz (by simp)
  rw [extS_find_not_mem δ σ αs' z hz', extS_find_not_mem δ σ αs z hz']

/-- `'0 ↦ 1`, `'1 ↦ 2` beside the stack: the substitution after the outer own lend and the inner
instance. -/
abbrev qδ : LSub := (kδ.extend 0 kα).extend 1 (OrderDual.toDual 2)

/-- The stack the outer own lend pushes: `'0` lending the place `0`, payload `1`. -/
abbrev qEnt : LEnt := ⟨0, 0, .unit, .mut, fun _ => true⟩

/-- The type of `Λ'0. Λ'1 ⊏ '0. thunk (return ())`. -/
abbrev qC : CTy := .all 0 .top (.all 1 (.var 0) (.ret (.thunk (.ret .unit))))

/-- **Typing reaches a variable off the stack bounded by a stack variable, at a `U` introduction,
at an index `binder0`'s own clauses read.** `Λ'0. Λ'1 ⊏ '0. thunk (return ())` is derived closed;
its `U` introduction is derived at `mΔ = '0 ⊏ ⊤, '1 ⊏ '0`. The outer `∀` at `binder0` pushes the
own lend of `'0` (`OwnPush`); the inner `∀` instantiates `'1` at `2 ⊏ 1` (`LtLife` at the pushed
stack). There `mΔ` holds, `BoundsStackFree` fails, and the re-lend of `'0` at `2`, which the `U`
clause quantifies over, breaks `'1 ⊏ '0`. -/
theorem q2_reached :
    CDerives LifeCtx.empty [] (.val (.lam (.val (.lam (.val (.lam (.val .unit))))))) (.comp qC) ∧
      CDerives mΔ [⟨.unit, false⟩, ⟨.unit, false⟩] (.val (.lam (.val .unit)))
        (.val (.thunk (.ret .unit))) ∧
      OwnPush kδ qC PMap.empty ([], []) qEnt kα ∧
      LtLife (extS (kδ.extend 0 kα) [qEnt] [kα]) (.var 0) (OrderDual.toDual 2) ∧
      mΔ.Models (extS qδ [qEnt] [kα]) ∧ ¬ BoundsStackFree mΔ [qEnt] ∧
      ReLend [OrderDual.toDual 2] [kα] ∧ ¬ mΔ.Models (extS qδ [qEnt] [OrderDual.toDual 2]) ∧
      ¬ ReLendModels mΔ qδ [qEnt] [kα] := by
  have hinner : CDerives mΔ [⟨.unit, false⟩, ⟨.unit, false⟩] (.val (.lam (.val .unit)))
      (.val (.thunk (.ret .unit))) := .thunkF (.ret (.unitI (.cons (.cons (.cons .nil)))))
  have hrl : ReLend [OrderDual.toDual 2] [kα] :=
    ⟨List.Forall₂.cons (show OrderDual.toDual (2 : ℕ) ≤ OrderDual.toDual 1 from by decide)
      List.Forall₂.nil, List.isChain_singleton _⟩
  have hbad : ¬ mΔ.Models (extS qδ [qEnt] [OrderDual.toDual 2]) := by
    intro h
    obtain ⟨m, n, hm, hn, hlt⟩ := h 1 (.var 0) rfl
    have hm' : m = 2 := by
      have : (extS qδ [qEnt] [OrderDual.toDual 2]).find? 1 = some 2 := rfl
      rw [this] at hm; exact (Option.some.inj hm).symm
    have hn' : n = 2 := by
      have : (Lifetime.Life.var 0).interp (extS qδ [qEnt] [OrderDual.toDual 2]) = some 2 := rfl
      rw [this] at hn; exact (Option.some.inj hn).symm
    subst hm' hn'
    exact absurd hlt (by simp [Lifetime.SLife.Lt])
  refine ⟨.allI (S := .unit) rfl (fun y u h => by simp [LifeCtx.empty, LifeCtx.find?,
      Lifetime.assocFind] at h) (fun s hs => absurd hs List.not_mem_nil)
      (.allI (S := .unit) rfl ?_ ?_ (.ret hinner)),
    hinner, ⟨0, .top, _, rfl, rfl, by simp [CTy.binders, VTy.binders], ?_, ?_⟩,
    ⟨1, rfl, show OrderDual.toDual (2 : ℕ) < OrderDual.toDual 1 from by decide⟩, ?_, fun hb => absurd (hb 1 (.var 0) rfl qEnt List.mem_cons_self) (by simp
      [Lifetime.Life.mentions]), hrl, hbad, fun h => hbad (h _ hrl)⟩
  · intro y u h
    rw [LifeCtx.find?_extend] at h
    by_cases h0 : (0 : LifeVar) = y
    · subst h0; rw [if_pos rfl] at h; cases h; rfl
    · rw [if_neg h0] at h
      exact absurd h (by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind])
  · intro s hs hl
    rcases List.mem_singleton.mp hs with rfl
    exact absurd hl (by simp)
  · exact ⟨List.isChain_singleton _, ResU.inStratum_empty _, List.not_mem_nil,
      List.not_mem_nil, fun y hy => absurd hy (by simp [VFree])⟩
  · exact ⟨Lifetime.SLife.top, rfl,
      show OrderDual.toDual (1 : ℕ) < OrderDual.toDual 0 from by decide⟩
  · intro x u hx
    rw [mΔ_find] at hx
    by_cases h1 : x = 1
    · subst h1
      simp only [if_true, Option.some.injEq] at hx
      subst hx
      exact ⟨2, 1, rfl, rfl, by simp [Lifetime.SLife.Lt]⟩
    · by_cases h0 : x = 0
      · subst h0
        have hu : u = .top := by simpa using hx.symm
        subst hu
        exact ⟨1, 0, rfl, rfl, by simp [Lifetime.SLife.Lt]⟩
      · simp [h1, h0] at hx

end ProbeD1

end
