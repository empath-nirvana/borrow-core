import ProbeD1.Rows0
import ProbeD1.Statement1

/-!
# ProbeD1 — the `U` introductions at W: what they owe

`ThunkFRow`, `ThunkVRow`, `BangThunkFRow` and `BangThunkVRow` (statement 0) introduce a `U` value
at W. Their conclusion is the `U` clause of a closure over the context, so it owes the body at
every re-lend of the stack (and, at `cbpv` and `binder`, at every future of the re-lend; at `cbpv`
at the own push there). GhostEnd proves the clause's half of each row at its own relation
(`thunkF_RLa`, `thunkE_RLa`), taking two things as hypotheses: the context re-lendable (`hG`) and
the body at every re-lend (`hM`). At W each is a fact about the judgement.

* **The context's re-lendability** (`CtxRelendable` at every context; `CtxRelendableAt` at one
  row's context and `SemS`'s index): a context related at the stack, at a resource with the table,
  splits into the views it holds and a part above the outermost lend that, handed the views at any
  re-lend, is the context there. A `U` slot meets it (`thawRelend`; `ctxRelendableAt_thunk`,
  `Relendability.lean`). `CtxRelendable binder0` is false, and `CtxRelendableAt` fails at some
  contexts (`not_ctxRelendable_binder0`, `not_ctxRelendableAt_k`): a leaf holding a cell at a stack
  place that is not that entry's view.
* **The body at a re-lend** comes from the premise's `SemS` at the re-lent stack, which asks
  `Δ.Models` there. A re-lend need not keep it at a configuration `SemS` admits
  (`models_reLend_fails`): a variable of `Δ` off the stack, bounded by a stack variable, keeps
  `δ`'s lifetime while the stack's is re-lent below it. Typing reaches such a `Δ` at a `U`
  introduction, at an index `binder0`'s own clauses read (`q2_reached`, `Relendability.lean`).
* **The table at a re-lend** (`tabRelend`, statement 1's `TabRelend`): the share lies above every
  lend, the views above the re-lent innermost lend's predecessor and at the stack's places.
* **At `binder0` these are all** (`thunkFRow_binder0_at`, `thunkVRow_binder0_at`,
  `bangThunkFRow_binder0_at`, `bangThunkVRow_binder0_at`): given `CtxRelendableAt binder0` at the
  row's context, each row holds at the configurations whose re-lends keep `Δ`'s models (`SemSR`).
  At `σ = []` that hypothesis is vacuous (the only re-lend of `[]` is `[]`), so `SemSR` and `SemS`
  agree there.
* **At `cbpv` and `binder`** the clause also owes the body at every future of the re-lend. The
  context reaches it by `MonoG`, which asks the future at the context's resource; that resource
  holds the inner entries' re-lent views, and a step inserting at depth `k > 0` puts its lifetimes
  above them, so `FutOK.below` fails there. And a future may insert a variable that is not
  `NsVar`, which `StackJ`'s second kind does not admit, so the premise is not available at that
  future. Neither is derived here.

No row is refuted here. `Relendability.lean` asks whether the configurations that break the first
two are reached.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS RelendableS jdgCty)
open BoCa.BoLo (Step1N Head)

/-- **The context's re-lendability at W** (GhostEnd's `thunkF_RLa` hypothesis `hG`, at the
placement's relation): a context related at the stack, at a resource with the table, is
re-lendable. Named, not proved. -/
def CtxRelendable (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (Γ : Ctx VTy) (γ : List Val)
    (ρ : WRes), StackOK σ αs → TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ →
    RelendableS δ [] σ (fun αs' ls' => gRL p σ δ αs' ls' Γ γ) αs ls ρ

/-- **The context's re-lendability at one row's context** `Δ; Γ`: at every index `SemS` admits
(the stack in shape, the substitution mapping only `Δ`'s variables and modelling `Δ` at the
stack's lifetimes, the table), a context related at the stack is re-lendable. The `U` rows take it
at their own context, where their proofs use it. `CtxRelendable p` gives it at every context
(`ctxRelendableAt_of`); that global form is refuted at `binder0` (`not_ctxRelendable_binder0`,
`Relendability.lean`), and so is this one at some contexts (`not_ctxRelendableAt_k`); it holds at
`Γ = []` and at a `U` slot (`ctxRelendableAt_nil`, `ctxRelendableAt_thunk`). -/
def CtxRelendableAt (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → SubDom δ Δ → Δ.Models (extS δ σ αs) → TabAtS σ αs ρ →
    gRL p σ δ αs ls Γ γ ρ → RelendableS δ [] σ (fun αs' ls' => gRL p σ δ αs' ls' Γ γ) αs ls ρ

theorem ctxRelendableAt_of {p : Placement} (h : CtxRelendable (ℍ := ℍ) p) (Δ : LifeCtx)
    (Γ : Ctx VTy) : CtxRelendableAt (ℍ := ℍ) p Δ Γ :=
  fun δ σ αs ls γ ρ hok _ _ ht hg => h σ δ αs ls Γ γ ρ hok ht hg

/-- `Δ = '0 ⊏ ⊤, '1 ⊏ '0`. -/
abbrev mΔ : LifeCtx := (LifeCtx.empty.extend 0 .top).extend 1 (.var 0)

/-- `'1 ↦ 2`; `'0` is the stack's. -/
abbrev mδ : LSub := ⟨[(1, 2)]⟩

/-- One `mut` entry lending the place `0` at the variable `'0`, payload `1`. -/
abbrev mσ : LStack := [⟨0, 0, .unit, .mut, fun _ => true⟩]

theorem mΔ_find (x : LifeVar) :
    mΔ.find? x = if x = 1 then some (.var 0) else if x = 0 then some .top else none := by
  by_cases h1 : x = 1
  · subst h1; rfl
  · by_cases h0 : x = 0
    · subst h0; rfl
    · simp only [h1, h0, if_false]
      simp [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, Lifetime.assocFind, Ne.symm h1,
        Ne.symm h0]

/-- **A re-lend can break `Δ`'s models at a configuration `SemS` admits.** At `'0 ↦ 1` both bounds
of `mΔ` hold (`⊤ = 0`, and the carrier's `⊏` is `>`); re-lent at `'0 ↦ 2`, `'1 ⊏ '0` reads
`2 ⊏ 2`. The stack is in shape and admitted by every judgement (`StackJ`), and `δ` maps only
`Δ`'s variables. -/
theorem models_reLend_fails : ∃ (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs αs' : List Life),
    StackOK σ αs ∧ (∀ Γ C, StackJ σ αs δ Δ Γ C) ∧ SubDom δ Δ ∧ Δ.Models (extS δ σ αs) ∧
      ReLend αs' αs ∧ ¬ Δ.Models (extS δ σ αs') := by
  refine ⟨mΔ, mδ, mσ, [OrderDual.toDual 1], [OrderDual.toDual 2], ⟨rfl, List.isChain_singleton _,
    List.nodup_singleton _⟩, fun Γ C => ⟨List.nodup_singleton _, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro e he y hy
    rw [List.mem_singleton.mp he] at hy
    exact absurd hy (by simp [VFree])
  · intro e he
    rw [List.mem_singleton.mp he]
    exact Or.inl ⟨.top, rfl⟩
  · intro y hy
    by_cases h1 : y = 1
    · subst h1; exact ⟨.var 0, rfl⟩
    · exact absurd (by simp [LSub.find?, Lifetime.assocFind, Ne.symm h1]) hy
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
  · exact ⟨List.Forall₂.cons (show OrderDual.toDual (2 : ℕ) ≤ OrderDual.toDual 1 from by decide)
      List.Forall₂.nil, List.isChain_singleton _⟩
  · intro h
    obtain ⟨m, n, hm, hn, hlt⟩ := h 1 (.var 0) rfl
    have hm' : m = 2 := by
      have : (extS mδ mσ [OrderDual.toDual 2]).find? 1 = some 2 := rfl
      rw [this] at hm; exact (Option.some.inj hm).symm
    have hn' : n = 2 := by
      have : (Lifetime.Life.var 0).interp (extS mδ mσ [OrderDual.toDual 2]) = some 2 := rfl
      rw [this] at hn; exact (Option.some.inj hn).symm
    subst hm' hn'
    exact absurd hlt (by simp [Lifetime.SLife.Lt])


/-! ### The table at a re-lend (statement 1's `TabRelend`) -/

/-- A view lies at its entry's place. -/
theorem vwE_places {δ : LSub} {e : LEnt} {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwE δ e d α ls ρ) : ∀ k ψ, ρ.get k = some ψ → k = e.l := by
  intro k ψ hk
  cases d with
  | false => obtain ⟨rfl, -⟩ := h; exact absurd (hk.symm.trans (PMap.empty_get k)) (by simp)
  | true =>
      obtain ⟨l, x, T, kd, cr⟩ := e
      cases kd with
      | «mut» =>
          obtain ⟨_, _, _, _, _, _, _, -, rfl, -⟩ := h
          exact (ResU.single_get_eq_some hk).1
      | imm v =>
          obtain ⟨_, _, _, _, _, rfl, -⟩ := h
          exact (ResU.single_get_eq_some hk).1

/-- **A stack's views lie at the stack's places.** -/
theorem vwS_places {δ : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs : List Life} {ls : List SRec} {ρ : WRes}, vwS δ seen σ ds αs ls ρ →
    ∀ k ψ, ρ.get k = some ψ → k ∈ σ.map LEnt.l
  | _, [], [], [], _, _, h, k, ψ, e => by
      obtain ⟨rfl, -⟩ := h; exact absurd (e.symm.trans (PMap.empty_get k)) (by simp)
  | _, e₀ :: σ, d :: ds, α :: αs, _, _, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩, k, ψ, e => by
      rcases ResU.Comp.get hc k with ⟨-, -, e'⟩ | ⟨ψ', e₁, -, -⟩ | ⟨ψ', -, e₂, -⟩ |
          ⟨ψ₁, ψ₂, ψ', e₁, -, -, -⟩
      · exact absurd (e.symm.trans e') (by simp)
      · exact List.mem_cons.mpr (Or.inl (vwE_places h₁ k ψ' e₁))
      · exact List.mem_cons_of_mem _ (vwS_places h₂ k ψ' e₂)
      · exact List.mem_cons.mpr (Or.inl (vwE_places h₁ k ψ₁ e₁))
  | _, [], [], _ :: _, _, _, h, _, _, _ => h.elim
  | _, [], _ :: _, [], _, _, h, _, _, _ => h.elim
  | _, [], _ :: _, _ :: _, _, _, h, _, _, _ => h.elim
  | _, _ :: _, [], [], _, _, h, _, _, _ => h.elim
  | _, _ :: _, [], _ :: _, _, _, h, _, _, _ => h.elim
  | _, _ :: _, _ :: _, [], _, _, h, _, _, _ => h.elim

/-- **`TabRelend`**: a share above the outermost lend, handed the views at a re-lend, has the table
at the re-lend. The share lies above every lend (`stratS_iff_all`), hence above the re-lent
innermost one; the views lie above the strict predecessor of the re-lent innermost lend
(`vwS_inStratum`) and at the stack's places (`vwS_places`). -/
theorem tabRelend : TabRelend (ℍ := ℍ) := by
  intro δ σ ds αs αs' ls ρz ρv R hok hr hz hv hc
  have hz' := (stratS_iff_all hok.2.1).mp hz
  refine ⟨fun a ha => ?_, fun a ha k ψ hk e => ?_⟩
  · refine (outlives_comp hc (↓a)).mpr ⟨?_, ?_⟩
    · -- the share: above the innermost lend, which the re-lend's innermost is below
      cases αs with
      | nil =>
          have := hr.1.length_eq; cases αs' with
          | nil => exact absurd ha (by simp)
          | cons _ _ => simp at this
      | cons α₁ αs₁ =>
          cases αs' with
          | nil => exact absurd ha (by simp)
          | cons a₁ αs₁' =>
              have ha' : a = a₁ := by simpa using ha.symm
              subst ha'
              have hle : a ≤ α₁ := by
                cases hr.1 with
                | cons h _ => exact h
              exact (hz' α₁ List.mem_cons_self).mono (le_of_lt (lt_of_lt_of_le (GhostEnd.down_lt a) hle))
    · -- the views: above `↓a`, every re-lent lifetime being at least the innermost
      refine GhostEnd.vwS_inStratum hv (↓a) fun α hα => ?_
      cases αs' with
      | nil => exact absurd ha (by simp)
      | cons a₁ αs₁' =>
          have ha' : a = a₁ := by simpa using ha.symm
          subst ha'
          rcases List.mem_cons.mp hα with rfl | hα
          · exact GhostEnd.down_lt _
          · exact lt_trans (GhostEnd.down_lt _) (GhostEnd.head_lt_mem hr.2 α hα)
  · -- away from the stack's places: only the share has a cell there
    refine ResU.inStratum_comp_at (CellU.compS_hC a) hc (fun φ f => ?_) (fun φ f => ?_) e
    · obtain ⟨b, hb, hab⟩ := GhostEnd.getLast?_le hr.1 a ha
      exact ((hz b (by simpa using hb)) k φ f).mono hab
    · exact absurd (vwS_places hv k φ f) hk

/-! ### The `U` introductions at `binder0`, given what they owe -/

/-- **`SemS` at the configurations whose re-lends keep `Δ`'s models**: `SemS` with one more
hypothesis on the index, every re-lend of the stack modelling `Δ` (`models_reLend_fails` shows it
is not implied). -/
def SemSR (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) → Scoped Δ Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → StackJ σ αs δ Δ Γ (jdgCty j) → SubDom δ Δ → Δ.Models (extS δ σ αs) →
    (∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) →
    TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ → cRL p σ δ (jdgCty j) αs ls (substAll γ e) ρ

theorem gRL_dead_cons {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec}
    {S : VTy} {Γ : Ctx VTy} {v : Val} {γ : List Val} {ρ : WRes} (h : gRL p σ δ αs ls Γ γ ρ) :
    gRL p σ δ αs ls (⟨S, false⟩ :: Γ) (v :: γ) ρ := by
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp h
  exact pure_sep_mk (by simpa using hlw) (by simpa [gSepRL] using hgs)

/-- The stack's entries in a judgement whose type is no `∀` are entries of every judgement at the
same `Δ` whose type's free variables and context's are among the first's: no entry is an own
lend. -/
theorem stackJ_body {σ : LStack} {αs αs' : List Life} {δ : LSub} {Δ : LifeCtx}
    {Γ Γ' : Ctx VTy} {C C' : CTy} (h : StackJ σ αs δ Δ Γ C) (hC : ∀ x c D, C ≠ .all x c D)
    (hfree : ∀ x, ¬ CFree x C → ¬ CFree x C') (hΓ : ∀ x, CtxAvoids x Γ → CtxAvoids x Γ') :
    StackJ σ αs' δ Δ Γ' C' := by
  obtain ⟨hn, hp, hk⟩ := h
  refine ⟨hn, hp, fun e he => ?_⟩
  rcases hk e he with h₁ | ⟨hns, hΔ, hCe, hctx⟩ | ⟨-, -, -, c, D, hall, -⟩
  · exact Or.inl h₁
  · exact Or.inr (Or.inl ⟨hns, hΔ, hfree _ hCe, hΓ _ hctx⟩)
  · exact absurd hall (hC _ _ _)

theorem ctxAvoids_dead {x : LifeVar} {S : VTy} {Γ : Ctx VTy} (h : CtxAvoids x Γ) :
    CtxAvoids x (⟨S, false⟩ :: Γ) := fun s hs hl => by
  rcases List.mem_cons.mp hs with rfl | hs
  · simp at hl
  · exact h s hs hl

/-- **The `U` clause of `thunk M : U (F A)` at `binder0`, given the context's thaw**: the clause at
the stack itself, the context re-lendable (`CtxRelendable`), the body at each re-lend by the
premise there, at the models the re-lend keeps, with the table there by `tabRelend`. -/
theorem thunkF_U_binder0 {Δ : LifeCtx} {Γ : Ctx VTy} (hR : CtxRelendableAt (ℍ := ℍ) .binder0 Δ Γ)
    {M : Expr} {A : VTy} (hM : SemS (ℍ := ℍ) .binder0 Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)))
    (hBL : BindersLow (⟨.unit, false⟩ :: Γ) (.ret A)) (hSc : Scoped Δ (⟨.unit, false⟩ :: Γ) (.ret A))
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hJ : ∀ αs', StackJ σ αs' δ Δ (⟨.unit, false⟩ :: Γ) (.ret A))
    (hSD : SubDom δ Δ) (hMod : Δ.Models (extS δ σ αs))
    (hModR : ∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) (ht : TabAtS σ αs ρ) (hg : gRL .binder0 σ δ αs ls Γ γ ρ) :
    vRL (ℍ := ℍ) .binder0 σ δ (.thunk (.ret A)) αs ls (.lam (Expr.psub 1 γ M)) ρ := by
  rw [vRL_thunk_eq]
  intro _
  rw [if_neg (by decide)]
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := hR δ σ αs ls γ ρ hok hSD hMod ht hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← GhostEnd.substAll_cons_l]
  exact hM hBL hSc δ σ αs' ls' (Val.unit :: γ) τ (hok.reLend hr) (hJ αs') hSD (hModR αs' hr)
    (tabRelend δ σ ds αs αs' ls' ρz ρv τ hok hr hz hv hcv)
    (gRL_dead_cons (H ls' he αs' hr ρv τ hv hcv))

/-- **The `U` clause of `thunk V : U C` at `binder0`, given the context's thaw**: as
`thunkF_U_binder0`, the thunk the λ-value itself. -/
theorem thunkV_U_binder0 {Δ : LifeCtx} {Γ : Ctx VTy} (hR : CtxRelendableAt (ℍ := ℍ) .binder0 Δ Γ)
    {N : Expr} {C : CTy} (hC : C.isRet = false)
    (hN : SemS (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.comp C))
    (hBL : BindersLow Γ C) (hSc : Scoped Δ Γ C)
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hJ : ∀ αs', StackJ σ αs' δ Δ Γ C)
    (hSD : SubDom δ Δ) (hMod : Δ.Models (extS δ σ αs))
    (hModR : ∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) (ht : TabAtS σ αs ρ) (hg : gRL .binder0 σ δ αs ls Γ γ ρ) :
    vRL (ℍ := ℍ) .binder0 σ δ (.thunk C) αs ls (.lam (Expr.psub 1 γ N)) ρ := by
  rw [vRL_thunk_eq]
  intro _
  rw [if_neg (by decide)]
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := hR δ σ αs ls γ ρ hok hSD hMod ht hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  rw [forceE_of_not_ret hC]
  exact hN hBL hSc δ σ αs' ls' γ τ (hok.reLend hr) (hJ αs') hSD (hModR αs' hr)
    (tabRelend δ σ ds αs αs' ls' ρz ρv τ hok hr hz hv hcv) (H ls' he αs' hr ρv τ hv hcv)

/-- **`ThunkFRow` at `binder0`, given the thaw of the row's own context** (`CtxRelendableAt` at
`Δ; Γ`), at the configurations whose re-lends keep `Δ`'s models (`SemSR`). -/
theorem thunkFRow_binder0_at :
    ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxRelendableAt (ℍ := ℍ) .binder0 Δ Γ →
      SemS (ℍ := ℍ) .binder0 Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
      SemSR (ℍ := ℍ) .binder0 Δ Γ (.val (.lam M)) (.val (.thunk (.ret A))) := by
  intro Δ Γ M A hR hM hBL hSc δ σ αs ls γ ρ hok hJ hSD hMod hModR ht hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ (thunkF_U_binder0 hR hM ⟨hBL.1, fun s hs hl => ?_⟩
    ⟨hSc.1, fun s hs hl => ?_⟩ hok (fun _ => stackJ_body hJ (fun _ _ _ h => by cases h)
      (fun _ h => h) fun _ => ctxAvoids_dead) hSD hMod hModR ht hg)
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl

/-- **`ThunkVRow` at `binder0`, given the thaw of the row's own context**, at the configurations
whose re-lends keep `Δ`'s models (`SemSR`). -/
theorem thunkVRow_binder0_at :
    ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxRelendableAt (ℍ := ℍ) .binder0 Δ Γ →
      C.isRet = false →
      SemS (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.comp C) →
      SemSR (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.val (.thunk C)) := by
  intro Δ Γ N C hR hC hN hBL hSc δ σ αs ls γ ρ hok hJ hSD hMod hModR ht hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val _ _ _ _ (thunkV_U_binder0 hR hC hN hBL hSc hok
    (fun _ => stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h)
    hSD hMod hModR ht hg)

/-- A persistent context holds nothing. -/
theorem gSepRL_persistent {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life}
    {ls : List SRec} : ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes), Persistent Γ →
    gSepRL p σ δ αs ls Γ γ ρ → ρ = PMap.empty
  | [], [], _, _, h => h.1
  | [], _ :: _, _, _, h => h.1
  | _ :: _, [], _, _, h => h.1
  | s :: Γ, v :: γ, ρ, hP, h => by
      have hP' : Persistent Γ := fun s' hs' hl => hP s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRL, hl, if_true] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        obtain ⟨A, hA⟩ := hP s List.mem_cons_self hl
        rw [hA] at h₁
        have e₁ : ρ₁ = PMap.empty := h₁.1
        rw [e₁, gSepRL_persistent Γ γ ρ₂ hP' h₂] at hc
        exact eq_empty_of_compS_empty hc
      · simp only [gSepRL, hl] at h
        exact gSepRL_persistent Γ γ ρ hP' h

/-- **`BangThunkFRow` at `binder0`, given the thaw of the row's own context**, at the
configurations whose re-lends keep `Δ`'s models: the context is persistent, so it, and the thunk
with it, hold nothing. -/
theorem bangThunkFRow_binder0_at :
    ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy), CtxRelendableAt (ℍ := ℍ) .binder0 Δ Γ →
      Persistent Γ →
      SemS (ℍ := ℍ) .binder0 Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) →
      SemSR (ℍ := ℍ) .binder0 Δ Γ (.val (.lam M)) (.val (.bang (.thunk (.ret A)))) := by
  intro Δ Γ M A hR hP hM hBL hSc δ σ αs ls γ ρ hok hJ hSD hMod hModR ht hg
  have hρ : ρ = PMap.empty := gSepRL_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ ⟨hρ, thunkF_U_binder0 hR hM ⟨hBL.1, fun s hs hl => ?_⟩
    ⟨hSc.1, fun s hs hl => ?_⟩ hok (fun _ => stackJ_body hJ (fun _ _ _ h => by cases h)
      (fun _ h => h) fun _ => ctxAvoids_dead) hSD hMod hModR ht hg⟩
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl

/-- **`BangThunkVRow` at `binder0`, given the thaw of the row's own context**, at the
configurations whose re-lends keep `Δ`'s models. -/
theorem bangThunkVRow_binder0_at :
    ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (N : Expr) (C : CTy), CtxRelendableAt (ℍ := ℍ) .binder0 Δ Γ →
      Persistent Γ → C.isRet = false →
      SemS (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.comp C) →
      SemSR (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.val (.bang (.thunk C))) := by
  intro Δ Γ N C hR hP hC hN hBL hSc δ σ αs ls γ ρ hok hJ hSD hMod hModR ht hg
  have hρ : ρ = PMap.empty := gSepRL_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val _ _ _ _ ⟨hρ, thunkV_U_binder0 hR hC hN hBL hSc hok
    (fun _ => stackJ_body hJ (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h)
    hSD hMod hModR ht hg⟩

end ProbeD1

end
