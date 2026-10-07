import ProbeD1.Rows0

/-!
# ProbeD1 — the `U` introductions at W: what they owe, and what is not derived

`ThunkFRow`, `ThunkVRow`, `BangThunkFRow` and `BangThunkVRow` (statement 0) introduce a `U` value
at W. Their conclusion is the `U` clause of a closure over the context, so it owes the body at
every re-lend of the stack (and, at `cbpv` and `binder`, at every future of the re-lend; at `cbpv`
at the own push there). GhostEnd proves the clause's half of each row at its own relation
(`thunkF_RLa`, `thunkE_RLa`), taking two things as hypotheses: the context re-lendable (`hG`) and
the body at every re-lend (`hM`). At W each is a fact about the judgement, and neither is derived
here.

* **The context's re-lendability** (`CtxRelendable`, named here, not proved): a context related
  at the stack, at a resource with the table, splits into the views it holds and a part above the
  outermost lend that, handed the views at any re-lend, is the context there. A `U` slot meets it
  by construction (`thawRelend`). A leaf holding a cell at a stack place that is not that entry's
  view (a different payload predicate) is not covered by the table, and nothing here excludes it.
* **The body at a re-lend.** It comes from the premise's `SemS` at the re-lent stack, which asks
  `Δ.Models` there. A re-lend need not keep it at a configuration `SemS` admits
  (`models_reLend_fails`): a variable of `Δ` off the stack, bounded by a stack variable, keeps
  `δ`'s lifetime while the stack's is re-lent below it. So the premise does not give the body at
  every re-lend the clause owes.
* **The table at a re-lend** is statement 1's `TabRelend`; at a future, `TabFut`.
* **At `cbpv` and `binder`**, the context at a future of the re-lend: `MonoG` asks the future at the
  context's resource, which holds the inner entries' re-lent views; a step that inserts at depth
  `k > 0` puts its lifetimes above those views, so `FutOK.below` fails there.

None of this is an obstruction: no configuration here arises in `TW`, and no row is refuted. It is
what a proof of the four rows must supply. I have not derived them and have not verified that any
obstruction is real.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS RelendableS)

/-- **The context's re-lendability at W** (GhostEnd's `thunkF_RLa` hypothesis `hG`, at the
placement's relation): a context related at the stack, at a resource with the table, is
re-lendable. Named, not proved. -/
def CtxRelendable (p : Placement) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (Γ : Ctx VTy) (γ : List Val)
    (ρ : WRes), StackOK σ αs → TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ →
    RelendableS δ [] σ (fun αs' ls' => gRL p σ δ αs' ls' Γ γ) αs ls ρ

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

end ProbeD1

end
