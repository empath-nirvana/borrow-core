import ProbeD1.Relation

/-!
# ProbeD1 — the semantic judgement at W, and W as a `SemWorld` (DESIGN §2.4, §2.5)

**`SemS p`** is GhostEnd's `SemA` (`gfp-arising:…/Arising.lean`) at the placement's relation: the
conclusion of the fundamental lemma at W for one judgement, at every stack the judgement admits.
FL at W for a rule is the rule's compatibility lemma at `SemS`.

Targets' `SemW`/`FL` (`Targets/B/World.lean`, `Targets/B/Guarantees.lean`) quantify over every
index with no hypothesis on its stack. At a stack whose variables a binder of the judgement
rebinds, or whose lifetimes do not model `Δ`, the rows' proofs have nothing to work with, so the
probe states FL at W with GhostEnd's index hypotheses (`StackOK`, `StackJ`, the models, the table).
At the nil index `SemS` and Targets' `SemW₀` read the same judgement.

**`WP p`** is the world as a `Targets.SemWorld`: the configurations are `TW`'s, the run-end
relation is Core's `↭` at every index, nothing is held, a run's stop is R-T1 with the stack fixed,
a stored payload is read stack-free (OQ-46 (b), as `vRLs`'s leaves read `vC`), and the order is
`OrdW` read at the empty substitution. Its `share` is Core's `contShare` at the record list: at a
stack index the ghost-end share lives in the relation's `F_Σ` clause (`bodyS`/`bodySF`), not in
this field.

Definitions only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack extS TabAtS jdgCty)
open Targets (Idx OpTabI OpEntI TableI)

/-- `x` is free in no live slot of `Γ`. -/
def CtxAvoids (x : LifeVar) (Γ : Ctx VTy) : Prop :=
  ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty

/-- **Binder hygiene**: no binder of the judgement's types is a name a future gives an entry
(`NsVar`). Every row takes it of the types its premises add (the rule's binder, its intermediate
types), as `allI_RLa` takes `hσx`. -/
def BindersLow (Γ : Ctx VTy) (C : CTy) : Prop :=
  (∀ x ∈ CTy.binders C, ¬ NsVar x) ∧ ∀ s ∈ Γ, s.live = true → ∀ x ∈ VTy.binders s.ty, ¬ NsVar x

/-- **The stack's entries in a judgement** `Δ; Γ ⊢ _ : C`: distinct variables, each one of three
kinds.
* A variable of `Δ` (GhostEnd's `LStack.WF`).
* A future's name (`NsVar`), new to `Δ` and free nowhere in `Γ` and `C`: an entry a future
  inserted. Under `BindersLow` no binder of the judgement is one.
* The innermost entry named by `C`'s outermost `∀`, new to `Δ`, at a lifetime meeting its bound,
  the variable bound nowhere else in `C` and free nowhere in `Γ`: the callback's own lend, which the
  `U` clause makes at `cbpv`. -/
def StackJ (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) :
    Prop :=
  (σ.map LEnt.x).Nodup ∧ ∀ e ∈ σ,
    (∃ u, Δ.find? e.x = some u) ∨
    (NsVar e.x ∧ Δ.find? e.x = none ∧ ¬ CFree e.x C ∧ CtxAvoids e.x Γ) ∨
    (Δ.find? e.x = none ∧ σ.head? = some e ∧ CtxAvoids e.x Γ ∧
      ∃ c C', C = .all e.x c C' ∧ e.x ∉ CTy.binders C' ∧ ∀ a ∈ αs.head?, LtLife (extS δ σ αs) c a)

/-- **The semantic judgement at W** (GhostEnd's `SemA` at the placement's relation): for a judgement
whose binders are hygienic, at every stack in shape that it admits, every substitution modelling
`Δ` at the stack's lifetimes, and every resource consistent with the stack's table, the context's
relation gives the conclusion's. -/
def SemS (p : Placement) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  BindersLow Γ (jdgCty j) →
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
    StackOK σ αs → StackJ σ αs δ Δ Γ (jdgCty j) → Δ.Models (extS δ σ αs) →
    TabAtS σ αs ρ → gRL p σ δ αs ls Γ γ ρ → cRL p σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-- W's order as the `Ext` field: `OrdW` at the empty substitution, an inserted variable new to the
stack and a future's name. -/
def ExtW (i i' : Ix) (ρ : WRes) : Prop := OrdW LSub.empty i i' ρ

/-- A table at W's index read at the records, the stack fixed. -/
def OpTabI.at (T : OpTabI Ix) (s : Stk) : OpTab :=
  fun n j => (T n j).map fun en => ⟨en.q, en.abort, fun ls v => en.PA (ls, s) v,
    fun ls v => en.PB (ls, s) v⟩

/-- **W as the interaction's world.** -/
def WP (p : Placement) : Targets.SemWorld where
  Stk := Stk
  nil := ([], [])
  Fam fρ ps i := TW fρ ps (rsOf i.1) ∧ Tagged fρ ps i.1 ∧ StackOK i.2.1 i.2.2
  Upd _ _ ρ _ π := ResU.UpdV ρ π
  Ext := ExtW
  payStk _ _ := ([], [])
  val b A i δ v := if b then vRL p i.2.1 δ A i.2.2 i.1 v else vC false A i.1 (extS δ i.2.1 i.2.2) v
  comp C i δ e := cRL p i.2.1 δ C i.2.2 i.1 e
  held _ := ([], [])
  Stop a b _ := (∀ q, q ∈ b.1 ↔ q ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1) ∧ b.2.2 = a.2.2
  share T en n i K Φ :=
    contShare (OpTabI.at T i.2) ⟨en.q, en.abort, fun ls v => en.PA (ls, i.2) v,
      fun ls v => en.PB (ls, i.2) v⟩ n i.1 K (fun ls t => Φ (ls, i.2) t)

end ProbeD1

end
