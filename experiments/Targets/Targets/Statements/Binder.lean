import Targets.Defs.Binder
import Targets.Statements.Soundness

/-!
# Targets — the freeze binder (I2.c), a target beside done (DESIGN §5 I2.c, §2 D9)

**World:** [W] (`FreezeBinderLoc`, `FreezeBinderLife`) and [prog] (`BinderMachine`,
`ReleasedOnceReuse`).  **Beside done**: stated at the same `M`, available, and not required.

"Freeze is a binder over internal locations, lifetimes and instances; resume and placement
instantiate it" (user, 2026-10-04).  The notebook lists what it unifies as "hypotheses to check",
and the brief asks that I2 be stated so that the reading is **available**, without presupposing
the hard proof.  So the binder is its own target at the same `M`, not a conjunct of done
(`EndStateBinder` adds it): I2's fields are the ones the binder acts on, and a W that meets every
guarantee and fails the binder still meets done.

* **locations** are a symmetry: a block-affine permutation is invertible, so its clauses are `↔`;
* **lifetimes** are instantiation: a re-stratification is injective and not surjective, so its
  clauses are forward implications.

The lifetime half carries a known risk: Restrat's `not_vDenNatural` refutes naturality of
`𝒱⟦Mut 'a (Imm 'b 1)⟧` at the paper layer, over all resources, in the forward direction the
`val` clause states.  Whether its witness arises was never checked; the binder's track starts with
that arising check, stated as `NotVDenNaturalArises`.  `FreezeBinder` is OPEN at every world.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The binder, location half, machine**: a run whose arrays lie in blocks `π` moves as blocks
renames to a run. -/
def BinderMachine : Prop :=
  ∀ (π : Equiv.Perm Loc) (rs : Ranges) μ e μ' e', BlockAffine π rs →
    StepsIn (ℍ := ℍ) rs μ e μ' e' →
    StepsIn (ℍ := ℍ) (fun q => ∃ p, rs p ∧ q = (π p.1, p.2)) (μ.renameLoc π) (e.renameLoc π)
      (μ'.renameLoc π) (e'.renameLoc π)

/-- **The binder at W, locations**: equivariance under a block-affine permutation of a
configuration that arises. -/
def FreezeBinderLoc (M : SemWorld) (a : StkAct M) : Prop :=
  (∀ π fρ ps i, BlockAffine π (ResU.arrRanges fρ) →
     (M.Fam fρ ps i ↔ M.Fam (fρ.mapLoc π) (ps.map (FrameRec.renameLoc π)) (idxLocAct a π i))) ∧
  (∀ π i, M.held (idxLocAct a π i) = heldLoc π (M.held i)) ∧
  (∀ π i i' ρ, M.Ext i i' ρ ↔ M.Ext (idxLocAct a π i) (idxLocAct a π i') (ρ.mapLoc π)) ∧
  (∀ π ps i ps' i' t, M.Stop (ps, i) (ps', i') t ↔
     M.Stop (ps.map (FrameRec.renameLoc π), idxLocAct a π i)
       (ps'.map (FrameRec.renameLoc π), idxLocAct a π i') (t.renameLoc π)) ∧
  (∀ π fρ ps i ρ ρf b A δ v, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (ResU.arrRanges fρ ⊔ v.1.arrRanges) →
     (M.val b A i δ v ρ ↔ M.val b A (idxLocAct a π i) δ (v.renameLoc π) (ρ.mapLoc π))) ∧
  (∀ π fρ ps i ρ ρf C δ e, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (ResU.arrRanges fρ ⊔ e.arrRanges) →
     (M.comp C i δ e ρ ↔ M.comp C (idxLocAct a π i) δ (e.renameLoc π) (ρ.mapLoc π))) ∧
  (∀ π fρ ps i ρ ρf T en n K Φ, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (ResU.arrRanges fρ ⊔ Kont.arrRanges K) →
     (M.share T en n i K Φ ρ ↔
       M.share (tabLocAct a π T) (entLocAct a π en) n (idxLocAct a π i) (K.renameLoc π)
         (predLocAct a π Φ) (ρ.mapLoc π)))

/-- **The binder at W, lifetimes**: instantiation along a re-stratification below a cut, of a
configuration that arises.  Every clause is forward. -/
def FreezeBinderLife (M : SemWorld) (a : StkAct M) : Prop :=
  (∀ c (θ : Restrat.Emb c) fρ ps i, M.Fam fρ ps i →
     M.Fam (θ.relRU fρ) (ps.map (FrameRec.restrat θ)) (idxLifeAct a θ i)) ∧
  (∀ c (θ : Restrat.Emb c) i, M.held (idxLifeAct a θ i) = heldRestrat θ (M.held i)) ∧
  (∀ c (θ : Restrat.Emb c) i i' ρ, M.Ext i i' ρ →
     M.Ext (idxLifeAct a θ i) (idxLifeAct a θ i') (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) ps i ps' i' t, M.Stop (ps, i) (ps', i') t →
     M.Stop (ps.map (FrameRec.restrat θ), idxLifeAct a θ i)
       (ps'.map (FrameRec.restrat θ), idxLifeAct a θ i') t) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf b A δ v, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.val b A i δ v ρ →
     M.val b A (idxLifeAct a θ i) (Restrat.LSub.mapN θ.toNat δ) v (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf C δ e, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.comp C i δ e ρ →
     M.comp C (idxLifeAct a θ i) (Restrat.LSub.mapN θ.toNat δ) e (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf T en n K Φ, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.share T en n i K Φ ρ →
     M.share (tabImgLife a θ T) (entImgLife a θ en) n (idxLifeAct a θ i) K (predImgLife a θ Φ)
       (θ.relRU ρ))

/-- **The freeze binder at W.** -/
def FreezeBinder (M : SemWorld) (a : StkAct M) : Prop :=
  FreezeBinderLoc M a ∧ FreezeBinderLife M a

/-- **Exactly-once release on runs that reuse locations** (beside done): each such complete run
has a no-reuse sibling, step for step, related to it at each step by a location renaming; the
sibling releases each cell exactly once.  Its proof needs `BinderMachine` at block-affine
permutations (OQ-43 (b)). -/
def ReleasedOnceReuse (J : TypingJ) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet (ℍ := ℍ) Γ γ →
    ∀ cs, PRun (ℍ := ℍ) P (init P (substAll γ e) :: cs) →
      (∀ c, (init P (substAll γ e) :: cs).getLast? = some c → Final P A c) →
      ∃ (cs' : List (Conf P)) (πs : ℕ → Equiv.Perm Loc),
        cs'.length = cs.length ∧ PRun (ℍ := ℍ) P (init P (substAll γ e) :: cs') ∧
        NoReuse (init P (substAll γ e) :: cs') ∧ ReleasedOnce (init P (substAll γ e) :: cs') ∧
        ∀ k (c c' : Conf P), cs[k]? = some c → cs'[k]? = some c' →
          c'.e = c.e.renameLoc (πs k) ∧ c'.μ = c.μ.renameLoc (πs k)

/-- **The arising check of `Restrat.Open.not_vDenNatural`'s witness at `coreW`**: some
configuration Core's world reaches holds the witness resource `MutCounterexample.ρ₀` (a `mut` cell
storing an `imm` cell at the lifetime the shift `n ↦ n + 1` leaves out) as a part of its world. -/
def NotVDenNaturalArises : Prop :=
  ∃ (fρ ρf : WRes) (ps : List FrameRec) (ls : List SRec),
    (coreW (ℍ := ℍ)).Fam fρ ps (ls, ()) ∧ ResU.CompS ρf Restrat.MutCounterexample.ρ₀ fρ

end Targets

end
