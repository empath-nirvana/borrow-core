import Targets.Defs.World
import Targets.Defs.Typing
import Targets.Defs.Runs

/-!
# Targets — the proof device: the fundamental lemma at W and the laws of W (DESIGN §4)

**World:** [W], at the end state's `M`.

* `FL M J`: every judgment of the typing system holds in W's relation, at every admissible
  instance ([TR] 6.151's shape).
* `Adequate M`: a closed computation in W's relation is safe and terminating under every platform
  (or safely driven).  Soundness is a corollary of FL and adequacy (`SoundnessOfFL`,
  `Statements/Composition.lean`).
* `WLaws M`: the laws every W satisfies.  Together they bound the relation from above at every
  index and every type former: data values are exactly data (`DataVals`), a computation of `F_Σ A`
  at an unr-free row is exactly W's runs (`EffInterp`), every other former is bounded by its
  eliminations and its shape (`RelLaws`; at `Imm` and `Mut` by Core's own clauses, with W's
  relation for the payload), and every run from every configuration W reaches is safe
  (`AdequateEvery`).

`SliceShape` pins the nil slice only structurally: the configurations, the order and the stop at
σ = [] are Core's.  It does not ask W's relation at σ = [] to equal Core's (DESIGN §4.2): the
embedding of Core into W is `ConservativeWB` (`Statements/Conservativity.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core

mutual
/-- Every effect layer anywhere in the type is abortive: the operations a callback of this type can
perform are in `{fn, abort}` (answering effects are borrows, not rows; I4). -/
def VTy.AbortRows : VTy → Prop
  | .tensor A B | .sum A B => A.AbortRows ∧ B.AbortRows
  | .thunk C => C.AbortRows
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .mu A | .fam A => A.AbortRows
  | .unit | .zero | .unk | .tvar _ | .int _ | .opq _ => True
/-- `VTy.AbortRows` at a computation type. -/
def CTy.AbortRows : CTy → Prop
  | .ret A => A.AbortRows
  | .arr A C => A.AbortRows ∧ C.AbortRows
  | .amp C D => C.AbortRows ∧ D.AbortRows
  | .top => True
  | .all _ _ C | .nu C => C.AbortRows
  | .eff _ _ q A B C => (B.isZero && q != .lin) = true ∧ A.AbortRows ∧ B.AbortRows ∧ C.AbortRows
end

end BoCa.Fig16.LogRel.Core

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### FL and adequacy (DESIGN §4.1) -/

/-- **The fundamental lemma at W**: every judgment of `J` holds in W's relation. -/
def FL (M : SemWorld) (J : TypingJ) : Prop := ∀ Θ Δ Γ e j, J Θ Δ Γ e j → SemW M Θ Δ Γ e j

/-- Adequacy at a platform, for programs at a div-free answer. -/
def AdequateRetAt (M : SemWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A : VTy) (e : Expr), DivFree S A → RowLe S P.ops →
    M.comp (CTy.effOf S A) ([], M.nil) LSub.empty e (PMap.empty : WRes) →
    SafeRuns (ℍ := ℍ) P A e ∧ Terminates (ℍ := ℍ) P A e

/-- Adequacy at a platform, for programs that return a loop. -/
def AdequateDriveAt (M : SemWorld) (P : Platform) : Prop :=
  ∀ (S : Row) (A B : VTy) (e : Expr), A.Data → RowLe S P.ops →
    M.comp (CTy.effOf S (.thunk (CTy.loopEff S A B))) ([], M.nil) LSub.empty e
      (PMap.empty : WRes) →
    SafeDrive (ℍ := ℍ) P A e

/-- Adequacy at a platform. -/
def AdequateAt (M : SemWorld) (P : Platform) : Prop :=
  AdequateRetAt (ℍ := ℍ) M P ∧ AdequateDriveAt (ℍ := ℍ) M P

/-- **Adequacy**: at every platform that respects its protocol. -/
def Adequate (M : SemWorld) : Prop := ∀ P : Platform, P.Respects → AdequateAt (ℍ := ℍ) M P

/-! ### The laws every W satisfies (DESIGN §4.2) -/

/-- **The nil slice, structurally**: at σ = [] nothing is held, the configurations, the order and
the stop are Core's, and a stored payload is read at σ = []. -/
def SliceShape (M : SemWorld) : Prop :=
  (∀ ls, M.held (ls, M.nil) = ([], [])) ∧
  (∀ fρ ps ls, M.Fam fρ ps (ls, M.nil) ↔ TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls) ∧
  (∀ ls ls' ρ, M.Ext (ls, M.nil) (ls', M.nil) ρ ↔ Ext ls ls' ρ) ∧
  (∀ ps ls ps' ls' t, M.Stop (ps, (ls, M.nil)) (ps', (ls', M.nil)) t ↔
     (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)) ∧
  (∀ b, M.payStk b M.nil = M.nil)

/-- **Mono**: Kripke monotonicity of the value relation, in both modes. -/
def Mono (M : SemWorld) : Prop :=
  ∀ b A i i' δ v ρ, M.Ext i i' ρ → M.val b A i δ v ρ → M.val b A i' δ v ρ

/-- The Kripke order is a preorder. -/
def ExtPre (M : SemWorld) : Prop :=
  (∀ i ρ, M.Ext i i ρ) ∧ (∀ i i' i'' ρ, M.Ext i i' ρ → M.Ext i' i'' ρ → M.Ext i i'' ρ)

/-- **EffInterp**: an unr-free row is read through its protocol ("opTable is the
interpretation"). -/
def EffInterp (M : SemWorld) : Prop :=
  ∀ S R i δ e ρ, Row.NU S → (M.comp (CTy.effOf S R) i δ e ρ ↔
    ewpW (ℍ := ℍ) M i e (opTabW M (rowTabW M S δ)) (fun j v => M.val true R j δ v) ρ)

/-- The empty configuration is reached at the nil index. -/
def FamEmpty (M : SemWorld) : Prop := M.Fam (PMap.empty : WRes) [] ([], M.nil)

/-- Data values are exactly data, and hold nothing. -/
def DataVals (M : SemWorld) : Prop :=
  ∀ b A i δ v ρ, A.Data → (M.val b A i δ v ρ ↔ ρ = PMap.empty ∧ DataVal A v)

/-- The share is monotone in what it owes, at non-`unr` entries. -/
def ShareMono (M : SemWorld) : Prop :=
  ∀ T en n i K (Φ Φ' : Idx M.Stk → Expr → WProp) ρ, en.q ≠ .unr →
    (∀ i e ρ, Φ i e ρ → Φ' i e ρ) → M.share T en n i K Φ ρ → M.share T en n i K Φ' ρ

/-- The eliminations, at the same index.  None has an `M.Ext` quantifier, so each holds under
either option of OQ-8. -/
def RelElim (M : SemWorld) : Prop :=
  (∀ C i δ v ρ, M.val true (.thunk C) i δ v ρ → M.comp C i δ (forceE C (.val v)) ρ) ∧
  (∀ A C i δ e ρ, M.comp (.arr A C) i δ e ρ →
     ∀ v, (M.val true A i δ v ─⋆ M.comp C i δ (.app e (.val v))) ρ) ∧
  (∀ C D i δ e ρ, M.comp (.amp C D) i δ e ρ →
     M.comp C i δ (.app e (.val (Val.inj₁ .unit))) ρ ∧
     M.comp D i δ (.app e (.val (Val.inj₂ .unit))) ρ) ∧
  (∀ x b C i δ e ρ, M.comp (.all x b C) i δ e ρ → ∀ α, LtLife δ b α →
     M.comp C i (δ.extend x α) (.app e (.val .unit)) ρ) ∧
  (∀ C i δ e ρ, C.NuOk → M.comp (.nu C) i δ e ρ → M.comp C.unroll i δ e ρ) ∧
  (∀ b A i δ v ρ, M.val b (.mu A) i δ v ρ → M.val b (VTy.inst (.mu A) A) i δ v ρ)

/-- **The shapes of values**, at the same index: `vCE`'s clauses with W's relation in place of
`vCE`'s recursive calls.  At `Imm` and `Mut` these are Core's `ptoImmS`/`ptoMutS` clauses at W's
index, with the coherence `CohE` and the payload in W's relation: the observable view at `Imm`, the
program's relation at `Mut`. -/
def RelShape (M : SemWorld) : Prop :=
  (∀ b i δ v ρ, M.val b .unit i δ v ρ → v = .unit ∧ ρ = PMap.empty) ∧
  (∀ b i δ v ρ, ¬ M.val b .zero i δ v ρ) ∧
  (∀ b A B i δ v ρ, M.val b (.tensor A B) i δ v ρ →
     ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ (M.val b A i δ v₁ ⋆ M.val b B i δ v₂) ρ) ∧
  (∀ b A B i δ v ρ, M.val b (.sum A B) i δ v ρ →
     (∃ w, v = Val.inj₁ w ∧ M.val b A i δ w ρ) ∨ (∃ w, v = Val.inj₂ w ∧ M.val b B i δ w ρ)) ∧
  (∀ b A i δ v ρ, M.val b (.ref A) i δ v ρ →
     ∃ ℓ v', v = Val.loc ℓ ∧ (ptoOwn ℓ v' ⋆ M.val b A i δ v') ρ) ∧
  (∀ b A i δ v ρ, M.val b (.bang A) i δ v ρ → ρ = PMap.empty ∧ M.val true A i δ v ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.box a A) i δ v ρ →
     atLife δ a (fun α => box α (M.val b A i δ v)) ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.imm a A) i δ v ρ →
     atLife δ a (fun α => ex fun ℓ => ⌜v = Val.loc ℓ ∧ CohE (rsOf i.1) ℓ A δ⌝ ⋆
       ptoImmSW M ℓ α i (fun i₀ => M.val false A i₀ δ)) ρ) ∧
  (∀ b a A i δ v ρ, M.val b (.mut a A) i δ v ρ →
     atLife δ a (fun α => ex fun ℓ => ⌜v = Val.loc ℓ⌝ ⋆
       ptoMutSW M ℓ α i (fun i₀ => M.val true A i₀ δ)) ρ) ∧
  (∀ b L i δ v ρ, M.val b (.fam L) i δ v ρ → ∃ ℓ c, v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31 ∧
     sepRange (fun m => M.val b L i δ (Val.loc m)) ℓ c.toNat ρ) ∧
  (∀ b i δ v ρ, M.val b .unk i δ v ρ → ρ = PMap.empty) ∧
  (∀ b w i δ v ρ, M.val b (.int w) i δ v ρ → v.IsInt w ∧ ρ = PMap.empty) ∧
  (∀ b k i δ v ρ, M.val b (.opq k) i δ v ρ → k.Holds v ∧ ρ = PMap.empty) ∧
  (∀ b n i δ v ρ, ¬ M.val b (.tvar n) i δ v ρ)

/-- The eliminations and the shapes. -/
def RelLaws (M : SemWorld) : Prop := RelElim M ∧ RelShape M

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

end
