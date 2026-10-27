import Frontend.Check.Program
import Core.Demonic
import Lowering.Low

/-!
# Lowering — the obligations  `[spec §53]`

A lowering keeps the kernel's guarantees by putting its output in the relation at the source's
type: `SemC` of the lowered term, at the checked program's context and type, proved once as a
theorem about the lowering function. That is the semantic typing the kernel already uses for
constants (`swap`) and for `PinLaw`; it is not a check of each compiled program, and it does not
derive `CDerives` for the output.

- `LowerSem lower`: every checked program with no relaxed rule lowers into the relation.
- `LowerSemRel lower`: whatever puts the source in the relation puts the lowered term there; with
  `PinLaw` it covers the programs with relaxed rules (`checked_sem_pin`).
- `LowersInto Site lower`: the output is in the low subset (`Lowering/Low.lean`).

`lowered_every_run` and `lowered_every_run_pin` are what the obligation buys with no new adequacy
proof: through `theorem32D`, every run of a lowered closed `F 1` program from the empty memory
continues to `()` at the empty memory. `erase_lowerSem` is the obligation's witness: the erasure
itself satisfies it.
-/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Lowering
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Check Frontend.Check
open BoCa.Lifetime (LSub LifeCtx)

/-- **The obligation**: the lowered term is in the kernel's relation at the source's context and
type, for every checked `main` with no relaxed rule. -/
def LowerSem (lower : TExpr → Expr) : Prop :=
  ∀ c : Checked, c.pins = [] → SemC (ℍ := ℍ) LifeCtx.empty c.ctx (lower c.t) c.C

/-- **The relative obligation**: whatever puts the source in the relation (the Fundamental
Property, or the Fundamental Property under `PinLaw`) puts the lowered term there too. -/
def LowerSemRel (lower : TExpr → Expr) : Prop :=
  ∀ c : Checked, SemC (ℍ := ℍ) LifeCtx.empty c.ctx c.t.erase c.C →
    SemC (ℍ := ℍ) LifeCtx.empty c.ctx (lower c.t) c.C

/-- **The output is low**: every checked `main` lowers into the low subset over its context, with
its stored-continuation sites `Site c`. -/
def LowersInto (Site : Checked → Expr → Prop) (lower : TExpr → Expr) : Prop :=
  ∀ c : Checked, LowExpr (Site c) c.ctx.length (lower c.t)

/-- **The output is low on a class `P` of checked programs.** `LowersInto` is the class of all. -/
def LowersIntoOn (Site : Checked → Expr → Prop) (P : Checked → Prop) (lower : TExpr → Expr) :
    Prop :=
  ∀ c : Checked, P c → LowExpr (Site c) c.ctx.length (lower c.t)

theorem lowersInto_iff (Site : Checked → Expr → Prop) (lower : TExpr → Expr) :
    LowersInto Site lower ↔ LowersIntoOn Site (fun _ => True) lower :=
  ⟨fun h c _ => h c, fun h c => h c trivial⟩

/-- A closed `F 1` term in the relation: every run from the empty memory continues to `()` at the
empty memory (`theorem32D`). -/
theorem every_run_of_sem {e : Expr} (hsem : SemC (ℍ := ℍ) LifeCtx.empty [] e (.ret .unit))
    {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr} (hs : BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ e₁) :
    BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val .unit) := by
  have hwp := hsem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have he : substAll [] e = e := Adequacy.psub_nil 0 _
  rw [he] at hwp
  obtain ⟨v, h, rfl⟩ := theorem32D (ℍ := ℍ) e (· = Val.unit) hwp hs
  exact h

/-- **What the obligation buys**: every run of the lowered closed `F 1` program from the empty
memory continues to `()` at the empty memory. -/
theorem lowered_every_run {lower : TExpr → Expr} (hL : LowerSem (ℍ := ℍ) lower) (c : Checked)
    (hp : c.pins = []) (hΓ : c.ctx = []) (hC : c.C = .ret .unit)
    {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (lower c.t) μ₁ e₁) :
    BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val .unit) := by
  have hsem := hL c hp
  rw [hΓ, hC] at hsem
  exact every_run_of_sem hsem hs

/-- Under `PinLaw`, the relative obligation gives the same for every checked `main`. -/
theorem lowered_every_run_pin {lower : TExpr → Expr} (hPin : PinLaw (ℍ := ℍ))
    (hL : LowerSemRel (ℍ := ℍ) lower) (c : Checked) (hΓ : c.ctx = []) (hC : c.C = .ret .unit)
    {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (lower c.t) μ₁ e₁) :
    BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val .unit) := by
  have hsem := hL c (checked_sem_pin hPin c)
  rw [hΓ, hC] at hsem
  exact every_run_of_sem hsem hs

/-- The relative obligation gives the absolute one. -/
theorem LowerSemRel.lowerSem {lower : TExpr → Expr} (hL : LowerSemRel (ℍ := ℍ) lower) :
    LowerSem (ℍ := ℍ) lower :=
  fun c hp => hL c (checked_sem c hp)

/-- **The witness**: the erasure itself satisfies the obligation (`checked_sem`). -/
theorem erase_lowerSem : LowerSem (ℍ := ℍ) TExpr.erase := fun c hp => checked_sem c hp

/-- The erasure satisfies the relative obligation. -/
theorem erase_lowerSemRel : LowerSemRel (ℍ := ℍ) TExpr.erase := fun _ h => h

/-- A value at `!A` owns nothing: a lowering that puts a persistent value's parts in a heap cell
cannot keep its source type `!A` in the relation. Boxing is representation, below the low
subset. -/
theorem bang_owns_nothing {A : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vC true (.bang A) ls δ v ρ) : ρ = PMap.empty := by
  simp only [vCE] at h
  exact h.1

end Lowering
