import Law2.Straight
import Law2.World
import GhostEnd.Open

/-!
# Law2 — Law 2, stated, with its open steps enumerated

**Law 2**: a lend ended at a stop is re-lent at a fresh lifetime beneath the resumer's list, and
the suspended continuation is related at that lifetime — at any nesting of lends.

`law2` states it for a borrower Core's typing derives at a resuming row, holding a mixed stack of
lends open across its stops (`MixedStack`: `mut` lends of distinct places, `imm` lends, reborrows),
every operation of the row crossing every lend: beside the owners of the stack's lenders, the
borrower is its `ewpTS`, the owners handed back with its answer. Its proof is `fold_mixed` (every
lender's ghost end at a stop and re-lend at resume, by one induction on the stack) applied to the
borrower's piece, which is the one open step:

* **(S1) `piece_of_typed`**: a borrower Core's typing derives is D16.1's piece at its stack — at
  every stop of every run, the suspended continuation runs again at every re-lend of the stack,
  handed the views made afresh. **Not derived; no obstruction verified.** It is the κ-side property
  at every stop (`KappaRelends`, read at the stack's re-lends), and the fundamental lemma at the
  stacked relation (GhostEnd's `GFP`).

Discharged parts of (S1): for straight-line borrowers it is proved (`law2_straight`, from
`runsAt_of_typed`: the fundamental property at the re-lent reading, the context rebuilt from the
views, closures re-derived hereditarily), with the acceptance instances as its corollaries
(`Law2/Instances.lean`).

`law2_depth1` is the program-level statement at one lend: the resume rule's compatibility for the
borrow constant `withbor` at a resuming row, GhostEnd's `withbor_of_relendOfTyped`, whose open
step is the same κ-side property at one lend:

* **(S1′) `relendOfTyped`**: GhostEnd's `RelendOfTyped` (every borrower typed at a resuming row is
  re-lendable). **Not derived; no obstruction verified.**

Outside `law2`'s class, not derived: an inner lend whose payload type reads the stack's own
variables (a borrow of a borrow opened inside the region; the stacked views read payloads at the
outer reading), a reborrow of an `imm` view (6.150 at a resuming table), a continuation typed over
an `imm` view (the view a re-lend hands carries no record for the `Imm` clause's coherence), a stop
handled between two lenders (`AllCross` at constant `true`), and the borrow constants' frames as
machine frames at a stack (GhostEnd #275).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

section
variable {δ : LSub}

/-- **(S1) Not derived.** A borrower Core's typing derives at a resuming row, its context rebuilt
from the views at every re-lend of the stack and its answer in `[top]`, is D16.1's piece at the
stack, holding nothing of its own. -/
theorem piece_of_typed {S : Row} {σ : LStack} (_hx : AllCross σ (Row.tab S δ))
    (_hLR : LinResume (Row.tab S δ)) {ds : List Bool} {Qa : List SRec → Val → WProp}
    {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (_hd : CDerives Δ Γ M (.comp (CTy.effOf S B))) {γ : List Val}
    (_hctx : ∀ (αs : List Life) (ls : List SRec), αs.length = σ.length →
      List.IsChain (· < ·) αs → (∀ a ∈ αs, a < ⊤) → ∀ ρv, vwS δ [] σ ds αs ls ρv →
        Δ.Models (extS δ σ αs) ∧ ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧
          gDenC (ℍ := ℍ) ls (extS δ σ αs) Γ γ ρg)
    (_hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    (αi : List Life) (ls : List SRec) :
    OpenS (ℍ := ℍ) δ σ (Row.tab S δ) (cbQ δ σ Qa) σ.length ds αi [] ls (substAll γ M)
      PMap.empty := by
  sorry

/-- **Law 2, at every mixed stack.** A borrower Core's typing derives at a resuming row, holding a
mixed stack of lends open across its stops, every operation crossing every lend, its context
rebuilt from the views at every re-lend: beside the owners of the stack's lenders, it is its
`ewpTS`, the owners handed back with its answer. `fold_mixed` (D3) folds the lenders; the piece is
(S1). -/
theorem law2 {S : Row} (hLR : LinResume (Row.tab S δ)) (hL : (Row.tab S δ).Local) {β : Life}
    {σ : LStack} (hσ : MixedStack σ) (hx : AllCross σ (Row.tab S δ))
    (hP : ∀ e ∈ σ, ∀ ls w ρ, vCE (ℍ := ℍ) none true e.T ls δ w ρ → ρ.InStratum β)
    (hadm : ∀ e ∈ σ, ∀ v, e.k = .imm v → AdmWf e.T δ)
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {ds : List Bool} {bs : List Life} (hds : ds.length = σ.length) (hbs : bs.length = σ.length)
    (hβ : ∀ a ∈ bs, a ≤ β) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {B : VTy}
    (hd : CDerives Δ Γ M (.comp (CTy.effOf S B))) {γ : List Val}
    (hctx : ∀ (αs : List Life) (ls : List SRec), αs.length = σ.length →
      List.IsChain (· < ·) αs → (∀ a ∈ αs, a < ⊤) → ∀ ρv, vwS δ [] σ ds αs ls ρv →
        Δ.Models (extS δ σ αs) ∧ ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧
          gDenC (ℍ := ℍ) ls (extS δ σ αs) Γ γ ρg)
    (hQ : ∀ (αs : List Life) ls v ρ, List.IsChain (· < ·) αs →
      vCE (ℍ := ℍ) none true B ls (extS δ σ αs) v ρ → boxTop αs (Qa ls v) ρ)
    (ls : List SRec) :
    Entails (ownersM (ℍ := ℍ) δ σ ls)
      (ewpTS (ℍ := ℍ) ls (substAll γ M) (opTable (Row.tab S δ)) (withOwnersM δ σ Qa)) :=
  fun ρo ho => fold_mixed hLR hL hσ hx hP hadm Qa hQa ds bs hds hbs hβ ls _ ρo PMap.empty ρo ho
    (fun ls₁ _ => piece_of_typed hx hLR hd hctx hQ bs ls₁) (ResU.comp_empty_right ρo)

end

/-- **(S1′) Not derived.** GhostEnd's `RelendOfTyped`: every borrower typed at a resuming row is
re-lendable at one lend. -/
theorem relendOfTyped : RelendOfTyped (ℍ := ℍ) := by
  sorry

/-- **Law 2 at one lend, at the program level**: the resume rule's compatibility for the borrow
constant at a resuming row — `withbor ℓ (Λ. λm. M)` from the owner, at `F_S (Ref T ⊗ B)`.
GhostEnd's `withbor_of_relendOfTyped`; its open step is (S1′). -/
theorem law2_depth1 {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hx : Δ.find? x = none) (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false) {T B : VTy} (hT : ¬ VFree x T)
    (hB : ¬ VFree x B) {βP : Life} (hP : ∀ ls w σ, vCE (ℍ := ℍ) none true T ls δ w σ → σ.InStratum βP)
    {S : Row} (hS : Row.Resume S x) {M : Expr} (hM : closedAt 1 M = true)
    (hD : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))))
    (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vCE (ℍ := ℍ) none true T ls δ v)
      (cC (ℍ := ℍ) (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) :=
  withbor_of_relendOfTyped relendOfTyped hδ hx hbx hΔx hT hB hP hS hM hD l v ls

end Law2

end
