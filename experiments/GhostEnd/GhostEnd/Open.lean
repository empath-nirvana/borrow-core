import GhostEnd.Program

/-!
# GhostEnd — what is not derived, stated

Two statements are written here as `Prop`s that elaborate. Neither is proved, and I have not
verified that any obstruction to either is real.

**`RelendOfTyped`: every typed borrower is re-lendable.** It concerns a borrower `M` typed at a row
of linear resuming operations whose arguments are closed data (`Row.Resume`, the analogue of
`Row.Unwind` for the resuming forms). It asks that `M` is `Relend` at every lifetime. Given it,
`withbor_of_relendOfTyped` derives O15.1's resume half for every such borrower, through
`ewpTS_M_frameR` exactly as `withbor_spans_yields` does for straight-line ones.

`relend_chain` proves it for straight-line borrowers. There the induction is on the number of
yields left, which no lifetime affects. Two steps of a general proof are not derived:

1. **Typed stops.** At a stop of `M`'s run the remaining context `K` has to be presented as a
   typed segment closed by the frames' values (`SegOf`). That is what lets `segment_fundamental`
   re-derive `K[w]` at the fresh assignment. `ewpTS`'s stops carry the continuation's share as a
   semantic proposition at the old assignment (`contShare`), not as a typed segment.
2. **A measure fixed across re-lends.** `Relend` is a least fixed point. Each resumption runs the
   remainder under the typing instantiated at a new `δ′`, and that is a different `ewpTS` from
   the one the stop came from. So an induction on the stop's own `ewpTS` does not reach the
   re-instantiated run. A proof needs a well-founded measure on the interaction that does not
   depend on the internal lifetimes.

**`O151AsStated`: §15's statement.** It is O15.1 as `docs/effects-tr/15-mut-cell.md` prints it: 6.65
over `ewpTS` at a table with a resuming entry, with the premise's callback quantified from its
start (`fresh (λα. ℓ ↦ M_α P̂ ─⋆ ewpTS …)`). `ewpTS_M_frameR` proves the variant whose premise is
`Relend`. A stop of a callback in the stated premise owes its continuation at the `α` it began
at, and a resumption needs it at a fresh `α′` (§15, route 2). I have not derived the stated form
from the variant.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A row a borrower may yield through with its lend open: linear resuming operations, answered
at `1`, whose arguments are closed data, free of `'x` and outliving every lifetime. -/
def Row.Resume (S : Row) (x : LifeVar) : Prop :=
  ∀ o ∈ S, o.abort = false ∧ o.n ≠ 0 ∧ o.q = .lin ∧ o.B = .unit ∧ ¬ VFree x o.A ∧
    ∀ Δ a, VOutlives Δ a o.A

/-- **Not derived.** Every borrower typed at a resuming row is re-lendable. -/
def RelendOfTyped : Prop :=
  ∀ (Δ : LifeCtx) (δ : LSub) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (S : Row)
    (M : Expr), Δ.Models δ → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) → ¬ VFree x T → ¬ VFree x B →
    Row.Resume S x →
    CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    ∀ (l : BoCa.Loc) (ls : List SRec),
      Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
        PMap.empty

/-- O15.1's resume half for every typed borrower, given `RelendOfTyped`. -/
theorem withbor_of_relendOfTyped (H : RelendOfTyped) {Δ : LifeCtx} {δ : LSub}
    (hδ : Δ.Models δ) {x : LifeVar} {b : Lifetime.Life} (hx : Δ.find? x = none)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    {S : Row} (hS : Row.Resume S x) {M : Expr} (hM : closedAt 1 M = true)
    (hD : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))))
    (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (cC (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ).mpr ?_
  exact withbor_relend (Row.tab S δ) hP _ v
    (relend_lam2 (opTable_mono _) hM (H Δ δ x b T B S M hδ hx hbx hΔx hT hB hS hD l ls)) ρ hρ

/-- **Not derived.** O15.1 as §15 states it: 6.65 over `ewpTS` at a table that may resume, the
callback's premise quantified from its start. -/
def O151AsStated : Prop :=
  ∀ (T' : OpTab) (l : BoCa.Loc) (T : VTy) (δ : LSub) (β : Life),
    (∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) →
    ∀ (v : Val) (e : Expr) (ls : List SRec) (Q : List SRec → Val → WProp),
      Entails
        (ptoOwn l v ⋆ vC true T ls δ v ⋆
          fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆
            ewpTS ls e (opTable T') (fun ls'' v' =>
              box α (all fun w => ptoOwn l w ─⋆ (vC true T ls'' δ w ─⋆ Q ls'' v')))))
        (ewpTS ls e (opTable T') Q)

end GhostEnd
