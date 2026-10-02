import GhostEnd.Typed

/-!
# GhostEnd — general typed borrowers: the reduction, and the step not derived

`RelendOfTyped` (`Open.lean`) asks that every borrower typed at a resuming row is `Relend`.
`relend_of_rbody` (`Typed.lean`) proves it for every borrower `RBody` reads. So
`RelendOfTyped` reduces to the fundamental lemma for `RBody`, `RBodyOfTyped`: every typed piece of
a borrower is an `RBody` piece. `relendOfTyped_of_rbodyOfTyped` is that reduction, with the bound
`@bδ` defined (added: `RelendOfTyped` does not carry it, and `Relend`'s `И` needs a bound).

The measure such a proof needs is the typing derivation: each rule's `RBody` from its premises',
as `rbody_ret`, `rbody_perform`, `rbody_letF`, `rbody_seq` and `rbody_case` are proved. Stops'
continuations are composed by `open_bind`, by induction on `Open`. Neither mentions a lifetime.

**Not derived.** `RBodyOfTyped` itself. The rules above cover every computation built by
`[ret]`, `[perform]`, `[let]`, `1E` and `+E` around the yields. Two kinds of step remain:

* **A frame spanning a stop whose values mention `'x`, other than `m` itself.** `rbody_letF`
  needs `FrameThaws` of the frame. It is derived for `StopSafe` frames (`stopSafe_thaws`): every
  live slot but `m` free of `'x` and outliving it. A frame holding `m` threaded through a value
  (`z : Mut 'x T ⊗ D`), or a closure that captures `m`, is outside it. The evident difficulty,
  not verified to be an obstruction: thawing a `Mut 'x T` slot at the fresh lend uses the view
  of the slot's location, and `FrameThaws` is stated at every closing substitution, which does
  not record that the location is `ℓ`. For a closure the thaw is the closure's relation at the
  fresh lend, which is O15.2.
* **Rules whose premises are effectful functions**: `[lam]`, `[app]`, `[force]`, `∀E` at a row,
  `[then]`, `[handle]` inside the borrower, and the borrow constants (nested lends). Each needs a
  relation for values of `U`, `→` and `∀` types read with the lend re-lendable. The loop of
  `Loop.lean` (`bounded_fix`) is proved directly, by induction on its budget, for that reason.

I have not derived these steps and have not verified that any obstruction is real.

**#262.** The first kind is closed for data in `TypedD.lean` (`RBodyT`, with `FrameThawsD` from
`lok_thaws`), and for closures the borrower builds in `ClosureBody.lean` (`RBodyC`, by
`tv_freeze` and `tv_thaw`, each closure re-derived by `fundamentalC`). Of the second kind,
`[lam]` and `[app]` at an effectful arrow are `cloL_of_rbodyC` and `cloL_call` (`Callee.lean`).
`RBodyTOfTyped` is the fundamental lemma for `RBodyT`, and `relendOfTyped_of_rbodyTOfTyped`
reduces `RelendOfTyped` to it. `KernelInvariant` (`Kernel.lean`) is where the kernel
invariant enters.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Not derived.** The fundamental lemma for `RBody`: every piece of a borrower, typed at a
resuming row in a context ending in the borrow, is an `RBody` piece. -/
def RBodyOfTyped : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (S : Row) (Γ : Ctx VTy)
    (ml : Bool) (E : Expr) (A : VTy),
    Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) → ¬ VFree x T → Row.Resume S x →
    CDerives (Δ.extend x b) (Γ ++ [mSlot x T ml]) E (.comp (CTy.effOf S A)) →
    RBody Δ x b T S Γ ml E A

/-- **`RelendOfTyped` from `RBodyOfTyped`**, at a defined bound. -/
theorem relendOfTyped_of_rbodyOfTyped (H : RBodyOfTyped) :
    ∀ (Δ : LifeCtx) (δ : LSub) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (S : Row)
      (M : Expr), Δ.Models δ → (∃ β, b.interp δ = some β) → Δ.find? x = none →
      b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
      ¬ VFree x T → ¬ VFree x B → Row.Resume S x →
      CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
        (.comp (CTy.effOf S (.box (.var x) B))) →
      ∀ (l : BoCa.Loc) (ls : List SRec),
        Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
          PMap.empty := by
  intro Δ δ x b T B S M hδ ⟨β, hβ⟩ hx hbx hΔx hT hB hS hD l ls
  exact relend_of_rbody hT hB hδ hβ (H Δ x b T S [] true M _ hx hbx hΔx hT hS hD) l ls

end GhostEnd
