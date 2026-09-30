import HandlersAsBorrows.Translate
import Shifts.Shifts

/-!
# Effect safety from the Fundamental Property (theorem (b))

Ξ's effect safety (Effekt TR Theorems 4–5 and §5.2): a closed well-typed program is never stuck
on an *undelimited label*, a capability applied outside the delimiter of its handler.  In the
translation a capability is `Mut 'x S` beside its clause; applying it is `withswap` on the
borrowed state cell; its handler's delimiter is the `withbor` that lent `'x`, after which the cell
is freed.  An application outside the handler would be a `withswap` on a location that is no
longer in memory: a use of a borrow after its lifetime.

* `effect_safety`: the translation of a closed program of type `1` runs from the empty memory
  to `()` and leaves memory empty.  It is `Fig16.LogRel.Typed.adequacy` ([CONF] Lemma 3.1 with
  Corollary 3.3, at `SemX`) applied to `translate_typed`: no new semantic argument.
* `effect_safety_open`: an open statement is in the logical relation (`SemX`) at the
  environment's type: in every world where its capabilities are live borrows at their
  lifetimes, it runs safely and hands them back.  It is the Fundamental Property
  (`Fig16.LogRel.Typed.fundamentalProperty`, [TR] 6.151 at `SemX`) applied to `translate_typed`.
* `capability_not_outlives`: the capability cannot leave its handler's `['x]` box: `Mut 'x S`
  does not outlive `'x` at any satisfiable `Δ`.  This is the step of `translate_typed` where Ξ's
  second-class restriction is replaced by the outlives check of `[]I` ([TR] p. 2, rows 2.13 and
  2.37).
* `lolli_not_outlives`: no function type outlives anything ([TR] p. 2 has no outlives rule at
  `⊸`), so a closure cannot cross a `['x]` box either.

`[about ours]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace HandlersAsBorrows.Xi
open BoCa BoCa.Lifetime BoCa.Programs

/-- A closed program of the fragment, run at the empty environment: `let (r, u) = (λenv. ⟦s⟧) ();
u; r`. -/
def prog (s : Stmt) : Expr := .letpair (.app (lam (tr s)) unit') (.seq (.var 0) (.var 1))

theorem good_empty : Good 0 [] LifeCtx.empty :=
  ⟨fun x hx => absurd hx (by simp [ncaps]), fun _ _ => rfl⟩

/-- A closed program of type `1` translates to a closed BoLo program of type `1`. -/
theorem d_prog {s : Stmt} (h : XDerives [] [] s .unit) :
    DerivesWf LifeCtx.empty [] (prog s) .unit :=
  .tensorE (T₁ := .unit) (T₂ := .unit) .nil rfl
    (.lolliE .nil (.unitI .nil) (.lolliI rfl (translate_typed h 0 LifeCtx.empty good_empty)))
    (.unitE (.left (.right .nil)) (.var (.here (.cons .nil))) (.var (.there (.here .nil))))

/-- **Theorem (b), closed programs.**  The translation of every closed program of the fragment
at type `1` runs from the empty memory to `()` and leaves memory empty: no operation is ever
applied to a capability whose handler's state is gone, and every handler's state is freed. -/
theorem effect_safety {s : Stmt} (h : XDerives [] [] s .unit) :
    BoLo.Steps Adequacy.emptyMem (prog s) Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ (d_prog h)

theorem ctx_scoped {n : Nat} {K : List Entry} {Δ : LifeCtx} (hG : Good n K Δ) (Γ : Ctx VTy) :
    Ctx.ScopedB Δ (⟨EnvTy n K, true⟩ :: emb Γ) := by
  intro sl hsl _
  rcases List.mem_cons.mp hsl with rfl | hsl'
  · exact hG.scoped
  · simp only [emb, List.mem_map] at hsl'
    obtain ⟨t, _, rfl⟩ := hsl'
    exact VTy.scoped _ _

/-- **Theorem (b), open statements.**  A statement typed in the fragment is in the logical
relation at `C ⊗ EnvTy n K`: run in a world where its environment holds live `Mut` borrows at
the handlers' lifetimes, it is safe and returns the environment, still valid. -/
theorem effect_safety_open {K : List Entry} {Γ : Ctx VTy} {s : Stmt} {C : VTy}
    (h : XDerives K Γ s C) {n : Nat} {Δ : LifeCtx} (hG : Good n K Δ) (hok : Δ.Ok) :
    Fig16.LogRel.Typed.SemX Δ (⟨EnvTy n K, true⟩ :: emb Γ) (tr s) (.tensor C.tr (EnvTy n K)) :=
  Fig16.LogRel.Typed.fundamentalProperty _ _ _ _ (translate_typed h n Δ hG) hok (ctx_scoped hG Γ)

/-- `Δ ⊨ @a ⊏ @a` holds at no satisfiable `Δ`. -/
theorem not_entailsLt_self {Δ : LifeCtx} (hs : Δ.Sat) (a : Life) : ¬ Δ.EntailsLt a a := by
  intro h
  obtain ⟨δ, hδ⟩ := hs
  obtain ⟨m, n, hm, hn, hlt⟩ := h δ hδ
  rw [hm] at hn
  cases hn
  exact Nat.lt_irrefl _ hlt

/-- The capability does not outlive its own handler's lifetime, so `[]I` ([TR] p. 2, row 2.13)
refuses any context or result that still holds it at the end of the handler. -/
theorem capability_not_outlives {Δ : LifeCtx} (hs : Δ.Sat) (a : Life) (S : Ty) :
    ¬ OutlivesRules Δ a (.mut a S) := by
  intro h
  cases h with
  | «mut» hlt => exact not_entailsLt_self hs a hlt

/-- The capability object `Mut 'x S ⊗ !code` does not outlive `'x` either. -/
theorem object_not_outlives {Δ : LifeCtx} (hs : Δ.Sat) (a : Life) (S T : Ty) :
    ¬ OutlivesRules Δ a (.tensor (.mut a S) T) := by
  intro h
  cases h with
  | tensor h₁ _ => exact capability_not_outlives hs a S h₁

/-- No function type outlives anything: `[TR]` p. 2 prints no outlives rule at `⊸`. -/
theorem lolli_not_outlives {Δ : LifeCtx} (a : Life) (T₁ T₂ : Ty) :
    ¬ OutlivesRules Δ a (.lolli T₁ T₂) := by
  intro h
  cases h

/-- At a handler's lifetime, `[]I`'s premise fails for a context holding the handler's own
capability live: this is the check a would-be escaping capability meets. -/
theorem escape_refused {Δ : LifeCtx} (hs : Δ.Sat) (a : Life) (S : Ty) (Γ : Ctx Ty) :
    ¬ Ctx.Outlives Δ (⟨.mut a S, true⟩ :: Γ) a := by
  intro h
  exact capability_not_outlives hs a S (h.2 _ List.mem_cons_self rfl)

/-- `handle` uses `withbor` form (2), an instance of `experiments/Shifts`' labelled shift with
source `Ref S`, view `Mut 'x S`, the source returned. -/
theorem handle_is_shift (x : LifeVar) (bnd : Life) (S T : Ty) :
    axWithbor2Ty x bnd S T = Experiments.Shifts.shiftTy (.ref S) (fun a => .mut a S) true x bnd T :=
  Experiments.Shifts.withbor2_shift x bnd S T

end HandlersAsBorrows.Xi
