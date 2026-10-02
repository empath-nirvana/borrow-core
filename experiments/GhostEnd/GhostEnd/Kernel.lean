import GhostEnd.Callee

/-!
# GhostEnd — the kernel invariant, where it enters (#262, item 4)

**The table is over resources, not types.** A closure's type does not record what it captures:
`thunk (return forget to fg. fg m)` is a `U(F 1)`, free of `'x`, and its value holds the lend's
cell in its environment (`capture_hides_lend`). So "every value whose type mentions `'x` is a
view of a cell recorded at a lifetime `⊒ 'x`" does not cover the borrower's frames: a value of a
type free of `'x` may hold the lend. `TabAt` (`Table.lean`) is stated over the resource for this
reason, and `TV` follows the cell into closures' environments by their typings.

**Where the kernel invariant is needed.** `RBodyC` reads its context as typed values. The
borrower's own `thunk` and `λ` values are typed by their derivations (`rbodyC_thunk`,
`cloL_of_rbodyC`), and its atoms by the relation. A pure piece run by `fundamentalC` answers in
the relation only. Its answer at a thunk type is a typed value only if every value a pure run
produces is a substitution instance of a typed term or a fixed axiomatic constant: the kernel
invariant (#262, item 4), stated here at a pure piece as `KernelInvariant`. Given it,
`rbodyC_retTV` reads every pure piece as an `RBodyC` piece answering a typed value.

Externs and `unsafe` are outside the verified fragment by design; `CDerives` has neither, so the
invariant is stated over it.

**Not derived.** `KernelInvariant` itself. I have not derived it and have not verified that any
obstruction is real. It is a statement about runs (a preservation property for the kernel's
machine at typed values), and `fundamentalC` does not give it, since its postconditions are the
relation's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The types whose values `TV` reads: atoms, pairs, sums and thunks. -/
def TVOk (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) : VTy → Prop
  | .tensor A B => TVOk Δ x b T A ∧ TVOk Δ x b T B
  | .sum A B => TVOk Δ x b T A ∧ TVOk Δ x b T B
  | .thunk _ => True
  | A => AtomOk Δ x b T A

/-- **Not derived.** The kernel invariant at a pure piece: from a context of typed values, every
answer at a `TVOk` type is a typed value at the same lend. -/
def KernelInvariant : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (Γ : Ctx VTy) (E : Expr)
    (A : VTy), CDerives (Δ.extend x b) Γ E (.comp (.ret A)) → TVOk Δ x b T A →
    ∀ (δ : LSub) (l : BoCa.Loc) (α : Life) (ls : List SRec) (γ : List Val) (ρ : WRes),
      (Δ.extend x b).Models (δ.extend x α) → TVG Δ x b T δ l false α Γ γ ls false ρ →
      wpTS ls (substAll γ E) (fun ls' v ρ' => TV Δ x b T δ l false α A ls' v false ρ') ρ

/-- **A pure piece answering a typed value**, given the kernel invariant. -/
theorem rbodyC_retTV (HK : KernelInvariant) {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life}
    {T : VTy} {S : Row} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ : Ctx VTy} {ml : Bool} {E : Expr} {A : VTy}
    (hD : CDerives (Δ.extend x b) (Γ ++ [mSlot x T ml]) E (.comp (.ret A)))
    (hA : TVOk Δ x b T A) : RBodyC Δ x b T S Γ ml E (ansTV Δ x b T A) := by
  intro δ hδ β hβ l α hα ls γ ρ ht hg
  have hδα := models_extend hδ hbx hΔx hβ hα
  refine bodyAtD_of_wpTS (wpTS_mono (P := fun ls' v ρ' =>
    TabAt l α ρ' ∧ TV Δ x b T δ l false α A ls' v false ρ') (Q := ansTV Δ x b T A δ l α)
    (fun _ _ _ h' => ⟨h'.2, h'.1⟩) ρ ?_)
  exact wpTS_tabAt l α ls _ _ ht (HK Δ x b T _ E A hD hA δ l α ls _ ρ hδα hg)

end GhostEnd

namespace GhostEnd.Kernel
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd.Branch (mS hT)

/-- `return forget to fg. fg m`, `m` at index `1` under the thunk's dead binder. -/
def useM : Expr := bindE forget (.app (.var 0) (.var 2))

theorem d_useM :
    CDerives Δ₁ (⟨.unit, false⟩ :: ([] ++ [mS true])) useM (.comp (.ret .unit)) :=
  .bind (.dead (.right .nil)) (.ret (.forgetMut (a := .var 0) (A := .unit) (.cons (.cons .nil))))
    (.app (.left (.dead (.right .nil))) (.force (.here (.cons (.cons .nil))))
      (.there (.there (.here .nil))))

/-- **A closure of a type free of `'x` holds the lend.** `thunk useM` is typed `U(F 1)` over
`m : Mut 'x 1`; the type does not mention `'x`, and at every lend the closure is a typed value
whose resource is the lend's cell at `ℓ`. -/
theorem capture_hides_lend (δ : LSub) (l : BoCa.Loc) (α : Life) (ls : List SRec) (ρ : WRes)
    (hv : viewP l .unit δ α ls ρ) :
    CDerives Δ₁ ([] ++ [mS true]) (.val (.lam useM)) (.val (.thunk (.ret .unit))) ∧
      ¬ VFree 0 (.thunk (.ret .unit)) ∧
      TV LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit δ l false α (.thunk (.ret .unit)) ls
        (Val.lam (Expr.psub 1 [Val.loc l] useM)) false ρ ∧
      ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = Kind.mut := by
  refine ⟨.thunkF d_useM, by simp [VFree, CFree], ?_, ?_⟩
  · exact .cloF (Γf := [] ++ [mS true]) d_useM
      (.live (.atomL (Or.inl rfl) (mutView hT hv)) .nil (by simp) (ResU.comp_empty_right ρ))
  · obtain ⟨ψ, rfl, hk⟩ := dropC_of_view hv
    exact ⟨ψ, ResU.single_get_self l ψ, hk⟩

end GhostEnd.Kernel
