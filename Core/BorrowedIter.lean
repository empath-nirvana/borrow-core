import Core.Dtor

/-!
# Core — iteration over borrowed data  `[spec §7]`

A sequence whose spine is a value and whose elements are cells,

    Seq A    ≜ μX. 1 ⊕ (Ref A ⊗ X)
    Views @a A ≜ μX. 1 ⊕ (Imm @a A ⊗ X)

is borrowed as a whole by one load: `Imm̲ @a (Seq A) = Views @a A` (`seqTy_view`), since `Imm̲`
keeps a head `X` and turns each `Ref A` into `Imm @a A`.  So `withload` on `Imm @b (Seq A)` hands
its callback every element's view at the callback's lifetime `'x`, at once.

The iterator over the views is `unfold` with the views as its state:

    iterImm : Views @a A ⊸ U(Iter (Imm @a A) 1 1)

`next` unrolls the state and yields the head view with the rest of the views, or finishes; `close`
drops the remaining views (`dtorE`: `foldOwn` whose algebra forgets each `Imm`).  The elements
are handed out at the state's own lifetime `@a`.  The term is closed and typed in `CDerives` at
every lifetime and every dead context (`iterImm_wf`), so `fundamentalC` covers it
(`iterImm_sem`).

A list linked through cells, `μX. 1 ⊕ (A ⊗ Ref X)` or the common list `μX. 1 ⊕ (Ref A ⊗ Ref X)`,
does not give this: its view `Imm̲ 'x` keeps the tail as `Imm 'x (μX. …)`, a borrow through a
pointer, which a further `withload` opens only inside a new callback at a shorter lifetime.
`SPEC.md` §7 records why an iterator whose state holds that tail cannot return it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Types -/

/-- The body of `Seq A`, `1 ⊕ (Ref A ⊗ X)`. -/
abbrev seqBody (A : VTy) : VTy := .sum .unit (.tensor (.ref A) (.tvar 0))

/-- `Seq A = μX. 1 ⊕ (Ref A ⊗ X)`: a value spine of element cells.  `[spec §7]` -/
abbrev seqTy (A : VTy) : VTy := .mu (seqBody A)

/-- The body of `Views @a A`, `1 ⊕ (Imm @a A ⊗ X)`. -/
abbrev viewsBody (a : Lifetime.Life) (A : VTy) : VTy := .sum .unit (.tensor (.imm a A) (.tvar 0))

/-- `Views @a A = μX. 1 ⊕ (Imm @a A ⊗ X)`: every element's view at one lifetime.  `[spec §7]` -/
abbrev viewsTy (a : Lifetime.Life) (A : VTy) : VTy := .mu (viewsBody a A)

/-- The iterator over the views: `Iter (Imm @a A) 1 1`. -/
abbrev iterImmC (a : Lifetime.Life) (A : VTy) : CTy := .iter (.imm a A) .unit .unit

/-- `iterImm`'s type, `Views @a A ⊸ U(Iter (Imm @a A) 1 1)`. -/
abbrev iterImmTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .lolli (viewsTy a A) (.thunk (iterImmC a A))

/-- **One load borrows every element.**  `Imm̲ @b (Seq A) = Views @b A` for a closed `A`.  `[spec §7]` -/
theorem seqTy_view (b : Lifetime.Life) {A : VTy} (hA : A.Cl 0) :
    (seqTy A).immReborrow b = viewsTy b A := by
  simp only [VTy.immReborrow, VTy.immG, VTy.subst_closed0 hA]

/-- The unrolling of `Views @a A` at a closed `A`. -/
theorem viewsTy_unroll (a : Lifetime.Life) {A : VTy} (hA : A.Cl 0) :
    VTy.inst (viewsTy a A) (viewsBody a A) = .sum .unit (.tensor (.imm a A) (viewsTy a A)) := by
  simp only [VTy.inst, VTy.subst, VTy.scons, VTy.subst_closed0 hA]

/-- `Iter (Imm @a A) 1 1` observed at the state type `S`: `F((Imm @a A ⊗ S) ⊕ 1) & F 1`. -/
theorem iterImm_instT (a : Lifetime.Life) (A S : VTy) :
    (CTy.iterBody (.imm a A) .unit .unit).instT S
      = .amp (.ret (.sum (.tensor (.imm a A) S) .unit)) (.ret .unit) :=
  CTy.iterBody_instT _ _ _ S

theorem viewsTy_hasDtor (a : Lifetime.Life) {A : VTy} (hA : A.Cl 0) : HasDtor (viewsTy a A) :=
  .mu (A := viewsBody a A) ⟨trivial, hA, trivial⟩ trivial (.sum .unit (.tensor .imm .unit))

/-! ### The terms -/

/-- The step at the state `s`:
`⟨case s {inj₁ u. inj₂ u | inj₂ p. inj₁ p}, dtor s⟩`.  Inside `withPair` the state is the
variable `2`. -/
def iterImmStepV (a : Lifetime.Life) (A : VTy) : Val :=
  .lam (withPair (.case (.var 2) (.inj₂ (.var 0)) (.inj₁ (.var 0)))
    (.app (dtorE (viewsTy a A)) (.var 2)))

/-- **`iterImm = λvs. unfold step to f. ⟨(f vs) π₁, (f vs) π₂⟩`**.  `[spec §7]` -/
def iterImmV (a : Lifetime.Life) (A : VTy) : Val :=
  .lam (elet (.app (.val (unfoldV (CTy.iterBody (.imm a A) .unit .unit)))
      (.val (iterImmStepV a A)))
    (withPair (.app (.app (.var 2) (.var 3)) (.val (.inj₁ .unit)))
      (.app (.app (.var 2) (.var 3)) (.val (.inj₂ .unit)))))

/-! ### Typing -/

section
variable {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy}

/-- The step: `!U(Views @a A ⊸ F((Imm @a A ⊗ Views @a A) ⊕ 1) & F 1)`. -/
theorem iterImmStep_wf (hA : A.Cl 0) {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (iterImmStepV a A))
      (.val (.bang (.thunk (.arr (viewsTy a A)
        ((CTy.iterBody (.imm a A) .unit .unit).instT (viewsTy a A)))))) := by
  rw [iterImm_instT a A]
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI ?_ ?_))
  · have hs : CDerives Δ (⟨.unit, false⟩ :: ⟨.sum .unit .unit, false⟩ ::
        ⟨viewsTy a A, true⟩ :: Γ) (.var 2) (.val (.sum .unit (.tensor (.imm a A) (viewsTy a A)))) := by
      have := CDerives.unroll (.var (.there (.there (.here hΓ.toP))) :
        CDerives Δ (⟨.unit, false⟩ :: ⟨.sum .unit .unit, false⟩ :: ⟨viewsTy a A, true⟩ :: Γ)
          (.var 2) (.val (viewsTy a A)))
      rwa [viewsTy_unroll a hA] at this
    exact .ret (.caseV (.dead (.dead (.left (deadSplit hΓ)))) hs
      (.sumI₂ (.var (.here (Ctx.Dead.cons (.cons (.cons hΓ))).toP)))
      (.sumI₁ (.var (.here (Ctx.Dead.cons (.cons (.cons hΓ))).toP))))
  · exact .ret (.lolliE (.dead (.dead (.left (deadSplit hΓ))))
      (.var (.there (.there (.here hΓ.toP))))
      (dtor_wf (viewsTy_hasDtor a hA) (.cons (.cons (.cons hΓ)))))

/-- `f : U(Views @a A ⊸ Iter …), vs : Views @a A ⊢ f vs`, inside `withPair`'s two binders. -/
theorem iterImm_fs {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (withCtx (⟨.thunk (.arr (viewsTy a A) (iterImmC a A)), true⟩ ::
        ⟨viewsTy a A, true⟩ :: Γ))
      (.app (.var 2) (.var 3)) (.comp (iterImmC a A)) :=
  .app (.dead (.dead (.left (.right (deadSplit hΓ)))))
    (.force (.there (.there (.here (Ctx.Dead.cons hΓ).toP))))
    (.there (.there (.there (.here hΓ.toP))))

/-- **`iterImm : Views @a A ⊸ U(Iter (Imm @a A) 1 1)`**, at every lifetime `@a` and every dead
context.  `[spec §7]` -/
theorem iterImm_wf (hA : A.Cl 0) {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (iterImmV a A)) (.val (iterImmTy a A)) := by
  have hOk := CTy.iterBody_nuOk (.imm a A) .unit .unit
  have hunf : CDerives Δ (⟨viewsTy a A, false⟩ :: Γ)
      (.app (.val (unfoldV (CTy.iterBody (.imm a A) .unit .unit))) (.val (iterImmStepV a A)))
      (.val (.thunk (.arr (viewsTy a A) (iterImmC a A)))) :=
    .bangE (.lolliE (deadSplit (.cons hΓ)) (iterImmStep_wf hA (.cons hΓ))
      (.unfoldN _ (viewsTy a A) hOk (Ctx.Dead.cons hΓ).toP))
  exact .lamV (.eletV (.right (deadSplit hΓ)) hunf
    (.thunkV rfl (.nuIn hOk (.withI (.proj₁ (.nuOut hOk (iterImm_fs hΓ)))
      (.proj₂ (.nuOut hOk (iterImm_fs hΓ)))))))

/-- The Fundamental Property at `iterImm`. -/
theorem iterImm_sem (hA : A.Cl 0) : SemV Δ [] (.val (iterImmV a A)) (iterImmTy a A) :=
  fundamentalC (iterImm_wf hA .nil)

end

end BoCa.Fig16.LogRel.Core

end
