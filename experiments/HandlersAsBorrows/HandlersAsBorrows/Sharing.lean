import HandlersAsBorrows.Safety

/-!
# Aliased stateful capabilities: what the borrow encoding refuses

System C (Brachthäuser, Schuster, Lee & Boruch-Gruszecki, OOPSLA 2022) lets one capability be
captured by several blocks at once, and a boxed block be duplicated.  With the capability a
`Mut` borrow of the handler's state, two closures that capture it are two live owners of one
unique borrow.  `DerivesWf` refuses them: a variable free in both components of a pair is live
in both halves of a `Ctx.Split`, which no split allows (`no_shared_pair`).

`twoBlocks` is the System C program

    try { f ⇒ (box {f} { () ⇒ f(()) }, box {f} { () ⇒ f(()) }) } with …

read through the encoding: two closures, each performing the operation on the same capability
`m` (de Bruijn `0`).  `twoBlocks_refused`: it has no `DerivesWf` derivation, at any `Δ`, any
context and any type.  The fragment of `Source.lean` still lets several blocks *use* one
capability (`Examples.lean`, `sharedUse`): a block does not capture the capability, it receives
the environment at each call, so uses are sequenced by the threading.

`[about ours]`
-/

noncomputable section

namespace HandlersAsBorrows.Xi
open BoCa BoCa.Lifetime BoCa.Programs

/-- `occ i e`: the variable `i` occurs free in `e`. -/
def occ (i : Nat) : Expr → Bool
  | .var j => i == j
  | .unit => false
  | .pair a b => occ i a || occ i b
  | .inj₁ e => occ i e
  | .inj₂ e => occ i e
  | .lam b => occ (i + 1) b
  | .loc _ => false
  | .prim _ => false
  | .seq a b => occ i a || occ i b
  | .letpair a b => occ i a || occ (i + 2) b
  | .case e a b => occ i e || occ (i + 1) a || occ (i + 1) b
  | .app f a => occ i f || occ i a

/-- `Γ`'s slot `i` is live. -/
def LiveAt (Γ : Ctx Ty) (i : Nat) : Prop := ∃ T, Γ[i]? = some ⟨T, true⟩

theorem liveAt_cons {s : Slot Ty} {Γ : Ctx Ty} {i : Nat} :
    LiveAt (s :: Γ) (i + 1) ↔ LiveAt Γ i := by
  simp [LiveAt]

theorem _root_.BoCa.Ctx.Dead.not_liveAt {Γ : Ctx Ty} (h : Ctx.Dead Γ) (i : Nat) : ¬ LiveAt Γ i := by
  induction h generalizing i with
  | nil => rintro ⟨T, hT⟩; simp at hT
  | cons _ ih =>
      rintro ⟨T, hT⟩
      cases i with
      | zero => simp at hT
      | succ i => exact ih i ⟨T, by simpa using hT⟩

theorem _root_.BoCa.Ctx.Solo.liveAt {Γ : Ctx Ty} {j : Nat} {T : Ty} (h : Ctx.Solo Γ j T) {i : Nat}
    (hij : i = j) : LiveAt Γ i := by
  subst hij
  induction h with
  | here _ => exact ⟨_, rfl⟩
  | there _ ih => exact liveAt_cons.mpr ih

theorem _root_.BoCa.Ctx.Split.liveAt_left {Γ Γ₁ Γ₂ : Ctx Ty} (h : Ctx.Split Γ Γ₁ Γ₂) :
    ∀ {i}, LiveAt Γ₁ i → LiveAt Γ i := by
  induction h with
  | nil => intro i hi; exact hi
  | left _ ih => intro i hi; cases i with
    | zero => exact ⟨_, rfl⟩
    | succ i => exact liveAt_cons.mpr (ih (liveAt_cons.mp hi))
  | right _ ih => intro i hi; cases i with
    | zero => obtain ⟨T, hT⟩ := hi; simp at hT
    | succ i => exact liveAt_cons.mpr (ih (liveAt_cons.mp hi))
  | dead _ ih => intro i hi; cases i with
    | zero => obtain ⟨T, hT⟩ := hi; simp at hT
    | succ i => exact liveAt_cons.mpr (ih (liveAt_cons.mp hi))

theorem _root_.BoCa.Ctx.Split.liveAt_right {Γ Γ₁ Γ₂ : Ctx Ty} (h : Ctx.Split Γ Γ₁ Γ₂) {i : Nat}
    (hi : LiveAt Γ₂ i) : LiveAt Γ i :=
  BoCa.Ctx.Split.liveAt_left (split_symm h) hi

/-- No slot is live in both halves of a split. -/
theorem _root_.BoCa.Ctx.Split.not_both {Γ Γ₁ Γ₂ : Ctx Ty} (h : Ctx.Split Γ Γ₁ Γ₂) :
    ∀ {i}, LiveAt Γ₁ i → LiveAt Γ₂ i → False := by
  induction h with
  | nil => intro i h₁ _; obtain ⟨T, hT⟩ := h₁; simp at hT
  | left _ ih => intro i h₁ h₂; cases i with
    | zero => obtain ⟨T, hT⟩ := h₂; simp at hT
    | succ i => exact ih (liveAt_cons.mp h₁) (liveAt_cons.mp h₂)
  | right _ ih => intro i h₁ h₂; cases i with
    | zero => obtain ⟨T, hT⟩ := h₁; simp at hT
    | succ i => exact ih (liveAt_cons.mp h₁) (liveAt_cons.mp h₂)
  | dead _ ih => intro i h₁ h₂; cases i with
    | zero => obtain ⟨T, hT⟩ := h₁; simp at hT
    | succ i => exact ih (liveAt_cons.mp h₁) (liveAt_cons.mp h₂)

theorem occ_closed_swap (i : Nat) : occ i swap = false := by
  simp [occ, swap, lam2, elet, v0, v1, v2, load', store']
theorem occ_closed_copy (i : Nat) : occ i copy = false := by simp [occ, copy, v0]
theorem occ_closed_forget (i : Nat) : occ i forget = false := by simp [occ, forget, unit']
theorem occ_closed_withbor (i : Nat) : occ i withbor = false := by
  simp [occ, withbor, lam2, v0, v1, unit']
theorem occ_closed_withload (i : Nat) : occ i withload = false := by
  simp [occ, withload, lam2, v0, v1, unit', load']
theorem occ_closed_withswap (i : Nat) : occ i withswap = false := by
  simp [occ, withswap, lam2, v0, v1, v3, load', store']

/-- A variable that occurs free in a typed term is live in its context. -/
theorem liveAt_of_occ {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (h : DerivesWf Δ Γ e T) :
    ∀ {i}, occ i e = true → LiveAt Γ i := by
  induction h with
  | var hs => intro i hi; exact hs.liveAt (by simpa [occ] using hi)
  | unitI _ => intro i hi; simp [occ] at hi
  | unitE hs _ _ ih₁ ih₂ =>
      intro i hi; simp only [occ, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact hs.liveAt_left (ih₁ hi)
      · exact hs.liveAt_right (ih₂ hi)
  | tensorI hs _ _ ih₁ ih₂ =>
      intro i hi; simp only [occ, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact hs.liveAt_left (ih₁ hi)
      · exact hs.liveAt_right (ih₂ hi)
  | tensorE hs _ _ _ ihp ihb =>
      intro i hi; simp only [occ, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact hs.liveAt_left (ihp hi)
      · exact hs.liveAt_right (liveAt_cons.mp (liveAt_cons.mp (ihb hi)))
  | sumI₁ _ ih => intro i hi; exact ih hi
  | sumI₂ _ ih => intro i hi; exact ih hi
  | sumE hs _ _ _ _ ih₀ ih₁ ih₂ =>
      intro i hi; simp only [occ, Bool.or_eq_true] at hi
      rcases hi with (hi | hi) | hi
      · exact hs.liveAt_left (ih₀ hi)
      · exact hs.liveAt_right (liveAt_cons.mp (ih₁ hi))
      · exact hs.liveAt_right (liveAt_cons.mp (ih₂ hi))
  | lolliI _ _ ih => intro i hi; exact liveAt_cons.mp (ih hi)
  | lolliE hs _ _ iha ihf =>
      intro i hi; simp only [occ, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact hs.liveAt_right (ihf hi)
      · exact hs.liveAt_left (iha hi)
  | allI _ _ _ _ ih => intro i hi; exact liveAt_cons.mp (ih hi)
  | allE _ _ ih =>
      intro i hi; simp only [occ, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact ih hi
      · simp [occ, Expr.val, Val.unit] at hi
  | boxIctx _ _ ih => exact ih
  | boxE _ ih => exact ih
  | immSub _ _ ih => exact ih
  | mutSub _ _ ih => exact ih
  | allocAx _ => intro i hi; simp [occ] at hi
  | freeAx _ => intro i hi; simp [occ] at hi
  | swapAx _ => intro i hi; simp [occ_closed_swap] at hi
  | copyAx _ => intro i hi; simp [occ_closed_copy] at hi
  | forgetImmAx _ => intro i hi; simp [occ_closed_forget] at hi
  | forgetMutAx _ => intro i hi; simp [occ_closed_forget] at hi
  | forgetUnkAx _ => intro i hi; simp [occ_closed_forget] at hi
  | withbor1Ax _ _ _ _ => intro i hi; simp [occ_closed_withbor] at hi
  | withbor2Ax _ _ _ _ _ => intro i hi; simp [occ_closed_withbor] at hi
  | withbor3Ax _ _ _ _ => intro i hi; simp [occ_closed_withbor] at hi
  | withloadAx _ _ _ _ => intro i hi; simp [occ_closed_withload] at hi
  | withswapAx _ => intro i hi; simp [occ_closed_withswap] at hi
  | bangLamI _ _ _ ih => intro i hi; exact liveAt_cons.mp (ih hi)
  | bangAllI _ _ _ _ _ ih => intro i hi; exact liveAt_cons.mp (ih hi)
  | bangE _ ih => exact ih
  | copyBangAx _ => intro i hi; simp [occ_closed_copy] at hi
  | forgetBangAx _ => intro i hi; simp [occ_closed_forget] at hi

/-- **No sharing.**  No typed pair has a variable free in both components. -/
theorem no_shared_pair {Δ : LifeCtx} {Γ : Ctx Ty} {e₁ e₂ : Expr} {T : Ty} {i : Nat}
    (h : DerivesWf Δ Γ (.pair e₁ e₂) T) (h₁ : occ i e₁ = true) (h₂ : occ i e₂ = true) : False := by
  generalize hp : Expr.pair e₁ e₂ = e at h
  induction h with
  | tensorI hs d₁ d₂ _ _ =>
      cases hp
      exact hs.not_both (liveAt_of_occ d₁ h₁) (liveAt_of_occ d₂ h₂)
  | boxIctx _ _ ih => exact ih hp
  | boxE _ ih => exact ih hp
  | immSub _ _ ih => exact ih hp
  | mutSub _ _ ih => exact ih hp
  | bangE _ ih => exact ih hp
  | _ => cases hp

/-- System C's `(box {f} {() ⇒ f(())}, box {f} {() ⇒ f(())})` through the encoding: two
closures that each perform the operation on the same capability (the environment, `0`). -/
def twoBlocks : Expr :=
  .pair (lam (.app (opAt 0) (.pair unit' (.var 1)))) (lam (.app (opAt 0) (.pair unit' (.var 1))))

/-- **The aliased stateful capability is refused**, at every `Δ`, context and type. -/
theorem twoBlocks_refused (Δ : LifeCtx) (Γ : Ctx Ty) (T : Ty) : ¬ DerivesWf Δ Γ twoBlocks T := by
  intro h
  exact no_shared_pair (i := 0) h (by simp [occ, opAt, atIdx, opHere, lam, app2])
    (by simp [occ, opAt, atIdx, opHere, lam, app2])

/-- The obstruction as a proposition: some typing of `twoBlocks`.  It elaborates, and
`twoBlocks_refused` refutes it. -/
def SharedCapture : Prop := ∃ Δ Γ T, DerivesWf Δ Γ twoBlocks T

theorem not_sharedCapture : ¬ SharedCapture := fun ⟨Δ, Γ, T, h⟩ => twoBlocks_refused Δ Γ T h

end HandlersAsBorrows.Xi
