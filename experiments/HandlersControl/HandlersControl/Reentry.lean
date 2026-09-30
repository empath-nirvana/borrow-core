import HandlersControl.Behind

/-!
# The reentry rule, and `memo`

A handler whose state sits in its frame (`Behind.lean`) runs a clause with the state token
`σ : Ref S`.  A clause **borrows** the state with `withbor σ`, which consumes `σ` for the scope of
its callback and hands it back after.  Resuming and forwarding take the state token: here the
forward is a function `fwd : Ref S ⊸ Ref S ⊗ B`.  So a borrow cannot span a forward: inside the
callback `σ` is gone, and outside the callback the borrow is over.  The reentry rule is BoLo's
linearity of `σ` and needs no new rule.

`memo` caches one answer in `S = 1 ⊕ B`:

    memo fwd (σ, ()) = let (σ, c) = get σ;                    -- borrow 1: read the cache
                       case c { none ⇒ let (σ, b) = fwd σ;    -- forward; may re-enter memo
                                        let (b₁, b₂) = dup b;
                                        let σ = insert (σ, b₁);   -- borrow 2: write the cache
                                        (σ, b₂)
                              | some v ⇒ (σ, v) }

`memo₁ = memo rec₁`, `rec₁ σ = let (σ, b) = memo₀ (σ, ()); (σ, not b)`, `memo₀ = memo base`:
the forward of `memo₁` re-enters `memo` on the same state while `memo₁`'s clause is live.

* **Accepted**: `d_memoProg`; safe (`memoProg_runs`); run twice, the second call hits
  (`memoPair_eval`: `(inj₂ (), inj₂ ())`; recomputing would answer `inj₁ ()` the second time).
* **Rejected**: `spanFwd`, one borrow spanning the forward, `withbor σ (Λ. λm. … fwd σ …)`, has no
  derivation at any `Δ`, context or type (`spanFwd_refused`): `σ` would be live in both the
  borrowed position and the callback (`no_shared_app`).

`[about ours]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace HandlersControl
open BoCa BoCa.Lifetime BoCa.Programs HandlersAsBorrows.Xi

/-- The cache `1 ⊕ B`. -/
abbrev S : Ty := .sum .unit B
/-- The state token. -/
abbrev StS : Ty := .ref S
/-- A borrow of the cache at the callback's lifetime `'0`. -/
abbrev MS : Ty := .mut (.var 0) S

theorem outlives_S (Δ : LifeCtx) (a : Life) : OutlivesRules Δ a S := .sum .unit (.sum .unit .unit)

/-! ## Data -/

def dupB : Expr := lam (.case (.var 0) (.pair (.inj₁ (.var 0)) (.inj₁ unit'))
  (.pair (.inj₂ (.var 0)) (.inj₂ unit')))

def notB : Expr := lam (.case (.var 0) (.inj₂ (.var 0)) (.inj₁ (.var 0)))

def dupS : Expr := lam (.case (.var 0) (.pair (.inj₁ (.var 0)) (.inj₁ unit'))
  (.letpair (.app dupB (.var 0)) (.pair (.inj₂ (.var 1)) (.inj₂ (.var 0)))))

def dropS : Expr := lam (.case (.var 0) (.var 0) (dropB (.var 0)))

variable {Δ : LifeCtx}

theorem d_dupB {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ dupB (.lolli B (.tensor B B)) :=
  .lolliI rfl (.sumE (T₁ := .unit) (T₂ := .unit) (.left hΓ.split) rfl (.var (.here hΓ))
    (.tensorI (.left (.dead hΓ.split)) (.sumI₁ (.var (.here (by dead)))) (.sumI₁ (.unitI (by dead))))
    (.tensorI (.left (.dead hΓ.split)) (.sumI₂ (.var (.here (by dead)))) (.sumI₂ (.unitI (by dead)))))

theorem d_notB {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ notB (.lolli B B) :=
  .lolliI rfl (.sumE (T₁ := .unit) (T₂ := .unit) (.left hΓ.split) rfl (.var (.here hΓ))
    (.sumI₂ (.var (.here (by dead)))) (.sumI₁ (.var (.here (by dead)))))

theorem d_dupS {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ dupS (.lolli S (.tensor S S)) :=
  .lolliI rfl (.sumE (T₁ := .unit) (T₂ := B) (.left hΓ.split) rfl (.var (.here hΓ))
    (.tensorI (.left (.dead hΓ.split)) (.sumI₁ (.var (.here (by dead)))) (.sumI₁ (.unitI (by dead))))
    (.tensorE (T₁ := B) (T₂ := B) (.left (.dead hΓ.split)) rfl
      (.lolliE (.left (.dead hΓ.split)) (.var (.here (by dead))) (d_dupB (by dead)))
      (.tensorI (.right (.left (.dead (.dead hΓ.split))))
        (.sumI₂ (.var (.there (.here (by dead))))) (.sumI₂ (.var (.here (by dead)))))))

theorem d_dropS {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ dropS (.lolli S .unit) :=
  .lolliI rfl (.sumE (T₁ := .unit) (T₂ := B) (.left hΓ.split) rfl (.var (.here hΓ))
    (.var (.here (by dead))) (d_dropB (by dead)))

/-! ## The two borrows -/

/-- `get σ`: borrow the cache, copy it out, end the borrow. -/
def getC : Expr :=
  lam (app2 withbor (.var 0)
    (lam (lam (.letpair (app2 withswap (.var 0) dupS) (.seq (.app forget (.var 1)) (.var 0))))))

/-- `insert (σ, b)`: borrow the cache, store `some b`, end the borrow. -/
def insC : Expr :=
  lam (.letpair (.var 0)
    (.letpair (app2 withbor (.var 1)
        (lam (lam (.letpair
          (app2 withswap (.var 0) (lam (.seq (.app dropS (.var 0)) (.pair (.inj₂ (.var 3)) unit'))))
          (.seq (.app forget (.var 1)) (.seq (.var 0) unit'))))))
      (.seq (.var 0) (.var 1))))

theorem wb2 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (T₂ : Ty)
    (h : (axWithbor2Ty 0 LifeCtx.empty.meetOfDom S T₂).scopedB LifeCtx.empty = true) :
    DerivesWf LifeCtx.empty Γ withbor (axWithbor2Ty 0 LifeCtx.empty.meetOfDom S T₂) :=
  .withbor2Ax hΓ 0 rfl ⟨.top, LifeCtx.defines_of_wf rfl, outlives_S _ _⟩ h

theorem d_getC {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf LifeCtx.empty Γ getC (.lolli StS (.tensor StS S)) := by
  refine .lolliI rfl (.lolliE (.right hΓ.split)
    (.allI (S := .unit) rfl rfl (Ctx.Dead.noBinds (by dead) 0) (.lolliI rfl ?_))
    (.lolliE (.left hΓ.split) (.var (.here hΓ)) (wb2 (by dead) S rfl)))
  -- ctx: m, _, σ
  refine .tensorE (T₁ := MS) (T₂ := S) (.left (.dead (.dead hΓ.split))) rfl
    (.lolliE (.right (.dead (.dead hΓ.split))) (d_dupS (by dead))
      (.lolliE (.left (.dead (.dead hΓ.split))) (.var (.here (by dead))) (.withswapAx (by dead)))) ?_
  -- ctx: c, m', m, _, σ
  exact .unitE (.right (.left (.dead (.dead (.dead hΓ.split)))))
    (.lolliE (.dead (.left (.dead (.dead (.dead hΓ.split))))) (.var (.there (.here (by dead))))
      (.forgetMutAx (by dead)))
    (.boxIctx (.var (.here (by dead)))
      (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) (outlives_S _ _) (by dead)))

theorem noBinds_cons {x : LifeVar} {T : Ty} {b : Bool} {Γ : Ctx Ty} (hT : T.bindsB x = false)
    (h : ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false) :
    ∀ s ∈ (⟨T, b⟩ :: Γ), s.live = true → s.ty.bindsB x = false := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact hT
  · exact h s hs' hl

theorem d_insC {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf LifeCtx.empty Γ insC (.lolli (.tensor StS B) StS) := by
  refine .lolliI rfl (.tensorE (T₁ := StS) (T₂ := B) (.left hΓ.split) rfl (.var (.here hΓ)) ?_)
  -- ctx: b, σ, p
  refine .tensorE (T₁ := StS) (T₂ := .unit) (.left (.left (.dead hΓ.split))) rfl ?_
    (.unitE (.left (.right (.dead (.dead (.dead hΓ.split)))))
      (.var (.here (by dead))) (.var (.there (.here (by dead)))))
  refine .lolliE (.left (.right (.dead hΓ.split)))
    (.allI (S := .unit) rfl rfl
      (noBinds_cons rfl (noBinds_cons rfl (noBinds_cons rfl (Ctx.Dead.noBinds hΓ 0))))
      (.lolliI rfl ?_))
    (.lolliE (.dead (.left (.dead hΓ.split))) (.var (.there (.here (by dead))))
      (wb2 (by dead) .unit rfl))
  -- ctx: m, _, b, σ, p
  refine .tensorE (T₁ := MS) (T₂ := .unit) (.left (.dead (.left (.dead (.dead hΓ.split))))) rfl
    (.lolliE (.right (.dead (.left (.dead (.dead hΓ.split)))))
      (.lolliI rfl
        (.unitE (.left (.dead (.dead (.right (.dead (.dead hΓ.split))))))
          (.lolliE (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))
            (.var (.here (by dead))) (d_dropS (by dead)))
          (.tensorI (.dead (.dead (.dead (.left (.dead (.dead hΓ.split))))))
            (.sumI₂ (.var (.there (.there (.there (.here (by dead)))))))
            (.unitI (by dead)))))
      (.lolliE (.left (.dead (.dead (.dead (.dead hΓ.split))))) (.var (.here (by dead)))
        (.withswapAx (by dead)))) ?_
  -- ctx: u, m', m, _, b, σ, p
  exact .unitE (.right (.left (.dead (.dead (.dead (.dead (.dead hΓ.split)))))))
    (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split)))))))
      (.var (.there (.here (by dead)))) (.forgetMutAx (by dead)))
    (.unitE (.left (.dead (.dead (.dead (.dead (.dead (.dead hΓ.split)))))))
      (.var (.here (by dead)))
      (.boxIctx (.unitI (by dead)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead))))

/-! ## `memo` -/

/-- The clause of `memo`, forwarding to `fwd` on a miss. -/
def memo (fwd : Expr) : Expr :=
  lam (.letpair (.var 0) (.seq (.var 0) (.letpair (.app getC (.var 1))
    (.case (.var 0)
      (.seq (.var 0) (.letpair (.app fwd (.var 2)) (.letpair (.app dupB (.var 0))
        (elet (.app insC (.pair (.var 3) (.var 1))) (.pair (.var 0) (.var 1))))))
      (.pair (.var 2) (.var 0))))))

/-- A forward's type: it takes the state token. -/
abbrev FwdTy : Ty := .lolli StS (.tensor StS B)

theorem d_memo {fwd : Expr}
    (hf : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → DerivesWf LifeCtx.empty Γ fwd FwdTy)
    {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf LifeCtx.empty Γ (memo fwd) (.lolli (.tensor StS .unit) (.tensor StS B)) := by
  refine .lolliI rfl (.tensorE (T₁ := StS) (T₂ := .unit) (.left hΓ.split) rfl (.var (.here hΓ)) ?_)
  -- ctx: u, σ, p
  refine .unitE (.left (.right (.dead hΓ.split))) (.var (.here (by dead))) ?_
  refine .tensorE (T₁ := StS) (T₂ := S) (.dead (.left (.dead hΓ.split))) rfl
    (.lolliE (.dead (.left (.dead hΓ.split))) (.var (.there (.here (by dead)))) (d_getC (by dead))) ?_
  -- ctx: c, σ1, u, σ, p
  refine .sumE (T₁ := .unit) (T₂ := B) (.left (.right (.dead (.dead (.dead hΓ.split))))) rfl
    (.var (.here (by dead))) ?_
    (.tensorI (.right (.dead (.left (.dead (.dead (.dead hΓ.split))))))
      (.var (.there (.there (.here (by dead))))) (.var (.here (by dead))))
  -- miss. ctx: n, c, σ1, u, σ, p
  refine .unitE (.left (.dead (.right (.dead (.dead (.dead hΓ.split)))))) (.var (.here (by dead))) ?_
  refine .tensorE (T₁ := StS) (T₂ := B) (.dead (.dead (.left (.dead (.dead (.dead hΓ.split))))))
    rfl (.lolliE (.dead (.dead (.left (.dead (.dead (.dead hΓ.split))))))
      (.var (.there (.there (.here (by dead))))) (hf (by dead))) ?_
  -- the forward has run.  ctx: b, σ2, n, c, σ1, u, σ, p
  refine .tensorE (T₁ := B) (T₂ := B)
    (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
    rfl (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
      (.var (.here (by dead))) (d_dupB (by dead))) ?_
  -- ctx: b2, b1, b, σ2, n, c, σ1, u, σ, p
  exact .lolliE (T₁ := StS)
    (.right (.left (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))))
    (.lolliE (.dead (.left (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))))
      (.tensorI (.dead (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))))
        (.var (.there (.there (.there (.here (by dead)))))) (.var (.there (.here (by dead)))))
      (d_insC (by dead)))
    (.lolliI rfl (.tensorI
      (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.dead hΓ.split)))))))))))
      (.var (.here (by dead))) (.var (.there (.here (by dead))))))

/-- The forward of `memo₀`: the base computation. -/
def base : Expr := lam (.pair (.var 0) (.inj₁ unit'))

theorem d_base {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf LifeCtx.empty Γ base FwdTy :=
  .lolliI rfl (.tensorI (.left hΓ.split) (.var (.here hΓ)) (.sumI₁ (.unitI (by dead))))

def memo₀ : Expr := memo base

/-- The forward of `memo₁`: it re-enters `memo` on the same state. -/
def rec₁ : Expr :=
  lam (.letpair (.app memo₀ (.pair (.var 0) unit')) (.pair (.var 1) (.app notB (.var 0))))

theorem d_rec₁ {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf LifeCtx.empty Γ rec₁ FwdTy :=
  .lolliI rfl (.tensorE (T₁ := StS) (T₂ := B) (.left hΓ.split) rfl
    (.lolliE (.left hΓ.split) (.tensorI (.left hΓ.split) (.var (.here hΓ)) (.unitI (by dead)))
      (d_memo (fun h => d_base h) (by dead)))
    (.tensorI (.right (.left (.dead hΓ.split))) (.var (.there (.here (by dead))))
      (.lolliE (.left (.dead (.dead hΓ.split))) (.var (.here (by dead))) (d_notB (by dead)))))

def memo₁ : Expr := memo rec₁

/-- Two calls of `memo₁` on one cache, answering both results. -/
def memoPair : Expr :=
  elet (.app alloc' (.inj₁ unit'))
    (.letpair (.app memo₁ (.pair (.var 0) unit'))
      (.letpair (.app memo₁ (.pair (.var 1) unit'))
        (.seq (.app dropS (.app free' (.var 1))) (.pair (.var 2) (.var 0)))))

theorem d_memoPair : DerivesWf LifeCtx.empty [] memoPair (.tensor B B) := by
  refine .lolliE (T₁ := StS) .nil (.lolliE .nil (.sumI₁ (.unitI .nil)) (.allocAx .nil)) (.lolliI rfl ?_)
  -- ctx: σ
  refine .tensorE (T₁ := StS) (T₂ := B) (.left .nil) rfl
    (.lolliE (.left .nil) (.tensorI (.left .nil) (.var (.here .nil)) (.unitI (by dead)))
      (d_memo (fun h => d_rec₁ h) (by dead))) ?_
  -- ctx: r1, σ1, σ
  refine .tensorE (T₁ := StS) (T₂ := B) (.right (.left (.dead .nil))) rfl
    (.lolliE (.dead (.left (.dead .nil)))
      (.tensorI (.dead (.left (.dead .nil))) (.var (.there (.here (by dead)))) (.unitI (by dead)))
      (d_memo (fun h => d_rec₁ h) (by dead))) ?_
  -- ctx: r2, σ2, r1, σ1, σ
  exact .unitE (.right (.left (.right (.dead (.dead .nil)))))
    (.lolliE (.dead (.left (.dead (.dead (.dead .nil)))))
      (.lolliE (.dead (.left (.dead (.dead (.dead .nil))))) (.var (.there (.here (by dead))))
        (.freeAx (by dead)))
      (d_dropS (by dead)))
    (.tensorI (.right (.dead (.left (.dead (.dead .nil)))))
      (.var (.there (.there (.here (by dead))))) (.var (.here (by dead))))

/-- The program at `1`. -/
def memoProg : Expr := .letpair memoPair (.seq (dropB (.var 1)) (dropB (.var 0)))

theorem d_memoProg : DerivesWf LifeCtx.empty [] memoProg .unit :=
  .tensorE (T₁ := B) (T₂ := B) .nil rfl d_memoPair
    (.unitE (.right (.left .nil))
      (.sumE (T₁ := .unit) (T₂ := .unit) (.dead (.left .nil)) rfl (.var (.there (.here .nil)))
        (.var (.here (by dead))) (.var (.here (by dead))))
      (d_dropB (by dead)))

/-- **Accepted, and safe** by the Fundamental Property. -/
theorem memoProg_runs : BoLo.Steps Adequacy.emptyMem memoProg Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_memoProg

theorem memoProg_eval : unitNoLeak (eval memoProg) = true := by decide

/-- **Run**: the first call misses, forwards (re-entering `memo₀`), and caches `inj₂ ()`; the
second call hits. -/
theorem memoPair_eval :
    (match eval memoPair with
      | .value ⟨.pair (.inj₂ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ## The rejected clause -/

/-- No typed application has a variable free in both the function and the argument. -/
theorem no_shared_app {Δ : LifeCtx} {Γ : Ctx Ty} {f a : Expr} {T : Ty} {i : Nat}
    (h : DerivesWf Δ Γ (.app f a) T) (h₁ : occ i f = true) (h₂ : occ i a = true) : False := by
  generalize hp : Expr.app f a = e at h
  induction h with
  | lolliE hs d₁ d₂ _ _ =>
      cases hp
      exact hs.not_both (liveAt_of_occ d₁ h₂) (liveAt_of_occ d₂ h₁)
  | allE _ _ _ =>
      cases hp
      simp [occ, Expr.val, Val.unit] at h₂
  | boxIctx _ _ ih => exact ih hp
  | boxE _ ih => exact ih hp
  | immSub _ _ ih => exact ih hp
  | mutSub _ _ ih => exact ih hp
  | bangE _ ih => exact ih hp
  | _ => cases hp

/-- One borrow spanning the forward: `withbor σ (Λ. λm. let (σ′, b) = fwd σ; …)`, with `σ` the
variable `0` and the forward `fwd` any code. -/
def spanFwd (fwd rest : Expr) : Expr :=
  app2 withbor (.var 0) (lam (lam (.letpair (.app fwd (.var 2)) rest)))

/-- **Rejected**, at every `Δ`, context, type and forward. -/
theorem spanFwd_refused (Δ : LifeCtx) (Γ : Ctx Ty) (T : Ty) (fwd rest : Expr) :
    ¬ DerivesWf Δ Γ (spanFwd fwd rest) T := by
  intro h
  exact no_shared_app (i := 0) h (by simp [occ])
    (by simp [occ, lam])

/-- The obstruction, elaborated: a typing of a borrow that spans the forward. -/
def BorrowSpansForward : Prop := ∃ Δ Γ T fwd rest, DerivesWf Δ Γ (spanFwd fwd rest) T

theorem not_borrowSpansForward : ¬ BorrowSpansForward :=
  fun ⟨Δ, Γ, T, fwd, rest, h⟩ => spanFwd_refused Δ Γ T fwd rest h

end HandlersControl
