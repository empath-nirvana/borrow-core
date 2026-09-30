import HandlersControl.Tac

/-!
# State behind control: two blocks share one stateful handler

`HandlersAsBorrows` makes a capability the handler's state, `Mut 'x S`, and so refuses two
closures that capture one capability (`not_sharedCapture`).  Here the state stays in the
**handler's frame**, an owned `Ref S` that only the handler touches, and an operation is a
**shift into that frame**: the caller hands the handler its argument and its continuation, as data,
and the handler updates the state and resumes.  The capability carries no resource at all.

    op   = λp. inj₂ p                                  -- the request: (argument, continuation)
    f    = !λp. op p          g = !λp. op p            -- two blocks, both performing `flip`
    body = f ((), λa. g ((), λb. (a, b)))              -- the rest of the computation, as `⊸`
    hS n = λ(c, σ). case c { r ⇒ (r, σ)                -- done
                           | (u, k) ⇒ u; let (σ, b) = flip σ; n (k b, σ) }   -- handle, resume
    prog = let σ = alloc (inj₁ ()); let (r, σ) = hS (hS id) (body, σ); drop (free σ); r

`flip σ` swaps the frame's cell: it answers the old state and stores its negation.  Typed
(`d_progU`), safe by the Fundamental Property through adequacy (`progU_runs`), and run: the second
block sees the state the first one left (`progP_eval`: `(inj₁ (), inj₂ ())`).

**Where it stops.**  The computation type is unrolled by the number of operations,
`C₀ = R`, `Cₙ₊₁ = R ⊕ (1 ⊗ (B ⊸ Cₙ))`, so each operation site has its own type and the two blocks
are two closed programs typed at two types.  One capability at one type, used at an unbounded
number of sites, needs a type `X = R ⊕ (A ⊗ (B ⊸ X))`, and BoLo's types have none
(`no_uniform_comp`).  That needs either `μX` with `X` under `⊸` (theory index T15, #182) or a native
capture construct (`README.md` §2, K-a).

`[about ours]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace HandlersControl
open BoCa BoCa.Lifetime BoCa.Programs

/-! ## Types -/

/-- The result of the handled computation, `B ⊗ B`. -/
abbrev R : Ty := .tensor B B
/-- The frame's state, an owned cell. -/
abbrev St : Ty := .ref B
/-- `Cₙ₊₁ = R ⊕ (1 ⊗ (B ⊸ Cₙ))`: a computation that performs at most `n + 1` more operations. -/
abbrev Cs (X : Ty) : Ty := .sum R (.tensor .unit (.lolli B X))
abbrev C1 : Ty := Cs R
abbrev C2 : Ty := Cs C1

/-- **No uniform computation type.**  No BoLo type solves `X = R ⊕ (A ⊗ (B ⊸ X))`: the free model
of one operation, which a single capability type used at unboundedly many sites would need. -/
theorem no_uniform_comp (R A B X : Ty) : X ≠ .sum R (.tensor A (.lolli B X)) := by
  intro h
  have := congrArg sizeOf h
  simp at this
  omega

/-! ## Closed code -/

/-- The request `op = λp. inj₂ p`. -/
def opC : Expr := lam (.inj₂ (.var 0))

/-- A block performing the operation: `λp. op p`. -/
def blk : Expr := lam (.app opC (.var 0))

/-- `flip σ`: swap the frame's cell; answer the old state, store its negation. -/
def flipOn : Expr :=
  lam (.letpair (app2 swap (.var 0) unit')
    (.case (.var 0)
      (.letpair (app2 swap (.var 2) (.inj₂ (.var 0))) (.seq (.var 0) (.pair (.var 1) (.inj₁ unit'))))
      (.letpair (app2 swap (.var 2) (.inj₁ (.var 0))) (.seq (.var 0) (.pair (.var 1) (.inj₂ unit'))))))

/-- One handler step. -/
def hS (next : Expr) : Expr :=
  lam (.letpair (.var 0) (.case (.var 1) (.pair (.var 0) (.var 1))
    (.letpair (.var 0) (.seq (.var 1)
      (.letpair (.app flipOn (.var 3)) (.app next (.pair (.app (.var 2) (.var 0)) (.var 1))))))))

/-- The handler after the last operation. -/
def h0 : Expr := lam (.var 0)

variable {Δ : LifeCtx}

theorem d_blk {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (X : Ty) (hX : X.scopedB Δ = true) :
    DerivesWf Δ Γ blk (.bang (.lolli (.tensor .unit (.lolli B X)) (Cs X))) :=
  .bangLamI hΓ.persistent (by simp [Ty.scopedB, hX])
    (.lolliE (.left hΓ.split) (.var (.here hΓ))
      (.lolliI (by simp [Ty.scopedB, hX])
        (.sumI₂ (.var (.here (by dead))))))

theorem d_flipOn {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ flipOn (.lolli St (.tensor St B)) := by
  refine .lolliI rfl (.tensorE (T₁ := .ref .unit) (T₂ := B) (.left hΓ.split) rfl
    (.lolliE (.right hΓ.split) (.unitI (by dead))
      (.lolliE (.left hΓ.split) (.var (.here hΓ)) (.swapAx (by dead)))) ?_)
  -- ctx: s, σ1, σ
  refine .sumE (T₁ := .unit) (T₂ := .unit) (.left (.right (.dead hΓ.split))) rfl
    (.var (.here (by dead))) ?_ ?_
  all_goals
    -- ctx: x, s, σ1, σ
    refine .tensorE (T₁ := .ref B) (T₂ := .unit) (.left (.dead (.left (.dead hΓ.split)))) rfl
      (.lolliE (.left (.dead (.right (.dead hΓ.split))))
        (by first
          | exact .sumI₂ (.var (.here (by dead)))
          | exact .sumI₁ (.var (.here (by dead))))
        (.lolliE (.dead (.dead (.left (.dead hΓ.split)))) (.var (.there (.there (.here (by dead)))))
          (.swapAx (by dead)))) ?_
    -- ctx: u, σ2, x, s, σ1, σ
    exact .unitE (.left (.right (.dead (.dead (.dead (.dead hΓ.split))))))
      (.var (.here (by dead)))
      (.tensorI (.dead (.left (.dead (.dead (.dead (.dead hΓ.split))))))
        (.var (.there (.here (by dead))))
        (by first
          | exact .sumI₁ (.unitI (by dead))
          | exact .sumI₂ (.unitI (by dead))))

theorem d_h0 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ h0 (.lolli (.tensor R St) (.tensor R St)) :=
  .lolliI rfl (.var (.here hΓ))

theorem d_hS {next : Expr} {X : Ty} (hX : X.scopedB Δ = true)
    (hn : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → DerivesWf Δ Γ next (.lolli (.tensor X St) (.tensor R St)))
    {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ (hS next) (.lolli (.tensor (Cs X) St) (.tensor R St)) := by
  refine .lolliI (by simp [Ty.scopedB, hX]) ?_
  refine .tensorE (T₁ := Cs X) (T₂ := St) (.left hΓ.split) (by simp [Ty.scopedB, hX])
    (.var (.here hΓ)) ?_
  -- ctx: σ, c, p
  refine .sumE (T₁ := R) (T₂ := .tensor .unit (.lolli B X)) (.right (.left (.dead hΓ.split)))
    (by simp [Ty.scopedB, hX]) (.var (.there (.here (by dead)))) ?_ ?_
  · -- ctx: r, σ, c, p
    exact .tensorI (.left (.right (.dead (.dead hΓ.split))))
      (.var (.here (by dead))) (.var (.there (.here (by dead))))
  · -- ctx: q, σ, c, p
    refine .tensorE (T₁ := .unit) (T₂ := .lolli B X) (.left (.right (.dead (.dead hΓ.split))))
      (by simp [Ty.scopedB, hX]) (.var (.here (by dead))) ?_
    -- ctx: k, u, q, σ, c, p
    refine .unitE (.right (.left (.dead (.right (.dead (.dead hΓ.split))))))
      (.var (.there (.here (by dead)))) ?_
    refine .tensorE (T₁ := St) (T₂ := B) (.right (.dead (.dead (.left (.dead (.dead hΓ.split))))))
      rfl (.lolliE (.dead (.dead (.dead (.left (.dead (.dead hΓ.split))))))
        (.var (.there (.there (.there (.here (by dead))))))
        (d_flipOn (by dead))) ?_
    -- ctx: b, σ', k, u, q, σ, c, p
    exact .lolliE (.left (.left (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
      (.tensorI (.left (.right (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
        (.lolliE (T₁ := B) (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
        (.var (.here (by dead))) (.var (.there (.there (.here (by dead))))))
        (.var (.there (.here (by dead)))))
      (hn (by dead))

/-! ## The program -/

/-- `f ((), λa. g ((), λb. (a, b)))`. -/
def body : Expr :=
  .app blk (.pair unit' (lam (.app blk (.pair unit' (lam (.pair (.var 1) (.var 0)))))))

theorem d_body {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ body C2 := by
  refine .lolliE hΓ.split (.tensorI hΓ.split (.unitI hΓ) (.lolliI rfl ?_)) (.bangE (d_blk hΓ C1 rfl))
  -- ctx: a
  refine .lolliE (.left hΓ.split)
    (.tensorI (.right hΓ.split) (.unitI (by dead))
      (.lolliI rfl (.tensorI (.right (.left hΓ.split)) (.var (.there (.here (by dead))))
        (.var (.here (by dead))))))
    (.bangE (d_blk (by dead) R rfl))

/-- The handled program, answering both results. -/
def progP : Expr :=
  elet (.app alloc' (.inj₁ unit'))
    (.letpair (.app (hS (hS h0)) (.pair body (.var 0))) (.seq (dropB (.app free' (.var 0))) (.var 1)))

theorem d_progP : DerivesWf LifeCtx.empty [] progP R := by
  refine .lolliE (T₁ := St) .nil (.lolliE .nil (.sumI₁ (.unitI .nil)) (.allocAx .nil)) (.lolliI rfl ?_)
  -- ctx: σ
  refine .tensorE (T₁ := R) (T₂ := St) (.left .nil) rfl
    (.lolliE (.left .nil) (.tensorI (.right .nil) (d_body (by dead)) (.var (.here .nil)))
      (d_hS rfl (fun hΓ => d_hS rfl (fun hΓ' => d_h0 hΓ') hΓ) (by dead))) ?_
  -- ctx: σ', r, σ
  exact .unitE (.left (.right (.dead .nil)))
    (.sumE (T₁ := .unit) (T₂ := .unit) (.left (.dead (.dead .nil))) rfl
      (.lolliE (.left (.dead (.dead .nil))) (.var (.here (by dead)))
        (.freeAx (by dead)))
      (.var (.here (by dead))) (.var (.here (by dead))))
    (.var (.there (.here (by dead))))

/-- The program at `1`: both answers consumed. -/
def progU : Expr := .letpair progP (.seq (dropB (.var 1)) (dropB (.var 0)))

theorem d_progU : DerivesWf LifeCtx.empty [] progU .unit :=
  .tensorE (T₁ := B) (T₂ := B) .nil rfl d_progP
    (.unitE (.right (.left .nil))
      (.sumE (T₁ := .unit) (T₂ := .unit) (.dead (.left .nil)) rfl (.var (.there (.here .nil)))
        (.var (.here (by dead))) (.var (.here (by dead))))
      (d_dropB (by dead)))

/-- **Safe** by the Fundamental Property: the frame's cell is freed, nothing is stuck. -/
theorem progU_runs : BoLo.Steps Adequacy.emptyMem progU Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_progU

theorem progU_eval : unitNoLeak (eval progU) = true := by decide

/-- **Run**: the first block's `flip` answers `inj₁ ()`, the second sees the flipped state. -/
theorem progP_eval :
    (match eval progP with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

end HandlersControl
