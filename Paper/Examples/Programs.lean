import Paper.CONF.Results
import Paper.Examples.Derivations
import Support.Dynamics.Interpreter

/-!
# Examples — closed programs of type `1`, typed and run

Closed programs that use the borrowing constructs of `[CONF]` §2, each with

* a derivation `DerivesWf ∅ [] e 1`, the hypothesis of
  `Fig16.LogRel.Typed.adequacy`;
* the adequacy instance `BoLo.Steps ∅ e ∅ ()`, from `Fig16.LogRel.Typed.adequacy`:
  from the empty memory the program runs to `()` and frees everything it allocates;
* a kernel-checked run of the executable interpreter `BoCa.eval`
  (`Support/Dynamics/Interpreter.lean`), ending at `()` with nothing leaked.

`allocFree`'s run is also given step by step on `BoLo.Steps` itself.

The programs of `[CONF]` §2 are its open fragments closed off: each borrow they
assume is taken by `withbor` from a reference the program allocates, and freed
after.  A borrower's body returns `['a] T`; `[l]I` asks the live slots of its
context to outlive `'a`, which the borrower's own `Imm 'a T₁` does not, so a
borrower ends in `; ()` with that `()` boxed, as §12.24 describes.

| program | constructs |
|---|---|
| `allocFree` | `alloc`, `free`, `⊸E` |
| `fig2c` | `[CONF]` Fig. 2c: `swap`, `let`, `⊗E`, `⊕I`, `⊕E` |
| `immBorrow` | `withbor` (1), `copy`, `forget` at `Imm`, `withload`, `∀I`, `[l]I`, `⊗E`, `1E` |
| `mutBorrow` | `withbor` (2) with its side condition, `withswap`, `forget` at `Mut` |
| `aliasLoad` | `[CONF]` p. 415:9: `dupl`, `withload` of a nested borrow, the loaded alias outliving the load |
| `swapTwo` | `[CONF]` p. 415:10: two mutable borrows, nested `withswap`, strong update of nested references |
| `greetProg` | `[CONF]` p. 415:11 (Fig. 10b): `withbor` (3), `∀E`, lifetime-polymorphic functions |
| `loadClosure` | `withload` of a function payload, `Imm̲ 'b (T₁ ⊸ T₂) = Unk`, `forget` at `Unk` |

`[about ours: derivations and runs of closed instances of [CONF] §2's programs]`
-/

noncomputable section

namespace BoCa.Programs

open BoCa BoCa.Lifetime

/-! ## Term formers -/

/-- `alloc`. -/
def alloc' : Expr := .val (.prim .alloc)

/-- `free`. -/
def free' : Expr := .val (.prim .free)

/-- `λx.e`, and `Λ.e ≜ λ_.e` (§12.14). -/
def lam (b : Expr) : Expr := .val (.lam b)

/-- `f a b`. -/
def app2 (f a b : Expr) : Expr := .app (.app f a) b

/-- `e[] ≜ e ()` (§12.14). -/
def inst (e : Expr) : Expr := .app e unit'

/-! ## Context facts -/

theorem _root_.BoCa.Ctx.Dead.noBinds {Γ : Ctx Ty} (h : Ctx.Dead Γ) (x : LifeVar) :
    ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false := by
  induction h with
  | nil => intro s hs; cases hs
  | cons _ ih =>
      intro s hs hl
      cases hs with
      | head => exact absurd hl (by simp)
      | tail _ hs' => exact ih s hs' hl

/-- A consumed context splits into two copies of itself. -/
theorem _root_.BoCa.Ctx.Dead.split {Γ : Ctx Ty} (h : Ctx.Dead Γ) : Ctx.Split Γ Γ Γ := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .dead ih

/-- `[l]I`'s context premise at a context with one live slot. -/
theorem _root_.BoCa.Ctx.Outlives.solo {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {T : Ty}
    (ha : Δ.Defines a) (hT : OutlivesRules Δ a T) (h : Ctx.Dead Γ) :
    Ctx.Outlives Δ (⟨T, true⟩ :: Γ) a := by
  refine ⟨ha, ?_⟩
  intro s hs hl
  cases hs with
  | head => exact hT
  | tail _ hs' => exact (Ctx.Dead.outlives ha h).2 s hs' hl

/-- `interp` of a meet is at least as short as its left side. -/
theorem interp_meet_left {δ : LSub} {a b : Life} {n : Nat}
    (h : (Life.meet a b).interp δ = some n) : ∃ p, a.interp δ = some p ∧ p ≤ n := by
  simp only [Life.interp] at h
  cases ha : a.interp δ with
  | none => rw [ha] at h; simp at h
  | some p =>
    cases hb : b.interp δ with
    | none => rw [ha, hb] at h; simp at h
    | some q =>
      rw [ha, hb] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      exact ⟨p, rfl, h ▸ Nat.le_max_left p q⟩

/-- `interp` of a meet is at least as short as its right side. -/
theorem interp_meet_right {δ : LSub} {a b : Life} {n : Nat}
    (h : (Life.meet a b).interp δ = some n) : ∃ q, b.interp δ = some q ∧ q ≤ n := by
  simp only [Life.interp] at h
  cases ha : a.interp δ with
  | none => rw [ha] at h; simp at h
  | some p =>
    cases hb : b.interp δ with
    | none => rw [ha, hb] at h; simp at h
    | some q =>
      rw [ha, hb] at h
      simp only [Option.bind_some, Option.some.injEq] at h
      exact ⟨q, rfl, h ▸ Nat.le_max_right p q⟩

/-- `Δ ⊨ 'x ⊏ @b` when `@b` is at least as long as `Δ('x)` under every `δ`. -/
theorem entailsLt_of_bound {Δ : LifeCtx} {x : LifeVar} {u b : Life}
    (h : Δ.find? x = some u)
    (hb : ∀ δ n, u.interp δ = some n → ∃ p, b.interp δ = some p ∧ p ≤ n) :
    Δ.EntailsLt (.var x) b := by
  intro δ hδ
  obtain ⟨m, n, hm, hn, hlt⟩ := hδ x u h
  obtain ⟨p, hp, hle⟩ := hb δ n hn
  exact ⟨m, p, hm, hp, Nat.lt_of_le_of_lt hle hlt⟩

/-! ## `allocFree` — `free (alloc ())` -/

def allocFree : Expr := .app free' (.app alloc' unit')

theorem d_allocFree : DerivesWf LifeCtx.empty [] allocFree .unit :=
  .lolliE .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil)) (.freeAx .nil)

theorem allocFree_runs : BoLo.Steps Adequacy.emptyMem allocFree Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_allocFree

/-- The run, step by step: `alloc↦` under the frame `free []`, then `free↦`. -/
theorem allocFree_steps :
    BoLo.Steps Adequacy.emptyMem allocFree Adequacy.emptyMem (.val .unit) := by
  have hback : (Adequacy.emptyMem.upd 0 Val.unit).del 0 = Adequacy.emptyMem := by
    funext k
    by_cases hk : k = 0
    · subst hk; simp [Adequacy.emptyMem]
    · simp [BoLo.Heap.del, BoLo.Heap.upd, hk, Adequacy.emptyMem]
  refine .more (μ₁ := Adequacy.emptyMem.upd 0 Val.unit) (e₁ := .app free' (.val (.loc 0)))
    ⟨.appR free' .hole, _, _, rfl, rfl, .alloc _ Val.unit 0 rfl⟩ ?_
  have h := BoLo.Steps.one (BoLo.Step1.head
    (BoLo.Head.free (Adequacy.emptyMem.upd 0 Val.unit) 0 Val.unit (BoLo.Heap.upd_same _ _ _)))
  rw [hback] at h
  exact h

/-- `Outcome.value ()` with no cell left, as a `Bool`. -/
def unitNoLeak : Outcome → Bool
  | .value ⟨.unit, _⟩ false => true
  | _ => false

theorem allocFree_eval : unitNoLeak (eval allocFree) = true := by decide

/-! ## Payload types -/

/-- `Ref 1`. -/
abbrev R : Ty := .ref .unit

/-- `1 ⊕ 1`. -/
abbrev B : Ty := .sum .unit .unit

/-- `case z {x ⇒ x, y ⇒ y}`: consumes a `1 ⊕ 1`. -/
def dropB (z : Expr) : Expr := .case z (.var 0) (.var 0)

theorem d_dropB {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨B, true⟩ :: Γ) (dropB (.var 0)) .unit :=
  .sumE (.left hΓ.split) rfl (.var (.here hΓ)) (.var (.here (.cons hΓ))) (.var (.here (.cons hΓ)))

/-! ## `fig2c` — `[CONF]` Fig. 2c: `swap` returns the old payload

    let x = alloc v; let (x′, y) = swap x (); free x′; y

*"returns `v`"* (`[CONF]` p. 415:4).  At `v = inj₁ ()`, with a final
`case y {x ⇒ x, y ⇒ y}` to reach type `1`.  `let x = e; e′` is `(λx. e′) e`
(`BoCa.elet`). -/

def fig2cBody : Expr :=
  elet (.app alloc' (.inj₁ unit'))
    (.letpair (app2 swap (.var 0) unit') (.seq (.app free' (.var 1)) (.var 0)))

def fig2c : Expr := dropB fig2cBody

theorem d_fig2cBody : DerivesWf LifeCtx.empty [] fig2cBody B :=
  .lolliE .nil (.lolliE .nil (.sumI₁ (.unitI .nil)) (.allocAx .nil))
    (.lolliI rfl
      (.tensorE (T₁ := R) (T₂ := B) (.left .nil) rfl
        (.lolliE (.right .nil) (.unitI (.cons .nil))
          (.lolliE (.left .nil) (.var (.here .nil)) (.swapAx (.cons .nil))))
        (.unitE (.right (.left (.dead .nil)))
          (.lolliE (.dead (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
            (.freeAx (.cons (.cons (.cons .nil)))))
          (.var (.here (.cons (.cons .nil)))))))

theorem d_fig2c : DerivesWf LifeCtx.empty [] fig2c .unit :=
  .sumE .nil rfl d_fig2cBody (.var (.here .nil)) (.var (.here .nil))

theorem fig2c_runs : BoLo.Steps Adequacy.emptyMem fig2c Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_fig2c

theorem fig2c_eval : unitNoLeak (eval fig2c) = true := by decide

/-- Without the final `case`, the program returns `v = inj₁ ()`, the payload `swap`
took out, and leaks nothing. -/
theorem fig2cBody_returns_v :
    (match eval fig2cBody with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-! ## `immBorrow` — an immutable borrow, copied, one copy loaded through

    let (r, u) = withbor (alloc ()) (Λ. λb. let (b₁, b₂) = copy b; forget b₁;
                                           withload b₂ (Λ. λy. y));
    u; free r

`withbor`'s first form at `T₁ = T₂ = 1`; the loader returns `y : Imm̲ 'b 1 = 1`
boxed at `'b` and at `'a`. -/

/-- The loader `Λ. λy. y`. -/
def immLoader : Expr := lam (lam (.var 0))

/-- The borrower `Λ. λb. let (b₁, b₂) = copy b; forget b₁; withload b₂ loader`. -/
def immBorrower : Expr :=
  lam (lam (.letpair (.app copy (.var 0))
    (.seq (.app forget (.var 1)) (app2 withload (.var 0) immLoader))))

def immBorrow : Expr :=
  .letpair (app2 withbor (.app alloc' unit') immBorrower) (.seq (.var 0) (.app free' (.var 1)))

theorem d_immLoader {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ immLoader
      (.all 1 D1.meetOfDom (.lolli (Ty.immReborrow (.var 1) .unit) (.box (.var 1) (.box (.var 0) .unit)))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl
      (.boxIctx (.boxIctx (.var (.here (.cons hΓ)))
          (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons hΓ)))
        (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons hΓ))))

theorem d_immBorrower :
    DerivesWf LifeCtx.empty [] immBorrower
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) .unit) (.box (.var 0) .unit))) := by
  refine .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0) (.lolliI rfl ?_)
  refine .tensorE (T₁ := .imm (.var 0) .unit) (T₂ := .imm (.var 0) .unit)
    (.left (.dead .nil)) rfl
    (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil))) (.copyAx (.cons (.cons .nil)))) ?_
  refine .unitE (.right (.left (.dead (.dead .nil))))
    (.lolliE (.dead (.left (.dead (.dead .nil)))) (.var (.there (.here (.cons (.cons .nil)))))
      (.forgetImmAx (.cons (.cons (.cons (.cons .nil)))))) ?_
  exact .lolliE (.right (.dead (.dead (.dead .nil))))
    (d_immLoader (.cons (.cons (.cons (.cons .nil)))))
    (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil)))))
      (.withloadAx (T₂ := .box (.var 0) .unit) (.cons (.cons (.cons (.cons .nil)))) 1 rfl rfl))

/-- The tail `u; free r`, at `u : 1, r : Ref 1`. -/
theorem d_useFree {Δ : LifeCtx} :
    DerivesWf Δ [⟨.unit, true⟩, ⟨.ref .unit, true⟩] (.seq (.var 0) (.app free' (.var 1))) .unit :=
  .unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
    (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))

theorem d_immBorrow : DerivesWf LifeCtx.empty [] immBorrow .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_immBorrower
      (.lolliE .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil)) (.withbor1Ax .nil 0 rfl rfl)))
    d_useFree

theorem immBorrow_runs : BoLo.Steps Adequacy.emptyMem immBorrow Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_immBorrow

theorem immBorrow_eval : unitNoLeak (eval immBorrow) = true := by decide

/-! ## `mutBorrow` — a mutable borrow, and a strong update through `withswap`

    let (r, u) = withbor (alloc (inj₁ ())) (Λ. λm.
                   let (m′, v) = withswap m (λz. case z {x ⇒ x, y ⇒ y}; (inj₂ (), ()));
                   v; forget m′; ());
    u; case (free r) {x ⇒ x, y ⇒ y}

`withbor`'s second form at `T₁ = 1 ⊕ 1`, with its side condition `∅ ⊢ 1 ⊕ 1 ⊐ ⊤`.
The cell holds `inj₁ ()` before the borrow and `inj₂ ()` after it. -/

/-- `λz. case z {x ⇒ x, y ⇒ y}; (inj₂ (), ())`. -/
def flipB : Expr := lam (.seq (dropB (.var 0)) (.pair (.inj₂ unit') unit'))

def mutBorrower : Expr :=
  lam (lam (.letpair (app2 withswap (.var 0) flipB)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))

def mutBorrow : Expr :=
  .letpair (app2 withbor (.app alloc' (.inj₁ unit')) mutBorrower)
    (.seq (.var 0) (dropB (.app free' (.var 1))))

theorem d_flipB {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ flipB (.lolli B (.tensor B .unit)) :=
  .lolliI rfl (.unitE (.left hΓ.split) (d_dropB hΓ)
    (.tensorI (.dead hΓ.split) (.sumI₂ (.unitI (.cons hΓ))) (.unitI (.cons hΓ))))

/-- `v; forget m′; □()` at `v : 1, m′ : Mut @a T`, the rest consumed. -/
theorem d_forgetTail {Δ : LifeCtx} {Γ : Ctx Ty} {a b : Life} {T : Ty} (hΓ : Ctx.Dead Γ)
    (hb : Δ.Defines b) :
    DerivesWf Δ (⟨.unit, true⟩ :: ⟨.mut a T, true⟩ :: Γ)
      (.seq (.var 0) (.seq (.app forget (.var 1)) unit')) (.box b .unit) :=
  .unitE (.left (.right hΓ.split)) (.var (.here (.cons hΓ)))
    (.unitE (.dead (.left hΓ.split))
      (.lolliE (.dead (.left hΓ.split)) (.var (.there (.here hΓ)))
        (.forgetMutAx (.cons (.cons hΓ))))
      (.boxIctx (.unitI (.cons (.cons hΓ))) (Ctx.Dead.outlives hb (.cons (.cons hΓ)))))

theorem d_mutBorrower :
    DerivesWf LifeCtx.empty [] mutBorrower
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) B) (.box (.var 0) .unit))) := by
  refine .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0) (.lolliI rfl ?_)
  refine .tensorE (T₁ := .mut (.var 0) B) (T₂ := .unit) (.left (.dead .nil)) rfl ?_
    (d_forgetTail (.cons (.cons .nil)) (LifeCtx.defines_of_wf rfl))
  exact .lolliE (.right (.dead .nil)) (d_flipB (.cons (.cons .nil)))
    (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil))) (.withswapAx (.cons (.cons .nil))))

/-- `u; case (free r) {x ⇒ x, y ⇒ y}`, at `u : 1, r : Ref (1 ⊕ 1)`. -/
theorem d_useFreeB {Δ : LifeCtx} :
    DerivesWf Δ [⟨.unit, true⟩, ⟨.ref B, true⟩]
      (.seq (.var 0) (dropB (.app free' (.var 1)))) .unit :=
  .unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
    (.sumE (.dead (.left .nil)) rfl
      (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))
      (.var (.here (.cons (.cons .nil)))) (.var (.here (.cons (.cons .nil)))))

theorem d_mutBorrow : DerivesWf LifeCtx.empty [] mutBorrow .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_mutBorrower
      (.lolliE .nil (.lolliE .nil (.sumI₁ (.unitI .nil)) (.allocAx .nil))
        (.withbor2Ax .nil 0 rfl ⟨.top, LifeCtx.defines_of_wf rfl, .sum .unit .unit⟩ rfl)))
    d_useFreeB

theorem mutBorrow_runs : BoLo.Steps Adequacy.emptyMem mutBorrow Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_mutBorrow

theorem mutBorrow_eval : unitNoLeak (eval mutBorrow) = true := by decide

/-- Without the final `case`, the program returns the cell's last payload: `inj₂ ()`,
the value `withswap` stored. -/
theorem mutBorrow_stored :
    (match eval (.letpair (app2 withbor (.app alloc' (.inj₁ unit')) mutBorrower)
        (.seq (.var 0) (.app free' (.var 1)))) with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-! ## `loadClosure` — loading a function payload gives `Unk`

    let (r, u) = withbor (alloc (λx.x)) (Λ. λb. withload b (Λ. λy. forget y; ()));
    u; (free r) ()

`Imm̲ 'b (1 ⊸ 1) ≜ Unk` (`[TR]` p. 3): the loader sees `Unk`, and the only operation
on it is `forget : Unk ⊸ 1`. -/

def unkLoader : Expr := lam (lam (.seq (.app forget (.var 0)) unit'))

def unkBorrower : Expr := lam (lam (app2 withload (.var 0) unkLoader))

def loadClosure : Expr :=
  .letpair (app2 withbor (.app alloc' (lam (.var 0))) unkBorrower)
    (.seq (.var 0) (.app (.app free' (.var 1)) unit'))

theorem d_unkLoader {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ unkLoader
      (.all 1 D1.meetOfDom
        (.lolli (Ty.immReborrow (.var 1) (.lolli .unit .unit)) (.box (.var 1) (.box (.var 0) .unit)))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl
      (.unitE (.left (.dead hΓ.split))
        (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ))) (.forgetUnkAx (.cons (.cons hΓ))))
        (.boxIctx (.boxIctx (.unitI (.cons (.cons hΓ)))
            (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons hΓ))))
          (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons hΓ))))))

theorem d_unkBorrower :
    DerivesWf LifeCtx.empty [] unkBorrower
      (.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.imm (.var 0) (.lolli .unit .unit)) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0)
    (.lolliI rfl
      (.lolliE (.right (.dead .nil)) (d_unkLoader (.cons (.cons .nil)))
        (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
          (.withloadAx (T₂ := .box (.var 0) .unit) (.cons (.cons .nil)) 1 rfl rfl))))

theorem d_loadClosure : DerivesWf LifeCtx.empty [] loadClosure .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_unkBorrower
      (.lolliE .nil (.lolliE .nil (.lolliI rfl (.var (.here .nil))) (.allocAx .nil))
        (.withbor1Ax .nil 0 rfl rfl)))
    (.unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
      (.lolliE (.dead (.right .nil)) (.unitI (.cons (.cons .nil)))
        (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))))

theorem loadClosure_runs :
    BoLo.Steps Adequacy.emptyMem loadClosure Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_loadClosure

theorem loadClosure_eval : unitNoLeak (eval loadClosure) = true := by decide

/-! ## `aliasLoad` — `[CONF]` p. 415:9: a nested borrow outlives the load

`[CONF]` p. 415:9 prints, at `x : Imm a T`,

    let (x1, x2) = dupl x;
    let (y, ()) = withbor (alloc x1) (Λ. λx1′.
       withload x1′ (Λ. λx1. // x1 and x2 both accessible, x2 allowed to escape ···));
    free y

with *"aliases to the inner borrow `Imm a T` are allowed to exist anyway"*.  Closed
off at `T = 1`, with `x` borrowed from a reference the program allocates, and the
elided loader body returning the loaded `x1 : Imm̲ 'c (Imm 'a 1) = Imm 'a 1` out of
the load and out of the inner borrow:

    let (r, u) = withbor (alloc ()) (Λ. λx.
       let (x1, x2) = copy x;
       let (y, x3) = withbor (alloc x1) (Λ. λx1′. withload x1′ (Λ. λz. z));
       forget x3; forget x2; forget (free y); ());
    u; free r

`copy` is `[CONF]`'s `dupl` (§12.21).  The loader returns `z` boxed at `'c` and at
`'b`, which `Imm 'a 1` outlives because `'c ⊏ 'b ⊏ 'a`. -/

/-- `['b ⊏ 'a ⊓ ⊤, 'a ⊏ ⊤]`: the inner borrower's context. -/
def D2 : LifeCtx := D1.extend 1 D1.meetOfDom

/-- `Λ. λz. z`. -/
def aliasLoader : Expr := lam (lam (.var 0))

/-- `Λ. λx1′. withload x1′ loader`. -/
def aliasInner : Expr := lam (lam (app2 withload (.var 0) aliasLoader))

def aliasBorrower : Expr :=
  lam (lam (.letpair (.app copy (.var 0))
    (.letpair (app2 withbor (.app alloc' (.var 1)) aliasInner)
      (.seq (.app forget (.var 0))
        (.seq (.app forget (.var 2))
          (.seq (.app forget (.app free' (.var 1))) unit'))))))

def aliasLoad : Expr :=
  .letpair (app2 withbor (.app alloc' unit') aliasBorrower) (.seq (.var 0) (.app free' (.var 1)))

theorem d_aliasLoader {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D2 Γ aliasLoader
      (.all 2 D2.meetOfDom
        (.lolli (Ty.immReborrow (.var 2) (.imm (.var 0) .unit))
          (.box (.var 2) (.box (.var 1) (.imm (.var 0) .unit))))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 2)
    (.lolliI rfl
      (.boxIctx
        (.boxIctx (.var (.here (.cons hΓ)))
          (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl)
            (.imm (entailsLt_of_bound rfl fun _ _ h => interp_meet_left h)) (.cons hΓ)))
        (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl)
          (.imm (entailsLt_of_bound rfl fun _ _ h => by
            obtain ⟨q, hq, hle⟩ := interp_meet_right h
            obtain ⟨p, hp, hle'⟩ := interp_meet_left hq
            exact ⟨p, hp, Nat.le_trans hle' hle⟩)) (.cons hΓ))))

theorem d_aliasInner {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ aliasInner
      (.all 1 D1.meetOfDom
        (.lolli (.imm (.var 1) (.imm (.var 0) .unit)) (.box (.var 1) (.imm (.var 0) .unit)))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl
      (.lolliE (.right (.dead hΓ.split)) (d_aliasLoader (.cons (.cons hΓ)))
        (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ)))
          (.withloadAx (T₂ := .box (.var 1) (.imm (.var 0) .unit)) (.cons (.cons hΓ)) 2 rfl rfl))))

theorem d_aliasBorrower :
    DerivesWf LifeCtx.empty [] aliasBorrower
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) .unit) (.box (.var 0) .unit))) := by
  refine .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0) (.lolliI rfl ?_)
  refine .tensorE (T₁ := .imm (.var 0) .unit) (T₂ := .imm (.var 0) .unit)
    (.left (.dead .nil)) rfl
    (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil))) (.copyAx (.cons (.cons .nil)))) ?_
  -- `[x2, x1, x, _]`: the inner `withbor` takes `x1`
  refine .tensorE (T₁ := .ref (.imm (.var 0) .unit)) (T₂ := .imm (.var 0) .unit)
    (.right (.left (.dead (.dead .nil)))) rfl
    (.lolliE (.dead (.right (.dead (.dead .nil)))) (d_aliasInner (.cons (.cons (.cons (.cons .nil)))))
      (.lolliE (.dead (.left (.dead (.dead .nil))))
        (.lolliE (.dead (.left (.dead (.dead .nil)))) (.var (.there (.here (.cons (.cons .nil)))))
          (.allocAx (.cons (.cons (.cons (.cons .nil))))))
        (.withbor1Ax (.cons (.cons (.cons (.cons .nil)))) 1 rfl rfl))) ?_
  -- `[x3, y, x2, x1, x, _]`
  refine .unitE (.left (.right (.right (.dead (.dead (.dead .nil))))))
    (.lolliE (.left (.dead (.dead (.dead (.dead (.dead .nil))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))
      (.forgetImmAx (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))) ?_
  refine .unitE (.dead (.right (.left (.dead (.dead (.dead .nil))))))
    (.lolliE (.dead (.dead (.left (.dead (.dead (.dead .nil))))))
      (.var (.there (.there (.here (.cons (.cons (.cons .nil)))))))
      (.forgetImmAx (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))) ?_
  refine .unitE (.dead (.left (.dead (.dead (.dead (.dead .nil))))))
    (.lolliE (.dead (.left (.dead (.dead (.dead (.dead .nil))))))
      (.lolliE (.dead (.left (.dead (.dead (.dead (.dead .nil))))))
        (.var (.there (.here (.cons (.cons (.cons (.cons .nil)))))))
        (.freeAx (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))
      (.forgetImmAx (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))) ?_
  exact .boxIctx (.unitI (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))
    (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))

theorem d_aliasLoad : DerivesWf LifeCtx.empty [] aliasLoad .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_aliasBorrower
      (.lolliE .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil)) (.withbor1Ax .nil 0 rfl rfl)))
    d_useFree

theorem aliasLoad_runs : BoLo.Steps Adequacy.emptyMem aliasLoad Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_aliasLoad

theorem aliasLoad_eval : unitNoLeak (eval aliasLoad) = true := by decide

/-! ## `swapTwo` — `[CONF]` p. 415:10: two mutable borrows, nested `withswap`

`[CONF]` p. 415:10 prints, at `x1 : Mut 'a1 Ref 1, x2 : Mut 'a2 Ref 1`,

    let (x1, ()) = withswap x1 (λx1′.
      let (x2, ()) = withswap x2 (λx2′.
          free x1′; free x2′; (alloc (), ()));
      forget x2;
      (alloc (), ()));
    forget x1

*"if the two mutable borrows aliased, there would be a use-after-free bug, but the
program is safe if they are distinct."*  Closed off with each `xᵢ` borrowed by
`withbor`'s second form from a reference to a reference the program allocates, and
both freed after:

    let (r1, u1) = withbor (alloc (alloc ())) (Λ. λx1.
       let (r2, u2) = withbor (alloc (alloc ())) (Λ. λx2. ⟨the program above⟩; ());
       u2; free (free r2); ());
    u1; free (free r1) -/

/-- `λx2′. free x1′; free x2′; (alloc (), ())`, capturing `x1′`. -/
def swapIn2 : Expr :=
  lam (.seq (.app free' (.var 1)) (.seq (.app free' (.var 0)) (.pair (.app alloc' unit') unit')))

/-- `λx1′. let (x2, ()) = withswap x2 swapIn2; forget x2; (alloc (), ())`,
capturing `x2`. -/
def swapIn1 : Expr :=
  lam (.letpair (app2 withswap (.var 1) swapIn2)
    (.seq (.var 0) (.seq (.app forget (.var 1)) (.pair (.app alloc' unit') unit'))))

/-- `Λ. λx2. let (x1, ()) = withswap x1 swapIn1; forget x1; ()`, capturing `x1`. -/
def swapInner : Expr :=
  lam (lam (.letpair (app2 withswap (.var 2) swapIn1)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))

def swapOuter : Expr :=
  lam (lam (.letpair (app2 withbor (.app alloc' (.app alloc' unit')) swapInner)
    (.seq (.var 0) (.seq (.app free' (.app free' (.var 1))) unit'))))

def swapTwo : Expr :=
  .letpair (app2 withbor (.app alloc' (.app alloc' unit')) swapOuter)
    (.seq (.var 0) (.app free' (.app free' (.var 1))))

/-- `(alloc (), ()) : Ref 1 ⊗ 1`. -/
theorem d_allocPair {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ (.pair (.app alloc' unit') unit') (.tensor R .unit) :=
  .tensorI hΓ.split (.lolliE hΓ.split (.unitI hΓ) (.allocAx hΓ)) (.unitI hΓ)

/-- `alloc (alloc ()) : Ref (Ref 1)`. -/
theorem d_allocAlloc {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ (.app alloc' (.app alloc' unit')) (.ref R) :=
  .lolliE hΓ.split (.lolliE hΓ.split (.unitI hΓ) (.allocAx hΓ)) (.allocAx hΓ)

theorem d_swapIn2 {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨R, true⟩ :: Γ) swapIn2 (.lolli R (.tensor R .unit)) :=
  .lolliI rfl
    (.unitE (.right (.left hΓ.split))
      (.lolliE (.dead (.left hΓ.split)) (.var (.there (.here hΓ))) (.freeAx (.cons (.cons hΓ))))
      (.unitE (.left (.dead hΓ.split))
        (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ))) (.freeAx (.cons (.cons hΓ))))
        (d_allocPair (.cons (.cons hΓ)))))

theorem d_swapIn1 {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} (hΓ : Ctx.Dead Γ) (ha : a.wf Δ = true) :
    DerivesWf Δ (⟨.mut a R, true⟩ :: Γ) swapIn1 (.lolli R (.tensor R .unit)) :=
  .lolliI rfl
    (.tensorE (T₁ := .mut a R) (T₂ := .unit) (.left (.left hΓ.split)) (by simp [Ty.scopedB, ha])
      (.lolliE (.left (.right hΓ.split)) (d_swapIn2 (.cons hΓ))
        (.lolliE (.dead (.left hΓ.split)) (.var (.there (.here hΓ))) (.withswapAx (.cons (.cons hΓ)))))
      (.unitE (.left (.right (.dead (.dead hΓ.split)))) (.var (.here (.cons (.cons (.cons hΓ)))))
        (.unitE (.dead (.left (.dead (.dead hΓ.split))))
          (.lolliE (.dead (.left (.dead (.dead hΓ.split)))) (.var (.there (.here (.cons (.cons hΓ)))))
            (.forgetMutAx (.cons (.cons (.cons (.cons hΓ))))))
          (d_allocPair (.cons (.cons (.cons (.cons hΓ))))))))

theorem d_swapInner :
    DerivesWf D1 [⟨.mut (.var 0) R, true⟩, ⟨.unit, false⟩] swapInner
      (.all 1 D1.meetOfDom (.lolli (.mut (.var 1) R) (.box (.var 1) .unit))) :=
  .allI (S := .unit) rfl rfl (by decide)
    (.lolliI rfl
      (.tensorE (T₁ := .mut (.var 0) R) (T₂ := .unit) (.left (.dead (.left (.dead .nil)))) rfl
        (.lolliE (.left (.dead (.right (.dead .nil)))) (d_swapIn1 (.cons (.cons (.cons .nil))) rfl)
          (.lolliE (.dead (.dead (.left (.dead .nil)))) (.var (.there (.there (.here (.cons .nil)))))
            (.withswapAx (.cons (.cons (.cons (.cons .nil)))))))
        (d_forgetTail (.cons (.cons (.cons (.cons .nil)))) (LifeCtx.defines_of_wf rfl))))

theorem d_swapOuter :
    DerivesWf LifeCtx.empty [] swapOuter
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) R) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0)
    (.lolliI rfl
      (.tensorE (T₁ := .ref R) (T₂ := .unit) (.left (.dead .nil)) rfl
        (.lolliE (.left (.dead .nil)) d_swapInner
          (.lolliE (.dead (.dead .nil)) (d_allocAlloc (.cons (.cons .nil)))
            (.withbor2Ax (.cons (.cons .nil)) 1 rfl ⟨.top, LifeCtx.defines_of_wf rfl, .ref .unit⟩ rfl)))
        (.unitE (.left (.right (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil)))))
          (.unitE (.dead (.left (.dead (.dead .nil))))
            (.lolliE (.dead (.left (.dead (.dead .nil))))
              (.lolliE (.dead (.left (.dead (.dead .nil)))) (.var (.there (.here (.cons (.cons .nil)))))
                (.freeAx (.cons (.cons (.cons (.cons .nil))))))
              (.freeAx (.cons (.cons (.cons (.cons .nil))))))
            (.boxIctx (.unitI (.cons (.cons (.cons (.cons .nil)))))
              (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons .nil))))))))))

theorem d_swapTwo : DerivesWf LifeCtx.empty [] swapTwo .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_swapOuter
      (.lolliE .nil (d_allocAlloc .nil)
        (.withbor2Ax .nil 0 rfl ⟨.top, LifeCtx.defines_of_wf rfl, .ref .unit⟩ rfl)))
    (.unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
      (.lolliE (.dead (.left .nil))
        (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))
        (.freeAx (.cons (.cons .nil)))))

theorem swapTwo_runs : BoLo.Steps Adequacy.emptyMem swapTwo Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_swapTwo

theorem swapTwo_eval : unitNoLeak (eval swapTwo) = true := by decide

/-! ## `greetProg` — `[CONF]` p. 415:11 (Fig. 10b): reborrowing a mutable borrow

`[CONF]` Fig. 10b prints

    writeln : ∀ 'a. Mut 'a File ⊸ Str ⊸ 1
    greet : ∀ 'a. Mut 'a File ⊸ 1
    greet f =
      let (f, ()) = withbor f (Λ. λf′. writeln () f′ "hello");
      writeln () f "world"

*"we allow withbor to reborrow from a mutable borrow at a new lifetime. Then, one may
insert such a reborrow before each call, as demonstrated in the body of greet."*
Closed off at `File = 1 ⊕ 1` and `Str = 1`, with `∀ 'a.` read at the bound `⊤`,
`writeln` a `withswap` that stores `inj₂ s` into the file, and the file borrowed by
`withbor`'s second form from a cell the program allocates:

    writeln ≜ Λ. λf. λs. let (f′, v) = withswap f (λc. case c {x ⇒ x, y ⇒ y}; (inj₂ s, ()));
                         v; forget f′
    greet   ≜ Λ. λf. let (f, v) = withbor f (Λ. λf′. writeln () f′ (); ());
                     v; writeln () f ()
    let (r, u) = withbor (alloc (inj₁ ())) (Λ. λf. greet () f; ());
    u; case (free r) {x ⇒ x, y ⇒ y}

The inner borrower ends in `; ()` (§12.24, above).  `greet () f` and each
`writeln ()` are `∀E`, at the borrow's own lifetime. -/

/-- `λc. case c {x ⇒ x, y ⇒ y}; (inj₂ s, ())`, capturing `s`. -/
def writeS : Expr := lam (.seq (dropB (.var 0)) (.pair (.inj₂ (.var 1)) unit'))

def writeln : Expr :=
  lam (lam (lam (.letpair (app2 withswap (.var 1) writeS) (.seq (.var 0) (.app forget (.var 1))))))

def greetBorrower : Expr := lam (lam (.seq (app2 (inst writeln) (.var 0) unit') unit'))

def greet : Expr :=
  lam (lam (.letpair (app2 withbor (.var 0) greetBorrower)
    (.seq (.var 0) (app2 (inst writeln) (.var 1) unit'))))

def greetMain : Expr := lam (lam (.seq (.app (inst greet) (.var 0)) unit'))

def greetProg : Expr :=
  .letpair (app2 withbor (.app alloc' (.inj₁ unit')) greetMain)
    (.seq (.var 0) (dropB (.app free' (.var 1))))

/-- `['g ⊏ ⊤, 'a ⊏ ⊤]`: `greet`'s body, `'g` the variable `1`. -/
def Dg : LifeCtx := D1.extend 1 .top

theorem wf_var_extend {Δ : LifeCtx} {x : LifeVar} {u : Life} :
    (Life.var x).wf (Δ.extend x u) = true := by
  simp [Life.wf, LifeCtx.find?_extend]

theorem instLife_writeln (x : LifeVar) (a : Life) :
    Ty.instLife x a (.lolli (.mut (.var x) B) (.lolli .unit .unit))
      = .lolli (.mut a B) (.lolli .unit .unit) := by
  simp [Ty.instLife, Ty.applyLSub, Life.applySub, assocFind]

theorem d_writeS {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨.unit, true⟩ :: Γ) writeS (.lolli B (.tensor B .unit)) :=
  .lolliI rfl
    (.unitE (.left (.right hΓ.split)) (d_dropB (.cons hΓ))
      (.tensorI (.dead (.left hΓ.split)) (.sumI₂ (.var (.there (.here hΓ))))
        (.unitI (.cons (.cons hΓ)))))

theorem d_writeln {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (x : LifeVar)
    (hx : Δ.find? x = none) :
    DerivesWf Δ Γ writeln (.all x .top (.lolli (.mut (.var x) B) (.lolli .unit .unit))) :=
  .allI (S := .unit) hx rfl (Ctx.Dead.noBinds hΓ x)
    (.lolliI (by simp [Ty.scopedB, wf_var_extend])
      (.lolliI rfl
        (.tensorE (T₁ := .mut (.var x) B) (T₂ := .unit) (.left (.left (.dead hΓ.split)))
          (by simp [Ty.scopedB, wf_var_extend])
          (.lolliE (.left (.right (.dead hΓ.split))) (d_writeS (.cons (.cons hΓ)))
            (.lolliE (.dead (.left (.dead hΓ.split))) (.var (.there (.here (.cons hΓ))))
              (.withswapAx (.cons (.cons (.cons hΓ))))))
          (.unitE (.left (.right (.dead (.dead (.dead hΓ.split)))))
            (.var (.here (.cons (.cons (.cons (.cons hΓ))))))
            (.lolliE (.dead (.left (.dead (.dead (.dead hΓ.split)))))
              (.var (.there (.here (.cons (.cons (.cons hΓ))))))
              (.forgetMutAx (.cons (.cons (.cons (.cons (.cons hΓ)))))))))))

/-- `writeln () f ()`, at `f : Mut 'y (1 ⊕ 1)` in slot `i` of `Γ` and the binder
`'x` of `writeln` fresh. -/
theorem d_callWriteln {Δ : LifeCtx} {Γ Γd : Ctx Ty} {i : Nat} {y : LifeVar} {u : Life}
    (hs₁ : Ctx.Split Γ Γd Γ) (hs₂ : Ctx.Split Γ Γ Γd) (hd : Ctx.Dead Γd)
    (hi : Ctx.Solo Γ i (.mut (.var y) B)) (x : LifeVar) (hx : Δ.find? x = none)
    (hy : Δ.find? y = some u) :
    DerivesWf Δ Γ (app2 (inst writeln) (.var i) unit') .unit := by
  have h := DerivesWf.allE (a := .var y) (d_writeln (Γ := Γd) hd x hx) (entailsLt_top hy)
  rw [instLife_writeln] at h
  exact .lolliE hs₁ (.unitI hd) (.lolliE hs₂ (.var hi) h)

theorem d_greetBorrower {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Dg Γ greetBorrower
      (.all 2 Dg.meetOfDom (.lolli (.mut (.var 2) B) (.box (.var 2) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 2)
    (.lolliI rfl
      (.unitE (.left (.dead hΓ.split))
        (d_callWriteln (.right (.dead hΓ.split)) (.left (.dead hΓ.split)) (.cons (.cons hΓ))
          (.here (.cons hΓ)) 3 rfl rfl)
        (.boxIctx (.unitI (.cons (.cons hΓ)))
          (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons hΓ))))))

theorem d_greet {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ greet (.all 1 .top (.lolli (.mut (.var 1) B) .unit)) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl
      (.tensorE (T₁ := .mut (.var 1) B) (T₂ := .unit) (.left (.dead hΓ.split)) rfl
        (.lolliE (.right (.dead hΓ.split)) (d_greetBorrower (.cons (.cons hΓ)))
          (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ)))
            (.withbor3Ax (a := .var 1) (.cons (.cons hΓ)) 2 rfl rfl)))
        (.unitE (.left (.right (.dead (.dead hΓ.split))))
          (.var (.here (.cons (.cons (.cons hΓ)))))
          (d_callWriteln (.dead (.right (.dead (.dead hΓ.split))))
            (.dead (.left (.dead (.dead hΓ.split)))) (.cons (.cons (.cons (.cons hΓ))))
            (.there (.here (.cons (.cons hΓ)))) 2 rfl rfl))))

theorem d_greetMain :
    DerivesWf LifeCtx.empty [] greetMain
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) B) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0)
    (.lolliI rfl
      (.unitE (.left (.dead .nil))
        (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
          (.allE (x := 1) (b := .top) (a := .var 0) (d_greet (.cons (.cons .nil)))
            (entailsLt_top rfl)))
        (.boxIctx (.unitI (.cons (.cons .nil)))
          (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons .nil))))))

theorem d_greetProg : DerivesWf LifeCtx.empty [] greetProg .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_greetMain
      (.lolliE .nil (.lolliE .nil (.sumI₁ (.unitI .nil)) (.allocAx .nil))
        (.withbor2Ax .nil 0 rfl ⟨.top, LifeCtx.defines_of_wf rfl, .sum .unit .unit⟩ rfl)))
    d_useFreeB

theorem greetProg_runs : BoLo.Steps Adequacy.emptyMem greetProg Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_greetProg

theorem greetProg_eval : unitNoLeak (eval greetProg) = true := by decide

end BoCa.Programs

end
