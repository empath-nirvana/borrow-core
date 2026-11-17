import Core.Splits
import Core.Tied
import Core.Consume
import Core.EffBorrow
import Core.DelayPrograms

/-!
# Local cells, derived from allocation, lending and free `[spec §80]`

The owner never reaches the callback. The normal result returns the final contents and the
callback answer. There is no new judgment or machine rule.
-/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Lifetime (LifeCtx LifeVar)

def withlocalTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli A (.lolli (.all x bnd (.lolli (.mut (.var x) A) (.box (.var x) B))) (.tensor A B))

def withlocalE : Expr := .val (.lam (.val (.lam
  (.letpair (.app (.app withbor (.app (.val (.prim .alloc)) (.var 1))) (.var 0))
    (.pair (.app (.val (.prim .free)) (.var 1)) (.var 0))))))

theorem withlocal_closed : closedAt 0 withlocalE = true := rfl

theorem withlocal_wf {Δ : LifeCtx} {Γ : Ctx VTy} (x : LifeVar) (A B : VTy)
    (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) :
    CDerives Δ Γ withlocalE (.val (withlocalTy x Δ.meetOfDom A B)) := by
  unfold withlocalE withlocalTy
  apply CDerives.lamV
  apply CDerives.lamV
  refine letW (A := .ref A) (B := B) ?_ ?_
  · exact appW (.var (by csolo))
      (appW (appW (.var (by csolo)) (.alloc (by cdead)))
        (.withbor2 x (by cdead) hx hside hA hB))
  · exact pairW (appW (.var (by csolo)) (.free (by cdead))) (.var (by csolo))

/-! ### The unwinding local `[spec §80]`

The callback is at a row of abortive operations (`Row.Unwind`). When it unwinds, the finaliser
`localFin` frees the owner and drops its persistent contents. The lend is `withbor2UD` at the
finaliser's row `[]`. -/

/-- `withlocalu : A ⊸ U(∀'x ⊏ @b. Mut 'x A ⊸ F_Σ_M(['x] B)) ⊸ F_Σ(A ⊗ B)`. -/
def withlocalUTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (SM S : Row) : VTy :=
  .thunk (.arr A (.arr (cbUTy x bnd (.mut (.var x) A) B SM) (CTy.effOf S (.tensor A B))))

/-- The unwind finaliser: `λr. forget (free r)`. -/
def localFin : Expr := .val (.lam (.app forget (.app (.val (.prim .free)) (.var 0))))

/-- `λv. λcb. r ← alloc v; w ← withborU localFin; (r, b) ← w r cb; (free r, b)`. -/
def withlocalUE : Expr := .val (.lam (.val (.lam
  (bindE (.app (.val (.prim .alloc)) (.var 1))
    (bindE (withborUE localFin)
      (bindE (.app (.app (.var 0) (.var 1)) (.var 2))
        (.letpair (.var 0) (.pair (.app (.val (.prim .free)) (.var 1)) (.var 0)))))))))

theorem localFin_wf {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hA : A.Persistent) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ localFin (.val (.lolli (.ref A) .unit)) :=
  .lamV (appW (appW (.var (by csolo)) (.free (by cdead))) (release_persistent hA (by cdead)))

theorem localFin_closed : closedAt 0 localFin = true := rfl

theorem withlocalU_closed : closedAt 0 withlocalUE = true := by
  have h : closedAt 3 (withborUE localFin) = true := withborUE_closedAt rfl
  simp [withlocalUE, bindE, closedAt, Expr.val, Val.lam, Val.prim, h]

theorem withlocalU_wf {Δ : LifeCtx} {Γ : Ctx VTy} (x : LifeVar) (A B : VTy) {SM S : Row}
    (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hP : A.Persistent)
    (hS : SM.Unwind x) (hMS : RowLe SM S) (hSv : Row.divB S = false) :
    CDerives Δ Γ withlocalUE (.val (withlocalUTy x Δ.meetOfDom A B SM S)) := by
  unfold withlocalUE withlocalUTy
  refine .thunkV rfl (.lam (.lam ?_))
  refine .bind (A := .ref A) (part_split (.app (.val (.prim .alloc)) (.var 1)) 0 _).toP
    (.ret (appW (.var (by csolo)) (.alloc (by cdead)))) ?_
  refine .bind (part_split (withborUE localFin) 0 _).toP
    (.ret (.withbor2UD (SD := []) x (by cdead) hx hside hA hB hS hMS (RowLe.nil S) hSv
      (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) (localFin_wf hP (by cdead)))) ?_
  refine .effLet (A := .tensor (.ref A) B)
    (part_split (.app (.app (.var 0) (.var 1)) (.var 2)) 0 _).toP
    (fun _ => fun s hs hl => dead_noLive (P := fun s => s.ty.OwnFree) (by cdead) s hs hl)
    (fun _ => dead_noLive (P := fun s => ∃ A, s.ty = .bang A) (by cdead)) ?_ ?_
  · exact .app (part_split (.app (.var 0) (.var 1)) 0 _).toP
      (.app (part_split (.var 0) 0 _).toP (.force (T := withbor2UTyD x Δ.meetOfDom A B SM S)
        (C := .arr (.ref A) (.arr (cbUTy x Δ.meetOfDom (.mut (.var x) A) B SM)
          (CTy.effOf S (.tensor (.ref A) B)))) (by csolo) rfl) (by csolo))
      (by csolo)
  · exact .effSub (RowLe.nil S) (.ret (letW (.var (by csolo))
      (pairW (appW (.var (by csolo)) (.free (by cdead))) (.var (by csolo)))))

/-! ### The loop local `[spec §80]`

A local cell across an uncounted loop. The loop's state holds the cell's contents beside the
caller's state `S`; each observation lends the contents as a plain local (`withlocalE`: `alloc`,
`withbor2`, `free`) to the step the caller gave for it, so the caller's steps see a
`Mut 'x A` and their own state, never the cell or its contents. `next` finishes with the final
contents and `B`, or goes on; `close` ends with the final contents and `R`. -/

/-- A turn's callback at the answer `B`: `∀'x ⊏ @b. Mut 'x A ⊸ ['x] B`. -/
abbrev localCbTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .all x bnd (.lolli (.mut (.var x) A) (.box (.var x) B))

/-- The caller's steps: `!(S ⊸ cb (B ⊕ S)) ⊗ !(S ⊸ cb R)`, from its state to the turn's
callback, for `next` and `close`. -/
def loopStepsTy (x : LifeVar) (bnd : Lifetime.Life) (A S B R : VTy) : VTy :=
  .tensor (.bang (.lolli S (localCbTy x bnd A (.sum B S))))
    (.bang (.lolli S (localCbTy x bnd A R)))

/-- `withlocal_loop : A ⊗ S ⊸ !(S ⊸ cb (B ⊕ S)) ⊗ !(S ⊸ cb R) ⊸ U(Loop (A ⊗ B) (A ⊗ R))`. -/
def withlocalLoopTy (x : LifeVar) (bnd : Lifetime.Life) (A S B R : VTy) : VTy :=
  .lolli (.tensor A S)
    (.lolli (loopStepsTy x bnd A S B R) (.thunk (.loop (.tensor A B) (.tensor A R))))

/-- The loop's body, `Loop (A ⊗ B) (A ⊗ R)`'s. -/
abbrev localLoopC (A B R : VTy) : CTy := CTy.loopBody (.tensor A B) (.tensor A R)

/-- `next`, at `p : A ⊗ S` with the steps `nx`, `cl`: `forget cl; let (a, s) = p;
let (a', o) = withlocal a (nx s); case o {b ⇒ inj₁ (a', b) | s' ⇒ inj₂ (a', s')}`. -/
def loopNextE : Expr :=
  .seq (.app forget (.var 3))
    (.letpair (.var 2)
      (.letpair (.app (.app withlocalE (.var 1)) (.app (.var 6) (.var 0)))
        (.case (.var 0) (.inj₁ (.pair (.var 2) (.var 0))) (.inj₂ (.pair (.var 2) (.var 0))))))

/-- `close`: `forget nx; let (a, s) = p; withlocal a (cl s)`. -/
def loopCloseE : Expr :=
  .seq (.app forget (.var 4))
    (.letpair (.var 2) (.app (.app withlocalE (.var 1)) (.app (.var 5) (.var 0))))

/-- The loop's step, `λp. ⟨next, close⟩`, over the steps `nx` and `cl`. -/
def loopStepE : Expr := .val (.lam (withPair loopNextE loopCloseE))

/-- `λv. λst. let (nx, cl) = st; let g = unfold step in ⟨(g v) π₁, (g v) π₂⟩`. -/
def withlocalLoopE (A B R : VTy) : Expr := .val (.lam (.val (.lam
  (.letpair (.var 0)
    (elet (.app (.val (unfoldV (localLoopC A B R))) loopStepE)
      (withPair (.app (.app (.var 2) (.var 6)) (.val (.inj₁ .unit)))
        (.app (.app (.var 2) (.var 6)) (.val (.inj₂ .unit)))))))))

theorem mapV_effFree : ∀ A : VTy, (mapV A).1.effFree = true
  | .tvar 0 => rfl
  | .tensor A B => by
      simp [mapV, Expr.effFree, Expr.val, Val.lam, mapV_effFree A, mapV_effFree B]
  | .sum A B => by
      simp [mapV, Expr.effFree, Expr.val, Val.lam, mapV_effFree A, mapV_effFree B]
  | .box _ A => mapV_effFree A
  | .tvar (_ + 1) | .unit | .zero | .thunk _ | .code _ _ _ | .ref _ | .imm _ _ | .mut _ _
  | .bang _ | .unk | .mu _ | .int _ | .opq _ | .fam _ => rfl

theorem nodeV_effFree : ∀ C : CTy, (nodeV C).1.effFree = true
  | .ret A => by simp [nodeV, bindE, Expr.effFree, Expr.val, Val.lam, Val.unit, mapV_effFree A]
  | .amp C D => by
      simp [nodeV, Expr.effFree, Expr.val, Val.lam, Val.unit, Val.inj₁, Val.inj₂,
        nodeV_effFree C, nodeV_effFree D]
  | .eff _ _ _ _ _ _ _ C => by
      simp [nodeV, bindE, Expr.effFree, Expr.val, Val.lam, Val.unit, mapV_effFree (effAns C)]
  | .arr _ D => by simp [nodeV, Expr.effFree, Expr.val, Val.lam, Val.unit, nodeV_effFree D]
  | .all _ _ D => by simp [nodeV, Expr.effFree, Expr.val, Val.lam, Val.unit, nodeV_effFree D]
  | .top | .nuSys _ _ _ => rfl

theorem unfoldV_effFree (C : CTy) : (unfoldV C).1.effFree = true := by
  simp [unfoldV, selfV, zX, fBN, Expr.effFree, Expr.val, Val.lam, nodeV_effFree C]

theorem withlocalLoop_closed (A B R : VTy) : closedAt 0 (withlocalLoopE A B R) = true := by
  have hu := closedAt_mono _ (unfoldV_closed (localLoopC A B R)) (Nat.zero_le 4)
  have hw : ∀ n, closedAt n withlocalE = true := fun n =>
    closedAt_mono _ withlocal_closed (Nat.zero_le n)
  simp [withlocalLoopE, loopStepE, loopNextE, loopCloseE, withPair, elet, forget, unit', closedAt,
    Expr.val, Val.lam, Val.unit, hu, hw]

theorem withlocalLoop_effFree (A B R : VTy) : (withlocalLoopE A B R).effFree = true := by
  have hu := unfoldV_effFree (localLoopC A B R)
  have hw : withlocalE.effFree = true := rfl
  simp [withlocalLoopE, loopStepE, loopNextE, loopCloseE, withPair, elet, forget, unit', Expr.effFree,
    Expr.val, Val.lam, Val.unit, Val.inj₁, Val.inj₂, hu, hw]

/-- The loop local's type. Each turn's alloc → lend → free is the plain local's skeleton,
`withlocal_wf`, used whole (at the answer `B ⊕ S` for `next`, `R` for `close`); this proof adds
only `unfold`, the `&` of the two turns and the codata's eta. `[spec §80]` -/
theorem withlocalLoop_wf {Δ : LifeCtx} {Γ : Ctx VTy} (x : LifeVar) (A S B R : VTy)
    (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : ¬ VFree x S) (hR : ¬ VFree x R) :
    CDerives Δ Γ (withlocalLoopE A B R) (.val (withlocalLoopTy x Δ.meetOfDom A S B R)) := by
  have hBS : ¬ VFree x (.sum B S) := by simp [VFree, hB, hS]
  unfold withlocalLoopE withlocalLoopTy loopStepsTy
  refine .lamV (.lamV (.letpairV (.left (.right (deadSplit hΓ))) (.var (by csolo)) ?_))
  refine .eletV (A := .thunk (.arr (.tensor A S) (.loop (.tensor A B) (.tensor A R))))
    (.left (.left (.dead (.right (deadSplit hΓ))))) ?_ ?_
  · -- `unfold step`
    refine .bangE (.lolliE (.left (.left (.dead (.dead (deadSplit hΓ))))) ?_
      (.unfoldN (localLoopC A B R) (.tensor A S) (CTy.loopBody_nuOk _ _)
        (CTy.BindsFresh.of_hasAll rfl _) (by cdead)))
    rw [CTy.loopBody_instT]
    have hfl : Ctx.FlatLive (⟨.bang (.lolli S (localCbTy x Δ.meetOfDom A R)), true⟩ ::
        ⟨.bang (.lolli S (localCbTy x Δ.meetOfDom A (.sum B S))), true⟩ ::
        ⟨loopStepsTy x Δ.meetOfDom A S B R, false⟩ :: ⟨.tensor A S, false⟩ :: Γ) := by
      intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs; · rfl
      rcases List.mem_cons.mp hs with rfl | hs; · rfl
      rcases List.mem_cons.mp hs with rfl | hs; · simp at hl
      rcases List.mem_cons.mp hs with rfl | hs; · simp at hl
      exact dead_noLive (P := fun s => s.ty.flat = true) hΓ s hs hl
    refine .bangThunkV hfl rfl (.lam (.withI ?_ ?_))
    · -- `next`
      refine .ret (seqW (appW (.var (by csolo)) (.releaseBang (by cdead))) ?_)
      refine letW (.var (by csolo)) ?_
      refine letW (appW (appW (.var (by csolo)) (.bangE (.var (by csolo))))
        (appW (.var (by csolo)) (withlocal_wf x A (.sum B S) (by cdead) hx hside hA hBS))) ?_
      exact caseW (.var (by csolo)) (.sumI₁ (pairW (.var (by csolo)) (.var (by csolo))))
        (.sumI₂ (pairW (.var (by csolo)) (.var (by csolo))))
    · -- `close`
      refine .ret (seqW (appW (.var (by csolo)) (.releaseBang (by cdead))) ?_)
      refine letW (.var (by csolo)) ?_
      exact appW (appW (.var (by csolo)) (.bangE (.var (by csolo))))
        (appW (.var (by csolo)) (withlocal_wf x A R (by cdead) hx hside hA hR))
  · -- `⟨(g v) π₁, (g v) π₂⟩`
    have d : CDerives Δ (withCtx (⟨.thunk (.arr (.tensor A S) (.loop (.tensor A B) (.tensor A R))),
        true⟩ :: ⟨.bang (.lolli S (localCbTy x Δ.meetOfDom A R)), false⟩ ::
        ⟨.bang (.lolli S (localCbTy x Δ.meetOfDom A (.sum B S))), false⟩ ::
        ⟨loopStepsTy x Δ.meetOfDom A S B R, false⟩ :: ⟨.tensor A S, true⟩ :: Γ))
        (.app (.var 2) (.var 6)) (.comp (.loop (.tensor A B) (.tensor A R))) :=
      .app (.dead (.dead (.left (.dead (.dead (.dead (.right (deadSplit hΓ))))))))
        (.force (T := .thunk (.arr (.tensor A S) (.loop (.tensor A B) (.tensor A R))))
          (C := .arr (.tensor A S) (.loop (.tensor A B) (.tensor A R)))
          (.there (.there (.here (.cons (.cons (.cons (.cons hΓ.toP))))))) rfl)
        (.there (.there (.there (.there (.there (.there (.here hΓ.toP)))))))
    exact .thunkV rfl (.loopIn (.withI (.proj₁ (.loopOut d)) (.proj₂ (.loopOut d))))

/-! ### The local family `[spec §80]`

The checker's typed term has one node and one rule for every local: `TExpr.withlocal` and
`TDerivesAt.withlocal`/`TDerivesP.withlocal`, indexed by a `LocalKind`. A kind is data: it
selects the side condition (`LocalOK`), the result type (`localTy`), the erased core term
(`localE`) and the derived kernel lemma the rule erases to (`LocalKind.wf`). Adding a kind adds a
constructor and a clause to each function here; the rule, the node and their pinned templates
(`scripts/pin/`) do not change. -/

/-- The kinds of scoped local. `[spec §80]` -/
inductive LocalKind where
  /-- The plain local (`withlocalE`). -/
  | plain
  /-- The unwinding local (`withlocalUE`): the callback at the abortive row `SM`, the scope at
  `S`. -/
  | unwind (SM S : Row)
  /-- The loop local (`withlocalLoopE`): the contents `A`, the caller's state `S`, `next`'s
  answer `B` and `close`'s `R`. Its type and term are the kind's own; the node's `A` and `B` are
  the kind's. -/
  | loop (A S B R : VTy)
  deriving Inhabited

/-- The side condition every kind shares, plain's whole: `x` fresh, `Δ ⊢ A ⊒ @b` for some
defined `@b`, and `x` free in neither `A` nor `B`. `[spec §80]` -/
abbrev LocalBase (Δ : LifeCtx) (x : LifeVar) (A B : VTy) : Prop :=
  Δ.find? x = none ∧ (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧ ¬ VFree x A ∧ ¬ VFree x B

/-- The kind's side condition at the lifetime context `Δ`, the callback's fresh lifetime `x`,
the contents `A` and the callback's answer `B`: `LocalBase` and the kind's own. `[spec §80]` -/
def LocalOK : LocalKind → LifeCtx → LifeVar → VTy → VTy → Prop
  | .plain, Δ, x, A, B => LocalBase Δ x A B
  | .unwind SM S, Δ, x, A, B =>
      LocalBase Δ x A B ∧ A.Persistent ∧ SM.Unwind x ∧ RowLe SM S ∧ Row.divB S = false
  | .loop A S B R, Δ, x, _, _ => LocalBase Δ x A B ∧ ¬ VFree x S ∧ ¬ VFree x R

/-- The kind's type at `Δ`. `[spec §80]` -/
def localTy : LocalKind → LifeCtx → LifeVar → VTy → VTy → VTy
  | .plain, Δ, x, A, B => withlocalTy x Δ.meetOfDom A B
  | .unwind SM S, Δ, x, A, B => withlocalUTy x Δ.meetOfDom A B SM S
  | .loop A S B R, Δ, x, _, _ => withlocalLoopTy x Δ.meetOfDom A S B R

/-- The kind's core term. `[spec §80]` -/
def localE : LocalKind → Expr
  | .plain => withlocalE
  | .unwind .. => withlocalUE
  | .loop A _ B R => withlocalLoopE A B R

theorem LocalKind.closed : ∀ k : LocalKind, closedAt 0 (localE k) = true
  | .plain => withlocal_closed
  | .unwind .. => withlocalU_closed
  | .loop A _ B R => withlocalLoop_closed A B R

theorem LocalKind.effFree : ∀ k : LocalKind, (localE k).effFree = true
  | .plain => rfl
  | .unwind .. => rfl
  | .loop A _ B R => withlocalLoop_effFree A B R

/-- Every kind's term has its type, by the kind's derived kernel lemma. `[spec §80]` -/
theorem LocalKind.wf {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {A B : VTy} :
    ∀ k : LocalKind, Ctx.Dead Γ → LocalOK k Δ x A B →
      CDerives Δ Γ (localE k) (.val (localTy k Δ x A B))
  | .plain, hΓ, ⟨hx, hside, hA, hB⟩ => withlocal_wf x A B hΓ hx hside hA hB
  | .unwind .., hΓ, ⟨⟨hx, hside, hA, hB⟩, hP, hS, hMS, hSv⟩ =>
      withlocalU_wf x A B hΓ hx hside hA hB hP hS hMS hSv
  | .loop A' S B' R, hΓ, ⟨⟨hx, hside, hA, hB⟩, hS, hR⟩ =>
      withlocalLoop_wf x A' S B' R hΓ hx hside hA hB hS hR

end BoCa.Fig16.LogRel.Core
end
