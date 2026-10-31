import Core.Decl

/-!
# Core — a declared value lent into a computation that may abort  `[spec §19, §42]`

A declared value `N = A ⊗ Tok` (`Core/Decl.lean`) is not `OwnFree` (`decl_not_ownFree`), so
`[let]`'s `hW` refuses it in the rest of the context of a computation that may abort. Lent, it is
not in that context: the owner's cell `Ref N` is consumed by the lend, and the computation holds
only the loan, which is `OwnFree` at every payload (`decl_loan_ownFree`). Where the lend ends
decides what the kernel asks for:

| the abort | lend form | what the kernel asks | program |
|---|---|---|---|
| handled inside the loan | `withbor` (1), pure callback | nothing more: the callback returns, the lend ends, the owner gets the value back | `declInside` |
| crosses the loan | `withbor1U`, the unwinding form | a closed finaliser `d : Ref N ⊸ 1`, run on the source when the lend unwinds | `declAcross` |

At the unwinding form any closed `d` of that type is accepted, and one that consumes the value is
derived: `declFin` frees the cell and burns the token (`d_declFin`). The checker passes the
source's derived destructor `dtorE (Ref N)` (`Frontend/Check/Consts.lean`, `finaliser`), which a
declared type has none of (`decl_ref_no_dtor`).

Both programs run, under every allocator, to their answer at the empty memory: the token is
burned on each path (`declInside_runs`, `declAcross_answers`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DeclLend
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.BoLo (Heap Steps)
open BoCa.Lifetime (LifeCtx)
open BoCa.Programs (alloc' free' app2)

/-! ### The kernel facts -/

/-- **A loan of a declared value holds no owned cell**: `[let]`'s `hW` admits it across an
abort.  `[spec §19, §42]` -/
theorem decl_loan_ownFree (a : Lifetime.Life) (A : VTy) :
    (VTy.imm a (declTy A)).OwnFree ∧ (VTy.mut a (declTy A)).OwnFree :=
  ⟨.imm a _, .mut a _⟩

/-- **The checker's finaliser does not exist at a declared type**: the unwinding lend's finaliser
the checker passes is the source's derived destructor, and `Ref N` has none.  `[spec §19, §42]` -/
theorem decl_ref_no_dtor (A : VTy) : ¬ HasDtor (.ref (declTy A)) :=
  not_hasDtor_ref (decl_linear A).2

/-! ### The declared value -/

/-- The declared type with payload `1`. -/
abbrev N₁ : VTy := declTy .unit

/-- `((), mint ())`: E7's constructor, minting the token. -/
def mkDecl : Expr := .pair (.val .unit) (.app mintE (.val .unit))

theorem d_mkDecl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ mkDecl (.val N₁) :=
  pairW (.unitI (by cdead)) (appW (.unitI (by cdead)) (.tokMint (by cdead)))

/-! ### The abort handled inside the loan

    r ← alloc ((), mint ());
    let (r, res) = withbor r (Λ. λv. to_result (y ← raise (); y; forget v) to s. [s]);
    let (u, t) = free r; u; burn t; res

`v : Imm 'x N₁` is live across the raise (`[let]` at `Fail`'s row): `hW` holds, the loan being
`OwnFree`. `to_result` catches the raise inside the callback, so the callback returns and the lend
is the pure `withbor` (1). The owner gets `r` back and consumes the value by `burn`. -/

/-- `y ← raise (); y; forget v`, `v` at index `2` (under `to_result`'s two bindings). -/
def holdRaise : Expr :=
  .app (.val (.lam (.seq (.var 0) (.app forget (.var 3))))) raiseU

theorem d_holdRaise {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {T₁ T₂ : VTy}
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨T₁, false⟩ :: ⟨T₂, false⟩ :: ⟨.imm a N₁, true⟩ :: ⟨.unit, false⟩ :: Γ)
      holdRaise (.comp (CTy.effOf Sf .unit)) := by
  refine .effLet (A := .unit) (.dead (.dead (.right (.dead (deadSplit hΓ)))))
    (fun _ s hs hl => ?_) (fun h => absurd h Sf_not_unr) (d_raiseU rfl (by cdead)) ?_
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | rfl | hs
    · simp at hl
    · simp at hl
    · exact (decl_loan_ownFree a .unit).1
    · simp at hl
    · exact dead_noLive (P := fun s => s.ty.OwnFree) hΓ s hs hl
  · exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (seqW (.var (by csolo)) (appW (.var (by csolo)) (.forgetImm (by cdead)))))

/-- `Λ. λv. to_result holdRaise to s. [s]`. -/
def declInCb : Expr := .val (.lam (.val (.lam (bindE (toResult holdRaise) (.var 0)))))

theorem d_declInCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ declInCb (.val (.all 0 LifeCtx.empty.meetOfDom
      (.lolli (.imm (.var 0) N₁) (.box (.var 0) (.sum .unit .unit))))) := by
  refine callbackW ok_empty rfl hΓ (.ofRet ?_)
  refine .bind (.left (.dead (deadSplit hΓ)))
    (d_toResultG (S := []) (A := .unit) (by simp) rfl (d_holdRaise hΓ)) ?_
  exact .ret (.boxI (.var (.here (.cons (.cons hΓ.toP))))
    (outlives_head (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (.cons (.cons hΓ))))

/-- **The declared value lent into a computation that aborts, the abort handled inside the
loan.** -/
def declInside : Expr :=
  bindE (.app alloc' mkDecl)
    (.letpair (app2 withbor (.var 0) declInCb)
      (.letpair (.app free' (.var 1)) (.seq (.var 1) (.seq (.app burnE (.var 0)) (.var 2)))))

/-- **The kernel admits it.**  `[spec §42]` -/
theorem d_declInside :
    CDerives LifeCtx.empty [] declInside (.comp (.ret (.sum .unit .unit))) := by
  refine .bind (A := .ref N₁) .nil (.ret (appW (d_mkDecl (by cdead)) (.alloc (by cdead)))) ?_
  refine .ret (letW (appW (d_declInCb (by cdead)) (appW (.var (by csolo))
    (.withbor1 (A := N₁) (B := .sum .unit .unit) 0 (by cdead) rfl (fun _ h => by rcases h with h | h <;> simp [VFree] at h)
      (by simp [VFree]) (by simp [VFree])))) ?_)
  exact letW (appW (.var (by csolo)) (.free (by cdead)))
    (seqW (.var (by csolo)) (seqW (appW (.var (by csolo)) (.tokBurn (by cdead))) (.var (by csolo))))

/-- **Every run of `declInside` continues to a value at the empty memory**: the token is
burned. -/
theorem declInside_runs {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem declInside μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs (by decide) d_declInside hs
  exact ⟨v, hv⟩

/-! ### The abort crossing the loan

    to_result {
      r ← alloc ((), mint ());
      (r, z) ← withborU declFin r (Λ. λv. forget v; raise ());
      absurd z }

The raise crosses the lend, by its unwinding form: the lend ends, `declFin` runs on `r`, freeing
the cell and burning the token, and `to_result` answers `inj₂ ()`. -/

/-- The written finaliser `λr. let (u, t) = free r; u; burn t`. -/
def declFin : Expr :=
  .val (.lam (.letpair (.app free' (.var 0)) (.seq (.var 1) (.app burnE (.var 0)))))

theorem declFin_closed : closedAt 0 declFin = true := by decide

/-- **A finaliser that consumes the declared value.** -/
theorem d_declFin {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ declFin (.val (.lolli (.ref N₁) .unit)) :=
  .thunkV rfl (.lam (.ret (letW (appW (.var (by csolo)) (.free (by cdead)))
    (seqW (.var (by csolo)) (appW (.var (by csolo)) (.tokBurn (by cdead)))))))

/-- `Λ. λv. forget v; raise ()`, at the unwinding row. -/
def declRaiseCb : Expr := .val (.lam (.val (.lam (.seq (.app forget (.var 0)) raiseU))))

theorem d_declRaiseCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ declRaiseCb (.val (cbUTy 0 LifeCtx.empty.meetOfDom
      (.imm (.var 0) N₁) .zero Sf)) :=
  callbackUW ok_empty rfl hΓ
    (.unitE (.left (.dead (deadSplit hΓ))) (appW (.var (by csolo)) (.forgetImm (by cdead)))
      (d_raiseU rfl (by cdead)))

/-- The handled body: `r ← alloc ((), mint ()); (r, z) ← withborU declFin r declRaiseCb;
absurd z`. -/
def declAcrossBody : Expr :=
  bindE (.app alloc' mkDecl)
    (bindE declRaiseCb
      (bindE (withborUE declFin)
        (.app (.val (.lam (.letpair (.var 0) (absurdE (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

/-- **The declared value lent into a computation whose abort crosses the loan.** -/
def declAcross : Expr := toResult declAcrossBody

theorem d_declAcrossBody :
    CDerives LifeCtx.empty [⟨retTy [] .zero (.sum .zero .unit), false⟩,
      ⟨clausesTy [] (.sum .zero .unit) Ef, false⟩] declAcrossBody
      (.comp (CTy.effOf Sf .zero)) := by
  refine .bind (A := .ref N₁) (.dead (.dead .nil))
    (.ret (appW (d_mkDecl (by cdead)) (.alloc (by cdead)))) ?_
  refine .bind (.right (.dead (.dead .nil))) (.ret (d_declRaiseCb (by cdead))) ?_
  refine .bind (.right (.right (.dead (.dead .nil))))
    (.ret (.withbor1U (A := N₁) (B := .zero) (S := Sf) 0 (by cdead) rfl (fun _ h => by rcases h with h | h <;> simp [VFree] at h)
      (by simp [VFree]) (by simp [VFree]) (Sf_unwind 0) declFin_closed (d_declFin (by cdead)))) ?_
  refine .effLet (A := .tensor (.ref N₁) .zero) (.left (.left (.left (.dead (.dead .nil)))))
    (fun _ => Ctx.Dead.drops (by cdead)) (fun h => absurd h Sf_not_unr) ?_ ?_
  · refine .app (.left (.right (.left (.dead (.dead .nil))))) ?_ (.there (.here (by cdead)))
    exact .app (.left (.dead (.right (.dead (.dead .nil))))) (.force (.here (by cdead)))
      (.there (.there (.here (by cdead))))
  · refine .tensorE (.left (deadSplit (by cdead))) (.var (.here (by cdead))) ?_
    exact .zeroE (.left (.right (deadSplit (by cdead)))) (.var (.here (by cdead)))

/-- **The kernel admits it, at the written finaliser.**  `[spec §19, §42]` -/
theorem d_declAcross :
    CDerives LifeCtx.empty [] declAcross (.comp (.ret (.sum .zero .unit))) :=
  d_toResult (S := []) (by simp) rfl d_declAcrossBody

/-- **Every run of `declAcross` continues to `inj₂ ()` at the empty memory**: the finaliser
burned the token. -/
theorem declAcross_answers {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem declAcross μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.inj₂ Val.unit)) := by
  obtain ⟨v, hv, ls, hP⟩ := adequacyD_obs (by decide) d_declAcross hs
  rwa [vP_zero_sum hP] at hv

end BoCa.Fig16.LogRel.Core.DeclLend

end
