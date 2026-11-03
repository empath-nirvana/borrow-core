import Core.LetDtorFiles
import Core.AwaitCancel

/-!
# Core — the cancel exit runs the destructors  `[spec §29a, §62]`

A cancel is a resume of the cancellable wait with `inr ()`, on which `await_n` raises the cancel
target (`[await-c]`, §29a; `await_cancelled`). So the cancel exit is the raise exit: the two files
held across an `await` by `[let-dtor]` are closed by the frame's `drop_ctx` when the cancel's raise
unwinds through it. Nothing is added: `[let-dtor]` at `M = await_1`.

The one premise the await row adds is `[then]`'s `hfin`: the wait is read for its cancel row
(`OpSig.finRead`), which must record the destructors' row, `await⟨{close}⟩` here (`hfin_await`).
That is §27's record of what a cancel's unwind may perform, the capability check of the cancel
path.

The closed program is the immediate scheduler of §29a (`AwaitCancel.stickyScope`) at the outer row
`{close}`, resuming the wait with *cancelled* at once, under `with_fs`:

    with_fs (sched (f₁ ← alloc 1; f₂ ← alloc 2; let _ = await_1 in drop_ctx unwind drop_ctx))
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LetDtor.Cancel
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.LetDtor.Files
open BoCa.Fig16.LogRel.Core.AwaitCancel (awaitF cancelled cancellable_await cancelTarget_cancelled
  Esched csSched flag_persistent)
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag)
open BoCa.BoLo (Heap Steps Step1 Kont freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The cancel row of the wait: the destructors' row. -/
abbrev FD : CTy := CTy.effOf SD .unit

/-- The cancel rows: `{close}` at `await`. -/
def fs2 : Nat → CTy := fun j => if j = 0 then FD else .ret .unit

/-- The body's row: `{await⟨{close}⟩, cancelled, close}`. -/
abbrev S2 : Row := [awaitF FD, cancelled, fcloseSig]

theorem ofEff_S2 : Row.ofEff 1 Esched 0 fs2 csSched ++ SD = S2 := rfl

theorem S2_nz : S2.NZ := by
  intro o ho
  simp only [S2, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> decide

theorem S2_uniq : S2.Uniq := by simp [Row.Uniq, awaitF, cancelled, fcloseSig]

theorem S2_not_unrD : ¬ S2.UnrD := by
  rintro ⟨o, ho, h⟩
  simp only [S2, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> rcases h with h | ⟨h, -⟩ <;>
    simp_all [awaitF, cancelled, fcloseSig, capB, VTy.isZero]

theorem SD_le_S2 : RowLe SD S2 := by
  intro n i o h
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
  simp only [SD, List.mem_singleton] at hm
  subst hm
  exact ⟨fcloseSig, rfl, OpSig.LeF.refl _⟩

/-- `F_{close} 1 ⋈ {close} ≤ F_{close} 1`: the wait's cancel row already records the destructors'
row. -/
theorem thenLe_FD : ThenLe FD SD FD := by
  have hcap : ∀ n i o, Row.find SD n i = some o → capB o.q o.B = false := by
    intro n i o h
    have := (Row.find_mem h).1
    simp only [SD, List.mem_singleton] at this
    subst this; rfl
  rw [ThenLe]
  refine .inr ⟨rfl, ?_, ?_⟩
  · intro n i o h
    rw [CTy.rowOf_effOf] at h ⊢
    exact ⟨o, h, OpSig.Sig.refl o, fun hc => by rw [hcap n i o h] at hc; cases hc⟩
  · intro n i o h
    refine ⟨o, by rw [CTy.rowOf_effOf]; exact h, OpSig.Sig.refl o, fun hc => ?_⟩
    rw [hcap n i o h] at hc; cases hc

/-- **`hfin` at the await row**: the wait's cancel row records `{close}`; the cancel target and
`close` are not read. -/
theorem hfin_await :
    ∀ n i o, Row.find S2 n i = some o → o.finRead = true → ThenLe o.fin SD o.fin := by
  intro n i o hf hr
  have hm := (Row.find_mem hf).1
  simp only [S2, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact thenLe_FD
  · simp [OpSig.finRead, cancelled, capB, OpSig.abort, VTy.isZero] at hr
  · simp [OpSig.finRead, fcloseSig, capB] at hr

/-- `await_1` at the body's row. -/
theorem d_awaitM {Δ : LifeCtx} (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives Δ Γ' (awaitE 1) (.comp (CTy.effOf S2 .unit)) :=
  .effAwait hΓ rfl (cancellable_await _) rfl rfl cancelTarget_cancelled

/-- **The two files held across a cancellable wait**: `[let-dtor]` at `M = await_1`. -/
theorem d_twoFilesAwait {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (twoFiles Γ.length (awaitE 1)) (.comp (CTy.effOf S2 .unit)) :=
  d_twoFilesAt hΓ S2_nz S2_uniq S2_not_unrD SD_le_S2 hfin_await d_awaitM

/-! ### The immediate scheduler at the outer row `{close}` -/

/-- The scheduler's answer: `U(Flag ⊸ F_{close} Flag)`. -/
abbrev StR : VTy := .thunk (.arr Flag (CTy.effOf SD Flag))

/-- `λx. return (λc. inj₁ x)`. -/
def hrS : Expr := .val (.lam (.val (.lam (.inj₁ (.var 1)))))

/-- `λ(v, κ). return (λc. κ.resume c to g. g c)`. -/
def clS : Expr :=
  .val (.lam (.letpair (.var 0) (.val (.lam
    (bindE (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 0)) (.app (.var 0) (.var 1)))))))

/-- `λ_. return (λc. inj₂ ())`. -/
def ccS : Expr := .val (.lam (.val (.lam (.inj₂ (.val .unit)))))

def clsS : Expr := .pair clS (.pair ccS (.val .unit))

/-- The immediate scheduler, from the cancelled flag. -/
def sched (e : Expr) : Expr :=
  bindE clsS (bindE hrS (bindE (hndTerm 1 [.lin, .cancel] 0 1 e)
    (bindE (.val (.inj₂ .unit)) (.app (.var 1) (.var 0)))))

theorem SD_not_unr : ¬ SD.Unr := Row.not_unr_of_not_cancels SD_not_cancels

theorem d_hrS {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ hrS (.val (retTy SD .unit StR)) :=
  .bangThunkV (banged_dead hΓ) rfl (.lam (.effSub (RowLe.nil SD) (.ret (.thunkV rfl
    (.lam (.effSub (RowLe.nil SD) (.ret (.sumI₁
      (.var (.skip flag_persistent (.here hΓ.toP)))))))))))

theorem d_ccS {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ ccS (.val (clauseTy SD StR (.cancel, .unit, .zero))) :=
  .bangThunkV (banged_dead hΓ) rfl (.lam (.effSub (RowLe.nil SD) (.ret (.thunkV rfl
    (.lam (.effSub (RowLe.nil SD) (.ret (.sumI₂ (.unitI (.drop rfl (.drop rfl hΓ.toP)))))))))))

theorem d_clS {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clS (.val (clauseTy SD StR (.lin, .unit, .sum .unit .unit) FD)) := by
  refine .bangThunkV (banged_dead hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .effSub (RowLe.nil SD) (.ret (.thunkV rfl (.lam ?_)))
  refine .effLet (A := StR) (.dup rfl (.left (.right (.dead (deadSplit hΓ)))))
    (fun h => absurd h SD_not_cancels) (fun h => absurd h SD_not_unr)
    (.app (.right (.left (.dead (.dead (deadSplit hΓ)))))
      (.proj₁ (.force (C := .amp (.arr (.sum .unit .unit) (CTy.effOf SD StR)) .top)
        (.there (.here (by cdead)))))
      (.here (by cdead))) ?_
  exact .app (.left (.right (.dead (.right (.dead (deadSplit hΓ))))))
    (.force (.here (by cdead))) (.there (.here (.cons (.drop rfl (.cons hΓ.toP)))))

/-- **The scheduler is typed** at the outer row `{close}`, around any body at `S2`. -/
theorem d_schedG {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {e : Expr}
    (he : CDerives Δ (⟨retTy SD .unit StR, false⟩ :: ⟨clausesTy SD StR Esched fs2, false⟩ :: kill Γ)
      e (.comp (CTy.effOf S2 .unit))) :
    CDerives Δ Γ (sched e) (.comp (CTy.effOf SD Flag)) := by
  refine .bind (split_kill Γ).toP (.ret (.tensorI (deadSplit (kill_dead Γ))
    (d_clS (kill_dead Γ)) (.tensorI (deadSplit (kill_dead Γ)) (d_ccS (kill_dead Γ))
      (.unitI (kill_dead Γ).toP)))) ?_
  refine .bind (.right (split_kill Γ).toP) (.ret (d_hrS (.cons (kill_dead Γ)))) ?_
  refine .effLet (A := StR) (.left (.left (split_kill Γ).toP))
    (fun h => absurd h SD_not_cancels) (fun h => absurd h SD_not_unr) ?_ ?_
  · refine CDerives.effHandleCs (S := SD) (E := Esched) (n := 1) (A := .unit) (R := StR) fs2 csSched
      (.left (.left (deadSplit (kill_dead Γ)))) (.left (.right (deadSplit (kill_dead Γ))))
      (.here (.cons (kill_dead Γ).toP)) (.there (.here (kill_dead Γ).toP))
      (by decide) (by simp [fcloseSig]) (by simp) (by decide) ?_
    rw [ofEff_S2]
    exact he
  · refine .bind (A := Flag) (.right (.dead (.dead (deadSplit hΓ))))
      (.ret (.sumI₂ (.unitI (by cdead)))) ?_
    exact .app (.right (.left (.dead (.dead (deadSplit hΓ)))))
      (.force (C := .arr Flag (CTy.effOf SD Flag)) (.there (.here (by cdead))))
      (.here (by cdead))

/-! ### The closed program -/

/-- `with_fs (sched (f₁ ← alloc 1; f₂ ← alloc 2; let _ = await_1 in drop_ctx unwind drop_ctx))`. -/
def cancelProg : Expr := withFs (sched (twoFiles 4 (awaitE 1)))

theorem d_cancelProg : CDerives LifeCtx.empty [] cancelProg (.comp (.ret Flag)) := by
  refine d_withFsG (S := []) (A := Flag) (by simp) rfl ?_
  show CDerives _ _ _ (.comp (CTy.effOf SD Flag))
  exact d_schedG (.cons (.cons .nil))
    (d_twoFilesAwait (Γ := [_, _, _, _]) (.cons (.cons (.cons (.cons .nil)))))

/-- **Resource safety on the cancel exit.** -/
theorem cancelProg_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem cancelProg μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety flag_persistent d_cancelProg hs

/-- The same body under the recording `with_fs`. -/
def cancelLog : Expr := withLogCell (withFsLog (sched (twoFiles 4 (awaitE 1))))

/-- The run answers `(inr (), log)`, the cancel, with `log` the given number and no cell left. -/
def cancelledWithLog (e : Expr) (l : UInt32) : Bool :=
  match eval e with
  | .value ⟨.pair (.inj₂ .unit) (.prim (.lit (.i32 b))), _⟩ false => b == l
  | _ => false

/-- **On the cancel, `f₂` is closed before `f₁`**, the scheduler answers *cancelled*, and no cell
is left. -/
theorem cancel_order : cancelledWithLog cancelLog 21 = true := by decide

end BoCa.Fig16.LogRel.Core.LetDtor.Cancel

end
