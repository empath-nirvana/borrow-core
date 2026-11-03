import Core.LetDtorCancel

/-!
# Core — files held across a suspension, the stored continuation as a resource  `[spec §28, §62]`

`y : 1 ↠^cancel 1` (name `6`) suspends: its handler receives `κ` and may store it. `κ`'s type is
`kTy Σ R cancel 1 F = U((1 ⊸ F_Σ R) & F_{F ⊕ Σ} 1)`: a thunk of a `&` whose second component is the
cancel, the paper's `↓N = N & 1` with `drop_N = π₂`. So `κ` is a resource whose destructor, by its
type, is `λk. k.2` (`dropOf_kappa`, `dropOk_kappa`, typed by `d_kDtor`), at the row of `y`'s cancel
row ahead of `Σ`.

The body holds two files across `y` by `[let-dtor]` (`Core/LetDtorFiles.lean`). The cancel row of `y` is the
destructors' row `F_{close} 1` (`[then]`'s `hfin` reads it: `y` is capturable), so a cancel of `κ`
may run `close`, and the handler's clause types `κ.2` at a row that admits it.

* (a) `ySeqResume`: the clause resumes `κ`; the body goes on and closes the files at the scope's
  end (`drop_ctx` as the continuation).
* (b) the level-triggered cancel of a stored `κ`: `Cancel.cancelProg` (the scheduler's
  answer is a closure holding `κ`, resumed with *cancelled*).
* (c) `ySeqDrop`: the clause stores `κ` in a cell, takes it back, and drops it by its destructor
  `κ.2`: the cancel runs the dead region of `κ`, whose `ubind` fires `[finalise-cancel]`, so
  `drop_ctx` closes both files.

Each program is a closed `CDerives` derivation: `resourceSafety` covers it, and `eval` records
the closes, `21` (f₂ then f₁), in each.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LetDtor.Suspend
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.LetDtor.Files
open BoCa.Fig16.LogRel.Core.LetDtor.Cancel (FD thenLe_FD)
open BoCa.BoLo (Heap Steps Step1 Kont freeE performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free')

/-! ### The continuation's destructor -/

/-- **`drop_κ = π₂`**: a cancellable continuation's destructor is its cancel component,
`λk. k.2 : kTy Σ R cancel B F ⊸ cancelTy Σ F`. At a must-resume operation the cancel component is
`⊤`, which has no destructor: such a `κ` must be resumed. -/
theorem d_kDtor {Δ : LifeCtx} {S : Row} {R B : VTy} {F : CTy} (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam (.app (.var 0) (.val (.inj₂ .unit)))))
      (.comp (.arr (kTy S R .cancel B F) (cancelTy S F))) :=
  .lam (.proj₂ (.force (C := .amp (.arr B (CTy.effOf S R)) (cancelTy S F)) (.here hΓ.toP)))

/-- At a cancel row `F_{Σ_F} 1`, the cancel component is at `F_{Σ_F ++ Σ} 1`. -/
theorem cancelTy_effOf (S SF : Row) : cancelTy S (CTy.effOf SF .unit) = CTy.effOf (SF ++ S) .unit := by
  unfold cancelTy
  rw [CTy.rowOf_effOf]
  cases SF <;> rfl

/-- **A stored `κ` has a destructor by its type**: `kTy` is `U(C & F_{Σ_F ++ Σ} 1)`, whose
destructor is `closeDropB = λk. k.2` (`dropOf`), at the row `Σ_F ++ Σ`, at every declaration. So
`[let-dtor]` holds a stored `κ` live across an abortive point and drops it by its cancel. -/
theorem dropOk_kappa {Δ : LifeCtx} {S SF : Row} {R B : VTy} {decl : Opaque → Option Expr} :
    DropOk Δ (SF ++ S) decl (kTy S R .cancel B (CTy.effOf SF .unit)) := by
  show DropOk Δ (SF ++ S) decl (.thunk (.amp _ (cancelTy S (CTy.effOf SF .unit))))
  rw [cancelTy_effOf]
  exact .close (RowLe.refl _)

/-- `κ`'s destructor by type is `d_kDtor`'s term. -/
theorem dropOf_kappa {S SF : Row} {R B : VTy} {decl : Opaque → Option Expr} :
    dropOf decl (kTy S R .cancel B (CTy.effOf SF .unit)) = some closeDropB := rfl

/-! ### The suspending operation and the body -/

/-- `y : 1 ↠^cancel 1`, the operation `0` of the name `6`, its cancel row `F_{close} 1`. -/
def ySig : OpSig := ⟨6, 0, .cancel, .unit, .unit, FD, false⟩

abbrev Ey : List (Qual × VTy × VTy) := [(.cancel, .unit, .unit)]

def fsY : Nat → CTy := fun _ => FD

/-- The body's row `{y⟨close⟩, close, open}`. -/
abbrev SY : Row := [ySig, fcloseSig, fopenSig]

theorem ofEff_SY : Row.ofEff 6 Ey 0 fsY rcsNil ++ SO = SY := rfl

theorem SY_nz : SY.NZ := by
  intro o ho
  simp only [SY, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> decide

theorem SY_uniq : SY.Uniq := by simp [Row.Uniq, ySig, fcloseSig, fopenSig]

theorem SY_not_unrD : ¬ SY.UnrD := by
  rintro ⟨o, ho, h⟩
  simp only [SY, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · rcases h with h | ⟨-, h⟩
    · cases h
    · simp [ySig, FD, CTy.effOf, CTy.FinUnr, fcloseSig] at h
  · rcases h with h | ⟨h, -⟩
    · cases h
    · simp [fcloseSig, capB] at h
  · rcases h with h | ⟨h, -⟩
    · cases h
    · simp [fopenSig, capB] at h

theorem SD_le_SY : RowLe SD SY := by
  intro n i o h
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
  simp only [SD, List.mem_singleton] at hm
  subst hm
  exact ⟨fcloseSig, rfl, OpSig.LeF.refl _⟩

/-- `hfin`: `y` is capturable, and its cancel row records the destructors' row. -/
theorem hfin_y : ∀ n i o, Row.find SY n i = some o → o.finRead = true → ThenLe o.fin SD o.fin := by
  intro n i o hf hr
  have hm := (Row.find_mem hf).1
  simp only [SY, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact thenLe_FD
  · simp [OpSig.finRead, fcloseSig, capB] at hr
  · simp [OpSig.finRead, fopenSig, capB] at hr

theorem d_yM {Δ : LifeCtx} (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives Δ Γ' (performE (opArgE 6 0 (.val .unit))) (.comp (CTy.effOf SY .unit)) :=
  .effPerform (o := ySig) rfl rfl rfl (.unitI hΓ.toP)

/-- **Two files held across the suspension `y`**, by `[let-dtor]`. -/
theorem d_twoFilesY {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (twoFiles Γ.length (performE (opArgE 6 0 (.val .unit))))
      (.comp (CTy.effOf SY .unit)) :=
  d_twoFilesAt hΓ SY_nz SY_uniq SY_not_unrD SD_le_SY rfl hfin_y d_yM

/-- **When `κ` is cancelled, the files' frame runs `close f₂; close f₁`**: `files_cancel_run` at
the body `M = y ()`, whose run, inside `κ`'s cancel, reaches the cancel.  `[spec §62]` -/
theorem y_cancel_run (k : Nat) {μ μ' : Heap} (N : Expr) {f₁ f₂ : Val} {γ₀ : List Val}
    (hγ : ∀ v ∈ f₂ :: f₁ :: γ₀, closedAt 0 v.1 = true) (hl : k ≤ γ₀.length) (K K' : Kont)
    {err : Option Val} (hK : K'.Catches 0 = false)
    (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 (f₂ :: f₁ :: γ₀) (performE (opArgE 6 0 (.val .unit)))) μ'
      (K'.plug (BoCa.BoLo.raiseE (.val (BoCa.BoLo.cancelVal err))))) :
    Steps (ℍ := ℍ) μ (K.plug (substAll (f₂ :: f₁ :: γ₀)
        (letDE (dsFiles k) N (performE (opArgE 6 0 (.val .unit)))))) μ'
      (K.plug (BoCa.BoLo.cfinE (BoCa.BoLo.cancelVal err)
        (bindE (.app (.val (.lam closeB)) (.val f₂))
          (bindE (.app (.val (.lam closeB)) (.val f₁)) (.val .unit))))) :=
  Cancel.files_cancel_run k N _ hγ hl K K' hK hM

/-! ### The handlers -/

/-- (a) `λ(v, κ). κ.1 v`: resume. -/
def clRes : Expr := .val (.lam (.letpair (.var 0) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.var 1))))

/-- (c) `λ(v, κ). v; c ← alloc κ; k ← free c; k.2`: store `κ`, take it back, drop it. -/
def clDrop : Expr :=
  .val (.lam (.letpair (.var 0) (.seq (.var 1)
    (bindE (.app alloc' (.var 0)) (bindE (.app free' (.var 0))
      (.app (.var 0) (.val (.inj₂ .unit))))))))

abbrev KY : VTy := kTy SO .unit .cancel .unit FD

theorem d_clRes {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clRes (.val (clauseTy SO .unit (.cancel, .unit, .unit) FD)) := by
  refine .bangThunkV (banged_dead hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  exact .app (.left (.right (.dead (deadSplit hΓ))))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf SO .unit)) (cancelTy SO FD))
      (.here (by cdead))))
    (.there (.here (by cdead)))

/-- `{close} ++ {close, open} ≤ {close, open}`. -/
theorem SDSO_le : RowLe (SD ++ SO) SO := by
  intro n i o h
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
  simp only [SD, SO, List.singleton_append, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨fcloseSig, rfl, OpSig.LeF.refl _⟩
  · exact ⟨fcloseSig, rfl, OpSig.LeF.refl _⟩
  · exact ⟨fopenSig, rfl, OpSig.LeF.refl _⟩

theorem d_clDrop {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clDrop (.val (clauseTy SO .unit (.cancel, .unit, .unit) FD)) := by
  refine .bangThunkV (banged_dead hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .unitE (.right (.left (.dead (deadSplit hΓ)))) (.var (by csolo)) ?_
  refine .bind (A := .ref KY) (.left (.dead (.dead (deadSplit hΓ))))
    (.ret (appW (.var (by csolo)) (.alloc (by cdead)))) ?_
  refine .bind (A := KY) (.left (.dead (.dead (.dead (deadSplit hΓ)))))
    (.ret (appW (.var (by csolo)) (.free (by cdead)))) ?_
  have h : CDerives Δ (⟨KY, true⟩ :: ⟨.ref KY, false⟩ :: ⟨KY, false⟩ :: ⟨.unit, false⟩ ::
      ⟨.tensor .unit KY, false⟩ :: Γ) (.app (.var 0) (.val (.inj₂ .unit))) (.comp (cancelTy SO FD)) :=
    .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf SO .unit)) (cancelTy SO FD)) (.here (by cdead)))
  rw [cancelTy_effOf] at h
  exact .effSub SDSO_le h

def yH (cl : Expr) (e : Expr) : Expr := bindE (.pair cl (.val .unit)) (bindE hrF (hndTerm 6 [.cancel] 0 1 e))

theorem d_yH {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {cl e : Expr}
    (hcl : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' →
      CDerives LifeCtx.empty Γ' cl (.val (clauseTy SO .unit (.cancel, .unit, .unit) FD)))
    (he : CDerives LifeCtx.empty (⟨retTy SO .unit .unit, false⟩ :: ⟨clausesTy SO .unit Ey fsY, false⟩
      :: Γ) e (.comp (CTy.effOf SY .unit))) :
    CDerives LifeCtx.empty Γ (yH cl e) (.comp (CTy.effOf SO .unit)) := by
  refine .bind (split_kill Γ).toP
    (.ret (.tensorI (deadSplit (kill_dead Γ)) (hcl (kill_dead Γ)) (.unitI (kill_dead Γ).toP))) ?_
  refine .bind (.right (split_kill Γ).toP) (.ret (d_hrF (S := SO) (A := .unit) (.cons (kill_dead Γ)))) ?_
  refine CDerives.effHandleCs (S := SO) (E := Ey) (n := 6) (A := .unit) (R := .unit) fsY rcsNil
    (.left (.left (deadSplit hΓ))) (.left (.right (deadSplit hΓ)))
    (.here (.cons hΓ.toP)) (.there (.here hΓ.toP))
    (by decide) (by simp [fcloseSig, fopenSig]) (by simp) (by decide) ?_
  rw [ofEff_SY]
  exact he

/-! ### The closed programs -/

def yProg (cl : Expr) : Expr := withFs (yH cl (twoFiles 4 (performE (opArgE 6 0 (.val .unit)))))

theorem d_yProg {cl : Expr}
    (hcl : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' →
      CDerives LifeCtx.empty Γ' cl (.val (clauseTy SO .unit (.cancel, .unit, .unit) FD))) :
    CDerives LifeCtx.empty [] (yProg cl) (.comp (.ret .unit)) := by
  refine d_withFsG (S := []) (A := .unit) (by simp) rfl ?_
  exact d_yH (.cons (.cons .nil)) hcl (d_twoFilesY (Γ := [_, _, _, _]) (by cdead))

/-- (a) resumed. -/
def ySeqResume : Expr := yProg clRes
/-- (c) stored and dropped. -/
def ySeqDrop : Expr := yProg clDrop

theorem d_ySeqResume : CDerives LifeCtx.empty [] ySeqResume (.comp (.ret .unit)) :=
  d_yProg d_clRes

theorem d_ySeqDrop : CDerives LifeCtx.empty [] ySeqDrop (.comp (.ret .unit)) :=
  d_yProg d_clDrop

theorem ySeqResume_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem ySeqResume μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_ySeqResume hs

theorem ySeqDrop_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem ySeqDrop μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_ySeqDrop hs

/-! ### The runs: the same body, `with_fs` recording the closes -/

def yLog (cl : Expr) : Expr :=
  withLogCell (withFsLog (yH cl (twoFiles 4 (performE (opArgE 6 0 (.val .unit))))))

/-- (a) Resumed: the files are closed at the scope's end, f₂ then f₁, once each. -/
theorem ySeqResume_order : logIs (yLog clRes) 21 = true := by decide

/-- (c) Dropped: the cancel unwinds the captured frame, which closes f₂ then f₁, once each. -/
theorem ySeqDrop_order : logIs (yLog clDrop) 21 = true := by decide

end BoCa.Fig16.LogRel.Core.LetDtor.Suspend

end
