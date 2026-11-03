import Core.LetDtorSafety

/-!
# Core — two files open across a raise, closed by their effectful destructors  `[spec §62]`

Two files are open and an error is raised. Each `File` is a cell
holding a descriptor, and its destructor is effectful: it frees the cell and performs `close` of
the effect `Fs`, a must-resume operation handled outside the program (the platform's place). The
two files are live across the abortive point, which `[let]`'s `hW` refuses; `[let-dtor]` admits
them, and on the raise the frame closes `f₂` then `f₁` before the error goes on.

    fs_prog M = to_result (with_fs (
                  f₁ ← alloc 1;  f₂ ← alloc 2;
                  let _ = M in drop_ctx  (unwind drop_ctx)))

`M` is `raise ()` (the error exit) or `return ()` (the normal exit). Both programs are closed
`CDerives` derivations, so every run of each, under every allocator, ends at the empty memory and
never sticks (`fsRaise_safe`, `fsReturn_safe`), and on both exits `f₂` is closed before `f₁`
(`fsRaise_order`, `fsReturn_order`).

**The capability reaches the destructor.** `close` is an operation of the row, not a value in the
context: the destructor performs it at `Σ_D = {close}`, a part of the frame's row `Σ`. The frame
`ubind` is inside every handler of `Σ`, so when `[finalise]` runs the destructors, `with_fs` is
still live. Typing checks it: `[let-dtor]`'s `Σ_D ≤ Σ`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LetDtor.Files
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (failSig Sf Ef ofEff_Ef toResult d_toResult raiseU d_raiseU
  adequacyD_obs)
open BoCa.BoLo (Heap Steps Step1 Kont freeE performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free')

/-! ### The effect `Fs` and the type `File` -/

abbrev I32 : VTy := .int .w32

/-- `close : I32 ↠^lin 1`, the operation `0` of the name `4`: must resume, so it never fails. -/
def fcloseSig : OpSig := ⟨4, 0, .lin, I32, .unit, .ret .unit, false⟩

/-- `Fs`'s operations. -/
abbrev Efs : List (Qual × VTy × VTy) := [(.lin, I32, .unit)]

/-- The destructors' row `{close}`. -/
abbrev SD : Row := [fcloseSig]

/-- The program's row `{close, raise}`. -/
abbrev Sfs : Row := [fcloseSig, failSig]

theorem ofEff_Efs : Row.ofEff 4 Efs 0 ++ Sf = Sfs := rfl

/-- A file: a cell holding its descriptor. -/
abbrev File : VTy := .ref I32

/-- **The file's destructor**, `λf. n ← free f; close n`: an object `File → F_{close} 1`. -/
def dFileB : Expr := bindE (.app free' (.var 0)) (performE (opArgE 4 0 (.var 0)))

theorem d_dFile {Δ : LifeCtx} (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam dFileB)) (.comp (.arr File (CTy.effOf SD .unit))) := by
  refine .lam (.bind (A := I32) (.left (deadSplit hΓ))
    (.ret (appW (.var (by csolo)) (.free (by cdead)))) ?_)
  exact .effPerform (S := SD) (o := fcloseSig) rfl rfl rfl (.var (by csolo))

/-- The destructors never fail: `close` must resume. -/
theorem SD_not_cancels : ¬ SD.Cancels := by
  rintro ⟨o, ho, hq⟩
  simp only [SD, List.mem_singleton] at ho
  subst ho
  exact hq rfl

theorem SD_divB : Row.divB SD = false := by decide

theorem SD_le : RowLe SD Sfs := by
  intro n i o h
  refine ⟨o, ?_, OpSig.LeF.refl o⟩
  simp only [Row.find, List.find?_cons] at h ⊢
  split at h
  · exact h
  · simp at h

theorem Sfs_nz : Sfs.NZ := by
  intro o ho
  simp only [Sfs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> decide

theorem Sfs_uniq : Sfs.Uniq := by simp [Row.Uniq, fcloseSig, failSig]

theorem Sfs_noRead : ∀ o ∈ Sfs, o.finRead = false := by
  intro o ho
  simp only [Sfs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> decide

theorem Sfs_not_unrD : ¬ Sfs.UnrD := by
  rintro ⟨o, ho, h⟩
  simp only [Sfs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> rcases h with h | ⟨h, -⟩ <;> simp_all [fcloseSig, failSig, capB, VTy.isZero]

/-! ### `[let]` refuses the two files; `[let-dtor]` admits them -/

/-- **`[let]`'s `hW` fails here**: the row has the abortive `raise`, and a file is owned. -/
theorem let_refuses_files (Γ : Ctx VTy) :
    ¬ (Sfs.Cancels → Ctx.OwnFree (⟨File, true⟩ :: ⟨File, true⟩ :: Γ)) := by
  intro h
  have := h ⟨failSig, by simp, by simp [failSig]⟩ ⟨File, true⟩ (by simp) rfl
  cases this

/-- The two files' destructors, then none for the dead rest. -/
def dsFiles (k : Nat) : List (Option Expr) := some dFileB :: some dFileB :: List.replicate k none

theorem dtors_files {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    Dtors Δ SD (⟨File, true⟩ :: ⟨File, true⟩ :: Γ) (dsFiles Γ.length) :=
  .drop (d_dFile (Δ := Δ)) (.drop (d_dFile (Δ := Δ)) (Dtors.ofDead hΓ))

/-- `f₁ ← alloc 1; f₂ ← alloc 2; let _ = M in drop_ctx unwind drop_ctx`, at the context `Γ`. -/
def twoFiles (k : Nat) (M : Expr) : Expr :=
  bindE (.app alloc' (.val (Val.i32 1)))
    (bindE (.app alloc' (.val (Val.i32 2)))
      (letDE (dsFiles k) (dropCtxE (dsFiles k) 1) M))

/-- **The body is typed** at every row `Σ ≥ {close}` that `[let-dtor]` admits, for every closed
`M` of that row: the two files are live across `M`, held by `[let-dtor]`. -/
theorem d_twoFilesAt {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {M : Expr}
    (hNZ : S.NZ) (hUq : S.Uniq) (hUnr : ¬ S.UnrD) (hDS : RowLe SD S)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' M (.comp (CTy.effOf S .unit))) :
    CDerives Δ Γ (twoFiles Γ.length M) (.comp (CTy.effOf S .unit)) := by
  refine .bind (A := File) (deadSplit hΓ)
    (.ret (appW (.lit (.i32 1) (by cdead)) (.alloc (by cdead)))) ?_
  refine .bind (A := File) (.right (deadSplit hΓ))
    (.ret (appW (.lit (.i32 2) (by cdead)) (.alloc (by cdead)))) ?_
  have hds := dtors_files (Δ := Δ) hΓ
  refine CDerives.effLetD (A := .unit) (split_kill _).toP hNZ hUq
    (fun h => absurd h hUnr) hDS SD_not_cancels SD_divB hfin hds (hM _ (kill_dead _)) ?_
  have hN := dropCtx_derives SD_not_cancels hds (P := [⟨.unit, true⟩]) (.drop rfl .nil)
  exact .effSub hDS hN

/-- The body at the row `{close, raise}`. -/
theorem d_twoFiles {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {M : Expr}
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' M (.comp (CTy.effOf Sfs .unit))) :
    CDerives Δ Γ (twoFiles Γ.length M) (.comp (CTy.effOf Sfs .unit)) :=
  d_twoFilesAt hΓ Sfs_nz Sfs_uniq Sfs_not_unrD SD_le (hfin_of_noRead Sfs_noRead) hM

/-! ### `with_fs`: the handler of `Fs` -/

/-- `with_fs`'s answer clause `λx. return x`. -/
def hrF : Expr := .val (.lam (.var 0))

/-- `close`'s clause: `λ(n, κ). u ← return (); κ.1 u`, resuming at once. -/
def clF : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (.val .unit) (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 0)))))

def clsF : Expr := .pair clF (.val .unit)

/-- `with_fs e`. -/
def withFs (e : Expr) : Expr := bindE clsF (bindE hrF (hndTerm 4 [.lin] 0 1 e))

theorem d_hrF {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ hrF (.val (retTy S A A)) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (RowLe.nil S) (.ret (.var (.here hΓ.toP)))))

theorem d_clF {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clF (.val (clauseTy S A (.lin, I32, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .bind (A := .unit) (.right (.right (.dead (deadSplit hΓ))))
    (.ret (.unitI (.cons (.cons (.cons hΓ.toP))))) ?_
  exact .app (.right (.left (.right (.dead (deadSplit hΓ)))))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S A)) .top) (.there (.here (by cdead)))))
    (.here (.cons (.drop rfl (.cons hΓ.toP))))

theorem d_withFsG {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {e : Expr}
    (hS : ∀ o ∈ S, o.n ≠ 4) (hSd : Row.divB S = false)
    (he : CDerives Δ (⟨retTy S A A, false⟩ :: ⟨clausesTy S A Efs, false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff 4 Efs 0 ++ S) A))) :
    CDerives Δ Γ (withFs e) (.comp (CTy.effOf S A)) := by
  refine .bind (split_kill Γ).toP
    (.ret (.tensorI (deadSplit (kill_dead Γ)) (d_clF (S := S) (A := A) (kill_dead Γ))
      (.unitI (kill_dead Γ).toP))) ?_
  refine .bind (.right (split_kill Γ).toP) (.ret (d_hrF (S := S) (A := A) (.cons (kill_dead Γ)))) ?_
  exact .effHandle (E := Efs) (.left (.left (split_kill Γ).toP))
    (.left (.right (deadSplit (kill_dead Γ)))) (.here (.cons (kill_dead Γ).toP))
    (.there (.here (kill_dead Γ).toP)) (by decide) hS (by simp)
    (by rw [Row.divB_ofEff_eq (by decide)]; exact hSd) he

/-! ### The closed programs -/

/-- `to_result (with_fs (twoFiles M))`. -/
def fsProg (M : Expr) : Expr := toResult (withFs (twoFiles 4 M))

theorem d_fsProg {M : Expr}
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives LifeCtx.empty Γ' M (.comp (CTy.effOf Sfs .unit))) :
    CDerives LifeCtx.empty [] (fsProg M) (.comp (.ret (.sum .unit .unit))) := by
  refine d_toResult (S := []) (A := .unit) (by simp) rfl ?_
  refine d_withFsG (S := Sf) (A := .unit) (by simp [failSig]) rfl ?_
  rw [ofEff_Efs]
  exact d_twoFiles (Γ := [_, _, _, _]) (.cons (.cons (.cons (.cons .nil)))) hM

/-- The error exit: `M = raise ()`. -/
theorem d_raiseM (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives LifeCtx.empty Γ' raiseU (.comp (CTy.effOf Sfs .unit)) :=
  d_raiseU rfl hΓ.toP

/-- The normal exit: `M = return ()`. -/
theorem d_returnM (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives LifeCtx.empty Γ' (.val .unit) (.comp (CTy.effOf Sfs .unit)) :=
  .effSub (RowLe.nil Sfs) (.ret (.unitI hΓ.toP))

def fsRaise : Expr := fsProg raiseU
def fsReturn : Expr := fsProg (.val .unit)

theorem d_fsRaise : CDerives LifeCtx.empty [] fsRaise (.comp (.ret (.sum .unit .unit))) :=
  d_fsProg d_raiseM

theorem d_fsReturn : CDerives LifeCtx.empty [] fsReturn (.comp (.ret (.sum .unit .unit))) :=
  d_fsProg d_returnM

/-! ### A `close` that can fail

The paper's destructors never fail, and `[let-dtor]` asks the same (`¬ Σ_D.Cancels`): a destructor
that raised would abandon the slots `drop_ctx` has not reached. A `close` that can fail is an
operation that answers its error, `close_try : I32 ↠^lin 1 ⊕ I32`, and the destructor ignores the
error, as Rust's `Drop` does; a program that wants the error closes the file itself on the normal
path, consuming it, and handles the answer. -/

/-- `close_try : I32 ↠^lin 1 ⊕ I32`, the operation `1` of `Fs`: must resume, answering an errno. -/
def ftrySig : OpSig := ⟨4, 1, .lin, I32, .sum .unit I32, .ret .unit, false⟩

/-- `λf. n ← free f; r ← close_try n; case r {inl u → u | inr _ → ()}`. -/
def dFileTryB : Expr :=
  bindE (.app free' (.var 0))
    (bindE (performE (opArgE 4 1 (.var 0))) (.case (.var 0) (.var 0) (.val .unit)))

/-- **The destructor that ignores `close_try`'s error** is an object `File → F_{close_try} 1`. -/
theorem d_dFileTry {Δ : LifeCtx} (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam dFileTryB)) (.comp (.arr File (CTy.effOf [ftrySig] .unit))) := by
  have hnc : ¬ Row.Cancels [ftrySig] := by
    rintro ⟨o, ho, hq⟩
    simp only [List.mem_singleton] at ho
    subst ho
    exact hq rfl
  refine .lam (.bind (A := I32) (.left (deadSplit hΓ))
    (.ret (appW (.var (by csolo)) (.free (by cdead)))) ?_)
  refine .effLet (A := .sum .unit I32) (.left (.dead (deadSplit hΓ))) (fun h => absurd h hnc)
    (fun h => absurd h (Row.not_unr_of_not_cancels hnc))
    (.effPerform (S := [ftrySig]) (o := ftrySig) rfl rfl rfl (.var (by csolo))) ?_
  refine .sumE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (by cdead)))
    (.effSub (RowLe.nil _) (.ret (.var (.here (by cdead)))))
    (.effSub (RowLe.nil _) (.ret (.unitI (.drop rfl (by cdead)))))

/-! ### Resource safety of the file programs -/

/-- **The file program, error exit**: resource safety at `fs_prog (raise ())`. -/
theorem fsRaise_safe {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem fsRaise μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_fsRaise hs

/-- **The file program, normal exit.** -/
theorem fsReturn_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem fsReturn μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_fsReturn hs

/-! ### The order of the closes, by `eval`

The same body `twoFiles 4 M` under a `with_fs` whose `close` clause records the descriptor in a
log cell at location `0`, `log := log · 10 + n`, then resumes. -/

def litE (n : UInt32) : Expr := (Val.i32 n).1

def binE (o : BinOp) (a b : Expr) : Expr := .app (.val (.prim (.host (.bin .w32 o)))) (.pair a b)

def loadE (l : Expr) : Expr := .app (.val (.prim .load)) l

def storeE (l v : Expr) : Expr := .app (.app (.val (.prim .store)) l) v

/-- `λ(n, κ). log := log · 10 + n; κ.1 ()`. -/
def clFLog : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (storeE (.val (Val.loc 0))
        (binE .add (binE .mul (loadE (.val (Val.loc 0))) (litE 10)) (.var 1)))
      (.app (.app (.var 1) (.val (.inj₁ .unit))) (.val .unit)))))

/-- `with_fs` that records the closes. -/
def withFsLog (e : Expr) : Expr :=
  bindE (.pair clFLog (.val .unit)) (bindE hrF (hndTerm 4 [.lin] 0 1 e))

/-- `log ← alloc 0; r ← P; (r, free log)`. -/
def withLogCell (P : Expr) : Expr :=
  bindE (.app (.val (.prim .alloc)) (litE 0))
    (bindE P (.pair (.var 0) (.app (.val (.prim .free)) (.val (Val.loc 0)))))

/-- The run answers `(r, log)` with `log` the given number and no cell left. -/
def logIs (e : Expr) (l : UInt32) : Bool :=
  match eval e with
  | .value ⟨.pair _ (.prim (.lit (.i32 b))), _⟩ false => b == l
  | _ => false

def fsRaiseLog : Expr := withLogCell (toResult (withFsLog (twoFiles 4 raiseU)))
def fsReturnLog : Expr := withLogCell (toResult (withFsLog (twoFiles 4 (.val .unit))))

/-- **On the raise, `f₂` is closed before `f₁`**, and no cell is left. -/
theorem fsRaise_order : logIs fsRaiseLog 21 = true := by decide

/-- **On the normal exit, the same order.** -/
theorem fsReturn_order : logIs fsReturnLog 21 = true := by decide

end BoCa.Fig16.LogRel.Core.LetDtor.Files

end
