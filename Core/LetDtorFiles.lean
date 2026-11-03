import Core.LetDtorSafety
import Core.Tok

/-!
# Core — two files open across a raise, closed by their effectful destructors  `[spec §62]`

A file is an abstract linear handle: `File = Tok` (`Core/Tok.lean`), a location owning a unit cell
with no derived drop, not own-free and not persistent (`file_no_derived_drop`,
`file_not_ownFree`), whose one Core eliminator is `burn`. The platform's effect `Fs` has two
must-resume operations,

    close : File ↠^lin 1        open : I32 ↠^lin File

handled by `with_fs` (the platform's place): `open`'s clause mints the handle, `close`'s burns it.
The program declares `File`'s destructor to be `close` (`fsDecl`), so every frame that drops a
`File` performs `close` (`dropOf_file`). The bodies below contain no `burn`: a `File` leaves a body
only as the argument of `close`.

Two files are open and an error is raised. Each is live across the abortive point, which
`[let]`'s `hW` refuses (`let_refuses_files`); `[let-dtor]` admits them, and on the raise the frame
closes `f₂` then `f₁` before the error goes on.

    fs_prog M = to_result (with_fs (
                  f₁ ← open 1;
                  let f₂ = open 2 in                (unwind: close f₁)
                  let _ = M in drop_ctx             (unwind: close f₂; close f₁)))

`M` is `raise ()` (the error exit) or `return ()` (the normal exit). Both programs are closed
`CDerives` derivations, so every run of each, under every allocator, ends at the empty memory and
never sticks (`fsRaise_safe`, `fsReturn_safe`): each handle's cell is freed. On both exits `f₂` is
closed before `f₁`, each once (`fsRaise_order`, `fsReturn_order`, by `eval`).

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

/-! ### The effect `Fs` and the handle `File` -/

abbrev I32 : VTy := .int .w32

/-- A file: the abstract linear handle `Tok`. -/
abbrev File : VTy := tokTy

/-- `close : File ↠^lin 1`, the operation `0` of the name `4`: must resume, so it never fails. -/
def fcloseSig : OpSig := ⟨4, 0, .lin, File, .unit, .ret .unit, false⟩

/-- `open : I32 ↠^lin File`, the operation `1` of the name `4`. -/
def fopenSig : OpSig := ⟨4, 1, .lin, I32, File, .ret .unit, false⟩

/-- `Fs`'s operations. -/
abbrev Efs : List (Qual × VTy × VTy) := [(.lin, File, .unit), (.lin, I32, File)]

/-- The destructors' row `{close}`. -/
abbrev SD : Row := [fcloseSig]

/-- The platform's row `{close, open}`. -/
abbrev SO : Row := [fcloseSig, fopenSig]

/-- The program's row `{close, open, raise}`. -/
abbrev Sfs : Row := [fcloseSig, fopenSig, failSig]

theorem ofEff_Efs : Row.ofEff 4 Efs 0 ++ Sf = Sfs := rfl

theorem ofEff_Efs_nil : Row.ofEff 4 Efs 0 ++ [] = SO := rfl

/-- **The handle has no derived drop**: nothing but its declared destructor disposes of it. -/
theorem file_no_derived_drop : ¬ HasDtor File := fun h => by cases h

/-- **The handle owns its cell**: an abort may not abandon it (`[let]`'s `hW`, `[raise]`'s `hd`). -/
theorem file_not_ownFree : ¬ File.OwnFree := fun h => by
  cases h with
  | opq _ hk => exact hk rfl

theorem file_not_persistent : File.persistent = false := rfl

/-! ### `File`'s destructor: `close` -/

/-- `close f`, the destructor's body. -/
def closeB : Expr := performE (opArgE 4 0 (.var 0))

/-- **The program's declaration**: `Tok`'s destructor is `close`. -/
def fsDecl : Opaque → Option Expr
  | .tok => some closeB
  | _ => none

theorem dropOf_file : dropOf fsDecl File = some closeB := rfl

theorem d_closeB {Δ : LifeCtx} (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam closeB)) (.comp (.arr File (CTy.effOf SD .unit))) :=
  .lam (.effPerform (S := SD) (o := fcloseSig) rfl rfl rfl (.var (.here hΓ.toP)))

/-- `File` has a destructor at `{close}`, its declared one. -/
theorem fileOk {Δ : LifeCtx} : DropOk Δ SD fsDecl File := .opq rfl d_closeB

/-- The destructors never fail: `close` must resume. -/
theorem SD_not_cancels : ¬ SD.Cancels := by
  rintro ⟨o, ho, hq⟩
  simp only [SD, List.mem_singleton] at ho
  subst ho
  exact hq rfl

theorem SD_divB : Row.divB SD = false := by decide

theorem SO_not_cancels : ¬ SO.Cancels := by
  rintro ⟨o, ho, hq⟩
  simp only [SO, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> exact hq rfl

theorem SO_not_unr : ¬ SO.Unr := Row.not_unr_of_not_cancels SO_not_cancels

theorem SD_le_SO : RowLe SD SO := by
  intro n i o h
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
  simp only [SD, List.mem_singleton] at hm
  subst hm
  exact ⟨fcloseSig, rfl, OpSig.LeF.refl _⟩

theorem SD_le : RowLe SD Sfs := by
  intro n i o h
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
  simp only [SD, List.mem_singleton] at hm
  subst hm
  exact ⟨fcloseSig, rfl, OpSig.LeF.refl _⟩

theorem Sfs_nz : Sfs.NZ := by
  intro o ho
  simp only [Sfs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> decide

theorem Sfs_uniq : Sfs.Uniq := by simp [Row.Uniq, fcloseSig, fopenSig, failSig]

theorem Sfs_noRead : ∀ o ∈ Sfs, o.finRead = false := by
  intro o ho
  simp only [Sfs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> decide

theorem Sfs_not_unrD : ¬ Sfs.UnrD := by
  rintro ⟨o, ho, h⟩
  simp only [Sfs, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> rcases h with h | ⟨h, -⟩ <;>
    simp_all [fcloseSig, fopenSig, failSig, capB, VTy.isZero]

/-- A consumed context holds nothing owned. -/
theorem deadOwnFree {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Γ.OwnFree :=
  fun s hs hl => dead_noLive (P := fun s => s.ty.OwnFree) h s hs hl

/-! ### `open` -/

/-- `open n`. -/
def openE (n : UInt32) : Expr := performE (opArgE 4 1 (.val (Val.i32 n)))

theorem d_openE {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row}
    (hop : Row.find S 4 1 = some fopenSig) (n : UInt32) :
    CDerives Δ Γ (openE n) (.comp (CTy.effOf S File)) :=
  .effPerform (o := fopenSig) hop rfl rfl (.lit (.i32 n) hΓ.toP)

/-! ### `[let]` refuses the files; `[let-dtor]` admits them -/

/-- **`[let]`'s `hW` fails here**: the row has the abortive `raise`, and a file is owned. -/
theorem let_refuses_files (Γ : Ctx VTy) :
    ¬ (Sfs.Cancels → Ctx.OwnFree (⟨File, true⟩ :: Γ)) := by
  intro h
  exact file_not_ownFree (h ⟨failSig, by simp, by simp [failSig]⟩ ⟨File, true⟩ (by simp) rfl)

/-- The destructors of `f₁` over a dead rest of length `k`. -/
def dsOne (k : Nat) : List (Option Expr) := some closeB :: List.replicate k none

/-- The two files' destructors, then none for the dead rest. -/
def dsFiles (k : Nat) : List (Option Expr) := some closeB :: some closeB :: List.replicate k none

theorem ctxDrops_one {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ctxDrops fsDecl (⟨File, true⟩ :: Γ) = dsOne Γ.length := by
  rw [ctxDrops_cons_live Γ file_not_persistent dropOf_file, ctxDrops_dead hΓ]; rfl

theorem ctxDrops_files {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ctxDrops fsDecl (⟨File, true⟩ :: ⟨File, true⟩ :: Γ) = dsFiles Γ.length := by
  rw [ctxDrops_cons_live _ file_not_persistent dropOf_file, ctxDrops_one hΓ]; rfl

/-- A context of live files over a rest that has its destructors has its destructors. -/
theorem hds_file {Δ : LifeCtx} {Γ : Ctx VTy}
    (hΓ : ∀ s ∈ Γ, s.live = true → s.ty.Persistent ∨ DropOk Δ SD fsDecl s.ty) :
    ∀ s ∈ (⟨File, true⟩ :: Γ : Ctx VTy), s.live = true →
      s.ty.Persistent ∨ DropOk Δ SD fsDecl s.ty := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact .inr fileOk
  · exact hΓ s hs' hl

theorem hds_dead {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ∀ s ∈ Γ, s.live = true → s.ty.Persistent ∨ DropOk Δ SD fsDecl s.ty :=
  dead_noLive (P := fun s => s.ty.Persistent ∨ DropOk Δ SD fsDecl s.ty) hΓ

/-- `f₁ ← open 1; let f₂ = open 2 in let _ = M in drop_ctx`, each `let` unwinding through
`drop_ctx`, at the context `Γ`. -/
def twoFiles (k : Nat) (M : Expr) : Expr :=
  bindE (openE 1)
    (letDE (dsOne k) (letDE (dsFiles k) (dropCtxE (dsFiles k) 1) M) (openE 2))

/-- **The body is typed** at every row `Σ ≥ {close, open}` that `[let-dtor]` admits, for every
closed `M` of that row: `f₁` is live across `open 2` and both files across `M`, each frame holding
them by `[let-dtor]` with `File`'s destructor. -/
theorem d_twoFilesAt {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {M : Expr}
    (hNZ : S.NZ) (hUq : S.Uniq) (hUnr : ¬ S.UnrD) (hDS : RowLe SD S)
    (hop : Row.find S 4 1 = some fopenSig)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' M (.comp (CTy.effOf S .unit))) :
    CDerives Δ Γ (twoFiles Γ.length M) (.comp (CTy.effOf S .unit)) := by
  refine .effLet (A := File) (deadSplit hΓ) (fun _ => deadOwnFree hΓ) (fun _ => banged_dead hΓ)
    (d_openE hΓ hop 1) ?_
  have h1 := hds_file (Δ := Δ) (hds_dead hΓ)
  have h2 := hds_file (Δ := Δ) h1
  show CDerives Δ (⟨File, true⟩ :: Γ)
    (letDE (dsOne Γ.length) (letDE (dsFiles Γ.length) (dropCtxE (dsFiles Γ.length) 1) M)
      (openE 2)) _
  rw [← ctxDrops_one hΓ, ← ctxDrops_files hΓ]
  refine CDerives.effLetD (A := File) (split_kill _).toP hNZ hUq (fun h => absurd h hUnr)
    (RowLe.refl S) hDS SD_not_cancels SD_divB (hfin_self hfin) h1 (d_openE (kill_dead _) hop 2) ?_
  refine CDerives.effLetD (A := .unit) (split_kill _).toP hNZ hUq (fun h => absurd h hUnr)
    (RowLe.refl S) hDS SD_not_cancels SD_divB (hfin_self hfin) h2 (hM _ (kill_dead _)) ?_
  have hN := dropCtx_derives SD_not_cancels (Dtors.ofDrops SD_not_cancels h2)
    (P := [⟨.unit, true⟩]) (.drop rfl .nil)
  exact .effSub hDS hN

/-- The body at the row `{close, open, raise}`. -/
theorem d_twoFiles {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {M : Expr}
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' M (.comp (CTy.effOf Sfs .unit))) :
    CDerives Δ Γ (twoFiles Γ.length M) (.comp (CTy.effOf Sfs .unit)) :=
  d_twoFilesAt hΓ Sfs_nz Sfs_uniq Sfs_not_unrD SD_le rfl
    (fun _ _ o hf hr => by rw [Sfs_noRead o (Row.find_mem hf).1] at hr; cases hr) hM

/-! ### The files' frames at the run -/

theorem dead_replicate (T : VTy) : ∀ k : Nat, Ctx.Dead (List.replicate k (⟨T, false⟩ : Slot VTy))
  | 0 => .nil
  | k + 1 => .cons (dead_replicate T k)

/-- **`FrameOk` at the files' inner frame**, from typing (`FrameOk.ofDrops`): closed values, a
value per slot.  `[spec §62]` -/
theorem files_frameOk {k : Nat} {γ : List Val} (hγ : ∀ v ∈ γ, closedAt 0 v.1 = true)
    (hl : k + 2 ≤ γ.length) : FrameOk (dsFiles k) γ := by
  have hΓ := dead_replicate File k
  have e := ctxDrops_files (Γ := List.replicate k ⟨File, false⟩) hΓ
  rw [List.length_replicate] at e
  rw [← e]
  exact FrameOk.ofDrops (Δ := LifeCtx.empty) SD_not_cancels
    (hds_file (hds_file (hds_dead hΓ))) hγ (by simp; omega)

/-- **`FrameOk` at the files' outer frame** (`f₁` across `open 2`). -/
theorem one_frameOk {k : Nat} {γ : List Val} (hγ : ∀ v ∈ γ, closedAt 0 v.1 = true)
    (hl : k + 1 ≤ γ.length) : FrameOk (dsOne k) γ := by
  have hΓ := dead_replicate File k
  have e := ctxDrops_one (Γ := List.replicate k ⟨File, false⟩) hΓ
  rw [List.length_replicate] at e
  rw [← e]
  exact FrameOk.ofDrops (Δ := LifeCtx.empty) SD_not_cancels (hds_file (hds_dead hΓ)) hγ
    (by simp; omega)

theorem dropChain_replicate_none : ∀ (k : Nat) (γ : List Val),
    dropChain (List.replicate k none) γ = .val .unit
  | 0, _ => rfl
  | k + 1, γ => dropChain_replicate_none k γ.tail

/-- The files' chain: `close f₂; close f₁`. -/
theorem dropChain_files (k : Nat) (f₁ f₂ : Val) (γ₀ : List Val) :
    dropChain (dsFiles k) (f₂ :: f₁ :: γ₀) =
      bindE (.app (.val (.lam closeB)) (.val f₂))
        (bindE (.app (.val (.lam closeB)) (.val f₁)) (.val .unit)) := by
  simp [dsFiles, dropChain, dropChain_replicate_none]

/-- **On the raise, the files' frame runs `close f₂; close f₁`, then the raise**: the inner frame
of `twoFiles` at `M = raise ()`, its slots at closed values.  `[spec §62]` -/
theorem files_raise_run (k : Nat) (μ : Heap) (N : Expr) {f₁ f₂ : Val} {γ₀ : List Val}
    (hγ : ∀ v ∈ f₂ :: f₁ :: γ₀, closedAt 0 v.1 = true) (hl : k ≤ γ₀.length) (K : Kont) :
    Steps (ℍ := ℍ) μ (K.plug (substAll (f₂ :: f₁ :: γ₀) (letDE (dsFiles k) N raiseU))) μ
      (K.plug (.seq (bindE (.app (.val (.lam closeB)) (.val f₂))
        (bindE (.app (.val (.lam closeB)) (.val f₁)) (.val .unit))) raiseU)) := by
  have h := letDE_raise_run (ℍ := ℍ) (N := N) (M := raiseU) (μ := μ) (μ' := μ)
    (files_frameOk hγ (by simp; omega)) K .hole (n := 1) (i := 0) (v := .unit) (by decide) rfl
    (by rw [psub_closedAt _ _ (by decide) (Nat.zero_le 0)]; exact .refl _ _)
  rwa [dropChain_files] at h

/-! ### `with_fs`: the handler of `Fs` -/

/-- `with_fs`'s answer clause `λx. return x`. -/
def hrF : Expr := .val (.lam (.var 0))

/-- `close`'s clause: `λ(f, κ). u ← burn f; κ.1 u`. -/
def clF : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (.app burnE (.var 1)) (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 0)))))

/-- `open`'s clause: `λ(n, κ). f ← mint (); κ.1 f`. -/
def clO : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (.app mintE (.val .unit)) (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 0)))))

def clsF : Expr := .pair clF (.pair clO (.val .unit))

/-- `with_fs e`. -/
def withFs (e : Expr) : Expr := bindE clsF (bindE hrF (hndTerm 4 [.lin, .lin] 0 1 e))

theorem d_hrF {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ hrF (.val (retTy S A A)) :=
  .bangThunkV (dead_noLive hΓ) rfl
    (.lam (.effSub (RowLe.nil S) (.ret (.var (.here hΓ.toP)))))

theorem d_clF {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clF (.val (clauseTy S A (.lin, File, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .bind (A := .unit) (.right (.left (.dead (deadSplit hΓ))))
    (.ret (appW (.var (by csolo)) (.tokBurn (by cdead)))) ?_
  exact .app (.right (.left (.dead (.dead (deadSplit hΓ)))))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S A)) .top) (.there (.here (by cdead)))))
    (.here (by cdead))

theorem d_clO {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clO (.val (clauseTy S A (.lin, I32, File))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .bind (A := File) (.right (.right (.dead (deadSplit hΓ))))
    (.ret (appW (.unitI (by cdead)) (.tokMint (by cdead)))) ?_
  exact .app (.right (.left (.right (.dead (deadSplit hΓ)))))
    (.proj₁ (.force (C := .amp (.arr File (CTy.effOf S A)) .top) (.there (.here (by cdead)))))
    (.here (.cons (.drop rfl (.cons hΓ.toP))))

theorem d_withFsG {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {e : Expr}
    (hS : ∀ o ∈ S, o.n ≠ 4) (hSd : Row.divB S = false)
    (he : CDerives Δ (⟨retTy S A A, false⟩ :: ⟨clausesTy S A Efs, false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff 4 Efs 0 ++ S) A))) :
    CDerives Δ Γ (withFs e) (.comp (CTy.effOf S A)) := by
  refine .bind (split_kill Γ).toP
    (.ret (.tensorI (deadSplit (kill_dead Γ)) (d_clF (S := S) (A := A) (kill_dead Γ))
      (.tensorI (deadSplit (kill_dead Γ)) (d_clO (S := S) (A := A) (kill_dead Γ))
        (.unitI (kill_dead Γ).toP)))) ?_
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

/-! ### One option for a `close` that can fail: the error ignored

`[let-dtor]` asks the destructors' row to have no failing operation (`hSDc`), as the paper's
`delete` releases without fail. What a destructor that can fail should do is *Open* (SPEC §62),
with three options: (a) the error is ignored; (b) destructors cannot fail, so a fallible close is
handled inside the destructor by the program; (c) the rest is unwound, then the error is raised,
which needs a policy for two errors. This section is an example of (a) only, not a rule: a close
that answers its error, `close_try : File ↠^lin 1 ⊕ I32`, whose error the destructor drops. -/

/-- `close_try : File ↠^lin 1 ⊕ I32`, the operation `2` of `Fs`: must resume, answering an
errno. -/
def ftrySig : OpSig := ⟨4, 2, .lin, File, .sum .unit I32, .ret .unit, false⟩

/-- `λf. r ← close_try f; case r {inl u → u | inr _ → ()}`. -/
def dFileTryB : Expr :=
  bindE (performE (opArgE 4 2 (.var 0))) (.case (.var 0) (.var 0) (.val .unit))

/-- **Option (a), the error ignored**: a destructor `File → F_{close_try} 1` that drops
`close_try`'s error. -/
theorem d_dFileTry {Δ : LifeCtx} (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam dFileTryB)) (.comp (.arr File (CTy.effOf [ftrySig] .unit))) := by
  have hnc : ¬ Row.Cancels [ftrySig] := by
    rintro ⟨o, ho, hq⟩
    simp only [List.mem_singleton] at ho
    subst ho
    exact hq rfl
  refine .lam (.effLet (A := .sum .unit I32) (.left (deadSplit hΓ)) (fun h => absurd h hnc)
    (fun h => absurd h (Row.not_unr_of_not_cancels hnc))
    (.effPerform (S := [ftrySig]) (o := ftrySig) rfl rfl rfl (.var (.here hΓ.toP))) ?_)
  refine .sumE (.left (.dead (deadSplit hΓ))) (.var (.here (by cdead)))
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

The same body `twoFiles 4 M` under a `with_fs` that records: `open n` allocates a cell holding
`n` as the handle, and `close` frees it and records its `n` in a log cell at location `0`,
`log := log · 10 + n`, then resumes. Each close appends one digit, so the log is the sequence of
closes. -/

def litE (n : UInt32) : Expr := (Val.i32 n).1

def binE (o : BinOp) (a b : Expr) : Expr := .app (.val (.prim (.host (.bin .w32 o)))) (.pair a b)

def loadE (l : Expr) : Expr := .app (.val (.prim .load)) l

def storeE (l v : Expr) : Expr := .app (.app (.val (.prim .store)) l) v

/-- `λ(f, κ). n ← free f; log := log · 10 + n; κ.1 ()`. -/
def clFLog : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (.app free' (.var 1))
      (bindE (storeE (.val (Val.loc 0))
          (binE .add (binE .mul (loadE (.val (Val.loc 0))) (litE 10)) (.var 0)))
        (.app (.app (.var 2) (.val (.inj₁ .unit))) (.val .unit))))))

/-- `λ(n, κ). f ← alloc n; κ.1 f`. -/
def clOLog : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (.app alloc' (.var 1)) (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 0)))))

/-- `with_fs` that records the closes. -/
def withFsLog (e : Expr) : Expr :=
  bindE (.pair clFLog (.pair clOLog (.val .unit))) (bindE hrF (hndTerm 4 [.lin, .lin] 0 1 e))

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

/-- **On the raise, `f₂` is closed before `f₁`**, each once, and no cell is left. -/
theorem fsRaise_order : logIs fsRaiseLog 21 = true := by decide

/-- **On the normal exit, the same order.** -/
theorem fsReturn_order : logIs fsReturnLog 21 = true := by decide

end BoCa.Fig16.LogRel.Core.LetDtor.Files

end
