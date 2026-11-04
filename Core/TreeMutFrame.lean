import Core.TreeLend
import Core.TreeBorrowEdges
import Core.TreeSchedRelay

/-!
# The Mut Frame and the Anti-Frame at `cerwpT`: statements, and the start world  `[spec §62]`

`docs/new-core/scope-791.md` O8. `CerwpTMFrame` and `CerwpTMAntiFrame` are Core's `erwp_M_frame`
and `erwp_M_antiFrame` (branch `tree-inv`, `StopFrameN.lean`, `AntiStopN.lean`) read at `cerwpT`:
the content folded back at every stop and lent again at the resume, the cell sealed at every stop
and opened again at the resume.

**The start world.** A Mut Frame turns `ℓ ↦ own(v)` into `ℓ ↦ mut(α, v, ρ_P, P̂)`, and a `mut` cell
is covered only where its invariant is its location's code (`Cov.mut`). An `own` cell pins no code
(`AgreeOn` reads `mut` cells only, `HoldsMut`), so the lender's run starts at extensions where `ℓ`
has another code, and the borrowed run is entered only at a world typing `ℓ` at `A`: the lender
re-types `ℓ` at the start and owes the frame condition there. `not_cerwpTMFrame` is the
configuration: a frame condition true exactly where `ℓ` is not typed at `A` admits the borrowed run
vacuously, and the lender's run, started at a world where `ℓ` is untyped, has no end.

`CerwpTMFrameM` is the statement with the frame conditions carried along extension: the present
one `F`, the base `Fb`, and every entry's resumer guarantee `fd` (`OpTabT.FdMono`), since a stop
resumes at `fdAt en v Fb O′` and the resumed run re-lends there. It also carries the premise
`ρ_b ∈ Res_{↓α}` of `erwp_M_frame` (`houtb`), read as a stratum `D` with `K.DownOf D {α}` as at
`ResUT.six27`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa BoCa.Fig16 BoCa.Fig16.Tree BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont performE opPayload)
open BoCa.Fig16.Tree.Wp.SchedProgs.Park (TP TP_some nP enPark)

/-- The cell's invariant read off its location's code (E1). -/
def codeP (w : TWd) (A : KTy) (b : TSet) : BoCa.Val → SPropST BoCa.Loc BoCa.Val w.K b :=
  fun u r => (A.interp w.Θ).P w.K u r.val

/-- `CellFold` (AntiStopN.lean:224) at the tree: the share holds `ℓ ↦ own(w)` beside content in
the location's code. -/
def CellFoldT (l : BoCa.Loc) (A : KTy) : (w : TWd) → TRes w.K → Prop := fun w ρ =>
  ∃ (u : BoCa.Val) (χ R rest : TRes w.K), (A.interp w.Θ).P w.K u χ ∧
    ResUT.CompS (ResUT.single l (CellUT.ownOf u)) rest ρ ∧ ResUT.CompS χ R rest

/-- `opTableG` (AntiStopN.lean:190) at the tree: `opTableT`'s stops, the continuation's share
guarded. -/
def opTableGT (T : OpTabT) (G : (w : TWd) → TRes w.K → Prop) : TableT := fun F k w ls O t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntT),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.abort = false ∧ en.oc w O ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧
      en.PA k w ls v ρa ∧ G w ρk ∧ contShareT en F k w ls O K v Ψ ρk

/-- `OpTabN.LendOK`/`AFOK` (AntiStopN.lean:234) at the tree: every non-abortive entry
must-resume. -/
def OpTabT.MustResume (T : OpTabT) : Prop :=
  ∀ m i en, T m i = some en → en.abort = false → en.q = .lin

/-- `MFPost` (WpN.lean:604) at the tree: the borrow handed back at the top, unfolded, `Q`. -/
def MFPostT (l : BoCa.Loc) (A : KTy) (Q : TPostV) : TPostV := fun k w ls O v ρ' =>
  ∀ (u : BoCa.Val) (Y : TRes w.K), ResUT.CompS ρ' (ResUT.single l (CellUT.ownOf u)) Y →
    ∀ σ, (A.interp w.Θ).P w.K u σ → ∀ Z, ResUT.CompS Y σ Z → Q k w ls O v Z

/-- **Mut Frame across stops at `cerwpT`** (`erwp_M_frame`, StopFrameN.lean:320, ported): the
content is folded back at every stop and lent again at the resume. -/
def CerwpTMFrame : Prop :=
  ∀ (T : OpTabT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (α : Life)
    [Fact (w.K.Anti (TSet.single α))] (v : BoCa.Val) (ρP ρlP ρb ρ : TRes w.K)
    (hP : ρP.InStratum (TSet.single α)) (hw : codeP w A (TSet.single α) v ⟨ρP, hP⟩),
    OpTabT.MustResume T → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρP ρlP → ResUT.CompS ρlP ρb ρ →
    (∀ BM, ResUT.CompS ρb (ResUT.single l (CellUT.mutOf (TSet.single α) v ρP hP
        (codeP w A (TSet.single α)) hw)) BM →
      cerwpT (ℍ := ℍ) (opTableT T) (MFPostT l A Q) Fb F n w ls O e BM) →
    cerwpT (ℍ := ℍ) (opTableT T) Q Fb F n w ls O e ρ

/-- **Anti-Frame across stops at `cerwpT`** (`erwp_M_antiFrame`, AntiStopN.lean:257, ported):
the cell is sealed at every stop (the callback stops only with its content in the code,
`CellFoldT`) and opened again at the resume. -/
def CerwpTMAntiFrame : Prop :=
  ∀ (T : OpTabT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (b : TSet)
    [Fact (w.K.Anti b)] (v : BoCa.Val) (σP ρa ρ : TRes w.K)
    (hP : σP.InStratum b) (hw : codeP w A b v ⟨σP, hP⟩),
    OpTabT.MustResume T → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.mutOf b v σP hP (codeP w A b) hw)) ρa ρ →
    (∀ W X, ResUT.CompS σP (ResUT.single l (CellUT.ownOf v)) W → ResUT.CompS ρa W X →
      cerwpT (ℍ := ℍ) (opTableGT T (CellFoldT l A)) (MFPostT l A Q) Fb F n w ls O e X) →
    cerwpT (ℍ := ℍ) (opTableT T) Q Fb F n w ls O e ρ

/-! ### The Mut Frame at a start world that re-types the lent location -/

/-- The code typing typing location `1` at `unit`. -/
def Θ1 : CodeTy := fun x => if x = 1 then some KTy.unit else none

/-- The chain world typing `1` at `unit`. -/
abbrev w1 : TWd := ⟨chainP, Θ1, tmplT _ Θ1⟩

/-- A frame condition true exactly where `1` is not typed at `unit`. -/
def FOff : TFrame := fun w _ => w.Θ 1 ≠ some KTy.unit

/-- **The Mut Frame's statement, at a frame condition reading the code typing at the lent
location, has a configuration refusing it.** `ℓ = 1 ↦ own(())` at `w1` (`Θ 1 = unit`), lent at
`unit` with an empty content and an empty frame; the borrowed run is admitted (every start world
carrying the `mut` cell types `1` at `unit`, so `FOff` holds at none), and the lender's run, at the
start world `wE` (an extension carrying `1 ↦ own(())`: an `own` cell pins no code), meets `FOff`
and ends at once at a value the postcondition `False` refuses. -/
theorem not_cerwpTMFrame : ¬ CerwpTMFrame (ℍ := ℍ) := by
  intro H
  have hP : ResUT.InStratum (TSet.single (lfE 1)) (PMap.empty : TRes w1.K) := ResUT.inStratum_empty _
  have hw : codeP w1 KTy.unit (TSet.single (lfE 1)) BoCa.Val.unit ⟨PMap.empty, hP⟩ :=
    ⟨rfl, rfl⟩
  have h := H OpTabT.empty (fun _ _ _ _ _ _ => False) FOff FOff 1 w1 [] [] (.val .unit) 1 KTy.unit
    (lfE 1) BoCa.Val.unit PMap.empty (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) PMap.empty
    (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) hP hw (fun _ _ _ h _ => by simp [OpTabT.empty] at h)
    (by simp [Θ1]) (ResUT.compS_empty_right _) (ResUT.compS_empty_right _) (fun BM hBM => by
      rw [cerwpT_eq]
      intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE _ _ _ hF
      exfalso
      have hk : (CellUT.mutOf (K := w1.K) (TSet.single (lfE 1)) BoCa.Val.unit PMap.empty hP
          (codeP w1 KTy.unit (TSet.single (lfE 1))) hw).kind ≠ Kind.imm := by
        simp [CellUT.kind, CellUT.mutOf]
      have hg := (ResUT.CompS.get_left_of_ne_imm (ResUT.CompS.comm hBM)
        (ResUT.single_get_self _ _) hk).2
      have := hE.2 1 (.top hg)
      exact hF (by rw [this]; simp [Θ1]))
  rw [cerwpT_eq] at h
  have hE : w1.Ext wE (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) :=
    ⟨WCactus.Ext.refl _, fun _ hl => absurd hl not_holdsMut_own⟩
  have hc : ResUT.CompS (PMap.empty : TRes wE.K) (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit))
      (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) :=
    ResUT.CompS.comm (ResUT.compS_empty_right _)
  obtain ⟨hR, hI⟩ := recWInv_alloc (w := wE) (l := 1) (recInv_empty chainP) (winv_empty chainP)
    rfl (ResUT.CompS.comm (ResUT.compS_empty_right _))
  have hfd : FinDom (BoCa.BoLo.Heap.upd (fun _ => none : Heap) 1 BoCa.Val.unit) :=
    ⟨[1], fun l hl => by
      by_cases e : l = 1
      · simp [e]
      · exact absurd (BoCa.BoLo.Heap.upd_other e) hl⟩
  obtain ⟨w', _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, hQ, -⟩ :=
    h wE (ResUT.single 1 (CellUT.ownOf BoCa.Val.unit)) PMap.empty _ [] [] [] [] _ hE
      (RR.refl hI.1) .nil .nil (by simp [FOff]) ⟨hc.1, _, hc, hI.valid⟩ hc
      ⟨fun p => by simp, fun p hp => by simp at hp⟩ hR hI hfd 0 _ _ (by omega) (.refl _ _)
      (final_val _ Val.unit)
  rcases hQ with ⟨_, _, hq⟩ | hq
  · exact hq
  · exact opTableT_empty_false hq


/-! ### The statement with the frame conditions carried along extension -/

/-- Every entry's resumer guarantee is carried along extension (`OpEntT.FdMono`). -/
def OpTabT.FdMono (T : OpTabT) : Prop := ∀ m i en, T m i = some en → en.FdMono

/-- **Mut Frame across stops at `cerwpT`, the frame conditions carried along extension** and the
frame below the lend (`ρ_b ∈ Res_D`, `K.DownOf D {α}`). -/
def CerwpTMFrameM : Prop :=
  ∀ (T : OpTabT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (α : Life) (D : TSet)
    (v : BoCa.Val) (ρP ρlP ρb ρ : TRes w.K)
    (hP : ρP.InStratum (TSet.single α)) (hw : codeP w A (TSet.single α) v ⟨ρP, hP⟩),
    OpTabT.MustResume T → OpTabT.FdMono T → Fb.Mono → F.Mono →
    w.K.DownOf D (TSet.single α) → ρb.InStratum D → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρP ρlP → ResUT.CompS ρlP ρb ρ →
    (∀ BM, ResUT.CompS ρb (ResUT.single l (CellUT.mutOf (TSet.single α) v ρP hP
        (codeP w A (TSet.single α)) hw)) BM →
      cerwpT (ℍ := ℍ) (opTableT T) (MFPostT l A Q) Fb F n w ls O e BM) →
    cerwpT (ℍ := ℍ) (opTableT T) Q Fb F n w ls O e ρ


/-! ### The premises at the scheduler -/

/-- The scheduler headline's base frame condition at its weakest, `fdMask ∅`, meets the
headline's premise and is carried along extension. -/
theorem fdMask_none_headline :
    (∀ (w : TWd) (ρf : TRes w.K), ResUT.Valid ρf → fdMask (fun _ => False) w ρf) ∧
      (fdMask (fun _ => False)).Mono :=
  ⟨fun _ _ hv => ⟨hv, NoneAt.of_false (fun _ h => h) _⟩, fdMask_mono _⟩

/-- `park`'s table meets `OpTabT.FdMono`: its one entry's guarantee is `fdJoinT`. -/
theorem TP_fdMono : OpTabT.FdMono TP := fun _ _ _ h => by
  obtain ⟨-, -, rfl⟩ := TP_some h
  exact fdJoinT_fdMono fun _ _ _ _ => Iff.rfl

/-- **`park` is not must-resume**: its entry is cancellable (`enPark.q = .cancel`), so a run that
parks inside a Mut Frame stops at a table `CerwpTMFrame`'s `OpTabT.MustResume` refuses. -/
theorem not_mustResume_TP : ¬ OpTabT.MustResume TP := fun h => by
  have := h nP 0 enPark (by simp [TP]) rfl
  simp [enPark] at this


/-! ### Cancellable stops: the cancel branch hands the borrow back -/

/-- **Every non-abortive entry keeps a share**: none is unrestricted (`contShareT`'s first clause
empties an unrestricted share, which could not hold the folded cell). A cancellable entry is
admitted: its cancel branch is a run of the continuation at the same postcondition
(`contShareT`'s second clause), so the borrowed run's cancel branch, re-lent, ends in
`MFPostT l A Q` and hands the borrow back as a resume does. -/
def OpTabT.KeepsShare (T : OpTabT) : Prop :=
  ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr

/-- **Mut Frame across stops at `cerwpT`, cancellable stops included**: `CerwpTMFrameM` with
`OpTabT.MustResume` replaced by `OpTabT.KeepsShare`. -/
def CerwpTMFrameC : Prop :=
  ∀ (T : OpTabT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (α : Life) (D : TSet)
    (v : BoCa.Val) (ρP ρlP ρb ρ : TRes w.K)
    (hP : ρP.InStratum (TSet.single α)) (hw : codeP w A (TSet.single α) v ⟨ρP, hP⟩),
    OpTabT.KeepsShare T → OpTabT.FdMono T → Fb.Mono → F.Mono →
    w.K.DownOf D (TSet.single α) → ρb.InStratum D → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρP ρlP → ResUT.CompS ρlP ρb ρ →
    (∀ BM, ResUT.CompS ρb (ResUT.single l (CellUT.mutOf (TSet.single α) v ρP hP
        (codeP w A (TSet.single α)) hw)) BM →
      cerwpT (ℍ := ℍ) (opTableT T) (MFPostT l A Q) Fb F n w ls O e BM) →
    cerwpT (ℍ := ℍ) (opTableT T) Q Fb F n w ls O e ρ

/-- `park`'s table keeps a share: its one entry is cancellable. -/
theorem TP_keepsShare : OpTabT.KeepsShare TP := fun _ _ _ h _ => by
  obtain ⟨-, -, rfl⟩ := TP_some h
  simp [enPark]

/-- **`MFPostT` with the code kept**: the borrowed run hands the content back at a world still
typing `ℓ` at `A`. The Anti-Frame's alternative to a closure premise on `Q`: the outer run reseals
`ℓ` as a `mut` cell, which `InvKeptA` and `Cov.mut` read at `A`. -/
def MFPostTK (l : BoCa.Loc) (A : KTy) (Q : TPostV) : TPostV := fun k w ls O v ρ' =>
  w.Θ l = some A ∧ MFPostT l A Q k w ls O v ρ'

end BoCa.Fig16.Tree.Wp

end
