import Core.LetDtorFiles

/-!
# Core — a lend whose callback raises, the source closed by an effectful destructor  `[spec §19, §62]`

`withborU d` (§19) runs a *pure* finaliser `d : Ref A ⊸ 1` on the source when the callback
unwinds: `ewp_unwind` reads `d` at `wpTS`, and the frame's row is abortive only (`Row.Unwind`), so
`d` cannot perform `close`. The lend here is derived instead, by the paper's translation itself:
`⟦t⟧ : ⇑A = A ⊕ E` (§4.3), an expression's error is a value of its result. The callback catches its
own raise (`to_result`) and answers `['x](B ⊕ 1)`; the **pure** lexical lend `withbor` (§3/§23)
then returns, ending the borrow; the lender cases on the answer and, at `inr`, runs the source's
destructor and raises again (the paper's `δ(s, x.⟦u⟧, e. raise_Γ(e))` with `Γ` the source):

    lendD cb d = (r′, res) ← withbor r cb;
                 case res { inl b → return (r′, b)
                          | inr u → d r′ to _. raise () }

**Order on the unwind**: `withbor` has returned before `d` runs, so the view's lifetime `'x` has
ended: the view is consumed inside the callback (its drop is `forget`, a no-op), and `d` takes the
owned source. **The capability**: `d` performs `close` at `Σ_D ≤ Σ`, the lender's row, so it
reaches `with_fs` as for the files (`Core/LetDtorFiles.lean`). The callback's own row is pure
(its `Fail` is handled inside it), so nothing crosses the borrow but the caught error, a value.

`d_lendD` is a `CDerives` derivation from existing rules (`withbor1`/`withbor2`, `[⊗E]`, `[⊕E]`,
`[let]`, `[raise]`): no rule is added, `fundamentalC` is unchanged, and `resourceSafety` covers
every closed program that uses it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.LetDtor.Lend
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (failSig Sf Ef toResult d_toResultG d_toResult raiseU
  d_raiseU outlives_head Flag logRaise d_logRaise2)
open BoCa.Fig16.LogRel.Core.LetDtor.Files (withLogCell storeE)
open BoCa.BoLo (Heap Steps Step1 Kont freeE performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2)

/-- A consumed context holds nothing owned. -/
theorem deadOwnFree {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Γ.OwnFree :=
  fun s hs hl => dead_noLive (P := fun s => s.ty.OwnFree) h s hs hl

/-! ### The derived lend -/

/-- The lend, the source at `0`: `(r′, res) ← withbor r cb; case res {inl b → (r′, b) | inr u →
d r′; raise ()}`. -/
def lendD (cb b : Expr) : Expr :=
  bindE (app2 withbor (.var 0) cb)
    (.letpair (.var 0)
      (.case (.var 0)
        (.pair (.var 2) (.var 0))
        (bindE (.app (.val (.lam b)) (.var 2)) raiseU)))

/-- **`d_lendD`: a lend whose callback's error becomes the lender's raise, after the source's
destructor.** For a lend constant `withbor : Src ⊸ CB ⊸ Src ⊗ (B ⊕ 1)` (an `imm` or `mut` lend of a cell,
`withbor1`/`withbor2`, or a reborrow of a view, `withbor3`), a callback `cb : CB`, and a
destructor `λx. b : Src ⊸ F_{Σ_D} 1` at
`Σ_D ≤ Σ`, with `raise` in `Σ`: the source is lent, and on the callback's error the destructor runs
on the returned source before the error is raised again. -/
theorem d_lendD {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {Src B CB : VTy} {S SD : Row}
    {cb b : Expr}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' withbor (.val (.lolli (Src) (.lolli CB (.tensor (Src) (.sum B .unit))))))
    (hcb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' cb (.val CB))
    (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr (Src) (CTy.effOf SD .unit))))
    (hDS : RowLe SD S) (hf : Row.find S 1 0 = some failSig) :
    CDerives Δ (⟨Src, true⟩ :: Γ) (lendD cb b) (.comp (CTy.effOf S (.tensor (Src) B))) := by
  refine .bind (A := .tensor (Src) (.sum B .unit)) (.left (deadSplit hΓ))
    (.ret (.lolliE (.right (deadSplit hΓ)) (hcb _ (.cons hΓ))
      (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (hw _ (.cons hΓ))))) ?_
  refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP))) ?_
  refine .sumE (.left (.right (.dead (.dead (deadSplit hΓ))))) (.var (.here (by cdead))) ?_ ?_
  · -- `inl b`: the borrow ended normally
    exact .effSub (RowLe.nil S) (.ret (.tensorI (.right (.dead (.left (.dead (.dead
      (deadSplit hΓ)))))) (.var (.there (.there (.here (by cdead))))) (.var (.here (by cdead)))))
  · -- `inr u`: the borrow has ended; the source's destructor, then the raise
    refine .effLet (A := .unit) (split_kill' _).toP
      (fun _ => deadOwnFree (kill_dead _)) (fun _ => banged_dead (kill_dead _)) ?_
      (d_raiseU hf (.drop rfl (kill_dead _).toP))
    exact .effSub hDS (.app (split_kill _).toP (hb _ (kill_dead _))
      (.skip rfl (.there (.here (by cdead)))))

/-- **A callback that catches its own raise**: `Λ. λm. to_result body to res. return res`, at
`∀'x ⊏ ⊓Δ. L ⊸ ['x](B ⊕ 1)`, for a body at the row `{raise}` over the view `m : L`. -/
def cbOf (body : Expr) : Expr := .val (.lam (.val (.lam (bindE (toResult body) (.var 0)))))

theorem d_cbOf {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {L B : VTy} {body : Expr}
    (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ)
    (hdef : (Δ.extend x Δ.meetOfDom).Defines (.var x))
    (hBout : VOutlives (Δ.extend x Δ.meetOfDom) (.var x) (.sum B .unit))
    (hbody : CDerives (Δ.extend x Δ.meetOfDom)
      (⟨retTy [] B (.sum B .unit), false⟩ :: ⟨clausesTy [] (.sum B .unit) Ef, false⟩ ::
        ⟨L, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.comp (CTy.effOf Sf B))) :
    CDerives Δ Γ (cbOf body) (.val (.all x Δ.meetOfDom (.lolli L (.box (.var x) (.sum B .unit))))) := by
  refine callbackW hΔ hx hΓ (.ofRet ?_)
  refine .bind (.left (.dead (deadSplit hΓ))) (d_toResultG (S := []) (A := B) (by simp) rfl hbody) ?_
  exact .ret (.boxI (.var (.here (.cons (.cons hΓ.toP))))
    (outlives_head hdef hBout (.cons (.cons hΓ))))

/-! ### A file lent mutably, written, closed on the unwind -/

/-- `close_f : Flag ↠^lin 1`, the operation `0` of the name `5`: closes a file whose state is a
`Flag`. -/
def closeFSig : OpSig := ⟨5, 0, .lin, Flag, .unit, .ret .unit, false⟩

abbrev SDF : Row := [closeFSig]

/-- The lender's row `{close_f, raise}`. -/
abbrev SF : Row := [closeFSig, failSig]

/-- A file: a cell holding its state. -/
abbrev FileF : VTy := .ref Flag

/-- The file's destructor: `λf. s ← free f; close_f s`. -/
def dFileFB : Expr := bindE (.app free' (.var 0)) (performE (opArgE 5 0 (.var 0)))

theorem d_dFileF {Δ : LifeCtx} (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam dFileFB)) (.comp (.arr FileF (CTy.effOf SDF .unit))) := by
  refine .lam (.bind (A := Flag) (.left (deadSplit hΓ))
    (.ret (appW (.var (by csolo)) (.free (by cdead)))) ?_)
  exact .effPerform (S := SDF) (o := closeFSig) rfl rfl rfl (.var (by csolo))

theorem SDF_le : RowLe SDF SF := by
  intro n i o h
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
  simp only [SDF, List.mem_singleton] at hm
  subst hm
  exact ⟨closeFSig, rfl, OpSig.LeF.refl _⟩

/-- `log m; ()`: write the file through the view, `m` at `2` under `to_result`'s binders. -/
def logOK : Expr :=
  .letpair (app2 withswap (.var 2) setG) (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit)))

theorem d_logOK {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {T₁ T₂ : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨T₁, false⟩ :: ⟨T₂, false⟩ :: ⟨.mut a Flag, true⟩ :: ⟨.unit, false⟩ :: Γ) logOK
      (.comp (CTy.effOf Sf .unit)) := by
  refine .tensorE (.dead (.dead (.left (.dead (deadSplit hΓ)))))
    (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine .unitE (.left (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
    (.var (by csolo)) ?_
  refine .unitE (.dead (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
    (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact .effSub (RowLe.nil _) (.ret (.unitI (by cdead)))

/-- `forget m; raise ()` over an `imm` view at `2`. -/
def readRaise : Expr := .seq (.app forget (.var 2)) raiseU

theorem d_readRaise {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {T₁ T₂ : VTy}
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨T₁, false⟩ :: ⟨T₂, false⟩ :: ⟨.imm a Flag, true⟩ :: ⟨.unit, false⟩ :: Γ) readRaise
      (.comp (CTy.effOf Sf .unit)) :=
  .unitE (.dead (.dead (.left (.dead (deadSplit hΓ)))))
    (appW (.var (by csolo)) (.forgetImm (by cdead))) (d_raiseU rfl (by cdead))

/-- The callback over a `mut` view, at the empty lifetime context. -/
theorem d_cbMut {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {body : Expr}
    (hbody : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' → ∀ {T₁ T₂ : VTy}, CDerives
      (LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom)
      (⟨T₁, false⟩ :: ⟨T₂, false⟩ :: ⟨.mut (.var 0) Flag, true⟩ :: ⟨.unit, false⟩ :: Γ') body
      (.comp (CTy.effOf Sf .unit))) :
    CDerives LifeCtx.empty Γ (cbOf body) (.val (.all 0 LifeCtx.empty.meetOfDom
      (.lolli (.mut (.var 0) Flag) (.box (.var 0) (.sum .unit .unit))))) :=
  d_cbOf ok_empty rfl hΓ (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (hbody hΓ)

theorem d_cbImm {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (cbOf readRaise) (.val (.all 0 LifeCtx.empty.meetOfDom
      (.lolli (.imm (.var 0) Flag) (.box (.var 0) (.sum .unit .unit))))) :=
  d_cbOf ok_empty rfl hΓ (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (d_readRaise hΓ)

/-- `withbor` at a `mut` lend of a file. -/
theorem d_withborMut (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives LifeCtx.empty Γ' withbor (.val (.lolli (.ref Flag) (.lolli
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) Flag) (.box (.var 0) (.sum .unit .unit))))
      (.tensor (.ref Flag) (.sum .unit .unit))))) :=
  .withbor2 (A := Flag) (B := .sum .unit .unit) 0 hΓ.toP rfl
    ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree])
    (by simp [VFree])

/-- `withbor` at an `imm` lend of a file. -/
theorem d_withborImm (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives LifeCtx.empty Γ' withbor (.val (.lolli (.ref Flag) (.lolli
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) Flag) (.box (.var 0) (.sum .unit .unit))))
      (.tensor (.ref Flag) (.sum .unit .unit))))) :=
  .withbor1 (A := Flag) (B := .sum .unit .unit) 0 hΓ.toP rfl
    (fun _ h => by simp [VFree] at h) (by simp [VFree]) (by simp [VFree])

/-- A context whose one live slot is of an `OwnFree` type. -/
theorem ownFree_head {T : VTy} (hT : T.OwnFree) {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    Ctx.OwnFree (⟨T, true⟩ :: Γ) := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact hT
  · exact dead_noLive (P := fun s => s.ty.OwnFree) hΓ s hs' hl

/-- The lender: `r ← alloc (inl ()); p ← lendD cb d; (r, b) = p; d r; b`. -/
def lendProgBody (cb : Expr) : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (bindE (lendD cb dFileFB)
      (.letpair (.var 0) (bindE (.app (.val (.lam dFileFB)) (.var 1)) (.var 1))))

theorem SF_not_unr : ¬ SF.Unr := by
  rintro ⟨o, ho, h⟩
  simp only [SF, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> cases h

theorem d_lendProgBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {CB : VTy} {cbE : Expr}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' withbor
      (.val (.lolli (.ref Flag) (.lolli CB (.tensor (.ref Flag) (.sum .unit .unit))))))
    (hcb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' cbE (.val CB)) :
    CDerives LifeCtx.empty Γ (lendProgBody cbE) (.comp (CTy.effOf SF .unit)) := by
  refine .bind (A := FileF) (deadSplit hΓ)
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .effLet (A := .tensor FileF .unit) (.left (deadSplit hΓ))
    (fun _ => deadOwnFree (.cons hΓ)) (fun h => absurd h SF_not_unr)
    (d_lendD hΓ hw hcb d_dFileF SDF_le rfl) ?_
  refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (by cdead))) ?_
  refine .effLet (A := .unit) (.right (.left (.dead (.dead (deadSplit hΓ)))))
    (fun _ => ownFree_head .unit (by cdead)) (fun h => absurd h SF_not_unr)
    (.effSub SDF_le (.app (split_kill _).toP (d_dFileF _ (kill_dead _))
      (.there (.here (by cdead))))) ?_
  exact .effSub (RowLe.nil SF) (.ret (.var (.skip rfl (.here (by cdead)))))

/-! ### `with_fsf` and the closed programs -/

/-- `close_f`'s clause: `λ(s, κ). u ← (); κ.1 u`. -/
def clFF : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (.val .unit) (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 0)))))

abbrev EfsF : List (Qual × VTy × VTy) := [(.lin, Flag, .unit)]

def withFsF (e : Expr) : Expr := bindE (.pair clFF (.val .unit)) (bindE Files.hrF (hndTerm 5 [.lin] 0 1 e))

theorem d_clFF {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ clFF (.val (clauseTy S A (.lin, Flag, .unit))) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .bind (A := .unit) (.right (.right (.dead (deadSplit hΓ))))
    (.ret (.unitI (.cons (.cons (.cons hΓ.toP))))) ?_
  exact .app (.right (.left (.right (.dead (deadSplit hΓ)))))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S A)) .top) (.there (.here (by cdead)))))
    (.here (.cons (.drop rfl (.cons hΓ.toP))))

theorem d_withFsFG {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy} {e : Expr}
    (hS : ∀ o ∈ S, o.n ≠ 5) (hSd : Row.divB S = false)
    (he : CDerives Δ (⟨retTy S A A, false⟩ :: ⟨clausesTy S A EfsF, false⟩ :: Γ) e
      (.comp (CTy.effOf (Row.ofEff 5 EfsF 0 ++ S) A))) :
    CDerives Δ Γ (withFsF e) (.comp (CTy.effOf S A)) := by
  refine .bind (split_kill Γ).toP
    (.ret (.tensorI (deadSplit (kill_dead Γ)) (d_clFF (S := S) (A := A) (kill_dead Γ))
      (.unitI (kill_dead Γ).toP))) ?_
  refine .bind (.right (split_kill Γ).toP)
    (.ret (Files.d_hrF (S := S) (A := A) (.cons (kill_dead Γ)))) ?_
  exact .effHandle (E := EfsF) (.left (.left (split_kill Γ).toP))
    (.left (.right (deadSplit (kill_dead Γ)))) (.here (.cons (kill_dead Γ).toP))
    (.there (.here (kill_dead Γ).toP)) (by decide) hS (by simp)
    (by rw [Row.divB_ofEff_eq (by decide)]; exact hSd) he

/-- `to_result (with_fsf (lendProgBody cb))`. -/
def lendProg (cb : Expr) : Expr := toResult (withFsF (lendProgBody cb))

theorem d_lendProg {cbE : Expr} {CB : VTy}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' withbor
      (.val (.lolli (.ref Flag) (.lolli CB (.tensor (.ref Flag) (.sum .unit .unit))))))
    (hcb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' cbE (.val CB)) :
    CDerives LifeCtx.empty [] (lendProg cbE) (.comp (.ret (.sum .unit .unit))) := by
  refine d_toResult (S := []) (A := .unit) (by simp) rfl ?_
  refine d_withFsFG (S := Sf) (A := .unit) (by simp [failSig]) rfl ?_
  exact d_lendProgBody (Γ := [_, _, _, _]) (.cons (.cons (.cons (.cons .nil)))) hw hcb

/-- The `mut` lend whose callback writes the file and raises. -/
def lendMutRaise : Expr := lendProg (cbOf (logRaise 2))
/-- The `mut` lend whose callback writes the file and returns. -/
def lendMutReturn : Expr := lendProg (cbOf logOK)
/-- The `imm` lend whose callback reads and raises. -/
def lendImmRaise : Expr := lendProg (cbOf readRaise)

theorem d_lendMutRaise : CDerives LifeCtx.empty [] lendMutRaise (.comp (.ret (.sum .unit .unit))) :=
  d_lendProg d_withborMut (fun _ h => d_cbMut h (fun h' => d_logRaise2 h'))

theorem d_lendMutReturn :
    CDerives LifeCtx.empty [] lendMutReturn (.comp (.ret (.sum .unit .unit))) :=
  d_lendProg d_withborMut (fun _ h => d_cbMut h (fun h' => d_logOK h'))

theorem d_lendImmRaise : CDerives LifeCtx.empty [] lendImmRaise (.comp (.ret (.sum .unit .unit))) :=
  d_lendProg d_withborImm (fun _ h => d_cbImm h)

/-- **Resource safety for a lent source**, on the raise exit of a `mut` lend. -/
theorem lendMutRaise_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem lendMutRaise μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_lendMutRaise hs

theorem lendMutReturn_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem lendMutReturn μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_lendMutReturn hs

theorem lendImmRaise_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem lendImmRaise μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_lendImmRaise hs

/-! ### The runs, by `eval`

`with_fsf` that records the state it closes in a log cell at `0` (`log := s`), then resumes. The
answer is `(r, log)`: `r` the program's (`inr ()` the error, `inl ()` the return), `log` the
closed file's state (`inr ()` written through the view, `inl ()` untouched), no cell left. -/

def clFFLog : Expr :=
  .val (.lam (.letpair (.var 0)
    (bindE (storeE (.val (Val.loc 0)) (.var 1))
      (.app (.app (.var 1) (.val (.inj₁ .unit))) (.val .unit)))))

def withFsFLog (e : Expr) : Expr :=
  bindE (.pair clFFLog (.val .unit)) (bindE Files.hrF (hndTerm 5 [.lin] 0 1 e))

def runLog (cb : Expr) : Expr :=
  withLogCell (toResult (withFsFLog (lendProgBody cb)))

/-- The run answers `(r, log)` as given, no cell left. -/
def answersRL (e : Expr) (r l : Bool) : Bool :=
  match eval e with
  | .value ⟨.pair (.inj₁ .unit) (.inj₁ .unit), _⟩ false => !r && !l
  | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => !r && l
  | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => r && !l
  | .value ⟨.pair (.inj₂ .unit) (.inj₂ .unit), _⟩ false => r && l
  | _ => false

/-- **`mut`, raise**: the error is delivered, and the file was closed with the state written
through the view: the write happened, the borrow ended, then `close_f`. -/
theorem lendMutRaise_run : answersRL (runLog (cbOf (logRaise 2))) true true = true := by decide

/-- **`mut`, return**: the normal exit closes the same file, once. -/
theorem lendMutReturn_run : answersRL (runLog (cbOf logOK)) false true = true := by decide

/-- **`imm`, raise**: the file is closed unwritten. -/
theorem lendImmRaise_run : answersRL (runLog (cbOf readRaise)) true false = true := by decide

/-! ### Nested: a reborrow of the view inside the callback

Inside the outer callback, the view `m : Mut 'x Flag` is itself lent by the same derived form, at
`withbor3` (a reborrow, `'y ⊏ 'x`). The inner source is a view: its destructor is `forget`, a
no-op at the pure row. The inner callback writes and raises; the inner lend ends, `m` is forgotten,
the error is raised in the outer callback, caught there, and the outer lend ends; then the file's
`close_f` runs, and the error goes on. -/

abbrev Δx : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

/-- `λm. forget m`, a view's destructor. -/
def forgetB : Expr := .app forget (.var 0)

theorem d_forgetB (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives Δx Γ' (.val (.lam forgetB)) (.comp (.arr (.mut (.var 0) Flag) (CTy.effOf [] .unit))) :=
  .lam (.ret (appW (.var (by csolo)) (.forgetMut (by cdead))))

theorem d_withbor3 (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives Δx Γ' withbor (.val (.lolli (.mut (.var 0) Flag) (.lolli
      (.all 1 Δx.meetOfDom (.lolli (.mut (.var 1) Flag) (.box (.var 1) (.sum .unit .unit))))
      (.tensor (.mut (.var 0) Flag) (.sum .unit .unit))))) :=
  .withbor3 (a := .var 0) (A := Flag) (B := .sum .unit .unit) 1 hΓ.toP rfl (by simp [VFree])
    (by simp [VFree])

theorem d_cbInner {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δx Γ (cbOf (logRaise 2)) (.val (.all 1 Δx.meetOfDom
      (.lolli (.mut (.var 1) Flag) (.box (.var 1) (.sum .unit .unit))))) :=
  d_cbOf d1_ok rfl hΓ (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (d_logRaise2 hΓ)

theorem Sf_not_unr' : ¬ Sf.Unr := by
  rintro ⟨o, ho, h⟩
  simp only [Sf, List.mem_singleton] at ho
  subst ho; cases h

/-- The outer callback's body, the view at `2`: `m ← return m; p ← lendD cbInner forget; (m, b) = p;
forget m; b`. -/
def nestedBody : Expr :=
  bindE (.var 2) (bindE (lendD (cbOf (logRaise 2)) forgetB)
    (.letpair (.var 0) (.seq (.app forget (.var 1)) (.var 0))))

theorem d_nestedBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {T₁ T₂ : VTy} :
    CDerives Δx (⟨T₁, false⟩ :: ⟨T₂, false⟩ :: ⟨.mut (.var 0) Flag, true⟩ :: ⟨.unit, false⟩ :: Γ)
      nestedBody (.comp (CTy.effOf Sf .unit)) := by
  refine .bind (A := .mut (.var 0) Flag) (.dead (.dead (.left (.dead (deadSplit hΓ)))))
    (.ret (.var (.there (.there (.here (by cdead)))))) ?_
  have hΓ' : Ctx.Dead (⟨T₁, false⟩ :: ⟨T₂, false⟩ :: ⟨.mut (.var 0) Flag, false⟩ ::
      ⟨.unit, false⟩ :: Γ) := by cdead
  refine .effLet (A := .tensor (.mut (.var 0) Flag) .unit) (.left (deadSplit hΓ'))
    (fun _ => deadOwnFree (.cons hΓ')) (fun h => absurd h Sf_not_unr')
    (d_lendD hΓ' d_withbor3 (fun _ h => d_cbInner h) d_forgetB (RowLe.nil Sf) rfl) ?_
  refine .tensorE (.left (.dead (deadSplit hΓ'))) (.var (.here (by cdead))) ?_
  exact .unitE (.right (.left (.dead (.dead (deadSplit hΓ')))))
    (appW (.var (by csolo)) (.forgetMut (by cdead)))
    (.effSub (RowLe.nil Sf) (.ret (.var (.here (by cdead)))))

/-- The nested program: a `mut` lend of the file, its callback reborrowing and raising inside. -/
def lendNested : Expr := lendProg (cbOf nestedBody)

theorem d_lendNested : CDerives LifeCtx.empty [] lendNested (.comp (.ret (.sum .unit .unit))) :=
  d_lendProg d_withborMut (fun _ h => d_cbMut h (fun h' => d_nestedBody h'))

theorem lendNested_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem lendNested μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_lendNested hs

/-- **Nested, raise**: written through the reborrow, both lends ended, the file closed, the error
delivered. -/
theorem lendNested_run : answersRL (runLog (cbOf nestedBody)) true true = true := by decide

end BoCa.Fig16.LogRel.Core.LetDtor.Lend

end
