import Core.LetDtorFiles

/-!
# Core — a lend whose callback raises, the source dropped by its destructor  `[spec §19, §62]`

`withborU d` (§19) runs a *pure* finaliser `d : Ref A ⊸ 1` on the source when the callback
unwinds: `ewp_unwind` reads `d` at `wpTS`, and the frame's row is abortive only (`Row.Unwind`), so
`d` cannot perform an operation. The lend here is derived instead, by the paper's translation
itself: `⟦t⟧ : ⇑A = A ⊕ E` (§4.3), an expression's error is a value of its result. The callback
catches its own raise and answers `['x](B ⊕ E)`; the **pure** lexical lend `withbor` (§3/§23)
then returns, ending the borrow; the lender cases on the answer and, at `inr e`, runs the source's
destructor and raises `e` again through the same operation, unchanged (the paper's
`δ(s, x.⟦u⟧, e. raise_Γ(e))` with `Γ` the source):

    lendD o cb d = (r′, res) ← withbor r cb;
                   case res { inl b → return (r′, b)
                            | inr e → d r′ to _. raise_o e }

The error type `E = o.A` is a parameter: any abortive operation `o` whose argument is own-free.
The programs below take `o = raise : 1`, so `E = 1`. Generalising `withborU`'s finaliser to a
destructor row `Σ_D` with the callback's error passed on is the next step, not done here.

**Order on the unwind**: `withbor` has returned before `d` runs, so the view's lifetime `'x` has
ended: the view is consumed inside the callback, and `d` takes the owned source. **The
capability**: `d` performs `Σ_D ≤ Σ`, the lender's row. The callback's own row is pure (its error
is handled inside it), so nothing crosses the borrow but the caught error, a value.

**The destructor is the source's type's** (`dropOf`): a lent cell `Ref Flag` is dropped by its
derived drop, a view by `forget` (its derived drop). An effectful close belongs to a type without
a derived drop, such as the file handle `Tok` of `Core/LetDtorFiles.lean`, which `withbor` does not
lend (it lends cells and views).

`d_lendD` is a `CDerives` derivation from existing rules (`withbor1`/`withbor2`/`withbor3`, `[⊗E]`,
`[⊕E]`, `[let]`, `[raise]`): no rule is added, `fundamentalC` is unchanged, and `resourceSafety`
covers every closed program that uses it.
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
open BoCa.BoLo (Heap Steps Step1 Kont freeE performE raiseE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2)

/-- A consumed context holds nothing owned. -/
theorem deadOwnFree {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Γ.OwnFree :=
  fun s hs hl => dead_noLive (P := fun s => s.ty.OwnFree) h s hs hl

/-! ### The derived lend -/

/-- A context whose one live slot is of an `OwnFree` type. -/
theorem ownFree_head {T : VTy} (hT : T.OwnFree) {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    Ctx.OwnFree (⟨T, true⟩ :: Γ) := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact hT
  · exact dead_noLive (P := fun s => s.ty.OwnFree) hΓ s hs' hl

/-- The lend, the source at `0`: `(r′, res) ← withbor r cb; case res {inl b → (r′, b) | inr e →
d r′; raise_o e}`. -/
def lendD (o : OpSig) (cb b : Expr) : Expr :=
  bindE (app2 withbor (.var 0) cb)
    (.letpair (.var 0)
      (.case (.var 0)
        (.pair (.var 2) (.var 0))
        (bindE (.app (.val (.lam b)) (.var 2)) (raiseE (opArgE o.n o.i (.var 1))))))

/-- **`d_lendD`: a lend whose callback's error becomes the lender's raise, unchanged, after the
source's destructor.** For a lend constant `withbor : Src ⊸ CB ⊸ Src ⊗ (B ⊕ E)` (an `imm` or `mut`
lend of a cell, `withbor1`/`withbor2`, or a reborrow of a view, `withbor3`), a callback `cb : CB`,
a destructor `λx. b : Src ⊸ F_{Σ_D} 1` at `Σ_D ≤ Σ`, and an abortive operation `o` of `Σ` at the
own-free error type `E = o.A`: the source is lent, and on the callback's error `e` the destructor
runs on the returned source before `raise_o e`. -/
theorem d_lendD {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {Src B CB : VTy} {S SD : Row}
    {o : OpSig} {cb b : Expr}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' withbor (.val (.lolli Src (.lolli CB (.tensor Src (.sum B o.A))))))
    (hcb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' cb (.val CB))
    (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr Src (CTy.effOf SD .unit))))
    (hDS : RowLe SD S) (hf : Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hrc : o.rc = false) (hE : o.A.OwnFree) (hU : S.Unr → ∃ A, o.A = .bang A) :
    CDerives Δ (⟨Src, true⟩ :: Γ) (lendD o cb b) (.comp (CTy.effOf S (.tensor Src B))) := by
  refine .bind (A := .tensor Src (.sum B o.A)) (.left (deadSplit hΓ))
    (.ret (.lolliE (.right (deadSplit hΓ)) (hcb _ (.cons hΓ))
      (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (hw _ (.cons hΓ))))) ?_
  refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP))) ?_
  refine .sumE (.left (.right (.dead (.dead (deadSplit hΓ))))) (.var (.here (by cdead))) ?_ ?_
  · -- `inl b`: the borrow ended normally
    exact .effSub (RowLe.nil S) (.ret (.tensorI (.right (.dead (.left (.dead (.dead
      (deadSplit hΓ)))))) (.var (.there (.there (.here (by cdead))))) (.var (.here (by cdead)))))
  · -- `inr e`: the borrow has ended; the source's destructor, then `raise_o e`
    have hd : Ctx.Dead (⟨VTy.sum B o.A, false⟩ :: ⟨Src, false⟩ :: ⟨.tensor Src (.sum B o.A), false⟩
        :: ⟨Src, false⟩ :: Γ) := by cdead
    refine .effLet (A := .unit) (.right (.dead (.left (.dead (.dead (deadSplit hΓ))))))
      (fun _ => ownFree_head hE hd) ?_ ?_ ?_
    · intro hu s hs hl
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact hU hu
      · exact dead_noLive (P := fun s => ∃ A, s.ty = .bang A) hd s hs' hl
    · exact .effSub hDS (.app (split_kill _).toP (hb _ (kill_dead _))
        (.there (.there (.here (by cdead)))))
    · exact .effRaise (o := o) hf ha hrc hE (.var (.skip (S := .unit) rfl (.here (by cdead))))

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

/-! ### A cell lent mutably, written, dropped on the unwind -/

theorem Sf_not_unr' : ¬ Sf.Unr := by
  rintro ⟨o, ho, h⟩
  simp only [Sf, List.mem_singleton] at ho
  subst ho; cases h

/-- The lender's destructor of its cell: the destructor of `Ref Flag`'s type, its derived drop. -/
theorem dropOf_refFlag {decl : Opaque → Option Expr} :
    dropOf decl (.ref Flag) = some (derivedDropB (.ref Flag)) :=
  dropOf_derived rfl (.ref (.sum .unit .unit))

theorem d_dropRef {Δ : LifeCtx} {SD : Row} (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam (derivedDropB (.ref Flag))))
      (.comp (.arr (.ref Flag) (CTy.effOf SD .unit))) :=
  derivedDropB_derives (.ref (.sum .unit .unit)) SD Γ hΓ

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

/-- The lender: `r ← alloc (inl ()); p ← lendD cb drop_{Ref Flag}; (r, b) = p; b; free r`, answering
the cell's last state. -/
def lendProgBody (cb : Expr) : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (bindE (lendD failSig cb (derivedDropB (.ref Flag)))
      (.letpair (.var 0) (.seq (.var 0) (.app free' (.var 1)))))

theorem d_lendProgBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {CB : VTy} {cbE : Expr}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' withbor
      (.val (.lolli (.ref Flag) (.lolli CB (.tensor (.ref Flag) (.sum .unit .unit))))))
    (hcb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' cbE (.val CB)) :
    CDerives LifeCtx.empty Γ (lendProgBody cbE) (.comp (CTy.effOf Sf Flag)) := by
  refine .bind (A := .ref Flag) (deadSplit hΓ)
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine .effLet (A := .tensor (.ref Flag) .unit) (.left (deadSplit hΓ))
    (fun _ => deadOwnFree (.cons hΓ)) (fun h => absurd h Sf_not_unr')
    (d_lendD hΓ hw hcb d_dropRef (RowLe.refl Sf) rfl rfl rfl .unit (fun h => absurd h Sf_not_unr'))
    ?_
  refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (by cdead))) ?_
  refine .unitE (.left (.right (.dead (.dead (deadSplit hΓ))))) (.var (by csolo)) ?_
  exact .effSub (RowLe.nil Sf) (.ret (appW (.var (by csolo)) (.free (by cdead))))

/-- `to_result (lendProgBody cb)`. -/
def lendProg (cb : Expr) : Expr := toResult (lendProgBody cb)

theorem d_lendProg {cbE : Expr} {CB : VTy}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' withbor
      (.val (.lolli (.ref Flag) (.lolli CB (.tensor (.ref Flag) (.sum .unit .unit))))))
    (hcb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' cbE (.val CB)) :
    CDerives LifeCtx.empty [] (lendProg cbE) (.comp (.ret (.sum Flag .unit))) := by
  refine d_toResult (S := []) (A := Flag) (by simp) rfl ?_
  exact d_lendProgBody (Γ := [_, _]) (.cons (.cons .nil)) hw hcb

/-- The `mut` lend whose callback writes the cell and raises. -/
def lendMutRaise : Expr := lendProg (cbOf (logRaise 2))
/-- The `mut` lend whose callback writes the cell and returns. -/
def lendMutReturn : Expr := lendProg (cbOf logOK)
/-- The `imm` lend whose callback reads and raises. -/
def lendImmRaise : Expr := lendProg (cbOf readRaise)

theorem d_lendMutRaise : CDerives LifeCtx.empty [] lendMutRaise (.comp (.ret (.sum Flag .unit))) :=
  d_lendProg d_withborMut (fun _ h => d_cbMut h (fun h' => d_logRaise2 h'))

theorem d_lendMutReturn :
    CDerives LifeCtx.empty [] lendMutReturn (.comp (.ret (.sum Flag .unit))) :=
  d_lendProg d_withborMut (fun _ h => d_cbMut h (fun h' => d_logOK h'))

theorem d_lendImmRaise : CDerives LifeCtx.empty [] lendImmRaise (.comp (.ret (.sum Flag .unit))) :=
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

The answer is `inr ()`, the error delivered, or `inl s`, the cell's state at the lender's `free`
(`inr ()` written through the view, `inl ()` untouched); `eval` also reports that no cell is
left, so on the raise the source was dropped. -/

/-- `0`: the error, no cell left; `1`: returned untouched; `2`: returned written; `3`: other. -/
def outcome (e : Expr) : Nat :=
  match eval e with
  | .value ⟨.inj₂ .unit, _⟩ false => 0
  | .value ⟨.inj₁ (.inj₁ .unit), _⟩ false => 1
  | .value ⟨.inj₁ (.inj₂ .unit), _⟩ false => 2
  | _ => 3

/-- **`mut`, raise**: the error is delivered and the source dropped. -/
theorem lendMutRaise_run : outcome lendMutRaise = 0 := by decide

/-- **`mut`, return**: the write is seen by the lender after the borrow ends. -/
theorem lendMutReturn_run : outcome lendMutReturn = 2 := by decide

/-- **`imm`, raise**: the error is delivered and the source dropped. -/
theorem lendImmRaise_run : outcome lendImmRaise = 0 := by decide

/-! ### Nested: a reborrow of the view inside the callback

Inside the outer callback, the view `m : Mut 'x Flag` is itself lent by the same derived form, at
`withbor3` (a reborrow, `'y ⊏ 'x`). The inner source is a view: its destructor, by its type, is its
derived drop, `forget`. The inner callback writes and raises; the inner lend ends, `m` is
forgotten, the error is raised in the outer callback, caught there, and the outer lend ends; then
the cell's destructor runs, and the error goes on. -/

abbrev Δx : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

/-- A view's destructor, by its type: its derived drop (`forget`). -/
theorem dropOf_mutFlag {decl : Opaque → Option Expr} :
    dropOf decl (.mut (.var 0) Flag) = some (derivedDropB (.mut (.var 0) Flag)) :=
  dropOf_derived rfl .mut

theorem d_dropMut (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives Δx Γ' (.val (.lam (derivedDropB (.mut (.var 0) Flag))))
      (.comp (.arr (.mut (.var 0) Flag) (CTy.effOf Sf .unit))) :=
  derivedDropB_derives .mut Sf Γ' hΓ

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

/-- The outer callback's body, the view at `2`: `m ← return m; p ← lendD raise cbInner drop_m; (m, b) = p;
forget m; b`. -/
def nestedBody : Expr :=
  bindE (.var 2) (bindE (lendD failSig (cbOf (logRaise 2)) (derivedDropB (.mut (.var 0) Flag)))
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
    (d_lendD hΓ' d_withbor3 (fun _ h => d_cbInner h) d_dropMut (RowLe.refl Sf) rfl rfl rfl .unit
      (fun h => absurd h Sf_not_unr')) ?_
  refine .tensorE (.left (.dead (deadSplit hΓ'))) (.var (.here (by cdead))) ?_
  exact .unitE (.right (.left (.dead (.dead (deadSplit hΓ')))))
    (appW (.var (by csolo)) (.forgetMut (by cdead)))
    (.effSub (RowLe.nil Sf) (.ret (.var (.here (by cdead)))))

/-- The nested program: a `mut` lend of the cell, its callback reborrowing and raising inside. -/
def lendNested : Expr := lendProg (cbOf nestedBody)

theorem d_lendNested : CDerives LifeCtx.empty [] lendNested (.comp (.ret (.sum Flag .unit))) :=
  d_lendProg d_withborMut (fun _ h => d_cbMut h (fun h' => d_nestedBody h'))

theorem lendNested_safe {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem lendNested μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) :=
  resourceSafety (by decide) d_lendNested hs

/-- **Nested, raise**: both lends ended, the source dropped, the error delivered. -/
theorem lendNested_run : outcome lendNested = 0 := by decide

end BoCa.Fig16.LogRel.Core.LetDtor.Lend

end
