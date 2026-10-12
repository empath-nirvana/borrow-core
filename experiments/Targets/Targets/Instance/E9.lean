import Targets.Instance.E8

/-!
# The Instance — E9 (a stored continuation) at `J₁`

`stash M = handle yield {return _ ⇒ λc. ff; yield (x, k) ⇒ λc. case c of inl _ ⇒ cancel k; x |
inr _ ⇒ resume k () to g. g (inr ())} M`: the clause answers a closure that holds the affine `κ`
(`d_stashCl`), at the answer type `U(bool ⊸ F_Σ bool)` (`stashR`).  The closure is applied after the
handler has returned.  `e9 gen (inr ())` resumes `κ` there (E9a), `e9 gen (inl ())` cancels it
(E9b), and in `e9c` the stored `κ`'s region holds a finaliser that raises `exnₒ`, handled outside
(E9c, `yield`'s cancel row holding `exnₒ`).

The closure's cancel branch holds `x : bool` across `cancel k`, a `[let]` at the closure's row,
which asks the continuation's context to be persistent when the row has an `unr` operation.  In
`e9c` that row holds `exnₒ`, so the typing here is at an affine `exnₒ` (`NoUnrExn`), as E5's.
`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont Heap performE raiseE hndE hndVal opPayload cancelVal kappaC kappaCell
  kappaCBody kappaAt capTag freeE ubindE cfinE ccatchE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg RowAt rowAt_nil CDerivesAt lookEnd)

/-! ### The programs, as our instance writes them -/

/-- `return _ ⇒ λc. ff`. -/
def stashRetE : Expr := .lam (.lam (.inj₁ .unit))

/-- `yield (x, k) ⇒ λc. case c of inl _ ⇒ cancel k; x | inr _ ⇒ resume k () to g. g (inr ())`. -/
def stashClE : Expr := .lam (.letpair (.var 0) (.lam (.case (.var 0)
  (bindE (cancelE (.var 2)) (.var 4))
  (bindE (resumeE (.var 2) .unit) (appE (.var 0) (.inj₂ .unit))))))

/-- `stash M` at the name `ny` and the tags `qy`. -/
def stashE (ny : UInt32) (qy M : Expr) : Expr := (handleK ny qy stashRetE [stashClE]).plug M

/-- `yield tt; yield ff`. -/
def gen9E (ny : UInt32) : Expr :=
  bindE (performE (opArgE ny 0 (.inj₂ .unit))) (performE (opArgE ny 0 (.inj₁ .unit)))

/-- `stash M to g. g c`. -/
def e9E (ny : UInt32) (qy M c : Expr) : Expr := bindE (stashE ny qy M) (appE (.var 0) c)

/-- `handle exnₒ {…} (stash (gen then x. return x unwind raise exnₒ ()) to g. g (inl ()))`. -/
def e9cE (ny no : UInt32) (qy qo : Expr) : Expr :=
  toResultE no qo (e9E ny qy ((thenK (.var 0) (raiseE (opArgE no 0 .unit))).plug (gen9E ny))
    (.inj₁ .unit))

section Vals
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem e9_val (ly : (orowAlg Ξ).Lab) (c : (𝕁).Val) :
    ((𝕁).e9 ly ((𝕁).gen9 ly) c : Expr) = e9E ly.1 (qsOf Ξ ly.1) (gen9E ly.1) c.1 := rfl

theorem e9c_val (ly lo : (orowAlg Ξ).Lab) :
    ((𝕁).e9c ly lo : Expr) = e9cE ly.1 lo.1 (qsOf Ξ ly.1) (qsOf Ξ lo.1) := rfl

end Vals

/-! ### Typing -/

/-- `stash`'s answer at the row `S`: a closure `U(bool ⊸ F_S bool)`. -/
abbrev stashR (S : Row) : VTy := .thunk (.arr boolT (CTy.effOf S boolT))

theorem isVal_stashH : IsVal (.pair stashRetE (clausesE [stashClE])) := .pair .lam (.pair .lam .unit)

section Typing
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- `return _ ⇒ λc. ff` at the row `S`. -/
theorem d_stashRet {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) :
    CDerivesAt Ξ Δ Γ stashRetE (.val (retTy S .unit (stashR S))) :=
  d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.thunkV rfl (.lam (.effSub (rowLe_nil S)
    (.ret (.sumI₁ (.unitI (.drop rfl (.drop rfl hΓ.toP))))))))))

/-- **`stash`'s clause** at the affine `bool ↠ 1` of cancel row `F`, at a row `S` with no `unr`
operation: the closure it answers holds `k` and `x`; its cancel branch is a `[let]` of `cancel k`,
whose `F_{F ⊕ S} 1` is read at `S`, holding `x` across it; its resume branch a `[let]` of
`resume k ()`, applying the closure the resumed computation answers. -/
theorem d_stashCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {F : CTy}
    (hF : F.isTop = false) (hFS : RowLe (F.rowOf ++ S) S) (hU : ¬ S.Unr) :
    CDerivesAt Ξ Δ Γ stashClE (.val (clauseTy S (stashR S) (.aff, boolT, .unit) F)) := by
  rw [clauseTy_resF F rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  -- `k` at `0`, `x` at `1`; the closure `λc. …`
  refine .effSub (rowLe_nil S) (.ret (.thunkV rfl (.lam ?_)))
  -- `c` at `0`, `k` at `1`, `x` at `2`
  refine .sumE (A := .unit) (B := .unit) (.left (.right (.right (.dead (deadSplit hΓ)))))
    (.var (.here (.cons (.cons (.cons hΓ.toP))))) ?_ ?_
  · -- `inl _ ⇒ cancel k; x`: `u` at `0`, `k` at `2`, `x` at `3`
    have hct : cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit := by simp [cancelTy, hF]
    refine .effLet (A := .unit) (.right (.dead (.left (.right (.dead (deadSplit hΓ))))))
      (fun _ => fun s hs hl => ?_) (fun hS => absurd hS hU) ?_ ?_
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | hs
      · exact .unit
      · cases hl
      · cases hl
      · exact .sum .unit .unit
      · cases hl
      · exact dead_noLive (P := fun s => s.ty.Drop) hΓ s hs hl
    · refine .effSub hFS ?_
      rw [← hct]
      exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S (stashR S))) (cancelTy S F))
        (.there (.there (.here (.cons (.cons hΓ.toP))))))
    · exact .effSub (rowLe_nil S) (.ret (.var (.skip rfl (.skip rfl (.there (.there
        (.here (.cons hΓ.toP))))))))
  · -- `inr _ ⇒ resume k () to g. g (inr ())`
    refine .effLet (A := stashR S) (.left (.dead (.left (.left (.dead (deadSplit hΓ))))))
      (fun _ => fun s hs hl => ?_) (fun hS => absurd hS hU) ?_ ?_
    · simp only [List.mem_cons] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | hs
      · cases hl
      · cases hl
      · cases hl
      · cases hl
      · cases hl
      · exact dead_noLive (P := fun s => s.ty.Drop) hΓ s hs hl
    · -- `resume k ()`: `() to y. k (inj₁ ()) y`
      refine .bind (.left (.dead (.right (.left (.dead (deadSplit hΓ))))))
        (.ret (.unitI (.drop rfl (.cons (.cons (.drop rfl (.cons hΓ.toP))))))) ?_
      show CDerivesAt Ξ Δ _ (.app (.app (.var 3) (.inj₁ .unit)) (.var 0)) _
      exact .app (.right (.dead (.dead (.left (.dead (.dead (deadSplit hΓ)))))))
        (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S (stashR S))) (cancelTy S F))
          (.there (.there (.there (.here (.cons (.cons hΓ.toP))))))))
        (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))
    · -- `g (inr ())`
      have hΓd : Ctx.Dead ([⟨.unit, false⟩, ⟨boolT, false⟩,
          ⟨kTy S (stashR S) .aff .unit F, false⟩, ⟨boolT, false⟩,
          ⟨.tensor boolT (kTy S (stashR S) .aff .unit F), false⟩] ++ Γ) :=
        .cons (.cons (.cons (.cons (.cons hΓ))))
      exact .bind (.right (deadSplit hΓd)) (.ret (.sumI₂ (.unitI (.cons hΓd.toP))))
        (.app (.right (.left (deadSplit hΓd))) (.force (C := .arr boolT (CTy.effOf S boolT))
          (.there (.here hΓd.toP))) (.here (.cons hΓd.toP)))

/-- `stash`'s handler value at the row `S`, `yield`'s cancel row `F`. -/
theorem d_stashH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {F : CTy}
    (hF : F.isTop = false) (hFS : RowLe (F.rowOf ++ S) S) (hU : ¬ S.Unr) :
    CDerivesAt Ξ Δ Γ (.pair stashRetE (clausesE [stashClE]))
      (.val (.tensor (retTy S .unit (stashR S))
        (clausesTy S (stashR S) [(.aff, boolT, .unit)] (fun _ => F)))) :=
  .tensorI (deadSplit hΓ) (d_stashRet hΓ S)
    (.tensorI (deadSplit hΓ) (d_stashCl hΓ hF hFS hU) (.unitI hΓ.toP))

/-- **`stash M` at the row `S`**, `M` at `yield`'s row of cancel row `F` before `S`. -/
theorem d_stash {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) {S : Row}
    (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ ly.1) {F : CTy} (hF : F.isTop = false)
    (hFS : RowLe (F.rowOf ++ S) S) (hU : ¬ S.Unr) {M : Expr}
    (hM : CDerivesAt Ξ LifeCtx.empty [] M
      (.comp (CTy.effOf (Row.ofEff ly.1 [(.aff, boolT, .unit)] 0 (fun _ => F) ++ S) .unit))) :
    CDerivesAt Ξ LifeCtx.empty [] (stashE ly.1 (qsOf Ξ ly.1) M) (.comp (CTy.effOf S (stashR S))) := by
  rw [← hly] at hM
  refine d_handleKF (fs := fun _ => F) (Targets.rowAt_append (rowAt_rowOf ly) hS) ly.2.1 hnS
    ly.2.2.2 isVal_stashH ?_ hM
  rw [hly]
  exact d_stashH .nil hF hFS hU

/-- `yield tt; yield ff` at `yield`'s row. -/
theorem d_gen9 {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) :
    CDerivesAt Ξ LifeCtx.empty [] (gen9E ly.1)
      (.comp (CTy.effOf (Row.ofEff ly.1 [(.aff, boolT, .unit)] 0 ++ []) .unit)) :=
  .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil)
    (d_performLab ly hly rfl (.sumI₂ (.unitI .nil)))
    (d_performLab ly hly rfl (.sumI₁ (.unitI (.drop rfl .nil))))

theorem not_unr_nil : ¬ Row.Unr ([] : Row) := fun ⟨_, h, _⟩ => absurd h List.not_mem_nil

/-- **`e9 gen c` is typed by `J₁`'s kernel**, at the pure row: `stash` answers the closure, which is
applied to `c`. -/
theorem d_e9 {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) {c : Expr}
    (hc : CDerivesAt Ξ LifeCtx.empty [⟨stashR [], false⟩] c (.val boolT)) :
    CDerivesAt Ξ LifeCtx.empty [] (e9E ly.1 (qsOf Ξ ly.1) (gen9E ly.1) c) (.comp (.ret boolT)) := by
  refine .bind (A := stashR []) .nil ?_ (d_callVar hc)
  exact d_stash hly (S := []) (rowAt_nil Ξ) (by simp) (F := .ret .unit) rfl
    (by simpa [CTy.rowOf] using RowLe.refl ([] : Row)) not_unr_nil (d_gen9 hly)

/-- `yield`'s operation at the cancel row `F`, as `stash`'s handled row finds it. -/
theorem find_yield_at (ny : UInt32) (F : CTy) (S : Row) :
    Row.find (Row.ofEff ny [(.aff, boolT, .unit)] 0 (fun _ => F) ++ S) ny 0 =
      some ⟨ny, 0, .aff, boolT, .unit, F⟩ := by
  simp [Row.ofEff, Row.find]

/-- **`e9c` is typed by `J₁`'s kernel**, at an affine `exnₒ`: `yield`'s cancel row holds the
finaliser's raise of `exnₒ`, whose handler is live where the closure cancels `κ`. -/
theorem d_e9c {ly lo : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)])
    (hlo : Ξ lo.1 = [(.aff, .unit, .zero)]) (hne : ly.1 ≠ lo.1) :
    CDerivesAt Ξ LifeCtx.empty [] (e9cE ly.1 lo.1 (qsOf Ξ ly.1) (qsOf Ξ lo.1))
      (.comp (.ret (.sum boolT .unit))) := by
  have hSlo := rowAt_ofEff_lab lo hlo
  have hnlo : ∀ o ∈ Row.ofEff lo.1 [(.aff, .unit, .zero)] 0 ++ [], o.n ≠ ly.1 :=
    names_ofEff hne.symm
  have hUlo : ¬ (Row.ofEff lo.1 [(.aff, .unit, .zero)] 0 ++ []).Unr := by
    rintro ⟨o, ho, hq⟩
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    subst ho
    cases hq
  refine d_toResult hlo (by decide) (S := []) (rowAt_nil Ξ) (by simp) ?_
  refine .effLet (A := stashR (Row.ofEff lo.1 [(.aff, .unit, .zero)] 0 ++ [])) .nil
    (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
    ?_ (d_callVar (.sumI₁ (.unitI (.cons .nil))))
  refine d_stash hly hSlo hnlo (F := finRaise lo.1 .aff) rfl ?_ hUlo ?_
  · refine RowLe.of_find fun n i o hf => ?_
    rw [Row.find_append] at hf
    simp only [CTy.rowOf, CTy.effOf] at hf
    rw [List.append_nil]
    by_cases hk : n = lo.1 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      simp [Row.find] at hf
      subst hf
      simp [Row.ofEff, Row.find]
    · have : Row.find [⟨lo.1, 0, .aff, .unit, .zero, .ret .unit⟩] n i = none := by
        simp only [Row.find, List.find?_cons, List.find?_nil]
        rw [decide_eq_false hk]
      rw [this, Option.none_or, List.append_nil] at hf
      exact hf
  -- `gen then x. return x unwind raise exnₒ ()` at `yield`'s row of cancel row `{exnₒ}`
  set F := finRaise lo.1 .aff
  refine .effThen (SM := Row.ofEff ly.1 [(.aff, boolT, .unit)] 0 ++ [])
    (SD := Row.ofEff lo.1 [(.aff, .unit, .zero)] 0 ++ []) .nil ?_ ?_
    (fun _ => fun _ h => absurd h List.not_mem_nil) ?_ (rowLe_ofEff_consF _ _ hnlo) ?_ ?_
    (d_gen9 hly) (.effSub (rowLe_nil _) (.ret (.var (.here .nil))))
    (d_raiseLab (.cons .nil) lo hlo (by decide) .unit)
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact ly.2.1
    · exact lo.2.1
  · simp [Row.Uniq, Row.ofEff, hne]
  · intro n i o hf
    rw [List.append_nil] at hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one (fs := finsNil) hf
    refine ⟨_, find_yield_at ly.1 F _, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    rw [finLe_iff]
    exact .inr ⟨rfl, RowLe.nil _⟩
  · intro n i o o' hf hf' _
    rw [List.append_nil] at hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one (fs := finsNil) hf
    rw [find_yield_at ly.1 F _] at hf'
    cases hf'
    exact thenLe_finRaise lo.1 .aff
  · intro _ o ho
    rw [List.append_nil] at ho
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, VTy.isZero] at h, fun _ => trivial⟩

/-- **`e9 gen c` is typed by `J₁`**, at `c` either injection of `()`. -/
theorem der_e9_J₁ {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) {c : (𝕁).Val}
    (hc : CDerivesAt Ξ LifeCtx.empty [⟨stashR [], false⟩] c.1 (.val boolT)) :
    (𝕁).der [] ((𝕁).e9 ly ((𝕁).gen9 ly) c) ((𝕁).F (𝕁).EA.unit (𝕁).bool) := by
  have hd := d_e9 hly hc
  rw [e9_val]
  exact der_J₁_ret (A := boolT) (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- **`e9c` is typed by `J₁`**, at an affine `exnₒ`. -/
theorem der_e9c_J₁ {ly lo : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)])
    (hlo : Ξ lo.1 = [(.aff, .unit, .zero)]) (hne : ly.1 ≠ lo.1) :
    (𝕁).der [] ((𝕁).e9c ly lo) ((𝕁).F (𝕁).EA.unit ((𝕁).Sum (𝕁).bool (𝕁).UnitT)) := by
  have hd := d_e9c hly hlo hne
  rw [e9c_val]
  exact der_J₁_ret (A := .sum boolT .unit) (by simpa using closedAt_of_derives hd.toCDerives) hd

end Typing

/-! ### The runs -/

/-- `stash`'s handler value at the name `ny`, its `yield` affine. -/
def sH (ny : UInt32) : Val :=
  hndVal ny (qualsVal [.aff]) ⟨stashRetE, .lam⟩ ⟨clausesE [stashClE], .pair .lam .unit⟩

theorem stashE_aff (ny : UInt32) (M : Expr) : stashE ny qA M = hndE (sH ny) M := rfl

/-- Around the allocation of `κ`'s cell, after `stash`'s catch of `yield v` in `K`. -/
def sKA (ny : UInt32) (v : Val) (K : Kont) : Kont :=
  .appR stashClE (.pairR v (.appR (.lam (kappaCBody true (sH ny) K)) .hole))

/-- The rest of `gen` after its first `yield`. -/
abbrev Kg (ny : UInt32) : Kont := bindK (performE (opArgE ny 0 (.inj₁ .unit)))

/-- `gen`'s first `yield` in its frame holding the finaliser `raise exnₒ ()`. -/
abbrev Kc (ny no : UInt32) : Kont := (thenK (.var 0) (raiseE (opArgE no 0 .unit))).comp (Kg ny)

/-- `□ to g. g c`: the stored closure's call. -/
abbrev Kcall (c : Expr) : Kont := bindK (appE (.var 0) c)

/-- **`stash`'s catch of `yield v`**: the clause applied to `v` and `κ`, whose cell is still to be
allocated. -/
theorem quiet_sHop (ny : UInt32) (v : Val) (K : Kont) (hK : K.HasHnd ny = false) :
    Quiet (ℍ := ℍ) (hndE (sH ny) (K.plug (performE (.val (opPayload ny 0 v)))))
      ((sKA ny v K).plug (allocE Val.unit)) := by
  have hk : kappaAt (capTag (qualsVal [.aff]).1 (0 : UInt32).toNat) (sH ny) K =
      kappaCell true (sH ny) K := by
    simp [capTag, qualsVal, Qual.tag, kappaAt, Val.pair, Val.i32]
  have hh : ∀ μ, Head (ℍ := ℍ) μ (hndE (sH ny) (K.plug (performE (.val (opPayload ny 0 v)))))
      μ (.app (.val ⟨stashClE, .lam⟩) (.pair (.val v) (kappaCell true (sH ny) K))) := by
    intro μ
    have h := Head.hop (ℍ := ℍ) μ ny 0 (qualsVal [.aff]) ⟨stashRetE, .lam⟩
      ⟨clausesE [stashClE], .pair .lam .unit⟩ ⟨stashClE, .lam⟩ v K
      (clauseAt_clausesE [stashClE] 0 .lam rfl) hK
    simp only [sH] at hk ⊢
    rwa [hk] at h
  exact Quiet.head (ℍ := ℍ) .hole hh rfl rfl

/-! #### Look's segments: no catch, no memory step -/

/-- The first `yield`'s catch, cancelled: from the cell, the closure answered and called at
`inl ()`, which cancels `κ`, up to the release of the cell. -/
theorem e9b_seg (ny : UInt32) (ℓ : Loc) :
    lookEnd 10 (((Kcall (.inj₁ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kg ny))).plug
      (.val (Val.loc ℓ))) = (tmKF (Kg ny)).plug (freeE (.val (Val.loc ℓ))) := by rfl

theorem e9b_seg_quiet (ny : UInt32) (ℓ : Loc) :
    (Targets.lookRun 10 (((Kcall (.inj₁ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kg ny))).plug
      (.val (Val.loc ℓ)))).all (fun x => !finHead x.2.1) = true := by rfl

/-- The same in `e9c`, `κ`'s region holding the finaliser frame. -/
theorem e9c_seg (ny no : UInt32) (ℓ : Loc) :
    lookEnd 10 (((Kcall (.inj₁ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kc ny no))).plug
      (.val (Val.loc ℓ))) = (tmKF (Kc ny no)).plug (freeE (.val (Val.loc ℓ))) := by rfl

theorem e9c_seg_quiet (ny no : UInt32) (ℓ : Loc) :
    (Targets.lookRun 10 (((Kcall (.inj₁ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kc ny no))).plug
      (.val (Val.loc ℓ)))).all (fun x => !finHead x.2.1) = true := by rfl

/-- The first `yield`'s catch, resumed: from the cell, the closure answered and called at
`inr ()`, which resumes `κ`, up to the release of the cell. -/
theorem e9a_seg1 (ny : UInt32) (ℓ : Loc) :
    lookEnd 11 (((Kcall (.inj₂ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kg ny))).plug
      (.val (Val.loc ℓ))) =
      ((Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) (Kg ny))) Val.unit)).plug
        (freeE (.val (Val.loc ℓ))) := by rfl

theorem e9a_seg1_quiet (ny : UInt32) (ℓ : Loc) :
    (Targets.lookRun 11 (((Kcall (.inj₂ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kg ny))).plug
      (.val (Val.loc ℓ)))).all (fun x => !finHead x.2.1) = true := by rfl

/-- After the release, the resume reinstalls `stash`, and `gen` yields again. -/
theorem e9a_seg2 (ny : UInt32) :
    lookEnd 3 (((Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) (Kg ny)))
      Val.unit)).plug (.val Val.unit)) =
      (Kcall (.inj₂ .unit)).plug (hndE (sH ny) (Kont.hole.plug
        (performE (.val (opPayload ny 0 (Val.inj₁ Val.unit)))))) := by rfl

theorem e9a_seg2_quiet (ny : UInt32) :
    (Targets.lookRun 3 (((Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) (Kg ny)))
      Val.unit)).plug (.val Val.unit))).all (fun x => !finHead x.2.1) = true := by rfl

/-- The second `yield`'s catch, resumed: from the cell, the second closure answered and called at
`inr ()`, which resumes `κ`, up to the release of the cell. -/
theorem e9a_seg3 (ny : UInt32) (ℓ : Loc) :
    lookEnd 11 (((Kcall (.inj₂ .unit)).comp (sKA ny (Val.inj₁ Val.unit) .hole)).plug
      (.val (Val.loc ℓ))) =
      ((Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) .hole)) Val.unit)).plug
        (freeE (.val (Val.loc ℓ))) := by rfl

theorem e9a_seg3_quiet (ny : UInt32) (ℓ : Loc) :
    (Targets.lookRun 11 (((Kcall (.inj₂ .unit)).comp (sKA ny (Val.inj₁ Val.unit) .hole)).plug
      (.val (Val.loc ℓ)))).all (fun x => !finHead x.2.1) = true := by rfl

/-- After the second release, `gen` returns, `stash` answers `λc. ff`, and the call answers `ff`. -/
theorem e9a_seg4 (ny : UInt32) :
    lookEnd 7 (((Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) .hole))
      Val.unit)).plug (.val Val.unit)) = .inj₁ .unit := by rfl

theorem e9a_seg4_quiet (ny : UInt32) :
    (Targets.lookRun 7 (((Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) .hole))
      Val.unit)).plug (.val Val.unit))).all (fun x => !finHead x.2.1) = true := by rfl

/-! #### E9a and E9b: calm runs -/

/-- **The stored `κ`, cancelled** (E9b): `stash`'s catch allocates `κ`'s cell, the closure it answers
is called at `inl ()` and cancels `κ`, which releases the cell; the cancel answers `()`, and the
call `tt`. -/
theorem calm_e9b (ny : UInt32) :
    Calm (ℍ := ℍ) (e9E ny qA (gen9E ny) (.inj₁ .unit)) (.inj₂ .unit) := by
  have hc : CellQuiet (ℍ := ℍ) (e9E ny qA (gen9E ny) (.inj₁ .unit))
      ((bindK (.inj₂ .unit)).plug (Targets.cancelOf (Kg ny))) := by
    refine ⟨(Kcall (.inj₁ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kg ny)), ?_, fun ℓ =>
      ⟨tmKF (Kg ny), ?_, ?_⟩⟩
    · rw [Kont.plug_comp]
      exact (quiet_sHop ny (Val.inj₂ Val.unit) (Kg ny) rfl).plug (Kcall (.inj₁ .unit))
    · have h := quiet_of_look (ℍ := ℍ) 10 _ (e9b_seg_quiet ny ℓ)
      rwa [e9b_seg] at h
    · have h := (kappaC_cancel_parts (ℍ := ℍ) ℓ (sH ny) (Kg ny)).2.plug (bindK (.inj₂ .unit))
      rw [tmKF, Kont.plug_comp]
      exact h
  have q₁ := (Quiet.head (ℍ := ℍ) .hole (fun μ => Head.cancel μ (Kg ny) rfl) rfl rfl).plug
    (bindK (.inj₂ .unit))
  have q₂ := quiet_beta (ℍ := ℍ) .hole (.inj₂ .unit) Val.unit
  exact hc.calm.trans ((q₁.trans q₂).calm)

/-- **The stored `κ`, resumed** (E9a): `stash`'s catch allocates `κ`'s cell, the closure it answers
is called at `inr ()` and resumes `κ`, which releases the cell and reinstalls `stash`; the second
yield is caught likewise, its closure resumes, `gen` returns, and the call answers `ff`. -/
theorem calm_e9a (ny : UInt32) :
    Calm (ℍ := ℍ) (e9E ny qA (gen9E ny) (.inj₂ .unit)) (.inj₁ .unit) := by
  have hc₁ : CellQuiet (ℍ := ℍ) (e9E ny qA (gen9E ny) (.inj₂ .unit))
      ((Kcall (.inj₂ .unit)).plug (hndE (sH ny) (Kont.hole.plug
        (performE (.val (opPayload ny 0 (Val.inj₁ Val.unit))))))) := by
    refine ⟨(Kcall (.inj₂ .unit)).comp (sKA ny (Val.inj₂ Val.unit) (Kg ny)), ?_, fun ℓ =>
      ⟨(Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) (Kg ny))) Val.unit),
        ?_, ?_⟩⟩
    · rw [Kont.plug_comp]
      exact (quiet_sHop ny (Val.inj₂ Val.unit) (Kg ny) rfl).plug (Kcall (.inj₂ .unit))
    · have h := quiet_of_look (ℍ := ℍ) 11 _ (e9a_seg1_quiet ny ℓ)
      rwa [e9a_seg1] at h
    · have h := quiet_of_look (ℍ := ℍ) 3 _ (e9a_seg2_quiet ny)
      rwa [e9a_seg2] at h
  have hc₂ : CellQuiet (ℍ := ℍ) ((Kcall (.inj₂ .unit)).plug (hndE (sH ny) (Kont.hole.plug
      (performE (.val (opPayload ny 0 (Val.inj₁ Val.unit))))))) (.inj₁ .unit) := by
    refine ⟨(Kcall (.inj₂ .unit)).comp (sKA ny (Val.inj₁ Val.unit) .hole), ?_, fun ℓ =>
      ⟨(Kcall (.inj₂ .unit)).comp (Kont.appL (Kont.seq .hole (kResV (sH ny) .hole)) Val.unit),
        ?_, ?_⟩⟩
    · rw [Kont.plug_comp]
      exact (quiet_sHop ny (Val.inj₁ Val.unit) .hole rfl).plug (Kcall (.inj₂ .unit))
    · have h := quiet_of_look (ℍ := ℍ) 11 _ (e9a_seg3_quiet ny ℓ)
      rwa [e9a_seg3] at h
    · have h := quiet_of_look (ℍ := ℍ) 7 _ (e9a_seg4_quiet ny)
      rwa [e9a_seg4] at h
  exact hc₁.calm.trans hc₂.calm

section Runs
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **E9a's run**: it answers `ff`, showing nothing. -/
theorem runsTo_e9a {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e9 ly ((𝕁).gen9 ly) ((𝕁).inr (𝕁).unitV)) (𝕁).ff [] := by
  rw [e9_val, qsOf_eq hly]
  exact runsTo_of_calm (𝕁).R₀ (v := Val.inj₁ Val.unit) (calm_e9a ly.1)

/-- **E9b's run**: it answers `tt`, showing nothing. -/
theorem runsTo_e9b {ly : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e9 ly ((𝕁).gen9 ly) ((𝕁).inl (𝕁).unitV)) (𝕁).tt [] := by
  rw [e9_val, qsOf_eq hly]
  exact runsTo_of_calm (𝕁).R₀ (v := Val.inj₂ Val.unit) (calm_e9b ly.1)

/-- **The stored `κ` with a finaliser, cancelled**: from `e9c`, at every memory with finitely many
cells, the complete runs are those from the cancel's start, inside `toResult` and the call's
`□; return tt`. -/
theorem obsFrom_e9cCatch (ny no : UInt32) (q : Qual) {μ : Heap} (hf : FinDom μ) (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, e9cE ny no qA (qualsVal [q]).1), ()) w tr ↔
      (𝕁).ObsFrom (𝕁).R₀ ((μ, ((trK no q).comp (bindK (.inj₂ .unit))).plug
        (Targets.cancelOf (Kc ny no))), ()) w tr := by
  have e₀ : e9cE ny no qA (qualsVal [q]).1 = ((trK no q).comp (Kcall (.inj₁ .unit))).plug
      (hndE (sH ny) ((Kc ny no).plug (performE (.val (opPayload ny 0 (Val.inj₂ Val.unit)))))) := rfl
  rw [e₀]
  refine (obsFrom_quiet_iff _ ((quiet_sHop ny (Val.inj₂ Val.unit) (Kc ny no) rfl).plug
    ((trK no q).comp (Kcall (.inj₁ .unit)))) w tr).trans ?_
  rw [← Kont.plug_comp]
  refine obsFrom_alloc_iff _ (((trK no q).comp (Kcall (.inj₁ .unit))).comp
    (sKA ny (Val.inj₂ Val.unit) (Kc ny no))) Val.unit (exists_fresh_of_finDom hf)
    (Q := fun w tr => (𝕁).ObsFrom (𝕁).R₀ ((μ, ((trK no q).comp (bindK (.inj₂ .unit))).plug
      (Targets.cancelOf (Kc ny no))), ()) w tr) (fun ℓ hℓ w tr => ?_) w tr
  have q₁ := quiet_of_look (ℍ := ℍ) 10 _ (e9c_seg_quiet ny no ℓ)
  rw [e9c_seg] at q₁
  rw [Kont.comp_assoc, Kont.plug_comp]
  refine (obsFrom_quiet_iff _ (q₁.plug (trK no q)) w tr).trans ?_
  rw [← Kont.plug_comp]
  refine (obsFrom_mstep_iff _ (Head.free _ ℓ Val.unit (Heap.upd_same _ _ _)) rfl
    (by rw [labelOf_tau_of rfl]; rfl) w tr).trans ?_
  rw [del_upd_fresh hℓ]
  have h₄ := (kappaC_cancel_parts (ℍ := ℍ) ℓ (sH ny) (Kc ny no)).2.plug
    ((trK no q).comp (bindK (.inj₂ .unit)))
  have e : ((trK no q).comp (bindK (.inj₂ .unit))).plug ((Kont.seq .hole (kCanE (Kc ny no))).plug
      (.val Val.unit)) = ((trK no q).comp (tmKF (Kc ny no))).plug (.val Val.unit) := by
    rw [Kont.plug_comp, Kont.plug_comp, tmKF, Kont.plug_comp]
  rw [e] at h₄
  exact obsFrom_quiet_iff _ h₄ w tr

/-- **`e9c`'s complete runs**, from every memory with finitely many cells: the stored `κ`'s cancel
fires the finaliser, which raises `exnₒ`; the cancel re-raises it at the closure, inside
`toResult`, which catches it.  Each answers `inr ()`. -/
theorem obsFrom_e9c (ly lo : (orowAlg Ξ).Lab) (q : Qual) {μ : Heap} (hf : FinDom μ) (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, e9cE ly.1 lo.1 qA (qualsVal [q]).1), ()) w tr ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧ tr = (𝕁).finTr lo := by
  have hT : ∀ tr', (𝕁).ObsFrom (𝕁).R₀ ((μ, ((Kont.hole.comp (trK lo.1 q)).comp
      (Kont.hole.comp ((bindK (.inj₂ .unit)).comp (ccatchK .hole)))).plug
        (cfinE (cancelVal none) (.app (.val (raiseFin lo.1)) (.val .unit)))), ()) w tr' ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧ tr' = [.finEnd (some (lo, 0, (𝕁).unitV))] := by
    intro tr'
    refine (obsFrom_finRaise _ none lo w tr').trans ?_
    constructor
    · rintro ⟨tr'', rfl, h⟩
      obtain ⟨hw, rfl⟩ := ((obsFrom_reraise_toResult .hole .hole rfl w tr'').trans
        (obsFrom_val_iff _ (Val.inj₂ Val.unit) w tr'')).1 h
      exact ⟨hw, rfl⟩
    · rintro ⟨hw, rfl⟩
      exact ⟨[], rfl, ((obsFrom_reraise_toResult .hole .hole rfl w []).trans
        (obsFrom_val_iff _ (Val.inj₂ Val.unit) w [])).2 ⟨hw, rfl⟩⟩
  refine (obsFrom_e9cCatch ly.1 lo.1 q hf w tr).trans ?_
  refine (obsFrom_ufinC (𝕁).R₀ (s := ()) (((Kont.hole.comp (trK lo.1 q)).comp
    (Kont.hole.comp ((bindK (.inj₂ .unit)).comp (ccatchK .hole))))) (Kg ly.1) ⟨.lam (.var 0), .lam⟩
    (raiseFin lo.1) none rfl w tr).trans ?_
  constructor
  · rintro ⟨tr', rfl, h⟩
    obtain ⟨hw, rfl⟩ := (hT tr').1 h
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨_, rfl, (hT _).2 ⟨hw, rfl⟩⟩

/-- **E9c's run**: it answers `inr ()`, showing the stored `κ`'s finaliser fired by its cancel and
its end with the raise of `exnₒ`. -/
theorem runsTo_e9c {ly lo : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) {q : Qual}
    (hlo : Ξ lo.1 = [(q, .unit, .zero)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e9c ly lo) ((𝕁).inr (𝕁).unitV) ((𝕁).finTr lo) := by
  rw [e9c_val, qsOf_eq hly, qsOf_eq hlo]
  exact runsTo_of_obsFrom _ (v := Val.inj₂ Val.unit) fun w tr => obsFrom_e9c ly lo q finDom_empty w tr

end Runs

/-! ### E9 -/

section E9
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **E9's labels**: a `yield` and an `exn` label, at a rich context. -/
theorem labelsAt_E9 (hΞ : AdmEff Ξ) : ∃ ls, (𝕁).LabelsAt [(𝕁).sigYield, (𝕁).sigExn] ls := by
  obtain ⟨ly, -, -, hly, -⟩ := rich_labs hΞ.2.2 (E := [(.aff, boolT, .unit)]) (by simp [eSigs])
  obtain ⟨lo, -, -, hlo, -⟩ := rich_labs hΞ.2.2 (E := [(.aff, .unit, .zero)]) (by simp [eSigs])
  refine ⟨[ly, lo], rfl, ?_, fun k h₁ _ => ?_⟩
  · have hne : ly ≠ lo := lab_ne_of_sig (by rw [hly, hlo]; simp)
    exact List.nodup_cons.mpr ⟨fun h => hne (List.mem_singleton.mp h), List.nodup_singleton _⟩
  · match k, h₁ with
    | 0, _ => exact (sig_yield_iff hΞ.1 ly).mpr hly
    | 1, _ => exact (sig_exn_iff lo).mpr ⟨.aff, hlo, by decide⟩

/-- **E9, a stored continuation, at `J₁`**, at every admissible effect context with no `unr` `exn`
signature: the closure holding `κ` is typed (the affine `κ` is captured by a linear closure), and
called after `stash` has returned, resuming (E9a) or cancelling (E9b) `κ`; a stored `κ`'s cancel
fires its region's finaliser, whose raise reaches the handler outside (E9c). -/
theorem storedK_J₁ (hΞ : AdmEff Ξ) (hx : NoUnrExn Ξ) : (𝕁).StoredK := by
  refine ⟨labelsAt_E9 hΞ, fun ls hls ly lo hlsEq => ?_⟩
  subst hlsEq
  have hly := (sig_yield_iff hΞ.1 ly).mp (hls.2.2 0 (by simp) (by simp))
  obtain ⟨q, hlo, hq⟩ := (sig_exn_iff lo).mp (hls.2.2 1 (by simp) (by simp))
  have hqa : q = .aff := by
    cases q with
    | lin => exact absurd rfl hq
    | aff => rfl
    | unr => exact absurd hlo (hx lo.1)
  subst hqa
  have hne : ly.1 ≠ lo.1 := fun h => by rw [h, hlo] at hly; simp at hly
  exact ⟨der_e9_J₁ hly (.sumI₂ (.unitI (.cons .nil))), runsTo_e9a hly,
    der_e9_J₁ hly (.sumI₁ (.unitI (.cons .nil))), runsTo_e9b hly, der_e9c_J₁ hly hlo hne,
    runsTo_e9c hly hlo⟩

end E9

end Targets.Inst

end
