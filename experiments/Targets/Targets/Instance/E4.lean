import Targets.Instance.E6

/-!
# The Instance — E4 (deep handlers) at `J₁`

`deepGen = handle yield {return _ ⇒ (); yield (_, k) ⇒ tick (); resume k ()} (yield tt; yield ff)`
is typed at `tick`'s row (`der_deepGen_J₁`): the handler at the row of `tick`, its clause a resuming
clause whose body performs `tick` before resuming `k` (`d_tickingCl`), the body at `yield`'s row
before `tick`'s.  Its run (`runsTo_deepGen`) answers `()` showing two ticks: each yield is caught
around `κ`'s cell (SPEC §25), the clause's `tick` is answered by the runner, and the resume releases
the cell and reinstalls the handler, which catches the second yield (`obsFrom_dgCatch`).
`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE hndE hndVal opPayload kappaCell kappaCBody kappaC freeE
  kappaAt capTag)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg RowAt CDerivesAt lookEnd)

/-! ### `deepGen`, as our instance writes it -/

/-- `op (_, k) ⇒ tick (); resume k ()`, at the name `nt` of `tick`. -/
def tickingClE (nt : UInt32) : Expr :=
  .lam (.letpair (.var 0) (bindE (performE (opArgE nt 0 .unit)) (resumeE (.var 1) .unit)))

/-- `deepGen`'s handler: `return _ ⇒ ()`, `yield (_, k) ⇒ tick (); resume k ()`. -/
def deepGenH (nt : UInt32) : Expr := .pair (.lam .unit) (clausesE [tickingClE nt])

theorem isVal_deepGenH (nt : UInt32) : IsVal (deepGenH nt) := .pair .lam (.pair .lam .unit)

/-- `deepGen` at the names `ny`, `nt` and the tags `qs`. -/
def deepGenE (ny nt : UInt32) (qs : Expr) : Expr :=
  (handleK ny qs (.lam .unit) [tickingClE nt]).plug
    (bindE (performE (opArgE ny 0 (.inj₂ .unit))) (performE (opArgE ny 0 (.inj₁ .unit))))

/-! ### Typing -/

/-- A row is below itself before any row. -/
theorem rowLe_append_nil (P S : Row) : RowLe (P ++ []) (P ++ S) := by
  intro m i o h
  rw [List.append_nil] at h
  rw [Row.find_append, h, Option.some_or]

/-- A row of one linear operation has no operation whose continuation may be dropped. -/
theorem not_weak_lin (n : UInt32) (A B : VTy) : ¬ (Row.ofEff n [(.lin, A, B)] 0 ++ []).Weak := by
  rintro ⟨o, ho, hq⟩
  simp [Row.ofEff] at ho
  subst ho
  exact hq rfl

/-- A row of one linear operation has no unrestricted operation. -/
theorem not_unr_lin (n : UInt32) (A B : VTy) : ¬ (Row.ofEff n [(.lin, A, B)] 0 ++ []).Unr := by
  rintro ⟨o, ho, hq⟩
  simp [Row.ofEff] at ho
  subst ho
  cases hq

section Typing
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem deepGen_val (ly lt : (orowAlg Ξ).Lab) :
    ((𝕁).deepGen ly lt : Expr) = deepGenE ly.1 lt.1 (qsOf Ξ ly.1) := rfl

/-- **The clause `op (_, k) ⇒ tick (); resume k ()`** at a linear or affine `A ↠ 1`, `A`
persistent, at `tick`'s row: `tick ()` is a `[let]` at a row of one linear operation, so the
continuation holding `k` is neither dropped nor copied. -/
theorem d_tickingCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (lt : (orowAlg Ξ).Lab)
    (hlt : Ξ lt.1 = [(.lin, .unit, .unit)]) (R : VTy) {q : Qual} {A : VTy} (hq : q ≠ .unr)
    (hA : A.Persistent) :
    CDerivesAt Ξ Δ Γ (tickingClE lt.1)
      (.val (clauseTy (Row.ofEff lt.1 [(.lin, .unit, .unit)] 0 ++ []) R (q, A, .unit))) := by
  rw [clauseTy_resuming rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .effLet (.right (.left (.dead (deadSplit hΓ))))
    (fun h => absurd h (not_weak_lin lt.1 .unit .unit))
    (fun h => absurd h (not_unr_lin lt.1 .unit .unit))
    (d_performLab lt hlt rfl (.unitI (.cons (.drop hA (.cons hΓ.toP))))) ?_
  refine .bind (.left (.right (.dead (.dead (deadSplit hΓ)))))
    (.ret (.unitI (.drop rfl (.cons (.cons (.cons hΓ.toP)))))) ?_
  show CDerivesAt Ξ Δ _ (.app (.app (.var 2) (.inj₁ .unit)) (.var 0)) _
  cases q with
  | lin =>
      exact .app (.right (.dead (.left (.dead (.dead (deadSplit hΓ))))))
        (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf _ R)) .top)
          (.there (.there (.here (.cons (.cons hΓ.toP)))))))
        (.here (.cons (.cons (.cons (.cons hΓ.toP)))))
  | aff =>
      exact .app (.right (.dead (.left (.dead (.dead (deadSplit hΓ))))))
        (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf _ R)) (CTy.effOf _ .unit))
          (.there (.there (.here (.cons (.cons hΓ.toP)))))))
        (.here (.cons (.cons (.cons (.cons hΓ.toP)))))
  | unr => exact absurd rfl hq

/-- `deepGen`'s handler at `tick`'s row, answering `()`. -/
theorem d_deepGenH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (lt : (orowAlg Ξ).Lab)
    (hlt : Ξ lt.1 = [(.lin, .unit, .unit)]) {q : Qual} {A : VTy} (hq : q ≠ .unr)
    (hA : A.Persistent) :
    CDerivesAt Ξ Δ Γ (deepGenH lt.1)
      (.val (.tensor (retTy (Row.ofEff lt.1 [(.lin, .unit, .unit)] 0 ++ []) .unit .unit)
        (clausesTy (Row.ofEff lt.1 [(.lin, .unit, .unit)] 0 ++ []) .unit [(q, A, .unit)]))) :=
  .tensorI (deadSplit hΓ) (d_lamBang hΓ (.effSub (rowLe_nil _) (.ret (.unitI (.drop rfl hΓ.toP)))))
    (.tensorI (deadSplit hΓ) (d_tickingCl hΓ lt hlt .unit hq hA) (.unitI hΓ.toP))

/-- **`deepGen` at `tick`'s row**: the body at `yield`'s row before `tick`'s. -/
theorem d_deepGen {ly lt : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)])
    (hlt : Ξ lt.1 = [(.lin, .unit, .unit)]) (hne : ly.1 ≠ lt.1) :
    CDerivesAt Ξ LifeCtx.empty [] (deepGenE ly.1 lt.1 (qsOf Ξ ly.1))
      (.comp (CTy.effOf (Row.ofEff lt.1 [(.lin, .unit, .unit)] 0 ++ []) .unit)) := by
  refine d_handleL ly hly (rowAt_ofEff_lab lt hlt) (fun o ho => ?_) (isVal_deepGenH lt.1)
    (d_deepGenH (kill_dead _) lt hlt (by decide) rfl) ?_
  · rw [List.append_nil] at ho
    rw [mem_ofEff_n ho]
    exact fun h => hne h.symm
  · exact .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil)
      (.effSub (rowLe_append_nil _ _) (d_performLab ly hly rfl (.sumI₂ (.unitI .nil))))
      (.effSub (rowLe_append_nil _ _) (d_performLab ly hly rfl (.sumI₁ (.unitI (.drop rfl .nil)))))

/-- **E4: `deepGen` is typed at `J₁`**, at `tick`'s row. -/
theorem der_deepGen_J₁ {ly lt : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)])
    (hlt : Ξ lt.1 = [(.lin, .unit, .unit)]) (hne : ly.1 ≠ lt.1) :
    (𝕁).der [] ((𝕁).deepGen ly lt) ((𝕁).F ((𝕁).EA.lift lt) (𝕁).UnitT) := by
  have hd := d_deepGen hly hlt hne
  have hcl : closedAt 0 (deepGenE ly.1 lt.1 (qsOf Ξ ly.1)) = true := by
    simpa using closedAt_of_derives hd.toCDerives
  refine der_J₁_closedRow (A := .unit) rfl (rowAt_rowOf lt) hcl ?_
  show CDerivesAt Ξ LifeCtx.empty [] (deepGenE ly.1 lt.1 (qsOf Ξ ly.1))
    (.comp (CTy.effOf (Row.ofEff lt.1 (Ξ lt.1) 0) .unit))
  rwa [List.append_nil, ← hlt] at hd

end Typing

/-! ### The run -/

/-- `deepGen`'s handler at the names `ny` and `nt`, at the affine `yield`. -/
def dgH (ny nt : UInt32) : Val :=
  hndVal ny (qualsVal [.aff]) ⟨.lam .unit, .lam⟩ ⟨clausesE [tickingClE nt], .pair .lam .unit⟩

/-- The second yield. -/
def dgN1 (ny : UInt32) : Expr := performE (opArgE ny 0 (.inj₁ .unit))

/-- Around the allocation of `κ`'s cell, after the catch of `yield v` in `K`. -/
def dgKA (ny nt : UInt32) (v : Val) (K : Kont) : Kont :=
  .appR (tickingClE nt) (.pairR v (.appR (.lam (kappaCBody true (dgH ny nt) K)) .hole))

/-- Around the clause's `tick`, `κ` at the cell `ℓ`. -/
def dgKT (ny nt : UInt32) (ℓ : Loc) (K : Kont) : Kont :=
  bindK (resumeE (kappaC true ℓ (dgH ny nt) K) .unit)

/-- Around the release of `κ`'s cell. -/
def dgKF (ny nt : UInt32) (K : Kont) : Kont :=
  Kont.appL (Kont.seq .hole (kResV (dgH ny nt) K)) Val.unit

/-- At `yield`'s tags `deepGen` is its handler around the first yield. -/
theorem deepGenE_aff (ny nt : UInt32) : deepGenE ny nt (qualsVal [.aff]).1 =
    hndE (dgH ny nt) ((bindK (dgN1 ny)).plug
      (performE (.val (opPayload ny 0 ⟨.inj₂ .unit, .inj₂ .unit⟩)))) := by
  rfl

/-- The catch of `yield v` in `K` by `deepGen`'s handler: the clause applied to `v` and `κ`, whose
cell is still to be allocated. -/
theorem quiet_dgHop (ny nt : UInt32) (K : Kont) (v : Val) (hK : K.HasHnd ny = false) :
    Quiet (ℍ := ℍ) (hndE (dgH ny nt) (K.plug (performE (.val (opPayload ny 0 v)))))
      ((dgKA ny nt v K).plug (allocE Val.unit)) := by
  have hk : kappaAt (capTag (qualsVal [.aff]).1 (0 : UInt32).toNat) (dgH ny nt) K =
      kappaCell true (dgH ny nt) K := by
    simp [capTag, qualsVal, Qual.tag, kappaAt, Val.pair, Val.i32]
  have hh : ∀ μ, Head (ℍ := ℍ) μ (hndE (dgH ny nt) (K.plug (performE (.val (opPayload ny 0 v))))) μ
      (.app (.val ⟨tickingClE nt, .lam⟩) (.pair (.val v) (kappaCell true (dgH ny nt) K))) := by
    intro μ
    have h := Head.hop (ℍ := ℍ) μ ny 0 (qualsVal [.aff]) ⟨.lam .unit, .lam⟩
      ⟨clausesE [tickingClE nt], .pair .lam .unit⟩ ⟨tickingClE nt, .lam⟩ v K
      (clauseAt_clausesE [tickingClE nt] 0 .lam rfl) hK
    simp only [dgH] at hk ⊢
    rwa [hk] at h
  exact Quiet.head (ℍ := ℍ) .hole hh rfl rfl

theorem dg_seg1 (ny nt : UInt32) (ℓ : Loc) :
    lookEnd 3 ((dgKA ny nt ⟨.inj₂ .unit, .inj₂ .unit⟩ (bindK (dgN1 ny))).plug (.val (Val.loc ℓ))) =
      (dgKT ny nt ℓ (bindK (dgN1 ny))).plug (performE (.val (opPayload nt 0 Val.unit))) := by
  rfl

theorem dg_seg2 (ny nt : UInt32) (ℓ : Loc) :
    lookEnd 10 ((dgKT ny nt ℓ (bindK (dgN1 ny))).plug .unit) =
      (dgKF ny nt (bindK (dgN1 ny))).plug (freeE (.val (Val.loc ℓ))) := by
  rfl

theorem dg_seg3 (ny nt : UInt32) :
    lookEnd 3 ((dgKF ny nt (bindK (dgN1 ny))).plug .unit) =
      hndE (dgH ny nt) (Kont.hole.plug
        (performE (.val (opPayload ny 0 ⟨.inj₁ .unit, .inj₁ .unit⟩)))) := by
  rfl

theorem dg_seg4 (ny nt : UInt32) (ℓ : Loc) :
    lookEnd 3 ((dgKA ny nt ⟨.inj₁ .unit, .inj₁ .unit⟩ .hole).plug (.val (Val.loc ℓ))) =
      (dgKT ny nt ℓ .hole).plug (performE (.val (opPayload nt 0 Val.unit))) := by
  rfl

theorem dg_seg5 (ny nt : UInt32) (ℓ : Loc) :
    lookEnd 10 ((dgKT ny nt ℓ .hole).plug .unit) =
      (dgKF ny nt .hole).plug (freeE (.val (Val.loc ℓ))) := by
  rfl

theorem dg_seg6 (ny nt : UInt32) : lookEnd 10 ((dgKF ny nt .hole).plug .unit) = .unit := by
  rfl

section Run
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **A catch by `deepGen`'s handler**: from `hnd H K[yield v]`, at every memory with finitely many
cells, the complete runs show `tick` and then the complete runs from `e'`, where the clause reaches
its `tick` (`h₁`) and the resume after it reaches the release of `κ`'s cell (`h₂`) and then `e'`
(`h₃`). -/
theorem obsFrom_dgCatch (ly lt : (orowAlg Ξ).Lab) {μ : Heap} (hf : FinDom μ) (K : Kont) (v : Val)
    (hK : K.HasHnd ly.1 = false) {e' : Expr}
    (hcl : ∀ ℓ, closedAt 0 ((dgKT ly.1 lt.1 ℓ K).plug
      (performE (.val (opPayload lt.1 (UInt32.ofNat 0) Val.unit)))) = true)
    (h₁ : ∀ ℓ, Quiet (ℍ := ℍ) ((dgKA ly.1 lt.1 v K).plug (.val (Val.loc ℓ)))
      ((dgKT ly.1 lt.1 ℓ K).plug (performE (.val (opPayload lt.1 (UInt32.ofNat 0) Val.unit)))))
    (h₂ : ∀ ℓ, Quiet (ℍ := ℍ) ((dgKT ly.1 lt.1 ℓ K).plug .unit)
      ((dgKF ly.1 lt.1 K).plug (freeE (.val (Val.loc ℓ)))))
    (h₃ : Quiet (ℍ := ℍ) ((dgKF ly.1 lt.1 K).plug .unit) e') (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom ((𝕁).Rtick lt)
        ((μ, hndE (dgH ly.1 lt.1) (K.plug (performE (.val (opPayload ly.1 0 v))))), ()) w tr ↔
      ∃ tr', tr = (𝕁).tickEv lt :: tr' ∧ (𝕁).ObsFrom ((𝕁).Rtick lt) ((μ, e'), ()) w tr' := by
  refine (obsFrom_quiet_iff _ (quiet_dgHop ly.1 lt.1 K v hK) w tr).trans ?_
  refine obsFrom_alloc_iff _ (dgKA ly.1 lt.1 v K) Val.unit (exists_fresh_of_finDom hf)
    (Q := fun w tr => ∃ tr', tr = (𝕁).tickEv lt :: tr' ∧
      (𝕁).ObsFrom ((𝕁).Rtick lt) ((μ, e'), ()) w tr')
    (fun ℓ hℓ w tr => ?_) w tr
  refine (obsFrom_quiet_iff _ (h₁ ℓ) w tr).trans ?_
  refine (obsFrom_io_iff ((𝕁).Rtick lt) (s := ()) (s' := ()) (by norm_num) (hcl ℓ) rfl ⟨rfl, rfl⟩
    (if_pos ⟨rfl, rfl⟩) w tr).trans ?_
  refine exists_congr fun tr' => and_congr Iff.rfl ?_
  refine (obsFrom_quiet_iff _ (h₂ ℓ) w tr').trans ?_
  refine (obsFrom_mstep_iff _ (Head.free _ ℓ Val.unit (Heap.upd_same _ _ _)) rfl
    (by rw [labelOf_tau_of rfl]; rfl) w tr').trans ?_
  rw [del_upd_fresh hℓ]
  exact obsFrom_quiet_iff _ h₃ w tr'

/-- **`deepGen`'s complete runs**, from every memory with finitely many cells: each answers `()`
and shows two ticks, one per catch, the second after the resume has reinstalled the handler. -/
theorem obsFrom_deepGen (ly lt : (orowAlg Ξ).Lab) {μ : Heap} (hf : FinDom μ) (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom ((𝕁).Rtick lt) ((μ, deepGenE ly.1 lt.1 (qualsVal [.aff]).1), ()) w tr ↔
      w.1 = Val.unit.1 ∧ tr = [(𝕁).tickEv lt, (𝕁).tickEv lt] := by
  have q₁ : ∀ ℓ, Quiet (ℍ := ℍ) ((dgKA ly.1 lt.1 ⟨.inj₂ .unit, .inj₂ .unit⟩
      (bindK (dgN1 ly.1))).plug (.val (Val.loc ℓ))) ((dgKT ly.1 lt.1 ℓ (bindK (dgN1 ly.1))).plug
        (performE (.val (opPayload lt.1 (UInt32.ofNat 0) Val.unit)))) := fun ℓ => by
    have h := quiet_of_look (ℍ := ℍ) 3
      ((dgKA ly.1 lt.1 ⟨.inj₂ .unit, .inj₂ .unit⟩ (bindK (dgN1 ly.1))).plug (.val (Val.loc ℓ))) rfl
    rwa [dg_seg1] at h
  have q₂ : ∀ ℓ, Quiet (ℍ := ℍ) ((dgKT ly.1 lt.1 ℓ (bindK (dgN1 ly.1))).plug .unit)
      ((dgKF ly.1 lt.1 (bindK (dgN1 ly.1))).plug (freeE (.val (Val.loc ℓ)))) := fun ℓ => by
    have h := quiet_of_look (ℍ := ℍ) 10 ((dgKT ly.1 lt.1 ℓ (bindK (dgN1 ly.1))).plug .unit) rfl
    rwa [dg_seg2] at h
  have q₃ := quiet_of_look (ℍ := ℍ) 3 ((dgKF ly.1 lt.1 (bindK (dgN1 ly.1))).plug .unit) rfl
  rw [dg_seg3] at q₃
  have q₄ : ∀ ℓ, Quiet (ℍ := ℍ) ((dgKA ly.1 lt.1 ⟨.inj₁ .unit, .inj₁ .unit⟩ .hole).plug
      (.val (Val.loc ℓ))) ((dgKT ly.1 lt.1 ℓ .hole).plug
        (performE (.val (opPayload lt.1 (UInt32.ofNat 0) Val.unit)))) := fun ℓ => by
    have h := quiet_of_look (ℍ := ℍ) 3
      ((dgKA ly.1 lt.1 ⟨.inj₁ .unit, .inj₁ .unit⟩ .hole).plug (.val (Val.loc ℓ))) rfl
    rwa [dg_seg4] at h
  have q₅ : ∀ ℓ, Quiet (ℍ := ℍ) ((dgKT ly.1 lt.1 ℓ .hole).plug .unit)
      ((dgKF ly.1 lt.1 .hole).plug (freeE (.val (Val.loc ℓ)))) := fun ℓ => by
    have h := quiet_of_look (ℍ := ℍ) 10 ((dgKT ly.1 lt.1 ℓ .hole).plug .unit) rfl
    rwa [dg_seg5] at h
  have q₆ := quiet_of_look (ℍ := ℍ) 10 ((dgKF ly.1 lt.1 .hole).plug .unit) rfl
  rw [dg_seg6] at q₆
  have c₂ := obsFrom_dgCatch ly lt hf .hole ⟨.inj₁ .unit, .inj₁ .unit⟩ rfl (fun _ => rfl) q₄ q₅ q₆
  rw [deepGenE_aff]
  refine (obsFrom_dgCatch ly lt hf (bindK (dgN1 ly.1)) ⟨.inj₂ .unit, .inj₂ .unit⟩ rfl
    (fun _ => rfl) q₁ q₂ q₃ w tr).trans ⟨?_, ?_⟩
  · rintro ⟨tr', rfl, h⟩
    obtain ⟨tr'', rfl, h'⟩ := (c₂ w tr').1 h
    obtain ⟨hw, rfl⟩ := (obsFrom_val_iff _ Val.unit w tr'').1 h'
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨_, rfl, (c₂ w _).2 ⟨[], rfl, (obsFrom_val_iff _ Val.unit w []).2 ⟨hw, rfl⟩⟩⟩

/-- **`deepGen`'s run**: it answers `()`, showing two ticks. -/
theorem runsTo_deepGen {ly lt : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)]) :
    (𝕁).RunsTo ((𝕁).Rtick lt) ((𝕁).deepGen ly lt) (𝕁).unitV [(𝕁).tickEv lt, (𝕁).tickEv lt] := by
  rw [deepGen_val, qsOf_eq hly]
  exact runsTo_of_obsFrom _ (v := Val.unit) fun w tr => obsFrom_deepGen ly lt finDom_empty w tr

/-- **S4's deep resume at a cell is not vacuous at `J₁`**: `deepGen`'s run reaches, after its first
catch, the cell's allocation and the runner's answer to the clause's `tick`, the clause's resume of
`κ` at its cell, the memory holding the cell — a configuration at which every premise of
`ResumeCellLaw` holds. -/
theorem resumeCell_deepGen {ly lt : (orowAlg Ξ).Lab} (hly : Ξ ly.1 = [(.aff, boolT, .unit)])
    (hlt : Ξ lt.1 = [(.lin, .unit, .unit)]) (hne : ly.1 ≠ lt.1) :
    ∃ (c : Heap × Expr) (ℓ : Loc) (K₀ : Kont) (H : OVal × List OVal) (K : Kont) (w : OVal),
      (𝕁).cellFree c ℓ ∧ (𝕁).Live ((𝕁).withCell c ℓ) ∧
      (𝕁).term ((𝕁).withCell c ℓ) =
        (𝕁).plug K₀ ((𝕁).resume ((𝕁).captureAt .affine ly H K ℓ) w) := by
  have hℓ : (Adequacy.emptyMem : Heap) 0 = none := rfl
  have hqs : qsOf Ξ ly.1 = (qualsVal [.aff]).1 := qsOf_eq hly
  have hreach : (𝕁).RReach ((𝕁).Rtick lt) ((𝕁).rinit ((𝕁).Rtick lt) ((𝕁).deepGen ly lt))
      ((Adequacy.emptyMem.upd 0 Val.unit,
        resumeE (kappaC true 0 (dgH ly.1 lt.1) (bindK (dgN1 ly.1))) .unit), ()) := by
    -- the catch of the first yield
    obtain ⟨q₀, hc₀, -⟩ := quiet_dgHop (ℍ := ℍ) ly.1 lt.1 (bindK (dgN1 ly.1))
      ⟨.inj₂ .unit, .inj₂ .unit⟩ rfl
    have h₀ := rreach_of_chain (J := J₁) (Ξ := Ξ) ((𝕁).Rtick lt) (μ := Adequacy.emptyMem) (s := ())
      hc₀
    -- the allocation of `κ`'s cell
    have hal : (𝕁).RStep ((𝕁).Rtick lt)
        ((Adequacy.emptyMem, (dgKA ly.1 lt.1 ⟨.inj₂ .unit, .inj₂ .unit⟩ (bindK (dgN1 ly.1))).plug
          (allocE Val.unit)), ())
        (labelOf orowRF Ξ (allocE Val.unit))
        ((Adequacy.emptyMem.upd 0 Val.unit, (dgKA ly.1 lt.1 ⟨.inj₂ .unit, .inj₂ .unit⟩
          (bindK (dgN1 ly.1))).plug (.val (Val.loc 0))), ()) :=
      .mach (OStep.mach (Head.alloc _ Val.unit 0 hℓ))
    -- to the clause's `tick`
    have hq₁ := quiet_of_look (ℍ := ℍ) 3 ((dgKA ly.1 lt.1 ⟨.inj₂ .unit, .inj₂ .unit⟩
      (bindK (dgN1 ly.1))).plug (.val (Val.loc 0))) rfl
    rw [dg_seg1] at hq₁
    obtain ⟨q₁, hc₁, -⟩ := hq₁
    have h₁ := rreach_of_chain (J := J₁) (Ξ := Ξ) ((𝕁).Rtick lt)
      (μ := Adequacy.emptyMem.upd 0 Val.unit) (s := ()) hc₁
    -- the runner answers the `tick`
    have hpe : (𝕁).perform lt 0 (𝕁).unitV =
        performE (.val (opPayload lt.1 (UInt32.ofNat 0) Val.unit)) :=
      (perform_eq (ℍ := ℍ) (RF := orowRF) (Ξ := Ξ) (J := J₁) (l := lt) (𝕁).unitV
        (by norm_num)).trans rfl
    have hio : (𝕁).RStep ((𝕁).Rtick lt) ((Adequacy.emptyMem.upd 0 Val.unit,
        (dgKT ly.1 lt.1 0 (bindK (dgN1 ly.1))).plug
          (performE (.val (opPayload lt.1 (UInt32.ofNat 0) Val.unit)))), ())
        ((𝕁).tickEv lt)
        ((Adequacy.emptyMem.upd 0 Val.unit, (dgKT ly.1 lt.1 0 (bindK (dgN1 ly.1))).plug .unit), ()) := by
      have := A.EffectSystem.RStep.io (S := 𝕁) (R := (𝕁).Rtick lt)
        (c := (Adequacy.emptyMem.upd 0 Val.unit,
          (dgKT ly.1 lt.1 0 (bindK (dgN1 ly.1))).plug ((𝕁).perform lt 0 (𝕁).unitV)))
        (s := ()) (s' := ()) (K := dgKT ly.1 lt.1 0 (bindK (dgN1 ly.1))) (l := lt) (i := 0)
        (v := (𝕁).unitV) (w := (𝕁).unitV) rfl rfl ⟨rfl, rfl⟩ (if_pos ⟨rfl, rfl⟩)
      rw [hpe] at this
      exact this
    -- the β-step to the resume
    have h₂ := rreach_of_chain (J := J₁) (Ξ := Ξ) ((𝕁).Rtick lt)
      (μ := Adequacy.emptyMem.upd 0 Val.unit) (s := ())
      (lookRun_sound (ℍ := ℍ) 1 ((dgKT ly.1 lt.1 0 (bindK (dgN1 ly.1))).plug .unit))
    have e : lookEnd 1 ((dgKT ly.1 lt.1 0 (bindK (dgN1 ly.1))).plug .unit) =
        resumeE (kappaC true 0 (dgH ly.1 lt.1) (bindK (dgN1 ly.1))) .unit := rfl
    rw [e] at h₂
    show (𝕁).RReach ((𝕁).Rtick lt) ((Adequacy.emptyMem, deepGenE ly.1 lt.1 (qsOf Ξ ly.1)), ()) _
    rw [hqs, deepGenE_aff]
    exact ((((h₀.tail ⟨_, hal⟩).trans h₁).tail ⟨_, hio⟩).trans h₂)
  refine ⟨(Adequacy.emptyMem,
      resumeE (kappaC true 0 (dgH ly.1 lt.1) (bindK (dgN1 ly.1))) .unit), 0, .hole,
    (⟨.lam .unit, .lam⟩, [⟨tickingClE lt.1, .lam⟩]), bindK (dgN1 ly.1), (𝕁).unitV, hℓ,
    ⟨(𝕁).deepGen ly lt, _, (𝕁).Rtick lt, (), A.EffectSystem.rtick_respects ((sig_tick_iff lt).mpr hlt),
      der_deepGen_J₁ hly hlt hne, hreach⟩, ?_⟩
  show _ = resumeE (captureAtE (decide (A.OpClass.affine = .affine)) 0 ly.1 (qsOf Ξ ly.1)
    (.lam .unit) [tickingClE lt.1] (bindK (dgN1 ly.1))) .unit
  rw [hqs]
  unfold captureAtE
  rw [dif_pos (show IsVal (hndValE ly.1 (qualsVal [.aff]).1 (.lam .unit) [tickingClE lt.1]) from
    (dgH ly.1 lt.1).2)]
  rfl

end Run

/-! ### E4 -/

section E4
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **E4's labels**: a `yield` and a `tick` label, at a rich context. -/
theorem labelsAt_E4 (hΞ : AdmEff Ξ) : ∃ ls, (𝕁).LabelsAt [(𝕁).sigYield, (𝕁).sigTick] ls := by
  obtain ⟨ly, -, -, hly, -⟩ := rich_labs hΞ.2.2 (E := [(.aff, boolT, .unit)]) (by simp [eSigs])
  obtain ⟨lt, -, -, hlt, -⟩ := rich_labs hΞ.2.2 (E := [(.lin, .unit, .unit)]) (by simp [eSigs])
  refine ⟨[ly, lt], rfl, ?_, fun k h₁ _ => ?_⟩
  · have hne : ly ≠ lt := lab_ne_of_sig (by rw [hly, hlt]; simp)
    exact List.nodup_cons.mpr ⟨fun h => hne (List.mem_singleton.mp h), List.nodup_singleton _⟩
  · match k, h₁ with
    | 0, _ => exact (sig_yield_iff hΞ.1 ly).mpr hly
    | 1, _ => exact (sig_tick_iff lt).mpr hlt

/-- **E4, deep handlers, at `J₁`**, at every admissible effect context. -/
theorem deepHandler_J₁ (hΞ : AdmEff Ξ) : (𝕁).DeepHandler := by
  refine ⟨labelsAt_E4 hΞ, fun ls hls ly lt hlsEq => ?_⟩
  subst hlsEq
  have hly := (sig_yield_iff hΞ.1 ly).mp (hls.2.2 0 (by simp) (by simp))
  have hlt := (sig_tick_iff lt).mp (hls.2.2 1 (by simp) (by simp))
  have hne : ly.1 ≠ lt.1 := fun h => by
    rw [h, hlt] at hly
    simp at hly
  exact ⟨der_deepGen_J₁ hly hlt hne, runsTo_deepGen hly⟩

end E4

end Targets.Inst

end
