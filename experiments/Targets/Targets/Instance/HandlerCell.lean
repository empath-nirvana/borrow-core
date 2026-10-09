import Core.EffExamples
import Targets.Instance.CellRuns

/-!
# The Instance — S4 at the capture cell

At a linear or affine operation the catch hands the clause `κ` with a fresh cell (SPEC §25): the
`[op]` step, which keeps the store, reaches the clause applied to `κ` before its cell; the next step
allocates `()` at a location the memory does not hold; and `κ`'s β-step makes it `kappaC` at that
location.  Resuming `κ` releases the cell three steps later, and so does an affine `κ`'s cancel.

* **S4 at every effect context** (`handlerSem_ourInst`; `handlerSem_orow` at the open-row form), at
  a typing system whose reached configurations are closed and go on (`LiveOK`).  The catch law
  (`catchLaw_ourInst`): at an unrestricted operation the catch hands `kappa` and keeps the store
  (`catch_unr_ourInst`); at a linear or affine one it allocates `κ`'s cell at a free location (a
  reached configuration's memory is finite, `finDom_reach`) and hands `kappaC` there, across that one
  allocation (`catch_cell_ourInst`).  Deep resume and an affine cancel at a cell release the cell,
  across that one release, and run on as `kappa`'s do (`resumeCellLaw_ourInst`,
  `cancelCellLaw_ourInst`, from `kappaC_resume_parts` and `kappaC_cancel_parts`).  The laws that read
  no cell are `Targets/Instance/Machine.lean`'s.
* **S4 with no cell** (`HandlerSemNoCell`: every catch hands `capture l H K` and keeps the store)
  **fails at `J₁`, at the admissible context `ΞA`** (`not_handlerSemNoCell_J₁_ΞA`).  The witness is
  `progT`: Core's handled program of `Core/EffExamples.lean` at the name `5`, where `ΞA` declares
  `tick : 1 ↠ 1` linear; Core's kernel types it at `F 1`, its handler's and operation's row tied to
  `ΞA` (`progT_derivesAt`).  Its run reaches the catch; from there the store-keeping steps reach only
  the catch and the clause applied to `κ` before its cell, each of which names `perform` or `alloc`,
  while the clause applied to `capture l H K` runs, keeping the store, through terms that name
  neither, to `()` (`not_pureJoin_progT`).  It holds where every resuming operation is unrestricted
  (`handlerSemNoCell_orow`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE hndVal kappa clauseAt
  capTag kappaAt kappaCell kappaC kappaCBody freeE)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg HeadChain lookRun lookEnd lookRun_sound)

/-! ### Store-keeping runs along a chain -/

section Chain
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- **The store-keeping runs from the start of a chain to a value stay on the chain**: each step of
the chain is its configuration's only step (`det_ourInst`), and a value takes none. -/
theorem pureSteps_chain {μ : Heap} : ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)},
    HeadChain (ℍ := ℍ) e q e' → IsVal e' → ∀ d, (𝕊).PureSteps (μ, e) d →
      d.1 = μ ∧ d.2 ∈ chainTerms e q
  | _, _, _, .nil, hv, d, h => by
      rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₁, ⟨ev, hst, -⟩, -⟩
      · exact ⟨rfl, List.mem_cons_self⟩
      · exact absurd ((isVal_val μ ⟨_, hv⟩).2 _ _ hst) (fun h => h)
  | _, _, _, @HeadChain.cons _ _ K a a' e' q hh hn hq, hv, d, h => by
      rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c₁, ⟨ev, hst, -⟩, hrest⟩
      · exact ⟨rfl, List.mem_cons_self⟩
      · obtain ⟨-, rfl⟩ := det_ourInst (hh μ) hn hst
        obtain ⟨h₁, h₂⟩ := pureSteps_chain hq hv d hrest
        refine ⟨h₁, ?_⟩
        simp only [chainTerms, List.map_cons, List.mem_cons] at h₂ ⊢
        rcases h₂ with h₂ | h₂
        · exact .inr (.inl h₂)
        · exact .inr (.inr h₂)

/-- A configuration at the allocation of `()` takes no step that keeps the store. -/
theorem no_pureStep_alloc {μ : Heap} (K : Kont) {ev : (𝕊).Event} {c' : (𝕊).Conf} :
    ¬ (𝕊).PureStep (μ, K.plug (allocE Val.unit)) ev c' := by
  rintro ⟨hst, hc'⟩
  have hal : Head (ℍ := ℍ) Adequacy.emptyMem (allocE Val.unit) (Adequacy.emptyMem.upd 0 Val.unit)
      (.val (Val.loc 0)) := Head.alloc _ Val.unit 0 rfl
  have hs1 : Step1 (ℍ := ℍ) Adequacy.emptyMem (K.plug (allocE Val.unit))
      (Adequacy.emptyMem.upd 0 Val.unit) (K.plug (.val (Val.loc 0))) := ⟨K, _, _, rfl, rfl, hal⟩
  change OStep (ℍ := ℍ) RF Ξ (μ, K.plug (allocE Val.unit)) ev c' at hst
  change c' = (μ, c'.2) at hc'
  generalize hc : (μ, K.plug (allocE Val.unit)) = c₀ at hst
  cases hst with
  | mach hh =>
      have h1 := (Prod.mk.inj hc).1
      have h2 := (Prod.mk.inj hc).2
      subst h1
      obtain ⟨rfl, rfl⟩ := plug_decomp hh K _ hal h2
      obtain ⟨ℓ, hℓ, rfl, rfl⟩ := Targets.head_alloc_inv hh
      have := congrArg (fun c : Heap × Expr => c.1 ℓ) hc'
      simp [hℓ] at this
  | again =>
      rw [(Prod.mk.inj hc).2] at hs1
      exact (no_step1_drive _ hs1).elim
  | fin =>
      rw [(Prod.mk.inj hc).2] at hs1
      exact (no_step1_drive _ hs1).elim

end Chain

/-! ### S4 at the capture cell -/

section Cell
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- A quiet run is a run of store-keeping steps, in every context and at every memory. -/
theorem pureSteps_of_quiet {μ : Heap} (K₀ : Kont) {e e' : Expr} (h : Quiet (ℍ := ℍ) e e') :
    (𝕊).PureSteps (μ, K₀.plug e) (μ, K₀.plug e') := by
  obtain ⟨q, hc, -⟩ := h
  exact pureSteps_of_chain (hc.plug K₀)

theorem captureAtE_of_val {aff : Bool} {ℓ : Loc} {n : UInt32} {qs r : Expr} {cs : List Expr}
    (K : Kont) (h : IsVal (hndValE n qs r cs)) :
    captureAtE aff ℓ n qs r cs K = kappaC aff ℓ ⟨_, h⟩ K := by
  unfold captureAtE; rw [dif_pos h]

theorem captureAtE_of_not_val {aff : Bool} {ℓ : Loc} {n : UInt32} {qs r : Expr} {cs : List Expr}
    (K : Kont) (h : ¬ IsVal (hndValE n qs r cs)) : captureAtE aff ℓ n qs r cs K = .unit := by
  unfold captureAtE; rw [dif_neg h]

/-- The memory of a configuration a typed program reaches leaves some location free. -/
theorem exists_fresh_of_live {c : Heap × Expr} (h : (𝕊).Live c) : ∃ ℓ, c.1 ℓ = none := by
  obtain ⟨P, C, R, s, -, -, hreach⟩ := h
  exact exists_fresh_of_finDom (finDom_reach hreach)

/-- **A catch whose operation is linear or affine allocates `κ`'s cell** (SPEC §25): the `[op]` step,
which keeps the store, hands the clause `κ` before its cell; then the allocation of `()` at a free
location `ℓ`; then `κ`'s β-step at `ℓ`.  At the store with `ℓ`, the clause applied to the argument
and `κ` at `ℓ` reaches the same term by `M V`'s β-step. -/
theorem catch_cell_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J)
    (hlen : ∀ l, (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) {c : Heap × Expr} {K₀ : Kont}
    {l : (RF.alg Ξ).Lab} {r : OVal} {cs : List OVal} {K : Kont} {i : ℕ} {v : OVal}
    {o : A.OpSig OVTy} {cl : OVal} {q : Qual} (hlive : (𝕊).Live c)
    (he : (𝕊).term c = (𝕊).plug K₀ ((𝕊).handle l ((𝕊).hnd r cs) ((𝕊).plug K ((𝕊).perform l i v))))
    (hK : (𝕊).catches K l = false) (hsig : ((𝕊).sig l)[i]? = some o) (hcl : cs[i]? = some cl)
    (hq : q ≠ .unr) (htag : capTag (qsOf Ξ (RF.name Ξ l)) i = q.tag)
    (haff : decide (o.cls = .affine) = cellAff q) :
    ∃ ℓ, (𝕊).cellFree c ℓ ∧ (𝕊).JoinAcross c ((𝕊).withCell c ℓ)
      ((𝕊).plug K₀ ((𝕊).app ((𝕊).force cl)
        ((𝕊).pair v ((𝕊).captureAt o.cls l ((𝕊).hnd r cs) K ℓ)))) := by
  obtain ⟨ℓ, hℓ⟩ := exists_fresh_of_live hlive
  obtain ⟨μ, e⟩ := c
  change μ ℓ = none at hℓ
  rw [perform_eq (ℍ := ℍ) (l := l) v (idx_lt (J := J) (hlen l) hsig)] at he
  change e = K₀.plug ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
    (K.plug (performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)))) at he
  subst he
  change K.HasHnd (RF.name Ξ l) = false at hK
  obtain ⟨hr, hcs⟩ := hndVal_of_live hL hlive rfl
  have hv : IsVal v.1 := val_of_live hL hlive v.2
    (K := ((K₀.comp (handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1
      (cs.map Subtype.val))).comp K).comp
      (.appR (.prim .perform) (.pairR (Val.i32 (RF.name Ξ l)) (.pairR (Val.i32 (UInt32.ofNat i))
        .hole))))
    (by simp only [Kont.plug_comp]; rfl)
  have hcl' : (cs.map Subtype.val)[i]? = some cl.1 := by
    rw [List.getElem?_map]; exact congrArg (Option.map Subtype.val) hcl
  have hclv : IsVal cl.1 := isVal_of_mem_clausesE hcs _ (List.mem_of_getElem? hcl')
  have hi := idx_lt (J := J) (hlen l) hsig
  have hca : clauseAt (clausesE (cs.map Subtype.val)) (UInt32.ofNat i).toNat =
      some ⟨cl.1, hclv⟩ := by
    rw [UInt32.toNat_ofNat_of_lt' hi]
    exact clauseAt_clausesE _ i hclv hcl'
  have hqv : IsVal (qsOf Ξ (RF.name Ξ l)) := (qualsVal _).2
  have hH : IsVal (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)) :=
    .pair .prim (.pair hqv (.pair hr hcs))
  have hkc : kappaAt (capTag (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)).1 (UInt32.ofNat i).toNat)
      (hndVal (RF.name Ξ l) (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) ⟨r.1, hr⟩
        ⟨_, hcs⟩) K = kappaCell (cellAff q) ⟨_, hH⟩ K := by
    change kappaAt (capTag (qsOf Ξ (RF.name Ξ l)) (UInt32.ofNat i).toNat) _ K = _
    rw [UInt32.toNat_ofNat_of_lt' hi, htag]
    exact kappaAt_cell hq _ K
  have hhop := Head.hop (ℍ := ℍ) μ (RF.name Ξ l) (UInt32.ofNat i)
    (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) ⟨r.1, hr⟩ ⟨_, hcs⟩ ⟨cl.1, hclv⟩ ⟨v.1, hv⟩ K hca hK
  rw [hkc] at hhop
  have hb := Head.beta (ℍ := ℍ) (μ.upd ℓ Val.unit)
    (kappaCBody (cellAff q) ⟨_, hH⟩ K) (Val.loc ℓ)
  rw [kappaCBody_subst] at hb
  have hstep := OStep.mach (ℍ := ℍ) (RF := RF) (Ξ := Ξ)
    (K := K₀.comp (.appR (.val ⟨cl.1, hclv⟩) (.pairR ⟨v.1, hv⟩
      (.appR (.val (Val.lam (kappaCBody (cellAff q) ⟨_, hH⟩ K))) .hole))))
    (Head.alloc μ Val.unit ℓ hℓ)
  refine ⟨ℓ, hℓ, _, _, _, (μ.upd ℓ Val.unit, K₀.plug (.app (.val ⟨cl.1, hclv⟩)
    (.pair (.val ⟨v.1, hv⟩) (kappaC (cellAff q) ℓ ⟨_, hH⟩ K)))), ?_, hstep, ?_, ?_⟩
  · -- the `[op]` step
    rw [Kont.plug_comp]
    exact pureSteps_head K₀ .hole hhop
  · -- `κ`'s β-step at its cell
    show (𝕊).PureSteps (μ.upd ℓ Val.unit, (K₀.comp (.appR (.val ⟨cl.1, hclv⟩) (.pairR ⟨v.1, hv⟩
      (.appR (.val (Val.lam (kappaCBody (cellAff q) ⟨_, hH⟩ K))) .hole)))).plug
        (.val (Val.loc ℓ))) _
    have h := pureSteps_head (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J)
      (K₀.comp (.appR (.val ⟨cl.1, hclv⟩) (.pairR ⟨v.1, hv⟩ .hole))) .hole hb
    simp only [Kont.plug_comp] at h ⊢
    exact h
  · -- the clause applied to the argument and `κ` at its cell
    show (𝕊).PureSteps (μ.upd ℓ Val.unit, K₀.plug (appE cl.1 (.pair v.1
      (captureAtE (decide (o.cls = .affine)) ℓ (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1
        (cs.map Subtype.val) K)))) _
    rw [captureAtE_of_val K hH, haff]
    exact appE_steps K₀ cl.1 ⟨.pair v.1 (kappaC (cellAff q) ℓ ⟨_, hH⟩ K),
      .pair hv (isVal_kappaC _ _ _ _)⟩

/-- **S4's catch law** at a configuration a typed program reaches, at a row form whose labels'
signatures are indexable by `UInt32`, at every effect context: at an unrestricted operation the
catch hands `kappa` and keeps the store; at a linear or affine one it allocates `κ`'s cell. -/
theorem catchLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J)
    (hlen : ∀ l, (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) : (𝕊).CatchLaw := by
  intro c K₀ l r cs K i v o cl hlive he hK hsig hres hcl
  obtain ⟨p, hp, hpo⟩ := sig_entry (J := J) hsig
  have hplt : i < (Ξ (RF.name Ξ l)).length := (List.getElem?_eq_some_iff.1 hp).1
  have hpe : (Ξ (RF.name Ξ l))[i] = p := (List.getElem?_eq_some_iff.1 hp).2
  have htag : capTag (qsOf Ξ (RF.name Ξ l)) i = p.1.tag := by
    unfold qsOf
    rw [capTag_qualsVal _ i (by simpa using hplt)]
    simp [hpe]
  have hres' := resuming_of_cls (hpo ▸ hres)
  rcases hq : p.1 with _ | _ | _
  · exact .inr (catch_cell_ourInst hL hlen hlive he hK hsig hcl (q := .lin) (by simp)
      (by rw [htag, hq]) (by rw [hpo, hq]; simp [clsOf, cellAff]))
  · rw [hq] at hres'
    have hz : p.2.2.isZero = false := by simpa using hres'
    exact .inr (catch_cell_ourInst hL hlen hlive he hK hsig hcl (q := .aff) (by simp)
      (by rw [htag, hq]) (by rw [hpo, hq]; simp [clsOf, cellAff, hz]))
  · exact .inl (catch_unr_ourInst hL hlen hlive he hK hsig hcl (by rw [htag, hq]; rfl))

/-- **S4's deep resume at a cell**: resuming `kappaC` at `ℓ`, in a memory that holds `ℓ`, reaches the
release of `ℓ` by store-keeping steps, releases it, and reaches the reinstalled handler by
store-keeping steps. -/
theorem resumeCellLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (𝕊).ResumeCellLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) k l (H : OVal × List OVal) (K : Kont) (ℓ : Loc) (w : OVal) hfree hlive
    he
  change μ ℓ = none at hfree
  change e = K₀.plug (resumeE (captureAtE (decide (k = .affine)) ℓ (RF.name Ξ l)
    (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K) w.1) at he
  subst he
  have hw : IsVal w.1 := val_of_live hL hlive w.2
    (K := K₀.comp (.appR (.lam (.app (.app ((captureAtE (decide (k = .affine)) ℓ (RF.name Ξ l)
      (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K).shift 1 0) (.inj₁ .unit)) (.var 0)))
      .hole))
    (by rw [Kont.plug_comp]; rfl)
  have hst := resumeE_steps (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (μ := μ.upd ℓ Val.unit) K₀
    (captureAtE (decide (k = .affine)) ℓ (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
      (H.2.map Subtype.val) K) ⟨w.1, hw⟩
  by_cases hH : IsVal (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val))
  · rw [captureAtE_of_val K hH] at hst
    obtain ⟨hq₁, hq₂⟩ := kappaC_resume_parts (ℍ := ℍ) (decide (k = .affine)) ℓ ⟨_, hH⟩ K
      ⟨w.1, hw⟩
    have hfr : Head (ℍ := ℍ) (μ.upd ℓ Val.unit) (freeE (.val (Val.loc ℓ))) μ (.val Val.unit) := by
      have h := Head.free (ℍ := ℍ) (μ.upd ℓ Val.unit) ℓ Val.unit (Heap.upd_same _ _ _)
      rwa [del_upd_fresh hfree] at h
    have hstep := OStep.mach (ℍ := ℍ) (RF := RF) (Ξ := Ξ)
      (K := K₀.comp (Kont.appL (Kont.seq .hole (kResV ⟨_, hH⟩ K)) ⟨w.1, hw⟩)) hfr
    rw [Kont.plug_comp, Kont.plug_comp] at hstep
    refine ⟨_, _, _, _, ?_, hstep, pureSteps_of_quiet K₀ hq₂, ?_⟩
    · show (𝕊).PureSteps (μ.upd ℓ Val.unit, K₀.plug (resumeE (captureAtE (decide (k = .affine)) ℓ
        (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K) w.1)) _
      rw [captureAtE_of_val K hH]
      exact hst.trans (pureSteps_of_quiet K₀ hq₁)
    · exact Relation.ReflTransGen.refl
  · exfalso
    have hl' := live_of_pureSteps hlive hst
    rw [captureAtE_of_not_val K hH] at hl'
    refine not_goesOn_stuck (RF := RF) (Ξ := Ξ) (stuckAt_unit_app (Val.inj₁ Val.unit))
      (K₀.comp (.appL .hole ⟨w.1, hw⟩)) (μ.upd ℓ Val.unit)
      (fun _ => plug_unit_app_ne_drive _ _ _) ?_
    rw [Kont.plug_comp]
    exact (hL _ hl').2

/-- **S4's cancel at a cell**: cancelling an affine `kappaC` at `ℓ`, in a memory that holds `ℓ`,
reaches the release of `ℓ` by store-keeping steps, releases it, and reaches `κ`'s cancel run by
store-keeping steps. -/
theorem cancelCellLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (𝕊).CancelCellLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) l (H : OVal × List OVal) (K : Kont) (ℓ : Loc) hfree hlive he
  change μ ℓ = none at hfree
  change e = K₀.plug (cancelE (captureAtE true ℓ (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
    (H.2.map Subtype.val) K)) at he
  subst he
  by_cases hH : IsVal (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val))
  · obtain ⟨hq₁, hq₂⟩ := kappaC_cancel_parts (ℍ := ℍ) ℓ ⟨_, hH⟩ K
    have hfr : Head (ℍ := ℍ) (μ.upd ℓ Val.unit) (freeE (.val (Val.loc ℓ))) μ (.val Val.unit) := by
      have h := Head.free (ℍ := ℍ) (μ.upd ℓ Val.unit) ℓ Val.unit (Heap.upd_same _ _ _)
      rwa [del_upd_fresh hfree] at h
    have hstep := OStep.mach (ℍ := ℍ) (RF := RF) (Ξ := Ξ)
      (K := K₀.comp (Kont.seq .hole (kCanE K))) hfr
    rw [Kont.plug_comp, Kont.plug_comp] at hstep
    refine ⟨_, _, _, _, ?_, hstep, pureSteps_of_quiet K₀ hq₂, ?_⟩
    · show (𝕊).PureSteps (μ.upd ℓ Val.unit, K₀.plug (cancelE (captureAtE true ℓ (RF.name Ξ l)
        (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K))) _
      rw [captureAtE_of_val K hH]
      exact pureSteps_of_quiet K₀ hq₁
    · show (𝕊).PureSteps (μ, K₀.plug (cancelOfE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
        (H.2.map Subtype.val) K)) _
      rw [cancelOfE_of_val K hH]
      exact Relation.ReflTransGen.refl
  · exfalso
    have hg := (hL _ hlive).2
    change GoesOn RF Ξ (μ.upd ℓ Val.unit, K₀.plug (cancelE (captureAtE true ℓ (RF.name Ξ l)
      (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K))) at hg
    rw [captureAtE_of_not_val K hH] at hg
    exact not_goesOn_stuck (stuckAt_unit_app (Val.inj₂ Val.unit)) K₀ (μ.upd ℓ Val.unit)
      (fun _ => plug_unit_app_ne_drive _ _ _) hg

/-- **S4** at a configuration a typed program reaches, at a row form whose labels' names are not the
reserved `0` and whose signatures are indexable by `UInt32`, at every effect context: the laws that
read no cell (`Targets/Instance/Machine.lean`), the catch law, and deep resume and cancel at a
cell. -/
theorem handlerSem_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hlen : ∀ l, (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) : (𝕊).HandlerSem :=
  ⟨retLaw_ourInst hL, catchLaw_ourInst hL hlen, abortLaw_ourInst hL hnz hlen,
    resumeLaw_ourInst hL, resumeCellLaw_ourInst hL, cancelLaw_ourInst hL, cancelCellLaw_ourInst hL,
    thenLaw_ourInst hL, finLaw_ourInst hL hnz⟩

end Cell

/-- **S4** at the open-row form, at every effect context: its labels' names are not `0` and their
signatures have at most `2³²` operations. -/
theorem handlerSem_orow {Ξ : EffCtx} {J : OurTyping orowRF} (hL : LiveOK (ℍ := ℍ) orowRF Ξ J) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).HandlerSem :=
  handlerSem_ourInst hL (fun l => l.2.1) (fun l => l.2.2.2)

/-! ### The witness -/

/-- `perform` occurs. -/
def isPerform : Expr → Bool
  | .prim .perform => true
  | _ => false

/-- `alloc` occurs. -/
def isAlloc : Expr → Bool
  | .prim .alloc => true
  | _ => false

/-- Core's handled program at the name `5`: `handle_5 (perform (5, (0, ()))) with (λx. x, (cl₀, ()))`,
`cl₀` resuming `κ` once. -/
def progT : Expr :=
  bindE EffExamples.cls (bindE EffExamples.hr
    (hndTerm 5 [.lin] 0 1 (performE (opArgE 5 0 (.val .unit)))))

theorem progT_derives : CDerives LifeCtx.empty [] progT (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.tensorI .nil EffExamples.cl₀_derives (.unitI .nil))) ?_
  refine .bind (.right .nil)
    (.ret (.bangThunkV (C := .arr .unit (.ret .unit)) (fun s hs hl => by
      simp at hs; subst hs; simp at hl) rfl (.lam (.ret (.var (.here (.cons .nil))))))) ?_
  exact .effHandle (S := []) (E := EffExamples.E₁) (A := .unit) (R := .unit)
    (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
    (by decide) (by simp) (by simp)
    (.effPerform (o := ⟨5, 0, .lin, .unit, .unit, .ret .unit⟩) (by rfl) rfl (.unitI (.cons (.cons .nil))))

/-- Core's clause `cl₀` (`Core/EffExamples.lean`), in Core's kernel with its inner rows tied: it
performs nothing and handles nothing. -/
theorem cl₀_derivesAt (Ξ : EffCtx) :
    CDerivesAt Ξ LifeCtx.empty [] EffExamples.cl₀
      (.val (clauseTy [] .unit (.lin, .unit, .unit))) := by
  refine .bangThunkV (fun _ hs => by simp at hs) rfl (.lam ?_)
  refine .tensorE (.left .nil) (.var (.here .nil)) ?_
  exact .app (.left (.right (.dead .nil)))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] .unit)) .top)
      (.here (.cons (.cons .nil)))))
    (.there (.here (.cons .nil)))

/-- **`progT` at `ΞA`, its inner rows tied**: its handler's row and its operation's row are
`(5)↑[tick]`, the signature `ΞA` declares at `5`. -/
theorem progT_derivesAt : CDerivesAt ΞA LifeCtx.empty [] progT (.comp (.ret .unit)) := by
  have hAt : RowAt ΞA (Row.ofEff 5 EffExamples.E₁ 0 ++ []) :=
    rowAt_ofEff_append (by rfl) (by decide) (by simp) (rowAt_nil _)
  refine .bind .nil (.ret (.tensorI .nil (cl₀_derivesAt ΞA) (.unitI .nil))) ?_
  refine .bind (.right .nil)
    (.ret (.bangThunkV (C := .arr .unit (.ret .unit)) (fun s hs hl => by
      simp at hs; subst hs; simp at hl) rfl (.lam (.ret (.var (.here (.cons .nil))))))) ?_
  exact .effHandle (S := []) (E := EffExamples.E₁) (A := .unit) (R := .unit) hAt
    (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
    (by decide) (by simp) (by simp)
    (.effPerform (o := ⟨5, 0, .lin, .unit, .unit, .ret .unit⟩) hAt (by rfl) rfl
      (.unitI (.cons (.cons .nil))))

/-- `cl₀`, the clause, as a term. -/
def clT : Expr := .lam (.letpair (.var 0) (.app (.app (.var 0) (.inj₁ .unit)) (.var 1)))

/-- `h_ret = λx. x`, as a term. -/
def hrT : Expr := .lam (.var 0)

/-- The catch: the handler of `5` around `perform (5, (0, ()))`, after the program's bindings. -/
theorem progT_catch : lookEnd 2 progT =
    (handleK 5 (qualsVal [.lin]).1 hrT [clT]).plug (performE (opArgE 5 0 .unit)) := by
  rfl

/-- The clause applied to the argument and `capture l H K`, run: a chain to `()`. -/
def capRun : Expr := appE clT (.pair .unit (kappa ⟨hndValE 5 (qualsVal [.lin]).1 hrT [clT],
  .pair .prim (.pair (qualsVal [.lin]).2 (.pair .lam (.pair .lam .unit)))⟩ .hole))

theorem capRun_end : lookEnd 20 capRun = .unit := by rfl

theorem capRun_shapes : (chainTerms capRun (lookRun 20 capRun)).all
    (fun t => !occursIn isPerform t && !occursIn isAlloc t) = true := by
  rfl

/-- `lab5A`'s operation is `tick : 1 ↠ 1`, linear. -/
theorem sig_lab5A {J : OurTyping orowRF} :
    ((ourInst (ℍ := ℍ) orowRF ΞA J).sig lab5A)[0]? =
      some ⟨OVTy.ofV .unit, OVTy.ofV .unit, .linear⟩ := by
  simp [lab5A, ΞA]; rfl

/-- **`progT`'s catch is reached by a typed program**: Core's kernel types `progT` at `F 1`, its
rows tied to `ΞA`, and `look`'s run reaches the catch. -/
theorem live_progT_catch :
    (ourInst (ℍ := ℍ) orowRF ΞA J₁).Live (Adequacy.emptyMem, lookEnd 2 progT) := by
  let S := ourInst (ℍ := ℍ) orowRF ΞA J₁
  have hder : S.der [] progT (S.F (orowAlg ΞA).unit (OVTy.ofV .unit)) :=
    der_J₁_ret (by decide) progT_derivesAt
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ progT) ((Adequacy.emptyMem, lookEnd 2 progT), ()) :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 2 progT)
  exact ⟨progT, _, S.R₀, (), r₀_respects, hder, hreach⟩

/-- `progT`'s catch is the handler of `lab5A` around `tick`'s `perform`, in the empty context. -/
theorem progT_catch_term :
    (ourInst (ℍ := ℍ) orowRF ΞA J₁).term (Adequacy.emptyMem, lookEnd 2 progT) =
      (ourInst (ℍ := ℍ) orowRF ΞA J₁).plug .hole ((ourInst (ℍ := ℍ) orowRF ΞA J₁).handle lab5A
        ((ourInst (ℍ := ℍ) orowRF ΞA J₁).hnd ⟨hrT, .lam⟩ [⟨clT, .lam⟩])
        ((ourInst (ℍ := ℍ) orowRF ΞA J₁).plug .hole ((ourInst (ℍ := ℍ) orowRF ΞA J₁).perform lab5A 0
          (ourInst (ℍ := ℍ) orowRF ΞA J₁).unitV))) := by
  rw [progT_catch]; rfl

/-- **At `progT`'s catch the store-keeping alternative fails**: from the catch, the store-keeping
steps reach only the catch and the clause applied to `κ` before its cell (the next step allocates
the cell), whose terms name `perform` and `alloc`; the clause applied to the argument and
`capture l H K` runs, keeping the store, through terms that name neither. -/
theorem not_pureJoin_progT :
    ¬ (ourInst (ℍ := ℍ) orowRF ΞA J₁).PureJoin (Adequacy.emptyMem, lookEnd 2 progT)
      ((ourInst (ℍ := ℍ) orowRF ΞA J₁).setT (Adequacy.emptyMem, lookEnd 2 progT)
        ((ourInst (ℍ := ℍ) orowRF ΞA J₁).plug .hole ((ourInst (ℍ := ℍ) orowRF ΞA J₁).app
          ((ourInst (ℍ := ℍ) orowRF ΞA J₁).force ⟨clT, .lam⟩)
          ((ourInst (ℍ := ℍ) orowRF ΞA J₁).pair (ourInst (ℍ := ℍ) orowRF ΞA J₁).unitV
            ((ourInst (ℍ := ℍ) orowRF ΞA J₁).capture lab5A
              ((ourInst (ℍ := ℍ) orowRF ΞA J₁).hnd ⟨hrT, .lam⟩ [⟨clT, .lam⟩]) .hole))))) := by
  rintro ⟨d, hdL, hdR⟩
  let S := ourInst (ℍ := ℍ) orowRF ΞA J₁
  -- from the catch: the catch, or the clause at `κ` before its cell
  have hcatchT : lookEnd 2 progT = Kont.hole.plug (hndE (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩
      ⟨clausesE [clT], .pair .lam .unit⟩) (Kont.hole.plug (performE (.val (opPayload 5 0 Val.unit))))) := by
    rw [progT_catch]; rfl
  have hhop := Head.hop (ℍ := ℍ) Adequacy.emptyMem 5 0 (qualsVal [.lin]) ⟨hrT, .lam⟩
    ⟨clausesE [clT], .pair .lam .unit⟩ ⟨clT, .lam⟩ Val.unit .hole
    (clauseAt_clausesE [clT] 0 .lam rfl) rfl
  have hkc : kappaAt (capTag (qualsVal [.lin]).1 (0 : UInt32).toNat)
      (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩) .hole =
      kappaCell false (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩)
        .hole := rfl
  rw [hkc] at hhop
  have hL : d = (Adequacy.emptyMem, lookEnd 2 progT) ∨
      d = (Adequacy.emptyMem, .app clT (.pair .unit (kappaCell false
        (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩) .hole))) := by
    rcases Relation.ReflTransGen.cases_head hdL with rfl | ⟨c₁, ⟨ev, hst, -⟩, hrest⟩
    · exact .inl rfl
    · right
      change OStep (ℍ := ℍ) orowRF ΞA (Adequacy.emptyMem, lookEnd 2 progT) ev c₁ at hst
      rw [hcatchT] at hst
      obtain ⟨-, rfl⟩ := det_ourInst (K := .hole) hhop rfl hst
      rcases Relation.ReflTransGen.cases_head hrest with rfl | ⟨c₂, ⟨ev', hpst⟩, -⟩
      · rfl
      · exact (no_pureStep_alloc (J := J₁) (μ := Adequacy.emptyMem)
          (.appR (.val ⟨clT, .lam⟩) (.pairR Val.unit (.appR (.val (Val.lam (BoCa.BoLo.kappaCBody
            false (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩)
              .hole))) .hole))) hpst).elim
  -- from the clause at `capture l H K`: the chain to `()`
  have hHV : IsVal (hndValE 5 (qsOf ΞA 5) hrT (List.map Subtype.val [(⟨clT, .lam⟩ : OVal)])) :=
    .pair .prim (.pair (qualsVal [.lin]).2 (.pair .lam (.pair .lam .unit)))
  have hc' : S.setT (Adequacy.emptyMem, lookEnd 2 progT) (S.plug .hole (S.app (S.force ⟨clT, .lam⟩)
      (S.pair S.unitV (S.capture lab5A (S.hnd ⟨hrT, .lam⟩ [⟨clT, .lam⟩]) .hole)))) =
      (Adequacy.emptyMem, capRun) := by
    show (Adequacy.emptyMem, appE clT (.pair .unit (captureE 5 (qsOf ΞA 5) hrT
      (List.map Subtype.val [(⟨clT, .lam⟩ : OVal)]) .hole))) = _
    rw [captureE_of_val .hole hHV]
    rfl
  rw [hc'] at hdR
  have hchain := lookRun_sound (ℍ := ℍ) 20 capRun
  rw [capRun_end] at hchain
  obtain ⟨-, hmem⟩ := pureSteps_chain (J := J₁) (Ξ := ΞA) hchain .unit d hdR
  have hall := List.all_eq_true.1 capRun_shapes d.2 hmem
  rcases hL with rfl | rfl
  · have hp : occursIn isPerform (lookEnd 2 progT) = true := by rfl
    simp [hp] at hall
  · have ha : occursIn isAlloc (.app clT (.pair .unit (kappaCell false
        (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩) .hole))) =
        true := by rfl
    simp [ha] at hall

/-- **S4 with no cell FAILS at `J₁`, at the admissible context `ΞA`**: its catch law asks the
store-keeping alternative at every catch, and `progT`'s catch of the linear `tick` has none
(`not_pureJoin_progT`).  S4 holds there (`handlerSem_orow`): the catch allocates `κ`'s cell. -/
theorem not_handlerSemNoCell_J₁_ΞA : ¬ (ourInst (ℍ := ℍ) orowRF ΞA J₁).HandlerSemNoCell :=
  fun hS => not_pureJoin_progT (hS.2.1 (Adequacy.emptyMem, lookEnd 2 progT) .hole lab5A
    ⟨hrT, .lam⟩ [⟨clT, .lam⟩] .hole 0 (ourInst (ℍ := ℍ) orowRF ΞA J₁).unitV
    ⟨OVTy.ofV .unit, OVTy.ofV .unit, .linear⟩ ⟨clT, .lam⟩ live_progT_catch progT_catch_term rfl
    sig_lab5A (fun h => by cases h) rfl)

end Targets.Inst

end
