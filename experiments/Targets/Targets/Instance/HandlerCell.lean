import Core.EffExamples
import Targets.Instance.CellRuns

/-!
# The Instance — S4's catch law, read at `capture`, at the capture cell

S4's catch law (`HandlerSem`, its second conjunct) says that a resuming operation caught by a
handler reaches, by steps that keep the store, a common reduct with the clause applied to the
argument and `capture l H K`.  At a linear or affine operation the catch hands the clause `κ` with a
fresh cell (SPEC §25): the `[op]` step reaches the clause applied to `κ` before its cell, and the next
step allocates the cell, which changes the store.

**The catch law FAILS AS WRITTEN at `J₁`, at the admissible context `ΞA`** (`not_handlerSem_J₁_ΞA`).
The witness is `progT`: Core's handled program of `Core/EffExamples.lean` at the name `5`, where `ΞA`
declares `tick : 1 ↠ 1` linear; Core's kernel types it at `F 1`.  Its run reaches the catch; from
there the store-keeping steps reach only the catch and the clause applied to `κ` before its cell,
each of which names `perform` or `alloc`, while the clause applied to `capture l H K` runs, keeping
the store, through terms that name neither, to `()` (`pureSteps_chain`).

What the witness reads: S4's catch law hands `capture l H K` and keeps the store; decision S6 makes
the catch of a linear or affine operation allocate.  At an effect context whose resuming operations
are unrestricted the law holds (`handlerSem_orow`).  The restatement is the user's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE hndVal kappa clauseAt
  capTag kappaAt kappaCell)
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
    (.effPerform (o := ⟨5, 0, .lin, .unit, .unit⟩) (by rfl) rfl (.unitI (.cons (.cons .nil))))

/-- `cl₀`, the clause, as a term. -/
def clT : Expr := .lam (.letpair (.var 0) (.app (.app (.var 0) (.inj₁ .unit)) (.var 1)))

/-- `h_ret = λx. x`, as a term. -/
def hrT : Expr := .lam (.var 0)

/-- The catch: the handler of `5` around `perform (5, (0, ()))`, after the program's bindings. -/
theorem progT_catch : lookEnd 2 progT =
    (handleK 5 (qualsVal [.lin]).1 hrT [clT]).plug (performE (opArgE 5 0 .unit)) := by
  rfl

/-- The clause applied to the argument and `capture l H K`, run: a chain to `()`. -/
def capRun : Expr := appE clT (.pair .unit (kappa 5 ⟨hndValE 5 (qualsVal [.lin]).1 hrT [clT],
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

/-- **S4's catch law FAILS AS WRITTEN at `J₁`, at the admissible context `ΞA`.**  `progT`, typed
by Core's kernel at `F 1`, reaches the catch of the linear `tick`; from there the store-keeping
steps reach only the catch and the clause applied to `κ` before its cell (the next step allocates
the cell), whose terms name `perform` and `alloc`; the clause applied to `capture l H K` runs,
keeping the store, through terms that name neither. -/
theorem not_handlerSem_J₁_ΞA : ¬ (ourInst (ℍ := ℍ) orowRF ΞA J₁).HandlerSem := by
  intro hS
  obtain ⟨-, hcatch, -⟩ := hS
  let S := ourInst (ℍ := ℍ) orowRF ΞA J₁
  have hder : S.der [] progT (S.F (orowAlg ΞA).unit (OVTy.ofV .unit)) :=
    der_J₁_ret (by decide) progT_derives
  have hreach : S.RReach S.R₀ (S.rinit S.R₀ progT) ((Adequacy.emptyMem, lookEnd 2 progT), ()) :=
    rreach_of_chain S.R₀ (lookRun_sound (ℍ := ℍ) 2 progT)
  have hlive : S.Live (Adequacy.emptyMem, lookEnd 2 progT) :=
    ⟨progT, _, S.R₀, (), r₀_respects, hder, hreach⟩
  obtain ⟨d, hdL, hdR⟩ := hcatch (Adequacy.emptyMem, lookEnd 2 progT) .hole lab5A ⟨hrT, .lam⟩
    [⟨clT, .lam⟩] .hole 0 S.unitV ⟨OVTy.ofV .unit, OVTy.ofV .unit, .linear⟩ ⟨clT, .lam⟩ hlive
    (by rw [progT_catch]; rfl) rfl sig_lab5A (fun h => by cases h) rfl
  -- from the catch: the catch, or the clause at `κ` before its cell
  have hcatchT : lookEnd 2 progT = Kont.hole.plug (hndE (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩
      ⟨clausesE [clT], .pair .lam .unit⟩) (Kont.hole.plug (performE (.val (opPayload 5 0 Val.unit))))) := by
    rw [progT_catch]; rfl
  have hhop := Head.hop (ℍ := ℍ) Adequacy.emptyMem 5 0 (qualsVal [.lin]) ⟨hrT, .lam⟩
    ⟨clausesE [clT], .pair .lam .unit⟩ ⟨clT, .lam⟩ Val.unit .hole
    (clauseAt_clausesE [clT] 0 .lam rfl) rfl
  have hkc : kappaAt (capTag (qualsVal [.lin]).1 (0 : UInt32).toNat) 5
      (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩) .hole =
      kappaCell false 5 (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩)
        .hole := rfl
  rw [hkc] at hhop
  have hL : d = (Adequacy.emptyMem, lookEnd 2 progT) ∨
      d = (Adequacy.emptyMem, .app clT (.pair .unit (kappaCell false 5
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
            false 5 (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩)
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
  · have ha : occursIn isAlloc (.app clT (.pair .unit (kappaCell false 5
        (hndVal 5 (qualsVal [.lin]) ⟨hrT, .lam⟩ ⟨clausesE [clT], .pair .lam .unit⟩) .hole))) =
        true := by rfl
    simp [ha] at hall

end Targets.Inst

end
