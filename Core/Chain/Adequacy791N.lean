import Core.Chain.HandlerLawN
import Core.EffPrograms

/-!
# #791's end goal: plain adequacy, every handler inside the program  `[spec §62]`

`docs/new-core/assert-boundary.md` §5.1. `Goal791N`: every closed program typed at `F 1` from the
suspending lend constants, each meeting its rule's premises, steps or is final with the empty
heap, or runs forever. A program that suspends handles its operations inside itself: its handlers
are typed by `CDerives`'s handler rules, so no scheduler or contract is quantified over.

* `constN_all`: every constant is a value of `!` its type at `vN`, its finaliser's judgment read
  by `fundamentalN_all`. No fragment premise.
* `gN_ctx791`: the constants' context is met by their values, with no resource.
* `goal791N`: `Goal791N` from `HandlerLawN`, its only hypothesis. `fundamentalN_all` at the
  program's derivation, at the empty world; `F 1` at `KW` is `erwp` at the empty table
  (`cN_ret_iff`); `erwp_adequacy` there.
* `goal791N_premises_inst`, `prog791_orDiverges`: every premise of `Goal791N` at a closed program
  whose lend callback performs while it holds a `mut` borrow, under a handler inside the program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 defines_meetOfDom_empty)
open BoCa.BoLo (performE)
open BoCa.Programs (alloc' free')
open BoCa.Fig16.LogRel.Core.EffPrograms (callbackUW)
open BoCa.Fig16.LogRel.Core.CancelIntercept (idV)

/-- **Every #791 constant is a value of `!` its type**, from `MissingN`: each constant's
compatibility lemma at `cN`, its finaliser's judgment read by `fundamentalN_all`. -/
theorem constN_all (hm : MissingN (ℍ := ℍ)) : ∀ c : Const791, ConstN (ℍ := ℍ) c
  | .w2 .. => by
      rintro ⟨hbnd, hO, hA, hB, hS, hdc, hder⟩ δ Θ n _
      exact withbor2S_compat hbnd hO hA hB hS hdc (fundamentalN_all hm hder) δ Θ n
  | .w3 .. => by
      rintro ⟨hbnd, hA, hB, hS, hdc, hder⟩ δ Θ n _
      exact withbor3S_compat hbnd hA hB hS hdc (fundamentalN_all hm hder) δ Θ n
  | .wF .. => by
      rintro ⟨hbnd, hA, hB, hS, hdc, hder⟩ δ Θ n _
      exact withborFS_compat hbnd hA hB hS hdc (fundamentalN_all hm hder) δ Θ n
  | .wl .. => constN_wl
  | .sm .. => by
      rintro ⟨hbnd, hOA, hOB, hA, hB, hS, hdc, hder⟩ δ Θ n _
      exact sliceBorrowMS_compat hbnd hOA hOB hA hB hS hdc (fundamentalN_all hm hder) δ Θ n

/-- **The constants' context is met by their values**, at every world, with no resource. -/
theorem gN_ctx791 (hC : ∀ c : Const791, ConstN (ℍ := ℍ) c) (δ : LSub) {Θ : LocTy} (hΘ : Θ.OK)
    (n : Nat) : ∀ cs : List Const791, (∀ c ∈ cs, c.OK) →
      gN (ℍ := ℍ) δ Θ (ctx791 cs) (vals791 cs) n PMap.empty
  | [], _ => rfl
  | c :: cs, hcs => by
      simp only [ctx791, vals791, List.map_cons, gN, if_true]
      exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
        hC c (hcs c (by simp)) δ Θ n hΘ,
        gN_ctx791 hC δ hΘ n cs (fun c' h => hcs c' (by simp [h]))⟩

/-- **#791's end goal.** Every closed program typed at `F 1` from the constants `cs`, each
meeting its rule's premises, with every handler it uses inside it, steps or is final with the
empty heap, or runs forever. -/
def _root_.BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N : Prop :=
  ∀ (cs : List Const791), (∀ c ∈ cs, c.OK) → ∀ e₀ : Expr,
    CDerives LifeCtx.empty (ctx791 cs) e₀ (.comp (.ret .unit)) →
      OrDiverges (ℍ := ℍ) (substAll (vals791 cs) e₀)

/-- **`Goal791N` from `HandlerLawN`**: the fundamental property at the program's derivation, at
the empty world and view, every constant a value of its type; `F 1` at the typed world is `erwp`
at the empty table (`cN_ret_iff`), and a closed `erwp` run of `F 1` at every index is
`OrDiverges` (`erwp_adequacy`). -/
theorem goal791N (h : HandlerLawN (ℍ := ℍ)) : Goal791N (ℍ := ℍ) := by
  intro cs hcs e₀ hder
  have hm := handlerLawN_iff.mp h
  have hall : ∀ n, erwp (ℍ := ℍ) LocFam.empty (opTableN OpTabN.empty)
      (fun k _ v ρ => vN (ℍ := ℍ) .unit LSub.empty LocTy.empty k v ρ) n []
      (substAll (vals791 cs) e₀) PMap.empty := fun n => by
    have hr := fundamentalN_all hm hder LSub.empty (vals791 cs) LocTy.empty (fun _ => none) n
      [] PMap.empty (models_empty_any _) LocTy.empty_ok (consistentX_empty _)
      (liveWithin_ctx791 cs) (gN_ctx791 (constN_all hm) LSub.empty LocTy.empty_ok n cs hcs)
    have hr' := (cN_ret_iff .unit LSub.empty LocTy.empty (fun _ => none) n [] _ _).mp hr
    rwa [LocTy.view_empty] at hr'
  intro μ e hs
  exact erwp_adequacy (fun _ _ _ _ hq => hq.2) hall (ImmTieL.nil _) hs

/-! ### `Goal791N`'s premises at a program holding a borrow across a suspension

`prog791` lends a cell `mut` with the constant `withbor (2)` at a suspending row, its callback
performs `wait` while it holds the borrow, then releases it; the cell is freed after the lend. The
handler of `wait` is inside the program (`effHandleT`, its clause resuming `κ` in tail position).
Every premise of `Goal791N` holds there (`goal791N_premises_inst`), so `Goal791N` concludes
`OrDiverges` of that program from `HandlerLawN` (`prog791_orDiverges`). -/

/-- `wait : 1 ↠^lin 1`, the operation `0` of the name `7`. -/
abbrev waitE : List (Qual × VTy × VTy) := [(.lin, .unit, .unit)]
/-- The name of `wait`. -/
abbrev waitN : UInt32 := 7
/-- The callback's row, and the handled row. -/
abbrev waitRow : Row := Row.ofEff waitN waitE 0 finsNil ++ []
/-- `wait`'s signature. -/
abbrev waitSig : OpSig := ⟨waitN, 0, .lin, .unit, .unit, .ret .unit, false⟩

theorem waitRow_eq : waitRow = [waitSig] := rfl

/-- The callback's type: `∀'x ⊏ ⊓∅. Mut 'x 1 ⊸ F_{wait}(['x] 1)`. -/
abbrev cbTy : VTy := cbUTy 0 LifeCtx.empty.meetOfDom (.mut (.var 0) .unit) .unit waitRow
/-- `withbor (2)` at the callback's row, finalised by the consume of `Ref 1`. -/
abbrev lendC : Const791 := .w2 0 LifeCtx.empty.meetOfDom .unit .unit waitRow (consumeE (.ref .unit))

/-- `wait ()`. -/
def waitPerform : Expr := performE (opArgE waitN 0 (.val .unit))

/-- The callback: `Λ. λm. wait (); release m; ['x] ()`. -/
def cbBody : Expr :=
  .app (.val (.lam (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit))))) waitPerform

/-- The callback as a value. -/
def cbE : Expr := .val (.lam (.val (.lam cbBody)))

/-- The handled body: `r ← alloc (); cb; w ← withbor; (r, b) ← w r cb; b; free r`. -/
def bodyE : Expr :=
  bindE (.app alloc' (.val .unit))
    (bindE cbE
      (bindE (.var 2)
        (.app (.val (.lam (.letpair (.var 0) (.seq (.var 0) (.app free' (.var 1))))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

theorem waitRow_not_cancels : ¬ waitRow.Cancels := by
  rintro ⟨o, ho, h⟩; simp [Row.ofEff] at ho; subst ho; exact h rfl

theorem waitRow_not_unr : ¬ waitRow.Unr := by
  rintro ⟨o, ho, h⟩; simp [Row.ofEff] at ho; subst ho; cases h

theorem d_cbE {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) : CDerives LifeCtx.empty Γ cbE (.val cbTy) := by
  refine callbackUW ok_empty rfl hΓ ?_
  refine .effLet (A := .unit) (.right (.dead (deadSplit hΓ)))
    (fun h => absurd h waitRow_not_cancels) (fun h => absurd h waitRow_not_unr)
    (.effPerform (o := waitSig) rfl rfl rfl (.unitI (by cdead))) ?_
  refine .unitE (.left (.right (.dead (deadSplit hΓ)))) (.var (by csolo)) ?_
  refine .unitE (.dead (.left (.dead (deadSplit hΓ))))
    (appW (.var (by csolo)) (.releaseMut (by cdead))) ?_
  exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
    (.ret (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, fun s hs hl =>
      dead_noLive (P := fun s => VOutlives _ _ s.ty) (by cdead) s hs hl⟩))

theorem d_bodyE :
    CDerives LifeCtx.empty [⟨.bang lendC.ty, true⟩] bodyE (.comp (CTy.effOf waitRow .unit)) := by
  refine .bind (A := .ref .unit) (.right .nil)
    (.ret (appW (.unitI (by cdead)) (.alloc (by cdead)))) ?_
  refine .bind (.right (.right .nil)) (.ret (d_cbE (by cdead))) ?_
  refine .bind (.right (.right (.left .nil)))
    (.ret (.bangE (.var (.there (.there (.here .nil)))))) ?_
  refine .effLet (A := .tensor (.ref .unit) .unit) (.left (.left (.left (.dead .nil))))
    (fun h => absurd h waitRow_not_cancels) (fun h => absurd h waitRow_not_unr) ?_ ?_
  · refine .app (.left (.right (.left (.dead .nil)))) ?_ (.there (.here (by cdead)))
    exact .app (.left (.dead (.right (.dead .nil)))) (.force (.here (by cdead)))
      (.there (.there (.here (by cdead))))
  · refine .tensorE (.left (.dead (.dead (.dead (.dead .nil))))) (.var (.here (by cdead))) ?_
    refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead .nil)))))))
      (.var (by csolo)) ?_
    exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (appW (.var (by csolo)) (.free (by cdead))))

/-- The handler: `h_ret = λx. x`, and `wait`'s clause resumes `κ` with `()` in tail position. -/
def waitH : Expr := .pair (.val idV) (tailTuple waitE 0 (.pair (.val idV) (.val .unit)))

/-- **The program**: `handle_7 (r ← alloc (); (r, b) ← withbor r (Λ. λm. wait (); release m);
b; free r) with waitH`. -/
def prog791 : Expr := hndExpr waitN (waitE.map Prod.fst) waitH bodyE

theorem d_prog791 :
    CDerives LifeCtx.empty (ctx791 [lendC]) prog791 (.comp (.ret .unit)) := by
  refine .effHandleT (S := []) (SN := []) (A := .unit) (R := .unit) (fs := finsNil)
    (.right .nil) (.cons .nil) (.val _) (.pair (.val _) (.val _)) ?_ (by decide) (by decide)
    (by simp) (by simp) (RowLe.nil []) (by simp) d_bodyE
  exact .tensorI (.dead .nil) (CancelIntercept.d_idVΓ (.cons .nil) [] .unit)
    (.tensorI (.dead .nil) (CancelIntercept.d_idVΓ (.cons .nil) [] .unit) (.unitI (.cons .nil)))

theorem lendC_ok : lendC.OK := by
  refine ⟨defines_meetOfDom_empty, ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩, id, id, ?_, by decide,
    consume_wf (.ref .unit) .nil⟩
  intro o ho
  simp [Row.ofEff] at ho
  subst ho
  exact ⟨by decide, by decide, id, id, .unit, .unit, fun _ => trivial⟩

/-- **Every premise of `Goal791N` holds at `prog791`**: the constant meets its rule's premises,
and the program, its handler inside it, is typed at `F 1` from it. -/
theorem goal791N_premises_inst :
    (∀ c ∈ [lendC], c.OK) ∧ CDerives LifeCtx.empty (ctx791 [lendC]) prog791 (.comp (.ret .unit)) :=
  ⟨by simpa using lendC_ok, d_prog791⟩

/-- **`Goal791N` at `prog791`**: the run of the program holding a borrow across `wait` is safe,
leak-free, or diverges, from `HandlerLawN`. -/
theorem prog791_orDiverges (h : HandlerLawN (ℍ := ℍ)) :
    OrDiverges (ℍ := ℍ) (substAll (vals791 [lendC]) prog791) :=
  goal791N h [lendC] goal791N_premises_inst.1 prog791 goal791N_premises_inst.2

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
