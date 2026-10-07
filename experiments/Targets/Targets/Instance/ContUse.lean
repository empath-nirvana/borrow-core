import Targets.Instance.Checks
import Targets.Instance.J1Checks

/-!
# The Instance — S6's teeth: R1–R4 at our machine

RESTRUCTURE §6.1 keeps four rejected programs as the witnesses that S6 (`ContUse`) bites.  Each is
`withCl l cl` (`Targets/A/Programs.lean`): a handler of `l` around `op () to _. return tt`, its
clause `cl` one of

* R1, `dropCl`: `op (v, k) ⇒ return ff` — `κ` is never used;
* R2, `twiceCl`: `op (v, k) ⇒ resume k () to _. resume k ()` — `κ` is resumed twice;
* R3, `cancelCl`: `op (v, k) ⇒ cancel k to _. return ff` — `κ` is cancelled;
* R4, `cancelResumeCl`: `op (v, k) ⇒ cancel k to _. resume k ()` — `κ` is resumed after its
  cancel.

Each runs to a data answer on our machine, under the runner that answers nothing, whatever the
typing system: the run is a chain of head steps that allocate nothing, so it is the program's only
run.  On it the counts of S6 break.  R1 catches `κ` once and uses it never, which breaks the
exactly-once clause when `l`'s operation resumes.  R2 and R4 use `κ` twice and catch it at most
once, at any label.  R3 cancels `κ`, and no affine catch made it when `l`'s operation is linear.
So **every typing system over our machine that types one of them at `F 0 bool` fails S6**
(`not_contUse_of_der_R1` … `_R4`).  At a general row form they take what `orowRF` gives: the pure
row reads as the empty row, labels' names are not the reserved `0` (the cancel), and signatures
have at most `2³²` operations (`_orow` drops them).

**The witnesses' premises are met**: `JR` types the four programs, and at the admissible context
`ΞA` each lemma applies to it (`teeth_JR_ΞA`).

**Today's kernel types none of R1–R4** (`refuses_R_tier1Open`), for the reason it types no A-level
handler: our instance's handler is the run-time frame, whose clauses are values, and `[handle]`
types clause variables (`not_der_handle_tier1Open`).  That reason is the handler's form, not the
linearity of `κ`.  The linearity refusal RESTRUCTURE §6.1 names (`kTy` at `lin`/`aff` is a thunk,
neither droppable nor persistent; a linear `κ`'s cancel branch is at `⊤`) is an inversion of the
clauses' typing at `clauseTy`, and is not built here.

The runs are written out at a symbolic label name `n`, since a label's name is the row form's.  A
step's configuration is read through `chainTerms`, and a count of S6 along a path is a count over
the configurations before its steps (`countP_range_take`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.A.EffectSystem

variable {S : EffectSystem}

/-- A count over the steps of a path is a count over the configurations before them. -/
theorem countP_range_take {R : S.Runner} (c : S.RConf R) (q : List (S.Event × S.RConf R))
    (p : ℕ → Bool) (p' : S.RConf R → Bool) (h : ∀ j < q.length, p j = p' (S.cfgAt c q j)) :
    (List.range q.length).countP p = ((c :: q.map Prod.snd).take q.length).countP p' := by
  have hmap : (List.range q.length).map (S.cfgAt c q) = (c :: q.map Prod.snd).take q.length := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp only [List.length_map, List.length_range] at h₁
      simp only [List.getElem_map, List.getElem_range, List.getElem_take]
      unfold cfgAt
      rw [List.getElem?_eq_getElem (by simp; omega)]
      rfl
  rw [← hmap, List.countP_map]
  refine List.countP_congr fun j hj => ?_
  rw [h j (List.mem_range.1 hj)]
  rfl

open Classical in
/-- A catch along the path counts. -/
theorem caught_pos {R : S.Runner} {c₀ : S.RConf R} {q : List (S.Event × S.RConf R)} {j : ℕ}
    {κ : S.Val} {k : OpClass} (h : S.CatchAt c₀ q j κ k) : 0 < S.caught c₀ q κ := by
  have hj : j ∈ List.range q.length := List.mem_range.2 h.1
  have hk : k ≠ .abortive := by
    obtain ⟨-, _, _, _, _, _, _, _, _, -, -, -, -, hk, -⟩ := h
    exact hk
  cases k with
  | abortive => exact absurd rfl hk
  | linear =>
      have : 0 < S.caughtLin c₀ q κ := List.countP_pos_iff.2 ⟨j, hj, by simpa using h⟩
      unfold caught; omega
  | affine =>
      have : 0 < S.caughtAff c₀ q κ := List.countP_pos_iff.2 ⟨j, hj, by simpa using h⟩
      unfold caught; omega

end Targets.A.EffectSystem

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa clauseAt)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF HeadChain)

/-! ### The programs, at a name -/

/-- The return clause `return x ⇒ x`. -/
def rRet : Expr := .lam (.var 0)

/-- `tt`. -/
def rTt : Expr := .inj₂ .unit

/-- `□ to _. return tt`. -/
def rK : Kont := bindK rTt

/-- The handler of the name `n` with the clause `cl`, as a value. -/
def rH (n : UInt32) (cl : Val) : Val := hndVal n ⟨rRet, .lam⟩ ⟨clausesE [cl.1], .pair cl.2 .unit⟩

/-- `withCl` at the name `n`: `hnd (n, (return x ⇒ x, [cl])) (op () to _. return tt)`. -/
def rProg (n : UInt32) (cl : Val) : Expr :=
  (handleK n rRet [cl.1]).plug (rK.plug (performE (opArgE n 0 .unit)))

/-- The continuation the catch hands the clause. -/
def rκ (n : UInt32) (cl : Val) : Val := ⟨kappa n (rH n cl) rK, .lam⟩

theorem rProg_eq (n : UInt32) (cl : Val) :
    rProg n cl = hndE (rH n cl) (rK.plug (performE (.val (opPayload n 0 Val.unit)))) := rfl

/-- **The catch**: the handler hands its clause `((), κ)`. -/
theorem head_rCatch (μ : Heap) (n : UInt32) (cl : Val) :
    Head (ℍ := ℍ) μ (rProg n cl) μ (.app cl.1 (.pair .unit (rκ n cl).1)) := by
  rw [rProg_eq]
  exact Head.hop μ n 0 ⟨rRet, .lam⟩ ⟨clausesE [cl.1], .pair cl.2 .unit⟩ cl Val.unit rK
    (clauseAt_clausesE [cl.1] 0 cl.2 rfl) rfl

/-! ### Chains: concatenation, and the segments of a resume and a cancel -/

theorem _root_.Targets.HeadChain.append {e e₁ e₂ : Expr} :
    ∀ {q₁ q₂ : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q₁ e₁ → HeadChain (ℍ := ℍ) e₁ q₂ e₂ →
      HeadChain (ℍ := ℍ) e (q₁ ++ q₂) e₂
  | _, _, .nil, h₂ => h₂
  | _, _, .cons hh hn h₁, h₂ => .cons hh hn (HeadChain.append h₁ h₂)

/-- A chain's steps, in a context. -/
def plugRun (K₀ : Kont) (q : List (Kont × Expr × Expr)) : List (Kont × Expr × Expr) :=
  q.map fun x => (K₀.comp x.1, x.2.1, x.2.2)

/-- `κ`'s body at the selector `s`: resume (`inj₁ ()`) or cancel (`inj₂ ()`). -/
def kSel (n : UInt32) (cl : Val) (s : Expr) : Expr :=
  .case s (.seq (.var 0) (.lam (hndE (rH n cl) (rK.plug (.var 0)))))
    (.seq (.var 0) (ccatchE (hndE (rH n cl) (rK.plug (raiseE (.val (cancelVal [n] none)))))))

/-- The handler frame of `withCl`. -/
def rHK (n : UInt32) (cl : Val) : Kont := .appR (.app (.prim .hnd) (rH n cl).1) .hole

/-- **A resume of `κ` at `w`**: `resume κ w` binds `w`, `κ` selects its resume branch, which
reinstalls the handler around `□ to _. return tt` at `w`; that returns `tt` through the handler's
return clause. -/
def resumeRun (n : UInt32) (cl : Val) (w : Val) : List (Kont × Expr × Expr) :=
  [(.hole, resumeE (rκ n cl).1 w.1, .app (.app (rκ n cl).1 (.inj₁ .unit)) w.1),
   (.appL .hole w, .app (rκ n cl).1 (.inj₁ .unit), kSel n cl (.inj₁ .unit)),
   (.appL .hole w, kSel n cl (.inj₁ .unit), .seq .unit (.lam (hndE (rH n cl) (rK.plug (.var 0))))),
   (.appL .hole w, .seq .unit (.lam (hndE (rH n cl) (rK.plug (.var 0)))),
     .lam (hndE (rH n cl) (rK.plug (.var 0)))),
   (.hole, .app (.lam (hndE (rH n cl) (rK.plug (.var 0)))) w.1, hndE (rH n cl) (rK.plug w.1)),
   (rHK n cl, rK.plug w.1, rTt),
   (.hole, hndE (rH n cl) rTt, .app rRet rTt),
   (.hole, .app rRet rTt, rTt)]

/-- `κ`'s body. -/
def kBody (n : UInt32) (cl : Val) : Expr :=
  .case (.var 0)
    (.seq (.var 0) (.val (.lam (hndE ((rH n cl).shift 3 0) ((rK.shift 3 0).plug (.var 0))))))
    (.seq (.var 0) (ccatchE (hndE ((rH n cl).shift 2 0)
      ((rK.shift 2 0).plug (raiseE (.val (cancelVal (n :: rK.hndNames) none)))))))

theorem rκ_eq (n : UInt32) (cl : Val) : (rκ n cl).1 = .lam (kBody n cl) := rfl

/-- The body of the twice-resuming clause under its `let`. -/
def twBody : Expr := bindE (resumeE (.var 0) .unit) (resumeE (.var 1) .unit)

/-- The twice-resuming clause, at our instance. -/
def twiceV : Val := ⟨.lam (.letpair (.var 0) twBody), .lam⟩

theorem resume_chain_twice (n : UInt32) (w : Val) :
    HeadChain (ℍ := ℍ) (resumeE (rκ n twiceV).1 w.1) (resumeRun n twiceV w) rTt := by
  refine .cons (K := .hole) (fun μ => Head.beta μ
    (.app (.app ((rκ n twiceV).1.shift 1 0) (.inj₁ .unit)) (.var 0)) w) rfl ?_
  refine .cons (K := .appL .hole w) (fun μ => Head.beta μ (kBody n twiceV) (Val.inj₁ Val.unit)) rfl ?_
  refine .cons (K := .appL .hole w) (fun μ => Head.case₁ μ Val.unit _ _) rfl ?_
  refine .cons (K := .appL .hole w) (fun μ => Head.seq μ _) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (hndE (rH n twiceV) (rK.plug (.var 0))) w) rfl ?_
  refine .cons (K := rHK n twiceV) (fun μ => Head.beta μ rTt w) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.hret μ n ⟨rRet, .lam⟩ _ ⟨rTt, .inj₂ .unit⟩) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (.var 0) ⟨rTt, .inj₂ .unit⟩) rfl ?_
  exact .nil

/-- `κ`'s handler catches no cancel: its name is not the reserved `0`. -/
theorem rCancelK_catches {n : UInt32} (hn : n ≠ 0) (cl : Val) :
    ((rHK n cl).comp rK).Catches 0 = false := by
  simp [rHK, rK, bindK, rH, hndVal, Kont.comp, Kont.Catches, Val.i32, hn]

/-- **A cancel of `κ`**: `κ` selects its cancel branch, which raises the cancel through the
reinstalled handler and `□ to _. return tt`, neither of which stops it, to `ccatch`, which answers
`()`. -/
def cancelRun (n : UInt32) (cl : Val) : List (Kont × Expr × Expr) :=
  [(.hole, cancelE (rκ n cl).1, kSel n cl (.inj₂ .unit)),
   (.hole, kSel n cl (.inj₂ .unit),
     .seq .unit (ccatchE (hndE (rH n cl) (rK.plug (raiseE (.val (cancelVal [n] none))))))),
   (.hole, .seq .unit (ccatchE (hndE (rH n cl) (rK.plug (raiseE (.val (cancelVal [n] none)))))),
     ccatchE (hndE (rH n cl) (rK.plug (raiseE (.val (cancelVal [n] none)))))),
   (.hole, ccatchE (hndE (rH n cl) (rK.plug (raiseE (.val (cancelVal [n] none))))), .unit)]

/-- The body of the cancelling clause under its `let`. -/
def cBody : Expr := bindE (cancelE (.var 0)) (.inj₁ .unit)

/-- The cancelling clause, at our instance. -/
def cancelV : Val := ⟨.lam (.letpair (.var 0) cBody), .lam⟩

/-- The body of the clause that cancels and then resumes, under its `let`. -/
def crBody : Expr := bindE (cancelE (.var 0)) (resumeE (.var 1) .unit)

/-- The clause that cancels and then resumes, at our instance. -/
def cancelResumeV : Val := ⟨.lam (.letpair (.var 0) crBody), .lam⟩

theorem cancel_chain_cancel {n : UInt32} (hn : n ≠ 0) :
    HeadChain (ℍ := ℍ) (cancelE (rκ n cancelV).1) (cancelRun n cancelV) .unit := by
  refine .cons (K := .hole) (fun μ => Head.beta μ (kBody n cancelV) (Val.inj₂ Val.unit)) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.case₂ μ Val.unit _ _) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.seq μ _) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.cancel μ [n] ((rHK n cancelV).comp rK)
    (rCancelK_catches hn cancelV)) rfl ?_
  exact .nil

theorem cancel_chain_cancelResume {n : UInt32} (hn : n ≠ 0) :
    HeadChain (ℍ := ℍ) (cancelE (rκ n cancelResumeV).1) (cancelRun n cancelResumeV) .unit := by
  refine .cons (K := .hole) (fun μ => Head.beta μ (kBody n cancelResumeV) (Val.inj₂ Val.unit))
    rfl ?_
  refine .cons (K := .hole) (fun μ => Head.case₂ μ Val.unit _ _) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.seq μ _) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.cancel μ [n] ((rHK n cancelResumeV).comp rK)
    (rCancelK_catches hn cancelResumeV)) rfl ?_
  exact .nil

theorem resume_chain_cancelResume (n : UInt32) (w : Val) :
    HeadChain (ℍ := ℍ) (resumeE (rκ n cancelResumeV).1 w.1) (resumeRun n cancelResumeV w) rTt := by
  refine .cons (K := .hole) (fun μ => Head.beta μ
    (.app (.app ((rκ n cancelResumeV).1.shift 1 0) (.inj₁ .unit)) (.var 0)) w) rfl ?_
  refine .cons (K := .appL .hole w) (fun μ => Head.beta μ (kBody n cancelResumeV)
    (Val.inj₁ Val.unit)) rfl ?_
  refine .cons (K := .appL .hole w) (fun μ => Head.case₁ μ Val.unit _ _) rfl ?_
  refine .cons (K := .appL .hole w) (fun μ => Head.seq μ _) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (hndE (rH n cancelResumeV) (rK.plug (.var 0))) w)
    rfl ?_
  refine .cons (K := rHK n cancelResumeV) (fun μ => Head.beta μ rTt w) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.hret μ n ⟨rRet, .lam⟩ _ ⟨rTt, .inj₂ .unit⟩) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (.var 0) ⟨rTt, .inj₂ .unit⟩) rfl ?_
  exact .nil

/-! ### R1: `κ` dropped -/

/-- `op (v, k) ⇒ return ff`, at our instance. -/
def dropV : Val := ⟨.lam (.letpair (.var 0) (.inj₁ .unit)), .lam⟩

/-- R1's run: the catch, the clause's β, and its `let`. -/
def r1Run (n : UInt32) : List (Kont × Expr × Expr) :=
  [(.hole, rProg n dropV, .app dropV.1 (.pair .unit (rκ n dropV).1)),
   (.hole, .app dropV.1 (.pair .unit (rκ n dropV).1), .letpair (.pair .unit (rκ n dropV).1) (.inj₁ .unit)),
   (.hole, .letpair (.pair .unit (rκ n dropV).1) (.inj₁ .unit), .inj₁ .unit)]

theorem r1_chain (n : UInt32) : HeadChain (ℍ := ℍ) (rProg n dropV) (r1Run n) (.inj₁ .unit) := by
  refine .cons (K := .hole) (fun μ => head_rCatch μ n dropV) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ _ (Val.pair Val.unit (rκ n dropV))) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.letpair μ Val.unit (rκ n dropV) (.inj₁ .unit)) rfl ?_
  exact .nil

/-! ### Shapes at evaluation positions -/

theorem not_resume_of_shape {t k : Expr} (h : (evalSubs t).any resumeShape = false) :
    ¬ ∃ (K₀ : Kont) (w : Expr), t = K₀.plug (resumeE k w) := by
  rintro ⟨K₀, w, rfl⟩
  rw [any_evalSubs_plug K₀ (resumeShape_resumeE k w)] at h
  exact absurd h (by decide)

theorem not_cancel_of_shape {t : Expr} {n : UInt32} {H : Val} {K : Kont}
    (h : (evalSubs t).any kappaCancelShape = false) :
    ¬ ∃ K₀ : Kont, t = K₀.plug (cancelE (kappa n H K)) := by
  rintro ⟨K₀, rfl⟩
  rw [any_evalSubs_plug K₀ (kappaCancelShape_cancelE n H K)] at h
  exact absurd h (by decide)

theorem not_catch_of_shape {t : Expr} (h : catchShape t = false) :
    ¬ ∃ (K₀ : Kont) (n : UInt32) (r : Expr) (cs : List Expr) (K : Kont) (p : Expr),
      t = K₀.plug ((handleK n r cs).plug (K.plug (performE p))) := by
  rintro ⟨K₀, n, r, cs, K, p, rfl⟩
  rw [catchShape_plug] at h
  exact absurd h (by decide)

/-! ### Counts along a computed run -/

section Counts
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- The configurations before the steps of a chain's path are the chain's terms but its last. -/
theorem take_chainPath (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) (μ : Heap) (s : R.St) (e : Expr)
    (q : List (Kont × Expr × Expr)) :
    ((((μ, e), s) : (ourInst (ℍ := ℍ) RF Ξ J).RConf R) ::
        (chainPath (ℍ := ℍ) R μ s q).map Prod.snd).take q.length =
      ((chainTerms e q).take q.length).map (fun t => ((μ, t), s)) := by
  simp only [chainPath, chainTerms, List.map_cons, List.map_map, List.map_take]
  rfl

/-- A count of S6 along a chain's path, as a count over the chain's terms. -/
theorem countP_chain (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) (μ : Heap) (s : R.St) (e : Expr)
    (q : List (Kont × Expr × Expr)) (p : ℕ → Bool) (P : Expr → Bool)
    (h : ∀ j < q.length, p j = P ((ourInst (ℍ := ℍ) RF Ξ J).term
      ((ourInst (ℍ := ℍ) RF Ξ J).cfgAt ((μ, e), s) (chainPath (ℍ := ℍ) R μ s q) j).1)) :
    (List.range q.length).countP p = ((chainTerms e q).take q.length).countP P := by
  have hl : (chainPath (ℍ := ℍ) R μ s q).length = q.length := by simp [chainPath]
  have := A.EffectSystem.countP_range_take (S := ourInst (ℍ := ℍ) RF Ξ J) ((μ, e), s)
    (chainPath (ℍ := ℍ) R μ s q) p (fun c => P ((ourInst (ℍ := ℍ) RF Ξ J).term c.1))
    (by rw [hl]; exact h)
  rw [hl, take_chainPath] at this
  exact this.trans List.countP_map

end Counts

/-! ### The pure row, answered -/

section Pure
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- A row form whose pure row reads as the empty row: the runner that answers nothing answers it. -/
theorem answers_unit_of (hU : ∀ η, RF.den Ξ (RF.alg Ξ).unit η = [])
    (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) :
    (ourInst (ℍ := ℍ) RF Ξ J).Answers R (RF.alg Ξ).unit := by
  intro l i h
  obtain ⟨-, h⟩ := h
  have := h (fun _ => [])
  rw [hU] at this
  simp [Targets.Row.Has, Row.find] at this

/-- `bool` is a data type. -/
theorem dataTy_bool : (ourInst (ℍ := ℍ) RF Ξ J).DataTy (ourInst (ℍ := ℍ) RF Ξ J).bool :=
  .sum .unit .unit

end Pure

/-! ### The catch, at our instance -/

section Catch
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- The A-handler of `withCl l cl`. -/
def rHA (cl : OVal) : OVal × List OVal := (⟨rRet, .lam⟩, [cl])

theorem withCl_eq (l : (RF.alg Ξ).Lab) (cl : Val) :
    (ourInst (ℍ := ℍ) RF Ξ J).withCl l (OVal.ofVal cl) = rProg (RF.name Ξ l) cl := rfl

/-- The A-continuation of `withCl l cl`'s catch is `rκ`. -/
theorem capture_eq (l : (RF.alg Ξ).Lab) (cl : Val) :
    ((ourInst (ℍ := ℍ) RF Ξ J).capture l (rHA (OVal.ofVal cl)) rK).1 = (rκ (RF.name Ξ l) cl).1 := by
  show captureE (RF.name Ξ l) rRet [cl.1] rK = kappa (RF.name Ξ l) (rH (RF.name Ξ l) cl) rK
  rw [captureE_of_val rK (rH (RF.name Ξ l) cl).2]
  rfl

/-- **`withCl l cl` catches its continuation at its first step**, at the class of `l`'s first
operation. -/
theorem catchAt_r (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) (s : R.St) (l : (RF.alg Ξ).Lab) (cl : Val)
    (q : List (Kont × Expr × Expr)) (hq : 0 < q.length) {o : A.OpSig OVTy}
    (ho : ((ourInst (ℍ := ℍ) RF Ξ J).sig l)[0]? = some o) (hk : o.cls ≠ .abortive) :
    (ourInst (ℍ := ℍ) RF Ξ J).CatchAt (((Adequacy.emptyMem, rProg (RF.name Ξ l) cl), s) :
        (ourInst (ℍ := ℍ) RF Ξ J).RConf R) (chainPath (ℍ := ℍ) R Adequacy.emptyMem s q) 0
      ((ourInst (ℍ := ℍ) RF Ξ J).capture l (rHA (OVal.ofVal cl)) rK) o.cls := by
  refine ⟨by simpa [chainPath] using hq, .hole, l, ⟨rRet, .lam⟩, [OVal.ofVal cl], rK, 0,
    ⟨.unit, .unit⟩, o, rfl, rfl, ho, rfl, hk, rfl⟩

end Catch

/-! ### The counts of S6 along a chain -/

section ChainCounts
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

theorem length_chainPath (R : (𝕊).Runner) (μ : Heap) (s : R.St) (q : List (Kont × Expr × Expr)) :
    (chainPath (ℍ := ℍ) R μ s q).length = q.length := by
  simp [chainPath]

open Classical in
theorem resumes_chain (R : (𝕊).Runner) (μ : Heap) (s : R.St) (e : Expr)
    (q : List (Kont × Expr × Expr)) (κ : OVal) :
    (𝕊).resumes ((μ, e), s) (chainPath (ℍ := ℍ) R μ s q) κ =
      ((chainTerms e q).take q.length).countP
        (fun t => decide (∃ (K₀ : Kont) (w : OVal), t = K₀.plug (resumeE κ.1 w.1))) := by
  unfold A.EffectSystem.resumes
  rw [length_chainPath]
  refine countP_chain R μ s e q _ _ fun j hj => ?_
  refine decide_eq_decide.2 ⟨fun h => h.2, fun h => ⟨by rw [length_chainPath]; exact hj, h⟩⟩

open Classical in
theorem cancels_chain (R : (𝕊).Runner) (μ : Heap) (s : R.St) (e : Expr)
    (q : List (Kont × Expr × Expr)) (κ : OVal) :
    (𝕊).cancels ((μ, e), s) (chainPath (ℍ := ℍ) R μ s q) κ =
      ((chainTerms e q).take q.length).countP
        (fun t => decide (∃ K₀ : Kont, t = K₀.plug (cancelE κ.1))) := by
  unfold A.EffectSystem.cancels
  rw [length_chainPath]
  refine countP_chain R μ s e q _ _ fun j hj => ?_
  refine decide_eq_decide.2 ⟨fun h => h.2, fun h => ⟨by rw [length_chainPath]; exact hj, h⟩⟩

/-- A catch at a configuration: a handler at an evaluation position whose body holds a `perform`
of its name at one, the continuation `κ` the catch would hand its clause, and the class `k`. -/
def CatchTerm (t : Expr) (κ : OVal) (k : A.OpClass) : Prop :=
  ∃ (K₀ : Kont) (l : (RF.alg Ξ).Lab) (r : OVal) (cs : List OVal) (K : Kont) (i : ℕ) (v : OVal)
    (o : A.OpSig OVTy),
    t = K₀.plug ((handleK (RF.name Ξ l) r.1 (cs.map Subtype.val)).plug
      (K.plug (performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)))) ∧
    K.HasHnd (RF.name Ξ l) = false ∧ ((𝕊).sig l)[i]? = some o ∧ o.cls = k ∧ k ≠ .abortive ∧
    κ = (𝕊).capture l (r, cs) K

open Classical in
theorem caught_chain (R : (𝕊).Runner) (μ : Heap) (s : R.St) (e : Expr)
    (q : List (Kont × Expr × Expr)) (κ : OVal) (k : A.OpClass) :
    (List.range (chainPath (ℍ := ℍ) R μ s q).length).countP
        (fun j => decide ((𝕊).CatchAt ((μ, e), s) (chainPath (ℍ := ℍ) R μ s q) j κ k)) =
      ((chainTerms e q).take q.length).countP
        (fun t => decide (CatchTerm (RF := RF) (Ξ := Ξ) (J := J) t κ k)) := by
  rw [length_chainPath]
  refine countP_chain R μ s e q _ _ fun j hj => ?_
  refine decide_eq_decide.2 ⟨fun h => h.2, fun h => ⟨by rw [length_chainPath]; exact hj, h⟩⟩

theorem not_catchTerm_of_shape {t : Expr} (h : catchShape t = false) (κ : OVal) (k : A.OpClass) :
    ¬ CatchTerm (RF := RF) (Ξ := Ξ) (J := J) t κ k := by
  rintro ⟨K₀, l, r, cs, K, i, v, o, rfl, -⟩
  exact not_catch_of_shape h ⟨K₀, _, _, _, K, _, rfl⟩

end ChainCounts

/-! ### R1 -/

section R1
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- No configuration of R1's run resumes or cancels a continuation. -/
theorem r1_shapes (n : UInt32) :
    ((chainTerms (rProg n dropV) (r1Run n)).take 3).all
      (fun t => !(evalSubs t).any resumeShape && !(evalSubs t).any kappaCancelShape) = true := rfl

/-- **R1 breaks S6.**  A typing system that types R1 at `F 0 bool`, at a label whose first
operation resumes (linear or affine), fails S6: R1's run completes at `ff`, catching `κ` once and
using it never. -/
theorem not_contUse_of_der_R1 (hU : ∀ η, RF.den Ξ (RF.alg Ξ).unit η = [])
    (l : (RF.alg Ξ).Lab) {o : A.OpSig OVTy} (ho : ((𝕊).sig l)[0]? = some o) (hk : o.cls ≠ .abortive)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).dropCl) ((𝕊).F (RF.alg Ξ).unit (𝕊).bool)) : ¬ (𝕊).ContUse := by
  intro hC
  have hchain := r1_chain (ℍ := ℍ) (RF.name Ξ l)
  have hpath := rpath_chainPath (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (μ := Adequacy.emptyMem)
    (s := (𝕊).R₀.s₀) hchain
  obtain ⟨-, -, h3⟩ := hC (𝕊).R₀ r₀_respects _ _ _ (answers_unit_of hU (𝕊).R₀) h _ hpath
    ((𝕊).capture l (rHA (OVal.ofVal dropV)) rK)
  have hlast := lastC_chainPath (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (μ := Adequacy.emptyMem)
    (s := (𝕊).R₀.s₀) hchain
  have hu := h3 dataTy_bool (by
    show (𝕊).IsVal ((𝕊).lastC ((Adequacy.emptyMem, rProg (RF.name Ξ l) dropV), (𝕊).R₀.s₀) _).1
    rw [hlast]
    exact isVal_val Adequacy.emptyMem (Val.inj₁ Val.unit))
  have hu' : (𝕊).resumes ((Adequacy.emptyMem, rProg (RF.name Ξ l) dropV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r1Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal dropV)) rK) +
      (𝕊).cancels ((Adequacy.emptyMem, rProg (RF.name Ξ l) dropV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r1Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal dropV)) rK) =
      (𝕊).caught ((Adequacy.emptyMem, rProg (RF.name Ξ l) dropV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r1Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal dropV)) rK) := hu
  have hshape := List.all_eq_true.1 (r1_shapes (RF.name Ξ l))
  have e1 : (𝕊).resumes ((Adequacy.emptyMem, rProg (RF.name Ξ l) dropV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r1Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal dropV)) rK) = 0 := by
    refine (resumes_chain (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ _ _ _ _ _).trans
      (List.countP_eq_zero.2 fun t ht => ?_)
    have := hshape t ht
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    simpa using fun K₀ (w : OVal) hw => not_resume_of_shape this.1 ⟨K₀, w.1, hw⟩
  have e2 : (𝕊).cancels ((Adequacy.emptyMem, rProg (RF.name Ξ l) dropV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r1Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal dropV)) rK) = 0 := by
    refine (cancels_chain (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ _ _ _ _ _).trans
      (List.countP_eq_zero.2 fun t ht => ?_)
    have := hshape t ht
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
    simp only [decide_eq_true_eq, not_exists]
    intro K₀ hK₀
    refine not_cancel_of_shape (n := RF.name Ξ l) (H := rH (RF.name Ξ l) dropV) (K := rK)
      this.2 ⟨K₀, ?_⟩
    rw [hK₀, capture_eq]
    rfl
  have e3 := A.EffectSystem.caught_pos (catchAt_r (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (𝕊).R₀.s₀ l
    dropV (r1Run (RF.name Ξ l)) (by simp [r1Run]) ho hk)
  rw [e1, e2] at hu'
  omega

end R1

/-! ### One catch, at one class -/

/-- A handler applied at a term. -/
def hndAppShape : Expr → Bool
  | .app (.app (.prim .hnd) _) _ => true
  | _ => false

/-- `perform p`. -/
def performAppShape : Expr → Bool
  | .app (.prim .perform) _ => true
  | _ => false

theorem two_le_countP {α : Type} (p : α → Bool) :
    ∀ (l : List α) (i j : ℕ) (hij : i < j) (hj : j < l.length), p (l[i]'(by omega)) = true →
      p l[j] = true → 2 ≤ l.countP p
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | a :: l, 0, j + 1, _, hj, hi, hj' => by
      have h1 : 0 < l.countP p :=
        List.countP_pos_iff.2 ⟨l[j]'(by simpa using hj), List.getElem_mem _, hj'⟩
      simp only [List.getElem_cons_zero] at hi
      rw [List.countP_cons, if_pos hi]
      omega
  | a :: l, i + 1, j + 1, hij, hj, hi, hj' => by
      have := two_le_countP p l i j (by omega) (by simpa using hj) hi hj'
      rw [List.countP_cons]
      omega

section Unique
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- The only handler at an evaluation position of `withCl`'s start is its own, and the only
`perform` its body. -/
theorem rProg_subs (n : UInt32) (b : Expr) :
    ((evalSubs (rProg n ⟨.lam b, .lam⟩)).tail.all fun x => !hndAppShape x) = true ∧
    ∀ x ∈ evalSubs (rK.plug (performE (opArgE n 0 .unit))), performAppShape x = true →
      x = performE (opArgE n 0 .unit) := by
  refine ⟨rfl, fun x hx hs => ?_⟩
  simp [rK, bindK, rTt, Kont.plug, performE, opArgE, evalSubs, Val.i32] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | simp [performAppShape] at hs

/-- **`withCl l cl`'s start catches at one class**: its handler's, at `l`'s first operation. -/
theorem catchTerm_rProg {l : (RF.alg Ξ).Lab} (hlen : (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32)
    (b : Expr) {κ : OVal} {k : A.OpClass}
    (h : CatchTerm (RF := RF) (Ξ := Ξ) (J := J) (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) κ k) :
    ∃ o, ((𝕊).sig l)[0]? = some o ∧ o.cls = k := by
  obtain ⟨K₀, l', r, cs, K, i, v, o, he, -, ho, hk, -, -⟩ := h
  obtain ⟨hH, hP⟩ := rProg_subs (RF.name Ξ l) b
  -- the handler is the start's own
  have hmem := mem_evalSubs_plug K₀ ((handleK (RF.name Ξ l') r.1 (cs.map Subtype.val)).plug
    (K.plug (performE (opArgE (RF.name Ξ l') (UInt32.ofNat i) v.1))))
  rw [← he] at hmem
  have hX : (handleK (RF.name Ξ l') r.1 (cs.map Subtype.val)).plug
      (K.plug (performE (opArgE (RF.name Ξ l') (UInt32.ofNat i) v.1))) =
      rProg (RF.name Ξ l) ⟨.lam b, .lam⟩ := by
    have hcons : evalSubs (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) =
        rProg (RF.name Ξ l) ⟨.lam b, .lam⟩ :: (evalSubs (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩)).tail :=
      rfl
    rw [hcons, List.mem_cons] at hmem
    rcases hmem with hx | hx
    · exact hx
    · have := List.all_eq_true.1 hH _ hx
      simp [handleK, Kont.plug, hndAppShape] at this
  simp only [handleK, rProg, Kont.plug, hndValE, Expr.app.injEq, Expr.pair.injEq, Expr.prim.injEq,
    Prim.lit.injEq, IntLit.i32.injEq, true_and] at hX
  obtain ⟨⟨hn, -⟩, hY⟩ := hX
  -- the `perform` is the start's own
  have hmem' := mem_evalSubs_plug K (performE (opArgE (RF.name Ξ l') (UInt32.ofNat i) v.1))
  have hY' : K.plug (performE (opArgE (RF.name Ξ l') (UInt32.ofNat i) v.1)) =
      rK.plug (performE (opArgE (RF.name Ξ l) 0 .unit)) := hY
  rw [hY'] at hmem'
  have := hP _ hmem' rfl
  simp only [performE, Expr.val, Val.prim, opArgE, Expr.app.injEq, Expr.pair.injEq, Val.i32,
    Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq, true_and] at this
  obtain ⟨-, hi, -⟩ := this
  -- the operation is `l`'s first
  have hsig : (𝕊).sig l' = (𝕊).sig l := by
    show (Ξ (RF.name Ξ l')).map _ = (Ξ (RF.name Ξ l)).map _
    rw [hn]
  rw [hsig] at ho
  have hlt := idx_lt (RF := RF) (Ξ := Ξ) (J := J) hlen ho
  have hi0 : i = 0 := by
    have := congrArg UInt32.toNat hi
    rwa [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at this
  subst hi0
  exact ⟨o, ho, hk⟩

end Unique

/-! ### At most one catch -/

section Caught
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

open Classical in
/-- The catches of `κ` at the class `k` along a run of `withCl l cl` that catches nothing after
its start: one if the start catches `κ` at `k`, none otherwise. -/
theorem caughtK_chain (R : (𝕊).Runner) (s : R.St) (l : (RF.alg Ξ).Lab) (b : Expr)
    (q : List (Kont × Expr × Expr)) (hq : 0 < q.length)
    (hrest : ∀ t ∈ ((chainTerms (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) q).take q.length).tail,
      catchShape t = false) (κ : OVal) (k : A.OpClass) :
    (List.range (chainPath (ℍ := ℍ) R Adequacy.emptyMem s q).length).countP
        (fun j => decide ((𝕊).CatchAt ((Adequacy.emptyMem, rProg (RF.name Ξ l) ⟨.lam b, .lam⟩), s)
          (chainPath (ℍ := ℍ) R Adequacy.emptyMem s q) j κ k)) =
      if CatchTerm (RF := RF) (Ξ := Ξ) (J := J) (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) κ k then 1
      else 0 := by
  rw [caught_chain]
  obtain ⟨m, hm⟩ : ∃ m, q.length = m + 1 := ⟨q.length - 1, by omega⟩
  have htake : (chainTerms (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) q).take q.length =
      rProg (RF.name Ξ l) ⟨.lam b, .lam⟩ ::
        ((chainTerms (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) q).take q.length).tail := by
    rw [hm]; rfl
  rw [htake, List.countP_cons, List.countP_eq_zero.2]
  · simp
  · intro t ht
    simpa using not_catchTerm_of_shape (RF := RF) (Ξ := Ξ) (J := J) (hrest t ht) κ k

open Classical in
/-- **At most one catch**: a run of `withCl l cl` that catches nothing after its start catches `κ`
at most once, its start catching at one class. -/
theorem caught_le_one (R : (𝕊).Runner) (s : R.St) {l : (RF.alg Ξ).Lab}
    (hlen : (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) (b : Expr)
    (q : List (Kont × Expr × Expr)) (hq : 0 < q.length)
    (hrest : ∀ t ∈ ((chainTerms (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) q).take q.length).tail,
      catchShape t = false) (κ : OVal) :
    (𝕊).caught ((Adequacy.emptyMem, rProg (RF.name Ξ l) ⟨.lam b, .lam⟩), s)
      (chainPath (ℍ := ℍ) R Adequacy.emptyMem s q) κ ≤ 1 := by
  have hL := caughtK_chain R s l b q hq hrest κ .linear
  have hA := caughtK_chain R s l b q hq hrest κ .affine
  have e : (𝕊).caught ((Adequacy.emptyMem, rProg (RF.name Ξ l) ⟨.lam b, .lam⟩), s)
      (chainPath (ℍ := ℍ) R Adequacy.emptyMem s q) κ =
      (if CatchTerm (RF := RF) (Ξ := Ξ) (J := J) (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) κ .linear
        then 1 else 0) +
      (if CatchTerm (RF := RF) (Ξ := Ξ) (J := J) (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) κ .affine
        then 1 else 0) := by
    rw [← hL, ← hA]; rfl
  rw [e]
  by_cases h₁ : CatchTerm (RF := RF) (Ξ := Ξ) (J := J) (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) κ .linear
  · by_cases h₂ : CatchTerm (RF := RF) (Ξ := Ξ) (J := J) (rProg (RF.name Ξ l) ⟨.lam b, .lam⟩) κ
        .affine
    · obtain ⟨o₁, ho₁, hk₁⟩ := catchTerm_rProg hlen b h₁
      obtain ⟨o₂, ho₂, hk₂⟩ := catchTerm_rProg hlen b h₂
      rw [ho₁] at ho₂
      cases ho₂
      rw [hk₁] at hk₂
      cases hk₂
    · simp [h₁, h₂]
  · rw [if_neg h₁]
    split <;> simp

end Caught

/-! ### R2: `κ` resumed twice -/

section R2
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- The second resume, under the first's bind. -/
def tw2 (n : UInt32) : Expr := resumeE (rκ n twiceV).1 .unit

/-- R2's run: the catch; the clause's β and `let`; the first resume, under `□ to _. resume κ ()`;
the bind; the second resume. -/
def r2Run (n : UInt32) : List (Kont × Expr × Expr) :=
  (.hole, rProg n twiceV, .app twiceV.1 (.pair .unit (rκ n twiceV).1)) ::
  (.hole, .app twiceV.1 (.pair .unit (rκ n twiceV).1), .letpair (.pair .unit (rκ n twiceV).1) twBody) ::
  (.hole, .letpair (.pair .unit (rκ n twiceV).1) twBody, (bindK (tw2 n)).plug (tw2 n)) ::
  (plugRun (bindK (tw2 n)) (resumeRun n twiceV Val.unit) ++
    ((.hole, (bindK (tw2 n)).plug rTt, tw2 n) :: resumeRun n twiceV Val.unit))

theorem r2_chain (n : UInt32) : HeadChain (ℍ := ℍ) (rProg n twiceV) (r2Run n) rTt := by
  refine .cons (K := .hole) (fun μ => head_rCatch μ n twiceV) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (.letpair (.var 0) twBody)
    (Val.pair Val.unit (rκ n twiceV))) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.letpair μ Val.unit (rκ n twiceV) twBody) rfl ?_
  refine HeadChain.append (HeadChain.plug (bindK (tw2 n)) (resume_chain_twice n Val.unit)) ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (tw2 n) ⟨rTt, .inj₂ .unit⟩) rfl ?_
  exact resume_chain_twice n Val.unit

theorem r2_length (n : UInt32) : (r2Run n).length = 20 := rfl

/-- No configuration of R2's run catches, but the first. -/
theorem r2_noCatch (n : UInt32) :
    (((chainTerms (rProg n twiceV) (r2Run n)).take 20).tail.all fun t => !catchShape t) = true :=
  rfl

theorem r2_at3 (n : UInt32) :
    ((chainTerms (rProg n twiceV) (r2Run n)).take 20)[3]? =
      some ((bindK (tw2 n)).plug (resumeE (rκ n twiceV).1 .unit)) := rfl

theorem r2_at12 (n : UInt32) :
    ((chainTerms (rProg n twiceV) (r2Run n)).take 20)[12]? =
      some (Kont.hole.plug (resumeE (rκ n twiceV).1 .unit)) := rfl

/-- **R2 breaks S6.**  A typing system that types R2 at `F 0 bool` fails S6: R2's run resumes
`κ` twice, and catches it at most once. -/
theorem not_contUse_of_der_R2 (hU : ∀ η, RF.den Ξ (RF.alg Ξ).unit η = [])
    (l : (RF.alg Ξ).Lab) (hlen : (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).twiceCl) ((𝕊).F (RF.alg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUse := by
  intro hC
  have hchain := r2_chain (ℍ := ℍ) (RF.name Ξ l)
  have hpath := rpath_chainPath (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (μ := Adequacy.emptyMem)
    (s := (𝕊).R₀.s₀) hchain
  obtain ⟨h1, -, -⟩ := hC (𝕊).R₀ r₀_respects _ _ _ (answers_unit_of hU (𝕊).R₀) h _ hpath
    ((𝕊).capture l (rHA (OVal.ofVal twiceV)) rK)
  have h1' : (𝕊).resumes ((Adequacy.emptyMem, rProg (RF.name Ξ l) twiceV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r2Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal twiceV)) rK) +
      (𝕊).cancels ((Adequacy.emptyMem, rProg (RF.name Ξ l) twiceV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r2Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal twiceV)) rK) ≤
      (𝕊).caught ((Adequacy.emptyMem, rProg (RF.name Ξ l) twiceV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r2Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal twiceV)) rK) := h1
  have hres : 2 ≤ (𝕊).resumes ((Adequacy.emptyMem, rProg (RF.name Ξ l) twiceV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r2Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal twiceV)) rK) := by
    refine le_of_le_of_eq ?_ (resumes_chain (RF := RF) (Ξ := Ξ) (J := J) _ _ _ _ _ _).symm
    rw [r2_length]
    refine two_le_countP _ _ 3 12 (by omega) (by simp [chainTerms, r2_length]) ?_ ?_
    · rw [(List.getElem_eq_iff _).2 (r2_at3 (RF.name Ξ l))]
      simp only [decide_eq_true_eq]
      exact ⟨bindK (tw2 (RF.name Ξ l)), (𝕊).unitV, by rw [capture_eq]; rfl⟩
    · rw [(List.getElem_eq_iff _).2 (r2_at12 (RF.name Ξ l))]
      simp only [decide_eq_true_eq]
      exact ⟨.hole, (𝕊).unitV, by rw [capture_eq]; rfl⟩
  have hrest : ∀ t ∈ ((chainTerms (rProg (RF.name Ξ l) twiceV) (r2Run (RF.name Ξ l))).take
      (r2Run (RF.name Ξ l)).length).tail, catchShape t = false := by
    rw [r2_length]
    intro t ht
    simpa using List.all_eq_true.1 (r2_noCatch (RF.name Ξ l)) t ht
  have hcaught : (𝕊).caught ((Adequacy.emptyMem, rProg (RF.name Ξ l) twiceV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r2Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal twiceV)) rK) ≤ 1 :=
    caught_le_one (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (𝕊).R₀.s₀ hlen
      (.letpair (.var 0) twBody) (r2Run (RF.name Ξ l)) (by rw [r2_length]; omega) hrest _
  omega

end R2

/-! ### R3: a linear `κ` cancelled -/

section R3
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- `ff`. -/
def rFf : Expr := .inj₁ .unit

/-- R3's run: the catch; the clause's β and `let`; the cancel, under `□ to _. return ff`; the
bind. -/
def r3Run (n : UInt32) : List (Kont × Expr × Expr) :=
  (.hole, rProg n cancelV, .app cancelV.1 (.pair .unit (rκ n cancelV).1)) ::
  (.hole, .app cancelV.1 (.pair .unit (rκ n cancelV).1), .letpair (.pair .unit (rκ n cancelV).1) cBody) ::
  (.hole, .letpair (.pair .unit (rκ n cancelV).1) cBody, (bindK rFf).plug (cancelE (rκ n cancelV).1)) ::
  (plugRun (bindK rFf) (cancelRun n cancelV) ++ [(.hole, (bindK rFf).plug .unit, rFf)])

theorem r3_chain {n : UInt32} (hn : n ≠ 0) : HeadChain (ℍ := ℍ) (rProg n cancelV) (r3Run n) rFf := by
  refine .cons (K := .hole) (fun μ => head_rCatch μ n cancelV) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (.letpair (.var 0) cBody)
    (Val.pair Val.unit (rκ n cancelV))) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.letpair μ Val.unit (rκ n cancelV) cBody) rfl ?_
  refine HeadChain.append (HeadChain.plug (bindK rFf) (cancel_chain_cancel hn)) ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ rFf Val.unit) rfl ?_
  exact .nil

theorem r3_length (n : UInt32) : (r3Run n).length = 8 := rfl

theorem r3_noCatch (n : UInt32) :
    (((chainTerms (rProg n cancelV) (r3Run n)).take 8).tail.all fun t => !catchShape t) = true :=
  rfl

theorem r3_at3 (n : UInt32) :
    ((chainTerms (rProg n cancelV) (r3Run n)).take 8)[3]? =
      some ((bindK rFf).plug (cancelE (rκ n cancelV).1)) := rfl

/-- **R3 breaks S6.**  A typing system that types R3 at `F 0 bool`, at a label whose first
operation is linear, fails S6: R3's run cancels a `κ` that no affine catch made. -/
theorem not_contUse_of_der_R3 (hU : ∀ η, RF.den Ξ (RF.alg Ξ).unit η = [])
    (l : (RF.alg Ξ).Lab) (hn : RF.name Ξ l ≠ 0) (hlen : (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32)
    {o : A.OpSig OVTy} (ho : ((𝕊).sig l)[0]? = some o) (hlin : o.cls = .linear)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).cancelCl) ((𝕊).F (RF.alg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUse := by
  intro hC
  have hchain := r3_chain (ℍ := ℍ) hn
  have hpath := rpath_chainPath (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (μ := Adequacy.emptyMem)
    (s := (𝕊).R₀.s₀) hchain
  obtain ⟨-, h2, -⟩ := hC (𝕊).R₀ r₀_respects _ _ _ (answers_unit_of hU (𝕊).R₀) h _ hpath
    ((𝕊).capture l (rHA (OVal.ofVal cancelV)) rK)
  have h2' : (𝕊).cancels ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r3Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal cancelV)) rK) ≤
      (𝕊).caughtAff ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r3Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal cancelV)) rK) := h2
  have hcan : 0 < (𝕊).cancels ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r3Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal cancelV)) rK) := by
    refine lt_of_lt_of_eq ?_ (cancels_chain (RF := RF) (Ξ := Ξ) (J := J) _ _ _ _ _ _).symm
    rw [r3_length]
    refine List.countP_pos_iff.2 ⟨_, List.mem_of_getElem? (r3_at3 (RF.name Ξ l)), ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨bindK rFf, by rw [capture_eq]; try rfl⟩
  have hrest : ∀ t ∈ ((chainTerms (rProg (RF.name Ξ l) cancelV) (r3Run (RF.name Ξ l))).take
      (r3Run (RF.name Ξ l)).length).tail, catchShape t = false := by
    rw [r3_length]
    intro t ht
    simpa using List.all_eq_true.1 (r3_noCatch (RF.name Ξ l)) t ht
  have haff := caughtK_chain (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (𝕊).R₀.s₀ l
    (.letpair (.var 0) cBody) (r3Run (RF.name Ξ l)) (by rw [r3_length]; omega) hrest
    ((𝕊).capture l (rHA (OVal.ofVal cancelV)) rK) .affine
  rw [if_neg] at haff
  · have : (𝕊).caughtAff ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r3Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal cancelV)) rK) = 0 := haff
    omega
  · intro hct
    obtain ⟨o', ho', hk'⟩ := catchTerm_rProg (RF := RF) (Ξ := Ξ) (J := J) hlen _ hct
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    rw [hlin] at hk'
    cases hk'

end R3

/-! ### R4: `κ` resumed after its cancel -/

section R4
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- The resume after the cancel, under the cancel's bind. -/
def cr2 (n : UInt32) : Expr := resumeE (rκ n cancelResumeV).1 .unit

/-- R4's run: the catch; the clause's β and `let`; the cancel, under `□ to _. resume κ ()`; the
bind; the resume. -/
def r4Run (n : UInt32) : List (Kont × Expr × Expr) :=
  (.hole, rProg n cancelResumeV, .app cancelResumeV.1 (.pair .unit (rκ n cancelResumeV).1)) ::
  (.hole, .app cancelResumeV.1 (.pair .unit (rκ n cancelResumeV).1),
    .letpair (.pair .unit (rκ n cancelResumeV).1) crBody) ::
  (.hole, .letpair (.pair .unit (rκ n cancelResumeV).1) crBody,
    (bindK (cr2 n)).plug (cancelE (rκ n cancelResumeV).1)) ::
  (plugRun (bindK (cr2 n)) (cancelRun n cancelResumeV) ++
    ((.hole, (bindK (cr2 n)).plug .unit, cr2 n) :: resumeRun n cancelResumeV Val.unit))

theorem r4_chain {n : UInt32} (hn : n ≠ 0) :
    HeadChain (ℍ := ℍ) (rProg n cancelResumeV) (r4Run n) rTt := by
  refine .cons (K := .hole) (fun μ => head_rCatch μ n cancelResumeV) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (.letpair (.var 0) crBody)
    (Val.pair Val.unit (rκ n cancelResumeV))) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.letpair μ Val.unit (rκ n cancelResumeV) crBody) rfl ?_
  refine HeadChain.append (HeadChain.plug (bindK (cr2 n)) (cancel_chain_cancelResume hn)) ?_
  refine .cons (K := .hole) (fun μ => Head.beta μ (cr2 n) Val.unit) rfl ?_
  exact resume_chain_cancelResume n Val.unit

theorem r4_length (n : UInt32) : (r4Run n).length = 16 := rfl

theorem r4_noCatch (n : UInt32) :
    (((chainTerms (rProg n cancelResumeV) (r4Run n)).take 16).tail.all
      fun t => !catchShape t) = true := rfl

theorem r4_at3 (n : UInt32) :
    ((chainTerms (rProg n cancelResumeV) (r4Run n)).take 16)[3]? =
      some ((bindK (cr2 n)).plug (cancelE (rκ n cancelResumeV).1)) := rfl

theorem r4_at8 (n : UInt32) :
    ((chainTerms (rProg n cancelResumeV) (r4Run n)).take 16)[8]? =
      some (Kont.hole.plug (resumeE (rκ n cancelResumeV).1 .unit)) := rfl

/-- **R4 breaks S6.**  A typing system that types R4 at `F 0 bool` fails S6: R4's run cancels `κ`
and then resumes it, and catches it at most once. -/
theorem not_contUse_of_der_R4 (hU : ∀ η, RF.den Ξ (RF.alg Ξ).unit η = [])
    (l : (RF.alg Ξ).Lab) (hn : RF.name Ξ l ≠ 0) (hlen : (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).cancelResumeCl) ((𝕊).F (RF.alg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUse := by
  intro hC
  have hchain := r4_chain (ℍ := ℍ) hn
  have hpath := rpath_chainPath (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (μ := Adequacy.emptyMem)
    (s := (𝕊).R₀.s₀) hchain
  obtain ⟨h1, -, -⟩ := hC (𝕊).R₀ r₀_respects _ _ _ (answers_unit_of hU (𝕊).R₀) h _ hpath
    ((𝕊).capture l (rHA (OVal.ofVal cancelResumeV)) rK)
  have h1' : (𝕊).resumes ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelResumeV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r4Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal cancelResumeV)) rK) +
      (𝕊).cancels ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelResumeV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r4Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal cancelResumeV)) rK) ≤
      (𝕊).caught ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelResumeV), (𝕊).R₀.s₀)
        (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r4Run (RF.name Ξ l)))
        ((𝕊).capture l (rHA (OVal.ofVal cancelResumeV)) rK) := h1
  have hres : 0 < (𝕊).resumes ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelResumeV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r4Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal cancelResumeV)) rK) := by
    refine lt_of_lt_of_eq ?_ (resumes_chain (RF := RF) (Ξ := Ξ) (J := J) _ _ _ _ _ _).symm
    rw [r4_length]
    refine List.countP_pos_iff.2 ⟨_, List.mem_of_getElem? (r4_at8 (RF.name Ξ l)), ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨.hole, (𝕊).unitV, by rw [capture_eq]; rfl⟩
  have hcan : 0 < (𝕊).cancels ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelResumeV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r4Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal cancelResumeV)) rK) := by
    refine lt_of_lt_of_eq ?_ (cancels_chain (RF := RF) (Ξ := Ξ) (J := J) _ _ _ _ _ _).symm
    rw [r4_length]
    refine List.countP_pos_iff.2 ⟨_, List.mem_of_getElem? (r4_at3 (RF.name Ξ l)), ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨bindK (cr2 (RF.name Ξ l)), by rw [capture_eq]; try rfl⟩
  have hrest : ∀ t ∈ ((chainTerms (rProg (RF.name Ξ l) cancelResumeV) (r4Run (RF.name Ξ l))).take
      (r4Run (RF.name Ξ l)).length).tail, catchShape t = false := by
    rw [r4_length]
    intro t ht
    simpa using List.all_eq_true.1 (r4_noCatch (RF.name Ξ l)) t ht
  have hcaught : (𝕊).caught ((Adequacy.emptyMem, rProg (RF.name Ξ l) cancelResumeV), (𝕊).R₀.s₀)
      (chainPath (ℍ := ℍ) (𝕊).R₀ Adequacy.emptyMem (𝕊).R₀.s₀ (r4Run (RF.name Ξ l)))
      ((𝕊).capture l (rHA (OVal.ofVal cancelResumeV)) rK) ≤ 1 :=
    caught_le_one (RF := RF) (Ξ := Ξ) (J := J) (𝕊).R₀ (𝕊).R₀.s₀ hlen
      (.letpair (.var 0) crBody) (r4Run (RF.name Ξ l)) (by rw [r4_length]; omega) hrest _
  omega

end R4

/-! ### At the open-row form -/

section Orow
variable {Ξ : EffCtx} {J : OurTyping orowRF}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ J

theorem orow_unit (η : RowEnv) : orowRF.den Ξ (orowAlg Ξ).unit η = [] := rfl

/-- R1 at the open-row form: its labels' names are not `0`. -/
theorem not_contUse_of_der_R1_orow (l : (orowAlg Ξ).Lab) {o : A.OpSig OVTy}
    (ho : ((𝕊).sig l)[0]? = some o) (hk : o.cls ≠ .abortive)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).dropCl) ((𝕊).F (orowAlg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUse :=
  not_contUse_of_der_R1 orow_unit l ho hk h

/-- R2 at the open-row form: its signatures have at most `2³²` operations. -/
theorem not_contUse_of_der_R2_orow (l : (orowAlg Ξ).Lab)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).twiceCl) ((𝕊).F (orowAlg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUse :=
  not_contUse_of_der_R2 orow_unit l l.2.2.2 h

/-- R3 at the open-row form. -/
theorem not_contUse_of_der_R3_orow (l : (orowAlg Ξ).Lab) {o : A.OpSig OVTy}
    (ho : ((𝕊).sig l)[0]? = some o) (hlin : o.cls = .linear)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).cancelCl) ((𝕊).F (orowAlg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUse :=
  not_contUse_of_der_R3 orow_unit l l.2.1 l.2.2.2 ho hlin h

/-- R4 at the open-row form. -/
theorem not_contUse_of_der_R4_orow (l : (orowAlg Ξ).Lab)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).cancelResumeCl) ((𝕊).F (orowAlg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUse :=
  not_contUse_of_der_R4 orow_unit l l.2.1 l.2.2.2 h

end Orow

/-! ### Today's kernel types none of R1–R4 -/

/-- **Today's kernel refuses R1–R4**, at every label and type.  The reason is the handler's form:
our instance's handler is the run-time frame, whose clauses are values, and today's `[handle]`
types only clause variables (`not_der_handle_tier1Open`).  It is not the linearity of `κ`: no
inversion of the clauses' typing at `kTy` is built here. -/
theorem refuses_R_tier1Open {Ξ : EffCtx} (l : (orowAlg Ξ).Lab) (C : OCTy) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der []
        ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).withCl l (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).dropCl) C ∧
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der []
        ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).withCl l (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).twiceCl) C ∧
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der []
        ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).withCl l (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).cancelCl) C ∧
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der []
        ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).withCl l
          (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).cancelResumeCl) C :=
  ⟨not_der_handle_tier1Open [] l _ _ C, not_der_handle_tier1Open [] l _ _ C,
    not_der_handle_tier1Open [] l _ _ C, not_der_handle_tier1Open [] l _ _ C⟩

/-! ### The witnesses' premises are met -/

/-- A typing system that types R1–R4, at every name, and nothing else. -/
def JR : OurTyping orowRF :=
  ⟨fun _ _ Γ e _ => Γ = [] ∧ ∃ n, e = rProg n dropV ∨ e = rProg n twiceV ∨ e = rProg n cancelV ∨
    e = rProg n cancelResumeV, OutJ.core, fun _ η => η⟩

/-- The label of the name `5`, linear at `ΞA` (`tick`). -/
def lab5A : (orowAlg ΞA).Lab := ⟨5, by decide, by simp [ΞA], by simp [ΞA]⟩

/-- The label of the name `2`, affine at `ΞA` (`wait`). -/
def lab2A : (orowAlg ΞA).Lab := ⟨2, by decide, by simp [ΞA], by simp [ΞA]⟩

/-- **S6's teeth bite at an admissible effect context**: `JR` types each of R1–R4 at `F 0 bool`,
R1 and R4 at the affine `wait`, R3 at the linear `tick`, R2 at both; each lemma's other premises
hold there; so `JR` fails S6, four times over. -/
theorem teeth_JR_ΞA :
    AdmEff ΞA ∧
    (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab2A (ourInst (ℍ := ℍ) orowRF ΞA JR).dropCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) ∧
    (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab5A (ourInst (ℍ := ℍ) orowRF ΞA JR).twiceCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) ∧
    (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab5A (ourInst (ℍ := ℍ) orowRF ΞA JR).cancelCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) ∧
    (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab2A (ourInst (ℍ := ℍ) orowRF ΞA JR).cancelResumeCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) ∧
    ¬ (ourInst (ℍ := ℍ) orowRF ΞA JR).ContUse := by
  have d1 : (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab2A (ourInst (ℍ := ℍ) orowRF ΞA JR).dropCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) :=
    .inl ⟨[], by simp, rfl, 2, .inl rfl⟩
  refine ⟨admEff_ΞA, d1, .inl ⟨[], by simp, rfl, 5, .inr (.inl rfl)⟩,
    .inl ⟨[], by simp, rfl, 5, .inr (.inr (.inl rfl))⟩,
    .inl ⟨[], by simp, rfl, 2, .inr (.inr (.inr rfl))⟩, ?_⟩
  exact not_contUse_of_der_R1_orow lab2A (o := ⟨OVTy.ofV .unit, OVTy.ofV .unit, .affine⟩)
    (by simp [lab2A, ΞA]; rfl) (by decide) d1

end Targets.Inst

end
