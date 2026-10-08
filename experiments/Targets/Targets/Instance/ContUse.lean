import Targets.Instance.Checks
import Targets.Instance.J1Checks

/-!
# The Instance — S6's tooth at the capture cell: R1 at our machine

RESTRUCTURE §6.1 keeps four rejected programs as the witnesses that S6 bites.  Each is `withCl l cl`
(`Targets/A/Programs.lean`): a handler of `l` around `op () to _. return tt`, its clause `cl` one of

* R1, `dropCl`: `op (v, k) ⇒ return ff` — `κ` is never used;
* R2, `twiceCl`: `op (v, k) ⇒ resume k () to _. resume k ()` — `κ` is resumed twice;
* R3, `cancelCl`: `op (v, k) ⇒ cancel k to _. return ff` — `κ` is cancelled;
* R4, `cancelResumeCl`: `op (v, k) ⇒ cancel k to _. resume k ()` — `κ` is resumed after its
  cancel.

At a linear or affine operation the catch hands `κ` a fresh cell (SPEC §25): the `[op]` step, the
allocation of the cell, and `κ` at its location.  R1's run is written out from the empty memory,
the cell at location `0`.

* **R1 breaks S6** (`not_contUseEv_of_der_R1`): its run completes at `ff`, the capture event hands
  `κ` once and nothing uses it.  (Its cell is left allocated.)
* R2, R3 and R4 are read by S6 only through their complete runs (decision S6).  At a linear or
  affine operation their second use of `κ`, or the cancel of a linear `κ`, reaches a release of a
  released cell or the linear cancel branch `() ()`; those runs are not written out here, and no
  lemma of this file concludes anything about R2–R4 beyond the kernel's refusal below.

So every typing system over our machine that types R1 at `F 0 bool` fails S6.  **The witness's
premises are met**: `JR` types the four programs, and at the admissible context `ΞA` the lemma
applies to it at the affine `wait` (`teeth_JR_ΞA`).

**Today's kernel types none of R1–R4** (`refuses_R_tier1Open`), for the reason it types no A-level
handler: our instance's handler is the run-time frame, whose clauses are values
(`not_der_handle_tier1Open`).  The linearity refusal is read at the clauses' typing
(`refuses_R_clauses`, `Targets/Instance/ClauseRefusals.lean`).
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
/-- A capture event along the path counts. -/
theorem caughtEv_pos {R : S.Runner} {c₀ : S.RConf R} {q : List (S.Event × S.RConf R)} {j : ℕ}
    {κ : S.Val} {k : OpClass} (h : S.CatchEvAt c₀ q j κ k) : 0 < S.caughtEv c₀ q κ := by
  have hj : j ∈ List.range q.length := List.mem_range.2 h.1
  have hk : k ≠ .abortive := by
    obtain ⟨-, _, _, _, _, _, _, _, _, _, -, -, -, -, hk, -⟩ := h
    exact hk
  cases k with
  | abortive => exact absurd rfl hk
  | linear =>
      have : 0 < S.caughtEvLin c₀ q κ := List.countP_pos_iff.2 ⟨j, hj, by simpa using h⟩
      unfold caughtEv; omega
  | affine =>
      have : 0 < S.caughtEvAff c₀ q κ := List.countP_pos_iff.2 ⟨j, hj, by simpa using h⟩
      unfold caughtEv; omega

/-- Two paths, the second from the first's end, make a path. -/
theorem rpath_append {R : S.Runner} :
    ∀ {c : S.RConf R} {q₁ q₂ : List (S.Event × S.RConf R)}, S.RPath R c q₁ →
      S.RPath R (S.lastC c q₁) q₂ → S.RPath R c (q₁ ++ q₂)
  | _, [], _, .nil, h₂ => h₂
  | c, (ev, c') :: q₁, q₂, .cons hs h₁, h₂ => by
      rw [lastC_cons] at h₂
      exact .cons hs (rpath_append h₁ h₂)

theorem lastC_append {R : S.Runner} (c : S.RConf R) :
    ∀ (q₁ q₂ : List (S.Event × S.RConf R)), S.lastC c (q₁ ++ q₂) = S.lastC (S.lastC c q₁) q₂
  | [], _ => rfl
  | (ev, c') :: q₁, q₂ => by
      rw [List.cons_append, lastC_cons, lastC_cons]
      exact lastC_append c' q₁ q₂

end Targets.A.EffectSystem

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa clauseAt capTag kappaAt kappaC kappaCBody kappaCell freeE stuckE)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF HeadChain)

/-! ### The programs, at a name and its tags -/

/-- The return clause `return x ⇒ x`. -/
def rRet : Expr := .lam (.var 0)

/-- `tt`. -/
def rTt : Expr := .inj₂ .unit

/-- `ff`. -/
def rFf : Expr := .inj₁ .unit

/-- `□ to _. return tt`. -/
def rK : Kont := bindK rTt

/-- The handler of the name `n` with the tags of `qs` and the clause `cl`, as a value. -/
def rH (n : UInt32) (qs : List Qual) (cl : Val) : Val :=
  hndVal n (qualsVal qs) ⟨rRet, .lam⟩ ⟨clausesE [cl.1], .pair cl.2 .unit⟩

/-- `withCl` at the name `n` and the tags of `qs`:
`hnd (n, (qs, (return x ⇒ x, [cl]))) (op () to _. return tt)`. -/
def rProg (n : UInt32) (qs : List Qual) (cl : Val) : Expr :=
  (handleK n (qualsVal qs).1 rRet [cl.1]).plug (rK.plug (performE (opArgE n 0 .unit)))

theorem rProg_eq (n : UInt32) (qs : List Qual) (cl : Val) :
    rProg n qs cl = hndE (rH n qs cl) (rK.plug (performE (.val (opPayload n 0 Val.unit)))) := rfl

/-- A linear or affine qualifier's cell: affine when its cancel frees it. -/
def cellAff (q : Qual) : Bool := q == .aff

/-- The tag of a linear or affine operation is a cell's. -/
theorem kappaAt_cell {q : Qual} (hq : q ≠ .unr) (n : UInt32) (H : Val) (K : Kont) :
    kappaAt q.tag n H K = kappaCell (cellAff q) n H K := by
  cases q
  · rfl
  · rfl
  · exact absurd rfl hq

/-- `withCl`'s `κ` at its cell `ℓ`. -/
def rκ (q : Qual) (qs : List Qual) (ℓ : Loc) (n : UInt32) (cl : Val) : OVal :=
  ⟨kappaC (cellAff q) ℓ n (rH n (q :: qs) cl) rK, .lam⟩

/-! ### Steps at our instance -/

section Steps
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- A head step in a context is a step of the runner, labelled `tau` off the finaliser frames. -/
theorem rstep_head (R : (𝕊).Runner) (s : R.St) {μ μ' : Heap} (K : Kont) {a a' : Expr}
    (hh : Head (ℍ := ℍ) μ a μ' a') (hf : finHead a = false) :
    (𝕊).RStep R ((μ, K.plug a), s) .tau ((μ', K.plug a'), s) := by
  have h := A.EffectSystem.RStep.mach (R := R) (s := s) (OStep.mach (RF := RF) (Ξ := Ξ) (K := K) hh)
  rwa [labelOf_tau_of hf] at h

/-- The runner that answers nothing takes only machine steps. -/
theorem ostep_of_r₀ {c : Heap × Expr} {s : Unit} {ev : (𝕊).Event} {c' : (𝕊).RConf (𝕊).R₀}
    (h : (𝕊).RStep (𝕊).R₀ (c, s) ev c') : OStep (ℍ := ℍ) RF Ξ c ev c'.1 := by
  cases h with
  | mach h' => exact h'
  | io _ _ hans _ => exact hans.elim

/-- A release of a location the memory does not hold has no step: the release is its
configuration's only redex. -/
theorem no_ostep_free {μ : Heap} (K : Kont) {ℓ : Loc} (hμ : μ ℓ = none)
    {ev : (𝕊).Event} {c' : Heap × Expr} :
    ¬ OStep (ℍ := ℍ) RF Ξ (μ, K.plug (freeE (.val (Val.loc ℓ)))) ev c' := by
  have hnv : ¬ IsVal (freeE (.val (Val.loc ℓ))) := by
    unfold freeE; intro h; cases h
  intro h
  generalize hc : (μ, K.plug (freeE (.val (Val.loc ℓ)))) = c₀ at h
  cases h with
  | mach hh =>
      obtain ⟨h1, h2⟩ := Prod.mk.inj hc
      subst h1
      have hfree : Head (ℍ := ℍ) (μ.upd ℓ Val.unit) (freeE (.val (Val.loc ℓ)))
          ((μ.upd ℓ Val.unit).del ℓ) (.val Val.unit) :=
        Head.free _ ℓ Val.unit (by simp [BoCa.BoLo.Heap.upd])
      obtain ⟨rfl, -⟩ := plug_decomp hh K _ hfree h2
      cases hh with
      | free _ v hv => rw [hμ] at hv; cases hv
  | again =>
      obtain ⟨-, h2⟩ := Prod.mk.inj hc
      have := plug_eq_drive h2 hnv
      subst this
      simp [Kont.plug, driveE, driveMark, freeE] at h2
  | fin =>
      obtain ⟨-, h2⟩ := Prod.mk.inj hc
      have := plug_eq_drive h2 hnv
      subst this
      simp [Kont.plug, driveE, driveMark, freeE] at h2

/-- A configuration at a release of a location the memory does not hold is stuck under the runner
that answers nothing. -/
theorem stuck_free_r₀ {μ : Heap} (K : Kont) {ℓ : Loc} (hμ : μ ℓ = none) :
    ¬ (𝕊).IsVal (μ, K.plug (freeE (.val (Val.loc ℓ)))) ∧
      ∀ ev c', ¬ (𝕊).RStep (𝕊).R₀ ((μ, K.plug (freeE (.val (Val.loc ℓ)))), ()) ev c' := by
  refine ⟨fun hval => ?_, fun ev c' h => no_ostep_free K hμ (ostep_of_r₀ h)⟩
  obtain ⟨⟨v, hv⟩, _⟩ := hval
  change K.plug _ = v.1 at hv
  exact not_isOVal_prim_app (p := .free) (by decide) _ (isOVal_of_plug K (hv ▸ v.2))

/-- The configurations after the catch of a linear or affine operation, the allocation of `κ`'s
cell at `ℓ`, and `κ` at its cell: the clause applied to `((), κ)`. -/
def prefixPath (R : (𝕊).Runner) (s : R.St) (μ : Heap) (q : Qual) (qs : List Qual) (ℓ : Loc)
    (n : UInt32) (cl : Val) : List ((𝕊).Event × (𝕊).RConf R) :=
  [(.tau, ((μ, .app cl.1 (.pair .unit (kappaCell (cellAff q) n (rH n (q :: qs) cl) rK))), s)),
   (.tau, ((μ.upd ℓ Val.unit, .app cl.1 (.pair .unit
      (.app (.lam (kappaCBody (cellAff q) n (rH n (q :: qs) cl) rK)) (.loc ℓ)))), s)),
   (.tau, ((μ.upd ℓ Val.unit, .app cl.1 (.pair .unit (rκ q qs ℓ n cl).1)), s))]

/-- **The catch of a linear or affine operation** hands its clause `κ` at a fresh cell: the `[op]`
step, the allocation, and `κ`'s `β`. -/
theorem rpath_prefix (R : (𝕊).Runner) (s : R.St) {μ : Heap} {q : Qual} (qs : List Qual) {ℓ : Loc}
    (n : UInt32) (cl : Val) (hq : q ≠ .unr) (hμ : μ ℓ = none) :
    (𝕊).RPath R ((μ, rProg n (q :: qs) cl), s) (prefixPath R s μ q qs ℓ n cl) := by
  have htag : capTag (qualsVal (q :: qs)).1 (0 : UInt32).toNat = q.tag := by
    rw [show (0 : UInt32).toNat = 0 from rfl, capTag_qualsVal _ 0 (by simp)]; rfl
  have hop := Head.hop (ℍ := ℍ) μ n 0 (qualsVal (q :: qs)) ⟨rRet, .lam⟩
    ⟨clausesE [cl.1], .pair cl.2 .unit⟩ cl Val.unit rK (clauseAt_clausesE [cl.1] 0 cl.2 rfl) rfl
  rw [htag, kappaAt_cell hq] at hop
  refine .cons (rstep_head R s .hole hop rfl) ?_
  have hal := Head.alloc (ℍ := ℍ) μ Val.unit ℓ hμ
  refine .cons (rstep_head R s (K := .appR (.val cl) (.pairR Val.unit
    (.appR (.val (Val.lam (kappaCBody (cellAff q) n (rH n (q :: qs) cl) rK))) .hole))) hal rfl) ?_
  have hb := Head.beta (ℍ := ℍ) (μ.upd ℓ Val.unit) (kappaCBody (cellAff q) n (rH n (q :: qs) cl) rK)
    (Val.loc ℓ)
  rw [kappaCBody_subst] at hb
  refine .cons (rstep_head R s (K := .appR (.val cl) (.pairR Val.unit .hole)) hb rfl) ?_
  exact .nil

end Steps

/-! ### The A-level reading -/

section Reading
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- The tags of a label's operations. -/
abbrev qsL (l : (RF.alg Ξ).Lab) : List Qual := (Ξ (RF.name Ξ l)).map Prod.fst

theorem withCl_eq (l : (RF.alg Ξ).Lab) (cl : Val) :
    (𝕊).withCl l (OVal.ofVal cl) = rProg (RF.name Ξ l) (qsL l) cl := rfl

/-- A row form whose pure row reads as the empty row: the runner that answers nothing answers it. -/
theorem answers_unit_of (hU : ∀ η, RF.den Ξ (RF.alg Ξ).unit η = [])
    (R : (𝕊).Runner) : (𝕊).Answers R (RF.alg Ξ).unit := by
  intro l i h
  obtain ⟨-, h⟩ := h
  have := h (fun _ => [])
  rw [hU] at this
  simp [Targets.Row.Has, Row.find] at this

/-- `bool` is a data type. -/
theorem dataTy_bool : (𝕊).DataTy (𝕊).bool := .sum .unit .unit

/-- An application of a value to a data value is the value applied at the evaluation position. -/
theorem use_app {K₀ : Kont} {w : OVal} {T : OVTy} (hw : (𝕊).DataVal T w) (k : Expr) :
    K₀.plug ((appK w.1).plug k) = K₀.plug (.app k w.1) := by
  have hv := isVal_of_dataVal hw
  unfold appK; rw [dif_pos hv]; rfl

/-- `appF` of a value form is a frame only at a Core value. -/
theorem isVal_of_appK_ne {V : Expr} (h : appK V ≠ .hole) : IsVal V := by
  unfold appK at h; split at h
  · assumption
  · exact absurd rfl h

theorem plug_appK_of_isVal {V : Expr} (h : IsVal V) (K₀ : Kont) (f : Expr) :
    K₀.plug ((appK V).plug f) = K₀.plug (.app f V) := by
  unfold appK; rw [dif_pos h]; rfl

/-- `κ = λs. case s {…}` applied at an argument. -/
def kappaAppShape : Expr → Bool
  | .app (.lam (.case (.var 0) _ _)) _ => true
  | _ => false

/-- A `κ`-shaped value `λs. case s {…}` applied at an evaluation position shows in `evalSubs`. -/
theorem not_use_of_shape {t b₁ b₂ : Expr} (h : (evalSubs t).any kappaAppShape = false) :
    ¬ ∃ (K₀ : Kont) (w : Expr), t = K₀.plug (.app (.lam (.case (.var 0) b₁ b₂)) w) := by
  rintro ⟨K₀, w, rfl⟩
  rw [any_evalSubs_plug K₀ (p := kappaAppShape) rfl] at h
  exact absurd h (by decide)

/-- No application of a `κ`-shaped value sits at an evaluation position of an operation tag list. -/
theorem any_kappa_qualsVal : ∀ qs : List Qual, (evalSubs (qualsVal qs).1).any kappaAppShape = false
  | [] => rfl
  | q :: qs => by
      show (evalSubs (.pair (.prim (.lit (.i32 q.tag))) (qualsVal qs).1)).any kappaAppShape = false
      simp only [evalSubs, List.any_cons, List.any_append, any_kappa_qualsVal qs]
      rfl

/-- Nor of `withCl` at a clause with none. -/
theorem any_kappa_rProg (n : UInt32) (qs : List Qual) (cl : Val)
    (hcl : (evalSubs cl.1).any kappaAppShape = false) :
    (evalSubs (rProg n qs cl)).any kappaAppShape = false := by
  simp only [rProg, handleK, hndValE, clausesE, rK, bindK, Kont.plug, performE, evalSubs,
    List.any_cons, List.any_append, any_kappa_qualsVal, hcl, List.any_nil]
  rfl

end Reading

/-! ### R1: `κ` dropped -/

/-- `op (v, k) ⇒ return ff`, at our instance. -/
def dropV : Val := ⟨.lam (.letpair (.var 0) (.inj₁ .unit)), .lam⟩

/-- The body of the twice-resuming clause under its `let`. -/
def twBody : Expr := bindE (resumeE (.var 0) .unit) (resumeE (.var 1) .unit)

/-- R2's clause `op (v, k) ⇒ resume k () to _. resume k ()`, at our instance. -/
def twiceV : Val := ⟨.lam (.letpair (.var 0) twBody), .lam⟩

/-- The body of the cancelling clause under its `let`. -/
def cBody : Expr := bindE (cancelE (.var 0)) (.inj₁ .unit)

/-- R3's clause `op (v, k) ⇒ cancel k to _. return ff`, at our instance. -/
def cancelV : Val := ⟨.lam (.letpair (.var 0) cBody), .lam⟩

/-- The body of the clause that cancels and then resumes, under its `let`. -/
def crBody : Expr := bindE (cancelE (.var 0)) (resumeE (.var 1) .unit)

/-- R4's clause `op (v, k) ⇒ cancel k to _. resume k ()`, at our instance. -/
def cancelResumeV : Val := ⟨.lam (.letpair (.var 0) crBody), .lam⟩

/-- R1's run after `κ` is handed: the clause's `β` and its `let`. -/
def r1Tail (κ : Val) : List (Kont × Expr × Expr) :=
  [(.hole, .app dropV.1 (.pair .unit κ.1), .letpair (.pair .unit κ.1) (.inj₁ .unit)),
   (.hole, .letpair (.pair .unit κ.1) (.inj₁ .unit), .inj₁ .unit)]

theorem r1Tail_chain (κ : Val) :
    HeadChain (ℍ := ℍ) (.app dropV.1 (.pair .unit κ.1)) (r1Tail κ) (.inj₁ .unit) := by
  refine .cons (K := .hole) (fun μ => Head.beta μ _ (Val.pair Val.unit κ)) rfl ?_
  refine .cons (K := .hole) (fun μ => Head.letpair μ Val.unit κ (.inj₁ .unit)) rfl ?_
  exact .nil

section R1
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- R1's run from the empty memory, its cell at `0`. -/
def r1Path (R : (𝕊).Runner) (s : R.St) (q : Qual) (qs : List Qual) (n : UInt32) :
    List ((𝕊).Event × (𝕊).RConf R) :=
  prefixPath R s Adequacy.emptyMem q qs 0 n dropV ++
    chainPath (ℍ := ℍ) R (Adequacy.emptyMem.upd 0 Val.unit) s
      (r1Tail ⟨(rκ q qs 0 n dropV).1, .lam⟩)

theorem rpath_r1 (R : (𝕊).Runner) (s : R.St) {q : Qual} (qs : List Qual) (n : UInt32)
    (hq : q ≠ .unr) :
    (𝕊).RPath R ((Adequacy.emptyMem, rProg n (q :: qs) dropV), s) (r1Path R s q qs n) :=
  A.EffectSystem.rpath_append (rpath_prefix R s qs n dropV hq rfl)
    (rpath_chainPath R (r1Tail_chain _))

theorem lastC_r1 (R : (𝕊).Runner) (s : R.St) (q : Qual) (qs : List Qual) (n : UInt32) :
    (𝕊).lastC ((Adequacy.emptyMem, rProg n (q :: qs) dropV), s) (r1Path R s q qs n) =
      ((Adequacy.emptyMem.upd 0 Val.unit, .inj₁ .unit), s) := by
  rw [r1Path, A.EffectSystem.lastC_append]
  exact lastC_chainPath R (r1Tail_chain _)

/-- The configurations before R1's five steps. -/
theorem take_r1 (R : (𝕊).Runner) (s : R.St) (q : Qual) (qs : List Qual) (n : UInt32) :
    ((((Adequacy.emptyMem, rProg n (q :: qs) dropV), s) : (𝕊).RConf R) ::
      (r1Path R s q qs n).map Prod.snd).take (r1Path R s q qs n).length =
    [((Adequacy.emptyMem, rProg n (q :: qs) dropV), s),
     ((Adequacy.emptyMem, .app dropV.1 (.pair .unit (kappaCell (cellAff q) n
        (rH n (q :: qs) dropV) rK))), s),
     ((Adequacy.emptyMem.upd 0 Val.unit, .app dropV.1 (.pair .unit
        (.app (.lam (kappaCBody (cellAff q) n (rH n (q :: qs) dropV) rK)) (.loc 0)))), s),
     ((Adequacy.emptyMem.upd 0 Val.unit, .app dropV.1 (.pair .unit (rκ q qs 0 n dropV).1)), s),
     ((Adequacy.emptyMem.upd 0 Val.unit,
        .letpair (.pair .unit (rκ q qs 0 n dropV).1) (.inj₁ .unit)), s)] := by
  rfl

open Classical in
/-- **R1 breaks S6.**  A typing system that types R1 at `F 0 bool`, at a label whose first operation
is resuming and linear or affine, fails S6: R1's run completes at `ff`; its capture event hands `κ`,
and no step uses it.  (The run ends with `κ`'s cell allocated.) -/
theorem not_contUseEv_of_der_R1 (hU : ∀ η, RF.den Ξ (RF.alg Ξ).unit η = [])
    (l : (RF.alg Ξ).Lab) {q : Qual} {qs : List Qual} (hqs : qsL l = q :: qs) (hq : q ≠ .unr)
    {o : A.OpSig OVTy} (ho : ((𝕊).sig l)[0]? = some o) (hk : o.cls ≠ .abortive)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).dropCl) ((𝕊).F (RF.alg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUseEv := by
  intro hC
  have he : (𝕊).withCl l (𝕊).dropCl = rProg (RF.name Ξ l) (q :: qs) dropV := by
    rw [← hqs]; rfl
  let R := (𝕊).R₀
  let q₁ := r1Path R () q qs (RF.name Ξ l)
  let κ : OVal := ⟨(rκ q qs 0 (RF.name Ξ l) dropV).1, .lam⟩
  have hpath := rpath_r1 R () qs (RF.name Ξ l) hq
  have hcomp : (𝕊).CompleteFrom R (((Adequacy.emptyMem, (𝕊).withCl l (𝕊).dropCl), ())) q₁ := by
    rw [he]
    refine ⟨hpath, ?_⟩
    change (𝕊).IsVal (Adequacy.emptyMem.upd 0 Val.unit, Expr.inj₁ Expr.unit)
    exact isVal_val _ (Val.inj₁ Val.unit)
  have hpv : IsVal (Expr.pair .unit κ.1) := .pair .unit .lam
  have hev : (𝕊).CatchEvAt (((Adequacy.emptyMem, (𝕊).withCl l (𝕊).dropCl), ())) q₁ 0 κ o.cls := by
    rw [he]
    refine ⟨by simp [q₁, r1Path, prefixPath, chainPath, r1Tail], .hole, l, ⟨rRet, .lam⟩,
      [(𝕊).dropCl], rK, 0, (𝕊).unitV, o, (𝕊).dropCl, ?_, rfl, ho, rfl, hk, rfl, ?_, 3,
      by omega, by simp [q₁, r1Path, prefixPath, chainPath, r1Tail], ?_, ?_⟩
    · show rProg (RF.name Ξ l) (q :: qs) dropV = _
      rw [← he]; rfl
    · show appK (Expr.pair .unit κ.1) ≠ .hole
      unfold appK; rw [dif_pos hpv]; simp
    · show Expr.app dropV.1 (.pair .unit κ.1) = Kont.hole.plug ((appK (Expr.pair .unit κ.1)).plug dropV.1)
      rw [plug_appK_of_isVal hpv]; rfl
    · intro j'' κ' h0 h3 hne
      have hv' : IsVal (Expr.pair .unit κ'.1) := isVal_of_appK_ne hne
      have hκ' : IsVal κ'.1 := hv'.pair_right
      change _ ≠ Kont.hole.plug ((appK (Expr.pair .unit κ'.1)).plug dropV.1)
      rw [plug_appK_of_isVal hv']
      interval_cases j''
      · intro heq
        have h1 : (𝕊).term ((𝕊).cfgAt (((Adequacy.emptyMem, rProg (RF.name Ξ l) (q :: qs) dropV), ())
            : (𝕊).RConf R) q₁ 1).1 = Expr.app dropV.1 (.pair .unit (kappaCell (cellAff q)
              (RF.name Ξ l) (rH (RF.name Ξ l) (q :: qs) dropV) rK)) := rfl
        rw [h1] at heq
        injection heq with _ h2
        injection h2 with _ h3
        rw [← h3] at hκ'
        unfold kappaCell at hκ'
        cases hκ'
      · intro heq
        have h1 : (𝕊).term ((𝕊).cfgAt (((Adequacy.emptyMem, rProg (RF.name Ξ l) (q :: qs) dropV), ())
            : (𝕊).RConf R) q₁ 2).1 = Expr.app dropV.1 (.pair .unit
              (.app (.lam (kappaCBody (cellAff q) (RF.name Ξ l) (rH (RF.name Ξ l) (q :: qs) dropV)
                rK)) (.loc 0))) := rfl
        rw [h1] at heq
        injection heq with _ h2
        injection h2 with _ h3
        rw [← h3] at hκ'
        cases hκ'
  obtain ⟨huse, -⟩ := hC R r₀_respects _ _ _ (answers_unit_of hU R) h dataTy_bool q₁ hcomp κ
    ⟨0, o.cls, hev⟩
  have huse' : (𝕊).uses (((Adequacy.emptyMem, (𝕊).withCl l (𝕊).dropCl), ()) : (𝕊).RConf R) q₁ κ =
      (𝕊).caughtEv (((Adequacy.emptyMem, (𝕊).withCl l (𝕊).dropCl), ()) : (𝕊).RConf R) q₁ κ := huse
  have hu0 : (𝕊).uses (((Adequacy.emptyMem, (𝕊).withCl l (𝕊).dropCl), ()) : (𝕊).RConf R) q₁ κ = 0 := by
    unfold A.EffectSystem.uses
    rw [A.EffectSystem.countP_range_take _ _ _
      (fun c : (𝕊).RConf R => decide (∃ (K₀ : Kont) (w : OVal) (T : OVTy), (𝕊).DataVal T w ∧
        c.1.2 = K₀.plug ((appK w.1).plug κ.1))) (fun j hj => decide_eq_decide.2
          ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩)]
    rw [he, show List.take q₁.length ((((Adequacy.emptyMem, rProg (RF.name Ξ l) (q :: qs) dropV), ())
        : (𝕊).RConf R) :: List.map Prod.snd q₁) = _ from take_r1 R () q qs (RF.name Ξ l)]
    refine List.countP_eq_zero.2 fun c hc => ?_
    simp only [decide_eq_true_eq, not_exists, not_and]
    intro K₀ w T hw heq
    rw [use_app hw] at heq
    refine not_use_of_shape (b₁ := _) (b₂ := _) ?_ ⟨K₀, w.1, heq⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact any_kappa_rProg _ _ dropV rfl
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    exact absurd hc List.not_mem_nil
  have hc1 := A.EffectSystem.caughtEv_pos hev
  omega

end R1

/-! ### At the open-row form -/

section Orow
variable {Ξ : EffCtx} {J : OurTyping orowRF}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ J

theorem orow_unit (η : RowEnv) : orowRF.den Ξ (orowAlg Ξ).unit η = [] := rfl

/-- R1 at the open-row form. -/
theorem not_contUseEv_of_der_R1_orow (l : (orowAlg Ξ).Lab) {q : Qual} {qs : List Qual}
    (hqs : qsL (RF := orowRF) (Ξ := Ξ) l = q :: qs) (hq : q ≠ .unr) {o : A.OpSig OVTy}
    (ho : ((𝕊).sig l)[0]? = some o) (hk : o.cls ≠ .abortive)
    (h : (𝕊).der [] ((𝕊).withCl l (𝕊).dropCl) ((𝕊).F (orowAlg Ξ).unit (𝕊).bool)) :
    ¬ (𝕊).ContUseEv :=
  not_contUseEv_of_der_R1 orow_unit l hqs hq ho hk h

end Orow

/-! ### Today's kernel types none of R1–R4 -/

/-- **Today's kernel refuses R1–R4**, at every label and type.  The reason is the handler's form:
our instance's handler is the run-time frame, whose clauses are values, and today's `[handle]`
types only clause variables (`not_der_handle_tier1Open`).  It is not the linearity of `κ`; that
refusal is read at the clauses themselves (`refuses_R_clauses`). -/
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

/-- A typing system that types R1–R4, at every name and tag list, and nothing else. -/
def JR : OurTyping orowRF :=
  ⟨fun _ _ Γ e _ => Γ = [] ∧ ∃ n qs, e = rProg n qs dropV ∨ e = rProg n qs twiceV ∨
    e = rProg n qs cancelV ∨ e = rProg n qs cancelResumeV, OutJ.core, fun _ η => η⟩

/-- The label of the name `5`, linear at `ΞA` (`tick`). -/
def lab5A : (orowAlg ΞA).Lab := ⟨5, by decide, by simp [ΞA], by simp [ΞA]⟩

/-- The label of the name `2`, affine at `ΞA` (`wait`). -/
def lab2A : (orowAlg ΞA).Lab := ⟨2, by decide, by simp [ΞA], by simp [ΞA]⟩

/-- **S6's tooth bites at an admissible effect context**: `JR` types R1 at `F 0 bool` at the affine
`wait` and at the linear `tick`; the lemma's other premises hold there; so `JR` fails S6. -/
theorem teeth_JR_ΞA :
    AdmEff ΞA ∧
    (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab2A (ourInst (ℍ := ℍ) orowRF ΞA JR).dropCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) ∧
    (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab5A (ourInst (ℍ := ℍ) orowRF ΞA JR).dropCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) ∧
    ¬ (ourInst (ℍ := ℍ) orowRF ΞA JR).ContUseEv := by
  have d1 : (ourInst (ℍ := ℍ) orowRF ΞA JR).der []
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).withCl lab2A (ourInst (ℍ := ℍ) orowRF ΞA JR).dropCl)
      ((ourInst (ℍ := ℍ) orowRF ΞA JR).F (orowAlg ΞA).unit (ourInst (ℍ := ℍ) orowRF ΞA JR).bool) :=
    ⟨tiedAt_unit JR _, .inl ⟨[], by simp, rfl, 2, _, .inl rfl⟩⟩
  refine ⟨admEff_ΞA, d1, ⟨tiedAt_unit JR _, .inl ⟨[], by simp, rfl, 5, _, .inl rfl⟩⟩, ?_⟩
  exact not_contUseEv_of_der_R1_orow lab2A (q := .aff) (qs := []) rfl (by decide)
    (o := ⟨OVTy.ofV .unit, OVTy.ofV .unit, .affine⟩) (by simp [lab2A, ΞA]; rfl) (by decide) d1

end Targets.Inst

end
