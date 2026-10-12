import Targets.Instance.CancelWitness
import Targets.I.RejectsFin

/-!
# The Instance — E7 (abandoning a suspension, the cancel policy) at `J₁`

`J₁`'s kernel takes SPEC §27's `[then]`: a finaliser may raise to a live handler, its raises
recorded in the cancel rows of the operations its computation performs.  E7's programs are
`timeout`s of `wait` around a body whose frame holds a finaliser.

* **E7a** (`d_e7a`): the finaliser returns; `wait`'s cancel row is empty.
* **E7b** (`d_e7b`, `Targets/Instance/CancelWitness.lean`): the finaliser raises `exnₒ`, handled
  outside the `timeout`; `wait`'s cancel row holds it.
* **E7c is rejected** (decision D3; `not_der_e7c`, `not_der_e7c_J₁`): the finaliser raises `exnᵢ`,
  handled only inside the cancelled region.  `[then]` puts `exnᵢ` in `wait`'s cancel row, and the
  `timeout` clause applies `κ`'s cancel branch, at `F_{F ⊕ Σ} 1`, at its own row `Σ`, so `Σ` holds
  `exnᵢ`, and so does every row the program is read at.  At a row with `exnᵢ` the program is typed
  (`d_e7c_lift`): its context then has an instance of `exnᵢ`, which the finaliser's raise reaches
  (decision D1), so the rejection is at the rows without `exnᵢ`.
* **E7d** (`d_e7d`): two finalisers, raising `exn_a` and `exn_b`; `wait`'s cancel row holds both
  (`F ⋈ Σ_D` at the outer `[then]`).

The runs (`runsTo_e7a`, `runsTo_e7b`, `runsTo_e7d`): the catch of the affine `wait` allocates `κ`'s
cell at every free location and the clause's cancel releases it (`obsFrom_tmCatch`); the cancel
fires the frozen finalisers innermost first, each showing its fire and its end, keeps the first
error and re-raises it at the canceller, where `toResult` catches it.  Every complete run answers
`inr ()`.  `cancelPolicy_J₁`: E7 at every admissible effect context.

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont Heap performE raiseE hndE hndVal opPayload cancelVal kappaC kappaCell
  kappaCBody kappaAt capTag freeE ubindE cfinE ccatchE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt lookEnd)

/-! ### The programs, as our instance writes them -/

/-- A's `e7a`: `timeout (body ())`. -/
def e7aE (nw : UInt32) (qw : Expr) : Expr := timeoutHE nw qw (bodyFE nw .unit)

/-- A's `e7c`: `timeout (handle exnᵢ {…} (body (raise exnᵢ ())))`. -/
def e7cE (nw ni : UInt32) (qw qi : Expr) : Expr :=
  timeoutHE nw qw (toResultE ni qi (bodyFE nw (raiseE (opArgE ni 0 .unit))))

/-- A's `e7d`: `handle exn_a {…} (handle exn_b {…} (timeout ((body (raise exn_a ())) then x. return x
unwind raise exn_b ())))`. -/
def e7dE (nw na nb : UInt32) (qw qa qb : Expr) : Expr :=
  toResultE na qa (toResultE nb qb (timeoutHE nw qw
    ((thenK (.var 0) (raiseE (opArgE nb 0 .unit))).plug (bodyFE nw (raiseE (opArgE na 0 .unit))))))

section Vals
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem e7a_val (lw : (orowAlg Ξ).Lab) : ((𝕁).e7a lw : Expr) = e7aE lw.1 (qsOf Ξ lw.1) := rfl

theorem e7b_val (lw lo : (orowAlg Ξ).Lab) :
    ((𝕁).e7b lw lo : Expr) = e7bE lw.1 lo.1 (qsOf Ξ lw.1) (qsOf Ξ lo.1) := rfl

theorem e7c_val (lw li : (orowAlg Ξ).Lab) :
    ((𝕁).e7c lw li : Expr) = e7cE lw.1 li.1 (qsOf Ξ lw.1) (qsOf Ξ li.1) := rfl

theorem e7d_val (lw la lb : (orowAlg Ξ).Lab) :
    ((𝕁).e7d lw la lb : Expr) = e7dE lw.1 la.1 lb.1 (qsOf Ξ lw.1) (qsOf Ξ la.1) (qsOf Ξ lb.1) := rfl

end Vals

/-! ### Rows -/

/-- An operation found in a one-operation signature row before the empty row. -/
theorem find_ofEff_one_nil {n : UInt32} {e : Qual × VTy × VTy} {m i : UInt32} {o : OpSig}
    (h : Row.find (Row.ofEff n [e] 0 ++ []) m i = some o) :
    m = n ∧ i = 0 ∧ o = ⟨n, 0, e.1, e.2.1, e.2.2, .ret .unit⟩ := by
  rw [List.append_nil] at h
  exact find_ofEff_one (fs := finsNil) h

/-- Rows that find the same operation at every key are below each other. -/
theorem rowLe_of_find_eq {S S' : Row} (h : ∀ n i, Row.find S n i = Row.find S' n i) : RowLe S S' :=
  RowLe.of_find fun n i _ hf => (h n i) ▸ hf

/-- A row whose first entry's cancel row grows: the rows below each other. -/
theorem rowLe_cons_fin {n i : UInt32} {q : Qual} {A B : VTy} {F F' : CTy} (hF : FinLe F F')
    (T : Row) : RowLe (⟨n, i, q, A, B, F⟩ :: T) (⟨n, i, q, A, B, F'⟩ :: T) := by
  intro m j o hf
  unfold Row.find at hf ⊢
  rw [List.find?_cons] at hf ⊢
  by_cases hk : m = n ∧ j = i
  · rw [decide_eq_true hk] at hf ⊢
    cases hf
    exact ⟨_, rfl, OpSig.Sig.refl _, fun _ => hF⟩
  · have hk' : decide (m = n ∧ j = i) = false := decide_eq_false hk
    rw [hk'] at hf ⊢
    exact ⟨o, hf, OpSig.LeF.refl o⟩

/-- An abortive `1 ↠ 0` is not capturable. -/
theorem capB_exn (q : Qual) : capB q .zero = false := by simp [capB, VTy.isZero]

/-- A cancel row of abortive operations with persistent arguments keeps only persistent errors. -/
theorem finPers_exns : ∀ (L : List OpSig), (∀ o ∈ L, o.A = .unit ∧ o.B = .zero ∧ o.fin = .ret .unit) →
    (CTy.effOf L .unit).FinPers
  | [], _ => trivial
  | o :: L, h => by
      obtain ⟨hA, hB, hF⟩ := h o List.mem_cons_self
      obtain ⟨n, i, q, A, B, F⟩ := o
      simp only at hA hB hF
      subst hA hB hF
      exact ⟨fun _ => rfl, fun _ => trivial, finPers_exns L fun o ho => h o (List.mem_cons_of_mem _ ho)⟩

/-! ### Typing -/

section Typing
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **`e7a` is typed by `J₁`'s kernel**: the finaliser returns, and `wait`'s cancel row is empty. -/
theorem d_e7a {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    CDerivesAt Ξ LifeCtx.empty [] (e7aE lw.1 (qsOf Ξ lw.1)) (.comp (.ret (.sum boolT .unit))) := by
  refine d_timeoutHA hlw (S := []) (rowAt_nil Ξ) (by simp) (X := boolT) (F := .ret .unit) rfl
    (by simpa [CTy.rowOf] using RowLe.refl ([] : Row)) ?_
  refine d_bodyFA hlw (SD := []) ?_ ?_ (RowLe.nil _) (ThenLe.nil _) (.ret (.unitI (.cons .nil)))
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    subst ho
    exact lw.2.1
  · simp [Row.Uniq, Row.ofEff]

/-- The cancel row of `wait` in `e7d`: the finalisers raise `exn_a` and `exn_b`. -/
abbrev finRaise2 (na nb : UInt32) (qa qb : Qual) : CTy :=
  CTy.effOf [⟨na, 0, qa, .unit, .zero, .ret .unit⟩, ⟨nb, 0, qb, .unit, .zero, .ret .unit⟩] .unit

/-- `exn_b`'s and `exn_a`'s rows, the row of `timeout` in `e7d`. -/
abbrev rowBA (na nb : UInt32) (qa qb : Qual) : Row :=
  Row.ofEff nb [(qb, .unit, .zero)] 0 ++ (Row.ofEff na [(qa, .unit, .zero)] 0 ++ [])

theorem find_rowBA_a {na nb : UInt32} (hab : na ≠ nb) (qa qb : Qual) :
    Row.find (rowBA na nb qa qb) na 0 = some ⟨na, 0, qa, .unit, .zero, .ret .unit⟩ := by
  rw [Row.find_append, Targets.find_ofEff_other _ hab, Option.none_or]
  simp [Row.ofEff, Row.find]

theorem find_rowBA_b {na nb : UInt32} (qa qb : Qual) :
    Row.find (rowBA na nb qa qb) nb 0 = some ⟨nb, 0, qb, .unit, .zero, .ret .unit⟩ := by
  simp [Row.ofEff, Row.find]

/-- `finRaise2` holds both raises: `{exn_a} ⋈ {exn_b}`, at the outer `[then]`. -/
theorem thenLe_finRaise2 {na nb : UInt32} (hab : na ≠ nb) (qa qb : Qual) :
    ThenLe (finRaise na qa) (Row.ofEff nb [(qb, .unit, .zero)] 0 ++ []) (finRaise2 na nb qa qb) := by
  rw [ThenLe]
  refine .inr ⟨rfl, fun n i o hf => ?_, fun n i o hf => ?_⟩
  · simp only [CTy.rowOf, CTy.effOf, Row.find, List.find?_cons, List.find?_nil] at hf
    by_cases hk : n = na ∧ i = 0
    · rw [decide_eq_true hk] at hf
      cases hf
      refine ⟨_, ?_, OpSig.Sig.refl _, fun h => by simp [capB, VTy.isZero] at h⟩
      obtain ⟨rfl, rfl⟩ := hk
      simp [CTy.rowOf, CTy.effOf, Row.find]
    · rw [decide_eq_false hk] at hf; cases hf
  · obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one_nil hf
    refine ⟨_, ?_, OpSig.Sig.refl _, fun h => by simp [capB, VTy.isZero] at h⟩
    simp [CTy.rowOf, CTy.effOf, Row.find, Ne.symm hab]

/-- **`e7d` is typed by `J₁`'s kernel**: the inner `[then]` puts `exn_a` in `wait`'s cancel row,
the outer one adds `exn_b`, and both are handled outside the `timeout`. -/
theorem d_e7d {lw la lb : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {qa qb : Qual}
    (hla : Ξ la.1 = [(qa, .unit, .zero)]) (hqa : qa ≠ .lin) (hlb : Ξ lb.1 = [(qb, .unit, .zero)])
    (hqb : qb ≠ .lin) (hwa : lw.1 ≠ la.1) (hwb : lw.1 ≠ lb.1) (hab : la.1 ≠ lb.1) :
    CDerivesAt Ξ LifeCtx.empty [] (e7dE lw.1 la.1 lb.1 (qsOf Ξ lw.1) (qsOf Ξ la.1) (qsOf Ξ lb.1))
      (.comp (.ret (.sum (.sum (.sum boolT .unit) .unit) .unit))) := by
  have hSa := rowAt_ofEff_lab la hla
  have hSba : RowAt Ξ (rowBA la.1 lb.1 qa qb) := by
    have h := rowAt_rowOf lb
    rw [rowOf, hlb] at h
    exact Targets.rowAt_append h hSa
  have hnba : ∀ o ∈ rowBA la.1 lb.1 qa qb, o.n ≠ lw.1 := by
    intro o ho
    simp only [rowBA, Row.ofEff, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact Ne.symm hwb
    · exact Ne.symm hwa
  refine d_toResult hla hqa (S := []) (rowAt_nil Ξ) (by simp) ?_
  refine d_toResult hlb hqb (S := Row.ofEff la.1 [(qa, .unit, .zero)] 0 ++ []) hSa
    (names_ofEff hab) ?_
  refine d_timeoutHA hlw (S := rowBA la.1 lb.1 qa qb) hSba hnba (X := boolT)
    (F := finRaise2 la.1 lb.1 qa qb) rfl ?_ ?_
  · refine RowLe.of_find fun n i o hf => ?_
    rw [Row.find_append] at hf
    cases hF : Row.find (finRaise2 la.1 lb.1 qa qb).rowOf n i with
    | none => rw [hF, Option.none_or] at hf; exact hf
    | some o' =>
        rw [hF, Option.some_or] at hf
        cases hf
        simp only [CTy.rowOf, CTy.effOf, Row.find, List.find?_cons, List.find?_nil] at hF
        by_cases ha : n = la.1 ∧ i = 0
        · rw [decide_eq_true ha] at hF
          cases hF
          obtain ⟨rfl, rfl⟩ := ha
          exact find_rowBA_a hab qa qb
        · rw [decide_eq_false ha] at hF
          by_cases hb : n = lb.1 ∧ i = 0
          · rw [decide_eq_true hb] at hF
            cases hF
            obtain ⟨rfl, rfl⟩ := hb
            exact find_rowBA_b qa qb
          · rw [decide_eq_false hb] at hF; cases hF
  -- the outer `[then]`, its finaliser `raise exn_b`
  set Fa := finRaise la.1 qa
  set Fab := finRaise2 la.1 lb.1 qa qb
  set Sba := rowBA la.1 lb.1 qa qb
  have hNZ : ∀ F : CTy, (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ Sba).NZ := by
    intro F o ho
    simp only [Sba, rowBA, Row.ofEff, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact lw.2.1
    · exact lb.2.1
    · exact la.2.1
  have hUq : ∀ F : CTy, (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ Sba).Uniq := by
    intro F
    simp [Sba, rowBA, Row.Uniq, Row.ofEff, hwa, hwb, Ne.symm hab]
  have hfind : ∀ F : CTy, Row.find (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ Sba)
      lw.1 0 = some ⟨lw.1, 0, .aff, .unit, .unit, F⟩ := by
    intro F; simp [Row.ofEff, Row.find]
  refine .effThen (SM := Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => Fa) ++ Sba)
    (SD := Row.ofEff lb.1 [(qb, .unit, .zero)] 0 ++ []) .nil (hNZ Fab) (hUq Fab)
    (fun _ => fun _ h => absurd h List.not_mem_nil) ?_ ?_ ?_ ?_ ?_
    (.effSub (rowLe_nil _) (.ret (.var (.here .nil)))) (d_raiseLab (.cons .nil) lb hlb hqb .unit)
  · -- `M`'s row is below the `[then]`'s: `wait`'s cancel row grows from `{exn_a}`
    show RowLe (⟨lw.1, UInt32.ofNat 0, .aff, .unit, .unit, Fa⟩ :: Sba)
      (⟨lw.1, UInt32.ofNat 0, .aff, .unit, .unit, Fab⟩ :: Sba)
    refine rowLe_cons_fin ?_ Sba
    rw [finLe_iff]
    refine .inr ⟨rfl, RowLe.of_find fun n i o hf => ?_⟩
    simp only [Fa, CTy.rowOf, CTy.effOf, Row.find, List.find?_cons, List.find?_nil] at hf
    by_cases ha : n = la.1 ∧ i = 0
    · rw [decide_eq_true ha] at hf
      cases hf
      obtain ⟨rfl, rfl⟩ := ha
      simp [Fab, CTy.rowOf, CTy.effOf, Row.find]
    · rw [decide_eq_false ha] at hf; cases hf
  · -- the finaliser's row is below the `[then]`'s
    refine RowLe.of_find fun n i o hf => ?_
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one_nil hf
    rw [Row.find_append, Row.find_ofEff_ne lw.1 _ 0 _ lb.1 0 (Ne.symm hwb), Option.none_or]
    exact find_rowBA_b qa qb
  · -- `F ⋈ Σ_D ≤ Σ(wait).fin`
    intro n i o o' hf hf' hc
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [Sba, rowBA, Row.ofEff, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · have hf'' : Row.find (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => Fab) ++ Sba) lw.1 0 =
          some o' := hf'
      rw [hfind Fab] at hf''
      cases hf''
      exact thenLe_finRaise2 hab qa qb
    · exact absurd hc (by simp [capB, VTy.isZero])
    · exact absurd hc (by simp [capB, VTy.isZero])
  · -- the errors pending at the finaliser are persistent
    intro _ o ho
    simp only [Sba, rowBA, Row.ofEff, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · refine ⟨fun h => by simp [OpSig.abort, VTy.isZero] at h, fun _ => ?_⟩
      exact finPers_exns _ (by simp)
    · exact ⟨fun _ => rfl, fun h => by simp [capB, VTy.isZero] at h⟩
    · exact ⟨fun _ => rfl, fun h => by simp [capB, VTy.isZero] at h⟩
  · -- the inner `[then]`: `body (raise exn_a ())`
    refine d_bodyFA hlw (hNZ Fa) (hUq Fa) ?_ (thenLe_finRaise la.1 qa)
      (d_raiseLab (.cons .nil) la hla hqa .unit)
    refine RowLe.of_find fun n i o hf => ?_
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one_nil hf
    rw [Row.find_append, Row.find_ofEff_ne lw.1 _ 0 _ la.1 0 (Ne.symm hwa), Option.none_or]
    exact find_rowBA_a hab qa qb

/-- **`e7a` is typed by `J₁`**. -/
theorem der_e7a_J₁ {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).der [] ((𝕁).e7a lw) ((𝕁).F (𝕁).EA.unit ((𝕁).Sum (𝕁).bool (𝕁).UnitT)) := by
  have hd := d_e7a hlw
  rw [e7a_val]
  exact der_J₁_ret (A := .sum boolT .unit) (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- **`e7b` is typed by `J₁`**, at every two labels. -/
theorem der_e7b_lab_J₁ {lw lo : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {qo : Qual}
    (hlo : Ξ lo.1 = [(qo, .unit, .zero)]) (hqo : qo ≠ .lin) (hne : lw.1 ≠ lo.1) :
    (𝕁).der [] ((𝕁).e7b lw lo) ((𝕁).F (𝕁).EA.unit (𝕁).ty7) := by
  have hd := d_e7b hlw hlo hqo hne
  rw [e7b_val]
  exact der_J₁_ret (A := .sum (.sum boolT .unit) .unit)
    (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- **`e7d` is typed by `J₁`**. -/
theorem der_e7d_J₁ {lw la lb : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {qa qb : Qual}
    (hla : Ξ la.1 = [(qa, .unit, .zero)]) (hqa : qa ≠ .lin) (hlb : Ξ lb.1 = [(qb, .unit, .zero)])
    (hqb : qb ≠ .lin) (hwa : lw.1 ≠ la.1) (hwb : lw.1 ≠ lb.1) (hab : la.1 ≠ lb.1) :
    (𝕁).der [] ((𝕁).e7d lw la lb) ((𝕁).F (𝕁).EA.unit (𝕁).ty7d) := by
  have hd := d_e7d hlw hla hqa hlb hqb hwa hwb hab
  rw [e7d_val]
  exact der_J₁_ret (A := .sum (.sum (.sum boolT .unit) .unit) .unit)
    (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- `e7c` at a row holding `exnᵢ`: the finaliser's raise reaches the context's instance of `exnᵢ`
(decision D1), recorded in `wait`'s cancel row and live at the `timeout` clause's row. -/
theorem d_e7c_lift {lw li : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {qi : Qual}
    (hli : Ξ li.1 = [(qi, .unit, .zero)]) (hqi : qi ≠ .lin) (hne : lw.1 ≠ li.1) :
    CDerivesAt Ξ LifeCtx.empty [] (e7cE lw.1 li.1 (qsOf Ξ lw.1) (qsOf Ξ li.1))
      (.comp (CTy.effOf (Row.ofEff li.1 [(qi, .unit, .zero)] 0 ++ []) (.sum (.sum boolT .unit) .unit))) := by
  have hSi := rowAt_ofEff_lab li hli
  have hnli : ∀ o ∈ Row.ofEff li.1 [(qi, .unit, .zero)] 0 ++ [], o.n ≠ lw.1 := names_ofEff hne.symm
  set F := finRaise li.1 qi
  refine d_timeoutHA hlw hSi hnli (X := .sum boolT .unit) (F := F) rfl ?_ ?_
  · refine RowLe.of_find fun n i o hf => ?_
    rw [Row.find_append] at hf
    simp only [F, CTy.rowOf, CTy.effOf] at hf
    rw [List.append_nil]
    by_cases hk : n = li.1 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      simp [Row.find] at hf
      subst hf
      simp [Row.ofEff, Row.find]
    · have : Row.find [⟨li.1, 0, qi, .unit, .zero, .ret .unit⟩] n i = none := by
        simp only [Row.find, List.find?_cons, List.find?_nil]
        rw [decide_eq_false hk]
      rw [this, Option.none_or, List.append_nil] at hf
      exact hf
  -- `toResult exnᵢ` at `wait`'s row alone, read at the row with `exnᵢ` after it
  have hW : RowAt Ξ (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ []) := by
    have h := rowAt_ofEff_lab lw hlw
    exact Targets.rowAt_ofEff_fs h
  refine .effSub (rowLe_append_nil _ _) (d_toResult hli hqi hW ?_ ?_)
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    subst ho
    exact hne
  -- the body at `wait`'s row before `exnᵢ`'s, read at `exnᵢ`'s before `wait`'s
  have hB := d_bodyFA hlw (D := raiseE (opArgE li.1 0 .unit))
    (S := Row.ofEff li.1 [(qi, .unit, .zero)] 0 ++ [])
    (SD := Row.ofEff li.1 [(qi, .unit, .zero)] 0 ++ []) (F := F) ?_ ?_
    (rowLe_ofEff_consF _ _ hnli) (thenLe_finRaise li.1 qi) (d_raiseLab (.cons .nil) li hli hqi .unit)
  · refine .effSub (rowLe_of_find_eq fun n i => ?_) hB
    simp only [Row.find_append, List.append_nil]
    by_cases hn : n = lw.1
    · subst hn
      rw [Row.find_ofEff_ne li.1 _ 0 _ _ i hne, Option.none_or, Option.or_none]
    · rw [Row.find_ofEff_ne lw.1 _ 0 _ n i hn, Option.none_or, Option.or_none]
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact lw.2.1
    · exact li.2.1
  · simp [Row.Uniq, Row.ofEff, hne]

end Typing

end Targets.Inst

/-! ### E7c's rejection, at Core's kernel -/

namespace Targets.Rej
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)
open BoCa.BoLo (performE raiseE)

/-- `bind`'s and `[let]`'s premise on the bound term, at the conclusion `j₀`: the bound term at a
row, and the conclusion at that row (`[let]`), or the bound term at the empty row (`bind`). -/
def LetBase (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (j₀ : Jdg) : Prop :=
  ∃ (Γ₁ : Ctx VTy) (S : Row) (A : VTy), CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ M (.comp (CTy.effOf S A)) ∧
    (S = [] ∨ ∃ B, j₀ = .comp (CTy.effOf S B))

/-- **A `M to x. N` whose bound term is no variable, λ-value, `()` or injection of `()`** is
`bind`'s or `[let]`'s, then the same-term rules; or `⊸E`'s, its bound term at a value
judgement. -/
theorem der_letJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ N M, e = .app (.lam N) M → (∀ i, M ≠ .var i) → (∀ b, M ≠ .lam b) → M ≠ .unit →
      M ≠ .inj₁ .unit → M ≠ .inj₂ .unit →
      (∃ j₀, LetBase Δ Γ M j₀ ∧ JR j₀ j) ∨ ∃ Γ₁ A, CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ M (.val A) := by
  induction h with
  | bind hs hM _ =>
      intro N M he _ _ _ _ _
      simp only [Expr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact .inl ⟨_, ⟨_, [], _, splitP_le_left hs, hM, .inl rfl⟩, .refl⟩
  | effLet hs _ _ hM _ =>
      intro N M he _ _ _ _ _
      simp only [Expr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact .inl ⟨_, ⟨_, _, _, splitP_le_left hs, hM, .inr ⟨_, rfl⟩⟩, .refl⟩
  | lolliE hs ha _ =>
      intro N M he _ _ _ _ _
      simp only [Expr.app.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact .inr ⟨_, _, splitP_le_left hs, ha⟩
  | app _ _ _ =>
      intro N M he hv _ _ _ _
      simp only [Expr.app.injEq] at he
      exact (hv _ he.2.symm).elim
  | letPoly b _ _ _ =>
      intro N M he _ hl _ _ _
      simp only [Expr.app.injEq] at he
      exact (hl _ he.2.symm).elim
  | allE _ _ =>
      intro N M he _ _ hu _ _
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | allEV _ _ =>
      intro N M he _ _ hu _ _
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | proj₁ _ =>
      intro N M he _ _ _ hu _
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | proj₂ _ =>
      intro N M he _ _ _ _ hu
      simp only [Expr.app.injEq] at he
      exact (hu he.2.symm).elim
  | force => intro N M he; rcases forceE_var he with h | h <;> simp at h
  | ret _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.ret _)⟩
      · exact .inr h
  | ofRet _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
      · exact .inr h
  | effSub hle _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
      · exact .inr h
  | nuIn hC _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
      · exact .inr h
  | nuOut hC _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
      · exact .inr h
  | bangE _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
      · exact .inr h
  | boxI _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
      · exact .inr h
  | boxE _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
      · exact .inr h
  | immSub _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
      · exact .inr h
  | mutSub _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
      · exact .inr h
  | roll _ _ _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
      · exact .inr h
  | unroll _ ih =>
      intro N M he h₁ h₂ h₃ h₄ h₅
      rcases ih N M he h₁ h₂ h₃ h₄ h₅ with ⟨j₀, hb, hr⟩ | h
      · exact .inl ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
      · exact .inr h
  | _ => intro N M he; cd_at he

/-- **An affine `κ`'s cancel branch, applied**: at a slot of `U(C₁ & C₂)`, `x (inj₂ ())` is read at
what the same-term rules reach from `C₂`. -/
theorem kcancel_jr_aff {Δ : LifeCtx} {Γ Γ' : Ctx VTy} {C₁ C₂ : CTy} {j : Jdg}
    (hslot : Γ[0]? = some ⟨.thunk (.amp C₁ C₂), true⟩) (hle : CtxLe Γ' Γ)
    (h : CDerives Δ Γ' (.app (.var 0) (.val (Val.inj₂ Val.unit))) j) : JR (.comp C₂) j := by
  obtain ⟨j₀, hb, hr⟩ := der_app h (.var 0) (.val (Val.inj₂ Val.unit)) rfl
  rcases hb with ⟨_, _, _, _, hs, -, hf, rfl⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, he, -⟩ |
    ⟨D₁, D₂, -, hX, rfl⟩ | ⟨he, -⟩ | he | he | ⟨_, he⟩ | ⟨_, he⟩
  · rcases varCls_of_le hslot (CtxLe.trans (splitP_le_right hs) hle) hf with hc | ⟨C, hT, -, hr'⟩
    · cases vview_thunk hc
    · cases hT
      obtain ⟨S, A, he⟩ := JR.comp_val hr'
      exact absurd he (Inst.effOf_ne_amp S A C₁ C₂).symm
  all_goals first
    | (cases he)
    | skip
  · rcases varCls_of_le hslot hle hX with hc | ⟨C, hT, -, hr'⟩
    · obtain ⟨S, Y, he, -⟩ := hc
      exact absurd he.symm (Inst.effOf_ne_amp S Y D₁ D₂)
    · cases hT
      obtain ⟨-, rfl⟩ := JR.amp_amp hr'
      exact hr

/-- **`timeout`'s clause reads `κ`'s cancel at its row**: the clause `wait (_, k) ⇒ cancel k;
return (inr ())`, at the clause type of an affine `A ↠ B`, `B` no `0`, at the cancel row `F`, applies
`κ`'s cancel branch, at `cancelTy Σ F`, where the same-term rules read it at the clause's row `Σ` or
below: `F` is no `⊤`, and `Σ` finds each operation `F` finds. -/
theorem timeoutCl_finds {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R A B : VTy} {F : CTy}
    (hB : B.isZero = false)
    (h : CDerives Δ Γ Inst.timeoutClA (.val (clauseTy S R (.aff, A, B) F))) :
    F.isTop = false ∧ ∀ n i o, Row.find F.rowOf n i = some o → ∃ o', Row.find S n i = some o' := by
  have hty : clauseTy S R (.aff, A, B) F =
      .bang (.thunk (.arr (.tensor A (kTy S R .aff B F)) (CTy.effOf S R))) := by
    simp [clauseTy, hB]
  rw [hty] at h
  obtain ⟨-, hb⟩ := lam_bang h (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨j₀, ⟨Γ₁, Γ₂, A', B', C, hs, hV, hB₂, rfl⟩, hr⟩ := der_letpairJ hb _ _ rfl
  have hslotP : (⟨.tensor A (kTy S R .aff B F), true⟩ :: Γ : Ctx VTy)[0]? =
      some ⟨.tensor A (kTy S R .aff B F), true⟩ := rfl
  rcases varCls_of_le hslotP (splitP_le_left hs) hV with hc | ⟨_, hT, -, -⟩
  swap
  · cases hT
  obtain ⟨rfl, rfl⟩ := vview_tensor hc
  have hslotK : (⟨kTy S R .aff B F, true⟩ :: ⟨A, true⟩ :: Γ₂ : Ctx VTy)[0]? =
      some ⟨.thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy S F)), true⟩ := rfl
  rcases der_letJ hB₂ (.inj₂ .unit) (Inst.cancelE (.var 0)) rfl (fun _ h => by cases h)
      (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) with
    ⟨j₁, ⟨Γ₃, S₅, X, hle₃, hM, hS₅⟩, hr₁⟩ | ⟨Γ₃, X, hle₃, hM⟩
  · -- `bind` or `[let]`: `cancel k` at a row below the clause's
    have hkj := kcancel_jr_aff hslotK hle₃ hM
    have hS₅S : RowLe S₅ S := by
      rcases hS₅ with rfl | ⟨B', rfl⟩
      · exact RowLe.nil S
      · exact JR.rowLe (hr₁.trans hr)
    cases hF : F.isTop
    · rw [show cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit by simp [cancelTy, hF]] at hkj
      have hle := (JR.rowLe hkj).trans hS₅S
      refine ⟨rfl, fun n i o hf => ?_⟩
      obtain ⟨o', hf', -⟩ := hle n i o (by rw [Row.find_append, hf]; rfl)
      exact ⟨o', hf'⟩
    · rw [show cancelTy S F = .top by simp [cancelTy, hF]] at hkj
      have := JR.rigid hkj rigid_top
      simp only [Jdg.comp.injEq] at this
      exact (effOf_ne_top S₅ X this).elim
  · -- `⊸E`: `cancel k` at a value judgement
    have hkj := kcancel_jr_aff hslotK hle₃ hM
    cases hF : F.isTop
    · rw [show cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit by simp [cancelTy, hF]] at hkj
      obtain ⟨hle, -⟩ := RowCls.reach hkj (S := F.rowOf ++ S) (Y := .unit)
        ⟨_, _, rfl, RowLe.refl _, .refl⟩
      refine ⟨rfl, fun n i o hf => ?_⟩
      obtain ⟨o', hf', -⟩ := hle n i o (by rw [Row.find_append, hf]; rfl)
      simp [Row.find] at hf'
    · rw [show cancelTy S F = .top by simp [cancelTy, hF]] at hkj
      have := JR.rigid hkj rigid_top
      cases this

/-- **`e7c` has no derivation at a row without `exnᵢ`** (decision D3).  `[handle] wait`'s body holds
`handle exnᵢ {…} (body (raise exnᵢ ()))`: the `[then]`'s premise puts `exnᵢ` in the cancel row of
`wait`, which `[sub]` up to the body keeps (cancel rows only grow); the `timeout` clause applies
`κ`'s cancel branch, at `F_{fs 0 ⊕ Σ} 1`, and the same-term rules read it at the clause's row `Σ`,
so `Σ` holds `exnᵢ`, and so does every row the program is read at. -/
theorem not_der_e7c {Δ : LifeCtx} {Γ : Ctx VTy} {nw ni : UInt32} {qi : Expr} (hne : nw ≠ ni)
    {S' : Row} {Y : VTy} (hS' : ∀ o ∈ S', o.n ≠ ni) :
    ¬ CDerives Δ Γ (Inst.e7cE nw ni (qualsVal [.aff]).1 qi) (.comp (CTy.effOf S' Y)) := by
  intro h
  -- `[handle] wait`
  obtain ⟨j₁, ⟨Γ₁, Γ₂, S, E, fs, A, R, -, hQ, hH, hM, -, rfl⟩, hr₁⟩ :=
    der_hndJ h nw (qualsVal [.aff]).1 (.pair (.lam (.inj₁ (.var 0))) (Inst.clausesE [Inst.timeoutClA]))
      (Inst.toResultE ni qi (Inst.bodyFE nw (raiseE (opArgE ni 0 .unit)))) rfl
  have hSS' : RowLe S S' := JR.rowLe hr₁
  have hE : [Qual.aff] = E.map Prod.fst := Targets.qualsVal_inj hQ
  obtain ⟨⟨q₁, A₁, B₁⟩, rfl⟩ : ∃ e, E = [e] := by
    rcases E with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE
    · exact ⟨e, rfl⟩
    · simp at hE
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE
  subst hE
  -- `[handle] exnᵢ`, then the `[then]`
  obtain ⟨j₂, ⟨Γ₃, Γ₄, S₂, E₂, fs₂, A₂, R₂, -, -, -, hM₂, -, rfl⟩, hr₂⟩ :=
    der_hndJ hM ni qi (.pair (.lam (.inj₁ (.var 0))) (Inst.clausesE [.lam (.inj₂ .unit)]))
      (Inst.bodyFE nw (raiseE (opArgE ni 0 .unit))) rfl
  have hS₂ : RowLe S₂ (Row.ofEff nw [(.aff, A₁, B₁)] 0 fs ++ S) := JR.rowLe hr₂
  obtain ⟨j₃, ⟨Γ₅, Γ₆, A₃, B₃, S₃, SM, SD, -, hMS, -, hfin, hMp, hDr, rfl⟩, hr₃⟩ :=
    der_thenJ hM₂ (.var 0) ((raiseE (opArgE ni 0 .unit)).shift 1 0)
      (bindE (performE (opArgE nw 0 .unit)) (.inj₂ .unit)) rfl
  have hS₃ : RowLe S₃ (Row.ofEff ni E₂ 0 fs₂ ++ S₂) := JR.rowLe hr₃
  -- `wait ()`'s row finds `wait`, below the `[then]`'s `M`'s row
  obtain ⟨S₄, oM₀, hf₄, ha₄, hS₄M⟩ : ∃ (S₄ : Row) (oM₀ : OpSig), Row.find S₄ nw 0 = some oM₀ ∧
      oM₀.abort = false ∧ RowLe S₄ SM := by
    rcases der_letJ hMp (.inj₂ .unit) (performE (opArgE nw 0 .unit)) rfl (fun _ h => by cases h)
        (fun _ h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) with
      ⟨j₄, ⟨Γ₇, S₇, X₇, -, hP, hS₇⟩, hr₄⟩ | ⟨Γ₇, X₇, -, hP⟩
    · obtain ⟨j₅, ⟨S₅, oM₀, hf₅, ha₅, rfl⟩, hr₅⟩ := der_performJ hP nw 0 .unit rfl
      have h57 : RowLe S₅ S₇ := JR.rowLe hr₅
      rcases hS₇ with rfl | ⟨B₇, rfl⟩
      · obtain ⟨o', hf', -⟩ := h57 nw 0 oM₀ hf₅
        simp [Row.find] at hf'
      · exact ⟨S₅, oM₀, hf₅, ha₅, h57.trans (JR.rowLe hr₄)⟩
    · obtain ⟨j₅, ⟨S₅, oM₀, hf₅, -, rfl⟩, hr₅⟩ := der_performJ hP nw 0 .unit rfl
      obtain ⟨hle, -⟩ := RowCls.reach hr₅ (S := S₅) (Y := oM₀.B) ⟨_, _, rfl, RowLe.refl _, .refl⟩
      obtain ⟨o', hf', -⟩ := hle nw 0 oM₀ hf₅
      simp [Row.find] at hf'
  obtain ⟨oM, hfM, hleM⟩ := hS₄M nw 0 oM₀ hf₄
  -- the finaliser's row finds `exnᵢ`
  obtain ⟨j₆, ⟨S₆, oD₀, B₆, hf₆, -, rfl⟩, hr₆⟩ := der_raiseJ hDr ni 0 .unit rfl
  obtain ⟨oD, hfD, -⟩ := JR.rowLe hr₆ ni 0 oD₀ hf₆
  -- `wait` from the `[then]` up to `[handle] wait`'s body
  obtain ⟨o₃, hf₃, hle₃⟩ := hMS nw 0 oM hfM
  obtain ⟨o₄, hf₄', hle₄⟩ := hS₃ nw 0 o₃ hf₃
  rw [Row.find_append, Row.find_ofEff_ne ni E₂ 0 fs₂ nw 0 hne, Option.none_or] at hf₄'
  obtain ⟨o₅, hf₅', hle₅⟩ := hS₂ nw 0 o₄ hf₄'
  rw [Row.find_append, show Row.find (Row.ofEff nw [(.aff, A₁, B₁)] 0 fs) nw 0 =
    some ⟨nw, 0, .aff, A₁, B₁, fs 0⟩ by simp [Row.ofEff, Row.find], Option.some_or] at hf₅'
  cases hf₅'
  have hsig : oM₀.Sig ⟨nw, 0, .aff, A₁, B₁, fs 0⟩ :=
    hleM.1.trans (hle₃.1.trans (hle₄.1.trans hle₅.1))
  have hB₁ : B₁.isZero = false := by
    have := hsig.abort_eq
    rw [ha₄] at this
    simpa [OpSig.abort] using this.symm
  have hcap₀ : capB oM₀.q oM₀.B = true := by
    rw [hsig.capB_eq]; simp [capB, hB₁]
  have hcapM : capB oM.q oM.B = true := hleM.1.capB_eq ▸ hcap₀
  have hcap₃ : capB o₃.q o₃.B = true := hle₃.1.capB_eq ▸ hcapM
  have hcap₄ : capB o₄.q o₄.B = true := hle₄.1.capB_eq ▸ hcap₃
  -- `exnᵢ` in the cancel row of `wait`, or that cancel row `⊤`
  have h₃₄ : FinLe o₃.fin o₄.fin := hle₄.2 hcap₃
  have h₄₅ : FinLe o₄.fin (fs 0) := hle₅.2 hcap₄
  have hfs : (fs 0).isTop = true ∨ ∃ o₆, Row.find (fs 0).rowOf ni 0 = some o₆ := by
    have hT := hfin nw 0 oM o₃ hfM hf₃ hcapM
    rw [ThenLe] at hT
    rcases hT with hT | ⟨-, -, hT⟩
    · exact .inl (finLe_top_top h₄₅ (finLe_top_top h₃₄ hT))
    · obtain ⟨o', hf', -⟩ := hT ni 0 oD hfD
      rcases finLe_find h₃₄ hf' with h₄ | ⟨o'', hf''⟩
      · exact .inl (finLe_top_top h₄₅ h₄)
      · exact finLe_find h₄₅ hf''
  -- the clause reads `κ`'s cancel at its row
  rcases der_pair hH _ _ rfl with ⟨Γ₇, Γ₈, X₁, X₂, -, -, hcl, hc₁⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨-, rfl⟩ := vview_tensor hc₁
  rcases der_pair hcl _ _ rfl with ⟨Γ₉, Γ₁₀, X₃, X₄, -, hcan, -, hc₂⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32, Inst.timeoutClA] at he
  obtain ⟨rfl, -⟩ := vview_tensor (show VView (.tensor X₃ X₄)
    (.tensor (clauseTy S R (.aff, A₁, B₁) (fs 0)) .unit) from hc₂)
  obtain ⟨hnt, hfS⟩ := timeoutCl_finds hB₁ hcan
  rcases hfs with htop | ⟨o₆, hf₆'⟩
  · rw [hnt] at htop; cases htop
  · obtain ⟨o₇, hf₇⟩ := hfS ni 0 o₆ hf₆'
    obtain ⟨o₈, hf₈, -⟩ := hSS' ni 0 o₇ hf₇
    obtain ⟨hm₈, hn₈, -⟩ := Row.find_mem hf₈
    exact hS' o₈ hm₈ hn₈

end Targets.Rej

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont Heap performE raiseE hndE hndVal opPayload cancelVal kappaC kappaCell
  kappaCBody kappaAt capTag freeE ubindE cfinE ccatchE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt lookEnd)

section Rejection
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- A closed program typed at `J₁` at a returner, no driven one, is typed by the tied kernel at the
returner's reading at the empty row environment. -/
theorem derAt_F_J₁ {e : Expr} {ε : ORow} {A : OVTy} (h : (𝕁).der [] e ((𝕁).F ε A))
    (hd : ∀ M, e ≠ driveE M) :
    CDerivesAt Ξ LifeCtx.empty [] e
      (.comp (CTy.effOf (orowRF.den Ξ ε (fun _ => [])) (A.den fun _ => []))) := by
  obtain ⟨-, ⟨Θ, hΘ, hd'⟩ | ⟨-, M, he, -⟩⟩ := h
  · have h' := hd'.2.2 (fun _ => []) (models_anyCon_nil hΘ) (envAt_nil Ξ) (fun _ => none)
      (closingAt_none (fun s hs => absurd hs List.not_mem_nil))
    rw [fillS_none] at h'
    exact h'
  · exact absurd he (hd M)

/-- A row lacking a label has, at the empty row environment, no operation of the label's name. -/
theorem names_den_of_lacks {ε : ORow} {l : (orowAlg Ξ).Lab} (hL : (𝕁).Lacks ε l) :
    ∀ o ∈ orowRF.den Ξ ε (fun _ => []), o.n ≠ l.1 := by
  intro o ho
  have hops : o ∈ ε.ops := by
    cases ht : ε.tail with
    | none => simpa [orowRF, ht] using ho
    | some ρ => simpa [orowRF, ht] using ho
  exact names_of_lacks hL o hops

/-- **E7c is rejected at `J₁`** (decision D3): at every row without `exnᵢ`, `e7c` has no typing. -/
theorem not_der_e7c_J₁ {lw li : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)])
    (hne : lw.1 ≠ li.1) {ε : ORow} {A : OVTy} (hL : (𝕁).Lacks ε li) :
    ¬ (𝕁).der [] ((𝕁).e7c lw li) ((𝕁).F ε A) := by
  intro h
  have hd := derAt_F_J₁ h (fun M => by rw [e7c_val]; exact handleK_ne_drive _ _ _ _ _ _)
  rw [e7c_val, qsOf_eq hlw] at hd
  simp only [List.map_cons, List.map_nil] at hd
  exact Rej.not_der_e7c hne (names_den_of_lacks hL) hd.toCDerives

/-- **At a row with `exnᵢ`, `e7c` is typed at `J₁`**: its finaliser's raise reaches the context's
instance of `exnᵢ` (decision D1).  So E7c's rejection holds at the rows without `exnᵢ`, and at no
other. -/
theorem der_e7c_lift_J₁ {lw li : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {qi : Qual}
    (hli : Ξ li.1 = [(qi, .unit, .zero)]) (hqi : qi ≠ .lin) (hne : lw.1 ≠ li.1) :
    (𝕁).der [] ((𝕁).e7c lw li) ((𝕁).F ((𝕁).EA.lift li) (𝕁).ty7) := by
  have hd := d_e7c_lift hlw hli hqi hne
  rw [e7c_val]
  refine der_J₁_closedRow (A := .sum (.sum boolT .unit) .unit) rfl (rowAt_rowOf li)
    (by simpa using closedAt_of_derives hd.toCDerives) ?_
  show CDerivesAt Ξ LifeCtx.empty [] _ (.comp (CTy.effOf (Row.ofEff li.1 (Ξ li.1) 0) _))
  rwa [List.append_nil, ← hli] at hd

end Rejection

/-! ### The runs -/

/-- `timeout`'s handler value at the name `nw`, its `wait` affine. -/
def tmH (nw : UInt32) : Val :=
  hndVal nw (qualsVal [.aff]) ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [timeoutClA], .pair .lam .unit⟩

theorem timeoutHE_aff (nw : UInt32) (M : Expr) : timeoutHE nw qA M = hndE (tmH nw) M := rfl

/-- Around the allocation of `κ`'s cell, after `timeout`'s catch of `wait` in `K`. -/
def tmKA (nw : UInt32) (K : Kont) : Kont :=
  .appR timeoutClA (.pairR Val.unit (.appR (.lam (kappaCBody true (tmH nw) K)) .hole))

/-- Around the release of `κ`'s cell, when the clause cancels `κ`. -/
def tmKF (K : Kont) : Kont := (bindK (.inj₂ .unit)).comp (Kont.seq .hole (kCanE K))

/-- **`timeout`'s catch of `wait`**: the clause applied to `()` and `κ`, whose cell is still to be
allocated. -/
theorem quiet_tmHop (nw : UInt32) (K : Kont) (hK : K.HasHnd nw = false) :
    Quiet (ℍ := ℍ) (hndE (tmH nw) (K.plug (performE (.val (opPayload nw 0 Val.unit)))))
      ((tmKA nw K).plug (allocE Val.unit)) := by
  have hk : kappaAt (capTag (qualsVal [.aff]).1 (0 : UInt32).toNat) (tmH nw) K =
      kappaCell true (tmH nw) K := by
    simp [capTag, qualsVal, Qual.tag, kappaAt, Val.pair, Val.i32]
  have hh : ∀ μ, Head (ℍ := ℍ) μ (hndE (tmH nw) (K.plug (performE (.val (opPayload nw 0 Val.unit)))))
      μ (.app (.val ⟨timeoutClA, .lam⟩) (.pair (.val Val.unit) (kappaCell true (tmH nw) K))) := by
    intro μ
    have h := Head.hop (ℍ := ℍ) μ nw 0 (qualsVal [.aff]) ⟨.lam (.inj₁ (.var 0)), .lam⟩
      ⟨clausesE [timeoutClA], .pair .lam .unit⟩ ⟨timeoutClA, .lam⟩ Val.unit K
      (clauseAt_clausesE [timeoutClA] 0 .lam rfl) hK
    simp only [tmH] at hk ⊢
    rwa [hk] at h
  exact Quiet.head (ℍ := ℍ) .hole hh rfl rfl

/-- **From the cell's allocation, the clause cancels `κ`**: `κ` at its cell `ℓ`, the clause's
β-step and pair, and `κ`'s cancel branch up to the release of `ℓ`. -/
theorem quiet_tmCancel (nw : UInt32) (K : Kont) (hKc : closedAt 0 (K.plug .unit) = true) (ℓ : Loc) :
    Quiet (ℍ := ℍ) ((tmKA nw K).plug (.val (Val.loc ℓ)))
      ((tmKF K).plug (freeE (.val (Val.loc ℓ)))) := by
  have hH : closedAt 0 (tmH nw).1 = true := rfl
  have hκc : closedAt 0 (kappaC true ℓ (tmH nw) K) = true := closedAt_kappaC true ℓ hH hKc
  let κ : Val := ⟨kappaC true ℓ (tmH nw) K, isVal_kappaC true ℓ (tmH nw) K⟩
  -- `κ` at its cell
  have hb₀ := Quiet.head (ℍ := ℍ) (.appR timeoutClA (.pairR Val.unit .hole))
    (fun μ => Head.beta μ (kappaCBody true (tmH nw) K) (Val.loc ℓ)) rfl rfl
  rw [kappaCBody_subst] at hb₀
  refine hb₀.trans ?_
  -- the clause's β-step and its pair
  have h₁ := quiet_beta (ℍ := ℍ) .hole (.letpair (.var 0) (bindE (cancelE (.var 0)) (.inj₂ .unit)))
    (Val.pair Val.unit κ)
  have e₁ : Expr.subst 0 (Val.pair Val.unit κ) (.letpair (.var 0) (bindE (cancelE (.var 0)) (.inj₂ .unit))) =
      .letpair (.val (Val.pair Val.unit κ)) (bindE (cancelE (.var 0)) (.inj₂ .unit)) := by
    simp [Expr.subst, bindE, cancelE, Val.pair]
  rw [e₁] at h₁
  refine (show Quiet (ℍ := ℍ) (Kont.hole.plug (.app (.val ⟨timeoutClA, .lam⟩)
    (.pair (.val Val.unit) (kappaC true ℓ (tmH nw) K)))) _ from h₁).trans ?_
  have h₂ := quiet_letpair (ℍ := ℍ) .hole Val.unit κ (bindE (cancelE (.var 0)) (.inj₂ .unit))
  have e₂ : Expr.subst 0 Val.unit (Expr.subst 0 (κ.shift 1 0) (bindE (cancelE (.var 0)) (.inj₂ .unit))) =
      (bindK (.inj₂ .unit)).plug (.app (kappaC true ℓ (tmH nw) K) (.val (Val.inj₂ .unit))) := by
    rw [val_shift_closed (v := κ) hκc]
    have hs : Expr.subst 0 Val.unit (kappaC true ℓ (tmH nw) K) = kappaC true ℓ (tmH nw) K :=
      subst_closedAt _ Val.unit hκc (le_refl _)
    simp only [Expr.subst, bindE, cancelE, bindK, Kont.plug, Expr.val, Val.lam, κ, ite_true, hs]
    rfl
  rw [e₂] at h₂
  refine h₂.trans ?_
  -- `κ`'s cancel branch, to the release of its cell
  have h₃ := (kappaC_cancel_parts (ℍ := ℍ) ℓ (tmH nw) K).1.plug (bindK (.inj₂ .unit))
  rw [← Kont.plug_comp] at h₃
  exact h₃

section Steps
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **`timeout`'s catch of `wait`, and the clause's cancel of `κ`**: from `K₀[timeout K[wait ()]]`,
at every memory with finitely many cells, the complete runs are those from the cancel's start
`K₀[□; return (inr ())][cancelOf K]`, at the same memory: the catch allocates `κ`'s cell at a free
location, and the cancel releases it. -/
theorem obsFrom_tmCatch (R : (𝕁).Runner) {μ : Heap} (hf : FinDom μ) {s : R.St} (K₀ K : Kont)
    (nw : UInt32) (hK : K.HasHnd nw = false) (hKc : closedAt 0 (K.plug .unit) = true) (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((μ, K₀.plug (hndE (tmH nw) (K.plug (performE (.val (opPayload nw 0 Val.unit)))))), s)
      w tr ↔
    (𝕁).ObsFrom R ((μ, (K₀.comp (bindK (.inj₂ .unit))).plug (Targets.cancelOf K)), s) w tr := by
  refine (obsFrom_quiet_iff _ ((quiet_tmHop nw K hK).plug K₀) w tr).trans ?_
  rw [← Kont.plug_comp]
  refine obsFrom_alloc_iff _ (K₀.comp (tmKA nw K)) Val.unit (exists_fresh_of_finDom hf)
    (Q := fun w tr => (𝕁).ObsFrom R ((μ, (K₀.comp (bindK (.inj₂ .unit))).plug (Targets.cancelOf K)), s)
      w tr) (fun ℓ hℓ w tr => ?_) w tr
  rw [Kont.plug_comp]
  refine (obsFrom_quiet_iff _ ((quiet_tmCancel nw K hKc ℓ).plug K₀) w tr).trans ?_
  rw [← Kont.plug_comp]
  refine (obsFrom_mstep_iff _ (Head.free _ ℓ Val.unit (Heap.upd_same _ _ _)) rfl
    (by rw [labelOf_tau_of rfl]; rfl) w tr).trans ?_
  rw [del_upd_fresh hℓ]
  have h₄ := (kappaC_cancel_parts (ℍ := ℍ) ℓ (tmH nw) K).2.plug (K₀.comp (bindK (.inj₂ .unit)))
  have e : (K₀.comp (bindK (.inj₂ .unit))).plug ((Kont.seq .hole (kCanE K)).plug (.val Val.unit)) =
      (K₀.comp (tmKF K)).plug (.val Val.unit) := by
    rw [Kont.plug_comp, Kont.plug_comp, tmKF, Kont.plug_comp]
  rw [e] at h₄
  exact obsFrom_quiet_iff _ h₄ w tr

/-- A raise in a context is no value. -/
theorem plug_raise_not_val (K : Kont) (p : Val) : ¬ IsVal (K.plug (raiseE (.val p))) :=
  fun h => plug_raise_ne_val K p ⟨_, h⟩ rfl

/-- **`[finalise-cancel]`**: the cancel reaches a finaliser frame and fires its finaliser, showing
the finaliser. -/
theorem obsFrom_ufinC (R : (𝕁).Runner) {μ : Heap} {s : R.St} (K₀ K : Kont) (N D : Val)
    (err : Option Val) (hK : K.Catches 0 = false) (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((μ, K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (cancelVal err)))))), s)
      w tr ↔
    ∃ tr', tr = .fire (finE D.1) :: tr' ∧
      (𝕁).ObsFrom R ((μ, K₀.plug (cfinE (cancelVal err) (.app (.val D) (.val .unit)))), s) w tr' := by
  rw [obsFrom_head_iff R (fun μ => Head.ufinC μ N D err K hK) rfl w tr,
    labelOf_fire (plug_raise_not_val K _)]
  rfl

/-- **`[cfin-ret]`**: the finaliser returned; its end shows no error. -/
theorem obsFrom_cfret (R : (𝕁).Runner) {μ : Heap} {s : R.St} (K₀ : Kont) (err : Option Val)
    (v : Val) (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((μ, K₀.plug (cfinE (cancelVal err) (.val v))), s) w tr ↔
    ∃ tr', tr = .finEnd none :: tr' ∧
      (𝕁).ObsFrom R ((μ, K₀.plug (raiseE (.val (cancelVal err)))), s) w tr' := by
  rw [obsFrom_head_iff R (fun μ => Head.cfret μ err v) rfl w tr, labelOf_cfret]
  rfl

/-- **`[cfin-raise]`**: the finaliser raised; its end shows the error, and the cancel keeps the first
one. -/
theorem obsFrom_cferr (R : (𝕁).Runner) {μ : Heap} {s : R.St} (K₀ K : Kont) (err : Option Val)
    {m : UInt32} (hm : m ≠ 0) (j : UInt32) (v : Val) (hK : K.Catches m = false) (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((μ, K₀.plug (cfinE (cancelVal err) (K.plug (raiseE (.val (opPayload m j v)))))), s)
      w tr ↔
    ∃ tr', tr = .finEnd (errOf orowRF Ξ m j v) :: tr' ∧
      (𝕁).ObsFrom R ((μ, K₀.plug (raiseE (.val (cancelVal (BoCa.BoLo.errNext err m j v))))), s) w tr' := by
  rw [obsFrom_head_iff R (fun μ => Head.cferr μ err m j v K hm hK) rfl w tr, labelOf_cferr _ _ hm]
  rfl

/-- A label's raise, read at the labels: the label, its operation and its argument. -/
theorem errOf_lab (l : (orowAlg Ξ).Lab) (j : UInt32) (v : Val) :
    errOf orowRF Ξ l.1 j v = some (l, j.toNat, OVal.ofVal v) := by
  obtain ⟨l', hl', hn⟩ := errOf_named (RF := orowRF) (Ξ := Ξ) (m := l.1) ⟨l, rfl⟩ j v
  rw [hl']
  have : l' = l := Subtype.ext hn
  rw [this]

end Steps

/-! #### E7a -/

/-- `e7a`'s cancelled region: the finaliser frame and `□; return tt`. -/
abbrev Ka : Kont := (thenK (.var 0) .unit).comp (bindK (.inj₂ .unit))

section E7aRun
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **`e7a`'s complete runs**, from every memory with finitely many cells: each answers `inr ()`,
showing the finaliser's fire and its end with no error. -/
theorem obsFrom_e7a (nw : UInt32) {μ : Heap} (hf : FinDom μ) (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, e7aE nw qA), ()) w tr ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧ tr = [.fire .unit, .finEnd none] := by
  -- the finaliser's end and the cancel's
  have hT : ∀ tr', (𝕁).ObsFrom (𝕁).R₀ ((μ, ((bindK (.inj₂ .unit)).comp (ccatchK .hole)).plug
      (cfinE (cancelVal none) (.app (.val ⟨.lam .unit, .lam⟩) (.val .unit)))), ()) w tr' ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧ tr' = [.finEnd none] := by
    intro tr'
    have q₁ : Quiet (ℍ := ℍ) (((bindK (.inj₂ .unit)).comp (ccatchK .hole)).plug
          (cfinE (cancelVal none) (.app (.val ⟨.lam .unit, .lam⟩) (.val .unit))))
        (((bindK (.inj₂ .unit)).comp (ccatchK .hole)).plug (cfinE (cancelVal none) (.val Val.unit))) :=
      (quiet_beta (ℍ := ℍ) (.appR (.app (.prim .cfin) (cancelVal none).1) .hole) .unit Val.unit).plug
        ((bindK (.inj₂ .unit)).comp (ccatchK .hole))
    refine (obsFrom_quiet_iff _ q₁ w tr').trans ?_
    refine (obsFrom_cfret (𝕁).R₀ (s := ()) _ none Val.unit w tr').trans ?_
    have q₂ := Quiet.head (ℍ := ℍ) (bindK (.inj₂ .unit)) (fun μ => Head.cancel μ .hole rfl) rfl rfl
    have q₃ := quiet_beta (ℍ := ℍ) .hole (.inj₂ .unit) Val.unit
    have hv : ∀ tr'', (𝕁).ObsFrom (𝕁).R₀ ((μ, ((bindK (.inj₂ .unit)).comp (ccatchK .hole)).plug
        (raiseE (.val (cancelVal none)))), ()) w tr'' ↔ w.1 = (Val.inj₂ Val.unit).1 ∧ tr'' = [] :=
      fun tr'' => (obsFrom_quiet_iff _ (q₂.trans q₃) w tr'').trans
        (obsFrom_val_iff _ (Val.inj₂ Val.unit) w tr'')
    constructor
    · rintro ⟨tr'', rfl, h⟩
      obtain ⟨hw, rfl⟩ := (hv tr'').1 h
      exact ⟨hw, rfl⟩
    · rintro ⟨hw, rfl⟩
      exact ⟨[], rfl, (hv []).2 ⟨hw, rfl⟩⟩
  refine (obsFrom_tmCatch (𝕁).R₀ hf (s := ()) .hole Ka nw rfl rfl w tr).trans ?_
  refine (obsFrom_ufinC (𝕁).R₀ (s := ()) ((bindK (.inj₂ .unit)).comp (ccatchK .hole))
    (bindK (.inj₂ .unit)) ⟨.lam (.var 0), .lam⟩ ⟨.lam .unit, .lam⟩ none rfl w tr).trans ?_
  constructor
  · rintro ⟨tr', rfl, h⟩
    obtain ⟨hw, rfl⟩ := (hT tr').1 h
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨_, rfl, (hT _).2 ⟨hw, rfl⟩⟩

/-- **`e7a`'s run**: it answers `inr ()`, showing the frozen finaliser's fire and its end. -/
theorem runsTo_e7a {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e7a lw) ((𝕁).inr (𝕁).unitV)
      [.fire ((𝕁).ret (𝕁).unitV), .finEnd none] := by
  rw [e7a_val, qsOf_Ew hlw]
  exact runsTo_of_obsFrom _ (v := Val.inj₂ Val.unit) fun w tr => obsFrom_e7a lw.1 finDom_empty w tr

end E7aRun

/-! #### E7b -/

/-- A finaliser frame whose finaliser raises `exn` at the name `no`, and `□; return tt`. -/
abbrev Kr (no : UInt32) : Kont :=
  (thenK (.var 0) (raiseE (opArgE no 0 .unit))).comp (bindK (.inj₂ .unit))

/-- `toResult`'s handler frame at the name `no`. -/
abbrev trK (no : UInt32) (q : Qual) : Kont :=
  handleK no (qualsVal [q]).1 (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]

/-- The finaliser `λ_. raise exn ()` of a `Kr` frame. -/
abbrev raiseFin (no : UInt32) : Val := ⟨.lam ((raiseE (opArgE no 0 .unit)).shift 1 0), .lam⟩

section E7bRun
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **The kept raise, re-raised at the canceller and caught by `toResult`**: from the cancel's end
keeping a raise of `exn`, the raise passes `K₁`, which catches nothing of it, and `toResult`'s
clause answers `inr ()`, showing nothing. -/
theorem obsFrom_reraise_toResult {no : UInt32} {q : Qual} (K₀ K₁ : Kont) (hK₁ : K₁.Catches no = false)
    {μ : Heap} (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, ((K₀.comp (trK no q)).comp (K₁.comp ((bindK (.inj₂ .unit)).comp
      (ccatchK .hole)))).plug (raiseE (.val (cancelVal (some (opPayload no 0 Val.unit)))))), ()) w tr ↔
    (𝕁).ObsFrom (𝕁).R₀ ((μ, K₀.plug (.val (Val.inj₂ Val.unit))), ()) w tr := by
  have q₁ : Quiet (ℍ := ℍ) (((K₀.comp (trK no q)).comp (K₁.comp ((bindK (.inj₂ .unit)).comp
      (ccatchK .hole)))).plug (raiseE (.val (cancelVal (some (opPayload no 0 Val.unit))))))
      ((K₀.comp (trK no q)).plug ((K₁.comp (bindK (.inj₂ .unit))).plug
        (raiseE (.val (opPayload no 0 Val.unit))))) := by
    have h := (Quiet.head (ℍ := ℍ) .hole (fun μ => Head.creraise μ (opPayload no 0 Val.unit) .hole rfl)
      rfl rfl).plug ((K₀.comp (trK no q)).comp (K₁.comp (bindK (.inj₂ .unit))))
    simp only [Kont.plug_comp] at h ⊢
    exact h
  have hK : (K₁.comp (bindK (.inj₂ .unit))).Catches no = false := by
    rw [catches_comp]; simp [hK₁, bindK, Kont.Catches]
  have q₂ : Quiet (ℍ := ℍ) ((K₀.comp (trK no q)).plug ((K₁.comp (bindK (.inj₂ .unit))).plug
      (raiseE (.val (opPayload no 0 Val.unit))))) (K₀.plug (.val (Val.inj₂ Val.unit))) := by
    have h₁ := (Quiet.head (ℍ := ℍ) .hole (fun μ => Head.hunwind μ no 0 (qualsVal [q])
      ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩
      ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit (K₁.comp (bindK (.inj₂ .unit)))
      (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl) hK) rfl rfl).plug K₀
    have h₂ := quiet_beta (ℍ := ℍ) K₀ (.inj₂ .unit) Val.unit
    rw [Kont.plug_comp]
    exact h₁.trans h₂
  exact obsFrom_quiet_iff _ (q₁.trans q₂) w tr

/-- **A finaliser that raises a label, run by a cancel**: from its fire, the complete runs show
its end with the label's error, then those of the cancel's end keeping the first error. -/
theorem obsFrom_finRaise (K₁ : Kont) (err : Option Val) (lo : (orowAlg Ξ).Lab) {μ : Heap} (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, K₁.plug (cfinE (cancelVal err)
      (.app (.val (raiseFin lo.1)) (.val .unit)))), ()) w tr ↔
    ∃ tr', tr = .finEnd (some (lo, 0, (𝕁).unitV)) :: tr' ∧
      (𝕁).ObsFrom (𝕁).R₀ ((μ, K₁.plug (raiseE (.val (cancelVal
        (BoCa.BoLo.errNext err lo.1 0 Val.unit))))), ()) w tr' := by
  have q₁ : Quiet (ℍ := ℍ) (K₁.plug (cfinE (cancelVal err) (.app (.val (raiseFin lo.1)) (.val .unit))))
      (K₁.plug (cfinE (cancelVal err) (Kont.hole.plug (raiseE (.val (opPayload lo.1 0 Val.unit)))))) :=
    (quiet_beta (ℍ := ℍ) (.appR (.app (.prim .cfin) (cancelVal err).1) .hole)
      ((raiseE (opArgE lo.1 0 .unit)).shift 1 0) Val.unit).plug K₁
  refine (obsFrom_quiet_iff _ q₁ w tr).trans ?_
  refine (obsFrom_cferr (𝕁).R₀ (s := ()) K₁ .hole err lo.2.1 0 Val.unit rfl w tr).trans ?_
  rw [errOf_lab]
  rfl

/-- **`e7b`'s complete runs**, from every memory with finitely many cells: each answers `inr ()`,
showing the finaliser's fire and its end with the raise of `exn`, which the cancel re-raises at the
canceller, inside `toResult`. -/
theorem obsFrom_e7b (lw lo : (orowAlg Ξ).Lab) (q : Qual) {μ : Heap} (hf : FinDom μ) (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, e7bE lw.1 lo.1 qA (qualsVal [q]).1), ()) w tr ↔
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
  refine (obsFrom_tmCatch (𝕁).R₀ hf (s := ()) (trK lo.1 q) (Kr lo.1) lw.1 rfl rfl w tr).trans ?_
  refine (obsFrom_ufinC (𝕁).R₀ (s := ()) (((Kont.hole.comp (trK lo.1 q)).comp
    (Kont.hole.comp ((bindK (.inj₂ .unit)).comp (ccatchK .hole))))) (bindK (.inj₂ .unit)) ⟨.lam (.var 0), .lam⟩
    (raiseFin lo.1) none rfl w tr).trans ?_
  constructor
  · rintro ⟨tr', rfl, h⟩
    obtain ⟨hw, rfl⟩ := (hT tr').1 h
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨_, rfl, (hT _).2 ⟨hw, rfl⟩⟩

/-- **`e7b`'s run**: it answers `inr ()`, showing the finaliser's fire and its end with the raise of
`exn`, which the cancel re-raises at the canceller. -/
theorem runsTo_e7b {lw lo : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {q : Qual}
    (hlo : Ξ lo.1 = [(q, .unit, .zero)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e7b lw lo) ((𝕁).inr (𝕁).unitV) ((𝕁).finTr lo) := by
  rw [e7b_val, qsOf_Ew hlw, qsOf_eq hlo]
  exact runsTo_of_obsFrom _ (v := Val.inj₂ Val.unit) fun w tr => obsFrom_e7b lw lo q finDom_empty w tr

end E7bRun

/-! #### E7d -/

section E7dRun
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **`e7d`'s complete runs**, from every memory with finitely many cells: the cancel fires the
inner finaliser, which raises `exn_a`, then the outer one, which raises `exn_b`; the first error is
kept and re-raised at the canceller, where it passes `toResult` of `exn_b` and `toResult` of `exn_a`
catches it.  Each answers `inr ()`. -/
theorem obsFrom_e7d (lw la lb : (orowAlg Ξ).Lab) (hab : la.1 ≠ lb.1) (qa qb : Qual) {μ : Heap}
    (hf : FinDom μ) (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, e7dE lw.1 la.1 lb.1 qA (qualsVal [qa]).1 (qualsVal [qb]).1), ()) w tr ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧ tr = (𝕁).finTr la ++ (𝕁).finTr lb := by
  have hKb : (Kont.hole.comp (trK lb.1 qb)).Catches la.1 = false := by
    simp [trK, handleK, hndValE, Kont.comp, Kont.Catches, Ne.symm hab]
  -- the outer finaliser, run with `exn_a` kept, and the kept `exn_a` re-raised
  have hT₂ : ∀ tr', (𝕁).ObsFrom (𝕁).R₀ ((μ, ((Kont.hole.comp (trK la.1 qa)).comp
      ((Kont.hole.comp (trK lb.1 qb)).comp ((bindK (.inj₂ .unit)).comp (ccatchK .hole)))).plug
        (cfinE (cancelVal (some (opPayload la.1 0 Val.unit)))
          (.app (.val (raiseFin lb.1)) (.val .unit)))), ()) w tr' ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧ tr' = [.finEnd (some (lb, 0, (𝕁).unitV))] := by
    intro tr'
    refine (obsFrom_finRaise _ (some (opPayload la.1 0 Val.unit)) lb w tr').trans ?_
    have hv := fun (tr'' : List (𝕁).Event) => (obsFrom_reraise_toResult (no := la.1) (q := qa) .hole
      (Kont.hole.comp (trK lb.1 qb)) hKb (μ := μ) w tr'').trans
        (obsFrom_val_iff _ (Val.inj₂ Val.unit) w tr'')
    constructor
    · rintro ⟨tr'', rfl, h⟩
      obtain ⟨hw, rfl⟩ := (hv tr'').1 h
      exact ⟨hw, rfl⟩
    · rintro ⟨hw, rfl⟩
      exact ⟨[], rfl, (hv []).2 ⟨hw, rfl⟩⟩
  -- the inner finaliser, then the outer one fired
  have hT₁ : ∀ tr', (𝕁).ObsFrom (𝕁).R₀ ((μ, ((((Kont.hole.comp (trK la.1 qa)).comp
      ((Kont.hole.comp (trK lb.1 qb)).comp ((bindK (.inj₂ .unit)).comp (ccatchK .hole))))).comp
        (thenK (.var 0) (raiseE (opArgE lb.1 0 .unit)))).plug
        (cfinE (cancelVal none) (.app (.val (raiseFin la.1)) (.val .unit)))), ()) w tr' ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧
        tr' = .finEnd (some (la, 0, (𝕁).unitV)) :: (𝕁).finTr lb := by
    intro tr'
    refine (obsFrom_finRaise _ none la w tr').trans ?_
    have hfire := fun (tr'' : List (𝕁).Event) => obsFrom_ufinC (𝕁).R₀ (μ := μ) (s := ())
      ((Kont.hole.comp (trK la.1 qa)).comp
        ((Kont.hole.comp (trK lb.1 qb)).comp ((bindK (.inj₂ .unit)).comp (ccatchK .hole))))
      .hole ⟨.lam (.var 0), .lam⟩ (raiseFin lb.1) (some (opPayload la.1 0 Val.unit)) rfl w tr''
    constructor
    · rintro ⟨tr'', rfl, h⟩
      rw [Kont.plug_comp] at h
      obtain ⟨tr₃, rfl, h₃⟩ := (hfire tr'').1 h
      obtain ⟨hw, rfl⟩ := (hT₂ tr₃).1 h₃
      exact ⟨hw, rfl⟩
    · rintro ⟨hw, rfl⟩
      refine ⟨_, rfl, ?_⟩
      rw [Kont.plug_comp]
      exact (hfire _).2 ⟨_, rfl, (hT₂ _).2 ⟨hw, rfl⟩⟩
  refine (obsFrom_tmCatch (𝕁).R₀ hf (s := ()) ((trK la.1 qa).comp (trK lb.1 qb))
    ((thenK (.var 0) (raiseE (opArgE lb.1 0 .unit))).comp (Kr la.1)) lw.1 rfl rfl w tr).trans ?_
  refine (obsFrom_ufinC (𝕁).R₀ (s := ()) ((((Kont.hole.comp (trK la.1 qa)).comp
      ((Kont.hole.comp (trK lb.1 qb)).comp ((bindK (.inj₂ .unit)).comp (ccatchK .hole))))).comp
        (thenK (.var 0) (raiseE (opArgE lb.1 0 .unit)))) (bindK (.inj₂ .unit)) ⟨.lam (.var 0), .lam⟩
    (raiseFin la.1) none rfl w tr).trans ?_
  constructor
  · rintro ⟨tr', rfl, h⟩
    obtain ⟨hw, rfl⟩ := (hT₁ tr').1 h
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨_, rfl, (hT₁ _).2 ⟨hw, rfl⟩⟩

/-- **`e7d`'s run**: it answers `inr ()`, showing the inner finaliser's fire and end with `exn_a`,
then the outer one's with `exn_b`; the first error is kept and re-raised at the canceller. -/
theorem runsTo_e7d {lw la lb : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {qa qb : Qual}
    (hla : Ξ la.1 = [(qa, .unit, .zero)]) (hlb : Ξ lb.1 = [(qb, .unit, .zero)]) (hab : la.1 ≠ lb.1) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e7d lw la lb) ((𝕁).inr (𝕁).unitV) ((𝕁).finTr la ++ (𝕁).finTr lb) := by
  rw [e7d_val, qsOf_Ew hlw, qsOf_eq hla, qsOf_eq hlb]
  exact runsTo_of_obsFrom _ (v := Val.inj₂ Val.unit) fun w tr =>
    obsFrom_e7d lw la lb hab qa qb finDom_empty w tr

end E7dRun

/-! ### E7 -/

section E7
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **E7's labels**: a `wait` and two `exn` labels, at a rich context. -/
theorem labelsAt_E7 (hΞ : AdmEff Ξ) :
    ∃ ls, (𝕁).LabelsAt [(𝕁).sigWait, (𝕁).sigExn, (𝕁).sigExn] ls := by
  obtain ⟨lw, -, -, hlw, -⟩ := rich_labs hΞ.2.2 (E := [(.aff, .unit, .unit)]) (by simp [eSigs])
  obtain ⟨la, lb, hab, hla, hlb⟩ := rich_labs hΞ.2.2 (E := [(.aff, .unit, .zero)]) (by simp [eSigs])
  have hwa : lw ≠ la := lab_ne_of_sig (by rw [hlw, hla]; simp)
  have hwb : lw ≠ lb := lab_ne_of_sig (by rw [hlw, hlb]; simp)
  refine ⟨[lw, la, lb], rfl, ?_, fun k h₁ _ => ?_⟩
  · refine List.nodup_cons.mpr ⟨fun h => ?_, List.nodup_cons.mpr
      ⟨fun h => hab (List.mem_singleton.mp h), List.nodup_singleton _⟩⟩
    rcases List.mem_cons.mp h with h | h
    · exact hwa h
    · exact hwb (List.mem_singleton.mp h)
  · match k, h₁ with
    | 0, _ => exact (sig_wait_iff hΞ.1 lw).mpr hlw
    | 1, _ => exact (sig_exn_iff la).mpr ⟨.aff, hla, by decide⟩
    | 2, _ => exact (sig_exn_iff lb).mpr ⟨.aff, hlb, by decide⟩

/-- **E7, abandoning a suspension, at `J₁`**, at every admissible effect context: `e7a`, `e7b` and
`e7d` typed and run, and `e7c` rejected at every row without its inner label (decision D3). -/
theorem cancelPolicy_J₁ (hΞ : AdmEff Ξ) : (𝕁).CancelPolicy := by
  refine ⟨labelsAt_E7 hΞ, fun ls hls lw la lb hlsEq => ?_⟩
  subst hlsEq
  have hlw := (sig_wait_iff hΞ.1 lw).mp (hls.2.2 0 (by simp) (by simp))
  obtain ⟨qa, hla, hqa⟩ := (sig_exn_iff la).mp (hls.2.2 1 (by simp) (by simp))
  obtain ⟨qb, hlb, hqb⟩ := (sig_exn_iff lb).mp (hls.2.2 2 (by simp) (by simp))
  have hwa : lw.1 ≠ la.1 := fun h => by rw [h, hla] at hlw; simp at hlw
  have hwb : lw.1 ≠ lb.1 := fun h => by rw [h, hlb] at hlw; simp at hlw
  have hab : la.1 ≠ lb.1 := fun h => by
    have hnd := hls.2.1
    rw [show la = lb from Subtype.ext h] at hnd
    simp at hnd
  exact ⟨der_e7a_J₁ hlw, runsTo_e7a hlw, der_e7b_lab_J₁ hlw hla hqa hwa, runsTo_e7b hlw hla,
    fun ε A hL => not_der_e7c_J₁ hlw hwa hL, der_e7d_J₁ hlw hla hqa hlb hqb hwa hwb hab,
    runsTo_e7d hlw hla hlb hab⟩

/-- **E7c's rejection is at the rows without its inner label, and at no other**: at an admissible
effect context, for every labels at E7's signatures, `e7c` is typed at its inner label's row
(`der_e7c_lift_J₁`), so no typing system meeting decision D1 rejects it at every type. -/
theorem e7c_typed_at_lift_J₁ (hΞ : AdmEff Ξ) :
    ∀ ls, (𝕁).LabelsAt [(𝕁).sigWait, (𝕁).sigExn, (𝕁).sigExn] ls → ∀ lw la lb, ls = [lw, la, lb] →
      (𝕁).der [] ((𝕁).e7c lw la) ((𝕁).F ((𝕁).EA.lift la) (𝕁).ty7) := by
  intro ls hls lw la lb hlsEq
  subst hlsEq
  have hlw := (sig_wait_iff hΞ.1 lw).mp (hls.2.2 0 (by simp) (by simp))
  obtain ⟨qa, hla, hqa⟩ := (sig_exn_iff la).mp (hls.2.2 1 (by simp) (by simp))
  have hwa : lw.1 ≠ la.1 := fun h => by rw [h, hla] at hlw; simp at hlw
  exact der_e7c_lift_J₁ hlw hla hqa hwa

end E7

end Targets.Inst

end
