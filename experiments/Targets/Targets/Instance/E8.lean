import Targets.Instance.E7

/-!
# The Instance — E8 (unwinding through finalisers) at `J₁`

`e8a = toResult exn ((raise exn ()) then x. return x unwind ())` and `e8b = toResult exn_a
(toResult exn_b ((raise exn_a ()) then x. return x unwind raise exn_b ()))`.  `J₁`'s kernel takes
SPEC §27's `[then]`, whose finaliser is at a row below the `[then]`'s (`Σ_D ≤ Σ`): in `e8b` the
finaliser raises `exn_b`, handled outside (`d_e8b`).  An unwind fires the finaliser in place
(`[finalise]`, `D (); raise p`), showing it and no end: in `e8a` the pending raise then reaches
`toResult` (`runsTo_e8a`); in `e8b` the finaliser's raise supersedes it and `toResult` of `exn_b`
catches it, so `toResult` of `exn_a` returns `inl (inr ())` (`runsTo_e8b`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont Heap raiseE hndE hndVal opPayload ubindE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg RowAt rowAt_nil CDerivesAt)

/-! ### The programs, as our instance writes them -/

/-- A's `e8a`: `handle exn {…} ((raise exn ()) then x. return x unwind ())`. -/
def e8aE (ne : UInt32) (qe : Expr) : Expr :=
  toResultE ne qe ((thenK (.var 0) .unit).plug (raiseE (opArgE ne 0 .unit)))

/-- A's `e8b`: `handle exn_a {…} (handle exn_b {…} ((raise exn_a ()) then x. return x unwind
raise exn_b ()))`. -/
def e8bE (na nb : UInt32) (qa qb : Expr) : Expr :=
  toResultE na qa (toResultE nb qb
    ((thenK (.var 0) (raiseE (opArgE nb 0 .unit))).plug (raiseE (opArgE na 0 .unit))))

section Typing
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem e8a_val (le : (orowAlg Ξ).Lab) : ((𝕁).e8a le : Expr) = e8aE le.1 (qsOf Ξ le.1) := rfl

theorem e8b_val (la lb : (orowAlg Ξ).Lab) :
    ((𝕁).e8b la lb : Expr) = e8bE la.1 lb.1 (qsOf Ξ la.1) (qsOf Ξ lb.1) := rfl

/-- A row of one abortive `1 ↠ 0` has no capturable operation. -/
theorem not_capB_exnRow {n : UInt32} {q : Qual} {o : OpSig}
    (ho : o ∈ Row.ofEff n [(q, .unit, .zero)] 0 ++ []) : capB o.q o.B = false := by
  simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at ho
  subst ho
  exact capB_exn q

/-- The errors pending at a finaliser below a row of one abortive `1 ↠ 0` are persistent. -/
theorem pendPers_exnRow (n : UInt32) (q : Qual) : (Row.ofEff n [(q, .unit, .zero)] 0 ++ []).PendPers := by
  intro o ho
  simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at ho
  subst ho
  exact ⟨fun _ => rfl, fun h => by simp [capB, VTy.isZero] at h⟩

/-- **`e8a` is typed by `J₁`'s kernel**: the `[then]` at `exn`'s row, its finaliser at the pure
row. -/
theorem d_e8a {le : (orowAlg Ξ).Lab} {q : Qual} (hle : Ξ le.1 = [(q, .unit, .zero)]) (hq : q ≠ .lin) :
    CDerivesAt Ξ LifeCtx.empty [] (e8aE le.1 (qsOf Ξ le.1)) (.comp (.ret (.sum .unit .unit))) := by
  refine d_toResult hle hq (S := []) (rowAt_nil Ξ) (by simp) ?_
  refine .effThen (SM := Row.ofEff le.1 [(q, .unit, .zero)] 0 ++ []) (SD := []) .nil ?_ ?_
    (fun _ => fun _ h => absurd h List.not_mem_nil) (RowLe.refl _) (RowLe.nil _) ?_
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) (d_raiseLab .nil le hle hq .unit)
    (.effSub (rowLe_nil _) (.ret (.var (.here .nil)))) (.ret (.unitI (.cons .nil)))
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    subst ho
    exact le.2.1
  · simp [Row.Uniq, Row.ofEff]
  · intro n i o o' hf _ hc
    rw [not_capB_exnRow (Row.find_mem hf).1] at hc
    cases hc

/-- **`e8b` is typed by `J₁`'s kernel**: the `[then]` at `exn_b`'s row before `exn_a`'s, its
finaliser at `exn_b`'s row (SPEC §27's `Σ_D ≤ Σ`), handled by the inner `toResult`. -/
theorem d_e8b {la lb : (orowAlg Ξ).Lab} {qa qb : Qual} (hla : Ξ la.1 = [(qa, .unit, .zero)])
    (hqa : qa ≠ .lin) (hlb : Ξ lb.1 = [(qb, .unit, .zero)]) (hqb : qb ≠ .lin) (hab : la.1 ≠ lb.1) :
    CDerivesAt Ξ LifeCtx.empty [] (e8bE la.1 lb.1 (qsOf Ξ la.1) (qsOf Ξ lb.1))
      (.comp (.ret (.sum (.sum .unit .unit) .unit))) := by
  have hSa := rowAt_ofEff_lab la hla
  refine d_toResult hla hqa (S := []) (rowAt_nil Ξ) (by simp) ?_
  refine d_toResult hlb hqb (S := Row.ofEff la.1 [(qa, .unit, .zero)] 0 ++ []) hSa
    (names_ofEff hab) ?_
  refine .effThen (SM := Row.ofEff la.1 [(qa, .unit, .zero)] 0 ++ [])
    (SD := Row.ofEff lb.1 [(qb, .unit, .zero)] 0 ++ []) .nil ?_ ?_
    (fun _ => fun _ h => absurd h List.not_mem_nil) (rowLe_ofEff_cons _ (names_ofEff hab))
    (rowLe_append_nil _ _) ?_ (fun _ => pendPers_exnRow la.1 qa) (d_raiseLab .nil la hla hqa .unit)
    (.effSub (rowLe_nil _) (.ret (.var (.here .nil)))) (d_raiseLab (.cons .nil) lb hlb hqb .unit)
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact lb.2.1
    · exact la.2.1
  · simp [Row.Uniq, Row.ofEff, Ne.symm hab]
  · intro n i o o' hf _ hc
    rw [not_capB_exnRow (Row.find_mem hf).1] at hc
    cases hc

/-- **`e8a` is typed by `J₁`**. -/
theorem der_e8a_J₁ {le : (orowAlg Ξ).Lab} {q : Qual} (hle : Ξ le.1 = [(q, .unit, .zero)])
    (hq : q ≠ .lin) :
    (𝕁).der [] ((𝕁).e8a le) ((𝕁).F (𝕁).EA.unit ((𝕁).Sum (𝕁).UnitT (𝕁).UnitT)) := by
  have hd := d_e8a hle hq
  rw [e8a_val]
  exact der_J₁_ret (A := .sum .unit .unit) (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- **`e8b` is typed by `J₁`**. -/
theorem der_e8b_J₁ {la lb : (orowAlg Ξ).Lab} {qa qb : Qual} (hla : Ξ la.1 = [(qa, .unit, .zero)])
    (hqa : qa ≠ .lin) (hlb : Ξ lb.1 = [(qb, .unit, .zero)]) (hqb : qb ≠ .lin) (hab : la.1 ≠ lb.1) :
    (𝕁).der [] ((𝕁).e8b la lb)
      ((𝕁).F (𝕁).EA.unit ((𝕁).Sum ((𝕁).Sum (𝕁).UnitT (𝕁).UnitT) (𝕁).UnitT)) := by
  have hd := d_e8b hla hqa hlb hqb hab
  rw [e8b_val]
  exact der_J₁_ret (A := .sum (.sum .unit .unit) .unit)
    (by simpa using closedAt_of_derives hd.toCDerives) hd

end Typing

/-! ### The runs -/

section Runs
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **`[finalise]`**: a raise reaches a finaliser frame, which fires its finaliser in place,
showing the finaliser, the raise pending. -/
theorem obsFrom_ufin (R : (𝕁).Runner) {μ : Heap} {s : R.St} (K₀ K : Kont) (N D : Val) {n : UInt32}
    (hn : n ≠ 0) (i : UInt32) (v : Val) (hK : K.Catches n = false) (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom R ((μ, K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v)))))), s)
      w tr ↔
    ∃ tr', tr = .fire (finE D.1) :: tr' ∧
      (𝕁).ObsFrom R ((μ, K₀.plug (.seq (.app (.val D) (.val .unit))
        (raiseE (.val (opPayload n i v))))), s) w tr' := by
  rw [obsFrom_head_iff R (fun μ => Head.ufin μ N D n i v K hn hK) rfl w tr,
    labelOf_fire (plug_raise_not_val K _)]
  rfl

/-- `toResult`'s clause, applied: `inr ()`. -/
theorem quiet_toResultCl (K₀ : Kont) :
    Quiet (ℍ := ℍ) (K₀.plug (.app (.val ⟨.lam (.inj₂ .unit), .lam⟩) (.val Val.unit)))
      (K₀.plug (.val (Val.inj₂ Val.unit))) :=
  quiet_beta (ℍ := ℍ) K₀ (.inj₂ .unit) Val.unit

/-- **`e8a`'s complete runs**, from every memory: the unwind fires the finaliser `()`, the pending
raise reaches `toResult`, and each run answers `inr ()`. -/
theorem obsFrom_e8a (le : (orowAlg Ξ).Lab) (q : Qual) {μ : Heap} (w : OVal) (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, e8aE le.1 (qualsVal [q]).1), ()) w tr ↔
      w.1 = (Val.inj₂ Val.unit).1 ∧ tr = [.fire .unit] := by
  have q₁ : Quiet (ℍ := ℍ) ((trK le.1 q).plug (.seq (.app (.val ⟨.lam .unit, .lam⟩) (.val .unit))
      (raiseE (.val (opPayload le.1 0 Val.unit))))) (.val (Val.inj₂ Val.unit)) := by
    have h₁ := (quiet_beta (ℍ := ℍ) (.seq .hole (raiseE (.val (opPayload le.1 0 Val.unit)))) .unit
      Val.unit).plug (trK le.1 q)
    have h₂ := (Quiet.head (ℍ := ℍ) .hole (fun μ => Head.seq μ (raiseE (.val (opPayload le.1 0 Val.unit))))
      rfl rfl).plug (trK le.1 q)
    have h₃ := quiet_hunwind (ℍ := ℍ) .hole le.1 0 (qualsVal [q]) ⟨.lam (.inj₁ (.var 0)), .lam⟩
      ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩ ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit
      (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl)
    exact (h₁.trans h₂).trans (h₃.trans (quiet_toResultCl .hole))
  refine (obsFrom_ufin (𝕁).R₀ (s := ()) (trK le.1 q) .hole ⟨.lam (.var 0), .lam⟩ ⟨.lam .unit, .lam⟩
    le.2.1 0 Val.unit rfl w tr).trans ?_
  constructor
  · rintro ⟨tr', rfl, h⟩
    obtain ⟨hw, rfl⟩ := ((obsFrom_quiet_iff _ q₁ w tr').trans
      (obsFrom_val_iff _ (Val.inj₂ Val.unit) w tr')).1 h
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨[], rfl, ((obsFrom_quiet_iff _ q₁ w []).trans
      (obsFrom_val_iff _ (Val.inj₂ Val.unit) w [])).2 ⟨hw, rfl⟩⟩

/-- **`e8b`'s complete runs**, from every memory: the unwind of `exn_a` fires the finaliser, whose
raise of `exn_b` supersedes the pending raise; `toResult` of `exn_b` catches it, and `toResult` of
`exn_a` returns.  Each answers `inl (inr ())`. -/
theorem obsFrom_e8b (la lb : (orowAlg Ξ).Lab) (qa qb : Qual) {μ : Heap} (w : OVal)
    (tr : List (𝕁).Event) :
    (𝕁).ObsFrom (𝕁).R₀ ((μ, e8bE la.1 lb.1 (qualsVal [qa]).1 (qualsVal [qb]).1), ()) w tr ↔
      w.1 = (Val.inj₁ (Val.inj₂ Val.unit)).1 ∧ tr = [.fire (raiseE (opArgE lb.1 0 .unit))] := by
  have q₁ : Quiet (ℍ := ℍ) (((trK la.1 qa).comp (trK lb.1 qb)).plug
      (.seq (.app (.val (raiseFin lb.1)) (.val .unit)) (raiseE (.val (opPayload la.1 0 Val.unit)))))
      (.val (Val.inj₁ (Val.inj₂ Val.unit))) := by
    have h₁ := (quiet_beta (ℍ := ℍ) (.seq .hole (raiseE (.val (opPayload la.1 0 Val.unit))))
      ((raiseE (opArgE lb.1 0 .unit)).shift 1 0) Val.unit).plug ((trK la.1 qa).comp (trK lb.1 qb))
    have h₂ : Quiet (ℍ := ℍ) (((trK la.1 qa).comp (trK lb.1 qb)).plug
        ((Kont.seq .hole (raiseE (.val (opPayload la.1 0 Val.unit)))).plug
          (raiseE (.val (opPayload lb.1 0 Val.unit)))))
        ((trK la.1 qa).plug (.app (.val ⟨.lam (.inj₂ .unit), .lam⟩) (.val Val.unit))) := by
      have h := (Quiet.head (ℍ := ℍ) .hole (fun μ => Head.hunwind μ lb.1 0 (qualsVal [qb])
        ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩
        ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit (.seq .hole (raiseE (.val (opPayload la.1 0 Val.unit))))
        (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl) rfl) rfl rfl).plug (trK la.1 qa)
      rw [Kont.plug_comp]
      exact h
    have h₃ := quiet_toResultCl (ℍ := ℍ) (trK la.1 qa)
    have h₄ := Quiet.head (ℍ := ℍ) .hole (fun μ => Head.hret μ la.1 (qualsVal [qa])
      ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩
      (Val.inj₂ Val.unit)) rfl rfl
    have h₅ := quiet_beta (ℍ := ℍ) .hole (.inj₁ (.var 0)) (Val.inj₂ Val.unit)
    exact (h₁.trans h₂).trans (h₃.trans (h₄.trans h₅))
  refine (obsFrom_ufin (𝕁).R₀ (s := ()) ((trK la.1 qa).comp (trK lb.1 qb)) .hole ⟨.lam (.var 0), .lam⟩
    (raiseFin lb.1) la.2.1 0 Val.unit rfl w tr).trans ?_
  constructor
  · rintro ⟨tr', rfl, h⟩
    obtain ⟨hw, rfl⟩ := ((obsFrom_quiet_iff _ q₁ w tr').trans
      (obsFrom_val_iff _ (Val.inj₁ (Val.inj₂ Val.unit)) w tr')).1 h
    exact ⟨hw, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨[], rfl, ((obsFrom_quiet_iff _ q₁ w []).trans
      (obsFrom_val_iff _ (Val.inj₁ (Val.inj₂ Val.unit)) w [])).2 ⟨hw, rfl⟩⟩

/-- **`e8a`'s run**: it answers `inr ()`, showing the finaliser fired in place. -/
theorem runsTo_e8a {le : (orowAlg Ξ).Lab} {q : Qual} (hle : Ξ le.1 = [(q, .unit, .zero)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e8a le) ((𝕁).inr (𝕁).unitV) [.fire ((𝕁).ret (𝕁).unitV)] := by
  rw [e8a_val, qsOf_eq hle]
  exact runsTo_of_obsFrom _ (v := Val.inj₂ Val.unit) fun w tr => obsFrom_e8a le q w tr

/-- **`e8b`'s run**: it answers `inl (inr ())`, showing the finaliser, whose raise supersedes the
pending one. -/
theorem runsTo_e8b {la lb : (orowAlg Ξ).Lab} {qa qb : Qual} (hla : Ξ la.1 = [(qa, .unit, .zero)])
    (hlb : Ξ lb.1 = [(qb, .unit, .zero)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).e8b la lb) ((𝕁).inl ((𝕁).inr (𝕁).unitV))
      [.fire ((𝕁).raise lb 0 (𝕁).unitV)] := by
  rw [e8b_val, qsOf_eq hla, qsOf_eq hlb]
  exact runsTo_of_obsFrom _ (v := Val.inj₁ (Val.inj₂ Val.unit)) fun w tr => obsFrom_e8b la lb qa qb w tr

end Runs

/-! ### E8 -/

section E8
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **E8, unwinding through finalisers, at `J₁`**, at every admissible effect context. -/
theorem unwindPolicy_J₁ (hΞ : AdmEff Ξ) : (𝕁).UnwindPolicy := by
  refine ⟨labelsAt_E6 hΞ, fun ls hls la lb hlsEq => ?_⟩
  subst hlsEq
  obtain ⟨qa, hla, hqa⟩ := (sig_exn_iff la).mp (hls.2.2 0 (by simp) (by simp))
  obtain ⟨qb, hlb, hqb⟩ := (sig_exn_iff lb).mp (hls.2.2 1 (by simp) (by simp))
  have hab : la.1 ≠ lb.1 := fun h => by
    have hnd := hls.2.1
    rw [show la = lb from Subtype.ext h] at hnd
    simp at hnd
  exact ⟨der_e8a_J₁ hla hqa, runsTo_e8a hla, der_e8b_J₁ hla hqa hlb hqb hab, runsTo_e8b hla hlb⟩

end E8

end Targets.Inst

end
