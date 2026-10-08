import Targets.Instance.EProps

/-!
# The Instance — E6 (no accidental handling) at `J₁`

`fwrap = λg. handle exnᵢ {return x ⇒ x; raise _ ⇒ ff} (g ())` is typed once, at `hof`'s
polymorphic type (`derV_fwrap_J₁`).  At an instance whose row has `exnᵢ`'s operations, the handler is
typed at the row without them (`Row.dropName`), the callback's row is read through `[sub]` below
the handled row (`rowLe_ofEff_dropName`), and the handler's answer is lifted back by `[sub]`.  Its one
typing serves a callback at every row (`polyUseLacks_fwrap_J₁`); `fwrap` calls its callback under
its own handler only (`callsThrough_fwrap`); and in `tunnel`, the callback's raise of `exnₒ`
passes `fwrap`'s handler of `exnᵢ` and is caught outside (`runsTo_tunnel`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont performE raiseE hndE hndVal opPayload)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt lookRun lookEnd find_ofEff_at)

/-! ### A row without a name -/

/-- The row without the operations of the name `n`. -/
def Row.dropName (n : UInt32) (S : Row) : Row := S.filter (fun o => o.n != n)

theorem find_dropName_ne {n m : UInt32} (h : m ≠ n) :
    ∀ (S : Row) (i : UInt32), Row.find (Row.dropName n S) m i = Row.find S m i
  | [], _ => rfl
  | o :: S, i => by
      unfold Row.dropName Row.find at *
      by_cases ho : o.n = n
      · have hk : decide (m = o.n ∧ i = o.i) = false := by
          simp only [decide_eq_false_iff_not, not_and]
          intro hm; exact absurd (hm.trans ho) h
        rw [List.filter_cons_of_neg (by simp [ho]), List.find?_cons, hk]
        exact find_dropName_ne h S i
      · rw [List.filter_cons_of_pos (by simp [ho]), List.find?_cons, List.find?_cons]
        split
        · rfl
        · exact find_dropName_ne h S i

theorem find_dropName_self (n : UInt32) :
    ∀ (S : Row) (i : UInt32), Row.find (Row.dropName n S) n i = none
  | [], _ => rfl
  | o :: S, i => by
      unfold Row.dropName Row.find at *
      by_cases ho : o.n = n
      · rw [List.filter_cons_of_neg (by simp [ho])]
        exact find_dropName_self n S i
      · rw [List.filter_cons_of_pos (by simp [ho]), List.find?_cons]
        have hk : decide (n = o.n ∧ i = o.i) = false := by
          simp only [decide_eq_false_iff_not, not_and]
          intro hm; exact absurd hm.symm ho
        rw [hk]
        exact find_dropName_self n S i

theorem rowLe_dropName (n : UInt32) (S : Row) : RowLe (Row.dropName n S) S := by
  intro m i o hf
  by_cases hm : m = n
  · subst hm; rw [find_dropName_self] at hf; cases hf
  · rwa [find_dropName_ne hm] at hf

theorem ne_of_mem_dropName {n : UInt32} {S : Row} : ∀ o ∈ Row.dropName n S, o.n ≠ n := by
  intro o ho
  simpa [Row.dropName] using (List.mem_filter.mp ho).2

/-- **A tied row is below its name's signature row before the rest**: the name's operations are
the context's, at their indices. -/
theorem rowLe_ofEff_dropName {Ξ : EffCtx} {S : Row} (hS : RowAt Ξ S) (n : UInt32) :
    RowLe S (Row.ofEff n (Ξ n) 0 ++ Row.dropName n S) := by
  intro m i o hf
  rw [Row.find_append]
  by_cases hm : m = n
  · subst hm
    obtain ⟨-, hlen, hget⟩ := hS m i o hf
    obtain ⟨-, hn, hi⟩ := Row.find_mem hf
    have hj : i.toNat < (Ξ m).length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hget; cases hget
    have hf' := find_ofEff_at m (Ξ m) i.toNat hj hlen
    rw [UInt32.ofNat_toNat] at hf'
    rw [hf', Option.some_or]
    rw [List.getElem?_eq_getElem hj] at hget
    have hg := Option.some.inj hget
    obtain ⟨n', i', q, A, B⟩ := o
    simp only at hn hi hg ⊢
    subst hn; subst hi
    rw [hg]
  · rw [Targets.find_ofEff_other _ hm, Option.none_or, find_dropName_ne hm]
    exact hf

theorem rowAt_dropName {Ξ : EffCtx} {S : Row} (hS : RowAt Ξ S) (n : UInt32) :
    RowAt Ξ (Row.dropName n S) :=
  Targets.rowAt_of_le (rowLe_dropName n S) hS

/-! ### `fwrap` -/

/-- `fwrap`'s handler: `return x ⇒ x`, `raise _ ⇒ ff`. -/
def fwrapH : Expr := .pair (.lam (.var 0)) (clausesE [.lam (.inj₁ .unit)])

theorem isVal_fwrapH : IsVal fwrapH := .pair .lam (.pair .lam .unit)

/-- `fwrap` at the name `n` and the tags `qs`, as our instance writes it. -/
def fwrapE (n : UInt32) (qs : Expr) : Expr :=
  .lam ((handleK n qs (.lam (.var 0)) [.lam (.inj₁ .unit)]).plug (appE (.var 0) .unit))

section Fwrap
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

theorem fwrap_val (li : (orowAlg Ξ).Lab) : ((𝕁).fwrap li).1 = fwrapE li.1 (qsOf Ξ li.1) := rfl

theorem d_fwrapH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) {q : Qual}
    (hq : q ≠ .lin) :
    CDerivesAt Ξ Δ Γ fwrapH
      (.val (.tensor (retTy S boolT boolT) (clausesTy S boolT [(q, .unit, .zero)]))) := by
  refine .tensorI (deadSplit hΓ) (d_lamBang hΓ (.effSub (rowLe_nil S) (.ret
    (.var (.here hΓ.toP))))) (.tensorI (deadSplit hΓ) ?_ (.unitI hΓ.toP))
  rw [clauseTy_abortive hq]
  exact d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.sumI₁ (.unitI (.drop rfl hΓ.toP)))))

/-- `g ()`, as our instance writes it, `g` a callback at the slot `0`. -/
theorem d_callVar0 {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {C : CTy} :
    CDerivesAt Ξ Δ (⟨.thunk (.arr .unit C), true⟩ :: Γ) (appE (.var 0) .unit) (.comp C) :=
  .bind (.right (deadSplit hΓ)) (.ret (.unitI (.cons hΓ.toP)))
    (.app (.right (.left (deadSplit hΓ))) (.force (C := .arr .unit C) (.there (.here hΓ.toP)))
      (.here (.cons hΓ.toP)))

/-- **`fwrap` at every instance**: at the row `r`, its handler at `r` without `exnᵢ`. -/
theorem d_fwrap (li : (orowAlg Ξ).Lab) {q : Qual} (hli : Ξ li.1 = [(q, .unit, .zero)])
    (hq : q ≠ .lin) {r : Row} (hr : RowAt Ξ r) {Δ : LifeCtx} :
    CDerivesAt Ξ Δ [] (fwrapE li.1 (qsOf Ξ li.1))
      (.comp (.arr (.thunk (.arr .unit (CTy.effOf r boolT))) (CTy.effOf r boolT))) := by
  refine .lam (.effSub (rowLe_dropName li.1 r) ?_)
  refine d_handleL li hli (S := Row.dropName li.1 r) (rowAt_dropName hr li.1)
    (fun o ho => ne_of_mem_dropName o ho) isVal_fwrapH (d_fwrapH (kill_dead _) _ hq) ?_
  have hle := rowLe_ofEff_dropName hr li.1
  rw [hli] at hle
  exact .effSub hle (d_callVar0 .nil)

/-- **E6: `fwrap` is typed once**, at `U(∀ρ:any. U(1 ⊸ F_ρ bool) ⊸ F_ρ bool)`. -/
theorem derV_fwrap_J₁ (li : (orowAlg Ξ).Lab) {q : Qual} (hli : Ξ li.1 = [(q, .unit, .zero)])
    (hq : q ≠ .lin) : (𝕁).derV [] ((𝕁).fwrap li) (polyTy (hofC boolT)) := by
  have hcl : closedAt 0 (fwrapE li.1 (qsOf Ξ li.1)) = true := by
    simpa using closedAt_of_derives (d_fwrap (Δ := LifeCtx.empty) li hli hq (rowAt_nil Ξ)).toCDerives
  exact derV_poly_J₁ (b := (handleK li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)]).plug
    (appE (.var 0) .unit)) (hofC_rFree boolT) trivial hcl fun r η _ hrt => by
      rw [hofC_den]; exact d_fwrap li hli hq hrt

/-- **E6's schema at `J₁`**: the one typing of `fwrap` serves a callback at every row without
`exnᵢ`, the callback and the use at the same row. -/
theorem polyUseLacks_fwrap_J₁ (hΞ : Ξ.NU) (li : (orowAlg Ξ).Lab) :
    (𝕁).PolyUseLacks [polyTy (hofC boolT)] li (fun g => (𝕁).call ((𝕁).var 0) g)
      (𝕁).bool (𝕁).bool := by
  intro ε M _ hM
  exact der_callPoly_J₁ hΞ (hofC_rFree boolT) trivial boolT_not_loop
    (fun η => hofC_den boolT η _) hM hM.1

/-- **`fwrap` calls its callback under its own handler only**: from
`let f = fwrap in f (λ_. M)`, the run reaches `M` by store-keeping steps, under `fwrap`'s handler
frame, which catches only `exnᵢ` and holds no finaliser. -/
theorem callsThrough_fwrap (li : (orowAlg Ξ).Lab) {M : Expr} (hM : closedAt 0 M = true) :
    (𝕁).CallsThrough (· ≠ li) ((𝕁).lets [(𝕁).fwrap li] ((𝕁).call ((𝕁).var 0) ((𝕁).lam M))) M := by
  have hLM : closedAt 0 (Expr.lam M) = true := by simpa [closedAt] using closedAt_of_zero hM 1
  have hHc : closedAt 0 (hndValE li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)]) = true := by
    simp [hndValE, clausesE, closedAt, qsOf, closedAt_qualsVal]
  have hfc : closedAt 0 (Expr.lam ((handleK li.1 (qsOf Ξ li.1) (.lam (.var 0))
      [.lam (.inj₁ .unit)]).plug (appE (.var 0) .unit))) = true := by
    have := closedAt_of_zero hHc 1
    simp [handleK, Kont.plug, appE, closedAt, Expr.shift, this]
  have h₁ := quiet_call_lam (ℍ := ℍ) hfc hM
  have e : Expr.subst 0 (Val.lam M) ((handleK li.1 (qsOf Ξ li.1) (.lam (.var 0))
      [.lam (.inj₁ .unit)]).plug (appE (.var 0) .unit)) =
      (handleK li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)]).plug
        (appE (.lam M) .unit) := by
    show Expr.app (Expr.app (Expr.subst 0 (Val.lam M) (.prim .hnd))
        (Expr.subst 0 (Val.lam M) (hndValE li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)])))
      (Expr.subst 0 (Val.lam M) (appE (.var 0) .unit)) = _
    rw [subst_closedAt _ _ hHc (le_refl _), appE_var0_subst rfl (Val.lam M) hLM]
    rfl
  rw [e] at h₁
  have h₂ := (quiet_appE (ℍ := ℍ) .hole (.lam M) Val.unit).plug
    (handleK li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)])
  have h₃ := (quiet_beta (ℍ := ℍ) .hole M Val.unit).plug
    (handleK li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)])
  rw [subst_closedAt M Val.unit hM (le_refl _)] at h₃
  obtain ⟨q, hc, -⟩ := h₁.trans (h₂.trans h₃)
  refine ⟨handleK li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)], fun m hm => ?_,
    ⟨fun x => by simp, fun s => by simp, trivial⟩, pureSteps_of_chain hc⟩
  have hm' : li.1 ≠ m.1 := fun h => hm (Subtype.ext h.symm)
  show Kont.HasHnd m.1 (handleK li.1 (qsOf Ξ li.1) (.lam (.var 0)) [.lam (.inj₁ .unit)]) = false
  simp [handleK, hndValE, Kont.HasHnd, hm']

/-! ### `tunnel` -/

/-- `tunnel`, as our instance writes it. -/
def tunnelE (ni no : UInt32) (qi qo : Expr) : Expr :=
  (handleK no qo (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).plug
    (bindE (fwrapE ni qi) (appE (.var 0) (failCbE no)))

theorem tunnel_val (li lo : (orowAlg Ξ).Lab) :
    ((𝕁).tunnel li lo : Expr) = tunnelE li.1 lo.1 (qsOf Ξ li.1) (qsOf Ξ lo.1) := rfl

/-- `f V`, as our instance writes it, `f` a function at the slot `0` and `V` a closed value. -/
theorem d_callVar {Δ : LifeCtx} {T : VTy} {C : CTy} {V : Expr}
    (hV : CDerivesAt Ξ Δ [⟨.thunk (.arr T C), false⟩] V (.val T)) :
    CDerivesAt Ξ Δ [⟨.thunk (.arr T C), true⟩] (appE (.var 0) V) (.comp C) :=
  .bind (.right .nil) (.ret hV)
    (.app (.right (.left .nil)) (.force (C := .arr T C) (.there (.here .nil))) (.here (.cons .nil)))

/-- **`tunnel` is typed at `J₁`**: `fwrap` let-bound and called at the row of `exnₒ`, which
`toResult` handles. -/
theorem d_tunnel {li lo : (orowAlg Ξ).Lab} {qi qo : Qual} (hli : Ξ li.1 = [(qi, .unit, .zero)])
    (hqi : qi ≠ .lin) (hlo : Ξ lo.1 = [(qo, .unit, .zero)]) (hqo : qo ≠ .lin) :
    CDerivesAt Ξ LifeCtx.empty [] (tunnelE li.1 lo.1 (qsOf Ξ li.1) (qsOf Ξ lo.1))
      (.comp (.ret (.sum boolT .unit))) := by
  have hR := rowAt_ofEff_lab lo hlo
  refine d_handleL lo hlo (S := []) (rowAt_nil Ξ) (by simp) isVal_toResultH
    (d_toResultH (kill_dead _) [] boolT hqo) ?_
  refine .bind .nil (.ret (.thunkV rfl (d_fwrap li hli hqi hR))) (d_callVar ?_)
  exact d_cbDead (.cons .nil) (d_raiseLab .nil lo hlo hqo boolT)

/-- `tunnel`'s rest after the callback's raise: `fwrap`'s handler of `exnᵢ` inside `toResult`'s
handler of `exnₒ`. -/
theorem tunnel_seg (ni no : UInt32) (qi qo : Qual) :
    lookEnd 5 (tunnelE ni no (qualsVal [qi]).1 (qualsVal [qo]).1) =
      hndE (toResultV no (qualsVal [qo])) ((handleK ni (qualsVal [qi]).1 (.lam (.var 0))
        [.lam (.inj₁ .unit)]).plug (raiseE (.val (opPayload no 0 Val.unit)))) := by rfl

/-- **`tunnel`'s run**: the raise of `exnₒ` passes `fwrap`'s handler of `exnᵢ` and is caught by
`toResult`; the answer is `inr ()`, with no event. -/
theorem runsTo_tunnel {li lo : (orowAlg Ξ).Lab} {qi qo : Qual} (hne : li ≠ lo)
    (hli : Ξ li.1 = [(qi, .unit, .zero)]) (hlo : Ξ lo.1 = [(qo, .unit, .zero)]) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).tunnel li lo) ((𝕁).inr (𝕁).unitV) [] := by
  rw [tunnel_val, qsOf_eq hli, qsOf_eq hlo]
  have hA := quiet_of_look (ℍ := ℍ) 5 (tunnelE li.1 lo.1 (qualsVal [qi]).1 (qualsVal [qo]).1) rfl
  rw [tunnel_seg] at hA
  have hne' : li.1 ≠ lo.1 := fun h => hne (Subtype.ext h)
  have hK : Kont.Catches lo.1 (Kont.appR (.app (.prim .hnd) (hndValE li.1 (qualsVal [qi]).1
      (.lam (.var 0)) [.lam (.inj₁ .unit)])) .hole) = false := by
    simp [Kont.Catches, hndValE, hne']
  have hB := Quiet.head (ℍ := ℍ) .hole (fun μ => Head.hunwind μ lo.1 0 (qualsVal [qo])
    ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩
    ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit _ (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl) hK)
    rfl rfl
  have hC := quiet_beta (ℍ := ℍ) .hole (.inj₂ .unit) Val.unit
  exact runsTo_of_calm (𝕁).R₀ (v := ⟨_, .inj₂ .unit⟩) ((hA.trans (hB.trans hC)).calm)

end Fwrap

/-! ### E6 -/

section E6
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **E6's labels**: two `exn` labels, at a rich context. -/
theorem labelsAt_E6 (hΞ : AdmEff Ξ) : ∃ ls, (𝕁).LabelsAt [(𝕁).sigExn, (𝕁).sigExn] ls := by
  obtain ⟨l₁, l₂, hne, h₁, h₂⟩ := rich_labs hΞ.2.2 (E := [(.aff, .unit, .zero)]) (by simp [eSigs])
  refine ⟨[l₁, l₂], rfl, List.nodup_cons.mpr ⟨fun h => hne (List.mem_singleton.mp h),
    List.nodup_singleton _⟩, fun k h₁' _ => ?_⟩
  match k, h₁' with
  | 0, _ => exact (sig_exn_iff l₁).mpr ⟨.aff, h₁, by decide⟩
  | 1, _ => exact (sig_exn_iff l₂).mpr ⟨.aff, h₂, by decide⟩

/-- **E6, no accidental handling, at `J₁`**, at every admissible effect context. -/
theorem tunnel_J₁ (hΞ : AdmEff Ξ) : (𝕁).Tunnel := by
  refine ⟨labelsAt_E6 hΞ, fun ls hls li lo hlsEq => ?_⟩
  subst hlsEq
  obtain ⟨qi, hli, hqi⟩ := (sig_exn_iff li).mp (hls.2.2 0 (by simp) (by simp))
  obtain ⟨qo, hlo, hqo⟩ := (sig_exn_iff lo).mp (hls.2.2 1 (by simp) (by simp))
  have hne : li ≠ lo := fun h => by
    have := hls.2.1
    simp [h] at this
  refine ⟨polyTy (hofC boolT), derV_fwrap_J₁ li hli hqi, polyUseLacks_fwrap_J₁ hΞ.1 li,
    fun ε M _ hM => callsThrough_fwrap li (closed_of_der_J₁ boolT_not_loop hM), der_retTt_J₁,
    der_raise_J₁ hlo hqo boolT, ?_, runsTo_tunnel hne hli hlo⟩
  refine ⟨tiedAt_unit J₁ _, .inl ⟨[], by simp, fun _ h => absurd h List.not_mem_nil,
    OVTy.rFree_ofV (.sum boolT .unit), fun η _ _ σ _ => ?_⟩⟩
  change CDerivesAt Ξ LifeCtx.empty [] (fillS σ 0 (tunnelE li.1 lo.1 (qsOf Ξ li.1) (qsOf Ξ lo.1)))
    (.comp (.ret (.sum boolT .unit)))
  have hd := d_tunnel hli hqi hlo hqo
  rw [fillS_closed σ _ 0 (by simpa using closedAt_of_derives hd.toCDerives)]
  exact hd

end E6

end Targets.Inst

end
