import Core.DivHandlers
import Core.BoundedFix

/-!
# Core — `div_fuel`  `[spec §14]`

    div_fuel : !U(U(1 ⊸ F_{tick, Σ} A) ⊗ I32 ⊸ F_Σ A)

`div_fuel (t, k)` handles `Div` in `t ()`: it answers *next* to the first `k` ticks (the budget
read unsigned) and *close* to every tick after.  It is a deep handler of `Div` whose handled
computation answers a function of the budget's self-reference, driven by `bounded_fix`:

    div_fuel (t, k)  ≜  (hnd_Div H (t ())) to g. bounded_fix (λ(self, g). g self, (k, g))
    h_ret v           =  λself. v
    h_tick ((), κ)    =  λself. case self { inl _ → (κ close) to g. g (inl ())
                                           | inr f → (κ next) to g. f g }

`bounded_fix`'s self-reference is `inl ()` once the budget is spent and otherwise the fixed point
at one less, so the budget is the machine's, counted down by the machine (SPEC §20): the
handler's state is a native counter.  `tick` must resume, so `κ` owns a cell, freed when it is
resumed.  Every path of the clause resumes `κ` once, in tail position up to the counter's
application.

**Totality** (`fuel_total`): `div_fuel` of a computation of `cwp` is in `ewpTS` at the rest of
the row, by induction on the budget and, inside, on the segment's least fixed point.  At a tick
with budget left, `κ next`'s continuation is in `cwp` (the induction on the budget); once it is
spent, `κ close`'s continuation is in `Closing`, and the handler of a computation of `Closing` is
total by induction on `Closing`'s least fixed point (`fuel_closing`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappaC kappaCell kappaAt clauseAt capTag freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The terms -/

/-- `h_ret = λv. λself. v`. -/
def fuelR : Val := .lam (.val (.lam (.var 1)))

/-- `λg. g (inl ())`: the budget spent. -/
def spentV : Val := .lam (.app (.var 0) (.val (Val.inj₁ .unit)))

/-- The tick's clause under the self-reference (`0`), `κ` (`1`) and `()` (`2`):
`case self { inl _ → spent ((κ close)) | inr f → (λg. f g) (κ next) }`. -/
def fuelBody : Expr :=
  .case (.var 0)
    (.app (.val spentV) (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.val closeV)))
    (.app (.val (.lam (.app (.var 1) (.var 0))))
      (.app (.app (.var 2) (.val (Val.inj₁ .unit))) (.val nextV)))

/-- The tick's clause `λ((), κ). λself. …`. -/
def fuelC : Val := .lam (.letpair (.var 0) (.val (.lam fuelBody)))

/-- The handler value: the name `Div`, `tick` must resume. -/
def fuelH : Val := hndVal divEff (qualsVal [.lin]) fuelR (Val.pair fuelC .unit)

/-- `bounded_fix`'s step: `λ(self, g). g self`. -/
def fuelStep : Val := .lam (.letpair (.var 0) (.app (.var 0) (.var 1)))

/-- **`div_fuel`**: `λ(t, k). (λg. bounded_fix (fuelStep, (k, g))) (hnd_Div H (t ()))`.
`[spec §14]` -/
def divFuelV : Val :=
  .lam (.letpair (.var 0) (.app (.val (.lam (.app (.val (.prim .boundedFix))
      (.pair (.val fuelStep) (.pair (.var 1) (.var 0))))))
    (hndE fuelH (.app (.var 1) (.val .unit)))))

/-- The frame `(λg. bounded_fix (fuelStep, (k, g))) [·]`. -/
def fuelK (k : UInt32) : Kont :=
  .appR (.val (.lam (.app (.val (.prim .boundedFix))
    (.pair (.val fuelStep) (.pair (.val (Val.i32 k)) (.var 0)))))) .hole

/-- The frame `(λg. f g) [·]`. -/
def nextK (f : Val) : Kont := .appR (.val (.lam (.app (.val f) (.var 0)))) .hole

/-- The frame `spent [·]`. -/
def spentK : Kont := .appR (.val spentV) .hole

theorem fuelStep_closed : closedAt 0 fuelStep.1 = true := rfl

theorem divFuelV_closed : closedAt 0 divFuelV.1 = true := by
  simp [divFuelV, closedAt, fuelStep, fuelH, hndVal, qualsVal, fuelR, fuelC, fuelBody, spentV,
    Val.pair, Val.i32, BoCa.BoLo.hndE, Qual.tag, nextV, closeV]

/-! ### Frames that hand the self-reference -/

/-- **A frame at the budget `k`**: plain, its own dead region, and applying the handled
computation's answer to the self-reference `bounded_fix` gives at `k`. -/
def FuelFrame (k : UInt32) (K : Kont) : Prop :=
  (∀ n, K.HasHnd n = false) ∧ (∀ n, K.Catches n = false) ∧ K.dead = K ∧
    ∀ g : Val, PureSteps (K.plug (.val g)) (.app (.val g) (.val (fixSelf fuelStep k)))

/-- `bounded_fix (fuelStep, (k, g)) ↦* g (self at k)`. -/
theorem bf_steps (k : UInt32) (g : Val) :
    PureSteps (boundedFixE fuelStep k g) (.app (.val g) (.val (fixSelf fuelStep k))) := by
  refine (PureSteps.head (fun μ => Head.boundedFix μ fuelStep k g) rfl).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ (fixSelf fuelStep k) g _) rfl).trans ?_
  simp [subst_shift_succ]
  exact .refl

theorem fuelK_frame (k : UInt32) : FuelFrame k (fuelK k) := by
  refine ⟨fun n => by simp [fuelK, Kont.HasHnd], fun n => by simp [fuelK, Kont.Catches],
    by simp [fuelK, Kont.dead, Kont.DeadFrame], fun g => ?_⟩
  refine (PureSteps.beta _ g).trans ?_
  have hs : closedAt 0 fuelStep.1 = true := fuelStep_closed
  have e : Expr.subst 0 g (.app (.val (.prim .boundedFix))
      (.pair (.val fuelStep) (.pair (.val (Val.i32 k)) (.var 0)))) = boundedFixE fuelStep k g := by
    simp [closed_subst hs, boundedFixE, Val.pair, Val.i32]
  rw [e]
  exact bf_steps k g

theorem spentK_frame : FuelFrame 0 spentK := by
  refine ⟨fun n => by simp [spentK, Kont.HasHnd, spentV], fun n => by simp [spentK, Kont.Catches, spentV],
    by simp [spentK, Kont.dead, Kont.DeadFrame, spentV], fun g => ?_⟩
  refine (PureSteps.beta _ g).trans ?_
  simp [fixSelf]
  exact .refl

/-- The fixed point at one less, `λx. bounded_fix (fuelStep, (k − 1, x))`. -/
theorem fixSelf_succ {k : UInt32} (hk : k ≠ 0) :
    fixSelf fuelStep k = Val.inj₂ (Val.lam (.app (.val (.prim .boundedFix))
      (.pair (.val (fuelStep.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0))))) := by
  simp [fixSelf, hk]

theorem nextK_frame (k : UInt32) :
    FuelFrame (k - 1) (nextK (Val.lam (.app (.val (.prim .boundedFix))
      (.pair (.val (fuelStep.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0)))))) := by
  refine ⟨fun n => by simp [nextK, Kont.HasHnd], fun n => by simp [nextK, Kont.Catches],
    by simp [nextK, Kont.dead, Kont.DeadFrame], fun g => ?_⟩
  refine (PureSteps.beta _ g).trans ?_
  have hF : closedAt 0 (Val.lam (.app (.val (.prim .boundedFix))
      (.pair (.val (fuelStep.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0))))).1 = true := by
    have h₁ := closed_shift fuelStep_closed 1 0
    simp [closedAt, Val.i32, h₁, closedAt_mono _ fuelStep_closed (Nat.zero_le 1)]
  have e : Expr.subst 0 g (.app (.val (Val.lam (.app (.val (.prim .boundedFix))
      (.pair (.val (fuelStep.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0)))))) (.var 0)) =
      .app (.val (Val.lam (.app (.val (.prim .boundedFix))
        (.pair (.val (fuelStep.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0)))))) (.val g) := by
    simp only [Expr.subst]; rw [closed_subst hF]; simp
  rw [e]
  refine (PureSteps.beta _ g).trans ?_
  rw [fixSelf_body_subst]
  exact bf_steps (k - 1) g

/-! ### The handler's steps -/

theorem fuelK_plain' {k : UInt32} {K : Kont} (h : FuelFrame k K) :
    (∀ n, K.HasHnd n = false) ∧ (∀ n, K.Catches n = false) := ⟨h.1, h.2.1⟩

/-- `[ret]`: the handled computation's answer `v`, under a frame at any budget, answers `v`. -/
theorem fuel_ret {k : UInt32} {K : Kont} (hK : FuelFrame k K) (v : Val) :
    PureSteps (K.plug (hndE fuelH (.val v))) (.val v) := by
  refine (PureSteps.plug K (PureSteps.head (fun μ => Head.hret μ divEff _ _ _ v) rfl)).trans ?_
  refine (PureSteps.plug K (PureSteps.beta _ v)).trans ?_
  have e : Expr.subst 0 v (.val (Val.lam (.var 1))) = .val (Val.lam ((v.shift 1 0).1)) := by
    simp
  rw [e]
  refine (hK.2.2.2 _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  simp [subst_shift_succ]
  exact .refl

/-- The clause's body at the self-reference, `κ` given. -/
theorem fuel_clause {k : UInt32} {K : Kont} (hK : FuelFrame k K) (κ : Val) :
    PureSteps (K.plug (.app (.val fuelC) (.val (Val.pair .unit κ))))
      (.case (.val (fixSelf fuelStep k))
        (.app (.val spentV) (.app (.app (.val (κ.shift 1 0)) (.val (Val.inj₁ .unit))) (.val closeV)))
        (.app (.val (.lam (.app (.var 1) (.var 0))))
          (.app (.app (.val (κ.shift 1 0)) (.val (Val.inj₁ .unit))) (.val nextV)))) := by
  refine (PureSteps.plug K (PureSteps.beta _ _)).trans ?_
  refine (PureSteps.plug K (PureSteps.head (fun μ => Head.letpair μ .unit κ _) rfl)).trans ?_
  have e : Expr.subst 0 Val.unit (Expr.subst 0 (Val.shift 1 0 κ)
      (Expr.subst (0 + 2) (Val.shift 2 0 (Val.unit.pair κ)) (Expr.val (Val.lam fuelBody)))) =
      .val (Val.lam (.case (.var 0)
        (.app (.val spentV) (.app (.app (.val (κ.shift 2 0)) (.val (Val.inj₁ .unit)))
          (.val closeV)))
        (.app (.val (.lam (.app (.var 1) (.var 0))))
          (.app (.app (.val (κ.shift 2 0)) (.val (Val.inj₁ .unit))) (.val nextV))))) := by
    simp [fuelBody, spentV, subst_shift_succ, nextV, closeV]
  rw [e]
  refine (hK.2.2.2 _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  simp [spentV, subst_shift_succ, nextV, closeV]
  exact .refl

/-- The fixed point at one less, as a value. -/
def fixF (k : UInt32) : Val := Val.lam (.app (.val (.prim .boundedFix))
  (.pair (.val (fuelStep.shift 1 0)) (.pair (.val (.i32 (k - 1))) (.var 0))))

theorem fixF_closed (k : UInt32) : closedAt 0 (fixF k).1 = true := by
  have h₁ := closed_shift fuelStep_closed 1 0
  simp [fixF, closedAt, Val.i32, h₁, closedAt_mono _ fuelStep_closed (Nat.zero_le 1)]

theorem kapV_eq (ℓ : Loc) (H : Val) (K : Kont) : (kapV ℓ H K).1 = kappaC false ℓ H K := rfl

/-- **A tick under `div_fuel` with the budget spent** resumes `κ` with *close*, under `spent`. -/
theorem fuel_tick_zero {Tb : Table} (hTb : Tb.Mono) {K : Kont} (hK : FuelFrame 0 K) (K₁ : Kont)
    (hK₁ : K₁.HasHnd divEff = false) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (spentK.plug (hndE fuelH (K₁.plug (.val closeV)))) Tb Q ρ) :
    ewpTS ls (K.plug (hndE fuelH (K₁.plug tickE))) Tb Q ρ := by
  refine hnd_tick hTb fuelR fuelC K K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine ewp_pureSteps hTb (fuel_clause hK _) _ _ σ₂ ?_
  simp only [fixSelf]
  refine ewp_pureSteps hTb (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl) _ _ σ₂ ?_
  have e : Expr.subst 0 Val.unit (.app (.val spentV) (.app (.app (.val ((kapV ℓ fuelH K₁).shift 1 0))
      (.val (Val.inj₁ .unit))) (.val closeV))) =
      spentK.plug (.app (.app (kappaC false ℓ fuelH K₁) (.val (Val.inj₁ .unit))) (.val closeV)) := by
    simp [spentK, spentV, subst_shift_succ, closeV, kapV_eq, Kont.plug]
  show ewpTS ls (Expr.subst 0 Val.unit (.app (.val spentV) (.app (.app
    (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val closeV)))) Tb Q σ₂
  rw [e]
  exact ewp_kappaC_resume_in hTb spentK false ℓ fuelH K₁ closeV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

/-- **A tick under `div_fuel` with budget left** resumes `κ` with *next*, under the fixed point
at one less. -/
theorem fuel_tick_succ {Tb : Table} (hTb : Tb.Mono) {k : UInt32} (hk : k ≠ 0) {K : Kont}
    (hK : FuelFrame k K) (K₁ : Kont) (hK₁ : K₁.HasHnd divEff = false) {ls : List SRec}
    {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls ((nextK (fixF k)).plug (hndE fuelH (K₁.plug (.val nextV)))) Tb Q ρ) :
    ewpTS ls (K.plug (hndE fuelH (K₁.plug tickE))) Tb Q ρ := by
  refine hnd_tick hTb fuelR fuelC K K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine ewp_pureSteps hTb (fuel_clause hK _) _ _ σ₂ ?_
  rw [show fixSelf fuelStep k = Val.inj₂ (fixF k) from fixSelf_succ hk]
  refine ewp_pureSteps hTb (PureSteps.head (fun μ => Head.case₂ μ (fixF k) _ _) rfl) _ _ σ₂ ?_
  have e : Expr.subst 0 (fixF k) (.app (.val (.lam (.app (.var 1) (.var 0))))
      (.app (.app (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val nextV))) =
      (nextK (fixF k)).plug
        (.app (.app (kappaC false ℓ fuelH K₁) (.val (Val.inj₁ .unit))) (.val nextV)) := by
    have hc := fixF_closed k
    simp [nextK, subst_shift_succ, nextV, kapV_eq, closed_shift hc, Kont.plug]
  show ewpTS ls (Expr.subst 0 (fixF k) (.app (.val (.lam (.app (.var 1) (.var 0))))
      (.app (.app (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val nextV))))
    Tb Q σ₂
  rw [e]
  exact ewp_kappaC_resume_in hTb (nextK (fixF k)) false ℓ fuelH K₁ nextV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

/-! ### Totality -/

section
variable {S : Row} (hS : ∀ o ∈ S, o.n ≠ divEff) (δ : LSub) {Q : List SRec → Val → WProp}

include hS in
/-- **An operation of another name passes `div_fuel`**, under its frame. -/
theorem fuel_fwd {k : UInt32} {K : Kont} (hK : FuelFrame k K) {Φ Ψ : List SRec → Expr → WProp}
    (hΦ : ∀ ls e ρ, Φ ls e ρ → Ψ ls (K.plug (hndE fuelH e)) ρ) {ls : List SRec} {t : Expr}
    {ρ : WRes} (h : opTable (Row.tab S δ) ls t Φ ρ) :
    opTable (Row.tab S δ) ls (K.plug (hndE fuelH t)) Ψ ρ := by
  have heq : ∀ x, K.plug (hndE fuelH x) = (K.comp (hndK fuelH)).plug x := fun x => by
    rw [Kont.plug_comp]; rfl
  rw [heq]
  exact hnd_fwd (Row.tab_without hS δ) (Row.tab_plainCancel S δ) K hK.1 hK.2.1 hK.2.2.1 _ _ _
    (fun ls x ρ h => by show Ψ ls ((K.comp (hndK fuelH)).plug x) ρ; rw [← heq]; exact hΦ ls x ρ h) h

include hS in
/-- **`div_fuel` of a computation of `Closing`, the budget spent, is total**: every tick is
answered *close*, and `Closing`'s least fixed point bounds them. -/
theorem fuel_closing {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Closing (Row.tab (tickSig :: S) δ) Q ls e ρ) :
    ∀ {K : Kont}, FuelFrame 0 K → ewpTS ls (K.plug (hndE fuelH e)) (opTable (Row.tab S δ)) Q ρ := by
  have hM := opTable_mono (Row.tab S δ)
  intro K₀ hK₀
  refine ewp_ind (fun ls e ρ => ∀ (K : Kont), FuelFrame 0 K →
    ewpTS ls (K.plug (hndE fuelH e)) (opTable (Row.tab S δ)) Q ρ) ?_ h K₀ hK₀
  intro ls e ρ hs K hK
  have e₁ : ∀ x, K.plug (hndE fuelH x) = (K.comp (hndK fuelH)).plug x := fun x => by
    rw [Kont.plug_comp]; rfl
  rw [e₁]
  refine ewp_fold hM (wpG_bind _ e ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
  rw [← e₁]
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact ewp_unfold hM (ewp_pureSteps hM (fuel_ret hK v) _ _ σ (ewp_val hM hv))
  rcases ht with ⟨K₁, m, i, v, en, hp'⟩ | ⟨K₁, m, i, v, en, hp'⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp'
    by_cases hk : m = divEff ∧ i = 0
    · -- a tick, answered *close*
      obtain ⟨rfl, rfl⟩ := hk
      rw [OpTab.closeAt_key, Row.tab_tick_key] at hT
      cases hT
      have ht := tickSig_isTick δ
      obtain ⟨rfl, rfl⟩ := (ht.2.2.1 ls' v ρa).mp hA
      rw [eq_of_compS_empty_left hcak]
      refine ewp_unfold hM (fuel_tick_zero hM hK K₁ hK₁ ?_)
      exact (hcont ls' (Ext.refl ls' _)).1 closeV PMap.empty _
        ⟨(ht.2.2.2 ls' closeV _).mpr ⟨Or.inr rfl, rfl⟩, rfl⟩ (ResU.comp_empty_right _) _
        spentK_frame
    · rw [OpTab.closeAt_ne hk, Row.tab_tick_ne S δ hk] at hT
      refine wpG_here _ _ _ σ (Or.inr (fuel_fwd hS δ hK (Φ := fun ls e ρ => ∀ (K : Kont),
        FuelFrame 0 K → ewpTS ls (K.plug (hndE fuelH e)) (opTable (Row.tab S δ)) Q ρ) ?_
        (Or.inl ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, hcont⟩⟩)))
      exact fun _ _ _ h => h K hK
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp'
    by_cases hk : m = divEff ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      rw [OpTab.closeAt_key, Row.tab_tick_key] at hT
      cases hT
      exact absurd ha (by simp [OpEnt.closeOnly, OpSig.ent, OpSig.abort, tickSig, VTy.isZero])
    · rw [OpTab.closeAt_ne hk, Row.tab_tick_ne S δ hk] at hT
      refine wpG_here _ _ _ σ (Or.inr (fuel_fwd hS δ hK (Φ := fun ls e ρ => ∀ (K : Kont),
        FuelFrame 0 K → ewpTS ls (K.plug (hndE fuelH e)) (opTable (Row.tab S δ)) Q ρ) ?_
        (Or.inr ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT, ha⟩ hrest⟩)))
      exact fun _ _ _ h => h K hK

include hS in
/-- **`div_fuel` is total**: at every budget, for every computation of `cwp`, in `ewpTS` at the
rest of the row, by induction on the budget and, inside, on the segment.  `[spec §14]` -/
theorem fuel_total : ∀ (n : ℕ) (k : UInt32), k.toNat = n → ∀ {K : Kont}, FuelFrame k K →
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, cwp (Row.tab (tickSig :: S) δ) Q ls e ρ →
      ewpTS ls (K.plug (hndE fuelH e)) (opTable (Row.tab S δ)) Q ρ := by
  have hM := opTable_mono (Row.tab S δ)
  intro n
  induction n with
  | zero =>
      intro k hk K hK ls e ρ h
      have hk0 : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
      subst hk0
      exact fuel_closing hS δ (closing_of_cwp h) hK
  | succ m ih =>
      intro k hk K hK ls e ρ h
      have hk0 : k ≠ 0 := fun h' => by subst h'; simp at hk
      have hkm : (k - 1).toNat = m := by
        have : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt32.toNat_sub_of_le]
          · rfl
          · rw [UInt32.le_iff_toNat_le]; simp; omega
        omega
      refine ewp_ind (fun ls e ρ => ∀ (K : Kont), FuelFrame k K →
        ewpTS ls (K.plug (hndE fuelH e)) (opTable (Row.tab S δ)) Q ρ) ?_ (cwp_out h) K hK
      intro ls e ρ hs K hK
      have e₁ : ∀ x, K.plug (hndE fuelH x) = (K.comp (hndK fuelH)).plug x := fun x => by
        rw [Kont.plug_comp]; rfl
      rw [e₁]
      refine ewp_fold hM (wpG_bind _ e ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
      rw [← e₁]
      rcases ht with ⟨v, rfl, hv⟩ | ht | ht
      · exact ewp_unfold hM (ewp_pureSteps hM (fuel_ret hK v) _ _ σ (ewp_val hM hv))
      · -- another operation passes the handler
        have hT' : ∀ n i en, (Row.tab (tickSig :: S) δ).erase0 n i = some en →
            Row.tab S δ n i = some en := by
          intro n i en h'
          unfold OpTab.erase0 at h'
          split at h'
          · cases h'
          · rwa [Row.tab_tick_ne S δ (by assumption)] at h'
        refine wpG_here _ _ _ σ (Or.inr (fuel_fwd hS δ hK (Φ := fun ls e ρ => ∀ (K : Kont),
          FuelFrame k K → ewpTS ls (K.plug (hndE fuelH e)) (opTable (Row.tab S δ)) Q ρ) ?_
          (opTable_le (fun n i en h' => ⟨en, hT' n i en h', OpEnt.Le.refl en⟩) ht)))
        exact fun _ _ _ h => h K hK
      · -- a tick, answered *next*
        obtain ⟨K₁, en, rfl, hK₁, hT0, ht', hcont⟩ :=
          tickStop_inv (Row.divOK_of_divB (Row.divB_tick S) δ) ht
        refine ewp_unfold hM (fuel_tick_succ hM hk0 hK K₁ hK₁ ?_)
        exact ih (k - 1) hkm (nextK_frame k) (hcont ls' (Ext.refl ls' σ) nextV (Or.inl rfl)).1

end

/-! ### The constant -/

/-- `div_fuel : !U(U(1 ⊸ F_{tick, Σ} A) ⊗ I32 ⊸ F_Σ A)`, the computation a callback
`U(1 ⊸ F_{tick, Σ} A)`.  `[spec §14]` -/
abbrev divFuelTy (S : Row) (A : VTy) : VTy :=
  .bang (.thunk (.arr (.tensor (.thunk (.arr .unit (CTy.effOf (tickSig :: S) A))) (.int .w32))
    (CTy.effOf S A)))

/-- `div_fuel (t, k) ↦* (λg. bounded_fix (fuelStep, (k, g))) (hnd_Div H (t ()))`. -/
theorem divFuel_steps (t : Val) (k : UInt32) :
    PureSteps (.app (.val divFuelV) (.val (Val.pair t (Val.i32 k))))
      ((fuelK k).plug (hndE fuelH (.app (.val t) (.val .unit)))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ t (Val.i32 k) _) rfl).trans ?_
  have hs : closedAt 0 fuelStep.1 = true := fuelStep_closed
  have hH : closedAt 0 fuelH.1 = true := by
    simp [fuelH, hndVal, qualsVal, fuelR, fuelC, fuelBody, spentV, closedAt, Val.pair, Val.i32,
      Qual.tag, nextV, closeV]
  simp [fuelK, Kont.plug, BoCa.BoLo.hndE, closed_subst hs, closed_subst hH, subst_shift_succ,
    Val.i32, Val.pair]
  exact .refl

/-- **`div_fuel` is sound**: total at the rest of the row.  `[spec §14]` -/
theorem divFuel_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy}
    (hS : ∀ o ∈ S, o.n ≠ divEff) (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val divFuelV) (divFuelTy S A) := by
  refine sem_const hΓ divFuelV_closed fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨t, vk, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, ht, ⟨rfl, n, rfl⟩⟩ := pure_sep_iff.mp hk
  rw [compS_empty_eq hc]
  refine (cC_effOf S A ls' δ _ σ₁ (Row.divB_of_without hS)).mpr ?_
  refine ewp_pureSteps (opTable_mono _) (divFuel_steps t n) _ _ σ₁ ?_
  have hM := (cC_effOf_wp (tickSig :: S) A ls' δ _ σ₁).mp
    (ht ls' (Ext.refl _ _) .unit PMap.empty σ₁ ⟨rfl, rfl⟩ (ResU.comp_empty_right σ₁))
  rw [Row.divB_tick] at hM
  exact fuel_total hS δ n.toNat n rfl (fuelK_frame n) hM

end BoCa.Fig16.LogRel.Core

end
