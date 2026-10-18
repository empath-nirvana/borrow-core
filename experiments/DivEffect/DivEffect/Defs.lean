import Core.EffFin
import Core.NuRel
import Core.Fix

/-!
# DivEffect — `Div` as a handled effect: the relation  (`docs/pipeline-architecture.md` §4.1)

`Div` is a name `d` with one linear operation `tick : 1 ↠ Next`, `Next = 1 ⊕ 1`, `inl ()` the
answer *next* and `inr ()` the answer *close*.

`ewpTS` is a least fixed point, so a computation that ticks forever is not in it.  The relation
at a row holding `Div` is a greatest fixed point over **segments**: each segment, up to the next
tick, is an `ewpTS` run, and a tick stops it, owing its continuation to the candidate.

    cwp T Q  ≜  gfp W. ewpTS · (opTable T ∨ Π_W) Q
    Π_W(tick)  =  λ_. λκ. ∀ n : Next. W (κ n) ∧ Closing (κ n)

`T` is the table of the rest of the row.  The tick stop `Π_W` owes nothing to the segment's least
fixed point: it is `performStop` at the tick's entry with the candidate in place of the
continuation the least fixed point would owe.

**`Closing`**, the second conjunct, is what makes a close a close.  It is the least fixed point at
the table where a tick may only be answered *close* (`closeEnt`): after a close, the computation
reaches its end through finitely many ticks, each answered close.  Without it the candidate
admits a computation that ignores every close (`Plain.lean`), and no handler with a linear
continuation can stop it: `div_fuel`'s totality and `reify`'s `close` both read it.

Every definition reuses Core's: `performStop`, `opTable`, `OpTab.ext`, `ewpTS`, `ewp_mono`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappa kappaC kappaCell kappaAt clauseAt capTag)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The effect -/

/-- `Next = 1 ⊕ 1`. -/
abbrev nextTy : VTy := .sum .unit .unit

/-- The answer *next*. -/
def nextV : Val := .inj₁ .unit

/-- The answer *close*. -/
def closeV : Val := .inj₂ .unit

/-- `tick : 1 ↠ Next`, the operation `0` of the name `d`, linear: its continuation has no
cancel. -/
def tickSig (d : UInt32) : OpSig := ⟨d, 0, .lin, .unit, nextTy, .ret .unit⟩

/-- `tick ()`. -/
def tickE (d : UInt32) : Expr := performE (.val (opPayload d 0 .unit))

/-- The tick's entry, as Core's row entry gives it. -/
abbrev tickEnt (δ : LSub) (d : UInt32) : OpEnt := (tickSig d).ent δ

/-- The tick where it may only be answered *close*: `tick : 1 ↠ 0 ⊕ 1`, whose one answer is
`inr ()`. -/
def closeSig (d : UInt32) : OpSig := ⟨d, 0, .lin, .unit, .sum .zero .unit, .ret .unit⟩

/-- The tick's entry where it may only be answered *close*: a row entry, so `Closing` is Core's
`ewpTS` at a row (`closing_row`). -/
abbrev closeEnt (δ : LSub) (d : UInt32) : OpEnt := (closeSig d).ent δ

/-- The table of the tick alone. -/
def tickT (δ : LSub) (d : UInt32) : OpTab := OpTab.ext d 0 (tickEnt δ d) OpTab.empty

/-! ### The relation -/

/-- `Closing T Q`: the computation ends, at `Q`, through finitely many ticks, each answered
*close*: the least fixed point at the rest of the row and a tick whose only answer is close. -/
def Closing (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) : CPred :=
  fun ls e => ewpTS ls e (opTable (OpTab.ext d 0 (closeEnt δ d) T)) Q

/-- What a tick owes its continuation, at the candidate `W`: `W` and `Closing`, at each answer. -/
def owe (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) (W : CPred) : CPred :=
  fun ls e ρ => W ls e ρ ∧ Closing δ d T Q ls e ρ

/-- The table of a segment at the candidate `W`: a stop of the rest of the row, or a tick, which
owes its continuation to `W` and to `Closing` (`owe`), not to the segment's least fixed point. -/
def divTab (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) (W : CPred) :
    Table := fun ls t Φ =>
  BoLo.or (opTable T ls t Φ) (performStop (tickT δ d) ls t (owe δ d T Q W))

/-- One unfolding of the greatest fixed point: a segment at the candidate. -/
def cwpF (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) (W : CPred) : CPred :=
  fun ls e => ewpTS ls e (divTab δ d T Q W) Q

/-- **`cwp`**: the greatest fixed point of `cwpF`, `⋃{W | W ⊆ cwpF W}`, written in `Prop` as
`∃ W`, as `𝒞⟦νX. C⟧` is (`nuRel`). -/
def cwp (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) : CPred :=
  fun ls e ρ => ∃ W : CPred, W.Le (cwpF δ d T Q W) ∧ W ls e ρ

/-! ### Monotonicity -/

theorem divTab_mono (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp)
    (W : CPred) : (divTab δ d T Q W).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with h | h
  · exact Or.inl (opTable_mono T ls t Φ Φ' ρ hΦ h)
  · exact Or.inr h

theorem owe_mono {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp}
    {W W' : CPred} (h : W.Le W') : (owe δ d T Q W).Le (owe δ d T Q W') :=
  fun ls e ρ hw => ⟨h ls e ρ hw.1, hw.2⟩

theorem divTab_le {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp}
    {W W' : CPred} (h : W.Le W') {ls : List SRec} {t : Expr} {Φ : List SRec → Expr → WProp}
    {ρ : WRes} (hd : divTab δ d T Q W ls t Φ ρ) : divTab δ d T Q W' ls t Φ ρ := by
  rcases hd with hd | hd
  · exact Or.inl hd
  · exact Or.inr (performStop_mono _ ls t _ _ ρ (fun ls e ρ hw => owe_mono h ls e ρ hw) hd)

theorem cwpF_mono {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp}
    {W W' : CPred} (h : W.Le W') : (cwpF δ d T Q W).Le (cwpF δ d T Q W') :=
  fun _ _ _ hw => ewp_mono (divTab_mono δ d T Q W') (fun _ _ _ _ hd => divTab_le h hd)
    (fun _ _ _ hq => hq) hw

/-! ### The greatest fixed point -/

/-- **Coinduction.** -/
theorem cwp_coind {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp} {W : CPred}
    (hW : W.Le (cwpF δ d T Q W)) : W.Le (cwp δ d T Q) :=
  fun _ _ ρ hw => ⟨W, hW, hw⟩

theorem cwp_out {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp} :
    (cwp δ d T Q).Le (cwpF δ d T Q (cwp δ d T Q)) := by
  rintro ls e ρ ⟨W, hW, hw⟩
  exact cwpF_mono (cwp_coind hW) ls e ρ (hW ls e ρ hw)

theorem cwp_roll {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp} :
    (cwpF δ d T Q (cwp δ d T Q)).Le (cwp δ d T Q) :=
  cwp_coind (W := cwpF δ d T Q (cwp δ d T Q)) (cwpF_mono cwp_out)

/-- **Coinduction up to `cwp`**: a candidate need only reach `W ∪ cwp`. -/
theorem cwp_coind_up {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp}
    {W : CPred} (hW : W.Le (cwpF δ d T Q (fun ls e ρ => W ls e ρ ∨ cwp δ d T Q ls e ρ))) :
    W.Le (cwp δ d T Q) := by
  have h : CPred.Le (fun ls e ρ => W ls e ρ ∨ cwp δ d T Q ls e ρ)
      (cwpF δ d T Q (fun ls e ρ => W ls e ρ ∨ cwp δ d T Q ls e ρ)) := by
    rintro ls e ρ (hw | hc)
    · exact hW ls e ρ hw
    · exact cwpF_mono (fun _ _ _ h => Or.inr h) ls e ρ (cwp_out ls e ρ hc)
  exact fun ls e ρ hw => cwp_coind h ls e ρ (Or.inl hw)

/-! ### `Closing` -/

/-- The closing tick's one answer: *close*, at the empty resource. -/
theorem vC_close {δ : LSub} {d : UInt32} {ls : List SRec} {w : Val} {ρ : WRes} :
    (closeEnt δ d).PB ls w ρ ↔ w = closeV ∧ ρ = PMap.empty := by
  constructor
  · rintro (⟨v, ρ₁, ρ₂, hc, ⟨rfl, rfl⟩, hz⟩ | ⟨v, ρ₁, ρ₂, hc, ⟨rfl, rfl⟩, hu⟩)
    · exact hz.elim
    · obtain ⟨rfl, rfl⟩ := hu
      exact ⟨rfl, eq_of_compS_empty_left hc⟩
  · rintro ⟨rfl, rfl⟩
    exact Or.inr ⟨.unit, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The tick entries agree on everything but the answers: *close* is one of `Next`'s. -/
theorem closeEnt_le (δ : LSub) (d : UInt32) :
    ∀ ls w ρ, (closeEnt δ d).PB ls w ρ → (tickEnt δ d).PB ls w ρ := by
  intro ls w ρ h
  obtain ⟨rfl, rfl⟩ := vC_close.mp h
  exact Or.inr ⟨.unit, ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩

/-- **`Closing` is Core's `ewpTS` at a row**: the rest of the row with the closing tick in front. -/
theorem closing_row (δ : LSub) (d : UInt32) (S : Row) :
    OpTab.ext d 0 (closeEnt δ d) (Row.tab S δ) = Row.tab (closeSig d :: S) δ := by
  funext n i
  simp only [OpTab.ext, Row.tab, Row.find, List.find?]
  by_cases h : n = d ∧ i = 0
  · simp [h, closeSig]; rfl
  · rw [if_neg h]
    have : decide (n = (closeSig d).n ∧ i = (closeSig d).i) = false := by
      simp only [closeSig]; exact decide_eq_false h
    simp [this]

/-- `Next`'s relation: `next` or `close`, at the empty resource. -/
theorem vC_next {ls : List SRec} {δ : LSub} {w : Val} {ρ : WRes}
    (h : vC true nextTy ls δ w ρ) : (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty := by
  rcases h with ⟨v, ρ₁, ρ₂, hc, ⟨rfl, hv⟩, hu⟩ | ⟨v, ρ₁, ρ₂, hc, ⟨rfl, hv⟩, hu⟩
  · obtain ⟨rfl, rfl⟩ := hu
    subst hv
    exact ⟨Or.inl rfl, eq_of_compS_empty_left hc⟩
  · obtain ⟨rfl, rfl⟩ := hu
    subst hv
    exact ⟨Or.inr rfl, eq_of_compS_empty_left hc⟩

/-- The tick's table holds only the tick. -/
theorem tickT_some {δ : LSub} {d n i : UInt32} {en : OpEnt} (h : tickT δ d n i = some en) :
    n = d ∧ i = 0 ∧ en = tickEnt δ d := by
  unfold tickT OpTab.ext at h
  by_cases hn : n = d ∧ i = 0
  · rw [if_pos hn] at h; exact ⟨hn.1, hn.2, (Option.some.inj h).symm⟩
  · rw [if_neg hn] at h; exact absurd h (by simp [OpTab.empty])

/-- The rest of the row is below the row with a tick at `(d, 0)` it does not hold. -/
theorem le_ext {T : OpTab} {d : UInt32} (hTd : T d 0 = none) (en : OpEnt) :
    T.Le (OpTab.ext d 0 en T) := by
  intro n i en' h
  refine ⟨en', ?_, OpEnt.Le.refl en'⟩
  unfold OpTab.ext
  by_cases hn : n = d ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := hn; rw [hTd] at h; cases h
  · rw [if_neg hn]; exact h

/-- **A segment's ticks owe `Closing`**, so every computation of `cwp` is in `Closing`: answered
*close* at every tick, it ends. -/
theorem closing_of_cwpF {δ : LSub} {d : UInt32} {T : OpTab} (hTd : T d 0 = none)
    {Q : List SRec → Val → WProp}
    {W : CPred} {ls : List SRec} {e : Expr} {ρ : WRes} (h : cwpF δ d T Q W ls e ρ) :
    Closing δ d T Q ls e ρ := by
  refine ewp_ind (fun ls e ρ => Closing δ d T Q ls e ρ) ?_ h
  intro ls e ρ hs
  refine ewp_fold (opTable_mono _) (wpG_mono (fun ls' t σ ht => ?_) hs)
  rcases ht with hv | ht | ht
  · exact Or.inl hv
  · -- a stop of the rest of the row
    exact Or.inr (opTable_le (le_ext hTd _) ht)
  · -- a tick: its continuation is in `Closing` at *close*
    obtain ⟨K, n, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
    refine Or.inr (Or.inl ⟨K, n, 0, v, closeEnt δ n,
      pure_sep_mk ⟨rfl, hK, by simp [OpTab.ext], rfl⟩ ⟨ρa, ρk, hcak, hA,
        And.intro (fun h => nomatch h) (fun ls'' he => And.intro (fun w τ₁ τ₂ hB hc =>
          ((hcont ls'' he).1 w τ₁ τ₂ (closeEnt_le δ n ls'' w τ₁ hB) hc).2)
          (fun h => absurd rfl h))⟩⟩)

theorem closing_of_cwp {δ : LSub} {d : UInt32} {T : OpTab} (hTd : T d 0 = none)
    {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cwp δ d T Q ls e ρ) : Closing δ d T Q ls e ρ :=
  closing_of_cwpF hTd (cwp_out ls e ρ h)

end BoCa.Fig16.LogRel.Core.DivEffect

end
