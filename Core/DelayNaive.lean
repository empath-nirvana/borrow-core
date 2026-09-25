import Core.DelayPrograms
import Core.Steps

/-!
# Core — `f = λd. later (g d)` is not a guardedness condition

A `fix` whose premise is only that `f` has the shape `λd. later (g d)`, with `g : U(D A) ⊸ D A`
typed as any other term, admits `g = skip`:

    skip d = ⟨(d π₁) to x. case x {inj₁ a. now a | inj₂ t. t π₁}, d π₂⟩

`skip` drops one `later` of its argument; it is a `CDerives` derivation (`d_skip`), so
`fundamentalC` gives it its semantic type.  The fixed point `N = later (skip N)` (`NV`, built
with the Z combinator) is not in `⟦D 1⟧` (`naive_not_delay`, `naive_not_sem`): its first `next`
returns `later t` (`nv_next_run`), and the `next` of `t` has no terminating run
(`tv_next_diverges`) — forcing `t` forces `N`, whose `later` hands back `t` itself, and `skip`
forces that again.  The step relation is deterministic along the way (`Steps.lean`'s
`step1_plug_inv`, with the head-step inversions below), so every run revisits its start.

`skip` observes `d` twice for each `later` it emits.  In `fixD` the step returns a state, not a
`D A`, and cannot observe the recursive computation at all (`Delay.lean`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### `skip` -/

/-- `(d π₁) to x. case x {inj₁ a. inj₁ a | inj₂ t. t π₁}`, under `withPair`'s binders. -/
def skipM : Expr :=
  bindE (.app (.var 2) (.val (.inj₁ .unit))) (.case (.var 0) (.inj₁ (.var 0)) (.app (.var 0) (.val (.inj₁ .unit))))

/-- `skip = λd. ⟨skipM, d π₂⟩`. -/
def skipV : Val := .lam (withPair skipM (.app (.var 2) (.val (.inj₂ .unit))))

/-- `skip : U(U(D 1) ⊸ D 1)`, a derivation. -/
theorem d_skip {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val skipV)
      (.val (.thunk (.arr (.thunk (.delay .unit)) (.delay .unit)))) :=
  .thunkV rfl (.lam (.delayIn (.withI
    (.bind (.dead (.dead (.left (deadSplit hΓ))))
      (.proj₁ (.delayOut (.force (.there (.there (.here hΓ))))))
      (.sumE (.left (.dead (.dead (.dead (deadSplit hΓ)))))
        (.var (.here (.cons (.cons (.cons hΓ)))))
        (.ret (.sumI₁ (.var (.here (.cons (.cons (.cons (.cons hΓ))))))))
        (.proj₁ (.delayOut (.force (.here (.cons (.cons (.cons (.cons hΓ))))))))))
    (.proj₂ (.delayOut (.force (.there (.there (.here hΓ)))))))))

theorem skip_sem : SemV LifeCtx.empty [] (.val skipV)
    (.thunk (.arr (.thunk (.delay .unit)) (.delay .unit))) :=
  fundamentalC (d_skip .nil)

/-! ### `N = later (skip N)` -/

/-- `λo′. skip (self ()) o′`, under `withPair`'s binders and the Z binders `self`, `u`. -/
def teO : Expr := .val (.lam (.app (.app (.val skipV) (.app (.var 4) (.val .unit))) (.var 0)))

/-- The Z body: `λself. λu. later (λo′. skip (self ()) o′)`, `later t = ⟨return inj₂ t, t π₂⟩`. -/
def bN : Expr := withPair (.inj₂ teO) (.app teO (.val (.inj₂ .unit)))

theorem bN_closed : closedAt 2 bN = true := rfl

/-- The recursive handle. -/
abbrev selfN : Val := selfV bN

/-- `t = λo′. skip (self ()) o′`. -/
def TV : Val := .lam (.app (.app (.val skipV) (.app (.val selfN) (.val .unit))) (.var 0))

/-- `N = later t`. -/
def NV : Val := .lam (.case (.var 0) (.seq (.var 0) (.inj₂ (.val TV)))
  (.seq (.var 0) (.app (.val TV) (.val (.inj₂ .unit)))))

/-- `N` is the Z combinator's fixed point: `self ()` reaches `N`. -/
theorem fixV_bN : (bN.subst 1 selfN).subst 0 .unit = .val NV := rfl

/-- `continuation of skip's next`, at `x`. -/
def kS : Expr := .case (.var 0) (.inj₁ (.var 0)) (.app (.var 0) (.val (.inj₁ .unit)))

/-- `skip N`. -/
def SV : Val := .lam (.case (.var 0)
  (.seq (.var 0) (bindE (.app (.val NV) (.val (.inj₁ .unit))) kS))
  (.seq (.var 0) (.app (.val NV) (.val (.inj₂ .unit)))))

/-! ### Head-step inversions -/

theorem step1_case₁_inv {μ μ₁ : Heap} {e₁ e₂ e' : Expr} {v : Val}
    (h : Step1 μ (.case (.inj₁ v.1) e₁ e₂) μ₁ e') : μ₁ = μ ∧ e' = e₁.subst 0 v := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | case K u w =>
        simp only [Kont.plug, Expr.case.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.inj₁ v.2)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.case (.inj₁ v.1) e₁ e₂ = E at hh
  cases hh with
  | case₁ v' e₁' e₂' =>
      simp only [Expr.case.injEq] at hE
      obtain ⟨hv, rfl, rfl⟩ := hE
      have : v = v' := Subtype.ext (by injection hv)
      subst this; exact ⟨rfl, rfl⟩
  | _ => simp_all

theorem step1_case₂_inv {μ μ₁ : Heap} {e₁ e₂ e' : Expr} {v : Val}
    (h : Step1 μ (.case (.inj₂ v.1) e₁ e₂) μ₁ e') : μ₁ = μ ∧ e' = e₂.subst 0 v := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | case K u w =>
        simp only [Kont.plug, Expr.case.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.inj₂ v.2)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.case (.inj₂ v.1) e₁ e₂ = E at hh
  cases hh with
  | case₂ v' e₁' e₂' =>
      simp only [Expr.case.injEq] at hE
      obtain ⟨hv, rfl, rfl⟩ := hE
      have : v = v' := Subtype.ext (by injection hv)
      subst this; exact ⟨rfl, rfl⟩
  | _ => simp_all

theorem step1_seq_inv {μ μ₁ : Heap} {e e' : Expr} (h : Step1 μ (.seq .unit e) μ₁ e') :
    μ₁ = μ ∧ e' = e := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | seq K u =>
        simp only [Kont.plug, Expr.seq.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.unit)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.seq .unit e = E at hh
  cases hh with
  | seq e'' =>
      simp only [Expr.seq.injEq] at hE
      obtain ⟨-, rfl⟩ := hE
      exact ⟨rfl, rfl⟩
  | _ => simp_all

/-- A redex in a context steps only by its head step. -/
theorem det_beta (K : Kont) (b : Expr) (v : Val) {μ μ₁ : Heap} {e₁ : Expr}
    (h : Step1 μ (K.plug (.app (.val (.lam b)) (.val v))) μ₁ e₁) : e₁ = K.plug (b.subst 0 v) := by
  obtain ⟨e', rfl, h'⟩ := step1_plug_inv K (by intro h; cases h) h
  rw [(step1_beta_inv h').2]

theorem det_case₁ (K : Kont) (v : Val) (e₁ e₂ : Expr) {μ μ₁ : Heap} {e' : Expr}
    (h : Step1 μ (K.plug (.case (.val (.inj₁ v)) e₁ e₂)) μ₁ e') : e' = K.plug (e₁.subst 0 v) := by
  obtain ⟨e'', rfl, h'⟩ := step1_plug_inv K not_isVal_case h
  rw [(step1_case₁_inv h').2]

theorem det_case₂ (K : Kont) (v : Val) (e₁ e₂ : Expr) {μ μ₁ : Heap} {e' : Expr}
    (h : Step1 μ (K.plug (.case (.val (.inj₂ v)) e₁ e₂)) μ₁ e') : e' = K.plug (e₂.subst 0 v) := by
  obtain ⟨e'', rfl, h'⟩ := step1_plug_inv K not_isVal_case h
  rw [(step1_case₂_inv h').2]

theorem det_seq (K : Kont) (e : Expr) {μ μ₁ : Heap} {e' : Expr}
    (h : Step1 μ (K.plug (.seq (.val .unit) e)) μ₁ e') : e' = K.plug e := by
  obtain ⟨e'', rfl, h'⟩ := step1_plug_inv K not_isVal_seq h
  rw [(step1_seq_inv h').2]

/-! ### The cycle -/

/-- `inj₁ ()`, the `next` observation. -/
abbrev o₁ : Val := .inj₁ .unit

abbrev zN : Val := zX bN

/-- `skip (self ()) o₁` with `self ()` in evaluation. -/
abbrev K₁ : Kont := .appL (.appR (.val skipV) .hole) o₁
abbrev K₂ : Kont := .appL (.appR (.val skipV) (.appL .hole .unit)) o₁
abbrev K₅ : Kont := .appL .hole o₁
abbrev K₉ : Kont := .appR (.val (.lam kS)) .hole

/-- The body of `skip`'s `next` at `N`. -/
abbrev sM : Expr := bindE (.app (.val NV) (.val o₁)) kS
abbrev sN : Expr := .app (.val NV) (.val (.inj₂ .unit))

/-- The states of `t`'s `next`, in order; the last steps back to the first. -/
def cyc : List Expr :=
  [ .app (.val TV) (.val o₁),
    K₁.plug (.app (.val selfN) (.val .unit)),
    K₂.plug (.app (.val zN) (.val zN)),
    K₂.plug (.app (.val (.lam (.lam bN))) (.val selfN)),
    K₁.plug (.app (.val (.lam (bN.subst 1 selfN))) (.val .unit)),
    K₅.plug (.app (.val skipV) (.val NV)),
    .app (.val SV) (.val o₁),
    .case (.val o₁) (.seq (.var 0) sM) (.seq (.var 0) sN),
    .seq (.val .unit) sM,
    K₉.plug (.app (.val NV) (.val o₁)),
    K₉.plug (.case (.val o₁) (.seq (.var 0) (.inj₂ (.val TV)))
      (.seq (.var 0) (.app (.val TV) (.val (.inj₂ .unit))))),
    K₉.plug (.seq (.val .unit) (.inj₂ (.val TV))),
    .app (.val (.lam kS)) (.val (.inj₂ TV)),
    .case (.val (.inj₂ TV)) (.inj₁ (.var 0)) (.app (.var 0) (.val o₁)) ]

theorem cyc_mem {e : Expr} (k : Nat) (hk : k < cyc.length) (h : cyc[k] = e) : e ∈ cyc :=
  h ▸ List.getElem_mem hk

/-- Every step from a state of the cycle lands in the cycle. -/
theorem cyc_step {μ μ₁ : Heap} {e e₁ : Expr} (he : e ∈ cyc) (h : Step1 μ e μ₁ e₁) : e₁ ∈ cyc := by
  simp only [cyc, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [det_beta .hole _ o₁ h]; exact cyc_mem 1 (by decide) rfl
  · rw [det_beta K₁ _ .unit h]; exact cyc_mem 2 (by decide) rfl
  · rw [det_beta K₂ _ zN h]; exact cyc_mem 3 (by decide) rfl
  · rw [det_beta K₂ _ selfN h]; exact cyc_mem 4 (by decide) rfl
  · rw [det_beta K₁ _ .unit h]; exact cyc_mem 5 (by decide) rfl
  · rw [det_beta K₅ _ NV h]; exact cyc_mem 6 (by decide) rfl
  · rw [det_beta .hole _ o₁ h]; exact cyc_mem 7 (by decide) rfl
  · rw [det_case₁ .hole .unit _ _ h]; exact cyc_mem 8 (by decide) rfl
  · rw [det_seq .hole _ h]; exact cyc_mem 9 (by decide) rfl
  · rw [det_beta K₉ _ o₁ h]; exact cyc_mem 10 (by decide) rfl
  · rw [det_case₁ K₉ .unit _ _ h]; exact cyc_mem 11 (by decide) rfl
  · rw [det_seq K₉ _ h]; exact cyc_mem 12 (by decide) rfl
  · rw [det_beta .hole _ (.inj₂ TV) h]; exact cyc_mem 13 (by decide) rfl
  · rw [det_case₂ .hole TV _ _ h]; exact cyc_mem 0 (by decide) rfl

/-- No state of the cycle is a value. -/
theorem cyc_not_val {e : Expr} (he : e ∈ cyc) : ¬ IsVal e := by
  simp only [cyc, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (intro h; cases h)

/-- A run from a state of the cycle never reaches a value. -/
theorem cyc_no_run {μ μ' : Heap} {e : Expr} {w : Val} (hs : Steps μ e μ' w.1) (he : e ∈ cyc) :
    False := by
  generalize hW : w.1 = W at hs
  induction hs with
  | refl μ E => subst hW; exact cyc_not_val he w.2
  | more h _ ih => exact ih (cyc_step he h) hW

/-- **`t`'s `next` has no terminating run.** -/
theorem tv_next_diverges {μ μ' : Heap} {w : Val} :
    ¬ Steps μ (.app (.val TV) (.val o₁)) μ' w.1 :=
  fun hs => cyc_no_run hs (List.mem_cons_self ..)

/-- **`N`'s `next` returns `later t`**: every run ends at `inj₂ t`. -/
theorem nv_next_run {μ μ' : Heap} {w : Val} (hs : Steps μ (.app (.val NV) (.val o₁)) μ' w.1) :
    w = .inj₂ TV := by
  have h₁ := steps_peel (e' := .case (.val o₁) (.seq (.var 0) (.inj₂ (.val TV)))
      (.seq (.var 0) (.app (.val TV) (.val (.inj₂ .unit))))) (m := μ) hs (by intro h; cases h)
    (fun μ₁ e₁ h => ⟨(step1_beta_inv h).1, (step1_beta_inv h).2⟩)
  have h₂ := steps_peel (e' := .seq (.val .unit) (.inj₂ (.val TV))) (m := μ) h₁ not_isVal_case
    (fun μ₁ e₁ h => step1_case₁_inv (v := .unit) h)
  have h₃ := steps_peel (e' := (Val.inj₂ TV).1) (m := μ) h₂ not_isVal_seq
    (fun μ₁ e₁ h => step1_seq_inv h)
  exact (steps_from_val h₃).2

/-- **`N = later (skip N)` is not a delayed computation**: `⟦D 1⟧` does not hold of it at the
empty list and resource. -/
theorem naive_not_delay (δ : LSub) : ¬ cC (.delay .unit) [] δ (.val NV) PMap.empty := by
  intro h
  have h₁ := (delayRel_out _ [] _ _ h).1
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', -, k₂, k₃, -, k₆, -, k₈, -, -, -,
    kT, ktg, -, -, kQ⟩ :=
    h₁ PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
  obtain rfl := nv_next_run k₈
  obtain ⟨_, σ₀, σ₃, _, ⟨_, he⟩, _⟩ | ⟨t, σ₀, σ₃, hc, ⟨hσ₀, he⟩, ht⟩ := kQ
  · cases he
  have ht' : t = TV := Val.ext (Expr.inj₂.inj (congrArg Subtype.val he)).symm
  subst ht' hσ₀
  obtain rfl := eq_of_compS_empty_left hc
  obtain rfl := eq_of_compS_empty_left k₂
  have h₂ := (delayRel_out _ ls' _ _ (ht ls' (Ext.refl _ _))).1
  obtain ⟨_, _, _, _, _, _, μ₂, μ₃, _, _, -, -, -, -, -, -, k₈', -⟩ :=
    h₂ ρp fρ'p ps' k₃ (ResU.CompS.comm k₆) kT ktg
  exact tv_next_diverges k₈'

/-- **The naive rule's conclusion fails at `skip`**: `skip : U(U(D 1) ⊸ D 1)` (`skip_sem`), yet
`N = later (skip N)` is not of type `D 1`. -/
theorem naive_not_sem : ¬ SemC LifeCtx.empty [] (.val NV) (.delay .unit) := by
  intro h
  have := h LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  rw [show substAll [] (Expr.val NV) = .val NV from Adequacy.psub_nil 0 _] at this
  exact naive_not_delay _ this

end BoCa.Fig16.LogRel.Core

end
