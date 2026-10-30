import Core.DivIterate

/-!
# Core — `Div`: steps of a handler with one linear clause  `[spec §14, §19]`

The handlers of `Div` the kernel has (`div_fuel`, `reify`) have one linear clause.  At a tick the
`[op]` step gives `κ` its cell (`hnd_tick`); resuming `κ` frees it and runs the continuation under
the handler (`ewp_kappaC_resume_in`).  An operation of another name passes a handler of `Div`
under a plain frame (`hnd_fwd`).
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

/-- **Resuming a `κ` that owns a cell, in a context `K₀`**: `ewp_kappaC_resume`'s steps
under `K₀`. -/
theorem ewp_kappaC_resume_in {Tb : Table} (hTb : Tb.Mono) (K₀ : Kont) (hasCancel : Bool) (ℓ : Loc)
    (H : Val) (K : Kont) (w : Val) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ ewpTS ls (K₀.plug (hndE H (K.plug (.val w)))) Tb Q) ρ) :
    ewpTS ls (K₀.plug (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w))) Tb Q ρ := by
  let K₁ : Kont := K₀.comp (.appL .hole w)
  have e₀ : ∀ x, K₀.plug (.app x (.val w)) = K₁.plug x := fun x => by
    simp only [K₁, Kont.plug_comp]; rfl
  rw [e₀]
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug K₁) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.case₁ μ Val.unit _ _) rfl).plug K₁) ls Q ρ ?_
  refine ewp_step hTb (fun μ => (Step1N.head (Head.seq μ _) rfl).plug K₁) ls Q ρ ?_
  have e₁ : ∀ x, K₁.plug (.seq (freeE (.val (Val.loc ℓ))) x) =
      (K₁.comp (.seq .hole x)).plug (freeE (.val (Val.loc ℓ))) := fun x => by
    rw [Kont.plug_comp, Kont.plug_comp, Kont.plug_comp]; rfl
  show ewpTS ls (K₁.plug (.seq (freeE (.val (Val.loc ℓ))) _)) Tb Q ρ
  rw [e₁]
  refine ewp_free hTb _ ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  rw [Kont.plug_comp]
  refine ewp_step hTb (fun μ => (Step1N.head (Head.seq μ _) rfl).plug K₁) ls Q ρ₂ ?_
  rw [← e₀]
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ w) rfl).plug K₀) ls Q ρ₂ ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact hq

theorem clauseAt_one (c : Val) : clauseAt (Val.pair c Val.unit).1 0 = some c := by
  simp [clauseAt, Val.pair]; exact c.2

theorem kappaAt_lin (d : UInt32) (hr c : Val) (K : Kont) :
    kappaAt (capTag (qualsVal [.lin]).1 (UInt32.toNat 0))
      (hndVal d (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K =
      kappaCell false (hndVal d (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K := by
  simp only [kappaAt, qualsVal, Qual.tag, Val.pair, Val.i32]; rfl

/-- A linear `κ` at its cell, as a value. -/
def kapV (ℓ : Loc) (H : Val) (K : Kont) : Val := ⟨kappaC false ℓ H K, isVal_kappaC false ℓ H K⟩

/-- **A tick under a handler of `Div` with one linear clause `c`**, in a context `K₀`: the
clause, with `κ` given its cell. -/
theorem hnd_tick {Tb : Table} (hTb : Tb.Mono) (hr c : Val) (K₀ K₁ : Kont)
    (hK₁ : K₁.HasHnd divEff = false) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ ewpTS ls (K₀.plug (.app (.val c)
      (.val (Val.pair .unit (kapV ℓ (hndVal divEff (qualsVal [.lin]) hr (c.pair .unit)) K₁)))))
        Tb Q) ρ) :
    ewpTS ls (K₀.plug (hndE (hndVal divEff (qualsVal [.lin]) hr (c.pair .unit)) (K₁.plug tickE)))
      Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.hop μ divEff 0 (qualsVal [.lin]) hr
    (Val.pair c .unit) c .unit K₁ (clauseAt_one c) hK₁) rfl).plug K₀) ls Q ρ ?_
  rw [kappaAt_lin]
  have e : K₀.plug (.app (.val c) (.pair (.val .unit)
      (kappaCell false (hndVal divEff (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁))) =
      (K₀.comp (.appR (.val c) (.pairR .unit .hole))).plug
        (kappaCell false (hndVal divEff (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine ewp_kappaCell hTb false _ K₁ _ (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [Kont.plug_comp]
  exact h ℓ σ₁ σ₂ hp hc

/-- A cancel run depends only on the dead region. -/
theorem cancelOK_of_dead {en : OpEnt} {ls : List SRec} {K K' : Kont} (h : K.dead = K'.dead)
    {ρ : WRes} (hc : cancelOK en ls K ρ) : cancelOK en ls K' ρ := by
  intro P hP; rw [← h]; exact hc P hP

/-- **An operation of another name passes a handler of `d`** under a plain frame `K₀` that a
cancel keeps: its stop, with the frames, is a stop of the rest of the row; its continuation keeps
them, and its cancel run is the plain frame's around the inner one (the handler is dead in it). -/
theorem hnd_fwd {d : UInt32} {T : OpTab} (hTd : ∀ i, T d i = none) (hPC : T.PlainCancel)
    (K₀ : Kont) (hH₀ : ∀ n, K₀.HasHnd n = false) (hC₀ : ∀ n, K₀.Catches n = false)
    (hD₀ : K₀.dead = K₀) (qs hr hs : Val) {Φ Ψ : List SRec → Expr → WProp}
    (hΦ : ∀ ls e ρ, Φ ls e ρ → Ψ ls ((K₀.comp (hndK (hndVal d qs hr hs))).plug e) ρ)
    {ls : List SRec} {t : Expr} {ρ : WRes}
    (h : opTable T ls t Φ ρ) : opTable T ls ((K₀.comp (hndK (hndVal d qs hr hs))).plug t) Ψ ρ := by
  have hne : ∀ m i en, T m i = some en → m ≠ d := by
    rintro m i en hT rfl; rw [hTd] at hT; cases hT
  have hdead : ∀ K, ((K₀.comp (hndK (hndVal d qs hr hs))).comp K).dead = K₀.comp K.dead :=
    fun K => by rw [dead_comp, dead_comp, hD₀, dead_hndK, Kont.comp_hole]
  rcases h with ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    refine Or.inl ⟨(K₀.comp (hndK (hndVal d qs hr hs))).comp K₁, m, i, v, en, pure_sep_mk
      ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
      ⟨ρa, ρk, hcak, hA, And.intro hu (fun ls'' he => And.intro (fun w τ₁ τ₂ hB hc => ?_)
        (fun hq => ?_))⟩⟩
    · rw [hasHnd_comp, hasHnd_comp, hH₀, hndK_hasHnd, hK₁]
      simpa using Ne.symm (hne m i en hT)
    · rw [Kont.plug_comp]
      exact hΦ _ _ _ ((hcont ls'' he).1 w τ₁ τ₂ hB hc)
    · refine cancelOK_of_dead (K := K₀.comp K₁) ?_
        (hPC m i en hT ha hq _ hH₀ (hC₀ 0) ls'' K₁ ρk ((hcont ls'' he).2 hq))
      rw [hdead, dead_comp, hD₀]
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp
    refine Or.inr ⟨(K₀.comp (hndK (hndVal d qs hr hs))).comp K₁, m, i, v, en, pure_sep_mk
      ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩ hrest⟩
    rw [catches_comp, catches_comp, hC₀, hndK_catches, hK₁]
    simpa using Ne.symm (hne m i en hT)

/-! ### The rows of `Div`'s handlers -/

/-- The row `tick, Σ`, `Σ` without `Div`'s name: it holds `Div`. -/
theorem Row.divB_tick (S : Row) : Row.divB (tickSig :: S) = true := by
  simp [Row.divB, CTy.effOf, CTy.divAt, tickSig, tickB, VTy.isUnitB, VTy.isNextB]

theorem Row.tab_tick_key (S : Row) (δ : LSub) :
    Row.tab (tickSig :: S) δ divEff 0 = some (tickSig.ent δ) :=
  Row.tab_find (by simp [Row.find, List.find?, tickSig])

theorem Row.tab_tick_ne (S : Row) (δ : LSub) {n i : UInt32} (h : ¬ (n = divEff ∧ i = 0)) :
    Row.tab (tickSig :: S) δ n i = Row.tab S δ n i := by
  have : decide (n = tickSig.n ∧ i = tickSig.i) = false := by
    simp only [tickSig]; exact decide_eq_false h
  simp [Row.tab, Row.find, List.find?, this]

/-- A row without `Div`'s name has nothing at it. -/
theorem Row.tab_without {S : Row} (h : ∀ o ∈ S, o.n ≠ divEff) (δ : LSub) (i : UInt32) :
    Row.tab S δ divEff i = none := by
  cases hf : Row.find S divEff i with
  | none => simp [Row.tab, hf]
  | some o =>
      obtain ⟨hm, hn, -⟩ := Row.find_mem hf
      exact absurd hn (h o hm)

theorem tickSig_isTick (δ : LSub) : (tickSig.ent δ).IsTick :=
  OpSig.isTick_ent δ (by simp [tickSig, tickB, VTy.isUnitB, VTy.isNextB])

end BoCa.Fig16.LogRel.Core

end
