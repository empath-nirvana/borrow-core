import DivEffect.Iterate

/-!
# DivEffect — `div_fuel`  (§4.1, unknown 1, item 4)

`div_fuel n M` handles `Div` in `M`: it answers *next* to the first `n` ticks and *close* to
every tick after.  It is a deep handler of `d` with its counter passed as state: the handled
computation answers a function of the counter,

    div_fuel n M  ≜  (hnd_d H M) to g. g n
    h_ret v        =  λk. v
    h_tick ((), κ) =  λk. case k { 0 → (κ close) to g. g 0 | k' + 1 → (κ next) to g. g k' }

The counter is unary (`natV`).  `tick` is linear, so `κ` owns a cell (`kappaCell`), freed when it
is resumed.  Every path of the clause resumes `κ` once, in tail position up to the counter's
application.

**Totality** (`fuel_total`): `div_fuel n M` is in `ewpTS` at the rest of the row, for every
`M` of `cwp`, by induction on `n` and, inside, on the segment's least fixed point.  At a tick
with the counter at `k' + 1`, `κ next`'s continuation is in `cwp` (the induction on `n`); at `0`,
`κ close`'s continuation is in `Closing`, and `div_fuel 0` of a computation of `Closing` is
total by induction on `Closing`'s least fixed point (`fuel_closing`).  `Closing` is what makes
this hold: `Plain.lean` builds a computation of the §4.1 candidate on which `div_fuel 0` never
ends.

`div_fuel` is a constant with its own rule (choice 4's recommended path): the proof reads its
clause, so no coinductive `[handle]` rule is needed.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappaC kappaCell kappaAt clauseAt capTag freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The terms -/

/-- The counter `n`, unary: `0 = inl ()`, `k + 1 = inr k`. -/
def natV : ℕ → Val
  | 0 => .inj₁ .unit
  | n + 1 => .inj₂ (natV n)

/-- `λk. λg. g k`: `[·] to g. g k` is `(apK k) [·]`. -/
def apK : Val := .lam (.val (.lam (.app (.var 0) (.var 1))))

/-- `λκ. λk. case k { 0 → (κ close) to g. g 0 | k' + 1 → (κ next) to g. g k' }`. -/
def fuelBody : Val :=
  .lam (.val (.lam (.case (.var 0)
    (.app (.app (.val apK) (.val (natV 0))) (.app (.app (.var 2) (.val (Val.inj₁ .unit)))
      (.val closeV)))
    (.app (.app (.val apK) (.var 0)) (.app (.app (.var 2) (.val (Val.inj₁ .unit)))
      (.val nextV))))))

/-- The tick's clause: `λ((), κ). fuelBody κ`. -/
def fuelC : Val := .lam (.letpair (.var 0) (.app (.val fuelBody) (.var 0)))

/-- `h_ret = λv. λk. v`. -/
def fuelR : Val := .lam (.val (.lam (.var 1)))

/-- The handler value: the name `d`, the tick linear. -/
def fuelH (d : UInt32) : Val := hndVal d (qualsVal [.lin]) fuelR (Val.pair fuelC .unit)

/-- The frame `[·] to g. g k`. -/
def fuelK (k : Val) : Kont := .appR (.app (.val apK) (.val k)) .hole

/-- **`div_fuel n M`.** -/
def fuelE (d : UInt32) (n : ℕ) (e : Expr) : Expr := (fuelK (natV n)).plug (hndE (fuelH d) e)

theorem fuelK_plain (k : Val) :
    (∀ n, (fuelK k).HasHnd n = false) ∧ (∀ n, (fuelK k).Catches n = false) :=
  ⟨fun n => by simp [fuelK, Kont.HasHnd, apK], fun n => by simp [fuelK, Kont.Catches, apK]⟩

theorem natV_closed : ∀ n, closedAt 0 (natV n).1 = true
  | 0 => rfl
  | n + 1 => by simpa [natV, closedAt] using natV_closed n

/-! ### The steps -/

/-- `(apK k) g ↦* g k`. -/
theorem apK_steps (k g : Val) :
    PureSteps (.app (.app (.val apK) (.val k)) (.val g)) (.app (.val g) (.val k)) := by
  refine (PureSteps.beta_in (.appL .hole g) _ k).trans ?_
  simp only [apK, Kont.plug]
  refine (PureSteps.beta _ g).trans ?_
  simp [subst_shift_succ]
  exact .refl

/-- `[ret]`: `(hnd H v) to g. g k` answers `v`. -/
theorem fuel_ret (d : UInt32) (k v : Val) :
    PureSteps ((fuelK k).plug (hndE (fuelH d) (.val v))) (.val v) := by
  refine (PureSteps.plug (fuelK k) (PureSteps.head (fun μ => Head.hret μ d _ _ _ v) rfl)).trans ?_
  refine (PureSteps.beta_in (fuelK k) _ v).trans ?_
  simp only [fuelK, Kont.plug, fuelR]
  refine (apK_steps k ⟨_, .lam⟩).trans ?_
  refine (PureSteps.beta _ k).trans ?_
  simp [subst_shift_succ]
  exact .refl

/-- `(fuelC ((), κ)) to g. g k`, up to the case on the counter. -/
theorem fuel_clause (k κ : Val) :
    PureSteps ((fuelK k).plug (.app (.val fuelC) (.val (Val.pair .unit κ))))
      (.case (.val k)
        (.app (.app (.val apK) (.val (natV 0))) (.app (.app (κ.1.shift 1 0) (.val (Val.inj₁ .unit)))
          (.val closeV)))
        (.app (.app (.val apK) (.var 0)) (.app (.app (κ.1.shift 1 0) (.val (Val.inj₁ .unit)))
          (.val nextV)))) := by
  refine (PureSteps.beta_in (fuelK k) _ _).trans ?_
  refine (PureSteps.plug (fuelK k) (PureSteps.head (fun μ => Head.letpair μ .unit κ _) rfl)).trans ?_
  have hb : closedAt 0 fuelBody.1 = true := rfl
  have e : Expr.subst 0 Val.unit (Expr.subst 0 (Val.shift 1 0 κ)
      (Expr.subst (0 + 2) (Val.shift 2 0 (Val.unit.pair κ)) ((Expr.val fuelBody).app (Expr.var 0))))
      = .app (.val fuelBody) (.val κ) := by
    simp [closed_subst hb, subst_shift_succ]
  rw [e]
  refine (PureSteps.plug (fuelK k) (PureSteps.beta _ κ)).trans ?_
  have hn := natV_closed 0
  simp only [fuelK, Kont.plug, fuelBody]
  refine (apK_steps k ⟨_, .lam⟩).trans ?_
  refine (PureSteps.beta _ k).trans ?_
  simp [subst_shift_succ, closed_subst hn, apK, natV, nextV, closeV]
  exact .refl

theorem fuel_clause_zero (κ : Val) :
    PureSteps ((fuelK (natV 0)).plug (.app (.val fuelC) (.val (Val.pair .unit κ))))
      ((fuelK (natV 0)).plug (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val closeV))) := by
  refine (fuel_clause _ κ).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  simp [subst_shift_succ, fuelK, Kont.plug, apK, natV, closeV]
  exact .refl

theorem fuel_clause_succ (m : ℕ) (κ : Val) :
    PureSteps ((fuelK (natV (m + 1))).plug (.app (.val fuelC) (.val (Val.pair .unit κ))))
      ((fuelK (natV m)).plug (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val nextV))) := by
  refine (fuel_clause _ κ).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ (natV m) _ _) rfl).trans ?_
  simp [subst_shift_succ, fuelK, Kont.plug, apK, natV, nextV]
  exact .refl

/-- **Resuming a `κ` that owns a cell, in a context `K₀`**: `ewp_kappaC_resume`'s steps
under `K₀`. -/
theorem ewp_kappaC_resume_in {Tb : Table} (hTb : Tb.Mono) (K₀ : Kont) (aff : Bool) (ℓ : Loc)
    (H : Val) (K : Kont) (w : Val) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ ewpTS ls (K₀.plug (hndE H (K.plug (.val w)))) Tb Q) ρ) :
    ewpTS ls (K₀.plug (.app (.app (kappaC aff ℓ H K) (.val (Val.inj₁ .unit))) (.val w))) Tb Q ρ := by
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

/-! ### A tick under `div_fuel` -/

theorem clauseAt_one (c : Val) : clauseAt (Val.pair c Val.unit).1 0 = some c := by
  simp [clauseAt, Val.pair]; exact c.2

theorem kappaAt_lin (d : UInt32) (hr c : Val) (K : Kont) :
    kappaAt (capTag (qualsVal [.lin]).1 (UInt32.toNat 0))
      (hndVal d (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K =
      kappaCell false (hndVal d (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K := by
  simp only [kappaAt, capTag, qualsVal, Qual.tag, Val.pair, Val.i32]; rfl

/-- A linear `κ` at its cell, as a value. -/
def kapV (ℓ : Loc) (H : Val) (K : Kont) : Val := ⟨kappaC false ℓ H K, isVal_kappaC false ℓ H K⟩

/-- **A tick under a handler of `d` with one linear clause `c`**, in a context `K₀`: the
clause, with `κ` given its cell. -/
theorem hnd_tick {Tb : Table} (hTb : Tb.Mono) (d : UInt32) (hr c : Val) (K₀ K₁ : Kont)
    (hK₁ : K₁.HasHnd d = false) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ ewpTS ls (K₀.plug (.app (.val c)
      (.val (Val.pair .unit (kapV ℓ (hndVal d (qualsVal [.lin]) hr (c.pair .unit)) K₁))))) Tb Q) ρ) :
    ewpTS ls (K₀.plug (hndE (hndVal d (qualsVal [.lin]) hr (c.pair .unit)) (K₁.plug (tickE d))))
      Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.hop μ d 0 (qualsVal [.lin]) hr
    (Val.pair c .unit) c .unit K₁ (clauseAt_one c) hK₁) rfl).plug K₀) ls Q ρ ?_
  rw [kappaAt_lin]
  have e : K₀.plug (.app (.val c) (.pair (.val .unit)
      (kappaCell false (hndVal d (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁))) =
      (K₀.comp (.appR (.val c) (.pairR .unit .hole))).plug
        (kappaCell false (hndVal d (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine ewp_kappaCell hTb false _ K₁ _ (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [Kont.plug_comp]
  exact h ℓ σ₁ σ₂ hp hc

/-- A tick under `div_fuel k`: the clause, with `κ` given its cell, up to the clause's body. -/
theorem fuel_tick {Tb : Table} (hTb : Tb.Mono) (d : UInt32) (k : Val) (K₁ : Kont)
    (hK₁ : K₁.HasHnd d = false) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ ewpTS ls ((fuelK k).plug (.app (.val fuelC)
      (.val (Val.pair .unit (kapV ℓ (fuelH d) K₁))))) Tb Q) ρ) :
    ewpTS ls ((fuelK k).plug (hndE (fuelH d) (K₁.plug (tickE d)))) Tb Q ρ :=
  hnd_tick hTb d fuelR fuelC _ K₁ hK₁ h

/-- A tick under `div_fuel 0` resumes `κ` with *close*. -/
theorem fuel_tick_zero (d : UInt32) {T : OpTab} (K₁ : Kont) (hK₁ : K₁.HasHnd d = false)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (fuelE d 0 (K₁.plug (.val closeV))) (opTable T) Q ρ) :
    ewpTS ls (fuelE d 0 (K₁.plug (tickE d))) (opTable T) Q ρ := by
  refine fuel_tick (opTable_mono T) d _ K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine ewp_pureSteps (opTable_mono T) (fuel_clause_zero _) _ _ σ₂ ?_
  exact ewp_kappaC_resume_in (opTable_mono T) _ false ℓ (fuelH d) K₁ closeV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

/-- A tick under `div_fuel (m + 1)` resumes `κ` with *next*, under `div_fuel m`. -/
theorem fuel_tick_succ (d : UInt32) (m : ℕ) {T : OpTab} (K₁ : Kont) (hK₁ : K₁.HasHnd d = false)
    {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (fuelE d m (K₁.plug (.val nextV))) (opTable T) Q ρ) :
    ewpTS ls (fuelE d (m + 1) (K₁.plug (tickE d))) (opTable T) Q ρ := by
  refine fuel_tick (opTable_mono T) d _ K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine ewp_pureSteps (opTable_mono T) (fuel_clause_succ m _) _ _ σ₂ ?_
  exact ewp_kappaC_resume_in (opTable_mono T) _ false ℓ (fuelH d) K₁ nextV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

/-! ### Other operations pass `div_fuel` -/

/-- `div_fuel`'s frames: the counter's application and the handler. -/
def fuelKF (d : UInt32) (n : ℕ) : Kont := (fuelK (natV n)).comp (hndK (fuelH d))

theorem fuelE_eq (d : UInt32) (n : ℕ) (e : Expr) : fuelE d n e = (fuelKF d n).plug e := by
  rw [fuelKF, Kont.plug_comp]; rfl

theorem fuelK_dead (k : Val) : (fuelK k).dead = fuelK k := by
  simp [fuelK, Kont.dead, Kont.DeadFrame, apK]

theorem fuelKF_dead (d : UInt32) (n : ℕ) (K : Kont) :
    ((fuelKF d n).comp K).dead = (fuelK (natV n)).comp K.dead := by
  rw [fuelKF, dead_comp, dead_comp, fuelK_dead, fuelH, dead_hndK]; rfl

theorem fuelKF_hasHnd (d : UInt32) (n : ℕ) {m : UInt32} (hm : m ≠ d) (K : Kont)
    (hK : K.HasHnd m = false) : ((fuelKF d n).comp K).HasHnd m = false := by
  rw [fuelKF, hasHnd_comp, hasHnd_comp, (fuelK_plain _).1, fuelH, hndK_hasHnd, hK]
  simpa using Ne.symm hm

theorem fuelKF_catches (d : UInt32) (n : ℕ) {m : UInt32} (hm : m ≠ d) (K : Kont)
    (hK : K.Catches m = false) : ((fuelKF d n).comp K).Catches m = false := by
  rw [fuelKF, catches_comp, catches_comp, (fuelK_plain _).2, fuelH, hndK_catches, hK]
  simpa using Ne.symm hm

/-- A cancel run depends only on the dead region. -/
theorem cancelOK_of_dead {en : OpEnt} {ls : List SRec} {K K' : Kont} (h : K.dead = K'.dead)
    {ρ : WRes} (hc : cancelOK en ls K ρ) : cancelOK en ls K' ρ := by
  intro P hP; rw [← h]; exact hc P hP

theorem kont_comp_hole : ∀ K : Kont, K.comp .hole = K
  | .hole => rfl
  | .pairL K e => by simp [Kont.comp, kont_comp_hole K]
  | .pairR v K => by simp [Kont.comp, kont_comp_hole K]
  | .letpair K e => by simp [Kont.comp, kont_comp_hole K]
  | .case K e₁ e₂ => by simp [Kont.comp, kont_comp_hole K]
  | .appR f K => by simp [Kont.comp, kont_comp_hole K]
  | .appL K v => by simp [Kont.comp, kont_comp_hole K]
  | .seq K e => by simp [Kont.comp, kont_comp_hole K]
  | .inj₁ K => by simp [Kont.comp, kont_comp_hole K]
  | .inj₂ K => by simp [Kont.comp, kont_comp_hole K]

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
    fun K => by rw [dead_comp, dead_comp, hD₀, dead_hndK, kont_comp_hole]
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

/-- **An operation of another name passes `div_fuel`.** -/
theorem fuel_fwd {d : UInt32} {T : OpTab} (hTd : ∀ i, T d i = none) (hPC : T.PlainCancel)
    (n : ℕ) {Φ Ψ : List SRec → Expr → WProp}
    (hΦ : ∀ ls e ρ, Φ ls e ρ → Ψ ls (fuelE d n e) ρ) {ls : List SRec} {t : Expr} {ρ : WRes}
    (h : opTable T ls t Φ ρ) : opTable T ls (fuelE d n t) Ψ ρ := by
  rw [fuelE_eq]
  exact hnd_fwd hTd hPC _ (fuelK_plain _).1 (fuelK_plain _).2 (fuelK_dead _) _ _ _
    (fun ls e ρ h => by rw [show (fuelK (natV n)).comp (hndK (hndVal d (qualsVal [.lin]) fuelR
      (Val.pair fuelC .unit))) = fuelKF d n from rfl, ← fuelE_eq]; exact hΦ ls e ρ h) h

/-! ### Totality -/

/-- **`div_fuel 0` of a computation of `Closing` is total**: every tick is answered *close*, and
`Closing`'s least fixed point bounds them. -/
theorem fuel_closing {δ : LSub} {d : UInt32} {T : OpTab} (hTd : ∀ i, T d i = none)
    (hPC : T.PlainCancel) {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Closing δ d T Q ls e ρ) : ewpTS ls (fuelE d 0 e) (opTable T) Q ρ := by
  refine ewp_ind (fun ls e ρ => ewpTS ls (fuelE d 0 e) (opTable T) Q ρ) ?_ h
  intro ls e ρ hs
  rw [fuelE_eq]
  refine ewp_fold (opTable_mono T) (wpG_bind _ e ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
  rw [← fuelE_eq]
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact ewp_unfold (opTable_mono T) (ewp_pureSteps (opTable_mono T) (fuel_ret d _ v) _ _ σ
      (ewp_val (opTable_mono T) hv))
  rcases ht with hp | hr
  · obtain ⟨K₁, m, i, v, en, hp'⟩ := hp
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp'
    rcases ext_some hT with ⟨rfl, rfl, rfl⟩ | hT'
    · -- a tick, answered *close*
      obtain ⟨rfl, rfl⟩ := hA
      rw [eq_of_compS_empty_left hcak]
      refine ewp_unfold (opTable_mono T) (fuel_tick_zero m K₁ hK₁ ?_)
      have := (hcont ls' (Ext.refl ls' ρk)).1 closeV PMap.empty ρk (vC_close.mpr ⟨rfl, rfl⟩)
        (ResU.comp_empty_right ρk)
      exact this
    · exact wpG_here _ _ _ σ (Or.inr (fuel_fwd hTd hPC 0 (fun _ _ _ h => h)
        (Or.inl ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT', ha⟩
          ⟨ρa, ρk, hcak, hA, hu, hcont⟩⟩)))
  · obtain ⟨K₁, m, i, v, en, hp'⟩ := hr
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp'
    rcases ext_some hT with ⟨rfl, rfl, rfl⟩ | hT'
    · exact absurd ha (by show ¬ (false = true); simp)
    · exact wpG_here _ _ _ σ (Or.inr (fuel_fwd hTd hPC 0 (fun _ _ _ h => h)
        (Or.inr ⟨K₁, m, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT', ha⟩ hrest⟩)))

/-- **`div_fuel n M` is total** (§4.1 unknown 1 item 4): in `ewpTS` at the rest of the row,
for every computation of `cwp`, by induction on `n` and, inside, on the segment. -/
theorem fuel_total {δ : LSub} {d : UInt32} {T : OpTab} (hTd : ∀ i, T d i = none)
    (hPC : T.PlainCancel) {Q : List SRec → Val → WProp} :
    ∀ (n : ℕ) {ls : List SRec} {e : Expr} {ρ : WRes}, cwp δ d T Q ls e ρ →
      ewpTS ls (fuelE d n e) (opTable T) Q ρ := by
  intro n
  induction n with
  | zero => exact fun h => fuel_closing hTd hPC (closing_of_cwp (hTd 0) h)
  | succ m ih =>
    intro ls e ρ h
    refine ewp_ind (fun ls e ρ => ewpTS ls (fuelE d (m + 1) e) (opTable T) Q ρ) ?_
      (cwp_out ls e ρ h)
    intro ls e ρ hs
    rw [fuelE_eq]
    refine ewp_fold (opTable_mono T) (wpG_bind _ e ls _ ρ (wpG_mono (fun ls' t σ ht => ?_) hs))
    rw [← fuelE_eq]
    rcases ht with ⟨v, rfl, hv⟩ | ht | ht
    · exact ewp_unfold (opTable_mono T) (ewp_pureSteps (opTable_mono T) (fuel_ret d _ v) _ _ σ
        (ewp_val (opTable_mono T) hv))
    · exact wpG_here _ _ _ σ (Or.inr (fuel_fwd hTd hPC (m + 1) (fun _ _ _ h => h) ht))
    · -- a tick, answered *next*
      obtain ⟨K₁, n, i, v, en, hp'⟩ := ht
      obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp'
      obtain ⟨rfl, rfl, rfl⟩ := tickT_some hT
      obtain ⟨rfl, rfl⟩ := hA
      rw [eq_of_compS_empty_left hcak]
      refine ewp_unfold (opTable_mono T) (fuel_tick_succ n m K₁ hK₁ (ih ?_))
      exact ((hcont ls' (Ext.refl ls' ρk)).1 nextV PMap.empty ρk
        (Or.inl ⟨.unit, ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩⟩)
        (ResU.comp_empty_right ρk)).1

end BoCa.Fig16.LogRel.Core.DivEffect

end
