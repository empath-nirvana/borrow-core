import Core.Chain.SI.ErwpN
import Core.EffRules

/-!
# A handler at the step index over Core's worlds: `erwp_handle`

`Core`'s `ewp_handle_or` (`Core/EffRules.lean`) proves `[handle]` by induction on the least fixed
point of the handled computation's `ewpTS`. At `erwp` there is no fixed point: the proof is by
induction on the index, as `ewp_handle` at `ewp`, and otherwise follows `ewp_handle_or`'s case
split at the end of the handled run: `[ret]`; an operation of the handler's name, whose clause
gets `κ`; an abortive one, whose clause runs and whose continuation is discarded; an operation or
raise of another name, which passes outward with the handler reinstalled in its continuation.
`κ` resumed at an answer at `k′` is the handled continuation at `k′`, which the induction
hypothesis covers since `k′ < k ≤ n`: the stop's continuation is owed only at lower indices, so
no `hdv` (guardedness) premise is needed.

All three qualifiers of a non-abortive operation are covered: unrestricted (`unr`, `κ` the plain
`kappa`, its share empty), must-resume (`lin`) and cancellable (`cancel`), where `κ` owns its cell
(`kappaCell`); a cancel of `κ` runs `ccatch (K†[raise …])` at the cancel row's table
(`erwp_ccatch`, by induction on the index). Two narrowings from `ewp_handle_or`: the cancel row's
table contains the entry's cancel obligation's table entry for entry (`OpTabN.Sub`, for `OpTab.Le`),
and there is no table beside the operation table (`Px`, a tick at a `Div` row).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

/-- `OpTabN.Down`'s cancel obligations, down any distance. -/
theorem OpTabN.Down.fin_le {T : OpTabN} (hT : T.Down) {n i : UInt32} {en : OpEntN}
    (hn : T n i = some en) {P : Nat → List SRec → Expr → WProp} (hP : en.fin = some P)
    {m k : Nat} (h : m ≤ k) {ls : List SRec} {e : Expr} {ρ : WRes} (hk : P k ls e ρ) :
    P m ls e ρ := by
  induction h with
  | refl => exact hk
  | step _ ih => exact ih (hT.fin _ _ _ _ hn hP _ _ _ _ hk)

/-! ### Garbage -/

/-- `wpG_garbage` at the index: a part of the final resource with no `own` cell joins `ρ⁺`. -/
theorem rwpG_garbage {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) Φ (fun k ls' t ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧ NoOwn ρ₂ ∧
      Q k ls' t ρ₁) n ls e ρ) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ h1 h2 h3 h4 hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', g1, g2, g3, g6, g7, g9, gA, gB,
    gT, gtg, gps, gls, ρ₁, ρ₂, hc, hno, hQ⟩ := h ρf fρ ps μ h1 h2 h3 h4 hl hfd j μ' e' hj hrun hfin
  obtain ⟨hf₁, -⟩ := ResU.Hash.split hc g1
  obtain ⟨F, hF, hF₂⟩ := (ResU.CompS.assoc ρf ρ₁ ρ₂ fρ').mp ⟨ρ', hc, g2⟩
  obtain ⟨Z, hZ, hFZ⟩ := (ResU.CompS.assoc F ρ₂ ρp fρ'p).mpr ⟨fρ', hF₂, g6⟩
  obtain ⟨Z', hZ', h₁Z⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρp π).mpr ⟨ρ', hc, g9⟩
  cases ResU.CompS.functional hZ' hZ
  have hv : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := g7; exact ⟨σ, hσ⟩
  exact ⟨ρ₁, Z, F, fρ'p, π, ps', ls', hf₁, hF,
    ⟨(ResU.CompS.comm hFZ).1, fρ'p, ResU.CompS.comm hFZ, hv⟩, hFZ, g7, h₁Z, gA,
    noOwn_compS hZ hno gB, gT, gtg, gps, gls, hQ⟩

/-! ### `κ` -/

/-- The postcondition of a cancel run caught at `ccatch`: `()`, owning nothing. -/
def unitPost : PostN := fun _ _ v => ⌜v = Val.unit⌝

theorem unitPost_down : unitPost.Down := fun _ _ _ _ h => h

/-- `KapRelT` at the index: resumed at every answer in `PB` at every `k′ < k`, and, with
weakening, cancelled at `opTableN Tk` at every `k′ < k` when its cancel branch has the table
`Tk`. -/
def KapRelN (Φ : LocFam) (Tb : TableN) (Q : PostN) (en : OpEntN) (Tc : Option OpTabN) (k : Nat)
    (ls : List SRec) (κ : Val) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ ls', en.wc ls ls' ρ → ∀ k', k' < k →
    (∀ w : Val, (en.PB k' ls' w ─⋆
      erwp (ℍ := ℍ) Φ Tb Q k' ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) ρ) ∧
    (en.q ≠ .lin → ∀ Tk, Tc = some Tk →
      erwp (ℍ := ℍ) Φ (opTableN Tk) unitPost k' ls' (.app κ.1 (.val (Val.inj₂ .unit))) ρ)

/-- Resuming `κ` at `w` runs `hnd H K[w]` (`ewp_kappa_resume`): four deterministic steps, for
free. -/
theorem erwp_kappa_resume {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTd : Tb.Down) {Q : PostN}
    (hQ : Q.Down) (H : Val) (K : Kont) (w : Val) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ Tb Q k ls (hndE H (K.plug (.val w))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q k ls (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val w)) ρ := by
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

/-- A stop of an operation is final at every memory. -/
theorem final_opPlug {K : Kont} {r : Bool} {p : Val} {n : UInt32}
    (hn : payloadName p = some n) (hK : OpFree r n K) (μ : Heap) :
    Final (ℍ := ℍ) μ (K.plug (opE r p)) :=
  fun _ _ h => opPlug_no_step hn hK h

/-! ### The capture cell at the index -/

/-- An allocation at an evaluation position, in front of an `erwp` (`ewp_alloc`): `rwp_alloc`
(6.141 at the index) and bind; the rest of the run at the index the step left. -/
theorem erwp_alloc {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) {Q : PostN}
    (Kc : Kont) (v : Val) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ v ─⋆
      erwp (ℍ := ℍ) Φ Tb Q (n - 1) ls (Kc.plug (.val (Val.loc ℓ)))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (Kc.plug (.app (.val (.prim .alloc)) (.val v))) ρ := by
  rw [erwp_eq]
  refine rwpG_bind hΦ Kc ?_
  have ha := rwp_alloc (ℍ := ℍ) (Φ := Φ) ls v
    (fun k ls' w => rwpG (ℍ := ℍ) Φ (erwpPost Tb Q (erwpC (ℍ := ℍ) Φ Tb Q n)) k ls'
      (Kc.plug w.1)) (n := n) (ρ := ρ)
    (fun ℓ σ₁ σ₂ hp hc => erwp_unfold_at hL (Nat.sub_le n 1) (h ℓ σ₁ σ₂ hp hc))
  rw [rwp_iff_rwpG] at ha
  exact rwpG_mono (fun _ _ _ _ ⟨w, hw, hq⟩ => hw ▸ hq) ha

/-- A release of an owned cell at an evaluation position, in front of an `erwp` (`ewp_free`). -/
theorem erwp_free {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) {Q : PostN}
    (Kc : Kont) (ℓ : Loc) (v : Val) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ v ⋆ erwp (ℍ := ℍ) Φ Tb Q (n - 1) ls (Kc.plug (.val v))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (Kc.plug (BoLo.freeE (.val (Val.loc ℓ)))) ρ := by
  rw [erwp_eq]
  refine rwpG_bind hΦ Kc ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  have hf := rwp_free (ℍ := ℍ) (Φ := Φ) ls ℓ v
    (fun k ls' w => rwpG (ℍ := ℍ) Φ (erwpPost Tb Q (erwpC (ℍ := ℍ) Φ Tb Q n)) k ls'
      (Kc.plug w.1)) (n := n) (ρ := ρ)
    ⟨ρ₁, ρ₂, hc, hp, erwp_unfold_at hL (Nat.sub_le n 1) hq⟩
  rw [rwp_iff_rwpG] at hf
  exact rwpG_mono (fun _ _ _ _ ⟨w, hw, hq⟩ => hw ▸ hq) hf

/-- **The capture cell's allocation at the index** (`ewp_kappaCell`). -/
theorem erwp_kappaCell {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local)
    (hTd : Tb.Down) {Q : PostN} (hQ : Q.Down) (hasCancel : Bool) (H : Val) (K : Kont)
    (Kc : Kont) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆
      erwp (ℍ := ℍ) Φ Tb Q (n - 1) ls (Kc.plug (kappaC hasCancel ℓ H K))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (Kc.plug (kappaCell hasCancel H K)) ρ := by
  have e : Kc.plug (kappaCell hasCancel H K) =
      (Kc.comp (.appR (.val (.lam (BoLo.kappaCBody hasCancel H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine erwp_alloc hΦ hL _ Val.unit (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [Kont.plug_comp]
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc ℓ)) rfl Kc) ?_
  rw [kappaCBody_subst]
  exact h ℓ σ₁ σ₂ hp hc

/-- **Resuming a `κ` that owns a cell, at the index** (`ewp_kappaC_resume`): the cell is freed,
one step, and `hnd H K[w]` runs at the index left. -/
theorem erwp_kappaC_resume {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local)
    (hTd : Tb.Down) {Q : PostN} (hQ : Q.Down) (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont)
    (w : Val) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ erwp (ℍ := ℍ) Φ Tb Q (k - 1) ls (hndE H (K.plug (.val w)))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q k ls
      (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) ρ := by
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_free hΦ hL (Kont.appL (Kont.seq .hole _) w) ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact hq

/-! ### Cancel runs at the index -/

/-- `errOk` at the index. -/
def errOkN (T : OpTabN) (k : Nat) (ls : List SRec) : Option Val → WProp
  | none => BoLo.emp
  | some E => ex fun (m : UInt32) => ex fun (j : UInt32) => ex fun (w : Val) =>
      ex fun (en : OpEntN) =>
        ⌜E = opPayload m j w ∧ T m j = some en ∧ en.abort = true⌝ ⋆
          fun ρ => en.PA k ls w ρ ∧ NoOwn ρ

/-- `cancelTab` at the index. -/
def cancelTabN (T : OpTabN) : TableN := fun k ls t Ψ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (err : Option Val) =>
      ⌜t = K.plug (raiseE (.val (cancelVal err))) ∧ K.Catches 0 = false⌝ ⋆
        (errOkN T k ls err ⋆ fun ρ => NoOwn ρ))
    (performStopN T k ls t Ψ)

/-- `cancelObl` at the index: the cancel run at `cancelTabN T`. -/
def cancelOblN (Φ : LocFam) (T : OpTabN) : Nat → List SRec → Expr → WProp :=
  fun k ls e => erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) k ls e

theorem cancelTabN_local (T : OpTabN) : (cancelTabN T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with h | ⟨K, n, i, v, en, h⟩
  · exact Or.inl h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, fun ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont ls' he).2⟩⟩⟩

/-- `T` is part of `T′`: every entry of `T` is `T′`'s at its key. -/
def OpTabN.Sub (T T' : OpTabN) : Prop := ∀ n i en, T n i = some en → T' n i = some en

/-- **A cancel run caught at `ccatch`, at the index** (`ewp_ccatch`), by induction on the
index. -/
theorem erwp_ccatch {Φ : LocFam} (hΦ : Φ.Down) {T Tout : OpTabN} (hT : T.Sub Tout)
    (hToutD : Tout.Down) :
    ∀ n ls e ρ, cancelOblN (ℍ := ℍ) Φ T n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) unitPost n ls (ccatchE e) ρ := by
  have hLin := cancelTabN_local T
  have hPD := erwpPost_down (opTableN_down hToutD) unitPost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  rw [erwp_eq]
  show rwpG (ℍ := ℍ) Φ _ n ls (ccatchK.plug e) ρ
  refine rwpG_bind hΦ ccatchK ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hLin le_rfl h)
  rcases ht with ⟨_, _, hv⟩ | ht
  · exact hv.elim
  rcases ht with ⟨K', err, hs'⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    cases err with
    | none =>
        refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.cancel μ K' hK') rfl .hole) ?_
        have hτa : τa = PMap.empty := he.1
        subst hτa
        rw [← eq_of_compS_empty_left hcab] at hnb
        refine rwpG_garbage (rwpG_here (fun μ => final_val μ Val.unit)
          ⟨PMap.empty, σ, compS_empty_left σ, hnb, Or.inl ⟨Val.unit, rfl, rfl, rfl⟩⟩)
    | some E =>
        refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.creraise μ E K' hK') rfl .hole) ?_
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨⟨rfl, hTe, ha⟩, hPA, hnA⟩ := pure_sep_iff.mp he
        have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (opPayload m j w))) :=
          final_opPlug (payloadName_opPayload m j w) (by simp [OpFree, Kont.Catches])
        exact rwpG_here hfin (Or.inr (Or.inr ⟨.hole, m, j, w, en,
          pure_sep_mk ⟨rfl, rfl, hT _ _ _ hTe, ha⟩ ⟨τa, τb, hcab, ⟨hPA, hnA⟩, hnb⟩⟩))
  · -- an operation of a finaliser passes `ccatch`
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hKo : (ccatchK.comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hK₁]; simp [Kont.HasHnd, Expr.val]
    have ht' : ccatchK.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (ccatchK.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨ccatchK.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT _ _ _ hT₁, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) _ _ _ hc
    · intro P hP
      show P k ls'' ((ccatchK.comp K₁).dead.plug _) ρk
      rw [dead_comp, dead_ccatchK]
      exact (hcont ls'' he).2 hq' P hP

/-- Cancelling `κ` runs `ccatch (K†[raise …])` (`ewp_kappa_cancel`): three deterministic steps,
for free. -/
theorem erwp_kappa_cancel {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTd : Tb.Down) {Q : PostN}
    (hQ : Q.Down) (H : Val) (K : Kont) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ Tb Q k ls (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q k ls (.app (kappa H K) (.val (Val.inj₂ .unit))) ρ := by
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-- **Cancelling a cancellable `κ`** frees its cell, then runs `ccatch (K†[raise …])`
(`ewp_kappaC_cancel`). -/
theorem erwp_kappaC_cancel {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local)
    (hTd : Tb.Down) {Q : PostN} (hQ : Q.Down) (ℓ : Loc) (H : Val) (K : Kont) {k : Nat}
    {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆ erwp (ℍ := ℍ) Φ Tb Q (k - 1) ls
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q k ls (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit))) ρ := by
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_free hΦ hL (Kont.seq .hole _) ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact hq

/-! ### The handler -/

/-- **A handler at the step index, its clauses asked at the stops up to `N`** (`[handle]`), by
induction on the index; `ewp_handle_or`'s cases at the end of the handled run. A run at `n ≤ N`
stops, and returns, only at indices up to `n`, so the return clause and the operation clauses are
asked only there. A clause that runs a computation under the same handler (a scheduler's spawn)
proves its case at `k` from this lemma below `k`. -/
theorem erwp_handle_le {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (Tin Tout : OpTabN) (hTinD : Tin.Down)
    (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Sub Tk ∧ Tk.Down)
    (hret : ∀ k, k ≤ N → ∀ ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ := by
  have hLin := opTableN_local Tin
  have hLout := opTableN_local Tout
  have hDout := opTableN_down hTout
  have hPD := erwpPost_down hDout hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h
  set H := hndVal n₀ qs hr hs with hH
  rw [erwp_eq]
  show rwpG (ℍ := ℍ) Φ _ n ls ((hndK H).plug e) ρ
  refine rwpG_bind hΦ (hndK H) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hLin le_rfl h)
  -- what the continuations of the handled run are owed, read through the induction hypothesis
  have hcontIH : ∀ k', k' < k → ∀ ls'' e'' τ,
      erwpC (ℍ := ℍ) Φ (opTableN Tin) Qin n k' ls'' e'' τ →
      erwpC (ℍ := ℍ) Φ (opTableN Tout) Qout n k' ls'' (hndE H e'') τ := by
    intro k' hk' ls'' e'' τ hc
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) (by omega) ls'' e'' τ hc
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · -- `[ret]`
    exact rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (erwp_unfold_at hLout hk (hret k (by omega) ls' v σ hv))
  · -- a stop at a non-abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[op]` at the handler's name: the clause, with `κ`
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop i en hT
      refine rwpG_det hΦ (hPD _)
        (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      -- the cancel run of the continuation, at the cancel row's table, at every `k″ ≤ k`
      have hcan : ∀ ls'', en.wc ls' ls'' ρk → en.q ≠ .lin → ∀ Tk, Tc i = some Tk → ∀ k'', k'' ≤ k →
          erwp (ℍ := ℍ) Φ (opTableN Tk) unitPost k'' ls''
            (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))) ρk := by
        intro ls'' he hq' Tk hTk k'' hk''
        obtain ⟨T₁, hf, hsub, hTkD⟩ := hTc i en hT ha hq' Tk hTk
        have hP := (hcont ls'' he).2 hq' _ hf
        exact erwp_ccatch hΦ hsub hTkD k'' ls'' _ ρk (hTinD.fin_le hT hf hk'' hP)
      have hDk : ∀ Tk : OpTabN, Tc i = some Tk → en.q ≠ .lin → (opTableN Tk).Down := by
        intro Tk hTk hq'
        obtain ⟨-, -, -, hTkD⟩ := hTc i en hT ha hq' Tk hTk
        exact opTableN_down hTkD
      rw [hq i en hT ha, kappaAt_tag]
      cases hqq : en.q with
      | unr =>
          refine erwp_unfold_at hLout hk (hna ha k (by omega) ls' v
            ⟨kappa H K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, hu, ?_⟩)
          intro ls'' he k' hk'
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · have h₁ := hcontIH k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
            simp only [erwpC, show k' < n by omega, if_true] at h₁
            exact erwp_kappa_resume hΦ hDout hQout H K₁ w h₁
          · exact erwp_kappa_cancel hΦ (hDk Tk hTk hq') unitPost_down H K₁
              (hcan ls'' he hq' Tk hTk k' (by omega))
      | lin | cancel =>
          -- the cell is allocated, one step; `κ` is `kappaC` at it, owning the cell and the share
          refine erwp_unfold_at hLout hk (erwp_kappaCell hΦ hLout hDout hQout _ H K₁
            (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ => ?_))
          obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
          have hA' : en.PA (k - 1) ls' v ρa := by
            cases k with
            | zero => exact hA
            | succ k₀ => exact hTinD.pa _ _ _ hT _ _ _ _ hA
          refine hna ha (k - 1) (by omega) ls' v ⟨_, isVal_kappaC _ ℓ H K₁⟩ σ₂
            ⟨ρa, y, hy₂, hA', fun hq' => absurd (hqq.symm.trans hq') (by simp), ?_⟩
          intro ls'' he k' hk'
          refine ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' Tk hTk => ?_⟩
          · obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
            have h₁ := hcontIH k' (by omega) _ _ _
              ((hcont ls'' (hTinD.wcl _ _ _ hT _ _ _ _ _ hy₁ he)).1 k' (by omega) w τ₁ z hB hz)
            simp only [erwpC, show k' < n by omega, if_true] at h₁
            exact erwp_kappaC_resume hΦ hLout hDout hQout _ ℓ H K₁ w
              ⟨σ₁, z, ResU.CompS.comm hzτ, hcell,
                erwp_le hΦ hLout hDout hQout (Nat.sub_le k' 1) h₁⟩
          · first
              | exact absurd hqq hq'
              | exact erwp_kappaC_cancel hΦ (opTableN_local Tk) (hDk Tk hTk hq') unitPost_down
                  ℓ H K₁ ⟨σ₁, ρk, ResU.CompS.comm hy₁, hcell,
                    hcan ls'' (hTinD.wcl _ _ _ hT _ _ _ _ _ hy₁ he) hq' Tk hTk (k' - 1) (by omega)⟩
    · -- an operation of another name passes outward
      have hKo : ((hndK H).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (performE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE false (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => ?_⟩⟩⟩))
      · rw [Kont.plug_comp]
        exact hcontIH k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
      · intro P hP
        show P k ls'' (((hndK H).comp K₁).dead.plug _) ρk
        rw [dead_comp, dead_hndK]
        exact (hcont ls'' he).2 hq' P hP
  · -- a stop at an abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[unwind]` at the handler's name: the clause; the continuation is discarded
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop i en hT
      refine rwpG_det hΦ (hPD _)
        (fun μ => step1Only_plug (Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      refine rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ =>
        ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩) (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hcan
          (erwp_unfold_at hLout hk (hab ha k (by omega) ls' v ρa hPA)) hnn))
    · -- an abortive operation of another name passes outward
      have hKo : ((hndK H).comp K₁).Catches m = false := by
        rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE true (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))

/-- **A handler at the step index** (`[handle]`): `erwp_handle_le` at `N = n`. -/
theorem erwp_handle {Φ : LocFam} (hΦ : Φ.Down) (Tin Tout : OpTabN) (hTinD : Tin.Down)
    (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (Tc : UInt32 → Option OpTabN)
    (hTc : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk, Tc i = some Tk →
      ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Sub Tk ∧ Tk.Down)
    (hret : ∀ k ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en (Tc i) k ls κ) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ :=
  fun n => erwp_handle_le hΦ n Tin Tout hTinD hTout n₀ hTin qs hr hs Qin Qout hQout hq Tc hTc
    (fun k _ => hret k)
    (fun i en hT => by
      obtain ⟨c, hc, h₁, h₂⟩ := hop i en hT
      exact ⟨c, hc, fun ha k _ => h₁ ha k, fun ha k _ => h₂ ha k⟩) n le_rfl

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-- The empty operation table: nothing may stop. -/
def OpTabN.empty : OpTabN := fun _ _ => none

/-- **Safety of a closed program at `erwp`**: at the empty table, at the empty world, at every
index, every configuration a run reaches is a value or steps. -/
theorem erwp_safe {Φ : LocFam} {Q : PostN} {e : Expr}
    (hall : ∀ n, erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n [] e (PMap.empty : WRes))
    {j : Nat} {μ' : BoCa.BoLo.Heap} {e' : Expr}
    (hrun : StepsN (ℍ := ℍ) j (fun _ => none) e μ' e') :
    IsVal e' ∨ ∃ μ'' e'', BoCa.BoLo.Step1 (ℍ := ℍ) μ' e' μ'' e'' := by
  refine rwpG_safe (Φ := Φ) (Q := erwpPost (opTableN OpTabN.empty) Q
    (erwpC (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q (j + 1))) ?_
    (fun n => ?_) hrun
  · intro k ls t ρ h
    rcases h with ⟨v, rfl, -⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
    · exact v.2
    · exact absurd (pure_sep_iff.mp h).1.2.2.1 (by simp [OpTabN.empty])
    · exact absurd (pure_sep_iff.mp h).1.2.2.1 (by simp [OpTabN.empty])
  · rcases Nat.le_total n (j + 1) with h | h
    · exact erwp_unfold_at (opTableN_local _) h (hall n)
    · have := erwp_unfold_at (opTableN_local _) le_rfl (hall n)
      refine rwpG_mono_le (fun k hk ls t ρ ht => ?_) this
      rcases ht with ht | ht
      · exact Or.inl ht
      · rcases ht with ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
        · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
        · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

end BoCa.Fig16.LogRel.Core.Chain.SI

end
