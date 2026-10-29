import SuspSpike.Frame
import Core.DivHandle

/-!
# SuspSpike — class 1's handler: a tail clause resumes in scope

A handler of a call-like name gets, at each of its operations, the argument and a `κ` owed only
at lists with the stop's members (`KapRelC`). `ewp_handleC` is Core's `ewp_handle_or` at graded
tables (the same cases: `[ret]`, `[op]` at the handler's name, an operation of another name
passing outward, an abortive one of another name). Its clause obligation is met by a **tail
clause** `λ(x, κ). (λw. κ.1 w) (g x)` whose `g` runs at a class-1 row (`tail_hop`): `g x`
answers in the scope it was called in (`ewp_frame_call`, the resume frame carried through `g`'s
call-like stops), and `κ` is resumed there. This is the effect-erasure law's case: a call-like
operation is a call.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload
  cancelVal hndE hndVal kappa clauseAt capTag kappaAt kappaC kappaCell)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `κ`'s relation at a call-like operation: resumed, at every list with the stop's members and
every answer, into `ewpTS` at `Tb`. No cancel: the operation is linear. -/
def KapRelC (Tb : Table) (Qout : List SRec → Val → WProp) (en : OpEnt) (ls : List SRec)
    (κ : Val) : WProp := fun ρ =>
  ∀ ls', SameMem ls ls' → ∀ w : Val,
    (en.PB ls' w ─⋆ ewpTS ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w)) Tb Qout) ρ

theorem KapRelC.same {Tb : Table} {Qout : List SRec → Val → WProp} {en : OpEnt}
    {ls ls' : List SRec} {κ : Val} (hs : SameMem ls ls') {ρ : WRes}
    (h : KapRelC Tb Qout en ls κ ρ) : KapRelC Tb Qout en ls' κ ρ :=
  fun ls'' hs' w => h ls'' (hs.trans hs') w

/-- A stop at an operation the grade marks, at any table that has it. -/
theorem stopC_mk' {T : OpTab} {C : Grade} {ls : List SRec}
    {Φ : List SRec → Expr → WProp} {K : Kont} {n i : UInt32} {v : Val} {en : OpEnt}
    {ρa ρk ρ : WRes} (hg : C n i = true) (hK : K.HasHnd n = false) (hT : T n i = some en)
    (ha : en.abort = false) (hc : ResU.CompS ρa ρk ρ) (hA : en.PA ls v ρa)
    (hk : contShareC en ls K Φ ρk) :
    opTableC T C ls (K.plug (performE (.val (opPayload n i v)))) Φ ρ :=
  Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩
    ⟨ρa, ρk, hc, hA, by rw [shareAt_true hg]; exact hk⟩⟩

/-- **A plain frame around a computation of a class-1 row.** `K` holds no handler; the frame `Fr`
(read at lists with the same members) is carried through every stop into the continuation's share,
and the stop is one of a larger graded table `T′` at which the operation is call-like too. -/
theorem ewp_frame_call {TN : OpTab} {CN : Grade} (hC : CallRow TN CN) {T' : OpTab} {C' : Grade}
    (hle : TN.Le T') (hg' : ∀ n i en, TN n i = some en → C' n i = true)
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', SameMem ls ls' → Entails (Fr ls) (Fr ls'))
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls) (ewpTS ls (K.plug (.val v)) (opTableC T' C') Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTableC TN CN) Q₁ ρ →
      ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        ewpTS ls (K.plug e) (opTableC T' C') Q ρ' := by
  have hM := opTableC_mono T' C'
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ∀ {ρ₂ ρ' : WRes}, Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
    ewpTS ls (K.plug e) (opTableC T' C') Q ρ') ?_ h
  intro ls e ρ hs ρ₂ ρ' hF hc
  refine ewp_fold hM (wpG_bind K e ls _ ρ' ?_)
  have h₁ := wpG_frame (e := e) Fr (fun ls' hs' => hFs ls ls' hs') ρ' ⟨ρ, ρ₂, hc, hs, hF⟩
  refine wpG_mono (fun ls' t σ ht => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, hp, hF'⟩ := ht
  rcases hp with ⟨v, rfl, hv⟩ | hp
  · exact ewp_unfold hM (hk ls' v σ ⟨σ₁, σ₂, hcσ, hv, hF'⟩)
  · obtain ⟨K₁, n, i, v, en, ρa, ρk, rfl, hK₁, hT, ha, hcak, hA, hcont⟩ := stopC_dest hC hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    obtain ⟨en', hT', hl⟩ := hle _ _ _ hT
    rw [← Kont.plug_comp]
    refine wpG_here _ _ _ σ (Or.inr (stopC_mk' (hg' n i en hT) ?_ hT' (hl.2.1 ▸ ha) hcσ'
      (by rw [← hl.2.2.1]; exact hA) fun ls'' hs'' w τ₁ τ₂ hB hcτ => ?_))
    · rw [hasHnd_comp, hH, hK₁]; rfl
    · obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      rw [Kont.plug_comp]
      rw [← hl.2.2.2.1] at hB
      exact hcont ls'' hs'' w τ₁ z hB hz (hFs ls' ls'' hs'' σ₂ hF') hcz

/-- **A handler at graded tables.** Core's `ewp_handle_or`, every case as printed there, at tables
graded by `Cin` inside and `Cout` outside, the handler's name call-like (`hn`): its clause receives
`κ` at `KapRelC`. -/
theorem ewp_handleC (Tin Tout : OpTab) (Cin Cout : Grade) (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i) (hCin : ∀ m i, m ≠ n → Cin m i = Cout m i)
    (hn : ∀ i en, Tin n i = some en → Cin n i = true ∧ en.q = .lin ∧ en.abort = false)
    (qs hr hs : Val) (Qin Qout : List SRec → Val → WProp)
    (hq : ∀ i en, Tin n i = some en → capTag qs.1 i.toNat = en.q.tag)
    (hret : ∀ ls v ρ, Qin ls v ρ →
      ewpTS ls (.app (.val hr) (.val v)) (opTableC Tout Cout) Qout ρ)
    (hop : ∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      ∀ ls v (κ : Val) ρ, (en.PA ls v ⋆ KapRelC (opTableC Tout Cout) Qout en ls κ) ρ →
        ewpTS ls (.app (.val c) (.pair (.val v) κ.1)) (opTableC Tout Cout) Qout ρ) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTableC Tin Cin) Qin ρ →
      ewpTS ls (hndE (hndVal n qs hr hs) e) (opTableC Tout Cout) Qout ρ := by
  have hM := opTableC_mono Tout Cout
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ewpTS ls (hndE (hndVal n qs hr hs) e)
    (opTableC Tout Cout) Qout ρ) ?_ h
  intro ls e ρ hstep
  refine ewp_fold hM (wpG_bind (hndK (hndVal n qs hr hs)) e ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_) hstep
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · -- `[ret]`
    exact wpG_head (fun μ => Head.hret μ n qs hr hs v) rfl _ _ σ
      (ewp_unfold hM (hret _ _ _ hv))
  rcases ht with ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · -- `[op]` at the handler's name: the clause, with `κ` and its cell
      subst hm
      obtain ⟨hgr, hlin, -⟩ := hn i en hT
      rw [shareAt_true hgr] at hcont
      obtain ⟨c, hc, hna⟩ := hop i en hT
      refine wpG_head (fun μ => Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl _ _ σ ?_
      rw [hq i en hT, kappaAt_tag, hlin]
      refine ewp_unfold hM (ewp_kappaCell hM _
        (hndVal m qs hr hs) K₁ (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₁ σ₂ hcell hc₂ => ?_))
      obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hcak hc₂
      refine hna ls' v ⟨_, isVal_kappaC _ ℓ (hndVal m qs hr hs) K₁⟩ σ₂ ⟨ρa, y, hy₂, hA, ?_⟩
      intro ls'' hs'' w τ₁ τ₂ hB hcτ
      obtain ⟨z, hz, hzτ⟩ := compS_exch hy₁ hcτ
      exact ewp_kappaC_resume hM _ ℓ _ K₁ w
        ⟨σ₁, z, ResU.CompS.comm hzτ, hcell, hcont ls'' hs'' w τ₁ z hB hz⟩
    · -- an operation of another name passes outward, at its own grade
      have hT' : Tout m i = some en := (hTin m i hm) ▸ hT
      have hHK : ((hndK (hndVal n qs hr hs)).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      refine wpG_here _ _ _ σ (Or.inr (Or.inl ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v, en,
        pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, hHK, hT', ha⟩ ⟨ρa, ρk, hcak, hA, ?_⟩⟩))
      cases hg : Cin m i
      · rw [shareAt_false hg] at hcont
        rw [shareAt_false ((hCin m i hm) ▸ hg)]
        refine ⟨hcont.1, fun ls'' he => ⟨fun w τ₁ τ₂ hB hc => ?_, fun hq' => ?_⟩⟩
        · rw [Kont.plug_comp]; exact (hcont.2 ls'' he).1 w τ₁ τ₂ hB hc
        · intro P hP
          show P ls'' (((hndK (hndVal n qs hr hs)).comp K₁).dead.plug _) ρk
          rw [dead_comp, dead_hndK]
          exact (hcont.2 ls'' he).2 hq' P hP
      · rw [shareAt_true hg] at hcont
        rw [shareAt_true ((hCin m i hm) ▸ hg)]
        intro ls'' hs'' w τ₁ τ₂ hB hc
        rw [Kont.plug_comp]; exact hcont ls'' hs'' w τ₁ τ₂ hB hc
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n
    · subst hm; exact absurd (hn i en hT).2.2 (by rw [ha]; decide)
    · -- an abortive operation of another name passes outward
      refine wpG_here _ _ _ σ (Or.inr (Or.inr ⟨(hndK (hndVal n qs hr hs)).comp K₁, m, i, v,
        en, pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))
      rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm

/-- **A tail clause meets the clause obligation.** The clause `λ(x, κ). (λw. κ.1 w) (g x)` at a
call-like operation, `g` answering at a class-1 row `TN` inside the outer table: `g x` answers in
the scope of the stop, where `κ` is owed. -/
theorem tail_hop {TN : OpTab} {CN : Grade} (hC : CallRow TN CN) {Tout : OpTab} {Cout : Grade}
    (hle : TN.Le Tout) (hg' : ∀ n i en, TN n i = some en → Cout n i = true)
    {Qout : List SRec → Val → WProp} {en : OpEnt} {c g : Val}
    (hcg : ∀ v κ : Val, PureSteps (.app (.val c) (.pair (.val v) κ.1))
      ((resK κ).plug (.app (.val g) (.val v))))
    (hgs : ∀ ls v ρ, en.PA ls v ρ → ewpTS ls (.app (.val g) (.val v)) (opTableC TN CN) en.PB ρ)
    {ls : List SRec} {v κ : Val} {ρ : WRes}
    (h : (en.PA ls v ⋆ KapRelC (opTableC Tout Cout) Qout en ls κ) ρ) :
    ewpTS ls (.app (.val c) (.pair (.val v) κ.1)) (opTableC Tout Cout) Qout ρ := by
  have hM := opTableC_mono Tout Cout
  obtain ⟨ρa, ρk, hc, hA, hK⟩ := h
  refine ewp_pureSteps hM (hcg v κ) _ _ ρ ?_
  refine ewp_frame_call hC hle hg' (resK κ) (resK_plain κ).1
    (fun ls => KapRelC (opTableC Tout Cout) Qout en ls κ)
    (fun ls ls' hs ρ h => KapRelC.same hs h) en.PB Qout ?_ (hgs ls v ρa hA) hK hc
  rintro ls' w σ ⟨σ₁, σ₂, hcσ, hB, hK'⟩
  refine ewp_pureSteps hM (resK_steps κ w) _ _ σ ?_
  exact hK' ls' (SameMem.refl ls') w σ₁ σ (hB) (ResU.CompS.comm hcσ)

end SuspSpike

end
