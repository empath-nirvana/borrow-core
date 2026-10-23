import Core.EffRules
import Core.DivRules
import Core.FoldImm
import Core.Slices

/-!
# Core — the unwinding forms of the borrow constants  `[spec §19]`

Each borrow constant has a pure form (§3) and an **unwinding form**, whose callback runs at a row
`Σ` of abortive operations only (`Row.Unwind`). The unwinding form's term is the pure one's
wrapped in `ubind` (`withborUE`):

    withborU d = λr. λf. (f [] r) then b. (r, b) unwind d r

When the callback returns, the source is paired with the answer, as the pure form does. When it
unwinds, the lend ends, the source goes back to the lender, the lender's finaliser `d` runs on it
(`dtorE` of the source: `forget` for a `Mut`/`Imm` source, `free` and the content's destructor
for an owned `Ref A`, §12), and the unwind continues outward.

**The proofs.** The callback runs under the frame of `[TR]` 6.64/6.65/6.66 over `ewpTS` at an
abortive table: `ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU` (`Core/EffWp.lean`),
the LIFO frame lemmas. Their table is the row's, extended so that a stop also hands back the
source the frame returned (`Table.withFr`). A stop of the callback is a `raise`: its abandoned
continuation holds nothing owned and is left behind (`wpG_garbage`), and its argument outlives
the frame because an operation's argument type outlives every lifetime (`Row.Unwind`). The frame
then ends at the stop exactly as at a return, and `ewp_unwind` runs the finaliser on the returned
source and raises again.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload ubindE eLoad)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### A table whose stops hand back a frame -/

/-- `Tb` with the frame `Fr` beside every stop: the stop of a callback under a borrow's frame,
holding the source the frame gave back.  `[spec §19]` -/
def Table.withFr (Tb : Table) (Fr : List SRec → WProp) : Table := fun ls t Φ => Tb ls t Φ ⋆ Fr ls

theorem Table.withFr_abortive {Tb : Table} (h : Tb.Abortive) (Fr : List SRec → WProp) :
    (Tb.withFr Fr).Abortive := by
  rintro ls t Φ Φ' ρ ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
  exact ⟨ρ₁, ρ₂, hc, h ls t Φ Φ' ρ₁ h₁, h₂⟩

/-- **The unwinding frame.**  `ubind (N, D) [·]` around a computation of an abortive row whose
every end hands back the frame `Fr`: at a return, `N` runs on the answer and the frame; at a
`raise`, the finaliser `D` runs on the frame, and the `raise` goes on.  `[spec §19]` -/
theorem ewp_unwind (T : OpTab) (hA : T.AbortOnly) (hL : T.Local) (h0 : ∀ i, T 0 i = none)
    (Nv Dv : Val) (Fr : List SRec → WProp)
    {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → v = .unit ∧ NoOwn ρ)
    (hD : ∀ ls, Entails (Fr ls) (wpTS ls (.app (.val Dv) (.val .unit)) Qd))
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v ⋆ Fr ls)
      (ewpTS ls ((ubindK Nv Dv).plug (.val v)) (opTable T) Q))
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e ((opTable T).withFr Fr) (fun ls v => Q₁ ls v ⋆ Fr ls) ρ) :
    ewpTS ls ((ubindK Nv Dv).plug e) (opTable T) Q ρ := by
  refine ewp_fold (opTable_mono T) (wpG_bind (ubindK Nv Dv) e ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_)
    ((ewp_abortive (Table.withFr_abortive (opTable_abortive hA) Fr)).mp h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨σ₁, σ₂, hcσ, hp, hF⟩
  · exact ewp_unfold (opTable_mono T) (hk ls' v σ hv)
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    rw [hA n i en hT] at ha; exact absurd ha (by simp)
  obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
  have hn0 : n ≠ 0 := fun h => by subst h; rw [h0 i] at hT; exact absurd hT (by simp)
  refine wpG_head (fun μ => Head.ufin μ Nv Dv n i v K₁ hn0 hK₁) rfl _ _ σ ?_
  refine wpG_bind (.seq .hole (raiseE (.val (opPayload n i v)))) _ ls' _ σ ?_
  let R : List SRec → WProp := fun ls => (fun τ => en.PA ls v τ ∧ NoOwn τ) ⋆ fun τ => NoOwn τ
  have hRs : ∀ ls'', (∀ x, x ∈ ls'' ↔ x ∈ ls') → Entails (R ls') (R ls'') := by
    rintro ls'' hs τ ⟨τa, τb, hcab, ⟨hPA', hnA'⟩, hnb⟩
    exact ⟨τa, τb, hcab, ⟨(hL n i en hT ls' ls'' v τa (ext_of_same hs τa)).1 hPA', hnA'⟩, hnb⟩
  have h₂ := wpG_frame (e := .app (.val Dv) (.val .unit)) R hRs σ
    ⟨σ₂, σ₁, ResU.CompS.comm hcσ, (wpTS_iff_wpG _ _ _ _).mp (hD ls' σ₂ hF),
      ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩
  refine wpG_mono (fun ls'' t τ ht => ?_) h₂
  obtain ⟨τ₁, τ₂, hcτ, ⟨w, rfl, hw⟩, ra, rn, hcr, ⟨hPA', hnA'⟩, hnr⟩ := ht
  obtain ⟨rfl, hnw⟩ := hQd _ _ _ hw
  refine wpG_head (fun μ => Head.seq μ _) rfl _ _ τ ?_
  obtain ⟨z, hz, hcz⟩ := compS_lcomm hcr hcτ
  exact wpG_here _ _ _ τ (Or.inr (Or.inr ⟨.hole, n, i, v, en,
    pure_sep_mk ⟨rfl, rfl, hT, ha⟩
      ⟨ra, z, hcz, ⟨hPA', hnA'⟩, noOwn_compS hz hnw hnr⟩⟩))

/-! ### A callback's run under a frame -/

/-- **The ends of a run at an abortive row.**  A return answers in `Q₁`; at a `raise` the
abandoned continuation holds nothing owned and is left behind (`wpG_garbage`), so the stop is
held by its argument's resource alone.  `[spec §19]` -/
theorem ewp_end {T : OpTab} (hA : T.AbortOnly) {Q₁ : List SRec → Val → WProp}
    (P : List SRec → Expr → WProp) (hval : ∀ ls v ρ, Q₁ ls v ρ → P ls (.val v) ρ)
    (hstop : ∀ ls t ρ, opTable T ls t (fun _ _ _ => False) ρ →
      (∃ n i en v, T n i = some en ∧ en.PA ls v ρ) → P ls t ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpTS ls e (opTable T) Q₁ ρ) :
    wpG ls e P ρ := by
  refine wpG_garbage (wpG_mono (fun ls' t σ ht => ?_)
    ((ewp_abortive (opTable_abortive hA)).mp h))
  rcases ht with ⟨v, rfl, hv⟩ | hp
  · exact ⟨σ, PMap.empty, ResU.comp_empty_right σ, noOwn_empty, hval _ _ _ hv⟩
  rcases hp with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    rw [hA n i en hT] at ha; exact absurd ha (by simp)
  obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
  exact ⟨ρa, ρn, hcan, hn, hstop _ _ _ (Or.inr ⟨K₁, n, i, v, en, pure_sep_mk ⟨rfl, hK₁, hT, ha⟩
    ⟨ρa, PMap.empty, ResU.comp_empty_right ρa, ⟨hPA, hnA⟩, noOwn_empty⟩⟩) ⟨n, i, en, v, hT, hPA⟩⟩

/-- **A callback at an abortive row ends in `Res_α`.**  At a return the answer is boxed at `α`
by its type; at a `raise` the abandoned continuation is left behind, and the argument outlives
`α` (`hout`).  So every end of the run is boxed at `α`, as a borrow's frame asks of its
callback.  `[spec §19]` -/
theorem ewp_box_end {T : OpTab} (hA : T.AbortOnly) {α : Life}
    (hout : ∀ n i en, T n i = some en → ∀ ls v ρ, en.PA ls v ρ → BoLo.Outlives ρ α)
    {Q₁ : List SRec → Val → WProp} (P : List SRec → Expr → WProp)
    (hval : ∀ ls v ρ, Q₁ ls v ρ → box α (P ls (.val v)) ρ)
    (hstop : ∀ ls t ρ, opTable T ls t (fun _ _ _ => False) ρ → P ls t ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpTS ls e (opTable T) Q₁ ρ) :
    wpG ls e (fun ls t => box α (P ls t)) ρ :=
  ewp_end hA _ hval (fun ls t ρ hst ⟨n, i, en, v, hT, hPA⟩ =>
    ⟨hstop ls t ρ hst, hout n i en hT ls v ρ hPA⟩) h

/-! ### The row of an unwinding callback -/

/-- The row of a callback that may unwind out of a borrow of lifetime `'x`: every operation is
abortive and named (not the reserved `0`), and its argument type is closed data: free of `'x` and
outliving every lifetime ("operation types are closed in lifetimes", §19); its answer type is free
of `'x` too.  `[spec §19, §53]` -/
def Row.Unwind (S : Row) (x : LifeVar) : Prop :=
  ∀ o ∈ S, o.abort = true ∧ o.n ≠ 0 ∧ ¬ VFree x o.A ∧ ¬ VFree x o.B ∧ ∀ Δ a, VOutlives Δ a o.A

theorem Row.Unwind.nz {S : Row} {x : LifeVar} (hS : S.Unwind x) : S.NZ :=
  fun o ho => (hS o ho).2.1

/-- **`tick` cannot cross a borrow**: an unwind-only row does not hold `Div`.  `[spec §14, §19]` -/
theorem Row.Unwind.divB {S : Row} {x : LifeVar} (hS : S.Unwind x) : Row.divB S = false :=
  Row.divB_of_abort fun o ho => (hS o ho).1

theorem Row.Unwind.abort {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) :
    (Row.tab S δ).AbortOnly := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  exact (hS o (Row.find_mem hf).1).1

/-- The row's table does not see `'x`. -/
theorem Row.Unwind.tab_extend {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (α : Life) :
    Row.tab S (δ.extend x α) = Row.tab S δ := by
  funext n i
  unfold Row.tab
  cases hf : Row.find S n i with
  | none => rfl
  | some o =>
      obtain ⟨ha, -, hx, hB, -⟩ := hS o (Row.find_mem hf).1
      have hc : capB o.cnt = false := by
        simp only [OpSig.abort, beq_iff_eq] at ha; simp [ha]
      simp only [Option.map_some, OpSig.ent, vC_extend_of_not_free hx,
        vC_extend_of_not_free hB, hc, Bool.false_eq_true, if_false]

/-- An argument of the row outlives every lifetime. -/
theorem Row.Unwind.out {S : Row} {x : LifeVar} (hS : S.Unwind x) (δ : LSub) (α : Life) :
    ∀ n i en, Row.tab S δ n i = some en → ∀ ls v ρ, en.PA ls v ρ → BoLo.Outlives ρ α := by
  intro n i en hT ls v ρ hPA
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨-, -, hx, -, hO⟩ := hS o (Row.find_mem hf).1
  have h' : vC true o.A ls (δ.extend x α) v ρ := by
    rw [vC_extend_of_not_free hx]; exact hPA
  exact vC_outlives (Δ := LifeCtx.empty) (a := .var x) (models_empty_any _)
    (interp_ext_self δ x α) (hO _ _) true ls v ρ h'

/-! ### The constants -/

/-- An unwinding callback, a thunk of `∀'x ⊏ @bnd. L ⊸ F_Σ(['x] B)`, `L` the lend.
`[spec §19]` -/
def cbUTy (x : LifeVar) (bnd : Lifetime.Life) (L B : VTy) (S : Row) : VTy :=
  .thunk (.all x bnd (.arr L (CTy.effOf S (.box (.var x) B))))

/-- An unwinding borrow constant's type: `U(src ⊸ cb ⊸ F_Σ R)`.  `[spec §19]` -/
def withborUTy (src cb : VTy) (S : Row) (R : VTy) : VTy :=
  .thunk (.arr src (.arr cb (CTy.effOf S R)))

/-- `withbor : Ref A ⊸ (∀'x ⊏ @bnd. Imm 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)`.  `[spec §19]` -/
def withbor1UTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) : VTy :=
  withborUTy (.ref A) (cbUTy x bnd (.imm (.var x) A) B S) S (.tensor (.ref A) B)

/-- `withbor : Ref A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)`.  `[spec §19]` -/
def withbor2UTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) : VTy :=
  withborUTy (.ref A) (cbUTy x bnd (.mut (.var x) A) B S) S (.tensor (.ref A) B)

/-- `withbor : Mut @a A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a A ⊗ B)`.
`[spec §19]` -/
def withbor3UTy (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) :
    VTy :=
  withborUTy (.mut a A) (cbUTy x bnd (.mut (.var x) A) B S) S (.tensor (.mut a A) B)

/-- **The unwinding form of `withbor`**, finalising the source with `d`:
`λr. λf. (f [] r) then b. (r, b) unwind d r`.  `[spec §19]` -/
def withborUE (d : Expr) : Expr :=
  .val (.lam (.val (.lam (thenE (.pair (.var 2) (.var 0)) (.app d (.var 2))
    (.app (.app (.var 0) (.val .unit)) (.var 1))))))

theorem withborUE_closed {d : Expr} (hd : closedAt 0 d = true) : closedAt 0 (withborUE d) = true := by
  simp [withborUE, thenE, closedAt, Expr.val, Val.lam, Val.unit, Val.prim,
    closedAt_mono d hd (Nat.zero_le 3)]

/-- The unwinding form as a value. -/
def withborUV (d : Expr) : Val := ⟨withborUE d, .lam⟩

/-- `withborU d u f` steps to the callback under the finaliser frame, `u` a closed source. -/
theorem withborUE_beta {Tb : Table} (hTb : Tb.Mono) {d : Expr} (hd : closedAt 0 d = true)
    (u : Val) (hu : closedAt 0 u.1 = true) (vf : Val) {ls : List SRec}
    {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls ((ubindK (Val.lam (.pair (.val u) (.var 0))) (Val.lam (.app d (.val u)))).plug
        (.app (.app (.val vf) (.val .unit)) (.val u))) Tb Q ρ) :
    ewpTS ls (.app (.app (.val (withborUV d)) (.val u)) (.val vf)) Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug (Kont.appL .hole vf))
    ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ vf) rfl) ls Q ρ ?_
  convert h using 1
  simp [thenE, Kont.plug, Expr.subst, Expr.val, Val.lam, Val.pair, Val.unit, Val.prim,
    Val.shift, closed_shift hu, closed_subst hu,
    subst_closedAt d (s := _) (closedAt_mono d hd (Nat.zero_le _)) (le_refl _)]

/-! ### The pieces every unwinding form shares -/

/-- A closed term's semantic judgment at a dead context, at every list. -/
theorem semV_dead_closed {Δ : LifeCtx} {Γ : Ctx VTy} {d : Expr} {T : VTy}
    (hdc : closedAt 0 d = true) (hd : SemV Δ Γ d T) {δ : LSub} {γ : List Val} {ls : List SRec}
    (hδ : Δ.Models δ) (hg : gDenC ls δ Γ γ PMap.empty) (ls' : List SRec) :
    wpTS ls' d (fun ls'' => vP T ls'' δ) PMap.empty := by
  have h := hd δ γ ls' PMap.empty hδ (gDenC_local (ext_empty' ls ls') hg)
  rwa [show substAll γ d = d from psub_closedAt d γ hdc (Nat.zero_le 0)] at h

/-- The finaliser `λ_. d u` on the returned source: `d`'s relation at the source's type.
`[spec §19]` -/
theorem fin_run {d : Expr} (hdc : closedAt 0 d = true) {src : VTy} {δ : LSub} {u : Val}
    (hu : closedAt 0 u.1 = true)
    (hd : ∀ ls, wpTS ls d (fun ls'' => vP (.lolli src .unit) ls'' δ) PMap.empty)
    (ls : List SRec) :
    Entails (vP src ls δ u)
      (wpTS ls (.app (.val (Val.lam (.app d (.val u)))) (.val .unit))
        (fun ls v => vP .unit ls δ v)) := by
  intro ρ hu'
  refine wpTS_lolli _ _ _ _ _ ?_
  rw [show Expr.subst 0 Val.unit (.app d (.val u)) = .app d (.val u) by
    simp [Expr.subst, subst_closedAt d (s := _) hdc (Nat.zero_le _), Expr.val, closed_subst hu]]
  refine wpTS_bind_frame (.appL .hole u) d ls (fun ls => vP (.lolli src .unit) ls δ)
    (fun ls => vP src ls δ u) _ (fun _ hs _ h => vP_same hs h) ?_ ρ
    ⟨PMap.empty, ρ, compS_empty_left ρ, hd ls, hu'⟩
  rintro ls' - g σ ⟨σ₁, σ₂, hc, hg, hu''⟩
  exact (hg ls' (Ext.refl _ _)) u σ₂ σ hu'' hc

/-- At a return the unwinding form pairs the source with the answer. -/
theorem ewp_ret_pair {Tb : Table} (hTb : Tb.Mono) (u : Val) (hu : closedAt 0 u.1 = true)
    (Dv w : Val) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : Q ls (Val.pair u w) ρ) :
    ewpTS ls ((ubindK (Val.lam (.pair (.val u) (.var 0))) Dv).plug (.val w)) Tb Q ρ := by
  refine ewp_step hTb (fun μ => Step1N.head (Head.uthen μ _ _ w) rfl) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ w) rfl) ls Q ρ ?_
  have e : Expr.subst 0 w (.pair (.val u) (.var 0)) = .val (Val.pair u w) := by
    simp [Expr.subst, Expr.val, Val.pair, closed_subst hu]
  rw [e]
  exact ewp_val hTb h

/-! ### `withbor` (2), unwinding -/

/-- **`withbor` (2) at an unwinding row**: `Ref A` lent as `Mut 'x A`.  `[TR]` 6.173's proof
(`withbor2_compatX`), with the frame over `ewpTS` (`ewpTS_M_frameU`) at the row's table, the
returned source beside each stop.  Every end of the callback is boxed at the frame's lifetime
(`ewp_box_end`), so the frame ends at a `raise` as at a return; then `ewp_unwind` pairs the
source with the answer, or finalises it and raises again.  Its side conditions are non-strict,
read at `↓@bδ`.  `[spec §19, §23]` -/
theorem withbor2U_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hdc : closedAt 0 d = true) (hd : SemV Δ Γ d (.lolli (.ref A) .unit)) :
    SemV Δ Γ (withborUE d) (withbor2UTy x Δ.meetOfDom A B S) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  have hdg := semV_dead_closed hdc hd hδ hg
  show wpTS ls (substAll γ (withborUE d)) _ _
  rw [show substAll γ (withborUE d) = .val (withborUV d) from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  intro vf ρ₂ τ hvf hc₂
  let T := Row.tab S δ
  have hA : T.AbortOnly := hS.abort δ
  refine (cC_effOf S _ ls₁ δ _ τ hS.divB).mpr (withborUE_beta (opTable_mono _) hdc (.loc ℓ) rfl vf ?_)
  -- the source handed back at every end of the callback
  let Fr : List SRec → WProp := fun ls => vP (.ref A) ls δ (.loc ℓ)
  let Q₁ : List SRec → Val → WProp := fun ls v => vP B ls δ v
  refine ewp_unwind T hA (Row.tab_local S δ) (Row.tab_zero hS.nz δ) _ _ Fr
    (Qd := fun ls v => vP .unit ls δ v) (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, noOwn_empty⟩)
    (fun ls => fin_run hdc rfl hdg ls) Q₁ _ ?_ ?_
  · -- a return: `(ℓ, v)`
    rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFr⟩
    refine ewp_ret_pair (opTable_mono _) (.loc ℓ) rfl _ v ?_
    exact ⟨.loc ℓ, v, pure_sep_mk rfl ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hFr, hv⟩⟩
  -- the Mut Frame over the callback, at the row's table with the source beside each stop
  obtain ⟨b, hdef, hO⟩ := hside
  obtain ⟨β, hb⟩ := hdef δ hδ
  -- 6.60 at the non-strict side condition: every stratum below `β`; the frame is
  -- taken at `↓β`  `[spec §23]`
  have hβ := fun ls' w σ' h =>
    vC_outlivesLe hδ hb hO true ls' w σ' h _ (Life.down_sqsubset β)
  generalize Life.down β = β at hβ
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine ewpTS_M_frameU ((opTable T).withFr Fr) (Table.withFr_abortive (opTable_abortive hA) Fr) ℓ A δ β
    (fun ls' w σ' h => hβ ls' w σ' h) vℓ _ ls₁ (fun ls v => Q₁ ls v ⋆ Fr ls) τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP, ?_⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  -- `─⋆R`: take the borrow `ℓ ↦ M α 𝒱⟦A⟧δ`
  intro ρm σ' hm' hcm
  have hmut' : vP (.mut (.var x) A) ls₁ (δ.extend x α) (.loc ℓ) ρm := by
    have e : (fun ls₀ => vC true A ls₀ (δ.extend x α)) = (fun ls₀ => vC true A ls₀ δ) :=
      funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
    refine ⟨α, interp_ext_self δ x α, ℓ, pure_sep_mk rfl ?_⟩
    show ptoMutS ℓ α ls₁ (fun ls₀ => vC true A ls₀ (δ.extend x α)) ρm
    rw [e]; exact hm'
  -- the callback at `α ⊏ ⊓Δδ`, at the borrow
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hcb := (hvf ls₁ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂))
    (.loc ℓ) ρm σ' hmut' hcm
  rw [cC_effOf (hS := hS.divB), hS.tab_extend δ α] at hcb
  refine ewp_box_end hA (hS.out δ α) _ ?_ ?_ hcb
  · -- a return: the answer leaves `['x]`, and the source joins it
    rintro ls'' v'' ρ'' ⟨α', hα', hB, hout⟩
    rw [interp_ext_self] at hα'
    cases Option.some.inj hα'
    have hB' : vP B ls'' δ v'' ρ'' := by rw [vC_extend_of_not_free hfree₂] at hB; exact hB
    refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
    obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
    exact Or.inl ⟨v'', rfl, ρ'', s, hρs, hB',
      ⟨ℓ, w, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩⟩
  · -- a `raise`: the source joins the stop
    intro ls'' t ρ'' hst w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp
    obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
    exact Or.inr ⟨ρ'', s, hρs, hst, ⟨ℓ, w, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩⟩

/-! ### `withbor` (3), unwinding -/

/-- **`withbor` (3) at an unwinding row**: `Mut @a A` reborrowed as `Mut 'x A`.  `[TR]` 6.174's
proof (`withbor3_compatX`): `AntiFrame` over `ewpTS` (`ewpTS_M_antiFrameU`) at the row's table,
the borrow given back beside each stop, then `MutFrame` (`wpG_M_frameX`) with its premise read off
the borrow in hand.  `[spec §19]` -/
theorem withbor3U_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {S : Row}
    {d : Expr} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hdc : closedAt 0 d = true) (hd : SemV Δ Γ d (.lolli (.mut a A) .unit)) :
    SemV Δ Γ (withborUE d) (withbor3UTy a x Δ.meetOfDom A B S) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  have hdg := semV_dead_closed hdc hd hδ hg
  show wpTS ls (substAll γ (withborUE d)) _ _
  rw [show substAll γ (withborUE d) = .val (withborUV d) from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  -- the `Mut` value: `ℓ ↦ M α₀ 𝒱⟦A⟧δ`
  obtain ⟨α₀, ha, ℓ, hs₂⟩ := id hv₁
  obtain ⟨rfl, hmut⟩ := pure_sep_iff.mp hs₂
  intro vf ρ₂ τ hvf hc₂
  let T := Row.tab S δ
  have hA : T.AbortOnly := hS.abort δ
  refine (cC_effOf S _ ls₁ δ _ τ hS.divB).mpr (withborUE_beta (opTable_mono _) hdc (.loc ℓ) rfl vf ?_)
  -- the borrow handed back at every end of the callback
  let Fr : List SRec → WProp := fun ls => vP (.mut a A) ls δ (.loc ℓ)
  let Q₁ : List SRec → Val → WProp := fun ls v => vP B ls δ v
  refine ewp_unwind T hA (Row.tab_local S δ) (Row.tab_zero hS.nz δ) _ _ Fr
    (Qd := fun ls v => vP .unit ls δ v)
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, noOwn_empty⟩)
    (fun ls => fin_run hdc rfl hdg ls) Q₁ _ ?_ ?_
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFr⟩
    refine ewp_ret_pair (opTable_mono _) (.loc ℓ) rfl _ v ?_
    exact ⟨.loc ℓ, v, pure_sep_mk rfl ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hFr, hv⟩⟩
  -- `MutFrame`'s premise, read off the borrow in hand
  obtain ⟨β, hβ⟩ : ∃ β, ∀ ls' w σ, vC true A ls' δ w σ → σ.InStratum β := by
    obtain ⟨b, -, -, -, -, -, -, -, -, -, -, hunif⟩ := hmut
    exact ⟨b, hunif⟩
  -- `AntiFrame` at `ℓ ↦ M α₀ 𝒱⟦A⟧δ`
  refine ewpTS_M_antiFrameU ((opTable T).withFr Fr) (Table.withFr_abortive (opTable_abortive hA) Fr)
    ℓ α₀ A δ _ ls₁ (fun ls v => Q₁ ls v ⋆ Fr ls) τ ⟨τ₀, ρ₂, hc₂, hmut, ?_⟩
  intro v₂ c₁ c₂ hc hcc p₁ p₂ hp hcp
  obtain ⟨σ, hcσ, hmid⟩ := compS_reassoc' hcc (ResU.CompS.comm hcp)
  refine wpG_M_frameX ℓ A δ β hβ v₂ _ ls₁ _ p₂
    ⟨c₁, σ, ResU.CompS.comm hmid, hc, p₁, ρ₂, hcσ, hp, ?_⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ρm σ' hm' hcm
  have hmut' : vP (.mut (.var x) A) ls₁ (δ.extend x α) (.loc ℓ) ρm := by
    have e : (fun ls₀ => vC true A ls₀ (δ.extend x α)) = (fun ls₀ => vC true A ls₀ δ) :=
      funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
    refine ⟨α, interp_ext_self δ x α, ℓ, pure_sep_mk rfl ?_⟩
    show ptoMutS ℓ α ls₁ (fun ls₀ => vC true A ls₀ (δ.extend x α)) ρm
    rw [e]; exact hm'
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hcb := (hvf ls₁ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂))
    (.loc ℓ) ρm σ' hmut' hcm
  rw [cC_effOf (hS := hS.divB), hS.tab_extend δ α] at hcb
  refine ewp_box_end hA (hS.out δ α) _ ?_ ?_ hcb
  · rintro ls'' v'' ρ'' ⟨α', hα', hB, hout⟩
    rw [interp_ext_self] at hα'
    cases Option.some.inj hα'
    have hB' : vP B ls'' δ v'' ρ'' := by rw [vC_extend_of_not_free hfree₂] at hB; exact hB
    refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
    obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
    obtain ⟨W, hcWi, hcW⟩ := compS_reassoc hs (ResU.CompS.comm hρs)
    exact ⟨w, c₁, W, hcW, hc₁, p₁, ρ'', hcWi, hp, fun m₁ m₂ hm hcm =>
      Or.inl ⟨v'', rfl, ρ'', m₁, hcm, hB', ⟨α₀, ha, ℓ, pure_sep_mk rfl hm⟩⟩⟩
  · intro ls'' t ρ'' hst w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp
    obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
    obtain ⟨W, hcWi, hcW⟩ := compS_reassoc hs (ResU.CompS.comm hρs)
    exact ⟨w, c₁, W, hcW, hc₁, p₁, ρ'', hcWi, hp, fun m₁ m₂ hm hcm =>
      Or.inr ⟨ρ'', m₁, hcm, hst, ⟨α₀, ha, ℓ, pure_sep_mk rfl hm⟩⟩⟩

/-! ### `withbor` (1), unwinding -/

/-- A stop of an abortive table is carried along `Ext`. -/
theorem opTable_ext {T : OpTab} (hA : T.AbortOnly) (hL : T.Local) {ls ls' : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (he : Ext ls ls' ρ) (h : opTable T ls t Φ ρ) :
    opTable T ls' t Φ ρ := by
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp h
    rw [hA n i en hT] at ha; exact absurd ha (by simp)
  · obtain ⟨hp, ρa, ρb, hc, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk hp
      ⟨ρa, ρb, hc, ⟨(hL n i en hp.2.2.1 ls ls' v ρa (he.left hc)).1 hPA, hnA⟩, hn⟩⟩

/-- **`withbor` (1) at an unwinding row**: `Ref A` lent as `Imm 'x A`.  `[TR]` 6.172's proof
(`withbor1_compatX`), with the frame over `ewpTS` (`ewpTS_I_frameU`) at the row's table, the
returned source beside each stop.  `[spec §19]` -/
theorem withbor1U_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc₁ : VScoped Δ A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hdc : closedAt 0 d = true) (hd : SemV Δ Γ d (.lolli (.ref A) .unit)) :
    SemV Δ Γ (withborUE d) (withbor1UTy x Δ.meetOfDom A B S) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  have hdg := semV_dead_closed hdc hd hδ hg
  show wpTS ls (substAll γ (withborUE d)) _ _
  rw [show substAll γ (withborUE d) = .val (withborUV d) from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  intro vf ρ₂ τ hvf hc₂
  let T := Row.tab S δ
  have hA : T.AbortOnly := hS.abort δ
  have hL : T.Local := Row.tab_local S δ
  refine (cC_effOf S _ ls₁ δ _ τ hS.divB).mpr (withborUE_beta (opTable_mono _) hdc (.loc ℓ) rfl vf ?_)
  let Fr : List SRec → WProp := fun ls => vP (.ref A) ls δ (.loc ℓ)
  let Q₁ : List SRec → Val → WProp := fun ls v => vP B ls δ v
  refine ewp_unwind T hA hL (Row.tab_zero hS.nz δ) _ _ Fr
    (Qd := fun ls v => vP .unit ls δ v)
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, noOwn_empty⟩)
    (fun ls => fin_run hdc rfl hdg ls) Q₁ _ ?_ ?_
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFr⟩
    refine ewp_ret_pair (opTable_mono _) (.loc ℓ) rfl _ v ?_
    exact ⟨.loc ℓ, v, pure_sep_mk rfl ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hFr, hv⟩⟩
  -- every end of the callback is carried along `Ext`
  have hQ : ∀ ls₁ ls₂ (w : Expr) ρ, Ext ls₁ ls₂ ρ →
      ewpPost ((opTable T).withFr Fr) (fun ls v => Q₁ ls v ⋆ Fr ls) ls₁ w ρ →
      ewpPost ((opTable T).withFr Fr) (fun ls v => Q₁ ls v ⋆ Fr ls) ls₂ w ρ := by
    rintro ls₁ ls₂ w ρ he (⟨v, rfl, ρa, ρb, hc, hq, hf⟩ | ⟨ρa, ρb, hc, hst, hf⟩)
    · exact Or.inl ⟨v, rfl, ρa, ρb, hc, vC_local true B (he.left hc) hq,
        vC_local true (.ref A) (he.right hc) hf⟩
    · exact Or.inr ⟨ρa, ρb, hc, opTable_ext hA hL (he.left hc) hst,
        vC_local true (.ref A) (he.right hc) hf⟩
  -- `ImmFrame` at `ℓ ↦ vℓ ⋆ 𝒱⟦A⟧δ(vℓ)`
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine ewpTS_I_frameU ((opTable T).withFr Fr) (Table.withFr_abortive (opTable_abortive hA) Fr)
    ℓ A δ (admWf_of_vScoped hsc₁ hδ) vℓ _ ls₁ (fun ls v => Q₁ ls v ⋆ Fr ls) hQ τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP, ?_⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  have hout₂ : ρ₂.InStratum α := outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)
  intro ls' hadd hrec ρm σ' hm' hcm
  have himm' : vP (.imm (.var x) A) ls' (δ.extend x α) (.loc ℓ) ρm := by
    obtain ⟨r, hr, hle, hT, hδr⟩ := hrec
    refine ⟨α, interp_ext_self δ x α, ℓ, pure_sep_mk ⟨rfl, cohE_of_coh
      (Or.inl ⟨r, hr, hle.symm, hT.symm, fun y hy => ?_⟩)⟩ ?_⟩
    · rw [hδr]
      rw [hT] at hy
      exact find?_extend_ne δ α (fun e => by subst e; exact hfree₁ hy)
    · exact ptoImmS_mono (fun ls₀ u σ h => by
        rw [vC_extend_of_not_free hfree₁]; exact vO_obs A h) hm'
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hcb := (hvf ls' (ext_add hadd hout₂) α PMap.empty ρ₂ ⟨rfl, hlt⟩
    (ResU.comp_empty_right ρ₂)) (.loc ℓ) ρm σ' himm' hcm
  rw [cC_effOf (hS := hS.divB), hS.tab_extend δ α] at hcb
  refine ewp_box_end hA (hS.out δ α) _ ?_ ?_ hcb
  · rintro ls'' v'' ρ'' ⟨α', hα', hB, hout⟩
    rw [interp_ext_self] at hα'
    cases Option.some.inj hα'
    have hB' : vP B ls'' δ v'' ρ'' := by rw [vC_extend_of_not_free hfree₂] at hB; exact hB
    refine ⟨fun c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, hout⟩
    obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
    exact Or.inl ⟨v'', rfl, ρ'', s, hρs, hB', ⟨ℓ, vℓ, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩⟩
  · intro ls'' t ρ'' hst c₁ c₂ hc₁ hcc p₁ p₂ hp hcp
    obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
    exact Or.inr ⟨ρ'', s, hρs, hst, ⟨ℓ, vℓ, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩⟩

/-! ### `withload`, unwinding -/

/-- `withload : Imm @a A ⊸ (∀'x ⊏ @bnd. Imm̲ 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ B`.  `[spec §19]` -/
def withloadUTy (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) :
    VTy :=
  withborUTy (.imm a A) (cbUTy x bnd (VTy.immReborrow (.var x) A) B S) S B

/-- `withload` as a value. -/
def withloadV : Val := ⟨withload, .lam⟩

/-- `withload ℓ f` steps to `f () (load ℓ)`. -/
theorem withload_beta {Tb : Table} (hTb : Tb.Mono) (ℓ : BoCa.Loc) (vf : Val) {ls : List SRec}
    {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls (.app (.app (.val vf) (.val .unit)) (eLoad ℓ)) Tb Q ρ) :
    ewpTS ls (.app (.app (.val withloadV) (.val (.loc ℓ))) (.val vf)) Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug (Kont.appL .hole vf))
    ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ vf) rfl) ls Q ρ ?_
  convert h using 1
  simp [eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit', load', Expr.val, Val.loc,
    Val.unit, Val.prim]

/-- **`withload` at an unwinding row.**  `withload`'s source is consumed by the load, so nothing
goes back to the lender and the term is `withload`'s own.  `[TR]` 6.175's proof
(`withload_compatX`), with 6.150 at `wpG` (`wpG_reborrow`): the reborrow ends when the callback
stops, at a `raise` as at a return.  `[spec §19]` -/
theorem withloadU_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A B : VTy} {S : Row}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) :
    SemV Δ Γ withload (withloadUTy a x Δ.meetOfDom A B S) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls (.val withloadV) _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨α₀, ha, ℓ, hs₂⟩ := id hv₁
  obtain ⟨⟨rfl, hcoh⟩, himm⟩ := pure_sep_iff.mp hs₂
  intro vf ρ₂ τ hvf hc₂
  let T := Row.tab S δ
  have hA : T.AbortOnly := hS.abort δ
  refine (cC_effOf S _ ls₁ δ _ τ hS.divB).mpr (withload_beta (opTable_mono _) ℓ vf ?_)
  refine ewp_fold (opTable_mono _)
    (wpG_bind_pure (.appR (.app (.val vf) (.val .unit)) .hole) (eLoad ℓ) ls₁ _ τ ?_)
  -- `wp-load-I`
  refine wpTS_load_I ls₁ ℓ α₀ (fun u => vC false A ls₁ δ u) _ τ
    ⟨τ₀, ρ₂, hc₂, ptoImmO_toImm himm, ?_⟩
  intro vℓ ρc ρcomp hcell hccomp
  simp only [Kont.plug]
  have hesc : RebChooseTW ls₁ ℓ
      (fun w σ => w = vℓ ∧ vC false A ls₁ δ w σ)
      (fun β w χ => vShape (A.immReborrow (.var x)) (δ.extend x β) w χ)
      (fun β w χ => (⌜vℓ = w⌝ ⋆ vC true (A.immReborrow (.var x)) ls₁ (δ.extend x β) w) χ) := by
    obtain ⟨S₀, δ₀, he, hc⟩ := hcoh
    have hx₀ : ¬ VFree S₀.lifeBound S₀ := fun h => lt_irrefl _ (lt_vLifeBound h)
    have heβ : ∀ β : Life, TyEq (A.immReborrow (.var x)) (δ.extend x β)
        (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) := fun β =>
      TyEq.immReborrow (by rw [interp_ext_self, interp_ext_self])
        (TyEq.extend_left hx₀ β (TyEq.extend_left hfree₁ β he).symm).symm
    have eR : vC false A ls₁ δ = vC false S₀ ls₁ δ₀ := vC_tyEq he false ls₁
    have eP₀ : ∀ β : Life, vShape (A.immReborrow (.var x)) (δ.extend x β)
        = vShape (S₀.immReborrow (.var S₀.lifeBound)) (δ₀.extend S₀.lifeBound β) :=
      fun β => vShape_tyEq (heβ β)
    have eP : ∀ β : Life, vC true (A.immReborrow (.var x)) ls₁ (δ.extend x β)
        = vC true (S₀.immReborrow (.var S₀.lifeBound)) ls₁ (δ₀.extend S₀.lifeBound β) :=
      fun β => vC_tyEq (heβ β) true ls₁
    simp only [eR, eP₀, eP]
    rcases hc with ⟨r, hr, rfl, rfl, hag⟩ | ⟨r, hr, p, u, hch, hag⟩
    · exact rebChooseTW_pin vℓ (rebChooseTW_top hr hag hx₀)
    · exact rebChooseTW_pin vℓ (rebChooseTW_deep hr hch hag hx₀)
  have hcell' : ptoImm ℓ α₀ (fun v σ => (v = vℓ ∧ vC false A ls₁ δ v σ) ∧
      fresh (fun b => reborrow b (vShape (A.immReborrow (.var x)) (δ.extend x b) v)) σ) ρc := by
    refine ptoImm_mono (fun u σ h => ?_) ρc hcell
    obtain ⟨he, hobs⟩ := pure_sep_iff.mp h
    subst he
    exact ⟨⟨rfl, hobs⟩, six132_shape_fresh hfree₁ δ vℓ σ (vC_vShape false A hobs)⟩
  -- 6.150 at `wpG`
  refine wpG_reborrow ls₁ ℓ α₀ _ _ _ _ _ hesc ρcomp ⟨ρc, ρ₂, ResU.CompS.comm hccomp, hcell', ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨g₂, hg₂⟩ := ResU.exists_stratum ρ₂
  refine ⟨m ⊓ g₂, fun β hβ => ⟨?_, hg₂.mono (le_of_lt (lt_of_lt_of_le hβ inf_le_right))⟩⟩
  intro v σ ρpc hP hpc
  obtain ⟨hvv, hreb⟩ := pure_sep_iff.mp hP
  subst hvv
  have hlt : LtLife δ Δ.meetOfDom β := ⟨m, hm, lt_of_lt_of_le hβ inf_le_left⟩
  have hcb := (hvf ls₁ (Ext.refl _ _) β PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂))
    vℓ σ ρpc hreb hpc
  rw [cC_effOf (hS := hS.divB), hS.tab_extend δ β] at hcb
  refine ewp_box_end hA (hS.out δ β) _ ?_ ?_ hcb
  · rintro ls'' v'' ρ'' ⟨α', hα', hB, hout⟩
    rw [interp_ext_self] at hα'
    cases Option.some.inj hα'
    have hB' : vP B ls'' δ v'' ρ'' := by rw [vC_extend_of_not_free hfree₂] at hB; exact hB
    exact ⟨Or.inl ⟨v'', rfl, hB'⟩, hout⟩
  · intro ls'' t ρ'' hst
    exact Or.inr (opTable_abortive hA _ _ _ _ _ hst)

/-! ### The slice borrows, unwinding -/

/-- `slice_borrow : Array A ⊸ (∀'x ⊏ @bnd. [Mut 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`.
`[spec §19]` -/
def sliceBorrowMUTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) : VTy :=
  withborUTy (.array A) (cbUTy x bnd (VTy.sliceMut (.var x) A) B S) S (.tensor (.array A) B)

/-- `slice_borrow : Array A ⊸ (∀'x ⊏ @bnd. [Imm 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`.
`[spec §19]` -/
def sliceBorrowIUTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) : VTy :=
  withborUTy (.array A) (cbUTy x bnd (.arrayImm (.var x) A) B S) S (.tensor (.array A) B)

theorem arr_closed (ℓ : BoCa.Loc) (n : UInt32) : closedAt 0 (Val.arr ℓ n).1 = true := rfl

/-- The ends of an unwinding callback under a family's frames: a result of `B`, or a stop held by
its argument alone. -/
def cbEnds (T : OpTab) (B : VTy) (δ : LSub) : List SRec → Expr → WProp := fun ls t ρ =>
  (∃ v, t = .val v ∧ vP B ls δ v ρ) ∨
    (opTable T ls t (fun _ _ _ => False) ρ ∧ ∃ n i en v, T n i = some en ∧ en.PA ls v ρ)

/-- **The `Mut` slice borrow at an unwinding row.**  `sliceBorrowM_compatX`'s proof, the `n`
Mut Frames at `wpG` (`wpG_M_frameFam`) around the callback, whose ends are a result or a stop
held by its argument (`cbEnds`, `ewp_end`).  Its side conditions are non-strict, read at
`↓@bδ`.  `[spec §19, §23]` -/
theorem sliceBorrowMU_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hdc : closedAt 0 d = true) (hd : SemV Δ Γ d (.lolli (.array A) .unit)) :
    SemV Δ Γ (withborUE d) (sliceBorrowMUTy x Δ.meetOfDom A B S) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  have hdg := semV_dead_closed hdc hd hδ hg
  show wpTS ls (substAll γ (withborUE d)) _ _
  rw [show substAll γ (withborUE d) = .val (withborUV d) from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp hv₁
  intro vf ρ₂ τ hvf hc₂
  let T := Row.tab S δ
  have hA : T.AbortOnly := hS.abort δ
  refine (cC_effOf S _ ls₁ δ _ τ hS.divB).mpr
    (withborUE_beta (opTable_mono _) hdc (Val.arr ℓ n) (arr_closed ℓ n) vf ?_)
  let Fr : List SRec → WProp := fun ls => vP (.array A) ls δ (Val.arr ℓ n)
  let Q₁ : List SRec → Val → WProp := fun ls v => vP B ls δ v
  refine ewp_unwind T hA (Row.tab_local S δ) (Row.tab_zero hS.nz δ) _ _ Fr
    (Qd := fun ls v => vP .unit ls δ v)
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, noOwn_empty⟩)
    (fun ls => fin_run hdc (arr_closed ℓ n) hdg ls) Q₁ _ ?_ ?_
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFr⟩
    refine ewp_ret_pair (opTable_mono _) (Val.arr ℓ n) (arr_closed ℓ n) _ v ?_
    exact ⟨Val.arr ℓ n, v, pure_sep_mk rfl ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hFr, hv⟩⟩
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βA, hβA⟩ := hdefa δ hδ
  -- 6.60 at the non-strict side condition: every stratum below `βA`; the frame is
  -- taken at `↓βA`  `[spec §23]`
  have hA' := fun ls' w σ' h =>
    vC_outlivesLe hδ hβA hOa true ls' w σ' h _ (Life.down_sqsubset βA)
  generalize Life.down βA = βA at hA'
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  -- 6.60 at the non-strict side condition: every stratum below `βB`; the frame is
  -- taken at `↓βB`  `[spec §23]`
  have hB := fun ls' w σ' h =>
    vC_outlivesLe hδ hβB hOb true ls' w σ' h _ (Life.down_sqsubset βB)
  generalize Life.down βB = βB at hB
  have hΦ : ∀ ls' t σ, cbEnds T B δ ls' t σ → BoLo.Outlives σ βB := by
    rintro ls' t σ (⟨v, -, hv⟩ | ⟨-, n, i, en, v, hT, hPA⟩)
    · exact hB ls' v σ hv
    · exact hS.out δ βB n i en hT ls' v σ hPA
  refine (ewp_abortive (Table.withFr_abortive (opTable_abortive hA) Fr)).mpr ?_
  refine wpG_M_frameFam A δ βA (fun ls' w σ h => hA' ls' w σ h) _ ls₁ (cbEnds T B δ) βB hΦ
    n.toNat ℓ _ ?_ τ ⟨τ₀, ρ₂, hc₂, hs, ?_⟩
  · -- the returned leaves are the array again, beside the callback's end
    rintro ls' t σ ⟨σo, σΦ, hσ, ho, (⟨v, rfl, hv⟩ | ⟨hst, -⟩)⟩
    · exact Or.inl ⟨v, rfl, σΦ, σo, ResU.CompS.comm hσ, hv, vP_fam_mk hn ho⟩
    · exact Or.inr ⟨σΦ, σo, ResU.CompS.comm hσ, hst, vP_fam_mk hn ho⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ρm σ' hm' hcm
  have e : (fun ls₀ => vC true A ls₀ (δ.extend x α)) = (fun ls₀ => vC true A ls₀ δ) :=
    funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
  have hmut' : vP (VTy.sliceMut (.var x) A) ls₁ (δ.extend x α) (Val.arr ℓ n) ρm := by
    refine vP_fam_mk hn (sepRange_mono' (fun k σ h => ?_) hm')
    refine ⟨α, interp_ext_self δ x α, k, pure_sep_mk rfl ?_⟩
    show ptoMutS k α ls₁ (fun ls₀ => vC true A ls₀ (δ.extend x α)) σ
    rw [e]; exact h
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hcb := (hvf ls₁ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂))
    (Val.arr ℓ n) ρm σ' hmut' hcm
  rw [cC_effOf (hS := hS.divB), hS.tab_extend δ α] at hcb
  refine ewp_end hA _ ?_ (fun ls'' t ρ'' hst harg => Or.inr ⟨hst, harg⟩) hcb
  rintro ls'' v'' ρ'' ⟨α', hα', hBδ', -⟩
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  exact Or.inl ⟨v'', rfl, by rw [vC_extend_of_not_free hfree₂] at hBδ'; exact hBδ'⟩

/-- **The `Imm` slice borrow at an unwinding row.**  `sliceBorrowI_compatX`'s proof, the `n` Imm
Frames at `wpG` (`wpG_I_frameFam`) around the callback, whose ends are carried along `Ext`.
Its side conditions are non-strict, read at `↓@bδ`.  `[spec §19, §23]` -/
theorem sliceBorrowIU_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {S : Row} {d : Expr}
    (x : LifeVar) (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A)
    (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hdc : closedAt 0 d = true) (hd : SemV Δ Γ d (.lolli (.array A) .unit)) :
    SemV Δ Γ (withborUE d) (sliceBorrowIUTy x Δ.meetOfDom A B S) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  have hdg := semV_dead_closed hdc hd hδ hg
  show wpTS ls (substAll γ (withborUE d)) _ _
  rw [show substAll γ (withborUE d) = .val (withborUV d) from
    psub_closedAt _ γ (withborUE_closed hdc) (Nat.zero_le 0)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp hv₁
  intro vf ρ₂ τ hvf hc₂
  let T := Row.tab S δ
  have hA : T.AbortOnly := hS.abort δ
  have hL : T.Local := Row.tab_local S δ
  refine (cC_effOf S _ ls₁ δ _ τ hS.divB).mpr
    (withborUE_beta (opTable_mono _) hdc (Val.arr ℓ n) (arr_closed ℓ n) vf ?_)
  let Fr : List SRec → WProp := fun ls => vP (.array A) ls δ (Val.arr ℓ n)
  let Q₁ : List SRec → Val → WProp := fun ls v => vP B ls δ v
  refine ewp_unwind T hA hL (Row.tab_zero hS.nz δ) _ _ Fr
    (Qd := fun ls v => vP .unit ls δ v)
    (fun _ _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, noOwn_empty⟩)
    (fun ls => fin_run hdc (arr_closed ℓ n) hdg ls) Q₁ _ ?_ ?_
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFr⟩
    refine ewp_ret_pair (opTable_mono _) (Val.arr ℓ n) (arr_closed ℓ n) _ v ?_
    exact ⟨Val.arr ℓ n, v, pure_sep_mk rfl ⟨σ₂, σ₁, ResU.CompS.comm hcσ, hFr, hv⟩⟩
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βA, hβA⟩ := hdefa δ hδ
  -- 6.60 at the non-strict side condition: every stratum below `βA`; the frame is
  -- taken at `↓βA`  `[spec §23]`
  have hA' := fun ls' w σ' h =>
    vC_outlivesLe hδ hβA hOa true ls' w σ' h _ (Life.down_sqsubset βA)
  generalize Life.down βA = βA at hA'
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  -- 6.60 at the non-strict side condition: every stratum below `βB`; the frame is
  -- taken at `↓βB`  `[spec §23]`
  have hB := fun ls' w σ' h =>
    vC_outlivesLe hδ hβB hOb true ls' w σ' h _ (Life.down_sqsubset βB)
  generalize Life.down βB = βB at hB
  have hΦ : ∀ ls' t σ, cbEnds T B δ ls' t σ → BoLo.Outlives σ βB := by
    rintro ls' t σ (⟨v, -, hv⟩ | ⟨-, n, i, en, v, hT, hPA⟩)
    · exact hB ls' v σ hv
    · exact hS.out δ βB n i en hT ls' v σ hPA
  have hΦext : ∀ ls₁ ls₂ t σ, Ext ls₁ ls₂ σ → cbEnds T B δ ls₁ t σ → cbEnds T B δ ls₂ t σ := by
    rintro ls₁ ls₂ t σ hk (⟨v, rfl, hv⟩ | ⟨hst, n, i, en, v, hT, hPA⟩)
    · exact Or.inl ⟨v, rfl, vC_local true B hk hv⟩
    · exact Or.inr ⟨opTable_ext hA hL hk hst, n, i, en, v, hT,
        (hL n i en hT ls₁ ls₂ v σ hk).1 hPA⟩
  refine (ewp_abortive (Table.withFr_abortive (opTable_abortive hA) Fr)).mpr ?_
  refine wpG_mono (fun ls' t σ ht => ?_)
    (wpG_I_frameFam A δ βA (fun ls' w σ h => hA' ls' w σ h) (admWf_of_vScoped hsc hδ) _
      (cbEnds T B δ) βB hΦ hΦext n.toNat ℓ ls₁ τ ⟨τ₀, ρ₂, hc₂, hs, ?_⟩)
  · obtain ⟨σo, σΦ, hσ, ho, (⟨v, rfl, hv⟩ | ⟨hst, -⟩)⟩ := ht
    · exact Or.inl ⟨v, rfl, σΦ, σo, ResU.CompS.comm hσ, hv, vP_fam_mk hn ho⟩
    · exact Or.inr ⟨σΦ, σo, ResU.CompS.comm hσ, hst, vP_fam_mk hn ho⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ls' hext ρm σ' hm' hcm
  have himm' : vP (.arrayImm (.var x) A) ls' (δ.extend x α) (Val.arr ℓ n) ρm :=
    vP_fam_mk hn (sepRange_mono' (fun k σ h => immLeaf_to_vP hfree₁ h) hm')
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hcb := (hvf ls' hext α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂))
    (Val.arr ℓ n) ρm σ' himm' hcm
  rw [cC_effOf (hS := hS.divB), hS.tab_extend δ α] at hcb
  refine ewp_end hA _ ?_ (fun ls'' t ρ'' hst harg => Or.inr ⟨hst, harg⟩) hcb
  rintro ls'' v'' ρ'' ⟨α', hα', hBδ', -⟩
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  exact Or.inl ⟨v'', rfl, by rw [vC_extend_of_not_free hfree₂] at hBδ'; exact hBδ'⟩

end BoCa.Fig16.LogRel.Core

end
