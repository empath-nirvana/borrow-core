import Core.TreeHandle
import Core.TreeSchedProgs

/-!
# Spike (#792): `[handle]` at `cerwpT` for a handler at an outer table

`cerwpT_schedHandle` (`Core/TreeHandle.lean`) is `[handle]` for a handler whose clauses run at the
empty table and whose tasks perform only its own operations. Here the handler's clauses, return
clause and resumed continuations run at an outer table `To`, and operations of other names pass
outward to `To` (forwarding). The conclusion is `cerwpT` at `To`, so the result is again a handled
computation of the same shape, and a handler stack is the theorem applied once per handler
(`cerwpT_handleStack`).

The proof is `cerwpT_schedHandle_le`'s, by induction on the index, with three changes:

* the bind is `twp_bind_fdAt`: the continuation after the handled run's segment is asked only at
  the world the segment ended at (`twpAt`), so a forwarded stop is a stop of `To` there, with no
  stability of the entry's `PA` along world extension;
* a forwarded stop's resume is the induction hypothesis at the frame condition
  `Fbo ∧ fdMask (recMask O″)`, read back at `fdAt en v Fbo O″` at the run's own records
  (`cerwpT_frameCond_rel`; `fd` is `fdJoinT`);
* a forwarded stop's **cancel branch** is not carried: `contShareT` owes it at the stopper's own
  continuation relation (table `T`, answer `Qin`), while the unwinding runs with the handler's
  frame removed (`Kont.dead`), so the outer stop owes it at `To` and `Qout`. `HandleOKT` asks that
  forwarded entries have no cancel branch (`en.q = .lin ∨ en.fin = false`); `Counter.lean` shows
  the conclusion fails without it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.HandleSpike
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp.SchedProgs (cerwpPostT_down)
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE freeE)

/-! ### `twp` at the run's own world -/

/-- `twp` started at the run's own world only. -/
def twpAt (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K) : Prop :=
  ∀ (ρf fρ : TRes w.K) (ps psF : List (FrameRecT w.K)) (μ : Heap),
    F w ρf → ResUT.Hash ρf ρ → ResUT.CompS ρf ρ fρ → SplitT ps O psF →
    RecInv w fρ ps ls → WInv w fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' → Final (ℍ := ℍ) μ' e' →
      EndT Q (n - j) w ρ O ρf psF μ' e'

theorem twpAt_of_twp {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} (h : twp (ℍ := ℍ) F Q n w ls O e ρ) :
    twpAt (ℍ := ℍ) F Q n w ls O e ρ :=
  fun ρf fρ ps psF μ hF hf hc hS hR hI hfd =>
    h w ρ ρf fρ ls O ps psF μ (TWd.Ext.refl _ _) (RR.refl (cov_of_comp hc hI))
      (SRecsRR.refl hR.cov_ls) (RecsRR.refl fun r hr => hR.cov_ps r (hS.left r hr)) hF hf hc hS
      hR hI hfd

/-- A final term in the postcondition at the run's own world. -/
theorem twpAt_here {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : Q n w ls O e ρ) : twpAt (ℍ := ℍ) F Q n w ls O e ρ := by
  intro ρf fρ ps psF μ _ hf hc hS hR hI _ j μ' e' hj hrun _
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  exact ⟨w, ρf, ρ, fρ, psF, ps, O, ls, TWd.Ext.refl _ _, RR.refl (covf_of_comp hc hI),
    RecsRR.refl fun r hr => hR.cov_ps r (hS.right r hr), ResUT.hash_symm hf, hc, hS, hR, hI,
    by simpa using h,
    UpdX.of_rr (WCactus.Ext.refl _) _ (cov_valid hc hI) (RR.refl (cov_of_comp hc hI)),
    NoneAt.of_false (fun x hx => by unfold MaskDiff at hx; tauto) _, InvKept.refl _ _ _⟩

/-- **`twp_bind_fd` with the continuation asked at the segment's end world only.** -/
theorem twp_bind_fdAt {F Fe : TFrame} (hFm : F.Mono) (hFe : ∀ w ρf, F w ρf → Fe w ρf)
    {P Q : TPost} (K : Kont) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hJ : ∀ w₀ ρf, F w₀ ρf → NoneAt (recMask O) ρf)
    (he : twp (ℍ := ℍ) Fe P n w ls O e ρ)
    (hk : ∀ k, k ≤ n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t
      (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' → ResUT.Valid ρ' →
      (∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) →
      (∀ r ∈ O', CovR (sem w'.Θ) w'.K r.R) → P k w' ls' O' t ρ' →
      twpAt (ℍ := ℍ) (F.and (fdMask (recMask O'))) Q k w' ls' O' (K.plug t) ρ') :
    twp (ℍ := ℍ) F Q n w ls O (K.plug e) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' E hj hrun hfin
  have go : ∀ j₁ j₂ μ₁ t, j₁ + j₂ = j → StepsN (ℍ := ℍ) j₁ μ e μ₁ t → Final (ℍ := ℍ) μ₁ t →
      StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E → EndT Q (n - j) w₀ ρ₀ O₀ ρf psF μ' E := by
    intro j₁ j₂ μ₁ t hjj hrun₁ hfin₁ hrun₂
    obtain ⟨w₁, ρf₁, ρ₁, fρ₁, psF₁, ps₁, O₁, ls₁, g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
        g₁₁⟩ := he w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO (hFe _ _ hF) hf hc hS hR hI hfd j₁ μ₁ t
        (by omega) hrun₁ hfin₁
    have hcov : CovR (sem w₁.Θ) w₁.K ρ₁ := cov_of_comp g₄ g₇
    have hJ₀ : NoneAt (recMask O₀) ρf := (hJ w₀ ρf hF).mono fun x hx => (recMask_rr hO x).mpr hx
    have hF₁ : (F.and (fdMask (recMask O₁))) w₁ ρf₁ :=
      ⟨hFm _ _ _ _ g₀ g₁ hF, covf_valid g₄ g₇,
        noneAt_recMask_end g₀.1 (covf_valid hc hI) g₁ hJ₀ g₁₀⟩
    obtain ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, k₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀,
        k₁₁⟩ := hk (n - j₁) (Nat.sub_le _ _) w₁ ls₁ O₁ t ρ₁ hcov (cov_valid g₄ g₇) g₆.cov_ls
        (fun r hr => g₆.cov_ps r (g₅.left r hr)) g₈ ρf₁ fρ₁ ps₁ psF₁ μ₁ hF₁
        (ResUT.hash_symm g₃) g₄ g₅ g₆ g₇ (fd_stepsN hrun₁ hfd) j₂ μ' E (by omega) hrun₂ hfin
    refine ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, g₀.trans g₁ k₀, RRw.trans k₀.1 g₁ k₁,
      g₂.trans k₀.1 k₂, k₃, k₄, k₅, k₆, k₇, ?_, UpdX.trans k₀.1 g₉ k₉, ?_, g₁₁.trans g₉ k₁₁⟩
    · rwa [show n - j₁ - j₂ = n - j by omega] at k₈
    · have hf₂ : NoneAt (MaskDiff (recMask O₀) (recMask O₁)) ρf₂ :=
        g₁₀.rr k₀.1 (covf_valid g₄ g₇) k₁
      exact (hf₂.or k₁₀).mono fun x hx => maskDiff_trans x hx
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    exact go j 0 μ' e' (by omega) hrun' hfin' (.refl _ _)
  · exact go j₁ j₂ μ₁ t hjj hrun₁ hirr hrun₂

/-- **A weaker frame condition at the run's own records**: `cerwpT` reads its present frame
condition only at worlds where its records have a re-reading. -/
theorem cerwpT_frameCond_rel {Tb : TableT} {Q : TPostV} {Fb F F' : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hF : ∀ (w₀ : TWd) (O₀ : List (FrameRecT w₀.K)) ρf, RecsRR w₀.Θ O O₀ → F' w₀ ρf → F w₀ ρf)
    (h : cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ) : cerwpT (ℍ := ℍ) Tb Q Fb F' n w ls O e ρ := by
  rw [cerwpT_eq] at h ⊢
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF'
  exact h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO (hF w₀ O₀ ρf hO hF')

/-! ### The handler's interface at an outer table -/

/-- **`κ` as a clause receives it, at the outer table `To`**: `KapSchedT` with the resumed run at
`cerwpT (opTableT To) Qout Fbo`. -/
def KapT (To : OpTabT) (Qout : TPostV) (Fbo : TFrame) (M : BoCa.Loc → Prop) (en : OpEntT)
    (H : Val) (k : Nat) (w : TWd) (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (v κ : Val) :
    TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧ (∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K))
    (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    ∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → ∀ F' : TFrame, F'.Mono → (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpT (ℍ := ℍ) (opTableT To) Qout Fbo F' k' w' ls' O'
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val a)) σ') ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    en.q ≠ .lin → en.fin = true → ∀ k', k' < k → ∀ F' : TFrame, F'.Mono →
      (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpT (ℍ := ℍ) (opTableT To) Qout Fbo F' k' w' ls' O'
        (hndE H (.app κ.1 (.val (Val.inj₂ .unit)))) ρ'

/-- The return clause at the outer table. -/
def RetT (To : OpTabT) (Qin Qout : TPostV) (Fbo : TFrame) (hr : Val) : Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v : Val) (ρ : TRes w.K), F.Mono →
    (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) → Qin k w ls O v ρ →
    cerwpT (ℍ := ℍ) (opTableT To) Qout Fbo F k w ls O (.app (.val hr) (.val v)) ρ

/-- An operation's clause at the outer table. -/
def ClauseT (To : OpTabT) (H : Val) (Qout : TPostV) (Fbo : TFrame) (en : OpEntT) (c : Val) :
    Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v κ : Val) (ρ : TRes w.K), F.Mono →
    en.oc w O → (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
    (∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧ en.PA k w ls v ρa ∧
      KapT (ℍ := ℍ) To Qout Fbo (recMask O) en H k w ls O v κ ρk) →
    cerwpT (ℍ := ℍ) (opTableT To) Qout Fbo F k w ls O (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- **What a handler `hnd (n₀, (qs, (h_ret, hs)))` between a computation at `T` and an outer table
`To` must satisfy**:

* (forwarding) every operation of `T` of another name is `To`'s, the same entry, and has no cancel
  branch;
* the tags, as `SchedOKT`;
* every entry's `fd` is the join's (`fdJoinT`), both ways;
* `Qout` and `To`'s `PA` are downward closed in the index;
* the return clause and the clauses, at `To`. -/
def HandleOKT (T To : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : TPostV) (Fbo : TFrame) :
    Prop :=
  (∀ m i en, m ≠ n₀ → T m i = some en → To m i = some en ∧ (en.q = .lin ∨ en.fin = false)) ∧
  (∀ i en, T n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag) ∧
  (∀ m i en, T m i = some en → ∀ v w O ρf, en.fd v w O ρf ↔ fdJoinT v w O ρf) ∧
  Qout.Down ∧
  (∀ m i en, To m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ) ∧
  RetT (ℍ := ℍ) To Qin Qout Fbo hr ∧
  (∀ i en, T n₀ i = some en →
    ∃ c, clauseAt hs.1 i.toNat = some c ∧
      ClauseT (ℍ := ℍ) To (hndVal n₀ qs hr hs) Qout Fbo en c)

/-! ### `[handle]` at an outer table -/

/-- **`[handle]` at `cerwpT` for a handler between a computation at `T` and an outer table `To`**,
by induction on the index. As `cerwpT_schedHandle_le`, with the conclusion at `cerwpT` at `To` and
base `Fbo`. A stop at the handler's name runs the clause (`κ` resumed by the induction hypothesis);
a stop of another name is a stop of `To`, its continuation the handler around the inner one,
resumed by the induction hypothesis at `Fbo ∧ fdMask (recMask O″)`. -/
theorem cerwpT_handle {T To : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Qout : TPostV}
    {Fbo : TFrame} (hOK : HandleOKT (ℍ := ℍ) T To n₀ qs hr hs Qin Qout Fbo) (hFbo : Fbo.Mono) :
    ∀ (n : Nat) (M : BoCa.Loc → Prop) (F Fb Fe : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K), F.Mono →
      (∀ w' ρf, F w' ρf → fdMask M w' ρf) → (∀ x, recMask O x → M x) →
      (∀ w' ρf, ResUT.Valid ρf → Fb w' ρf) → (∀ w' ρf, fdMask M w' ρf → Fe w' ρf) →
      cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n w ls O e ρ →
      cerwpT (ℍ := ℍ) (opTableT To) Qout Fbo F n w ls O (hndE (hndVal n₀ qs hr hs) e) ρ := by
  obtain ⟨hfw, htag, hfd, hQd, hPA, hret, hop⟩ := hOK
  have hPd : ∀ Ψ : ContT, (cerwpPostT (opTableT To) Qout Ψ Fbo).Down :=
    fun _ => cerwpPostT_down hQd hPA
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M F Fb Fe w ls O e ρ hFm hFM hOM hFb hFe h
  rw [cerwpT_eq] at h ⊢
  -- the resumed run's present frame condition, met by every frame avoiding the records' masks
  have hFe₀ : ∀ (m i : UInt32) (en : OpEntT), T m i = some en → ∀ (v : Val) (w'' : TWd)
      (O'' : List (FrameRecT w''.K)) w₃ ρf, fdMask (recMask O'') w₃ ρf → fdAt en v Fb O'' w₃ ρf :=
    fun m i en hT v w'' O'' w₃ ρf hf => ⟨hFb w₃ ρf hf.1,
      fun O₃ hO₃ => (hfd m i en hT v w₃ O₃ ρf).mpr (fdMask_le (fun x hx =>
        (recMask_rr hO₃ x).mpr hx) hf)⟩
  have hFe' : ∀ (m i : UInt32) (en : OpEntT), T m i = some en → ∀ (v : Val) (w' : TWd)
      (O' : List (FrameRecT w'.K)) (w'' : TWd) (O'' : List (FrameRecT w''.K)),
      RecsRR w''.Θ O' O'' → ∀ w₃ ρf, fdMask (recMask O') w₃ ρf → fdAt en v Fb O'' w₃ ρf :=
    fun m i en hT v w' O' w'' O'' hO w₃ ρf hf => hFe₀ m i en hT v w'' O'' w₃ ρf
      (fdMask_le (fun x hx => (recMask_rr hO x).mpr hx) hf)
  show twp (ℍ := ℍ) F _ n w ls O ((hndK (hndVal n₀ qs hr hs)).plug e) ρ
  refine twp_bind_fdAt hFm (fun w ρf hf => hFe w ρf (hFM w ρf hf)) (hndK (hndVal n₀ qs hr hs))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2.mono hOM) h
    (fun k hk w' ls' O' t ρ' hcov' _ hls' hO' ht => ?_)
  have hF'm : (F.and (fdMask (recMask O'))).Mono := TFrame.and_mono hFm (fdMask_mono _)
  have hF'M : ∀ w'' ρf, (F.and (fdMask (recMask O'))) w'' ρf → fdMask (recMask O') w'' ρf :=
    fun _ _ hf => hf.2
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · -- `[ret]`
    refine twpAt_of_twp (twp_det (hPd _)
      (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole) ?_)
    exact cerwpT_unfold_at (opTableT_local _) hk
      (hret _ k w' ls' O' v ρ' hF'm hF'M hcov' hls' hO' hv)
  obtain ⟨K₁, m, i, v, en, rfl, hK₁, hTe, ha, hoc, ρa, ρk, hcak, hA, hsh⟩ := ht
  by_cases hm : m = n₀
  swap
  · -- an operation of another name passes outward
    obtain ⟨hTo, hnc⟩ := hfw m i en hm hTe
    have hK : ((hndK (hndVal n₀ qs hr hs)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
    have e₁ : ∀ x, (hndK (hndVal n₀ qs hr hs)).plug (K₁.plug x) =
        ((hndK (hndVal n₀ qs hr hs)).comp K₁).plug x := fun x => (Kont.plug_comp _ _ _).symm
    rw [e₁]
    refine twpAt_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr
      ⟨(hndK (hndVal n₀ qs hr hs)).comp K₁, m, i, v, en, rfl, hK, hTo, ha, hoc, ρa, ρk, hcak, hA,
        hsh.1, fun w'' ρk' ls'' O'' hE hr' hx hO => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
        fun hq hf k' hk' => ?_⟩⟩)
    · have h₁ := contShareT_resume hsh hE hr' hx hO hk' hB hcσ
      simp only [cerwpTC, show k' < n by omega, if_true] at h₁ ⊢
      rw [← e₁]
      refine cerwpT_frameCond_rel (F := Fbo.and (fdMask (recMask O''))) (fun w₀ O₀ ρf hO₀ hf => ⟨hf.1,
        fdMask_le (fun x hx => (recMask_rr hO₀ x).mp hx)
          ((hfd m i en hTe v w₀ O₀ ρf).mp (hf.2 O₀ hO₀))⟩) ?_
      exact ih k' (by omega) (recMask O'') (Fbo.and (fdMask (recMask O''))) Fb
        (fdAt en v Fb O'') w'' ls'' O'' _ σ' (TFrame.and_mono hFbo (fdMask_mono _))
        (fun _ _ hf => hf.2) (fun _ hx => hx) hFb
        (hFe₀ m i en hTe v w'' O'') h₁
    · rcases hnc with hl | hf'
      · exact absurd hl hq
      · rw [hf'] at hf; cases hf
  subst hm
  obtain ⟨c, hc, hcl⟩ := hop i en hTe
  refine twpAt_of_twp (twp_det (hPd _)
    (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_)
  have hres : ∀ (w'' : TWd) (ρk' : TRes w''.K) (ls'' : List (SRecT w''.K))
      (O'' : List (FrameRecT w''.K)), w'.Ext w'' ρk → RRw (w := w') (w' := w'') ρk ρk' →
      KeepRel w''.Θ ls' ls'' ρk → RecsRR w''.Θ O' O'' →
      ∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w''.K), en.PBv v k' w'' ls'' a σ →
      ResUT.CompS ρk' σ σ' → ∀ F'' : TFrame, F''.Mono →
      (∀ w₃ ρf, F'' w₃ ρf → fdMask (recMask O') w₃ ρf) →
      cerwpT (ℍ := ℍ) (opTableT To) Qout Fbo F'' k' w'' ls'' O''
        (hndE (hndVal m qs hr hs) (K₁.plug (.val a))) σ' := by
    intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
    have h₁ := contShareT_resume hsh hE hr' hx hO hk' hB hcσ
    simp only [cerwpTC, show k' < n by omega, if_true] at h₁
    exact ih k' (by omega) (recMask O') F'' Fb (fdAt en v Fb O'') w'' ls'' O'' _ σ' hF''m
      hF''M (fun x hx => (recMask_rr hO x).mpr hx) hFb (hFe' m i en hTe v w' O' w'' O'' hO) h₁
  have hcan : ∀ (w'' : TWd) (ρk' : TRes w''.K) (ls'' : List (SRecT w''.K))
      (O'' : List (FrameRecT w''.K)), w'.Ext w'' ρk → RRw (w := w') (w' := w'') ρk ρk' →
      KeepRel w''.Θ ls' ls'' ρk → RecsRR w''.Θ O' O'' → en.q ≠ .lin → en.fin = true →
      ∀ k', k' < k → ∀ F'' : TFrame, F''.Mono →
      (∀ w₃ ρf, F'' w₃ ρf → fdMask (recMask O') w₃ ρf) →
      cerwpT (ℍ := ℍ) (opTableT To) Qout Fbo F'' k' w'' ls'' O''
        (hndE (hndVal m qs hr hs) (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))))
        ρk' := by
    intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
    have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).2 hq hf k' hk'
    simp only [cerwpTC, show k' < n by omega, if_true] at h₁
    exact ih k' (by omega) (recMask O') F'' Fb (fdAt en v Fb O'') w'' ls'' O'' _ ρk' hF''m
      hF''M (fun x hx => (recMask_rr hO x).mpr hx) hFb (hFe' m i en hTe v w' O' w'' O'' hO) h₁
  have hPdk := hPd (cerwpTC (ℍ := ℍ) (opTableT To) Qout Fbo n)
  rw [htag i en hTe ha, kappaAt_tag]
  cases hqq : en.q with
  | unr =>
      refine cerwpT_unfold_at (opTableT_local _) hk (hcl _ k w' ls' O' v
        ⟨kappa (hndVal m qs hr hs) K₁, by unfold kappa; exact .lam⟩ ρ' hF'm hoc hF'M hcov' hls'
        hO' ⟨ρa, ρk, hcak, hA, ⟨hsh.1, ?_, ?_⟩⟩)
      · intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
        have h₂ := hres w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
        rw [cerwpT_eq] at h₂ ⊢
        exact twp_kappa_resume (hPd _) _ K₁ a h₂
      · intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
        have h₂ := hcan w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
        rw [cerwpT_eq] at h₂ ⊢
        exact twp_kappa_cancel_in (hPd _) _ K₁ (hndK _) h₂
  | lin | cancel =>
      refine twp_kappaCell hPdk _ _ K₁ (.appR (.val c) (.pairR v .hole)) fun l ρ₁ hc₁ => ?_
      obtain ⟨x, hx₂, hx₁⟩ :=
        (ResUT.CompS.assoc ρa ρk (ResUT.single l (CellUT.ownOf Val.unit)) ρ₁).mpr
          ⟨ρ', hcak, hc₁⟩
      have hρkl : ρk.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hx₂.1)
      have hxl : x.get l = some (CellUT.ownOf Val.unit) := by
        rw [ResUT.Comp.get_of_left_none hx₂ hρkl, ResUT.single_get_self]
      have hxd : x.del l = ρk := (eq_del_of_compS_single (ResUT.CompS.comm hx₂)).symm
      refine cerwpT_unfold_at (opTableT_local _) hk (hcl _ k w' ls' O' v
        ⟨kappaC _ l (hndVal m qs hr hs) K₁, isVal_kappaC _ l _ K₁⟩ ρ₁ hF'm hoc hF'M
        (covR_compS_own hc₁ hcov') hls' hO'
        ⟨ρa, x, hx₁, hA, ⟨fun hu => (by rw [hqq] at hu; cases hu), ?_, ?_⟩⟩)
      swap
      · intro w'' ρx' ls'' O'' hE hr' hxF hO hq hf k' hk' F'' hF''m hF''M
        first
        | exact absurd hqq hq
        | have hρx'l := RR.own_fwd hr' hxl
          have hrk : RRw (w := w') (w' := w'') ρk (ρx'.del l) := hxd ▸ RR.del hr' l
          have h₂ := hcan w'' (ρx'.del l) ls'' O'' (hE.of_compS_left hx₂) hrk
            (hxF.of_compS_left hx₂) hO hq hf k' hk' F'' hF''m hF''M
          rw [cerwpT_eq] at h₂ ⊢
          exact twp_kappaC_cancel_in (hPd _) l _ K₁ (hndK _) (compS_single_del hρx'l) h₂
      intro w'' ρx' ls'' O'' hE hr' hxF hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
      have hρx'l := RR.own_fwd hr' hxl
      have hrk : RRw (w := w') (w' := w'') ρk (ρx'.del l) := hxd ▸ RR.del hr' l
      obtain ⟨z, hz, hzσ⟩ :=
        (ResUT.CompS.assoc (ResUT.single l (CellUT.ownOf Val.unit)) (ρx'.del l) σ σ').mpr
          ⟨ρx', compS_single_del hρx'l, hcσ⟩
      have h₂ := hres w'' (ρx'.del l) ls'' O'' (hE.of_compS_left hx₂) hrk
        (hxF.of_compS_left hx₂) hO k' hk' a σ z hB hz F'' hF''m hF''M
      rw [cerwpT_eq] at h₂ ⊢
      exact twp_kappaC_resume (hPd _) _ l _ K₁ a hzσ h₂

end BoCa.Fig16.Tree.Wp.HandleSpike

end
