import HandleSpike.Handle
import HandleSpike.Counter
import HandleSpike.Stack

/-!
# Spike (#792): the cancel branch at an ambient cancel relation

The change: `contShareT`'s cancel clause owes the unwinding at a **cancel relation fixed below every
handler** (`cerwpT (opTableT Tc) Qc Fc`, the table finalisers' operations reach, the cancel's
answer, its base) instead of at `Ψ`, the stopper's own continuation relation. `contShareC` is
`contShareT` with that one clause changed; `opTableC Tc Qc Fc T` is `opTableT T` at `contShareC`.
`twp`, `EndT` and `cerwpT` are unchanged: `cerwpT` is read at the table `opTableC Tc Qc Fc T`.

With it, `[handle]` holds for every handler, forwarding cancellable operations included
(`cerwpC_handle`, no restriction on forwarded entries): a forwarded stop's cancel branch is owed at
the same relation inside and outside the handler, of the same unwinding (`dead_hndK`). The clause
receives `κ`'s cancel at the cancel relation, not under the handler (`KapC`).
`Counter.lean`'s program passes (`fixed_counter`).
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
open BoCa.Fig16.Tree.Wp.SchedProgs (cerwpPostT_down compS_empty_left_eq cerwpT_det)
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE freeE)

/-- **`contShareT` with the cancel branch at `Ψc`**, at the frame condition over the cancel's
base `Fc`. -/
def contShareC (en : OpEntT) (F Fc : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (K : Kont) (v : Val) (Ψ Ψc : ContT) : TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ →
    RecsRR w'.Θ O O' →
    (∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → Ψ (fdAt en v F O') w' O' k' ls' (K.plug (.val a)) σ') ∧
    (en.q ≠ .lin → en.fin = true → ∀ k', k' < k → Ψc (fdAt en v Fc O') w' O' k' ls'
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ')

/-- `opTableT T` at `contShareC`, the cancel owed at `cerwpT (opTableT Tc) Qc Fc`. -/
def opTableC (Tc : OpTabT) (Qc : TPostV) (Fc : TFrame) (T : OpTabT) : TableT :=
  fun F k w ls O t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntT),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.abort = false ∧ en.oc w O ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧
      en.PA k w ls v ρa ∧
      contShareC en F Fc k w ls O K v Ψ (cerwpTC (ℍ := ℍ) (opTableT Tc) Qc Fc k) ρk

theorem opTableC_local (Tc : OpTabT) (Qc : TPostV) (Fc : TFrame) (T : OpTabT) :
    (opTableC (ℍ := ℍ) Tc Qc Fc T).Local := by
  intro F k w ls O t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu, hcont⟩ := h
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu,
    fun w' ρ' ls' O' hE hr hx hO =>
    ⟨fun k' hk a σ σ' hB hcσ =>
      hΨ _ _ _ k' hk _ _ _ ((hcont w' ρ' ls' O' hE hr hx hO).1 k' hk a σ σ' hB hcσ),
      (hcont w' ρ' ls' O' hE hr hx hO).2⟩⟩

theorem cerwpPostC_down {Tc : OpTabT} {Qc : TPostV} {Fc : TFrame} {T : OpTabT} {Q : TPostV}
    (hQ : Q.Down) {Ψ : ContT} {F : TFrame}
    (hPA : ∀ m i en, T m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ) :
    (cerwpPostT (opTableC (ℍ := ℍ) Tc Qc Fc T) Q Ψ F).Down := by
  intro k w ls O t ρ h
  rcases h with ⟨v, hv, hq⟩ | ⟨K, m, i, v, en, ht, hK, hT, ha, hoc, ρa, ρk, hc, hA, hsh⟩
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ _ _ hq⟩
  · refine Or.inr ⟨K, m, i, v, en, ht, hK, hT, ha, hoc, ρa, ρk, hc, hPA m i en hT _ _ _ _ _ hA,
      hsh.1, fun w' ρ' ls' O' hE hr hx hO => ⟨fun k' hk' a σ σ' hB hcσ =>
        (hsh.2 w' ρ' ls' O' hE hr hx hO).1 k' (by omega) a σ σ' hB hcσ,
        fun hq hf k' hk' => ?_⟩⟩
    have h₁ := (hsh.2 w' ρ' ls' O' hE hr hx hO).2 hq hf k' (by omega)
    simp only [cerwpTC, show k' < k + 1 by omega, show k' < k by omega, if_true] at h₁ ⊢
    exact h₁

/-! ### The interface -/

/-- `KapT` with `κ`'s cancel at the cancel relation, not under the handler. -/
def KapC (Tc : OpTabT) (Qc : TPostV) (Fc : TFrame) (To : OpTabT) (Qout : TPostV) (Fbo : TFrame)
    (M : BoCa.Loc → Prop) (en : OpEntT) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v κ : Val) : TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧ (∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K))
    (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    ∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → ∀ F' : TFrame, F'.Mono → (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc To) Qout Fbo F' k' w' ls' O'
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val a)) σ') ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    en.q ≠ .lin → en.fin = true → ∀ k', k' < k → ∀ F' : TFrame, F'.Mono →
      (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpT (ℍ := ℍ) (opTableT Tc) Qc Fc F' k' w' ls' O' (.app κ.1 (.val (Val.inj₂ .unit))) ρ'

def RetC (Tc : OpTabT) (Qc : TPostV) (Fc : TFrame) (To : OpTabT) (Qin Qout : TPostV)
    (Fbo : TFrame) (hr : Val) : Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v : Val) (ρ : TRes w.K), F.Mono →
    (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) → Qin k w ls O v ρ →
    cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc To) Qout Fbo F k w ls O (.app (.val hr) (.val v)) ρ

def ClauseC (Tc : OpTabT) (Qc : TPostV) (Fc : TFrame) (To : OpTabT) (Qout : TPostV)
    (Fbo : TFrame) (en : OpEntT) (c : Val) : Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v κ : Val) (ρ : TRes w.K), F.Mono →
    en.oc w O → (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
    (∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧ en.PA k w ls v ρa ∧
      KapC (ℍ := ℍ) Tc Qc Fc To Qout Fbo (recMask O) en k w ls O v κ ρk) →
    cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc To) Qout Fbo F k w ls O
      (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- **`HandleOKT` at the changed share, with no restriction on forwarded entries.** The cancel
relation's answer and table's `PA` are downward closed, and its base is met by every valid frame. -/
def HandleOKC (Tc : OpTabT) (Qc : TPostV) (Fc : TFrame) (T To : OpTabT) (n₀ : UInt32)
    (qs hr hs : Val) (Qin Qout : TPostV) (Fbo : TFrame) : Prop :=
  (∀ m i en, m ≠ n₀ → T m i = some en → To m i = some en) ∧
  (∀ i en, T n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag) ∧
  (∀ m i en, T m i = some en → ∀ v w O ρf, en.fd v w O ρf ↔ fdJoinT v w O ρf) ∧
  Qout.Down ∧
  (∀ m i en, To m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ) ∧
  Qc.Down ∧
  (∀ m i en, Tc m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ) ∧
  (∀ w ρf, ResUT.Valid ρf → Fc w ρf) ∧
  RetC (ℍ := ℍ) Tc Qc Fc To Qin Qout Fbo hr ∧
  (∀ i en, T n₀ i = some en →
    ∃ c, clauseAt hs.1 i.toNat = some c ∧ ClauseC (ℍ := ℍ) Tc Qc Fc To Qout Fbo en c)

/-! ### `[handle]` -/

/-- **`[handle]` for every handler at the changed share**, forwarding cancellable operations
included, by induction on the index. -/
theorem cerwpC_handle {Tc : OpTabT} {Qc : TPostV} {Fc : TFrame} {T To : OpTabT} {n₀ : UInt32}
    {qs hr hs : Val} {Qin Qout : TPostV} {Fbo : TFrame}
    (hOK : HandleOKC (ℍ := ℍ) Tc Qc Fc T To n₀ qs hr hs Qin Qout Fbo) (hFbo : Fbo.Mono) :
    ∀ (n : Nat) (M : BoCa.Loc → Prop) (F Fb Fe : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K), F.Mono →
      (∀ w' ρf, F w' ρf → fdMask M w' ρf) → (∀ x, recMask O x → M x) →
      (∀ w' ρf, ResUT.Valid ρf → Fb w' ρf) → (∀ w' ρf, fdMask M w' ρf → Fe w' ρf) →
      cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc T) Qin Fb Fe n w ls O e ρ →
      cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc To) Qout Fbo F n w ls O
        (hndE (hndVal n₀ qs hr hs) e) ρ := by
  obtain ⟨hfw, htag, hfd, hQd, hPA, hQc, hPAc, hFc, hret, hop⟩ := hOK
  have hPd : ∀ Ψ : ContT, (cerwpPostT (opTableC (ℍ := ℍ) Tc Qc Fc To) Qout Ψ Fbo).Down :=
    fun _ => cerwpPostC_down hQd hPA
  have hPc : ∀ Ψ : ContT, (cerwpPostT (opTableT Tc) Qc Ψ Fc).Down :=
    fun _ => cerwpPostT_down hQc hPAc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M F Fb Fe w ls O e ρ hFm hFM hOM hFb hFe h
  rw [cerwpT_eq] at h ⊢
  have hFe₀ : ∀ (Fx : TFrame), (∀ w' ρf, ResUT.Valid ρf → Fx w' ρf) →
      ∀ (m i : UInt32) (en : OpEntT), T m i = some en → ∀ (v : Val) (w'' : TWd)
      (O'' : List (FrameRecT w''.K)) w₃ ρf, fdMask (recMask O'') w₃ ρf → fdAt en v Fx O'' w₃ ρf :=
    fun Fx hFx m i en hT v w'' O'' w₃ ρf hf => ⟨hFx w₃ ρf hf.1,
      fun O₃ hO₃ => (hfd m i en hT v w₃ O₃ ρf).mpr (fdMask_le (fun x hx =>
        (recMask_rr hO₃ x).mpr hx) hf)⟩
  have hFe' : ∀ (Fx : TFrame), (∀ w' ρf, ResUT.Valid ρf → Fx w' ρf) →
      ∀ (m i : UInt32) (en : OpEntT), T m i = some en → ∀ (v : Val) (w' : TWd)
      (O' : List (FrameRecT w'.K)) (w'' : TWd) (O'' : List (FrameRecT w''.K)),
      RecsRR w''.Θ O' O'' → ∀ w₃ ρf, fdMask (recMask O') w₃ ρf → fdAt en v Fx O'' w₃ ρf :=
    fun Fx hFx m i en hT v w' O' w'' O'' hO w₃ ρf hf => hFe₀ Fx hFx m i en hT v w'' O'' w₃ ρf
      (fdMask_le (fun x hx => (recMask_rr hO x).mpr hx) hf)
  show twp (ℍ := ℍ) F _ n w ls O ((hndK (hndVal n₀ qs hr hs)).plug e) ρ
  refine twp_bind_fdAt hFm (fun w ρf hf => hFe w ρf (hFM w ρf hf)) (hndK (hndVal n₀ qs hr hs))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2.mono hOM) h
    (fun k hk w' ls' O' t ρ' hcov' _ hls' hO' ht => ?_)
  have hF'm : (F.and (fdMask (recMask O'))).Mono := TFrame.and_mono hFm (fdMask_mono _)
  have hF'M : ∀ w'' ρf, (F.and (fdMask (recMask O'))) w'' ρf → fdMask (recMask O') w'' ρf :=
    fun _ _ hf => hf.2
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · refine twpAt_of_twp (twp_det (hPd _)
      (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole) ?_)
    exact cerwpT_unfold_at (opTableC_local _ _ _ _) hk
      (hret _ k w' ls' O' v ρ' hF'm hF'M hcov' hls' hO' hv)
  obtain ⟨K₁, m, i, v, en, rfl, hK₁, hTe, ha, hoc, ρa, ρk, hcak, hA, hsh⟩ := ht
  by_cases hm : m = n₀
  swap
  · -- an operation of another name passes outward, its cancel branch unchanged
    have hTo := hfw m i en hm hTe
    have hK : ((hndK (hndVal n₀ qs hr hs)).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
    have e₁ : ∀ x, (hndK (hndVal n₀ qs hr hs)).plug (K₁.plug x) =
        ((hndK (hndVal n₀ qs hr hs)).comp K₁).plug x := fun x => (Kont.plug_comp _ _ _).symm
    rw [e₁]
    refine twpAt_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr
      ⟨(hndK (hndVal n₀ qs hr hs)).comp K₁, m, i, v, en, rfl, hK, hTo, ha, hoc, ρa, ρk, hcak, hA,
        hsh.1, fun w'' ρk' ls'' O'' hE hr' hx hO => ⟨fun k' hk' a σ σ' hB hcσ => ?_,
        fun hq hf k' hk' => ?_⟩⟩)
    · have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).1 k' hk' a σ σ' hB hcσ
      simp only [cerwpTC, show k' < n by omega, if_true] at h₁ ⊢
      rw [← e₁]
      refine cerwpT_frameCond_rel (F := Fbo.and (fdMask (recMask O'')))
        (fun w₀ O₀ ρf hO₀ hf => ⟨hf.1, fdMask_le (fun x hx => (recMask_rr hO₀ x).mp hx)
          ((hfd m i en hTe v w₀ O₀ ρf).mp (hf.2 O₀ hO₀))⟩) ?_
      exact ih k' (by omega) (recMask O'') (Fbo.and (fdMask (recMask O''))) Fb
        (fdAt en v Fb O'') w'' ls'' O'' _ σ' (TFrame.and_mono hFbo (fdMask_mono _))
        (fun _ _ hf => hf.2) (fun _ hx => hx) hFb (hFe₀ Fb hFb m i en hTe v w'' O'') h₁
    · have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).2 hq hf k' hk'
      rwa [dead_comp, dead_hndK]
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
      cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc To) Qout Fbo F'' k' w'' ls'' O''
        (hndE (hndVal m qs hr hs) (K₁.plug (.val a))) σ' := by
    intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
    have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).1 k' hk' a σ σ' hB hcσ
    simp only [cerwpTC, show k' < n by omega, if_true] at h₁
    exact ih k' (by omega) (recMask O') F'' Fb (fdAt en v Fb O'') w'' ls'' O'' _ σ' hF''m
      hF''M (fun x hx => (recMask_rr hO x).mpr hx) hFb (hFe' Fb hFb m i en hTe v w' O' w'' O'' hO) h₁
  -- the cancel: the share's unwinding at the cancel relation, no induction
  have hcan : ∀ (w'' : TWd) (ρk' : TRes w''.K) (ls'' : List (SRecT w''.K))
      (O'' : List (FrameRecT w''.K)), w'.Ext w'' ρk → RRw (w := w') (w' := w'') ρk ρk' →
      KeepRel w''.Θ ls' ls'' ρk → RecsRR w''.Θ O' O'' → en.q ≠ .lin → en.fin = true →
      ∀ k', k' < k → ∀ F'' : TFrame, (∀ w₃ ρf, F'' w₃ ρf → fdMask (recMask O') w₃ ρf) →
      twp (ℍ := ℍ) F'' (cerwpPostT (opTableT Tc) Qc (cerwpTC (ℍ := ℍ) (opTableT Tc) Qc Fc k') Fc)
        k' w'' ls'' O'' (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))) ρk' := by
    intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''M
    have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).2 hq hf k' hk'
    simp only [cerwpTC, hk', if_true] at h₁
    rw [cerwpT_eq] at h₁
    exact twp_frameCond (fun w₃ ρf hf => hFe' Fc hFc m i en hTe v w' O' w'' O'' hO w₃ ρf
      (hF''M w₃ ρf hf)) h₁
  have hPdk := hPd (cerwpTC (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc To) Qout Fbo n)
  rw [htag i en hTe ha, kappaAt_tag]
  cases hqq : en.q with
  | unr =>
      refine cerwpT_unfold_at (opTableC_local _ _ _ _) hk (hcl _ k w' ls' O' v
        ⟨kappa (hndVal m qs hr hs) K₁, by unfold kappa; exact .lam⟩ ρ' hF'm hoc hF'M hcov' hls'
        hO' ⟨ρa, ρk, hcak, hA, ⟨hsh.1, ?_, ?_⟩⟩)
      · intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
        have h₂ := hres w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
        rw [cerwpT_eq] at h₂ ⊢
        exact twp_kappa_resume (hPd _) _ K₁ a h₂
      · intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' _ hF''M
        rw [cerwpT_eq]
        exact twp_kappa_cancel (hPc _) _ K₁
          (hcan w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''M)
  | lin | cancel =>
      refine twp_kappaCell hPdk _ _ K₁ (.appR (.val c) (.pairR v .hole)) fun l ρ₁ hc₁ => ?_
      obtain ⟨x, hx₂, hx₁⟩ :=
        (ResUT.CompS.assoc ρa ρk (ResUT.single l (CellUT.ownOf Val.unit)) ρ₁).mpr
          ⟨ρ', hcak, hc₁⟩
      have hρkl : ρk.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hx₂.1)
      have hxl : x.get l = some (CellUT.ownOf Val.unit) := by
        rw [ResUT.Comp.get_of_left_none hx₂ hρkl, ResUT.single_get_self]
      have hxd : x.del l = ρk := (eq_del_of_compS_single (ResUT.CompS.comm hx₂)).symm
      refine cerwpT_unfold_at (opTableC_local _ _ _ _) hk (hcl _ k w' ls' O' v
        ⟨kappaC _ l (hndVal m qs hr hs) K₁, isVal_kappaC _ l _ K₁⟩ ρ₁ hF'm hoc hF'M
        (covR_compS_own hc₁ hcov') hls' hO'
        ⟨ρa, x, hx₁, hA, ⟨fun hu => (by rw [hqq] at hu; cases hu), ?_, ?_⟩⟩)
      swap
      · intro w'' ρx' ls'' O'' hE hr' hxF hO hq hf k' hk' F'' _ hF''M
        first
        | exact absurd hqq hq
        | have hρx'l := RR.own_fwd hr' hxl
          have hrk : RRw (w := w') (w' := w'') ρk (ρx'.del l) := hxd ▸ RR.del hr' l
          rw [cerwpT_eq]
          exact twp_kappaC_cancel (hPc _) l _ K₁ (compS_single_del hρx'l)
            (hcan w'' (ρx'.del l) ls'' O'' (hE.of_compS_left hx₂) hrk
              (hxF.of_compS_left hx₂) hO hq hf k' hk' F'' hF''M)
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

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.HandleSpike
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp.SchedProgs (cerwpPostT_down compS_empty_left_eq cerwpT_det)
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE hndVal ccatchE)

/-- A stop at the changed share, at every extension of the world. -/
theorem cerwpC_perform {Tc : OpTabT} {Qc : TPostV} {Fc : TFrame} {T : OpTabT} {Q : TPostV}
    {Fb F : TFrame} (K : Kont) {m i : UInt32} {v : Val} {en : OpEntT}
    (hK : K.HasHnd m = false) (hT : T m i = some en) (ha : en.abort = false) {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K) (ls₀ : List (SRecT w₀.K)) (O₀ : List (FrameRecT w₀.K)),
      w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → SRecsRR w₀.Θ ls ls₀ → RecsRR w₀.Θ O O₀ →
      en.oc w₀ O₀ ∧ ∃ ρa ρk : TRes w₀.K, ResUT.CompS ρa ρk ρ₀ ∧ en.PA n w₀ ls₀ v ρa ∧
        contShareC en Fb Fc n w₀ ls₀ O₀ K v
          (cerwpTC (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc T) Q Fb n)
          (cerwpTC (ℍ := ℍ) (opTableT Tc) Qc Fc n) ρk) :
    cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc T) Q Fb F n w ls O
      (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [cerwpT_eq]
  refine twp_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK)
    fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => Or.inr ?_
  obtain ⟨hoc, ρa, ρk, hc, hA, hs⟩ := h w₀ ρ₀ ls₀ O₀ hE hr hl hO
  exact ⟨K, m, i, v, en, rfl, hK, hT, ha, hoc, ρa, ρk, hc, hA, hs⟩

namespace FixedCounter
open BoCa.Fig16.Tree.Wp.HandleSpike.Counter
open BoCa.Fig16.Tree.Wp.HandleSpike.Inst (valid_mono)

/-- The cancel relation: no operations, answer `()` owning nothing. -/
abbrev Tc : OpTabT := OpTabT.empty
abbrev Qc : TPostV := Qin
abbrev Fc : TFrame := fun _ ρf => ResUT.Valid ρf

theorem inner_okC (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc T) Qin Fb F n w ls [] e PMap.empty := by
  show cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc T) Qin Fb F n w ls [] (Kont.hole.plug e)
    PMap.empty
  refine cerwpC_perform .hole rfl (show T nB 0 = some enF by simp [T]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨rfl, PMap.empty, PMap.empty, ResUT.compS_empty_right _, ⟨rfl, rfl⟩, ?_⟩
  unfold contShareC
  refine ⟨fun h => absurd h (by simp [enF]), ?_⟩
  intro w' ρ' ls' O' _ hr' _ hO'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ _ k' hk' => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := RR.of_empty hr'
    obtain rfl := compS_empty_left_eq hcσ
    cases hO'
    simp only [cerwpTC, hk', if_true]
    exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
      cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩
  · obtain rfl := RR.of_empty hr'
    cases hO'
    simp only [cerwpTC, hk', if_true]
    refine cerwpT_det (cerwpPostT_down Qin_down (fun _ _ _ h => by simp [OpTabT.empty] at h))
      (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole) ?_
    exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
      cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

theorem handler_okC : HandleOKC (ℍ := ℍ) Tc Qc Fc T T nH qsH retOne hsH Qin Qout
    (fun _ ρf => ResUT.Valid ρf) := by
  refine ⟨fun _ _ _ _ h => h, fun i en h => ?_, fun m i en h v w O ρf => ?_, Qout_down,
    T_PA_down, Qin_down, fun _ _ _ h => by simp [OpTabT.empty] at h, fun _ _ hv => hv, ?_, fun i en h => ?_⟩
  · obtain ⟨h, -⟩ := T_some h; cases h
  · obtain ⟨-, -, rfl⟩ := T_some h; exact Iff.rfl
  · intro F k w ls O v ρ _ _ _ _ _ ⟨_, hO, hρ⟩
    subst hO; subst hρ
    refine cerwpT_det (cerwpPostC_down Qout_down T_PA_down)
      (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
    exact cerwpT_val (v := Val.i32 1) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
      cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩
  · obtain ⟨h, -⟩ := T_some h; cases h

/-- **`Counter.lean`'s program at the changed share**: `hnd H (perform (nB, 0, ()))`, the
cancellable `nB` forwarded, at every index. -/
theorem fixed_counter (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableC (ℍ := ℍ) Tc Qc Fc T) Qout (fun _ ρf => ResUT.Valid ρf)
      (fdMask fun _ => False) n w ls [] (hndE H e) PMap.empty :=
  cerwpC_handle handler_okC valid_mono n _ (fdMask fun _ => False) (fun _ ρf => ResUT.Valid ρf)
    (fdMask fun _ => False) w ls [] e PMap.empty (fdMask_mono _) (fun _ _ h => h)
    (fun x hx => by simp [recMask] at hx) (fun _ _ hv => hv) (fun _ _ h => h)
    (inner_okC n _ _ w ls)

end FixedCounter

end BoCa.Fig16.Tree.Wp.HandleSpike

end
