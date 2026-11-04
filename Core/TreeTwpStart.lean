import Core.TreeWpEff

/-!
# `twp`'s start reads `KeepRel`: the Kripke rule along it, and D13's resume from it  `[spec §62]`

Spike (#781). `twp` starts at every list keeping the re-readings of the records of the run's list
its resource reads (`KeepRel`), in place of a re-reading of the whole list.

* **`cerwpT` is Kripke along `KeepRel`** (`cerwpT_keepKripke`): `KeepKripkeRun`, the property
  branch `si-782`'s `Obs.cerwpT_not_keepKripke` refutes at the whole-list start, holds.
* **D13's resume from a whole-list resume** (`contShareT_of_rr`): a share that resumes at every
  re-reading of its stop list (the condition before D13) resumes at every list keeping the records
  it reads, by `cerwpT_kripke`, for an entry whose answers hold nothing and do not read the list,
  wherever a re-reading of the stop list exists at the resume world (`hex`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.TwpStart
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont raiseE cancelVal ccatchE)

/-- `si-782`'s property, verbatim: a bare run is Kripke along `KeepRel`. -/
def KeepKripkeRun : Prop :=
  ∀ (Tb : TableT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w w' : TWd) (ls : List (SRecT w.K))
    (ls' : List (SRecT w'.K)) (O : List (FrameRecT w.K)) (O' : List (FrameRecT w'.K)) (e : Expr)
    (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' →
    KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' → CovR (sem w.Θ) w.K ρ →
    cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ → cerwpT (ℍ := ℍ) Tb Q Fb F n w' ls' O' e ρ'

/-- **A bare run is Kripke along `KeepRel`**, at `twp`'s `KeepRel` start. -/
theorem cerwpT_keepKripke : KeepKripkeRun (ℍ := ℍ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE hr hl hO _ h => cerwpT_kripke hE hr hl hO h

/-! ### D13 from the whole-list resume -/

theorem compS_empty_right_eq_tw {K : WCactus} {a b : TRes K} (h : ResUT.CompS a PMap.empty b) :
    b = a :=
  ResUT.CompS.functional h (ResUT.compS_empty_right a)

/-- `KeepRel` read from a re-reading of its list, at the same world. -/
theorem KeepRel.of_rr_back {K K' : WCactus} {Θ' : CodeTy} {ls : List (SRecT K)}
    {lsR ls' : List (SRecT K')} {ρ : TRes K} {ρ' : TRes K'} (hl : SRecsRR Θ' ls lsR)
    (hr : RR (sem Θ') ρ ρ') (h : KeepRel Θ' ls ls' ρ) : KeepRel Θ' lsR ls' ρ' := by
  intro rR hrR hrel
  obtain ⟨r, hr₀, e⟩ := hl.mem_back hrR
  obtain ⟨r', hr', e'⟩ := h r hr₀ ((RelFT.rr_iff e hr).mpr hrel)
  obtain rfl := RecRR.func e e'
  exact ⟨rR, hr', RecRR.refl (RR.cov e.2.2.2)⟩

theorem RecsRR.cov_right {K K' : WCactus} {Θ' : CodeTy} {O : List (FrameRecT K)}
    {O' : List (FrameRecT K')} (h : RecsRR Θ' O O') : ∀ r ∈ O', CovR (sem Θ') K' r.R := by
  intro r hr
  obtain ⟨_, -, e⟩ := forall₂_mem_right h hr
  exact RR.cov e.2.2.2

/-- **The share before D13**: `contShareT` with the resume list a re-reading of the stop list. -/
def contShareRR (en : OpEntT) (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (K : Kont) (v : Val) (Ψ : ContT) : TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → SRecsRR w'.Θ ls ls' →
    RecsRR w'.Θ O O' →
    (∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → Ψ (fdAt en v F O') w' O' k' ls'
        (K.plug (.val a)) σ') ∧
    (en.q ≠ .lin → en.fin = true → ∀ k', k' < k → Ψ (fdAt en v F O') w' O' k' ls'
      (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ')

/-- `cerwpTC` is Kripke along `KeepRel` at one world. -/
theorem cerwpTC_keep {Tb : TableT} {Q : TPostV} {Fb : TFrame} {N : Nat} {F' : TFrame} {w : TWd}
    {O : List (FrameRecT w.K)} {k' : Nat} {ls ls' : List (SRecT w.K)} {e : Expr}
    {ρ : TRes w.K} (hcov : CovR (sem w.Θ) w.K ρ) (hO : ∀ r ∈ O, CovR (sem w.Θ) w.K r.R)
    (hl : KeepRel w.Θ ls ls' ρ) (h : cerwpTC (ℍ := ℍ) Tb Q Fb N F' w O k' ls e ρ) :
    cerwpTC (ℍ := ℍ) Tb Q Fb N F' w O k' ls' e ρ := by
  unfold cerwpTC at h ⊢
  split_ifs at h ⊢ with hk
  · exact cerwpT_kripke (TWd.Ext.refl _ _) (RR.refl hcov) hl (RecsRR.refl hO) h
  · exact h

/-- **D13's resume from the whole-list resume, by the Kripke rule along `KeepRel`.** For an entry
whose answers hold nothing (`hPB`) and do not read the list (`hPBl`), a share resuming at every
re-reading of its stop list resumes at every list keeping the records it reads, wherever the stop
list has a re-reading at the resume world (`hex`). -/
theorem contShareT_of_rr {Tb : TableT} {Q : TPostV} {Fb : TFrame} {N : Nat} {en : OpEntT}
    {F : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {K : Kont} {v : Val} {ρ : TRes w.K}
    (hPB : ∀ k' (w' : TWd) ls' a (σ : TRes w'.K), en.PBv v k' w' ls' a σ → σ = PMap.empty)
    (hPBl : ∀ k' (w' : TWd) (ls₁ ls₂ : List (SRecT w'.K)) a (σ : TRes w'.K),
      en.PBv v k' w' ls₁ a σ → en.PBv v k' w' ls₂ a σ)
    (hex : ∀ w' : TWd, w.Ext w' ρ → ∃ lsR : List (SRecT w'.K), SRecsRR w'.Θ ls lsR)
    (h : contShareRR en F k w ls O K v (cerwpTC (ℍ := ℍ) Tb Q Fb N) ρ) :
    contShareT en F k w ls O K v (cerwpTC (ℍ := ℍ) Tb Q Fb N) ρ := by
  refine ⟨h.1, fun w' ρ' ls' O' hE hr hx hO => ?_⟩
  obtain ⟨lsR, hlR⟩ := hex w' hE
  obtain ⟨hres, hcan⟩ := h.2 w' ρ' lsR O' hE hr hlR hO
  have hcov : CovR (sem w'.Θ) w'.K ρ' := RR.cov hr
  have hkeep : KeepRel w'.Θ lsR ls' ρ' := KeepRel.of_rr_back hlR hr hx
  refine ⟨fun k' hk a σ σ' hB hc => ?_, fun hq hf k' hk => ?_⟩
  · obtain rfl := hPB _ _ _ _ _ hB
    obtain rfl := compS_empty_right_eq_tw hc
    exact cerwpTC_keep hcov (RecsRR.cov_right hO) hkeep
      (hres k' hk a PMap.empty _ (hPBl _ _ _ _ _ _ hB) hc)
  · exact cerwpTC_keep hcov (RecsRR.cov_right hO) hkeep (hcan hq hf k' hk)

end BoCa.Fig16.Tree.Wp.TwpStart

end
