import Core.TreeSchedPool
import Core.TreeLendJoin

/-!
# A pool whose tasks hold views of each other's lends, kept as a stack  `[spec §62]`

`PoolT` (`Core/TreeSchedPool.lean`) holds every two stored tasks apart at each other's record
masks, so no stored task holds a view of another's lend. This file keeps the pool as a **stack**
instead (`PoolTJ`), in which tasks above a **joiner** may hold views of what the joiner shares:

* **Each entry is held apart from the entries below it** at their masks, except at the lent
  locations the nearest joiner below shares (`shTop`, `AvoidUnsh`); the entries below hold
  nothing at its masks. Its `imm` cells sit at its own masks or where the nearest joiner below
  shares (`HoldsIn`). A joiner shares only lent locations of its own or already shared with it.
* **A joiner collects the views handed back to it** (its accumulator `c`): copies of lends
  (`ViewsT`), deposited by the tasks above it as they end (`PoolTJ.deposit`), and handed to it
  with its answer when it is resumed. A task that is not a joiner collects nothing.

Every condition is per record and is carried by every run beside the pool (`twp_keepsPoolJ`):
from `twp_frame_keep_sh` (`twp_frame_keep` with the separation from the frame read record by
record, the shared records exempt) and `twp_holdsIn` (every run keeps `HoldsIn`, from `UpdX`'s
converse clause). The stack's moves at `twp`: resume the top (`poolTJ_resume`, its accumulator
handed with the answer), cancel the top (`poolTJ_cancel`), exchange the two top entries when
neither is a joiner (`PoolTJ.swap`), deposit a finished task's views at the nearest joiner
(`PoolTJ.deposit`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont hndE)

/-! ### A run beside a frame that may hold views of the run's lenders -/

/-- **A resource framed beside a run keeps the records it reads, the run apart from it record by
record.** `twp_frame_keep` with the separation from the frame read one record at a time: the run
may hold anything at the masks of framed records lent at a location in `S`; for every other framed
record it holds nothing at the record's masks at the start, and still holds nothing there at
every end. The framed part holds nothing at the masks of the run's records, at the start and at
every end; each side's lent locations are outside the other's masks at every end. -/
theorem twp_frame_keep_sh {S : BoCa.Loc → Prop} {F F₁ : TFrame} {P : TPost} {R : TRProp}
    (hR : R.Mono) {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O₁ O₂ : List (FrameRecT w.K)}
    (hO : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) {e : Expr} {ρ₁ ρ₂ ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρ₂ ρ) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ)
    (hesc₁ : NoneAt (recMask O₁) ρ₂) (hesc₂ : ∀ q ∈ O₂, ¬ S q.le → NoneAt (recMask [q]) ρ₁)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      RecsRR w₀.Θ O₁ O₁₀ → RecsRR w₀.Θ O₂ O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls O₁ e ρ₁) (hR₂ : R w O₂ ρ₂) :
    twp (ℍ := ℍ) F (fun k w' ls' O' t ρ' => ∃ (O₁' O₂' : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = O₁' ++ O₂' ∧ ResUT.CompS a b ρ' ∧ P k w' ls' O₁' t a ∧ R w' O₂' b ∧
        KeepRel w'.Θ ls ls' ρ₂ ∧ NoneAt (recMask O₁') b ∧
          (∀ q ∈ O₂', ¬ S q.le → NoneAt (recMask [q]) a) ∧
        (∀ p ∈ O₁', ∀ q ∈ O₂', p.le ≠ q.le) ∧ (∀ q ∈ O₂', ¬ recMask O₁' q.le) ∧
        ∀ p ∈ O₁', ¬ recMask O₂' p.le)
      n w ls (O₁ ++ O₂) e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hOr hFρ hf hc hS hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₁₀, O₂₀, rfl, hO₁, hO₂⟩ := forall₂_append_left hOr
  have hO₀ : ∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le := by
    intro p hp q hq
    obtain ⟨p₁, hp₁, r₁⟩ := forall₂_mem_right hO₁ hp
    obtain ⟨q₂, hq₂, r₂⟩ := forall₂_mem_right hO₂ hq
    rw [r₁.1, r₂.1]
    exact hO p₁ hp₁ q₂ hq₂
  obtain ⟨ρ₁₀, ρ₂₀, h₁₀, h₂₀, hc₀⟩ := RR.split_retype hE.1 hcρ hcov hE.2 hr
  have hE₁ := hE.of_compS_left hcρ
  have hE₂ := hE.of_compS_right hcρ
  obtain ⟨y, hy, hyf⟩ := reassoc_out hc hc₀
  have hS₁ : SplitT ps O₁₀ (O₂₀ ++ psF) := by
    refine ⟨fun p => ?_, fun p hp q hq => ?_⟩
    · rw [hS.1 p, List.mem_append, List.mem_append]; tauto
    · rcases List.mem_append.mp hq with h | h
      · exact hO₀ p hp q h
      · exact hS.2 p (List.mem_append_left _ hp) q h
  obtain ⟨w', y', ρ₁', fρ', psF'', ps', O₁', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    hwp w₀ ρ₁₀ y fρ ls₀ O₁₀ ps (O₂₀ ++ psF) μ hE₁ h₁₀ hl hO₁
      (hF w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE₂ h₂₀ hO₁ hO₂ hFρ hy hyf hS hO₀ hRi hI)
      (hash_of_inv hyf hI) hyf hS₁ hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₂', psF', rfl, hO₂', hpsF'⟩ := forall₂_append_left g₂
  obtain ⟨ρf', ρ₂', hf', h₂', hy'⟩ :=
    RR.split_retype g₀.1 hy (covf_of_comp hyf hI) g₀.2 g₁
  obtain ⟨ρ', hρ', hfρ'⟩ := reassoc_in hy' g₄
  have hR₂₀ : R w₀ O₂₀ ρ₂₀ := hR _ _ _ _ _ _ hE₂ h₂₀ hO₂ hR₂
  have hvy' : ResUT.Valid y' := (ResUT.Valid.split g₄ g₇.valid).1
  have hu : UpdX (sem w'.Θ) (recMask O₁₀) (recMask O₁') ρ₀ ρ' :=
    UpdX.frame g₀.1 g₉ h₂' hc₀ hρ' (cov_valid hc hI) (cov_valid hfρ' g₇)
      (g₁₀.of_compS_right hy' hvy')
  have hmask : ∀ x, MaskDiff (recMask (O₁₀ ++ O₂₀)) (recMask (O₁' ++ O₂')) x →
      MaskDiff (recMask O₁₀) (recMask O₁') x := fun x hx => by
    unfold MaskDiff at hx ⊢
    rw [recMask_append, recMask_append, ← recMask_rr hO₂' x] at hx
    tauto
  have hv₁ : ResUT.Valid ρ₁ := (ResUT.Valid.split hcρ hv).1
  have hv₂ : ResUT.Valid ρ₂ := (ResUT.Valid.split hcρ hv).2
  have hvy : ResUT.Valid y := (ResUT.Valid.split hyf hI.valid).1
  have hv₂₀ : ResUT.Valid ρ₂₀ := (ResUT.Valid.split hy hvy).2
  have hvesc : ∀ p ∈ ps, ResUT.Valid p.R := TWNT.esc_valid hRi.1
  have hesc₁₀ : NoneAt (recMask O₁₀) ρ₂₀ :=
    (hesc₁.rr hE.1 hv₂ h₂₀).mono fun x hx => (recMask_rr hO₁ x).mpr hx
  -- the records the framed part reads are kept
  have hkeep : KeepRel w'.Θ ls ls' ρ₂ := by
    intro r hr₀ hrel
    obtain ⟨r₀, hr₀', e₀⟩ := hl.mem_fwd hr₀
    have hrel₀ : RelFT r₀ ρ₂₀ := (RelFT.rr_iff e₀ h₂₀).mp hrel
    obtain ⟨p₁, hp₁, hd⟩ := (hRi.1.inv.2.2.2.2.2.2.1 r₀).mp hr₀'
    rcases (hS₁.1 p₁).mp hp₁ with hp₁O | hp₁F
    · exact (relFT_not_fdEsc hd hrel₀ hv₂₀ (hvesc p₁ hp₁)
        (fdEsc_of_noneAt hRi.1 hp₁O hp₁ hesc₁₀)).elim
    · obtain ⟨r', hr', e'⟩ := keep_frameRooted g₂ g₅ g₆.1 ⟨p₁, hp₁F, hd⟩
      exact ⟨r', hr', RecRR.trans g₀.1 e₀ e'⟩
  -- the framed part avoids the masks of the records the run ends with
  have hb : NoneAt (recMask O₁') ρ₂' := by
    intro τ hτ x hx
    by_cases hx₀ : recMask O₁₀ x
    · exact (hesc₁₀.rr g₀.1 hv₂₀ h₂') τ hτ x hx₀
    · exact (g₁₀.of_compS_right hy' hvy') τ hτ x (Or.inr ⟨hx, hx₀⟩)
  -- the run's end avoids the masks of the framed records not lent at `S`
  have ha : ∀ q' ∈ O₂', ¬ S q'.le → NoneAt (recMask [q']) ρ₁' := by
    intro q' hq' hS'
    refine noneAt_recMask (fun q hq => by
      rcases List.mem_singleton.mp hq with rfl
      exact TWNT.esc_valid g₆.1 q (g₅.right q (List.mem_append_left _ hq'))) fun q₁ hq₁ => ?_
    rcases List.mem_singleton.mp hq₁ with rfl
    obtain ⟨q, hq, hqq⟩ := forall₂_mem_right hO₂' hq'
    obtain ⟨q₂, hq₂, hqq₂⟩ := forall₂_mem_right hO₂ hq
    have hq₀ : q ∈ ps := (hS.1 q).mpr (Or.inl (List.mem_append_right _ hq))
    have hn₂ : ¬ S q₂.le := by rw [← hqq₂.1, ← hqq.1]; exact hS'
    have hn : NoneAt (recMask [q]) ρ₁₀ :=
      ((hesc₂ q₂ hq₂ hn₂).rr hE.1 hv₁ h₁₀).mono fun x hx =>
        (recMask_rr (List.Forall₂.cons hqq₂ .nil) x).mpr hx
    exact fdEsc_of_updX g₀.1 (hvesc q hq₀) (fdEsc_of_noneAt hRi.1 (List.mem_singleton_self q) hq₀ hn)
      g₆.1 g₄ g₅ (List.mem_append_left _ hq') hqq g₉
  -- each side's lent locations are outside the other's masks
  have hout : ∀ q ∈ O₂', ¬ recMask O₁' q.le := by
    rintro q hq ⟨p, hp, hx⟩
    have hTI := g₆.1.inv
    have hpps : p ∈ ps' := (g₅.1 p).mpr (Or.inl hp)
    have hqps : q ∈ ps' := (g₅.1 q).mpr (Or.inr (List.mem_append_left _ hq))
    rcases hx with hx | hx
    · exact g₅.2 p hp q (List.mem_append_left _ hq) hx.symm
    · have hprs : p ∈ rsOfT ls' := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hpps, [], .nil p⟩
      exact le_not_linLoc g₆.1 hpps hqps (ExDom.linLoc w'.Θ hx p rfl (hTI.1.2.2.2.1 p hprs))
  have hout' : ∀ p ∈ O₁', ¬ recMask O₂' p.le := by
    rintro p hp ⟨q, hq, hx⟩
    have hTI := g₆.1.inv
    have hpps : p ∈ ps' := (g₅.1 p).mpr (Or.inl hp)
    have hqps : q ∈ ps' := (g₅.1 q).mpr (Or.inr (List.mem_append_left _ hq))
    rcases hx with hx | hx
    · exact g₅.2 p hp q (List.mem_append_left _ hq) hx
    · have hqrs : q ∈ rsOfT ls' := (hTI.2.2.2.2.2.2.1 q).mpr ⟨q, hqps, [], .nil q⟩
      exact le_not_linLoc g₆.1 hqps hpps (ExDom.linLoc w'.Θ hx q rfl (hTI.1.2.2.2.1 q hqrs))
  refine ⟨w', ρf', ρ', fρ', psF', ps', O₁' ++ O₂', ls', g₀.of_compS_left hy, hf', hpsF',
    ResUT.hash_symm (hash_of_inv hfρ' g₇), hfρ', ⟨fun p => ?_, fun p hp q hq => ?_⟩, g₆, g₇,
    ⟨O₁', O₂', ρ₁', ρ₂', rfl, hρ', g₈, hR _ _ _ _ _ _ (g₀.of_compS_right hy) h₂' hO₂' hR₂₀,
      hkeep, hb, ha, fun p hp q hq => g₅.2 p hp q (List.mem_append_left _ hq), hout, hout'⟩,
    (hu.widen (recMask O₂₀)).congr (fun l => recMask_append l)
      (fun l => by rw [recMask_append, recMask_rr hO₂' l]),
    (g₁₀.of_compS_left hy' hvy').mono hmask,
    (g₁₁.mono fun l h => (recMask_append l).mpr (Or.inl h)).frame hc₀ (TWNT.mutOne hRi.1)
      (fun _ _ h k => (h.of_compS_right hc₀ (kind_mut_ne_imm k)).of_compS_right hc
        (kind_mut_ne_imm k))
      (AgreeOn.of_compS_right hy g₀.2)⟩
  · rw [g₅.1 p, List.mem_append, List.mem_append]; tauto
  · rcases List.mem_append.mp hp with h | h
    · exact g₅.2 p h q (List.mem_append_right _ hq)
    · obtain ⟨p₀, hp₀, r₀⟩ := forall₂_mem_right hO₂' h
      obtain ⟨q₀, hq₀, s₀⟩ := forall₂_mem_right hpsF' hq
      rw [r₀.1, s₀.1]
      exact hS.2 p₀ (List.mem_append_right _ hp₀) q₀ hq₀

/-! ### Where a task's borrowed cells sit -/

section Holds
variable {K K' : WCactus}

/-- **Borrowed cells only at own masks or at `A`**: every `imm` cell of `ρ`'s flattening is at a
location masked by the records `O` or in `A`. -/
def HoldsIn (A : BoCa.Loc → Prop) (O : List (FrameRecT K)) (ρ : TRes K) : Prop :=
  ∀ τ, ResUT.Flat ρ τ → ∀ x (ψ : TCell K), τ.get x = some ψ → ψ.kind = Kind.imm →
    recMask O x ∨ A x

theorem kcomb_imm_left {k₂ : Kind} : kcomb Kind.imm k₂ = Kind.imm := by
  cases k₂ <;> rfl

theorem kcomb_imm {k₁ k₂ : Kind} (h : kcomb k₁ k₂ = Kind.imm) :
    k₁ = Kind.imm ∨ k₂ = Kind.imm := by
  cases k₁ <;> cases k₂ <;> simp_all [kcomb]

theorem HoldsIn.mono {A A' : BoCa.Loc → Prop} {O : List (FrameRecT K)} {ρ : TRes K}
    (h : HoldsIn A O ρ) (hA : ∀ x, A x → A' x) : HoldsIn A' O ρ :=
  fun τ hτ x ψ e k => (h τ hτ x ψ e k).imp id (hA x)

theorem HoldsIn.empty (A : BoCa.Loc → Prop) (O : List (FrameRecT K)) :
    HoldsIn A O (PMap.empty : TRes K) := by
  intro τ hτ x ψ e _
  obtain rfl := ResUT.Flat.functional hτ flat_empty
  simp at e

theorem HoldsIn.of_compS_left {A : BoCa.Loc → Prop} {O : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hv : ResUT.Valid c) (h : HoldsIn A O c) : HoldsIn A O a := by
  intro τa hτa x ψ e k
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨σ₁, σ₂, h₁, -, hσ⟩ := BoLo.flat_compR hc hτ
  obtain rfl := ResUT.Flat.functional h₁ hτa
  have hp := hσ.2 x
  rw [e] at hp
  revert hp
  cases e₂ : σ₂.get x with
  | none => intro hp; exact h τ hτ x ψ hp k
  | some ψ₂ =>
      rintro ⟨χ, hχ, hC⟩
      exact h τ hτ x χ hχ (by rw [CellUT.CompR.kind_eq hC, k]; exact kcomb_imm_left)

theorem HoldsIn.of_compS_right {A : BoCa.Loc → Prop} {O : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hv : ResUT.Valid c) (h : HoldsIn A O c) : HoldsIn A O b :=
  HoldsIn.of_compS_left (ResUT.CompS.comm hc) hv h

theorem HoldsIn.compS {A : BoCa.Loc → Prop} {O : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (ha : HoldsIn A O a) (hb : HoldsIn A O b) : HoldsIn A O c := by
  intro τ hτ x ψ e k
  obtain ⟨σ₁, σ₂, h₁, h₂, hσ⟩ := BoLo.flat_compR hc hτ
  have hp := hσ.2 x
  rw [e] at hp
  revert hp
  cases e₁ : σ₁.get x with
  | none =>
      cases e₂ : σ₂.get x with
      | none => intro hp; cases hp
      | some ψ₂ => intro hp; cases hp; exact hb σ₂ h₂ x _ e₂ k
  | some ψ₁ =>
      cases e₂ : σ₂.get x with
      | none => intro hp; cases hp; exact ha σ₁ h₁ x _ e₁ k
      | some ψ₂ =>
          rintro ⟨χ, hχ, hC⟩
          cases hχ
          rcases kcomb_imm ((CellUT.CompR.kind_eq hC).symm.trans k) with k₁ | k₂
          · exact ha σ₁ h₁ x ψ₁ e₁ k₁
          · exact hb σ₂ h₂ x ψ₂ e₂ k₂

/-- **Carried by re-reading**: the flattening's cells are re-read with their kinds. -/
theorem HoldsIn.rr {Θ : LocTy} (hE : K.Ext K') {A : BoCa.Loc → Prop} {O : List (FrameRecT K)}
    {O' : List (FrameRecT K')} (hO : ∀ x, recMask O x ↔ recMask O' x) {ρ : TRes K}
    {ρ' : TRes K'} (hv : ResUT.Valid ρ) (hr : RR Θ ρ ρ') (h : HoldsIn A O ρ) :
    HoldsIn A O' ρ' := by
  intro τ' hτ' x ψ' e k
  obtain ⟨τ, hτ⟩ := hv
  obtain ⟨σ', hσ', hs⟩ := ResUT.Flat.rrLs hE hτ hr
  obtain rfl := ResUT.Flat.functional hσ' hτ'
  have hl := hs x
  rw [e] at hl
  revert hl
  cases eψ : τ.get x with
  | none => intro hl; cases hl
  | some ψ =>
      intro hl
      cases hl with
      | some hl => exact (h τ hτ x ψ eψ (hl.1.symm.trans k)).imp (hO x).mp id

/-- The masks of the records read: `HoldsIn` asks only where the masks are. -/
theorem HoldsIn.congr {A : BoCa.Loc → Prop} {O O' : List (FrameRecT K)}
    (hO : ∀ x, recMask O x → recMask O' x) {ρ : TRes K} (h : HoldsIn A O ρ) : HoldsIn A O' ρ :=
  fun τ hτ x ψ e k => (h τ hτ x ψ e k).imp (hO x) id

end Holds

/-- **Kept by every run**: a cell of the end's flattening outside the end's masks is one of the
start's, outside the start's masks (`UpdX`, its converse clause). -/
theorem twp_holdsIn {A : BoCa.Loc → Prop} {F : TFrame} {P : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hv : ResUT.Valid ρ) (hA : HoldsIn A O ρ) (h : twp (ℍ := ℍ) F P n w ls O e ρ) :
    twp (ℍ := ℍ) F (fun k w' ls' O' t ρ' => P k w' ls' O' t ρ' ∧ HoldsIn A O' ρ') n w ls O e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ := h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  have hA₀ : HoldsIn A O₀ ρ₀ := hA.rr hE.1 (recMask_rr hO) hv hr
  refine ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, ⟨g₈, ?_⟩, g₉,
    g₁₀, g₁₁⟩
  intro τ' hτ' x ψ' eψ k
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := g₉
  obtain rfl := ResUT.Flat.functional hσ' hτ'
  by_cases hm : recMask O' x
  · exact Or.inl hm
  · obtain ⟨hm₀, ψ, eψ₀, hX⟩ := (hx x).2 ψ' eψ (by rw [k]; decide) hm
    exact (hA₀ σ hσ x ψ eψ₀ (hX.1.symm.trans k)).resolve_left hm₀ |> Or.inr

/-! ### Copies of lends -/

section Views
variable {K K' : WCactus}

/-- **Copies of lends**: every cell is `imm(S, (), ∅)` at some lifetime set `S`, the cell a lend
of `ℓ ↦ own(())` with the empty escrow hands out (`viewRes`). -/
def ViewsT (ρ : TRes K) : Prop :=
  ∀ x ψ, ρ.get x = some ψ → ∃ S : TSet,
    ψ = CellUT.immOf S BoCa.Val.unit PMap.empty (emptyT_inStratum _)

theorem ViewsT.empty : ViewsT (PMap.empty : TRes K) := fun _ _ e => by simp at e

theorem ViewsT.view (β : Life) (l : BoCa.Loc) : ViewsT (viewRes (K := K) β l) := by
  intro x ψ e
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  exact ⟨TSet.single β, rfl⟩

theorem ViewsT.viewS (S : TSet) (l : BoCa.Loc) : ViewsT (viewResS (K := K) S l) := by
  intro x ψ e
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  exact ⟨S, rfl⟩

/-- A cell composed of two copies is a copy. -/
theorem viewCell_compS {ψ₁ ψ₂ ψ : TCell K} (hC : CellUT.CompS ψ₁ ψ₂ ψ) {S : TSet}
    (h₁ : ψ₁ = CellUT.immOf S BoCa.Val.unit PMap.empty (emptyT_inStratum _)) :
    ∃ T : TSet, ψ = CellUT.immOf T BoCa.Val.unit PMap.empty (emptyT_inStratum _) := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, -, e₃⟩ := hC
  obtain ⟨-, rfl, rfl⟩ := CellUT.immOf_inj (h₁.symm.trans e₁)
  exact ⟨s₁ ∪ s₂, e₃.trans (CellUT.immOf_congr rfl rfl rfl _ _)⟩

theorem ViewsT.compS {a b c : TRes K} (hc : ResUT.CompS a b c) (ha : ViewsT a) (hb : ViewsT b) :
    ViewsT c := by
  intro x ψ e
  rcases ResUT.Comp.get hc x with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [e] at f; cases f
  · rw [e] at f; cases f; exact ha x _ f₁
  · rw [e] at f; cases f; exact hb x _ f₂
  · rw [e] at f; cases f
    obtain ⟨S, hS⟩ := ha x _ f₁
    exact viewCell_compS hC hS

theorem ViewsT.del {ρ : TRes K} (h : ViewsT ρ) (l : BoCa.Loc) : ViewsT (ρ.del l) := by
  classical
  intro x ψ e
  by_cases hx : x = l
  · subst hx; rw [ResUT.del_get_self] at e; cases e
  · rw [ResUT.del_get_ne _ hx] at e; exact h x ψ e

theorem ViewsT.rr {Θ : LocTy} {ρ : TRes K} {ρ' : TRes K'} (hr : RR Θ ρ ρ') (h : ViewsT ρ) :
    ViewsT ρ' := by
  intro x ψ' e'
  obtain ⟨ψ, e, hrc⟩ := hr.get_some' e'
  obtain ⟨S, rfl⟩ := h x ψ e
  obtain ⟨χ', h', rfl, hχ⟩ := RC.immOf_inv hrc
  obtain rfl := RR.of_empty hχ
  exact ⟨S, rfl⟩

/-- Every cell of a resource of copies is `imm`. -/
theorem ViewsT.kind {ρ : TRes K} (h : ViewsT ρ) {x : BoCa.Loc} {ψ : TCell K}
    (e : ρ.get x = some ψ) : ψ.kind = Kind.imm := by
  obtain ⟨S, rfl⟩ := h x ψ e; rfl

/-- **Copies held nowhere are nothing**: a valid resource of copies whose `imm` cells sit nowhere
(`HoldsIn` at no location and no record) is empty. -/
theorem ViewsT.eq_empty {ρ : TRes K} (h : ViewsT ρ) (hv : ResUT.Valid ρ)
    (hH : HoldsIn (fun _ => False) ([] : List (FrameRecT K)) ρ) : ρ = PMap.empty := by
  obtain ⟨τ, hτ⟩ := hv
  refine PMap.ext fun x => ?_
  cases e : ρ.get x with
  | none => simp
  | some ψ =>
      obtain ⟨χ, eχ, kχ, -⟩ := ResUT.Flat.get hτ e
      rcases hH τ hτ x χ eχ (kχ.trans (h.kind e)) with ⟨p, hp, -⟩ | hf
      · cases hp
      · exact hf.elim

/-- A copy at `ℓ` splits off a resource of copies. -/
theorem ViewsT.split_at {ρ : TRes K} (h : ViewsT ρ) (l : BoCa.Loc) :
    ρ.get l = none ∨ ∃ S, ResUT.CompS (ρ.del l) (viewResS S l) ρ := by
  cases e : ρ.get l with
  | none => exact Or.inl rfl
  | some ψ =>
      obtain ⟨S, rfl⟩ := h l _ e
      exact Or.inr ⟨S, ResUT.del_compS e⟩

end Views

/-! ### The stack -/

/-- **A pool entry**: a stored task, whether it waits for the tasks above it (`join`), the lent
locations it shares with them (`sh`), and the tag the scheduler's code stores beside it. -/
structure StoredJ where
  t : StoredT
  join : Bool
  sh : BoCa.Loc → Prop
  tag : Val

/-- What the nearest joiner shares. -/
def shTop : List StoredJ → BoCa.Loc → Prop
  | [] => fun _ => False
  | s :: ss => fun x => (s.join = true ∧ s.sh x) ∨ (s.join = false ∧ shTop ss x)

theorem shTop_joiner {s : StoredJ} {ss : List StoredJ} (h : s.join = true) (x : BoCa.Loc) :
    shTop (s :: ss) x ↔ s.sh x := by
  simp [shTop, h]

theorem shTop_ready {s : StoredJ} {ss : List StoredJ} (h : s.join = false) (x : BoCa.Loc) :
    shTop (s :: ss) x ↔ shTop ss x := by
  simp [shTop, h]

/-- **Nothing at the masks of the records not lent at `A`.** -/
def AvoidUnsh {K : WCactus} (A : BoCa.Loc → Prop) (Os : List (FrameRecT K)) (ρ : TRes K) : Prop :=
  ∀ q ∈ Os, ¬ A q.le → NoneAt (recMask [q]) ρ

/-- Records apart by location, and each list's lent locations outside the other's masks. -/
def RecsApart {K : WCactus} (O₁ O₂ : List (FrameRecT K)) : Prop :=
  (∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) ∧ (∀ q ∈ O₂, ¬ recMask O₁ q.le) ∧ ∀ p ∈ O₁, ¬ recMask O₂ p.le

section Avoid
variable {K K' : WCactus}

theorem noneAt_of_each {O : List (FrameRecT K)} {ρ : TRes K}
    (h : ∀ q ∈ O, NoneAt (recMask [q]) ρ) : NoneAt (recMask O) ρ := by
  intro τ hτ x ⟨q, hq, hx⟩
  exact h q hq τ hτ x ⟨q, List.mem_singleton_self q, hx⟩

theorem AvoidUnsh.of_noneAt {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {ρ : TRes K}
    (h : NoneAt (recMask Os) ρ) : AvoidUnsh A Os ρ :=
  fun q hq _ => h.mono fun x ⟨p, hp, hx⟩ => ⟨p, by simp at hp; exact hp ▸ hq, hx⟩

theorem AvoidUnsh.mono {A A' : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {ρ : TRes K}
    (h : AvoidUnsh A Os ρ) (hA : ∀ x, A x → A' x) : AvoidUnsh A' Os ρ :=
  fun q hq hn => h q hq fun h' => hn (hA _ h')

theorem AvoidUnsh.sub {A : BoCa.Loc → Prop} {O O' : List (FrameRecT K)} {ρ : TRes K}
    (h : AvoidUnsh A O ρ) (hO : ∀ q ∈ O', q ∈ O) : AvoidUnsh A O' ρ :=
  fun q hq => h q (hO q hq)

theorem AvoidUnsh.append {A : BoCa.Loc → Prop} {O₁ O₂ : List (FrameRecT K)} {ρ : TRes K}
    (h₁ : AvoidUnsh A O₁ ρ) (h₂ : AvoidUnsh A O₂ ρ) : AvoidUnsh A (O₁ ++ O₂) ρ := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact h₁ q h
  · exact h₂ q h

theorem AvoidUnsh.compS {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hva : ResUT.Valid a) (hvb : ResUT.Valid b) (ha : AvoidUnsh A Os a)
    (hb : AvoidUnsh A Os b) : AvoidUnsh A Os c :=
  fun q hq hn => NoneAt.compS hc hva hvb (ha q hq hn) (hb q hq hn)

theorem AvoidUnsh.of_compS_left {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hv : ResUT.Valid c) (h : AvoidUnsh A Os c) : AvoidUnsh A Os a :=
  fun q hq hn => (h q hq hn).of_compS_left hc hv

theorem AvoidUnsh.of_compS_right {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hv : ResUT.Valid c) (h : AvoidUnsh A Os c) : AvoidUnsh A Os b :=
  fun q hq hn => (h q hq hn).of_compS_right hc hv

theorem AvoidUnsh.empty (A : BoCa.Loc → Prop) (Os : List (FrameRecT K)) :
    AvoidUnsh A Os (PMap.empty : TRes K) :=
  fun _ _ _ => noneAt_empty _

theorem AvoidUnsh.rr {Θ : CodeTy} (hE : K.Ext K') {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)}
    {Os' : List (FrameRecT K')} (hO : RecsRR Θ Os Os') {ρ : TRes K} {ρ' : TRes K'}
    (hv : ResUT.Valid ρ) (hr : RR (sem Θ) ρ ρ') (h : AvoidUnsh A Os ρ) : AvoidUnsh A Os' ρ' := by
  intro q' hq' hn
  obtain ⟨q, hq, hqq⟩ := forall₂_mem_right hO hq'
  exact ((h q hq (by rw [← hqq.1]; exact hn)).rr hE hv hr).mono fun x hx =>
    (recMask_rr (List.Forall₂.cons hqq .nil) x).mpr hx

theorem RecsApart.rr {Θ : CodeTy} {O₁ O₂ : List (FrameRecT K)} {O₁' O₂' : List (FrameRecT K')}
    (h₁ : RecsRR Θ O₁ O₁') (h₂ : RecsRR Θ O₂ O₂') (h : RecsApart O₁ O₂) : RecsApart O₁' O₂' := by
  refine ⟨apart_rr h₁ h₂ h.1, fun q' hq' hm => ?_, fun p' hp' hm => ?_⟩
  · obtain ⟨q, hq, hqq⟩ := forall₂_mem_right h₂ hq'
    exact h.2.1 q hq ((recMask_rr h₁ _).mpr (hqq.1 ▸ hm))
  · obtain ⟨p, hp, hpp⟩ := forall₂_mem_right h₁ hp'
    exact h.2.2 p hp ((recMask_rr h₂ _).mpr (hpp.1 ▸ hm))

theorem RecsApart.symm {O₁ O₂ : List (FrameRecT K)} (h : RecsApart O₁ O₂) : RecsApart O₂ O₁ :=
  ⟨fun p hp q hq e => h.1 q hq p hp e.symm, h.2.2, h.2.1⟩

theorem RecsApart.append_right {O₁ O₂ O₃ : List (FrameRecT K)} :
    RecsApart O₁ (O₂ ++ O₃) ↔ RecsApart O₁ O₂ ∧ RecsApart O₁ O₃ := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨⟨fun p hp q hq => h₁ p hp q (List.mem_append_left _ hq),
        fun q hq => h₂ q (List.mem_append_left _ hq),
        fun p hp hm => h₃ p hp ((recMask_append _).mpr (Or.inl hm))⟩,
      ⟨fun p hp q hq => h₁ p hp q (List.mem_append_right _ hq),
        fun q hq => h₂ q (List.mem_append_right _ hq),
        fun p hp hm => h₃ p hp ((recMask_append _).mpr (Or.inr hm))⟩⟩
  · rintro ⟨⟨a₁, a₂, a₃⟩, ⟨b₁, b₂, b₃⟩⟩
    refine ⟨fun p hp q hq => ?_, fun q hq => ?_, fun p hp hm => ?_⟩
    · rcases List.mem_append.mp hq with h | h
      · exact a₁ p hp q h
      · exact b₁ p hp q h
    · rcases List.mem_append.mp hq with h | h
      · exact a₂ q h
      · exact b₂ q h
    · rcases (recMask_append _).mp hm with h | h
      · exact a₃ p hp h
      · exact b₃ p hp h

theorem RecsApart.nil_right (O : List (FrameRecT K)) : RecsApart O [] :=
  ⟨fun _ _ _ hq => (by cases hq), fun _ hq => (by cases hq), fun _ _ h => (by simp [recMask] at h)⟩

end Avoid

/-- **The pool as a stack.** Each entry `s` above the rest `ss`:

* its share `a` (its continuation held at `w`, `KapAtT`) beside what it has collected `c` (a
  joiner's: copies of lends, `ViewsT`; nothing for a task that is not a joiner), the two `a′`;
* its mask its records' masks; the rest a stack at `w`, holding nothing at its masks;
* `a′` holding nothing at the masks of the rest's records not lent at what the nearest joiner of
  the rest shares, its `imm` cells at its own masks or there;
* what it shares lent by itself or shared with it; its records apart from the rest's. -/
def PoolTJ : List StoredJ → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → TRes w.K → Prop
  | [], _, _, O, ρ => O = [] ∧ ρ = PMap.empty
  | s :: ss, w, ls, O, ρ => ∃ (Ot Os : List (FrameRecT w.K)) (a c a' b : TRes w.K),
      O = Ot ++ Os ∧ ResUT.CompS a c a' ∧ ResUT.CompS a' b ρ ∧
      KapAtT (ℍ := ℍ) s.t.Q s.t.M s.t.en s.t.H s.t.k s.t.v s.t.κ w ls Ot a ∧
      (s.join = false → c = PMap.empty) ∧ ViewsT c ∧
      (∀ x, s.t.M x ↔ recMask Ot x) ∧ PoolTJ ss w ls Os b ∧ NoneAt (recMask Ot) b ∧
      AvoidUnsh (shTop ss) Os a' ∧ HoldsIn (shTop ss) Ot a' ∧
      (∀ x, s.sh x → recMask Ot x ∨ shTop ss x) ∧ RecsApart Ot Os

theorem poolTJ_nil {w : TWd} {ls : List (SRecT w.K)} :
    PoolTJ (ℍ := ℍ) [] w ls [] (PMap.empty : TRes w.K) := ⟨rfl, rfl⟩

/-- **What the nearest joiner shares is lent in the pool.** -/
theorem shTop_sub : ∀ {ss : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {Os : List (FrameRecT w.K)} {b : TRes w.K}, PoolTJ (ℍ := ℍ) ss w ls Os b →
    ∀ x, shTop ss x → recMask Os x
  | [], _, _, _, _, _, _, hx => hx.elim
  | s :: ss, _, _, _, _, ⟨Ot, Os, a, c, a', b, hO, _, _, _, _, _, _, hP, _, _, _, hsh, _⟩, x, hx => by
      subst hO
      rcases hx with ⟨-, hx⟩ | ⟨-, hx⟩
      · rcases hsh x hx with h | h
        · exact (recMask_append x).mpr (Or.inl h)
        · exact (recMask_append x).mpr (Or.inr (shTop_sub hP x h))
      · exact (recMask_append x).mpr (Or.inr (shTop_sub hP x hx))

/-- **The pool is held at every extension of the world**, on its re-reading, at every list keeping
the records of `ls` its shares read. -/
theorem PoolTJ.kripke : ∀ {ts : List StoredJ} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {O : List (FrameRecT w.K)} {O' : List (FrameRecT w'.K)}
    {ρ : TRes w.K} {ρ' : TRes w'.K}, PoolTJ (ℍ := ℍ) ts w ls O ρ → w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → RecsRR w'.Θ O O' → KeepRel w'.Θ ls ls' ρ →
    CovR (sem w.Θ) w.K ρ → ResUT.Valid ρ → PoolTJ (ℍ := ℍ) ts w' ls' O' ρ'
  | [], _, _, _, _, _, _, _, _, ⟨hO, hρ⟩, _, hr, hOr, _, _, _ => by
      subst hO; subst hρ; cases hOr; exact ⟨rfl, RR.of_empty hr⟩
  | t :: ts, w, w', ls, ls', O, O', ρ, ρ',
      ⟨Ot, Os, a, c, a₁, b, hO, hac, hc, hκ, hj, hV, hM, hP, hb, ha, hH, hsh, hap⟩, hE, hr, hOr, hl,
        hcov, hv => by
      subst hO
      obtain ⟨Ot', Os', rfl, hOt, hOs⟩ := forall₂_append_left hOr
      obtain ⟨a₁', b', hra₁, hrb, hc'⟩ := RR.split_retype hE.1 hc hcov hE.2 hr
      have hva₁ := (ResUT.Valid.split hc hv).1
      have hvb := (ResUT.Valid.split hc hv).2
      have hcov₁ := hcov.of_compS_left hc
      have hE₁ := hE.of_compS_left hc
      obtain ⟨a', c', hra, hrc, hac'⟩ := RR.split_retype hE₁.1 hac hcov₁ hE₁.2 hra₁
      refine ⟨Ot', Os', a', c', a₁', b', rfl, hac', hc',
        hκ.kripke (hE₁.of_compS_left hac) hra hOt ((hl.of_compS_left hc).of_compS_left hac),
        fun hjf => by obtain rfl := hj hjf; exact RR.of_empty hrc, hV.rr hrc,
        fun x => (hM x).trans (recMask_rr hOt x),
        PoolTJ.kripke hP (hE.of_compS_right hc) hrb hOs
          (hl.of_compS_left (ResUT.CompS.comm hc)) (hcov.of_compS_right hc) hvb,
        (NoneAt.rr hE.1 hvb hrb hb).mono fun x hx => (recMask_rr hOt x).mpr hx,
        ha.rr hE.1 hOs hva₁ hra₁, hH.rr hE.1 (recMask_rr hOt) hva₁ hra₁,
        fun x hx => (hsh x hx).imp (recMask_rr hOt x).mp id, hap.rr hOt hOs⟩

/-- The pool's records are covered at its world (each a re-reading, `KapAtT`). -/
theorem PoolTJ.cov_recs : ∀ {ts : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K}, PoolTJ (ℍ := ℍ) ts w ls O ρ →
    ∀ r ∈ O, CovR (sem w.Θ) w.K r.R
  | [], _, _, _, _, ⟨hO, _⟩ => by subst hO; intro r hr; cases hr
  | _ :: _, _, _, _, _, ⟨Ot, Os, a, c, a', b, hO, _, _, hκ, _, _, _, hP, _⟩ => by
      subst hO
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨w₁, ls₁, O₁, ρ₁', hK, hE₁, hr₁, hO₁, -⟩ := hκ
        obtain ⟨r₁, -, hrr⟩ := forall₂_mem_right hO₁ hr
        exact hrr.2.2.2.cov
      · exact PoolTJ.cov_recs hP r hr

/-! ### A run beside the stack -/

/-- **What a run beside the pool ends with**: its end (`P`, owning `Oa`) beside the pool held at
the end world and list (owning `Ob`), and the running task's conditions against it: the pool
holds nothing at the run's masks, the run nothing at the masks of the pool's records not lent at
what the nearest joiner shares, its `imm` cells at its own masks or there, the records apart. -/
def PoolPostJ (P : TPost) (ts : List StoredJ) : TPost := fun k₁ w' ls' O' t ρ' =>
  ∃ (Oa Ob : List (FrameRecT w'.K)) (a b : TRes w'.K), O' = Oa ++ Ob ∧ ResUT.CompS a b ρ' ∧
    P k₁ w' ls' Oa t a ∧ PoolTJ (ℍ := ℍ) ts w' ls' Ob b ∧ NoneAt (recMask Oa) b ∧
    AvoidUnsh (shTop ts) Ob a ∧ HoldsIn (shTop ts) Oa a ∧ RecsApart Oa Ob

/-- **A run keeps the pool**: from the running task's conditions against the pool at the start,
the pool held, and the same conditions, at every end. -/
theorem twp_keepsPoolJ {ts : List StoredJ} {F F₁ : TFrame} {P : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr} {ρ₁ ρp ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρp ρ) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ)
    (hap : ∀ p ∈ Or, ∀ q ∈ Op, p.le ≠ q.le)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : AvoidUnsh (shTop ts) Op ρ₁)
    (hA : HoldsIn (shTop ts) Or ρ₁)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρp → RRw (w := w) (w' := w₀) ρp ρ₂₀ →
      RecsRR w₀.Θ Or O₁₀ → RecsRR w₀.Θ Op O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls Or e ρ₁) (hP : PoolTJ (ℍ := ℍ) ts w ls Op ρp) :
    twp (ℍ := ℍ) F (PoolPostJ (ℍ := ℍ) P ts) n w ls (Or ++ Op) e ρ := by
  let R : TRProp := fun w' O ρ' => w.Ext w' ρp ∧ RRw (w := w) (w' := w') ρp ρ' ∧ RecsRR w'.Θ Op O
  have hRm : R.Mono := fun _ _ _ _ _ _ hE hr hO ⟨a, b, c⟩ =>
    ⟨a.trans b hE, RRw.trans hE.1 b hr, c.trans hE.1 hO⟩
  have hcovp : CovR (sem w.Θ) w.K ρp := CovR.of_compS_right hcρ hcov
  have hvp : ResUT.Valid ρp := (ResUT.Valid.split hcρ hv).2
  have hv₁ : ResUT.Valid ρ₁ := (ResUT.Valid.split hcρ hv).1
  have hOpc : ∀ r ∈ Op, CovR (sem w.Θ) w.K r.R := PoolTJ.cov_recs hP
  have h := twp_frame_keep_sh (S := shTop ts) (R := R) hRm hap hcρ hcov hv hesc₁ hesc₂ hF
    (twp_holdsIn hv₁ hA hwp) ⟨TWd.Ext.refl _ _, RR.refl hcovp, RecsRR.refl hOpc⟩
  refine twp_mono (fun k₁ w' ls' O' t ρ' hp => ?_) h
  obtain ⟨Oa, Ob, a, b, hO', hc, ⟨hPa, hHa⟩, ⟨hEb, hrb, hOb⟩, hkeep, hb, ha, hap', ho₁, ho₂⟩ := hp
  exact ⟨Oa, Ob, a, b, hO', hc, hPa, hP.kripke hEb hrb hOb hkeep hcovp hvp, hb, ha, hHa,
    hap', ho₁, ho₂⟩

/-! ### The stack's moves -/

/-- **Resume the top**: the pool's top task resumed at an answer `a` its entry accepts, with
what it has collected (`c`) beside the answer's resource `σ`; the rest of the pool beside it. `σ`
holds nothing at the masks of the pool's records not lent at what the top's nearest joiner shares,
and its `imm` cells only there. -/
theorem poolTJ_resume {t : StoredJ} {ts : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K} (hP : PoolTJ (ℍ := ℍ) (t :: ts) w ls O ρp)
    {k' : Nat} (hk : k' < t.t.k) {a : Val}
    (hB : ∀ c σ' : TRes w.K, ViewsT c → (t.join = false → c = PMap.empty) → ResUT.CompS c σ σ' →
      t.t.en.PBv t.t.v k' w ls a σ')
    (hc : ResUT.CompS ρp σ ρ) (hσ : AvoidUnsh (shTop (t :: ts)) O σ)
    (hσH : HoldsIn (shTop (t :: ts)) [] σ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) {F : TFrame} (hFM : ∀ w' ρf, F w' ρf → fdMask t.t.M w' ρf) :
    twp (ℍ := ℍ) F (PoolPostJ (ℍ := ℍ) (valPost t.t.Q) ts)
      k' w ls O (.app (.app t.t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) ρ := by
  obtain ⟨Ot, Os, ρt, c, ρt', ρs, rfl, hac, hcp, hκ, hj, hV, hM, hPs, hb, ha, hH, hsh, hap⟩ := hP
  -- `ρ = (ρt ● (c ● σ)) ● ρs`
  obtain ⟨x, hx₁, hx₂⟩ := (ResUT.CompS.assoc ρt' ρs σ ρ).mpr ⟨ρp, hcp, hc⟩
  obtain ⟨y, hy₁, hy₂⟩ := (ResUT.CompS.assoc ρt' σ ρs ρ).mp
    ⟨x, ResUT.CompS.comm hx₁, hx₂⟩
  obtain ⟨σ', hσ₁, hσ₂⟩ := (ResUT.CompS.assoc ρt c σ y).mpr ⟨ρt', hac, hy₁⟩
  have hvy := (ResUT.Valid.split hy₂ hv).1
  have hvs := (ResUT.Valid.split hy₂ hv).2
  have hvt' := ResUT.Valid.split hy₁ hvy
  -- `σ` against the rest: what the top shares is its own or shared below
  have hσs : AvoidUnsh (shTop ts) Os σ := fun q hq hn => hσ q (List.mem_append_right _ hq) fun h => by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · rcases hsh _ h with h | h
      · exact hap.2.1 q hq h
      · exact hn h
    · exact hn h
  have hσH' : HoldsIn (shTop ts) Ot σ := by
    intro τ hτ x ψ e k
    rcases (hσH τ hτ x ψ e k).resolve_left (by simp [recMask]) with ⟨-, h⟩ | ⟨-, h⟩
    · rcases hsh x h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inr h
  have hres := cerwpTE_iff.mp (hκ.resume hk (hB c σ' hV hj hσ₁) hσ₂ (fdMask_mono t.t.M)
    (fun _ _ h => h))
  exact twp_keepsPoolJ (ts := ts) hy₂ hcov hv hap.1 hb
    (AvoidUnsh.compS hy₁ hvt'.1 hvt'.2 ha hσs) (hH.compS hy₁ hσH')
    (pool_frame (F := F) (M := t.t.M) hFM hM hvs hb) hres hPs

/-- **Cancel the top**: the pool's top task, not a joiner, at a cancellable entry: its cancel
branch run under its scheduler, the rest of the pool beside it. -/
theorem poolTJ_cancel {t : StoredJ} {ts : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K} (hP : PoolTJ (ℍ := ℍ) (t :: ts) w ls O ρ)
    (hjn : t.join = false) (hq : t.t.en.q ≠ .lin) (hf : t.t.en.fin = true) {k' : Nat}
    (hk : k' < t.t.k) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame}
    (hFM : ∀ w' ρf, F w' ρf → fdMask t.t.M w' ρf) :
    twp (ℍ := ℍ) F (PoolPostJ (ℍ := ℍ) (valPost t.t.Q) ts)
      k' w ls O (hndE t.t.H (.app t.t.κ.1 (.val (Val.inj₂ .unit)))) ρ := by
  obtain ⟨Ot, Os, ρt, c, ρt', ρs, rfl, hac, hcp, hκ, hj, -, hM, hPs, hb, ha, hH, -, hap⟩ := hP
  obtain rfl := hj hjn
  obtain rfl : ρt = ρt' := (ResUT.CompS.functional hac (ResUT.compS_empty_right ρt)).symm
  have hvs := (ResUT.Valid.split hcp hv).2
  have h := cerwpTE_iff.mp (hκ.cancel hq hf hk (fdMask_mono t.t.M) (fun _ _ h => h))
  exact twp_keepsPoolJ (ts := ts) hcp hcov hv hap.1 hb ha hH
    (pool_frame (F := F) (M := t.t.M) hFM hM hvs hb) h hPs

/-- **Exchange the two top entries**, neither a joiner: the same resource, the records permuted. -/
theorem PoolTJ.swap {p t : StoredJ} {ts : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K} (hP : PoolTJ (ℍ := ℍ) (p :: t :: ts) w ls O ρ)
    (hpj : p.join = false) (htj : t.join = false) (hv : ResUT.Valid ρ) :
    ∃ O' : List (FrameRecT w.K), O'.Perm O ∧ PoolTJ (ℍ := ℍ) (t :: p :: ts) w ls O' ρ := by
  obtain ⟨Op, Os₁, ra, ca, ra', rs₁, rfl, hca, hc₁, hκa, hja, -, hMa, hP₁, hb₁, ha₁, hH₁, hsh₁,
    hap₁⟩ := hP
  obtain ⟨Ot, Os, rb, cb, rb', rs, rfl, hcb, hc₂, hκb, hjb, -, hMb, hPs, hb₂, ha₂, hH₂, hsh₂,
    hap₂⟩ := hP₁
  obtain rfl := hja hpj
  obtain rfl := hjb htj
  obtain rfl : ra = ra' := (ResUT.CompS.functional hca (ResUT.compS_empty_right ra)).symm
  obtain rfl : rb = rb' := (ResUT.CompS.functional hcb (ResUT.compS_empty_right rb)).symm
  have hsht : ∀ x, shTop (t :: ts) x ↔ shTop ts x := shTop_ready htj
  have hshp : ∀ x, shTop (p :: ts) x ↔ shTop ts x := shTop_ready hpj
  obtain ⟨x, hx₁, hx₂⟩ := (ResUT.CompS.assoc ra rb rs ρ).mp ⟨_, hc₂, hc₁⟩
  obtain ⟨y, hy₁, hy₂⟩ := (ResUT.CompS.assoc rb ra rs ρ).mpr ⟨x, ResUT.CompS.comm hx₁, hx₂⟩
  have hvs₁ := (ResUT.Valid.split hc₁ hv).2
  have hvy := (ResUT.Valid.split hy₂ hv).2
  have hvar := ResUT.Valid.split hy₁ hvy
  obtain ⟨hapt, haps⟩ := RecsApart.append_right.mp hap₁
  -- `p`'s share holds nothing at `t`'s masks: what is shared below `t` is lent below it
  have hpt : NoneAt (recMask Ot) ra := noneAt_of_each fun q hq => by
    refine ha₁ q (List.mem_append_left _ hq) fun h => ?_
    exact hap₂.2.2 q hq (shTop_sub hPs _ ((hsht _).mp h))
  refine ⟨Ot ++ (Op ++ Os), ?_, Ot, Op ++ Os, rb, PMap.empty, rb, y, rfl,
    ResUT.compS_empty_right rb, hy₂, hκb, fun h => rfl, ViewsT.empty, hMb,
    ⟨Op, Os, ra, PMap.empty, ra, rs, rfl, ResUT.compS_empty_right ra, hy₁, hκa, fun _ => rfl,
      ViewsT.empty, hMa, hPs, hb₁.of_compS_right hc₂ hvs₁,
      (ha₁.mono fun x hx => (hsht x).mp hx).sub fun q hq => List.mem_append_right _ hq,
      hH₁.mono fun x hx => (hsht x).mp hx, fun x hx => (hsh₁ x hx).imp id (hsht x).mp, haps⟩,
    NoneAt.compS hy₁ hvar.1 hvar.2 hpt hb₂,
    AvoidUnsh.append (AvoidUnsh.of_noneAt (hb₁.of_compS_left hc₂ hvs₁))
      (ha₂.mono fun x hx => (hshp x).mpr hx),
    hH₂.mono fun x hx => (hshp x).mpr hx, fun x hx => (hsh₂ x hx).imp id (hshp x).mpr,
    RecsApart.append_right.mpr ⟨hapt.symm, hap₂⟩⟩
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_comm.append_right _

/-- **Deposit a finished task's copies at the nearest joiner**: copies `L` beside the pool, held
where the nearest joiner shares and nowhere else of the pool's, join that joiner's collection;
with no joiner they are nothing (`ViewsT.eq_empty`). -/
theorem PoolTJ.deposit : ∀ {ts : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ L ρ' : TRes w.K}, PoolTJ (ℍ := ℍ) ts w ls O ρ →
    ResUT.CompS ρ L ρ' → ResUT.Valid ρ' → ViewsT L → HoldsIn (shTop ts) [] L →
    AvoidUnsh (shTop ts) O L → PoolTJ (ℍ := ℍ) ts w ls O ρ'
  | [], _, _, _, _, _, _, ⟨hO, hρ⟩, hc, hv, hV, hH, _ => by
      subst hO; subst hρ
      have hvL := (ResUT.Valid.split hc hv).2
      obtain rfl := hV.eq_empty hvL hH
      exact ⟨rfl, ResUT.CompS.functional hc (ResUT.compS_empty_right _)⟩
  | s :: ss, w, ls, O, ρ, L, ρ',
      ⟨Ot, Os, a, c, a', b, hO, hac, hcp, hκ, hj, hV, hM, hP, hb, ha, hH, hsh, hap⟩, hc, hv, hVL,
        hHL, hAL => by
      subst hO
      cases hjs : s.join with
      | true =>
          have hst : ∀ x, shTop (s :: ss) x ↔ s.sh x := shTop_joiner hjs
          -- `ρ′ = (a ● (c ● L)) ● b`
          obtain ⟨x, hx₁, hx₂⟩ := (ResUT.CompS.assoc a' b L ρ').mpr ⟨ρ, hcp, hc⟩
          obtain ⟨a'', hy₁, hy₂⟩ := (ResUT.CompS.assoc a' L b ρ').mp
            ⟨x, ResUT.CompS.comm hx₁, hx₂⟩
          obtain ⟨c', hc₁, hc₂⟩ := (ResUT.CompS.assoc a c L a'').mpr ⟨a', hac, hy₁⟩
          have hva'' := (ResUT.Valid.split hy₂ hv).1
          have hvs := ResUT.Valid.split hy₁ hva''
          -- `L` against the rest: what `s` shares is its own or shared below it
          have hLs : AvoidUnsh (shTop ss) Os L := fun q hq hn =>
            hAL q (List.mem_append_right _ hq) fun h => by
              rcases hsh _ ((hst _).mp h) with h | h
              · exact hap.2.1 q hq h
              · exact hn h
          have hLH : HoldsIn (shTop ss) Ot L := by
            intro τ hτ x ψ e k
            rcases (hHL τ hτ x ψ e k).resolve_left (by simp [recMask]) with h
            exact hsh x ((hst x).mp h)
          exact ⟨Ot, Os, a, c', a'', b, rfl, hc₂, hy₂, hκ, fun h => by simp [hjs] at h,
            hV.compS hc₁ hVL, hM, hP, hb, AvoidUnsh.compS hy₁ hvs.1 hvs.2 ha hLs,
            hH.compS hy₁ hLH, hsh, hap⟩
      | false =>
          have hst : ∀ x, shTop (s :: ss) x ↔ shTop ss x := shTop_ready hjs
          -- `ρ′ = a′ ● (b ● L)`
          obtain ⟨b', hb₁, hb₂⟩ := (ResUT.CompS.assoc a' b L ρ').mpr ⟨ρ, hcp, hc⟩
          have hvb' := (ResUT.Valid.split hb₂ hv).2
          have hvbL := ResUT.Valid.split hb₁ hvb'
          have hPb := PoolTJ.deposit hP hb₁ hvb' hVL (hHL.mono fun x hx => (hst x).mp hx)
            (fun q hq hn => hAL q (List.mem_append_right _ hq) fun h => hn ((hst _).mp h))
          -- `L` holds nothing at `s`'s masks: what is shared below `s` is lent below it
          have hLt : NoneAt (recMask Ot) L := noneAt_of_each fun q hq =>
            hAL q (List.mem_append_left _ hq) fun h =>
              hap.2.2 q hq (shTop_sub hP _ ((hst _).mp h))
          exact ⟨Ot, Os, a, c, a', b', rfl, hac, hb₂, hκ, hj, hV, hM, hPb,
            NoneAt.compS hb₁ hvbL.1 hvbL.2 hb hLt, ha, hH, hsh, hap⟩

end BoCa.Fig16.Tree.Wp

end
