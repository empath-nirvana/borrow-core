import TwoRun.Rename

/-!
# TwoRun — runs that allocate fresh locations agree up to renaming

A configuration `(μ, e)` *names* a location when the heap holds it, when `e` mentions it, or
when a value in the heap mentions it (`Named`).  A *fresh* step allocates only locations its
configuration does not name (`Step1F`); a fresh run takes only fresh steps (`FreshRun`).  A run
that does not allocate is fresh (`StepsNA.toFresh`).

`alloc↦` picks any location the heap misses, so the machine is not deterministic.  It is
deterministic up to renaming on fresh runs (`freshRun_det`): two fresh runs to values from one
configuration end in heaps and values related by a permutation of the locations.  The proof is a
lockstep simulation.  A step that is not an allocation is the only step (`step1_det`), and
renaming carries it (`step1_rename`).  At an allocation the two runs pick `ℓA` and `ℓB`; the
permutation is extended by swapping `σ ℓA` with `ℓB`, which fixes everything the configuration
names because both picks are fresh.

Freshness is what makes the swap harmless.  A run that reuses a location its configuration
still names (a dangling pointer after `free`) is not related to a fresh run by any renaming
(`Refute.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.TwoRun
open BoCa
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Fig16.LogRel.Core.FrameTheorems (allocRedex StepsNA Step1NA head_det)

/-! ### Naming and freshness -/

/-- `(μ, e)` names `ℓ`: `ℓ` is allocated, or occurs in `e` or in a value `μ` holds. -/
def Named (μ : Heap) (e : Expr) (ℓ : Loc) : Prop :=
  μ ℓ ≠ none ∨ e.Occ ℓ ∨ ∃ k v, μ k = some v ∧ v.1.Occ ℓ

/-- A step that allocates only locations its configuration does not name. -/
def Step1F (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  Step1 μ e μ' e' ∧ ∀ ℓ, μ' ℓ ≠ none → μ ℓ = none → ¬ Named μ e ℓ

/-- A run whose every allocation is of a location its configuration does not name. -/
inductive FreshRun : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : FreshRun μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1F μ e μ₁ e₁) (t : FreshRun μ₁ e₁ μ' e') : FreshRun μ e μ' e'

theorem FreshRun.toSteps {μ μ' : Heap} {e e' : Expr} (h : FreshRun μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih => exact .more h.1 ih

/-- A head step that is not an allocation adds no location. -/
theorem head_dom_of_not_alloc {μ μ' : Heap} {a a' : Expr} (h : Head μ a μ' a')
    (hna : ∀ v : Val, a ≠ allocRedex v) {ℓ : Loc} (h' : μ' ℓ ≠ none) : μ ℓ ≠ none := by
  cases h with
  | alloc v k _ => exact absurd rfl (hna v)
  | free k v _ =>
      intro h0; apply h'
      by_cases e : ℓ = k
      · subst e; exact Heap.del_same _ _
      · rw [Heap.del_other e, h0]
  | store k v w hk =>
      intro h0; apply h'
      by_cases e : ℓ = k
      · subst e; rw [hk] at h0; cases h0
      · rw [Heap.upd_other e, h0]
  | _ => exact h'

/-- **A run that does not allocate is fresh.** -/
theorem StepsNA.toFresh {μ μ' : Heap} {e e' : Expr} (h : StepsNA μ e μ' e') :
    FreshRun μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more h _ ih =>
      obtain ⟨K, a, a', he, he', hh, hna⟩ := h
      exact .more ⟨⟨K, a, a', he, he', hh⟩, fun ℓ h₁ h₂ => absurd h₂
        (head_dom_of_not_alloc hh hna h₁)⟩ ih

/-! ### Renaming and naming -/

theorem Expr.rename_inv (σ : Equiv.Perm Loc) (e : Expr) : (e.rename σ).rename σ.symm = e := by
  rw [Expr.rename_comp]
  convert Expr.rename_id e
  funext k; simp

theorem occ_rename_perm (σ : Equiv.Perm Loc) {e : Expr} {ℓ : Loc} :
    (e.rename σ).Occ (σ ℓ) ↔ e.Occ ℓ := by
  rw [Expr.occ_rename]
  exact ⟨fun ⟨k, h, e⟩ => σ.injective e ▸ h, fun h => ⟨ℓ, h, rfl⟩⟩

theorem named_rename (σ : Equiv.Perm Loc) {μ : Heap} {e : Expr} {ℓ : Loc} :
    Named (μ.rename σ) (e.rename σ) (σ ℓ) ↔ Named μ e ℓ := by
  unfold Named
  rw [Heap.rename_apply, occ_rename_perm]
  refine or_congr (by cases μ ℓ <;> simp) (or_congr Iff.rfl ⟨?_, ?_⟩)
  · rintro ⟨k, w, hk, hw⟩
    obtain ⟨u, hu, rfl⟩ : ∃ u, μ (σ.symm k) = some u ∧ u.rename σ = w := by
      simp only [BoLo.Heap.rename, Option.map_eq_some_iff] at hk; exact hk
    exact ⟨σ.symm k, u, hu, (occ_rename_perm σ).mp (by simpa using hw)⟩
  · rintro ⟨k, u, hk, hu⟩
    exact ⟨σ k, u.rename σ, by simp [hk], by simpa using (occ_rename_perm σ).mpr hu⟩

/-- A renaming that fixes every location `K[e]` mentions fixes `K`. -/
theorem Kont.rename_eq_self {τ : Loc → Loc} :
    ∀ (K : Kont) (e : Expr), (∀ ℓ, (K.plug e).Occ ℓ → τ ℓ = ℓ) → K.rename τ = K
  | .hole, _, _ => rfl
  | .pairL K e₂, e, h | .letpair K e₂, e, h | .seq K e₂, e, h => by
      simp only [Kont.rename, Kont.rename_eq_self K e (fun ℓ o => h ℓ (Or.inl o)),
        Expr.rename_eq_self e₂ (fun ℓ o => h ℓ (Or.inr o))]
  | .pairR v K, e, h => by
      simp only [Kont.rename, Kont.rename_eq_self K e (fun ℓ o => h ℓ (Or.inr o))]
      exact congrArg₂ _ (Subtype.ext (Expr.rename_eq_self _ (fun ℓ o => h ℓ (Or.inl o)))) rfl
  | .appR f K, e, h => by
      simp only [Kont.rename, Kont.rename_eq_self K e (fun ℓ o => h ℓ (Or.inr o)),
        Expr.rename_eq_self f (fun ℓ o => h ℓ (Or.inl o))]
  | .appL K v, e, h => by
      simp only [Kont.rename, Kont.rename_eq_self K e (fun ℓ o => h ℓ (Or.inl o))]
      exact congrArg₂ _ rfl (Subtype.ext (Expr.rename_eq_self _ (fun ℓ o => h ℓ (Or.inr o))))
  | .case K e₁ e₂, e, h => by
      simp only [Kont.rename, Kont.rename_eq_self K e (fun ℓ o => h ℓ (Or.inl o)),
        Expr.rename_eq_self e₁ (fun ℓ o => h ℓ (Or.inr (Or.inl o))),
        Expr.rename_eq_self e₂ (fun ℓ o => h ℓ (Or.inr (Or.inr o)))]
  | .inj₁ K, e, h | .inj₂ K, e, h => by
      simp only [Kont.rename, Kont.rename_eq_self K e h]

theorem Kont.occ_plug {ℓ : Loc} {e : Expr} : ∀ (K : Kont), e.Occ ℓ → (K.plug e).Occ ℓ
  | .hole, h => h
  | .pairL K _, h | .letpair K _, h | .seq K _, h | .case K _ _, h | .appL K _, h =>
      Or.inl (Kont.occ_plug K h)
  | .pairR _ K, h | .appR _ K, h => Or.inr (Kont.occ_plug K h)
  | .inj₁ K, h | .inj₂ K, h => Kont.occ_plug K h

/-- Swapping two locations a heap neither holds nor mentions leaves it unchanged. -/
theorem Heap.rename_swap_eq_self {μ : Heap} {x y : Loc} (hx : μ x = none) (hy : μ y = none)
    (hv : ∀ k w, μ k = some w → ¬ w.1.Occ x ∧ ¬ w.1.Occ y) :
    μ.rename (Equiv.swap x y) = μ := by
  funext k
  simp only [BoLo.Heap.rename, Equiv.symm_swap]
  by_cases kx : k = x
  · subst kx; rw [Equiv.swap_apply_left, hy, hx]; rfl
  by_cases ky : k = y
  · subst ky; rw [Equiv.swap_apply_right, hx, hy]; rfl
  rw [Equiv.swap_apply_of_ne_of_ne kx ky]
  cases hk : μ k with
  | none => rfl
  | some w =>
      refine congrArg some (Subtype.ext (Expr.rename_eq_self _ fun ℓ o => ?_))
      obtain ⟨n₁, n₂⟩ := hv k w hk
      exact Equiv.swap_apply_of_ne_of_ne (fun e => n₁ (e ▸ o)) (fun e => n₂ (e ▸ o))

/-! ### One step -/

theorem not_allocRedex_rename (σ : Loc → Loc) {a : Expr} (hna : ∀ v : Val, a ≠ allocRedex v) :
    ∀ v : Val, a.rename σ ≠ allocRedex v := by
  intro v h
  cases a with
  | app f x =>
      simp only [Expr.rename, allocRedex, Expr.app.injEq] at h
      obtain ⟨h₁, h₂⟩ := h
      cases f with
      | prim p =>
          simp only [Expr.rename, Expr.val, Val.prim, Expr.prim.injEq] at h₁
          have hx : IsVal x := isVal_of_rename σ (h₂ ▸ v.2)
          exact hna ⟨x, hx⟩ (by rw [h₁]; rfl)
      | _ => simp [Expr.rename, Val.prim] at h₁
  | _ => simp [Expr.rename, allocRedex] at h

/-- The head steps of an allocation redex. -/
theorem head_alloc_inv {μ μ' : Heap} {a a' : Expr} (h : Head μ a μ' a') {v : Val}
    (ha : a = allocRedex v) : ∃ ℓ, μ ℓ = none ∧ μ' = μ.upd ℓ v ∧ a' = .val (.loc ℓ) := by
  cases h with
  | alloc w ℓ hℓ =>
      simp only [allocRedex, Expr.app.injEq] at ha
      obtain rfl : w = v := Subtype.ext ha.2
      exact ⟨ℓ, hℓ, rfl, rfl⟩
  | _ => simp_all [allocRedex, Expr.val, Val.prim, Val.lam]

/-- **One fresh step, simulated.**  A fresh step from `(μ, e)` and a fresh step from its
renaming `(σ μ, σ e)` end in configurations related by a permutation. -/
theorem step1F_sim {σ : Equiv.Perm Loc} {μ μ' μB : Heap} {e e' eB : Expr}
    (hA : Step1F μ e μ' e') (hB : Step1F (μ.rename σ) (e.rename σ) μB eB) :
    ∃ σ' : Equiv.Perm Loc, μB = μ'.rename σ' ∧ eB = e'.rename σ' := by
  obtain ⟨⟨K, a, a', rfl, rfl, hh⟩, hfA⟩ := hA
  obtain ⟨⟨K', b, b', hE, rfl, hhB⟩, hfB⟩ := hB
  have hh' := BoLo.head_rename σ hh
  rw [BoLo.Kont.rename_plug] at hE
  obtain ⟨K'', hb, rfl⟩ := Fig16.LogRel.Core.plug_decomp hhB (K.rename σ) K' hh'.not_isVal hE
  obtain rfl : K'' = .hole := Fig16.LogRel.Core.head_plug hh' K'' hhB.not_isVal hb
  simp only [Kont.plug] at hb
  subst hb
  rw [BoLo.Kont.plug_comp]
  simp only [Kont.plug]
  by_cases hal : ∃ v, a = allocRedex v
  · obtain ⟨v, rfl⟩ := hal
    obtain ⟨ℓA, hℓA, rfl, rfl⟩ := head_alloc_inv hh rfl
    obtain ⟨ℓB, hℓB, rfl, rfl⟩ := head_alloc_inv hhB (v := v.rename σ) rfl
    have nA := hfA ℓA (by simp) hℓA
    have nB := hfB ℓB (by simp) hℓB
    have nA' : ¬ Named (μ.rename σ) ((K.plug (allocRedex v)).rename σ) (σ ℓA) :=
      fun h => nA ((named_rename σ).mp h)
    rw [BoLo.Kont.rename_plug] at nA' nB
    set τ := Equiv.swap (σ ℓA) ℓB
    have hfix : ∀ ℓ, ((K.rename σ).plug ((allocRedex v).rename σ)).Occ ℓ → τ ℓ = ℓ :=
      fun ℓ o => Equiv.swap_apply_of_ne_of_ne (fun e => nA' (.inr (.inl (e ▸ o))))
        (fun e => nB (.inr (.inl (e ▸ o))))
    have hv : (v.rename σ).rename τ = v.rename σ :=
      Subtype.ext (Expr.rename_eq_self _ fun ℓ o =>
        hfix ℓ (Kont.occ_plug _ (show (Expr.app _ _).Occ ℓ from Or.inr o)))
    refine ⟨τ * σ, ?_, ?_⟩
    · rw [← BoLo.Heap.rename_mul, BoLo.Heap.rename_upd, BoLo.Heap.rename_upd,
        Heap.rename_swap_eq_self (by simpa using hℓA) hℓB
          (fun k w hk => ⟨fun o => nA' (.inr (.inr ⟨k, w, hk, o⟩)),
            fun o => nB (.inr (.inr ⟨k, w, hk, o⟩))⟩), hv, Equiv.swap_apply_left]
    · rw [Equiv.Perm.coe_mul, ← Expr.rename_comp, BoLo.Kont.rename_plug, BoLo.Kont.rename_plug,
        Kont.rename_eq_self _ _ hfix]
      simp only [Expr.rename, Expr.val, Val.loc, τ, Equiv.swap_apply_left]
  · push Not at hal
    obtain ⟨rfl, rfl⟩ := head_det hh' hhB (not_allocRedex_rename σ hal)
    exact ⟨σ, rfl, (BoLo.Kont.rename_plug σ K a').symm⟩

/-! ### Fresh runs -/

theorem not_step1_of_isVal {μ μ' : Heap} {e e' : Expr} (h : IsVal e) : ¬ Step1 μ e μ' e' :=
  BoLo.no_step_val (w := ⟨e, h⟩)

/-- Fresh runs to values from a configuration and from its renaming end in configurations
related by a permutation. -/
theorem freshRun_sim {μ μ' : Heap} {e e' : Expr} (hA : FreshRun μ e μ' e') :
    IsVal e' → ∀ {σ : Equiv.Perm Loc} {μB : Heap} {eB : Expr},
      FreshRun (μ.rename σ) (e.rename σ) μB eB → IsVal eB →
      ∃ σ' : Equiv.Perm Loc, μB = μ'.rename σ' ∧ eB = e'.rename σ' := by
  induction hA with
  | refl μ e =>
      intro hv σ μB eB hB _
      cases hB with
      | refl => exact ⟨σ, rfl, rfl⟩
      | more h _ => exact absurd h.1 (not_step1_of_isVal (hv.rename σ))
  | more hs _ ih =>
      intro hv σ μB eB hB hvB
      cases hB with
      | refl => exact absurd hs.1 (not_step1_of_isVal (isVal_of_rename σ hvB))
      | more h t =>
          obtain ⟨σ₁, rfl, rfl⟩ := step1F_sim hs h
          exact ih hv t hvB

/-- **Fresh runs are deterministic up to renaming.**  Two fresh runs to values from one
configuration end in heaps and values that a permutation of the locations relates. -/
theorem freshRun_det {μ μ₁ μ₂ : Heap} {e : Expr} {v₁ v₂ : Val}
    (h₁ : FreshRun μ e μ₁ v₁.1) (h₂ : FreshRun μ e μ₂ v₂.1) :
    ∃ σ : Equiv.Perm Loc, μ₂ = μ₁.rename σ ∧ v₂ = v₁.rename σ := by
  have h₂' : FreshRun (μ.rename 1) (e.rename (1 : Equiv.Perm Loc)) μ₂ v₂.1 := by
    rw [BoLo.Heap.rename_one, Equiv.Perm.coe_one, Expr.rename_id]; exact h₂
  obtain ⟨σ, h, hv⟩ := freshRun_sim h₁ v₁.2 h₂' v₂.2
  exact ⟨σ, h, Subtype.ext hv⟩

end BoCa.Fig16.LogRel.Core.TwoRun

end
