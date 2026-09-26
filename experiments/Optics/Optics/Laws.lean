import Optics.Lens

/-!
# Optics — the accessor laws, as equations between runs  (stage 1)

`over m f = lift m (Λ. λmv. let (mv′, t) = withswap mv f; forget mv′; t)` runs `f : V ⊸ V ⊗ T`
on the focus of the cell `m`, through the lens.  Its runs are characterised exactly
(`steps_over_iff`): `f` runs on the focus cell's content, its first component is stored in the
focus cell, and the source cell gets back the value it held.

The laws are Marshall–Orchard's `&unit` and `&assoc` (`withBorrow id ≡ id`,
`withBorrow (f ∘ g) ≡ withBorrow f ∘ withBorrow g`) at a pure function, each an `↔` between
runs, so each holds on every run:

* `over_id`: `over ℓ (λv. (v, ()))` runs to `(ℓ, ())` and leaves the heap as it was;
* `over_fuse`: two `over`s in sequence run exactly as one `over` of the sequenced function.

A function `f` is pure at `(φ₁, φ₂)` when every run of `f v` changes nothing and returns
`(φ₁ v, φ₂ v)` (`PureFn`).  At an effectful `f` the laws need a frame condition on the callback
that typing gives and the bare machine does not.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Optics
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Kont)
open BoCa.Programs (app2)

attribute [local simp] Expr.subst Expr.shift Val.val_shift Expr.shift_zero

/-- `setCb f` with `f` substituted. -/
def setCbV (f : Val) : Val :=
  .lam (.val (.lam (.letpair (app2 withswap (.var 0) f.1) (.seq (.app forget (.var 1)) (.var 0)))))

theorem setCbV_closed {f : Val} (hf : closedAt 0 f.1 = true) : closedAt 0 (setCbV f).1 = true := by
  simp [setCbV, app2, withswap, lam2, forget, unit', v0, v1, v3, load', store', closedAt,
    closedAt_mono _ hf (Nat.zero_le _)]

/-- The callback `over` hands the lens: `withswap` on the focus cell. -/
theorem steps_setCb_iff {μ μ₁ : Heap} {f z t : Val} (hf : closedAt 0 f.1 = true)
    (hz : closedAt 0 z.1 = true) :
    Steps μ (app2 (setCbV f).1 unit' z.1) μ₁ t.1 ↔
      ∃ (ℓ' : Loc) (v : Val) (μ₂ : Heap) (v' : Val), z = .loc ℓ' ∧ μ ℓ' = some v ∧
        Steps μ (.app f.1 v.1) μ₂ (Val.pair v' t).1 ∧ (∃ u, μ₂ ℓ' = some u) ∧
        μ₁ = μ₂.upd ℓ' v' := by
  rw [show (setCbV f).1 = lam2 (.letpair (app2 withswap (.var 0) f.1)
    (.seq (.app forget (.var 1)) (.var 0))) from rfl, steps_app2_unit_iff]
  have e : ((Expr.letpair (app2 withswap (.var 0) f.1)
      (.seq (.app forget (.var 1)) (.var 0))).subst 1 (Val.unit.shift 1 0)).subst 0 z
      = .letpair (app2 withswap z.1 f.1) (.seq (.app forget (.var 1)) (.var 0)) := by
    simp [app2, withswap, lam2, forget, unit', v0, v1, v3, load', store', closed_subst hf,
      closed_subst hz, closed_shift hf]
  rw [e, steps_forgetFst_iff]
  constructor
  · rintro ⟨m, h⟩
    obtain ⟨ℓ, v, μ₂, v', t', rfl, hℓ, hf', hd, rfl, hw⟩ := (steps_withswap_iff hz).mp h
    obtain rfl : t = t' := by
      have := congrArg Subtype.val hw
      simp only [Val.val_pair, Expr.pair.injEq] at this
      exact Subtype.ext this.2
    exact ⟨ℓ, v, μ₂, v', rfl, hℓ, hf', hd, rfl⟩
  · rintro ⟨ℓ, v, μ₂, v', rfl, hℓ, hf', hd, rfl⟩
    exact ⟨.loc ℓ, (steps_withswap_iff hz).mpr ⟨ℓ, v, μ₂, v', t, rfl, hℓ, hf', hd, rfl, rfl⟩⟩

section accessor
variable {S V : VTy} (L : Lens (fun _ => S) (fun c => .mut c V)) (Dom : Val → Prop)
  (foc : Val → Val) (hL : L.Obs = LensObs Dom foc)
  (hfoc : ∀ s, closedAt 0 s.1 = true → Dom s → closedAt 0 (foc s).1 = true)
include hL hfoc

/-- **The runs of `over`**: the source cell `ℓ` holds `s`, the focus of `s` is a cell `ℓ′`
holding `v`, `f v` runs to `(v′, t)`, `v′` goes into `ℓ′`, `s` goes back into `ℓ`, and the
result is `(ℓ, t)`. -/
theorem steps_over_iff {μ μ' : Heap} {ℓ : Loc} {f w : Val} (hμ : HeapClosed μ)
    (hf : closedAt 0 f.1 = true) :
    Steps μ (app2 (.val (overV L.run)) (Val.loc ℓ).1 f.1) μ' w.1 ↔
      ∃ (s : Val) (ℓ' : Loc) (v : Val) (μ₂ : Heap) (v' t : Val),
        μ ℓ = some s ∧ Dom s ∧ foc s = .loc ℓ' ∧ μ ℓ' = some v ∧
        Steps μ (.app f.1 v.1) μ₂ (Val.pair v' t).1 ∧ (∃ u, μ₂ ℓ' = some u) ∧
        (∃ u, (μ₂.upd ℓ' v') ℓ = some u) ∧ μ' = (μ₂.upd ℓ' v').upd ℓ s ∧
        w = .pair (.loc ℓ) t := by
  rw [show Expr.val (overV L.run) = lam2 (app2 (.val (liftV L.run)) (.var 1) (setCb (.var 2)))
    from rfl, steps_app2_iff]
  have e : ((app2 (.val (liftV L.run)) (.var 1) (setCb (.var 2))).subst 1
      ((Val.loc ℓ).shift 1 0)).subst 0 f = app2 (.val L.lift.run) (Val.loc ℓ).1 (setCbV f).1 := by
    simp [app2, setCb, setCbV, withswap, lam2, forget, unit', v0, v1, v3, load', store',
      closed_subst (liftV_closed L.closed), closed_subst hf, closed_shift hf, Optic.lift]
  rw [e, L.lift.runs hμ rfl (setCbV_closed hf)]
  simp only [Optic.lift, liftObs, hL, LensObs]
  constructor
  · rintro ⟨t, rfl, ℓ₀, s, μ₁, hℓ₀, hs, ⟨hd, hcb⟩, hdom, rfl⟩
    obtain rfl : ℓ = ℓ₀ := by simpa using hℓ₀
    obtain ⟨ℓ', v, μ₂, v', hfoc', hv, hfv, hd₂, rfl⟩ :=
      (steps_setCb_iff hf (hfoc s (hμ _ _ hs) hd)).mp hcb
    exact ⟨s, ℓ', v, μ₂, v', t, hs, hd, hfoc', hv, hfv, hd₂, hdom, rfl, rfl⟩
  · rintro ⟨s, ℓ', v, μ₂, v', t, hs, hd, hfoc', hv, hfv, hd₂, hdom, rfl, rfl⟩
    exact ⟨t, rfl, ℓ, s, _, rfl, hs,
      ⟨hd, (steps_setCb_iff hf (hfoc s (hμ _ _ hs) hd)).mpr ⟨ℓ', v, μ₂, v', hfoc', hv, hfv, hd₂, rfl⟩⟩,
      hdom, rfl⟩

end accessor

/-! ### Pure functions -/

/-- Every run of `f v` changes nothing and returns `(φ₁ v, φ₂ v)`. -/
def PureFn (f : Val) (φ₁ φ₂ : Val → Val) : Prop :=
  ∀ {μ μ' : Heap} {v w : Val}, Steps μ (.app f.1 v.1) μ' w.1 ↔ μ' = μ ∧ w = .pair (φ₁ v) (φ₂ v)

/-- `λv. (v, ())`. -/
def idF : Val := .lam (.pair (.var 0) unit')

theorem idF_pure : PureFn idF id (fun _ => .unit) := by
  intro μ μ' v w
  show Steps μ (.app (.val (Val.lam (.pair (.var 0) unit'))) v.1) μ' w.1 ↔ _
  rw [steps_beta_iff]
  simp only [Expr.subst, unit', if_true]
  exact steps_val_iff (v := Val.pair v .unit)

theorem upd_self {μ : Heap} {ℓ : Loc} {v : Val} (h : μ ℓ = some v) : μ.upd ℓ v = μ := by
  funext k
  by_cases hk : k = ℓ
  · subst hk; simp [BoLo.Heap.upd, h]
  · simp [BoLo.Heap.upd, hk]

/-- **`&unit`**: `over` at the identity leaves the heap as it was and returns `(ℓ, ())`. -/
theorem over_id {S V : VTy} (L : Lens (fun _ => S) (fun c => .mut c V)) (Dom : Val → Prop)
    (foc : Val → Val) (hL : L.Obs = LensObs Dom foc)
    (hfoc : ∀ s, closedAt 0 s.1 = true → Dom s → closedAt 0 (foc s).1 = true)
    {μ μ' : Heap} {ℓ : Loc} {w : Val} (hμ : HeapClosed μ) :
    Steps μ (app2 (.val (overV L.run)) (Val.loc ℓ).1 idF.1) μ' w.1 ↔
      (∃ s ℓ' v, μ ℓ = some s ∧ Dom s ∧ foc s = .loc ℓ' ∧ μ ℓ' = some v) ∧
        μ' = μ ∧ w = .pair (.loc ℓ) .unit := by
  rw [steps_over_iff L Dom foc hL hfoc hμ rfl]
  constructor
  · rintro ⟨s, ℓ', v, μ₂, v', t, hs, hd, hf, hv, hrun, -, -, rfl, rfl⟩
    obtain ⟨hμ₂, he⟩ := idF_pure.mp hrun
    have hvt : v' = v ∧ t = .unit := by
      have := congrArg Subtype.val he
      simp only [Val.val_pair, Expr.pair.injEq] at this
      exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
    rw [hvt.1, hvt.2, hμ₂]
    refine ⟨⟨s, ℓ', v, hs, hd, hf, hv⟩, ?_, rfl⟩
    rw [upd_self hv, upd_self hs]
  · rintro ⟨⟨s, ℓ', v, hs, hd, hf, hv⟩, rfl, rfl⟩
    refine ⟨s, ℓ', v, _, v, .unit, hs, hd, hf, hv, idF_pure.mpr ⟨rfl, rfl⟩, ⟨v, hv⟩, ?_, ?_, rfl⟩
    · rw [upd_self hv]; exact ⟨s, hs⟩
    · rw [upd_self hv, upd_self hs]

/-- `over` at a pure function: one write to the focus cell, and the source cell as it was. -/
theorem over_pure {S V : VTy} (L : Lens (fun _ => S) (fun c => .mut c V)) (Dom : Val → Prop)
    (foc : Val → Val) (hL : L.Obs = LensObs Dom foc)
    (hfoc : ∀ s, closedAt 0 s.1 = true → Dom s → closedAt 0 (foc s).1 = true)
    {f : Val} {φ₁ φ₂ : Val → Val} (hf : closedAt 0 f.1 = true) (hp : PureFn f φ₁ φ₂)
    {μ μ' : Heap} {ℓ ℓ' : Loc} {s v w : Val} (hμ : HeapClosed μ) (hs : μ ℓ = some s)
    (hd : Dom s) (hfs : foc s = .loc ℓ') (hv : μ ℓ' = some v) :
    Steps μ (app2 (.val (overV L.run)) (Val.loc ℓ).1 f.1) μ' w.1 ↔
      μ' = (μ.upd ℓ' (φ₁ v)).upd ℓ s ∧ w = .pair (.loc ℓ) (φ₂ v) := by
  rw [steps_over_iff L Dom foc hL hfoc hμ hf]
  constructor
  · rintro ⟨s₀, ℓ₀, v₀, μ₂, v', t, hs₀, -, hf₀, hv₀, hrun, -, -, rfl, rfl⟩
    obtain rfl : s₀ = s := Option.some.inj (hs₀.symm.trans hs)
    obtain rfl : ℓ₀ = ℓ' := by simpa [hfs] using hf₀.symm
    obtain rfl : v₀ = v := Option.some.inj (hv₀.symm.trans hv)
    obtain ⟨rfl, he⟩ := hp.mp hrun
    have := congrArg Subtype.val he
    simp only [Val.val_pair, Expr.pair.injEq] at this
    rw [show v' = φ₁ v₀ from Subtype.ext this.1, show t = φ₂ v₀ from Subtype.ext this.2]
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨s, ℓ', v, μ, φ₁ v, φ₂ v, hs, hd, hfs, hv, hp.mpr ⟨rfl, rfl⟩, ⟨v, hv⟩, ?_, rfl, rfl⟩
    by_cases h : ℓ = ℓ'
    · subst h; exact ⟨φ₁ v, by simp [BoLo.Heap.upd]⟩
    · exact ⟨s, by simp [BoLo.Heap.upd, h, hs]⟩

/-- `λv. let (v₁, t) = f v; let (v₂, u) = g v₁; (v₂, (t, u))`. -/
def seqF (f g : Val) : Val :=
  .lam (.letpair (.app f.1 (.var 0))
    (.letpair (.app g.1 (.var 1)) (.pair (.var 1) (.pair (.var 2) (.var 0)))))

theorem seqF_closed {f g : Val} (hf : closedAt 0 f.1 = true) (hg : closedAt 0 g.1 = true) :
    closedAt 0 (seqF f g).1 = true := by
  simp [seqF, closedAt, closedAt_mono _ hf (Nat.zero_le _), closedAt_mono _ hg (Nat.zero_le _)]

/-- Sequencing two pure functions is pure. -/
theorem seqF_pure {f g : Val} {φ₁ φ₂ ψ₁ ψ₂ : Val → Val} (hf : closedAt 0 f.1 = true)
    (hg : closedAt 0 g.1 = true) (hpf : PureFn f φ₁ φ₂) (hpg : PureFn g ψ₁ ψ₂)
    (hφ : ∀ v, closedAt 0 (φ₂ v).1 = true) :
    PureFn (seqF f g) (fun v => ψ₁ (φ₁ v)) (fun v => .pair (φ₂ v) (ψ₂ (φ₁ v))) := by
  intro μ μ' v w
  show Steps μ (.app (.val (Val.lam (.letpair (.app f.1 (.var 0))
    (.letpair (.app g.1 (.var 1)) (.pair (.var 1) (.pair (.var 2) (.var 0))))))) v.1) μ' w.1 ↔ _
  rw [steps_beta_iff]
  have e₁ : Expr.subst 0 v (.letpair (.app f.1 (.var 0))
      (.letpair (.app g.1 (.var 1)) (.pair (.var 1) (.pair (.var 2) (.var 0)))))
      = .letpair (.app f.1 v.1)
          (.letpair (.app g.1 (.var 1)) (.pair (.var 1) (.pair (.var 2) (.var 0)))) := by
    simp [closed_subst hf, closed_subst hg]
  rw [e₁, steps_letpairK_iff]
  have e₂ : ∀ a b : Val, ((Expr.letpair (.app g.1 (.var 1))
      (.pair (.var 1) (.pair (.var 2) (.var 0)))).subst 0 (b.shift 1 0)).subst 0 a
      = .letpair (.app g.1 a.1) (.pair (.var 1) (.pair (b.shift 2 0).1 (.var 0))) := fun a b => by
    simp [closed_subst hg, fun s => Expr.subst_shift 2 0 2 s b.1 (Nat.zero_le _) (by omega), Expr.shift_shift]
  have e₃ : ∀ b c d : Val, closedAt 0 b.1 = true →
      (((Expr.pair (.var 1) (.pair (b.shift 2 0).1 (.var 0))).subst 0 (d.shift 1 0)).subst 0 c)
      = (Val.pair c (.pair b d)).1 := fun b c d hb => by
    simp [closed_shift hb, closed_subst hb, Expr.subst_shift 0 0 0 c d.1 (le_refl _) (le_refl _)]
  constructor
  · rintro ⟨μm, p, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := hpf.mp h₁
    rw [steps_letpair_iff, e₂, steps_letpairK_iff] at h₂
    obtain ⟨μn, q, h₃, h₄⟩ := h₂
    obtain ⟨rfl, rfl⟩ := hpg.mp h₃
    rw [steps_letpair_iff, e₃ _ _ _ (hφ v)] at h₄
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₄
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨_, _, hpf.mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_letpair_iff, e₂, steps_letpairK_iff]
    refine ⟨_, _, hpg.mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_letpair_iff, e₃ _ _ _ (hφ v)]
    exact .refl _ _

/-- `let (m, t) = over ℓ f; let (m′, u) = over m g; (m′, (t, u))`. -/
def twiceE (run : Val) (ℓ : Loc) (f g : Val) : Expr :=
  .letpair (app2 (.val (overV run)) (Val.loc ℓ).1 f.1)
    (.letpair (app2 (.val (overV run)) (.var 1) g.1) (.pair (.var 1) (.pair (.var 2) (.var 0))))

/-- **`&assoc` (fusion)**: two `over`s in sequence run exactly as one `over` of the sequenced
function, when the source cell and the focus cell are distinct. -/
theorem over_fuse {S V : VTy} (L : Lens (fun _ => S) (fun c => .mut c V)) (Dom : Val → Prop)
    (foc : Val → Val) (hL : L.Obs = LensObs Dom foc)
    (hfoc : ∀ s, closedAt 0 s.1 = true → Dom s → closedAt 0 (foc s).1 = true)
    {f g : Val} {φ₁ φ₂ ψ₁ ψ₂ : Val → Val} (hf : closedAt 0 f.1 = true)
    (hg : closedAt 0 g.1 = true) (hpf : PureFn f φ₁ φ₂) (hpg : PureFn g ψ₁ ψ₂)
    (hφ₁ : ∀ v, closedAt 0 (φ₁ v).1 = true) (hφ₂ : ∀ v, closedAt 0 (φ₂ v).1 = true)
    {μ μ' : Heap} {ℓ ℓ' : Loc} {s v w : Val} (hμ : HeapClosed μ) (hs : μ ℓ = some s)
    (hd : Dom s) (hfs : foc s = .loc ℓ') (hv : μ ℓ' = some v) (hne : ℓ ≠ ℓ') :
    Steps μ (twiceE L.run ℓ f g) μ' w.1 ↔
      Steps μ (app2 (.val (overV L.run)) (Val.loc ℓ).1 (seqF f g).1) μ' w.1 := by
  rw [over_pure L Dom foc hL hfoc (seqF_closed hf hg) (seqF_pure hf hg hpf hpg hφ₂) hμ hs hd hfs hv,
    twiceE, steps_letpairK_iff]
  have hne' : ℓ' ≠ ℓ := Ne.symm hne
  set μ₁ := (μ.upd ℓ' (φ₁ v)).upd ℓ s with hμ₁
  have hμ₁ℓ : μ₁ ℓ = some s := by simp [hμ₁, BoLo.Heap.upd]
  have hμ₁ℓ' : μ₁ ℓ' = some (φ₁ v) := by simp [hμ₁, BoLo.Heap.upd, hne']
  have hc₁ : HeapClosed μ₁ := by
    intro k u hk
    simp only [hμ₁, BoLo.Heap.upd] at hk
    split_ifs at hk with h₁ h₂
    · cases hk; exact hμ _ _ hs
    · cases hk; exact hφ₁ v
    · exact hμ _ _ hk
  have e₂ : ∀ t : Val, ((Expr.letpair (app2 (.val (overV L.run)) (.var 1) g.1)
      (.pair (.var 1) (.pair (.var 2) (.var 0)))).subst 0 (t.shift 1 0)).subst 0 (Val.loc ℓ)
      = .letpair (app2 (.val (overV L.run)) (Val.loc ℓ).1 g.1)
          (.pair (.var 1) (.pair (t.shift 2 0).1 (.var 0))) := fun t => by
    simp [app2, closed_subst (show closedAt 0 (overV L.run).1 = true by
        simp [overV, setCb, app2, withswap, lam2, forget, unit', v0, v1, v3, load', store',
          closedAt, closedAt_mono _ (liftV_closed L.closed) (Nat.zero_le _)]),
      closed_subst hg, fun s => Expr.subst_shift 2 0 2 s t.1 (Nat.zero_le _) (by omega),
      Expr.shift_shift]
  have e₃ : ∀ b d : Val, closedAt 0 b.1 = true →
      (((Expr.pair (.var 1) (.pair (b.shift 2 0).1 (.var 0))).subst 0 (d.shift 1 0)).subst 0
        (Val.loc ℓ)) = (Val.pair (.loc ℓ) (.pair b d)).1 := fun b d hb => by
    simp [closed_shift hb, closed_subst hb,
      Expr.subst_shift 0 0 0 (Val.loc ℓ) d.1 (le_refl _) (le_refl _)]
  have hμ₂ : (μ₁.upd ℓ' (ψ₁ (φ₁ v))).upd ℓ s = (μ.upd ℓ' (ψ₁ (φ₁ v))).upd ℓ s := by
    funext k
    simp only [hμ₁, BoLo.Heap.upd]
    split_ifs <;> rfl
  constructor
  · rintro ⟨μm, p, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := (over_pure L Dom foc hL hfoc hf hpf hμ hs hd hfs hv).mp h₁
    rw [steps_letpair_iff, e₂, steps_letpairK_iff] at h₂
    obtain ⟨μn, q, h₃, h₄⟩ := h₂
    obtain ⟨rfl, rfl⟩ := (over_pure L Dom foc hL hfoc hg hpg hc₁ hμ₁ℓ hd hfs hμ₁ℓ').mp h₃
    rw [steps_letpair_iff, e₃ _ _ (hφ₂ v)] at h₄
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₄
    exact ⟨hμ₂, rfl⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨μ₁, _, (over_pure L Dom foc hL hfoc hf hpf hμ hs hd hfs hv).mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_letpair_iff, e₂, steps_letpairK_iff]
    refine ⟨_, _, (over_pure L Dom foc hL hfoc hg hpg hc₁ hμ₁ℓ hd hfs hμ₁ℓ').mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_letpair_iff, e₃ _ _ (hφ₂ v), hμ₂]
    exact .refl _ _

end BoCa.Fig16.LogRel.Core.Optics

end
