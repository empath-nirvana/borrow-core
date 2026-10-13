import ProbeD1.GapWitness

/-!
# ProbeD1 — `TyEq` reads no room: `TyEqInst` at every type (`GAP.md` §2)

`TyEq` and `CTyEq` (`Core/FrameRecords.lean`) are conjunctions of syntactic equalities and of
equalities `@aδ = @a′δ′` of lifetime terms, under one unbounded `∀` at `∀'x ⊏ @b. C`. On a chain an
equality is decided threshold by threshold, and a lifetime term commutes with the two-point
collapse at a threshold. So `TyEq` holds at every pair of readings whose threshold patterns are
those of `TyEq` pairs, and an instantiation, which only spreads lifetimes apart, keeps it.

* **The collapse** (`interpCollapse`, `eqOfCollapse`): `collapseN t` is monotone and fixes `⊤`, so
  it commutes with every lifetime term (`interp_mapN_mono`); two readings every collapse equates
  are equal.
* **The cover** (`tyEq_of_cover`, `cTyEq_of_cover`, `tyEqOfCover`): `TyEq` holds at every pair a
  family of `TyEq` pairs covers. At `∀` the family is extended at the binder by every lifetime; at
  each threshold the bound variable's pattern is met by `⊤` or by a lifetime just below the
  threshold (`cover_extend`). The member may change with the threshold, and that is where the
  factorisation through one source lifetime, which adjacency blocks, is not needed.
* **Instantiations are covers** (`coverInst`): a threshold of the image is met by the source's
  largest lifetime the instantiation sends at or above it (`collapse_comp_strictMono`). With the
  cover, **`TyEqInst` at every type** (`tyEqInst`).
* **A gap instance is covered by the image instances** (`coverGap`), which gives the step the
  fixed-instantiation induction could not take (`tyEqGapStep`).
* **`TyEq` is invariant, both ways, under every embedding fixing `⊤`** (`tyEqRoomBlind`), the
  embeddings that open a gap included. Contrast `coreAllNotNatural`, where Core's relation is not.

No printed proof governs `TyEq`, which is ours (`[about ours]`). The technique built is the
threshold cover; it reads only equalities of lifetime terms and the unbounded `∀`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The collapse -/

theorem collapseN_monotone (t : ℕ) : Monotone (collapseN t) := by
  intro a b h
  unfold collapseN
  split_ifs <;> omega

@[simp] theorem collapseN_zero (t : ℕ) : collapseN t 0 = 0 := by
  simp [collapseN]

theorem collapseN_of_le {t n : ℕ} (h : n ≤ t) : collapseN t n = 0 := by
  simp [collapseN, h]

theorem collapseN_of_lt {t n : ℕ} (h : t < n) : collapseN t n = 1 := by
  simp [collapseN, not_le.mpr h]

/-- **A monotone map fixing `⊤` commutes with every lifetime term**: `Restrat.Emb.interp_mapN`'s
argument, which reads only monotonicity and `⊤`. -/
theorem interp_mapN_mono {g : ℕ → ℕ} (hg : Monotone g) (h0 : g 0 = 0) (δ : LSub) :
    ∀ a : Lifetime.Life, a.interp (Restrat.LSub.mapN g δ) = (a.interp δ).map g
  | .var x => Restrat.LSub.find?_mapN g δ x
  | .top => by simp [Lifetime.Life.interp, Lifetime.SLife.top, h0]
  | .join a b => by
      simp only [Lifetime.Life.interp, interp_mapN_mono hg h0 δ a, interp_mapN_mono hg h0 δ b]
      cases a.interp δ <;> cases b.interp δ <;>
        simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some,
          Lifetime.SLife.join]
      exact congrArg some hg.map_min.symm
  | .meet a b => by
      simp only [Lifetime.Life.interp, interp_mapN_mono hg h0 δ a, interp_mapN_mono hg h0 δ b]
      cases a.interp δ <;> cases b.interp δ <;>
        simp only [Option.map_none, Option.map_some, Option.bind_none, Option.bind_some,
          Lifetime.SLife.meet]
      exact congrArg some hg.map_max.symm

/-- **A lifetime term commutes with the collapse.** -/
theorem interpCollapse : InterpCollapse := fun a t δ =>
  interp_mapN_mono (collapseN_monotone t) (collapseN_zero t) δ a

/-- **Two readings every collapse equates are equal**: the collapse at the longer of two distinct
lifetimes separates them. -/
theorem eqOfCollapse : EqOfCollapse := by
  intro o o' h
  cases o with
  | none =>
      cases o' with
      | none => rfl
      | some n' => exact absurd (h 0) (by simp)
  | some n =>
      cases o' with
      | none => exact absurd (h 0) (by simp)
      | some n' =>
          congr 1
          by_contra hne
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · have h₁ := h n
            simp only [Option.map_some, Option.some.injEq] at h₁
            rw [collapseN_of_le le_rfl, collapseN_of_lt hlt] at h₁
            exact absurd h₁ (by decide)
          · have h₁ := h n'
            simp only [Option.map_some, Option.some.injEq] at h₁
            rw [collapseN_of_le le_rfl, collapseN_of_lt hlt] at h₁
            exact absurd h₁ (by decide)

/-! ### The cover -/

/-- **An equation of lifetime terms holds at every pair a family of pairs satisfying it covers.**
`eqOfCollapse`, then at each threshold the member the cover gives, read through
`interpCollapse` on both sides. -/
theorem interp_eq_of_cover {S : LSub → LSub → Prop} {s₂ s₂' : LSub} (hc : TyCover S s₂ s₂')
    (a a' : Lifetime.Life) (h : ∀ s₁ s₁', S s₁ s₁' → a.interp s₁ = a'.interp s₁') :
    a.interp s₂ = a'.interp s₂' := by
  apply eqOfCollapse
  intro t₂
  obtain ⟨s₁, s₁', hm, t₁, hy⟩ := hc t₂
  rw [← interpCollapse, ← interpCollapse]
  have e₁ : a.interp (Restrat.LSub.mapN (collapseN t₂) s₂) =
      a.interp (Restrat.LSub.mapN (collapseN t₁) s₁) :=
    interp_congr a fun y _ => by
      rw [Restrat.LSub.find?_mapN, Restrat.LSub.find?_mapN]; exact (hy y).1
  have e₂ : a'.interp (Restrat.LSub.mapN (collapseN t₂) s₂') =
      a'.interp (Restrat.LSub.mapN (collapseN t₁) s₁') :=
    interp_congr a' fun y _ => by
      rw [Restrat.LSub.find?_mapN, Restrat.LSub.find?_mapN]; exact (hy y).2
  rw [e₁, e₂, interpCollapse, interpCollapse, h s₁ s₁' hm]

/-- A reading extended at the front by a lifetime, looked up. -/
theorem find?_extendL (δ : LSub) (x y : LifeVar) (v : Life) :
    (δ.extend x v).find? y = if x = y then some (OrderDual.ofDual v) else δ.find? y :=
  LSub.find?_extend δ x v y

/-- The family of the members extended at the binder by every lifetime. -/
def extFam (S : LSub → LSub → Prop) (x x' : LifeVar) (r r' : LSub) : Prop :=
  ∃ (s₁ s₁' : LSub) (α : Life), S s₁ s₁' ∧ r = s₁.extend x α ∧ r' = s₁'.extend x' α

/-- **The extended family covers the pair extended by any one lifetime**: at a threshold, the
bound variable's pattern is `⊤`'s when it is at or above the threshold, and otherwise that of the
lifetime just below the member's threshold. -/
theorem cover_extend {S : LSub → LSub → Prop} {s₂ s₂' : LSub} (hc : TyCover S s₂ s₂')
    (x x' : LifeVar) (β : Life) :
    TyCover (extFam S x x') (s₂.extend x β) (s₂'.extend x' β) := by
  intro t₂
  obtain ⟨s₁, s₁', hm, t₁, hy⟩ := hc t₂
  let α : ℕ := if OrderDual.ofDual β ≤ t₂ then 0 else t₁ + 1
  have hα : collapseN t₂ (OrderDual.ofDual β) = collapseN t₁ α := by
    by_cases hβ : OrderDual.ofDual β ≤ t₂
    · simp only [α, if_pos hβ, collapseN_of_le hβ, collapseN_zero]
    · simp only [α, if_neg hβ, collapseN_of_lt (not_le.mp hβ),
        collapseN_of_lt (Nat.lt_succ_self t₁)]
  refine ⟨s₁.extend x (OrderDual.toDual α), s₁'.extend x' (OrderDual.toDual α),
    ⟨s₁, s₁', OrderDual.toDual α, hm, rfl, rfl⟩, t₁, fun y => ⟨?_, ?_⟩⟩
  · rw [find?_extendL, find?_extendL]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos hxy]; exact congrArg some hα
    · rw [if_neg hxy, if_neg hxy]; exact (hy y).1
  · rw [find?_extendL, find?_extendL]
    by_cases hxy : x' = y
    · rw [if_pos hxy, if_pos hxy]; exact congrArg some hα
    · rw [if_neg hxy, if_neg hxy]; exact (hy y).2

mutual
/-- **`TyEq` holds at every pair a family of `TyEq` pairs covers.** By the type, mutually with
`CTyEq`: an equation by `interp_eq_of_cover`, a syntactic atom at any member, a conjunction
componentwise, and `∀` at the extended family (`cover_extend`). -/
theorem tyEq_of_cover : ∀ (A : VTy) {B : VTy} {S : LSub → LSub → Prop} {s₂ s₂' : LSub},
    (∀ s₁ s₁', S s₁ s₁' → TyEq A s₁ B s₁') → TyCover S s₂ s₂' → TyEq A s₂ B s₂'
  | .unit, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      have h := hS s₁ s₁' hm
      cases B <;> simp only [TyEq] at h ⊢
  | .zero, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      have h := hS s₁ s₁' hm
      cases B <;> simp only [TyEq] at h ⊢
  | .unk, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      have h := hS s₁ s₁' hm
      cases B <;> simp only [TyEq] at h ⊢
  | .int _, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      have h := hS s₁ s₁' hm
      cases B <;> simp only [TyEq] at h ⊢
      exact h
  | .opq _, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      have h := hS s₁ s₁' hm
      cases B <;> simp only [TyEq] at h ⊢
      exact h
  | .tvar _, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      have h := hS s₁ s₁' hm
      cases B <;> simp only [TyEq] at h ⊢
      exact h
  | .tensor A₁ A₂, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case tensor B₁ B₂ =>
        exact ⟨tyEq_of_cover A₁ (fun r r' h => (hS r r' h).1) hc,
          tyEq_of_cover A₂ (fun r r' h => (hS r r' h).2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
  | .sum A₁ A₂, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case sum B₁ B₂ =>
        exact ⟨tyEq_of_cover A₁ (fun r r' h => (hS r r' h).1) hc,
          tyEq_of_cover A₂ (fun r r' h => (hS r r' h).2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
  | .thunk C, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case thunk D => exact cTyEq_of_cover C (fun r r' h => hS r r' h) hc
      all_goals exact (hS s₁ s₁' hm).elim
  | .ref A, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case ref B => exact tyEq_of_cover A (fun r r' h => hS r r' h) hc
      all_goals exact (hS s₁ s₁' hm).elim
  | .bang A, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case bang B => exact tyEq_of_cover A (fun r r' h => hS r r' h) hc
      all_goals exact (hS s₁ s₁' hm).elim
  | .mu A, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case mu B => exact tyEq_of_cover A (fun r r' h => hS r r' h) hc
      all_goals exact (hS s₁ s₁' hm).elim
  | .fam A, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case fam B => exact tyEq_of_cover A (fun r r' h => hS r r' h) hc
      all_goals exact (hS s₁ s₁' hm).elim
  | .box a A, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case box a' B =>
        exact ⟨interp_eq_of_cover hc a a' (fun r r' h => (hS r r' h).1),
          tyEq_of_cover A (fun r r' h => (hS r r' h).2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
  | .imm a A, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case imm a' B =>
        exact ⟨interp_eq_of_cover hc a a' (fun r r' h => (hS r r' h).1),
          tyEq_of_cover A (fun r r' h => (hS r r' h).2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
  | .mut a A, B, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases B
      case «mut» a' B =>
        exact ⟨interp_eq_of_cover hc a a' (fun r r' h => (hS r r' h).1),
          tyEq_of_cover A (fun r r' h => (hS r r' h).2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
/-- **`CTyEq` holds at every pair a family of `CTyEq` pairs covers.** -/
theorem cTyEq_of_cover : ∀ (C : CTy) {D : CTy} {S : LSub → LSub → Prop} {s₂ s₂' : LSub},
    (∀ s₁ s₁', S s₁ s₁' → CTyEq C s₁ D s₁') → TyCover S s₂ s₂' → CTyEq C s₂ D s₂'
  | .ret A, D, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases D
      case ret B => exact tyEq_of_cover A (fun r r' h => hS r r' h) hc
      all_goals exact (hS s₁ s₁' hm).elim
  | .arr A C, D, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases D
      case arr B D =>
        exact ⟨tyEq_of_cover A (fun r r' h => (hS r r' h).1) hc,
          cTyEq_of_cover C (fun r r' h => (hS r r' h).2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
  | .amp C₁ C₂, D, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases D
      case amp D₁ D₂ =>
        exact ⟨cTyEq_of_cover C₁ (fun r r' h => (hS r r' h).1) hc,
          cTyEq_of_cover C₂ (fun r r' h => (hS r r' h).2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
  | .top, D, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      have h := hS s₁ s₁' hm
      cases D <;> simp only [CTyEq] at h ⊢
  | .nu C, D, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases D
      case nu D => exact cTyEq_of_cover C (fun r r' h => hS r r' h) hc
      all_goals exact (hS s₁ s₁' hm).elim
  | .all x b C, D, S, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases D
      case all x' b' D =>
        refine ⟨interp_eq_of_cover hc b b' (fun r r' h => (hS r r' h).1), fun β => ?_⟩
        refine cTyEq_of_cover C (S := extFam S x x') ?_ (cover_extend hc x x' β)
        rintro r r' ⟨r₁, r₁', α, h, rfl, rfl⟩
        exact (hS r₁ r₁' h).2 α
      all_goals exact (hS s₁ s₁' hm).elim
  | .eff n i q A B C, D, _, _, _, hS, hc => by
      obtain ⟨s₁, s₁', hm, -⟩ := hc 0
      cases D
      case eff n' i' q' A' B' D =>
        have h := hS s₁ s₁' hm
        exact ⟨h.1, h.2.1, h.2.2.1, tyEq_of_cover A (fun r r' h => (hS r r' h).2.2.2.1) hc,
          tyEq_of_cover B (fun r r' h => (hS r r' h).2.2.2.2.1) hc,
          cTyEq_of_cover C (fun r r' h => (hS r r' h).2.2.2.2.2) hc⟩
      all_goals exact (hS s₁ s₁' hm).elim
end

theorem tyEqOfCover : TyEqOfCover :=
  ⟨fun A _ _ _ _ hS hc => tyEq_of_cover A hS hc, fun C _ _ _ _ hS hc => cTyEq_of_cover C hS hc⟩

/-! ### Instantiations are covers -/

/-- **A strictly monotone map fixing `⊤` sends every threshold back to a threshold**: the largest
`n` it sends at or below `t₂`. -/
theorem collapse_comp_strictMono {g : ℕ → ℕ} (hg : StrictMono g) (h0 : g 0 = 0) (t₂ : ℕ) :
    ∃ t₁, ∀ n, collapseN t₂ (g n) = collapseN t₁ n := by
  have hex : ∃ n, t₂ < g (n + 1) := ⟨t₂, lt_of_lt_of_le (Nat.lt_succ_self t₂) (hg.id_le _)⟩
  classical
  refine ⟨Nat.find hex, fun n => ?_⟩
  have key : g n ≤ t₂ ↔ n ≤ Nat.find hex := by
    constructor
    · intro h
      by_contra hn
      have h₁ : Nat.find hex + 1 ≤ n := Nat.succ_le_of_lt (not_le.mp hn)
      exact absurd (lt_of_lt_of_le (Nat.find_spec hex) (hg.monotone h₁)) (not_lt.mpr h)
    · intro h
      cases n with
      | zero => rw [h0]; exact Nat.zero_le _
      | succ k => exact not_lt.mp (Nat.find_min hex (Nat.lt_of_succ_le h))
  unfold collapseN
  by_cases h : g n ≤ t₂
  · rw [if_pos h, if_pos (key.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (key.mpr h'))]

/-- An instantiation's action on the naturals that carry `Life`: strictly monotone, fixing `⊤`. -/
theorem inst_toNat (ι : Inst) :
    ∃ g : ℕ → ℕ, StrictMono g ∧ g 0 = 0 ∧ ∀ δ : LSub, ι.sub δ = Restrat.LSub.mapN g δ := by
  rcases ι with _ | ⟨c, θ⟩
  · refine ⟨id, strictMono_id, rfl, fun δ => ?_⟩
    show δ = Restrat.LSub.mapN id δ
    cases δ with
    | mk entries =>
        show (⟨entries⟩ : LSub) = ⟨entries.map fun p => (p.1, p.2)⟩
        simp
  · exact ⟨θ.toNat, θ.toNat_strictMono, θ.toNat_zero, fun _ => rfl⟩

/-- **An instantiated pair is covered by its source.** -/
theorem coverInst : CoverInst := by
  intro s s' ι t₂
  obtain ⟨g, hg, h0, hsub⟩ := inst_toNat ι
  obtain ⟨t₁, ht⟩ := collapse_comp_strictMono hg h0 t₂
  refine ⟨s, s', ⟨rfl, rfl⟩, t₁, fun y => ⟨?_, ?_⟩⟩
  · rw [hsub, Restrat.LSub.find?_mapN, Option.map_map]
    exact Option.map_congr fun n _ => ht n
  · rw [hsub, Restrat.LSub.find?_mapN, Option.map_map]
    exact Option.map_congr fun n _ => ht n

/-- **`TyEqInst` at every type.** -/
theorem tyEqInst : TyEqInst := fun A _ s s' ι h =>
  tyEq_of_cover A (S := fun r r' => r = s ∧ r' = s')
    (fun r r' hm => by obtain ⟨rfl, rfl⟩ := hm; exact h) (coverInst s s' ι)

/-- **`CTyEq` is kept by an instantiation**, at every computation type. -/
theorem cTyEq_inst (C D : CTy) (s s' : LSub) (ι : Inst) (h : CTyEq C s D s') :
    CTyEq C (ι.sub s) D (ι.sub s') :=
  cTyEq_of_cover C (S := fun r r' => r = s ∧ r' = s')
    (fun r r' hm => by obtain ⟨rfl, rfl⟩ := hm; exact h) (coverInst s s' ι)

/-! ### The gap step -/

/-- An instantiation fixes `⊤`. -/
theorem Inst.life1_top (ι : Inst) : ι.life1 ⊤ = ⊤ := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · exact θ.map_top

/-- **A gap instance is covered by the image instances**: at a threshold, the image of `⊤`, or of
the lifetime just below the threshold, which an instantiation keeps below it. -/
theorem coverGap : CoverGap := by
  intro x x' s s' ι α' t₂
  let α : Life := if OrderDual.ofDual α' ≤ t₂ then ⊤ else OrderDual.toDual (t₂ + 1)
  have hα : collapseN t₂ (OrderDual.ofDual α') =
      collapseN t₂ (OrderDual.ofDual (ι.life1 α)) := by
    by_cases hβ : OrderDual.ofDual α' ≤ t₂
    · have e : ι.life1 α = ⊤ := by simp only [α, if_pos hβ]; exact ι.life1_top
      rw [e, collapseN_of_le hβ]
      exact (collapseN_of_le (Nat.zero_le _)).symm
    · have hle : t₂ + 1 ≤ OrderDual.ofDual (ι.life1 α) := by
        have := ι.life1_le α
        simp only [α, if_neg hβ] at this ⊢
        exact this
      rw [collapseN_of_lt (not_le.mp hβ), collapseN_of_lt (Nat.lt_of_succ_le hle)]
  refine ⟨(ι.sub s).extend x (ι.life1 α), (ι.sub s').extend x' (ι.life1 α), ⟨α, rfl, rfl⟩, t₂,
    fun y => ⟨?_, ?_⟩⟩
  · rw [find?_extendL, find?_extendL]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos hxy]; exact congrArg some hα
    · rw [if_neg hxy, if_neg hxy]
  · rw [find?_extendL, find?_extendL]
    by_cases hxy : x' = y
    · rw [if_pos hxy, if_pos hxy]; exact congrArg some hα
    · rw [if_neg hxy, if_neg hxy]

/-- **The step the fixed-instantiation induction could not take**: from the instances at the image
of `ι` to every instance, those in `ι`'s gap among them. -/
theorem tyEqGapStep : TyEqGapStep := by
  intro C C' x x' s s' ι h α'
  refine cTyEq_of_cover C (S := fun r r' => ∃ α : Life, r = (ι.sub s).extend x (ι.life1 α) ∧
    r' = (ι.sub s').extend x' (ι.life1 α)) ?_ (coverGap x x' s s' ι α')
  rintro r r' ⟨α, rfl, rfl⟩
  exact h α

/-! ### Every embedding fixing `⊤` -/

/-- **`TyEq` is invariant, both ways, under every embedding fixing `⊤`**: forwards, an
embedding at `⊤` is an instantiation; backwards, a threshold of the source is the image of its own
image's threshold. -/
theorem tyEqRoomBlind : TyEqRoomBlind := by
  intro A B s s' φ
  constructor
  · exact tyEqInst A B s s' (Inst.ofEmb φ)
  · intro h
    refine tyEq_of_cover A (S := fun r r' => r = Restrat.LSub.mapN φ.toNat s ∧
      r' = Restrat.LSub.mapN φ.toNat s') (fun r r' hm => by obtain ⟨rfl, rfl⟩ := hm; exact h) ?_
    intro t₂
    have ht : ∀ n, collapseN (φ.toNat t₂) (φ.toNat n) = collapseN t₂ n := by
      intro n
      simp only [collapseN, φ.toNat_strictMono.le_iff_le]
    refine ⟨_, _, ⟨rfl, rfl⟩, φ.toNat t₂, fun y => ⟨?_, ?_⟩⟩
    · rw [Restrat.LSub.find?_mapN, Option.map_map]
      exact Option.map_congr fun n _ => (ht n).symm
    · rw [Restrat.LSub.find?_mapN, Option.map_map]
      exact Option.map_congr fun n _ => (ht n).symm

end ProbeD1

end
