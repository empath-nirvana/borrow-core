import ProbeD1.R1Mono

/-!
# ProbeD1 — the three obligations the binder unit left (`R1MONO.md` §3)

* **`OuterBelowTop` at every lend** (`outerBelowTopPush`, `outerBelowTopFresh`,
  `outerBelowTopArises`): a lend pushed below a bound is below `⊤`, and every configuration of the
  revised arising set has its outermost lend below `⊤`, from H4's consequence that `LendMutI` and
  `LendImmI` now carry.
* **`RetainedPay` row by row** (§3.2): the lend's view, the transports across a push, a pop and a
  binding, a leaf's payload type a part of the slot's (`leafPos_vFree`, `payLeavesOfPayExt`), the
  slice borrows outside W at two or more elements (`sliceGuardFails`, `retainedPaySliceRow`, both
  vacuous at the guard), and `InternalPayloadArises`'s shape refuting no read-out
  (`readOutAtInternalPayload`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView)

/-! ### §3.1 `OuterBelowTop` at every lend -/

/-- Pushing a lend below `⊤` keeps the outermost lend below `⊤`. -/
theorem outerBelowTop_cons {αs : List Life} {a : Life} (h : OuterBelowTop αs) (ha : a < ⊤) :
    OuterBelowTop (a :: αs) := by
  intro o ho
  cases αs with
  | nil =>
      obtain rfl : o = a := (Option.some.inj ho).symm
      exact ha
  | cons b bs =>
      have : (a :: b :: bs).getLast? = (b :: bs).getLast? := List.getLast?_cons_cons
      rw [this] at ho
      exact h o ho

/-- **`OuterBelowTopPush`**: a lend pushed below a bound (`LtLife`) is below `⊤`. -/
theorem outerBelowTopPush : OuterBelowTopPush := by
  intro αs a s c h ⟨β, _, hlt⟩
  exact outerBelowTop_cons h (lt_of_lt_of_le hlt le_top)

/-- **`OuterBelowTopFresh`**: a lend chosen below a lifetime ([TR] 6.64's and 6.65's H4) is below
`⊤`. -/
theorem outerBelowTopFresh : OuterBelowTopFresh := fun _ _ _ h hlt =>
  outerBelowTop_cons h (lt_of_lt_of_le hlt le_top)

/-- **`OuterBelowTopArises`**: by induction on the revised arising set. A run, a part and a hiding
keep the lifetimes; a lend pushes its lifetime, below `⊤` by H4's consequence. -/
theorem outerBelowTopArises : OuterBelowTopArises (ℍ := ℍ) := by
  intro c h
  refine ArisesI.rec (motive_1 := fun c _ => OuterBelowTop c.αs)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    ?nil ?run ?part ?lendMut ?lendImm ?hide (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) h
  case nil =>
    intro fρ ρf ρ ps ls _ _ _ _ o ho
    simp at ho
  case run =>
    intro c c' Δ Γ e₀ j γ t _ _ _ hR ih _
    rw [hR.2.1]; exact ih
  case part =>
    intro c ρ₁ ρ₂ ρf' _ _ _ _ ih
    exact ih
  case lendMut =>
    intro c c' e _ hL ih
    obtain ⟨⟨-, -, -, -, -, -, -, α, -, -, -, -, -, -, -, -, hαs, -⟩, -, htop⟩ := hL
    rw [hαs] at htop ⊢
    exact outerBelowTop_cons ih (htop α rfl)
  case lendImm =>
    intro c c' e _ hL ih
    obtain ⟨⟨-, -, -, -, α, -, -, -, -, -, -, -, -, -, hαs, -⟩, -, htop⟩ := hL
    rw [hαs] at htop ⊢
    exact outerBelowTop_cons ih (htop α rfl)
  case hide =>
    intro c N _ ih
    exact ih

/-! ### §3.2 `RetainedPay`: the view and the transports -/

/-- **`RetainedPayViewRow`**: at the pushed stack the lend's view is at the pushed entry's place,
which the pushed entry lends; `RetainedPay` is vacuous there. -/
theorem retainedPayViewRow : RetainedPayViewRow := by
  intro σ αs s e α T l hl hi
  cases hl
  rw [innerAt_cons, if_pos rfl] at hi
  exact absurd hi (by simp)

/-- **`RetainedPayPop`**: at the end of a lend the cut is the same or gone, and the reading agrees
off the ended variable. -/
theorem retainedPayPop : RetainedPayPop := by
  intro σ αs δ e a T v hok hx hne h l hv hi y hy m hm hint
  have hyx : e.x ≠ y := fun he => hx (he ▸ hy)
  have hi' : innerAt (e :: σ) (a :: αs) l = none := by
    rw [innerAt_cons, if_neg (fun he => hne l hv he.symm)]; exact hi
  refine h l hv hi' y hy m (by rw [extS_push_find δ e σ a αs hyx]; exact hm) ?_
  obtain ⟨c, hc, hlt⟩ := hint
  refine ⟨c, ?_, hlt⟩
  cases αs with
  | nil => simp [cutOf] at hc
  | cons b bs =>
      have : (a :: b :: bs).getLast? = (b :: bs).getLast? := List.getLast?_cons_cons
      simp only [cutOf, this] at hc ⊢
      exact hc

/-- **`RetainedPayExtend`**: a binding the payload type does not read, new to the stack, leaves its
readings alone. -/
theorem retainedPayExtend : RetainedPayExtend := by
  intro σ αs δ x a T v hσ hx h l hv hi y hy m hm
  have hyx : x ≠ y := fun he => hx (he ▸ hy)
  refine h l hv hi y hy m ?_
  rw [extS_find_base (X := δ) (X' := δ.extend x a) (find?_extend_ne δ a hyx).symm σ αs]
  exact hm

/-! ### §3.2 A leaf's payload type is a part of the slot's -/

/-- **A leaf's payload type reads only the slot type's variables**: through every former `LeafPos`
crosses, the unrolling of a `μ` by `vFree_subst`. -/
theorem leafPos_vFree {R : WRes} {T : VTy} {v : Val} {l : BoCa.Loc} {S : VTy} {y : LifeVar}
    (h : LeafPos R T v l S) (hy : VFree y S) : VFree y T := by
  induction h with
  | «mut» a S l => exact Or.inr hy
  | imm a S l => exact Or.inr hy
  | tensorL _ ih => exact Or.inl (ih hy)
  | tensorR _ ih => exact Or.inr (ih hy)
  | sumL _ ih => exact Or.inl (ih hy)
  | sumR _ ih => exact Or.inr (ih hy)
  | bang _ ih => exact ih hy
  | box _ ih => exact Or.inr (ih hy)
  | ref _ _ ih => exact ih hy
  | @mu A _ _ _ _ _ ih =>
      rcases vFree_subst A _ (ih hy) with h | ⟨n, hn⟩
      · exact h
      · cases n with
        | zero => exact hn
        | succ n => exact hn.elim
  | fam _ _ ih => exact ih hy

/-- **`PayLeavesOfPayExt`**: a payload type read at external lifetimes covers its leaves. -/
theorem payLeavesOfPayExt : PayLeavesOfPayExt := by
  intro σ αs s R T v hp l S hl l' hv _ y hy m hm
  exact hp y (leafPos_vFree hl hy) m hm

/-- **`ReadOutAtInternalPayload`**: at `InternalPayloadArises`'s shape, `x`'s payload type
`Imm 'b 1` has one leaf, whose payload type `1` reads nothing. -/
theorem readOutAtInternalPayload : ReadOutAtInternalPayload := by
  intro s R u l S hl
  cases hl with
  | imm a S l => exact retainedPay_of_closed (fun y hy => hy)

/-! ### §3.2 The slice borrows: outside W at two or more elements -/

/-- **`SliceGuardFails`**: two of the family's cells are at distinct places, one of which the pushed
entry does not lend; the table puts it strictly above the outermost lend, while it is at the
innermost. -/
theorem sliceGuardFails : SliceGuardFails := by
  intro σ αs en α ρ ℓ n hok h2 hσ hcells ht
  obtain ⟨o, ho⟩ : ∃ o, (α :: αs).getLast? = some o := by
    cases h : (α :: αs).getLast? with
    | none => simp at h
    | some o => exact ⟨o, rfl⟩
  have hαo : α ≤ o := GhostEnd.head_le_last hok.2.1 o ho
  -- one of the first two places is not the pushed entry's
  obtain ⟨i, hi, hie⟩ : ∃ i < n, ℓ + i ≠ en.l := by
    by_cases h0 : ℓ + 0 = en.l
    · refine ⟨1, by omega, fun h1 => ?_⟩
      have : ℓ + 1 = ℓ + 0 := h1.trans h0.symm
      simp at this
    · exact ⟨0, by omega, h0⟩
  obtain ⟨ψ, hψ, hk, hat⟩ := hcells i hi
  have hnot : ℓ + i ∉ (en :: σ).map LEnt.l := by
    rw [List.map_cons, List.mem_cons, not_or]
    exact ⟨hie, hσ i hi⟩
  have := lt_at_of_inStratum (ht.2 o ho (ℓ + i) ψ hnot hψ) hk
  rw [hat] at this
  exact absurd hαo (not_le.mpr this)

/-- **`RetainedPaySliceRow`, vacuous at every count**: at an element the pushed stack does not
lend, the table puts its cell strictly above the outermost lend, while it is at the own lend's
lifetime; at an element it lends, `RetainedPay` is vacuous. It is no evidence that a slice row is
covered: at two or more elements the guard fails (`sliceGuardFails`). -/
theorem retainedPaySliceRow : RetainedPaySliceRow (ℍ := ℍ) := by
  intro Δ Γ C δ σ αs ls ρ A ℓ n x c L D ρc en α ρa hidx _ _ _ _ _ hpush _ _ hcells ht _ i hi l hl
    hin
  cases hl
  obtain ⟨_, _, _, _, _, _, hoi, _, _⟩ := hpush
  obtain ⟨o, ho⟩ : ∃ o, (α :: αs).getLast? = some o := by
    cases h : (α :: αs).getLast? with
    | none => simp at h
    | some o => exact ⟨o, rfl⟩
  have hαo : α ≤ o := GhostEnd.head_le_last hoi.chain o ho
  obtain ⟨ψ, hψ, hk, hat⟩ := hcells i hi
  have hnot : ℓ + i ∉ (en :: σ).map LEnt.l := by
    intro hm
    obtain ⟨e', α', he'⟩ := innerAt_isSome (σ := en :: σ) (αs := α :: αs)
      (by simp [hidx.2.2.1.1]) hm
    rw [hin] at he'; exact absurd he' (by simp)
  have := lt_at_of_inStratum (ht.2 o ho (ℓ + i) ψ hnot hψ) hk
  rw [hat] at this
  exact absurd hαo (not_le.mpr this)


/-! ### §3.2 The nested `Mut` leaf of a bound view: through `CohS`'s `TyEq` -/

/-- **`LeafPosTyEq`**: `TyEq` is positional, so a leaf's position on one side is a leaf's position
on the other, at the same place, the payload types one type up to the readings. At a `μ` the
unrollings are `TyEq` (`TyEq.inst`) and closed together (`TyEq.Cl_iff`). -/
theorem leafPosTyEq : LeafPosTyEq := by
  intro R T T' s s' v l S hT h
  induction h generalizing T' with
  | «mut» a S l =>
      cases T' <;> simp only [TyEq] at hT
      exact ⟨_, LeafPos.mut _ _ l, hT.2⟩
  | imm a S l =>
      cases T' <;> simp only [TyEq] at hT
      exact ⟨_, LeafPos.imm _ _ l, hT.2⟩
  | tensorL _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT.1
      exact ⟨S', LeafPos.tensorL h', hS⟩
  | tensorR _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT.2
      exact ⟨S', LeafPos.tensorR h', hS⟩
  | sumL _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT.1
      exact ⟨S', LeafPos.sumL h', hS⟩
  | sumR _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT.2
      exact ⟨S', LeafPos.sumR h', hS⟩
  | bang _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT
      exact ⟨S', LeafPos.bang h', hS⟩
  | box _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT.2
      exact ⟨S', LeafPos.box h', hS⟩
  | ref hg _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT
      exact ⟨S', LeafPos.ref hg h', hS⟩
  | @mu A _ _ _ hcl _ ih =>
      cases T' with
      | mu A' =>
          simp only [TyEq] at hT
          have hM : TyEq (VTy.mu A) s (VTy.mu A') s' := hT
          obtain ⟨S', h', hS⟩ := ih _ (TyEq.inst hT hM)
          exact ⟨S', LeafPos.mu ((TyEq.Cl_iff (.mu A) 0 hM).mp hcl) h', hS⟩
      | _ => simp only [TyEq] at hT
  | fam hi _ ih =>
      cases T' <;> simp only [TyEq] at hT
      obtain ⟨S', h', hS⟩ := ih _ hT
      exact ⟨S', LeafPos.fam hi h', hS⟩

/-- A lifetime term with no join reads each of its variables at a lifetime at least as long as its
own: its value is the shortest of its variables' values, or `⊤`. -/
theorem noJoinL_le {s : LSub} : ∀ {a : Lifetime.Life} {n : ℕ}, NoJoinL a →
    a.interp s = some n → ∀ {y : LifeVar} {m : ℕ}, a.mentions y = true → s.find? y = some m →
      m ≤ n
  | .var z, n, _, ha, y, m, hy, hm => by
      simp only [Lifetime.Life.mentions, beq_iff_eq] at hy
      subst hy
      rw [Lifetime.Life.interp_var, hm] at ha
      exact le_of_eq (Option.some.inj ha)
  | .top, _, _, _, _, _, hy, _ => by simp [Lifetime.Life.mentions] at hy
  | .join _ _, _, h, _, _, _, _, _ => h.elim
  | .meet a b, n, h, ha, y, m, hy, hm => by
      simp only [Lifetime.Life.interp] at ha
      cases hea : a.interp s with
      | none => rw [hea] at ha; simp at ha
      | some na =>
          cases heb : b.interp s with
          | none => rw [hea, heb] at ha; simp at ha
          | some nb =>
              rw [hea, heb] at ha
              simp only [Option.bind_some, Option.some.injEq] at ha
              subst ha
              simp only [Lifetime.Life.mentions, Bool.or_eq_true] at hy
              show m ≤ max na nb
              rcases hy with hy | hy
              · exact le_trans (noJoinL_le h.1 hea hy hm) (le_max_left _ _)
              · exact le_trans (noJoinL_le h.2 heb hy hm) (le_max_right _ _)

/-- A lifetime term every variable of which is read at a lifetime not internal to the stack has a
value not internal to it: `⊤`, a meet and a join of such values are such values. -/
theorem interp_not_internal {αs : List Life} {s : LSub} : ∀ {a : Lifetime.Life} {n : ℕ},
    (∀ y m, a.mentions y = true → s.find? y = some m → ¬ Internal αs (OrderDual.toDual m)) →
    a.interp s = some n → ¬ Internal αs (OrderDual.toDual n)
  | .var z, n, h, ha => by
      rw [Lifetime.Life.interp_var] at ha
      exact h z n (by simp [Lifetime.Life.mentions]) ha
  | .top, n, _, ha => by
      rw [Lifetime.Life.interp_top] at ha
      obtain rfl := (Option.some.inj ha).symm
      rintro ⟨c, -, hc⟩
      exact absurd hc (not_lt.mpr le_top)
  | .join a b, n, h, ha => by
      simp only [Lifetime.Life.interp] at ha
      cases hea : a.interp s with
      | none => rw [hea] at ha; simp at ha
      | some na =>
          cases heb : b.interp s with
          | none => rw [hea, heb] at ha; simp at ha
          | some nb =>
              rw [hea, heb] at ha
              simp only [Option.bind_some, Option.some.injEq] at ha
              subst ha
              have h₁ := interp_not_internal (a := a)
                (fun y m hy hm => h y m (by simp [Lifetime.Life.mentions, hy]) hm) hea
              have h₂ := interp_not_internal (a := b)
                (fun y m hy hm => h y m (by simp [Lifetime.Life.mentions, hy]) hm) heb
              show ¬ Internal αs (OrderDual.toDual (min na nb))
              rcases le_total na nb with hle | hle
              · rw [min_eq_left hle]; exact h₁
              · rw [min_eq_right hle]; exact h₂
  | .meet a b, n, h, ha => by
      simp only [Lifetime.Life.interp] at ha
      cases hea : a.interp s with
      | none => rw [hea] at ha; simp at ha
      | some na =>
          cases heb : b.interp s with
          | none => rw [hea, heb] at ha; simp at ha
          | some nb =>
              rw [hea, heb] at ha
              simp only [Option.bind_some, Option.some.injEq] at ha
              subst ha
              have h₁ := interp_not_internal (a := a)
                (fun y m hy hm => h y m (by simp [Lifetime.Life.mentions, hy]) hm) hea
              have h₂ := interp_not_internal (a := b)
                (fun y m hy hm => h y m (by simp [Lifetime.Life.mentions, hy]) hm) heb
              show ¬ Internal αs (OrderDual.toDual (max na nb))
              rcases le_total na nb with hle | hle
              · rw [max_eq_right hle]; exact h₂
              · rw [max_eq_left hle]; exact h₁

/-- A term every variable of which is read is read. -/
theorem interp_defined {s : LSub} : ∀ {a : Lifetime.Life},
    (∀ y, a.mentions y = true → ∃ m, s.find? y = some m) → ∃ n, a.interp s = some n
  | .var z, h => h z (by simp [Lifetime.Life.mentions])
  | .top, _ => ⟨_, rfl⟩
  | .join a b, h => by
      obtain ⟨na, hna⟩ := interp_defined (a := a) (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))
      obtain ⟨nb, hnb⟩ := interp_defined (a := b) (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))
      exact ⟨BoCa.Lifetime.SLife.join na nb,
        by simp only [Lifetime.Life.interp, hna, hnb, Option.bind_some]⟩
  | .meet a b, h => by
      obtain ⟨na, hna⟩ := interp_defined (a := a) (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))
      obtain ⟨nb, hnb⟩ := interp_defined (a := b) (fun y hy => h y (by simp [Lifetime.Life.mentions, hy]))
      exact ⟨BoCa.Lifetime.SLife.meet na nb,
        by simp only [Lifetime.Life.interp, hna, hnb, Option.bind_some]⟩

/-- **The step at one lifetime term**: a term with no join, its variables read, `TyEq` to a term
whose variables are read at lifetimes not internal to the stack, reads its variables at lifetimes
not internal to it. -/
theorem lifeTerm_payExt {αs : List Life} {s s' : LSub} {a a' : Lifetime.Life}
    (heq : a.interp s = a'.interp s') (hnj : NoJoinL a)
    (hdef : ∀ y, a.mentions y = true → ∃ m, s.find? y = some m)
    (hext : ∀ y m, a'.mentions y = true → s'.find? y = some m → ¬ Internal αs (OrderDual.toDual m))
    {y : LifeVar} {m : ℕ} (hy : a.mentions y = true) (hm : s.find? y = some m) :
    ¬ Internal αs (OrderDual.toDual m) := by
  obtain ⟨n, hn⟩ := interp_defined hdef
  have hle := noJoinL_le hnj hn hy hm
  have hn' : ¬ Internal αs (OrderDual.toDual n) := interp_not_internal hext (heq ▸ hn)
  rintro ⟨c, hc, hlt⟩
  exact hn' ⟨c, hc, lt_of_le_of_lt (show OrderDual.toDual n ≤ OrderDual.toDual m from hle) hlt⟩

/-- `PayExt` at a computation type. -/
def PayExtC (αs : List Life) (s : LSub) (C : CTy) : Prop :=
  ∀ y, CFree y C → ∀ m, s.find? y = some m → ¬ Internal αs (OrderDual.toDual m)

/-- The value `⊤` a bound variable is read at is not internal. -/
theorem top_not_internal (αs : List Life) : ¬ Internal αs (OrderDual.toDual 0) := by
  rintro ⟨c, -, hc⟩
  exact absurd hc (not_lt.mpr le_top)

mutual
/-- **`PayExtOfTyEq` at two readings**: by induction on the type, each lifetime term by
`lifeTerm_payExt`; under a `∀` the two readings are extended at the binders by `⊤`, which no stack
makes internal. -/
theorem payExt_of_tyEq : ∀ (S : VTy) {S' : VTy} {s s' : LSub} {αs : List Life},
    TyEq S s S' s' → NoJoinV S → (∀ y, VFree y S → ∃ m, s.find? y = some m) →
    PayExt αs s' S' → PayExt αs s S
  | .unit, _, _, _, _, _, _, _, _ => fun _ hy => hy.elim
  | .zero, _, _, _, _, _, _, _, _ => fun _ hy => hy.elim
  | .unk, _, _, _, _, _, _, _, _ => fun _ hy => hy.elim
  | .int _, _, _, _, _, _, _, _, _ => fun _ hy => hy.elim
  | .opq _, _, _, _, _, _, _, _, _ => fun _ hy => hy.elim
  | .tvar _, _, _, _, _, _, _, _, _ => fun _ hy => hy.elim
  | .tensor A B, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      rename_i A' B'
      intro y hy m hm
      rcases hy with hy | hy
      · exact payExt_of_tyEq A h.1 hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z hz => hext z (Or.inl hz)) y hy m hm
      · exact payExt_of_tyEq B h.2 hnj.2 (fun z hz => hdef z (Or.inr hz))
          (fun z hz => hext z (Or.inr hz)) y hy m hm
  | .sum A B, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      rename_i A' B'
      intro y hy m hm
      rcases hy with hy | hy
      · exact payExt_of_tyEq A h.1 hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z hz => hext z (Or.inl hz)) y hy m hm
      · exact payExt_of_tyEq B h.2 hnj.2 (fun z hz => hdef z (Or.inr hz))
          (fun z hz => hext z (Or.inr hz)) y hy m hm
  | .ref A, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      exact payExt_of_tyEq A h hnj hdef hext
  | .bang A, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      exact payExt_of_tyEq A h hnj hdef hext
  | .fam A, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      exact payExt_of_tyEq A h hnj hdef hext
  | .mu A, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      exact payExt_of_tyEq A h hnj hdef hext
  | .box a A, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      intro y hy m hm
      rcases hy with hy | hy
      · exact lifeTerm_payExt h.1 hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z m' hz hm' => hext z (Or.inl hz) m' hm') hy hm
      · exact payExt_of_tyEq A h.2 hnj.2 (fun z hz => hdef z (Or.inr hz))
          (fun z hz => hext z (Or.inr hz)) y hy m hm
  | .imm a A, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      intro y hy m hm
      rcases hy with hy | hy
      · exact lifeTerm_payExt h.1 hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z m' hz hm' => hext z (Or.inl hz) m' hm') hy hm
      · exact payExt_of_tyEq A h.2 hnj.2 (fun z hz => hdef z (Or.inr hz))
          (fun z hz => hext z (Or.inr hz)) y hy m hm
  | .mut a A, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      intro y hy m hm
      rcases hy with hy | hy
      · exact lifeTerm_payExt h.1 hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z m' hz hm' => hext z (Or.inl hz) m' hm') hy hm
      · exact payExt_of_tyEq A h.2 hnj.2 (fun z hz => hdef z (Or.inr hz))
          (fun z hz => hext z (Or.inr hz)) y hy m hm
  | .thunk C, S', _, _, _, h, hnj, hdef, hext => by
      cases S' <;> simp only [TyEq] at h
      exact payExtC_of_cTyEq C h hnj hdef hext
theorem payExtC_of_cTyEq : ∀ (C : CTy) {C' : CTy} {s s' : LSub} {αs : List Life},
    CTyEq C s C' s' → NoJoinC C → (∀ y, CFree y C → ∃ m, s.find? y = some m) →
    PayExtC αs s' C' → PayExtC αs s C
  | .ret A, C', _, _, _, h, hnj, hdef, hext => by
      cases C' <;> simp only [CTyEq] at h
      exact payExt_of_tyEq A h hnj hdef hext
  | .arr A D, C', _, _, _, h, hnj, hdef, hext => by
      cases C' <;> simp only [CTyEq] at h
      intro y hy m hm
      rcases hy with hy | hy
      · exact payExt_of_tyEq A h.1 hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z hz => hext z (Or.inl hz)) y hy m hm
      · exact payExtC_of_cTyEq D h.2 hnj.2 (fun z hz => hdef z (Or.inr hz))
          (fun z hz => hext z (Or.inr hz)) y hy m hm
  | .amp D E, C', _, _, _, h, hnj, hdef, hext => by
      cases C' <;> simp only [CTyEq] at h
      intro y hy m hm
      rcases hy with hy | hy
      · exact payExtC_of_cTyEq D h.1 hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z hz => hext z (Or.inl hz)) y hy m hm
      · exact payExtC_of_cTyEq E h.2 hnj.2 (fun z hz => hdef z (Or.inr hz))
          (fun z hz => hext z (Or.inr hz)) y hy m hm
  | .top, _, _, _, _, _, _, _, _ => fun _ hy => hy.elim
  | .nu D, C', _, _, _, h, hnj, hdef, hext => by
      cases C' <;> simp only [CTyEq] at h
      exact payExtC_of_cTyEq D h hnj hdef hext
  | .eff n i q A B D, C', _, _, _, h, hnj, hdef, hext => by
      cases C' <;> simp only [CTyEq] at h
      obtain ⟨-, -, -, hA, hB, hD⟩ := h
      intro y hy m hm
      rcases hy with hy | hy | hy
      · exact payExt_of_tyEq A hA hnj.1 (fun z hz => hdef z (Or.inl hz))
          (fun z hz => hext z (Or.inl hz)) y hy m hm
      · exact payExt_of_tyEq B hB hnj.2.1 (fun z hz => hdef z (Or.inr (Or.inl hz)))
          (fun z hz => hext z (Or.inr (Or.inl hz))) y hy m hm
      · exact payExtC_of_cTyEq D hD hnj.2.2 (fun z hz => hdef z (Or.inr (Or.inr hz)))
          (fun z hz => hext z (Or.inr (Or.inr hz))) y hy m hm
  | .all x b D, C', s, s', αs, h, hnj, hdef, hext => by
      cases C' with
      | all x' b' D' =>
          simp only [CTyEq] at h
          obtain ⟨hb, hD⟩ := h
          intro y hy m hm
          rcases hy with hy | ⟨hyx, hy⟩
          · exact lifeTerm_payExt hb hnj.1 (fun z hz => hdef z (Or.inl hz))
              (fun z m' hz hm' => hext z (Or.inl hz) m' hm') hy hm
          · have hD' := hD (OrderDual.toDual 0)
            have := payExtC_of_cTyEq D hD' hnj.2 (s := s.extend x (OrderDual.toDual 0))
              (s' := s'.extend x' (OrderDual.toDual 0)) (αs := αs)
              (fun z hz => by
                by_cases hzx : x = z
                · subst hzx; exact ⟨_, find?_extend_self _ _ _⟩
                · rw [find?_extend_ne _ _ hzx]; exact hdef z (Or.inr ⟨Ne.symm hzx, hz⟩))
              (fun z hz m' hm' => by
                by_cases hzx : x' = z
                · subst hzx
                  rw [find?_extend_self] at hm'
                  obtain rfl := (Option.some.inj hm').symm
                  exact top_not_internal αs
                · rw [find?_extend_ne _ _ hzx] at hm'
                  exact hext z (Or.inr ⟨Ne.symm hzx, hz⟩) m' hm')
            exact this y hy m (by rw [find?_extend_ne _ _ (Ne.symm hyx)]; exact hm)
      | _ => simp only [CTyEq] at h
end

/-- **`PayExtOfTyEq`.** -/
theorem payExtOfTyEq : PayExtOfTyEq :=
  fun _ _ S _ h hnj hdef hext => payExt_of_tyEq S h hnj hdef hext


/-- Renaming type variables keeps `NoJoinV`. -/
theorem noJoinV_rename : ∀ (A : VTy) (r : Nat → Nat), NoJoinV A → NoJoinV (A.rename r) := by
  intro A
  induction A using VTy.recV with
  | unit | zero | unk | int _ | opq _ | tvar _ | thunk _ => intro r h; exact h
  | tensor A B ihA ihB => intro r h; exact ⟨ihA r h.1, ihB r h.2⟩
  | sum A B ihA ihB => intro r h; exact ⟨ihA r h.1, ihB r h.2⟩
  | ref A ih => intro r h; exact ih r h
  | bang A ih => intro r h; exact ih r h
  | fam A ih => intro r h; exact ih r h
  | mu A ih => intro r h; exact ih _ h
  | box a A ih => intro r h; exact ⟨h.1, ih r h.2⟩
  | imm a A ih => intro r h; exact ⟨h.1, ih r h.2⟩
  | «mut» a A ih => intro r h; exact ⟨h.1, ih r h.2⟩

/-- Substituting types with no join keeps `NoJoinV`. -/
theorem noJoinV_subst : ∀ (A : VTy) (σ : Nat → VTy), NoJoinV A → (∀ n, NoJoinV (σ n)) →
    NoJoinV (A.subst σ) := by
  intro A
  induction A using VTy.recV with
  | unit | zero | unk | int _ | opq _ | thunk _ => intro σ h _; exact h
  | tvar n => intro σ _ hσ; exact hσ n
  | tensor A B ihA ihB => intro σ h hσ; exact ⟨ihA σ h.1 hσ, ihB σ h.2 hσ⟩
  | sum A B ihA ihB => intro σ h hσ; exact ⟨ihA σ h.1 hσ, ihB σ h.2 hσ⟩
  | ref A ih => intro σ h hσ; exact ih σ h hσ
  | bang A ih => intro σ h hσ; exact ih σ h hσ
  | fam A ih => intro σ h hσ; exact ih σ h hσ
  | mu A ih =>
      intro σ h hσ
      refine ih _ h fun n => ?_
      cases n with
      | zero => trivial
      | succ n => exact noJoinV_rename _ _ (hσ n)
  | box a A ih => intro σ h hσ; exact ⟨h.1, ih σ h.2 hσ⟩
  | imm a A ih => intro σ h hσ; exact ⟨h.1, ih σ h.2 hσ⟩
  | «mut» a A ih => intro σ h hσ; exact ⟨h.1, ih σ h.2 hσ⟩

/-- A leaf's payload type of a type with no join has none. -/
theorem noJoinV_leafPos {R : WRes} {T : VTy} {v : Val} {l : BoCa.Loc} {S : VTy}
    (h : LeafPos R T v l S) (hnj : NoJoinV T) : NoJoinV S := by
  induction h with
  | «mut» a S l => exact hnj.2
  | imm a S l => exact hnj.2
  | tensorL _ ih => exact ih hnj.1
  | tensorR _ ih => exact ih hnj.2
  | sumL _ ih => exact ih hnj.1
  | sumR _ ih => exact ih hnj.2
  | bang _ ih => exact ih hnj
  | box _ ih => exact ih hnj.2
  | ref _ _ ih => exact ih hnj
  | @mu A _ _ _ _ _ ih =>
      refine ih (noJoinV_subst A _ hnj fun n => ?_)
      cases n with
      | zero => exact hnj
      | succ n => trivial
  | fam _ _ ih => exact ih hnj

/-- **`PayLeavesOfTyEq`**: each leaf of one side is a leaf of the other at the same place
(`leafPosTyEq`), and its payload type's external readings transfer (`payExtOfTyEq`). -/
theorem payLeavesOfTyEq : PayLeavesOfTyEq := by
  intro σ αs s R T T' v hT hnj hdef hP l S hl l' hv hi
  obtain ⟨S', hl', hS⟩ := leafPosTyEq R T T' s s v l S hT hl
  exact payExtOfTyEq αs s S S' hS (noJoinV_leafPos hl hnj)
    (fun y hy => hdef y (leafPos_vFree hl hy)) (hP l S' hl' l' hv hi)

/-- **`RetainedPayLoadMutBound`**: the view's `CohS` gives `TyEq T s e.T s` at the stack's reading,
and `payLeavesOfTyEq` carries the leaves read at `e.T` to `T`. -/
theorem retainedPayLoadMutBound : RetainedPayLoadMutBound (ℍ := ℍ) := by
  intro σ αs δ ls ρ a T l ψ e α hi hnj hdef h _ hP
  rw [vRLM_mut_eq, vRLJ_mut_eq] at h
  have hTy : TyEq T (extS δ σ αs) e.T (extS δ σ αs) := ((h.2.1 l e α rfl hi).1).2
  exact payLeavesOfTyEq σ αs _ _ T e.T _ hTy hnj hdef hP

/-- **`RetainedPayLoadMutRow` at a retained view**: the view's own `RetainedPay` gives `PayExt` of
its payload type, which covers the payload's leaves. At every payload type. -/
theorem retainedPayLoadMutRow_retained {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {ρ : WRes} {a : Lifetime.Life} {T : VTy}
    {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (hi : innerAt σ αs l = none)
    (h : vRLM (ℍ := ℍ) .binder0 none σ δ (.mut a T) αs ls (.loc l) ρ) :
    PayLeaves σ αs (extS δ σ αs) ψ.wit T ψ.erase := by
  rw [vRLM_mut_eq, vRLJ_mut_eq] at h
  exact payLeavesOfPayExt σ αs _ _ T _ (h.2.2 l rfl hi)

/-- **`RetainedPayLoadMutRow` at every payload type with no join, from `EntryPayLeaves`**: at a
retained view by `retainedPayLoadMutRow_retained`; at a bound view by `retainedPayLoadMutBound`,
the leftover the entry's payload type's leaves, `EntryPayLeaves`. The payload type's variables are
read at the row's index (`Scoped`, `Δ.Models`). -/
def RetainedPayLoadMutRowNJ : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy) (δ : LSub) (σ : LStack) (αs : List Life)
    (ls : List SRec) (ρ : WRes) (a : Lifetime.Life) (T : VTy) (l : BoCa.Loc)
    (ψ : CellU BoCa.Loc Val) (W ρr : WRes) (ps rs : List FrameRec), NoJoinV T →
    SemIdxM Δ Γ C δ σ αs ls ρ → ⟨.mut a T, true⟩ ∈ Γ →
    vRLM (ℍ := ℍ) .binder0 none σ δ (.mut a T) αs ls (.loc l) ρ → ρ.get l = some ψ →
    TabAtS σ αs ψ.wit → PlaceViewsL (extS δ σ αs) σ αs ls ψ.wit →
    TW W ps rs → Tagged W ps ls → ResU.CompS ψ.wit ρr W →
    PayLeaves σ αs (extS δ σ αs) ψ.wit T ψ.erase

theorem retainedPayLoadMutRowNJ_of_entry (hE : EntryPayLeaves) :
    RetainedPayLoadMutRowNJ (ℍ := ℍ) := by
  intro Δ Γ C δ σ αs ls ρ a T l ψ W ρr ps rs hnj hidx hΓ h hψ ht hpv hT htg hc
  cases hi : innerAt σ αs l with
  | none => exact retainedPayLoadMutRow_retained hi h
  | some p =>
      obtain ⟨e, α⟩ := p
      have h' := h
      rw [vRLM_mut_eq, vRLJ_mut_eq] at h'
      have hk : e.k = .mut := by
        have hkind := ((h'.2.1 l e α rfl hi).1).1
        cases hek : e.k with
        | «mut» => rfl
        | imm u₀ => rw [hek] at hkind; exact hkind.elim
      have hdef : ∀ y, VFree y T → ∃ m, (extS δ σ αs).find? y = some m := by
        intro y hy
        obtain ⟨u, hu⟩ := hidx.2.1.2 _ hΓ rfl y (Or.inr hy)
        obtain ⟨m, -, hm, -, -⟩ := hidx.2.2.2.2.2.2.1 y u hu
        exact ⟨m, hm⟩
      exact retainedPayLoadMutBound σ αs δ ls ρ a T l ψ e α hi hnj hdef h hψ
        (hE Δ Γ C δ σ αs ls ρ l ψ e α W ρr ps rs hidx hi hk hψ ht hpv hT htg hc)

/-! ### §3.2 The variant leaf's thaw -/

/-- **`ThawLeafP`**: the variant leaf at a bound place is re-established from the view handed at
an instantiation: the first three conjuncts as at `viewSlotInstOB`'s `Mut` case, the fourth by the
handed view's leaves at `e.T`, carried to `T` by `TyEq T s e.T s` moved by `tyEqInst` and
`payLeavesOfTyEq` at the instantiated reading. -/
theorem thawLeafP : ThawLeafP (ℍ := ℍ) := by
  intro σ αs s ls ls' a T l e α ρ ρv ι hi _ _ _ _ hnj hdef h hv hPv
  obtain ⟨hvc, hcoh, -, -⟩ := h
  have hel : e.l = l := (innerAt_mem hi).2
  obtain ⟨⟨hkind, hTy⟩, hatl⟩ := hcoh l e α rfl hi
  have hk : e.k = .mut := by
    cases hek : e.k with
    | «mut» => rfl
    | imm u₀ => rw [hek] at hkind; exact hkind.elim
  have hTy' : TyEq T (ι.sub s) e.T (ι.sub s) := tyEqInst T e.T s s ι hTy
  refine ⟨vC_mut_boundK ι hel hk hTy hvc hatl hv, fun l' e' α' hl' hi' => ?_,
    retainedPay_of_bound (by rw [innerAt_inst_some ι hi]; simp), fun l' ψ hl' hψ => ?_⟩
  · cases hl'
    rw [innerAt_inst_some ι hi] at hi'
    obtain ⟨rfl, rfl⟩ : e = e' ∧ ι.life1 α = α' := by simpa using hi'
    exact ⟨⟨by rw [hk]; trivial, hTy'⟩, fun ψ hψ => (hv.2 ψ (by rw [hel]; exact hψ)).1⟩
  · cases hl'
    exact payLeavesOfTyEq σ (ι.life αs) (ι.sub s) ψ.wit T e.T ψ.erase hTy' hnj hdef
      (hPv e.l ψ rfl (by rw [hel]; exact hψ))


/-! ### §3.3 `KeepsT` at the share: the bridge to the instantiated list -/

/-- A record above the outermost lend is fixed by the stack's instantiation. -/
theorem rec1_eq_of_above {αs : List Life} {ι : Inst} (hat : InstAt αs ι) {y : SRec}
    (hy : ∀ o ∈ αs.getLast?, o < y.2) : ι.rec1 y = y := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · obtain ⟨o, ho, rfl⟩ := cutOf_eq.mp (hat c θ rfl)
    exact Inst.rec1_fixed θ (cut_le_of_lt (hy o ho))

/-- **`ExtKeepsTInst`**: the records relevant to the retained part are above the outermost lend,
so the instantiation fixes them, and `Ext` and `KeepsT` from the list carry to the instantiated
list (`mem_recs_iff_of_lt`). -/
theorem extKeepsTInst : ExtKeepsTInst := by
  intro αs ι ls ls' ρz hat hz hra he hkt
  have hkt' : KeepsT (ι.recs ls) ls' ρz := by
    intro x hx hr
    obtain ⟨y, hy, rfl⟩ := Inst.mem_recs.mp hx
    have hry : Core.Rel y.1 ρz := (rel_rec1 ι y ρz).mp hr
    rw [rec1_eq_of_above hat (hra y hy hry)]
    exact hkt y hy hry
  refine ⟨⟨fun r hr hrel => ?_, fun b hb x hx => ?_⟩, hkt'⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact List.mem_map_of_mem (hkt' x hx hrel)
  · have hlast : ∀ o ∈ αs.getLast?, o < x.2 := fun o ho => lt_trans (lt_of_cellIn hz hb ho) hx
    exact (mem_recs_iff_of_lt hat hlast).trans (he.2 b hb x hx)

/-! ### §3.3 The relevant records lie above the outermost lend -/

/-- A chain's last step is an `own` cell of the escrow. -/
theorem chain_get_own {R : WRes} {T : VTy} {v : Val} {p : Option BoCa.Loc} {l : BoCa.Loc}
    {S : VTy} {u : Val} (h : Chain R T v p l S u) : R.get l = some (CellU.ownOf u) := by
  induction h with
  | one _ hg => exact hg
  | step _ _ _ ih => exact ih

/-- **A proper lineage member's place is a lineage location**: a `mut` cell of its parent's escrow. -/
theorem linLoc_of_linPath {p d : FrameRec} {path : List BoCa.Loc} (h : LinPath p path d)
    (hne : path ≠ []) : LinLoc p d.le := by
  induction h with
  | nil r => exact absurd rfl hne
  | @cons r d e q hs t ih =>
      cases q with
      | nil =>
          obtain rfl := t.inv_nil
          obtain ⟨-, -, ζ, hζ, hk, -, -⟩ := hs
          exact ⟨r, DescR.refl r, ζ, hζ, by rw [hk]; decide⟩
      | cons m q =>
          obtain ⟨d', ⟨q', hq'⟩, ζ, hζ, hk⟩ := ih (by simp)
          exact ⟨d', ⟨_, LinPath.cons hs hq'⟩, ζ, hζ, hk⟩

/-- **`RelAboveOfTagged`**: a record relevant to the retained part through an `imm` cell is tagged
with the lifetime of a frame whose lineage holds it; that cell's lifetimes are among `ag(W)`'s at
its place, which the frame's lifetime bounds (`FrameLife`: equal at the frame's own place, no
longer at a lineage location); and the retained part is strictly above the outermost lend. -/
theorem relAboveOfTagged : RelAboveOfTagged := by
  intro W ρz ρr ps rs ls αs hT htg hc hz x hx hrel o ho
  obtain ⟨m, ψ, hψ, hk, hpos⟩ := hrel
  obtain ⟨p, -, ⟨path, hpath⟩, hfl⟩ := htg x hx
  have hlt : o < ψ.at := cell_above_of_stratS hz hψ (by rw [hk]; decide) o ho
  obtain ⟨ψW, hψW, hsub⟩ := top_of_compS_left hc hψ
  obtain ⟨σW, ex, ag, -, hag, -⟩ := hT.valid
  obtain ⟨s, hs, hψe⟩ := CellU.imm_eta hk
  have hkW : ψW.kind = Kind.imm := hsub.kind ▸ hk
  obtain ⟨sW, hsW, hψWe⟩ := CellU.imm_eta hkW
  obtain ⟨ζ, hζ, hkζ, -, -⟩ := AgW.get_imm hag hψW hkW
  obtain ⟨t, ht, hζe⟩ := CellU.imm_eta hkζ
  -- `ψ`'s shortest lifetime is a lifetime of `ag(W)`'s cell at `m`
  have hmemW : sW.mem ψ.at := by
    rcases hsub with h | ⟨S, S', v, χ, h₁, h₂, e₁, e₂, hSS⟩
    · subst h
      rw [hψWe, CellU.at_immOf]
      exact LSet.meet_mem _
    · rw [e₁, CellU.at_immOf]
      rw [hψWe] at e₂
      have := congrArg CellU.lsOf e₂
      simp only [CellU.lsOf_immOf, Option.some.injEq] at this
      rw [this]; exact hSS _ (LSet.meet_mem _)
  have hmemA : t.mem ψ.at := by
    rw [hψWe] at hψW
    rw [hζe] at hζ
    exact AgW.get_ls_imm hag hψW hζ hmemW
  have hlsζ : ζ.lsOf = some t := by rw [hζe, CellU.lsOf_immOf]
  by_cases hm : m = p.le
  · subst hm
    have := hfl.1 ag hag ζ t hζ hlsζ ψ.at hmemA
    rw [← this]; exact hlt
  · have hloc : LinLoc p m := by
      rcases hpos with hle | ⟨q, S, u, hch⟩
      · cases path with
        | nil =>
            obtain rfl := hpath.inv_nil
            exact absurd hle hm
        | cons m' path' =>
            subst hle
            exact linLoc_of_linPath hpath (by simp)
      · exact ⟨x.1, ⟨path, hpath⟩, _, chain_get_own hch, by simp⟩
    exact lt_of_lt_of_le hlt (hfl.2 ag hag m hloc ζ t hζ hlsζ ψ.at hmemA)


/-! ### §3.3 The tags, given one frame per lineage

`LineageUnique` (a record lies in one frame's lineage at a `TW` world) is not derived here: the
records-proper case reads `TI`'s location clauses, and the sub-record case needs two frames'
escrows to meet at no `mut` cell, a walk lemma on `ex(W)` not found among `TW.inv`'s consequences.
The statements below are proved from it. -/

/-- A record proper's cell is an `imm` view of `ag(W)` (`TI`'s `LeInv`), with a lifetime set. -/
theorem frame_cell_ag {W : WRes} {ps rs : List FrameRec} (hT : TW W ps rs) {p : FrameRec}
    (hp : p ∈ ps) : ∃ ag, AgW W ag ∧ ∃ (ζ : CellU BoCa.Loc Val) (t : LSet),
      ag.get p.le = some ζ ∧ ζ.lsOf = some t := by
  obtain ⟨σW, ex, ag, -, hag, -⟩ := hT.valid
  obtain ⟨ζ, hζ, hk, -, -⟩ := hT.inv.2.1 p hp ag hag
  obtain ⟨t, ht⟩ := lsOf_of_imm hk
  exact ⟨ag, hag, ζ, t, hζ, ht⟩

/-- Two `FrameLife`s of one record proper name one lifetime (`frameLife_eq`). -/
theorem frameLife_unique {W : WRes} {ps rs : List FrameRec} (hT : TW W ps rs) {p : FrameRec}
    (hp : p ∈ ps) {α β : Life} (hα : FrameLife W p α) (hβ : FrameLife W p β) : α = β := by
  obtain ⟨ag, hag, ζ, t, hζ, ht⟩ := frame_cell_ag hT hp
  exact (frameLife_eq hα hag hζ ht (LSet.meet_mem t)).symm.trans
    (frameLife_eq hβ hag hζ ht (LSet.meet_mem t))

/-- **`TagFixed`, from `LineageUnique`.** -/
theorem tagFixed_of (hL : LineageUnique) : TagFixed := by
  intro W ps rs ls ls' x x' hT htg htg' hx hx' heq
  obtain ⟨p, hp, hd, hfl⟩ := htg x hx
  obtain ⟨p', hp', hd', hfl'⟩ := htg' x' hx'
  rw [heq] at hd'
  obtain rfl := hL W ps rs p p' x.1 hT hp hp' hd hd'
  exact frameLife_unique hT hp hfl' hfl

/-- **`KeepsTOfTagged`, from `LineageUnique`.** -/
theorem keepsTOfTagged_of (hL : LineageUnique) : KeepsTOfTagged := by
  intro W ρ ps rs ls ls' hT htg htg' he x hx hr
  obtain ⟨t, ht⟩ := mem_rsOf.mp (he.1 x.1 (List.mem_map_of_mem hx) hr)
  have : t = x.2 := tagFixed_of hL W ps rs ls ls' x (x.1, t) hT htg htg' hx ht rfl
  have hxe : (x.1, t) = x := by rw [this]
  rw [← hxe]; exact ht

/-- **`ResumeKeepsT`, from `LineageUnique`**: a relevant record's frame is kept with its lifetime
(`FramesKept`), the resume's list holds the record at a frame of its lineage, which is that frame,
so at that lifetime. -/
theorem resumeKeepsT_of (hL : LineageUnique) : ResumeKeepsT := by
  intro W W' ρz ps ps' rs rs' ls ls' hT htg hT' htg' hkept he x hx hr
  obtain ⟨t, ht⟩ := mem_rsOf.mp (he.1 x.1 (List.mem_map_of_mem hx) hr)
  obtain ⟨p, hp, hd, hfl⟩ := htg x hx
  obtain ⟨hp', hfl'⟩ := hkept p hp ⟨x, hx, hd, hr⟩
  obtain ⟨p'', hp'', hd'', hfl''⟩ := htg' (x.1, t) ht
  obtain rfl := hL W' ps' rs' p p'' x.1 hT' hp' hp'' hd hd''
  have : t = x.2 := frameLife_unique hT' hp' hfl'' (hfl' x.2 hfl)
  have hxe : (x.1, t) = x := by rw [this]
  rw [← hxe]; exact ht

/-- **`ShareKeepsT`, from `LineageUnique`**: `resumeKeepsT_of`, then `relAboveOfTagged` at the
stop's world, then `extKeepsTInst`. -/
theorem shareKeepsT_of (hL : LineageUnique) : ShareKeepsT := by
  intro W W' ρz ρr ps ps' rs rs' ls ls' αs ι hat hz hT htg hc hT' htg' hkept he
  exact extKeepsTInst αs ι ls ls' ρz hat hz (relAboveOfTagged W ρz ρr ps rs ls αs hT htg hc hz)
    he (resumeKeepsT_of hL W W' ρz ps ps' rs rs' ls ls' hT htg hT' htg' hkept he)

/-- **`RelFramesNotEnded`, from `LineageUnique`**: the frame of a record relevant to the retained
part is at the record's tag, strictly above the outermost lend (`relAboveOfTagged`), and a frame
names one lifetime (`frameLife_unique`), while every lend of the stack is at or below the
outermost lend. -/
theorem relFramesNotEnded_of (hL : LineageUnique) : RelFramesNotEnded := by
  intro W ρz ρr ps rs ls σ αs p hT htg hc hok hz hp ⟨x, hx, hd, hr⟩ α hα hfl
  obtain ⟨p₀, hp₀, hd₀, hfl₀⟩ := htg x hx
  obtain rfl := hL W ps rs p₀ p x.1 hT hp₀ hp hd₀ hd
  obtain ⟨o, ho⟩ : ∃ o, αs.getLast? = some o := by
    cases h : αs.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; subst h; exact absurd hα List.not_mem_nil
    | some o => exact ⟨o, rfl⟩
  have hαo : α ≤ o := mem_le_last hok.2.1 α hα o ho
  have hox : o < x.2 := relAboveOfTagged W ρz ρr ps rs ls αs hT htg hc hz x hx hr o ho
  have : α = x.2 := frameLife_unique hT hp₀ hfl hfl₀
  rw [this] at hαo
  exact absurd hox (not_lt.mpr hαo)


/-! ### §3.2 `∀E`: the free variables of an instance -/

/-- A variable a substituted term mentions is mentioned by the image of one of the term's. -/
theorem mentions_applySub {σ : Lifetime.LSubst} {z : LifeVar} : ∀ {a : Lifetime.Life},
    (a.applySub σ).mentions z = true →
      ∃ w, a.mentions w = true ∧ ((Lifetime.Life.var w).applySub σ).mentions z = true
  | .var w, h => ⟨w, by simp [Lifetime.Life.mentions], h⟩
  | .top, h => by simp [Lifetime.Life.applySub, Lifetime.Life.mentions] at h
  | .join a b, h => by
      simp only [Lifetime.Life.applySub, Lifetime.Life.mentions, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := mentions_applySub (a := a) h
        exact ⟨w, by simp [Lifetime.Life.mentions, hw], hz⟩
      · obtain ⟨w, hw, hz⟩ := mentions_applySub (a := b) h
        exact ⟨w, by simp [Lifetime.Life.mentions, hw], hz⟩
  | .meet a b, h => by
      simp only [Lifetime.Life.applySub, Lifetime.Life.mentions, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := mentions_applySub (a := a) h
        exact ⟨w, by simp [Lifetime.Life.mentions, hw], hz⟩
      · obtain ⟨w, hw, hz⟩ := mentions_applySub (a := b) h
        exact ⟨w, by simp [Lifetime.Life.mentions, hw], hz⟩

/-- Off the dropped variable, the dropped substitution is the substitution. -/
theorem applySub_var_lsubDrop_ne {σ : Lifetime.LSubst} {w y : LifeVar} (h : w ≠ y) :
    (Lifetime.Life.var w).applySub (lsubDrop σ y) = (Lifetime.Life.var w).applySub σ := by
  simp only [Lifetime.Life.applySub, assocFind_lsubDrop_ne h]

mutual
/-- **A variable free in an instance is the image of a free variable**: through every former, a
`∀`'s binder renamed or dropped on the way under it. -/
theorem vFree_applyLSub : ∀ (A : VTy) (σ : Lifetime.LSubst) {z : LifeVar},
    VFree z (A.applyLSub σ) →
      ∃ w, VFree w A ∧ ((Lifetime.Life.var w).applySub σ).mentions z = true
  | .unit, _, _, h => h.elim
  | .zero, _, _, h => h.elim
  | .unk, _, _, h => h.elim
  | .int _, _, _, h => h.elim
  | .opq _, _, _, h => h.elim
  | .tvar _, _, _, h => h.elim
  | .tensor A B, σ, _, h => by
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub A σ h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub B σ h; exact ⟨w, Or.inr hw, hz⟩
  | .sum A B, σ, _, h => by
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub A σ h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub B σ h; exact ⟨w, Or.inr hw, hz⟩
  | .ref A, σ, _, h => vFree_applyLSub A σ h
  | .bang A, σ, _, h => vFree_applyLSub A σ h
  | .fam A, σ, _, h => vFree_applyLSub A σ h
  | .mu A, σ, _, h => vFree_applyLSub A σ h
  | .thunk C, σ, _, h => cFree_applyLSub C σ h
  | .imm a A, σ, _, h => by
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := mentions_applySub h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub A σ h; exact ⟨w, Or.inr hw, hz⟩
  | .mut a A, σ, _, h => by
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := mentions_applySub h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub A σ h; exact ⟨w, Or.inr hw, hz⟩
  | .box a A, σ, _, h => by
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := mentions_applySub h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub A σ h; exact ⟨w, Or.inr hw, hz⟩
theorem cFree_applyLSub : ∀ (C : CTy) (σ : Lifetime.LSubst) {z : LifeVar},
    CFree z (C.applyLSub σ) →
      ∃ w, CFree w C ∧ ((Lifetime.Life.var w).applySub σ).mentions z = true
  | .ret A, σ, _, h => vFree_applyLSub A σ h
  | .arr A D, σ, _, h => by
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub A σ h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := cFree_applyLSub D σ h; exact ⟨w, Or.inr hw, hz⟩
  | .amp D E, σ, _, h => by
      rcases h with h | h
      · obtain ⟨w, hw, hz⟩ := cFree_applyLSub D σ h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := cFree_applyLSub E σ h; exact ⟨w, Or.inr hw, hz⟩
  | .top, _, _, h => h.elim
  | .nu D, σ, _, h => cFree_applyLSub D σ h
  | .eff _ _ _ A B D, σ, _, h => by
      rcases h with h | h | h
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub A σ h; exact ⟨w, Or.inl hw, hz⟩
      · obtain ⟨w, hw, hz⟩ := vFree_applyLSub B σ h; exact ⟨w, Or.inr (Or.inl hw), hz⟩
      · obtain ⟨w, hw, hz⟩ := cFree_applyLSub D σ h; exact ⟨w, Or.inr (Or.inr hw), hz⟩
  | .all y b D, σ, z, h => by
      cases hcap : lsubCaptures (lsubDrop σ y) y with
      | true =>
          rw [CTy.applyLSub_all_captures hcap] at h
          rcases h with h | ⟨hne, h⟩
          · obtain ⟨w, hw, hz⟩ := mentions_applySub h; exact ⟨w, Or.inl hw, hz⟩
          · obtain ⟨w, hw, hz⟩ := cFree_applyLSub D _ h
            by_cases hwy : w = y
            · subst hwy
              simp [Lifetime.Life.applySub, Lifetime.assocFind, Lifetime.Life.mentions] at hz
              exact (hne hz).elim
            · refine ⟨w, Or.inr ⟨hwy, hw⟩, ?_⟩
              have : (Lifetime.Life.var w).applySub ((y, Lifetime.Life.var
                  (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) D.lifeBound))) ::
                    lsubDrop σ y) = (Lifetime.Life.var w).applySub (lsubDrop σ y) := by
                simp only [Lifetime.Life.applySub, Lifetime.assocFind,
                  if_neg (Ne.symm hwy)]
              rw [this, applySub_var_lsubDrop_ne hwy] at hz
              exact hz
      | false =>
          rw [CTy.applyLSub_all_not_captures hcap] at h
          rcases h with h | ⟨hne, h⟩
          · obtain ⟨w, hw, hz⟩ := mentions_applySub h; exact ⟨w, Or.inl hw, hz⟩
          · obtain ⟨w, hw, hz⟩ := cFree_applyLSub D _ h
            by_cases hwy : w = y
            · subst hwy
              simp [Lifetime.Life.applySub, assocFind_lsubDrop_self,
                Lifetime.Life.mentions] at hz
              exact (hne hz).elim
            · rw [applySub_var_lsubDrop_ne hwy] at hz
              exact ⟨w, Or.inr ⟨hwy, hw⟩, hz⟩
end

/-- **`RetainedPayInstRow`**: a variable free in `S[b/'x]` is free in `S` and not `'x`, read where
the callee read it, or is a variable of `b` with `'x` free in `S`; `b` has no join, so it reads
that variable at a lifetime at least as long as `⟦b⟧`, which the callee read at an external
lifetime. -/
theorem retainedPayInstRow : RetainedPayInstRow := by
  intro σ αs δ x b S v m hx hnj hb h l hv hi y hy my hmy
  have hp := h l hv hi
  obtain ⟨w, hw, hz⟩ := vFree_applyLSub S [(x, b)] hy
  by_cases hwx : w = x
  · rw [hwx] at hw hz
    have hzb : b.mentions y = true := by
      simpa [Lifetime.Life.applySub, Lifetime.assocFind] using hz
    have hm : (extS (δ.extend x m) σ αs).find? x = some m := by
      rw [extS_find_not_mem _ σ αs x hx, LSub.find?_extend, if_pos rfl]
    have hext := hp x hw m hm
    have hle := noJoinL_le hnj hb hzb hmy
    rintro ⟨c, hc, hlt⟩
    exact hext ⟨c, hc, lt_of_le_of_lt (show OrderDual.toDual m ≤ OrderDual.toDual my from hle) hlt⟩
  · have hwy : y = w := by
      simpa [Lifetime.Life.applySub, Lifetime.assocFind, Ne.symm hwx,
        Lifetime.Life.mentions] using hz
    rw [hwy] at hmy
    refine hp w hw my ?_
    rw [extS_find_base (X := δ.extend x m) (X' := δ) (find?_extend_ne δ m (Ne.symm hwx)) σ αs]
    exact hmy

end ProbeD1

end
