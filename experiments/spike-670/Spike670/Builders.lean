import Spike670.Split

/-!
# #670 — the conversion's small builders

`leaf` (every other live slot dropped), `bindTm` (a term's value named), and the actions that
read types (`vty`, `cty`, `repJ`), which move neither the counter nor the machine set.
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

/-! ### Actions that keep the counter -/

/-- The action moved neither the counter nor the machine set. -/
def Keeps (s s' : CState) : Prop := s'.next = s.next ∧ s'.mach = s.mach

theorem Keeps.grows {s s' : CState} (h : Keeps s s') : Grows s s' := ⟨h.1.ge, h.2⟩
theorem Keeps.refl (s : CState) : Keeps s s := ⟨rfl, rfl⟩
theorem Keeps.trans {a b c : CState} (h₁ : Keeps a b) (h₂ : Keeps b c) : Keeps a c :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem ok_lift {r : Except String α} {s s' : CState} {a : α} (h : Ok (lift r) s a s') :
    s' = s := by
  unfold lift at h; split at h
  · exact (ok_pure h).2
  · exact (ok_throw h).elim

theorem ok_readFormers {fs : List String} {s s' : CState} {u : Unit}
    (h : Ok (readFormers fs) s u s') : Keeps s s' := by
  simp only [readFormers] at h
  obtain ⟨d, s₁, h₁, h₂⟩ := ok_bind h
  obtain ⟨rfl, rfl⟩ := ok_get h₁
  split at h₂
  · obtain ⟨_, s₂, h₃, h₄⟩ := ok_bind h₂
    obtain ⟨-, rfl⟩ := ok_pure h₄
    exact forIn_rule fs.eraseDups _ (fun _ _ st => Keeps s₁ st)
      (fun _ _ _ _ st r st' _ hI hf => by
        obtain ⟨_, s₅, h₅, h₆⟩ := ok_bind hf
        obtain ⟨rfl, rfl⟩ := ok_pure h₆
        exact ⟨_, rfl, hI.trans (ok_readFact h₅)⟩) fs.eraseDups [] _ s₁ _ _ (by simp)
      (Keeps.refl _) h₃
  · exact (ok_pure h₂).2 ▸ Keeps.refl _

theorem ok_vty {A : VTy} {s s' : CState} {t : LTy} (h : Ok (vty A) s t s') : Keeps s s' := by
  simp only [vty] at h
  obtain ⟨_, s₁, h₁, h₂⟩ := ok_bind h
  obtain ⟨d, s₂, h₃, h₄⟩ := ok_bind h₂
  obtain ⟨rfl, rfl⟩ := ok_get h₃
  exact (ok_lift h₄) ▸ ok_readFormers h₁

theorem ok_cty {C : CTy} {s s' : CState} {t : LCTy} (h : Ok (cty C) s t s') : Keeps s s' := by
  simp only [cty] at h
  obtain ⟨_, s₁, h₁, h₂⟩ := ok_bind h
  obtain ⟨d, s₂, h₃, h₄⟩ := ok_bind h₂
  obtain ⟨rfl, rfl⟩ := ok_get h₃
  exact (ok_lift h₄) ▸ ok_readFormers h₁

theorem ok_repJ {j : Jdg} {s s' : CState} {t : LTy} (h : Ok (repJ j) s t s') : Keeps s s' := by
  unfold repJ at h
  split at h
  · exact ok_vty h
  · exact ok_vty h
  · obtain ⟨_, s₁, h₁, h₂⟩ := ok_bind h
    split at h₂
    · exact (ok_pure h₂).2 ▸ ok_cty h₁
    · exact (ok_throw h₂).elim
  · exact (ok_pure h).2 ▸ Keeps.refl _
  · obtain ⟨_, s₁, h₁, h₂⟩ := ok_bind h
    exact (ok_pure h₂).2 ▸ ok_cty h₁

/-! ### `leaf` -/

theorem live_zipIdx (ctx : Ctx) : live ctx = ctx.zipIdx.filterMap (·.1) := by
  conv_lhs => rw [← List.zipIdx_map_fst 0 ctx]
  simp [live, List.filterMap_map]

theorem leaf_none (ctx : Ctx) (b : Tm) : leaf ctx none b = drops (live ctx) b := by
  have : ctx.zipIdx.filter (fun (q : Option Var × Nat) => some q.2 != none) = ctx.zipIdx :=
    List.filter_eq_self.2 (fun a _ => by simp)
  simp only [leaf, live_zipIdx]
  rw [this]

/-- The slots other than `i`: every live variable but `i`'s. -/
theorem leaf_others {ctx : Ctx} {i : Nat} {x : Var} (hx : ctx[i]? = some (some x))
    (hn : (live ctx).Nodup) :
    let others := (ctx.zipIdx.filter fun (_, j) => some j != some i).filterMap (·.1)
    others.Nodup ∧ x ∉ others ∧ ∀ y, y ∈ live ctx ↔ y ∈ others ∨ y = x := by
  intro others
  have P := (List.filter_append_perm (fun (q : Option Var × Nat) => some q.2 != some i)
    ctx.zipIdx).filterMap (·.1)
  rw [List.filterMap_append, ← live_zipIdx] at P
  have hM : ∀ y, y ∈ ((ctx.zipIdx.filter fun q => !(some q.2 != some i)).filterMap (·.1)) ↔
      y = x := by
    intro y
    simp only [List.mem_filterMap, List.mem_filter, List.mem_zipIdx_iff_getElem?]
    constructor
    · rintro ⟨⟨o, j⟩, ⟨hj, hji⟩, rfl⟩
      simp at hji; subst hji
      simp at hj; rw [hx] at hj; cases hj; rfl
    · intro hy; rw [hy]; exact ⟨(some x, i), ⟨by simpa using hx, by simp⟩, rfl⟩
  have hnd := P.nodup_iff.2 hn
  refine ⟨(List.nodup_append.1 hnd).1, fun h => ?_, fun y => ?_⟩
  · exact (List.nodup_append.1 hnd).2.2 x h x ((hM x).2 rfl) rfl
  · rw [← P.mem_iff, List.mem_append, hM]

/-! ### Results -/

/-- What a conversion promises: its term consumes `Γ` (or is unreachable), binds each variable
once, each from the counter's range `[lo, s'.next)`. -/
structure PostG (D : Var → Prop) (Γ : Finset Var) (lo : Nat) (s' : CState) (tm : Tm) : Prop where
  closed : ClosedL D Γ tm
  nodup : (bnd tm).Nodup
  range : ∀ y ∈ bnd tm, lo ≤ y ∧ y < s'.next

/-- The context's variables are distinct and below the counter. -/
def WF (ctx : Ctx) (s : CState) : Prop := (live ctx).Nodup ∧ ∀ y ∈ live ctx, y < s.next

/-- **The conversion's contract at a context.** -/
def Post (D : Var → Prop) (ctx : Ctx) (s : CState) (tm : Tm) (s' : CState) : Prop :=
  Grows s s' ∧ PostG D (liveF ctx) s.next s' tm

/-- The contract of a conversion of one node, at every context and state. -/
def Spec (D : Var → Prop) (f : Ctx → CM Tm) : Prop :=
  ∀ ctx s tm s', WF ctx s → s.mach.isEmpty = true → Ok (f ctx) s tm s' → Post D ctx s tm s'

/-- A leaf: the term `b` consumes `Γb`, every other live variable dropped. -/
theorem post_drops {D : Var → Prop} {Γb : Finset Var} {xs : List Var} {b : Tm} {lo : Nat}
    {s' : CState} (hn : xs.Nodup) (hd : ∀ x ∈ xs, x ∉ Γb) (hb : PostG D Γb lo s' b) :
    PostG D (Γb ∪ xs.toFinset) lo s' (drops xs b) := by
  obtain ⟨⟨Δ, hl, hc⟩, n, r⟩ := hb
  refine ⟨⟨Δ, LinL.drops hn (fun x hx => by simp [hx]) ?_, hc⟩, by rwa [bnd_drops],
    by rwa [bnd_drops]⟩
  convert hl using 1
  ext y; by_cases hy : y ∈ xs
  · simp [hy, hd y hy]
  · simp [hy]

/-- `leaf ctx none b`, `b` consuming nothing. -/
theorem post_leaf_none {D : Var → Prop} {ctx : Ctx} {b : Tm} {s : CState}
    (hw : WF ctx s) (hb : PostG D ∅ s.next s b) : Post D ctx s (leaf ctx none b) s := by
  refine ⟨Grows.refl s, ?_⟩
  rw [leaf_none]
  have := post_drops hw.1 (by simp) hb
  simpa [liveF] using this

/-- `leaf ctx (some i) b`, `b` consuming the slot `i`'s variable. -/
theorem post_leaf_some {D : Var → Prop} {ctx : Ctx} {i : Nat} {x : Var} {b : Tm} {s : CState}
    (hw : WF ctx s) (hx : ctx[i]? = some (some x)) (hb : PostG D {x} s.next s b) :
    Post D ctx s (leaf ctx (some i) b) s := by
  refine ⟨Grows.refl s, ?_⟩
  obtain ⟨n, hxo, hiff⟩ := leaf_others hx hw.1
  have := post_drops n (fun y hy h => hxo (by simp at h; exact h ▸ hy)) hb
  convert this using 2
  · ext y; rw [mem_liveF, hiff y]; simp only [Finset.mem_union, Finset.mem_singleton,
      List.mem_toFinset]; exact or_comm
  · rfl

/-- An operand-only term that consumes exactly `xs`. -/
theorem postG_ops {D : Var → Prop} {t : Tm} {xs : List Var} {lo : Nat} {s' : CState}
    (ho : operands t = some xs) (hn : xs.Nodup) : PostG D xs.toFinset lo s' t := by
  refine ⟨⟨some ∅, .ops ho ?_, .inr rfl⟩, by simp [operands_bnd ho], by simp [operands_bnd ho]⟩
  clear ho
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    refine .cons (by simp) ?_
    have : (insert x xs.toFinset).erase x = xs.toFinset := by
      rw [Finset.erase_insert]; simpa using (List.nodup_cons.1 hn).1
    simp only [List.toFinset_cons, this]
    exact ih (List.nodup_cons.1 hn).2

/-! ### `bindTm` -/

theorem ok_bindTm {e : Tm} {t : LTy} {k : Var → CM Tm} {s s' : CState} {r : Tm}
    (h : Ok (bindTm e t k) s r s') :
    (∃ x, e = .var x ∧ Ok (k x) s r s') ∨
    (∃ s₁ b, s₁.next = s.next + 1 ∧ s₁.mach = s.mach ∧ r = .letv s.next e b ∧
      Ok (k s.next) s₁ b s') := by
  unfold bindTm at h
  split at h
  · exact .inl ⟨_, rfl, h⟩
  · obtain ⟨x, s₁, h₁, h₂⟩ := ok_bind h
    obtain ⟨rfl, hn, hm⟩ := ok_fresh h₁
    obtain ⟨b, s₂, h₃, h₄⟩ := ok_bind h₂
    obtain ⟨rfl, rfl⟩ := ok_pure h₄
    exact .inr ⟨s₁, b, hn, hm, rfl, h₃⟩

/-- **`bindTm e t k`**, `e` consuming `Γ₁` with its binders in `[lo, s.next)`, the continuation
consuming `Γ₂` and the value's variable. -/
theorem post_bindTm {D : Var → Prop} {e : Tm} {t : LTy} {k : Var → CM Tm} {s s' : CState} {r : Tm}
    {Γ₁ Γ₂ : Finset Var} {lo : Nat}
    (h : Ok (bindTm e t k) s r s') (he : PostG D Γ₁ lo s e) (hlo : lo ≤ s.next)
    (h₁ : ∀ y ∈ Γ₁, y < s.next) (h₂ : ∀ y ∈ Γ₂, y < lo) (hdj : ∀ y ∈ Γ₂, y ∉ Γ₁)
    (hk : ∀ x s₁ b s₂, x ∉ Γ₂ → x < s₁.next → s.next ≤ s₁.next → s₁.mach = s.mach →
      Ok (k x) s₁ b s₂ → Grows s₁ s₂ ∧ PostG D (insert x Γ₂) s₁.next s₂ b) :
    Grows s s' ∧ PostG D (Γ₁ ∪ Γ₂) lo s' r := by
  rcases ok_bindTm h with ⟨x, rfl, hkx⟩ | ⟨s₁, b, hn, hm, rfl, hkb⟩
  · have hΓ := LinL.var_closed he.closed
    subst hΓ
    have hx : x < s.next := h₁ x (by simp)
    obtain ⟨g, ⟨cl, nd, rg⟩⟩ := hk x s r s' (fun h => hdj x h (by simp)) hx (le_refl _) rfl hkx
    refine ⟨g, ⟨?_, nd, fun y hy => ⟨le_trans hlo (rg y hy).1, (rg y hy).2⟩⟩⟩
    rw [Finset.insert_eq] at cl; exact cl
  · obtain ⟨g, ⟨cl, nd, rg⟩⟩ := hk s.next s₁ b s' (fun h => by have := h₂ _ h; vomega)
      (by vomega) (by vomega) hm hkb
    refine ⟨⟨by have := g.next; vomega, g.mach.trans hm⟩, ⟨?_, ?_, ?_⟩⟩
    · exact LinL.letv_closed he.closed cl fun y hy =>
        ⟨hdj y hy, fun hb => by have := (he.range y hb).1; have := h₂ y hy; vomega⟩
    · simp only [bnd, List.nodup_cons, List.mem_append, not_or, List.nodup_append]
      refine ⟨⟨fun hb => by have := (he.range _ hb).2; vomega,
        fun hb => by have := (rg _ hb).1; vomega⟩, he.nodup, nd, fun a ha b hb => ?_⟩
      rintro rfl; have := (he.range a ha).2; have := (rg a hb).1; vomega
    · intro y hy
      simp only [bnd, List.mem_cons, List.mem_append] at hy
      have := g.next
      rcases hy with rfl | hy | hy
      · exact ⟨hlo, by vomega⟩
      · have := he.range y hy; exact ⟨this.1, by vomega⟩
      · have := rg y hy; exact ⟨by vomega, this.2⟩

end Backend2.Spike670
