import Spike670.Monad
import Spike670.LinLemmas

/-!
# #670 — `splitCtx`, read slot by slot

`splitCtx ctx m` walks the context with the masks (`Backend2/Convert.lean`). At each slot:

| slot | masks | left | right | made |
|---|---|---|---|---|
| dead | `(false, false)` | dead | dead | — |
| dead | other | — | — | throws |
| `x` | `(true, true)` | `x` | `x'` fresh | `copy x x'` |
| `x` | `(true, false)` | `x` | dead | — |
| `x` | `(false, true)` | dead | `x` | — |
| `x` | `(false, false)` | dead | dead | `drop x` |

`splitCtx_spec` is the table as a theorem, with what the parts' terms need: the parts' live
variables are disjoint, the wrapper `pre` turns a term over both parts into one over `ctx`
(copying exactly the `(true, true)` slots, which must satisfy `D`), and its binders are the fresh
copies.
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core.Check

/-- A loop over `L`, read with an invariant over the elements done. -/
theorem forIn_rule {γ β : Type} (L : List γ) (f : γ → β → CM (ForInStep β))
    (I : List γ → β → CState → Prop)
    (step : ∀ pfx a rest b s r s', pfx ++ a :: rest = L → I pfx b s → Ok (f a b) s r s' →
      ∃ b', r = .yield b' ∧ I (pfx ++ [a]) b' s') :
    ∀ (rest pfx : List γ) (b : β) (s : CState) (r : β) (s' : CState), pfx ++ rest = L →
      I pfx b s → Ok (forIn rest b f) s r s' → I L r s' := by
  intro rest
  induction rest with
  | nil =>
    intro pfx b s r s' hL hI h
    simp only [List.forIn_nil] at h
    obtain ⟨rfl, rfl⟩ := ok_pure h
    simpa [← hL] using hI
  | cons a rest ih =>
    intro pfx b s r s' hL hI h
    simp only [List.forIn_cons] at h
    obtain ⟨st, s₁, h₁, h₂⟩ := ok_bind h
    obtain ⟨b', rfl, hI'⟩ := step pfx a rest b s st s₁ hL hI h₁
    exact ih (pfx ++ [a]) b' s₁ r s' (by simp [← hL]) hI' h₂

/-- The live variables of a context, as a set. -/
def liveF (ctx : Ctx) : Finset Var := (live ctx).toFinset

/-- Apply a list of wrappers, the head innermost. -/
def appPre (pre : List (Tm → Tm)) (t : Tm) : Tm := pre.foldl (fun t f => f t) t

/-- What a slot of the split is, given its context slot and masks, the parts' slots, and the range
of fresh variables. -/
def SlotOK (lo hi : Nat) : Option Var × Bool × Bool → Option Var → Option Var → Prop
  | (none, a, b), o₁, o₂ => a = false ∧ b = false ∧ o₁ = none ∧ o₂ = none
  | (some x, true, true), o₁, o₂ => o₁ = some x ∧ ∃ x', o₂ = some x' ∧ lo ≤ x' ∧ x' < hi
  | (some x, true, false), o₁, o₂ => o₁ = some x ∧ o₂ = none
  | (some x, false, true), o₁, o₂ => o₁ = none ∧ o₂ = some x
  | (some _, false, false), o₁, o₂ => o₁ = none ∧ o₂ = none

theorem SlotOK.mono {lo hi hi' : Nat} (h : hi ≤ hi') {e o₁ o₂}
    (k : SlotOK lo hi e o₁ o₂) : SlotOK lo hi' e o₁ o₂ := by
  obtain ⟨o, a, b⟩ := e
  rcases o with _ | x <;> rcases a <;> rcases b <;> simp only [SlotOK] at k ⊢ <;> try exact k
  rcases k with ⟨a, x', b, c, d⟩; exact ⟨a, x', b, c, lt_of_lt_of_le d h⟩

/-- The ctx variables at the slots both masks hold: the copy set. -/
def bothVars (L : List (Option Var × Bool × Bool)) : List Var :=
  L.filterMap fun | (some x, true, true) => some x | _ => none

theorem live_append (a b : Ctx) : live (a ++ b) = live a ++ live b := by
  simp [live, List.filterMap_append]

theorem live_push (c : Array (Option Var)) (o : Option Var) :
    live (c.push o).toList = live c.toList ++ o.toList := by
  cases o <;> simp [live, List.filterMap_append]

/-- The slots of the parts, each by `SlotOK`. -/
def SlotsOK (lo hi : Nat) : List (Option Var × Bool × Bool) → List (Option Var) → List (Option Var) → Prop
  | [], [], [] => True
  | e :: es, o₁ :: os₁, o₂ :: os₂ => SlotOK lo hi e o₁ o₂ ∧ SlotsOK lo hi es os₁ os₂
  | _, _, _ => False

theorem SlotsOK.snoc {lo hi : Nat} : ∀ {es os₁ os₂} {e o₁ o₂}, SlotsOK lo hi es os₁ os₂ →
    SlotOK lo hi e o₁ o₂ → SlotsOK lo hi (es ++ [e]) (os₁ ++ [o₁]) (os₂ ++ [o₂])
  | [], [], [], _, _, _, _, k => ⟨k, trivial⟩
  | _ :: _, _ :: _, _ :: _, _, _, _, ⟨a, h⟩, k => ⟨a, SlotsOK.snoc h k⟩
  | [], _ :: _, _, _, _, _, h, _ | [], [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, _, h, _ | _ :: _, _ :: _, [], _, _, _, h, _ => h.elim

theorem SlotsOK.mono {lo hi hi' : Nat} (hh : hi ≤ hi') : ∀ {es os₁ os₂},
    SlotsOK lo hi es os₁ os₂ → SlotsOK lo hi' es os₁ os₂
  | [], [], [], _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨a, h⟩ => ⟨a.mono hh, SlotsOK.mono hh h⟩
  | [], _ :: _, _, h | [], [], _ :: _, h => h.elim
  | _ :: _, [], _, h | _ :: _, _ :: _, [], h => h.elim

theorem SlotsOK.length {lo hi : Nat} : ∀ {es os₁ os₂}, SlotsOK lo hi es os₁ os₂ →
    os₁.length = es.length ∧ os₂.length = es.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, ⟨_, h⟩ => by simp [(SlotsOK.length h).1, (SlotsOK.length h).2]
  | [], _ :: _, _, h | [], [], _ :: _, h => h.elim
  | _ :: _, [], _, h | _ :: _, _ :: _, [], h => h.elim

/-- The loop's invariant. -/
structure SplitInv (D : Var → Prop) (s₀ : CState) (pfx : List (Option Var × Bool × Bool))
    (preL : List (Tm → Tm)) (c₁ c₂ : Array (Option Var)) (s : CState) : Prop where
  grows : Grows s₀ s
  slots : SlotsOK s₀.next s.next pfx c₁.toList c₂.toList
  nd₁ : (live c₁.toList).Nodup
  nd₂ : (live c₂.toList).Nodup
  disj : ∀ y ∈ live c₁.toList, y ∉ live c₂.toList
  lt : ∀ y ∈ live c₁.toList ++ live c₂.toList, y < s.next
  orig : ∀ y ∈ live c₁.toList ++ live c₂.toList, y ∈ live (pfx.map (·.1)) ∨ s₀.next ≤ y
  pre : ∀ Γ t Δ, (∀ y ∈ Γ, y ∉ live (pfx.map (·.1)) ∧ y < s₀.next) →
    LinL D (Γ ∪ liveF c₁.toList ∪ liveF c₂.toList) t Δ →
    LinL D (Γ ∪ liveF (pfx.map (·.1))) (appPre preL t) Δ
  bnd : ∀ t, ∃ K, bnd (appPre preL t) = K ++ bnd t ∧ K.Nodup ∧ ∀ y ∈ K, s₀.next ≤ y ∧ y < s.next

theorem appPre_cons (w : Tm → Tm) (pre : List (Tm → Tm)) (t : Tm) :
    appPre (w :: pre) t = appPre pre (w t) := rfl

@[simp] theorem live_nil' : live [] = [] := rfl

@[simp] theorem live_snoc (l : Ctx) (o : Option Var) : live (l ++ [o]) = live l ++ o.toList := by
  cases o <;> simp [live, List.filterMap_append]

@[simp] theorem live_map_snoc (pfx : List (Option Var × Bool × Bool)) (o : Option Var)
    (ab : Bool × Bool) :
    live ((pfx ++ [(o, ab)]).map (fun e => e.1)) = live (pfx.map (fun e => e.1)) ++ o.toList := by
  simp [List.map_append]

theorem mem_liveF {c : Ctx} {y : Var} : y ∈ liveF c ↔ y ∈ live c := by simp [liveF]

section steps
variable {D : Var → Prop} {s₀ s st' : CState} {pfx : List (Option Var × Bool × Bool)}
  {preL : List (Tm → Tm)} {c₁ c₂ : Array (Option Var)}

/-- A step of the loop: the slot's entry `e`, the parts' slots `o₁ o₂`, the wrapper list `pre'`. -/
theorem SplitInv.step (I : SplitInv D s₀ pfx preL c₁ c₂ s) {o : Option Var} {ab : Bool × Bool}
    {o₁ o₂ : Option Var} {pre' : List (Tm → Tm)} {st' : CState}
    (g' : Grows s st')
    (hs : SlotOK s₀.next st'.next (o, ab) o₁ o₂)
    (hx : ∀ x, o = some x → x ∉ live (pfx.map (·.1)) ∧ x < s₀.next)
    (hnew : ∀ y, (y ∈ o₁.toList ∨ y ∈ o₂.toList) → o = some y ∨ y = s.next)
    (hfresh : ∀ y, y ∈ o₁.toList → y ∈ o₂.toList → False)
    (hlt : ∀ y, (y ∈ o₁.toList ∨ y ∈ o₂.toList) → y < st'.next)
    (hpre : ∀ Γ t Δ, (∀ y ∈ Γ, y ∉ live ((pfx ++ [(o, ab)]).map (·.1)) ∧ y < s₀.next) →
      LinL D (Γ ∪ liveF (c₁.toList ++ [o₁]) ∪ liveF (c₂.toList ++ [o₂])) t Δ →
      LinL D (Γ ∪ liveF ((pfx ++ [(o, ab)]).map (·.1))) (appPre pre' t) Δ)
    (hbnd : ∀ t, ∃ K : List Var, Spike670.bnd (appPre pre' t) = K ++ Spike670.bnd t ∧ K.Nodup ∧
      ∀ y ∈ K, s₀.next ≤ y ∧ y < st'.next) :
    SplitInv D s₀ (pfx ++ [(o, ab)]) pre' (c₁.push o₁) (c₂.push o₂) st' := by
  obtain ⟨g, sl, n₁, n₂, dj, lt, og, pr, bn⟩ := I
  have gn := g.next
  have g'n := g'.next
  -- A new variable is the slot's own, or the fresh copy.
  have hnewA : ∀ y, (y ∈ o₁.toList ∨ y ∈ o₂.toList) → y ∉ live c₁.toList ++ live c₂.toList := by
    intro y hy hA
    rcases hnew y hy with h | h
    · obtain ⟨h₁, h₂⟩ := hx y h
      rcases og y hA with h' | h'
      · exact h₁ h'
      · vomega
    · have := lt y hA; vomega
  refine ⟨g.trans g', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (sl.mono g'n).snoc hs
  · simp only [Array.toList_push, live_snoc, List.nodup_append, n₁, true_and]
    refine ⟨?_, fun a ha b hb => ?_⟩
    · cases o₁ <;> simp
    · rintro rfl; exact hnewA a (.inl hb) (by simp [ha])
  · simp only [Array.toList_push, live_snoc, List.nodup_append, n₂, true_and]
    refine ⟨?_, fun a ha b hb => ?_⟩
    · cases o₂ <;> simp
    · rintro rfl; exact hnewA a (.inr hb) (by simp [ha])
  · intro y hy hy'
    simp only [Array.toList_push, live_snoc, List.mem_append] at hy hy'
    rcases hy with hy | hy <;> rcases hy' with hy' | hy'
    · exact dj y hy hy'
    · exact hnewA y (.inr hy') (by simp [hy])
    · exact hnewA y (.inl hy) (by simp [hy'])
    · exact hfresh y hy hy'
  · intro y hy
    simp only [Array.toList_push, live_snoc, List.mem_append] at hy
    rcases hy with (hy | hy) | (hy | hy)
    · have := lt y (by simp [hy]); vomega
    · exact hlt y (.inl hy)
    · have := lt y (by simp [hy]); vomega
    · exact hlt y (.inr hy)
  · intro y hy
    simp only [Array.toList_push, live_snoc, List.mem_append] at hy
    have key : ∀ y, (y ∈ o₁.toList ∨ y ∈ o₂.toList) →
        y ∈ live ((pfx ++ [(o, ab)]).map (·.1)) ∨ s₀.next ≤ y := by
      intro y hy
      rcases hnew y hy with rfl | rfl
      · exact .inl (by simp)
      · exact .inr gn
    have old : y ∈ live c₁.toList ++ live c₂.toList →
        y ∈ live ((pfx ++ [(o, ab)]).map (·.1)) ∨ s₀.next ≤ y := by
      intro h; rcases og y h with h | h
      · exact .inl (by simp [h])
      · exact .inr h
    rcases hy with (hy | hy) | (hy | hy)
    · exact old (by simp [hy])
    · exact key y (.inl hy)
    · exact old (by simp [hy])
    · exact key y (.inr hy)
  · simpa using hpre
  · exact hbnd

end steps


/-- **`splitCtx`, slot by slot.** -/
theorem splitCtx_spec {D : Var → Prop} {ctx : Ctx} {m : Masks} {rule : String} {s s' : CState}
    {pre : Tm → Tm} {c₁ c₂ : Ctx} (h : Ok (splitCtx ctx m rule) s (pre, c₁, c₂) s')
    (hnd : (live ctx).Nodup) (hlt : ∀ y ∈ live ctx, y < s.next)
    (hD : ∀ x ∈ bothVars (ctx.zip m.ms), D x) :
    Grows s s' ∧ m.ms.length = ctx.length ∧ SlotsOK s.next s'.next (ctx.zip m.ms) c₁ c₂ ∧
    (live c₁).Nodup ∧ (live c₂).Nodup ∧ (∀ y ∈ live c₁, y ∉ live c₂) ∧
    (∀ y ∈ live c₁ ++ live c₂, y < s'.next) ∧
    (∀ y ∈ live c₁ ++ live c₂, y ∈ live ctx ∨ s.next ≤ y) ∧
    (∀ Γ t Δ, (∀ y ∈ Γ, y ∉ live ctx ∧ y < s.next) →
      LinL D (Γ ∪ liveF c₁ ∪ liveF c₂) t Δ → LinL D (Γ ∪ liveF ctx) (pre t) Δ) ∧
    (∀ t, ∃ K, bnd (pre t) = K ++ bnd t ∧ K.Nodup ∧ ∀ y ∈ K, s.next ≤ y ∧ y < s'.next) := by
  simp only [splitCtx] at h
  split at h
  · obtain ⟨_, _, h, _⟩ := ok_bind h; exact (ok_throw h).elim
  rename_i hlen
  have hlen : m.ms.length = ctx.length := by simpa using hlen
  obtain ⟨⟨preL, a₁, a₂⟩, s₁, hfor, hrest⟩ := ok_bind h
  obtain ⟨_, s₂, hrf, hfin⟩ := ok_bind hrest
  obtain ⟨hres, rfl⟩ := ok_pure hfin
  simp only [Prod.mk.injEq] at hres
  obtain ⟨rfl, rfl, rfl⟩ := hres
  obtain ⟨hn₂, hm₂⟩ := ok_readFact hrf
  have hzip : (ctx.zip m.ms).map (·.1) = ctx := by
    rw [List.map_fst_zip]; vomega
  have I := forIn_rule (ctx.zip m.ms) _ (fun pfx (b : List (Tm → Tm) × Array (Option Var) ×
      Array (Option Var)) st => SplitInv D s pfx b.1 b.2.1 b.2.2 st) ?step (ctx.zip m.ms) []
      ([], #[], #[]) s _ s₁ (by simp) ?init hfor
  case init =>
    refine ⟨Grows.refl s, trivial, by simp [live], by simp [live],
      by simp [live], by simp [live], by simp [live], ?_, ?_⟩
    · intro Γ t Δ _ h; simpa [liveF, live, appPre] using h
    · intro t; exact ⟨[], by simp [appPre], by simp, by simp⟩
  case step =>
    intro pfx a rest b st r st' hL hI hf
    obtain ⟨preL, c₁, c₂⟩ := b
    obtain ⟨o, ma, mb⟩ := a
    -- The slot's variable is not among the earlier slots', and below the counter.
    have hfresh : ∀ x, o = some x → x ∉ live (pfx.map (·.1)) ∧ x < s.next := by
      intro x hx
      have hc : live ctx = live (pfx.map (·.1)) ++ x :: live (rest.map (·.1)) := by
        rw [← hzip, ← hL]; simp [live, List.filterMap_append, hx]
      refine ⟨fun hm => ?_, hlt x (by rw [hc]; simp)⟩
      rw [hc] at hnd
      exact (List.nodup_append.1 hnd).2.2 x hm x (by simp) rfl
    have hDx : ∀ x, o = some x → ma = true → mb = true → D x := by
      intro x hx ha hb
      apply hD
      rw [← hL]; simp [bothVars, List.filterMap_append, hx, ha, hb]
    simp only at hf
    have hI' := hI
    obtain ⟨g, sl, n₁, n₂, dj, lt, og, pr, bn⟩ := hI'
    rcases o with _ | x <;> rcases ma <;> rcases mb
    -- dead, unused
    · obtain ⟨rfl, rfl⟩ := ok_pure hf
      refine ⟨_, rfl, hI.step (Grows.refl _) ⟨rfl, rfl, rfl, rfl⟩ (by simp) (by simp) (by simp)
        (by simp) ?_ bn⟩
      intro Γ t Δ hΓ ht
      simpa [liveF] using pr Γ t Δ (by simpa using hΓ) (by simpa [liveF] using ht)
    -- dead, used: throws
    all_goals try (obtain ⟨_, _, h, _⟩ := ok_bind hf; exact (ok_throw h).elim)
    · -- live, unused: dropped
      obtain ⟨rfl, rfl⟩ := ok_pure hf
      have hx := hfresh x rfl
      refine ⟨_, rfl, hI.step (Grows.refl _) ⟨rfl, rfl⟩ (by simpa using hx) (by simp) (by simp)
        (by simp) ?_ ?_⟩
      · intro Γ t Δ hΓ ht
        have hxΓ : x ∉ Γ := fun h => (hΓ x h).1 (by simp)
        rw [appPre_cons]
        have := pr (insert x Γ) (.drop x t) Δ (fun y hy => by
            rcases Finset.mem_insert.1 hy with rfl | hy
            · exact hx
            · exact ⟨fun h => (hΓ y hy).1 (by simp [h]), (hΓ y hy).2⟩)
          (by
            refine .drop (by simp) ?_
            convert ht using 1
            ext y; by_cases hy : y = x
            · subst hy
              have h₁ : y ∉ live c₁.toList := fun h => by
                rcases og y (by simp [h]) with h | h
                · exact hx.1 h
                · vomega
              have h₂ : y ∉ live c₂.toList := fun h => by
                rcases og y (by simp [h]) with h | h
                · exact hx.1 h
                · vomega
              simp [liveF, hxΓ, h₁, h₂]
            · simp [liveF, hy])
        convert this using 1
        ext y; simp [liveF] <;> tauto
      · intro t
        obtain ⟨K, hK, n, r⟩ := bn (.drop x t)
        exact ⟨K, by rw [appPre_cons, hK]; rfl, n, r⟩
    · -- live, right only
      obtain ⟨rfl, rfl⟩ := ok_pure hf
      have hx := hfresh x rfl
      refine ⟨_, rfl, hI.step (Grows.refl _) ⟨rfl, rfl⟩ (by simpa using hx) (by simp) (by simp)
        (by simp; have := hx.2; have := g.next; vomega) ?_ bn⟩
      intro Γ t Δ hΓ ht
      have := pr (insert x Γ) t Δ (fun y hy => by
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact hx
          · exact ⟨fun h => (hΓ y hy).1 (by simp [h]), (hΓ y hy).2⟩)
        (by convert ht using 1; ext y; simp [liveF] <;> tauto)
      convert this using 1
      ext y; simp [liveF] <;> tauto
    · -- live, left only
      obtain ⟨rfl, rfl⟩ := ok_pure hf
      have hx := hfresh x rfl
      refine ⟨_, rfl, hI.step (Grows.refl _) ⟨rfl, rfl⟩ (by simpa using hx) (by simp) (by simp)
        (by simp; have := hx.2; have := g.next; vomega) ?_ bn⟩
      intro Γ t Δ hΓ ht
      have := pr (insert x Γ) t Δ (fun y hy => by
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact hx
          · exact ⟨fun h => (hΓ y hy).1 (by simp [h]), (hΓ y hy).2⟩)
        (by convert ht using 1; ext y; simp [liveF] <;> tauto)
      convert this using 1
      ext y; simp [liveF] <;> tauto
    · -- live, both: copied
      obtain ⟨x', s₂, h₁, h₂⟩ := ok_bind hf
      obtain ⟨hx', hn', hm'⟩ := ok_freshLike h₁
      obtain ⟨d, s₃, h₃, h₄⟩ := ok_bind h₂
      obtain ⟨hd, hs3⟩ := ok_get h₃
      rw [hd, hs3] at h₄
      clear h₂
      have hfin : r = .yield ((fun t => Tm.copy x x' t) :: preL, c₁.push (some x), c₂.push (some x'))
          ∧ st'.next = s₂.next ∧ st'.mach = s₂.mach := by
        split at h₄
        · obtain ⟨_, s₄, h₅, h₆⟩ := ok_bind h₄
          have := ok_modify h₅
          obtain ⟨rfl, rfl⟩ := ok_pure h₆
          subst this; exact ⟨rfl, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := ok_pure h₄; exact ⟨rfl, rfl, rfl⟩
      obtain ⟨rfl, hn'', hm''⟩ := hfin
      have hx := hfresh x rfl
      have gst : Grows st st' := ⟨by vomega, hm''.trans hm'⟩
      refine ⟨_, rfl, hI.step gst ⟨rfl, x', rfl, by have := g.next; vomega, by vomega⟩
        (by simpa using hx) ?_ ?_ ?_ ?_ ?_⟩
      · intro y hy; simp at hy; rcases hy with rfl | rfl
        · exact .inl rfl
        · exact .inr hx'
      · intro y h₁ h₂; simp at h₁ h₂; subst h₁; have := hx.2; have := g.next; vomega
      · intro y hy; simp at hy; rcases hy with rfl | rfl
        · have := hx.2; have := g.next; vomega
        · vomega
      · intro Γ t Δ hΓ ht
        rw [appPre_cons]
        have := pr (insert x Γ) (.copy x x' t) Δ (fun y hy => by
            rcases Finset.mem_insert.1 hy with rfl | hy
            · exact hx
            · exact ⟨fun h => (hΓ y hy).1 (by simp [h]), (hΓ y hy).2⟩)
          (by
            refine .copy (by simp) (hDx x rfl rfl rfl) ?_
            convert ht using 1
            ext y; simp [liveF] <;> tauto)
        convert this using 1
        ext y; simp [liveF] <;> tauto
      · intro t
        obtain ⟨K, hK, n, r⟩ := bn (.copy x x' t)
        refine ⟨K ++ [x'], by rw [appPre_cons, hK]; simp [Spike670.bnd], ?_, ?_⟩
        · simp only [List.nodup_append, n, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
            List.nodup_nil, and_self, List.mem_cons, or_false, true_and]
          intro a ha b hb; subst hb; have := (r a ha).2; vomega
        · intro y hy
          simp at hy
          rcases hy with hy | rfl
          · have := r y hy; vomega
          · have := g.next; vomega
  obtain ⟨hg, hsl, hn₁', hn₂', hdj, hlt', hor, hpre, hbnd⟩ := I
  rw [hzip] at hor hpre
  have hs' : s'.next = s₁.next := hn₂
  refine ⟨⟨by have := hg.next; vomega, hm₂.trans hg.mach⟩, hlen, by rw [hs']; exact hsl, hn₁', hn₂', hdj,
    by rw [hs']; exact hlt', hor, ?_, ?_⟩
  · intro Γ t Δ hΓ ht; exact hpre Γ t Δ hΓ (by simpa [liveF] using ht)
  · intro t; obtain ⟨K, a, b, c⟩ := hbnd t; exact ⟨K, a, b, by rw [hs']; exact c⟩

end Backend2.Spike670
