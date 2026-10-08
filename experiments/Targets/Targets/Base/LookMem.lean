import Targets.Base.Look

/-!
# Base — runs with memory, computed

`look` decides the steps that keep every memory and allocate nothing.  `runM` adds the four memory
steps (`alloc`, `free`, `load`, `store`) at a finite memory kept as a list of cells (`LMem`): the
step allocates one past the largest location in use.  A closed program's run is then a computation
the kernel performs.

* `memAt`: a memory redex at an evaluation position of the term, with its context.
* `memOp`: the memory step at such a redex, on the list.
* `runM_sound`: every run `runM` computes is a run of Core's machine (`Steps`), from the memory the
  list denotes (`LMem.heap`) to the memory the final list denotes.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- A finite memory, as its cells; the first cell at a location is its content. -/
abbrev LMem := List (Loc × Val)

/-- The memory a list of cells denotes. -/
def LMem.heap (m : LMem) : Heap := fun ℓ => List.lookup ℓ m

/-- One past the largest location in use. -/
def LMem.fresh (m : LMem) : Loc := (m.map Prod.fst).foldr max 0 + 1

theorem lookup_gt : ∀ (m : LMem) (ℓ : Loc), (m.map Prod.fst).foldr max 0 < ℓ →
    List.lookup ℓ m = none
  | [], _, _ => rfl
  | (k, v) :: m, ℓ, h => by
      simp only [List.map_cons, List.foldr_cons] at h
      have hk : k < ℓ := lt_of_le_of_lt (le_max_left _ _) h
      have hm : (m.map Prod.fst).foldr max 0 < ℓ := lt_of_le_of_lt (le_max_right _ _) h
      have hne : (ℓ == k) = false := by rw [beq_eq_false_iff_ne]; exact fun he => absurd hk (by rw [he]; exact lt_irrefl k)
      simp only [List.lookup, hne]
      exact lookup_gt m ℓ hm

/-- The fresh location is free. -/
theorem LMem.heap_fresh (m : LMem) : m.heap m.fresh = none :=
  lookup_gt m _ (Nat.lt_succ_self _)

/-- A cell in front updates the memory. -/
theorem LMem.heap_cons (m : LMem) (ℓ : Loc) (v : Val) :
    LMem.heap ((ℓ, v) :: m) = (LMem.heap m).upd ℓ v := by
  funext k
  simp only [LMem.heap, List.lookup, Heap.upd]
  by_cases h : k = ℓ
  · subst h; simp
  · have : (k == ℓ) = false := by simp [h]
    simp [this, h]

/-- Dropping every cell at a location removes it from the memory. -/
theorem LMem.heap_filter (m : LMem) (ℓ : Loc) :
    LMem.heap (m.filter fun c => c.1 != ℓ) = (LMem.heap m).del ℓ := by
  funext k
  simp only [LMem.heap, Heap.del]
  induction m with
  | nil => simp
  | cons c m ih =>
      obtain ⟨k', v⟩ := c
      by_cases hk' : k' = ℓ
      · subst hk'
        have hf : (k' != k') = false := by simp
        simp only [List.filter_cons, hf, Bool.false_eq_true, if_false]
        rw [ih]
        by_cases hk : k = k'
        · simp [hk]
        · have : (k == k') = false := by simp [hk]
          simp [List.lookup, this, hk]
      · have hf : (k' != ℓ) = true := by simp [hk']
        simp only [List.filter_cons, hf, if_true, List.lookup]
        by_cases hk : k = k'
        · subst hk; simp [hk']
        · have : (k == k') = false := by simp [hk]
          simp only [this]
          exact ih

/-! ### The memory redex at an evaluation position -/

/-- A memory redex at an evaluation position of the term, and its context: the redex is `alloc v`,
`free ℓ`, `load ℓ` or `store ℓ v`, the argument a value. -/
def memAt : Expr → Option (Kont × Expr)
  | .pair a b =>
      match valOf? a with
      | some va => (memAt b).map fun p => (.pairR va p.1, p.2)
      | none => (memAt a).map fun p => (.pairL p.1 b, p.2)
  | .inj₁ a => (memAt a).map fun p => (.inj₁ p.1, p.2)
  | .inj₂ a => (memAt a).map fun p => (.inj₂ p.1, p.2)
  | .seq a b => (memAt a).map fun p => (.seq p.1 b, p.2)
  | .letpair a b => (memAt a).map fun p => (.letpair p.1 b, p.2)
  | .case a b₁ b₂ => (memAt a).map fun p => (.case p.1 b₁ b₂, p.2)
  | .app f a =>
      match valOf? a with
      | none => (memAt a).map fun p => (.appR f p.1, p.2)
      | some va =>
          match f with
          | .prim .alloc => some (.hole, .app f a)
          | .prim .free => some (.hole, .app f a)
          | .prim .load => some (.hole, .app f a)
          | .app (.prim .store) (.loc ℓ) => some (.hole, .app (.app (.prim .store) (.loc ℓ)) a)
          | _ =>
              match valOf? f with
              | some _ => none
              | none => (memAt f).map fun p => (.appL p.1 va, p.2)
  | _ => none

theorem memAt_sound : ∀ (e : Expr) (K : Kont) (x : Expr), memAt e = some (K, x) → e = K.plug x
  | .pair a b, K, x, h => by
      unfold memAt at h
      rcases hva : valOf? a with _ | va <;> rw [hva] at h <;> simp only at h
      · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
        rw [memAt_sound a K' x' h']; rfl
      · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
        rw [valOf?_some hva, memAt_sound b K' x' h']; rfl
  | .inj₁ a, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .inj₂ a, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .seq a b, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .letpair a b, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .case a b₁ b₂, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .app f a, K, x, h => by
      unfold memAt at h
      rcases hva : valOf? a with _ | va <;> rw [hva] at h <;> simp only at h
      · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
        rw [memAt_sound a K' x' h']; rfl
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · rcases hvf : valOf? f with _ | vf <;> rw [hvf] at h <;> simp only at h
          · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
            rw [memAt_sound f K' x' h', valOf?_some hva]; rfl
          · cases h
  | .var _, _, _, h | .unit, _, _, h | .lam _, _, _, h | .loc _, _, _, h | .prim _, _, _, h => by
      simp [memAt] at h

/-! ### The memory steps -/

/-- The memory step at a redex `memAt` finds. -/
def memOp (m : LMem) : Expr → Option (LMem × Expr)
  | .app (.prim .alloc) a => (valOf? a).map fun v => ((m.fresh, v) :: m, .loc m.fresh)
  | .app (.prim .free) (.loc ℓ) =>
      (List.lookup ℓ m).map fun v => (m.filter fun c => c.1 != ℓ, v.1)
  | .app (.prim .load) (.loc ℓ) => (List.lookup ℓ m).map fun v => (m, v.1)
  | .app (.app (.prim .store) (.loc ℓ)) a =>
      match valOf? a, List.lookup ℓ m with
      | some v, some _ => some ((ℓ, v) :: m, .unit)
      | _, _ => none
  | _ => none

theorem memOp_sound {m m' : LMem} {a a' : Expr} (h : memOp m a = some (m', a')) :
    Head (ℍ := ℍ) m.heap a m'.heap a' := by
  unfold memOp at h
  split at h
  · rename_i x
    obtain ⟨v, hv, hm⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
    rw [valOf?_some hv, LMem.heap_cons]
    exact Head.alloc m.heap v m.fresh (LMem.heap_fresh m)
  · rename_i ℓ
    obtain ⟨v, hv, hm⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
    rw [LMem.heap_filter]
    exact Head.free m.heap ℓ v hv
  · rename_i ℓ
    obtain ⟨v, hv, hm⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
    exact Head.load m.heap ℓ v hv
  · rename_i ℓ x
    split at h
    · rename_i v w hv hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [valOf?_some hv, LMem.heap_cons]
      exact Head.store m.heap ℓ v w hw
    · cases h
  · cases h

/-! ### Runs -/

/-- One step: `look`'s memory-free step, or a memory step at a redex `memAt` finds. -/
def stepM (m : LMem) (e : Expr) : Option (LMem × Expr) :=
  match look e with
  | .red K _ a' => some (m, K.plug a')
  | _ =>
      match memAt e with
      | some (K, x) => (memOp m x).map fun p => (p.1, K.plug p.2)
      | none => none

theorem stepM_sound {m m' : LMem} {e e' : Expr} (h : stepM m e = some (m', e')) :
    Step1 (ℍ := ℍ) m.heap e m'.heap e' := by
  unfold stepM at h
  split at h
  · rename_i K a a' hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hok := look_sound (ℍ := ℍ) e
    rw [hl] at hok
    obtain ⟨he, hh, -⟩ := hok
    exact ⟨K, a, a', he, rfl, hh m.heap⟩
  · split at h
    · rename_i K x hK
      obtain ⟨⟨m₁, x'⟩, hx, hm⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
      exact ⟨K, x, x', memAt_sound e K x hK, rfl, memOp_sound hx⟩
    · cases h

/-- At most `k` steps from `(m, e)`, ending where no step is found. -/
def runM : ℕ → LMem → Expr → LMem × Expr
  | 0, m, e => (m, e)
  | k + 1, m, e =>
      match stepM m e with
      | some (m', e') => runM k m' e'
      | none => (m, e)

/-- **The run `runM` computes is a run of Core's machine.** -/
theorem runM_sound : ∀ (k : ℕ) (m : LMem) (e : Expr),
    Steps (ℍ := ℍ) m.heap e (runM k m e).1.heap (runM k m e).2
  | 0, m, e => .refl _ _
  | k + 1, m, e => by
      unfold runM
      split
      · rename_i m' e' hs
        exact .more (stepM_sound hs) (runM_sound k m' e')
      · exact .refl _ _

/-- The empty list denotes the empty memory. -/
theorem LMem.heap_nil : LMem.heap [] = Adequacy.emptyMem := rfl

end Targets

end
