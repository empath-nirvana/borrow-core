import Lowering.LIRPrint
import Core.Steps
import Core.Alloc

/-!
# Lowering — the source machine's runs under an allocator, read big-step  `[spec §56]`

The print's simulation (`Lowering/PrintFwd.lean`) follows a run of the source machine into the
interpreter's evaluation, which is big-step. `BigN A k c μ e c' μ' w`: `e` runs from the memory `μ`
at allocation count `c` to the value `w` at `μ'` and count `c'`, every allocation at the allocator
`A`'s location (`AHead`), the derivation of size `k`, in the machine's order (a pair left first, an
application its argument first, then its function, then the head step on the two values). A value
is its own run, of size `0`. An application whose function runs to `store` is the value
`store v` (`storeF`).

`big_of_arun`: a run under the allocator to a value, of a term with no effect primitive from a
memory holding none (`HeapEF`), is such a derivation. The proof reads each step backwards
(`big_expand`): a head step under a context is a derivation of the context around the redex's.
The effect-free terms are kept by every step (`effFree_head`).
-/

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Lowering
open BoCa
open BoCa.BoLo (Heap Head Step1 Steps Kont Alloc AHead AStep1 ARun)

/-- **A run to a value, big-step, under the allocator `A`**, its derivation of size `k`, from
allocation count `c` to `c'`. -/
inductive BigN (A : Alloc) : Nat → Nat → Heap → Expr → Nat → Heap → Val → Prop where
  | val (c : Nat) (μ : Heap) (v : Val) : BigN A 0 c μ v.1 c μ v
  | pair {i j c c₁ c₂ : Nat} {μ μ₁ μ₂ : Heap} {a b : Expr} {u₁ u₂ : Val}
      (ha : BigN A i c μ a c₁ μ₁ u₁) (hb : BigN A j c₁ μ₁ b c₂ μ₂ u₂) :
      BigN A (i + j + 1) c μ (.pair a b) c₂ μ₂ (Val.pair u₁ u₂)
  | inj₁ {i c c₁ : Nat} {μ μ₁ : Heap} {a : Expr} {u : Val} (ha : BigN A i c μ a c₁ μ₁ u) :
      BigN A (i + 1) c μ (.inj₁ a) c₁ μ₁ (Val.inj₁ u)
  | inj₂ {i c c₁ : Nat} {μ μ₁ : Heap} {a : Expr} {u : Val} (ha : BigN A i c μ a c₁ μ₁ u) :
      BigN A (i + 1) c μ (.inj₂ a) c₁ μ₁ (Val.inj₂ u)
  | seq {i j c c₁ c₂ : Nat} {μ μ₁ μ₂ : Heap} {a b : Expr} {w : Val}
      (ha : BigN A i c μ a c₁ μ₁ Val.unit) (hb : BigN A j c₁ μ₁ b c₂ μ₂ w) :
      BigN A (i + j + 1) c μ (.seq a b) c₂ μ₂ w
  | letpair {i j c c₁ c₂ : Nat} {μ μ₁ μ₂ : Heap} {a b : Expr} {v₁ v₂ w : Val}
      (ha : BigN A i c μ a c₁ μ₁ (Val.pair v₁ v₂))
      (hb : BigN A j c₁ μ₁ ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) c₂ μ₂ w) :
      BigN A (i + j + 1) c μ (.letpair a b) c₂ μ₂ w
  | case₁ {i j c c₁ c₂ : Nat} {μ μ₁ μ₂ : Heap} {s a b : Expr} {v w : Val}
      (hs : BigN A i c μ s c₁ μ₁ (Val.inj₁ v)) (ha : BigN A j c₁ μ₁ (a.subst 0 v) c₂ μ₂ w) :
      BigN A (i + j + 1) c μ (.case s a b) c₂ μ₂ w
  | case₂ {i j c c₁ c₂ : Nat} {μ μ₁ μ₂ : Heap} {s a b : Expr} {v w : Val}
      (hs : BigN A i c μ s c₁ μ₁ (Val.inj₂ v)) (hb : BigN A j c₁ μ₁ (b.subst 0 v) c₂ μ₂ w) :
      BigN A (i + j + 1) c μ (.case s a b) c₂ μ₂ w
  | app {i j k c c₁ c₂ c₃ c' : Nat} {μ μ₁ μ₂ μ₃ μ' : Heap} {f a r : Expr} {va vf w : Val}
      (ha : BigN A i c μ a c₁ μ₁ va) (hf : BigN A j c₁ μ₁ f c₂ μ₂ vf)
      (hh : AHead (ℍ := ℍ) A c₂ μ₂ (.app vf.1 va.1) c₃ μ₃ r) (hr : BigN A k c₃ μ₃ r c' μ' w) :
      BigN A (i + j + k + 1) c μ (.app f a) c' μ' w
  | storeF {i j c c₁ c₂ : Nat} {μ μ₁ μ₂ : Heap} {f a : Expr} {va : Val}
      (ha : BigN A i c μ a c₁ μ₁ va) (hf : BigN A j c₁ μ₁ f c₂ μ₂ (Val.prim .store)) :
      BigN A (i + j + 1) c μ (.app f a) c₂ μ₂ (Val.storeV va)

/-! ### Inversions -/

/-- **A value is its own run.** -/
theorem big_val_inv {A : Alloc} : ∀ {n c c' : Nat} {μ μ' : Heap} {e : Expr} {w : Val},
    BigN (ℍ := ℍ) A n c μ e c' μ' w → ∀ (v : Val), e = v.1 → c' = c ∧ μ' = μ ∧ w = v := by
  intro n c c' μ μ' e w h
  induction h with
  | val c μ u => intro v hv; exact ⟨rfl, rfl, Subtype.ext hv⟩
  | pair ha hb iha ihb =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      cases hv' with
      | pair h₁ h₂ =>
        obtain ⟨rfl, rfl, rfl⟩ := iha ⟨_, h₁⟩ rfl
        obtain ⟨rfl, rfl, rfl⟩ := ihb ⟨_, h₂⟩ rfl
        exact ⟨rfl, rfl, Subtype.ext hv⟩
  | inj₁ ha iha =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      cases hv' with
      | inj₁ h₁ =>
        obtain ⟨rfl, rfl, rfl⟩ := iha ⟨_, h₁⟩ rfl
        exact ⟨rfl, rfl, Subtype.ext hv⟩
  | inj₂ ha iha =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      cases hv' with
      | inj₂ h₁ =>
        obtain ⟨rfl, rfl, rfl⟩ := iha ⟨_, h₁⟩ rfl
        exact ⟨rfl, rfl, Subtype.ext hv⟩
  | seq => intro v hv; have := hv ▸ v.2; simp at this
  | letpair => intro v hv; have := hv ▸ v.2; simp at this
  | case₁ => intro v hv; have := hv ▸ v.2; simp at this
  | case₂ => intro v hv; have := hv ▸ v.2; simp at this
  | app ha hf hh hr iha ihf ihr =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      obtain ⟨rfl, h₂⟩ := isVal_app_iff.mp hv'
      obtain ⟨rfl, rfl, rfl⟩ := iha ⟨_, h₂⟩ rfl
      obtain ⟨rfl, rfl, rfl⟩ := ihf (Val.prim .store) rfl
      exact absurd (hh.toHead) (by intro h; cases h)
  | storeF ha hf iha ihf =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      obtain ⟨rfl, h₂⟩ := isVal_app_iff.mp hv'
      obtain ⟨rfl, rfl, rfl⟩ := iha ⟨_, h₂⟩ rfl
      obtain ⟨rfl, rfl, -⟩ := ihf (Val.prim .store) rfl
      exact ⟨rfl, rfl, Subtype.ext hv⟩

theorem big_pair_inv {A : Alloc} {n c c' : Nat} {μ μ' : Heap} {a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) A n c μ (.pair a b) c' μ' w) :
    ∃ i j c₁ μ₁ u₁ u₂, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) A i c μ a c₁ μ₁ u₁ ∧
      BigN (ℍ := ℍ) A j c₁ μ₁ b c' μ' u₂ ∧ w = Val.pair u₁ u₂ := by
  generalize he : Expr.pair a b = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.pair a b) := he ▸ w.2
      cases hv with
      | pair h₁ h₂ => exact ⟨0, 0, _, _, ⟨a, h₁⟩, ⟨b, h₂⟩, le_refl _, le_refl _, .val _ _ ⟨a, h₁⟩,
          .val _ _ ⟨b, h₂⟩, Subtype.ext he.symm⟩
  | pair ha hb =>
      simp only [Expr.pair.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, _, _, _, _, by omega, by omega, ha, hb, rfl⟩
  | _ => simp at he

theorem big_inj₁_inv {A : Alloc} {n c c' : Nat} {μ μ' : Heap} {a : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) A n c μ (.inj₁ a) c' μ' w) :
    ∃ i u, i ≤ n ∧ BigN (ℍ := ℍ) A i c μ a c' μ' u ∧ w = Val.inj₁ u := by
  generalize he : Expr.inj₁ a = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.inj₁ a) := he ▸ w.2
      cases hv with
      | inj₁ h₁ => exact ⟨0, ⟨a, h₁⟩, le_refl _, .val _ _ ⟨a, h₁⟩, Subtype.ext he.symm⟩
  | inj₁ ha => simp only [Expr.inj₁.injEq] at he; subst he; exact ⟨_, _, by omega, ha, rfl⟩
  | _ => simp at he

theorem big_inj₂_inv {A : Alloc} {n c c' : Nat} {μ μ' : Heap} {a : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) A n c μ (.inj₂ a) c' μ' w) :
    ∃ i u, i ≤ n ∧ BigN (ℍ := ℍ) A i c μ a c' μ' u ∧ w = Val.inj₂ u := by
  generalize he : Expr.inj₂ a = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.inj₂ a) := he ▸ w.2
      cases hv with
      | inj₂ h₁ => exact ⟨0, ⟨a, h₁⟩, le_refl _, .val _ _ ⟨a, h₁⟩, Subtype.ext he.symm⟩
  | inj₂ ha => simp only [Expr.inj₂.injEq] at he; subst he; exact ⟨_, _, by omega, ha, rfl⟩
  | _ => simp at he

theorem big_seq_inv {A : Alloc} {n c c' : Nat} {μ μ' : Heap} {a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) A n c μ (.seq a b) c' μ' w) :
    ∃ i j c₁ μ₁, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) A i c μ a c₁ μ₁ Val.unit ∧
      BigN (ℍ := ℍ) A j c₁ μ₁ b c' μ' w := by
  generalize he : Expr.seq a b = E at h
  cases h with
  | val => have := he ▸ w.2; simp at this
  | seq ha hb =>
      simp only [Expr.seq.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, _, _, by omega, by omega, ha, hb⟩
  | _ => simp at he

theorem big_letpair_inv {A : Alloc} {n c c' : Nat} {μ μ' : Heap} {a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) A n c μ (.letpair a b) c' μ' w) :
    ∃ i j c₁ μ₁ v₁ v₂, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) A i c μ a c₁ μ₁ (Val.pair v₁ v₂) ∧
      BigN (ℍ := ℍ) A j c₁ μ₁ ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) c' μ' w := by
  generalize he : Expr.letpair a b = E at h
  cases h with
  | val => have := he ▸ w.2; simp at this
  | letpair ha hb =>
      simp only [Expr.letpair.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, _, _, _, _, by omega, by omega, ha, hb⟩
  | _ => simp at he

theorem big_case_inv {A : Alloc} {n c c' : Nat} {μ μ' : Heap} {s a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) A n c μ (.case s a b) c' μ' w) :
    (∃ i j c₁ μ₁ v, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) A i c μ s c₁ μ₁ (Val.inj₁ v) ∧
      BigN (ℍ := ℍ) A j c₁ μ₁ (a.subst 0 v) c' μ' w) ∨
    (∃ i j c₁ μ₁ v, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) A i c μ s c₁ μ₁ (Val.inj₂ v) ∧
      BigN (ℍ := ℍ) A j c₁ μ₁ (b.subst 0 v) c' μ' w) := by
  generalize he : Expr.case s a b = E at h
  cases h with
  | val => have := he ▸ w.2; simp at this
  | case₁ hs ha =>
      simp only [Expr.case.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact .inl ⟨_, _, _, _, _, by omega, by omega, hs, ha⟩
  | case₂ hs hb =>
      simp only [Expr.case.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact .inr ⟨_, _, _, _, _, by omega, by omega, hs, hb⟩
  | _ => simp at he

/-- **An application**: its argument, then its function, then the head step on the two values
and the rest; or the function runs to `store` and the application is the value `store v`. -/
theorem big_app_inv {A : Alloc} {n c c' : Nat} {μ μ' : Heap} {f a : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) A n c μ (.app f a) c' μ' w) :
    (∃ i j k c₁ μ₁ c₂ μ₂ c₃ μ₃ va vf r, i ≤ n ∧ j ≤ n ∧ k < n ∧
      BigN (ℍ := ℍ) A i c μ a c₁ μ₁ va ∧ BigN (ℍ := ℍ) A j c₁ μ₁ f c₂ μ₂ vf ∧
      AHead (ℍ := ℍ) A c₂ μ₂ (.app vf.1 va.1) c₃ μ₃ r ∧ BigN (ℍ := ℍ) A k c₃ μ₃ r c' μ' w) ∨
    (∃ i j c₁ μ₁ va, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) A i c μ a c₁ μ₁ va ∧
      BigN (ℍ := ℍ) A j c₁ μ₁ f c' μ' (Val.prim .store) ∧ w = Val.storeV va) := by
  generalize he : Expr.app f a = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.app f a) := he ▸ w.2
      obtain ⟨rfl, ha⟩ := isVal_app_iff.mp hv
      exact .inr ⟨0, 0, _, _, ⟨a, ha⟩, le_refl _, le_refl _, .val _ _ ⟨a, ha⟩,
        .val _ _ (Val.prim .store), Subtype.ext he.symm⟩
  | app ha hf hh hr =>
      simp only [Expr.app.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, by omega, by omega, by omega, ha, hf, hh, hr⟩
  | storeF ha hf =>
      simp only [Expr.app.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .inr ⟨_, _, _, _, _, by omega, by omega, ha, hf, rfl⟩
  | _ => simp at he

/-! ### Effect-free terms are kept by the machine -/

/-- Every cell holds an effect-free value. -/
def HeapEF (μ : Heap) : Prop := ∀ ℓ v, μ ℓ = some v → effFreeB v.1 = true

theorem effFreeB_shift : ∀ (e : Expr) (d c : Nat), effFreeB (e.shift d c) = effFreeB e
  | .var i, d, c => by simp only [Expr.shift]; split <;> rfl
  | .unit, _, _ | .loc _, _, _ | .prim _, _, _ => rfl
  | .pair a b, d, c | .seq a b, d, c | .app a b, d, c => by
      simp only [Expr.shift, effFreeB, effFreeB_shift a, effFreeB_shift b]
  | .letpair a b, d, c => by simp only [Expr.shift, effFreeB, effFreeB_shift a, effFreeB_shift b]
  | .inj₁ a, d, c | .inj₂ a, d, c => by simp only [Expr.shift, effFreeB, effFreeB_shift a]
  | .lam a, d, c => by simp only [Expr.shift, effFreeB, effFreeB_shift a]
  | .case s a b, d, c => by
      simp only [Expr.shift, effFreeB, effFreeB_shift s, effFreeB_shift a, effFreeB_shift b]

theorem effFreeB_valShift (v : Val) (d c : Nat) : effFreeB (v.shift d c).1 = effFreeB v.1 := by
  simpa [Val.shift] using effFreeB_shift v.1 d c

theorem effFreeB_subst : ∀ (e : Expr) (j : Nat) (v : Val), effFreeB e = true →
    effFreeB v.1 = true → effFreeB (e.subst j v) = true
  | .var i, j, v, _, hv => by
      simp only [Expr.subst]; split
      · exact hv
      · split <;> rfl
  | .unit, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ => h
  | .pair a b, j, v, h, hv | .seq a b, j, v, h, hv | .app a b, j, v, h, hv => by
      simp only [effFreeB, Bool.and_eq_true] at h
      simp only [Expr.subst, effFreeB, effFreeB_subst a j v h.1 hv, effFreeB_subst b j v h.2 hv]
      rfl
  | .letpair a b, j, v, h, hv => by
      simp only [effFreeB, Bool.and_eq_true] at h
      have hv' : effFreeB (v.shift 2 0).1 = true := by rw [effFreeB_valShift]; exact hv
      simp only [Expr.subst, effFreeB, effFreeB_subst a j v h.1 hv, effFreeB_subst b _ _ h.2 hv']
      rfl
  | .inj₁ a, j, v, h, hv | .inj₂ a, j, v, h, hv => by
      simp only [effFreeB] at h
      simp only [Expr.subst, effFreeB, effFreeB_subst a j v h hv]
  | .lam a, j, v, h, hv => by
      simp only [effFreeB] at h
      have hv' : effFreeB (v.shift 1 0).1 = true := by rw [effFreeB_valShift]; exact hv
      simp only [Expr.subst, effFreeB, effFreeB_subst a _ _ h hv']
  | .case s a b, j, v, h, hv => by
      simp only [effFreeB, Bool.and_eq_true] at h
      have hv' : effFreeB (v.shift 1 0).1 = true := by rw [effFreeB_valShift]; exact hv
      simp only [Expr.subst, effFreeB, effFreeB_subst s j v h.1.1 hv, effFreeB_subst a _ _ h.1.2 hv',
        effFreeB_subst b _ _ h.2 hv']
      rfl

omit [HostIs ℍ] in
/-- A host operation answers an effect-free value. -/
theorem effFreeB_call {op : HostOp} {v r : Val} (h : ℍ.call op v = some r) :
    effFreeB r.1 = true := by
  have hb : ∀ b, effFreeB (Val.bool b).1 = true := by intro b; cases b <;> rfl
  have hw : ∀ (w : Width) (n : w.bits), effFreeB (Val.ofBits w n).1 = true := by
    intro w; cases w <;> intro n <;> rfl
  have ho : ∀ (o : Option Val), (∀ x, o = some x → effFreeB x.1 = true) →
      effFreeB (Val.opt o).1 = true := by
    intro o ho; cases o with
    | none => rfl
    | some x => simpa [Val.opt, effFreeB, Val.inj₁] using ho x rfl
  unfold Host.call at h
  split at h <;> simp only [Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨_, _, rfl⟩ := h <;>
    first
    | rfl
    | exact hb _
    | exact hw _ _
    | (apply ho; intro x hx; simp only [Option.map_eq_some_iff] at hx
       obtain ⟨_, _, rfl⟩ := hx; first | rfl | exact hw _ _)

theorem effFreeB_tabFill (f : Val) (hf : effFreeB f.1 = true) (ℓ : Loc) (n : UInt32) :
    ∀ i k, effFreeB (tabFill f ℓ n i k) = true
  | _, 0 => rfl
  | i, k + 1 => by
      simp only [tabFill, effFreeB, Expr.val, hf, Bool.true_and]
      exact effFreeB_tabFill f hf ℓ n (i + 1) k

theorem effFreeB_dropFill (f : Val) (hf : effFreeB f.1 = true) (ℓ : Loc) :
    ∀ i k, effFreeB (dropFill f ℓ i k) = true
  | _, 0 => rfl
  | i, k + 1 => by
      simp only [dropFill, effFreeB, Expr.val, hf, Bool.true_and]
      exact effFreeB_dropFill f hf ℓ (i + 1) k

theorem effFreeB_idxAns (ℓ : Loc) (n i : UInt32) : effFreeB (idxAns ℓ n i).1 = true := by
  unfold idxAns; split <;> rfl

theorem effFreeB_splitAns (ℓ : Loc) (n i : UInt32) : effFreeB (splitAns ℓ n i).1 = true := by
  unfold splitAns; split <;> rfl

theorem effFreeB_val_pair {a b : Val} : effFreeB (Val.pair a b).1 = (effFreeB a.1 && effFreeB b.1) :=
  rfl

/-- **A head step of an effect-free redex** from a memory of effect-free values: its reduct and
the memory after are effect-free. -/
theorem effFree_head {μ μ₁ : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ₁ a')
    (ha : effFreeB a = true) (hμ : HeapEF μ) : effFreeB a' = true ∧ HeapEF μ₁ := by
  cases h with
  | beta b v =>
      simp only [effFreeB, Expr.val, Val.lam, Bool.and_eq_true] at ha
      exact ⟨effFreeB_subst b 0 v ha.1 ha.2, hμ⟩
  | alloc v ℓ _ =>
      simp only [effFreeB, Expr.val, Val.prim, Bool.and_eq_true] at ha
      refine ⟨rfl, fun k w hk => ?_⟩
      by_cases hkℓ : k = ℓ
      · subst hkℓ; simp only [BoLo.Heap.upd_same, Option.some.injEq] at hk; subst hk; exact ha.2
      · rw [BoLo.Heap.upd_other hkℓ] at hk; exact hμ k w hk
  | free ℓ v hv =>
      refine ⟨hμ ℓ v hv, fun k w hk => ?_⟩
      by_cases hkℓ : k = ℓ
      · subst hkℓ; simp at hk
      · rw [BoLo.Heap.del_other hkℓ] at hk; exact hμ k w hk
  | load ℓ v hv => exact ⟨hμ ℓ v hv, hμ⟩
  | store ℓ v w' _ =>
      simp only [effFreeB, Expr.val, Val.prim, Bool.and_eq_true] at ha
      refine ⟨rfl, fun k w hk => ?_⟩
      by_cases hkℓ : k = ℓ
      · subst hkℓ; simp only [BoLo.Heap.upd_same, Option.some.injEq] at hk; subst hk; exact ha.2
      · rw [BoLo.Heap.upd_other hkℓ] at hk; exact hμ k w hk
  | seq e =>
      simp only [effFreeB, Bool.and_eq_true] at ha; exact ⟨ha.2, hμ⟩
  | letpair v₁ v₂ e =>
      simp only [effFreeB, Bool.and_eq_true, Expr.val, Val.pair] at ha
      have h₂ : effFreeB (v₂.shift 1 0).1 = true := by rw [effFreeB_valShift]; exact ha.1.2
      exact ⟨effFreeB_subst _ 0 v₁ (effFreeB_subst e 0 _ ha.2 h₂) ha.1.1, hμ⟩
  | case₁ v e₁ e₂ =>
      simp only [effFreeB, Bool.and_eq_true, Expr.val, Val.inj₁] at ha
      exact ⟨effFreeB_subst e₁ 0 v ha.1.2 ha.1.1, hμ⟩
  | case₂ v e₁ e₂ =>
      simp only [effFreeB, Bool.and_eq_true, Expr.val, Val.inj₂] at ha
      exact ⟨effFreeB_subst e₂ 0 v ha.2 ha.1.1, hμ⟩
  | host op v r hr => exact ⟨effFreeB_call hr, hμ⟩
  | tab c f ℓ _ =>
      simp only [effFreeB, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      refine ⟨effFreeB_tabFill f ha.2.2 ℓ _ _ _, fun k w hk => ?_⟩
      simp only [BoLo.Heap.fill] at hk
      split at hk
      · cases hk; rfl
      · exact hμ k w hk
  | idx ℓ n i => exact ⟨effFreeB_idxAns ℓ n i, hμ⟩
  | split ℓ n i => exact ⟨effFreeB_splitAns ℓ n i, hμ⟩
  | drop f ℓ n =>
      simp only [effFreeB, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      exact ⟨effFreeB_dropFill f ha.2.1 ℓ _ _, hμ⟩
  | count f n i s =>
      simp only [effFreeB, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      unfold countNext; split
      · simp [effFreeB, effPrim, Expr.val, Val.pair, Val.i32, ha.2.1, ha.2.2.2.2]
      · exact ha.2.2.2.2
  | countTry f n i s =>
      simp only [effFreeB, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      unfold countTryNext; split
      · simp [effFreeB, effPrim, Expr.val, Val.pair, Val.i32, ha.2.1, ha.2.2.2.2, effFreeB_shift]
      · simp [effFreeB, Expr.val, Val.inj₁, ha.2.2.2.2]
  | boundedFix s k a =>
      simp only [effFreeB, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      unfold boundedFixNext fixSelf; split
      · simp [effFreeB, Expr.val, Val.pair, Val.inj₁, Val.unit, ha.2.1, ha.2.2.2]
      · simp [effFreeB, effPrim, Expr.val, Val.pair, Val.inj₂, Val.lam, Val.i32, ha.2.1, ha.2.2.2,
          effFreeB_shift]
  | iterate f s => simp [effFreeB, effPrim, Expr.val, Val.prim] at ha
  | _ => simp [effFreeB, effPrim, Expr.val, Val.prim, BoLo.hndE, BoLo.ubindE, BoLo.ccatchE,
      BoLo.cfinE] at ha

theorem effFreeB_plug_inner : ∀ (K : Kont) (x : Expr), effFreeB (K.plug x) = true →
    effFreeB x = true
  | .hole, _, h => h
  | .pairL K _, x, h | .letpair K _, x, h | .seq K _, x, h => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h; exact effFreeB_plug_inner K x h.1
  | .pairR _ K, x, h | .appR _ K, x, h => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h; exact effFreeB_plug_inner K x h.2
  | .appL K _, x, h => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h; exact effFreeB_plug_inner K x h.1
  | .case K _ _, x, h => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h; exact effFreeB_plug_inner K x h.1.1
  | .inj₁ K, x, h | .inj₂ K, x, h => by
      simp only [Kont.plug, effFreeB] at h; exact effFreeB_plug_inner K x h

theorem effFreeB_plug_swap : ∀ (K : Kont) (x y : Expr), effFreeB (K.plug x) = true →
    effFreeB y = true → effFreeB (K.plug y) = true
  | .hole, _, _, _, hy => hy
  | .pairL K _, x, y, h, hy | .letpair K _, x, y, h, hy | .seq K _, x, y, h, hy => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h ⊢
      exact ⟨effFreeB_plug_swap K x y h.1 hy, h.2⟩
  | .pairR _ K, x, y, h, hy | .appR _ K, x, y, h, hy => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, effFreeB_plug_swap K x y h.2 hy⟩
  | .appL K _, x, y, h, hy => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h ⊢
      exact ⟨effFreeB_plug_swap K x y h.1 hy, h.2⟩
  | .case K _ _, x, y, h, hy => by
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨effFreeB_plug_swap K x y h.1.1 hy, h.1.2⟩, h.2⟩
  | .inj₁ K, x, y, h, hy | .inj₂ K, x, y, h, hy => by
      simp only [Kont.plug, effFreeB] at h ⊢; exact effFreeB_plug_swap K x y h hy

/-- **A step under the allocator of an effect-free term**, from a memory of effect-free values:
the term and the memory after are effect-free. -/
theorem effFree_step {A : Alloc} {c c₁ : Nat} {μ μ₁ : Heap} {e e₁ : Expr}
    (h : AStep1 (ℍ := ℍ) A c μ e c₁ μ₁ e₁) (he : effFreeB e = true) (hμ : HeapEF μ) :
    effFreeB e₁ = true ∧ HeapEF μ₁ := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  obtain ⟨ha', hμ₁⟩ := effFree_head hh.toHead (effFreeB_plug_inner K a he) hμ
  exact ⟨effFreeB_plug_swap K a a' he ha', hμ₁⟩

/-! ### Runs to a value are derivations -/

/-- A head step of an effect-free redex is a head step on an application of two values, or a
`;`, a `let` or a `case` of a value. -/
theorem head_shape {μ μ₁ : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ₁ a')
    (ha : effFreeB a = true) :
    (∃ vf va : Val, a = .app vf.1 va.1) ∨ (∃ e, a = .seq Val.unit.1 e ∧ μ₁ = μ ∧ a' = e) ∨
    (∃ v₁ v₂ e, a = .letpair (Val.pair v₁ v₂).1 e ∧ μ₁ = μ ∧
      a' = (e.subst 0 (v₂.shift 1 0)).subst 0 v₁) ∨
    (∃ v e₁ e₂, a = .case (Val.inj₁ v).1 e₁ e₂ ∧ μ₁ = μ ∧ a' = e₁.subst 0 v) ∨
    (∃ v e₁ e₂, a = .case (Val.inj₂ v).1 e₁ e₂ ∧ μ₁ = μ ∧ a' = e₂.subst 0 v) := by
  cases h with
  | beta b v => exact .inl ⟨Val.lam b, v, rfl⟩
  | alloc v ℓ _ => exact .inl ⟨Val.prim .alloc, v, rfl⟩
  | free ℓ v _ => exact .inl ⟨Val.prim .free, Val.loc ℓ, rfl⟩
  | load ℓ v _ => exact .inl ⟨Val.prim .load, Val.loc ℓ, rfl⟩
  | store ℓ v w _ => exact .inl ⟨Val.storeV (Val.loc ℓ), v, rfl⟩
  | seq => exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
  | letpair v₁ v₂ e => exact .inr (.inr (.inl ⟨v₁, v₂, e, rfl, rfl, rfl⟩))
  | case₁ v e₁ e₂ => exact .inr (.inr (.inr (.inl ⟨v, e₁, e₂, rfl, rfl, rfl⟩)))
  | case₂ v e₁ e₂ => exact .inr (.inr (.inr (.inr ⟨v, e₁, e₂, rfl, rfl, rfl⟩)))
  | host op v r _ => exact .inl ⟨Val.prim (.host op), v, rfl⟩
  | tab c f ℓ _ => exact .inl ⟨Val.prim .tab, Val.pair (Val.i32 c) f, rfl⟩
  | idx ℓ n i => exact .inl ⟨Val.prim .idx, Val.pair (Val.arr ℓ n) (Val.i32 i), rfl⟩
  | split ℓ n i => exact .inl ⟨Val.prim .split, Val.pair (Val.arr ℓ n) (Val.i32 i), rfl⟩
  | drop f ℓ n => exact .inl ⟨Val.prim .drop, Val.pair f (Val.arr ℓ n), rfl⟩
  | count f n i s =>
      exact .inl ⟨Val.prim .count, Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)), rfl⟩
  | countTry f n i s =>
      exact .inl ⟨Val.prim .countTry, Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)),
        rfl⟩
  | boundedFix s k a => exact .inl ⟨Val.prim .boundedFix, Val.pair s (Val.pair (Val.i32 k) a), rfl⟩
  | iterate f s => simp [effFreeB, effPrim, Expr.val, Val.prim] at ha
  | _ => simp [effFreeB, effPrim, Expr.val, Val.prim, BoLo.hndE, BoLo.ubindE, BoLo.ccatchE,
      BoLo.cfinE] at ha

/-- **A step read backwards**: a step under the allocator of an effect-free term, followed by a
derivation from its result, is a derivation of the whole. -/
theorem big_expand {A : Alloc} {c c₁ c' : Nat} {μ μ₁ μ' : Heap} {e e₁ : Expr} {w : Val} {n : Nat}
    (h : AStep1 (ℍ := ℍ) A c μ e c₁ μ₁ e₁) (he : effFreeB e = true)
    (hb : BigN (ℍ := ℍ) A n c₁ μ₁ e₁ c' μ' w) : ∃ m, BigN (ℍ := ℍ) A m c μ e c' μ' w := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  have hea := effFreeB_plug_inner K a he
  induction K generalizing n w c' μ' with
  | hole =>
      simp only [Kont.plug] at hb ⊢
      rcases head_shape hh.toHead hea with ⟨vf, va, rfl⟩ | ⟨e, rfl, rfl, rfl⟩ |
          ⟨v₁, v₂, e, rfl, rfl, rfl⟩ | ⟨v, e₁, e₂, rfl, rfl, rfl⟩ | ⟨v, e₁, e₂, rfl, rfl, rfl⟩
      · exact ⟨_, .app (.val _ _ va) (.val _ _ vf) hh hb⟩
      · cases hh with
        | det _ _ => exact ⟨_, .seq (.val _ _ Val.unit) hb⟩
      · cases hh with
        | det _ _ => exact ⟨_, .letpair (.val _ _ (Val.pair v₁ v₂)) hb⟩
      · cases hh with
        | det _ _ => exact ⟨_, .case₁ (.val _ _ (Val.inj₁ v)) hb⟩
      · cases hh with
        | det _ _ => exact ⟨_, .case₂ (.val _ _ (Val.inj₂ v)) hb⟩
  | pairL K e₂ ih =>
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at hb he ⊢
      obtain ⟨i, j, c₂, μ₂, u₁, u₂, -, -, h₁, h₂, rfl⟩ := big_pair_inv hb
      obtain ⟨m, hm⟩ := ih he.1 h₁
      exact ⟨_, .pair hm h₂⟩
  | pairR v K ih =>
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at hb he ⊢
      obtain ⟨i, j, c₂, μ₂, u₁, u₂, -, -, h₁, h₂, rfl⟩ := big_pair_inv hb
      obtain ⟨rfl, rfl, rfl⟩ := big_val_inv h₁ v rfl
      obtain ⟨m, hm⟩ := ih he.2 h₂
      exact ⟨_, .pair (.val _ _ _) hm⟩
  | letpair K e₂ ih =>
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at hb he ⊢
      obtain ⟨i, j, c₂, μ₂, v₁, v₂, -, -, h₁, h₂⟩ := big_letpair_inv hb
      obtain ⟨m, hm⟩ := ih he.1 h₁
      exact ⟨_, .letpair hm h₂⟩
  | case K e₁ e₂ ih =>
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at hb he ⊢
      rcases big_case_inv hb with ⟨i, j, c₂, μ₂, v, -, -, h₁, h₂⟩ | ⟨i, j, c₂, μ₂, v, -, -, h₁, h₂⟩
      · obtain ⟨m, hm⟩ := ih he.1.1 h₁; exact ⟨_, .case₁ hm h₂⟩
      · obtain ⟨m, hm⟩ := ih he.1.1 h₁; exact ⟨_, .case₂ hm h₂⟩
  | appR f K ih =>
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at hb he ⊢
      rcases big_app_inv hb with
          ⟨i, j, k, c₂, μ₂, c₃, μ₃, c₄, μ₄, va, vf, r, -, -, -, h₁, h₂, h₃, h₄⟩ |
          ⟨i, j, c₂, μ₂, va, -, -, h₁, h₂, rfl⟩
      · obtain ⟨m, hm⟩ := ih he.2 h₁
        exact ⟨_, .app hm h₂ h₃ h₄⟩
      · obtain ⟨m, hm⟩ := ih he.2 h₁
        exact ⟨_, .storeF hm h₂⟩
  | appL K v ih =>
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at hb he ⊢
      rcases big_app_inv hb with
          ⟨i, j, k, c₂, μ₂, c₃, μ₃, c₄, μ₄, va, vf, r, -, -, -, h₁, h₂, h₃, h₄⟩ |
          ⟨i, j, c₂, μ₂, va, -, -, h₁, h₂, rfl⟩
      · obtain ⟨rfl, rfl, rfl⟩ := big_val_inv h₁ v rfl
        obtain ⟨m, hm⟩ := ih he.1 h₂
        exact ⟨_, .app (.val _ _ _) hm h₃ h₄⟩
      · obtain ⟨rfl, rfl, rfl⟩ := big_val_inv h₁ v rfl
        obtain ⟨m, hm⟩ := ih he.1 h₂
        exact ⟨_, .storeF (.val _ _ _) hm⟩
  | seq K e₂ ih =>
      simp only [Kont.plug, effFreeB, Bool.and_eq_true] at hb he ⊢
      obtain ⟨i, j, c₂, μ₂, -, -, h₁, h₂⟩ := big_seq_inv hb
      obtain ⟨m, hm⟩ := ih he.1 h₁
      exact ⟨_, .seq hm h₂⟩
  | inj₁ K ih =>
      simp only [Kont.plug, effFreeB] at hb he ⊢
      obtain ⟨i, u, -, h₁, rfl⟩ := big_inj₁_inv hb
      obtain ⟨m, hm⟩ := ih he h₁
      exact ⟨_, .inj₁ hm⟩
  | inj₂ K ih =>
      simp only [Kont.plug, effFreeB] at hb he ⊢
      obtain ⟨i, u, -, h₁, rfl⟩ := big_inj₂_inv hb
      obtain ⟨m, hm⟩ := ih he h₁
      exact ⟨_, .inj₂ hm⟩

/-- **A run under the allocator to a value is a derivation**, for an effect-free term from a
memory of effect-free values. -/
theorem big_of_arun {A : Alloc} {c c' : Nat} {μ μ' : Heap} {e e' : Expr}
    (hs : ARun (ℍ := ℍ) A c μ e c' μ' e') :
    ∀ {w : Val}, e' = w.1 → effFreeB e = true → HeapEF μ →
      ∃ n, BigN (ℍ := ℍ) A n c μ e c' μ' w := by
  induction hs with
  | refl c μ e => intro w hw _ _; subst hw; exact ⟨0, .val c μ w⟩
  | more h _ ih =>
      intro w hw he hμ
      obtain ⟨he₁, hμ₁⟩ := effFree_step h he hμ
      obtain ⟨n, hn⟩ := ih hw he₁ hμ₁
      exact big_expand h he hn

end Lowering
