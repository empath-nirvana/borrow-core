import Lowering.LIRPrint
import Core.Steps

/-!
# Lowering — the source machine's runs, read big-step, on the core fragment  `[spec §56]`

The print's simulation (`Lowering/PrintFwd.lean`) follows a run of the source machine into the
interpreter's evaluation, which is big-step. `BigN k μ e μ' w`: `e` runs from `μ` to the value `w`
at `μ'`, the derivation of size `k`, in the machine's order (a pair left first, an application
its argument first, then its function, then the head step on the two values). A value is its own
run, of size `0`.

`big_of_steps`: on the core fragment (`coreB`, no location and no primitive but literals and host
operations), a run of the machine to a value is such a derivation. The proof reads each step
backwards (`big_expand`): a head step under a context is a derivation of the context around the
redex's. `coreB` is kept by every step (`coreB_step`), and its steps leave the memory as it is.
-/

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Lowering
open BoCa
open BoCa.BoLo (Heap Head Step1 Steps Kont)

/-- **A run to a value, big-step**, its derivation of size `k`. -/
inductive BigN : Nat → Heap → Expr → Heap → Val → Prop where
  | val (μ : Heap) (v : Val) : BigN 0 μ v.1 μ v
  | pair {i j : Nat} {μ μ₁ μ₂ : Heap} {a b : Expr} {u₁ u₂ : Val}
      (ha : BigN i μ a μ₁ u₁) (hb : BigN j μ₁ b μ₂ u₂) :
      BigN (i + j + 1) μ (.pair a b) μ₂ (Val.pair u₁ u₂)
  | inj₁ {i : Nat} {μ μ₁ : Heap} {a : Expr} {u : Val} (ha : BigN i μ a μ₁ u) :
      BigN (i + 1) μ (.inj₁ a) μ₁ (Val.inj₁ u)
  | inj₂ {i : Nat} {μ μ₁ : Heap} {a : Expr} {u : Val} (ha : BigN i μ a μ₁ u) :
      BigN (i + 1) μ (.inj₂ a) μ₁ (Val.inj₂ u)
  | seq {i j : Nat} {μ μ₁ μ₂ : Heap} {a b : Expr} {w : Val}
      (ha : BigN i μ a μ₁ Val.unit) (hb : BigN j μ₁ b μ₂ w) : BigN (i + j + 1) μ (.seq a b) μ₂ w
  | letpair {i j : Nat} {μ μ₁ μ₂ : Heap} {a b : Expr} {v₁ v₂ w : Val}
      (ha : BigN i μ a μ₁ (Val.pair v₁ v₂))
      (hb : BigN j μ₁ ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) μ₂ w) :
      BigN (i + j + 1) μ (.letpair a b) μ₂ w
  | case₁ {i j : Nat} {μ μ₁ μ₂ : Heap} {s a b : Expr} {v w : Val}
      (hs : BigN i μ s μ₁ (Val.inj₁ v)) (ha : BigN j μ₁ (a.subst 0 v) μ₂ w) :
      BigN (i + j + 1) μ (.case s a b) μ₂ w
  | case₂ {i j : Nat} {μ μ₁ μ₂ : Heap} {s a b : Expr} {v w : Val}
      (hs : BigN i μ s μ₁ (Val.inj₂ v)) (hb : BigN j μ₁ (b.subst 0 v) μ₂ w) :
      BigN (i + j + 1) μ (.case s a b) μ₂ w
  | app {i j k : Nat} {μ μ₁ μ₂ μ₃ μ' : Heap} {f a r : Expr} {va vf w : Val}
      (ha : BigN i μ a μ₁ va) (hf : BigN j μ₁ f μ₂ vf)
      (hh : Head (ℍ := ℍ) μ₂ (.app vf.1 va.1) μ₃ r) (hr : BigN k μ₃ r μ' w) :
      BigN (i + j + k + 1) μ (.app f a) μ' w

/-! ### The core fragment is kept by the machine -/

theorem coreB_shift : ∀ (e : Expr) (d c : Nat), coreB (e.shift d c) = coreB e
  | .var i, d, c => by simp only [Expr.shift]; split <;> rfl
  | .unit, _, _ | .loc _, _, _ | .prim _, _, _ => rfl
  | .pair a b, d, c | .seq a b, d, c | .app a b, d, c => by
      simp only [Expr.shift, coreB, coreB_shift a, coreB_shift b]
  | .letpair a b, d, c => by simp only [Expr.shift, coreB, coreB_shift a, coreB_shift b]
  | .inj₁ a, d, c | .inj₂ a, d, c => by simp only [Expr.shift, coreB, coreB_shift a]
  | .lam a, d, c => by simp only [Expr.shift, coreB, coreB_shift a]
  | .case s a b, d, c => by simp only [Expr.shift, coreB, coreB_shift s, coreB_shift a, coreB_shift b]

theorem coreB_subst : ∀ (e : Expr) (j : Nat) (v : Val), coreB e = true → coreB v.1 = true →
    coreB (e.subst j v) = true
  | .var i, j, v, _, hv => by
      simp only [Expr.subst]; split
      · exact hv
      · split <;> rfl
  | .unit, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ => h
  | .pair a b, j, v, h, hv | .seq a b, j, v, h, hv | .app a b, j, v, h, hv => by
      simp only [coreB, Bool.and_eq_true] at h
      simp only [Expr.subst, coreB, coreB_subst a j v h.1 hv, coreB_subst b j v h.2 hv]; rfl
  | .letpair a b, j, v, h, hv => by
      simp only [coreB, Bool.and_eq_true] at h
      have hv' : coreB (v.shift 2 0).1 = true := by simpa [Val.shift, coreB_shift] using hv
      simp only [Expr.subst, coreB, coreB_subst a j v h.1 hv, coreB_subst b _ _ h.2 hv']; rfl
  | .inj₁ a, j, v, h, hv | .inj₂ a, j, v, h, hv => by
      simp only [coreB] at h
      simp only [Expr.subst, coreB, coreB_subst a j v h hv]
  | .lam a, j, v, h, hv => by
      simp only [coreB] at h
      have hv' : coreB (v.shift 1 0).1 = true := by simpa [Val.shift, coreB_shift] using hv
      simp only [Expr.subst, coreB, coreB_subst a _ _ h hv']
  | .case s a b, j, v, h, hv => by
      simp only [coreB, Bool.and_eq_true] at h
      have hv' : coreB (v.shift 1 0).1 = true := by simpa [Val.shift, coreB_shift] using hv
      simp only [Expr.subst, coreB, coreB_subst s j v h.1.1 hv, coreB_subst a _ _ h.1.2 hv',
        coreB_subst b _ _ h.2 hv']; rfl

omit [HostIs ℍ] in
/-- A host operation answers a core value. -/
theorem coreB_call {op : HostOp} {v r : Val} (h : ℍ.call op v = some r) : coreB r.1 = true := by
  have hb : ∀ b, coreB (Val.bool b).1 = true := by intro b; cases b <;> rfl
  have hw : ∀ (w : Width) (n : w.bits), coreB (Val.ofBits w n).1 = true := by
    intro w; cases w <;> intro n <;> rfl
  have ho : ∀ (o : Option Val), (∀ x, o = some x → coreB x.1 = true) → coreB (Val.opt o).1 = true := by
    intro o ho; cases o with
    | none => rfl
    | some x => simpa [Val.opt, coreB, Val.inj₁] using ho x rfl
  unfold Host.call at h
  split at h <;> simp only [Option.map_eq_some_iff, reduceCtorEq] at h <;>
    obtain ⟨_, _, rfl⟩ := h <;>
    first
    | rfl
    | exact hb _
    | exact hw _ _
    | (apply ho; intro x hx; simp only [Option.map_eq_some_iff] at hx
       obtain ⟨_, _, rfl⟩ := hx; first | rfl | exact hw _ _)

theorem coreB_plug_inner : ∀ (K : Kont) (x : Expr), coreB (K.plug x) = true → coreB x = true
  | .hole, _, h => h
  | .pairL K _, x, h | .letpair K _, x, h | .seq K _, x, h => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h; exact coreB_plug_inner K x h.1
  | .pairR _ K, x, h | .appR _ K, x, h => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h; exact coreB_plug_inner K x h.2
  | .appL K _, x, h => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h; exact coreB_plug_inner K x h.1
  | .case K _ _, x, h => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h; exact coreB_plug_inner K x h.1.1
  | .inj₁ K, x, h | .inj₂ K, x, h => by
      simp only [Kont.plug, coreB] at h; exact coreB_plug_inner K x h

theorem coreB_plug_swap : ∀ (K : Kont) (x y : Expr), coreB (K.plug x) = true → coreB y = true →
    coreB (K.plug y) = true
  | .hole, _, _, _, hy => hy
  | .pairL K _, x, y, h, hy | .letpair K _, x, y, h, hy | .seq K _, x, y, h, hy => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h ⊢
      exact ⟨coreB_plug_swap K x y h.1 hy, h.2⟩
  | .pairR _ K, x, y, h, hy | .appR _ K, x, y, h, hy => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, coreB_plug_swap K x y h.2 hy⟩
  | .appL K _, x, y, h, hy => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h ⊢
      exact ⟨coreB_plug_swap K x y h.1 hy, h.2⟩
  | .case K _ _, x, y, h, hy => by
      simp only [Kont.plug, coreB, Bool.and_eq_true] at h ⊢
      exact ⟨⟨coreB_plug_swap K x y h.1.1 hy, h.1.2⟩, h.2⟩
  | .inj₁ K, x, y, h, hy | .inj₂ K, x, y, h, hy => by
      simp only [Kont.plug, coreB] at h ⊢; exact coreB_plug_swap K x y h hy

/-- **A head step of a core redex** leaves the memory, and its reduct is core. -/
theorem coreB_head {μ μ₁ : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ₁ a') (hc : coreB a = true) :
    μ₁ = μ ∧ coreB a' = true := by
  cases h with
  | beta b v =>
      simp only [coreB, Expr.val, Val.lam, Bool.and_eq_true] at hc
      exact ⟨rfl, coreB_subst b 0 v hc.1 hc.2⟩
  | seq e => simp only [coreB, Bool.and_eq_true] at hc; exact ⟨rfl, hc.2⟩
  | letpair v₁ v₂ e =>
      simp only [coreB, Bool.and_eq_true, Expr.val, Val.pair] at hc
      have h₂ : coreB (v₂.shift 1 0).1 = true := by simpa [Val.shift, coreB_shift] using hc.1.2
      exact ⟨rfl, coreB_subst _ 0 v₁ (coreB_subst e 0 _ hc.2 h₂) hc.1.1⟩
  | case₁ v e₁ e₂ =>
      simp only [coreB, Bool.and_eq_true, Expr.val, Val.inj₁] at hc
      exact ⟨rfl, coreB_subst e₁ 0 v hc.1.2 hc.1.1⟩
  | case₂ v e₁ e₂ =>
      simp only [coreB, Bool.and_eq_true, Expr.val, Val.inj₂] at hc
      exact ⟨rfl, coreB_subst e₂ 0 v hc.2 hc.1.1⟩
  | host op v r hr => exact ⟨rfl, coreB_call hr⟩
  | _ => simp [coreB, BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim] at hc

/-- **A step of a core term** leaves the memory, and its result is core. -/
theorem coreB_step {μ μ₁ : Heap} {e e₁ : Expr} (h : Step1 (ℍ := ℍ) μ e μ₁ e₁)
    (hc : coreB e = true) : μ₁ = μ ∧ coreB e₁ = true := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  obtain ⟨rfl, ha'⟩ := coreB_head hh (coreB_plug_inner K a hc)
  exact ⟨rfl, coreB_plug_swap K a a' hc ha'⟩

/-! ### Inversions -/

theorem not_head_store {μ μ₁ : Heap} {a r : Expr} (hh : Head (ℍ := ℍ) μ (.app (.prim .store) a) μ₁ r) :
    False := by
  cases hh

/-- **A value is its own run.** -/
theorem big_val_inv : ∀ {n : Nat} {μ μ' : Heap} {e : Expr} {w : Val}, BigN (ℍ := ℍ) n μ e μ' w →
    ∀ (v : Val), e = v.1 → μ' = μ ∧ w = v := by
  intro n μ μ' e w h
  induction h with
  | val μ u => intro v hv; exact ⟨rfl, Subtype.ext hv⟩
  | pair ha hb iha ihb =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      cases hv' with
      | pair h₁ h₂ =>
        obtain ⟨rfl, rfl⟩ := iha ⟨_, h₁⟩ rfl
        obtain ⟨rfl, rfl⟩ := ihb ⟨_, h₂⟩ rfl
        exact ⟨rfl, Subtype.ext hv⟩
  | inj₁ ha iha =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      cases hv' with
      | inj₁ h₁ =>
        obtain ⟨rfl, rfl⟩ := iha ⟨_, h₁⟩ rfl
        exact ⟨rfl, Subtype.ext hv⟩
  | inj₂ ha iha =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      cases hv' with
      | inj₂ h₁ =>
        obtain ⟨rfl, rfl⟩ := iha ⟨_, h₁⟩ rfl
        exact ⟨rfl, Subtype.ext hv⟩
  | seq => intro v hv; have := hv ▸ v.2; simp at this
  | letpair => intro v hv; have := hv ▸ v.2; simp at this
  | case₁ => intro v hv; have := hv ▸ v.2; simp at this
  | case₂ => intro v hv; have := hv ▸ v.2; simp at this
  | app ha hf hh hr iha ihf ihr =>
      intro v hv
      have hv' : IsVal _ := hv ▸ v.2
      obtain ⟨rfl, h₂⟩ := isVal_app_iff.mp hv'
      obtain ⟨rfl, rfl⟩ := iha ⟨_, h₂⟩ rfl
      obtain ⟨rfl, rfl⟩ := ihf (Val.prim .store) rfl
      exact (not_head_store hh).elim

theorem big_pair_inv {n : Nat} {μ μ' : Heap} {a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) n μ (.pair a b) μ' w) :
    ∃ i j μ₁ u₁ u₂, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) i μ a μ₁ u₁ ∧ BigN (ℍ := ℍ) j μ₁ b μ' u₂ ∧
      w = Val.pair u₁ u₂ := by
  generalize he : Expr.pair a b = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.pair a b) := he ▸ w.2
      cases hv with
      | pair h₁ h₂ => exact ⟨0, 0, _, ⟨a, h₁⟩, ⟨b, h₂⟩, le_refl _, le_refl _, .val _ ⟨a, h₁⟩,
          .val _ ⟨b, h₂⟩, Subtype.ext he.symm⟩
  | pair ha hb =>
      simp only [Expr.pair.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, _, _, _, by omega, by omega, ha, hb, rfl⟩
  | _ => simp at he

theorem big_inj₁_inv {n : Nat} {μ μ' : Heap} {a : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) n μ (.inj₁ a) μ' w) :
    ∃ i u, i ≤ n ∧ BigN (ℍ := ℍ) i μ a μ' u ∧ w = Val.inj₁ u := by
  generalize he : Expr.inj₁ a = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.inj₁ a) := he ▸ w.2
      cases hv with
      | inj₁ h₁ => exact ⟨0, ⟨a, h₁⟩, le_refl _, .val _ ⟨a, h₁⟩, Subtype.ext he.symm⟩
  | inj₁ ha => simp only [Expr.inj₁.injEq] at he; subst he; exact ⟨_, _, by omega, ha, rfl⟩
  | _ => simp at he

theorem big_inj₂_inv {n : Nat} {μ μ' : Heap} {a : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) n μ (.inj₂ a) μ' w) :
    ∃ i u, i ≤ n ∧ BigN (ℍ := ℍ) i μ a μ' u ∧ w = Val.inj₂ u := by
  generalize he : Expr.inj₂ a = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.inj₂ a) := he ▸ w.2
      cases hv with
      | inj₂ h₁ => exact ⟨0, ⟨a, h₁⟩, le_refl _, .val _ ⟨a, h₁⟩, Subtype.ext he.symm⟩
  | inj₂ ha => simp only [Expr.inj₂.injEq] at he; subst he; exact ⟨_, _, by omega, ha, rfl⟩
  | _ => simp at he

theorem big_seq_inv {n : Nat} {μ μ' : Heap} {a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) n μ (.seq a b) μ' w) :
    ∃ i j μ₁, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) i μ a μ₁ Val.unit ∧ BigN (ℍ := ℍ) j μ₁ b μ' w := by
  generalize he : Expr.seq a b = E at h
  cases h with
  | val => have := he ▸ w.2; simp at this
  | seq ha hb =>
      simp only [Expr.seq.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, _, by omega, by omega, ha, hb⟩
  | _ => simp at he

theorem big_letpair_inv {n : Nat} {μ μ' : Heap} {a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) n μ (.letpair a b) μ' w) :
    ∃ i j μ₁ v₁ v₂, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) i μ a μ₁ (Val.pair v₁ v₂) ∧
      BigN (ℍ := ℍ) j μ₁ ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) μ' w := by
  generalize he : Expr.letpair a b = E at h
  cases h with
  | val => have := he ▸ w.2; simp at this
  | letpair ha hb =>
      simp only [Expr.letpair.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, _, _, _, by omega, by omega, ha, hb⟩
  | _ => simp at he

theorem big_case_inv {n : Nat} {μ μ' : Heap} {s a b : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) n μ (.case s a b) μ' w) :
    (∃ i j μ₁ v, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) i μ s μ₁ (Val.inj₁ v) ∧
      BigN (ℍ := ℍ) j μ₁ (a.subst 0 v) μ' w) ∨
    (∃ i j μ₁ v, i ≤ n ∧ j ≤ n ∧ BigN (ℍ := ℍ) i μ s μ₁ (Val.inj₂ v) ∧
      BigN (ℍ := ℍ) j μ₁ (b.subst 0 v) μ' w) := by
  generalize he : Expr.case s a b = E at h
  cases h with
  | val => have := he ▸ w.2; simp at this
  | case₁ hs ha =>
      simp only [Expr.case.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact .inl ⟨_, _, _, _, by omega, by omega, hs, ha⟩
  | case₂ hs hb =>
      simp only [Expr.case.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      exact .inr ⟨_, _, _, _, by omega, by omega, hs, hb⟩
  | _ => simp at he

theorem big_app_inv {n : Nat} {μ μ' : Heap} {f a : Expr} {w : Val}
    (h : BigN (ℍ := ℍ) n μ (.app f a) μ' w) (hf : f ≠ .prim .store) :
    ∃ i j k μ₁ μ₂ μ₃ va vf r, i ≤ n ∧ j ≤ n ∧ k < n ∧ BigN (ℍ := ℍ) i μ a μ₁ va ∧
      BigN (ℍ := ℍ) j μ₁ f μ₂ vf ∧ Head (ℍ := ℍ) μ₂ (.app vf.1 va.1) μ₃ r ∧
      BigN (ℍ := ℍ) k μ₃ r μ' w := by
  generalize he : Expr.app f a = E at h
  cases h with
  | val =>
      have hv : IsVal (Expr.app f a) := he ▸ w.2
      exact absurd (isVal_app_iff.mp hv).1 hf
  | app ha hf' hh hr =>
      simp only [Expr.app.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact ⟨_, _, _, _, _, _, _, _, _, by omega, by omega, by omega, ha, hf', hh, hr⟩
  | _ => simp at he

/-! ### Runs to a value are derivations -/

/-- **A step read backwards**: a head step under a context, followed by a run to a value, is a
derivation of the whole. -/
theorem big_expand {μ μ₁ μ' : Heap} {e e₁ : Expr} {w : Val} {n : Nat}
    (h : Step1 (ℍ := ℍ) μ e μ₁ e₁) (hc : coreB e = true) (hb : BigN (ℍ := ℍ) n μ₁ e₁ μ' w) :
    ∃ m, BigN (ℍ := ℍ) m μ e μ' w := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  have hca := coreB_plug_inner K a hc
  have hc₁ := coreB_plug_swap K a a' hc (coreB_head hh hca).2
  induction K generalizing n w μ' with
  | hole =>
      simp only [Kont.plug] at hb ⊢
      cases hh with
      | beta b v => exact ⟨_, .app (.val _ v) (.val _ (Val.lam b)) (.beta _ b v) hb⟩
      | seq e => exact ⟨_, .seq (.val _ Val.unit) hb⟩
      | letpair v₁ v₂ e => exact ⟨_, .letpair (.val _ (Val.pair v₁ v₂)) hb⟩
      | case₁ v e₁ e₂ => exact ⟨_, .case₁ (.val _ (Val.inj₁ v)) hb⟩
      | case₂ v e₁ e₂ => exact ⟨_, .case₂ (.val _ (Val.inj₂ v)) hb⟩
      | host op v r hr =>
          exact ⟨_, .app (.val _ v) (.val _ (Val.prim (.host op))) (.host _ op v r hr) hb⟩
      | _ => simp [coreB, BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val,
          Val.prim] at hca
  | pairL K e₂ ih =>
      simp only [Kont.plug, coreB, Bool.and_eq_true] at hb hc hc₁ ⊢
      obtain ⟨i, j, μ₂, u₁, u₂, -, -, h₁, h₂, rfl⟩ := big_pair_inv hb
      obtain ⟨m, hm⟩ := ih hc.1 h₁ hc₁.1
      exact ⟨_, .pair hm h₂⟩
  | pairR v K ih =>
      simp only [Kont.plug, coreB, Bool.and_eq_true] at hb hc hc₁ ⊢
      obtain ⟨i, j, μ₂, u₁, u₂, -, -, h₁, h₂, rfl⟩ := big_pair_inv hb
      obtain ⟨rfl, rfl⟩ := big_val_inv h₁ v rfl
      obtain ⟨m, hm⟩ := ih hc.2 h₂ hc₁.2
      exact ⟨_, .pair (.val _ _) hm⟩
  | letpair K e₂ ih =>
      simp only [Kont.plug, coreB, Bool.and_eq_true] at hb hc hc₁ ⊢
      obtain ⟨i, j, μ₂, v₁, v₂, -, -, h₁, h₂⟩ := big_letpair_inv hb
      obtain ⟨m, hm⟩ := ih hc.1 h₁ hc₁.1
      exact ⟨_, .letpair hm h₂⟩
  | case K e₁ e₂ ih =>
      simp only [Kont.plug, coreB, Bool.and_eq_true] at hb hc hc₁ ⊢
      rcases big_case_inv hb with ⟨i, j, μ₂, v, -, -, h₁, h₂⟩ | ⟨i, j, μ₂, v, -, -, h₁, h₂⟩
      · obtain ⟨m, hm⟩ := ih hc.1.1 h₁ hc₁.1.1; exact ⟨_, .case₁ hm h₂⟩
      · obtain ⟨m, hm⟩ := ih hc.1.1 h₁ hc₁.1.1; exact ⟨_, .case₂ hm h₂⟩
  | appR f K ih =>
      simp only [Kont.plug, coreB, Bool.and_eq_true] at hb hc hc₁ ⊢
      have hfs : f ≠ .prim .store := fun h => by subst h; simp [coreB] at hc
      obtain ⟨i, j, k, μa, μf, μr, va, vf, r, -, -, -, h₁, h₂, h₃, h₄⟩ := big_app_inv hb hfs
      obtain ⟨m, hm⟩ := ih hc.2 h₁ hc₁.2
      exact ⟨_, .app hm h₂ h₃ h₄⟩
  | appL K v ih =>
      simp only [Kont.plug, coreB, Bool.and_eq_true] at hb hc hc₁ ⊢
      have hfs : K.plug a' ≠ .prim .store := fun h => by rw [h] at hc₁; simp [coreB] at hc₁
      obtain ⟨i, j, k, μa, μf, μr, va, vf, r, -, -, -, h₁, h₂, h₃, h₄⟩ := big_app_inv hb hfs
      obtain ⟨rfl, rfl⟩ := big_val_inv h₁ v rfl
      obtain ⟨m, hm⟩ := ih hc.1 h₂ hc₁.1
      exact ⟨_, .app (.val _ _) hm h₃ h₄⟩
  | seq K e₂ ih =>
      simp only [Kont.plug, coreB, Bool.and_eq_true] at hb hc hc₁ ⊢
      obtain ⟨i, j, μ₂, -, -, h₁, h₂⟩ := big_seq_inv hb
      obtain ⟨m, hm⟩ := ih hc.1 h₁ hc₁.1
      exact ⟨_, .seq hm h₂⟩
  | inj₁ K ih =>
      simp only [Kont.plug, coreB] at hb hc hc₁ ⊢
      obtain ⟨i, u, -, h₁, rfl⟩ := big_inj₁_inv hb
      obtain ⟨m, hm⟩ := ih hc h₁ hc₁
      exact ⟨_, .inj₁ hm⟩
  | inj₂ K ih =>
      simp only [Kont.plug, coreB] at hb hc hc₁ ⊢
      obtain ⟨i, u, -, h₁, rfl⟩ := big_inj₂_inv hb
      obtain ⟨m, hm⟩ := ih hc h₁ hc₁
      exact ⟨_, .inj₂ hm⟩

/-- **A run to a value is a derivation**, on the core fragment. -/
theorem big_of_steps {μ μ' : Heap} {e e' : Expr} (hs : Steps (ℍ := ℍ) μ e μ' e') :
    ∀ {w : Val}, e' = w.1 → coreB e = true → ∃ n, BigN (ℍ := ℍ) n μ e μ' w := by
  induction hs with
  | refl μ e => intro w hw _; subst hw; exact ⟨0, .val μ w⟩
  | more h _ ih =>
      intro w hw hc
      obtain ⟨n, hn⟩ := ih hw (coreB_step h hc).2
      exact big_expand h hc hn

end Lowering
