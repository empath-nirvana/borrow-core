import Core.Fundamental
import Core.Dtor
import Core.LetCopy

/-!
# Frontend — Check — deciders for the side conditions

Every side condition of `CDerives` that the checker discharges (syntax-core §11, §12) is
decided by a `Bool` function proved sound: `f … = true → P …`. Each is also complete for the
cases the comments name; where it is not, the gap is stated at the function.

* `DecidableEq` on `VTy` and `CTy` (§12 item 4), derived; on `Expr`, `Core/LetCopy.lean`'s.
* `VTy.clB`, `VTy.occB`, `VTy.noMutB`: `Cl`, `Occ`, `NoMut`, exactly.
* `CTy.nuOkB`: `νX. C`'s positivity `NuOk`, exactly.
* `vfreeB`/`cfreeB`: `VFree`/`CFree`, exactly.
* `ordB`: lifetime entailment `Δ ⊨ @a ⊏ @b` / `Δ ⊨ @a ⊑ @b` (§12 item 1), sound, by a bounded
  search over the structural rules of the carrier (`⊓` is `max`, `⊔` is `min`, `⊤` is `0`).
* `outlivesB`: `VOutlives`, sound (complete relative to `ordB`); `ansOutlivesB`, BOXED-κ's
  `Row.AnsOutlives`, from it.
* `outlivesAllB`: foldImm's `∀ Δ' a, VOutlives Δ' a R` (§12 item 2), sound.
* `scopedB`: `VScoped`, sound.
-/

namespace BoCa.Fig16.LogRel.Core

deriving instance DecidableEq for VTy, CTy

deriving instance DecidableEq for OpSig

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Lifetime

/-! ### Type variables: `Cl`, `Occ`, `NoMut` -/

/-- `Cl k A`, decided. -/
def VTy.clB : Nat → VTy → Bool
  | _, .unit => true
  | k, .tensor A B => VTy.clB k A && VTy.clB k B
  | _, .zero => true
  | k, .sum A B => VTy.clB k A && VTy.clB k B
  | _, .thunk _ => true
  | k, .ref A => VTy.clB k A
  | k, .imm _ A => VTy.clB k A
  | k, .mut _ A => VTy.clB k A
  | k, .box _ A => VTy.clB k A
  | k, .bang A => VTy.clB k A
  | k, .fam A => VTy.clB k A
  | _, .unk => true
  | _, .int _ => true
  | _, .opq _ => true
  | k, .tvar n => decide (n < k)
  | k, .mu A => VTy.clB (k + 1) A

theorem VTy.clB_sound : ∀ (k : Nat) (A : VTy), VTy.clB k A = true → A.Cl k
  | _, .unit, _ => trivial
  | k, .tensor A B, h => by
      simp only [VTy.clB, Bool.and_eq_true] at h
      exact ⟨clB_sound k A h.1, clB_sound k B h.2⟩
  | _, .zero, _ => trivial
  | k, .sum A B, h => by
      simp only [VTy.clB, Bool.and_eq_true] at h
      exact ⟨clB_sound k A h.1, clB_sound k B h.2⟩
  | _, .thunk _, _ => trivial
  | k, .ref A, h => clB_sound k A h
  | k, .imm _ A, h => clB_sound k A h
  | k, .mut _ A, h => clB_sound k A h
  | k, .box _ A, h => clB_sound k A h
  | k, .bang A, h => clB_sound k A h
  | k, .fam A, h => clB_sound k A h
  | _, .unk, _ => trivial
  | _, .int _, _ => trivial
  | _, .opq _, _ => trivial
  | k, .tvar n, h => by simpa [VTy.clB, VTy.Cl] using h
  | k, .mu A, h => clB_sound (k + 1) A h

/-- `Occ k A`, decided. -/
def VTy.occB : Nat → VTy → Bool
  | _, .unit => false
  | k, .tensor A B => VTy.occB k A || VTy.occB k B
  | _, .zero => false
  | k, .sum A B => VTy.occB k A || VTy.occB k B
  | _, .thunk _ => false
  | k, .ref A => VTy.occB k A
  | k, .imm _ A => VTy.occB k A
  | k, .mut _ A => VTy.occB k A
  | k, .box _ A => VTy.occB k A
  | k, .bang A => VTy.occB k A
  | k, .fam A => VTy.occB k A
  | _, .unk => false
  | _, .int _ => false
  | _, .opq _ => false
  | k, .tvar n => n == k
  | k, .mu A => VTy.occB (k + 1) A

theorem VTy.not_occ_of_occB : ∀ (k : Nat) (A : VTy), VTy.occB k A = false → ¬ A.Occ k
  | _, .unit, _, h => h
  | k, .tensor A B, hb, h => by
      simp only [VTy.occB, Bool.or_eq_false_iff] at hb
      exact h.elim (not_occ_of_occB k A hb.1) (not_occ_of_occB k B hb.2)
  | _, .zero, _, h => h
  | k, .sum A B, hb, h => by
      simp only [VTy.occB, Bool.or_eq_false_iff] at hb
      exact h.elim (not_occ_of_occB k A hb.1) (not_occ_of_occB k B hb.2)
  | _, .thunk _, _, h => h
  | k, .ref A, hb, h => not_occ_of_occB k A hb h
  | k, .imm _ A, hb, h => not_occ_of_occB k A hb h
  | k, .mut _ A, hb, h => not_occ_of_occB k A hb h
  | k, .box _ A, hb, h => not_occ_of_occB k A hb h
  | k, .bang A, hb, h => not_occ_of_occB k A hb h
  | k, .fam A, hb, h => not_occ_of_occB k A hb h
  | _, .unk, _, h => h
  | _, .int _, _, h => h
  | _, .opq _, _, h => h
  | k, .tvar n, hb, h => by
      simp only [VTy.occB, beq_eq_false_iff_ne] at hb
      exact hb h
  | k, .mu A, hb, h => not_occ_of_occB (k + 1) A hb h

/-- `NoMut k A`, decided. -/
def VTy.noMutB : Nat → VTy → Bool
  | _, .unit => true
  | k, .tensor A B => VTy.noMutB k A && VTy.noMutB k B
  | _, .zero => true
  | k, .sum A B => VTy.noMutB k A && VTy.noMutB k B
  | _, .thunk _ => true
  | k, .ref A => VTy.noMutB k A
  | k, .imm _ A => VTy.noMutB k A
  | k, .mut _ A => !VTy.occB k A
  | k, .box _ A => VTy.noMutB k A
  | k, .bang A => VTy.noMutB k A
  | k, .fam A => VTy.noMutB k A
  | _, .unk => true
  | _, .int _ => true
  | _, .opq _ => true
  | _, .tvar _ => true
  | k, .mu A => VTy.noMutB (k + 1) A

theorem VTy.noMutB_sound : ∀ (k : Nat) (A : VTy), VTy.noMutB k A = true → A.NoMut k
  | _, .unit, _ => trivial
  | k, .tensor A B, h => by
      simp only [VTy.noMutB, Bool.and_eq_true] at h
      exact ⟨noMutB_sound k A h.1, noMutB_sound k B h.2⟩
  | _, .zero, _ => trivial
  | k, .sum A B, h => by
      simp only [VTy.noMutB, Bool.and_eq_true] at h
      exact ⟨noMutB_sound k A h.1, noMutB_sound k B h.2⟩
  | _, .thunk _, _ => trivial
  | k, .ref A, h => noMutB_sound k A h
  | k, .imm _ A, h => noMutB_sound k A h
  | k, .mut _ A, h => by
      simp only [VTy.noMutB, Bool.not_eq_true'] at h
      exact VTy.not_occ_of_occB k A h
  | k, .box _ A, h => noMutB_sound k A h
  | k, .bang A, h => noMutB_sound k A h
  | k, .fam A, h => noMutB_sound k A h
  | _, .unk, _ => trivial
  | _, .int _, _ => trivial
  | _, .opq _, _ => trivial
  | _, .tvar _, _ => trivial
  | k, .mu A, h => noMutB_sound (k + 1) A h

/-! ### `νX. C`: positivity and polynomial observations -/

/-- `VTy.Poly`, decided.  `[spec §7, §22]` -/
def VTy.polyB : VTy → Bool
  | .tensor A B => VTy.polyB A && VTy.polyB B
  | .sum A B => VTy.polyB A && VTy.polyB B
  | .box _ A => VTy.polyB A
  | .tvar _ => true
  | A => !VTy.occB 0 A

theorem VTy.polyB_sound : ∀ A : VTy, VTy.polyB A = true → A.Poly
  | .tensor A B, h => by
      simp only [VTy.polyB, Bool.and_eq_true] at h
      exact ⟨polyB_sound A h.1, polyB_sound B h.2⟩
  | .sum A B, h => by
      simp only [VTy.polyB, Bool.and_eq_true] at h
      exact ⟨polyB_sound A h.1, polyB_sound B h.2⟩
  | .tvar _, _ => trivial
  | .box _ A, h => polyB_sound A (by simpa [VTy.polyB] using h)
  | .unit, h | .zero, h | .thunk _, h | .unk, h | .int _, h | .opq _, h | .ref _, h | .imm _ _, h
  | .mut _ _, h | .bang _, h | .mu _, h | .fam _, h =>
      VTy.not_occ_of_occB 0 _ (by simpa [VTy.polyB] using h)

/-- `CTy.EffLeaf`, decided: `F_Σ A`, the operation types closed.  `[spec §19]` -/
def CTy.effLeafB : CTy → Bool
  | .ret A => VTy.polyB A
  | .eff _ _ _ _ A B fin C => VTy.clB 0 A && VTy.clB 0 B && CTy.effLeafB C
  | _ => false

theorem CTy.effLeafB_sound : ∀ C : CTy, CTy.effLeafB C = true → C.EffLeaf
  | .ret A, h => VTy.polyB_sound A h
  | .eff _ _ _ _ A B fin C, h => by
      simp only [CTy.effLeafB, Bool.and_eq_true] at h
      exact ⟨VTy.clB_sound 0 A h.1.1, VTy.clB_sound 0 B h.1.2, effLeafB_sound C h.2⟩
  | .arr _ _, h | .amp _ _, h | .top, h | .all _ _ _, h | .nu _, h => by simp [CTy.effLeafB] at h

/-- `CTy.NuLeaf`, decided.  `[spec §7, §22]` -/
def CTy.nuLeafB : CTy → Bool
  | .ret A => VTy.polyB A
  | .amp C D => CTy.nuLeafB C && CTy.nuLeafB D
  | .eff n i q wq A B fin C => CTy.effLeafB (.eff n i q wq A B fin C)
  | .arr A D => VTy.clB 0 A && CTy.nuLeafB D
  | _ => false

theorem CTy.nuLeafB_sound : ∀ C : CTy, CTy.nuLeafB C = true → C.NuLeaf
  | .ret A, h => VTy.polyB_sound A h
  | .amp C D, h => by
      simp only [CTy.nuLeafB, Bool.and_eq_true] at h
      exact ⟨nuLeafB_sound C h.1, nuLeafB_sound D h.2⟩
  | .eff n i q wq A B fin C, h => CTy.effLeafB_sound (.eff n i q wq A B fin C) h
  | .arr A D, h => by
      simp only [CTy.nuLeafB, Bool.and_eq_true] at h
      exact ⟨VTy.clB_sound 0 A h.1, nuLeafB_sound D h.2⟩
  | .top, h | .all _ _ _, h | .nu _, h => by simp [CTy.nuLeafB] at h

/-- `CTy.NuOk`, decided. -/
def CTy.nuOkB : CTy → Bool
  | .amp C D => CTy.nuLeafB C && CTy.nuLeafB D
  | _ => false

theorem CTy.nuOkB_sound : ∀ C : CTy, CTy.nuOkB C = true → C.NuOk
  | .amp C D, h => by
      simp only [CTy.nuOkB, Bool.and_eq_true] at h
      exact ⟨CTy.nuLeafB_sound C h.1, CTy.nuLeafB_sound D h.2⟩
  | .ret _, h | .arr _ _, h | .top, h | .all _ _ _, h | .nu _, h | .eff _ _ _ _ _ _ _ _, h => by
      simp [CTy.nuOkB] at h

/-- The bodies `C` of the thunks `U(νX. C)` in a value type: where `nu_in` looks for the type
whose unrolling its body has. -/
def VTy.nuThunks : VTy → List CTy
  | .thunk (.nu C) => [C]
  | .tensor A B | .sum A B => VTy.nuThunks A ++ VTy.nuThunks B
  | .ref A | .box _ A | .imm _ A | .bang A => VTy.nuThunks A
  | _ => []

/-- `VTy.nuThunks` over the observations of a `&`-tree. -/
def CTy.nuThunks : CTy → List CTy
  | .ret A => VTy.nuThunks A
  | .amp C D => CTy.nuThunks C ++ CTy.nuThunks D
  | .eff _ _ _ _ _ _ _ C => CTy.nuThunks C
  | .arr _ D => CTy.nuThunks D
  | _ => []

/-! ### Free lifetime variables -/

mutual
/-- `VFree x A`, decided. -/
def vfreeB (x : LifeVar) : VTy → Bool
  | .unit => false
  | .zero => false
  | .unk => false
  | .int _ => false
  | .opq _ => false
  | .tensor A B => vfreeB x A || vfreeB x B
  | .sum A B => vfreeB x A || vfreeB x B
  | .thunk C => cfreeB x C
  | .ref A => vfreeB x A
  | .bang A => vfreeB x A
  | .fam A => vfreeB x A
  | .imm a A => a.mentions x || vfreeB x A
  | .mut a A => a.mentions x || vfreeB x A
  | .box a A => a.mentions x || vfreeB x A
  | .tvar _ => false
  | .mu A => vfreeB x A
/-- `CFree x C`, decided. -/
def cfreeB (x : LifeVar) : CTy → Bool
  | .ret A => vfreeB x A
  | .arr A C => vfreeB x A || cfreeB x C
  | .amp C D => cfreeB x C || cfreeB x D
  | .top => false
  | .all y b C => b.mentions x || (x != y && cfreeB x C)
  | .nu C => cfreeB x C
  | .eff _ _ _ _ A B fin C => vfreeB x A || vfreeB x B || cfreeB x fin || cfreeB x C
end

mutual
theorem vfreeB_iff (x : LifeVar) : ∀ A : VTy, vfreeB x A = true ↔ VFree x A
  | .unit => by simp [vfreeB, VFree]
  | .zero => by simp [vfreeB, VFree]
  | .unk => by simp [vfreeB, VFree]
  | .int _ => by simp [vfreeB, VFree]
  | .opq _ => by simp [vfreeB, VFree]
  | .tensor A B => by simp [vfreeB, VFree, vfreeB_iff x A, vfreeB_iff x B]
  | .sum A B => by simp [vfreeB, VFree, vfreeB_iff x A, vfreeB_iff x B]
  | .thunk C => by simp [vfreeB, VFree, cfreeB_iff x C]
  | .ref A => by simp [vfreeB, VFree, vfreeB_iff x A]
  | .bang A => by simp [vfreeB, VFree, vfreeB_iff x A]
  | .fam A => by simp [vfreeB, VFree, vfreeB_iff x A]
  | .imm a A => by simp [vfreeB, VFree, vfreeB_iff x A]
  | .mut a A => by simp [vfreeB, VFree, vfreeB_iff x A]
  | .box a A => by simp [vfreeB, VFree, vfreeB_iff x A]
  | .tvar _ => by simp [vfreeB, VFree]
  | .mu A => by simp [vfreeB, VFree, vfreeB_iff x A]
theorem cfreeB_iff (x : LifeVar) : ∀ C : CTy, cfreeB x C = true ↔ CFree x C
  | .ret A => by simp [cfreeB, CFree, vfreeB_iff x A]
  | .arr A C => by simp [cfreeB, CFree, vfreeB_iff x A, cfreeB_iff x C]
  | .amp C D => by simp [cfreeB, CFree, cfreeB_iff x C, cfreeB_iff x D]
  | .top => by simp [cfreeB, CFree]
  | .all y b C => by simp [cfreeB, CFree, cfreeB_iff x C]
  | .nu C => by simp [cfreeB, CFree, cfreeB_iff x C]
  | .eff _ _ _ _ A B fin C => by
      simp [cfreeB, CFree, vfreeB_iff x A, vfreeB_iff x B, cfreeB_iff x fin, cfreeB_iff x C,
        or_assoc]
end

theorem not_vfree_of_vfreeB {x : LifeVar} {A : VTy} (h : vfreeB x A = false) : ¬ VFree x A :=
  fun hf => by rw [(vfreeB_iff x A).mpr hf] at h; exact Bool.noConfusion h

/-! ### Lifetime entailment

On the carrier a lifetime is a number, larger for shorter-lived: `⊤ = 0`, `⊓ = max`, `⊔ = min`,
and `Δ ⊨ δ` puts every `'x ∈ dom Δ` strictly below its bound (`δ('x) > Δ('x)δ`). `ordB` searches
the rules below, strict (`s = true`, `⊏`) or not (`⊑`):

* `@a ⊑ @a` and `@a ⊑ ⊤`, for `@a` defined (`Life.wf`);
* `'x ⊏ @b` and `'x ⊑ @b` from `Δ('x) ⊑ @b`;
* `@a₁ ⊓ @a₂ ⊏ @b` from `@aᵢ ⊏ @b`; `@a₁ ⊔ @a₂ ⊏ @b` from both;
* `@a ⊏ @b₁ ⊔ @b₂` from `@a ⊏ @bᵢ`; `@a ⊏ @b₁ ⊓ @b₂` from both.

It is incomplete: it never compares two lifetimes through a common lower bound other than by
these rules (for example `'x ⊓ 'y ⊑ 'y ⊓ 'x` holds only through the `⊓`/`⊔` rules, which do
find it, but `('x ⊔ 'y) ⊓ 'z ⊑ ('x ⊓ 'z) ⊔ ('y ⊓ 'z)`, distributivity, is not found). -/

/-- `m` and `n` in the order asked: `n < m` strictly, `n ≤ m` otherwise. -/
def Rel (s : Bool) (m n : Nat) : Prop := if s then n < m else n ≤ m

theorem Rel.weaken {s : Bool} {m n : Nat} (h : Rel s m n) : n ≤ m := by
  cases s <;> simp [Rel] at h <;> omega

/-- The entailment search, bounded by `fuel`. -/
def ordB (Δ : LifeCtx) : Nat → Bool → Lifetime.Life → Lifetime.Life → Bool
  | 0, _, _, _ => false
  | n + 1, s, a, b =>
    (!s && a == b && a.wf Δ) ||
    (!s && b == .top && a.wf Δ) ||
    (match a with
     | .var x =>
        match Δ.find? x with
        | some u => ordB Δ n false u b
        | none => false
     | .meet a₁ a₂ => (ordB Δ n s a₁ b && a₂.wf Δ) || (ordB Δ n s a₂ b && a₁.wf Δ)
     | .join a₁ a₂ => ordB Δ n s a₁ b && ordB Δ n s a₂ b
     | .top => false) ||
    (match b with
     | .join b₁ b₂ => (ordB Δ n s a b₁ && b₂.wf Δ) || (ordB Δ n s a b₂ && b₁.wf Δ)
     | .meet b₁ b₂ => ordB Δ n s a b₁ && ordB Δ n s a b₂
     | _ => false)

/-- What `ordB` asserts. -/
def OrdSem (Δ : LifeCtx) (s : Bool) (a b : Lifetime.Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ Rel s m n

theorem interp_of_wf {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {a : Lifetime.Life} (h : a.wf Δ = true) :
    ∃ n, a.interp δ = some n := Life.interp_defined_of_wf hδ h

theorem ordB_sound (Δ : LifeCtx) :
    ∀ (fuel : Nat) (s : Bool) (a b : Lifetime.Life), ordB Δ fuel s a b = true → OrdSem Δ s a b
  | 0, _, _, _, h => by simp [ordB] at h
  | n + 1, s, a, b, h => by
    intro δ hδ
    simp only [ordB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
    rcases h with ((⟨⟨hs, rfl⟩, ha⟩ | ⟨⟨hs, rfl⟩, ha⟩) | ha) | hb
    · obtain ⟨m, hm⟩ := interp_of_wf hδ ha
      exact ⟨m, m, hm, hm, by simp [Rel, hs]⟩
    · obtain ⟨m, hm⟩ := interp_of_wf hδ ha
      exact ⟨m, 0, hm, rfl, by simp [Rel, hs]⟩
    · cases a with
      | var x =>
          simp only at ha
          cases hu : Δ.find? x with
          | none => rw [hu] at ha; simp at ha
          | some u =>
              rw [hu] at ha
              obtain ⟨mu, nb, hmu, hnb, hr⟩ := ordB_sound Δ n false u b ha δ hδ
              obtain ⟨mx, nu, hmx, hnu, hlt⟩ := hδ x u hu
              rw [hmu] at hnu; cases hnu
              refine ⟨mx, nb, hmx, hnb, ?_⟩
              simp only [Rel, SLife.Lt] at hr hlt ⊢
              cases s <;> simp at hr ⊢ <;> omega
      | top => simp at ha
      | meet a₁ a₂ =>
          simp only [Bool.or_eq_true, Bool.and_eq_true] at ha
          rcases ha with ⟨h₁, hw⟩ | ⟨h₂, hw⟩
          · obtain ⟨m₁, nb, hm₁, hnb, hr⟩ := ordB_sound Δ n s a₁ b h₁ δ hδ
            obtain ⟨m₂, hm₂⟩ := interp_of_wf hδ hw
            refine ⟨SLife.meet m₁ m₂, nb, Life.interp_meet_some hm₁ hm₂, hnb, ?_⟩
            simp only [Rel, SLife.meet] at hr ⊢
            cases s <;> simp at hr ⊢ <;> omega
          · obtain ⟨m₂, nb, hm₂, hnb, hr⟩ := ordB_sound Δ n s a₂ b h₂ δ hδ
            obtain ⟨m₁, hm₁⟩ := interp_of_wf hδ hw
            refine ⟨SLife.meet m₁ m₂, nb, Life.interp_meet_some hm₁ hm₂, hnb, ?_⟩
            simp only [Rel, SLife.meet] at hr ⊢
            cases s <;> simp at hr ⊢ <;> omega
      | join a₁ a₂ =>
          simp only [Bool.and_eq_true] at ha
          obtain ⟨m₁, nb, hm₁, hnb, hr₁⟩ := ordB_sound Δ n s a₁ b ha.1 δ hδ
          obtain ⟨m₂, nb', hm₂, hnb', hr₂⟩ := ordB_sound Δ n s a₂ b ha.2 δ hδ
          rw [hnb] at hnb'; cases hnb'
          refine ⟨SLife.join m₁ m₂, nb, Life.interp_join_some hm₁ hm₂, hnb, ?_⟩
          simp only [Rel, SLife.join] at hr₁ hr₂ ⊢
          cases s <;> simp at hr₁ hr₂ ⊢ <;> omega
    · cases b with
      | var _ => simp at hb
      | top => simp at hb
      | join b₁ b₂ =>
          simp only [Bool.or_eq_true, Bool.and_eq_true] at hb
          rcases hb with ⟨h₁, hw⟩ | ⟨h₂, hw⟩
          · obtain ⟨ma, n₁, hma, hn₁, hr⟩ := ordB_sound Δ n s a b₁ h₁ δ hδ
            obtain ⟨n₂, hn₂⟩ := interp_of_wf hδ hw
            refine ⟨ma, SLife.join n₁ n₂, hma, Life.interp_join_some hn₁ hn₂, ?_⟩
            simp only [Rel, SLife.join] at hr ⊢
            cases s <;> simp at hr ⊢ <;> omega
          · obtain ⟨ma, n₂, hma, hn₂, hr⟩ := ordB_sound Δ n s a b₂ h₂ δ hδ
            obtain ⟨n₁, hn₁⟩ := interp_of_wf hδ hw
            refine ⟨ma, SLife.join n₁ n₂, hma, Life.interp_join_some hn₁ hn₂, ?_⟩
            simp only [Rel, SLife.join] at hr ⊢
            cases s <;> simp at hr ⊢ <;> omega
      | meet b₁ b₂ =>
          simp only [Bool.and_eq_true] at hb
          obtain ⟨ma, n₁, hma, hn₁, hr₁⟩ := ordB_sound Δ n s a b₁ hb.1 δ hδ
          obtain ⟨ma', n₂, hma', hn₂, hr₂⟩ := ordB_sound Δ n s a b₂ hb.2 δ hδ
          rw [hma] at hma'; cases hma'
          refine ⟨ma, SLife.meet n₁ n₂, hma, Life.interp_meet_some hn₁ hn₂, ?_⟩
          simp only [Rel, SLife.meet] at hr₁ hr₂ ⊢
          cases s <;> simp at hr₁ hr₂ ⊢ <;> omega

/-- The search budget: the depth of both sides plus every bound of `Δ` once. -/
def ordFuel (Δ : LifeCtx) (a b : Lifetime.Life) : Nat :=
  a.depth + b.depth + (Δ.entries.map (fun p => p.2.depth + 1)).sum + 1

/-- `Δ ⊨ @a ⊏ @b`, decided soundly. -/
def ltB (Δ : LifeCtx) (a b : Lifetime.Life) : Bool := ordB Δ (ordFuel Δ a b) true a b

/-- `Δ ⊨ @a ⊑ @b`, decided soundly. -/
def leB (Δ : LifeCtx) (a b : Lifetime.Life) : Bool := ordB Δ (ordFuel Δ a b) false a b

theorem ltB_sound {Δ : LifeCtx} {a b : Lifetime.Life} (h : ltB Δ a b = true) : Δ.EntailsLt a b := by
  intro δ hδ
  obtain ⟨m, n, hm, hn, hr⟩ := ordB_sound Δ _ true a b h δ hδ
  exact ⟨m, n, hm, hn, by simpa [Rel, SLife.Lt] using hr⟩

theorem leB_sound {Δ : LifeCtx} {a b : Lifetime.Life} (h : leB Δ a b = true) : Δ.EntailsLe a b := by
  intro δ hδ
  obtain ⟨m, n, hm, hn, hr⟩ := ordB_sound Δ _ false a b h δ hδ
  exact ⟨m, n, hm, hn, by simpa [Rel, SLife.Le] using hr⟩

theorem defines_of_wf {Δ : LifeCtx} {a : Lifetime.Life} (h : a.wf Δ = true) : Δ.Defines a :=
  fun _ hδ => interp_of_wf hδ h

/-! ### Outlives and scoping -/

/-- `Δ ⊢ A ⊐ @a`, decided through `leB` at a box and `ltB` at a borrow.  `[spec §23]` -/
def outlivesB (Δ : LifeCtx) (a : Lifetime.Life) : VTy → Bool
  | .unit => true
  | .zero => true
  | .int _ => true
  | .opq _ => true
  | .bang _ => true
  | .fam A => outlivesB Δ a A
  | .tvar _ => true
  | .tensor A B => outlivesB Δ a A && outlivesB Δ a B
  | .sum A B => outlivesB Δ a A && outlivesB Δ a B
  | .ref A => outlivesB Δ a A
  | .box b _ => leB Δ a b
  | .imm b _ => ltB Δ a b
  | .mut b _ => ltB Δ a b
  | .mu A => outlivesB Δ a A
  | .thunk _ => false
  | .unk => false

theorem outlivesB_sound (Δ : LifeCtx) (a : Lifetime.Life) :
    ∀ A : VTy, outlivesB Δ a A = true → VOutlives Δ a A
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .int _, _ => .int
  | .opq _, _  => .opq
  | .bang _, _ => .bang
  | .fam A, h => .fam (outlivesB_sound Δ a A h)
  | .tvar _, _ => .tvar
  | .tensor A B, h => by
      simp only [outlivesB, Bool.and_eq_true] at h
      exact .tensor (outlivesB_sound Δ a A h.1) (outlivesB_sound Δ a B h.2)
  | .sum A B, h => by
      simp only [outlivesB, Bool.and_eq_true] at h
      exact .sum (outlivesB_sound Δ a A h.1) (outlivesB_sound Δ a B h.2)
  | .ref A, h => .ref (outlivesB_sound Δ a A h)
  | .box _ _, h => .box (leB_sound h)
  | .imm _ _, h => .imm (ltB_sound h)
  | .mut _ _, h => .mut (ltB_sound h)
  | .mu A, h => .mu (outlivesB_sound Δ a A h)
  | .thunk _, h => by simp [outlivesB] at h
  | .unk, h => by simp [outlivesB] at h

/-- BOXED-κ's answer premise `Row.AnsOutlives Δ d S`: every non-abortive operation's answer type
outlives `@d`, by `outlivesB`.  `[spec §28]` -/
def ansOutlivesB (Δ : LifeCtx) (d : Lifetime.Life) (S : Row) : Bool :=
  S.all fun o => o.abort || outlivesB Δ d o.B

theorem ansOutlivesB_sound {Δ : LifeCtx} {d : Lifetime.Life} {S : Row}
    (h : ansOutlivesB Δ d S = true) : Row.AnsOutlives Δ d S := by
  intro o ho ha
  have := List.all_eq_true.mp h o ho
  rw [ha, Bool.false_or] at this
  exact outlivesB_sound Δ d o.B this

/-- `Δ ⊢ A ⊒ @a`, decided through `leB` at a box and at a borrow: the side condition of the
borrows that lend a payload `mut`.  `[spec §23]` -/
def outlivesLeB (Δ : LifeCtx) (a : Lifetime.Life) : VTy → Bool
  | .unit => true
  | .zero => true
  | .int _ => true
  | .opq _ => true
  | .bang _ => true
  | .fam A => outlivesLeB Δ a A
  | .tvar _ => true
  | .tensor A B => outlivesLeB Δ a A && outlivesLeB Δ a B
  | .sum A B => outlivesLeB Δ a A && outlivesLeB Δ a B
  | .ref A => outlivesLeB Δ a A
  | .box b _ => leB Δ a b
  | .imm b _ => leB Δ a b
  | .mut b _ => leB Δ a b
  | .mu A => outlivesLeB Δ a A
  | .thunk _ => false
  | .unk => false

theorem outlivesLeB_sound (Δ : LifeCtx) (a : Lifetime.Life) :
    ∀ A : VTy, outlivesLeB Δ a A = true → VOutlivesLe Δ a A
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .int _, _ => .int
  | .opq _, _  => .opq
  | .bang _, _ => .bang
  | .fam A, h => .fam (outlivesLeB_sound Δ a A h)
  | .tvar _, _ => .tvar
  | .tensor A B, h => by
      simp only [outlivesLeB, Bool.and_eq_true] at h
      exact .tensor (outlivesLeB_sound Δ a A h.1) (outlivesLeB_sound Δ a B h.2)
  | .sum A B, h => by
      simp only [outlivesLeB, Bool.and_eq_true] at h
      exact .sum (outlivesLeB_sound Δ a A h.1) (outlivesLeB_sound Δ a B h.2)
  | .ref A, h => .ref (outlivesLeB_sound Δ a A h)
  | .box _ _, h => .box (leB_sound h)
  | .imm _ _, h => .imm (leB_sound h)
  | .mut _ _, h => .mut (leB_sound h)
  | .mu A, h => .mu (outlivesLeB_sound Δ a A h)
  | .thunk _, h => by simp [outlivesLeB] at h
  | .unk, h => by simp [outlivesLeB] at h

/-- foldImm's `∀ Δ' a, VOutlives Δ' a R`: true at `1`, `0`, `I32`/`I64`, `!`, `X`, and `⊗`,
`⊕`, `Ref`, `μ` over such types. It is false at `U`, `Unk`, `Imm`, `Mut` and `[@]`, where the
premise fails at `Δ' = ∅`, `@a = ⊤`, so the decision is also complete. -/
def outlivesAllB : VTy → Bool
  | .unit => true
  | .zero => true
  | .int _ => true
  | .opq _ => true
  | .bang _ => true
  | .fam A => outlivesAllB A
  | .tvar _ => true
  | .tensor A B => outlivesAllB A && outlivesAllB B
  | .sum A B => outlivesAllB A && outlivesAllB B
  | .ref A => outlivesAllB A
  | .mu A => outlivesAllB A
  | .box _ _ => false
  | .imm _ _ => false
  | .mut _ _ => false
  | .thunk _ => false
  | .unk => false

theorem outlivesAllB_sound : ∀ R : VTy, outlivesAllB R = true → ∀ Δ' a, VOutlives Δ' a R
  | .unit, _, _, _ => .unit
  | .zero, _, _, _ => .zero
  | .int _, _, _, _ => .int
  | .opq _, _, _, _  => .opq
  | .bang _, _, _, _ => .bang
  | .fam A, h, Δ', a => .fam (outlivesAllB_sound A h Δ' a)
  | .tvar _, _, _, _ => .tvar
  | .tensor A B, h, Δ', a => by
      simp only [outlivesAllB, Bool.and_eq_true] at h
      exact .tensor (outlivesAllB_sound A h.1 Δ' a) (outlivesAllB_sound B h.2 Δ' a)
  | .sum A B, h, Δ', a => by
      simp only [outlivesAllB, Bool.and_eq_true] at h
      exact .sum (outlivesAllB_sound A h.1 Δ' a) (outlivesAllB_sound B h.2 Δ' a)
  | .ref A, h, Δ', a => .ref (outlivesAllB_sound A h Δ' a)
  | .mu A, h, Δ', a => .mu (outlivesAllB_sound A h Δ' a)
  | .box _ _, h, _, _ => by simp [outlivesAllB] at h
  | .imm _ _, h, _, _ => by simp [outlivesAllB] at h
  | .mut _ _, h, _, _ => by simp [outlivesAllB] at h
  | .thunk _, h, _, _ => by simp [outlivesAllB] at h
  | .unk, h, _, _ => by simp [outlivesAllB] at h

/-- Every variable of `a` is in `ex` or bound by `Δ`. -/
def lifeScopedB (Δ : LifeCtx) (ex : List LifeVar) : Lifetime.Life → Bool
  | .var x => ex.contains x || (Δ.find? x).isSome
  | .top => true
  | .join a b => lifeScopedB Δ ex a && lifeScopedB Δ ex b
  | .meet a b => lifeScopedB Δ ex a && lifeScopedB Δ ex b

theorem lifeScopedB_sound {Δ : LifeCtx} {ex : List LifeVar} {y : LifeVar} :
    ∀ a : Lifetime.Life, lifeScopedB Δ ex a = true → a.mentions y = true → y ∈ ex ∨ (Δ.find? y).isSome
  | .var x, h, hm => by
      simp only [Life.mentions, beq_iff_eq] at hm
      subst hm
      simpa [lifeScopedB] using h
  | .top, _, hm => by simp [Life.mentions] at hm
  | .join a b, h, hm => by
      simp only [lifeScopedB, Bool.and_eq_true] at h
      simp only [Life.mentions, Bool.or_eq_true] at hm
      exact hm.elim (lifeScopedB_sound a h.1) (lifeScopedB_sound b h.2)
  | .meet a b, h, hm => by
      simp only [lifeScopedB, Bool.and_eq_true] at h
      simp only [Life.mentions, Bool.or_eq_true] at hm
      exact hm.elim (lifeScopedB_sound a h.1) (lifeScopedB_sound b h.2)

mutual
/-- Every free lifetime variable of `A` is in `ex` or bound by `Δ`. -/
def vScopedB (Δ : LifeCtx) (ex : List LifeVar) : VTy → Bool
  | .unit => true
  | .zero => true
  | .unk => true
  | .int _ => true
  | .opq _ => true
  | .tvar _ => true
  | .tensor A B => vScopedB Δ ex A && vScopedB Δ ex B
  | .sum A B => vScopedB Δ ex A && vScopedB Δ ex B
  | .thunk C => cScopedB Δ ex C
  | .ref A => vScopedB Δ ex A
  | .bang A => vScopedB Δ ex A
  | .fam A => vScopedB Δ ex A
  | .mu A => vScopedB Δ ex A
  | .imm a A => lifeScopedB Δ ex a && vScopedB Δ ex A
  | .mut a A => lifeScopedB Δ ex a && vScopedB Δ ex A
  | .box a A => lifeScopedB Δ ex a && vScopedB Δ ex A
/-- Every free lifetime variable of `C` is in `ex` or bound by `Δ`. -/
def cScopedB (Δ : LifeCtx) (ex : List LifeVar) : CTy → Bool
  | .ret A => vScopedB Δ ex A
  | .arr A C => vScopedB Δ ex A && cScopedB Δ ex C
  | .amp C D => cScopedB Δ ex C && cScopedB Δ ex D
  | .top => true
  | .all y b C => lifeScopedB Δ ex b && cScopedB Δ (y :: ex) C
  | .nu C => cScopedB Δ ex C
  | .eff _ _ _ _ A B fin C =>
      vScopedB Δ ex A && vScopedB Δ ex B && cScopedB Δ ex fin && cScopedB Δ ex C
end

mutual
theorem vScopedB_sound {Δ : LifeCtx} {y : LifeVar} : ∀ {ex : List LifeVar} (A : VTy),
    vScopedB Δ ex A = true → VFree y A → y ∈ ex ∨ (Δ.find? y).isSome
  | _, .unit, _, hf => hf.elim
  | _, .zero, _, hf => hf.elim
  | _, .unk, _, hf => hf.elim
  | _, .int _, _, hf => hf.elim
  | _, .opq _, _, hf => hf.elim
  | _, .tvar _, _, hf => hf.elim
  | _, .tensor A B, h, hf => by
      simp only [vScopedB, Bool.and_eq_true] at h
      exact hf.elim (vScopedB_sound A h.1) (vScopedB_sound B h.2)
  | _, .sum A B, h, hf => by
      simp only [vScopedB, Bool.and_eq_true] at h
      exact hf.elim (vScopedB_sound A h.1) (vScopedB_sound B h.2)
  | _, .thunk C, h, hf => cScopedB_sound C h hf
  | _, .ref A, h, hf => vScopedB_sound A h hf
  | _, .bang A, h, hf => vScopedB_sound A h hf
  | _, .fam A, h, hf => vScopedB_sound A h hf
  | _, .mu A, h, hf => vScopedB_sound A h hf
  | _, .imm a A, h, hf => by
      simp only [vScopedB, Bool.and_eq_true] at h
      exact hf.elim (lifeScopedB_sound a h.1) (vScopedB_sound A h.2)
  | _, .mut a A, h, hf => by
      simp only [vScopedB, Bool.and_eq_true] at h
      exact hf.elim (lifeScopedB_sound a h.1) (vScopedB_sound A h.2)
  | _, .box a A, h, hf => by
      simp only [vScopedB, Bool.and_eq_true] at h
      exact hf.elim (lifeScopedB_sound a h.1) (vScopedB_sound A h.2)
theorem cScopedB_sound {Δ : LifeCtx} {y : LifeVar} : ∀ {ex : List LifeVar} (C : CTy),
    cScopedB Δ ex C = true → CFree y C → y ∈ ex ∨ (Δ.find? y).isSome
  | _, .ret A, h, hf => vScopedB_sound A h hf
  | _, .arr A C, h, hf => by
      simp only [cScopedB, Bool.and_eq_true] at h
      exact hf.elim (vScopedB_sound A h.1) (cScopedB_sound C h.2)
  | _, .amp C D, h, hf => by
      simp only [cScopedB, Bool.and_eq_true] at h
      exact hf.elim (cScopedB_sound C h.1) (cScopedB_sound D h.2)
  | _, .top, _, hf => hf.elim
  | _, .all z b C, h, hf => by
      simp only [cScopedB, Bool.and_eq_true] at h
      rcases hf with hb | ⟨hne, hC⟩
      · exact lifeScopedB_sound b h.1 hb
      · rcases cScopedB_sound C h.2 hC with hm | hs
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact absurd rfl hne
          · exact Or.inl hm
        · exact Or.inr hs
  | _, .nu C, h, hf => cScopedB_sound C h hf
  | _, .eff _ _ _ _ A B fin C, h, hf => by
      simp only [cScopedB, Bool.and_eq_true] at h
      rcases hf with hf | hf | hf | hf
      · exact vScopedB_sound A h.1.1.1 hf
      · exact vScopedB_sound B h.1.1.2 hf
      · exact cScopedB_sound fin h.1.2 hf
      · exact cScopedB_sound C h.2 hf
end

/-- `VScoped Δ A`, decided soundly (and completely). -/
def scopedB (Δ : LifeCtx) (A : VTy) : Bool := vScopedB Δ [] A

theorem scopedB_sound {Δ : LifeCtx} {A : VTy} (h : scopedB Δ A = true) : VScoped Δ A := by
  intro y hy
  rcases vScopedB_sound A h hy with hm | hs
  · simp at hm
  · exact Option.isSome_iff_exists.mp hs

/-! ### Contexts of `!` types, and binders fresh for `Δ` -/

/-- `A` is a `!` type. -/
def isBangB : VTy → Bool
  | .bang _ => true
  | _ => false

theorem isBangB_sound {A : VTy} (h : isBangB A = true) : ∃ B, A = .bang B := by
  cases A <;> simp [isBangB] at h
  exact ⟨_, rfl⟩

/-- No bound of `Δ` mentions `x`. -/
def boundsAvoidB (Δ : LifeCtx) (x : LifeVar) : Bool := Δ.entries.all (fun p => !p.2.mentions x)

theorem assocFind_mem {β : Type} {y : LifeVar} {u : β} :
    ∀ {l : List (LifeVar × β)}, assocFind y l = some u → ∃ z, (z, u) ∈ l
  | [], h => by simp [assocFind] at h
  | (z, v) :: t, h => by
      simp only [assocFind] at h
      split at h
      · cases h; exact ⟨z, List.mem_cons_self⟩
      · obtain ⟨w, hw⟩ := assocFind_mem h
        exact ⟨w, List.mem_cons_of_mem _ hw⟩

theorem boundsAvoidB_sound {Δ : LifeCtx} {x : LifeVar} (h : boundsAvoidB Δ x = true) :
    ∀ y u, Δ.find? y = some u → u.mentions x = false := by
  intro y u hu
  obtain ⟨z, hz⟩ := assocFind_mem hu
  have := List.all_eq_true.mp h _ hz
  simpa using this

/-! ### Rows  `[spec §19]` -/

/-- `VTy.Drop`, decided: data, borrows and `!`, under `⊗` and `⊕`. -/
def dropB : VTy → Bool
  | .unit | .zero | .int _ | .unk | .opq _ | .bang _ | .imm _ _ | .mut _ _ => true
  | .tensor A B | .sum A B => dropB A && dropB B
  | _ => false

theorem dropB_sound : ∀ A : VTy, dropB A = true → A.Drop
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .int w, _ => .int w
  | .unk, _ => .unk
  | .opq k, _ => .opq k
  | .bang A, _ => .bang A
  | .imm a A, _ => .imm a A
  | .mut a A, _ => .mut a A
  | .tensor A B, h => by
      simp only [dropB, Bool.and_eq_true] at h
      exact .tensor (dropB_sound A h.1) (dropB_sound B h.2)
  | .sum A B, h => by
      simp only [dropB, Bool.and_eq_true] at h
      exact .sum (dropB_sound A h.1) (dropB_sound B h.2)
  | .thunk _, h | .ref _, h | .box _ _, h | .tvar _, h | .mu _, h | .fam _, h => by
      simp [dropB] at h

/-- `RowLe S S'`, decided: every operation of `S` is found in `S'` as itself. -/
def rowLeB (S S' : Row) : Bool := S.all fun o => Row.find S' o.n o.i == some o

theorem rowLeB_sound {S S' : Row} (h : rowLeB S S' = true) : RowLe S S' := by
  refine RowLe.of_find fun n i o hf => ?_
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  have := List.all_eq_true.mp h o hm
  simpa using this

/-- **`[handle-last]`'s cancel rows at the checker's empty ones** (SPEC §51, `LastFinOK`): where
`Σ_W` is below `Σ` (`rowLeB`), `Σ_W` finds what `Σ` finds, so `LastFinOK` holds at the empty cancel
row (`lastFinOK_nil_of_find`).  `[spec §51, §54]` -/
theorem lastFinOK_of_rowLeB {S SW : Row} (h : rowLeB SW S = true) (X : VTy) :
    LastFinOK S SW (.ret .unit) X :=
  lastFinOK_nil_of_find fun _ _ o hf => by
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    have := List.all_eq_true.mp h o hm
    simpa using this

/-- `Row.NZ`, decided. -/
def Row.nzB (S : Row) : Bool := S.all fun o => o.n != 0

theorem Row.nzB_sound {S : Row} (h : Row.nzB S = true) : S.NZ := fun o ho => by
  have := List.all_eq_true.mp h o ho
  simpa using this

/-- `Row.Uniq`, decided. -/
def Row.uniqB (S : Row) : Bool := decide (S.Pairwise fun o o' => ¬ (o.n = o'.n ∧ o.i = o'.i))

theorem Row.uniqB_sound {S : Row} (h : Row.uniqB S = true) : S.Uniq :=
  (of_decide_eq_true h : S.Pairwise fun o o' => ¬ (o.n = o'.n ∧ o.i = o'.i))

/-- `Row.Weak`, decided. -/
def Row.weakB (S : Row) : Bool := S.any fun o => o.q != .lin

theorem Row.weakB_iff {S : Row} : Row.weakB S = true ↔ S.Weak := by
  simp [Row.weakB, Row.Weak]

/-- `Row.Unr`, decided. -/
def Row.unrB (S : Row) : Bool := S.any fun o => o.q == .unr

theorem Row.unrB_iff {S : Row} : Row.unrB S = true ↔ S.Unr := by
  simp [Row.unrB, Row.Unr]

/-- `CTy.FinUnr`, decided. -/
def finUnrB : CTy → Bool
  | .eff _ _ q _ _ B f C => q.toQual == .unr || (capB q && finUnrB f) || finUnrB C
  | _ => false

theorem finUnrB_iff : ∀ C : CTy, finUnrB C = true ↔ C.FinUnr
  | .eff _ _ q _ _ B f C => by
      simp only [finUnrB, CTy.FinUnr, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
        finUnrB_iff f, finUnrB_iff C, or_assoc]
  | .ret _ | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => by
      simp [finUnrB, CTy.FinUnr]

/-- `Row.UnrD`, decided. -/
def Row.unrDB (S : Row) : Bool := S.any fun o => o.q == .unr || (capB o.cnt && finUnrB o.fin)

theorem Row.unrDB_iff {S : Row} : Row.unrDB S = true ↔ S.UnrD := by
  simp [Row.unrDB, Row.UnrD, finUnrB_iff]

/-- `Row.Unwind S x`, decided: every operation abortive, named, its argument free of `'x` and
outliving every lifetime (`outlivesAllB`), its answer free of `'x`. -/
def Row.unwindB (S : Row) (x : LifeVar) : Bool :=
  S.all fun o => o.abort && o.n != 0 && !vfreeB x o.A && !vfreeB x o.B && outlivesAllB o.A

theorem Row.unwindB_sound {S : Row} {x : LifeVar} (h : Row.unwindB S x = true) : S.Unwind x := by
  intro o ho
  have := List.all_eq_true.mp h o ho
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
  exact ⟨this.1.1.1.1, this.1.1.1.2, not_vfree_of_vfreeB this.1.1.2, not_vfree_of_vfreeB this.1.2,
    outlivesAllB_sound _ this.2⟩

end BoCa.Fig16.LogRel.Core.Check
