import Lowering.PrintRel

/-!
# Lowering — the print writes no `unreachable`  `[spec §56]`

The print of a term with no effect primitive writes no `unreachable` (`Tm.noUnr`): not in `main`,
not in the code of any `λ`, not in the primitives' codes (`lirOf_noUnr`). Every construct of the
pure fragment is printed as code that runs.
-/

namespace Lowering
open BoCa
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op)

/-- `t` writes no `unreachable`. -/
def Tm.noUnr : Tm → Bool
  | .prim .unreachable _ => false
  | .letv _ e b => Tm.noUnr e && Tm.noUnr b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => Tm.noUnr b
  | .case _ _ b₁ _ b₂ => Tm.noUnr b₁ && Tm.noUnr b₂
  | _ => true

/-- Every function the print has written writes no `unreachable`. -/
def PSNoUnr (s : PS) : Prop := ∀ f ∈ s.fns, Tm.noUnr f.body = true

theorem noUnr_dropIf (c : Bool) (x : Nat) {t : Tm} (h : Tm.noUnr t = true) :
    Tm.noUnr (dropIf c x t) = true := by
  cases c <;> simp [dropIf, Tm.noUnr, h]

theorem noUnr_dropsT : ∀ (xs : List Nat) {t : Tm}, Tm.noUnr t = true → Tm.noUnr (dropsT xs t) = true
  | [], _, h => h
  | x :: xs, _, h => by
      simp only [dropsT, List.foldr_cons] at *
      simp only [Tm.noUnr]
      exact noUnr_dropsT xs h

theorem noUnr_envCopies (ρ : Nat → Nat) (out : Out) :
    ∀ (cs : List Nat) (m : Nat) {t : Tm}, Tm.noUnr t = true → Tm.noUnr (envCopies ρ out cs m t) = true
  | [], _, _, h => h
  | k :: ks, m, _, h => by
      simp only [envCopies]
      split
      · simp only [Tm.noUnr]; exact noUnr_envCopies ρ out ks (m + 1) h
      · exact noUnr_envCopies ρ out ks (m + 1) h

theorem emit_noUnr {k : Nat} {body : Tm} {m : Nat} {s : PS} (hs : PSNoUnr s)
    (hb : Tm.noUnr body = true) : PSNoUnr (emit k body m s).2 := by
  intro f hf
  simp only [emit, Array.mem_push] at hf
  rcases hf with hf | rfl
  · exact hs f hf
  · exact hb

/-- **The print of an effect-free term writes no `unreachable`**, nor any code it writes. -/
theorem prG_noUnr : ∀ (e : Expr) (ρ : Nat → Nat) (n : Nat) (out : Out) (s : PS),
    effFreeB e = true → PSNoUnr s →
    Tm.noUnr (prG ρ n out e s).1.1 = true ∧ PSNoUnr (prG ρ n out e s).2 := by
  intro e
  induction e with
  | var k =>
      intro ρ n out s _ hs
      cases hk : out k
      · have : prG ρ n out (.var k) s = ((.var (ρ k), n), s) := by simp [prG, hk]; rfl
        rw [this]; exact ⟨rfl, hs⟩
      · have : prG ρ n out (.var k) s = ((.copy (ρ k) n (.var n), n + 1), s) := by
          simp [prG, hk]; rfl
        rw [this]; exact ⟨rfl, hs⟩
  | unit | loc _ => intro ρ n out s _ hs; exact ⟨rfl, hs⟩
  | prim q =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.not_eq_true'] at hc
      by_cases hl : ∃ c, q = .lit c
      · obtain ⟨c, rfl⟩ := hl; exact ⟨rfl, hs⟩
      by_cases hh : ∃ op, q = .host op
      · obtain ⟨op, rfl⟩ := hh
        exact ⟨rfl, emit_noUnr hs rfl⟩
      simp only [not_exists] at hl hh
      obtain ⟨c, hcq⟩ := rtCode_of_effFree hc hl hh
      have : prG ρ n out (.prim q) s = ((.clos c [], n), s) := by
        cases q <;> simp_all [prG, primT, rtCode] <;> rfl
      rw [this]; exact ⟨rfl, hs⟩
  | pair a b iha ihb | seq a b iha ihb | app a b iha ihb =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.and_eq_true] at hc
      first
      | (obtain ⟨h1, s1⟩ := iha ρ (n + 2) (unionO out (fvAt 0 b)) s hc.1 hs
         obtain ⟨h2, s2⟩ := ihb ρ (prG ρ (n + 2) (unionO out (fvAt 0 b)) a s).1.2 out _ hc.2 s1
         refine ⟨?_, s2⟩
         show Tm.noUnr (.letv n _ (.letv (n + 1) _ (.pair n (n + 1)))) = true
         simp [Tm.noUnr, h1, h2])
      | (obtain ⟨h1, s1⟩ := iha ρ (n + 1) (unionO out (fvAt 0 b)) s hc.1 hs
         obtain ⟨h2, s2⟩ := ihb ρ (prG ρ (n + 1) (unionO out (fvAt 0 b)) a s).1.2 out _ hc.2 s1
         refine ⟨?_, s2⟩
         show Tm.noUnr (.letv n _ (.drop n _)) = true
         simp [Tm.noUnr, h1, h2])
      | (obtain ⟨h1, s1⟩ := ihb ρ (n + 2) (unionO out (fvAt 0 a)) s hc.2 hs
         obtain ⟨h2, s2⟩ := iha ρ (prG ρ (n + 2) (unionO out (fvAt 0 a)) b s).1.2 out _ hc.1 s1
         refine ⟨?_, s2⟩
         show Tm.noUnr (.letv n _ (.letv (n + 1) _ (.app (n + 1) n))) = true
         simp [Tm.noUnr, h1, h2])
  | inj₁ a ih | inj₂ a ih =>
      intro ρ n out s hc hs
      obtain ⟨h1, s1⟩ := ih ρ (n + 1) out s hc hs
      refine ⟨?_, s1⟩
      show Tm.noUnr (.letv n _ (.inj _ n)) = true
      simp [Tm.noUnr, h1]
  | letpair a b iha ihb =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.and_eq_true] at hc
      obtain ⟨h1, s1⟩ := iha ρ (n + 3) (unionO out (fvAt 2 b)) s hc.1 hs
      obtain ⟨h2, s2⟩ := ihb (cons2 (n + 2) (n + 1) ρ)
        (prG ρ (n + 3) (unionO out (fvAt 2 b)) a s).1.2 (liftO 2 out) _ hc.2 s1
      refine ⟨?_, s2⟩
      show Tm.noUnr (.letv n _ (.letpair (n + 1) (n + 2) n (dropIf _ (n + 1) (dropIf _ (n + 2) _))))
        = true
      simp only [Tm.noUnr, h1, Bool.true_and]
      exact noUnr_dropIf _ _ (noUnr_dropIf _ _ h2)
  | case v a b ihv iha ihb =>
      intro ρ n out s hc hs
      simp only [effFreeB, Bool.and_eq_true] at hc
      obtain ⟨h1, s1⟩ := ihv ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) s hc.1.1 hs
      obtain ⟨h2, s2⟩ := iha (cons1 (n + 1) ρ)
        (prG ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) v s).1.2 (liftO 1 out) _ hc.1.2 s1
      obtain ⟨h3, s3⟩ := ihb (cons1 (n + 2) ρ)
        (prG (cons1 (n + 1) ρ) (prG ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) v s).1.2
          (liftO 1 out) a (prG ρ (n + 3) (unionO out (unionO (fvAt 1 a) (fvAt 1 b))) v s).2).1.2
        (liftO 1 out) _ hc.2 s2
      refine ⟨?_, s3⟩
      show Tm.noUnr (.letv n _ (.case n (n + 1) (dropIf _ (n + 1) (dropsT _ _))
        (n + 2) (dropIf _ (n + 2) (dropsT _ _)))) = true
      simp only [Tm.noUnr, h1, Bool.true_and, Bool.and_eq_true]
      exact ⟨noUnr_dropIf _ _ (noUnr_dropsT _ h2), noUnr_dropIf _ _ (noUnr_dropsT _ h3)⟩
  | lam b ih =>
      intro ρ n out s hc hs
      simp only [effFreeB] at hc
      obtain ⟨h1, s1⟩ := ih (lamEnv b) ((capt b).length + 1) noOut s hc hs
      refine ⟨noUnr_envCopies ρ out (capt b) n rfl, emit_noUnr s1 (noUnr_dropIf _ _ h1)⟩

theorem preludePS_noUnr : PSNoUnr preludePS := by
  have h0 : PSNoUnr rtPS := by
    intro f hf
    simp only [rtPS, rtBodies, List.foldl_cons, List.foldl_nil, emit] at hf
    simp only [Array.mem_push] at hf
    rcases hf with ((((((((((((((hf | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) |
      rfl) | rfl) | rfl) | rfl) | rfl) <;> first | (simp at hf) | rfl
  rw [preludePS_eq]
  exact (prG_noUnr (.lam fixBody) (fun _ => 0) 0 noOut rtPS rfl h0).2

/-- **The program of an effect-free term writes no `unreachable`**: not in `main`, not in any
function. -/
theorem lirOf_noUnr (e : Expr) (he : effFreeB e = true) :
    Tm.noUnr (lirOf e).main = true ∧ ∀ f ∈ (lirOf e).fns, Tm.noUnr f.body = true :=
  prG_noUnr e (fun _ => 0) 0 noOut preludePS he preludePS_noUnr

end Lowering
