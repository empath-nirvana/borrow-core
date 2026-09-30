import HandlersAsBorrows.Source

/-!
# The target environment: capabilities as borrows

The lexical environment `K` becomes one threaded value of type `EnvTy n K`:

* a capability `cap S A B` is the **object** `Mut 'x S ⊗ !(S ⊗ A ⊸ S ⊗ B)`: the handler's
  state, borrowed mutably at the handler's lifetime `'x`, beside its clause as `!` code;
* a block `blk A B` is `!(A ⊗ E ⊸ B ⊗ E)`, `E` the environment of its definition;
* `EnvTy n [] = 1`, and each entry is paired in front of the environment it was defined in.

The capability with `k` capabilities below it has lifetime variable `'(n + k)`: handlers are
numbered outermost first from the base `n` (`ncaps`).  `Good n K Δ` says `Δ` binds exactly the
variables below `n + ncaps K`.

`[about ours]`
-/

noncomputable section

namespace HandlersAsBorrows.Xi
open BoCa BoCa.Lifetime

/-- The number of capabilities in an environment. -/
def ncaps : List Entry → Nat
  | [] => 0
  | .cap _ _ _ :: t => ncaps t + 1
  | .blk _ _ :: t => ncaps t

/-- The clause's type `!(S ⊗ A ⊸ S ⊗ B)`. -/
def codeTy (S A B : VTy) : Ty := .bang (.lolli (.tensor S.tr A.tr) (.tensor S.tr B.tr))

/-- The environment's type. -/
def EnvTy (n : Nat) : List Entry → Ty
  | [] => .unit
  | .cap S A B :: t => .tensor (.tensor (.mut (.var (n + ncaps t)) S.tr) (codeTy S A B)) (EnvTy n t)
  | .blk A B :: t =>
      .tensor (.bang (.lolli (.tensor A.tr (EnvTy n t)) (.tensor B.tr (EnvTy n t)))) (EnvTy n t)

/-- `Δ` binds exactly the variables below `n + ncaps K`. -/
structure Good (n : Nat) (K : List Entry) (Δ : LifeCtx) : Prop where
  bound : ∀ x, x < n + ncaps K → (Δ.find? x).isSome = true
  fresh : ∀ x, n + ncaps K ≤ x → Δ.find? x = none

/-- The lifetime context of a handler's body: `Δ, 'x ⊏ ⊓Δ` at `x = n + ncaps K`, `withbor`'s
binder. -/
abbrev hΔ (n : Nat) (K : List Entry) (Δ : LifeCtx) : LifeCtx :=
  Δ.extend (n + ncaps K) Δ.meetOfDom

theorem Good.handle {n : Nat} {K : List Entry} {Δ : LifeCtx} (h : Good n K Δ) (S A B : VTy) :
    Good n (.cap S A B :: K) (hΔ n K Δ) := by
  constructor
  · intro x hx
    rw [LifeCtx.find?_extend]
    by_cases hxe : n + ncaps K = x
    · simp [hxe]
    · rw [if_neg hxe]; exact h.bound x (by simp [ncaps] at hx; omega)
  · intro x hx
    simp only [ncaps] at hx
    have hne : n + ncaps K ≠ x := by omega
    rw [LifeCtx.find?_extend, if_neg hne]
    exact h.fresh x (by omega)

theorem Good.clause {n : Nat} {K : List Entry} {Δ : LifeCtx} (h : Good n K Δ) :
    Good (n + ncaps K + 1) [] (hΔ n K Δ) := by
  constructor
  · intro x hx
    rw [LifeCtx.find?_extend]
    by_cases hxe : n + ncaps K = x
    · simp [hxe]
    · rw [if_neg hxe]; exact h.bound x (by simp [ncaps] at hx; omega)
  · intro x hx
    simp only [ncaps] at hx
    have hne : n + ncaps K ≠ x := by omega
    rw [LifeCtx.find?_extend, if_neg hne]
    exact h.fresh x (by omega)

theorem Good.blk {n : Nat} {K : List Entry} {Δ : LifeCtx} (h : Good n K Δ) (A B : VTy) :
    Good n (.blk A B :: K) Δ := ⟨h.bound, h.fresh⟩

/-! ## Scoping -/

@[simp] theorem VTy.scoped (A : VTy) (Δ : LifeCtx) : A.tr.scopedB Δ = true := by
  induction A <;> simp_all [VTy.tr, Ty.scopedB]

@[simp] theorem VTy.noBinds (A : VTy) (x : LifeVar) : A.tr.bindsB x = false := by
  induction A <;> simp_all [VTy.tr, Ty.bindsB]

@[simp] theorem codeTy_scoped (S A B : VTy) (Δ : LifeCtx) : (codeTy S A B).scopedB Δ = true := by
  simp [codeTy, Ty.scopedB]

@[simp] theorem codeTy_noBinds (S A B : VTy) (x : LifeVar) : (codeTy S A B).bindsB x = false := by
  simp [codeTy, Ty.bindsB]

@[simp] theorem EnvTy.noBinds (n : Nat) (x : LifeVar) : ∀ K, (EnvTy n K).bindsB x = false
  | [] => rfl
  | .cap S A B :: t => by simp [EnvTy, Ty.bindsB, EnvTy.noBinds n x t]
  | .blk A B :: t => by simp [EnvTy, Ty.bindsB, EnvTy.noBinds n x t]

theorem EnvTy.scoped_of (n : Nat) (Δ : LifeCtx) : ∀ K,
    (∀ x, x < n + ncaps K → (Δ.find? x).isSome = true) → (EnvTy n K).scopedB Δ = true
  | [] => fun _ => rfl
  | .cap S A B :: t => fun h => by
      have ht := EnvTy.scoped_of n Δ t (fun x hx => h x (by simp [ncaps]; omega))
      have hv := h (n + ncaps t) (by simp [ncaps])
      simp [EnvTy, Ty.scopedB, ht, Life.wf, hv]
  | .blk A B :: t => fun h => by
      have ht := EnvTy.scoped_of n Δ t (fun x hx => h x (by simpa [ncaps] using hx))
      simp [EnvTy, Ty.scopedB, ht]

theorem Good.scoped {n : Nat} {K : List Entry} {Δ : LifeCtx} (h : Good n K Δ) :
    (EnvTy n K).scopedB Δ = true :=
  EnvTy.scoped_of n Δ K h.bound

/-! ## Outlives: the environment outlives a fresh handler lifetime -/

/-- Data outlives every lifetime. -/
theorem VTy.outlives (A : VTy) (Δ : LifeCtx) (a : Life) : OutlivesRules Δ a A.tr := by
  induction A with
  | unit => exact .unit
  | pair A B ihA ihB => exact .tensor ihA ihB
  | sum A B ihA ihB => exact .sum ihA ihB

theorem EnvTy.outlives_of (n : Nat) (Δ : LifeCtx) (a : Life) : ∀ K,
    (∀ y, y < n + ncaps K → Δ.EntailsLt a (.var y)) → OutlivesRules Δ a (EnvTy n K)
  | [] => fun _ => .unit
  | .cap S A B :: t => fun h =>
      .tensor (.tensor (.mut (h _ (by simp [ncaps]))) .bang)
        (EnvTy.outlives_of n Δ a t (fun y hy => h y (by simp [ncaps]; omega)))
  | .blk A B :: t => fun h =>
      .tensor .bang (EnvTy.outlives_of n Δ a t (fun y hy => h y (by simpa [ncaps] using hy)))

/-- Every variable of `Δ` is at most as long-lived as `⊓Δ`, under every `δ`. -/
theorem meetOfDomL_le {δ : LSub} : ∀ (t : List (LifeVar × Life)) {y : LifeVar} {n : Nat},
    (assocFind y t).isSome = true → (meetOfDomL t).interp δ = some n →
      ∃ p, (Life.var y).interp δ = some p ∧ p ≤ n
  | [], _, _, hy, _ => by simp [assocFind] at hy
  | (x, u) :: t, y, n, hy, hm => by
      simp only [meetOfDomL] at hm
      simp only [assocFind] at hy
      by_cases hxy : x = y
      · subst hxy
        exact BoCa.Programs.interp_meet_left hm
      · rw [if_neg hxy] at hy
        obtain ⟨q, hq, hqn⟩ := BoCa.Programs.interp_meet_right hm
        obtain ⟨p, hp, hpq⟩ := meetOfDomL_le t hy hq
        exact ⟨p, hp, Nat.le_trans hpq hqn⟩

/-- The handler's fresh lifetime is strictly shorter than every lifetime of `Δ`. -/
theorem hΔ_lt {n : Nat} {K : List Entry} {Δ : LifeCtx} {y : LifeVar}
    (hy : (Δ.find? y).isSome = true) : (hΔ n K Δ).EntailsLt (.var (n + ncaps K)) (.var y) := by
  apply BoCa.Programs.entailsLt_of_bound (u := Δ.meetOfDom)
  · simp [LifeCtx.find?_extend]
  · intro δ m hm
    have hy' : (assocFind y Δ.entries).isSome = true := hy
    obtain ⟨p, hp, hle⟩ := meetOfDomL_le Δ.entries hy' hm
    refine ⟨p, ?_, hle⟩
    simp only [Life.interp] at hp ⊢
    exact hp

theorem Good.outlives {n : Nat} {K : List Entry} {Δ : LifeCtx} (h : Good n K Δ) :
    OutlivesRules (hΔ n K Δ) (.var (n + ncaps K)) (EnvTy n K) :=
  EnvTy.outlives_of n _ _ K (fun y hy => by
    have hb := h.bound y hy
    have hne : n + ncaps K ≠ y := by omega
    exact hΔ_lt (hb))

end HandlersAsBorrows.Xi
