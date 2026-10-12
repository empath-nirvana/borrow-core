import Targets.Instance.UnaryLaws

/-!
# The Instance — algebraicity's two sides, step for step

Algebraicity's two sides, `(op v to x. M) to y. N` and `op v to x. (M to y. N)`, differ in two
frames of the evaluation context: the left holds `□ to x. M` inside `□ to y. N`, the right
`□ to x. (M to y. N)`.  A catch puts the frames into the continuation it hands its clause, and from
there they go wherever the clause sends `κ`: into a finaliser, into a stored closure, into a frame.

* **The relation.**  `AlgRel M N` relates two terms equal constructor by constructor except where
  the left holds `(x to x. M) to y. N` and the right `y to x. (M to y. N)` at related `x` and `y`;
  `AlgRelK M N` relates evaluation contexts the same way, the left's two frames against the right's
  one; `AlgRelH M N` relates memories cell by cell.  With `M` and `N` closed under their binders the
  relation is kept by shifting and substitution (`AlgRel.shift`, `AlgRel.subst`), and the machine
  reads alike what it reads off a related term: a frame's handler name, what it stops and what a
  dead region keeps (`AlgRelK.hasHnd`, `AlgRelK.catches`, `AlgRelK.dead`), a clause and a tag (`clauseAt_rel`,
  `capTag_eq`), a literal (`AlgRel.host_call_eq`), and an allocation (`AlgRel.allocs_eq`).  On terms
  with no λ it is equality (`AlgRel.eq_of_lamFree`).
* **A head step** (`AlgRel.head`): at a related redex and memory the same rule steps to a related
  term and memory, every rule of Core's machine; its label agrees read without a finaliser's code,
  a cancel-mode finaliser's error agreeing when it holds no λ (`labelOf_start`).
* **A machine step** (`ostep_sim`): a step of the left is the right's step by the same rule at the
  related redex (`AlgRel.plug_inv`), except at the left's inner `x to x. M` at a value, where the
  left's β-step and the right's β-step at `y to x. (M to y. N)` both reach `M[x] to y. N`.
* **Runs** (`rstep_fwd`, `rstep_bwd`, `rpath_fwd`, `rpath_bwd`): a run of the left is matched step
  for step by a run of the right, and conversely when the left is reached by a typed program
  (`AlgGood`: closed, going on, asking the runner at arguments with no λ, keeping errors with no λ,
  answering terms with no λ) — the left's step is the right's by Core's unique decomposition and
  determinism, an allocation taken at the right's location.
* **Algebraicity** (`algLaw_of_good`): at every typing system whose typed programs' runs are
  `AlgGood`, the two sides' complete runs show the same answers and traces read without a
  finaliser's code.  `KeptLamFree` (every error a typed program's run keeps holds no λ) is what
  gives `AlgGood`'s errors at `J₁` (`Targets/I/AlgJ1.lean`).

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa clauseAt errNext errVal capTag kappaAt kappaC kappaCell kappaCBody
  freeE stuckE)

/-! ### The relation -/

section Rel
variable (M N : Expr)

/-- **Terms that differ only at algebraicity's two sides**: constructor by constructor, but where
the left holds `(x to x. M) to y. N` the right may hold `y to x. (M to y. N)`, at related `x` and
`y` (`bindE (bindE x M) N` and `bindE y (bindE M N)`). -/
inductive AlgRel : Expr → Expr → Prop
  | var (i : ℕ) : AlgRel (.var i) (.var i)
  | unit : AlgRel .unit .unit
  | pair {a b a' b' : Expr} : AlgRel a a' → AlgRel b b' → AlgRel (.pair a b) (.pair a' b')
  | inj₁ {a a' : Expr} : AlgRel a a' → AlgRel (.inj₁ a) (.inj₁ a')
  | inj₂ {a a' : Expr} : AlgRel a a' → AlgRel (.inj₂ a) (.inj₂ a')
  | lam {b b' : Expr} : AlgRel b b' → AlgRel (.lam b) (.lam b')
  | loc (ℓ : Loc) : AlgRel (.loc ℓ) (.loc ℓ)
  | prim (p : Prim) : AlgRel (.prim p) (.prim p)
  | seq {a b a' b' : Expr} : AlgRel a a' → AlgRel b b' → AlgRel (.seq a b) (.seq a' b')
  | letpair {a b a' b' : Expr} : AlgRel a a' → AlgRel b b' →
      AlgRel (.letpair a b) (.letpair a' b')
  | case {a b c a' b' c' : Expr} : AlgRel a a' → AlgRel b b' → AlgRel c c' →
      AlgRel (.case a b c) (.case a' b' c')
  | app {f a f' a' : Expr} : AlgRel f f' → AlgRel a a' → AlgRel (.app f a) (.app f' a')
  | alg {x y : Expr} : AlgRel x y →
      AlgRel (.app (.lam N) (.app (.lam M) x)) (.app (.lam (.app (.lam N) M)) y)

/-- Evaluation contexts that differ only at algebraicity's frames: the left's `□ to x. M` inside
`□ to y. N` against the right's `□ to x. (M to y. N)`. -/
inductive AlgRelK : Kont → Kont → Prop
  | hole : AlgRelK .hole .hole
  | pairL {K K' : Kont} {e e' : Expr} : AlgRelK K K' → AlgRel M N e e' →
      AlgRelK (.pairL K e) (.pairL K' e')
  | pairR {v v' : Val} {K K' : Kont} : AlgRel M N v.1 v'.1 → AlgRelK K K' →
      AlgRelK (.pairR v K) (.pairR v' K')
  | letpair {K K' : Kont} {e e' : Expr} : AlgRelK K K' → AlgRel M N e e' →
      AlgRelK (.letpair K e) (.letpair K' e')
  | case {K K' : Kont} {e₁ e₂ e₁' e₂' : Expr} : AlgRelK K K' → AlgRel M N e₁ e₁' →
      AlgRel M N e₂ e₂' → AlgRelK (.case K e₁ e₂) (.case K' e₁' e₂')
  | appR {f f' : Expr} {K K' : Kont} : AlgRel M N f f' → AlgRelK K K' →
      AlgRelK (.appR f K) (.appR f' K')
  | appL {K K' : Kont} {v v' : Val} : AlgRelK K K' → AlgRel M N v.1 v'.1 →
      AlgRelK (.appL K v) (.appL K' v')
  | seq {K K' : Kont} {e e' : Expr} : AlgRelK K K' → AlgRel M N e e' →
      AlgRelK (.seq K e) (.seq K' e')
  | inj₁ {K K' : Kont} : AlgRelK K K' → AlgRelK (.inj₁ K) (.inj₁ K')
  | inj₂ {K K' : Kont} : AlgRelK K K' → AlgRelK (.inj₂ K) (.inj₂ K')
  | alg {K K' : Kont} : AlgRelK K K' →
      AlgRelK (.appR (.lam N) (.appR (.lam M) K)) (.appR (.lam (.app (.lam N) M)) K')

/-- Memories that hold related values at the same locations. -/
def AlgRelH (μ ν : Heap) : Prop :=
  ∀ ℓ, (μ ℓ = none ∧ ν ℓ = none) ∨ ∃ v w : Val, μ ℓ = some v ∧ ν ℓ = some w ∧ AlgRel M N v.1 w.1

end Rel

variable {M N : Expr}

namespace AlgRel

theorem refl : ∀ e : Expr, AlgRel M N e e
  | .var i => .var i
  | .unit => .unit
  | .pair a b => .pair (refl a) (refl b)
  | .inj₁ a => .inj₁ (refl a)
  | .inj₂ a => .inj₂ (refl a)
  | .lam b => .lam (refl b)
  | .loc ℓ => .loc ℓ
  | .prim p => .prim p
  | .seq a b => .seq (refl a) (refl b)
  | .letpair a b => .letpair (refl a) (refl b)
  | .case a b c => .case (refl a) (refl b) (refl c)
  | .app f a => .app (refl f) (refl a)

/-! #### Inversions at the left's shape -/

theorem var_inv {i : ℕ} {y : Expr} (h : AlgRel M N (.var i) y) : y = .var i := by
  cases h; rfl

theorem unit_inv {y : Expr} (h : AlgRel M N .unit y) : y = .unit := by
  cases h; rfl

theorem loc_inv {ℓ : Loc} {y : Expr} (h : AlgRel M N (.loc ℓ) y) : y = .loc ℓ := by
  cases h; rfl

theorem prim_inv {p : Prim} {y : Expr} (h : AlgRel M N (.prim p) y) : y = .prim p := by
  cases h; rfl

theorem pair_inv {a b y : Expr} (h : AlgRel M N (.pair a b) y) :
    ∃ a' b', y = .pair a' b' ∧ AlgRel M N a a' ∧ AlgRel M N b b' := by
  cases h with
  | pair h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem inj₁_inv {a y : Expr} (h : AlgRel M N (.inj₁ a) y) : ∃ a', y = .inj₁ a' ∧ AlgRel M N a a' := by
  cases h with
  | inj₁ h₁ => exact ⟨_, rfl, h₁⟩

theorem inj₂_inv {a y : Expr} (h : AlgRel M N (.inj₂ a) y) : ∃ a', y = .inj₂ a' ∧ AlgRel M N a a' := by
  cases h with
  | inj₂ h₁ => exact ⟨_, rfl, h₁⟩

theorem lam_inv {b y : Expr} (h : AlgRel M N (.lam b) y) : ∃ b', y = .lam b' ∧ AlgRel M N b b' := by
  cases h with
  | lam h₁ => exact ⟨_, rfl, h₁⟩

theorem seq_inv {a b y : Expr} (h : AlgRel M N (.seq a b) y) :
    ∃ a' b', y = .seq a' b' ∧ AlgRel M N a a' ∧ AlgRel M N b b' := by
  cases h with
  | seq h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem letpair_inv {a b y : Expr} (h : AlgRel M N (.letpair a b) y) :
    ∃ a' b', y = .letpair a' b' ∧ AlgRel M N a a' ∧ AlgRel M N b b' := by
  cases h with
  | letpair h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem case_inv {a b c y : Expr} (h : AlgRel M N (.case a b c) y) :
    ∃ a' b' c', y = .case a' b' c' ∧ AlgRel M N a a' ∧ AlgRel M N b b' ∧ AlgRel M N c c' := by
  cases h with
  | case h₁ h₂ h₃ => exact ⟨_, _, _, rfl, h₁, h₂, h₃⟩

/-- An application: related part by part, or algebraicity's left side. -/
theorem app_inv {f a y : Expr} (h : AlgRel M N (.app f a) y) :
    (∃ f' a', y = .app f' a' ∧ AlgRel M N f f' ∧ AlgRel M N a a') ∨
      ∃ x y₀, f = .lam N ∧ a = .app (.lam M) x ∧ y = .app (.lam (.app (.lam N) M)) y₀ ∧
        AlgRel M N x y₀ := by
  cases h with
  | app h₁ h₂ => exact .inl ⟨_, _, rfl, h₁, h₂⟩
  | alg h₁ => exact .inr ⟨_, _, rfl, rfl, rfl, h₁⟩

/-- An application whose function is no λ: related part by part. -/
theorem app_inv_nl {f a y : Expr} (h : AlgRel M N (.app f a) y) (hf : ∀ b, f ≠ .lam b) :
    ∃ f' a', y = .app f' a' ∧ AlgRel M N f f' ∧ AlgRel M N a a' := by
  rcases app_inv h with h' | ⟨x, y₀, rfl, -⟩
  · exact h'
  · exact absurd rfl (hf N)

/-- An application whose argument is a value: related part by part. -/
theorem app_inv_val {f a y : Expr} (h : AlgRel M N (.app f a) y) (ha : IsVal a) :
    ∃ f' a', y = .app f' a' ∧ AlgRel M N f f' ∧ AlgRel M N a a' := by
  rcases app_inv h with h' | ⟨x, y₀, -, rfl, -⟩
  · exact h'
  · exact absurd ha (by simp)

/-! #### Inversions at the right's shape -/

theorem prim_inv_r {p : Prim} {x : Expr} (h : AlgRel M N x (.prim p)) : x = .prim p := by
  cases h; rfl

/-! #### Values -/

theorem isVal {a b : Expr} (h : AlgRel M N a b) (ha : IsVal a) : IsVal b := by
  induction h with
  | var => exact absurd ha (by simp)
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ ha.pair_left) (ih₂ ha.pair_right)
  | inj₁ _ ih => exact .inj₁ (ih ha.inj₁_inv)
  | inj₂ _ ih => exact .inj₂ (ih ha.inj₂_inv)
  | lam _ => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | seq => exact absurd ha (by simp)
  | letpair => exact absurd ha (by simp)
  | case => exact absurd ha (by simp)
  | app h₁ _ _ ih₂ =>
      obtain ⟨hf, ha'⟩ := isVal_app_iff.mp ha
      subst hf
      rw [prim_inv h₁]
      exact .storeV (ih₂ ha')
  | alg => exact absurd ha (by simp)

theorem isVal_left {a b : Expr} (h : AlgRel M N a b) (hb : IsVal b) : IsVal a := by
  induction h with
  | var => exact absurd hb (by simp)
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ hb.pair_left) (ih₂ hb.pair_right)
  | inj₁ _ ih => exact .inj₁ (ih hb.inj₁_inv)
  | inj₂ _ ih => exact .inj₂ (ih hb.inj₂_inv)
  | lam _ => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | seq => exact absurd hb (by simp)
  | letpair => exact absurd hb (by simp)
  | case => exact absurd hb (by simp)
  | app h₁ _ _ ih₂ =>
      obtain ⟨hf, hb'⟩ := isVal_app_iff.mp hb
      subst hf
      rw [prim_inv_r h₁]
      exact .storeV (ih₂ hb')
  | alg => exact absurd hb (by simp)

end AlgRel

/-! ### Terms with no λ: the relation is equality there -/

/-- `e` holds no λ. -/
def lamFree : Expr → Bool
  | .lam _ => false
  | .pair a b | .seq a b | .letpair a b | .app a b => lamFree a && lamFree b
  | .inj₁ a | .inj₂ a => lamFree a
  | .case a b c => lamFree a && lamFree b && lamFree c
  | _ => true

theorem AlgRel.eq_of_lamFree {a b : Expr} (h : AlgRel M N a b) (ha : lamFree a = true) : b = a := by
  induction h with
  | var | unit | loc | prim => rfl
  | pair _ _ ih₁ ih₂ | seq _ _ ih₁ ih₂ | letpair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ =>
      simp only [lamFree, Bool.and_eq_true] at ha
      rw [ih₁ ha.1, ih₂ ha.2]
  | inj₁ _ ih | inj₂ _ ih =>
      simp only [lamFree] at ha
      rw [ih ha]
  | case _ _ _ ih₁ ih₂ ih₃ =>
      simp only [lamFree, Bool.and_eq_true] at ha
      rw [ih₁ ha.1.1, ih₂ ha.1.2, ih₃ ha.2]
  | lam => simp [lamFree] at ha
  | alg => simp [lamFree] at ha

/-- A Core data value holds no λ. -/
theorem lamFree_of_dataVal : ∀ {A : VTy} {v : Val}, DataVal A v → lamFree v.1 = true
  | _, _, .unit => rfl
  | _, _, .int hv => by
      obtain ⟨c, hc⟩ := hv.val
      rw [hc]; rfl
  | _, _, .pair h₁ h₂ => by
      show lamFree (.pair _ _) = true
      simp only [lamFree, lamFree_of_dataVal h₁, lamFree_of_dataVal h₂, Bool.and_self]
  | _, _, .inj₁ h => by
      show lamFree (.inj₁ _) = true
      exact lamFree_of_dataVal h
  | _, _, .inj₂ h => by
      show lamFree (.inj₂ _) = true
      exact lamFree_of_dataVal h
  | _, _, .roll h => lamFree_of_dataVal h

/-! ### Shifting and substitution -/

section Subst
variable (hM : closedAt 1 M = true) (hN : closedAt 1 N = true)
include hM hN

theorem AlgRel.shift {a b : Expr} (h : AlgRel M N a b) (d : ℕ) :
    ∀ c, AlgRel M N (a.shift d c) (b.shift d c) := by
  induction h with
  | var i =>
      intro c
      simp only [Expr.shift]
      split_ifs <;> exact .var _
  | unit => intro c; exact .unit
  | pair _ _ ih₁ ih₂ => intro c; exact .pair (ih₁ c) (ih₂ c)
  | inj₁ _ ih => intro c; exact .inj₁ (ih c)
  | inj₂ _ ih => intro c; exact .inj₂ (ih c)
  | lam _ ih => intro c; exact .lam (ih (c + 1))
  | loc ℓ => intro c; exact .loc ℓ
  | prim p => intro c; exact .prim p
  | seq _ _ ih₁ ih₂ => intro c; exact .seq (ih₁ c) (ih₂ c)
  | letpair _ _ ih₁ ih₂ => intro c; exact .letpair (ih₁ c) (ih₂ (c + 2))
  | case _ _ _ ih₁ ih₂ ih₃ => intro c; exact .case (ih₁ c) (ih₂ (c + 1)) (ih₃ (c + 1))
  | app _ _ ih₁ ih₂ => intro c; exact .app (ih₁ c) (ih₂ c)
  | alg _ ih =>
      intro c
      simp only [Expr.shift]
      rw [shift_closedAt M d hM (by omega), shift_closedAt N d hN (by omega),
        shift_closedAt N d hN (by omega)]
      exact .alg (ih c)

theorem AlgRel.shiftV {v w : Val} (h : AlgRel M N v.1 w.1) (d c : ℕ) :
    AlgRel M N (v.shift d c).1 (w.shift d c).1 :=
  h.shift hM hN d c

theorem AlgRel.subst {a b : Expr} (h : AlgRel M N a b) :
    ∀ (j : ℕ) {s s' : Val}, AlgRel M N s.1 s'.1 → AlgRel M N (a.subst j s) (b.subst j s') := by
  induction h with
  | var i =>
      intro j s s' hs
      simp only [Expr.subst]
      split_ifs
      · exact hs
      · exact .var _
      · exact .var _
  | unit => intro j s s' _; exact .unit
  | pair _ _ ih₁ ih₂ => intro j s s' hs; exact .pair (ih₁ j hs) (ih₂ j hs)
  | inj₁ _ ih => intro j s s' hs; exact .inj₁ (ih j hs)
  | inj₂ _ ih => intro j s s' hs; exact .inj₂ (ih j hs)
  | lam _ ih => intro j s s' hs; exact .lam (ih (j + 1) (hs.shiftV hM hN 1 0))
  | loc ℓ => intro j s s' _; exact .loc ℓ
  | prim p => intro j s s' _; exact .prim p
  | seq _ _ ih₁ ih₂ => intro j s s' hs; exact .seq (ih₁ j hs) (ih₂ j hs)
  | letpair _ _ ih₁ ih₂ =>
      intro j s s' hs; exact .letpair (ih₁ j hs) (ih₂ (j + 2) (hs.shiftV hM hN 2 0))
  | case _ _ _ ih₁ ih₂ ih₃ =>
      intro j s s' hs
      exact .case (ih₁ j hs) (ih₂ (j + 1) (hs.shiftV hM hN 1 0)) (ih₃ (j + 1) (hs.shiftV hM hN 1 0))
  | app _ _ ih₁ ih₂ => intro j s s' hs; exact .app (ih₁ j hs) (ih₂ j hs)
  | alg _ ih =>
      intro j s s' hs
      simp only [Expr.subst]
      rw [subst_closedAt M _ hM (by omega), subst_closedAt N _ hN (by omega),
        subst_closedAt N _ hN (by omega), subst_closedAt M _ hM (by omega)]
      exact .alg (ih j hs)

end Subst

/-! ### Contexts -/

namespace AlgRelK

theorem refl : ∀ K : Kont, AlgRelK M N K K
  | .hole => .hole
  | .pairL K e => .pairL (refl K) (AlgRel.refl e)
  | .pairR v K => .pairR (AlgRel.refl v.1) (refl K)
  | .letpair K e => .letpair (refl K) (AlgRel.refl e)
  | .case K e₁ e₂ => .case (refl K) (AlgRel.refl e₁) (AlgRel.refl e₂)
  | .appR f K => .appR (AlgRel.refl f) (refl K)
  | .appL K v => .appL (refl K) (AlgRel.refl v.1)
  | .seq K e => .seq (refl K) (AlgRel.refl e)
  | .inj₁ K => .inj₁ (refl K)
  | .inj₂ K => .inj₂ (refl K)

theorem plug {K K' : Kont} (hK : AlgRelK M N K K') {a a' : Expr} (ha : AlgRel M N a a') :
    AlgRel M N (K.plug a) (K'.plug a') := by
  induction hK with
  | hole => exact ha
  | pairL _ he ih => exact .pair ih he
  | pairR hv _ ih => exact .pair hv ih
  | letpair _ he ih => exact .letpair ih he
  | case _ h₁ h₂ ih => exact .case ih h₁ h₂
  | appR hf _ ih => exact .app hf ih
  | appL _ hv ih => exact .app ih hv
  | seq _ he ih => exact .seq ih he
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | alg _ ih => exact .alg ih

theorem shift (hM : closedAt 1 M = true) (hN : closedAt 1 N = true) {K K' : Kont}
    (hK : AlgRelK M N K K') (d c : ℕ) : AlgRelK M N (K.shift d c) (K'.shift d c) := by
  induction hK with
  | hole => exact .hole
  | pairL _ he ih => exact .pairL ih (he.shift hM hN d c)
  | pairR hv _ ih => exact .pairR (hv.shiftV hM hN d c) ih
  | letpair _ he ih => exact .letpair ih (he.shift hM hN d (c + 2))
  | case _ he₁ he₂ ih => exact .case ih (he₁.shift hM hN d (c + 1)) (he₂.shift hM hN d (c + 1))
  | appR hf _ ih => exact .appR (hf.shift hM hN d c) ih
  | appL _ hv ih => exact .appL ih (hv.shiftV hM hN d c)
  | seq _ he ih => exact .seq ih (he.shift hM hN d c)
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | alg _ ih =>
      simp only [Kont.shift, Expr.shift]
      rw [shift_closedAt M d hM (by omega), shift_closedAt N d hN (by omega),
        shift_closedAt N d hN (by omega)]
      exact .alg ih

end AlgRelK

/-! ### Memories -/

namespace AlgRelH

theorem refl (μ : Heap) : AlgRelH M N μ μ := fun ℓ => by
  cases h : μ ℓ with
  | none => exact .inl ⟨rfl, rfl⟩
  | some v => exact .inr ⟨v, v, rfl, rfl, AlgRel.refl v.1⟩

theorem none_iff {μ ν : Heap} (h : AlgRelH M N μ ν) (ℓ : Loc) : μ ℓ = none ↔ ν ℓ = none := by
  rcases h ℓ with ⟨h₁, h₂⟩ | ⟨v, w, h₁, h₂, -⟩ <;> simp [h₁, h₂]

theorem some {μ ν : Heap} (h : AlgRelH M N μ ν) {ℓ : Loc} {v : Val} (hv : μ ℓ = some v) :
    ∃ w : Val, ν ℓ = some w ∧ AlgRel M N v.1 w.1 := by
  rcases h ℓ with ⟨h₁, -⟩ | ⟨v', w, h₁, h₂, h₃⟩
  · rw [hv] at h₁; cases h₁
  · rw [hv] at h₁; cases h₁; exact ⟨w, h₂, h₃⟩

theorem upd {μ ν : Heap} (h : AlgRelH M N μ ν) (ℓ : Loc) {v w : Val} (hvw : AlgRel M N v.1 w.1) :
    AlgRelH M N (μ.upd ℓ v) (ν.upd ℓ w) := fun k => by
  by_cases hk : k = ℓ
  · subst hk
    exact .inr ⟨v, w, Heap.upd_same _ _ _, Heap.upd_same _ _ _, hvw⟩
  · rw [Heap.upd_other hk, Heap.upd_other hk]; exact h k

theorem del {μ ν : Heap} (h : AlgRelH M N μ ν) (ℓ : Loc) : AlgRelH M N (μ.del ℓ) (ν.del ℓ) :=
  fun k => by
    by_cases hk : k = ℓ
    · subst hk
      exact .inl ⟨Heap.del_same _ _, Heap.del_same _ _⟩
    · rw [Heap.del_other hk, Heap.del_other hk]; exact h k

theorem fill {μ ν : Heap} (h : AlgRelH M N μ ν) (ℓ : Loc) (n : ℕ) (v : Val) :
    AlgRelH M N (μ.fill ℓ n v) (ν.fill ℓ n v) := fun k => by
  simp only [Heap.fill]
  split_ifs
  · exact .inr ⟨v, v, rfl, rfl, AlgRel.refl v.1⟩
  · exact h k

end AlgRelH

/-! ### Inversions at the right's shape, and applications of primitives -/

namespace AlgRel

theorem pair_inv_r {x a' b' : Expr} (h : AlgRel M N x (.pair a' b')) :
    ∃ a b, x = .pair a b ∧ AlgRel M N a a' ∧ AlgRel M N b b' := by
  cases h with
  | pair h₁ h₂ => exact ⟨_, _, rfl, h₁, h₂⟩

theorem inj₁_inv_r {x a' : Expr} (h : AlgRel M N x (.inj₁ a')) :
    ∃ a, x = .inj₁ a ∧ AlgRel M N a a' := by
  cases h with
  | inj₁ h₁ => exact ⟨_, rfl, h₁⟩

theorem inj₂_inv_r {x a' : Expr} (h : AlgRel M N x (.inj₂ a')) :
    ∃ a, x = .inj₂ a ∧ AlgRel M N a a' := by
  cases h with
  | inj₂ h₁ => exact ⟨_, rfl, h₁⟩

/-- An application on the right: related part by part, or algebraicity's right side. -/
theorem app_inv_r {x f' a' : Expr} (h : AlgRel M N x (.app f' a')) :
    (∃ f a, x = .app f a ∧ AlgRel M N f f' ∧ AlgRel M N a a') ∨
      ∃ x₀, f' = .lam (.app (.lam N) M) ∧ x = .app (.lam N) (.app (.lam M) x₀) ∧
        AlgRel M N x₀ a' := by
  cases h with
  | app h₁ h₂ => exact .inl ⟨_, _, rfl, h₁, h₂⟩
  | alg h₁ => exact .inr ⟨_, rfl, rfl, h₁⟩

theorem primApp_inv {p : Prim} {x y : Expr} (h : AlgRel M N (.app (.prim p) x) y) :
    ∃ x', y = .app (.prim p) x' ∧ AlgRel M N x x' := by
  obtain ⟨f', a', rfl, hf, ha⟩ := h.app_inv_nl (fun b hb => by cases hb)
  rw [hf.prim_inv]
  exact ⟨a', rfl, ha⟩

theorem primApp_inv_r {p : Prim} {x' y : Expr} (h : AlgRel M N y (.app (.prim p) x')) :
    ∃ x, y = .app (.prim p) x ∧ AlgRel M N x x' := by
  rcases h.app_inv_r with ⟨f, a, rfl, hf, ha⟩ | ⟨x₀, hf, -, -⟩
  · rw [hf.prim_inv_r]
    exact ⟨a, rfl, ha⟩
  · cases hf

/-- A related integer literal is the same literal. -/
theorem lit_inv {c : IntLit} {y : Expr} (h : AlgRel M N (.prim (.lit c)) y) : y = .prim (.lit c) :=
  h.prim_inv

/-- At a literal, `lit?` is the same on both sides. -/
theorem lit?_eq {a b : Expr} (h : AlgRel M N a b) : a.lit? = b.lit? := by
  cases h <;> rfl

theorem arg32?_eq {a b : Expr} (h : AlgRel M N a b) : a.arg32? = b.arg32? := by
  simp only [Expr.arg32?, h.lit?_eq]

theorem arg64?_eq {a b : Expr} (h : AlgRel M N a b) : a.arg64? = b.arg64? := by
  simp only [Expr.arg64?, h.lit?_eq]

theorem arg8?_eq {a b : Expr} (h : AlgRel M N a b) : a.arg8? = b.arg8? := by
  simp only [Expr.arg8?, h.lit?_eq]

theorem args32?_eq {a b : Expr} (h : AlgRel M N a b) : a.args32? = b.args32? := by
  cases h with
  | pair h₁ h₂ => simp only [Expr.args32?, h₁.arg32?_eq, h₂.arg32?_eq]
  | _ => rfl

theorem args64?_eq {a b : Expr} (h : AlgRel M N a b) : a.args64? = b.args64? := by
  cases h with
  | pair h₁ h₂ => simp only [Expr.args64?, h₁.arg64?_eq, h₂.arg64?_eq]
  | _ => rfl

set_option linter.unnecessarySeqFocus false in
/-- **The host step reads literals only**: at related arguments it answers alike. -/
theorem host_call_eq (H : Host) (op : HostOp) {v w : Val} (h : AlgRel M N v.1 w.1) :
    H.call op v = H.call op w := by
  cases op with
  | bin w o => cases w <;> simp only [Host.call, h.args32?_eq, h.args64?_eq]
  | div w o => cases w <;> simp only [Host.call, h.args32?_eq, h.args64?_eq]
  | un w o => cases w <;> simp only [Host.call, h.arg32?_eq, h.arg64?_eq]
  | eqz w => cases w <;> simp only [Host.call, h.arg32?_eq, h.arg64?_eq]
  | rel w o => cases w <;> simp only [Host.call, h.args32?_eq, h.args64?_eq]
  | _ => simp only [Host.call, h.arg32?_eq, h.arg64?_eq, h.arg8?_eq]

end AlgRel

/-! ### What the machine reads off a frame, a tuple or a payload -/

/-- A handler frame of name `m` on one side is one on the other. -/
theorem hndFrame_iff {f f' : Expr} (h : AlgRel M N f f') (m : UInt32) :
    (∃ x, f = .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) x)) ↔
      ∃ x', f' = .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) x') := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x₁, rfl, h₂⟩ := h.primApp_inv
    obtain ⟨a', b', rfl, h₄, -⟩ := h₂.pair_inv
    rw [h₄.lit_inv]
    exact ⟨b', rfl⟩
  · rintro ⟨x', rfl⟩
    obtain ⟨x₁, rfl, h₂⟩ := h.primApp_inv_r
    obtain ⟨a, b, rfl, h₄, -⟩ := h₂.pair_inv_r
    rw [h₄.prim_inv_r]
    exact ⟨b, rfl⟩

/-- An application of the primitive `p` on one side is one on the other. -/
theorem primAppFrame_iff {f f' : Expr} (h : AlgRel M N f f') (p : Prim) :
    (∃ x, f = .app (.prim p) x) ↔ ∃ x', f' = .app (.prim p) x' := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x₁, rfl, -⟩ := h.primApp_inv
    exact ⟨x₁, rfl⟩
  · rintro ⟨x', rfl⟩
    obtain ⟨x₁, rfl, -⟩ := h.primApp_inv_r
    exact ⟨x₁, rfl⟩

theorem primFrame_iff {f f' : Expr} (h : AlgRel M N f f') (p : Prim) : f = .prim p ↔ f' = .prim p :=
  ⟨fun h' => by subst h'; exact h.prim_inv, fun h' => by subst h'; exact h.prim_inv_r⟩

/-- A handler frame's name, read alike on both sides. -/
theorem hasHnd_frame {f f' : Expr} (h : AlgRel M N f f') (n : UInt32) {K K' : Kont}
    (hK : K.HasHnd n = K'.HasHnd n) : Kont.HasHnd n (.appR f K) = Kont.HasHnd n (.appR f' K') := by
  simp only [Kont.HasHnd, hK]
  congr 1
  split
  next m x =>
    obtain ⟨x', hx'⟩ := (hndFrame_iff h m).1 ⟨x, rfl⟩
    subst hx'
    rfl
  next hne =>
    split
    next m' x' =>
      obtain ⟨x, hx⟩ := (hndFrame_iff h m').2 ⟨x', rfl⟩
      exact absurd hx (hne m' x)
    next => rfl

/-- A frame the dead region drops, read alike on both sides. -/
theorem deadFrame_eq {f f' : Expr} (h : AlgRel M N f f') : Kont.DeadFrame f = Kont.DeadFrame f' := by
  unfold Kont.DeadFrame
  split
  next m x =>
    obtain ⟨x', hx'⟩ := (hndFrame_iff h m).1 ⟨x, rfl⟩
    subst hx'
    rfl
  next =>
    rw [(primFrame_iff h .ccatch).1 rfl]
  next h₁ h₂ =>
    split
    next m' x' =>
      obtain ⟨x, hx⟩ := (hndFrame_iff h m').2 ⟨x', rfl⟩
      exact absurd hx (h₁ m' x)
    next =>
      exact absurd ((primFrame_iff h .ccatch).2 rfl) h₂
    next => rfl

/-- What stops a raise at a frame, read alike on both sides. -/
theorem catches_frame {f f' : Expr} (h : AlgRel M N f f') (n : UInt32) {K K' : Kont}
    (hK : K.Catches n = K'.Catches n) : Kont.Catches n (.appR f K) = Kont.Catches n (.appR f' K') := by
  simp only [Kont.Catches, hK]
  congr 1
  split
  next m x =>
    obtain ⟨x', hx'⟩ := (hndFrame_iff h m).1 ⟨x, rfl⟩
    subst hx'
    rfl
  next x =>
    obtain ⟨x', hx'⟩ := (primAppFrame_iff h .ubind).1 ⟨x, rfl⟩
    subst hx'
    rfl
  next =>
    rw [(primFrame_iff h .ccatch).1 rfl]
  next x =>
    obtain ⟨x', hx'⟩ := (primAppFrame_iff h .cfin).1 ⟨x, rfl⟩
    subst hx'
    rfl
  next h₁ h₂ h₃ h₄ =>
    split
    next m' x' =>
      obtain ⟨x, hx⟩ := (hndFrame_iff h m').2 ⟨x', rfl⟩
      exact absurd hx (h₁ m' x)
    next x' =>
      obtain ⟨x, hx⟩ := (primAppFrame_iff h .ubind).2 ⟨x', rfl⟩
      exact absurd hx (h₂ x)
    next =>
      exact absurd ((primFrame_iff h .ccatch).2 rfl) h₃
    next x' =>
      obtain ⟨x, hx⟩ := (primAppFrame_iff h .cfin).2 ⟨x', rfl⟩
      exact absurd hx (h₄ x)
    next => rfl

namespace AlgRelK

theorem hasHnd {K K' : Kont} (hK : AlgRelK M N K K') (n : UInt32) : K.HasHnd n = K'.HasHnd n := by
  induction hK with
  | hole => rfl
  | appR hf _ ih => exact hasHnd_frame hf n ih
  | alg _ ih => simpa [Kont.HasHnd] using ih
  | pairL _ _ ih | pairR _ _ ih | letpair _ _ ih | case _ _ _ ih | appL _ _ ih | seq _ _ ih
  | inj₁ _ ih | inj₂ _ ih => simpa [Kont.HasHnd] using ih

theorem catches {K K' : Kont} (hK : AlgRelK M N K K') (n : UInt32) : K.Catches n = K'.Catches n := by
  induction hK with
  | hole => rfl
  | appR hf _ ih => exact catches_frame hf n ih
  | alg _ ih => simpa [Kont.Catches] using ih
  | pairL _ _ ih | pairR _ _ ih | letpair _ _ ih | case _ _ _ ih | appL _ _ ih | seq _ _ ih
  | inj₁ _ ih | inj₂ _ ih => simpa [Kont.Catches] using ih

/-- Related contexts have related dead regions. -/
theorem dead {K K' : Kont} (hK : AlgRelK M N K K') : AlgRelK M N K.dead K'.dead := by
  induction hK with
  | hole => exact .hole
  | appR hf _ ih =>
      simp only [Kont.dead, deadFrame_eq hf]
      split
      · exact ih
      · exact .appR hf ih
  | alg _ ih =>
      simp only [Kont.dead, Kont.DeadFrame, Bool.false_eq_true, ↓reduceIte]
      exact .alg ih
  | pairL _ he ih => exact .pairL ih he
  | pairR hv _ ih => exact .pairR hv ih
  | letpair _ he ih => exact .letpair ih he
  | case _ h₁ h₂ ih => exact .case ih h₁ h₂
  | appL _ hv ih => exact .appL ih hv
  | seq _ he ih => exact .seq ih he
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih

end AlgRelK

/-- A clause of related tuples: related clauses. -/
theorem clauseAt_rel : ∀ (i : ℕ) {hs hs' : Expr}, AlgRel M N hs hs' → ∀ {c : Val},
    clauseAt hs i = some c → ∃ c' : Val, clauseAt hs' i = some c' ∧ AlgRel M N c.1 c'.1
  | 0, hs, hs', h, c, hc => by
      cases h with
      | @pair a b a' b' h₁ _ =>
          simp only [clauseAt] at hc ⊢
          split_ifs at hc with ha
          cases hc
          rw [dif_pos (h₁.isVal ha)]
          exact ⟨_, rfl, h₁⟩
      | _ => simp [clauseAt] at hc
  | i + 1, hs, hs', h, c, hc => by
      cases h with
      | pair _ h₂ =>
          simp only [clauseAt] at hc ⊢
          exact clauseAt_rel i h₂ hc
      | _ => simp [clauseAt] at hc

theorem capTag_zero_prim (p : Prim) (r r' : Expr) : capTag (.pair (.prim p) r) 0 = capTag (.pair (.prim p) r') 0 := by
  cases p <;> try rfl
  rename_i c
  cases c <;> rfl

theorem capTag_succ (a r : Expr) (i : ℕ) : capTag (.pair a r) (i + 1) = capTag r i := by
  cases a <;> try rfl
  rename_i p
  cases p <;> try rfl
  rename_i c
  cases c <;> rfl

/-- The tags of related tuples agree. -/
theorem capTag_eq : ∀ (i : ℕ) {qs qs' : Expr}, AlgRel M N qs qs' → capTag qs i = capTag qs' i
  | 0, qs, qs', h => by
      cases h with
      | pair h₁ _ =>
          cases h₁ with
          | prim p => exact capTag_zero_prim p _ _
          | _ => rfl
      | _ => rfl
  | i + 1, qs, qs', h => by
      cases h with
      | pair _ h₂ => rw [capTag_succ, capTag_succ]; exact capTag_eq i h₂
      | _ => rfl

/-! ### The terms a head step builds -/

/-- Errors a cancel keeps, related. -/
inductive ErrRel (M N : Expr) : Option Val → Option Val → Prop
  | none : ErrRel M N none none
  | some {E E' : Val} : AlgRel M N E.1 E'.1 → ErrRel M N (some E) (some E')

/-- Congruence, constructor by constructor, closing with the hypotheses at hand. -/
macro "alg_cong" : tactic => `(tactic| repeat' (first
  | assumption | exact AlgRel.refl _ | apply AlgRel.pair | apply AlgRel.inj₁ | apply AlgRel.inj₂
  | apply AlgRel.lam | apply AlgRel.seq | apply AlgRel.letpair | apply AlgRel.case
  | apply AlgRel.app))

namespace AlgRel

/-- A related payload: the same name and index, a related argument. -/
theorem opPayload_inv {n i : UInt32} {v : Val} {y : Expr} (h : AlgRel M N (opPayload n i v).1 y) :
    ∃ v' : Val, y = (opPayload n i v').1 ∧ AlgRel M N v.1 v'.1 := by
  obtain ⟨a, b, rfl, ha, hb⟩ := h.pair_inv
  obtain ⟨c, d, rfl, hc, hd⟩ := hb.pair_inv
  rw [ha.lit_inv, hc.lit_inv]
  exact ⟨⟨d, hd.isVal v.2⟩, rfl, hd⟩

/-- A related handler value: the same name, related tags and clauses. -/
theorem hndVal_inv {n : UInt32} {qs hr hs : Val} {y : Expr} (h : AlgRel M N (hndVal n qs hr hs).1 y) :
    ∃ qs' hr' hs' : Val, y = (hndVal n qs' hr' hs').1 ∧ AlgRel M N qs.1 qs'.1 ∧
      AlgRel M N hr.1 hr'.1 ∧ AlgRel M N hs.1 hs'.1 := by
  obtain ⟨a, b, rfl, ha, hb⟩ := h.pair_inv
  obtain ⟨c, d, rfl, hc, hd⟩ := hb.pair_inv
  obtain ⟨e, f, rfl, he, hf⟩ := hd.pair_inv
  rw [ha.lit_inv]
  exact ⟨⟨c, hc.isVal qs.2⟩, ⟨e, he.isVal hr.2⟩, ⟨f, hf.isVal hs.2⟩, rfl, hc, he, hf⟩

/-- A related cancel payload: a related kept error. -/
theorem cancelVal_inv {err : Option Val} {y : Expr}
    (h : AlgRel M N (cancelVal err).1 y) :
    ∃ err', y = (cancelVal err').1 ∧ ErrRel M N err err' := by
  obtain ⟨v', rfl, hv⟩ := h.opPayload_inv
  cases err with
  | none =>
      obtain ⟨c, he, hc⟩ := (show AlgRel M N (.inj₁ .unit) v'.1 from hv).inj₁_inv
      rw [hc.unit_inv] at he
      refine ⟨none, ?_, .none⟩
      rw [show v' = errVal none from Subtype.ext he]
      rfl
  | some E =>
      obtain ⟨c, he, hc⟩ := (show AlgRel M N (.inj₂ E.1) v'.1 from hv).inj₂_inv
      refine ⟨some ⟨c, hc.isVal E.2⟩, ?_, .some hc⟩
      rw [show v' = errVal (some ⟨c, hc.isVal E.2⟩) from Subtype.ext he]
      rfl

end AlgRel

theorem ErrRel.next {err err' : Option Val} (h : ErrRel M N err err')
    (m j : UInt32) {w w' : Val} (hw : AlgRel M N w.1 w'.1) :
    ErrRel M N (errNext err m j w) (errNext err' m j w') := by
  cases h with
  | none =>
      show ErrRel M N (Option.some (opPayload m j w)) (Option.some (opPayload m j w'))
      refine .some ?_
      show AlgRel M N (opPayload m j w).1 (opPayload m j w').1
      simp only [opPayload, Val.pair, Val.i32]
      alg_cong
  | some hE => exact .some hE

/-- The earlier of two kept errors, related. -/
theorem ErrRel.or {e₁ e₁' e₂ e₂' : Option Val} (h₁ : ErrRel M N e₁ e₁') (h₂ : ErrRel M N e₂ e₂') :
    ErrRel M N (e₁.or e₂) (e₁'.or e₂') := by
  cases h₁ with
  | none => exact h₂
  | some hE => exact .some hE

theorem ErrRel.cancelRel {err err' : Option Val} (h : ErrRel M N err err') :
    AlgRel M N (cancelVal err).1 (cancelVal err').1 := by
  cases h with
  | none => exact AlgRel.refl _
  | some hE =>
      simp only [cancelVal, opPayload, errVal, Val.pair, Val.i32, Val.inj₂]
      alg_cong

section Builders
variable (hM : closedAt 1 M = true) (hN : closedAt 1 N = true)
include hM hN

theorem kappa_rel {H H' : Val} {K K' : Kont} (hH : AlgRel M N H.1 H'.1)
    (hK : AlgRelK M N K K') : AlgRel M N (kappa H K) (kappa H' K') := by
  have h3 := (hK.shift hM hN 3 0).plug (AlgRel.var (M := M) (N := N) 0)
  have h2 := (hK.dead.shift hM hN 2 0).plug
    (AlgRel.refl (M := M) (N := N) (raiseE (.val (cancelVal none))))
  have hH3 := hH.shiftV hM hN 3 0
  unfold kappa
  alg_cong

theorem kappaCBody_rel {aff : Bool} {H H' : Val} {K K' : Kont}
    (hH : AlgRel M N H.1 H'.1) (hK : AlgRelK M N K K') :
    AlgRel M N (kappaCBody aff H K) (kappaCBody aff H' K') := by
  have h4 := (hK.shift hM hN 4 0).plug (AlgRel.var (M := M) (N := N) 0)
  have h3 := (hK.dead.shift hM hN 3 0).plug
    (AlgRel.refl (M := M) (N := N) (raiseE (.val (cancelVal none))))
  have hH4 := hH.shiftV hM hN 4 0
  unfold kappaCBody
  cases aff <;> simp only [if_true, if_false, Bool.false_eq_true] <;> alg_cong

theorem kappaAt_rel {t : UInt32} {H H' : Val} {K K' : Kont} (hH : AlgRel M N H.1 H'.1)
    (hK : AlgRelK M N K K') : AlgRel M N (kappaAt t H K) (kappaAt t H' K') := by
  have hb₀ := kappaCBody_rel hM hN (aff := false) hH hK
  have hb₁ := kappaCBody_rel hM hN (aff := true) hH hK
  have hk := kappa_rel hM hN hH hK
  unfold kappaAt kappaCell
  split_ifs <;> alg_cong

omit hM hN in
theorem tabFill_rel {f f' : Val} (hf : AlgRel M N f.1 f'.1) (ℓ : Loc) (n : UInt32) :
    ∀ i k, AlgRel M N (tabFill f ℓ n i k) (tabFill f' ℓ n i k)
  | _, 0 => AlgRel.refl _
  | i, k + 1 => by
      have ih := tabFill_rel hf ℓ n (i + 1) k
      simp only [tabFill]
      alg_cong

omit hM hN in
theorem dropFill_rel {f f' : Val} (hf : AlgRel M N f.1 f'.1) (ℓ : Loc) :
    ∀ i k, AlgRel M N (dropFill f ℓ i k) (dropFill f' ℓ i k)
  | _, 0 => AlgRel.refl _
  | i, k + 1 => by
      have ih := dropFill_rel hf ℓ (i + 1) k
      simp only [dropFill]
      alg_cong

omit hM hN in
theorem countNext_rel {f f' s s' : Val} (hf : AlgRel M N f.1 f'.1) (hs : AlgRel M N s.1 s'.1)
    (n i : UInt32) : AlgRel M N (countNext f n i s) (countNext f' n i s') := by
  unfold countNext
  split_ifs
  · simp only [Val.pair, Val.i32]
    alg_cong
  · exact hs

theorem countTryNext_rel {f f' s s' : Val} (hf : AlgRel M N f.1 f'.1) (hs : AlgRel M N s.1 s'.1)
    (n i : UInt32) : AlgRel M N (countTryNext f n i s) (countTryNext f' n i s') := by
  have hf1 := hf.shiftV hM hN 1 0
  unfold countTryNext
  split_ifs
  · simp only [Val.pair, Val.i32]
    alg_cong
  · simp only [Val.inj₁]
    alg_cong

theorem fixSelf_rel {s s' : Val} (hs : AlgRel M N s.1 s'.1) (k : UInt32) :
    AlgRel M N (fixSelf s k).1 (fixSelf s' k).1 := by
  have hs1 := hs.shiftV hM hN 1 0
  unfold fixSelf
  split_ifs
  · exact AlgRel.refl _
  · simp only [Val.inj₂, Val.lam]
    alg_cong

theorem boundedFixNext_rel {s s' a a' : Val} (hs : AlgRel M N s.1 s'.1) (ha : AlgRel M N a.1 a'.1)
    (k : UInt32) : AlgRel M N (boundedFixNext s k a) (boundedFixNext s' k a') := by
  have hfs := fixSelf_rel hM hN hs k
  unfold boundedFixNext
  simp only [Val.pair]
  alg_cong

end Builders

/-! ### Contexts, through the relation -/

/-- What a plugged term relates to, in one disjunct of `AlgRel.plug_inv`: `y` is `K'[t']` at a
related context and term. -/
def PlugRel (M N : Expr) (K : Kont) (t y : Expr) : Prop :=
  ∃ K' t', y = K'.plug t' ∧ AlgRelK M N K K' ∧ AlgRel M N t t'

/-- The other disjunct: the hole is the left's inner `x to x. M`, under the frame `□ to y. N`, and
`y` holds the right's `y₀ to x. (M to y. N)` there. -/
def PlugAlg (M N : Expr) (K : Kont) (t y : Expr) : Prop :=
  ∃ (K₁ K₁' : Kont) (x y₀ : Expr), K = K₁.comp (bindK N) ∧ t = .app (.lam M) x ∧
    y = K₁'.plug (.app (.lam (.app (.lam N) M)) y₀) ∧ AlgRelK M N K₁ K₁' ∧ AlgRel M N x y₀

/-- **A plugged term, through the relation**: a term related to `K[t]`, `t` no value, is `K'[t']`
at a related context and term, or the hole is the left's inner `x to x. M` under `□ to y. N`. -/
theorem AlgRel.plug_inv : ∀ (K : Kont) {t y : Expr}, AlgRel M N (K.plug t) y → ¬ IsVal t →
    PlugRel M N K t y ∨ PlugAlg M N K t y
  | .hole, t, y, h, _ => .inl ⟨.hole, y, rfl, .hole, h⟩
  | .pairL K e, t, y, h, ht => by
      obtain ⟨a', b', rfl, ha, hb⟩ := h.pair_inv
      rcases AlgRel.plug_inv K ha ht with ⟨K', t', rfl, hK, htt⟩ | ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · exact .inl ⟨.pairL K' b', t', rfl, .pairL hK hb, htt⟩
      · exact .inr ⟨.pairL K₁ e, .pairL K₁' b', x, y₀, rfl, rfl, rfl, .pairL hK hb, hx⟩
  | .pairR v K, t, y, h, ht => by
      obtain ⟨a', b', rfl, ha, hb⟩ := h.pair_inv
      let v' : Val := ⟨a', ha.isVal v.2⟩
      rcases AlgRel.plug_inv K hb ht with ⟨K', t', rfl, hK, htt⟩ | ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · exact .inl ⟨.pairR v' K', t', rfl, .pairR ha hK, htt⟩
      · exact .inr ⟨.pairR v K₁, .pairR v' K₁', x, y₀, rfl, rfl, rfl, .pairR ha hK, hx⟩
  | .letpair K e, t, y, h, ht => by
      obtain ⟨a', b', rfl, ha, hb⟩ := h.letpair_inv
      rcases AlgRel.plug_inv K ha ht with ⟨K', t', rfl, hK, htt⟩ | ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · exact .inl ⟨.letpair K' b', t', rfl, .letpair hK hb, htt⟩
      · exact .inr ⟨.letpair K₁ e, .letpair K₁' b', x, y₀, rfl, rfl, rfl, .letpair hK hb, hx⟩
  | .case K e₁ e₂, t, y, h, ht => by
      obtain ⟨a', b', c', rfl, ha, hb, hc⟩ := h.case_inv
      rcases AlgRel.plug_inv K ha ht with ⟨K', t', rfl, hK, htt⟩ | ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · exact .inl ⟨.case K' b' c', t', rfl, .case hK hb hc, htt⟩
      · exact .inr ⟨.case K₁ e₁ e₂, .case K₁' b' c', x, y₀, rfl, rfl, rfl, .case hK hb hc, hx⟩
  | .seq K e, t, y, h, ht => by
      obtain ⟨a', b', rfl, ha, hb⟩ := h.seq_inv
      rcases AlgRel.plug_inv K ha ht with ⟨K', t', rfl, hK, htt⟩ | ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · exact .inl ⟨.seq K' b', t', rfl, .seq hK hb, htt⟩
      · exact .inr ⟨.seq K₁ e, .seq K₁' b', x, y₀, rfl, rfl, rfl, .seq hK hb, hx⟩
  | .inj₁ K, t, y, h, ht => by
      obtain ⟨a', rfl, ha⟩ := h.inj₁_inv
      rcases AlgRel.plug_inv K ha ht with ⟨K', t', rfl, hK, htt⟩ | ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · exact .inl ⟨.inj₁ K', t', rfl, .inj₁ hK, htt⟩
      · exact .inr ⟨.inj₁ K₁, .inj₁ K₁', x, y₀, rfl, rfl, rfl, .inj₁ hK, hx⟩
  | .inj₂ K, t, y, h, ht => by
      obtain ⟨a', rfl, ha⟩ := h.inj₂_inv
      rcases AlgRel.plug_inv K ha ht with ⟨K', t', rfl, hK, htt⟩ | ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · exact .inl ⟨.inj₂ K', t', rfl, .inj₂ hK, htt⟩
      · exact .inr ⟨.inj₂ K₁, .inj₂ K₁', x, y₀, rfl, rfl, rfl, .inj₂ hK, hx⟩
  | .appL K v, t, y, h, ht => by
      rcases h.app_inv with ⟨f', a', rfl, hf, ha⟩ | ⟨x, y₀, hf, -, -, -⟩
      · let v' : Val := ⟨a', ha.isVal v.2⟩
        rcases AlgRel.plug_inv K hf ht with ⟨K', t', rfl, hK, htt⟩ |
          ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
        · exact .inl ⟨.appL K' v', t', rfl, .appL hK ha, htt⟩
        · exact .inr ⟨.appL K₁ v, .appL K₁' v', x, y₀, rfl, rfl, rfl, .appL hK ha, hx⟩
      · exact absurd (K.isVal_of_plug (show IsVal (K.plug t) by rw [hf]; exact .lam)) ht
  | .appR f K, t, y, h, ht => by
      rcases h.app_inv with ⟨f', a', rfl, hf, ha⟩ | ⟨x, y₀, rfl, hx, rfl, hxy⟩
      · rcases AlgRel.plug_inv K ha ht with ⟨K', t', rfl, hK, htt⟩ |
          ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
        · exact .inl ⟨.appR f' K', t', rfl, .appR hf hK, htt⟩
        · exact .inr ⟨.appR f K₁, .appR f' K₁', x, y₀, rfl, rfl, rfl, .appR hf hK, hx⟩
      · cases K with
        | hole =>
            simp only [Kont.plug] at hx
            exact .inr ⟨.hole, .hole, x, y₀, rfl, hx, rfl, .hole, hxy⟩
        | appL K₂ v =>
            simp only [Kont.plug, Expr.app.injEq] at hx
            exact absurd (K₂.isVal_of_plug (show IsVal (K₂.plug t) by rw [hx.1]; exact .lam)) ht
        | appR f₂ K₂ =>
            simp only [Kont.plug, Expr.app.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            rcases AlgRel.plug_inv K₂ hxy ht with ⟨K', t', rfl, hK, htt⟩ |
              ⟨K₁, K₁', x, y₁, rfl, rfl, rfl, hK, hx⟩
            · exact .inl ⟨.appR (.lam (.app (.lam N) M)) K', t', rfl, .alg hK, htt⟩
            · exact .inr ⟨.appR (.lam N) (.appR (.lam M) K₁), .appR (.lam (.app (.lam N) M)) K₁', x,
                y₁, rfl, rfl, rfl, .alg hK, hx⟩
        | _ => simp [Kont.plug] at hx

/-! ### Redexes, through the relation -/

namespace AlgRel

/-- A primitive applied to a value. -/
theorem primVal_inv {p : Prim} {v : Val} {y : Expr} (h : AlgRel M N (.app (.prim p) v.1) y) :
    ∃ v' : Val, y = .app (.prim p) v'.1 ∧ AlgRel M N v.1 v'.1 := by
  obtain ⟨x', rfl, hx⟩ := h.primApp_inv
  exact ⟨⟨x', hx.isVal v.2⟩, rfl, hx⟩

/-- A primitive applied to a value, then to a term: `hnd H e`, `ubind ND e`, `cfin s e`. -/
theorem prim2_inv {p : Prim} {v : Val} {e y : Expr}
    (h : AlgRel M N (.app (.app (.prim p) v.1) e) y) :
    ∃ (v' : Val) (e' : Expr), y = .app (.app (.prim p) v'.1) e' ∧ AlgRel M N v.1 v'.1 ∧
      AlgRel M N e e' := by
  obtain ⟨f', e', rfl, hf, he⟩ := h.app_inv_nl (fun b hb => by cases hb)
  obtain ⟨v', rfl, hv⟩ := hf.primVal_inv
  exact ⟨v', e', rfl, hv, he⟩

/-- An operation in a context: a related context and payload. -/
theorem plugOp_inv {K : Kont} {p : Prim} (hp : p ≠ .store) {x y : Expr}
    (h : AlgRel M N (K.plug (.app (.prim p) x)) y) :
    ∃ K' x', y = K'.plug (.app (.prim p) x') ∧ AlgRelK M N K K' ∧ AlgRel M N x x' := by
  rcases h.plug_inv K (fun hv => hp (Expr.prim.inj (isVal_app_iff.mp hv).1)) with
    ⟨K', t', rfl, hK, ht⟩ | ⟨K₁, K₁', x₀, y₀, -, ht, -⟩
  · obtain ⟨x', rfl, hx⟩ := ht.primApp_inv
    exact ⟨K', x', rfl, hK, hx⟩
  · simp at ht

end AlgRel

section Head
variable (hM : closedAt 1 M = true) (hN : closedAt 1 N = true)
include hM hN

/-- **A head step, through the relation**: at a related redex and memory, the same rule steps to a
related term and memory, allocating where the given step does. -/
theorem AlgRel.head {μ μ' ν : Heap} {a a' b : Expr} (hh : Head (ℍ := ℍ) μ a μ' a')
    (hab : AlgRel M N a b) (hμ : AlgRelH M N μ ν) :
    ∃ ν' b', Head (ℍ := ℍ) ν b ν' b' ∧ AlgRel M N a' b' ∧ AlgRelH M N μ' ν' := by
  cases hh with
  | beta b₀ v =>
      obtain ⟨f', x', rfl, hf, hx⟩ := hab.app_inv_val v.2
      obtain ⟨b₀', rfl, hb⟩ := (show AlgRel M N (.lam b₀) f' from hf).lam_inv
      let v' : Val := ⟨x', hx.isVal v.2⟩
      exact ⟨ν, b₀'.subst 0 v', Head.beta ν b₀' v', hb.subst hM hN 0 hx, hμ⟩
  | alloc v ℓ hℓ =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      exact ⟨ν.upd ℓ v', .val (.loc ℓ), Head.alloc ν v' ℓ ((hμ.none_iff ℓ).1 hℓ), .loc ℓ,
        hμ.upd ℓ hv⟩
  | free ℓ v hv =>
      obtain ⟨w', rfl, hw⟩ := hab.primVal_inv (v := Val.loc ℓ)
      obtain rfl : w' = Val.loc ℓ := Subtype.ext (hw.eq_of_lamFree rfl)
      obtain ⟨w, hνw, hvw⟩ := hμ.some hv
      exact ⟨ν.del ℓ, w.1, Head.free ν ℓ w hνw, hvw, hμ.del ℓ⟩
  | load ℓ v hv =>
      obtain ⟨w', rfl, hw⟩ := hab.primVal_inv (v := Val.loc ℓ)
      obtain rfl : w' = Val.loc ℓ := Subtype.ext (hw.eq_of_lamFree rfl)
      obtain ⟨w, hνw, hvw⟩ := hμ.some hv
      exact ⟨ν, w.1, Head.load ν ℓ w hνw, hvw, hμ⟩
  | store ℓ v w hw =>
      obtain ⟨f', x', rfl, hf, hx⟩ := hab.app_inv_val v.2
      obtain ⟨l', rfl, hl⟩ := (show AlgRel M N (.app (.prim .store) (Val.loc ℓ).1) f' from hf).primVal_inv
      obtain rfl : l' = Val.loc ℓ := Subtype.ext (hl.eq_of_lamFree rfl)
      obtain ⟨w', hνw, -⟩ := hμ.some hw
      let v' : Val := ⟨x', hx.isVal v.2⟩
      exact ⟨ν.upd ℓ v', .val .unit, Head.store ν ℓ v' w' hνw, .unit, hμ.upd ℓ hx⟩
  | seq e =>
      obtain ⟨a', b', rfl, ha, hb⟩ := hab.seq_inv
      rw [ha.unit_inv]
      exact ⟨ν, b', Head.seq ν b', hb, hμ⟩
  | letpair v₁ v₂ e =>
      obtain ⟨a', b', rfl, ha, hb⟩ := hab.letpair_inv
      obtain ⟨x₁, x₂, rfl, h₁, h₂⟩ := (show AlgRel M N (.pair v₁.1 v₂.1) a' from ha).pair_inv
      let w₁ : Val := ⟨x₁, h₁.isVal v₁.2⟩
      let w₂ : Val := ⟨x₂, h₂.isVal v₂.2⟩
      exact ⟨ν, (b'.subst 0 (w₂.shift 1 0)).subst 0 w₁, Head.letpair ν w₁ w₂ b',
        (hb.subst hM hN 0 (h₂.shiftV hM hN 1 0)).subst hM hN 0 h₁, hμ⟩
  | case₁ v e₁ e₂ =>
      obtain ⟨a', b', c', rfl, ha, hb, hc⟩ := hab.case_inv
      obtain ⟨x, rfl, hx⟩ := (show AlgRel M N (.inj₁ v.1) a' from ha).inj₁_inv
      let w : Val := ⟨x, hx.isVal v.2⟩
      exact ⟨ν, b'.subst 0 w, Head.case₁ ν w b' c', hb.subst hM hN 0 hx, hμ⟩
  | case₂ v e₁ e₂ =>
      obtain ⟨a', b', c', rfl, ha, hb, hc⟩ := hab.case_inv
      obtain ⟨x, rfl, hx⟩ := (show AlgRel M N (.inj₂ v.1) a' from ha).inj₂_inv
      let w : Val := ⟨x, hx.isVal v.2⟩
      exact ⟨ν, c'.subst 0 w, Head.case₂ ν w b' c', hc.subst hM hN 0 hx, hμ⟩
  | host op v r hr =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      refine ⟨ν, r.1, Head.host ν op v' r ?_, AlgRel.refl _, hμ⟩
      rw [← hv.host_call_eq ℍ op]
      exact hr
  | tab c f ℓ hℓ =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain ⟨a₁, b₁, he, ha₁, hb₁⟩ := (show AlgRel M N (.pair (Val.i32 c).1 f.1) v'.1 from hv).pair_inv
      have ha₁' := ha₁.lit_inv
      let f' : Val := ⟨b₁, hb₁.isVal f.2⟩
      have hv' : v' = Val.pair (Val.i32 c) f' := Subtype.ext (by rw [he, ha₁']; rfl)
      subst hv'
      exact ⟨ν.fill ℓ (arrLen c).toNat .unit, tabFill f' ℓ (arrLen c) 0 (arrLen c).toNat,
        Head.tab ν c f' ℓ (fun i hi => (hμ.none_iff _).1 (hℓ i hi)),
        tabFill_rel hb₁ ℓ (arrLen c) 0 (arrLen c).toNat, hμ.fill ℓ _ _⟩
  | idx ℓ n i =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain rfl : v' = Val.pair (Val.arr ℓ n) (Val.i32 i) := Subtype.ext (hv.eq_of_lamFree rfl)
      exact ⟨ν, _, Head.idx ν ℓ n i, AlgRel.refl _, hμ⟩
  | split ℓ n i =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain rfl : v' = Val.pair (Val.arr ℓ n) (Val.i32 i) := Subtype.ext (hv.eq_of_lamFree rfl)
      exact ⟨ν, _, Head.split ν ℓ n i, AlgRel.refl _, hμ⟩
  | drop f ℓ n =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain ⟨a₁, b₁, he, ha₁, hb₁⟩ :=
        (show AlgRel M N (.pair f.1 (Val.arr ℓ n).1) v'.1 from hv).pair_inv
      have hb₁' := hb₁.eq_of_lamFree rfl
      let f' : Val := ⟨a₁, ha₁.isVal f.2⟩
      have hv' : v' = Val.pair f' (Val.arr ℓ n) := Subtype.ext (by rw [he, hb₁']; rfl)
      subst hv'
      exact ⟨ν, dropFill f' ℓ 0 n.toNat, Head.drop ν f' ℓ n, dropFill_rel ha₁ ℓ 0 n.toNat, hμ⟩
  | count f n i s =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain ⟨a₁, b₁, he, ha₁, hb₁⟩ :=
        (show AlgRel M N (.pair f.1 (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)).1) v'.1
          from hv).pair_inv
      obtain ⟨a₂, b₂, rfl, ha₂, hb₂⟩ := hb₁.pair_inv
      obtain ⟨a₃, b₃, rfl, ha₃, hb₃⟩ := hb₂.pair_inv
      have e₂ := ha₂.lit_inv
      have e₃ := ha₃.lit_inv
      subst e₂ e₃
      let f' : Val := ⟨a₁, ha₁.isVal f.2⟩
      let s' : Val := ⟨b₃, hb₃.isVal s.2⟩
      have hv' : v' = Val.pair f' (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s')) :=
        Subtype.ext he
      subst hv'
      exact ⟨ν, countNext f' n i s', Head.count ν f' n i s', countNext_rel ha₁ hb₃ n i, hμ⟩
  | countTry f n i s =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain ⟨a₁, b₁, he, ha₁, hb₁⟩ :=
        (show AlgRel M N (.pair f.1 (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)).1) v'.1
          from hv).pair_inv
      obtain ⟨a₂, b₂, rfl, ha₂, hb₂⟩ := hb₁.pair_inv
      obtain ⟨a₃, b₃, rfl, ha₃, hb₃⟩ := hb₂.pair_inv
      have e₂ := ha₂.lit_inv
      have e₃ := ha₃.lit_inv
      subst e₂ e₃
      let f' : Val := ⟨a₁, ha₁.isVal f.2⟩
      let s' : Val := ⟨b₃, hb₃.isVal s.2⟩
      have hv' : v' = Val.pair f' (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s')) :=
        Subtype.ext he
      subst hv'
      exact ⟨ν, countTryNext f' n i s', Head.countTry ν f' n i s',
        countTryNext_rel hM hN ha₁ hb₃ n i, hμ⟩
  | boundedFix s k x =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain ⟨a₁, b₁, he, ha₁, hb₁⟩ :=
        (show AlgRel M N (.pair s.1 (Val.pair (Val.i32 k) x).1) v'.1 from hv).pair_inv
      obtain ⟨a₂, b₂, rfl, ha₂, hb₂⟩ := hb₁.pair_inv
      have e₂ := ha₂.lit_inv
      subst e₂
      let s' : Val := ⟨a₁, ha₁.isVal s.2⟩
      let x' : Val := ⟨b₂, hb₂.isVal x.2⟩
      have hv' : v' = Val.pair s' (Val.pair (Val.i32 k) x') := Subtype.ext he
      subst hv'
      exact ⟨ν, boundedFixNext s' k x', Head.boundedFix ν s' k x',
        boundedFixNext_rel hM hN ha₁ hb₂ k, hμ⟩
  | hret n qs hr hs w =>
      obtain ⟨H', e', rfl, hH, he⟩ := hab.prim2_inv (p := .hnd) (v := hndVal n qs hr hs)
      obtain ⟨qs', hr', hs', hH', hqs, hhr, hhs⟩ := hH.hndVal_inv
      have : H' = hndVal n qs' hr' hs' := Subtype.ext hH'
      subst this
      let w' : Val := ⟨e', he.isVal w.2⟩
      exact ⟨ν, .app (.val hr') (.val w'), Head.hret ν n qs' hr' hs' w', .app hhr he, hμ⟩
  | hop n i qs hr hs c v K hc hK =>
      obtain ⟨H', e', rfl, hH, he⟩ := hab.prim2_inv (p := .hnd) (v := hndVal n qs hr hs)
      obtain ⟨qs', hr', hs', hH', hqs, hhr, hhs⟩ := hH.hndVal_inv
      have : H' = hndVal n qs' hr' hs' := Subtype.ext hH'
      subst this
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .perform) (opPayload n i v).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨v', rfl, hv⟩ := hx.opPayload_inv
      obtain ⟨c', hc', hcc⟩ := clauseAt_rel i.toNat hhs hc
      refine ⟨ν, _, Head.hop ν n i qs' hr' hs' c' v' K' hc' (by rw [← hK'.hasHnd]; exact hK), ?_, hμ⟩
      rw [← capTag_eq i.toNat hqs]
      have hHH : AlgRel M N (hndVal n qs hr hs).1 (hndVal n qs' hr' hs').1 := by
        simp only [hndVal, Val.pair, Val.i32]
        alg_cong
      exact .app hcc (.pair hv (kappaAt_rel hM hN hHH hK'))
  | hunwind n i qs hr hs c v K hc hK =>
      obtain ⟨H', e', rfl, hH, he⟩ := hab.prim2_inv (p := .hnd) (v := hndVal n qs hr hs)
      obtain ⟨qs', hr', hs', hH', hqs, hhr, hhs⟩ := hH.hndVal_inv
      have : H' = hndVal n qs' hr' hs' := Subtype.ext hH'
      subst this
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (opPayload n i v).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨v', rfl, hv⟩ := hx.opPayload_inv
      obtain ⟨c', hc', hcc⟩ := clauseAt_rel i.toNat hhs hc
      exact ⟨ν, _, Head.hunwind ν n i qs' hr' hs' c' v' K' hc' (by rw [← hK'.catches]; exact hK),
        .app hcc hv, hμ⟩
  | uthen N₀ D w =>
      obtain ⟨ND', e', rfl, hND, he⟩ := hab.prim2_inv (p := .ubind) (v := Val.pair N₀ D)
      obtain ⟨a₁, b₁, hND', ha₁, hb₁⟩ := (show AlgRel M N (.pair N₀.1 D.1) ND'.1 from hND).pair_inv
      let N₀' : Val := ⟨a₁, ha₁.isVal N₀.2⟩
      let D' : Val := ⟨b₁, hb₁.isVal D.2⟩
      have : ND' = Val.pair N₀' D' := Subtype.ext hND'
      subst this
      let w' : Val := ⟨e', he.isVal w.2⟩
      exact ⟨ν, .app (.val N₀') (.val w'), Head.uthen ν N₀' D' w', .app ha₁ he, hμ⟩
  | ufin N₀ D n i v K hn hK =>
      obtain ⟨ND', e', rfl, hND, he⟩ := hab.prim2_inv (p := .ubind) (v := Val.pair N₀ D)
      obtain ⟨a₁, b₁, hND', ha₁, hb₁⟩ := (show AlgRel M N (.pair N₀.1 D.1) ND'.1 from hND).pair_inv
      let N₀' : Val := ⟨a₁, ha₁.isVal N₀.2⟩
      let D' : Val := ⟨b₁, hb₁.isVal D.2⟩
      have : ND' = Val.pair N₀' D' := Subtype.ext hND'
      subst this
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (opPayload n i v).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨v', rfl, hv⟩ := hx.opPayload_inv
      refine ⟨ν, _, Head.ufin ν N₀' D' n i v' K' hn (by rw [← hK'.catches]; exact hK), ?_, hμ⟩
      have hp : AlgRel M N (opPayload n i v).1 (opPayload n i v').1 := by
        simp only [opPayload, Val.pair, Val.i32]
        alg_cong
      exact .seq (.app hb₁ .unit) (.app (.prim _) hp)
  | ufinC N₀ D err K hK =>
      obtain ⟨ND', e', rfl, hND, he⟩ := hab.prim2_inv (p := .ubind) (v := Val.pair N₀ D)
      obtain ⟨a₁, b₁, hND', ha₁, hb₁⟩ := (show AlgRel M N (.pair N₀.1 D.1) ND'.1 from hND).pair_inv
      let N₀' : Val := ⟨a₁, ha₁.isVal N₀.2⟩
      let D' : Val := ⟨b₁, hb₁.isVal D.2⟩
      have : ND' = Val.pair N₀' D' := Subtype.ext hND'
      subst this
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (cancelVal err).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨err', rfl, herr⟩ := hx.cancelVal_inv
      exact ⟨ν, _, Head.ufinC ν N₀' D' err' K' (by rw [← hK'.catches]; exact hK),
        .app (.app (.prim _) herr.cancelRel) (.app hb₁ .unit), hμ⟩
  | cfret err w =>
      obtain ⟨s', e', rfl, hs, he⟩ := hab.prim2_inv (p := .cfin) (v := cancelVal err)
      obtain ⟨err', hs', herr⟩ := hs.cancelVal_inv
      have : s' = cancelVal err' := Subtype.ext hs'
      subst this
      let w' : Val := ⟨e', he.isVal w.2⟩
      exact ⟨ν, _, Head.cfret ν err' w', .app (.prim _) herr.cancelRel, hμ⟩
  | cferr err m j w K hm hK =>
      obtain ⟨s', e', rfl, hs, he⟩ := hab.prim2_inv (p := .cfin) (v := cancelVal err)
      obtain ⟨err', hs', herr⟩ := hs.cancelVal_inv
      have : s' = cancelVal err' := Subtype.ext hs'
      subst this
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (opPayload m j w).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨w', rfl, hw⟩ := hx.opPayload_inv
      exact ⟨ν, _, Head.cferr ν err' m j w' K' hm (by rw [← hK'.catches]; exact hK),
        .app (.prim _) (herr.next m j hw).cancelRel, hμ⟩
  | cfcancel err err₂ K hK =>
      obtain ⟨s', e', rfl, hs, he⟩ := hab.prim2_inv (p := .cfin) (v := cancelVal err)
      obtain ⟨err', hs', herr⟩ := hs.cancelVal_inv
      have : s' = cancelVal err' := Subtype.ext hs'
      subst this
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (cancelVal err₂).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨err₂', rfl, herr₂⟩ := hx.cancelVal_inv
      exact ⟨ν, _, Head.cfcancel ν err' err₂' K' (by rw [← hK'.catches]; exact hK),
        .app (.prim _) (herr.or herr₂).cancelRel, hμ⟩
  | cancel K hK =>
      obtain ⟨e', rfl, he⟩ := hab.primApp_inv (p := .ccatch)
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (cancelVal none).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨err', rfl, herr⟩ := hx.cancelVal_inv
      cases herr
      exact ⟨ν, _, Head.cancel ν K' (by rw [← hK'.catches]; exact hK), .unit, hμ⟩
  | creraise E K hK =>
      obtain ⟨e', rfl, he⟩ := hab.primApp_inv (p := .ccatch)
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (cancelVal (some E)).1)) e' from
          he).plugOp_inv (by decide)
      obtain ⟨err', rfl, herr⟩ := hx.cancelVal_inv
      cases herr with
      | some hE =>
          rename_i E'
          exact ⟨ν, _, Head.creraise ν E' K' (by rw [← hK'.catches]; exact hK),
            .app (.prim _) hE, hμ⟩

end Head

/-! ### The label of a step, read without a finaliser's code -/

/-- A primitive applied twice, on one side, is one on the other. -/
theorem prim2Frame_iff {a b : Expr} (h : AlgRel M N a b) (p : Prim) :
    (∃ x e, a = .app (.app (.prim p) x) e) ↔ ∃ x e, b = .app (.app (.prim p) x) e := by
  constructor
  · rintro ⟨x, e, rfl⟩
    obtain ⟨f', e', rfl, hf, -⟩ := h.app_inv_nl (fun b hb => by cases hb)
    obtain ⟨x', rfl, -⟩ := hf.primApp_inv
    exact ⟨x', e', rfl⟩
  · rintro ⟨x', e', rfl⟩
    rcases h.app_inv_r with ⟨f, e, rfl, hf, -⟩ | ⟨x₀, hf, -, -⟩
    · obtain ⟨x, rfl, -⟩ := hf.primApp_inv_r
      exact ⟨x, e, rfl⟩
    · cases hf

/-- The redexes `labelOf` reads, read alike on both sides. -/
theorem finHead_eq {a b : Expr} (h : AlgRel M N a b) : finHead a = finHead b := by
  have hu := prim2Frame_iff h .ubind
  have hc := prim2Frame_iff h .cfin
  unfold finHead
  split
  next x e =>
    obtain ⟨x', e', rfl⟩ := hu.1 ⟨x, e, rfl⟩
    rfl
  next x e =>
    obtain ⟨x', e', rfl⟩ := hc.1 ⟨x, e, rfl⟩
    rfl
  next h₁ h₂ =>
    split
    next x' e' =>
      obtain ⟨x, e, hx⟩ := hu.2 ⟨x', e', rfl⟩
      exact absurd hx (h₁ x e)
    next x' e' =>
      obtain ⟨x, e, hx⟩ := hc.2 ⟨x', e', rfl⟩
      exact absurd hx (h₂ x e)
    next => rfl

/-- **A head step's label, through the relation, read without a finaliser's code**: a finaliser's
start on one side is one on the other, and a cancel-mode finaliser's end is the same end when the
error it raised holds no λ. -/
theorem labelOf_start {RF : RowForm} {Ξ : EffCtx} {μ μ' : Heap} {a a' b : Expr}
    (hh : Head (ℍ := ℍ) μ a μ' a') (hab : AlgRel M N a b)
    (hpay : ∀ (s : Val) (K : Kont) (m j : UInt32) (w : Val),
      a = cfinE s (K.plug (raiseE (.val (opPayload m j w)))) → K.Catches m = false →
        lamFree w.1 = true) :
    (labelOf RF Ξ a).start = (labelOf RF Ξ b).start := by
  have tau : finHead a = false → (labelOf RF Ξ a).start = (labelOf RF Ξ b).start := fun h => by
    rw [labelOf_tau_of h, labelOf_tau_of ((finHead_eq hab).symm.trans h)]
  cases hh with
  | uthen N₀ D w =>
      obtain ⟨ND', e', rfl, hND, he⟩ := hab.prim2_inv (p := .ubind) (v := Val.pair N₀ D)
      obtain ⟨a₁, b₁, hND', ha₁, hb₁⟩ := (show AlgRel M N (.pair N₀.1 D.1) ND'.1 from hND).pair_inv
      have hND'' : ND' = Val.pair ⟨a₁, ha₁.isVal N₀.2⟩ ⟨b₁, hb₁.isVal D.2⟩ := Subtype.ext hND'
      subst hND''
      rw [labelOf_uthen, show Expr.app (.app (.prim .ubind) (Val.pair ⟨a₁, ha₁.isVal N₀.2⟩
        ⟨b₁, hb₁.isVal D.2⟩).1) e' = ubindE (Val.pair ⟨a₁, ha₁.isVal N₀.2⟩ ⟨b₁, hb₁.isVal D.2⟩)
        (.val ⟨e', he.isVal w.2⟩) from rfl, labelOf_uthen]
  | ufin N₀ D n i v K hn hK =>
      obtain ⟨ND', e', rfl, hND, he⟩ := hab.prim2_inv (p := .ubind) (v := Val.pair N₀ D)
      obtain ⟨a₁, b₁, hND', ha₁, hb₁⟩ := (show AlgRel M N (.pair N₀.1 D.1) ND'.1 from hND).pair_inv
      have hND'' : ND' = Val.pair ⟨a₁, ha₁.isVal N₀.2⟩ ⟨b₁, hb₁.isVal D.2⟩ := Subtype.ext hND'
      subst hND''
      have hnv : ¬ IsVal (K.plug (raiseE (.val (opPayload n i v)))) := fun h =>
        plug_raise_ne_val K _ ⟨_, h⟩ rfl
      rw [labelOf_fire hnv, show Expr.app (.app (.prim .ubind) (Val.pair ⟨a₁, ha₁.isVal N₀.2⟩
        ⟨b₁, hb₁.isVal D.2⟩).1) e' = ubindE (Val.pair ⟨a₁, ha₁.isVal N₀.2⟩ ⟨b₁, hb₁.isVal D.2⟩) e'
        from rfl, labelOf_fire (fun h => hnv (he.isVal_left h))]
      rfl
  | ufinC N₀ D err K hK =>
      obtain ⟨ND', e', rfl, hND, he⟩ := hab.prim2_inv (p := .ubind) (v := Val.pair N₀ D)
      obtain ⟨a₁, b₁, hND', ha₁, hb₁⟩ := (show AlgRel M N (.pair N₀.1 D.1) ND'.1 from hND).pair_inv
      have hND'' : ND' = Val.pair ⟨a₁, ha₁.isVal N₀.2⟩ ⟨b₁, hb₁.isVal D.2⟩ := Subtype.ext hND'
      subst hND''
      have hnv : ¬ IsVal (K.plug (raiseE (.val (cancelVal err)))) := fun h =>
        plug_raise_ne_val K _ ⟨_, h⟩ rfl
      rw [labelOf_fire hnv, show Expr.app (.app (.prim .ubind) (Val.pair ⟨a₁, ha₁.isVal N₀.2⟩
        ⟨b₁, hb₁.isVal D.2⟩).1) e' = ubindE (Val.pair ⟨a₁, ha₁.isVal N₀.2⟩ ⟨b₁, hb₁.isVal D.2⟩) e'
        from rfl, labelOf_fire (fun h => hnv (he.isVal_left h))]
      rfl
  | cfret err w =>
      obtain ⟨s', e', rfl, hs, he⟩ := hab.prim2_inv (p := .cfin) (v := cancelVal err)
      rw [labelOf_cfret, show Expr.app (.app (.prim .cfin) s'.1) e' = cfinE s'
        (.val ⟨e', he.isVal w.2⟩) from rfl, labelOf_cfret]
  | cferr err m j w K hm hK =>
      obtain ⟨s', e', rfl, hs, he⟩ := hab.prim2_inv (p := .cfin) (v := cancelVal err)
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (opPayload m j w).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨w', rfl, hw⟩ := hx.opPayload_inv
      have hw' : w' = w := Subtype.ext (hw.eq_of_lamFree (hpay _ K m j w rfl hK))
      subst hw'
      rw [labelOf_cferr _ _ hm, show Expr.app (.app (.prim .cfin) s'.1)
        (K'.plug (.app (.prim .raise) (opPayload m j w').1)) =
        cfinE s' (K'.plug (raiseE (.val (opPayload m j w')))) from rfl, labelOf_cferr _ _ hm]
  | cfcancel err err₂ K hK =>
      obtain ⟨s', e', rfl, hs, he⟩ := hab.prim2_inv (p := .cfin) (v := cancelVal err)
      obtain ⟨K', x', rfl, hK', hx⟩ :=
        (show AlgRel M N (K.plug (.app (.prim .raise) (cancelVal err₂).1)) e' from he).plugOp_inv
          (by decide)
      obtain ⟨err₂', rfl, herr⟩ := hx.cancelVal_inv
      have hl : lamFree (errVal err₂).1 = true := hpay _ K 0 0 (errVal err₂) rfl hK
      have he₂ : err₂' = err₂ := by
        cases herr with
        | none => rfl
        | some hE =>
            rename_i E E'
            exact congrArg some (Subtype.ext (hE.eq_of_lamFree hl))
      subst he₂
      rw [labelOf_cfcancel, show Expr.app (.app (.prim .cfin) s'.1)
        (K'.plug (.app (.prim .raise) (cancelVal err₂').1)) =
        cfinE s' (K'.plug (raiseE (.val (cancelVal err₂')))) from rfl, labelOf_cfcancel]
  | _ => exact tau rfl

/-! ### A machine step, through the relation -/

section Step
variable (hM : closedAt 1 M = true) (hN : closedAt 1 N = true)
include hM hN

omit hM in
/-- `y to x. (M to y. N)` at a value: the β-step reaches `M[y] to y. N`. -/
theorem algR_beta (w : Val) :
    ((Expr.app (.lam N) M).subst 0 w) = .app (.lam N) (M.subst 0 w) := by
  simp only [Expr.subst]
  rw [subst_closedAt N _ hN (by omega)]

omit hM hN in
/-- The left's inner `x to x. M` steps only by β, at a value. -/
theorem head_lamM_inv {μ μ' : Heap} {x a' : Expr} (hh : Head (ℍ := ℍ) μ (.app (.lam M) x) μ' a') :
    ∃ w : Val, x = w.1 ∧ μ' = μ ∧ a' = M.subst 0 w := by
  generalize hX : Expr.app (.lam M) x = X at hh
  cases hh with
  | beta b v =>
      simp only [Expr.app.injEq] at hX
      obtain ⟨h₁, rfl⟩ := hX
      have : M = b := by simpa [Expr.val, Val.lam] using h₁
      subst this
      exact ⟨v, rfl, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, cfinE, ccatchE, Expr.val, Val.prim]

/-- **A labelled step, through the relation**: from related configurations, the right takes the
step the left takes, by the same rule at the related redex, with the same label read without a
finaliser's code, to related configurations.  At the left's inner `x to x. M` the right's β-step
at `y to x. (M to y. N)` reaches the same `M[x] to y. N`. -/
theorem ostep_sim {RF : RowForm} {Ξ : EffCtx} {c c' d : Heap × Expr}
    {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} (h : OStep (ℍ := ℍ) RF Ξ c ev c')
    (hμ : AlgRelH M N c.1 d.1) (he : AlgRel M N c.2 d.2)
    (hpay : ∀ (K₀ : Kont) (s : Val) (K : Kont) (m j : UInt32) (w : Val),
      c.2 = K₀.plug (cfinE s (K.plug (raiseE (.val (opPayload m j w))))) → K.Catches m = false →
        lamFree w.1 = true) :
    ∃ ev' d', OStep (ℍ := ℍ) RF Ξ d ev' d' ∧ ev.start = ev'.start ∧ AlgRelH M N c'.1 d'.1 ∧
      AlgRel M N c'.2 d'.2 := by
  obtain ⟨ν, y⟩ := d
  cases h with
  | @mach μ μ' K a a' hh =>
      simp only at hμ he hpay ⊢
      rcases he.plug_inv K hh.not_isVal with ⟨K', b, rfl, hK, hab⟩ |
        ⟨K₁, K₁', x, y₀, rfl, rfl, rfl, hK, hx⟩
      · obtain ⟨ν', b', hb, hab', hμ'⟩ := hab.head hM hN hh hμ
        refine ⟨labelOf RF Ξ b, (ν', K'.plug b'), OStep.mach hb, ?_, hμ', hK.plug hab'⟩
        exact labelOf_start hh hab (fun s K₂ m j w hs hc => hpay K s K₂ m j w (by rw [hs]) hc)
      · obtain ⟨w, rfl, rfl, rfl⟩ := head_lamM_inv hh
        let w' : Val := ⟨y₀, hx.isVal w.2⟩
        have hb := Head.beta (ℍ := ℍ) ν (.app (.lam N) M) w'
        refine ⟨_, _, OStep.mach hb, ?_, hμ, ?_⟩
        · rw [labelOf_tau_of rfl, labelOf_tau_of rfl]
        · show AlgRel M N ((K₁.comp (bindK N)).plug (M.subst 0 w)) (K₁'.plug ((Expr.app (.lam N) M).subst 0 w'))
          rw [Kont.plug_comp, algR_beta hN]
          exact hK.plug (.app (.lam (AlgRel.refl N)) ((AlgRel.refl M).subst hM hN 0 hx))
  | @again μ l =>
      simp only at hμ he ⊢
      obtain ⟨f', a', rfl, hf, ha⟩ := (show AlgRel M N (.app driveMark (.inj₂ l.1)) y from he).app_inv_nl
        (fun b hb => by cases hb)
      have hf' : f' = driveMark := hf.prim_inv
      subst hf'
      obtain ⟨x, rfl, hx⟩ := ha.inj₂_inv
      let l' : Val := ⟨x, hx.isVal l.2⟩
      refine ⟨.top, (ν, driveE (nextE l')), OStep.again (l := l'), rfl, hμ, ?_⟩
      exact .app (.prim _) (.app hx (AlgRel.refl _))
  | @fin μ a =>
      simp only at hμ he ⊢
      obtain ⟨f', a', rfl, hf, ha⟩ := (show AlgRel M N (.app driveMark (.inj₁ a.1)) y from he).app_inv_nl
        (fun b hb => by cases hb)
      have hf' : f' = driveMark := hf.prim_inv
      subst hf'
      obtain ⟨x, rfl, hx⟩ := ha.inj₁_inv
      let a' : Val := ⟨x, hx.isVal a.2⟩
      exact ⟨.top, (ν, a'.1), OStep.fin (a := a'), rfl, hμ, hx⟩

end Step

/-! ### Closed terms, open values, allocations -/

theorem AlgRel.closed (hM : closedAt 1 M = true) (hN : closedAt 1 N = true) {a b : Expr}
    (h : AlgRel M N a b) : ∀ k, closedAt k a = true → closedAt k b = true := by
  induction h with
  | var i => exact fun _ h => h
  | unit | loc | prim => exact fun _ _ => rfl
  | pair _ _ ih₁ ih₂ | seq _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ =>
      intro k h
      simp only [BoCa.Fig16.LogRel.Core.closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | inj₁ _ ih | inj₂ _ ih => intro k h; exact ih k h
  | lam _ ih => intro k h; exact ih (k + 1) h
  | letpair _ _ ih₁ ih₂ =>
      intro k h
      simp only [BoCa.Fig16.LogRel.Core.closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨ih₁ k h.1, ih₂ (k + 2) h.2⟩
  | case _ _ _ ih₁ ih₂ ih₃ =>
      intro k h
      simp only [BoCa.Fig16.LogRel.Core.closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨ih₁ k h.1.1, ih₂ (k + 1) h.1.2⟩, ih₃ (k + 1) h.2⟩
  | alg _ ih =>
      intro k h
      simp only [BoCa.Fig16.LogRel.Core.closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨⟨closedAt_mono N hN (by omega), closedAt_mono M hM (by omega)⟩, ih k h.2.2⟩

theorem AlgRel.isOVal_left {a b : Expr} (h : AlgRel M N a b) (hb : IsOVal b) : IsOVal a := by
  induction h with
  | var i => exact .var i
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => cases hb with | pair h₁ h₂ => exact .pair (ih₁ h₁) (ih₂ h₂)
  | inj₁ _ ih => cases hb with | inj₁ h₁ => exact .inj₁ (ih h₁)
  | inj₂ _ ih => cases hb with | inj₂ h₁ => exact .inj₂ (ih h₁)
  | lam _ => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | seq => cases hb
  | letpair => cases hb
  | case => cases hb
  | app h₁ _ _ ih₂ =>
      cases hb with
      | storeV h₂ => rw [h₁.prim_inv_r]; exact .storeV (ih₂ h₂)
  | alg => cases hb

/-- The redexes that choose a location, read alike on both sides. -/
theorem AlgRel.allocs_eq {a b : Expr} (h : AlgRel M N a b) : a.allocs = b.allocs := by
  have ha := primAppFrame_iff h .alloc
  have ht := primAppFrame_iff h .tab
  unfold Expr.allocs
  split
  next x =>
    obtain ⟨x', rfl⟩ := ha.1 ⟨x, rfl⟩
    rfl
  next x =>
    obtain ⟨x', rfl⟩ := ht.1 ⟨x, rfl⟩
    rfl
  next h₁ h₂ =>
    split
    next x' =>
      obtain ⟨x, hx⟩ := ha.2 ⟨x', rfl⟩
      exact absurd hx (h₁ x)
    next x' =>
      obtain ⟨x, hx⟩ := ht.2 ⟨x', rfl⟩
      exact absurd hx (h₂ x)
    next => rfl

/-- A payload on the right: the same name and index, a related argument. -/
theorem AlgRel.opPayload_inv_r {n i : UInt32} {v' : Val} {x : Expr}
    (h : AlgRel M N x (opPayload n i v').1) :
    ∃ v : Val, x = (opPayload n i v).1 ∧ AlgRel M N v.1 v'.1 := by
  obtain ⟨a, b, rfl, ha, hb⟩ := (show AlgRel M N x (.pair (Val.i32 n).1
    (.pair (Val.i32 i).1 v'.1)) from h).pair_inv_r
  obtain ⟨c, d, rfl, hc, hd⟩ := hb.pair_inv_r
  rw [ha.prim_inv_r, hc.prim_inv_r]
  exact ⟨⟨d, hd.isVal_left v'.2⟩, rfl, hd⟩

/-! ### Runs, through the relation -/

section Runs
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- **What algebraicity reads of the configurations of a run**: closed, going on, asking the
platform at arguments that hold no λ, keeping only errors that hold no λ at a cancel-mode
finaliser's `cfin` frame, and answering a term with no λ.  The first, second, third and fifth are
facts about the runs of typed programs (`LiveOK`, the platform's protocol, data answers); the fourth
is `KeptLamFree`. -/
structure AlgGood (R : (𝕊).Runner) (x : (𝕊).RConf R) : Prop where
  closed : closedAt 0 x.1.2 = true
  goes : GoesOn (ℍ := ℍ) RF Ξ x.1
  io : ∀ (K : Kont) (l : (RF.alg Ξ).Lab) (i : ℕ) (v : OVal),
    x.1.2 = K.plug ((𝕊).perform l i v) → K.HasHnd (RF.name Ξ l) = false → R.answers l i →
      lamFree v.1 = true
  cfin : ∀ (K₀ : Kont) (s : Val) (K : Kont) (m j : UInt32) (w : Val),
    x.1.2 = K₀.plug (cfinE s (K.plug (raiseE (.val (opPayload m j w))))) → K.Catches m = false →
      lamFree w.1 = true
  ans : IsVal x.1.2 → lamFree x.1.2 = true

/-- **No configuration a typed program reaches is at a `[cfin-raise]` step**: a finaliser a cancel
runs never lets a raise escape to its `cfin` frame.  Option A's `[then]` types a finaliser at
`F 1` (SPEC §19, decision D3: a finaliser handles its raises itself).  SPEC §27 types a finaliser
that raises to a live handler, and `J₁` takes it, so this fails at `J₁` (`not_cfinQuiet_J₁`). -/
def _root_.Targets.Inst.CfinQuiet (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ c, (ourInst (ℍ := ℍ) RF Ξ J).Live c → ¬ ∃ (K₀ : Kont) (s : Val) (K : Kont) (m j : UInt32)
    (w : Val), c.2 = K₀.plug (cfinE s (K.plug (raiseE (.val (opPayload m j w))))) ∧
      K.Catches m = false

/-- **Every error a typed program's run keeps holds no λ**: at a configuration a typed program
reaches, a raise that escapes a running finaliser to its `cfin` frame (`[cfin-raise]`) or a cancel
that passes it (`[cfin-cancel]`) carries an argument with no λ.  What `AlgGood.cfin` reads: the two
sides' kept errors are then equal terms, so their `finEnd` labels are equal. -/
def _root_.Targets.Inst.KeptLamFree (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ c, (ourInst (ℍ := ℍ) RF Ξ J).Live c → ∀ (K₀ : Kont) (s : Val) (K : Kont) (m j : UInt32)
    (w : Val), c.2 = K₀.plug (cfinE s (K.plug (raiseE (.val (opPayload m j w))))) →
      K.Catches m = false → lamFree w.1 = true

/-- A run with no `[cfin-raise]` step keeps no error. -/
theorem _root_.Targets.Inst.keptLamFree_of_cfinQuiet {RF : RowForm} {Ξ : EffCtx}
    {J : OurTyping RF} (h : Inst.CfinQuiet (ℍ := ℍ) RF Ξ J) : Inst.KeptLamFree (ℍ := ℍ) RF Ξ J :=
  fun c hc K₀ s K m j w he hK => (h c hc ⟨K₀, s, K, m, j, w, he, hK⟩).elim

variable (hM : closedAt 1 M = true) (hN : closedAt 1 N = true)
include hM hN

omit hM hN in
/-- `opArgE` at an argument with no λ holds no λ. -/
theorem lamFree_opArgE (n i : UInt32) {V : Expr} (hV : lamFree V = true) :
    lamFree (opArgE n i V) = true := by
  simp only [opArgE, lamFree, Expr.val, Val.i32, Bool.true_and, hV]

/-- **A step under the runner, through the relation**: the right takes the step the left takes,
the runner answering alike, its argument holding no λ. -/
theorem rstep_fwd (R : (𝕊).Runner) {x x' : (𝕊).RConf R} {ev : (𝕊).Event}
    (h : (𝕊).RStep R x ev x') {d : (𝕊).Conf} (hμ : AlgRelH M N x.1.1 d.1)
    (he : AlgRel M N x.1.2 d.2) (hg : AlgGood R x) :
    ∃ (ev' : (𝕊).Event) (d' : (𝕊).Conf), (𝕊).RStep R (d, x.2) ev' (d', x'.2) ∧
      ev.start = ev'.start ∧ AlgRelH M N x'.1.1 d'.1 ∧ AlgRel M N x'.1.2 d'.2 := by
  cases h with
  | mach hst =>
      obtain ⟨ev', d', hst', hev, hμ', he'⟩ := ostep_sim hM hN hst hμ he
        (fun K₀ s K m j w h₁ h₂ => hg.cfin K₀ s K m j w h₁ h₂)
      exact ⟨ev', d', .mach hst', hev, hμ', he'⟩
  | @io c s s' K l i v w hterm hK ha hco =>
      change c.2 = K.plug ((𝕊).perform l i v) at hterm
      have hlf := hg.io K l i v hterm hK ha
      have hK' : K.HasHnd (RF.name Ξ l) = false := hK
      change AlgRel M N c.2 d.2 at he
      rw [hterm] at he
      have key : ∃ K', d.2 = K'.plug ((𝕊).perform l i v) ∧ AlgRelK M N K K' := by
        rcases perform_cases (ℍ := ℍ) (J := J) l i v with ⟨-, hp⟩ | ⟨-, hp⟩
        · rw [hp] at he ⊢
          obtain ⟨K', x', hy, hKK, hx⟩ :=
            (show AlgRel M N (K.plug (.app (.prim .perform) (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)))
              d.2 from he).plugOp_inv (by decide)
          rw [hx.eq_of_lamFree (lamFree_opArgE _ _ hlf)] at hy
          exact ⟨K', hy, hKK⟩
        · rw [hp] at he ⊢
          obtain ⟨K', x', hy, hKK, hx⟩ :=
            (show AlgRel M N (K.plug (.app (.prim .perform) (.var 0))) d.2 from he).plugOp_inv
              (by decide)
          rw [hx.var_inv] at hy
          exact ⟨K', hy, hKK⟩
      obtain ⟨K', hy, hKK⟩ := key
      refine ⟨.io l i v w, (d.1, K'.plug w.1), ?_, rfl, hμ, hKK.plug (AlgRel.refl _)⟩
      have hK'' : K'.HasHnd (RF.name Ξ l) = false := by rw [← hKK.hasHnd]; exact hK'
      exact A.EffectSystem.RStep.io (K := K') (c := d) hy hK'' ha hco

omit hM hN in
/-- **An allocating step, back to the left, at the right's location.** -/
theorem AlgRel.head_back_alloc {μ ν ν' μ₀ : Heap} {a b b' a₀ : Expr} (hab : AlgRel M N a b)
    (hμ : AlgRelH M N μ ν) (ha : a.allocs = true) (hb : Head (ℍ := ℍ) ν b ν' b')
    (hh : Head (ℍ := ℍ) μ a μ₀ a₀) :
    ∃ μ₁ a₁, Head (ℍ := ℍ) μ a μ₁ a₁ ∧ AlgRel M N a₁ b' ∧ AlgRelH M N μ₁ ν' := by
  cases hh with
  | alloc v ℓ₀ _ =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain ⟨ℓ, hνℓ, rfl, rfl⟩ := head_alloc_inv hb
      exact ⟨μ.upd ℓ v, .val (.loc ℓ), Head.alloc μ v ℓ ((hμ.none_iff ℓ).2 hνℓ), .loc ℓ,
        hμ.upd ℓ hv⟩
  | tab c f ℓ₀ _ =>
      obtain ⟨v', rfl, hv⟩ := hab.primVal_inv
      obtain ⟨a₁, b₁, he, ha₁, hb₁⟩ := (show AlgRel M N (.pair (Val.i32 c).1 f.1) v'.1 from hv).pair_inv
      have ha₁' := ha₁.lit_inv
      let f' : Val := ⟨b₁, hb₁.isVal f.2⟩
      have hv' : v' = Val.pair (Val.i32 c) f' := Subtype.ext (by rw [he, ha₁']; rfl)
      subst hv'
      obtain ⟨ℓ, hℓ, rfl, rfl⟩ := head_tab_inv hb
      exact ⟨μ.fill ℓ (arrLen c).toNat .unit, tabFill f ℓ (arrLen c) 0 (arrLen c).toNat,
        Head.tab μ c f ℓ (fun i hi => (hμ.none_iff _).2 (hℓ i hi)),
        tabFill_rel hb₁ ℓ (arrLen c) 0 (arrLen c).toNat, hμ.fill ℓ _ _⟩
  | _ => simp [Expr.allocs, hndE, ubindE, cfinE, ccatchE] at ha

omit hM hN in
/-- A plugged operation under the relation: the right holds the same operation, at a related
payload, in a related context. -/
theorem plugOpE_rel {K : Kont} {r : Bool} {p : Val} {y : Expr}
    (h : AlgRel M N (K.plug (opE r p)) y) :
    ∃ (K' : Kont) (p' : Val), y = K'.plug (opE r p') ∧ AlgRelK M N K K' ∧ AlgRel M N p.1 p'.1 := by
  rw [opE_eq_app] at h
  obtain ⟨K', x', rfl, hK, hx⟩ :=
    (show AlgRel M N (K.plug (.app (.prim (if r then .raise else .perform)) p.1)) y from h).plugOp_inv
      (by cases r <;> decide)
  refine ⟨K', ⟨x', hx.isVal p.2⟩, ?_, hK, hx⟩
  rw [opE_eq_app]
  rfl

omit hM hN in
/-- A payload's name, through the relation. -/
theorem payloadName_rel {p p' : Val} (h : AlgRel M N p.1 p'.1) : payloadName p' = payloadName p := by
  obtain ⟨e, he⟩ := p
  obtain ⟨e', he'⟩ := p'
  simp only at h
  cases h with
  | pair h₁ _ =>
      cases h₁ with
      | prim q =>
          cases q <;> try rfl
          rename_i c
          cases c <;> rfl
      | _ => rfl
  | _ => rfl

/-- **A step of the right, back to the left**: from related configurations, the left one a run of
a typed program reaches (`AlgGood`) takes the step the right takes, with the same label read
without a finaliser's code, to related configurations.  The left goes on (`LiveOK`); its step is
the right's by the forward simulation and the machine's unique decomposition and determinism, at an
allocation re-taken at the right's location; an answer of the runner is at the same argument, which
holds no λ. -/
theorem rstep_bwd (R : (𝕊).Runner) {c d : (𝕊).Conf} {s : R.St} {y : (𝕊).RConf R}
    {ev' : (𝕊).Event} (h : (𝕊).RStep R (d, s) ev' y) (hμ : AlgRelH M N c.1 d.1)
    (he : AlgRel M N c.2 d.2) (hg : AlgGood R (c, s)) :
    ∃ (ev : (𝕊).Event) (c' : (𝕊).Conf), (𝕊).RStep R (c, s) ev (c', y.2) ∧ ev.start = ev'.start ∧
      AlgRelH M N c'.1 y.1.1 ∧ AlgRel M N c'.2 y.1.2 := by
  obtain ⟨μ, x⟩ := c
  obtain ⟨ν, z⟩ := d
  have hcl : closedAt 0 z = true := he.closed hM hN 0 hg.closed
  have hpay : ∀ (K₀ : Kont) (s : Val) (K : Kont) (m j : UInt32) (w : Val),
      x = K₀.plug (cfinE s (K.plug (raiseE (.val (opPayload m j w))))) → K.Catches m = false →
        lamFree w.1 = true := hg.cfin
  -- the left goes on: no value, a step, or a stopped operation
  have hgo : GoesOn (ℍ := ℍ) RF Ξ (μ, x) := hg.goes
  cases h with
  | mach hst =>
      cases hst with
      | @mach _ ν' K₂ b₂ b₂' hb =>
          simp only at hμ he hcl ⊢
          rcases hgo with ⟨w, hw⟩ | ⟨ev₀, c₀, hst₀⟩ | ⟨r, K, p, n, hx, hp, hK⟩
          · exfalso
            simp only at hw
            subst hw
            exact hb.not_isVal (K₂.isVal_of_plug (he.isVal w.2))
          · cases hst₀ with
            | @mach _ μ₀ K a a₀ hh =>
                rcases he.plug_inv K hh.not_isVal with ⟨K', b, hz, hK, hab⟩ |
                  ⟨K₁, K₁', x₀, y₀, rfl, rfl, hz, hK, hxy⟩
                · obtain ⟨ν₁, b₁, hb₁, hab₁, hμ₁⟩ := hab.head hM hN hh hμ
                  obtain ⟨rfl, rfl⟩ := plug_decomp hb₁ K₂ K' hb hz
                  cases hal : b₂.allocs with
                  | false =>
                      obtain ⟨rfl, rfl⟩ := head_det hb₁ hal hb rfl
                      exact ⟨_, _, .mach (OStep.mach hh), labelOf_start hh hab
                        (fun s K₃ m j w hs hc => hpay K s K₃ m j w (by rw [hs]) hc), hμ₁,
                        hK.plug hab₁⟩
                  | true =>
                      obtain ⟨μ₁, a₁, hh₁, hab₁', hμ₁'⟩ :=
                        hab.head_back_alloc hμ (by rw [hab.allocs_eq]; exact hal) hb hh
                      exact ⟨_, _, .mach (OStep.mach hh₁), labelOf_start hh₁ hab
                        (fun s K₃ m j w hs hc => hpay K s K₃ m j w (by rw [hs]) hc), hμ₁',
                        hK.plug hab₁'⟩
                · obtain ⟨w, rfl, rfl, rfl⟩ := head_lamM_inv hh
                  let w' : Val := ⟨y₀, hxy.isVal w.2⟩
                  have hβ := Head.beta (ℍ := ℍ) ν (.app (.lam N) M) w'
                  obtain ⟨rfl, rfl⟩ := plug_decomp hβ K₂ K₁' hb hz
                  obtain ⟨rfl, rfl⟩ := head_det hβ rfl hb rfl
                  refine ⟨_, _, .mach (OStep.mach hh), ?_, hμ, ?_⟩
                  · rw [labelOf_tau_of rfl, labelOf_tau_of rfl]
                  · show AlgRel M N ((K₁.comp (bindK N)).plug (M.subst 0 w))
                      (K₁'.plug ((Expr.app (.lam N) M).subst 0 w'))
                    rw [Kont.plug_comp, algR_beta hN]
                    exact hK.plug (.app (.lam (AlgRel.refl N)) ((AlgRel.refl M).subst hM hN 0 hxy))
            | @again _ l =>
                exfalso
                obtain ⟨f', a', hz, hf, ha⟩ :=
                  (show AlgRel M N (.app driveMark (.inj₂ l.1)) (K₂.plug b₂) from he).app_inv_nl
                    (fun b hb => by cases hb)
                rw [hf.prim_inv] at hz
                obtain ⟨q, rfl, hq⟩ := ha.inj₂_inv
                exact no_step1_drive (Val.inj₂ ⟨q, hq.isVal l.2⟩) ⟨K₂, b₂, b₂', hz.symm, rfl, hb⟩
            | @fin _ a =>
                exfalso
                obtain ⟨f', a', hz, hf, ha⟩ :=
                  (show AlgRel M N (.app driveMark (.inj₁ a.1)) (K₂.plug b₂) from he).app_inv_nl
                    (fun b hb => by cases hb)
                rw [hf.prim_inv] at hz
                obtain ⟨q, rfl, hq⟩ := ha.inj₁_inv
                exact no_step1_drive (Val.inj₁ ⟨q, hq.isVal a.2⟩) ⟨K₂, b₂, b₂', hz.symm, rfl, hb⟩
          · exfalso
            simp only at hx
            subst hx
            obtain ⟨K', p', hz, hKK, hpp⟩ := plugOpE_rel he
            have hK' : OpFree r n K' := by
              cases r
              · simp only [OpFree] at hK ⊢; rw [← hKK.hasHnd]; exact hK
              · simp only [OpFree] at hK ⊢; rw [← hKK.catches]; exact hK
            exact opPlug_no_step (by rw [payloadName_rel hpp]; exact hp) hK'
              (⟨K₂, b₂, b₂', hz.symm, rfl, hb⟩ : Step1 (ℍ := ℍ) ν (K'.plug (opE r p')) ν' (K₂.plug b₂'))
      | @again _ l =>
          simp only at hμ he ⊢
          rcases (show AlgRel M N x (.app driveMark (.inj₂ l.1)) from he).app_inv_r with
            ⟨f, a, rfl, hf, ha⟩ | ⟨x₀, hf, -, -⟩
          · rw [hf.prim_inv_r]
            obtain ⟨q, rfl, hq⟩ := ha.inj₂_inv_r
            let l₀ : Val := ⟨q, hq.isVal_left l.2⟩
            exact ⟨.top, (μ, driveE (nextE l₀)), .mach (OStep.again (l := l₀)), rfl, hμ,
              .app (.prim _) (.app hq (AlgRel.refl _))⟩
          · cases hf
      | @fin _ a =>
          simp only at hμ he ⊢
          rcases (show AlgRel M N x (.app driveMark (.inj₁ a.1)) from he).app_inv_r with
            ⟨f, a', rfl, hf, ha⟩ | ⟨x₀, hf, -, -⟩
          · rw [hf.prim_inv_r]
            obtain ⟨q, rfl, hq⟩ := ha.inj₁_inv_r
            let a₀ : Val := ⟨q, hq.isVal_left a.2⟩
            exact ⟨.top, (μ, a₀.1), .mach (OStep.fin (a := a₀)), rfl, hμ, hq⟩
          · cases hf
  | @io _ _ s' K' l i v' w hterm hK ha hco =>
      change z = K'.plug ((𝕊).perform l i v') at hterm
      simp only at hμ he hcl ⊢
      have hK₀ : K'.HasHnd (RF.name Ξ l) = false := hK
      rcases hgo with ⟨w₀, hw⟩ | ⟨ev₀, c₀, hst₀⟩ | ⟨r, K, p, n, hx, hp, hKf⟩
      · exfalso
        simp only at hw
        subst hw
        obtain ⟨q, hq⟩ := perform_app (ℍ := ℍ) (J := J) l i v'
        have hv := K'.isVal_of_plug (show IsVal (K'.plug ((𝕊).perform l i v')) by
          rw [← hterm]; exact he.isVal w₀.2)
        rw [hq] at hv
        cases hv
      · exfalso
        obtain ⟨ev₁, d₁, hst₁, -, -, -⟩ := ostep_sim (d := (ν, z)) hM hN hst₀ hμ he hpay
        cases hst₁ with
        | @mach _ _ K₃ b₃ b₃' hb₃ =>
            exact no_io_of_step1 (J := J) ⟨K₃, b₃, b₃', rfl, rfl, hb₃⟩ K' l i v' hterm hK₀
        | @again _ l₁ =>
            obtain ⟨q, hq⟩ := perform_app (ℍ := ℍ) (J := J) l i v'
            obtain ⟨K'', -, hl⟩ := plug_eq_driveE hterm.symm (by rw [hq]; intro h; cases h)
              (by rw [hq]; intro b h; cases h)
            have : IsVal (K''.plug ((𝕊).perform l i v')) := by rw [← hl]; exact (Val.inj₂ l₁).2
            rw [hq] at this
            exact absurd (K''.isVal_of_plug this) (by intro h; cases h)
        | @fin _ a₁ =>
            obtain ⟨q, hq⟩ := perform_app (ℍ := ℍ) (J := J) l i v'
            obtain ⟨K'', -, hl⟩ := plug_eq_driveE hterm.symm (by rw [hq]; intro h; cases h)
              (by rw [hq]; intro b h; cases h)
            have : IsVal (K''.plug ((𝕊).perform l i v')) := by rw [← hl]; exact (Val.inj₁ a₁).2
            rw [hq] at this
            exact absurd (K''.isVal_of_plug this) (by intro h; cases h)
      · simp only at hx
        subst hx
        obtain ⟨K'', p', hz, hKK, hpp⟩ := plugOpE_rel he
        rcases perform_cases (ℍ := ℍ) (J := J) l i v' with ⟨hi, hpe⟩ | ⟨-, hpe⟩
        swap
        · exfalso
          have h0 : closedAt 0 (Kont.plug (K' : Kont) (opJunk false)) = false := not_closed_opJunk K' false
          rw [hterm, hpe] at hcl
          exact absurd (h0.symm.trans hcl) Bool.false_ne_true
        have hvcl : closedAt 0 v'.1 = true := by
          rw [hterm, hpe] at hcl
          have := closedAt_plug_inv K' hcl
          simp only [performE, opArgE, BoCa.Fig16.LogRel.Core.closedAt, Expr.val, Val.prim,
            Val.i32, Bool.true_and] at this
          exact this
        have hv'v : IsVal v'.1 := isVal_of_closed_oval v'.2 hvcl
        have hz' : K'.plug (opE false (opPayload (RF.name Ξ l) (UInt32.ofNat i) ⟨v'.1, hv'v⟩)) =
            K''.plug (opE r p') := by
          rw [← hz, hterm, hpe]; rfl
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq hz'
        obtain ⟨v₀, hp₀, hv₀⟩ := hpp.opPayload_inv_r
        obtain rfl : p = opPayload (RF.name Ξ l) (UInt32.ofNat i) v₀ := Subtype.ext hp₀
        have hxv : K.plug (opE false (opPayload (RF.name Ξ l) (UInt32.ofNat i) v₀)) =
            K.plug ((𝕊).perform l i (OVal.ofVal v₀)) :=
          (congrArg (Kont.plug K) (perform_eq (ℍ := ℍ) (J := J) (l := l) (OVal.ofVal v₀) hi)).symm
        have hKl : K.HasHnd (RF.name Ξ l) = false := by rw [hKK.hasHnd]; exact hK₀
        have hlf := hg.io K l i (OVal.ofVal v₀) hxv hKl ha
        have hvv : v' = OVal.ofVal v₀ := Subtype.ext (hv₀.eq_of_lamFree hlf)
        subst hvv
        refine ⟨.io l i (OVal.ofVal v₀) w, (μ, K.plug w.1), ?_, rfl, hμ, hKK.plug (AlgRel.refl _)⟩
        exact A.EffectSystem.RStep.io (K := K) (c := (μ, _)) hxv hKl ha hco

omit hM hN in
/-- One step's contribution to a trace read without a finaliser's code. -/
theorem obsStart_cons (R : (𝕊).Runner) (ev : (𝕊).Event) (c : (𝕊).RConf R)
    (q : List ((𝕊).Event × (𝕊).RConf R)) :
    (𝕊).obsStart ((ev, c) :: q) = ([ev].filter Targets.A.Ev.Obs).map A.Ev.start ++ (𝕊).obsStart q := by
  simp only [A.EffectSystem.obsStart, obs_cons, List.map_append]

omit hM hN in
theorem obsStart_step (R : (𝕊).Runner) {ev ev' : (𝕊).Event} (h : ev.start = ev'.start)
    (c c' : (𝕊).RConf R) {q q' : List ((𝕊).Event × (𝕊).RConf R)}
    (hq : (𝕊).obsStart q = (𝕊).obsStart q') :
    (𝕊).obsStart ((ev, c) :: q) = (𝕊).obsStart ((ev', c') :: q') := by
  rw [obsStart_cons, obsStart_cons, hq]
  congr 1
  simp only [List.filter_cons, List.filter_nil, A.Ev.obs_of_start_eq h]
  split <;> simp [h]

/-- **A run of the left, through the relation**: every path from a configuration whose runs are
`AlgGood` is matched, step for step, by a path of the right from a related configuration, with the
same trace read without a finaliser's code and related ends. -/
theorem rpath_fwd (R : (𝕊).Runner) :
    ∀ {x : (𝕊).RConf R} {q : List ((𝕊).Event × (𝕊).RConf R)}, (𝕊).RPath R x q →
      (∀ z, (𝕊).RReach R x z → AlgGood R z) → ∀ {d : (𝕊).Conf}, AlgRelH M N x.1.1 d.1 →
      AlgRel M N x.1.2 d.2 →
      ∃ q', (𝕊).RPath R (d, x.2) q' ∧ (𝕊).obsStart q = (𝕊).obsStart q' ∧
        AlgRelH M N ((𝕊).lastC x q).1.1 ((𝕊).lastC (d, x.2) q').1.1 ∧
        AlgRel M N ((𝕊).lastC x q).1.2 ((𝕊).lastC (d, x.2) q').1.2 ∧
        ((𝕊).lastC x q).2 = ((𝕊).lastC (d, x.2) q').2
  | _, _, .nil, _, _, hμ, he => ⟨[], .nil, rfl, hμ, he, rfl⟩
  | x, _, @A.EffectSystem.RPath.cons _ _ _ ev x' q h hp, hG, d, hμ, he => by
      obtain ⟨ev', d', h', hev, hμ', he'⟩ := rstep_fwd hM hN R h hμ he (hG x .refl)
      obtain ⟨q', hp', hobs, hμ'', he'', hs⟩ := rpath_fwd R hp
        (fun z hz => hG z (Relation.ReflTransGen.head ⟨ev, h⟩ hz)) hμ' he'
      refine ⟨(ev', (d', x'.2)) :: q', .cons h' hp', obsStart_step R hev _ _ hobs, ?_, ?_, ?_⟩
      · rw [A.EffectSystem.lastC_cons, A.EffectSystem.lastC_cons]; exact hμ''
      · rw [A.EffectSystem.lastC_cons, A.EffectSystem.lastC_cons]; exact he''
      · rw [A.EffectSystem.lastC_cons, A.EffectSystem.lastC_cons]; exact hs

/-- **A run of the right, back to the left**: every path from a configuration related to one whose
runs are `AlgGood` is matched, step for step, by a path of the left. -/
theorem rpath_bwd (R : (𝕊).Runner) :
    ∀ {y : (𝕊).RConf R} {q' : List ((𝕊).Event × (𝕊).RConf R)}, (𝕊).RPath R y q' →
      ∀ {c : (𝕊).Conf}, (∀ z, (𝕊).RReach R (c, y.2) z → AlgGood R z) →
      AlgRelH M N c.1 y.1.1 → AlgRel M N c.2 y.1.2 →
      ∃ q, (𝕊).RPath R (c, y.2) q ∧ (𝕊).obsStart q = (𝕊).obsStart q' ∧
        AlgRelH M N ((𝕊).lastC (c, y.2) q).1.1 ((𝕊).lastC y q').1.1 ∧
        AlgRel M N ((𝕊).lastC (c, y.2) q).1.2 ((𝕊).lastC y q').1.2 ∧
        ((𝕊).lastC (c, y.2) q).2 = ((𝕊).lastC y q').2
  | _, _, .nil, c, _, hμ, he => ⟨[], .nil, rfl, hμ, he, rfl⟩
  | y, _, @A.EffectSystem.RPath.cons _ _ _ ev' y' q' h hp, c, hG, hμ, he => by
      obtain ⟨ev, c', h', hev, hμ', he'⟩ := rstep_bwd hM hN R (c := c) (d := y.1) (s := y.2) h hμ he
        (hG _ .refl)
      obtain ⟨q, hp₁, hobs, hμ'', he'', hs⟩ := rpath_bwd R hp (c := c')
        (fun z hz => hG z (Relation.ReflTransGen.head ⟨ev, h'⟩ hz)) hμ' he'
      refine ⟨(ev, (c', y'.2)) :: q, .cons h' hp₁, obsStart_step R hev _ _ hobs, ?_, ?_, ?_⟩
      · rw [A.EffectSystem.lastC_cons, A.EffectSystem.lastC_cons]; exact hμ''
      · rw [A.EffectSystem.lastC_cons, A.EffectSystem.lastC_cons]; exact he''
      · rw [A.EffectSystem.lastC_cons, A.EffectSystem.lastC_cons]; exact hs

/-- **Related configurations, one whose runs are `AlgGood`, show the same complete runs**: the same
answers and the same traces read without a finaliser's code. -/
theorem obsStartFrom_iff_rel (R : (𝕊).Runner) {c d : (𝕊).Conf} {s : R.St}
    (hG : ∀ z, (𝕊).RReach R (c, s) z → AlgGood R z) (hμ : AlgRelH M N c.1 d.1)
    (he : AlgRel M N c.2 d.2) (v : OVal) (tr : List (A.Ev (RF.alg Ξ).Lab OVal Unit)) :
    (𝕊).ObsStartFrom R (c, s) v tr ↔ (𝕊).ObsStartFrom R (d, s) v tr := by
  constructor
  · rintro ⟨q, ⟨hp, -⟩, hret, rfl⟩
    obtain ⟨q', hp', hobs, -, he', -⟩ := rpath_fwd hM hN R hp hG hμ he
    have hg := hG _ (rreach_of_path hp)
    have hX : ((𝕊).lastC (c, s) q).1.2 = v.1 := hret
    have hXv : IsVal v.1 := isVal_of_closed_oval v.2 (hX ▸ hg.closed)
    have hY : ((𝕊).lastC (d, s) q').1.2 = v.1 := by
      have := he'.eq_of_lamFree (hX ▸ hg.ans (hX ▸ hXv))
      rw [this, hX]
    refine ⟨q', ⟨hp', ?_⟩, hY, hobs.symm⟩
    have hv := isVal_val (RF := RF) (Ξ := Ξ) (J := J) ((𝕊).lastC (d, s) q').1.1 ⟨v.1, hXv⟩
    have e : ((𝕊).lastC (d, s) q').1 = (((𝕊).lastC (d, s) q').1.1, v.1) := by
      rw [← hY]
      rfl
    rw [e]
    exact hv
  · rintro ⟨q', ⟨hp', -⟩, hret, rfl⟩
    obtain ⟨q, hp, hobs, -, he', -⟩ := rpath_bwd hM hN R hp' (c := c) hG hμ he
    have hg := hG _ (rreach_of_path hp)
    have hY : ((𝕊).lastC (d, s) q').1.2 = v.1 := hret
    rw [hY] at he'
    have hXo : IsOVal ((𝕊).lastC (c, s) q).1.2 := he'.isOVal_left v.2
    have hXv : IsVal ((𝕊).lastC (c, s) q).1.2 := isVal_of_closed_oval hXo hg.closed
    have hX : ((𝕊).lastC (c, s) q).1.2 = v.1 := (he'.eq_of_lamFree (hg.ans hXv)).symm
    refine ⟨q, ⟨hp, ?_⟩, hX, hobs⟩
    have hv := isVal_val (RF := RF) (Ξ := Ξ) (J := J) ((𝕊).lastC (c, s) q).1.1
      ⟨((𝕊).lastC (c, s) q).1.2, hXv⟩
    exact hv

end Runs

/-! ### Algebraicity at our instance -/

section Law
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

local notation "𝕊" => ourInst (ℍ := ℍ) RF Ξ J

/-- **Algebraicity at our instance, a finaliser's start observed but not its code**, at every
typing system whose typed programs' runs are `AlgGood`: from the configuration with the left side
in `K₀`, the run of the right side in `K₀` is the run of the left step for step (`rpath_fwd`,
`rpath_bwd`), every term along it related by `AlgRel` — the two frames `□ to x. M`, `□ to y. N`
against `□ to x. (M to y. N)`, wherever a catch puts them — so the complete runs show the same
answers and the same traces read without a finaliser's code (`obsStartFrom_iff_rel`).  `M` and
`N` are closed under their binders: the configuration is closed. -/
theorem algLaw_of_good
    (hgood : ∀ (R : (𝕊).Runner) (P : Expr) (ε : (RF.alg Ξ).Eff) (A : OVTy) (c : (𝕊).RConf R),
      R.Respects → (𝕊).DataTy A → (𝕊).der [] P ((𝕊).F ε A) → (𝕊).RReach R ((𝕊).rinit R P) c →
      AlgGood R c) :
    (𝕊).AlgLaw := by
  intro l i v o M N _ _ R hR P ε A c K₀ hA hP hreach hterm w tr
  obtain ⟨⟨μ, e⟩, s⟩ := c
  have hG : ∀ z, (𝕊).RReach R ((μ, e), s) z → AlgGood R z := fun z hz =>
    hgood R P ε A z hR hA hP (hreach.trans hz)
  have hcl := (hG _ .refl).closed
  change e = K₀.plug (bindE (bindE ((𝕊).perform l i v) M) N) at hterm
  subst hterm
  have hc := closedAt_plug_inv K₀ hcl
  simp only [bindE, BoCa.Fig16.LogRel.Core.closedAt, Expr.val, Val.lam, Bool.and_eq_true] at hc
  obtain ⟨hN, hM, -⟩ := hc
  exact obsStartFrom_iff_rel hM hN R hG (AlgRelH.refl μ)
    ((AlgRelK.refl K₀).plug (.alg (AlgRel.refl _))) w tr

end Law

end Targets.Inst

end
