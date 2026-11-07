import Support.Syntax.Terms

/-!
# Core — a code's normal form: its free variables renumbered by rank  `[spec §68]`

A code is a closure's body with its captures abstracted. `capNorm e` is `e` with its free de
Bruijn variables renumbered `0, 1, …` in increasing order (`capVars e`, sorted, without
repeats), so two closures of the same body placed at different depths have the same code.

* `capNorm_shift`: `capNorm` is invariant under `shift`, which preserves the order of the free
  variables.
* `psub_capNorm`, `lam_psub_capNorm`: a closing substitution of `e` is the code's at the
  captured values in rank order (`capEnv`), the syntactic half of `codeI`.
* `occs_capNorm_lt`: a code's free variables are below its number of captures.
-/

namespace BoCa

/-- The free variables of `e` under `k` binders, as indices counted from the binders, in
order of occurrence and with repeats. -/
def Expr.occs : Nat → Expr → List Nat
  | k, .var i         => if i < k then [] else [i - k]
  | _, .unit          => []
  | k, .pair e₁ e₂    => Expr.occs k e₁ ++ Expr.occs k e₂
  | k, .inj₁ e        => Expr.occs k e
  | k, .inj₂ e        => Expr.occs k e
  | k, .lam b         => Expr.occs (k + 1) b
  | _, .loc _         => []
  | _, .prim _        => []
  | k, .seq e₁ e₂     => Expr.occs k e₁ ++ Expr.occs k e₂
  | k, .letpair e₁ e₂ => Expr.occs k e₁ ++ Expr.occs (k + 2) e₂
  | k, .case e e₁ e₂  => Expr.occs k e ++ Expr.occs (k + 1) e₁ ++ Expr.occs (k + 1) e₂
  | k, .app f a       => Expr.occs k f ++ Expr.occs k a

/-- `e` with each free variable `i` (counted from the `k` binders) renamed to `r i`. -/
def Expr.ren (r : Nat → Nat) : Nat → Expr → Expr
  | k, .var i         => if i < k then .var i else .var (r (i - k) + k)
  | _, .unit          => .unit
  | k, .pair e₁ e₂    => .pair (Expr.ren r k e₁) (Expr.ren r k e₂)
  | k, .inj₁ e        => .inj₁ (Expr.ren r k e)
  | k, .inj₂ e        => .inj₂ (Expr.ren r k e)
  | k, .lam b         => .lam (Expr.ren r (k + 1) b)
  | _, .loc ℓ         => .loc ℓ
  | _, .prim p        => .prim p
  | k, .seq e₁ e₂     => .seq (Expr.ren r k e₁) (Expr.ren r k e₂)
  | k, .letpair e₁ e₂ => .letpair (Expr.ren r k e₁) (Expr.ren r (k + 2) e₂)
  | k, .case e e₁ e₂  =>
      .case (Expr.ren r k e) (Expr.ren r (k + 1) e₁) (Expr.ren r (k + 1) e₂)
  | k, .app f a       => .app (Expr.ren r k f) (Expr.ren r k a)

/-- Insert `x` into a sorted list without repeats. -/
def sortIns (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: sortIns x ys

/-- The captures of `e`: its free variables, sorted, without repeats.  `[spec §68]` -/
def Expr.capVars (e : Expr) : List Nat := (Expr.occs 0 e).foldr sortIns []

/-- A capture's rank: its position in `capVars`. -/
def Expr.capIdx (e : Expr) (i : Nat) : Nat := (Expr.capVars e).idxOf i

/-- **The code of `e`**: `e` with its free variables renumbered `0, 1, …` by rank.
`[spec §68]` -/
def Expr.capNorm (e : Expr) : Expr := Expr.ren (Expr.capIdx e) 0 e

/-- The captured values of a closing substitution `γ`, in rank order.  `[spec §68]` -/
def Expr.capEnv (e : Expr) (γ : List Val) : List Val :=
  (Expr.capVars e).map (fun i => γ.getD i Val.unit)

/-- The renaming a `shift d c` is. -/
def shiftIdx (d c : Nat) (i : Nat) : Nat := if i < c then i else i + d

/-- `λ. x₅ x₂ x₅` captures the free variables `1` and `4`, renumbered `0` and `1`. -/
example : Expr.capNorm (.lam (.app (.app (.var 5) (.var 2)) (.var 5))) =
    .lam (.app (.app (.var 2) (.var 1)) (.var 2)) := rfl

/-! ### Renaming -/

theorem Expr.shift_eq_ren (d c : Nat) :
    ∀ (e : Expr) (k : Nat), Expr.shift d (c + k) e = Expr.ren (shiftIdx d c) k e
  | .var i, k => by
      simp only [Expr.shift, Expr.ren, shiftIdx]
      by_cases h₁ : i < k
      · rw [if_pos (by omega), if_pos h₁]
      · rw [if_neg h₁]
        by_cases h₂ : i - k < c
        · rw [if_pos (by omega), if_pos h₂]; congr 1; omega
        · rw [if_neg (by omega), if_neg h₂]; congr 1; omega
  | .unit, _ => rfl
  | .pair a b, k => by simp only [Expr.shift, Expr.ren, Expr.shift_eq_ren d c a k,
      Expr.shift_eq_ren d c b k]
  | .inj₁ a, k => by simp only [Expr.shift, Expr.ren, Expr.shift_eq_ren d c a k]
  | .inj₂ a, k => by simp only [Expr.shift, Expr.ren, Expr.shift_eq_ren d c a k]
  | .lam b, k => by
      simp only [Expr.shift, Expr.ren, ← Expr.shift_eq_ren d c b (k + 1), Nat.add_assoc]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, k => by simp only [Expr.shift, Expr.ren, Expr.shift_eq_ren d c a k,
      Expr.shift_eq_ren d c b k]
  | .letpair a b, k => by
      simp only [Expr.shift, Expr.ren, Expr.shift_eq_ren d c a k,
        ← Expr.shift_eq_ren d c b (k + 2), Nat.add_assoc]
  | .case a b₁ b₂, k => by
      simp only [Expr.shift, Expr.ren, Expr.shift_eq_ren d c a k,
        ← Expr.shift_eq_ren d c b₁ (k + 1), ← Expr.shift_eq_ren d c b₂ (k + 1), Nat.add_assoc]
  | .app f a, k => by simp only [Expr.shift, Expr.ren, Expr.shift_eq_ren d c f k,
      Expr.shift_eq_ren d c a k]

theorem Expr.ren_ren (f g : Nat → Nat) :
    ∀ (e : Expr) (k : Nat), Expr.ren g k (Expr.ren f k e) = Expr.ren (g ∘ f) k e
  | .var i, k => by
      by_cases h : i < k
      · simp only [Expr.ren, if_pos h]
      · simp only [Expr.ren, if_neg h, if_neg (show ¬ (f (i - k) + k < k) by omega),
          Nat.add_sub_cancel, Function.comp]
  | .unit, _ => rfl
  | .pair a b, k => by simp only [Expr.ren, Expr.ren_ren f g a k, Expr.ren_ren f g b k]
  | .inj₁ a, k => by simp only [Expr.ren, Expr.ren_ren f g a k]
  | .inj₂ a, k => by simp only [Expr.ren, Expr.ren_ren f g a k]
  | .lam b, k => by simp only [Expr.ren, Expr.ren_ren f g b (k + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, k => by simp only [Expr.ren, Expr.ren_ren f g a k, Expr.ren_ren f g b k]
  | .letpair a b, k => by
      simp only [Expr.ren, Expr.ren_ren f g a k, Expr.ren_ren f g b (k + 2)]
  | .case a b₁ b₂, k => by
      simp only [Expr.ren, Expr.ren_ren f g a k, Expr.ren_ren f g b₁ (k + 1),
        Expr.ren_ren f g b₂ (k + 1)]
  | .app f' a, k => by simp only [Expr.ren, Expr.ren_ren f g f' k, Expr.ren_ren f g a k]

theorem Expr.occs_ren (f : Nat → Nat) :
    ∀ (e : Expr) (k : Nat), Expr.occs k (Expr.ren f k e) = (Expr.occs k e).map f
  | .var i, k => by
      by_cases h : i < k
      · simp only [Expr.ren, Expr.occs, if_pos h, List.map_nil]
      · simp only [Expr.ren, Expr.occs, if_neg h, if_neg (show ¬ (f (i - k) + k < k) by omega),
          Nat.add_sub_cancel, List.map_cons, List.map_nil]
  | .unit, _ => rfl
  | .pair a b, k => by simp only [Expr.ren, Expr.occs, Expr.occs_ren f a k,
      Expr.occs_ren f b k, List.map_append]
  | .inj₁ a, k => by simp only [Expr.ren, Expr.occs, Expr.occs_ren f a k]
  | .inj₂ a, k => by simp only [Expr.ren, Expr.occs, Expr.occs_ren f a k]
  | .lam b, k => by simp only [Expr.ren, Expr.occs, Expr.occs_ren f b (k + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, k => by simp only [Expr.ren, Expr.occs, Expr.occs_ren f a k,
      Expr.occs_ren f b k, List.map_append]
  | .letpair a b, k => by simp only [Expr.ren, Expr.occs, Expr.occs_ren f a k,
      Expr.occs_ren f b (k + 2), List.map_append]
  | .case a b₁ b₂, k => by
      simp only [Expr.ren, Expr.occs, Expr.occs_ren f a k, Expr.occs_ren f b₁ (k + 1),
        Expr.occs_ren f b₂ (k + 1), List.map_append]
  | .app f' a, k => by simp only [Expr.ren, Expr.occs, Expr.occs_ren f f' k,
      Expr.occs_ren f a k, List.map_append]

/-- A renaming that fixes every free variable leaves the term unchanged. -/
theorem Expr.ren_eq_self (f : Nat → Nat) :
    ∀ (e : Expr) (k : Nat), (∀ i ∈ Expr.occs k e, f i = i) → Expr.ren f k e = e
  | .var i, k, h => by
      by_cases hi : i < k
      · simp only [Expr.ren, if_pos hi]
      · have := h (i - k) (by simp [Expr.occs, hi])
        simp only [Expr.ren, if_neg hi, this]; congr 1; omega
  | .unit, _, _ => rfl
  | .pair a b, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.ren_eq_self f a k (fun i hi => h i (.inl hi)),
        Expr.ren_eq_self f b k (fun i hi => h i (.inr hi))]
  | .inj₁ a, k, h => by simp only [Expr.ren, Expr.ren_eq_self f a k h]
  | .inj₂ a, k, h => by simp only [Expr.ren, Expr.ren_eq_self f a k h]
  | .lam b, k, h => by simp only [Expr.ren, Expr.ren_eq_self f b (k + 1) h]
  | .loc _, _, _ => rfl
  | .prim _, _, _ => rfl
  | .seq a b, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.ren_eq_self f a k (fun i hi => h i (.inl hi)),
        Expr.ren_eq_self f b k (fun i hi => h i (.inr hi))]
  | .letpair a b, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.ren_eq_self f a k (fun i hi => h i (.inl hi)),
        Expr.ren_eq_self f b (k + 2) (fun i hi => h i (.inr hi))]
  | .case a b₁ b₂, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.ren_eq_self f a k (fun i hi => h i (.inl (.inl hi))),
        Expr.ren_eq_self f b₁ (k + 1) (fun i hi => h i (.inl (.inr hi))),
        Expr.ren_eq_self f b₂ (k + 1) (fun i hi => h i (.inr hi))]
  | .app f' a, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.ren_eq_self f f' k (fun i hi => h i (.inl hi)),
        Expr.ren_eq_self f a k (fun i hi => h i (.inr hi))]

/-! ### The captures under an order-preserving renaming -/

/-- `f` preserves the order strictly. -/
def StrictOrd (f : Nat → Nat) : Prop := ∀ a b, a < b → f a < f b

theorem StrictOrd.lt_iff {f : Nat → Nat} (hf : StrictOrd f) (a b : Nat) : f a < f b ↔ a < b := by
  refine ⟨fun h => ?_, hf a b⟩
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · exact hab
  · exact absurd h (Nat.lt_irrefl _)
  · exact absurd (hf b a hab) (Nat.lt_asymm h)

theorem StrictOrd.inj {f : Nat → Nat} (hf : StrictOrd f) {a b : Nat} (h : f a = f b) : a = b := by
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · exact absurd h (Nat.ne_of_lt (hf a b hab))
  · rfl
  · exact absurd h (Nat.ne_of_gt (hf b a hab))

theorem shiftIdx_strictOrd (d c : Nat) : StrictOrd (shiftIdx d c) := by
  intro a b h
  simp only [shiftIdx]
  split <;> split <;> omega

theorem sortIns_map {f : Nat → Nat} (hf : StrictOrd f) (x : Nat) :
    ∀ l : List Nat, sortIns (f x) (l.map f) = (sortIns x l).map f
  | [] => rfl
  | y :: ys => by
      simp only [List.map_cons, sortIns, hf.lt_iff]
      by_cases h₁ : x < y
      · simp only [if_pos h₁, List.map_cons]
      · by_cases h₂ : x = y
        · subst h₂; simp
        · have h₂' : f x ≠ f y := fun h => h₂ (hf.inj h)
          simp only [if_neg h₁, if_neg h₂, if_neg h₂', List.map_cons, sortIns_map hf x ys]

theorem foldr_sortIns_map {f : Nat → Nat} (hf : StrictOrd f) :
    ∀ l : List Nat, (l.map f).foldr sortIns [] = (l.foldr sortIns []).map f
  | [] => rfl
  | x :: l => by
      simp only [List.map_cons, List.foldr_cons, foldr_sortIns_map hf l, sortIns_map hf x]

theorem mem_sortIns (a x : Nat) : ∀ l : List Nat, a ∈ sortIns x l ↔ a = x ∨ a ∈ l
  | [] => by simp [sortIns]
  | y :: ys => by
      simp only [sortIns]
      split
      · simp
      · split
        · subst_vars; simp
        · simp only [List.mem_cons, mem_sortIns a x ys]; exact or_left_comm

theorem mem_foldr_sortIns (a : Nat) : ∀ l : List Nat, a ∈ l.foldr sortIns [] ↔ a ∈ l
  | [] => by simp
  | x :: l => by
      simp only [List.foldr_cons, mem_sortIns, mem_foldr_sortIns a l, List.mem_cons]

theorem Expr.mem_capVars {e : Expr} {i : Nat} : i ∈ Expr.capVars e ↔ i ∈ Expr.occs 0 e :=
  mem_foldr_sortIns i _

theorem Expr.capVars_ren {f : Nat → Nat} (hf : StrictOrd f) (e : Expr) :
    Expr.capVars (Expr.ren f 0 e) = (Expr.capVars e).map f := by
  simp only [Expr.capVars, Expr.occs_ren, foldr_sortIns_map hf]

theorem idxOf_map_of_inj {f : Nat → Nat} (hf : ∀ {a b}, f a = f b → a = b) (i : Nat) :
    ∀ l : List Nat, (l.map f).idxOf (f i) = l.idxOf i
  | [] => rfl
  | y :: ys => by
      simp only [List.map_cons, List.idxOf_cons, idxOf_map_of_inj hf i ys]
      by_cases h : y = i
      · subst h; simp
      · have : f y ≠ f i := fun h' => h (hf h')
        rw [beq_false_of_ne this, beq_false_of_ne h]

/-- **The code is invariant under an order-preserving renaming of the free variables.** -/
theorem Expr.capNorm_ren {f : Nat → Nat} (hf : StrictOrd f) (e : Expr) :
    Expr.capNorm (Expr.ren f 0 e) = Expr.capNorm e := by
  simp only [Expr.capNorm, Expr.ren_ren]
  congr 1
  funext i
  simp only [Function.comp, Expr.capIdx, Expr.capVars_ren hf]
  exact idxOf_map_of_inj hf.inj i _

/-- **`capNorm` is invariant under `shift`.**  `[spec §68]` -/
theorem Expr.capNorm_shift (d c : Nat) (e : Expr) :
    Expr.capNorm (Expr.shift d c e) = Expr.capNorm e := by
  have h := Expr.shift_eq_ren d c e 0
  rw [Nat.add_zero] at h
  rw [h, Expr.capNorm_ren (shiftIdx_strictOrd d c)]

/-! ### A code's free variables -/

theorem Expr.capIdx_lt {e : Expr} {i : Nat} (h : i ∈ Expr.occs 0 e) :
    Expr.capIdx e i < (Expr.capVars e).length :=
  List.idxOf_lt_length_of_mem (Expr.mem_capVars.mpr h)

/-- **A code is closed relative to its captures**: each free variable is below their number.
`[spec §68]` -/
theorem Expr.occs_capNorm_lt (e : Expr) :
    ∀ i ∈ Expr.occs 0 (Expr.capNorm e), i < (Expr.capVars e).length := by
  intro i hi
  simp only [Expr.capNorm, Expr.occs_ren, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact Expr.capIdx_lt hj

/-! ### A closing substitution through the code -/

/-- A substitution of a renamed term is the substitution of the term when the renamed indices
read the same values. -/
theorem Expr.psub_ren (r : Nat → Nat) (γ us : List Val) :
    ∀ (e : Expr) (k : Nat), (∀ i ∈ Expr.occs k e, ∃ v, γ[i]? = some v ∧ us[r i]? = some v) →
      Expr.psub k us (Expr.ren r k e) = Expr.psub k γ e
  | .var i, k, h => by
      by_cases hi : i < k
      · simp only [Expr.ren, Expr.psub, if_pos hi]
      · obtain ⟨v, hγ, hus⟩ := h (i - k) (by simp [Expr.occs, hi])
        simp only [Expr.ren, Expr.psub, if_neg hi, if_neg (show ¬ (r (i - k) + k < k) by omega),
          Nat.add_sub_cancel, hγ, hus]
  | .unit, _, _ => rfl
  | .pair a b, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.psub, Expr.psub_ren r γ us a k (fun i hi => h i (.inl hi)),
        Expr.psub_ren r γ us b k (fun i hi => h i (.inr hi))]
  | .inj₁ a, k, h => by simp only [Expr.ren, Expr.psub, Expr.psub_ren r γ us a k h]
  | .inj₂ a, k, h => by simp only [Expr.ren, Expr.psub, Expr.psub_ren r γ us a k h]
  | .lam b, k, h => by simp only [Expr.ren, Expr.psub, Expr.psub_ren r γ us b (k + 1) h]
  | .loc _, _, _ => rfl
  | .prim _, _, _ => rfl
  | .seq a b, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.psub, Expr.psub_ren r γ us a k (fun i hi => h i (.inl hi)),
        Expr.psub_ren r γ us b k (fun i hi => h i (.inr hi))]
  | .letpair a b, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.psub, Expr.psub_ren r γ us a k (fun i hi => h i (.inl hi)),
        Expr.psub_ren r γ us b (k + 2) (fun i hi => h i (.inr hi))]
  | .case a b₁ b₂, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.psub,
        Expr.psub_ren r γ us a k (fun i hi => h i (.inl (.inl hi))),
        Expr.psub_ren r γ us b₁ (k + 1) (fun i hi => h i (.inl (.inr hi))),
        Expr.psub_ren r γ us b₂ (k + 1) (fun i hi => h i (.inr hi))]
  | .app f a, k, h => by
      simp only [Expr.occs, List.mem_append] at h
      simp only [Expr.ren, Expr.psub, Expr.psub_ren r γ us f k (fun i hi => h i (.inl hi)),
        Expr.psub_ren r γ us a k (fun i hi => h i (.inr hi))]

/-- **A closing substitution is the code's at the captured values**: when `γ` covers `e`'s free
variables, `γ(e) = (capNorm e)[capEnv e γ]`.  `[spec §68]` -/
theorem Expr.psub_capNorm (e : Expr) (γ : List Val)
    (hγ : ∀ i ∈ Expr.occs 0 e, i < γ.length) :
    Expr.psub 0 (Expr.capEnv e γ) (Expr.capNorm e) = Expr.psub 0 γ e := by
  refine Expr.psub_ren _ γ _ e 0 (fun i hi => ⟨γ[i]'(hγ i hi), ?_, ?_⟩)
  · exact List.getElem?_eq_getElem (hγ i hi)
  · have hm : i ∈ Expr.capVars e := Expr.mem_capVars.mpr hi
    have hl := List.idxOf_lt_length_of_mem hm
    simp only [Expr.capEnv, Expr.capIdx, List.getElem?_map, List.getElem?_eq_getElem hl,
      List.getElem_idxOf hl, Option.map_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (hγ i hi), Option.getD_some]

/-- **`codeI`'s syntactic step**: the closed thunk `λ(γ(M))` (`thunkF_compatC`) is the code of
`λM` at its captured values.  `[spec §68]` -/
theorem Expr.lam_psub_capNorm (M : Expr) (γ : List Val)
    (hγ : ∀ i ∈ Expr.occs 1 M, i < γ.length) :
    Expr.lam (Expr.psub 1 γ M) =
      Expr.psub 0 (Expr.capEnv (.lam M) γ) (Expr.capNorm (.lam M)) :=
  (Expr.psub_capNorm (.lam M) γ hγ).symm

end BoCa
