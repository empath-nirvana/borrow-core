import DenseCarrier.Carrier

/-!
# DenseCarrier — the dense lifetime order `WithTop ℚ`, its segment shifts and their automorphisms

`WithTop ℚ` is a dense linear order with a top and no bottom. The **segment shift at the cut `c`
by `k > 0`** (`shiftQ c k`) fixes every lifetime at or above `c` and moves every lifetime strictly
below `c` down by `k`: an order embedding fixing `⊤`, which leaves the interval `[c - k, c)` with
no preimage. It is the move `Restrat.Emb.shift` makes on `ℕᵒᵈ`.

It is not onto, but on any set of lifetimes whose part below the cut is bounded below the cut it
agrees with an order automorphism (`exists_aut_agree`): the translation by `-k` when `c = ⊤`, and
otherwise the piecewise-affine map that translates by `-k` up to the bound `a`, stretches `[a, c]`
onto `[a - k, c]`, and fixes the rest (`plIso`). The lifetimes a configuration reads (the slots and
the reading `δ`) have such a bound at every cut (`slots_bound`, `config_bound`).
-/

noncomputable section

namespace DenseCarrier

/-! ### The segment shift -/

/-- The segment shift at the cut `c` by `k`. -/
def shiftQ (c : WithTop ℚ) (k : ℚ) (x : WithTop ℚ) : WithTop ℚ :=
  if x < c then WithTop.map (fun q => q - k) x else x

theorem shiftQ_of_lt {c x : WithTop ℚ} {k : ℚ} (h : x < c) :
    shiftQ c k x = WithTop.map (fun q => q - k) x := if_pos h

theorem shiftQ_of_le {c x : WithTop ℚ} {k : ℚ} (h : c ≤ x) : shiftQ c k x = x :=
  if_neg (not_lt.mpr h)

@[simp] theorem shiftQ_top (c : WithTop ℚ) (k : ℚ) : shiftQ c k ⊤ = ⊤ := by
  by_cases h : (⊤ : WithTop ℚ) < c
  · exact absurd h (not_lt.mpr le_top)
  · exact if_neg h

theorem shiftQ_coe_lt {c : WithTop ℚ} {q k : ℚ} (h : (q : WithTop ℚ) < c) :
    shiftQ c k q = ((q - k : ℚ) : WithTop ℚ) := by
  rw [shiftQ_of_lt h]; rfl

theorem shiftQ_strictMono {c : WithTop ℚ} {k : ℚ} (hk : 0 < k) : StrictMono (shiftQ c k) := by
  intro x y hxy
  induction y using WithTop.recTopCoe with
  | top =>
      rw [shiftQ_top]
      induction x using WithTop.recTopCoe with
      | top => exact absurd hxy (lt_irrefl _)
      | coe q =>
          by_cases hq : (q : WithTop ℚ) < c
          · rw [shiftQ_coe_lt hq]; exact WithTop.coe_lt_top _
          · rw [shiftQ_of_le (not_lt.mp hq)]; exact WithTop.coe_lt_top _
  | coe r =>
      induction x using WithTop.recTopCoe with
      | top => exact absurd hxy (not_lt.mpr le_top)
      | coe q =>
          have hqr : q < r := WithTop.coe_lt_coe.mp hxy
          by_cases hr : (r : WithTop ℚ) < c
          · have hq : (q : WithTop ℚ) < c := lt_trans hxy hr
            rw [shiftQ_coe_lt hq, shiftQ_coe_lt hr]
            exact WithTop.coe_lt_coe.mpr (by linarith)
          · rw [shiftQ_of_le (not_lt.mp hr)]
            by_cases hq : (q : WithTop ℚ) < c
            · rw [shiftQ_coe_lt hq]
              exact WithTop.coe_lt_coe.mpr (by linarith)
            · rw [shiftQ_of_le (not_lt.mp hq)]; exact hxy

/-! ### Slots in `WithTop ℚ` -/

/-- The position of Core's slot `n`: `⊤` at `0`, `-n` otherwise. -/
def ratPos (n : ℕ) : WithTop ℚ := if n = 0 then ⊤ else ((-(n : ℚ) : ℚ) : WithTop ℚ)

theorem ratPos_lt {m n : ℕ} (h : n < m) : ratPos m < ratPos n := by
  have hm : m ≠ 0 := by omega
  unfold ratPos
  rw [if_neg hm]
  by_cases hn : n = 0
  · rw [if_pos hn]; exact WithTop.coe_lt_top _
  · rw [if_neg hn]
    exact WithTop.coe_lt_coe.mpr (neg_lt_neg (by exact_mod_cast h))

open BoCa.Fig16 in
/-- Core's slots in `WithTop ℚ`: slot `n` at `-n`, slot `0` at `⊤`. -/
def ratSlots : Slots (WithTop ℚ) where
  f x := ratPos (OrderDual.ofDual x)
  strictMono := fun _ _ hxy => ratPos_lt hxy
  map_top := if_pos rfl

open BoCa.Fig16 in
/-- Below every lifetime of `WithTop ℚ` there is a slot. -/
theorem ratSlots_unbounded (q : WithTop ℚ) : ∃ s : Life, ratSlots s < q := by
  induction q using WithTop.recTopCoe with
  | top =>
      refine ⟨OrderDual.toDual 1, ?_⟩
      show ratPos 1 < ⊤
      unfold ratPos
      rw [if_neg one_ne_zero]
      exact WithTop.coe_lt_top _
  | coe r =>
      obtain ⟨n, hn⟩ := exists_nat_gt (-r)
      refine ⟨OrderDual.toDual (n + 1), ?_⟩
      show ratPos (n + 1) < r
      unfold ratPos
      rw [if_neg (Nat.succ_ne_zero n)]
      exact WithTop.coe_lt_coe.mpr (by push_cast; linarith)

/-! ### The translation -/

/-- Translation by `-k`, on `WithTop ℚ`. -/
def transIso (k : ℚ) : WithTop ℚ ≃o WithTop ℚ := (OrderIso.addRight (-k)).withTopCongr

theorem transIso_coe (k q : ℚ) : transIso k q = ((q - k : ℚ) : WithTop ℚ) := by
  simp [transIso, OrderIso.withTopCongr_apply, sub_eq_add_neg]

theorem transIso_agree_top (k : ℚ) (x : WithTop ℚ) : transIso k x = shiftQ ⊤ k x := by
  induction x using WithTop.recTopCoe with
  | top => rw [shiftQ_top]; exact OrderIso.map_top _
  | coe q => rw [transIso_coe, shiftQ_coe_lt (WithTop.coe_lt_top q)]

/-! ### The stretch -/

section PL
variable (a b k : ℚ)

/-- Translate by `-k` up to `a`, stretch `[a, b]` onto `[a - k, b]`, fix the rest. -/
def plQ (q : ℚ) : ℚ :=
  if q ≤ a then q - k else if q < b then a - k + (q - a) * ((b - a + k) / (b - a)) else q

variable {a b k}

theorem plQ_slope_pos (hab : a < b) (hk : 0 < k) : 0 < (b - a + k) / (b - a) :=
  div_pos (by linarith) (by linarith)

theorem plQ_of_le {q : ℚ} (h : q ≤ a) : plQ a b k q = q - k := if_pos h

theorem plQ_of_mid {q : ℚ} (h₁ : a < q) (h₂ : q < b) :
    plQ a b k q = a - k + (q - a) * ((b - a + k) / (b - a)) := by
  rw [plQ, if_neg (not_le.mpr h₁), if_pos h₂]

theorem plQ_of_ge {q : ℚ} (hab : a < b) (h : b ≤ q) : plQ a b k q = q := by
  rw [plQ, if_neg (not_le.mpr (lt_of_lt_of_le hab h)), if_neg (not_lt.mpr h)]

/-- The middle piece at `b` is `b`. -/
theorem plQ_mid_at_b (hab : a < b) : a - k + (b - a) * ((b - a + k) / (b - a)) = b := by
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

theorem plQ_strictMono (hab : a < b) (hk : 0 < k) : StrictMono (plQ a b k) := by
  have hs := plQ_slope_pos hab hk
  intro x y hxy
  rcases le_or_gt x a with hxa | hxa
  · rw [plQ_of_le hxa]
    rcases le_or_gt y a with hya | hya
    · rw [plQ_of_le hya]; linarith
    · rcases lt_or_ge y b with hyb | hyb
      · rw [plQ_of_mid hya hyb]
        have : 0 < (y - a) * ((b - a + k) / (b - a)) := mul_pos (by linarith) hs
        linarith
      · rw [plQ_of_ge hab hyb]; linarith
  · rcases lt_or_ge x b with hxb | hxb
    · rw [plQ_of_mid hxa hxb]
      rcases lt_or_ge y b with hyb | hyb
      · rw [plQ_of_mid (lt_trans hxa hxy) hyb]
        have : (x - a) * ((b - a + k) / (b - a)) < (y - a) * ((b - a + k) / (b - a)) :=
          mul_lt_mul_of_pos_right (by linarith) hs
        linarith
      · rw [plQ_of_ge hab hyb]
        have h1 : (x - a) * ((b - a + k) / (b - a)) < (b - a) * ((b - a + k) / (b - a)) :=
          mul_lt_mul_of_pos_right (by linarith) hs
        have h2 := plQ_mid_at_b (k := k) hab
        linarith
    · rw [plQ_of_ge hab hxb, plQ_of_ge hab (le_of_lt (lt_of_le_of_lt hxb hxy))]
      exact hxy

theorem plQ_surjective (hab : a < b) (hk : 0 < k) : Function.Surjective (plQ a b k) := by
  have hs := plQ_slope_pos hab hk
  intro y
  rcases le_or_gt y (a - k) with hy | hy
  · exact ⟨y + k, by rw [plQ_of_le (by linarith)]; ring⟩
  · rcases lt_or_ge y b with hyb | hyb
    · refine ⟨a + (y - (a - k)) / ((b - a + k) / (b - a)), ?_⟩
      have hq₁ : a < a + (y - (a - k)) / ((b - a + k) / (b - a)) := by
        have : 0 < (y - (a - k)) / ((b - a + k) / (b - a)) := div_pos (by linarith) hs
        linarith
      have hq₂ : a + (y - (a - k)) / ((b - a + k) / (b - a)) < b := by
        have h3 : (y - (a - k)) / ((b - a + k) / (b - a)) < b - a := by
          rw [div_lt_iff₀ hs]
          have h2 := plQ_mid_at_b (k := k) hab
          linarith
        linarith
      rw [plQ_of_mid hq₁ hq₂,
        show a + (y - (a - k)) / ((b - a + k) / (b - a)) - a
          = (y - (a - k)) / ((b - a + k) / (b - a)) by ring,
        div_mul_cancel₀ _ hs.ne']
      ring
    · exact ⟨y, plQ_of_ge hab hyb⟩

/-- The stretch as an order automorphism of `ℚ`. -/
def plIsoQ (hab : a < b) (hk : 0 < k) : ℚ ≃o ℚ :=
  StrictMono.orderIsoOfSurjective _ (plQ_strictMono hab hk) (plQ_surjective hab hk)

/-- … and of `WithTop ℚ`. -/
def plIso (hab : a < b) (hk : 0 < k) : WithTop ℚ ≃o WithTop ℚ := (plIsoQ hab hk).withTopCongr

theorem plIso_coe (hab : a < b) (hk : 0 < k) (q : ℚ) :
    plIso hab hk q = (plQ a b k q : WithTop ℚ) := by
  simp [plIso, plIsoQ, OrderIso.withTopCongr_apply]

/-- The stretch agrees with the segment shift at the cut `b` up to `a` and from `b` on. -/
theorem plIso_agree (hab : a < b) (hk : 0 < k) {x : WithTop ℚ}
    (hx : x ≤ (a : WithTop ℚ) ∨ (b : WithTop ℚ) ≤ x) : plIso hab hk x = shiftQ b k x := by
  induction x using WithTop.recTopCoe with
  | top => rw [shiftQ_top]; exact OrderIso.map_top _
  | coe q =>
      rw [plIso_coe]
      rcases hx with hx | hx
      · have hqa : q ≤ a := WithTop.coe_le_coe.mp hx
        rw [plQ_of_le hqa, shiftQ_coe_lt (WithTop.coe_lt_coe.mpr (lt_of_le_of_lt hqa hab))]
      · have hqb : b ≤ q := WithTop.coe_le_coe.mp hx
        rw [plQ_of_ge hab hqb, shiftQ_of_le hx]

end PL

/-! ### An automorphism agreeing with the shift on a configuration's lifetimes -/

/-- **On a set whose part below the cut is bounded below the cut, the segment shift agrees with an
order automorphism.** -/
theorem exists_aut_agree {c : WithTop ℚ} {k : ℚ} (hk : 0 < k) (S : Set (WithTop ℚ))
    (hS : ∃ a : WithTop ℚ, a < c ∧ ∀ x ∈ S, x < c → x ≤ a) :
    ∃ π : WithTop ℚ ≃o WithTop ℚ, ∀ x ∈ S, π x = shiftQ c k x := by
  induction c using WithTop.recTopCoe with
  | top => exact ⟨transIso k, fun x _ => transIso_agree_top k x⟩
  | coe b =>
      obtain ⟨a, hab, ha⟩ := hS
      induction a using WithTop.recTopCoe with
      | top => exact absurd hab (not_lt.mpr le_top)
      | coe a =>
          have hab' : a < b := WithTop.coe_lt_coe.mp hab
          refine ⟨plIso hab' hk, fun x hx => plIso_agree hab' hk ?_⟩
          by_cases hxc : x < (b : WithTop ℚ)
          · exact Or.inl (ha x hx hxc)
          · exact Or.inr (not_lt.mp hxc)

open BoCa.Fig16 in
/-- **The slots below any cut have a greatest one**, wherever they sit: the slots below the cut
are a lower set of `ℕᵒᵈ`, whose least natural is the greatest slot. -/
theorem slots_bound {L : Type} [LinearOrder L] [OrderTop L] (ι : Slots L) (c : L)
    (h : ∃ s, ι s < c) : ∃ s₀, ι s₀ < c ∧ ∀ s, ι s < c → ι s ≤ ι s₀ := by
  classical
  have hex : ∃ n : ℕ, ι (OrderDual.toDual n) < c := by
    obtain ⟨s, hs⟩ := h
    exact ⟨OrderDual.ofDual s, hs⟩
  refine ⟨OrderDual.toDual (Nat.find hex), Nat.find_spec hex, fun s hs => ?_⟩
  apply ι.strictMono.monotone
  show Nat.find hex ≤ OrderDual.ofDual s
  exact Nat.find_min' hex hs

/-- A finite list of lifetimes has a bound below the cut on its part below the cut. -/
theorem list_bound (l : List (WithTop ℚ)) (c : WithTop ℚ) :
    ∃ a : WithTop ℚ, a < c ∧ ∀ x ∈ l, x < c → x ≤ a := by
  induction l with
  | nil =>
      induction c using WithTop.recTopCoe with
      | top => exact ⟨(0 : ℚ), WithTop.coe_lt_top 0, fun _ h => absurd h List.not_mem_nil⟩
      | coe b =>
          exact ⟨((b - 1 : ℚ) : WithTop ℚ), WithTop.coe_lt_coe.mpr (by linarith),
            fun _ h => absurd h List.not_mem_nil⟩
  | cons y t ih =>
      obtain ⟨a, hac, ha⟩ := ih
      by_cases hy : y < c
      · refine ⟨max a y, max_lt hac hy, fun x hx hxc => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_max_right _ _
        · exact le_trans (ha x hx hxc) (le_max_left _ _)
      · refine ⟨a, hac, fun x hx hxc => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hxc hy
        · exact ha x hx hxc

/-- The lifetimes a configuration reads: the slots' positions and the reading's values. -/
def configLifes (ι : Slots (WithTop ℚ)) (δ : LSubD (WithTop ℚ)) : Set (WithTop ℚ) :=
  {x | (∃ s, ι s = x) ∨ x ∈ δ.entries.map Prod.snd}

/-- **A configuration's lifetimes have a bound below every cut.** -/
theorem config_bound (ι : Slots (WithTop ℚ)) (δ : LSubD (WithTop ℚ)) (c : WithTop ℚ) :
    ∃ a : WithTop ℚ, a < c ∧ ∀ x ∈ configLifes ι δ, x < c → x ≤ a := by
  obtain ⟨a₁, ha₁c, ha₁⟩ := list_bound (δ.entries.map Prod.snd) c
  by_cases hs : ∃ s, ι s < c
  · obtain ⟨s₀, hs₀c, hs₀⟩ := slots_bound ι c hs
    refine ⟨max a₁ (ι s₀), max_lt ha₁c hs₀c, fun x hx hxc => ?_⟩
    rcases hx with ⟨s, rfl⟩ | hx
    · exact le_trans (hs₀ s hxc) (le_max_right _ _)
    · exact le_trans (ha₁ x hx hxc) (le_max_left _ _)
  · refine ⟨a₁, ha₁c, fun x hx hxc => ?_⟩
    rcases hx with ⟨s, rfl⟩ | hx
    · exact absurd ⟨s, hxc⟩ hs
    · exact ha₁ x hx hxc

end DenseCarrier

end
