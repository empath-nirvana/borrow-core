import DenseCarrier.Relend
import DenseCarrier.FL

/-!
# DenseCarrier — re-lending reads room: the invariant is not closed under `U`

`Relend.lean` closes the invariant `RelendV` over every first-order type. This file shows it is not
closed under `U`, at every lifetime order, every placement of the slots and every re-lending other
than the identity, and in Core. The cause is not depth: it is **room**.

A cell sits at a slot, and the slots are discrete (`Cantor.lean`: the index of the strata is
reverse-well-founded). `[@'a] (Mut 'a (Mut 'b 1))` (`boxMM`) needs its outer cell strictly above
`@'a` (the `[−]`) and strictly below the inner cell's slot (the `Mut` clause's stratification), so
it needs a slot strictly between `@'a` and `@'b`:

* `vD_boxMM_empty`: with `'a` at a slot and `'b` at the slot just above it, nothing is related at
  `boxMM`, at any list;
* `vD_boxMM_room`: with a slot strictly between, the borrow of a borrow whose outer cell sits there
  is related, and is a typed world.

A re-lending other than the identity moves its least moved slot below itself and fixes the slot
just above, so it opens a slot between them (`exists_adjGap`): the reading of `'a` at the least
moved slot and of `'b` at the one above has no room, and its moved reading has room. So:

* `not_reflect_boxMM`: re-lending does not reflect the relation, already at a first-order type:
  `boxMM` is empty at the reading and inhabited at the moved one. The relation's quantifiers over
  resources read how many slots lie between two lifetimes, not only their order.
* `not_relend_kU`: a closure of `U (boxMM ⊸ F mm0)` (`kU`), with `mm0 = Mut 'a (Mut 'a 1)` empty at
  every reading (`vD_mm0_empty`), is related at the reading because its argument type is empty
  there, and at the moved reading it is not related at the re-make of its resource (which is `∅`).
  The closure stores no predicate: no invariant of stored predicates rules it out. Contravariance
  turns the failure of reflection at the argument into a failure of preservation at `U`.
* `not_relend_kMut`: the same closure stored in a lent cell, `Mut 'a ([@'a] kU)`, a stored
  continuation's type: related at the reading, no re-make related at the moved one.
* `not_relendV_kU_rat`, `not_relendV_kU_life`: `RelendV` fails at `kU` over `WithTop ℚ` (probe 1's
  slots and shift) and over `Life` (Core's carrier); `core_not_relend_kU`: in Core's own relation
  `vC`, through `vD_id`, at every re-slotting other than the identity — so at every segment shift
  at every cut.

The closure is related only vacuously at its argument type, and no typable term is: a typable `λ`
of that type would be related at the moved reading too, where `F mm0` has no value. Whether such a
closure arises is not checked; the refutations do not depend on it, but their consequence for Law 2
does.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx)
open GhostEnd (innerView unitQ unitQ_holds)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-! ### The types -/

/-- `Mut 'a (Mut 'a 1)`: no value at any reading. -/
abbrev mm0 : VTy := .mut (.var 0) (.mut (.var 0) .unit)

/-- `[@'a] (Mut 'a (Mut 'b 1))`: a borrow of a borrow whose outer cell is strictly above `'a`. -/
abbrev boxMM : VTy := .box (.var 0) mm

/-- `boxMM ⊸ F mm0`. -/
abbrev kC : CTy := .arr boxMM (.ret mm0)

/-- `U (boxMM ⊸ F mm0)`: a closure, or a continuation awaiting a value of `boxMM`. -/
abbrev kU : VTy := .thunk kC

/-- `Mut 'a ([@'a] kU)`: such a continuation stored in a lent cell. -/
abbrev kMut : VTy := .mut (.var 0) (.box (.var 0) kU)

theorem fov_boxMM : FOV boxMM := trivial
theorem fragV_kU : FragV kU := ⟨trivial, trivial⟩
theorem fragV_kMut : FragV kMut := ⟨trivial, trivial⟩

/-! ### `Mut 'a (Mut 'a 1)` is empty -/

/-- **`Mut 'a (Mut 'a 1)` has no value**: the payload `Mut 'a 1` holds at a cell at the outer cell's
own slot, which is not in its stratum. -/
theorem vD_mm0_empty (ι : Slots L) (ls : List SRec) (δ : LSubD L) (v : Val) (ρ : WRes) :
    ¬ vD (ℍ := ℍ) ι mm0 ls δ v ρ := by
  intro h
  obtain ⟨α, hα, ℓ, hsep⟩ := h
  obtain ⟨-, b, u, σ, hσ, Q, hw, ls₀, hαb, -, -, -, hstr⟩ := pure_sep_iff.mp hsep
  have hin : vD (ℍ := ℍ) ι (.mut (.var 0) .unit) [] δ (.loc 0) (innerView 0 b) :=
    ⟨α, hα, 0, pure_sep_mk rfl (ptoMutD_innerView_le ι hαb [] δ)⟩
  have hs := hstr [] _ _ hin 0 _ (ResU.single_get_self _ _)
  exact lt_irrefl b hs

/-! ### No room: `boxMM` is empty -/

/-- **No slot between `@'a` and `@'b`: nothing is related at `boxMM`**, when `'a` reads the slot
`m + 1` and `'b` the slot `m` just above it. -/
theorem vD_boxMM_empty (ι : Slots L) {δ : LSubD L} {m : ℕ}
    (h0 : δ.find? 0 = some (ι (OrderDual.toDual (m + 1))))
    (h1 : δ.find? 1 = some (ι (OrderDual.toDual m))) (ls : List SRec) (v : Val) (ρ : WRes) :
    ¬ vD (ℍ := ℍ) ι boxMM ls δ v ρ := by
  intro h
  obtain ⟨α, hα, hb, ho⟩ := h
  change δ.find? 0 = some α at hα
  rw [h0] at hα
  obtain rfl := Option.some.inj hα
  obtain ⟨α', hα', ℓ, hsep⟩ := hb
  change δ.find? 0 = some α' at hα'
  rw [h0] at hα'
  obtain rfl := Option.some.inj hα'
  obtain ⟨-, b, u, σ, hσ, Q, hw, ls₀, hαb, hρ, -, -, hstr⟩ := pure_sep_iff.mp hsep
  -- the payload holds at a cell at the slot `m`, which has to be above `b`
  have hin : vD (ℍ := ℍ) ι mb [] δ (.loc 0) (innerView 0 (OrderDual.toDual m)) :=
    ⟨_, h1, 0, pure_sep_mk rfl (ptoMutD_innerView_le ι le_rfl [] δ)⟩
  have hbm : b < OrderDual.toDual m := hstr [] _ _ hin 0 _ (ResU.single_get_self _ _)
  -- the `[−]` puts `b` strictly above the slot `m + 1`
  have hcell := ho ℓ _ (by rw [hρ]; exact ResU.single_get_self _ _)
  have hab : OrderDual.toDual (m + 1) < b := ι.lt_iff.mp hcell
  have e₁ : m < OrderDual.ofDual b := hbm
  have e₂ : OrderDual.ofDual b < m + 1 := hab
  omega

/-! ### Room: `boxMM` is inhabited -/

/-- The borrow of a borrow is related at `Mut 'a (Mut 'b 1)` whenever `'a` is at or below the outer
cell's slot (`vD_rhoMM` with `⊑` for `=`). -/
theorem vD_rhoMM_le (ι : Slots L) (δ : LSubD L) {si bo : Life} (ℓ ℓ' : Loc) {α : L}
    (h0 : δ.find? 0 = some α) (hα : α ≤ ι bo) (h1 : δ.find? 1 = some (ι si)) (hbs : bo < si) :
    vD (ℍ := ℍ) ι mm [] δ (.loc ℓ) (rhoMM (ℍ := ℍ) ι δ ℓ ℓ' h1 hbs) :=
  ⟨α, h0, ℓ, pure_sep_mk rfl ⟨bo, .loc ℓ', innerView ℓ' si, innerView_inStratum ℓ' hbs,
    qOut ι δ bo, qOut_holds ι δ ℓ' h1 hbs, [], hα, rfl, ofS_qOut ι δ h1 hbs,
    fun x => by simp, fun _ _ _ h => vD_mb_inStratum ι δ h1 hbs h⟩⟩

/-- **Room between `@'a` and `@'b`: `boxMM` is inhabited** by the borrow of a borrow whose outer
cell sits at a slot strictly between them. -/
theorem vD_boxMM_room (ι : Slots L) (δ : LSubD L) {si bo : Life} (ℓ ℓ' : Loc) {α : L}
    (h0 : δ.find? 0 = some α) (hα : α < ι bo) (h1 : δ.find? 1 = some (ι si)) (hbs : bo < si) :
    vD (ℍ := ℍ) ι boxMM [] δ (.loc ℓ) (rhoMM (ℍ := ℍ) ι δ ℓ ℓ' h1 hbs) := by
  refine ⟨α, h0, vD_rhoMM_le ι δ ℓ ℓ' h0 hα.le h1 hbs, fun l ψ e => ?_⟩
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact hα

/-- The borrow of a borrow is a typed world. -/
theorem tw_rhoMM (ι : Slots L) (δ : LSubD L) {si bo : Life} (h1 : δ.find? 1 = some (ι si))
    (hbs : bo < si) : TW (rhoMM (ℍ := ℍ) ι δ 0 1 h1 hbs) [] [] :=
  tw_nested (ℓ' := 1) (by decide) rfl rfl

/-! ### A re-lending opens room -/

/-- **A re-slotting other than the identity opens a slot**: it fixes some slot `m` and moves the
slot `m + 1` just below it strictly lower, leaving `m + 1` strictly between the two images. -/
theorem exists_adjGap {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x) :
    ∃ m : ℕ, θ (OrderDual.toDual m) = OrderDual.toDual m ∧
      θ (OrderDual.toDual (m + 1)) < OrderDual.toDual (m + 1) := by
  classical
  have hex : ∃ n : ℕ, θ.toNat n ≠ n := by
    obtain ⟨x, hx⟩ := hθ
    exact ⟨OrderDual.ofDual x, fun h => hx (congrArg OrderDual.toDual h)⟩
  have hmin : ∀ m < Nat.find hex, θ.toNat m = m := fun m hm => not_not.mp (Nat.find_min hex hm)
  have hn : θ.toNat (Nat.find hex) ≠ Nat.find hex := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, θ.toNat_zero] at hn
    exact hn rfl
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  refine ⟨m, ?_, ?_⟩
  · rw [← θ.toNat_toDual, hmin m (by omega)]
  · rw [← θ.toNat_toDual]
    have hn' : θ.toNat (m + 1) ≠ m + 1 := by rw [← Nat.succ_eq_add_one, ← hm]; exact hn
    have hle : m + 1 ≤ θ.toNat (m + 1) := θ.toNat_strictMono.id_le (m + 1)
    exact OrderDual.toDual_lt_toDual.mpr (lt_of_le_of_ne hle (Ne.symm hn'))

/-! ### Re-lending does not reflect the relation -/

/-- At the reading of `'a` at the moved slot `m + 1` and `'b` at the fixed slot `m`, the moved reading
has room, and `boxMM` is inhabited there by a typed world. -/
theorem boxMM_moved {ι : Slots L} (R : Relend ι) {m : ℕ}
    (hfix : R.θ (OrderDual.toDual m) = OrderDual.toDual m)
    (hmove : R.θ (OrderDual.toDual (m + 1)) < OrderDual.toDual (m + 1)) :
    ∃ ρ', vD (ℍ := ℍ) ι boxMM []
        ((δmm ι (OrderDual.toDual (m + 1)) (OrderDual.toDual m)).map R.ψ) (.loc 0) ρ' ∧
      TW ρ' [] [] := by
  have h1 : ((δmm ι (OrderDual.toDual (m + 1)) (OrderDual.toDual m)).map R.ψ).find? 1 =
      some (ι (OrderDual.toDual m)) := by
    rw [δmm_map_find1, R.agree, hfix]
  have h0 : ((δmm ι (OrderDual.toDual (m + 1)) (OrderDual.toDual m)).map R.ψ).find? 0 =
      some (ι (R.θ (OrderDual.toDual (m + 1)))) := by
    show some (R.ψ (ι _)) = _
    rw [R.agree]
  have hbs : OrderDual.toDual (m + 1) < (OrderDual.toDual m : Life) := succ_lt_life m
  exact ⟨_, vD_boxMM_room ι _ 0 1 h0 (ι.lt_iff.mpr hmove) h1 hbs, tw_rhoMM ι _ h1 hbs⟩

/-- **Re-lending does not reflect the relation, at a first-order type**: for every re-lending other
than the identity, `boxMM` is empty at a reading and inhabited — by a typed world — at its moved
reading. -/
theorem not_reflect_boxMM {ι : Slots L} (R : Relend ι) (hθ : ∃ x, R.θ x ≠ x) :
    ∃ (δ : LSubD L) (v : Val) (ρ' : WRes),
      vD (ℍ := ℍ) ι boxMM [] (δ.map R.ψ) v ρ' ∧ TW ρ' [] [] ∧
      ∀ ls w ρ, ¬ vD (ℍ := ℍ) ι boxMM ls δ w ρ := by
  obtain ⟨m, hfix, hmove⟩ := exists_adjGap R.θ hθ
  obtain ⟨ρ', h', hT⟩ := boxMM_moved (ℍ := ℍ) R hfix hmove
  exact ⟨_, _, ρ', h', hT, fun ls w ρ => vD_boxMM_empty ι (δmm_find0 ι _ _) (δmm_find1 ι _ _) ls w ρ⟩

/-! ### The closure -/

/-- **A closure of `kU` is related wherever `boxMM` is empty**: its argument type has no value. -/
theorem vD_kU_vacuous (ι : Slots L) {δ : LSubD L} (hE : ∀ ls w σ, ¬ vD (ℍ := ℍ) ι boxMM ls δ w σ)
    (ls : List SRec) (v : Val) (ρ : WRes) : vD (ℍ := ℍ) ι kU ls δ v ρ :=
  fun ls' _ w ρ₁ _ h₁ _ => absurd h₁ (hE ls' w ρ₁)

/-- **No closure of `kU` with an empty resource is related where `boxMM` holds at a typed world**:
the argument is there, and `F mm0` has no value. -/
theorem not_vD_kU (ι : Slots L) {δ : LSubD L} {w : Val} {ρ₁ : WRes}
    (h₁ : vD (ℍ := ℍ) ι boxMM [] δ w ρ₁) (hT : TW ρ₁ [] []) (v : Val) :
    ¬ vD (ℍ := ℍ) ι kU [] δ v PMap.empty := by
  intro h
  have hc : cD (ℍ := ℍ) ι kC [] δ (.val v) PMap.empty := h [] (Ext.refl [] _)
  have hwp : wpTS [] (.app (.val v) (.val w)) (fun ls'' => vD (ℍ := ℍ) ι mm0 ls'' δ) ρ₁ :=
    hc w ρ₁ ρ₁ h₁ (compS_empty_left ρ₁)
  have hval : ResU.Valid ρ₁ := hT.valid
  obtain ⟨ρ', -, -, -, -, v', -, -, -, ls', -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ⟩ :=
    hwp PMap.empty _ [] ⟨(compS_empty_left _).1, _, compS_empty_left _, hval⟩
      (compS_empty_left _) hT (fun _ hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  exact vD_mm0_empty ι _ _ _ _ hQ

/-- **Re-lending breaks the relation at `U`**: for every re-lending other than the identity, a
closure of `kU` with an empty resource is related at a reading, and its re-make (the empty
resource) is not related at the moved reading. -/
theorem not_relend_kU {ι : Slots L} (R : Relend ι) (hθ : ∃ x, R.θ x ≠ x) :
    ∃ (δ : LSubD L) (v : Val), vD (ℍ := ℍ) ι kU [] δ v PMap.empty ∧
      ¬ ∃ ρ', RemakeR R.θ PMap.empty ρ' ∧ vD (ℍ := ℍ) ι kU [] (δ.map R.ψ) v ρ' := by
  obtain ⟨δ, w, ρ₁, h₁, hT, hE⟩ := not_reflect_boxMM (ℍ := ℍ) R hθ
  refine ⟨δ, .unit, vD_kU_vacuous ι hE [] _ _, ?_⟩
  rintro ⟨ρ', hR, h⟩
  rw [remakeR_empty_iff.mp hR] at h
  exact not_vD_kU ι h₁ hT _ h

/-- **`RelendV` is not closed under `U`**: wherever a re-lending other than the identity exists. -/
theorem not_relendV_kU {ι : Slots L} (R : Relend ι) (hθ : ∃ x, R.θ x ≠ x) :
    ¬ RelendV (ℍ := ℍ) ι kU := by
  intro h
  obtain ⟨δ, v, h₁, h₂⟩ := not_relend_kU (ℍ := ℍ) R hθ
  obtain ⟨ρ', hR, h'⟩ := h R [] δ v PMap.empty h₁
  exact h₂ ⟨ρ', hR, h'⟩

/-! ### The closure stored in a lent cell -/

/-- `𝒱⟦[@'a] kU⟧`, the stored predicate, at the stratum `b`. -/
def qK (ι : Slots L) (δ : LSubD L) (b : Life) : Val → SPropS Loc Val b :=
  fun x r => vD (ℍ := ℍ) ι (.box (.var 0) kU) [] δ x r.val

/-- **The stored continuation's type breaks too**: for every re-lending other than the identity, a
lent cell holding a closure of `kU` is related at `kMut = Mut 'a ([@'a] kU)` at a reading, and no
re-make of it is related at the moved reading. -/
theorem not_relend_kMut {ι : Slots L} (R : Relend ι) (hθ : ∃ x, R.θ x ≠ x) :
    ∃ (δ : LSubD L) (v : Val) (ρ : WRes), vD (ℍ := ℍ) ι kMut [] δ v ρ ∧
      ¬ ∃ ρ', RemakeR R.θ ρ ρ' ∧ vD (ℍ := ℍ) ι kMut [] (δ.map R.ψ) v ρ' := by
  obtain ⟨m, hfix, hmove⟩ := exists_adjGap R.θ hθ
  set a : Life := OrderDual.toDual (m + 1) with ha
  set b : Life := OrderDual.toDual m with hb
  set δ := δmm ι a b with hδ
  have hE : ∀ ls w σ, ¬ vD (ℍ := ℍ) ι boxMM ls δ w σ :=
    fun ls w σ => vD_boxMM_empty ι (δmm_find0 ι _ _) (δmm_find1 ι _ _) ls w σ
  -- the payload holds only in the stratum of `a`, by its `[@'a]`
  have hstr : ∀ ls' u' σ', vD (ℍ := ℍ) ι (.box (.var 0) kU) ls' δ u' σ' → σ'.InStratum a := by
    rintro ls' u' σ' ⟨α, hα, -, ho⟩
    change δ.find? 0 = some α at hα
    rw [δmm_find0] at hα
    obtain rfl := Option.some.inj hα
    exact (outlivesD_slot ι σ' a).mp ho
  have hQk : qK ι δ a .unit ⟨PMap.empty, ResU.inStratum_empty a⟩ :=
    ⟨ι a, δmm_find0 ι _ _, vD_kU_vacuous ι hE [] _ _, fun l ψ e => absurd e (by simp)⟩
  refine ⟨δ, .loc 0, ResU.single 0 (CellU.mutOf a .unit PMap.empty (ResU.inStratum_empty a)
    (qK ι δ a) hQk), ⟨ι a, δmm_find0 ι _ _, 0, pure_sep_mk rfl ⟨a, .unit, PMap.empty, _, qK ι δ a,
      hQk, [], le_rfl, rfl, ?_, fun x => by simp, hstr⟩⟩, ?_⟩
  · funext x r
    exact propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨hstr _ _ _ h, h⟩⟩
  · rintro ⟨ρ', hR, h'⟩
    obtain ⟨α', -, ℓ', hsep'⟩ := h'
    obtain ⟨hv', b', u', σ', hσ', Q', hw', ls₀', -, hρ', hQ', hmem', -⟩ := pure_sep_iff.mp hsep'
    cases hv'
    -- the re-made cell keeps the value and re-makes the empty witness
    have h0 := hR 0
    rw [ResU.single_get_self, hρ', ResU.single_get_self] at h0
    have hcell : RemakeC R.θ (CellU.mutOf a .unit PMap.empty (ResU.inStratum_empty a)
        (qK ι δ a) hQk) (CellU.mutOf b' u' σ' hσ' Q' hw') := by
      cases h0 with
      | some h => exact h
    have hu : u' = .unit := hcell.erase
    have hσe : σ' = PMap.empty := by
      have hw := hcell.wit
      rw [CellU.wit_mutOf, CellU.wit_mutOf] at hw
      exact remakeR_empty_iff.mp hw
    subst hu; subst hσe
    have hls : ls₀' = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
      simpa using (hmem' x).mp hx
    subst hls
    have hpay : vD (ℍ := ℍ) ι (.box (.var 0) kU) [] (δ.map R.ψ) .unit PMap.empty := by
      have hx : ofS Q' .unit PMap.empty := ⟨hσ', hw'⟩
      rwa [hQ'] at hx
    obtain ⟨-, -, hk, -⟩ := hpay
    obtain ⟨ρ₁, h₁, hT⟩ := boxMM_moved (ℍ := ℍ) R hfix hmove
    exact not_vD_kU ι h₁ hT _ hk

/-! ### Instances: `WithTop ℚ`, `Life`, and Core -/

/-- At `WithTop ℚ` with Core's slots at `-n`: a segment shift of the slots with probe 1's shift of
the reading is a re-lending. -/
def ratRelend (c : Life) {k : ℕ} (hk : 0 < k) : Relend ratSlots where
  c := c
  θ := Restrat.Emb.shift c k
  ψ := shiftQ (ratSlots c) (k : ℚ)
  mono := shiftQ_strictMono (by exact_mod_cast hk)
  agree := shiftQ_ratSlots c k

/-- At `Life` with the identity placement: the re-slotting itself. -/
def lifeRelend {c : Life} (θ : Restrat.Emb c) : Relend (Slots.id) where
  c := c
  θ := θ
  ψ := θ.f
  mono := θ.strictMono
  agree := fun _ => rfl

/-- **At every cut**: at every lifetime order, every placement, every segment shift of the slots
by `k > 0` at every cut and every order-preserving reading move agreeing with it, `RelendV` fails
at `kU`. -/
theorem not_relendV_kU_everyCut (ι : Slots L) (c : Life) {k : ℕ} (hk : 0 < k) (ψ : L → L)
    (hψ : StrictMono ψ) (hag : ∀ s, ψ (ι s) = ι (Restrat.Emb.shift c k s)) :
    ¬ RelendV (ℍ := ℍ) ι kU :=
  not_relendV_kU ⟨c, Restrat.Emb.shift c k, ψ, hψ, hag⟩ (shift_ne_id c hk)

theorem not_relendV_kU_rat : ¬ RelendV (ℍ := ℍ) ratSlots kU :=
  not_relendV_kU (ratRelend ⊤ one_pos) (shift_ne_id ⊤ one_pos)

theorem not_relendV_kU_life : ¬ RelendV (ℍ := ℍ) Slots.id kU :=
  not_relendV_kU (lifeRelend (Restrat.Emb.shift ⊤ 1)) (shift_ne_id ⊤ one_pos)

/-- **In Core**: Core's own relation `vC`, at every re-slotting other than the identity, relates a
closure of `kU` with an empty resource at a reading and not at the re-slotted reading — a type
with no `∀` and no `Imm`. -/
theorem core_not_relend_kU {c : Life} (θ : Restrat.Emb c) (hθ : ∃ x, θ x ≠ x) :
    ∃ (δ : BoCa.Lifetime.LSub) (v : Val), vCE (ℍ := ℍ) none true kU [] δ v PMap.empty ∧
      ¬ vCE (ℍ := ℍ) none true kU [] (Restrat.LSub.mapN θ.toNat δ) v PMap.empty := by
  obtain ⟨δ, v, h₁, h₂⟩ := not_relend_kU (ℍ := ℍ) (lifeRelend θ) hθ
  refine ⟨toLSub δ, v, ?_, ?_⟩
  · rw [← vD_id kU fragV_kU [] δ]; exact h₁
  · rw [← toLSub_map_emb, ← vD_id kU fragV_kU [] _]
    exact fun h => h₂ ⟨PMap.empty, remakeR_empty, h⟩

/-- In Core, at every segment shift by `k > 0` at every cut. -/
theorem core_not_relend_kU_everyCut (c : Life) {k : ℕ} (hk : 0 < k) :
    ∃ (δ : BoCa.Lifetime.LSub) (v : Val), vCE (ℍ := ℍ) none true kU [] δ v PMap.empty ∧
      ¬ vCE (ℍ := ℍ) none true kU [] (Restrat.LSub.mapN (Restrat.Emb.shift c k).toNat δ) v
        PMap.empty :=
  core_not_relend_kU (ℍ := ℍ) _ (shift_ne_id c hk)

end DenseCarrier

end
