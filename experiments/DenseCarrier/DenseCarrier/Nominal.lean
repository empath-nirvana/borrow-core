import DenseCarrier.Cantor

/-!
# DenseCarrier — cells at every lifetime, with finitely supported stored predicates

`Cantor.lean` shows the layer equation has no solution over an order with an infinite ascending
chain when a `mut` cell may store every predicate on the stratum above it. The nominal reading
(sets with atoms `L`; for ordered atoms, Bojańczyk–Klin–Lasota) keeps cells at every lifetime of
`L` and restricts what a cell stores: the cells form a set acted on by the automorphisms of `L`,
and a stored predicate must be finitely supported, invariant under every automorphism fixing some
finite set of lifetimes. This is the carrier that recursion over the finitely many lifetimes in
play would build: a cell, and each predicate it stores, mentions finitely many lifetimes. A
dense `L`'s automorphisms would then move cells as well as readings, with no gap.

* `FSCarrier L Loc Val Adm`: a solution of the layer equation over `L` in the union view
  (`CellU`'s, with `L` for `Life`): a set of cells `C` acted on by `L ≃o L`, and a map `out` from
  cells to layers that is injective, lands in the well-formed layers, reaches each of them, and
  commutes with the action. A well-formed `mut` layer stores a predicate that holds only in its
  stratum, holds at the cell's value and witness, and is supported by a finite set `S` with
  `Adm β S`. `AnySupport` is the nominal reading; `SupportAbove` admits only lifetimes at or above
  the cell's, as the outlives discipline of `Mut 'a A` gives the predicates the relation stores.
* `no_fsCarrier`: **over an order with an infinite ascending chain there is no such carrier**,
  whenever a cell may store a predicate supported by `∅` or by its own lifetime and one above it.
  Along `a₀ < a₁ < ⋯`, let `Y k` be the cells at `a k` whose witness is one cell at `a (k+1)` and
  which are fixed by every automorphism fixing `a k` and `a (k+1)`. A subset `T` of `Y (k+1)` is
  stored as its closure under the automorphisms fixing `a k` and `a (k+1)` (`clo`), a predicate
  supported by those two lifetimes; the witness of a cell of `Y (k+1)` pins `a (k+2)` (`Y_pin`),
  so the closure meets `Y (k+1)` in `T` alone (`mem_clo_iff`). So `#Y k ≥ 2^#Y (k+1) > #Y (k+1)`,
  a descending sequence of cardinals. The stored closure holds at cells whose witness sits at any
  lifetime above `a (k+1)` that such an automorphism reaches: infinitely many, at a dense `L`.
* `no_fsCarrier_of_dense`, `no_fsCarrier_withTopRat`, `no_fsCarrier_withTopRat_above`: no dense
  order with two points carries one, in the nominal reading or with supports above the cell.
* `fsCarrier_life`, `fsCarrier_lifeAny`, `fsCarrier_lifeAbove`: Core's own cells are an
  `FSCarrier` over `Life`, whose only automorphism is the identity: the notion is the paper's
  model, and not empty.

So finite support does not replace recursion down `⊏`: the obstruction is `Cantor.lean`'s, with
the predicates confined to those a cell at a lifetime and the one above it can see.
-/

noncomputable section

namespace DenseCarrier
open BoCa.Fig16 (PMap)

/-! ### Lifetime sets moved by an automorphism -/

/-- `σ(ᾱ)`. -/
def LSetG.mapIso {L : Type} [LinearOrder L] (σ : L ≃o L) (s : LSetG L) : LSetG L where
  mem y := ∃ x, s.mem x ∧ σ x = y
  join := σ s.join
  meet := σ s.meet
  join_mem := ⟨_, s.join_mem, rfl⟩
  meet_mem := ⟨_, s.meet_mem, rfl⟩
  join_greatest := by
    rintro _ ⟨x, hx, rfl⟩
    exact σ.monotone (s.join_greatest x hx)
  meet_least := by
    rintro _ ⟨x, hx, rfl⟩
    exact σ.monotone (s.meet_least x hx)

/-! ### Partial maps -/

section PMapFacts
variable {Loc A B D : Type}

theorem pmap_map_map (f : A → B) (g : B → D) (p : PMap Loc A) :
    (p.map f).map g = p.map (g ∘ f) :=
  PMap.ext fun l => by simp [Option.map_map]

theorem pmap_map_id' {f : A → A} (hf : ∀ x, f x = x) (p : PMap Loc A) : p.map f = p :=
  PMap.ext fun l => by
    simp only [PMap.map_get]
    cases p.get l <;> simp [hf]

theorem pmap_map_injective' {f : A → B} (hf : Function.Injective f) :
    Function.Injective (PMap.map (Loc := Loc) f) := by
  intro p q h
  refine PMap.ext fun l => ?_
  have := congrArg (fun r => PMap.get r l) h
  simp only [PMap.map_get] at this
  exact Option.map_injective hf this

theorem pmap_map_eq_empty {f : A → B} {p : PMap Loc A} : p.map f = PMap.empty ↔ p = PMap.empty := by
  constructor
  · intro h
    refine PMap.ext fun l => ?_
    have := congrArg (fun r => PMap.get r l) h
    simp only [PMap.map_get, PMap.empty_get, Option.map_eq_none_iff] at this
    simpa using this
  · rintro rfl
    exact PMap.ext fun _ => rfl

theorem pmapSingle_get_self (l : Loc) (a : A) : (pmapSingle l a).get l = some a := by
  classical
  simp [pmapSingle]

theorem pmapSingle_get_ne {l l' : Loc} (a : A) (h : l' ≠ l) : (pmapSingle l a).get l' = none := by
  classical
  simp [pmapSingle, h]

theorem pmapSingle_map (l : Loc) (a : A) (f : A → B) :
    (pmapSingle l a).map f = pmapSingle l (f a) := by
  classical
  refine PMap.ext fun l' => ?_
  by_cases h : l' = l
  · subst h
    simp only [PMap.map_get, pmapSingle_get_self, Option.map_some]
  · simp only [PMap.map_get, pmapSingle_get_ne _ h, Option.map_none]

theorem pmapSingle_ne_of_ne {l l' : Loc} (h : l ≠ l') (a b : A) :
    pmapSingle l a ≠ pmapSingle l' b := by
  intro e
  have := congrArg (fun r => PMap.get r l) e
  simp only [pmapSingle_get_self, pmapSingle_get_ne _ h] at this
  exact absurd this (by simp)

end PMapFacts

/-! ### Layers, their action, and the carrier -/

/-- One layer of the cells over `L`, in the union view (`CellU`'s, with `L` for `Life`):
`own(v)`, `imm(ᾱ, v, ρ)`, or `mut(β, v, ρ, P̂)`, with `ρ` a resource of cells and `P̂` a
predicate on values and resources. -/
inductive LayerU (L Loc Val : Type) [LinearOrder L] (C : Type) : Type where
  | own (v : Val)
  | imm (ls : LSetG L) (v : Val) (ρ : PMap Loc C)
  | mut (β : L) (v : Val) (ρ : PMap Loc C) (P : Val → PMap Loc C → Prop)

section Ops
variable {L Loc Val C : Type} [LinearOrder L]

/-- A stored predicate moved to its image. -/
def predImg (act : (L ≃o L) → C → C) (σ : L ≃o L) (P : Val → PMap Loc C → Prop) :
    Val → PMap Loc C → Prop :=
  fun v ρ' => ∃ ρ, ρ.map (act σ) = ρ' ∧ P v ρ

/-- An automorphism on a layer: lifetimes by `σ`, the witness cell by cell, the stored predicate
to its image. -/
def layerAct (act : (L ≃o L) → C → C) (σ : L ≃o L) :
    LayerU L Loc Val C → LayerU L Loc Val C
  | .own v => .own v
  | .imm ls v ρ => .imm (ls.mapIso σ) v (ρ.map (act σ))
  | .mut β v ρ P => .mut (σ β) v (ρ.map (act σ)) (predImg act σ P)

/-- `ψ ∈ Cell_β`, read off the cell's layer. -/
def InStr (out : C → LayerU L Loc Val C) (β : L) (x : C) : Prop :=
  match out x with
  | .own _ => True
  | .imm ls _ _ => β < ls.meet
  | .mut β' _ _ _ => β < β'

/-- `ρ ∈ Res_β`. -/
def ResInStr (out : C → LayerU L Loc Val C) (β : L) (ρ : PMap Loc C) : Prop :=
  ∀ l x, ρ.get l = some x → InStr out β x

/-- `P̂` is supported by `S`: invariant under every automorphism fixing `S` pointwise. -/
def Supported (act : (L ≃o L) → C → C) (S : Finset L) (P : Val → PMap Loc C → Prop) : Prop :=
  ∀ σ : L ≃o L, (∀ x ∈ S, σ x = x) → ∀ v ρ, P v (ρ.map (act σ)) ↔ P v ρ

/-- A well-formed layer, `CellFG`'s side conditions in the union view: the witness in its
stratum; a stored predicate that holds only in the stratum, holds at the value and the witness,
and is supported by a finite set of lifetimes that `Adm` admits for a cell at `β`. -/
def LayerWF (Adm : L → Finset L → Prop) (out : C → LayerU L Loc Val C)
    (act : (L ≃o L) → C → C) : LayerU L Loc Val C → Prop
  | .own _ => True
  | .imm ls _ ρ => ResInStr out ls.join ρ
  | .mut β v ρ P => ResInStr out β ρ ∧ (∀ v' ρ', P v' ρ' → ResInStr out β ρ') ∧ P v ρ ∧
      ∃ S : Finset L, Adm β S ∧ Supported act S P

end Ops

/-- **A solution of the layer equation over `L` with finitely supported stored predicates**: a set
of cells acted on by the automorphisms of `L`, and the cells' layers, `C ≃ {y // LayerWF y}`
commuting with the action. `Adm β S` says which finite supports a cell at `β` may store a
predicate with. -/
structure FSCarrier (L Loc Val : Type) [LinearOrder L] (Adm : L → Finset L → Prop) where
  C : Type
  act : (L ≃o L) → C → C
  act_refl : ∀ x, act (OrderIso.refl L) x = x
  act_trans : ∀ σ τ x, act (σ.trans τ) x = act τ (act σ x)
  out : C → LayerU L Loc Val C
  out_injective : Function.Injective out
  out_wf : ∀ x, LayerWF Adm out act (out x)
  out_surj : ∀ y, LayerWF Adm out act y → ∃ x, out x = y
  out_act : ∀ σ x, out (act σ x) = layerAct act σ (out x)

/-- The nominal reading: every finite support. -/
abbrev AnySupport {L : Type} : L → Finset L → Prop := fun _ _ => True

/-- Supports at or above the cell's own lifetime, as the outlives discipline of `Mut 'a A` gives
the predicates the relation stores. -/
abbrev SupportAbove {L : Type} [LinearOrder L] : L → Finset L → Prop :=
  fun β S => ∀ x ∈ S, β ≤ x

namespace FSCarrier
variable {L Loc Val : Type} [LinearOrder L] {Adm : L → Finset L → Prop}
  (K : FSCarrier L Loc Val Adm)

theorem act_symm_act (σ : L ≃o L) (x : K.C) : K.act σ.symm (K.act σ x) = x := by
  rw [← K.act_trans, OrderIso.self_trans_symm, K.act_refl]

theorem act_act_symm (σ : L ≃o L) (x : K.C) : K.act σ (K.act σ.symm x) = x := by
  rw [← K.act_trans, OrderIso.symm_trans_self, K.act_refl]

theorem act_injective (σ : L ≃o L) : Function.Injective (K.act σ) := fun x y h => by
  rw [← K.act_symm_act σ x, h, K.act_symm_act]

/-- A supported predicate is its own image under an automorphism fixing its support. -/
theorem predImg_eq {S : Finset L} {P : Val → PMap Loc K.C → Prop} (hS : Supported K.act S P)
    {σ : L ≃o L} (hσ : ∀ x ∈ S, σ x = x) : predImg K.act σ P = P := by
  funext v ρ'
  apply propext
  constructor
  · rintro ⟨ρ, rfl, hP⟩
    exact (hS σ hσ v ρ).mpr hP
  · intro hP
    have hσ' : ∀ x ∈ S, σ.symm x = x := fun x hx => by
      conv_lhs => rw [← hσ x hx]
      exact σ.symm_apply_apply x
    refine ⟨ρ'.map (K.act σ.symm), ?_, (hS σ.symm hσ' v ρ').mpr hP⟩
    rw [pmap_map_map]
    exact pmap_map_id' (fun x => K.act_act_symm σ x) ρ'

theorem inStr_of_out {β β' : L} {x : K.C} {v : Val} {ρ : PMap Loc K.C}
    {P : Val → PMap Loc K.C → Prop} (h : K.out x = .mut β' v ρ P) (hlt : β < β') :
    InStr K.out β x := by
  unfold InStr
  rw [h]
  exact hlt

/-! ### The cells `Y k` -/

variable (a : ℕ → L) (ℓ₀ : Loc)

/-- The cells at `a k` whose witness is one cell at `a (k+1)`, at `ℓ₀`, and which are fixed by
every automorphism fixing `a k` and `a (k+1)`. -/
def Y (k : ℕ) : Set K.C :=
  {x | (∃ v c P, K.out x = .mut (a k) v (pmapSingle ℓ₀ c) P ∧
        ∃ v' ρ' P', K.out c = .mut (a (k + 1)) v' ρ' P') ∧
      ∀ σ : L ≃o L, σ (a k) = a k → σ (a (k + 1)) = a (k + 1) → K.act σ x = x}

/-- **The witness pins the lifetime below**: an automorphism fixing `a (k+1)` that keeps a cell of
`Y (k+1)` in `Y (k+1)` fixes `a (k+2)`, hence the cell. -/
theorem Y_pin {k : ℕ} {y : K.C} (hy : y ∈ K.Y a ℓ₀ (k + 1)) {σ : L ≃o L}
    (h1 : σ (a (k + 1)) = a (k + 1)) (hσy : K.act σ y ∈ K.Y a ℓ₀ (k + 1)) : K.act σ y = y := by
  obtain ⟨⟨v, c, P, hy, v', ρ', P', hc⟩, hsupp⟩ := hy
  obtain ⟨⟨w, d, Q, hd, w', ρ'', Q', hd'⟩, -⟩ := hσy
  rw [K.out_act, hy] at hd
  simp only [layerAct, LayerU.mut.injEq] at hd
  obtain ⟨-, -, hρ, -⟩ := hd
  rw [pmapSingle_map] at hρ
  have hcd : K.act σ c = d := pmapSingle_injective _ hρ
  have e := K.out_act σ c
  rw [hcd, hd', hc] at e
  simp only [layerAct, LayerU.mut.injEq] at e
  exact hsupp σ h1 e.1.symm

/-- The closure of a set of cells under the automorphisms fixing `a k` and `a (k+1)`. -/
def clo (k : ℕ) (T : Set K.C) : Set K.C :=
  {z | ∃ σ : L ≃o L, σ (a k) = a k ∧ σ (a (k + 1)) = a (k + 1) ∧ ∃ t ∈ T, z = K.act σ t}

theorem act_mem_clo {k : ℕ} {T : Set K.C} {τ : L ≃o L} (h0 : τ (a k) = a k)
    (h1 : τ (a (k + 1)) = a (k + 1)) {z : K.C} (hz : z ∈ K.clo a k T) :
    K.act τ z ∈ K.clo a k T := by
  obtain ⟨σ, hσ0, hσ1, t, ht, rfl⟩ := hz
  refine ⟨σ.trans τ, ?_, ?_, t, ht, (K.act_trans σ τ t).symm⟩
  · rw [OrderIso.trans_apply, hσ0, h0]
  · rw [OrderIso.trans_apply, hσ1, h1]

/-- **The closure meets `Y (k+1)` in `T` alone.** -/
theorem mem_clo_iff {k : ℕ} {T : Set K.C} (hT : T ⊆ K.Y a ℓ₀ (k + 1)) {y : K.C}
    (hy : y ∈ K.Y a ℓ₀ (k + 1)) : y ∈ K.clo a k T ↔ y ∈ T := by
  constructor
  · rintro ⟨σ, -, h1, t, ht, rfl⟩
    rw [K.Y_pin a ℓ₀ (hT ht) h1 hy]
    exact ht
  · intro hyT
    exact ⟨OrderIso.refl L, rfl, rfl, y, hyT, (K.act_refl y).symm⟩

/-! ### The stored predicates -/

/-- The cell at `a (k+1)` with an empty witness, storing "the witness is empty". -/
theorem exists_c (v₀ : Val) (k : ℕ) (hA : Adm (a (k + 1)) ∅) :
    ∃ c, K.out c = .mut (a (k + 1)) v₀ PMap.empty (fun _ ρ => ρ = PMap.empty) := by
  refine K.out_surj _ ⟨fun l x h => absurd h (by simp), ?_, rfl, ∅, hA, ?_⟩
  · rintro _ _ rfl l x h
    exact absurd h (by simp)
  · intro σ _ v ρ
    exact pmap_map_eq_empty

/-- That cell is fixed by every automorphism fixing `a (k+1)`. -/
theorem act_c {v₀ : Val} {k : ℕ} {c : K.C}
    (hc : K.out c = .mut (a (k + 1)) v₀ PMap.empty (fun _ ρ => ρ = PMap.empty)) {σ : L ≃o L}
    (h1 : σ (a (k + 1)) = a (k + 1)) : K.act σ c = c := by
  apply K.out_injective
  rw [K.out_act, hc]
  simp only [layerAct, LayerU.mut.injEq, h1, true_and]
  refine ⟨pmap_map_eq_empty.mpr rfl, ?_⟩
  funext v ρ'
  apply propext
  constructor
  · rintro ⟨ρ, rfl, rfl⟩
    exact pmap_map_eq_empty.mpr rfl
  · rintro rfl
    exact ⟨PMap.empty, pmap_map_eq_empty.mpr rfl, rfl⟩

/-- The stored predicate: the witness `ℓ₀ ↦ c`, or `ℓ₁ ↦ z` for `z` in `Z`. -/
def enc (ℓ₁ : Loc) (c : K.C) (Z : Set K.C) : Val → PMap Loc K.C → Prop :=
  fun _ ρ => ρ = pmapSingle ℓ₀ c ∨ ∃ z ∈ Z, ρ = pmapSingle ℓ₁ z

theorem enc_supported {ℓ₁ : Loc} {v₀ : Val} {k : ℕ} {c : K.C}
    (hc : K.out c = .mut (a (k + 1)) v₀ PMap.empty (fun _ ρ => ρ = PMap.empty)) (T : Set K.C) :
    Supported K.act {a k, a (k + 1)} (K.enc ℓ₀ ℓ₁ c (K.clo a k T)) := by
  intro τ hτ v ρ
  have h0 : τ (a k) = a k := hτ _ (Finset.mem_insert_self _ _)
  have h1 : τ (a (k + 1)) = a (k + 1) := hτ _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hτc := K.act_c a hc h1
  have hinj := pmap_map_injective' (Loc := Loc) (K.act_injective τ)
  constructor
  · rintro (h | ⟨z, hz, h⟩)
    · left
      refine hinj ?_
      rw [h, pmapSingle_map, hτc]
    · right
      refine ⟨K.act τ.symm z, ?_, hinj ?_⟩
      · refine K.act_mem_clo a ?_ ?_ hz
        · rw [OrderIso.symm_apply_eq, h0]
        · rw [OrderIso.symm_apply_eq, h1]
      · rw [h, pmapSingle_map, K.act_act_symm]
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · left
      rw [pmapSingle_map, hτc]
    · right
      exact ⟨K.act τ z, K.act_mem_clo a h0 h1 hz, pmapSingle_map _ _ _⟩

/-- The stored layer of a subset `T` of `Y (k+1)` is well formed. -/
theorem enc_wf (ha : StrictMono a) {ℓ₁ : Loc} {v₀ : Val} {k : ℕ} {c : K.C}
    (hc : K.out c = .mut (a (k + 1)) v₀ PMap.empty (fun _ ρ => ρ = PMap.empty)) {T : Set K.C}
    (hT : T ⊆ K.Y a ℓ₀ (k + 1)) (hA : Adm (a k) {a k, a (k + 1)}) :
    LayerWF Adm K.out K.act
      (.mut (a k) v₀ (pmapSingle ℓ₀ c) (K.enc ℓ₀ ℓ₁ c (K.clo a k T))) := by
  have hck : InStr K.out (a k) c := K.inStr_of_out hc (ha (Nat.lt_succ_self k))
  have hsingle : ∀ (l : Loc) (x : K.C), InStr K.out (a k) x →
      ResInStr K.out (a k) (pmapSingle l x) := by
    intro l x hx l' y hy
    by_cases e : l' = l
    · subst e
      rw [pmapSingle_get_self] at hy
      cases Option.some.inj hy
      exact hx
    · rw [pmapSingle_get_ne _ e] at hy
      exact absurd hy (by simp)
  refine ⟨hsingle _ _ hck, ?_, Or.inl rfl, _, hA, K.enc_supported a ℓ₀ hc T⟩
  rintro _ ρ' (rfl | ⟨z, ⟨σ, -, hσ1, t, ht, rfl⟩, rfl⟩)
  · exact hsingle _ _ hck
  · refine hsingle _ _ ?_
    obtain ⟨⟨w, d, Q, hd, -⟩, -⟩ := hT ht
    have e := K.out_act σ t
    rw [hd] at e
    simp only [layerAct, hσ1] at e
    exact K.inStr_of_out e (ha (Nat.lt_succ_self k))

/-- **A subset of `Y (k+1)` is stored by a cell of `Y k`, injectively.** -/
theorem exists_inj (ha : StrictMono a) {ℓ₁ : Loc} (hℓ : ℓ₀ ≠ ℓ₁) (v₀ : Val) (k : ℕ)
    (hA₀ : Adm (a (k + 1)) ∅) (hA₂ : Adm (a k) {a k, a (k + 1)}) :
    ∃ f : Set (K.Y a ℓ₀ (k + 1)) → K.Y a ℓ₀ k, Function.Injective f := by
  classical
  obtain ⟨c, hc⟩ := K.exists_c a v₀ k hA₀
  have hsub : ∀ T : Set (K.Y a ℓ₀ (k + 1)), Subtype.val '' T ⊆ K.Y a ℓ₀ (k + 1) := by
    rintro T _ ⟨t, -, rfl⟩
    exact t.2
  let m : Set (K.Y a ℓ₀ (k + 1)) → K.C := fun T =>
    Classical.choose (K.out_surj _ (K.enc_wf a ℓ₀ ha (ℓ₁ := ℓ₁) hc (hsub T) hA₂))
  have hm : ∀ T, K.out (m T) =
      .mut (a k) v₀ (pmapSingle ℓ₀ c) (K.enc ℓ₀ ℓ₁ c (K.clo a k (Subtype.val '' T))) :=
    fun T => Classical.choose_spec (K.out_surj _ (K.enc_wf a ℓ₀ ha (ℓ₁ := ℓ₁) hc (hsub T) hA₂))
  have hmY : ∀ T, m T ∈ K.Y a ℓ₀ k := by
    intro T
    refine ⟨⟨v₀, c, _, hm T, v₀, _, _, hc⟩, fun σ h0 h1 => ?_⟩
    apply K.out_injective
    rw [K.out_act, hm T]
    simp only [layerAct, LayerU.mut.injEq, h0, true_and]
    refine ⟨by rw [pmapSingle_map, K.act_c a hc h1], ?_⟩
    refine K.predImg_eq (K.enc_supported a ℓ₀ hc _) ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h0
    · rw [Finset.mem_singleton.mp hx]; exact h1
  refine ⟨fun T => ⟨m T, hmY T⟩, fun T T' hTT => ?_⟩
  have hout := congrArg K.out (congrArg Subtype.val hTT)
  simp only [hm, LayerU.mut.injEq, true_and] at hout
  have hP := congrFun (congrFun hout v₀)
  have hZ : ∀ z, z ∈ K.clo a k (Subtype.val '' T) ↔ z ∈ K.clo a k (Subtype.val '' T') := by
    intro z
    have := hP (pmapSingle ℓ₁ z)
    simp only [enc, eq_iff_iff] at this
    have hne : pmapSingle ℓ₁ z ≠ pmapSingle ℓ₀ c := pmapSingle_ne_of_ne hℓ.symm _ _
    constructor
    · intro hz
      rcases this.mp (Or.inr ⟨z, hz, rfl⟩) with h | ⟨z', hz', h⟩
      · exact absurd h hne
      · rwa [pmapSingle_injective _ h]
    · intro hz
      rcases this.mpr (Or.inr ⟨z, hz, rfl⟩) with h | ⟨z', hz', h⟩
      · exact absurd h hne
      · rwa [pmapSingle_injective _ h]
  ext t
  have h₁ := K.mem_clo_iff a ℓ₀ (hsub T) t.2
  have h₂ := K.mem_clo_iff a ℓ₀ (hsub T') t.2
  rw [Subtype.val_injective.mem_set_image] at h₁ h₂
  rw [← h₁, ← h₂]
  exact hZ t.1

end FSCarrier

/-! ### No carrier over an ascending chain -/

/-- **No solution of the layer equation with finitely supported stored predicates over an order
with an infinite strictly ascending chain**, given two locations and a value, whenever a cell at
`a (k+1)` may store a predicate supported by `∅` and a cell at `a k` one supported by
`{a k, a (k+1)}`. -/
theorem no_fsCarrier {L Loc Val : Type} [LinearOrder L] {Adm : L → Finset L → Prop}
    {ℓ₀ ℓ₁ : Loc} (hℓ : ℓ₀ ≠ ℓ₁) (v₀ : Val) {a : ℕ → L} (ha : StrictMono a)
    (hA₀ : ∀ k, Adm (a (k + 1)) ∅) (hA₂ : ∀ k, Adm (a k) {a k, a (k + 1)})
    (K : FSCarrier L Loc Val Adm) : False := by
  have key : ∀ n, Cardinal.mk (K.Y a ℓ₀ (n + 1)) < Cardinal.mk (K.Y a ℓ₀ n) := by
    intro n
    obtain ⟨f, hf⟩ := K.exists_inj a ℓ₀ ha hℓ v₀ n (hA₀ n) (hA₂ n)
    calc Cardinal.mk (K.Y a ℓ₀ (n + 1)) < 2 ^ Cardinal.mk (K.Y a ℓ₀ (n + 1)) := Cardinal.cantor _
      _ = Cardinal.mk (Set (K.Y a ℓ₀ (n + 1))) := Cardinal.mk_set.symm
      _ ≤ Cardinal.mk (K.Y a ℓ₀ n) := Cardinal.mk_le_of_injective hf
  exact not_strictAnti_of_wellFoundedLT (fun n => Cardinal.mk (K.Y a ℓ₀ n))
    (strictAnti_nat_of_succ_lt key)

/-- **No dense order with two points carries one**, whenever a cell may store a predicate
supported by `∅` or by its own lifetime and one above it: in the nominal reading
(`AnySupport`), and with supports at or above the cell (`SupportAbove`). -/
theorem no_fsCarrier_of_dense {L Loc Val : Type} [LinearOrder L] [DenselyOrdered L]
    [Nontrivial Loc] [Nonempty Val] {Adm : L → Finset L → Prop} (hA₀ : ∀ β, Adm β ∅)
    (hA₂ : ∀ β β', β < β' → Adm β {β, β'}) {x y : L} (h : x < y) :
    IsEmpty (FSCarrier L Loc Val Adm) := by
  refine ⟨fun K => ?_⟩
  obtain ⟨ℓ₀, ℓ₁, hℓ⟩ := exists_pair_ne Loc
  obtain ⟨v₀⟩ := (inferInstance : Nonempty Val)
  obtain ⟨a, ha, -⟩ := exists_strictMono_of_dense h
  exact no_fsCarrier hℓ v₀ ha (fun _ => hA₀ _) (fun k => hA₂ _ _ (ha (Nat.lt_succ_self k))) K

/-- At `WithTop ℚ`, with `[TR]` §3's `Loc` and `Val`, in the nominal reading. -/
theorem no_fsCarrier_withTopRat :
    IsEmpty (FSCarrier (WithTop ℚ) BoCa.Loc BoCa.Val AnySupport) :=
  haveI : Nonempty BoCa.Val := ⟨BoCa.Val.unit⟩
  no_fsCarrier_of_dense (fun _ => trivial) (fun _ _ _ => trivial)
    (show ((0 : ℚ) : WithTop ℚ) < ⊤ from WithTop.coe_lt_top 0)

/-- At `WithTop ℚ`, with supports at or above the cell. -/
theorem no_fsCarrier_withTopRat_above :
    IsEmpty (FSCarrier (WithTop ℚ) BoCa.Loc BoCa.Val SupportAbove) :=
  haveI : Nonempty BoCa.Val := ⟨BoCa.Val.unit⟩
  no_fsCarrier_of_dense (fun _ _ h => absurd h (Finset.notMem_empty _))
    (fun β β' hlt x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_rfl
      · rw [Finset.mem_singleton.mp hx]; exact hlt.le)
    (show ((0 : ℚ) : WithTop ℚ) < ⊤ from WithTop.coe_lt_top 0)

/-! ### Core's cells are an `FSCarrier` over `Life` -/

section Life
open BoCa.Fig16 (Life LSet CellU ResU Res ResS)
variable {Loc Val : Type}

theorem LSetG.ext' {L : Type} [LinearOrder L] {s t : LSetG L} (hm : ∀ x, s.mem x ↔ t.mem x)
    (hj : s.join = t.join) (hm' : s.meet = t.meet) : s = t := by
  obtain ⟨m, j, mt, _, _, _, _⟩ := s
  obtain ⟨m', j', mt', _, _, _, _⟩ := t
  simp only at hj hm' hm
  subst hj; subst hm'
  have : m = m' := funext fun x => propext (hm x)
  subst this; rfl

/-- `℘⁺(Life)` as an `LSetG Life`, field for field. -/
def lsetToG (s : LSet) : LSetG Life :=
  ⟨s.mem, s.join, s.meet, s.join_mem, s.meet_mem, s.join_greatest, s.meet_least⟩

/-- An `LSetG Life` as `℘⁺(Life)`. -/
def lsetOfG (s : LSetG Life) : LSet :=
  ⟨s.mem, s.join, s.meet, s.join_mem, s.meet_mem, s.join_greatest, s.meet_least⟩

theorem lsetOfG_toG (s : LSet) : lsetOfG (lsetToG s) = s := rfl

/-- A cell's layer: its constructor, with the witness as a resource of cells and the stored
predicate read on resources of the stratum. -/
def lifeOut : CellU Loc Val → LayerU Life Loc Val (CellU Loc Val)
  | .own v => .own v
  | .imm i => .imm (lsetToG i.ls) i.v i.ρ.toU
  | .mut m => .mut m.β m.v m.ρ.toU
      (fun v r => ∃ h : ResU.InStratum m.β r, m.P v (ResS.toRes ⟨r, h⟩))

/-- Core's cells are acted on trivially: `Life`'s only automorphism is the identity. -/
def lifeAct : (Life ≃o Life) → CellU Loc Val → CellU Loc Val := fun _ x => x

theorem inStr_lifeOut (β : Life) (x : CellU Loc Val) : InStr lifeOut β x ↔ x.InStratum β := by
  cases x <;> exact Iff.rfl

theorem resInStr_lifeOut (β : Life) (ρ : ResU Loc Val) :
    ResInStr lifeOut β ρ ↔ ρ.InStratum β :=
  forall_congr' fun _ => forall_congr' fun x => imp_congr_right fun _ => inStr_lifeOut β x

theorem res_toU_inj {α : Life} {ρ ρ' : Res Loc Val α} (h : ρ.toU = ρ'.toU) : ρ = ρ' := by
  rw [← BoCa.Fig16.Res.toRes_toS ρ, ← BoCa.Fig16.Res.toRes_toS ρ']
  exact congrArg ResS.toRes (Subtype.ext h)

theorem lifeOut_injective : Function.Injective (lifeOut (Loc := Loc) (Val := Val)) := by
  intro x y h
  cases x with
  | own v =>
      cases y with
      | own w => cases h; rfl
      | imm j => cases h
      | «mut» n => cases h
  | imm i =>
      cases y with
      | own w => cases h
      | «mut» n => cases h
      | imm j =>
          obtain ⟨ls, v, ρ⟩ := i
          obtain ⟨ls', v', ρ'⟩ := j
          simp only [lifeOut, LayerU.imm.injEq] at h
          obtain ⟨hl, rfl, hρ⟩ := h
          have hls : ls = ls' := by rw [← lsetOfG_toG ls, hl, lsetOfG_toG]
          subst hls
          cases res_toU_inj hρ
          rfl
  | «mut» m =>
      cases y with
      | own w => cases h
      | imm j => cases h
      | «mut» n =>
          obtain ⟨β, v, ρ, P, hw⟩ := m
          obtain ⟨β', v', ρ', P', hw'⟩ := n
          simp only [lifeOut, LayerU.mut.injEq] at h
          obtain ⟨rfl, rfl, hρ, hP⟩ := h
          cases res_toU_inj hρ
          have hPP : P = P' := by
            funext u r
            have k := Iff.of_eq (congrFun (congrFun hP u) r.toU)
            have hr : ResS.toRes ⟨r.toU, r.toU_inStratum⟩ = r := BoCa.Fig16.Res.toRes_toS r
            apply propext
            constructor
            · intro hu
              obtain ⟨h₂, h₃⟩ := k.mp ⟨r.toU_inStratum, by rw [hr]; exact hu⟩
              rwa [show ResS.toRes ⟨r.toU, h₂⟩ = r from BoCa.Fig16.Res.toRes_toS r] at h₃
            · intro hu
              obtain ⟨h₂, h₃⟩ := k.mpr ⟨r.toU_inStratum, by rw [hr]; exact hu⟩
              rwa [show ResS.toRes ⟨r.toU, h₂⟩ = r from BoCa.Fig16.Res.toRes_toS r] at h₃
          subst hPP
          rfl

theorem lifeOut_wf {Adm : Life → Finset Life → Prop} (hA : ∀ β, Adm β ∅) (x : CellU Loc Val) :
    LayerWF Adm lifeOut lifeAct (lifeOut x) := by
  cases x with
  | own v => exact trivial
  | imm i => exact (resInStr_lifeOut _ _).mpr i.ρ.toU_inStratum
  | «mut» m =>
      refine ⟨(resInStr_lifeOut _ _).mpr m.ρ.toU_inStratum, ?_, ?_, ∅, hA _, ?_⟩
      · rintro _ _ ⟨h, -⟩
        exact (resInStr_lifeOut _ _).mpr h
      · refine ⟨m.ρ.toU_inStratum, ?_⟩
        rw [show ResS.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩ = m.ρ from BoCa.Fig16.Res.toRes_toS m.ρ]
        exact m.hw
      · intro σ _ v ρ
        rw [pmap_map_id' (f := lifeAct σ) (fun _ => rfl)]

theorem lifeOut_surj {Adm : Life → Finset Life → Prop} (y : LayerU Life Loc Val (CellU Loc Val))
    (hy : LayerWF Adm lifeOut lifeAct y) : ∃ x, lifeOut x = y := by
  cases y with
  | own v => exact ⟨.own v, rfl⟩
  | imm ls v ρ =>
      have h : ResU.InStratum (lsetOfG ls).join ρ := (resInStr_lifeOut _ _).mp hy
      refine ⟨CellU.immOf (lsetOfG ls) v ρ h, ?_⟩
      show LayerU.imm (lsetToG (lsetOfG ls)) v (ResS.toRes ⟨ρ, h⟩).toU = LayerU.imm ls v ρ
      rw [BoCa.Fig16.ResS.toU_toRes]
      rfl
  | «mut» β v ρ P =>
      obtain ⟨hρ, hP, hw, -⟩ := hy
      have h : ResU.InStratum β ρ := (resInStr_lifeOut _ _).mp hρ
      refine ⟨CellU.mutOf β v ρ h (fun u r => P u r.val) hw, ?_⟩
      show LayerU.mut β v (ResS.toRes ⟨ρ, h⟩).toU
          (fun u r => ∃ h' : ResU.InStratum β r, P u (ResS.toRes ⟨r, h'⟩).toS.val) =
        LayerU.mut β v ρ P
      rw [BoCa.Fig16.ResS.toU_toRes]
      congr 1
      funext u r
      apply propext
      constructor
      · rintro ⟨h', hu⟩
        rwa [show (ResS.toRes ⟨r, h'⟩).toS.val = r from
          congrArg Subtype.val (BoCa.Fig16.ResS.toS_toRes ⟨r, h'⟩)] at hu
      · intro hu
        refine ⟨(resInStr_lifeOut _ _).mp (hP u r hu), ?_⟩
        rwa [show (ResS.toRes ⟨r, _⟩).toS.val = r from
          congrArg Subtype.val (BoCa.Fig16.ResS.toS_toRes ⟨r, _⟩)]

theorem layerAct_refl (y : LayerU Life Loc Val (CellU Loc Val)) :
    layerAct lifeAct (OrderIso.refl Life) y = y := by
  cases y with
  | own v => rfl
  | imm ls v ρ =>
      show LayerU.imm (ls.mapIso (OrderIso.refl Life)) v (ρ.map (lifeAct (OrderIso.refl Life))) = _
      rw [pmap_map_id' (f := lifeAct (OrderIso.refl Life)) (fun _ => rfl)]
      congr 1
      exact LSetG.ext' (fun x => ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩) rfl rfl
  | «mut» β v ρ P =>
      show LayerU.mut β v (ρ.map (lifeAct (OrderIso.refl Life)))
        (predImg lifeAct (OrderIso.refl Life) P) = _
      rw [pmap_map_id' (f := lifeAct (OrderIso.refl Life)) (fun _ => rfl)]
      congr 1
      funext u r
      apply propext
      constructor
      · rintro ⟨r₀, e, hu⟩
        rw [pmap_map_id' (f := lifeAct (OrderIso.refl Life)) (fun _ => rfl)] at e
        exact e ▸ hu
      · intro hu
        exact ⟨r, pmap_map_id' (f := lifeAct (OrderIso.refl Life)) (fun _ => rfl) r, hu⟩

/-- **Core's carrier is an `FSCarrier` over `Life`**, for every admissibility that admits `∅`:
`Life` has no automorphism but the identity, so every stored predicate is supported by `∅`, and
`out` is a cell's constructor. -/
def fsCarrier_life {Adm : Life → Finset Life → Prop} (hA : ∀ β, Adm β ∅) :
    FSCarrier Life Loc Val Adm where
  C := CellU Loc Val
  act := lifeAct
  act_refl _ := rfl
  act_trans _ _ _ := rfl
  out := lifeOut
  out_injective := lifeOut_injective
  out_wf := lifeOut_wf hA
  out_surj := lifeOut_surj
  out_act σ x := by
    rw [Subsingleton.elim σ (OrderIso.refl Life), layerAct_refl]
    rfl

/-- In the nominal reading. -/
def fsCarrier_lifeAny : FSCarrier Life Loc Val AnySupport := fsCarrier_life fun _ => trivial

/-- With supports at or above the cell. -/
def fsCarrier_lifeAbove : FSCarrier Life Loc Val SupportAbove :=
  fsCarrier_life fun _ _ h => absurd h (Finset.notMem_empty _)

end Life

end DenseCarrier

end
