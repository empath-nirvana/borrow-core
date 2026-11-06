import Core.Chain.MFrameK835N
import Core.Chain.LendExit835N
import Core.Chain.Restrict835N
import Core.Chain.PoolN

/-!
# The typed tables at the world `KW`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md`. A row's table at the typed world (`tabNK`, its entries
`entNK`, its cancel obligations `finNK`), read through `erwpK`:

* **an entry's order** (`KW.OwedS`): an entry at a scheduler name owes its continuation along
  `KW.Owed` (`ExtP` at the floor the stop chose); every other entry along `KW.OwedR` (`ExtR`, no
  floor), the order `vN`'s `U` reads (`scope-835-lendexit.md`). The entries of the cancel row of a
  scheduler entry owe along `KW.Owed` whatever their names: that cancel run is the scheduler's,
  at a table inside its own (`SchedOKNLe.fin`), and it runs inside the stopped continuation, under
  the lends live there;
* **the answer and the cancel obligation are read at the resumption world**, the payload at the
  stop's;
* **posts keep the floor** (`KW.PostK`): a run's values are posted at its own world. Along it a
  table allows the same stops (`tabLe_postK`), which `KW.Post` lowering the floor did not
  (`LendExit835N.not_tabLe_post_lower`).

A table carries a map `g` on worlds: its entries owe their continuation at `g y` for a resumption
world `y`, and its cancel runs are at `g y`'s view and floor. The lender's tables take `g = id`;
the borrowed run's tables inside a Mut Frame are indexed by the lender's worlds and take the lend's
world (`KW.lend`), which is how `erwpK_M_frameCR_KW` reads them.

At the typed world the Mut Frame's premises are discharged (`tabNK_lendOKCR`, `tabNK_foldTwin`,
`tabRK_canK`) and the frame stated at the typed tables (`erwpK_M_frameCR_tab`); the scheduler's
contract is restated at `erwpK` (`SchedOKNK`), `SchedOKN` its instance at one world
(`schedOKN_iff_K`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel (LtLife)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload clauseAt capTag)

/-! ### Posts keep the floor -/

/-- **A post's world at the typed world**: the run's own world. -/
def KW.PostK (x y : KW) : Prop := y = x

theorem KW.postK_refl (x : KW) : x.PostK x := rfl

theorem KW.PostK.trans {x y z : KW} (h₁ : x.PostK y) (h₂ : y.PostK z) : x.PostK z := by
  unfold KW.PostK at *; subst h₁ h₂; rfl

theorem KW.PostK.post {x y : KW} (h : x.PostK y) : x.Post y := by
  subst h; exact KW.post_refl _

/-- **Along a post every table allows the same stops**: `erwpK_shift`'s `hTV` at `KW.PostK`. -/
theorem tabLe_postK (Tb : KW → TableK KW) {x y : KW} (h : x.PostK y) : (Tb y).Le (Tb x) := by
  subst h; exact fun _ _ _ _ _ h => h

/-- **`erwpK_shift` at the typed world**, its premises discharged at `KW.PostK`. -/
theorem erwpK_shift_postK {Φ : KW → LocFam} {Tb : KW → TableK KW} (hTb : ∀ x, (Tb x).Local)
    {Q : KW → PostN} {x y : KW} (hxy : x.PostK y) {k N : Nat} (hk : k ≤ N) {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : erwpK (ℍ := ℍ) KW.PostK Φ Tb Q y k ls e ρ) :
    rwpG (ℍ := ℍ) (Φ x) (erwpPostK (KW.PostK x) (Tb x) Q (erwpCK (ℍ := ℍ) KW.PostK Φ Tb Q N))
      k ls e ρ :=
  erwpK_shift (fun _ _ _ h₁ h₂ => h₁.trans h₂) (fun _ _ h => by rw [h])
    (fun _ _ h => tabLe_postK Tb h) hTb hxy hk h

/-! ### An entry's order -/

/-- **The order of an entry at the name `m`**: along `KW.Owed` at a scheduler name, along
`KW.OwedR` at any other. -/
def KW.OwedS (S : UInt32 → Prop) (m : UInt32) (x : KW) (f : Life) (y : KW) (ρ : WRes) : Prop :=
  (S m → x.Owed f y ρ) ∧ (¬ S m → x.OwedR y ρ)

theorem KW.Owed.owedS {S : UInt32 → Prop} {m : UInt32} {x y : KW} {f : Life} {ρ : WRes}
    (h : x.Owed f y ρ) : x.OwedS S m f y ρ :=
  ⟨fun _ => h, fun _ => h.owedR⟩

theorem KW.OwedS.owed {S : UInt32 → Prop} {m : UInt32} {x y : KW} {f : Life} {ρ : WRes}
    (h : x.OwedS S m f y ρ) (hm : S m) : x.Owed f y ρ :=
  h.1 hm

/-- Both orders owe the worlds `KW.OwedR` reads at most. -/
theorem KW.OwedS.owedR {S : UInt32 → Prop} {m : UInt32} {x y : KW} {f : Life} {ρ : WRes}
    (h : x.OwedS S m f y ρ) : x.OwedR y ρ := by
  by_cases hm : S m
  · exact (h.1 hm).owedR
  · exact h.2 hm

/-- **A stop's own world is owed, at every floor and every name**. -/
theorem KW.owedS_self (S : UInt32 → Prop) (m : UInt32) {x : KW} (hΘ : x.Θ.OK) (f : Life)
    {ρ : WRes} (hc : ConsistentX x.c ρ) : x.OwedS S m f x ρ :=
  (KW.owed_self hΘ f hc).owedS

/-! ### The tables -/

variable {ι : Type}

/-- One more layer of a table over a world index: the first match wins. -/
def extTabK (n i : UInt32) (en : OpEntK ι) (T : OpTabK ι) : OpTabK ι :=
  fun m j => if m = n ∧ j = i then some en else T m j

/-- The table with no entry. -/
def OpTabK.empty : OpTabK ι := fun _ _ => none

theorem extTabK_some {n i m j : UInt32} {en en' : OpEntK ι} {T : OpTabK ι}
    (h : extTabK n i en T m j = some en') : (m = n ∧ j = i ∧ en' = en) ∨ T m j = some en' := by
  unfold extTabK at h
  split at h
  · rename_i hmj; exact .inl ⟨hmj.1, hmj.2, (Option.some.inj h).symm⟩
  · exact .inr h

/-- **An entry of a row's table at the typed world** (`entN`): abortive as Core's; the payload at
the stop's world; the answer, the cancel obligation and the order at the resumption world. -/
def entNK (q : Qual) (B : VTy) (PA : Nat → Val → WRes → Prop) (PB : KW → Nat → Val → WRes → Prop)
    (fin : Option (KW → Nat → List SRec → Expr → WProp)) (wk : Life → KW → WRes → Prop) :
    OpEntK KW where
  q := q
  abort := B.isZero && q != .lin
  PA := fun k _ v ρ => PA k v ρ
  PB := fun y k _ v ρ => PB y k v ρ
  fin := if capB q B then fin else none
  wc := extF
  wk := wk

/-- **The cancel run at the typed world** (`cancelOblN`): at the view and the floor of `g y`, its
stops at `T`'s entries. -/
def cancelOblK (g : KW → KW) (T : KW → OpTabK KW) : KW → Nat → List SRec → Expr → WProp :=
  fun y k ls e => erwpK (ℍ := ℍ) KW.PostK (fun z => (g z).Θ.view (g z).c)
    (fun z => cancelTabK (g z).lo (T z)) (fun _ _ _ _ _ => False) y k ls e

/-- **The cancel run ending at a claim** (`cancelOblRN`). -/
def cancelOblRK (g : KW → KW) (T : KW → OpTabK KW) (R : Nat → WProp) :
    KW → Nat → List SRec → Expr → WProp :=
  fun y k ls e => erwpK (ℍ := ℍ) KW.PostK (fun z => (g z).Θ.view (g z).c)
    (fun z => cancelTabRK (g z).lo (T z) R) (fun _ _ _ _ _ => False) y k ls e

/-- The cancel row of an entry at `m` under the scheduler names `S`: every name is a scheduler
name in the cancel row of a scheduler entry. -/
def finSched (S : UInt32 → Prop) (m : UInt32) : UInt32 → Prop := fun n => S m ∨ S n

mutual
/-- **The table of a row's layers at the typed world** (`tabN`), at the stop's world `x`: an
entry at `m` owes its continuation at `g y` along `KW.OwedS` from `g x`. -/
def tabNK (S : UInt32 → Prop) (g : KW → KW) : CTy → LSub → KW → OpTabK KW
  | .eff m i q A B fin _ C, δ, x => extTabK m i
      (entNK q B (fun k v ρ => vN (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ))
      (tabNK S g C δ x)
  | _, _, _ => OpTabK.empty
/-- **The cancel obligation of a cancel row at the typed world** (`finN`): `none` at `⊤`;
otherwise the cancel run at the row's `tabNK`. -/
def finNK (S : UInt32 → Prop) (g : KW → KW) : CTy → LSub →
    Option (KW → Nat → List SRec → Expr → WProp)
  | .top, _ => none
  | .eff m i q A B fin _ C, δ => some (cancelOblK (ℍ := ℍ) g (fun x => extTabK m i
      (entNK q B (fun k v ρ => vN (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ))
      (tabNK S g C δ x)))
  | .ret _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .arr _ _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .amp _ _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .all _ _ _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .nu _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
end

mutual
/-- **The lender's table at the typed world** (`tabR`): `tabNK`'s entries, every capturable one's
cancel run ending at `R`. -/
def tabRK (R : Nat → WProp) (S : UInt32 → Prop) (g : KW → KW) : CTy → LSub → KW → OpTabK KW
  | .eff m i q A B fin _ C, δ, x => extTabK m i
      (entNK q B (fun k v ρ => vN (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRK R (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ))
      (tabRK R S g C δ x)
  | _, _, _ => OpTabK.empty
/-- The lender's cancel obligation at the typed world (`finR`). -/
def finRK (R : Nat → WProp) (S : UInt32 → Prop) (g : KW → KW) : CTy → LSub →
    Option (KW → Nat → List SRec → Expr → WProp)
  | .top, _ => none
  | .eff m i q A B fin _ C, δ => some (cancelOblRK (ℍ := ℍ) g (fun x => extTabK m i
      (entNK q B (fun k v ρ => vN (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRK R (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ))
      (tabRK R S g C δ x)) R)
  | .ret _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .arr _ _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .amp _ _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .all _ _ _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .nu _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
end

theorem finNK_eq (S : UInt32 → Prop) (g : KW → KW) {F : CTy} (hF : F ≠ .top) (δ : LSub) :
    finNK (ℍ := ℍ) S g F δ = some (cancelOblK (ℍ := ℍ) g (fun x => tabNK (ℍ := ℍ) S g F δ x)) := by
  cases F <;> simp_all [finNK, tabNK]

theorem finRK_eq (R : Nat → WProp) (S : UInt32 → Prop) (g : KW → KW) {F : CTy} (hF : F ≠ .top)
    (δ : LSub) :
    finRK (ℍ := ℍ) R S g F δ =
      some (cancelOblRK (ℍ := ℍ) g (fun x => tabRK (ℍ := ℍ) R S g F δ x) R) := by
  cases F <;> simp_all [finRK, tabRK]

/-- **An entry of `tabNK` is a layer's, and every `tabRK` has the layer's entry at the same
key.** -/
theorem tab_lookupNK : ∀ (F : CTy) {S : UInt32 → Prop} {g : KW → KW} {δ : LSub} {x : KW}
    {m j : UInt32} {en : OpEntK KW},
    tabNK (ℍ := ℍ) S g F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vN (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK (ℍ := ℍ) (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ) ∧
      ∀ (R : Nat → WProp) (S₂ : UInt32 → Prop) (g₂ : KW → KW) (δ₂ : LSub) (x₂ : KW),
        tabRK (ℍ := ℍ) R S₂ g₂ F δ₂ x₂ m j =
          some (entNK q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ x₂.Θ k v ρ)
            (fun y k v ρ => vN (ℍ := ℍ) B δ₂ y.Θ k v ρ ∧ ConsistentX y.c ρ)
            (finRK (ℍ := ℍ) R (finSched S₂ m) g₂ fin δ₂)
            (fun f y ρ => (g₂ x₂).OwedS S₂ m f (g₂ y) ρ))
  | .eff m₀ i₀ q A B fin rc C, S, g, δ, x, m, j, en, h => by
      simp only [tabNK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R S₂ g₂ δ₂ x₂ => by
          simp only [tabRK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupNK C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R S₂ g₂ δ₂ x₂ => by
          simp only [tabRK, extTabK, if_neg hmj]; exact hR R S₂ g₂ δ₂ x₂⟩
  | .ret _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h

/-- **An entry at a scheduler name owes along `KW.Owed`** (the lender's tables, `g = id`). -/
theorem tabNK_wk_sched {S : UInt32 → Prop} {F : CTy} {δ : LSub} {x : KW} {m j : UInt32}
    {en : OpEntK KW} (h : tabNK (ℍ := ℍ) S id F δ x m j = some en) (hm : S m) :
    ∀ f y ρ, en.wk f y ρ ↔ x.Owed f y ρ := by
  obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupNK F h
  exact fun f y ρ => ⟨fun h => h.owed hm, fun h => h.owedS⟩

/-- **An entry at any other name owes along `KW.OwedR`**, so a stop there is one at every floor
bound (`contShareK_owedR_lo`) and owes its continuation at `U`'s futures
(`contShareK_owedR_U`). -/
theorem tabNK_wk_owedR {S : UInt32 → Prop} {F : CTy} {δ : LSub} {x : KW} {m j : UInt32}
    {en : OpEntK KW} (h : tabNK (ℍ := ℍ) S id F δ x m j = some en) (hm : ¬ S m) :
    ∀ f y ρ, en.wk f y ρ ↔ x.OwedR y ρ := by
  obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupNK F h
  exact fun f y ρ => ⟨fun h => h.2 hm, fun h => ⟨fun h' => absurd h' hm, fun _ => h⟩⟩

/-! ### The restriction on a row -/

/-- **A row whose resuming layers are at scheduler names** (`Row.SchedOnly` on a row type). -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.SchedOnly (S : UInt32 → Prop) : CTy → Prop
  | .eff m _ q _ B _ _ C => ((B.isZero && q != .lin) = false → S m) ∧ CTy.SchedOnly S C
  | _ => True

theorem _root_.BoCa.Fig16.LogRel.Core.CTy.schedOnly_effOf {S : UInt32 → Prop} {Sr : Row}
    (h : Sr.SchedOnly S) (R : VTy) : (CTy.effOf Sr R).SchedOnly S := by
  induction Sr with
  | nil => trivial
  | cons o Sr ih =>
      exact ⟨fun ha => h o (List.mem_cons_self ..) ha,
        ih fun o' ho' => h o' (List.mem_cons_of_mem _ ho')⟩

/-- A row whose layers are all at scheduler names. -/
theorem _root_.BoCa.Fig16.LogRel.Core.CTy.schedOnly_of_all {S : UInt32 → Prop} (hS : ∀ n, S n) :
    ∀ F : CTy, F.SchedOnly S
  | .eff _ _ _ _ _ _ _ C => ⟨fun _ => hS _, CTy.schedOnly_of_all hS C⟩
  | .ret _ | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => trivial

/-- **A resuming entry of a restricted row's table is at a scheduler name.** -/
theorem tabNK_sched {S : UInt32 → Prop} : ∀ {F : CTy}, F.SchedOnly S → ∀ {g : KW → KW} {δ : LSub}
    {x : KW} {m j : UInt32} {en : OpEntK KW}, tabNK (ℍ := ℍ) S g F δ x m j = some en →
    en.abort = false → S m
  | .eff m₀ i₀ q A B fin rc C, hS, g, δ, x, m, j, en, h, ha => by
      simp only [tabNK] at h
      rcases extTabK_some h with ⟨rfl, -, rfl⟩ | h
      · exact hS.1 ha
      · exact tabNK_sched hS.2 h ha
  | .ret _, _, _, _, _, _, _, _, h, _ => by simp [tabNK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, h, _ => by simp [tabNK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, h, _ => by simp [tabNK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, h, _ => by simp [tabNK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, h, _ => by simp [tabNK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, h, _ => by simp [tabNK, OpTabK.empty] at h

/-! ### The Mut Frame's premises at the typed world -/

/-- **The callback's table at the typed world may be stopped at under a lend at `α ⊏ @bnd`**
(`tabN_lendOKCR_C` at `KW`): at every world, the answer read at every resumption world. -/
theorem tabNK_lendOKCR {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {F : CTy}
    (hF : F.SuspendC xv bnd) (S : UInt32 → Prop) (g : KW → KW) (δ : LSub)
    (hLt : LtLife δ bnd α) (x : KW) : (tabNK (ℍ := ℍ) S g F (δ.extend xv α) x).LendOKCR α where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    obtain ⟨-, hA, -, hOA, -⟩ := layer_suspend F hF hL
    have hp' : vN (ℍ := ℍ) A (δ.extend xv α) x.Θ k v ρ := hp
    rw [vN_extend_of_not_free hA] at hp'
    exact vN_inStratum_bnd hOA hLt hp'
  pb := fun m i en h y k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    obtain ⟨-, -, hB, -, hOB, -⟩ := layer_suspend F hF hL
    have hp' : vN (ℍ := ℍ) B (δ.extend xv α) y.Θ k w ρ := hp.1
    rw [vN_extend_of_not_free hB] at hp'
    exact (vN_inStratum_bnd hOB hLt hp').mono (Life.down_sqsubset α).le

/-- **The callback's table and the lender's twin across the fold, at the typed world.** The
callback's entries, indexed by the lender's worlds, owe at the lend's world (`KW.lend`); the
lender's at its own. They agree but for the cancel obligations (`'x` is read by no layer's types),
a world the lend's order owes is one the callback's entry owes, and, the row's resuming layers
being at scheduler names (`hS`), a world the lender's entry owes is one `KW.Owed` owes. -/
theorem tabNK_foldTwin {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {F : CTy}
    (hF : F.SuspendC xv bnd) {S : UInt32 → Prop} (hS : F.SchedOnly S) (R : Nat → WProp)
    (δ : LSub) (l : Loc) (Fam : Nat → Val → SPropS Loc Val α) (x : KW) :
    ∀ m i en, tabNK (ℍ := ℍ) S (·.lend l α Fam) F (δ.extend xv α) x m i = some en →
      ∃ en', tabRK (ℍ := ℍ) R S id F δ x m i = some en' ∧
        en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        (en.abort = false →
          (∀ f z ρ, (x.lend l α Fam).Owed f (z.lend l α Fam) ρ → en.wk f z ρ) ∧
          (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)) := by
  intro m i en h
  have hm := tabNK_sched hS h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNK F h
  obtain ⟨-, hA, hB, -, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R S id δ x, rfl, rfl, ?_, ?_, rfl, fun ha => ⟨fun f z ρ hz => hz.owedS,
    fun f z ρ hz => hz.owed (hm ha)⟩⟩
  · simp only [entNK, vN_extend_of_not_free (ℍ := ℍ) hA δ α]
  · simp only [entNK, vN_extend_of_not_free (ℍ := ℍ) hB δ α]

/-- **The lender's cancel obligations from the callback's, at the typed world** (`tabR_can` at
`KW`, the premise `CanFold`), by induction on how deep cancel rows nest. At a capturable entry, the
callback's cancel run at its cancel row's table, indexed by the lender's worlds at the lend's
world, framed by `erwpK_M_frame_cancelRunCR` at the cancel row's tables (`FoldTwin` by
`foldTwin_owed`, the cancel row being the scheduler's, `finSched`), its own nested cancel
obligations by the induction. -/
theorem tabRK_canK {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub}
    (hLt : LtLife δ bnd α) {l : Loc} {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd → ∀ (S : UInt32 → Prop),
      F.SchedOnly S →
      CanFold (fun y : KW => y.Θ.FoldInv α)
        (fun x => tabNK (ℍ := ℍ) S (·.lend l α Fam) F (δ.extend xv α) x)
        (fun x => tabRK (ℍ := ℍ) (claimR l α Fam) S id F δ x) l α Fam := by
  intro d
  induction d with
  | zero =>
      intro F hd hF S _ x _ m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupNK F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF S hS x _ m i en en' h h' ha hql y hy k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw''
    hno hZ hZd hdZd hPk hW'' hkL hc
  have hm := tabNK_sched hS h ha
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNK F h
  simp only at h'
  rw [hR] at h'
  cases Option.some.inj h'
  have hcap : capB q B = true := by
    simp only [entNK] at ha hql
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨hql, ?_⟩
    cases hB : B.isZero
    · rfl
    · simp [hB, hql] at ha
  have hfin := (layer_suspend F hF hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  have hfS : fin.SchedOnly (finSched S m) := CTy.schedOnly_of_all (fun _ => Or.inl hm) fin
  intro P' hP'
  simp only [entNK, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finRK] at hP'
  rw [finRK_eq _ _ _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hc _ (finNK_eq _ _ htop _)
  have hM := erwpK_M_frame_cancelRunCR (ℍ := ℍ) (V := KW.PostK)
    (Φ := fun z => z.Θ.view z.c) (Inv := fun y : KW => y.Θ.FoldInv α) (flI := fun _ => α)
    (flO := fun z => z.lo)
    (Ti := fun x => tabNK (ℍ := ℍ) (finSched S m) (·.lend l α Fam) fin (δ.extend xv α) x)
    (To := fun x => tabRK (ℍ := ℍ) (claimR l α Fam) (finSched S m) id fin δ x) hFam
    (fun x => tabNK_lendOKCR hfin _ _ δ hLt x) (ih fin hfd hfin _ hfS)
    (fun x hx => foldTwin_owed hFam hx (tabNK_foldTwin hfin hfS _ δ l Fam x))
  refine hM k k le_rfl y hy ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  have hΦ : (fun z : KW => (z.Θ.view z.c).set l α Fam) =
      fun z : KW => (z.lend l α Fam).Θ.view (z.lend l α Fam).c :=
    funext fun z => (KW.lend_view z l α Fam).symm
  rw [hΦ]
  exact erwpK_garbage hZ hno hin

/-- **The Mut Frame at the typed tables.** The callback's table is the row's `tabNK` at the lend's
world, indexed by the lender's worlds; the lender's is its twin `tabRK`, ending at the lend's
claim, at its own world and floor. The row's resuming layers are at scheduler names (`hS`, the
restriction's (S1)). Every premise of `erwpK_M_frameCR_KW` is discharged: `LendOKCR`
(`tabNK_lendOKCR`), `CanFold` (`tabRK_canK`) and the twin across the fold (`tabNK_foldTwin`). -/
theorem erwpK_M_frameCR_tab {V : KW → KW → Prop} {Φ : KW → LocFam} {xv : LifeVar}
    {bnd : Lifetime.Life} {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) {F : CTy}
    (hF : F.SuspendC xv bnd) {S : UInt32 → Prop} (hS : F.SchedOnly S) {Q : KW → PostN} :
    KFrame (ℍ := ℍ) V Φ (fun y => y.Θ.FoldInv α) l α Fam
      (fun y => opTableK α (tabNK (ℍ := ℍ) S (·.lend l α Fam) F (δ.extend xv α) y))
      (fun y => opTableRK y.lo (tabRK (ℍ := ℍ) (claimR l α Fam) S id F δ y) (claimR l α Fam))
      (fun y => MFPost l α Fam (Q y)) Q :=
  erwpK_M_frameCR_KW hFam (fun x => tabNK_lendOKCR hF S _ δ hLt x)
    (tabRK_canK hLt hFam F.cdepth F le_rfl hF S hS)
    (fun x _ => tabNK_foldTwin hF hS _ δ l Fam x)

/-! ### The scheduler's contract at `erwpK` -/

/-- One table's entries are another's. -/
def OpTabK.Sub (T T' : OpTabK ι) : Prop := ∀ n i en, T n i = some en → T' n i = some en

/-- **The continuation a clause receives, at `erwpK`** (`KapRelN`): the stopped run's Kripke stop.
It owes, at a floor it chose below `lo`, at every world `y` its entry allows there: the resumed run
at `y` for every answer read at `y`, and a capturable entry's cancel run at `y`, at the floor of
each world it reaches. -/
def KapRelK (V : ι → ι → Prop) (Φ : ι → LocFam) (fl : ι → Life) (Tb : ι → TableK ι)
    (Q : ι → PostN) (en : OpEntK ι) (lo : Life) (Tc : Option (ι → OpTabK ι)) (k : Nat)
    (ls : List SRec) (κ : Val) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∃ f, f ≤ lo ∧ ∀ y, en.wk f y ρ → ∀ ls', en.wc ls ls' ρ → ∀ k', k' < k →
    (∀ w : Val, (en.PB y k' ls' w ─⋆
      erwpK (ℍ := ℍ) V Φ Tb Q y k' ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) ρ) ∧
    (en.q ≠ .lin → ∀ Tk, Tc = some Tk →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tk z)) (fun _ => unitPost) y k' ls'
        (.app κ.1 (.val (Val.inj₂ .unit))) ρ)

/-- **The scheduler's contract at `erwpK`, at the stops up to `N`** (`SchedOKNLe`), at every
world `x`: the table's conditions; a cancellable entry's cancel obligation a cancel run, read at
the resumption world, at a table inside the scheduler's; the return clause and every operation's
clause at the empty table, each stopped task received as its Kripke stop (`KapRelK`) at a floor
the clause does not know. -/
structure SchedOKNLeK (V : ι → ι → Prop) (Φ : ι → LocFam) (fl : ι → Life) (N : Nat)
    (T : ι → OpTabK ι) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : ι → PostN) : Prop where
  down : ∀ x, (T x).Down
  wcl : ∀ x n i en, T x n i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
    en.wc ls ls' ρ → en.wc ls ls' ρ₁
  names : ∀ x m i, m ≠ n₀ → T x m i = none
  tags : ∀ x i en, T x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag
  fin : ∀ x i en, T x n₀ i = some en → en.abort = false → en.q ≠ .lin →
    ∃ T₁ : ι → OpTabK ι, en.fin = some (fun y k ls e => erwpK (ℍ := ℍ) V Φ
      (fun z => cancelTabK (fl z) (T₁ z)) (fun _ _ _ _ _ => False) y k ls e) ∧
      ∀ z, (T₁ z).Sub (T z)
  wc : ∀ x i en, T x n₀ i = some en → ∀ (ls ls' : List SRec) (ρ : WRes),
    (∀ s, s ∈ ls' ↔ s ∈ ls) → en.wc ls ls' ρ
  qdown : ∀ x, (Qout x).Down
  ret : ∀ x k, k ≤ N → ∀ ls v ρ, Qin x k ls v ρ →
    erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) OpTabK.empty) Qout x k ls
      (.app (.val hr) (.val v)) ρ
  op : ∀ x i en, T x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
    (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
      (en.PA k ls v ⋆ KapRelK (ℍ := ℍ) V Φ fl (fun z => opTableK (fl z) OpTabK.empty) Qout en
        (fl x) (some T) k ls κ) ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) OpTabK.empty) Qout x k ls
        (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
    (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) OpTabK.empty) Qout x k ls
        (.app (.val c) (.val v)) ρ)

/-- **The scheduler's contract at `erwpK`, at every stop index** (`SchedOKN`). -/
def SchedOKNK (V : ι → ι → Prop) (Φ : ι → LocFam) (fl : ι → Life) (T : ι → OpTabK ι)
    (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : ι → PostN) : Prop :=
  ∀ N, SchedOKNLeK (ℍ := ℍ) V Φ fl N T n₀ qs hr hs Qin Qout

/-- **The scheduler's contract at the typed world**: the location family the world's view, posts
at the run's world, each world's floor, the scheduler's table at every world. -/
abbrev SchedOKNKW (T : KW → OpTabK KW) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : KW → PostN) :
    Prop :=
  SchedOKNK (ℍ := ℍ) KW.PostK (fun x => x.Θ.view x.c) (fun x => x.lo) T n₀ qs hr hs Qin Qout

/-! #### At one world -/

theorem liftTabK_empty : liftTabK OpTabN.empty = (OpTabK.empty : OpTabK Unit) := by
  funext m i; simp [liftTabK, OpTabN.empty, OpTabK.empty]

theorem erwp_empty_eq_K (lo : Life) (Φ : LocFam) (Q : PostN) (n : Nat) (ls : List SRec) (e : Expr) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e =
      erwpK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => opTableK lo OpTabK.empty)
        (fun _ => Q) () n ls e := by
  rw [erwp_opTableN_eq_erwpK lo, liftTabK_empty]

theorem kapRelK_lift_iff (lo : Life) (Φ : LocFam) (Q : PostN) (en : OpEntN) (Tc : Option OpTabN)
    (k : Nat) (ls : List SRec) (κ : Val) (ρ : WRes) :
    KapRelK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => lo)
        (fun _ => opTableK lo OpTabK.empty) (fun _ => Q) (liftEntK en) lo
        (Tc.map (fun T _ => liftTabK T)) k ls κ ρ ↔
      KapRelN (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q en Tc k ls κ ρ := by
  constructor
  · rintro ⟨hu, f, -, h⟩
    refine ⟨hu, fun ls' he k' hk' => ⟨fun w σ₁ σ₂ hB hc => ?_, fun hq Tk hTk => ?_⟩⟩
    · have := (h () trivial ls' he k' hk').1 w σ₁ σ₂ hB hc
      rw [erwp_empty_eq_K lo]; exact this
    · have := (h () trivial ls' he k' hk').2 hq (fun _ => liftTabK Tk) (by rw [hTk]; rfl)
      rw [erwp_opTableN_eq_erwpK lo]; exact this
  · rintro ⟨hu, h⟩
    refine ⟨hu, lo, le_rfl, fun _ _ ls' he k' hk' => ⟨fun w σ₁ σ₂ hB hc => ?_,
      fun hq Tk hTk => ?_⟩⟩
    · have := (h ls' he k' hk').1 w σ₁ σ₂ hB hc
      rw [erwp_empty_eq_K lo] at this; exact this
    · cases Tc with
      | none => cases hTk
      | some T₀ =>
          cases Option.some.inj hTk
          have := (h ls' he k' hk').2 hq T₀ rfl
          rw [erwp_opTableN_eq_erwpK lo] at this; exact this

theorem cancelOblN_eq_K (lo : Life) (Φ : LocFam) (T : OpTabN) :
    (fun (_ : Unit) k ls e => cancelOblN (ℍ := ℍ) Φ T k ls e) =
      fun y k ls e => erwpK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ)
        (fun z => cancelTabK ((fun _ => lo) z) ((fun _ => liftTabK T) z))
        (fun _ _ _ _ _ => False) y k ls e := by
  funext y k ls e
  cases y
  exact erwp_eq_erwpK_of (cancelTabK_lift lo T) Φ _ k ls e

/-- **`SchedOKNLe` is `SchedOKNLeK` at one world**, at any floor. -/
theorem schedOKNLe_iff_K (lo : Life) (Φ : LocFam) (N : Nat) (T : OpTabN) (n₀ : UInt32)
    (qs hr hs : Val) (Qin Qout : PostN) :
    SchedOKNLeK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => lo) N (fun _ => liftTabK T) n₀
        qs hr hs (fun _ => Qin) (fun _ => Qout) ↔
      SchedOKNLe (ℍ := ℍ) Φ N T n₀ qs hr hs Qin Qout := by
  constructor
  · intro h
    refine ⟨⟨fun n i en hT => (h.down ()).pa n i _ (liftTabK_of_some hT),
      fun n i en P hT hP k ls e ρ hk => ?_, fun n i en hT => h.wcl () n i _ (liftTabK_of_some hT)⟩,
      fun m i hm => ?_, fun i en hT => h.tags () i _ (liftTabK_of_some hT),
      fun i en hT ha hq => ?_, fun i en hT => h.wc () i _ (liftTabK_of_some hT), h.qdown (),
      fun k hk ls v ρ hq => ?_, fun i en hT => ?_⟩
    · exact (h.down ()).fin n i _ (fun _ => P) (liftTabK_of_some hT)
        (by simp [liftEntK, hP]) () k ls e ρ hk
    · have := h.names () m i hm
      simpa [liftTabK] using this
    · obtain ⟨T₁, hf, hsub⟩ := h.fin () i _ (liftTabK_of_some hT) ha hq
      classical
      let T₂ : OpTabN := fun m j => if (T₁ () m j).isSome then T m j else none
      have hT₂ : liftTabK T₂ = T₁ () := by
        funext m j
        cases h₁ : T₁ () m j with
        | none => simp [T₂, liftTabK, h₁]
        | some e =>
            have h2 := hsub () m j e h₁
            show (T₂ m j).map liftEntK = some e
            simp only [T₂, h₁, Option.isSome_some, if_true]
            exact h2
      refine ⟨T₂, ?_, fun m j e he => ?_⟩
      · simp only [liftEntK, Option.map_eq_some_iff] at hf
        obtain ⟨P₀, hP₀, hPe⟩ := hf
        rw [hP₀]
        congr 1
        have := congrFun hPe ()
        have hT₁ : T₁ = fun _ => liftTabK T₂ := funext fun u => by cases u; exact hT₂.symm
        rw [hT₁] at this
        rw [this]
        funext k ls e
        simp only [cancelOblN]
        exact (erwp_eq_erwpK_of (cancelTabK_lift lo T₂) Φ _ k ls e).symm
      · simp only [T₂] at he
        split_ifs at he
        exact he
    · rw [erwp_empty_eq_K lo]; exact h.ret () k hk ls v ρ hq
    · obtain ⟨c, hc, h₁, h₂⟩ := h.op () i _ (liftTabK_of_some hT)
      refine ⟨c, hc, fun ha k hk ls v κ ρ hp => ?_, fun ha k hk ls v ρ hp => ?_⟩
      · obtain ⟨ρa, ρk, hcak, hA, hK⟩ := hp
        have := h₁ ha k hk ls v κ ρ ⟨ρa, ρk, hcak, hA,
          (kapRelK_lift_iff lo Φ Qout en (some T) k ls κ ρk).mpr hK⟩
        rw [erwp_empty_eq_K lo]; exact this
      · rw [erwp_empty_eq_K lo]; exact h₂ ha k hk ls v ρ hp
  · intro h
    refine ⟨fun _ => ⟨fun n i en hT => ?_, fun n i en P hT hP => ?_⟩,
      fun _ n i en hT => ?_, fun _ m i hm => by simp [liftTabK, h.names m i hm],
      fun _ i en hT => ?_, fun _ i en hT ha hq => ?_, fun _ i en hT => ?_, fun _ => h.qdown,
      fun _ k hk ls v ρ hq => ?_, fun _ i en hT => ?_⟩
    · obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      exact h.down.pa n i en₀ h₀
    · obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      simp only [liftEntK, Option.map_eq_some_iff] at hP
      obtain ⟨P₀, hP₀, rfl⟩ := hP
      exact fun y k ls e ρ hk => h.down.fin n i en₀ P₀ h₀ hP₀ k ls e ρ hk
    · obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      exact h.down.wcl n i en₀ h₀
    · obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      exact h.tags i en₀ h₀
    · obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      obtain ⟨T₁, hf, hsub⟩ := h.fin i en₀ h₀ ha hq
      refine ⟨fun _ => liftTabK T₁, ?_, fun _ m j e he => ?_⟩
      · simp only [liftEntK, hf, Option.map_some]
        rw [cancelOblN_eq_K lo Φ T₁]
      · obtain ⟨e₀, he₀, rfl⟩ := liftTabK_some he
        exact liftTabK_of_some (hsub m j e₀ he₀)
    · obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      exact h.wc i en₀ h₀
    · have := h.ret k hk ls v ρ hq
      rw [erwp_empty_eq_K lo] at this; exact this
    · obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
      obtain ⟨c, hc, h₁, h₂⟩ := h.op i en₀ h₀
      refine ⟨c, hc, fun ha k hk ls v κ ρ hp => ?_, fun ha k hk ls v ρ hp => ?_⟩
      · obtain ⟨ρa, ρk, hcak, hA, hK⟩ := hp
        have := h₁ ha k hk ls v κ ρ ⟨ρa, ρk, hcak, hA,
          (kapRelK_lift_iff lo Φ Qout en₀ (some T) k ls κ ρk).mp hK⟩
        rw [erwp_empty_eq_K lo] at this; exact this
      · have := h₂ ha k hk ls v ρ hp
        rw [erwp_empty_eq_K lo] at this; exact this

/-- **`SchedOKN` is `SchedOKNK` at one world**, at any floor. -/
theorem schedOKN_iff_K (lo : Life) (Φ : LocFam) (T : OpTabN) (n₀ : UInt32) (qs hr hs : Val)
    (Qin Qout : PostN) :
    SchedOKNK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => lo) (fun _ => liftTabK T) n₀
        qs hr hs (fun _ => Qin) (fun _ => Qout) ↔
      SchedOKN (ℍ := ℍ) Φ T n₀ qs hr hs Qin Qout :=
  ⟨fun h N => (schedOKNLe_iff_K lo Φ N T n₀ qs hr hs Qin Qout).mp (h N),
    fun h N => (schedOKNLe_iff_K lo Φ N T n₀ qs hr hs Qin Qout).mpr (h N)⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
