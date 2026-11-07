import Core.Chain.MFrameK835N
import Core.Chain.LendExit835N
import Core.Chain.PoolN

/-!
# The typed tables at the world `KW`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md`. A row's table at the typed world (`tabNK`, its entries
`entNK`, its cancel obligations `finNK`), its values at a value relation `vr` (`ValRelOK`), read
through `erwpK`:

* **an entry's order**: every entry, and every entry of a cancel row, owes its continuation along
  `KW.Owed` (`ExtP` at the floor the stop chose);
* **the answer and the cancel obligation are read at the resumption world**, the payload at the
  stop's;
* **posts keep the floor** (`KW.PostK`): a run's values are posted at its own world. Along it a
  table allows the same stops (`tabLe_postK`), which `KW.Post` lowering the floor did not
  (`LendExit835N.not_tabLe_post_lower`).

A table carries a map `g` on worlds: its entries owe their continuation at `g y` for a resumption
world `y`, and its cancel runs are at `g y`'s view and floor. The lender's tables take `g = id`;
the borrowed run's tables inside a Mut Frame are indexed by the lender's worlds and take the lend's
world (`KW.lend`), which is how `erwpK_M_frameCR_KW` reads them. `tabNK vr g` is
`tabF (rdNv vr g δ) ()` (`tabF_N`), and at `vr = vN`, `g = id` it is `cN`'s table `tabN`
(`tabNK_vN`).

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

/-! ### The value relation a table reads -/

/-- A value relation: `vr A δ Θ k v ρ`, the value `v` of type `A` at the world `Θ`. -/
abbrev VRel : Type := VTy → LSub → LocTy → Nat → Val → WRes → Prop

/-- **What the typed tables read of their value relation**: closed in the index; a value of a
persistent type owns nothing; a lifetime variable `A` does not mention is not read; a value of a
type outliving a bound lies in the stratum of every lifetime below it; kept along `ExtR` at its
resource. `vN` meets it (`valRelOK_vN`). -/
structure ValRelOK (vr : VRel) : Prop where
  down : ∀ A δ Θ k v ρ, vr A δ Θ (k + 1) v ρ → vr A δ Θ k v ρ
  pers : ∀ A, A.Persistent → ∀ δ Θ k v ρ, vr A δ Θ k v ρ → ρ = PMap.empty
  extend : ∀ {xv : LifeVar} {A : VTy}, ¬ VFree xv A → ∀ (δ : LSub) (α : Life),
    vr A (δ.extend xv α) = vr A δ
  inStratum : ∀ {A : VTy} {bnd : Lifetime.Life}, VOutlives LifeCtx.empty bnd A →
    ∀ {δ : LSub} {α : Life}, LtLife δ bnd α → ∀ {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes},
      vr A δ Θ n v ρ → ρ.InStratum α
  extR : ∀ A δ {Θ Θ' : LocTy} n v ρ, Θ.ExtR Θ' ρ → vr A δ Θ n v ρ → vr A δ Θ' n v ρ

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

mutual
/-- **The table of a row's layers at the typed world**, its values at `vr`, at the stop's world
`x`: every entry owes its continuation at `g y` along `KW.Owed` from `g x`. It is
`tabF (rdNv vr g δ) ()` (`tabF_N`). -/
def tabNK (vr : VRel) (g : KW → KW) : CTy → LSub → KW → OpTabK KW
  | .eff m i q A B fin _ C, δ, x => extTabK m i
      (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ))
      (tabNK vr g C δ x)
  | _, _, _ => OpTabK.empty
/-- **The cancel obligation of a cancel row at the typed world**: `none` at `⊤`; otherwise the
cancel run at the row's `tabNK`. -/
def finNK (vr : VRel) (g : KW → KW) : CTy → LSub →
    Option (KW → Nat → List SRec → Expr → WProp)
  | .top, _ => none
  | .eff m i q A B fin _ C, δ => some (cancelOblK (ℍ := ℍ) g (fun x => extTabK m i
      (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ))
      (tabNK vr g C δ x)))
  | .ret _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .arr _ _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .amp _ _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .all _ _ _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
  | .nu _, _ => some (cancelOblK (ℍ := ℍ) g (fun _ => OpTabK.empty))
end

mutual
/-- **The lender's table at the typed world** (`tabR`): `tabNK`'s entries, every capturable one's
cancel run ending at `R`. -/
def tabRK (R : Nat → WProp) (vr : VRel) (g : KW → KW) : CTy → LSub → KW → OpTabK KW
  | .eff m i q A B fin _ C, δ, x => extTabK m i
      (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRK R vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ))
      (tabRK R vr g C δ x)
  | _, _, _ => OpTabK.empty
/-- The lender's cancel obligation at the typed world (`finR`). -/
def finRK (R : Nat → WProp) (vr : VRel) (g : KW → KW) : CTy → LSub →
    Option (KW → Nat → List SRec → Expr → WProp)
  | .top, _ => none
  | .eff m i q A B fin _ C, δ => some (cancelOblRK (ℍ := ℍ) g (fun x => extTabK m i
      (entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRK R vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ))
      (tabRK R vr g C δ x)) R)
  | .ret _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .arr _ _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .amp _ _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .all _ _ _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
  | .nu _, _ => some (cancelOblRK (ℍ := ℍ) g (fun _ => OpTabK.empty) R)
end

theorem finNK_eq (vr : VRel) (g : KW → KW) {F : CTy} (hF : F ≠ .top) (δ : LSub) :
    finNK (ℍ := ℍ) vr g F δ =
      some (cancelOblK (ℍ := ℍ) g (fun x => tabNK (ℍ := ℍ) vr g F δ x)) := by
  cases F <;> simp_all [finNK, tabNK]

theorem finRK_eq (R : Nat → WProp) (vr : VRel) (g : KW → KW) {F : CTy} (hF : F ≠ .top)
    (δ : LSub) :
    finRK (ℍ := ℍ) R vr g F δ =
      some (cancelOblRK (ℍ := ℍ) g (fun x => tabRK (ℍ := ℍ) R vr g F δ x) R) := by
  cases F <;> simp_all [finRK, tabRK]

/-- **An entry of `tabNK` is a layer's, and every `tabRK` has the layer's entry at the same
key.** -/
theorem tab_lookupNK : ∀ (F : CTy) {vr : VRel} {g : KW → KW} {δ : LSub} {x : KW}
    {m j : UInt32} {en : OpEntK KW},
    tabNK (ℍ := ℍ) vr g F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK (ℍ := ℍ) vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ) ∧
      ∀ (R : Nat → WProp) (g₂ : KW → KW) (δ₂ : LSub) (x₂ : KW),
        tabRK (ℍ := ℍ) R vr g₂ F δ₂ x₂ m j =
          some (entNK q B (fun k v ρ => vr A δ₂ x₂.Θ k v ρ)
            (fun y k v ρ => vr B δ₂ y.Θ k v ρ ∧ ConsistentX y.c ρ)
            (finRK (ℍ := ℍ) R vr g₂ fin δ₂)
            (fun f y ρ => (g₂ x₂).Owed f (g₂ y) ρ))
  | .eff m₀ i₀ q A B fin rc C, vr, g, δ, x, m, j, en, h => by
      simp only [tabNK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R g₂ δ₂ x₂ => by
          simp only [tabRK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupNK C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R g₂ δ₂ x₂ => by
          simp only [tabRK, extTabK, if_neg hmj]; exact hR R g₂ δ₂ x₂⟩
  | .ret _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h

/-- **Every entry of the lender's tables owes along `KW.Owed`** (`g = id`). -/
theorem tabNK_wk {vr : VRel} {F : CTy} {δ : LSub} {x : KW} {m j : UInt32} {en : OpEntK KW}
    (h : tabNK (ℍ := ℍ) vr id F δ x m j = some en) : ∀ f y ρ, en.wk f y ρ ↔ x.Owed f y ρ := by
  obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupNK F h
  exact fun f y ρ => Iff.rfl

/-! ### The Mut Frame's premises at the typed world -/

/-- **The callback's table at the typed world may be stopped at under a lend at `α ⊏ @bnd`**
(`tabN_lendOKCR_C` at `KW`): at every world, the answer read at every resumption world. -/
theorem tabNK_lendOKCR {vr : VRel} (hv : ValRelOK vr) {xv : LifeVar} {bnd : Lifetime.Life}
    {α : Life} {F : CTy} (hF : F.SuspendC xv bnd) (g : KW → KW) (δ : LSub)
    (hLt : LtLife δ bnd α) (x : KW) : (tabNK (ℍ := ℍ) vr g F (δ.extend xv α) x).LendOKCR α where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    obtain ⟨-, hA, -, hOA, -⟩ := layer_suspend F hF hL
    have hp' : vr A (δ.extend xv α) x.Θ k v ρ := hp
    rw [hv.extend hA] at hp'
    exact hv.inStratum hOA hLt hp'
  pb := fun m i en h y k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    obtain ⟨-, -, hB, -, hOB, -⟩ := layer_suspend F hF hL
    have hp' : vr B (δ.extend xv α) y.Θ k w ρ := hp.1
    rw [hv.extend hB] at hp'
    exact (hv.inStratum hOB hLt hp').mono (Life.down_sqsubset α).le

/-- **The callback's table and the lender's twin across the fold, at the typed world.** The
callback's entries, indexed by the lender's worlds, owe at the lend's world (`KW.lend`); the
lender's at its own. They agree but for the cancel obligations (`'x` is read by no layer's types);
a world the lend's order owes is one the callback's entry owes, and a world the lender's entry owes
is one `KW.Owed` owes. -/
theorem tabNK_foldTwin {vr : VRel} (hv : ValRelOK vr) {xv : LifeVar} {bnd : Lifetime.Life}
    {α : Life} {F : CTy} (hF : F.SuspendC xv bnd) (R : Nat → WProp)
    (δ : LSub) (l : Loc) (Fam : Nat → Val → SPropS Loc Val α) (x : KW) :
    ∀ m i en, tabNK (ℍ := ℍ) vr (·.lend l α Fam) F (δ.extend xv α) x m i = some en →
      ∃ en', tabRK (ℍ := ℍ) R vr id F δ x m i = some en' ∧
        en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        (en.abort = false →
          (∀ f z ρ, (x.lend l α Fam).Owed f (z.lend l α Fam) ρ → en.wk f z ρ) ∧
          (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)) := by
  intro m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNK F h
  obtain ⟨-, hA, hB, -, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R id δ x, rfl, rfl, ?_, ?_, rfl, fun _ => ⟨fun f z ρ hz => hz,
    fun f z ρ hz => hz⟩⟩
  · simp only [entNK, hv.extend hA δ α]
  · simp only [entNK, hv.extend hB δ α]

/-- **The lender's cancel obligations from the callback's, at the typed world** (`tabR_can` at
`KW`, the premise `CanFold`), by induction on how deep cancel rows nest. At a capturable entry, the
callback's cancel run at its cancel row's table, indexed by the lender's worlds at the lend's
world, framed by `erwpK_M_frame_cancelRunCR` at the cancel row's tables (`FoldTwin` by
`foldTwin_owed`), its own nested cancel obligations by the induction. -/
theorem tabRK_canK {vr : VRel} (hv : ValRelOK vr) {xv : LifeVar} {bnd : Lifetime.Life}
    {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) {l : Loc} {Fam : Nat → Val → SPropS Loc Val α}
    (hFam : DownFam α Fam) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd →
      CanFold (fun y : KW => y.Θ.FoldInv α)
        (fun x => tabNK (ℍ := ℍ) vr (·.lend l α Fam) F (δ.extend xv α) x)
        (fun x => tabRK (ℍ := ℍ) (claimR l α Fam) vr id F δ x) l α Fam := by
  intro d
  induction d with
  | zero =>
      intro F hd hF x _ m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupNK F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF x _ m i en en' h h' ha hql y hy k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw''
    hno hZ hZd hdZd hPk hW'' hkL hc
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
    (Ti := fun x => tabNK (ℍ := ℍ) vr (·.lend l α Fam) fin (δ.extend xv α) x)
    (To := fun x => tabRK (ℍ := ℍ) (claimR l α Fam) vr id fin δ x) hFam
    (fun x => tabNK_lendOKCR hv hfin _ δ hLt x) (ih fin hfd hfin)
    (fun x hx => foldTwin_owed hFam hx (tabNK_foldTwin hv hfin _ δ l Fam x))
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
claim, at its own world and floor. Every premise of `erwpK_M_frameCR_KW` is discharged: `LendOKCR`
(`tabNK_lendOKCR`), `CanFold` (`tabRK_canK`) and the twin across the fold (`tabNK_foldTwin`). -/
theorem erwpK_M_frameCR_tab {vr : VRel} (hv : ValRelOK vr) {V : KW → KW → Prop}
    {Φ : KW → LocFam} {xv : LifeVar}
    {bnd : Lifetime.Life} {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) {F : CTy}
    (hF : F.SuspendC xv bnd) {Q : KW → PostN} :
    KFrame (ℍ := ℍ) V Φ (fun y => y.Θ.FoldInv α) l α Fam
      (fun y => opTableK α (tabNK (ℍ := ℍ) vr (·.lend l α Fam) F (δ.extend xv α) y))
      (fun y => opTableRK y.lo (tabRK (ℍ := ℍ) (claimR l α Fam) vr id F δ y) (claimR l α Fam))
      (fun y => MFPost l α Fam (Q y)) Q :=
  erwpK_M_frameCR_KW hFam (fun x => tabNK_lendOKCR hv hF _ δ hLt x)
    (tabRK_canK hv hLt hFam F.cdepth F le_rfl hF)
    (fun x _ => tabNK_foldTwin hv hF _ δ l Fam x)

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

end BoCa.Fig16.LogRel.Core.Chain.SI

end
