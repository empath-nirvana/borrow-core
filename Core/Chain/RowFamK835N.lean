import Core.Chain.TabKW835N2
import Core.Chain.MechK835N5
import Core.Chain.Then835N

/-!
# A row's table over a world index  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §9. The table of a row's layers (`tabF`), its cancel
obligations (`finF`) and its entries (`RowRd.ent`), over any world index, read through `erwpK`.
How the table reads a world is a record (`RowRd`):

* the payload at the stop's world, the answer and its view at the resumption world;
* the worlds an entry at a name owes its continuation at (`wk`), under a *mode* `μ`;
* the mode of a capturable entry's cancel row (`sub`), and an order on modes (`le`) along which
  an entry owes at fewer worlds;
* the cancel runs' location family, floor, post order and the worlds they run at (`Inv`).

The cancel-row structure (`PendLe`, `ThenLe`) and the recursion on `CTy` are `tabN`'s. Two
instances:

* **one world** (`rdU`): every entry owes at the one world, one mode; `tabF` is `tabN` lifted
  (`tabF_unit`, `finF_unit`);
* **the typed world** (`rdKW`): the mode is the scheduler names, an entry at `m` owes along
  `KW.OwedS` from `g x`, its cancel row's mode `finSched`; `tabF` is `tabNK` (`tabF_KW`,
  `finF_KW`).

The interface lemmas (`tabF_effOf_find`, `tabF_rowOf`, `tabF_find_sig`, `tabF_rowOf_find`,
`entF_fin_cancel`, `entF_fin_of`, `errOkF_of_sub`, `tabF_rowLe_entry`, `finF_mono`) are `tabN`'s,
proved once over the record. E5 (`tabF_ctxClosed`) is proved here and read at `KW`
(`tabNK_ctxClosed`).

A world's location family is downward closed only at the worlds `Inv` holds at, which every world
an entry owes at satisfies (`RowRd.OK.wkInv`). So the tables' closure in the index and under a
plain context is read at those worlds (`OpTabK.DownI`, `OpTabK.CtxClosedI`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

variable {ι M : Type}

/-! ### Closure read at the worlds an invariant holds at -/

theorem cancelTabK_downI {Inv : ι → Prop} {lo : Life} {T : OpTabK ι} (hT : T.DownI Inv) :
    (cancelTabK lo T).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, err, hp⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk => (hcont y hy ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP y (hT.wkI _ _ _ h₃ f y ρk hy) _ _ _ _
          ((hcont y hy ls' he).2 hq P hP)⟩⟩⟩
  · obtain ⟨hc, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hp
    refine Or.inr ⟨K, err, pure_sep_mk hc ⟨τa, τb, hcab, ?_, hnb⟩⟩
    cases err with
    | none => exact he
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨hh, hPA, hn⟩ := pure_sep_iff.mp he
        exact ⟨m, j, w, en, pure_sep_mk hh ⟨hT.pa _ _ _ hh.2.1 _ _ _ _ hPA, hn⟩⟩

/-! ### How a row's table reads a world -/

/-- **How a row's table reads a world.** `Θ`/`c`: the location typing and view a world reads
values at; `wk μ m x f y ρ`: under the mode `μ`, an entry at the name `m` of the table at `x`, at
the floor `f`, owes its continuation at `y` at the share `ρ`; `sub μ m`: the mode of the cancel row
of an entry at `m`; `le`: the order on modes; `V`, `Φ`, `fl`: the post order, location family and
floor bound of the runs at the table; `Inv`: the worlds those runs are read at. -/
structure RowRd (ι M : Type) where
  δ : LSub
  Θ : ι → LocTy
  c : ι → Loc → Option Life
  wk : M → UInt32 → ι → Life → ι → WRes → Prop
  sub : M → UInt32 → M
  le : M → M → Prop
  V : ι → ι → Prop
  Φ : ι → LocFam
  fl : ι → Life
  Inv : ι → Prop

/-- **What the interface needs of a reading.** Every world an entry owes at is one the runs are
read at, and the location family is downward closed there; an entry's order passes to a part of
a valid share; a cancel row's mode is above the entry's, and `sub` is monotone; an entry at a
higher mode owes at fewer worlds; a run's values are posted at its own world. -/
structure RowRd.OK (R : RowRd ι M) : Prop where
  wkInv : ∀ μ m x f y ρ, R.wk μ m x f y ρ → R.Inv y
  ΦDown : ∀ x, R.Inv x → (R.Φ x).Down
  wkLeft : ∀ μ m x f y (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → ResU.Valid ρ → R.wk μ m x f y ρ →
    R.wk μ m x f y ρ₁
  le_refl : ∀ μ, R.le μ μ
  le_trans : ∀ μ₁ μ₂ μ₃, R.le μ₁ μ₂ → R.le μ₂ μ₃ → R.le μ₁ μ₃
  le_sub : ∀ μ m, R.le μ (R.sub μ m)
  sub_mono : ∀ μ μ' m, R.le μ μ' → R.le (R.sub μ m) (R.sub μ' m)
  wk_anti : ∀ μ μ' m x f y ρ, R.le μ μ' → R.wk μ' m x f y ρ → R.wk μ m x f y ρ
  Veq : ∀ x y, R.V x y → y = x

/-- **A value at a part of a stop's share is one at every world the stop owes**: the payload
reading carried along an entry's order (Core's `errOk_local`, the error carried along `Ext`). -/
def RowRd.PayExt (R : RowRd ι M) : Prop :=
  ∀ μ m x f y (ρa ρb ρ : WRes), ResU.CompS ρa ρb ρ → R.wk μ m x f y ρ →
    ∀ (A : VTy) k v, vN (ℍ := ℍ) A R.δ (R.Θ x) k v ρa → vN (ℍ := ℍ) A R.δ (R.Θ y) k v ρa

namespace RowRd

/-- **An entry of a row's table** (`entN`, `entNK`): abortive as Core's; the payload at the stop's
world; the answer and the order at the resumption world; resumed under `extF`. -/
def ent (R : RowRd ι M) (μ : M) (m : UInt32) (q : Qual) (A B : VTy)
    (fin : Option (ι → Nat → List SRec → Expr → WProp)) (x : ι) : OpEntK ι where
  q := q
  abort := B.isZero && q != .lin
  PA := fun k _ v ρ => vN (ℍ := ℍ) A R.δ (R.Θ x) k v ρ
  PB := fun y k _ v ρ => vN (ℍ := ℍ) B R.δ (R.Θ y) k v ρ ∧ ConsistentX (R.c y) ρ
  fin := if capB q B then fin else none
  wc := extF
  wk := R.wk μ m x

/-- **The cancel run at a table** (`cancelOblN`, `cancelOblK`). -/
def canc (R : RowRd ι M) (T : ι → OpTabK ι) : ι → Nat → List SRec → Expr → WProp :=
  fun y k ls e => erwpK (ℍ := ℍ) R.V R.Φ (fun z => cancelTabK (R.fl z) (T z))
    (fun _ _ _ _ _ => False) y k ls e

end RowRd

mutual
/-- **The table of a row's layers over a world index** (`tabN`, `tabNK`): an entry at `m` under
the mode `μ`, its cancel row's under `sub μ m`. -/
def tabF (R : RowRd ι M) (μ : M) : CTy → ι → OpTabK ι
  | .eff m i q A B fin _ C, x => extTabK m i
      (R.ent (ℍ := ℍ) μ m q A B (finF R (R.sub μ m) fin) x) (tabF R μ C x)
  | _, _ => OpTabK.empty
/-- **The cancel obligation of a cancel row over a world index** (`finN`, `finNK`): `none` at `⊤`;
otherwise the cancel run at the row's table. -/
def finF (R : RowRd ι M) (μ : M) : CTy → Option (ι → Nat → List SRec → Expr → WProp)
  | .top => none
  | .eff m i q A B fin _ C => some (R.canc (ℍ := ℍ) (fun x => extTabK m i
      (R.ent (ℍ := ℍ) μ m q A B (finF R (R.sub μ m) fin) x) (tabF R μ C x)))
  | .ret _ => some (R.canc (ℍ := ℍ) (fun _ => OpTabK.empty))
  | .arr _ _ => some (R.canc (ℍ := ℍ) (fun _ => OpTabK.empty))
  | .amp _ _ => some (R.canc (ℍ := ℍ) (fun _ => OpTabK.empty))
  | .all _ _ _ => some (R.canc (ℍ := ℍ) (fun _ => OpTabK.empty))
  | .nu _ => some (R.canc (ℍ := ℍ) (fun _ => OpTabK.empty))
end

/-! ### The typed world -/

/-- **The typed world's reading** (`tabNK`): values at the world's location typing and view; an
entry at `m` owes along `KW.OwedS` from `g x` to `g y`; a cancel row's mode is `finSched`; modes
ordered by inclusion; the cancel runs at `g`'s view and floor, posted at their own world, read at
the worlds whose location typing under `g` is downward closed. -/
def rdKW (g : KW → KW) (δ : LSub) : RowRd KW (UInt32 → Prop) where
  δ := δ
  Θ := fun x => x.Θ
  c := fun x => x.c
  wk := fun S m x f y ρ => (g x).OwedS S m f (g y) ρ
  sub := finSched
  le := fun S S' => ∀ n, S n → S' n
  V := KW.PostK
  Φ := fun z => (g z).Θ.view (g z).c
  fl := fun z => (g z).lo
  Inv := fun z => (g z).Θ.Down

theorem rdKW_ok (g : KW → KW) (δ : LSub) : (rdKW g δ).OK where
  wkInv := fun S m x f y ρ h => by
    by_cases hm : S m
    · exact (h.1 hm).2.1.1
    · exact (h.2 hm).2.1.1
  ΦDown := fun x hx => LocTy.view_down hx (g x).c
  wkLeft := fun _ _ _ _ _ _ _ _ hc hv h => KW.OwedS.left hc hv h
  le_refl := fun _ _ h => h
  le_trans := fun _ _ _ h₁ h₂ n h => h₂ n (h₁ n h)
  le_sub := fun _ _ _ h => Or.inr h
  sub_mono := fun _ _ _ h n hn => hn.elim (fun h' => Or.inl (h _ h')) (fun h' => Or.inr (h _ h'))
  wk_anti := fun S S' m x f y ρ hle h =>
    ⟨fun hm => h.1 (hle m hm), fun _ => h.owedR⟩
  Veq := fun _ _ h => h

/-- Both orders make the resumption world's view consistent with the share. -/
theorem KW.OwedS.consistent {S : UInt32 → Prop} {m : UInt32} {x y : KW} {f : Life} {ρ : WRes}
    (h : x.OwedS S m f y ρ) : ConsistentX y.c ρ := by
  by_cases hm : S m
  · exact (h.1 hm).2.2.1
  · exact (h.2 hm).2.2

/-- **The payload reading along the typed order** at the lender's tables: the order is `ExtR` at
the share (`KW.OwedS.extR`), so at a part of it, along which `𝒱⟦A⟧` is kept (`vN_extR`). -/
theorem rdKW_payExt (δ : LSub) : (rdKW id δ).PayExt (ℍ := ℍ) := by
  intro S m x f y ρa ρb ρ hc hy A k v hv
  exact vN_extR A δ k v ρa ((KW.OwedS.extR hy).left hc) hv

/-- **`tabF` at the typed world is `tabNK`, and `finF` is `finNK`.** -/
theorem tabF_finF_KW (g : KW → KW) (δ : LSub) : ∀ F : CTy,
    (∀ S x, tabF (ℍ := ℍ) (rdKW g δ) S F x = tabNK (ℍ := ℍ) S g F δ x) ∧
      ∀ S, finF (ℍ := ℍ) (rdKW g δ) S F = finNK (ℍ := ℍ) S g F δ
  | .eff m i q A B fin rc C => by
      have hf := tabF_finF_KW g δ fin
      have hC := tabF_finF_KW g δ C
      refine ⟨fun S x => ?_, fun S => ?_⟩
      · simp only [tabF, tabNK, hf.2, hC.1]; rfl
      · simp only [finF, finNK, hf.2, hC.1]; rfl
  | .ret _ => ⟨fun _ _ => by simp [tabF, tabNK], fun _ => by simp [finF, finNK]; rfl⟩
  | .arr _ _ => ⟨fun _ _ => by simp [tabF, tabNK], fun _ => by simp [finF, finNK]; rfl⟩
  | .amp _ _ => ⟨fun _ _ => by simp [tabF, tabNK], fun _ => by simp [finF, finNK]; rfl⟩
  | .top => ⟨fun _ _ => by simp [tabF, tabNK], fun _ => by simp [finF, finNK]⟩
  | .all _ _ _ => ⟨fun _ _ => by simp [tabF, tabNK], fun _ => by simp [finF, finNK]; rfl⟩
  | .nu _ => ⟨fun _ _ => by simp [tabF, tabNK], fun _ => by simp [finF, finNK]; rfl⟩
  termination_by structural F => F

theorem tabF_KW (g : KW → KW) (δ : LSub) (S : UInt32 → Prop) (F : CTy) (x : KW) :
    tabF (ℍ := ℍ) (rdKW g δ) S F x = tabNK (ℍ := ℍ) S g F δ x :=
  (tabF_finF_KW g δ F).1 S x

theorem finF_KW (g : KW → KW) (δ : LSub) (S : UInt32 → Prop) (F : CTy) :
    finF (ℍ := ℍ) (rdKW g δ) S F = finNK (ℍ := ℍ) S g F δ :=
  (tabF_finF_KW g δ F).2 S

/-! ### One world -/

/-- **The one-world reading** (`tabN`): every value at `Θ` and `c`; one mode; every entry owes at
the one world; the runs at `Θ.view c`. -/
def rdU (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) : RowRd Unit Unit where
  δ := δ
  Θ := fun _ => Θ
  c := fun _ => c
  wk := fun _ _ _ _ _ _ => True
  sub := fun _ _ => ()
  le := fun _ _ => True
  V := fun _ _ => True
  Φ := fun _ => Θ.view c
  fl := fun _ => 0
  Inv := fun _ => True

theorem rdU_ok {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) (c : Loc → Option Life) : (rdU δ Θ c).OK where
  wkInv := fun _ _ _ _ _ _ _ => trivial
  ΦDown := fun _ _ => LocTy.view_down hΘ c
  wkLeft := fun _ _ _ _ _ _ _ _ _ _ _ => trivial
  le_refl := fun _ => trivial
  le_trans := fun _ _ _ _ _ => trivial
  le_sub := fun _ _ => trivial
  sub_mono := fun _ _ _ _ => trivial
  wk_anti := fun _ _ _ _ _ _ _ _ _ => trivial
  Veq := fun _ _ _ => rfl

theorem rdU_payExt (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) : (rdU δ Θ c).PayExt (ℍ := ℍ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h

/-- `cancelOblN` is the one-world reading's cancel run at the lifted table. -/
theorem canc_unit (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (T : OpTabN) :
    (rdU δ Θ c).canc (ℍ := ℍ) (fun _ => liftTabK T) = fun _ => cancelOblN (ℍ := ℍ) (Θ.view c) T := by
  funext y k ls e ρ
  cases y
  show erwpK (ℍ := ℍ) (fun _ _ => True) (fun _ => Θ.view c) (fun _ => cancelTabK 0 (liftTabK T))
      (fun _ _ _ _ _ => False) () k ls e ρ = erwp (ℍ := ℍ) (Θ.view c) (cancelTabN T) _ k ls e ρ
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 T) (Θ.view c) _]

theorem liftTabK_extTabN (n i : UInt32) (en : OpEntN) (T : OpTabN) :
    liftTabK (extTabN n i en T) = extTabK n i (liftEntK en) (liftTabK T) := by
  funext m j
  simp only [liftTabK, extTabN, extTabK]
  split <;> rfl

/-- **`tabF` at one world is `tabN` lifted, and `finF` is `finN` lifted.** -/
theorem tabF_finF_unit (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) : ∀ F : CTy,
    (∀ x, tabF (ℍ := ℍ) (rdU δ Θ c) () F x = liftTabK (tabN (ℍ := ℍ) F δ Θ c)) ∧
      finF (ℍ := ℍ) (rdU δ Θ c) () F = (finN (ℍ := ℍ) F δ Θ c).map (fun P _ => P)
  | .eff m i q A B fin rc C => by
      have hf := tabF_finF_unit δ Θ c fin
      have hC := tabF_finF_unit δ Θ c C
      have he : ∀ x, (rdU δ Θ c).ent (ℍ := ℍ) () m q A B (finF (ℍ := ℍ) (rdU δ Θ c) () fin) x =
          liftEntK (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
            (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ ∧ ConsistentX c ρ) (finN (ℍ := ℍ) fin δ Θ c)) := by
        intro x
        rw [hf.2]
        simp only [RowRd.ent, liftEntK, entN]
        congr 1
        split <;> rfl
      have hT : ∀ x, tabF (ℍ := ℍ) (rdU δ Θ c) () (.eff m i q A B fin rc C) x =
          liftTabK (tabN (ℍ := ℍ) (.eff m i q A B fin rc C) δ Θ c) := by
        intro x
        simp only [tabF, tabN]
        rw [liftTabK_extTabN, he x, hC.1 x]
      refine ⟨hT, ?_⟩
      have hT' : (fun x => extTabK m i ((rdU δ Θ c).ent (ℍ := ℍ) () m q A B
          (finF (ℍ := ℍ) (rdU δ Θ c) ((rdU δ Θ c).sub () m) fin) x)
          (tabF (ℍ := ℍ) (rdU δ Θ c) () C x)) =
          fun _ => liftTabK (tabN (ℍ := ℍ) (.eff m i q A B fin rc C) δ Θ c) := funext hT
      simp only [finF, finN, Option.map_some]
      rw [hT', canc_unit]
      rfl
  | .ret _ => ⟨fun _ => by simp [tabF, tabN, liftTabK_empty], by
      simp only [finF, finN, Option.map_some]; rw [← liftTabK_empty, canc_unit]⟩
  | .arr _ _ => ⟨fun _ => by simp [tabF, tabN, liftTabK_empty], by
      simp only [finF, finN, Option.map_some]; rw [← liftTabK_empty, canc_unit]⟩
  | .amp _ _ => ⟨fun _ => by simp [tabF, tabN, liftTabK_empty], by
      simp only [finF, finN, Option.map_some]; rw [← liftTabK_empty, canc_unit]⟩
  | .all _ _ _ => ⟨fun _ => by simp [tabF, tabN, liftTabK_empty], by
      simp only [finF, finN, Option.map_some]; rw [← liftTabK_empty, canc_unit]⟩
  | .nu _ => ⟨fun _ => by simp [tabF, tabN, liftTabK_empty], by
      simp only [finF, finN, Option.map_some]; rw [← liftTabK_empty, canc_unit]⟩
  | .top => ⟨fun _ => by simp [tabF, tabN, liftTabK_empty], by simp [finF, finN]⟩
  termination_by structural F => F

theorem tabF_unit (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (F : CTy) (x : Unit) :
    tabF (ℍ := ℍ) (rdU δ Θ c) () F x = liftTabK (tabN (ℍ := ℍ) F δ Θ c) :=
  (tabF_finF_unit δ Θ c F).1 x

theorem finF_unit (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (F : CTy) :
    finF (ℍ := ℍ) (rdU δ Θ c) () F = (finN (ℍ := ℍ) F δ Θ c).map (fun P _ => P) :=
  (tabF_finF_unit δ Θ c F).2

/-! ### The interface -/

section Interface
variable (R : RowRd ι M)

/-- **A row's table at a key is the entry of the operation the row finds there**
(`tabN_effOf_find`). -/
theorem tabF_effOf_find (μ : M) (S : Row) (Rt : VTy) (x : ι) (n i : UInt32) :
    tabF (ℍ := ℍ) R μ (CTy.effOf S Rt) x n i = (Row.find S n i).map (fun o =>
      R.ent (ℍ := ℍ) μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o.fin) x) := by
  induction S with
  | nil => simp [CTy.effOf, tabF, OpTabK.empty, Row.find]
  | cons o S ih =>
      show extTabK o.n o.i _ (tabF (ℍ := ℍ) R μ (CTy.effOf S Rt) x) n i = _
      unfold extTabK Row.find
      by_cases h : n = o.n ∧ i = o.i
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · simp only [if_neg h, List.find?_cons, decide_eq_false h]
        exact ih

variable {R}

theorem tabF_effOf_some_find {μ : M} {S : Row} {Rt : VTy} {x : ι} {n i : UInt32}
    {en : OpEntK ι} (h : tabF (ℍ := ℍ) R μ (CTy.effOf S Rt) x n i = some en) :
    ∃ o, Row.find S n i = some o ∧
      en = R.ent (ℍ := ℍ) μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o.fin) x := by
  rw [tabF_effOf_find] at h
  obtain ⟨o, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨o, hf, rfl⟩

variable (R)

/-- The table of a cancel row is the table of its layers (`tabN_rowOf`). -/
theorem tabF_rowOf (μ : M) : ∀ (F : CTy) (x : ι),
    tabF (ℍ := ℍ) R μ F x = tabF (ℍ := ℍ) R μ (CTy.effOf F.rowOf .unit) x
  | .eff m i q A B fin rc C, x => by
      simp only [CTy.rowOf, CTy.effOf, tabF]
      rw [tabF_rowOf μ C x]
  | .ret _, _ => by simp [CTy.rowOf, CTy.effOf, tabF]
  | .arr _ _, _ => by simp [CTy.rowOf, CTy.effOf, tabF]
  | .amp _ _, _ => by simp [CTy.rowOf, CTy.effOf, tabF]
  | .top, _ => by simp [CTy.rowOf, CTy.effOf, tabF]
  | .all _ _ _, _ => by simp [CTy.rowOf, CTy.effOf, tabF]
  | .nu _, _ => by simp [CTy.rowOf, CTy.effOf, tabF]

variable {R}

/-- A row's table at a key, rewritten along a signature (`tabN_find_sig`). -/
theorem tabF_find_sig {μ : M} {S : Row} {Rt : VTy} {x : ι} {n i : UInt32} {o o' : OpSig}
    (hf : Row.find S n i = some o') (hs : o.Sig o') :
    tabF (ℍ := ℍ) R μ (CTy.effOf S Rt) x n i =
      some (R.ent (ℍ := ℍ) μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o'.fin) x) := by
  obtain ⟨-, -, hq, hA, hB, -⟩ := hs
  rw [tabF_effOf_find, hf, hq, hA, hB]; rfl

/-- A cancel row's table is the table of its layers, at a key (`tabN_rowOf_find`). -/
theorem tabF_rowOf_find {μ : M} {G : CTy} {x : ι} {n i : UInt32} {en : OpEntK ι}
    (h : tabF (ℍ := ℍ) R μ G x n i = some en) :
    ∃ o, Row.find G.rowOf n i = some o ∧
      en = R.ent (ℍ := ℍ) μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o.fin) x := by
  rw [tabF_rowOf] at h
  exact tabF_effOf_some_find h

/-- An entry of a row's table at one world has the same layer's entry at every world. -/
theorem tabF_at {μ : M} {G : CTy} {x : ι} {n i : UInt32} {en : OpEntK ι}
    (h : tabF (ℍ := ℍ) R μ G x n i = some en) :
    ∃ o, Row.find G.rowOf n i = some o ∧
      en = R.ent (ℍ := ℍ) μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o.fin) x ∧
      ∀ y, tabF (ℍ := ℍ) R μ G y n i =
        some (R.ent (ℍ := ℍ) μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o.fin) y) := by
  obtain ⟨o, hf, rfl⟩ := tabF_rowOf_find h
  exact ⟨o, hf, rfl, fun y => by rw [tabF_rowOf, tabF_effOf_find, hf]; rfl⟩

variable (R)

/-- **A cancel row's obligation** (`finN_eq_ite`): none at `⊤`; otherwise the cancel run at the
row's table. -/
theorem finF_eq_ite (μ : M) (F : CTy) :
    finF (ℍ := ℍ) R μ F =
      if F.isTop then none else some (R.canc (ℍ := ℍ) (fun x => tabF (ℍ := ℍ) R μ F x)) := by
  cases F <;> simp [finF, tabF, CTy.isTop]

variable {R}

/-- The cancel obligation of a capturable entry is the cancel run at its cancel row, which is not
`⊤` (`entN_fin_cancel`). -/
theorem entF_fin_cancel {μ μ' : M} {m : UInt32} {q : Qual} {A B : VTy} {F : CTy} {x : ι}
    {P : ι → Nat → List SRec → Expr → WProp}
    (hP : (R.ent (ℍ := ℍ) μ' m q A B (finF (ℍ := ℍ) R μ F) x).fin = some P) :
    capB q B = true ∧ F.isTop = false ∧ P = R.canc (ℍ := ℍ) (fun x => tabF (ℍ := ℍ) R μ F x) := by
  simp only [RowRd.ent] at hP
  split at hP
  · rename_i hcap
    rw [finF_eq_ite] at hP
    split at hP
    · cases hP
    · rename_i hT
      cases hP
      exact ⟨hcap, by simpa using hT, rfl⟩
  · cases hP

/-- The entry at a capturable key has the cancel obligation at its cancel row (`entN_fin_of`). -/
theorem entF_fin_of {μ μ' : M} {m : UInt32} {q : Qual} {A B : VTy} {F : CTy} {x : ι}
    (hcap : capB q B = true) (hT : F.isTop = false) :
    (R.ent (ℍ := ℍ) μ' m q A B (finF (ℍ := ℍ) R μ F) x).fin =
      some (R.canc (ℍ := ℍ) (fun x => tabF (ℍ := ℍ) R μ F x)) := by
  simp only [RowRd.ent, hcap, if_true, finF_eq_ite, hT, Bool.false_eq_true, if_false]

/-- **Errors move along a first-match inclusion of abortive operations, at any modes**
(`errOkN_of_sub`): an error reads only an entry's payload, which no mode reads. -/
theorem errOkF_of_sub {μ μ' : M} {x : ι} {P P' : Row}
    (h : ∀ n i o, Row.find P n i = some o → o.abort = true →
      ∃ o', Row.find P' n i = some o' ∧ o.Sig o') {k : Nat} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes},
      errOkK (tabF (ℍ := ℍ) R μ (CTy.effOf P .unit) x) k ls err ρ →
      errOkK (tabF (ℍ := ℍ) R μ' (CTy.effOf P' .unit) x) k ls err ρ
  | none, _, h => h
  | some _, _, ⟨m, j, w, en, h'⟩ => by
      obtain ⟨⟨h₁, hT, ha⟩, h₅⟩ := pure_sep_iff.mp h'
      obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
      have ha' : o.abort = true := by simpa [RowRd.ent, OpSig.abort] using ha
      obtain ⟨o', hf', hs⟩ := h m j o hf ha'
      exact ⟨m, j, w, _, pure_sep_mk ⟨h₁, tabF_find_sig hf' hs, ha⟩ h₅⟩

/-- An error read at a lower index and any list (`errOkN_tabN_le`). -/
theorem errOkF_le {μ : M} {F : CTy} {x : ι} {k k' : Nat} (hk : k' ≤ k) {ls ls' : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOkK (tabF (ℍ := ℍ) R μ F x) k ls err ρ →
      errOkK (tabF (ℍ := ℍ) R μ F x) k' ls' err ρ :=
  errOkK_le (fun m i en hT _ k k' ls ls' v ρ hk hv => by
    obtain ⟨o, -, rfl⟩ := tabF_rowOf_find hT
    exact vN_le hk hv) hk

/-- **An error at a part of a stop's share is one at every world the stop owes** (Core's
`errOk_local`, the error carried along the stop's order). -/
theorem errOkF_ext (hP : R.PayExt (ℍ := ℍ)) {μ μ' : M} {F : CTy} {m' : UInt32} {x y : ι}
    {f : Life} {ρa ρb ρ : WRes} (hc : ResU.CompS ρa ρb ρ) (hy : R.wk μ' m' x f y ρ) {k : Nat}
    {ls : List SRec} : ∀ {err : Option Val}, errOkK (tabF (ℍ := ℍ) R μ F x) k ls err ρa →
      errOkK (tabF (ℍ := ℍ) R μ F y) k ls err ρa
  | none, h => h
  | some _, ⟨m, j, w, en, h'⟩ => by
      obtain ⟨⟨h₁, hT, ha⟩, hA, hn⟩ := pure_sep_iff.mp h'
      obtain ⟨o, -, rfl, hy'⟩ := tabF_at hT
      exact ⟨m, j, w, _, pure_sep_mk ⟨h₁, hy' y, ha⟩ ⟨hP μ' m' x f y ρa ρb ρ hc hy o.A k w hA, hn⟩⟩

/-! ### Closure in the index -/

theorem OpTabK.empty_downI (Inv : ι → Prop) : (OpTabK.empty : OpTabK ι).DownI Inv where
  pa := fun _ _ _ h => by cases h
  fin := fun _ _ _ _ h => by cases h
  wkI := fun _ _ _ h => by cases h

/-- The cancel run at a table closed in the index at the worlds `Inv` holds at is, at those
worlds. -/
theorem canc_down (hR : R.OK) {T : ι → OpTabK ι} (hT : ∀ x, (T x).DownI R.Inv) :
    ∀ y, R.Inv y → ∀ k ls e ρ, R.canc (ℍ := ℍ) T y (k + 1) ls e ρ → R.canc (ℍ := ℍ) T y k ls e ρ :=
  fun y hy _ _ _ _ h => erwpK_le (hR.ΦDown y hy) (fun _ => cancelTabK_local _ _)
    (cancelTabK_downI (hT y)) (fun _ => falsePost_down) (Nat.le_succ _) h

theorem extTabK_ent_downI (hR : R.OK) {μ : M} {m i : UInt32} {q : Qual} {A B : VTy}
    {fin : Option (ι → Nat → List SRec → Expr → WProp)}
    (hfin : ∀ P, fin = some P → ∀ y, R.Inv y → ∀ k ls e ρ, P y (k + 1) ls e ρ → P y k ls e ρ)
    {T : OpTabK ι} (hT : T.DownI R.Inv) (x : ι) :
    (extTabK m i (R.ent (ℍ := ℍ) μ m q A B fin x) T).DownI R.Inv where
  pa := fun n j en h k ls v ρ hp => by
    rcases extTabK_some h with ⟨-, -, rfl⟩ | h
    · exact vN_down A R.δ (R.Θ x) k v ρ hp
    · exact hT.pa _ _ _ h k ls v ρ hp
  fin := fun n j en P h hP y hy k ls e ρ hp => by
    rcases extTabK_some h with ⟨-, -, rfl⟩ | h
    · simp only [RowRd.ent] at hP
      split at hP
      · exact hfin P hP y hy k ls e ρ hp
      · cases hP
    · exact hT.fin _ _ _ _ h hP y hy k ls e ρ hp
  wkI := fun n j en h f y ρ hy => by
    rcases extTabK_some h with ⟨-, -, rfl⟩ | h
    · exact hR.wkInv μ m x f y ρ hy
    · exact hT.wkI _ _ _ h f y ρ hy

/-- **A row's table is closed in the index at the worlds the runs are read at** (`tabN_down`),
and so is its cancel obligation (`finN_down`). -/
theorem tabF_finF_down (hR : R.OK) : ∀ F : CTy,
    (∀ μ x, (tabF (ℍ := ℍ) R μ F x).DownI R.Inv) ∧
      ∀ μ P, finF (ℍ := ℍ) R μ F = some P → ∀ y, R.Inv y → ∀ k ls e ρ,
        P y (k + 1) ls e ρ → P y k ls e ρ
  | .eff m i q A B fin rc C => by
      have hf := tabF_finF_down hR fin
      have hC := tabF_finF_down hR C
      have hT : ∀ μ x, (tabF (ℍ := ℍ) R μ (.eff m i q A B fin rc C) x).DownI R.Inv :=
        fun μ x => extTabK_ent_downI hR (hf.2 _) (hC.1 μ x) x
      refine ⟨hT, fun μ P hP => ?_⟩
      simp only [finF, Option.some.injEq] at hP
      subst hP
      exact canc_down hR (hT μ)
  | .ret _ => ⟨fun _ _ => by simpa [tabF] using OpTabK.empty_downI R.Inv, fun _ P hP => by
      simp only [finF, Option.some.injEq] at hP; subst hP
      exact canc_down hR (fun _ => OpTabK.empty_downI R.Inv)⟩
  | .arr _ _ => ⟨fun _ _ => by simpa [tabF] using OpTabK.empty_downI R.Inv, fun _ P hP => by
      simp only [finF, Option.some.injEq] at hP; subst hP
      exact canc_down hR (fun _ => OpTabK.empty_downI R.Inv)⟩
  | .amp _ _ => ⟨fun _ _ => by simpa [tabF] using OpTabK.empty_downI R.Inv, fun _ P hP => by
      simp only [finF, Option.some.injEq] at hP; subst hP
      exact canc_down hR (fun _ => OpTabK.empty_downI R.Inv)⟩
  | .top => ⟨fun _ _ => by simpa [tabF] using OpTabK.empty_downI R.Inv, fun _ P hP => by
      simp [finF] at hP⟩
  | .all _ _ _ => ⟨fun _ _ => by simpa [tabF] using OpTabK.empty_downI R.Inv, fun _ P hP => by
      simp only [finF, Option.some.injEq] at hP; subst hP
      exact canc_down hR (fun _ => OpTabK.empty_downI R.Inv)⟩
  | .nu _ => ⟨fun _ _ => by simpa [tabF] using OpTabK.empty_downI R.Inv, fun _ P hP => by
      simp only [finF, Option.some.injEq] at hP; subst hP
      exact canc_down hR (fun _ => OpTabK.empty_downI R.Inv)⟩
  termination_by structural F => F

theorem tabF_downI (hR : R.OK) (μ : M) (F : CTy) (x : ι) :
    (tabF (ℍ := ℍ) R μ F x).DownI R.Inv :=
  (tabF_finF_down hR F).1 μ x

/-- An entry's order passes to a part of a valid share. -/
theorem tabF_wkLeft (hR : R.OK) {μ : M} {F : CTy} {x : ι} {m i : UInt32} {en : OpEntK ι}
    (h : tabF (ℍ := ℍ) R μ F x m i = some en) {f : Life} {y : ι} {ρ₁ ρ₂ ρ : WRes}
    (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ResU.Valid ρ) (hy : en.wk f y ρ) : en.wk f y ρ₁ := by
  obtain ⟨o, -, rfl⟩ := tabF_rowOf_find h
  exact hR.wkLeft μ m x f y ρ₁ ρ₂ ρ hc hv hy

/-- An entry's list order passes to a part of the share. -/
theorem tabF_wcl {μ : M} {F : CTy} {x : ι} {m i : UInt32} {en : OpEntK ι}
    (h : tabF (ℍ := ℍ) R μ F x m i = some en) {ls ls' : List SRec} {ρ₁ ρ₂ ρ : WRes}
    (hc : ResU.CompS ρ₁ ρ₂ ρ) (he : en.wc ls ls' ρ) : en.wc ls ls' ρ₁ := by
  obtain ⟨o, -, rfl⟩ := tabF_rowOf_find h
  exact extF_left ls ls' ρ₁ ρ₂ ρ hc he

end Interface

/-! ### A cancel run under a plain context -/

/-- **A cancel run under a plain context, at `erwpK`, read at the worlds `Inv` holds at**
(`cancelOblNK_frame` with no frame): the cancel's end leaves the context behind; a stop keeps it in
its continuation, whose own cancel carries through `K` at the resumption world (`hK`). -/
theorem cancelK_plainI {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) {fl : ι → Life} {T : ι → OpTabK ι} (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (hC : K.Catches 0 = false)
    (hwkI : ∀ x n i en, T x n i = some en → ∀ f y ρ, en.wk f y ρ → Inv y)
    (hK : ∀ x n i en, T x n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ y, Inv y → ∀ k ls K₁ ρ, cancelOKK en y k ls K₁ ρ → cancelOKK en y k ls (K.comp K₁) ρ) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z))
        (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z)) (fun _ _ _ _ _ => False) x n ls
        (K.plug e) ρ := by
  have hL : ∀ z, (cancelTabK (fl z) (T z)).Local := fun z => cancelTabK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρ h
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x hx) K ?_
  refine rwpG_mono_le (fun k hk ls' t τ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, _, _, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hs'⟩
  · exact hv.elim
  · -- an operation: the context joins its continuation
    obtain ⟨⟨rfl, hK₁, hT₁, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT₁, ha⟩ ⟨ρa, ρk, hcak, hA, hu, f, hf,
        fun y hy ls'' he => ⟨fun k' hk'' w τa' τb' hB hcτ' => ?_, fun hq P hP => ?_⟩⟩⟩))
    · have h₁ := (hcont y hy ls'' he).1 k' hk'' w τa' τb' hB hcτ'
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y (hwkI x m i en hT₁ f y ρk hy) ls'' _ τb' h₁
    · exact hK x m i en hT₁ ha hq y (hwkI x m i en hT₁ f y ρk hy) k ls'' K₁ ρk
        (fun P hP => (hcont y hy ls'' he).2 hq P hP) P hP
  · -- the cancel's end: the context is left behind
    obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hs'
    have hKo : (K.comp K').Catches 0 = false := by rw [catches_comp, hC, hK']; rfl
    have ht' : K.plug (K'.plug (raiseE (.val (cancelVal err)))) =
        (K.comp K').plug (opE true (cancelVal err)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_cancelVal err) hKo) (Or.inr (Or.inr
      ⟨K.comp K', err, pure_sep_mk ⟨rfl, hKo⟩ ⟨τa, τb, hcab, he, hnb⟩⟩))

section Plain
variable {R : RowRd ι M}

/-- **A cancel run under a plain context, at a cancel row's table, beside no frame**
(`cancelOblN_plain₀`, Core's `plain_cancel₀`), by recursion on the cancel row. -/
theorem tabF_plain₀ (hR : R.OK) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : K.Catches 0 = false) (G : CTy) :
    ∀ {μ : M} {y : ι}, R.Inv y → ∀ {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes},
      R.canc (ℍ := ℍ) (fun x => tabF (ℍ := ℍ) R μ G x) y n ls e ρ →
      R.canc (ℍ := ℍ) (fun x => tabF (ℍ := ℍ) R μ G x) y n ls (K.plug e) ρ := by
  intro μ y hy n ls e ρ h
  refine cancelK_plainI hR.ΦDown K hH hC
    (fun x m i en hT f y ρ hw => (tabF_downI hR μ G x).wkI m i en hT f y ρ hw) ?_ n y hy ls e ρ h
  intro x m i en hT _ _ y' hy' k ls₁ K₁ ρ₁ hcan P hP
  obtain ⟨o, hf, rfl⟩ := tabF_rowOf_find hT
  obtain ⟨hcap, hnT, rfl⟩ := entF_fin_cancel hP
  show R.canc (ℍ := ℍ) _ y' k ls₁ ((K.comp K₁).dead.plug _) ρ₁
  rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
  exact tabF_plain₀ hR K hH hC o.fin hy' (hcan _ (entF_fin_of hcap hnT))
termination_by sizeOf G
decreasing_by exact rowOf_fin_lt G (Row.find_mem hf).1

/-- **E5: a row's table is closed under a plain context** (`tabN_ctxClosed`), at the worlds the
runs are read at: a context with no handler that catches no cancel carries every cancel
obligation of the table (`tabF_plain₀`). -/
theorem tabF_ctxClosed (hR : R.OK) (G : CTy) (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : K.Catches 0 = false) (μ : M) (x : ι) :
    (tabF (ℍ := ℍ) R μ G x).CtxClosedI R.Inv K := by
  intro m i en P hT hP y hy k ls K' e ρ h
  obtain ⟨o, -, rfl⟩ := tabF_rowOf_find hT
  obtain ⟨-, -, rfl⟩ := entF_fin_cancel hP
  rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
  exact tabF_plain₀ hR K hH hC o.fin hy h

/-- **An entry's cancel obligation under a plain context, beside a frame holding nothing owned**
(`entN_plain`, Core's `ent_plain`): the frame is left behind (`erwpK_garbage`). -/
theorem entF_plain (hR : R.OK) (K : Kont) (hH : ∀ n, K.HasHnd n = false)
    (hC : K.Catches 0 = false) {σ : WRes} (hσ : NoOwn σ) {μ μ' : M} {m : UInt32} (o : OpSig)
    {x y : ι} (hy : R.Inv y) {k : Nat} {ls : List SRec} {K₁ : Kont} {ρ ρ' : WRes}
    (hcan : cancelOKK (R.ent (ℍ := ℍ) μ' m o.q o.A o.B (finF (ℍ := ℍ) R μ o.fin) x) y k ls K₁ ρ)
    (hc : ResU.CompS ρ σ ρ') :
    cancelOKK (R.ent (ℍ := ℍ) μ' m o.q o.A o.B (finF (ℍ := ℍ) R μ o.fin) x) y k ls
      (K.comp K₁) ρ' := by
  intro P hP
  have hP₀ := hP
  obtain ⟨-, -, rfl⟩ := entF_fin_cancel hP₀
  show R.canc (ℍ := ℍ) _ y k ls ((K.comp K₁).dead.plug _) ρ'
  rw [dead_comp, dead_plain K hH hC, Kont.plug_comp]
  exact erwpK_garbage hc hσ (tabF_plain₀ hR K hH hC o.fin hy (hcan _ hP))

end Plain

/-! ### Tables widened -/

/-- An error of a table is one of a wider table. -/
theorem errOkK_tabLe {T T' : OpTabK ι} (hT : T.Le T') {k : Nat} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOkK T k ls err ρ → errOkK T' k ls err ρ
  | none, _, h => h
  | some _, _, ⟨m, j, w, en, h⟩ => by
      obtain ⟨⟨h₁, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp h
      obtain ⟨en', hTe', -, hab, hPA', -⟩ := hT m j en hTe
      exact ⟨m, j, w, en', pure_sep_mk ⟨h₁, hTe', hab ▸ ha⟩ ⟨hPA' ▸ hPA, hn⟩⟩

/-- **A stop of `cancelTabK lo T` is one of `cancelTabK lo T′` when `T ≤ T′`**
(`cancelTabN_le`). -/
theorem cancelTabK_le {lo : Life} {T T' : OpTabK ι} (hT : T.Le T') :
    ∀ k ls t (Ψ Ψ' : ContK ι) ρ, (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
      cancelTabK lo T k ls t Ψ ρ → cancelTabK lo T' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases cancelTabK_local lo T k ls t Ψ Ψ' ρ hΨ h with ⟨K, n, i, v, en, hp⟩ | ⟨K, err, hp⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', h₃', hq, hab, hPA, hPB, hwc, hwk, hfl⟩ := hT n i en h₃
    refine Or.inl ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩ ⟨ρa, ρk, hc, hPA ▸ hA,
      fun hu' => hu (hq.trans hu'), f, hf, fun y hy ls' he => ?_⟩⟩
    rw [← hwc] at he
    have hy' := hwk f y ρk hy
    refine ⟨fun k' hk' w => hPB ▸ (hcont y hy' ls' he).1 k' hk' w, fun hq' P hP => ?_⟩
    exact finLeSK_apply (hfl h₄ (hq ▸ hq')) hP
      (fun P₀ hP₀ => (hcont y hy' ls' he).2 (hq ▸ hq') P₀ hP₀)
  · obtain ⟨h₁, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hp
    exact Or.inr ⟨K, err, pure_sep_mk h₁ ⟨τa, τb, hcab, errOkK_tabLe hT he, hnb⟩⟩

section Widen
variable (R : RowRd ι M)

theorem entF_le_of_leF {μ μ₁ : M} {m : UInt32} {o o' : OpSig} {x : ι} (hs : o.Sig o')
    (hfin : capB o.q o.B = true →
      FinLeSK (finF (ℍ := ℍ) R μ₁ o.fin) (finF (ℍ := ℍ) R μ₁ o'.fin)) :
    (R.ent (ℍ := ℍ) μ m o.q o.A o.B (finF (ℍ := ℍ) R μ₁ o.fin) x).Le
      (R.ent (ℍ := ℍ) μ m o'.q o'.A o'.B (finF (ℍ := ℍ) R μ₁ o'.fin) x) := by
  obtain ⟨-, -, hq, hA, hB, -⟩ := hs
  refine ⟨hq, by simp [RowRd.ent, hq, hB], by simp [RowRd.ent, hA], by simp [RowRd.ent, hB], rfl,
    fun _ _ _ h => h, fun ha hq' => ?_⟩
  have hcap : capB o.q o.B = true := by
    simp only [RowRd.ent, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at ha hq'
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
    rcases ha with ha | ha
    · exact ⟨hq', by simpa using ha⟩
    · exact absurd ha hq'
  simp only [RowRd.ent, hcap, if_true, ← hq, ← hB]
  exact hfin hcap

/-- **A cancel row's obligation grows with the row** (`finN_mono`, Core's `finObl_mono`), along
`FinLe`, by recursion on the cancel row. -/
theorem finF_mono (μ : M) (F : CTy) :
    ∀ {F' : CTy}, FinLe F F' → FinLeSK (finF (ℍ := ℍ) R μ F) (finF (ℍ := ℍ) R μ F') := by
  intro F' h
  rw [finLe_iff] at h
  rw [finF_eq_ite R μ F, finF_eq_ite R μ F']
  rcases h with h | ⟨hF, h⟩
  · simp only [h, if_true]; exact trivial
  · cases hF' : F'.isTop
    · simp only [hF, Bool.false_eq_true, if_false, FinLeSK]
      intro y k ls e ρ hc
      refine erwpK_mono (Φ := R.Φ) (Tb := fun z => cancelTabK (R.fl z) (tabF (ℍ := ℍ) R μ F z))
        (Tb' := fun z => cancelTabK (R.fl z) (tabF (ℍ := ℍ) R μ F' z)) (fun _ _ h => h)
        (fun _ _ _ _ _ h => h)
        (fun z k ls t Ψ Ψ' ρ hΨ hh => cancelTabK_le ?_ k ls t Ψ Ψ' ρ hΨ hh) k y ls e ρ hc
      intro n i en hT
      rw [tabF_rowOf] at hT
      obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
      obtain ⟨o', hf', hs, hle⟩ := h n i o hf
      refine ⟨_, by rw [tabF_rowOf, tabF_effOf_find, hf']; rfl, entF_le_of_leF R hs fun hcap => ?_⟩
      exact finF_mono (R.sub μ n) o.fin (hle (by simp [OpSig.finRead, hcap]))
    · simp only [if_true]; exact trivial
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (Row.find_mem (by assumption)).1

/-- The entry `Σ′` has at the key of an operation of `Σ ≤ Σ′`, and the entries' order
(`tabN_rowLe_entry`). -/
theorem tabF_rowLe_entry {S S' : Row} (hle : RowLe S S') {μ : M} {x : ι} {n i : UInt32}
    {o : OpSig} (hf : Row.find S n i = some o) :
    ∃ o', Row.find S' n i = some o' ∧ o.Sig o' ∧
      tabF (ℍ := ℍ) R μ (CTy.effOf S' .unit) x n i =
        some (R.ent (ℍ := ℍ) μ n o'.q o'.A o'.B (finF (ℍ := ℍ) R (R.sub μ n) o'.fin) x) ∧
      (R.ent (ℍ := ℍ) μ n o.q o.A o.B (finF (ℍ := ℍ) R (R.sub μ n) o.fin) x).Le
        (R.ent (ℍ := ℍ) μ n o'.q o'.A o'.B (finF (ℍ := ℍ) R (R.sub μ n) o'.fin) x) := by
  obtain ⟨o', hf', hs, hfl⟩ := hle n i o hf
  exact ⟨o', hf', hs, by rw [tabF_effOf_find, hf']; rfl, entF_le_of_leF R hs fun hcap =>
    finF_mono R (R.sub μ n) o.fin (hfl (by simp [OpSig.finRead, hcap]))⟩

end Widen

/-! ### E5 at the typed world -/

/-- **E5 at `KW`: a row's table is closed under a plain context** (`tabN_ctxClosed` at `KW`), at
every world whose location typing under `g` is downward closed, which every world an entry owes
at is. -/
theorem tabNK_ctxClosed (S : UInt32 → Prop) (g : KW → KW) (G : CTy) (δ : LSub) (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : K.Catches 0 = false) (x : KW) :
    (tabNK (ℍ := ℍ) S g G δ x).CtxClosedI (fun z => (g z).Θ.Down) K := by
  rw [← tabF_KW]
  exact tabF_ctxClosed (rdKW_ok g δ) G K hH hC S x

/-- **`tabNK` is closed in the index at those worlds**, and every world an entry owes at is
one. -/
theorem tabNK_downI (S : UInt32 → Prop) (g : KW → KW) (G : CTy) (δ : LSub) (x : KW) :
    (tabNK (ℍ := ℍ) S g G δ x).DownI (fun z => (g z).Θ.Down) := by
  rw [← tabF_KW]
  exact tabF_downI (rdKW_ok g δ) S G x

end BoCa.Fig16.LogRel.Core.Chain.SI

end
