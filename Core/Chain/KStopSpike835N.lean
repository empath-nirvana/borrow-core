import Core.Chain.Public835N

/-!
# A Kripke stop for `erwp`: local definitions and two producers  `[spec §19, §27]`

`docs/new-core/scope-835-kripke-stop.md`. Dreyer, Neis & Birkedal's `K⟦τ⟧` (JFP 2012, Fig. 6)
owes a continuation at every public future of the world it is captured at. Here that is a stop
whose continuation is owed at every world its entry's order allows, with the answer, the cancel
obligation, the tables, the location family and the postcondition read at that world. Nothing
here changes `erwp`; the definitions are local copies at a world index `ι`.

* `erwpK V Φ Tb Q x` is `erwp` at the world `x`: the run at `Φ x` and `Tb x`; its stops owe their
  continuations `erwpK … y` at the worlds `y` the stop's entry allows (`OpEntK.wk`); its values
  are in `Q y` at a world `y` with `V x y` (an existentially chosen later world for the post).
* **The constant-world embedding.** At `ι = Unit`, `V` trivial, every family constant and the
  table lifted, `erwpK` is `erwp` (`erwp_eq_erwpK`), and `opTableK` of the lifted table is
  `opTableN` (`opTableK_liftTab`). So every statement about `erwp` is a statement about `erwpK`.
* **`perform`** (`erwpK_perform`): `erwp_perform`'s proof, the continuation premise read at every
  world the entry allows.
* **The Mut Frame across stops** (`erwpK_M_frame`): `erwp_M_frame`'s proof at every world. The one
  new premise is `OpTabK.FoldTwin`: the lender's order at the lender's share gives the borrowed
  entry's order at the borrowed share across the fold, and keeps an invariant of the worlds the
  frame's stops are taken at. At the typed world it is `LocTy.ExtP.fold` (`extP_foldFrame`,
  `foldTwin_wk_typed`), with the invariant `FoldInv A`: `A` fresh and no `imm` record at `A`.
  `ExtP` at the floor `A` alone does not keep `FoldInv A` (`extP_not_foldInv`), so the lender's
  order under a live lend carries it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
namespace KStopSpike835N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### Tables over a world index -/

/-- `OpEntN` with the answer and the cancel obligation read at the resumption world, and `wk`, the
worlds the continuation is owed at (from the world of the table the entry is in), at the
continuation's share. -/
structure OpEntK (ι : Type) where
  q : Qual
  abort : Bool
  PA : Nat → List SRec → Val → WProp
  PB : ι → Nat → List SRec → Val → WProp
  fin : Option (ι → Nat → List SRec → Expr → WProp)
  wc : List SRec → List SRec → WRes → Prop
  wk : ι → WRes → Prop

variable {ι : Type}

abbrev OpTabK (ι : Type) := UInt32 → UInt32 → Option (OpEntK ι)

/-- What a stop owes, at every world, index and list. -/
abbrev ContK (ι : Type) := ι → Nat → List SRec → Expr → WProp

/-- A protocol table at the index, owing a world-indexed continuation. -/
abbrev TableK (ι : Type) := Nat → List SRec → Expr → ContK ι → WProp

/-- `cancelOKN` at the resumption world. -/
def cancelOKK (en : OpEntK ι) (y : ι) (k : Nat) (ls : List SRec) (K : Kont) : WProp := fun ρ =>
  ∀ P, en.fin = some P → P y k ls (K.dead.plug (raiseE (.val (cancelVal none)))) ρ

/-- **The Kripke stop**: `contShareN` at every world `y` the entry's order allows at the
continuation's share, the answer, the cancel obligation and the continuation read at `y`. -/
def contShareK (en : OpEntK ι) (k : Nat) (ls : List SRec) (K : Kont) (Ψ : ContK ι) : WProp :=
  fun ρ =>
    (en.q = .unr → ρ = PMap.empty) ∧
    ∀ y, en.wk y ρ → ∀ ls', en.wc ls ls' ρ →
      (∀ k', k' < k → ∀ w : Val, (en.PB y k' ls' w ─⋆ Ψ y k' ls' (K.plug (.val w))) ρ) ∧
      (en.q ≠ .lin → cancelOKK en y k ls' K ρ)

/-- `performStopN` at the Kripke stop. -/
def performStopK (T : OpTabK ι) : TableK ι := fun k ls t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntK ι) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆ (en.PA k ls v ⋆ contShareK en k ls K Ψ)

/-- `raiseStopN`: an abortive stop owes no continuation, so it reads no world. -/
def raiseStopK (T : OpTabK ι) : TableK ι := fun k ls t _ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntK ι) =>
      ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
        T n i = some en ∧ en.abort = true⌝ ⋆
        ((fun ρ => en.PA k ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ)

def opTableK (T : OpTabK ι) : TableK ι := fun k ls t Ψ =>
  BoLo.or (performStopK T k ls t Ψ) (raiseStopK T k ls t Ψ)

/-- A table reads what is owed only below the index it stops at, at every world. -/
def TableK.Local (Tb : TableK ι) : Prop :=
  ∀ k ls t (Ψ Ψ' : ContK ι) ρ, (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
    Tb k ls t Ψ ρ → Tb k ls t Ψ' ρ

theorem opTableK_local (T : OpTabK ι) : (opTableK T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, fun y hy ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ y k' hk _ _ _ ((hcont y hy ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont y hy ls' he).2⟩⟩⟩
  · exact Or.inr h

/-! ### The relation over a world index -/

/-- A value in `Q` at a world `V` allows, or a stop the table allows. -/
def erwpPostK (V : ι → Prop) (Tb : TableK ι) (Q : ι → PostN) (Ψ : ContK ι) : PostG :=
  fun k ls t => BoLo.or (fun ρ => ∃ v : Val, t = v.1 ∧ ∃ y, V y ∧ Q y k ls v ρ) (Tb k ls t Ψ)

/-- **`erwp` at a world.** The run at `Φ x`, its stops at `Tb x` owing `erwpK` at the worlds the
stop allows, its values in `Q` at a world `V x` allows. -/
def erwpK (V : ι → ι → Prop) (Φ : ι → LocFam) (Tb : ι → TableK ι) (Q : ι → PostN) :
    ι → Nat → List SRec → Expr → WProp
  | x, n, ls, e => rwpG (ℍ := ℍ) (Φ x) (erwpPostK (V x) (Tb x) Q (fun y k' ls' e' =>
      if _h : k' < n then erwpK V Φ Tb Q y k' ls' e' else fun _ => False)) n ls e
termination_by _ n => n

/-- What `erwpK` at `N` owes below it. -/
def erwpCK (V : ι → ι → Prop) (Φ : ι → LocFam) (Tb : ι → TableK ι) (Q : ι → PostN) (N : Nat) :
    ContK ι := fun y k' ls' e' =>
  if k' < N then erwpK (ℍ := ℍ) V Φ Tb Q y k' ls' e' else fun _ => False

theorem erwpK_eq (V : ι → ι → Prop) (Φ : ι → LocFam) (Tb : ι → TableK ι) (Q : ι → PostN) (x : ι)
    (n : Nat) (ls : List SRec) (e : Expr) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls e =
      rwpG (ℍ := ℍ) (Φ x) (erwpPostK (V x) (Tb x) Q (erwpCK (ℍ := ℍ) V Φ Tb Q n)) n ls e := by
  rw [erwpK]
  congr 1

/-! ### The constant-world embedding -/

/-- A table at one world, read at `Unit`. -/
def liftTb (Tb : TableN) : TableK Unit := fun k ls t Ψ => Tb k ls t (Ψ ())

/-- **`erwp` is `erwpK` at one world.** -/
theorem erwp_eq_erwpK (Φ : LocFam) (Tb : TableN) (Q : PostN) :
    ∀ n ls e, erwp (ℍ := ℍ) Φ Tb Q n ls e =
      erwpK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => liftTb Tb) (fun _ => Q) () n ls e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e
  rw [erwp_eq, erwpK_eq]
  have hC : erwpC (ℍ := ℍ) Φ Tb Q n = erwpCK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ)
      (fun _ => liftTb Tb) (fun _ => Q) n () := by
    funext k' ls' e'
    simp only [erwpC, erwpCK]
    split_ifs with hk
    · exact ih k' hk ls' e'
    · rfl
  have hP : erwpPost Tb Q (erwpC (ℍ := ℍ) Φ Tb Q n) =
      erwpPostK (fun _ => True) (liftTb Tb) (fun _ => Q)
        (erwpCK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => liftTb Tb) (fun _ => Q) n) := by
    funext k ls' t ρ
    simp only [erwpPost, erwpPostK, valPostN, liftTb, hC, BoLo.or]
    apply propext
    constructor
    · rintro (⟨v, hv, hq⟩ | h)
      · exact Or.inl ⟨v, hv, (), trivial, hq⟩
      · exact Or.inr h
    · rintro (⟨v, hv, -, -, hq⟩ | h)
      · exact Or.inl ⟨v, hv, hq⟩
      · exact Or.inr h
  rw [hP]

/-- An entry at one world, read at `Unit`: every world allowed. -/
def liftEnt (en : OpEntN) : OpEntK Unit where
  q := en.q
  abort := en.abort
  PA := en.PA
  PB := fun _ => en.PB
  fin := en.fin.map (fun P _ => P)
  wc := en.wc
  wk := fun _ _ => True

def liftTab (T : OpTabN) : OpTabK Unit := fun m i => (T m i).map liftEnt

theorem contShareK_liftEnt (en : OpEntN) (k : Nat) (ls : List SRec) (K : Kont) (Ψ : ContK Unit)
    (ρ : WRes) : contShareK (liftEnt en) k ls K Ψ ρ ↔ contShareN en k ls K (Ψ ()) ρ := by
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun ls' he => ⟨(h () trivial ls' he).1, fun hq P hP => ?_⟩⟩
    exact (h () trivial ls' he).2 hq (fun _ => P) (by simp [liftEnt, hP])
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun y _ ls' he => ⟨(h ls' he).1, fun hq P hP => ?_⟩⟩
    simp only [liftEnt, Option.map_eq_some_iff] at hP
    obtain ⟨P₀, hP₀, rfl⟩ := hP
    exact (h ls' he).2 hq P₀ hP₀

/-- **`opTableN` is `opTableK` at one world.** -/
theorem opTableK_liftTab (T : OpTabN) (k : Nat) (ls : List SRec) (t : Expr) (Ψ : ContK Unit)
    (ρ : WRes) : opTableK (liftTab T) k ls t Ψ ρ ↔ liftTb (opTableN T) k ls t Ψ ρ := by
  simp only [liftTb, opTableK, opTableN, BoLo.or]
  constructor
  · rintro (⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩)
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hcs⟩ := pure_sep_iff.mp h
      simp only [liftTab, Option.map_eq_some_iff] at h₃
      obtain ⟨en₀, he₀, rfl⟩ := h₃
      exact Or.inl ⟨K, n, i, v, en₀, pure_sep_mk ⟨h₁, h₂, he₀, h₄⟩
        ⟨ρa, ρk, hc, hA, (contShareK_liftEnt en₀ k ls K Ψ ρk).mp hcs⟩⟩
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hr⟩ := pure_sep_iff.mp h
      simp only [liftTab, Option.map_eq_some_iff] at h₃
      obtain ⟨en₀, he₀, rfl⟩ := h₃
      exact Or.inr ⟨K, n, i, v, en₀, pure_sep_mk ⟨h₁, h₂, he₀, h₄⟩ hr⟩
  · rintro (⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩)
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hcs⟩ := pure_sep_iff.mp h
      exact Or.inl ⟨K, n, i, v, liftEnt en, pure_sep_mk ⟨h₁, h₂, by simp [liftTab, h₃], h₄⟩
        ⟨ρa, ρk, hc, hA, (contShareK_liftEnt en k ls K Ψ ρk).mpr hcs⟩⟩
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hr⟩ := pure_sep_iff.mp h
      exact Or.inr ⟨K, n, i, v, liftEnt en, pure_sep_mk ⟨h₁, h₂, by simp [liftTab, h₃], h₄⟩ hr⟩

/-- **The embedding at an operation table**: `erwp` at `opTableN T` is `erwpK` at one world, at
`opTableK` of the lifted table. -/
theorem erwp_opTableN_eq_erwpK (Φ : LocFam) (T : OpTabN) (Q : PostN) (n : Nat) (ls : List SRec)
    (e : Expr) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e =
      erwpK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => opTableK (liftTab T)) (fun _ => Q)
        () n ls e := by
  have hT : (fun _ : Unit => opTableK (liftTab T)) = fun _ => liftTb (opTableN T) := by
    funext _ k ls t Ψ ρ
    exact propext (opTableK_liftTab T k ls t Ψ ρ)
  rw [hT]
  exact erwp_eq_erwpK Φ (opTableN T) Q n ls e

/-! ### Generic laws used below -/

theorem erwpK_unfold_at {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hTb : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} {n N : Nat} (hnN : n ≤ N) {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ) :
    rwpG (ℍ := ℍ) (Φ x) (erwpPostK (V x) (Tb x) Q (erwpCK (ℍ := ℍ) V Φ Tb Q N)) n ls e ρ := by
  rw [erwpK_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb x k ls' t _ _ ρ' (fun y k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpCK, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

/-- **Garbage at `erwpK`** (`erwp_garbage`). -/
theorem erwpK_garbage {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} {n : Nat} {ls : List SRec} {e : Expr} {ρ g ρg : WRes} (hc : ResU.CompS ρ g ρg)
    (hg : NoOwn g) (h : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρg := by
  rw [erwpK_eq] at h ⊢
  exact rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ => ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩)
    (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hc h hg))

/-! ### Producer 1: `perform` -/

/-- **A Kripke stop at a must-resume operation** (`erwp_perform`): the payload in `PA`, and the
continuation owed at every world the entry allows, every answer there and every lower index. -/
theorem erwpK_perform {V : ι → ι → Prop} {Φ : ι → LocFam} {T : ι → OpTabK ι} {Q : ι → PostN}
    {x : ι} (K : Kont) {m i : UInt32} {v : Val} {en : OpEntK ι} (hK : K.HasHnd m = false)
    (hT : T x m i = some en) (ha : en.abort = false) (hq : en.q = .lin) {n : Nat}
    {ls : List SRec} {ρa ρk ρ : WRes} (hc : ResU.CompS ρa ρk ρ) (hA : en.PA n ls v ρa)
    (hk : ∀ y, en.wk y ρk → ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB y k' ls' w ─⋆
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (T z)) Q y k' ls' (K.plug (.val w))) ρk) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableK (T z)) Q x n ls
      (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwpK_eq]
  refine rwpG_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr (Or.inl
    ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk, hc, hA,
      fun hu => absurd (hq.symm.trans hu) (by simp), fun y hy ls' he =>
        ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' => absurd hq hq'⟩⟩⟩))
  simp only [erwpCK, hk', if_true]
  exact hk y hy ls' he k' hk' w τ₁ τ₂ hB hcτ

/-! ### Producer 2: the Mut Frame across a stop -/

/-- `OpTabN.LendOK` over a world index: the answers in the lend's stratum at every world. -/
structure OpTabK.LendOK (T : OpTabK ι) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q = .lin ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → ρ.InStratum (↓A)

/-- **The lender's table across the fold.** Every entry of the borrowed run's table `Ti` has one
in the lender's `To` with the same qualifier, payload, answer and list order; at the shares of a
fold at `ℓ` (`extF_fold`'s), every world the lender's entry allows at the lender's share is one
the borrowed entry allows at the borrowed share, and satisfies `Inv`. -/
def OpTabK.FoldTwin (Inv : ι → Prop) (Ti To : OpTabK ι) (l : Loc) (A : Life) : Prop :=
  ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
    ∀ (ρk ρp Z W'' ρkL χ : WRes) (v : Val) (ψ : CellU Loc Val), ResU.CompS ρk ρp Z →
      Z.get l = some ψ → ψ.kind = Kind.mut → ψ.at = A → ψ.wit = χ →
      ResU.CompS χ (ResU.single l (CellU.ownOf v)) W'' → ResU.CompS (Z.del l) W'' ρkL →
      ∀ y, en'.wk y ρkL → en.wk y ρk ∧ Inv y

/-- **Mut Frame at `erwpK`, across Kripke stops** (`erwp_M_frame` at every world). At a stop, the
lender's continuation is owed at every world `y` its entry allows; `FoldTwin` gives the borrowed
continuation at `y`, and the frame is re-entered at `y` by induction on the index. -/
theorem erwpK_M_frame {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {Ti To : ι → OpTabK ι}
    (hT : ∀ x, (Ti x).LendOK A) (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (To x) l A)
    {Q : ι → PostN} :
    ∀ n j, n ≤ j → ∀ (x : ι), Inv x → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes)
      (houtP : ρP.InStratum A), ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwpK (ℍ := ℍ) V (fun y => (Φ y).set l A F) (fun y => opTableK (Ti y))
          (fun y => MFPost l A F (Q y)) x n ls e BM) →
      erwpK (ℍ := ℍ) V Φ (fun y => opTableK (To y)) Q x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwpK_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwpK_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, y₀, hy₀, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ |
      ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.65's end, the post at the world the borrowed run chose
    rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, y₀, hy₀, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · -- a stop: the borrow folded into the lender's share, owed at every world the lender allows
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := (hT x).entry m i en hTe
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc', hwk⟩ := hTT x hx m i en hTe
    have hρa := (hT x).pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc ρa ρk ρp X).mpr ⟨ρ', hcak, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Z.del l) W'' Y).mpr ⟨_, hD, hY⟩
    have hdZd : (Z.del l).InStratum (↓A) :=
      ResU.CompS.inStratum_left hZd (ResU.CompS.inStratum_right haZ hdX)
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPA, fun hu' => absurd (hq'.trans hq ▸ hu') (by simp), fun y hy ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq'' => absurd (hq'.trans hq) hq''⟩⟩⟩)⟩
    -- the world the lender's continuation is resumed at, read at the borrowed share
    obtain ⟨hyi, hyInv⟩ := hwk ρk ρp Z W'' ρkL χ v'' _ hZ hZl (CellU.kind_mutOf _ _ _ _ _ _)
      (CellU.at_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL y hy
    simp only [erwpCK, show k' < n by omega, if_true]
    rw [hPB'] at hB
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hdB : ρbB.InStratum (↓A) :=
      inStratum_compS hρbB hdZd ((hT x).pb m i en hTe _ _ _ _ _ hB)
    refine ih k' (by omega) k (le_of_lt hk') y hyInv ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
      (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
    have he' : en.wc ls' ls'' ρk := by
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW''
        hkL he
    obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
    obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
        ⟨s1, ResU.CompS.comm hs1, hZds1⟩
    obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
    obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
    obtain ⟨Xk, hXk, hXkp⟩ := (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
    have hc := (hcont y hyi ls'' he').1 k' hk' w σB Xk hB hXk
    simp only [erwpCK, show k' < n by omega, if_true] at hc
    exact erwpK_garbage hXkp hnoρp hc
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [((hT x).entry m i en hTe).1]; simp)

/-! ### The fold premise at the typed world -/

/-- **`ExtP` at the floor `A` across the fold at the frame's shares**: the lender's share
`ρkL = Z/ℓ ● W″` and the borrowed one `ρk ⊆ Z`, `Z`'s cell at `ℓ` lent at `A`. -/
theorem extP_foldFrame {Θ Θ' : LocTy} {A : Life} (hf : Θ.Fresh A) (hI : ∀ x ∈ Θ.imm, x.2 ≠ A)
    {l : Loc} (F : Nat → Val → SPropS Loc Val A) {ρk ρp Z W'' ρkL : WRes} {ψ : CellU Loc Val}
    (hZ : ResU.CompS ρk ρp Z) (hZl : Z.get l = some ψ) (hat : ψ.at = A)
    (hkL : ResU.CompS (Z.del l) W'' ρkL) (h : Θ.ExtP A Θ' ρkL) :
    (Θ.add l A F).ExtP A (Θ'.add l A F) ρk := by
  have hc : ∀ a, a < A → CellIn ρk a → CellIn ρkL a := by
    intro a ha hca
    obtain ⟨m, φ, e, hk, hle⟩ := CellIn.of_left hZ hca
    by_cases hm : m = l
    · subst hm
      rw [hZl] at e
      cases Option.some.inj e
      rw [hat] at hle
      exact absurd (lt_of_le_of_lt hle ha) (lt_irrefl _)
    · exact CellIn.of_left hkL ⟨m, φ, by rw [ResU.del_get_ne _ hm]; exact e, hk, hle⟩
  refine ⟨h.fold hf hI hc l F, fun x b hb => ?_, ?_⟩
  · rw [LocTy.add_keep _ _ _ _ (ne_of_gt hb), LocTy.add_keep _ _ _ _ (ne_of_gt hb)]
    exact h.2.1 x b hb
  · simp only [LocTy.add_imm]
    exact h.2.2

/-- The worlds a fold at `A` can be taken at: `A` fresh, no `imm` record lent at `A`. -/
def FoldInv (A : Life) (Θ : LocTy) : Prop := Θ.Fresh A ∧ ∀ x ∈ Θ.imm, x.2 ≠ A

/-- **`FoldTwin`'s world clause at the typed world.** The lender's order under the live lend: `ExtP`
at the floor `A`, to a world where the fold can be taken again. The borrowed entry's: `ExtP` at
`A` between the worlds with the lend. -/
theorem foldTwin_wk_typed {Θ : LocTy} {A : Life} (hΘ : FoldInv A Θ) {l : Loc}
    (F : Nat → Val → SPropS Loc Val A) {ρk ρp Z W'' ρkL : WRes} {ψ : CellU Loc Val}
    (hZ : ResU.CompS ρk ρp Z) (hZl : Z.get l = some ψ) (hat : ψ.at = A)
    (hkL : ResU.CompS (Z.del l) W'' ρkL) (Θ' : LocTy)
    (hy : Θ.ExtP A Θ' ρkL ∧ FoldInv A Θ') :
    (Θ.add l A F).ExtP A (Θ'.add l A F) ρk ∧ FoldInv A Θ' :=
  ⟨extP_foldFrame hΘ.1 hΘ.2 F hZ hZl hat hkL hy.1, hy.2⟩

/-- **`ExtP` at `A` does not keep `FoldInv A`**: a key at `A` itself is a public move at the floor
`A` (`LocTy.extP_add` at `α = A`). So the order the lender's stop owes under a live lend at `A`
must carry `FoldInv A` for the frame's induction to re-enter at the resumption world. -/
theorem extP_not_foldInv (A : Life) (l : Loc) (G : Nat → Val → SPropS Loc Val A) (ρ : WRes) :
    LocTy.empty.ExtP A (LocTy.empty.add l A G) ρ ∧ FoldInv A LocTy.empty ∧
      ¬ FoldInv A (LocTy.empty.add l A G) := by
  refine ⟨LocTy.extP_add (fun _ _ h => absurd rfl h) le_rfl l G ρ,
    ⟨fun _ _ h => absurd rfl h, fun x hx => by simp [LocTy.empty] at hx⟩, fun h => ?_⟩
  have := h.1 l A (by rw [LocTy.add_self]; simp)
  exact lt_irrefl _ this

end KStopSpike835N
end BoCa.Fig16.LogRel.Core.Chain.SI

end
