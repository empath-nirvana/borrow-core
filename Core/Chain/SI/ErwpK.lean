import Core.Chain.Public835N

/-!
# `erwp` at a world: Kripke stops  `[spec §19, §27]`

`docs/new-core/scope-835-kripke-stop.md` §1 and `docs/new-core/scope-835-restriction.md`.
Dreyer, Neis & Birkedal's `K⟦τ⟧` (JFP 2012, Fig. 6) owes a continuation at every public future of
the world it is captured at. `erwpK` is `erwp` over a world index `ι`:

* the run at `Φ x`, its stops allowed by the table `Tb x`, its values in `Q y` at a world `y` with
  `V x y`: the post is read at an existentially chosen later world, as in DNB's Lemma 3;
* **a Kripke stop** (`contShareK`) owes its continuation `erwpK … y` at every world `y` its entry
  allows (`OpEntK.wk`), the answer, the cancel obligation and the continuation read at `y`;
* **the stop chooses its floor.** The table at a world carries that world's floor `lo`, and a stop
  picks a floor `f ≤ lo` (`contShareK`'s `∃ f`); the entry's order is read at `f`. A stop under a
  live lend at `A` takes `f = A`, below the lender's floor.

`rwpG`, and every lemma at it, is unchanged: a run between stops never changes its world.

**The constant world.** At `ι = Unit`, every family constant, the order on posts trivial and the
table lifted, `erwpK` is `erwp` (`erwp_eq_erwpK`, `erwp_opTableN_eq_erwpK`). Each generic law below
has its `erwp` statement as the instance at `Unit` (`erwp_val_of_K`, `erwp_of_rwp_of_K`,
`erwp_bindR_of_K`, `erwp_mono_of_K`, `erwp_bind_of_K`, `erwp_frame_plain_of_K`,
`erwp_perform_of_K`), each proved from the law at `erwpK` through the embedding.

**The typed world** (`KW`): a location typing, a view and a floor. A post's world keeps the
location typing and the view and may lower the floor (`KW.Post`). A stop at `x`, at the floor `f`
it chose, owes its continuation at the worlds `y` of `KW.Owed x f y`: `ExtP f` at the
continuation's share, a valid location typing, every view consistent with the share, a floor no
higher, and **`FoldInv g` kept at every `g ≥ f`** (if it held at `x`, it holds at `y`). `ExtP`
at `A` alone does not keep `FoldInv A` (`KStopSpike835N.extP_not_foldInv`), and a frame's
induction re-enters at the resumption world, where it needs it (`kw_owed_fold`); under nested
lends the stop's floor is the innermost lend's, below the frame's. Kept rather than asked, it holds at the
stop's own world for every floor (`KW.owed_self`), which is where a handler that resumes in place
resumes.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### Tables over a world index -/

/-- `OpEntN` with the answer and the cancel obligation read at the resumption world, and `wk f y ρ`:
at the floor `f` the stop chose, the worlds `y` the continuation is owed at, at its share `ρ`. -/
structure OpEntK (ι : Type) where
  q : Qual
  abort : Bool
  PA : Nat → List SRec → Val → WProp
  PB : ι → Nat → List SRec → Val → WProp
  fin : Option (ι → Nat → List SRec → Expr → WProp)
  wc : List SRec → List SRec → WRes → Prop
  wk : Life → ι → WRes → Prop

variable {ι : Type}

abbrev OpTabK (ι : Type) := UInt32 → UInt32 → Option (OpEntK ι)

/-- What a stop owes, at every world, index and list. -/
abbrev ContK (ι : Type) := ι → Nat → List SRec → Expr → WProp

/-- A protocol table at the index, owing a world-indexed continuation. -/
abbrev TableK (ι : Type) := Nat → List SRec → Expr → ContK ι → WProp

/-- `cancelOKN` at the resumption world. -/
def cancelOKK (en : OpEntK ι) (y : ι) (k : Nat) (ls : List SRec) (K : Kont) : WProp := fun ρ =>
  ∀ P, en.fin = some P → P y k ls (K.dead.plug (raiseE (.val (cancelVal none)))) ρ

/-- **The Kripke stop at the floor bound `lo`**: the stop chooses a floor `f ≤ lo`, and owes
`contShareN`'s obligations at every world `y` the entry allows at `f`, read at `y`. -/
def contShareK (en : OpEntK ι) (lo : Life) (k : Nat) (ls : List SRec) (K : Kont) (Ψ : ContK ι) :
    WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∃ f, f ≤ lo ∧ ∀ y, en.wk f y ρ → ∀ ls', en.wc ls ls' ρ →
    (∀ k', k' < k → ∀ w : Val, (en.PB y k' ls' w ─⋆ Ψ y k' ls' (K.plug (.val w))) ρ) ∧
    (en.q ≠ .lin → cancelOKK en y k ls' K ρ)

/-- `performStopN` at the Kripke stop, at the floor bound `lo`. -/
def performStopK (lo : Life) (T : OpTabK ι) : TableK ι := fun k ls t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntK ι) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆ (en.PA k ls v ⋆ contShareK en lo k ls K Ψ)

/-- `raiseStopN`: an abortive stop owes no continuation, so it reads no world and no floor. -/
def raiseStopK (T : OpTabK ι) : TableK ι := fun k ls t _ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntK ι) =>
      ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
        T n i = some en ∧ en.abort = true⌝ ⋆
        ((fun ρ => en.PA k ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ)

/-- `opTableN` at the floor bound `lo`. -/
def opTableK (lo : Life) (T : OpTabK ι) : TableK ι := fun k ls t Ψ =>
  BoLo.or (performStopK lo T k ls t Ψ) (raiseStopK T k ls t Ψ)

/-- A table reads what is owed only below the index it stops at, at every world. -/
def TableK.Local (Tb : TableK ι) : Prop :=
  ∀ k ls t (Ψ Ψ' : ContK ι) ρ, (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
    Tb k ls t Ψ ρ → Tb k ls t Ψ' ρ

/-- One table allows every stop another does, owing the same. -/
def TableK.Le (Tb Tb' : TableK ι) : Prop :=
  ∀ k ls t (Ψ : ContK ι) ρ, Tb k ls t Ψ ρ → Tb' k ls t Ψ ρ

/-- A table is downward closed in its index. -/
def TableK.Down (Tb : TableK ι) : Prop :=
  ∀ k ls t Ψ ρ, Tb (k + 1) ls t Ψ ρ → Tb k ls t Ψ ρ

theorem opTableK_local (lo : Life) (T : OpTabK ι) : (opTableK lo T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ y k' hk _ _ _ ((hcont y hy ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont y hy ls' he).2⟩⟩⟩
  · exact Or.inr h

/-- **A table at a lower floor allows fewer stops**: a stop's floor is at most the table's. -/
theorem opTableK_floor_le {lo lo' : Life} (hlo : lo ≤ lo') (T : OpTabK ι) :
    (opTableK lo T).Le (opTableK lo' T) := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, f, le_trans hf hlo, hcont⟩⟩
  · exact Or.inr h

/-- An operation table's predicates read at the current index are downward closed. -/
structure OpTabK.Down (T : OpTabK ι) : Prop where
  pa : ∀ n i en, T n i = some en → ∀ k ls v ρ, en.PA (k + 1) ls v ρ → en.PA k ls v ρ
  fin : ∀ n i en P, T n i = some en → en.fin = some P → ∀ y k ls e ρ, P y (k + 1) ls e ρ →
    P y k ls e ρ

theorem opTableK_down {lo : Life} {T : OpTabK ι} (hT : T.Down) : (opTableK lo T).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk => (hcont y hy ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP _ _ _ _ _ ((hcont y hy ls' he).2 hq P hP)⟩⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρn, hc, ⟨hA, hnA⟩, hnn⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩
      ⟨ρa, ρn, hc, ⟨hT.pa _ _ _ h₃ _ _ _ _ hA, hnA⟩, hnn⟩⟩

/-- The cancel obligations of `T`'s entries are kept, at every world, when a context `K` is put
around the continuation they cancel (`OpTabN.CtxClosed`). -/
def OpTabK.CtxClosed (T : OpTabK ι) (K : Kont) : Prop :=
  ∀ m i en P, T m i = some en → en.fin = some P → ∀ y k ls (K' : Kont) x ρ,
    P y k ls (K'.dead.plug x) ρ → P y k ls ((K.comp K').dead.plug x) ρ

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

theorem erwpK_fold_at {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hTb : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} {n N : Nat} (hnN : n ≤ N) {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) (Φ x) (erwpPostK (V x) (Tb x) Q (erwpCK (ℍ := ℍ) V Φ Tb Q N)) n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ := by
  rw [erwpK_eq]
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb x k ls' t _ _ ρ' (fun y k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpCK, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

/-- **A run at a later world, read at the earlier one.** Along `V` the location family is the
same, the later table allows no more stops, and `V` is transitive; so a run at `y` is a run at `x`.
This is how a continuation run at the world a value was posted at joins the run before it. -/
theorem erwpK_shift {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦV : ∀ x y, V x y → Φ y = Φ x) {Tb : ι → TableK ι}
    (hTV : ∀ x y, V x y → (Tb y).Le (Tb x)) (hTb : ∀ x, (Tb x).Local) {Q : ι → PostN} {x y : ι}
    (hxy : V x y) {k N : Nat} (hk : k ≤ N) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ Tb Q y k ls e ρ) :
    rwpG (ℍ := ℍ) (Φ x) (erwpPostK (V x) (Tb x) Q (erwpCK (ℍ := ℍ) V Φ Tb Q N)) k ls e ρ := by
  have h' := erwpK_unfold_at hTb hk h
  rw [hΦV x y hxy] at h'
  refine rwpG_mono (fun k' ls' t σ ht => ?_) h'
  rcases ht with ⟨v, hv, z, hz, hq⟩ | ht
  · exact Or.inl ⟨v, hv, z, hVt x y z hxy hz, hq⟩
  · exact Or.inr (hTV x y hxy _ _ _ _ _ ht)

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

/-- An entry at one world, read at `Unit`: every floor and every world allowed. -/
def liftEntK (en : OpEntN) : OpEntK Unit where
  q := en.q
  abort := en.abort
  PA := en.PA
  PB := fun _ => en.PB
  fin := en.fin.map (fun P _ => P)
  wc := en.wc
  wk := fun _ _ _ => True

def liftTabK (T : OpTabN) : OpTabK Unit := fun m i => (T m i).map liftEntK

theorem liftTabK_some {T : OpTabN} {m i : UInt32} {en : OpEntK Unit} (h : liftTabK T m i = some en) :
    ∃ en₀, T m i = some en₀ ∧ en = liftEntK en₀ := by
  simp only [liftTabK, Option.map_eq_some_iff] at h
  obtain ⟨en₀, h₀, rfl⟩ := h
  exact ⟨en₀, h₀, rfl⟩

theorem liftTabK_of_some {T : OpTabN} {m i : UInt32} {en : OpEntN} (h : T m i = some en) :
    liftTabK T m i = some (liftEntK en) := by
  simp [liftTabK, h]

theorem cancelOKK_liftEntK (en : OpEntN) (k : Nat) (ls : List SRec) (K : Kont) (ρ : WRes) :
    cancelOKK (liftEntK en) () k ls K ρ ↔ cancelOKN en k ls K ρ := by
  constructor
  · intro h P hP
    exact h (fun _ => P) (by simp [liftEntK, hP])
  · intro h P hP
    simp only [liftEntK, Option.map_eq_some_iff] at hP
    obtain ⟨P₀, hP₀, rfl⟩ := hP
    exact h P₀ hP₀

theorem contShareK_liftEntK (en : OpEntN) (lo : Life) (k : Nat) (ls : List SRec) (K : Kont)
    (Ψ : ContK Unit) (ρ : WRes) :
    contShareK (liftEntK en) lo k ls K Ψ ρ ↔ contShareN en k ls K (Ψ ()) ρ := by
  constructor
  · rintro ⟨hu, f, -, h⟩
    refine ⟨hu, fun ls' he => ⟨(h () trivial ls' he).1, fun hq => ?_⟩⟩
    exact (cancelOKK_liftEntK en k ls' K ρ).mp ((h () trivial ls' he).2 hq)
  · rintro ⟨hu, h⟩
    refine ⟨hu, lo, le_rfl, fun y _ ls' he => ⟨(h ls' he).1, fun hq => ?_⟩⟩
    exact (cancelOKK_liftEntK en k ls' K ρ).mpr ((h ls' he).2 hq)

/-- **`opTableN` is `opTableK` at one world**, at any floor bound. -/
theorem opTableK_liftTab (lo : Life) (T : OpTabN) (k : Nat) (ls : List SRec) (t : Expr)
    (Ψ : ContK Unit) (ρ : WRes) :
    opTableK lo (liftTabK T) k ls t Ψ ρ ↔ liftTb (opTableN T) k ls t Ψ ρ := by
  simp only [liftTb, opTableK, opTableN, BoLo.or]
  constructor
  · rintro (⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩)
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hcs⟩ := pure_sep_iff.mp h
      obtain ⟨en₀, he₀, rfl⟩ := liftTabK_some h₃
      exact Or.inl ⟨K, n, i, v, en₀, pure_sep_mk ⟨h₁, h₂, he₀, h₄⟩
        ⟨ρa, ρk, hc, hA, (contShareK_liftEntK en₀ lo k ls K Ψ ρk).mp hcs⟩⟩
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hr⟩ := pure_sep_iff.mp h
      obtain ⟨en₀, he₀, rfl⟩ := liftTabK_some h₃
      exact Or.inr ⟨K, n, i, v, en₀, pure_sep_mk ⟨h₁, h₂, he₀, h₄⟩ hr⟩
  · rintro (⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩)
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hcs⟩ := pure_sep_iff.mp h
      exact Or.inl ⟨K, n, i, v, liftEntK en, pure_sep_mk ⟨h₁, h₂, liftTabK_of_some h₃, h₄⟩
        ⟨ρa, ρk, hc, hA, (contShareK_liftEntK en lo k ls K Ψ ρk).mpr hcs⟩⟩
    · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hr⟩ := pure_sep_iff.mp h
      exact Or.inr ⟨K, n, i, v, liftEntK en, pure_sep_mk ⟨h₁, h₂, liftTabK_of_some h₃, h₄⟩ hr⟩

/-- **The embedding at an operation table**: `erwp` at `opTableN T` is `erwpK` at one world, at
`opTableK` of the lifted table, at any floor bound. -/
theorem erwp_opTableN_eq_erwpK (lo : Life) (Φ : LocFam) (T : OpTabN) (Q : PostN) (n : Nat)
    (ls : List SRec) (e : Expr) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e =
      erwpK (ℍ := ℍ) (fun _ _ => True) (fun _ => Φ) (fun _ => opTableK lo (liftTabK T))
        (fun _ => Q) () n ls e := by
  have hT : (fun _ : Unit => opTableK lo (liftTabK T)) = fun _ => liftTb (opTableN T) := by
    funext _ k ls t Ψ ρ
    exact propext (opTableK_liftTab lo T k ls t Ψ ρ)
  rw [hT]
  exact erwp_eq_erwpK Φ (opTableN T) Q n ls e

/-! ### Values, steps, garbage and downward closure -/

theorem erwpK_zero {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} {ls : List SRec} {e : Expr} {ρ : WRes} : erwpK (ℍ := ℍ) V Φ Tb Q x 0 ls e ρ := by
  rw [erwpK_eq]; exact rwpG_zero

/-- **A value in the postcondition** at the run's own world (`erwp_val`); the post's order is
reflexive there. -/
theorem erwpK_val {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} (hV : V x x) {n : Nat} {ls : List SRec} {v : Val} {ρ : WRes} (h : Q x n ls v ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls v.1 ρ := by
  rw [erwpK_eq]
  exact rwpG_here (fun μ => final_val μ v) (Or.inl ⟨v, rfl, x, hV, h⟩)

/-- **Garbage at `erwpK`** (`erwp_garbage`). -/
theorem erwpK_garbage {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} {n : Nat} {ls : List SRec} {e : Expr} {ρ g ρg : WRes} (hc : ResU.CompS ρ g ρg)
    (hg : NoOwn g) (h : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρg := by
  rw [erwpK_eq] at h ⊢
  exact rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ => ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩)
    (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hc h hg))

/-- `erwpK`'s postcondition is downward closed. -/
theorem erwpPostK_down {V : ι → Prop} {Tb : TableK ι} (hTb : Tb.Down) {Q : ι → PostN}
    (hQ : ∀ y, (Q y).Down) (Ψ : ContK ι) : (erwpPostK V Tb Q Ψ).Down := by
  intro k ls t ρ h
  rcases h with ⟨v, hv, y, hy, hq⟩ | h
  · exact Or.inl ⟨v, hv, y, hy, hQ y _ _ _ _ hq⟩
  · exact Or.inr (hTb _ _ _ _ _ h)

/-- **`erwpK` is downward closed** (`erwp_le`). -/
theorem erwpK_le {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} (hΦ : (Φ x).Down) (hTb : ∀ x, (Tb x).Local) (hTd : (Tb x).Down)
    (hQ : ∀ y, (Q y).Down) {m n : Nat} (hmn : m ≤ n) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ) : erwpK (ℍ := ℍ) V Φ Tb Q x m ls e ρ :=
  erwpK_fold_at hTb hmn (rwpG_le hΦ (erwpPostK_down hTd hQ _) hmn (erwpK_unfold_at hTb le_rfl h))

/-- A deterministic step in front of an `erwpK`, for free (`erwp_det`). -/
theorem erwpK_det {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down) (hQ : ∀ y, (Q y).Down) {n : Nat}
    {ls : List SRec} {e e' : Expr} {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e' ρ) : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ := by
  rw [erwpK_eq] at h ⊢
  exact rwpG_det hΦ (erwpPostK_down hTd hQ _) hdet h

/-! ### The `rwpG` bridge -/

/-- **A computation that never stops is in `erwpK`** at every table (`erwp_of_rwp`): its value is
posted at the run's own world. -/
theorem erwpK_of_rwp {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} (hV : V x x) {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwp (ℍ := ℍ) (Φ x) (Q x) n ls e ρ) : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ := by
  rw [erwpK_eq]
  exact rwpG_mono (fun _ _ _ _ ⟨v, hv, hq⟩ => Or.inl ⟨v, hv, x, hV, hq⟩) (rwp_iff_rwpG.mp h)

/-- **A computation that never stops, then an `erwpK`** at the same world (`erwp_bindR`). -/
theorem erwpK_bindR {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι}
    (hL : ∀ x, (Tb x).Local) {Q : ι → PostN} {x : ι} (hΦ : (Φ x).Down) (K : Kont) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwp (ℍ := ℍ) (Φ x) (fun k ls' v => erwpK (ℍ := ℍ) V Φ Tb Q x k ls' (K.plug v.1)) n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls (K.plug e) ρ := by
  rw [erwpK_eq]
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨v, hv, hq⟩ => ?_) (rwp_iff_rwpG.mp h)
  subst hv
  exact erwpK_unfold_at hL hk hq

/-! ### Monotonicity -/

/-- **`erwpK` is monotone** in its post order, its postcondition and its tables, each table read
below the index at every world (`erwp_mono`). -/
theorem erwpK_mono {V V' : ι → ι → Prop} {Φ : ι → LocFam} {Tb Tb' : ι → TableK ι}
    {Q Q' : ι → PostN} (hV : ∀ x y, V x y → V' x y)
    (hQ : ∀ y k ls v ρ, Q y k ls v ρ → Q' y k ls v ρ)
    (hT : ∀ x k ls t (Ψ Ψ' : ContK ι) ρ,
      (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
      Tb x k ls t Ψ ρ → Tb' x k ls t Ψ' ρ) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ → erwpK (ℍ := ℍ) V' Φ Tb' Q' x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ht
  · exact Or.inl ⟨v, hv, y, hV x y hy, hQ _ _ _ _ _ hq⟩
  · refine Or.inr (hT x k ls' t _ _ σ (fun y k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpCK, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) _ _ _ _ hΨ

/-! ### Bind -/

/-- **Bind at `erwpK`** (`erwp_bind`, DNB's Lemma 3), around a context with no handler and no
catcher. The rest runs at the world the value was posted at, so its premise is read at every
world; along the post order the location family is the same and the table allows no more stops
(`erwpK_shift`). -/
theorem erwpK_bind {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {T : ι → OpTabK ι} (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    {Q Q' : ι → PostN} (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) (hK : ∀ x, (T x).CtxClosed K)
    (hcont : ∀ y k ls (v : Val) ρ, Q' y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q y k ls (K.plug v.1) ρ) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q' x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls (K.plug e) ρ := by
  have hL : ∀ z, (opTableK (fl z) (T z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ht | ht
  · exact erwpK_shift hVt hΦV hTV hL hy hk (hcont y k ls' v σ hv)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont'⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by simp [hasHnd_comp, hH, hK₁]
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont' y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) y _ _ _ hc
    · exact hK x m i en P hT hP y _ _ _ _ _ ((hcont' y hy ls'' he).2 hq' P hP)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).Catches m = false := by simp [catches_comp, hC, hK₁]
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ hrest⟩))

/-! ### The plain frame -/

/-- **A run's returned resource is valid**: `↭` gives it. -/
theorem rwpG_validK {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) :
    rwpG (ℍ := ℍ) Φ (fun k ls t ρ' => Q k ls t ρ' ∧ ResU.Valid ρ') n ls e ρ := by
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, (ResU.Valid.split h₆ h₇.2.2).1⟩

/-- **A plain frame around an effectful computation at `erwpK`** (`erwp_frame_plain`), the frame
read at a world. At a stop the frame joins the continuation's share and is read at the world the
continuation is resumed at (`hFk`), the entry's order read at the run's own share (`hkl`), both at
the joint share, which is valid (`rwpG_validK`); at a value, at the world the value was posted at
(`hFV`). -/
theorem erwpK_frame_plain {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {T : ι → OpTabK ι} (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    (K : Kont) (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false)
    (Fr : ι → List SRec → WProp)
    (hFs : ∀ x ls ls', (∀ a, a ∈ ls' ↔ a ∈ ls) → ∀ ρ, Fr x ls ρ → Fr x ls' ρ)
    (hFV : ∀ x y, V x y → ∀ ls ρ, Fr x ls ρ → Fr y ls ρ)
    (hwl : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → en.wc ls ls' ρ)
    (hkl : ∀ x n i en, T x n i = some en → ∀ f y ρ σ ρ', ResU.CompS ρ σ ρ' → ResU.Valid ρ' →
      en.wk f y ρ' → en.wk f y ρ)
    (hFe : ∀ x n i en, T x n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' →
      en.wc ls ls' ρ' → Fr x ls σ → Fr x ls' σ)
    (hFk : ∀ x n i en, T x n i = some en → ∀ f y ls ρ σ ρ', ResU.CompS ρ σ ρ' →
      ResU.Valid ρ' → en.wk f y ρ' → Fr x ls σ → Fr y ls σ)
    (hW : ∀ x n i en, T x n i = some en → en.abort = true → ∀ ls ρ, Fr x ls ρ → NoOwn ρ)
    (hU : ∀ x n i en, T x n i = some en → en.q = .unr → ∀ ls ρ, Fr x ls ρ → ρ = PMap.empty)
    (hK : ∀ x n i en, T x n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ y k ls K₁ ρ σ ρ', cancelOKK en y k ls K₁ ρ → Fr y ls σ → ResU.CompS ρ σ ρ' →
        cancelOKK en y k ls (K.comp K₁) ρ')
    (Q₁ Q : ι → PostN)
    (hkv : ∀ y k ls (v : Val) ρ, (Q₁ y k ls v ⋆ Fr y ls) ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q y k ls (K.plug v.1) ρ) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q₁ x n ls e ρ →
      ∀ ρ₂ ρ', Fr x ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls (K.plug e) ρ' := by
  have hL : ∀ z, (opTableK (fl z) (T z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h ρ₂ ρ' hF hc
  rw [erwpK_eq] at h ⊢
  refine rwpG_bind (hΦ x) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hcσ, hp, hF'⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (Fr x) (hFs x) hc h hF))
  rcases hp with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact erwpK_shift hVt hΦV hTV hL hy hk
      (hkv y k ls' v σ ⟨σ₁, σ₂, hcσ, hv, hFV x y hy ls' σ₂ hF'⟩)
  · -- a `perform`: the frame joins the continuation's share
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨ρk', hk', hcσ'⟩ := compS_reassoc hcak hcσ
    have hvk : ResU.Valid ρk' := (ResU.Valid.split hcσ' hvσ).2
    have hKo : (K.comp K₁).HasHnd m = false := by rw [hasHnd_comp, hH, hK₁]; rfl
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ ⟨ρa, ρk', hcσ', hA,
        fun hq => ?_, f, hf, fun y hy ls'' he => ⟨fun k' hk'' w τ₁ τ₂ hB hcτ => ?_,
          fun hq P hP => ?_⟩⟩⟩))
    · rw [hu hq, hU x m i en hT hq ls' σ₂ hF'] at hk'
      exact eq_of_compS_empty_left hk'
    · have hyk := hkl x m i en hT f y ρk σ₂ ρk' hk' hvk hy
      have hFy := hFk x m i en hT f y ls'' ρk σ₂ ρk' hk' hvk hy
        (hFe x m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF')
      obtain ⟨z, hz, hcz⟩ := compS_exch hk' hcτ
      have h₁ := (hcont y hyk ls'' (hwl x m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).1 k' hk'' w τ₁ z
        hB hz
      simp only [erwpCK, show k' < n by omega, if_true] at h₁ ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y ls'' _ z h₁ σ₂ τ₂ hFy hcz
    · have hyk := hkl x m i en hT f y ρk σ₂ ρk' hk' hvk hy
      have hFy := hFk x m i en hT f y ls'' ρk σ₂ ρk' hk' hvk hy
        (hFe x m i en hT ls' ls'' ρk σ₂ ρk' hk' he hF')
      exact hK x m i en hT ha hq y k ls'' K₁ ρk σ₂ ρk'
        (fun P hP => (hcont y hyk ls'' (hwl x m i en hT ls' ls'' ρk σ₂ ρk' hk' he)).2 hq P hP)
        hFy hk' P hP
  · -- a `raise`: the frame is left behind
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hn⟩ := pure_sep_iff.mp hp
    obtain ⟨ρn', hn', hcσ'⟩ := compS_reassoc hcan hcσ
    have hKo : (K.comp K₁).Catches m = false := by rw [catches_comp, hC, hK₁]; rfl
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ ⟨ρa, ρn', hcσ', ⟨hPA, hnA⟩,
        noOwn_compS hn' hn (hW x m i en hT ha ls' σ₂ hF')⟩⟩))

/-! ### `perform` -/

/-- **A Kripke stop at a must-resume operation** (`erwp_perform`): the payload in `PA`, a floor
`f` no higher than the table's, and the continuation owed at every world the entry allows at `f`,
every answer there and every lower index. -/
theorem erwpK_perform {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {T : ι → OpTabK ι}
    {Q : ι → PostN} {x : ι} (K : Kont) {m i : UInt32} {v : Val} {en : OpEntK ι}
    (hK : K.HasHnd m = false) (hT : T x m i = some en) (ha : en.abort = false)
    (hq : en.q = .lin) {n : Nat} {ls : List SRec} {ρa ρk ρ : WRes} (hc : ResU.CompS ρa ρk ρ)
    (hA : en.PA n ls v ρa) (f : Life) (hf : f ≤ fl x)
    (hk : ∀ y, en.wk f y ρk → ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB y k' ls' w ─⋆
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q y k' ls' (K.plug (.val w))) ρk) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls
      (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwpK_eq]
  refine rwpG_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr (Or.inl
    ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk, hc, hA,
      fun hu => absurd (hq.symm.trans hu) (by simp), f, hf, fun y hy ls' he =>
        ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' => absurd hq hq'⟩⟩⟩))
  simp only [erwpCK, hk', if_true]
  exact hk y hy ls' he k' hk' w τ₁ τ₂ hB hcτ

/-! ### The old statements as the instance at one world -/

/-- `erwp_val` from `erwpK_val`. -/
theorem erwp_val_of_K {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec} {v : Val}
    {ρ : WRes} (h : Q n ls v ρ) : erwp (ℍ := ℍ) Φ Tb Q n ls v.1 ρ := by
  rw [erwp_eq_erwpK]
  exact erwpK_val (ℍ := ℍ) (V := fun _ _ => True) (x := ()) trivial h

/-- `erwp_of_rwp` from `erwpK_of_rwp`. -/
theorem erwp_of_rwp_of_K {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : rwp (ℍ := ℍ) Φ Q n ls e ρ) : erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp_eq_erwpK]
  exact erwpK_of_rwp (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (Q := fun _ => Q)
    (x := ()) trivial h

theorem liftTb_local {Tb : TableN} (hL : Tb.Local) : (liftTb Tb).Local :=
  fun k ls t Ψ Ψ' ρ hΨ h => hL k ls t (Ψ ()) (Ψ' ()) ρ (fun k' hk ls e ρ => hΨ () k' hk ls e ρ) h

/-- `erwp_bindR` from `erwpK_bindR`. -/
theorem erwp_bindR_of_K {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) {Q : PostN}
    (K : Kont) {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwp (ℍ := ℍ) Φ (fun k ls' v => erwp (ℍ := ℍ) Φ Tb Q k ls' (K.plug v.1)) n ls e ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug e) ρ := by
  rw [erwp_eq_erwpK]
  refine erwpK_bindR (ℍ := ℍ) (Φ := fun _ => Φ) (fun _ => liftTb_local hL) (x := ()) hΦ K ?_
  simpa only [erwp_eq_erwpK] using h

/-- `erwp_mono` from `erwpK_mono`. -/
theorem erwp_mono_of_K {Φ : LocFam} {Tb Tb' : TableN} {Q Q' : PostN}
    (hQ : ∀ k ls v ρ, Q k ls v ρ → Q' k ls v ρ)
    (hT : ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      Tb k ls t Ψ ρ → Tb' k ls t Ψ' ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ Tb Q n ls e ρ → erwp (ℍ := ℍ) Φ Tb' Q' n ls e ρ := by
  intro n ls e ρ h
  rw [erwp_eq_erwpK] at h ⊢
  exact erwpK_mono (ℍ := ℍ) (fun _ _ h => h) (fun _ k ls v ρ h => hQ k ls v ρ h)
    (fun _ k ls t Ψ Ψ' ρ hΨ h => hT k ls t (Ψ ()) (Ψ' ()) ρ
      (fun k' hk ls e ρ => hΨ () k' hk ls e ρ) h) n () ls e ρ h

theorem liftTabK_ctxClosed {T : OpTabN} {K : Kont} (hK : T.CtxClosed K) :
    (liftTabK T).CtxClosed K := by
  intro m i en P hT hP y k ls K' x ρ h
  obtain ⟨en₀, hT₀, rfl⟩ := liftTabK_some hT
  simp only [liftEntK, Option.map_eq_some_iff] at hP
  obtain ⟨P₀, hP₀, rfl⟩ := hP
  exact hK m i en₀ P₀ hT₀ hP₀ k ls K' x ρ h

/-- `erwp_bind` from `erwpK_bind`. -/
theorem erwp_bind_of_K (lo : Life) {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} {Q Q' : PostN}
    (K : Kont) (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false)
    (hK : T.CtxClosed K)
    (hcont : ∀ k ls (v : Val) ρ, Q' k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (K.plug v.1) ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q' n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug e) ρ := by
  intro n ls e ρ h
  rw [erwp_opTableN_eq_erwpK lo] at h ⊢
  refine erwpK_bind (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => lo)
    (T := fun _ => liftTabK T) (fun _ _ _ _ _ _ _ _ h => h) K hH hC (fun _ => liftTabK_ctxClosed hK)
    ?_ n () ls e ρ h
  intro y k ls' v ρ' hv
  rw [← erwp_opTableN_eq_erwpK lo]
  exact hcont k ls' v ρ' hv

/-- `erwp_frame_plain` from `erwpK_frame_plain`. -/
theorem erwp_frame_plain_of_K (lo : Life) {Φ : LocFam} (hΦ : Φ.Down) (T : OpTabN) (K : Kont)
    (hH : ∀ n, K.HasHnd n = false) (hC : ∀ n, K.Catches n = false) (Fr : List SRec → WProp)
    (hFs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, Fr ls ρ → Fr ls' ρ)
    (hwl : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      en.wc ls ls' ρ)
    (hFe : ∀ n i en, T n i = some en → ∀ ls ls' ρ σ ρ', ResU.CompS ρ σ ρ' → en.wc ls ls' ρ' →
      Fr ls σ → Fr ls' σ)
    (hW : ∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    (hU : ∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty)
    (hK : ∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ k ls K₁ ρ σ ρ', cancelOKN en k ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOKN en k ls (K.comp K₁) ρ')
    (Q₁ Q : PostN)
    (hkv : ∀ k ls (v : Val) ρ, (Q₁ k ls v ⋆ Fr ls) ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (K.plug v.1) ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q₁ n ls e ρ →
      ∀ ρ₂ ρ', Fr ls ρ₂ → ResU.CompS ρ ρ₂ ρ' →
        erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug e) ρ' := by
  intro n ls e ρ h ρ₂ ρ' hF hc
  rw [erwp_opTableN_eq_erwpK lo] at h ⊢
  refine erwpK_frame_plain (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => lo)
    (T := fun _ => liftTabK T) (fun _ _ _ _ _ _ _ _ h => h) K hH hC (fun _ => Fr)
    (fun _ => hFs) (fun _ _ _ _ ρ h => h) ?_ ?_ ?_
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ (fun _ => Q₁) (fun _ => Q) ?_
    n () ls e ρ h ρ₂ ρ' hF hc
  · intro _ m i en hT
    obtain ⟨en₀, hT₀, rfl⟩ := liftTabK_some hT
    exact hwl m i en₀ hT₀
  · intro _ m i en hT _ _ _ _ _ _ _ _
    obtain ⟨en₀, hT₀, rfl⟩ := liftTabK_some hT
    trivial
  · intro _ m i en hT
    obtain ⟨en₀, hT₀, rfl⟩ := liftTabK_some hT
    exact hFe m i en₀ hT₀
  · intro _ m i en hT
    obtain ⟨en₀, hT₀, rfl⟩ := liftTabK_some hT
    exact hW m i en₀ hT₀
  · intro _ m i en hT
    obtain ⟨en₀, hT₀, rfl⟩ := liftTabK_some hT
    exact hU m i en₀ hT₀
  · intro _ m i en hT ha hq y k ls' K₁ ρ σ ρ' hcan hFσ hc'
    obtain ⟨en₀, hT₀, rfl⟩ := liftTabK_some hT
    exact (cancelOKK_liftEntK en₀ k ls' (K.comp K₁) ρ').mpr (hK m i en₀ hT₀ ha hq k ls' K₁ ρ σ ρ'
      ((cancelOKK_liftEntK en₀ k ls' K₁ ρ).mp hcan) hFσ hc')
  · intro y k ls' v ρ' hv
    rw [← erwp_opTableN_eq_erwpK lo]
    exact hkv k ls' v ρ' hv

/-- `erwp_perform` from `erwpK_perform`. -/
theorem erwp_perform_of_K (lo : Life) {Φ : LocFam} {T : OpTabN} {Q : PostN} (K : Kont)
    {m i : UInt32} {v : Val} {en : OpEntN} (hK : K.HasHnd m = false) (hT : T m i = some en)
    (ha : en.abort = false) (hq : en.q = .lin) {n : Nat} {ls : List SRec} {ρa ρk ρ : WRes}
    (hc : ResU.CompS ρa ρk ρ) (hA : en.PA n ls v ρa)
    (hk : ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB k' ls' w ─⋆ erwp (ℍ := ℍ) Φ (opTableN T) Q k' ls' (K.plug (.val w))) ρk) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwp_opTableN_eq_erwpK lo]
  refine erwpK_perform (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fl := fun _ => lo)
    (T := fun _ => liftTabK T) (Q := fun _ => Q) (x := ()) K hK (liftTabK_of_some hT) ha hq hc hA lo
    le_rfl ?_
  intro y _ ls' he k' hk' w
  have h := hk ls' he k' hk' w
  rw [erwp_opTableN_eq_erwpK lo] at h
  exact h

/-! ### The typed world -/

/-- A world of the typed instance: a location typing, a view, and the floor below which every lend
taken from here on lies. -/
structure KW where
  Θ : LocTy
  c : Loc → Option Life
  lo : Life

/-- The worlds a fold at `A` can be taken at: `A` fresh, no `imm` record lent at `A`. -/
def LocTy.FoldInv (A : Life) (Θ : LocTy) : Prop := Θ.Fresh A ∧ ∀ x ∈ Θ.imm, x.2 ≠ A

/-- **A post's world**: the run's location typing and view, at a floor no higher. -/
def KW.Post (x y : KW) : Prop := y.Θ = x.Θ ∧ y.c = x.c ∧ y.lo ≤ x.lo

theorem KW.post_refl (x : KW) : x.Post x := ⟨rfl, rfl, le_rfl⟩

theorem KW.Post.trans {x y z : KW} (h₁ : x.Post y) (h₂ : y.Post z) : x.Post z :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, le_trans h₂.2.2 h₁.2.2⟩

/-- **The worlds a stop at `x` owes its continuation at**, at the floor `f` it chose and the
continuation's share `ρ`: `ExtP f` at the share, a valid location typing, every view consistent
with the share, a floor no higher than `x`'s, and `FoldInv g` kept at every floor `g ≥ f`. A stop
under live lends at `A > B` chooses `B`; the frame of the lend at `A` re-enters at the resumption
world, where it needs `FoldInv A`. -/
def KW.Owed (x : KW) (f : Life) (y : KW) (ρ : WRes) : Prop :=
  x.Θ.ExtP f y.Θ ρ ∧ y.Θ.OK ∧ ConsistentX y.c ρ ∧ y.lo ≤ x.lo ∧
    (∀ g, f ≤ g → x.Θ.FoldInv g → y.Θ.FoldInv g)

/-- **A stop's own world is owed, at every floor**: a handler that resumes in place does not need
to know the floor the stop chose. -/
theorem KW.owed_self {x : KW} (hΘ : x.Θ.OK) (f : Life) {ρ : WRes} (hc : ConsistentX x.c ρ) :
    x.Owed f x ρ :=
  ⟨LocTy.extP_refl f x.Θ ρ, hΘ, hc, le_rfl, fun _ _ h => h⟩

/-- A world reached at the same location typing and view, at a floor no higher, is owed. -/
theorem KW.owed_of_post {x y : KW} (hxy : x.Post y) (hΘ : x.Θ.OK) (f : Life) {ρ : WRes}
    (hc : ConsistentX x.c ρ) : x.Owed f y ρ := by
  obtain ⟨hΘy, hcy, hlo⟩ := hxy
  refine ⟨?_, hΘy ▸ hΘ, hcy ▸ hc, hlo, fun _ _ h => hΘy ▸ h⟩
  rw [hΘy]; exact LocTy.extP_refl f x.Θ ρ

theorem KW.Owed.trans {x y z : KW} {f : Life} {ρ : WRes} (h₁ : x.Owed f y ρ)
    (h₂ : y.Owed f z ρ) : x.Owed f z ρ :=
  ⟨h₁.1.trans h₂.1, h₂.2.1, h₂.2.2.1, le_trans h₂.2.2.2.1 h₁.2.2.2.1,
    fun g hg h => h₂.2.2.2.2 g hg (h₁.2.2.2.2 g hg h)⟩

/-- **Under a live lend at `A`, the resumption world keeps `FoldInv A`**, which the frame needs to
re-enter there. -/
theorem KW.Owed.foldInv {x y : KW} {A : Life} {ρ : WRes} (h : x.Owed A y ρ)
    (hx : x.Θ.FoldInv A) : y.Θ.FoldInv A :=
  h.2.2.2.2 A le_rfl hx

/-- **`ExtP` at the floor `A` across the fold at a frame's shares**: the lender's share
`ρkL = Z/ℓ ● W″` and the borrowed one `ρk ⊆ Z`, `Z`'s cell at `ℓ` lent at `A`
(`LocTy.ExtP.fold`, its premise `hc` discharged at these shares). -/
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

/-- **The typed fold across a Kripke stop.** The lender's stop at `x`, at the floor `A` of its live
lend at `ℓ`, owes its continuation at `y` (`KW.Owed`), and `FoldInv A` held at `x`. Then the borrowed
run's world with the lend is a public extension at the borrowed share, read at `A`, and `y` keeps
`FoldInv A`, so the frame can be re-entered there. -/
theorem kw_owed_fold {x y : KW} {A : Life} (hx : x.Θ.FoldInv A) {l : Loc}
    (F : Nat → Val → SPropS Loc Val A) {ρk ρp Z W'' ρkL : WRes} {ψ : CellU Loc Val}
    (hZ : ResU.CompS ρk ρp Z) (hZl : Z.get l = some ψ) (hat : ψ.at = A)
    (hkL : ResU.CompS (Z.del l) W'' ρkL) (hy : x.Owed A y ρkL) :
    (x.Θ.add l A F).ExtP A (y.Θ.add l A F) ρk ∧ y.Θ.FoldInv A :=
  ⟨extP_foldFrame hx.1 hx.2 F hZ hZl hat hkL hy.1, hy.foldInv hx⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
