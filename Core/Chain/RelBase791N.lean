import Core.Chain.Hardest791N
import Core.Chain.SI.TabLeN
import Core.Chain.SI.StopRaiseN
import Core.Chain.SI.LocTy

/-!
# #791 at the rule level over the chain relation: the interpretation and the statements
`[spec §62]`

The relation here is the one-world relation, its names suffixed `₀`; `Goal791N.lean` holds the
relation at the typed world `KW` under the unsuffixed names. The statements below and the files
that import this one read the one-world relation until they are restated at `KW`.

`docs/new-core/chain-interpretation.md` is the design: the world, the interpretation, the
departures from Core. `Core/TreeGoal791.lean` states #791's end goal over the tree relation; here the
interpretation and the statements are restated over Core's step-indexed chain relation `erwp`
(`Core/Chain/SI/*`), at the per-lend world `LocTy` (`Core/Chain/SI/LocTy.lean`).

* **§1. The interpretation.** `vN₀ A δ Θ k v ρ` (`𝒱⟦A⟧δ` at the world `Θ` and the index `k`) and
  `cN₀ C δ Θ c k ls e ρ` (`𝒞⟦C⟧δ` at the world `Θ`, the run's live lifetimes `c`, the index `k`
  and the record list `ls`). Every run is `erwp` at the view `Θ.view c`, the relation's `LocFam`.
  `F_Σ R` is read at the table of the row's layers (`tabN₀`, each capturable entry with its cancel
  row's obligation `finN₀`) and its answer `retN₀`. A table's answers are read at the view: an
  answer's resource enters the run, and is consistent with the view as every resource entering a
  run is (`SemJN₀`'s start, `U`'s thunk, `⊸`'s composite). Core's `vCE`/`cC`/`effTab`/`finObl`/`effRet`
  clause by clause, with `ewpTS`/`wpTS` replaced by `erwp`:
  - `Mut` is Core's `ptoMutS` shape over the world: the cell at some `b ⊒ @aδ` (`mutL b`) holds a
    member of the payload read at the world above `b`, the family the world stores at the lend's
    key, and every value of the payload is in `Res_b`;
  - `U C` is Kripke along Core's resource-relative order (`LocTy.ExtR` at the thunk's
    resource), at every view consistent with the resource (`ConsistentX`); `⊸` is Core's plain
    wand at the same world, step-indexed (every later index) and at every view consistent with
    the composite.
  - `Imm` is Core's `ptoImmS` shape over the world: one `imm` cell, its payload in the
    observable view `vO₀` (Core's `vCE false`), its location witnessed in the world's `imm`
    records (`ImmWitW`, Core's `CohE`); the relation's entry tie (`ImmTieL`) puts the witness's
    record on the run's list.
  `gN₀`, `SemJN₀`.
* **§2. Laws.** Downward closure of every piece; `vN₀`/`cN₀` read `δ` only at free variables
  (`vN_congr₀`); values stable along the resource-relative order (`vN_extR₀`), hence along the
  world-relative `ExtA` (`vN_extA₀`), computations too except at an effect row (`cN_extA₀`); values in
  a lend's stratum do not read the lend (`vN_local₀`); `𝒱⟦A⟧` of an outliving `A` in the stratum
  (`vN_outlives₀`); `F_Σ R` as `erwp` at the row's table (`cN_effOf₀`).
* **§3. The statements**: `ConstN₀`, `ConstsN₀`, `FundamentalN₀`, `BridgeN`, `Goal791SchedN`, and
  `goal791Sched_of`: `Goal791SchedN` from `FundamentalN₀` and `ConstsN₀`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC)
open BoCa.BoLo (Heap Kont hndE hndVal)

/-! ## §1. The interpretation -/

/-- An entry of a row's table: the qualifier; abortive as Core's (`B` empty, not `lin`); payload
and answer at their value types, at every record list; the cancel obligation where Core's `capB`
reads one; resumed under `extF`. -/
def entN (q : Qual) (B : VTy) (PA PB : Nat → Val → WRes → Prop)
    (fin : Option (Nat → List SRec → Expr → WProp)) : OpEntN where
  q := q
  abort := B.isZero && q != .lin
  PA := fun k _ v ρ => PA k v ρ
  PB := fun k _ v ρ => PB k v ρ
  fin := if capB q B then fin else none
  wc := extF

/-- One more layer of a table: the first match wins. -/
def extTabN (n i : UInt32) (en : OpEntN) (T : OpTabN) : OpTabN :=
  fun m j => if m = n ∧ j = i then some en else T m j

/-- **An `imm` borrow at `α`** (`ptoImmS`, `Core/Relation.lean`, without the record list): one
`imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄` whose payload is in `P`. -/
def immCell (α : Life) (P : Val → WRes → Prop) (v : Val) (ρ : WRes) : Prop :=
  ∃ (l : Loc) (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join), v = Val.loc l ∧
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ α ⊑ s.meet ∧ P u σ

/-- **The witness of an `imm` cell `imm(s, …)` at `ℓ` of type `A` at `δ`** in the world's `imm`
records: a record of the world lent no shorter-lived than the cell (`⊓s ⊑ x.2`), and Core's `CohE`
at a descendant `d` of it, a record of the world's lineage whose own cell is at `ℓ` or one of whose
chain positions is `ℓ`, at a type `TyEq` to `A`. The lifetime match is what makes the witness
relevant to the cell (`LocTy.Keeps`): the orders keep it at the cell's resource, and a record lent
below a stratum witnesses no cell in it. The relation's entry tie (`ImmTieL`) puts the record on
the run's list, whose typed world holds its descendants (`TI`). -/
def ImmWitW (I : List SRec) (l : Loc) (s : LSet) (A : VTy) (δ : LSub) : Prop :=
  ∃ x ∈ I, s.meet ≤ x.2 ∧ ∃ d, DescR x.1 d ∧ CohE [d] l A δ

/-- **A candidate for `νX. C`** at a fixed `δ`: `cN₀`'s signature with `δ` applied (Core's
`CPred`, with the world, the view and the index). -/
abbrev CandN := LocTy → (Loc → Option Life) → Nat → List SRec → Expr → WRes → Prop

/-- `R ⊆ R′` pointwise. -/
def CandN.Le (R R' : CandN) : Prop :=
  ∀ Θ c n ls e ρ, R Θ c n ls e ρ → R' Θ c n ls e ρ

/-- **`U X` at the candidate `R`** (Core's `thunkR`): `vN₀`'s `U` clause with `R` in place of
`𝒞⟦νX. C⟧`, at every extension of the world along `ExtR` at the thunk's resource, every view
consistent with it and every record list. -/
def thunkRN (R : CandN) : LocTy → Nat → Val → WRes → Prop := fun Θ n v ρ =>
  ∀ Θ' : LocTy, Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls, R Θ' c n ls v.1 ρ

/-- **An entry of `vNE₀`'s type-variable environment** (Core's `TEnt`): the closed type the
variable stands for, which the `Imm` clause's witness reads, and the candidate it is read at, over
the mode (`true` the program's relation `vN₀`, `false` the observable view `vO₀`), the world, the
index and the value. -/
structure TEntN where
  ty : VTy
  P : Bool → LocTy → Nat → Val → WRes → Prop

/-- The environment of a closed type: every variable is empty (Core's `tEnv`). -/
def tEnvN : Option (Nat → TEntN) → Nat → TEntN
  | none => fun n => ⟨.tvar n, fun _ _ _ _ _ => False⟩
  | some η => η

/-- A variable's candidate (Core's `tEnvP`). -/
def tEnvPN : Option (Nat → TEntN) → Nat → Bool → LocTy → Nat → Val → WRes → Prop
  | none, _, _, _, _, _, _ => False
  | some η, n, b, Θ, k, v, ρ => (η n).P b Θ k v ρ

/-- The closed type a type stands for under the environment (Core's `tClose`). -/
def tCloseN : Option (Nat → TEntN) → VTy → VTy
  | none, A => A
  | some η, A => A.subst (fun n => (η n).ty)

/-- **`X`'s candidate in `νX. C`'s one-entry environment** (Core's `nuP`): `P` in the program's
relation, `True` in the observable view. -/
def nuPN (P : LocTy → Nat → Val → WRes → Prop) : Bool → LocTy → Nat → Val → WRes → Prop
  | true => P
  | false => fun _ _ _ _ => True

/-- **The one-entry environment of a `ν` observation** (Core's `nuEnv`): `X` (index `0`) stands for
the closed type `S` and is read at `nuPN P`; every other variable is empty. -/
def nuEnvN (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) : Option (Nat → TEntN) :=
  some (VTy.scons ⟨S, nuPN P⟩ (tEnvN none))

/-! ### The environment (Core's `RelMu`)

`vNE₀ η` reads a type variable at its entry in `η` and `μX. A` at the least fixed point, the
candidate joint over the mode, the world and the index. `vBN₀ η b` is `vNE₀ η` (`b = true`) or
`vOE₀ η` (`b = false`), Core's `vCE η b`. Every law below is Core's (`Core/RelMu.lean`), read at
the chain's arguments. -/

theorem TEntN.ext' {a b : TEntN} (h₁ : a.ty = b.ty) (h₂ : a.P = b.P) : a = b := by
  cases a; cases b; simp only at h₁ h₂; subst h₁; subst h₂; rfl

theorem tEnvPN_eq (η : Option (Nat → TEntN)) (n : Nat) (b : Bool) (Θ : LocTy) (k : Nat) (v : Val)
    (ρ : WRes) : tEnvPN η n b Θ k v ρ = (tEnvN η n).P b Θ k v ρ := by
  cases η <;> rfl

theorem tCloseN_eq (η : Option (Nat → TEntN)) (A : VTy) :
    tCloseN η A = A.subst (fun n => (tEnvN η n).ty) := by
  cases η with
  | none => exact (VTy.subst_id A).symm
  | some η => rfl

/-- The environment of one unfolding of `μX. A` under `η` at the candidate `P`. -/
def muEnvN (η : Option (Nat → TEntN)) (A : VTy) (P : Bool → LocTy → Nat → Val → WRes → Prop) :
    Option (Nat → TEntN) :=
  some (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η))

/-! ### Renaming and substitution -/

/-! ### Monotonicity in an entry outside every `Mut` payload -/

/-! ### The unroll equation -/

/-! ### The induction principle -/

/-! ## §2. Laws -/

theorem extTabN_some {n i m j : UInt32} {en en' : OpEntN} {T : OpTabN}
    (h : extTabN n i en T m j = some en') : (m = n ∧ j = i ∧ en' = en) ∨ T m j = some en' := by
  unfold extTabN at h
  split at h
  · rename_i hmj; exact .inl ⟨hmj.1, hmj.2, (Option.some.inj h).symm⟩
  · exact .inr h

theorem extTabN_down {n i : UInt32} {q : Qual} {B : VTy} {PA PB : Nat → Val → WRes → Prop}
    {fin : Option (Nat → List SRec → Expr → WProp)} {T : OpTabN}
    (hA : ∀ k v ρ, PA (k + 1) v ρ → PA k v ρ)
    (hfin : ∀ P, fin = some P → ∀ k ls e ρ, P (k + 1) ls e ρ → P k ls e ρ) (hT : T.Down) :
    (extTabN n i (entN q B PA PB fin) T).Down where
  pa := fun m j en h k ls v ρ hp => by
    rcases extTabN_some h with ⟨-, -, rfl⟩ | h
    · exact hA k v ρ hp
    · exact hT.pa _ _ _ h k ls v ρ hp
  fin := fun m j en P h hP k ls e ρ hp => by
    rcases extTabN_some h with ⟨-, -, rfl⟩ | h
    · simp only [entN] at hP
      split at hP
      · exact hfin P hP k ls e ρ hp
      · cases hP
    · exact hT.fin _ _ _ _ h hP k ls e ρ hp
  wcl := fun m j en h => by
    rcases extTabN_some h with ⟨-, -, rfl⟩ | h
    · exact extF_left
    · exact hT.wcl _ _ _ h

theorem cancelOblN_down {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hT : T.Down) :
    ∀ k ls e ρ, cancelOblN (ℍ := ℍ) Φ T (k + 1) ls e ρ → cancelOblN (ℍ := ℍ) Φ T k ls e ρ :=
  fun _ _ _ _ h => erwp_le hΦ (cancelTabN_local T) (cancelTabN_down hT) falsePost_down
    (Nat.le_succ _) h

/-- Every entry of the environment is downward closed in the index. -/
def EnvDownN (η : Option (Nat → TEntN)) : Prop :=
  ∀ m b Θ k v ρ, (tEnvN η m).P b Θ (k + 1) v ρ → (tEnvN η m).P b Θ k v ρ

theorem envDownN_none : EnvDownN none := fun _ _ _ _ _ _ h => h

/-- A property down the index, from one step. -/
theorem down_iter {F : Nat → Prop} (step : ∀ i, F (i + 1) → F i) {j k : Nat} (hjk : j ≤ k)
    (h : F k) : F j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (step _ (by rwa [← Nat.add_assoc] at h))

/-! ### `ν`: the candidate's order -/

/-- `R ⊆ R′` at every `OK` world: the only worlds `U X` reads a candidate at. -/
def CandN.LeOK (R R' : CandN) : Prop :=
  ∀ Θ : LocTy, Θ.OK → ∀ c n ls e ρ, R Θ c n ls e ρ → R' Θ c n ls e ρ

/-- A candidate downward closed in the index at every `OK` world. -/
def CandN.Down (R : CandN) : Prop :=
  ∀ Θ : LocTy, Θ.OK → ∀ c n ls e ρ, R Θ c (n + 1) ls e ρ → R Θ c n ls e ρ

theorem thunkRN_mono {R R' : CandN} (h : R.LeOK R') :
    ∀ Θ n v ρ, thunkRN R Θ n v ρ → thunkRN R' Θ n v ρ :=
  fun _ _ _ _ hv Θ' hE hOK c hc ls => h Θ' hOK c _ ls _ _ (hv Θ' hE hOK c hc ls)

theorem thunkRN_down {R : CandN} (h : R.Down) :
    ∀ Θ n v ρ, thunkRN R Θ (n + 1) v ρ → thunkRN R Θ n v ρ :=
  fun _ _ _ _ hv Θ' hE hOK c hc ls => h Θ' hOK c _ ls _ _ (hv Θ' hE hOK c hc ls)

/-- `ν`'s one-entry environment is downward closed at a downward closed candidate. -/
theorem envDownN_nu {S : VTy} {P : LocTy → Nat → Val → WRes → Prop}
    (hP : ∀ Θ n v ρ, P Θ (n + 1) v ρ → P Θ n v ρ) : EnvDownN (nuEnvN S P) := by
  intro m b Θ k v ρ h
  cases m with
  | zero => cases b with
    | true => exact hP Θ k v ρ h
    | false => trivial
  | succ m => exact h

/-! ### Rows -/

/-! ### `δ` is read only at free variables -/

/-- `CohE` reads `δ` only at the type's free variables. -/
theorem cohE_congr_ty {rs : List FrameRec} {l : Loc} {A : VTy} {δ δ' : LSub}
    (h : ∀ y, VFree y A → δ.find? y = δ'.find? y) : CohE rs l A δ ↔ CohE rs l A δ' :=
  ⟨fun ⟨S₀, δ₀, he, hc⟩ => ⟨S₀, δ₀, (TyEq.of_agree A fun y hy => (h y hy).symm).trans he, hc⟩,
    fun ⟨S₀, δ₀, he, hc⟩ => ⟨S₀, δ₀, (TyEq.of_agree A h).trans he, hc⟩⟩

/-- `ImmWitW` reads `δ` only at the type's free variables. -/
theorem immWitW_congr {A : VTy} {δ δ' : LSub} (h : ∀ y, VFree y A → δ.find? y = δ'.find? y)
    (I : List SRec) (l : Loc) (s : LSet) : ImmWitW I l s A δ = ImmWitW I l s A δ' := by
  unfold ImmWitW
  apply propext
  constructor
  · rintro ⟨x, hx, hs, d, hd, hc⟩; exact ⟨x, hx, hs, d, hd, (cohE_congr_ty h).mp hc⟩
  · rintro ⟨x, hx, hs, d, hd, hc⟩; exact ⟨x, hx, hs, d, hd, (cohE_congr_ty h).mpr hc⟩

/-- `δ` and `δ'` agree on the free lifetime variables of every type the environment holds (Core's
`EnvAgree`). -/
def EnvAgreeN (η : Option (Nat → TEntN)) (δ₁ δ₂ : LSub) : Prop :=
  ∀ n y, VFree y (tEnvN η n).ty → δ₁.find? y = δ₂.find? y

theorem envAgreeN_none (δ₁ δ₂ : LSub) : EnvAgreeN none δ₁ δ₂ := fun _ _ hy => hy.elim

theorem envAgreeN_tClose {η : Option (Nat → TEntN)} {δ₁ δ₂ : LSub} (hη : EnvAgreeN η δ₁ δ₂)
    {A : VTy} (h : ∀ y, VFree y A → δ₁.find? y = δ₂.find? y) :
    ∀ y, VFree y (tCloseN η A) → δ₁.find? y = δ₂.find? y := by
  intro y hy
  rw [tCloseN_eq] at hy
  rcases vFree_subst A _ hy with hy | ⟨n, hn⟩
  · exact h y hy
  · exact hη n y hn

/-- `ν`'s one-entry environment agrees at `δ₁`, `δ₂` where `S` does. -/
theorem envAgreeN_nu {S : VTy} {P : LocTy → Nat → Val → WRes → Prop} {δ₁ δ₂ : LSub}
    (hS : ∀ y, VFree y S → δ₁.find? y = δ₂.find? y) : EnvAgreeN (nuEnvN S P) δ₁ δ₂ := by
  intro n y hy
  cases n with
  | zero => exact hS y hy
  | succ n => exact hy.elim

/-! ### Outliving types lie in the stratum -/

/-! ### Values along the Kripke order -/

/-- One cell at one location determines both. -/
theorem single_immOf_inj {l l' : Loc} {ψ ψ' : CellU Loc Val}
    (e : ResU.single l ψ = ResU.single l' ψ') : l = l' ∧ ψ = ψ' := by
  have h : (ResU.single l' ψ').get l = some ψ := e ▸ ResU.single_get_self l ψ
  exact ResU.single_get_eq_some h

/-- Every entry of the environment is stable along the resource-relative order. -/
def EnvExtRN (η : Option (Nat → TEntN)) : Prop :=
  ∀ m b (Θ Θ' : LocTy) k v ρ, Θ.ExtR Θ' ρ → (tEnvN η m).P b Θ k v ρ → (tEnvN η m).P b Θ' k v ρ

theorem envExtRN_none : EnvExtRN none := fun _ _ _ _ _ _ _ _ h => h

/-- The computation types `cN_extA₀` covers: `F A` and `⊤`, read through `&` and `∀`. Not
an effect row (`F_Σ R`), and not `⊸`: a plain wand at `Θ` reads its argument at `Θ`, and an
argument at an extension `Θ′` is not one at `Θ`. Not `ν`, whose observation trees hold both. -/
def noEffSpine : CTy → Prop
  | .ret _ => True
  | .arr _ _ => False
  | .amp C D => noEffSpine C ∧ noEffSpine D
  | .top => True
  | .all _ _ C => noEffSpine C
  | .nu _ => False
  | .eff _ _ _ _ _ _ _ _ => False

/-! ### Values in a lend's stratum do not read the lend -/

/-! ### `ν`: the greatest fixed point -/

/-! ### Rule checks: `⊑mut`, `⊑imm`, `∀I` at `SemJN₀` -/

/-- `Δ ⊨ a ⊑ b`'s order on interpretations is `Life`'s. -/
theorem sLe_life {m n : Life} (h : BoCa.Lifetime.SLife.Le m n) : m ≤ n := h

/-! ## §3. The statements -/

mutual
/-- **The formers the interpretation covers**: every former. `μ` is covered at a covered body, a
type variable always (its environment entry, empty at the empty environment). `ν` is covered at a
covered body, whose variable `X` (`VTy.inFragNu`) `cN₀` reads at the candidate. Families (arrays and
slices) are covered at a covered leaf, and opaque types (`Tok` and the host types) always.
Decidable. -/
def _root_.BoCa.Fig16.LogRel.Core.VTy.inFrag : VTy → Bool
  | .unit | .zero | .unk | .int _ | .opq _ => true
  | .tensor A B | .sum A B => A.inFrag && B.inFrag
  | .thunk C => C.inFrag
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .fam A | .mu A => A.inFrag
  | .tvar _ => true
/-- The computation-type formers the interpretation covers. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.inFrag : CTy → Bool
  | .ret A => A.inFrag
  | .arr A C => A.inFrag && C.inFrag
  | .amp C D => C.inFrag && D.inFrag
  | .top => true
  | .all _ _ C => C.inFrag
  | .nu C => C.inFragNu
  | .eff _ _ _ A B fin _ C => A.inFrag && B.inFrag && fin.inFrag && C.inFrag
/-- The value-type formers a `ν` body covers: `VTy.inFrag`'s, and the body's variable `X`
(index `0`). A thunk is read by `vN₀`, where `X` does not occur. -/
def _root_.BoCa.Fig16.LogRel.Core.VTy.inFragNu : VTy → Bool
  | .tvar 0 => true
  | .unit | .zero | .unk | .int _ | .opq _ => true
  | .tensor A B | .sum A B => A.inFragNu && B.inFragNu
  | .thunk C => C.inFrag
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .fam A => A.inFragNu
  | .tvar (_ + 1) | .mu _ => false
/-- The computation-type formers a `ν` body covers. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.inFragNu : CTy → Bool
  | .ret A => A.inFragNu
  | .arr A C => A.inFragNu && C.inFragNu
  | .amp C D => C.inFragNu && D.inFragNu
  | .top => true
  | .all _ _ C => C.inFragNu
  | .nu C => C.inFragNu
  | .eff _ _ _ A B fin _ C => A.inFragNu && B.inFragNu && fin.inFrag && C.inFragNu
end

/-- **A judgment inside the fragment**: its context's types and its own type use only the formers
the interpretation covers. -/
def JdgInFrag (Γ : Ctx VTy) (j : Jdg) : Bool :=
  Γ.all (fun s => s.ty.inFrag) &&
    match j with
    | .val A => A.inFrag
    | .comp C => C.inFrag

/-- **A #791 constant inside the fragment**: its type uses only the formers the interpretation
covers. -/
def _root_.BoCa.Fig16.Tree.Wp.Goal791.Const791.InFrag (c : Const791) : Prop := c.ty.inFrag = true

/-- A finaliser's judgment `L ⊸ 1` is in the fragment where `L` is. -/
theorem jdgInFrag_lolli {L : VTy} (h : L.inFrag = true) :
    JdgInFrag [] (.val (.lolli L .unit)) = true := by
  simp [JdgInFrag, VTy.lolli, VTy.inFrag, CTy.inFrag, h]

theorem liveWithin_ctx791 : ∀ cs : List Const791, Ctx.LiveWithin (ctx791 cs) (vals791 cs)
  | [] => trivial
  | _ :: cs => liveWithin_ctx791 cs

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
