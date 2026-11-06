import Core.Chain.Hardest791N
import Core.Chain.SI.TabLeN
import Core.Chain.SI.StopRaiseN
import Core.Chain.SI.LocTy

/-!
# #791 at the rule level over the chain relation: the interpretation and the statements
`[spec §62]`

`docs/new-core/chain-interpretation.md` is the design: the world, the interpretation, the
departures from Core. `Core/TreeGoal791.lean` states #791's end goal over the tree relation; here the
interpretation and the statements are restated over Core's step-indexed chain relation `erwp`
(`Core/Chain/SI/*`), at the per-lend world `LocTy` (`Core/Chain/SI/LocTy.lean`).

* **§1. The interpretation.** `vN A δ Θ k v ρ` (`𝒱⟦A⟧δ` at the world `Θ` and the index `k`) and
  `cN C δ Θ c k ls e ρ` (`𝒞⟦C⟧δ` at the world `Θ`, the run's live lifetimes `c`, the index `k`
  and the record list `ls`). Every run is `erwp` at the view `Θ.view c`, the relation's `LocFam`.
  `F_Σ R` is read at the table of the row's layers (`tabN`, each capturable entry with its cancel
  row's obligation `finN`) and its answer `retN`. Core's `vCE`/`cC`/`effTab`/`finObl`/`effRet`
  clause by clause, with `ewpTS`/`wpTS` replaced by `erwp`:
  - `Mut` is Core's `ptoMutS` shape over the world: the cell at some `b ⊒ @aδ` (`mutL b`) holds a
    member of the payload read at the world above `b`, the family the world stores at the lend's
    key, and every value of the payload is in `Res_b`;
  - `U C` is Kripke along Core's resource-relative order (`LocTy.ExtR` at the thunk's
    resource), at every view consistent with the resource (`ConsistentX`); `⊸` is Core's plain
    wand at the same world, step-indexed (every later index) and at every view consistent with
    the composite.
  - `Imm` is Core's `ptoImmS` shape over the world: one `imm` cell, its payload in the
    observable view `vO` (Core's `vCE false`), its location witnessed in the world's `imm`
    records (`ImmWitW`, Core's `CohE`); the relation's entry tie (`ImmTieL`) puts the witness's
    record on the run's list.
  `gN`, `SemJN`.
* **§2. Laws.** Downward closure of every piece; `vN`/`cN` read `δ` only at free variables
  (`vN_congr`); values stable along the resource-relative order (`vN_extR`), hence along the
  world-relative `ExtA` (`vN_extA`), computations too except at an effect row (`cN_extA`); values in
  a lend's stratum do not read the lend (`vN_local`); `𝒱⟦A⟧` of an outliving `A` in the stratum
  (`vN_outlives`); `F_Σ R` as `erwp` at the row's table (`cN_effOf`).
* **§3. The statements**: `ConstN`, `ConstsN`, `FundamentalN`, `BridgeN`, `Goal791SchedN`, and
  `goal791Sched_of`: `Goal791SchedN` from `FundamentalN` and `ConstsN`.
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

/-- **A candidate for `νX. C`** at a fixed `δ`: `cN`'s signature with `δ` applied (Core's
`CPred`, with the world, the view and the index). -/
abbrev CandN := LocTy → (Loc → Option Life) → Nat → List SRec → Expr → WRes → Prop

/-- `R ⊆ R′` pointwise. -/
def CandN.Le (R R' : CandN) : Prop :=
  ∀ Θ c n ls e ρ, R Θ c n ls e ρ → R' Θ c n ls e ρ

/-- **`U X` at the candidate `R`** (Core's `thunkR`): `vN`'s `U` clause with `R` in place of
`𝒞⟦νX. C⟧`, at every extension of the world along `ExtR` at the thunk's resource, every view
consistent with it and every record list. -/
def thunkRN (R : CandN) : LocTy → Nat → Val → WRes → Prop := fun Θ n v ρ =>
  ∀ Θ' : LocTy, Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ → ∀ ls, R Θ' c n ls v.1 ρ

mutual
/-- **`𝒱⟦A⟧δ` at the world and the index.** Core's `vCE` clause by clause, `⋆` written as
`ResU.CompS`; `Mut` is Core's `ptoMutS` shape over the world (`Core/Relation.lean`): a lifetime
`b` with `@aδ ⊑ b` (Core's slack, which `mutSub` reads), a location whose cell at `b` holds the
member `j ≥ k` of the payload read at the world above `b`, which the world stores at the lend's
key `(ℓ, b)` (`mutL`), and every value of `A` in the stratum `b` (`ptoMutS`'s last conjunct,
`hunif`); `Imm` one `imm` cell longer-lived than `@aδ` with its payload in the observable view
`vO` (Core's `ptoImmS` at `vCE false`), witnessed in the world's `imm` records at a type `TyEq` to
`A` (`ImmWitW`, Core's `CohE`); `[@a] A` in
the stratum; `U C` the forced thunk in `𝒞⟦C⟧` at every extension of the world along `ExtR` at the
thunk's resource (Core's `vCE` at `U`), every view consistent with that resource and every record
list; `opq k` Core's `k.rel` (at `Tok` a location owning a unit cell); `[L]` Core's family: a
value `arr(ℓ, c)` with `c < 2³¹` whose leaves `loc (ℓ + i)`, `i < c`, are values of `L` over a
separation of the resource (`sepRange`). A lifetime with no interpretation reads as empty. Type
variables and `μ` are outside the fragment and empty. -/
def vN : VTy → LSub → LocTy → Nat → Val → WRes → Prop
  | .unit, _, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | .tensor A B, δ, Θ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      vN A δ Θ n v₁ ρ₁ ∧ vN B δ Θ n v₂ ρ₂
  | .zero, _, _, _, _, _ => False
  | .sum A B, δ, Θ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ vN A δ Θ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ vN B δ Θ n v₂ ρ)
  | .thunk C, δ, Θ, n, v, ρ => ∀ Θ' : LocTy, Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ →
      ∀ ls, cN C δ Θ' c n ls (forceE C v.1) ρ
  | .ref A, δ, Θ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ vN A δ Θ n u σ
  | .imm a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => vO A δ Θ n u σ) v ρ ∧
        ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s A δ
  | .mut a A, δ, Θ, n, v, ρ => ∃ α : Life, a.interp δ = some α ∧ ∃ b : Life, α ≤ b ∧
      mutL b (fun Θ' j u r => vN A δ Θ' j u r) Θ n v ρ ∧
        ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN A δ Θ' j u r → r.InStratum b
  | .box a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧ vN A δ Θ n v ρ ∧ ρ.InStratum α
  | .bang A, δ, Θ, n, v, ρ => ρ = PMap.empty ∧ vN A δ Θ n v ρ
  | .unk, _, _, _, _, ρ => ρ = PMap.empty
  | .int w, _, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | .tvar _, _, _, _, _, _ => False
  | .mu _, _, _, _, _, _ => False
  | .fam L, δ, Θ, n, v, ρ => ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vN L δ Θ n (Val.loc m)) l c.toNat ρ
  | .opq k, _, _, _, v, ρ => k.rel v ρ
  termination_by structural x => x
/-- **`𝒱⟦A⟧δ` in the observable view an `imm` payload is held at** (Core's `vCE false`): `vN`'s
clauses with `U C` read as `True`, `!A` and `Mut`'s stored family read at `vN`. -/
def vO : VTy → LSub → LocTy → Nat → Val → WRes → Prop
  | .unit, _, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | .tensor A B, δ, Θ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      vO A δ Θ n v₁ ρ₁ ∧ vO B δ Θ n v₂ ρ₂
  | .zero, _, _, _, _, _ => False
  | .sum A B, δ, Θ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ vO A δ Θ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ vO B δ Θ n v₂ ρ)
  | .thunk _, _, _, _, _, _ => True
  | .ref A, δ, Θ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ vO A δ Θ n u σ
  | .imm a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => vO A δ Θ n u σ) v ρ ∧
        ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s A δ
  | .mut a A, δ, Θ, n, v, ρ => ∃ α : Life, a.interp δ = some α ∧ ∃ b : Life, α ≤ b ∧
      mutL b (fun Θ' j u r => vN A δ Θ' j u r) Θ n v ρ ∧
        ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN A δ Θ' j u r → r.InStratum b
  | .box a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧ vO A δ Θ n v ρ ∧ ρ.InStratum α
  | .bang A, δ, Θ, n, v, ρ => ρ = PMap.empty ∧ vN A δ Θ n v ρ
  | .unk, _, _, _, _, ρ => ρ = PMap.empty
  | .int w, _, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | .tvar _, _, _, _, _, _ => False
  | .mu _, _, _, _, _, _ => False
  | .fam L, δ, Θ, n, v, ρ => ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vO L δ Θ n (Val.loc m)) l c.toNat ρ
  | .opq k, _, _, _, v, ρ => k.rel v ρ
  termination_by structural x => x
/-- **`𝒱⟦A⟧δ` with one type variable** (Core's `vCE η` at an environment with one entry): `vN`'s
clauses, the variable `X` (index `0`) read at `P`, every other variable empty, and the `Imm`
witness read at the closed type `A[S/X]` (Core's `tClose`). -/
def vNX (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    VTy → LSub → LocTy → Nat → Val → WRes → Prop
  | .unit, _, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | .tensor A B, δ, Θ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      vNX S P A δ Θ n v₁ ρ₁ ∧ vNX S P B δ Θ n v₂ ρ₂
  | .zero, _, _, _, _, _ => False
  | .sum A B, δ, Θ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ vNX S P A δ Θ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ vNX S P B δ Θ n v₂ ρ)
  | .thunk C, δ, Θ, n, v, ρ => ∀ Θ' : LocTy, Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ →
      ∀ ls, cN C δ Θ' c n ls (forceE C v.1) ρ
  | .ref A, δ, Θ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ vNX S P A δ Θ n u σ
  | .imm a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => vOX S P A δ Θ n u σ) v ρ ∧
        ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s (VTy.inst S A) δ
  | .mut a A, δ, Θ, n, v, ρ => ∃ α : Life, a.interp δ = some α ∧ ∃ b : Life, α ≤ b ∧
      mutL b (fun Θ' j u r => vNX S P A δ Θ' j u r) Θ n v ρ ∧
        ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vNX S P A δ Θ' j u r → r.InStratum b
  | .box a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧ vNX S P A δ Θ n v ρ ∧ ρ.InStratum α
  | .bang A, δ, Θ, n, v, ρ => ρ = PMap.empty ∧ vNX S P A δ Θ n v ρ
  | .unk, _, _, _, _, ρ => ρ = PMap.empty
  | .int w, _, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | .tvar 0, _, Θ, n, v, ρ => P Θ n v ρ
  | .tvar (_ + 1), _, _, _, _, _ => False
  | .mu _, _, _, _, _, _ => False
  | .fam L, δ, Θ, n, v, ρ => ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vNX S P L δ Θ n (Val.loc m)) l c.toNat ρ
  | .opq k, _, _, _, v, ρ => k.rel v ρ
  termination_by structural x => x
/-- **The observable view with one type variable** (Core's `vCE η false`): `vO`'s clauses, `X`
read as `True` (Core's `nuP false`). -/
def vOX (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    VTy → LSub → LocTy → Nat → Val → WRes → Prop
  | .unit, _, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | .tensor A B, δ, Θ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      vOX S P A δ Θ n v₁ ρ₁ ∧ vOX S P B δ Θ n v₂ ρ₂
  | .zero, _, _, _, _, _ => False
  | .sum A B, δ, Θ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ vOX S P A δ Θ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ vOX S P B δ Θ n v₂ ρ)
  | .thunk _, _, _, _, _, _ => True
  | .ref A, δ, Θ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ vOX S P A δ Θ n u σ
  | .imm a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => vOX S P A δ Θ n u σ) v ρ ∧
        ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s (VTy.inst S A) δ
  | .mut a A, δ, Θ, n, v, ρ => ∃ α : Life, a.interp δ = some α ∧ ∃ b : Life, α ≤ b ∧
      mutL b (fun Θ' j u r => vNX S P A δ Θ' j u r) Θ n v ρ ∧
        ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vNX S P A δ Θ' j u r → r.InStratum b
  | .box a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧ vOX S P A δ Θ n v ρ ∧ ρ.InStratum α
  | .bang A, δ, Θ, n, v, ρ => ρ = PMap.empty ∧ vNX S P A δ Θ n v ρ
  | .unk, _, _, _, _, ρ => ρ = PMap.empty
  | .int w, _, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | .tvar 0, _, _, _, _, _ => True
  | .tvar (_ + 1), _, _, _, _, _ => False
  | .mu _, _, _, _, _, _ => False
  | .fam L, δ, Θ, n, v, ρ => ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vOX S P L δ Θ n (Val.loc m)) l c.toNat ρ
  | .opq k, _, _, _, v, ρ => k.rel v ρ
  termination_by structural x => x
/-- **`𝒞⟦C⟧δ` at the world, the run's live lifetimes, the index and the record list.** Every
run is `erwp` at the view `Θ.view c`. `F A` is `erwp` at the empty table; `F_Σ R` is `erwp` at the
table of the row's layers; `⊸` is Core's plain wand at the same world, read at every view
consistent with the argument's and the function's resource and every later index (the
step-indexed `−∗`); `∀'x ⊏ @c` every `α ⊏ @cδ` (Core's `cC`: vacuous where `@c` has no
interpretation; a constant's premises carry its bound's definedness, `Const791.OK`); `ν` is outside
the fragment. -/
def cN : CTy → LSub → LocTy → (Loc → Option Life) → Nat → List SRec → Expr → WRes → Prop
  | .ret A, δ, Θ, c, n, ls, e, ρ =>
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (fun k _ v ρ => vN A δ Θ k v ρ) n ls e ρ
  | .arr A C, δ, Θ, _, n, ls, e, ρ => ∀ c',
      ∀ k, k ≤ n → ∀ (v : Val) (ρv ρ' : WRes), ResU.CompS ρ ρv ρ' → vN A δ Θ k v ρv →
        ConsistentX c' ρ' → cN C δ Θ c' k ls (.app e (.val v)) ρ'
  | .amp C D, δ, Θ, c, n, ls, e, ρ => cN C δ Θ c n ls (.app e (.val (Val.inj₁ .unit))) ρ ∧
      cN D δ Θ c n ls (.app e (.val (Val.inj₂ .unit))) ρ
  | .top, _, _, _, _, _, _, _ => True
  | .all x c' C, δ, Θ, c, n, ls, e, ρ =>
      ∀ α, LtLife δ c' α → cN C (δ.extend x α) Θ c n ls (.app e (.val .unit)) ρ
  | .nu C, δ, Θ, c, n, ls, e, ρ => C.NuShape →
      ∃ R : CandN, R.Le (cBN (.thunk (.nu C)) R C δ) ∧ R Θ c n ls e ρ
  | .eff m i q A B fin _ C, δ, Θ, c, n, ls, e, ρ =>
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (extTabN m i
          (entN q B (fun k v ρ => vN A δ Θ k v ρ) (fun k v ρ => vN B δ Θ k v ρ) (finN fin δ Θ c))
          (tabN C δ Θ c)))
        (fun k _ v ρ => retN C δ Θ k v ρ) n ls e ρ
  termination_by structural x => x
/-- **One unfolding of an observation tree at the candidate `R`** (Core's `cB`): `cN`'s `F`, `&`,
`F_Σ`, `⊸` and `∀` clauses, each leaf's answer read by `vNX S (thunkRN R)`; a row's operation
types and an observation's argument are closed and read by `vN`. Other formers are not
observation trees and hold trivially. -/
def cBN (S : VTy) (R : CandN) : CTy → LSub → CandN
  | .ret A, δ, Θ, c, n, ls, e, ρ =>
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
        (fun k _ v ρ => vNX S (thunkRN R) A δ Θ k v ρ) n ls e ρ
  | .amp C D, δ, Θ, c, n, ls, e, ρ => cBN S R C δ Θ c n ls (.app e (.val (Val.inj₁ .unit))) ρ ∧
      cBN S R D δ Θ c n ls (.app e (.val (Val.inj₂ .unit))) ρ
  | .eff m i q A B fin _ C, δ, Θ, c, n, ls, e, ρ =>
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (extTabN m i
          (entN q B (fun k v ρ => vN A δ Θ k v ρ) (fun k v ρ => vN B δ Θ k v ρ) (finN fin δ Θ c))
          (tabN C δ Θ c)))
        (fun k _ v ρ => retNX S (thunkRN R) C δ Θ k v ρ) n ls e ρ
  | .arr A D, δ, Θ, _, n, ls, e, ρ => ∀ c',
      ∀ k, k ≤ n → ∀ (v : Val) (ρv ρ' : WRes), ResU.CompS ρ ρv ρ' → vN A δ Θ k v ρv →
        ConsistentX c' ρ' → cBN S R D δ Θ c' k ls (.app e (.val v)) ρ'
  | .all x c' D, δ, Θ, c, n, ls, e, ρ =>
      ∀ α, LtLife δ c' α → cBN S R D (δ.extend x α) Θ c n ls (.app e (.val .unit)) ρ
  | .top, _, _, _, _, _, _, _ => True
  | .nu _, _, _, _, _, _, _, _ => True
  termination_by structural x => x
/-- The answer of a row's layers with one type variable (Core's `effRetE`). -/
def retNX (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    CTy → LSub → LocTy → Nat → Val → WRes → Prop
  | .ret A, δ, Θ, k, v, ρ => vNX S P A δ Θ k v ρ
  | .eff _ _ _ _ _ _ _ C, δ, Θ, k, v, ρ => retNX S P C δ Θ k v ρ
  | .arr _ _, _, _, _, _, _ => False
  | .amp _ _, _, _, _, _, _ => False
  | .top, _, _, _, _, _ => False
  | .all _ _ _, _, _, _, _, _ => False
  | .nu _, _, _, _, _, _ => False
  termination_by structural x => x
/-- The table of a row's layers below the top one. -/
def tabN : CTy → LSub → LocTy → (Loc → Option Life) → OpTabN
  | .eff m i q A B fin _ C, δ, Θ, c => extTabN m i
      (entN q B (fun k v ρ => vN A δ Θ k v ρ) (fun k v ρ => vN B δ Θ k v ρ) (finN fin δ Θ c))
      (tabN C δ Θ c)
  | _, _, _, _ => OpTabN.empty
  termination_by structural x => x
/-- **The cancel obligation of a cancel row**: `none` at `⊤`; otherwise the cancel run at the
table of the row's layers, read at the view. -/
def finN : CTy → LSub → LocTy → (Loc → Option Life) →
    Option (Nat → List SRec → Expr → WProp)
  | .top, _, _, _ => none
  | .eff m i q A B fin _ C, δ, Θ, c => some (cancelOblN (ℍ := ℍ) (Θ.view c) (extTabN m i
      (entN q B (fun k v ρ => vN A δ Θ k v ρ) (fun k v ρ => vN B δ Θ k v ρ) (finN fin δ Θ c))
      (tabN C δ Θ c)))
  | .ret _, _, Θ, c => some (cancelOblN (ℍ := ℍ) (Θ.view c) OpTabN.empty)
  | .arr _ _, _, Θ, c => some (cancelOblN (ℍ := ℍ) (Θ.view c) OpTabN.empty)
  | .amp _ _, _, Θ, c => some (cancelOblN (ℍ := ℍ) (Θ.view c) OpTabN.empty)
  | .all _ _ _, _, Θ, c => some (cancelOblN (ℍ := ℍ) (Θ.view c) OpTabN.empty)
  | .nu _, _, Θ, c => some (cancelOblN (ℍ := ℍ) (Θ.view c) OpTabN.empty)
  termination_by structural x => x
/-- The answer of a row's layers. -/
def retN : CTy → LSub → LocTy → Nat → Val → WRes → Prop
  | .ret A, δ, Θ, k, v, ρ => vN A δ Θ k v ρ
  | .eff _ _ _ _ _ _ _ C, δ, Θ, k, v, ρ => retN C δ Θ k v ρ
  | .arr _ _, _, _, _, _, _ => False
  | .amp _ _, _, _, _, _, _ => False
  | .top, _, _, _, _, _ => False
  | .all _ _ _, _, _, _, _, _ => False
  | .nu _, _, _, _, _, _ => False
  termination_by structural x => x

end

/-- **`𝒢⟦Γ⟧δγ` at the world and the index**: the live slots' values over a split of the
resource. -/
def gN (δ : LSub) (Θ : LocTy) : Ctx VTy → List Val → Nat → WRes → Prop
  | [], _, _, ρ => ρ = PMap.empty
  | _ :: _, [], _, ρ => ρ = PMap.empty
  | s :: Γ, v :: γ, n, ρ => if s.live then
      ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vN (ℍ := ℍ) s.ty δ Θ n v ρ₁ ∧ gN δ Θ Γ γ n ρ₂
    else gN δ Θ Γ γ n ρ

/-- **`Δ; Γ ⊨ e : j` over `erwp`**: at every `δ ⊨ Δ`, every world, every view consistent with the
resource, index and record list, from every resource meeting the context. -/
def SemJN (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  ∀ (δ : LSub) (γ : List Val) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ls : List SRec)
    (ρ : WRes), Δ.Models δ → Θ.OK → ConsistentX c ρ → Ctx.LiveWithin Γ γ →
      gN (ℍ := ℍ) δ Θ Γ γ n ρ → cN (ℍ := ℍ) (jdgC j) δ Θ c n ls (substAll γ e) ρ

/-- **The table a task at the row `S` runs at**, at the world `Θ` and the view `c`. -/
def rowTabN (S : Row) (Θ : LocTy) (c : Loc → Option Life) : OpTabN :=
  tabN (ℍ := ℍ) (CTy.effOf S .unit) LSub.empty Θ c

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

mutual
/-- **`vNX` does not read `X`'s entry at a type `X` does not occur in** (Core's
`vCE_congr_occ` at index `0`): neither the candidate nor the closed type. -/
theorem vNX_occ (S S' : VTy) (P P' : LocTy → Nat → Val → WRes → Prop) :
    ∀ (A : VTy), ¬ A.Occ 0 → vNX (ℍ := ℍ) S P A = vNX (ℍ := ℍ) S' P' A
  | .unit, _ => rfl
  | .zero, _ => rfl
  | .unk, _ => rfl
  | .int _, _ => rfl
  | .opq _, _ => rfl
  | .thunk _, _ => rfl
  | .mu _, _ => rfl
  | .tvar 0, h => absurd rfl h
  | .tvar (_ + 1), _ => rfl
  | .tensor A B, h => by
      have h₁ := vNX_occ S S' P P' A (fun h' => h (.inl h'))
      have h₂ := vNX_occ S S' P P' B (fun h' => h (.inr h'))
      funext δ Θ n v ρ; simp only [vNX, h₁, h₂]
  | .sum A B, h => by
      have h₁ := vNX_occ S S' P P' A (fun h' => h (.inl h'))
      have h₂ := vNX_occ S S' P P' B (fun h' => h (.inr h'))
      funext δ Θ n v ρ; simp only [vNX, h₁, h₂]
  | .ref A, h => by
      have h₁ := vNX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vNX, h₁]
  | .box _ A, h => by
      have h₁ := vNX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vNX, h₁]
  | .bang A, h => by
      have h₁ := vNX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vNX, h₁]
  | .fam A, h => by
      have h₁ := vNX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vNX, h₁]
  | .mut _ A, h => by
      have h₁ := vNX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vNX, h₁]
  | .imm _ A, h => by
      have h₁ := vOX_occ S S' P P' A h
      have hi : VTy.inst S A = VTy.inst S' A := VTy.subst_congr_occ A fun k hk => by
        cases k with
        | zero => exact absurd hk h
        | succ k => rfl
      funext δ Θ n v ρ; simp only [vNX, h₁, hi]
theorem vOX_occ (S S' : VTy) (P P' : LocTy → Nat → Val → WRes → Prop) :
    ∀ (A : VTy), ¬ A.Occ 0 → vOX (ℍ := ℍ) S P A = vOX (ℍ := ℍ) S' P' A
  | .unit, _ => rfl
  | .zero, _ => rfl
  | .unk, _ => rfl
  | .int _, _ => rfl
  | .opq _, _ => rfl
  | .thunk _, _ => rfl
  | .mu _, _ => rfl
  | .tvar 0, h => absurd rfl h
  | .tvar (_ + 1), _ => rfl
  | .tensor A B, h => by
      have h₁ := vOX_occ S S' P P' A (fun h' => h (.inl h'))
      have h₂ := vOX_occ S S' P P' B (fun h' => h (.inr h'))
      funext δ Θ n v ρ; simp only [vOX, h₁, h₂]
  | .sum A B, h => by
      have h₁ := vOX_occ S S' P P' A (fun h' => h (.inl h'))
      have h₂ := vOX_occ S S' P P' B (fun h' => h (.inr h'))
      funext δ Θ n v ρ; simp only [vOX, h₁, h₂]
  | .ref A, h => by
      have h₁ := vOX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vOX, h₁]
  | .box _ A, h => by
      have h₁ := vOX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vOX, h₁]
  | .bang A, h => by
      have h₁ := vNX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vOX, h₁]
  | .fam A, h => by
      have h₁ := vOX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vOX, h₁]
  | .mut _ A, h => by
      have h₁ := vNX_occ S S' P P' A h
      funext δ Θ n v ρ; simp only [vOX, h₁]
  | .imm _ A, h => by
      have h₁ := vOX_occ S S' P P' A h
      have hi : VTy.inst S A = VTy.inst S' A := VTy.subst_congr_occ A fun k hk => by
        cases k with
        | zero => exact absurd hk h
        | succ k => rfl
      funext δ Θ n v ρ; simp only [vOX, h₁, hi]
end

/-- **`vNX` is monotone in the candidate at a polynomial type** (Core's `vCE_mono_at` at
`VTy.noMut_of_poly`): `X` occurs only under `⊗`, `⊕` and `[@a]`. -/
theorem vNX_mono {S : VTy} {P P' : LocTy → Nat → Val → WRes → Prop}
    (hP : ∀ Θ n v ρ, P Θ n v ρ → P' Θ n v ρ) :
    ∀ {A : VTy}, A.Poly → ∀ δ Θ n v ρ, vNX (ℍ := ℍ) S P A δ Θ n v ρ →
      vNX (ℍ := ℍ) S P' A δ Θ n v ρ
  | .tensor A B, h, δ, Θ, n, _, _, ⟨v₁, v₂, ρ₁, ρ₂, e, hc, h₁, h₂⟩ =>
      ⟨v₁, v₂, ρ₁, ρ₂, e, hc, vNX_mono hP h.1 δ Θ n v₁ ρ₁ h₁, vNX_mono hP h.2 δ Θ n v₂ ρ₂ h₂⟩
  | .sum A B, h, δ, Θ, n, _, ρ, hv => by
      rcases hv with ⟨v₁, e, h₁⟩ | ⟨v₂, e, h₂⟩
      · exact .inl ⟨v₁, e, vNX_mono hP h.1 δ Θ n v₁ ρ h₁⟩
      · exact .inr ⟨v₂, e, vNX_mono hP h.2 δ Θ n v₂ ρ h₂⟩
  | .box _ A, h, δ, Θ, n, v, ρ, ⟨α, hα, h₁, h₂⟩ => ⟨α, hα, vNX_mono hP (A := A) h δ Θ n v ρ h₁, h₂⟩
  | .tvar 0, _, _, Θ, n, v, ρ, hv => hP Θ n v ρ hv
  | .tvar (_ + 1), _, _, _, _, _, _, hv => hv
  | .unit, h, _, _, _, _, _, hv | .zero, h, _, _, _, _, _, hv | .unk, h, _, _, _, _, _, hv
  | .int _, h, _, _, _, _, _, hv | .opq _, h, _, _, _, _, _, hv | .thunk _, h, _, _, _, _, _, hv
  | .mu _, h, _, _, _, _, _, hv | .ref _, h, _, _, _, _, _, hv | .imm _ _, h, _, _, _, _, _, hv
  | .mut _ _, h, _, _, _, _, _, hv | .bang _, h, _, _, _, _, _, hv | .fam _, h, _, _, _, _, _, hv => by
      rwa [← vNX_occ S S P P' _ h]

/-- The answer of an effectful observation is monotone in the candidate (Core's `effRetE_mono`). -/
theorem retNX_mono {S : VTy} {P P' : LocTy → Nat → Val → WRes → Prop}
    (hP : ∀ Θ n v ρ, P Θ n v ρ → P' Θ n v ρ) :
    ∀ {D : CTy}, D.EffLeaf → ∀ δ Θ n v ρ, retNX (ℍ := ℍ) S P D δ Θ n v ρ →
      retNX (ℍ := ℍ) S P' D δ Θ n v ρ
  | .ret _, h, δ, Θ, n, v, ρ, hv => vNX_mono hP h δ Θ n v ρ hv
  | .eff _ _ _ _ _ _ _ D, h, δ, Θ, n, v, ρ, hv => retNX_mono hP (D := D) h.2.2 δ Θ n v ρ hv

/-- **One unfolding of an observation tree is monotone in the candidate** (Core's `cB_mono`). -/
theorem cBN_mono {S : VTy} {R R' : CandN} (hR : R.LeOK R') :
    ∀ {D : CTy}, D.NuLeaf → ∀ δ, (cBN (ℍ := ℍ) S R D δ).Le (cBN (ℍ := ℍ) S R' D δ)
  | .ret _, hA, δ, Θ, _, n, ls, e, ρ, h =>
      erwp_mono (fun k _ v ρ h => vNX_mono (thunkRN_mono hR) hA δ Θ k v ρ h) (opTableN_local _)
        n ls e ρ h
  | .amp _ _, hD, δ, Θ, c, n, ls, _, ρ, h =>
      ⟨cBN_mono hR hD.1 δ Θ c n ls _ ρ h.1, cBN_mono hR hD.2 δ Θ c n ls _ ρ h.2⟩
  | .eff _ _ _ _ _ _ _ D, hD, δ, Θ, _, n, ls, e, ρ, h =>
      erwp_mono (fun k _ v ρ h => retNX_mono (thunkRN_mono hR) (D := D) hD.2.2 δ Θ k v ρ h)
        (opTableN_local _) n ls e ρ h
  | .arr _ D, hD, δ, Θ, _, _, ls, _, _, h => fun c' k hk v ρv ρ' hc hv hcon =>
      cBN_mono hR (D := D) hD.2 δ Θ c' k ls _ ρ' (h c' k hk v ρv ρ' hc hv hcon)
  | .all x _ D, hD, δ, Θ, c, n, ls, _, ρ, h => fun α hα =>
      cBN_mono hR (D := D) hD (δ.extend x α) Θ c n ls _ ρ (h α hα)
  | .top, hD, _, _, _, _, _, _, _, _ | .nu _, hD, _, _, _, _, _, _, _, _ => hD.elim

/-- **At a polynomial type `vNX` does not read `X`'s closed type** (Core's `cB_poly_ty` at a
leaf): `X` occurs only under `⊗`, `⊕` and `[@a]`, and the `Imm` witness reads the closed type only
where `X` does not occur. -/
theorem vNX_poly_ty (S S' : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    ∀ {A : VTy}, A.Poly → vNX (ℍ := ℍ) S P A = vNX (ℍ := ℍ) S' P A
  | .tensor A B, h => by
      have h₁ := vNX_poly_ty S S' P (A := A) h.1
      have h₂ := vNX_poly_ty S S' P (A := B) h.2
      funext δ Θ n v ρ; simp only [vNX, h₁, h₂]
  | .sum A B, h => by
      have h₁ := vNX_poly_ty S S' P (A := A) h.1
      have h₂ := vNX_poly_ty S S' P (A := B) h.2
      funext δ Θ n v ρ; simp only [vNX, h₁, h₂]
  | .box _ A, h => by
      have h₁ := vNX_poly_ty S S' P (A := A) h
      funext δ Θ n v ρ; simp only [vNX, h₁]
  | .tvar 0, _ => rfl
  | .tvar (_ + 1), _ => rfl
  | .unit, h | .zero, h | .unk, h | .int _, h | .opq _, h | .thunk _, h | .mu _, h | .ref _, h
  | .imm _ _, h | .mut _ _, h | .bang _, h | .fam _, h => vNX_occ S S' P P _ h

theorem retNX_poly_ty (S S' : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    ∀ {D : CTy}, D.EffLeaf → retNX (ℍ := ℍ) S P D = retNX (ℍ := ℍ) S' P D
  | .ret A, h => by
      have h₁ := vNX_poly_ty S S' P (A := A) h
      funext δ Θ n v ρ; simp only [retNX, h₁]
  | .eff _ _ _ _ _ _ _ D, h => by
      have h₁ := retNX_poly_ty S S' P (D := D) h.2.2
      funext δ Θ n v ρ; simp only [retNX, h₁]

/-- **One unfolding of an observation tree does not read `X`'s closed type** (Core's
`cB_poly_ty`). -/
theorem cBN_poly_ty (S S' : VTy) (R : CandN) :
    ∀ {D : CTy}, D.NuLeaf → cBN (ℍ := ℍ) S R D = cBN (ℍ := ℍ) S' R D
  | .ret A, h => by
      have h₁ := vNX_poly_ty S S' (thunkRN R) (A := A) h
      funext δ Θ c n ls e ρ; simp only [cBN, h₁]
  | .amp C D, h => by
      have h₁ := cBN_poly_ty S S' R (D := C) h.1
      have h₂ := cBN_poly_ty S S' R (D := D) h.2
      funext δ Θ c n ls e ρ; simp only [cBN, h₁, h₂]
  | .eff _ _ _ _ _ _ _ D, h => by
      have h₁ := retNX_poly_ty S S' (thunkRN R) (D := D) h.2.2
      funext δ Θ c n ls e ρ; simp only [cBN, h₁]
  | .arr _ D, h => by
      have h₁ := cBN_poly_ty S S' R (D := D) h.2
      funext δ Θ c n ls e ρ; simp only [cBN, h₁]
  | .all _ _ D, h => by
      have h₁ := cBN_poly_ty S S' R (D := D) h
      funext δ Θ c n ls e ρ; simp only [cBN, h₁]
  | .top, h | .nu _, h => h.elim

mutual
theorem vN_down : ∀ (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    vN (ℍ := ℍ) A δ Θ (n + 1) v ρ → vN (ℍ := ℍ) A δ Θ n v ρ
  | .unit, _, _, _, _, _, h => h
  | .tensor A B, δ, Θ, n, _, _, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vN_down A δ Θ n v₁ ρ₁ h₃, vN_down B δ Θ n v₂ ρ₂ h₄⟩
  | .zero, _, _, _, _, _, h => h
  | .sum A B, δ, Θ, n, _, ρ, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vN_down A δ Θ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, vN_down B δ Θ n v₂ ρ h₂⟩
  | .thunk C, δ, Θ, n, v, ρ, h => fun Θ' hE hOK c hc ls =>
      cN_down C δ Θ' hOK.1 c n ls _ ρ (h Θ' hE hOK c hc ls)
  | .ref A, δ, Θ, n, _, _, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vN_down A δ Θ n u σ h₃⟩
  | .imm a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
      exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, vO_down A δ Θ n u σ h₄⟩, hw⟩
  | .mut a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩, hu⟩ := h
      exact ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩, hu⟩
  | .box a A, δ, Θ, n, v, ρ, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vN_down A δ Θ n v ρ h₁, h₂⟩
  | .bang A, δ, Θ, n, v, ρ, h => ⟨h.1, vN_down A δ Θ n v ρ h.2⟩
  | .unk, _, _, _, _, _, h => h
  | .int _, _, _, _, _, _, h => h
  | .tvar _, _, _, _, _, _, h => h
  | .mu _, _, _, _, _, _, h => h
  | .fam L, δ, Θ, n, _, _, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono' (fun m σ hm => vN_down L δ Θ n (Val.loc m) σ hm) h₃⟩
  | .opq _, _, _, _, _, _, h => h
  termination_by structural x => x
theorem vO_down : ∀ (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    vO (ℍ := ℍ) A δ Θ (n + 1) v ρ → vO (ℍ := ℍ) A δ Θ n v ρ
  | .unit, _, _, _, _, _, h => h
  | .tensor A B, δ, Θ, n, _, _, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vO_down A δ Θ n v₁ ρ₁ h₃, vO_down B δ Θ n v₂ ρ₂ h₄⟩
  | .zero, _, _, _, _, _, h => h
  | .sum A B, δ, Θ, n, _, ρ, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vO_down A δ Θ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, vO_down B δ Θ n v₂ ρ h₂⟩
  | .thunk _, _, _, _, _, _, _ => trivial
  | .ref A, δ, Θ, n, _, _, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vO_down A δ Θ n u σ h₃⟩
  | .imm a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
      exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, vO_down A δ Θ n u σ h₄⟩, hw⟩
  | .mut a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩, hu⟩ := h
      exact ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩, hu⟩
  | .box a A, δ, Θ, n, v, ρ, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vO_down A δ Θ n v ρ h₁, h₂⟩
  | .bang A, δ, Θ, n, v, ρ, h => ⟨h.1, vN_down A δ Θ n v ρ h.2⟩
  | .unk, _, _, _, _, _, h => h
  | .int _, _, _, _, _, _, h => h
  | .tvar _, _, _, _, _, _, h => h
  | .mu _, _, _, _, _, _, h => h
  | .fam L, δ, Θ, n, _, _, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono' (fun m σ hm => vO_down L δ Θ n (Val.loc m) σ hm) h₃⟩
  | .opq _, _, _, _, _, _, h => h
  termination_by structural x => x
theorem cN_down : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes),
    cN (ℍ := ℍ) C δ Θ c (n + 1) ls e ρ → cN (ℍ := ℍ) C δ Θ c n ls e ρ
  | .ret A, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      erwp_le (LocTy.view_down hΘ c) (opTableN_local _) (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vN_down A δ Θ k v ρ h) (Nat.le_succ n) h
  | .arr A C, δ, Θ, hΘ, c, n, ls, e, ρ, h => fun c' k hk => h c' k (by omega)
  | .amp C D, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      ⟨cN_down C δ Θ hΘ c n ls _ ρ h.1, cN_down D δ Θ hΘ c n ls _ ρ h.2⟩
  | .top, _, _, _, _, _, _, _, _, h => h
  | .all x c' C, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      fun α hα => cN_down C (δ.extend x α) Θ hΘ c n ls _ ρ (h α hα)
  | .nu C, δ, Θ, hΘ, c, n, ls, e, ρ, h => fun hS => by
      obtain ⟨R, hR, hr⟩ := h hS
      refine ⟨fun Θ c k ls e ρ => Θ.Down ∧ ∃ m, k ≤ m ∧ R Θ c m ls e ρ, ?_,
        hΘ, n + 1, Nat.le_succ n, hr⟩
      rintro Θ' c' k ls' e' ρ' ⟨hΘ', m, hkm, hm⟩
      exact cBN_le _ _ (fun _ hOK _ _ _ _ _ ⟨hd, m, hkm, hm⟩ => ⟨hd, m, Nat.le_of_succ_le hkm, hm⟩)
        C δ Θ' hΘ' c' k m hkm ls' e' ρ'
        (cBN_mono (fun Θ hOK _ k _ _ _ h => ⟨hOK.1, k, le_rfl, h⟩) hS.nuLeaf δ Θ' c' m ls' e' ρ'
          (hR Θ' c' m ls' e' ρ' hm))
  | .eff m i q A B fin rc C, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      erwp_le (LocTy.view_down hΘ c) (opTableN_local _)
        (opTableN_down (extTabN_down (fun k v ρ h => vN_down A δ Θ k v ρ h)
          (finN_down fin δ Θ hΘ c) (tabN_down C δ Θ hΘ c)))
        (fun k _ v ρ h => retN_down C δ Θ k v ρ h) (Nat.le_succ n) h
  termination_by structural x => x
/-- One unfolding at a candidate downward closed in the index is downward closed. -/
theorem cBN_le (S : VTy) (R : CandN) (hR : R.Down) : ∀ (D : CTy) (δ : LSub) (Θ : LocTy),
    Θ.Down → ∀ (c : Loc → Option Life) (k n : Nat), k ≤ n → ∀ (ls : List SRec) (e : Expr)
    (ρ : WRes), cBN (ℍ := ℍ) S R D δ Θ c n ls e ρ → cBN (ℍ := ℍ) S R D δ Θ c k ls e ρ
  | .ret A, δ, Θ, hΘ, c, k, n, hkn, ls, e, ρ, h =>
      erwp_le (LocTy.view_down hΘ c) (opTableN_local _) (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vNX_down S _ (thunkRN_down hR) A δ Θ k v ρ h) hkn h
  | .arr A D, δ, Θ, hΘ, c, k, n, hkn, ls, e, ρ, h => fun c' k' hk' => h c' k' (le_trans hk' hkn)
  | .amp C D, δ, Θ, hΘ, c, k, n, hkn, ls, e, ρ, h =>
      ⟨cBN_le S R hR C δ Θ hΘ c k n hkn ls _ ρ h.1, cBN_le S R hR D δ Θ hΘ c k n hkn ls _ ρ h.2⟩
  | .top, _, _, _, _, _, _, _, _, _, _, h => h
  | .all x c' D, δ, Θ, hΘ, c, k, n, hkn, ls, e, ρ, h =>
      fun α hα => cBN_le S R hR D (δ.extend x α) Θ hΘ c k n hkn ls _ ρ (h α hα)
  | .nu _, _, _, _, _, _, _, _, _, _, _, h => h
  | .eff m i q A B fin rc D, δ, Θ, hΘ, c, k, n, hkn, ls, e, ρ, h =>
      erwp_le (LocTy.view_down hΘ c) (opTableN_local _)
        (opTableN_down (extTabN_down (fun k v ρ h => vN_down A δ Θ k v ρ h)
          (finN_down fin δ Θ hΘ c) (tabN_down D δ Θ hΘ c)))
        (fun k _ v ρ h => retNX_down S _ (thunkRN_down hR) D δ Θ k v ρ h) hkn h
  termination_by structural x => x
/-- The answer of a row's layers with one type variable is downward closed. -/
theorem retNX_down (S : VTy) (P : LocTy → Nat → Val → WRes → Prop)
    (hP : ∀ Θ n v ρ, P Θ (n + 1) v ρ → P Θ n v ρ) :
    ∀ (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    retNX (ℍ := ℍ) S P C δ Θ (n + 1) v ρ → retNX (ℍ := ℍ) S P C δ Θ n v ρ
  | .ret A, δ, Θ, n, v, ρ, h => vNX_down S P hP A δ Θ n v ρ h
  | .eff _ _ _ _ _ _ _ C, δ, Θ, n, v, ρ, h => retNX_down S P hP C δ Θ n v ρ h
  | .arr _ _, _, _, _, _, _, h => h
  | .amp _ _, _, _, _, _, _, h => h
  | .top, _, _, _, _, _, h => h
  | .all _ _ _, _, _, _, _, _, h => h
  | .nu _, _, _, _, _, _, h => h
  termination_by structural x => x
/-- `vNX` is downward closed at a downward closed candidate. -/
theorem vNX_down (S : VTy) (P : LocTy → Nat → Val → WRes → Prop)
    (hP : ∀ Θ n v ρ, P Θ (n + 1) v ρ → P Θ n v ρ) :
    ∀ (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    vNX (ℍ := ℍ) S P A δ Θ (n + 1) v ρ → vNX (ℍ := ℍ) S P A δ Θ n v ρ
  | .unit, _, _, _, _, _, h => h
  | .tensor A B, δ, Θ, n, _, _, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vNX_down S P hP A δ Θ n v₁ ρ₁ h₃,
        vNX_down S P hP B δ Θ n v₂ ρ₂ h₄⟩
  | .zero, _, _, _, _, _, h => h
  | .sum A B, δ, Θ, n, _, ρ, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vNX_down S P hP A δ Θ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, vNX_down S P hP B δ Θ n v₂ ρ h₂⟩
  | .thunk C, δ, Θ, n, v, ρ, h => fun Θ' hE hOK c hc ls =>
      cN_down C δ Θ' hOK.1 c n ls _ ρ (h Θ' hE hOK c hc ls)
  | .ref A, δ, Θ, n, _, _, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vNX_down S P hP A δ Θ n u σ h₃⟩
  | .imm a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
      exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, vOX_down S P hP A δ Θ n u σ h₄⟩, hw⟩
  | .mut a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩, hu⟩ := h
      exact ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩, hu⟩
  | .box a A, δ, Θ, n, v, ρ, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vNX_down S P hP A δ Θ n v ρ h₁, h₂⟩
  | .bang A, δ, Θ, n, v, ρ, h => ⟨h.1, vNX_down S P hP A δ Θ n v ρ h.2⟩
  | .unk, _, _, _, _, _, h => h
  | .int _, _, _, _, _, _, h => h
  | .tvar 0, _, Θ, n, v, ρ, h => hP Θ n v ρ h
  | .tvar (_ + 1), _, _, _, _, _, h => h
  | .mu _, _, _, _, _, _, h => h
  | .fam L, δ, Θ, n, _, _, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂,
        sepRange_mono' (fun m σ hm => vNX_down S P hP L δ Θ n (Val.loc m) σ hm) h₃⟩
  | .opq _, _, _, _, _, _, h => h
  termination_by structural x => x
/-- `vOX` is downward closed at a downward closed candidate. -/
theorem vOX_down (S : VTy) (P : LocTy → Nat → Val → WRes → Prop)
    (hP : ∀ Θ n v ρ, P Θ (n + 1) v ρ → P Θ n v ρ) :
    ∀ (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    vOX (ℍ := ℍ) S P A δ Θ (n + 1) v ρ → vOX (ℍ := ℍ) S P A δ Θ n v ρ
  | .unit, _, _, _, _, _, h => h
  | .tensor A B, δ, Θ, n, _, _, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vOX_down S P hP A δ Θ n v₁ ρ₁ h₃,
        vOX_down S P hP B δ Θ n v₂ ρ₂ h₄⟩
  | .zero, _, _, _, _, _, h => h
  | .sum A B, δ, Θ, n, _, ρ, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vOX_down S P hP A δ Θ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, vOX_down S P hP B δ Θ n v₂ ρ h₂⟩
  | .thunk _, _, _, _, _, _, _ => trivial
  | .ref A, δ, Θ, n, _, _, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vOX_down S P hP A δ Θ n u σ h₃⟩
  | .imm a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
      exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, vOX_down S P hP A δ Θ n u σ h₄⟩, hw⟩
  | .mut a A, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩, hu⟩ := h
      exact ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩, hu⟩
  | .box a A, δ, Θ, n, v, ρ, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vOX_down S P hP A δ Θ n v ρ h₁, h₂⟩
  | .bang A, δ, Θ, n, v, ρ, h => ⟨h.1, vNX_down S P hP A δ Θ n v ρ h.2⟩
  | .unk, _, _, _, _, _, h => h
  | .int _, _, _, _, _, _, h => h
  | .tvar 0, _, _, _, _, _, h => h
  | .tvar (_ + 1), _, _, _, _, _, h => h
  | .mu _, _, _, _, _, _, h => h
  | .fam L, δ, Θ, n, _, _, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂,
        sepRange_mono' (fun m σ hm => vOX_down S P hP L δ Θ n (Val.loc m) σ hm) h₃⟩
  | .opq _, _, _, _, _, _, h => h
  termination_by structural x => x
theorem tabN_down : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life),
    (tabN (ℍ := ℍ) C δ Θ c).Down
  | .eff m i q A B fin rc C, δ, Θ, hΘ, c =>
      extTabN_down (fun k v ρ h => vN_down A δ Θ k v ρ h) (finN_down fin δ Θ hΘ c)
        (tabN_down C δ Θ hΘ c)
  | .ret _, _, _, _, _ => OpTabN.empty_down
  | .arr _ _, _, _, _, _ => OpTabN.empty_down
  | .amp _ _, _, _, _, _ => OpTabN.empty_down
  | .top, _, _, _, _ => OpTabN.empty_down
  | .all _ _ _, _, _, _, _ => OpTabN.empty_down
  | .nu _, _, _, _, _ => OpTabN.empty_down
  termination_by structural x => x
theorem finN_down : ∀ (F : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life),
    ∀ P, finN (ℍ := ℍ) F δ Θ c = some P → ∀ k ls e ρ, P (k + 1) ls e ρ → P k ls e ρ
  | .top, _, _, _, _, _, h => by cases h
  | .eff m i q A B fin rc C, δ, Θ, hΘ, c, P, h => by
      simp only [finN, Option.some.injEq] at h
      subst h
      exact cancelOblN_down (LocTy.view_down hΘ c)
        (extTabN_down (fun k v ρ h => vN_down A δ Θ k v ρ h)
          (finN_down fin δ Θ hΘ c) (tabN_down C δ Θ hΘ c))
  | .ret _, _, Θ, hΘ, c, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down (LocTy.view_down hΘ c) OpTabN.empty_down
  | .arr _ _, _, Θ, hΘ, c, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down (LocTy.view_down hΘ c) OpTabN.empty_down
  | .amp _ _, _, Θ, hΘ, c, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down (LocTy.view_down hΘ c) OpTabN.empty_down
  | .all _ _ _, _, Θ, hΘ, c, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down (LocTy.view_down hΘ c) OpTabN.empty_down
  | .nu _, _, Θ, hΘ, c, P, h => by
      simp only [finN, Option.some.injEq] at h; subst h
      exact cancelOblN_down (LocTy.view_down hΘ c) OpTabN.empty_down
  termination_by structural x => x
theorem retN_down : ∀ (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    retN (ℍ := ℍ) C δ Θ (n + 1) v ρ → retN (ℍ := ℍ) C δ Θ n v ρ
  | .ret A, δ, Θ, n, v, ρ, h => vN_down A δ Θ n v ρ h
  | .eff _ _ _ _ _ _ _ C, δ, Θ, n, v, ρ, h => retN_down C δ Θ n v ρ h
  | .arr _ _, _, _, _, _, _, h => h
  | .amp _ _, _, _, _, _, _, h => h
  | .top, _, _, _, _, _, h => h
  | .all _ _ _, _, _, _, _, _, h => h
  | .nu _, _, _, _, _, _, h => h
  termination_by structural x => x
end

theorem vN_le {A : VTy} {δ : LSub} {Θ : LocTy} {k n : Nat} (hkn : k ≤ n) {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) A δ Θ n v ρ) : vN (ℍ := ℍ) A δ Θ k v ρ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (vN_down A δ Θ _ v ρ (by rwa [← Nat.add_assoc] at h))

theorem cN_le {C : CTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life} {k n : Nat}
    (hkn : k ≤ n) {ls : List SRec} {e : Expr} {ρ : WRes} (h : cN (ℍ := ℍ) C δ Θ c n ls e ρ) :
    cN (ℍ := ℍ) C δ Θ c k ls e ρ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (cN_down C δ Θ hΘ c _ ls e ρ (by rwa [← Nat.add_assoc] at h))

/-- A `Mut` payload's family, as the world stores it, is downward closed (the anti-frame's
`DownFam` premise, `reseal_at_entry`). -/
theorem vN_fam_down (A : VTy) (δ : LSub) (α : Life) (Θ : LocTy) :
    DownFam α (famL α (fun Θ' j u r => vN (ℍ := ℍ) A δ Θ' j u r) Θ) :=
  fun k u r h => vN_down A δ _ k u r.1 h

/-! ### Rows -/

/-- A row's answer is its base's value type. -/
theorem retN_effOf (S : Row) (R : VTy) (δ : LSub) (Θ : LocTy) :
    retN (ℍ := ℍ) (CTy.effOf S R) δ Θ = vN (ℍ := ℍ) R δ Θ := by
  induction S with
  | nil => funext k v ρ; simp only [CTy.effOf, retN]
  | cons o S ih => funext k v ρ; simp only [CTy.effOf, retN]; rw [ih]

/-- **`F_Σ R` is `erwp` at the view, the row's table and `𝒱⟦R⟧`.** -/
theorem cN_effOf (S : Row) (R : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) (n : Nat)
    (ls : List SRec) (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (CTy.effOf S R) δ Θ c n ls e ρ ↔
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S R) δ Θ c))
        (fun k _ v ρ => vN (ℍ := ℍ) R δ Θ k v ρ) n ls e ρ := by
  cases S with
  | nil => simp only [CTy.effOf, cN, tabN]
  | cons o S =>
      simp only [CTy.effOf, cN, tabN]
      rw [retN_effOf]

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

mutual
theorem vN_congr : ∀ (A : VTy) {δ δ' : LSub}, (∀ y, VFree y A → δ.find? y = δ'.find? y) →
    vN (ℍ := ℍ) A δ = vN (ℍ := ℍ) A δ'
  | .unit, _, _, _ => rfl
  | .tensor A B, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ n v ρ; simp only [vN, h₁, h₂]
  | .zero, _, _, _ => rfl
  | .sum A B, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ n v ρ; simp only [vN, h₁, h₂]
  | .thunk C, δ, δ', h => by
      have h₁ := cN_congr C (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vN, h₁]
  | .ref A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vN, h₁]
  | .imm a A, δ, δ', h => by
      have h₁ := vO_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      have hw := immWitW_congr (A := A) (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ n v ρ; simp only [vN, h₁, ha, hw]
  | .mut a A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vN, ha, h₁]
  | .box a A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vN, h₁, ha]
  | .bang A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vN, h₁]
  | .unk, _, _, _ => rfl
  | .int _, _, _, _ => rfl
  | .tvar _, _, _, _ => rfl
  | .mu _, _, _, _ => rfl
  | .fam L, δ, δ', h => by
      have h₁ := vN_congr L (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vN, h₁]
  | .opq _, _, _, _ => rfl
  termination_by structural x => x
theorem vO_congr : ∀ (A : VTy) {δ δ' : LSub}, (∀ y, VFree y A → δ.find? y = δ'.find? y) →
    vO (ℍ := ℍ) A δ = vO (ℍ := ℍ) A δ'
  | .unit, _, _, _ => rfl
  | .tensor A B, δ, δ', h => by
      have h₁ := vO_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vO_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ n v ρ; simp only [vO, h₁, h₂]
  | .zero, _, _, _ => rfl
  | .sum A B, δ, δ', h => by
      have h₁ := vO_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vO_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ n v ρ; simp only [vO, h₁, h₂]
  | .thunk _, _, _, _ => rfl
  | .ref A, δ, δ', h => by
      have h₁ := vO_congr A (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vO, h₁]
  | .imm a A, δ, δ', h => by
      have h₁ := vO_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      have hw := immWitW_congr (A := A) (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ n v ρ; simp only [vO, h₁, ha, hw]
  | .mut a A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vO, ha, h₁]
  | .box a A, δ, δ', h => by
      have h₁ := vO_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vO, h₁, ha]
  | .bang A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vO, h₁]
  | .unk, _, _, _ => rfl
  | .int _, _, _, _ => rfl
  | .tvar _, _, _, _ => rfl
  | .mu _, _, _, _ => rfl
  | .fam L, δ, δ', h => by
      have h₁ := vO_congr L (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vO, h₁]
  | .opq _, _, _, _ => rfl
  termination_by structural x => x
theorem vNX_congr (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (A : VTy) {δ δ' : LSub},
    (∀ y, VFree y A → δ.find? y = δ'.find? y) → (∀ y, VFree y S → δ.find? y = δ'.find? y) →
    vNX (ℍ := ℍ) S P A δ = vNX (ℍ := ℍ) S P A δ'
  | .unit, _, _, _, _ => rfl
  | .tensor A B, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hS
      have h₂ := vNX_congr S P B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      funext Θ n v ρ; simp only [vNX, h₁, h₂]
  | .zero, _, _, _, _ => rfl
  | .sum A B, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hS
      have h₂ := vNX_congr S P B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      funext Θ n v ρ; simp only [vNX, h₁, h₂]
  | .thunk C, δ, δ', h, hS => by
      have h₁ := cN_congr C (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vNX, h₁]
  | .ref A, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') h hS
      funext Θ n v ρ; simp only [vNX, h₁]
  | .imm a A, δ, δ', h, hS => by
      have h₁ := vOX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      have hw := immWitW_congr (A := VTy.inst S A) (δ := δ) (δ' := δ') (fun y hy =>
        (vFree_inst hy).elim (fun hy => h y (.inr hy)) (hS y))
      funext Θ n v ρ; simp only [vNX, h₁, ha, hw]
  | .mut a A, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vNX, ha, h₁]
  | .box a A, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vNX, h₁, ha]
  | .bang A, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') h hS
      funext Θ n v ρ; simp only [vNX, h₁]
  | .unk, _, _, _, _ => rfl
  | .int _, _, _, _, _ => rfl
  | .tvar 0, _, _, _, _ => rfl
  | .tvar (_ + 1), _, _, _, _ => rfl
  | .mu _, _, _, _, _ => rfl
  | .fam L, δ, δ', h, hS => by
      have h₁ := vNX_congr S P L (δ := δ) (δ' := δ') h hS
      funext Θ n v ρ; simp only [vNX, h₁]
  | .opq _, _, _, _, _ => rfl
  termination_by structural x => x
theorem vOX_congr (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (A : VTy) {δ δ' : LSub},
    (∀ y, VFree y A → δ.find? y = δ'.find? y) → (∀ y, VFree y S → δ.find? y = δ'.find? y) →
    vOX (ℍ := ℍ) S P A δ = vOX (ℍ := ℍ) S P A δ'
  | .unit, _, _, _, _ => rfl
  | .tensor A B, δ, δ', h, hS => by
      have h₁ := vOX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hS
      have h₂ := vOX_congr S P B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      funext Θ n v ρ; simp only [vOX, h₁, h₂]
  | .zero, _, _, _, _ => rfl
  | .sum A B, δ, δ', h, hS => by
      have h₁ := vOX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hS
      have h₂ := vOX_congr S P B (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      funext Θ n v ρ; simp only [vOX, h₁, h₂]
  | .thunk _, _, _, _, _ => rfl
  | .ref A, δ, δ', h, hS => by
      have h₁ := vOX_congr S P A (δ := δ) (δ' := δ') h hS
      funext Θ n v ρ; simp only [vOX, h₁]
  | .imm a A, δ, δ', h, hS => by
      have h₁ := vOX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      have hw := immWitW_congr (A := VTy.inst S A) (δ := δ) (δ' := δ') (fun y hy =>
        (vFree_inst hy).elim (fun hy => h y (.inr hy)) (hS y))
      funext Θ n v ρ; simp only [vOX, h₁, ha, hw]
  | .mut a A, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vOX, ha, h₁]
  | .box a A, δ, δ', h, hS => by
      have h₁ := vOX_congr S P A (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vOX, h₁, ha]
  | .bang A, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') h hS
      funext Θ n v ρ; simp only [vOX, h₁]
  | .unk, _, _, _, _ => rfl
  | .int _, _, _, _, _ => rfl
  | .tvar 0, _, _, _, _ => rfl
  | .tvar (_ + 1), _, _, _, _ => rfl
  | .mu _, _, _, _, _ => rfl
  | .fam L, δ, δ', h, hS => by
      have h₁ := vOX_congr S P L (δ := δ) (δ' := δ') h hS
      funext Θ n v ρ; simp only [vOX, h₁]
  | .opq _, _, _, _, _ => rfl
  termination_by structural x => x
/-- One unfolding of an observation tree reads `δ` only at the free variables of the tree and
of the closed type `S` (Core's `cB_congr`, `EnvAgree` at `S`). -/
theorem cBN_congr (S : VTy) (R : CandN) : ∀ (C : CTy) {δ δ' : LSub},
    (∀ y, CFree y C → δ.find? y = δ'.find? y) → (∀ y, VFree y S → δ.find? y = δ'.find? y) →
    cBN (ℍ := ℍ) S R C δ = cBN (ℍ := ℍ) S R C δ'
  | .ret A, δ, δ', h, hS => by
      have h₁ := vNX_congr S (thunkRN R) A (δ := δ) (δ' := δ') h hS
      funext Θ c n ls e ρ; simp only [cBN, h₁]
  | .arr A D, δ, δ', h, hS => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := cBN_congr S R D (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      funext Θ c n ls e ρ; simp only [cBN, h₁, h₂]
  | .amp C D, δ, δ', h, hS => by
      have h₁ := cBN_congr S R C (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hS
      have h₂ := cBN_congr S R D (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hS
      funext Θ c n ls e ρ; simp only [cBN, h₁, h₂]
  | .top, _, _, _, _ => rfl
  | .all x c D, δ, δ', h, hS => by
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') c (fun y hy => h y (.inl hy))
      have hext : ∀ (α : Life) (y : LifeVar), (∀ y, CFree y D → x ≠ y → δ.find? y = δ'.find? y) →
          ∀ (P : LifeVar → Prop), (∀ y, P y → x ≠ y → δ.find? y = δ'.find? y) → P y →
          (δ.extend x α).find? y = (δ'.extend x α).find? y := by
        intro α y _ P hP hy
        by_cases hxy : x = y
        · subst hxy
          rw [BoCa.Fig16.LogRel.find?_extend_self, BoCa.Fig16.LogRel.find?_extend_self]
        · rw [BoCa.Fig16.LogRel.find?_extend_ne _ _ hxy, BoCa.Fig16.LogRel.find?_extend_ne _ _ hxy]
          exact hP y hy hxy
      have h₁ : ∀ α : Life, cBN (ℍ := ℍ) S R D (δ.extend x α) = cBN (ℍ := ℍ) S R D (δ'.extend x α) :=
        fun α => cBN_congr S R D
          (fun y hy => hext α y (fun y hy hxy => h y (.inr ⟨fun e => hxy e.symm, hy⟩)) _
            (fun y hy hxy => h y (.inr ⟨fun e => hxy e.symm, hy⟩)) hy)
          (fun y hy => hext α y (fun y hy hxy => h y (.inr ⟨fun e => hxy e.symm, hy⟩)) _
            (fun y hy _ => hS y hy) hy)
      have hL : ∀ α : Life, LtLife δ c α = LtLife δ' c α := by
        intro α; unfold LtLife; rw [ha]
      funext Θ c' n ls e ρ; simp only [cBN, h₁, hL]
  | .nu _, _, _, _, _ => rfl
  | .eff m i q A B fin rc C, δ, δ', h, hS => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy)))
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      have h₅ := retNX_congr S (thunkRN R) C (δ := δ) (δ' := δ')
        (fun y hy => h y (.inr (.inr (.inr hy)))) hS
      funext Θ c n ls e ρ; simp only [cBN, h₁, h₂, h₃, h₄, h₅]
  termination_by structural x => x
/-- The answer of a row's layers with one type variable reads `δ` only at free variables. -/
theorem retNX_congr (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) : ∀ (C : CTy) {δ δ' : LSub},
    (∀ y, CFree y C → δ.find? y = δ'.find? y) → (∀ y, VFree y S → δ.find? y = δ'.find? y) →
    retNX (ℍ := ℍ) S P C δ = retNX (ℍ := ℍ) S P C δ'
  | .ret A, δ, δ', h, hS => by
      have h₁ := vNX_congr S P A (δ := δ) (δ' := δ') h hS
      funext Θ n v ρ; simp only [retNX, h₁]
  | .eff _ _ _ _ _ _ _ C, δ, δ', h, hS => by
      have h₁ := retNX_congr S P C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy)))) hS
      funext Θ n v ρ; simp only [retNX, h₁]
  | .arr _ _, _, _, _, _ => rfl
  | .amp _ _, _, _, _, _ => rfl
  | .top, _, _, _, _ => rfl
  | .all _ _ _, _, _, _, _ => rfl
  | .nu _, _, _, _, _ => rfl
  termination_by structural x => x
theorem cN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    cN (ℍ := ℍ) C δ = cN (ℍ := ℍ) C δ'
  | .ret A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext Θ c n ls e ρ; simp only [cN, h₁]
  | .arr A C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := cN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ c n ls e ρ; simp only [cN, h₁, h₂]
  | .amp C D, δ, δ', h => by
      have h₁ := cN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := cN_congr D (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy))
      funext Θ c n ls e ρ; simp only [cN, h₁, h₂]
  | .top, _, _, _ => rfl
  | .all x c C, δ, δ', h => by
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') c (fun y hy => h y (.inl hy))
      have h₁ : ∀ α : Life, cN (ℍ := ℍ) C (δ.extend x α) = cN (ℍ := ℍ) C (δ'.extend x α) := by
        intro α
        refine cN_congr C (fun y hy => ?_)
        by_cases hxy : x = y
        · subst hxy
          rw [BoCa.Fig16.LogRel.find?_extend_self, BoCa.Fig16.LogRel.find?_extend_self]
        · rw [BoCa.Fig16.LogRel.find?_extend_ne _ _ hxy, BoCa.Fig16.LogRel.find?_extend_ne _ _ hxy]
          exact h y (.inr ⟨fun e => hxy e.symm, hy⟩)
      have hL : ∀ α : Life, LtLife δ c α = LtLife δ' c α := by
        intro α; unfold LtLife; rw [ha]
      funext Θ c' n ls e ρ; simp only [cN, h₁, hL, ha]
  | .nu C, δ, δ', h => by
      have hB : ∀ R : CandN, cBN (ℍ := ℍ) (.thunk (.nu C)) R C δ = cBN (ℍ := ℍ) (.thunk (.nu C)) R C δ' :=
        fun R => cBN_congr _ R C h h
      funext Θ c n ls e ρ; simp only [cN, hB]
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy)))
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      have h₅ := retN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ c n ls e ρ; simp only [cN, h₁, h₂, h₃, h₄, h₅]
  termination_by structural x => x
theorem tabN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    tabN (ℍ := ℍ) C δ = tabN (ℍ := ℍ) C δ'
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy)))
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ c; simp only [tabN, h₁, h₂, h₃, h₄]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
  termination_by structural x => x
theorem finN_congr : ∀ (F : CTy) {δ δ' : LSub}, (∀ y, CFree y F → δ.find? y = δ'.find? y) →
    finN (ℍ := ℍ) F δ = finN (ℍ := ℍ) F δ'
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy))
      have h₂ := vN_congr B (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy)))
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ c; simp only [finN, h₁, h₂, h₃, h₄]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
  termination_by structural x => x
theorem retN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    retN (ℍ := ℍ) C δ = retN (ℍ := ℍ) C δ'
  | .ret A, δ, δ', h => by
      have h₁ := vN_congr A (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [retN, h₁]
  | .eff _ _ _ _ _ _ _ C, δ, δ', h => by
      have h₁ := retN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ n v ρ; simp only [retN, h₁]
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
  termination_by structural x => x
end

/-- Extending `δ` at a variable `A` does not mention leaves `𝒱⟦A⟧` alone. -/
theorem vN_extend_of_not_free {x : LifeVar} {A : VTy} (h : ¬ VFree x A) (δ : LSub) (α : Life) :
    vN (ℍ := ℍ) A (δ.extend x α) = vN (ℍ := ℍ) A δ :=
  vN_congr A fun y hy => BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact h hy)

/-! ### Outliving types lie in the stratum -/

/-- **`Δ ⊢ A ⊐ @a`: `𝒱⟦A⟧` lies in `Res_α`, `α = @aδ`** (Core's `vC_outlives`), at every
world. -/
theorem vN_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life} (hδ : Δ.Models δ)
    (ha : a.interp δ = some α) {T : VTy} (hT : VOutlives Δ a T) :
    ∀ Θ n v ρ, vN (ℍ := ℍ) T δ Θ n v ρ → ρ.InStratum α := by
  induction hT with
  | unit => rintro Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty α
  | tensor _ _ ih₁ ih₂ =>
      rintro Θ n v ρ ⟨v₁, v₂, ρ₁, ρ₂, -, hc, h₁, h₂⟩
      exact inStratum_compS hc (ih₁ Θ n v₁ ρ₁ h₁) (ih₂ Θ n v₂ ρ₂ h₂)
  | zero => intro Θ n v ρ h; exact h.elim
  | sum _ _ ih₁ ih₂ =>
      rintro Θ n v ρ (⟨v₁, -, h₁⟩ | ⟨v₂, -, h₂⟩)
      · exact ih₁ Θ n v₁ ρ h₁
      · exact ih₂ Θ n v₂ ρ h₂
  | ref _ ih =>
      rintro Θ n v ρ ⟨l, u, σ, -, hc, h⟩
      exact inStratum_compS hc (ResU.inStratum_single_own α l u) (ih Θ n u σ h)
  | bang => rintro Θ n v ρ ⟨rfl, -⟩; exact ResU.inStratum_empty α
  | box hle =>
      rintro Θ n v ρ ⟨β, hb, -, ho⟩
      obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ho.mono (show (α : Life) ≤ β from hle')
  | imm hlt =>
      rintro Θ n v ρ ⟨β, hb, ⟨l, s, u, σ, hs, -, rfl, hle, -⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l (lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | «mut» hlt =>
      rintro Θ n v ρ ⟨β, hb, b, hβb, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l (lt_of_lt_of_le (show (α : Life) < β from hlt') hβb)
  | tvar => intro Θ n v ρ h; exact h.elim
  | mu _ _ => intro Θ n v ρ h; exact h.elim
  | int => rintro Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty α
  | opq =>
      intro Θ n v ρ h
      rcases Opaque.rel_cases h with ⟨-, rfl, -⟩ | ⟨-, l, -, rfl⟩
      · exact ResU.inStratum_empty α
      · exact ResU.inStratum_single_own α l _
  | fam _ ih =>
      rintro Θ n v ρ ⟨l, c, -, -, hs⟩
      exact sepRange_closed (R := fun σ => σ.InStratum α) (ResU.inStratum_empty α)
        (fun _ _ _ hc o₁ o₂ => inStratum_compS hc o₁ o₂) (fun m σ hm => ih Θ n _ σ hm) hs

/-- **`Δ ⊢ A ⊒ @a`: `𝒱⟦A⟧` lies in every stratum strictly below `α = @aδ`** (Core's
`vC_outlivesLe`, `[TR]` 6.60 at the non-strict side condition), at every world. -/
theorem vN_outlivesLe {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α γ : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) (hγ : γ < α) {T : VTy}
    (hT : VOutlivesLe Δ a T) :
    ∀ Θ n v ρ, vN (ℍ := ℍ) T δ Θ n v ρ → ρ.InStratum γ := by
  induction hT with
  | unit => rintro Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty γ
  | tensor _ _ ih₁ ih₂ =>
      rintro Θ n v ρ ⟨v₁, v₂, ρ₁, ρ₂, -, hc, h₁, h₂⟩
      exact inStratum_compS hc (ih₁ Θ n v₁ ρ₁ h₁) (ih₂ Θ n v₂ ρ₂ h₂)
  | zero => intro Θ n v ρ h; exact h.elim
  | sum _ _ ih₁ ih₂ =>
      rintro Θ n v ρ (⟨v₁, -, h₁⟩ | ⟨v₂, -, h₂⟩)
      · exact ih₁ Θ n v₁ ρ h₁
      · exact ih₂ Θ n v₂ ρ h₂
  | ref _ ih =>
      rintro Θ n v ρ ⟨l, u, σ, -, hc, h⟩
      exact inStratum_compS hc (ResU.inStratum_single_own γ l u) (ih Θ n u σ h)
  | bang => rintro Θ n v ρ ⟨rfl, -⟩; exact ResU.inStratum_empty γ
  | box hle =>
      rintro Θ n v ρ ⟨β, hb, -, ho⟩
      obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ho.mono (le_trans hγ.le (show (α : Life) ≤ β from hle'))
  | imm hlt =>
      rintro Θ n v ρ ⟨β, hb, ⟨l, s, u, σ, hs, -, rfl, hle, -⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l (lt_of_lt_of_le (lt_of_lt_of_le hγ (show (α : Life) ≤ β from hlt')) hle)
  | «mut» hlt =>
      rintro Θ n v ρ ⟨β, hb, b, hβb, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l
        (lt_of_lt_of_le hγ ((show (α : Life) ≤ β from hlt').trans hβb))
  | tvar => intro Θ n v ρ h; exact h.elim
  | mu _ _ => intro Θ n v ρ h; exact h.elim
  | int => rintro Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty γ
  | opq =>
      intro Θ n v ρ h
      rcases Opaque.rel_cases h with ⟨-, rfl, -⟩ | ⟨-, l, -, rfl⟩
      · exact ResU.inStratum_empty γ
      · exact ResU.inStratum_single_own γ l _
  | fam _ ih =>
      rintro Θ n v ρ ⟨l, c, -, -, hs⟩
      exact sepRange_closed (R := fun σ => σ.InStratum γ) (ResU.inStratum_empty γ)
        (fun _ _ _ hc o₁ o₂ => inStratum_compS hc o₁ o₂) (fun m σ hm => ih Θ n _ σ hm) hs

/-! ### Values along the Kripke order -/

/-- One cell at one location determines both. -/
theorem single_immOf_inj {l l' : Loc} {ψ ψ' : CellU Loc Val}
    (e : ResU.single l ψ = ResU.single l' ψ') : l = l' ∧ ψ = ψ' := by
  have h : (ResU.single l' ψ').get l = some ψ := e ▸ ResU.single_get_self l ψ
  exact ResU.single_get_eq_some h


mutual
/-- **`𝒱⟦A⟧` is stable along the resource-relative order at the value's resource** (Core's
`vC_local`): `Mut` by `mutL_extR` (the cell's key and what lies above it are kept), `U` by the
order's transitivity at the thunk's resource, `Imm` because its payload's borrow cells are
longer-lived than the cell and the order keeps every `imm` record, the rest by their parts. -/
theorem vN_extR : ∀ (A : VTy) (δ : LSub) {Θ Θ' : LocTy} (n : Nat) (v : Val) (ρ : WRes),
    Θ.ExtR Θ' ρ → vN (ℍ := ℍ) A δ Θ n v ρ → vN (ℍ := ℍ) A δ Θ' n v ρ
  | .unit, _, _, _, _, _, _, _, h => h
  | .tensor A B, δ, _, _, n, _, _, hE, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vN_extR A δ n v₁ ρ₁ (hE.left h₂) h₃,
        vN_extR B δ n v₂ ρ₂ (hE.right h₂) h₄⟩
  | .zero, _, _, _, _, _, _, _, h => h
  | .sum A B, δ, _, _, n, _, ρ, hE, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vN_extR A δ n v₁ ρ hE h₂⟩
      · exact .inr ⟨v₂, h₁, vN_extR B δ n v₂ ρ hE h₂⟩
  | .thunk _, _, _, _, _, _, _, hE, h => fun Θ'' hE' hOK c hc ls =>
      h Θ'' (hE.trans hE') hOK c hc ls
  | .ref A, δ, _, _, n, _, _, hE, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vN_extR A δ n u σ (hE.right h₂) h₃⟩
  | .imm a A, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, h₄⟩, hw⟩ := h
      have hσ : LocTy.ExtR _ _ σ := hE.mono fun b hb => by
        have hjb : s.join < b := hb.of_stratum hs
        exact ⟨l, CellU.immOf s u σ hs, ResU.single_get_self _ _,
          by simp [CellU.kind_immOf],
          le_of_lt (lt_of_le_of_lt (LSet.meet_le_join s) hjb)⟩
      refine ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, vO_extR A δ n u σ hσ h₄⟩,
        fun l' s' u' σ' hs' e => ?_⟩
      obtain ⟨x, hx, hxs, hd⟩ := hw l' s' u' σ' hs' e
      obtain ⟨-, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨x, hE.2 x hx ⟨l, _, ResU.single_get_self _ _, by simp [CellU.kind_immOf], hxs⟩,
        hxs, hd⟩
  | .mut a A, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, b, hab, hm, hu⟩ := h
      exact ⟨α, hα, b, hab, mutL_extR hE hm, hu⟩
  | .box a A, δ, _, _, n, v, ρ, hE, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vN_extR A δ n v ρ hE h₁, h₂⟩
  | .bang A, δ, _, _, n, v, ρ, hE, h => ⟨h.1, vN_extR A δ n v ρ hE h.2⟩
  | .unk, _, _, _, _, _, _, _, h => h
  | .int _, _, _, _, _, _, _, _, h => h
  | .tvar _, _, _, _, _, _, _, _, h => h
  | .mu _, _, _, _, _, _, _, _, h => h
  | .fam L, δ, Θ, Θ', n, _, _, hE, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono_down (R := fun σ => LocTy.ExtR Θ Θ' σ)
        (fun _ _ _ hc hE' => ⟨hE'.left hc, hE'.right hc⟩)
        (fun m σ hEσ hm => vN_extR L δ n (Val.loc m) σ hEσ hm) hE h₃⟩
  | .opq _, _, _, _, _, _, _, _, h => h

/-- **The observable view is stable along the resource-relative order**, as `vN_extR`. -/
theorem vO_extR : ∀ (A : VTy) (δ : LSub) {Θ Θ' : LocTy} (n : Nat) (v : Val) (ρ : WRes),
    Θ.ExtR Θ' ρ → vO (ℍ := ℍ) A δ Θ n v ρ → vO (ℍ := ℍ) A δ Θ' n v ρ
  | .unit, _, _, _, _, _, _, _, h => h
  | .tensor A B, δ, _, _, n, _, _, hE, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vO_extR A δ n v₁ ρ₁ (hE.left h₂) h₃,
        vO_extR B δ n v₂ ρ₂ (hE.right h₂) h₄⟩
  | .zero, _, _, _, _, _, _, _, h => h
  | .sum A B, δ, _, _, n, _, ρ, hE, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vO_extR A δ n v₁ ρ hE h₂⟩
      · exact .inr ⟨v₂, h₁, vO_extR B δ n v₂ ρ hE h₂⟩
  | .thunk _, _, _, _, _, _, _, _, _ => trivial
  | .ref A, δ, _, _, n, _, _, hE, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vO_extR A δ n u σ (hE.right h₂) h₃⟩
  | .imm a A, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, h₄⟩, hw⟩ := h
      have hσ : LocTy.ExtR _ _ σ := hE.mono fun b hb => by
        have hjb : s.join < b := hb.of_stratum hs
        exact ⟨l, CellU.immOf s u σ hs, ResU.single_get_self _ _,
          by simp [CellU.kind_immOf],
          le_of_lt (lt_of_le_of_lt (LSet.meet_le_join s) hjb)⟩
      refine ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, vO_extR A δ n u σ hσ h₄⟩,
        fun l' s' u' σ' hs' e => ?_⟩
      obtain ⟨x, hx, hxs, hd⟩ := hw l' s' u' σ' hs' e
      obtain ⟨-, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨x, hE.2 x hx ⟨l, _, ResU.single_get_self _ _, by simp [CellU.kind_immOf], hxs⟩,
        hxs, hd⟩
  | .mut a A, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, b, hab, hm, hu⟩ := h
      exact ⟨α, hα, b, hab, mutL_extR hE hm, hu⟩
  | .box a A, δ, _, _, n, v, ρ, hE, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vO_extR A δ n v ρ hE h₁, h₂⟩
  | .bang A, δ, _, _, n, v, ρ, hE, h => ⟨h.1, vN_extR A δ n v ρ hE h.2⟩
  | .unk, _, _, _, _, _, _, _, h => h
  | .int _, _, _, _, _, _, _, _, h => h
  | .tvar _, _, _, _, _, _, _, _, h => h
  | .mu _, _, _, _, _, _, _, _, h => h
  | .fam L, δ, Θ, Θ', n, _, _, hE, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono_down (R := fun σ => LocTy.ExtR Θ Θ' σ)
        (fun _ _ _ hc hE' => ⟨hE'.left hc, hE'.right hc⟩)
        (fun m σ hEσ hm => vO_extR L δ n (Val.loc m) σ hEσ hm) hE h₃⟩
  | .opq _, _, _, _, _, _, _, _, h => h
end

/-- **`𝒱⟦A⟧` is stable along `ExtA`**, at every type: `ExtA` is `ExtR` at every resource. -/
theorem vN_extA (A : VTy) (δ : LSub) {Θ Θ' : LocTy} (hE : Θ.ExtA Θ') (n : Nat) (v : Val)
    (ρ : WRes) (h : vN (ℍ := ℍ) A δ Θ n v ρ) : vN (ℍ := ℍ) A δ Θ' n v ρ :=
  vN_extR A δ n v ρ (hE.extR ρ) h

/-- The computation types `cN_extA` covers: `F A` and `⊤`, read through `&` and `∀`. Not
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

/-- **`𝒞⟦C⟧` is stable along `ExtA`**: `F A` by `erwp_extΦ` at the view (which grows along the
order, `LocTy.view_ext`) and `vN_extA` for its values. Not at an effect row: there the table's answer `vN B δ Θ` is what the continuation was proved to accept,
and the table at `Θ′` hands back answers at `Θ′`. -/
theorem cN_extA : ∀ (C : CTy), noEffSpine C → ∀ (δ : LSub) {Θ Θ' : LocTy}, Θ.ExtA Θ' →
    ∀ c n ls e ρ, cN (ℍ := ℍ) C δ Θ c n ls e ρ → cN (ℍ := ℍ) C δ Θ' c n ls e ρ
  | .ret A, _, δ, _, _, hE, c, n, ls, e, ρ, h =>
      erwp_mono (fun k _ v ρ h => vN_extA A δ hE k v ρ h) (opTableN_local _) n ls e ρ
        (erwp_extΦ (LocTy.view_ext (LocTy.ext_of_extA hE) c) (LocTy.view_immLe hE.2.2 c)
          (opTableN_local _) n ls e ρ h)
  | .arr _ _, hC, _, _, _, _, _, _, _, _, _, _ => hC.elim
  | .amp C D, hC, δ, _, _, hE, c, n, ls, e, ρ, h =>
      ⟨cN_extA C hC.1 δ hE c n ls _ ρ h.1, cN_extA D hC.2 δ hE c n ls _ ρ h.2⟩
  | .top, _, _, _, _, _, _, _, _, _, _, h => h
  | .all x _ C, hC, δ, _, _, hE, c, n, ls, e, ρ, h =>
      fun α hα => cN_extA C hC (δ.extend x α) hE c n ls _ ρ (h α hα)
  | .nu _, hC, _, _, _, _, _, _, _, _, _, _ => hC.elim
  | .eff _ _ _ _ _ _ _ _, hC, _, _, _, _, _, _, _, _, _, _ => hC.elim

/-! ### Values in a lend's stratum do not read the lend -/

/-- **Locality** (Core's `vC_local` along `ext_drop`): a value at the world with a lend at `α`,
whose resource is in `α`'s stratum, is one at the world without it, at every type, `U` included:
the world without the lend is an extension at that resource (`LocTy.extR_of_add`). -/
theorem vN_local (A : VTy) (δ : LSub) (Θ : LocTy) (l₀ : Loc) (α : Life)
    (F : Nat → Val → SPropS Loc Val α) (n : Nat) (v : Val) (ρ : WRes) (hs : ρ.InStratum α)
    (h : vN (ℍ := ℍ) A δ (Θ.add l₀ α F) n v ρ) : vN (ℍ := ℍ) A δ Θ n v ρ :=
  vN_extR A δ n v ρ (LocTy.extR_of_add Θ l₀ F hs) h

/-- **A value of a type outliving the bound lies in the stratum of every lend below it.** -/
theorem vN_inStratum_bnd {A : VTy} {bnd : Lifetime.Life} (hO : VOutlives LifeCtx.empty bnd A)
    {δ : LSub} {α : Life} (hLt : LtLife δ bnd α) {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) A δ Θ n v ρ) : ρ.InStratum α := by
  obtain ⟨γ, hγ, hlt⟩ := hLt
  exact (vN_outlives (models_empty_any _) hγ hO Θ n v ρ h).mono hlt.le

/-- **A fresh lend below the bound does not change `𝒱⟦A⟧` of a type outliving the bound**: its
values are in the lend's stratum, so `vN_local` and `vN_extA` relate the two worlds both ways. -/
theorem vN_add_eq_bnd {A : VTy} {bnd : Lifetime.Life} (hO : VOutlives LifeCtx.empty bnd A)
    (δ : LSub) {α : Life} (hLt : LtLife δ bnd α) {Θ : LocTy} (hf : Θ.Fresh α) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) :
    vN (ℍ := ℍ) A δ (Θ.add l α F) = vN (ℍ := ℍ) A δ Θ := by
  funext n v ρ
  exact propext ⟨fun h => vN_local A δ Θ l α F n v ρ (vN_inStratum_bnd hO hLt h) h,
    fun h => vN_extA A δ (LocTy.extA_add hf l F) n v ρ h⟩

/-- **A stored family is the payload at the world** on content in the cell's stratum. -/
theorem vN_above (A : VTy) (δ : LSub) (Θ : LocTy) {a : Life} {n : Nat} {v : Val} {ρ : WRes}
    (hρ : ρ.InStratum a) : vN (ℍ := ℍ) A δ (Θ.above a) n v ρ ↔ vN (ℍ := ℍ) A δ Θ n v ρ :=
  ⟨vN_extR A δ n v ρ (LocTy.extR_above Θ hρ).1, vN_extR A δ n v ρ (LocTy.extR_above Θ hρ).2⟩

/-! ### `ν`: the greatest fixed point -/

/-- **`𝒞⟦νX. C⟧δ` as a candidate.** -/
abbrev nuCand (C : CTy) (δ : LSub) : CandN := fun Θ c n ls e ρ => cN (ℍ := ℍ) (.nu C) δ Θ c n ls e ρ

theorem nuCand_down (C : CTy) (δ : LSub) : (nuCand (ℍ := ℍ) C δ).Down :=
  fun Θ hOK c n ls e ρ h => cN_down (.nu C) δ Θ hOK.1 c n ls e ρ h

/-- **Coinduction** (Core's `nuRel_coind`): a post-fixed point of one unfolding is below
`𝒞⟦νX. C⟧`. -/
theorem cN_nu_coind {C : CTy} {δ : LSub} {R : CandN}
    (hR : R.Le (cBN (ℍ := ℍ) (.thunk (.nu C)) R C δ)) : R.Le (nuCand (ℍ := ℍ) C δ) :=
  fun _ _ _ _ _ _ h _ => ⟨R, hR, h⟩

/-- **`out`** (Core's `nuRel_out`). -/
theorem cN_nu_out {C : CTy} (hS : C.NuShape) (δ : LSub) :
    (nuCand (ℍ := ℍ) C δ).Le (cBN (ℍ := ℍ) (.thunk (.nu C)) (nuCand (ℍ := ℍ) C δ) C δ) := by
  intro Θ c n ls e ρ h
  obtain ⟨R, hR, hr⟩ := h hS
  exact cBN_mono (fun Θ' _ c' k ls' e' ρ' h' => cN_nu_coind hR Θ' c' k ls' e' ρ' h') hS.nuLeaf δ
    Θ c n ls e ρ (hR Θ c n ls e ρ hr)

/-- **`roll`** (Core's `nuRel_roll`). -/
theorem cN_nu_roll {C : CTy} (hS : C.NuShape) (δ : LSub) :
    (cBN (ℍ := ℍ) (.thunk (.nu C)) (nuCand (ℍ := ℍ) C δ) C δ).Le (nuCand (ℍ := ℍ) C δ) :=
  cN_nu_coind (cBN_mono (fun Θ' _ c' k ls' e' ρ' h' => cN_nu_out hS δ Θ' c' k ls' e' ρ' h')
    hS.nuLeaf δ)

/-- **`𝒞⟦νX. C⟧` is one unfolding of `C` at `𝒞⟦νX. C⟧`** (Core's `cC_nu_unfold`). -/
theorem cN_nu_unfold {C : CTy} (hS : C.NuShape) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (.nu C) δ Θ c n ls e ρ ↔
      cBN (ℍ := ℍ) (.thunk (.nu C)) (nuCand (ℍ := ℍ) C δ) C δ Θ c n ls e ρ :=
  ⟨cN_nu_out hS δ Θ c n ls e ρ, cN_nu_roll hS δ Θ c n ls e ρ⟩

/-- **One unfolding is closed under a pure head step backwards** (Core's `cB_step`). -/
theorem cBN_head (S : VTy) {R : CandN} (hR : R.Down) : ∀ (D : CTy) (δ : LSub) (Θ : LocTy),
    Θ.Down → ∀ (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ : WRes) (K : Kont)
    (a a' : Expr), (∀ μ, BoCa.BoLo.Head (ℍ := ℍ) μ a μ a') → a.allocs = false →
    cBN (ℍ := ℍ) S R D δ Θ c n ls (K.plug a') ρ → cBN (ℍ := ℍ) S R D δ Θ c n ls (K.plug a) ρ
  | .ret A, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      erwp_det (LocTy.view_down hΘ c) (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vNX_down S _ (thunkRN_down hR) A δ Θ k v ρ h)
        (fun μ => step1Only_plug (hh μ) hn K) h
  | .arr A D, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      fun c' k hk v ρv ρ' hc hv hcon =>
        cBN_head S hR D δ Θ hΘ c' k ls ρ' (.appL K v) a a' hh hn (h c' k hk v ρv ρ' hc hv hcon)
  | .amp C D, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      ⟨cBN_head S hR C δ Θ hΘ c n ls ρ (.appL K _) a a' hh hn h.1,
        cBN_head S hR D δ Θ hΘ c n ls ρ (.appL K _) a a' hh hn h.2⟩
  | .top, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | .all x c' D, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      fun α hα => cBN_head S hR D (δ.extend x α) Θ hΘ c n ls ρ (.appL K _) a a' hh hn (h α hα)
  | .nu _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | .eff m i q A B fin rc D, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      erwp_det (LocTy.view_down hΘ c)
        (opTableN_down (extTabN_down (fun k v ρ h => vN_down A δ Θ k v ρ h)
          (finN_down fin δ Θ hΘ c) (tabN_down D δ Θ hΘ c)))
        (fun k _ v ρ h => retNX_down S _ (thunkRN_down hR) D δ Θ k v ρ h)
        (fun μ => step1Only_plug (hh μ) hn K) h

/-! ### Rule checks: `⊑mut`, `⊑imm`, `∀I` at `SemJN` -/

/-- **`𝒞⟦C⟧` is closed under a pure head step backwards**, in every evaluation context: the
`F`/`F_Σ` clauses by `erwp_det`, the others by their parts (Core's `cC_head`). -/
theorem cN_head : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (ρ : WRes) (K : Kont) (a a' : Expr),
    (∀ μ, BoCa.BoLo.Head (ℍ := ℍ) μ a μ a') → a.allocs = false →
    cN (ℍ := ℍ) C δ Θ c n ls (K.plug a') ρ → cN (ℍ := ℍ) C δ Θ c n ls (K.plug a) ρ
  | .ret A, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      erwp_det (LocTy.view_down hΘ c) (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vN_down A δ Θ k v ρ h) (fun μ => step1Only_plug (hh μ) hn K) h
  | .arr A C, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      fun c' k hk v ρv ρ' hc hv hcon =>
        cN_head C δ Θ hΘ c' k ls ρ' (.appL K v) a a' hh hn (h c' k hk v ρv ρ' hc hv hcon)
  | .amp C D, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      ⟨cN_head C δ Θ hΘ c n ls ρ (.appL K _) a a' hh hn h.1,
        cN_head D δ Θ hΘ c n ls ρ (.appL K _) a a' hh hn h.2⟩
  | .top, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | .all x c' C, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      fun α hα => cN_head C (δ.extend x α) Θ hΘ c n ls ρ (.appL K _) a a' hh hn (h α hα)
  | .nu C, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h => fun hS =>
      (cN_nu_unfold hS δ Θ c n ls _ ρ).mpr (cBN_head _ (nuCand_down C δ) C δ Θ hΘ c n ls ρ K a a'
        hh hn ((cN_nu_unfold hS δ Θ c n ls _ ρ).mp h)) hS
  | .eff m i q A B fin rc C, δ, Θ, hΘ, c, n, ls, ρ, K, a, a', hh, hn, h =>
      erwp_det (LocTy.view_down hΘ c)
        (opTableN_down (extTabN_down (fun k v ρ h => vN_down A δ Θ k v ρ h)
          (finN_down fin δ Θ hΘ c) (tabN_down C δ Θ hΘ c)))
        (fun k _ v ρ h => retN_down C δ Θ k v ρ h) (fun μ => step1Only_plug (hh μ) hn K) h

/-- `Δ ⊨ a ⊑ b`'s order on interpretations is `Life`'s. -/
theorem sLe_life {m n : Life} (h : BoCa.Lifetime.SLife.Le m n) : m ≤ n := h

/-- **`⊑mut` at `SemJN`** (`mutSub`, `Core/Fundamental.lean`): Core's `mutSub_compatC` by
`ptoMutS_antitone`. The `Mut` clause's slack `@aδ ⊑ b` absorbs `@aδ ⊑ @bδ`: the cell stays at
its `b`, its key and its uniform conjunct unchanged. -/
theorem mutSub_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.mut b A))) (hle : Δ.EntailsLe a b) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.mut a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine erwp_mono (fun k _ v ρ hv => ?_) (opTableN_local _) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)
  obtain ⟨β', hβ', b', hβb', hm, hu⟩ := hv
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  exact ⟨α, ha, b', le_trans (sLe_life hle') hβb', hm, hu⟩

/-- **`⊑imm` at `SemJN`** (`immSub`): Core's `immSub_compatC` by `ptoImmS_antitone`. -/
theorem immSub_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {a b : Lifetime.Life} {A : VTy}
    (h : SemJN (ℍ := ℍ) Δ Γ e (.val (.imm b A))) (hle : Δ.EntailsLe a b) :
    SemJN (ℍ := ℍ) Δ Γ e (.val (.imm a A)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain ⟨α, β, ha, hb, hle'⟩ := hle δ hδ
  refine erwp_mono (fun k _ v ρ hv => ?_) (opTableN_local _) n ls _ ρ
    (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)
  obtain ⟨β', hβ', ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := hv
  rw [hb] at hβ'
  cases Option.some.inj hβ'
  exact ⟨α, ha, ⟨l, s, u, σ, hs, h₁, h₂, le_trans (sLe_life hle') h₃, h₄⟩, hw⟩

/-- `𝒢⟦Γ⟧` does not read `δ` at a variable no live slot mentions. -/
theorem gN_extend_of_not_free {x : LifeVar} (δ : LSub) (α : Life) (Θ : LocTy) :
    ∀ (Γ : Ctx VTy), (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → ∀ γ n ρ,
      gN (ℍ := ℍ) δ Θ Γ γ n ρ → gN (ℍ := ℍ) (δ.extend x α) Θ Γ γ n ρ
  | [], _, _, _, _, h => h
  | _ :: _, _, [], _, _, h => h
  | s :: Γ, hΓ, v :: γ, n, ρ, h => by
      have ih := gN_extend_of_not_free δ α Θ Γ (fun s' hs' => hΓ s' (List.mem_cons_of_mem _ hs'))
      unfold gN at h ⊢
      split
      · rename_i hl
        rw [if_pos hl] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        refine ⟨ρ₁, ρ₂, hc, ?_, ih γ n ρ₂ h₂⟩
        rw [vN_extend_of_not_free (hΓ s (List.mem_cons_self ..) hl)]
        exact h₁
      · rename_i hl
        rw [if_neg hl] at h
        exact ih γ n ρ h

/-- **`∀I` at `SemJN`** (`allI`, `Core/Fundamental.lean`): Core's `allI_compatC`. At every
`α ⊏ @bδ`, `δ[x ↦ α]` models `Δ, 'x ⊏ @b` (the bound and `Δ`'s bounds do not mention `'x`), the
context's reading does not change (`gN_extend_of_not_free`), and the body is one β step away
(`cN_head`). The `∀` clause reads no definedness of `@b`, as Core's `cC`, so the rule needs none. -/
theorem allI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {M : Expr}
    {S : VTy} {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemJN (ℍ := ℍ) (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.lam M)) (.comp (.all x b C)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg α hα
  obtain ⟨β, hβ, hlt⟩ := hα
  have hδ' : (Δ.extend x b).Models (δ.extend x α) := by
    intro y u hy
    rw [LifeCtx.find?_extend] at hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨α, β, BoCa.Fig16.LogRel.find?_extend_self δ x α,
        by rw [BoCa.Fig16.LogRel.interp_extend_of_not_mentions hbx]; exact hβ, hlt⟩
    · rw [if_neg hxy] at hy
      obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
      exact ⟨m, k, by rw [BoCa.Fig16.LogRel.find?_extend_ne δ α hxy]; exact hm,
        by rw [BoCa.Fig16.LogRel.interp_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩
  show cN (ℍ := ℍ) C (δ.extend x α) Θ c n ls
    (Kont.hole.plug (.app (.val (.lam (Expr.psub 1 γ M))) (.val .unit))) ρ
  refine cN_head C _ Θ hΘ.1 c n ls ρ .hole _ _
    (fun μ => BoCa.BoLo.Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl ?_
  rw [show Kont.hole.plug (Expr.subst 0 Val.unit (Expr.psub 1 γ M)) = substAll (Val.unit :: γ) M
    from (substAll_cons_psub Val.unit γ M).symm]
  exact h (δ.extend x α) (Val.unit :: γ) Θ c n ls ρ hδ' hΘ hc hlw
    (gN_extend_of_not_free δ α Θ Γ hΓx γ n ρ hg)

/-! ## §3. The statements -/

mutual
/-- **The formers the interpretation covers**: every former but type variables and `μ`, which
`vN` reads as empty, and `ν`, which `cN` reads as empty. Families (arrays and slices) are covered
at a covered leaf, and opaque types (`Tok` and the host types) always. Decidable. -/
def _root_.BoCa.Fig16.LogRel.Core.VTy.inFrag : VTy → Bool
  | .unit | .zero | .unk | .int _ | .opq _ => true
  | .tensor A B | .sum A B => A.inFrag && B.inFrag
  | .thunk C => C.inFrag
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .fam A => A.inFrag
  | .tvar _ | .mu _ => false
/-- The computation-type formers the interpretation covers. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.inFrag : CTy → Bool
  | .ret A => A.inFrag
  | .arr A C => A.inFrag && C.inFrag
  | .amp C D => C.inFrag && D.inFrag
  | .top => true
  | .all _ _ C => C.inFrag
  | .nu _ => false
  | .eff _ _ _ A B fin _ C => A.inFrag && B.inFrag && fin.inFrag && C.inFrag
end

/-- **A judgment inside the fragment**: its context's types and its own type use only the formers
the interpretation covers. -/
def JdgInFrag (Γ : Ctx VTy) (j : Jdg) : Bool :=
  Γ.all (fun s => s.ty.inFrag) &&
    match j with
    | .val A => A.inFrag
    | .comp C => C.inFrag

/-- **A #791 constant is a value of `!` its type**, at every `δ`, world and index, from its
rule's premises. -/
def ConstN (c : Const791) : Prop :=
  c.OK → ∀ (δ : LSub) (Θ : LocTy) (n : Nat), Θ.OK →
    vN (ℍ := ℍ) (.bang c.ty) δ Θ n c.val PMap.empty

/-- **A #791 constant inside the fragment**: its type uses only the formers the interpretation
covers. -/
def _root_.BoCa.Fig16.Tree.Wp.Goal791.Const791.InFrag (c : Const791) : Prop := c.ty.inFrag = true

/-- Every #791 constant inside the fragment. -/
def ConstsN : Prop := ∀ c : Const791, c.InFrag → ConstN (ℍ := ℍ) c

/-- **The fundamental property over `erwp`, on the fragment**: every derivation of the existing
judgment whose context and type lie in the fragment (`JdgInFrag`). The rules whose conclusion is
at a former the interpretation reads as empty (the fold constants over `μ`, `roll`, `nuIn`,
`unfoldN`, a type variable's introduction) conclude outside the fragment and are not quantified
over. A derivation of a judgment in the fragment may still cut through an excluded type inside
(`unroll` of a `μ` value); at such a cut the interpretation gives no reading, so `FundamentalN`
is not shown attainable by induction on the derivation until those formers have clauses.

The rule-by-rule map is `docs/new-core/scope-831-map.md`. Its answers on the two risks it named:
* An `imm` lend (`withbor1`, `withbor1U`) runs its callback at the world with the lend's record.
  With `LocTy.above` Core's `ls₀` and `ExtR`'s record conjunct Core's `Keeps`, that world is an
  extension at the callback's resource (`LocTy.extR_addImm`, Core's `ext_add`) and the world
  without the record is one at the result's (`LocTy.extR_of_addImm`, Core's `ext_drop`);
  `withbor1_compatN` and `withbor1U_compatN` (`Core/Chain/ImmLend833N.lean`) follow Core's proofs,
  as do `withbor2_compatN` and `withbor2U_compatN` (the latter at any `Δ` and a `Row.Unwind` row).
  At a `Row.Unwind` row the reborrows `withbor3U_compatN` and `withloadU_compatN`
  (`Core/Chain/Unwind833N.lean`) follow Core's proofs too: the Mut Anti-Frame at the row's own
  table (`erwp_M_antiFrameU`), and 6.150 across the row's raises, abortive unrestricted operations
  included (`withload_rebT`).
* `cN_extA` at an effect row `F_Σ R` is needed by no rule: Core carries the callback's table along
  `Ext` only in `withbor1U_compatX` and `sliceBorrowIU_compatX` (`opTable_ext`), and the chain's
  table does not read the record list. -/
def FundamentalN : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerives Δ Γ e j → JdgInFrag Γ j = true →
    SemJN (ℍ := ℍ) Δ Γ e j

/-- A finaliser's judgment `L ⊸ 1` is in the fragment where `L` is. -/
theorem jdgInFrag_lolli {L : VTy} (h : L.inFrag = true) :
    JdgInFrag [] (.val (.lolli L .unit)) = true := by
  simp [JdgInFrag, VTy.lolli, VTy.inFrag, CTy.inFrag, h]

/-- **The adequacy bridge**: a closed run of `F 1` over `erwp` is `OrDiverges`. -/
def BridgeN : Prop :=
  ∀ e : Expr, (∀ (Θ : LocTy) (c : Loc → Option Life), Θ.OK → ∀ n,
    cN (ℍ := ℍ) (.ret .unit) LSub.empty Θ c n [] e (PMap.empty : WRes)) → OrDiverges (ℍ := ℍ) e

/-- **#791's end goal under a scheduler at the top, over `erwp`**: `poolSchedAdequacyN`'s form,
at the view of any world holding no `imm` record (the task starts at the empty list, which the
relation's entry tie `ImmTieL` reads against the world's `imm` records). A task typed at `F_Σ 1`
from the constants, run by a scheduler meeting `SchedOKN` at the row's table, is safe,
leak-free, or diverges. Scoped to the fragment: the constants' types and the row's
(`Const791.InFrag`, `VTy.inFrag`). -/
def Goal791SchedN : Prop :=
  ∀ (cs : List Const791), (∀ c ∈ cs, c.OK) → (∀ c ∈ cs, c.InFrag) → ∀ (S : Row) (e₀ : Expr),
    (CTy.effOf S .unit).inFrag = true →
    CDerives LifeCtx.empty (ctx791 cs) e₀ (.comp (CTy.effOf S .unit)) →
    ∀ (Θ : LocTy) (c : Loc → Option Life) (n₀ : UInt32) (qs hr hs : Val) (Q : PostN)
      (Inv : List StoredN → Prop),
      Θ.OK → Θ.imm = [] → (∀ k ls v ρ, Q k ls v ρ → ρ = PMap.empty) → Inv [] →
      SchedOKN (ℍ := ℍ) (Θ.view c) (rowTabN (ℍ := ℍ) S Θ c) n₀ qs hr hs
        (fun k _ v ρ => vN (ℍ := ℍ) .unit LSub.empty Θ k v ρ)
        (PoolAnsN (ℍ := ℍ) (Θ.view c) Q (hndVal n₀ qs hr hs) Inv) →
      OrDiverges (ℍ := ℍ)
        (.app (hndE (hndVal n₀ qs hr hs) (substAll (vals791 cs) e₀))
          (stateValN (hndVal n₀ qs hr hs) []).1)

/-- `withbor (2)` at a suspending row. -/
def Withbor2SN : Prop := ∀ x bnd A B S d, ConstN (ℍ := ℍ) (.w2 x bnd A B S d)
/-- `withbor (3)` at a suspending row. -/
def Withbor3SN : Prop := ∀ a x bnd A B S d, ConstN (ℍ := ℍ) (.w3 a x bnd A B S d)
/-- The field reborrow at a suspending row. -/
def WithborFSN : Prop := ∀ a x bnd A B S d, ConstN (ℍ := ℍ) (.wF a x bnd A B S d)
/-- `withload` at a suspending row. -/
def WithloadSN : Prop := ∀ a x bnd A B S, ConstN (ℍ := ℍ) (.wl a x bnd A B S)
/-- `slice_borrow_mut` at a suspending row. -/
def SliceBorrowMSN : Prop := ∀ x bnd A B S d, ConstN (ℍ := ℍ) (.sm x bnd A B S d)

/-! ### What is proved of the statements -/

/-- **The adequacy bridge holds**: `erwp_adequacy` at `F 1`, whose values own nothing, at the
empty world, whose view types nothing. -/
theorem bridgeN : BridgeN (ℍ := ℍ) := fun e h =>
  erwp_adequacy (Φ := LocFam.empty)
    (Q := fun k _ v ρ => vN (ℍ := ℍ) .unit LSub.empty LocTy.empty k v ρ) (fun _ _ _ _ hq => hq.2)
    (fun n => by
      have := h LocTy.empty (fun _ => none) LocTy.empty_ok n
      simp only [cN] at this
      rwa [LocTy.view_empty] at this)

theorem liveWithin_ctx791 : ∀ cs : List Const791, Ctx.LiveWithin (ctx791 cs) (vals791 cs)
  | [] => trivial
  | _ :: cs => liveWithin_ctx791 cs

theorem gN_ctx791 (hC : ConstsN (ℍ := ℍ)) (δ : LSub) {Θ : LocTy} (hΘ : Θ.OK) (n : Nat) :
    ∀ cs : List Const791, (∀ c ∈ cs, c.OK) → (∀ c ∈ cs, c.InFrag) →
      gN (ℍ := ℍ) δ Θ (ctx791 cs) (vals791 cs) n PMap.empty
  | [], _, _ => rfl
  | c :: cs, hcs, hfr => by
      simp only [ctx791, vals791, List.map_cons, gN, if_true]
      exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
        hC c (hfr c (by simp)) (hcs c (by simp)) δ Θ n hΘ,
        gN_ctx791 hC δ hΘ n cs (fun c' h => hcs c' (by simp [h])) (fun c' h => hfr c' (by simp [h]))⟩

theorem jdgInFrag_ctx791 (cs : List Const791) (hfr : ∀ c ∈ cs, c.InFrag) {S : Row}
    (hS : (CTy.effOf S .unit).inFrag = true) :
    JdgInFrag (ctx791 cs) (.comp (CTy.effOf S .unit)) = true := by
  simp only [JdgInFrag, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun s hs => ?_, hS⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
  simpa [VTy.inFrag, Const791.InFrag] using hfr c hc

/-- **`Goal791SchedN` from the fundamental property and the constants**, through
`poolSchedAdequacyN` at the view. -/
theorem goal791Sched_of (hF : FundamentalN (ℍ := ℍ)) (hC : ConstsN (ℍ := ℍ)) :
    Goal791SchedN (ℍ := ℍ) := by
  intro cs hcs hfr S e₀ hSf hder Θ c n₀ qs hr hs Q Inv hΘ hΘI hQ hInv hS
  refine poolSchedAdequacyN (Θ.view c) (rowTabN S Θ c) n₀ qs hr hs _ Q Inv _
    (LocTy.view_down hΘ.1 c) hΘI hQ hInv hS (fun n => ?_)
  have h := hF _ _ _ _ hder (jdgInFrag_ctx791 cs hfr hSf) LSub.empty (vals791 cs) Θ c n []
    PMap.empty (BoCa.Fig16.LogRel.Core.models_empty_any _) hΘ (consistentX_empty c)
    (liveWithin_ctx791 cs) (gN_ctx791 hC LSub.empty hΘ n cs hcs hfr)
  exact (cN_effOf S .unit LSub.empty Θ c n [] _ _).mp h

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
