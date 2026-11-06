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

/-- **An entry of `vNE`'s type-variable environment** (Core's `TEnt`): the closed type the
variable stands for, which the `Imm` clause's witness reads, and the candidate it is read at, over
the mode (`true` the program's relation `vN`, `false` the observable view `vO`), the world, the
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

section
-- Inside the definition, `vN`/`vO` are the relations at the empty environment.
set_option hygiene false in
local notation "vN" => vNE none
set_option hygiene false in
local notation "vO" => vOE none

mutual
/-- **`𝒱⟦A⟧δ` at the world and the index, under a type-variable environment `η`.** Core's `vCE`
clause by clause, `⋆` written as `ResU.CompS`; `Mut` is Core's `ptoMutS` shape over the world
(`Core/Relation.lean`): a lifetime
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
separation of the resource (`sepRange`). A lifetime with no interpretation reads as empty. A type
variable is its environment entry's candidate (empty at the empty environment); `μX. A` is Core's
least fixed point `⋂{P | A[P/X] ⊆ P}`, the candidate joint over the mode, the world and the index,
empty unless `X` is outside `A`'s `Mut` payloads and the `μ` is closed. The `U` clause reads no
environment (Core's `vCE` at `U`: `cC` has none). -/
def vNE : (η : Option (Nat → TEntN)) → VTy → LSub → LocTy → Nat → Val → WRes → Prop
  | _, .unit, _, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | η, .tensor A B, δ, Θ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      vNE η A δ Θ n v₁ ρ₁ ∧ vNE η B δ Θ n v₂ ρ₂
  | _, .zero, _, _, _, _, _ => False
  | η, .sum A B, δ, Θ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ vNE η A δ Θ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ vNE η B δ Θ n v₂ ρ)
  | _, .thunk C, δ, Θ, n, v, ρ => ∀ Θ' : LocTy, Θ.ExtR Θ' ρ → Θ'.OK → ∀ c, ConsistentX c ρ →
      ∀ ls, cN C δ Θ' c n ls (forceE C v.1) ρ
  | η, .ref A, δ, Θ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ vNE η A δ Θ n u σ
  | η, .imm a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => vOE η A δ Θ n u σ) v ρ ∧
        ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s (tCloseN η A) δ
  | η, .mut a A, δ, Θ, n, v, ρ => ∃ α : Life, a.interp δ = some α ∧ ∃ b : Life, α ≤ b ∧
      mutL b (fun Θ' j u r => vNE η A δ Θ' j u r) Θ n v ρ ∧
        ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vNE η A δ Θ' j u r → r.InStratum b
  | η, .box a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧ vNE η A δ Θ n v ρ ∧ ρ.InStratum α
  | η, .bang A, δ, Θ, n, v, ρ => ρ = PMap.empty ∧ vNE η A δ Θ n v ρ
  | _, .unk, _, _, _, _, ρ => ρ = PMap.empty
  | _, .int w, _, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | η, .tvar n, _, Θ, k, v, ρ => tEnvPN η n true Θ k v ρ
  | η, .mu A, δ, Θ, n, v, ρ => A.NoMut 0 ∧ (tCloseN η (.mu A)).Cl 0 ∧
      ∀ P : Bool → LocTy → Nat → Val → WRes → Prop,
        (∀ Θ' k u r, vNE (some (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η))) A δ Θ' k u r →
          P true Θ' k u r) →
        (∀ Θ' k u r, vOE (some (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η))) A δ Θ' k u r →
          P false Θ' k u r) →
        P true Θ n v ρ
  | η, .fam L, δ, Θ, n, v, ρ => ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vNE η L δ Θ n (Val.loc m)) l c.toNat ρ
  | _, .opq k, _, _, _, v, ρ => k.rel v ρ
/-- **`𝒱⟦A⟧δ` in the observable view an `imm` payload is held at** (Core's `vCE false`): `vNE`'s
clauses with `U C` read as `True`, `!A` and `Mut`'s stored family read at `vNE`, a variable at its
entry's observable candidate. -/
def vOE : (η : Option (Nat → TEntN)) → VTy → LSub → LocTy → Nat → Val → WRes → Prop
  | _, .unit, _, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | η, .tensor A B, δ, Θ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      vOE η A δ Θ n v₁ ρ₁ ∧ vOE η B δ Θ n v₂ ρ₂
  | _, .zero, _, _, _, _, _ => False
  | η, .sum A B, δ, Θ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ vOE η A δ Θ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ vOE η B δ Θ n v₂ ρ)
  | _, .thunk _, _, _, _, _, _ => True
  | η, .ref A, δ, Θ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ vOE η A δ Θ n u σ
  | η, .imm a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => vOE η A δ Θ n u σ) v ρ ∧
        ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s (tCloseN η A) δ
  | η, .mut a A, δ, Θ, n, v, ρ => ∃ α : Life, a.interp δ = some α ∧ ∃ b : Life, α ≤ b ∧
      mutL b (fun Θ' j u r => vNE η A δ Θ' j u r) Θ n v ρ ∧
        ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vNE η A δ Θ' j u r → r.InStratum b
  | η, .box a A, δ, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧ vOE η A δ Θ n v ρ ∧ ρ.InStratum α
  | η, .bang A, δ, Θ, n, v, ρ => ρ = PMap.empty ∧ vNE η A δ Θ n v ρ
  | _, .unk, _, _, _, _, ρ => ρ = PMap.empty
  | _, .int w, _, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | η, .tvar n, _, Θ, k, v, ρ => tEnvPN η n false Θ k v ρ
  | η, .mu A, δ, Θ, n, v, ρ => A.NoMut 0 ∧ (tCloseN η (.mu A)).Cl 0 ∧
      ∀ P : Bool → LocTy → Nat → Val → WRes → Prop,
        (∀ Θ' k u r, vNE (some (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η))) A δ Θ' k u r →
          P true Θ' k u r) →
        (∀ Θ' k u r, vOE (some (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η))) A δ Θ' k u r →
          P false Θ' k u r) →
        P false Θ n v ρ
  | η, .fam L, δ, Θ, n, v, ρ => ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vOE η L δ Θ n (Val.loc m)) l c.toNat ρ
  | _, .opq k, _, _, _, v, ρ => k.rel v ρ
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
  | .nu _, _, _, _, _, _, _, _ => False
  | .eff m i q A B fin _ C, δ, Θ, c, n, ls, e, ρ =>
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (extTabN m i
          (entN q B (fun k v ρ => vN A δ Θ k v ρ) (fun k v ρ => vN B δ Θ k v ρ) (finN fin δ Θ c))
          (tabN C δ Θ c)))
        (fun k _ v ρ => retN C δ Θ k v ρ) n ls e ρ
/-- The table of a row's layers below the top one. -/
def tabN : CTy → LSub → LocTy → (Loc → Option Life) → OpTabN
  | .eff m i q A B fin _ C, δ, Θ, c => extTabN m i
      (entN q B (fun k v ρ => vN A δ Θ k v ρ) (fun k v ρ => vN B δ Θ k v ρ) (finN fin δ Θ c))
      (tabN C δ Θ c)
  | _, _, _, _ => OpTabN.empty
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
/-- The answer of a row's layers. -/
def retN : CTy → LSub → LocTy → Nat → Val → WRes → Prop
  | .ret A, δ, Θ, k, v, ρ => vN A δ Θ k v ρ
  | .eff _ _ _ _ _ _ _ C, δ, Θ, k, v, ρ => retN C δ Θ k v ρ
  | .arr _ _, _, _, _, _, _ => False
  | .amp _ _, _, _, _, _, _ => False
  | .top, _, _, _, _, _ => False
  | .all _ _ _, _, _, _, _, _ => False
  | .nu _, _, _, _, _, _ => False
end

end

/-- `𝒱⟦A⟧δ` at the world and the index: `vNE` at the empty environment (Core's `vC`, which is
`vCE none`). `vN (ℍ := h) A …` is `vNE (ℍ := h) none A …`. -/
syntax "vN" : term
macro_rules
  | `(vN) => `(vNE (η := none))
macro_rules
  | `(vN (ℍ := $h) $args*) => `(vNE (ℍ := $h) none $args*)

/-- The observable view at the empty environment. -/
syntax "vO" : term
macro_rules
  | `(vO) => `(vOE (η := none))
macro_rules
  | `(vO (ℍ := $h) $args*) => `(vOE (ℍ := $h) none $args*)

/-! ### The environment (Core's `RelMu`)

`vNE η` reads a type variable at its entry in `η` and `μX. A` at the least fixed point, the
candidate joint over the mode, the world and the index. `vBN η b` is `vNE η` (`b = true`) or
`vOE η` (`b = false`), Core's `vCE η b`. Every law below is Core's (`Core/RelMu.lean`), read at
the chain's arguments. -/

/-- `vNE` in the mode `b` (Core's `vCE η b`). -/
def vBN (η : Option (Nat → TEntN)) : Bool → VTy → LSub → LocTy → Nat → Val → WRes → Prop
  | true => vNE (ℍ := ℍ) η
  | false => vOE (ℍ := ℍ) η

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

/-- `P` is closed under one unfolding of `μX. A` under `η`, in both modes. -/
def MuClosedN (η : Option (Nat → TEntN)) (A : VTy) (δ : LSub)
    (P : Bool → LocTy → Nat → Val → WRes → Prop) : Prop :=
  ∀ b Θ k u r, vBN (ℍ := ℍ) (muEnvN η A P) b A δ Θ k u r → P b Θ k u r

/-- The `μ` clause in both modes. -/
theorem vBN_mu {η : Option (Nat → TEntN)} {A : VTy} {δ : LSub} {b : Bool} {Θ : LocTy} {n : Nat}
    {v : Val} {ρ : WRes} :
    vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ ↔
      A.NoMut 0 ∧ (tCloseN η (.mu A)).Cl 0 ∧
        ∀ P, MuClosedN (ℍ := ℍ) η A δ P → P b Θ n v ρ := by
  cases b
  · exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun P hP => h₃ P (hP true) (hP false)⟩,
      fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun P ht hf => h₃ P (fun b => by cases b; exacts [hf, ht])⟩⟩
  · exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun P hP => h₃ P (hP true) (hP false)⟩,
      fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, fun P ht hf => h₃ P (fun b => by cases b; exacts [hf, ht])⟩⟩

/-- The two modes of an equation of `vBN`. -/
theorem vBN_eq_both {η₁ η₂ : Option (Nat → TEntN)} {A A' : VTy}
    (h : ∀ b, vBN (ℍ := ℍ) η₁ b A = vBN (ℍ := ℍ) η₂ b A') :
    vNE (ℍ := ℍ) η₁ A = vNE η₂ A' ∧ vOE (ℍ := ℍ) η₁ A = vOE η₂ A' :=
  ⟨h true, h false⟩

/-- The relation reads its environment only through `tEnvN` (Core's `vCE_some`). -/
theorem vBN_some (η : Option (Nat → TEntN)) :
    ∀ (A : VTy) (b : Bool), vBN (ℍ := ℍ) η b A = vBN (ℍ := ℍ) (some (tEnvN η)) b A := by
  intro A
  induction A using VTy.recV with
  | unit => intro b; cases b <;> rfl
  | int w => intro b; cases b <;> rfl
  | opq k => intro b; cases b <;> rfl
  | zero => intro b; cases b <;> rfl
  | unk => intro b; cases b <;> rfl
  | thunk _ => intro b; cases b <;> rfl
  | tensor A B ihA ihB =>
      intro b
      obtain ⟨hA₁, hA₂⟩ := vBN_eq_both (ℍ := ℍ) ihA
      obtain ⟨hB₁, hB₂⟩ := vBN_eq_both (ℍ := ℍ) ihB
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | sum A B ihA ihB =>
      intro b
      obtain ⟨hA₁, hA₂⟩ := vBN_eq_both (ℍ := ℍ) ihA
      obtain ⟨hB₁, hB₂⟩ := vBN_eq_both (ℍ := ℍ) ihB
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | ref A ih =>
      intro b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) ih
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | fam L ih =>
      intro b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) ih
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | box a A ih =>
      intro b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) ih
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | bang A ih =>
      intro b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) ih
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | «mut» a A ih =>
      intro b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) ih
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | imm a A ih =>
      intro b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) ih
      have e : tCloseN η A = tCloseN (some (tEnvN η)) A := by rw [tCloseN_eq]; rfl
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂, e]
  | tvar n =>
      intro b; cases b <;> funext δ Θ k v ρ <;> simp only [vBN, vNE, vOE, tEnvPN_eq] <;> rfl
  | mu A _ =>
      intro b
      have e : tCloseN η (.mu A) = tCloseN (some (tEnvN η)) (.mu A) := by rw [tCloseN_eq]; rfl
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, e] <;> rfl

/-- The relation reads only the entries of the variables that occur (Core's `vCE_congr_occ`). -/
theorem vBN_congr_occ : ∀ (A : VTy) (η₁ η₂ : Nat → TEntN), (∀ n, A.Occ n → η₁ n = η₂ n) →
    ∀ b, vBN (ℍ := ℍ) (some η₁) b A = vBN (ℍ := ℍ) (some η₂) b A := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ _ b; cases b <;> rfl
  | int w => intro _ _ _ b; cases b <;> rfl
  | opq k => intro _ _ _ b; cases b <;> rfl
  | zero => intro _ _ _ b; cases b <;> rfl
  | unk => intro _ _ _ b; cases b <;> rfl
  | thunk _ => intro _ _ _ b; cases b <;> rfl
  | tensor A B ihA ihB =>
      intro η₁ η₂ h b
      obtain ⟨hA₁, hA₂⟩ := vBN_eq_both (ℍ := ℍ) (ihA η₁ η₂ (fun n hn => h n (Or.inl hn)))
      obtain ⟨hB₁, hB₂⟩ := vBN_eq_both (ℍ := ℍ) (ihB η₁ η₂ (fun n hn => h n (Or.inr hn)))
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | sum A B ihA ihB =>
      intro η₁ η₂ h b
      obtain ⟨hA₁, hA₂⟩ := vBN_eq_both (ℍ := ℍ) (ihA η₁ η₂ (fun n hn => h n (Or.inl hn)))
      obtain ⟨hB₁, hB₂⟩ := vBN_eq_both (ℍ := ℍ) (ihB η₁ η₂ (fun n hn => h n (Or.inr hn)))
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | ref A ih =>
      intro η₁ η₂ h b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η₁ η₂ h)
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | fam L ih =>
      intro η₁ η₂ h b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η₁ η₂ h)
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | box a A ih =>
      intro η₁ η₂ h b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η₁ η₂ h)
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | bang A ih =>
      intro η₁ η₂ h b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η₁ η₂ h)
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | «mut» a A ih =>
      intro η₁ η₂ h b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η₁ η₂ h)
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂]
  | imm a A ih =>
      intro η₁ η₂ h b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η₁ η₂ h)
      have e : tCloseN (some η₁) A = tCloseN (some η₂) A :=
        VTy.subst_congr_occ A (fun n hn => by rw [h n hn])
      cases b <;> funext δ Θ n v ρ <;> simp only [vBN, vNE, vOE, h₁, h₂, e]
  | tvar n =>
      intro η₁ η₂ h b
      cases b <;> funext δ Θ k v ρ <;> simp only [vBN, vNE, vOE, tEnvPN, h n rfl]
  | mu A ih =>
      intro η₁ η₂ h b
      have e : tCloseN (some η₁) (.mu A) = tCloseN (some η₂) (.mu A) :=
        VTy.subst_congr_occ (.mu A) (fun n hn => by rw [h n hn])
      have hb : ∀ P, ∀ b', vBN (ℍ := ℍ) (muEnvN (some η₁) A P) b' A =
          vBN (ℍ := ℍ) (muEnvN (some η₂) A P) b' A := by
        intro P b'
        simp only [muEnvN, e, tEnvN]
        exact ih _ _ (fun n hn => by
          cases n with
          | zero => rfl
          | succ n => exact h n hn) b'
      funext δ Θ n v ρ
      apply propext
      rw [vBN_mu, vBN_mu, e]
      refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun P => imp_congr ?_ Iff.rfl))
      unfold MuClosedN
      simp only [hb]


/-! ### Renaming and substitution -/

theorem vBN_rename : ∀ (A : VTy) (η : Nat → TEntN) (r : Nat → Nat) (b : Bool),
    vBN (ℍ := ℍ) (some η) b (A.rename r) = vBN (ℍ := ℍ) (some (η ∘ r)) b A := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ b; cases b <;> rfl
  | int w => intro _ _ b; cases b <;> rfl
  | opq k => intro _ _ b; cases b <;> rfl
  | zero => intro _ _ b; cases b <;> rfl
  | unk => intro _ _ b; cases b <;> rfl
  | thunk _ => intro _ _ b; cases b <;> rfl
  | tvar n => intro _ _ b; cases b <;> rfl
  | tensor A B ihA ihB =>
      intro η r b
      obtain ⟨hA₁, hA₂⟩ := vBN_eq_both (ℍ := ℍ) (ihA η r)
      obtain ⟨hB₁, hB₂⟩ := vBN_eq_both (ℍ := ℍ) (ihB η r)
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | sum A B ihA ihB =>
      intro η r b
      obtain ⟨hA₁, hA₂⟩ := vBN_eq_both (ℍ := ℍ) (ihA η r)
      obtain ⟨hB₁, hB₂⟩ := vBN_eq_both (ℍ := ℍ) (ihB η r)
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | ref A ih =>
      intro η r b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η r)
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, h₁, h₂]
  | fam L ih =>
      intro η r b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η r)
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, h₁, h₂]
  | box a A ih =>
      intro η r b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η r)
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, h₁, h₂]
  | bang A ih =>
      intro η r b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η r)
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, h₁, h₂]
  | «mut» a A ih =>
      intro η r b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η r)
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, h₁, h₂]
  | imm a A ih =>
      intro η r b
      obtain ⟨h₁, h₂⟩ := vBN_eq_both (ℍ := ℍ) (ih η r)
      have e : tCloseN (some η) (A.rename r) = tCloseN (some (η ∘ r)) A := by
        simp only [tCloseN, VTy.subst_rename]; rfl
      cases b <;> funext δ Θ n v w <;> simp only [VTy.rename, vBN, vNE, vOE, h₁, h₂, e]
  | mu A ih =>
      intro η r b
      have e' : tCloseN (some η) (.mu (A.rename (VTy.upR r))) = tCloseN (some (η ∘ r)) (.mu A) := by
        simp only [tCloseN]
        rw [show VTy.mu (A.rename (VTy.upR r)) = (VTy.mu A).rename r from rfl, VTy.subst_rename]
        rfl
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN (some η) (A.rename (VTy.upR r)) P) b'
          (A.rename (VTy.upR r)) = vBN (ℍ := ℍ) (muEnvN (some (η ∘ r)) A P) b' A := by
        intro P b'
        simp only [muEnvN, tEnvN]
        rw [ih, scons_comp_upR, e']
      show vBN (ℍ := ℍ) (some η) b (.mu (A.rename (VTy.upR r))) = _
      funext δ Θ n v w
      apply propext
      rw [vBN_mu, vBN_mu, e', VTy.noMut_rename_upR_iff]
      refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun P => imp_congr ?_ Iff.rfl))
      unfold MuClosedN
      simp only [hb]

/-- The environment a substitution moves into (Core's `substEnv`). -/
def substEnvN (η : Nat → TEntN) (σ : Nat → VTy) (δ : LSub) : Nat → TEntN :=
  fun n => ⟨(σ n).subst (fun k => (η k).ty), fun b => vBN (ℍ := ℍ) (some η) b (σ n) δ⟩

theorem vBN_subst : ∀ (A : VTy) (η : Nat → TEntN) (σ : Nat → VTy) (δ : LSub) (b : Bool),
    vBN (ℍ := ℍ) (some η) b (A.subst σ) δ = vBN (ℍ := ℍ) (some (substEnvN (ℍ := ℍ) η σ δ)) b A δ := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ _ b; cases b <;> rfl
  | int w => intro _ _ _ b; cases b <;> rfl
  | opq k => intro _ _ _ b; cases b <;> rfl
  | zero => intro _ _ _ b; cases b <;> rfl
  | unk => intro _ _ _ b; cases b <;> rfl
  | thunk _ => intro _ _ _ b; cases b <;> rfl
  | tvar n => intro _ _ _ b; cases b <;> rfl
  | tensor A B ihA ihB =>
      intro η σ δ b
      have hA₁ := ihA η σ δ true; have hA₂ := ihA η σ δ false
      have hB₁ := ihB η σ δ true; have hB₂ := ihB η σ δ false
      simp only [vBN] at hA₁ hA₂ hB₁ hB₂
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | sum A B ihA ihB =>
      intro η σ δ b
      have hA₁ := ihA η σ δ true; have hA₂ := ihA η σ δ false
      have hB₁ := ihB η σ δ true; have hB₂ := ihB η σ δ false
      simp only [vBN] at hA₁ hA₂ hB₁ hB₂
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, hA₁, hA₂, hB₁, hB₂]
  | ref A ih =>
      intro η σ δ b
      have h₁ := ih η σ δ true; have h₂ := ih η σ δ false
      simp only [vBN] at h₁ h₂
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, h₁, h₂]
  | fam L ih =>
      intro η σ δ b
      have h₁ := ih η σ δ true; have h₂ := ih η σ δ false
      simp only [vBN] at h₁ h₂
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, h₁, h₂]
  | box a A ih =>
      intro η σ δ b
      have h₁ := ih η σ δ true; have h₂ := ih η σ δ false
      simp only [vBN] at h₁ h₂
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, h₁, h₂]
  | bang A ih =>
      intro η σ δ b
      have h₁ := ih η σ δ true; have h₂ := ih η σ δ false
      simp only [vBN] at h₁ h₂
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, h₁, h₂]
  | «mut» a A ih =>
      intro η σ δ b
      have h₁ := ih η σ δ true; have h₂ := ih η σ δ false
      simp only [vBN] at h₁ h₂
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, h₁, h₂]
  | imm a A ih =>
      intro η σ δ b
      have h₁ := ih η σ δ true; have h₂ := ih η σ δ false
      simp only [vBN] at h₁ h₂
      have e : tCloseN (some η) (A.subst σ) = tCloseN (some (substEnvN (ℍ := ℍ) η σ δ)) A := by
        simp only [tCloseN, substEnvN, VTy.subst_subst]
      cases b <;> funext Θ n v w <;> simp only [VTy.subst, vBN, vNE, vOE, h₁, h₂, e]
  | mu A ih =>
      intro η σ δ b
      have eM : tCloseN (some η) (.mu (A.subst (VTy.upS σ)))
          = tCloseN (some (substEnvN (ℍ := ℍ) η σ δ)) (.mu A) := by
        simp only [tCloseN, substEnvN]
        rw [show VTy.mu (A.subst (VTy.upS σ)) = (VTy.mu A).subst σ from rfl, VTy.subst_subst]
      have eenv : ∀ P, substEnvN (ℍ := ℍ)
          (VTy.scons ⟨tCloseN (some (substEnvN (ℍ := ℍ) η σ δ)) (.mu A), P⟩ η) (VTy.upS σ) δ =
          VTy.scons ⟨tCloseN (some (substEnvN (ℍ := ℍ) η σ δ)) (.mu A), P⟩
            (substEnvN (ℍ := ℍ) η σ δ) := by
        intro P
        funext n
        cases n with
        | zero =>
            refine TEntN.ext' rfl ?_
            funext b; cases b <;> rfl
        | succ n =>
            refine TEntN.ext' ?_ ?_
            · show (VTy.rename Nat.succ (σ n)).subst _ = _
              rw [VTy.subst_rename]; rfl
            · funext b
              show vBN (ℍ := ℍ) _ b (VTy.rename Nat.succ (σ n)) δ = _
              rw [vBN_rename]; rfl
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN (some η) (A.subst (VTy.upS σ)) P) b'
          (A.subst (VTy.upS σ)) δ =
          vBN (ℍ := ℍ) (muEnvN (some (substEnvN (ℍ := ℍ) η σ δ)) A P) b' A δ := by
        intro P b'
        simp only [muEnvN, tEnvN]
        rw [eM, ih, eenv]
      show vBN (ℍ := ℍ) (some η) b (.mu (A.subst (VTy.upS σ))) δ = _
      funext Θ n v w
      apply propext
      rw [vBN_mu, vBN_mu, eM, VTy.noMut_upS_iff]
      refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun P => imp_congr ?_ Iff.rfl))
      unfold MuClosedN
      simp only [hb]

/-! ### Monotonicity in an entry outside every `Mut` payload -/

/-- The relation is monotone in the entry of a variable that occurs in no `Mut` payload (Core's
`vCE_mono_at`). -/
theorem vBN_mono_at : ∀ (A : VTy) (k : Nat) (η₁ η₂ : Nat → TEntN), A.NoMut k →
    (∀ n, (η₁ n).ty = (η₂ n).ty) → (∀ n, n ≠ k → (η₁ n).P = (η₂ n).P) →
    (∀ b Θ j v ρ, (η₁ k).P b Θ j v ρ → (η₂ k).P b Θ j v ρ) →
    ∀ b δ Θ j v ρ, vBN (ℍ := ℍ) (some η₁) b A δ Θ j v ρ → vBN (ℍ := ℍ) (some η₂) b A δ Θ j v ρ := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ _ _ _ _ _ b _ _ _ _ _ h; cases b <;> exact h
  | int w => intro _ _ _ _ _ _ _ b _ _ _ _ _ h; cases b <;> exact h
  | opq k => intro _ _ _ _ _ _ _ b _ _ _ _ _ h; cases b <;> exact h
  | zero => intro _ _ _ _ _ _ _ b _ _ _ _ _ h; cases b <;> exact h
  | unk => intro _ _ _ _ _ _ _ b _ _ _ _ _ h; cases b <;> exact h
  | thunk _ => intro _ _ _ _ _ _ _ b _ _ _ _ _ h; cases b <;> exact h
  | tensor A B ihA ihB =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      cases b <;>
      · obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
        first
        | exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, ihA k η₁ η₂ hk.1 ht hP hPk false δ Θ j v₁ ρ₁ h₃,
            ihB k η₁ η₂ hk.2 ht hP hPk false δ Θ j v₂ ρ₂ h₄⟩
        | exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, ihA k η₁ η₂ hk.1 ht hP hPk true δ Θ j v₁ ρ₁ h₃,
            ihB k η₁ η₂ hk.2 ht hP hPk true δ Θ j v₂ ρ₂ h₄⟩
  | sum A B ihA ihB =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      cases b <;>
      · rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
        · first
          | exact .inl ⟨v₁, h₁, ihA k η₁ η₂ hk.1 ht hP hPk false δ Θ j v₁ ρ h₂⟩
          | exact .inl ⟨v₁, h₁, ihA k η₁ η₂ hk.1 ht hP hPk true δ Θ j v₁ ρ h₂⟩
        · first
          | exact .inr ⟨v₂, h₁, ihB k η₁ η₂ hk.2 ht hP hPk false δ Θ j v₂ ρ h₂⟩
          | exact .inr ⟨v₂, h₁, ihB k η₁ η₂ hk.2 ht hP hPk true δ Θ j v₂ ρ h₂⟩
  | ref A ih =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      cases b <;>
      · obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
        first
        | exact ⟨l, u, σ, h₁, h₂, ih k η₁ η₂ hk ht hP hPk false δ Θ j u σ h₃⟩
        | exact ⟨l, u, σ, h₁, h₂, ih k η₁ η₂ hk ht hP hPk true δ Θ j u σ h₃⟩
  | fam L ih =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      cases b <;>
      · obtain ⟨l, c, h₁, h₂, h₃⟩ := h
        first
        | exact ⟨l, c, h₁, h₂, sepRange_mono'
            (fun m σ hm => ih k η₁ η₂ hk ht hP hPk false δ Θ j _ σ hm) h₃⟩
        | exact ⟨l, c, h₁, h₂, sepRange_mono'
            (fun m σ hm => ih k η₁ η₂ hk ht hP hPk true δ Θ j _ σ hm) h₃⟩
  | imm a A ih =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      have e : tCloseN (some η₁) A = tCloseN (some η₂) A := by
        simp only [tCloseN]; congr 1; funext n; exact ht n
      cases b <;>
      · obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
        exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃,
          ih k η₁ η₂ hk ht hP hPk false δ Θ j u σ h₄⟩, fun l s u σ h hρ => e ▸ hw l s u σ h hρ⟩
  | «mut» a A _ =>
      intro k η₁ η₂ hk ht hP _ b δ Θ j v ρ h
      rw [vBN_congr_occ (.mut a A) η₁ η₂ (fun n hn => by
        refine TEntN.ext' (ht n) (hP n ?_)
        rintro rfl; exact hk hn)] at h
      exact h
  | box a A ih =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      cases b <;>
      · obtain ⟨α, hα, h₁, h₂⟩ := h
        first
        | exact ⟨α, hα, ih k η₁ η₂ hk ht hP hPk false δ Θ j v ρ h₁, h₂⟩
        | exact ⟨α, hα, ih k η₁ η₂ hk ht hP hPk true δ Θ j v ρ h₁, h₂⟩
  | bang A ih =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      cases b <;> exact ⟨h.1, ih k η₁ η₂ hk ht hP hPk true δ Θ j v ρ h.2⟩
  | tvar n =>
      intro k η₁ η₂ _ _ hP hPk b δ Θ j v ρ h
      by_cases e : n = k
      · subst e; cases b <;> exact hPk _ Θ j v ρ h
      · cases b <;>
        · show (η₂ n).P _ Θ j v ρ
          rw [← hP n e]; exact h
  | mu A ih =>
      intro k η₁ η₂ hk ht hP hPk b δ Θ j v ρ h
      have eM : tCloseN (some η₁) (.mu A) = tCloseN (some η₂) (.mu A) := by
        simp only [tCloseN]; congr 1; funext n; exact ht n
      obtain ⟨hnm, hcl, hlfp⟩ := vBN_mu.mp h
      refine vBN_mu.mpr ⟨hnm, eM ▸ hcl, fun P hPre => hlfp P (fun b' Θ' k' u r h' => hPre b' Θ' k' u r ?_)⟩
      refine ih (k + 1) _ _ hk (fun n => ?_) (fun n hn => ?_) ?_ b' δ Θ' k' u r h'
      · cases n with
        | zero => exact eM
        | succ n => exact ht n
      · cases n with
        | zero => rfl
        | succ n => exact hP n (fun e => hn (by rw [e]))
      · exact hPk

/-! ### The unroll equation -/

/-- One unfolding of `μX. A` at the candidate `P` (Core's `cBody`). -/
def bodyN (A : VTy) (δ : LSub) (P : Bool → LocTy → Nat → Val → WRes → Prop) :
    Bool → LocTy → Nat → Val → WRes → Prop :=
  fun b => vBN (ℍ := ℍ) (muEnvN none A P) b A δ

/-- `A[μX. A/X]` is the body at `𝒱⟦μX. A⟧` (Core's `vC_inst`). -/
theorem vN_inst (A : VTy) (δ : LSub) (b : Bool) :
    vBN (ℍ := ℍ) none b (VTy.inst (.mu A) A) δ =
      bodyN (ℍ := ℍ) A δ (fun b => vBN (ℍ := ℍ) none b (.mu A) δ) b := by
  rw [vBN_some none, VTy.inst, vBN_subst, bodyN, muEnvN]
  congr 2
  funext n
  cases n with
  | zero =>
      refine TEntN.ext' (VTy.subst_id _) ?_
      funext b
      show vBN (ℍ := ℍ) (some (tEnvN none)) b (.mu A) δ = vBN (ℍ := ℍ) none b (.mu A) δ
      rw [← vBN_some]
  | succ n =>
      refine TEntN.ext' rfl ?_
      funext b; cases b <;> rfl

theorem bodyN_mono (A : VTy) (δ : LSub) (hA : A.NoMut 0)
    {P Q : Bool → LocTy → Nat → Val → WRes → Prop}
    (h : ∀ b Θ k v ρ, P b Θ k v ρ → Q b Θ k v ρ) :
    ∀ b Θ k v ρ, bodyN (ℍ := ℍ) A δ P b Θ k v ρ → bodyN (ℍ := ℍ) A δ Q b Θ k v ρ :=
  fun b Θ k v ρ => vBN_mono_at A 0 _ _ hA (fun n => by cases n <;> rfl)
    (fun n hn => by
      cases n with
      | zero => exact absurd rfl hn
      | succ n => rfl) h b δ Θ k v ρ

/-- `roll` (Core's `vC_roll`), at the same index: the machine has no `roll` step. -/
theorem vBN_roll {A : VTy} {b : Bool} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0)
    (h : vBN (ℍ := ℍ) none b (VTy.inst (.mu A) A) δ Θ n v ρ) :
    vBN (ℍ := ℍ) none b (.mu A) δ Θ n v ρ := by
  rw [vN_inst] at h
  exact vBN_mu.mpr ⟨hA, hc, fun P hP => hP b Θ n v ρ
    (bodyN_mono A δ hA (fun b' Θ' k' v' ρ' h' => (vBN_mu.mp h').2.2 P hP) b Θ n v ρ h)⟩

/-- `unroll` (Core's `vC_unfold`), at the same index. -/
theorem vBN_unfold {A : VTy} {b : Bool} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (h : vBN (ℍ := ℍ) none b (.mu A) δ Θ n v ρ) :
    A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vBN (ℍ := ℍ) none b (VTy.inst (.mu A) A) δ Θ n v ρ := by
  obtain ⟨hA, hc, hlfp⟩ := vBN_mu.mp h
  refine ⟨hA, hc, ?_⟩
  rw [vN_inst]
  exact hlfp (bodyN A δ (fun b => vBN (ℍ := ℍ) none b (.mu A) δ)) (fun b' Θ' k' v' ρ' h' =>
    bodyN_mono A δ hA (fun b'' Θ'' k'' v'' ρ'' h'' => vBN_roll hA hc (by rw [vN_inst]; exact h''))
      b' Θ' k' v' ρ' h')

/-- **The unroll equation** (Core's `vC_mu_iff`), at the same index. -/
theorem vBN_mu_iff {A : VTy} {b : Bool} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes} :
    vBN (ℍ := ℍ) none b (.mu A) δ Θ n v ρ ↔
      A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vBN (ℍ := ℍ) none b (VTy.inst (.mu A) A) δ Θ n v ρ :=
  ⟨vBN_unfold, fun ⟨hA, hc, h⟩ => vBN_roll hA hc h⟩

/-- `roll` at `vN`. -/
theorem vN_roll {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (hA : A.NoMut 0) (hc : (VTy.mu A).Cl 0) (h : vN (ℍ := ℍ) (VTy.inst (.mu A) A) δ Θ n v ρ) :
    vN (ℍ := ℍ) (.mu A) δ Θ n v ρ :=
  vBN_roll (b := true) hA hc h

/-- `unroll` at `vN`. -/
theorem vN_unfold {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.mu A) δ Θ n v ρ) :
    A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vN (ℍ := ℍ) (VTy.inst (.mu A) A) δ Θ n v ρ :=
  vBN_unfold (b := true) h

/-- **The unroll equation at `vN`.** -/
theorem vN_mu_iff {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes} :
    vN (ℍ := ℍ) (.mu A) δ Θ n v ρ ↔
      A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ vN (ℍ := ℍ) (VTy.inst (.mu A) A) δ Θ n v ρ :=
  vBN_mu_iff (b := true)

/-- `roll` under an environment: the body at the environment whose new entry is `μX. A` itself is a
value of `μX. A`. -/
theorem vBN_rollE {η : Option (Nat → TEntN)} {A : VTy} {δ : LSub} {b : Bool} {Θ : LocTy} {n : Nat}
    {v : Val} {ρ : WRes} (hA : A.NoMut 0) (hc : (tCloseN η (.mu A)).Cl 0)
    (h : vBN (ℍ := ℍ) (muEnvN η A (fun b => vBN (ℍ := ℍ) η b (.mu A) δ)) b A δ Θ n v ρ) :
    vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ :=
  vBN_mu.mpr ⟨hA, hc, fun P hP => hP b Θ n v ρ
    (vBN_mono_at A 0 (VTy.scons ⟨tCloseN η (.mu A), fun b => vBN (ℍ := ℍ) η b (.mu A) δ⟩ (tEnvN η))
      (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η)) hA (fun m => by cases m <;> rfl)
      (fun m hm => by
        cases m with
        | zero => exact absurd rfl hm
        | succ m => rfl)
      (fun b' Θ' k' v' ρ' (h' : vBN (ℍ := ℍ) η b' (.mu A) δ Θ' k' v' ρ') => (vBN_mu.mp h').2.2 P hP)
      b δ Θ n v ρ h)⟩

/-- **Induction on the least fixed point at `μX. A` under an environment** (Core's `vC_mu_ind`): a
property closed under one unfolding of the body, read at the relation and the property at `X`,
holds of `μX. A`. -/
theorem vBN_mu_ind {η : Option (Nat → TEntN)} {A : VTy} {δ : LSub}
    (Φ : Bool → LocTy → Nat → Val → WRes → Prop)
    (h : ∀ b Θ n v ρ, A.NoMut 0 → (tCloseN η (.mu A)).Cl 0 →
      vBN (ℍ := ℍ) (muEnvN η A (fun b Θ n v ρ => vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ ∧ Φ b Θ n v ρ))
        b A δ Θ n v ρ → Φ b Θ n v ρ) :
    ∀ b Θ n v ρ, vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ → Φ b Θ n v ρ := by
  intro b Θ n v ρ hv
  obtain ⟨hA, hc, hlfp⟩ := vBN_mu.mp hv
  refine (hlfp (fun b Θ n v ρ => vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ ∧ Φ b Θ n v ρ)
    (fun b' Θ' n' v' ρ' h' => ⟨vBN_rollE hA hc ?_, h b' Θ' n' v' ρ' hA hc h'⟩)).2
  exact vBN_mono_at A 0
    (VTy.scons ⟨tCloseN η (.mu A), fun b Θ n v ρ => vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ ∧ Φ b Θ n v ρ⟩
      (tEnvN η))
    (VTy.scons ⟨tCloseN η (.mu A), fun b => vBN (ℍ := ℍ) η b (.mu A) δ⟩ (tEnvN η)) hA
    (fun m => by cases m <;> rfl)
    (fun m hm => by
      cases m with
      | zero => exact absurd rfl hm
      | succ m => rfl)
    (fun _ _ _ _ _ h => h.1) b' δ Θ' n' v' ρ' h'

/-! ### The induction principle -/

/-- One unfolding of the relation at every type (Core's `vF`), with `S` at the positions the
clauses recurse to: the `Mut` clause is kept, with `S` at every value of its payload's type; at
`μX. A` the unrolling `A[μX. A/X]`. -/
def vFN (S : Bool → VTy → LocTy → Nat → Val → WRes → Prop) (δ : LSub) :
    Bool → VTy → LocTy → Nat → Val → WRes → Prop
  | _, .unit, _, _, v, ρ => v = Val.unit ∧ ρ = PMap.empty
  | _, .int w, _, _, v, ρ => v.IsInt w ∧ ρ = PMap.empty
  | _, .opq k, _, _, v, ρ => k.rel v ρ
  | b, .tensor A B, Θ, n, v, ρ => ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ ρ ∧
      S b A Θ n v₁ ρ₁ ∧ S b B Θ n v₂ ρ₂
  | _, .zero, _, _, _, _ => False
  | b, .sum A B, Θ, n, v, ρ =>
      (∃ v₁, v = Val.inj₁ v₁ ∧ S b A Θ n v₁ ρ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ S b B Θ n v₂ ρ)
  | b, .thunk C, Θ, n, v, ρ => vBN (ℍ := ℍ) none b (.thunk C) δ Θ n v ρ
  | _, .bang A, Θ, n, v, ρ => ρ = PMap.empty ∧ S true A Θ n v ρ
  | b, .box a A, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧ S b A Θ n v ρ ∧ ρ.InStratum α
  | b, .ref A, Θ, n, v, ρ => ∃ (l : Loc) (u : Val) (σ : WRes), v = Val.loc l ∧
      ResU.CompS (ResU.single l (CellU.ownOf u)) σ ρ ∧ S b A Θ n u σ
  | b, .fam L, Θ, n, v, ρ => ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => S b L Θ n (Val.loc m)) l c.toNat ρ
  | _, .imm a A, Θ, n, v, ρ => ∃ α, a.interp δ = some α ∧
      immCell α (fun u σ => S false A Θ n u σ) v ρ ∧
        ∀ l s u σ h, ρ = ResU.single l (CellU.immOf s u σ h) → ImmWitW Θ.imm l s A δ
  | b, .mut a A, Θ, n, v, ρ => vBN (ℍ := ℍ) none b (.mut a A) δ Θ n v ρ ∧
      ∀ Θ' j u σ, vN (ℍ := ℍ) A δ Θ' j u σ → S true A Θ' j u σ
  | _, .unk, _, _, _, ρ => ρ = PMap.empty
  | _, .tvar _, _, _, _, _ => False
  | b, .mu A, Θ, n, v, ρ => A.NoMut 0 ∧ (VTy.mu A).Cl 0 ∧ S b (VTy.inst (.mu A) A) Θ n v ρ

/-- The relation is its own unfolding (Core's `vF_vC`). -/
theorem vFN_vN (δ : LSub) : ∀ (b : Bool) (T : VTy) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    vBN (ℍ := ℍ) none b T δ Θ n v ρ ↔
      vFN (ℍ := ℍ) (fun b T => vBN (ℍ := ℍ) none b T δ) δ b T Θ n v ρ
  | b, .unit, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .int _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .opq _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .tensor _ _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .sum _ _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .zero, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .thunk _, _, _, _, _ => Iff.rfl
  | b, .box _ _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .ref _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .fam _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .bang _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .imm _ _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | _, .mut _ _, _, _, _, _ => ⟨fun h => ⟨h, fun _ _ _ _ h => h⟩, And.left⟩
  | b, .unk, _, _, _, _ => by cases b <;> exact Iff.rfl
  | b, .tvar _, _, _, _, _ => by cases b <;> exact Iff.rfl
  | _, .mu _, _, _, _, _ => vBN_mu_iff

theorem vFN_mono {S₁ S₂ : Bool → VTy → LocTy → Nat → Val → WRes → Prop}
    (h : ∀ b T Θ n v ρ, S₁ b T Θ n v ρ → S₂ b T Θ n v ρ) (δ : LSub) :
    ∀ (b : Bool) (T : VTy) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
      vFN (ℍ := ℍ) S₁ δ b T Θ n v ρ → vFN (ℍ := ℍ) S₂ δ b T Θ n v ρ
  | _, .unit, _, _, _, _, hs => hs
  | _, .int _, _, _, _, _, hs => hs
  | _, .opq _, _, _, _, _, hs => hs
  | b, .tensor T₁ T₂, Θ, n, _, _, hs => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := hs
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h b T₁ Θ n v₁ ρ₁ h₃, h b T₂ Θ n v₂ ρ₂ h₄⟩
  | b, .sum T₁ T₂, Θ, n, _, ρ, hs => by
      rcases hs with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, h b T₁ Θ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, h b T₂ Θ n v₂ ρ h₂⟩
  | _, .zero, _, _, _, _, hs => hs
  | _, .thunk _, _, _, _, _, hs => hs
  | b, .box _ T, Θ, n, v, ρ, hs => by
      obtain ⟨α, hα, h₁, h₂⟩ := hs
      exact ⟨α, hα, h b T Θ n v ρ h₁, h₂⟩
  | b, .ref T, Θ, n, _, _, hs => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := hs
      exact ⟨l, u, σ, h₁, h₂, h b T Θ n u σ h₃⟩
  | b, .fam L, Θ, n, _, _, hs => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := hs
      exact ⟨l, c, h₁, h₂, sepRange_mono' (fun m σ hm => h b L Θ n _ σ hm) h₃⟩
  | _, .bang T, Θ, n, v, ρ, hs => ⟨hs.1, h true T Θ n v ρ hs.2⟩
  | _, .imm _ T, Θ, n, _, _, hs => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs', h₁, h₂, h₃, h₄⟩, hw⟩ := hs
      exact ⟨α, hα, ⟨l, s, u, σ, hs', h₁, h₂, h₃, h false T Θ n u σ h₄⟩, hw⟩
  | _, .mut _ T, _, _, _, _, hs => ⟨hs.1, fun Θ' j u σ hu => h true T Θ' j u σ (hs.2 Θ' j u σ hu)⟩
  | _, .unk, _, _, _, _, hs => hs
  | _, .tvar _, _, _, _, _, hs => hs
  | b, .mu _, Θ, n, v, ρ, hs => ⟨hs.1, hs.2.1, h b _ Θ n v ρ hs.2.2⟩

/-- **Induction on the least fixed points, at every type, in both modes** (Core's `vC_ind`). A
property of the relation closed under one unfolding of every clause (`vFN` with the relation
and the property at the positions it recurses to, the unrolling at `μ`) holds of the relation. -/
theorem vN_ind (δ : LSub) (Φ : Bool → VTy → LocTy → Nat → Val → WRes → Prop)
    (h : ∀ b T Θ n v ρ, vFN (ℍ := ℍ)
      (fun b T Θ n v ρ => vBN (ℍ := ℍ) none b T δ Θ n v ρ ∧ Φ b T Θ n v ρ) δ b T Θ n v ρ →
      Φ b T Θ n v ρ) :
    ∀ b T Θ n v ρ, vBN (ℍ := ℍ) none b T δ Θ n v ρ → Φ b T Θ n v ρ := by
  let G : Bool → VTy → LocTy → Nat → Val → WRes → Prop :=
    fun b T Θ n v ρ => vBN (ℍ := ℍ) none b T δ Θ n v ρ ∧ Φ b T Θ n v ρ
  have hG : ∀ b T Θ n v ρ, vFN (ℍ := ℍ) G δ b T Θ n v ρ → G b T Θ n v ρ := fun b T Θ n v ρ hs =>
    ⟨(vFN_vN δ b T Θ n v ρ).mpr (vFN_mono (fun _ _ _ _ _ _ h => h.1) δ b T Θ n v ρ hs),
      h b T Θ n v ρ hs⟩
  have gen : ∀ (A : VTy) (η₀ : Nat → TEntN) (σ : Nat → VTy), (∀ n, (η₀ n).ty = σ n) →
      (∀ n b Θ k v r, (η₀ n).P b Θ k v r → G b (σ n) Θ k v r) →
      (∀ n, ¬ A.NoMut n → (η₀ n).P = fun b => vBN (ℍ := ℍ) none b (σ n) δ) →
      ∀ b Θ k v r, vBN (ℍ := ℍ) (some η₀) b A δ Θ k v r → G b (A.subst σ) Θ k v r := by
    intro A
    induction A using VTy.recV with
    | unit => intro _ _ _ _ _ b Θ k v r hr; exact hG b _ Θ k v r (by cases b <;> exact hr)
    | int w => intro _ _ _ _ _ b Θ k v r hr; exact hG b _ Θ k v r (by cases b <;> exact hr)
    | opq _ => intro _ _ _ _ _ b Θ k v r hr; exact hG b _ Θ k v r (by cases b <;> exact hr)
    | unk => intro _ _ _ _ _ b Θ k v r hr; exact hG b _ Θ k v r (by cases b <;> exact hr)
    | zero => intro _ _ _ _ _ b _ _ _ _ hr; cases b <;> exact hr.elim
    | thunk _ => intro _ _ _ _ _ b Θ k v r hr; exact hG b _ Θ k v r (by cases b <;> exact hr)
    | tensor A B ihA ihB =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have hr' : ∃ v₁ v₂ ρ₁ ρ₂, v = Val.pair v₁ v₂ ∧ ResU.CompS ρ₁ ρ₂ r ∧
            vBN (ℍ := ℍ) (some η₀) b A δ Θ k v₁ ρ₁ ∧ vBN (ℍ := ℍ) (some η₀) b B δ Θ k v₂ ρ₂ := by
          cases b <;> exact hr
        obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := hr'
        exact hG b _ Θ k v r ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂,
          ihA η₀ σ ht hP (fun n hn => hex n (fun h => hn h.1)) b Θ k v₁ ρ₁ h₃,
          ihB η₀ σ ht hP (fun n hn => hex n (fun h => hn h.2)) b Θ k v₂ ρ₂ h₄⟩
    | sum A B ihA ihB =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have hr' : (∃ v₁, v = Val.inj₁ v₁ ∧ vBN (ℍ := ℍ) (some η₀) b A δ Θ k v₁ r) ∨
            (∃ v₂, v = Val.inj₂ v₂ ∧ vBN (ℍ := ℍ) (some η₀) b B δ Θ k v₂ r) := by
          cases b <;> exact hr
        rcases hr' with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
        · exact hG b _ Θ k v r (.inl ⟨v₁, h₁,
            ihA η₀ σ ht hP (fun n hn => hex n (fun h => hn h.1)) b Θ k v₁ r h₂⟩)
        · exact hG b _ Θ k v r (.inr ⟨v₂, h₁,
            ihB η₀ σ ht hP (fun n hn => hex n (fun h => hn h.2)) b Θ k v₂ r h₂⟩)
    | ref A ih =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have hr' : ∃ (l : Loc) (u : Val) (σ' : WRes), v = Val.loc l ∧
            ResU.CompS (ResU.single l (CellU.ownOf u)) σ' r ∧
              vBN (ℍ := ℍ) (some η₀) b A δ Θ k u σ' := by
          cases b <;> exact hr
        obtain ⟨l, u, σ', h₁, h₂, h₃⟩ := hr'
        exact hG b _ Θ k v r ⟨l, u, σ', h₁, h₂, ih η₀ σ ht hP hex b Θ k u σ' h₃⟩
    | fam L ih =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have hr' : ∃ (l : Loc) (c : UInt32), v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
            sepRange (fun m => vBN (ℍ := ℍ) (some η₀) b L δ Θ k (Val.loc m)) l c.toNat r := by
          cases b <;> exact hr
        obtain ⟨l, c, h₁, h₂, h₃⟩ := hr'
        exact hG b _ Θ k v r ⟨l, c, h₁, h₂,
          sepRange_mono' (fun m σ' hm => ih η₀ σ ht hP hex b Θ k _ σ' hm) h₃⟩
    | imm a A ih =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have e : tCloseN (some η₀) A = A.subst σ := by
          simp only [tCloseN]; congr 1; funext n; exact ht n
        have hr' : ∃ α, a.interp δ = some α ∧
            immCell α (fun u σ' => vOE (ℍ := ℍ) (some η₀) A δ Θ k u σ') v r ∧
              ∀ l s u σ' h, r = ResU.single l (CellU.immOf s u σ' h) →
                ImmWitW Θ.imm l s (tCloseN (some η₀) A) δ := by
          cases b <;> exact hr
        obtain ⟨α, hα, ⟨l, s, u, σ', hs, h₁, h₂, h₃, h₄⟩, hw⟩ := hr'
        rw [e] at hw
        exact hG b _ Θ k v r ⟨α, hα, ⟨l, s, u, σ', hs, h₁, h₂, h₃,
          ih η₀ σ ht hP hex false Θ k u σ' h₄⟩, hw⟩
    | «mut» a A ih =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have hmut : vNE (ℍ := ℍ) (some η₀) A δ = vNE (ℍ := ℍ) none (A.subst σ) δ := by
          have h₁ := vBN_subst (ℍ := ℍ) A (tEnvN none) σ δ true
          have h₂ := vBN_some (ℍ := ℍ) none (A.subst σ) true
          refine Eq.trans ?_ ((congrFun h₂ δ).trans h₁).symm
          refine congrFun (vBN_congr_occ A _ _ (fun n hn => ?_) true) δ
          refine TEntN.ext' ((ht n).trans (VTy.subst_id _).symm) ?_
          rw [hex n (fun h => h hn)]
          funext b''
          exact congrFun (vBN_some (ℍ := ℍ) none (σ n) b'') δ
        have hr' : vBN (ℍ := ℍ) none b (.mut a (A.subst σ)) δ Θ k v r := by
          cases b <;>
          · obtain ⟨α, hα, b', hab, hm, hu⟩ := hr
            refine ⟨α, hα, b', hab, ?_, fun Θ' j u σ' h' => hu Θ' j u σ' (hmut ▸ h')⟩
            rw [← hmut]; exact hm
        refine hG b _ Θ k v r ⟨hr', fun Θ' j u σ' hu => ?_⟩
        replace hu : vNE (ℍ := ℍ) (some η₀) A δ Θ' j u σ' := by rw [hmut]; exact hu
        exact ih η₀ σ ht hP (fun n hn => hex n (fun h => hn (VTy.noMut_of_not_occ A h)))
          true Θ' j u σ' hu
    | box a A ih =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have hr' : ∃ α, a.interp δ = some α ∧ vBN (ℍ := ℍ) (some η₀) b A δ Θ k v r ∧
            r.InStratum α := by
          cases b <;> exact hr
        obtain ⟨α, hα, h₁, h₂⟩ := hr'
        exact hG b _ Θ k v r ⟨α, hα, ih η₀ σ ht hP hex b Θ k v r h₁, h₂⟩
    | bang A ih =>
        intro η₀ σ ht hP hex b Θ k v r hr
        have hr' : r = PMap.empty ∧ vBN (ℍ := ℍ) (some η₀) true A δ Θ k v r := by
          cases b <;> exact hr
        exact hG b _ Θ k v r ⟨hr'.1, ih η₀ σ ht hP hex true Θ k v r hr'.2⟩
    | tvar n =>
        intro η₀ σ _ hP _ b Θ k v r hr
        exact hP n b Θ k v r (by cases b <;> exact hr)
    | mu B ih =>
        intro η₀ σ ht hP hex b Θ k v r hr
        obtain ⟨hnm, hcl, hlfp⟩ := vBN_mu.mp hr
        have hM : tCloseN (some η₀) (.mu B) = (VTy.mu B).subst σ := by
          simp only [tCloseN]; congr 1; funext n; exact ht n
        rw [hM] at hcl
        refine hlfp (fun b Θ k v r => G b ((VTy.mu B).subst σ) Θ k v r) (fun b' Θ' k' v' r' h' => ?_)
          
        have hB := ih (VTy.scons ⟨tCloseN (some η₀) (.mu B),
            fun b Θ k v r => G b ((VTy.mu B).subst σ) Θ k v r⟩ η₀)
          (VTy.scons ((VTy.mu B).subst σ) σ)
          (fun n => by cases n with
            | zero => exact hM
            | succ n => exact ht n)
          (fun n => by cases n with
            | zero => exact fun _ _ _ _ _ h => h
            | succ n => exact hP n)
          (fun n hn => by cases n with
            | zero => exact absurd hnm hn
            | succ n => exact hex n hn) b' Θ' k' v' r' h'
        rw [VTy.subst_scons_eq_inst] at hB
        exact hG _ _ _ _ _ _ ⟨(VTy.noMut_upS_iff B σ).mpr hnm, hcl, hB⟩
  intro b T Θ n v ρ hT
  rw [vBN_some none] at hT
  have := gen T (tEnvN none) .tvar (fun _ => rfl) (fun _ _ _ _ _ _ h => h.elim)
    (fun _ _ => by funext b; cases b <;> rfl)
    b Θ n v ρ hT
  rw [VTy.subst_id] at this
  exact this.2




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

/-- `μ` down the index, from the body's law at every downward-closed environment: the least
fixed point lies in `{x | every lower index of x is in the candidate}`. -/
theorem vBN_mu_down {η : Option (Nat → TEntN)} {A : VTy} {δ : LSub} {b : Bool} {Θ : LocTy}
    {n : Nat} {v : Val} {ρ : WRes} (hη : EnvDownN η)
    (ih : ∀ η', EnvDownN η' → ∀ b' Θ' k u r,
      vBN (ℍ := ℍ) η' b' A δ Θ' (k + 1) u r → vBN (ℍ := ℍ) η' b' A δ Θ' k u r)
    (h : vBN (ℍ := ℍ) η b (.mu A) δ Θ (n + 1) v ρ) : vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ := by
  obtain ⟨hA, hc, hl⟩ := vBN_mu.mp h
  refine vBN_mu.mpr ⟨hA, hc, fun P hP => ?_⟩
  let Q : Bool → LocTy → Nat → Val → WRes → Prop := fun b Θ' k u r => ∀ j ≤ k, P b Θ' j u r
  have hd : EnvDownN (muEnvN η A Q) := fun m b' Θ' k u r h' => by
    cases m with
    | zero => exact fun j hj => h' j (Nat.le_succ_of_le hj)
    | succ m => exact hη m b' Θ' k u r h'
  have hQ : MuClosedN (ℍ := ℍ) η A δ Q := by
    intro b' Θ' k u r hb j hj
    have hb' : vBN (ℍ := ℍ) (muEnvN η A Q) b' A δ Θ' j u r :=
      down_iter (F := fun i => vBN (ℍ := ℍ) (muEnvN η A Q) b' A δ Θ' i u r)
        (fun i hi => ih _ hd b' Θ' i u r hi) hj hb
    refine hP b' Θ' j u r (vBN_mono_at A 0 (VTy.scons ⟨tCloseN η (.mu A), Q⟩ (tEnvN η))
      (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η)) hA (fun m => by cases m <;> rfl) (fun m hm => ?_)
      (fun b'' Θ'' i v'' ρ'' hq => hq i le_rfl) b' δ Θ' j u r hb')
    cases m with
    | zero => exact absurd rfl hm
    | succ m => rfl
  exact hl Q hQ n (Nat.le_succ n)

mutual
theorem vNE_down : ∀ (A : VTy) (η : Option (Nat → TEntN)), EnvDownN η → ∀ (δ : LSub) (Θ : LocTy)
    (n : Nat) (v : Val) (ρ : WRes),
    vNE (ℍ := ℍ) η A δ Θ (n + 1) v ρ → vNE (ℍ := ℍ) η A δ Θ n v ρ
  | .unit, η, hη, _, _, _, _, _, h => h
  | .tensor A B, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vNE_down A η hη δ Θ n v₁ ρ₁ h₃, vNE_down B η hη δ Θ n v₂ ρ₂ h₄⟩
  | .zero, η, hη, _, _, _, _, _, h => h
  | .sum A B, η, hη, δ, Θ, n, _, ρ, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vNE_down A η hη δ Θ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, vNE_down B η hη δ Θ n v₂ ρ h₂⟩
  | .thunk C, η, hη, δ, Θ, n, v, ρ, h => fun Θ' hE hOK c hc ls =>
      cN_down C δ Θ' hOK.1 c n ls _ ρ (h Θ' hE hOK c hc ls)
  | .ref A, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vNE_down A η hη δ Θ n u σ h₃⟩
  | .imm a A, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
      exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, vOE_down A η hη δ Θ n u σ h₄⟩, hw⟩
  | .mut a A, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩, hu⟩ := h
      exact ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩, hu⟩
  | .box a A, η, hη, δ, Θ, n, v, ρ, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vNE_down A η hη δ Θ n v ρ h₁, h₂⟩
  | .bang A, η, hη, δ, Θ, n, v, ρ, h => ⟨h.1, vNE_down A η hη δ Θ n v ρ h.2⟩
  | .unk, η, hη, _, _, _, _, _, h => h
  | .int _, η, hη, _, _, _, _, _, h => h
  | .tvar m, η, hη, δ, Θ, n, v, ρ, h => by
      cases η with
      | none => exact h
      | some η => exact hη m true Θ n v ρ h
  | .mu A, η, hη, δ, Θ, n, v, ρ, h => vBN_mu_down (b := true) hη (fun η' hη' b' Θ' k u r h' => by
      cases b'
      · exact vOE_down A η' hη' δ Θ' k u r h'
      · exact vNE_down A η' hη' δ Θ' k u r h') h
  | .fam L, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono' (fun m σ hm => vNE_down L η hη δ Θ n (Val.loc m) σ hm) h₃⟩
  | .opq _, η, hη, _, _, _, _, _, h => h
theorem vOE_down : ∀ (A : VTy) (η : Option (Nat → TEntN)), EnvDownN η → ∀ (δ : LSub) (Θ : LocTy)
    (n : Nat) (v : Val) (ρ : WRes),
    vOE (ℍ := ℍ) η A δ Θ (n + 1) v ρ → vOE (ℍ := ℍ) η A δ Θ n v ρ
  | .unit, η, hη, _, _, _, _, _, h => h
  | .tensor A B, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vOE_down A η hη δ Θ n v₁ ρ₁ h₃, vOE_down B η hη δ Θ n v₂ ρ₂ h₄⟩
  | .zero, η, hη, _, _, _, _, _, h => h
  | .sum A B, η, hη, δ, Θ, n, _, ρ, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vOE_down A η hη δ Θ n v₁ ρ h₂⟩
      · exact .inr ⟨v₂, h₁, vOE_down B η hη δ Θ n v₂ ρ h₂⟩
  | .thunk _, η, hη, _, _, _, _, _, _ => trivial
  | .ref A, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vOE_down A η hη δ Θ n u σ h₃⟩
  | .imm a A, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, h₄⟩, hw⟩ := h
      exact ⟨α, hα, ⟨l, s, u, σ, hs, h₁, h₂, h₃, vOE_down A η hη δ Θ n u σ h₄⟩, hw⟩
  | .mut a A, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, hj, h₁, h₂, h₃⟩, hu⟩ := h
      exact ⟨α, hα, b, hab, ⟨l, w, χ, hχ, j, hw, by omega, h₁, h₂, h₃⟩, hu⟩
  | .box a A, η, hη, δ, Θ, n, v, ρ, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vOE_down A η hη δ Θ n v ρ h₁, h₂⟩
  | .bang A, η, hη, δ, Θ, n, v, ρ, h => ⟨h.1, vNE_down A η hη δ Θ n v ρ h.2⟩
  | .unk, η, hη, _, _, _, _, _, h => h
  | .int _, η, hη, _, _, _, _, _, h => h
  | .tvar m, η, hη, δ, Θ, n, v, ρ, h => by
      cases η with
      | none => exact h
      | some η => exact hη m false Θ n v ρ h
  | .mu A, η, hη, δ, Θ, n, v, ρ, h => vBN_mu_down (b := false) hη (fun η' hη' b' Θ' k u r h' => by
      cases b'
      · exact vOE_down A η' hη' δ Θ' k u r h'
      · exact vNE_down A η' hη' δ Θ' k u r h') h
  | .fam L, η, hη, δ, Θ, n, _, _, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono' (fun m σ hm => vOE_down L η hη δ Θ n (Val.loc m) σ hm) h₃⟩
  | .opq _, η, hη, _, _, _, _, _, h => h
theorem cN_down : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes),
    cN (ℍ := ℍ) C δ Θ c (n + 1) ls e ρ → cN (ℍ := ℍ) C δ Θ c n ls e ρ
  | .ret A, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      erwp_le (LocTy.view_down hΘ c) (opTableN_local _) (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vNE_down A none envDownN_none δ Θ k v ρ h) (Nat.le_succ n) h
  | .arr A C, δ, Θ, hΘ, c, n, ls, e, ρ, h => fun c' k hk => h c' k (by omega)
  | .amp C D, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      ⟨cN_down C δ Θ hΘ c n ls _ ρ h.1, cN_down D δ Θ hΘ c n ls _ ρ h.2⟩
  | .top, _, _, _, _, _, _, _, _, h => h
  | .all x c' C, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      fun α hα => cN_down C (δ.extend x α) Θ hΘ c n ls _ ρ (h α hα)
  | .nu _, _, _, _, _, _, _, _, _, h => h
  | .eff m i q A B fin rc C, δ, Θ, hΘ, c, n, ls, e, ρ, h =>
      erwp_le (LocTy.view_down hΘ c) (opTableN_local _)
        (opTableN_down (extTabN_down (fun k v ρ h => vNE_down A none envDownN_none δ Θ k v ρ h)
          (finN_down fin δ Θ hΘ c) (tabN_down C δ Θ hΘ c)))
        (fun k _ v ρ h => retN_down C δ Θ k v ρ h) (Nat.le_succ n) h
theorem tabN_down : ∀ (C : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life),
    (tabN (ℍ := ℍ) C δ Θ c).Down
  | .eff m i q A B fin rc C, δ, Θ, hΘ, c =>
      extTabN_down (fun k v ρ h => vNE_down A none envDownN_none δ Θ k v ρ h) (finN_down fin δ Θ hΘ c)
        (tabN_down C δ Θ hΘ c)
  | .ret _, _, _, _, _ => OpTabN.empty_down
  | .arr _ _, _, _, _, _ => OpTabN.empty_down
  | .amp _ _, _, _, _, _ => OpTabN.empty_down
  | .top, _, _, _, _ => OpTabN.empty_down
  | .all _ _ _, _, _, _, _ => OpTabN.empty_down
  | .nu _, _, _, _, _ => OpTabN.empty_down
theorem finN_down : ∀ (F : CTy) (δ : LSub) (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life),
    ∀ P, finN (ℍ := ℍ) F δ Θ c = some P → ∀ k ls e ρ, P (k + 1) ls e ρ → P k ls e ρ
  | .top, _, _, _, _, _, h => by cases h
  | .eff m i q A B fin rc C, δ, Θ, hΘ, c, P, h => by
      simp only [finN, Option.some.injEq] at h
      subst h
      exact cancelOblN_down (LocTy.view_down hΘ c)
        (extTabN_down (fun k v ρ h => vNE_down A none envDownN_none δ Θ k v ρ h)
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
theorem retN_down : ∀ (C : CTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes),
    retN (ℍ := ℍ) C δ Θ (n + 1) v ρ → retN (ℍ := ℍ) C δ Θ n v ρ
  | .ret A, δ, Θ, n, v, ρ, h => vNE_down A none envDownN_none δ Θ n v ρ h
  | .eff _ _ _ _ _ _ _ C, δ, Θ, n, v, ρ, h => retN_down C δ Θ n v ρ h
  | .arr _ _, _, _, _, _, _, h => h
  | .amp _ _, _, _, _, _, _, h => h
  | .top, _, _, _, _, _, h => h
  | .all _ _ _, _, _, _, _, _, h => h
  | .nu _, _, _, _, _, _, h => h
end

theorem vN_down (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes)
    (h : vN (ℍ := ℍ) A δ Θ (n + 1) v ρ) : vN (ℍ := ℍ) A δ Θ n v ρ :=
  vNE_down A none envDownN_none δ Θ n v ρ h

theorem vO_down (A : VTy) (δ : LSub) (Θ : LocTy) (n : Nat) (v : Val) (ρ : WRes)
    (h : vO (ℍ := ℍ) A δ Θ (n + 1) v ρ) : vO (ℍ := ℍ) A δ Θ n v ρ :=
  vOE_down A none envDownN_none δ Θ n v ρ h

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

mutual
theorem vNE_congr : ∀ (A : VTy) (η : Option (Nat → TEntN)) {δ δ' : LSub},
    (∀ y, VFree y A → δ.find? y = δ'.find? y) → EnvAgreeN η δ δ' →
    vNE (ℍ := ℍ) η A δ = vNE (ℍ := ℍ) η A δ'
  | .unit, _, _, _, _, _ => rfl
  | .tensor A B, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hη
      have h₂ := vNE_congr B η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      funext Θ n v ρ; simp only [vNE, h₁, h₂]
  | .zero, _, _, _, _, _ => rfl
  | .sum A B, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hη
      have h₂ := vNE_congr B η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      funext Θ n v ρ; simp only [vNE, h₁, h₂]
  | .thunk C, η, δ, δ', h, hη => by
      have h₁ := cN_congr C (δ := δ) (δ' := δ') h
      funext Θ n v ρ; simp only [vNE, h₁]
  | .ref A, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') h hη
      funext Θ n v ρ; simp only [vNE, h₁]
  | .imm a A, η, δ, δ', h, hη => by
      have h₁ := vOE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      have hw := immWitW_congr (A := tCloseN η A) (δ := δ) (δ' := δ')
        (envAgreeN_tClose hη (fun y hy => h y (.inr hy)))
      funext Θ n v ρ; simp only [vNE, h₁, ha, hw]
  | .mut a A, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vNE, ha, h₁]
  | .box a A, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vNE, h₁, ha]
  | .bang A, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') h hη
      funext Θ n v ρ; simp only [vNE, h₁]
  | .unk, _, _, _, _, _ => rfl
  | .int _, _, _, _, _, _ => rfl
  | .tvar _, _, _, _, _, _ => rfl
  | .mu A, η, δ, δ', h, hη => by
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN (ℍ := ℍ) (muEnvN η A P) b' A δ' := by
        intro P b'
        have hη' : EnvAgreeN (muEnvN η A P) δ δ' := fun n y hy => by
          cases n with
          | zero => exact envAgreeN_tClose hη (A := .mu A) h y hy
          | succ n => exact hη n y hy
        cases b'
        · exact vOE_congr A _ h hη'
        · exact vNE_congr A _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu (b := true)).trans (Iff.trans (and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun P => imp_congr (by unfold MuClosedN; simp only [hb]) Iff.rfl)))
        (vBN_mu (b := true)).symm))
  | .fam L, η, δ, δ', h, hη => by
      have h₁ := vNE_congr L η (δ := δ) (δ' := δ') h hη
      funext Θ n v ρ; simp only [vNE, h₁]
  | .opq _, _, _, _, _, _ => rfl
theorem vOE_congr : ∀ (A : VTy) (η : Option (Nat → TEntN)) {δ δ' : LSub},
    (∀ y, VFree y A → δ.find? y = δ'.find? y) → EnvAgreeN η δ δ' →
    vOE (ℍ := ℍ) η A δ = vOE (ℍ := ℍ) η A δ'
  | .unit, _, _, _, _, _ => rfl
  | .tensor A B, η, δ, δ', h, hη => by
      have h₁ := vOE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hη
      have h₂ := vOE_congr B η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      funext Θ n v ρ; simp only [vOE, h₁, h₂]
  | .zero, _, _, _, _, _ => rfl
  | .sum A B, η, δ, δ', h, hη => by
      have h₁ := vOE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) hη
      have h₂ := vOE_congr B η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      funext Θ n v ρ; simp only [vOE, h₁, h₂]
  | .thunk _, _, _, _, _, _ => rfl
  | .ref A, η, δ, δ', h, hη => by
      have h₁ := vOE_congr A η (δ := δ) (δ' := δ') h hη
      funext Θ n v ρ; simp only [vOE, h₁]
  | .imm a A, η, δ, δ', h, hη => by
      have h₁ := vOE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      have hw := immWitW_congr (A := tCloseN η A) (δ := δ) (δ' := δ')
        (envAgreeN_tClose hη (fun y hy => h y (.inr hy)))
      funext Θ n v ρ; simp only [vOE, h₁, ha, hw]
  | .mut a A, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vOE, ha, h₁]
  | .box a A, η, δ, δ', h, hη => by
      have h₁ := vOE_congr A η (δ := δ) (δ' := δ') (fun y hy => h y (.inr hy)) hη
      have ha := BoCa.Fig16.LogRel.interp_congr (δ₁ := δ) (δ₂ := δ') a (fun y hy => h y (.inl hy))
      funext Θ n v ρ; simp only [vOE, h₁, ha]
  | .bang A, η, δ, δ', h, hη => by
      have h₁ := vNE_congr A η (δ := δ) (δ' := δ') h hη
      funext Θ n v ρ; simp only [vOE, h₁]
  | .unk, _, _, _, _, _ => rfl
  | .int _, _, _, _, _, _ => rfl
  | .tvar _, _, _, _, _, _ => rfl
  | .mu A, η, δ, δ', h, hη => by
      have hb : ∀ P b', vBN (ℍ := ℍ) (muEnvN η A P) b' A δ = vBN (ℍ := ℍ) (muEnvN η A P) b' A δ' := by
        intro P b'
        have hη' : EnvAgreeN (muEnvN η A P) δ δ' := fun n y hy => by
          cases n with
          | zero => exact envAgreeN_tClose hη (A := .mu A) h y hy
          | succ n => exact hη n y hy
        cases b'
        · exact vOE_congr A _ h hη'
        · exact vNE_congr A _ h hη'
      funext Θ n v ρ
      exact propext ((vBN_mu (b := false)).trans (Iff.trans (and_congr Iff.rfl (and_congr Iff.rfl
        (forall_congr' fun P => imp_congr (by unfold MuClosedN; simp only [hb]) Iff.rfl)))
        (vBN_mu (b := false)).symm))
  | .fam L, η, δ, δ', h, hη => by
      have h₁ := vOE_congr L η (δ := δ) (δ' := δ') h hη
      funext Θ n v ρ; simp only [vOE, h₁]
  | .opq _, _, _, _, _, _ => rfl
theorem cN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    cN (ℍ := ℍ) C δ = cN (ℍ := ℍ) C δ'
  | .ret A, δ, δ', h => by
      have h₁ := vNE_congr A none (δ := δ) (δ' := δ') h (envAgreeN_none _ _)
      funext Θ c n ls e ρ; simp only [cN, h₁]
  | .arr A C, δ, δ', h => by
      have h₁ := vNE_congr A none (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) (envAgreeN_none _ _)
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
  | .nu _, _, _, _ => rfl
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vNE_congr A none (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) (envAgreeN_none _ _)
      have h₂ := vNE_congr B none (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy))) (envAgreeN_none _ _)
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      have h₅ := retN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ c n ls e ρ; simp only [cN, h₁, h₂, h₃, h₄, h₅]
theorem tabN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    tabN (ℍ := ℍ) C δ = tabN (ℍ := ℍ) C δ'
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vNE_congr A none (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) (envAgreeN_none _ _)
      have h₂ := vNE_congr B none (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy))) (envAgreeN_none _ _)
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ c; simp only [tabN, h₁, h₂, h₃, h₄]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
theorem finN_congr : ∀ (F : CTy) {δ δ' : LSub}, (∀ y, CFree y F → δ.find? y = δ'.find? y) →
    finN (ℍ := ℍ) F δ = finN (ℍ := ℍ) F δ'
  | .eff m i q A B fin rc C, δ, δ', h => by
      have h₁ := vNE_congr A none (δ := δ) (δ' := δ') (fun y hy => h y (.inl hy)) (envAgreeN_none _ _)
      have h₂ := vNE_congr B none (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inl hy))) (envAgreeN_none _ _)
      have h₃ := finN_congr fin (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inl hy))))
      have h₄ := tabN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ c; simp only [finN, h₁, h₂, h₃, h₄]
  | .ret _, _, _, _ => rfl
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
theorem retN_congr : ∀ (C : CTy) {δ δ' : LSub}, (∀ y, CFree y C → δ.find? y = δ'.find? y) →
    retN (ℍ := ℍ) C δ = retN (ℍ := ℍ) C δ'
  | .ret A, δ, δ', h => by
      have h₁ := vNE_congr A none (δ := δ) (δ' := δ') h (envAgreeN_none _ _)
      funext Θ n v ρ; simp only [retN, h₁]
  | .eff _ _ _ _ _ _ _ C, δ, δ', h => by
      have h₁ := retN_congr C (δ := δ) (δ' := δ') (fun y hy => h y (.inr (.inr (.inr hy))))
      funext Θ n v ρ; simp only [retN, h₁]
  | .arr _ _, _, _, _ => rfl
  | .amp _ _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .all _ _ _, _, _, _ => rfl
  | .nu _, _, _, _ => rfl
end

/-- A value along an equation of the relations at two types (or two substitutions). -/
theorem vN_cast {A A' : VTy} {δ δ' : LSub} (h : vN (ℍ := ℍ) A' δ' = vN (ℍ := ℍ) A δ) {Θ : LocTy}
    {j : Nat} {u : Val} {r : WRes} (hv : vN (ℍ := ℍ) A' δ' Θ j u r) : vN (ℍ := ℍ) A δ Θ j u r :=
  h ▸ hv

theorem vN_congr (A : VTy) {δ δ' : LSub} (h : ∀ y, VFree y A → δ.find? y = δ'.find? y) :
    vN (ℍ := ℍ) A δ = vN (ℍ := ℍ) A δ' :=
  vNE_congr A none h (envAgreeN_none _ _)

theorem vO_congr (A : VTy) {δ δ' : LSub} (h : ∀ y, VFree y A → δ.find? y = δ'.find? y) :
    vO (ℍ := ℍ) A δ = vO (ℍ := ℍ) A δ' :=
  vOE_congr A none h (envAgreeN_none _ _)

/-- Extending `δ` at a variable `A` does not mention leaves `𝒱⟦A⟧` alone. -/
theorem vN_extend_of_not_free {x : LifeVar} {A : VTy} (h : ¬ VFree x A) (δ : LSub) (α : Life) :
    vN (ℍ := ℍ) A (δ.extend x α) = vN (ℍ := ℍ) A δ :=
  vN_congr A fun y hy => BoCa.Fig16.LogRel.find?_extend_ne δ α (fun e => by subst e; exact h hy)

/-! ### Outliving types lie in the stratum -/

/-- **`Δ ⊢ A ⊐ @a`: `𝒱⟦A⟧` lies in `Res_α`, `α = @aδ`** (Core's `vC_outlives`), at every
world. -/
theorem vNE_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life} (hδ : Δ.Models δ)
    (ha : a.interp δ = some α) {T : VTy} (hT : VOutlives Δ a T) :
    ∀ {η : Option (Nat → TEntN)}, (∀ m Θ k v ρ, (tEnvN η m).P true Θ k v ρ → ρ.InStratum α) →
    ∀ Θ n v ρ, vNE (ℍ := ℍ) η T δ Θ n v ρ → ρ.InStratum α := by
  induction hT with
  | unit => rintro η hη Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty α
  | tensor _ _ ih₁ ih₂ =>
      rintro η hη Θ n v ρ ⟨v₁, v₂, ρ₁, ρ₂, -, hc, h₁, h₂⟩
      exact inStratum_compS hc (ih₁ hη Θ n v₁ ρ₁ h₁) (ih₂ hη Θ n v₂ ρ₂ h₂)
  | zero => intro η hη Θ n v ρ h; exact h.elim
  | sum _ _ ih₁ ih₂ =>
      rintro η hη Θ n v ρ (⟨v₁, -, h₁⟩ | ⟨v₂, -, h₂⟩)
      · exact ih₁ hη Θ n v₁ ρ h₁
      · exact ih₂ hη Θ n v₂ ρ h₂
  | ref _ ih =>
      rintro η hη Θ n v ρ ⟨l, u, σ, -, hc, h⟩
      exact inStratum_compS hc (ResU.inStratum_single_own α l u) (ih hη Θ n u σ h)
  | bang => rintro η hη Θ n v ρ ⟨rfl, -⟩; exact ResU.inStratum_empty α
  | box hle =>
      rintro η hη Θ n v ρ ⟨β, hb, -, ho⟩
      obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ho.mono (show (α : Life) ≤ β from hle')
  | imm hlt =>
      rintro η hη Θ n v ρ ⟨β, hb, ⟨l, s, u, σ, hs, -, rfl, hle, -⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l (lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | «mut» hlt =>
      rintro η hη Θ n v ρ ⟨β, hb, b, hβb, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l (lt_of_lt_of_le (show (α : Life) < β from hlt') hβb)
  | tvar =>
      intro η hη Θ n v ρ h
      cases η with
      | none => exact h.elim
      | some η => exact hη _ Θ n v ρ h
  | mu _ ih =>
      intro η hη Θ n v ρ h
      obtain ⟨-, -, hl⟩ := vBN_mu (b := true) |>.mp h
      refine hl (fun b _ _ _ r => b = true → r.InStratum α) ?_ rfl
      intro b Θ' k u r hb e
      subst e
      exact ih (η := muEnvN η _ _) (fun m Θ'' k' v' ρ' h' => by
        cases m with
        | zero => exact h' rfl
        | succ m => exact hη m Θ'' k' v' ρ' h') Θ' k u r hb
  | int => rintro η hη Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty α
  | opq =>
      intro η hη Θ n v ρ h
      rcases Opaque.rel_cases h with ⟨-, rfl, -⟩ | ⟨-, l, -, rfl⟩
      · exact ResU.inStratum_empty α
      · exact ResU.inStratum_single_own α l _
  | fam _ ih =>
      rintro η hη Θ n v ρ ⟨l, c, -, -, hs⟩
      exact sepRange_closed (R := fun σ => σ.InStratum α) (ResU.inStratum_empty α)
        (fun _ _ _ hc o₁ o₂ => inStratum_compS hc o₁ o₂) (fun m σ hm => ih hη Θ n _ σ hm) hs

theorem vN_outlives {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life} (hδ : Δ.Models δ)
    (ha : a.interp δ = some α) {T : VTy} (hT : VOutlives Δ a T) :
    ∀ Θ n v ρ, vN (ℍ := ℍ) T δ Θ n v ρ → ρ.InStratum α :=
  vNE_outlives hδ ha hT (η := none) (fun _ _ _ _ _ h => h.elim)

/-- **`Δ ⊢ A ⊒ @a`: `𝒱⟦A⟧` lies in every stratum strictly below `α = @aδ`** (Core's
`vC_outlivesLe`, `[TR]` 6.60 at the non-strict side condition), at every world. -/
theorem vNE_outlivesLe {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α γ : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) (hγ : γ < α) {T : VTy}
    (hT : VOutlivesLe Δ a T) :
    ∀ {η : Option (Nat → TEntN)}, (∀ m Θ k v ρ, (tEnvN η m).P true Θ k v ρ → ρ.InStratum γ) →
    ∀ Θ n v ρ, vNE (ℍ := ℍ) η T δ Θ n v ρ → ρ.InStratum γ := by
  induction hT with
  | unit => rintro η hη Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty γ
  | tensor _ _ ih₁ ih₂ =>
      rintro η hη Θ n v ρ ⟨v₁, v₂, ρ₁, ρ₂, -, hc, h₁, h₂⟩
      exact inStratum_compS hc (ih₁ hη Θ n v₁ ρ₁ h₁) (ih₂ hη Θ n v₂ ρ₂ h₂)
  | zero => intro η hη Θ n v ρ h; exact h.elim
  | sum _ _ ih₁ ih₂ =>
      rintro η hη Θ n v ρ (⟨v₁, -, h₁⟩ | ⟨v₂, -, h₂⟩)
      · exact ih₁ hη Θ n v₁ ρ h₁
      · exact ih₂ hη Θ n v₂ ρ h₂
  | ref _ ih =>
      rintro η hη Θ n v ρ ⟨l, u, σ, -, hc, h⟩
      exact inStratum_compS hc (ResU.inStratum_single_own γ l u) (ih hη Θ n u σ h)
  | bang => rintro η hη Θ n v ρ ⟨rfl, -⟩; exact ResU.inStratum_empty γ
  | box hle =>
      rintro η hη Θ n v ρ ⟨β, hb, -, ho⟩
      obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ho.mono (le_trans hγ.le (show (α : Life) ≤ β from hle'))
  | imm hlt =>
      rintro η hη Θ n v ρ ⟨β, hb, ⟨l, s, u, σ, hs, -, rfl, hle, -⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l (lt_of_lt_of_le (lt_of_lt_of_le hγ (show (α : Life) ≤ β from hlt')) hle)
  | «mut» hlt =>
      rintro η hη Θ n v ρ ⟨β, hb, b, hβb, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩
      obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact ResU.inStratum_single l
        (lt_of_lt_of_le hγ ((show (α : Life) ≤ β from hlt').trans hβb))
  | tvar =>
      intro η hη Θ n v ρ h
      cases η with
      | none => exact h.elim
      | some η => exact hη _ Θ n v ρ h
  | mu _ ih =>
      intro η hη Θ n v ρ h
      obtain ⟨-, -, hl⟩ := vBN_mu (b := true) |>.mp h
      refine hl (fun b _ _ _ r => b = true → r.InStratum γ) ?_ rfl
      intro b Θ' k u r hb e
      subst e
      exact ih (η := muEnvN η _ _) (fun m Θ'' k' v' ρ' h' => by
        cases m with
        | zero => exact h' rfl
        | succ m => exact hη m Θ'' k' v' ρ' h') Θ' k u r hb
  | int => rintro η hη Θ n v ρ ⟨-, rfl⟩; exact ResU.inStratum_empty γ
  | opq =>
      intro η hη Θ n v ρ h
      rcases Opaque.rel_cases h with ⟨-, rfl, -⟩ | ⟨-, l, -, rfl⟩
      · exact ResU.inStratum_empty γ
      · exact ResU.inStratum_single_own γ l _
  | fam _ ih =>
      rintro η hη Θ n v ρ ⟨l, c, -, -, hs⟩
      exact sepRange_closed (R := fun σ => σ.InStratum γ) (ResU.inStratum_empty γ)
        (fun _ _ _ hc o₁ o₂ => inStratum_compS hc o₁ o₂) (fun m σ hm => ih hη Θ n _ σ hm) hs

theorem vN_outlivesLe {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α γ : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) (hγ : γ < α) {T : VTy}
    (hT : VOutlivesLe Δ a T) :
    ∀ Θ n v ρ, vN (ℍ := ℍ) T δ Θ n v ρ → ρ.InStratum γ :=
  vNE_outlivesLe hδ ha hγ hT (η := none) (fun _ _ _ _ _ h => h.elim)

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

/-- `μ` along the resource-relative order, from the body's law at every stable environment: the
least fixed point lies in `{x | x is in the candidate at every extension}`. -/
theorem vBN_mu_extR {η : Option (Nat → TEntN)} {A : VTy} {δ : LSub} {b : Bool} {Θ Θ' : LocTy}
    {n : Nat} {v : Val} {ρ : WRes} (hη : EnvExtRN η)
    (ih : ∀ η', EnvExtRN η' → ∀ b' (Θ₀ Θ₁ : LocTy) k u r, Θ₀.ExtR Θ₁ r →
      vBN (ℍ := ℍ) η' b' A δ Θ₀ k u r → vBN (ℍ := ℍ) η' b' A δ Θ₁ k u r)
    (hE : Θ.ExtR Θ' ρ) (h : vBN (ℍ := ℍ) η b (.mu A) δ Θ n v ρ) :
    vBN (ℍ := ℍ) η b (.mu A) δ Θ' n v ρ := by
  obtain ⟨hA, hc, hl⟩ := vBN_mu.mp h
  refine vBN_mu.mpr ⟨hA, hc, fun P hP => ?_⟩
  let Q : Bool → LocTy → Nat → Val → WRes → Prop :=
    fun b Θ₀ k u r => ∀ Θ₁ : LocTy, Θ₀.ExtR Θ₁ r → P b Θ₁ k u r
  have hd : EnvExtRN (muEnvN η A Q) := fun m b' Θ₀ Θ₁ k u r hE' h' => by
    cases m with
    | zero => exact fun Θ₂ hE'' => h' Θ₂ (hE'.trans hE'')
    | succ m => exact hη m b' Θ₀ Θ₁ k u r hE' h'
  have hQ : MuClosedN (ℍ := ℍ) η A δ Q := by
    intro b' Θ₀ k u r hb Θ₁ hE'
    have hb' : vBN (ℍ := ℍ) (muEnvN η A Q) b' A δ Θ₁ k u r := ih _ hd b' Θ₀ Θ₁ k u r hE' hb
    refine hP b' Θ₁ k u r (vBN_mono_at A 0 (VTy.scons ⟨tCloseN η (.mu A), Q⟩ (tEnvN η))
      (VTy.scons ⟨tCloseN η (.mu A), P⟩ (tEnvN η)) hA (fun m => by cases m <;> rfl) (fun m hm => ?_)
      (fun b'' Θ'' i v'' ρ'' hq => hq Θ'' (LocTy.extR_refl Θ'' ρ'')) b' δ Θ₁ k u r hb')
    cases m with
    | zero => exact absurd rfl hm
    | succ m => rfl
  exact hl Q hQ Θ' hE

mutual
/-- **`𝒱⟦A⟧` is stable along the resource-relative order at the value's resource** (Core's
`vC_local`): `Mut` by `mutL_extR` (the cell's key and what lies above it are kept), `U` by the
order's transitivity at the thunk's resource, `Imm` because its payload's borrow cells are
longer-lived than the cell and the order keeps every `imm` record, the rest by their parts. -/
theorem vNE_extR : ∀ (A : VTy) (η : Option (Nat → TEntN)), EnvExtRN η → ∀ (δ : LSub)
    {Θ Θ' : LocTy} (n : Nat) (v : Val) (ρ : WRes),
    Θ.ExtR Θ' ρ → vNE (ℍ := ℍ) η A δ Θ n v ρ → vNE (ℍ := ℍ) η A δ Θ' n v ρ
  | .unit, η, hη, _, _, _, _, _, _, _, h => h
  | .tensor A B, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vNE_extR A η hη δ n v₁ ρ₁ (hE.left h₂) h₃,
        vNE_extR B η hη δ n v₂ ρ₂ (hE.right h₂) h₄⟩
  | .zero, η, hη, _, _, _, _, _, _, _, h => h
  | .sum A B, η, hη, δ, _, _, n, _, ρ, hE, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vNE_extR A η hη δ n v₁ ρ hE h₂⟩
      · exact .inr ⟨v₂, h₁, vNE_extR B η hη δ n v₂ ρ hE h₂⟩
  | .thunk _, η, hη, _, _, _, _, _, _, hE, h => fun Θ'' hE' hOK c hc ls =>
      h Θ'' (hE.trans hE') hOK c hc ls
  | .ref A, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vNE_extR A η hη δ n u σ (hE.right h₂) h₃⟩
  | .imm a A, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, h₄⟩, hw⟩ := h
      have hσ : LocTy.ExtR _ _ σ := hE.mono fun b hb => by
        have hjb : s.join < b := hb.of_stratum hs
        exact ⟨l, CellU.immOf s u σ hs, ResU.single_get_self _ _,
          by simp [CellU.kind_immOf],
          le_of_lt (lt_of_le_of_lt (LSet.meet_le_join s) hjb)⟩
      refine ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, vOE_extR A η hη δ n u σ hσ h₄⟩,
        fun l' s' u' σ' hs' e => ?_⟩
      obtain ⟨x, hx, hxs, hd⟩ := hw l' s' u' σ' hs' e
      obtain ⟨-, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨x, hE.2 x hx ⟨l, _, ResU.single_get_self _ _, by simp [CellU.kind_immOf], hxs⟩,
        hxs, hd⟩
  | .mut a A, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, b, hab, hm, hu⟩ := h
      exact ⟨α, hα, b, hab, mutL_extR hE hm, hu⟩
  | .box a A, η, hη, δ, _, _, n, v, ρ, hE, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vNE_extR A η hη δ n v ρ hE h₁, h₂⟩
  | .bang A, η, hη, δ, _, _, n, v, ρ, hE, h => ⟨h.1, vNE_extR A η hη δ n v ρ hE h.2⟩
  | .unk, η, hη, _, _, _, _, _, _, _, h => h
  | .int _, η, hη, _, _, _, _, _, _, _, h => h
  | .tvar m, η, hη, _, _, _, n, v, ρ, hE, h => by
      cases η with
      | none => exact h
      | some η => exact hη m true _ _ n v ρ hE h
  | .mu A, η, hη, δ, _, _, n, v, ρ, hE, h => vBN_mu_extR (b := true) hη (fun η' hη' b' _ _ k u r hE' h' => by
      cases b'
      · exact vOE_extR A η' hη' δ k u r hE' h'
      · exact vNE_extR A η' hη' δ k u r hE' h') hE h
  | .fam L, η, hη, δ, Θ, Θ', n, _, _, hE, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono_down (R := fun σ => LocTy.ExtR Θ Θ' σ)
        (fun _ _ _ hc hE' => ⟨hE'.left hc, hE'.right hc⟩)
        (fun m σ hEσ hm => vNE_extR L η hη δ n (Val.loc m) σ hEσ hm) hE h₃⟩
  | .opq _, η, hη, _, _, _, _, _, _, _, h => h

/-- **The observable view is stable along the resource-relative order**, as `vN_extR`. -/
theorem vOE_extR : ∀ (A : VTy) (η : Option (Nat → TEntN)), EnvExtRN η → ∀ (δ : LSub)
    {Θ Θ' : LocTy} (n : Nat) (v : Val) (ρ : WRes),
    Θ.ExtR Θ' ρ → vOE (ℍ := ℍ) η A δ Θ n v ρ → vOE (ℍ := ℍ) η A δ Θ' n v ρ
  | .unit, η, hη, _, _, _, _, _, _, _, h => h
  | .tensor A B, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, vOE_extR A η hη δ n v₁ ρ₁ (hE.left h₂) h₃,
        vOE_extR B η hη δ n v₂ ρ₂ (hE.right h₂) h₄⟩
  | .zero, η, hη, _, _, _, _, _, _, _, h => h
  | .sum A B, η, hη, δ, _, _, n, _, ρ, hE, h => by
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, vOE_extR A η hη δ n v₁ ρ hE h₂⟩
      · exact .inr ⟨v₂, h₁, vOE_extR B η hη δ n v₂ ρ hE h₂⟩
  | .thunk _, η, hη, _, _, _, _, _, _, _, _ => trivial
  | .ref A, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨l, u, σ, h₁, h₂, h₃⟩ := h
      exact ⟨l, u, σ, h₁, h₂, vOE_extR A η hη δ n u σ (hE.right h₂) h₃⟩
  | .imm a A, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, h₄⟩, hw⟩ := h
      have hσ : LocTy.ExtR _ _ σ := hE.mono fun b hb => by
        have hjb : s.join < b := hb.of_stratum hs
        exact ⟨l, CellU.immOf s u σ hs, ResU.single_get_self _ _,
          by simp [CellU.kind_immOf],
          le_of_lt (lt_of_le_of_lt (LSet.meet_le_join s) hjb)⟩
      refine ⟨α, hα, ⟨l, s, u, σ, hs, h₁, rfl, h₃, vOE_extR A η hη δ n u σ hσ h₄⟩,
        fun l' s' u' σ' hs' e => ?_⟩
      obtain ⟨x, hx, hxs, hd⟩ := hw l' s' u' σ' hs' e
      obtain ⟨-, e'⟩ := single_immOf_inj e
      obtain ⟨rfl, -⟩ := CellU.immOf_inj e'
      exact ⟨x, hE.2 x hx ⟨l, _, ResU.single_get_self _ _, by simp [CellU.kind_immOf], hxs⟩,
        hxs, hd⟩
  | .mut a A, η, hη, δ, _, _, n, _, _, hE, h => by
      obtain ⟨α, hα, b, hab, hm, hu⟩ := h
      exact ⟨α, hα, b, hab, mutL_extR hE hm, hu⟩
  | .box a A, η, hη, δ, _, _, n, v, ρ, hE, h => by
      obtain ⟨α, hα, h₁, h₂⟩ := h
      exact ⟨α, hα, vOE_extR A η hη δ n v ρ hE h₁, h₂⟩
  | .bang A, η, hη, δ, _, _, n, v, ρ, hE, h => ⟨h.1, vNE_extR A η hη δ n v ρ hE h.2⟩
  | .unk, η, hη, _, _, _, _, _, _, _, h => h
  | .int _, η, hη, _, _, _, _, _, _, _, h => h
  | .tvar m, η, hη, _, _, _, n, v, ρ, hE, h => by
      cases η with
      | none => exact h
      | some η => exact hη m false _ _ n v ρ hE h
  | .mu A, η, hη, δ, _, _, n, v, ρ, hE, h => vBN_mu_extR (b := false) hη (fun η' hη' b' _ _ k u r hE' h' => by
      cases b'
      · exact vOE_extR A η' hη' δ k u r hE' h'
      · exact vNE_extR A η' hη' δ k u r hE' h') hE h
  | .fam L, η, hη, δ, Θ, Θ', n, _, _, hE, h => by
      obtain ⟨l, c, h₁, h₂, h₃⟩ := h
      exact ⟨l, c, h₁, h₂, sepRange_mono_down (R := fun σ => LocTy.ExtR Θ Θ' σ)
        (fun _ _ _ hc hE' => ⟨hE'.left hc, hE'.right hc⟩)
        (fun m σ hEσ hm => vOE_extR L η hη δ n (Val.loc m) σ hEσ hm) hE h₃⟩
  | .opq _, η, hη, _, _, _, _, _, _, _, h => h
end

theorem vN_extR (A : VTy) (δ : LSub) {Θ Θ' : LocTy} (n : Nat) (v : Val) (ρ : WRes)
    (hE : Θ.ExtR Θ' ρ) (h : vN (ℍ := ℍ) A δ Θ n v ρ) : vN (ℍ := ℍ) A δ Θ' n v ρ :=
  vNE_extR A none envExtRN_none δ n v ρ hE h

theorem vO_extR (A : VTy) (δ : LSub) {Θ Θ' : LocTy} (n : Nat) (v : Val) (ρ : WRes)
    (hE : Θ.ExtR Θ' ρ) (h : vO (ℍ := ℍ) A δ Θ n v ρ) : vO (ℍ := ℍ) A δ Θ' n v ρ :=
  vOE_extR A none envExtRN_none δ n v ρ hE h

/-- **`𝒱⟦A⟧` is stable along `ExtA`**, at every type: `ExtA` is `ExtR` at every resource. -/
theorem vN_extA (A : VTy) (δ : LSub) {Θ Θ' : LocTy} (hE : Θ.ExtA Θ') (n : Nat) (v : Val)
    (ρ : WRes) (h : vN (ℍ := ℍ) A δ Θ n v ρ) : vN (ℍ := ℍ) A δ Θ' n v ρ :=
  vN_extR A δ n v ρ (hE.extR ρ) h

/-- The computation types `cN_extA` covers: `F A`, `⊤` and `ν`, read through `&` and `∀`. Not
an effect row (`F_Σ R`), and not `⊸`: a plain wand at `Θ` reads its argument at `Θ`, and an
argument at an extension `Θ′` is not one at `Θ`. -/
def noEffSpine : CTy → Prop
  | .ret _ => True
  | .arr _ _ => False
  | .amp C D => noEffSpine C ∧ noEffSpine D
  | .top => True
  | .all _ _ C => noEffSpine C
  | .nu _ => True
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
  | .nu _, _, _, _, _, _, _, _, _, _, _, h => h
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
  | .nu _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
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
