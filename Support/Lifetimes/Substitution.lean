import Paper.S1_Syntax.Definitions
import Support.Lifetimes.Terms

/-!
# Support — Lifetimes — Substitution

`[about ours]`.  Substitution of lifetimes into lifetime terms and types, with the capture and range bounds it needs.
-/

noncomputable section

namespace BoCa.Lifetime
open BoCa.Lifetime

/-- Does this lifetime mention the variable `x`? -/
def Life.mentions (x : LifeVar) : Life → Bool
  | .var y    => x == y
  | .top      => false
  | .join a b => a.mentions x || b.mentions x
  | .meet a b => a.mentions x || b.mentions x

/-- One past the largest variable index in a lifetime.  Used to choose a `∀`
    binder fresh for some collection of types. -/
def Life.varBound : Life → Nat
  | .var x    => x + 1
  | .top      => 0
  | .join a b => max a.varBound b.varBound
  | .meet a b => max a.varBound b.varBound

/-- A simultaneous substitution on lifetime variables. -/
abbrev LSubst := List (LifeVar × Life)

def Life.applySub (σ : LSubst) : Life → Life
  | .var x    => match assocFind x σ with
                 | some a => a
                 | none   => .var x
  | .top      => .top
  | .join a b => .join (a.applySub σ) (b.applySub σ)
  | .meet a b => .meet (a.applySub σ) (b.applySub σ)

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- One past the largest lifetime index anywhere in `T`, binders included.
    Used to pick capture-avoiding renamings. -/
def Ty.lifeBound : Ty → Nat
  | .unit         => 0
  | .unk          => 0
  | .ref T        => T.lifeBound
  | .bang T        => T.lifeBound
  | .imm a T      => max a.varBound T.lifeBound
  | .mut a T      => max a.varBound T.lifeBound
  | .box a T      => max a.varBound T.lifeBound
  | .all x b T    => max (x + 1) (max b.varBound T.lifeBound)
  | .sum    T₁ T₂ => max T₁.lifeBound T₂.lifeBound
  | .tensor T₁ T₂ => max T₁.lifeBound T₂.lifeBound
  | .lolli  T₁ T₂ => max T₁.lifeBound T₂.lifeBound

/-- Would applying `σ` capture a free `'y`?  (`LSubst` is an abbreviation for a
    `List`, so these cannot be dot-notation methods.) -/
def lsubCaptures (σ : LSubst) (y : LifeVar) : Bool :=
  σ.any (fun p => p.2.mentions y)

/-- `σ` with the binding for `'y` removed — `'y` is shadowed. -/
def lsubDrop (σ : LSubst) (y : LifeVar) : LSubst :=
  σ.filter (fun p => p.1 != y)

/-- One past the largest variable index `σ` mentions, key or value. -/
def lsubRangeBound (σ : LSubst) : Nat :=
  σ.foldr (fun p acc => max (max (p.1 + 1) p.2.varBound) acc) 0

/-- `T` with the simultaneous lifetime substitution `σ` applied, renaming `∀`
    binders where necessary to avoid capture. -/
def Ty.applyLSub (σ : LSubst) : Ty → Ty
  | .unit         => .unit
  | .unk          => .unk
  | .ref T        => .ref (T.applyLSub σ)
  | .bang T        => .bang (T.applyLSub σ)
  | .imm a T      => .imm (a.applySub σ) (T.applyLSub σ)
  | .mut a T      => .mut (a.applySub σ) (T.applyLSub σ)
  | .box a T      => .box (a.applySub σ) (T.applyLSub σ)
  | .sum    T₁ T₂ => .sum    (T₁.applyLSub σ) (T₂.applyLSub σ)
  | .tensor T₁ T₂ => .tensor (T₁.applyLSub σ) (T₂.applyLSub σ)
  | .lolli  T₁ T₂ => .lolli  (T₁.applyLSub σ) (T₂.applyLSub σ)
  | .all y b T    =>
      let σ' := lsubDrop σ y                    -- `'y` is shadowed inside `T`
      if lsubCaptures σ' y then
        let z := max (y + 1) (max (lsubRangeBound σ') T.lifeBound)
        .all z (b.applySub σ) (T.applyLSub ((y, Life.var z) :: σ'))
      else
        .all y (b.applySub σ) (T.applyLSub σ')

/-- `T[@a/'x]` — the substitution `∀E` performs. -/
def Ty.instLife (x : LifeVar) (a : Life) (T : Ty) : Ty := T.applyLSub [(x, a)]

end BoCa

end
