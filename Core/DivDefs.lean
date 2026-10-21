import Core.EffDefs
import Support.Dynamics.Iterate

/-!
# Core — `Div`: the relation at a row that holds it  `[spec §14, §19]`

`Div` is the reserved name `divEff` with one linear operation `tick : 1 ↠ Next`, `Next = 1 ⊕ 1`
(`Support/Dynamics/Iterate.lean`).  A row *holds* `Div` when the operation it finds at
`(divEff, 0)` is `tick` (`CTy.divAt`).

`ewpTS` is a least fixed point, so a computation that ticks forever is not in it.  At a row that
holds `Div` the relation is a greatest fixed point over **segments** (`cwp`): a segment, up to
the next tick, is an `ewpTS` run; a tick stops it and owes its continuation, at each answer, to
the candidate and to `Closing`.

    cwp T Q   ≜  gfp W. ewpTS · (opTable T∖tick ∨ Π_W) Q
    Π_W(tick)  =  λ_. λκ. ∀ n : Next. W (κ n) ∧ Closing (κ n)
    Closing   ≜  ewpTS · (opTable T, tick answered close only) Q

`T` is the row's whole table.  `Closing` is the least fixed point at the table where a tick may
only be answered *close*: after a close, the computation reaches its end through finitely many
ticks, each answered close.  It is what makes a close a close: `div_fuel`'s totality and
`reify`'s close read it.  `cwp` is written in `Prop` as `∃ W`, as `𝒞⟦νX. C⟧` is.

`effWp` is the relation at a row's table: `cwp` where the row holds `Div`, `ewpTS` elsewhere.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Kont)
open BoCa.Lifetime (LSub)

/-! ### The effect -/

/-- `Next = 1 ⊕ 1`.  `[spec §14]` -/
abbrev nextTy : VTy := .sum .unit .unit

/-- `tick : 1 ↠ Next`, the operation `0` of `Div`, linear: its continuation has no cancel.
`[spec §14]` -/
def tickSig : OpSig := ⟨divEff, 0, .lin, .unit, nextTy, .ret .unit, false⟩

/-- `A` is `1`. -/
def VTy.isUnitB : VTy → Bool
  | .unit => true
  | _ => false

/-- `B` is `Next`. -/
def VTy.isNextB : VTy → Bool
  | .sum A B => A.isUnitB && B.isUnitB
  | _ => false

/-- The signature `A ↠^q B` is `tick`'s. -/
def tickB (q : Qual) (A B : VTy) : Bool := q == .lin && A.isUnitB && B.isNextB

/-- **The row holds `Div`**: the operation it finds at `(divEff, 0)` is `tick`.  `[spec §14]` -/
def CTy.divAt : CTy → Bool
  | .eff n i q A B _ _ C => if n = divEff ∧ i = 0 then tickB q A B else C.divAt
  | _ => false

/-! ### The tables -/

/-- The table without `Div`'s key. -/
def OpTab.erase0 (T : OpTab) : OpTab := fun n i => if n = divEff ∧ i = 0 then none else T n i

/-- The table at `Div`'s key alone. -/
def OpTab.only0 (T : OpTab) : OpTab := fun n i => if n = divEff ∧ i = 0 then T n i else none

/-- An entry answered *close* only. -/
def OpEnt.closeOnly (en : OpEnt) : OpEnt :=
  { en with PB := fun ls w ρ => en.PB ls w ρ ∧ w = closeV }

/-- The table whose entry at `Div`'s key is answered *close* only. -/
def OpTab.closeAt (T : OpTab) : OpTab :=
  fun n i => if n = divEff ∧ i = 0 then (T n i).map OpEnt.closeOnly else T n i

/-! ### The relation -/

/-- `Closing T Q`: the computation ends, at `Q`, through finitely many ticks, each answered
*close*.  `[spec §14]` -/
def Closing (T : OpTab) (Q : List SRec → Val → WProp) : List SRec → Expr → WProp :=
  fun ls e => ewpTS ls e (opTable T.closeAt) Q

/-- What a tick owes its continuation, at the candidate `W`: `W` and `Closing`. -/
def owe (T : OpTab) (Q : List SRec → Val → WProp) (W : List SRec → Expr → WProp) :
    List SRec → Expr → WProp :=
  fun ls e ρ => W ls e ρ ∧ Closing T Q ls e ρ

/-- The tick's stop, owing `owe W` whatever the run would owe. -/
def tickStop (T : OpTab) (Q : List SRec → Val → WProp) (W : List SRec → Expr → WProp) : Table :=
  fun ls t _ => performStop T.only0 ls t (owe T Q W)

/-- The table of a segment at the candidate `W`: a stop of the row but the tick, or a tick, which
owes its continuation to `owe W`, not to the segment's least fixed point. -/
def divTab (T : OpTab) (Q : List SRec → Val → WProp) (W : List SRec → Expr → WProp) : Table :=
  orTab (opTable T.erase0) (tickStop T Q W)

/-- One unfolding of the greatest fixed point: a segment at the candidate. -/
def cwpF (T : OpTab) (Q : List SRec → Val → WProp) (W : List SRec → Expr → WProp) :
    List SRec → Expr → WProp :=
  fun ls e => ewpTS ls e (divTab T Q W) Q

/-- **`cwp`**: the greatest fixed point of `cwpF`, `⋃{W | W ⊆ cwpF W}`, written in `Prop`.
`[spec §14, §19]` -/
def cwp (T : OpTab) (Q : List SRec → Val → WProp) : List SRec → Expr → WProp :=
  fun ls e ρ => ∃ W : List SRec → Expr → WProp,
    (∀ ls e ρ, W ls e ρ → cwpF T Q W ls e ρ) ∧ W ls e ρ

/-- **The relation at a row's table**: `cwp` where the row holds `Div`, `ewpTS` elsewhere.
`[spec §14, §19]` -/
def effWp : Bool → OpTab → (List SRec → Val → WProp) → List SRec → Expr → WProp
  | true, T, Q => cwp T Q
  | false, T, Q => fun ls e => ewpTS ls e (opTable T) Q

end BoCa.Fig16.LogRel.Core

end
