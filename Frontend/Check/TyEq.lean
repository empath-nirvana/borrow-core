import Frontend.Check.Elab

/-!
# Frontend — Check — type compatibility  `[spec §3, §19]`

The checker's one test of whether two kernel types agree: equal up to the names of their lifetime
binders (`[α]`, SPEC §3). This file holds the decisions; `Frontend/Check/Conv.lean` holds the same
decisions with the derivation nodes (`rAlpha`, `rEffSub`) that carry a checked term from one type
to the other. Every place under `Frontend/Check/` that compares two kernel types asks one of the
two, or is listed with the reason it compares exactly in `scripts/type-eq.allow`;
`scripts/check-type-eq.sh` refuses any other comparison of `VTy`, `CTy`, `OpSig` or a row there.

* `tyEqV`, `tyEqC`: `VTy.alphaB`, `CTy.alphaB` at no binder pairs.
* `tyEqEnts`: two handlers' operation lists `(q, A, B)`, each signature up to `[α]`.
* `effRow?`, `effRowOf?`: a computation type as a returner chain `F_Σ A`, with the proof that the
  chain rebuilds it (`effOf_of_effRow?`).
* `rowUnion`: the rows two premises' derivations read, together.
* `alignFin`, `alignRow`: a row read at the names of another's, so that `[sub]` (`RowLe`, which
  compares operations exactly) and then `[α]` reach a row that both grows and renames.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check (rowLeB)

/-- Value types compatible: equal up to the names of their lifetime binders.  `[spec §3]` -/
abbrev tyEqV (A B : CVTy) : Bool := BoCa.Fig16.LogRel.Core.VTy.alphaB [] A B

/-- Computation types compatible: equal up to the names of their lifetime binders.  `[spec §3]` -/
abbrev tyEqC (C D : CCTy) : Bool := BoCa.Fig16.LogRel.Core.CTy.alphaB [] C D

/-- Two lists of value types, position by position, each up to `[α]`. -/
def tyEqVs : List CVTy → List CVTy → Bool
  | [], [] => true
  | A :: As, B :: Bs => tyEqV A B && tyEqVs As Bs
  | _, _ => false

/-- Two optional value types: both absent, or both present and equal up to `[α]`. -/
def tyEqVo : Option CVTy → Option CVTy → Bool
  | none, none => true
  | some A, some B => tyEqV A B
  | _, _ => false

/-- Two lists of a handler's operations `(q, A ↠ B)`, position by position: the same qualifier and
each signature up to `[α]`. -/
def tyEqEnts : List (CQual × CVTy × CVTy) → List (CQual × CVTy × CVTy) → Bool
  | [], [] => true
  | (q, A, B) :: es, (q', A', B') :: es' =>
      decide (q = q') && tyEqV A A' && tyEqV B B' && tyEqEnts es es'
  | _, _ => false

/-- `C` as a returner chain `F_Σ A`: its row and answer. -/
def effRow? : CCTy → Option (CRow × CVTy)
  | .ret A => some ([], A)
  | .eff n i q A B fin rc C => (effRow? C).map fun (S, R) => (⟨n, i, q, A, B, fin, rc⟩ :: S, R)
  | _ => none

/-- `effRow?` reads `C` back exactly: the chain its row and answer rebuild is `C`. -/
theorem effOf_of_effRow? : ∀ {C : CCTy} {S : CRow} {A : CVTy}, effRow? C = some (S, A) →
    effOf S A = C
  | .ret A, S, A', h => by
      simp only [effRow?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
  | .eff n i q A B fin rc C, S, R, h => by
      simp only [effRow?, Option.map_eq_some_iff] at h
      obtain ⟨⟨S', R'⟩, h', he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simp only [effOf, BoCa.Fig16.LogRel.Core.CTy.effOf]
      rw [show BoCa.Fig16.LogRel.Core.CTy.effOf S' R' = C from effOf_of_effRow? h']
  | .arr _ _, _, _, h | .amp _ _, _, _, h | .top, _, _, h | .all _ _ _, _, _, h
  | .nuSys _ _ _, _, _, h => by simp [effRow?] at h

/-- `C` as a returner chain `F_Σ A`, with the proof that `F_Σ A` is `C` (`effOf_of_effRow?`). -/
def effRowOf? (C : CCTy) : Option (Σ' (S : CRow) (A : CVTy), effOf S A = C) :=
  match h : effRow? C with
  | some (S, A) => some ⟨S, A, effOf_of_effRow? h⟩
  | none => none

/-- The rows the derivations of two premises read, together (`Res.sigs`): their union. A list of
signatures, not a comparison of two types: an operation the two read at α-variants of one
signature is kept twice, and `sigsOkB` reads the two as one signature. -/
abbrev rowUnion (s t : CRow) : CRow := s ∪ t

@[inherit_doc] infixl:65 " ∪ᵣ " => rowUnion

/-- The cancel row `F` read at the names of `F'`: each layer `F'` finds at its key with an
α-equivalent argument and answer takes those, and its own cancel row read at that layer's, in
turn. Every other component is kept, so the result is α-equivalent to `F`. -/
def alignFin (F' : CCTy) : CCTy → CCTy
  | .eff n i q A B f rc C =>
    match BoCa.Fig16.LogRel.Core.Row.find (BoCa.Fig16.LogRel.Core.CTy.rowOf F') n i with
    | some o' =>
      if tyEqV o'.A A && tyEqV o'.B B
      then .eff n i q o'.A o'.B (alignFin o'.fin f) rc (alignFin F' C)
      else .eff n i q A B f rc (alignFin F' C)
    | none => .eff n i q A B f rc (alignFin F' C)
  | F => F

/-- `S`'s operations read at the names of `S'`'s: where `S'` finds an operation at the key with an
α-equivalent argument and answer, those, and its cancel row read at the names of `S'`'s
(`alignFin`), at every depth. An operation of `S` that `S'` does not find, and a cancel row's
layer its counterpart does not hold, keep their names. The row `[sub]` reaches from `S'`
before `[α]` reads it at `S` (`convComp`). Where some row α-equivalent to `S` is above `S'`, this
one is (argued, not proved): `[sub]` compares the operations `S'` finds, and those are read at
`S'`'s names. -/
def alignRow (S' S : CRow) : CRow := S.map fun o =>
  match BoCa.Fig16.LogRel.Core.Row.find S' o.n o.i with
  | some o' =>
    if tyEqV o'.A o.A && tyEqV o'.B o.B
    then { o with A := o'.A, B := o'.B, fin := alignFin o'.fin o.fin }
    else o
  | none => o

/-! The row `[sub]` then `[α]` reach at a cancel row that both grows and names its binder
differently. The synthesized row `S'` holds a cancellable `1.0` whose cancel row holds `2.0`, its
argument `U (∀'5 ⊏ ⊤. F 1)`; the expected row `S` holds `1.0` with a cancel row holding `2.0` at
`U (∀'7 ⊏ ⊤. F 1)` and `3.0` besides. `[sub]` alone does not reach `S`, nor `[α]` alone; `S` read at
`S'`'s names is above `S'` and α-equivalent to `S`, which is what `convComp` emits. -/
section
open BoCa.Fig16.LogRel.Core (OpSig CTy VTy)

private def finSyn : CCTy :=
  .eff 2 0 .cancel (.thunk (.all 5 .top (.ret .unit))) .unit (.ret .unit) false (.ret .unit)
private def finExp : CCTy :=
  .eff 2 0 .cancel (.thunk (.all 7 .top (.ret .unit))) .unit (.ret .unit) false
    (.eff 3 0 .cancel .unit .unit (.ret .unit) false (.ret .unit))
private def rowSyn : CRow := [⟨1, 0, .cancel, .unit, .unit, finSyn, false⟩]
private def rowExp : CRow := [⟨1, 0, .cancel, .unit, .unit, finExp, false⟩]

theorem alignRow_grow_renamed :
    rowLeB rowSyn rowExp = false ∧
    tyEqC (CTy.effOf rowSyn .unit) (CTy.effOf rowExp .unit) = false ∧
    rowLeB rowSyn (alignRow rowSyn rowExp) = true ∧
    tyEqC (CTy.effOf (alignRow rowSyn rowExp) .unit) (CTy.effOf rowExp .unit) = true := by
  decide

end

end Frontend.Check
