import Frontend.Check.Consts

/-!
# Frontend — Check — the relaxed lend R1  `[spec §29]`

`withbor2r['x, @b, A, B, [ROW]](p, m) M` is R1 (`CDerivesP.lendR`): the owned cell `p : ref A`
lent as `m : mut 'x A` to a body `M` at a row of resuming operations (`Row.ResumeO`). `M` is
checked at the lifetime context `Δ, 'x ⊏ @b` and the context `m : mut 'x A` alone: it sees no
other variable. The rule concludes at the context `p : ref A` alone; under the program's other
slots its term is `(λp. withborU d p (Λ. λm. M)) p`, the λ at the empty context placed by
`nilDead`. The derivation is `CDerivesP`'s, and the result's `pins` records the use.

* `noThunkB`, `Row.resumeOB`: `NoThunkT` and `Row.ResumeO`, decided, with their soundness.
* `rLendR`: the builder.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core (NoThunkT Row.ResumeO)

/-- `NoThunkT`, decided.  `[spec §29]` -/
def noThunkB : VTy → Bool
  | .tensor A B => noThunkB A && noThunkB B
  | .sum A B => noThunkB A && noThunkB B
  | .thunk _ => false
  | .bang A => noThunkB A
  | .ref A => noThunkB A
  | .box _ A => noThunkB A
  | .fam L => noThunkB L
  | _ => true

theorem noThunkB_sound : ∀ {A : VTy}, noThunkB A = true → NoThunkT A
  | .tensor A B, h | .sum A B, h => by
      simp only [noThunkB, Bool.and_eq_true] at h
      exact ⟨noThunkB_sound h.1, noThunkB_sound h.2⟩
  | .thunk _, h => by simp [noThunkB] at h
  | .bang A, h | .ref A, h | .box _ A, h | .fam A, h => noThunkB_sound (A := A) h
  | .unit, _ | .zero, _ | .imm _ _, _ | .mut _ _, _ | .unk, _ | .tvar _, _ | .mu _, _
  | .int _, _ | .opq _, _ => by simp [NoThunkT]

/-- `Row.ResumeO`, decided: every operation resumes, is not unrestricted, has the empty cancel
row, answers `1`, is of a nonzero name, and takes closed data with no `U`.  `[spec §29]` -/
def Row.resumeOB (S : Row) (x : LifeVar) : Bool :=
  S.all fun o => !o.abort && o.q != .unr && decide (o.fin = .ret .unit) && decide (o.B = .unit) &&
    o.n != 0 && !vfreeB x o.A && outlivesAllB o.A && noThunkB o.A

theorem Row.resumeOB_sound {S : Row} {x : LifeVar} (h : Row.resumeOB S x = true) :
    Row.ResumeO S x := by
  intro o ho
  have := List.all_eq_true.mp h o ho
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', decide_eq_true_eq] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩ := this
  exact ⟨h₁, h₂, h₃, h₄, h₅, not_vfree_of_vfreeB h₆, outlivesAllB_sound _ h₇, noThunkB_sound h₈⟩

end BoCa.Fig16.LogRel.Core.Check

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerivesP Jdg NoThunkT Row.ResumeO VFree VOutlivesLe HasDtor dtorE
  dtor_wf withborUV lendCb closedAt)

/-- A derivation that uses a relaxed rule: its tie is not claimed. -/
theorem TiedDer.pinned {p : Pins} {s : CRow} {Δ : LifeCtx} {Γ : Ctx CVTy} {e : BoCa.Expr}
    {j : Jdg} (q : Pin) (h : CDerivesP Δ Γ e j) : TiedDer (q :: p) s Δ Γ e j :=
  ⟨fun h' => absurd h' (List.cons_ne_nil _ _), h⟩

/-- R1's term at `r : ref A`, the variable `0`: `withborU d r (Λ. λm. M)`. -/
def lendRE (d M : CExpr) : CExpr :=
  .app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M))

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- **R1** (`CDerivesP.lendR`) at the slot `i : ref A`, its body `rM` checked at `Δ, 'x ⊏ @b`
and the view alone: the λ over the rule's term at the empty context, placed by `nilDead` and
applied to the slot.  `[spec §29]` -/
def rLendR {A B : CVTy} {S : CRow} (q : Pin) (x : LifeVar) (b : CLife) (i : Nat)
    (hi : T[i]? = some (.ref A)) (hb : Δ.Defines b) (hx : Δ.find? x = none)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x A) (hB : ¬ VFree x B) (hBn : NoThunkT B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' A) (hS : Row.ResumeO S x)
    (hdt : HasDtor (.ref A)) (hdc : closedAt 0 (dtorE (.ref A)) = true)
    (rM : Res (Δ.extend x b) [.mut (.var x) A] (.comp (effOf S (.box (.var x) B))))
    (hL : subL (allL [.mut (.var x) A]) (orL rM.F.u rM.F.w) = true)
    (hM1 : closedAt 1 rM.e = true) (hcb : closedAt 0 (lendCb rM.e).1 = true)
    (h : overlapOK T (Fam.deadStrict T).u (oneL T i) = true) :
    Res Δ T (.comp (effOf S (.tensor (.ref A) B))) :=
  let dM := (rM.F.d _ (btw_allL _ _ _ rM.F.hu rM.F.hw hL)).2
  let hR1 : CDerivesP Δ [⟨.ref A, true⟩] (lendRE (dtorE (.ref A)) rM.e)
      (.comp (effOf S (.tensor (.ref A) B))) :=
    .lendR hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc (CDerivesP.ofC (dtor_wf hdt .nil)) dM
  let rL : Res Δ T (.comp (.arr (.ref A) (effOf S (.tensor (.ref A) B)))) :=
    ⟨.val (BoCa.Val.lam (lendRE (dtorE (.ref A)) rM.e)), rM.sigs, q :: rM.pins,
      (Fam.deadStrict T).map fun _ hd => TiedDer.pinned q (.nilDead hd (.lam hR1))⟩
  rApp rL i hi h

end

end Frontend.Check
