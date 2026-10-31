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
* `rLendR`: the builder, at the typed term.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core (NoThunkT Row.ResumeO Row.ResumeOC)

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

/-- `Row.ResumeOT` (W-tick, the #743 spike), decided: each operation is `tick`, or one
`Row.resumeOB` admits. -/
def Row.resumeOTB (S : Row) (x : LifeVar) : Bool :=
  S.all fun o => decide (o = BoCa.Fig16.LogRel.Core.tickSig) || Row.resumeOB [o] x

theorem Row.resumeOTB_sound {S : Row} {x : LifeVar} (h : Row.resumeOTB S x = true) :
    BoCa.Fig16.LogRel.Core.Row.ResumeOT S x := by
  intro o ho
  have := List.all_eq_true.mp h o ho
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · exact .inl h
  · exact .inr (Row.resumeOB_sound h o (List.mem_singleton.mpr rfl))

/-- `Row.ResumeOC`, decided: each operation is one `Row.resumeOB` admits, a cancellable `await`
of a nonzero name taking closed data, or the abortive `cancelled` of an `await`'s name.
`[spec §29, §29a]` -/
def Row.resumeOCB (S : Row) (x : LifeVar) : Bool :=
  S.all fun o =>
    (!o.abort && o.q != .unr && decide (o.fin = .ret .unit) && decide (o.B = .unit) &&
      o.n != 0 && !vfreeB x o.A && outlivesAllB o.A && noThunkB o.A) ||
    (o.awaitB && o.n != 0 && !vfreeB x o.A && outlivesAllB o.A && noThunkB o.A) ||
    (o.abort && o.i == 1 && o.q == .cancel && decide (o.A = .unit) && o.n != 0 &&
      S.any fun a => a.n == o.n && a.awaitB)

theorem Row.resumeOCB_sound {S : Row} {x : LifeVar} (h : Row.resumeOCB S x = true) :
    Row.ResumeOC S x := by
  intro o ho
  have := List.all_eq_true.mp h o ho
  simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    decide_eq_true_eq, beq_iff_eq, List.any_eq_true] at this
  rcases this with (⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩ | ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩) |
      ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, a, ha, han, haw⟩
  · exact .inl ⟨h₁, h₂, h₃, h₄, h₅, not_vfree_of_vfreeB h₆, outlivesAllB_sound _ h₇,
      noThunkB_sound h₈⟩
  · exact .inr (.inl ⟨h₁, h₂, not_vfree_of_vfreeB h₃, outlivesAllB_sound _ h₄, noThunkB_sound h₅⟩)
  · exact .inr (.inr ⟨h₁, h₂, h₃, h₄, h₅, a, ha, han, haw⟩)

/-- `OpSig.LendO`, decided.  `[spec §29, §29a]` -/
def OpSig.lendOB (x : LifeVar) (o : OpSig) : Bool :=
  (!o.abort && o.q != .unr && decide (o.fin = .ret .unit) && decide (o.B = .unit) &&
    o.n != 0 && !vfreeB x o.A && outlivesAllB o.A && noThunkB o.A) ||
  (o.awaitB && o.n != 0 && !vfreeB x o.A && outlivesAllB o.A && noThunkB o.A) ||
  (o.abort && o.n != 0 && !vfreeB x o.A && outlivesAllB o.A && noThunkB o.A)

theorem OpSig.lendOB_sound {x : LifeVar} {o : OpSig} (h : OpSig.lendOB x o = true) :
    BoCa.Fig16.LogRel.Core.OpSig.LendO x o := by
  simp only [OpSig.lendOB, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h with (⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩ | ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩) |
      ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩
  · exact .inl ⟨h₁, h₂, h₃, h₄, h₅, not_vfree_of_vfreeB h₆, outlivesAllB_sound _ h₇,
      noThunkB_sound h₈⟩
  · exact .inr (.inl ⟨h₁, h₂, not_vfree_of_vfreeB h₃, outlivesAllB_sound _ h₄, noThunkB_sound h₅⟩)
  · exact .inr (.inr ⟨h₁, h₂, not_vfree_of_vfreeB h₃, outlivesAllB_sound _ h₄, noThunkB_sound h₅⟩)

/-- `Row.ResumeOCE` (R1 with error escape), decided. -/
def Row.resumeOCEB (S : Row) (x : LifeVar) : Bool := S.all (OpSig.lendOB x)

theorem Row.resumeOCEB_sound {S : Row} {x : LifeVar} (h : Row.resumeOCEB S x = true) :
    BoCa.Fig16.LogRel.Core.Row.ResumeOCE S x :=
  fun o ho => OpSig.lendOB_sound (List.all_eq_true.mp h o ho)

/-- `Row.ResumeOE` (W-tick and W-hold with the cancel path and error escape), decided. -/
def Row.resumeOEB (S : Row) (x : LifeVar) : Bool :=
  S.all fun o => decide (o = BoCa.Fig16.LogRel.Core.tickSig) || OpSig.lendOB x o

theorem Row.resumeOEB_sound {S : Row} {x : LifeVar} (h : Row.resumeOEB S x = true) :
    BoCa.Fig16.LogRel.Core.Row.ResumeOE S x := by
  intro o ho
  have := List.all_eq_true.mp h o ho
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · exact .inl h
  · exact .inr (OpSig.lendOB_sound h)

end BoCa.Fig16.LogRel.Core.Check

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerivesP Jdg NoThunkT Row.ResumeO Row.ResumeOT Row.ResumeOC VFree VOutlivesLe
  HasDtor dtorE dtor_wf withborUV lendCb closedAt lendView LendSide)

/-- A derivation that uses a relaxed rule: its tie is not claimed. -/
theorem TiedDer.pinned {p : Pins} {s : CRow} {Δ : LifeCtx} {Γ : Ctx CVTy} {e : BoCa.Expr}
    {j : Jdg} (q : Pin) (h : CDerivesP Δ Γ e j) : TiedDer (q :: p) s Δ Γ e j :=
  ⟨fun h' => absurd h' (List.cons_ne_nil _ _), h⟩

/-- R1's term at `r : ref A`, the variable `0`: `withborU d r (Λ. λm. M)`. -/
def lendRE (d M : CExpr) : CExpr :=
  .app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M))

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- **R1** (`CDerivesP.lendR`) at the slot `k : ref A`, its body `rM` checked at `Δ, 'x ⊏ @b`
and the view alone: the λ over the rule's node at the empty context, placed by `nilDead` and
applied to the slot. The finaliser is the owner's destructor, its derived node.  `[spec §29]` -/
def rLendR (i : TInfo) {A B : CVTy} {S : CRow} (q : Pin) (x : LifeVar) (b : CLife) (k : Nat)
    (hk : T[k]? = some (.ref A)) (hb : Δ.Defines b) (hx : Δ.find? x = none)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x A) (hB : ¬ VFree x B) (hBn : NoThunkT B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' A) (hS : BoCa.Fig16.LogRel.Core.Row.ResumeOCE S x)
    (hdt : HasDtor (.ref A)) (hdc : closedAt 0 (dtorE (.ref A)) = true)
    (hde : (dtorE (.ref A)).effFree = true)
    (rM : Res (Δ.extend x b) [.mut (.var x) A] (.comp (effOf S (.box (.var x) B))))
    (hL : subL (allL [.mut (.var x) A]) (orL rM.F.u rM.F.w) = true)
    (hM1 : closedAt 1 rM.e = true) (hcb : closedAt 0 (lendCb rM.e).1 = true)
    (h : overlapOK T (Fam.deadStrict T).u (oneL T k) = true) :
    Res Δ T (.comp (effOf S (.tensor (.ref A) B))) :=
  let dM := (rM.F.d _ (btw_allL _ _ _ rM.F.hu rM.F.hw hL)).2
  let J : Jdg := .comp (effOf S (.tensor (.ref A) B))
  let JL : Jdg := .comp (.arr (.ref A) (effOf S (.tensor (.ref A) B)))
  let tR : TExpr := .lendR i J x b A B S (.dtor i (.val (.lolli (.ref A) .unit)) (.ref A)) rM.t
  let hR1 : TDerivesP Δ [⟨.ref A, true⟩] tR J :=
    .lendR hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc (.dtor hdt hdc hde .nil) dM
  let rL : Res Δ T JL :=
    ⟨.nilDead i JL JL (.lam i JL (.ref A) (effOf S (.tensor (.ref A) B)) tR), rM.sigs, q :: rM.pins,
      (Fam.deadStrict T).map fun _ hd => TTied.pinned q (.nilDead hd (.lam hR1))⟩
  rApp i rL k hk h

/-- **W-imm** (`CDerivesP.lendRI`, the #743 spike) at the slot `k : ref A`: `rLendR` at an `imm` view.  `[spec §29]` -/
def rLendRI (i : TInfo) {A B : CVTy} {S : CRow} (q : Pin) (x : LifeVar) (b : CLife) (k : Nat)
    (hk : T[k]? = some (.ref A)) (hb : Δ.Defines b) (hx : Δ.find? x = none)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x A) (hB : ¬ VFree x B) (hBn : NoThunkT B)
    (hsc : BoCa.Fig16.LogRel.Core.VScoped Δ A) (hS : Row.ResumeO S x)
    (hdt : HasDtor (.ref A)) (hdc : closedAt 0 (dtorE (.ref A)) = true)
    (hde : (dtorE (.ref A)).effFree = true)
    (rM : Res (Δ.extend x b) [.imm (.var x) A] (.comp (effOf S (.box (.var x) B))))
    (hL : subL (allL [.imm (.var x) A]) (orL rM.F.u rM.F.w) = true)
    (hM1 : closedAt 1 rM.e = true) (hcb : closedAt 0 (lendCb rM.e).1 = true)
    (h : overlapOK T (Fam.deadStrict T).u (oneL T k) = true) :
    Res Δ T (.comp (effOf S (.tensor (.ref A) B))) :=
  let dM := (rM.F.d _ (btw_allL _ _ _ rM.F.hu rM.F.hw hL)).2
  let J : Jdg := .comp (effOf S (.tensor (.ref A) B))
  let JL : Jdg := .comp (.arr (.ref A) (effOf S (.tensor (.ref A) B)))
  let tR : TExpr := .lendRI i J x b A B S (.dtor i (.val (.lolli (.ref A) .unit)) (.ref A)) rM.t
  let hR1 : TDerivesP Δ [⟨.ref A, true⟩] tR J :=
    .lendRI hb hx hbx hΔx hT hB hBn hsc hS hM1 hcb hdc (.dtor hdt hdc hde .nil) dM
  let rL : Res Δ T JL :=
    ⟨.nilDead i JL JL (.lam i JL (.ref A) (effOf S (.tensor (.ref A) B)) tR), rM.sigs, q :: rM.pins,
      (Fam.deadStrict T).map fun _ hd => TTied.pinned q (.nilDead hd (.lam hR1))⟩
  rApp i rL k hk h

/-- **W-nest** (`CDerivesP.lendRF`, the #743 spike) at the slot `k : array A`: `rLendR` at a family.  `[spec §29]` -/
def rLendRF (i : TInfo) {A B : CVTy} {S : CRow} (q : Pin) (x : LifeVar) (b : CLife) (k : Nat)
    (hk : T[k]? = some (.array A)) (hb : Δ.Defines b) (hx : Δ.find? x = none)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x A) (hB : ¬ VFree x B) (hBn : NoThunkT B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' A)
    (hsideB : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' B) (hS : Row.ResumeO S x)
    (hdt : HasDtor (.array A)) (hdc : closedAt 0 (dtorE (.array A)) = true)
    (hde : (dtorE (.array A)).effFree = true)
    (rM : Res (Δ.extend x b) [.fam (.mut (.var x) A)] (.comp (effOf S (.box (.var x) B))))
    (hL : subL (allL [.fam (.mut (.var x) A)]) (orL rM.F.u rM.F.w) = true)
    (hM1 : closedAt 1 rM.e = true) (hcb : closedAt 0 (lendCb rM.e).1 = true)
    (h : overlapOK T (Fam.deadStrict T).u (oneL T k) = true) :
    Res Δ T (.comp (effOf S (.tensor (.array A) B))) :=
  let dM := (rM.F.d _ (btw_allL _ _ _ rM.F.hu rM.F.hw hL)).2
  let J : Jdg := .comp (effOf S (.tensor (.array A) B))
  let JL : Jdg := .comp (.arr (.array A) (effOf S (.tensor (.array A) B)))
  let tR : TExpr := .lendRF i J x b A B S (.dtor i (.val (.lolli (.array A) .unit)) (.array A)) rM.t
  let hR1 : TDerivesP Δ [⟨.array A, true⟩] tR J :=
    .lendRF hb hx hbx hΔx hT hB hBn hside hsideB hS hM1 hcb hdc (.dtor hdt hdc hde .nil) dM
  let rL : Res Δ T JL :=
    ⟨.nilDead i JL JL (.lam i JL (.array A) (effOf S (.tensor (.array A) B)) tR), rM.sigs, q :: rM.pins,
      (Fam.deadStrict T).map fun _ hd => TTied.pinned q (.nilDead hd (.lam hR1))⟩
  rApp i rL k hk h

/-- `LendSide kv Δ A`, decided: `A` scoped (`imm`), or `A ⊒ @b` (`mut`). -/
def lendSideW (sp : Span) (kv : Bool) (b : CLife) (A : CVTy) :
    Except Error (PLift (LendSide kv Δ A)) :=
  match kv with
  | true =>
    if hsc : scopedB Δ A = true then
      pure ⟨by simpa [LendSide] using scopedB_sound hsc⟩
    else throw ⟨sp, s!"`{ppVTy A}` mentions a lifetime not in scope"⟩
  | false => do
    let ⟨h⟩ ← outlivesWitness (Δ := Δ) sp b A
    pure ⟨by simpa [LendSide] using h⟩

/-- **W-tick** (`CDerivesP.lendRT`, the #743 spike) at the slot `k : ref A`: `rLendR` (`kv =
false`) or `rLendRI` (`kv = true`) at a row that may hold `Div`'s `tick`.  `[spec §29]` -/
def rLendRT (i : TInfo) {A B : CVTy} {S : CRow} (q : Pin) (kv : Bool) (x : LifeVar) (b : CLife)
    (k : Nat) (hk : T[k]? = some (.ref A)) (hb : Δ.Defines b) (hx : Δ.find? x = none)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x A) (hB : ¬ VFree x B) (hBn : NoThunkT B) (hside : LendSide kv Δ A)
    (hS : BoCa.Fig16.LogRel.Core.Row.ResumeOE S x)
    (hdt : HasDtor (.ref A)) (hdc : closedAt 0 (dtorE (.ref A)) = true)
    (hde : (dtorE (.ref A)).effFree = true)
    (rM : Res (Δ.extend x b) [lendView kv x A] (.comp (effOf S (.box (.var x) B))))
    (hL : subL (allL [lendView kv x A]) (orL rM.F.u rM.F.w) = true)
    (hM1 : closedAt 1 rM.e = true) (hcb : closedAt 0 (lendCb rM.e).1 = true)
    (h : overlapOK T (Fam.deadStrict T).u (oneL T k) = true) :
    Res Δ T (.comp (effOf S (.tensor (.ref A) B))) :=
  let dM := (rM.F.d _ (btw_allL _ _ _ rM.F.hu rM.F.hw hL)).2
  let J : Jdg := .comp (effOf S (.tensor (.ref A) B))
  let JL : Jdg := .comp (.arr (.ref A) (effOf S (.tensor (.ref A) B)))
  let tR : TExpr := .lendRT i J x b A B S (.dtor i (.val (.lolli (.ref A) .unit)) (.ref A)) rM.t
  let hR1 : TDerivesP Δ [⟨.ref A, true⟩] tR J :=
    .lendRT kv hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc (.dtor hdt hdc hde .nil) dM
  let rL : Res Δ T JL :=
    ⟨.nilDead i JL JL (.lam i JL (.ref A) (effOf S (.tensor (.ref A) B)) tR), rM.sigs, q :: rM.pins,
      (Fam.deadStrict T).map fun _ hd => TTied.pinned q (.nilDead hd (.lam hR1))⟩
  rApp i rL k hk h

/-- **W-hold** (`CDerivesP.lendRH`, the #743 spike) at the slot `k : ref A`: `rLendRT` with the
body checked at `Δ, 'x ⊏ @b, 'y ⊏ 'x`, the nursery scope `'y`.  `[spec §29]` -/
def rLendRH (i : TInfo) {A B : CVTy} {S : CRow} (q : Pin) (kv : Bool) (x y : LifeVar)
    (b : CLife) (k : Nat) (hk : T[k]? = some (.ref A)) (hb : Δ.Defines b) (hx : Δ.find? x = none)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hy : (Δ.extend x b).find? y = none)
    (hΔy : ∀ z u, (Δ.extend x b).find? z = some u → u.mentions y = false)
    (hT : ¬ VFree x A) (hB : ¬ VFree x B) (hyT : ¬ VFree y A) (hyB : ¬ VFree y B)
    (hBn : NoThunkT B) (hside : LendSide kv Δ A) (hS : BoCa.Fig16.LogRel.Core.Row.ResumeOE S x)
    (hdt : HasDtor (.ref A)) (hdc : closedAt 0 (dtorE (.ref A)) = true)
    (hde : (dtorE (.ref A)).effFree = true)
    (rM : Res ((Δ.extend x b).extend y (.var x)) [lendView kv x A]
      (.comp (effOf S (.box (.var x) B))))
    (hL : subL (allL [lendView kv x A]) (orL rM.F.u rM.F.w) = true)
    (hM1 : closedAt 1 rM.e = true) (hcb : closedAt 0 (lendCb rM.e).1 = true)
    (h : overlapOK T (Fam.deadStrict T).u (oneL T k) = true) :
    Res Δ T (.comp (effOf S (.tensor (.ref A) B))) :=
  let dM := (rM.F.d _ (btw_allL _ _ _ rM.F.hu rM.F.hw hL)).2
  let J : Jdg := .comp (effOf S (.tensor (.ref A) B))
  let JL : Jdg := .comp (.arr (.ref A) (effOf S (.tensor (.ref A) B)))
  let tR : TExpr := .lendRH i J x b A B S y (.dtor i (.val (.lolli (.ref A) .unit)) (.ref A)) rM.t
  let hR1 : TDerivesP Δ [⟨.ref A, true⟩] tR J :=
    .lendRH kv y hb hx hbx hΔx hy hΔy hT hB hyT hyB hBn hside hS hM1 hcb hdc
      (.dtor hdt hdc hde .nil) dM
  let rL : Res Δ T JL :=
    ⟨.nilDead i JL JL (.lam i JL (.ref A) (effOf S (.tensor (.ref A) B)) tR), rM.sigs, q :: rM.pins,
      (Fam.deadStrict T).map fun _ hd => TTied.pinned q (.nilDead hd (.lam hR1))⟩
  rApp i rL k hk h

/-- **R2** (`CDerivesP.lendLoopR`) at the slot `k : ref A`: the per-observation `imm` lend of `k`
over a loop whose state `S` may mention the lend's lifetime, its steps `rN`, `rK` checked at
`Δ, 'x ⊏ ⊓Δ` and the pair `(view, state)` alone, its first state `rs0` at the empty context. As
`rLendR`, the λ over the rule's node at the empty context, placed by `nilDead` and applied to the
slot. The core form is `lend_loop_r` (the #743 spike, `experiments/Spike743`).  `[spec §29]` -/
def rLendLoopR (i : TInfo) {A S B R : CVTy} (q : Pin) (x : LifeVar) (k : Nat)
    (hk : T[k]? = some (.ref A)) (hx : Δ.find? x = none) (hbx : Δ.meetOfDom.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hR : ¬ VFree x R) (hBn : NoThunkT B)
    (hRn : NoThunkT R) (hsc : BoCa.Fig16.LogRel.Core.VScoped Δ A)
    (rN : Res (Δ.extend x Δ.meetOfDom) [.tensor (.imm (.var x) A) S] (.comp (.ret (.sum B S))))
    (rK : Res (Δ.extend x Δ.meetOfDom) [.tensor (.imm (.var x) A) S] (.comp (.ret R)))
    (rs0 : Res (Δ.extend x Δ.meetOfDom) [] (.val S))
    (hLN : subL (allL [.tensor (.imm (.var x) A) S]) (orL rN.F.u rN.F.w) = true)
    (hLK : subL (allL [.tensor (.imm (.var x) A) S]) (orL rK.F.u rK.F.w) = true)
    (hLs0 : subL (allL []) (orL rs0.F.u rs0.F.w) = true)
    (hN1 : closedAt 1 rN.e = true) (hK1 : closedAt 1 rK.e = true)
    (hs0c : closedAt 0 rs0.e = true)
    (h : overlapOK T (Fam.deadStrict T).u (oneL T k) = true) :
    Res Δ T (.comp (BoCa.Fig16.LogRel.Core.CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R))) :=
  let dN := (rN.F.d _ (btw_allL _ _ _ rN.F.hu rN.F.hw hLN)).2
  let dK := (rK.F.d _ (btw_allL _ _ _ rK.F.hu rK.F.hw hLK)).2
  let ds0 := (rs0.F.d _ (btw_allL _ _ _ rs0.F.hu rs0.F.hw hLs0)).2
  let C : CCTy := BoCa.Fig16.LogRel.Core.CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R)
  let J : Jdg := .comp C
  let JL : Jdg := .comp (.arr (.ref A) C)
  let tR : TExpr := .lendLoopR i J x A S B R rN.t rK.t rs0.t
  let hR2 : TDerivesP Δ [⟨.ref A, true⟩] tR J :=
    .lendLoopR hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c dN dK ds0
  let rL : Res Δ T JL :=
    ⟨.nilDead i JL JL (.lam i JL (.ref A) C tR), rN.sigs ++ rK.sigs, q :: (rN.pins ++ rK.pins ++ rs0.pins),
      (Fam.deadStrict T).map fun _ hd => TTied.pinned q (.nilDead hd (.lam hR2))⟩
  rApp i rL k hk h

end

end Frontend.Check
