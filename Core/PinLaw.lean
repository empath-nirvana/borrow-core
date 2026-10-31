import Core.PinDerives

/-!
# Core — `PinLaw`, the one named hypothesis  `[spec §29]`

`docs/async-capabilities.md` §4. A borrow held across a suspension is believed sound because the
place does not move: the suspension may be read as ending the lend and the resumption as lending
the place again at a fresh lifetime. `PinLaw` asserts the compatibility lemmas of the two relaxed
rules that rely on this, and nothing more:

* `PinStop`: R1 (`lendR`), the lend of `r : Ref T` whose borrower performs resuming operations
  (`Row.ResumeO`) while the view is live, is in the kernel's relation at `F_Σ (Ref T ⊗ B)`.
* `PinLoop`: R2 (`lendLoopR`), the per-observation `imm` lend whose state may hold views of the
  place, is in the kernel's relation at `U(Loop (Ref A ⊗ B) (Ref A ⊗ R))`.

Both are stated at the rules' own premises, with every quantifier over code a quantifier over
`CDerivesP` derivations: no statement here is pointwise over configurations. The hypothesis is
tested by running programs that use the rules (`docs/async-capabilities.md` §6), not proved.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **PinStop.** R1's compatibility lemma, as a `Prop`: the relaxed lend at `r : Ref T`, whose
borrower `M` is typed in `CDerivesP` at a resuming row with the view `Mut 'x T` in its context, is
in the kernel's relation at `F_Σ (Ref T ⊗ B)`. The row is `Row.ResumeOCE`: besides resuming
operations, a cancellable `await`, so the borrower may stop, be resumed with `inr ()`, and unwind
past the lend through finalisers that stop again; and abortive operations of closed data (its
`cancelled` among them), which unwind past the lend through its finaliser `d`. -/
def PinStop : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (d M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B →
    (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T) →
    Row.ResumeOCE S x → closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
    closedAt 0 d = true → SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit) →
    CDerivesP (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δ [⟨.ref T, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor (.ref T) B))

/-- **PinLoop.** R2's compatibility lemma, as a `Prop`: the per-observation `imm` lend of
`r : Ref A` whose steps `N`, `K` and first state `s₀` are typed in `CDerivesP`, the state at a type
`S` that may mention the lend's lifetime, is in the kernel's relation at
`U(Loop (Ref A ⊗ B) (Ref A ⊗ R))`. Its content is Law 2 at an observation boundary: at the end of
each observation the `imm` lend is ended with the state holding views of the place, and the next
observation re-lends the place at a fresh lifetime, at which the state is again in the relation
because it was built by typed code. -/
def PinLoop : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (A S B R : VTy) (N K s0 : Expr),
    Δ.find? x = none → Δ.meetOfDom.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x A → ¬ VFree x B → ¬ VFree x R → NoThunkT B → NoThunkT R → VScoped Δ A →
    closedAt 1 N = true → closedAt 1 K = true → closedAt 0 s0 = true →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.comp (.ret (.sum B S))) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.comp (.ret R)) →
    CDerivesP (Δ.extend x Δ.meetOfDom) [] s0 (.val S) →
    SemC (ℍ := ℍ) Δ [⟨.ref A, true⟩] (lendLoopApp A B R N K s0)
      (CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R))

/-- **W-imm** (the #743 spike, P8): `lendRI`'s compatibility lemma. `PinStop` with the view
`Imm 'x T` and `withbor1U`'s scoping of `T` in place of `withbor2U`'s side condition. -/
def PinStopImm : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (d M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B → VScoped Δ T →
    Row.ResumeO S x → closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
    closedAt 0 d = true → SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit) →
    CDerivesP (Δ.extend x b) [⟨.imm (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δ [⟨.ref T, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor (.ref T) B))

/-- **W-nest** (the #743 spike, P10): `lendRF`'s compatibility lemma. `PinStop` at an owned
array lent as the family `[Mut 'x A]`, with `sliceBorrowMU`'s side conditions. Nested relaxed
lends at any depth are in its premise's `CDerivesP` derivation (`nilDead`), not in a clause of
the statement. -/
def PinNest : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (A B : VTy) (d M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x A → ¬ VFree x B → NoThunkT B →
    (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' A) → (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' B) →
    Row.ResumeO S x → closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
    closedAt 0 d = true → SemV (ℍ := ℍ) Δ [] d (.lolli (.array A) .unit) →
    CDerivesP (Δ.extend x b) [⟨VTy.sliceMut (.var x) A, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δ [⟨.array A, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor (.array A) B))

/-- **W-tick** (the #743 spike, P1's shape and #750's nursery): `lendRT`'s compatibility lemma.
`PinStop` (`k = false`) and `PinStopImm` (`k = true`) at `Row.ResumeOE`: the callback's row may
also hold `Div`'s `tick` beside `PinStop`'s cancellable `await` and escaping errors. The conclusion
is `SemC` at that row, which is the relation the kernel already gives a row holding `Div`
(`cC_effOf_wp`: `cwp`, not `ewpTS`). -/
def PinStopTick : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (d M : Expr) (S : Row) (k : Bool),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B → LendSide k Δ T →
    Row.ResumeOE S x → closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
    closedAt 0 d = true → SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit) →
    CDerivesP (Δ.extend x b) [⟨lendView k x T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δ [⟨.ref T, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor (.ref T) B))

/-- **W-hold** (the #743 spike, #750's nursery): `lendRH`'s compatibility lemma. `PinStopTick`
with the callback typed at a second fresh lifetime `'y ⊏ 'x`, the nursery scope: what is boxed at
`'y` may hold views at `'x` across the callback's stops, and `'y` is free in `T` and `B`. -/
def PinStopHold : Prop :=
  ∀ (Δ : LifeCtx) (x y : LifeVar) (b : Lifetime.Life) (T B : VTy) (d M : Expr) (S : Row)
    (k : Bool),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (Δ.extend x b).find? y = none →
    (∀ z u, (Δ.extend x b).find? z = some u → u.mentions y = false) →
    ¬ VFree x T → ¬ VFree x B → ¬ VFree y T → ¬ VFree y B → NoThunkT B → LendSide k Δ T →
    Row.ResumeOE S x → closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
    closedAt 0 d = true → SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit) →
    CDerivesP (Δ.extend x b |>.extend y (.var x)) [⟨lendView k x T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    SemC (ℍ := ℍ) Δ [⟨.ref T, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
      (CTy.effOf S (.tensor (.ref T) B))

/-- **PinFin.** `[then]`'s compatibility lemma with `Div` admitted in the finaliser's row
(`CDerivesP.effThenDiv`): `then_compatC` without `hSD`, at a body `M` whose row has no capturable
operation. Where `Σ_D` holds `Div`, `Σ` does, and the relation at `Σ` is `cwp`: the finaliser's
run is a greatest fixed point of segments, run on the ordinary unwind. `hcap` keeps every
finaliser off a cancel run, whose obligation (`cancelObl`) is a least fixed point. -/
def PinFin : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M N D : Expr) (A B : VTy) (S SM SD : Row),
    Ctx.SplitP Γ Γ₁ Γ₂ → S.NZ → (S.UnrD → Ctx.Banged Γ₂) → RowLe SM S → RowLe SD S →
    (∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      o.finRead = true → ThenLe o.fin SD o'.fin) →
    (SD.UnrD → SM.PendPers) → (∀ o ∈ SM, capB o.q o.B = false) →
    SemC (ℍ := ℍ) Δ Γ₁ M (CTy.effOf SM A) →
    SemC (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B) →
    SemC (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf SD .unit) →
    SemC (ℍ := ℍ) Δ Γ (thenE N D M) (CTy.effOf S B)

/-- `PinFin` at a finaliser row without `Div` is `then_compatC`: the field asserts only the
rows that hold `Div`. -/
theorem pinFin_divFree {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N D : Expr} {A B : VTy}
    {S SM SD : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      o.finRead = true → ThenLe o.fin SD o'.fin)
    (hP : SD.UnrD → SM.PendPers) (hSD : Row.divB SD = false)
    (hM : SemC (ℍ := ℍ) Δ Γ₁ M (CTy.effOf SM A))
    (hN : SemC (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B))
    (hD : SemC (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ₂) D (CTy.effOf SD .unit)) :
    SemC (ℍ := ℍ) Δ Γ (thenE N D M) (CTy.effOf S B) :=
  then_compatC hs hNZ hU hMS hDS (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂
    (OpSig.finRead_of_capB hc)) hP hSD hM hN hD

/-- **PinLaw**: the one named assumption. Its fields are stated over `CDerivesP` derivations
and the kernel's relation only. -/
structure PinLaw : Prop where
  /-- R1: the lend held across resuming operations, and across the cancel path, is in the
  relation. -/
  stop : PinStop (ℍ := ℍ)
  /-- R2: the lend over a loop whose state holds the borrow is in the relation. -/
  loop : PinLoop (ℍ := ℍ)
  /-- W-imm (the #743 spike): R1 at an `imm` view. -/
  stopImm : PinStopImm (ℍ := ℍ)
  /-- W-nest (the #743 spike): R1 at an owned array's family of `mut` leaves. -/
  nest : PinNest (ℍ := ℍ)
  /-- W-tick (the #743 spike): R1 and W-imm at a row holding `Div`'s `tick`. -/
  tick : PinStopTick (ℍ := ℍ)
  /-- W-hold (the #743 spike): R1 and W-imm with a nursery scope `'y ⊏ 'x`. -/
  hold : PinStopHold (ℍ := ℍ)

  /-- `[then]` with a finaliser that may loop is in the relation. -/
  fin : PinFin (ℍ := ℍ)

/-! ### The cancel row where termination matters

A cancel at a cancellable operation is a resume with `inr ()`; what it runs before the handler's
`cancelled` clause is the finalisers between the operation and the handler, whose rows `[then]`
records in the operation's cancel row (`hfin`, `ThenLe`), `Div` included. A cancel that must end
(a bounded scheduler's cancel-at-budget, `run_in`) asks for its tasks' row `Row.CancelTotal`.
That such a cancel ends is open, as decision 69's "finalisers are total" is. -/

/-- Every cancellable or capturable operation of the row has a cancel row that is not `⊤` and does
not hold `Div`.  `[spec §29a]` -/
def Row.CancelTotal (S : Row) : Prop :=
  ∀ o ∈ S, o.finRead = true → o.fin.isTop = false ∧ Row.divB o.fin.rowOf = false


/-! ### The rows a relaxed lend admits

`Row.ResumeO` is satisfiable by the operations a task performs inside a relaxed lend: the
scheduler's `await : 1 ↠^cancel 1` and the generator's `yield : i32 ↠^cancel 1`. An abortive
operation is outside it. -/

/-- `await : 1 ↠^cancel 1` at the name `1`. -/
def pinAwaitSig : OpSig := ⟨1, 0, .cancel, .unit, .unit, .ret .unit⟩

/-- `yield : i32 ↠^cancel 1` at the name `2`. -/
def pinYieldSig : OpSig := ⟨2, 0, .cancel, .int .w32, .unit, .ret .unit⟩

/-- `raise : i32 ↠^cancel 0`, abortive. -/
def pinRaiseSig : OpSig := ⟨3, 0, .cancel, .int .w32, .zero, .ret .unit⟩

theorem resumeO_await_yield (x : LifeVar) : Row.ResumeO [pinAwaitSig, pinYieldSig] x := by
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · refine ⟨rfl, by decide, rfl, rfl, by decide, fun h => by simp [pinAwaitSig, VFree] at h, fun _ _ => .unit, trivial⟩
  · refine ⟨rfl, by decide, rfl, rfl, by decide, fun h => by simp [pinYieldSig, VFree] at h, fun _ _ => .int, trivial⟩

theorem not_resumeO_raise (x : LifeVar) : ¬ Row.ResumeO [pinRaiseSig] x := by
  intro h
  have := (h pinRaiseSig (by simp)).1
  simp [OpSig.abort, pinRaiseSig, VTy.isZero] at this

end BoCa.Fig16.LogRel.Core

end
