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
in the kernel's relation at `F_Σ (Ref T ⊗ B)`. -/
def PinStop : Prop :=
  ∀ (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (d M : Expr) (S : Row),
    Δ.Defines b → Δ.find? x = none → b.mentions x = false →
    (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B →
    (∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T) →
    Row.ResumeO S x → closedAt 1 M = true → closedAt 0 (lendCb M).1 = true →
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

/-- **PinLaw**: the one named assumption. Its fields are stated over `CDerivesP` derivations
only. -/
structure PinLaw : Prop where
  /-- R1: the lend held across resuming operations is in the relation. -/
  stop : PinStop (ℍ := ℍ)
  /-- R2: the lend over a loop whose state holds the borrow is in the relation. -/
  loop : PinLoop (ℍ := ℍ)

/-! ### The rows a relaxed lend admits

`Row.ResumeO` is satisfiable by the operations a task performs inside a relaxed lend: the
scheduler's `await : 1 ↠^cancel 1` and the generator's `yield : i32 ↠^cancel 1`. An abortive operation
is outside it. -/

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
