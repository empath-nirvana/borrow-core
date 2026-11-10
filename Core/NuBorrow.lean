import Core.Fundamental

/-!
# Core — codata whose observations take borrowed arguments  `[spec §7, §22]`

A protocol object `File^c = νX. ((∀'x ⊏ ⊤. Mut 'x I32 ⊸ F(I32 ⊗ [@c] U X))
& (∀'x ⊏ ⊤. Imm 'x I32 ⊸ F(I32 ⊗ [@c] U X))) & F I32`: `read` is lent a buffer `mut` for one
call, `write` one `imm`, and `close` ends it.  Each observation quantifies the borrow's lifetime
(`CTy.NuLeaf`'s `∀` case), and the rest it hands back is boxed at the object's bound `@c`, so the
object outlives the lend its call is made in.

* `fileBody_nuOk`: the body is positive, its binder fresh for it.
* `d_fileRead`, `d_fileWrite`: a call of each observation through `nuOut`, the projections and
  `∀E` at the lend's lifetime, a `CDerives` derivation; `fundamentalC` covers both
  (`fileRead_sem`, `fileWrite_sem`).
* The type each call answers is `I32 ⊗ [@c] File^c` itself: `∀E` at the lend's lifetime leaves
  the rest's type unchanged (`fileRead_inst`, `fileWrite_inst`), since `'x` is not free in it.

The runs, through a lend of the buffer and back, are `corpus/nu-file-read.bc`,
`corpus/nu-file-twice.bc` and `corpus/nu-file-consumed.bc`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The buffer's payload. -/
abbrev bufT : VTy := .int .w32

/-- The rest, boxed at `@c`. -/
abbrev fileRest (c : Lifetime.Life) : VTy := .tensor bufT (.box c (.tvar 0))

/-- `read : ∀'x ⊏ ⊤. Mut 'x I32 ⊸ F(I32 ⊗ [@c] U X)`. -/
abbrev fileReadObs (x : LifeVar) (c : Lifetime.Life) : CTy :=
  .all x .top (.arr (.mut (.var x) bufT) (.ret (fileRest c)))

/-- `write : ∀'x ⊏ ⊤. Imm 'x I32 ⊸ F(I32 ⊗ [@c] U X)`. -/
abbrev fileWriteObs (x : LifeVar) (c : Lifetime.Life) : CTy :=
  .all x .top (.arr (.imm (.var x) bufT) (.ret (fileRest c)))

/-- The body of `File^c`, its observations' binder `'x`. -/
abbrev fileBody (x : LifeVar) (c : Lifetime.Life) : CTy :=
  .amp (.amp (fileReadObs x c) (fileWriteObs x c)) (.ret bufT)

/-- `U(File^c)`. -/
abbrev fileT (x : LifeVar) (c : Lifetime.Life) : VTy := .thunk (.nu (fileBody x c))

/-- **Positivity**: at a bound `@c` that does not mention the binder. -/
theorem fileBody_nuOk {x : LifeVar} {c : Lifetime.Life} (hc : c.mentions x = false) :
    (fileBody x c).NuOk := by
  refine ⟨⟨⟨⟨trivial, fun h => h, trivial⟩, ⟨trivial, fun h => h, trivial⟩⟩, fun h => h⟩, ?_⟩
  intro y hy
  have hxy : y = x := by
    simp only [CTy.LeafBinds] at hy
    rcases hy with (h | h) | h
    · rcases h with h | h
      · exact h.symm
      · exact h.elim
    · rcases h with h | h
      · exact h.symm
      · exact h.elim
    · exact h.elim
  subst hxy
  simp [CFree, VFree, Lifetime.Life.mentions, hc]

/-! ### The calls, at the binder `'1`, the bound `'0` and the lend's lifetime `'2` -/

/-- `∀E` at the lend's lifetime leaves the rest's type `File^c`: `read`. -/
theorem fileRead_inst :
    ((CTy.arr (.mut (.var 1) bufT) (.ret (fileRest (.var 0)))).instT
        (fileT 1 (.var 0))).instLife 1 (.var 2)
      = .arr (.mut (.var 2) bufT) (.ret (.tensor bufT (.box (.var 0) (fileT 1 (.var 0))))) := by
  decide

/-- `∀E` at the lend's lifetime leaves the rest's type `File^c`: `write`. -/
theorem fileWrite_inst :
    ((CTy.arr (.imm (.var 1) bufT) (.ret (fileRest (.var 0)))).instT
        (fileT 1 (.var 0))).instLife 1 (.var 2)
      = .arr (.imm (.var 2) bufT) (.ret (.tensor bufT (.box (.var 0) (fileT 1 (.var 0))))) := by
  decide

theorem fileBody_nuOk₁ : (fileBody 1 (.var 0)).NuOk := fileBody_nuOk rfl

/-- `f π₁ π₁ [] m`: `read` through the unrolling. -/
def fileReadE : Expr :=
  .app (.app (.app (.app (.var 1) (.val (.inj₁ .unit))) (.val (.inj₁ .unit))) (.val .unit)) (.var 0)

/-- `f π₁ π₂ [] b`: `write` through the unrolling. -/
def fileWriteE : Expr :=
  .app (.app (.app (.app (.var 1) (.val (.inj₁ .unit))) (.val (.inj₂ .unit))) (.val .unit)) (.var 0)

/-- **`read` called inside a lend**: with `m : Mut '2 I32` the lent buffer and `f : File^'0`,
`f π₁ π₁ [] m : F(I32 ⊗ [@'0] File^'0)`, the rest outliving the lend's `'2`. -/
theorem d_fileRead {Δ : LifeCtx} (hlt : Δ.EntailsLt (.var 2) .top) :
    CDerives Δ [⟨.mut (.var 2) bufT, true⟩, ⟨fileT 1 (.var 0), true⟩] fileReadE
      (.comp (.ret (.tensor bufT (.box (.var 0) (fileT 1 (.var 0)))))) := by
  have hf : CDerives Δ [⟨.mut (.var 2) bufT, false⟩, ⟨fileT 1 (.var 0), true⟩] (.var 1)
      (.comp (.nu (fileBody 1 (.var 0)))) :=
    .force (T := .thunk _) (C := .nu (fileBody 1 (.var 0))) (.there (.here .nil)) rfl
  have hu := CDerives.nuOut fileBody_nuOk₁ hf
  have hp := CDerives.allE (CDerives.proj₁ (CDerives.proj₁ hu)) hlt
  rw [fileRead_inst] at hp
  exact .app (.right (.left .nil)) hp (.here (.cons .nil))

/-- **`write` called inside a lend**: with `b : Imm '2 I32` and `f : File^'0`,
`f π₁ π₂ [] b : F(I32 ⊗ [@'0] File^'0)`. -/
theorem d_fileWrite {Δ : LifeCtx} (hlt : Δ.EntailsLt (.var 2) .top) :
    CDerives Δ [⟨.imm (.var 2) bufT, true⟩, ⟨fileT 1 (.var 0), true⟩] fileWriteE
      (.comp (.ret (.tensor bufT (.box (.var 0) (fileT 1 (.var 0)))))) := by
  have hf : CDerives Δ [⟨.imm (.var 2) bufT, false⟩, ⟨fileT 1 (.var 0), true⟩] (.var 1)
      (.comp (.nu (fileBody 1 (.var 0)))) :=
    .force (T := .thunk _) (C := .nu (fileBody 1 (.var 0))) (.there (.here .nil)) rfl
  have hu := CDerives.nuOut fileBody_nuOk₁ hf
  have hp := CDerives.allE (CDerives.proj₂ (CDerives.proj₁ hu)) hlt
  rw [fileWrite_inst] at hp
  exact .app (.right (.left .nil)) hp (.here (.cons .nil))

/-- `fundamentalC` at the `read` call. -/
theorem fileRead_sem {Δ : LifeCtx} (hlt : Δ.EntailsLt (.var 2) .top) :
    SemC (ℍ := ℍ) Δ [⟨.mut (.var 2) bufT, true⟩, ⟨fileT 1 (.var 0), true⟩] fileReadE
      (.ret (.tensor bufT (.box (.var 0) (fileT 1 (.var 0))))) :=
  fundamentalC (d_fileRead hlt)

/-- `fundamentalC` at the `write` call. -/
theorem fileWrite_sem {Δ : LifeCtx} (hlt : Δ.EntailsLt (.var 2) .top) :
    SemC (ℍ := ℍ) Δ [⟨.imm (.var 2) bufT, true⟩, ⟨fileT 1 (.var 0), true⟩] fileWriteE
      (.ret (.tensor bufT (.box (.var 0) (fileT 1 (.var 0))))) :=
  fundamentalC (d_fileWrite hlt)

end BoCa.Fig16.LogRel.Core

end
