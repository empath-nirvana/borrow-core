import Core.ResourceSafety
import Core.EffBorrow
import Core.Consume
import Core.Classes
import Core.Records
import Core.EffFin

/-!
# ExnGlue — the source fragment  `[spec §12, §19]`

A source language with exceptions in which owned values may be in scope at a raise
(`docs/new-core/scope-804.md` §1). It is the kernel's computations at rows of exception
operations, with the consume glue left out: a `let` whose head may raise and a `raise` abandon
their context as written, and the borrow block `borrowI` lends a `Ref` to a callback that may
raise.

* **Exception operations** (`ExnRow`): abortive at `cancel` (answer `0`), unmarked, names nonzero
  and keys unique, and the payload holds no owned cell (`VTy.OwnFree`, `[raise]`'s `hd`).
* **Values** are the kernel's: a source value is a `CDerives` value derivation.
* **Annotations.** `letv` and `raise` carry the context the abort abandons (`R`), so the
  translation reads the consumes off the term; the rule ties `R` to the split.
* **Handlers** (`try`) see only the slots of a `!` context, as `[handle]`'s handler value does.

No hypothesis of a rule stands in for a fact: each is read off the program (a split, a row, a
type's class), and a checker decides it (`Frontend/Check/Decide.lean`'s `ownFreeB`,
`Row.uniqB`, `Row.unwindB`; `consumableB`).
-/

namespace ExnGlue
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

/-- The row of a `try` of the name `n` at payload `P` around a body at the outer row `S`: the
exception operation `(n, 0)`, abortive at `cancel`, ahead of `S`. -/
abbrev exnRow (n : UInt32) (P : VTy) (S : Row) : Row := Row.ofEff n [(.cancel, P, .zero)] 0 ++ S

/-- A row of exception operations: names nonzero, keys unique, and each operation abortive at
`cancel`, unmarked, with a payload that holds no owned cell. -/
def ExnRow (S : Row) : Prop :=
  S.NZ ∧ S.Uniq ∧ ∀ o ∈ S, o.q = .cancel ∧ o.B = .zero ∧ o.rc = false ∧ o.A.OwnFree

/-- Every live slot of `Γ` is at a type that is consumable (SPEC §12). -/
def ConsumableLive (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → Consumable s.ty

/-- Source terms. Values are kernel expressions; `R` is the context an abort abandons. -/
inductive STm where
  /-- `return V`. -/
  | ret (V : Expr)
  /-- `x ← M; N`, the rest's context `R`. -/
  | letv (R : Ctx VTy) (M N : STm)
  /-- `let (x, y) = V; M`. -/
  | letp (V : Expr) (M : STm)
  /-- `raise_n V`, abandoning `R`. -/
  | raise (n : UInt32) (R : Ctx VTy) (V : Expr)
  /-- `try_n M with (x. Nr) (e. Ne)`. -/
  | tryCatch (n : UInt32) (Nr Ne M : STm)
  /-- `borrow xᵢ as m in M`: the `Ref A` in slot `i` lent as `Imm 'x A` to `M`. -/
  | borrowI (A : VTy) (i : Nat) (M : STm)

/-- **The source judgment**: `Γ ⊢ t : F_Σ A` at an exception row.  `[spec §19]` -/
inductive SDerives : LifeCtx → Ctx VTy → STm → Row → VTy → Prop where
  | ret {Δ Γ V S A} (h : CDerives Δ Γ V (.val A)) : SDerives Δ Γ (.ret V) S A
  /-- `x ← M; N` with no condition on what an abort of `M` abandons beyond its consumability. -/
  | letv {Δ Γ Γ₁ Γ₂ R M N S A B} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hR : R = Γ₂) (hS : ExnRow S)
      (hC : ConsumableLive Γ₂) (hM : SDerives Δ Γ₁ M S A)
      (hN : SDerives Δ (⟨A, true⟩ :: Γ₂) N S B) : SDerives Δ Γ (.letv R M N) S B
  | letp {Δ Γ Γp Γb V M S A B C} (hs : Ctx.SplitP Γ Γp Γb)
      (hV : CDerives Δ Γp V (.val (.tensor A B)))
      (hM : SDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M S C) : SDerives Δ Γ (.letp V M) S C
  /-- `raise_n V`, the rest `Γᵣ` abandoned. -/
  | raise {Δ Γ Γv Γr R n V S B} {o : OpSig} (hs : Ctx.SplitP Γ Γv Γr) (hR : R = Γr)
      (hS : ExnRow S) (hC : ConsumableLive Γr) (hf : Row.find S n 0 = some o)
      (hV : CDerives Δ Γv V (.val o.A)) : SDerives Δ Γ (.raise n R V) S B
  /-- `try_n M with (x. Nr) (e. Ne)`: the arms see their binder and a `!` context. -/
  | tryCatch {Δ Γ Γh Γb n P Nr Ne M S A R} (hs : Ctx.SplitP Γ Γh Γb) (hB : Ctx.Banged Γh)
      (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hS : ExnRow (exnRow n P S))
      (hM : SDerives Δ Γb M (exnRow n P S) A)
      (hr : SDerives Δ (⟨A, true⟩ :: Γh) Nr S R) (he : SDerives Δ (⟨P, true⟩ :: Γh) Ne S R) :
      SDerives Δ Γ (.tryCatch n Nr Ne M) S R
  /-- `borrow xᵢ as m in M` at a fresh `'x ⊏ ⊓Δ`: the callback at `Σ`, which may raise
  (`Row.Unwind`), its answer boxed at `'x`; the callback captures `Γc`. -/
  | borrowI {Δ Γ Γc Γv A B i M S} (x : LifeVar) (hs : Ctx.SplitP Γ Γc Γv)
      (hi : Ctx.SoloP Γv i (.ref A)) (hA : Consumable A) (hΔ : Δ.Ok) (hx : Δ.find? x = none)
      (hsc : VScoped Δ A) (hfA : ¬ VFree x A) (hfB : ¬ VFree x B) (hU : S.Unwind x)
      (hΓx : ∀ s ∈ Γc, s.live = true → ¬ VFree x s.ty)
      (hM : SDerives (Δ.extend x Δ.meetOfDom) (⟨.imm (.var x) A, true⟩ :: ⟨.unit, false⟩ :: Γc)
        M S (.box (.var x) B)) :
      SDerives Δ Γ (.borrowI A i M) S (.tensor (.ref A) B)

/-! ### Exception rows -/

theorem ExnRow.abort {S : Row} (h : ExnRow S) : ∀ o ∈ S, o.abort = true := by
  intro o ho
  obtain ⟨hq, hB, -⟩ := h.2.2 o ho
  simp [OpSig.abort, hq, hB, VTy.isZero]

theorem ExnRow.not_unrD {S : Row} (h : ExnRow S) : ¬ S.UnrD := by
  rintro ⟨o, ho, hu⟩
  obtain ⟨hq, hB, -⟩ := h.2.2 o ho
  rcases hu with hu | ⟨hc, -⟩
  · rw [hq] at hu; cases hu
  · simp [capB, hB, VTy.isZero] at hc

/-- An owned payload is not in an exception row: the scope of `ExnRow`'s payload condition. -/
theorem not_exnRow_ref (n : UInt32) (A : VTy) (S : Row) : ¬ ExnRow (exnRow n (.ref A) S) := by
  intro h
  obtain ⟨-, -, -, hA⟩ := h.2.2 _ (List.mem_cons_self ..)
  cases hA

end ExnGlue
