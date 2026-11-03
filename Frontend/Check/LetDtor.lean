import Core.LetDtorSafety
import Core.LetCopy
import Frontend.Check.Steps

/-!
# Frontend — Check — the certificate of a `[let-dtor]` frame  `[spec §62]`

Where a slot live across a computation that may abort has no derived drop, the checker builds
`[then]` at the finaliser `drop_ctx` (`Steps.lean`, `thenItD`, `finalOfD`), each slot dropped by
the destructor of its type. This file states what that frame is, as a check the checker runs on
every such frame it emits, and what the check gives:

* `dropOfB`, `ctxDropsB`: `dropOf` and `ctxDrops` computed, `hasDtorB` for `HasDtor`
  (`dropOfB_eq`, `ctxDropsB_eq`);
* `frameCert decl Γ₂ D`: the finaliser `D` is `drop_ctx` of `Γ₂` by type, `dropCtxE (ctxDrops decl
  Γ₂) 1`, and each destructor is closed. Then the frame's term is `[let-dtor]`'s,
  `thenE N D M = letDT decl Γ₂ N M` (`frameCert_letDT`), so the derivation the checker's builders
  give for it is a `CDerives` derivation of `CDerives.effLetD`'s conclusion;
* **no destructor is skipped on an error exit** (`certFrame_raise`, `certFrame_cancel`): at a frame
  that passes the check, a raise or a cancel of `M` reaches the error only through `drop_ctx`, and
  every run past it ran each slot's destructor on its value, the slot bound last first
  (`letDE_raise_exit`, `letDE_cancel_exit`).

`Γ₂` is the context of the slots the rest of the computation uses (`mkCtx T u`), the slots the
finaliser drops. `decl` is the program's destructors at its opaque types, read off the checked
destructors (`declOf`).
-/

namespace Frontend.Check
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Kont raiseE opPayload cancelVal cfinE)

theorem dropOfB_eq (decl : Opaque → Option BoCa.Expr) : ∀ T : CVTy, dropOfB decl T = dropOf decl T
  | .tensor A B => by
      have ha := dropOfB_eq decl A
      have hb := dropOfB_eq decl B
      cases h1 : dropOf decl A <;> cases h2 : dropOf decl B <;> simp_all [dropOfB, dropOf]
  | .sum A B => by
      have ha := dropOfB_eq decl A
      have hb := dropOfB_eq decl B
      cases h1 : dropOf decl A <;> cases h2 : dropOf decl B <;> simp_all [dropOfB, dropOf]
  | .opq k => rfl
  | .thunk C => by
      cases C <;> simp [dropOfB, dropOf, hasDtorB_iff]
  | .unit | .zero | .unk | .bang _ | .imm _ _ | .mut _ _ | .box _ _ | .ref _ | .tvar _ | .mu _
  | .int _ | .fam _ => by simp [dropOfB, dropOf, hasDtorB_iff]

theorem ctxDropsB_eq (decl : Opaque → Option BoCa.Expr) (Γ : Ctx CVTy) :
    ctxDropsB decl Γ = ctxDrops decl Γ := by
  simp only [ctxDropsB, ctxDrops, dropOfB_eq]

theorem frameCert_D {decl : Opaque → Option BoCa.Expr} {Γ₂ : Ctx CVTy} {D : BoCa.Expr}
    (h : frameCert decl Γ₂ D = true) : D = dropCtxE (ctxDrops decl Γ₂) 1 := by
  simp only [frameCert, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, ctxDropsB_eq]

theorem frameCert_closed {decl : Opaque → Option BoCa.Expr} {Γ₂ : Ctx CVTy} {D : BoCa.Expr}
    (h : frameCert decl Γ₂ D = true) : ∀ b, some b ∈ ctxDrops decl Γ₂ → closedAt 1 b = true := by
  simp only [frameCert, Bool.and_eq_true, List.all_eq_true] at h
  intro b hb
  rw [← ctxDropsB_eq] at hb
  simpa using h.2 _ hb

/-- **A frame that passes the check is `[let-dtor]`'s**: `M then x. N unwind D` is
`letDT decl Γ₂ N M`, the term `CDerives.effLetD` types.  `[spec §62]` -/
theorem frameCert_letDT {decl : Opaque → Option BoCa.Expr} {Γ₂ : Ctx CVTy} {N D M : BoCa.Expr}
    (h : frameCert decl Γ₂ D = true) : thenE N D M = letDT decl Γ₂ N M := by
  rw [frameCert_D h]; rfl

/-- `FrameOk` at a frame that passes the check, for a closing substitution of closed values with
a value per slot. -/
theorem frameCert_frameOk {decl : Opaque → Option BoCa.Expr} {Γ₂ : Ctx CVTy} {D : BoCa.Expr} {γ : List BoCa.Val}
    (h : frameCert decl Γ₂ D = true) (hγ : ∀ v ∈ γ, closedAt 0 v.1 = true)
    (hl : Γ₂.length ≤ γ.length) : FrameOk (ctxDrops decl Γ₂) γ :=
  ⟨hγ, frameCert_closed h, by simpa [ctxDrops] using hl⟩

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- **No destructor is skipped on a raise.** At a frame that passes the check, if `M`, at the
closing values `γ`, reaches a raise `p` through a context that catches nothing of its name, the
frame reaches `drop_ctx; raise p` (`letDE_raise_run`); and every run from there to a
configuration past the chain first runs the chain to a term that takes no step, which, if it is a
value, ran each live slot's destructor on its value, the slot bound last first, before the raise
(`letDE_raise_exit`, `DropsRan`).  `[spec §62]` -/
theorem certFrame_raise {decl : Opaque → Option BoCa.Expr} {Γ₂ : Ctx CVTy} {N D M : BoCa.Expr}
    {γ : List BoCa.Val} {μ μ' : Heap} (hc : frameCert decl Γ₂ D = true)
    (hγ : ∀ v ∈ γ, closedAt 0 v.1 = true) (hl : Γ₂.length ≤ γ.length)
    (K K' : Kont) {n i : UInt32} {v : BoCa.Val} (hn : n ≠ 0) (hK : K'.Catches n = false)
    (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 γ M) μ' (K'.plug (raiseE (.val (opPayload n i v))))) :
    Steps (ℍ := ℍ) μ (K.plug (BoCa.Fig16.LogRel.substAll γ (thenE N D M))) μ'
      (K.plug (.seq (dropChain (ctxDrops decl Γ₂) γ) (raiseE (.val (opPayload n i v))))) ∧
    ∀ {μ₂ : Heap} {F : BoCa.Expr},
      Steps (ℍ := ℍ) μ' (K.plug (.seq (dropChain (ctxDrops decl Γ₂) γ)
        (raiseE (.val (opPayload n i v))))) μ₂ F →
      (∀ e, F ≠ K.plug (.seq e (raiseE (.val (opPayload n i v))))) →
      ∃ μ₁ t, Steps (ℍ := ℍ) μ' (dropChain (ctxDrops decl Γ₂) γ) μ₁ t ∧
        (∀ μ₃ t₃, ¬ Step1 (ℍ := ℍ) μ₁ t μ₃ t₃) ∧
        Steps (ℍ := ℍ) μ₁ (K.plug (.seq t (raiseE (.val (opPayload n i v))))) μ₂ F ∧
        (IsVal t → DropsRan (ℍ := ℍ) μ' (ctxDrops decl Γ₂) γ μ₁) := by
  have hok := frameCert_frameOk hc hγ hl
  rw [frameCert_letDT hc]
  exact ⟨letDE_raise_run hok K K' hn hK hM, fun hrun hF => letDE_raise_exit hok K hrun hF⟩

/-- **No destructor is skipped on a cancel**: as `certFrame_raise`, for a cancel reaching the frame
through a context that catches nothing of name `0` (`letDE_cancel_run`, `letDE_cancel_exit`).
`[spec §62]` -/
theorem certFrame_cancel {decl : Opaque → Option BoCa.Expr} {Γ₂ : Ctx CVTy} {N D M : BoCa.Expr}
    {γ : List BoCa.Val} {μ μ' : Heap} (hc : frameCert decl Γ₂ D = true)
    (hγ : ∀ v ∈ γ, closedAt 0 v.1 = true) (hl : Γ₂.length ≤ γ.length)
    (K K' : Kont) {err : Option BoCa.Val} (hK : K'.Catches 0 = false)
    (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 γ M) μ' (K'.plug (raiseE (.val (cancelVal err))))) :
    Steps (ℍ := ℍ) μ (K.plug (BoCa.Fig16.LogRel.substAll γ (thenE N D M))) μ'
      (K.plug (cfinE (cancelVal err) (dropChain (ctxDrops decl Γ₂) γ))) ∧
    ∀ {μ₂ : Heap} {F : BoCa.Expr},
      Steps (ℍ := ℍ) μ' (K.plug (cfinE (cancelVal err) (dropChain (ctxDrops decl Γ₂) γ))) μ₂ F →
      (∀ e, F ≠ K.plug (cfinE (cancelVal err) e)) →
      ∃ μ₁ t, Steps (ℍ := ℍ) μ' (dropChain (ctxDrops decl Γ₂) γ) μ₁ t ∧
        (∀ μ₃ t₃, ¬ Step1 (ℍ := ℍ) μ₁ t μ₃ t₃) ∧
        Steps (ℍ := ℍ) μ₁ (K.plug (cfinE (cancelVal err) t)) μ₂ F ∧
        (IsVal t → DropsRan (ℍ := ℍ) μ' (ctxDrops decl Γ₂) γ μ₁) := by
  have hok := frameCert_frameOk hc hγ hl
  rw [frameCert_letDT hc]
  exact ⟨letDE_cancel_run hok K K' hK hM, fun hrun hF => letDE_cancel_exit hok K hrun hF⟩

end Frontend.Check
