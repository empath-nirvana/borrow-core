import GhostEnd.Handle
import Core.Examples

/-!
# GhostEnd — a lend spanning two yields, every hypothesis discharged

    withbor ℓ (Λ. λm. perform yield 1; perform yield 2; return forget to fg. fg m to z. return z)

at the row `{yield : I32 ↠ 1}` with a linear, resuming `yield`. The borrower holds `m` across both
yields and uses it after the second resumption. `spans_two_yields` is `withbor_spans_yields_cC`
with every hypothesis discharged: the shape is not vacuous, and it arises in this program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd.Instance
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `return forget to fg. fg m to z. return z`, with `m` at index `0`. -/
def nfEx : Expr := bindE forget (bindE (.app (.var 0) (.var 1)) (.var 0))

theorem d_nfEx :
    CDerives Δ₁ [⟨.mut (.var 0) .unit, true⟩] nfEx (.comp (.ret (.box (.var 0) .unit))) :=
  .bind (.right .nil) (.ret (.forgetMut (a := .var 0) (A := .unit) (.cons .nil)))
    (.bind (.left (.left .nil))
      (.app (.left (.right .nil)) (.force (.here (.cons .nil))) (.there (.here .nil)))
      (.ret (.boxI (.var (.here (.cons (.cons .nil))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (.cons .nil))))))

/-- `yield : I32 ↠ 1`, linear and resuming. -/
def yieldOp : OpSig := ⟨7, 0, .lin, .int .w32, .unit, .ret .unit⟩

/-- The payloads. -/
def ys : List Val := [Val.i32 1, Val.i32 2]

/-- **A lend spanning two yields.** From `ℓ ↦ v ⋆ 𝒱⟦1⟧(v)`, the program is in
`𝒞⟦F_{yield} (Ref 1 ⊗ 1)⟧`, at every assignment and record list. -/
theorem spans_two_yields (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true .unit ls δ v)
      (cC (CTy.effOf [yieldOp] (.tensor (.ref .unit) .unit)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val (cbV yieldOp.n yieldOp.i ys nfEx)))) := by
  have hδ : LifeCtx.empty.Models δ := fun x u h => by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  obtain ⟨β, hβ⟩ : ∃ β, LifeCtx.empty.meetOfDom.interp δ = some β :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)
  refine withbor_spans_yields_cC (Δ := LifeCtx.empty) (x := 0) hδ (by decide)
    (fun y u h => by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h) hβ
    (by simp [VFree]) (by simp [VFree]) (βP := ⊤) ?_ (by decide) d_nfEx
    [yieldOp] yieldOp (by simp [Row.find, yieldOp]) (by decide) rfl rfl ys
    (by simp [ys]; decide) ?_ l v ls
  · intro ls w σ h
    rw [h.1]; exact ResU.inStratum_empty _
  · intro y hy ls
    simp only [ys, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨rfl, 1, rfl⟩
    · exact ⟨rfl, 2, rfl⟩

/-- The same program as a semantic judgment at `r : Ref 1`, ready for the kernel's `[handle]`. -/
theorem spans_two_yields_sem :
    SemC LifeCtx.empty [⟨.ref .unit, true⟩]
      (.app (.app withbor (.var 0)) (.val (cbV yieldOp.n yieldOp.i ys nfEx)))
      (CTy.effOf [yieldOp] (.tensor (.ref .unit) .unit)) :=
  withbor_spans_yields_sem (x := 0) (LifeCtx.defines_of_wf rfl) (by decide)
    (fun y u h => by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h)
    (by simp [VFree]) (by simp [VFree])
    ⟨LifeCtx.empty.meetOfDom, LifeCtx.defines_of_wf rfl, .unit⟩ (by decide) d_nfEx
    [yieldOp] yieldOp (by simp [Row.find, yieldOp]) (by decide) rfl rfl ys
    (by simp [ys]; decide)
    (fun δ y hy ls => by
      simp only [ys, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact ⟨rfl, 1, rfl⟩
      · exact ⟨rfl, 2, rfl⟩)
    (by decide)

end GhostEnd.Instance
