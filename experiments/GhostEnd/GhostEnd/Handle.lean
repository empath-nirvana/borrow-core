import GhostEnd.Program

/-!
# GhostEnd — the body under the kernel's handler

`withbor_spans_yields_sem` states the lend spanning the yields as a semantic judgment.
`r : Ref T ⊨ withbor r (Λ. λm. yield …; N_f) : F_Σ (Ref T ⊗ B)` holds at every `δ ∈ ⟦Δ⟧`, with
`Σ`'s `yield` linear and resuming. `handle_spans_yields` hands it to the kernel's `[handle]`
(`handle_compatC`) unchanged. The handler's clause receives the continuation in the kernel's
continuation type (`kTy`, through `KapRel`), exactly as for a body with no spanning lend. So what
§15 builds on a handled body (T15.6 → L15.3 → T15.4/T15.5) starts from this body as it does from
any other. Its resume half is §15's `call` clause. Its drop half needs the `close` clause at an
affine `yield`, and the yield here is linear.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The lend spanning the yields, as a semantic judgment** at `r : Ref T`. The owner is the
context's `Ref T`. The side condition `Δ ⊢ T ⊒ @b′` gives 6.65's premise, as in
`withbor2_compatX`. -/
theorem withbor_spans_yields_sem {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life}
    (hb : Δ.Defines b) (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T)
    {Nf : Expr} (hNf : closedAt 1 Nf = true)
    (hN : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.comp (.ret (.box (.var x) B))))
    (S : Row) (o : OpSig) (hf : Row.find S o.n o.i = some o) (ha : o.abort = false)
    (hq : o.q = .lin) (hoB : o.B = .unit)
    (ys : List Val) (hys : ∀ y ∈ ys, closedAt 0 y.1 = true)
    (hy : ∀ δ, ∀ y ∈ ys, ∀ ls, vC true o.A ls δ y PMap.empty)
    (hcb : closedAt 0 (cbV o.n o.i ys Nf).1 = true) :
    SemC Δ [⟨.ref T, true⟩] (.app (.app withbor (.var 0)) (.val (cbV o.n o.i ys Nf)))
      (CTy.effOf S (.tensor (.ref T) B)) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  cases γ with
  | nil => exact absurd hlen (by simp [Ctx.LiveWithin])
  | cons vr γ' =>
    obtain ⟨ρ₁, ρ₂, hc, hv, hρ₂, -⟩ := hgs
    subst hρ₂
    obtain rfl : ρ = ρ₁ := ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)
    obtain ⟨ℓ, v', hs⟩ := hv
    obtain ⟨rfl, hrest⟩ := pure_sep_iff.mp hs
    have hsub : substAll (Val.loc ℓ :: γ') (.app (.app withbor (.var 0)) (.val (cbV o.n o.i ys Nf)))
        = .app (.app withbor (.val (.loc ℓ))) (.val (cbV o.n o.i ys Nf)) := by
      have hw : Expr.psub 0 (Val.loc ℓ :: γ') withbor = withbor :=
        psub_closedAt withbor (k := 0) _ (by decide) le_rfl
      have hc' : Expr.psub 0 (Val.loc ℓ :: γ') (cbV o.n o.i ys Nf).1 = (cbV o.n o.i ys Nf).1 :=
        psub_closedAt _ _ hcb le_rfl
      show Expr.psub 0 _ _ = _
      simp only [Expr.psub, hw]
      rw [show Expr.val (cbV o.n o.i ys Nf) = (cbV o.n o.i ys Nf).1 from rfl, hc']
      simp [Val.shift_zero, Expr.val]
    rw [hsub]
    obtain ⟨β, hβ⟩ := hb δ hδ
    obtain ⟨b', hdef, hO⟩ := hside
    obtain ⟨β', hb'⟩ := hdef δ hδ
    have hP : ∀ ls' w σ', vC true T ls' δ w σ' → σ'.InStratum (Life.down β') :=
      fun ls' w σ' h => vC_outlivesLe hδ hb' hO true ls' w σ' h _ (Life.down_sqsubset β')
    exact withbor_spans_yields_cC hδ hbx hΔx hβ hT hB hP hNf hN S o hf ha hq hoB ys hys (hy δ)
      ℓ v' ls ρ hrest

/-- **Under the kernel's `[handle]`.** The body, at a row of the handler's operations followed by
`Σ′`, is handed to `handle_compatC` unchanged. -/
theorem handle_spans_yields {Δ : LifeCtx} {Γ Γ₁ Γr Γc : Ctx VTy} {S' : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {R : VTy} {ir ic : Nat}
    {x : LifeVar} {b : Lifetime.Life}
    (hb : Δ.Defines b) (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T)
    {Nf : Expr} (hNf : closedAt 1 Nf = true)
    (hN : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.comp (.ret (.box (.var x) B))))
    (o : OpSig) (hf : Row.find (Row.ofEff n E 0 ++ S') o.n o.i = some o) (ha : o.abort = false)
    (hq : o.q = .lin) (hoB : o.B = .unit)
    (ys : List Val) (hys : ∀ y ∈ ys, closedAt 0 y.1 = true)
    (hy : ∀ δ, ∀ y ∈ ys, ∀ ls, vC true o.A ls δ y PMap.empty)
    (hcb : closedAt 0 (cbV o.n o.i ys Nf).1 = true)
    (hsp : Ctx.SplitP Γ Γ₁ [⟨.ref T, true⟩]) (hsp₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S' (.tensor (.ref T) B) R))
    (hc : Ctx.SoloP Γc ic (clausesTy S' R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S', o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) :
    SemC Δ Γ (hndTerm n ir ic
      (.app (.app withbor (.var 0)) (.val (cbV o.n o.i ys Nf)))) (CTy.effOf S' R) :=
  handle_compatC hsp hsp₁ hr hc hn0 hnS hlen
    (withbor_spans_yields_sem hb hbx hΔx hT hB hside hNf hN _ o hf ha hq hoB ys hys hy hcb)

end GhostEnd
