import AsyncCap.Derives

/-!
# AsyncCap — `PinLaw`, the one asserted fact, and what is proved from it

`docs/async-capabilities.md` §4. A borrow held across a suspension is sound because the
suspension **ends** the lend and the resumption **re-lends** the place at a fresh lifetime
(GhostEnd's ghost end; Law 2 of `research/effects/src/synthesis.md` §10). Nothing in Core's
`wpG` changes: at the stop the lend is ended, so `↭` (`Core/EffDefs.lean:37`) and the frame
condition (`Core/EffDefs.lean:40`) hold as they do at a return.

What is not proved for every program is the borrower's half: that typed code, re-run at the
fresh lifetime, is again in the relation. `PinLaw` asserts it, **for typed programs only**:
every quantifier over code is a quantifier over `PDerives` derivations. No statement here is
pointwise over configurations; such statements were refuted by configurations no program
builds (`core_not_relend_kU`, `law2-typed-world`).

* `PinStop` (R1's content): every borrower typed in `PDerives` at a resuming row is re-lendable
  (`GhostEnd.Relend`) at the unwinding lend's table. It is GhostEnd's `RelendOfTyped`, at
  `opTableO` (affine stops may be cancelled), over `PDerives` (a borrower may hold relaxed lends
  of its own), with Law 2's added hypotheses (`∃ β, b.interp δ = some β`, `NoThunkT B`).
* `PinLoop` (R2's content): `lendLoopR`'s compatibility lemma, as a `Prop`.

**Proved from `PinStop`, no open step:** `lendR_compat`, the compatibility lemma of R1: the
lender side is GhostEnd's `withborR_compat` (6.65 at a resuming table, re-applied at each
resumption; the owner's finaliser at a cancel).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.AsyncCap
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (Relend opTableO opTableO_mono finPost withborR_compat ResumeAff finNil_tab
  relend_lam2)

/-- **PinStop.** Every borrower `M` typed in `PDerives` at a resuming row (`Row.ResumeO`), with the
view `m : Mut 'x T` alone in its context, is re-lendable at the unwinding lend of every place
`ℓ`: at each stop the lend is ended, and at each resumption the place is lent again at a fresh
lifetime below the bound, and `M`'s continuation is in the relation there. Cancelled at a stop,
its frames unwind and the owner is left for the lender's finaliser. -/
def PinStop : Prop :=
  ∀ (Δ : LifeCtx) (δ : LSub) (x : LifeVar) (b : Lifetime.Life) (T B : VTy) (S : Row)
    (M : Expr), Δ.Models δ → (∃ β, b.interp δ = some β) → Δ.find? x = none →
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    ¬ VFree x T → ¬ VFree x B → NoThunkT B → Row.ResumeO S x → closedAt 1 M = true →
    PDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B))) →
    ∀ (l : BoCa.Loc) (ls : List SRec),
      Relend (ℍ := ℍ) (opTableO (Row.tab S δ) l T δ) l T δ (finPost l T B δ) ls
        (substAll [Val.loc l] M) PMap.empty

/-- **R1's compatibility lemma, from `PinStop`.** The relaxed lend at `r : Ref T`, in the
kernel's relation at `F_Σ (Ref T ⊗ B)`. The proof is `GhostEnd.withborR_spans_yields_sem`'s
with the borrower's re-lendability taken from `PinStop` at its derivation, in place of the
straight-line borrower's `relendO_chain`. -/
theorem lendR_compat (H : PinStop (ℍ := ℍ)) {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life}
    {T B : VTy} {d M : Expr} {S : Row}
    (hb : Δ.Defines b) (hx : Δ.find? x = none) (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hT : ¬ VFree x T) (hB : ¬ VFree x B) (hBn : NoThunkT B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T)
    (hS : Row.ResumeO S x) (hM1 : closedAt 1 M = true) (hcb : closedAt 0 (lendCb M).1 = true)
    (hdc : closedAt 0 d = true) (hd : SemV (ℍ := ℍ) Δ [] d (.lolli (.ref T) .unit))
    (hM : PDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] M
      (.comp (CTy.effOf S (.box (.var x) B)))) :
    SemC (ℍ := ℍ) Δ [⟨.ref T, true⟩] (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
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
    have hsub : substAll (Val.loc ℓ :: γ')
        (.app (.app (.val (withborUV d)) (.var 0)) (.val (lendCb M)))
        = .app (.app (.val (withborUV d)) (.val (.loc ℓ))) (.val (lendCb M)) := by
      have hw : Expr.psub 0 (Val.loc ℓ :: γ') (withborUV d).1 = (withborUV d).1 :=
        psub_closedAt _ _ (withborUE_closed hdc) le_rfl
      have hc' : Expr.psub 0 (Val.loc ℓ :: γ') (lendCb M).1 = (lendCb M).1 :=
        psub_closedAt _ _ hcb le_rfl
      show Expr.psub 0 _ _ = _
      simp only [Expr.psub]
      rw [show Expr.val (withborUV d) = (withborUV d).1 from rfl, hw,
        show Expr.val (lendCb M) = (lendCb M).1 from rfl, hc']
      simp [Val.shift_zero, Expr.val]
    rw [hsub]
    obtain ⟨b', hdef, hO⟩ := hside
    obtain ⟨β', hb'⟩ := hdef δ hδ
    have hP : ∀ ls' w σ', vC true T ls' δ w σ' → σ'.InStratum (Life.down β') :=
      fun ls' w σ' h => vC_outlivesLe hδ hb' hO true ls' w σ' h _ (Life.down_sqsubset β')
    have hd' : ∀ ls', wpTS ls' d (fun ls'' => vP (.lolli (.ref T) .unit) ls'' δ) PMap.empty := by
      intro ls'
      have h := hd δ [] ls' PMap.empty hδ (gDenC_nil ls' δ)
      rwa [show substAll [] d = d from BoCa.Adequacy.psub_nil 0 d] at h
    have hRA : ResumeAff (Row.tab S δ) := by
      intro n i en hT'
      obtain ⟨o, hf, rfl⟩ := Row.tab_some hT'
      obtain ⟨ha, hq, -⟩ := hS o (Row.find_mem hf).1
      exact ⟨ha, hq⟩
    have hFin : ∀ o ∈ S, o.fin = .ret .unit := fun o ho => (hS o ho).2.2.1
    refine (cC_effOf S _ ls δ _ ρ).mpr ?_
    refine withborR_compat (Row.tab S δ) hRA (finNil_tab hFin δ) hdc hP hd' _ ℓ v' ls ?_ ρ hrest
    exact relend_lam2 (opTableO_mono _ _ _ _) hM1
      (H Δ δ x b T B S M hδ (hb δ hδ) hx hbx hΔx hT hB hBn hS hM1 hM ℓ ls)

/-- **PinLoop.** R2's compatibility lemma, as a `Prop`: the per-observation `imm` lend of
`r : Ref A` whose steps `N`, `K` and first state `s₀` are typed in `PDerives`, the state at a type
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
    PDerives (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] N
      (.comp (.ret (.sum B S))) →
    PDerives (Δ.extend x Δ.meetOfDom) [⟨.tensor (.imm (.var x) A) S, true⟩] K (.comp (.ret R)) →
    PDerives (Δ.extend x Δ.meetOfDom) [] s0 (.val S) →
    SemC (ℍ := ℍ) Δ [⟨.ref A, true⟩] (lendLoopApp A B R N K s0)
      (CTy.loop (.tensor (.ref A) B) (.tensor (.ref A) R))

/-- **PinLaw**: the one named assumption. Its fields are stated over `PDerives` derivations
only. -/
structure PinLaw : Prop where
  /-- R1: every typed borrower at a resuming row is re-lendable. -/
  stop : PinStop (ℍ := ℍ)
  /-- R2: the lend over a loop whose state holds the borrow is in the relation. -/
  loop : PinLoop (ℍ := ℍ)

end BoCa.Fig16.LogRel.Core.AsyncCap

end
