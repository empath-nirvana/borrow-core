import SuspSpike.Handler

/-!
# SuspSpike — the lend at a class-1 row: `withbor` of an owned cell

`withborC`: `withbor ℓ f`, the kernel's term (`[TR]` 6.173's constant), whose callback runs at a
class-1 table, is in `ewpTS` at the graded table with answer `𝒱⟦Ref T ⊗ B⟧`, from
`ℓ ↦ v ⋆ 𝒱⟦T⟧(v)`. The callback is any computation in the graded relation at every lend
(`fresh`), as `withbor2_compatX` reads Core's callback; in particular any callback in Core's own
relation at the row (`withborC_core`, by `ewp_grade`). No property of the callback's code is read:
the borrower side is Core's relation, unchanged.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- What the borrower hands back: the owner, and the answer at `B`. -/
def finPost (l : BoCa.Loc) (T B : VTy) (δ : LSub) (ls : List SRec) (r : Val) : WProp :=
  owner l T δ ls ⋆ vC true B ls δ r

/-- `withbor ℓ` after its first β-step. -/
def withborAt (l : BoCa.Loc) : Val :=
  Val.lam (.pair (.val (.loc l)) (.app (.app BoCa.v0 unit') (.val (.loc l))))

theorem withbor_step₁ (l : BoCa.Loc) (f : Val) (μ : Heap) :
    Step1N μ (.app (.app withbor (.val (.loc l))) (.val f)) μ
      (.app (.val (withborAt l)) (.val f)) := by
  have hβ₁ : Expr.subst 0 (Val.loc l)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (withborAt l) := by
    simp [withborAt, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit']
  have h1 := (Step1N.head (ℍ := ℍ) (Head.beta μ (.lam (.pair BoCa.v1
    (.app (.app BoCa.v0 unit') BoCa.v1))) (Val.loc l)) rfl).plug (Kont.appL .hole f)
  simp only [Kont.plug] at h1
  rw [show Expr.subst 0 (Val.loc l) (Expr.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1)))
    = Expr.val (withborAt l) from hβ₁] at h1
  exact h1

theorem withbor_step₂ (l : BoCa.Loc) (f : Val) (μ : Heap) :
    Step1N μ (.app (.val (withborAt l)) (.val f)) μ
      (.pair (.val (.loc l)) (.app (.app (.val f) (.val .unit)) (.val (.loc l)))) := by
  have hβ₂ : Expr.subst 0 f
        (Expr.pair (.val (.loc l)) (.app (.app BoCa.v0 unit') (.val (.loc l))))
      = Expr.pair (.val (.loc l)) (.app (.app (.val f) (.val .unit)) (.val (.loc l))) := by
    simp [Expr.subst, BoCa.v0, unit']
  have h2 := Step1N.head (ℍ := ℍ) (Head.beta μ (.pair (.val (.loc l))
    (.app (.app BoCa.v0 unit') (.val (.loc l)))) f) rfl
  rw [hβ₂] at h2
  exact h2

/-- The callback applied to its lend: `f () ℓ`. -/
def cbApp (f : Val) (l : BoCa.Loc) : Expr := .app (.app (.val f) (.val .unit)) (.val (.loc l))

/-- **The lend at a class-1 row.** `withbor ℓ f`, its callback in the graded relation at every
lend, answers `𝒱⟦Ref T ⊗ B⟧` at the graded table. The lend spans every call-like stop of the
callback (`frameC`); the pair frame `(ℓ, [·])` is carried through them (`ewp_frame_call`). -/
theorem withborC {T : OpTab} {C : Grade} (hC : CallRow T C) (hArg : ∀ α, ArgIn α T)
    {l : BoCa.Loc} {T₁ T₂ : VTy} {δ : LSub} {β : Life}
    (hP : ∀ ls w σ, vC true T₁ ls δ w σ → σ.InStratum β) (f : Val) (ls : List SRec) (v : Val) :
    Entails
      (ptoOwn l v ⋆ vC true T₁ ls δ v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true T₁ ls₀ δ) ─⋆
          ewpTS ls (cbApp f l) (opTableC T C) (postA l T₁ δ α (finPost l T₁ T₂ δ))))
      (ewpTS ls (.app (.app withbor (.val (.loc l))) (.val f)) (opTableC T C)
        (fun ls r => vC true (.tensor (.ref T₁) T₂) ls δ r)) := by
  intro ρ hρ
  have hM := opTableC_mono T C
  have hcb := frameC hC hArg l T₁ δ β hP v (cbApp f l) ls (finPost l T₁ T₂ δ) ρ hρ
  have hpair := ewp_frame_call hC (OpTab.Le.refl T) (fun n i en h => (hC.1 n i en h).1)
    (.pairR (Val.loc l) .hole) (fun _ => rfl) (fun _ => emp) (fun _ _ _ _ h => h)
    (finPost l T₁ T₂ δ) (fun ls r => vC true (.tensor (.ref T₁) T₂) ls δ r) ?_ hcb
    (ρ₂ := PMap.empty) ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
  · exact ewp_step hM (withbor_step₁ l _) ls _ ρ (ewp_step hM (withbor_step₂ l _) ls _ ρ hpair)
  · rintro ls' r σ ⟨σ₁, σ₂, hc, ⟨so, sb, hcs, ⟨w, ρl, ρP, hcl, hl, hw⟩, hBr⟩, hσ₂, -⟩
    subst hσ₂
    obtain rfl : σ = σ₁ := ResU.CompS.functional hc (ResU.comp_empty_right σ₁)
    show ewpTS ls' (.val (Val.pair (Val.loc l) r)) _ _ σ
    exact ewp_val hM ⟨Val.loc l, r, pure_sep_mk rfl
      ⟨so, sb, hcs, ⟨l, w, pure_sep_mk rfl ⟨ρl, ρP, hcl, hl, hw⟩⟩, hBr⟩⟩

/-- **The lend at a class-1 row, from Core's relation.** A callback in Core's relation at the row
(`opTable T`, every lend) is in the graded one (`ewp_grade`), so `withborC` applies to it. This is
the case of a callback Core types at a resuming row: the borrower side needs nothing beyond
`fundamentalC`. -/
theorem withborC_core {T : OpTab} {C : Grade} (hC : CallRow T C) (hArg : ∀ α, ArgIn α T)
    {l : BoCa.Loc} {T₁ T₂ : VTy} {δ : LSub} {β : Life}
    (hP : ∀ ls w σ, vC true T₁ ls δ w σ → σ.InStratum β) (f : Val) (ls : List SRec) (v : Val) :
    Entails
      (ptoOwn l v ⋆ vC true T₁ ls δ v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true T₁ ls₀ δ) ─⋆
          ewpTS ls (cbApp f l) (opTable T) (postA l T₁ δ α (finPost l T₁ T₂ δ))))
      (ewpTS ls (.app (.app withbor (.val (.loc l))) (.val f)) (opTableC T C)
        (fun ls r => vC true (.tensor (.ref T₁) T₂) ls δ r)) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, h₁, ρ₃, ρ₄, hc', h₃, ⟨γ, hγ⟩⟩
  refine withborC hC hArg hP f ls v ρ ⟨ρ₁, ρ₂, hc, h₁, ρ₃, ρ₄, hc', h₃, γ, fun α hα => ?_⟩
  obtain ⟨hw, hout⟩ := hγ α hα
  exact ⟨fun ρm σ hm hcm => ewp_grade T C (hw ρm σ hm hcm), hout⟩

end SuspSpike

end
