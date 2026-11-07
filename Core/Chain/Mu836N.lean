import Core.Chain.Rules834N
import Core.Chain.ImmLend833N
import Core.Chain.Fuel835N
import Core.FoldReuse

/-!
# The `μ` rows at `SemJN₀`  `[spec §6]`

`docs/new-core/scope-831-interface.md` §13. `vN₀` reads `μX. A` at Core's least fixed point
(`vNE₀`'s `μ` clause), the candidate joint over the mode, the world and the index; unfolding costs
no step, as in Core, where the machine has no `roll`/`unroll` step.

* `roll_compatN₀`, `unroll_compatN₀`: Core's `roll_compatX`, `unroll_compatX`, with `vN_roll₀` and
  `vN_unfold₀` under `erwp_mono`.
* `foldOwn_compatN₀`, `foldReuse_compatN₀`: Core's `foldOwn_compatX`, `foldReuse_compatX`.

`foldOwnG` is `Core/Chain/FoldG836N.lean`, `foldImm` `Core/Chain/FoldImm836N.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-! ### `foldOwn` (Core's `Core/FoldOwn.lean`)

The term is Core's (`foldOwnV`, `travO`, `selfO`, `hO`) and so are its reductions; each pure step is
`erwp_det` at the same index, a `free` costs one (`erwp_free`). The induction is Core's: on a
bound of the owned resource's size (`dsize`), then on the size of the value. The run is at one
world and one view; the algebra is read at that world (`vN_extR₀` at its empty resource), at
every index below the fold's. -/

section FoldOwn

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- `travO G h w` steps to its body (Core's `travO_app`). -/
theorem travO_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (G : FShape) (h w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (((tO G).subst 1 (h.shift 1 0)).subst 0 w) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (travO G)) (.val h)) (.val w)) ρ := by
  rw [travO_eq]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ h) rfl (.appL .hole w)) ?_
  exact erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) hw

/-- `h w` for `h = λw. self g w` reaches `travO T h w to r. g r` (Core's `hO_app`). -/
theorem hO_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (F : FShape) (g w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      ((Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
        (.app (.app (.val (travO F)) (.val (hO F g))) (.val w))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val (hO F g)) (.val w)) ρ := by
  have hT := opTableN_down OpTabN.empty_down
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfO F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfO F)) (.val g)) (.val w) := by
    simp [closed_subst (selfO_closed F), subst_shift_succ]
  rw [e₁]
  refine erwp_pureSteps hΦ hT hQ (selfV_steps_in (fBO_closed F) (.appL .hole w) g) ?_
  rw [fixV_eq (fBO_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ g) rfl (.appL .hole w)) ?_
  rw [fBO_subst F (selfO_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [fBO_body F (selfO_closed F)]
  exact hw

end FoldOwn

/-! ### `foldReuse` (Core's `Core/FoldReuse.lean`)

`foldOwn`'s port with the `Ref X` clause replaced: the cell is emptied by `swap w ()` (`erwp_swapN`,
Core's `wpTS_swap`: a load and a store, one step each), and the emptied cell goes to the algebra
beside the recursive result. -/

section FoldReuse

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- **`swap ℓ v`** at `ℓ ↦ w` returns `(ℓ, w)` with `ℓ ↦ v` (Core's `wpTS_swap`): the load and the
store cost one step each. -/
theorem erwp_swapN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (ℓ : Loc) (w v : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : (sep (ptoOwn ℓ w) (wand (ptoOwn ℓ v) (Q (n - 1 - 1) ls (.pair (.loc ℓ) w)))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.app swap (.val (.loc ℓ))) (.val v)) ρ := by
  obtain ⟨ρo, ρR, hc, rfl, hR⟩ := h
  have hT := opTableN_down OpTabN.empty_down
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (elet (.app load' BoCa.v1)
          (.seq (.app (.app store' BoCa.v2) BoCa.v1) (.pair BoCa.v2 BoCa.v0)))))
      = Expr.val (Val.lam (elet (eLoad ℓ)
          (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                (.pair (.val (.loc ℓ)) BoCa.v0)))) := by
    simp [elet, eLoad, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, BoCa.v2, load', store']
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc ℓ)) rfl (.appL .hole v)) ?_
  rw [hβ₁]
  simp only [Kont.plug]
  have hβ₂ : Expr.subst 0 v
        (elet (eLoad ℓ) (.seq (.app (.app store' (.val (.loc ℓ))) BoCa.v1)
                              (.pair (.val (.loc ℓ)) BoCa.v0)))
      = elet (eLoad ℓ) (.seq (eStore ℓ (v.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0)) := by
    simp [elet, eLoad, eStore, Expr.subst, BoCa.v0, BoCa.v1, store']
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  rw [hβ₂]
  refine erwp_bindR hΦ (opTableN_local _) (.appR (.val (.lam _)) .hole) ?_
  refine rwp_load ls ℓ w _ ⟨_, ρR, hc, rfl, fun c₁ p₁ hc₁ hp₁ => ?_⟩
  obtain rfl := hc₁
  simp only [Kont.plug]
  have hβ₃ : Expr.subst 0 w
        (Expr.seq (eStore ℓ (v.shift 1 0)) (.pair (.val (.loc ℓ)) BoCa.v0))
      = Expr.seq (eStore ℓ v) (.pair (.val (.loc ℓ)) (.val w)) := by
    simp [eStore, Expr.subst, BoCa.v0,
      Expr.subst_shift 0 0 0 w v.val (Nat.le_refl 0) (Nat.le_refl 0), Expr.shift_zero]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [hβ₃, show eStore ℓ v = .app (.val (Val.storeV (Val.loc ℓ))) (.val v) from rfl]
  refine erwp_bindR hΦ (opTableN_local _) (.seq .hole (.pair (.val (.loc ℓ)) (.val w))) ?_
  refine rwp_store ls ℓ w v _ ⟨_, ρR, ResU.CompS.comm hp₁, rfl, fun c₃ p₃ hc₃ hp₃ => ?_⟩
  simp only [Kont.plug]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  exact erwp_val (v := Val.pair (.loc ℓ) w) (hR c₃ p₃ hc₃ hp₃)

theorem travR_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (G : FShape) (h w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (((tR G).subst 1 (h.shift 1 0)).subst 0 w) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      (.app (.app (.val (travR G)) (.val h)) (.val w)) ρ := by
  rw [travR_eq]
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ h) rfl (.appL .hole w)) ?_
  exact erwp_det hΦ (opTableN_down OpTabN.empty_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) hw

theorem hR_appN {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} (hQ : Q.Down) (F : FShape) (g w : Val)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (hw : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls
      ((Kont.appR (.val (.lam (.app (.val (g.shift 1 0)) (.var 0)))) .hole).plug
        (.app (.app (.val (travR F)) (.val (hR F g))) (.val w))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app (.val (hR F g)) (.val w)) ρ := by
  have hT := opTableN_down OpTabN.empty_down
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e₁ : Expr.subst 0 w (.app (.app (.val (selfR F)) (.val (g.shift 1 0))) (.var 0))
      = .app (.app (.val (selfR F)) (.val g)) (.val w) := by
    simp [closed_subst (selfR_closed F), subst_shift_succ]
  rw [e₁]
  refine erwp_pureSteps hΦ hT hQ (selfV_steps_in (fBR_closed F) (.appL .hole w) g) ?_
  rw [fixV_eq (fBR_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ g) rfl (.appL .hole w)) ?_
  rw [fBR_subst F (selfR_closed F)]
  refine erwp_det hΦ hT hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [fBR_body F (selfR_closed F)]
  exact hw

end FoldReuse

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
