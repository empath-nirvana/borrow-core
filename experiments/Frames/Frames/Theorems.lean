import Frames.Accounting

/-!
# Frames — the target theorems

Four statements, each of them one induction over `FDerives` or a composition with Core's own
theorems:

1. **Elaboration** (`FDerives.elab`): every frame's elaborated term is a `CDerives` derivation at
   the frame type. One case per frame rule (`Elab.lean`); the dead-binder weakening it needs
   (`CDerives.shift_dead`) is Core's `CDerives.insert_dead`.
2. **Conservativity** (`frame_sound`, `frame_adequacy`, `core_conservative`): nothing of Core is
   changed, so `fundamentalC`, `adequacyC` and `adequacyD` cover every frame through its
   elaboration, and a Core computation embedded as a frame runs as it did.
3. **Accounting** (`accounting`): every exit of a well-typed frame hands back each of its slots,
   the same slot at the same position, exactly once; one induction over `FDerives`, one case
   lemma per rule (`Accounting.lean`) over the run lemmas of `Runs.lean`.
4. **Agreement with §19** (`frame_handled`, `frame_unwind_leakfree`): `raise` and abort leave a
   frame by §19's unwinding, through Core's own `[handle]` and `[then]`; the frame adds no rule
   for them.

Everything is proved. The statements are not vacuous (`not_returns_swap`: a Core term at the
frame type that swaps two slots satisfies the typing and fails the accounting).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload ubindE no_step_val)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### O1: the weakening the elaboration needs -/

/-- **O1.** A derivation stays one under a new dead binder at the front, its term shifted: Core's
`CDerives.insert_dead` at `Γa = []`, `Γd = [⟨T, false⟩]`. -/
theorem CDerives.shift_dead {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (T : VTy)
    (h : CDerives Δ Γ e j) : CDerives Δ (⟨T, false⟩ :: Γ) (e.shift 1 0) j :=
  Core.CDerives.insert_dead (Γd := [⟨T, false⟩]) (.cons .nil) h [] Γ rfl

/-! ### 1. Elaboration -/

/-- **Elaboration**: a frame is a `CDerives` derivation at its frame type. -/
theorem FDerives.elab {Δ : LifeCtx} {Γ : Ctx VTy} {Φ : List FBlock} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy}
    (h : FDerives Δ Γ Φ Ps e S E A) : CDerives Δ Γ e (.comp (frTy S Ps E A)) := by
  induction h with
  | core hS hP hN => exact elab_core hS hP hN
  | exit hk hV => exact elab_exit hk hV
  | bind hs hW hU hX _ _ ihM ihN => exact elab_bind hs hW hU hX ihM ihN
  | case hs hV _ _ ih₁ ih₂ => exact elab_case hs hV ih₁ ih₂
  | «catch» hs hW hU hX _ _ ihM ihH => exact elab_catch hs hW hU hX ihM ihH
  | under hS hQ _ ih => exact elab_under hS hQ ih
  | use src x hx hS hS' hP hsrc hsrcD hB hN => exact elab_use src x hx hS hS' hP hsrc hsrcD hB hN
  | lend src x hΔ hx hS hsrc hsrcD hΓx hfree hout _ ih =>
      exact elab_lend src x hΔ hx hS hsrc hsrcD hΓx hfree hout ih
  | new hs hA hV _ ih => exact elab_new hs hA hV ih
  | loopCount hs hs₁ hp hn hs0 _ ih => exact elab_loopCount hs hs₁ hp hn hs0 ih
  | loopIter hdiv hs hp hS₀ hs0 _ ih => exact elab_loopIter hdiv hs hp hS₀ hs0 ih
  | callBlock _ hb hj => exact elab_callBlock hb hj
  | sub hle _ ih => exact elab_sub hle ih

/-! ### 2. Conservativity -/

/-- **Frames are sound** at Core's own relation: `fundamentalC` at the elaboration. Nothing in
the relation, the model or `CDerives` is changed for frames. -/
theorem frame_sound {Δ : LifeCtx} {Γ : Ctx VTy} {Φ : List FBlock} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy}
    (h : FDerives Δ Γ Φ Ps e S E A) : SemC Δ Γ e (frTy S Ps E A) :=
  fundamentalC (FDerives.elab h)

/-- A closed frame over no slots, run on `()`. -/
def runFrameE (e : Expr) : Expr := .app (.val (.lam (.app (sh 1 e) (.var 0)))) (.val .unit)

/-- The run of a closed frame is a Core computation. -/
theorem runFrame_derives {Φ : List FBlock} {e : Expr} {A : VTy}
    (h : FDerives LifeCtx.empty [] Φ [] e [] [] A) :
    CDerives LifeCtx.empty [] (runFrameE e) (.comp (.ret (.tensor .unit (exitsTy A [])))) :=
  .bind (Γ₁ := []) (Γ₂ := []) .nil (.ret (.unitI .nil))
    (.app (Γ₁ := [⟨.unit, false⟩]) (Γ₂ := [⟨.unit, true⟩]) (.right .nil)
      (CDerives.shift_dead .unit (FDerives.elab h)) (.here .nil))

/-- **Adequacy for frames**, `adequacyD_obs` unchanged: every run of a closed frame program at a
persistent answer, from the empty memory, continues to a value at the empty memory. -/
theorem frame_adequacy {Φ : List FBlock} {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : FDerives LifeCtx.empty [] Φ [] e [] [] A)
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem (runFrameE e) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls, vP (.tensor .unit (exitsTy A [])) ls LSub.empty v PMap.empty := by
  have hp : (VTy.tensor .unit (exitsTy A [])).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, exitsTy, ExitRow.sumTy, Bool.true_and,
      Bool.and_true]
    exact hA
  exact EffPrograms.adequacyD_obs hp (runFrame_derives h) hs

/-- `core N` on `π`, after its β step: `N` under the frame `[then]` that answers `(π, inl x)`. -/
theorem coreE_beta (Ps : List VTy) (N : Expr) (π : Val) :
    (thenE (.pair (.var 1) (.inj₁ (.var 0))) (.app (dtorE (slotsTy Ps)) (.var 1)) (sh 1 N)).subst 0 π =
      ubindE (Val.pair (Val.lam (.pair (π.shift 1 0).1 (.inj₁ (.var 0))))
        (Val.lam (.app (dtorE (slotsTy Ps)) (π.shift 1 0).1))) N := by
  simp [thenE, ubindE, Expr.subst, subst_dtor, sh, subst_shift_expr, Val.pair, Val.lam, Expr.val]

/-- **A Core computation is a frame, and runs as it did.** On every run, `core N` on the slots
`π` reaches `(π, inl v)` exactly when `N` reaches `v`, at the same memory. -/
theorem core_conservative (Ps : List VTy) (N : Expr) (hN : closedAt 0 N = true) (π : Val)
    (μ μ' : Heap) (v : Val) :
    Steps μ N μ' (.val v) ↔
      Steps μ (.app (coreE Ps N) (.val π)) μ' (.val (Val.pair π (Val.inj₁ v))) := by
  set ND := Val.pair (Val.lam (.pair (π.shift 1 0).1 (.inj₁ (.var 0))))
    (Val.lam (.app (dtorE (slotsTy Ps)) (π.shift 1 0).1)) with hND
  have hβ : ∀ μ₀ μ₁ e₁, Step1 μ₀ (.app (coreE Ps N) (.val π)) μ₁ e₁ →
      μ₁ = μ₀ ∧ e₁ = ubindE ND N := by
    intro μ₀ μ₁ e₁ h
    obtain ⟨rfl, rfl⟩ := step1_beta_inv (b := thenE (.pair (.var 1) (.inj₁ (.var 0)))
      (.app (dtorE (slotsTy Ps)) (.var 1)) (sh 1 N)) (v := π) h
    exact ⟨rfl, coreE_beta Ps N π⟩
  have hret : (Expr.pair (π.shift 1 0).1 (.inj₁ (.var 0))).subst 0 v = .val (Val.pair π (Val.inj₁ v)) := by
    simp [Expr.subst, Val.pair, Val.inj₁, Expr.val]
  constructor
  · intro hs
    refine .more (Step1.head (Head.beta μ _ π)) ?_
    rw [coreE_beta]
    refine Steps.trans (Steps.plug (app2K .ubind ND) hs) ?_
    refine .more (Step1.head (Head.uthen μ' _ _ v)) ?_
    refine .more (Step1.head (Head.beta μ' _ v)) ?_
    rw [hret]
    exact .refl _ _
  · intro hs
    have hs' := steps_peel hs (by simp [coreE]) (fun μ₁ e₁ h => hβ μ μ₁ e₁ h)
    rcases steps_plug_split (app2K .ubind ND) hs' with ⟨e', he, -⟩ | ⟨μ₁, t₁, h₁, hirr₁, h₂⟩
    · exact absurd (isVal_eq he) (app2_not_isVal .ubind _ e')
    · by_cases hv : IsVal t₁
      · -- `N` reached a value: `[then]` and β, at the same memory
        have h₃ := steps_peel (m := μ₁)
          (e' := .app (.val (Val.lam (.pair (π.shift 1 0).1 (.inj₁ (.var 0))))) (.val ⟨t₁, hv⟩)) h₂
          (app2_not_isVal .ubind _ _) (fun μ₂ e₂ h => by
          rcases step1_app2 (p := .ubind) (x := ND) trivial h with ⟨e', -, he'⟩ | hh
          · exact absurd he' (no_step_val (w := ⟨t₁, hv⟩))
          · rcases head_ubind_inv hh with ⟨v', hv', rfl, rfl⟩ | ⟨hnv, -⟩
            · simp only [Kont.plug] at hv'
              subst hv'
              exact ⟨rfl, rfl⟩
            · exact absurd hv hnv)
        have h₄ := steps_peel h₃ (by simp) (fun μ₂ e₂ h => step1_beta_inv (v := ⟨t₁, hv⟩) h)
        have hret' : (Expr.pair (π.shift 1 0).1 (.inj₁ (.var 0))).subst 0 ⟨t₁, hv⟩ =
            .val (Val.pair π (Val.inj₁ ⟨t₁, hv⟩)) := by
          simp [Expr.subst, Val.pair, Val.inj₁, Expr.val]
        rw [hret'] at h₄
        obtain ⟨rfl, hw⟩ := steps_from_val h₄
        obtain ⟨-, hw⟩ := pairV_inj hw
        have : (⟨t₁, hv⟩ : Val) = v := by
          have := congrArg Subtype.val hw
          simp [Val.inj₁] at this
          exact Subtype.ext this.symm
        rw [← this]
        exact h₁
      · -- `N` unwound: the finaliser runs and no value is reached
        exfalso
        rcases steps_cases h₂ with ⟨-, h⟩ | ⟨μ₂, e₂, h₃, t₃⟩
        · exact app2_not_isVal .ubind ND t₁ (isVal_eq (w := Val.pair π (Val.inj₁ v)) h)
        · rcases head_ubind_inv (step1_appR_irred hv hirr₁ h₃) with ⟨w, rfl, -, -⟩ | ⟨-, hu⟩
          · exact hv w.2
          · rcases hu with ⟨p, rfl⟩ | ⟨s, rfl⟩
            · exact (retsG_unfold (retsG_seq (Q := fun _ => False) (G := fun _ => False)
                (retsG_raise p))).1 _ _ _ t₃
            · exact (retsG_unfold (retsG_cfin (Q := fun _ => False) (G := fun _ => False) s _)).1 _ _ _ t₃

/-- **No Core rule is touched**: the frame judgment's `core` rule takes every `CDerives`
computation, so a program that uses no frame is its own `CDerives` derivation, and every Core
theorem holds of it unchanged (the library is not edited; `make gate`'s kernel counts and goldens
check that). Stated as the embedding at a frame over no slots and no exits. -/
theorem core_embeds {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {S : Row} {A : VTy} (Φ : List FBlock)
    (hS : FRow S) (hN : CDerives Δ Γ N (.comp (CTy.effOf S A))) :
    FDerives Δ Γ Φ [] (coreE [] N) S [] A :=
  .core hS (fun _ h => absurd h List.not_mem_nil) hN

/-! ### 3. Accounting -/

/-- **Accounting**: every exit of a well-typed frame returns each of its slots exactly once, the
same slot at the same position. ONE induction over `FDerives`; each case uses only its premises'
induction hypotheses. A rule added to `FDerives` fails this proof until its case is written.

Each case is one lemma of `Accounting.lean`, which names its own rule, the run lemmas of
`Runs.lean` and the hypothesis of each premise; none mentions another frame rule. -/
theorem accounting {Δ : LifeCtx} {Γ : Ctx VTy} {Φ : List FBlock} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy} (hΦ : ∀ b ∈ Φ, b.Returns)
    (h : FDerives Δ Γ Φ Ps e S E A) : ∀ γ : List Val, Returns (substAll γ e) := by
  induction h with
  | core => exact acc_core _ _
  | exit => exact acc_exit _ _
  | bind _ _ _ _ _ _ ihM ihN => exact acc_bind (ihM hΦ) (ihN hΦ)
  | case _ _ _ _ ih₁ ih₂ => exact acc_case (ih₁ hΦ) (ih₂ hΦ)
  | «catch» _ _ _ _ _ _ ihM ihH => exact acc_catch (ihM hΦ) (ihH hΦ)
  | under _ _ _ ih => exact acc_under (ih hΦ)
  | use src => exact acc_use src _ _
  | lend src _ _ _ _ _ _ _ _ _ _ ih => exact acc_lend src (ih hΦ)
  | new _ _ _ _ ih => exact acc_new _ _ (ih hΦ)
  | loopCount _ _ _ _ _ _ ih => exact acc_loopCount (ih hΦ)
  | loopIter _ _ _ _ _ _ ih => exact acc_loopIter _ (ih hΦ)
  | callBlock hk hb _ => exact acc_callBlock hb (hΦ _ (List.mem_of_getElem? hk))
  | sub _ _ ih => exact acc_sub (ih hΦ)

/-- Blocks built from frames return their slots: a block of the program typed by `FDerives`
satisfies the hypothesis `accounting` asks of `Φ`. -/
theorem block_returns {Δ : LifeCtx} {Φ : List FBlock} {B : VTy} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy} (hΦ : ∀ b ∈ Φ, b.Returns)
    (h : FDerives Δ [⟨B, true⟩] Φ Ps e S E A) :
    FBlock.Returns ⟨Val.lam e, B, S, Ps, E, A⟩ := by
  -- β at the argument `a`, then `accounting` at `γ = [a]` (`substAll [a] e = e[a/0]`).
  intro a π
  apply rets_of_retsG
  refine retsG_beta (K := .appL .hole π) ?_
  have hacc := accounting hΦ h [a] π
  rw [substAll_cons_psub, Adequacy.psub_nil] at hacc
  exact retsG_of_rets hacc

/-! ### 4. Agreement with §19: raise and abort -/

/-- **A frame is handled by Core's own `[handle]`.** A frame at a row with the operations of
`n`, run on no slots, under a handler of `n`: the handled computation is a `CDerives` derivation
by `effHandleV`, so raise and abort out of a frame are §19's `[unwind]`/`[finalise]`, with no
frame rule for them. -/
theorem frame_handled {Φ : List FBlock} {e H : Expr} {S : Row} {Eff : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} (h : FDerives LifeCtx.empty [] Φ [] e (Row.ofEff n Eff 0 ++ S) [] A)
    (hH : H.ValFormIn [])
    (hc : CDerives LifeCtx.empty [] H
      (.val (.tensor (retTy S (.tensor .unit (exitsTy A [])) R) (clausesTy S R Eff finsNil))))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : Eff.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n Eff 0 ++ S) = false) :
    CDerives LifeCtx.empty [] (hndExpr n (Eff.map Prod.fst) H (runFrameE e))
      (.comp (CTy.effOf S R)) := by
  -- `effHandleV` at the split `[] = [], []`, with the handled computation `runFrameE e`: the
  -- `[let]` of `()` at the handled row (`effLet`, nothing in its context) over `app` of the
  -- elaboration under O1.
  refine .effHandleV (fs := finsNil) .nil .nil hH hc hn0 hnS hlen hdv ?_
  exact .effLet (Γ₁ := []) (Γ₂ := []) .nil (fun _ _ h => absurd h List.not_mem_nil)
    (fun _ _ h => absurd h List.not_mem_nil) (.effSub (RowLe.nil _) (.ret (.unitI .nil)))
    (.app (Γ₁ := [⟨.unit, false⟩]) (Γ₂ := [⟨.unit, true⟩]) (.right .nil)
      (CDerives.shift_dead .unit (FDerives.elab h)) (.here .nil))

/-- **Leak freedom across a raise.** Every run of a closed, handled frame program at a persistent
answer, from the empty memory, continues to a value at the empty memory, whether or not the frame
raised: every slot the frame owned was finalised, once, by §19's unwinding (the holders'
`[then]` finalisers and the unwinding borrow constants). `adequacyD_obs` unchanged. -/
theorem frame_unwind_leakfree {Φ : List FBlock} {e H : Expr} {Eff : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} (hR : R.Persistent) (h : FDerives LifeCtx.empty [] Φ [] e (Row.ofEff n Eff 0) [] A)
    (hH : H.ValFormIn [])
    (hc : CDerives LifeCtx.empty [] H
      (.val (.tensor (retTy [] (.tensor .unit (exitsTy A [])) R) (clausesTy [] R Eff finsNil))))
    (hn0 : n ≠ 0) (hlen : Eff.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n Eff 0 ++ []) = false)
    {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (hndExpr n (Eff.map Prod.fst) H (runFrameE e)) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧ ∃ ls, vP R ls LSub.empty v PMap.empty := by
  have h' : FDerives LifeCtx.empty [] Φ [] e (Row.ofEff n Eff 0 ++ []) [] A := by
    simpa using h
  exact EffPrograms.adequacyD_obs hR
    (frame_handled h' hH hc hn0 (fun _ h => absurd h List.not_mem_nil) hlen hdv) hs

end BoCa.Fig16.LogRel.Core.Frames

end
