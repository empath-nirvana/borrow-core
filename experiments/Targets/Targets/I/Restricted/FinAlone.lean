import Targets.I.Restricted.Core
import Targets.I.Routes
import Targets.B.BoLo
import Targets.B.Adequacy
import Targets.Instance.Restricted.NoInterception

/-!
# The interaction — a fired finaliser runs alone: what B gives, and what typing must

`FinAloneAt FR J` (`Targets/Base/CoreCancel.lean`) is what `FinaliserOrder` reads: in a
platform-free run of a typed closed program, a fired finaliser's run alone ends at a value or at an
uncaught raise of a name in `FR`, the names a finaliser may raise (decision D3: today's kernel's
endings are raises of nonzero names, option A's are none).  It has two halves.

* **Stuck redexes: B gives them.**  A program in Core's relation never gets stuck, under the
  platform with no operation (`platOK_of_ewp`, B2's runs).  A finaliser's run alone is the whole
  run's, inside `K₀[□; raise p]` or `K₀[cfin s □]`.  A term that is no value, takes no step, and
  leaves no operation uncaught, takes no step in such a context either (`no_step_plug`).  So a
  finaliser whose run alone stopped at such a term would leave the whole run stuck.
* **Operations: typing must give them.**  `FinRowsAt FR J`: an operation the finaliser's run alone
  leaves uncaught is a raise of a name in `FR`, neither a resuming operation nor a cancel.  This is
  the finaliser's row read at run time.  No route proves it (TIER1-PLAN §4).

`finAloneAt_of_finRows`: FL at Core's world and `FinRowsAt FR` give `FinAloneAt FR`, at every `FR`;
at today's unr-free kernel FL holds (`fl_core_tier1NU`), so `FinaliserOrder tier1NU` follows from
`FinRowsAt (· ≠ 0) tier1NU` alone (`finaliserOrder_tier1NU_of_finRows`), and from option A's
`FinRowsAt (fun _ => False) tier1NU` (`finaliserOrder_tier1NU_of_finRowsA`).

**Route 8.2's statement** (`RowRoute`): a typing of configurations at rows, through the heap, that
types the configurations a typed program reaches, types a fired finaliser at a row of abortive
operations with nonzero names, is preserved by steps, and at such a row leaves no resuming
operation and no cancel uncaught.  Its obligations give `FinRowsAt` (`finRowsAt_of_route`).  They
are not circular only when `Typed` is a syntactic judgement, whose `step` is subject reduction and
whose `stop` is canonical forms; no such judgement is built (TIER1-PLAN §4 records the review).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal)
open BoCa.Lifetime (LSub LifeCtx)

/-! ### A stuck term is stuck in a context -/

/-- The context is the hole. -/
def _root_.BoCa.BoLo.Kont.IsHole : Kont → Bool
  | .hole => true
  | _ => false

/-- The innermost frame of a context is `□ v`. -/
def _root_.BoCa.BoLo.Kont.EndsAppL : Kont → Bool
  | .hole => false
  | .appL K _ => K.IsHole || K.EndsAppL
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appR _ K | .seq K _ | .inj₁ K
  | .inj₂ K => K.EndsAppL

theorem endsAppL_appL (w : Val) : ∀ K : Kont, (K.comp (.appL .hole w)).EndsAppL = true
  | .hole => rfl
  | .appL K v => by simp [Kont.comp, Kont.EndsAppL, endsAppL_appL w K]
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appR _ K | .seq K _ | .inj₁ K
  | .inj₂ K => by simp [Kont.comp, Kont.EndsAppL, endsAppL_appL w K]

theorem isHole_comp {F : Kont} (hF : F.IsHole = false) : ∀ K : Kont, (K.comp F).IsHole = false
  | .hole => by simpa [Kont.comp] using hF
  | .appL _ _ | .pairL _ _ | .pairR _ _ | .letpair _ _ | .case _ _ _ | .appR _ _ | .seq _ _
  | .inj₁ _ | .inj₂ _ => rfl

theorem endsAppL_comp_of {F : Kont} (hF : F.IsHole = false) (hF' : F.EndsAppL = false) :
    ∀ K : Kont, (K.comp F).EndsAppL = false
  | .hole => by simpa [Kont.comp] using hF'
  | .appL K v => by simp [Kont.comp, Kont.EndsAppL, isHole_comp hF K, endsAppL_comp_of hF hF' K]
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appR _ K | .seq K _ | .inj₁ K
  | .inj₂ K => by simp [Kont.comp, Kont.EndsAppL, endsAppL_comp_of hF hF' K]

/-- A context whose innermost frame is not `□ v` is no context of the form `K₁[□ v]`. -/
theorem ne_comp_appL {K : Kont} (hK : K.EndsAppL = false) (K₁ : Kont) (w : Val) :
    K ≠ K₁.comp (.appL .hole w) := by
  rintro rfl
  rw [endsAppL_appL w K₁] at hK
  cases hK

/-- **A stuck term is stuck in a context**: a term that is no value, takes no step, and leaves no
operation uncaught, takes no step under `K`, provided it is no inert application or `K`'s innermost
frame is not `□ v`.  Each catcher frame's step needs a value or an operation its inner context
leaves uncaught at its hole (`head_plug`). -/
theorem no_step_plug {μ : Heap} {t : Expr} (hirr : ∀ μ' t', ¬ Step1 (ℍ := ℍ) μ t μ' t')
    (hnv : ¬ IsVal t)
    (hop : ∀ (K' : Kont) (r : Bool) (m j : UInt32) (w : Val),
      t = K'.plug (opE r (opPayload m j w)) → ¬ OpFree r m K')
    (K : Kont)
    (hin : (∀ (p : Prim) (H : Val), p.Inert → t ≠ .app (.val (.prim p)) (.val H)) ∨
      K.EndsAppL = false)
    {μ' : Heap} {E : Expr} : ¬ Step1 (ℍ := ℍ) μ (K.plug t) μ' E := by
  -- an operation at the hole of a catcher's inner context, left uncaught there, is not `t`'s
  have key : ∀ (K₃ K₄ : Kont) (r : Bool) (m j : UInt32) (w : Val),
      K₃.plug t = K₄.plug (opE r (opPayload m j w)) → OpFree r m K₄ → False := by
    intro K₃ K₄ r m j w h hfree
    rcases plug_cmp K₃ K₄ hnv (opE_not_isVal r _) h with ⟨K₅, h₅, h₆⟩ | ⟨K₅, h₅, h₆⟩
    · exact hop K₅ r m j w h₅ (opFree_right (h₆ ▸ hfree))
    · by_cases h5 : K₅ = .hole
      · subst h5
        refine hop .hole r m j w (by simpa [Kont.plug] using h₅.symm) ?_
        cases r <;> simp [OpFree, Kont.HasHnd, Kont.Catches]
      · exact hnv (isVal_of_plug_opE h₅.symm h5)
  have keyV : ∀ (K₃ : Kont) (w : Val), K₃.plug t = w.1 → False :=
    fun K₃ w h => hnv (K₃.isVal_of_plug (h ▸ w.2))
  rintro ⟨K', a, a', hE, rfl, hh⟩
  rcases plug_cmp K K' hnv hh.not_isVal hE with ⟨K'', h₁, -⟩ | ⟨K'', h₁, h₂⟩
  · exact hirr _ _ ⟨K'', a, a', h₁, rfl, hh⟩
  by_cases h0 : K'' = .hole
  · subst h0
    exact hirr _ _ ⟨.hole, a, a', by simpa [Kont.plug] using h₁.symm, rfl, hh⟩
  rcases head_plug hh K'' hnv h₁ h0 with ⟨n, qs, hr, hs, K₃, rfl⟩ | ⟨N, D, K₃, rfl⟩ | ⟨K₃, rfl⟩ |
      ⟨w, H, p, hp, rfl, rfl⟩ | ⟨err, K₃, rfl⟩
  · -- a handler frame: `[ret]`, `[op]`, `[unwind]`
    generalize hX : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal n qs hr hs))) K₃).plug t = X
      at h₁
    subst h₁
    cases hh with
    | hret n' qs' hr' hs' w =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hX
        exact keyV K₃ w hX.2
    | hop n' i qs' hr' hs' c v K₄ _ hK₄ =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ false n' i v (by simpa [opE] using hX.2) (by simpa [OpFree] using hK₄)
    | hunwind n' i qs' hr' hs' c v K₄ _ hK₄ =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ true n' i v (by simpa [opE] using hX.2) (by simpa [OpFree] using hK₄)
    | _ => simp [Kont.plug, ubindE, ccatchE, cfinE] at hX
  · -- a finaliser frame: `[then]`, `[finalise]`, `[finalise-cancel]`
    generalize hX : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) K₃).plug t = X
      at h₁
    subst h₁
    cases hh with
    | uthen N' D' w =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
        exact keyV K₃ w hX.2
    | ufin N' D' n' i v K₄ _ hK₄ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ true n' i v (by simpa [opE] using hX.2) (by simpa [OpFree] using hK₄)
    | ufinC N' D' err K₄ hK₄ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ true 0 0 _ hX.2 (by simpa [OpFree] using hK₄)
    | _ => simp [Kont.plug, hndE, ccatchE, cfinE] at hX
  · -- `ccatch`: `[cancel]`, `[cancel-raise]`
    generalize hX : (Kont.appR (.val (.prim .ccatch)) K₃).plug t = X at h₁
    subst h₁
    cases hh with
    | cancel K₄ hK₄ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ true 0 0 _ hX.2 (by simpa [OpFree] using hK₄)
    | creraise E' K₄ hK₄ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ true 0 0 _ hX.2 (by simpa [OpFree] using hK₄)
    | _ => simp [Kont.plug, hndE, ubindE, cfinE] at hX
  · -- an inert application under `□ v`
    rcases hin with hin | hin
    · exact hin p H hp rfl
    · exact ne_comp_appL hin K' w h₂
  · -- a cancel-mode finaliser frame: `[cfin-ret]`, `[cfin-raise]`, `[cfin-cancel]`
    generalize hX : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) K₃).plug t = X
      at h₁
    subst h₁
    cases hh with
    | cfret err' w =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
        exact keyV K₃ w hX.2
    | cferr err' m j w K₄ _ hK₄ =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ true m j w (by simpa [opE] using hX.2) (by simpa [OpFree] using hK₄)
    | cfcancel err' err'' K₄ hK₄ =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
        exact key K₃ K₄ true 0 0 _ hX.2 (by simpa [OpFree] using hK₄)
    | _ => simp [Kont.plug, hndE, ubindE, ccatchE] at hX

/-! ### The memory half, from B -/

/-- **A program in Core's relation at `F A` never gets stuck** without a platform: every
configuration its run reaches that takes no step is a value. -/
theorem stuck_of_rel {e : Expr} {A : VTy}
    (h : (B.coreB (ℍ := ℍ)).comp (.ret A) ([], (B.coreB (ℍ := ℍ)).nil) LSub.empty e
      (PMap.empty : WRes))
    {μ₁ : Heap} {X : Expr} (hX : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ X)
    (hirr : ∀ μ'' X', ¬ Step1 (ℍ := ℍ) μ₁ X μ'' X') : IsVal X := by
  have hok := platOK_init (P := Platform.none) (platOK_of_ewp platformNone_respects
    (S := []) (fun _ _ _ h => by simp [Row.find] at h)
    ((cC_effOf [] A [] LSub.empty e PMap.empty).mp h))
  obtain ⟨c', hc', hend⟩ := hok.1 ⟨μ₁, X, ()⟩ (psteps_of_steps Platform.none () hX)
  rcases Relation.ReflTransGen.cases_head hc' with rfl | ⟨c₁, h₁, -⟩
  · obtain ⟨v, -, -, -, -, -, hv, -⟩ := hend
    exact (show X = v.1 from hv) ▸ v.2
  · rcases pstep_cases h₁ with ⟨hs, -⟩ | ⟨K', n', i', v', w', s', o', -, -, hf, -⟩
    · exact absurd hs (hirr _ _)
    · simp [Platform.none, Row.find] at hf

/-- **`FinAloneAt` from `FinRowsAt` and FL at Core's world.**  The finaliser fires
(`[finalise]` or `[finalise-cancel]`, its frame being the innermost that stops the raise); its run
alone is the whole run's, inside `K₀[□; raise p]` or `K₀[cfin p □]`; where it stops at a term
that is no value and leaves no operation uncaught, the whole run is stuck (`no_step_plug`), which
FL and B2's runs exclude (`stuck_of_rel`).  What is left is an operation left uncaught, and
`FinRowsAt FR` says it is a raise of a name in `FR`. -/
theorem finAloneAt_of_finRows {FR : UInt32 → Prop} {J : TypingJ} (hR : FinRowsAt (ℍ := ℍ) FR J)
    (hFL : FL (B.coreB (ℍ := ℍ)) J) : FinAloneAt (ℍ := ℍ) FR J := by
  intro e A he μ K₀ K N D n i v hreach hK μ' t hD hirr
  have hrel := comp_of_FL hFL he
  by_cases hv : IsVal t
  · exact .inl hv
  by_cases hraise : ∃ (K' : Kont) (m j : UInt32) (w : Val),
      t = K'.plug (raiseE (.val (opPayload m j w))) ∧ K'.Catches m = false
  · obtain ⟨K', m, j, w, rfl, hK'⟩ := hraise
    obtain ⟨-, hm⟩ := hR he hreach hK hD K' true m j w rfl (by simpa [OpFree] using hK')
    exact .inr ⟨K', m, j, w, rfl, hK', hm⟩
  exfalso
  have hop : ∀ (K' : Kont) (r : Bool) (m j : UInt32) (w : Val),
      t = K'.plug (opE r (opPayload m j w)) → ¬ OpFree r m K' := by
    intro K' r m j w ht hfree
    obtain ⟨rfl, -⟩ := hR he hreach hK hD K' r m j w ht hfree
    exact hraise ⟨K', m, j, w, by simpa [opE] using ht, by simpa [OpFree] using hfree⟩
  -- the configuration at the fire point steps, or the whole run is stuck there
  have hE₀ : K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v))))) =
      (K₀.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) K)).plug
        (raiseE (.val (opPayload n i v))) := by
    rw [Kont.plug_comp]; rfl
  by_cases hstep : ∃ μ₁ E₁, Step1 (ℍ := ℍ) μ
      (K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v)))))) μ₁ E₁
  swap
  · refine (show ¬ IsVal (K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v))))))
      from ?_) (stuck_of_rel hrel hreach (fun μ'' X' h => hstep ⟨μ'', X', h⟩))
    rw [hE₀]
    exact fun h => opE_not_isVal true _ (Kont.isVal_of_plug _ h)
  obtain ⟨μ₁, E₁, hst⟩ := hstep
  rw [hE₀] at hst
  obtain ⟨Ko, f, Ki, a', hIC, hhead, rfl⟩ := step1_raise (payloadName_opPayload n i v) hst
  have hIC₀ : InnerCatch n (K₀.comp (.appR (.app (.prim .ubind) (Val.pair N D).1) K)) K₀
      (.app (.prim .ubind) (Val.pair N D).1) K :=
    ⟨rfl, hK, by simp [FrameCatches, Kont.Catches]⟩
  obtain ⟨rfl, rfl, rfl⟩ := innerCatch_unique hIC₀ hIC
  obtain ⟨rfl, N', D', hND, hcase⟩ := head_ubind_raise hhead
  obtain ⟨rfl, rfl⟩ := valPair_inj hND
  rw [← hE₀] at hst
  rcases hcase with ⟨n', i', v', -, -, rfl⟩ | ⟨err, -, rfl⟩
  · -- `[finalise]`: the finaliser runs inside `K₀[□; raise p]`
    have hX : Steps (ℍ := ℍ) Adequacy.emptyMem e μ'
        (K₀.plug ((Kont.seq .hole (raiseE (.val (opPayload n i v)))).plug t)) :=
      hreach.trans (.more hst (Steps.plug K₀ (Steps.plug (.seq .hole _) hD)))
    refine (show ¬ IsVal (K₀.plug ((Kont.seq .hole (raiseE (.val (opPayload n i v)))).plug t))
      from fun h => hv (Kont.isVal_of_plug _ (Kont.isVal_of_plug _ h))) (stuck_of_rel hrel hX ?_)
    intro μ'' X' h
    refine no_step_plug (μ' := μ'') (E := X') hirr hv hop
      (K₀.comp (.seq .hole (raiseE (.val (opPayload n i v))))) (.inr (endsAppL_comp_of rfl rfl K₀)) ?_
    rw [Kont.plug_comp]
    exact h
  · -- `[finalise-cancel]`: the finaliser runs inside `K₀[cfin p □]`
    have hX : Steps (ℍ := ℍ) Adequacy.emptyMem e μ'
        (K₀.plug ((Kont.appR (.app (.prim .cfin) (cancelVal err).1) .hole).plug t)) :=
      hreach.trans (.more hst (Steps.plug K₀ (Steps.plug (.appR _ .hole) hD)))
    refine (show ¬ IsVal (K₀.plug ((Kont.appR (.app (.prim .cfin) (cancelVal err).1) .hole).plug t))
      from fun h => hv (Kont.isVal_of_plug _ (Kont.isVal_of_plug _ h))) (stuck_of_rel hrel hX ?_)
    intro μ'' X' h
    refine no_step_plug (μ' := μ'') (E := X') hirr hv hop
      (K₀.comp (.appR (.app (.prim .cfin) (cancelVal err).1) .hole))
      (.inr (endsAppL_comp_of rfl rfl K₀)) ?_
    rw [Kont.plug_comp]
    exact h

/-- **`FinaliserOrder` from `FinRowsAt`**, at a typing system that meets FL at Core's world. -/
theorem finaliserOrder_of_finRows {J : TypingJ}
    (hR : FinRowsAt (ℍ := ℍ) (· ≠ 0) J) (hFL : FL (B.coreB (ℍ := ℍ)) J) : FinaliserOrder (ℍ := ℍ) J :=
  finaliserOrder_at (finAloneAt_of_finRows hR hFL)

/-- `NoInterception` at today's unr-free kernel. -/
theorem noInterception_tier1NU : NoInterception tier1NU := fun Θ _ _ e _ h =>
  okE_sound e (okE_of_derives (h _ (models_empty Θ)).toCDerives)

/-- **`FinaliserOrder` at today's unr-free kernel, given `FinRowsAt`**: what is left of Core's
I3.b is the operations a fired finaliser's run alone stops at. -/
theorem finaliserOrder_tier1NU_of_finRows (hR : FinRowsAt (ℍ := ℍ) (· ≠ 0) tier1NU) :
    FinaliserOrder (ℍ := ℍ) tier1NU :=
  finaliserOrder_of_finRows hR fl_core_tier1NU

/-- **`FinaliserOrder` at today's unr-free kernel, given option A's `FinRowsAt`** (decision D3): a
fired finaliser's run alone leaves no operation uncaught. -/
theorem finaliserOrder_tier1NU_of_finRowsA (hR : FinRowsAt (ℍ := ℍ) (fun _ => False) tier1NU) :
    FinaliserOrder (ℍ := ℍ) tier1NU :=
  finaliserOrder_A (finAloneAt_of_finRows hR fl_core_tier1NU)

/-! ### The route's statement (TIER1-PLAN §4, route 8.2) -/

/-- **What a typing of configurations must give for `FinRowsAt`** (route 8.2, stated for review;
TIER1-PLAN §4 records the review).  `Typed μ E S`: the term `E`, with the heap `μ`, typed at the
row `S`.  Four obligations: every configuration a run of a typed program at `F A` reaches is typed
at the pure row (`reach`, the plan's `cfgTyped_init` with `cfgTyped_step` along the whole run); at
the step that fires a finaliser, the finaliser is typed at a row of abortive operations with
nonzero names (`fire`, SPEC §19's `D : F_{Σ^abort} 1` read at run time); typing is preserved by
steps (`step`, along the finaliser's run alone); and a term typed at such a row leaves no resuming
operation and no cancel uncaught (`stop`). -/
structure RowRoute (J : TypingJ) where
  Typed : Heap → Expr → Row → Prop
  reach : ∀ {e : Expr} {A : VTy}, J.closed e (.ret A) →
    ∀ {μ : Heap} {E : Expr}, Steps (ℍ := ℍ) Adequacy.emptyMem e μ E → Typed μ E []
  fire : ∀ {μ : Heap} {K₀ K : Kont} {N D : Val} {n i : UInt32} {v : Val} {S : Row},
    Typed μ (K₀.plug (ubindE (Val.pair N D) (K.plug (raiseE (.val (opPayload n i v)))))) S →
    K.Catches n = false →
    ∃ S' : Row, RowClass.Admits .abortive S' ∧ S'.NZ ∧ Typed μ (.app (.val D) (.val .unit)) S'
  step : ∀ {μ : Heap} {e : Expr} {S : Row} {μ' : Heap} {e' : Expr},
    Typed μ e S → Step1 (ℍ := ℍ) μ e μ' e' → Typed μ' e' S
  stop : ∀ {μ : Heap} {t : Expr} {S : Row}, Typed μ t S → RowClass.Admits .abortive S → S.NZ →
    ∀ (K' : Kont) (r : Bool) (m j : UInt32) (w : Val), t = K'.plug (opE r (opPayload m j w)) →
      OpFree r m K' → r = true ∧ m ≠ 0

/-- The route's obligations give `FinRowsAt`. -/
theorem finRowsAt_of_route {J : TypingJ} (hr : RowRoute (ℍ := ℍ) J) :
    FinRowsAt (ℍ := ℍ) (· ≠ 0) J := by
  intro e A he μ K₀ K N D n i v hreach hK μ' t hD K' r m j w ht hfree
  obtain ⟨S', hS', hNZ, hT⟩ := hr.fire (hr.reach he hreach) hK
  have hsteps : ∀ {μ₁ : Heap} {e₁ : Expr} {μ₂ : Heap} {e₂ : Expr},
      Steps (ℍ := ℍ) μ₁ e₁ μ₂ e₂ → hr.Typed μ₁ e₁ S' → hr.Typed μ₂ e₂ S' := by
    intro μ₁ e₁ μ₂ e₂ h
    induction h with
    | refl => exact id
    | more h _ ih => exact fun hT₁ => ih (hr.step hT₁ h)
  have hT' : hr.Typed μ' t S' := hsteps hD hT
  exact hr.stop hT' hS' hNZ K' r m j w ht hfree

/-- The route's obligations, with FL at Core's world, give `FinAloneAt`, and so
`FinaliserOrder`. -/
theorem finaliserOrder_of_route {J : TypingJ} (hr : RowRoute (ℍ := ℍ) J)
    (hFL : FL (B.coreB (ℍ := ℍ)) J) : FinaliserOrder (ℍ := ℍ) J :=
  finaliserOrder_of_finRows (finRowsAt_of_route hr) hFL

end Targets

end
