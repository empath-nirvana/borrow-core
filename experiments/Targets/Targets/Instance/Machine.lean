import Targets.Instance.Bridges
import Targets.Base.Look

/-!
# The Instance — our labelled machine, run

The machine layer the bridges and the statement checks read, at Core σ=[]:

* the label of each head step (`labelOf_tau_of`, `labelOf_fire`, `labelOf_uthen`,
  `labelOf_cfret`, `labelOf_cferr`);
* **determinism** (`det_ourInst`, `rstep_det`): a step whose redex allocates nothing is the only
  step of its configuration, under every runner;
* a run `look` computes is a path of `ourInst` (`rpath_chainPath`), and from a configuration
  whose every step `look` decides, it is the only complete run (`complete_chainPath`);
* an A-value that is not a Core value holds a variable at an evaluation position
  (`exists_var_of_isOVal`), so a configuration holding one takes no step.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa)
open Targets (RowForm EffCtx orowRF Look look lookRun lookEnd HeadChain LookOK)

variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-! ### The label of a head step -/

/-- The redexes `labelOf` reads: a finaliser frame and a cancel-mode finaliser frame. -/
def finHead : Expr → Bool
  | .app (.app (.prim .ubind) _) _ => true
  | .app (.app (.prim .cfin) _) _ => true
  | _ => false

theorem labelOf_tau_of {a : Expr} (h : finHead a = false) : labelOf RF Ξ a = .tau := by
  unfold labelOf
  rw [dif_neg, if_neg, dif_neg]
  · rintro ⟨s, K, m, j, w, rfl⟩; simp [finHead, cfinE] at h
  · rintro ⟨s, w, rfl⟩; simp [finHead, cfinE] at h
  · rintro ⟨N, D, e, rfl, -⟩; simp [finHead, ubindE] at h

theorem cfinE_inj {s s' : Val} {e e' : Expr} (h : cfinE s e = cfinE s' e') : s = s' ∧ e = e' := by
  simp only [cfinE, Expr.app.injEq, true_and] at h
  exact ⟨Subtype.ext h.1, h.2⟩

theorem ubindE_inj {s s' : Val} {e e' : Expr} (h : ubindE s e = ubindE s' e') :
    s = s' ∧ e = e' := by
  simp only [ubindE, Expr.app.injEq, true_and] at h
  exact ⟨Subtype.ext h.1, h.2⟩

theorem labelOf_fire {N D : Val} {e : Expr} (he : ¬ IsVal e) :
    labelOf RF Ξ (ubindE (Val.pair N D) e) = .fire (finE D.1) := by
  unfold labelOf
  have h : ∃ (N' D' : Val) (e' : Expr), ubindE (Val.pair N D) e = ubindE (Val.pair N' D') e' ∧
      ¬ IsVal e' := ⟨N, D, e, rfl, he⟩
  rw [dif_pos h]
  obtain ⟨e', he', -⟩ := Classical.choose_spec (Classical.choose_spec h)
  obtain ⟨-, hD⟩ := valPair_inj (congrArg Subtype.val (ubindE_inj he').1)
  rw [← hD]

theorem labelOf_uthen (N D w : Val) : labelOf RF Ξ (ubindE (Val.pair N D) (.val w)) = .tau := by
  unfold labelOf
  rw [dif_neg, if_neg, dif_neg]
  · rintro ⟨s, K, m, j, w', h⟩; simp [ubindE, cfinE] at h
  · rintro ⟨s, w', h⟩; simp [ubindE, cfinE] at h
  · rintro ⟨N', D', e, h, he⟩
    simp only [ubindE, Expr.app.injEq, true_and] at h
    exact he (h.2 ▸ w.2)

theorem labelOf_cfret (s w : Val) : labelOf RF Ξ (cfinE s (.val w)) = .finEnd none := by
  unfold labelOf
  rw [dif_neg, if_pos ⟨s, w, rfl⟩]
  rintro ⟨N, D, e, h, -⟩; simp [ubindE, cfinE] at h

theorem labelOf_cferr (s : Val) (K : Kont) (m j : UInt32) (w : Val) :
    labelOf RF Ξ (cfinE s (K.plug (raiseE (.val (opPayload m j w))))) =
      .finEnd (errOf RF Ξ m j w) := by
  unfold labelOf
  have h : ∃ (s' : Val) (K' : Kont) (m' j' : UInt32) (w' : Val),
      cfinE s (K.plug (raiseE (.val (opPayload m j w)))) =
        cfinE s' (K'.plug (raiseE (.val (opPayload m' j' w')))) := ⟨s, K, m, j, w, rfl⟩
  rw [dif_neg, if_neg, dif_pos h]
  · have hs := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec h))))
    obtain ⟨-, hp⟩ := plug_raise_inj (cfinE_inj hs).2
    obtain ⟨hm, hj, hw⟩ := opPayload_inj hp
    rw [← hw, ← hj, ← hm]
  · rintro ⟨s', w', h'⟩
    exact plug_raise_ne_val K _ w' (cfinE_inj h').2
  · rintro ⟨N, D, e, h', -⟩; simp [ubindE, cfinE] at h'

/-! ### Open values -/

/-- An A-value that is not a Core value holds a variable at an evaluation position. -/
theorem exists_var_of_isOVal : ∀ {e : Expr}, IsOVal e → ¬ IsVal e → ∃ (K : Kont) (j : ℕ),
    e = K.plug (.var j)
  | _, .var j, _ => ⟨.hole, j, rfl⟩
  | _, .unit, h => absurd .unit h
  | _, @IsOVal.pair a b ha hb, h => by
      by_cases hva : IsVal a
      · obtain ⟨K, j, rfl⟩ := exists_var_of_isOVal hb (fun hvb => h (.pair hva hvb))
        exact ⟨.pairR ⟨a, hva⟩ K, j, rfl⟩
      · obtain ⟨K, j, rfl⟩ := exists_var_of_isOVal ha hva
        exact ⟨.pairL K b, j, rfl⟩
  | _, .inj₁ ha, h => by
      obtain ⟨K, j, rfl⟩ := exists_var_of_isOVal ha (fun hv => h (.inj₁ hv))
      exact ⟨.inj₁ K, j, rfl⟩
  | _, .inj₂ ha, h => by
      obtain ⟨K, j, rfl⟩ := exists_var_of_isOVal ha (fun hv => h (.inj₂ hv))
      exact ⟨.inj₂ K, j, rfl⟩
  | _, .lam, h => absurd .lam h
  | _, .loc, h => absurd .loc h
  | _, .prim, h => absurd .prim h
  | _, .storeV ha, h => by
      obtain ⟨K, j, rfl⟩ := exists_var_of_isOVal ha (fun hv => h (.storeV hv))
      exact ⟨.appR (.prim .store) K, j, rfl⟩

/-- An operation whose argument is an A-value: the payload is a Core value, or the term holds a
variable at an evaluation position. -/
theorem opArg_val_or_var (K : Kont) (r : Bool) (n i : UInt32) (v : OVal) :
    (∃ w : Val, v.1 = w.1) ∨ ∃ (K' : Kont) (j : ℕ),
      K.plug (if r then raiseE (opArgE n i v.1) else performE (opArgE n i v.1)) =
        K'.plug (.var j) := by
  by_cases hv : IsVal v.1
  · exact .inl ⟨⟨v.1, hv⟩, rfl⟩
  · obtain ⟨Kv, j, hKv⟩ := exists_var_of_isOVal v.2 hv
    refine .inr ⟨K.comp (.appR (.prim (if r then .raise else .perform))
      (.pairR (Val.i32 n) (.pairR (Val.i32 i) Kv))), j, ?_⟩
    rw [Kont.plug_comp]
    cases r <;> simp [Kont.plug, opArgE, performE, raiseE, hKv]

/-! ### Determinism -/

theorem no_head_lit {μ μ' : Heap} {c : IntLit} {v : Val} {a' : Expr} :
    ¬ Head (ℍ := ℍ) μ (.app (.prim (.lit c)) (.val v)) μ' a' := by
  intro h
  generalize hE : Expr.app (.prim (.lit c)) (.val v) = E at h
  cases h <;> simp_all [hndE, ubindE, ccatchE, cfinE]

/-- The driver's configurations take no machine step. -/
theorem no_step1_drive {μ μ' : Heap} (v : Val) {t : Expr} :
    ¬ Step1 (ℍ := ℍ) μ (driveE (.val v)) μ' t := by
  rintro ⟨K, a, a', hE, -, hh⟩
  cases K with
  | hole =>
      simp only [Kont.plug, driveE, driveMark] at hE
      subst hE
      exact no_head_lit hh
  | appR f K =>
      simp only [Kont.plug, driveE, Expr.app.injEq] at hE
      exact hh.not_isVal (K.isVal_of_plug (by rw [← hE.2]; exact v.2))
  | appL K w =>
      simp only [Kont.plug, driveE, driveMark, Expr.app.injEq] at hE
      have := hE.1
      cases K <;> simp [Kont.plug] at this
      subst this
      exact hh.not_isVal .prim
  | _ => simp [Kont.plug, driveE] at hE

/-- **A step whose redex allocates nothing is the only step of its configuration.** -/
theorem det_ourInst {μ μ' : Heap} {K : Kont} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a')
    (hn : a.allocs = false) {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} {c' : Heap × Expr}
    (h : OStep (ℍ := ℍ) RF Ξ (μ, K.plug a) ev c') :
    ev = labelOf RF Ξ a ∧ c' = (μ', K.plug a') := by
  generalize hc : (μ, K.plug a) = c at h
  cases h with
  | mach h' =>
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, hc⟩ := hc
      obtain ⟨rfl, rfl⟩ := plug_decomp hh _ _ h' hc.symm
      obtain ⟨rfl, rfl⟩ := head_det hh hn h' rfl
      exact ⟨rfl, rfl⟩
  | again =>
      have hs : Step1 (ℍ := ℍ) μ (K.plug a) μ' (K.plug a') := ⟨K, a, a', rfl, rfl, hh⟩
      simp only [Prod.mk.injEq] at hc
      rw [hc.2] at hs
      exact (no_step1_drive _ hs).elim
  | fin =>
      have hs : Step1 (ℍ := ℍ) μ (K.plug a) μ' (K.plug a') := ⟨K, a, a', rfl, rfl, hh⟩
      simp only [Prod.mk.injEq] at hc
      rw [hc.2] at hs
      exact (no_step1_drive _ hs).elim

/-- A configuration with a machine step is not stopped at an operation the runner answers. -/
theorem no_io_of_step1 {μ μ' : Heap} {e t : Expr} (hs : Step1 (ℍ := ℍ) μ e μ' t) (K : Kont)
    (l : (RF.alg Ξ).Lab) (i : ℕ) (v : OVal)
    (he : e = K.plug (performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)))
    (hK : K.HasHnd (RF.name Ξ l) = false) : False := by
  subst he
  rcases opArg_val_or_var K false (RF.name Ξ l) (UInt32.ofNat i) v with ⟨w, hw⟩ | ⟨K', j, hK'⟩
  · have : K.plug (performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)) =
        K.plug (opE false (opPayload (RF.name Ξ l) (UInt32.ofNat i) w)) := by
      simp [opE, opArgE, opPayload, hw, performE, Val.pair, Val.i32]
    rw [this] at hs
    exact opPlug_no_step (payloadName_opPayload _ _ _) (by simpa [OpFree] using hK) hs
  · simp only [Bool.false_eq_true, if_false] at hK'
    rw [hK'] at hs
    exact step1_plug_var K' j hs

/-- **Determinism under every runner**: at a configuration whose redex allocates nothing, the
machine's step is the only step, and the runner answers nothing. -/
theorem rstep_det {R : (ourInst (ℍ := ℍ) RF Ξ J).Runner} {s : R.St} {μ μ' : Heap} {K : Kont}
    {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a') (hn : a.allocs = false)
    {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} {c' : (Heap × Expr) × R.St}
    (h : (ourInst (ℍ := ℍ) RF Ξ J).RStep R ((μ, K.plug a), s) ev c') :
    ev = labelOf RF Ξ a ∧ c' = ((μ', K.plug a'), s) := by
  generalize hc : ((μ, K.plug a), s) = c at h
  cases h with
  | mach h' =>
      obtain ⟨rfl, rfl⟩ := det_ourInst hh hn h'
      exact ⟨rfl, rfl⟩
  | io hterm hK =>
      exact (no_io_of_step1 ⟨K, a, a', rfl, rfl, hh⟩ _ _ _ _ hterm hK).elim

/-! ### The runs `look` computes, as paths -/

section Paths
variable (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner)

/-- The path of a chain of head steps, at the memory `μ` and the runner's state `s`. -/
def chainPath (μ : Heap) (s : R.St) (q : List (Kont × Expr × Expr)) :
    List ((ourInst (ℍ := ℍ) RF Ξ J).Event × (ourInst (ℍ := ℍ) RF Ξ J).RConf R) :=
  q.map fun x => (labelOf RF Ξ x.2.1, ((μ, x.1.plug x.2.2), s))

theorem rpath_chainPath {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q e' →
      (ourInst (ℍ := ℍ) RF Ξ J).RPath R ((μ, e), s) (chainPath R μ s q)
  | _, _, _, .nil => .nil
  | _, _, _, .cons hh _ hq => .cons (.mach (OStep.mach (hh μ))) (rpath_chainPath hq)

theorem lastC_chainPath {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q e' →
      (ourInst (ℍ := ℍ) RF Ξ J).lastC ((μ, e), s) (chainPath R μ s q) = ((μ, e'), s)
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ _ hq =>
      (A.EffectSystem.lastC_cons (S := ourInst (ℍ := ℍ) RF Ξ J) _ _ _ _).trans
        (lastC_chainPath hq)

/-- The terms of a chain's configurations, the start included. -/
def chainTerms (e : Expr) (q : List (Kont × Expr × Expr)) : List Expr :=
  e :: q.map fun x => x.1.plug x.2.2

theorem chainTerms_length (e : Expr) (q : List (Kont × Expr × Expr)) :
    (chainTerms e q).length = q.length + 1 := by
  simp [chainTerms]

theorem cfgAt_chainPath {μ : Heap} {s : R.St} : ∀ (e : Expr) (q : List (Kont × Expr × Expr))
    (j : ℕ) {t : Expr}, (chainTerms e q)[j]? = some t →
      (ourInst (ℍ := ℍ) RF Ξ J).cfgAt ((μ, e), s) (chainPath R μ s q) j = ((μ, t), s)
  | e, [], 0, t, h => by
      simp only [chainTerms, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
  | e, [], j + 1, t, h => by simp [chainTerms] at h
  | e, x :: q, 0, t, h => by
      simp only [chainTerms, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
  | e, x :: q, j + 1, t, h => by
      have h' : (chainTerms (x.1.plug x.2.2) q)[j]? = some t := by
        simpa [chainTerms] using h
      have ih := cfgAt_chainPath (μ := μ) (s := s) (x.1.plug x.2.2) q j h'
      have hj : j < q.length + 1 := by
        have := (List.getElem?_eq_some_iff.mp h').1
        rwa [chainTerms_length] at this
      unfold A.EffectSystem.cfgAt at ih ⊢
      simp only [chainPath, List.map_cons, List.map_map] at ih ⊢
      rw [List.getElem?_cons_succ]
      rw [List.getElem?_eq_getElem (by simpa using hj)] at ih ⊢
      exact ih

end Paths

/-! ### Subterms at evaluation positions -/

/-- The subterms of `e` at evaluation positions, and more: every subterm reached without entering
a binder's body or a branch. -/
def evalSubs : Expr → List Expr
  | .pair a b => .pair a b :: (evalSubs a ++ evalSubs b)
  | .inj₁ a => .inj₁ a :: evalSubs a
  | .inj₂ a => .inj₂ a :: evalSubs a
  | .seq a b => .seq a b :: evalSubs a
  | .letpair a b => .letpair a b :: evalSubs a
  | .case a b₁ b₂ => .case a b₁ b₂ :: evalSubs a
  | .app f a => .app f a :: (evalSubs f ++ evalSubs a)
  | e => [e]

theorem self_mem_evalSubs (e : Expr) : e ∈ evalSubs e := by
  cases e <;> simp [evalSubs]

/-- What a context holds at its hole is among the term's evaluation subterms. -/
theorem mem_evalSubs_plug : ∀ (K : Kont) (s : Expr), s ∈ evalSubs (K.plug s)
  | .hole, s => self_mem_evalSubs s
  | .pairL K _, s | .letpair K _, s | .case K _ _, s | .seq K _, s | .inj₁ K, s | .inj₂ K, s
  | .appL K _, s => by simp [Kont.plug, evalSubs, mem_evalSubs_plug K s]
  | .pairR _ K, s | .appR _ K, s => by simp [Kont.plug, evalSubs, mem_evalSubs_plug K s]

theorem any_evalSubs_plug {p : Expr → Bool} (K : Kont) {s : Expr} (hs : p s = true) :
    (evalSubs (K.plug s)).any p = true :=
  List.any_eq_true.mpr ⟨s, mem_evalSubs_plug K s, hs⟩

/-- `resume k w` at our instance: `(λy. k (inj₁ ()) y) w`. -/
def resumeShape : Expr → Bool
  | .app (.lam (.app (.app _ (.inj₁ .unit)) (.var 0))) _ => true
  | _ => false

theorem resumeShape_resumeE (k w : Expr) : resumeShape (resumeE k w) = true := rfl

/-- `cancel κ` at a continuation `κ = kappa n H K`: `κ (inj₂ ())`. -/
def kappaCancelShape : Expr → Bool
  | .app (.lam (.case (.var 0) _ _)) (.inj₂ .unit) => true
  | _ => false

theorem kappaCancelShape_cancelE (n : UInt32) (H : Val) (K : Kont) :
    kappaCancelShape (cancelE (kappa n H K)) = true := rfl

/-- `perform p`. -/
def performShape : Expr → Bool
  | .app (.prim .perform) _ => true
  | _ => false

/-- A handler at an evaluation position whose body has a `perform` at one. -/
def catchShape (t : Expr) : Bool :=
  (evalSubs t).any fun s =>
    match s with
    | .app (.app (.prim .hnd) _) b => (evalSubs b).any performShape
    | _ => false

theorem catchShape_plug (K₀ : Kont) (n : UInt32) (r : Expr) (cs : List Expr) (K : Kont)
    (p : Expr) : catchShape (K₀.plug ((handleK n r cs).plug (K.plug (performE p)))) = true := by
  unfold catchShape
  refine any_evalSubs_plug K₀ ?_
  simp only [handleK, Kont.plug]
  exact any_evalSubs_plug K (p := performShape) rfl

/-! ### Chains as reachability and as store-keeping steps -/

theorem rreach_of_chain (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q e' →
      (ourInst (ℍ := ℍ) RF Ξ J).RReach R ((μ, e), s) ((μ, e'), s)
  | _, _, _, .nil => Relation.ReflTransGen.refl
  | _, _, _, .cons hh _ hq =>
      Relation.ReflTransGen.head ⟨_, .mach (OStep.mach (hh μ))⟩ (rreach_of_chain R hq)

theorem pureSteps_of_chain {μ : Heap} :
    ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q e' →
      (ourInst (ℍ := ℍ) RF Ξ J).PureSteps (μ, e) (μ, e')
  | _, _, _, .nil => Relation.ReflTransGen.refl
  | _, _, _, .cons hh _ hq =>
      Relation.ReflTransGen.head ⟨_, OStep.mach (hh μ), rfl⟩ (pureSteps_of_chain hq)

/-- A context is injective in what it holds. -/
theorem plug_inj_hole : ∀ (K : Kont) {a b : Expr}, K.plug a = K.plug b → a = b
  | .hole, _, _, h => h
  | .pairL K _, _, _, h | .letpair K _, _, _, h | .case K _ _, _, _, h | .seq K _, _, _, h
  | .appL K _, _, _, h => by
      simp only [Kont.plug, Expr.pair.injEq, Expr.letpair.injEq, Expr.case.injEq,
        Expr.seq.injEq, Expr.app.injEq] at h
      exact plug_inj_hole K h.1
  | .pairR _ K, _, _, h | .appR _ K, _, _, h => by
      simp only [Kont.plug, Expr.pair.injEq, Expr.app.injEq] at h
      exact plug_inj_hole K h.2
  | .inj₁ K, _, _, h | .inj₂ K, _, _, h => by
      simp only [Kont.plug, Expr.inj₁.injEq, Expr.inj₂.injEq] at h
      exact plug_inj_hole K h

/-- A `raise` of the name `n`. -/
def raiseShape (n : UInt32) : Expr → Bool
  | .app (.prim .raise) p => nameOf? p == some n
  | _ => false

/-- A cancel-mode finaliser frame. -/
def cfinShape : Expr → Bool
  | .app (.app (.prim .cfin) _) _ => true
  | _ => false

/-! ### The only complete run -/

/-- A configuration at a Core value takes no step under any runner. -/
theorem no_rstep_val (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} (v : Val)
    {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} {c' : (Heap × Expr) × R.St}
    (h : (ourInst (ℍ := ℍ) RF Ξ J).RStep R ((μ, v.1), s) ev c') : False := by
  generalize hc : ((μ, v.1), s) = c at h
  cases h with
  | mach h' =>
      change OStep (ℍ := ℍ) RF Ξ (μ, v.1) _ _ at h'
      generalize hcc : (μ, v.1) = cc at h'
      cases h' with
      | mach hh =>
          simp only [Prod.mk.injEq] at hcc
          exact hh.not_isVal (Kont.isVal_of_plug _ (hcc.2 ▸ v.2))
      | again =>
          simp only [Prod.mk.injEq] at hcc
          exact not_isOVal_prim_app (p := .lit (.u8 0)) (by decide) _
            (hcc.2 ▸ isOVal_of_isVal v.2)
      | fin =>
          simp only [Prod.mk.injEq] at hcc
          exact not_isOVal_prim_app (p := .lit (.u8 0)) (by decide) _
            (hcc.2 ▸ isOVal_of_isVal v.2)
  | io hterm _ _ _ =>
      have h' : v.1 = _ := hterm
      exact not_isOVal_prim_app (p := .perform) (by decide) _
        (isOVal_of_plug _ (h' ▸ isOVal_of_isVal v.2))

/-- **A run `look` computes to a value is the only complete run**, under every runner. -/
theorem complete_chain (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q₀ : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q₀ e' → IsVal e' →
      ∀ q, (ourInst (ℍ := ℍ) RF Ξ J).CompleteFrom R ((μ, e), s) q →
        ((ourInst (ℍ := ℍ) RF Ξ J).lastC ((μ, e), s) q).1.2 = e'
  | _, _, _, .nil, hv, q, ⟨hp, _⟩ => by
      cases hp with
      | nil => rfl
      | cons hst _ => exact (no_rstep_val R ⟨_, hv⟩ hst).elim
  | _, _, _, @HeadChain.cons _ _ K a a' e' q₀ hh hn hq, hv, q, ⟨hp, hlast⟩ => by
      cases hp with
      | nil =>
          exact absurd (hlast.2 _ _ (OStep.mach (hh μ))) (fun h => h)
      | @cons _ ev c₁ q' hst hp' =>
          obtain ⟨-, rfl⟩ := rstep_det (hh μ) hn hst
          have := complete_chain R hq hv q' ⟨hp', by
            rw [← A.EffectSystem.lastC_cons (S := ourInst (ℍ := ℍ) RF Ξ J) _ _ ev]
            exact hlast⟩
          exact (congrArg (fun x : (ourInst (ℍ := ℍ) RF Ξ J).RConf R => x.1.2)
            (A.EffectSystem.lastC_cons (S := ourInst (ℍ := ℍ) RF Ξ J) _ _ ev q')).trans this

/-- A chain of steps none of which is a finaliser's shows no event. -/
theorem obs_chainPath (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) (μ : Heap) (s : R.St)
    (q : List (Kont × Expr × Expr)) (h : q.all (fun x => finHead x.2.1 == false) = true) :
    (ourInst (ℍ := ℍ) RF Ξ J).obs (chainPath R μ s q) = [] := by
  unfold A.EffectSystem.obs chainPath
  rw [List.filter_eq_nil_iff]
  intro ev hev
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hev
  obtain ⟨x, hx, rfl⟩ := hev
  have hx' := List.all_eq_true.mp h x hx
  simp only [beq_iff_eq] at hx'
  rw [labelOf_tau_of hx']
  simp [Targets.A.Ev.Obs]

/-- `p` holds of some subterm. -/
def occursIn (p : Expr → Bool) : Expr → Bool
  | .pair a b => p (.pair a b) || occursIn p a || occursIn p b
  | .inj₁ a => p (.inj₁ a) || occursIn p a
  | .inj₂ a => p (.inj₂ a) || occursIn p a
  | .lam b => p (.lam b) || occursIn p b
  | .seq a b => p (.seq a b) || occursIn p a || occursIn p b
  | .letpair a b => p (.letpair a b) || occursIn p a || occursIn p b
  | .case a b c => p (.case a b c) || occursIn p a || occursIn p b || occursIn p c
  | .app f a => p (.app f a) || occursIn p f || occursIn p a
  | e => p e

end Targets.Inst

end
