import Targets.Instance.Bridges
import Targets.Base.Look
import Targets.A.UnaryLaws

/-!
# The Instance — our labelled machine, run

The machine layer the bridges and the statement checks read, at Core σ=[]:

* the label of each head step (`labelOf_tau_of`, `labelOf_fire`, `labelOf_uthen`,
  `labelOf_cfret`, `labelOf_cferr`);
* **determinism** (`det_ourInst`, `rstep_det`): a step whose redex allocates nothing is the only
  step of its configuration, under every runner;
* a run `look` computes is a path of `ourInst` (`rpath_chainPath`), and from a configuration
  whose every step `look` decides, it is the only complete run (`complete_chain`);
* **runs that join** (`runsAlike_of_join`): two terms that reach one term by head steps that
  allocate nothing and show no event run alike in every evaluation context;
* an A-value that is not a Core value holds a variable at an evaluation position
  (`exists_var_of_isOVal`), so a configuration holding one takes no step;
* **S0** (`appLaw_ourInst`, `congr_ourInst`, `opStuck_ourInst`, `loopLaws_ourInst`,
  `driveLaws_ourInst`; `machShape_orow` at the open-row form) and S4's laws that read no capture
  cell (`retLaw_ourInst`, `catch_unr_ourInst`, `abortLaw_ourInst`, `resumeLaw_ourInst`,
  `cancelLaw_ourInst`, `thenLaw_ourInst`, `finLaw_ourInst`; S4 with no cell where resuming
  operations are unrestricted, `handlerSemNoCell_ourInst`; S4 itself is
  `Targets/Instance/HandlerCell.lean`'s).  κ's administrative steps are `ewp_kappa_resume`'s and
  `ewp_kappa_cancel`'s;
  a loop's are Core's `etaN_obs`, `nodeV_*_steps`, `mapV_*_steps` and `hN_steps`, read through
  `pureSteps_of_core`.

The laws that assert a step take `LiveOK`: every configuration a typed closed program reaches,
under a runner that keeps its protocol, has a closed term and goes on (`GoesOn`).  Its source is
`Live`'s docstring ("a calculus steps on closed values only") and RESTRUCTURE §4.1's reading of the
junk encodings ("no configuration a typed closed program reaches has one").  Without it, an open
A-value, a handler of non-values (where `captureE`, `cancelOfE` and `unfoldE` are `()`) or a loop
answer of the wrong shape leaves a configuration stuck where the law asks for a step.  It states
nothing about which step a configuration takes.  It is met at a typing system that types one
program with a handler, an operation and a continuation (`liveOK_JnLog`,
`Targets/Instance/LiveWitness.lean`), and at today's kernel at every effect context
(`liveOK_tier1Open`, `Targets/I/Restricted/InstanceSafety.lean`); its discharge at `J₁` is piece
4's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  capTag kappaAt
  hndVal cancelVal kappa clauseAt)
open Targets (RowForm EffCtx orowRF Look look lookRun lookEnd HeadChain LookOK StuckAt stuck_no_step
  stuck_ne_op stuckAt_unit_app)

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

/-! ### Operation indices beyond `UInt32` -/

/-- The junk of an index beyond `UInt32`, plugged: a variable at an evaluation position. -/
theorem opJunk_plug (K : Kont) (r : Bool) :
    K.plug (opJunk r) =
      (K.comp (.appR (.prim (if r then .raise else .perform)) .hole)).plug (.var 0) := by
  rw [Kont.plug_comp]; rfl

/-- A plugged `perform`: the Core operation at an index below `2³²`, the junk beyond it. -/
theorem perform_cases (l : (RF.alg Ξ).Lab) (i : ℕ) (v : OVal) :
    (i < 2 ^ 32 ∧ (ourInst (ℍ := ℍ) RF Ξ J).perform l i v =
      performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)) ∨
    (¬ i < 2 ^ 32 ∧ (ourInst (ℍ := ℍ) RF Ξ J).perform l i v = opJunk false) := by
  by_cases hi : i < 2 ^ 32
  · exact .inl ⟨hi, perform_eq (ℍ := ℍ) (l := l) v hi⟩
  · exact .inr ⟨hi, perform_junk (ℍ := ℍ) (l := l) v hi⟩

/-- A plugged `raise`: the Core raise at an index below `2³²`, the junk beyond it. -/
theorem raise_cases (l : (RF.alg Ξ).Lab) (i : ℕ) (v : OVal) :
    (i < 2 ^ 32 ∧ (ourInst (ℍ := ℍ) RF Ξ J).raise l i v =
      raiseE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)) ∨
    (¬ i < 2 ^ 32 ∧ (ourInst (ℍ := ℍ) RF Ξ J).raise l i v = opJunk true) := by
  by_cases hi : i < 2 ^ 32
  · exact .inl ⟨hi, raise_eq (ℍ := ℍ) (l := l) v hi⟩
  · exact .inr ⟨hi, raise_junk (ℍ := ℍ) (l := l) v hi⟩

/-- `perform` and `raise` are applications of their primitives. -/
theorem perform_app (l : (RF.alg Ξ).Lab) (i : ℕ) (v : OVal) :
    ∃ x, (ourInst (ℍ := ℍ) RF Ξ J).perform l i v = .app (.prim .perform) x := by
  rcases perform_cases (ℍ := ℍ) (J := J) l i v with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact ⟨_, rfl⟩

theorem raise_app (l : (RF.alg Ξ).Lab) (i : ℕ) (v : OVal) :
    ∃ x, (ourInst (ℍ := ℍ) RF Ξ J).raise l i v = .app (.prim .raise) x := by
  rcases raise_cases (ℍ := ℍ) (J := J) l i v with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact ⟨_, rfl⟩

/-- A closed term holds no junk. -/
theorem not_closed_opJunk (K : Kont) (r : Bool) : closedAt 0 (K.plug (opJunk r)) = false := by
  rw [opJunk_plug]
  induction (K.comp (.appR (.prim (if r then .raise else .perform)) .hole)) generalizing r with
  | hole => rfl
  | _ => simp_all [Kont.plug, closedAt]

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
    (he : e = K.plug ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v))
    (hK : K.HasHnd (RF.name Ξ l) = false) : False := by
  rcases perform_cases (ℍ := ℍ) (J := J) l i v with ⟨-, hp⟩ | ⟨-, hp⟩
  swap
  · rw [hp, opJunk_plug] at he
    subst he
    exact step1_plug_var _ 0 hs
  rw [hp] at he
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

theorem catchShape_plug (K₀ : Kont) (n : UInt32) (qs r : Expr) (cs : List Expr) (K : Kont)
    (p : Expr) : catchShape (K₀.plug ((handleK n qs r cs).plug (K.plug (performE p)))) = true := by
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
  | @io _ _ _ K l i u _ hterm _ _ _ =>
      have h' : v.1 = K.plug ((ourInst (ℍ := ℍ) RF Ξ J).perform l i u) := hterm
      obtain ⟨x, hx⟩ := perform_app (ℍ := ℍ) (J := J) l i u
      rw [hx] at h'
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

/-! ### Runs that join -/

/-- A chain of head steps, in a context. -/
theorem _root_.Targets.HeadChain.plug (K₀ : Kont) : ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)},
    HeadChain (ℍ := ℍ) e q e' →
      HeadChain (ℍ := ℍ) (K₀.plug e) (q.map fun x => (K₀.comp x.1, x.2.1, x.2.2)) (K₀.plug e')
  | _, _, _, .nil => .nil
  | _, _, _, @HeadChain.cons _ _ K a a' _ _ hh hn hq => by
      have := HeadChain.cons (K := K₀.comp K) hh hn
        (by rw [Kont.plug_comp]; exact HeadChain.plug K₀ hq)
      rw [Kont.plug_comp] at this
      exact this

/-- At a configuration whose redex allocates nothing and whose step shows no event, the complete
runs are that step followed by the complete runs of the next configuration. -/
theorem obsFrom_step_iff (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} {K : Kont}
    {a a' : Expr} (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a') (hn : a.allocs = false)
    (hτ : (labelOf RF Ξ a).Obs = false) (v : OVal) (tr : List (ourInst (ℍ := ℍ) RF Ξ J).Event) :
    (ourInst (ℍ := ℍ) RF Ξ J).ObsFrom R ((μ, K.plug a), s) v tr ↔
      (ourInst (ℍ := ℍ) RF Ξ J).ObsFrom R ((μ, K.plug a'), s) v tr := by
  have hτ' : (labelOf RF Ξ a : (ourInst (ℍ := ℍ) RF Ξ J).Event).Obs = false := hτ
  constructor
  · rintro ⟨q, ⟨hp, hlast⟩, hv, htr⟩
    cases hp with
    | nil => exact absurd (hlast.2 _ _ (OStep.mach (hh μ))) (fun h => h)
    | @cons _ ev c₁ q' hst hp' =>
        obtain ⟨rfl, rfl⟩ := rstep_det (hh μ) hn hst
        refine ⟨q', ⟨hp', ?_⟩, ?_, ?_⟩
        · rw [← A.EffectSystem.lastC_cons (S := ourInst (ℍ := ℍ) RF Ξ J) _ _ (labelOf RF Ξ a)]
          exact hlast
        · rw [← A.EffectSystem.lastC_cons (S := ourInst (ℍ := ℍ) RF Ξ J) _ _ (labelOf RF Ξ a)]
          exact hv
        · rw [← htr]
          exact (List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ')).symm
  · rintro ⟨q, ⟨hp, hlast⟩, hv, htr⟩
    have hc := A.EffectSystem.lastC_cons (S := ourInst (ℍ := ℍ) RF Ξ J) ((μ, K.plug a), s)
      ((μ, K.plug a'), s) (labelOf RF Ξ a) q
    refine ⟨(labelOf RF Ξ a, ((μ, K.plug a'), s)) :: q,
      ⟨.cons (.mach (OStep.mach (hh μ))) hp, ?_⟩, ?_, ?_⟩
    · exact (congrArg (fun x => (ourInst (ℍ := ℍ) RF Ξ J).IsVal x.1) hc).mpr hlast
    · exact (congrArg (fun x => (ourInst (ℍ := ℍ) RF Ξ J).term x.1 =
        (ourInst (ℍ := ℍ) RF Ξ J).ret v) hc).mpr hv
    · rw [← htr]
      exact List.filter_cons_of_neg (Bool.eq_false_iff.mp hτ')

/-- Along a chain of head steps that allocate nothing and show no event, the complete runs of the
start and of the end show the same answers and traces. -/
theorem obsFrom_chain_iff (R : (ourInst (ℍ := ℍ) RF Ξ J).Runner) {μ : Heap} {s : R.St} :
    ∀ {e e' : Expr} {q : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q e' →
      (∀ x ∈ q, (labelOf RF Ξ x.2.1).Obs = false) → ∀ v tr,
      ((ourInst (ℍ := ℍ) RF Ξ J).ObsFrom R ((μ, e), s) v tr ↔
        (ourInst (ℍ := ℍ) RF Ξ J).ObsFrom R ((μ, e'), s) v tr)
  | _, _, _, .nil, _, _, _ => Iff.rfl
  | _, _, _, .cons hh hn hq, hτ, v, tr =>
      (obsFrom_step_iff R hh hn (hτ _ List.mem_cons_self) v tr).trans
        (obsFrom_chain_iff R hq (fun x hx => hτ x (List.mem_cons_of_mem _ hx)) v tr)

/-- **Two terms that reach one term by head steps that allocate nothing and show no event run
alike in every evaluation context.** -/
theorem runsAlike_of_join {t₁ t₂ t : Expr} {q₁ q₂ : List (Kont × Expr × Expr)}
    (h₁ : HeadChain (ℍ := ℍ) t₁ q₁ t) (h₂ : HeadChain (ℍ := ℍ) t₂ q₂ t)
    (hτ₁ : ∀ x ∈ q₁, (labelOf RF Ξ x.2.1).Obs = false)
    (hτ₂ : ∀ x ∈ q₂, (labelOf RF Ξ x.2.1).Obs = false) :
    (ourInst (ℍ := ℍ) RF Ξ J).RunsAlike t₁ t₂ := by
  rintro R - P ε A ⟨⟨μ, e⟩, s⟩ (K₀ : Kont) - - - hterm v tr
  change e = K₀.plug t₁ at hterm
  subst hterm
  have lift : ∀ {q : List (Kont × Expr × Expr)}, (∀ x ∈ q, (labelOf RF Ξ x.2.1).Obs = false) →
      ∀ x ∈ q.map (fun x => (K₀.comp x.1, x.2.1, x.2.2)), (labelOf RF Ξ x.2.1).Obs = false := by
    intro q hq x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hq y hy
  exact (obsFrom_chain_iff R (h₁.plug K₀) (lift hτ₁) v tr).trans
    (obsFrom_chain_iff R (h₂.plug K₀) (lift hτ₂) v tr).symm

/-! ### What typing gives at run time -/

/-- At `c` evaluation goes on: `c` is at a Core value, it steps, or it is stopped at an operation
its context does not catch. -/
def GoesOn (RF : RowForm) (Ξ : EffCtx) (c : Heap × Expr) : Prop :=
  (∃ v : Val, c.2 = v.1) ∨ (∃ ev c', OStep (ℍ := ℍ) RF Ξ c ev c') ∨
    ∃ (r : Bool) (K : Kont) (p : Val) (n : UInt32), c.2 = K.plug (opE r p) ∧
      payloadName p = some n ∧ OpFree r n K

/-- **What typing gives at run time**: every configuration a typed closed program reaches, under
a runner that keeps its protocol, has a closed term and goes on.  This is the property `Live`'s
docstring states of a calculus ("A's values include variables, and a calculus steps on closed
values only"), and RESTRUCTURE §4.1's reading of the junk encodings ("no configuration a typed
closed program reaches has one").  It is a fact about the configurations of runs, which neither
FL nor adequacy states at every answer type.  At today's kernel it holds at every effect context
(`liveOK_tier1Open`); its discharge at `J₁` is piece 4's. -/
def LiveOK (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : Prop :=
  ∀ c, (ourInst (ℍ := ℍ) RF Ξ J).Live c → closedAt 0 c.2 = true ∧ GoesOn (ℍ := ℍ) RF Ξ c

theorem live_of_ostep {c c' : Heap × Expr} {ev : A.Ev (RF.alg Ξ).Lab OVal Expr}
    (hc : (ourInst (ℍ := ℍ) RF Ξ J).Live c) (h : OStep (ℍ := ℍ) RF Ξ c ev c') :
    (ourInst (ℍ := ℍ) RF Ξ J).Live c' := by
  obtain ⟨P, C, R, s, hR, hP, hreach⟩ := hc
  exact ⟨P, C, R, s, hR, hP, Relation.ReflTransGen.tail hreach ⟨ev, .mach h⟩⟩

theorem live_of_pureSteps {c c' : Heap × Expr} (hc : (ourInst (ℍ := ℍ) RF Ξ J).Live c)
    (h : (ourInst (ℍ := ℍ) RF Ξ J).PureSteps c c') : (ourInst (ℍ := ℍ) RF Ξ J).Live c' := by
  induction h with
  | refl => exact hc
  | tail _ hst ih =>
      obtain ⟨ev, hst, -⟩ := hst
      exact live_of_ostep ih hst

theorem closedAt_plug_inv : ∀ (K : Kont) {k : ℕ} {x : Expr}, closedAt k (K.plug x) = true →
    closedAt k x = true
  | .hole, _, _, h => h
  | .pairL K _, _, _, h | .letpair K _, _, _, h | .seq K _, _, _, h | .appL K _, _, _, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      exact closedAt_plug_inv K h.1
  | .case K _ _, _, _, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      exact closedAt_plug_inv K h.1.1
  | .pairR _ K, _, _, h | .appR _ K, _, _, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      exact closedAt_plug_inv K h.2
  | .inj₁ K, _, _, h | .inj₂ K, _, _, h => by
      simp only [Kont.plug, closedAt] at h
      exact closedAt_plug_inv K h

/-- A closed A-value is a Core value. -/
theorem isVal_of_closed_oval : ∀ {x : Expr}, IsOVal x → closedAt 0 x = true → IsVal x
  | _, .var _, h => by simp [closedAt] at h
  | _, .unit, _ => .unit
  | _, .pair ha hb, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      exact .pair (isVal_of_closed_oval ha h.1) (isVal_of_closed_oval hb h.2)
  | _, .inj₁ ha, h => .inj₁ (isVal_of_closed_oval ha h)
  | _, .inj₂ ha, h => .inj₂ (isVal_of_closed_oval ha h)
  | _, .lam, _ => .lam
  | _, .loc, _ => .loc
  | _, .prim, _ => .prim
  | _, .storeV ha, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      exact .storeV (isVal_of_closed_oval ha h.2)

/-- At a configuration a typed program reaches, an A-value its term holds at an evaluation
position is a Core value. -/
theorem val_of_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c : Heap × Expr}
    (hc : (ourInst (ℍ := ℍ) RF Ξ J).Live c) {K : Kont} {x : Expr} (hx : IsOVal x)
    (h : c.2 = K.plug x) : IsVal x :=
  isVal_of_closed_oval hx (closedAt_plug_inv K (h ▸ (hL c hc).1))

/-! ### S0: the shape of the machine -/

/-- **`Congr`**: a step of a term is its step in every context. -/
theorem congr_ourInst : (ourInst (ℍ := ℍ) RF Ξ J).Congr := by
  rintro ⟨μ, e⟩ t ev c' (K : Kont) hev h
  change OStep (ℍ := ℍ) RF Ξ (μ, t) ev c' at h
  change OStep (ℍ := ℍ) RF Ξ (μ, K.plug t) ev (c'.1, K.plug c'.2)
  cases h with
  | mach hh =>
      rw [← Kont.plug_comp, ← Kont.plug_comp]
      exact OStep.mach hh
  | again => exact absurd rfl hev
  | fin => exact absurd rfl hev

/-- The driver's configurations hold no non-value but themselves at an evaluation position. -/
theorem plug_eq_drive {K : Kont} {x : Expr} {w : Val} (h : K.plug x = driveE (.val w))
    (hx : ¬ IsVal x) : K = .hole := by
  cases K with
  | hole => rfl
  | appR f K =>
      simp only [Kont.plug, driveE, Expr.app.injEq] at h
      exact absurd (K.isVal_of_plug (by rw [h.2]; exact w.2)) hx
  | appL K v =>
      simp only [Kont.plug, driveE, driveMark, Expr.app.injEq] at h
      have h1 := h.1
      cases K <;> simp [Kont.plug] at h1
      subst h1; exact absurd .prim hx
  | _ => simp [Kont.plug, driveE] at h

theorem not_isVal_opE' (r : Bool) (x : Expr) :
    ¬ IsVal (if r then raiseE x else performE x) := by
  cases r <;> simp [raiseE, performE]

/-- A plugged operation at an A-value takes no machine step. -/
theorem no_ostep_op {c : Heap × Expr} {K : Kont} (r : Bool) (n i : UInt32) (v : OVal)
    (hterm : c.2 = K.plug (if r then raiseE (opArgE n i v.1) else performE (opArgE n i v.1)))
    (hK : OpFree r n K) {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} {c' : Heap × Expr} :
    ¬ OStep (ℍ := ℍ) RF Ξ c ev c' := by
  intro h
  have hstep : ∃ μ' t', Step1 (ℍ := ℍ) c.1 c.2 μ' t' := by
    obtain ⟨μ, e⟩ := c
    generalize hc : (μ, e) = c₀ at h
    cases h with
    | mach hh =>
        simp only [Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨_, _, _, _, _, rfl, rfl, hh⟩
    | again =>
        simp only [Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hK0 := plug_eq_drive hterm.symm (not_isVal_opE' r _)
        subst hK0
        cases r <;> simp [Kont.plug, raiseE, performE, driveE, driveMark] at hterm
    | fin =>
        simp only [Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hK0 := plug_eq_drive hterm.symm (not_isVal_opE' r _)
        subst hK0
        cases r <;> simp [Kont.plug, raiseE, performE, driveE, driveMark] at hterm
  obtain ⟨μ', t', hs⟩ := hstep
  rcases opArg_val_or_var K r n i v with ⟨w, hw⟩ | ⟨K', j, hK'⟩
  · have : c.2 = K.plug (opE r (opPayload n i w)) := by
      rw [hterm]; cases r <;> simp [opE, opArgE, opPayload, hw, performE, raiseE, Val.pair, Val.i32]
    rw [this] at hs
    exact opPlug_no_step (payloadName_opPayload _ _ _) hK hs
  · rw [hterm, hK'] at hs
    exact step1_plug_var K' j hs

/-- The junk of an index beyond `UInt32` takes no step of our machine. -/
theorem no_ostep_junk {c : Heap × Expr} {K : Kont} (r : Bool) (hterm : c.2 = K.plug (opJunk r))
    {ev : A.Ev (RF.alg Ξ).Lab OVal Expr} {c' : Heap × Expr} :
    ¬ OStep (ℍ := ℍ) RF Ξ c ev c' := by
  intro h
  rw [opJunk_plug] at hterm
  obtain ⟨μ, e⟩ := c
  simp only at hterm
  subst hterm
  generalize hc : (μ, (K.comp (.appR (.prim (if r then .raise else .perform)) .hole)).plug
    (Expr.var 0)) = c₀ at h
  cases h with
  | mach hh =>
      obtain ⟨rfl, he⟩ := Prod.mk.inj hc
      exact step1_plug_var _ 0 ⟨_, _, _, he, rfl, hh⟩
  | again =>
      obtain ⟨-, he⟩ := Prod.mk.inj hc
      have := plug_eq_drive he (by simp)
      rw [this] at he
      simp [Kont.plug, driveE, driveMark] at he
  | fin =>
      obtain ⟨-, he⟩ := Prod.mk.inj hc
      have := plug_eq_drive he (by simp)
      rw [this] at he
      simp [Kont.plug, driveE, driveMark] at he

/-- A context with no finaliser frame and no handler of the name `n ≠ 0` stops no raise of it. -/
theorem catches_of_noUnwind (n : UInt32) (hn : n ≠ 0) :
    ∀ (K : Kont), K.NoUnwind → K.HasHnd n = false → K.Catches n = false
  | .hole, _, _ => rfl
  | .appR f K, ⟨hu, hc, hK⟩, hH => by
      simp only [Kont.HasHnd, Bool.or_eq_false_iff] at hH
      simp only [Kont.Catches, Bool.or_eq_false_iff]
      refine ⟨?_, catches_of_noUnwind n hn K hK hH.2⟩
      have hH1 := hH.1
      split <;> simp_all
  | .pairL K _, h, hH | .pairR _ K, h, hH | .letpair K _, h, hH | .case K _ _, h, hH
  | .appL K _, h, hH | .seq K _, h, hH | .inj₁ K, h, hH | .inj₂ K, h, hH =>
      catches_of_noUnwind n hn K h hH

/-- **`OpStuck`**: an operation no handler catches takes no step; nor does a raise no frame
stops.  At a row form whose labels' names are not the reserved `0`. -/
theorem opStuck_ourInst (hnz : ∀ l, RF.name Ξ l ≠ 0) : (ourInst (ℍ := ℍ) RF Ξ J).OpStuck := by
  refine ⟨fun c K l i v hterm hK ev c' h => ?_, fun c K l i v hterm hK hU ev c' h => ?_⟩
  · rcases perform_cases (ℍ := ℍ) (J := J) l i v with ⟨-, hp⟩ | ⟨-, hp⟩
    · have hterm' : c.2 = K.plug (performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)) := by
        rw [← hp]; exact hterm
      exact no_ostep_op (r := false) (K := K) (RF.name Ξ l) (UInt32.ofNat i) v hterm' hK h
    · have hterm' : c.2 = K.plug (opJunk false) := by rw [← hp]; exact hterm
      exact no_ostep_junk (K := K) false hterm' h
  · rcases raise_cases (ℍ := ℍ) (J := J) l i v with ⟨-, hp⟩ | ⟨-, hp⟩
    · have hterm' : c.2 = K.plug (raiseE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)) := by
        rw [← hp]; exact hterm
      exact no_ostep_op (r := true) (K := K) (RF.name Ξ l) (UInt32.ofNat i) v hterm'
        (catches_of_noUnwind _ (hnz l) K hU hK) h
    · have hterm' : c.2 = K.plug (opJunk true) := by rw [← hp]; exact hterm
      exact no_ostep_junk (K := K) true hterm' h

/-- A configuration holding a stuck redex at an evaluation position does not go on. -/
theorem not_goesOn_stuck {s : Expr} (hs : StuckAt (ℍ := ℍ) s) (K : Kont) (μ : Heap)
    (hd : ∀ w : Val, K.plug s ≠ driveE (.val w)) : ¬ GoesOn (ℍ := ℍ) RF Ξ (μ, K.plug s) := by
  rintro (⟨v, hv⟩ | ⟨ev, c', h⟩ | ⟨r, K', p, n, he, -, -⟩)
  · exact hs.not_val (K.isVal_of_plug (by rw [show K.plug s = v.1 from hv]; exact v.2))
  · generalize hc : (μ, K.plug s) = c₀ at h
    cases h with
    | mach hh =>
        obtain ⟨h1, he⟩ := Prod.mk.inj hc
        subst h1
        exact stuck_no_step hs K ⟨_, _, _, he, rfl, hh⟩
    | again => exact hd _ (Prod.mk.inj hc).2
    | fin => exact hd _ (Prod.mk.inj hc).2
  · exact stuck_ne_op hs K K' r p he

theorem plug_unit_app_ne_drive (K : Kont) (x w : Val) :
    K.plug (.app .unit x.1) ≠ driveE (.val w) := by
  intro h
  have := plug_eq_drive h (by simp)
  subst this
  simp [Kont.plug, driveE, driveMark] at h

theorem labelOf_ne_top (a : Expr) : labelOf RF Ξ a ≠ .top := by
  unfold labelOf
  split_ifs <;> simp

/-- **`AppLaw`**: `M V` reaches `□ V` around `M` by one β-step, at a configuration a typed
program reaches. -/
theorem appLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (ourInst (ℍ := ℍ) RF Ξ J).AppLaw := by
  rintro ⟨μ, e⟩ (M : Expr) (V : OVal) hlive
  have hV : IsVal V.1 :=
    val_of_live hL hlive V.2 (K := .appR (.lam (.app (M.shift 1 0) (.var 0))) .hole) rfl
  show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps (μ, appE M V.1) (μ, (appK V.1).plug M)
  have hK : appK V.1 = .appL .hole ⟨V.1, hV⟩ := by unfold appK; rw [dif_pos hV]
  have hs : (Expr.app (M.shift 1 0) (.var 0)).subst 0 ⟨V.1, hV⟩ = .app M V.1 := by
    show Expr.app ((M.shift 1 0).subst 0 ⟨V.1, hV⟩) ((Expr.var 0).subst 0 ⟨V.1, hV⟩) = _
    rw [Expr.subst_shift 0 0 0 _ M (le_refl _) (le_refl _), Expr.shift_zero]
    simp [Expr.subst]
  rw [hK]
  have h := OStep.mach (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (K := .hole)
    (Head.beta μ (.app (M.shift 1 0) (.var 0)) ⟨V.1, hV⟩)
  rw [hs] at h
  exact Relation.ReflTransGen.single ⟨_, h, rfl⟩

/-- **`DriveLaws`**: the driver's two transitions, each the only step of its configuration, and
the only `top` steps. -/
theorem driveLaws_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (ourInst (ℍ := ℍ) RF Ξ J).DriveLaws := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨μ, e⟩ l ev c' hlive hterm
    change e = driveE (.inj₂ l.1) at hterm
    subst hterm
    have hl : IsVal l.1 := val_of_live hL hlive l.2 (K := .appR driveMark (.inj₂ .hole)) rfl
    change OStep (ℍ := ℍ) RF Ξ (μ, driveE (.val (Val.inj₂ ⟨l.1, hl⟩))) ev c' ↔ _
    constructor
    · intro h
      generalize hc : (μ, driveE (.val (Val.inj₂ ⟨l.1, hl⟩))) = c₀ at h
      cases h with
      | mach hh =>
          obtain ⟨h1, he⟩ := Prod.mk.inj hc
          subst h1
          exact (no_step1_drive _ ⟨_, _, _, he, rfl, hh⟩).elim
      | @again μ' l' =>
          obtain ⟨h1, he⟩ := Prod.mk.inj hc
          subst h1
          have hl' : l'.1 = l.1 := by
            simp only [driveE, Expr.app.injEq, true_and, Expr.val, Val.inj₂, Expr.inj₂.injEq] at he
            exact he.symm
          refine ⟨rfl, ?_⟩
          show (μ, driveE (nextE l')) = (μ, driveE (.app l.1 (.inj₁ .unit)))
          simp only [nextE, Expr.val, hl']
          rfl
      | fin =>
          obtain ⟨-, he⟩ := Prod.mk.inj hc
          simp [driveE, Val.inj₁, Val.inj₂] at he
    · rintro ⟨rfl, rfl⟩
      exact OStep.again (l := ⟨l.1, hl⟩)
  · rintro ⟨μ, e⟩ a ev c' hlive hterm
    change e = driveE (.inj₁ a.1) at hterm
    subst hterm
    have ha : IsVal a.1 := val_of_live hL hlive a.2 (K := .appR driveMark (.inj₁ .hole)) rfl
    change OStep (ℍ := ℍ) RF Ξ (μ, driveE (.val (Val.inj₁ ⟨a.1, ha⟩))) ev c' ↔ _
    constructor
    · intro h
      generalize hc : (μ, driveE (.val (Val.inj₁ ⟨a.1, ha⟩))) = c₀ at h
      cases h with
      | mach hh =>
          obtain ⟨h1, he⟩ := Prod.mk.inj hc
          subst h1
          exact (no_step1_drive _ ⟨_, _, _, he, rfl, hh⟩).elim
      | again =>
          obtain ⟨-, he⟩ := Prod.mk.inj hc
          simp [driveE, Val.inj₁, Val.inj₂] at he
      | @fin μ' a' =>
          obtain ⟨h1, he⟩ := Prod.mk.inj hc
          subst h1
          have ha' : a'.1 = a.1 := by
            simp only [driveE, Expr.app.injEq, true_and, Expr.val, Val.inj₁, Expr.inj₁.injEq] at he
            exact he.symm
          exact ⟨rfl, by show (μ, a'.1) = (μ, a.1); rw [ha']⟩
    · rintro ⟨rfl, rfl⟩
      exact OStep.fin (a := ⟨a.1, ha⟩)
  · rintro c c' h
    change OStep (ℍ := ℍ) RF Ξ c .top c' at h
    generalize hev : (A.Ev.top : A.Ev (RF.alg Ξ).Lab OVal Expr) = ev at h
    cases h with
    | mach _ => exact absurd hev.symm (labelOf_ne_top _)
    | @again μ l => exact ⟨OVal.ofVal (Val.inj₂ l), rfl⟩
    | @fin μ a => exact ⟨OVal.ofVal (Val.inj₁ a), rfl⟩


/-! ### S4: the handler laws -/
/-- A head step in a context keeps the store. -/
theorem pureSteps_head {μ : Heap} (K₀ K : Kont) {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ a') :
    (ourInst (ℍ := ℍ) RF Ξ J).PureSteps (μ, K₀.plug (K.plug a)) (μ, K₀.plug (K.plug a')) := by
  rw [← Kont.plug_comp, ← Kont.plug_comp]
  exact Relation.ReflTransGen.single ⟨_, OStep.mach h, rfl⟩

theorem isVal_clausesE : ∀ cs : List Expr, (∀ c ∈ cs, IsVal c) → IsVal (clausesE cs)
  | [], _ => .unit
  | c :: cs, h => .pair (h c (by simp)) (isVal_clausesE cs (fun c' hc' => h c' (by simp [hc'])))

theorem clauseAt_clausesE : ∀ (cs : List Expr) (i : ℕ) {c : Expr} (hc : IsVal c), cs[i]? = some c →
    clauseAt (clausesE cs) i = some ⟨c, hc⟩
  | [], _, _, _, h => by simp at h
  | c' :: cs, 0, c, hc, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [clausesE, clauseAt, hc]
  | c' :: cs, i + 1, c, hc, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [clausesE, clauseAt]
      exact clauseAt_clausesE cs i hc h

theorem closedAt_clausesE : ∀ (cs : List Expr) {k : ℕ}, closedAt k (clausesE cs) = true →
    ∀ c ∈ cs, closedAt k c = true
  | [], _, _, c, hc => by simp at hc
  | c' :: cs, k, h, c, hc => by
      simp only [clausesE, closedAt, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h.1
      · exact closedAt_clausesE cs h.2 c hc

/-- At a configuration a typed program reaches, a handler frame's handler is a Core value. -/
theorem hndVal_of_live (hL : LiveOK (ℍ := ℍ) RF Ξ J) {c : Heap × Expr}
    (hc : (ourInst (ℍ := ℍ) RF Ξ J).Live c) {K₀ : Kont} {n : UInt32} {qs : List Qual} {r : OVal}
    {cs : List OVal} {x : Expr}
    (h : c.2 = K₀.plug ((handleK n (qualsVal qs).1 r.1 (cs.map Subtype.val)).plug x)) :
    IsVal r.1 ∧ IsVal (clausesE (cs.map Subtype.val)) := by
  have hcl := closedAt_plug_inv K₀ (h ▸ (hL c hc).1)
  simp only [handleK, Kont.plug, hndValE, closedAt, Bool.and_eq_true, Bool.true_and] at hcl
  refine ⟨isVal_of_closed_oval r.2 hcl.1.2.1, isVal_clausesE _ ?_⟩
  intro e he
  obtain ⟨cl, -, rfl⟩ := List.mem_map.1 he
  exact isVal_of_closed_oval cl.2 (closedAt_clausesE _ hcl.1.2.2 _ he)


/-- Resuming `κ` at `w` reaches `hnd H K[w]`: `ewp_kappa_resume`'s four steps. -/
theorem kappa_resume_steps {μ : Heap} (K₀ : Kont) (n : UInt32) (H : Val) (K : Kont) (w : Val) :
    (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
      (μ, K₀.plug (.app (.app (kappa n H K) (.val (Val.inj₁ .unit))) (.val w)))
      (μ, K₀.plug (hndE H (K.plug (.val w)))) := by
  refine .trans (pureSteps_head K₀ (.appL .hole w) (Head.beta μ _ _)) ?_
  refine .trans (pureSteps_head K₀ (.appL .hole w) (Head.case₁ μ Val.unit _ _)) ?_
  refine .trans (pureSteps_head K₀ (.appL .hole w) (Head.seq μ _)) ?_
  refine .trans (pureSteps_head K₀ .hole (Head.beta μ _ w)) ?_
  have e : ∀ (s u : Val), Expr.subst 0 w (Expr.subst 1 u (Expr.subst 2 s
      (hndE (Val.shift 3 0 H) ((Kont.shift 3 0 K).plug (Expr.var 0))))) =
      hndE H (K.plug (.val w)) := by
    intro s u
    simp only [hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 2 0 2 s H.1 (by omega) (by omega),
      Expr.subst_shift 1 0 1 u H.1 (by omega) (by omega),
      Expr.subst_shift 0 0 0 w H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 2 K 0 2 s _ (by omega) (by omega),
      plug_shift_subst 1 K 0 1 u _ (by omega) (by omega),
      plug_shift_subst 0 K 0 0 w _ (by omega) (by omega), Kont.shift_zero]
    simp [Expr.subst]
  simp only [Kont.plug]
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, e]
  rfl

/-- Cancelling `κ` reaches `ccatch (hnd H K[raise (0, (0, (N, none)))])`: `ewp_kappa_cancel`'s
three steps. -/
theorem kappa_cancel_steps {μ : Heap} (K₀ : Kont) (n : UInt32) (H : Val) (K : Kont) :
    (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
      (μ, K₀.plug (.app (kappa n H K) (.val (Val.inj₂ .unit))))
      (μ, K₀.plug (Targets.cancelOf n H K)) := by
  refine .trans (pureSteps_head K₀ .hole (Head.beta μ _ _)) ?_
  refine .trans (pureSteps_head K₀ .hole (Head.case₂ μ Val.unit _ _)) ?_
  refine .trans (pureSteps_head K₀ .hole (Head.seq μ _)) ?_
  have e : ∀ (s u : Val), Expr.subst 0 u (Expr.subst 1 s
      (ccatchE (hndE (Val.shift 2 0 H) ((Kont.shift 2 0 K).plug
        (raiseE (.val (cancelVal (n :: K.hndNames) none))))))) =
      ccatchE (hndE H (K.plug (raiseE (.val (cancelVal (n :: K.hndNames) none))))) := by
    intro s u
    simp only [ccatchE, hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 1 0 1 s H.1 (by omega) (by omega),
      Expr.subst_shift 0 0 0 u H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 1 K 0 1 s _ (by omega) (by omega),
      plug_shift_subst 0 K 0 0 u _ (by omega) (by omega), Kont.shift_zero]
    simp only [raiseE, Expr.subst, Expr.val, subst_cancelVal_none, Val.prim]
  simp only [Kont.plug]
  rw [show (0 + 1 : Nat) = 1 from rfl, e]
  rfl


theorem isVal_of_mem_clausesE : ∀ {cs : List Expr}, IsVal (clausesE cs) → ∀ c ∈ cs, IsVal c
  | [], _, c, hc => by simp at hc
  | c' :: cs, h, c, hc => by
      cases h with
      | pair h₁ h₂ =>
          rcases List.mem_cons.1 hc with rfl | hc
          · exact h₁
          · exact isVal_of_mem_clausesE h₂ c hc

/-- `M V`'s β-step: `(λx. M↑ x) V ↦ M V`. -/
theorem appE_subst (M : Expr) (V : Val) :
    (Expr.app (M.shift 1 0) (.var 0)).subst 0 V = .app M V.1 := by
  show Expr.app ((M.shift 1 0).subst 0 V) ((Expr.var 0).subst 0 V) = _
  rw [Expr.subst_shift 0 0 0 _ M (le_refl _) (le_refl _), Expr.shift_zero]
  simp [Expr.subst]

theorem appE_steps {μ : Heap} (K₀ : Kont) (M : Expr) (V : Val) :
    (ourInst (ℍ := ℍ) RF Ξ J).PureSteps (μ, K₀.plug (appE M V.1)) (μ, K₀.plug (.app M V.1)) := by
  have h := pureSteps_head (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (μ := μ) K₀ .hole
    (Head.beta μ (.app (M.shift 1 0) (.var 0)) V)
  rw [appE_subst] at h
  exact h

theorem resumeE_subst (k : Expr) (w : Val) :
    (Expr.app (.app (k.shift 1 0) (.inj₁ .unit)) (.var 0)).subst 0 w =
      .app (.app k (.inj₁ .unit)) w.1 := by
  show Expr.app (.app ((k.shift 1 0).subst 0 w) ((Expr.inj₁ .unit).subst 0 w))
    ((Expr.var 0).subst 0 w) = _
  rw [Expr.subst_shift 0 0 0 _ k (le_refl _) (le_refl _), Expr.shift_zero]
  simp [Expr.subst]

/-- `resume k w`'s first step binds `w`. -/
theorem resumeE_steps {μ : Heap} (K₀ : Kont) (k : Expr) (w : Val) :
    (ourInst (ℍ := ℍ) RF Ξ J).PureSteps (μ, K₀.plug (resumeE k w.1))
      (μ, K₀.plug (.app (.app k (.inj₁ .unit)) w.1)) := by
  have h := pureSteps_head (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (μ := μ) K₀ .hole
    (Head.beta μ (.app (.app (k.shift 1 0) (.inj₁ .unit)) (.var 0)) w)
  rw [resumeE_subst] at h
  exact h

theorem captureE_of_val {n : UInt32} {qs r : Expr} {cs : List Expr} (K : Kont)
    (h : IsVal (hndValE n qs r cs)) : captureE n qs r cs K = kappa n ⟨_, h⟩ K := by
  unfold captureE; rw [dif_pos h]

theorem captureE_of_not_val {n : UInt32} {qs r : Expr} {cs : List Expr} (K : Kont)
    (h : ¬ IsVal (hndValE n qs r cs)) : captureE n qs r cs K = .unit := by
  unfold captureE; rw [dif_neg h]

theorem cancelOfE_of_val {n : UInt32} {qs r : Expr} {cs : List Expr} (K : Kont)
    (h : IsVal (hndValE n qs r cs)) : cancelOfE n qs r cs K = Targets.cancelOf n ⟨_, h⟩ K := by
  unfold cancelOfE; rw [dif_pos h]

/-- **Every resuming operation of `Ξ` is unrestricted**: its `κ` owns no cell (SPEC §25).  At a
linear or affine operation the catch is followed by the cell's allocation, which changes the
store, so S4 with no cell, whose catch law keeps it, is read at contexts with this property. -/
def _root_.Targets.EffCtx.CatchUnr (Ξ : EffCtx) : Prop :=
  ∀ n q A B, (q, A, B) ∈ Ξ n → (B.isZero && q != .lin) = false → q = .unr

/-- At a context whose resuming operations are unrestricted, a resuming operation's tag is the
unrestricted one. -/
theorem capTag_qsOf_unr {Ξ : EffCtx} (hU : Ξ.CatchUnr) {n : UInt32} {i : ℕ}
    {p : Qual × VTy × VTy} (hp : (Ξ n)[i]? = some p) (hres : (p.2.2.isZero && p.1 != .lin) = false) :
    capTag (qsOf Ξ n) i = 2 := by
  have hi : i < (Ξ n).length := (List.getElem?_eq_some_iff.1 hp).1
  have hpe : (Ξ n)[i] = p := (List.getElem?_eq_some_iff.1 hp).2
  have hq := hU n p.1 p.2.1 p.2.2 (by rw [← hpe]; exact List.getElem_mem hi) hres
  unfold qsOf
  rw [capTag_qualsVal _ i (by simpa using hi)]
  simp [hpe, hq, Qual.tag]

/-- An operation's index is below `2³²` when its label's signature is no longer. -/
theorem idx_lt {l : (RF.alg Ξ).Lab} {i : ℕ} {o : A.OpSig OVTy}
    (hlen : (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32)
    (h : ((ourInst (ℍ := ℍ) RF Ξ J).sig l)[i]? = some o) : i < 2 ^ 32 := by
  have h1 := (List.getElem?_eq_some_iff.1 h).1
  have h2 : ((ourInst (ℍ := ℍ) RF Ξ J).sig l).length = (Ξ (RF.name Ξ l)).length := by
    first | exact List.length_map _ _ | exact List.length_map _
  omega

/-- The signature entry behind an operation of A's signature at our instance. -/
theorem sig_entry {l : (RF.alg Ξ).Lab} {i : ℕ} {o : A.OpSig OVTy}
    (h : ((ourInst (ℍ := ℍ) RF Ξ J).sig l)[i]? = some o) :
    ∃ p, (Ξ (RF.name Ξ l))[i]? = some p ∧ o.cls = clsOf p.1 p.2.2 := by
  change ((Ξ (RF.name Ξ l)).map fun p => (⟨OVTy.ofV p.2.1, OVTy.ofV p.2.2, clsOf p.1 p.2.2⟩ :
    A.OpSig OVTy))[i]? = some o at h
  rw [List.getElem?_map] at h
  cases hp : (Ξ (RF.name Ξ l))[i]? with
  | none => rw [hp] at h; cases h
  | some p => rw [hp] at h; cases h; exact ⟨p, rfl, rfl⟩

/-- A resuming operation is not abortive. -/
theorem resuming_of_cls {q : Qual} {B : VTy} (h : clsOf q B ≠ .abortive) :
    (B.isZero && q != .lin) = false := by
  unfold clsOf at h
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  simp [hc] at h

/-- **S4's return law** at a configuration a typed program reaches. -/
theorem retLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (ourInst (ℍ := ℍ) RF Ξ J).RetLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) l (r : OVal) (cs : List OVal) (v : OVal) hlive he
  change e = K₀.plug ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1
    (cs.map Subtype.val)).plug v.1) at he
  subst he
  obtain ⟨hr, hcs⟩ := hndVal_of_live hL hlive rfl
  have hv : IsVal v.1 := val_of_live hL hlive v.2
    (K := K₀.comp (handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)))
    (by rw [Kont.plug_comp])
  exact ⟨_, pureSteps_head K₀ .hole (Head.hret μ (RF.name Ξ l)
    (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) ⟨r.1, hr⟩ ⟨_, hcs⟩ ⟨v.1, hv⟩),
    appE_steps K₀ r.1 ⟨v.1, hv⟩⟩

/-- **A catch whose operation's tag is the unrestricted one** hands `kappa` and keeps the store: the
`[op]` step reaches the clause applied to the argument and `capture l H K`, as `M V`'s β-step does. -/
theorem catch_unr_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J)
    (hlen : ∀ l, (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) {c : Heap × Expr} {K₀ : Kont}
    {l : (RF.alg Ξ).Lab} {r : OVal} {cs : List OVal} {K : Kont} {i : ℕ} {v : OVal}
    {o : A.OpSig OVTy} {cl : OVal} (hlive : (ourInst (ℍ := ℍ) RF Ξ J).Live c)
    (he : (ourInst (ℍ := ℍ) RF Ξ J).term c = (ourInst (ℍ := ℍ) RF Ξ J).plug K₀
      ((ourInst (ℍ := ℍ) RF Ξ J).handle l ((ourInst (ℍ := ℍ) RF Ξ J).hnd r cs)
        ((ourInst (ℍ := ℍ) RF Ξ J).plug K ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v))))
    (hK : (ourInst (ℍ := ℍ) RF Ξ J).catches K l = false)
    (hsig : ((ourInst (ℍ := ℍ) RF Ξ J).sig l)[i]? = some o) (hcl : cs[i]? = some cl)
    (htag : capTag (qsOf Ξ (RF.name Ξ l)) i = 2) :
    (ourInst (ℍ := ℍ) RF Ξ J).PureJoin c ((ourInst (ℍ := ℍ) RF Ξ J).setT c
      ((ourInst (ℍ := ℍ) RF Ξ J).plug K₀ ((ourInst (ℍ := ℍ) RF Ξ J).app
        ((ourInst (ℍ := ℍ) RF Ξ J).force cl) ((ourInst (ℍ := ℍ) RF Ξ J).pair v
          ((ourInst (ℍ := ℍ) RF Ξ J).capture l ((ourInst (ℍ := ℍ) RF Ξ J).hnd r cs) K))))) := by
  obtain ⟨μ, e⟩ := c
  rw [perform_eq (ℍ := ℍ) (l := l) v (idx_lt (J := J) (hlen l) hsig)] at he
  change e = K₀.plug ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
    (K.plug (performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)))) at he
  subst he
  change K.HasHnd (RF.name Ξ l) = false at hK
  obtain ⟨hr, hcs⟩ := hndVal_of_live hL hlive rfl
  have hv : IsVal v.1 := val_of_live hL hlive v.2
    (K := ((K₀.comp (handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1
      (cs.map Subtype.val))).comp K).comp
      (.appR (.prim .perform) (.pairR (Val.i32 (RF.name Ξ l)) (.pairR (Val.i32 (UInt32.ofNat i))
        .hole))))
    (by simp only [Kont.plug_comp]; rfl)
  have hcl' : (cs.map Subtype.val)[i]? = some cl.1 := by
    rw [List.getElem?_map]; exact congrArg (Option.map Subtype.val) hcl
  have hclv : IsVal cl.1 := isVal_of_mem_clausesE hcs _ (List.mem_of_getElem? hcl')
  have hi := idx_lt (J := J) (hlen l) hsig
  have hca : clauseAt (clausesE (cs.map Subtype.val)) (UInt32.ofNat i).toNat =
      some ⟨cl.1, hclv⟩ := by
    rw [UInt32.toNat_ofNat_of_lt' hi]
    exact clauseAt_clausesE _ i hclv hcl'
  have hqv : IsVal (qsOf Ξ (RF.name Ξ l)) := (qualsVal _).2
  have hH : IsVal (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)) :=
    .pair .prim (.pair hqv (.pair hr hcs))
  have htag' : capTag (qsOf Ξ (RF.name Ξ l)) (UInt32.ofNat i).toNat = 2 := by
    rw [UInt32.toNat_ofNat_of_lt' hi]; exact htag
  refine ⟨_, pureSteps_head K₀ .hole (Head.hop μ (RF.name Ξ l) (UInt32.ofNat i)
    (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) ⟨r.1, hr⟩ ⟨_, hcs⟩ ⟨cl.1, hclv⟩ ⟨v.1, hv⟩ K hca hK),
    ?_⟩
  show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps (μ, K₀.plug (appE cl.1
    (.pair v.1 (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val) K)))) _
  rw [captureE_of_val K hH]
  have hk : kappaAt (capTag (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)).1 (UInt32.ofNat i).toNat)
      (RF.name Ξ l) (hndVal (RF.name Ξ l) (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst))
        ⟨r.1, hr⟩ ⟨_, hcs⟩) K =
      kappa (RF.name Ξ l) ⟨_, hH⟩ K := by
    change kappaAt (capTag (qsOf Ξ (RF.name Ξ l)) (UInt32.ofNat i).toNat) _ _ K = _
    rw [htag']; rfl
  rw [hk]
  exact appE_steps K₀ cl.1 ⟨.pair v.1 (kappa _ _ K), .pair hv .lam⟩

/-- **S4's catch law with no cell**, at an effect context whose resuming operations are
unrestricted (`CatchUnr`): there every catch hands `kappa`, which owns no cell, and keeps the
store. -/
theorem catchKeep_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J)
    (hlen : ∀ l, (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) (hU : Ξ.CatchUnr) :
    (ourInst (ℍ := ℍ) RF Ξ J).CatchKeep := by
  intro c K₀ l r cs K i v o cl hlive he hK hsig hres hcl
  obtain ⟨p, hp, hpo⟩ := sig_entry (J := J) hsig
  exact catch_unr_ourInst hL hlen hlive he hK hsig hcl
    (capTag_qsOf_unr hU hp (resuming_of_cls (hpo ▸ hres)))

/-- **S4's abortive law**, at a row form whose labels' names are not the reserved `0`. -/
theorem abortLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hlen : ∀ l, (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) : (ourInst (ℍ := ℍ) RF Ξ J).AbortLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) l (r : OVal) (cs : List OVal) (K : Kont) i (v : OVal) o (cl : OVal)
    hlive he hK hU' hsig - hcl
  rw [raise_eq (ℍ := ℍ) (l := l) v (idx_lt (J := J) (hlen l) hsig)] at he
  change e = K₀.plug ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1 (cs.map Subtype.val)).plug
    (K.plug (raiseE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)))) at he
  subst he
  change K.HasHnd (RF.name Ξ l) = false at hK
  change K.NoUnwind at hU'
  obtain ⟨hr, hcs⟩ := hndVal_of_live hL hlive rfl
  have hv : IsVal v.1 := val_of_live hL hlive v.2
    (K := ((K₀.comp (handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) r.1
      (cs.map Subtype.val))).comp K).comp
      (.appR (.prim .raise) (.pairR (Val.i32 (RF.name Ξ l)) (.pairR (Val.i32 (UInt32.ofNat i))
        .hole))))
    (by simp only [Kont.plug_comp]; rfl)
  have hcl' : (cs.map Subtype.val)[i]? = some cl.1 := by
    rw [List.getElem?_map]; exact congrArg (Option.map Subtype.val) hcl
  have hclv : IsVal cl.1 := isVal_of_mem_clausesE hcs _ (List.mem_of_getElem? hcl')
  have hca : clauseAt (clausesE (cs.map Subtype.val)) (UInt32.ofNat i).toNat =
      some ⟨cl.1, hclv⟩ := by
    rw [UInt32.toNat_ofNat_of_lt' (idx_lt (hlen l) hsig)]
    exact clauseAt_clausesE _ i hclv hcl'
  exact ⟨_, pureSteps_head K₀ .hole (Head.hunwind μ (RF.name Ξ l) (UInt32.ofNat i)
    (qualsVal ((Ξ (RF.name Ξ l)).map Prod.fst)) ⟨r.1, hr⟩
    ⟨_, hcs⟩ ⟨cl.1, hclv⟩ ⟨v.1, hv⟩ K hca (catches_of_noUnwind _ (hnz l) K hU' hK)),
    appE_steps K₀ cl.1 ⟨v.1, hv⟩⟩

/-- **S4's deep-resume law**: resuming `kappa` reaches the reinstalled handler, keeping the
store. -/
theorem resumeLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (ourInst (ℍ := ℍ) RF Ξ J).ResumeLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) l (H : OVal × List OVal) (K : Kont) (w : OVal) hlive he
  change e = K₀.plug (resumeE (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
    (H.2.map Subtype.val) K) w.1) at he
  subst he
  have hw : IsVal w.1 := val_of_live hL hlive w.2
    (K := K₀.comp (.appR (.lam (.app (.app ((captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
      (H.2.map Subtype.val) K).shift 1 0) (.inj₁ .unit)) (.var 0))) .hole))
    (by rw [Kont.plug_comp]; rfl)
  have hst := resumeE_steps (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (μ := μ) K₀
    (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K) ⟨w.1, hw⟩
  by_cases hH : IsVal (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val))
  · refine ⟨_, ?_, Relation.ReflTransGen.refl⟩
    show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
      (μ, K₀.plug (resumeE (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
        (H.2.map Subtype.val) K) w.1))
      (μ, K₀.plug ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
        (H.2.map Subtype.val)).plug (K.plug w.1)))
    rw [captureE_of_val K hH] at hst ⊢
    exact hst.trans (kappa_resume_steps K₀ _ ⟨_, hH⟩ K ⟨w.1, hw⟩)
  · exfalso
    have hl' := live_of_pureSteps hlive hst
    rw [captureE_of_not_val K hH] at hl'
    refine not_goesOn_stuck (RF := RF) (Ξ := Ξ) (stuckAt_unit_app (Val.inj₁ Val.unit))
      (K₀.comp (.appL .hole ⟨w.1, hw⟩))
      μ (fun _ => plug_unit_app_ne_drive _ _ _) ?_
    rw [Kont.plug_comp]
    exact (hL _ hl').2

/-- **S4's cancel law**: cancelling `kappa` reaches its cancel run, keeping the store. -/
theorem cancelLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (ourInst (ℍ := ℍ) RF Ξ J).CancelLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) l (H : OVal × List OVal) (K : Kont) hlive he
  change e = K₀.plug (cancelE (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
    (H.2.map Subtype.val) K)) at he
  subst he
  by_cases hH : IsVal (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val))
  · refine ⟨_, ?_, Relation.ReflTransGen.refl⟩
    show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
      (μ, K₀.plug (cancelE (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
        (H.2.map Subtype.val) K)))
      (μ, K₀.plug (cancelOfE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K))
    rw [captureE_of_val K hH, cancelOfE_of_val K hH]
    exact kappa_cancel_steps K₀ _ _ K
  · exfalso
    have hg := (hL _ hlive).2
    change GoesOn RF Ξ (μ, K₀.plug (cancelE (captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1
      (H.2.map Subtype.val) K))) at hg
    rw [captureE_of_not_val K hH] at hg
    exact not_goesOn_stuck (stuckAt_unit_app (Val.inj₂ Val.unit)) K₀ μ
      (fun _ => plug_unit_app_ne_drive _ _ _) hg

/-- **S4's law of a finaliser frame whose body returned.** -/
theorem thenLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (ourInst (ℍ := ℍ) RF Ξ J).ThenLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) (v : OVal) (N : Expr) (D : Expr) hlive he
  change e = K₀.plug ((thenK N D).plug v.1) at he
  subst he
  have hv : IsVal v.1 := val_of_live hL hlive v.2 (K := K₀.comp (thenK N D))
    (by rw [Kont.plug_comp])
  exact ⟨_, pureSteps_head K₀ .hole (Head.uthen μ (Val.lam N) (Val.lam (D.shift 1 0)) ⟨v.1, hv⟩),
    Relation.ReflTransGen.refl⟩

/-- **S4's law of an unwind that reaches a finaliser frame**, at a row form whose labels' names are
not the reserved `0`. -/
theorem finLaw_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0) :
    (ourInst (ℍ := ℍ) RF Ξ J).FinLaw := by
  rintro ⟨μ, e⟩ (K₀ : Kont) (N : Expr) (D : Expr) (K : Kont) m j (w : OVal) hlive he hK hU
  rcases raise_cases (ℍ := ℍ) (J := J) m j w with ⟨-, hp⟩ | ⟨-, hp⟩
  swap
  · -- an index beyond `UInt32`: the junk, which no closed configuration holds
    rw [hp] at he
    have hcl := (hL _ hlive).1
    change e = K₀.plug ((thenK N D).plug (K.plug (opJunk true))) at he
    rw [he, ← Kont.plug_comp, ← Kont.plug_comp, not_closed_opJunk] at hcl
    cases hcl
  rw [hp] at he
  rw [hp]
  change e = K₀.plug ((thenK N D).plug
    (K.plug (raiseE (opArgE (RF.name Ξ m) (UInt32.ofNat j) w.1)))) at he
  subst he
  change K.HasHnd (RF.name Ξ m) = false at hK
  change K.NoUnwind at hU
  have hw : IsVal w.1 := val_of_live hL hlive w.2
    (K := ((K₀.comp (thenK N D)).comp K).comp
      (.appR (.prim .raise) (.pairR (Val.i32 (RF.name Ξ m)) (.pairR (Val.i32 (UInt32.ofNat j))
        .hole))))
    (by simp only [Kont.plug_comp]; rfl)
  have hnv : ¬ IsVal (K.plug (raiseE (.val (opPayload (RF.name Ξ m) (UInt32.ofNat j)
      ⟨w.1, hw⟩)))) := fun h => by
    have := K.isVal_of_plug h
    simp [raiseE] at this
  have hst := OStep.mach (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (K := K₀)
    (Head.ufin μ (Val.lam N) (Val.lam (D.shift 1 0)) (RF.name Ξ m) (UInt32.ofNat j) ⟨w.1, hw⟩ K
      (hnz m) (catches_of_noUnwind _ (hnz m) K hU hK))
  rw [labelOf_fire hnv, Val.val_lam, finE_shift] at hst
  refine ⟨_, .seq .hole (raiseE (opArgE (RF.name Ξ m) (UInt32.ofNat j) w.1)), hst,
    fun _ => rfl, trivial, ?_, ?_⟩
  · show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps _
      (μ, (K₀.comp (.seq .hole (raiseE (opArgE (RF.name Ξ m) (UInt32.ofNat j) w.1)))).plug D)
    rw [Kont.plug_comp]
    have h := pureSteps_head (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) K₀
      (.seq .hole (raiseE (opArgE (RF.name Ξ m) (UInt32.ofNat j) w.1)))
      (Head.beta μ (D.shift 1 0) Val.unit)
    rw [Expr.subst_shift 0 0 0 _ D (le_refl _) (le_refl _), Expr.shift_zero] at h
    exact h
  · show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
      (μ, (K₀.comp (.seq .hole (raiseE (opArgE (RF.name Ξ m) (UInt32.ofNat j) w.1)))).plug .unit)
      _
    rw [Kont.plug_comp]
    exact pureSteps_head K₀ .hole (Head.seq μ _)

/-- **S4 with no cell** (`HandlerSemNoCell`) at a configuration a typed program
reaches, at a row form whose labels' names are not the reserved `0` and whose signatures are
indexable by `UInt32`, at an effect context whose resuming operations are unrestricted
(`CatchUnr`): there the catch hands `kappa`, which owns no cell, and keeps the store.  At a linear
or affine operation the catch is followed by the allocation of `κ`'s cell (SPEC §25); S4 at every
effect context is `handlerSem_ourInst` (`Targets/Instance/HandlerCell.lean`). -/
theorem handlerSemNoCell_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) (hnz : ∀ l, RF.name Ξ l ≠ 0)
    (hlen : ∀ l, (Ξ (RF.name Ξ l)).length ≤ 2 ^ 32) (hU : Ξ.CatchUnr) :
    (ourInst (ℍ := ℍ) RF Ξ J).HandlerSemNoCell :=
  ⟨retLaw_ourInst hL, catchKeep_ourInst hL hlen hU, abortLaw_ourInst hL hnz hlen,
    resumeLaw_ourInst hL, cancelLaw_ourInst hL, thenLaw_ourInst hL, finLaw_ourInst hL hnz⟩

/-! ### S0: loops -/

/-- Core's store-keeping reduction is the instance's. -/
theorem pureSteps_of_core {μ : Heap} {e e' : Expr}
    (h : BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ) e e') :
    (ourInst (ℍ := ℍ) RF Ξ J).PureSteps (μ, e) (μ, e') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
      obtain ⟨K, a, a', h₁, h₂, hh, -⟩ := hs μ
      subst h₁ h₂
      exact ih.tail ⟨_, OStep.mach hh, rfl⟩

/-- The coalgebra at a state, at `next`'s selector: `⟨f s, g s⟩ (inj₁ ())` reaches `f s`. -/
theorem coalgE_steps₁ (f g : Expr) (s : Val) :
    BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ) (.app (.app (coalgE f g) s.1) (.inj₁ .unit))
      (appE f s.1) := by
  refine (PureSteps.beta_in (.appL .hole (Val.inj₁ Val.unit)) _ s).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ Val.unit _ _) rfl).trans ?_
  refine (PureSteps.head (fun μ => Head.seq μ _) rfl).trans ?_
  simp [appE, Expr.subst, Expr.shift_shift, Expr.shift_zero, subst_shift_succ, Val.val_shift]
  exact .refl

/-- The coalgebra at a state, at `close`'s selector: `⟨f s, g s⟩ (inj₂ ())` reaches `g s`. -/
theorem coalgE_steps₂ (f g : Expr) (s : Val) :
    BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ) (.app (.app (coalgE f g) s.1) (.inj₂ .unit))
      (appE g s.1) := by
  refine (PureSteps.beta_in (.appL .hole (Val.inj₂ Val.unit)) _ s).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ Val.unit _ _) rfl).trans ?_
  refine (PureSteps.head (fun μ => Head.seq μ _) rfl).trans ?_
  simp [appE, Expr.subst, Expr.shift_shift, Expr.shift_zero, subst_shift_succ, Val.val_shift]
  exact .refl

/-- The step of `unfold A B f g`: the coalgebra `λs. ⟨f s, g s⟩`, a value. -/
def stepV (f g : Expr) : Val := ⟨coalgE f g, .lam⟩

/-- A loop observation's frame: `□ to w. map_A (unfold f g) w`, at the observation's answer `A`. -/
def loopK (A : VTy) (C : CTy) (f g : Expr) : Kont :=
  bindK (.app (.app (.val (mapV A)) (.val ((hN C (stepV f g)).shift 1 0))) (.var 0))

theorem loopK_hasHnd (A : VTy) (C : CTy) (f g : Expr) (n : UInt32) :
    (loopK A C f g).HasHnd n = false := rfl

/-- `next (unfold A B f g s)` reaches `f s` under `next`'s frame. -/
theorem next_steps (A B : VTy) (f g : Expr) (s : Val) :
    BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ)
      (.app (etaN (CTy.loopEffBody [] A B) (stepV f g) s).1 (.inj₁ .unit))
      ((loopK (.sum (A.rename Nat.succ) (.tvar 0)) (CTy.loopEffBody [] A B) f g).plug
        (appE f s.1)) := by
  refine (etaN_obs _ _ s (Val.inj₁ Val.unit)).trans ?_
  refine (nodeV_amp₁_steps _ _ _ _).trans ?_
  refine (nodeV_ret_steps _ _ _).trans ?_
  refine (PureSteps.plug (loopK _ _ f g) (childV_steps _ _ rfl)).trans ?_
  refine (PureSteps.plug (loopK _ _ f g) (PureSteps.plug (.appL .hole (Val.inj₁ Val.unit))
    (rootV_steps _ _))).trans ?_
  exact PureSteps.plug (loopK _ _ f g) (coalgE_steps₁ f g s)

/-- `close (unfold A B f g s)` reaches `g s` under `close`'s frame. -/
theorem close_steps (A B : VTy) (f g : Expr) (s : Val) :
    BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ)
      (.app (etaN (CTy.loopEffBody [] A B) (stepV f g) s).1 (.inj₂ .unit))
      ((loopK (B.rename Nat.succ) (CTy.loopEffBody [] A B) f g).plug (appE g s.1)) := by
  refine (etaN_obs _ _ s (Val.inj₂ Val.unit)).trans ?_
  refine (nodeV_amp₂_steps _ _ _ _).trans ?_
  refine (nodeV_ret_steps _ _ _).trans ?_
  refine (PureSteps.plug (loopK _ _ f g) (childV_steps _ _ rfl)).trans ?_
  refine (PureSteps.plug (loopK _ _ f g) (PureSteps.plug (.appL .hole (Val.inj₂ Val.unit))
    (rootV_steps _ _))).trans ?_
  exact PureSteps.plug (loopK _ _ f g) (coalgE_steps₂ f g s)

/-- The frame binds the answer and maps it. -/
theorem loopK_steps (A : VTy) (C : CTy) (f g : Expr) (w : Val) :
    BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ) ((loopK A C f g).plug w.1)
      (.app (.app (.val (mapV A)) (.val (hN C (stepV f g)))) (.val w)) := by
  refine (PureSteps.beta _ w).trans ?_
  simp [Expr.subst, Val.val_shift, closed_subst (mapV_closed A), subst_shift_succ,
    Expr.shift_zero]
  exact .refl

theorem mapV_tensor_head (A B : VTy) (wr a : Val) : ∃ e,
    BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ)
      (.app (.app (.val (mapV (.tensor A B))) (.val wr)) (.val a)) (.letpair a.1 e) :=
  ⟨_, (PureSteps.beta_in (.appL .hole a) _ wr).trans ((PureSteps.beta _ a).trans .refl)⟩

theorem mapV_sum_head (A B : VTy) (wr a : Val) : ∃ e₁ e₂,
    BoCa.Fig16.LogRel.Core.PureSteps (ℍ := ℍ)
      (.app (.app (.val (mapV (.sum A B))) (.val wr)) (.val a)) (.case a.1 e₁ e₂) :=
  ⟨_, _, (PureSteps.beta_in (.appL .hole a) _ wr).trans ((PureSteps.beta _ a).trans .refl)⟩

/-- A term that is neither a value nor an application is not the driver's configuration. -/
theorem plug_ne_drive {K : Kont} {x : Expr} (hx : ¬ IsVal x) (hna : ∀ f b, x ≠ .app f b)
    (w : Val) : K.plug x ≠ driveE (.val w) := by
  intro h
  have := plug_eq_drive h hx
  subst this
  exact hna _ _ h

/-- `map_{A↑} wr a` reaches `a`, at a configuration a typed program reaches: `A↑` holds no `X`,
and an answer of the wrong shape is stuck. -/
theorem mapV_rename_steps (hL : LiveOK (ℍ := ℍ) RF Ξ J) :
    ∀ (A : VTy) (K : Kont) (μ : Heap) (wr a : Val),
      (ourInst (ℍ := ℍ) RF Ξ J).Live
        (μ, K.plug (.app (.app (.val (mapV (A.rename Nat.succ))) (.val wr)) (.val a))) →
      (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
        (μ, K.plug (.app (.app (.val (mapV (A.rename Nat.succ))) (.val wr)) (.val a)))
        (μ, K.plug a.1)
  | .tensor A B, K, μ, wr, a, hlive => by
      by_cases hp : ∃ x y, a.1 = Expr.pair x y
      · obtain ⟨x, y, ha⟩ := hp
        have hv := a.2
        rw [ha] at hv
        obtain rfl : a = Val.pair ⟨x, hv.pair_left⟩ ⟨y, hv.pair_right⟩ := Subtype.ext ha
        have h1 := pureSteps_of_core (μ := μ) (RF := RF) (Ξ := Ξ) (J := J)
          (PureSteps.plug K (mapV_tensor_steps (A.rename Nat.succ) (B.rename Nat.succ) wr
            ⟨x, hv.pair_left⟩ ⟨y, hv.pair_right⟩))
        have hl1 := live_of_pureSteps hlive h1
        have h2 := mapV_rename_steps hL A (K.comp (.pairL .hole
          (.app (.app (.val (mapV (B.rename Nat.succ))) (.val wr)) y))) μ wr ⟨x, hv.pair_left⟩
          (by rw [Kont.plug_comp]; exact hl1)
        rw [Kont.plug_comp, Kont.plug_comp] at h2
        have hl2 := live_of_pureSteps hl1 h2
        have h3 := mapV_rename_steps hL B (K.comp (.pairR ⟨x, hv.pair_left⟩ .hole)) μ wr
          ⟨y, hv.pair_right⟩ (by rw [Kont.plug_comp]; exact hl2)
        rw [Kont.plug_comp, Kont.plug_comp] at h3
        exact h1.trans (h2.trans h3)
      · exfalso
        obtain ⟨e, he⟩ := mapV_tensor_head (ℍ := ℍ) (A.rename Nat.succ) (B.rename Nat.succ) wr a
        have hl := live_of_pureSteps hlive
          (pureSteps_of_core (RF := RF) (Ξ := Ξ) (J := J) (μ := μ) (PureSteps.plug K he))
        exact not_goesOn_stuck (RF := RF) (Ξ := Ξ)
          (stuckAt_letpair (v := a) (fun x y h => hp ⟨x, y, h⟩) e) K μ
          (plug_ne_drive (by simp) (by simp)) (hL _ hl).2
  | .sum A B, K, μ, wr, a, hlive => by
      by_cases h₁ : ∃ x, a.1 = Expr.inj₁ x
      · obtain ⟨x, ha⟩ := h₁
        have hv := a.2
        rw [ha] at hv
        obtain rfl : a = Val.inj₁ ⟨x, hv.inj₁_inv⟩ := Subtype.ext ha
        have h1 := pureSteps_of_core (μ := μ) (RF := RF) (Ξ := Ξ) (J := J)
          (PureSteps.plug K (mapV_sum₁_steps (A.rename Nat.succ) (B.rename Nat.succ) wr
            ⟨x, hv.inj₁_inv⟩))
        have hl1 := live_of_pureSteps hlive h1
        have h2 := mapV_rename_steps hL A (K.comp (.inj₁ .hole)) μ wr ⟨x, hv.inj₁_inv⟩
          (by rw [Kont.plug_comp]; exact hl1)
        rw [Kont.plug_comp, Kont.plug_comp] at h2
        exact h1.trans h2
      by_cases h₂ : ∃ x, a.1 = Expr.inj₂ x
      · obtain ⟨x, ha⟩ := h₂
        have hv := a.2
        rw [ha] at hv
        obtain rfl : a = Val.inj₂ ⟨x, hv.inj₂_inv⟩ := Subtype.ext ha
        have h1 := pureSteps_of_core (μ := μ) (RF := RF) (Ξ := Ξ) (J := J)
          (PureSteps.plug K (mapV_sum₂_steps (A.rename Nat.succ) (B.rename Nat.succ) wr
            ⟨x, hv.inj₂_inv⟩))
        have hl1 := live_of_pureSteps hlive h1
        have h2 := mapV_rename_steps hL B (K.comp (.inj₂ .hole)) μ wr ⟨x, hv.inj₂_inv⟩
          (by rw [Kont.plug_comp]; exact hl1)
        rw [Kont.plug_comp, Kont.plug_comp] at h2
        exact h1.trans h2
      exfalso
      obtain ⟨e₁, e₂, he⟩ := mapV_sum_head (ℍ := ℍ) (A.rename Nat.succ) (B.rename Nat.succ) wr a
      have hl := live_of_pureSteps hlive
        (pureSteps_of_core (RF := RF) (Ξ := Ξ) (J := J) (μ := μ) (PureSteps.plug K he))
      exact not_goesOn_stuck (RF := RF) (Ξ := Ξ)
        (stuckAt_case (v := a) (fun x => ⟨fun h => h₁ ⟨x, h⟩, fun h => h₂ ⟨x, h⟩⟩) e₁ e₂) K μ
        (plug_ne_drive (by simp) (by simp)) (hL _ hl).2
  | .box b A, K, μ, wr, a, hlive => mapV_rename_steps hL A K μ wr a hlive
  | .tvar n, K, μ, wr, a, _ => pureSteps_of_core (PureSteps.plug K (mapV_id_steps rfl wr a))
  | .mu A, K, μ, wr, a, _ => pureSteps_of_core (PureSteps.plug K (mapV_id_steps rfl wr a))
  | .unit, K, μ, wr, a, _ | .zero, K, μ, wr, a, _ | .thunk _, K, μ, wr, a, _
  | .ref _, K, μ, wr, a, _ | .imm _ _, K, μ, wr, a, _ | .mut _ _, K, μ, wr, a, _
  | .bang _, K, μ, wr, a, _ | .unk, K, μ, wr, a, _ | .int _, K, μ, wr, a, _
  | .fam _, K, μ, wr, a, _ | .opq _, K, μ, wr, a, _ =>
      pureSteps_of_core (PureSteps.plug K (mapV_id_steps rfl wr a))

theorem unfoldE_of_val (A B : VTy) (f g : Expr) (s : Val) :
    unfoldE A B f g s.1 = (etaN (CTy.loopEffBody [] A B) (stepV f g) s).1 := by
  unfold unfoldE; rw [dif_pos ⟨.lam, s.2⟩]; rfl

theorem unfoldE_of_not_val (A B : VTy) (f g s : Expr) (h : ¬ IsVal s) :
    unfoldE A B f g s = .unit := by
  unfold unfoldE; rw [dif_neg (fun h' => h h'.2)]

/-- **`LoopLaws`**: `next` and `close` of a loop value run the coalgebra's branch under a frame
that catches nothing and holds no finaliser, and map its answer, at a configuration a typed
program reaches. -/
theorem loopLaws_ourInst (hL : LiveOK (ℍ := ℍ) RF Ξ J) : (ourInst (ℍ := ℍ) RF Ξ J).LoopLaws := by
  refine ⟨?_, ?_⟩
  · rintro ⟨μ, e⟩ (A : OVTy) (B : OVTy) (f : OVal) (g : OVal) (s : OVal) hlive
    by_cases hs : IsVal s.1
    · refine ⟨loopK (.sum ((A.den fun _ => []).rename Nat.succ) (.tvar 0))
        (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1,
        fun _ => rfl, bindK_noUnwind _, ?_, ?_, ?_⟩
      · show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
          (μ, .app (unfoldE (A.den fun _ => []) (B.den fun _ => []) f.1 g.1 s.1) (.inj₁ .unit)) _
        rw [unfoldE_of_val _ _ _ _ ⟨s.1, hs⟩]
        exact pureSteps_of_core (next_steps _ _ f.1 g.1 ⟨s.1, hs⟩)
      · rintro (a : OVal) hla
        have ha : IsVal a.1 := val_of_live hL hla a.2
          (K := (loopK (.sum ((A.den fun _ => []).rename Nat.succ) (.tvar 0))
            (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1).comp
              (.inj₁ .hole)) (by rw [Kont.plug_comp]; rfl)
        have h1 := pureSteps_of_core (RF := RF) (Ξ := Ξ) (J := J) (μ := μ)
          ((loopK_steps (ℍ := ℍ) (.sum ((A.den fun _ => []).rename Nat.succ) (.tvar 0))
            (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1
            (Val.inj₁ ⟨a.1, ha⟩)).trans (mapV_sum₁_steps _ _ _ ⟨a.1, ha⟩))
        exact h1.trans (mapV_rename_steps hL (A.den fun _ => []) (.inj₁ .hole) μ _ ⟨a.1, ha⟩
          (live_of_pureSteps hla h1))
      · rintro (s' : OVal) hls
        have hs' : IsVal s'.1 := val_of_live hL hls s'.2
          (K := (loopK (.sum ((A.den fun _ => []).rename Nat.succ) (.tvar 0))
            (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1).comp
              (.inj₂ .hole)) (by rw [Kont.plug_comp]; rfl)
        show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps _
          (μ, .inj₂ (unfoldE (A.den fun _ => []) (B.den fun _ => []) f.1 g.1 s'.1))
        rw [unfoldE_of_val _ _ _ _ ⟨s'.1, hs'⟩]
        exact pureSteps_of_core
          ((loopK_steps (ℍ := ℍ) (.sum ((A.den fun _ => []).rename Nat.succ) (.tvar 0))
            (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1
            (Val.inj₂ ⟨s'.1, hs'⟩)).trans
            ((mapV_sum₂_steps _ _ _ ⟨s'.1, hs'⟩).trans
              (PureSteps.plug (.inj₂ .hole) ((mapV_var_steps _ _).trans (hN_steps _ _ _)))))
    · exfalso
      have hg := (hL _ hlive).2
      change GoesOn RF Ξ
        (μ, .app (unfoldE (A.den fun _ => []) (B.den fun _ => []) f.1 g.1 s.1) (.inj₁ .unit)) at hg
      rw [unfoldE_of_not_val _ _ _ _ _ hs] at hg
      exact not_goesOn_stuck (stuckAt_unit_app (Val.inj₁ Val.unit)) .hole μ
        (fun _ => plug_unit_app_ne_drive _ _ _) hg
  · rintro ⟨μ, e⟩ (A : OVTy) (B : OVTy) (f : OVal) (g : OVal) (s : OVal) hlive
    by_cases hs : IsVal s.1
    · refine ⟨loopK ((B.den fun _ => []).rename Nat.succ)
        (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1,
        fun _ => rfl, bindK_noUnwind _, ?_, ?_⟩
      · show (ourInst (ℍ := ℍ) RF Ξ J).PureSteps
          (μ, .app (unfoldE (A.den fun _ => []) (B.den fun _ => []) f.1 g.1 s.1) (.inj₂ .unit)) _
        rw [unfoldE_of_val _ _ _ _ ⟨s.1, hs⟩]
        exact pureSteps_of_core (close_steps _ _ f.1 g.1 ⟨s.1, hs⟩)
      · rintro (v : OVal) hlv
        have hv : IsVal v.1 := val_of_live hL hlv v.2
          (K := loopK ((B.den fun _ => []).rename Nat.succ)
            (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1) rfl
        have h1 := pureSteps_of_core (RF := RF) (Ξ := Ξ) (J := J) (μ := μ)
          (loopK_steps (ℍ := ℍ) ((B.den fun _ => []).rename Nat.succ)
            (CTy.loopEffBody [] (A.den fun _ => []) (B.den fun _ => [])) f.1 g.1 ⟨v.1, hv⟩)
        exact h1.trans (mapV_rename_steps hL (B.den fun _ => []) .hole μ _ ⟨v.1, hv⟩
          (live_of_pureSteps hlv h1))
    · exfalso
      have hg := (hL _ hlive).2
      change GoesOn RF Ξ
        (μ, .app (unfoldE (A.den fun _ => []) (B.den fun _ => []) f.1 g.1 s.1) (.inj₂ .unit)) at hg
      rw [unfoldE_of_not_val _ _ _ _ _ hs] at hg
      exact not_goesOn_stuck (stuckAt_unit_app (Val.inj₂ Val.unit)) .hole μ
        (fun _ => plug_unit_app_ne_drive _ _ _) hg


/-! ### S0 and S4 at the open-row form -/

/-- **S0** at the open-row form: its labels' names are not the reserved `0`. -/
theorem machShape_orow {J : OurTyping orowRF} (hL : LiveOK (ℍ := ℍ) orowRF Ξ J) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).MachShape :=
  ⟨confLaws_ourInst, kontLaws_orow J, appLaw_ourInst hL, congr_ourInst, noIO_ourInst,
    opStuck_ourInst (fun l => l.2.1), dataInj_ourInst, loopLaws_ourInst hL, driveLaws_ourInst hL⟩

/-- **S4 with no cell** at the open-row form, at an effect context whose resuming operations are
unrestricted: its labels' names are not `0` and their signatures have at most `2³²` operations. -/
theorem handlerSemNoCell_orow {J : OurTyping orowRF} (hL : LiveOK (ℍ := ℍ) orowRF Ξ J)
    (hU : Ξ.CatchUnr) : (ourInst (ℍ := ℍ) orowRF Ξ J).HandlerSemNoCell :=
  handlerSemNoCell_ourInst hL (fun l => l.2.1) (fun l => l.2.2.2) hU

end Targets.Inst

end
