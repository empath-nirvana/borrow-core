import Targets.A.Theories
import Targets.Instance.UnaryLaws

/-!
# The Instance — theories at our instance: the answering class, models and comodels (D1.h4)

At our instance, `A.Theories`' answering handler is Core's run-time handler frame with the
state-passing clauses, and its runs are calm (`Calm`) when the co-operations' are quiet
(`PureCo`).  `[Core σ=[]]`

* **The fold** (`calm_fold`): a straight-line computation handled by `ansHnd co` from the state
  `s` runs, calmly, as the co-operations do on the threaded state (`CoRun`), to
  `(□ to f. f sₙ)[hnd H (k fin)]`.  Each operation is caught, its clause returns the state
  function, the closing frame applies it to the current state, the co-operation runs, and `κ` is
  resumed in place with the closing frame at the new state (`calm_opStep`): quietly when `κ` owns
  no cell (`quiet_opStep`), and around the cell when it does, the resume releasing it
  (`cellQuiet_opStep`, SPEC §25).  This is the native counterpart of `handle_fold`
  (`Core/Handlers.lean`), which states the same of the borrow form.
* **The co-run** (`quiet_coRun`): the co-operations' own run of the computation reaches
  `(sₙ, fin)` quietly.
* **D1.h4 (c)** (`ansCorrect_of_comodel`): at a typing system whose reached configurations are
  closed, co-operations that run quietly and form a comodel give a correct handler: the two sides
  of each equation reach one configuration calmly (`calm_side`).
* **Global state** (`state_isComodel`, `state_correct`): `stateCo` is a comodel of the four laws
  at every carrier, and its handler is correct, at every row form, effect context and typing
  system with `LiveOK`; so at `J₁` (`state_correct_J₁`).
* **Non-vacuity** (`not_ansCorrect_badState`): at `J₁` and an admissible effect context with a
  state signature (`Ξst`), the handler whose `put` keeps the old state fails the update–lookup law,
  at a typed program that reaches the law's left side.

`PureCo` is this piece's added hypothesis (TIER1-PLAN §5): `RunsAlike` compares runs step by step,
and co-operations that allocate or show events would make the two sides of an equation differ in
their memories or traces.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE hndVal kappa
  clauseAt capTag kappaAt kappaC kappaCBody kappaCell)
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg HeadChain lookRun lookEnd lookRun_sound closedAt_kappa
  closedAt_plug_iff kont_shift_closed)
open Targets.A (VExpr SLComp Eqn)
open Targets (closedAt_of_derives CDerivesAt RowAt rowAt_nil rowAt_ofEff_append)

/-! ### Values written over the parameters and the answers -/

/-- A value expression's value, at the parameters `vs` and the answers so far `rs`, the latest
first. -/
def VExpr.eval (vs rs : List Val) : VExpr → Val
  | .param p => vs.getD p Val.unit
  | .res r => rs.getD (rs.length - 1 - r) Val.unit
  | .unit => Val.unit
  | .pair a b => Val.pair (VExpr.eval vs rs a) (VExpr.eval vs rs b)
  | .inl a => Val.inj₁ (VExpr.eval vs rs a)
  | .inr a => Val.inj₂ (VExpr.eval vs rs a)

/-- A value expression is well formed after `j` answers, at `np` parameters. -/
def VExpr.WF (np j : ℕ) : VExpr → Prop
  | .param p => p < np
  | .res r => r < j
  | .unit => True
  | .pair a b => VExpr.WF np j a ∧ VExpr.WF np j b
  | .inl a | .inr a => VExpr.WF np j a

/-- A computation from its `j`-th step is well formed, at `np` parameters and `nops` operations. -/
def SLComp.WFFrom (np : ℕ) (fin : VExpr) (nops : ℕ) : List (ℕ × VExpr) → ℕ → Prop
  | [], j => VExpr.WF np j fin
  | (i, a) :: rest, j => i < nops ∧ VExpr.WF np j a ∧ SLComp.WFFrom np fin nops rest (j + 1)

/-- An equation is well formed at `nops` operations. -/
def Eqn.WF {Ty : Type} (nops : ℕ) (eq : Eqn Ty) : Prop :=
  SLComp.WFFrom eq.params.length eq.lhs.fin nops eq.lhs.steps 0 ∧
    SLComp.WFFrom eq.params.length eq.rhs.fin nops eq.rhs.steps 0

theorem closedAt_eval {vs rs : List Val} (hvs : ∀ v ∈ vs, closedAt 0 v.1 = true)
    (hrs : ∀ v ∈ rs, closedAt 0 v.1 = true) : ∀ a : VExpr, closedAt 0 (VExpr.eval vs rs a).1 = true
  | .param p => by
      simp only [VExpr.eval, List.getD_eq_getElem?_getD]
      cases h : vs[p]? with
      | none => rfl
      | some v => exact hvs v (List.mem_of_getElem? h)
  | .res r => by
      simp only [VExpr.eval, List.getD_eq_getElem?_getD]
      cases h : rs[rs.length - 1 - r]? with
      | none => rfl
      | some v => exact hrs v (List.mem_of_getElem? h)
  | .unit => rfl
  | .pair a b => by
      simp only [VExpr.eval, Val.pair, closedAt, Bool.and_eq_true]
      exact ⟨closedAt_eval hvs hrs a, closedAt_eval hvs hrs b⟩
  | .inl a => closedAt_eval hvs hrs a
  | .inr a => closedAt_eval hvs hrs a

section Subst
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

theorem substAll_var_some {γ : List Val} {i : ℕ} {v : Val} (h : γ[i]? = some v) :
    substAll γ (.var i) = v.1 := by
  show Expr.psub 0 γ (.var i) = _
  simp only [Expr.psub, Nat.not_lt_zero, if_false, Nat.sub_zero, h]
  rw [Val.shift_zero]

theorem vAt_subst {vs rs : List Val} {k : Val} :
    ∀ a : VExpr, VExpr.WF vs.length rs.length a →
      substAll (rs ++ vs ++ [k]) ((ourInst (ℍ := ℍ) RF Ξ J).vAt rs.length a).1 =
        (VExpr.eval vs rs a).1
  | .param p, h => by
      have h' : (rs ++ vs ++ [k])[rs.length + p]? = some (vs.getD p Val.unit) := by
        have hp : p < vs.length := h
        rw [List.append_assoc, List.getElem?_append_right (by omega),
          show rs.length + p - rs.length = p by omega, List.getElem?_append_left hp,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
        rfl
      exact substAll_var_some h'
  | .res r, h => by
      have h' : (rs ++ vs ++ [k])[rs.length - 1 - r]? =
          some (rs.getD (rs.length - 1 - r) Val.unit) := by
        have hr : rs.length - 1 - r < rs.length := by
          have : r < rs.length := h
          omega
        rw [List.append_assoc, List.getElem?_append_left hr, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hr]
        rfl
      exact substAll_var_some h'
  | .unit, _ => rfl
  | .pair a b, h => by
      show Expr.psub 0 _ (.pair _ _) = _
      simp only [Expr.psub]
      exact congrArg₂ Expr.pair (vAt_subst a h.1) (vAt_subst b h.2)
  | .inl a, h => by
      show Expr.psub 0 _ (.inj₁ _) = _
      simp only [Expr.psub]
      exact congrArg Expr.inj₁ (vAt_subst a h)
  | .inr a, h => by
      show Expr.psub 0 _ (.inj₂ _) = _
      simp only [Expr.psub]
      exact congrArg Expr.inj₂ (vAt_subst a h)

theorem substAll_cons_eq (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

/-- **`lets` binds its values by β-steps**: at closed values, `lets vs N` reaches `N` closed by
`vs` quietly. -/
theorem quiet_lets : ∀ (vs : List Val), (∀ v ∈ vs, closedAt 0 v.1 = true) → ∀ N : Expr,
    Quiet (ℍ := ℍ) ((ourInst (ℍ := ℍ) RF Ξ J).lets (vs.map OVal.ofVal) N) (substAll vs N)
  | [], _, N => by
      show Quiet (ℍ := ℍ) N (Expr.psub 0 [] N)
      rw [BoCa.Adequacy.psub_nil]; exact Quiet.refl N
  | v :: vs, h, N => by
      have ih := quiet_lets vs (fun w hw => h w (List.mem_cons_of_mem _ hw)) (bindE v.1 N)
      have hv := h v List.mem_cons_self
      have e : substAll vs (bindE v.1 N) = .app (.val (.lam (Expr.psub 1 vs N))) (.val v) := by
        show Expr.psub 0 vs (.app (.lam N) v.1) = _
        simp only [Expr.psub, Expr.val, Val.lam]
        rw [psub_closedAt v.1 vs hv (le_refl _)]
      rw [e] at ih
      have hb := quiet_beta (ℍ := ℍ) .hole (Expr.psub 1 vs N) v
      rw [← substAll_cons_eq] at hb
      exact ih.trans hb


/-- The state-passing clause's body at our instance, under `s`, `k` and `a`:
`co (s, a) to q. let (s', b) = q in k.resume b to f. f s'`. -/
def ansBody (co : Expr) : Expr :=
  bindE (appE co (.pair (.var 0) (.var 2)))
    (.letpair (.var 0) (bindE (resumeE (.var 4) (.var 0)) (appE (.var 0) (.var 2))))

/-- The clause's last part, after the co-operation: `let (s', b) = q in k.resume b to f. f s'`. -/
def ansRest (κ : Expr) : Expr :=
  .letpair (.var 0) (bindE (resumeE κ (.var 0)) (appE (.var 0) (.var 2)))

/-- The state-passing clause at our instance. -/
def ansClauseE (co : Expr) : Expr := .lam (.letpair (.var 0) (.lam (ansBody co)))

/-- The answer clause at our instance: `λr. λs. (s, r)`. -/
def ansRetE : Expr := .lam (.lam (.pair (.var 0) (.var 1)))

theorem ansClause_val (co : OVal) :
    ((ourInst (ℍ := ℍ) RF Ξ J).ansClause co).1 = ansClauseE co.1 := rfl

theorem ansRet_val : ((ourInst (ℍ := ℍ) RF Ξ J).ansRet).1 = ansRetE := rfl

theorem ansBody_closedAt {co : Expr} (hc : closedAt 0 co = true) :
    closedAt 3 (ansBody co) = true := by
  have h1 : closedAt 4 (co.shift 1 0) = true := by
    rw [shift_closed0 hc]; exact closedAt_mono _ hc (by omega)
  simp [ansBody, bindE, appE, resumeE, closedAt, Expr.val, Val.lam, Expr.shift, h1]

/-- The clause's `letpair`: `a` and `k` substituted. -/
theorem ansBody_letpair {co κ : Expr} (hc : closedAt 0 co = true) (hκ : closedAt 0 κ = true)
    (hκv : IsVal κ) {a : Val} (ha : closedAt 0 a.1 = true) :
    ((Expr.lam (ansBody co)).subst 0 (Val.shift 1 0 ⟨κ, hκv⟩)).subst 0 a =
      .lam (bindE (appE co (.pair (.var 0) a.1)) (ansRest κ)) := by
  simp [ansBody, ansRest, bindE, appE, resumeE, Expr.subst, Expr.shift, Expr.val, Val.lam,
    Val.shift, shift_closed0 hc, subst_closedE hc, shift_closed0 hκ, subst_closedE hκ,
    shift_closed0 ha]

/-- The state applied: the clause's body at the state `s`. -/
theorem ansBody_state {co κ : Expr} (hc : closedAt 0 co = true) (hκ : closedAt 0 κ = true)
    {a s : Val} (ha : closedAt 0 a.1 = true) :
    (bindE (appE co (.pair (.var 0) a.1)) (ansRest κ)).subst 0 s =
      bindE (appE co (.pair s.1 a.1)) (ansRest κ) := by
  simp [ansRest, bindE, appE, resumeE, Expr.subst, Expr.shift, Expr.val, Val.lam,
    shift_closed0 hc, subst_closedE hc, shift_closed0 hκ, subst_closedE hκ, subst_closedE ha]

/-- The co-operation's answer bound: `let (s', b) = (s', b) in …`. -/
theorem ansRest_pair {κ : Expr} (hκ : closedAt 0 κ = true) (q : Val) :
    (ansRest κ).subst 0 q =
      .letpair (.val q) (bindE (resumeE κ (.var 0)) (appE (.var 0) (.var 2))) := by
  simp [ansRest, bindE, appE, resumeE, Expr.subst, Expr.shift, Expr.val, Val.lam,
    shift_closed0 hκ, subst_closedE hκ]

/-- The answer split: `k.resume b to f. f s'`. -/
theorem ansRest_split {κ : Expr} (hκ : closedAt 0 κ = true) {s' b : Val}
    (hs' : closedAt 0 s'.1 = true) (hb : closedAt 0 b.1 = true) :
    ((bindE (resumeE κ (.var 0)) (appE (.var 0) (.var 2))).subst 0 (b.shift 1 0)).subst 0 s' =
      bindE (resumeE κ b.1) (appE (.var 0) s'.1) := by
  simp [bindE, appE, resumeE, Expr.subst, Expr.shift, Expr.val, Val.lam, Val.shift,
    shift_closed0 hκ, subst_closedE hκ, shift_closed0 hs', shift_closed0 hb, subst_closedE hb]


theorem isVal_ansClauses (co : List OVal) :
    IsVal (clausesE (co.map fun c => ansClauseE c.1)) :=
  isVal_clausesE _ fun e he => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 he
    exact .lam

/-- **The answering handler's value at our instance**, at the tags `ts` of its operations. -/
def ansHV (n : UInt32) (ts : List Qual) (co : List OVal) : Val :=
  hndVal n (qualsVal ts) ⟨ansRetE, .lam⟩ ⟨_, isVal_ansClauses co⟩

/-- The closing frame at the state `s`: `□ to f. f s`. -/
def stFrame (s : Val) : Kont := bindK (appE (.var 0) s.1)

theorem closedAt_ansHV (n : UInt32) (ts : List Qual) {co : List OVal}
    (hco : ∀ c ∈ co, closedAt 0 c.1 = true) : closedAt 0 (ansHV n ts co).1 = true := by
  have hcl : ∀ cs : List OVal, (∀ c ∈ cs, closedAt 0 c.1 = true) →
      closedAt 0 (clausesE (cs.map fun c => ansClauseE c.1)) = true := by
    intro cs hcs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
        have hc := hcs c List.mem_cons_self
        have hb := ansBody_closedAt hc
        simp only [List.map_cons, clausesE, ansClauseE, closedAt, Bool.and_eq_true]
        exact ⟨⟨rfl, closedAt_mono _ hb (by omega)⟩, ih fun c' h' => hcs c' (List.mem_cons_of_mem _ h')⟩
  simp only [ansHV, hndVal, Val.pair, Val.i32, ansRetE, closedAt, Bool.and_eq_true, Bool.true_and]
  exact ⟨Targets.closedAt_qualsVal 0 ts, by simp, hcl co hco⟩

theorem clauseAt_ansHV {co : List OVal} {i : ℕ} (hi : i < co.length) :
    clauseAt (clausesE (co.map fun c => ansClauseE c.1)) i = some ⟨ansClauseE co[i].1, .lam⟩ :=
  clauseAt_clausesE _ i .lam (by rw [List.getElem?_map, List.getElem?_eq_getElem hi]; rfl)

/-- **The answering clause after the catch**: applied to `(a, κ)` under the closing frame at the
state `s`, the clause answers the state function, the closing frame applies it to `s`, the
co-operation `co_i` runs quietly from `(s, a)` to `(s', b)`, and the clause resumes `κ` at `b` under
the closing frame at `s'`.  The clause's β-step and `letpair`; the closing frame's β-step and
`app`; the state function's β-step; the co-operation; the bind and the `letpair` of its answer;
`resume`'s β-step. -/
theorem quiet_ansClause {co : List OVal} {i : ℕ} (hi : i < co.length) (hc : closedAt 0 co[i].1 = true)
    (κ : Expr) (hκv : IsVal κ) (hκ : closedAt 0 κ = true) {s a s' b : Val}
    (hs : closedAt 0 s.1 = true) (ha : closedAt 0 a.1 = true) (hs' : closedAt 0 s'.1 = true)
    (hb : closedAt 0 b.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app co[i].1 (Val.pair s a).1) (.val (Val.pair s' b))) :
    Quiet (ℍ := ℍ)
      ((stFrame s).plug (.app (.val ⟨ansClauseE co[i].1, .lam⟩) (.pair (.val a) κ)))
      ((stFrame s').plug (.app (.app κ (.val (Val.inj₁ .unit))) (.val b))) := by
  let κV : Val := ⟨κ, hκv⟩
  -- the clause answers the state function
  have h₂ := quiet_beta (ℍ := ℍ) (stFrame s) (.letpair (.var 0) (.lam (ansBody co[i].1)))
    (Val.pair a κV)
  have e₂ : Expr.subst 0 (Val.pair a κV) (.letpair (.var 0) (.lam (ansBody co[i].1))) =
      .letpair (.val (Val.pair a κV)) (.lam (ansBody co[i].1)) := by
    show Expr.letpair _ ((Expr.lam (ansBody co[i].1)).subst 2 _) = _
    rw [subst_closedAt _ _ (show closedAt 2 (Expr.lam (ansBody co[i].1)) = true from
      ansBody_closedAt hc) (le_refl _)]
    rfl
  rw [e₂] at h₂
  refine h₂.trans ?_
  have h₃ := quiet_letpair (ℍ := ℍ) (stFrame s) a κV (.lam (ansBody co[i].1))
  rw [ansBody_letpair hc hκ hκv ha] at h₃
  refine h₃.trans ?_
  -- the closing frame applies it to `s`
  have h₄ := quiet_beta (ℍ := ℍ) .hole (appE (.var 0) s.1)
    ⟨.lam (bindE (appE co[i].1 (.pair (.var 0) a.1)) (ansRest κ)), .lam⟩
  have e₄ : Expr.subst 0
      ⟨.lam (bindE (appE co[i].1 (.pair (.var 0) a.1)) (ansRest κ)), .lam⟩
      (appE (.var 0) s.1) =
      appE (.lam (bindE (appE co[i].1 (.pair (.var 0) a.1)) (ansRest κ))) s.1 := by
    simp [appE, Expr.subst, Expr.shift, subst_closedE hs]
  rw [e₄] at h₄
  refine (show Quiet (ℍ := ℍ) ((stFrame s).plug _) _ from h₄).trans ?_
  have h₅ := quiet_appE (ℍ := ℍ) .hole
    (.lam (bindE (appE co[i].1 (.pair (.var 0) a.1)) (ansRest κ))) s
  refine h₅.trans ?_
  have h₆ := quiet_beta (ℍ := ℍ) .hole
    (bindE (appE co[i].1 (.pair (.var 0) a.1)) (ansRest κ)) s
  rw [ansBody_state hc hκ ha] at h₆
  refine h₆.trans ?_
  -- the co-operation, under the clause's rest
  have h₇ := ((quiet_appE (ℍ := ℍ) .hole co[i].1 (Val.pair s a)).trans hq).plug
    (bindK (ansRest κ))
  refine h₇.trans ?_
  have h₈ := quiet_beta (ℍ := ℍ) .hole (ansRest κ) (Val.pair s' b)
  rw [ansRest_pair hκ] at h₈
  refine h₈.trans ?_
  have h₉ := quiet_letpair (ℍ := ℍ) .hole s' b
    (bindE (resumeE κ (.var 0)) (appE (.var 0) (.var 2)))
  rw [ansRest_split hκ hs' hb] at h₉
  refine h₉.trans ?_
  -- the resume, under the closing frame at `s'`
  have h₁₀ := quiet_resumeE (ℍ := ℍ) (stFrame s') κ b
  exact (show Quiet (ℍ := ℍ) (.app (.val (.lam (appE (.var 0) s'.1))) (resumeE κ b.1)) _ from h₁₀)

/-- **One operation whose `κ` owns no cell, caught by the answering handler**: at the state `s`,
`op (n, i, a)` with the rest `R` runs quietly to `R[b]` under the handler at the state `s'`, when
the co-operation `co_i` runs quietly from `(s, a)` to `(s', b)`.  The catch; the clause
(`quiet_ansClause`); `κ`'s four steps (`quiet_kappa_resume`), which reinstall the handler under the
closing frame at `s'`; and the rest's β-step. -/
theorem quiet_opStep {n i : UInt32} {ts : List Qual} {co : List OVal}
    (hco : ∀ c ∈ co, closedAt 0 c.1 = true) (hi : i.toNat < co.length) {s a s' b : Val}
    (hs : closedAt 0 s.1 = true) (ha : closedAt 0 a.1 = true) (hs' : closedAt 0 s'.1 = true)
    (hb : closedAt 0 b.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app co[i.toNat].1 (Val.pair s a).1) (.val (Val.pair s' b)))
    {R : Expr} (hR : closedAt 1 R = true)
    (hu : kappaAt (capTag (qualsVal ts).1 i.toNat) (ansHV n ts co) (bindK R) =
      kappa (ansHV n ts co) (bindK R)) :
    Quiet (ℍ := ℍ)
      ((stFrame s).plug (hndE (ansHV n ts co) (bindE (performE (.val (opPayload n i a))) R)))
      ((stFrame s').plug (hndE (ansHV n ts co) (R.subst 0 b))) := by
  have hc : closedAt 0 co[i.toNat].1 = true := hco _ (List.getElem_mem hi)
  have hH := closedAt_ansHV n ts hco
  have hRk : closedAt 0 ((bindK R).plug .unit) = true := by
    simp [bindK, Kont.plug, closedAt, hR]
  have hκ : closedAt 0 (kappa (ansHV n ts co) (bindK R)) = true := closedAt_kappa hH hRk
  have hκv := isVal_kappa (ansHV n ts co) (bindK R)
  -- the catch
  have h₁ := quiet_hop (ℍ := ℍ) (stFrame s) n i (qualsVal ts) ⟨ansRetE, .lam⟩
    ⟨_, isVal_ansClauses co⟩ ⟨ansClauseE co[i.toNat].1, .lam⟩ a (bindK R)
    (clauseAt_ansHV hi) (by simp [bindK, Kont.HasHnd]) hu
  refine h₁.trans ?_
  refine (quiet_ansClause hi hc _ hκv hκ hs ha hs' hb hq).trans ?_
  have h₁₁ := quiet_kappa_resume (ℍ := ℍ) (stFrame s') (ansHV n ts co) (bindK R) b
  refine h₁₁.trans ?_
  have h₁₂ := quiet_beta (ℍ := ℍ)
    ((stFrame s').comp (.appR (.app (.prim .hnd) (ansHV n ts co).1) .hole)) R b
  simp only [Kont.plug_comp] at h₁₂
  exact h₁₂

/-- **One operation whose `κ` owns a cell, caught by the answering handler**: as `quiet_opStep`,
around the cell (SPEC §25).  The catch and the allocation; at the cell's location `ℓ`, `κ`'s β-step
at `ℓ`, the clause (`quiet_ansClause`) and `κ`'s resume branch up to the release of `ℓ`; after it,
the rest of the resume branch (`kappaC_resume_parts`) and the rest's β-step. -/
theorem cellQuiet_opStep {n i : UInt32} {ts : List Qual} {co : List OVal} (aff : Bool)
    (hco : ∀ c ∈ co, closedAt 0 c.1 = true) (hi : i.toNat < co.length) {s a s' b : Val}
    (hs : closedAt 0 s.1 = true) (ha : closedAt 0 a.1 = true) (hs' : closedAt 0 s'.1 = true)
    (hb : closedAt 0 b.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app co[i.toNat].1 (Val.pair s a).1) (.val (Val.pair s' b)))
    {R : Expr} (hR : closedAt 1 R = true)
    (hcell : kappaAt (capTag (qualsVal ts).1 i.toNat) (ansHV n ts co) (bindK R) =
      kappaCell aff (ansHV n ts co) (bindK R)) :
    CellQuiet (ℍ := ℍ)
      ((stFrame s).plug (hndE (ansHV n ts co) (bindE (performE (.val (opPayload n i a))) R)))
      ((stFrame s').plug (hndE (ansHV n ts co) (R.subst 0 b))) := by
  have hc : closedAt 0 co[i.toNat].1 = true := hco _ (List.getElem_mem hi)
  have hH := closedAt_ansHV n ts hco
  have hRk : closedAt 0 ((bindK R).plug .unit) = true := by
    simp [bindK, Kont.plug, closedAt, hR]
  have hh : ∀ μ, Head (ℍ := ℍ) μ
      (hndE (ansHV n ts co) ((bindK R).plug (performE (.val (opPayload n i a))))) μ
      (.app (.val ⟨ansClauseE co[i.toNat].1, .lam⟩)
        (.pair (.val a) (kappaCell aff (ansHV n ts co) (bindK R)))) := by
    intro μ
    have h : Head (ℍ := ℍ) μ
        (hndE (ansHV n ts co) ((bindK R).plug (performE (.val (opPayload n i a))))) μ
        (.app (.val ⟨ansClauseE co[i.toNat].1, .lam⟩)
          (.pair (.val a) (kappaAt (capTag (qualsVal ts).1 i.toNat) (ansHV n ts co) (bindK R)))) :=
      Head.hop (ℍ := ℍ) μ n i (qualsVal ts) ⟨ansRetE, .lam⟩ ⟨_, isVal_ansClauses co⟩
        ⟨ansClauseE co[i.toNat].1, .lam⟩ a (bindK R) (clauseAt_ansHV hi)
        (by simp [bindK, Kont.HasHnd])
    rwa [hcell] at h
  refine ⟨(stFrame s).comp (.appR (.val ⟨ansClauseE co[i.toNat].1, .lam⟩) (.pairR a
    (.appR (.val (Val.lam (kappaCBody aff (ansHV n ts co) (bindK R)))) .hole))), ?_,
    fun ℓ => ?_⟩
  · rw [Kont.plug_comp]
    exact Quiet.head (stFrame s) hh rfl rfl
  refine ⟨(stFrame s').comp (Kont.appL (Kont.seq .hole (kResV (ansHV n ts co) (bindK R))) b),
    ?_, ?_⟩
  · rw [Kont.plug_comp, Kont.plug_comp]
    have hb₀ := Quiet.head (ℍ := ℍ) (.appR (.val ⟨ansClauseE co[i.toNat].1, .lam⟩) (.pairR a .hole))
      (fun μ => Head.beta μ (kappaCBody aff (ansHV n ts co) (bindK R)) (Val.loc ℓ)) rfl rfl
    rw [kappaCBody_subst] at hb₀
    refine (hb₀.plug (stFrame s)).trans ?_
    have hκ := closedAt_kappaC aff ℓ hH hRk
    refine (quiet_ansClause hi hc _ (isVal_kappaC aff ℓ (ansHV n ts co) (bindK R)) hκ hs ha hs'
      hb hq).trans ?_
    exact (kappaC_resume_parts aff ℓ (ansHV n ts co) (bindK R) b).1.plug (stFrame s')
  · rw [Kont.plug_comp]
    refine ((kappaC_resume_parts aff ℓ (ansHV n ts co) (bindK R) b).2.plug (stFrame s')).trans ?_
    have h₁₂ := quiet_beta (ℍ := ℍ)
      ((stFrame s').comp (.appR (.app (.prim .hnd) (ansHV n ts co).1) .hole)) R b
    simp only [Kont.plug_comp] at h₁₂
    exact h₁₂

/-- **One operation, caught by the answering handler, calmly**: quietly when its `κ` owns no cell,
around the cell when it does. -/
theorem calm_opStep {n i : UInt32} {ts : List Qual} {co : List OVal}
    (hco : ∀ c ∈ co, closedAt 0 c.1 = true) (hi : i.toNat < co.length) {s a s' b : Val}
    (hs : closedAt 0 s.1 = true) (ha : closedAt 0 a.1 = true) (hs' : closedAt 0 s'.1 = true)
    (hb : closedAt 0 b.1 = true)
    (hq : Quiet (ℍ := ℍ) (.app co[i.toNat].1 (Val.pair s a).1) (.val (Val.pair s' b)))
    {R : Expr} (hR : closedAt 1 R = true) :
    Calm (ℍ := ℍ)
      ((stFrame s).plug (hndE (ansHV n ts co) (bindE (performE (.val (opPayload n i a))) R)))
      ((stFrame s').plug (hndE (ansHV n ts co) (R.subst 0 b))) := by
  by_cases h0 : capTag (qualsVal ts).1 i.toNat = 0
  · exact (cellQuiet_opStep false hco hi hs ha hs' hb hq hR (by rw [kappaAt, if_pos h0])).calm
  by_cases h1 : capTag (qualsVal ts).1 i.toNat = 1
  · exact (cellQuiet_opStep true hco hi hs ha hs' hb hq hR
      (by rw [kappaAt, if_neg h0, if_pos h1])).calm
  exact (quiet_opStep hco hi hs ha hs' hb hq hR (by rw [kappaAt, if_neg h0, if_neg h1])).calm


/-- **The co-operations' run of a computation**, from its `j`-th step, at the parameters `vs`,
the answers so far `rs` (the latest first) and the state `s`: each step's co-operation runs
quietly from the state and the argument to the next state and the answer; it ends at the final
state `sn` and the continuation's argument `fv`. -/
inductive CoRun (co : List OVal) (vs : List Val) (fin : VExpr) :
    List (ℕ × VExpr) → List Val → Val → Val → Val → Prop
  | nil {rs : List Val} {s : Val} : CoRun co vs fin [] rs s s (VExpr.eval vs rs fin)
  | cons {i : ℕ} {a : VExpr} {rest : List (ℕ × VExpr)} {rs : List Val} {s s' b sn fv : Val}
      (hi : i < co.length)
      (hq : Quiet (ℍ := ℍ) (.app co[i].1 (Val.pair s (VExpr.eval vs rs a)).1) (.val (Val.pair s' b)))
      (hs' : closedAt 0 s'.1 = true) (hb : closedAt 0 b.1 = true)
      (h : CoRun co vs fin rest (b :: rs) s' sn fv) : CoRun co vs fin ((i, a) :: rest) rs s sn fv

theorem psub_closed_of {γ : List Val} (hγ : ∀ v ∈ γ, closedAt 0 v.1 = true) :
    ∀ (e : Expr) (k : ℕ), closedAt (k + γ.length) e = true → closedAt k (Expr.psub k γ e) = true
  | .var i, k, h => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.psub]
      split
      · simp [closedAt]; omega
      · split
        · rename_i v hv
          rw [val_shift_closed (hγ v (List.mem_of_getElem? hv))]
          exact closedAt_mono _ (hγ v (List.mem_of_getElem? hv)) (Nat.zero_le _)
        · rename_i hn
          simp only [closedAt, decide_eq_true_eq]
          have : γ.length ≤ i - k := by
            by_contra hc
            rw [List.getElem?_eq_getElem (not_le.mp hc)] at hn; cases hn
          omega
  | .unit, _, _ => rfl
  | .pair a b, k, h => by
      simp only [closedAt, Bool.and_eq_true, Expr.psub] at h ⊢
      exact ⟨psub_closed_of hγ a k h.1, psub_closed_of hγ b k h.2⟩
  | .inj₁ a, k, h => psub_closed_of hγ a k h
  | .inj₂ a, k, h => psub_closed_of hγ a k h
  | .lam b, k, h => by
      simp only [closedAt, Expr.psub] at h ⊢
      exact psub_closed_of hγ b (k + 1) (by rwa [Nat.add_right_comm])
  | .loc _, _, _ => rfl
  | .prim _, _, _ => rfl
  | .seq a b, k, h => by
      simp only [closedAt, Bool.and_eq_true, Expr.psub] at h ⊢
      exact ⟨psub_closed_of hγ a k h.1, psub_closed_of hγ b k h.2⟩
  | .letpair a b, k, h => by
      simp only [closedAt, Bool.and_eq_true, Expr.psub] at h ⊢
      exact ⟨psub_closed_of hγ a k h.1, psub_closed_of hγ b (k + 2) (by
        have := h.2; rwa [show k + γ.length + 2 = k + 2 + γ.length by omega] at this)⟩
  | .case a b c, k, h => by
      simp only [closedAt, Bool.and_eq_true, Expr.psub] at h ⊢
      exact ⟨⟨psub_closed_of hγ a k h.1.1, psub_closed_of hγ b (k + 1) (by
        have := h.1.2; rwa [show k + γ.length + 1 = k + 1 + γ.length by omega] at this)⟩,
        psub_closed_of hγ c (k + 1) (by
          have := h.2; rwa [show k + γ.length + 1 = k + 1 + γ.length by omega] at this)⟩
  | .app a b, k, h => by
      simp only [closedAt, Bool.and_eq_true, Expr.psub] at h ⊢
      exact ⟨psub_closed_of hγ a k h.1, psub_closed_of hγ b k h.2⟩


theorem vAt_closedAt {np : ℕ} : ∀ {j : ℕ} (a : VExpr), VExpr.WF np j a →
    closedAt (j + np + 1) ((ourInst (ℍ := ℍ) RF Ξ J).vAt j a).1 = true
  | j, .param p, h => by
      show closedAt _ (.var (j + p)) = true
      have : p < np := h
      simp only [closedAt, decide_eq_true_eq]; omega
  | j, .res r, h => by
      show closedAt _ (.var (j - 1 - r)) = true
      have : r < j := h
      simp only [closedAt, decide_eq_true_eq]; omega
  | _, .unit, _ => rfl
  | j, .pair a b, h => by
      show closedAt _ (.pair _ _) = true
      simp only [closedAt, Bool.and_eq_true]
      exact ⟨vAt_closedAt a h.1, vAt_closedAt b h.2⟩
  | j, .inl a, h => vAt_closedAt (j := j) a h
  | j, .inr a, h => vAt_closedAt (j := j) a h

theorem slFrom_closedAt {l : (RF.alg Ξ).Lab} {np nops : ℕ} {fin : VExpr} (hn : nops ≤ 2 ^ 32) :
    ∀ (rest : List (ℕ × VExpr)) (j : ℕ), SLComp.WFFrom np fin nops rest j →
      closedAt (j + np + 1) ((ourInst (ℍ := ℍ) RF Ξ J).slFrom l np fin rest j) = true
  | [], j, h => by
      have hv := vAt_closedAt (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) fin h
      show closedAt _ (appE (.var (j + np)) _) = true
      have e : (Expr.var (j + np)).shift 1 0 = .var (j + np + 1) := by simp [Expr.shift]
      simp only [appE, e, closedAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by omega, by omega⟩, hv⟩
  | (i, a) :: rest, j, ⟨hi, ha, hr⟩ => by
      have hv := vAt_closedAt (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) a ha
      have ih := slFrom_closedAt (l := l) hn rest (j + 1) hr
      show closedAt _ (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i _) _) = true
      erw [perform_eq _ (by omega)]
      simp only [bindE, performE, opArgE, closedAt, Expr.val, Val.lam, Val.prim, Val.i32,
        Bool.and_eq_true, Bool.true_and]
      exact ⟨by rwa [show j + np + 1 + 1 = j + 1 + np + 1 by omega], hv⟩

theorem slFrom_cons_subst {l : (RF.alg Ξ).Lab} {np : ℕ} {fin : VExpr} {i : ℕ} {a : VExpr}
    {rest : List (ℕ × VExpr)} {j : ℕ} (env : List Val) (hi : i < 2 ^ 32) :
    substAll env ((ourInst (ℍ := ℍ) RF Ξ J).slFrom l np fin ((i, a) :: rest) j) =
      bindE (performE (opArgE (RF.name Ξ l) (UInt32.ofNat i)
          (substAll env ((ourInst (ℍ := ℍ) RF Ξ J).vAt j a).1)))
        (Expr.psub 1 env ((ourInst (ℍ := ℍ) RF Ξ J).slFrom l np fin rest (j + 1))) := by
  show Expr.psub 0 env (bindE ((ourInst (ℍ := ℍ) RF Ξ J).perform l i _) _) = _
  erw [perform_eq _ hi]
  rfl

theorem slFrom_nil_subst {l : (RF.alg Ξ).Lab} {np : ℕ} {fin : VExpr} {j : ℕ} {env : List Val}
    {k : Val} (hk : env[j + np]? = some k) (hkc : closedAt 0 k.1 = true) :
    substAll env ((ourInst (ℍ := ℍ) RF Ξ J).slFrom l np fin [] j) =
      appE k.1 (substAll env ((ourInst (ℍ := ℍ) RF Ξ J).vAt j fin).1) := by
  show Expr.psub 0 env (appE (.var (j + np)) _) = _
  simp only [appE, Expr.psub, Expr.shift, if_neg (show ¬ j + np < 0 by omega)]
  have : ¬ (j + np + 1 < 0 + 1) := by omega
  simp only [if_neg this, Nat.zero_add, show j + np + 1 - 1 = j + np by omega, hk]
  simp [Val.val_shift, shift_closed0 hkc]
  rfl

/-- **The fold**: a straight-line computation handled by `ansHnd co` at the state `s` runs
calmly, as the co-operations run on the threaded state, to the continuation applied to the last
value, the closing frame at the final state. -/
theorem calm_fold {l : (RF.alg Ξ).Lab} {co : List OVal} (hco : ∀ c ∈ co, closedAt 0 c.1 = true)
    (hlen : co.length ≤ 2 ^ 32) {vs : List Val} {k : Val} (hvs : ∀ v ∈ vs, closedAt 0 v.1 = true)
    (hk : closedAt 0 k.1 = true) {fin : VExpr} :
    ∀ {rest : List (ℕ × VExpr)} {rs : List Val} {s sn fv : Val},
      CoRun (ℍ := ℍ) co vs fin rest rs s sn fv → (∀ v ∈ rs, closedAt 0 v.1 = true) →
      closedAt 0 s.1 = true → SLComp.WFFrom vs.length fin co.length rest rs.length →
      Calm (ℍ := ℍ)
        ((stFrame s).plug (hndE (ansHV (RF.name Ξ l) ((Ξ (RF.name Ξ l)).map Prod.fst) co)
          (substAll (rs ++ vs ++ [k])
            ((ourInst (ℍ := ℍ) RF Ξ J).slFrom l vs.length fin rest rs.length))))
        ((stFrame sn).plug (hndE (ansHV (RF.name Ξ l) ((Ξ (RF.name Ξ l)).map Prod.fst) co)
          (appE k.1 fv.1)))
  | _, rs, s, _, _, .nil, _, _, hwf => by
      have hkj : (rs ++ vs ++ [k])[rs.length + vs.length]? = some k := by
        rw [List.append_assoc, List.getElem?_append_right (by omega),
          show rs.length + vs.length - rs.length = vs.length by omega,
          List.getElem?_append_right (le_refl _)]
        simp
      rw [slFrom_nil_subst hkj hk, vAt_subst fin hwf]
      exact Calm.refl _
  | _, rs, s, _, _, @CoRun.cons _ _ _ _ _ i a rest _ _ s' b sn fv hi hq hs' hb h, hrs, hs,
      ⟨hi', ha, hwf⟩ => by
      have hi32 : i < 2 ^ 32 := by omega
      have henv : ∀ v ∈ rs ++ vs ++ [k], closedAt 0 v.1 = true := by
        intro v hv
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with (hv | hv) | rfl
        · exact hrs v hv
        · exact hvs v hv
        · exact hk
      have hev := closedAt_eval hvs hrs a
      rw [slFrom_cons_subst _ hi32, vAt_subst a ha]
      have hR : closedAt 1 (Expr.psub 1 (rs ++ vs ++ [k])
          ((ourInst (ℍ := ℍ) RF Ξ J).slFrom l vs.length fin rest (rs.length + 1))) = true := by
        refine psub_closed_of henv _ 1 ?_
        have := slFrom_closedAt (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) (l := l) hlen rest
          (rs.length + 1) hwf
        simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
        rwa [show 1 + (rs.length + vs.length + (0 + 1)) = rs.length + 1 + vs.length + 1 by omega]
      have hi'' : (UInt32.ofNat i).toNat = i := UInt32.toNat_ofNat_of_lt' hi32
      have hq' : Quiet (ℍ := ℍ) (.app co[(UInt32.ofNat i).toNat].1
          (Val.pair s (VExpr.eval vs rs a)).1) (.val (Val.pair s' b)) := by
        simp only [hi'']; exact hq
      have hstep := calm_opStep (ℍ := ℍ) (n := RF.name Ξ l) (i := UInt32.ofNat i)
        (ts := (Ξ (RF.name Ξ l)).map Prod.fst) hco (by rw [hi'']; exact hi) hs hev hs' hb hq' hR
      refine (show Calm (ℍ := ℍ) _ _ from hstep).trans ?_
      erw [← substAll_cons_eq]
      exact calm_fold hco hlen hvs hk h (fun v hv => by
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hb
        · exact hrs v hv) hs' hwf

/-- **The co-run's environment** after the answers `rs` (the latest first) at the state `s`:
each answer at three times its distance from the latest, the state at `coState`, the parameters
past the start state, every value closed. -/
def CoEnv (envC rs : List Val) (s : Val) (vs : List Val) : Prop :=
  (∀ v ∈ envC, closedAt 0 v.1 = true) ∧
  (∀ r < rs.length, envC[3 * (rs.length - 1 - r)]? = some (rs.getD (rs.length - 1 - r) Val.unit)) ∧
  envC[A.EffectSystem.coState rs.length]? = some s ∧
  ∀ p < vs.length, envC[3 * rs.length + 1 + p]? = some (vs.getD p Val.unit)

theorem coEnv_init {s : Val} {vs : List Val} (hs : closedAt 0 s.1 = true)
    (hvs : ∀ v ∈ vs, closedAt 0 v.1 = true) : CoEnv (s :: vs) [] s vs := by
  refine ⟨fun v hv => ?_, fun r hr => absurd hr (by simp), rfl, fun p hp => ?_⟩
  · rcases List.mem_cons.1 hv with rfl | hv
    · exact hs
    · exact hvs v hv
  · simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
    rw [show 1 + p = p + 1 by omega, List.getElem?_cons_succ, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hp]
    rfl

theorem coEnv_step {envC rs : List Val} {s s' b : Val} {vs : List Val}
    (h : CoEnv envC rs s vs) (hs' : closedAt 0 s'.1 = true) (hb : closedAt 0 b.1 = true) :
    CoEnv (b :: s' :: Val.pair s' b :: envC) (b :: rs) s' vs := by
  obtain ⟨hcl, hres, -, hpar⟩ := h
  refine ⟨fun v hv => ?_, fun r hr => ?_, rfl, fun p hp => ?_⟩
  · simp only [List.mem_cons] at hv
    rcases hv with rfl | rfl | rfl | hv
    · exact hb
    · exact hs'
    · simp only [Val.pair, closedAt, Bool.and_eq_true]; exact ⟨hs', hb⟩
    · exact hcl v hv
  · simp only [List.length_cons] at hr ⊢
    by_cases hr0 : r = rs.length
    · subst hr0
      simp
    · have hr' : r < rs.length := by omega
      have := hres r hr'
      rw [show 3 * (rs.length + 1 - 1 - r) = 3 * (rs.length - 1 - r) + 3 by omega]
      simp only [List.getElem?_cons_succ]
      rw [this, show rs.length + 1 - 1 - r = (rs.length - 1 - r) + 1 by omega]
      simp
  · simp only [List.length_cons]
    rw [show 3 * (rs.length + 1) + 1 + p = 3 * rs.length + 1 + p + 3 by omega]
    simp only [List.getElem?_cons_succ]
    exact hpar p hp

theorem vAtCo_subst {envC rs : List Val} {s : Val} {vs : List Val} (h : CoEnv envC rs s vs) :
    ∀ a : VExpr, VExpr.WF vs.length rs.length a →
      substAll envC ((ourInst (ℍ := ℍ) RF Ξ J).vAtCo rs.length a).1 = (VExpr.eval vs rs a).1
  | .param p, hp => substAll_var_some (h.2.2.2 p hp)
  | .res r, hr => substAll_var_some (h.2.1 r hr)
  | .unit, _ => rfl
  | .pair a b, hab => by
      show Expr.psub 0 _ (.pair _ _) = _
      simp only [Expr.psub]
      exact congrArg₂ Expr.pair (vAtCo_subst h a hab.1) (vAtCo_subst h b hab.2)
  | .inl a, ha => by
      show Expr.psub 0 _ (.inj₁ _) = _
      simp only [Expr.psub]
      exact congrArg Expr.inj₁ (vAtCo_subst h a ha)
  | .inr a, ha => by
      show Expr.psub 0 _ (.inj₂ _) = _
      simp only [Expr.psub]
      exact congrArg Expr.inj₂ (vAtCo_subst h a ha)

/-- A `letpair` of a bound pair, in the co-run's layout: the answer, the new state and the pair
put for the split's and the bind's variables. -/
theorem letpair_psub (q b s' : Val) (envC : List Val) (X : Expr) :
    Expr.psub 0 (b :: s' :: q :: envC) X =
      Expr.subst 0 s' (Expr.subst 0 (Val.shift 1 0 b)
        (Expr.subst 2 (Val.shift 2 0 q) (Expr.psub 3 envC X))) := by
  rw [Expr.psub_cons₂ 0 b s' (q :: envC) X, Expr.psub_cons 2 q envC X, Val.shift_zero]

/-- **The co-run**: the co-operations' own run of a computation, in its environment, reaches the
final state and the continuation's argument quietly. -/
theorem quiet_coFrom {co : List OVal} (hco : ∀ c ∈ co, closedAt 0 c.1 = true) {vs : List Val}
    {fin : VExpr} :
    ∀ {rest : List (ℕ × VExpr)} {rs : List Val} {s sn fv : Val} {envC : List Val},
      CoRun (ℍ := ℍ) co vs fin rest rs s sn fv → CoEnv envC rs s vs →
      SLComp.WFFrom vs.length fin co.length rest rs.length →
      Quiet (ℍ := ℍ) (substAll envC ((ourInst (ℍ := ℍ) RF Ξ J).coFrom
          co fin rest rs.length)) (.val (Val.pair sn fv))
  | _, rs, s, _, _, envC, .nil, hE, hwf => by
      have hst : Expr.psub 0 envC ((ourInst (ℍ := ℍ) RF Ξ J).var
          (A.EffectSystem.coState rs.length)).1 = s.1 :=
        substAll_var_some hE.2.2.1
      have hv : Expr.psub 0 envC ((ourInst (ℍ := ℍ) RF Ξ J).vAtCo rs.length fin).1 =
          (VExpr.eval vs rs fin).1 := vAtCo_subst hE fin hwf
      show Quiet (ℍ := ℍ) (Expr.psub 0 envC (.pair _ _)) _
      simp only [Expr.psub]
      rw [hst, hv]
      exact Quiet.refl _
  | _, rs, s, _, _, envC, @CoRun.cons _ _ _ _ _ i a rest _ _ s' b sn fv hi hq hs' hb h, hE,
      ⟨hi', ha, hwf⟩ => by
      have hc : closedAt 0 co[i].1 = true := hco _ (List.getElem_mem hi)
      have hst : Expr.psub 0 envC ((ourInst (ℍ := ℍ) RF Ξ J).var
          (A.EffectSystem.coState rs.length)).1 = s.1 :=
        substAll_var_some hE.2.2.1
      have hva : Expr.psub 0 envC ((ourInst (ℍ := ℍ) RF Ξ J).vAtCo rs.length a).1 =
          (VExpr.eval vs rs a).1 := vAtCo_subst hE a ha
      have hcoi : co.getD i (ourInst (ℍ := ℍ) RF Ξ J).unitV = co[i] := by
        show List.getD (α := OVal) co i ⟨.unit, .unit⟩ = co[i]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
      -- the call, its answer bound and split
      have e₀ : substAll envC ((ourInst (ℍ := ℍ) RF Ξ J).coFrom co fin ((i, a) :: rest)
          rs.length) =
          bindE (appE co[i].1 (Val.pair s (VExpr.eval vs rs a)).1)
            (.letpair (.var 0) (Expr.psub 3 envC
              ((ourInst (ℍ := ℍ) RF Ξ J).coFrom co fin rest (rs.length + 1)))) := by
        show Expr.psub 0 envC (bindE (appE (co.getD i _).1 (.pair _ _))
          (.letpair (.var 0) _)) = _
        rw [hcoi]
        simp only [bindE, appE, Expr.psub, Expr.val, Val.lam, Val.pair]
        rw [hst, hva]
        rw [psub_closedAt _ envC (show closedAt 1 (co[i].1.shift 1 0) = true by
          rw [shift_closed0 hc]; exact closedAt_mono _ hc (by omega)) (le_refl _)]
        simp
      rw [e₀]
      have h₁ := ((quiet_appE (ℍ := ℍ) .hole co[i].1 (Val.pair s (VExpr.eval vs rs a))).trans
        hq).plug (bindK (.letpair (.var 0) (Expr.psub 3 envC
          ((ourInst (ℍ := ℍ) RF Ξ J).coFrom co fin rest (rs.length + 1)))))
      refine h₁.trans ?_
      have h₂ := quiet_beta (ℍ := ℍ) .hole (.letpair (.var 0) (Expr.psub 3 envC
        ((ourInst (ℍ := ℍ) RF Ξ J).coFrom co fin rest (rs.length + 1)))) (Val.pair s' b)
      refine h₂.trans ?_
      have h₃ := quiet_letpair (ℍ := ℍ) .hole s' b
        ((Expr.psub 3 envC ((ourInst (ℍ := ℍ) RF Ξ J).coFrom co fin rest
          (rs.length + 1))).subst 2 ((Val.pair s' b).shift 2 0))
      have e₃ : ((((Expr.psub 3 envC ((ourInst (ℍ := ℍ) RF Ξ J).coFrom co fin rest
          (rs.length + 1))).subst 2 ((Val.pair s' b).shift 2 0)).subst 0 (b.shift 1 0)).subst 0 s') =
          substAll (b :: s' :: Val.pair s' b :: envC)
            ((ourInst (ℍ := ℍ) RF Ξ J).coFrom co fin rest (rs.length + 1)) := by
        exact (letpair_psub _ _ _ _ _).symm
      simp only [Kont.plug, Expr.subst] at h₃ ⊢
      rw [e₃] at h₃
      refine h₃.trans ?_
      have := quiet_coFrom hco h (coEnv_step hE hs' hb) hwf
      simpa using this


/-! ### Co-operations that run quietly, and the comodel reduction -/

/-- **Co-operations that run quietly**: closed, and each, at a closed state and a closed argument,
runs quietly to a pair of closed values.  The scope of the reduction below: co-operations that
allocate or show events would make the two sides of an equation differ in their memories or
traces. -/
def PureCo (co : List OVal) : Prop :=
  (∀ c ∈ co, closedAt 0 c.1 = true) ∧
    ∀ i (hi : i < co.length) (s a : Val), closedAt 0 s.1 = true → closedAt 0 a.1 = true →
      ∃ s' b : Val, closedAt 0 s'.1 = true ∧ closedAt 0 b.1 = true ∧
        Quiet (ℍ := ℍ) (.app co[i].1 (Val.pair s a).1) (.val (Val.pair s' b))

theorem coRun_exists {co : List OVal} (hP : PureCo (ℍ := ℍ) co) {vs : List Val}
    (hvs : ∀ v ∈ vs, closedAt 0 v.1 = true) {fin : VExpr} :
    ∀ (rest : List (ℕ × VExpr)) (rs : List Val) (s : Val), (∀ v ∈ rs, closedAt 0 v.1 = true) →
      closedAt 0 s.1 = true → SLComp.WFFrom vs.length fin co.length rest rs.length →
      ∃ sn fv, CoRun (ℍ := ℍ) co vs fin rest rs s sn fv
  | [], rs, s, _, _, _ => ⟨s, _, .nil⟩
  | (i, a) :: rest, rs, s, hrs, hs, ⟨hi, _, hwf⟩ => by
      obtain ⟨s', b, hs', hb, hq⟩ := hP.2 i hi s (VExpr.eval vs rs a) hs (closedAt_eval hvs hrs a)
      obtain ⟨sn, fv, h⟩ := coRun_exists hP hvs rest (b :: rs) s' (fun v hv => by
        rcases List.mem_cons.1 hv with rfl | hv
        · exact hb
        · exact hrs v hv) hs' hwf
      exact ⟨sn, fv, .cons hi hq hs' hb h⟩

/-- A closed A-value is a Core value. -/
theorem oval_of_closed (v : OVal) (h : closedAt 0 v.1 = true) :
    ∃ w : Val, v = OVal.ofVal w ∧ closedAt 0 w.1 = true :=
  ⟨⟨v.1, isVal_of_closed_oval v.2 h⟩, Subtype.ext rfl, h⟩

theorem ovals_of_closed : ∀ (vs : List OVal), (∀ v ∈ vs, closedAt 0 v.1 = true) →
    ∃ ws : List Val, vs = ws.map OVal.ofVal ∧ ∀ w ∈ ws, closedAt 0 w.1 = true
  | [], _ => ⟨[], rfl, fun _ h => absurd h List.not_mem_nil⟩
  | v :: vs, h => by
      obtain ⟨w, rfl, hw⟩ := oval_of_closed v (h v List.mem_cons_self)
      obtain ⟨ws, rfl, hws⟩ := ovals_of_closed vs (fun v' hv' => h v' (List.mem_cons_of_mem _ hv'))
      exact ⟨w :: ws, rfl, fun w' hw' => by
        rcases List.mem_cons.1 hw' with rfl | hw'
        · exact hw
        · exact hws w' hw'⟩

theorem lets_append_one (vs : List (ourInst (ℍ := ℍ) RF Ξ J).Val) (k : (ourInst (ℍ := ℍ) RF Ξ J).Val)
    (X : Expr) :
    (ourInst (ℍ := ℍ) RF Ξ J).lets (vs ++ [k]) X =
      bindE k.1 ((ourInst (ℍ := ℍ) RF Ξ J).lets vs X) := by
  induction vs generalizing X with
  | nil => rfl
  | cons v vs ih => exact ih _

theorem clauses_eq : ∀ co : List OVal,
    (co.map (ourInst (ℍ := ℍ) RF Ξ J).ansClause).map Subtype.val = co.map fun c => ansClauseE c.1
  | [] => rfl
  | _ :: cs => congrArg (List.cons _) (clauses_eq cs)

/-- The answering handler, as our instance installs it, is the frame of `ansHV`, at the tags of
its label's operations. -/
theorem runAt_eq (l : (RF.alg Ξ).Lab) (co : List OVal) (s₀ : Val) (M : Expr) :
    (ourInst (ℍ := ℍ) RF Ξ J).runAt l co (OVal.ofVal s₀) M =
      (stFrame s₀).plug (hndE (ansHV (RF.name Ξ l) ((Ξ (RF.name Ξ l)).map Prod.fst) co) M) := by
  have h := clauses_eq (ℍ := ℍ) (RF := RF) (Ξ := Ξ) (J := J) co
  show bindE (Expr.app (.app (.prim .hnd) (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) ansRetE
      ((co.map (ourInst (ℍ := ℍ) RF Ξ J).ansClause).map Subtype.val))) M) (appE (.var 0) s₀.1) =
    bindE (Expr.app (.app (.prim .hnd) (hndValE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) ansRetE
      (co.map fun c => ansClauseE c.1))) M) (appE (.var 0) s₀.1)
  rw [h]

/-- A RunsTo's answer at a configuration with a quiet run to a value is that value. -/
theorem runsTo_val {e : Expr} {v : Val} (h : Quiet (ℍ := ℍ) e (.val v)) {w : OVal}
    {tr : List (ourInst (ℍ := ℍ) RF Ξ J).Event}
    (hR : (ourInst (ℍ := ℍ) RF Ξ J).RunsTo (ourInst (ℍ := ℍ) RF Ξ J).R₀ e w tr) : w.1 = v.1 := by
  obtain ⟨q, hc, -⟩ := h
  have hobs := obsFrom_of_chain (J := J) (ourInst (ℍ := ℍ) RF Ξ J).R₀ (μ := Adequacy.emptyMem)
    (s := ()) hc v.2
  obtain ⟨q', hq', hv', -⟩ := hobs
  have := (hR.2 q' hq').1
  exact (hv'.symm.trans this).symm

/-- **Each side of an equation, handled from the state, runs calmly through the fold**: the
parameters and the continuation are bound, and the straight-line computation is folded as the
co-operations run (`calm_fold`), to the continuation applied to the last value under the closing
frame at the final state. -/
theorem calm_side {l : (RF.alg Ξ).Lab} {co : List OVal} (hco : ∀ c ∈ co, closedAt 0 c.1 = true)
    (hlen : co.length ≤ 2 ^ 32) {vsV : List Val} {kV s₀V : Val}
    (hvsV : ∀ v ∈ vsV, closedAt 0 v.1 = true) (hkV : closedAt 0 kV.1 = true)
    (hs₀V : closedAt 0 s₀V.1 = true) {np : ℕ} (hnp : vsV.length = np) {c : SLComp} {sn fv : Val}
    (hc : CoRun (ℍ := ℍ) co vsV c.fin c.steps [] s₀V sn fv)
    (hw : SLComp.WFFrom vsV.length c.fin co.length c.steps 0) :
    Calm (ℍ := ℍ) ((ourInst (ℍ := ℍ) RF Ξ J).runAt l co (OVal.ofVal s₀V)
        ((ourInst (ℍ := ℍ) RF Ξ J).lets (vsV.map OVal.ofVal ++ [OVal.ofVal kV])
          ((ourInst (ℍ := ℍ) RF Ξ J).slTerm l np c)))
      ((stFrame sn).plug (hndE (ansHV (RF.name Ξ l) ((Ξ (RF.name Ξ l)).map Prod.fst) co)
        (appE kV.1 fv.1))) := by
  have hvk : ∀ v ∈ vsV ++ [kV], closedAt 0 v.1 = true := by
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact hvsV v hv
    · rw [List.mem_singleton.1 hv]; exact hkV
  erw [runAt_eq, show vsV.map OVal.ofVal ++ [OVal.ofVal kV] = (vsV ++ [kV]).map OVal.ofVal by simp]
  have h₁ := (quiet_lets (Ξ := Ξ) (J := J) (vsV ++ [kV]) hvk
    ((ourInst (ℍ := ℍ) RF Ξ J).slTerm l np c)).plug
    ((stFrame s₀V).comp (.appR (.app (.prim .hnd)
      (ansHV (RF.name Ξ l) ((Ξ (RF.name Ξ l)).map Prod.fst) co).1) .hole))
  simp only [Kont.plug_comp] at h₁
  refine (show Quiet (ℍ := ℍ) _ _ from h₁).calm.trans ?_
  have h₂ := calm_fold (J := J) (l := l) hco hlen hvsV hkV hc
    (fun _ h => absurd h List.not_mem_nil) hs₀V hw
  rw [← hnp]
  exact h₂

/-- **D1.h4 (c): a comodel's handler is correct.**  At a typing system whose reached
configurations are closed and whose typed closed values are closed, co-operations that run
quietly (`PureCo`) and validate a theory's well-formed equations on the carrier (`IsComodel`)
give a handler that is correct for it (`AnsCorrect`): the two sides of each equation, handled and
run from the state, reach one configuration calmly (`calm_fold`), since the co-runs, which reach
the same answer, are their operations' co-operation runs. -/
theorem ansCorrect_of_comodel (hL : LiveOK (ℍ := ℍ) RF Ξ J)
    (hJV : ∀ (v : OVal) (T : OVTy), (ourInst (ℍ := ℍ) RF Ξ J).derV [] v T → closedAt 0 v.1 = true)
    {th : (ourInst (ℍ := ℍ) RF Ξ J).Theory} {l : (RF.alg Ξ).Lab} {co : List OVal} {T : OVTy}
    (hP : PureCo (ℍ := ℍ) co) (hlen : co.length ≤ 2 ^ 32)
    (hwf : ∀ eq ∈ th l, Eqn.WF co.length eq)
    (hC : (ourInst (ℍ := ℍ) RF Ξ J).IsComodel th l co T) :
    (ourInst (ℍ := ℍ) RF Ξ J).AnsCorrect th l co T := by
  intro eq heq vs k s₀ hs₀ hvs
  refine runsAlike_of_live_calm hL fun hcl => ?_
  obtain ⟨hwfL, hwfR⟩ := hwf eq heq
  have hlenv : vs.length = eq.params.length := hvs.length_eq
  -- the values are closed
  have hs₀c := hJV _ _ hs₀
  have hvsc : ∀ v ∈ vs, closedAt 0 v.1 = true := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    exact hJV _ _ (hvs.get hi (by rw [← hlenv]; exact hi))
  have hkc : closedAt 0 k.1 = true := by
    change closedAt 0 (bindE ((handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) ansRetE
      (((co.map (ourInst (ℍ := ℍ) RF Ξ J).ansClause)).map Subtype.val)).plug
      ((ourInst (ℍ := ℍ) RF Ξ J).lets (vs ++ [k]) _)) (appE (.var 0) s₀.1)) = true at hcl
    simp only [bindE, closedAt, Bool.and_eq_true] at hcl
    have h₁ := closedAt_plug_inv _ hcl.2
    erw [lets_append_one] at h₁
    simp only [bindE, closedAt, Bool.and_eq_true] at h₁
    exact h₁.2
  obtain ⟨s₀V, rfl, hs₀V⟩ := oval_of_closed s₀ hs₀c
  obtain ⟨kV, rfl, hkV⟩ := oval_of_closed k hkc
  obtain ⟨vsV, rfl, hvsV⟩ := ovals_of_closed vs hvsc
  have hlen' : vsV.length = eq.params.length := by
    have := hlenv; erw [List.length_map] at this; exact this
  rw [← hlen'] at hwfL hwfR
  -- the co-runs
  obtain ⟨snL, fvL, hcL⟩ := coRun_exists hP hvsV eq.lhs.steps [] s₀V
    (fun _ h => absurd h List.not_mem_nil) hs₀V hwfL
  obtain ⟨snR, fvR, hcR⟩ := coRun_exists hP hvsV eq.rhs.steps [] s₀V
    (fun _ h => absurd h List.not_mem_nil) hs₀V hwfR
  have hcl₀ : ∀ v ∈ s₀V :: vsV, closedAt 0 v.1 = true := by
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hs₀V
    · exact hvsV v hv
  have qL : Quiet (ℍ := ℍ) ((ourInst (ℍ := ℍ) RF Ξ J).lets ((s₀V :: vsV).map OVal.ofVal)
      ((ourInst (ℍ := ℍ) RF Ξ J).coRun co eq.lhs)) (.val (Val.pair snL fvL)) :=
    (quiet_lets (s₀V :: vsV) hcl₀ _).trans
      (quiet_coFrom (J := J) hP.1 hcL (coEnv_init hs₀V hvsV) hwfL)
  have qR : Quiet (ℍ := ℍ) ((ourInst (ℍ := ℍ) RF Ξ J).lets ((s₀V :: vsV).map OVal.ofVal)
      ((ourInst (ℍ := ℍ) RF Ξ J).coRun co eq.rhs)) (.val (Val.pair snR fvR)) :=
    (quiet_lets (s₀V :: vsV) hcl₀ _).trans
      (quiet_coFrom (J := J) hP.1 hcR (coEnv_init hs₀V hvsV) hwfR)
  -- the comodel: one final state and one continuation argument
  obtain ⟨w, hwL, hwR⟩ := hC eq heq (vsV.map OVal.ofVal) (OVal.ofVal s₀V) hs₀ hvs
  have eL := runsTo_val qL hwL
  have eR := runsTo_val qR hwR
  have hpair : Expr.pair snL.1 fvL.1 = Expr.pair snR.1 fvR.1 := eL.symm.trans eR
  simp only [Expr.pair.injEq] at hpair
  have hsn : snL = snR := Val.ext hpair.1
  have hfv : fvL = fvR := Val.ext hpair.2
  -- both sides reach the continuation at the last value, the closing frame at the final state
  have hvk : ∀ v ∈ vsV ++ [kV], closedAt 0 v.1 = true := by
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact hvsV v hv
    · rw [List.mem_singleton.1 hv]; exact hkV
  have hside : ∀ {c : SLComp} {sn fv : Val}, CoRun (ℍ := ℍ) co vsV c.fin c.steps [] s₀V sn fv →
      SLComp.WFFrom vsV.length c.fin co.length c.steps 0 →
      Calm (ℍ := ℍ) ((ourInst (ℍ := ℍ) RF Ξ J).runAt l co (OVal.ofVal s₀V)
          ((ourInst (ℍ := ℍ) RF Ξ J).lets (vsV.map OVal.ofVal ++ [OVal.ofVal kV])
            ((ourInst (ℍ := ℍ) RF Ξ J).slTerm l eq.params.length c)))
        ((stFrame sn).plug (hndE (ansHV (RF.name Ξ l) ((Ξ (RF.name Ξ l)).map Prod.fst) co)
          (appE kV.1 fv.1))) := fun hc hw => calm_side hP.1 hlen hvsV hkV hs₀V hlen' hc hw
  exact ⟨_, hside hcL hwfL, by rw [hsn, hfv]; exact hside hcR hwfR⟩

end Subst

section State
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- The co-operations' runs at our instance: `get` from `(s, a)` answers `(s, s)`. -/
theorem quiet_getCo (s a : Val) :
    Quiet (ℍ := ℍ) (.app ((ourInst (ℍ := ℍ) RF Ξ J).getCo).1 (Val.pair s a).1) (.val (Val.pair s s)) := by
  have h₁ := quiet_beta (ℍ := ℍ) .hole (.letpair (.var 0) (.pair (.var 1) (.var 1))) (Val.pair s a)
  have h₂ := quiet_letpair (ℍ := ℍ) .hole s a (.pair (.var 1) (.var 1))
  simp only [Kont.plug, Expr.subst] at h₁ h₂
  refine h₁.trans ?_
  simpa [Expr.subst, Val.pair] using h₂

theorem quiet_putCo (s a : Val) :
    Quiet (ℍ := ℍ) (.app ((ourInst (ℍ := ℍ) RF Ξ J).putCo).1 (Val.pair s a).1) (.val (Val.pair a Val.unit)) := by
  have h₁ := quiet_beta (ℍ := ℍ) .hole (.letpair (.var 0) (.pair (.var 0) .unit)) (Val.pair s a)
  have h₂ := quiet_letpair (ℍ := ℍ) .hole s a (.pair (.var 0) .unit)
  simp only [Kont.plug, Expr.subst] at h₁ h₂
  refine h₁.trans ?_
  simp only [if_pos, Val.val_shift] at h₂
  rw [Expr.subst_shift 0 0 0 s a.1 (le_refl _) (le_refl _), Expr.shift_zero] at h₂
  exact h₂

theorem quiet_badPutCo (s a : Val) :
    Quiet (ℍ := ℍ) (.app ((ourInst (ℍ := ℍ) RF Ξ J).badPutCo).1 (Val.pair s a).1) (.val (Val.pair s Val.unit)) := by
  have h₁ := quiet_beta (ℍ := ℍ) .hole (.letpair (.var 0) (.pair (.var 1) .unit)) (Val.pair s a)
  have h₂ := quiet_letpair (ℍ := ℍ) .hole s a (.pair (.var 1) .unit)
  simp only [Kont.plug, Expr.subst] at h₁ h₂
  refine h₁.trans ?_
  simpa [Expr.subst, Val.pair, Val.shift, Val.unit] using h₂


theorem closedAt_getCo : closedAt 0 ((ourInst (ℍ := ℍ) RF Ξ J).getCo).1 = true := rfl
theorem closedAt_putCo : closedAt 0 ((ourInst (ℍ := ℍ) RF Ξ J).putCo).1 = true := rfl
theorem closedAt_badPutCo : closedAt 0 ((ourInst (ℍ := ℍ) RF Ξ J).badPutCo).1 = true := rfl

/-- **State's co-operations run quietly.** -/
theorem pureCo_stateCo : PureCo (ℍ := ℍ) (ourInst (ℍ := ℍ) RF Ξ J).stateCo := by
  refine ⟨fun c hc => ?_, fun i hi s a hs ha => ?_⟩
  · simp only [A.EffectSystem.stateCo] at hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact closedAt_getCo
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact closedAt_putCo
      · exact absurd hc List.not_mem_nil
  · have hi' : i < 2 := hi
    rcases i with _ | _ | i
    · exact ⟨s, s, hs, hs, quiet_getCo s a⟩
    · exact ⟨a, Val.unit, ha, rfl, quiet_putCo s a⟩
    · omega

theorem pureCo_badStateCo : PureCo (ℍ := ℍ) (ourInst (ℍ := ℍ) RF Ξ J).badStateCo := by
  refine ⟨fun c hc => ?_, fun i hi s a hs ha => ?_⟩
  · simp only [A.EffectSystem.badStateCo] at hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact closedAt_getCo
    · rcases List.mem_cons.1 hc with rfl | hc
      · exact closedAt_badPutCo
      · exact absurd hc List.not_mem_nil
  · have hi' : i < 2 := hi
    rcases i with _ | _ | i
    · exact ⟨s, s, hs, hs, quiet_getCo s a⟩
    · exact ⟨s, Val.unit, hs, rfl, quiet_badPutCo s a⟩
    · omega

/-- A configuration with a quiet run to a value runs to it, with no event. -/
theorem runsTo_of_quiet {e : Expr} {v : Val} (h : Quiet (ℍ := ℍ) e (.val v)) :
    (ourInst (ℍ := ℍ) RF Ξ J).RunsTo (ourInst (ℍ := ℍ) RF Ξ J).R₀ e (OVal.ofVal v) [] := by
  obtain ⟨q, hc, hf⟩ := h
  have hall : q.all (fun x => finHead x.2.1 == false) = true :=
    List.all_eq_true.2 fun x hx => by simp [hf x hx]
  have hobs := obs_chainPath (J := J) (ourInst (ℍ := ℍ) RF Ξ J).R₀ Adequacy.emptyMem () q hall
  refine ⟨?_, fun q' hq' => ?_⟩
  · have := obsFrom_of_chain (J := J) (ourInst (ℍ := ℍ) RF Ξ J).R₀ (μ := Adequacy.emptyMem) (s := ())
      hc v.2
    rw [hobs] at this
    exact this
  · have := complete_chain_eq (J := J) (ourInst (ℍ := ℍ) RF Ξ J).R₀ (μ := Adequacy.emptyMem)
      (s := ()) hc v.2 q' hq'
    subst this
    refine ⟨?_, hobs⟩
    have hl := lastC_chainPath (J := J) (ourInst (ℍ := ℍ) RF Ξ J).R₀ (μ := Adequacy.emptyMem)
      (s := ()) hc
    exact congrArg (fun x : (ourInst (ℍ := ℍ) RF Ξ J).RConf (ourInst (ℍ := ℍ) RF Ξ J).R₀ =>
      (ourInst (ℍ := ℍ) RF Ξ J).term x.1) hl

/-- **A comodel, from the co-operations' runs**: at a typing system whose typed closed values are
closed, co-operations that are closed and whose runs of the two sides of each equation, from
every closed state and parameters, reach one final state and continuation argument, are a
comodel. -/
theorem isComodel_of
    (hJV : ∀ (v : OVal) (T : OVTy), (ourInst (ℍ := ℍ) RF Ξ J).derV [] v T → closedAt 0 v.1 = true)
    {th : (ourInst (ℍ := ℍ) RF Ξ J).Theory} {l : (RF.alg Ξ).Lab} {co : List OVal} {T : OVTy}
    (hco : ∀ c ∈ co, closedAt 0 c.1 = true) (hwf : ∀ eq ∈ th l, Eqn.WF co.length eq)
    (h : ∀ eq ∈ th l, ∀ (vs : List Val) (s : Val), (∀ v ∈ vs, closedAt 0 v.1 = true) →
      closedAt 0 s.1 = true → vs.length = eq.params.length →
      ∃ sn fv, CoRun (ℍ := ℍ) co vs eq.lhs.fin eq.lhs.steps [] s sn fv ∧
        CoRun (ℍ := ℍ) co vs eq.rhs.fin eq.rhs.steps [] s sn fv) :
    (ourInst (ℍ := ℍ) RF Ξ J).IsComodel th l co T := by
  intro eq heq vs s hs hvs
  obtain ⟨hwfL, hwfR⟩ := hwf eq heq
  have hlenv : vs.length = eq.params.length := hvs.length_eq
  have hsc := hJV _ _ hs
  have hvsc : ∀ v ∈ vs, closedAt 0 v.1 = true := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    exact hJV _ _ (hvs.get hi (by rw [← hlenv]; exact hi))
  obtain ⟨sV, rfl, hsV⟩ := oval_of_closed s hsc
  obtain ⟨vsV, rfl, hvsV⟩ := ovals_of_closed vs hvsc
  have hlen' : vsV.length = eq.params.length := by
    have := hlenv; erw [List.length_map] at this; exact this
  rw [← hlen'] at hwfL hwfR
  obtain ⟨sn, fv, hcL, hcR⟩ := h eq heq vsV sV hvsV hsV hlen'
  have hcl₀ : ∀ v ∈ sV :: vsV, closedAt 0 v.1 = true := by
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact hsV
    · exact hvsV v hv
  refine ⟨OVal.ofVal (Val.pair sn fv), ?_, ?_⟩
  · exact runsTo_of_quiet ((quiet_lets (Ξ := Ξ) (J := J) (sV :: vsV) hcl₀ _).trans
      (quiet_coFrom (J := J) hco hcL (coEnv_init hsV hvsV) hwfL))
  · exact runsTo_of_quiet ((quiet_lets (Ξ := Ξ) (J := J) (sV :: vsV) hcl₀ _).trans
      (quiet_coFrom (J := J) hco hcR (coEnv_init hsV hvsV) hwfR))


theorem mem_stateTheory {T : OVTy} {l : (RF.alg Ξ).Lab} {eq : Eqn OVTy}
    (h : eq ∈ (ourInst (ℍ := ℍ) RF Ξ J).stateTheory T l) :
    eq = (ourInst (ℍ := ℍ) RF Ξ J).eqnGG ∨ eq = (ourInst (ℍ := ℍ) RF Ξ J).eqnGP ∨
      eq = (ourInst (ℍ := ℍ) RF Ξ J).eqnPP T ∨ eq = (ourInst (ℍ := ℍ) RF Ξ J).eqnPG T := by
  unfold A.EffectSystem.stateTheory at h
  split at h
  · simp only [A.EffectSystem.stateEqns] at h
    rcases List.mem_cons.1 h with h | h
    · exact .inl h
    rcases List.mem_cons.1 h with h | h
    · exact .inr (.inl h)
    rcases List.mem_cons.1 h with h | h
    · exact .inr (.inr (.inl h))
    rcases List.mem_cons.1 h with h | h
    · exact .inr (.inr (.inr h))
    · exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil

/-- The four laws are well formed at two operations. -/
theorem stateTheory_wf (T : OVTy) (l : (RF.alg Ξ).Lab) :
    ∀ eq ∈ (ourInst (ℍ := ℍ) RF Ξ J).stateTheory T l, Eqn.WF 2 eq := by
  intro eq h
  rcases mem_stateTheory h with rfl | rfl | rfl | rfl <;>
    simp [Eqn.WF, SLComp.WFFrom, VExpr.WF, A.EffectSystem.eqnGG, A.EffectSystem.eqnGP,
      A.EffectSystem.eqnPP, A.EffectSystem.eqnPG] <;>
    first
    | exact ⟨(by show 0 < 2; decide), (by show 1 < 2; decide)⟩
    | (show 0 < 1; decide)

/-- **`stateCo` is a comodel of the four laws of global state**, at every carrier, label, row
form, effect context and typing system whose typed closed values are closed. -/
theorem state_isComodel
    (hJV : ∀ (v : OVal) (T : OVTy), (ourInst (ℍ := ℍ) RF Ξ J).derV [] v T → closedAt 0 v.1 = true)
    (T : OVTy) (l : (RF.alg Ξ).Lab) :
    (ourInst (ℍ := ℍ) RF Ξ J).IsComodel ((ourInst (ℍ := ℍ) RF Ξ J).stateTheory T) l
      (ourInst (ℍ := ℍ) RF Ξ J).stateCo T := by
  refine isComodel_of hJV pureCo_stateCo.1 (stateTheory_wf T l) ?_
  intro eq heq vs s hvs hs hlen
  rcases mem_stateTheory heq with rfl | rfl | rfl | rfl
  · -- get; get at `(x, y)` is get at `(x, x)`
    match vs, hlen with
    | [], _ =>
      exact ⟨s, Val.pair s s,
        .cons (i := 0) (by show 0 < 2; decide) (quiet_getCo s _) hs hs
          (.cons (i := 0) (by show 0 < 2; decide) (quiet_getCo s _) hs hs .nil),
        .cons (i := 0) (by show 0 < 2; decide) (quiet_getCo s _) hs hs .nil⟩
  · -- get; put back is no operation
    match vs, hlen with
    | [], _ =>
      exact ⟨s, Val.unit,
        .cons (i := 0) (by show 0 < 2; decide) (quiet_getCo s _) hs hs
          (.cons (i := 1) (by show 1 < 2; decide) (quiet_putCo s _) hs rfl .nil),
        .nil⟩
  · -- put s; put t is put t
    match vs, hlen with
    | [t₁, t₂], _ =>
      have h₁ := hvs t₁ (by simp)
      have h₂ := hvs t₂ (by simp)
      exact ⟨t₂, Val.unit,
        .cons (i := 1) (by show 1 < 2; decide) (quiet_putCo s _) h₁ rfl
          (.cons (i := 1) (by show 1 < 2; decide) (quiet_putCo t₁ _) h₂ rfl .nil),
        .cons (i := 1) (by show 1 < 2; decide) (quiet_putCo s _) h₂ rfl .nil⟩
  · -- put s; get is put s, answering s
    match vs, hlen with
    | [t], _ =>
      have h₁ := hvs t (by simp)
      exact ⟨t, t,
        .cons (i := 1) (by show 1 < 2; decide) (quiet_putCo s _) h₁ rfl
          (.cons (i := 0) (by show 0 < 2; decide) (quiet_getCo t _) h₁ h₁ .nil),
        .cons (i := 1) (by show 1 < 2; decide) (quiet_putCo s _) h₁ rfl .nil⟩

/-- **The handler of global state is correct** (D1.h4 (b), (c)): at every carrier and label, at
every typing system whose reached configurations are closed and whose typed closed values are
closed, `ansHnd stateCo` validates the four laws, by the comodel reduction. -/
theorem state_correct (hL : LiveOK (ℍ := ℍ) RF Ξ J)
    (hJV : ∀ (v : OVal) (T : OVTy), (ourInst (ℍ := ℍ) RF Ξ J).derV [] v T → closedAt 0 v.1 = true)
    (T : OVTy) (l : (RF.alg Ξ).Lab) :
    (ourInst (ℍ := ℍ) RF Ξ J).AnsCorrect ((ourInst (ℍ := ℍ) RF Ξ J).stateTheory T) l
      (ourInst (ℍ := ℍ) RF Ξ J).stateCo T :=
  ansCorrect_of_comodel hL hJV pureCo_stateCo (by show 2 ≤ 2 ^ 32; decide) (stateTheory_wf T l)
    (state_isComodel hJV T l)

end State


/-! ### At `J₁` -/

section AtJ1
variable {Ξ : EffCtx}

/-- `J₁`'s typed closed values are closed: at the empty context `J₁` at `Ξ` is Core's kernel with
its inner rows tied. -/
theorem closed_of_derV_J₁ (v : OVal) (T : OVTy)
    (h : (ourInst (ℍ := ℍ) orowRF Ξ J₁).derV [] v T) : closedAt 0 v.1 = true := by
  obtain ⟨Θ, hΘ, -, -, hd⟩ := h
  have h' := hd _ (models_anyCon_nil hΘ) (envAt_nil Ξ) (fun _ => none)
    (closingAt_none (fun s hs => absurd hs List.not_mem_nil))
  rw [fillS_none] at h'
  simp only [J1CoreAt] at h'
  split at h'
  · rename_i hp
    obtain ⟨b, hb, -, hC⟩ := h'
    obtain ⟨C', hC'⟩ := OVTy.polyInstAt_nonempty Ξ hp (fun _ => [])
    have := closedAt_of_derives (hC C' hC').toCDerives
    rw [hb]; exact this
  · exact closedAt_of_derives h'.toCDerives

/-- **`stateCo` is a comodel at `J₁`.** -/
theorem state_isComodel_J₁ (T : OVTy) (l : (orowAlg Ξ).Lab) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).IsComodel ((ourInst (ℍ := ℍ) orowRF Ξ J₁).stateTheory T) l
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).stateCo T :=
  state_isComodel closed_of_derV_J₁ T l

end AtJ1

/-! ### Non-vacuity: a handler that is no model of state -/

section Witness
open BoCa.Fig16.LogRel.Core.EffPrograms

/-- The state function's type at state `bool`: `U(bool ⊸ F(bool ⊗ bool))`. -/
abbrev stR : VTy := .thunk (.arr boolT (.ret (.tensor boolT boolT)))

/-- `ansRetE : !U(bool ⊸ F stR)`. -/
theorem d_ansRetE {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ ansRetE (.val (retTy [] boolT stR)) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam (.ret (.thunkV rfl (.lam ?_))))
  exact .ret (.tensorI (.left (.right (deadSplit hΓ))) (.var (.here (.cons hΓ.toP)))
    (.var (.there (.here hΓ.toP))))

/-- `get`'s co-operation `λ(s, u). (s, s)` at `bool ⊗ 1 ⊸ F(bool ⊗ bool)`. -/
theorem d_getCoE {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ (.lam (.letpair (.var 0) (.pair (.var 1) (.var 1))))
      (.comp (.arr (.tensor boolT .unit) (.ret (.tensor boolT boolT)))) := by
  refine .lam (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  exact .ret (.tensorI (.dup rfl (.dup rfl (.dead (deadSplit hΓ))))
    (.var (.skip rfl (.here (.cons hΓ.toP)))) (.var (.skip rfl (.here (.cons hΓ.toP)))))


/-- `put`'s co-operation that keeps the old state, `λ(s, t). (s, ())`, at
`bool ⊗ bool ⊸ F(bool ⊗ 1)`. -/
theorem d_badPutCoE {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ (.lam (.letpair (.var 0) (.pair (.var 1) .unit)))
      (.comp (.arr (.tensor boolT boolT) (.ret (.tensor boolT .unit)))) := by
  refine .lam (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  exact .ret (.tensorI (.left (.left (.dead (deadSplit hΓ))))
    (.var (.skip rfl (.here (.cons hΓ.toP)))) (.unitI (.cons (.cons (.cons hΓ.toP)))))

theorem clauseTy_lin (R A B : VTy) :
    clauseTy [] R (.lin, A, B) = .bang (.thunk (.arr (.tensor A (kTy [] R .lin B)) (.ret R))) := by
  simp [clauseTy]; rfl

/-- **The state-passing clause at state `bool`**, from its co-operation's type. -/
theorem d_ansClauseE {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} {co : Expr}
    (hco : closedAt 0 co = true)
    (hcoT : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerivesAt Ξ Δ Γ' co (.comp (.arr (.tensor boolT A) (.ret (.tensor boolT B)))))
    (hΓ : Ctx.Dead Γ) :
    CDerivesAt Ξ Δ Γ (ansClauseE co) (.val (clauseTy [] stR (.lin, A, B))) := by
  rw [clauseTy_lin]
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .ret (.thunkV rfl (.lam ?_))
  -- `co (s, a) to q. …`, under `s`, `k`, `a`
  refine .bind (A := .tensor boolT B) (.left (.right (.left (.dead (deadSplit hΓ))))) ?_ ?_
  · -- `co (s, a)`: `(λx. co x) (s, a)`
    refine .bind (A := .tensor boolT A) (.left (.dead (.left (.dead (deadSplit hΓ)))))
      (.ret (.tensorI (.left (.dead (.right (.dead (deadSplit hΓ)))))
        (.var (.here (.cons (.cons (.cons hΓ.toP)))))
        (.var (.there (.there (.here (.cons hΓ.toP))))))) ?_
    refine .app (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))) ?_
      (.here (.cons (.cons (.cons (.cons hΓ.toP)))))
    rw [shift_closed0 hco]
    exact hcoT _ (.cons (.cons (.cons (.cons (.cons hΓ)))))
  · -- `let (s', b) = q in k.resume b to f. f s'`
    refine .tensorE (.left (.dead (.right (.dead (.dead (deadSplit hΓ))))))
      (.var (.here (.cons (.cons (.cons (.cons hΓ.toP)))))) ?_
    refine .bind (A := stR) (.left (.right (.dead (.dead (.left (.dead (.dead (deadSplit hΓ))))))))
      ?_ ?_
    · -- `k.resume b`: `(λy. k (inj₁ ()) y) b`
      refine .bind (A := B) (.left (.dead (.dead (.dead (.right (.dead (.dead (deadSplit hΓ))))))))
        (.ret (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))))) ?_
      refine .app (.right (.dead (.dead (.dead (.dead (.left (.dead (.dead (deadSplit hΓ)))))))))
        (.proj₁ (.force (C := .amp (.arr B (.ret stR)) .top)
          (.there (.there (.there (.there (.there (.here (.cons (.cons hΓ.toP))))))))))
        (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))))
    · -- `f s'`: `(λz. f z) s'`
      refine .bind (A := boolT) (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead
          (deadSplit hΓ)))))))))
        (.ret (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))) ?_
      exact .app (.right (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead
          (deadSplit hΓ))))))))))
        (.force (C := .arr boolT (.ret (.tensor boolT boolT)))
          (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))))))
        (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))


/-- `get : 1 ↠ bool` and `put : bool ↠ 1`, linear: global state of `bool`. -/
abbrev stE : List (Qual × VTy × VTy) := [(.lin, .unit, boolT), (.lin, boolT, .unit)]

/-- The handled row of the name `13`. -/
abbrev stRow : Row := Row.ofEff 13 stE 0 ++ []

/-- The program: `M` handled by the co-operations' handler at the name `13`, run from `tt`. -/
def stProg (cos : List Expr) (M : Expr) : Expr :=
  bindE (hndExpr 13 (stE.map Prod.fst) (.pair ansRetE (clausesE (cos.map ansClauseE))) M)
    (appE (.var 0) (.inj₂ .unit))

/-- The update–lookup law's left side, at the parameter `ff` and the continuation `λx. x`:
`put ff; get to y. k y`. -/
def stBodyL : Expr :=
  bindE (.lam (.var 0)) (bindE (.inj₁ .unit) (bindE (performE (opArgE 13 1 (.var 0)))
    (bindE (performE (opArgE 13 0 (.val .unit))) (appE (.var 3) (.var 0)))))

/-- Its right side: `put ff; k ff`. -/
def stBodyR : Expr :=
  bindE (.lam (.var 0)) (bindE (.inj₁ .unit) (bindE (performE (opArgE 13 1 (.var 0)))
    (appE (.var 2) (.var 1))))

theorem nW_stRow : ¬ stRow.Weak := by simp [Row.Weak, Row.ofEff]

/-- The handled row of `13` is tied to every context declaring global state there. -/
theorem rowAt_stRow {Ξ : EffCtx} (h13 : Ξ 13 = stE) : RowAt Ξ stRow :=
  rowAt_ofEff_append h13 (by decide) (by simp) (rowAt_nil Ξ)

theorem nU_stRow : ¬ stRow.Unr := by simp [Row.Unr, Row.ofEff]

theorem d_stBodyL {Ξ : EffCtx} (h13 : Ξ 13 = stE) {Δ : LifeCtx} :
    CDerivesAt Ξ Δ [] stBodyL (.comp (CTy.effOf stRow boolT)) := by
  refine .bind (A := .thunk (.arr boolT (CTy.effOf stRow boolT))) .nil
    (.ret (.thunkV rfl (.lam (.effSub (S := []) (rowLe_nil _) (.ret (.var (.here .nil))))))) ?_
  refine .bind (A := boolT) (.right .nil) (.ret (.sumI₁ (.unitI (.cons .nil)))) ?_
  refine .effLet (A := .unit) (.left (.right .nil)) (fun h => absurd h nW_stRow)
    (fun h => absurd h nU_stRow)
    (.effPerform (o := ⟨13, 1, .lin, boolT, .unit, .ret .unit⟩) (rowAt_stRow h13) rfl rfl
      (.var (.here (.cons .nil)))) ?_
  refine .effLet (A := boolT) (.left (.dead (.right .nil))) (fun h => absurd h nW_stRow)
    (fun h => absurd h nU_stRow)
    (.effPerform (o := ⟨13, 0, .lin, .unit, boolT, .ret .unit⟩) (rowAt_stRow h13) rfl rfl
      (.unitI (.drop rfl (.cons (.cons .nil)))))
    ?_
  exact .bind (A := boolT) (.left (.dead (.dead (.right .nil))))
    (.ret (.var (.here (.cons (.cons (.cons .nil))))))
    (.app (.right (.dead (.dead (.dead (.left .nil)))))
      (.force (C := .arr boolT (CTy.effOf stRow boolT)) (.there (.there (.there (.there (.here .nil))))))
      (.here (.cons (.cons (.cons (.cons .nil))))))

theorem d_stBodyR {Ξ : EffCtx} (h13 : Ξ 13 = stE) {Δ : LifeCtx} :
    CDerivesAt Ξ Δ [] stBodyR (.comp (CTy.effOf stRow boolT)) := by
  refine .bind (A := .thunk (.arr boolT (CTy.effOf stRow boolT))) .nil
    (.ret (.thunkV rfl (.lam (.effSub (S := []) (rowLe_nil _) (.ret (.var (.here .nil))))))) ?_
  refine .bind (A := boolT) (.right .nil) (.ret (.sumI₁ (.unitI (.cons .nil)))) ?_
  refine .effLet (A := .unit) (.dup rfl (.right .nil)) (fun h => absurd h nW_stRow)
    (fun h => absurd h nU_stRow)
    (.effPerform (o := ⟨13, 1, .lin, boolT, .unit, .ret .unit⟩) (rowAt_stRow h13) rfl rfl
      (.var (.here (.cons .nil)))) ?_
  exact .bind (A := boolT) (.left (.left (.right .nil)))
    (.ret (.var (.skip rfl (.here (.cons .nil)))))
    (.app (.right (.dead (.dead (.left .nil))))
      (.force (C := .arr boolT (CTy.effOf stRow boolT)) (.there (.there (.there (.here .nil)))))
      (.here (.cons (.cons (.cons .nil)))))

/-- **The program is typed by Core's kernel with its inner rows tied**, at `F(bool ⊗ bool)`, for
co-operations at state's types, at every context declaring global state at `13`. -/
theorem d_stProg {Ξ : EffCtx} (h13 : Ξ 13 = stE) {Δ : LifeCtx} {co₁ co₂ : Expr}
    (hc₁ : closedAt 0 co₁ = true)
    (hc₂ : closedAt 0 co₂ = true)
    (ht₁ : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerivesAt Ξ Δ Γ' co₁ (.comp (.arr (.tensor boolT .unit) (.ret (.tensor boolT boolT)))))
    (ht₂ : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerivesAt Ξ Δ Γ' co₂ (.comp (.arr (.tensor boolT boolT) (.ret (.tensor boolT .unit)))))
    {M : Expr} (hM : CDerivesAt Ξ Δ [] M (.comp (CTy.effOf stRow boolT))) :
    CDerivesAt Ξ Δ [] (stProg [co₁, co₂] M) (.comp (.ret (.tensor boolT boolT))) := by
  have hH : CDerivesAt Ξ Δ [] (.pair ansRetE (clausesE ([co₁, co₂].map ansClauseE)))
      (.val (.tensor (retTy [] boolT stR) (clausesTy [] stR stE))) :=
    .tensorI .nil (d_ansRetE .nil) (.tensorI .nil (d_ansClauseE hc₁ ht₁ .nil)
      (.tensorI .nil (d_ansClauseE hc₂ ht₂ .nil) (.unitI .nil)))
  have hv : IsVal (.pair ansRetE (clausesE ([co₁, co₂].map ansClauseE))) :=
    .pair .lam (.pair .lam (.pair .lam .unit))
  refine .bind (A := stR) .nil (.effHandleV (S := []) (E := stE) (A := boolT) (R := stR)
    (rowAt_stRow h13) .nil .nil
    (.val ⟨_, hv⟩) hH (by decide) (by simp) (by simp) hM) ?_
  exact .bind (A := boolT) (.right .nil) (.ret (.sumI₂ (.unitI (.cons .nil))))
    (.app (.right (.left .nil)) (.force (C := .arr boolT (.ret (.tensor boolT boolT)))
      (.there (.here .nil))) (.here (.cons .nil)))


/-! ### The witness: a `put` that keeps the old state -/

/-- `ΞA` with global state of `bool` at the name `13`. -/
def Ξst : EffCtx := fun n => if n = 13 then stE else ΞA n

theorem Ξst_13 : Ξst 13 = stE := rfl

theorem Ξst_other {n : UInt32} (h : n ≠ 13) : Ξst n = ΞA n := by simp [Ξst, h]

/-- **`Ξst` is admissible.** -/
theorem admEff_Ξst : AdmEff Ξst := by
  obtain ⟨hNU, hCL, hR⟩ := admEff_ΞA
  refine ⟨fun n q A B h hq => ?_, fun n q A B h x => ?_, fun E hE => ?_⟩
  · by_cases hn : n = 13
    · subst hn; rw [Ξst_13] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> cases hq
    · rw [Ξst_other hn] at h; exact hNU n q A B h hq
  · by_cases hn : n = 13
    · subst hn; rw [Ξst_13] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> simp [VFree, boolT]
    · rw [Ξst_other hn] at h; exact hCL n q A B h x
  · obtain ⟨n₁, n₂, hne, h₁, h₂, e₁, e₂⟩ := hR E hE
    have h13 : ΞA 13 = [] := by simp [ΞA]
    have hn₁ : n₁ ≠ 13 := by
      rintro rfl; rw [h13] at e₁; subst e₁; simp [eSigs] at hE
    have hn₂ : n₂ ≠ 13 := by
      rintro rfl; rw [h13] at e₂; subst e₂; simp [eSigs] at hE
    exact ⟨n₁, n₂, hne, h₁, h₂, by rw [Ξst_other hn₁, e₁], by rw [Ξst_other hn₂, e₂]⟩

/-- The label of the name `13`: global state of `bool`. -/
def labSt : (orowAlg Ξst).Lab := ⟨13, by decide, by simp [Ξst], by simp [Ξst]⟩

/-- The state type, at our instance. -/
abbrev stT : OVTy := OVTy.ofV boolT

/-- `λx. x`, the continuation. -/
def idK : OVal := ⟨.lam (.var 0), .lam⟩

def getCoE : Expr := .lam (.letpair (.var 0) (.pair (.var 1) (.var 1)))

def badPutCoE : Expr := .lam (.letpair (.var 0) (.pair (.var 1) .unit))

/-- The update–lookup law's two sides, handled by the bad co-operations and run from `tt`, at the
parameter `ff` and the continuation `λx. x`, are `stProg`'s programs. -/
theorem badL_eq :
    (ourInst (ℍ := ℍ) orowRF Ξst J₁).runAt labSt (ourInst (ℍ := ℍ) orowRF Ξst J₁).badStateCo
      (ourInst (ℍ := ℍ) orowRF Ξst J₁).tt
      ((ourInst (ℍ := ℍ) orowRF Ξst J₁).lets
        [(ourInst (ℍ := ℍ) orowRF Ξst J₁).ff, idK]
        ((ourInst (ℍ := ℍ) orowRF Ξst J₁).slTerm labSt [stT].length
          ((ourInst (ℍ := ℍ) orowRF Ξst J₁).eqnPG stT).lhs)) =
      stProg [getCoE, badPutCoE] stBodyL := rfl

theorem badR_eq :
    (ourInst (ℍ := ℍ) orowRF Ξst J₁).runAt labSt (ourInst (ℍ := ℍ) orowRF Ξst J₁).badStateCo
      (ourInst (ℍ := ℍ) orowRF Ξst J₁).tt
      ((ourInst (ℍ := ℍ) orowRF Ξst J₁).lets
        [(ourInst (ℍ := ℍ) orowRF Ξst J₁).ff, idK]
        ((ourInst (ℍ := ℍ) orowRF Ξst J₁).slTerm labSt [stT].length
          ((ourInst (ℍ := ℍ) orowRF Ξst J₁).eqnPG stT).rhs)) =
      stProg [getCoE, badPutCoE] stBodyR := rfl

/-- `λx. x`, the continuation, as a Core value. -/
def idKV : Val := ⟨.lam (.var 0), .lam⟩

/-- The handler's last steps from the fold's end: the continuation `λx. x` at the answer `fv`, the
return clause and the closing frame at the state `tt` answer `(tt, fv)`. -/
def badTail (fv : Val) : Expr :=
  (stFrame (Val.inj₂ Val.unit)).plug (hndE (ansHV (orowRF.name Ξst labSt)
    ((Ξst (orowRF.name Ξst labSt)).map Prod.fst) (ourInst (ℍ := ℍ) orowRF Ξst J₁).badStateCo)
    (appE idKV.1 fv.1))

theorem badTail_tt : lookEnd 20 (badTail (ℍ := ℍ) (Val.inj₂ Val.unit)) = .pair (.inj₂ .unit) (.inj₂ .unit) := by
  rfl

theorem badTail_ff : lookEnd 20 (badTail (ℍ := ℍ) (Val.inj₁ Val.unit)) = .pair (.inj₂ .unit) (.inj₁ .unit) := by
  rfl

theorem quiet_badTail_tt :
    Quiet (ℍ := ℍ) (badTail (ℍ := ℍ) (Val.inj₂ Val.unit)) (.pair (.inj₂ .unit) (.inj₂ .unit)) := by
  have h := quiet_of_look (ℍ := ℍ) 20 (badTail (ℍ := ℍ) (Val.inj₂ Val.unit)) rfl
  rwa [badTail_tt] at h

theorem quiet_badTail_ff :
    Quiet (ℍ := ℍ) (badTail (ℍ := ℍ) (Val.inj₁ Val.unit)) (.pair (.inj₂ .unit) (.inj₁ .unit)) := by
  have h := quiet_of_look (ℍ := ℍ) 20 (badTail (ℍ := ℍ) (Val.inj₁ Val.unit)) rfl
  rwa [badTail_ff] at h

/-- A closed value that Core's kernel with its inner rows tied types at a type free of the row `∀`
is typed at our instance by `J₁`. -/
theorem derV_J₁_of {Ξ : EffCtx} {v : OVal} {A : VTy} (hcl : closedAt 0 v.1 = true)
    (h : CDerivesAt Ξ LifeCtx.empty [] v.1 (.val A)) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).derV [] v (OVTy.ofV A) := by
  refine ⟨[], by simp, fun _ h => absurd h List.not_mem_nil, .inl (OVTy.rFree_ofV A), ?_⟩
  intro η _ _ σ _
  simp only [J1CoreAt, OVTy.isPoly_of_rFree (OVTy.rFree_ofV A), Bool.false_eq_true, if_false]
  show CDerivesAt Ξ LifeCtx.empty [] (fillS σ 0 v.1) (.val (OVTy.den η (OVTy.ofV A)))
  rw [fillS_closed σ v.1 0 hcl, OVTy.den_ofV]
  exact h

/-- **A handler that is no model of global state** (non-vacuity of `AnsCorrect`).  At `J₁` and
the admissible effect context `Ξst`, the handler whose `put` keeps the old state fails the
update–lookup law: `put ff; get to y. k y`, handled from `tt` with `k = λx. x`, answers
`(tt, tt)`, and `put ff; k ff` answers `(tt, ff)`.  Both sides are typed by Core's kernel, so the
first is reached from a typed program, its own start. -/
theorem not_ansCorrect_badState :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξst J₁).AnsCorrect
      ((ourInst (ℍ := ℍ) orowRF Ξst J₁).stateTheory stT) labSt
      (ourInst (ℍ := ℍ) orowRF Ξst J₁).badStateCo stT := by
  intro h
  let S := ourInst (ℍ := ℍ) orowRF Ξst J₁
  have hsig : S.sig labSt = S.stateSig stT := rfl
  have hmem : S.eqnPG stT ∈ S.stateTheory stT labSt := by
    unfold A.EffectSystem.stateTheory
    rw [if_pos hsig]
    simp [A.EffectSystem.stateEqns]
  have htt : S.derV [] S.tt stT := derV_J₁_of rfl (.sumI₂ (.unitI .nil))
  have hff : S.derV [] S.ff stT := derV_J₁_of rfl (.sumI₁ (.unitI .nil))
  have hRA : S.RunsAlike (stProg [getCoE, badPutCoE] stBodyL) (stProg [getCoE, badPutCoE] stBodyR) :=
    h _ hmem [S.ff] idK S.tt htt (.cons hff .nil)
  have hcg : closedAt 0 getCoE = true := rfl
  have hcb : closedAt 0 badPutCoE = true := rfl
  have hder : S.der [] (stProg [getCoE, badPutCoE] stBodyL)
      (S.F (orowAlg Ξst).unit (OVTy.ofV (.tensor boolT boolT))) :=
    der_J₁_ret (by decide) (d_stProg Ξst_13 hcg hcb (fun _ hΓ => d_getCoE hΓ)
      (fun _ hΓ => d_badPutCoE hΓ) (d_stBodyL Ξst_13))
  let ttV : Val := Val.inj₂ Val.unit
  let ffV : Val := Val.inj₁ Val.unit
  have hco : ∀ c ∈ S.badStateCo, closedAt 0 c.1 = true := pureCo_badStateCo.1
  -- the co-runs: `put ff` keeps `tt`; then `get` answers `tt`, or the continuation takes `ff`
  have cL : CoRun (ℍ := ℍ) S.badStateCo [ffV] (S.eqnPG stT).lhs.fin (S.eqnPG stT).lhs.steps [] ttV
      ttV ttV :=
    .cons (i := 1) (by show 1 < 2; decide) (quiet_badPutCo ttV _) rfl rfl
      (.cons (i := 0) (by show 0 < 2; decide) (quiet_getCo ttV _) rfl rfl .nil)
  have cR : CoRun (ℍ := ℍ) S.badStateCo [ffV] (S.eqnPG stT).rhs.fin (S.eqnPG stT).rhs.steps [] ttV
      ttV ffV :=
    .cons (i := 1) (by show 1 < 2; decide) (quiet_badPutCo ttV _) rfl rfl .nil
  have hwf := stateTheory_wf (ℍ := ℍ) (RF := orowRF) (Ξ := Ξst) (J := J₁) stT labSt _ hmem
  have hvs : ∀ v ∈ [ffV], closedAt 0 v.1 = true := fun v hv => by rw [List.mem_singleton.1 hv]; rfl
  -- each side runs calmly through the fold, then to its answer
  have hcalmL : Calm (ℍ := ℍ) (stProg [getCoE, badPutCoE] stBodyL)
      (.pair (.inj₂ .unit) (.inj₂ .unit)) := by
    rw [← badL_eq]
    exact (calm_side (J := J₁) (l := labSt) hco (show 2 ≤ 2 ^ 32 by decide) (vsV := [ffV]) (kV := idKV)
      (s₀V := ttV) hvs rfl rfl rfl cL hwf.1).trans quiet_badTail_tt.calm
  have hcalmR : Calm (ℍ := ℍ) (stProg [getCoE, badPutCoE] stBodyR)
      (.pair (.inj₂ .unit) (.inj₁ .unit)) := by
    rw [← badR_eq]
    exact (calm_side (J := J₁) (l := labSt) hco (show 2 ≤ 2 ^ 32 by decide) (vsV := [ffV]) (kV := idKV)
      (s₀V := ttV) hvs rfl rfl rfl cR hwf.2).trans quiet_badTail_ff.calm
  have hvL : IsVal (Expr.pair (.inj₂ .unit) (.inj₂ .unit)) := .pair (.inj₂ .unit) (.inj₂ .unit)
  have hvR : IsVal (Expr.pair (.inj₂ .unit) (.inj₁ .unit)) := .pair (.inj₂ .unit) (.inj₁ .unit)
  have hL := (obsFrom_calm_iff S.R₀ (μ := Adequacy.emptyMem) (s := ()) finDom_empty hcalmL _ _).2
    (obsFrom_of_chain (J := J₁) S.R₀ (μ := Adequacy.emptyMem) (s := ()) .nil hvL)
  have hdat : S.DataTy (OVTy.ofV (.tensor boolT boolT)) :=
    A.EffectSystem.DataTy.tensor (A.EffectSystem.DataTy.sum .unit .unit)
      (A.EffectSystem.DataTy.sum .unit .unit)
  have h' := (hRA S.R₀ r₀_respects _ _ _ ((Adequacy.emptyMem, stProg [getCoE, badPutCoE] stBodyL), ())
    .hole hdat hder .refl rfl _ _).mp hL
  have h'' := (obsFrom_calm_iff S.R₀ (μ := Adequacy.emptyMem) (s := ()) finDom_empty hcalmR _ _).1 h'
  obtain ⟨q, hq, hv, -⟩ := h''
  have hend := complete_chain (J := J₁) S.R₀ .nil hvR q hq
  have e : (Expr.pair (.inj₂ .unit) (.inj₂ .unit) : Expr) = .pair (.inj₂ .unit) (.inj₁ .unit) :=
    hv.symm.trans hend
  simp at e


/-- **Co-operations that are no comodel of global state**: at `J₁` and `Ξst`, the bad
co-operations' runs of the update–lookup law from `tt` at `ff` reach the final state `tt` and the
continuation arguments `tt` and `ff`. -/
theorem not_isComodel_badState :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξst J₁).IsComodel
      ((ourInst (ℍ := ℍ) orowRF Ξst J₁).stateTheory stT) labSt
      (ourInst (ℍ := ℍ) orowRF Ξst J₁).badStateCo stT := by
  intro h
  let S := ourInst (ℍ := ℍ) orowRF Ξst J₁
  have hsig : S.sig labSt = S.stateSig stT := rfl
  have hmem : S.eqnPG stT ∈ S.stateTheory stT labSt := by
    unfold A.EffectSystem.stateTheory
    rw [if_pos hsig]
    simp [A.EffectSystem.stateEqns]
  have htt : S.derV [] S.tt stT := derV_J₁_of rfl (.sumI₂ (.unitI .nil))
  have hff : S.derV [] S.ff stT := derV_J₁_of rfl (.sumI₁ (.unitI .nil))
  obtain ⟨w, hL, hR⟩ := h _ hmem [S.ff] S.tt htt (.cons hff .nil)
  let ttV : Val := Val.inj₂ Val.unit
  let ffV : Val := Val.inj₁ Val.unit
  have hco : ∀ c ∈ S.badStateCo, closedAt 0 c.1 = true := pureCo_badStateCo.1
  -- the co-runs: `put ff` keeps `tt`; then `get` answers `tt`, or the continuation takes `ff`
  have cL : CoRun (ℍ := ℍ) S.badStateCo [ffV] (S.eqnPG stT).lhs.fin (S.eqnPG stT).lhs.steps [] ttV
      ttV ttV :=
    .cons (i := 1) (by show 1 < 2; decide) (quiet_badPutCo ttV _) rfl rfl
      (.cons (i := 0) (by show 0 < 2; decide) (quiet_getCo ttV _) rfl rfl .nil)
  have cR : CoRun (ℍ := ℍ) S.badStateCo [ffV] (S.eqnPG stT).rhs.fin (S.eqnPG stT).rhs.steps [] ttV
      ttV ffV :=
    .cons (i := 1) (by show 1 < 2; decide) (quiet_badPutCo ttV _) rfl rfl .nil
  have hcl₀ : ∀ v ∈ [ttV, ffV], closedAt 0 v.1 = true := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> rfl
  have hwf := stateTheory_wf (ℍ := ℍ) (RF := orowRF) (Ξ := Ξst) (J := J₁) stT labSt _ hmem
  have qL := (quiet_lets (Ξ := Ξst) (J := J₁) [ttV, ffV] hcl₀ _).trans
    (quiet_coFrom (Ξ := Ξst) (J := J₁) hco cL (coEnv_init rfl (fun v hv => by rw [List.mem_singleton.1 hv]; rfl))
      hwf.1)
  have qR := (quiet_lets (Ξ := Ξst) (J := J₁) [ttV, ffV] hcl₀ _).trans
    (quiet_coFrom (Ξ := Ξst) (J := J₁) hco cR (coEnv_init rfl (fun v hv => by rw [List.mem_singleton.1 hv]; rfl))
      hwf.2)
  have eL := runsTo_val (J := J₁) qL hL
  have eR := runsTo_val (J := J₁) qR hR
  have e : Expr.pair (.inj₂ .unit) (.inj₂ .unit) = Expr.pair (.inj₂ .unit) (.inj₁ .unit) :=
    eL.symm.trans eR
  injection e with _ h₂
  injection h₂


end Witness

end Targets.Inst

end
