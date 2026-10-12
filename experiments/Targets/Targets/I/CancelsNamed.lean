import Targets.Base.RaiseNames
import Targets.I.CancelsNZ

/-!
# The interaction — no run of a typed program keeps an error of a name no label has

A's traces read the error a cancel keeps at the labels (`keptErrOf`), so S5's no-interception at
our instance needs each running finaliser's `cfin` frame in a cancelled region to hold an error of a
label's name (`CancelsNamed`, `Targets/Instance/CancelRuns.lean`).  At `J₁` it is a run invariant:

* **a typed program raises only its labels' names** (`rcE_of_derivesAt`): `J₁`'s kernel ties the
  row a raise is found in to the effect context (`CDerivesAt.effRaise`, decision R), and holds no
  `cfin`;
* **no machine step leaves the labels' names** (`raiseOK_step1`, `Targets/Base/RaiseNames.lean`):
  a step raises only what it consumed or the error a cancel keeps, and keeps only the raise of a
  nonzero name, which is a label's;
* **the runner answers with data**, which holds no raise: a typed program asks the runner at data
  arguments only (`platData_of_start`; a driven program's, `driveData_of_reach`), and the protocol
  answers a data argument with data.

So every configuration a typed program reaches holds raises and cancel states of labels' names
only (`raiseOK_reach`).  A cancelled `κ` holds the continuation's context in its resume branch,
shifted past the branch's binders, and a shift keeps the names its running finalisers hold
(`kcfinNamed_of_shift`); so `CancelsNamed` holds at `J₁` at every effect context
(`I.cancelsNamed_J₁`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx)

/-! ### Raises at named labels, decided -/

/-- The names `q` raises reach, and no `cfin`, decided: `raise` only applied to a literal-named
payload of a name in `q`. -/
def rcE (q : UInt32 → Bool) : Expr → Bool
  | .app (.prim .raise) (.pair (.prim (.lit (.i32 m))) r) => q m && rcE q r
  | .prim p => p != .raise && p != .cfin
  | .var _ | .unit | .loc _ => true
  | .pair a b | .seq a b | .letpair a b | .app a b => rcE q a && rcE q b
  | .inj₁ a | .inj₂ a | .lam a => rcE q a
  | .case a b c => rcE q a && rcE q b && rcE q c

theorem rcE_sound (q : UInt32 → Bool) (e : Expr) (h : rcE q e = true) :
    e.RaiseOK (fun m => q m = true) := by
  fun_induction rcE q e with
  | case1 m r ih =>
      simp only [Bool.and_eq_true] at h
      exact ⟨.inl rfl, ⟨raiseOK_lit _, ih h.2⟩, fun _ => ⟨m, r, rfl, .inl h.1⟩,
        fun h' => (nomatch h')⟩
  | case2 p =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact h
  | case3 => trivial
  | case4 => trivial
  | case5 => trivial
  | case6 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | case7 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | case8 a b iha ihb =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1, ihb h.2⟩
  | case9 a b hab iha ihb =>
      simp only [Bool.and_eq_true] at h
      have ha := iha h.1
      refine raiseOK_app_val ha (ihb h.2)
  | case10 a iha => exact iha h
  | case11 a iha => exact iha h
  | case12 a iha => exact iha h
  | case13 a b c iha ihb ihc =>
      simp only [Bool.and_eq_true] at h
      exact ⟨iha h.1.1, ihb h.1.2, ihc h.2⟩

section Checker
variable {q : UInt32 → Bool}

theorem rcE_app {a b : Expr} (ha : rcE q a = true) : rcE q (.app a b) = rcE q b := by
  rw [rcE.eq_9 q a b (fun m r h₁ _ => by subst h₁; simp [rcE] at ha)]
  simp [ha]

theorem rcE_qualsVal : ∀ qs : List Qual, rcE q (qualsVal qs).1 = true
  | [] => rfl
  | _ :: qs => by
      simp only [qualsVal, Val.pair, Val.i32, rcE, rcE_qualsVal qs, Bool.and_true]
      rfl

theorem rcE_travK : ∀ F : FShape, rcE q (travK F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travK, bindE, rcE, rcE_app, rcE_travK F, rcE_travK G]
  | .sum F G => by
      simp [travK, bindE, rcE, rcE_app, rcE_travK F, rcE_travK G]

theorem rcE_travO : ∀ F : FShape, rcE q (travO F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travO, bindE, rcE, rcE_app, rcE_travO F, rcE_travO G]
  | .sum F G => by
      simp [travO, bindE, rcE, rcE_app, rcE_travO F, rcE_travO G]

theorem rcE_travR : ∀ F : FShape, rcE q (travR F).1 = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travR, bindE, rcE, rcE_app, rcE_travR F, rcE_travR G]
  | .sum F G => by
      simp [travR, bindE, rcE, rcE_app, rcE_travR F, rcE_travR G]

theorem rcE_selfV {B : Expr} (hB : rcE q B = true) : rcE q (selfV B).1 = true := by
  simp [selfV, zX, rcE, hB]

theorem rcE_foldImmV (F : FShape) : rcE q (foldImmV F).1 = true := by
  have hB : rcE q (fB F) = true := by simp [fB, bindE, rcE, rcE_app, rcE_travK]
  simp [foldImmV, rcE, rcE_app, rcE_travK, rcE_selfV hB]

theorem rcE_foldOwnV (F : FShape) : rcE q (foldOwnV F).1 = true := by
  have hB : rcE q (fBO F) = true := by simp [fBO, bindE, rcE, rcE_app, rcE_travO]
  simp [foldOwnV, rcE, rcE_app, rcE_selfV hB]

theorem rcE_foldReuseV (F : FShape) : rcE q (foldReuseV F).1 = true := by
  have hB : rcE q (fBR F) = true := by simp [fBR, bindE, rcE, rcE_app, rcE_travR]
  simp [foldReuseV, rcE, rcE_app, rcE_selfV hB]

theorem rcE_mapV : ∀ A : VTy, rcE q (mapV A).1 = true
  | .tvar 0 => rfl
  | .tensor A B => by simp [mapV, rcE, rcE_app, rcE_mapV A, rcE_mapV B]
  | .sum A B => by simp [mapV, rcE, rcE_app, rcE_mapV A, rcE_mapV B]
  | .box _ A => rcE_mapV A
  | .tvar (_ + 1) | .unit | .zero | .thunk _ | .ref _ | .imm _ _ | .mut _ _
  | .bang _ | .unk | .mu _ | .int _ | .opq _ | .fam _ => rfl

theorem rcE_nodeV : ∀ C : CTy, rcE q (nodeV C).1 = true
  | .ret A => by simp [nodeV, bindE, rcE, rcE_app, rcE_mapV]
  | .amp C D => by simp [nodeV, rcE, rcE_app, rcE_nodeV C, rcE_nodeV D]
  | .eff _ _ _ _ _ _ C => by simp [nodeV, bindE, rcE, rcE_app, rcE_mapV]
  | .arr _ D => by simp [nodeV, rcE, rcE_app, rcE_nodeV D]
  | .top | .all _ _ _ | .nu _ => rfl

theorem rcE_unfoldV (C : CTy) : rcE q (unfoldV C).1 = true := by
  have hB : rcE q (fBN C) = true := by simp [fBN, rcE, rcE_app, rcE_nodeV]
  simp [unfoldV, rcE, rcE_app, rcE_selfV hB]

theorem rcE_forceE_var (C : CTy) (i : Nat) : rcE q (forceE C (.var i)) = true := by
  cases C <;> rfl

theorem rcE_withPair {M N : Expr} (hM : rcE q M = true) (hN : rcE q N = true) :
    rcE q (withPair M N) = true := by
  simp [withPair, rcE, hM, hN]

theorem rcE_withborUE {d : Expr} (hd : rcE q d = true) : rcE q (withborUE d) = true := by
  simp [withborUE, thenE, rcE, rcE_app, hd]

/-- **Filling a variable with a closed λ-value whose body passes `rcE` leaves `rcE` as it was**:
the λ-value is no primitive and no pair, so no raise is made or unmade. -/
theorem rcE_fill {b : Expr} (hb : rcE q b = true) (hc : closedAt 0 (Val.lam b).1 = true) :
    ∀ (N : Expr) (j : Nat), rcE q ((N.subst j (Val.lam b)).shift 1 j) = rcE q N
  | .var i, j => by
      have hv : rcE q (.var i) = true := rfl
      rw [hv]
      simp only [Expr.subst]
      split_ifs with h₁ h₂
      · rw [shift_closedAt _ 1 hc (Nat.zero_le _)]; exact hb
      · simp only [Expr.shift]; split_ifs <;> rfl
      · simp only [Expr.shift]; split_ifs <;> rfl
  | .unit, _ => rfl
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .pair a c, j => by
      simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j, rcE_fill hb hc c j]
  | .seq a c, j => by
      simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j, rcE_fill hb hc c j]
  | .letpair a c, j => by
      have hs : (Val.lam b).shift 2 0 = Val.lam b := val_shift_closed hc 2 0
      simp only [Expr.subst, Expr.shift, rcE, hs, rcE_fill hb hc a j, rcE_fill hb hc c (j + 2)]
  | .case a c e, j => by
      have hs : (Val.lam b).shift 1 0 = Val.lam b := val_shift_closed hc 1 0
      simp only [Expr.subst, Expr.shift, rcE, hs, rcE_fill hb hc a j, rcE_fill hb hc c (j + 1),
        rcE_fill hb hc e (j + 1)]
  | .inj₁ a, j => by simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j]
  | .inj₂ a, j => by simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc a j]
  | .lam a, j => by
      have hs : (Val.lam b).shift 1 0 = Val.lam b := val_shift_closed hc 1 0
      simp only [Expr.subst, Expr.shift, rcE, hs, rcE_fill hb hc a (j + 1)]
  | .app a c, j => by
      by_cases hp : ∃ m r, a = .prim .raise ∧ c = .pair (.prim (.lit (.i32 m))) r
      · obtain ⟨m, r, rfl, rfl⟩ := hp
        simp only [Expr.subst, Expr.shift, rcE, rcE_fill hb hc r j]
      · have hq : ∀ (m : UInt32) (r : Expr), (a.subst j (Val.lam b)).shift 1 j = .prim .raise →
            (c.subst j (Val.lam b)).shift 1 j = .pair (.prim (.lit (.i32 m))) r → False := by
          intro m r ha hc'
          obtain ⟨x₁, x₂, rfl, h₁, -⟩ := fill_pair_inv hc hc'
          exact hp ⟨m, x₂, fill_prim_inv hc ha, by rw [fill_prim_inv hc h₁]⟩
        show rcE q (.app ((a.subst j (Val.lam b)).shift 1 j) ((c.subst j (Val.lam b)).shift 1 j)) = _
        rw [rcE.eq_9 q _ _ hq, rcE.eq_9 q a c (fun m r h₁ h₂ => hp ⟨m, r, h₁, h₂⟩),
          rcE_fill hb hc a j, rcE_fill hb hc c j]

end Checker

/-- A label's name, decided: not the reserved `0`, declared, and at most `2³²` operations long. -/
def labQ (Ξ : EffCtx) (m : UInt32) : Bool := decide (m ≠ 0 ∧ Ξ m ≠ [] ∧ (Ξ m).length ≤ 2 ^ 32)

theorem labQ_zero (Ξ : EffCtx) : labQ Ξ 0 ≠ true := by simp [labQ]

/-- An operation a row tied to the effect context finds is of a label's name. -/
theorem labQ_of_rowAt {Ξ : EffCtx} {S : Row} (h : RowAt Ξ S) {n i : UInt32} {o : OpSig}
    (hf : Row.find S n i = some o) : labQ Ξ n = true := by
  obtain ⟨hn0, hlen, hget⟩ := h n i o hf
  have hne : Ξ n ≠ [] := by intro h0; rw [h0] at hget; simp at hget
  simp only [labQ, decide_eq_true_eq]
  exact ⟨hn0, hne, hlen⟩

/-- **A term the tied kernel types raises only its labels' names, and holds no `cfin`**: `[raise]`
finds its operation in a row tied to `Ξ` (decision R). -/
theorem rcE_of_derivesAt {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : rcE (labQ Ξ) e = true := by
  induction h with
  | force => exact rcE_forceE_var _ _
  | withI _ _ ihM ihN => exact rcE_withPair ihM ihN
  | withbor1U _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | withbor2U _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | withbor3U _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | sliceBorrowMU _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | sliceBorrowIU _ _ _ _ _ _ _ _ _ _ ih => exact rcE_withborUE ih
  | foldImm => exact rcE_foldImmV _
  | foldOwn => exact rcE_foldOwnV _
  | foldReuse => exact rcE_foldReuseV _
  | unfoldN => exact rcE_unfoldV _
  | lolliE _ _ _ iha ihf => rw [rcE_app ihf]; exact iha
  | @effRaise _ _ V S o _ hAt hf _ _ _ ih =>
      simp only [BoCa.BoLo.raiseE, opArgE, Expr.val, Val.prim, Val.i32, rcE, ih,
        labQ_of_rowAt hAt hf, Bool.and_true, Bool.true_and]
      rfl
  | effHandleV _ _ _ _ _ _ _ _ _ ihc ihe =>
      simp [hndExpr, Val.i32, rcE, rcE_app, rcE_qualsVal, ihc, ihe]
  | @letPoly _ _ N _ _ b hcl _ _ ihV ihN =>
      have hb : rcE (labQ Ξ) b = true := ihV
      rw [rcE_fill hb hcl N 0] at ihN
      rw [rcE.eq_9 _ _ _ (fun m r h _ => by cases h)]
      simp [rcE, Expr.val, Val.lam, ihN, hb]
  | _ => first | rfl | simp_all [rcE, rcE_app, absurdE, thenE, performE, opArgE, Val.i32]

/-! ### Data, and runs under a platform -/

/-- A data value holds no raise. -/
theorem raiseOK_of_dataVal {P : UInt32 → Prop} : ∀ {A : VTy} {v : Val}, DataVal A v → v.1.RaiseOK P
  | _, _, .unit => trivial
  | _, _, .int h => by
      obtain ⟨c, hc⟩ := h.val
      rw [hc]
      exact raiseOK_lit _
  | _, _, @DataVal.pair _ _ v₁ v₂ h₁ h₂ =>
      ⟨(raiseOK_of_dataVal h₁ : v₁.1.RaiseOK P), (raiseOK_of_dataVal h₂ : v₂.1.RaiseOK P)⟩
  | _, _, @DataVal.inj₁ _ _ v h => (raiseOK_of_dataVal h : v.1.RaiseOK P)
  | _, _, @DataVal.inj₂ _ _ v h => (raiseOK_of_dataVal h : v.1.RaiseOK P)
  | _, _, .roll h => raiseOK_of_dataVal h

section Runs
variable {P : UInt32 → Prop}

/-- **A step under a platform keeps every raise at the names `P`**, at a configuration where the
platform is asked at data arguments only: a machine step leaves no raise of another name
(`raiseOK_step1`), and the platform's answer to a data argument is data. -/
theorem raiseOK_pstep (hP0 : ¬ P 0) {Pl : Platform} (hP : Pl.Respects) {c c' : Conf Pl}
    (hPD : PlatData Pl c) (h : PStep (ℍ := ℍ) Pl c c') (he : c.e.RaiseOK P)
    (hμ : HeapRaiseOK P c.μ) : c'.e.RaiseOK P ∧ HeapRaiseOK P c'.μ := by
  cases h with
  | mach hs => exact raiseOK_step1 hP0 hs he hμ
  | @plat μ s s' K n i v w o hK hf hco =>
      have hdA : DataVal o.A v := hPD K n i v o rfl hK hf
      have hm := Row.find_mem hf
      have hdB : DataVal o.B w :=
        hP.typed s s' o v w hm.1 hdA (by rw [hm.2.1, hm.2.2]; exact hco)
      exact ⟨plug_raiseOK K (plug_raiseOK_inv K (plain_perform _) he).1 (raiseOK_of_dataVal hdB),
        hμ⟩

/-- **Every run from a start in Core's relation keeps every raise at the names `P`**, from a
program that raises at `P` only. -/
theorem raiseOK_of_start (hP0 : ¬ P 0) {Pl : Platform} (hP : Pl.Respects) {S : Row}
    (hag : PlatAgree Pl S) {Q : List SRec → Val → WProp} {e : Expr}
    (h₀ : ewpTS (ℍ := ℍ) [] e (opTable (Row.tab S LSub.empty)) Q PMap.empty) (he : e.RaiseOK P) :
    ∀ c, PSteps (ℍ := ℍ) Pl (init Pl e) c → c.e.RaiseOK P ∧ HeapRaiseOK P c.μ := by
  intro c h
  induction h with
  | refl => exact ⟨he, heapRaiseOK_empty⟩
  | @tail b c hb hbc ih =>
      exact raiseOK_pstep hP0 hP (Inst.platData_of_start hP hag h₀ b hb).1 hbc ih.1 ih.2

theorem raiseOK_nextE {l : Val} (hl : l.1.RaiseOK P) : (nextE l).RaiseOK P :=
  raiseOK_app_val hl trivial

/-- **Every configuration a drive reaches from a start in Core's relation keeps every raise at the
names `P`**, from a step that raises at `P` only. -/
theorem raiseOK_drive_of_reach (hP0 : ¬ P 0) {Pl : Platform} (hP : Pl.Respects) {S S₀ : Row}
    {A : VTy} (hsub : ∀ n i o, Row.find Pl.ops n i = some o → Row.find S n i = some o)
    (hle : RowLe S₀ S) (hC : (CTy.loopEffBody S₀ A .unit).NuOk) {M : Expr}
    (h : cC (ℍ := ℍ) (CTy.effOf S (.sum A (.thunk (CTy.loopEff S₀ A .unit)))) [] LSub.empty M
      PMap.empty) (hM : M.RaiseOK P)
    {rc : Conf Pl × Phase} (hr : Relation.ReflTransGen (RStep (ℍ := ℍ) Pl) (init Pl M, .drive) rc) :
    rc.1.e.RaiseOK P ∧ HeapRaiseOK P rc.1.μ := by
  induction hr with
  | refl => exact ⟨hM, heapRaiseOK_empty⟩
  | @tail b c hb hbc ih =>
      have hPD := (driveData_of_reach hP hsub hle hC h hb).1
      rcases rstep_cases hbc with ⟨hp, -⟩ | ⟨-, l, he, rfl⟩ | ⟨-, l, he, rfl⟩
      · exact raiseOK_pstep hP0 hP hPD hp ih.1 ih.2
      · refine ⟨raiseOK_nextE ?_, ih.2⟩
        have := ih.1
        rw [he] at this
        exact this
      · refine ⟨raiseOK_nextE ?_, ih.2⟩
        have := ih.1
        rw [he] at this
        exact this

end Runs

end Targets

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload kappa kappaC cancelVal)
open BoCa.Lifetime (LSub LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowAt RowCtx Platform PSteps labQ rcE
  rcE_of_derivesAt rcE_sound)

section Reach
variable {Ξ : EffCtx}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer (J1DerAt Ξ))

variable {R : (ourInst (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer (J1DerAt Ξ))).Runner}

theorem plain_cancelE (k : Expr) : Plain (cancelE k) := trivial

/-- The function of an application at the names `P`, a λ-value, is at `P`. -/
theorem raiseOK_app_lam_inv {P : UInt32 → Prop} {b a : Expr} (h : (Expr.app (.lam b) a).RaiseOK P) :
    (Expr.lam b).RaiseOK P :=
  (raiseOK_app_inv (f := .lam b) (a := a) (fun h => (nomatch h)) (fun h => (nomatch h)) h).1

/-- A label's name, decided, is a label's name. -/
theorem labQ_iff {m : UInt32} : labQ Ξ m = true ↔ LabName orowRF Ξ m := by
  constructor
  · intro h
    simp only [labQ, decide_eq_true_eq] at h
    exact ⟨⟨m, h⟩, rfl⟩
  · rintro ⟨l, rfl⟩
    simp only [labQ, decide_eq_true_eq]
    exact l.2

/-- **A program typed at `J₁` raises only its labels' names, and holds no `cfin`**: its
derivation, or its driven step's, is the tied kernel's. -/
theorem raiseOK_of_der_J₁ {e : Expr} {C : OCTy} (h : (𝕊).der [] e C) :
    e.RaiseOK (fun m => labQ Ξ m = true) := by
  obtain ⟨-, hd⟩ := h
  rcases hd with ⟨Θ, hΘ, hd⟩ | ⟨-, M, rfl, -, Θ, hΘ, hd⟩
  · exact rcE_sound _ e (rcE_of_derivesAt (coreClosedAt_J₁ Ξ hΘ hd))
  · exact raiseOK_app_val (raiseOK_lit _)
      (rcE_sound _ M (rcE_of_derivesAt (coreClosedAt_J₁ Ξ hΘ hd)))

/-- **No run of a program typed at `J₁` raises or keeps a name no label has**, under every runner
that keeps its protocol: every configuration it reaches is at the labels' names, and so is its
memory unless the configuration is the driven program's answer.  A plain program's run is its run
under the runner's platform (`plain_reach`), a driven program's the drive's (`drive_reach`); along
both the platform is asked at data arguments only, and answers with data. -/
theorem raiseOK_reach (hR : R.Respects) {P : Expr} {C : OCTy} (hP : (𝕊).der [] P C)
    {x : (𝕊).RConf R} (hx : (𝕊).RReach R ((𝕊).rinit R P) x) :
    x.1.2.RaiseOK (fun m => labQ Ξ m = true) := by
  have hJ := coreClosed_J₁At Ξ
  have hP0 : ¬ (fun m => labQ Ξ m = true) 0 := Targets.labQ_zero Ξ
  have hPok := raiseOK_of_der_J₁ hP
  obtain ⟨S, A₀, -, hS, hcases⟩ := der_cases hJ hP
  have hcl := closed_of_der hJ hP
  have hPl := platformOf_respects hR hS
  rcases hcases with hcC | ⟨M, S₀, A₁, rfl, hle, hnu, rfl, hcC⟩
  · obtain ⟨-, -, hps⟩ := plain_reach hR hS hcC hcl hx
    exact (Targets.raiseOK_of_start hP0 hPl platAgree_platformOf
      ((cC_effOf S _ [] LSub.empty P PMap.empty).mp hcC) hPok _ hps).1
  · have hM : closedAt 0 M = true := by simpa [driveE, driveMark, closedAt] using hcl
    have hMok : M.RaiseOK (fun m => labQ Ξ m = true) := (raiseOK_app_inv (f := driveMark) (a := M)
      (by simp [driveMark]) (by simp [driveMark]) hPok).2
    rcases drive_reach hR hS hle hnu hcC hM hx with ⟨t, he, -, -, hr⟩ | ⟨a, μ₀, s₀, he, -, hr⟩
    · obtain ⟨h₁, -⟩ := Targets.raiseOK_drive_of_reach hP0 hPl platformOf_sub hle hnu hcC hMok hr
      rw [he]
      exact raiseOK_app_val (raiseOK_lit _) h₁
    · obtain ⟨h₁, -⟩ := Targets.raiseOK_drive_of_reach hP0 hPl platformOf_sub hle hnu hcC hMok hr
      rw [he]
      exact h₁

/-- Running finalisers' kept errors at the labels' names, decided, are kept errors the labels
read. -/
theorem cfinNamed_of_kcfinNamed : ∀ {K : Kont},
    KCfinNamed (fun m => labQ Ξ m = true) K → CfinNamed orowRF Ξ K
  | .hole, _ => trivial
  | .appR f K, h => by
      refine ⟨fun e he => ?_, cfinNamed_of_kcfinNamed h.2⟩
      rcases h.1 e he with rfl | ⟨m, j, w, rfl, hm⟩
      · trivial
      · exact ⟨m, j, w, rfl, labQ_iff.1 hm⟩
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => cfinNamed_of_kcfinNamed (K := K) h

/-- **At `J₁`, every cancelled continuation's running finalisers hold kept errors the labels read**,
at every effect context: the configuration that cancels `κ` is at the labels' names
(`raiseOK_reach`), and `κ`'s resume branch holds its context shifted, which keeps the names its
running finalisers hold (`kcfinNamed_of_shift`).  The handler is a value: otherwise the cancel is
stuck at `() (inj₂ ())`, against `LiveOK`. -/
theorem cancelsNamed_J₁At : CancelsNamed (ℍ := ℍ) orowRF Ξ (OurTyping.ofDer (J1DerAt Ξ)) := by
  intro R hR e ε A _ he c₀ K₀ l H K hreach h₀
  have hlive : (𝕊).Live c₀.1 := ⟨e, _, R, c₀.2, hR, he, hreach⟩
  have hv := hnd_val_of_cancel (I.liveOK_J₁ (Ξ := Ξ)) hlive h₀
  have hok := raiseOK_reach hR he hreach
  obtain ⟨⟨μ₀, e₀⟩, s₀⟩ := c₀
  change e₀.RaiseOK _ at hok
  rcases h₀ with h₀ | ⟨ℓ, h₀⟩
  · change e₀ = Kont.plug K₀ (cancelE (captureE (orowRF.name Ξ l) (qsOf Ξ (orowRF.name Ξ l))
      H.1.1 (H.2.map Subtype.val) K)) at h₀
    rw [captureE_of_val K hv] at h₀
    rw [h₀] at hok
    have hc := (plug_raiseOK_inv K₀ (plain_cancelE _) hok).2
    exact cfinNamed_of_kcfinNamed (kcfinNamed_of_shift (kcfinNamed_of_kraiseOK
      (kraiseOK_of_kappa (raiseOK_app_lam_inv hc))))
  · change e₀ = Kont.plug K₀ (cancelE (captureAtE true ℓ (orowRF.name Ξ l)
      (qsOf Ξ (orowRF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K)) at h₀
    have hc : captureAtE true ℓ (orowRF.name Ξ l) (qsOf Ξ (orowRF.name Ξ l)) H.1.1
        (H.2.map Subtype.val) K = kappaC true ℓ ⟨_, hv⟩ K := by
      unfold captureAtE; rw [dif_pos hv]
    rw [hc] at h₀
    rw [h₀] at hok
    have hc := (plug_raiseOK_inv K₀ (plain_cancelE _) hok).2
    exact cfinNamed_of_kcfinNamed (kcfinNamed_of_shift (kcfinNamed_of_kraiseOK
      (kraiseOK_of_kappaC (raiseOK_app_lam_inv hc))))

end Reach

end Targets.Inst

namespace Targets.I
open Targets.Inst (ourInst J₁ J1DerAt)

/-- **At `J₁`, every cancelled continuation's running finalisers hold kept errors the labels
read**, at every effect context. -/
theorem cancelsNamed_J₁ {Ξ : EffCtx} : Inst.CancelsNamed (ℍ := ℍ) orowRF Ξ J₁ :=
  Inst.cancelsNamed_J₁At

end Targets.I

end
