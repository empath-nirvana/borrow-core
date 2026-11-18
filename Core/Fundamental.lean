import Core.Compat
import Core.CodeRules
import Core.CodeNuOut
import Core.Integers
import Core.Arrays
import Core.SliceOps
import Core.SliceCopy
import Core.CountFold
import Core.BoundedFix
import Core.FoldReuse
import Core.FoldOwnG
import Core.Nu
import Core.EffFin
import Core.EffBorrow
import Core.EffBoxed
import Core.PolyLet
import Core.DivHandle
import Core.DivHandleLast
import Core.Tok
import Core.Alpha
import Core.PinLaw
import Support.LogicalRelation.Adequacy

/-!
# Core — Fundamental Property and adequacy  `[spec §3]`

`CDerives Δ Γ e j`: the CBPV typing judgment on BoLo expressions, with `j` a value judgment
`val A` or a computation judgment `comp C`, in A-normal form.  Beside the CBPV formers it has
the lifetime `∀` (`∀E` at every `C`), the `!` rules, `[]I`/`[]E` (`[]I` at every value type),
`⊑imm`/`⊑mut`, one constant per borrow axiom at arbitrary value-type payloads, three
call-by-value derived forms (`lolliE`, `allEV`, `ofRet`), `roll`/`unroll` at `μ`, and the
borrowed and owned folds `foldImm`, `foldOwn`, `foldReuse` (`FoldImm.lean`, `FoldOwn.lean`,
`FoldReuse.lean`), and `νX. C`'s `nuIn`/`nuOut` and coiteration `unfoldN` (`Nu.lean`), of which
the delay and stream types' rules are instances (`fixD`, `unfoldS`).  §19's effect rules, with
§24's polymorphic let (`letPoly`), its `[handle]` at a value form (`effHandleV`, of which the
two-variable `effHandle` is an instance) and its `[then]` at a finaliser of the pure row; §28's
BOXED-κ (`effHandleVB`: `[handle]` with each clause's continuation boxed at `@d`); §26's
`λ_. M` at `1 ⊸ F_Σ B` with its binder dead (`lamDead`).
`fundamentalC` proves every rule sound at `SemV`/`SemC`; `adequacyC` runs a closed `F 1`
computation to `()` from the empty memory.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### `roll` and `unroll`

Typing rules on the same term, as `!E` is: the machine has no `roll`/`unroll` step. -/

/-- `roll` is sound: the unroll equation at `vC true`, under `wpTS_mono`. -/
theorem roll_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} (hA : A.NoMut 0)
    (hc : (VTy.mu A).Cl 0) (h : SemV Δ Γ e (VTy.inst (.mu A) A)) : SemV Δ Γ e (.mu A) :=
  fun δ γ ls ρ hδ hΓ => wpTS_mono (fun _ _ _ hv => vC_roll hA hc hv) ρ (h δ γ ls ρ hδ hΓ)

/-- `unroll` is sound. -/
theorem unroll_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : SemV Δ Γ e (.mu A)) : SemV Δ Γ e (VTy.inst (.mu A) A) :=
  fun δ γ ls ρ hδ hΓ => wpTS_mono (fun _ _ _ hv => (vC_unfold hv).2.2) ρ (h δ γ ls ρ hδ hΓ)

/-! ### `[λ-dead]`  `[spec §26]` -/

/-- A live slot of `1` gives the context relation with the slot dead: a value of `1` holds only
the empty resource. -/
theorem gDenC_unit_dead {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    (h : gDenC ls δ (⟨.unit, true⟩ :: Γ) γ ρ) : gDenC ls δ (⟨.unit, false⟩ :: Γ) γ ρ := by
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp h
  cases γ with
  | nil => exact absurd hlen (by simp)
  | cons v γ =>
      obtain ⟨-, hs'⟩ := gSepC_cons_persistent (T := .unit) rfl hs
      exact gDenC_dead_cons .unit v (gDenC_mk (by simpa using hlen) hs')

/-- `λx. M : 1 ⊸ C` with `x`'s slot dead: `[λ]` at the context with `x : 1` live, whose relation
gives the one with `x` dead.  `[spec §26]` -/
theorem lamDead_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : SemC Δ (⟨.unit, false⟩ :: Γ) M C) : SemC Δ Γ (.val (.lam M)) (.arr .unit C) :=
  lam_compatC fun δ γ ls ρ hδ hg => h δ γ ls ρ hδ (gDenC_unit_dead hg)

/-! ### The cancellable marker is read by typing only  `[spec §29a]` -/

/-- An operation without its marker. -/
def OpSig.unmark (o : OpSig) : OpSig := { o with rc := false }

theorem Row.unmark_ofEff (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy)
    (cs : Nat → Bool), (Row.ofEff n E k fs cs).map OpSig.unmark = (Row.ofEff n E k fs).map OpSig.unmark
  | [], _, _, _ => rfl
  | _ :: E, k, fs, cs => by
      simp only [Row.ofEff, List.map_cons, OpSig.unmark]
      exact congrArg _ (Row.unmark_ofEff n E (k + 1) _ _)

theorem Row.unmark_ofEff_append (n : UInt32) (E : List (Qual × VTy × VTy)) (k : Nat)
    (fs : Nat → CTy) (cs : Nat → Bool) (S : Row) :
    (Row.ofEff n E k fs cs ++ S).map OpSig.unmark = (Row.ofEff n E k fs ++ S).map OpSig.unmark := by
  rw [List.map_append, List.map_append, Row.unmark_ofEff]

/-- Rows equal up to their markers are `CTyEq` at every answer: `CTyEq` does not read `rc`. -/
theorem CTyEq.effOf_unmark : ∀ {S S' : Row} (A : VTy) (δ : LSub),
    S.map OpSig.unmark = S'.map OpSig.unmark → CTyEq (CTy.effOf S A) δ (CTy.effOf S' A) δ
  | [], [], A, δ, _ => CTyEq.refl _ δ
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | o :: S, o' :: S', A, δ, h => by
      simp only [List.map_cons, List.cons.injEq, OpSig.unmark, OpSig.mk.injEq] at h
      obtain ⟨⟨h1, h2, h3, h4, h5, h6, -⟩, hS⟩ := h
      simp only [CTy.effOf, CTyEq]
      refine ⟨h1, h2, h3, ?_, ?_, ?_, CTyEq.effOf_unmark A δ hS⟩
      · rw [h4]; exact TyEq.refl _ δ
      · rw [h5]; exact TyEq.refl _ δ
      · rw [h6]; exact CTyEq.refl _ δ

/-- **The relation at `F_Σ A` does not read the markers.**  `[spec §29a]` -/
theorem semC_effOf_rc {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S S' : Row} {A : VTy}
    (h : S.map OpSig.unmark = S'.map OpSig.unmark) (hS : SemC Δ Γ e (CTy.effOf S A)) :
    SemC Δ Γ e (CTy.effOf S' A) := by
  intro δ γ ls ρ hδ hg
  rw [← cC_tyEq (CTyEq.effOf_unmark A δ h) ls]
  exact hS δ γ ls ρ hδ hg

theorem Row.divB_unmark : ∀ {S S' : Row}, S.map OpSig.unmark = S'.map OpSig.unmark →
    Row.divB S = Row.divB S'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | o :: S, o' :: S', h => by
      have h' := h
      simp only [List.map_cons, List.cons.injEq, OpSig.unmark, OpSig.mk.injEq] at h'
      obtain ⟨⟨h1, h2, h3, h4, h5, -, -⟩, hS⟩ := h'
      have ih := Row.divB_unmark hS
      simp only [Row.divB, CTy.effOf, CTy.divAt] at ih ⊢
      rw [h1, h2, h3, h4, h5, divAt_effOf, divAt_effOf]
      rw [divAt_effOf, divAt_effOf] at ih
      rw [ih]

theorem Row.divB_ofEff_rc {n : UInt32} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
    {cs : Nat → Bool} {S : Row} :
    Row.divB (Row.ofEff n E 0 fs cs ++ S) = Row.divB (Row.ofEff n E 0 fs ++ S) :=
  Row.divB_unmark (Row.unmark_ofEff_append n E 0 fs cs S)

theorem Row.ansOutlives_ofEff_rc {Δ : LifeCtx} {d : Lifetime.Life} {n : UInt32}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {cs : Nat → Bool} {S : Row}
    (h : Row.AnsOutlives Δ d (Row.ofEff n E 0 fs cs ++ S)) :
    Row.AnsOutlives Δ d (Row.ofEff n E 0 fs ++ S) := by
  intro o' ho' ha
  have hm : o'.unmark ∈ (Row.ofEff n E 0 fs cs ++ S).map OpSig.unmark := by
    rw [Row.unmark_ofEff_append]; exact List.mem_map_of_mem ho'
  obtain ⟨o, ho, heq⟩ := List.mem_map.mp hm
  simp only [OpSig.unmark, OpSig.mk.injEq] at heq
  obtain ⟨-, -, hq, -, hB, -, -⟩ := heq
  have ha' : o.abort = false := by simp only [OpSig.abort, hq, hB]; exact ha
  rw [← hB]; exact h o ho ha'

/-- **`[await-c]`'s compatibility**: `await_n` is `[perform]` of the cancellable `a`, then a `case`
whose `inl` arm returns and whose `inr` arm raises the cancel target `c`, each by its own
compatibility lemma.  `[spec §29a]` -/
theorem await_compatC {Δ : LifeCtx} {S : Row} {n : UInt32} {a c : OpSig}
    (hfa : Row.find S n 0 = some a) (ha : a.Cancellable) (haA : a.A = .unit)
    (hfc : Row.find S n 1 = some c) (hc : c.CancelTarget) :
    SemC Δ [] (awaitE n) (CTy.effOf S .unit) := by
  obtain ⟨-, han, hai⟩ := Row.find_mem hfa
  obtain ⟨-, hcn, hci⟩ := Row.find_mem hfc
  obtain ⟨-, hq, hB⟩ := ha
  obtain ⟨-, hcab, hcA⟩ := hc
  have hna : a.abort = false := by simp [OpSig.abort, hq]
  have hP : SemC Δ [] (BoCa.BoLo.performE (opArgE n 0 (.val .unit)))
      (CTy.effOf S (.sum .unit .unit)) := by
    have h := perform_compatC (Δ := Δ) (Γ := []) (V := .val .unit) (o := a)
      (by rw [han, hai]; exact hfa) hna (by rw [haA]; exact unitI_compatC .nil)
    rw [han, hai, hB] at h; exact h
  have h₁ : SemC Δ [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩] (.var 0) (CTy.effOf S .unit) :=
    sub_compatC (S := []) (RowLe.nil S) (ret_compatC (var_compatC (.here (.cons .nil))))
  have h₂ : SemC Δ [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩]
      (BoCa.BoLo.raiseE (opArgE n 1 (.var 0))) (CTy.effOf S .unit) := by
    have h := raise_compatC (Δ := Δ) (Γ := [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩])
      (V := .var 0) (o := c) (B := .unit) (by rw [hcn, hci]; exact hfc) hcab
      (fun _ _ _ _ h => vC_noOwn_of_ownFree (by rw [hcA]; exact .unit) h)
      (by rw [hcA]; exact var_compatC (.here (.cons .nil)))
    rw [hcn, hci] at h; exact h
  exact let_compatC .nil (fun _ s hs => absurd hs List.not_mem_nil)
    (fun _ s hs => absurd hs List.not_mem_nil) hP
    (sumE_compatC (.left .nil) (var_compatC (.here .nil)) h₁ h₂)

/-- `[then]` with its finaliser at the pure row (SPEC §24, option A): `effThen` at `Σ_M = Σ` and
`Σ_D = ∅`, since `F ⋈ ∅ ≤ F` (`ThenLe.nil`).  `[spec §24, §27, §83]` -/
theorem CDerivesX.effThenA {I : JIdx} {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hM : CDerivesX I Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerivesX I Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : CDerivesX I Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    CDerivesX I Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  .effThen (SD := []) hs hNZ hUq hU (RowLe.refl S) (RowLe.nil S)
    (fun _ _ o _ hf hf' _ => by rw [hf] at hf'; cases hf'; exact ThenLe.nil o.fin)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) rfl hM hN hD

/-- `[handle]` at two variables: `handle_n e with (h_ret, hs)`, `h_ret` and `hs` variables of
slots at their types.  An instance of `effHandleV`: `(h_ret, hs)` is a value form, typed by
`[⊗I]`, over slots that are persistent.  `[spec §19, §83]` -/
theorem CDerivesX.effHandle {I : JIdx} {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} {ir ic : Nat} (hAt : I.RowOK (Row.ofEff n E 0 ++ S))
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerivesX I Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
    CDerivesX I Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleV (cs := rcsNil) hAt hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R)) (hc.deadP (clausesTy_persistent S R E finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he

/-- `[handle]` at two variables with cancel rows `fs` and markers `cs`.  `[spec §19, §27, §29a, §83]` -/
theorem CDerivesX.effHandleCs {I : JIdx} {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)}
    (fs : Nat → CTy) (cs : Nat → Bool)
    {n : UInt32} {A R : VTy} {ir ic : Nat} (hAt : I.RowOK (Row.ofEff n E 0 fs cs ++ S))
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E fs))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 fs cs ++ S) = false)
    (he : CDerivesX I Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs cs ++ S) A))) :
    CDerivesX I Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleV (cs := cs) hAt hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R)) (hc.deadP (clausesTy_persistent S R E fs)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he

/-- The unwinding form of `withbor` (1) with its finaliser at the pure row: `withbor1UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19, §72, §83]` -/
theorem CDerivesX.withbor1U {I : JIdx} {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) (hd : CDerivesX I Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerivesX I Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S)) :=
  .withbor1UD (SD := []) x hΓ hx hsc₁ hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S) hS.divB
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-- The unwinding form of `withbor` (2) with its finaliser at the pure row: `withbor2UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19, §23, §83]` -/
theorem CDerivesX.withbor2U {I : JIdx} {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerivesX I Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerivesX I Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S)) :=
  .withbor2UD (SD := []) x hΓ hx hside hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S) hS.divB
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-- The unwinding form of `withbor` (3) with its finaliser at the pure row: `withbor3UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19, §83]` -/
theorem CDerivesX.withbor3U {I : JIdx} {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerivesX I Δ Γ d (.val (.lolli (.mut a A) .unit))) :
    CDerivesX I Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S)) :=
  .withbor3UD (SD := []) x hΓ hx hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S) hS.divB
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-- `[then]` with its finaliser at the pure row (SPEC §24, option A): `effThen` at `Σ_M = Σ` and
`Σ_D = ∅`, since `F ⋈ ∅ ≤ F` (`ThenLe.nil`).  `[spec §24, §27]` -/
theorem CDerives.effThenA {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    CDerives Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  CDerivesX.effThenA hs hNZ hUq hU hM hN hD

/-- `[handle]` at two variables: `handle_n e with (h_ret, hs)`, `h_ret` and `hs` variables of
slots at their types.  An instance of `effHandleV`: `(h_ret, hs)` is a value form, typed by
`[⊗I]`, over slots that are persistent.  `[spec §19]` -/
theorem CDerives.effHandle {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} {ir ic : Nat} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
    CDerives Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) :=
  CDerivesX.effHandle trivial hs hs₁ hr hc hn0 hnS hlen hdv he

/-- `[handle]` at two variables with cancel rows `fs` and markers `cs`.  `[spec §19, §27, §29a]` -/
theorem CDerives.effHandleCs {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)}
    (fs : Nat → CTy) (cs : Nat → Bool)
    {n : UInt32} {A R : VTy} {ir ic : Nat} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E fs))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 fs cs ++ S) = false)
    (he : CDerives Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs cs ++ S) A))) :
    CDerives Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) :=
  CDerivesX.effHandleCs fs cs trivial hs hs₁ hr hc hn0 hnS hlen hdv he

/-- The unwinding form of `withbor` (1) with its finaliser at the pure row: `withbor1UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19, §72]` -/
theorem CDerives.withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerives Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S)) :=
  CDerivesX.withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hd

/-- The unwinding form of `withbor` (2) with its finaliser at the pure row: `withbor2UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19, §23]` -/
theorem CDerives.withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerives Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerives Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S)) :=
  CDerivesX.withbor2U x hΓ hx hside hfree₁ hfree₂ hS hd

/-- The unwinding form of `withbor` (3) with its finaliser at the pure row: `withbor3UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19]` -/
theorem CDerives.withbor3U {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerives Δ Γ d (.val (.lolli (.mut a A) .unit))) :
    CDerives Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S)) :=
  CDerivesX.withbor3U x hΓ hx hfree₁ hfree₂ hS hd

/-- `CDerives.effThenA` in `CDerivesP`.  `[spec §29, §83]` -/
theorem CDerivesP.effThenA {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hM : CDerivesP Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerivesP Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : CDerivesP Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    CDerivesP Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  CDerivesX.effThenA hs hNZ hUq hU hM hN hD

/-- `CDerives.effHandle` in `CDerivesP`.  `[spec §29, §83]` -/
theorem CDerivesP.effHandle {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} {ir ic : Nat} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerivesP Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
    CDerivesP Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) :=
  CDerivesX.effHandle trivial hs hs₁ hr hc hn0 hnS hlen hdv he

/-- `CDerives.effHandleCs` in `CDerivesP`.  `[spec §29, §83]` -/
theorem CDerivesP.effHandleCs {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row} {E : List (Qual × VTy × VTy)}
    (fs : Nat → CTy) (cs : Nat → Bool)
    {n : UInt32} {A R : VTy} {ir ic : Nat} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E fs))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 fs cs ++ S) = false)
    (he : CDerivesP Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs cs ++ S) A))) :
    CDerivesP Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) :=
  CDerivesX.effHandleCs fs cs trivial hs hs₁ hr hc hn0 hnS hlen hdv he

/-- `CDerives.withbor1U` in `CDerivesP`.  `[spec §29, §83]` -/
theorem CDerivesP.withbor1U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) (hd : CDerivesP Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerivesP Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S)) :=
  CDerivesX.withbor1U x hΓ hx hsc₁ hfree₁ hfree₂ hS hd

/-- `CDerives.withbor2U` in `CDerivesP`.  `[spec §29, §83]` -/
theorem CDerivesP.withbor2U {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerivesP Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerivesP Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S)) :=
  CDerivesX.withbor2U x hΓ hx hside hfree₁ hfree₂ hS hd

/-- `CDerives.withbor3U` in `CDerivesP`.  `[spec §29, §83]` -/
theorem CDerivesP.withbor3U {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerivesP Δ Γ d (.val (.lolli (.mut a A) .unit))) :
    CDerivesP Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S)) :=
  CDerivesX.withbor3U x hΓ hx hfree₁ hfree₂ hS hd

/-! ### The delay, stream and finite iterator instances  `[spec §7]`

`D A`, `Stream A` and `Iter A R R'` are `νX. C` at fixed bodies (`CTy.delay`, `CTy.stream`,
`CTy.iter`), each positive and polynomial; their in/out rules and loops are `nuIn`, `nuOut` and
`unfoldN` there. -/

/-- The step's type of `fixD`, `S ⊸ F(A ⊕ S) & F 1`. -/
abbrev stepDC (A S : VTy) : CTy := .arr S (.amp (.ret (.sum A S)) (.ret .unit))

/-- `fixD`'s type, `!U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)`. -/
abbrev fixDTy (A S : VTy) : VTy :=
  .lolli (.bang (.thunk (stepDC A S))) (.bang (.thunk (.arr S (.delay A))))

/-- `fixD = unfold` at `D A`. -/
abbrev fixDV (A : VTy) : Val := unfoldV (CTy.delayBody A)

/-- The step's type of `unfoldS`, `S ⊸ F(A ⊗ S) & F 1`. -/
abbrev stepSC (A S : VTy) : CTy := .arr S (.amp (.ret (.tensor A S)) (.ret .unit))

/-- `unfoldS`'s type, `!U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)`. -/
abbrev unfoldSTy (A S : VTy) : VTy :=
  .lolli (.bang (.thunk (stepSC A S))) (.bang (.thunk (.arr S (.stream A))))

/-- `unfoldS = unfold` at `Stream A`. -/
abbrev unfoldSV (A : VTy) : Val := unfoldV (CTy.streamBody A)

theorem CDerives.delayIn {Δ Γ e A} (h : CDerives Δ Γ e (.comp (delayUnroll A))) :
    CDerives Δ Γ e (.comp (.delay A)) :=
  .nuIn (m := 0) (i := 0) (CTy.delayBody_nuOk A) (by rw [CTy.unrollS_zero, CTy.delay_unroll]; exact h)

theorem CDerives.delayOut {Δ Γ e A} (h : CDerives Δ Γ e (.comp (.delay A))) :
    CDerives Δ Γ e (.comp (delayUnroll A)) := by
  rw [← CTy.delay_unroll]; exact .nuOut (m := 0) (i := 0) (CTy.delayBody_nuOk A) h

/-- Guarded recursion on the delay type: `fixD : !U(S ⊸ F(A ⊕ S) & F 1) ⊸ !U(S ⊸ D A)`. -/
theorem CDerives.fixD {Δ Γ} (A S : VTy) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val (fixDV A)) (.val (fixDTy A S)) := by
  have h := CDerives.unfoldN (Δ := Δ) (CTy.delayBody A) S (CTy.delayBody_nuOk A) (CTy.BindsFresh.of_hasAll rfl S) hΓ
  rwa [unfoldTy, CTy.delayBody_instT] at h

theorem CDerives.streamIn {Δ Γ e A} (h : CDerives Δ Γ e (.comp (streamUnroll A))) :
    CDerives Δ Γ e (.comp (.stream A)) :=
  .nuIn (m := 0) (i := 0) (CTy.streamBody_nuOk A) (by rw [CTy.unrollS_zero, CTy.stream_unroll]; exact h)

theorem CDerives.streamOut {Δ Γ e A} (h : CDerives Δ Γ e (.comp (.stream A))) :
    CDerives Δ Γ e (.comp (streamUnroll A)) := by
  rw [← CTy.stream_unroll]; exact .nuOut (m := 0) (i := 0) (CTy.streamBody_nuOk A) h

/-- Coiteration on the stream type: `unfoldS : !U(S ⊸ F(A ⊗ S) & F 1) ⊸ !U(S ⊸ Stream A)`. -/
theorem CDerives.unfoldS {Δ Γ} (A S : VTy) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val (unfoldSV A)) (.val (unfoldSTy A S)) := by
  have h := CDerives.unfoldN (Δ := Δ) (CTy.streamBody A) S (CTy.streamBody_nuOk A) (CTy.BindsFresh.of_hasAll rfl S) hΓ
  rwa [unfoldTy, CTy.streamBody_instT] at h

/-- The semantic judgment at a judgment form.  `[spec §3]` -/
def SemJ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) : Jdg → Prop
  | .val A => SemV Δ Γ e A
  | .comp C => SemC Δ Γ e C

/-- `[α]` at a value judgment. -/
theorem CDerives.alphaV {Δ Γ e} {A A' : VTy} (h : CDerives Δ Γ e (.val A))
    (hα : VTy.alphaB [] A A' = true) : CDerives Δ Γ e (.val A') := .alpha h hα

/-- `[α]` at a computation judgment. -/
theorem CDerives.alphaC {Δ Γ e} {C C' : CTy} (h : CDerives Δ Γ e (.comp C))
    (hα : CTy.alphaB [] C C' = true) : CDerives Δ Γ e (.comp C') := .alpha h hα

/-- `[α]`'s compatibility lemma: the relation reads α-equivalent types alike (`cC_tyEq`).
`[spec §3]` -/
theorem alpha_compatJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ {j j' : Jdg}, j.alphaB j' = true → SemJ Δ Γ e j → SemJ Δ Γ e j'
  | .val _, .val _, hα, h => alpha_compatC (C := .ret _) (C' := .ret _) hα h
  | .comp _, .comp _, hα, h => alpha_compatC hα h
  | .val _, .comp _, hα, _ | .comp _, .val _, hα, _ => by simp [Jdg.alphaB] at hα

/-- **Every constant is sound**: `constK` at each kind is its constant's compatibility lemma.  A tie
is not read.  `[spec §3]` -/
theorem constK_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (k : ConstKind) (hk : k.OK Δ)
    (hΓ : Ctx.DeadP Γ) : SemJ (ℍ := ℍ) Δ Γ k.E (.val (k.ty Δ.meetOfDom)) := by
  cases k with
  | unitI => exact unitI_compatC hΓ
  | copyBang => exact copyBang_compatC hΓ
  | releaseBang => exact releaseBang_compatC hΓ
  | alloc => exact alloc_compatX hΓ
  | free => exact free_compatX hΓ
  | tokMint => exact tokMint_compatX hΓ
  | tokBurn => exact tokBurn_compatX hΓ
  | swap => exact swap_compatX hΓ
  | copy => exact copy_compatX hΓ
  | releaseImm => exact forgetImm_compatX hΓ
  | releaseMut => exact forgetMut_compatX hΓ
  | releaseUnk => exact forgetUnk_compatX hΓ
  | lit c => exact lit_compatX c hΓ
  | hostOp op => exact hostOp_compatX op hΓ
  | arrNew => exact arrNew_compatX hΓ
  | arrFree => exact arrFree_compatX hΓ
  | arrSize => exact arrSize_compatX hΓ
  | arrReplace => exact arrReplace_compatX hΓ
  | arrLen => exact arrLen_compatX hΓ
  | arrGet => exact arrGet_compatX hΓ
  | arrCopy => exact arrCopy_compatX hΓ
  | arrRelease => exact arrRelease_compatX hΓ
  | countFold => exact countFold_compatX hΓ
  | countTry => exact countTry_compatX hΓ
  | boundedFix => exact boundedFix_compatX hΓ
  | iterate => exact iterate_compatX hk hΓ
  | divFuel => exact divFuel_compatX hk hΓ
  | sliceBorrowM _ _ x =>
      obtain ⟨hA, hB, hf₁, hf₂⟩ := hk; exact sliceBorrowM_compatX x hΓ hA hB hf₁ hf₂
  | sliceBorrowI _ _ x =>
      obtain ⟨hsc, hA, hB, hf₁, hf₂⟩ := hk; exact sliceBorrowI_compatX x hΓ hsc hA hB hf₁ hf₂
  | sliceGetM => exact sliceGetM_compatX hΓ
  | sliceLenM => exact sliceLenM_compatX hΓ
  | sliceSplitI => exact sliceSplitI_compatX hΓ
  | sliceSplitM => exact sliceSplitM_compatX hΓ
  | sliceEmptyI => exact sliceEmptyI_compatX hΓ
  | sliceEmptyM => exact sliceEmptyM_compatX hΓ
  | arrEmpty => exact arrEmpty_compatX hΓ
  | sliceReplaceM => exact sliceReplaceM_compatX hΓ
  | sliceSwapM => exact sliceSwapM_compatX hΓ
  | sliceCopyM => exact sliceCopyM_compatX hΓ hk
  | withbor1 _ _ x =>
      obtain ⟨hx, hsc₁, hf₁, hf₂⟩ := hk; exact withbor1_compatX x hΓ hx hsc₁ hf₁ hf₂
  | withbor2 _ _ x =>
      obtain ⟨hx, hside, hf₁, hf₂⟩ := hk; exact withbor2_compatX x hΓ hx hside hf₁ hf₂
  | withbor3 _ _ _ x => obtain ⟨hx, hf₁, hf₂⟩ := hk; exact withbor3_compatX x hΓ hx hf₁ hf₂
  | withload _ _ _ x => obtain ⟨hx, hf₁, hf₂⟩ := hk; exact withload_compatX x hΓ hx hf₁ hf₂
  | withswap => exact withswap_compatX hΓ
  | withloadU _ _ _ _ x => obtain ⟨_, hf₁, hf₂, hS⟩ := hk; exact withloadU_compatX x hΓ hf₁ hf₂ hS
  | foldImm F y c R =>
      obtain ⟨hF, hG, hyM, hyR, hR⟩ := hk; exact foldImm_compatX F hF hG y c R hΓ hyM hyR hR
  | foldOwn F R => obtain ⟨hF, hG⟩ := hk; exact foldOwn_compatX F hF hG R hΓ
  | foldReuse F R => obtain ⟨hF, hG⟩ := hk; exact foldReuse_compatX F hF hG R hΓ
  | foldOwnG B₀ Rs => exact FoldP.foldOwnG_compatX B₀ hk Rs hΓ
  | unfoldN C S => obtain ⟨hC, hS⟩ := hk; exact unfold_compatX hC S hS hΓ
  | unfoldK => obtain ⟨hC, hG, hS⟩ := hk; exact unfoldK_compatX hC hG hS hΓ

/-- **The Fundamental Property at every judgment index** (SPEC §83): every derivation is sound,
outright when the relaxed rules are off, and under `PinLaw` when they are on (R1's case is
`PinLaw.lendFrame` at the form `ref`, R2's `PinLaw.loopFrame`, each at the induction hypotheses of
its code; `nilDead`'s is `semC_dead`). A tie is not read.  `[spec §3, §29, §83]` -/
theorem fundamentalX {I : JIdx} (hLaw : I.pin = true → PinLaw (ℍ := ℍ)) {Δ : LifeCtx}
    {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesX I Δ Γ e j) : SemJ (ℍ := ℍ) Δ Γ e j := by
  induction h with
  | var h => exact var_compatC h
  | constK k _ hk hΓ => exact constK_compatX k hk hΓ
  | tensorI hs _ _ ih₁ ih₂ => exact tensorI_compatC hs ih₁ ih₂
  | sumI₁ _ ih => exact sumI₁_compatC ih
  | sumI₂ _ ih => exact sumI₂_compatC ih
  | thunkF _ ih => exact thunkF_compatC ih
  | thunkV hC _ ih => exact thunkV_compatC hC ih
  | ret _ ih => exact ret_compatC ih
  | bind hs _ _ ihM ihN => exact bind_compatC hs ihM ihN
  | force h hT => exact force_compatC h hT
  | lam _ ih => exact lam_compatC ih
  | lamDead _ ih => exact lamDead_compatC ih
  | app hs _ hx ih => exact app_compatC hs ih hx
  | withI _ _ ihM ihN => exact withI_compatC ihM ihN
  | proj₁ _ ih => exact proj₁_compatC ih
  | proj₂ _ ih => exact proj₂_compatC ih
  | topI => exact topI_compatC
  | unitE hs _ _ ihV ihM => exact unitE_compatC hs ihV ihM
  | tensorE hs _ _ ihV ihM => exact tensorE_compatC hs ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact sumE_compatC hs ihV ih₁ ih₂
  | zeroE hs _ ihV => exact zeroE_compatC hs ihV
  | allI hbx hΔx hΓx _ ih =>
      exact allI_compatC hbx hΔx hΓx ((semC_liveEq (.dead (LiveEq.refl _))).mp ih)
  | allE _ hlt ih => exact allE_compatC ih hlt
  | bangThunkF hp _ ih => exact bangThunkF_compatC hp ih
  | bangThunkV hp hC _ ih => exact bangThunkV_compatC hp hC ih
  | codeI _ hok ih => exact codeI_compatC ih hok
  | codeIB hp _ hok ih => exact codeIB_compatC hp ih hok
  | codeErase _ ih => exact codeErase_compatC ih
  | codeEraseB _ ih => exact codeEraseB_compatC ih
  | bangE _ ih => exact bangE_compatC ih
  | boxI _ hΓ ih => exact boxI_compatC ih hΓ
  | boxE _ ih => exact boxE_compatC ih
  | immSub _ hle ih => exact immSub_compatC ih hle
  | mutSub _ hle ih => exact mutSub_compatC ih hle
  | reify _ _ _ _ _ hS hcl _ hΓ ihres => exact reify_compatX hS hcl ihres hΓ
  | withborUD k x hΓ _ hk hf₁ hf₂ hS hMS hDS hSv hP _ ihd =>
      exact withborUD_compatX k x hΓ hk hf₁ hf₂ hS hMS hDS hSv hP ihd
  | sliceBorrowMU x hΓ hA hB hf₁ hf₂ hS _ ihd =>
      exact sliceBorrowMU_compatX x hΓ hA hB hf₁ hf₂ hS ihd
  | sliceBorrowIU x hΓ hsc hA hB hf₁ hf₂ hS _ ihd =>
      exact sliceBorrowIU_compatX x hΓ hsc hA hB hf₁ hf₂ hS ihd
  | lolliE hs _ _ iha ihf => exact lolliE_compatX hs iha ihf
  | allEV _ hlt ih => exact allE_compatX ih hlt
  | ofRet _ ih => exact ih
  | roll hA hc _ ih => exact roll_compatX hA hc ih
  | unroll _ ih => exact unroll_compatX ih
  | nuIn hC _ ih => exact nuIn_compatX hC ih
  | nuOut hC _ ih => exact nuOut_compatX hC ih
  | nuOutK hC hG hS hGf h => exact nuOutK_compatX hC hG hS hGf h
  | effSub hle _ ih => exact sub_compatC hle ih
  | effPerform _ hf hna _ _ ih => exact perform_compatC hf hna ih
  | effAwait _ hΓ hfa ha haA hfc hc => exact semC_dead .nil hΓ (await_compatC hfa ha haA hfc hc)
  | effRaise _ hf ha _ hd _ ih => exact raise_compatC hf ha (fun _ _ _ _ h => vC_noOwn_of_ownFree hd h) ih
  | effLet hs hW hU _ _ ihM ihN => exact let_compatC hs hW hU ihM ihN
  | effThen hs hNZ _ hU hMS hDS hfin hP hSD _ _ _ ihM ihN ihD =>
      exact then_compatC hs hNZ hU hMS hDS
        (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc)) hP hSD ihM ihN ihD
  | @effThenDiv _ _ _ _ _ _ _ _ _ _ SM SD hs hNZ _ hU hMS hDS hfin hP hcap _ _ _ ihM ihN ihD =>
      cases hSD : Row.divB SD
      · exact then_compatC hs hNZ hU hMS hDS
          (fun n i o o' h₁ h₂ hc => hfin n i o o' h₁ h₂ (OpSig.finRead_of_capB hc)) hP hSD ihM ihN ihD
      · exact then_compatC_div hs hNZ hU hMS hDS hP hcap hSD ihM ihN ihD
  | effHandleV _ hs hd hH _ hn0 hnS hlen hdv _ ihc ihe =>
      exact handleV_compatC hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
        (semC_effOf_rc (Row.unmark_ofEff_append _ _ _ _ _ _) ihe)
  | effHandleVB _ hs hd hH _ hn0 hnS hlen hdv _ hΓd hSd ihc ihe =>
      exact handleV_compatCB hs hd hH ihc hn0 hnS hlen (by rwa [Row.divB_ofEff_rc] at hdv)
        (semC_effOf_rc (Row.unmark_ofEff_append _ _ _ _ _ _) ihe) hΓd
        (Row.ansOutlives_ofEff_rc hSd)
  | effHandleT _ hs hd hHr hHc _ hn0 hnd hnS hlen hSN hLin _ ihc ihe =>
      exact handleT_compatC hs hd hHr hHc ihc hn0 hnd hnS hlen hSN hLin ihe
  | effHandleL _ hs hd hHr hHw hHn _ hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin _ ihc ihe =>
      exact handleL_compatC hs hd hHr hHw hHn ihc hn0 hnd hnS hlen hNZ hCancel hSW hSu hFin ihe
  | letPoly b hcl _ _ _ ihN => exact letPoly_compatC (Val.lam b) hcl ihN
  | alpha _ hα ih => exact alpha_compatJ hα ih
  | lendR hPin hb hx hbx hΔx hT hB hBn hside hS hM1 hcb hdc _ hM ihd ihM =>
      exact (hLaw hPin).lendFrame _ _ _ _ _ _ _ _ _ _ (.ref hT hside)
        hb hx hbx hΔx hB hBn hS hM1 hcb hdc ihd (hM.mono (JIdx.le_pin _)) ihM
  | lendLoopR hPin hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c hN hK hs0 ihN ihK ihs0 =>
      exact (hLaw hPin).loopFrame _ _ _ _ _ _ _ _ _ hx hbx hΔx hA hB hR hBn hRn hsc hN1 hK1 hs0c
        (hN.mono (JIdx.le_pin _)) (hK.mono (JIdx.le_pin _)) (hs0.mono (JIdx.le_pin _)) ihN ihK ihs0
  | @nilDead _ _ _ j _ hΓ _ ih => cases j <;> exact semC_dead .nil hΓ ih

/-- **Fundamental Property** of the CBPV judgment over the typed world at CBPV types:
`fundamentalX` at `{}`, where its hypothesis is vacuous.  `[spec §3]` -/
theorem fundamentalC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : SemJ Δ Γ e j :=
  fundamentalX (fun h => absurd h Bool.false_ne_true) h

/-- **The stop lemma** (BOXED-κ's premise, `[spec §28]`): a computation typed at `F_Σ A` under
`Γ`, with `Δ ⊨ Γ ⊐ @d` and every non-abortive answer type of `Σ` outliving `@d`, has the
continuation's share in `Res_{δ(d)}` at every stop, at every `δ`. No premise asks that no lend be
open at a stop: `CDerives` types a lend's callback at the pure row or at a row of abortive
operations, and `wpG`'s `↭` already excludes a lend open at a stop. -/
theorem stop_lemma {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {S : Row} {A : VTy}
    {d : Lifetime.Life} (hSd : Row.divB S = false) (hder : CDerives Δ Γ M (.comp (CTy.effOf S A)))
    (hΓ : CtxOutlives Δ Γ d) (hS : Row.AnsOutlives Δ d S) : SemCS Δ Γ M S A d :=
  stop_sem hSd (fundamentalC hder) hΓ hS

/-! ### Adequacy -/

/-- `∅ ↭ ρ⁺` and `ρ⁺|own = ∅` force `ρ⁺ = ∅` (`Adequacy.reclaim`'s argument). -/
theorem reclaim (ρ : WRes) (hupd : ResU.UpdV PMap.empty ρ) (hno : NoOwn ρ) : ρ = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  cases hg : ρ.get l with
  | none => rfl
  | some ψ =>
      exfalso
      obtain ⟨σ, hσ⟩ := hupd.2.2
      obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ hg
      have hfa : ρ.FlatAt l χ := (ResU.flatAt_iff hσ l χ).mpr hχ
      rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
      · have hko : ψ.kind = Kind.own := by rw [← hk]; exact CellU.kind_ownOf w
        have hr : (ρ.restrict Kind.own).get l = some ψ :=
          ResU.restrict_eq_some.mpr ⟨hg, hko⟩
        rw [hno, PMap.empty_get] at hr
        simp at hr
      · have hemp := (hupd.1.1 l s w ξ hξ).mpr hfa
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hemp
        simp at hemp
      · obtain ⟨w', ξ', h', hP', hfa'⟩ := (hupd.1.2 l b P).mpr ⟨w, ξ, hξ, hP, hfa⟩
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hfa'
        simp at hfa'

/-- `[CONF]` Theorem 3.2 at this world's `wpTS`, at the empty list. -/
theorem theorem32 (e : Expr) (P : Val → Prop)
    (hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes)) :
    ∃ v : Val, BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val v) ∧ P v := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', -, -,
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, -, -, -, -, h12⟩ :=
    wpTS_angelic _ hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty
      (ResU.comp_empty_right _) TW.empty htg
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

/-- `[CONF]` Corollary 3.3 at `SemC … (F 1)`. -/
theorem corollary33 (e : Expr) (hsem : SemC LifeCtx.empty [] e (.ret .unit)) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) := by
  have hwp := hsem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have hwp' : wpTS [] e (fun _ v => Fig16.BoLo.pure (v = Val.unit)) (PMap.empty : WRes) := by
    have he : substAll [] e = e := Adequacy.psub_nil 0 e
    rw [he] at hwp
    exact hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32 e (· = Val.unit) hwp'
  subst hv
  exact hsteps

/-- **Adequacy**: a closed computation of type `F 1` runs from the empty memory to `()` and the
empty memory.  `[spec §3]` -/
theorem adequacyC {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit))) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  corollary33 e (fundamentalC h)

/-! ### A closed program through `U`, `&`, `⊤`, `force` and a projection -/

/-- `thunk ⟨return (), ⟨⟩⟩ to t. π₁ (force t) : F 1`.  The thunk of a `&` is the pair itself,
and forcing it is using it. -/
def exProg : Expr :=
  .app (.val (.lam (.app (.var 0) (.val (.inj₁ .unit))))) (withPair (.val .unit) (.val .unit))

theorem exProg_derives : CDerives LifeCtx.empty [] exProg (.comp (.ret .unit)) :=
  .bind (Γ₁ := []) (Γ₂ := []) .nil
    (.ret (.thunkV rfl (.withI (.ret (.unitI (.cons (.cons .nil)))) .topI)))
    (.proj₁ (.force (T := .thunk _) (C := .amp (.ret .unit) .top) (.here .nil) rfl))

theorem exProg_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem exProg Adequacy.emptyMem (.val .unit) :=
  adequacyC exProg_derives

end BoCa.Fig16.LogRel.Core

end
