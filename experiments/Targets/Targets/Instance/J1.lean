import Targets.Instance.J1Checks
import Targets.Base.Support
import Targets.Base.Closed

/-!
# The Instance — `J₁`, tier 1's typing (TIER1-PLAN §2; decision D5)

`J₁` is Core's kernel (SPEC §24) over the open types, with the row `∀`.

* **Core's kernel.**  At judgements free of the row `∀`, `J₁` is `CDerives` at every admissible
  instance: `J₁.read = tier1` (`j1_read`).  So the let of a polymorphic function is Core's
  `[let-poly]` (`CDerives.letPoly`), and a handler at clause values is Core's `[handle]`
  (`CDerives.effHandleV`).
* **The row `∀`.**  Rows are erased, so a value of `U(∀ρ:k. C)` or `!U(∀ρ:k. C)` is one closed
  λ-value related at every instance `C[r/ρ]`, `r` admissible at `k`.  A context slot of such a type
  holds that value: `J₁` types a term with such slots when Core types the term with the slots'
  values in place of their variables (`fillS`), the slots dead, at every closing of the slots by
  closed λ-values that Core types at every instance (`Closing`).  A judgement at such a type is Core
  typing the term, a λ-value, at every instance.  This is let-polymorphism by substitution, the
  reading of `[let-poly]` at an open judgement.
* **What it gives at our instance**: the let law at every row (`letLaw_ourInst_J₁`), subeffecting
  at every well-formed target (`subClosed_ourInst_J₁`), and Core's closed programs
  (`coreClosed_J₁`), from which the interaction gets S0, S2, S3 and S4 (`Targets/I/J1.lean`).
Typing work: none of it inverts `CDerives`; each fact constructs derivations or reads `J₁`'s
definition.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowCtx RowEnv RowCon RVar RowAt rowAt_nil
  orowRF_den TypingJ tier1 OutJ rowLink_orowRF closedAt_of_derives)

/-! ### Typing systems that read their row variables as themselves -/

/-- The typing system of a judgement, at Core's outlives judgements, its row variables read as
themselves. -/
def OurTyping.ofDer (D : RowCtx → LifeCtx → Ctx OVTy → Expr → OJdg → Prop) : OurTyping orowRF :=
  ⟨D, OutJ.core, fun _ η => η⟩

/-- **A typing system whose closed programs are Core's**: at a row context of `any` variables, a
closed derivation at a computation type is a `CDerives` derivation of the type's instance with the
row variables read as empty rows. -/
def CoreClosed (J : OurTyping orowRF) : Prop :=
  ∀ Θ e C, (∀ p ∈ Θ, p.2 = anyCon) → J.der Θ LifeCtx.empty [] e (.comp C) →
    CDerives LifeCtx.empty [] e (.comp (C.den (fun _ => [])))

/-- Today's kernel's closed programs are Core's. -/
theorem coreClosed_tier1Open : CoreClosed tier1Open := fun _ _ _ hΘ hd =>
  (hd.2.2 _ (models_anyCon_nil hΘ)).toCDerives

/-! ### Polymorphic function types -/

/-- A row is an admissible instance of a constraint. -/
def AdmRow (k : RowCon) (r : Row) : Prop := k.cls.Admits r ∧ ∀ o ∈ r, k.adm o

/-- The empty row is an admissible instance of every constraint. -/
theorem admRow_nil (k : RowCon) : AdmRow k [] := by
  refine ⟨?_, fun _ h => absurd h List.not_mem_nil⟩
  rcases k with ⟨cls, adm⟩
  cases cls with
  | abortive => intro o h; exact absurd h List.not_mem_nil
  | resumeOnce => intro o h; exact absurd h List.not_mem_nil
  | any => exact row_nu_nil

/-- A polymorphic function type: `U(∀ρ:k. C)` or `!U(∀ρ:k. C)`. -/
def OVTy.isPoly : OVTy → Bool
  | .thunk (.allR _ _ _) => true
  | .bang (.thunk (.allR _ _ _)) => true
  | _ => false

/-- The computation types a polymorphic function type's values are related at, at `η`: its body
with its variable read as each admissible row. -/
def OVTy.PolyInst : OVTy → RowEnv → CTy → Prop
  | .thunk (.allR ρ k C), η, C' => ∃ r, AdmRow k r ∧ C' = C.den (Function.update η ρ r)
  | .bang (.thunk (.allR ρ k C)), η, C' => ∃ r, AdmRow k r ∧ C' = C.den (Function.update η ρ r)
  | _, _, _ => False

/-- A polymorphic function type has an instance at every row environment. -/
theorem OVTy.polyInst_nonempty : ∀ {A : OVTy}, A.isPoly = true → ∀ η, ∃ C', A.PolyInst η C'
  | .thunk (.allR _ k _), _, _ => ⟨_, [], admRow_nil k, rfl⟩
  | .bang (.thunk (.allR _ k _)), _, _ => ⟨_, [], admRow_nil k, rfl⟩

/-- A computation type that is no returner: an arrow, a `&`, `⊤`, a lifetime `∀` or a `ν`. -/
def OCTy.NotRet : OCTy → Prop
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => True
  | _ => False

theorem OCTy.isRet_den_of_notRet {C : OCTy} (h : C.NotRet) (η : RowEnv) : (C.den η).isRet = false := by
  cases C <;> first | rfl | exact absurd h id

/-- A polymorphic function type's body is free of the row `∀` and no returner (a function). -/
def OVTy.PolyOK : OVTy → Prop
  | .thunk (.allR _ _ C) => C.RFree ∧ C.NotRet
  | .bang (.thunk (.allR _ _ C)) => C.RFree ∧ C.NotRet
  | _ => False

/-- A `!` type. -/
def OVTy.isBang : OVTy → Bool
  | .bang _ => true
  | _ => false

/-- The slot and judgement types `J₁` reads: free of the row `∀`, or polymorphic function types. -/
def OVTy.J1OK (A : OVTy) : Prop := A.RFree ∨ (A.isPoly = true ∧ A.PolyOK)

theorem OVTy.isPoly_of_rFree : ∀ {A : OVTy}, A.RFree → A.isPoly = false
  | .thunk (.allR _ _ _), h => absurd h id
  | .bang (.thunk (.allR _ _ _)), h => absurd h id
  | .unit, _ | .tensor _ _, _ | .zero, _ | .sum _ _, _ | .ref _, _ | .imm _ _, _ | .mut _ _, _
  | .box _ _, _ | .unk, _ | .tvar _, _ | .mu _, _ | .int _, _ | .fam _, _ | .opq _, _ => rfl
  | .thunk (.ret _), _ | .thunk (.arr _ _), _ | .thunk (.amp _ _), _ | .thunk .top, _
  | .thunk (.all _ _ _), _ | .thunk (.nu _), _ | .thunk (.eff _ _ _ _ _ _), _
  | .thunk (.effF _ _), _ => rfl
  | .bang .unit, _ | .bang (.tensor _ _), _ | .bang .zero, _ | .bang (.sum _ _), _
  | .bang (.ref _), _ | .bang (.imm _ _), _ | .bang (.mut _ _), _ | .bang (.box _ _), _
  | .bang (.bang _), _ | .bang .unk, _ | .bang (.tvar _), _ | .bang (.mu _), _ | .bang (.int _), _
  | .bang (.fam _), _ | .bang (.opq _), _ => rfl
  | .bang (.thunk (.ret _)), _ | .bang (.thunk (.arr _ _)), _ | .bang (.thunk (.amp _ _)), _
  | .bang (.thunk .top), _ | .bang (.thunk (.all _ _ _)), _ | .bang (.thunk (.nu _)), _
  | .bang (.thunk (.eff _ _ _ _ _ _)), _ | .bang (.thunk (.effF _ _)), _ => rfl

/-! ### Closing the polymorphic slots -/

/-- A context's instance for Core: a live polymorphic slot is dead (its value is put in place of
its variable), every other slot is its type's instance. -/
def octxStrip (η : RowEnv) (Γ : Ctx OVTy) : Ctx VTy :=
  Γ.map fun s => if s.live && s.ty.isPoly then ⟨.unit, false⟩ else ⟨s.ty.den η, s.live⟩

theorem octxStrip_of_rFree (η : RowEnv) :
    ∀ {Γ : Ctx OVTy}, octxRFree Γ → octxStrip η Γ = octxDen η Γ
  | [], _ => rfl
  | s :: Γ, h => by
      have hs : s.ty.isPoly = false := OVTy.isPoly_of_rFree (h s (List.mem_cons_self ..))
      have ih := octxStrip_of_rFree η (Γ := Γ) (fun s' h' => h s' (List.mem_cons_of_mem _ h'))
      simp only [octxStrip, octxDen, List.map_cons, hs, Bool.and_false, Bool.false_eq_true,
        if_false] at ih ⊢
      rw [ih]

/-- `e` with the closed value `σ i` in place of each variable `i` (counted outside `k` binders) it
gives one for, every other variable where it was. -/
def fillS (σ : ℕ → Option Val) : ℕ → Expr → Expr
  | k, .var i => if i < k then .var i else
      (match σ (i - k) with | some W => W.1 | none => .var i)
  | _, .unit => .unit
  | k, .pair a b => .pair (fillS σ k a) (fillS σ k b)
  | k, .inj₁ a => .inj₁ (fillS σ k a)
  | k, .inj₂ a => .inj₂ (fillS σ k a)
  | k, .lam b => .lam (fillS σ (k + 1) b)
  | _, .loc ℓ => .loc ℓ
  | _, .prim p => .prim p
  | k, .seq a b => .seq (fillS σ k a) (fillS σ k b)
  | k, .letpair a b => .letpair (fillS σ k a) (fillS σ (k + 2) b)
  | k, .case a b c => .case (fillS σ k a) (fillS σ (k + 1) b) (fillS σ (k + 1) c)
  | k, .app f a => .app (fillS σ k f) (fillS σ k a)

theorem fillS_none : ∀ (k : ℕ) (e : Expr), fillS (fun _ => none) k e = e
  | k, .var i => by unfold fillS; split <;> rfl
  | _, .unit => rfl
  | k, .pair a b => by simp only [fillS, fillS_none k a, fillS_none k b]
  | k, .inj₁ a => by simp only [fillS, fillS_none k a]
  | k, .inj₂ a => by simp only [fillS, fillS_none k a]
  | k, .lam b => by simp only [fillS, fillS_none (k + 1) b]
  | _, .loc _ => rfl
  | _, .prim _ => rfl
  | k, .seq a b => by simp only [fillS, fillS_none k a, fillS_none k b]
  | k, .letpair a b => by simp only [fillS, fillS_none k a, fillS_none (k + 2) b]
  | k, .case a b c => by simp only [fillS, fillS_none k a, fillS_none (k + 1) b, fillS_none (k + 1) c]
  | k, .app f a => by simp only [fillS, fillS_none k f, fillS_none k a]

/-- A term closed below the binders is left as it is. -/
theorem fillS_closed (σ : ℕ → Option Val) : ∀ (e : Expr) (k : ℕ), closedAt k e = true →
    fillS σ k e = e
  | .var i, k, h => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [fillS, if_pos h]
  | .unit, _, _ => rfl
  | .pair a b, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [fillS, fillS_closed σ a k h.1, fillS_closed σ b k h.2]
  | .inj₁ a, k, h => by simp only [fillS, fillS_closed σ a k h]
  | .inj₂ a, k, h => by simp only [fillS, fillS_closed σ a k h]
  | .lam b, k, h => by simp only [fillS, fillS_closed σ b (k + 1) h]
  | .loc _, _, _ => rfl
  | .prim _, _, _ => rfl
  | .seq a b, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [fillS, fillS_closed σ a k h.1, fillS_closed σ b k h.2]
  | .letpair a b, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [fillS, fillS_closed σ a k h.1, fillS_closed σ b (k + 2) h.2]
  | .case a b c, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [fillS, fillS_closed σ a k h.1.1, fillS_closed σ b (k + 1) h.1.2,
        fillS_closed σ c (k + 1) h.2]
  | .app f a, k, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [fillS, fillS_closed σ f k h.1, fillS_closed σ a k h.2]

/-- A slot that is not filled, at the front: the rest is filled one binder further out. -/
theorem fillS_scons_none (σ : ℕ → Option Val) :
    ∀ (e : Expr) (k : ℕ), fillS (VTy.scons none σ) k e = fillS σ (k + 1) e
  | .var i, k => by
      rcases Nat.lt_trichotomy i k with h | rfl | h
      · simp only [fillS, if_pos h, if_pos (Nat.lt_succ_of_lt h)]
      · simp only [fillS, Nat.lt_irrefl, if_false, Nat.sub_self, VTy.scons, if_pos (Nat.lt_succ_self i)]
      · have h₁ : ¬ i < k := by omega
        have h₂ : ¬ i < k + 1 := by omega
        have h₃ : i - k = (i - (k + 1)) + 1 := by omega
        simp only [fillS, if_neg h₁, if_neg h₂, h₃, VTy.scons]
  | .unit, _ => rfl
  | .pair a b, k => by simp only [fillS, fillS_scons_none σ a k, fillS_scons_none σ b k]
  | .inj₁ a, k => by simp only [fillS, fillS_scons_none σ a k]
  | .inj₂ a, k => by simp only [fillS, fillS_scons_none σ a k]
  | .lam b, k => by simp only [fillS, fillS_scons_none σ b (k + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, k => by simp only [fillS, fillS_scons_none σ a k, fillS_scons_none σ b k]
  | .letpair a b, k => by simp only [fillS, fillS_scons_none σ a k, fillS_scons_none σ b (k + 2)]
  | .case a b c, k => by
      simp only [fillS, fillS_scons_none σ a k, fillS_scons_none σ b (k + 1),
        fillS_scons_none σ c (k + 1)]
  | .app f a, k => by simp only [fillS, fillS_scons_none σ f k, fillS_scons_none σ a k]

/-- **A filled slot at the front is the polymorphic let's premise term**: filling it with the closed
value `V` is substituting `V` for it and keeping its slot (`CDerives.letPoly`). -/
theorem fillS_scons_some {σ : ℕ → Option Val} (hσ : ∀ i W, σ i = some W → closedAt 0 W.1 = true)
    {V : Val} (hV : closedAt 0 V.1 = true) :
    ∀ (e : Expr) (k : ℕ),
      fillS (VTy.scons (some V) σ) k e = ((fillS σ (k + 1) e).subst k V).shift 1 k
  | .var i, k => by
      rcases Nat.lt_trichotomy i k with h | rfl | h
      · have h₂ : ¬ i = k := by omega
        have h₃ : ¬ i > k := by omega
        simp only [fillS, if_pos h, if_pos (Nat.lt_succ_of_lt h), Expr.subst, if_neg h₂, if_neg h₃,
          Expr.shift]
      · simp only [fillS, Nat.lt_irrefl, if_false, Nat.sub_self, VTy.scons,
          if_pos (Nat.lt_succ_self i), Expr.subst]
        rw [if_pos trivial, shift_closedAt V.1 1 hV (Nat.zero_le _)]
      · have h₁ : ¬ i < k := by omega
        have h₂ : ¬ i < k + 1 := by omega
        have h₃ : i - k = (i - (k + 1)) + 1 := by omega
        simp only [fillS, if_neg h₁, if_neg h₂, h₃, VTy.scons]
        cases hs : σ (i - (k + 1)) with
        | none =>
            have h₄ : ¬ i = k := by omega
            have h₅ : ¬ (i - 1 < k) := by omega
            simp only [Expr.subst, if_neg h₄, if_pos h, Expr.shift, if_neg h₅]
            congr 1; omega
        | some W =>
            have hW := hσ _ W hs
            simp only
            rw [subst_closedAt W.1 V hW (Nat.zero_le _), shift_closedAt W.1 1 hW (Nat.zero_le _)]
  | .unit, _ => rfl
  | .pair a b, k => by
      simp only [fillS, Expr.subst, Expr.shift, fillS_scons_some hσ hV a k, fillS_scons_some hσ hV b k]
  | .inj₁ a, k => by simp only [fillS, Expr.subst, Expr.shift, fillS_scons_some hσ hV a k]
  | .inj₂ a, k => by simp only [fillS, Expr.subst, Expr.shift, fillS_scons_some hσ hV a k]
  | .lam b, k => by
      simp only [fillS, Expr.subst, Expr.shift, val_shift_closed hV, fillS_scons_some hσ hV b (k + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, k => by
      simp only [fillS, Expr.subst, Expr.shift, fillS_scons_some hσ hV a k, fillS_scons_some hσ hV b k]
  | .letpair a b, k => by
      simp only [fillS, Expr.subst, Expr.shift, val_shift_closed hV, fillS_scons_some hσ hV a k,
        fillS_scons_some hσ hV b (k + 2)]
  | .case a b c, k => by
      simp only [fillS, Expr.subst, Expr.shift, val_shift_closed hV, fillS_scons_some hσ hV a k,
        fillS_scons_some hσ hV b (k + 1), fillS_scons_some hσ hV c (k + 1)]
  | .app f a, k => by
      simp only [fillS, Expr.subst, Expr.shift, fillS_scons_some hσ hV f k, fillS_scons_some hσ hV a k]

/-- The live polymorphic slot `i` of `Γ`. -/
def PolyAt (Γ : Ctx OVTy) (i : ℕ) (s : Slot OVTy) : Prop :=
  Γ[i]? = some s ∧ s.live = true ∧ s.ty.isPoly = true

/-- **The closings of a context's live polymorphic slots at `η`**: each by a closed λ-value Core
types at every instance of the slot's type, and nothing else filled. -/
def Closing (Δ : LifeCtx) (Γ : Ctx OVTy) (η : RowEnv) (σ : ℕ → Option Val) : Prop :=
  ∀ i, (σ i = none ↔ ∀ s, ¬ PolyAt Γ i s) ∧
    ∀ s W, PolyAt Γ i s → σ i = some W → ∃ b, W = Val.lam b ∧ closedAt 0 W.1 = true ∧
      ∀ C', s.ty.PolyInst η C' → CDerives Δ [] (.val W) (.comp C')

theorem Closing.closed {Δ : LifeCtx} {Γ : Ctx OVTy} {η : RowEnv} {σ : ℕ → Option Val}
    (h : Closing Δ Γ η σ) : ∀ i W, σ i = some W → closedAt 0 W.1 = true := by
  intro i W hW
  have hs : ¬ ∀ s, ¬ PolyAt Γ i s := fun hn => by rw [(h i).1.mpr hn] at hW; cases hW
  push Not at hs
  obtain ⟨s, hs⟩ := hs
  obtain ⟨b, -, hc, -⟩ := (h i).2 s W hs hW
  exact hc

/-- A context with no live polymorphic slot is closed by filling nothing. -/
theorem closing_none {Δ : LifeCtx} {Γ : Ctx OVTy} {η : RowEnv}
    (hΓ : ∀ s ∈ Γ, s.live = true → s.ty.isPoly = false) : Closing Δ Γ η (fun _ => none) := by
  intro i
  refine ⟨⟨fun _ s ⟨hs, hl, hp⟩ => ?_, fun _ => rfl⟩, fun _ _ _ h => by cases h⟩
  rw [hΓ s (List.mem_of_getElem? hs) hl] at hp
  cases hp

/-- A closing that fills nothing fills nothing. -/
theorem fillS_of_closing_noPoly {Δ : LifeCtx} {Γ : Ctx OVTy} {η : RowEnv} {σ : ℕ → Option Val}
    (h : Closing Δ Γ η σ) (hΓ : ∀ s ∈ Γ, s.live = true → s.ty.isPoly = false) (k : ℕ) (e : Expr) :
    fillS σ k e = e := by
  have hσ : σ = fun _ => none := by
    funext i
    refine (h i).1.mpr fun s ⟨hs, hl, hp⟩ => ?_
    rw [hΓ s (List.mem_of_getElem? hs) hl] at hp
    cases hp
  rw [hσ]; exact fillS_none k e

/-- A closing extends past a live polymorphic slot at the front. -/
theorem closing_cons_poly {Δ : LifeCtx} {Γ : Ctx OVTy} {η : RowEnv} {σ : ℕ → Option Val}
    (h : Closing Δ Γ η σ) {A : OVTy} (hA : A.isPoly = true) {b : Expr}
    (hc : closedAt 0 (Val.lam b).1 = true)
    (hb : ∀ C', A.PolyInst η C' → CDerives Δ [] (.val (Val.lam b)) (.comp C')) :
    Closing Δ (⟨A, true⟩ :: Γ) η (VTy.scons (some (Val.lam b)) σ) := by
  intro i
  cases i with
  | zero =>
      refine ⟨⟨fun h' => by simp [VTy.scons] at h',
        fun hn => absurd (show PolyAt (⟨A, true⟩ :: Γ) 0 ⟨A, true⟩ from ⟨rfl, rfl, hA⟩) (hn _)⟩, ?_⟩
      rintro s W ⟨hs, -, -⟩ hW
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      simp only [VTy.scons, Option.some.injEq] at hW
      subst hW
      exact ⟨b, rfl, hc, hb⟩
  | succ i =>
      have hpi : ∀ s, PolyAt (⟨A, true⟩ :: Γ) (i + 1) s ↔ PolyAt Γ i s := fun s => by
        simp [PolyAt]
      refine ⟨?_, fun s W hs hW => (h i).2 s W ((hpi s).mp hs) hW⟩
      simp only [VTy.scons]
      exact ⟨fun hn s hs => (h i).1.mp hn s ((hpi s).mp hs),
        fun hn => (h i).1.mpr fun s hs => hn s ((hpi s).mpr hs)⟩

/-- A closing extends past a slot at the front that is not a live polymorphic one. -/
theorem closing_cons_mono {Δ : LifeCtx} {Γ : Ctx OVTy} {η : RowEnv} {σ : ℕ → Option Val}
    (h : Closing Δ Γ η σ) {s₀ : Slot OVTy} (hs₀ : (s₀.live && s₀.ty.isPoly) = false) :
    Closing Δ (s₀ :: Γ) η (VTy.scons none σ) := by
  intro i
  cases i with
  | zero =>
      refine ⟨⟨fun _ s ⟨hs, hl, hp⟩ => ?_, fun _ => rfl⟩, fun _ _ _ h' => by cases h'⟩
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs
      simp [hl, hp] at hs₀
  | succ i =>
      have hpi : ∀ s, PolyAt (s₀ :: Γ) (i + 1) s ↔ PolyAt Γ i s := fun s => by
        simp [PolyAt]
      refine ⟨?_, fun s W hs hW => (h i).2 s W ((hpi s).mp hs) hW⟩
      simp only [VTy.scons]
      exact ⟨fun hn s hs => (h i).1.mp hn s ((hpi s).mp hs),
        fun hn => (h i).1.mpr fun s hs => hn s ((hpi s).mpr hs)⟩

/-! ### `J₁` -/

/-- The judgements `J₁` reads: a computation type free of the row `∀`, or a value type `J₁`
reads as a slot. -/
def J1JOK : OJdg → Prop
  | .comp C => C.RFree
  | .val A => A.J1OK

/-- **Core's judgement at an instance**: Core's kernel at the instance, or, at a polymorphic
function type, a λ-value Core types at every instance of the type, over a persistent context at
`!U(∀ρ:k. C)`. -/
def J1Core (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (η : RowEnv) : OJdg → Prop
  | .comp C => CDerives Δ Γ e (.comp (C.den η))
  | .val A => if A.isPoly = true then
        ∃ b, e = .lam b ∧ (A.isBang = true → Persistent Γ) ∧
          ∀ C', A.PolyInst η C' → CDerives Δ Γ (.val (Val.lam b)) (.comp C')
      else CDerives Δ Γ e (.val (A.den η))

/-- **`J₁`'s judgement**: the context's slots and the judgement are free of the row `∀` or
polymorphic function types, and at every admissible instance and every closing of the context's
live polymorphic slots, Core's kernel types the term with the closing's values in place. -/
def J1Der (Θ : RowCtx) (Δ : LifeCtx) (Γ : Ctx OVTy) (e : Expr) (j : OJdg) : Prop :=
  (∀ s ∈ Γ, s.ty.J1OK) ∧ J1JOK j ∧
    ∀ η, Θ.Models η → ∀ σ, Closing Δ Γ η σ → J1Core Δ (octxStrip η Γ) (fillS σ 0 e) η j

/-- **`J₁`, tier 1's typing**: Core's kernel (SPEC §24) over the open types, with the row `∀`. -/
def J₁ : OurTyping orowRF := OurTyping.ofDer J1Der

theorem J1Core_of_rFree {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {η : RowEnv} :
    ∀ {j : OJdg}, j.RFree → (J1Core Δ Γ e η j ↔ CDerives Δ Γ e (j.den η))
  | .comp _, _ => Iff.rfl
  | .val A, h => by
      simp only [J1Core, OVTy.isPoly_of_rFree h, Bool.false_eq_true, if_false]
      rfl

theorem j1JOK_ofJ : ∀ j : Jdg, J1JOK (OJdg.ofJ j)
  | .comp C => OCTy.rFree_ofC C
  | .val A => .inl (OVTy.rFree_ofV A)

theorem octx_noPoly_of_rFree {Γ : Ctx OVTy} (h : octxRFree Γ) :
    ∀ s ∈ Γ, s.live = true → s.ty.isPoly = false :=
  fun s hs _ => OVTy.isPoly_of_rFree (h s hs)

/-- **At judgements free of the row `∀`, `J₁` is Core's kernel**: its reading is `tier1`. -/
theorem j1_read : J₁.read = tier1 := by
  show TypingJ.mk _ _ = TypingJ.mk _ _
  congr 1
  funext Θ Δ Γ e j
  apply propext
  constructor
  · intro h η hη
    obtain ⟨Γ', j', hΓ', hj', ⟨-, -, hd⟩, hΓ, hj⟩ := h η hη
    have h' := hd η (rowCtx_models_nil η) (fun _ => none) (closing_none (octx_noPoly_of_rFree hΓ'))
    rw [fillS_none, octxStrip_of_rFree η hΓ', J1Core_of_rFree hj', hΓ η, hj η] at h'
    exact h'
  · intro h η hη
    refine ⟨octxOf (Γ η), OJdg.ofJ (j η), octxRFree_octxOf _, OJdg.rFree_ofJ _,
      ⟨fun s hs => .inl (octxRFree_octxOf _ s hs), j1JOK_ofJ _, fun η' _ σ hσ => ?_⟩,
      fun η' => octxDen_octxOf η' _, fun η' => OJdg.den_ofJ η' _⟩
    · rw [fillS_of_closing_noPoly hσ (octx_noPoly_of_rFree (octxRFree_octxOf _)),
        octxStrip_of_rFree η' (octxRFree_octxOf _), J1Core_of_rFree (OJdg.rFree_ofJ _),
        octxDen_octxOf, OJdg.den_ofJ]
      exact h η hη

/-- **`J₁`'s closed programs are Core's.** -/
theorem coreClosed_J₁ : CoreClosed J₁ := by
  intro Θ e C hΘ hd
  have h := hd.2.2 _ (models_anyCon_nil hΘ) (fun _ => none)
    (closing_none (fun s hs => absurd hs List.not_mem_nil))
  rw [fillS_none] at h
  exact h

/-! ### The let law and subeffecting at our instance -/

section Ours
variable {Ξ : EffCtx}

theorem octxStrip_live_cons_poly (η : RowEnv) {A : OVTy} (hA : A.isPoly = true) (Γ : List OVTy) :
    octxStrip η (liveCtx (A :: Γ)) = ⟨.unit, false⟩ :: octxStrip η (liveCtx Γ) := by
  simp only [octxStrip, liveCtx, List.map_cons, Bool.true_and, hA, if_true]

theorem octxStrip_live_cons_mono (η : RowEnv) {A : OVTy} (hA : A.isPoly = false) (Γ : List OVTy) :
    octxStrip η (liveCtx (A :: Γ)) = ⟨A.den η, true⟩ :: octxStrip η (liveCtx Γ) := by
  simp only [octxStrip, liveCtx, List.map_cons, Bool.true_and, hA, Bool.false_eq_true, if_false]

/-- **The let law at `J₁`**, at every row: a closed value at a polymorphic function type is bound by
Core's `[let-poly]` (`CDerives.letPoly`), its body typed with the value in place; at any other
type by `[let]` (`CDerives.bind`). -/
theorem letLaw_ourInst_J₁ : (ourInst (ℍ := ℍ) orowRF Ξ J₁).LetLaw := by
  intro Γ V A N C hV hN
  obtain ⟨Θ, hΘ, hVOK, hAOK, hVd⟩ := hV
  obtain ⟨hT, hN⟩ := hN
  refine ⟨hT, ?_⟩
  rcases hN with ⟨Θ', hΘ', hNOK, hCOK, hNd⟩ | ⟨h, -⟩
  · refine .inl ⟨Θ ++ Θ', fun p hp => ?_, ⟨fun s hs => hNOK s (List.mem_cons_of_mem _ hs), hCOK,
      fun η hη σ hσ => ?_⟩⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact hΘ p hp
      · exact hΘ' p hp
    · obtain ⟨hη₁, hη₂⟩ := models_append hη
      have hV₀ := hVd η hη₁ (fun _ => none) (closing_none (fun s hs => absurd hs List.not_mem_nil))
      rw [fillS_none] at hV₀
      have hV₁ : J1Core LifeCtx.empty [] (V.1 : Expr) η (.val (A : OVTy)) := hV₀
      change CDerives LifeCtx.empty (octxStrip η (liveCtx Γ))
        (.app (.lam (fillS σ 1 N)) (fillS σ 0 V.1)) (.comp (C.den η))
      have hN₁ : ∀ σ', Closing LifeCtx.empty (liveCtx ((A : OVTy) :: (Γ : List OVTy))) η σ' →
          CDerives LifeCtx.empty (octxStrip η (liveCtx ((A : OVTy) :: (Γ : List OVTy))))
            (fillS σ' 0 (N : Expr)) (.comp ((C : OCTy).den η)) := fun σ' h' => hNd η hη₂ σ' h'
      by_cases hA : A.isPoly = true
      · -- a polymorphic function: `[let-poly]`
        simp only [J1Core, hA, if_true] at hV₁
        obtain ⟨b, hVb, -, hb⟩ := hV₁
        obtain ⟨C₀, hC₀⟩ := OVTy.polyInst_nonempty hA η
        have hcl : closedAt 0 (Val.lam b).1 = true := by
          have := closedAt_of_derives (hb C₀ hC₀); simpa using this
        have hN₀ := hN₁ _ (closing_cons_poly hσ hA hcl hb)
        rw [fillS_scons_some hσ.closed hcl (N : Expr) 0, octxStrip_live_cons_poly η hA (Γ : List OVTy)] at hN₀
        rw [hVb, fillS_closed σ (.lam b) 0 hcl]
        exact .letPoly b hcl (hb C₀ hC₀) hN₀
      · -- any other type: `[let]`
        have hA' : A.isPoly = false := by simpa using hA
        simp only [J1Core, hA', Bool.false_eq_true, if_false] at hV₁
        have hcl : closedAt 0 V.1 = true := by
          have := closedAt_of_derives hV₁; simpa using this
        have hN₀ := hN₁ _ (closing_cons_mono hσ (s₀ := ⟨A, true⟩) (by simp [hA']))
        rw [fillS_scons_none σ (N : Expr) 0, octxStrip_live_cons_mono η hA' (Γ : List OVTy)] at hN₀
        rw [fillS_closed σ V.1 0 hcl]
        exact .bind (splitP_kill_left _) (.ret (hV₁.append_dead (kill_dead _))) hN₀
  · cases h

/-- **Subeffecting at `J₁`** (S1's `SubClosed`): at every target row tied to the effect context,
Core's `[sub]` at every instance and every closing. -/
theorem subClosed_J₁_tied {Γ : List OVTy} {e : Expr} {ε₁ ε₂ : ORow} {A : OVTy}
    (h : (ourInst (ℍ := ℍ) orowRF Ξ J₁).der Γ e ((ourInst (ℍ := ℍ) orowRF Ξ J₁).F ε₁ A))
    (hsub : (orowAlg Ξ).Sub ε₁ ε₂) (hat : RowAt Ξ ε₂.ops) :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).der Γ e ((ourInst (ℍ := ℍ) orowRF Ξ J₁).F ε₂ A) := by
  have hle : ∀ η, RowLe (orowRF.den Ξ ε₁ η) (orowRF.den Ξ ε₂ η) :=
    rowLink_orowRF.sub Ξ ε₁ ε₂ hsub
  obtain ⟨-, h⟩ := h
  refine ⟨tiedAt_F (fun _ => rfl) hat A, ?_⟩
  rcases h with ⟨Θ, hΘ, hOK, hCOK, hd⟩ | ⟨hΓ, M, he, hL, Θ, hΘ, hOK, hCOK, hd⟩
  · exact .inl ⟨Θ, hΘ, hOK, hCOK, fun η hη σ hσ => CDerives.effSub (hle η) (hd η hη σ hσ)⟩
  · refine .inr ⟨hΓ, M, he, fun η => ?_, Θ, hΘ, hOK, hCOK, fun η hη σ hσ =>
      CDerives.effSub (hle η) (hd η hη σ hσ)⟩
    obtain ⟨S, S₀, A₀, hS₀, hC₀, hC⟩ := hL η
    have hC' : CTy.effOf (orowRF.den Ξ ε₁ η) (A.den η) =
        CTy.effOf S (.sum A₀ (.thunk (CTy.loopEff S₀ A₀ .unit))) := hC
    obtain ⟨rfl, hA⟩ := effOf_inj hC'
    refine ⟨orowRF.den Ξ ε₂ η, S₀, A₀, fun n i o hf => hle η n i o (hS₀ n i o hf), hC₀, ?_⟩
    show CTy.effOf (orowRF.den Ξ ε₂ η) (A.den η) = _
    rw [hA]

/-- **S1's subeffecting at `J₁`**, at every effect context: a well-formed target is tied to the
context (`orowAlg`'s `WF`), and Core's `[sub]` asks nothing of its rows. -/
theorem subClosed_ourInst_J₁ : (ourInst (ℍ := ℍ) orowRF Ξ J₁).SubClosed := by
  rintro Γ e ε₁ ε₂ A h hsub ⟨Δ, hwf⟩
  exact subClosed_J₁_tied h hsub hwf.2

/-- **S1 at `J₁`**, at every effect context. -/
theorem rowAlgebra_ourInst_J₁ : (ourInst (ℍ := ℍ) orowRF Ξ J₁).RowAlgebra :=
  ⟨orowAlg_laws Ξ, orowAlg_safe Ξ, rowSig_orow, subClosed_ourInst_J₁⟩

end Ours

end Targets.Inst

end
