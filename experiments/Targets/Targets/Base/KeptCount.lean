import Targets.Base.RaiseNames
import Targets.Base.Look

/-!
# Base — the kept errors a term holds

A cancel keeps the first error its region's finalisers raise (SPEC §19).  The error is held in one
of two places: the raise of the cancel, `raise (0, (0, inj₂ E))`, or the `cfin` frame of a running
finaliser, `cfin (0, (0, inj₂ E)) e`.  `kc e` counts the holders in `e`; `OnPath e` says that every
holder of `e` is at its evaluation position (on its spine), so that no holder sits in a value, a
branch not taken, or code not yet reached.

A head step changes the count only where the algebra says (`kc_head`):

* `[cfin-raise]` at a cancel that kept nothing keeps a new error (`KeepRedex`): one more;
* `[cancel-raise]` re-raises the kept error at the canceller (`ReraiseRedex`): one fewer;
* `[cfin-cancel]` at two kept errors keeps the earlier (`MergeRedex`): one fewer;
* every other step moves a holder, or holds none, provided `[op]` captures no context holding a
  kept error (`NoKeptCaptureAt`).

The step keeps `OnPath`, under the run invariants a typed program's run has: every raise is of a
name in `P` or a cancel's (`Expr.RaiseOK`, `0 ∉ P`), and every handler is named nonzero
(`HndNamesNZ`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload cancelVal errVal errNext hndE
  hndVal kappa kappaC kappaAt kappaCell kappaCBody freeE stuckE ccatchE cfinE ubindE clauseAt capTag)

/-! ### The count -/

/-- **A cancel state keeping an error**, by its shape: `(0, (0, inj₂ y))`. -/
def keptB : Expr → Bool
  | .pair (.prim (.lit (.i32 m))) (.pair (.prim (.lit (.i32 j))) (.inj₂ _)) => m == 0 && j == 0
  | _ => false

/-- **The holder at an application's root**: `raise` of a cancel state keeping an error, or `cfin`
applied to one (the running finaliser's frame, counted at its state). -/
def holdAt : Expr → Expr → ℕ
  | .prim .raise, p => if keptB p then 1 else 0
  | .prim .cfin, s => if keptB s then 1 else 0
  | _, _ => 0

@[simp] theorem holdAt_app (f a b : Expr) : holdAt (.app f a) b = 0 := rfl
@[simp] theorem holdAt_lam (f b : Expr) : holdAt (.lam f) b = 0 := rfl
@[simp] theorem holdAt_var (i : ℕ) (b : Expr) : holdAt (.var i) b = 0 := rfl
@[simp] theorem holdAt_hnd (b : Expr) : holdAt (.prim .hnd) b = 0 := rfl
@[simp] theorem holdAt_ubind (b : Expr) : holdAt (.prim .ubind) b = 0 := rfl
@[simp] theorem holdAt_ccatch (b : Expr) : holdAt (.prim .ccatch) b = 0 := rfl
@[simp] theorem holdAt_perform (b : Expr) : holdAt (.prim .perform) b = 0 := rfl
@[simp] theorem holdAt_store (b : Expr) : holdAt (.prim .store) b = 0 := rfl
@[simp] theorem holdAt_alloc (b : Expr) : holdAt (.prim .alloc) b = 0 := rfl
@[simp] theorem holdAt_free (b : Expr) : holdAt (.prim .free) b = 0 := rfl
@[simp] theorem holdAt_count (b : Expr) : holdAt (.prim .count) b = 0 := rfl
@[simp] theorem holdAt_countTry (b : Expr) : holdAt (.prim .countTry) b = 0 := rfl
@[simp] theorem holdAt_boundedFix (b : Expr) : holdAt (.prim .boundedFix) b = 0 := rfl
@[simp] theorem holdAt_unit (b : Expr) : holdAt .unit b = 0 := rfl

/-- **The kept errors a term holds.** -/
def kc : Expr → ℕ
  | .app f a => holdAt f a + kc f + kc a
  | .pair a b | .seq a b | .letpair a b => kc a + kc b
  | .case a b c => kc a + kc b + kc c
  | .inj₁ a | .inj₂ a | .lam a => kc a
  | .var _ | .unit | .loc _ | .prim _ => 0

/-- **Every holder of a term is on its evaluation spine**: a value, a binder's body, a branch and
code not yet reached hold none; an application whose argument is not yet a value holds none at
its root, and its function is a running finaliser's `cfin` at a value state or holds none. -/
def OnPath : Expr → Prop
  | .app f a =>
      if isValB a then kc a = 0 ∧ (if isValB f then kc f = 0 else OnPath f)
      else OnPath a ∧ holdAt f a = 0 ∧
        (kc f = 0 ∨ ∃ s, f = .app (.prim .cfin) s ∧ isValB s = true ∧ kc s = 0)
  | .pair a b => if isValB a then kc a = 0 ∧ OnPath b else OnPath a ∧ kc b = 0
  | .seq a b | .letpair a b => OnPath a ∧ kc b = 0
  | .case a b c => OnPath a ∧ kc b = 0 ∧ kc c = 0
  | .inj₁ a | .inj₂ a => OnPath a
  | .lam b => kc b = 0
  | .var _ | .unit | .loc _ | .prim _ => True

/-- Every stored value holds no kept error. -/
def HeapKC (μ : Heap) : Prop := ∀ ℓ v, μ ℓ = some v → kc v.1 = 0

/-! ### Values and the count -/

theorem isValB_eq_false {e : Expr} (h : ¬ IsVal e) : isValB e = false := by
  cases hb : isValB e
  · rfl
  · exact absurd (isVal_of_isValB e hb) h

/-- A term holding nothing is on its spine. -/
theorem onPath_of_kc : ∀ {e : Expr}, kc e = 0 → OnPath e
  | .app f a, h => by
      simp only [kc, Nat.add_eq_zero_iff] at h
      obtain ⟨⟨h₀, hf⟩, ha⟩ := h
      simp only [OnPath]
      split
      · refine ⟨ha, ?_⟩
        split
        · exact hf
        · exact onPath_of_kc hf
      · exact ⟨onPath_of_kc ha, h₀, .inl hf⟩
  | .pair a b, h => by
      simp only [kc, Nat.add_eq_zero_iff] at h
      simp only [OnPath]
      split
      · exact ⟨h.1, onPath_of_kc h.2⟩
      · exact ⟨onPath_of_kc h.1, h.2⟩
  | .seq a b, h | .letpair a b, h => by
      simp only [kc, Nat.add_eq_zero_iff] at h
      exact ⟨onPath_of_kc h.1, h.2⟩
  | .case a b c, h => by
      simp only [kc, Nat.add_eq_zero_iff] at h
      exact ⟨onPath_of_kc h.1.1, h.1.2, h.2⟩
  | .inj₁ a, h | .inj₂ a, h => onPath_of_kc (e := a) h
  | .lam b, h => h
  | .var _, _ | .unit, _ | .loc _, _ | .prim _, _ => trivial

/-- A value on its spine holds nothing. -/
theorem kc_of_onPath_val : ∀ {e : Expr}, IsVal e → OnPath e → kc e = 0
  | _, .unit, _ => rfl
  | _, .lam, h => h
  | _, .loc, _ => rfl
  | _, .prim, _ => rfl
  | _, .pair (a := a) (b := b) ha hb, h => by
      simp only [OnPath, isValB_of_isVal ha, if_true] at h
      simp only [kc, h.1, kc_of_onPath_val hb h.2]
  | _, .inj₁ (a := a) ha, h => kc_of_onPath_val (e := a) ha h
  | _, .inj₂ (a := a) ha, h => kc_of_onPath_val (e := a) ha h
  | _, .storeV (a := a) ha, h => by
      simp only [OnPath, isValB_of_isVal ha, if_true, isValB] at h
      simp only [kc, holdAt, h.1]

/-! ### The shape of a kept error -/

theorem keptB_iff {e : Expr} :
    keptB e = true ↔ ∃ y, e = .pair (.prim (.lit (.i32 0))) (.pair (.prim (.lit (.i32 0))) (.inj₂ y)) := by
  constructor
  · intro h
    unfold keptB at h
    split at h
    · rename_i m j y
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨y, rfl⟩
    · cases h
  · rintro ⟨y, rfl⟩
    rfl

theorem keptB_cancelVal (err : Option Val) : keptB (cancelVal err).1 = err.isSome := by
  cases err <;> rfl

theorem not_keptB_opPayload {m j : UInt32} (hm : m ≠ 0) (w : Val) :
    keptB (opPayload m j w).1 = false := by
  cases hk : keptB (opPayload m j w).1
  · rfl
  · obtain ⟨y, hy⟩ := keptB_iff.1 hk
    simp only [opPayload, Val.pair, Val.i32, Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq,
      IntLit.i32.injEq] at hy
    exact absurd hy.1 hm

theorem keptB_shift (e : Expr) (d c : ℕ) : keptB (e.shift d c) = keptB e := by
  cases hk : keptB e
  · cases hk' : keptB (e.shift d c)
    · rfl
    · obtain ⟨y, hy⟩ := keptB_iff.1 hk'
      cases e with
      | var i => simp only [Expr.shift] at hy; split at hy <;> cases hy
      | pair a b =>
          simp only [Expr.shift, Expr.pair.injEq] at hy
          obtain ⟨ha, hb⟩ := hy
          cases a with
          | var i => simp only [Expr.shift] at ha; split at ha <;> cases ha
          | prim p =>
              simp only [Expr.shift, Expr.prim.injEq] at ha
              subst ha
              cases b with
              | var i => simp only [Expr.shift] at hb; split at hb <;> cases hb
              | pair b₁ b₂ =>
                  simp only [Expr.shift, Expr.pair.injEq] at hb
                  obtain ⟨hb₁, hb₂⟩ := hb
                  cases b₁ with
                  | var i => simp only [Expr.shift] at hb₁; split at hb₁ <;> cases hb₁
                  | prim q =>
                      simp only [Expr.shift, Expr.prim.injEq] at hb₁
                      subst hb₁
                      cases b₂ with
                      | var i => simp only [Expr.shift] at hb₂; split at hb₂ <;> cases hb₂
                      | inj₂ z => simp [keptB] at hk
                      | _ => simp [Expr.shift] at hb₂
                  | _ => simp [Expr.shift] at hb₁
              | _ => simp [Expr.shift] at hb
          | _ => simp [Expr.shift] at ha
      | _ => simp [Expr.shift] at hy
  · obtain ⟨y, rfl⟩ := keptB_iff.1 hk
    exact keptB_iff.2 ⟨y.shift d c, rfl⟩

theorem holdAt_shift (f a : Expr) (d c : ℕ) : holdAt (f.shift d c) (a.shift d c) = holdAt f a := by
  cases f with
  | var i =>
      simp only [Expr.shift]
      split <;> rfl
  | prim p => cases p <;> simp [Expr.shift, holdAt, keptB_shift]
  | _ => rfl

theorem kc_shift : ∀ (e : Expr) (d c : ℕ), kc (e.shift d c) = kc e
  | .var i, d, c => by simp only [Expr.shift]; split <;> rfl
  | .unit, _, _ | .loc _, _, _ | .prim _, _, _ => rfl
  | .pair a b, d, c | .seq a b, d, c => by simp [Expr.shift, kc, kc_shift a, kc_shift b]
  | .letpair a b, d, c => by simp [Expr.shift, kc, kc_shift a, kc_shift b]
  | .case a b e, d, c => by simp [Expr.shift, kc, kc_shift a, kc_shift b, kc_shift e]
  | .inj₁ a, d, c | .inj₂ a, d, c | .lam a, d, c => by simp [Expr.shift, kc, kc_shift a]
  | .app f a, d, c => by simp [Expr.shift, kc, kc_shift f, kc_shift a, holdAt_shift]

theorem kc_val_shift (v : Val) (d c : ℕ) : kc (v.shift d c).1 = kc v.1 := kc_shift v.1 d c

/-! ### Substitution, at the names `P` -/

section Subst
variable {P : UInt32 → Prop}

/-- A cancel state's shape, kept by substitution: its literals and its `inj` are syntax. -/
theorem keptB_subst_cancelShape {r : Expr} (h : CancelShape P r) (j : ℕ) (s : Val) :
    keptB (Expr.pair (.prim (.lit (.i32 0))) (r.subst j s)) =
      keptB (Expr.pair (.prim (.lit (.i32 0))) r) := by
  rcases h with rfl | ⟨m, i, y, rfl, -⟩ <;> rfl

/-- **The holder at an application's root, kept by substitution**: at the names `P`, `0` not one of
them, a raise and a `cfin` are applied to literal-named payloads whose shape no substitution
changes, and the substituted value is neither `raise` nor `cfin`. -/
theorem holdAt_subst (hP0 : ¬ P 0) {f a : Expr} (h : (Expr.app f a).RaiseOK P) (j : ℕ) {s : Val}
    (hs : s.1.RaiseOK P) : holdAt (f.subst j s) (a.subst j s) = holdAt f a := by
  obtain ⟨-, -, hok⟩ := h
  cases f with
  | var i =>
      simp only [Expr.subst]
      split
      · have h₁ : s.1 ≠ .prim .raise := fun he => by rw [he] at hs; exact not_raiseOK_raise hs
        have h₂ : s.1 ≠ .prim .cfin := fun he => by rw [he] at hs; exact not_raiseOK_cfin hs
        show holdAt s.1 _ = 0
        rcases s with ⟨e, he⟩
        cases e with
        | prim p => cases p <;> simp_all [holdAt]
        | _ => rfl
      · split <;> rfl
  | prim p =>
      cases p with
      | raise =>
          obtain ⟨m, r, rfl, hm⟩ := hok.1 rfl
          simp only [Expr.subst, holdAt]
          rcases hm with hm | ⟨rfl, hr⟩
          · have hm0 : m ≠ 0 := fun h0 => hP0 (h0 ▸ hm)
            have e₁ : keptB (Expr.pair (.prim (.lit (.i32 m))) (r.subst j s)) = false := by
              cases hk : keptB (Expr.pair (.prim (.lit (.i32 m))) (r.subst j s))
              · rfl
              · obtain ⟨y, hy⟩ := keptB_iff.1 hk
                simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hy
                exact absurd hy.1 hm0
            have e₂ : keptB (Expr.pair (.prim (.lit (.i32 m))) r) = false := by
              cases hk : keptB (Expr.pair (.prim (.lit (.i32 m))) r)
              · rfl
              · obtain ⟨y, hy⟩ := keptB_iff.1 hk
                simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hy
                exact absurd hy.1 hm0
            rw [e₁, e₂]
          · rw [keptB_subst_cancelShape hr]
      | cfin =>
          obtain ⟨r, rfl, hr⟩ := hok.2 rfl
          simp only [Expr.subst, holdAt]
          rw [keptB_subst_cancelShape hr]
      | _ => rfl
  | _ => rfl

/-- **Substituting a value that holds nothing keeps the count**, at the names `P`. -/
theorem kc_subst (hP0 : ¬ P 0) : ∀ (e : Expr) (j : ℕ) (s : Val), e.RaiseOK P → s.1.RaiseOK P →
    kc s.1 = 0 → kc (e.subst j s) = kc e
  | .var i, j, s, _, _, hk => by
      simp only [Expr.subst]
      split
      · exact hk
      · split <;> rfl
  | .unit, _, _, _, _, _ | .loc _, _, _, _, _, _ | .prim _, _, _, _, _, _ => rfl
  | .pair a b, j, s, he, hs, hk => by
      simp only [Expr.subst, kc, kc_subst hP0 a j s he.1 hs hk, kc_subst hP0 b j s he.2 hs hk]
  | .seq a b, j, s, he, hs, hk => by
      simp only [Expr.subst, kc, kc_subst hP0 a j s he.1 hs hk, kc_subst hP0 b j s he.2 hs hk]
  | .letpair a b, j, s, he, hs, hk => by
      simp only [Expr.subst, kc, kc_subst hP0 a j s he.1 hs hk,
        kc_subst hP0 b (j + 2) (s.shift 2 0) he.2 (raiseOK_val_shift hs 2 0)
          (by rw [kc_val_shift]; exact hk)]
  | .case a b c, j, s, he, hs, hk => by
      simp only [Expr.subst, kc, kc_subst hP0 a j s he.1 hs hk,
        kc_subst hP0 b (j + 1) (s.shift 1 0) he.2.1 (raiseOK_val_shift hs 1 0)
          (by rw [kc_val_shift]; exact hk),
        kc_subst hP0 c (j + 1) (s.shift 1 0) he.2.2 (raiseOK_val_shift hs 1 0)
          (by rw [kc_val_shift]; exact hk)]
  | .inj₁ a, j, s, he, hs, hk | .inj₂ a, j, s, he, hs, hk => by
      simp only [Expr.subst, kc, kc_subst hP0 a j s he hs hk]
  | .lam b, j, s, he, hs, hk => by
      simp only [Expr.subst, kc, kc_subst hP0 b (j + 1) (s.shift 1 0) he
        (raiseOK_val_shift hs 1 0) (by rw [kc_val_shift]; exact hk)]
  | .app f a, j, s, he, hs, hk => by
      have hf : kc (f.subst j s) = kc f := by
        rcases he.1 with rfl | rfl | hf
        · rfl
        · rfl
        · exact kc_subst hP0 f j s hf hs hk
      simp only [Expr.subst, kc, holdAt_subst hP0 he j hs, hf, kc_subst hP0 a j s he.2.1 hs hk]

theorem kc_val_subst (hP0 : ¬ P 0) {v : Val} (hv : v.1.RaiseOK P) (j : ℕ) {s : Val}
    (hs : s.1.RaiseOK P) (hk : kc s.1 = 0) : kc (Val.subst j s v).1 = kc v.1 :=
  kc_subst hP0 v.1 j s hv hs hk

end Subst

/-! ### Contexts -/

section Plug
variable {P : UInt32 → Prop}

theorem not_isVal_plug (K : Kont) {a : Expr} (hv : ¬ IsVal a) : ¬ IsVal (K.plug a) :=
  fun h => hv (K.isVal_of_plug h)

/-- A kept error's shape read through a context at a plain term: the hole is inside the error, so
every term plugged there gives the shape. -/
theorem keptB_plug {a : Expr} (ha : Plain a) {K : Kont} (h : keptB (K.plug a) = true) (b : Expr) :
    keptB (K.plug b) = true := by
  obtain ⟨y, hy⟩ := keptB_iff.1 h
  obtain ⟨v₁, K₁, rfl, hv₁, h₁⟩ := plug_eq_pairLit ha hy
  obtain ⟨v₂, K₂, rfl, hv₂, h₂⟩ := plug_eq_pairLit ha h₁.symm
  obtain ⟨K₃, rfl, -⟩ := plug_eq_inj₂ ha h₂.symm
  exact keptB_iff.2 ⟨K₃.plug b, by simp only [Kont.plug, Expr.val, hv₁, hv₂]⟩

theorem keptB_pairLit_ne {m : UInt32} (hm : m ≠ 0) (r : Expr) :
    keptB (Expr.pair (.prim (.lit (.i32 m))) r) = false := by
  cases hk : keptB (Expr.pair (.prim (.lit (.i32 m))) r)
  · rfl
  · obtain ⟨y, hy⟩ := keptB_iff.1 hk
    simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hy
    exact absurd hy.1 hm

/-- A cancel state's shape at the names `P`, read through a context at a plain term, keeps an error:
the plain term is in the kept raise's argument. -/
theorem keptB_cancelShape_plug {a : Expr} (ha : Plain a) {K : Kont}
    (h : CancelShape P (K.plug a)) : keptB (Expr.pair (.prim (.lit (.i32 0))) (K.plug a)) = true := by
  rcases h with h | ⟨m, j, y, h, -⟩
  · obtain ⟨v, K₁, rfl, -, h₁⟩ := plug_eq_pairLit ha h
    exact absurd h₁.symm (plug_ne_inj₁_unit ha)
  · rw [h]; rfl

/-- **The holder at a frame's root does not depend on what its hole holds**, at a context at the
names `P` (`0` not one of them): a raise's and a `cfin`'s payloads are literal-named, and a cancel
state's `inj` is syntax. -/
theorem holdAt_appR_plug (hP0 : ¬ P 0) {f : Expr} {K : Kont}
    (h : KRaiseOK P (.appR f K)) (x : Expr) : holdAt f (K.plug x) = holdAt f (K.plug (.var 0)) := by
  have h' : (Expr.app f (K.plug (.var 0))).RaiseOK P := h
  obtain ⟨-, -, hok⟩ := h'
  cases f with
  | prim p =>
      cases p with
      | raise =>
          obtain ⟨m, r, hr, hm⟩ := hok.1 rfl
          obtain ⟨v, K₁, rfl, hv, rfl⟩ := plug_eq_pairLit (plain_var 0) hr
          simp only [holdAt, Kont.plug, Expr.val, hv]
          rcases hm with hm | ⟨rfl, hs⟩
          · have hm0 : m ≠ 0 := fun h0 => hP0 (h0 ▸ hm)
            rw [keptB_pairLit_ne hm0, keptB_pairLit_ne hm0]
          · have h₁ := keptB_cancelShape_plug (plain_var 0) hs
            have h₂ := keptB_plug (K := .pairR ⟨.prim (.lit (.i32 0)), .prim⟩ K₁) (plain_var 0) h₁ x
            simp only [Kont.plug, Expr.val] at h₂
            rw [h₁, h₂]
      | cfin =>
          obtain ⟨r, hr, hs⟩ := hok.2 rfl
          obtain ⟨v, K₁, rfl, hv, rfl⟩ := plug_eq_pairLit (plain_var 0) hr
          simp only [holdAt, Kont.plug, Expr.val, hv]
          have h₁ := keptB_cancelShape_plug (plain_var 0) hs
          have h₂ := keptB_plug (K := .pairR ⟨.prim (.lit (.i32 0)), .prim⟩ K₁) (plain_var 0) h₁ x
          simp only [Kont.plug, Expr.val] at h₂
          rw [h₁, h₂]
      | _ => rfl
  | _ => rfl

/-- At a context at the names `P`, a function position holds neither `raise` nor `cfin` alone. -/
theorem kraiseOK_appL {K : Kont} {v : Val} (h : KRaiseOK P (.appL K v)) : KRaiseOK P K ∧ v.1.RaiseOK P := by
  have h' : (Expr.app (K.plug (.var 0)) v.1).RaiseOK P := h
  obtain ⟨hf, hv, -⟩ := h'
  refine ⟨?_, hv⟩
  rcases hf with hf | hf | hf
  · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
  · exact absurd hf (plug_ne_prim_of_plain (plain_var 0))
  · exact hf

theorem kraiseOK_appR {f : Expr} {K : Kont} (h : KRaiseOK P (.appR f K)) : KRaiseOK P K :=
  (show (Expr.app f (K.plug (.var 0))).RaiseOK P from h).2.1

theorem holdAt_of_raiseOK {f : Expr} (hf : f.RaiseOK P) (a : Expr) : holdAt f a = 0 := by
  cases f with
  | prim p =>
      cases p with
      | raise => exact absurd hf not_raiseOK_raise
      | cfin => exact absurd hf not_raiseOK_cfin
      | _ => rfl
  | _ => rfl

/-- **The count through a context**: what a context at the names `P` holds and what its hole
holds, the hole's filling at `P`. -/
theorem kc_plug (hP0 : ¬ P 0) : ∀ (K : Kont) {x : Expr}, KRaiseOK P K → x.RaiseOK P →
    kc (K.plug x) = kc (K.plug (.var 0)) + kc x := by
  intro K
  induction K with
  | hole => intro x _ _; simp [Kont.plug, kc]
  | pairL K e ih =>
      intro x hK hx
      have hK' : KRaiseOK P K := (show (Expr.pair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, kc, ih hK' hx]; omega
  | pairR v K ih =>
      intro x hK hx
      have hK' : KRaiseOK P K := (show (Expr.pair v.1 (K.plug (.var 0))).RaiseOK P from hK).2
      simp only [Kont.plug, kc, ih hK' hx]; omega
  | letpair K e ih =>
      intro x hK hx
      have hK' : KRaiseOK P K := (show (Expr.letpair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, kc, ih hK' hx]; omega
  | case K e₁ e₂ ih =>
      intro x hK hx
      have hK' : KRaiseOK P K := (show (Expr.case (K.plug (.var 0)) e₁ e₂).RaiseOK P from hK).1
      simp only [Kont.plug, kc, ih hK' hx]; omega
  | seq K e ih =>
      intro x hK hx
      have hK' : KRaiseOK P K := (show (Expr.seq (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, kc, ih hK' hx]; omega
  | inj₁ K ih => intro x hK hx; simp only [Kont.plug, kc, ih hK hx]
  | inj₂ K ih => intro x hK hx; simp only [Kont.plug, kc, ih hK hx]
  | appR f K ih =>
      intro x hK hx
      simp only [Kont.plug, kc, ih (kraiseOK_appR hK) hx, holdAt_appR_plug hP0 hK x]; omega
  | appL K v ih =>
      intro x hK hx
      obtain ⟨hK', -⟩ := kraiseOK_appL hK
      have hx' : (K.plug x).RaiseOK P := plug_raiseOK K hK' hx
      have h₁ : holdAt (K.plug x) v.1 = 0 := holdAt_of_raiseOK hx' _
      have h₂ : holdAt (K.plug (.var 0)) v.1 = 0 := holdAt_of_raiseOK hK' _
      simp only [Kont.plug, kc, ih hK' hx, h₁, h₂]; omega

/-- **On the spine through a context**, at a term that is not a value: the context's spine and the
term's. -/
theorem onPath_plug_inv : ∀ (K : Kont) {a : Expr}, Plain a → ¬ IsVal a → OnPath (K.plug a) →
    OnPath (K.plug (.var 0)) ∧ OnPath a := by
  intro K
  induction K with
  | hole => intro a _ _ h; exact ⟨trivial, h⟩
  | pairL K e ih =>
      intro a hp hv h
      simp only [Kont.plug, OnPath, isValB_eq_false (not_isVal_plug K hv),
        isValB_eq_false (not_isVal_plug K (not_isVal_var (i := 0))), Bool.false_eq_true,
        if_false] at h ⊢
      exact ⟨⟨(ih hp hv h.1).1, h.2⟩, (ih hp hv h.1).2⟩
  | pairR v K ih =>
      intro a hp hv h
      simp only [Kont.plug, OnPath, isValB_of_isVal v.2, if_true] at h ⊢
      exact ⟨⟨h.1, (ih hp hv h.2).1⟩, (ih hp hv h.2).2⟩
  | letpair K e ih =>
      intro a hp hv h
      simp only [Kont.plug, OnPath] at h ⊢
      exact ⟨⟨(ih hp hv h.1).1, h.2⟩, (ih hp hv h.1).2⟩
  | case K e₁ e₂ ih =>
      intro a hp hv h
      simp only [Kont.plug, OnPath] at h ⊢
      exact ⟨⟨(ih hp hv h.1).1, h.2⟩, (ih hp hv h.1).2⟩
  | seq K e ih =>
      intro a hp hv h
      simp only [Kont.plug, OnPath] at h ⊢
      exact ⟨⟨(ih hp hv h.1).1, h.2⟩, (ih hp hv h.1).2⟩
  | inj₁ K ih => intro a hp hv h; exact ih hp hv h
  | inj₂ K ih => intro a hp hv h; exact ih hp hv h
  | appR f K ih =>
      intro a hp hv h
      simp only [Kont.plug, OnPath, isValB_eq_false (not_isVal_plug K hv),
        isValB_eq_false (not_isVal_plug K (not_isVal_var (i := 0))), Bool.false_eq_true,
        if_false] at h ⊢
      obtain ⟨h₁, h₂, h₃⟩ := h
      refine ⟨⟨(ih hp hv h₁).1, ?_, h₃⟩, (ih hp hv h₁).2⟩
      cases f with
      | prim p =>
          cases p with
          | raise =>
              simp only [holdAt] at h₂ ⊢
              cases hk : keptB (K.plug (.var 0))
              · rfl
              · rw [keptB_plug (plain_var 0) hk a] at h₂; simp at h₂
          | cfin =>
              simp only [holdAt] at h₂ ⊢
              cases hk : keptB (K.plug (.var 0))
              · rfl
              · rw [keptB_plug (plain_var 0) hk a] at h₂; simp at h₂
          | _ => rfl
      | _ => rfl
  | appL K v ih =>
      intro a hp hv h
      simp only [Kont.plug, OnPath, isValB_of_isVal v.2, if_true,
        isValB_eq_false (not_isVal_plug K hv),
        isValB_eq_false (not_isVal_plug K (not_isVal_var (i := 0))), Bool.false_eq_true,
        if_false] at h ⊢
      exact ⟨⟨h.1, (ih hp hv h.2).1⟩, (ih hp hv h.2).2⟩

/-- **On the spine, plugged**: a context on its spine at the names `P`, filled with a term on its
spine at `P`, is on its spine. -/
theorem onPath_plug (hP0 : ¬ P 0) : ∀ (K : Kont) {x : Expr}, KRaiseOK P K → x.RaiseOK P →
    OnPath (K.plug (.var 0)) → OnPath x → OnPath (K.plug x) := by
  intro K
  induction K with
  | hole => intro x _ _ _ h; exact h
  | pairL K e ih =>
      intro x hK hx hKo h
      have hK' : KRaiseOK P K := (show (Expr.pair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath, isValB_eq_false (not_isVal_plug K (not_isVal_var (i := 0))),
        Bool.false_eq_true, if_false] at hKo
      have ih' := ih hK' hx hKo.1 h
      simp only [Kont.plug, OnPath]
      split
      · rename_i hb
        exact ⟨kc_of_onPath_val (isVal_of_isValB _ hb) ih', onPath_of_kc hKo.2⟩
      · exact ⟨ih', hKo.2⟩
  | pairR v K ih =>
      intro x hK hx hKo h
      have hK' : KRaiseOK P K := (show (Expr.pair v.1 (K.plug (.var 0))).RaiseOK P from hK).2
      simp only [Kont.plug, OnPath, isValB_of_isVal v.2, if_true] at hKo ⊢
      exact ⟨hKo.1, ih hK' hx hKo.2 h⟩
  | letpair K e ih =>
      intro x hK hx hKo h
      have hK' : KRaiseOK P K := (show (Expr.letpair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath] at hKo ⊢
      exact ⟨ih hK' hx hKo.1 h, hKo.2⟩
  | case K e₁ e₂ ih =>
      intro x hK hx hKo h
      have hK' : KRaiseOK P K := (show (Expr.case (K.plug (.var 0)) e₁ e₂).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath] at hKo ⊢
      exact ⟨ih hK' hx hKo.1 h, hKo.2⟩
  | seq K e ih =>
      intro x hK hx hKo h
      have hK' : KRaiseOK P K := (show (Expr.seq (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath] at hKo ⊢
      exact ⟨ih hK' hx hKo.1 h, hKo.2⟩
  | inj₁ K ih => intro x hK hx hKo h; exact ih hK hx hKo h
  | inj₂ K ih => intro x hK hx hKo h; exact ih hK hx hKo h
  | appR f K ih =>
      intro x hK hx hKo h
      have hK' := kraiseOK_appR hK
      simp only [Kont.plug, OnPath, isValB_eq_false (not_isVal_plug K (not_isVal_var (i := 0))),
        Bool.false_eq_true, if_false] at hKo
      obtain ⟨h₁, h₂, h₃⟩ := hKo
      have ih' := ih hK' hx h₁ h
      simp only [Kont.plug, OnPath]
      split
      · rename_i hb
        refine ⟨kc_of_onPath_val (isVal_of_isValB _ hb) ih', ?_⟩
        rcases h₃ with h₃ | ⟨s, rfl, hs, hks⟩
        · split
          · exact h₃
          · exact onPath_of_kc h₃
        · simp only [isValB, Bool.false_eq_true, if_false, OnPath, hs, if_true, hks, true_and]
          rfl
      · exact ⟨ih', by rw [holdAt_appR_plug hP0 hK x]; exact h₂, h₃⟩
  | appL K v ih =>
      intro x hK hx hKo h
      obtain ⟨hK', -⟩ := kraiseOK_appL hK
      simp only [Kont.plug, OnPath, isValB_of_isVal v.2, if_true,
        isValB_eq_false (not_isVal_plug K (not_isVal_var (i := 0))), Bool.false_eq_true,
        if_false] at hKo
      have ih' := ih hK' hx hKo.2 h
      simp only [Kont.plug, OnPath, isValB_of_isVal v.2, if_true]
      refine ⟨hKo.1, ?_⟩
      split
      · rename_i hb
        exact kc_of_onPath_val (isVal_of_isValB _ hb) ih'
      · exact ih'

end Plug

/-! ### The terms a head step builds -/

section Built
variable {P : UInt32 → Prop}

/-- A dead region holds no kept error where the region holds none: it is the region with handler
frames and cancel delimiters removed, and a raise's and a `cfin`'s payloads keep their shape. -/
theorem kc_dead (hP0 : ¬ P 0) : ∀ {K : Kont}, KRaiseOK P K → kc (K.plug (.var 0)) = 0 →
    kc (K.dead.plug (.var 0)) = 0
  | .hole, _, _ => rfl
  | .pairL K e, hK, h => by
      have hK' : KRaiseOK P K := (show (Expr.pair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, kc, Nat.add_eq_zero_iff] at h
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 hK' h.1, h.2]
  | .pairR v K, hK, h => by
      have hK' : KRaiseOK P K := (show (Expr.pair v.1 (K.plug (.var 0))).RaiseOK P from hK).2
      simp only [Kont.plug, kc, Nat.add_eq_zero_iff] at h
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 hK' h.2, h.1]
  | .letpair K e, hK, h => by
      have hK' : KRaiseOK P K := (show (Expr.letpair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, kc, Nat.add_eq_zero_iff] at h
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 hK' h.1, h.2]
  | .case K e₁ e₂, hK, h => by
      have hK' : KRaiseOK P K := (show (Expr.case (K.plug (.var 0)) e₁ e₂).RaiseOK P from hK).1
      simp only [Kont.plug, kc, Nat.add_eq_zero_iff] at h
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 hK' h.1.1, h.1.2, h.2]
  | .seq K e, hK, h => by
      have hK' : KRaiseOK P K := (show (Expr.seq (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, kc, Nat.add_eq_zero_iff] at h
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 hK' h.1, h.2]
  | .inj₁ K, hK, h => by
      simp only [Kont.plug, kc] at h
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 (K := K) hK h]
  | .inj₂ K, hK, h => by
      simp only [Kont.plug, kc] at h
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 (K := K) hK h]
  | .appL K v, hK, h => by
      obtain ⟨hK', hv⟩ := kraiseOK_appL hK
      simp only [Kont.plug, kc, Nat.add_eq_zero_iff] at h
      have hd : KRaiseOK P K.dead := kraiseOK_dead hK'
      simp only [Kont.dead, Kont.plug, kc, kc_dead hP0 hK' h.1.2, h.2, holdAt_of_raiseOK hd]
  | .appR f K, hK, h => by
      have hK' := kraiseOK_appR hK
      simp only [Kont.plug, kc, Nat.add_eq_zero_iff] at h
      obtain ⟨⟨h₀, hf⟩, hk⟩ := h
      simp only [Kont.dead]
      split
      · exact kc_dead hP0 hK' hk
      · have hd : KRaiseOK P (.appR f K.dead) := by
          have := kraiseOK_dead (P := P) (K := .appR f K) hK
          simp only [Kont.dead] at this
          rwa [if_neg (by assumption)] at this
        have e₁ := holdAt_appR_plug hP0 hd (.var 0)
        have e₂ := holdAt_appR_plug hP0 hK (K.dead.plug (.var 0))
        simp only [Kont.plug, kc, kc_dead hP0 hK' hk, hf]
        -- the root's holder reads the payload's shape, which the dead region keeps
        have e₃ : holdAt f (K.dead.plug (.var 0)) = holdAt f (K.plug (.var 0)) := by
          have h' : (Expr.app f (K.plug (.var 0))).RaiseOK P := hK
          obtain ⟨-, -, hok⟩ := h'
          cases f with
          | prim p =>
              cases p with
              | raise =>
                  obtain ⟨m, r, hr, hm⟩ := hok.1 rfl
                  obtain ⟨v, K₁, rfl, hv, rfl⟩ := plug_eq_pairLit (plain_var 0) hr
                  simp only [holdAt, Kont.dead, Kont.plug, Expr.val, hv]
                  rcases hm with hm | ⟨rfl, hs⟩
                  · have hm0 : m ≠ 0 := fun h0 => hP0 (h0 ▸ hm)
                    rw [keptB_pairLit_ne hm0, keptB_pairLit_ne hm0]
                  · have h₁ := keptB_cancelShape_plug (plain_var 0) hs
                    have h₂ := keptB_cancelShape_plug (plain_var 0) (cancelShape_dead hs)
                    rw [h₁, h₂]
              | cfin =>
                  obtain ⟨r, hr, hs⟩ := hok.2 rfl
                  obtain ⟨v, K₁, rfl, hv, rfl⟩ := plug_eq_pairLit (plain_var 0) hr
                  simp only [holdAt, Kont.dead, Kont.plug, Expr.val, hv]
                  have h₁ := keptB_cancelShape_plug (plain_var 0) hs
                  have h₂ := keptB_cancelShape_plug (plain_var 0) (cancelShape_dead hs)
                  rw [h₁, h₂]
              | _ => rfl
          | _ => rfl
        rw [e₃, h₀]

/-- A context shifted holds what it held. -/
theorem kc_shift_plug (hP0 : ¬ P 0) {K : Kont} (hK : KRaiseOK P K) (d : ℕ) :
    kc ((K.shift d 0).plug (.var 0)) = kc (K.plug (.var 0)) := by
  have h₁ := kc_shift (K.plug (.var 0)) d 0
  rw [Kont.plug_shift] at h₁
  simp only [Expr.shift, Nat.not_lt_zero, if_false, zero_add] at h₁
  rw [kc_plug hP0 (K.shift d 0) (kraiseOK_shift hK d) (x := .var d) trivial] at h₁
  simpa [kc] using h₁

theorem kc_raise_cancel_none : kc (raiseE (.val (cancelVal none))) = 0 := rfl

/-- **κ holds no kept error** where its handler and its context hold none. -/
theorem kc_kappa (hP0 : ¬ P 0) {H : Val} {K : Kont} (hH : kc H.1 = 0) (hKr : KRaiseOK P K)
    (hK : kc (K.plug (.var 0)) = 0) : kc (kappa H K) = 0 := by
  have h₁ : kc ((K.shift 3 0).plug (.var 0)) = 0 := by rw [kc_shift_plug hP0 hKr]; exact hK
  have hd : KRaiseOK P (K.dead.shift 2 0) := kraiseOK_shift (kraiseOK_dead hKr) 2
  have h₂ : kc ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none)))) = 0 := by
    rw [kc_plug hP0 _ hd raiseOK_raise_cancel_none, kc_shift_plug hP0 (kraiseOK_dead hKr),
      kc_dead hP0 hKr hK]
    rfl
  simp only [kappa, Expr.val, Val.lam, Val.prim, kc, holdAt_app, holdAt_hnd, holdAt_ccatch,
    hndE, ccatchE, Val.val_shift, kc_shift, hH, h₁, h₂]

theorem kc_kappaCell (hP0 : ¬ P 0) (aff : Bool) {H : Val} {K : Kont} (hH : kc H.1 = 0)
    (hKr : KRaiseOK P K) (hK : kc (K.plug (.var 0)) = 0) : kc (kappaCell aff H K) = 0 := by
  have h₁ : kc ((K.shift 4 0).plug (.var 0)) = 0 := by rw [kc_shift_plug hP0 hKr]; exact hK
  have hd : KRaiseOK P (K.dead.shift 3 0) := kraiseOK_shift (kraiseOK_dead hKr) 3
  have h₂ : kc ((K.dead.shift 3 0).plug (raiseE (.val (cancelVal none)))) = 0 := by
    rw [kc_plug hP0 _ hd raiseOK_raise_cancel_none, kc_shift_plug hP0 (kraiseOK_dead hKr),
      kc_dead hP0 hKr hK]
    rfl
  cases aff <;>
    simp [kappaCell, kappaCBody, Expr.val, Val.lam, Val.prim, Val.unit, kc, hndE,
      ccatchE, freeE, stuckE, Val.val_shift, kc_shift, hH, h₁, h₂]

theorem kc_kappaAt (hP0 : ¬ P 0) (t : UInt32) {H : Val} {K : Kont} (hH : kc H.1 = 0)
    (hKr : KRaiseOK P K) (hK : kc (K.plug (.var 0)) = 0) : kc (kappaAt t H K) = 0 := by
  unfold kappaAt
  split
  · exact kc_kappaCell hP0 false hH hKr hK
  · split
    · exact kc_kappaCell hP0 true hH hKr hK
    · exact kc_kappa hP0 hH hKr hK

theorem kc_clauseAt : ∀ (e : Expr) (i : ℕ) {c : Val}, clauseAt e i = some c → kc e = 0 → kc c.1 = 0
  | .pair c' _, 0, c, h, he => by
      simp only [clauseAt] at h
      split at h
      · cases h; simp only [kc, Nat.add_eq_zero_iff] at he; exact he.1
      · cases h
  | .pair _ r, i + 1, c, h, he => by
      simp only [kc, Nat.add_eq_zero_iff] at he
      exact kc_clauseAt r i h he.2
  | .var _, _, _, h, _ | .unit, _, _, h, _ | .inj₁ _, _, _, h, _ | .inj₂ _, _, _, h, _
  | .lam _, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ | .seq _ _, _, _, h, _
  | .letpair _ _, _, _, h, _ | .case _ _ _, _, _, h, _ | .app _ _, _, _, h, _ => by
      simp [clauseAt] at h

theorem kc_opt {o : Option Val} (h : ∀ v, o = some v → kc v.1 = 0) : kc (Val.opt o).1 = 0 := by
  cases o with
  | none => rfl
  | some v => exact h v rfl

theorem kc_bool (b : Bool) : kc (Val.bool b).1 = 0 := by cases b <;> rfl

theorem kc_host (H : Host) (op : HostOp) {v r : Val} (h : H.call op v = some r) : kc r.1 = 0 := by
  have hi32 : ∀ n, kc (Val.i32 n).1 = 0 := fun _ => rfl
  have hi64 : ∀ n, kc (Val.i64 n).1 = 0 := fun _ => rfl
  have hu8 : ∀ n, kc (Val.u8 n).1 = 0 := fun _ => rfl
  cases op with
  | bin w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi64 _
  | div w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h
        exact kc_opt fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h
        exact kc_opt fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi64 _
  | un w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | eqz w =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact kc_bool _
      · obtain ⟨_, -, rfl⟩ := h; exact kc_bool _
  | rel w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact kc_bool _
      · obtain ⟨_, _, -, rfl⟩ := h; exact kc_bool _
  | wrap =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | extend_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend32_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | wrap8 =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hu8 _
  | extend8_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _

theorem kc_tabFill {f : Val} (hf : f.1.RaiseOK P) (hk : kc f.1 = 0) (ℓ : Loc) (n : UInt32) :
    ∀ i k, kc (tabFill f ℓ n i k) = 0
  | i, 0 => rfl
  | i, k + 1 => by
      simp only [tabFill, kc, Expr.val, Val.prim, Val.loc, Val.i32, holdAt_app, holdAt_store, hk,
        holdAt_of_raiseOK hf, kc_tabFill hf hk ℓ n (i + 1) k]

theorem kc_dropFill {f : Val} (hf : f.1.RaiseOK P) (hk : kc f.1 = 0) (ℓ : Loc) :
    ∀ i k, kc (dropFill f ℓ i k) = 0
  | i, 0 => rfl
  | i, k + 1 => by
      simp only [dropFill, kc, Expr.val, Val.prim, Val.loc, holdAt_free, hk, holdAt_of_raiseOK hf,
        kc_dropFill hf hk ℓ (i + 1) k]

/-- A term holding nothing at the names `P` holds nothing applied to one holding nothing. -/
theorem kc_app_of {f a : Expr} (hf : f.RaiseOK P) (hkf : kc f = 0) (hka : kc a = 0) :
    kc (.app f a) = 0 := by
  simp only [kc, holdAt_of_raiseOK hf, hkf, hka]

end Built

/-! ### Memories -/

theorem heapKC_upd {μ : Heap} (hμ : HeapKC μ) (ℓ : Loc) {v : Val} (hv : kc v.1 = 0) :
    HeapKC (μ.upd ℓ v) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h; subst h; exact hv
  · rw [Heap.upd_other hk] at h; exact hμ k w h

theorem heapKC_del {μ : Heap} (hμ : HeapKC μ) (ℓ : Loc) : HeapKC (μ.del ℓ) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h
  · rw [Heap.del_other hk] at h; exact hμ k w h

theorem heapKC_fill {μ : Heap} (hμ : HeapKC μ) (ℓ : Loc) (n : ℕ) {v : Val} (hv : kc v.1 = 0) :
    HeapKC (μ.fill ℓ n v) := by
  intro k w h
  simp only [Heap.fill] at h
  split at h
  · cases h; exact hv
  · exact hμ k w h

theorem heapKC_empty : HeapKC Adequacy.emptyMem := fun _ _ h => by simp [Adequacy.emptyMem] at h

/-! ### A head step -/

/-- **`[cfin-raise]` at a cancel that kept nothing**: the step that keeps a new error. -/
def KeepRedex (a : Expr) : Prop :=
  ∃ (K : Kont) (m j : UInt32) (w : Val),
    a = cfinE (cancelVal none) (K.plug (raiseE (.val (opPayload m j w)))) ∧ m ≠ 0 ∧
      K.Catches m = false

/-- **`[cancel-raise]`**: the step that re-raises a kept error at its canceller. -/
def ReraiseRedex (a : Expr) : Prop :=
  ∃ (K : Kont) (E : Val), a = ccatchE (K.plug (raiseE (.val (cancelVal (some E))))) ∧
    K.Catches 0 = false

/-- **`[cfin-cancel]` at two kept errors**: the step at which the later error loses to the
earlier (SPEC §19: the first kept wins). -/
def MergeRedex (a : Expr) : Prop :=
  ∃ (K : Kont) (E E' : Val),
    a = cfinE (cancelVal (some E)) (K.plug (raiseE (.val (cancelVal (some E'))))) ∧
      K.Catches 0 = false

/-- No `[op]` at the root of `a` captures a context holding a kept error. -/
def NoKeptCaptureRedex (a : Expr) : Prop :=
  ∀ (n i : UInt32) (qs hr hs v : Val) (K : Kont),
    a = hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))) →
      K.HasHnd n = false → kc (K.plug (.var 0)) = 0

section Head
variable {P : UInt32 → Prop}
open Classical

theorem keepRedex_shape {a : Expr} (h : KeepRedex a) : ∃ s x, a = .app (.app (.prim .cfin) s) x := by
  obtain ⟨K, m, j, w, rfl, -, -⟩ := h
  exact ⟨_, _, rfl⟩

theorem mergeRedex_shape {a : Expr} (h : MergeRedex a) : ∃ s x, a = .app (.app (.prim .cfin) s) x := by
  obtain ⟨K, E, E', rfl, -⟩ := h
  exact ⟨_, _, rfl⟩

theorem reraiseRedex_shape {a : Expr} (h : ReraiseRedex a) : ∃ x, a = .app (.prim .ccatch) x := by
  obtain ⟨K, E, rfl, -⟩ := h
  exact ⟨_, rfl⟩

/-- A redex that is no `cfin` or `ccatch` application changes the count only by what it holds and
what it builds. -/
theorem head_count_plain {a a' : Expr} (hcf : ∀ s x, a ≠ .app (.app (.prim .cfin) s) x)
    (hcc : ∀ x, a ≠ .app (.prim .ccatch) x) (ha : kc a = 0) (ha' : kc a' = 0) :
    kc a' + (if ReraiseRedex a then 1 else 0) + (if MergeRedex a then 1 else 0) =
      kc a + (if KeepRedex a then 1 else 0) := by
  have h₁ : ¬ KeepRedex a := fun h => by obtain ⟨s, x, hx⟩ := keepRedex_shape h; exact hcf s x hx
  have h₂ : ¬ MergeRedex a := fun h => by obtain ⟨s, x, hx⟩ := mergeRedex_shape h; exact hcf s x hx
  have h₃ : ¬ ReraiseRedex a := fun h => by obtain ⟨x, hx⟩ := reraiseRedex_shape h; exact hcc x hx
  simp [h₁, h₂, h₃, ha, ha']

/-- On the spine at an application whose argument is a value. -/
theorem onPath_app_val {f a : Expr} (ha : IsVal a) (h : OnPath (.app f a)) :
    kc a = 0 ∧ (IsVal f → kc f = 0) ∧ (¬ IsVal f → OnPath f) := by
  simp only [OnPath, isValB_of_isVal ha, if_true] at h
  refine ⟨h.1, fun hf => ?_, fun hf => ?_⟩
  · simpa [isValB_of_isVal hf] using h.2
  · simpa [isValB_eq_false hf] using h.2

/-- On the spine at an application whose argument is not a value. -/
theorem onPath_app_nval {f a : Expr} (ha : ¬ IsVal a) (h : OnPath (.app f a)) :
    OnPath a ∧ holdAt f a = 0 ∧
      (kc f = 0 ∨ ∃ s, f = .app (.prim .cfin) s ∧ isValB s = true ∧ kc s = 0) := by
  simpa [OnPath, isValB_eq_false ha] using h

theorem kc_val_pair {v w : Val} : kc (Val.pair v w).1 = kc v.1 + kc w.1 := rfl

/-- A running finaliser's `cfin` frame at a value state holding nothing, its body on its spine. -/
theorem onPath_cfin {s x : Expr} (hs : IsVal s) (hks : kc s = 0) (hx : OnPath x) :
    OnPath (.app (.app (.prim .cfin) s) x) := by
  simp only [OnPath]
  split
  · rename_i hb
    refine ⟨kc_of_onPath_val (isVal_of_isValB _ hb) hx, ?_⟩
    simp only [isValB, Bool.false_eq_true, if_false, isValB_of_isVal hs, if_true, hks,
      true_and]
    rfl
  · exact ⟨hx, rfl, .inr ⟨s, rfl, isValB_of_isVal hs, hks⟩⟩

/-- A raise at a value payload holding nothing is on its spine. -/
theorem onPath_raise {p : Val} (hp : kc p.1 = 0) : OnPath (raiseE (.val p)) := by
  show OnPath (.app (.prim .raise) p.1)
  simp only [OnPath, isValB_of_isVal p.2, if_true, isValB]
  exact ⟨hp, rfl⟩

theorem kc_cancelVal (err : Option Val) : kc (cancelVal err).1 = (match err with
    | none => 0 | some E => kc E.1) := by
  cases err <;> simp [cancelVal, opPayload, errVal, Val.pair, Val.i32, Val.inj₁, Val.inj₂,
    Val.unit, kc]

theorem kc_opPayload (m j : UInt32) (w : Val) : kc (opPayload m j w).1 = kc w.1 := by
  simp [opPayload, Val.pair, Val.i32, kc]

theorem kc_raise_cancelVal (err : Option Val) :
    kc (raiseE (.val (cancelVal err))) = (if err.isSome then 1 else 0) + kc (cancelVal err).1 := by
  show holdAt (.prim .raise) (cancelVal err).1 + 0 + kc (cancelVal err).1 = _
  simp only [holdAt, keptB_cancelVal, Nat.add_zero]

theorem kc_raise_payload {m j : UInt32} (hm : m ≠ 0) (w : Val) :
    kc (raiseE (.val (opPayload m j w))) = kc w.1 := by
  show holdAt (.prim .raise) (opPayload m j w).1 + 0 + kc (opPayload m j w).1 = _
  simp only [holdAt, not_keptB_opPayload hm, Nat.zero_add, Nat.add_zero, Bool.false_eq_true,
    if_false, kc_opPayload]

theorem kc_cfin_state (err : Option Val) (x : Expr) :
    kc (cfinE (cancelVal err) x) = (if err.isSome then 1 else 0) + kc (cancelVal err).1 + kc x := by
  show 0 + (holdAt (.prim .cfin) (cancelVal err).1 + 0 + kc (cancelVal err).1) + kc x = _
  simp only [holdAt, keptB_cancelVal, Nat.zero_add, Nat.add_zero]

/-- **A context that stops a raise holds no kept error**, on its spine: a running finaliser's
`cfin` frame stops every raise, and nothing off the spine holds one. -/
theorem kc_plug_var_of_catches (hP0 : ¬ P 0) {n : UInt32} : ∀ {K : Kont}, KRaiseOK P K →
    OnPath (K.plug (.var 0)) → K.Catches n = false → kc (K.plug (.var 0)) = 0
  | .hole, _, _, _ => rfl
  | .pairL K e, hK, h, hc => by
      have hK' : KRaiseOK P K := (show (Expr.pair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath, isValB_eq_false (not_isVal_plug K (not_isVal_var (i := 0))),
        Bool.false_eq_true, if_false] at h
      simp only [Kont.plug, kc, kc_plug_var_of_catches hP0 hK' h.1 hc, h.2]
  | .pairR v K, hK, h, hc => by
      have hK' : KRaiseOK P K := (show (Expr.pair v.1 (K.plug (.var 0))).RaiseOK P from hK).2
      simp only [Kont.plug, OnPath, isValB_of_isVal v.2, if_true] at h
      simp only [Kont.plug, kc, kc_plug_var_of_catches hP0 hK' h.2 hc, h.1]
  | .letpair K e, hK, h, hc => by
      have hK' : KRaiseOK P K := (show (Expr.letpair (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath] at h
      simp only [Kont.plug, kc, kc_plug_var_of_catches hP0 hK' h.1 hc, h.2]
  | .case K e₁ e₂, hK, h, hc => by
      have hK' : KRaiseOK P K := (show (Expr.case (K.plug (.var 0)) e₁ e₂).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath] at h
      simp only [Kont.plug, kc, kc_plug_var_of_catches hP0 hK' h.1 hc, h.2.1, h.2.2]
  | .seq K e, hK, h, hc => by
      have hK' : KRaiseOK P K := (show (Expr.seq (K.plug (.var 0)) e).RaiseOK P from hK).1
      simp only [Kont.plug, OnPath] at h
      simp only [Kont.plug, kc, kc_plug_var_of_catches hP0 hK' h.1 hc, h.2]
  | .inj₁ K, hK, h, hc => by
      simp only [Kont.plug, kc]; exact kc_plug_var_of_catches hP0 (K := K) hK h hc
  | .inj₂ K, hK, h, hc => by
      simp only [Kont.plug, kc]; exact kc_plug_var_of_catches hP0 (K := K) hK h hc
  | .appL K v, hK, h, hc => by
      obtain ⟨hK', -⟩ := kraiseOK_appL hK
      have h' := onPath_app_val v.2 h
      simp only [Kont.plug, kc, holdAt_of_raiseOK hK',
        kc_plug_var_of_catches hP0 hK' (h'.2.2 (not_isVal_plug K (not_isVal_var (i := 0)))) hc,
        h'.1]
  | .appR f K, hK, h, hc => by
      have hK' := kraiseOK_appR hK
      obtain ⟨h₁, h₂, h₃⟩ := onPath_app_nval (not_isVal_plug K (not_isVal_var (i := 0))) h
      have hc' : K.Catches n = false := by
        simp only [Kont.Catches, Bool.or_eq_false_iff] at hc; exact hc.2
      have hf : kc f = 0 := by
        rcases h₃ with h₃ | ⟨s, rfl, -, -⟩
        · exact h₃
        · simp [Kont.Catches] at hc
      simp only [Kont.plug, kc, h₂, hf, kc_plug_var_of_catches hP0 hK' h₁ hc']

theorem hndName_ne_zero {n : UInt32} {qs hr hs : Val} {e : Expr}
    (h : (hndE (hndVal n qs hr hs) e).HndNamesNZ) : n ≠ 0 := by
  have h₁ := (hndNZ_app _ _).1 h
  rcases h₁ with ⟨hf, -⟩ | ⟨-, hf, -⟩
  · simp [Expr.val] at hf
  · rcases (hndNZ_app _ _).1 hf with ⟨-, m, r, hr', hm, -⟩ | ⟨hne, -⟩
    · have e₀ : (hndVal n qs hr hs).1 =
          Expr.pair (.prim (.lit (.i32 n))) (.pair qs.1 (.pair hr.1 hs.1)) := rfl
      have hr'' : Expr.pair (.prim (.lit (.i32 n))) (.pair qs.1 (.pair hr.1 hs.1)) =
          .pair (.prim (.lit (.i32 m))) r := e₀ ▸ hr'
      simp only [Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hr''
      exact hr''.1 ▸ hm
    · exact absurd rfl hne

theorem kc_hndE (H : Val) (e : Expr) : kc (hndE H e) = kc H.1 + kc e := by
  show holdAt (.app (.prim .hnd) H.1) e + (holdAt (.prim .hnd) H.1 + 0 + kc H.1) + kc e = _
  simp only [holdAt_app, holdAt_hnd, Nat.zero_add, Nat.add_zero]

theorem kc_ubindE (ND : Val) (e : Expr) : kc (ubindE ND e) = kc ND.1 + kc e := by
  show holdAt (.app (.prim .ubind) ND.1) e + (holdAt (.prim .ubind) ND.1 + 0 + kc ND.1) + kc e = _
  simp only [holdAt_app, holdAt_ubind, Nat.zero_add, Nat.add_zero]

theorem kc_ccatchE (e : Expr) : kc (ccatchE e) = kc e := by
  show holdAt (.prim .ccatch) e + 0 + kc e = _
  simp only [holdAt_ccatch, Nat.zero_add, Nat.add_zero]

theorem kc_performE (p : Val) : kc (performE (.val p)) = kc p.1 := by
  show holdAt (.prim .perform) p.1 + 0 + kc p.1 = _
  simp only [holdAt_perform, Nat.zero_add, Nat.add_zero]

/-- A handler frame's function part, read off the spine condition: it holds nothing. -/
theorem kc_hnd_of {H : Val} (h : kc (Expr.app (.val (Val.prim .hnd)) (.val H)) = 0 ∨
    ∃ s, Expr.app (.val (Val.prim .hnd)) (.val H) = .app (.prim .cfin) s ∧ isValB s = true ∧
      kc s = 0) : kc H.1 = 0 := by
  rcases h with h | ⟨s, hs, -, -⟩
  · have h' : holdAt (.prim .hnd) H.1 + 0 + kc H.1 = 0 := h
    omega
  · simp [Expr.val, Val.prim] at hs

theorem kc_ubind_of {ND : Val} (h : kc (Expr.app (.val (Val.prim .ubind)) (.val ND)) = 0 ∨
    ∃ s, Expr.app (.val (Val.prim .ubind)) (.val ND) = .app (.prim .cfin) s ∧ isValB s = true ∧
      kc s = 0) : kc ND.1 = 0 := by
  rcases h with h | ⟨s, hs, -, -⟩
  · have h' : holdAt (.prim .ubind) ND.1 + 0 + kc ND.1 = 0 := h
    omega
  · simp [Expr.val, Val.prim] at hs

theorem kc_cfin_of {err : Option Val}
    (h : kc (Expr.app (.val (Val.prim .cfin)) (.val (cancelVal err))) = 0 ∨
      ∃ s, Expr.app (.val (Val.prim .cfin)) (.val (cancelVal err)) = .app (.prim .cfin) s ∧
        isValB s = true ∧ kc s = 0) : kc (cancelVal err).1 = 0 := by
  rcases h with h | ⟨s, hs, -, hks⟩
  · have h' : holdAt (.prim .cfin) (cancelVal err).1 + 0 + kc (cancelVal err).1 = 0 := h
    omega
  · simp only [Expr.val, Val.prim, Expr.app.injEq, true_and] at hs
    rw [hs]; exact hks

/-- **A head step changes the kept errors only as the algebra says**: `[cfin-raise]` at a cancel
that kept nothing keeps one more, `[cancel-raise]` re-raises one at its canceller, `[cfin-cancel]`
at two kept errors keeps the earlier; every other step keeps the count, provided `[op]` captures
no context holding a kept error.  The step keeps every holder on the spine, and every stored value
free of kept errors.  At the names `P` (`0` not one of them), every handler named nonzero. -/
theorem kc_head (hP0 : ¬ P 0) {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a')
    (hok : a.RaiseOK P) (hnz : a.HndNamesNZ) (hon : OnPath a) (hμ : HeapKC μ)
    (hcap : NoKeptCaptureRedex a) :
    OnPath a' ∧ HeapKC μ' ∧
      kc a' + (if ReraiseRedex a then 1 else 0) + (if MergeRedex a then 1 else 0) =
        kc a + (if KeepRedex a then 1 else 0) := by
  cases h with
  | beta b v =>
      obtain ⟨hv, hb, -⟩ := onPath_app_val v.2 hon
      have hb0 : kc b = 0 := hb .lam
      have hr := raiseOK_app_inv (f := .lam b) (fun h => (nomatch h)) (fun h => (nomatch h)) hok
      have ha' : kc (b.subst 0 v) = 0 := by rw [kc_subst hP0 b 0 v hr.1 hr.2 hv]; exact hb0
      refine ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) ?_ ha'⟩
      simp only [Expr.val, Val.lam, kc, holdAt_lam, hb0, hv]
  | alloc v ℓ hℓ =>
      obtain ⟨hv, -, -⟩ := onPath_app_val v.2 hon
      refine ⟨trivial, heapKC_upd hμ ℓ hv, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) ?_ rfl⟩
      simp only [Expr.val, Val.prim, kc, holdAt_alloc, hv]
  | free ℓ v hv =>
      refine ⟨onPath_of_kc (hμ ℓ v hv), heapKC_del hμ ℓ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) rfl (hμ ℓ v hv)⟩
  | load ℓ v hv =>
      exact ⟨onPath_of_kc (hμ ℓ v hv), hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) rfl (hμ ℓ v hv)⟩
  | store ℓ v w hw =>
      obtain ⟨hv, -, -⟩ := onPath_app_val v.2 hon
      refine ⟨trivial, heapKC_upd hμ ℓ hv, head_count_plain (fun _ _ h => by
        simp only [Expr.val, Val.prim, Val.loc, Expr.app.injEq, Expr.prim.injEq] at h
        exact absurd h.1.1 (by decide)) (fun _ h => by cases h) ?_ rfl⟩
      simp only [Expr.val, Val.prim, Val.loc, kc, holdAt_app, holdAt_store, hv]
  | seq _ =>
      have he : kc a' = 0 := hon.2
      exact ⟨onPath_of_kc he, hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.unit, kc, he]) he⟩
  | letpair v₁ v₂ e =>
      have hp := kc_of_onPath_val (Val.pair v₁ v₂).2 hon.1
      have he : kc e = 0 := hon.2
      simp only [kc_val_pair, Nat.add_eq_zero_iff] at hp
      have hr : (Val.pair v₁ v₂).1.RaiseOK P := hok.1
      have hr₂ : (v₂.shift 1 0).1.RaiseOK P := raiseOK_val_shift hr.2 1 0
      have ha' : kc ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁) = 0 := by
        rw [kc_subst hP0 _ 0 v₁ (raiseOK_subst e 0 _ hok.2 hr₂) hr.1 hp.1,
          kc_subst hP0 e 0 _ hok.2 hr₂ (by rw [kc_val_shift]; exact hp.2)]
        exact he
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, kc, kc_val_pair] at *; omega) ha'⟩
  | case₁ v e₁ e₂ =>
      have hv := kc_of_onPath_val (Val.inj₁ v).2 hon.1
      have hr : (Val.inj₁ v).1.RaiseOK P := hok.1
      have ha' : kc (e₁.subst 0 v) = 0 := by
        rw [kc_subst hP0 e₁ 0 v hok.2.1 hr hv]; exact hon.2.1
      have h₁ : kc e₁ = 0 := hon.2.1
      have h₂ : kc e₂ = 0 := hon.2.2
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.inj₁, kc] at hv ⊢; omega) ha'⟩
  | case₂ v e₁ e₂ =>
      have hv := kc_of_onPath_val (Val.inj₂ v).2 hon.1
      have hr : (Val.inj₂ v).1.RaiseOK P := hok.1
      have ha' : kc (e₂.subst 0 v) = 0 := by
        rw [kc_subst hP0 e₂ 0 v hok.2.2 hr hv]; exact hon.2.2
      have h₁ : kc e₁ = 0 := hon.2.1
      have h₂ : kc e₂ = 0 := hon.2.2
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.inj₂, kc] at hv ⊢; omega) ha'⟩
  | host op v r hr =>
      obtain ⟨hv, -, -⟩ := onPath_app_val v.2 hon
      exact ⟨onPath_of_kc (kc_host ℍ op hr), hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.prim, kc, hv]; rfl) (kc_host ℍ op hr)⟩
  | tab c f ℓ hℓ =>
      obtain ⟨hv, -, -⟩ := onPath_app_val (Val.pair (Val.i32 c) f).2 hon
      have hr := (raiseOK_primApp (P := P) (by decide) (by decide) _).1 hok
      have hf : kc f.1 = 0 := by
        have h' := hv
        simp only [Val.pair, Val.i32, kc] at h'
        omega
      have ha' := kc_tabFill hr.2 hf ℓ (arrLen c) 0 (arrLen c).toNat
      exact ⟨onPath_of_kc ha', heapKC_fill hμ ℓ _ rfl, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.prim, kc, hv]; rfl) ha'⟩
  | idx ℓ n i =>
      have ha' : kc (idxAns ℓ n i).1 = 0 := by simp only [idxAns]; split <;> rfl
      obtain ⟨hv, -, -⟩ := onPath_app_val (Val.pair (Val.arr ℓ n) (Val.i32 i)).2 hon
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.prim, kc, hv]; rfl) ha'⟩
  | split ℓ n i =>
      have ha' : kc (splitAns ℓ n i).1 = 0 := by simp only [splitAns]; split <;> rfl
      obtain ⟨hv, -, -⟩ := onPath_app_val (Val.pair (Val.arr ℓ n) (Val.i32 i)).2 hon
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.prim, kc, hv]; rfl) ha'⟩
  | drop f ℓ n =>
      obtain ⟨hv, -, -⟩ := onPath_app_val (Val.pair f (Val.arr ℓ n)).2 hon
      have hr := (raiseOK_primApp (P := P) (by decide) (by decide) _).1 hok
      have hf : kc f.1 = 0 := by simp only [kc_val_pair, Nat.add_eq_zero_iff] at hv; exact hv.1
      have ha' := kc_dropFill hr.1 hf ℓ 0 n.toNat
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h) (by simp only [Expr.val, Val.prim, kc, hv]; rfl) ha'⟩
  | count f n i s' =>
      obtain ⟨hv, -, -⟩ := onPath_app_val
        (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s'))).2 hon
      have hr := (raiseOK_primApp (P := P) (by decide) (by decide) _).1 hok
      have hfr : f.1.RaiseOK P := hr.1
      simp only [kc_val_pair, Nat.add_eq_zero_iff] at hv
      have hf : kc f.1 = 0 := hv.1
      have hs : kc s'.1 = 0 := hv.2.2.2
      have ha' : kc (countNext f n i s') = 0 := by
        simp only [countNext]
        split
        · simp only [kc, Expr.val, Val.prim, Val.pair, Val.i32, holdAt_count, hf, hs,
            holdAt_of_raiseOK hfr]
        · exact hs
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h)
        (by simp only [Expr.val, Val.prim, kc, kc_val_pair, hf, hs, holdAt_count]; rfl) ha'⟩
  | countTry f n i s' =>
      obtain ⟨hv, -, -⟩ := onPath_app_val
        (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s'))).2 hon
      have hr := (raiseOK_primApp (P := P) (by decide) (by decide) _).1 hok
      have hfr : f.1.RaiseOK P := hr.1
      simp only [kc_val_pair, Nat.add_eq_zero_iff] at hv
      have hf : kc f.1 = 0 := hv.1
      have hs : kc s'.1 = 0 := hv.2.2.2
      have ha' : kc (countTryNext f n i s') = 0 := by
        simp only [countTryNext]
        split
        · simp only [kc, Expr.val, Val.prim, Val.pair, Val.i32, Val.val_shift, kc_shift,
            holdAt_countTry, hf, hs, holdAt_of_raiseOK hfr]
        · exact hs
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h)
        (by simp only [Expr.val, Val.prim, kc, kc_val_pair, hf, hs, holdAt_countTry]; rfl) ha'⟩
  | boundedFix s' k b =>
      obtain ⟨hv, -, -⟩ := onPath_app_val (Val.pair s' (Val.pair (Val.i32 k) b)).2 hon
      have hr := (raiseOK_primApp (P := P) (by decide) (by decide) _).1 hok
      have hsr : s'.1.RaiseOK P := hr.1
      simp only [kc_val_pair, Nat.add_eq_zero_iff] at hv
      have hs : kc s'.1 = 0 := hv.1
      have hb : kc b.1 = 0 := hv.2.2
      have hfix : kc (fixSelf s' k).1 = 0 := by
        simp only [fixSelf]
        split
        · rfl
        · simp only [Val.inj₂, Val.lam, kc, Expr.val, Val.prim, Val.i32, Val.val_shift,
            kc_shift, hs, holdAt_boundedFix]
      have ha' : kc (boundedFixNext s' k b) = 0 := by
        simp only [boundedFixNext, kc, Expr.val, holdAt_of_raiseOK hsr, kc_val_pair, hs, hfix, hb]
      exact ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => by cases h)
        (fun _ h => by cases h)
        (by simp only [Expr.val, Val.prim, kc, kc_val_pair, hs, hb, holdAt_boundedFix]; rfl) ha'⟩
  | hret n qs hr hs w =>
      obtain ⟨hw, -, hH⟩ := onPath_app_val w.2 hon
      have hH' := hH (by simp)
      obtain ⟨hHv, -, -⟩ := onPath_app_val (hndVal n qs hr hs).2 hH'
      have hrr := (raiseOK_hndVal.1 (raiseOK_hndE.1 hok).1).2.1
      have hk : kc hr.1 = 0 := by
        simp only [hndVal, kc_val_pair, Nat.add_eq_zero_iff] at hHv; exact hHv.2.2.1
      have ha' : kc (Expr.app (.val hr) (.val w)) = 0 := kc_app_of hrr hk hw
      refine ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => ?_) (fun _ h => by cases h) ?_ ha'⟩
      · simp [hndE, Expr.val, Val.prim] at h
      · rw [kc_hndE, hHv, hw]
  | hop n i qs hr hs c v K hc hK =>
      have hnv : ¬ IsVal (K.plug (performE (.val (opPayload n i v)))) :=
        not_isVal_plug K (opE_not_isVal false _)
      obtain ⟨hb, -, hHf⟩ := onPath_app_nval hnv hon
      have hH : kc (hndVal n qs hr hs).1 = 0 := kc_hnd_of hHf
      obtain ⟨hKo, hp⟩ := onPath_plug_inv K (plain_perform _) (opE_not_isVal false _) hb
      obtain ⟨hHr, hbr⟩ := raiseOK_hndE.1 hok
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_perform _) hbr
      have hpv := (onPath_app_val (opPayload n i v).2 hp).1
      have hv : kc v.1 = 0 := by rw [kc_opPayload] at hpv; exact hpv
      have hK0 := hcap n i qs hr hs v K rfl hK
      have hcr := raiseOK_clauseAt hs.1 i.toNat hc (raiseOK_hndVal.1 hHr).2.2
      have hck : kc c.1 = 0 := kc_clauseAt hs.1 i.toNat hc (by
        simp only [hndVal, kc_val_pair, Nat.add_eq_zero_iff] at hH; exact hH.2.2.2)
      have ha' : kc (Expr.app (.val c) (.pair (.val v) (kappaAt (capTag qs.1 i.toNat)
          (hndVal n qs hr hs) K))) = 0 := by
        show holdAt c.1 _ + kc c.1 + (kc v.1 + kc (kappaAt (capTag qs.1 i.toNat)
          (hndVal n qs hr hs) K)) = 0
        rw [holdAt_of_raiseOK hcr, hck, hv, kc_kappaAt hP0 _ hH hKr hK0]
      refine ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => ?_) (fun _ h => by cases h) ?_ ha'⟩
      · simp [hndE, Expr.val, Val.prim] at h
      · rw [kc_hndE, hH, kc_plug hP0 K hKr hpr, hK0, kc_performE, hpv]
  | hunwind n i qs hr hs c v K hc hK =>
      have hnv : ¬ IsVal (K.plug (raiseE (.val (opPayload n i v)))) :=
        not_isVal_plug K (opE_not_isVal true _)
      obtain ⟨hb, -, hHf⟩ := onPath_app_nval hnv hon
      have hH : kc (hndVal n qs hr hs).1 = 0 := kc_hnd_of hHf
      obtain ⟨hKo, hp⟩ := onPath_plug_inv K (plain_raise _) (opE_not_isVal true _) hb
      obtain ⟨hHr, hbr⟩ := raiseOK_hndE.1 hok
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_raise _) hbr
      have hpv := (onPath_app_val (opPayload n i v).2 hp).1
      have hv : kc v.1 = 0 := by rw [kc_opPayload] at hpv; exact hpv
      have hn := hndName_ne_zero hnz
      have hcr := raiseOK_clauseAt hs.1 i.toNat hc (raiseOK_hndVal.1 hHr).2.2
      have hck : kc c.1 = 0 := kc_clauseAt hs.1 i.toNat hc (by
        simp only [hndVal, kc_val_pair, Nat.add_eq_zero_iff] at hH; exact hH.2.2.2)
      have ha' : kc (Expr.app (.val c) (.val v)) = 0 := kc_app_of hcr hck hv
      refine ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => ?_) (fun _ h => by cases h) ?_ ha'⟩
      · simp [hndE, Expr.val, Val.prim] at h
      · rw [kc_hndE, hH, kc_plug hP0 K hKr hpr, kc_plug_var_of_catches hP0 hKr hKo hK,
          kc_raise_payload hn, hv]
  | uthen N D w =>
      obtain ⟨hw, -, hND⟩ := onPath_app_val w.2 hon
      obtain ⟨hNDv, -, -⟩ := onPath_app_val (Val.pair N D).2 (hND (by simp))
      have hNr := (raiseOK_ubindE.1 hok).1.1
      have hN : kc N.1 = 0 := by simp only [kc_val_pair, Nat.add_eq_zero_iff] at hNDv; exact hNDv.1
      have ha' : kc (Expr.app (.val N) (.val w)) = 0 := kc_app_of hNr hN hw
      refine ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => ?_) (fun _ h => by cases h) ?_ ha'⟩
      · simp [ubindE, Expr.val, Val.prim] at h
      · rw [kc_ubindE, hNDv, hw]
  | ufin N D n i v K hn hK =>
      have hnv : ¬ IsVal (K.plug (raiseE (.val (opPayload n i v)))) :=
        not_isVal_plug K (opE_not_isVal true _)
      obtain ⟨hb, -, hNDf⟩ := onPath_app_nval hnv hon
      have hND : kc (Val.pair N D).1 = 0 := kc_ubind_of hNDf
      obtain ⟨hKo, hp⟩ := onPath_plug_inv K (plain_raise _) (opE_not_isVal true _) hb
      obtain ⟨hNDr, hbr⟩ := raiseOK_ubindE.1 hok
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_raise _) hbr
      have hpv := (onPath_app_val (opPayload n i v).2 hp).1
      have hv : kc v.1 = 0 := by rw [kc_opPayload] at hpv; exact hpv
      have hND' := hND
      simp only [kc_val_pair, Nat.add_eq_zero_iff] at hND'
      have hD : kc (Expr.app (.val D) (.val .unit)) = 0 := kc_app_of hNDr.2 hND'.2 rfl
      have ha' : kc (Expr.seq (.app (.val D) (.val .unit)) (raiseE (.val (opPayload n i v)))) = 0 := by
        show kc (Expr.app (.val D) (.val .unit)) + kc (raiseE (.val (opPayload n i v))) = 0
        rw [hD, kc_raise_payload hn, hv]
      refine ⟨onPath_of_kc ha', hμ, head_count_plain (fun _ _ h => ?_) (fun _ h => by cases h) ?_ ha'⟩
      · simp [ubindE, Expr.val, Val.prim] at h
      · rw [kc_ubindE, hND, kc_plug hP0 K hKr hpr, kc_plug_var_of_catches hP0 hKr hKo hK,
          kc_raise_payload hn, hv]
  | ufinC N D err K hK =>
      have hnv : ¬ IsVal (K.plug (raiseE (.val (cancelVal err)))) :=
        not_isVal_plug K (opE_not_isVal true _)
      obtain ⟨hb, -, hNDf⟩ := onPath_app_nval hnv hon
      have hND : kc (Val.pair N D).1 = 0 := kc_ubind_of hNDf
      obtain ⟨hKo, hp⟩ := onPath_plug_inv K (plain_raise _) (opE_not_isVal true _) hb
      obtain ⟨hNDr, hbr⟩ := raiseOK_ubindE.1 hok
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_raise _) hbr
      have hpv := (onPath_app_val (cancelVal err).2 hp).1
      have hND' := hND
      simp only [kc_val_pair, Nat.add_eq_zero_iff] at hND'
      have hD : kc (Expr.app (.val D) (.val .unit)) = 0 := kc_app_of hNDr.2 hND'.2 rfl
      refine ⟨onPath_cfin (cancelVal err).2 hpv (onPath_of_kc hD), hμ, ?_⟩
      have h₁ : ∀ s x, ubindE (Val.pair N D) (K.plug (raiseE (.val (cancelVal err)))) ≠
          .app (.app (.prim .cfin) s) x := fun _ _ h => by simp [ubindE, Expr.val, Val.prim] at h
      have n₁ : ¬ KeepRedex (ubindE (Val.pair N D) (K.plug (raiseE (.val (cancelVal err))))) :=
        fun h => by obtain ⟨s, x, hx⟩ := keepRedex_shape h; exact h₁ s x hx
      have n₂ : ¬ MergeRedex (ubindE (Val.pair N D) (K.plug (raiseE (.val (cancelVal err))))) :=
        fun h => by obtain ⟨s, x, hx⟩ := mergeRedex_shape h; exact h₁ s x hx
      have n₃ : ¬ ReraiseRedex (ubindE (Val.pair N D) (K.plug (raiseE (.val (cancelVal err))))) :=
        fun h => by obtain ⟨x, hx⟩ := reraiseRedex_shape h; cases hx
      rw [if_neg n₁, if_neg n₂, if_neg n₃, kc_cfin_state, hpv, hD, kc_ubindE, hND,
        kc_plug hP0 K hKr hpr, kc_plug_var_of_catches hP0 hKr hKo hK, kc_raise_cancelVal, hpv]
      omega
  | cfret err w =>
      obtain ⟨hw, -, hs⟩ := onPath_app_val w.2 hon
      have hs' := (onPath_app_val (cancelVal err).2 (hs (by simp))).1
      refine ⟨onPath_raise hs', hμ, ?_⟩
      have n₁ : ¬ KeepRedex (cfinE (cancelVal err) (.val w)) := by
        rintro ⟨K, m, j, w', h, -, -⟩
        simp only [cfinE, Expr.app.injEq] at h
        exact plug_raise_ne_val K _ w h.2.symm
      have n₂ : ¬ MergeRedex (cfinE (cancelVal err) (.val w)) := by
        rintro ⟨K, E, E', h, -⟩
        simp only [cfinE, Expr.app.injEq] at h
        exact plug_raise_ne_val K _ w h.2.symm
      have n₃ : ¬ ReraiseRedex (cfinE (cancelVal err) (.val w)) := fun h => by
        obtain ⟨x, hx⟩ := reraiseRedex_shape h; simp [cfinE] at hx
      rw [if_neg n₁, if_neg n₂, if_neg n₃, kc_raise_cancelVal, kc_cfin_state, hs', hw]
  | cferr err m j w K hm hK =>
      have hnv : ¬ IsVal (K.plug (raiseE (.val (opPayload m j w)))) :=
        not_isVal_plug K (opE_not_isVal true _)
      obtain ⟨hb, -, hsf⟩ := onPath_app_nval hnv hon
      have hs : kc (cancelVal err).1 = 0 := kc_cfin_of hsf
      obtain ⟨hKo, hp⟩ := onPath_plug_inv K (plain_raise _) (opE_not_isVal true _) hb
      have hbr := (raiseOK_cfinE.1 hok).2
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_raise _) hbr
      have hpv := (onPath_app_val (opPayload m j w).2 hp).1
      have hw : kc w.1 = 0 := by rw [kc_opPayload] at hpv; exact hpv
      have hnext : kc (cancelVal (errNext err m j w)).1 = 0 := by
        cases err with
        | none => rw [kc_cancelVal]; exact hpv
        | some E => rw [kc_cancelVal]; rw [kc_cancelVal] at hs; exact hs
      refine ⟨onPath_raise hnext, hμ, ?_⟩
      have n₂ : ¬ MergeRedex (cfinE (cancelVal err) (K.plug (raiseE (.val (opPayload m j w))))) := by
        rintro ⟨K', E, E', h, -⟩
        simp only [cfinE, Expr.app.injEq] at h
        obtain ⟨-, hp'⟩ := plug_raise_inj h.2.symm
        obtain ⟨rfl, -, -⟩ := opPayload_inj hp'
        exact hm rfl
      have n₃ : ¬ ReraiseRedex (cfinE (cancelVal err) (K.plug (raiseE (.val (opPayload m j w))))) :=
        fun h => by obtain ⟨x, hx⟩ := reraiseRedex_shape h; simp [cfinE] at hx
      have hkeep : KeepRedex (cfinE (cancelVal err) (K.plug (raiseE (.val (opPayload m j w))))) ↔
          err = none := by
        constructor
        · rintro ⟨K', m', j', w', h, -, -⟩
          simp only [cfinE, Expr.app.injEq, true_and] at h
          exact cancelVal_inj (Subtype.ext h.1)
        · rintro rfl; exact ⟨K, m, j, w, rfl, hm, hK⟩
      rw [if_neg n₂, if_neg n₃, kc_raise_cancelVal, hnext, kc_cfin_state, hs,
        kc_plug hP0 K hKr hpr, kc_plug_var_of_catches hP0 hKr hKo hK, kc_raise_payload hm, hw]
      cases err <;> simp [errNext, hkeep]
  | cfcancel err err' K hK =>
      have hnv : ¬ IsVal (K.plug (raiseE (.val (cancelVal err')))) :=
        not_isVal_plug K (opE_not_isVal true _)
      obtain ⟨hb, -, hsf⟩ := onPath_app_nval hnv hon
      have hs : kc (cancelVal err).1 = 0 := kc_cfin_of hsf
      obtain ⟨hKo, hp⟩ := onPath_plug_inv K (plain_raise _) (opE_not_isVal true _) hb
      have hbr := (raiseOK_cfinE.1 hok).2
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_raise _) hbr
      have hpv := (onPath_app_val (cancelVal err').2 hp).1
      have hor : kc (cancelVal (err.or err')).1 = 0 := by
        cases err with
        | none => simpa [Option.or] using hpv
        | some E => simpa [Option.or] using hs
      refine ⟨onPath_raise hor, hμ, ?_⟩
      have n₁ : ¬ KeepRedex (cfinE (cancelVal err) (K.plug (raiseE (.val (cancelVal err'))))) := by
        rintro ⟨K', m', j', w', h, hm', -⟩
        simp only [cfinE, Expr.app.injEq] at h
        obtain ⟨-, hp'⟩ := plug_raise_inj h.2.symm
        obtain ⟨rfl, -, -⟩ := opPayload_inj hp'
        exact hm' rfl
      have n₃ : ¬ ReraiseRedex (cfinE (cancelVal err) (K.plug (raiseE (.val (cancelVal err'))))) :=
        fun h => by obtain ⟨x, hx⟩ := reraiseRedex_shape h; simp [cfinE] at hx
      have hmerge : MergeRedex (cfinE (cancelVal err) (K.plug (raiseE (.val (cancelVal err'))))) ↔
          (err.isSome ∧ err'.isSome) := by
        constructor
        · rintro ⟨K', E, E', h, -⟩
          simp only [cfinE, Expr.app.injEq, true_and] at h
          obtain ⟨h₁, h₂⟩ := h
          have e₁ := cancelVal_inj (Subtype.ext h₁)
          obtain ⟨-, hp'⟩ := plug_raise_inj h₂.symm
          have e₂ := cancelVal_inj hp'
          rw [e₁]
          rw [← e₂]
          simp
        · rintro ⟨h₁, h₂⟩
          obtain ⟨E, rfl⟩ := Option.isSome_iff_exists.1 h₁
          obtain ⟨E', rfl⟩ := Option.isSome_iff_exists.1 h₂
          exact ⟨K, E, E', rfl, hK⟩
      rw [if_neg n₁, if_neg n₃, kc_raise_cancelVal, hor, kc_cfin_state, hs,
        kc_plug hP0 K hKr hpr, kc_plug_var_of_catches hP0 hKr hKo hK, kc_raise_cancelVal, hpv]
      cases err <;> cases err' <;> simp [Option.or, hmerge]
  | cancel K hK =>
      have hnv : ¬ IsVal (K.plug (raiseE (.val (cancelVal none)))) :=
        not_isVal_plug K (opE_not_isVal true _)
      obtain ⟨hb, -, -⟩ := onPath_app_nval hnv hon
      obtain ⟨hKo, -⟩ := onPath_plug_inv K (plain_raise _) (opE_not_isVal true _) hb
      have hbr := raiseOK_ccatchE.1 hok
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_raise _) hbr
      refine ⟨trivial, hμ, ?_⟩
      have n₁ : ¬ KeepRedex (ccatchE (K.plug (raiseE (.val (cancelVal none))))) := fun h => by
        obtain ⟨s, x, hx⟩ := keepRedex_shape h; simp [ccatchE] at hx
      have n₂ : ¬ MergeRedex (ccatchE (K.plug (raiseE (.val (cancelVal none))))) := fun h => by
        obtain ⟨s, x, hx⟩ := mergeRedex_shape h; simp [ccatchE] at hx
      have n₃ : ¬ ReraiseRedex (ccatchE (K.plug (raiseE (.val (cancelVal none))))) := by
        rintro ⟨K', E, h, -⟩
        simp only [ccatchE, Expr.app.injEq, true_and] at h
        obtain ⟨-, hp'⟩ := plug_raise_inj h.symm
        exact absurd (cancelVal_inj hp') (by simp)
      rw [if_neg n₁, if_neg n₂, if_neg n₃, kc_ccatchE, kc_plug hP0 K hKr hpr,
        kc_plug_var_of_catches hP0 hKr hKo hK, kc_raise_cancel_none]
      rfl
  | creraise E K hK =>
      have hnv : ¬ IsVal (K.plug (raiseE (.val (cancelVal (some E))))) :=
        not_isVal_plug K (opE_not_isVal true _)
      obtain ⟨hb, -, -⟩ := onPath_app_nval hnv hon
      obtain ⟨hKo, hp⟩ := onPath_plug_inv K (plain_raise _) (opE_not_isVal true _) hb
      have hbr := raiseOK_ccatchE.1 hok
      obtain ⟨hKr, hpr⟩ := plug_raiseOK_inv K (plain_raise _) hbr
      have hpv := (onPath_app_val (cancelVal (some E)).2 hp).1
      have hE : kc E.1 = 0 := by rw [kc_cancelVal] at hpv; exact hpv
      obtain ⟨m, j, w, rfl, hPm, -⟩ := (raiseOK_raise_cancel hP0).1 hpr
      have hm : m ≠ 0 := fun h0 => hP0 (h0 ▸ hPm)
      have ha' : kc (raiseE (.val (opPayload m j w))) = 0 := by
        rw [kc_raise_payload hm]; rw [kc_opPayload] at hE; exact hE
      refine ⟨onPath_of_kc ha', hμ, ?_⟩
      have n₁ : ¬ KeepRedex (ccatchE (K.plug (raiseE (.val (cancelVal (some (opPayload m j w))))))) :=
        fun h => by obtain ⟨s, x, hx⟩ := keepRedex_shape h; simp [ccatchE] at hx
      have n₂ : ¬ MergeRedex (ccatchE (K.plug (raiseE (.val (cancelVal (some (opPayload m j w))))))) :=
        fun h => by obtain ⟨s, x, hx⟩ := mergeRedex_shape h; simp [ccatchE] at hx
      have y₃ : ReraiseRedex (ccatchE (K.plug (raiseE (.val (cancelVal (some (opPayload m j w))))))) :=
        ⟨K, _, rfl, hK⟩
      rw [if_neg n₁, if_neg n₂, if_pos y₃, ha', kc_ccatchE, kc_plug hP0 K hKr hpr,
        kc_plug_var_of_catches hP0 hKr hKo hK, kc_raise_cancelVal, hpv]
      rfl

end Head

/-! ### A machine step -/

/-- **A configuration at `[cfin-raise]` keeping a new error.** -/
def KeepAt (e : Expr) : Prop := ∃ (K : Kont) (a : Expr), e = K.plug a ∧ KeepRedex a

/-- **A configuration at `[cancel-raise]`**, re-raising a kept error at its canceller. -/
def ReraiseAt (e : Expr) : Prop := ∃ (K : Kont) (a : Expr), e = K.plug a ∧ ReraiseRedex a

/-- **A configuration at `[cfin-cancel]` at two kept errors.** -/
def MergeAt (e : Expr) : Prop := ∃ (K : Kont) (a : Expr), e = K.plug a ∧ MergeRedex a

/-- **No `[op]` step at the configuration captures a context holding a kept error.** -/
def NoKeptCaptureAt (e : Expr) : Prop := ∀ (K : Kont) (a : Expr), e = K.plug a → NoKeptCaptureRedex a

section Step
variable {P : UInt32 → Prop}
open Classical

theorem head_of_keepRedex {a : Expr} (h : KeepRedex a) (μ : Heap) :
    ∃ a', Head (ℍ := ℍ) μ a μ a' := by
  obtain ⟨K, m, j, w, rfl, hm, hK⟩ := h
  exact ⟨_, Head.cferr μ none m j w K hm hK⟩

theorem head_of_reraiseRedex {a : Expr} (h : ReraiseRedex a) (μ : Heap) :
    ∃ a', Head (ℍ := ℍ) μ a μ a' := by
  obtain ⟨K, E, rfl, hK⟩ := h
  exact ⟨_, Head.creraise μ E K hK⟩

theorem head_of_mergeRedex {a : Expr} (h : MergeRedex a) (μ : Heap) :
    ∃ a', Head (ℍ := ℍ) μ a μ a' := by
  obtain ⟨K, E, E', rfl, hK⟩ := h
  exact ⟨_, Head.cfcancel μ (some E) (some E') K hK⟩

/-- At a configuration whose redex is `a`, the configuration keeps a new error exactly when `a` is
that step (Core's unique decomposition). -/
theorem keepAt_iff {μ μ' : Heap} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a') (K : Kont) :
    KeepAt (K.plug a) ↔ KeepRedex a := by
  constructor
  · rintro ⟨K', r, he, hr⟩
    obtain ⟨r', hr'⟩ := head_of_keepRedex (ℍ := ℍ) hr μ
    obtain ⟨rfl, -⟩ := plug_decomp hh K' K hr' he.symm
    exact hr
  · intro h; exact ⟨K, a, rfl, h⟩

theorem reraiseAt_iff {μ μ' : Heap} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a') (K : Kont) :
    ReraiseAt (K.plug a) ↔ ReraiseRedex a := by
  constructor
  · rintro ⟨K', r, he, hr⟩
    obtain ⟨r', hr'⟩ := head_of_reraiseRedex (ℍ := ℍ) hr μ
    obtain ⟨rfl, -⟩ := plug_decomp hh K' K hr' he.symm
    exact hr
  · intro h; exact ⟨K, a, rfl, h⟩

theorem mergeAt_iff {μ μ' : Heap} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a') (K : Kont) :
    MergeAt (K.plug a) ↔ MergeRedex a := by
  constructor
  · rintro ⟨K', r, he, hr⟩
    obtain ⟨r', hr'⟩ := head_of_mergeRedex (ℍ := ℍ) hr μ
    obtain ⟨rfl, -⟩ := plug_decomp hh K' K hr' he.symm
    exact hr
  · intro h; exact ⟨K, a, rfl, h⟩

/-- **A machine step changes the kept errors only as the algebra says** (`kc_head`, through the
step's context, which holds what it held): `[cfin-raise]` at a cancel that kept nothing keeps one
more, `[cancel-raise]` re-raises one, `[cfin-cancel]` at two kept errors keeps the earlier, and no
other step makes or loses one, provided no `[op]` captures a context holding a kept error. -/
theorem kc_step1 (hP0 : ¬ P 0) {μ μ' : Heap} {e e' : Expr} (h : Step1 (ℍ := ℍ) μ e μ' e')
    (hok : e.RaiseOK P) (hμr : HeapRaiseOK P μ) (hnz : e.HndNamesNZ) (hon : OnPath e)
    (hμ : HeapKC μ) (hcap : NoKeptCaptureAt e) :
    OnPath e' ∧ HeapKC μ' ∧
      kc e' + (if ReraiseAt e then 1 else 0) + (if MergeAt e then 1 else 0) =
        kc e + (if KeepAt e then 1 else 0) := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  obtain ⟨hKr, har⟩ := plug_raiseOK_inv K (plain_head hh) hok
  obtain ⟨-, hanz⟩ := plug_hndNZ_inv K (notNameLike_head hh) hnz
  obtain ⟨hKo, hao⟩ := onPath_plug_inv K (plain_head hh) hh.not_isVal hon
  obtain ⟨hon', hμ', hc⟩ := kc_head hP0 hh har hanz hao hμ (hcap K a rfl)
  have har' := (raiseOK_head hP0 hh har hμr).1
  refine ⟨onPath_plug hP0 K hKr har' hKo hon', hμ', ?_⟩
  rw [keepAt_iff hh K, reraiseAt_iff hh K, mergeAt_iff hh K, kc_plug hP0 K hKr har',
    kc_plug hP0 K hKr har]
  omega

end Step

/-! ### Configurations whose captures hold no kept error -/

section Capture

/-- Neither `raise` nor `cfin`: no holder at an application of it. -/
theorem holdAt_of_ne {f : Expr} (h₁ : f ≠ .prim .raise) (h₂ : f ≠ .prim .cfin) (a : Expr) :
    holdAt f a = 0 := by
  cases f with
  | prim p =>
      cases p with
      | raise => exact absurd rfl h₁
      | cfin => exact absurd rfl h₂
      | _ => rfl
  | _ => rfl

/-- **The count through a context at two plain terms**: the context's frames hold the same at
both, a plain term being no literal, pair or `inj` a kept error's shape reads. -/
theorem kc_plug_plain {a b : Expr} (ha : Plain a) (hb : Plain b) :
    ∀ K : Kont, kc (K.plug a) + kc b = kc (K.plug b) + kc a := by
  intro K
  induction K with
  | hole => simp only [Kont.plug]; omega
  | pairL K e ih => simp only [Kont.plug, kc]; omega
  | pairR v K ih => simp only [Kont.plug, kc]; omega
  | letpair K e ih => simp only [Kont.plug, kc]; omega
  | case K e₁ e₂ ih => simp only [Kont.plug, kc]; omega
  | seq K e ih => simp only [Kont.plug, kc]; omega
  | inj₁ K ih => simp only [Kont.plug, kc]; omega
  | inj₂ K ih => simp only [Kont.plug, kc]; omega
  | appR f K ih =>
      have e : holdAt f (K.plug a) = holdAt f (K.plug b) := by
        cases f with
        | prim p =>
            cases p with
            | raise =>
                simp only [holdAt]
                cases h₁ : keptB (K.plug a) <;> cases h₂ : keptB (K.plug b)
                · rfl
                · rw [keptB_plug hb h₂ a] at h₁; cases h₁
                · rw [keptB_plug ha h₁ b] at h₂; cases h₂
                · rfl
            | cfin =>
                simp only [holdAt]
                cases h₁ : keptB (K.plug a) <;> cases h₂ : keptB (K.plug b)
                · rfl
                · rw [keptB_plug hb h₂ a] at h₁; cases h₁
                · rw [keptB_plug ha h₁ b] at h₂; cases h₂
                · rfl
            | _ => rfl
        | _ => rfl
      simp only [Kont.plug, kc, e]; omega
  | appL K v ih =>
      have e₁ : holdAt (K.plug a) v.1 = 0 :=
        holdAt_of_ne (plug_ne_prim_of_plain ha) (plug_ne_prim_of_plain ha) _
      have e₂ : holdAt (K.plug b) v.1 = 0 :=
        holdAt_of_ne (plug_ne_prim_of_plain hb) (plug_ne_prim_of_plain hb) _
      simp only [Kont.plug, kc, e₁, e₂]; omega

/-- **A configuration holding no kept error captures none.** -/
theorem noKeptCaptureAt_of_kc {e : Expr} (h : kc e = 0) : NoKeptCaptureAt e := by
  intro K a he n i qs hr hs v K' ha _
  subst he
  have h₁ := kc_plug_plain (a := a) (b := .var 0) (by rw [ha]; trivial) trivial K
  have hk : kc a = 0 := by simp only [kc] at h₁; omega
  rw [ha, kc_hndE] at hk
  have h₂ := kc_plug_plain (a := performE (.val (opPayload n i v))) (b := .var 0) trivial trivial K'
  simp only [kc] at h₂
  omega

/-- `perform` applied to something, somewhere in a term. -/
def hasPerformB : Expr → Bool
  | .app f a => (match f with | .prim .perform => true | _ => false) || hasPerformB f ||
      hasPerformB a
  | .pair a b | .seq a b | .letpair a b => hasPerformB a || hasPerformB b
  | .case a b c => hasPerformB a || hasPerformB b || hasPerformB c
  | .inj₁ a | .inj₂ a | .lam a => hasPerformB a
  | .var _ | .unit | .loc _ | .prim _ => false

theorem hasPerformB_plug {x : Expr} (hx : hasPerformB x = true) :
    ∀ K : Kont, hasPerformB (K.plug x) = true := by
  intro K
  induction K with
  | hole => exact hx
  | pairL K e ih | letpair K e ih | seq K e ih => simp [Kont.plug, hasPerformB, ih]
  | pairR v K ih => simp [Kont.plug, hasPerformB, ih]
  | case K e₁ e₂ ih => simp [Kont.plug, hasPerformB, ih]
  | inj₁ K ih | inj₂ K ih => simp [Kont.plug, hasPerformB, ih]
  | appR f K ih => simp [Kont.plug, hasPerformB, ih]
  | appL K v ih => simp [Kont.plug, hasPerformB, ih]

/-- **A configuration with no `perform` captures nothing.** -/
theorem noKeptCaptureAt_of_noPerform {e : Expr} (h : hasPerformB e = false) : NoKeptCaptureAt e := by
  intro K a he n i qs hr hs v K' ha _
  have h₁ : hasPerformB (performE (.val (opPayload n i v))) = true := by
    simp [performE, hasPerformB]
  have hX := hasPerformB_plug h₁ K'
  have ha' : hasPerformB a = true := by
    rw [ha]; simp [hndE, hasPerformB, hX]
  have h₂ := hasPerformB_plug ha' K
  rw [← he, h] at h₂
  cases h₂

end Capture

end Targets

end
