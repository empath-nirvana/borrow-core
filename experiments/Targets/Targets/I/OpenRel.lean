import Targets.B.Guarantees
import Targets.Instance.Typing

/-!
# The interaction — the relation at the open types (RESTRUCTURE §4.2; TIER1-PLAN §2)

**Law 1** (synthesis §10 item 1): the row `∀` is the intersection of its instances.

* `ovalW M b A i η δ v`: the relation at an open value type, in a borrow world.  At a `∀`-free type
  it is `M.val` at the type's instance under `η`; at `U(∀ρ:k. C)` and `!U(∀ρ:k. C)` it relates a
  value when the value is related at `U C` (`!U C`) at every row admissible at `k` put for `ρ`, on
  the same value (`ovalW_allR`, `ovalW_bang_allR`).  Rows are erased, so the value is the same at
  every instance.  `ovalW` reads `M.val` everywhere else, so it is not a new relation family.
* `ojdgW`: its computation counterpart, at a judgement: `M.comp` at a computation type's instance,
  `return e` at a value type's, and at a prenex row `∀` every admissible instance.
* `FLOpen M J`: FL at the open judgements of `J`, contexts and judgements read through `ovalW` and
  `ojdgW`.  `fl_of_flOpen`: it gives B1 at `J`'s reading, whose judgements are `∀`-free.
* `flOpen_core_tier1Open`: at today's kernel over the open types, `FLOpen` is `fundamentalC` at
  every instance.

`FLOpen B.coreB J₁` is not proved here: `J₁` is not built (TIER1-PLAN §2's outcome,
`Targets/Instance/J1Checks.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx)
open Targets.Inst (OVTy OCTy OJdg OurTyping octxDen octxRFree tier1Open rowCtx_models_nil)

/-- A row is an admissible instance of the constraint `k`. -/
def AdmRow (k : RowCon) (r : Row) : Prop := k.cls.Admits r ∧ ∀ o ∈ r, k.adm o

/-- The relation at `U C` (`bang = false`) or `!U C` (`bang = true`): through `C`'s prenex row
`∀`s, every admissible instance; then `M.val` at the instance. -/
def ovalThunk (M : B.BWorld) (b bang : Bool) : OCTy → Idx M.Stk → RowEnv → LSub → Val → WProp
  | .allR ρ k C, i, η, δ, v => fun σ => ∀ r, AdmRow k r →
      ovalThunk M b bang C i (Function.update η ρ r) δ v σ
  | C, i, η, δ, v => M.val b (if bang then .bang (.thunk (C.den η)) else .thunk (C.den η)) i δ v

/-- **The relation at an open value type** (Law 1): `M.val` at the instance under `η`, except at a
prenex `U(∀ρ:k. C)` or `!U(∀ρ:k. C)`, related at every admissible instance, on the same value. -/
def ovalW (M : B.BWorld) (b : Bool) : OVTy → Idx M.Stk → RowEnv → LSub → Val → WProp
  | .thunk C => ovalThunk M b false C
  | .bang (.thunk C) => ovalThunk M b true C
  | A => fun i η δ v => M.val b (A.den η) i δ v

/-- The relation at an open computation type: through its prenex row `∀`s, every admissible
instance; then `M.comp` at the instance. -/
def ocompW (M : B.BWorld) : OCTy → Idx M.Stk → RowEnv → LSub → Expr → WProp
  | .allR ρ k C, i, η, δ, e => fun σ => ∀ r, AdmRow k r →
      ocompW M C i (Function.update η ρ r) δ e σ
  | C, i, η, δ, e => M.comp (C.den η) i δ e

/-- `return e` at `U C` or `!U C`, through `C`'s prenex row `∀`s. -/
def oretThunk (M : B.BWorld) (bang : Bool) : OCTy → Idx M.Stk → RowEnv → LSub → Expr → WProp
  | .allR ρ k C, i, η, δ, e => fun σ => ∀ r, AdmRow k r →
      oretThunk M bang C i (Function.update η ρ r) δ e σ
  | C, i, η, δ, e =>
      M.comp (.ret (if bang then .bang (.thunk (C.den η)) else .thunk (C.den η))) i δ e

/-- The computation counterpart at an open judgement. -/
def ojdgW (M : B.BWorld) : OJdg → Idx M.Stk → RowEnv → LSub → Expr → WProp
  | .comp C => ocompW M C
  | .val (.thunk C) => oretThunk M false C
  | .val (.bang (.thunk C)) => oretThunk M true C
  | .val A => fun i η δ e => M.comp (.ret (A.den η)) i δ e

/-- `⊛_{x ∈ dom(Γ)} ovalW⟦Γ(x)⟧`. -/
def ogSepW (M : B.BWorld) (i : Idx M.Stk) (η : RowEnv) (δ : LSub) :
    Ctx OVTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then ovalW M true s.ty i η δ v ⋆ ogSepW M i η δ Γ γ else ogSepW M i η δ Γ γ

/-- The context relation at open types. -/
def ogDenW (M : B.BWorld) (i : Idx M.Stk) (η : RowEnv) (δ : LSub) (Γ : Ctx OVTy) (γ : List Val) :
    WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ ogSepW M i η δ Γ γ

/-- **FL at the open judgements of `J`**, beside done: every derivation, at every admissible
instance, is in the relation, contexts and judgements read through `ovalW` and `ojdgW`. -/
def FLOpen (M : B.BWorld) (J : OurTyping orowRF) : Prop :=
  ∀ Θ Δ Γ e j, J.der Θ Δ Γ e j → ∀ η, Θ.Models η → ∀ δ γ (i : Idx M.Stk) ρ, Δ.Models δ →
    ogDenW M i η δ Γ γ ρ → ojdgW M j i η δ (substAll γ e) ρ

/-! ### Law 1, at the relation -/

/-- **`U(∀ρ:k. C)` is the intersection of its instances.** -/
theorem ovalW_allR (M : B.BWorld) (b : Bool) (ρ : RVar) (k : RowCon) (C : OCTy) (i : Idx M.Stk)
    (η : RowEnv) (δ : LSub) (v : Val) (σ : WRes) :
    ovalW M b (.thunk (.allR ρ k C)) i η δ v σ ↔
      ∀ r, AdmRow k r → ovalW M b (.thunk C) i (Function.update η ρ r) δ v σ := Iff.rfl

/-- **`!U(∀ρ:k. C)` is the intersection of its instances.** -/
theorem ovalW_bang_allR (M : B.BWorld) (b : Bool) (ρ : RVar) (k : RowCon) (C : OCTy)
    (i : Idx M.Stk) (η : RowEnv) (δ : LSub) (v : Val) (σ : WRes) :
    ovalW M b (.bang (.thunk (.allR ρ k C))) i η δ v σ ↔
      ∀ r, AdmRow k r → ovalW M b (.bang (.thunk C)) i (Function.update η ρ r) δ v σ := Iff.rfl

/-! ### At `∀`-free types, the borrow world's relation -/

theorem ovalThunk_rFree (M : B.BWorld) (b bang : Bool) {C : OCTy} (hC : C.RFree) (i : Idx M.Stk)
    (η : RowEnv) (δ : LSub) (v : Val) :
    ovalThunk M b bang C i η δ v =
      M.val b (if bang then .bang (.thunk (C.den η)) else .thunk (C.den η)) i δ v := by
  cases C <;> first | rfl | exact absurd hC id

theorem ocompW_rFree (M : B.BWorld) {C : OCTy} (hC : C.RFree) (i : Idx M.Stk) (η : RowEnv)
    (δ : LSub) (e : Expr) : ocompW M C i η δ e = M.comp (C.den η) i δ e := by
  cases C <;> first | rfl | exact absurd hC id

theorem oretThunk_rFree (M : B.BWorld) (bang : Bool) {C : OCTy} (hC : C.RFree) (i : Idx M.Stk)
    (η : RowEnv) (δ : LSub) (e : Expr) :
    oretThunk M bang C i η δ e =
      M.comp (.ret (if bang then .bang (.thunk (C.den η)) else .thunk (C.den η))) i δ e := by
  cases C <;> first | rfl | exact absurd hC id

/-- At a `∀`-free type, `ovalW` is `M.val` at the instance. -/
theorem ovalW_rFree (M : B.BWorld) (b : Bool) {A : OVTy} (hA : A.RFree) (i : Idx M.Stk)
    (η : RowEnv) (δ : LSub) (v : Val) : ovalW M b A i η δ v = M.val b (A.den η) i δ v := by
  match A, hA with
  | .thunk C, hA => exact ovalThunk_rFree M b false hA i η δ v
  | .bang (.thunk C), hA => exact ovalThunk_rFree M b true hA i η δ v
  | .unit, _ | .tensor _ _, _ | .zero, _ | .sum _ _, _ | .ref _, _ | .imm _ _, _ | .mut _ _, _
  | .box _ _, _ | .unk, _ | .tvar _, _ | .mu _, _ | .int _, _ | .fam _, _ | .opq _, _ => rfl
  | .bang .unit, _ | .bang (.tensor _ _), _ | .bang .zero, _ | .bang (.sum _ _), _
  | .bang (.ref _), _ | .bang (.imm _ _), _ | .bang (.mut _ _), _ | .bang (.box _ _), _
  | .bang (.bang _), _ | .bang .unk, _ | .bang (.tvar _), _ | .bang (.mu _), _
  | .bang (.int _), _ | .bang (.fam _), _ | .bang (.opq _), _ => rfl

/-- At a `∀`-free judgement, `ojdgW` is `SemW₀`'s reading of the instance. -/
theorem ojdgW_rFree (M : B.BWorld) {j : OJdg} (hj : j.RFree) (i : Idx M.Stk) (η : RowEnv)
    (δ : LSub) (e : Expr) :
    ojdgW M j i η δ e = match j.den η with
      | .comp C => M.comp C i δ e
      | .val A => M.comp (.ret A) i δ e := by
  match j, hj with
  | .comp C, hj => exact ocompW_rFree M hj i η δ e
  | .val (.thunk C), hj => exact oretThunk_rFree M false hj i η δ e
  | .val (.bang (.thunk C)), hj => exact oretThunk_rFree M true hj i η δ e
  | .val .unit, _ | .val (.tensor _ _), _ | .val .zero, _ | .val (.sum _ _), _ | .val (.ref _), _
  | .val (.imm _ _), _ | .val (.mut _ _), _ | .val (.box _ _), _ | .val .unk, _
  | .val (.tvar _), _ | .val (.mu _), _ | .val (.int _), _ | .val (.fam _), _
  | .val (.opq _), _ => rfl
  | .val (.bang .unit), _ | .val (.bang (.tensor _ _)), _ | .val (.bang .zero), _
  | .val (.bang (.sum _ _)), _ | .val (.bang (.ref _)), _ | .val (.bang (.imm _ _)), _
  | .val (.bang (.mut _ _)), _ | .val (.bang (.box _ _)), _ | .val (.bang (.bang _)), _
  | .val (.bang .unk), _ | .val (.bang (.tvar _)), _ | .val (.bang (.mu _)), _
  | .val (.bang (.int _)), _ | .val (.bang (.fam _)), _ | .val (.bang (.opq _)), _ => rfl

theorem ogSepW_rFree (M : B.BWorld) (i : Idx M.Stk) (η : RowEnv) (δ : LSub) :
    ∀ (Γ : Ctx OVTy) (γ : List Val), octxRFree Γ →
      ogSepW M i η δ Γ γ = gSepW M i δ (octxDen η Γ) γ
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | s :: Γ, v :: γ, hΓ => by
      have hs : s.ty.RFree := hΓ s (List.mem_cons_self ..)
      have ih := ogSepW_rFree M i η δ Γ γ (fun s' h => hΓ s' (List.mem_cons_of_mem _ h))
      simp only [ogSepW, octxDen, List.map_cons, gSepW, ovalW_rFree M true hs]
      rw [ih]
      rfl

theorem liveWithin_octxDen (η : RowEnv) :
    ∀ (Γ : Ctx OVTy) (γ : List Val), Ctx.LiveWithin (octxDen η Γ) γ ↔ Ctx.LiveWithin Γ γ
  | [], _ => by simp [octxDen]
  | s :: Γ, [] => by
      have := liveWithin_octxDen η Γ []
      simp only [octxDen, List.map_cons, Ctx.LiveWithin] at this ⊢
      rw [this]
  | s :: Γ, _ :: γ => by
      have := liveWithin_octxDen η Γ γ
      simp only [octxDen, List.map_cons, Ctx.LiveWithin] at this ⊢
      exact this

/-- At a `∀`-free context, `ogDenW` is `gDenW` at the instance. -/
theorem ogDenW_rFree (M : B.BWorld) (i : Idx M.Stk) (η : RowEnv) (δ : LSub) {Γ : Ctx OVTy}
    (hΓ : octxRFree Γ) (γ : List Val) : ogDenW M i η δ Γ γ = gDenW M i δ (octxDen η Γ) γ := by
  simp only [ogDenW, gDenW, ogSepW_rFree M i η δ Γ γ hΓ, liveWithin_octxDen η Γ γ]

/-- **`FLOpen` gives B1 at `J`'s reading**: the reading's judgements are `∀`-free and denote the
instance, where `ovalW` and `ojdgW` are the borrow world's relation. -/
theorem fl_of_flOpen {M : B.BWorld} {J : OurTyping orowRF} (h : FLOpen M J) : FL M J.read := by
  intro Θ Δ Γ e j hJ η hη
  obtain ⟨Γ', j', hΓ', hj', hd, hΓe, hje⟩ := hJ η hη
  rw [← hΓe η, ← hje η]
  have hF := h [] Δ Γ' e j' hd η (rowCtx_models_nil η)
  have key : ∀ δ γ (i : Idx M.Stk) ρ, Δ.Models δ → gDenW M i δ (octxDen η Γ') γ ρ →
      ojdgW M j' i η δ (substAll γ e) ρ := fun δ γ i ρ hδ hg =>
    hF δ γ i ρ hδ (by rw [ogDenW_rFree M i η δ hΓ' γ]; exact hg)
  cases j' with
  | comp C =>
      intro δ γ i ρ hδ hg
      have := key δ γ i ρ hδ hg
      rw [ojdgW_rFree M hj' i η δ] at this
      exact this
  | val A =>
      intro δ γ i ρ hδ hg
      have := key δ γ i ρ hδ hg
      rw [ojdgW_rFree M hj' i η δ] at this
      exact this

/-- **`FLOpen` at today's kernel over the open types**: its judgements are `∀`-free, and FL there
is `fundamentalC` at every instance. -/
theorem flOpen_core_tier1Open : FLOpen (B.coreB (ℍ := ℍ)) tier1Open := by
  intro Θ Δ Γ e j hd η hη δ γ i ρ hδ hg
  obtain ⟨hΓ, hj, hder⟩ := hd
  have hsem : SemW₀ (B.coreB (ℍ := ℍ)) Δ (octxDen η Γ) e (j.den η) :=
    semW₀_core.mpr (fundamentalC (hder η hη).toCDerives)
  rw [ogDenW_rFree _ i η δ hΓ γ] at hg
  rw [ojdgW_rFree _ hj i η δ]
  cases j with
  | comp C => exact hsem δ γ i ρ hδ hg
  | val A => exact hsem δ γ i ρ hδ hg

end Targets.I

end
