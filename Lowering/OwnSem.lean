import Lowering.Own
import Lowering.NoRelaxed
import Lowering.Obligations
import Core.PinFundamental
import Core.EffMachine

/-!
# Lowering — `own` is in the relation  `[spec §54]`

**`own`'s output is in `SemC` at the source's context and type** (`own_lowerSem`,
`own_lowerSem_pin`). The proof follows the Fundamental Property's: by induction on the typed
derivation, each node by its rule's compatibility lemma (`Core/Compat.lean`), at `own`'s parts in
place of the erasure's. What `own` adds to a node is pure steps in front of it:

- a drop `forget x; e` runs `forget x` (a β-step to `()`) and `(); e` to `e` (`sem_drop`);
- a copy `let (x₁, x₂) = copy x in N'` runs `copy x` to `(x, x)` and the `let` to `N'` at the
  substitution extended by `x` twice; there `N'`, the node with its parts renamed to read the
  copies, is the node at the original substitution (`psub_ren`), so the copies change nothing the
  relation sees (`sem_copies`);
- the `()` a dead binder receives is consumed by `(); …` (`thunkF_seq_compatC`,
  `allI_seq_compatC`, `bangThunkF_seq_compatC`): the relation forces those thunks at `()`;
- `absurdL V` is `absurd` at `V : 0` with other arms (`absurdL_compatC`).

A node `own` leaves as its erasure is in the relation by the Fundamental Property, through the
oracle the induction is given: `fundamentalC` for a tied derivation, `fundamentalC_pin` under
`PinLaw`. The drops and copies are read from the derivation's facts: a slot `own` holds live is
live in the node's context (`LiveIn`), so its value is in the substitution; the parts' masks hold
only slots live in their parts (`SplitMasks`).
-/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Lowering
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Check Frontend.Check
open BoCa.BoLo (Heap Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Live slots -/

/-- The slots `own` holds live are live in the context. -/
def LiveIn (L : List Bool) (Γ : Ctx VTy) : Prop := ∀ k, lv L k = true → liveAt Γ k = true

theorem LiveIn.nil (Γ : Ctx VTy) : LiveIn [] Γ := fun k h => by simp [lv] at h

theorem LiveIn.cons {L : List Bool} {Γ : Ctx VTy} (h : LiveIn L Γ) (A : VTy) (b : Bool) :
    LiveIn (false :: L) (⟨A, b⟩ :: Γ) := by
  intro k hk
  cases k with
  | zero => simp [lv] at hk
  | succ k => simpa [lv, liveAt] using h k (by simpa [lv] using hk)

theorem LiveIn.live {L : List Bool} {Γ : Ctx VTy} (h : LiveIn L Γ) (A : VTy) :
    LiveIn (true :: L) (⟨A, true⟩ :: Γ) := by
  intro k hk
  cases k with
  | zero => simp [liveAt]
  | succ k => simpa [lv, liveAt] using h k (by simpa [lv] using hk)

theorem lv_part {L : List Bool} {u : Nat → Bool} {k : Nat} (h : lv (part L u) k = true) :
    lv L k = true ∧ u k = true := by
  simp only [lv, part] at h
  by_cases hk : k < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk] at h
    simpa [lv, List.getD_eq_getElem?_getD] using h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hk)] at h
    simp at h

theorem SplitMasks.live_of_mask₁ : ∀ {Γ₁ Γ₂ : Ctx VTy} {u₁ u₂ : List Bool},
    SplitMasks Γ₁ Γ₂ u₁ u₂ → ∀ k, u₁.getD k false = true → liveAt Γ₁ k = true
  | _, _, _, _, .nil, k, h => by simp at h
  | _, _, _, _, .cons h₁ _ _ h, 0, ha => by simpa [liveAt] using h₁ (by simpa using ha)
  | _, _, _, _, .cons _ _ _ h, k + 1, ha => by
      simpa [liveAt] using SplitMasks.live_of_mask₁ h k (by simpa using ha)

theorem SplitMasks.live_of_mask₂ : ∀ {Γ₁ Γ₂ : Ctx VTy} {u₁ u₂ : List Bool},
    SplitMasks Γ₁ Γ₂ u₁ u₂ → ∀ k, u₂.getD k false = true → liveAt Γ₂ k = true
  | _, _, _, _, .nil, k, h => by simp at h
  | _, _, _, _, .cons _ h₂ _ _, 0, hb => by simpa [liveAt] using h₂ (by simpa using hb)
  | _, _, _, _, .cons _ _ _ h, k + 1, hb => by
      simpa [liveAt] using SplitMasks.live_of_mask₂ h k (by simpa using hb)

/-- A part receives, of the node's live slots, those its mask holds: live in its context. -/
theorem LiveIn.part₁ {L : List Bool} {Γ₁ Γ₂ : Ctx VTy} {m : Masks} (hm : m.Rel Γ₁ Γ₂) :
    LiveIn (part L (mk m.u₁)) Γ₁ := fun k hk =>
  SplitMasks.live_of_mask₁ hm k (lv_part hk).2

theorem LiveIn.part₂ {L : List Bool} {Γ₁ Γ₂ : Ctx VTy} {m : Masks} (hm : m.Rel Γ₁ Γ₂) :
    LiveIn (part L (mk m.u₂)) Γ₂ := fun k hk =>
  SplitMasks.live_of_mask₂ hm k (lv_part hk).2

/-- A live slot holds a value of the substitution. -/
theorem val_of_live : ∀ {Γ : Ctx VTy} {γ : List Val} {k : Nat}, Ctx.LiveWithin Γ γ →
    liveAt Γ k = true → ∃ v, γ[k]? = some v
  | [], _, k, _, h => by simp [liveAt] at h
  | s :: Γ, [], 0, hw, h => by simp [liveAt] at h; exact absurd h hw.1
  | s :: Γ, [], k + 1, hw, h => by
      obtain ⟨v, hv⟩ := val_of_live (Γ := Γ) (γ := []) (k := k) hw.2 (by simpa [liveAt] using h)
      simp at hv
  | s :: Γ, v :: γ, 0, _, _ => ⟨v, rfl⟩
  | s :: Γ, v :: γ, k + 1, hw, h => by
      simpa using val_of_live (Γ := Γ) (γ := γ) (k := k) hw (by simpa [liveAt] using h)

theorem LiveIn.val {L : List Bool} {Γ : Ctx VTy} (hL : LiveIn L Γ) {γ : List Val}
    (hw : Ctx.LiveWithin Γ γ) {k : Nat} (hk : lv L k = true) : ∃ v, γ[k]? = some v :=
  val_of_live hw (hL k hk)

theorem lv_of_mem_liveIdx {L : List Bool} {k : Nat} (h : k ∈ liveIdx L) : lv L k = true := by
  simp only [liveIdx, List.mem_filter] at h
  exact h.2

/-! ### Drops -/

private theorem substAll_var' {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v) :
    substAll γ (.var i) = .val v := by
  show Expr.psub 0 γ (.var i) = _
  simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]

theorem substAll_forget (γ : List Val) : substAll γ forget = forget := rfl

theorem substAll_copy (γ : List Val) : substAll γ copy = copy := rfl

/-- **A drop is pure steps**: `forget x; e` runs to `e`. -/
theorem sem_drop {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} {k : Nat}
    (hk : liveAt Γ k = true) (h : SemC (ℍ := ℍ) Δ Γ e C) : SemC (ℍ := ℍ) Δ Γ (dropE k e) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨v, hv⟩ := val_of_live (gDenC_iff.mp hg).1 hk
  have hs : substAll γ (dropE k e) = .seq (.app forget (.val v)) (substAll γ e) := by
    show Expr.psub 0 γ (.seq (.app forget (.var k)) e) = _
    simp only [Expr.psub]
    rw [show Expr.psub 0 γ forget = forget from rfl]
    exact congrArg₂ _ (congrArg _ (substAll_var' hv)) rfl
  rw [hs]
  refine cC_step C (fun μ => (BoCa.BoLo.Step1N.head (Head.beta μ unit' v) rfl).plug
    (Kont.seq .hole (substAll γ e))) ls δ ρ ?_
  refine cC_head C (fun μ => Head.seq μ _) rfl ls δ ρ ?_
  exact h δ γ ls ρ hδ hg

theorem sem_drops {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} :
    ∀ {ks : List Nat}, (∀ k ∈ ks, liveAt Γ k = true) → SemC (ℍ := ℍ) Δ Γ e C →
      SemC (ℍ := ℍ) Δ Γ (dropsE ks e) C
  | [], _, h => h
  | k :: ks, hks, h => sem_drop (hks k (by simp)) (sem_drops (fun j hj => hks j (by simp [hj])) h)

/-- **A leaf's drops** keep it in the relation. -/
theorem sem_leaf {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} {L : List Bool}
    (hL : LiveIn L Γ) (keep : Option Nat) (h : SemC (ℍ := ℍ) Δ Γ e C) :
    SemC (ℍ := ℍ) Δ Γ (leafE L keep e) C :=
  sem_drops (fun k hk => hL k (lv_of_mem_liveIdx (List.mem_filter.mp hk).1)) h

/-! ### Copies -/

theorem renOK_cpL {γ : List Val} {k : Nat} {v : Val} (hv : γ[k]? = some v) :
    RenOK (cpL k) (v :: v :: γ) γ := by
  intro i
  by_cases hi : i = k
  · subst hi
    refine ⟨by simp [cpL, hv], fun hl => ?_⟩
    rw [List.getElem?_eq_none hl] at hv; simp at hv
  · simp only [cpL, if_neg hi]
    exact ⟨by simp, fun _ => by simp⟩

theorem renOK_cpR {γ : List Val} {k : Nat} {v : Val} (hv : γ[k]? = some v) :
    RenOK (cpR k) (v :: v :: γ) γ := by
  intro i
  by_cases hi : i = k
  · subst hi
    refine ⟨by simp [cpR, hv], fun hl => ?_⟩
    rw [List.getElem?_eq_none hl] at hv; simp at hv
  · simp only [cpR, if_neg hi]
    exact ⟨by simp, fun _ => by simp⟩

/-- `copy x` then `let`: the body at the substitution extended by `x` twice. -/
theorem cC_copy_let {C : CTy} {ls : List SRec} {δ : LSub} {ρ : WRes} {γ : List Val} {k : Nat}
    {v : Val} (hv : γ[k]? = some v) {R : Expr}
    (h : cC (ℍ := ℍ) C ls δ (substAll (v :: v :: γ) R) ρ) :
    cC (ℍ := ℍ) C ls δ (substAll γ (.letpair (.app copy (.var k)) R)) ρ := by
  have hs : substAll γ (.letpair (.app copy (.var k)) R) =
      .letpair (.app copy (.val v)) (Expr.psub 2 γ R) := by
    show Expr.psub 0 γ (.letpair (.app copy (.var k)) R) = _
    simp only [Expr.psub]
    rw [show Expr.psub 0 γ copy = copy from rfl]
    exact congrArg₂ _ (congrArg _ (substAll_var' hv)) rfl
  rw [hs]
  refine cC_step C (fun μ => (BoCa.BoLo.Step1N.head (Head.beta μ (.pair v0 v0) v) rfl).plug
    (Kont.letpair .hole (Expr.psub 2 γ R))) ls δ ρ ?_
  refine cC_head C (fun μ => Head.letpair μ v v _) rfl ls δ ρ ?_
  have he : substAll (v :: v :: γ) R =
      Expr.subst 0 v (Expr.subst 0 (v.shift 1 0) (Expr.psub 2 γ R)) := by
    show Expr.psub 0 (v :: v :: γ) R = _
    rw [Expr.psub_cons₂ 0 v v γ R, Val.shift_zero]
  rw [he] at h
  exact h

/-- **The copies are pure steps**: the copies of the slots `ks` in front of a node whose parts,
renamed to read their copies, give the node at the original substitution. -/
theorem sem_copies {C : CTy} {ls : List SRec} {δ : LSub} {ρ : WRes} :
    ∀ (ks : List Nat) (off : Nat) (F : Node) (γ : List Val),
      (∀ k ∈ ks, ∃ v, γ[k + off]? = some v) →
      (∀ ρ₁ ρ₂ γ', RenOK ρ₁ γ' γ → RenOK ρ₂ γ' γ → cC (ℍ := ℍ) C ls δ (substAll γ' (F ρ₁ ρ₂)) ρ) →
      cC (ℍ := ℍ) C ls δ (substAll γ (copiesE off ks F)) ρ
  | [], _, F, γ, _, hF => hF id id γ (RenOK.id γ) (RenOK.id γ)
  | k :: ks, off, F, γ, hks, hF => by
      obtain ⟨v, hv⟩ := hks k (by simp)
      refine cC_copy_let hv ?_
      refine sem_copies ks (off + 2) _ (v :: v :: γ) (fun j hj => ?_) ?_
      · obtain ⟨w, hw⟩ := hks j (by simp [hj])
        exact ⟨w, by rw [show j + (off + 2) = (j + off) + 2 by omega]; simpa using hw⟩
      · intro ρ₁ ρ₂ γ' h₁ h₂
        exact hF _ _ γ' (h₁.comp (renOK_cpL hv)) (h₂.comp (renOK_cpR hv))

/-- A node whose renamed parts give the node: the node is `F id id`, and a renaming of its parts
that keeps the substitution keeps the substituted node. -/
def NodeInv (F : Node) : Prop :=
  ∀ ρ₁ ρ₂ γ' γ, RenOK ρ₁ γ' γ → RenOK ρ₂ γ' γ → substAll γ' (F ρ₁ ρ₂) = substAll γ (F id id)

/-- **A node at a split keeps its relation with its drops and copies made explicit.** -/
theorem sem_split {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} {L : List Bool} {u₁ u₂ : Nat → Bool}
    {F : Node} (hL : LiveIn L Γ) (hF : NodeInv F) (h : SemC (ℍ := ℍ) Δ Γ (F id id) C) :
    SemC (ℍ := ℍ) Δ Γ (splitE L u₁ u₂ F) C := by
  refine sem_drops (fun k hk => hL k (lv_of_mem_liveIdx (List.mem_filter.mp hk).1)) ?_
  intro δ γ ls ρ hδ hg
  refine sem_copies _ 0 F γ (fun k hk => ?_) (fun ρ₁ ρ₂ γ' h₁ h₂ => ?_)
  · exact hL.val (gDenC_iff.mp hg).1 (lv_of_mem_liveIdx (List.mem_filter.mp hk).1)
  · rw [hF ρ₁ ρ₂ γ' γ h₁ h₂]
    exact h δ γ ls ρ hδ hg

theorem sem_split_eq {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} {L : List Bool} {u₁ u₂ : Nat → Bool}
    {F : Node} {N : Expr} (hL : LiveIn L Γ) (hF : NodeInv F) (he : F id id = N)
    (h : SemC (ℍ := ℍ) Δ Γ N C) : SemC (ℍ := ℍ) Δ Γ (splitE L u₁ u₂ F) C :=
  sem_split hL hF (he ▸ h)

/-- A node's template commutes with the substitution, its parts' renamings keeping it. -/
syntax "nodeinv" : tactic
macro_rules
  | `(tactic| nodeinv) => `(tactic| (intro ρ₁ ρ₂ γ' γ h₁ h₂; simp only [substAll, Expr.psub,
      psub_ren0 h₁, psub_ren0 h₂, psub_ren1 h₂, psub_ren2 h₂, liftR_id, ren_id, absurdL,
      BoLo.stuckE, Expr.val, Val.unit]))

/-! ### The binders the kernel types dead -/

private theorem substAll_cons' (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

/-- `thunk M : U (F A)` written `λu. (u; M)`: forced at `()`, the `()` consumed. -/
theorem thunkF_seq_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (h : SemC (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) :
    SemV (ℍ := ℍ) Δ Γ (.lam (.seq (.var 0) M)) (.thunk (.ret A)) := by
  intro δ γ ls ρ hδ hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ (.seq (.var 0) M)))) _ ρ
  refine wpTS_val _ _ _ _ ?_
  intro ls' hext
  refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γ (.seq (.var 0) M)) Val.unit) rfl
    ls' δ ρ ?_
  show cC (.ret A) ls' δ (.seq (.val .unit) ((Expr.psub 1 γ M).subst 0 Val.unit)) ρ
  refine cC_head (.ret A) (fun μ => Head.seq μ _) rfl ls' δ ρ ?_
  rw [← substAll_cons']
  exact h δ (Val.unit :: γ) ls' ρ hδ (gDenC_dead_cons _ _ (gDenC_local hext hg))

/-- `thunk M : !U (F A)` over `!Γ`, written `λu. (u; M)`. -/
theorem bangThunkF_seq_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (hp : Persistent Γ) (h : SemC (ℍ := ℍ) Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) :
    SemV (ℍ := ℍ) Δ Γ (.lam (.seq (.var 0) M)) (.bang (.thunk (.ret A))) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨-, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ (.seq (.var 0) M)))) _ ρ
  refine wpTS_val _ _ _ _ ⟨gSepC_persistent hp hgs, ?_⟩
  intro ls' hext
  refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γ (.seq (.var 0) M)) Val.unit) rfl
    ls' δ ρ ?_
  show cC (.ret A) ls' δ (.seq (.val .unit) ((Expr.psub 1 γ M).subst 0 Val.unit)) ρ
  refine cC_head (.ret A) (fun μ => Head.seq μ _) rfl ls' δ ρ ?_
  rw [← substAll_cons']
  exact h δ (Val.unit :: γ) ls' ρ hδ (gDenC_dead_cons _ _ (gDenC_local hext hg))

/-- `Λ. M` written `λu. (u; M)`: instantiated at `()`, the `()` consumed. -/
theorem allI_seq_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {M : Expr}
    {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : SemC (ℍ := ℍ) (Δ.extend x b) (⟨.unit, false⟩ :: Γ) M C) :
    SemC (ℍ := ℍ) Δ Γ (.lam (.seq (.var 0) M)) (.all x b C) := by
  intro δ γ ls ρ hδ hg α ρ₁ ρ₂ hpure hcomp
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  have hδ' : (Δ.extend x b).Models (δ.extend x α) := by
    intro y u hy
    rw [LifeCtx.find?_extend] at hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨α, β, find?_extend_self δ x α,
        by rw [interp_extend_of_not_mentions hbx]; exact hβ, hlt⟩
    · rw [if_neg hxy] at hy
      obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
      exact ⟨m, k, by rw [find?_extend_ne δ α hxy]; exact hm,
        by rw [interp_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩
  show cC C ls (δ.extend x α) (.app (.val (.lam (Expr.psub 1 γ (.seq (.var 0) M)))) (.val .unit)) ρ
  refine cC_head C (fun μ => Head.beta μ (Expr.psub 1 γ (.seq (.var 0) M)) Val.unit) rfl ls
    (δ.extend x α) ρ ?_
  show cC C ls (δ.extend x α) (.seq (.val .unit) ((Expr.psub 1 γ M).subst 0 Val.unit)) ρ
  refine cC_head C (fun μ => Head.seq μ _) rfl ls (δ.extend x α) ρ ?_
  rw [← substAll_cons']
  refine h (δ.extend x α) (Val.unit :: γ) ls ρ hδ' (gDenC_dead_cons _ _ ?_)
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  refine gDenC_mk hlen ?_
  rw [gSepC_congr (δ₂ := δ) (fun s hs hl => vC_extend_of_not_free (hΓx s hs hl) true ls δ α)]
  exact hgs

/-- `absurdL V : C` for `V : 0`: no arm runs. -/
theorem absurdL_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : SemV (ℍ := ℍ) Δ Γ₁ V .zero) :
    SemC (ℍ := ℍ) Δ Γ (absurdL V) C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine cC_bind C (.case .hole BoLo.stuckE BoLo.stuckE) (substAll γ V) ls δ
    (fun ls' => vC true .zero ls' δ) (fun ls' => gDenC ls' δ Γ₂ γ)
    (fun ls' hls σ h => gDenC_same hls h) ?_ ρ ⟨ρ₁, ρ₂, hc, hV δ γ ls ρ₁ hδ hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, -, hv, -⟩
  exact hv.elim

/-! ### At a judgment -/

theorem semJ_leaf {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {L : List Bool} (hL : LiveIn L Γ)
    (keep : Option Nat) : ∀ {j : Jdg}, SemJ (ℍ := ℍ) Δ Γ e j → SemJ (ℍ := ℍ) Δ Γ (leafE L keep e) j
  | .val _, h => sem_leaf hL keep h
  | .comp _, h => sem_leaf hL keep h

/-- A node `own` leaves as its erasure, or a constant with its context's live slots dropped. -/
theorem own_default {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg} {L : List Bool}
    (he : ownAt L t = if constNode t then leafE L none t.erase else t.erase) (hL : LiveIn L Γ)
    (h : SemJ (ℍ := ℍ) Δ Γ t.erase j) : SemJ (ℍ := ℍ) Δ Γ (ownAt L t) j := by
  rw [he]; split
  · exact semJ_leaf hL none h
  · exact h

/-! ### The induction -/

/-- **`own` is in the relation**, at every derivation of `TDerivesP` whose subderivations are in
the relation at their erasures (`O`: the Fundamental Property, under `PinLaw`). The motive takes
the node's own erasure in the relation, for the nodes `own` leaves as they are. -/
theorem own_semP (O : ∀ {Δ Γ t j}, TDerivesP Δ Γ t j → relaxedFree t = true →
      SemJ (ℍ := ℍ) Δ Γ t.erase j)
    {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg} (h : TDerivesP Δ Γ t j) :
    relaxedFree t = true → SemJ (ℍ := ℍ) Δ Γ t.erase j → ∀ L, LiveIn L Γ →
      SemJ (ℍ := ℍ) Δ Γ (ownAt L t) j := by
  induction h with
  | var h => intro _ _ L hL; exact sem_leaf hL _ (var_compatC h)
  | unitI h => intro _ _ L hL; exact sem_leaf hL _ (unitI_compatC h)
  | tensorI hs hm _ h₁ h₂ ih₁ ih₂ =>
      intro hr _ L hL; simp only [relaxedFree, Bool.and_eq_true] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [ren_id])
        (tensorI_compatC hs (ih₁ hr.1 (O h₁ hr.1) _ (LiveIn.part₁ (L := L) hm)) (ih₂ hr.2 (O h₂ hr.2) _ (LiveIn.part₂ (L := L) hm)))
  | sumI₁ h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact sumI₁_compatC (ih hr (O h hr) L hL)
  | sumI₂ h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact sumI₂_compatC (ih hr (O h hr) L hL)
  | thunkF h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact thunkF_seq_compatC (ih hr (O h hr) _ (hL.cons _ _))
  | thunkV hC h q ih =>
      intro hr _ L hL; simp only [relaxedFree] at hr
      show SemV _ _ (match ownAt L _ with | .lam N => .lam N | _ => _) _
      split
      · next N hN =>
          have := ih hr (O h hr) L hL
          rw [hN] at this
          exact thunkV_compatC hC this
      · have := O h hr
        simp only [SemJ] at this
        rw [q] at this ⊢
        exact thunkV_compatC hC this
  | ret h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ret_compatC (ih hr (O h hr) L hL)
  | bind hs hm _ hM hN ihM ihN =>
      intro hr _ L hL; simp only [relaxedFree, Bool.and_eq_true] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [liftR_id, ren_id]; rfl)
        (bind_compatC hs (ihM hr.1 (O hM hr.1) _ (LiveIn.part₁ (L := L) hm)) (ihN hr.2 (O hN hr.2) _ ((LiveIn.part₂ (L := L) hm).live _)))
  | force h => intro _ _ L hL; exact sem_leaf hL _ (force_compatC h)
  | lam h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact lam_compatC (ih hr (O h hr) _ (hL.live _))
  | app hs hm _ hM hx ih =>
      intro hr _ L hL; simp only [relaxedFree] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [ren_id])
        (app_compatC hs (ih hr (O hM hr) _ (LiveIn.part₁ (L := L) hm)) hx)
  | withI hM hN ihM ihN =>
      intro hr _ L hL; simp only [relaxedFree, Bool.and_eq_true] at hr
      exact withI_compatC (ihM hr.1 (O hM hr.1) _ ((hL.cons _ _).cons _ _)) (ihN hr.2 (O hN hr.2) _ ((hL.cons _ _).cons _ _))
  | proj₁ h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact proj₁_compatC (ih hr (O h hr) L hL)
  | proj₂ h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact proj₂_compatC (ih hr (O h hr) L hL)
  | topI => intro _ _ L hL; exact sem_leaf hL _ topI_compatC
  | unitE hs hm _ hV hM ihV ihM =>
      intro hr _ L hL; simp only [relaxedFree, Bool.and_eq_true] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [ren_id])
        (unitE_compatC hs (ihV hr.1 (O hV hr.1) _ (LiveIn.part₁ (L := L) hm)) (ihM hr.2 (O hM hr.2) _ (LiveIn.part₂ (L := L) hm)))
  | tensorE hs hm _ hV hM ihV ihM =>
      intro hr _ L hL; simp only [relaxedFree, Bool.and_eq_true] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [liftR_id, ren_id])
        (tensorE_compatC hs (ihV hr.1 (O hV hr.1) _ (LiveIn.part₁ (L := L) hm))
          (ihM hr.2 (O hM hr.2) _ (((LiveIn.part₂ (L := L) hm).live _).live _)))
  | sumE hs hm _ hV h₁ h₂ ihV ih₁ ih₂ =>
      intro hr _ L hL; simp only [relaxedFree, Bool.and_eq_true] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [liftR_id, ren_id])
        (sumE_compatC hs (ihV hr.1.1 (O hV hr.1.1) _ (LiveIn.part₁ (L := L) hm))
          (ih₁ hr.1.2 (O h₁ hr.1.2) _ ((LiveIn.part₂ (L := L) hm).live _)) (ih₂ hr.2 (O h₂ hr.2) _ ((LiveIn.part₂ (L := L) hm).live _)))
  | zeroE hs hm _ hV ih =>
      intro hr _ L hL; simp only [relaxedFree] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [ren_id])
        (absurdL_compatC hs (ih hr (O hV hr) _ (LiveIn.part₁ (L := L) hm)))
  | allI hbx hΔx hΓx h ih =>
      intro hr _ L hL; simp only [relaxedFree] at hr
      exact allI_seq_compatC hbx hΔx hΓx
        ((semC_liveEq (.dead (LiveEq.refl _))).mp (ih hr (O h hr) _ (hL.cons _ _)))
  | allE h hlt ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact allE_compatC (ih hr (O h hr) L hL) hlt
  | bangThunkF hp h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact bangThunkF_seq_compatC hp (ih hr (O h hr) _ (hL.cons _ _))
  | bangThunkV hp hC h q ih =>
      intro hr _ L hL; simp only [relaxedFree] at hr
      show SemV _ _ (match ownAt L _ with | .lam N => .lam N | _ => _) _
      split
      · next N hN =>
          have := ih hr (O h hr) L hL
          rw [hN] at this
          exact bangThunkV_compatC hp hC this
      · have := O h hr
        simp only [SemJ] at this
        rw [q] at this ⊢
        exact bangThunkV_compatC hp hC this
  | bangE h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact bangE_compatC (ih hr (O h hr) L hL)
  | boxI h hΓ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact boxI_compatC (ih hr (O h hr) L hL) hΓ
  | boxE h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact boxE_compatC (ih hr (O h hr) L hL)
  | immSub h hle ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact immSub_compatC (ih hr (O h hr) L hL) hle
  | mutSub h hle ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact mutSub_compatC (ih hr (O h hr) L hL) hle
  | lolliE hs hm _ ha hfn iha ihf =>
      intro hr _ L hL; simp only [relaxedFree, Bool.and_eq_true] at hr
      exact sem_split_eq hL (by nodeinv) (by simp only [ren_id])
        (lolliE_compatX hs (iha hr.1 (O ha hr.1) _ (LiveIn.part₁ (L := L) hm)) (ihf hr.2 (O hfn hr.2) _ (LiveIn.part₂ (L := L) hm)))
  | allEV h hlt ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact allE_compatX (ih hr (O h hr) L hL) hlt
  | ofRet h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | roll hA hc h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact roll_compatX hA hc (ih hr (O h hr) L hL)
  | unroll h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact unroll_compatX (ih hr (O h hr) L hL)
  | nuIn hC h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact nuIn_compatX hC (ih hr (O h hr) L hL)
  | nuOut hC h ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact nuOut_compatX hC (ih hr (O h hr) L hL)
  | litFn h _ _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | divLit h _ _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | walk h _ _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | walkGet h _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | selfCall h _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | lendCell h _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | nuEta h _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | use h _ ih => intro hr _ L hL; simp only [relaxedFree] at hr; exact ih hr (O h hr) L hL
  | _ => intro _ hs L hL; exact own_default rfl hL hs

/-- The oracle: a typed derivation with no relaxed rule is in the relation at its erasure
(`TDerivesP.toC`, `fundamentalC`). -/
theorem semJ_of_relaxedFree {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg}
    (h : TDerivesP Δ Γ t j) (hr : relaxedFree t = true) : SemJ (ℍ := ℍ) Δ Γ t.erase j :=
  fundamentalC (h.toC hr)

/-- **`own` meets the relative obligation**: whatever puts the checked term in the relation puts
`own`'s output there. A term with no relaxed rule is in it unconditionally; one with a relaxed
rule is its own erasure. -/
theorem own_lowerSemRel : LowerSemRel (ℍ := ℍ) own := by
  intro c hsem
  unfold own
  split
  · next hr =>
      exact own_semP semJ_of_relaxedFree c.typedP hr (semJ_of_relaxedFree c.typedP hr) []
        (LiveIn.nil _)
  · exact hsem

/-- **`own` meets the obligation.** -/
theorem own_lowerSem : LowerSem (ℍ := ℍ) own := own_lowerSemRel.lowerSem

/-- **What it buys**: every run of `own`'s output for a closed `main : F 1` with no relaxed rule
continues to `()` at the empty memory. -/
theorem own_every_run (c : Checked) (hp : c.pins = []) (hΓ : c.ctx = []) (hC : c.C = .ret .unit)
    {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (own c.t) μ₁ e₁) :
    BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  lowered_every_run own_lowerSem c hp hΓ hC hs

/-- Under `PinLaw`, for every closed `main : F 1`. -/
theorem own_every_run_pin (hPin : PinLaw (ℍ := ℍ)) (c : Checked) (hΓ : c.ctx = [])
    (hC : c.C = .ret .unit) {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (own c.t) μ₁ e₁) :
    BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  lowered_every_run_pin hPin own_lowerSemRel c hΓ hC hs

end Lowering
