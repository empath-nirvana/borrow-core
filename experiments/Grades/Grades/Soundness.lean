import Grades.Judgment

/-!
# Grades — soundness of the graded judgment

`fundamentalG`: under any profile whose droppable types hold only resources with no owned cell
(`SemForget`), a graded derivation is sound at its erasure.  Every rule reuses `Core`'s
compatibility lemma; the graded premises reach it through three facts:

* a graded split is `Ctx.SplitP` of the erasures (`GSplit.toSplitP`);
* a droppable slot at a forgettable type is removed by one frame lemma (`semC_weak`): its
  resource has no owned cell, and `wpTS_frame_noOwn` passes such a frame through any run.  This
  one lemma is what `forgetImm`, `forgetMut` (and, for persistent types, `DeadP.drop`) each do;
* promotion over a context whose live slots are persistent holds `∅` (`gSepC_deadP`), the premise
  `bangThunkF_compatC` uses, read at `VTy.persistent` instead of `!`-types.

The erased abstraction is `lam_compatC` after dropping the binder, whose run-time type
`ghost A` holds only `∅`; the erased application is `cC`'s `⊸` clause at `inj₁ ()`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Graded
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Grades
open Grades.Grade

/-! ### Forgettable types -/

/-- A value of `T` holds no owned cell, at every list, substitution and value. -/
def SemForget (T : VTy) : Prop :=
  ∀ (ls : List SRec) (δ : LSub) (v : Val) (ρ : WRes), vP T ls δ v ρ → NoOwn ρ

theorem semForget_of_persistent {T : VTy} (hT : T.persistent = true) : SemForget (ℍ := ℍ) T := by
  intro ls δ v ρ h
  rw [vP_empty_of_persistent hT h]
  exact noOwn_empty

/-- `Imm`, `Mut` and persistent types are forgettable: an `Imm`/`Mut` value holds one `imm`/`mut`
cell, which is not owned. -/
theorem semForget_forgettable : ∀ {T : VTy}, VTy.forgettable T = true → SemForget (ℍ := ℍ) T
  | .imm a A, _ => by
      intro ls δ v ρ h
      obtain ⟨α, -, ℓ, hs⟩ := h
      obtain ⟨-, himm⟩ := pure_sep_iff.mp hs
      obtain ⟨s, u, σ, hσ, ls₀, rfl, -⟩ := himm
      exact ResU.restrict_single_other (by simp)
  | .mut a A, _ => by
      intro ls δ v ρ h
      obtain ⟨α, -, ℓ, hs⟩ := h
      obtain ⟨-, hmut⟩ := pure_sep_iff.mp hs
      obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := hmut
      exact ResU.restrict_single_other (by simp)
  | .unit, h | .zero, h | .unk, h | .int _, h | .bang _, h | .tvar _, h | .tensor _ _, h
  | .sum _ _, h | .box _ _, h | .mu _, h | .thunk _, h | .ref _, h => semForget_of_persistent h

/-- `ghost A` holds only `∅`. -/
theorem ghost_empty {A : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vP (ghost A) ls δ v ρ) : ρ = PMap.empty := by
  rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
  · obtain ⟨-, hu⟩ := pure_sep_iff.mp hs
    exact hu.1
  · obtain ⟨-, ⟨w₁, w₂, hs'⟩⟩ := pure_sep_iff.mp hs
    obtain ⟨-, ⟨_, _, _, hz, _⟩⟩ := pure_sep_iff.mp hs'
    exact hz.elim

theorem semForget_ghost (A : VTy) : SemForget (ℍ := ℍ) (ghost A) := by
  intro ls δ v ρ h
  rw [ghost_empty h]
  exact noOwn_empty

theorem ghostV_rel (A : VTy) (ls : List SRec) (δ : LSub) :
    vP (ℍ := ℍ) (ghost A) ls δ ghostV PMap.empty :=
  Or.inl ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

/-! ### Dropping forgettable slots -/

/-- `Γ` is `Γc` with some dead slots made live, each at a forgettable type. -/
inductive Weak : Ctx VTy → Ctx VTy → Prop where
  | nil : Weak [] []
  | same {Γc Γ : Ctx VTy} (s : Slot VTy) : Weak Γc Γ → Weak (s :: Γc) (s :: Γ)
  | drop {Γc Γ : Ctx VTy} {T : VTy} (hT : SemForget (ℍ := ℍ) T) :
      Weak Γc Γ → Weak (⟨T, false⟩ :: Γc) (⟨T, true⟩ :: Γ)

theorem Weak.refl : ∀ Γ : Ctx VTy, Weak (ℍ := ℍ) Γ Γ
  | [] => .nil
  | s :: Γ => .same s (Weak.refl Γ)

theorem Weak.liveWithin {Γc Γ : Ctx VTy} (hw : Weak (ℍ := ℍ) Γc Γ) :
    ∀ {γ : List Val}, Ctx.LiveWithin Γ γ → Ctx.LiveWithin Γc γ := by
  induction hw with
  | nil => intro γ _; simp
  | same s _ ih =>
      intro γ h
      cases γ with
      | nil => exact ⟨h.1, ih h.2⟩
      | cons v γ => exact ih h
  | drop _ _ ih =>
      intro γ h
      cases γ with
      | nil => exact ⟨by simp, ih h.2⟩
      | cons v γ => exact ih h

theorem gSepC_nil_emp {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} :
    gSepC (ℍ := ℍ) ls δ Γ [] PMap.empty := by
  cases Γ <;> exact ⟨rfl, trivial⟩

/-- The dropped slots' resources split off, with no owned cell. -/
theorem gSepC_weak {ls : List SRec} {δ : LSub} {Γc Γ : Ctx VTy} (hw : Weak (ℍ := ℍ) Γc Γ) :
    ∀ {γ : List Val} {ρ : WRes}, gSepC ls δ Γ γ ρ →
      ∃ R ρc, ResU.CompS R ρc ρ ∧ NoOwn R ∧ gSepC ls δ Γc γ ρc := by
  induction hw with
  | nil =>
      intro γ ρ h
      exact ⟨PMap.empty, ρ, compS_empty_left ρ, noOwn_empty, h⟩
  | same s _ ih =>
      intro γ ρ h
      cases γ with
      | nil =>
          obtain ⟨rfl, -⟩ := h
          exact ⟨PMap.empty, PMap.empty, compS_empty_left _, noOwn_empty, gSepC_nil_emp⟩
      | cons v γ =>
          obtain ⟨T, l⟩ := s
          cases l with
          | false =>
              obtain ⟨R, ρc, hc, hR, h'⟩ := ih (γ := γ) h
              exact ⟨R, ρc, hc, hR, h'⟩
          | true =>
              obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
              obtain ⟨R, ρc, hc', hR, h'⟩ := ih hrest
              obtain ⟨x, hx, hxρ⟩ := compS_lcomm hc' hc
              exact ⟨R, x, hxρ, hR, ⟨ρ₁, ρc, hx, hv, h'⟩⟩
  | drop hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil =>
          obtain ⟨rfl, -⟩ := h
          exact ⟨PMap.empty, PMap.empty, compS_empty_left _, noOwn_empty, gSepC_nil_emp⟩
      | cons v γ =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨R, ρc, hc', hR, h'⟩ := ih hrest
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hc' hc
          exact ⟨x, ρc, hxρ, noOwn_compS hx (hT _ _ _ _ hv) hR, h'⟩

/-- A frame with no owned cell passes through `cC`, at every computation type. -/
theorem cC_frame {C : CTy} {ls : List SRec} {δ : LSub} {e : Expr} {R ρc ρ : WRes}
    (hR : NoOwn R) (hc : ResU.CompS R ρc ρ) (h : cC C ls δ e ρc) : cC C ls δ e ρ := by
  rw [cC_iff_stacks] at h ⊢
  intro S Q ρ₁ ρ₂ hs hc'
  obtain ⟨y, hy, hρ₂⟩ := compS_reassoc hc hc'
  exact wpTS_frame_noOwn (R := fun σ => σ = R) (fun _ h => h ▸ hR) ls _ Q ρ₂
    ⟨R, y, hρ₂, rfl, h S Q ρ₁ y hs hy⟩

/-- **Dropping forgettable slots** is sound: one lemma for every affine drop. -/
theorem semC_weak {Δ : LifeCtx} {Γc Γ : Ctx VTy} {e : Expr} {C : CTy}
    (h : SemC Δ Γc e C) (hw : Weak (ℍ := ℍ) Γc Γ) : SemC Δ Γ e C := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hs⟩ := gDenC_iff.mp hg
  obtain ⟨R, ρc, hc, hR, hs'⟩ := gSepC_weak hw hs
  exact cC_frame hR hc (h δ γ ls ρc hδ (gDenC_mk (hw.liveWithin hlen) hs'))

/-! ### Graded dead and solo contexts -/

/-- Every slot of a graded context made dead. -/
def kill (Γ : GCtx) : Ctx VTy := Γ.map fun s => ⟨s.ty, false⟩

theorem kill_dead : ∀ Γ : GCtx, Ctx.Dead (kill Γ)
  | [] => .nil
  | _ :: Γ => .cons (kill_dead Γ)

theorem GDrop.drop_of_live {P : Profile} {s : GSlot} (h : GDrop P s) (hl : s.g.live = true) :
    P.drop s.ty = true := by
  obtain ⟨hd, hok⟩ := h
  unfold Profile.Ok Grade.ok at hok
  rw [hd, hl] at hok
  generalize P.drop s.ty = f at hok ⊢
  generalize s.ty.persistent = p at hok
  revert hok; cases f <;> cases p <;> simp

variable {P : Profile} (hP : ∀ T, P.drop T = true → SemForget (ℍ := ℍ) T)
include hP

theorem gdrop_weak {s : GSlot} (hs : GDrop P s) {Γc Γ : Ctx VTy} (hw : Weak (ℍ := ℍ) Γc Γ) :
    Weak (ℍ := ℍ) (⟨s.ty, false⟩ :: Γc) (⟨s.ty, s.g.live⟩ :: Γ) := by
  cases hl : s.g.live
  · exact .same _ hw
  · exact .drop (hP _ (hs.drop_of_live hl)) hw

theorem GDead.weak : ∀ {Γ : GCtx}, GDead P Γ → Weak (ℍ := ℍ) (kill Γ) (GCtx.erase Γ)
  | [], _ => .nil
  | _ :: _, h => gdrop_weak hP h.head (GDead.weak h.tail)

theorem GSolo.weak : ∀ {Γ : GCtx} {i : Nat} {T : VTy}, GSolo P Γ i T →
    ∃ Γc, Weak (ℍ := ℍ) Γc (GCtx.erase Γ) ∧ Ctx.Solo Γc i T
  | _, _, _, .here (Γ := Γ) (T := T) hl _ hd =>
      ⟨⟨T, true⟩ :: kill Γ, by simp only [erase_cons, hl]; exact .same _ (GDead.weak hP hd),
        .here (kill_dead Γ)⟩
  | _, _, _, .there hs h => by
      obtain ⟨Γc, hw, hso⟩ := GSolo.weak h
      exact ⟨_ :: Γc, gdrop_weak hP hs hw, .there hso⟩

/-- A leaf at a graded dead context: `Core`'s compatibility lemma at the killed context, then
the drops. -/
theorem viaDead {Γ : GCtx} (hΓ : GDead P Γ) {Δ : LifeCtx} {e : Expr} {C : CTy}
    (h : ∀ Γc : Ctx VTy, Ctx.DeadP Γc → SemC Δ Γc e C) : SemC Δ (GCtx.erase Γ) e C :=
  semC_weak (h _ (kill_dead Γ).toP) (GDead.weak hP hΓ)

theorem viaSolo {Γ : GCtx} {i : Nat} {T : VTy} (hΓ : GSolo P Γ i T) {Δ : LifeCtx} {e : Expr}
    {C : CTy} (h : ∀ Γc : Ctx VTy, Ctx.SoloP Γc i T → SemC Δ Γc e C) :
    SemC Δ (GCtx.erase Γ) e C := by
  obtain ⟨Γc, hw, hso⟩ := GSolo.weak hP hΓ
  exact semC_weak (h Γc hso.toP) hw

omit hP

/-- Dropping slots of a split's right side is dropping them from the whole. -/
theorem splitP_weak_right : ∀ {Γ Γ₁ Γ₂ Γc : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → Weak (ℍ := ℍ) Γc Γ₂ →
    ∃ Γ', Ctx.SplitP Γ' Γ₁ Γc ∧ Weak (ℍ := ℍ) Γ' Γ
  | _, _, _, _, .nil, .nil => ⟨[], .nil, .nil⟩
  | _, _, _, _, .left h, .same _ hw => by
      obtain ⟨Γ', hs, hw'⟩ := splitP_weak_right h hw
      exact ⟨_, .left hs, .same _ hw'⟩
  | _, _, _, _, .right h, .same _ hw => by
      obtain ⟨Γ', hs, hw'⟩ := splitP_weak_right h hw
      exact ⟨_, .right hs, .same _ hw'⟩
  | _, _, _, _, .right h, .drop hT hw => by
      obtain ⟨Γ', hs, hw'⟩ := splitP_weak_right h hw
      exact ⟨_, .dead hs, .drop hT hw'⟩
  | _, _, _, _, .dead h, .same _ hw => by
      obtain ⟨Γ', hs, hw'⟩ := splitP_weak_right h hw
      exact ⟨_, .dead hs, .same _ hw'⟩
  | _, _, _, _, .dup hT h, .same _ hw => by
      obtain ⟨Γ', hs, hw'⟩ := splitP_weak_right h hw
      exact ⟨_, .dup hT hs, .same _ hw'⟩
  | _, _, _, _, .dup _ h, .drop _ hw => by
      obtain ⟨Γ', hs, hw'⟩ := splitP_weak_right h hw
      exact ⟨_, .left hs, .same _ hw'⟩

/-! ### Promotion over persistent contexts -/

theorem substAll_cons' (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

theorem deadP_of_persistent : ∀ {Γ : Ctx VTy},
    (∀ s ∈ Γ, s.live = true → s.ty.persistent = true) → Ctx.DeadP Γ
  | [], _ => .nil
  | ⟨T, l⟩ :: Γ, h => by
      have h' : ∀ s ∈ Γ, s.live = true → s.ty.persistent = true :=
        fun s hs hl => h s (List.mem_cons_of_mem _ hs) hl
      cases l with
      | false => exact .cons (deadP_of_persistent h')
      | true => exact .drop (h ⟨T, true⟩ List.mem_cons_self rfl) (deadP_of_persistent h')

/-- A well-graded `ω · Γ` has persistent live slots. -/
theorem persistent_of_gok {Q : Profile} {Γ : GCtx} (h : GOk Q (GCtx.scale ω Γ)) :
    ∀ s ∈ GCtx.erase Γ, s.live = true → s.ty.persistent = true := by
  intro s hs hl
  simp only [GCtx.erase, List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hok := h ⟨t.ty, ω * t.g⟩ (List.mem_map.mpr ⟨t, ht, rfl⟩)
  change Grade.ok (ω * t.g) (Q.drop t.ty) t.ty.persistent = true at hok
  rw [ω_mul_live t.g hl] at hok
  generalize Q.drop t.ty = f at hok
  generalize t.ty.persistent = p at hok ⊢
  revert hok; cases f <;> cases p <;> decide

/-- Promotion of `thunk M : U (F A)` over a context whose live slots are persistent. -/
theorem bangThunkF_compatG {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (hp : ∀ s ∈ Γ, s.live = true → s.ty.persistent = true)
    (h : SemC Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) :
    SemV Δ Γ (.val (.lam M)) (.bang (.thunk (.ret A))) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨-, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ ⟨gSepC_deadP (deadP_of_persistent hp) hgs, ?_⟩
  intro ls' hext
  refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) ls' δ ρ ?_
  rw [← substAll_cons']
  exact h δ (Val.unit :: γ) ls' ρ hδ (gDenC_dead_cons _ _ (gDenC_local hext hg))

/-- Promotion of a λ-value `V : C` over a context whose live slots are persistent. -/
theorem bangThunkV_compatG {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy}
    (hp : ∀ s ∈ Γ, s.live = true → s.ty.persistent = true)
    (hC : C.isRet = false) (h : SemC Δ Γ (.val (.lam N)) C) :
    SemV Δ Γ (.val (.lam N)) (.bang (.thunk C)) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨-, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  refine wpTS_val _ _ _ _ ⟨gSepC_deadP (deadP_of_persistent hp) hgs, ?_⟩
  intro ls' hext
  rw [forceE_of_not_ret hC]
  exact h δ γ ls' ρ hδ (gDenC_local hext hg)

/-! ### Erased abstraction and application -/

/-- `λ⁰x. M`: the binder is dead in `M`, so `M` holds at any argument, and the argument
(`ghost A`) holds `∅`. -/
theorem lam0_compat {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (h : SemC Δ (⟨A, false⟩ :: Γ) M C) : SemC Δ Γ (.val (.lam M)) (.arr (ghost A) C) :=
  lam_compatC (semC_weak ((semC_liveEq (.dead (LiveEq.refl Γ))).mp h)
    (.drop (semForget_ghost A) (Weak.refl Γ)))

theorem substAll_app_ghost (γ : List Val) (M : Expr) :
    substAll γ (.app M (.val ghostV)) = .app (substAll γ M) (.val ghostV) := by
  show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ ghostV.val) = _
  simp [Expr.psub, ghostV]; rfl

/-- `M [x]`: `M` applied to `inj₁ ()`, which holds `∅`. -/
theorem app0_compat {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (h : SemC Δ Γ M (.arr (ghost A) C)) : SemC Δ Γ (.app M (.val ghostV)) C := by
  intro δ γ ls ρ hδ hg
  rw [substAll_app_ghost]
  exact h δ γ ls ρ hδ hg ghostV PMap.empty ρ (ghostV_rel A ls δ) (ResU.comp_empty_right ρ)

/-! ### The Fundamental Property of the graded judgment -/

/-- **Fundamental Property**, graded: under a profile whose droppable types are forgettable, a
graded derivation is sound at its erasure.  Every case is `Core`'s compatibility lemma. -/
theorem fundamentalG {P : Profile} (hP : ∀ T, P.drop T = true → SemForget (ℍ := ℍ) T)
    {Δ : LifeCtx} {Γ : GCtx} {e : Expr} {j : Jdg}
    (h : GDerives P Δ Γ e j) : SemJ Δ (GCtx.erase Γ) e j := by
  induction h with
  | var h => exact viaSolo hP h fun _ h => var_compatC h
  | unitI h => exact viaDead hP h fun _ h => unitI_compatC h
  | tensorI hs _ _ ih₁ ih₂ => exact tensorI_compatC hs.toSplitP ih₁ ih₂
  | sumI₁ _ ih => exact sumI₁_compatC ih
  | sumI₂ _ ih => exact sumI₂_compatC ih
  | thunkF _ ih => exact thunkF_compatC ih
  | thunkV hC _ ih => exact thunkV_compatC hC ih
  | ret _ ih => exact ret_compatC ih
  | bind hs _ hg _ ihM ihN =>
      rw [SemJ, erase_cons_live hg] at ihN; exact bind_compatC hs.toSplitP ihM ihN
  | force h => exact viaSolo hP h fun _ h => force_compatC h
  | lam hg _ ih => rw [SemJ, erase_cons_live hg] at ih; exact lam_compatC ih
  | app hs _ hx ih =>
      obtain ⟨Γc, hw, hso⟩ := GSolo.weak hP hx
      obtain ⟨Γ', hs', hw'⟩ := splitP_weak_right hs.toSplitP hw
      exact semC_weak (app_compatC hs' ih hso.toP) hw'
  | withI _ _ ihM ihN => exact withI_compatC ihM ihN
  | proj₁ _ ih => exact proj₁_compatC ih
  | proj₂ _ ih => exact proj₂_compatC ih
  | topI => exact topI_compatC
  | unitE hs _ _ ihV ihM => exact unitE_compatC hs.toSplitP ihV ihM
  | tensorE hs _ hgA hgB _ ihV ihM =>
      rw [SemJ, erase_cons_live hgB, erase_cons_live hgA] at ihM
      exact tensorE_compatC hs.toSplitP ihV ihM
  | sumE hs _ hg₁ hg₂ _ _ ihV ih₁ ih₂ =>
      rw [SemJ, erase_cons_live hg₁] at ih₁; rw [SemJ, erase_cons_live hg₂] at ih₂
      exact sumE_compatC hs.toSplitP ihV ih₁ ih₂
  | zeroE hs _ ihV => exact zeroE_compatC hs.toSplitP ihV
  | allI hbx hΔx hΓx _ ih =>
      exact allI_compatC hbx hΔx hΓx ((semC_liveEq (.dead (LiveEq.refl _))).mp ih)
  | allE _ hlt ih => exact allE_compatC ih hlt
  | bangThunkF hok _ _ ih =>
      show SemC _ _ _ _; rw [erase_scale_ω]; exact bangThunkF_compatG (persistent_of_gok hok) ih
  | bangThunkV hok _ hC _ ih =>
      show SemC _ _ _ _; rw [erase_scale_ω]; exact bangThunkV_compatG (persistent_of_gok hok) hC ih
  | bangE _ ih => exact bangE_compatC ih
  | copyBang hΓ => exact viaDead hP hΓ fun _ h => copyBang_compatC h
  | forgetBang hΓ => exact viaDead hP hΓ fun _ h => forgetBang_compatC h
  | boxI _ hΓ ih => exact boxI_compatC ih hΓ
  | boxE _ ih => exact boxE_compatC ih
  | immSub _ hle ih => exact immSub_compatC ih hle
  | mutSub _ hle ih => exact mutSub_compatC ih hle
  | alloc hΓ => exact viaDead hP hΓ fun _ h => alloc_compatX h
  | free hΓ => exact viaDead hP hΓ fun _ h => free_compatX h
  | swap hΓ => exact viaDead hP hΓ fun _ h => swap_compatX h
  | copy hΓ => exact viaDead hP hΓ fun _ h => copy_compatX h
  | forgetImm hΓ => exact viaDead hP hΓ fun _ h => forgetImm_compatX h
  | forgetMut hΓ => exact viaDead hP hΓ fun _ h => forgetMut_compatX h
  | forgetUnk hΓ => exact viaDead hP hΓ fun _ h => forgetUnk_compatX h
  | lit c hΓ => exact viaDead hP hΓ fun _ h => lit_compatX c h
  | hostOp op hΓ => exact viaDead hP hΓ fun _ h => hostOp_compatX op h
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact viaDead hP hΓ fun _ h => withbor1_compatX x h hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ =>
      exact viaDead hP hΓ fun _ h => withbor2_compatX x h hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact viaDead hP hΓ fun _ h => withbor3_compatX x h hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact viaDead hP hΓ fun _ h => withload_compatX x h hx hf₁ hf₂
  | withswap hΓ => exact viaDead hP hΓ fun _ h => withswap_compatX h
  | lolliE hs _ _ iha ihf => exact lolliE_compatX hs.toSplitP iha ihf
  | allEV _ hlt ih => exact allE_compatX ih hlt
  | ofRet _ ih => exact ih
  | roll hA hc _ ih => exact roll_compatX hA hc ih
  | unroll _ ih => exact unroll_compatX ih
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      exact viaDead hP hΓ fun _ h => foldImm_compatX F hF hG y c R h hyM hyR hR
  | foldOwn F R hΓ hF hG => exact viaDead hP hΓ fun _ h => foldOwn_compatX F hF hG R h
  | foldReuse F R hΓ hF hG => exact viaDead hP hΓ fun _ h => foldReuse_compatX F hF hG R h
  | nuIn hC _ ih => exact nuIn_compatX hC ih
  | nuOut hC _ ih => exact nuOut_compatX hC ih
  | unfoldN C S hC hΓ => exact viaDead hP hΓ fun _ h => unfold_compatX hC S h
  | lam0 _ _ ih => exact lam0_compat ih
  | app0 _ _ _ ih => exact app0_compat ih

/-- The graded profile's droppable types are forgettable. -/
theorem graded_drop_sound : ∀ T, Profile.graded.drop T = true → SemForget (ℍ := ℍ) T :=
  fun _ h => semForget_forgettable h

/-- `fundamentalG` at the graded profile. -/
theorem fundamentalGraded {Δ : LifeCtx} {Γ : GCtx} {e : Expr} {j : Jdg}
    (h : GDerives Profile.graded Δ Γ e j) : SemJ (ℍ := ℍ) Δ (GCtx.erase Γ) e j :=
  fundamentalG graded_drop_sound h

end BoCa.Fig16.LogRel.Core.Graded

end
