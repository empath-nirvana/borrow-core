import ProbeD1.Own

/-!
# ProbeD1 — statement 0's `U`-clause facts at the guarded W: `[force]`, the thaw, the callback

* **`[force]`** (`forceRow`, every placement): the `U` clause read at the identity, the list
  itself, the stack's own lifetimes and (at `cbpv` and `binder`) the reflexive future, the dropped
  views handed back. Its guard is the table the judgement assumes. The context is a solo slot up
  to persistent ones (`gSepRL_soloP`, the kernel's `gSepC_soloP` at W).
* **The thaw at a re-lend** (`thawRelend`, every placement): the old witnesses, the share above
  the outermost lend at the re-lend too (`stratS_mono`), every later re-lend, list and future of
  the re-lent value one of the original's (`reLend_trans`, `Ext.trans`). GhostEnd's
  `relendableS_thunkA` at W's `U` clause.
* **The callback at `σ·y`** (`callbackExtMut_own`, `callbackExtImm_own`; at `binder0` and
  `binder`): the `U` clause at the identity gives the callback's `∀`; the `∀` clause's own lend at
  the stack itself, the entry the lend pushes, gives its body at `σ·y`, at the instance's lifetime
  and with the bound read at the old stack as `OwnPush` reads it; the `⊸` clause there takes the
  argument. GhostEnd's `callback_ext` at W.
* **At `cbpv`** the own lend is the `U` clause's, and the `∀` clause at the pushed stack is the
  plain one, whose bound is read at the pushed stack's substitution. The two readings of the bound
  agree when the bound does not mention the binder (`callbackExtMut_cbpv_of`,
  `callbackExtImm_cbpv_of`, under `c.mentions y = false`). `CallbackExtMut cbpv` as stated has no
  such hypothesis, and at a bound that mentions the binder the pushed stack reads the binder at the
  entry's own lifetime. I have not derived that case.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS RelendableS)

/-! ### The context at W: persistent slots, dead contexts, a solo slot -/

/-- At a persistent type W's relation holds only at `∅`. -/
theorem vRL_empty_of_persistent (p : Placement) : ∀ {A : VTy}, A.Persistent →
    ∀ {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes},
      vRL p σ δ A αs ls v ρ → ρ = PMap.empty
  | .unit, hp, _, _, _, _, _, _, h => vP_empty_of_persistent hp h
  | .zero, hp, _, _, _, _, _, _, h => vP_empty_of_persistent hp h
  | .unk, hp, _, _, _, _, _, _, h => vP_empty_of_persistent hp h
  | .int _, hp, _, _, _, _, _, _, h => vP_empty_of_persistent hp h
  | .tvar _, hp, _, _, _, _, _, _, h => vP_empty_of_persistent hp h
  | .mu _, hp, _, _, _, _, _, _, h => vP_empty_of_persistent hp h
  | .bang _, _, _, _, _, _, _, _, h => h.1
  | .tensor A B, hp, _, _, _, _, _, _, h => by
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      rw [vRL_empty_of_persistent p hp.1 h₁, vRL_empty_of_persistent p hp.2 h₂] at hc
      exact eq_empty_of_compS_empty hc
  | .sum A B, hp, _, _, _, _, _, _, h => by
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
      · exact vRL_empty_of_persistent p hp.1 (pure_sep_iff.mp hs).2
      · exact vRL_empty_of_persistent p hp.2 (pure_sep_iff.mp hs).2
  | .box _ A, hp, _, _, _, _, _, _, h => by
      obtain ⟨α, -, hb, -⟩ := h
      exact vRL_empty_of_persistent p (A := A) hp hb
  | .thunk _, hp, _, _, _, _, _, _, _ => absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | .ref _, hp, _, _, _, _, _, _, _ => absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | .imm _ _, hp, _, _, _, _, _, _, _ => absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | .mut _ _, hp, _, _, _, _, _, _, _ => absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | .fam _, hp, _, _, _, _, _, _, _ => absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | .opq _, hp, _, _, _, _, _, _, _ => absurd hp (by simp [VTy.Persistent, VTy.persistent])

section ctx
variable {p : Placement} {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec}

theorem gSepRL_cons_persistent {T : VTy} (hT : T.Persistent) {Γ : Ctx VTy} {v : Val}
    {γ : List Val} {ρ : WRes} (h : gSepRL p σ δ αs ls (⟨T, true⟩ :: Γ) (v :: γ) ρ) :
    vRL p σ δ T αs ls v PMap.empty ∧ gSepRL p σ δ αs ls Γ γ ρ := by
  obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
  obtain rfl := vRL_empty_of_persistent p hT hv
  rw [eq_of_compS_empty_left hc]
  exact ⟨hv, hrest⟩

/-- A consumed context, up to persistent slots, holds nothing (`gSepC_deadP` at W). -/
theorem gSepRL_deadP : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → ∀ {γ : List Val} {ρ : WRes},
    gSepRL p σ δ αs ls Γ γ ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; cases γ <;> exact h.1
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (γ := γ') h
  | drop hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (gSepRL_cons_persistent hT h).2

/-- **A solo slot's context is the slot's value** (`gSepC_soloP` at W). -/
theorem gSepRL_soloP : ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.SoloP Γ i T →
    ∀ {γ : List Val} {ρ : WRes}, i < γ.length → gSepRL p σ δ αs ls Γ γ ρ →
      ∃ v, γ[i]? = some v ∧ vRL p σ δ T αs ls v ρ := by
  intro Γ i T hs
  induction hs with
  | here hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [gSepRL_deadP hdead hrest] at hc
          rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
          exact ⟨v, rfl, hv⟩
  | there _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨w, hw, hv⟩ := ih (γ := γ') (by simpa using hlen) hg
          exact ⟨w, by simpa using hw, hv⟩
  | skip hS _ ih =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨w, hw, hv⟩ := ih (γ := γ') (by simpa using hlen) (gSepRL_cons_persistent hS hg).2
          exact ⟨w, by simpa using hw, hv⟩

end ctx

theorem substAll_forceE' {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v) :
    ∀ C : CTy, substAll γ (forceE C (.var i)) = forceE C (.val v)
  | .ret _ => by
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, GhostEnd.substAll_var_l hv]; rfl
  | .eff _ _ _ _ _ _ => by
      show Expr.app (Expr.psub 0 γ (.var i)) (Expr.psub 0 γ Expr.unit) = _
      rw [← substAll, GhostEnd.substAll_var_l hv]; rfl
  | .arr _ _ => GhostEnd.substAll_var_l hv
  | .amp _ _ => GhostEnd.substAll_var_l hv
  | .top => GhostEnd.substAll_var_l hv
  | .all _ _ _ => GhostEnd.substAll_var_l hv
  | .nu _ => GhostEnd.substAll_var_l hv

/-! ### The `U` clause at the identity -/

theorem extQ_refl (b : Bool) (ls : List SRec) (ρ : WRes) : ExtQ b ls ls ρ := by
  unfold ExtQ; split
  · exact Ext.refl ls ρ
  · rfl

theorem futQ_refl (b : Bool) (δ : LSub) (ρ : WRes) (s : Stk) : FutQ b δ ρ s s := by
  unfold FutQ; split
  · exact Relation.ReflTransGen.refl
  · rfl

theorem futAvoids_self (C : CTy) (σ : LStack) : FutAvoids C σ σ :=
  fun _ he hx => absurd (List.mem_map_of_mem he) hx

theorem vRL_thunk_eq (p : Placement) (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life)
    (ls : List SRec) (f : Val) :
    vRL p σ δ (.thunk C) αs ls f =
      guardW σ αs (if p.uFut || p.uOwn then
          RelendU p.uFut p.uOwn δ σ C
            (fun σ' αs' ls' => cRL p σ' δ C αs' ls' (forceE C (.val f))) αs ls
        else
          RelendableS δ [] σ (fun αs' ls' => cRL p σ δ C αs' ls' (forceE C (.val f))) αs ls) := by
  rw [vRL]

/-- **The `U` clause at the identity**: the list carried along `Ext`, the stack's own lifetimes,
the reflexive future; the guard is the table. -/
theorem force_U (p : Placement) {σ : LStack} {δ : LSub} {C : CTy} {αs : List Life}
    {ls ls' : List SRec} {f : Val} {ρ : WRes} (hc : List.IsChain (· < ·) αs) (ht : TabAtS σ αs ρ)
    (he : Ext ls ls' ρ) (h : vRL p σ δ (.thunk C) αs ls f ρ) :
    cRL p σ δ C αs ls' (forceE C (.val f)) ρ := by
  rw [vRL_thunk_eq] at h
  have h' := h ht
  split at h'
  · obtain ⟨ds, ρz, ρn, hcomp, hn, -, H⟩ := h'
    exact (H ls' (he.left hcomp) αs (GhostEnd.reLend_refl hc) σ αs (futQ_refl _ δ ρz _)
      (futAvoids_self C σ)).1 ρn ρ (GhostEnd.vwS_local (he.right hcomp) hn) hcomp
  · obtain ⟨ds, ρz, ρn, hcomp, hn, -, H⟩ := h'
    exact H ls' (he.left hcomp) αs (GhostEnd.reLend_refl hc) ρn ρ
      (GhostEnd.vwS_local (he.right hcomp) hn) hcomp

/-- **`ForceRow` at every placement.** -/
theorem forceRow (p : Placement) : ForceRow (ℍ := ℍ) p := by
  intro Δ Γ i C hsolo _ _ δ σ αs ls γ ρ hok _ _ _ ht hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  obtain ⟨v, hv, hval⟩ := gSepRL_soloP hsolo (hsolo.lt_of_liveWithin hlw) hgs
  show cRL p σ δ C αs ls (substAll γ (forceE C (.var i))) ρ
  rw [substAll_forceE' hv]
  exact force_U p hok.2.1 ht (Ext.refl ls ρ) hval

/-- **`ThawRelend` at every placement**: the original witnesses, every later re-lend, list and
future of the re-lent value one of the original's. -/
theorem thawRelend (p : Placement) : ThawRelend (ℍ := ℍ) p := by
  intro σ δ C αs ls f ρ _ ht h
  rw [vRL_thunk_eq] at h
  have h' := h ht
  by_cases hb : (p.uFut || p.uOwn) = true
  · rw [if_pos hb] at h'
    obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h'
    refine ⟨ds, ρz, ρn, hc, hn, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
    rw [vRL_thunk_eq]
    intro _
    rw [if_pos hb]
    exact ⟨ds, ρz, ρv, hcv, hv, GhostEnd.stratS_mono hr hz,
      fun ls'' he' αs'' hr' σ' αs''' hf hav =>
        H ls'' (he.trans he') αs'' (GhostEnd.reLend_trans hr' hr) σ' αs''' hf hav⟩
  · rw [if_neg hb] at h'
    obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h'
    refine ⟨ds, ρz, ρn, hc, hn, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
    rw [vRL_thunk_eq]
    intro _
    rw [if_neg hb]
    exact ⟨ds, ρz, ρv, hcv, hv, GhostEnd.stratS_mono hr hz,
      fun ls'' he' αs'' hr' => H ls'' (he.trans he') αs'' (GhostEnd.reLend_trans hr' hr)⟩

/-! ### The callback at `σ·y` -/

theorem OwnOK.part {δ : LSub} {σ : LStack} {αs : List Life} {e : LEnt} {a : Life}
    {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (h : OwnOK δ σ αs e a ρ) : OwnOK δ σ αs e a ρ₁ :=
  { h with below := ResU.CompS.inStratum_left hc h.below }

/-- The callback's own lend at the stack itself, at a placement whose `∀` clause makes it: the
body of a `∀`-computation at the pushed stack, at the instance's lifetime. -/
theorem all_own {p : Placement} (hp : p.allOwn = true) {σ : LStack} {δ : LSub} {y : LifeVar}
    {c : Lifetime.Life} {C' : CTy} {αs : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cRL p σ δ (.all y c C') αs ls e ρ) {en : LEnt} {α : Life} (hex : en.x = y)
    (hy : y ∉ CTy.binders C') (hown : OwnOK δ σ αs en α ρ) (hlt : LtLife (extS δ σ αs) c α)
    (ht : TabAtS (en :: σ) (α :: αs) ρ) :
    cRL p (en :: σ) (δ.extend y α) C' (α :: αs) ls (.app e (.val .unit)) ρ :=
  (h ls σ αs (extQ_refl _ ls ρ) (futQ_refl _ δ ρ _) (futAvoids_self _ σ)).2 hp en α
    ⟨y, c, C', rfl, hex, hy, hown, hlt⟩ ht

/-- `⊸` at the stack itself: the argument's resource joined, the result under the guard. -/
theorem arr_app {p : Placement} {σ : LStack} {δ : LSub} {A : VTy} {D : CTy} {αs : List Life}
    {ls : List SRec} {e : Expr} {w : Val} {ρf ρv ρ : WRes} (h : cRL p σ δ (.arr A D) αs ls e ρf)
    (hw : vRL p σ δ A αs ls w ρv) (hc : ResU.CompS ρf ρv ρ) (ht : TabAtS σ αs ρ) :
    cRL p σ δ D αs ls (.app e (.val w)) ρ :=
  h ls σ αs (extQ_refl _ ls ρf) (futQ_refl _ δ ρf _) (futAvoids_self _ σ) w ρv ρ hw hc ht

/-- **A 6.65 callback at `σ·y`, at a placement whose `∀` clause makes the own lend.** -/
theorem callbackExtMut_own (p : Placement) (hp : p.allOwn = true) : CallbackExtMut (ℍ := ℍ) p := by
  intro σ δ y c T D αs ls f w ρf e α ρv ρ hok hex _ hy hown hlt htf hf hw hc ht
  have hall := force_U p hok.2.1 htf (Ext.refl ls ρf) hf
  have htf' : TabAtS (e :: σ) (α :: αs) ρf := ((GhostEnd.tabAtS_comp hc).mp ht).1
  exact arr_app (all_own hp hall hex hy hown hlt htf') hw hc ht

/-- **A 6.64 callback at `σ·y`, at a placement whose `∀` clause makes the own lend.** -/
theorem callbackExtImm_own (p : Placement) (hp : p.allOwn = true) : CallbackExtImm (ℍ := ℍ) p := by
  intro σ δ y c T D αs ls ls' f w ρf e u α ρv ρ hok hex _ hy hown hlt htf he hf hw hc ht
  have hall := force_U p hok.2.1 htf he hf
  have htf' : TabAtS (e :: σ) (α :: αs) ρf := ((GhostEnd.tabAtS_comp hc).mp ht).1
  exact arr_app (all_own hp hall hex hy hown hlt htf') hw hc ht

theorem callbackExtMut_binder0 : CallbackExtMut (ℍ := ℍ) .binder0 := callbackExtMut_own _ rfl
theorem callbackExtMut_binder : CallbackExtMut (ℍ := ℍ) .binder := callbackExtMut_own _ rfl
theorem callbackExtImm_binder0 : CallbackExtImm (ℍ := ℍ) .binder0 := callbackExtImm_own _ rfl
theorem callbackExtImm_binder : CallbackExtImm (ℍ := ℍ) .binder := callbackExtImm_own _ rfl

/-! ### At `cbpv`: the own lend at `U`, the plain `∀` at the pushed stack -/

/-- The `U` clause's own lend at `cbpv`, at the stack itself: the forced computation at the pushed
stack. -/
theorem force_own_cbpv {σ : LStack} {δ : LSub} {C : CTy} {αs : List Life} {ls ls' : List SRec}
    {f : Val} {ρ : WRes} (hc : List.IsChain (· < ·) αs) (ht : TabAtS σ αs ρ) (he : Ext ls ls' ρ)
    (h : vRL .cbpv σ δ (.thunk C) αs ls f ρ) {en : LEnt} {a : Life}
    (hown : ∀ {ρz ρn : WRes}, ResU.CompS ρz ρn ρ → OwnPush δ C ρz (σ, αs) en a) :
    cRL .cbpv (en :: σ) δ C (a :: αs) ls' (forceE C (.val f)) ρ := by
  rw [vRL_thunk_eq] at h
  have h' := h ht
  have hb : (Placement.cbpv.uFut || Placement.cbpv.uOwn) = true := rfl
  rw [if_pos hb] at h'
  obtain ⟨ds, ρz, ρn, hcomp, hn, -, H⟩ := h'
  exact (H ls' (he.left hcomp) αs (GhostEnd.reLend_refl hc) σ αs (futQ_refl _ δ ρz _)
    (futAvoids_self C σ)).2 rfl en a (hown hcomp) ρn ρ (GhostEnd.vwS_local (he.right hcomp) hn)
    hcomp

/-- **A 6.65 callback at `σ·y`, at `cbpv`, when the bound does not mention the binder.** -/
theorem callbackExtMut_cbpv_of : ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life)
    (T : VTy) (D : CTy) (αs : List Life) (ls : List SRec) (f w : Val) (ρf : WRes) (e : LEnt)
    (α : Life) (ρv ρ : WRes),
    c.mentions y = false →
    StackOK σ αs → e.x = y → e.k = .mut → y ∉ CTy.binders (.arr (.mut (.var y) T) D) →
    OwnOK δ σ αs e α ρf → LtLife (extS δ σ αs) c α → TabAtS σ αs ρf →
    vRL (ℍ := ℍ) .cbpv σ δ (.thunk (.all y c (.arr (.mut (.var y) T) D))) αs ls f ρf →
    vRL (ℍ := ℍ) .cbpv (e :: σ) (δ.extend y α) (.mut (.var y) T) (α :: αs) ls w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    cRL (ℍ := ℍ) .cbpv (e :: σ) (δ.extend y α) D (α :: αs) ls
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ := by
  intro σ δ y c T D αs ls f w ρf e α ρv ρ hcm hok hex _ hy hown hlt htf hf hw hc ht
  have hall := force_own_cbpv (en := e) (a := α) hok.2.1 htf (Ext.refl ls ρf) hf
    (fun hcomp => ⟨y, c, _, rfl, hex, hy, hown.part hcomp, hlt⟩)
  have htf' : TabAtS (e :: σ) (α :: αs) ρf := ((GhostEnd.tabAtS_comp hc).mp ht).1
  have hlt' : LtLife (extS δ (e :: σ) (α :: αs)) c α := by
    obtain ⟨β, hβ, hαβ⟩ := hlt
    refine ⟨β, ?_, hαβ⟩
    show c.interp ((extS δ σ αs).extend e.x α) = some β
    rw [hex, interp_extend_of_not_mentions hcm]; exact hβ
  have hbody := (hall ls (e :: σ) (α :: αs) (extQ_refl _ ls ρf) (futQ_refl _ δ ρf _)
    (futAvoids_self _ _)).1 α PMap.empty ρf ⟨rfl, hlt'⟩ (ResU.comp_empty_right ρf) htf'
  exact arr_app hbody hw hc ht

/-- **A 6.64 callback at `σ·y`, at `cbpv`, when the bound does not mention the binder.** -/
theorem callbackExtImm_cbpv_of : ∀ (σ : LStack) (δ : LSub) (y : LifeVar) (c : Lifetime.Life)
    (T : VTy) (D : CTy) (αs : List Life) (ls ls' : List SRec) (f w : Val) (ρf : WRes) (e : LEnt)
    (u : Val) (α : Life) (ρv ρ : WRes),
    c.mentions y = false →
    StackOK σ αs → e.x = y → e.k = .imm u → y ∉ CTy.binders (.arr (.imm (.var y) T) D) →
    OwnOK δ σ αs e α ρf → LtLife (extS δ σ αs) c α → TabAtS σ αs ρf → Ext ls ls' ρf →
    vRL (ℍ := ℍ) .cbpv σ δ (.thunk (.all y c (.arr (.imm (.var y) T) D))) αs ls f ρf →
    vRL (ℍ := ℍ) .cbpv (e :: σ) (δ.extend y α) (.imm (.var y) T) (α :: αs) ls' w ρv →
    ResU.CompS ρf ρv ρ → TabAtS (e :: σ) (α :: αs) ρ →
    cRL (ℍ := ℍ) .cbpv (e :: σ) (δ.extend y α) D (α :: αs) ls'
      (.app (.app (.val f) (.val .unit)) (.val w)) ρ := by
  intro σ δ y c T D αs ls ls' f w ρf e u α ρv ρ hcm hok hex _ hy hown hlt htf he hf hw hc ht
  have hall := force_own_cbpv (en := e) (a := α) hok.2.1 htf he hf
    (fun hcomp => ⟨y, c, _, rfl, hex, hy, hown.part hcomp, hlt⟩)
  have htf' : TabAtS (e :: σ) (α :: αs) ρf := ((GhostEnd.tabAtS_comp hc).mp ht).1
  have hlt' : LtLife (extS δ (e :: σ) (α :: αs)) c α := by
    obtain ⟨β, hβ, hαβ⟩ := hlt
    refine ⟨β, ?_, hαβ⟩
    show c.interp ((extS δ σ αs).extend e.x α) = some β
    rw [hex, interp_extend_of_not_mentions hcm]; exact hβ
  have hbody := (hall ls' (e :: σ) (α :: αs) (extQ_refl _ ls' ρf) (futQ_refl _ δ ρf _)
    (futAvoids_self _ _)).1 α PMap.empty ρf ⟨rfl, hlt'⟩ (ResU.comp_empty_right ρf) htf'
  exact arr_app hbody hw hc ht

end ProbeD1

end
