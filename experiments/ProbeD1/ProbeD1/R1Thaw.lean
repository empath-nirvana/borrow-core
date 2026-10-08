import ProbeD1.R1

/-!
# ProbeD1 — R1: the thaw at every type, W reading `μ` and `fam` itself (`R1MONO.md` §1)

`R1.lean` states `vRLM`: `vRLJ` with Core's `tvar`, `μ` and `fam` clauses read at W's formers. This
file proves what `R1MONO.md` §1 plans for it.

* **Where `vRLM` is `vRLJ`** (`relMAgreesJ`): at a type with no `μ`, `fam`, type variable, lifetime
  `∀` or persistent thunk outside a borrow payload, computation types included. The leaves agree
  because `wClose none` is the identity.
* **The persistence box** (`pBox_mono`, `pBox_inst`, `pBox_env`): what the `!` clause's box asks is
  kept by an instantiation (`instComp`), and at a thunk it reads no environment.
* **The fixed point's facts** (`vRLMMonoAt`, `vRLMRoll`): monotone in a variable's candidate, and
  the body read at the `μ` itself is the `μ`. W's leaves read an environment entry only through
  its type, so monotonicity needs no `NoMut` at the leaves; the `μ` clause carries Core's `NoMut`
  conjunct as Core's does.
* **The thaw at every type** (`relendM_valueE`, `relendMValue`): by induction on the type, the
  environment generalised (`EnvThaws`). At `μ` the fixed point's own least-ness puts the value in
  the candidate "related, and thawing under the guard"; the candidate is closed under the body by
  the induction hypothesis at the body, at the environment that reads the variable at the
  candidate, and `vRLMRoll` at each instantiated index. At `[L]` slot by slot
  (`relendJ_sepRange`); at a variable by the environment's hypothesis; every other case is
  `GapRows.lean`'s, the leaves at their closed types.
* **The corollaries** (`ctxRelendsAllM`, `thawInstM`, the two `U` rows `thunkFRowM` and
  `thunkVRowM`): `GapRows.lean`'s proofs at `vRLM`, at every context. The two `!U` rows and
  `statement0UFullM` are in `R1Box.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty innerView)
open BoCa.BoLo (Step1N Head)

/-! ### The environment and the equations -/

theorem wEnvP_eq (η : Option (Nat → WEnt)) (n : Nat) (v : Val) :
    wEnvP η n v = (wEnv η n).P v := by
  cases η <;> rfl

theorem wClose_eq (η : Option (Nat → WEnt)) (A : VTy) :
    wClose η A = A.subst (fun n => (wEnv η n).ty) := by
  cases η with
  | none => exact (VTy.subst_id A).symm
  | some η => rfl

/-- The closed type depends only on the environment's types. -/
theorem wClose_congr {η η' : Option (Nat → WEnt)}
    (h : ∀ n, (wEnv η' n).ty = (wEnv η n).ty) (A : VTy) :
    wClose η' A = wClose η A := by
  rw [wClose_eq, wClose_eq]
  congr 1
  funext n
  exact h n

theorem vRLM_mut_eq (p : Placement) (η : Option (Nat → WEnt)) (σ : LStack) (δ : LSub)
    (a : Lifetime.Life) (T : VTy) (αs : List Life) (ls : List SRec) (v : Val) :
    vRLM (ℍ := ℍ) p η σ δ (.mut a T) αs ls v = vRLJ (ℍ := ℍ) p σ δ (.mut a (wClose η T)) αs ls v := by
  rw [vRLM, vRLJ_mut_eq]

theorem vRLM_imm_eq (p : Placement) (η : Option (Nat → WEnt)) (σ : LStack) (δ : LSub)
    (a : Lifetime.Life) (T : VTy) (αs : List Life) (ls : List SRec) (v : Val) :
    vRLM (ℍ := ℍ) p η σ δ (.imm a T) αs ls v = vRLJ (ℍ := ℍ) p σ δ (.imm a (wClose η T)) αs ls v := by
  rw [vRLM, vRLJ_imm_eq]

theorem vRLM_thunk0 (η : Option (Nat → WEnt)) (σ : LStack) (δ : LSub) (C : CTy) (αs : List Life)
    (ls : List SRec) (f : Val) :
    vRLM (ℍ := ℍ) .binder0 η σ δ (.thunk C) αs ls f = guardPV (extS δ σ αs) σ αs ls
      (RelendJ δ σ (fun δ' αs' ls' => cRLM (ℍ := ℍ) .binder0 σ δ' C αs' ls' (forceE C (.val f)))
        αs ls) := by
  rw [vRLM]; rfl

/-- **`vRLM`'s `U` clause reads no environment.** -/
theorem vRLM_thunk_env (p : Placement) (η η' : Option (Nat → WEnt)) (σ : LStack) (δ : LSub)
    (C : CTy) (αs : List Life) (ls : List SRec) (f : Val) :
    vRLM (ℍ := ℍ) p η σ δ (.thunk C) αs ls f = vRLM (ℍ := ℍ) p η' σ δ (.thunk C) αs ls f := by
  rw [vRLM, vRLM]

/-! ### Where `vRLM` is `vRLJ` -/

mutual
theorem vRLM_none_eq (p : Placement) : ∀ (A : VTy), VMuFree A → VAllFree A → VBoxFree A →
    ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec),
      vRLM (ℍ := ℍ) p none σ δ A αs ls = vRLJ (ℍ := ℍ) p σ δ A αs ls
  | .thunk C, h, h', hb, σ, δ, αs, ls => by
      funext f
      have ih := cRLM_eq p C h h' hb
      rw [vRLM, vRLJ]
      simp only [ih]
  | .tensor A B, h, h', hb, σ, δ, αs, ls => by
      funext v
      have ihA := vRLM_none_eq p A h.1 h'.1 hb.1
      have ihB := vRLM_none_eq p B h.2 h'.2 hb.2
      rw [vRLM, vRLJ]
      simp only [ihA, ihB]
  | .sum A B, h, h', hb, σ, δ, αs, ls => by
      funext v
      have ihA := vRLM_none_eq p A h.1 h'.1 hb.1
      have ihB := vRLM_none_eq p B h.2 h'.2 hb.2
      rw [vRLM, vRLJ]
      simp only [ihA, ihB]
  | .bang A, h, h', hb, σ, δ, αs, ls => by
      funext v
      have ih := vRLM_none_eq p A h h' hb.2
      have hP : ∀ P, PBox A δ σ αs P ↔ True := fun P => by
        cases A with
        | thunk C => exact absurd rfl (hb.1 C)
        | _ => exact Iff.rfl
      rw [vRLM, vRLJ]
      funext ρ
      simp only [ih, hP, and_true]
  | .box a A, h, h', hb, σ, δ, αs, ls => by
      funext v
      have ih := vRLM_none_eq p A h h' hb
      rw [vRLM, vRLJ]
      simp only [ih]
  | .ref A, h, h', hb, σ, δ, αs, ls => by
      funext v
      have ih := vRLM_none_eq p A h h' hb
      rw [vRLM, vRLJ]
      simp only [ih]
  | .mut a T, _, _, _, σ, δ, αs, ls => by
      funext v
      rw [vRLM_mut_eq]; rfl
  | .imm a T, _, _, _, σ, δ, αs, ls => by
      funext v
      rw [vRLM_imm_eq]; rfl
  | .unit, _, _, _, _, _, _, _ => rfl
  | .zero, _, _, _, _, _, _, _ => rfl
  | .unk, _, _, _, _, _, _, _ => rfl
  | .int _, _, _, _, _, _, _, _ => rfl
  | .opq _, _, _, _, _, _, _, _ => rfl
  | .tvar _, h, _, _, _, _, _, _ => h.elim
  | .mu _, h, _, _, _, _, _, _ => h.elim
  | .fam _, h, _, _, _, _, _, _ => h.elim
theorem cRLM_eq (p : Placement) : ∀ (C : CTy), CMuFree C → CAllFree C → CBoxFree C →
    ∀ (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec),
      cRLM (ℍ := ℍ) p σ δ C αs ls = cRLJ (ℍ := ℍ) p σ δ C αs ls
  | .ret B, h, h', hb, σ, δ, αs, ls => by
      funext e
      have ih := vRLM_none_eq p B h h' hb
      rw [cRLM, cRLJ]
      simp only [ih]
  | .arr A C, h, h', hb, σ, δ, αs, ls => by
      funext e
      have ihA := vRLM_none_eq p A h.1 h'.1 hb.1
      have ihC := cRLM_eq p C h.2 h'.2 hb.2
      rw [cRLM, cRLJ]
      simp only [ihA, ihC]
  | .amp C D, h, h', hb, σ, δ, αs, ls => by
      funext e
      have ihC := cRLM_eq p C h.1 h'.1 hb.1
      have ihD := cRLM_eq p D h.2 h'.2 hb.2
      rw [cRLM, cRLJ]
      simp only [ihC, ihD]
  | .top, _, _, _, _, _, _, _ => by
      funext e
      rw [cRLM, cRLJ]
  | .all _ _ _, _, h', _, _, _, _, _ => h'.elim
  | .nu C, _, _, _, σ, δ, αs, ls => by
      funext e
      rw [cRLM, cRLJ]
  | .eff n i q A B C, h, h', hb, σ, δ, αs, ls => by
      funext e
      have ih := effRetM_eq p C h h' hb
      rw [cRLM, cRLJ]
      simp only [ih]
theorem effRetM_eq (p : Placement) : ∀ (C : CTy), CMuFree C → CAllFree C → CBoxFree C →
    ∀ (σ : LStack) (δ : LSub) (αs : List Life),
      effRetM (ℍ := ℍ) p σ δ C αs = effRetJ (ℍ := ℍ) p σ δ C αs
  | .ret A, h, h', hb, σ, δ, αs => by
      have ih := vRLM_none_eq p A h h' hb
      rw [effRetM, effRetJ]
      funext ls v
      rw [ih]
  | .eff _ _ _ _ _ C, h, h', hb, σ, δ, αs => by
      have ih := effRetM_eq p C h h' hb
      rw [effRetM, effRetJ]
      exact ih σ δ αs
  | .arr _ _, _, _, _, _, _, _ => rfl
  | .amp _ _, _, _, _, _, _, _ => rfl
  | .top, _, _, _, _, _, _ => rfl
  | .all _ _ _, _, _, _, _, _, _ => rfl
  | .nu _, _, _, _, _, _, _ => rfl
end

/-- **`RelMAgreesJ`**, restated at types with no lifetime `∀` (`NEXT.md` §3.1) and no persistent
thunk. The statement without `VAllFree` was proved at commit `5210cf1`, before (E1) and (E2)
changed `vRLM`'s `∀` clause; the one without `VBoxFree` before the persistence box. -/
theorem relMAgreesJ : RelMAgreesJ (ℍ := ℍ) :=
  ⟨fun p σ δ A αs ls v hA hA' hb => by rw [vRLM_none_eq p A hA hA' hb],
    fun p σ δ C αs ls e hC hC' hb => by rw [cRLM_eq p C hC hC' hb]⟩


/-! ### The persistence box -/

/-- **The box is monotone in what it asks.** -/
theorem pBox_mono {A : VTy} {δ : LSub} {σ : LStack} {αs : List Life}
    {P Q : LStack → LSub → List Life → List SRec → Prop}
    (hPQ : ∀ σ' δ' αs' ls', P σ' δ' αs' ls' → Q σ' δ' αs' ls') (h : PBox A δ σ αs P) :
    PBox A δ σ αs Q := by
  cases A with
  | thunk C => exact fun ι hat ls' hro σ' αs' hst => hPQ _ _ _ _ (h ι hat ls' hro σ' αs' hst)
  | _ => trivial

/-- **The box at a thunk type**, unfolded. -/
theorem pBox_thunk {C : CTy} {δ : LSub} {σ : LStack} {αs : List Life}
    {P : LStack → LSub → List Life → List SRec → Prop} :
    PBox (.thunk C) δ σ αs P ↔ ∀ ι : Inst, InstAt αs ι → ∀ ls' : List SRec,
      RecsOutside (ι.life αs) ls' → ∀ (σ' : LStack) (αs' : List Life),
        Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs') →
        P σ' (ι.sub δ) αs' ls' := Iff.rfl

/-- **The box is kept by an instantiation**: an instantiation of the instantiated stack, after the
first, is one of the stack (`instComp`). -/
theorem pBox_inst {A : VTy} {δ : LSub} {σ : LStack} {αs : List Life}
    {P : LStack → LSub → List Life → List SRec → Prop} {ι : Inst} (hat : InstAt αs ι)
    (h : PBox A δ σ αs P) : PBox A (ι.sub δ) σ (ι.life αs) P := by
  cases A with
  | thunk C =>
      intro ι₂ hat₂ ls' hro σ' αs' hst
      obtain ⟨ι₃, hat₃, hsub, hlife, -⟩ := instComp αs ι ι₂ hat hat₂
      have hl₃ : ι₃.life αs = ι₂.life (ι.life αs) := by
        simp only [Inst.life, List.map_map]
        exact List.map_congr_left fun a _ => hlife a
      have := h ι₃ hat₃ ls' (by rw [hl₃]; exact hro) σ' αs' (by rw [hl₃, hsub]; exact hst)
      rwa [hsub] at this
  | _ => trivial

/-- **The box asks nothing at a type that is no thunk.** -/
theorem pBox_of_not_thunk {A : VTy} {δ : LSub} {σ : LStack} {αs : List Life}
    {P : LStack → LSub → List Life → List SRec → Prop} (h : ∀ C, A ≠ .thunk C) :
    PBox A δ σ αs P := by
  cases A with
  | thunk C => exact absurd rfl (h C)
  | _ => trivial

/-- **At a thunk the box reads no environment**: the `U` clause reads none. -/
theorem pBox_env {p : Placement} {η η' : Option (Nat → WEnt)} {A : VTy} {δ : LSub} {σ : LStack}
    {αs : List Life} {v : Val}
    (h : PBox A δ σ αs (fun σ' δ' αs' ls' => vRLM (ℍ := ℍ) p η σ' δ' A αs' ls' v PMap.empty)) :
    PBox A δ σ αs (fun σ' δ' αs' ls' => vRLM (ℍ := ℍ) p η' σ' δ' A αs' ls' v PMap.empty) := by
  cases A with
  | thunk C =>
      exact pBox_mono (fun σ' δ' αs' ls' hv => by rwa [vRLM_thunk_env p η' η]) h
  | _ => trivial

/-- **At a thunk the box reads no environment**, as an equation. -/
theorem pBox_env_eq (p : Placement) (η η' : Option (Nat → WEnt)) (A : VTy) (δ : LSub)
    (σ : LStack) (αs : List Life) (v : Val) :
    PBox A δ σ αs (fun σ' δ' αs' ls' => vRLM (ℍ := ℍ) p η σ' δ' A αs' ls' v PMap.empty) =
      PBox A δ σ αs (fun σ' δ' αs' ls' => vRLM (ℍ := ℍ) p η' σ' δ' A αs' ls' v PMap.empty) := by
  cases A with
  | thunk C =>
      have e : (fun σ' δ' αs' ls' => vRLM (ℍ := ℍ) p η σ' δ' (.thunk C) αs' ls' v PMap.empty) =
          (fun σ' δ' αs' ls' => vRLM (ℍ := ℍ) p η' σ' δ' (.thunk C) αs' ls' v PMap.empty) := by
        funext σ' δ' αs' ls'
        rw [vRLM_thunk_env p η η']
      rw [e]
  | _ => rfl

/-- **The box at a type that is no thunk is trivial**, as an equation. -/
theorem pBox_not_thunk_eq {A : VTy} {δ : LSub} {σ : LStack} {αs : List Life}
    {P : LStack → LSub → List Life → List SRec → Prop} (h : ∀ C, A ≠ .thunk C) :
    PBox A δ σ αs P = True := by
  cases A with
  | thunk C => exact absurd rfl (h C)
  | _ => rfl

/-! ### The fixed point's facts -/

/-- **Monotone in a variable's candidate.** W's leaves read an entry through its type only, which
agree, so the variable's candidate is read at the variable itself and at the formers that keep
the index. `vCE_mono_at`'s recursion at W's clauses. -/
theorem vRLM_mono_at (p : Placement) : ∀ (A : VTy) (k : Nat) (η₁ η₂ : Nat → WEnt), A.NoMut k →
    (∀ n, (η₁ n).ty = (η₂ n).ty) → (∀ n, n ≠ k → η₁ n = η₂ n) →
    (∀ v ρ, (η₁ k).P v ρ → (η₂ k).P v ρ) →
    ∀ σ δ αs ls v ρ, vRLM (ℍ := ℍ) p (some η₁) σ δ A αs ls v ρ →
      vRLM (ℍ := ℍ) p (some η₂) σ δ A αs ls v ρ := by
  intro A
  induction A using VTy.recV with
  | unit => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | int w => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | opq k => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | unk => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; exact h
  | thunk C =>
      intro _ η₁ η₂ _ _ _ _ σ δ αs ls v ρ h
      rw [vRLM_thunk_env p (some η₂) (some η₁)]; exact h
  | tensor A B ihA ihB =>
      intro k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ihA k η₁ η₂ hk.1 ht hP hPk σ δ αs ls v₁ ρ₁ h₁,
        ihB k η₁ η₂ hk.2 ht hP hPk σ δ αs ls v₂ ρ₂ h₂⟩
  | sum A B ihA ihB =>
      intro k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, ihA k η₁ η₂ hk.1 ht hP hPk σ δ αs ls v₁ ρ₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, ihB k η₁ η₂ hk.2 ht hP hPk σ δ αs ls v₂ ρ₂ h₂⟩
  | ref A ih =>
      intro k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, ih k η₁ η₂ hk ht hP hPk σ δ αs ls v' ρ₂ h₂⟩
  | box a A ih =>
      intro k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, ih k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ hb, ho⟩
  | bang A ih =>
      intro k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h
      exact ⟨h.1, ih k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h.2.1,
        pBox_mono (fun σ' δ' αs' ls' => ih k η₁ η₂ hk ht hP hPk σ' δ' αs' ls' v _) h.2.2⟩
  | imm a T _ =>
      intro k η₁ η₂ _ ht _ _ σ δ αs ls v ρ h
      rw [vRLM_imm_eq] at h ⊢
      rwa [wClose_congr (η := some η₁) (η' := some η₂) (fun n => (ht n).symm)]
  | «mut» a T _ =>
      intro k η₁ η₂ _ ht _ _ σ δ αs ls v ρ h
      rw [vRLM_mut_eq] at h ⊢
      rwa [wClose_congr (η := some η₁) (η' := some η₂) (fun n => (ht n).symm)]
  | tvar n =>
      intro k η₁ η₂ _ _ hP hPk σ δ αs ls v ρ h
      show (η₂ n).P v ρ
      by_cases e : n = k
      · subst e; exact hPk v ρ h
      · rw [← hP n e]; exact h
  | fam L ih =>
      intro k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h
      obtain ⟨ℓ, c, ρ₀, ρ₁, hc, hp, hs⟩ := h
      exact ⟨ℓ, c, ρ₀, ρ₁, hc, hp,
        sepRange_mono' (fun m τ hm => ih k η₁ η₂ hk ht hP hPk σ δ αs ls _ τ hm) hs⟩
  | mu A ih =>
      intro k η₁ η₂ hk ht hP hPk σ δ αs ls v ρ h
      have eM : wClose (some η₁) (.mu A) = wClose (some η₂) (.mu A) :=
        wClose_congr (η := some η₂) (η' := some η₁) ht (.mu A)
      obtain ⟨hnm, hcl, hlfp⟩ := h
      refine ⟨hnm, eM ▸ hcl, fun P hPre => hlfp P (fun v' ρ' h' => hPre v' ρ' ?_)⟩
      refine ih (k + 1) _ _ hk (fun n => ?_) (fun n hn => ?_) hPk σ δ αs ls v' ρ' h'
      · cases n with
        | zero => exact congrArg (fun T => (⟨T, P⟩ : WEnt).ty) eM
        | succ n => exact ht n
      · cases n with
        | zero => show (⟨wClose (some η₁) (.mu A), P⟩ : WEnt) = ⟨wClose (some η₂) (.mu A), P⟩; rw [eM]
        | succ n => exact hP n (fun e => hn (by rw [e]))

/-- **`VRLMMonoAt`.** -/
theorem vRLMMonoAt : VRLMMonoAt (ℍ := ℍ) := vRLM_mono_at

/-- **`roll`**: the body, its variable read at the `μ` itself, is the `μ`. `vC_roll`'s argument: for
a candidate closed under the body, the `μ` is inside it by its own definition, so the body at the
`μ` is inside the body at the candidate (`vRLM_mono_at` at `0`), which is inside the candidate. -/
theorem vRLM_roll {p : Placement} {η : Option (Nat → WEnt)} {A : VTy} {σ : LStack} {δ : LSub}
    {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes} (hA : A.NoMut 0)
    (hc : (wClose η (.mu A)).Cl 0)
    (h : vRLM (ℍ := ℍ) p (some (VTy.scons ⟨wClose η (.mu A), vRLM p η σ δ (.mu A) αs ls⟩ (wEnv η)))
      σ δ A αs ls v ρ) :
    vRLM (ℍ := ℍ) p η σ δ (.mu A) αs ls v ρ := by
  refine ⟨hA, hc, fun P hP => hP v ρ ?_⟩
  refine vRLM_mono_at p A 0 (VTy.scons ⟨wClose η (.mu A), vRLM p η σ δ (.mu A) αs ls⟩ (wEnv η))
    (VTy.scons ⟨wClose η (.mu A), P⟩ (wEnv η)) hA (fun n => by cases n <;> rfl) (fun n hn => ?_)
    (fun v' ρ' (h' : vRLM (ℍ := ℍ) p η σ δ (.mu A) αs ls v' ρ') => h'.2.2 P hP) σ δ αs ls v ρ h
  cases n with
  | zero => exact absurd rfl hn
  | succ n => rfl

/-- **`VRLMRoll`.** -/
theorem vRLMRoll : VRLMRoll (ℍ := ℍ) :=
  fun _ _ _ _ _ _ _ _ _ hA hc h => vRLM_roll hA hc h

/-! ### The thaw at a family -/

/-- **The clause over a family**: each element thawed under its part of the guard, the elements
joined by `relendJ_sep`, the empty range by `relendJ_emp`. -/
theorem relendJ_sepRange {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    {P : BoCa.Loc → WProp} {Q : BoCa.Loc → LSub → List Life → List SRec → WProp}
    (hl : αs.length = σ.length)
    (hP : ∀ m ρ, TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → P m ρ →
      RelendJ δ σ (Q m) αs ls ρ) :
    ∀ {ℓ : BoCa.Loc} {n : Nat} {ρ : WRes}, TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
      sepRange P ℓ n ρ →
      RelendJ δ σ (fun δ' αs' ls' => sepRange (fun m => Q m δ' αs' ls') ℓ n) αs ls ρ
  | _, 0, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendJ_emp hl fun _ _ _ => ⟨rfl, trivial⟩
  | ℓ, _ + 1, _, ht, hpv, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ =>
      relendJ_sep ⟨ρ₁, ρ₂, hc, hP ℓ ρ₁ (tabAtS_left hc ht) (placeViewsL_left hc hpv) h₁,
        relendJ_sepRange hl hP (tabAtS_right hc ht) (placeViewsL_right hc hpv) h₂⟩

/-! ### The thaw at `U`, at `vRLM` -/

/-- **A `U` value instantiated is a `U` value at the instantiation**, at `vRLM`: `relendJ_thunk`'s
proof. The `U` clause reads no environment, so the instantiated value is at any. -/
theorem relendM_thunk {C : CTy} {η : Option (Nat → WEnt)}
    {ηf : LSub → List Life → List SRec → Option (Nat → WEnt)} {δ : LSub} {σ : LStack}
    {αs : List Life} {ls : List SRec} {f : Val} {ρ : WRes} (ht : TabAtS σ αs ρ)
    (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ) (h : vRLM (ℍ := ℍ) .binder0 η σ δ (.thunk C) αs ls f ρ) :
    RelendJ δ σ (fun δ' αs' ls' => vRLM (ℍ := ℍ) .binder0 (ηf δ' αs' ls') σ δ' (.thunk C) αs' ls' f)
      αs ls ρ := by
  rw [vRLM_thunk0] at h
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h ht hpv
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks _ ρv τ hv hcv => ?_⟩
  beta_reduce
  rw [vRLM_thunk0]
  intro _ _
  refine ⟨ds, ρz, ρv, hcv, hv, stratS_inst ι hz,
    fun ι₂ hat₂ ls₂ he₂ hkt₂ hks₂ hro₂ ρv₂ τ₂ hv₂ hcv₂ => ?_⟩
  obtain ⟨ι₃, hat₃, hsub, hlife, hrecs⟩ := instComp αs ι ι₂ hat hat₂
  have hl₃ : ι₃.life αs = ι₂.life (ι.life αs) := by
    simp only [Inst.life, List.map_map]
    exact List.map_congr_left fun a _ => hlife a
  obtain ⟨he₃, hkt₃⟩ := ext_inst_comp hat₂ hz he hkt he₂ hkt₂
  have hks₃ := keepsSComp _ _ σ ds αs (ι.life αs) ls ls' ls' ls₂ ρn ρv ι ι₂ hn hv hks hks₂
  rw [← hrecs] at he₃ hkt₃ hks₃
  have := H ι₃ hat₃ ls₂ he₃ hkt₃ hks₃ (by rw [hl₃]; exact hro₂) ρv₂ τ₂
    (by rw [hl₃, hsub]; exact hv₂) hcv₂
  rw [hl₃, hsub] at this
  exact this

/-! ### The thaw at every type, by induction on the data -/

/-- **The thaw of a value at every type, under a thawing environment** (`RelendMValueE`). Every
case is `relendJ_valueK`'s, the leaves at their closed types (`wClose`, the conclusion's the same by
`EnvThaws`' first conjunct), except three. A variable thaws by `EnvThaws`' second conjunct. A
family thaws element by element (`relendJ_sepRange`). At `μX. A` the value is in the fixed point,
so in every candidate closed under the body; the candidate is "a `μ` value that thaws under the
guard". It is closed under the body: the first half by `vRLM_mono_at` and `vRLM_roll`; the second
by the induction hypothesis at the body, at the environment reading `X` at the candidate and the
family reading `X` at the `μ` at each instantiated index, then `vRLM_roll` there. The induction is
on the data: no fuel, no step index. -/
theorem relendM_valueE : ∀ (A : VTy) (η : Option (Nat → WEnt))
    (ηf : LSub → List Life → List SRec → Option (Nat → WEnt))
    (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes),
    EnvThaws η ηf δ σ αs ls → StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls →
    TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ → vRLM (ℍ := ℍ) .binder0 η σ δ A αs ls v ρ →
    RelendJ δ σ (fun δ' αs' ls' => vRLM (ℍ := ℍ) .binder0 (ηf δ' αs' ls') σ δ' A αs' ls' v) αs ls ρ := by
  intro A
  induction A using VTy.recV with
  | thunk C =>
      intro η ηf δ σ αs ls v ρ _ _ _ _ ht hpv h
      exact relendM_thunk ht hpv h
  | tensor A B ihA ihB =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      obtain ⟨v₁, v₂, hsep⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hsep
      have R₁ := ihA η ηf δ σ αs ls v₁ ρ₁ hE hok hob hro (tabAtS_left hc ht)
        (placeViewsL_left hc hpv) h₁
      have R₂ := ihB η ηf δ σ αs ls v₂ ρ₂ hE hok hob hro (tabAtS_right hc ht)
        (placeViewsL_right hc hpv) h₂
      exact relendJ_mono (fun _ _ _ τ hτ => ⟨v₁, v₂, pure_sep_mk rfl hτ⟩)
        (relendJ_sep ⟨ρ₁, ρ₂, hc, R₁, R₂⟩)
  | sum A B ihA ihB =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      rcases h with ⟨v₁, hsep⟩ | ⟨v₂, hsep⟩
      · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hsep
        exact relendJ_mono (fun _ _ _ τ hτ => Or.inl ⟨v₁, pure_sep_mk rfl hτ⟩)
          (ihA η ηf δ σ αs ls v₁ ρ hE hok hob hro ht hpv h₁)
      · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hsep
        exact relendJ_mono (fun _ _ _ τ hτ => Or.inr ⟨v₂, pure_sep_mk rfl hτ⟩)
          (ihB η ηf δ σ αs ls v₂ ρ hE hok hob hro ht hpv h₂)
  | bang A ih =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      obtain ⟨rfl, h₁, hB⟩ := h
      obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := ih η ηf δ σ αs ls v _ hE hok hob hro ht hpv h₁
      have hz0 := eq_empty_of_compS_left hc
      have hn0 := eq_empty_of_compS_right hc
      subst hz0 hn0
      refine ⟨ds, PMap.empty, PMap.empty, hc, hn, hz,
        fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
      have hv0 : ρv = PMap.empty := vwSW_eq_empty_inst ι hn.1 hv.1
      subst hv0
      have hτ := eq_empty_of_compS_empty hcv
      refine ⟨hτ, H ι hat ls' he hkt hks hro' PMap.empty τ hv hcv, ?_⟩
      exact pBox_env (pBox_inst hat hB)
  | box a A ih =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      obtain ⟨α, hα, hv, hout⟩ := h
      obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := ih η ηf δ σ αs ls v ρ hE hok hob hro ht hpv hv
      have hzo := (outlives_comp hc α).mp hout
      refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv' hcv => ?_⟩
      refine ⟨ι.life1 α, ?_, H ι hat ls' he hkt hks hro' ρv τ hv' hcv, ?_⟩
      · rw [extS_inst, Inst.interp_sub, hα]; rfl
      · exact (outlives_comp hcv _).mpr ⟨ResU.InStratum.mono (ι.life1_le α) hzo.1,
          vwSW_outlives_inst ι hn.1 hv'.1 hzo.2⟩
  | ref A ih =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      obtain ⟨ℓ, v', hsep⟩ := h
      obtain ⟨rfl, ρo, ρa, hc, hown, ha⟩ := pure_sep_iff.mp hsep
      obtain ⟨ds, ρz, ρn, hc', hn, hz, H⟩ :=
        ih η ηf δ σ αs ls v' ρa hE hok hob hro (tabAtS_right hc ht) (placeViewsL_right hc hpv) ha
      obtain ⟨ρz', hcz, hc''⟩ := compS_reassoc' hc' hc
      refine ⟨ds, ρz', ρn, hc'', hn, fun o ho => (outlives_comp hcz o).mpr
        ⟨by rw [hown]; exact ResU.inStratum_single_own o ℓ v', hz o ho⟩,
        fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
      obtain ⟨τa, hτa, hτ⟩ := compS_reassoc hcz hcv
      exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, τa, hτ, hown,
        H ι hat ls' (he.right hcz) (hkt.right hcz) hks hro' ρv τa hv hτa⟩⟩
  | «mut» a T _ =>
      intro η ηf δ σ αs ls v ρ hE hok _ _ ht hpv h
      rw [vRLM_mut_eq] at h
      refine relendJ_mono (fun δ' αs' ls' τ hτ => ?_) (relendJ_mutK hok ht hpv h)
      rw [vRLM_mut_eq, wClose_congr (hE.1 δ' αs' ls')]
      exact hτ
  | imm a T _ =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      rw [vRLM_imm_eq] at h
      refine relendJ_mono (fun δ' αs' ls' τ hτ => ?_) (relendJ_immK hok hob hro ht hpv h)
      rw [vRLM_imm_eq, wClose_congr (hE.1 δ' αs' ls')]
      exact hτ
  | unit =>
      intro η ηf δ σ αs ls v ρ _ hok _ _ _ _ h
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | int w =>
      intro η ηf δ σ αs ls v ρ _ hok _ _ _ _ h
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | opq k =>
      intro η ηf δ σ αs ls v ρ _ hok _ _ _ _ h
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | unk =>
      intro η ηf δ σ αs ls v ρ _ hok _ _ _ _ h
      obtain ⟨rfl, hv⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, hv⟩
  | zero =>
      intro η ηf δ σ αs ls v ρ _ _ _ _ _ _ h
      exact h.elim
  | tvar n =>
      intro η ηf δ σ αs ls v ρ hE _ _ _ ht hpv h
      exact hE.2 n v ρ ht hpv h
  | fam L ih =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      obtain ⟨ℓ, c, hsep⟩ := h
      obtain ⟨⟨rfl, hcn⟩, hs⟩ := pure_sep_iff.mp hsep
      exact relendJ_mono (fun _ _ _ τ hτ => ⟨ℓ, c, pure_sep_mk ⟨rfl, hcn⟩ hτ⟩)
        (relendJ_sepRange hok.1 (fun m ρ' ht' hpv' hm =>
          ih η ηf δ σ αs ls (.loc m) ρ' hE hok hob hro ht' hpv' hm) ht hpv hs)
  | mu A ih =>
      intro η ηf δ σ αs ls v ρ hE hok hob hro ht hpv h
      obtain ⟨hnm, hcl, hlfp⟩ := h
      -- the candidate: a `μ` value that thaws under the guard
      let P' : Val → WProp := fun v ρ => vRLM (ℍ := ℍ) .binder0 η σ δ (.mu A) αs ls v ρ ∧
        (TabAtS σ αs ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
          RelendJ δ σ (fun δ' αs' ls' => vRLM (ℍ := ℍ) .binder0 (ηf δ' αs' ls') σ δ' (.mu A) αs' ls' v)
            αs ls ρ)
      -- the family reading `X` at the `μ` at each instantiated index
      let ηf₁ : LSub → List Life → List SRec → Option (Nat → WEnt) := fun δ' αs' ls' =>
        some (VTy.scons ⟨wClose (ηf δ' αs' ls') (.mu A),
          vRLM (ℍ := ℍ) .binder0 (ηf δ' αs' ls') σ δ' (.mu A) αs' ls'⟩ (wEnv (ηf δ' αs' ls')))
      have hE₁ : EnvThaws (some (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η))) ηf₁ δ σ αs ls := by
        refine ⟨fun δ' αs' ls' n => ?_, fun n v'' ρ'' ht'' hpv'' hP => ?_⟩
        · cases n with
          | zero => exact wClose_congr (hE.1 δ' αs' ls') _
          | succ n => exact hE.1 δ' αs' ls' n
        · cases n with
          | zero => exact hP.2 ht'' hpv''
          | succ n =>
              have hP' : wEnvP η n v'' ρ'' := by rw [wEnvP_eq]; exact hP
              refine relendJ_mono (fun δ' αs' ls' τ hτ => ?_) (hE.2 n v'' ρ'' ht'' hpv'' hP')
              rw [wEnvP_eq] at hτ
              exact hτ
      have hclosed : ∀ v' ρ', vRLM (ℍ := ℍ) .binder0
          (some (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η))) σ δ A αs ls v' ρ' → P' v' ρ' := by
        intro v' ρ' h'
        refine ⟨?_, fun ht' hpv' => ?_⟩
        · refine vRLM_roll hnm hcl ?_
          refine vRLM_mono_at .binder0 A 0 (VTy.scons ⟨wClose η (.mu A), P'⟩ (wEnv η))
            (VTy.scons ⟨wClose η (.mu A), vRLM (ℍ := ℍ) .binder0 η σ δ (.mu A) αs ls⟩ (wEnv η)) hnm
            (fun n => by cases n <;> rfl) (fun n hn => ?_)
            (fun v'' ρ'' (hv : P' v'' ρ'') => hv.1) σ δ αs ls v' ρ' h'
          cases n with
          | zero => exact absurd rfl hn
          | succ n => rfl
        · refine relendJ_mono (fun δ' αs' ls' τ hτ => ?_)
            (ih _ ηf₁ δ σ αs ls v' ρ' hE₁ hok hob hro ht' hpv' h')
          exact vRLM_roll hnm (by rw [wClose_congr (hE.1 δ' αs' ls')]; exact hcl) hτ
      exact (hlfp P' hclosed).2 ht hpv

/-- **`RelendMValueE`.** -/
theorem relendMValueE : RelendMValueE (ℍ := ℍ) := relendM_valueE

/-- The empty environment thaws. -/
theorem envThaws_none (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) :
    EnvThaws none (fun _ _ _ => none) δ σ αs ls :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ h => absurd h id⟩

/-- **The thaw of a value at every type** (`RelendMValue`): `relendM_valueE` at `none`. -/
theorem relendMValue : RelendMValue (ℍ := ℍ) :=
  fun A δ σ αs ls v ρ hok hob hro ht hpv h =>
    relendM_valueE A none (fun _ _ _ => none) δ σ αs ls v ρ (envThaws_none δ σ αs ls) hok hob hro
      ht hpv h


/-! ### The context's thaw, at every context -/

/-- **The thaw of a context's slots, at every context.** -/
theorem relendM_gSep : ∀ (Γ : Ctx VTy) (γ : List Val)
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {ρ : WRes},
    StackOK σ αs → OuterBelowTop αs → RecsOutside αs ls → TabAtS σ αs ρ →
    PlaceViewsL (extS δ σ αs) σ αs ls ρ → gSepRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ →
    RelendJ δ σ (fun δ' αs' ls' => gSepRLM (ℍ := ℍ) .binder0 σ δ' αs' ls' Γ γ) αs ls ρ
  | [], _, _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, trivial⟩
  | _ :: _, [], _, _, _, _, _, hok, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendJ_emp hok.1 fun _ _ _ => ⟨rfl, trivial⟩
  | s :: Γ, v :: γ, _, _, _, _, _, hok, hob, hro, ht, hpv, h => by
      by_cases hl : s.live = true
      · simp only [gSepRLM, hl, if_true] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have R₁ := relendMValue s.ty _ _ _ _ _ _ hok hob hro (tabAtS_left hc ht)
          (placeViewsL_left hc hpv) h₁
        have R₂ := relendM_gSep Γ γ hok hob hro (tabAtS_right hc ht) (placeViewsL_right hc hpv) h₂
        exact relendJ_sep ⟨ρ₁, ρ₂, hc, R₁, R₂⟩
      · simp only [gSepRLM, hl] at h ⊢
        exact relendM_gSep Γ γ hok hob hro ht hpv h

/-- **`CtxRelendsAllM binder0`**: the context's thaw at every context. -/
theorem ctxRelendsAllM : CtxRelendsAllM (ℍ := ℍ) .binder0 := by
  intro Δ Γ δ σ αs ls γ ρ hok hob _ _ hro _ ht hpv hg
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  exact relendJ_mono (fun _ _ _ τ hτ => pure_sep_mk hlw hτ)
    (relendM_gSep Γ γ hok hob hro ht hpv hgs)

/-- **`ThawInstM binder0`.** -/
theorem thawInstM : ThawInstM (ℍ := ℍ) .binder0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ ht hpv h => relendM_thunk ht hpv h

/-! ### The `U` introductions at every context -/

theorem gRLM_dead_cons {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec} {S : VTy}
    {Γ : Ctx VTy} {v : Val} {γ : List Val} {ρ : WRes} (h : gRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ) :
    gRLM (ℍ := ℍ) .binder0 σ δ αs ls (⟨S, false⟩ :: Γ) (v :: γ) ρ := by
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp h
  exact pure_sep_mk (by simpa using hlw) (by simpa [gSepRLM] using hgs)

/-- A persistent context holds nothing, at `vRLM`. -/
theorem gSepRLM_persistent {σ : LStack} {δ : LSub} {αs : List Life} {ls : List SRec} :
    ∀ (Γ : Ctx VTy) (γ : List Val) (ρ : WRes), Persistent Γ →
    gSepRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ → ρ = PMap.empty
  | [], [], _, _, h => h.1
  | [], _ :: _, _, _, h => h.1
  | _ :: _, [], _, _, h => h.1
  | s :: Γ, v :: γ, ρ, hP, h => by
      have hP' : Persistent Γ := fun s' hs' hl => hP s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRLM, hl, if_true] at h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        obtain ⟨A, hA⟩ := hP s List.mem_cons_self hl
        rw [hA] at h₁
        have e₁ : ρ₁ = PMap.empty := h₁.1
        rw [e₁, gSepRLM_persistent Γ γ ρ₂ hP' h₂] at hc
        exact eq_empty_of_compS_empty hc
      · simp only [gSepRLM, hl] at h
        exact gSepRLM_persistent Γ γ ρ hP' h

/-- **`StackJM` at a type that is no lifetime `∀`**: its added conjunct reads an outermost `∀`. -/
theorem stackJM_of_notAll {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {C : CTy} (hJ : StackJ σ αs δ Δ Γ C) (hC : ∀ x c D, C ≠ .all x c D) :
    StackJM σ αs δ Δ Γ C :=
  ⟨hJ, fun _ _ _ _ ⟨_, _, h⟩ => absurd h (hC _ _ _)⟩

/-- **`StackJM` where every entry is of `StackJ`'s first two kinds**: an entry of the second kind is
a name no program binds, so under `BindersLow` no `∀` of the type binds it. -/
theorem stackJM_of_kinds {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {C : CTy} (hJ : StackJ σ αs δ Δ Γ C) (hBL : BindersLow Γ C)
    (hk : ∀ e ∈ σ, (∃ u, Δ.find? e.x = some u) ∨ NsVar e.x) : StackJM σ αs δ Δ Γ C := by
  refine ⟨hJ, fun e he hΔ _ ⟨c, C', hC⟩ => ?_⟩
  exfalso
  rcases hk e he with ⟨u, hu⟩ | hns
  · rw [hΔ] at hu; cases hu
  · exact hBL.1 e.x (by rw [hC]; exact List.mem_cons_self ..) hns

/-- At a type that is no lifetime `∀`, every entry `StackJ` admits is of the first two kinds. -/
theorem stackJ_kinds_of_notAll {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx}
    {Γ : Ctx VTy} {C : CTy} (hJ : StackJ σ αs δ Δ Γ C) (hC : ∀ x c D, C ≠ .all x c D) :
    ∀ e ∈ σ, (∃ u, Δ.find? e.x = some u) ∨ NsVar e.x := by
  intro e he
  rcases hJ.2.2 e he with h | ⟨hns, -⟩ | ⟨-, -, -, c, D, hall, -⟩
  · exact Or.inl h
  · exact Or.inr hns
  · exact absurd hall (hC _ _ _)

/-- **The `U` clause of `thunk M : U (F A)` at `binder0`, at `vRLM`**: `thunkF_U_of_thawJ`'s proof,
the context's thaw by `ctxRelendsAllM`. -/
theorem thunkF_U_M {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    (hM : SemSM (ℍ := ℍ) .binder0 Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)))
    (hBL : BindersLow (⟨.unit, false⟩ :: Γ) (.ret A))
    (hSc : Scoped Δ (⟨.unit, false⟩ :: Γ) (.ret A))
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs)
    (hJ : StackJ σ αs δ Δ (⟨.unit, false⟩ :: Γ) (.ret A)) (hSD : SubDom δ Δ)
    (hMod : Δ.Models (extS δ σ αs)) (hro : RecsOutside αs ls) (hso : SubOutside σ αs δ)
    (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (hg : gRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ) :
    vRLM (ℍ := ℍ) .binder0 none σ δ (.thunk (.ret A)) αs ls (.lam (Expr.psub 1 γ M)) ρ := by
  rw [vRLM_thunk0]
  intro _ _
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ :=
    ctxRelendsAllM Δ Γ δ σ αs ls γ ρ hok hob hSD hMod hro hso ht hpv hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
  obtain ⟨ht', hpv'⟩ := guardInst δ σ ds αs ls ls' ρz ρn ρ ρv τ ι hok hat hz hn hc hpv hv hcv
  have hg' := H ι hat ls' he hkt hks hro' ρv τ hv hcv
  refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← GhostEnd.substAll_cons_l]
  exact hM hBL hSc (ι.sub δ) σ (ι.life αs) ls' (Val.unit :: γ) τ (hok.inst ι)
    (outerBelowTop_inst ι hob)
    (stackJM_of_notAll (stackJInst σ αs δ Δ _ _ ι hok.1 hJ) (fun _ _ _ h => by cases h))
    (subDom_inst ι hSD)
    (instModels Δ δ σ αs ι hMod) hro' (subOutsideInst σ αs δ ι hso) ht' hpv'
    (gRLM_dead_cons hg')

/-- **The `U` clause of `thunk V : U C` at `binder0`, at `vRLM`.** -/
theorem thunkV_U_M {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy}
    (hC : C.isRet = false) (hN : SemSM (ℍ := ℍ) .binder0 Δ Γ (.val (.lam N)) (.comp C))
    (hBL : BindersLow Γ C) (hSc : Scoped Δ Γ C)
    {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes}
    (hok : StackOK σ αs) (hob : OuterBelowTop αs) (hJ : StackJ σ αs δ Δ Γ C)
    (hk : ∀ e ∈ σ, (∃ u, Δ.find? e.x = some u) ∨ NsVar e.x)
    (hSD : SubDom δ Δ) (hMod : Δ.Models (extS δ σ αs)) (hro : RecsOutside αs ls)
    (hso : SubOutside σ αs δ) (ht : TabAtS σ αs ρ) (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ)
    (hg : gRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ ρ) :
    vRLM (ℍ := ℍ) .binder0 none σ δ (.thunk C) αs ls (.lam (Expr.psub 1 γ N)) ρ := by
  rw [vRLM_thunk0]
  intro _ _
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ :=
    ctxRelendsAllM Δ Γ δ σ αs ls γ ρ hok hob hSD hMod hro hso ht hpv hg
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat ls' he hkt hks hro' ρv τ hv hcv => ?_⟩
  obtain ⟨ht', hpv'⟩ := guardInst δ σ ds αs ls ls' ρz ρn ρ ρv τ ι hok hat hz hn hc hpv hv hcv
  rw [forceE_of_not_ret hC]
  exact hN hBL hSc (ι.sub δ) σ (ι.life αs) ls' γ τ (hok.inst ι) (outerBelowTop_inst ι hob)
    (stackJM_of_kinds (stackJInst σ αs δ Δ Γ C ι hok.1 hJ) hBL hk) (subDom_inst ι hSD)
    (instModels Δ δ σ αs ι hMod) hro'
    (subOutsideInst σ αs δ ι hso) ht' hpv' (H ι hat ls' he hkt hks hro' ρv τ hv hcv)

/-- **`ThunkFRowM binder0`.** -/
theorem thunkFRowM : ThunkFRowM (ℍ := ℍ) .binder0 := by
  intro Δ Γ M A hM hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ (thunkF_U_M hM ⟨hBL.1, fun s hs hl => ?_⟩ ⟨hSc.1, fun s hs hl => ?_⟩
    hok hob (stackJ_body hJ.1 (fun _ _ _ h => by cases h) (fun _ h => h) fun _ => ctxAvoids_dead)
    hSD hMod hro hso ht hpv hg)
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl
  · rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl

/-- **`ThunkVRowM binder0`.** -/
theorem thunkVRowM : ThunkVRowM (ℍ := ℍ) .binder0 := by
  intro Δ Γ N C hC _ hN hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ ρ
  exact wpTS_val _ _ _ _ (thunkV_U_M hC hN hBL hSc hok hob
    (stackJ_body hJ.1 (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h)
    (stackJ_kinds_of_notAll hJ.1 (fun _ _ _ h => by cases h))
    hSD hMod hro hso ht hpv hg)

/-! The two `!U` introductions and `statement0UFullM` are in `R1Box.lean`: at the persistence box
their thunk is read at every instantiation and every reserved-name push, which needs the box's world
facts and the `U`-free push (`R1Mono.lean`). -/

/-! ### `GAP.md` §4's `μ` slot at W's own `μ`

`muAdjNotVRLM` (the closure `Λ. return ℓ₀`, which Core's `μ` admits at `μX. U(adjC)` by adjacency,
is no `vRLM` value there) was proved of `vRLM` at commit `5210cf1`, through the unrestricted
`relMAgreesJ` at `U(adjC)`, whose type has a lifetime `∀`. (E1) restricts `vRLM`'s `∀` clause to the
instances in scope (`NEXT.md` §3.1), so that proof no longer applies, and it is withdrawn here.
`MuAdjVRLME1` (`Nx.lean`) decides the statement after (E1). -/

end ProbeD1

end
