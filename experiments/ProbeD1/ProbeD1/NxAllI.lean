import ProbeD1.NxE1

/-!
# ProbeD1 — the `∀I` row's open cases (`NEXT.md` item 3, §3.2–§3.5)

* **The binder-named index** (§3.2). At an index whose stack names the binder `x`, `StackJM` puts the
  entry at the head, of the third kind, pushed fresh below the reading (`SubFresh`), its variable
  read by no payload type. The first conjunct's premise is at the reading extended at `x`, which
  the stack shadows: the stack reads `x` at the head either way, so the two readings of the stack
  agree everywhere (`extS_extend_shadowed`). `SubOutside` moves there (`subOutsideExtendNamed`),
  `Δ`'s models do at the extended `Δ` (the head below `b` by the third kind's `LtLife`), and the
  premise's stack meets `StackJM` (the head is now `Δ`'s). The own-lend conjunct is vacuous: the
  own push is named `x`, which the stack already names (`OwnOKI.var`).
  - `allIRowMAt0_of`: the row at one context at every index, from the three transports and the
    named one (`CtxExtendNamedMAt`).
  - `allIRowMUFree0`: the row at every context whose live slots reach no `U`, at every index.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)
open BoCa.BoLo (Step1N Head Heap Kont)

/-! ### §3.2 The binder-named index -/

/-- **`SubOutsideExtendNamed`**: at the innermost entry's variable the bindings made before it are
all of the old reading's, read above the head (`SubFresh`); every other entry's are unchanged. -/
theorem subOutsideExtendNamed : SubOutsideExtendNamed := by
  intro σ αs δ e α a hnd hh ha hsf hso e' a' hm p hp
  cases σ with
  | nil => cases hh
  | cons e₀ σ₀ =>
      cases αs with
      | nil => cases ha
      | cons a₀ αs₀ =>
          obtain rfl : e₀ = e := Option.some.inj hh
          obtain rfl : a₀ = a := Option.some.inj ha
          by_cases hx : e₀.x = e'.x
          · -- the head's variable: `e'` is the head
            have he' : e' = e₀ ∧ a' = a₀ := by
              rcases (by simpa [List.zip_cons_cons] using hm :
                  (e' = e₀ ∧ a' = a₀) ∨ (e', a') ∈ σ₀.zip αs₀) with h | h
              · exact h
              · exfalso
                have hmem : e'.x ∈ σ₀.map LEnt.x := List.mem_map_of_mem (List.of_mem_zip h).1
                rw [List.map_cons, List.nodup_cons] at hnd
                exact hnd.1 (hx ▸ hmem)
            obtain ⟨rfl, rfl⟩ := he'
            rw [boundBefore_extend_self] at hp
            exact hsf p hp
          · rw [boundBefore_extend_ne hx] at hp
            exact hso e' a' hm p hp

/-- **The stack's reading at a binding of one of its variables is unchanged**: the stack reads that
variable itself. -/
theorem extS_extend_shadowed (δ : LSub) {x : LifeVar} (α : Life) :
    ∀ (σ : LStack) (αs : List Life), αs.length = σ.length → x ∈ σ.map LEnt.x →
      ∀ y, (extS (δ.extend x α) σ αs).find? y = (extS δ σ αs).find? y
  | [], _, _, hx, _ => by simp at hx
  | _ :: _, [], hl, _, _ => by simp at hl
  | e :: σ, a :: αs, hl, hx, y => by
      show ((extS (δ.extend x α) σ αs).extend e.x a).find? y = ((extS δ σ αs).extend e.x a).find? y
      by_cases hey : e.x = y
      · subst hey; rw [find?_extend_self, find?_extend_self]
      · rw [find?_extend_ne _ _ hey, find?_extend_ne _ _ hey]
        by_cases hxe : e.x = x
        · subst hxe
          exact extS_find_base (find?_extend_ne δ α hey) σ αs
        · have hx' : x ∈ σ.map LEnt.x := by
            rw [List.map_cons, List.mem_cons] at hx
            rcases hx with h | h
            · exact absurd h.symm hxe
            · exact h
          exact extS_extend_shadowed δ α σ αs (by simpa using hl) hx' y

/-- **`StackJ` at the first conjunct's premise, the binder naming the head**: the head is `Δ`'s at
the extended `Δ`; every other entry keeps its kind, a second-kind entry's name being no `∀` of the
body's under `BindersLow`. With the kinds it reads, for `StackJM`. -/
theorem stackJ_allNamed {e : LEnt} {σ₀ : LStack} {αs : List Life} {δ δ' : LSub} {Δ : LifeCtx}
    {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life} {C : CTy} {S : VTy}
    (h : StackJ (e :: σ₀) αs δ Δ Γ (.all x b C)) (hex : e.x = x) :
    StackJ (e :: σ₀) αs δ' (Δ.extend x b) (⟨S, false⟩ :: Γ) C ∧
      ∀ e' ∈ e :: σ₀, (∃ u, (Δ.extend x b).find? e'.x = some u) ∨ NsVar e'.x := by
  have hnd := h.1
  have hne : ∀ e' ∈ σ₀, e'.x ≠ x := by
    intro e' he' hx
    rw [List.map_cons, List.nodup_cons] at hnd
    exact hnd.1 (hex ▸ hx ▸ List.mem_map_of_mem he')
  have hkinds : ∀ e' ∈ e :: σ₀, (∃ u, (Δ.extend x b).find? e'.x = some u) ∨
      (NsVar e'.x ∧ (Δ.extend x b).find? e'.x = none ∧ ¬ CFree e'.x C ∧
        CtxAvoids e'.x (⟨S, false⟩ :: Γ)) := by
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact Or.inl ⟨b, by rw [hex, LifeCtx.find?_extend, if_pos rfl]⟩
    · have hx' := hne e' he'
      rcases h.2.2 e' (List.mem_cons_of_mem _ he') with ⟨u, hu⟩ | ⟨hns, hΔ, hCe, hctx⟩ |
          ⟨-, hhd, -⟩
      · exact Or.inl (lifeCtx_find?_extend_some hu x b)
      · refine Or.inr ⟨hns, ?_, fun hc => hCe (Or.inr ⟨hx', hc⟩), ctxAvoids_dead hctx⟩
        rw [LifeCtx.find?_extend, if_neg (Ne.symm hx')]; exact hΔ
      · exfalso
        obtain rfl : e = e' := Option.some.inj hhd
        rw [List.map_cons, List.nodup_cons] at hnd
        exact hnd.1 (List.mem_map_of_mem he')
  refine ⟨⟨hnd, fun e' he' y hy => ?_, fun e' he' => ?_⟩, fun e' he' =>
    (hkinds e' he').imp id (fun h => h.1)⟩
  · rcases h.2.1 e' he' y hy with ⟨u, hu⟩ | hm
    · exact Or.inl (lifeCtx_find?_extend_some hu x b)
    · exact Or.inr hm
  · rcases hkinds e' he' with h₁ | h₂
    · exact Or.inl h₁
    · exact Or.inr (Or.inl h₂)

/-- **`[allI]` at `binder0` at one context, at every index**: `allIRowMNKAt0_of` where the stack
does not name the binder; where it does, the first conjunct by the premise at the reading extended
at the binder, which the stack shadows (`CtxExtendNamedMAt` moves the context there), and the
own-lend conjunct vacuous. -/
theorem allIRowMAt0_of (Γ : Ctx VTy) (hMono : MonoOwnGMAt (ℍ := ℍ) .binder0 Γ)
    (hExt : CtxExtendMAt (ℍ := ℍ) .binder0 Γ) (hSh : CtxShadowMAt (ℍ := ℍ) .binder0 Γ)
    (hNamed : CtxExtendNamedMAt (ℍ := ℍ) .binder0 Γ) : AllIRowMAt (ℍ := ℍ) .binder0 Γ := by
  intro Δ x b M S C hbx hΔx hΓx hΔ hΓb hM hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso
    ht hpv hg
  change BindersLow Γ (.all x b C) at hBL
  change Scoped Δ Γ (.all x b C) at hSc
  change StackJM σ αs δ Δ Γ (.all x b C) at hJ
  by_cases hxσ : x ∈ σ.map LEnt.x
  swap
  · exact allIRowMNKAt0_of Γ hMono hExt hSh Δ x b M S C hbx hΔx hΓx hΔ hΓb hM hBL hSc δ σ αs ls
      γ ρ hxσ hok hob hJ.1 hSD hMod hro hso ht hpv hg
  -- the stack names the binder: the entry is the head, of the third kind
  obtain ⟨e, he, hex⟩ := List.mem_map.mp hxσ
  have hthird : σ.head? = some e ∧ CtxFresh e.x Γ ∧
      ∀ a ∈ αs.head?, LtLife (extS δ σ αs) b a := by
    rcases hJ.1.2.2 e he with ⟨u, hu⟩ | ⟨hns, -⟩ | ⟨-, hhd, hfr, c, C', hall, -, hlt⟩
    · rw [hex, hΔ] at hu; cases hu
    · exact absurd hns (hBL.1 e.x (by rw [hex]; exact List.mem_cons_self ..))
    · obtain ⟨rfl, rfl, rfl⟩ : x = e.x ∧ b = c ∧ C = C' := by simpa using hall
      exact ⟨hhd, hfr, hlt⟩
  obtain ⟨hhd, hfr, hlt⟩ := hthird
  have hxe : e.x = x := hex
  have hextra := hJ.2 e he (by rw [hxe]; exact hΔ) hhd ⟨b, C, by rw [hxe]⟩
  cases σ with
  | nil => cases he
  | cons e₀ σ₀ =>
  obtain rfl : e₀ = e := Option.some.inj hhd
  cases αs with
  | nil => exact absurd hok.1 (by simp)
  | cons a αs₀ =>
  have hsf : SubFresh δ a := hextra.1 a rfl
  have hBL' := bindersLow_allBody (S := S) hBL
  have hSc' := scoped_allBody (S := S) hSc
  show cRLM .binder0 (e₀ :: σ₀) δ (.all x b C) (a :: αs₀) ls (.val (.lam (Expr.psub 1 γ M))) ρ
  intro ls' σ' αs' hE hF _
  have hE' : ls' = ls := by simpa [ExtQ, Placement.bindFut] using hE
  have hF' : σ' = e₀ :: σ₀ ∧ αs' = a :: αs₀ := by simpa [FutQI, Placement.bindFut] using hF
  obtain ⟨rfl, rfl⟩ := hF'
  subst hE'
  refine ⟨fun α ρ₁ ρ₂ hp hc ht' hpv' => ?_, fun _ en α' hpush _ _ _ _ => ?_⟩
  · -- the first conjunct
    obtain ⟨rfl, -, hin⟩ := hp
    rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ)] at ht' hpv' ⊢
    refine cRLM_step .binder0 C (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) _
      (δ.extend x α) _ ls' ρ ?_
    rw [← GhostEnd.substAll_cons_l]
    obtain ⟨hJ', hk⟩ := stackJ_allNamed (δ' := δ.extend x α) (S := S) hJ.1 hxe
    have hagree := extS_extend_shadowed δ α (e₀ :: σ₀) (a :: αs₀) hok.1 hxσ
    have hMod' : (Δ.extend x b).Models (extS (δ.extend x α) (e₀ :: σ₀) (a :: αs₀)) := by
      refine GhostEnd.models_congr (δ₁ := extS δ (e₀ :: σ₀) (a :: αs₀)) ?_ (fun y => (hagree y).symm)
      intro y u hy
      rw [LifeCtx.find?_extend] at hy
      split at hy
      · rename_i hyx
        subst hyx
        obtain rfl : b = u := Option.some.inj hy
        obtain ⟨β, hβ, hαβ⟩ := hlt a rfl
        refine ⟨OrderDual.ofDual a, β, ?_, hβ, hαβ⟩
        show ((extS δ σ₀ αs₀).extend e₀.x a).find? x = _
        rw [hxe, find?_extend_self]; rfl
      · exact hMod y u hy
    exact hM hBL' hSc' (δ.extend x α) (e₀ :: σ₀) (a :: αs₀) ls' (Val.unit :: γ) ρ hok hob
      (stackJM_of_kinds hJ' hBL' hk) (subDom_extend hSD x α b) hMod' hro
      (by rw [← hxe]; exact subOutsideExtendNamed _ _ δ e₀ α a hok.2.2 rfl rfl hsf hso) ht' hpv'
      (gRLM_dead_cons (by rw [← hxe]; exact hNamed _ δ γ _ ls' ρ e₀ α hok rfl hin hfr hg))
  · -- the own-lend conjunct: the own push is named `x`, which the stack names
    obtain ⟨⟨x', c', C', hall, hex', -, hoi, -, -⟩, -, -⟩ := hpush
    obtain ⟨rfl, -, -⟩ : x = x' ∧ b = c' ∧ C = C' := by simpa using hall
    exact absurd (hex' ▸ hxσ) hoi.var

/-- **`CtxExtendNamedMAt` at a context reaching no `U`**: the stack reads the head's variable
itself, so the two readings agree everywhere (`extS_extend_shadowed`). -/
theorem ctxExtendNamedMAt_uFree (p : Placement) (Γ : Ctx VTy)
    (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty) : CtxExtendNamedMAt (ℍ := ℍ) p Γ := by
  intro σ δ γ αs ls ρ e α hok hhd _ _ hg
  have hx : e.x ∈ σ.map LEnt.x := by
    cases σ with
    | nil => cases hhd
    | cons e₀ σ₀ => obtain rfl : e₀ = e := Option.some.inj hhd; exact List.mem_cons_self ..
  have hag : ∀ y, (extS δ σ αs).find? y = (extS (δ.extend e.x α) σ αs).find? y :=
    fun y => (extS_extend_shadowed δ α σ αs hok.1 hx y).symm
  exact gRLM_reading_uFree p hU (fun _ _ _ y _ => hag y) (fun _ _ y _ => hag y) hg

/-- **`[allI]` at `binder0` at every context whose live slots reach no `U`, at every index**
(target (3a)): `allIRowMAt0_of` with the four transports at such a context. -/
theorem allIRowMUFree0 (Γ : Ctx VTy) (hU : ∀ s ∈ Γ, s.live = true → UFreeM s.ty) :
    AllIRowMAt (ℍ := ℍ) .binder0 Γ :=
  allIRowMAt0_of Γ (monoOwnGMAt_uFree .binder0 Γ hU) (ctxExtendMAt_uFree .binder0 Γ hU)
    (ctxShadowMAt_uFree .binder0 Γ hU) (ctxExtendNamedMAt_uFree .binder0 Γ hU)

/-! ### §3.3 The reading transports: where `VRLMReadEquiv`'s route stops

`VRLMReadEquiv`'s route carries `ReadEquiv` through every clause of `vRLM` (`NEXT.md` §3.3). At the
`F_Σ` clause the continuation of a stop is owed at a re-lend of the ghost-ended entries (`openFS`),
which moves the stack's lifetimes and not the base readings. `ReadEquiv`'s in-scope conjunct is not
kept there: a base reading that binds a fresh variable to one of the stack's lifetimes has that
value in scope at every re-lend, while the stack itself no longer reads it
(`not_readEquivRelend`). This is a fact about our `ReadEquiv`, at a configuration not shown to
arise; it shows only that the planned route does not pass the `F_Σ` clause. I have not derived
`VRLMReadEquiv` and have not verified that any obstruction to it is real. -/

/-- **`ReadEquiv` along a re-lend of the stack**: the step `VRLMReadEquiv`'s `F_Σ` case takes at
`openFS`'s re-lend. -/
def ReadEquivRelend : Prop :=
  ∀ (X : LifeVar → Prop) (σ : LStack) (αs αs' : List Life) (δ₁ δ₂ : LSub),
    StackOK σ αs → StackOK σ αs' → ReadEquiv X σ αs δ₁ δ₂ → ReLend αs' αs →
    ReadEquiv X σ αs' δ₁ δ₂

/-- **`ReadEquivRelend` fails**: at the stack `['0 ↦ 1]`, the readings `∅` and `'5 ↦ 1` are
equivalent off `'5` (both read `1` in scope, the stack's own lifetime), and at the re-lend `[2]` the
second still reads `1` in scope and the first does not. -/
theorem not_readEquivRelend : ¬ ReadEquivRelend := by
  intro h
  have hok : ∀ a : Life, StackOK [(⟨0, 0, .unit, .mut, fun _ => true⟩ : LEnt)] [a] :=
    fun a => ⟨rfl, List.isChain_singleton _, List.nodup_singleton _⟩
  have hRE : ReadEquiv (· = 5) [⟨0, 0, .unit, .mut, fun _ => true⟩] [lifeN 1] ⟨[]⟩ ⟨[(5, 1)]⟩ := by
    refine ⟨fun y hy => ?_, fun α => ?_, fun a ha => ?_⟩
    · have : (5 : LifeVar) ≠ y := fun h => hy h.symm
      simp [LSub.find?, Lifetime.assocFind, this]
    · constructor
      · rintro ⟨q, hq, hqα⟩
        exact ⟨q, List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hq)), hqα⟩
      · rintro ⟨q, hq, hqα⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨_, List.mem_singleton_self _, hqα⟩
        · obtain rfl := List.mem_singleton.mp hq
          exact ⟨_, List.mem_singleton_self _, hqα⟩
    · constructor
      · intro _ p hp
        simp only [List.mem_singleton] at hp
        subst hp
        exact ha (lifeN 1) rfl
      · intro _ p hp
        simp at hp
  have := h (· = 5) _ [lifeN 1] [lifeN 2] ⟨[]⟩ ⟨[(5, 1)]⟩ (hok _) (hok _) hRE
    ⟨List.Forall₂.cons (by decide) List.Forall₂.nil, List.isChain_singleton _⟩
  obtain ⟨q, hq, hqα⟩ := (this.2.1 (lifeN 1)).mpr
    ⟨(5, 1), List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩
  obtain rfl := List.mem_singleton.mp hq
  exact absurd hqα (by decide)

end ProbeD1

end
