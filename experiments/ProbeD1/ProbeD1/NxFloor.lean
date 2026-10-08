import ProbeD1.NxHide

/-!
# ProbeD1 — the floor for persistent values (`NEXT.md` §10)

The corrections of 2026-10-08 set a floor: ordinary closures, higher-order functions and borrows
without suspension are proved in Core (`fundamentalC` at `σ = []`), the draft relation must
reproduce that, and a persistent resource-free value must be carried across a lend push by
construction. This file records what (E1) left, what the relation before (E1) already lacked, and
what the persistence box (`PBox`, `R1.lean`; `R1Box.lean`) gives.

* **What (E1) leaves at the top level** (`inScope_top_none`): at the empty stack and the empty
  reading no lifetime is in scope, so the `∀` clause's first conjunct reads no instance there. A
  value made at the top level was checked by its own pushes alone.
* **Before the box the relation carried no persistent value across a push, (E1) or not**
  (`gdBangJ`): at `vRLJ`, the relation before (E1), the persistent closure `!gdTy` over `gdF` is
  related at `gd`'s stack and not after the own lend's push. `gdTy` has no lifetime `∀`, so (E1)
  plays no part. `gd` is not shown to arise and `gdF` is no Core value: this is a fact about the
  draft relation, which reverting (E1) does not change.
* **With the box a persistent thunk is carried by construction** (`persistentBoxWorld`,
  `persistentPushN`): to every instantiation, every list and every own push under a reserved name,
  in any order. A context of persistent thunks and persistent data reaching no `U` is carried across
  such a push (`monoOwnGMAtBoxN`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-! ### What (E1) leaves at the top level -/

/-- **At the empty stack and the empty reading no lifetime is in scope**: under (E1) the `∀`
clause's first conjunct reads no instance at a top-level index, and the own lends are the only
readings a value made there is checked at. -/
theorem inScope_top_none (α : Life) : ¬ InScope (extS (⟨[]⟩ : LSub) [] []) α := by
  rintro ⟨p, hp, -⟩
  simp [extS] at hp

/-! ### Before the box -/

/-- `gdTy` has no `μ`, `fam`, type variable, lifetime `∀` or persistent thunk. -/
theorem gdTy_free : VMuFree gdTy ∧ VAllFree gdTy ∧ VBoxFree gdTy := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [VMuFree, CMuFree, VAllFree, CAllFree, VBoxFree, CBoxFree]

/-- **At `vRLJ`, the relation before (E1) and before the box, a persistent resource-free closure is
related at a stack and not after the own lend's push**: `gdF` at `!gdTy` (`gdRelated`,
`gdNotPushed`, read at `vRLJ` by `relMAgreesJ`). The push is `gdIndex`'s own lend. `gdTy` has no
lifetime `∀`, so (E1) is not what fails here. A fact about the draft relation, at a configuration
not shown to arise, whose closure is no Core value (`gdNotCore`). -/
theorem gdBangJ :
    vRLJ (ℍ := ℍ) .binder0 gdσ gdδ (.bang gdTy) gdαs gdls gdF PMap.empty ∧
      ¬ vRLJ (ℍ := ℍ) .binder0 (gdY :: gdσ) gdδ (.bang gdTy) (lifeN 4 :: gdαs) gdls gdF
        PMap.empty := by
  obtain ⟨h1, h2, h3⟩ := gdTy_free
  have eq : ∀ (σ : LStack) (αs : List Life),
      vRLM (ℍ := ℍ) .binder0 none σ gdδ gdTy αs gdls gdF =
        vRLJ (ℍ := ℍ) .binder0 σ gdδ gdTy αs gdls gdF :=
    fun σ αs => relMAgreesJ.1 .binder0 σ gdδ gdTy αs gdls gdF h1 h2 h3
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp (gdRelated (ℍ := ℍ))
  constructor
  · refine ⟨rfl, ?_⟩
    simp only [gSepRLM, if_true] at hgs
    obtain ⟨ρ₁, ρ₂, hc, h₁, -⟩ := hgs
    have e₁ := eq_empty_of_compS_left hc
    subst e₁
    rw [← eq]
    exact h₁
  · rintro ⟨-, h⟩
    rw [← eq] at h
    refine gdNotPushed (ℍ := ℍ) (pure_sep_mk hlw ?_)
    simp only [gSepRLM, if_true]
    exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, h, rfl, trivial⟩

/-! ### With the box -/

/-- **A persistent thunk at every world of the box, by construction**: every instantiation, every
list kept outside, every sequence of own pushes under reserved names from there. -/
theorem persistentBoxWorld {C : CTy} {σ σ' : LStack} {δ : LSub} {αs αs' : List Life}
    {ls ls' : List SRec} {v : Val} {ρ : WRes} {ι : Inst} (hok : StackOK σ αs)
    (h : vRLM (ℍ := ℍ) .binder0 none σ δ (.bang (.thunk C)) αs ls v ρ) (hat : InstAt αs ι)
    (hro : RecsOutside (ι.life αs) ls')
    (hst : Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs')) :
    vRLM (ℍ := ℍ) .binder0 none σ' (ι.sub δ) (.bang (.thunk C)) αs' ls' v ρ := by
  obtain ⟨rfl, -, hbox⟩ := h
  exact ⟨rfl, hbox ι hat ls' hro σ' αs' hst, pBox_world hok hbox hat hst⟩

/-- **The floor at a persistent thunk: carried across an own push under a reserved name, by
construction.** -/
theorem persistentPushN {C : CTy} {σ σ' : LStack} {δ : LSub} {αs αs' : List Life}
    {ls : List SRec} {v : Val} {ρ : WRes} (hok : StackOK σ αs) (hro : RecsOutside αs ls)
    (hst : BoxStep δ ls (σ, αs) (σ', αs'))
    (h : vRLM (ℍ := ℍ) .binder0 none σ δ (.bang (.thunk C)) αs ls v ρ) :
    vRLM (ℍ := ℍ) .binder0 none σ' δ (.bang (.thunk C)) αs' ls v ρ := by
  have hl : Inst.life none αs = αs := Inst.life_none αs
  exact persistentBoxWorld (ι := none) hok h (fun _ _ h => by cases h) (by rw [hl]; exact hro)
    (by rw [hl]; exact Relation.ReflTransGen.single hst)

/-- **`MonoOwnGM` at a context the box carries, across an own push under a reserved name**: the
context is persistent, so it holds nothing; a persistent thunk crosses by the box
(`persistentPushN`), persistent data reaching no `U` by the `U`-free push (`monoOwnUFree_go`). -/
def MonoOwnGMAtBoxN (p : Placement) (Γ : Ctx VTy) : Prop :=
  ∀ (σ : LStack) (δ : LSub) (γ : List Val) (αs : List Life) (ls : List SRec) (ρ : WRes)
    (e : LEnt) (a : Life),
    Persistent Γ → PersistentBoxed Γ → CtxFresh e.x Γ → StackPayAvoids e.x σ →
    StackOK σ αs → RecsOutside αs ls → BoxStep δ ls (σ, αs) (e :: σ, a :: αs) →
    gRLM (ℍ := ℍ) p σ δ αs ls Γ γ ρ → gRLM (ℍ := ℍ) p (e :: σ) δ (a :: αs) ls Γ γ ρ

/-- **`MonoOwnGMAtBoxN` at `binder0`, at every context.** -/
theorem monoOwnGMAtBoxN (Γ : Ctx VTy) : MonoOwnGMAtBoxN (ℍ := ℍ) .binder0 Γ := by
  intro σ δ γ αs ls ρ e a hP hPB hfr hσ hok hro hst hg
  have hρ : ρ = PMap.empty := gSepRLM_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  subst hρ
  obtain ⟨e', a', he, hoi, -, -, -, -, -, hsf⟩ := boxStep_inv hst
  simp only [Prod.mk.injEq, List.cons.injEq] at he
  obtain ⟨⟨rfl, -⟩, rfl, -⟩ := he
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  refine pure_sep_mk hlw ?_
  have key : ∀ (Γ : Ctx VTy) (γ : List Val), PersistentBoxed Γ → CtxFresh e.x Γ →
      gSepRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ PMap.empty →
      gSepRLM (ℍ := ℍ) .binder0 (e :: σ) δ (a :: αs) ls Γ γ PMap.empty := by
    intro Γ
    induction Γ with
    | nil => intro γ _ _ h; cases γ <;> exact h
    | cons s Γ ih =>
        intro γ hPB' hfr' h
        cases γ with
        | nil => exact h
        | cons v γ =>
            have hPB'' : PersistentBoxed Γ :=
              fun s' hs' hl => hPB' s' (List.mem_cons_of_mem _ hs') hl
            have hfr'' : CtxFresh e.x Γ := fun s' hs' hl => hfr' s' (List.mem_cons_of_mem _ hs') hl
            by_cases hl : s.live = true
            · simp only [gSepRLM, hl, if_true] at h ⊢
              obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
              have e₁ := eq_empty_of_compS_left hc
              have e₂ := eq_empty_of_compS_right hc
              subst e₁ e₂
              refine ⟨PMap.empty, PMap.empty, hc, ?_, ih γ hPB'' hfr'' h₂⟩
              obtain ⟨B, hBt, hB⟩ := hPB' s List.mem_cons_self hl
              have hxB := hfr' s List.mem_cons_self hl
              rw [hBt] at h₁ hxB ⊢
              rcases hB with ⟨C, rfl⟩ | hu
              · exact persistentPushN hok hro hst h₁
              · refine ⟨rfl, ?_, pBox_of_not_thunk fun C hC => by subst hC; exact hu⟩
                exact monoOwnUFree_go .binder0 e a B none none σ δ αs ls v PMap.empty hu
                  (envPushNone σ δ αs ls e a) hok hoi.chain hsf hσ hxB.1
                  ⟨tab_empty _ _, placeViewsL_empty, hoi.placeFree, ResU.inStratum_empty _⟩ h₁.2.1
            · simp only [gSepRLM, hl] at h ⊢
              exact ih γ hPB'' hfr'' h
  exact key Γ γ hPB hfr hgs

/-! ### What the `∀I` row needs beside the box at a persistent context

The `∀` clause's own lend names its entry by the type's binder, which is no reserved name, so the
box does not reach the row's push directly. The row's push differs from a box step only in the
entry's name. The statement below says the relation does not read that name; it is stated and not
derived here. The row's two reading transports (`CtxExtendMSAt`, `CtxShadowMSAt`, `Nx.lean`) are
the other step: the box's pushes may read a variable the extended reading binds, so they move with
the reading as well. -/

/-- An entry with its payload type's variable `x` read as `y`. -/
def renEnt (x y : LifeVar) (e : LEnt) : LEnt := { e with T := e.T.applyLSub [(x, .var y)] }

/-- **The relation does not read the name of a stack entry that nothing in sight reads**: renaming
the entry's variable `x` to `y`, and `x` to `y` in the payload types of the entries pushed after it,
leaves `vRLM` as it is, when neither name is read or bound by the type or read by the reading, `y`
is new to the stack and to every payload type, and `x` is read by no payload type at or below the
entry. With `persistentPushN` it gives the `∀I` row's own push at a context the box carries. Not
derived here. -/
def VRLMStackRename : Prop :=
  ∀ (A : VTy) (σ₁ σ₂ : LStack) (e : LEnt) (y : LifeVar) (δ : LSub) (αs : List Life)
    (ls : List SRec) (v : Val) (ρ : WRes),
    ¬ VFree e.x A → e.x ∉ VTy.binders A → ¬ VFree y A → y ∉ VTy.binders A →
    δ.find? e.x = none → δ.find? y = none →
    e.x ∉ (σ₁ ++ σ₂).map LEnt.x → y ∉ (σ₁ ++ e :: σ₂).map LEnt.x →
    (∀ e' ∈ σ₁ ++ e :: σ₂, ¬ VFree y e'.T) → (∀ e' ∈ e :: σ₂, ¬ VFree e.x e'.T) →
    αs.length = (σ₁ ++ e :: σ₂).length →
    (vRLM (ℍ := ℍ) .binder0 none (σ₁ ++ e :: σ₂) δ A αs ls v ρ ↔
      vRLM (ℍ := ℍ) .binder0 none (σ₁.map (renEnt e.x y) ++ { e with x := y } :: σ₂) δ A αs ls v ρ)

end ProbeD1

end
