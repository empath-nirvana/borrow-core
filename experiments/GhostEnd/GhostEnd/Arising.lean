import GhostEnd.Below

/-!
# GhostEnd — D16.1 with the table as a guard at `U`, `⊸` and `∀` (#279)

`Below.lean` refutes GFP (D16.2) over D16.1 at the stack `[x]` (`not_gfpAt_below`). This file
asks whether that configuration arises, and restates D16.1 with the arising restriction that
`GFPAt` already carries (`TabAtS`) applied at every clause that receives a resource from outside.

## Whether the witness arises

It does not, at the stack `[x]`.

* **The witness fails the table.** The argument the refutation hands the function is the inner
  view `k ↦ M_{αy}`, a borrow cell away from the stack's place at a lifetime below the stack's
  lend. It is not consistent with the table at `[x]` (`not_tabAtS_innerView`), and neither is any
  resource it is a part of (`not_tabAtS_of_part`).
* **What arises at `[x]` is consistent with the table.** The callback of `x`'s lend starts from a
  resource consistent with the table (`tabAtS_start_one`, from `tabAt_start`), every run keeps it,
  at a return as at a stop (`wpG_tabAtS_one`, from `wpG_tabAt`, `[TR]` 6.50), and so does every
  part of what it reaches (`tabAtS_comp`).
* So no run at the stack `[x]` reaches a state of which the inner view is a part
  (`wpG_below_not_arises`). The view `k ↦ M_{αy}` exists only inside an inner lend of `k`, where
  the stack is `[y, x]` and the cell is that stack's own view (`tabAtS_innerView_inner`).

## The restatement

`guardS σ αs P` asks `P` of a resource only when it is consistent with the table at the stack.
`vRLa`/`cRLa`/`effRetA` are D16.1 (`vRLs`/`cRLs`/`effRetS`) with that guard at the three clauses
that hand the relation a resource it did not build:

* `U C`: the clause (`RelendableS`) under the guard, #266's change 3 at the stack;
* `A ⊸ C`: the argument's resource joined to the function's, and the result under the guard;
* `∀'x ⊏ c. C`: the instance under the guard.

Every other clause, and every stack component (`RelendableS`, `OpenS`, `bodyS`, `stopS`), is
D16.1's own definition, unchanged. `GFPAtA` is `GFPAt` at the restated relation: the same
hypotheses, `TabAtS` among them.

## What is proved

* **`σ = []`**: the table at the empty stack holds of every resource, so the guard vanishes:
  `vRLa [] = vC`, `cRLa [] = cC`, `gRLa [] = gDenC` (`vRLa_nil`, `cRLa_nil`, `gRLa_nil`), and
  `GFPAtA [] ↔` the fundamental property (`gfpAtA_nil_iff`); `GFPAtA []` holds (`gfpAtA_nil`).
* **The stack results carry over.** `cRLa` at `F_Σ R` is D16.1's piece itself (`cRLa_eff`), so
  every result of `StackStep.lean` and the `withbor` rows of `Stacked.lean`, which are stated over
  `OpenS`/`bodyS` at an arbitrary answer relation, apply to it verbatim. The `U`-clause rows are
  restated: `force_RLa` (the guard discharged by `GFPAt`'s table), `relendableS_thunkA`,
  `thunkF_RLa`, `thunkE_RLa`.
* **Elimination is not weakened.** At `app` and `allE` the joined resource is the context's, which
  `GFPAt` assumes consistent with the table (`arr_elimA`, `all_elimA`).
* **The rows `lam` and `allI`** at the restated relation (`lam_RLa`, `allI_RLa`). Each guard is
  the table at the resource the body's judgment starts from, which is what `GFPAt` assumes.
  `allI` takes two added hypotheses: its variable is not a stack variable and is free in no stack
  payload type. Both follow from the presupposed rule's freshness (`stackFresh_of_fresh`,
  `stackTyFresh_of_fresh`). Its proof needs D16.1 to read `δ` only at the type's and the stack's
  variables (`vRLa_congr`, `cRLa_congr`), as the kernel's `allI_compatC` uses `vC_congr`.
* **The refuted configuration is excluded by the guard** (`below_excluded`, `below_excluded_at`):
  at the restated relation the `⊸` clause asks nothing of the inner view.

## What this does not settle

The guard at `⊸` also means that a callback read at `σ` is obliged on no argument holding a cell
below the stack (`below_excluded` holds at every expression). A borrow constant at `σ` hands its
callback a view at a fresh lifetime below the stack, so its row (#275) cannot take the callback's
behaviour on that view from the callback's reading at `σ`. It has to take it at `σ·y`. Whether
that is reachable with the existing machinery is not part of this file. I have not derived it and
have not verified that any obstruction is real.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The table at a stack: parts, one entry, the start of a lend -/

/-- **Parts and whole.** The table at a stack holds of a composite iff it holds of both parts. -/
theorem tabAtS_comp {σ : LStack} {αs : List Life} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) :
    TabAtS σ αs ρ ↔ (TabAtS σ αs ρ₁ ∧ TabAtS σ αs ρ₂) := by
  constructor
  · rintro ⟨hd, ho⟩
    refine ⟨⟨fun a ha => ((outlives_comp hc (↓a)).mp (hd a ha)).1,
        fun a ha k ψ hk e => ResU.CompS.inStratum_left_at hc (fun φ f => ho a ha k φ hk f) e⟩,
      ⟨fun a ha => ((outlives_comp hc (↓a)).mp (hd a ha)).2,
        fun a ha k ψ hk e => ResU.CompS.inStratum_right_at hc (fun φ f => ho a ha k φ hk f) e⟩⟩
  · rintro ⟨⟨hd₁, ho₁⟩, ⟨hd₂, ho₂⟩⟩
    exact ⟨fun a ha => (outlives_comp hc (↓a)).mpr ⟨hd₁ a ha, hd₂ a ha⟩, fun a ha k ψ hk e =>
      ResU.inStratum_comp_at (CellU.compS_hC a) hc (fun φ f => ho₁ a ha k φ hk f)
        (fun φ f => ho₂ a ha k φ hk f) e⟩

/-- A resource inconsistent with the table makes every resource it is a part of inconsistent. -/
theorem not_tabAtS_of_part {σ : LStack} {αs : List Life} {ρ₁ ρ₂ ρ : WRes}
    (hc : ResU.CompS ρ₁ ρ₂ ρ) (h : ¬ TabAtS σ αs ρ₁) : ¬ TabAtS σ αs ρ :=
  fun ht => h ((tabAtS_comp hc).mp ht).1

/-- **At one entry the table at the stack is #262's `TabAt`.** -/
theorem tabAtS_one {e : LEnt} {α : Life} {ρ : WRes} : TabAtS [e] [α] ρ ↔ TabAt e.l α ρ := by
  constructor
  · rintro ⟨hd, ho⟩
    exact ⟨hd α rfl, fun k ψ hk g => ho α rfl k ψ (by simpa using hk) g⟩
  · rintro ⟨hd, ho⟩
    refine ⟨fun a ha => ?_, fun a ha k ψ hk g => ?_⟩
    · cases ha; exact hd
    · cases ha; exact ho k ψ (by simpa using hk) g

/-- **Every run at one entry keeps the table** (`wpG_tabAt`, `[TR]` 6.50). -/
theorem wpG_tabAtS_one {e : LEnt} {α : Life} (ls : List SRec) (t : Expr)
    (Q : List SRec → Expr → WProp) {ρ : WRes} (ht : TabAtS [e] [α] ρ) (hw : wpG ls t Q ρ) :
    wpG ls t (fun ls' t' ρ' => TabAtS [e] [α] ρ' ∧ Q ls' t' ρ') ρ :=
  wpG_mono (fun _ _ _ h => ⟨tabAtS_one.mpr h.1, h.2⟩)
    (wpG_tabAt e.l α ls t Q (tabAtS_one.mp ht) hw)

/-- **The start of a lend is consistent with the table**: the callback's resource strictly above
the fresh lifetime, joined to the new view (`tabAt_start`). -/
theorem tabAtS_start_one {δ : LSub} {e : LEnt} {d : Bool} {α : Life} {ls : List SRec}
    {ρ ρv a va R : WRes} (hρ : ρ.InStratum α) (hv : ρv.InStratum α) (ha : vwE δ e d α ls a)
    (hek : e.k = .mut) (hva : ResU.CompS ρv a va) (hR : ResU.CompS ρ va R) :
    TabAtS [e] [α] R :=
  tabAtS_one.mpr (tabAt_start rfl hρ hv ha hek hva hR)

/-! ### The witness does not arise at `[x]` -/

/-- **The inner view is not consistent with the table at `[x]`**: a `mut` cell away from the
stack's place, at a lifetime below the stack's lend. -/
theorem not_tabAtS_innerView {e : LEnt} {k : BoCa.Loc} (hk : k ≠ e.l) {α αy : Life}
    (hαy : αy ⊏ α) : ¬ TabAtS [e] [α] (innerView k αy) := by
  intro ht
  have h := (tabAtS_one.mp ht).2 k _ hk (ResU.single_get_self k _)
  exact lt_asymm hαy h

/-- **No run at `[x]` reaches a state of which the inner view is a part.** From a resource
consistent with the table, every resource a run ends with (at a return or at a stop) has no part
equal to `k ↦ M_{αy}`. -/
theorem wpG_below_not_arises {e : LEnt} {k : BoCa.Loc} (hk : k ≠ e.l) {α αy : Life}
    (hαy : αy ⊏ α) (ls : List SRec) (t : Expr) (Q : List SRec → Expr → WProp) {ρ : WRes}
    (ht : TabAtS [e] [α] ρ) (hw : wpG ls t Q ρ) :
    wpG ls t (fun ls' t' ρ' => (∀ ρa ρb, ResU.CompS ρa ρb ρ' → ρa ≠ innerView k αy) ∧
      Q ls' t' ρ') ρ :=
  wpG_mono (fun _ _ _ h => ⟨fun _ _ hc hρa =>
      not_tabAtS_of_part hc (hρa ▸ not_tabAtS_innerView hk hαy) h.1, h.2⟩)
    (wpG_tabAtS_one ls t Q ht hw)

/-- **The inner view is consistent with the table at `[y, x]`**: inside an inner lend of `k` it is
that lend's own view. -/
theorem tabAtS_innerView_inner {ey ex : LEnt} {k : BoCa.Loc} (hk : ey.l = k) {α αy : Life} :
    TabAtS [ey, ex] [αy, α] (innerView k αy) := by
  refine ⟨fun a ha => ?_, fun a ha m ψ hm g => ?_⟩
  · cases ha
    intro m ψ g
    by_cases hm : m = k
    · subst hm
      rw [innerView, ResU.single_get_self] at g
      cases Option.some.inj g
      exact down_lt αy
    · rw [innerView, ResU.single_get_ne _ hm] at g
      exact absurd g (by simp)
  · have hmk : m ≠ k := fun h => hm (by simp [h, ← hk])
    rw [innerView, ResU.single_get_ne _ hmk] at g
    exact absurd g (by simp)

/-! ### The restated relation -/

/-- **The guard**: `P` asked only of a resource consistent with the table at the stack. -/
def guardS (σ : LStack) (αs : List Life) (P : WProp) : WProp := fun ρ => TabAtS σ αs ρ → P ρ

mutual
/-- **`vRL_σ` with the table as a guard at `U`.** D16.1's `vRLs` otherwise. -/
def vRLa (σ : LStack) : LSub → VTy → List Life → List SRec → Val → WProp
  | δ, .thunk C, αs, ls, f =>
      guardS σ αs
        (RelendableS δ [] σ (fun αs' ls' => cRLa σ δ C αs' ls' (forceE C (.val f))) αs ls)
  | δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLa σ δ A αs ls v₁ ⋆ vRLa σ δ B αs ls v₂
  | δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLa σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLa σ δ B αs ls v₂)
  | δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRLa σ δ A αs ls v ρ
  | δ, .box a A, αs, ls, v => atLife (extS δ σ αs) a fun α => box α (vRLa σ δ A αs ls v)
  | δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLa σ δ A αs ls v'
  | δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ A => A
/-- **`cRL_σ` with the table as a guard at `⊸` and `∀`.** D16.1's `cRLs` otherwise. -/
def cRLa (σ : LStack) : LSub → CTy → List Life → List SRec → Expr → WProp
  | δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRLa σ δ B αs ls'' v
  | δ, .eff n i q A B fin C, αs, ls, e =>
      bodyS δ σ (rowTab n i q A B fin C δ) (fun αs' ls v => effRetA σ δ C αs' ls v)
        (OpenS δ σ (rowTab n i q A B fin C δ) (fun αs' ls v => effRetA σ δ C αs' ls v)) αs ls e
  | δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ v, (vRLa σ δ A αs ls v ─⋆ guardS σ αs (cRLa σ δ C αs ls (.app e (.val v)))) ρ
  | δ, .amp C D, αs, ls, e => fun ρ =>
      cRLa σ δ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLa σ δ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | _, .top, _, _, _ => fun _ => True
  | δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ α, (⌜LtLife (extS δ σ αs) c α⌝ ─⋆
        guardS σ αs (cRLa σ (δ.extend x α) C αs ls (.app e (.val .unit)))) ρ
  | δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
termination_by structural _ C => C
/-- The answer relation of `F_Σ R` at the restated relation. -/
def effRetA (σ : LStack) : LSub → CTy → List Life → List SRec → Val → WProp
  | δ, .ret A, αs => fun ls v => vRLa σ δ A αs ls v
  | δ, .eff _ _ _ _ _ _ C, αs => effRetA σ δ C αs
  | _, _, _ => fun _ _ _ => False
termination_by structural _ C => C
end

/-- `⊛_{x ∈ dom(Γ)} vRLa_σ(Γ(x))`. -/
def gSepRLa (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then vRLa σ δ s.ty αs ls v ⋆ gSepRLa σ δ αs ls Γ γ else gSepRLa σ δ αs ls Γ γ

/-- The context relation at the restated relation. -/
def gRLa (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (Γ : Ctx VTy)
    (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLa σ δ αs ls Γ γ

/-- The semantic judgment at the stack `σ`: `GFPAt`'s conclusion for one judgment. -/
def SemA (σ : LStack) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  σ.WF Δ → ∀ (δ : LSub) (αs : List Life), αs.length = σ.length → List.IsChain (· < ·) αs →
    Δ.Models (extS δ σ αs) → ∀ (ls : List SRec) (γ : List Val) (ρ : WRes),
      TabAtS σ αs ρ → gRLa σ δ αs ls Γ γ ρ → cRLa σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-- **GFP (D16.2) at the stack `σ`, at the restated relation.** `GFPAt`'s statement, word for
word, over `cRLa`/`gRLa`. -/
def GFPAtA (σ : LStack) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerives Δ Γ e j → SemA σ Δ Γ e j

/-- **GFP at the restated relation**, at every stack. -/
def GFPA : Prop := ∀ σ : LStack, GFPAtA σ

/-- `cRLa` at `F_Σ R` is D16.1's piece itself: the stack components are not restated. -/
theorem cRLa_eff (σ : LStack) (δ : LSub) (n i : UInt32) (q : Qual) (A B : VTy) (C : CTy)
    (αs : List Life) (ls : List SRec) (e : Expr) :
    cRLa σ δ (.eff n i q A B fin C) αs ls e =
      bodyS δ σ (rowTab n i q A B fin C δ) (fun αs' ls v => effRetA σ δ C αs' ls v)
        (OpenS δ σ (rowTab n i q A B fin C δ) (fun αs' ls v => effRetA σ δ C αs' ls v)) αs ls e :=
  rfl

/-! ### At `σ = []`: the kernel's relation -/

/-- The table at the empty stack holds of every resource. -/
theorem tabAtS_nil (ρ : WRes) : TabAtS [] [] ρ := ⟨by simp, by simp⟩

/-- At the empty stack the guard vanishes. -/
theorem guardS_nil (P : WProp) : guardS [] [] P = P := by
  funext ρ
  exact propext ⟨fun h => h (tabAtS_nil ρ), fun h _ => h⟩

mutual
/-- **`vRLa_[] = vC`.** -/
theorem vRLa_nil : ∀ (δ : LSub) (A : VTy), vRLa [] δ A [] = fun ls v => vC true A ls δ v
  | δ, .thunk C => by
      funext ls f; funext ρ
      show guardS [] [] (RelendableS δ [] []
        (fun αs' ls' => cRLa [] δ C αs' ls' (forceE C (.val f))) [] ls) ρ = _
      rw [guardS_nil, propext relendableS_nil, cRLa_nil δ C]; rfl
  | δ, .tensor A B => by
      funext ls v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
        vRLa [] δ A [] ls v₁ ⋆ vRLa [] δ B [] ls v₂) = _
      rw [vRLa_nil δ A, vRLa_nil δ B]; rfl
  | δ, .sum A B => by
      funext ls v
      show BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLa [] δ A [] ls v₁)
        (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLa [] δ B [] ls v₂) = _
      rw [vRLa_nil δ A, vRLa_nil δ B]; rfl
  | δ, .bang A => by
      funext ls v
      show (fun ρ => ρ = PMap.empty ∧ vRLa [] δ A [] ls v ρ) = _
      rw [vRLa_nil δ A]; rfl
  | δ, .box a A => by
      funext ls v
      show atLife (extS δ [] []) a (fun α => box α (vRLa [] δ A [] ls v)) = _
      rw [vRLa_nil δ A]; rfl
  | δ, .ref A => by
      funext ls v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLa [] δ A [] ls v') = _
      rw [vRLa_nil δ A]; rfl
  | _, .unit => rfl
  | _, .zero => rfl
  | _, .imm _ _ => rfl
  | _, .mut _ _ => rfl
  | _, .unk => rfl
  | _, .tvar _ => rfl
  | _, .mu _ => rfl
  | _, .int _ => rfl
  | _, .fam _ => rfl
  | _, .opq _ => rfl
termination_by structural _ A => A
/-- **`cRLa_[] = cC`.** -/
theorem cRLa_nil : ∀ (δ : LSub) (C : CTy), cRLa [] δ C [] = fun ls e => cC C ls δ e
  | δ, .ret B => by
      funext ls e
      show wpTS ls e (fun ls'' v => vRLa [] δ B [] ls'' v) = _
      rw [vRLa_nil δ B]; rfl
  | δ, .eff n i q A B fin C => by
      funext ls e ρ
      exact propext (bodyS_nil_iff (Q' := effRet C δ)
        (fun ls v ρ => by rw [effRetA_nil δ C]))
  | δ, .arr A C => by
      funext ls e
      show (fun ρ => ∀ v, (vRLa [] δ A [] ls v ─⋆
        guardS [] [] (cRLa [] δ C [] ls (.app e (.val v)))) ρ) = _
      simp only [vRLa_nil δ A, cRLa_nil δ C, guardS_nil]; rfl
  | δ, .amp C D => by
      funext ls e
      show (fun ρ => cRLa [] δ C [] ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLa [] δ D [] ls (.app e (.val (.inj₂ .unit))) ρ) = _
      rw [cRLa_nil δ C, cRLa_nil δ D]; rfl
  | _, .top => rfl
  | δ, .all x c C => by
      have ih := fun α : Life => cRLa_nil (δ.extend x α) C
      funext ls e
      show (fun ρ => ∀ α : Life, (⌜LtLife (extS δ [] []) c α⌝ ─⋆
        guardS [] [] (cRLa [] (δ.extend x α) C [] ls (.app e (.val .unit)))) ρ) = _
      simp only [ih, guardS_nil]; rfl
  | _, .nu _ => rfl
termination_by structural _ C => C
/-- The answer relation at `[]` is the kernel's. -/
theorem effRetA_nil : ∀ (δ : LSub) (C : CTy), effRetA [] δ C [] = effRet C δ
  | δ, .ret A => by
      show (fun ls v => vRLa [] δ A [] ls v) = _
      rw [vRLa_nil δ A]; rfl
  | δ, .eff _ _ _ _ _ _ C => effRetA_nil δ C
  | _, .arr _ _ => rfl
  | _, .amp _ _ => rfl
  | _, .top => rfl
  | _, .all _ _ _ => rfl
  | _, .nu _ => rfl
termination_by structural _ C => C
end

theorem gSepRLa_nil (δ : LSub) (ls : List SRec) :
    ∀ (Γ : Ctx VTy) (γ : List Val), gSepRLa [] δ [] ls Γ γ = gSepC ls δ Γ γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      simp only [gSepRLa, gSepC, gSepRLa_nil δ ls Γ γ, vRLa_nil]

theorem gRLa_nil (δ : LSub) (ls : List SRec) (Γ : Ctx VTy) (γ : List Val) :
    gRLa [] δ [] ls Γ γ = gDenC ls δ Γ γ := by
  simp only [gRLa, gDenC, gSepRLa_nil]

/-- **GFP at the restated relation, at `σ = []`, is the fundamental property.** -/
theorem gfpAtA_nil_iff :
    GFPAtA [] ↔ ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerives Δ Γ e j →
      SemJ Δ Γ e j := by
  have hwf : ∀ Δ : LifeCtx, LStack.WF [] Δ := fun _ => ⟨by simp, List.nodup_nil⟩
  have hsem : ∀ Δ Γ e j, SemJ Δ Γ e j ↔ ∀ δ γ (ls : List SRec) ρ, Δ.Models δ →
      gDenC ls δ Γ γ ρ → cC (jdgCty j) ls δ (substAll γ e) ρ := by
    intro Δ Γ e j; cases j <;> rfl
  constructor
  · intro H Δ Γ e j h
    refine (hsem Δ Γ e j).mpr fun δ γ ls ρ hδ hg => ?_
    have := H Δ Γ e j h (hwf Δ) δ [] rfl List.IsChain.nil hδ ls γ ρ (tabAtS_nil ρ)
      (by rw [gRLa_nil]; exact hg)
    rwa [cRLa_nil] at this
  · intro H Δ Γ e j h _ δ αs hlen _ hδ ls γ ρ _ hg
    obtain rfl : αs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [cRLa_nil]
    rw [gRLa_nil] at hg
    exact (hsem Δ Γ e j).mp (H Δ Γ e j h) δ γ ls ρ hδ hg

/-- **GFP at the restated relation holds at `σ = []`**: it is `fundamentalC`. -/
theorem gfpAtA_nil : GFPAtA [] := gfpAtA_nil_iff.mpr fun _ _ _ _ h => fundamentalC h

/-! ### The stacked `U` clause at the restated relation -/

section
variable {σ : LStack} {δ : LSub}

/-- **`[force]`**: the guard discharged by the table, then D16.1's reading at `αs′ = αs`. -/
theorem force_RLa {C : CTy} {αs : List Life} (hc : List.IsChain (· < ·) αs) {ls : List SRec}
    {f : Val} {ρ : WRes} (ht : TabAtS σ αs ρ) (h : vRLa σ δ (.thunk C) αs ls f ρ) :
    cRLa σ δ C αs ls (forceE C (.val f)) ρ := by
  obtain ⟨ds, ρz, ρn, hcomp, hn, -, hth⟩ := h ht
  exact hth ls (Ext.refl ls ρz) αs (reLend_refl hc) ρn ρ hn hcomp

/-- **A `U` slot consistent with the table thaws by construction** (`relendableS_thunk`). -/
theorem relendableS_thunkA {C : CTy} {αs : List Life} {ls : List SRec} {f : Val} {ρ : WRes}
    (ht : TabAtS σ αs ρ) (h : vRLa σ δ (.thunk C) αs ls f ρ) :
    RelendableS δ [] σ (fun αs' ls' => vRLa σ δ (.thunk C) αs' ls' f) αs ls ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := h ht
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv _ => ?_⟩
  exact ⟨ds, ρz, ρv, hcv, hv, stratS_mono hr hz,
    fun ls'' he' αs'' hr' => hth ls'' (he.trans he') αs'' (reLend_trans hr' hr)⟩

/-- **`thunk M : U (F A)`** (`thunkF_RLs`): a closure over a re-lendable context. -/
theorem thunkF_RLa {G : List Life → List SRec → WProp} {M : Expr} {A : VTy} {γ : List Val}
    {αs : List Life} {ls : List SRec} {ρ : WRes} (hG : RelendableS δ [] σ G αs ls ρ)
    (hM : ∀ αs', ReLend αs' αs → ∀ ls' τ, G αs' ls' τ →
      cRLa σ δ (.ret A) αs' ls' (substAll (Val.unit :: γ) M) τ) :
    vRLa σ δ (.thunk (.ret A)) αs ls (Val.lam (Expr.psub 1 γ M)) ρ := fun _ => by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := hG
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← substAll_cons_l]
  exact hM αs' hr ls' τ (hth ls' he αs' hr ρv τ hv hcv)

/-- **`thunk M : U (F_Σ R)`** (`thunkE_RLs`). -/
theorem thunkE_RLa {G : List Life → List SRec → WProp} {M : Expr} {n i : UInt32} {q : Qual}
    {A B : VTy} {C : CTy} {γ : List Val} {αs : List Life} {ls : List SRec} {ρ : WRes}
    (hG : RelendableS δ [] σ G αs ls ρ)
    (hM : ∀ αs', ReLend αs' αs → ∀ ls' τ, G αs' ls' τ →
      cRLa σ δ (.eff n i q A B fin C) αs' ls' (substAll (Val.unit :: γ) M) τ) :
    vRLa σ δ (.thunk (.eff n i q A B fin C)) αs ls (Val.lam (Expr.psub 1 γ M)) ρ := fun _ => by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := hG
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  refine wpG_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← substAll_cons_l]
  exact hM αs' hr ls' τ (hth ls' he αs' hr ρv τ hv hcv)

/-! ### Elimination: the guard is the table `GFPAt` already assumes -/

/-- **`⊸` elimination.** The joined resource is the context's, consistent with the table. -/
theorem arr_elimA {A : VTy} {C : CTy} {αs : List Life} {ls : List SRec} {e : Expr} {v : Val}
    {ρ₁ ρ₂ ρ : WRes} (hf : cRLa σ δ (.arr A C) αs ls e ρ₁) (hv : vRLa σ δ A αs ls v ρ₂)
    (hc : ResU.CompS ρ₁ ρ₂ ρ) (ht : TabAtS σ αs ρ) :
    cRLa σ δ C αs ls (.app e (.val v)) ρ :=
  hf v ρ₂ ρ hv hc ht

/-- **`∀` elimination.** -/
theorem all_elimA {x : LifeVar} {c : Lifetime.Life} {C : CTy} {αs : List Life} {ls : List SRec}
    {e : Expr} {α : Life} {ρ : WRes} (hf : cRLa σ δ (.all x c C) αs ls e ρ)
    (hlt : LtLife (extS δ σ αs) c α) (ht : TabAtS σ αs ρ) :
    cRLa σ (δ.extend x α) C αs ls (.app e (.val .unit)) ρ :=
  hf α PMap.empty ρ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ) ht

end

/-! ### The refuted configuration is excluded by the guard -/

/-- **`not_gfpAt_below`'s configuration is excluded.** At the restated relation, with `σ = [x]`
and the function's resource empty, the `⊸` clause asks nothing of the inner view
`k ↦ M_{αy}`, `αy ⊏ α`: the joined resource is the inner view, which the table excludes. So the
step `Below.lean` takes (`h1`, the first run from the inner view) is not available. -/
theorem below_excluded {δ : LSub} {C : CTy} {ls : List SRec} {e : Expr} {v : Val}
    {α αy : Life} (hαy : αy ⊏ α) (k : BoCa.Loc) (hk : k ≠ e₀.l) :
    guardS [e₀] [α] (cRLa [e₀] δ C [α] ls (.app e (.val v))) (innerView k αy) :=
  fun ht => absurd ht (not_tabAtS_innerView hk hαy)

/-- `below_excluded` at the refutation's own numerals: `'y ↦ 3`, the lend at `1`, `k = 1`. -/
theorem below_excluded_at (δ : LSub) (ls : List SRec) (e : Expr) (v : Val) :
    guardS [e₀] [OrderDual.toDual 1]
      (cRLa [e₀] δ (.ret (.thunk (.ret belowA))) [OrderDual.toDual 1] ls (.app e (.val v)))
      (innerView 1 (OrderDual.toDual 3)) :=
  below_excluded (show (1 : ℕ) < 3 from by decide) 1 (by decide)

/-! ### `[lam]` -/

/-- **`cRLa` is closed under a pure step in front.** -/
theorem cRLa_step {σ : LStack} : ∀ (C : CTy) {δ : LSub} {e e' : Expr},
    (∀ μ : Heap, Step1N μ e μ e') → ∀ (αs : List Life) (ls : List SRec),
      Entails (cRLa σ δ C αs ls e') (cRLa σ δ C αs ls e)
  | .ret _, _, _, _, h, _, ls => wpTS_step h ls _
  | .eff _ _ _ _ _ _ _, _, _, _, h, _, ls => wpG_step h ls _
  | .arr _ C, _, _, _, h, αs, ls => fun _ h' v ρ₁ ρ₂ hv hc ht =>
      cRLa_step C (fun μ => (h μ).plug (Kont.appL .hole v)) αs ls _ (h' v ρ₁ ρ₂ hv hc ht)
  | .amp C D, _, _, _, h, αs, ls => fun _ ⟨h₁, h₂⟩ =>
      ⟨cRLa_step C (fun μ => (h μ).plug (Kont.appL .hole _)) αs ls _ h₁,
       cRLa_step D (fun μ => (h μ).plug (Kont.appL .hole _)) αs ls _ h₂⟩
  | .top, _, _, _, _, _, _ => fun _ _ => trivial
  | .all _ _ C, _, _, _, h, αs, ls => fun _ h' α ρ₁ ρ₂ hp hc ht =>
      cRLa_step C (fun μ => (h μ).plug (Kont.appL .hole _)) αs ls _ (h' α ρ₁ ρ₂ hp hc ht)
  | .nu C, _, _, _, h, _, ls => cC_step (.nu C) h ls _

/-- **`[lam]` at the restated relation.** The `⊸` clause's guard is the table at the joined
resource, which is what the body's judgment assumes. -/
theorem lam_RLa {σ : LStack} {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (h : SemA σ Δ (⟨A, true⟩ :: Γ) M (.comp C)) : SemA σ Δ Γ (.val (.lam M)) (.comp (.arr A C)) := by
  intro hwf δ αs hlen hc hδ ls γ ρ _ hg v ρ₁ ρ₂ hv hcomp ht₂
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp hg
  refine cRLa_step C (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ M) v) rfl) αs ls ρ₂ ?_
  rw [← substAll_cons_l]
  exact h hwf δ αs hlen hc hδ ls (v :: γ) ρ₂ ht₂
    (pure_sep_mk (by simpa using hlw) ⟨ρ₁, ρ, ResU.CompS.comm hcomp, hv, hgs⟩)

/-! ### `[allI]`: the relation reads `δ` only at the type's and the stack's variables -/

/-- `δ₁` and `δ₂` agree at every variable free in a stack entry's payload type. -/
def SAg (σ : LStack) (δ₁ δ₂ : LSub) : Prop :=
  ∀ e ∈ σ, ∀ y, VFree y e.T → δ₁.find? y = δ₂.find? y

section
variable {δ₁ δ₂ : LSub}

theorem SAg.take {σ : LStack} (h : SAg σ δ₁ δ₂) (k : Nat) : SAg (σ.take k) δ₁ δ₂ :=
  fun e he => h e (List.mem_of_mem_take he)

theorem SAg.drop {σ : LStack} (h : SAg σ δ₁ δ₂) (k : Nat) : SAg (σ.drop k) δ₁ δ₂ :=
  fun e he => h e (List.mem_of_mem_drop he)

theorem SAg.tail {e : LEnt} {σ : LStack} (h : SAg (e :: σ) δ₁ δ₂) : SAg σ δ₁ δ₂ :=
  fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- `δ_σ(αs)` agrees wherever `δ` does. -/
theorem extS_find_congr {P : LifeVar → Prop} (h : ∀ y, P y → δ₁.find? y = δ₂.find? y) :
    ∀ (σ : LStack) (αs : List Life) (y : LifeVar), P y →
      (extS δ₁ σ αs).find? y = (extS δ₂ σ αs).find? y
  | [], _, y, hy => h y hy
  | _ :: _, [], y, hy => h y hy
  | e :: σ, α :: αs, y, hy => by
      show ((extS δ₁ σ αs).extend e.x α).find? y = ((extS δ₂ σ αs).extend e.x α).find? y
      by_cases hxy : e.x = y
      · subst hxy; rw [find?_extend_self, find?_extend_self]
      · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
        exact extS_find_congr h σ αs y hy

theorem vwE_congr {e : LEnt} (h : ∀ y, VFree y e.T → δ₁.find? y = δ₂.find? y) :
    vwE δ₁ e = vwE δ₂ e := by
  obtain ⟨l, x, T, k, cr⟩ := e
  have hT : ∀ ls, vC true T ls δ₁ = vC true T ls δ₂ := fun ls => vC_congr T h true ls
  funext d α ls
  cases d with
  | false => rfl
  | true => cases k <;> simp only [vwE, viewP, hT]

theorem vwS_congr : ∀ {σ : LStack}, SAg σ δ₁ δ₂ → ∀ seen, vwS δ₁ seen σ = vwS δ₂ seen σ
  | [], _, _ => by
      funext ds αs ls
      cases ds <;> cases αs <;> rfl
  | e :: σ, h, seen => by
      funext ds αs ls
      cases ds with
      | nil => cases αs <;> rfl
      | cons d ds =>
          cases αs with
          | nil => rfl
          | cons α αs =>
              simp only [vwS, vwE_congr (h e (List.mem_cons_self ..)), vwS_congr h.tail]

theorem ownerE_congr {e : LEnt} (h : ∀ y, VFree y e.T → δ₁.find? y = δ₂.find? y) :
    ownerE δ₁ e = ownerE δ₂ e := by
  obtain ⟨l, x, T, k, cr⟩ := e
  have hT : ∀ ls, vC true T ls δ₁ = vC true T ls δ₂ := fun ls => vC_congr T h true ls
  funext ls
  cases k <;> simp only [ownerE, owner, ownerI, hT]

theorem ownWandE_congr {e : LEnt} (h : ∀ y, VFree y e.T → δ₁.find? y = δ₂.find? y) :
    ownWandE δ₁ e = ownWandE δ₂ e := by
  obtain ⟨l, x, T, k, cr⟩ := e
  have hT : ∀ ls, vC true T ls δ₁ = vC true T ls δ₂ := fun ls => vC_congr T h true ls
  funext ls R
  cases k <;> simp only [ownWandE, ownWand, hT]

theorem ghostS_congr : ∀ {σ : LStack}, SAg σ δ₁ δ₂ → ghostS δ₁ σ = ghostS δ₂ σ
  | [], _ => by funext αs ls R; rfl
  | e :: σ, h => by
      funext αs ls R
      cases αs with
      | nil => rfl
      | cons α αs =>
          have he := h e (List.mem_cons_self ..)
          simp only [ghostS, ownerE_congr he, ownWandE_congr he]

theorem relendableS_congr {σ : LStack} (h : SAg σ δ₁ δ₂) (seen : List BoCa.Loc) :
    RelendableS δ₁ seen σ = RelendableS δ₂ seen σ := by
  funext P αs ls ρ
  simp only [RelendableS, vwS_congr h seen]

theorem relendableN_congr {σ : LStack} (h : SAg σ δ₁ δ₂) (seen : List BoCa.Loc) :
    RelendableN δ₁ seen σ = RelendableN δ₂ seen σ := by
  funext P αs ls ρ
  simp only [RelendableN, vwS_congr h seen]

theorem stopS_congr {σ : LStack} (h : SAg σ δ₁ δ₂) : stopS δ₁ σ = stopS δ₂ σ := by
  have hg := fun k => ghostS_congr (h.take k)
  have hr := fun k seen => relendableN_congr (h.drop k) seen
  funext Tab X αs ls t
  simp only [stopS, hg, hr]

theorem bodyS_congr {σ : LStack} (h : SAg σ δ₁ δ₂) : bodyS δ₁ σ = bodyS δ₂ σ := by
  funext Tab Q X αs ls e
  simp only [bodyS, stopS_congr h]

theorem openFS_congr {σ : LStack} (h : SAg σ δ₁ δ₂) : openFS δ₁ σ = openFS δ₂ σ := by
  have hv := fun k => vwS_congr (h.take k) []
  funext Tab Q X k ds αi αo ls e ρ
  unfold openFS
  simp only [hv, bodyS_congr h]

theorem openS_congr {σ : LStack} (h : SAg σ δ₁ δ₂) : OpenS δ₁ σ = OpenS δ₂ σ := by
  funext Tab Q k ds αi αo ls e ρ
  unfold OpenS
  simp only [openFS_congr h]

theorem rowTab_congr {n i : UInt32} {q : Qual} {A B : VTy} {fin C : CTy}
    (h : ∀ y, CFree y (.eff n i q A B fin C) → δ₁.find? y = δ₂.find? y) :
    rowTab n i q A B fin C δ₁ = rowTab n i q A B fin C δ₂ := by
  have hA : ∀ ls, vC true A ls δ₁ = vC true A ls δ₂ :=
    fun ls => vC_congr A (fun y hy => h y (Or.inl hy)) true ls
  have hB : ∀ ls, vC true B ls δ₁ = vC true B ls δ₂ :=
    fun ls => vC_congr B (fun y hy => h y (Or.inr (Or.inl hy))) true ls
  have hF := finObl_congr fin (fun y hy => h y (Or.inr (Or.inr (Or.inl hy))))
  have hT := effTab_congr C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy))))
  simp only [rowTab, hA, hB, hF, hT]

end

mutual
/-- **`vRLa_σ⟦A⟧δ` reads `δ` only at the variables free in `A` and in the stack's payloads.** -/
theorem vRLa_congr (σ : LStack) : ∀ (A : VTy) {δ₁ δ₂ : LSub},
    (∀ y, VFree y A → δ₁.find? y = δ₂.find? y) → SAg σ δ₁ δ₂ → vRLa σ δ₁ A = vRLa σ δ₂ A
  | .thunk C, δ₁, δ₂, h, hs => by
      have ih := cRLa_congr σ C h hs
      funext αs ls f
      show guardS σ αs (RelendableS δ₁ [] σ
          (fun αs' ls' => cRLa σ δ₁ C αs' ls' (forceE C (.val f))) αs ls) =
        guardS σ αs (RelendableS δ₂ [] σ
          (fun αs' ls' => cRLa σ δ₂ C αs' ls' (forceE C (.val f))) αs ls)
      rw [ih, relendableS_congr hs]
  | .tensor A B, δ₁, δ₂, h, hs => by
      have h₁ := vRLa_congr σ A (fun y hy => h y (Or.inl hy)) hs
      have h₂ := vRLa_congr σ B (fun y hy => h y (Or.inr hy)) hs
      funext αs ls v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vRLa σ δ₁ A αs ls v₁ ⋆ vRLa σ δ₁ B αs ls v₂) =
        (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
          vRLa σ δ₂ A αs ls v₁ ⋆ vRLa σ δ₂ B αs ls v₂)
      rw [h₁, h₂]
  | .sum A B, δ₁, δ₂, h, hs => by
      have h₁ := vRLa_congr σ A (fun y hy => h y (Or.inl hy)) hs
      have h₂ := vRLa_congr σ B (fun y hy => h y (Or.inr hy)) hs
      funext αs ls v
      show BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLa σ δ₁ A αs ls v₁)
          (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLa σ δ₁ B αs ls v₂) =
        BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLa σ δ₂ A αs ls v₁)
          (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLa σ δ₂ B αs ls v₂)
      rw [h₁, h₂]
  | .bang A, δ₁, δ₂, h, hs => by
      have ih := vRLa_congr σ A h hs
      funext αs ls v
      show (fun ρ => ρ = PMap.empty ∧ vRLa σ δ₁ A αs ls v ρ) =
        (fun ρ => ρ = PMap.empty ∧ vRLa σ δ₂ A αs ls v ρ)
      rw [ih]
  | .box a A, δ₁, δ₂, h, hs => by
      have ih := vRLa_congr σ A (fun y hy => h y (Or.inr hy)) hs
      funext αs ls v
      have ha : a.interp (extS δ₁ σ αs) = a.interp (extS δ₂ σ αs) :=
        interp_congr a (fun y hy =>
          extS_find_congr (P := fun y => a.mentions y = true) (fun y hy => h y (Or.inl hy))
            σ αs y hy)
      show atLife (extS δ₁ σ αs) a (fun α => box α (vRLa σ δ₁ A αs ls v)) =
        atLife (extS δ₂ σ αs) a (fun α => box α (vRLa σ δ₂ A αs ls v))
      rw [ih, atLife_congr' ha]
  | .ref A, δ₁, δ₂, h, hs => by
      have ih := vRLa_congr σ A h hs
      funext αs ls v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLa σ δ₁ A αs ls v') =
        (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLa σ δ₂ A αs ls v')
      rw [ih]
  | .unit, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .zero, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .imm _ _, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .mut _ _, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .unk, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .tvar _, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .mu _, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .int _, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .fam _, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
  | .opq _, _, _, h, _ => by
      funext αs ls v; exact congrFun (vC_congr _ (extS_find_congr h σ αs) true ls) v
/-- `cRLa_σ⟦C⟧δ` reads `δ` only at the variables free in `C` and in the stack's payloads. -/
theorem cRLa_congr (σ : LStack) : ∀ (C : CTy) {δ₁ δ₂ : LSub},
    (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) → SAg σ δ₁ δ₂ → cRLa σ δ₁ C = cRLa σ δ₂ C
  | .ret B, δ₁, δ₂, h, hs => by
      have ih := vRLa_congr σ B h hs
      funext αs ls e
      show wpTS ls e (fun ls'' v => vRLa σ δ₁ B αs ls'' v) =
        wpTS ls e (fun ls'' v => vRLa σ δ₂ B αs ls'' v)
      rw [ih]
  | .eff n i q A B fin C, δ₁, δ₂, h, hs => by
      have hR := rowTab_congr h
      have ih := effRetA_congr σ C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy)))) hs
      funext αs ls e
      show bodyS δ₁ σ (rowTab n i q A B fin C δ₁) (fun αs' ls v => effRetA σ δ₁ C αs' ls v)
          (OpenS δ₁ σ (rowTab n i q A B fin C δ₁) (fun αs' ls v => effRetA σ δ₁ C αs' ls v)) αs ls e =
        bodyS δ₂ σ (rowTab n i q A B fin C δ₂) (fun αs' ls v => effRetA σ δ₂ C αs' ls v)
          (OpenS δ₂ σ (rowTab n i q A B fin C δ₂) (fun αs' ls v => effRetA σ δ₂ C αs' ls v)) αs ls e
      rw [hR, ih, bodyS_congr hs, openS_congr hs]
  | .arr A C, δ₁, δ₂, h, hs => by
      have hA := vRLa_congr σ A (fun y hy => h y (Or.inl hy)) hs
      have hC := cRLa_congr σ C (fun y hy => h y (Or.inr hy)) hs
      funext αs ls e
      show (fun ρ => ∀ v, (vRLa σ δ₁ A αs ls v ─⋆
          guardS σ αs (cRLa σ δ₁ C αs ls (.app e (.val v)))) ρ) =
        (fun ρ => ∀ v, (vRLa σ δ₂ A αs ls v ─⋆
          guardS σ αs (cRLa σ δ₂ C αs ls (.app e (.val v)))) ρ)
      rw [hA, hC]
  | .amp C D, δ₁, δ₂, h, hs => by
      have hC := cRLa_congr σ C (fun y hy => h y (Or.inl hy)) hs
      have hD := cRLa_congr σ D (fun y hy => h y (Or.inr hy)) hs
      funext αs ls e
      show (fun ρ => cRLa σ δ₁ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
          cRLa σ δ₁ D αs ls (.app e (.val (.inj₂ .unit))) ρ) =
        (fun ρ => cRLa σ δ₂ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
          cRLa σ δ₂ D αs ls (.app e (.val (.inj₂ .unit))) ρ)
      rw [hC, hD]
  | .top, _, _, _, _ => by funext αs ls e; rfl
  | .all x c C, δ₁, δ₂, h, hs => by
      have hC : ∀ α : Life, cRLa σ (δ₁.extend x α) C = cRLa σ (δ₂.extend x α) C := by
        intro α
        refine cRLa_congr σ C (fun y hy => ?_) (fun e he y hy => ?_)
        · by_cases hxy : x = y
          · subst hxy; rw [find?_extend_self, find?_extend_self]
          · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
            exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)
        · by_cases hxy : x = y
          · subst hxy; rw [find?_extend_self, find?_extend_self]
          · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
            exact hs e he y hy
      funext αs ls e
      have hL : ∀ α : Life, LtLife (extS δ₁ σ αs) c α = LtLife (extS δ₂ σ αs) c α := by
        intro α; unfold LtLife
        rw [interp_congr c (fun y hy =>
          extS_find_congr (P := fun y => c.mentions y = true) (fun y hy => h y (Or.inl hy))
            σ αs y hy)]
      show (fun ρ => ∀ α, (⌜LtLife (extS δ₁ σ αs) c α⌝ ─⋆
          guardS σ αs (cRLa σ (δ₁.extend x α) C αs ls (.app e (.val .unit)))) ρ) =
        (fun ρ => ∀ α, (⌜LtLife (extS δ₂ σ αs) c α⌝ ─⋆
          guardS σ αs (cRLa σ (δ₂.extend x α) C αs ls (.app e (.val .unit)))) ρ)
      simp only [hC, hL]
  | .nu C, δ₁, δ₂, h, _ => by
      funext αs ls e
      show cC (.nu C) ls (extS δ₁ σ αs) e = cC (.nu C) ls (extS δ₂ σ αs) e
      rw [cC_congr (.nu C) (extS_find_congr h σ αs) ls]
/-- The answer relation reads `δ` only at the row's and the stack's variables. -/
theorem effRetA_congr (σ : LStack) : ∀ (C : CTy) {δ₁ δ₂ : LSub},
    (∀ y, CFree y C → δ₁.find? y = δ₂.find? y) → SAg σ δ₁ δ₂ → effRetA σ δ₁ C = effRetA σ δ₂ C
  | .ret A, δ₁, δ₂, h, hs => by
      have ih := vRLa_congr σ A h hs
      funext αs
      show (fun ls v => vRLa σ δ₁ A αs ls v) = (fun ls v => vRLa σ δ₂ A αs ls v)
      rw [ih]
  | .eff _ _ _ _ _ _ C, _, _, h, hs =>
      effRetA_congr σ C (fun y hy => h y (Or.inr (Or.inr (Or.inr hy)))) hs
  | .arr _ _, _, _, _, _ => rfl
  | .amp _ _, _, _, _, _ => rfl
  | .top, _, _, _, _ => rfl
  | .all _ _ _, _, _, _, _ => rfl
  | .nu _, _, _, _, _ => rfl
end

theorem gSepRLa_congr {σ : LStack} {δ₁ δ₂ : LSub} {αs : List Life} {ls : List SRec} :
    ∀ {Γ : Ctx VTy} {γ : List Val}, (∀ s ∈ Γ, s.live = true → vRLa σ δ₁ s.ty = vRLa σ δ₂ s.ty) →
      gSepRLa σ δ₁ αs ls Γ γ = gSepRLa σ δ₂ αs ls Γ γ := by
  intro Γ
  induction Γ with
  | nil => intro γ _; cases γ <;> rfl
  | cons s Γ' ih =>
      intro γ h
      cases γ with
      | nil => rfl
      | cons v γ' =>
          have htail : ∀ t ∈ Γ', t.live = true → vRLa σ δ₁ t.ty = vRLa σ δ₂ t.ty :=
            fun t ht => h t (List.mem_cons_of_mem _ ht)
          by_cases hl : s.live
          · simp only [gSepRLa, if_pos hl, ih htail, h s (List.mem_cons_self ..) hl]
          · simp only [gSepRLa, if_neg hl, ih htail]

/-- At a variable not bound by the stack, extending `δ` commutes with `δ_σ(αs)`. -/
theorem extS_extend_find {x : LifeVar} {α : Life} {δ : LSub} :
    ∀ {σ : LStack} {αs : List Life}, x ∉ σ.map LEnt.x → ∀ y,
      (extS (δ.extend x α) σ αs).find? y = ((extS δ σ αs).extend x α).find? y
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | e :: σ, α' :: αs, hx, y => by
      have hex : e.x ≠ x := fun h => hx (by simp [h])
      have hx' : x ∉ σ.map LEnt.x := fun h => hx (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ h)
      show ((extS (δ.extend x α) σ αs).extend e.x α').find? y =
        (((extS δ σ αs).extend e.x α').extend x α).find? y
      by_cases hy : e.x = y
      · subst hy
        rw [find?_extend_self, find?_extend_ne _ _ (Ne.symm hex), find?_extend_self]
      · rw [find?_extend_ne _ _ hy, extS_extend_find hx' y]
        by_cases hxy : x = y
        · subst hxy; rw [find?_extend_self, find?_extend_self]
        · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy, find?_extend_ne _ _ hy]

/-- `Δ ⊨ δ` reads `δ` only through `find?`. -/
theorem models_congr {Δ : LifeCtx} {δ₁ δ₂ : LSub} (hδ : Δ.Models δ₁)
    (hf : ∀ y, δ₁.find? y = δ₂.find? y) : Δ.Models δ₂ := by
  intro z u hz
  obtain ⟨m, n, hm, hn, hlt⟩ := hδ z u hz
  exact ⟨m, n, by rw [← hf z]; exact hm, by rw [← interp_congr u (fun y _ => hf y)]; exact hn, hlt⟩

/-- **`[allI]` at the restated relation.** The `∀` clause's guard is the table at the function's
own resource, which is what the body's judgment assumes; the instance is read at
`δ[x ↦ α]`, the context unchanged since `'x` is free in none of its live slots.

Two hypotheses are added, both about the stack: the bound variable is not one of the stack's
lifetime variables (`hσx`), and is free in none of its payload types (`hσT`). The rule's own
premises say the same of `Δ`'s bounds and of `Γ`; the stack is the one place `GFPAt` reads `δ`
that the rule does not mention. `hσx` holds whenever `'x` is fresh for `Δ` (`stackFresh_of_fresh`,
the side condition of the presupposed rule, `Support/Statics/Presupposed.lean`), and `hσT` too
when the payload types are scoped in `Δ` (`stackTyFresh_of_fresh`); both hold at
`σ = []` and at `Below.lean`'s derivation (`allI_hyps_below`). -/
theorem allI_RLa {σ : LStack} {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {b : Lifetime.Life}
    {M : Expr} {S : VTy} {C : CTy} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (hσx : x ∉ σ.map LEnt.x) (hσT : ∀ e ∈ σ, ¬ VFree x e.T)
    (h : SemA σ (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C)) :
    SemA σ Δ Γ (.val (.lam M)) (.comp (.all x b C)) := by
  intro hwf δ αs hlen hc hδ ls γ ρ hT hg α ρ₁ ρ₂ hpure hcomp _
  obtain ⟨rfl, β, hβ, hlt⟩ := hpure
  have hρ₂ : ρ₂ = ρ := eq_of_compS_empty_left (ResU.CompS.comm hcomp)
  subst ρ₂
  have hwf' : σ.WF (Δ.extend x b) := ⟨fun e he => by
      obtain ⟨u, hu⟩ := hwf.1 e he
      rw [LifeCtx.find?_extend]
      by_cases hxe : x = e.x
      · exact ⟨b, by rw [if_pos hxe]⟩
      · exact ⟨u, by rw [if_neg hxe]; exact hu⟩, hwf.2⟩
  have hδ' : (Δ.extend x b).Models ((extS δ σ αs).extend x α) := by
    intro y u hy
    rw [LifeCtx.find?_extend] at hy
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨α, β, find?_extend_self _ x α,
        by rw [interp_extend_of_not_mentions hbx]; exact hβ, hlt⟩
    · rw [if_neg hxy] at hy
      obtain ⟨m, k, hm, hk, hlk⟩ := hδ y u hy
      exact ⟨m, k, by rw [find?_extend_ne _ α hxy]; exact hm,
        by rw [interp_extend_of_not_mentions (hΔx y u hy)]; exact hk, hlk⟩
  have hδ'' : (Δ.extend x b).Models (extS (δ.extend x α) σ αs) :=
    models_congr hδ' (fun y => (extS_extend_find hσx y).symm)
  have hs : SAg σ (δ.extend x α) δ := fun e he y hy =>
    find?_extend_ne δ α (fun h => hσT e he (h ▸ hy))
  have hgs : gSepRLa σ (δ.extend x α) αs ls Γ γ = gSepRLa σ δ αs ls Γ γ :=
    gSepRLa_congr (fun s hs' hl => vRLa_congr σ s.ty
      (fun y hy => find?_extend_ne δ α (fun h => hΓx s hs' hl (h ▸ hy))) hs)
  obtain ⟨hlw, hgs0⟩ := pure_sep_iff.mp hg
  refine cRLa_step C (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl) αs ls ρ ?_
  rw [← substAll_cons_l]
  refine h hwf' (δ.extend x α) αs hlen hc hδ'' ls (Val.unit :: γ) ρ hT
    (pure_sep_mk (by simpa using hlw) ?_)
  show gSepRLa σ (δ.extend x α) αs ls Γ γ ρ
  rw [hgs]; exact hgs0

/-- `hσx` is the presupposed rule's freshness, read at the stack. -/
theorem stackFresh_of_fresh {σ : LStack} {Δ : LifeCtx} {x : LifeVar} (hwf : σ.WF Δ)
    (hx : Δ.find? x = none) : x ∉ σ.map LEnt.x := by
  intro hm
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  obtain ⟨u, hu⟩ := hwf.1 e he
  rw [hx] at hu; cases hu

/-- `hσT` is the same freshness, at stack payload types scoped in `Δ`. -/
theorem stackTyFresh_of_fresh {σ : LStack} {Δ : LifeCtx} {x : LifeVar}
    (hsc : ∀ e ∈ σ, VScoped Δ e.T) (hx : Δ.find? x = none) : ∀ e ∈ σ, ¬ VFree x e.T := by
  intro e he hf
  obtain ⟨u, hu⟩ := hsc e he x hf
  rw [hx] at hu; cases hu

/-- `allI_RLa`'s added hypotheses at `Below.lean`'s derivation: the stack `[e₀]`, the binder `'y`
the variable `1`. -/
theorem allI_hyps_below : (1 : LifeVar) ∉ [e₀].map LEnt.x ∧ ∀ e ∈ [e₀], ¬ VFree 1 e.T := by
  refine ⟨by decide, fun e he => ?_⟩
  simp only [List.mem_singleton] at he
  subst he
  exact fun h => h

end GhostEnd
