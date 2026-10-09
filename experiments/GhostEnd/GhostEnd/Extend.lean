import GhostEnd.Arising

/-!
# GhostEnd — the `∀` clause read at every extension of the lend stack (#286)

`Arising.lean` guards D16.1 by the table at `U`, `⊸` and `∀` (`vRLa`/`cRLa`). With the guard, a
callback read at `σ` is obliged on no argument holding a cell below the stack
(`below_excluded`). A borrow constant hands its callback exactly such a view, at a fresh lifetime
below the stack, so the `withbor` row (#275) has to read the callback at `σ·y`.

This file tests #286's hypothesis: read the `∀` clause as a Kripke quantifier over **future
stacks**, `τ ++ σ`, the lend vectors growing with them. That is how the Kripke models surveyed in
`docs/effects-tr/17-borrow-callbacks.md` read every clause of a world-indexed relation that
receives a value from outside: for every future world (ADR09 Fig. 4, NDR09 Fig. 2, DNB10 Fig. 3,
Pitts–Stark Def. 4.2). The instance `τ = []` is D16.1's own `∀` clause.

## The recursion

`vRLk`, `cRLk`, `effRetK` are `vRLa`/`cRLa`/`effRetA` with one change, at `∀`. The stack is an
**index**, not a parameter: it grows at `∀` and nowhere else. The block is still
`termination_by structural` on the type. The `∀` clause refers to `cRLk` at the body `C`, a strict
subterm, at the stack `τ ++ σ`. The extension `τ` and its lifetimes are universally quantified to
the left of the clause and are not relations, so nothing occurs negatively at the same type.

## What is proved

* The block elaborates as structural recursion (the definitions below).
* **Elimination is not weakened** (`all_elimK`): the instance `τ = []` is `all_elimA`'s step.
* **The row's starting point** (`callback_ext`): a callback read at `σ`, at its type
  `∀'y ⊏ c. Mut 'y T ⊸ D`, applied to the view of a fresh lend `e` of a place `ℓ′` at `α` below
  the stack, is in `cRLk (e :: σ) D` at `α :: αs`. That is the hypothesis §16.4 takes "from the
  callback's premise at `σ·y`", here taken from the callback's value.
* At one entry the table at the extended stack is discharged from the callback's own resource
  lying above the new lend (`callback_ext_one`), as `[TR]` 6.172–6.174 discharge `⋔` by `⋔r` at the
  callback's resource.

## What is not proved here

* GFP at this relation. Its `allI` row needs the context read at `σ` to be read at `τ ++ σ`
  (Kripke monotonicity of `gRLk`). The premise-style alternative needs the same lemma: §16.4
  applies the induction hypothesis to the callback's body "at `σ·y`", with the outer context.
* The step from `cRLk (e :: σ) D` (answers in `effRetK (e :: σ)`) to the callback form
  `StackStep.lean` consumes (`OpenS … (cbQ …)`), #275's remaining half.

I have not derived these and have not verified that any obstruction is real.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The relation with the `∀` clause over future stacks -/

mutual
/-- **`vRL_σ` with the `∀` clause read at every extension of the stack.** `vRLa` otherwise, the
stack an index. -/
def vRLk : LStack → LSub → VTy → List Life → List SRec → Val → WProp
  | σ, δ, .thunk C, αs, ls, f =>
      guardS σ αs
        (RelendableS δ [] σ (fun αs' ls' => cRLk σ δ C αs' ls' (forceE C (.val f))) αs ls)
  | σ, δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLk σ δ A αs ls v₁ ⋆ vRLk σ δ B αs ls v₂
  | σ, δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLk σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLk σ δ B αs ls v₂)
  | σ, δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRLk σ δ A αs ls v ρ
  | σ, δ, .box a A, αs, ls, v => atLife (extS δ σ αs) a fun α => box α (vRLk σ δ A αs ls v)
  | σ, δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLk σ δ A αs ls v'
  | σ, δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ _ A => A
/-- **`cRL_σ` with the `∀` clause read at every extension `τ ++ σ`.** The extension's lifetimes
`αt` sit below the stack's, in nesting order. An entry of `τ` names a variable that is not the
stack's and is either the bound variable (the lend the binder names) or not free in the body, so
the extension rebinds nothing the body reads. `τ = []` is `cRLa`'s clause. -/
def cRLk : LStack → LSub → CTy → List Life → List SRec → Expr → WProp
  | σ, δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRLk σ δ B αs ls'' v
  | σ, δ, .eff n i q A B fin C, αs, ls, e =>
      bodyS δ σ (rowTab n i q A B fin C δ) (fun αs' ls v => effRetK σ δ C αs' ls v)
        (OpenS δ σ (rowTab n i q A B fin C δ) (fun αs' ls v => effRetK σ δ C αs' ls v)) αs ls e
  | σ, δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ v, (vRLk σ δ A αs ls v ─⋆ guardS σ αs (cRLk σ δ C αs ls (.app e (.val v)))) ρ
  | σ, δ, .amp C D, αs, ls, e => fun ρ =>
      cRLk σ δ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLk σ δ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | _, _, .top, _, _, _ => fun _ => True
  | σ, δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ (τ : LStack) (αt : List Life), αt.length = τ.length → List.IsChain (· < ·) (αt ++ αs) →
        (∀ e' ∈ τ, e'.x ∉ σ.map LEnt.x ∧ (e'.x = x ∨ ¬ CFree e'.x C)) → ∀ α, (⌜LtLife (extS δ (τ ++ σ) (αt ++ αs)) c α⌝ ─⋆
          guardS (τ ++ σ) (αt ++ αs)
            (cRLk (τ ++ σ) (δ.extend x α) C (αt ++ αs) ls (.app e (.val .unit)))) ρ
  | σ, δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
termination_by structural _ _ C => C
/-- The answer relation of `F_Σ R`. -/
def effRetK : LStack → LSub → CTy → List Life → List SRec → Val → WProp
  | σ, δ, .ret A, αs => fun ls v => vRLk σ δ A αs ls v
  | σ, δ, .eff _ _ _ _ _ _ C, αs => effRetK σ δ C αs
  | _, _, _, _ => fun _ _ _ => False
termination_by structural _ _ C => C
end

/-! ### Elimination at the stack itself -/

/-- **`∀` elimination is not weakened**: the extension `τ = []` is `cRLa`'s clause. -/
theorem all_elimK {σ : LStack} {δ : LSub} {x : LifeVar} {c : Lifetime.Life} {C : CTy}
    {αs : List Life} {ls : List SRec} {e : Expr} {α : Life} {ρ : WRes}
    (hc : List.IsChain (· < ·) αs) (hf : cRLk σ δ (.all x c C) αs ls e ρ)
    (hlt : LtLife (extS δ σ αs) c α) (ht : TabAtS σ αs ρ) :
    cRLk σ (δ.extend x α) C αs ls (.app e (.val .unit)) ρ :=
  hf [] [] rfl hc (fun _ h => absurd h List.not_mem_nil) α PMap.empty ρ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ) ht

/-! ### The row's starting point: the callback at `σ·y` -/

/-- `δ_{e·σ}(α·αs)` reads the new entry's variable at the new lifetime. -/
theorem extS_cons_self (δ : LSub) (e : LEnt) (σ : LStack) (α : Life) (αs : List Life) :
    Lifetime.Life.interp (extS δ (e :: σ) (α :: αs)) (.var e.x) = some α := by
  rw [Lifetime.Life.interp_var]
  exact find?_extend_self _ _ _

/-- **The callback read at `σ`, applied to a fresh lend's view, is read at `σ·y`.** Let the
callback `f` be in `cRLk σ` at `∀'y ⊏ c. Mut 'y T ⊸ D`, and let `e` be a `mut` lend at the
variable `y` of a place `ℓ′`, opened at `α` below the stack. Given the view `ℓ′ ↦ M_α` read at
`δ_{e·σ}`, and the table at the extended stack for the callback's resource beside the view, the
application `f () ℓ′` is in `cRLk (e :: σ) D` at `α :: αs`: the piece at `σ·new` that
`StackStep.lean`'s commutation lemmas fold back to `σ`. -/
theorem callback_ext {σ : LStack} {δ : LSub} {y : LifeVar} {c : Lifetime.Life} {T : VTy}
    {D : CTy} {αs : List Life} {ls : List SRec} {f : Val} {ρf : WRes}
    (hf : cRLk σ δ (.all y c (.arr (.mut (.var y) T) D)) αs ls (.val f) ρf)
    {e : LEnt} (hex : e.x = y) (hσ : e.x ∉ σ.map LEnt.x) {α : Life} (hch : List.IsChain (· < ·) (α :: αs))
    (hlt : LtLife (extS δ (e :: σ) (α :: αs)) c α) {ρv ρ : WRes}
    (hv : ptoMutS e.l α ls (fun ls₀ => vC true T ls₀ (extS (δ.extend y α) (e :: σ) (α :: αs)))
      ρv)
    (hc : ResU.CompS ρf ρv ρ) (ht₀ : TabAtS (e :: σ) (α :: αs) ρf)
    (ht : TabAtS (e :: σ) (α :: αs) ρ) :
    cRLk (e :: σ) (δ.extend y α) D (α :: αs) ls
      (.app (.app (.val f) (.val .unit)) (.val (.loc e.l))) ρ := by
  have hτ : ∀ e' ∈ [e], e'.x ∉ σ.map LEnt.x ∧ (e'.x = y ∨ ¬ CFree e'.x (.arr (.mut (.var y) T) D)) :=
    fun e' he' => by
      rw [List.mem_singleton] at he'; subst he'; exact ⟨hσ, Or.inl hex⟩
  have h1 := hf [e] [α] rfl hch hτ α PMap.empty ρf ⟨rfl, hlt⟩ (ResU.comp_empty_right ρf) ht₀
  refine h1 (.loc e.l) ρv ρ ?_ hc ht
  show vC true (.mut (.var y) T) ls (extS (δ.extend y α) (e :: σ) (α :: αs)) (.loc e.l) ρv
  refine ⟨α, ?_, e.l, pure_sep_mk rfl hv⟩
  rw [← hex]
  exact extS_cons_self _ e σ α αs

/-- Extending twice at one variable is extending once. -/
theorem find?_extend_extend (δ : LSub) (y : LifeVar) (α : Life) (z : LifeVar) :
    ((δ.extend y α).extend y α).find? z = (δ.extend y α).find? z := by
  by_cases h : y = z
  · subst h; rw [find?_extend_self, find?_extend_self]
  · rw [find?_extend_ne _ _ h, find?_extend_ne _ _ h]

/-- `vC` read at two substitutions agreeing everywhere, at every list. -/
theorem vC_congr' {δ₁ δ₂ : LSub} (T : VTy) (h : ∀ z, δ₁.find? z = δ₂.find? z) :
    (fun ls₀ => vC true T ls₀ δ₁) = (fun ls₀ => vC true T ls₀ δ₂) :=
  funext fun ls₀ => vC_congr T (fun z _ => h z) true ls₀

/-- **At one entry the table is the callback's resource above the new lend.** `callback_ext` at
`σ = []`, both tables discharged as `[TR]` 6.172–6.174 discharge `⋔`: the callback's resource lies
strictly above the fresh lifetime (`⋔r` at `@ρ₂`), and the view is the new entry's own. -/
theorem callback_ext_one {δ : LSub} {y : LifeVar} {c : Lifetime.Life} {T : VTy} {D : CTy}
    {ls : List SRec} {f : Val} {ρf : WRes}
    (hf : cRLk [] δ (.all y c (.arr (.mut (.var y) T) D)) [] ls (.val f) ρf)
    {l' : BoCa.Loc} {cr : UInt32 → Bool} {α : Life}
    (hlt : LtLife (extS δ [⟨l', y, T, .mut, cr⟩] [α]) c α) (hρf : ρf.InStratum α) {ρv ρ : WRes}
    (hv : viewP l' T (δ.extend y α) α ls ρv) (hc : ResU.CompS ρf ρv ρ) :
    cRLk [⟨l', y, T, .mut, cr⟩] (δ.extend y α) D [α] ls
      (.app (.app (.val f) (.val .unit)) (.val (.loc l'))) ρ := by
  let e : LEnt := ⟨l', y, T, .mut, cr⟩
  have hδ : extS (δ.extend y α) [e] [α] = (δ.extend y α).extend y α := rfl
  have hv' : ptoMutS e.l α ls
      (fun ls₀ => vC true T ls₀ (extS (δ.extend y α) [e] [α])) ρv := by
    rw [hδ, vC_congr' (δ₁ := (δ.extend y α).extend y α) (δ₂ := δ.extend y α) T
      (fun z => find?_extend_extend δ y α z)]
    exact hv
  have ht₀ : TabAtS [e] [α] ρf :=
    tabAtS_start_one (e := e) (d := false) (ls := ls) (δ := δ.extend y α) hρf (ResU.inStratum_empty α) ⟨rfl, trivial⟩ rfl
      (ResU.comp_empty_right PMap.empty) (ResU.comp_empty_right ρf)
  have ht : TabAtS [e] [α] ρ :=
    tabAtS_start_one (e := e) (d := true) (δ := δ.extend y α) (ρv := PMap.empty) hρf (ResU.inStratum_empty α) hv rfl
      (ResU.comp_empty_left ρv) hc
  exact callback_ext hf rfl (by simp) (List.isChain_singleton α) hlt hv' hc ht₀ ht

end GhostEnd
