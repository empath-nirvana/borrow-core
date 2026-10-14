import Law2.Inner

/-!
# Law2 — re-lendable values and computations at the stack

A borrower holding a stack `σ` of lends open across its stops runs, at each re-lend, from a
context the lenders' fresh views rebuild. Between stops it computes values, and the ones held
across a stop are frozen with the frame that holds them and thawed at the next re-lend. What a
value must satisfy for that is **re-lendability** (GhostEnd's `RelendableS`): its resource splits
into the views it holds at the current lifetimes and a part in `[top]`, and at every re-lend that
part, handed the views made afresh, is again in the relation.

`RSlot σ S₀ A` is that predicate read along `A`'s shape, `S₀` the lenders' row, and `RC σ S₀ C`
its computation side, by one structural recursion on the types:

* `⊗`, `⊕`, `!`, `Ref`: componentwise (a pair's components re-lend each with its own share);
* `U C`: re-lendable, and forced at every re-lend it is `RC C`;
* `[@a] A`: re-lendable, and at every re-lend in `Res_{@a}` and `RSlot A`;
* every other value type (`Imm`, `Mut`, `μ`, `[L]`, the leaves): re-lendable at the kernel's
  relation;
* `F_Σ R` and `F R` (the empty row): the piece (`bodyH`/`OpenH`, `Law2/Inner.lean`) at the
  lenders' operations the row has (`RTab`), the operations of other names caught by a handler
  inside the borrower (`RIn`), answering in `RSlot R`. At `F R` the table is empty and nothing is
  caught inside: a run to a re-lendable answer (`wpTS_of_rc_ret`);
* `A ⊸ C`, `C & D`, `⊤`: as the kernel's `𝒞⟦−⟧`, with `RSlot` at the argument;
* `∀`, `ν`: the kernel's relation at the current lifetimes.

`RCtx` is `⊛` of `RSlot` over a context's live slots.

* `relendableS_idem`, `rslot_relendable`, `rctx_relendable`: a re-lendable value or context is
  re-lendable *as such* — frozen at a stop and thawed at a re-lend, it is again an `RSlot`
  (`RCtx`). This is the frame a bind carries across its inner piece's stops.
* `rctx_split`: `RCtx` splits along `Ctx.SplitP`, a persistent slot to both sides.
* `rslot_vC`, `rctx_gDenC`: at the current lifetimes a re-lendable value is in the kernel's
  relation, at types with no `U` at a position `RSlot` reads componentwise (`NoThunkT`).
* `rslot_of_frozen`: a value whose type reads none of the stack's variables and whose resource
  lies in `[top]` is re-lendable, its whole share frozen and no view held.
* `rc_step`, `rc_bind`: `RC` is closed under a pure step in front and under a pure bind with a
  frame, at every computation type.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

/-- A name of the lenders' row `S₀`: its stops cross every lend. Every other name a borrower
performs is caught by a handler installed inside it. -/
def outN (S₀ : Row) (n : UInt32) : Bool := S₀.any fun o => o.n == n

/-- **The lenders' operations of a computation type's row**: its layers at the lenders' names, as
the kernel's table reads them (`effTab`). -/
def RTab (δ : LSub) (S₀ : Row) (C : CTy) : OpTab :=
  fun m j => if outN S₀ m then effTab (ℍ := ℍ) C δ m j else none

mutual
/-- **Re-lendable values** at the stack `σ`, its lends at `αs`, the lenders' row `S₀`.
Componentwise at `⊗`, `⊕`, `!` and `Ref`; at `U C`, re-lendable and forced at every re-lend
`RC C`; at `[@a] A`, re-lendable and at every re-lend in `Res_{@a}` and `RSlot A`; elsewhere
re-lendable at the kernel's relation. -/
def RSlot (δ : LSub) (σ : LStack) (S₀ : Row) : VTy → List Life → List SRec → Val → WProp
  | .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      RSlot δ σ S₀ A αs ls v₁ ⋆ RSlot δ σ S₀ B αs ls v₂
  | .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ RSlot δ σ S₀ A αs ls v₁)
        (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ RSlot δ σ S₀ B αs ls v₂)
  | .thunk C, αs, ls, f =>
      RelendableS δ [] σ (fun αs' ls' => RC δ σ S₀ C αs' ls' (forceE C (.val f))) αs ls
  | .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ RSlot δ σ S₀ A αs ls v ρ
  | .ref A, αs, ls, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆
      RSlot δ σ S₀ A αs ls v'
  | .box a A, αs, ls, v =>
      RelendableS δ [] σ (fun αs' ls' =>
        atLife (extS δ σ αs') a fun α => box α (RSlot δ σ S₀ A αs' ls' v)) αs ls
  | A, αs, ls, v =>
      RelendableS δ [] σ (fun αs' ls' => vCE (ℍ := ℍ) none true A ls' (extS δ σ αs') v) αs ls
termination_by structural A => A
/-- **Re-lendable computations**: at a row the piece, at its lenders' operations (`RTab`) and the
operations it catches inside (`RIn`), answering re-lendably; at `⊸`, `&`, `⊤` as the kernel's
`𝒞⟦−⟧`; at `∀` and `ν` the kernel's relation at the current lifetimes. -/
def RC (δ : LSub) (σ : LStack) (S₀ : Row) : CTy → List Life → List SRec → Expr → WProp
  | .ret A, αs, ls, e =>
      bodyH δ σ (RTab (ℍ := ℍ) δ S₀ (.ret A)) (fun _ _ => none)
        (fun αs' ls' v => RSlot δ σ S₀ A αs' ls' v)
        (OpenH δ σ (RTab (ℍ := ℍ) δ S₀ (.ret A)) (fun _ _ => none)
          (fun αs' ls' v => RSlot δ σ S₀ A αs' ls' v)) αs ls e
  | .eff n i q A B fin C, αs, ls, e =>
      bodyH δ σ (RTab (ℍ := ℍ) δ S₀ (.eff n i q A B fin C))
        (fun m j => if m = n ∧ j = i then
          (if outN S₀ n then none else
            some (fun αs ls v => RSlot δ σ S₀ A αs ls v, fun αs ls v => RSlot δ σ S₀ B αs ls v))
          else RIn δ σ S₀ C m j)
        (fun αs' ls' v => RAns δ σ S₀ C αs' ls' v)
        (OpenH δ σ (RTab (ℍ := ℍ) δ S₀ (.eff n i q A B fin C))
          (fun m j => if m = n ∧ j = i then
            (if outN S₀ n then none else
              some (fun αs ls v => RSlot δ σ S₀ A αs ls v, fun αs ls v => RSlot δ σ S₀ B αs ls v))
            else RIn δ σ S₀ C m j)
          (fun αs' ls' v => RAns δ σ S₀ C αs' ls' v)) αs ls e
  | .arr A C, αs, ls, e => fun ρ =>
      ∀ v, (RSlot δ σ S₀ A αs ls v ─⋆ RC δ σ S₀ C αs ls (.app e (.val v))) ρ
  | .amp C D, αs, ls, e => fun ρ =>
      RC δ σ S₀ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        RC δ σ S₀ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x b C, αs, ls, e => cC (ℍ := ℍ) (.all x b C) ls (extS δ σ αs) e
  | .nu C, αs, ls, e => cC (ℍ := ℍ) (.nu C) ls (extS δ σ αs) e
termination_by structural C => C
/-- The answer of a computation type at a row: `RSlot` at its answer type. -/
def RAns (δ : LSub) (σ : LStack) (S₀ : Row) : CTy → List Life → List SRec → Val → WProp
  | .ret A, αs, ls, v => RSlot δ σ S₀ A αs ls v
  | .eff _ _ _ _ _ _ C, αs, ls, v => RAns δ σ S₀ C αs ls v
  | _, _, _, _ => fun _ => False
termination_by structural C => C
/-- **The operations of a row a handler inside the borrower catches**: those whose name is not
the lenders' (`outN`), each with its argument and answer types read re-lendably. The first layer of
a name and index is the one a `perform` reaches, as for `effTab`. -/
def RIn (δ : LSub) (σ : LStack) (S₀ : Row) : CTy → UInt32 → UInt32 → Option InRel
  | .eff n i _ A B _ C, m, j =>
      if m = n ∧ j = i then
        (if outN S₀ n then none else
          some (fun αs ls v => RSlot δ σ S₀ A αs ls v, fun αs ls v => RSlot δ σ S₀ B αs ls v))
      else RIn δ σ S₀ C m j
  | _, _, _ => none
termination_by structural C => C
end

/-! ### Re-lendability: the lemmas `RSlot` and `RCtx` are built from -/

section rel
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- At the current lifetimes a re-lendable resource is in its predicate: the views it holds
handed back to the part it froze. -/
theorem relendableS_now {seen : List BoCa.Loc} {P : List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} {ρ : WRes} (hch : List.IsChain (· < ·) αs)
    (h : RelendableS δ seen σ P αs ls ρ) : P αs ls ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, -, hth⟩ := h
  exact hth ls (Ext.refl ls ρz) αs (reLend_refl hch) ρn ρ hn hc

/-- **Re-lendable, re-lent, is re-lendable**: thawed at a re-lend, the part frozen at a stop is
re-lendable again, its views those just handed. -/
theorem relendableS_idem {seen : List BoCa.Loc} {P : List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} {ρ : WRes} (h : RelendableS δ seen σ P αs ls ρ) :
    RelendableS δ seen σ (fun αs' ls' => RelendableS δ seen σ P αs' ls') αs ls ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := h
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  refine ⟨ds, ρz, ρv, hcv, hv, stratS_mono hr hz, fun ls'' he' αs'' hr' => ?_⟩
  exact hth ls'' (Ext.trans he he') αs'' (reLend_trans hr' hr)

/-- No entry's view: the flags all off. -/
theorem vwS_none : ∀ {seen : List BoCa.Loc} {σ : LStack} {αs : List Life} {ls : List SRec},
    αs.length = σ.length → vwS δ seen σ (List.replicate σ.length false) αs ls PMap.empty
  | _, [], [], _, _ => ⟨rfl, trivial⟩
  | _, _ :: σ, _ :: αs, _, h => ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
      by simp [vis, vwE]; exact ⟨rfl, trivial⟩, vwS_none (σ := σ) (by simpa using h)⟩
  | _, [], _ :: _, _, h => by simp at h
  | _, _ :: _, [], _, h => by simp at h

theorem vwS_none_eq : ∀ {seen : List BoCa.Loc} {σ : LStack} {αs : List Life} {ls : List SRec}
    {ρ : WRes}, vwS δ seen σ (List.replicate σ.length false) αs ls ρ → ρ = PMap.empty
  | _, [], [], _, _, h => h.1
  | _, _ :: σ, _ :: αs, _, _, ⟨a, b, hc, ha, hb⟩ => by
      have ha' : a = PMap.empty := by simp [vis, vwE] at ha; exact ha.1
      subst ha'
      rw [eq_of_compS_empty_left hc]
      exact vwS_none_eq (σ := σ) hb
  | _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, [], _, _, h => h.elim

/-- **A share frozen whole is re-lendable**, holding no view: in `[top]` and in the predicate at
every re-lend and every extension of the list. -/
theorem relendableS_frozen {P : List Life → List SRec → WProp} {αs : List Life}
    {ls : List SRec} {ρ : WRes} (hlen : αs.length = σ.length) (hz : stratS αs ρ)
    (h : ∀ ls', Ext ls ls' ρ → ∀ αs', ReLend αs' αs → P αs' ls' ρ) :
    RelendableS δ [] σ P αs ls ρ := by
  refine ⟨List.replicate σ.length false, ρ, PMap.empty, ResU.comp_empty_right ρ,
    vwS_none hlen, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  rw [vwS_none_eq hv] at hcv
  rw [ResU.CompS.functional hcv (ResU.comp_empty_right ρ)]
  exact h ls' he αs' hr

/-- **A frozen part beside a re-lendable one**: a resource in `[top]` whose predicate reads no
list joins the frozen part. -/
theorem relendableS_frame {seen : List BoCa.Loc} {F : WProp} {P : List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} (hF : ∀ ρ, F ρ → stratS αs ρ) :
    Entails (F ⋆ RelendableS δ seen σ P αs ls)
      (RelendableS δ seen σ (fun αs' ls' => F ⋆ P αs' ls') αs ls) := by
  rintro ρ ⟨ρf, ρr, hc, hf, ds, ρz, ρn, hcz, hn, hz, hth⟩
  obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hcz hc
  refine ⟨ds, x, ρn, hxρ, hn, fun a ha => (outlives_comp hx a).mpr ⟨hF ρf hf a ha, hz a ha⟩,
    fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  obtain ⟨y, hy, hyτ⟩ := compS_reassoc hx hcv
  exact ⟨ρf, y, hyτ, hf, hth ls' (he.right hx) αs' hr ρv y hv hy⟩

/-- Two parts compose to `∅` only when both are `∅`. -/
theorem compS_eq_empty {ρ₁ ρ₂ : WRes} (h : ResU.CompS ρ₁ ρ₂ PMap.empty) :
    ρ₁ = PMap.empty ∧ ρ₂ = PMap.empty := by
  have hg : ∀ l, ρ₁.get l = none ∧ ρ₂.get l = none := fun l => by
    rcases ResU.Comp.get h l with ⟨e₁, e₂, -⟩ | ⟨_, -, -, e⟩ | ⟨_, -, -, e⟩ | ⟨_, _, _, -, -, e, -⟩
    · exact ⟨e₁, e₂⟩
    all_goals exact absurd e (by simp)
  obtain ⟨g₁, f₁⟩ := ρ₁
  obtain ⟨g₂, f₂⟩ := ρ₂
  have e₁ : g₁ = fun _ => none := funext fun l => (hg l).1
  have e₂ : g₂ = fun _ => none := funext fun l => (hg l).2
  subst e₁ e₂
  exact ⟨rfl, rfl⟩

/-- The views at flags that hand nothing hand nothing at every vector. -/
theorem vwS_empty_any : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {αs αs' : List Life}
    {ls ls' : List SRec}, vwS δ seen σ ds αs ls PMap.empty → αs'.length = σ.length →
      vwS δ seen σ ds αs' ls' PMap.empty
  | _, [], [], [], [], _, _, h, _ => h
  | seen, e :: σ, d :: ds, _ :: αs, α' :: αs', ls, ls', ⟨a, b, hc, ha, hb⟩, hl => by
      obtain ⟨rfl, rfl⟩ := compS_eq_empty hc
      have hv : vis seen e d = false := by
        cases hd : vis seen e d
        · rfl
        · rw [hd] at ha
          obtain ⟨l, x, T, k, cr⟩ := e
          cases k with
          | «mut» =>
              obtain ⟨_, _, _, _, _, _, _, _, hρ, -⟩ := ha
              exact absurd (congrArg (fun r => r.get l) hρ) (by simp [ResU.single_get_self])
          | imm v =>
              obtain ⟨_, _, _, _, _, hρ, -⟩ := ha
              exact absurd (congrArg (fun r => r.get l) hρ) (by simp [ResU.single_get_self])
      refine ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ?_,
        vwS_empty_any hb (by simpa using hl)⟩
      rw [hv]; exact ⟨rfl, trivial⟩
  | _, [], [], _ :: _, _, _, _, h, _ => h.elim
  | _, [], _ :: _, αs, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, _ :: _, [], αs, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, _ :: _, _ :: _, [], _, _, _, h, _ => h.elim
  | _, _ :: _, _ :: _, _ :: _, [], _, _, _, hl => by simp at hl

/-- Flags that hand nothing at one vector hand nothing at every vector. -/
theorem vwS_flags_empty : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs αs' : List Life} {ls ls' : List SRec} {ρ : WRes}, vwS δ seen σ ds αs ls PMap.empty →
      vwS δ seen σ ds αs' ls' ρ → ρ = PMap.empty
  | _, [], [], [], [], _, _, _, _, h' => h'.1
  | seen, e :: σ, d :: ds, _ :: αs, _ :: αs', ls, ls', _, ⟨a, b, hc, ha, hb⟩,
      ⟨a', b', hc', ha', hb'⟩ => by
      obtain ⟨rfl, rfl⟩ := compS_eq_empty hc
      have hv : vis seen e d = false := by
        cases hd : vis seen e d
        · rfl
        · rw [hd] at ha
          obtain ⟨l, x, T, k, cr⟩ := e
          cases k with
          | «mut» =>
              obtain ⟨_, _, _, _, _, _, _, _, hρ, -⟩ := ha
              exact absurd (congrArg (fun r => r.get l) hρ) (by simp [ResU.single_get_self])
          | imm v =>
              obtain ⟨_, _, _, _, _, hρ, -⟩ := ha
              exact absurd (congrArg (fun r => r.get l) hρ) (by simp [ResU.single_get_self])
      rw [hv] at ha'
      obtain ⟨rfl, -⟩ := ha'
      rw [eq_of_compS_empty_left hc', vwS_flags_empty hb hb']
  | _, [], [], _ :: _, _, _, _, _, h, _ => h.elim
  | _, [], [], [], _ :: _, _, _, _, _, h' => h'.elim
  | _, [], _ :: _, αs, _, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, _ :: _, [], αs, _, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, h, _ => h.elim
  | _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, h' => h'.elim

/-- **A re-lendable `∅`** is in its predicate at `∅` at every re-lend and extension: it holds no
view. -/
theorem relendableS_empty {P : List Life → List SRec → WProp} {αs : List Life} {ls : List SRec}
    (h : RelendableS δ [] σ P αs ls PMap.empty) :
    ∀ ls', Ext ls ls' PMap.empty → ∀ αs', ReLend αs' αs → P αs' ls' PMap.empty := by
  obtain ⟨ds, ρz, ρn, hc, hn, -, hth⟩ := h
  obtain ⟨rfl, rfl⟩ := compS_eq_empty hc
  intro ls' he αs' hr
  have hlen : αs'.length = σ.length :=
    (List.Forall₂.length_eq hr.1).trans (vwS_length hn).2
  exact hth ls' he αs' hr PMap.empty PMap.empty (vwS_empty_any hn hlen) (ResU.comp_empty_right _)

end rel

/-! ### `RSlot` along a type's shape -/

section slot
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- A type `RSlot` reads at the kernel's relation: not `⊗`, `⊕`, `U`, `!`, `Ref` or `[@a]`. -/
def LeafR (A : VTy) : Prop :=
  (∀ A₁ A₂, A ≠ .tensor A₁ A₂) ∧ (∀ A₁ A₂, A ≠ .sum A₁ A₂) ∧ (∀ C, A ≠ .thunk C) ∧
    (∀ A', A ≠ .bang A') ∧ (∀ A', A ≠ .ref A') ∧ ∀ a A', A ≠ .box a A'

/-- The kernel's types at which `RSlot` reads the kernel's relation. -/
macro "leafR_tac" : tactic => `(tactic| exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
  ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩))))))

/-- The shapes `RSlot` reads. -/
theorem vty_shape (A : VTy) : (∃ A₁ A₂, A = .tensor A₁ A₂) ∨ (∃ A₁ A₂, A = .sum A₁ A₂) ∨
    (∃ C, A = .thunk C) ∨ (∃ A', A = .bang A') ∨ (∃ A', A = .ref A') ∨
    (∃ a A', A = .box a A') ∨ LeafR A := by
  cases A with
  | tensor A₁ A₂ => exact Or.inl ⟨_, _, rfl⟩
  | sum A₁ A₂ => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | thunk C => exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  | bang A' => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
  | ref A' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
  | box a A' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩)))))
  | _ => leafR_tac

theorem rslot_leaf {A : VTy} (hA : LeafR A) (αs : List Life) (ls : List SRec) (v : Val) :
    RSlot (ℍ := ℍ) δ σ S₀ A αs ls v =
      RelendableS δ [] σ (fun αs' ls' => vCE (ℍ := ℍ) none true A ls' (extS δ σ αs') v) αs ls := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hA
  cases A with
  | tensor A₁ A₂ => exact absurd rfl (h₁ A₁ A₂)
  | sum A₁ A₂ => exact absurd rfl (h₂ A₁ A₂)
  | thunk C => exact absurd rfl (h₃ C)
  | bang A' => exact absurd rfl (h₄ A')
  | ref A' => exact absurd rfl (h₅ A')
  | box a A' => exact absurd rfl (h₆ a A')
  | _ => rfl

theorem rslot_leaf_fun {A : VTy} (hA : LeafR A) (v : Val) :
    (fun αs ls => RSlot (ℍ := ℍ) δ σ S₀ A αs ls v) =
      fun αs ls => RelendableS δ [] σ
        (fun αs' ls' => vCE (ℍ := ℍ) none true A ls' (extS δ σ αs') v) αs ls :=
  funext fun αs => funext fun ls => rslot_leaf hA αs ls v

/-- An owned cell lies in every stratum. -/
theorem stratS_ptoOwn {αs : List Life} {ℓ : BoCa.Loc} {v : Val} {ρ : WRes} (h : ptoOwn ℓ v ρ) :
    stratS αs ρ := fun a _ => by rw [h]; exact ResU.inStratum_single_own a ℓ v

/-- **A re-lendable value is re-lendable as such**: frozen at a stop and thawed at a re-lend, it
is a re-lendable value again. Componentwise at `⊗` and `⊕` (`relendableS_sep`); the owned cell of a
`Ref` frozen beside its payload (`relendableS_frame`); at `U`, `[@a]` and the kernel's types, by
`relendableS_idem`. -/
theorem rslot_relendable (A : VTy) : ∀ {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes},
    RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ →
      RelendableS δ [] σ (fun αs' ls' => RSlot (ℍ := ℍ) δ σ S₀ A αs' ls' v) αs ls ρ := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨C, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ |
    ⟨a, A', rfl⟩ | hA
  · intro αs ls v ρ h
    obtain ⟨v₁, v₂, hp⟩ := h
    obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hp
    exact relendableS_mono' (fun αs' ls' τ hτ => ⟨v₁, v₂, pure_sep_mk rfl hτ⟩) ρ
      (relendableS_sep ρ ⟨ρ₁, ρ₂, hc, rslot_relendable A₁ h₁, rslot_relendable A₂ h₂⟩)
  · intro αs ls v ρ h
    rcases h with ⟨v₁, hp⟩ | ⟨v₂, hp⟩
    · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hp
      exact relendableS_mono' (fun αs' ls' τ hτ => Or.inl ⟨v₁, pure_sep_mk rfl hτ⟩) ρ
        (rslot_relendable A₁ h₁)
    · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hp
      exact relendableS_mono' (fun αs' ls' τ hτ => Or.inr ⟨v₂, pure_sep_mk rfl hτ⟩) ρ
        (rslot_relendable A₂ h₂)
  · intro αs ls v ρ h
    exact relendableS_idem h
  · intro αs ls v ρ h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := rslot_relendable A' h
    obtain ⟨rfl, rfl⟩ := compS_eq_empty hc
    refine ⟨ds, PMap.empty, PMap.empty, ResU.comp_empty_right _, hn, hz,
      fun ls' he αs' hr' ρv τ hv hcv => ?_⟩
    obtain rfl := vwS_flags_empty hn hv
    obtain rfl := eq_of_compS_empty_left hcv
    exact ⟨rfl, hth ls' he αs' hr' PMap.empty PMap.empty hv (ResU.comp_empty_right _)⟩
  · intro αs ls v ρ h
    obtain ⟨ℓ, v', hp⟩ := h
    obtain ⟨rfl, ρo, ρp, hc, ho, hpay⟩ := pure_sep_iff.mp hp
    exact relendableS_mono' (fun αs' ls' τ hτ => ⟨ℓ, v', pure_sep_mk rfl hτ⟩) ρ
      (relendableS_frame (fun _ h => stratS_ptoOwn h) ρ
        ⟨ρo, ρp, hc, ho, rslot_relendable A' hpay⟩)
  · intro αs ls v ρ h
    exact relendableS_idem h
  · intro αs ls v ρ h
    rw [rslot_leaf hA] at h
    rw [rslot_leaf_fun hA]
    exact relendableS_idem h
termination_by sizeOf A

/-- A type with no `U` at a position `RSlot` reads componentwise. -/
def NoThunkT : VTy → Prop
  | .tensor A B => NoThunkT A ∧ NoThunkT B
  | .sum A B => NoThunkT A ∧ NoThunkT B
  | .thunk _ => False
  | .bang A => NoThunkT A
  | .ref A => NoThunkT A
  | .box _ A => NoThunkT A
  | _ => True

/-- **A re-lendable value of a persistent type holds nothing**: at the current lifetimes it is in
the kernel's relation, which holds such a value only at `∅`. -/
theorem rslot_persistent_empty (A : VTy) (hp : A.Persistent) : ∀ {αs : List Life}
    {ls : List SRec} {v : Val} {ρ : WRes}, List.IsChain (· < ·) αs →
      RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ → ρ = PMap.empty := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨C, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ |
    ⟨a, A', rfl⟩ | hA
  · intro αs ls v ρ hch h
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
    obtain ⟨v₁, v₂, hq⟩ := h
    obtain ⟨-, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hq
    obtain rfl := rslot_persistent_empty A₁ hp.1 hch h₁
    obtain rfl := rslot_persistent_empty A₂ hp.2 hch h₂
    exact eq_of_compS_empty_left hc
  · intro αs ls v ρ hch h
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
    rcases h with ⟨v₁, hq⟩ | ⟨v₂, hq⟩
    · exact rslot_persistent_empty A₁ hp.1 hch (pure_sep_iff.mp hq).2
    · exact rslot_persistent_empty A₂ hp.2 hch (pure_sep_iff.mp hq).2
  · simp [VTy.Persistent, VTy.persistent] at hp
  · intro αs ls v ρ _ h
    exact h.1
  · simp [VTy.Persistent, VTy.persistent] at hp
  · intro αs ls v ρ hch h
    simp only [VTy.Persistent, VTy.persistent] at hp
    obtain ⟨α, -, hb, -⟩ := relendableS_now hch h
    exact rslot_persistent_empty A' hp hch hb
  · intro αs ls v ρ hch h
    rw [rslot_leaf hA] at h
    exact vP_empty_of_persistent hp (relendableS_now hch h)
termination_by sizeOf A

/-- **At the current lifetimes a re-lendable value is in the kernel's relation**, at a type with
no `U` at a position `RSlot` reads componentwise. -/
theorem rslot_vC (A : VTy) (hA : NoThunkT A) : ∀ {αs : List Life} {ls : List SRec} {v : Val}
    {ρ : WRes}, List.IsChain (· < ·) αs → RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ →
      vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨C, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ |
    ⟨a, A', rfl⟩ | hL
  · intro αs ls v ρ hch h
    obtain ⟨v₁, v₂, hq⟩ := h
    obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hq
    exact ⟨v₁, v₂, pure_sep_mk rfl
      ⟨ρ₁, ρ₂, hc, rslot_vC A₁ hA.1 hch h₁, rslot_vC A₂ hA.2 hch h₂⟩⟩
  · intro αs ls v ρ hch h
    rcases h with ⟨v₁, hq⟩ | ⟨v₂, hq⟩
    · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hq
      exact Or.inl ⟨v₁, pure_sep_mk rfl (rslot_vC A₁ hA.1 hch h₁)⟩
    · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hq
      exact Or.inr ⟨v₂, pure_sep_mk rfl (rslot_vC A₂ hA.2 hch h₂)⟩
  · exact hA.elim
  · intro αs ls v ρ hch h
    exact ⟨h.1, rslot_vC A' hA hch h.2⟩
  · intro αs ls v ρ hch h
    obtain ⟨ℓ, v', hq⟩ := h
    obtain ⟨rfl, ρo, ρp, hc, ho, hp⟩ := pure_sep_iff.mp hq
    exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, ρp, hc, ho, rslot_vC A' hA hch hp⟩⟩
  · intro αs ls v ρ hch h
    obtain ⟨α, ha, hb, hs⟩ := relendableS_now hch h
    exact ⟨α, ha, rslot_vC A' hA hch hb, hs⟩
  · intro αs ls v ρ hch h
    rw [rslot_leaf hL] at h
    exact relendableS_now hch h
termination_by sizeOf A

end slot

/-! ### Contexts -/

section ctx
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- `⊛` of `RSlot` over a context's live slots. -/
def rSep (δ : LSub) (σ : LStack) (S₀ : Row) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then RSlot (ℍ := ℍ) δ σ S₀ s.ty αs ls v ⋆ rSep δ σ S₀ αs ls Γ γ
      else rSep δ σ S₀ αs ls Γ γ

/-- **A re-lendable context**: its values re-lendable slot by slot. -/
def RCtx (δ : LSub) (σ : LStack) (S₀ : Row) (αs : List Life) (ls : List SRec) (Γ : Ctx VTy)
    (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ

theorem rSep_nil_vals : ∀ (Γ : Ctx VTy) {αs : List Life} {ls : List SRec} {ρ : WRes},
    rSep (ℍ := ℍ) δ σ S₀ αs ls Γ [] ρ → ρ = PMap.empty
  | [], _, _, _, h => h.1
  | _ :: _, _, _, _, h => h.1

/-- **`RCtx` splits along `Ctx.SplitP`**; a persistent slot holds nothing (`rslot_persistent_empty`)
and goes to both sides. -/
theorem rSep_split {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec} :
    ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ → ∀ {γ : List Val} {ρ : WRes},
      rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ → (rSep δ σ S₀ αs ls Γ₁ γ ⋆ rSep δ σ S₀ αs ls Γ₂ γ) ρ := by
  intro Γ Γ₁ Γ₂ hsp
  induction hsp with
  | nil =>
      intro γ ρ h
      refine ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ?_⟩
      cases γ <;> exact ⟨rfl, trivial⟩
  | left _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc' hcσ hc
          exact ⟨x, σ₂, hxρ, ⟨ρ₁, σ₁, hx, hv, h₁⟩, h₂⟩
  | right _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          obtain ⟨x, hx, hxρ⟩ := compS_lcomm hcσ hc
          exact ⟨σ₁, x, hxρ, h₁, ⟨ρ₁, σ₂, hx, hv, h₂⟩⟩
  | dead _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' => exact ih (γ := γ') h
  | dup hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, ⟨rfl, trivial⟩⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain rfl := rslot_persistent_empty _ hT hch hv
          rw [← eq_of_compS_empty_left hc] at hrest
          obtain ⟨σ₁, σ₂, hcσ, h₁, h₂⟩ := ih (γ := γ') hrest
          exact ⟨σ₁, σ₂, hcσ, ⟨PMap.empty, σ₁, compS_empty_left σ₁, hv, h₁⟩,
            ⟨PMap.empty, σ₂, compS_empty_left σ₂, hv, h₂⟩⟩

theorem rctx_split {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec}
    {Γ Γ₁ Γ₂ : Ctx VTy} (hsp : Ctx.SplitP Γ Γ₁ Γ₂) {γ : List Val} {ρ : WRes}
    (h : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) :
    (RCtx δ σ S₀ αs ls Γ₁ γ ⋆ RCtx δ σ S₀ αs ls Γ₂ γ) ρ := by
  obtain ⟨hl, h⟩ := pure_sep_iff.mp h
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := rSep_split hch hsp h
  exact ⟨ρ₁, ρ₂, hc, pure_sep_mk (hsp.liveWithin hl).1 h₁, pure_sep_mk (hsp.liveWithin hl).2 h₂⟩

/-- **A re-lendable context is re-lendable as such**, slot by slot (`relendableS_sep`). -/
theorem rSep_relendable {αs : List Life} (hlen : αs.length = σ.length) {ls : List SRec} :
    ∀ (Γ : Ctx VTy) (γ : List Val) {ρ : WRes}, rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ →
      RelendableS δ [] σ (fun αs' ls' => rSep (ℍ := ℍ) δ σ S₀ αs' ls' Γ γ) αs ls ρ
  | [], γ, ρ, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a)
        fun _ _ _ _ => by cases γ <;> exact ⟨rfl, trivial⟩
  | _ :: _, [], ρ, h => by
      obtain ⟨rfl, -⟩ := h
      exact relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a)
        fun _ _ _ _ => ⟨rfl, trivial⟩
  | s :: Γ, v :: γ, ρ, h => by
      unfold rSep at h ⊢
      by_cases hl : s.live = true
      · rw [if_pos hl] at h
        simp only [if_pos hl]
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact relendableS_sep ρ ⟨ρ₁, ρ₂, hc, rslot_relendable _ h₁, rSep_relendable hlen Γ γ h₂⟩
      · rw [if_neg hl] at h
        simp only [if_neg hl]
        exact rSep_relendable hlen Γ γ h

theorem rctx_relendable {αs : List Life} (hlen : αs.length = σ.length) {ls : List SRec}
    {Γ : Ctx VTy} {γ : List Val} {ρ : WRes} (h : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) :
    RelendableS δ [] σ (fun αs' ls' => RCtx (ℍ := ℍ) δ σ S₀ αs' ls' Γ γ) αs ls ρ := by
  obtain ⟨hl, h⟩ := pure_sep_iff.mp h
  exact relendableS_mono' (fun _ _ τ hτ => pure_sep_mk hl hτ) ρ (rSep_relendable hlen Γ γ h)

/-- Every live slot's type is free of `U` at the positions `RSlot` reads componentwise. -/
def CtxNoThunk (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → NoThunkT s.ty

/-- **At the current lifetimes a re-lendable context is in `𝒢⟦Γ⟧`**, at slots free of `U`. -/
theorem rSep_gSepC {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec} :
    ∀ (Γ : Ctx VTy) (γ : List Val), CtxNoThunk Γ → ∀ {ρ : WRes},
      rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ → gSepC (ℍ := ℍ) ls (extS δ σ αs) Γ γ ρ
  | [], _, _, _, h => by cases ‹List Val› <;> exact h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, hΓ, ρ, h => by
      unfold rSep at h
      unfold gSepC
      by_cases hl : s.live = true
      · rw [if_pos hl] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc, rslot_vC _ (hΓ s (List.mem_cons_self ..) hl) hch h₁,
          rSep_gSepC hch Γ γ (fun s' hs' hl' => hΓ s' (List.mem_cons_of_mem _ hs') hl') h₂⟩
      · rw [if_neg hl] at h ⊢
        exact rSep_gSepC hch Γ γ (fun s' hs' hl' => hΓ s' (List.mem_cons_of_mem _ hs') hl') h

theorem rctx_gDenC {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec}
    {Γ : Ctx VTy} (hΓ : CtxNoThunk Γ) {γ : List Val} {ρ : WRes}
    (h : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) : gDenC (ℍ := ℍ) ls (extS δ σ αs) Γ γ ρ := by
  obtain ⟨hl, h⟩ := pure_sep_iff.mp h
  exact pure_sep_mk hl (rSep_gSepC hch Γ γ hΓ h)

end ctx

/-! ### Locality along `Ext`, and frozen values -/

section local_
variable {δ : LSub} {σ : LStack} {S₀ : Row}

theorem relendableS_local {seen : List BoCa.Loc} {P : List Life → List SRec → WProp}
    {αs : List Life} {ls ls' : List SRec} {ρ : WRes} (hk : Ext ls ls' ρ)
    (h : RelendableS δ seen σ P αs ls ρ) : RelendableS δ seen σ P αs ls' ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := h
  exact ⟨ds, ρz, ρn, hc, vwS_local (hk.right hc) hn, hz,
    fun ls'' he αs' hr => hth ls'' (Ext.trans (hk.left hc) he) αs' hr⟩

theorem rslot_local (A : VTy) : ∀ {αs : List Life} {ls ls' : List SRec} {v : Val} {ρ : WRes},
    Ext ls ls' ρ → RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ → RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v ρ := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨C, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ |
    ⟨a, A', rfl⟩ | hA
  · intro αs ls ls' v ρ hk h
    obtain ⟨v₁, v₂, hq⟩ := h
    obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hq
    exact ⟨v₁, v₂, pure_sep_mk rfl
      ⟨ρ₁, ρ₂, hc, rslot_local A₁ (hk.left hc) h₁, rslot_local A₂ (hk.right hc) h₂⟩⟩
  · intro αs ls ls' v ρ hk h
    rcases h with ⟨v₁, hq⟩ | ⟨v₂, hq⟩
    · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hq
      exact Or.inl ⟨v₁, pure_sep_mk rfl (rslot_local A₁ hk h₁)⟩
    · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hq
      exact Or.inr ⟨v₂, pure_sep_mk rfl (rslot_local A₂ hk h₂)⟩
  · intro αs ls ls' v ρ hk h
    exact relendableS_local hk h
  · intro αs ls ls' v ρ hk h
    exact ⟨h.1, rslot_local A' hk h.2⟩
  · intro αs ls ls' v ρ hk h
    obtain ⟨ℓ, v', hq⟩ := h
    obtain ⟨rfl, ρo, ρp, hc, ho, hp⟩ := pure_sep_iff.mp hq
    exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, ρp, hc, ho, rslot_local A' (hk.right hc) hp⟩⟩
  · intro αs ls ls' v ρ hk h
    exact relendableS_local hk h
  · intro αs ls ls' v ρ hk h
    rw [rslot_leaf hA] at h ⊢
    exact relendableS_local hk h
termination_by sizeOf A

theorem rSep_local {αs : List Life} {ls ls' : List SRec} :
    ∀ (Γ : Ctx VTy) (γ : List Val) {ρ : WRes}, Ext ls ls' ρ →
      rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ → rSep (ℍ := ℍ) δ σ S₀ αs ls' Γ γ ρ
  | [], _, _, _, h => h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, ρ, hk, h => by
      unfold rSep at h ⊢
      by_cases hl : s.live = true
      · rw [if_pos hl] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact ⟨ρ₁, ρ₂, hc, rslot_local _ (hk.left hc) h₁, rSep_local Γ γ (hk.right hc) h₂⟩
      · rw [if_neg hl] at h ⊢
        exact rSep_local Γ γ hk h

theorem rctx_local {αs : List Life} {ls ls' : List SRec} {Γ : Ctx VTy} {γ : List Val}
    {ρ : WRes} (hk : Ext ls ls' ρ) (h : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) :
    RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γ γ ρ := by
  obtain ⟨hl, h⟩ := pure_sep_iff.mp h
  exact pure_sep_mk hl (rSep_local Γ γ hk h)

/-- **The kernel's relation reads none of the stack's variables at a type free of them.** -/
theorem vC_extS_of_not_free {A : VTy} (b : Bool) (ls : List SRec) :
    ∀ (σ : LStack) (αs : List Life), (∀ e ∈ σ, ¬ VFree e.x A) →
      vCE (ℍ := ℍ) none b A ls (extS δ σ αs) = vCE (ℍ := ℍ) none b A ls δ
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | e :: σ, α :: αs, h => by
      show vCE none b A ls ((extS δ σ αs).extend e.x α) = _
      rw [vC_extend_of_not_free (h e (List.mem_cons_self ..))]
      exact vC_extS_of_not_free b ls σ αs fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- **A lifetime mentioning none of the stack's variables reads the same at every vector.** -/
theorem interp_extS_of_not_mentions {a : Lifetime.Life} :
    ∀ (σ : LStack) (αs : List Life), (∀ e ∈ σ, a.mentions e.x = false) →
      a.interp (extS δ σ αs) = a.interp δ
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | e :: σ, α :: αs, h => by
      show a.interp ((extS δ σ αs).extend e.x α) = _
      rw [interp_extend_of_not_mentions (h e (List.mem_cons_self ..))]
      exact interp_extS_of_not_mentions σ αs fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- **A frozen value is re-lendable**: a value of a type that reads none of the stack's
variables, whose resource lies in `[top]`, holds no view; its share is frozen whole and its
relation is the same at every re-lend. -/
theorem rslot_of_frozen (A : VTy) (hA : NoThunkT A) (hx : ∀ e ∈ σ, ¬ VFree e.x A) :
    ∀ {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes}, αs.length = σ.length →
      vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ → stratS αs ρ →
      RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨C, rfl⟩ | ⟨A', rfl⟩ | ⟨A', rfl⟩ |
    ⟨a, A', rfl⟩ | hL
  · intro αs ls v ρ hlen h hz
    obtain ⟨v₁, v₂, hq⟩ := h
    obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hq
    refine ⟨v₁, v₂, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc, ?_, ?_⟩⟩
    · exact rslot_of_frozen A₁ hA.1 (fun e he hv => hx e he (Or.inl hv)) hlen h₁
        fun a ha => ((outlives_comp hc a).mp (hz a ha)).1
    · exact rslot_of_frozen A₂ hA.2 (fun e he hv => hx e he (Or.inr hv)) hlen h₂
        fun a ha => ((outlives_comp hc a).mp (hz a ha)).2
  · intro αs ls v ρ hlen h hz
    rcases h with ⟨v₁, hq⟩ | ⟨v₂, hq⟩
    · obtain ⟨rfl, h₁⟩ := pure_sep_iff.mp hq
      exact Or.inl ⟨v₁, pure_sep_mk rfl
        (rslot_of_frozen A₁ hA.1 (fun e he hv => hx e he (Or.inl hv)) hlen h₁ hz)⟩
    · obtain ⟨rfl, h₂⟩ := pure_sep_iff.mp hq
      exact Or.inr ⟨v₂, pure_sep_mk rfl
        (rslot_of_frozen A₂ hA.2 (fun e he hv => hx e he (Or.inr hv)) hlen h₂ hz)⟩
  · exact hA.elim
  · intro αs ls v ρ hlen h hz
    exact ⟨h.1, rslot_of_frozen A' hA (fun e he hv => hx e he hv) hlen h.2 hz⟩
  · intro αs ls v ρ hlen h hz
    obtain ⟨ℓ, v', hq⟩ := h
    obtain ⟨rfl, ρo, ρp, hc, ho, hp⟩ := pure_sep_iff.mp hq
    exact ⟨ℓ, v', pure_sep_mk rfl ⟨ρo, ρp, hc, ho,
      rslot_of_frozen A' hA (fun e he hv => hx e he hv) hlen hp
        fun a ha => ((outlives_comp hc a).mp (hz a ha)).2⟩⟩
  · intro αs ls v ρ hlen h hz
    have hxa : ∀ e ∈ σ, a.mentions e.x = false := fun e he => by
      cases hm : a.mentions e.x
      · rfl
      · exact absurd (Or.inl hm) (hx e he)
    have hxA : ∀ e ∈ σ, ¬ VFree e.x A' := fun e he hv => hx e he (Or.inr hv)
    obtain ⟨α, ha, hb, hs⟩ := h
    refine relendableS_frozen hlen hz fun ls' he αs' hr => ⟨α, ?_, ?_, hs⟩
    · rw [interp_extS_of_not_mentions σ αs' hxa]
      rwa [interp_extS_of_not_mentions σ αs hxa] at ha
    · have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr.1).trans hlen
      refine rslot_of_frozen A' hA hxA hlen' ?_ (stratS_mono hr hz)
      rw [vC_extS_of_not_free true ls' σ αs' hxA]
      rw [vC_extS_of_not_free true ls σ αs hxA] at hb
      exact vC_local true A' he hb
  · intro αs ls v ρ hlen h hz
    rw [rslot_leaf hL]
    refine relendableS_frozen hlen hz fun ls' he αs' _ => ?_
    rw [vC_extS_of_not_free true ls' σ αs' hx]
    rw [vC_extS_of_not_free true ls σ αs hx] at h
    exact vC_local true A he h
termination_by sizeOf A

end local_

/-! ### The rows, and `RC` along a computation type's shape -/

section rows
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- The answer predicate of a piece at the computation type `C`. -/
abbrev QA (δ : LSub) (σ : LStack) (S₀ : Row) (C : CTy) : List Life → List SRec → Val → WProp :=
  fun αs ls v => RAns (ℍ := ℍ) δ σ S₀ C αs ls v

/-- The piece at the row of `C`. -/
abbrev OHC (δ : LSub) (σ : LStack) (S₀ : Row) (C : CTy) : XT :=
  OpenH δ σ (RTab (ℍ := ℍ) δ S₀ C) (RIn (ℍ := ℍ) δ σ S₀ C) (QA (ℍ := ℍ) δ σ S₀ C)

/-- One run of the piece at the row of `C`. -/
abbrev BHC (δ : LSub) (σ : LStack) (S₀ : Row) (C : CTy) (αs : List Life) :
    List SRec → Expr → WProp :=
  bodyH δ σ (RTab (ℍ := ℍ) δ S₀ C) (RIn (ℍ := ℍ) δ σ S₀ C) (QA (ℍ := ℍ) δ σ S₀ C)
    (OHC (ℍ := ℍ) δ σ S₀ C) αs

theorem rIn_ret (A : VTy) : RIn (ℍ := ℍ) δ σ S₀ (.ret A) = fun _ _ => none := by
  funext m j; simp [RIn]

/-- **At a row, `RC` is the piece**: at `F R` with nothing caught inside, at `F_Σ R` with the
operations the row has beside the lenders'. -/
theorem rc_effOf (S : Row) (B : VTy) :
    RC (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) = BHC (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) := by
  cases S with
  | nil =>
      funext αs ls e
      simp only [CTy.effOf, BHC, OHC, rIn_ret]
      rw [RC]; rfl
  | cons o S =>
      funext αs ls e
      simp only [CTy.effOf, BHC, OHC]
      rw [RC]
      have hI : RIn (ℍ := ℍ) δ σ S₀ (.eff o.n o.i o.q o.A o.B o.fin (CTy.effOf S B)) =
          fun m j => if m = o.n ∧ j = o.i then
            (if outN S₀ o.n then none else
              some (fun αs ls v => RSlot (ℍ := ℍ) δ σ S₀ o.A αs ls v,
                fun αs ls v => RSlot (ℍ := ℍ) δ σ S₀ o.B αs ls v))
            else RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) m j := by
        funext m j; rw [RIn]
      rw [hI]; rfl

theorem rAns_effOf (A : VTy) : ∀ (S : Row) (αs : List Life) (ls : List SRec) (v : Val),
    RAns (ℍ := ℍ) δ σ S₀ (CTy.effOf S A) αs ls v = RSlot δ σ S₀ A αs ls v
  | [], _, _, _ => rfl
  | _ :: S, αs, ls, v => rAns_effOf A S αs ls v

theorem outN_of_mem {o : OpSig} (h : o ∈ S₀) : outN S₀ o.n = true :=
  List.any_eq_true.mpr ⟨o, h, by simp⟩

/-- A name outside the lenders' row has no entry in their table. -/
theorem tab_none_of_outN {n : UInt32} (h : outN S₀ n = false) (i : UInt32) :
    Row.tab S₀ δ n i = none := by
  unfold Row.tab
  cases hf : Row.find S₀ n i with
  | none => rfl
  | some o =>
      obtain ⟨hm, rfl, -⟩ := Row.find_mem hf
      rw [outN_of_mem hm] at h; cases h

/-- The lenders' operations of `F_Σ R`: `Σ`'s, at the lenders' names. -/
theorem rTab_effOf (S : Row) (B : VTy) :
    RTab (ℍ := ℍ) δ S₀ (CTy.effOf S B) =
      fun m j => if outN S₀ m then Row.tab S δ m j else none := by
  funext m j
  simp only [RTab, effTab_effOf]

/-- `RTab` reads a row's layers, not its answer type. -/
theorem rTab_effOf_ans (S : Row) (A B : VTy) :
    RTab (ℍ := ℍ) δ S₀ (CTy.effOf S A) = RTab (ℍ := ℍ) δ S₀ (CTy.effOf S B) := by
  rw [rTab_effOf, rTab_effOf]

/-- **At the lenders' row, the lenders' table.** -/
theorem rTab_self (B : VTy) : RTab (ℍ := ℍ) δ S₀ (CTy.effOf S₀ B) = Row.tab S₀ δ := by
  rw [rTab_effOf]
  funext m j
  cases h : outN S₀ m
  · simp [tab_none_of_outN h]
  · rfl

/-- A name outside the lenders' row has no entry in `RTab`. -/
theorem rTab_none_of_outN {n : UInt32} (h : outN S₀ n = false) (C : CTy) (i : UInt32) :
    RTab (ℍ := ℍ) δ S₀ C n i = none := by
  simp [RTab, h]

/-- An operation of the row at a lenders' name is its `RTab` entry. -/
theorem rTab_find {S : Row} (B : VTy) {o : OpSig} (hf : Row.find S o.n o.i = some o)
    (ho : outN S₀ o.n = true) : RTab (ℍ := ℍ) δ S₀ (CTy.effOf S B) o.n o.i = some (o.ent δ) := by
  rw [rTab_effOf]; simp [ho, Row.tab_find hf]

/-- Every operation of `Σ` a `perform` reaches at a lenders' name is linear and resumes. -/
def RowLin (S₀ S : Row) : Prop :=
  ∀ n i o, Row.find S n i = some o → outN S₀ n = true → o.q = .lin ∧ o.abort = false

theorem linResume_rTab {S : Row} (h : RowLin S₀ S) (B : VTy) :
    LinResume (RTab (ℍ := ℍ) δ S₀ (CTy.effOf S B)) := by
  intro m j en hT
  rw [rTab_effOf] at hT
  dsimp only at hT
  by_cases ho : outN S₀ m = true
  · rw [if_pos ho] at hT
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    obtain ⟨hq, ha⟩ := h m j o hf ho
    exact ⟨ha, hq⟩
  · rw [if_neg ho] at hT; cases hT

/-- The lenders' row resumes linearly when its table does. -/
theorem rowLin_self (hLR : LinResume (Row.tab S₀ δ)) : RowLin S₀ S₀ := fun n i o hf _ => by
  obtain ⟨ha, hq⟩ := hLR n i (o.ent δ) (Row.tab_find hf)
  exact ⟨hq, ha⟩

/-- Operations of a name outside the lenders' in front of a row leave its lenders' operations. -/
theorem rowLin_append {S₁ S : Row} (h₁ : ∀ o ∈ S₁, outN S₀ o.n = false) (h : RowLin S₀ S) :
    RowLin S₀ (S₁ ++ S) := by
  intro n i o hf ho
  rw [Row.find_append] at hf
  cases h₁f : Row.find S₁ n i with
  | some o' =>
      obtain ⟨hm, rfl, -⟩ := Row.find_mem h₁f
      rw [h₁ o' hm] at ho; cases ho
  | none =>
      rw [h₁f] at hf
      exact h n i o hf ho

/-- `RIn` reads a row's layers, not its answer type. -/
theorem rIn_effOf_ans : ∀ (S : Row) (A B : VTy),
    RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S A) = RIn δ σ S₀ (CTy.effOf S B)
  | [], _, _ => by funext m j; rfl
  | o :: S, A, B => by
      funext m j
      simp only [CTy.effOf, RIn, rIn_effOf_ans S A B]

/-- **An operation caught inside**: the row's operation of that name and index, read
re-lendably. -/
theorem rIn_effOf_find (B : VTy) : ∀ (S : Row) {n i : UInt32} {o : OpSig},
    Row.find S n i = some o → outN S₀ n = false →
    RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) n i =
      some (fun αs ls v => RSlot (ℍ := ℍ) δ σ S₀ o.A αs ls v,
        fun αs ls v => RSlot (ℍ := ℍ) δ σ S₀ o.B αs ls v)
  | [], _, _, _, h, _ => by simp [Row.find] at h
  | o' :: S, n, i, o, h, hout => by
      simp only [CTy.effOf, RIn]
      by_cases hc : n = o'.n ∧ i = o'.i
      · rw [if_pos hc]
        have e : o' = o := by
          unfold Row.find at h
          rw [List.find?_cons_of_pos (by simpa using hc)] at h
          exact Option.some.inj h
        subst e
        rw [← hc.1, hout]; rfl
      · rw [if_neg hc]
        refine rIn_effOf_find B S ?_ hout
        unfold Row.find at h ⊢
        rwa [List.find?_cons_of_neg (by simpa using hc)] at h

theorem rIn_effOf_some {B : VTy} : ∀ (S : Row) {n i : UInt32} {P : InRel},
    RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) n i = some P →
    ∃ o, Row.find S n i = some o ∧ outN S₀ n = false ∧
      P = (fun αs ls v => RSlot (ℍ := ℍ) δ σ S₀ o.A αs ls v,
        fun αs ls v => RSlot (ℍ := ℍ) δ σ S₀ o.B αs ls v)
  | [], _, _, _, h => by simp [CTy.effOf, RIn] at h
  | o' :: S, n, i, P, h => by
      simp only [CTy.effOf, RIn] at h
      by_cases hc : n = o'.n ∧ i = o'.i
      · rw [if_pos hc] at h
        cases hout : outN S₀ o'.n
        · rw [hout] at h
          simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
          refine ⟨o', ?_, by rw [hc.1]; exact hout, h.symm⟩
          unfold Row.find
          rw [List.find?_cons_of_pos (by simpa using hc)]
        · rw [hout] at h; simp at h
      · rw [if_neg hc] at h
        obtain ⟨o, hf, hout, rfl⟩ := rIn_effOf_some S h
        refine ⟨o, ?_, hout, rfl⟩
        unfold Row.find
        rw [List.find?_cons_of_neg (by simpa using hc)]
        exact hf

/-- **Nothing is caught inside** at a row of the lenders' names. -/
theorem rIn_effOf_none (B : VTy) (S : Row) (hS : ∀ o ∈ S, outN S₀ o.n = true) (n i : UInt32) :
    RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) n i = none := by
  cases h : RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) n i with
  | none => rfl
  | some P =>
      obtain ⟨o, hf, hout, -⟩ := rIn_effOf_some S h
      obtain ⟨hm, rfl, -⟩ := Row.find_mem hf
      rw [hS o hm] at hout; cases hout

/-- Layers of other names in front of a row do not change what it catches of a name. -/
theorem rIn_effOf_append {B : VTy} {n : UInt32} : ∀ (S₁ : Row) {S₂ : Row},
    (∀ o ∈ S₁, o.n ≠ n) → ∀ i,
      RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf (S₁ ++ S₂) B) n i = RIn δ σ S₀ (CTy.effOf S₂ B) n i
  | [], _, _, _ => rfl
  | o :: S₁, S₂, h, i => by
      simp only [List.cons_append, CTy.effOf, RIn]
      rw [if_neg (fun hc => h o (List.mem_cons_self ..) hc.1.symm)]
      exact rIn_effOf_append S₁ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho')) i

/-- **`RC` is closed under a pure step in front**, at every computation type. -/
theorem rc_step : ∀ (C : CTy) {e e' : Expr}, (∀ μ : Heap, Step1N μ e μ e') →
    ∀ (αs : List Life) (ls : List SRec),
      Entails (RC (ℍ := ℍ) δ σ S₀ C αs ls e') (RC (ℍ := ℍ) δ σ S₀ C αs ls e)
  | .ret _, _, _, h, _, ls => fun ρ hρ => by
      rw [RC] at hρ ⊢; exact wpG_step h ls _ ρ hρ
  | .eff _ _ _ _ _ _ _, _, _, h, _, ls => fun ρ hρ => by
      rw [RC] at hρ ⊢; exact wpG_step h ls _ ρ hρ
  | .arr _ C, _, _, h, αs, ls => fun ρ hρ => by
      rw [RC] at hρ ⊢
      exact fun v ρ₁ ρ₂ hv hc =>
        rc_step C (fun μ => (h μ).plug (Kont.appL .hole v)) αs ls _ (hρ v ρ₁ ρ₂ hv hc)
  | .amp C D, _, _, h, αs, ls => fun ρ hρ => by
      rw [RC] at hρ ⊢
      exact ⟨rc_step C (fun μ => (h μ).plug (Kont.appL .hole _)) αs ls _ hρ.1,
        rc_step D (fun μ => (h μ).plug (Kont.appL .hole _)) αs ls _ hρ.2⟩
  | .top, _, _, _, _, _ => fun ρ _ => by rw [RC]; trivial
  | .all x b C, _, _, h, αs, ls => fun ρ hρ => by
      rw [RC] at hρ ⊢; exact cC_step (.all x b C) h ls _ ρ hρ
  | .nu C, _, _, h, αs, ls => fun ρ hρ => by
      rw [RC] at hρ ⊢; exact cC_step (.nu C) h ls _ ρ hρ

/-- One head step in front of `RC`. -/
theorem rc_head (C : CTy) {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e') (hn : e.allocs = false)
    (αs : List Life) (ls : List SRec) :
    Entails (RC (ℍ := ℍ) δ σ S₀ C αs ls e') (RC (ℍ := ℍ) δ σ S₀ C αs ls e) :=
  rc_step C (fun μ => Step1N.head (h μ) hn) αs ls

/-- **Bind at `RC`.** Run a pure `M` in the hole of `K`, framing `R` through the run; the rest of
the computation continues at the list `M` returns. At a row it is `wpG_bind_frame`; at `⊸` the
argument joins the frame; at `∀` and `ν` it is the kernel's `cC_bind`. -/
theorem rc_bind : ∀ (C : CTy) (K : Kont) (M : Expr) (αs : List Life) (ls : List SRec)
    (P : List SRec → Val → WProp) (R : List SRec → WProp),
    (∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls')) →
    (∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails (P ls' v ⋆ R ls') (RC (ℍ := ℍ) δ σ S₀ C αs ls' (K.plug (.val v)))) →
    Entails (wpTS ls M P ⋆ R ls) (RC (ℍ := ℍ) δ σ S₀ C αs ls (K.plug M))
  | .ret A, K, M, αs, ls, P, R, hR, h => fun ρ hρ => by
      rw [RC]
      exact wpG_bind_frame K M ls P R _ hR
        (fun ls' hls v τ hτ => by have := h ls' hls v τ hτ; rw [RC] at this; exact this) ρ hρ
  | .eff n i q A B fin C, K, M, αs, ls, P, R, hR, h => fun ρ hρ => by
      rw [RC]
      exact wpG_bind_frame K M ls P R _ hR
        (fun ls' hls v τ hτ => by have := h ls' hls v τ hτ; rw [RC] at this; exact this) ρ hρ
  | .arr A C, K, M, αs, ls, P, R, hR, h => by
      rintro ρ ⟨ρ₁, ρ₂, hc, hw, hr⟩
      rw [RC]
      intro v a x ha hx
      obtain ⟨y, hy, hyx⟩ := compS_reassoc hc hx
      refine rc_bind C (.appL K v) M αs ls P (fun l => R l ⋆ RSlot (ℍ := ℍ) δ σ S₀ A αs l v) ?_ ?_ x
        ⟨ρ₁, y, hyx, hw, ρ₂, a, hy, hr, ha⟩
      · rintro ls' hls τ ⟨τ₁, τ₂, hcτ, h₁, h₂⟩
        exact ⟨τ₁, τ₂, hcτ, hR ls' hls τ₁ h₁, rslot_local A (ext_of_same hls τ₂) h₂⟩
      · rintro ls' hls w τ ⟨τ₁, τ₂, hcτ, hp, υ₁, υ₂, hcυ, hr', hv⟩
        obtain ⟨z, hz, hzτ⟩ := compS_reassoc' hcυ hcτ
        have := h ls' hls w z ⟨τ₁, υ₁, hz, hp, hr'⟩
        rw [RC] at this
        exact this v υ₂ τ hv hzτ
  | .amp C D, K, M, αs, ls, P, R, hR, h => fun ρ hρ => by
      rw [RC]
      exact ⟨rc_bind C (.appL K _) M αs ls P R hR
          (fun ls' hls w τ hτ => by have := h ls' hls w τ hτ; rw [RC] at this; exact this.1) ρ hρ,
        rc_bind D (.appL K _) M αs ls P R hR
          (fun ls' hls w τ hτ => by have := h ls' hls w τ hτ; rw [RC] at this; exact this.2) ρ hρ⟩
  | .top, _, _, _, _, _, _, _, _ => fun _ _ => by rw [RC]; trivial
  | .all x b C, K, M, αs, ls, P, R, hR, h => fun ρ hρ => by
      rw [RC]
      exact cC_bind (.all x b C) K M ls _ P R hR
        (fun ls' hls w τ hτ => by have := h ls' hls w τ hτ; rw [RC] at this; exact this) ρ hρ
  | .nu C, K, M, αs, ls, P, R, hR, h => fun ρ hρ => by
      rw [RC]
      exact cC_bind (.nu C) K M ls _ P R hR
        (fun ls' hls w τ hτ => by have := h ls' hls w τ hτ; rw [RC] at this; exact this) ρ hρ

end rows

/-! ### The piece judgment -/

section piece
variable {δ : LSub} {σ : LStack} {S₀ : Row}

theorem substAll_var' {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v) :
    substAll γ (.var i) = .val v := by
  show Expr.psub 0 γ (.var i) = _
  simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]

theorem rSep_deadP {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec} :
    ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → ∀ {γ : List Val} {ρ : WRes},
      rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; exact h.1
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (γ := γ') h
  | drop hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain rfl := rslot_persistent_empty _ hT hch hv
          obtain rfl := ih hrest
          exact eq_of_compS_empty_left hc

theorem rSep_soloP {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec} :
    ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.SoloP Γ i T → ∀ {γ : List Val} {ρ : WRes},
      i < γ.length → rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ →
        ∃ v, γ[i]? = some v ∧ RSlot (ℍ := ℍ) δ σ S₀ T αs ls v ρ := by
  intro Γ i T hs
  induction hs with
  | here hdead =>
      intro γ ρ hlen hg
      cases γ with
      | nil => simp at hlen
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          rw [rSep_deadP hch hdead hrest] at hc
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
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := hg
          obtain rfl := rslot_persistent_empty _ hS hch hv
          rw [← eq_of_compS_empty_left hc] at hrest
          obtain ⟨w, hw, hv'⟩ := ih (γ := γ') (by simpa using hlen) hrest
          exact ⟨w, by simpa using hw, hv'⟩

/-- **The piece judgment.** At every lifetime vector of the stack, in nesting order, whose
re-lends all model `Δ`, from a re-lendable context, the term is in `RC C`: at a row, it runs as the
piece at the row's lenders' operations and the operations it catches inside, to an answer
re-lendable at `C`'s answer type or to a stop whose continuations are the piece again. -/
def PJ (δ : LSub) (σ : LStack) (S₀ : Row) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) :
    Prop :=
  ∀ (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes), αs.length = σ.length →
    List.IsChain (· < ·) αs → (∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) →
    RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ → RC (ℍ := ℍ) δ σ S₀ C αs ls (substAll γ e) ρ

/-- The piece judgment at a row is one run of the piece. -/
theorem pj_effOf_iff {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {S : Row} {B : VTy} :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (CTy.effOf S B) ↔
      ∀ (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes), αs.length = σ.length →
        List.IsChain (· < ·) αs → (∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) →
        RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ →
          BHC (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) αs ls (substAll γ e) ρ := by
  simp only [PJ, rc_effOf]

/-- **`[var]`** at a row: the variable's re-lendable value. -/
theorem pj_var {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy} {S : Row} (h : Ctx.SoloP Γ i A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.var i) (CTy.effOf S A) := by
  refine pj_effOf_iff.mpr fun αs ls γ ρ _ hch _ hg => ?_
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg
  obtain ⟨v, hv, hval⟩ := rSep_soloP hch h (h.lt_of_liveWithin hl) hs
  rw [substAll_var' hv]
  refine wpG_here _ _ _ ρ (Or.inl ⟨v, rfl, ?_⟩)
  show RAns δ σ S₀ (CTy.effOf S A) αs ls v ρ
  rw [rAns_effOf]; exact hval

/-- **A pure computation whose answer is frozen**: Core's typing derives it at `F A`, `A` reads
none of the stack's variables and its values lie in `[top]` (`hz`). The fundamental property at the
current lifetimes runs it; its answer, frozen whole, is re-lendable (`rslot_of_frozen`). Its
context holds no `U`. -/
theorem pj_pure {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {S : Row}
    (hd : CDerives Δ Γ e (.comp (.ret A))) (hΓ : CtxNoThunk Γ) (hA : NoThunkT A)
    (hx : ∀ en ∈ σ, ¬ VFree en.x A)
    (hz : ∀ αs ls v ρ, αs.length = σ.length → List.IsChain (· < ·) αs →
      vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ → stratS αs ρ) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (CTy.effOf S A) := by
  refine pj_effOf_iff.mpr fun αs ls γ ρ hlen hch hΔ hg => ?_
  have hS : SemC Δ Γ e (.ret A) := fundamentalC (ℍ := ℍ) hd
  have hrun : wpTS ls (substAll γ e) (fun ls'' => vCE (ℍ := ℍ) none true A ls'' (extS δ σ αs)) ρ :=
    hS (extS δ σ αs) γ ls ρ (hΔ αs (reLend_refl hch)) (rctx_gDenC hch hΓ hg)
  refine wpG_mono (fun ls' t τ hq => Or.inl ?_) ((wpTS_iff_wpG _ _ _ _).mp hrun)
  obtain ⟨v, rfl, hv⟩ := hq
  refine ⟨v, rfl, ?_⟩
  show RAns δ σ S₀ (CTy.effOf S A) αs ls' v τ
  rw [rAns_effOf]
  exact rslot_of_frozen A hA hx hlen hv (hz αs ls' v τ hlen hch hv)

/-- What a stop drops when it drops no view. -/
theorem dropS_none : ∀ {seen : List BoCa.Loc} {σ : LStack},
    dropS seen σ (List.replicate σ.length false) PMap.empty
  | _, [] => ⟨rfl, trivial⟩
  | _, _ :: σ => ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _,
      by simp [vis, dropE]; exact ⟨rfl, trivial⟩, dropS_none (σ := σ)⟩

/-- **A value, frozen whole, is the piece**: holding no view, at every re-lend it answers in
`Q`. -/
theorem openH_val_frozen {To : OpTab} {RI : UInt32 → UInt32 → Option InRel}
    {Q : List Life → List SRec → Val → WProp} {αi : List Life} {ls : List SRec} {v : Val}
    {ρ : WRes}
    (hz : ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) αi' → stratS αi' ρ)
    (hq : ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) αi' →
      αi'.length = σ.length → Q αi' ls v ρ) :
    OpenH δ σ To RI Q σ.length (List.replicate σ.length false) αi [] ls (.val v) ρ := by
  refine openH_fold fun αi' hlt hch => ?_
  rw [List.append_nil] at hch ⊢
  refine ⟨fun w W hw hc => ?_, hz αi' hlt hch⟩
  rw [List.take_length] at hw
  have hlen : αi'.length = σ.length := (vwS_length hw).2
  rw [vwS_none_eq hw] at hc
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ)]
  exact wpG_here _ _ _ ρ (Or.inl ⟨v, rfl, hq αi' hlt hch hlen⟩)

/-- A value of a type outliving every lifetime lies in `[top]` at every vector. -/
theorem stratS_of_outlives {A : VTy} (hAo : ∀ Δ a, VOutlives Δ a A) {y : LifeVar}
    (hy : ¬ VFree y A) {ls : List SRec} {v : Val} {ρ : WRes}
    (h : vCE (ℍ := ℍ) none true A ls δ v ρ) (αs : List Life) : stratS αs ρ := fun a _ => by
  have h' : vCE (ℍ := ℍ) none true A ls (δ.extend y a) v ρ := by
    rw [vC_extend_of_not_free hy]; exact h
  exact vC_outlives (Δ := LifeCtx.empty) (a := .var y) (models_empty_any _)
    (interp_ext_self δ y a) (hAo _ _) true ls v ρ h'

/-- The value judgment: from a re-lendable context the value expression runs, purely, to a
re-lendable value. -/
def PV (δ : LSub) (σ : LStack) (S₀ : Row) (Δ : LifeCtx) (Γ : Ctx VTy) (V : Expr) (A : VTy) :
    Prop :=
  ∀ (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes), αs.length = σ.length →
    List.IsChain (· < ·) αs → (∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) →
    RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ →
    wpTS ls (substAll γ V) (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v) ρ

/-- **`[perform]` at a resuming operation of the lenders' names**: linear, answered at `1`, its
argument data reading none of the stack's variables and outliving every lifetime. The argument is
re-lendable and so, at the current lifetimes, in the kernel's relation; by 6.60 it is in `[top]`.
The stop crosses every lend and drops no view, and its continuation, a value, is the piece. -/
theorem pj_perform {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hout : outN S₀ o.n = true) (ha : o.abort = false)
    (hq : o.q = .lin) (hoB : o.B = .unit) (hx : ∀ en ∈ σ, ¬ VFree en.x o.A)
    (hAo : ∀ Δ a, VOutlives Δ a o.A) (hA : NoThunkT o.A) (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γ V o.A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) := by
  refine pj_effOf_iff.mpr fun αs ls γ ρ hlen hch hΔ hg => ?_
  change wpG ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ ρ
  refine wpG_bind_pure _ _ ls _ ρ (wpTS_mono (fun ls' v τ hv => ?_) ρ
    (hV αs ls γ ρ hlen hch hΔ hg))
  have hv' : vCE (ℍ := ℍ) none true o.A ls' δ v τ := by
    have := rslot_vC o.A hA hch hv
    rw [vC_extS_of_not_free true ls' σ αs hx] at this; exact this
  have hzt : stratS αs τ := by
    cases σ with
    | nil =>
        obtain rfl : αs = [] := List.eq_nil_of_length_eq_zero hlen
        exact stratS_nil τ
    | cons en σ' => exact stratS_of_outlives hAo (hx en (List.mem_cons_self ..)) hv' αs
  refine wpG_here _ _ _ τ (Or.inr (Or.inl ?_))
  refine stopAt_of_perform (K := .hole) (n := o.n) (i := o.i) (en := o.ent δ) rfl
    (rTab_find o.B hf hout) ha (ds := List.replicate σ.length false) dropS_none ?_ ?_
    (ResU.comp_empty_right τ) hzt (compS_empty_left τ)
  · exact hv'
  · refine ⟨fun hu => absurd (hq.symm.trans hu) (by decide),
      fun ls'' _ => ⟨fun w τ₁ τ₂ hBw hcτ => ?_,
      fun hl => absurd hq hl⟩⟩
    have hBw' : vCE (ℍ := ℍ) none true .unit ls'' δ w τ₁ := by
      simpa [OpSig.ent, hoB] using hBw
    obtain ⟨rfl, rfl⟩ := hBw'
    rw [eq_of_compS_empty_left hcτ]
    refine openH_val_frozen (fun _ _ _ a _ => ResU.inStratum_empty a) fun αi' _ hch' hlen' => ?_
    show RAns δ σ S₀ (CTy.effOf S o.B) αi' ls'' Val.unit PMap.empty
    rw [rAns_effOf, hoB]
    exact relendableS_frozen hlen' (fun a _ => ResU.inStratum_empty a)
      fun _ _ _ _ => ⟨rfl, rfl⟩

/-- The frozen form of a re-lendable context: in `[top]`, and at every extension and every re-lend,
handed the views its drops ask for, the context again. -/
def FzCtx (δ : LSub) (σ : LStack) (S₀ : Row) (Γ : Ctx VTy) (γ : List Val) (αs : List Life)
    (d : List Bool) (ls : List SRec) : WProp := fun τ =>
  stratS αs τ ∧ ∀ ls', Ext ls ls' τ → ∀ αs', ReLend αs' αs →
    (vwS δ [] σ d αs' ls' ─⋆ RCtx (ℍ := ℍ) δ σ S₀ αs' ls' Γ γ) τ

/-- **`[let]` at a row**: `M to x. N`. `M` runs as a piece; `N`'s context is the frame, its views
and the rest of what it holds re-lendable (`rctx_relendable`): dropped and frozen at each of `M`'s
full-depth stops and thawed at the next re-lend, carried live into the continuation at a stop
inside. At `M`'s answer, re-lendable, the β-step hands `N` its re-lendable context. One run is
`bodyH_bind`, every continuation `openH_bind`. The row's lenders' operations resume linearly
(`RowLin`). -/
theorem pj_let {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hLR : RowLin S₀ S) (hsp : Ctx.SplitP Γ Γ₁ Γ₂)
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₁ M (CTy.effOf S A))
    (hN : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.val (.lam N)) M) (CTy.effOf S B) := by
  refine pj_effOf_iff.mpr fun αs ls γ ρ hlen hch hΔ hg => ?_
  have hlr := linResume_rTab (ℍ := ℍ) (δ := δ) hLR B
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  let K : Kont := .appR (.val (.lam (Expr.psub 1 γ N))) .hole
  have hH : ∀ n, K.HasHnd n = false := fun n => by simp [K, Kont.HasHnd]
  let Fr : List Life → List SRec → WProp := fun αs' ls' => RCtx (ℍ := ℍ) δ σ S₀ αs' ls' Γ₂ γ
  let Fz : List Life → List Bool → List SRec → WProp := FzCtx (ℍ := ℍ) δ σ S₀ Γ₂ γ
  have hFs : ∀ αs' ls' ls'', (∀ x, x ∈ ls'' ↔ x ∈ ls') → Entails (Fr αs' ls') (Fr αs' ls'') :=
    fun _ _ _ hs τ h => rctx_local (ext_of_same hs τ) h
  have hFe : ∀ αs' d ls' ls'' τ, Ext ls' ls'' τ → Fz αs' d ls' τ → Fz αs' d ls'' τ :=
    fun _ _ _ _ _ hk h => ⟨h.1, fun l he => h.2 l (Ext.trans hk he)⟩
  have hFo : ∀ αs' d ls' τ, Fz αs' d ls' τ → stratS αs' τ := fun _ _ _ _ h => h.1
  have hfz : ∀ αs', αs'.length = σ.length → List.IsChain (· < ·) αs' → ∀ ls' τ,
      Fr αs' ls' τ → ∃ d τz τn, ResU.CompS τz τn τ ∧ Fz αs' d ls' τz ∧
        vwS δ [] σ d αs' ls' τn := by
    intro αs' hlen' _ ls' τ hF
    obtain ⟨d, τz, τn, hcz, hn, hz, hth⟩ := rctx_relendable hlen' hF
    exact ⟨d, τz, τn, hcz, ⟨hz, hth⟩, hn⟩
  have hthaw : ∀ αs' αs'' d ls' τz τv τ, ReLend αs'' αs' → Fz αs' d ls' τz →
      vwS δ [] σ d αs'' ls' τv → ResU.CompS τz τv τ → Fr αs'' ls' τ :=
    fun _ _ _ ls' τz _ _ hr hz hv hc' => hz.2 ls' (Ext.refl ls' τz) _ hr _ _ hv hc'
  -- at an answer of `M`: the β-step, then `N` from its re-lendable context
  have hk : ∀ αs', ReLend αs' αs → αs'.length = σ.length → ∀ ls' v,
      Entails (QA (ℍ := ℍ) δ σ S₀ (CTy.effOf S A) αs' ls' v ⋆ Fr αs' ls')
        (BHC (ℍ := ℍ) δ σ S₀ (CTy.effOf S B) αs' ls' (K.plug (.val v))) := by
    intro αs' hr hlen' ls' v τ ⟨τ₁, τ₂, hcτ, hv, hF⟩
    refine wpG_step (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ τ ?_
    rw [← substAll_cons_psub]
    obtain ⟨hl, hs⟩ := pure_sep_iff.mp hF
    have hv' : RSlot (ℍ := ℍ) δ σ S₀ A αs' ls' v τ₁ := by
      have := hv; simp only [QA] at this; rwa [rAns_effOf] at this
    refine pj_effOf_iff.mp hN αs' ls' (v :: γ) τ hlen' hr.2
      (fun αs'' hr' => hΔ αs'' (reLend_trans hr' hr)) (pure_sep_mk hl ?_)
    show (RSlot δ σ S₀ A αs' ls' v ⋆ rSep δ σ S₀ αs' ls' Γ₂ γ) τ
    exact ⟨τ₁, τ₂, hcτ, hv', hs⟩
  have hb := pj_effOf_iff.mp hM αs ls γ ρ₁ hlen hch hΔ hg₁
  simp only [BHC, OHC] at hb
  rw [rIn_effOf_ans S A B, rTab_effOf_ans S A B] at hb
  obtain ⟨hB₁, hB₀⟩ := openH_bind hlr K hH Fr Fz hFs hFe hFo hfz hthaw (B := αs)
    (fun αs' hle hlen' hch' => hk αs' ⟨hle, hch'⟩ hlen')
  exact bodyH_bind hlr K hH Fr Fz hFs hFe hFo (hfz αs hlen hch) (hthaw αs)
    (fun d₁ d₂ ls' e τ₁ τz τ hd hl₁ hl₂ hO hz hc' =>
      hB₁ hd hl₁ hl₂ (List.forall₂_same.mpr fun _ _ => le_rfl) hO hz hc')
    (fun αs' ls' e τ₁ τf τ hr hO hf hc' =>
      hB₀ ((List.Forall₂.length_eq hr.1).trans hlen) hr.1 hO hf hc')
    (hk αs (reLend_refl hch) hlen) hb hg₂ hc

/-! ### Values, eliminations, and closures -/

theorem substAll_cons₂' (w₂ w₁ : Val) (γ : List Val) (e : Expr) :
    substAll (w₂ :: w₁ :: γ) e =
      Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ e)) := by
  show Expr.psub 0 (w₂ :: w₁ :: γ) e = _
  rw [Expr.psub_cons₂ 0 w₂ w₁ γ e, Val.shift_zero]

/-- **`return V`** at a row: a value expression is a piece that does not stop. -/
theorem pj_of_pv {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy} {S : Row}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ V A) : PJ (ℍ := ℍ) δ σ S₀ Δ Γ V (CTy.effOf S A) := by
  refine pj_effOf_iff.mpr fun αs ls γ ρ hlen hch hΔ hg => ?_
  refine wpG_mono (fun ls' t τ hq => Or.inl ?_)
    ((wpTS_iff_wpG _ _ _ _).mp (h αs ls γ ρ hlen hch hΔ hg))
  obtain ⟨v, rfl, hv⟩ := hq
  exact ⟨v, rfl, by show RAns δ σ S₀ (CTy.effOf S A) αs ls' v τ; rw [rAns_effOf]; exact hv⟩

/-- **At `F A` the piece does not stop**: its table is empty and it catches nothing inside, so it
is a run to a re-lendable answer. -/
theorem wpTS_of_rc_ret {A : VTy} {αs : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : RC (ℍ := ℍ) δ σ S₀ (.ret A) αs ls e ρ) :
    wpTS ls e (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v) ρ := by
  rw [RC] at h
  refine (wpTS_iff_wpG _ _ _ _).mpr (wpG_mono (fun ls' t τ hq => ?_) h)
  rcases hq with hv | ⟨ds, ρ₁, ρ₂, -, -, hb, -⟩ | ⟨K, n, i, v, P, hp⟩
  · exact hv
  · rcases hb with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
    · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp
      simp [RTab, effTab, OpTab.empty] at hT
    · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp
      simp [RTab, effTab, OpTab.empty] at hT
  · obtain ⟨⟨-, -, hP⟩, -⟩ := pure_sep_iff.mp hp
    cases hP

/-- **A value judgment is the piece judgment at `F A`**, and back. -/
theorem pv_iff_pj {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy} :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ V A ↔ PJ (ℍ := ℍ) δ σ S₀ Δ Γ V (.ret A) :=
  ⟨fun h => pj_of_pv (S := []) h,
    fun h αs ls γ ρ hlen hch hΔ hg => wpTS_of_rc_ret (h αs ls γ ρ hlen hch hΔ hg)⟩

theorem pv_var {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.var i) A := by
  intro αs ls γ ρ _ hch _ hg
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg
  obtain ⟨v, hv, hval⟩ := rSep_soloP hch h (h.lt_of_liveWithin hl) hs
  rw [substAll_var' hv]
  exact wpTS_val ls v _ ρ hval

theorem pv_unit {Δ : LifeCtx} {Γ : Ctx VTy} (h : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val .unit) .unit := by
  intro αs ls γ ρ hlen hch _ hg
  obtain ⟨-, hs⟩ := pure_sep_iff.mp hg
  obtain rfl := rSep_deadP hch h hs
  exact wpTS_val ls Val.unit _ PMap.empty
    (relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a) fun _ _ _ _ => ⟨rfl, rfl⟩)

/-- **A pair of re-lendable values**, each with its own share. -/
theorem pv_pair {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e₁ e₂ : Expr} {A B : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (h₁ : PV (ℍ := ℍ) δ σ S₀ Δ Γ₁ e₁ A)
    (h₂ : PV (ℍ := ℍ) δ σ S₀ Δ Γ₂ e₂ B) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.pair e₁ e₂) (.tensor A B) := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine wpTS_bind_frame (.pairL .hole (substAll γ e₂)) (substAll γ e₁) ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v) (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γ₂ γ) _
    (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, h₁ αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v₁ τ ⟨τ₁, τ₂, hcτ, hv₁, hg₂'⟩
  refine wpTS_bind_frame (.pairR v₁ .hole) (substAll γ e₂) ls'
    (fun ls'' v => RSlot (ℍ := ℍ) δ σ S₀ B αs ls'' v)
    (fun ls'' => RSlot (ℍ := ℍ) δ σ S₀ A αs ls'' v₁) _
    (fun ls'' hls τ h => rslot_local A (ext_of_same hls τ) h) ?_ τ
    ⟨τ₂, τ₁, ResU.CompS.comm hcτ, h₂ αs ls' γ τ₂ hlen hch hΔ hg₂', hv₁⟩
  rintro ls'' - v₂ υ ⟨υ₁, υ₂, hcυ, hv₂, hv₁'⟩
  exact wpTS_val ls'' (.pair v₁ v₂) _ υ
    ⟨v₁, v₂, pure_sep_mk rfl ⟨υ₂, υ₁, ResU.CompS.comm hcυ, hv₁', hv₂⟩⟩

theorem pv_inj₁ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e A) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.inj₁ e) (.sum A B) := by
  intro αs ls γ ρ hlen hch hΔ hg
  refine wpTS_bind (.inj₁ .hole) (substAll γ e) ls _ ρ
    (wpTS_mono (fun ls' v τ hv => ?_) ρ (h αs ls γ ρ hlen hch hΔ hg))
  exact wpTS_val ls' (.inj₁ v) _ τ (Or.inl ⟨v, pure_sep_mk rfl hv⟩)

theorem pv_inj₂ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A B : VTy}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e B) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.inj₂ e) (.sum A B) := by
  intro αs ls γ ρ hlen hch hΔ hg
  refine wpTS_bind (.inj₂ .hole) (substAll γ e) ls _ ρ
    (wpTS_mono (fun ls' v τ hv => ?_) ρ (h αs ls γ ρ hlen hch hΔ hg))
  exact wpTS_val ls' (.inj₂ v) _ τ (Or.inr ⟨v, pure_sep_mk rfl hv⟩)

/-- **A value whose type is frozen**: Core's typing derives it, its type reads none of the
stack's variables and its values lie in `[top]`. -/
theorem pv_frozen {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy}
    (hd : CDerives Δ Γ V (.val A)) (hΓ : CtxNoThunk Γ) (hA : NoThunkT A)
    (hx : ∀ en ∈ σ, ¬ VFree en.x A)
    (hz : ∀ αs ls v ρ, αs.length = σ.length → List.IsChain (· < ·) αs →
      vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ → stratS αs ρ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ V A := by
  intro αs ls γ ρ hlen hch hΔ hg
  have hS : SemV Δ Γ V A := fundamentalC (ℍ := ℍ) hd
  exact wpTS_mono (fun ls' v τ hv => rslot_of_frozen A hA hx hlen hv (hz αs ls' v τ hlen hch hv)) ρ
    (hS (extS δ σ αs) γ ls ρ (hΔ αs (reLend_refl hch)) (rctx_gDenC hch hΓ hg))

/-- **`[perform]` at an operation caught inside the borrower**: its name is not the lenders'.
The argument is any re-lendable value; the stop drops no view, and its continuation, holding
nothing, is at every re-lend and on every re-lendable answer that answer. -/
theorem pj_performIn {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S o.n o.i = some o) (hout : outN S₀ o.n = false)
    (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γ V o.A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) := by
  refine pj_effOf_iff.mpr fun αs ls γ ρ hlen hch hΔ hg => ?_
  change wpG ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ ρ
  refine wpG_bind_pure _ _ ls _ ρ
    (wpTS_mono (fun ls' v τ hv => ?_) ρ (hV αs ls γ ρ hlen hch hΔ hg))
  refine wpG_here _ _ _ τ (Or.inr (Or.inr ⟨.hole, o.n, o.i, v, _, pure_sep_mk
    ⟨rfl, rfl, rIn_effOf_find o.B S hf hout⟩ ⟨τ, PMap.empty, ResU.comp_empty_right τ, hv, ?_⟩⟩))
  refine relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a)
    fun ls'' _ αs' _ w τw τ' hw hc => ?_
  rw [eq_of_compS_empty_left hc]
  refine openH_zero_fold fun _ => wpG_here _ _ _ τw (Or.inl ⟨w, rfl, ?_⟩)
  show RAns δ σ S₀ (CTy.effOf S o.B) αs' ls'' w τw
  rw [rAns_effOf]; exact hw

/-- **A closure built by the borrower** (`[λ]`, `thunk` at `A ⊸ C`): its environment, re-lendable,
is its frozen share; called at a re-lend on a re-lendable argument, the β-step hands the body its
re-lendable context, and the body is in `RC C`. -/
theorem rslot_lam {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ) M C)
    {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes} (hlen : αs.length = σ.length)
    (hΔ : ∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs'))
    (hg : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) :
    RSlot (ℍ := ℍ) δ σ S₀ (.thunk (.arr A C)) αs ls ⟨.lam (Expr.psub 1 γ M), .lam⟩ ρ := by
  have hr := rctx_relendable hlen hg
  rw [RSlot]
  refine relendableS_mono_rel ?_ ρ hr
  intro αs' ls' hr' τ hτ
  show RC δ σ S₀ (.arr A C) αs' ls' (.val ⟨.lam (Expr.psub 1 γ M), .lam⟩) τ
  rw [RC]
  intro v τv τ' hv hc'
  refine rc_head C (fun μ => Head.beta μ (Expr.psub 1 γ M) v) rfl αs' ls' τ' ?_
  rw [← substAll_cons_psub]
  obtain ⟨hl', hs'⟩ := pure_sep_iff.mp hτ
  refine hM αs' ls' (v :: γ) τ' ((List.Forall₂.length_eq hr'.1).trans hlen) hr'.2
    (fun αs'' h'' => hΔ αs'' (reLend_trans h'' hr')) (pure_sep_mk hl' ?_)
  show (RSlot δ σ S₀ A αs' ls' v ⋆ rSep δ σ S₀ αs' ls' Γ γ) τ'
  exact ⟨τv, τ, ResU.CompS.comm hc', hv, hs'⟩

theorem pv_lam {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ) M C) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.thunk (.arr A C)) := by
  intro αs ls γ ρ hlen _ hΔ hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  exact wpTS_val ls _ _ ρ (rslot_lam hM hlen hΔ hg)

/-- **Calling a closure** (`[app]` of `force f` at `A ⊸ C`, the argument a variable): at the
current lifetimes the closure's re-lendable reading, applied to the argument's re-lendable
value. -/
theorem pj_call {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {k j : Nat} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hk : Ctx.SoloP Γ₁ k (.thunk (.arr A C))) (hj : Ctx.SoloP Γ₂ j A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.var k) (.var j)) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  obtain ⟨hl₁, hs₁⟩ := pure_sep_iff.mp hg₁
  obtain ⟨hl₂, hs₂⟩ := pure_sep_iff.mp hg₂
  obtain ⟨f, hf, hfv⟩ := rSep_soloP hch hk (hk.lt_of_liveWithin hl₁) hs₁
  obtain ⟨v, hv, hvv⟩ := rSep_soloP hch hj (hj.lt_of_liveWithin hl₂) hs₂
  show RC δ σ S₀ C αs ls (.app (substAll γ (.var k)) (substAll γ (.var j))) ρ
  rw [substAll_var' hf, substAll_var' hv]
  rw [RSlot] at hfv
  have h := relendableS_now hch hfv
  simp only [forceE] at h
  rw [RC] at h
  exact h v ρ₂ ρ hvv hc

/-- **Resuming a continuation** (`[app]` of `[proj₁]` of `force κ` at `(B ⊸ C) & ⊤`, the answer
a variable): at the current lifetimes the continuation's re-lendable reading, resumed on the
answer's re-lendable value. -/
theorem pj_resume {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {k j : Nat} {A : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hk : Ctx.SoloP Γ₁ k (.thunk (.amp (.arr A C) .top)))
    (hj : Ctx.SoloP Γ₂ j A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.app (.var k) (.val (.inj₁ .unit))) (.var j)) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  obtain ⟨hl₁, hs₁⟩ := pure_sep_iff.mp hg₁
  obtain ⟨hl₂, hs₂⟩ := pure_sep_iff.mp hg₂
  obtain ⟨f, hf, hfv⟩ := rSep_soloP hch hk (hk.lt_of_liveWithin hl₁) hs₁
  obtain ⟨v, hv, hvv⟩ := rSep_soloP hch hj (hj.lt_of_liveWithin hl₂) hs₂
  show RC δ σ S₀ C αs ls (.app (.app (substAll γ (.var k)) (substAll γ (.val (.inj₁ .unit))))
    (substAll γ (.var j))) ρ
  rw [substAll_var' hf, substAll_var' hv]
  rw [RSlot] at hfv
  have h := relendableS_now hch hfv
  simp only [forceE] at h
  rw [RC] at h
  have h₁ := h.1
  rw [RC] at h₁
  exact h₁ v ρ₂ ρ hvv hc

/-- **`case V {inj₁ x. M₁ | inj₂ y. M₂}`**: a branch on a re-lendable value; the branch taken is in
`RC C`, its context the payload's re-lendable value beside the rest. -/
theorem pj_case {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {V M₁ M₂ : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γs Γb) (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γs V (.sum A B))
    (h₁ : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γb) M₁ C)
    (h₂ : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨B, true⟩ :: Γb) M₂ C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.case V M₁ M₂) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine rc_bind C (.case .hole (Expr.psub 1 γ M₁) (Expr.psub 1 γ M₂)) (substAll γ V) αs ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ (.sum A B) αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γb γ)
    (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, hcτ, hsum, hg₂'⟩
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg₂'
  rcases hsum with ⟨w, hq⟩ | ⟨w, hq⟩
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hq
    refine rc_head C (fun μ => Head.case₁ μ w _ _) rfl αs ls' τ ?_
    rw [← substAll_cons_psub]
    exact h₁ αs ls' (w :: γ) τ hlen hch hΔ (pure_sep_mk hl ⟨τ₁, τ₂, hcτ, hw, hs⟩)
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hq
    refine rc_head C (fun μ => Head.case₂ μ w _ _) rfl αs ls' τ ?_
    rw [← substAll_cons_psub]
    exact h₂ αs ls' (w :: γ) τ hlen hch hΔ (pure_sep_mk hl ⟨τ₁, τ₂, hcτ, hw, hs⟩)

/-- **`let (x, y) = V in M`**: the pair's components, re-lendable each with its own share. -/
theorem pj_letpair {Δ : LifeCtx} {Γ Γp Γb : Ctx VTy} {V M : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γp Γb) (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γp V (.tensor A B))
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.letpair V M) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine rc_bind C (.letpair .hole (Expr.psub 2 γ M)) (substAll γ V) αs ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ (.tensor A B) αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γb γ)
    (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, hcτ, hpair, hg₂'⟩
  obtain ⟨w₁, w₂, hq⟩ := hpair
  obtain ⟨rfl, b₁, b₂, hcb, hw₁, hw₂⟩ := pure_sep_iff.mp hq
  refine rc_head C (fun μ => Head.letpair μ w₁ w₂ _) rfl αs ls' τ ?_
  rw [← substAll_cons₂']
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg₂'
  obtain ⟨x, hx, hxτ⟩ := compS_reassoc hcb hcτ
  obtain ⟨y, hy, hyτ⟩ := compS_lcomm hx hxτ
  exact hM αs ls' (w₂ :: w₁ :: γ) τ hlen hch hΔ
    (pure_sep_mk (by simpa using hl) ⟨b₂, y, hyτ, hw₂, ⟨b₁, τ₂, hy, hw₁, hs⟩⟩)

/-- **`V; M`** for `V : 1`. -/
theorem pj_seq {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V M : Expr} {C : CTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γ₁ V .unit)
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₂ M C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.seq V M) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine rc_bind C (.seq .hole (substAll γ M)) (substAll γ V) αs ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ .unit αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γ₂ γ)
    (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, hcτ, hu, hg₂'⟩
  have hu' := relendableS_now hch hu
  obtain ⟨rfl, rfl⟩ := hu'
  rw [eq_of_compS_empty_left hcτ]
  exact rc_head C (fun μ => Head.seq μ _) rfl αs ls' τ₂ (hM αs ls' γ τ₂ hlen hch hΔ hg₂')

/-! ### Persistent values, and loops -/

/-- A unit, frozen. -/
theorem rslot_unit {αs : List Life} (hlen : αs.length = σ.length) (ls : List SRec) :
    RSlot (ℍ := ℍ) δ σ S₀ .unit αs ls .unit PMap.empty :=
  relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a) fun _ _ _ _ => ⟨rfl, rfl⟩

/-- Dereliction: `!A`'s value at `∅` is `A`'s. -/
theorem pv_bangE {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ e (.bang A)) : PV (ℍ := ℍ) δ σ S₀ Δ Γ e A :=
  fun αs ls γ ρ hlen hch hΔ hg =>
    wpTS_mono (fun _ _ _ hv => hv.2) ρ (h αs ls γ ρ hlen hch hΔ hg)

/-- A context whose live slots are persistent holds nothing. -/
theorem rSep_persistent_empty {αs : List Life} {ls : List SRec} :
    ∀ (Γ : Ctx VTy) (γ : List Val) {ρ : WRes}, Persistent Γ →
      rSep (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ → ρ = PMap.empty := by
  intro Γ
  induction Γ with
  | nil => intro γ ρ _ h; cases γ <;> exact h.1
  | cons sl Γ ih =>
      intro γ ρ hp h
      cases γ with
      | nil => exact h.1
      | cons v γ =>
          unfold rSep at h
          by_cases hl : sl.live = true
          · rw [if_pos hl] at h
            obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
            obtain ⟨A₀, hA₀⟩ := hp sl (List.mem_cons_self ..) hl
            rw [hA₀] at h₁
            obtain rfl := h₁.1
            obtain rfl := ih γ (fun s hs hl' => hp s (List.mem_cons_of_mem _ hs) hl') h₂
            exact eq_of_compS_empty_left hc
          · rw [if_neg hl] at h
            exact ih γ (fun s hs hl' => hp s (List.mem_cons_of_mem _ hs) hl') h

/-- **A persistent closure** (`[!thunkV]` over `!Γ` at `A ⊸ C`): its environment holds nothing,
and called at any re-lend on a re-lendable argument its body is in `RC C`. -/
theorem pv_bangLam {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {C : CTy}
    (hp : Persistent Γ) (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ) M C) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.bang (.thunk (.arr A C))) := by
  intro αs ls γ ρ hlen hch hΔ hg
  have hρ : ρ = PMap.empty := by
    obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg
    exact rSep_persistent_empty Γ γ hp hs
  subst hρ
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ PMap.empty
  exact wpTS_val ls _ _ PMap.empty ⟨rfl, rslot_lam hM hlen hΔ hg⟩

/-- **The self-reference of a loop is a closure**, at every budget, by induction on the budget:
`inj₁ ()` once spent; at `j + 1`, called at a re-lend on a re-lendable argument it steps to the
loop at `j`, which runs the step — re-lendable at every re-lend, holding nothing — on the
self-reference at `j`. -/
theorem rslot_fixSelf {A : VTy} {C : CTy} {s : Val} {Bd : List Life}
    (hs : ∀ αs ls, ReLend αs Bd →
      RSlot (ℍ := ℍ) δ σ S₀ (fixStepTy A C) αs ls s PMap.empty) :
    ∀ (m : Nat) (k : UInt32), k.toNat = m → ∀ αs ls, ReLend αs Bd → αs.length = σ.length →
      RSlot (ℍ := ℍ) δ σ S₀ (fixSelfTy A C) αs ls (fixSelf s k) PMap.empty
  | 0, k, hk, αs, ls, _, hlen => by
      have hk0 : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
      unfold fixSelf
      rw [if_pos hk0]
      exact Or.inl ⟨Val.unit, pure_sep_mk rfl (rslot_unit hlen ls)⟩
  | j + 1, k, hk, αs, ls, hr, hlen => by
      have hk0 : k ≠ 0 := fun h => by subst h; simp at hk
      have hkj : (k - 1).toNat = j := by
        have : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt32.toNat_sub_of_le]
          · rfl
          · rw [UInt32.le_iff_toNat_le]; simp; omega
        omega
      unfold fixSelf
      rw [if_neg hk0]
      refine Or.inr ⟨_, pure_sep_mk rfl ⟨rfl, ?_⟩⟩
      rw [RSlot]
      refine relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a)
        fun ls' _ αs' hr' => ?_
      show RC δ σ S₀ (.arr A C) αs' ls' (.val _) PMap.empty
      rw [RC]
      intro x ρx τ hx hc
      rw [eq_of_compS_empty_left hc]
      refine rc_step C (fun μ => Step1N.head (Head.beta μ _ x) rfl) αs' ls' ρx ?_
      rw [fixSelf_body_subst]
      refine rc_step C (fun μ => Step1N.head (Head.boundedFix μ s (k - 1) x) rfl) αs' ls' ρx ?_
      have hr'' : ReLend αs' Bd := reLend_trans hr' hr
      have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr'.1).trans hlen
      obtain ⟨-, hs'⟩ := hs αs' ls' hr''
      rw [RSlot] at hs'
      have hnow := relendableS_now hr'.2 hs'
      simp only [forceE] at hnow
      rw [RC] at hnow
      exact hnow (Val.pair (fixSelf s (k - 1)) x) ρx ρx
        ⟨fixSelf s (k - 1), x, pure_sep_mk rfl
          ⟨PMap.empty, ρx, compS_empty_left ρx,
            rslot_fixSelf hs j (k - 1) hkj αs' ls' hr'' hlen', hx⟩⟩ (compS_empty_left ρx)

/-- **`bounded_fix` is a closure**, at every computation type: called at a re-lend on
`(s, (k, a))`, it steps to the step on its self-reference (`rslot_fixSelf`) and the argument. The
step holds nothing, so it is re-lendable at every later re-lend. -/
theorem rslot_boundedFix {A : VTy} {C : CTy} {αs : List Life} (hlen : αs.length = σ.length)
    (ls : List SRec) :
    RSlot (ℍ := ℍ) δ σ S₀ (boundedFixTy A C) αs ls (Val.prim .boundedFix) PMap.empty := by
  refine ⟨rfl, ?_⟩
  rw [RSlot]
  refine relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a)
    fun ls' _ αs' hr => ?_
  show RC δ σ S₀ (.arr _ C) αs' ls' (.val _) PMap.empty
  rw [RC]
  intro v ρv τ hv hc
  rw [eq_of_compS_empty_left hc]
  have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr.1).trans hlen
  obtain ⟨s, w, hq⟩ := hv
  obtain ⟨rfl, ρs, ρw, hcw, ⟨rfl, hs⟩, hw⟩ := pure_sep_iff.mp hq
  obtain ⟨kv, a, hq'⟩ := hw
  obtain ⟨rfl, ρk, ρa, hck, hk, ha⟩ := pure_sep_iff.mp hq'
  obtain ⟨rfl, k, rfl⟩ := relendableS_now hr.2 hk
  rw [eq_of_compS_empty_left hcw, eq_of_compS_empty_left hck]
  refine rc_step C (fun μ => Step1N.head (Head.boundedFix μ s k a) rfl) αs' ls' ρa ?_
  have hsall : ∀ αs'' ls'', ReLend αs'' αs' →
      RSlot (ℍ := ℍ) δ σ S₀ (fixStepTy A C) αs'' ls'' s PMap.empty := by
    intro αs'' ls'' hr''
    refine ⟨rfl, ?_⟩
    have hs₁ := hs
    rw [RSlot] at hs₁ ⊢
    exact relendableS_empty (relendableS_idem hs₁) ls'' (ext_empty' _ _) αs'' hr''
  have hs₂ := hs
  rw [RSlot] at hs₂
  have hnow := relendableS_now hr.2 hs₂
  simp only [forceE] at hnow
  rw [RC] at hnow
  exact hnow (Val.pair (fixSelf s k) a) ρa ρa
    ⟨fixSelf s k, a, pure_sep_mk rfl
      ⟨PMap.empty, ρa, compS_empty_left ρa,
        rslot_fixSelf hsall k.toNat k rfl αs' ls' (reLend_refl hr.2) hlen', ha⟩⟩
    (compS_empty_left ρa)

/-- `bounded_fix` as a value of the borrower: the constant, at a consumed context. -/
theorem pv_boundedFix {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} {C : CTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .boundedFix)) (boundedFixTy A C) := by
  intro αs ls γ ρ hlen hch _ hg
  obtain ⟨-, hs⟩ := pure_sep_iff.mp hg
  obtain rfl := rSep_deadP hch hΓ hs
  exact wpTS_val ls _ _ PMap.empty (rslot_boundedFix hlen ls)

/-! ### From the piece judgment to D16.1's piece -/

/-- **The piece is monotone in its answer at the stack's length**: every vector a run answers at
is a re-lend of the stack, of its length. -/
theorem openH_mono_Q {To : OpTab} {RI : UInt32 → UInt32 → Option InRel}
    {Q Q' : List Life → List SRec → Val → WProp}
    (hQ : ∀ αs ls v, List.IsChain (· < ·) αs → αs.length = σ.length →
      Entails (Q αs ls v) (Q' αs ls v)) {k : Nat} {ds : List Bool} {αi αo : List Life}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hl : (αi ++ αo).length = σ.length)
    (h : OpenH δ σ To RI Q k ds αi αo ls e ρ) : OpenH δ σ To RI Q' k ds αi αo ls e ρ := by
  let Mot : XT := fun k ds αi αo ls e ρ => (αi ++ αo).length = σ.length →
    OpenH δ σ To RI Q' k ds αi αo ls e ρ
  refine h Mot ?_ hl
  intro k ds αi αo ls e ρ hF hl
  refine openH_fold fun αi' hlt hch => ?_
  have hl' : (αi' ++ αo).length = σ.length := by
    rw [List.length_append, hlt.length_eq]; simpa using hl
  exact boxTop_mono (wand_mono_right (bodyH_mono' (fun ls v => hQ _ ls v hch hl')
    (fun _ _ _ _ hM => hM (by simpa using hl'))
    (fun _ _ _ _ hr hM => hM (by simpa using hr.1.length_eq.trans hl')))) ρ (hF αi' hlt hch)

theorem forall₂_le_lt : ∀ {a b c : List Life}, List.Forall₂ (· ≤ ·) a b →
    List.Forall₂ (· < ·) b c → List.Forall₂ (· < ·) a c
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ =>
      .cons (lt_of_le_of_lt h₁ h₂) (forall₂_le_lt t₁ t₂)

/-- **The piece judgment gives D16.1's piece**, at the lenders' row (`rTab_self`), nothing of which
is caught inside. At every re-lend below `αi` the views handed rebuild the borrower's context
re-lendably, beside garbage (`hctx`); every re-lend models `Δ` (`hΔ`). The piece holds nothing of
its own. -/
theorem openS_of_pj (hx : AllCross σ (Row.tab S₀ δ)) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr}
    {B : VTy} (hpj : PJ (ℍ := ℍ) δ σ S₀ Δ Γ M (CTy.effOf S₀ B))
    {Q : List Life → List SRec → Val → WProp}
    (hQ : ∀ αs ls v, List.IsChain (· < ·) αs → αs.length = σ.length →
      Entails (RSlot (ℍ := ℍ) δ σ S₀ B αs ls v) (Q αs ls v))
    {ds : List Bool} {αi : List Life} {ls : List SRec} {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ρv, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρg) :
    OpenS δ σ (Row.tab S₀ δ) Q σ.length ds αi [] ls (substAll γ M) PMap.empty := by
  have hRI : ∀ n i, RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S₀ B) n i = none :=
    rIn_effOf_none B S₀ fun o ho => outN_of_mem ho
  have hQ' : ∀ αs ls v, List.IsChain (· < ·) αs → αs.length = σ.length →
      Entails (QA (ℍ := ℍ) δ σ S₀ (CTy.effOf S₀ B) αs ls v) (Q αs ls v) := by
    intro αs ls v hch hlen τ hq
    simp only [QA] at hq; rw [rAns_effOf] at hq
    exact hQ αs ls v hch hlen τ hq
  have hx' : AllCross σ (RTab (ℍ := ℍ) δ S₀ (CTy.effOf S₀ B)) := by
    rw [rTab_self]; exact hx
  have hO : OpenH δ σ (RTab (ℍ := ℍ) δ S₀ (CTy.effOf S₀ B))
      (RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S₀ B)) Q σ.length ds αi [] ls (substAll γ M)
      PMap.empty := by
    refine openH_fold fun αi' hlt hch => ?_
    rw [List.append_nil] at hch ⊢
    refine ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
    rw [List.take_length] at hw
    rw [eq_of_compS_empty_left hc]
    have hlen : αi'.length = σ.length := (vwS_length hw).2
    obtain ⟨ρg, ρd, hcg, hno, hg⟩ := hctx αi' w hlt hch hw
    have hb := pj_effOf_iff.mp hpj αi' ls γ ρg hlen hch
      (fun αs'' hr => hΔ αs'' (forall₂_le_lt hr.1 hlt) hr.2) hg
    refine wpG_absorb ?_ hno hcg
    exact bodyH_mono' (fun ls v => hQ' αi' ls v hch hlen)
      (fun _ _ _ _ hO => openH_mono_Q hQ' (by simpa using hlen) hO)
      (fun _ _ _ _ hr hO => openH_mono_Q hQ' (by simpa using hr.1.length_eq.trans hlen) hO) _ hb
  have := openS_of_openH hx' hRI hO
  rwa [rTab_self] at this

end piece

end Law2

end
