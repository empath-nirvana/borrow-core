import Law2.Inner

/-!
# Law2 — re-lendable values and contexts at the stack

A borrower holding a stack `σ` of lends open across its stops runs, at each re-lend, from a
context the lenders' fresh views rebuild. Between stops it computes values, and the ones held
across a stop are frozen with the frame that holds them and thawed at the next re-lend. What a
value must satisfy for that is **re-lendability** (GhostEnd's `RelendableS`): its resource splits
into the views it holds at the current lifetimes and a part in `[top]`, and at every re-lend that
part, handed the views made afresh, is again in the relation.

`RSlot σ S₀ A` is that predicate read along `A`'s shape, `S₀` the lenders' row: componentwise at
`⊗` and `⊕`, so that a pair's components re-lend each with its own share; at a closure that stops,
`U(A ⊸ F_Σ B)`, called on a re-lendable argument at every re-lend it is the piece; at a
continuation a handler installed inside the borrower hands its clause, `U((B ⊸ F_Σ R) & ⊤)`,
resumed on a re-lendable answer at every re-lend it is the piece; at `!A`, `A`'s at `∅`; at every
other type the kernel's relation at every re-lend. The piece is `OpenH` (`Law2/Inner.lean`): the
operations of `Σ` outside `S₀` are caught by a handler inside the borrower (`RIn`), those of `S₀`
cross every lend. `RCtx` is `⊛` of `RSlot` over a context's live slots.

* `relendableS_idem`, `rslot_relendable`, `rctx_relendable`: a re-lendable value or context is
  re-lendable *as such* — frozen at a stop and thawed at a re-lend, it is again an `RSlot`
  (`RCtx`). This is the frame a bind carries across its inner piece's stops.
* `rctx_split`: `RCtx` splits along `Ctx.SplitP`, a persistent slot to both sides.
* `rslot_vC`, `rctx_gDenC`: at the current lifetimes a re-lendable value is in the kernel's
  relation, away from closures that stop and continuations (`NoEffT`).
* `rslot_of_frozen`: a value whose type reads none of the stack's variables and whose resource
  lies in `[top]` is re-lendable, its whole share frozen and no view held.
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

mutual
/-- **Re-lendable values** at the stack `σ`, its lends at `αs`, the lenders' row `S₀`.
Componentwise at `⊗` and `⊕`; at a closure that stops (`U(A ⊸ F_Σ B)`), called at every re-lend on
a re-lendable argument, the piece; at a continuation (`U((A ⊸ F_Σ B) & ⊤)`), resumed at every
re-lend on a re-lendable answer, the piece; at `!A`, `A`'s at `∅`; elsewhere re-lendable at the
kernel's relation. -/
def RSlot (δ : LSub) (σ : LStack) (S₀ : Row) : VTy → List Life → List SRec → Val → WProp
  | .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      RSlot δ σ S₀ A αs ls v₁ ⋆ RSlot δ σ S₀ B αs ls v₂
  | .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ RSlot δ σ S₀ A αs ls v₁)
        (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ RSlot δ σ S₀ B αs ls v₂)
  | .thunk (.arr A (.eff n i q A' B' fin C)), αs, ls, f =>
      RelendableS δ [] σ (fun αs' ls' ρ => ∀ v, (RSlot δ σ S₀ A αs' ls' v ─⋆
        bodyH δ σ (Row.tab S₀ δ) (fun m j => RIn δ σ S₀ (.eff n i q A' B' fin C) m j)
          (fun αs'' ls'' w => RAns δ σ S₀ C αs'' ls'' w)
          (OpenH δ σ (Row.tab S₀ δ) (fun m j => RIn δ σ S₀ (.eff n i q A' B' fin C) m j)
            (fun αs'' ls'' w => RAns δ σ S₀ C αs'' ls'' w))
          αs' ls' (.app (.val f) (.val v))) ρ) αs ls
  | .thunk (.amp (.arr A (.eff n i q A' B' fin C)) .top), αs, ls, f =>
      RelendableS δ [] σ (fun αs' ls' ρ => ∀ v, (RSlot δ σ S₀ A αs' ls' v ─⋆
        bodyH δ σ (Row.tab S₀ δ) (fun m j => RIn δ σ S₀ (.eff n i q A' B' fin C) m j)
          (fun αs'' ls'' w => RAns δ σ S₀ C αs'' ls'' w)
          (OpenH δ σ (Row.tab S₀ δ) (fun m j => RIn δ σ S₀ (.eff n i q A' B' fin C) m j)
            (fun αs'' ls'' w => RAns δ σ S₀ C αs'' ls'' w))
          αs' ls' (.app (.app (.val f) (.val (.inj₁ .unit))) (.val v))) ρ) αs ls
  | .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ RSlot δ σ S₀ A αs ls v ρ
  | A, αs, ls, v =>
      RelendableS δ [] σ (fun αs' ls' => vCE (ℍ := ℍ) none true A ls' (extS δ σ αs') v) αs ls
termination_by structural A => A
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

/-- A type `RSlot` reads at the kernel's relation: not `⊗`, not `⊕`, not a closure that stops,
not a continuation, not `!`. -/
def LeafR (A : VTy) : Prop :=
  (∀ A₁ A₂, A ≠ .tensor A₁ A₂) ∧ (∀ A₁ A₂, A ≠ .sum A₁ A₂) ∧
    (∀ A' n i q A₂ B fin C, A ≠ .thunk (.arr A' (.eff n i q A₂ B fin C))) ∧
    (∀ A' n i q A₂ B fin C, A ≠ .thunk (.amp (.arr A' (.eff n i q A₂ B fin C)) .top)) ∧
    ∀ A', A ≠ .bang A'

/-- The kernel's types at which `RSlot` reads the kernel's relation. -/
macro "leafR_tac" : tactic => `(tactic| exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
  ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ _ _ _ _ _ _ _ h => nomatch h),
    (fun _ _ _ _ _ _ _ _ h => nomatch h), (fun _ h => nomatch h)⟩)))))

/-- The shapes `RSlot` reads. -/
theorem vty_shape (A : VTy) : (∃ A₁ A₂, A = .tensor A₁ A₂) ∨ (∃ A₁ A₂, A = .sum A₁ A₂) ∨
    (∃ A' n i q A₂ B fin C, A = .thunk (.arr A' (.eff n i q A₂ B fin C))) ∨
    (∃ A' n i q A₂ B fin C, A = .thunk (.amp (.arr A' (.eff n i q A₂ B fin C)) .top)) ∨
    (∃ A', A = .bang A') ∨ LeafR A := by
  cases A with
  | tensor A₁ A₂ => exact Or.inl ⟨_, _, rfl⟩
  | sum A₁ A₂ => exact Or.inr (Or.inl ⟨_, _, rfl⟩)
  | bang A' => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))
  | thunk C =>
      cases C with
      | arr A' C' =>
          cases C' with
          | eff n i q A₂ B fin C => exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, _, rfl⟩))
          | _ => leafR_tac
      | amp C₁ C₂ =>
          cases C₁ with
          | arr A' C' =>
              cases C' with
              | eff n i q A₂ B fin C =>
                  cases C₂ with
                  | top => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, _, rfl⟩)))
                  | _ => leafR_tac
              | _ => leafR_tac
          | _ => leafR_tac
      | _ => leafR_tac
  | _ => leafR_tac

theorem rslot_leaf {A : VTy} (hA : LeafR A) (αs : List Life) (ls : List SRec) (v : Val) :
    RSlot (ℍ := ℍ) δ σ S₀ A αs ls v =
      RelendableS δ [] σ (fun αs' ls' => vCE (ℍ := ℍ) none true A ls' (extS δ σ αs') v) αs ls := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hA
  cases A with
  | tensor A₁ A₂ => exact absurd rfl (h₁ A₁ A₂)
  | sum A₁ A₂ => exact absurd rfl (h₂ A₁ A₂)
  | bang A' => exact absurd rfl (h₅ A')
  | thunk C =>
      cases C with
      | arr A' C' =>
          cases C' with
          | eff n i q A₂ B fin C => exact absurd rfl (h₃ A' n i q A₂ B fin C)
          | _ => rfl
      | amp C₁ C₂ =>
          cases C₁ with
          | arr A' C' =>
              cases C' with
              | eff n i q A₂ B fin C =>
                  cases C₂ with
                  | top => exact absurd rfl (h₄ A' n i q A₂ B fin C)
                  | _ => rfl
              | _ => rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

theorem rslot_leaf_fun {A : VTy} (hA : LeafR A) (v : Val) :
    (fun αs ls => RSlot (ℍ := ℍ) δ σ S₀ A αs ls v) =
      fun αs ls => RelendableS δ [] σ
        (fun αs' ls' => vCE (ℍ := ℍ) none true A ls' (extS δ σ αs') v) αs ls :=
  funext fun αs => funext fun ls => rslot_leaf hA αs ls v

/-- **A re-lendable value is re-lendable as such**: frozen at a stop and thawed at a re-lend, it
is a re-lendable value again. Componentwise at `⊗` and `⊕` (`relendableS_sep`); at a closure that
stops and at the kernel's types, by `relendableS_idem`. -/
theorem rslot_relendable (A : VTy) : ∀ {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes},
    RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ →
      RelendableS δ [] σ (fun αs' ls' => RSlot (ℍ := ℍ) δ σ S₀ A αs' ls' v) αs ls ρ := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ |
    ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ | ⟨A', rfl⟩ | hA
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
    rw [rslot_leaf hA] at h
    rw [rslot_leaf_fun hA]
    exact relendableS_idem h
termination_by sizeOf A

/-- A type with no closure that stops and no continuation at a position `RSlot` reads
componentwise. -/
def NoEffT : VTy → Prop
  | .tensor A B => NoEffT A ∧ NoEffT B
  | .sum A B => NoEffT A ∧ NoEffT B
  | .thunk (.arr _ (.eff _ _ _ _ _ _ _)) => False
  | .thunk (.amp (.arr _ (.eff _ _ _ _ _ _ _)) .top) => False
  | .bang A => NoEffT A
  | _ => True

/-- **A re-lendable value of a persistent type holds nothing**: at the current lifetimes it is in
the kernel's relation, which holds such a value only at `∅`. -/
theorem rslot_persistent_empty (A : VTy) (hp : A.Persistent) : ∀ {αs : List Life}
    {ls : List SRec} {v : Val} {ρ : WRes}, List.IsChain (· < ·) αs →
      RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ → ρ = PMap.empty := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ |
    ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ | ⟨A', rfl⟩ | hA
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
  · simp [VTy.Persistent, VTy.persistent] at hp
  · intro αs ls v ρ _ h
    exact h.1
  · intro αs ls v ρ hch h
    rw [rslot_leaf hA] at h
    exact vP_empty_of_persistent hp (relendableS_now hch h)
termination_by sizeOf A

/-- **At the current lifetimes a re-lendable value is in the kernel's relation**, away from
closures that stop. -/
theorem rslot_vC (A : VTy) (hA : NoEffT A) : ∀ {αs : List Life} {ls : List SRec} {v : Val}
    {ρ : WRes}, List.IsChain (· < ·) αs → RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ →
      vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ |
    ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ | ⟨A', rfl⟩ | hL
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
  · exact hA.elim
  · intro αs ls v ρ hch h
    exact ⟨h.1, rslot_vC A' hA hch h.2⟩
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

/-- Every live slot's type is free of thunks that stop. -/
def CtxNoEffT (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → NoEffT s.ty

/-- **At the current lifetimes a re-lendable context is in `𝒢⟦Γ⟧`**, away from thunks that
stop. -/
theorem rSep_gSepC {αs : List Life} (hch : List.IsChain (· < ·) αs) {ls : List SRec} :
    ∀ (Γ : Ctx VTy) (γ : List Val), CtxNoEffT Γ → ∀ {ρ : WRes},
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
    {Γ : Ctx VTy} (hΓ : CtxNoEffT Γ) {γ : List Val} {ρ : WRes}
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
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ |
    ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ | ⟨A', rfl⟩ | hA
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
    exact relendableS_local hk h
  · intro αs ls ls' v ρ hk h
    exact ⟨h.1, rslot_local A' hk h.2⟩
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

/-- **A frozen value is re-lendable**: a value of a type that reads none of the stack's
variables, whose resource lies in `[top]`, holds no view; its share is frozen whole and its
relation is the same at every re-lend. -/
theorem rslot_of_frozen (A : VTy) (hA : NoEffT A) (hx : ∀ e ∈ σ, ¬ VFree e.x A) :
    ∀ {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes}, αs.length = σ.length →
      vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ → stratS αs ρ →
      RSlot (ℍ := ℍ) δ σ S₀ A αs ls v ρ := by
  rcases vty_shape A with ⟨A₁, A₂, rfl⟩ | ⟨A₁, A₂, rfl⟩ | ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ |
    ⟨A', n, i, q, A₂, B, fin, C, rfl⟩ | ⟨A', rfl⟩ | hL
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
  · exact hA.elim
  · intro αs ls v ρ hlen h hz
    exact ⟨h.1, rslot_of_frozen A' hA (fun e he hv => hx e he hv) hlen h.2 hz⟩
  · intro αs ls v ρ hlen h hz
    rw [rslot_leaf hL]
    refine relendableS_frozen hlen hz fun ls' he αs' _ => ?_
    rw [vC_extS_of_not_free true ls' σ αs' hx]
    rw [vC_extS_of_not_free true ls σ αs hx] at h
    exact vC_local true A he h
termination_by sizeOf A

end local_

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

/-- The answer predicate of a piece at the computation type `C`. -/
abbrev QA (δ : LSub) (σ : LStack) (S₀ : Row) (C : CTy) : List Life → List SRec → Val → WProp :=
  fun αs ls v => RAns (ℍ := ℍ) δ σ S₀ C αs ls v

/-- **The piece judgment.** At every lifetime vector of the stack, in nesting order, whose
re-lends all model `Δ`, from a re-lendable context, the term runs as the piece at the lenders'
row `S₀` and the operations `C`'s row has beside it caught inside (`RIn`): to an answer
re-lendable at `C`'s answer type, or to a stop whose continuations are the piece again. It is the
semantic judgment GFP reads at `F_Σ`, with the value side re-lendable (`RSlot`). -/
def PJ (δ : LSub) (σ : LStack) (S₀ : Row) (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) :
    Prop :=
  ∀ (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes), αs.length = σ.length →
    List.IsChain (· < ·) αs → (∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) →
    RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ →
    bodyH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ C) (QA (ℍ := ℍ) δ σ S₀ C)
      (OpenH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ C) (QA (ℍ := ℍ) δ σ S₀ C)) αs ls
      (substAll γ e) ρ

/-- **`[var]`**: the variable's re-lendable value. -/
theorem pj_var {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy} {S : Row} (h : Ctx.SoloP Γ i A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.var i) (CTy.effOf S A) := by
  intro αs ls γ ρ _ hch _ hg
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg
  obtain ⟨v, hv, hval⟩ := rSep_soloP hch h (h.lt_of_liveWithin hl) hs
  rw [substAll_var' hv]
  refine wpG_here _ _ _ ρ (Or.inl ⟨v, rfl, ?_⟩)
  show RAns δ σ S₀ (CTy.effOf S A) αs ls v ρ
  rw [rAns_effOf]; exact hval

/-- **A pure computation whose answer is frozen**: Core's typing derives it at `F A`, `A` reads
none of the stack's variables and its values lie in `[top]` (`hz`, 6.60 for a type outliving the
lends). The fundamental property at the current lifetimes runs it; its answer, frozen whole, is
re-lendable (`rslot_of_frozen`). Its context holds no thunk that stops. -/
theorem pj_pure {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy} {S : Row}
    (hd : CDerives Δ Γ e (.comp (.ret A))) (hΓ : CtxNoEffT Γ) (hA : NoEffT A)
    (hx : ∀ en ∈ σ, ¬ VFree en.x A)
    (hz : ∀ αs ls v ρ, αs.length = σ.length → List.IsChain (· < ·) αs →
      vCE (ℍ := ℍ) none true A ls (extS δ σ αs) v ρ → stratS αs ρ) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ e (CTy.effOf S A) := by
  intro αs ls γ ρ hlen hch hΔ hg
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

/-- **`[perform]` at a resuming operation of the lenders' row**: linear, answered at `1`, its
argument closed data reading none of the stack's variables and outliving every lifetime
(GhostEnd's `Row.Resume` at every entry). The argument is run by the fundamental property at the
current lifetimes; the stop crosses every lend and drops no view (the context's views went into
the argument, which by 6.60 is in `[top]`, or were garbage), and its continuation, a value, is the
piece. -/
theorem pj_perform {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {o : OpSig}
    (hf : Row.find S₀ o.n o.i = some o) (ha : o.abort = false) (hq : o.q = .lin)
    (hoB : o.B = .unit) (hx : ∀ en ∈ σ, ¬ VFree en.x o.A) (hAo : ∀ Δ a, VOutlives Δ a o.A)
    (hd : CDerives Δ Γ V (.val o.A)) (hΓ : CtxNoEffT Γ) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (performE (opArgE o.n o.i V)) (CTy.effOf S o.B) := by
  intro αs ls γ ρ hlen hch hΔ hg
  have hS : SemV Δ Γ V o.A := fundamentalC (ℍ := ℍ) hd
  change wpG ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll γ V)) _ ρ
  refine wpG_bind_pure _ _ ls _ ρ (wpTS_mono (fun ls' v τ hv => ?_) ρ
    (hS (extS δ σ αs) γ ls ρ (hΔ αs (reLend_refl hch)) (rctx_gDenC hch hΓ hg)))
  have hv' : vCE (ℍ := ℍ) none true o.A ls' δ v τ := by
    rw [vC_extS_of_not_free true ls' σ αs hx] at hv; exact hv
  have hzt : stratS αs τ := by
    cases σ with
    | nil =>
        obtain rfl : αs = [] := List.eq_nil_of_length_eq_zero hlen
        exact stratS_nil τ
    | cons en σ' => exact stratS_of_outlives hAo (hx en (List.mem_cons_self ..)) hv' αs
  refine wpG_here _ _ _ τ (Or.inr (Or.inl ?_))
  refine stopAt_of_perform (K := .hole) (n := o.n) (i := o.i) (en := o.ent δ) rfl
    (Row.tab_find hf) ha (ds := List.replicate σ.length false) dropS_none ?_ ?_
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

/-- **`[let]` at the row**: `M to x. N`. `M` runs as a piece; `N`'s context is the frame, its
views and the rest of what it holds re-lendable (`rctx_relendable`): dropped and frozen at each
of `M`'s full-depth stops and thawed at the next re-lend, carried live into the continuation at a
stop inside. At `M`'s answer, re-lendable, the β-step hands `N` its re-lendable context. One run
is `bodyH_bind`, every continuation `openH_bind`. -/
theorem pj_let (hLR : LinResume (Row.tab S₀ δ)) {Δ : LifeCtx}
    {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row} (hsp : Ctx.SplitP Γ Γ₁ Γ₂)
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ Γ₁ M (CTy.effOf S A))
    (hN : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ₂) N (CTy.effOf S B)) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.val (.lam N)) M) (CTy.effOf S B) := by
  intro αs ls γ ρ hlen hch hΔ hg
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
        (bodyH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S B))
          (QA δ σ S₀ (CTy.effOf S B))
          (OpenH δ σ (Row.tab S₀ δ) (RIn (ℍ := ℍ) δ σ S₀ (CTy.effOf S B))
            (QA δ σ S₀ (CTy.effOf S B))) αs' ls' (K.plug (.val v))) := by
    intro αs' hr hlen' ls' v τ ⟨τ₁, τ₂, hcτ, hv, hF⟩
    refine wpG_step (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ τ ?_
    rw [← substAll_cons_psub]
    obtain ⟨hl, hs⟩ := pure_sep_iff.mp hF
    have hv' : RSlot (ℍ := ℍ) δ σ S₀ A αs' ls' v τ₁ := by
      have := hv; simp only [QA] at this; rwa [rAns_effOf] at this
    refine hN αs' ls' (v :: γ) τ hlen' hr.2 (fun αs'' hr' => hΔ αs'' (reLend_trans hr' hr))
      (pure_sep_mk hl ?_)
    show (RSlot δ σ S₀ A αs' ls' v ⋆ rSep δ σ S₀ αs' ls' Γ₂ γ) τ
    exact ⟨τ₁, τ₂, hcτ, hv', hs⟩
  have hb := hM αs ls γ ρ₁ hlen hch hΔ hg₁
  rw [rIn_effOf_ans S A B] at hb
  obtain ⟨hB₁, hB₀⟩ := openH_bind hLR K hH Fr Fz hFs hFe hFo hfz hthaw (B := αs)
    (fun αs' hle hlen' hch' => hk αs' ⟨hle, hch'⟩ hlen')
  exact bodyH_bind hLR K hH Fr Fz hFs hFe hFo (hfz αs hlen hch) (hthaw αs)
    (fun d₁ d₂ ls' e τ₁ τz τ hd hl₁ hl₂ hO hz hc' =>
      hB₁ hd hl₁ hl₂ (List.forall₂_same.mpr fun _ _ => le_rfl) hO hz hc')
    (fun αs' ls' e τ₁ τf τ hr hO hf hc' =>
      hB₀ ((List.Forall₂.length_eq hr.1).trans hlen) hr.1 hO hf hc')
    (hk αs (reLend_refl hch) hlen) hb hg₂ hc

/-! ### Values, eliminations, and closures that stop -/

theorem substAll_cons₂' (w₂ w₁ : Val) (γ : List Val) (e : Expr) :
    substAll (w₂ :: w₁ :: γ) e =
      Expr.subst 0 w₁ (Expr.subst 0 (w₂.shift 1 0) (Expr.psub 2 γ e)) := by
  show Expr.psub 0 (w₂ :: w₁ :: γ) e = _
  rw [Expr.psub_cons₂ 0 w₂ w₁ γ e, Val.shift_zero]

/-- **The value judgment**: from a re-lendable context the value expression runs, purely, to a
re-lendable value. -/
def PV (δ : LSub) (σ : LStack) (S₀ : Row) (Δ : LifeCtx) (Γ : Ctx VTy) (V : Expr) (A : VTy) :
    Prop :=
  ∀ (αs : List Life) (ls : List SRec) (γ : List Val) (ρ : WRes), αs.length = σ.length →
    List.IsChain (· < ·) αs → (∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs')) →
    RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ →
    wpTS ls (substAll γ V) (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v) ρ

/-- **`return V`**: a value expression is a piece that does not stop. -/
theorem pj_of_pv {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {A : VTy} {S : Row}
    (h : PV (ℍ := ℍ) δ σ S₀ Δ Γ V A) : PJ (ℍ := ℍ) δ σ S₀ Δ Γ V (CTy.effOf S A) := by
  intro αs ls γ ρ hlen hch hΔ hg
  refine wpG_mono (fun ls' t τ hq => Or.inl ?_)
    ((wpTS_iff_wpG _ _ _ _).mp (h αs ls γ ρ hlen hch hΔ hg))
  obtain ⟨v, rfl, hv⟩ := hq
  exact ⟨v, rfl, by show RAns δ σ S₀ (CTy.effOf S A) αs ls' v τ; rw [rAns_effOf]; exact hv⟩

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
    (hd : CDerives Δ Γ V (.val A)) (hΓ : CtxNoEffT Γ) (hA : NoEffT A)
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
  intro αs ls γ ρ hlen hch hΔ hg
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

/-- **A closure that stops, built by the borrower** (`[lam]`, `[thunkV]` at `A ⊸ F_Σ B`): its
environment, re-lendable, is its frozen share; called at a re-lend on a re-lendable argument, the
β-step hands the body its re-lendable context, and the body is the piece. -/
theorem rslot_lamEff {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    {n i : UInt32} {q : Qual} {A' B' : VTy} {fin C : CTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ) M (.eff n i q A' B' fin C))
    {αs : List Life} {ls : List SRec} {γ : List Val} {ρ : WRes} (hlen : αs.length = σ.length)
    (hΔ : ∀ αs', ReLend αs' αs → Δ.Models (extS δ σ αs'))
    (hg : RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρ) :
    RSlot (ℍ := ℍ) δ σ S₀ (.thunk (.arr A (.eff n i q A' B' fin C))) αs ls
      ⟨.lam (Expr.psub 1 γ M), .lam⟩ ρ := by
  have hr := rctx_relendable hlen hg
  change RelendableS δ [] σ _ αs ls ρ
  refine relendableS_mono_rel ?_ ρ hr
  intro αs' ls' hr' τ hτ v τv τ' hv hc'
  refine wpG_step (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ M) v) rfl) ls' _ τ' ?_
  rw [← substAll_cons_psub]
  obtain ⟨hl', hs'⟩ := pure_sep_iff.mp hτ
  refine hM αs' ls' (v :: γ) τ' ((List.Forall₂.length_eq hr'.1).trans hlen) hr'.2
    (fun αs'' h'' => hΔ αs'' (reLend_trans h'' hr')) (pure_sep_mk hl' ?_)
  show (RSlot δ σ S₀ A αs' ls' v ⋆ rSep δ σ S₀ αs' ls' Γ γ) τ'
  exact ⟨τv, τ, ResU.CompS.comm hc', hv, hs'⟩

theorem pv_lamEff {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    {n i : UInt32} {q : Qual} {A' B' : VTy} {fin C : CTy}
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ) M (.eff n i q A' B' fin C)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.thunk (.arr A (.eff n i q A' B' fin C))) := by
  intro αs ls γ ρ hlen _ hΔ hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  exact wpTS_val ls _ _ ρ (rslot_lamEff hM hlen hΔ hg)

/-- **Calling a closure that stops** (`[app]` of `force f` at `A ⊸ F_Σ B`, the argument a
variable): at the current lifetimes the closure's re-lendable reading, applied to the argument's
re-lendable value. -/
theorem pj_call {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {k j : Nat} {A : VTy}
    {n i : UInt32} {q : Qual} {A' B' : VTy} {fin C : CTy} (hsp : Ctx.SplitP Γ Γ₁ Γ₂)
    (hk : Ctx.SoloP Γ₁ k (.thunk (.arr A (.eff n i q A' B' fin C)))) (hj : Ctx.SoloP Γ₂ j A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.var k) (.var j)) (.eff n i q A' B' fin C) := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  obtain ⟨hl₁, hs₁⟩ := pure_sep_iff.mp hg₁
  obtain ⟨hl₂, hs₂⟩ := pure_sep_iff.mp hg₂
  obtain ⟨f, hf, hfv⟩ := rSep_soloP hch hk (hk.lt_of_liveWithin hl₁) hs₁
  obtain ⟨v, hv, hvv⟩ := rSep_soloP hch hj (hj.lt_of_liveWithin hl₂) hs₂
  show wpG ls (.app (substAll γ (.var k)) (substAll γ (.var j))) _ ρ
  rw [substAll_var' hf, substAll_var' hv]
  exact relendableS_now hch hfv v ρ₂ ρ hvv hc

/-- **Resuming a continuation** (`[app]` of `[proj₁]` of `force κ` at `(B ⊸ F_Σ R) & ⊤`, the
answer a variable): at the current lifetimes the continuation's re-lendable reading, resumed on
the answer's re-lendable value. -/
theorem pj_resume {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {k j : Nat} {A : VTy}
    {n i : UInt32} {q : Qual} {A' B' : VTy} {fin C : CTy} (hsp : Ctx.SplitP Γ Γ₁ Γ₂)
    (hk : Ctx.SoloP Γ₁ k (.thunk (.amp (.arr A (.eff n i q A' B' fin C)) .top)))
    (hj : Ctx.SoloP Γ₂ j A) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.app (.app (.var k) (.val (.inj₁ .unit))) (.var j))
      (.eff n i q A' B' fin C) := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  obtain ⟨hl₁, hs₁⟩ := pure_sep_iff.mp hg₁
  obtain ⟨hl₂, hs₂⟩ := pure_sep_iff.mp hg₂
  obtain ⟨f, hf, hfv⟩ := rSep_soloP hch hk (hk.lt_of_liveWithin hl₁) hs₁
  obtain ⟨v, hv, hvv⟩ := rSep_soloP hch hj (hj.lt_of_liveWithin hl₂) hs₂
  show wpG ls (.app (.app (substAll γ (.var k)) (substAll γ (.val (.inj₁ .unit))))
    (substAll γ (.var j))) _ ρ
  rw [substAll_var' hf, substAll_var' hv]
  exact relendableS_now hch hfv v ρ₂ ρ hvv hc

/-- **`case V {inj₁ x. M₁ | inj₂ y. M₂}`**: a branch on a re-lendable value; the branch taken is the
piece, its context the payload's re-lendable value beside the rest. -/
theorem pj_case {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {V M₁ M₂ : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γs Γb) (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γs V (.sum A B))
    (h₁ : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γb) M₁ C)
    (h₂ : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨B, true⟩ :: Γb) M₂ C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.case V M₁ M₂) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine wpG_bind_frame (.case .hole (Expr.psub 1 γ M₁) (Expr.psub 1 γ M₂)) (substAll γ V) ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ (.sum A B) αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γb γ)
    _ (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, hcτ, hsum, hg₂'⟩
  obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg₂'
  rcases hsum with ⟨w, hq⟩ | ⟨w, hq⟩
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hq
    refine wpG_step (fun μ => Step1N.head (Head.case₁ μ w _ _) rfl) ls' _ τ ?_
    rw [← substAll_cons_psub]
    exact h₁ αs ls' (w :: γ) τ hlen hch hΔ (pure_sep_mk hl ⟨τ₁, τ₂, hcτ, hw, hs⟩)
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hq
    refine wpG_step (fun μ => Step1N.head (Head.case₂ μ w _ _) rfl) ls' _ τ ?_
    rw [← substAll_cons_psub]
    exact h₂ αs ls' (w :: γ) τ hlen hch hΔ (pure_sep_mk hl ⟨τ₁, τ₂, hcτ, hw, hs⟩)

/-- **`let (x, y) = V in M`**: the pair's components, re-lendable each with its own share. -/
theorem pj_letpair {Δ : LifeCtx} {Γ Γp Γb : Ctx VTy} {V M : Expr} {A B : VTy} {C : CTy}
    (hsp : Ctx.SplitP Γ Γp Γb) (hV : PV (ℍ := ℍ) δ σ S₀ Δ Γp V (.tensor A B))
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M C) :
    PJ (ℍ := ℍ) δ σ S₀ Δ Γ (.letpair V M) C := by
  intro αs ls γ ρ hlen hch hΔ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := rctx_split hch hsp hg
  refine wpG_bind_frame (.letpair .hole (Expr.psub 2 γ M)) (substAll γ V) ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ (.tensor A B) αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γb γ)
    _ (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, hcτ, hpair, hg₂'⟩
  obtain ⟨w₁, w₂, hq⟩ := hpair
  obtain ⟨rfl, b₁, b₂, hcb, hw₁, hw₂⟩ := pure_sep_iff.mp hq
  refine wpG_step (fun μ => Step1N.head (Head.letpair μ w₁ w₂ _) rfl) ls' _ τ ?_
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
  refine wpG_bind_frame (.seq .hole (substAll γ M)) (substAll γ V) ls
    (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ .unit αs ls' v)
    (fun ls' => RCtx (ℍ := ℍ) δ σ S₀ αs ls' Γ₂ γ)
    _ (fun ls' hls τ h => rctx_local (ext_of_same hls τ) h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV αs ls γ ρ₁ hlen hch hΔ hg₁, hg₂⟩
  rintro ls' - v τ ⟨τ₁, τ₂, hcτ, hu, hg₂'⟩
  have hu' := relendableS_now hch hu
  obtain ⟨rfl, rfl⟩ := hu'
  rw [eq_of_compS_empty_left hcτ]
  exact wpG_step (fun μ => Step1N.head (Head.seq μ _) rfl) ls' _ τ₂
    (hM αs ls' γ τ₂ hlen hch hΔ hg₂')

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

/-- **A persistent closure that stops** (`[!thunkV]` over `!Γ` at `A ⊸ F_Σ B`): its environment
holds nothing, and called at any re-lend on a re-lendable argument its body is the piece. -/
theorem pv_bangLamEff {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy}
    {n i : UInt32} {q : Qual} {A' B' : VTy} {fin C : CTy}
    (hp : Persistent Γ)
    (hM : PJ (ℍ := ℍ) δ σ S₀ Δ (⟨A, true⟩ :: Γ) M (.eff n i q A' B' fin C)) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.lam M)) (.bang (.thunk (.arr A (.eff n i q A' B' fin C)))) := by
  intro αs ls γ ρ hlen hch hΔ hg
  have hρ : ρ = PMap.empty := by
    obtain ⟨hl, hs⟩ := pure_sep_iff.mp hg
    have : ∀ (Γ : Ctx VTy) (γ : List Val) {ρ : WRes}, Persistent Γ →
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
    exact this Γ γ hp hs
  subst hρ
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ PMap.empty
  exact wpTS_val ls _ _ PMap.empty ⟨rfl, rslot_lamEff hM hlen hΔ hg⟩

/-- **The self-reference of a loop is a closure that stops**, at every budget, by induction on
the budget: `inj₁ ()` once spent; at `j + 1`, called at a re-lend on a re-lendable argument it
steps to the loop at `j`, which runs the step — re-lendable at every re-lend, holding nothing — on
the self-reference at `j`. -/
theorem rslot_fixSelf {A : VTy} {n i : UInt32} {q : Qual} {A' B' : VTy} {fin C : CTy} {s : Val}
    {Bd : List Life}
    (hs : ∀ αs ls, ReLend αs Bd →
      RSlot (ℍ := ℍ) δ σ S₀ (fixStepTy A (.eff n i q A' B' fin C)) αs ls s PMap.empty) :
    ∀ (m : Nat) (k : UInt32), k.toNat = m → ∀ αs ls, ReLend αs Bd → αs.length = σ.length →
      RSlot (ℍ := ℍ) δ σ S₀ (fixSelfTy A (.eff n i q A' B' fin C)) αs ls (fixSelf s k) PMap.empty
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
      change RelendableS δ [] σ _ αs ls PMap.empty
      refine relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a)
        fun ls' _ αs' hr' x ρx τ hx hc => ?_
      rw [eq_of_compS_empty_left hc]
      refine wpG_step (fun μ => Step1N.head (Head.beta μ _ x) rfl) ls' _ ρx ?_
      rw [fixSelf_body_subst]
      refine wpG_step (fun μ => Step1N.head (Head.boundedFix μ s (k - 1) x) rfl) ls' _ ρx ?_
      have hr'' : ReLend αs' Bd := reLend_trans hr' hr
      have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr'.1).trans hlen
      obtain ⟨-, hs'⟩ := hs αs' ls' hr''
      exact relendableS_now hr'.2 hs' (Val.pair (fixSelf s (k - 1)) x) ρx ρx
        ⟨fixSelf s (k - 1), x, pure_sep_mk rfl
          ⟨PMap.empty, ρx, compS_empty_left ρx,
            rslot_fixSelf hs j (k - 1) hkj αs' ls' hr'' hlen', hx⟩⟩ (compS_empty_left ρx)

/-- **`bounded_fix` is a closure that stops**, at every computation type of a row: called at a
re-lend on `(s, (k, a))`, it steps to the step on its self-reference (`rslot_fixSelf`) and the
argument. The step holds nothing, so it is re-lendable at every later re-lend. -/
theorem rslot_boundedFix {A : VTy} {n i : UInt32} {q : Qual} {A' B' : VTy} {fin C : CTy}
    {αs : List Life} (hlen : αs.length = σ.length) (ls : List SRec) :
    RSlot (ℍ := ℍ) δ σ S₀ (boundedFixTy A (.eff n i q A' B' fin C)) αs ls (Val.prim .boundedFix)
      PMap.empty := by
  refine ⟨rfl, ?_⟩
  change RelendableS δ [] σ _ αs ls PMap.empty
  refine relendableS_frozen hlen (fun a _ => ResU.inStratum_empty a)
    fun ls' _ αs' hr v ρv τ hv hc => ?_
  rw [eq_of_compS_empty_left hc]
  have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr.1).trans hlen
  obtain ⟨s, w, hq⟩ := hv
  obtain ⟨rfl, ρs, ρw, hcw, ⟨rfl, hs⟩, hw⟩ := pure_sep_iff.mp hq
  obtain ⟨kv, a, hq'⟩ := hw
  obtain ⟨rfl, ρk, ρa, hck, hk, ha⟩ := pure_sep_iff.mp hq'
  obtain ⟨rfl, k, rfl⟩ := relendableS_now hr.2 hk
  rw [eq_of_compS_empty_left hcw, eq_of_compS_empty_left hck]
  refine wpG_step (fun μ => Step1N.head (Head.boundedFix μ s k a) rfl) ls' _ ρa ?_
  have hsall : ∀ αs'' ls'', ReLend αs'' αs' →
      RSlot (ℍ := ℍ) δ σ S₀ (fixStepTy A (.eff n i q A' B' fin C)) αs'' ls'' s PMap.empty :=
    fun αs'' ls'' hr'' => ⟨rfl, relendableS_empty (relendableS_idem hs) ls'' (ext_empty' _ _) αs''
      hr''⟩
  exact relendableS_now hr.2 hs (Val.pair (fixSelf s k) a) ρa ρa
    ⟨fixSelf s k, a, pure_sep_mk rfl
      ⟨PMap.empty, ρa, compS_empty_left ρa,
        rslot_fixSelf hsall k.toNat k rfl αs' ls' (reLend_refl hr.2) hlen', ha⟩⟩
    (compS_empty_left ρa)

/-- `bounded_fix` as a value of the borrower: the constant, at a consumed context. -/
theorem pv_boundedFix {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} {n i : UInt32} {q : Qual}
    {A' B' : VTy} {fin C : CTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .boundedFix))
      (boundedFixTy A (.eff n i q A' B' fin C)) := by
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

/-- **The piece judgment gives D16.1's piece**, at a row nothing of which is caught inside
(`hRI`). At every re-lend below `αi` the views handed rebuild the borrower's context
re-lendably, beside garbage (`hctx`); every re-lend models `Δ` (`hΔ`). The piece holds nothing of
its own. -/
theorem openS_of_pj (hx : AllCross σ (Row.tab S₀ δ)) {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr}
    {C : CTy} (hRI : ∀ n i, RIn (ℍ := ℍ) δ σ S₀ C n i = none)
    (hpj : PJ (ℍ := ℍ) δ σ S₀ Δ Γ M C) {Q : List Life → List SRec → Val → WProp}
    (hQ : ∀ αs ls v, List.IsChain (· < ·) αs → αs.length = σ.length →
      Entails (QA (ℍ := ℍ) δ σ S₀ C αs ls v) (Q αs ls v))
    {ds : List Bool} {αi : List Life} {ls : List SRec} {γ : List Val}
    (hΔ : ∀ αs, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs))
    (hctx : ∀ αs ρv, List.Forall₂ (· < ·) αs αi → List.IsChain (· < ·) αs →
      vwS δ [] σ ds αs ls ρv →
        ∃ ρg ρd, ResU.CompS ρg ρd ρv ∧ NoOwn ρd ∧ RCtx (ℍ := ℍ) δ σ S₀ αs ls Γ γ ρg) :
    OpenS δ σ (Row.tab S₀ δ) Q σ.length ds αi [] ls (substAll γ M) PMap.empty := by
  refine openS_of_openH (RI := RIn (ℍ := ℍ) δ σ S₀ C) hx hRI ?_
  refine openH_fold fun αi' hlt hch => ?_
  rw [List.append_nil] at hch ⊢
  refine ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
  rw [List.take_length] at hw
  rw [eq_of_compS_empty_left hc]
  have hlen : αi'.length = σ.length := (vwS_length hw).2
  obtain ⟨ρg, ρd, hcg, hno, hg⟩ := hctx αi' w hlt hch hw
  have hb := hpj αi' ls γ ρg hlen hch
    (fun αs'' hr => hΔ αs'' (forall₂_le_lt hr.1 hlt) hr.2) hg
  refine wpG_absorb ?_ hno hcg
  exact bodyH_mono' (fun ls v => hQ αi' ls v hch hlen)
    (fun _ _ _ _ hO => openH_mono_Q hQ (by simpa using hlen) hO)
    (fun _ _ _ _ hr hO => openH_mono_Q hQ (by simpa using hr.1.length_eq.trans hlen) hO) _ hb

end piece

end Law2

end
