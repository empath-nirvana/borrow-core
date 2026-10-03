import GhostEnd.Stacked

/-!
# GhostEnd — the stacked lemmas at every stack (#279)

Step 3h wrote D16.1 (`Stacked.lean`) and showed the `withbor` rows at `|σ| = 1`. This file proves
the three lemmas that remained, each **once, for every stack**: one statement with the stack `σ`
a parameter, proved by induction on D16.1's piece `OpenS` at `σ·new` (its least fixed point of
stops). The entries of `σ` are carried along by lemmas proved by recursion on the stack list
(`vwS_seen_congr`, `vwS_inStratum`, `dropS_places`, `dropS_unseen`, `vwS_local`, `vwS_join`,
`vwS_split`). No step depends on `|σ|`.

Every stop of the row crosses every entry (`AllCross`), so a stop is at depth `|σ|` (`stopS_full`,
`stopS_of_full`): the generalisation of step 3h's `hcross`. Stops at an intermediate depth are
#278's.

## The commutation lemma, `σ·new` to `σ`

Both are maps from D16.1's piece at `σ·new` to D16.1's piece at `σ`, answering as a callback
(`cbQ`, `ghostS`):

* `stack_step_other`: `new` lends a place `ℓ′` that `σ` does not hold. At each re-lend `αs′` of
  `σ`, 6.65 (`wpG_M_frameX`) lends `ℓ′` below the innermost of `αs′`, and the piece runs at
  `α :: αs′`. The owner of `ℓ′` joins the answer, or the continuation at a stop (`opTable_frame`).
* `stack_step_reborrow`: `new` lends again the place of `σ`'s innermost `mut` entry. 6.66
  (`wpG_M_antiFrameX`) unfolds the view `σ` is handed, and 6.65 lends its content. At a stop
  6.66's refold is the cell the stop drops for that entry.

At a stop, `σ`'s dropped views are kept, not discarded: the table at the new lend (`wpG_tabAt`)
puts them strictly above it, so they pass 6.65's exit.

## An `imm` entry, and `⋆`

* `stack_step_imm`: 6.64 (`wpG_I_frameX`) at every stack. 6.64 runs the callback at a list it
  extends with a fresh record. The piece is therefore taken at every `Ext`-extension of the list.
  This is the quantifier `RelendI` builds into its unfolding. Inside the induction the table owes
  every continuation at every extension (`opTable_shift`), and `fold_imm` folds that family.
* `relendableS_sep`: `Relendable_σ` is closed under `⋆`.
  - A `mut` view is held by at most one part (`dropC_disj`).
  - Two `imm` views at one entry are one cell (`ptoImmS_join`, `[TR]` 6.43), split again at the
    re-lend (`ptoImmS_dup`, 6.116).

## The fold, and every hypothesis discharged

* At `σ = []` the piece is `ewpTS` (`openS_nil_ewp`). The steps at `σ = []` give 6.65 and 6.64 at
  a resuming table (`stack_spans_mut`, `stack_spans_imm`).
* `fold_other`: a stack of `mut` lends of distinct places folds to `ewpTS`, by induction on the
  stack, its step `stack_step_other`.
* `stack2_reborrow_spans` is step 3h's `withbor_reborrow_spans`, from the uniform steps.
* `stack3_reborrow_yield`: three lends of one place spanning a yield. The same two lemmas fold the
  stack as at depth 2.
* `stack2_imm_yield`: an `imm` lend inside a `mut` lend spanning a yield.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Stacks: views, drops and strata, by induction on the stack -/

section stack
variable {δ : LSub}

/-- The views of a stack depend on `seen` only through which of its places it holds. -/
theorem vwS_seen_congr : ∀ {σ : LStack} {s s' : List BoCa.Loc},
    (∀ e ∈ σ, (e.l ∈ s ↔ e.l ∈ s')) → ∀ (ds : List Bool) (αs : List Life) (ls : List SRec),
      vwS δ s σ ds αs ls = vwS δ s' σ ds αs ls
  | [], _, _, _, [], [], _ => rfl
  | [], _, _, _, [], _ :: _, _ => rfl
  | [], _, _, _, _ :: _, αs, _ => by cases αs <;> rfl
  | _ :: _, _, _, _, [], αs, _ => by cases αs <;> rfl
  | _ :: _, _, _, _, _ :: _, [], _ => rfl
  | e :: σ, s, s', h, d :: ds, α :: αs, ls => by
      have hv : vis s e d = vis s' e d := by
        simp only [vis, decide_eq_decide.mpr (h e (List.mem_cons_self ..))]
      have ih := vwS_seen_congr (σ := σ) (s := e.l :: s) (s' := e.l :: s')
        (fun e' he' => by
          simp only [List.mem_cons]
          exact or_congr Iff.rfl (h e' (List.mem_cons_of_mem _ he'))) ds αs ls
      simp only [vwS, hv, ih]

/-- What a stop drops depends on `seen` only through which of the stack's places it holds. -/
theorem dropS_seen_congr : ∀ {σ : LStack} {s s' : List BoCa.Loc},
    (∀ e ∈ σ, (e.l ∈ s ↔ e.l ∈ s')) → ∀ (ds : List Bool), dropS s σ ds = dropS s' σ ds
  | [], _, _, _, [] => rfl
  | [], _, _, _, _ :: _ => rfl
  | _ :: _, _, _, _, [] => rfl
  | e :: σ, s, s', h, d :: ds => by
      have hv : vis s e d = vis s' e d := by
        simp only [vis, decide_eq_decide.mpr (h e (List.mem_cons_self ..))]
      have ih := dropS_seen_congr (σ := σ) (s := e.l :: s) (s' := e.l :: s')
        (fun e' he' => by
          simp only [List.mem_cons]
          exact or_congr Iff.rfl (h e' (List.mem_cons_of_mem _ he'))) ds
      simp only [dropS, hv, ih]

/-- A cell of what a stop drops is at one of the stack's places. -/
theorem dropS_places : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {ρ : WRes},
    dropS seen σ ds ρ → ∀ k ψ, ρ.get k = some ψ → k ∈ σ.map LEnt.l
  | _, [], [], _, h, k, ψ, e => by
      obtain ⟨rfl, -⟩ := h; exact absurd (e.symm.trans (PMap.empty_get k)) (by simp)
  | _, e₀ :: σ, d :: ds, _, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩, k, ψ, e => by
      rcases ResU.Comp.get hc k with ⟨-, -, e'⟩ | ⟨ψ', e₁, -, -⟩ | ⟨ψ', -, e₂, -⟩ |
          ⟨ψ₁, ψ₂, ψ', e₁, -, -, -⟩
      · exact absurd (e.symm.trans e') (by simp)
      · refine List.mem_cons.mpr (Or.inl ?_)
        cases hd : vis _ e₀ d <;> rw [hd] at h₁
        · obtain ⟨rfl, -⟩ := h₁; exact absurd (e₁.symm.trans (PMap.empty_get k)) (by simp)
        · obtain ⟨φ, rfl, -⟩ := h₁; exact (ResU.single_get_eq_some e₁).1
      · exact List.mem_cons_of_mem _ (dropS_places h₂ k ψ' e₂)
      · refine List.mem_cons.mpr (Or.inl ?_)
        cases hd : vis _ e₀ d <;> rw [hd] at h₁
        · obtain ⟨rfl, -⟩ := h₁; exact absurd (e₁.symm.trans (PMap.empty_get k)) (by simp)
        · obtain ⟨φ, rfl, -⟩ := h₁; exact (ResU.single_get_eq_some e₁).1
  | _, [], _ :: _, _, h, _, _, _ => h.elim
  | _, _ :: _, [], _, h, _, _, _ => h.elim

/-- A cell of what a stop drops is at a place no entry inside it lends: a shadowed entry drops
nothing. -/
theorem dropS_unseen : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {ρ : WRes},
    dropS seen σ ds ρ → ∀ k ψ, ρ.get k = some ψ → k ∉ seen
  | _, [], [], _, h, k, ψ, e => by
      obtain ⟨rfl, -⟩ := h; exact absurd (e.symm.trans (PMap.empty_get k)) (by simp)
  | seen, e₀ :: σ, d :: ds, _, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩, k, ψ, e => by
      have hone : ∀ ψ', ρ₁.get k = some ψ' → k ∉ seen := by
        intro ψ' e₁
        cases hd : vis seen e₀ d <;> rw [hd] at h₁
        · obtain ⟨rfl, -⟩ := h₁; exact absurd (e₁.symm.trans (PMap.empty_get k)) (by simp)
        · obtain ⟨φ, rfl, -⟩ := h₁
          obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e₁
          simp only [vis, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hd
          exact hd.2
      rcases ResU.Comp.get hc k with ⟨-, -, e'⟩ | ⟨ψ', e₁, -, -⟩ | ⟨ψ', -, e₂, -⟩ |
          ⟨ψ₁, ψ₂, ψ', e₁, -, -, -⟩
      · exact absurd (e.symm.trans e') (by simp)
      · exact hone ψ' e₁
      · exact fun hk => dropS_unseen h₂ k ψ' e₂ (List.mem_cons_of_mem _ hk)
      · exact hone ψ₁ e₁
  | _, [], _ :: _, _, h, _, _, _ => h.elim
  | _, _ :: _, [], _, h, _, _, _ => h.elim

/-- A view at `α` lies in `Res_a` for every `a ⊏ α`. -/
theorem vwE_inStratum {e : LEnt} {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwE δ e d α ls ρ) {a : Life} (ha : a < α) : ρ.InStratum a := by
  cases d with
  | false => obtain ⟨rfl, -⟩ := h; exact ResU.inStratum_empty a
  | true =>
      obtain ⟨l, x, T, k, cr⟩ := e
      cases k with
      | «mut» => exact ptoMutS_below ha h
      | imm v =>
          obtain ⟨s, u, σ, hs, ls₀, rfl, -, hα, -⟩ := h
          exact ResU.inStratum_single l (show s.meet ⊐ a from lt_of_lt_of_le ha hα)

/-- The views of a stack at `αs` lie in `Res_a` for every `a` below each of `αs`. -/
theorem vwS_inStratum : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {αs : List Life}
    {ls : List SRec} {ρ : WRes}, vwS δ seen σ ds αs ls ρ → ∀ a, (∀ α ∈ αs, a < α) → ρ.InStratum a
  | _, [], [], [], _, _, h, a, _ => by obtain ⟨rfl, -⟩ := h; exact ResU.inStratum_empty a
  | _, _ :: _, _ :: _, α :: αs, _, _, ⟨_, _, hc, h₁, h₂⟩, a, ha =>
      (outlives_comp hc a).mpr ⟨vwE_inStratum h₁ (ha α (List.mem_cons_self ..)),
        vwS_inStratum h₂ a fun α' h' => ha α' (List.mem_cons_of_mem _ h')⟩
  | _, [], [], _ :: _, _, _, h, _, _ => h.elim
  | _, [], _ :: _, [], _, _, h, _, _ => h.elim
  | _, [], _ :: _, _ :: _, _, _, h, _, _ => h.elim
  | _, _ :: _, [], [], _, _, h, _, _ => h.elim
  | _, _ :: _, [], _ :: _, _, _, h, _, _ => h.elim
  | _, _ :: _, _ :: _, [], _, _, h, _, _ => h.elim

end stack

/-! ### Full-depth stops, the vector's ends, and `ghostS` -/

section full
variable {δ : LSub}

/-- Every operation of `Tab` crosses every entry of `σ`: its stops are at depth `|σ|`. -/
def AllCross (σ : LStack) (Tab : OpTab) : Prop :=
  ∀ n i en, Tab n i = some en → ∀ e ∈ σ, e.cross n = true

theorem AllCross.tail {e : LEnt} {σ : LStack} {Tab : OpTab} (h : AllCross (e :: σ) Tab) :
    AllCross σ Tab := fun n i en hT e' he' => h n i en hT e' (List.mem_cons_of_mem _ he')

theorem depth_full {σ : LStack} {n : UInt32} (h : ∀ e ∈ σ, e.cross n = true) :
    depth σ n = σ.length := by
  unfold depth
  rw [List.takeWhile_eq_self_iff.mpr (fun e he => h e he)]

theorem tabK_full {σ : LStack} {Tab : OpTab} (h : AllCross σ Tab) : tabK σ σ.length Tab = Tab := by
  funext n i
  unfold tabK
  cases hT : Tab n i with
  | none => split <;> rfl
  | some en => rw [if_pos (depth_full (h n i en hT))]

theorem tabK_ne_full {σ : LStack} {Tab : OpTab} (h : AllCross σ Tab) {k : Nat}
    (hk : k ≠ σ.length) : ∀ n i, tabK σ k Tab n i = none := by
  intro n i
  unfold tabK
  cases hT : Tab n i with
  | none => split <;> rfl
  | some en => rw [if_neg (by rw [depth_full (h n i en hT)]; exact fun e => hk e.symm)]

/-- In nesting order, the innermost lifetime is below the outermost. -/
theorem head_le_last : ∀ {α : Life} {αs : List Life}, List.IsChain (· < ·) (α :: αs) →
    ∀ a ∈ (α :: αs).getLast?, α ≤ a
  | _, [], _, a, ha => by simp at ha; exact le_of_eq ha
  | α, β :: αs, h, a, ha => by
      rw [List.isChain_cons_cons] at h
      rw [List.getLast?_cons_cons] at ha
      exact le_of_lt (lt_of_lt_of_le h.1 (head_le_last h.2 a ha))

/-- `[top (a :: αs)]` is `[top αs]` when `αs` has an outermost entry. -/
theorem stratS_tail {a : Life} {αs : List Life} {ρ : WRes} (h : stratS (a :: αs) ρ) :
    stratS αs ρ := by
  cases αs with
  | nil => exact stratS_nil ρ
  | cons b αs => intro x hx; exact h x (by rw [List.getLast?_cons_cons]; exact hx)

/-- In nesting order, `[top αs]` puts a share in `[α]` for every `α` in the vector. -/
theorem stratS_head {α : Life} {αs : List Life} (hc : List.IsChain (· < ·) (α :: αs)) {ρ : WRes}
    (h : stratS (α :: αs) ρ) : ρ.InStratum α := by
  obtain ⟨a, ha⟩ : ∃ a, a ∈ (α :: αs).getLast? := by
    cases hl : (α :: αs).getLast? with
    | none => simp at hl
    | some a => exact ⟨a, rfl⟩
  exact (h a ha).mono (head_le_last hc a ha)

/-- An owner whose payload is in `Res_β` is in `Res_α` for `α ⊑ β`. -/
theorem owner_inStratum_le {l : BoCa.Loc} {T : VTy} {β : Life}
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) {α : Life} (hα : α ≤ β)
    {ls : List SRec} {ρ : WRes} (h : owner l T δ ls ρ) : ρ.InStratum α := by
  obtain ⟨w, ρ₁, ρ₂, hc, hρ₁, hv⟩ := h
  rw [hρ₁] at hc
  exact (outlives_comp hc α).mpr ⟨ResU.inStratum_single_own α l w, (hP ls w ρ₂ hv).mono hα⟩

/-- The owner of an entry, handed back, is passed on: `X ⊨ ownerE ─⋆ ownerE ⋆ X`. -/
theorem ownWandE_pass {e : LEnt} {ls : List SRec} {X : WProp} {ρ : WRes} (h : X ρ) :
    ownWandE δ e ls (ownerE δ e ls ⋆ X) ρ := by
  obtain ⟨l, x, T, k, cr⟩ := e
  cases k with
  | «mut» =>
      intro w ρa ρb ha hcab ρc ρd hv hccd
      obtain ⟨o, ho, hd⟩ := compS_reassoc hcab hccd
      exact ⟨o, ρ, ResU.CompS.comm hd, ⟨w, ρa, ρc, ho, ha, hv⟩, h⟩
  | imm v =>
      intro ρa ρb ha hcab ρc ρd hv hccd
      obtain ⟨o, ho, hd⟩ := compS_reassoc hcab hccd
      exact ⟨o, ρ, ResU.CompS.comm hd, ⟨ρa, ρc, ho, ha, hv⟩, h⟩

/-- **What a stop owes the lenders, from a share in `[top]`.** The owners handed back are passed
on. -/
theorem ghostS_of_boxTop : ∀ {σ : LStack} {αs : List Life}, αs.length = σ.length →
    List.IsChain (· < ·) αs → ∀ {ls : List SRec} {R : WProp} {ρ : WRes},
      boxTop αs R ρ → ghostS δ σ αs ls R ρ
  | [], [], _, _, _, _, _, h => h.1
  | _ :: _, _ :: _, _, hc, _, _, _, h =>
      ⟨ownWandE_pass h, stratS_head hc h.2⟩

/-- **A stop when every operation crosses every entry.** It is at depth `|σ|`: every entry's
view is dropped and the continuation is owed the next unfolding at the full vector. A stop at any
other depth is not one the table admits; what it leaves is garbage beside a share that owes
nothing it can produce. -/
theorem stopS_full {σ : LStack} {Tab : OpTab} (hx : AllCross σ Tab) {X : XT} {αs : List Life}
    (hlen : αs.length = σ.length) {ls : List SRec} {t : Expr} {ρ : WRes}
    (h : stopS δ σ Tab X αs ls t ρ) :
    (∃ ds, ds.length = σ.length ∧ (dropS [] σ ds ⋆
        ghostS δ σ αs ls (opTable Tab ls t fun ls' e' => X σ.length ds αs [] ls' e')) ρ) ∨
      ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ NoOwn ρ₂ ∧ ghostS δ σ αs ls (fun _ => False) ρ₁ := by
  obtain ⟨k, ds, ρ₁, ρ₂, hc, hd, hg⟩ := h
  by_cases hk : k = σ.length
  · subst hk
    rw [List.take_length] at hd hg
    rw [List.take_of_length_le (le_of_eq hlen), tabK_full hx] at hg
    rw [List.drop_length] at hg
    rw [List.drop_of_length_le (le_of_eq hlen)] at hg
    refine Or.inl ⟨ds, dropS_length hd, ρ₁, ρ₂, hc, hd, ?_⟩
    exact ghostS_mono (fun _ h => opTable_mono _ _ _ _ _ _
      (fun _ _ _ h' => relendableN_nil.mp h') h) _ _ _ ρ₂ hg
  · have hn := tabK_ne_full hx hk
    refine Or.inr ⟨ρ₂, ρ₁, ResU.CompS.comm hc, dropS_noOwn hd, ?_⟩
    match σ, αs, k, hlen with
    | [], [], k, _ => simp only [List.take_nil] at hg; exact (opTable_none hn hg).elim
    | _ :: _, _ :: _, 0, _ => exact (opTable_none hn hg).elim
    | _ :: _, _ :: _, _ + 1, _ =>
        exact box_mono (ownWandE_mono fun _ ⟨_, _, _, _, hb⟩ => (opTable_none hn hb.1).elim) ρ₂ hg

/-- In nesting order, the innermost lifetime is below every other. -/
theorem head_lt_mem : ∀ {α : Life} {αs : List Life}, List.IsChain (· < ·) (α :: αs) →
    ∀ a ∈ αs, α < a
  | _, [], _, _, ha => by simp at ha
  | _, β :: αs, h, a, ha => by
      rw [List.isChain_cons_cons] at h
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.1
      · exact lt_trans h.1 (head_lt_mem h.2 a ha)

/-- **A stop at depth `|σ|`, assembled.** -/
theorem stopS_of_full {σ : LStack} {Tab : OpTab} (hx : AllCross σ Tab) {X : XT} {αs : List Life}
    (hlen : αs.length = σ.length) {ls : List SRec} {t : Expr} {ds : List Bool} {ρ₁ ρ₂ ρ : WRes}
    (hd : dropS [] σ ds ρ₁)
    (hg : ghostS δ σ αs ls (opTable Tab ls t fun ls' e' => X σ.length ds αs [] ls' e') ρ₂)
    (hc : ResU.CompS ρ₁ ρ₂ ρ) : stopS δ σ Tab X αs ls t ρ := by
  refine ⟨σ.length, ds, ρ₁, ρ₂, hc, by rw [List.take_length]; exact hd, ?_⟩
  rw [List.take_length, List.take_of_length_le (le_of_eq hlen), tabK_full hx, List.drop_length,
    List.drop_of_length_le (le_of_eq hlen)]
  exact ghostS_mono (fun _ h => opTable_mono _ _ _ _ _ _
    (fun _ _ _ h' => relendableN_nil.mpr h') h) _ _ _ ρ₂ hg

end full

/-! ### The commutation lemma at every stack: a lend of another place -/

section other
variable {δ : LSub} {Tab : OpTab}

/-- D16.1's piece answering as a callback at `σ`: in `[α_inner]`, the owners handed back passed
on, the answer in `[top]`. -/
abbrev cbQ (δ : LSub) (σ : LStack) (Qa : List SRec → Val → WProp) :
    List Life → List SRec → Val → WProp :=
  fun αs ls v => ghostS δ σ αs ls (Qa ls v)

theorem take_cons_length (e : LEnt) (σ : LStack) : (e :: σ).take (σ.length + 1) = e :: σ := by
  simp

/-- The views handed at a re-lend of `σ·new`, where `new` lends a place `σ` does not hold: the
new entry's beside `σ`'s. -/
theorem vwS_cons_other {σ : LStack} {e : LEnt} (he : e.l ∉ σ.map LEnt.l) {d : Bool}
    {ds : List Bool} {α : Life} {αs : List Life} {ls : List SRec} {a v w : WRes}
    (ha : vwE δ e d α ls a) (hv : vwS δ [] σ ds αs ls v) (hc : ResU.CompS a v w) :
    vwS δ [] (e :: σ) (d :: ds) (α :: αs) ls w := by
  have h₀ : vis [] e d = d := by simp [vis]
  have hcg : vwS δ [e.l] σ ds αs ls = vwS δ [] σ ds αs ls :=
    vwS_seen_congr (fun e' he' => by
      simp only [List.mem_singleton, List.not_mem_nil, iff_false]
      intro h; exact he (h ▸ List.mem_map_of_mem he')) ds αs ls
  show (vwE δ e (vis [] e d) α ls ⋆ vwS δ [e.l] σ ds αs ls) w
  rw [h₀, hcg]
  exact ⟨a, v, hc, ha, hv⟩

/-- What a stop of `σ·new` drops, where `new` lends a place `σ` does not hold: the new entry's
beside `σ`'s. -/
theorem dropS_cons_other {σ : LStack} {e : LEnt} (he : e.l ∉ σ.map LEnt.l) {d : Bool}
    {ds : List Bool} {ρ : WRes} (h : dropS [] (e :: σ) (d :: ds) ρ) :
    (dropE e d ⋆ dropS [] σ ds) ρ := by
  have h₀ : vis [] e d = d := by simp [vis]
  have hcg : dropS [e.l] σ ds = dropS [] σ ds :=
    dropS_seen_congr (fun e' he' => by
      simp only [List.mem_singleton, List.not_mem_nil, iff_false]
      intro h; exact he (h ▸ List.mem_map_of_mem he')) ds
  have h' : (dropE e (vis [] e d) ⋆ dropS [e.l] σ ds) ρ := h
  rwa [h₀, hcg] at h'

/-- The table at the new lend `α` of `ℓ′`, at the start of the callback: the piece and `σ`'s
views are strictly above `α`, and the new view is at `ℓ′`. -/
theorem tabAt_start {l' : BoCa.Loc} {e : LEnt} (hel : e.l = l') {d : Bool} {α : Life}
    {ls : List SRec} {ρ ρv a va R : WRes} (hρ : ρ.InStratum α) (hv : ρv.InStratum α)
    (ha : vwE δ e d α ls a) (hek : e.k = .mut) (hva : ResU.CompS ρv a va)
    (hR : ResU.CompS ρ va R) : TabAt l' α R := by
  have hta : TabAt l' α a := by
    cases d with
    | false => obtain ⟨rfl, -⟩ := ha; exact tabAt_empty l' α
    | true =>
        obtain ⟨l, x, T, k, cr⟩ := e
        simp only at hel hek; subst hel hek
        exact tabAt_view ha
  exact (tabAt_comp hR).mpr ⟨tabAt_of_inStratum hρ,
    (tabAt_comp hva).mpr ⟨tabAt_of_inStratum hv, hta⟩⟩

/-- At the end of the callback, a part at places other than `ℓ′` is strictly above `α`. -/
theorem tabAt_off {l' : BoCa.Loc} {α : Life} {τ q : WRes} (ht : TabAt l' α τ)
    (hq : ∃ y, ResU.CompS q y τ) (hpl : ∀ k ψ, q.get k = some ψ → k ≠ l') : q.InStratum α := by
  obtain ⟨y, hy⟩ := hq
  have := ((tabAt_comp hy).mp ht).1
  exact fun k ψ e => this.2 k ψ (hpl k ψ e) e

/-- **The commutation lemma at every stack, for a lend of another place** (`withbor` (1)–(2) at
`σ·new`). D16.1's piece at `σ·new`, `new` lending a place `ℓ′` that `σ` does not hold, every stop
of the row crossing every entry, is, beside the owner of `ℓ′`, D16.1's piece at `σ`, answering
with that owner. One statement, `σ` a parameter; by induction on `OpenS` at `σ·new`.

At each re-lend `αs′` of `σ`: 6.65 lends `ℓ′` below the innermost of `αs′` and below the new
entry's last lifetime, and the piece at `σ·new` runs at `α :: αs′` with every view of `σ` beside
the new one. At a return 6.65's exit hands the owner of `ℓ′` back and it joins the answer. At a
stop the new view is garbage, `σ`'s dropped views stay (they are strictly above `α`: the table
at `α`, `wpG_tabAt`), the owner of `ℓ′` joins the continuation (`opTable_frame`), and the
continuation is again the piece at `σ·new`, folded at the next re-lend of `σ`. -/
theorem stack_step_other (hLR : LinResume Tab) {σ : LStack} {l' : BoCa.Loc} {x' : LifeVar}
    {T' : VTy} {cr' : UInt32 → Bool} (hx : AllCross (⟨l', x', T', .mut, cr'⟩ :: σ) Tab)
    (hl' : l' ∉ σ.map LEnt.l) {β' : Life} (hP' : ∀ ls w ρ, vC true T' ls δ w ρ → ρ.InStratum β')
    {Qa : List SRec → Val → WProp} {d : Bool} {ds : List Bool} {b : Life} {bs : List Life}
    (hβ : ∀ a ∈ bs.getLast?, a ≤ β')
    {ls : List SRec} {e : Expr} {ρo ρ ρt : WRes} (ho : owner l' T' δ ls ρo)
    (h : OpenS δ (⟨l', x', T', .mut, cr'⟩ :: σ) Tab (cbQ δ (⟨l', x', T', .mut, cr'⟩ :: σ) Qa)
      (σ.length + 1) (d :: ds) (b :: bs) [] ls e ρ) (hc : ResU.CompS ρo ρ ρt) :
    OpenS δ σ Tab (cbQ δ σ fun ls v => owner l' T' δ ls ⋆ Qa ls v) σ.length ds bs [] ls e ρt := by
  let en : LEnt := ⟨l', x', T', .mut, cr'⟩
  let Qo : List SRec → Val → WProp := fun ls v => owner l' T' δ ls ⋆ Qa ls v
  let Out : XT := OpenS δ σ Tab (cbQ δ σ Qo)
  let Mot : XT := fun k ds' αi αo ls e ρ => k = σ.length + 1 → αo = [] → ∀ d ds b bs,
    ds' = d :: ds → αi = b :: bs → (∀ a ∈ bs.getLast?, a ≤ β') →
      ∀ ρo ρt, owner l' T' δ ls ρo → ResU.CompS ρo ρ ρt → Out σ.length ds bs [] ls e ρt
  refine h Mot ?_ rfl rfl d ds b bs rfl rfl hβ ρo ρt ho hc
  rintro k ds' αi αo ls e ρ hF rfl rfl d ds b bs rfl rfl hβ ρo ρt ho hc
  refine openS_fold fun αs' hlt hch' => ?_
  rw [List.append_nil] at hch' ⊢
  rw [List.take_length]
  -- the bound 6.65 is handed: below the innermost of `αs′` and below `b`
  let γ : Life := b ⊓ αs'.headD ⊤
  have hγ : ∀ α, α < γ → α < b ∧ List.IsChain (· < ·) (α :: αs') := by
    intro α hα
    refine ⟨lt_of_lt_of_le hα inf_le_left, ?_⟩
    cases αs' with
    | nil => exact List.isChain_singleton α
    | cons a αs =>
        exact List.isChain_cons_cons.mpr ⟨lt_of_lt_of_le hα inf_le_right, hch'⟩
  have hrun : ∀ α, α < γ → boxTop (α :: αs') (vwS δ [] (en :: σ) (d :: ds) (α :: αs') ls ─⋆
      bodyS δ (en :: σ) Tab (cbQ δ (en :: σ) Qa) Mot (α :: αs') ls e) ρ := by
    intro α hα
    have := hF (α :: αs') (.cons (hγ α hα).1 hlt) (by rw [List.append_nil]; exact (hγ α hα).2)
    rwa [take_cons_length, List.append_nil] at this
  have hz : stratS αs' ρ := stratS_tail (hrun _ (down_lt γ)).2
  have hβ' : ∀ a ∈ αs'.getLast?, a ≤ β' := fun a ha => by
    obtain ⟨y, hy, hle⟩ := getLast?_le (hlt.imp fun _ _ => le_of_lt) a ha
    exact le_trans hle (hβ y hy)
  have hzo : stratS αs' ρo := fun a ha => owner_inStratum_le hP' (hβ' a ha) ho
  refine ⟨fun ρv τ hv hcv => ?_, fun a ha => (outlives_comp hc a).mpr ⟨hzo a ha, hz a ha⟩⟩
  have hlen' : αs'.length = σ.length := (vwS_length hv).2
  -- `τ = ℓ′ ↦ w ● (𝒱⟦T′⟧(w) ● (ρ ● ρv))`
  obtain ⟨w, ρl, ρP, hcl, hl, hvw⟩ := ho
  obtain ⟨R, hR, hoR⟩ := compS_reassoc hc hcv
  obtain ⟨Y, hY, hlY⟩ := compS_reassoc hcl hoR
  let Φ : List SRec → Expr → WProp := fun ls'' t ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧ NoOwn ρ₂ ∧
    (valPost (cbQ δ σ Qo αs') ls'' t ρ₁ ∨ stopS δ σ Tab Out αs' ls'' t ρ₁)
  refine wpG_garbage (wpG_M_frameX l' T' δ β' hP' w e ls Φ τ
    ⟨ρl, Y, hlY, hl, ρP, R, hY, hvw, γ, fun α hα => ?_⟩)
  have hrα := hrun α hα
  have hchα := (hγ α hα).2
  have hρα : ρ.InStratum α := stratS_head hchα hrα.2
  have hvα : ρv.InStratum α := vwS_inStratum hv α (head_lt_mem hchα)
  refine ⟨fun ρm W hm hcW => ?_, (outlives_comp hR α).mpr ⟨hρα, hvα⟩⟩
  -- the new view to the piece, if its drop flag asks for it; else garbage
  obtain ⟨a, g, hag, ha, hg⟩ := view_split (e := en) rfl (d := d) hm
  obtain ⟨Ra, hRa, hRag⟩ := compS_reassoc' hag hcW
  obtain ⟨va, hva, hρva⟩ := compS_reassoc hR hRa
  have hvin : vwS δ [] (en :: σ) (d :: ds) (α :: αs') ls va :=
    vwS_cons_other hl' ha hv (ResU.CompS.comm hva)
  have hbody := hrα.1 va Ra hvin hρva
  have htab : TabAt l' α Ra := tabAt_start rfl hρα hvα ha rfl hva hρva
  refine wpG_absorb (wpG_garbage (wpG_mono (fun ls'' t τ' hq => ?_)
    (wpG_tabAt l' α ls e _ htab hbody))) hg hRag
  obtain ⟨ht, hq⟩ := hq
  rcases hq with ⟨v, rfl, hqv⟩ | hs
  · -- a return: the owner of `ℓ′` handed back joins the answer
    refine ⟨τ', PMap.empty, ResU.comp_empty_right τ', noOwn_empty, ?_⟩
    refine box_mono (ownWand_mono fun ρ' ⟨o, r, hcor, hor, hr⟩ => ?_) τ' hqv
    refine ⟨ρ', PMap.empty, ResU.comp_empty_right ρ', noOwn_empty, Or.inl ⟨v, rfl, ?_⟩⟩
    exact ghostS_of_boxTop hlen' hch' ⟨⟨o, r, hcor, hor, hr.1⟩,
      fun a ha => (outlives_comp hcor a).mpr ⟨owner_inStratum_le hP' (hβ' a ha) hor,
        stratS_tail hr.2 a ha⟩⟩
  · rcases stopS_full hx (by simp [hlen']) hs with ⟨ds', hdl, ρ₁, ρ₂, hc₁₂, hd, hgs⟩ |
        ⟨ρ₁, ρ₂, hc₁₂, hno, hgs⟩
    · -- a stop: `σ`'s dropped views stay, the new one is garbage, the owner joins the
      -- continuation
      obtain ⟨d', ds₀, rfl⟩ : ∃ d' ds₀, ds' = d' :: ds₀ := by
        cases ds' with
        | nil => simp at hdl
        | cons d' ds₀ => exact ⟨d', ds₀, rfl⟩
      obtain ⟨g₁, q₁, hcq, hg₁, hq₁⟩ := dropS_cons_other (e := en) hl' hd
      obtain ⟨x, hcx, hgx⟩ := compS_reassoc hcq hc₁₂
      have hqα : q₁.InStratum α := by
        obtain ⟨y, -, hy⟩ := compS_lcomm hcx hgx
        exact tabAt_off ht ⟨_, hy⟩ fun k ψ e' hk =>
          hl' (hk ▸ dropS_places hq₁ k ψ e')
      refine ⟨x, g₁, ResU.CompS.comm hgx, dropE_noOwn hg₁,
        fun w ρa ρb ha hcab ρc ρd hvc hccd => ?_, (outlives_comp hcx α).mpr ⟨hqα, hgs.2⟩⟩
      obtain ⟨y, hy, hqy⟩ := compS_reassoc hcx hcab
      obtain ⟨z, hz, hqz⟩ := compS_reassoc hqy hccd
      obtain ⟨o, r, hcor, hor, hr⟩ := hgs.1 w ρa y ha hy ρc z hvc hz
      refine ⟨ρd, PMap.empty, ResU.comp_empty_right ρd, noOwn_empty,
        Or.inr (stopS_of_full hx.tail hlen' hq₁ ?_ hqz)⟩
      refine ghostS_of_boxTop hlen' hch' ⟨?_, fun a ha => (outlives_comp hcor a).mpr
        ⟨owner_inStratum_le hP' (hβ' a ha) hor, stratS_tail hr.2 a ha⟩⟩
      exact opTable_frame hLR .hole (fun _ => rfl) (owner l' T' δ)
        (fun _ _ _ he h => owner_local he h)
        (fun _ _ _ ρz _ hM hoz hc' => hM rfl rfl d' ds₀ α αs' rfl rfl hβ' ρz _ hoz
          (ResU.CompS.comm hc')) hr.1 hor (ResU.CompS.comm hcor)
    · refine ⟨ρ₁, ρ₂, hc₁₂, hno, box_mono (ownWand_mono fun _ ⟨_, _, _, _, hb⟩ => hb.1.elim) ρ₁ hgs⟩

end other

/-! ### The commutation lemma at every stack: a reborrow -/

section reborrow
variable {δ : LSub} {Tab : OpTab}

theorem seen_dup_congr {σ : LStack} {l : BoCa.Loc} :
    ∀ e ∈ σ, (e.l ∈ [l, l] ↔ e.l ∈ [l]) := fun _ _ => by simp

/-- The views handed at a re-lend of `σ·new`, where `new` reborrows the place of `σ`'s innermost
entry: the new entry's beside the rest of `σ`'s, the reborrowed entry shadowed. -/
theorem vwS_cons_reb {σ₀ : LStack} {en eh : LEnt} (hl : eh.l = en.l) {d dh : Bool}
    {ds : List Bool} {α αh : Life} {αs : List Life} {ls : List SRec} {a v w : WRes}
    (ha : vwE δ en d α ls a) (hv : vwS δ [en.l] σ₀ ds αs ls v) (hc : ResU.CompS a v w) :
    vwS δ [] (en :: eh :: σ₀) (d :: dh :: ds) (α :: αh :: αs) ls w := by
  have h₀ : vis [] en d = d := by simp [vis]
  have h₁ : vis [en.l] eh dh = false := by simp [vis, hl]
  have hcg : vwS δ [eh.l, en.l] σ₀ ds αs ls = vwS δ [en.l] σ₀ ds αs ls := by
    rw [hl]; exact vwS_seen_congr seen_dup_congr ds αs ls
  show (vwE δ en (vis [] en d) α ls ⋆
    (vwE δ eh (vis [en.l] eh dh) αh ls ⋆ vwS δ [eh.l, en.l] σ₀ ds αs ls)) w
  rw [h₀, h₁, hcg]
  exact ⟨a, v, hc, ha, PMap.empty, v, compS_empty_left v, ⟨rfl, trivial⟩, hv⟩

/-- The views handed at a re-lend of `σ`, its innermost entry's beside the rest. -/
theorem vwS_cons_split {eh : LEnt} {σ₀ : LStack} {dh : Bool} {ds : List Bool} {αh : Life}
    {αs : List Life} {ls : List SRec} {ρ : WRes} (h : vwS δ [] (eh :: σ₀) (dh :: ds) (αh :: αs) ls ρ) :
    (vwE δ eh dh αh ls ⋆ vwS δ [eh.l] σ₀ ds αs ls) ρ := by
  have h₀ : vis [] eh dh = dh := by simp [vis]
  have h' : (vwE δ eh (vis [] eh dh) αh ls ⋆ vwS δ [eh.l] σ₀ ds αs ls) ρ := h
  rwa [h₀] at h'

/-- What a stop of `σ·new` drops, `new` reborrowing the innermost entry's place: the new entry's
beside the rest of `σ`'s. -/
theorem dropS_cons_reb {σ₀ : LStack} {en eh : LEnt} (hl : eh.l = en.l) {d dh : Bool}
    {ds : List Bool} {ρ : WRes} (h : dropS [] (en :: eh :: σ₀) (d :: dh :: ds) ρ) :
    (dropE en d ⋆ dropS [en.l] σ₀ ds) ρ := by
  have h₀ : vis [] en d = d := by simp [vis]
  have h₁ : vis [en.l] eh dh = false := by simp [vis, hl]
  have hcg : dropS [eh.l, en.l] σ₀ ds = dropS [en.l] σ₀ ds := by
    rw [hl]; exact dropS_seen_congr seen_dup_congr ds
  have h' : (dropE en (vis [] en d) ⋆ (dropE eh (vis [en.l] eh dh) ⋆
    dropS [eh.l, en.l] σ₀ ds)) ρ := h
  rw [h₀, h₁, hcg] at h'
  obtain ⟨a, b, hc, ha, b₁, b₂, hb, ⟨rfl, -⟩, hb₂⟩ := h'
  rw [eq_of_compS_empty_left hb] at hc
  exact ⟨a, b₂, hc, ha, hb₂⟩

/-- What a stop of `σ` drops: its innermost entry's view beside the rest. -/
theorem dropS_cons_mk {eh : LEnt} {σ₀ : LStack} {ds : List Bool} {a b ρ : WRes}
    (ha : dropE eh true a) (hb : dropS [eh.l] σ₀ ds b) (hc : ResU.CompS a b ρ) :
    dropS [] (eh :: σ₀) (true :: ds) ρ := by
  have h₀ : vis [] eh true = true := by simp [vis]
  show (dropE eh (vis [] eh true) ⋆ dropS [eh.l] σ₀ ds) ρ
  rw [h₀]
  exact ⟨a, b, hc, ha, hb⟩

/-- **The commutation lemma at every stack, for a reborrow** (`withbor` (3) at `σ·new`). D16.1's
piece at `σ·new`, `new` lending again the place `ℓ` of `σ`'s innermost `mut` entry, every stop of
the row crossing every entry, is D16.1's piece at `σ`. One statement, the entries under the
innermost (`σ₀`) a parameter; by induction on `OpenS` at `σ·new`.

At each re-lend `αₕ :: αs₀` of `σ`: 6.66 unfolds the view `ℓ ↦ M_{αₕ}` `σ` is handed, 6.65 lends
its content below `αₕ` and below the new entry's last lifetime, and the piece at `σ·new` runs with
the rest of `σ`'s views beside the new one. At a return or a stop 6.65's exit hands the owner of
`ℓ` back and 6.66's exit refolds it into `ℓ ↦ M_{αₕ}`. At a return the view is garbage; at a stop
it is the cell the stop drops for the innermost entry of `σ`, beside the rest of `σ`'s (strictly
above the new lend: `wpG_tabAt`), and the continuation is again the piece at `σ·new`. -/
theorem stack_step_reborrow {σ₀ : LStack} {l : BoCa.Loc} {T : VTy} {x xh : LifeVar}
    {cr crh : UInt32 → Bool}
    (hx : AllCross (⟨l, x, T, .mut, cr⟩ :: ⟨l, xh, T, .mut, crh⟩ :: σ₀) Tab) {β : Life}
    (hP : ∀ ls w ρ, vC true T ls δ w ρ → ρ.InStratum β)
    {Qa : List SRec → Val → WProp} {d dh : Bool} {ds : List Bool} {b bh : Life}
    {bs : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenS δ (⟨l, x, T, .mut, cr⟩ :: ⟨l, xh, T, .mut, crh⟩ :: σ₀) Tab
      (cbQ δ (⟨l, x, T, .mut, cr⟩ :: ⟨l, xh, T, .mut, crh⟩ :: σ₀) Qa)
      (σ₀.length + 2) (d :: dh :: ds) (b :: bh :: bs) [] ls e ρ) :
    OpenS δ (⟨l, xh, T, .mut, crh⟩ :: σ₀) Tab (cbQ δ (⟨l, xh, T, .mut, crh⟩ :: σ₀) Qa)
      (σ₀.length + 1) (true :: ds) (bh :: bs) [] ls e ρ := by
  let en : LEnt := ⟨l, x, T, .mut, cr⟩
  let eh : LEnt := ⟨l, xh, T, .mut, crh⟩
  let Out : XT := OpenS δ (eh :: σ₀) Tab (cbQ δ (eh :: σ₀) Qa)
  let Mot : XT := fun k ds' αi αo ls e ρ => k = σ₀.length + 2 → αo = [] → ∀ d dh ds b bh bs,
    ds' = d :: dh :: ds → αi = b :: bh :: bs → Out (σ₀.length + 1) (true :: ds) (bh :: bs) [] ls e ρ
  refine h Mot ?_ rfl rfl d dh ds b bh bs rfl rfl
  rintro k ds' αi αo ls e ρ hF rfl rfl d dh ds b bh bs rfl rfl
  refine openS_fold fun αs' hlt hch' => ?_
  rw [List.append_nil] at hch' ⊢
  have htk : (eh :: σ₀).take (σ₀.length + 1) = eh :: σ₀ := by simp
  rw [htk]
  obtain ⟨αh, αs, rfl⟩ : ∃ αh αs, αs' = αh :: αs := by
    cases αs' with
    | nil => cases hlt
    | cons αh αs => exact ⟨αh, αs, rfl⟩
  obtain ⟨hαh, hlt₀⟩ := List.forall₂_cons.mp hlt
  let γ : Life := b ⊓ αh
  have hγ : ∀ α, α < γ → α < b ∧ List.IsChain (· < ·) (α :: αh :: αs) := fun α hα =>
    ⟨lt_of_lt_of_le hα inf_le_left,
      List.isChain_cons_cons.mpr ⟨lt_of_lt_of_le hα inf_le_right, hch'⟩⟩
  have hrun : ∀ α, α < γ → boxTop (α :: αh :: αs)
      (vwS δ [] (en :: eh :: σ₀) (d :: dh :: ds) (α :: αh :: αs) ls ─⋆
        bodyS δ (en :: eh :: σ₀) Tab (cbQ δ (en :: eh :: σ₀) Qa) Mot (α :: αh :: αs) ls e) ρ := by
    intro α hα
    have := hF (α :: αh :: αs) (.cons (hγ α hα).1 (.cons hαh hlt₀))
      (by rw [List.append_nil]; exact (hγ α hα).2)
    have htk' : (en :: eh :: σ₀).take (σ₀.length + 2) = en :: eh :: σ₀ := by simp
    rwa [htk', List.append_nil] at this
  have hz : stratS (αh :: αs) ρ := stratS_tail (hrun _ (down_lt γ)).2
  refine ⟨fun ρv τ hv hcv => ?_, hz⟩
  have hlen' : (αh :: αs).length = (eh :: σ₀).length := (vwS_length hv).2
  obtain ⟨vh, v₀, hcv₀, hvh, hv₀⟩ := vwS_cons_split hv
  -- `τ = (ℓ ↦ M_{αₕ}) ● (ρ ● v₀)`: 6.66 at the view `σ` is handed
  obtain ⟨rest, hrest, hτ⟩ := compS_lcomm hcv₀ hcv
  let Φ : List SRec → Expr → WProp := fun ls'' t ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
    NoOwn ρ₂ ∧ (valPost (cbQ δ (eh :: σ₀) Qa (αh :: αs)) ls'' t ρ₁ ∨
      stopS δ (eh :: σ₀) Tab Out (αh :: αs) ls'' t ρ₁)
  refine wpG_garbage (wpG_M_antiFrameX l αh T δ e ls Φ τ ⟨vh, rest, hτ, hvh, ?_⟩)
  intro v ρa ρb hρa hcab ρc ρd hρc hccd
  -- 6.65 lends the content below `αₕ`
  obtain ⟨Y, hY, hdY⟩ := compS_reassoc (ResU.CompS.comm hcab) hccd
  refine wpG_M_frameX l T δ β hP v e ls _ ρd
    ⟨ρa, Y, hdY, hρa, ρc, rest, ResU.CompS.comm hY, hρc, γ, fun α hα => ?_⟩
  have hrα := hrun α hα
  have hchα := (hγ α hα).2
  have hρα : ρ.InStratum α := stratS_head hchα hrα.2
  have hv₀α : v₀.InStratum α := vwS_inStratum hv₀ α fun a ha =>
    head_lt_mem hchα a (List.mem_cons_of_mem _ ha)
  have hrα' : (ResU.CompS ρ v₀ rest) := ResU.CompS.comm (ResU.CompS.comm hrest)
  refine ⟨fun ρm W hm hcW => ?_, (outlives_comp hrα' α).mpr ⟨hρα, hv₀α⟩⟩
  obtain ⟨a, g, hag, ha, hg⟩ := view_split (e := en) rfl (d := d) hm
  obtain ⟨Ra, hRa, hRag⟩ := compS_reassoc' hag hcW
  obtain ⟨va, hva, hρva⟩ := compS_reassoc hrα' hRa
  have hvin : vwS δ [] (en :: eh :: σ₀) (d :: dh :: ds) (α :: αh :: αs) ls va :=
    vwS_cons_reb (eh := eh) rfl ha hv₀ (ResU.CompS.comm hva)
  have hbody := hrα.1 va Ra hvin hρva
  have htab : TabAt l α Ra := tabAt_start rfl hρα hv₀α ha rfl hva hρva
  refine wpG_absorb (wpG_garbage (wpG_mono (fun ls'' t τ' hq => ?_)
    (wpG_tabAt l α ls e _ htab hbody))) hg hRag
  obtain ⟨ht, hq⟩ := hq
  rcases hq with ⟨u, rfl, hqv⟩ | hs
  · -- a return: the owner refolds into the view, which is garbage
    refine ⟨τ', PMap.empty, ResU.comp_empty_right τ', noOwn_empty, ?_⟩
    refine box_mono (ownWand_mono fun ρ' ⟨o, r, hcor, hor, hr⟩ => ?_) τ' hqv
    obtain ⟨w, ol, oP, hco, hol, hoP⟩ := hor
    obtain ⟨y, hy, hρ'⟩ := compS_reassoc hco hcor
    refine ⟨w, ol, y, hρ', hol, oP, r, hy, hoP, fun ρv' z hv' hcz => ?_⟩
    exact ⟨r, ρv', hcz, noOwn_ptoMutS hv', Or.inl ⟨u, rfl,
      ghostS_of_boxTop hlen' hch' ⟨hr.1, stratS_tail hr.2⟩⟩⟩
  · rcases stopS_full hx (by simp [hlen']) hs with ⟨ds', hdl, ρ₁, ρ₂, hc₁₂, hd, hgs⟩ |
        ⟨ρ₁, ρ₂, hc₁₂, hno, hgs⟩
    · obtain ⟨d', dh', ds₀, rfl⟩ : ∃ d' dh' ds₀, ds' = d' :: dh' :: ds₀ := by
        match ds', hdl with
        | d' :: dh' :: ds₀, _ => exact ⟨d', dh', ds₀, rfl⟩
      obtain ⟨g₁, q₁, hcq, hg₁, hq₁⟩ := dropS_cons_reb (en := en) (eh := eh) rfl hd
      obtain ⟨x₁, hcx, hgx⟩ := compS_reassoc hcq hc₁₂
      have hqα : q₁.InStratum α := by
        obtain ⟨y, -, hy⟩ := compS_lcomm hcx hgx
        exact tabAt_off ht ⟨_, hy⟩ fun k ψ e' hk =>
          dropS_unseen hq₁ k ψ e' (List.mem_singleton.mpr hk)
      refine ⟨x₁, g₁, ResU.CompS.comm hgx, dropE_noOwn hg₁,
        fun w ρa' ρb' ha' hcab' ρc' ρd' hvc hccd' => ?_, (outlives_comp hcx α).mpr ⟨hqα, hgs.2⟩⟩
      obtain ⟨y, hy, hqy⟩ := compS_reassoc hcx hcab'
      obtain ⟨z, hz, hqz⟩ := compS_reassoc hqy hccd'
      obtain ⟨o, r, hcor, hor, hr⟩ := hgs.1 w ρa' y ha' hy ρc' z hvc hz
      obtain ⟨w', ol, oP, hco, hol, hoP⟩ := hor
      -- `ρd′ = q₁ ● (ol ● (oP ● r))`
      obtain ⟨y₁, hy₁, hzy⟩ := compS_reassoc hco hcor
      obtain ⟨y₂, hy₂, hqd⟩ := compS_lcomm hzy hqz
      obtain ⟨y₃, hy₃, hy₂'⟩ := compS_lcomm hy₁ hy₂
      refine ⟨w', ol, y₂, hqd, hol, oP, y₃, hy₂', hoP, fun ρv' z' hv' hcz' => ?_⟩
      -- the refolded view is the cell the stop drops for `σ`'s innermost entry
      obtain ⟨qv, hqv, hz'⟩ := compS_exch hy₃ hcz'
      refine ⟨z', PMap.empty, ResU.comp_empty_right z', noOwn_empty, Or.inr ?_⟩
      refine stopS_of_full hx.tail hlen'
        (dropS_cons_mk (eh := eh) (dropE_of_vwE (e := eh) (d := true) hv') hq₁
          (ResU.CompS.comm hqv)) ?_ hz'
      refine ghostS_of_boxTop hlen' hch' ⟨?_, stratS_tail hr.2⟩
      exact opTable_mono _ _ _ _ _ _ (fun _ _ _ hM => hM rfl rfl d' dh' ds₀ α αh αs rfl rfl)
        hr.1
    · refine ⟨ρ₁, ρ₂, hc₁₂, hno, box_mono (ownWand_mono fun _ ⟨_, _, _, _, hb⟩ => hb.1.elim) ρ₁ hgs⟩

end reborrow

/-! ### `Relendable_σ` is closed under `⋆`, at every stack -/

section sep
variable {δ : LSub}

/-- At an entry, two parts cannot both hold a `mut` view: two `mut` cells at one place do not
compose (`dropC_disj`). -/
theorem vwE_disj {e : LEnt} (hk : e.k = .mut) {d₁ d₂ : Bool} {α : Life} {ls : List SRec}
    {a₁ a₂ a : WRes} (h₁ : vwE δ e d₁ α ls a₁) (h₂ : vwE δ e d₂ α ls a₂) (hc : ResU.CompS a₁ a₂ a) :
    ¬ (d₁ = true ∧ d₂ = true) := by
  rintro ⟨rfl, rfl⟩
  obtain ⟨l, x, T, k, cr⟩ := e
  simp only at hk; subst hk
  exact dropC_disj (dropC_of_view h₁) (dropC_of_view h₂) (ResU.comp_empty_right _)
    (ResU.comp_empty_right _) hc

/-- **Two `imm` views at one place join into one** (`[TR]` 6.43, `I Agree`): the cells compose
only at the same value and payload, and the composite is the cell at the union of the sets. -/
theorem ptoImmS_join {l : BoCa.Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {a₁ a₂ a : WRes} (h₁ : ptoImmS l α ls P a₁) (h₂ : ptoImmS l α ls P a₂)
    (hc : ResU.CompS a₁ a₂ a) : ptoImmS l α ls P a := by
  obtain ⟨s₁, u₁, σ₁, hs₁, ls₁, rfl, hP₁, hα₁, hls₁⟩ := h₁
  obtain ⟨s₂, u₂, σ₂, hs₂, ls₂, rfl, hP₂, hα₂, hls₂⟩ := h₂
  rcases ResU.Comp.get hc l with ⟨e₁, -, -⟩ | ⟨_, -, e₂, -⟩ | ⟨_, e₁, -, -⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, -, hψ⟩
  · rw [ResU.single_get_self] at e₁; exact absurd e₁ (by simp)
  · rw [ResU.single_get_self] at e₂; exact absurd e₂ (by simp)
  · rw [ResU.single_get_self] at e₁; exact absurd e₁ (by simp)
  · rw [ResU.single_get_self] at e₁ e₂
    cases Option.some.inj e₁; cases Option.some.inj e₂
    obtain ⟨t₁, t₂, v, ρ, k₁, k₂, k₃, f₁, f₂, -⟩ := hψ
    obtain ⟨g₁, g₂, g₃⟩ := CellU.immOf_inj f₁
    subst t₁ v ρ
    obtain ⟨g₄, g₅, g₆⟩ := CellU.immOf_inj f₂
    subst t₂ u₂ σ₂
    have hcu := ResU.compS_single_imm l s₁ s₂ u₁ σ₁ hs₁ hs₂ k₃
    rw [ResU.CompS.functional hc hcu]
    have hm : (s₁ ∪ s₂).meet = s₁.meet ⊓ s₂.meet := rfl
    rcases le_total s₁.meet s₂.meet with hle | hle
    · refine ⟨s₁ ∪ s₂, u₁, σ₁, k₃, ls₁, rfl, hP₁, le_inf hα₁ hα₂, ?_⟩
      rw [hm, inf_eq_left.mpr hle]; exact hls₁
    · refine ⟨s₁ ∪ s₂, u₁, σ₁, k₃, ls₂, rfl, hP₂, le_inf hα₁ hα₂, ?_⟩
      rw [hm, inf_eq_right.mpr hle]; exact hls₂

/-- **The views of one entry join.** At most one is a `mut` view; two `imm` views are one. -/
theorem vwE_join {e : LEnt} {d₁ d₂ : Bool} {α : Life} {ls : List SRec} {a₁ a₂ a : WRes}
    (h₁ : vwE δ e d₁ α ls a₁) (h₂ : vwE δ e d₂ α ls a₂) (hc : ResU.CompS a₁ a₂ a) :
    vwE δ e (d₁ || d₂) α ls a := by
  cases d₁ with
  | false =>
      obtain ⟨rfl, -⟩ := h₁
      rw [eq_of_compS_empty_left hc]; exact h₂
  | true =>
      cases d₂ with
      | false =>
          obtain ⟨rfl, -⟩ := h₂
          rw [ResU.CompS.functional hc (ResU.comp_empty_right a₁)]; exact h₁
      | true =>
          obtain ⟨l, x, T, k, cr⟩ := e
          cases k with
          | «mut» => exact (vwE_disj rfl h₁ h₂ hc ⟨rfl, rfl⟩).elim
          | imm v => exact ptoImmS_join h₁ h₂ hc

/-- **A view handed at a re-lend splits** between two parts: an `imm` view is duplicated
(`[TR]` 6.116), and a `mut` view goes to the one part that dropped it. -/
theorem vwE_split {e : LEnt} {d₁ d₂ : Bool} (hd : e.k = .mut → ¬ (d₁ = true ∧ d₂ = true))
    {α : Life} {ls : List SRec} {a : WRes} (h : vwE δ e (d₁ || d₂) α ls a) :
    ∃ a₁ a₂, ResU.CompS a₁ a₂ a ∧ vwE δ e d₁ α ls a₁ ∧ vwE δ e d₂ α ls a₂ := by
  cases d₁ with
  | false => exact ⟨PMap.empty, a, compS_empty_left a, ⟨rfl, trivial⟩, by simpa using h⟩
  | true =>
      cases d₂ with
      | false => exact ⟨a, PMap.empty, ResU.comp_empty_right a, h, ⟨rfl, trivial⟩⟩
      | true =>
          obtain ⟨l, x, T, k, cr⟩ := e
          cases k with
          | «mut» => exact (hd rfl ⟨rfl, rfl⟩).elim
          | imm v => exact ptoImmS_dup h

theorem vis_or (seen : List BoCa.Loc) (e : LEnt) (d₁ d₂ : Bool) :
    vis seen e (d₁ || d₂) = (vis seen e d₁ || vis seen e d₂) := by
  cases d₁ <;> cases d₂ <;> simp [vis]

/-- At no entry do both parts hold a `mut` view. -/
def MutDisj : List BoCa.Loc → LStack → List Bool → List Bool → Prop
  | seen, e :: σ, d₁ :: ds₁, d₂ :: ds₂ =>
      (e.k = .mut → ¬ (vis seen e d₁ = true ∧ vis seen e d₂ = true)) ∧
        MutDisj (e.l :: seen) σ ds₁ ds₂
  | _, _, _, _ => True

/-- **The views of two parts join**, entry by entry; by induction on the stack. -/
theorem vwS_join : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds₁ ds₂ : List Bool} {αs : List Life}
    {ls : List SRec} {ρ₁ ρ₂ ρ : WRes}, vwS δ seen σ ds₁ αs ls ρ₁ → vwS δ seen σ ds₂ αs ls ρ₂ →
      ResU.CompS ρ₁ ρ₂ ρ →
      vwS δ seen σ (List.zipWith (· || ·) ds₁ ds₂) αs ls ρ ∧ MutDisj seen σ ds₁ ds₂
  | _, [], [], [], [], _, _, _, _, h₁, h₂, hc => by
      obtain ⟨rfl, -⟩ := h₁; obtain ⟨rfl, -⟩ := h₂
      rw [eq_of_compS_empty_left hc]; exact ⟨⟨rfl, trivial⟩, trivial⟩
  | seen, e :: σ, d₁ :: ds₁, d₂ :: ds₂, α :: αs, ls, _, _, _,
      ⟨a₁, r₁, hc₁, ha₁, hr₁⟩, ⟨a₂, r₂, hc₂, ha₂, hr₂⟩, hc => by
      obtain ⟨ac, bd, hac, hbd, hρ⟩ := compS_four hc₁ hc₂ hc
      obtain ⟨hv, hdisj⟩ := vwS_join hr₁ hr₂ hbd
      refine ⟨⟨ac, bd, hρ, ?_, hv⟩, fun hk => vwE_disj hk ha₁ ha₂ hac, hdisj⟩
      rw [vis_or]; exact vwE_join ha₁ ha₂ hac
  | _, [], [], _ :: _, αs, _, _, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, [], _ :: _, _, αs, _, _, _, _, h, _, _ => by cases αs <;> exact h.elim
  | _, _ :: _, [], _, αs, _, _, _, _, h, _, _ => by cases αs <;> exact h.elim
  | _, _ :: _, _ :: _, [], αs, _, _, _, _, _, h, _ => by cases αs <;> exact h.elim
  | _, [], [], [], _ :: _, _, _, _, _, h, _, _ => h.elim
  | _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, h, _, _ => h.elim

/-- **The views handed at a re-lend split between the two parts**; by induction on the stack. -/
theorem vwS_split : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds₁ ds₂ : List Bool} {αs : List Life}
    {ls : List SRec} {ρ : WRes}, MutDisj seen σ ds₁ ds₂ → ds₁.length = σ.length →
      ds₂.length = σ.length → vwS δ seen σ (List.zipWith (· || ·) ds₁ ds₂) αs ls ρ →
      ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vwS δ seen σ ds₁ αs ls ρ₁ ∧ vwS δ seen σ ds₂ αs ls ρ₂
  | _, [], [], [], [], _, _, _, _, _, h => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩
  | seen, e :: σ, d₁ :: ds₁, d₂ :: ds₂, α :: αs, ls, _, ⟨hd, hdisj⟩, hl₁, hl₂,
      ⟨a, r, hc, ha, hr⟩ => by
      rw [vis_or] at ha
      obtain ⟨a₁, a₂, hca, ha₁, ha₂⟩ := vwE_split hd ha
      obtain ⟨r₁, r₂, hcr, hr₁, hr₂⟩ := vwS_split hdisj (by simpa using hl₁) (by simpa using hl₂) hr
      obtain ⟨x, y, hx, hy, hxy⟩ := compS_four hca hcr hc
      exact ⟨x, y, hxy, ⟨a₁, r₁, hx, ha₁, hr₁⟩, ⟨a₂, r₂, hy, ha₂, hr₂⟩⟩
  | _, [], [], [], _ :: _, _, _, _, _, _, h => h.elim
  | _, [], _ :: _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _, [], [], _ :: _, _, _, _, _, _, hl, _ => by simp at hl
  | _, _ :: _, [], _, _, _, _, _, hl, _, _ => by simp at hl
  | _, _ :: _, _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl
  | _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, h => h.elim

/-- **`Relendable_σ` is closed under `⋆`, at every stack.** The remainders compose and stay in
`[top]`; the dropped views join entry by entry (`vwS_join`: a `mut` view in at most one part,
two `imm` views one cell); at a re-lend the views handed split back (`vwS_split`: an `imm` view
duplicated), each part thawed by its own. One statement, `σ` a parameter; the entries are handled
by one induction on the stack. -/
theorem relendableS_sep {seen : List BoCa.Loc} {σ : LStack} {P Q : List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} :
    Entails (RelendableS δ seen σ P αs ls ⋆ RelendableS δ seen σ Q αs ls)
      (RelendableS δ seen σ (fun αs' ls' => P αs' ls' ⋆ Q αs' ls') αs ls) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨ds₁, ρz₁, ρn₁, hc₁, hn₁, hz₁, hth₁⟩, ⟨ds₂, ρz₂, ρn₂, hc₂, hn₂, hz₂, hth₂⟩⟩
  obtain ⟨ρz, ρn, hcz, hcn, hcρ⟩ := compS_four hc₁ hc₂ hc
  obtain ⟨hn, hdisj⟩ := vwS_join hn₁ hn₂ hcn
  refine ⟨_, ρz, ρn, hcρ, hn, fun a ha => (outlives_comp hcz a).mpr ⟨hz₁ a ha, hz₂ a ha⟩,
    fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  obtain ⟨ρv₁, ρv₂, hcv₁₂, hv₁, hv₂⟩ :=
    vwS_split hdisj (vwS_length hn₁).1 (vwS_length hn₂).1 hv
  obtain ⟨x, y, hx, hy, hxy⟩ := compS_four hcz hcv₁₂ hcv
  exact ⟨x, y, hxy, hth₁ ls' (he.left hcz) αs' hr ρv₁ x hv₁ hx,
    hth₂ ls' (he.right hcz) αs' hr ρv₂ y hv₂ hy⟩

end sep

/-! ### An `imm` entry at `σ·new`, at every stack -/

section imm
variable {δ : LSub} {Tab : OpTab}

/-- An `imm` view is Kripke along `Ext`, as `ptoMutS_local`. -/
theorem ptoImmS_local {l : BoCa.Loc} {α : Life} {ls ls' : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (hk : Ext ls ls' ρ) (h : ptoImmS l α ls P ρ) :
    ptoImmS l α ls' P ρ := by
  obtain ⟨s, u, σ, hσ, ls₀, hρ, hP, hα, hls₀⟩ := h
  have him : CellIn ρ s.meet :=
    ⟨l, _, by rw [hρ]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
  refine ⟨s, u, σ, hσ, ls₀, hρ, hP, hα, fun x => ?_⟩
  rw [hls₀ x]
  exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ him x hb).mp hx, hb⟩,
    fun ⟨hx, hb⟩ => ⟨(hk.2 _ him x hb).mpr hx, hb⟩⟩

theorem vwE_local {e : LEnt} {d : Bool} {α : Life} {ls ls' : List SRec} {ρ : WRes}
    (hk : Ext ls ls' ρ) (h : vwE δ e d α ls ρ) : vwE δ e d α ls' ρ := by
  cases d with
  | false => exact h
  | true =>
      obtain ⟨l, x, T, k, cr⟩ := e
      cases k with
      | «mut» => exact ptoMutS_local hk h
      | imm v => exact ptoImmS_local hk h

/-- The views of a stack are Kripke along `Ext`. -/
theorem vwS_local : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {αs : List Life}
    {ls ls' : List SRec} {ρ : WRes}, Ext ls ls' ρ → vwS δ seen σ ds αs ls ρ →
      vwS δ seen σ ds αs ls' ρ
  | _, [], [], [], _, _, _, _, h => h
  | _, _ :: _, _ :: _, _ :: _, _, _, _, hk, ⟨a, b, hc, ha, hb⟩ =>
      ⟨a, b, hc, vwE_local (hk.left hc) ha, vwS_local (hk.right hc) hb⟩
  | _, [], [], _ :: _, _, _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, h => h.elim

/-- **A stop's continuations, at every extension.** A table whose operations are local owes, at
each list, the continuation at every `Ext`-extension of it. -/
theorem opTable_shift (hL : Tab.Local) (hLR : LinResume Tab) {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (h : opTable Tab ls t Φ ρ) :
    opTable Tab ls t (fun ls₂ e' ρ' => ∀ ls₃, Ext ls₂ ls₃ ρ' → Φ ls₃ e' ρ') ρ := by
  rcases h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    have hq := (hLR n i en hT).2
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩
      ⟨ρa, ρk, hcak, hA, hu, fun ls₂ he₂ => ⟨fun w ρb ρ' hB hcb ls₃ he₃ => ?_,
        fun hq' => absurd hq hq'⟩⟩⟩
    have he : Ext ls ls₃ ρk := he₂.trans (he₃.left hcb)
    exact (hcont ls₃ he).1 w ρb ρ' ((hL n i en hT ls₂ ls₃ w ρb (he₃.right hcb)).2 hB) hcb
  · exact Or.inr ⟨K, n, i, v, en, hp⟩

/-- The table at the new lend, at an `imm` view of `ℓ′`. -/
theorem tabAt_viewI {l : BoCa.Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {ρ : WRes} (h : ptoImmS l α ls P ρ) : TabAt l α ρ := by
  obtain ⟨s, u, σ, hσ, ls₀, rfl, -, hα, -⟩ := h
  refine ⟨ResU.inStratum_single l (show s.meet ⊐ ↓α from lt_of_lt_of_le (down_lt α) hα),
    fun k ψ hk e => ?_⟩
  rw [ResU.single_get_ne _ hk] at e
  exact absurd e (by simp)

/-- What 6.64's callback leaves, before the owner of `ℓ′` is handed back: an answer, or a stop
with `σ`'s dropped views beside a share in `[top αs]` owing the piece at `σ`. Both carried along
`Ext`, as 6.64's `hQ` asks. -/
def Q64 (δ : LSub) (σ : LStack) (Tab : OpTab) (Qo : List SRec → Val → WProp) (αs : List Life) :
    List SRec → Expr → WProp := fun ls'' t ρ =>
  valPost (fun ls u => boxTop αs (Qo ls u)) ls'' t ρ ∨
    ∃ ds, (dropS [] σ ds ⋆ boxTop αs (opTable Tab ls'' t fun ls' e' =>
      OpenS δ σ Tab (cbQ δ σ Qo) σ.length ds αs [] ls' e')) ρ

theorem q64_ext (hL : Tab.Local) {σ : LStack} {Qo : List SRec → Val → WProp}
    (hQo : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qo ls₁ u ρ → Qo ls₂ u ρ) {αs : List Life} :
    ∀ ls₁ ls₂ (t : Expr) ρ, Ext ls₁ ls₂ ρ → Q64 δ σ Tab Qo αs ls₁ t ρ → Q64 δ σ Tab Qo αs ls₂ t ρ := by
  rintro ls₁ ls₂ t ρ he (⟨u, rfl, hb⟩ | ⟨ds, ρ₁, ρ₂, hc, hd, hb⟩)
  · exact Or.inl ⟨u, rfl, hQo _ _ _ _ he hb.1, hb.2⟩
  · exact Or.inr ⟨ds, ρ₁, ρ₂, hc, hd, opTable_extR hL (he.right hc) hb.1, hb.2⟩

/-- The body of 6.64's callback at the list `ls₁` 6.64 extended, at each re-lend `αs` of `σ` and
each `α` below it and below `b`: the piece's share is in `[top (α :: αs)]`, and handed `σ`'s
views and the new `imm` view, it runs to 6.64's postcondition. -/
def ImmBody (δ : LSub) (σ : LStack) (Tab : OpTab) (l' : BoCa.Loc) (v : Val) (T' : VTy)
    (Qo : List SRec → Val → WProp) (ds : List Bool) (b : Life) (bs : List Life) (ls₁ : List SRec)
    (e : Expr) (ρ : WRes) : Prop :=
  (∀ αs α, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) (α :: αs) → α < b →
    stratS (α :: αs) ρ) ∧
  ∀ αs α, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) (α :: αs) → α < b →
    ∀ ρv, vwS δ [] σ ds αs ls₁ ρv → ∀ ρm, ptoImmS l' α ls₁ (fun ls₀ => vC true T' ls₀ δ) ρm →
      ∀ R W, ResU.CompS ρ ρv R → ResU.CompS R ρm W →
        wpG ls₁ e (fun ls'' t => box α (ptoOwn l' v ─⋆ (vC true T' ls'' δ v ─⋆
          Q64 δ σ Tab Qo αs ls'' t))) W

/-- **6.64 folds the `imm` entry back, at every stack.** The owner of `ℓ′` beside a share whose
6.64 body holds at every `Ext`-extension of the list is D16.1's piece at `σ`, answering with the
owner. At each re-lend of `σ` 6.64 lends `ℓ′` below it at a list it extends; the body runs there
with `σ`'s views carried along (`vwS_local`). -/
theorem fold_imm {σ : LStack} (hx : AllCross σ Tab) {l' : BoCa.Loc} {v : Val} {T' : VTy}
    (hadm : AdmWf T' δ) {β' : Life} (hP' : ∀ ls w ρ, vC true T' ls δ w ρ → ρ.InStratum β')
    {Qa : List SRec → Val → WProp}
    (hQK : ∀ αs : List Life, ∀ ls₁ ls₂ (t : Expr) ρ, Ext ls₁ ls₂ ρ →
      Q64 δ σ Tab (fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) αs ls₁ t ρ →
      Q64 δ σ Tab (fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) αs ls₂ t ρ)
    {ds : List Bool} {b : Life} {bs : List Life} (hβ : ∀ a ∈ bs.getLast?, a ≤ β')
    {ls : List SRec} {e : Expr} {ρo ρ ρt : WRes}
    (H : ∀ ls₁, Ext ls ls₁ ρ →
      ImmBody δ σ Tab l' v T' (fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) ds b bs ls₁ e ρ)
    (ho : ownerI l' v T' δ ls ρo) (hc : ResU.CompS ρo ρ ρt) :
    OpenS δ σ Tab (cbQ δ σ fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) σ.length ds bs [] ls e ρt := by
  refine openS_fold fun αs hlt hch => ?_
  rw [List.append_nil] at hch ⊢
  rw [List.take_length]
  let γ : Life := b ⊓ αs.headD ⊤
  have hγ : ∀ α, α < γ → α < b ∧ List.IsChain (· < ·) (α :: αs) := by
    intro α hα
    refine ⟨lt_of_lt_of_le hα inf_le_left, ?_⟩
    cases αs with
    | nil => exact List.isChain_singleton α
    | cons a αs => exact List.isChain_cons_cons.mpr ⟨lt_of_lt_of_le hα inf_le_right, hch⟩
  have H₀ := H ls (Ext.refl ls ρ)
  have hz : stratS αs ρ := stratS_tail
    (H₀.1 αs _ hlt (hγ _ (down_lt γ)).2 (hγ _ (down_lt γ)).1)
  have hβ' : ∀ a ∈ αs.getLast?, a ≤ β' := fun a ha => by
    obtain ⟨y, hy, hle⟩ := getLast?_le (hlt.imp fun _ _ => le_of_lt) a ha
    exact le_trans hle (hβ y hy)
  have hzo : stratS αs ρo := fun a ha => by
    obtain ⟨ρ₁, ρ₂, hc₁, h₁, h₂⟩ := ho
    exact (outlives_comp hc₁ a).mpr ⟨by rw [h₁]; exact ResU.inStratum_single_own a l' v,
      (hP' ls v ρ₂ h₂).mono (hβ' a ha)⟩
  refine ⟨fun ρv τ hv hcv => ?_, fun a ha => (outlives_comp hc a).mpr ⟨hzo a ha, hz a ha⟩⟩
  have hlen : αs.length = σ.length := (vwS_length hv).2
  obtain ⟨ρl, ρP, hcl, hl, hvP⟩ := ho
  obtain ⟨R, hR, hoR⟩ := compS_reassoc hc hcv
  obtain ⟨Y, hY, hlY⟩ := compS_reassoc hcl hoR
  refine wpG_mono (fun ls'' t τ' hq => ?_) (wpG_I_frameX l' T' δ hadm v e ls _ (hQK αs) τ
    ⟨ρl, Y, hlY, hl, ρP, R, hY, hvP, γ, fun α hα => ?_⟩)
  · -- 6.64's postcondition is the piece's at `σ`
    rcases hq with ⟨u, rfl, hu⟩ | ⟨ds', ρ₁, ρ₂, hc₁₂, hd, hb⟩
    · exact Or.inl ⟨u, rfl, ghostS_of_boxTop hlen hch hu⟩
    · exact Or.inr (stopS_of_full hx hlen hd (ghostS_of_boxTop hlen hch hb) hc₁₂)
  · obtain ⟨hαb, hchα⟩ := hγ α hα
    have hρα : ρ.InStratum α := stratS_head hchα (H₀.1 αs α hlt hchα hαb)
    have hvα : ρv.InStratum α := vwS_inStratum hv α (head_lt_mem hchα)
    refine ⟨fun ls₁ hadd _ ρm W hm hcW => ?_, (outlives_comp hR α).mpr ⟨hρα, hvα⟩⟩
    exact (H ls₁ (ext_add hadd hρα)).2 αs α hlt hchα hαb ρv
      (vwS_local (ext_add hadd hvα) hv) ρm hm R W hR hcW

/-- An `imm` view handed to the piece, if its drop flag asks for it; else garbage. -/
theorem viewI_split {e : LEnt} {v : Val} (he : e.k = .imm v) {d : Bool} {α : Life}
    {ls : List SRec} {ρm : WRes} (hm : ptoImmS e.l α ls (fun ls₀ => vC true e.T ls₀ δ) ρm) :
    ∃ a g, ResU.CompS a g ρm ∧ vwE δ e d α ls a ∧ NoOwn g := by
  cases d with
  | true =>
      refine ⟨ρm, PMap.empty, ResU.comp_empty_right ρm, ?_, noOwn_empty⟩
      obtain ⟨l, x, T, k, cr⟩ := e; simp only at he; subst he; exact hm
  | false => exact ⟨PMap.empty, ρm, compS_empty_left ρm, ⟨rfl, trivial⟩, noOwn_ptoImmS hm⟩

/-- **An `imm` entry at `σ·new`, at every stack** (`[TR]` 6.64 at a resuming table, its depth-1
form `ewpTS_I_frameR`). D16.1's piece at `σ·new`, `new` an `imm` lend of a place `ℓ′` that `σ`
does not hold, every stop of the row crossing every entry, at every `Ext`-extension of the list,
is, beside the owner `ℓ′ ↦ v ⋆ 𝒱⟦T′⟧(v)`, D16.1's piece at `σ` answering with that owner. One
statement, `σ` a parameter; by induction on `OpenS` at `σ·new`.

At each re-lend of `σ`, 6.64 lends `ℓ′` below it at a list it extends with a fresh record
(`fold_imm`), and the piece at `σ·new` runs there. At a stop 6.64's exit hands the owner back (the
internal view is the garbage the ghost end removes), the owner joins the continuation, which the
table owes at every extension of the list (`opTable_shift`), so at the next re-lend 6.64 applies
again at a fresh lifetime with a new record. -/
theorem stack_step_imm (hLR : LinResume Tab) (hL : Tab.Local) {σ : LStack} {l' : BoCa.Loc}
    {x' : LifeVar} {T' : VTy} {v : Val} {cr' : UInt32 → Bool}
    (hx : AllCross (⟨l', x', T', .imm v, cr'⟩ :: σ) Tab) (hl' : l' ∉ σ.map LEnt.l)
    (hadm : AdmWf T' δ) {β' : Life} (hP' : ∀ ls w ρ, vC true T' ls δ w ρ → ρ.InStratum β')
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {d : Bool} {ds : List Bool} {b : Life} {bs : List Life} (hβ : ∀ a ∈ bs.getLast?, a ≤ β')
    {ls : List SRec} {e : Expr} {ρo ρ ρt : WRes} (ho : ownerI l' v T' δ ls ρo)
    (h : ∀ ls₁, Ext ls ls₁ ρ →
      OpenS δ (⟨l', x', T', .imm v, cr'⟩ :: σ) Tab (cbQ δ (⟨l', x', T', .imm v, cr'⟩ :: σ) Qa)
        (σ.length + 1) (d :: ds) (b :: bs) [] ls₁ e ρ) (hc : ResU.CompS ρo ρ ρt) :
    OpenS δ σ Tab (cbQ δ σ fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u) σ.length ds bs [] ls e ρt := by
  let en : LEnt := ⟨l', x', T', .imm v, cr'⟩
  let Qo : List SRec → Val → WProp := fun ls u => ownerI l' v T' δ ls ⋆ Qa ls u
  have hQo : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qo ls₁ u ρ → Qo ls₂ u ρ :=
    fun _ _ _ _ he ⟨a, b, hc, ha, hb⟩ =>
      ⟨a, b, hc, ownerI_local (he.left hc) ha, hQa _ _ _ _ (he.right hc) hb⟩
  let Mot : XT := fun k ds' αi αo ls₁ e ρ => k = σ.length + 1 → αo = [] → ∀ d ds b bs,
    ds' = d :: ds → αi = b :: bs → (∀ a ∈ bs.getLast?, a ≤ β') →
      ImmBody δ σ Tab l' v T' Qo ds b bs ls₁ e ρ
  have hind : ∀ ls₁ e ρ, OpenS δ (en :: σ) Tab (cbQ δ (en :: σ) Qa) (σ.length + 1) (d :: ds)
      (b :: bs) [] ls₁ e ρ → Mot (σ.length + 1) (d :: ds) (b :: bs) [] ls₁ e ρ := by
    intro ls₁ e ρ hO
    refine hO Mot ?_
    rintro k ds' αi αo ls₁ e ρ hF rfl rfl d ds b bs rfl rfl hβ
    have hrun : ∀ αs α, List.Forall₂ (· < ·) αs bs → List.IsChain (· < ·) (α :: αs) → α < b →
        boxTop (α :: αs) (vwS δ [] (en :: σ) (d :: ds) (α :: αs) ls₁ ─⋆
          bodyS δ (en :: σ) Tab (cbQ δ (en :: σ) Qa) Mot (α :: αs) ls₁ e) ρ := by
      intro αs α hlt hch hαb
      have := hF (α :: αs) (.cons hαb hlt) (by rw [List.append_nil]; exact hch)
      rwa [take_cons_length, List.append_nil] at this
    refine ⟨fun αs α hlt hch hαb => (hrun αs α hlt hch hαb).2, ?_⟩
    intro αs α hlt hch hαb ρv hv ρm hm R W hR hcW
    have hrα := hrun αs α hlt hch hαb
    have hρα : ρ.InStratum α := stratS_head hch hrα.2
    have hvα : ρv.InStratum α := vwS_inStratum hv α (head_lt_mem hch)
    have hlen : αs.length = σ.length := (vwS_length hv).2
    have hch' : List.IsChain (· < ·) αs := hch.tail
    have hβ' : ∀ a ∈ αs.getLast?, a ≤ β' := fun a ha => by
      obtain ⟨y, hy, hle⟩ := getLast?_le (hlt.imp fun _ _ => le_of_lt) a ha
      exact le_trans hle (hβ y hy)
    obtain ⟨a, g, hag, ha, hg⟩ := viewI_split (e := en) rfl (d := d) hm
    obtain ⟨Ra, hRa, hRag⟩ := compS_reassoc' hag hcW
    obtain ⟨va, hva, hρva⟩ := compS_reassoc hR hRa
    have hvin : vwS δ [] (en :: σ) (d :: ds) (α :: αs) ls₁ va :=
      vwS_cons_other hl' ha hv (ResU.CompS.comm hva)
    have hbody := hrα.1 va Ra hvin hρva
    have hta : TabAt l' α a := by
      cases d with
      | false => obtain ⟨rfl, -⟩ := ha; exact tabAt_empty l' α
      | true => exact tabAt_viewI ha
    have htab : TabAt l' α Ra := (tabAt_comp hρva).mpr ⟨tabAt_of_inStratum hρα,
      (tabAt_comp hva).mpr ⟨tabAt_of_inStratum hvα, hta⟩⟩
    refine wpG_absorb (wpG_garbage (wpG_mono (fun ls'' t τ' hq => ?_)
      (wpG_tabAt l' α ls₁ e _ htab hbody))) hg hRag
    obtain ⟨ht, hq⟩ := hq
    rcases hq with ⟨u, rfl, hqv⟩ | hs
    · -- a return: the owner handed back joins the answer
      refine ⟨τ', PMap.empty, ResU.comp_empty_right τ', noOwn_empty, ?_⟩
      refine ⟨fun ρa ρb ha' hcab ρc ρd hvc hccd => ?_, hqv.2⟩
      obtain ⟨o, r, hcor, hor, hr⟩ := hqv.1 ρa ρb ha' hcab ρc ρd hvc hccd
      exact Or.inl ⟨u, rfl, ⟨o, r, hcor, hor, hr.1⟩, fun a' ha'' => (outlives_comp hcor a').mpr
        ⟨fun k ψ e' => by
          obtain ⟨o₁, o₂, hco, ho₁, ho₂⟩ := hor
          exact ((outlives_comp hco a').mpr ⟨by rw [ho₁]; exact ResU.inStratum_single_own a' l' v,
            (hP' ls'' v o₂ ho₂).mono (hβ' a' ha'')⟩) k ψ e',
          stratS_tail hr.2 a' ha''⟩⟩
    · rcases stopS_full hx (by simp [hlen]) hs with ⟨ds', hdl, ρ₁, ρ₂, hc₁₂, hd, hgs⟩ |
          ⟨ρ₁, ρ₂, hc₁₂, hno, hgs⟩
      · obtain ⟨d', ds₀, rfl⟩ : ∃ d' ds₀, ds' = d' :: ds₀ := by
          cases ds' with
          | nil => simp at hdl
          | cons d' ds₀ => exact ⟨d', ds₀, rfl⟩
        obtain ⟨g₁, q₁, hcq, hg₁, hq₁⟩ := dropS_cons_other (e := en) hl' hd
        obtain ⟨x₁, hcx, hgx⟩ := compS_reassoc hcq hc₁₂
        have hqα : q₁.InStratum α := by
          obtain ⟨y, -, hy⟩ := compS_lcomm hcx hgx
          exact tabAt_off ht ⟨_, hy⟩ fun k ψ e' hk =>
            hl' (hk ▸ dropS_places hq₁ k ψ e')
        refine ⟨x₁, g₁, ResU.CompS.comm hgx, dropE_noOwn hg₁,
          fun ρa ρb ha' hcab ρc ρd hvc hccd => ?_, (outlives_comp hcx α).mpr ⟨hqα, hgs.2⟩⟩
        obtain ⟨y, hy, hqy⟩ := compS_reassoc hcx hcab
        obtain ⟨z, hz, hqz⟩ := compS_reassoc hqy hccd
        obtain ⟨o, r, hcor, hor, hr⟩ := hgs.1 ρa y ha' hy ρc z hvc hz
        refine Or.inr ⟨ds₀, q₁, z, hqz, hq₁, ?_, fun a' ha'' => (outlives_comp hcor a').mpr
          ⟨fun k ψ e' => by
            obtain ⟨o₁, o₂, hco, ho₁, ho₂⟩ := hor
            exact ((outlives_comp hco a').mpr ⟨by rw [ho₁]; exact ResU.inStratum_single_own a' l' v,
              (hP' ls'' v o₂ ho₂).mono (hβ' a' ha'')⟩) k ψ e',
            stratS_tail hr.2 a' ha''⟩⟩
        refine opTable_frame hLR .hole (fun _ => rfl) (ownerI l' v T' δ)
          (fun _ _ _ he h => ownerI_local he h) (fun ls₂ e₂ ρ₁' ρz ρ' hall hoz hc' => ?_)
          (opTable_shift hL hLR hr.1) hor (ResU.CompS.comm hcor)
        exact fold_imm hx.tail hadm hP' (fun αs' => q64_ext hL hQo) hβ'
          (fun ls₃ he₃ => hall ls₃ he₃ rfl rfl d' ds₀ α αs rfl rfl hβ') hoz
          (ResU.CompS.comm hc')
      · refine ⟨ρ₁, ρ₂, hc₁₂, hno, fun ρa ρb ha' hcab ρc ρd hvc hccd => ?_, hgs.2⟩
        obtain ⟨_, _, _, _, hb⟩ := hgs.1 ρa ρb ha' hcab ρc ρd hvc hccd
        exact hb.1.elim
  exact fold_imm hx.tail hadm hP' (fun αs => q64_ext hL hQo) hβ
    (fun ls₁ he => hind ls₁ e ρ (h ls₁ he) rfl rfl d ds b bs rfl rfl hβ) ho hc

end imm

/-! ### Folding a stack back to the empty stack, and every hypothesis discharged -/

section fold
variable {δ : LSub} {Tab : OpTab}

/-- **At the empty stack the piece is `ewpTS`** (`bodyS_nil_iff`). -/
theorem openS_nil_ewp {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenS δ [] Tab (cbQ δ [] Q) 0 [] [] [] ls e ρ) : ewpTS ls e (opTable Tab) Q ρ :=
  (bodyS_nil_iff (fun _ _ _ => Iff.rfl)).mp (openFS_nil.mp (openS_unfold h))

/-- **6.65 at a resuming table, from the step**: `stack_step_other` at `σ = []`. -/
theorem stack_spans_mut (hLR : LinResume Tab) {l : BoCa.Loc} {x : LifeVar} {T : VTy}
    {cr : UInt32 → Bool} (hx : AllCross [⟨l, x, T, .mut, cr⟩] Tab) {β : Life}
    (hP : ∀ ls w ρ, vC true T ls δ w ρ → ρ.InStratum β) {Qa : List SRec → Val → WProp}
    {d : Bool} {b : Life} (ls : List SRec) (e : Expr) :
    Entails (owner l T δ ls ⋆ OpenS δ [⟨l, x, T, .mut, cr⟩] Tab (cbQ δ [⟨l, x, T, .mut, cr⟩] Qa)
      1 [d] [b] [] ls e)
      (ewpTS ls e (opTable Tab) fun ls v => owner l T δ ls ⋆ Qa ls v) := by
  rintro ρ ⟨ρo, ρr, hc, ho, hr⟩
  exact openS_nil_ewp (stack_step_other hLR (σ := []) hx (by simp) hP
    (by simp) ho hr hc)

/-- **6.64 at a resuming table, from the step**: `stack_step_imm` at `σ = []`. -/
theorem stack_spans_imm (hLR : LinResume Tab) (hL : Tab.Local) {l : BoCa.Loc} {x : LifeVar}
    {T : VTy} {v : Val} {cr : UInt32 → Bool} (hx : AllCross [⟨l, x, T, .imm v, cr⟩] Tab)
    (hadm : AdmWf T δ) {β : Life} (hP : ∀ ls w ρ, vC true T ls δ w ρ → ρ.InStratum β)
    {Qa : List SRec → Val → WProp} (hQa : ∀ ls₁ ls₂ u ρ, Ext ls₁ ls₂ ρ → Qa ls₁ u ρ → Qa ls₂ u ρ)
    {d : Bool} {b : Life} {ls : List SRec} {e : Expr} {ρo ρ ρt : WRes}
    (ho : ownerI l v T δ ls ρo)
    (h : ∀ ls₁, Ext ls ls₁ ρ → OpenS δ [⟨l, x, T, .imm v, cr⟩] Tab
      (cbQ δ [⟨l, x, T, .imm v, cr⟩] Qa) 1 [d] [b] [] ls₁ e ρ) (hc : ResU.CompS ρo ρ ρt) :
    ewpTS ls e (opTable Tab) (fun ls u => ownerI l v T δ ls ⋆ Qa ls u) ρt :=
  openS_nil_ewp (stack_step_imm hLR hL (σ := []) hx (by simp) hadm hP hQa (by simp) ho h hc)

/-- D16.1's piece at an answer, at every stack: the views are left behind. -/
theorem openS_val_any {σ : LStack} {Qa : List SRec → Val → WProp} {u : Val}
    (hu : ∀ ls, Qa ls u PMap.empty) (ds : List Bool) (αi : List Life) (ls : List SRec) :
    OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls (.val u) PMap.empty := by
  refine openS_fold fun αi' _ hch => ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
  rw [List.append_nil] at hch ⊢
  rw [eq_of_compS_empty_left hc]
  rw [List.take_length] at hw
  exact wpG_garbage (wpG_here ls _ _ w ⟨PMap.empty, w, compS_empty_left w, vwS_noOwn hw,
    Or.inl ⟨u, rfl, ghostS_of_boxTop (vwS_length hw).2 hch
      ⟨hu ls, fun a _ => ResU.inStratum_empty a⟩⟩⟩)

/-- D16.1's piece at a yield crossing every entry, at every stack: every view is dropped (every
lend ghost-ended), and the continuation is the piece again at the re-lend. -/
theorem openS_yield_any {σ : LStack} (hx : AllCross σ Tab) {n i : UInt32} {en : OpEnt}
    (hTn : Tab n i = some en) (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {Qa : List SRec → Val → WProp} {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    (h : ∀ ls ds αi, OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls rest PMap.empty)
    (ds : List Bool) (αi : List Life) (ls : List SRec) :
    OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds αi [] ls (yieldSeq n i y rest) PMap.empty := by
  refine openS_fold fun αi' _ hch => ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
  rw [List.append_nil] at hch ⊢
  rw [eq_of_compS_empty_left hc]
  rw [List.take_length] at hw
  have hlen := (vwS_length hw).2
  refine wpG_here ls _ _ w (Or.inr (stopS_of_full hx hlen (dropS_of_vwS hw)
    (ghostS_of_boxTop hlen hch ⟨?_, fun a _ => ResU.inStratum_empty a⟩)
    (ResU.comp_empty_right w)))
  refine Or.inl ⟨.seq .hole rest, n, i, y, en, pure_sep_mk ⟨rfl, rfl, hTn, ha⟩
    ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, hy ls, ?_⟩⟩
  refine ⟨fun _ => rfl, fun ls' _ => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  rw [eq_of_compS_empty_left hcτ]
  exact openS_step (fun μ => Step1N.head (Head.seq μ rest) rfl) (h ls' ds αi')

/-- The owners of a stack's places: `⊛_{e ∈ σ} ∃w. ℓₑ ↦ w ⋆ 𝒱⟦Tₑ⟧(w)`. -/
def ownersS (δ : LSub) : LStack → List SRec → WProp
  | [], _ => emp
  | e :: σ, ls => owner e.l e.T δ ls ⋆ ownersS δ σ ls

/-- An answer with the owners of a stack's places beside it, innermost handed back first. -/
def withOwners (δ : LSub) : LStack → (List SRec → Val → WProp) → List SRec → Val → WProp
  | [], Q => Q
  | e :: σ, Q => withOwners δ σ fun ls v => owner e.l e.T δ ls ⋆ Q ls v

/-- **A whole stack folds back to the empty stack, by induction on the stack.** A stack of `mut`
lends of distinct places, every stop crossing every entry: D16.1's piece at `σ` beside the owners
of `σ`'s places gives the piece's `ewpTS`. The step from `σ·new` to `σ` is `stack_step_other`;
the base is `bodyS_nil_iff`. -/
theorem fold_other (hLR : LinResume Tab) {β : Life} : ∀ (σ : LStack), (∀ e ∈ σ, e.k = .mut) →
    (σ.map LEnt.l).Nodup → AllCross σ Tab →
    (∀ e ∈ σ, ∀ ls w ρ, vC true e.T ls δ w ρ → ρ.InStratum β) →
    ∀ (Qa : List SRec → Val → WProp) (ds : List Bool) (bs : List Life),
      ds.length = σ.length → bs.length = σ.length → (∀ a ∈ bs, a ≤ β) →
      ∀ (ls : List SRec) (e : Expr) (ρo ρ ρt : WRes), ownersS δ σ ls ρo →
        OpenS δ σ Tab (cbQ δ σ Qa) σ.length ds bs [] ls e ρ → ResU.CompS ρo ρ ρt →
        ewpTS ls e (opTable Tab) (withOwners δ σ Qa) ρt
  | [], _, _, _, _, Qa, ds, bs, hd, hb, _, ls, e, ρo, ρ, ρt, ho, h, hc => by
      obtain rfl : ds = [] := List.eq_nil_of_length_eq_zero hd
      obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero hb
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hc]
      exact openS_nil_ewp h
  | ⟨l, x, T, k, cr⟩ :: σ, hk, hnd, hx, hP, Qa, d :: ds, b :: bs, hd, hb, hβ, ls, e,
      ρo, ρ, ρt, ⟨o, os, hco, ho, hos⟩, h, hc => by
      obtain rfl : k = .mut := hk _ (List.mem_cons_self ..)
      obtain ⟨hl, hnd'⟩ := List.nodup_cons.mp hnd
      obtain ⟨y, hy, hcy⟩ := compS_exch hco hc
      have hstep := stack_step_other hLR (σ := σ) hx hl (hP _ (List.mem_cons_self ..))
        (fun a ha => hβ a (List.mem_cons_of_mem _ (List.mem_of_getLast? ha))) ho h hy
      exact fold_other hLR σ (fun e he => hk e (List.mem_cons_of_mem _ he)) hnd' hx.tail
        (fun e he => hP e (List.mem_cons_of_mem _ he)) _ ds bs (by simpa using hd)
        (by simpa using hb) (fun a ha => hβ a (List.mem_cons_of_mem _ ha)) ls e os y ρt
        hos hstep (ResU.CompS.comm hcy)
  | _ :: _, _, _, _, _, _, [], _, hd, _, _, _, _, _, _, _, _, _, _ => by simp at hd
  | _ :: _, _, _, _, _, _, _ :: _, [], _, hb, _, _, _, _, _, _, _, _, _ => by simp at hb

/-- **The `withbor` (3) row at depth 2, from the uniform steps**: `stack_step_reborrow` at
`σ₀ = []`, then `stack_spans_mut`. The same conclusion as `withbor_reborrow_spans`. -/
theorem stack2_reborrow_spans (hLR : LinResume Tab) {l : BoCa.Loc} {T : VTy} {β : Life}
    (hP : ∀ ls w ρ, vC true T ls δ w ρ → ρ.InStratum β) {xi xo : LifeVar}
    {cri cro : UInt32 → Bool}
    (hx : AllCross [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] Tab)
    {Qa : List SRec → Val → WProp} {d₂ d₁ : Bool} {a₂ a₁ : Life} (ls : List SRec) (e : Expr) :
    Entails (owner l T δ ls ⋆ OpenS δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] Tab
      (cbQ δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] Qa) 2 [d₂, d₁] [a₂, a₁] [] ls e)
      (ewpTS ls e (opTable Tab) fun ls v => owner l T δ ls ⋆ Qa ls v) := by
  rintro ρ ⟨ρo, ρr, hc, ho, hr⟩
  exact stack_spans_mut hLR hx.tail hP ls e ρ
    ⟨ρo, ρr, hc, ho, stack_step_reborrow (σ₀ := []) hx hP hr⟩

end fold

section inst
open GhostEnd.Instance

theorem yield_linResume (δ : LSub) : LinResume (Row.tab [yieldOp] δ) := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨hm, -, -⟩ := Row.find_mem hf
  simp only [List.mem_singleton] at hm
  subst hm
  exact ⟨rfl, rfl⟩

theorem yield_local (δ : LSub) : (Row.tab [yieldOp] δ).Local := by
  intro n i en hT ls ls' w ρ he
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  exact ⟨fun h => vC_local true _ he h, fun h => vC_local true _ he h⟩

theorem yield_PB (δ : LSub) : ∀ ls w ρ, (yieldOp.ent δ).PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty := by
  intro ls w σ h
  simp only [OpSig.ent, yieldOp] at h
  exact ⟨h.2, h.1⟩

theorem unit_stratum (δ : LSub) : ∀ ls w ρ, vC true VTy.unit ls δ w ρ → ρ.InStratum ⊤ :=
  fun _ _ σ h => by rw [h.1]; exact ResU.inStratum_empty _

/-- A piece that yields once with every lend of the stack open, then returns `()`, at the row
`{yield : I32 ↠ 1}`, every entry crossed by `yield`. -/
theorem yield_piece (δ : LSub) {σ : LStack} (hx : AllCross σ (Row.tab [yieldOp] δ))
    (ds : List Bool) (αi : List Life) (ls : List SRec) :
    OpenS δ σ (Row.tab [yieldOp] δ) (cbQ δ σ fun _ v => ⌜v = Val.unit⌝) σ.length ds αi [] ls
      (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.val .unit)) PMap.empty :=
  openS_yield_any hx (en := yieldOp.ent δ) (by simp [Row.tab, Row.find, yieldOp]) rfl rfl
    (yield_PB δ) (fun ls => ⟨rfl, 1, rfl⟩)
    (fun ls ds αi => openS_val_any (fun _ => ⟨rfl, rfl⟩) ds αi ls) ds αi ls

/-- **Three lends spanning a stop, every hypothesis discharged.** A callback holding a reborrow of
a reborrow of the outer view of `ℓ` yields once with all three lends open, then returns `()`. The
stack `[ℓ@α₃, ℓ@α₂, ℓ@α₁]` folds back by the same two lemmas used at depth 2:
`stack_step_reborrow` at `σ₀ = [outer]`, again at `σ₀ = []`, then `stack_step_other` at `σ = []`. -/
theorem stack3_reborrow_yield (δ : LSub) (l : BoCa.Loc) (ls : List SRec) :
    Entails (owner l .unit δ ls)
      (ewpTS ls (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.val .unit))
        (opTable (Row.tab [yieldOp] δ)) (fun ls v => owner l .unit δ ls ⋆ ⌜v = Val.unit⌝)) := by
  let tt : UInt32 → Bool := fun _ => true
  let e₀ : LEnt := ⟨l, 0, .unit, .mut, tt⟩
  let e₁ : LEnt := ⟨l, 1, .unit, .mut, tt⟩
  let e₂ : LEnt := ⟨l, 2, .unit, .mut, tt⟩
  have hall : ∀ σ : LStack, (∀ e ∈ σ, e.cross = tt) → AllCross σ (Row.tab [yieldOp] δ) :=
    fun σ h n i en _ e he => by rw [h e he]
  have h₃ := yield_piece δ (σ := [e₂, e₁, e₀]) (hall _ (by simp [e₀, e₁, e₂]))
    [true, false, false] [OrderDual.toDual 3, OrderDual.toDual 2, OrderDual.toDual 1] ls
  have h₂ := stack_step_reborrow (σ₀ := [e₀]) (hall _ (by simp [e₀]))
    (unit_stratum δ) h₃
  have h₁ := stack_step_reborrow (σ₀ := []) (hall _ (by simp)) (unit_stratum δ) h₂
  intro ρ ho
  exact openS_nil_ewp (stack_step_other (yield_linResume δ) (σ := []) (hall _ (by simp))
    (by simp) (unit_stratum δ) (by simp) ho h₁
    (ResU.comp_empty_right ρ))

/-- **An `imm` entry inside a `mut` lend spanning a stop, every hypothesis discharged.** A
callback holding the outer view of `ℓ` and an `imm` view of `ℓ′` yields once with both lends open,
then returns `()`. The stack `[ℓ′@α₂ imm, ℓ@α₁]` folds back by `stack_step_imm` at `σ = [outer]`,
then `stack_step_other` at `σ = []`. -/
theorem stack2_imm_yield (δ : LSub) {l l' : BoCa.Loc} (hne : l' ≠ l) (u : Val) (ls : List SRec) :
    Entails (owner l .unit δ ls ⋆ ownerI l' u .unit δ ls)
      (ewpTS ls (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.val .unit))
        (opTable (Row.tab [yieldOp] δ))
        (fun ls v => owner l .unit δ ls ⋆ (ownerI l' u .unit δ ls ⋆ ⌜v = Val.unit⌝))) := by
  let tt : UInt32 → Bool := fun _ => true
  let e₀ : LEnt := ⟨l, 0, .unit, .mut, tt⟩
  let eᵢ : LEnt := ⟨l', 1, .unit, .imm u, tt⟩
  have hall : ∀ σ : LStack, (∀ e ∈ σ, e.cross = tt) → AllCross σ (Row.tab [yieldOp] δ) :=
    fun σ h n i en _ e he => by rw [h e he]
  rintro ρ ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
  have hI := stack_step_imm (yield_linResume δ) (yield_local δ) (σ := [e₀])
    (hall _ (by simp [e₀])) (by simp [e₀, hne]) (fun _ h => absurd h (by simp [VFree]))
    (unit_stratum δ) (Qa := fun _ v => ⌜v = Val.unit⌝) (fun _ _ _ _ _ h => h)
    (d := true) (b := OrderDual.toDual 2) (bs := [OrderDual.toDual 1]) (by simp) h₂
    (fun ls₁ _ => yield_piece δ (σ := [eᵢ, e₀]) (hall _ (by simp [e₀, eᵢ])) [true, true]
      [OrderDual.toDual 2, OrderDual.toDual 1] ls₁) (ResU.comp_empty_right ρ₂)
  exact openS_nil_ewp (stack_step_other (yield_linResume δ) (σ := []) (hall _ (by simp))
    (by simp) (unit_stratum δ) (by simp) h₁ hI hc)

end inst

end GhostEnd
