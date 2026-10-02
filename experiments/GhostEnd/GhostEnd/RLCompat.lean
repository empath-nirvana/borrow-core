import GhostEnd.Bridge

/-!
# GhostEnd — the compatibility lemmas at `vRL`/`cRL` (#266)

`fundamentalC` has one compatibility lemma per `CDerives` rule. Read at route (b)'s relation,
each is **routine**, the kernel's proof carrying over with a mechanical change, or **non-routine**,
the `U` clause's re-lend entering it. This file proves the step every non-routine lemma reduces
to, and shows where the single-lend relation stops. The full table is in the README, step 3f.

## Re-lendability

`Relendable l T δ P α`: the resource splits into the view it dropped at `α` and a part in `Res_α`
that, at every extension of the list and every later lend `α′ ⊑ α`, handed the view if it dropped
the cell, is in `P α′`. `vRL`'s `U` clause is `Relendable` of `cRL C` at the forced closure
(`vRL_thunk_iff`). It is monotone (`relendable_mono`), Kripke (`relendable_local`) and closed
under `⋆` (`relendable_sep`). These are re-lendable:

* a `U` slot, by construction (`relendable_thunk`). So `URelend`, the one step routes (a) and (c)
  need at the kernel's relation (`frameThawsD_thunk_iff`), holds at `vRL` at every computation
  type with no hypothesis (`uRelendRL`);
* the borrow's own view (`relendable_view`), a slot free of `'x` in `Res_α` (`relendable_free`),
  and a pair of re-lendable components (`relendable_tensor`);
* a context of re-lendable slots (`gRL`, `relendable_gRL`).

## The non-routine lemmas, reduced

* `[force]`: `force_RL`, the clause read at `α′ = α`.
* `thunk`: `thunkF_RL`, `thunkF_RL_ctx`. A closure over a re-lendable context is in `vRL`, its
  body read at every `α′ ⊑ α` from the thawed context.
* `[let]`, `bind`, call-by-value application, at a linear resuming table: `bind_RL`. The frame's
  frozen form is read off `Relendable`, and `openD_bind` and `bodyAtD_bind` do the rest.
* `[handle]`: a continuation captured at an inner stop stays re-lendable under a re-lendable frame
  (`relendable_cont_frame`).
* a constant, and `bounded_fix`'s self-reference: a closed `U` value (`vRL_thunk_closed`).

## Where the single-lend relation stops

`relendable_off_cell`: a re-lendable resource holds no cell off `ℓ` at or below `α`. Inside an
inner borrow's callback, `y ⊏ ⊓Δ` with `'x` in `Δ`, the context holds the inner view
`n : Mut 'y 1`, a cell at `αy ⊏ α`. `thunkF_RL_fails_below` builds that configuration:

* `thunk (return n)` is typed there, and the substitution models the context;
* the context is in `gRL`, and `thunkF_RL`'s body premise holds;
* the context is not re-lendable, and no closure value over that resource is in `vRL`'s `U`
  clause;
* `TabAt` fails, so a fundamental lemma that assumes the table says nothing about the callback.

`thunkF_RL_fails_below_at` discharges every hypothesis at numerals. The resource is an inhabitant
of `ptoMutS k αy`, which 6.65's premise `fresh (λα. ℓ ↦ M_α P̂ ─⋆ …)` quantifies over, at
the lifetime 6.65's entry chooses below the bound `withbor`'s type gives (`innerCtx`).

## The table as a guard: `vRLg`

`vRLg` asks the stratum and the re-lend of a `U` value only when its resource is consistent with
the table. A frame at a stop is consistent with it (`wpG_tabAt`), so a stop is read exactly as at
`vRL` (`relendableG_thunk`, `uRelendRLg`). A closure over a value below the lend owes the reading
at `α` alone (`forceG`, `thunkF_RLg`). The configuration above is inside `vRLg`
(`thunkF_RLg_below`). What `vRLg` does not cover is a lend opened inside the borrower that itself
spans a stop: a value then holds a cell of each lend open at the stop, and has to be re-lendable at
each. That is `vRL` indexed by the stack of open lends. I have not derived it and have not verified
that any obstruction is real.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Re-lendable at `α`.** The resource splits into the view it dropped at `α` and a part in
`Res_α` that, at every extension of the list and every later lend `α′ ⊑ α`, handed the view if
it dropped the cell, is in `P α′`. -/
def Relendable (l : BoCa.Loc) (T : VTy) (δ : LSub) (P : Life → List SRec → WProp) (α : Life)
    (ls : List SRec) : WProp := fun ρ =>
  ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ vwD l T δ d α ls ρn ∧ ρz.InStratum α ∧
    ∀ ls', Ext ls ls' ρz → ∀ α', α' ≤ α → (vwD l T δ d α' ls' ─⋆ P α' ls') ρz

/-- A view is Kripke along `Ext`, as `vC_local`'s `Mut` case. -/
theorem ptoMutS_local {l : BoCa.Loc} {α : Life} {ls ls' : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (hk : Ext ls ls' ρ) (h : ptoMutS l α ls P ρ) :
    ptoMutS l α ls' P ρ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, hls₀, hunif⟩ := h
  have hmut : CellIn ρ b :=
    ⟨l, _, by rw [hρ]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
  refine ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, fun x => ?_, hunif⟩
  rw [hls₀ x]
  exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 b hmut x hb).mp hx, hb⟩,
    fun ⟨hx, hb⟩ => ⟨(hk.2 b hmut x hb).mpr hx, hb⟩⟩

section
variable {l : BoCa.Loc} {T : VTy} {δ : LSub}

/-- `Relendable` is monotone in what the thawed part satisfies. -/
theorem relendable_mono {P P' : Life → List SRec → WProp}
    (hP : ∀ α' ls', Entails (P α' ls') (P' α' ls')) {α : Life} {ls : List SRec} :
    Entails (Relendable l T δ P α ls) (Relendable l T δ P' α ls) := by
  rintro ρ ⟨d, ρz, ρn, hc, hn, hz, hth⟩
  exact ⟨d, ρz, ρn, hc, hn, hz, fun ls' he α' hle =>
    wand_mono_right (hP α' ls') ρz (hth ls' he α' hle)⟩

/-- `Relendable` is Kripke along `Ext`. -/
theorem relendable_local {P : Life → List SRec → WProp} {α : Life} {ls ls' : List SRec}
    {ρ : WRes} (he : Ext ls ls' ρ) (h : Relendable l T δ P α ls ρ) :
    Relendable l T δ P α ls' ρ := by
  obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ := h
  refine ⟨d, ρz, ρn, hc, ?_, hz, fun ls'' he' => hth ls'' ((he.left hc).trans he')⟩
  cases d with
  | false => exact hn
  | true => exact ptoMutS_local (he.right hc) hn

/-- **Re-lendability is closed under `⋆`.** At most one part dropped the cell (`dropC_disj`); at
a thaw the view goes to that part. -/
theorem relendable_sep {P Q : Life → List SRec → WProp} {α : Life} {ls : List SRec} :
    Entails (Relendable l T δ P α ls ⋆ Relendable l T δ Q α ls)
      (Relendable l T δ (fun α' ls' => P α' ls' ⋆ Q α' ls') α ls) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, ⟨d₁, ρz₁, ρn₁, hc₁, hn₁, hz₁, hth₁⟩, ⟨d₂, ρz₂, ρn₂, hc₂, hn₂, hz₂, hth₂⟩⟩
  have hnd : ¬ (d₁ = true ∧ d₂ = true) := by
    rintro ⟨rfl, rfl⟩
    exact dropC_disj (dropC_of_vwD hn₁) (dropC_of_vwD hn₂) (ResU.CompS.comm hc₁)
      (ResU.CompS.comm hc₂) hc
  obtain ⟨ρz, ρn, hcz, hcn, hcρ⟩ := compS_four hc₁ hc₂ hc
  refine ⟨d₁ || d₂, ρz, ρn, hcρ, vwD_join hnd hn₁ hn₂ hcn,
    (outlives_comp hcz α).mpr ⟨hz₁, hz₂⟩, fun ls' he α' hle ρv σ hv hcv => ?_⟩
  cases d₁ with
  | true =>
      obtain rfl : d₂ = false := by cases d₂ <;> simp_all
      obtain ⟨y, hy, hcy⟩ := compS_exch hcz hcv
      exact ⟨y, ρz₂, hcy, hth₁ ls' (he.left hcz) α' hle ρv y hv hy,
        hth₂ ls' (he.right hcz) α' hle PMap.empty ρz₂ ⟨rfl, trivial⟩
          (ResU.comp_empty_right ρz₂)⟩
  | false =>
      obtain ⟨y, hy, hcy⟩ := compS_reassoc hcz hcv
      exact ⟨ρz₁, y, hcy, hth₁ ls' (he.left hcz) α' hle PMap.empty ρz₁ ⟨rfl, trivial⟩
          (ResU.comp_empty_right ρz₁),
        hth₂ ls' (he.right hcz) α' hle ρv y (by simpa using hv) hy⟩

end

section
variable {S : Row} {x : LifeVar} {T : VTy} {δ : LSub} {l : BoCa.Loc}

/-- `vRL`'s `U` clause is `Relendable` of `cRL C` at the forced closure. -/
theorem vRL_thunk_iff {C : CTy} {α : Life} {ls : List SRec} {f : Val} {ρ : WRes} :
    vRL S x T δ l (.thunk C) α ls f ρ ↔
      Relendable l T δ (fun α' ls' => cRL S x T δ l C α' ls' (forceE C (.val f))) α ls ρ :=
  Iff.rfl

/-- **`[force]`**: the `U` clause at `α′ = α`, the dropped view handed back. -/
theorem force_RL {C : CTy} {α : Life} {ls : List SRec} {f : Val} {ρ : WRes}
    (h : vRL S x T δ l (.thunk C) α ls f ρ) :
    cRL S x T δ l C α ls (forceE C (.val f)) ρ := by
  obtain ⟨d, ρz, ρn, hc, hn, -, hth⟩ := h
  exact hth ls (Ext.refl ls ρz) α le_rfl ρn ρ hn hc

/-- **A `U` slot thaws by construction**: frozen at `α` and thawed at `α′ ⊑ α`, it is a `vRL` value
at `α′`. -/
theorem relendable_thunk {C : CTy} {α : Life} {ls : List SRec} {f : Val} {ρ : WRes}
    (h : vRL S x T δ l (.thunk C) α ls f ρ) :
    Relendable l T δ (fun α' ls' => vRL S x T δ l (.thunk C) α' ls' f) α ls ρ := by
  obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ := h
  refine ⟨d, ρz, ρn, hc, hn, hz, fun ls' he α' hle ρv σ hv hcv => ?_⟩
  exact ⟨d, ρz, ρv, hcv, hv, hz.mono hle,
    fun ls'' he' α'' hle' => hth ls'' (he.trans he') α'' (le_trans hle' hle)⟩

/-- **`URelend` at `vRL`**: `Bridge.lean`'s `URelend`, the one step routes (a) and (c) need, read
at route (b)'s relation. -/
def URelendRL (S : Row) (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) (C : CTy) : Prop :=
  ∀ (f : Val) (α : Life) (ls : List SRec) (ρ : WRes),
    TabAt l α ρ → vRL S x T δ l (.thunk C) α ls f ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ dropC l d ρn ∧ ρz.InStratum α ∧
        ∀ ls', Ext ls ls' ρz → ∀ α', α' ⊏ α → ∀ ρv ρ', vwD l T δ d α' ls' ρv →
          ResU.CompS ρv ρz ρ' → TabAt l α' ρ' ∧ vRL S x T δ l (.thunk C) α' ls' f ρ'

/-- **`URelend` holds at `vRL`, at every computation type, with no hypothesis.** -/
theorem uRelendRL (C : CTy) : URelendRL S x T δ l C := by
  intro f α ls ρ _ h
  obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ := relendable_thunk h
  refine ⟨d, ρz, ρn, hc, dropC_of_vwD hn, hz, fun ls' he α' hα' ρv ρ' hv hc' => ⟨?_, ?_⟩⟩
  · refine (tabAt_comp hc').mpr ⟨?_, tabAt_of_inStratum (hz.mono (le_of_lt hα'))⟩
    cases d with
    | false => obtain ⟨rfl, -⟩ := hv; exact tabAt_empty l α'
    | true => exact tabAt_view hv
  · exact hth ls' he α' (le_of_lt hα') ρv ρ' hv (ResU.CompS.comm hc')

/-- **A closed `U` value**: a constant, or `bounded_fix`'s self-reference. It drops nothing. -/
theorem vRL_thunk_closed {C : CTy} {α : Life} {ls : List SRec} {f : Val}
    (h : ∀ ls', ∀ α', α' ≤ α → cRL S x T δ l C α' ls' (forceE C (.val f)) PMap.empty) :
    vRL S x T δ l (.thunk C) α ls f PMap.empty := by
  refine ⟨false, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩,
    ResU.inStratum_empty α, fun ls' _ α' hle ρv σ hv hc => ?_⟩
  obtain ⟨rfl, -⟩ := hv
  rw [eq_of_compS_empty_left hc]
  exact h ls' α' hle

/-- **`thunk M : U (F A)`**: the closure over a re-lendable context is in `vRL`. -/
theorem thunkF_RL {G : Life → List SRec → WProp} {M : Expr} {A : VTy} {γ : List Val}
    {α : Life} {ls : List SRec} {ρ : WRes} (hG : Relendable l T δ G α ls ρ)
    (hM : ∀ α', α' ≤ α → ∀ ls' σ, G α' ls' σ →
      cRL S x T δ l (.ret A) α' ls' (substAll (Val.unit :: γ) M) σ) :
    vRL S x T δ l (.thunk (.ret A)) α ls (Val.lam (Expr.psub 1 γ M)) ρ := by
  obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ := hG
  refine ⟨d, ρz, ρn, hc, hn, hz, fun ls' he α' hle ρv σ hv hcv => ?_⟩
  refine wpG_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ σ ?_
  rw [← substAll_cons_l]
  exact hM α' hle ls' σ (hth ls' he α' hle ρv σ hv hcv)

/-- **The borrow's own slot**: the view at `ℓ` is dropped, and re-lent at `α′` (`mutView`). -/
theorem relendable_view (hT : ¬ VFree x T) {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vC true (.mut (.var x) T) ls (δ.extend x α) (.loc l) ρ) :
    Relendable l T δ (fun α' ls' => vC true (.mut (.var x) T) ls' (δ.extend x α') (.loc l))
      α ls ρ := by
  obtain ⟨α₀, hα₀, l', hs⟩ := h
  rw [interp_ext_self] at hα₀
  cases Option.some.inj hα₀
  obtain ⟨hv, hm⟩ := pure_sep_iff.mp hs
  obtain rfl : l = l' := by injection hv with h; injection h
  have e : (fun ls₀ => vC true T ls₀ (δ.extend x α)) = (fun ls₀ => vC true T ls₀ δ) :=
    funext fun ls₀ => vC_extend_of_not_free hT true ls₀ δ α
  have hm' : viewP l T δ α ls ρ := by
    show ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρ
    rw [← e]; exact hm
  refine ⟨true, PMap.empty, ρ, compS_empty_left ρ, hm', ResU.inStratum_empty α,
    fun ls' _ α' _ ρv σ hv hcv => ?_⟩
  rw [eq_of_compS_empty_left hcv]
  exact mutView hT hv

/-- **A slot free of `'x`, in `Res_α`**: nothing is dropped, and the relation does not read `'x`. -/
theorem relendable_free {A : VTy} (hA : ¬ VFree x A) {α : Life} {ls : List SRec} {v : Val}
    {ρ : WRes} (hz : ρ.InStratum α) (h : vC true A ls (δ.extend x α) v ρ) :
    Relendable l T δ (fun α' ls' => vC true A ls' (δ.extend x α') v) α ls ρ := by
  refine ⟨false, ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨rfl, trivial⟩, hz,
    fun ls' he α' _ ρv σ hv hcv => ?_⟩
  obtain ⟨rfl, -⟩ := hv
  rw [ResU.CompS.functional hcv (ResU.comp_empty_right ρ)]
  rw [vC_extend_of_not_free hA] at h ⊢
  exact vC_local true A he h

/-- **A pair is re-lendable when its components are** (`relendable_sep`). -/
theorem relendable_tensor {A B : VTy} {α : Life} {ls : List SRec}
    (hA : ∀ v ρ, vRL S x T δ l A α ls v ρ →
      Relendable l T δ (fun α' ls' => vRL S x T δ l A α' ls' v) α ls ρ)
    (hB : ∀ v ρ, vRL S x T δ l B α ls v ρ →
      Relendable l T δ (fun α' ls' => vRL S x T δ l B α' ls' v) α ls ρ)
    {v : Val} {ρ : WRes} (h : vRL S x T δ l (.tensor A B) α ls v ρ) :
    Relendable l T δ (fun α' ls' => vRL S x T δ l (.tensor A B) α' ls' v) α ls ρ := by
  obtain ⟨v₁, v₂, hs⟩ := h
  obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
  exact relendable_mono (fun α' ls' σ hσ => ⟨v₁, v₂, pure_sep_mk rfl hσ⟩) ρ
    (relendable_sep ρ ⟨ρ₁, ρ₂, hc, hA v₁ ρ₁ h₁, hB v₂ ρ₂ h₂⟩)

/-- `⊛_{x ∈ dom(Γ)} vRL(Γ(x))`: a context read at route (b)'s relation. -/
def gRL (S : Row) (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) (α : Life)
    (ls : List SRec) : Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then vRL S x T δ l s.ty α ls v ⋆ gRL S x T δ l α ls Γ γ
      else gRL S x T δ l α ls Γ γ

/-- The empty context is re-lendable. -/
theorem relendable_emp {α : Life} {ls : List SRec} {ρ : WRes} (h : emp ρ) :
    Relendable l T δ (fun _ _ => emp) α ls ρ := by
  obtain ⟨rfl, -⟩ := h
  refine ⟨false, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩,
    ResU.inStratum_empty α, fun _ _ _ _ ρv σ hv hc => ?_⟩
  obtain ⟨rfl, -⟩ := hv
  exact ⟨eq_of_compS_empty_left hc, trivial⟩

/-- **A context is re-lendable when its live slots are.** -/
theorem relendable_gRL {α : Life} {ls : List SRec} : ∀ (Γ : Ctx VTy),
    (∀ s ∈ Γ, s.live = true → ∀ v ρ, vRL S x T δ l s.ty α ls v ρ →
      Relendable l T δ (fun α' ls' => vRL S x T δ l s.ty α' ls' v) α ls ρ) →
    ∀ (γ : List Val) {ρ : WRes}, gRL S x T δ l α ls Γ γ ρ →
      Relendable l T δ (fun α' ls' => gRL S x T δ l α' ls' Γ γ) α ls ρ
  | [], _, _, _, h => relendable_emp h
  | _ :: _, _, [], _, h => relendable_emp h
  | s :: Γ, hs, v :: γ, ρ, h => by
      have hs' : ∀ s' ∈ Γ, s'.live = true → ∀ v ρ, vRL S x T δ l s'.ty α ls v ρ →
          Relendable l T δ (fun α' ls' => vRL S x T δ l s'.ty α' ls' v) α ls ρ :=
        fun s' hm hl => hs s' (List.mem_cons_of_mem _ hm) hl
      by_cases hl : s.live = true
      · simp only [gRL, hl, if_true] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact relendable_sep ρ ⟨ρ₁, ρ₂, hc, hs s List.mem_cons_self hl v ρ₁ h₁,
          relendable_gRL Γ hs' γ h₂⟩
      · simp only [gRL, hl] at h ⊢
        exact relendable_gRL Γ hs' γ h

/-- **`thunk M : U (F A)` at `vRL`, from the body's judgment**: every live slot re-lendable. -/
theorem thunkF_RL_ctx {Γ : Ctx VTy} {M : Expr} {A : VTy} {γ : List Val} {α : Life}
    {ls : List SRec} {ρ : WRes}
    (hs : ∀ s ∈ Γ, s.live = true → ∀ v ρ, vRL S x T δ l s.ty α ls v ρ →
      Relendable l T δ (fun α' ls' => vRL S x T δ l s.ty α' ls' v) α ls ρ)
    (hM : ∀ α', α' ≤ α → ∀ ls' σ, gRL S x T δ l α' ls' (⟨.unit, false⟩ :: Γ) (Val.unit :: γ) σ →
      cRL S x T δ l (.ret A) α' ls' (substAll (Val.unit :: γ) M) σ)
    (hg : gRL S x T δ l α ls Γ γ ρ) :
    vRL S x T δ l (.thunk (.ret A)) α ls (Val.lam (Expr.psub 1 γ M)) ρ :=
  thunkF_RL (relendable_gRL Γ hs γ hg) (fun α' hle ls' σ h => hM α' hle ls' σ h)

end

/-! ### `[let]` with a re-lendable frame -/

section
variable {Tab : OpTab} {l : BoCa.Loc} {T : VTy} {δ : LSub}

/-- **`[let]`, `bind`, call-by-value application** at a linear resuming table: a pure context `K`
around a piece, its frame re-lendable. -/
theorem bind_RL (hLR : LinResume Tab) (K : Kont) (hH : ∀ n, K.HasHnd n = false) {β : Life}
    (Fr : Life → List SRec → WProp)
    (hFs : ∀ α ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α ls) (Fr α ls'))
    (hG : ∀ α, α ⊏ β → ∀ ls, Entails (Fr α ls) (Relendable l T δ Fr α ls))
    {Q₁ Q : Life → List SRec → Val → WProp}
    (hk : ∀ α, α ⊏ β → ∀ ls v, Entails (Q₁ α ls v ⋆ Fr α ls)
      (bodyAtD (opTable Tab) l T δ Q (OpenD (opTable Tab) l T δ Q) α ls (K.plug (.val v))))
    {α : Life} (hα : α ⊏ β) {ls : List SRec} {e : Expr} {ρ₁ ρf ρ : WRes}
    (h : bodyAtD (opTable Tab) l T δ Q₁ (OpenD (opTable Tab) l T δ Q₁) α ls e ρ₁)
    (hf : Fr α ls ρf) (hc : ResU.CompS ρ₁ ρf ρ) :
    bodyAtD (opTable Tab) l T δ Q (OpenD (opTable Tab) l T δ Q) α ls (K.plug e) ρ := by
  let Fz : Life → Bool → List SRec → WProp := fun β' d ls ρz =>
    ρz.InStratum β' ∧ ∀ ls', Ext ls ls' ρz → ∀ α', α' ≤ β' → (vwD l T δ d α' ls' ─⋆ Fr α' ls') ρz
  have hFe : ∀ β' d ls ls' ρ, Ext ls ls' ρ → Fz β' d ls ρ → Fz β' d ls' ρ :=
    fun _ _ _ _ _ he h => ⟨h.1, fun ls'' he' => h.2 ls'' (he.trans he')⟩
  have hFo : ∀ β' d ls ρ, Fz β' d ls ρ → ρ.InStratum β' := fun _ _ _ _ h => h.1
  have hfz : ∀ α', α' ⊏ β → ∀ ls ρ, Fr α' ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz α' d ls ρz ∧ dropC l d ρn := by
    intro α' hα' ls ρ hF
    obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ := hG α' hα' ls ρ hF
    exact ⟨d, ρz, ρn, hc, ⟨hz, hth⟩, dropC_of_vwD hn⟩
  have hthaw : ∀ β' α' d₂ ls ρv ρz ρ, α' ⊏ β' → β' ≤ β → vwD l T δ d₂ α' ls ρv →
      Fz β' d₂ ls ρz → ResU.CompS ρv ρz ρ → Fr α' ls ρ :=
    fun _ α' _ ls ρv ρz ρ hα' _ hv hz hc =>
      hz.2 ls (Ext.refl ls ρz) α' (le_of_lt hα') ρv ρ hv (ResU.CompS.comm hc)
  exact bodyAtD_bind hLR K hH Fr Fz hFs hFe hFo (hfz α hα)
    (fun d₁ d₂ _ _ _ _ _ hnd hx hz hcτ =>
      openD_bind hLR K hH β Fr Fz hFs hFe hFo hfz hthaw hk (le_of_lt hα) hnd hx hz hcτ)
    (hk α hα) h hf hc

/-- **`[handle]`'s continuation**: a continuation re-lendable at an inner stop stays re-lendable
under a re-lendable frame. -/
theorem relendable_cont_frame {K₁ Fr K : Life → List SRec → WProp}
    (hplug : ∀ α' ls', Entails (K₁ α' ls' ⋆ Fr α' ls') (K α' ls')) {α : Life}
    {ls : List SRec} :
    Entails (Relendable l T δ K₁ α ls ⋆ Relendable l T δ Fr α ls) (Relendable l T δ K α ls) :=
  fun ρ h => relendable_mono hplug ρ (relendable_sep ρ h)

end

/-! ### Where the single-lend relation stops: a value below the lend -/

section
variable {l : BoCa.Loc} {T : VTy} {δ : LSub}

/-- **A re-lendable resource holds no cell off `ℓ` at or below `α`.** -/
theorem relendable_off_cell {P : Life → List SRec → WProp} {α : Life} {ls : List SRec}
    {ρ : WRes} (h : Relendable l T δ P α ls ρ) {k : BoCa.Loc} {ψ : CellU BoCa.Loc BoCa.Val}
    (hk : k ≠ l) (e : ρ.get k = some ψ) : ψ.InStratum α := by
  obtain ⟨d, ρz, ρn, hc, hn, hz, -⟩ := h
  refine ResU.inStratum_comp_at (CellU.compS_hC α) hc (fun φ f => hz k φ f) (fun φ f => ?_) e
  exfalso
  cases d with
  | false => obtain ⟨rfl, -⟩ := hn; rw [PMap.empty_get] at f; exact absurd f (by simp)
  | true =>
      obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := hn
      rw [ResU.single_get_ne _ hk] at f; exact absurd f (by simp)

end

/-- `𝒱⟦1⟧` as a stored predicate at `b`. -/
def unitQ (b : Life) : BoCa.Val → SPropS BoCa.Loc BoCa.Val b :=
  fun v => SPropU.toS b (BoLo.pure (v = Val.unit))

theorem unitQ_holds (b : Life) : unitQ b Val.unit ⟨PMap.empty, ResU.inStratum_empty b⟩ :=
  ⟨rfl, rfl⟩

/-- **An inner lend's view**, `k ↦ M_{αy} 𝒱⟦1⟧`: the cell 6.65's entry builds at a fresh `αy`. -/
def innerView (k : BoCa.Loc) (αy : Life) : WRes :=
  ResU.single k (CellU.mutOf αy Val.unit PMap.empty (ResU.inStratum_empty αy) (unitQ αy)
    (unitQ_holds αy))

/-- The inner view is a `mut` cell at `αy` storing `𝒱⟦1⟧`. -/
theorem innerView_ptoMutS (k : BoCa.Loc) (αy : Life) (ls : List SRec) (δ' : LSub) :
    ptoMutS k αy ls (fun ls₀ => vC true .unit ls₀ δ') (innerView k αy) := by
  refine ⟨αy, Val.unit, PMap.empty, ResU.inStratum_empty αy, unitQ αy, unitQ_holds αy,
    ls.filter (fun r => decide (r.2 ⊐ αy)), le_rfl, rfl, ?_, ?_, ?_⟩
  · funext v ρ
    apply propext
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      exact ⟨by obtain ⟨rfl, -⟩ := h; exact ResU.inStratum_empty αy, h⟩
  · intro r; simp [List.mem_filter]
  · rintro ls' u' σ' ⟨rfl, -⟩; exact ResU.inStratum_empty αy

/-- The context of an inner borrow's callback inside the borrower: `x ⊏ ⊤, y ⊏ ⊓Δ`, the bound
`withbor`'s type gives its lifetime (`axWithbor1Ty x Δ.meetOfDom`). -/
abbrev innerCtx (x y : LifeVar) : LifeCtx :=
  (LifeCtx.empty.extend x .top).extend y (LifeCtx.empty.extend x .top).meetOfDom

/-- `δ₀[y ↦ αy][x ↦ α] ∈ ⟦x ⊏ ⊤, y ⊏ ⊓Δ⟧` for `αy ⊏ α ⊏ ⊤`. -/
theorem innerCtx_models {x y : LifeVar} (hxy : x ≠ y) (δ₀ : LSub) {α αy : Life}
    (hα : α ⊏ (Lifetime.SLife.top : Life)) (hαy : αy ⊏ α) :
    (innerCtx x y).Models ((δ₀.extend y αy).extend x α) := by
  intro z u hz
  rw [LifeCtx.find?_extend] at hz
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos rfl] at hz
    cases hz
    refine ⟨αy, α, by rw [find?_extend_ne _ _ hxy, find?_extend_self]; rfl, ?_, hαy⟩
    show ((Lifetime.Life.var x).interp _).bind _ = _
    rw [Lifetime.Life.interp_var, find?_extend_self]
    show some (Lifetime.SLife.meet α Lifetime.SLife.top) = some α
    exact congrArg some (Nat.max_eq_left (Nat.zero_le _))
  · rw [if_neg hyz, LifeCtx.find?_extend] at hz
    by_cases hxz : x = z
    · subst hxz
      rw [if_pos rfl] at hz
      cases hz
      exact ⟨α, Lifetime.SLife.top, find?_extend_self _ _ _, rfl, hα⟩
    · rw [if_neg hxz] at hz
      exact absurd hz (by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind])

/-- The inner borrow's view in the callback's context `n : Mut 'y 1`, the borrow's own `m` dead. -/
abbrev innerΓ (x y : LifeVar) (T : VTy) : Ctx VTy := [⟨.mut (.var y) .unit, true⟩, mSlot x T false]

/-- **`thunk (return n)` under an inner lend is outside the single-lend `vRL`.** The term is
typed in the callback's context, the substitution models it, the context is in `gRL`, and
`thunkF_RL`'s body premise holds. Its other premise, the context re-lendable, fails, and so does
its conclusion, for every closure value. The table's hypothesis `TabAt` fails here too. -/
theorem thunkF_RL_fails_below {S : Row} {x y : LifeVar} (hxy : x ≠ y) {T : VTy} (δ₀ : LSub)
    {l k : BoCa.Loc} (hkl : k ≠ l) {α αy : Life} (hα : α ⊏ (Lifetime.SLife.top : Life))
    (hαy : αy ⊏ α) (ls : List SRec) :
    let δ := δ₀.extend y αy
    let γ : List Val := [.loc k, .loc l]
    let A : VTy := .mut (.var y) .unit
    CDerives (innerCtx x y) (innerΓ x y T) (.val (.lam (.var 1))) (.val (.thunk (.ret A))) ∧
      (innerCtx x y).Models (δ.extend x α) ∧
      gRL S x T δ l α ls (innerΓ x y T) γ (innerView k αy) ∧
      (∀ α', α' ≤ α → ∀ ls' σ,
        gRL S x T δ l α' ls' (⟨.unit, false⟩ :: innerΓ x y T) (Val.unit :: γ) σ →
        cRL S x T δ l (.ret A) α' ls' (substAll (Val.unit :: γ) (.var 1)) σ) ∧
      ¬ TabAt l α (innerView k αy) ∧
      ¬ Relendable l T δ (fun α' ls' => gRL S x T δ l α' ls' (innerΓ x y T) γ) α ls
        (innerView k αy) ∧
      ∀ f : Val, ¬ vRL S x T δ l (.thunk (.ret A)) α ls f (innerView k αy) := by
  intro δ γ A
  have hcell : ¬ (CellU.mutOf αy Val.unit PMap.empty (ResU.inStratum_empty αy) (unitQ αy)
      (unitQ_holds αy)).InStratum α := fun h => lt_asymm hαy h
  have hget := ResU.single_get_self k (CellU.mutOf αy Val.unit PMap.empty
    (ResU.inStratum_empty αy) (unitQ αy) (unitQ_holds αy))
  have hslot : vRL S x T δ l A α ls (.loc k) (innerView k αy) := by
    refine ⟨αy, ?_, k, pure_sep_mk rfl (innerView_ptoMutS k αy ls _)⟩
    rw [Lifetime.Life.interp_var, find?_extend_ne _ _ hxy, find?_extend_self]; rfl
  refine ⟨.thunkF (.ret (.var (.there (.here (.cons .nil))))),
    innerCtx_models hxy δ₀ hα hαy, ?_, ?_, fun ht => hcell (ht.2 k _ hkl hget),
    fun hr => hcell (relendable_off_cell hr hkl hget),
    fun f hf => hcell (relendable_off_cell hf hkl hget)⟩
  · exact ⟨_, _, ResU.comp_empty_right _, hslot, rfl, trivial⟩
  · intro α' _ ls' σ h
    rw [substAll_var_l (show (Val.unit :: γ)[1]? = some (.loc k) from rfl)]
    obtain ⟨σ₁, σ₂, hc, h₁, rfl, -⟩ := h
    rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)]
    exact bodyAtD_of_wpTS (wpTS_val ls' _ _ σ₁ h₁)

/-- The configuration at numerals: `x = 0`, `y = 1`, `ℓ = 0`, `k = 1`, `α = 1`, `αy = 2`. -/
theorem thunkF_RL_fails_below_at (S : Row) (T : VTy) (ls : List SRec) :
    let α : Life := OrderDual.toDual 1
    let δ := LSub.empty.extend 1 (OrderDual.toDual 2)
    let γ : List Val := [.loc 1, .loc 0]
    let A : VTy := .mut (.var 1) .unit
    let ρ := innerView 1 (OrderDual.toDual 2)
    CDerives (innerCtx 0 1) (innerΓ 0 1 T) (.val (.lam (.var 1))) (.val (.thunk (.ret A))) ∧
      (innerCtx 0 1).Models (δ.extend 0 α) ∧
      gRL S 0 T δ 0 α ls (innerΓ 0 1 T) γ ρ ∧
      (∀ α', α' ≤ α → ∀ ls' σ,
        gRL S 0 T δ 0 α' ls' (⟨.unit, false⟩ :: innerΓ 0 1 T) (Val.unit :: γ) σ →
        cRL S 0 T δ 0 (.ret A) α' ls' (substAll (Val.unit :: γ) (.var 1)) σ) ∧
      ¬ TabAt 0 α ρ ∧
      ¬ Relendable 0 T δ (fun α' ls' => gRL S 0 T δ 0 α' ls' (innerΓ 0 1 T) γ) α ls ρ ∧
      ∀ f : Val, ¬ vRL S 0 T δ 0 (.thunk (.ret A)) α ls f ρ :=
  thunkF_RL_fails_below (by decide) LSub.empty (by decide)
    (show (0 : ℕ) < 1 from by decide) (show (1 : ℕ) < 2 from by decide) ls

/-! ### The table as a guard: `vRLg`

`relendable_off_cell` makes the stratum a demand on every `U` value. `vRLg` makes it a guard: at
the lend `α` a `U` value is read as it stands, and it is frozen into `Res_α` and re-lent at every
`α′ ⊑ α` only when its resource is consistent with the table. A frame at a stop is consistent with
it (`wpG_tabAt`), so a stop loses nothing. A closure over a value below the lend is not, so it owes
the reading at `α` alone. -/

/-- **Re-lendable when consistent with the table.** -/
def RelendableG (l : BoCa.Loc) (T : VTy) (δ : LSub) (P : Life → List SRec → WProp) (α : Life)
    (ls : List SRec) : WProp := fun ρ =>
  ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ vwD l T δ d α ls ρn ∧
    (∀ ls', Ext ls ls' ρz → (vwD l T δ d α ls' ─⋆ P α ls') ρz) ∧
    (TabAt l α ρ → ρz.InStratum α ∧
      ∀ ls', Ext ls ls' ρz → ∀ α', α' ≤ α → (vwD l T δ d α' ls' ─⋆ P α' ls') ρz)

mutual
/-- **`vRL` with the table as a guard.** At `U C` the clause is `RelendableG`; at `⊗`
componentwise; elsewhere the ordinary relation at `δ[x ↦ α]`, as `vRL`. -/
def vRLg (S : Row) (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) :
    VTy → Life → List SRec → Val → WProp
  | .thunk C, α, ls, f => fun ρ => ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ vwD l T δ d α ls ρn ∧
      (∀ ls', Ext ls ls' ρz → (vwD l T δ d α ls' ─⋆ cRLg S x T δ l C α ls' (forceE C (.val f))) ρz) ∧
      (TabAt l α ρ → ρz.InStratum α ∧ ∀ ls', Ext ls ls' ρz → ∀ α', α' ≤ α →
        (vwD l T δ d α' ls' ─⋆ cRLg S x T δ l C α' ls' (forceE C (.val f))) ρz)
  | .tensor A B, α, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLg S x T δ l A α ls v₁ ⋆ vRLg S x T δ l B α ls v₂
  | A, α, ls, v => vC true A ls (δ.extend x α) v
/-- `cRL` over `vRLg`. -/
def cRLg (S : Row) (x : LifeVar) (T : VTy) (δ : LSub) (l : BoCa.Loc) :
    CTy → Life → List SRec → Expr → WProp
  | .ret B, α, ls, e => bodyAtD (opTable (Row.tab S δ)) l T δ
      (fun α' ls' v => vRLg S x T δ l B α' ls' v)
      (OpenD (opTable (Row.tab S δ)) l T δ (fun α' ls' v => vRLg S x T δ l B α' ls' v)) α ls e
  | .arr A C, α, ls, e => fun ρ =>
      ∀ v, (vRLg S x T δ l A α ls v ─⋆ cRLg S x T δ l C α ls (.app e (.val v))) ρ
  | _, _, _, _ => fun _ => True
end

section
variable {S : Row} {x : LifeVar} {T : VTy} {δ : LSub} {l : BoCa.Loc}

/-- `vRLg`'s `U` clause is `RelendableG` of `cRLg C` at the forced closure. -/
theorem vRLg_thunk_iff {C : CTy} {α : Life} {ls : List SRec} {f : Val} {ρ : WRes} :
    vRLg S x T δ l (.thunk C) α ls f ρ ↔
      RelendableG l T δ (fun α' ls' => cRLg S x T δ l C α' ls' (forceE C (.val f))) α ls ρ :=
  Iff.rfl

/-- **`[force]` at `vRLg`**: the reading at `α`, with no table. -/
theorem forceG {C : CTy} {α : Life} {ls : List SRec} {f : Val} {ρ : WRes}
    (h : vRLg S x T δ l (.thunk C) α ls f ρ) :
    cRLg S x T δ l C α ls (forceE C (.val f)) ρ := by
  obtain ⟨d, ρz, ρn, hc, hn, hnow, -⟩ := h
  exact hnow ls (Ext.refl ls ρz) ρn ρ hn hc

/-- **A `U` slot consistent with the table thaws by construction**: `relendable_thunk` at
`vRLg`, the guard discharged by the table. -/
theorem relendableG_thunk {C : CTy} {α : Life} {ls : List SRec} {f : Val} {ρ : WRes}
    (ht : TabAt l α ρ) (h : vRLg S x T δ l (.thunk C) α ls f ρ) :
    Relendable l T δ (fun α' ls' => vRLg S x T δ l (.thunk C) α' ls' f) α ls ρ := by
  obtain ⟨d, ρz, ρn, hc, hn, -, hg⟩ := h
  obtain ⟨hz, hth⟩ := hg ht
  refine ⟨d, ρz, ρn, hc, hn, hz, fun ls' he α' hle ρv σ hv hcv => ?_⟩
  exact ⟨d, ρz, ρv, hcv, hv, fun ls'' he' => hth ls'' (he.trans he') α' hle,
    fun _ => ⟨hz.mono hle, fun ls'' he' α'' hle' => hth ls'' (he.trans he') α''
      (le_trans hle' hle)⟩⟩

/-- **`URelend` at `vRLg`**, with no hypothesis beyond the table it already carries. -/
theorem uRelendRLg (C : CTy) (f : Val) (α : Life) (ls : List SRec) (ρ : WRes)
    (ht : TabAt l α ρ) (h : vRLg S x T δ l (.thunk C) α ls f ρ) :
    ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ dropC l d ρn ∧ ρz.InStratum α ∧
      ∀ ls', Ext ls ls' ρz → ∀ α', α' ⊏ α → ∀ ρv ρ', vwD l T δ d α' ls' ρv →
        ResU.CompS ρv ρz ρ' → TabAt l α' ρ' ∧ vRLg S x T δ l (.thunk C) α' ls' f ρ' := by
  obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ := relendableG_thunk ht h
  refine ⟨d, ρz, ρn, hc, dropC_of_vwD hn, hz, fun ls' he α' hα' ρv ρ' hv hc' => ⟨?_, ?_⟩⟩
  · refine (tabAt_comp hc').mpr ⟨?_, tabAt_of_inStratum (hz.mono (le_of_lt hα'))⟩
    cases d with
    | false => obtain ⟨rfl, -⟩ := hv; exact tabAt_empty l α'
    | true => exact tabAt_view hv
  · exact hth ls' he α' (le_of_lt hα') ρv ρ' hv (ResU.CompS.comm hc')

/-- **`thunk M : U (F A)` at `vRLg`.** The body is read at `α` from the context at `α`; when the
context is consistent with the table it is re-lendable, and the body is read at every `α′ ⊑ α`. -/
theorem thunkF_RLg {G : Life → List SRec → WProp} {M : Expr} {A : VTy} {γ : List Val}
    {α : Life} {ls : List SRec} {ρ : WRes}
    (hGl : ∀ ls', Ext ls ls' ρ → G α ls ρ → G α ls' ρ) (hG₀ : G α ls ρ)
    (hG : TabAt l α ρ → Relendable l T δ G α ls ρ)
    (hM : ∀ α', α' ≤ α → ∀ ls' σ, G α' ls' σ →
      cRLg S x T δ l (.ret A) α' ls' (substAll (Val.unit :: γ) M) σ) :
    vRLg S x T δ l (.thunk (.ret A)) α ls (Val.lam (Expr.psub 1 γ M)) ρ := by
  have hrun : ∀ α', α' ≤ α → ∀ ls' σ, G α' ls' σ →
      cRLg S x T δ l (.ret A) α' ls' (forceE (.ret A) (.val (Val.lam (Expr.psub 1 γ M)))) σ := by
    intro α' hle ls' σ h
    refine wpG_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    exact hM α' hle ls' σ h
  by_cases ht : TabAt l α ρ
  · obtain ⟨d, ρz, ρn, hc, hn, hz, hth⟩ := hG ht
    exact ⟨d, ρz, ρn, hc, hn,
      fun ls' he ρv σ hv hcv => hrun α le_rfl ls' σ (hth ls' he α le_rfl ρv σ hv hcv),
      fun _ => ⟨hz, fun ls' he α' hle ρv σ hv hcv =>
        hrun α' hle ls' σ (hth ls' he α' hle ρv σ hv hcv)⟩⟩
  · refine ⟨false, ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨rfl, trivial⟩,
      fun ls' he ρv σ hv hcv => ?_, fun h => absurd h ht⟩
    obtain ⟨rfl, -⟩ := hv
    rw [ResU.CompS.functional hcv (ResU.comp_empty_right ρ)]
    exact hrun α le_rfl ls' ρ (hGl ls' he hG₀)

end

/-- **The configuration of `thunkF_RL_fails_below` is inside `vRLg`.** The closure over the
inner borrow's view is read at `α` and owes no re-lend, since its resource is not consistent with
the table. -/
theorem thunkF_RLg_below {S : Row} {x y : LifeVar} (hxy : x ≠ y) {T : VTy} (δ₀ : LSub)
    {l k : BoCa.Loc} (hkl : k ≠ l) {α αy : Life} (hαy : αy ⊏ α) (ls : List SRec) :
    vRLg S x T (δ₀.extend y αy) l (.thunk (.ret (.mut (.var y) .unit))) α ls
      (Val.lam (Expr.psub 1 [.loc k, .loc l] (.var 1))) (innerView k αy) := by
  let δ := δ₀.extend y αy
  have hcell : ¬ (CellU.mutOf αy Val.unit PMap.empty (ResU.inStratum_empty αy) (unitQ αy)
      (unitQ_holds αy)).InStratum α := fun h => lt_asymm hαy h
  have hget := ResU.single_get_self k (CellU.mutOf αy Val.unit PMap.empty
    (ResU.inStratum_empty αy) (unitQ αy) (unitQ_holds αy))
  have hslot : ∀ ls', vC true (.mut (.var y) .unit) ls' (δ.extend x α) (.loc k)
      (innerView k αy) := by
    intro ls'
    refine ⟨αy, ?_, k, pure_sep_mk rfl (innerView_ptoMutS k αy ls' _)⟩
    rw [Lifetime.Life.interp_var, find?_extend_ne _ _ hxy, find?_extend_self]; rfl
  refine thunkF_RLg (G := fun α' ls' σ => α' = α ∧
      vC true (.mut (.var y) .unit) ls' (δ.extend x α') (.loc k) σ)
    (fun ls' _ h => ⟨rfl, hslot ls'⟩) ⟨rfl, hslot ls⟩
    (fun ht => absurd (ht.2 k _ hkl hget) hcell) ?_
  rintro α' - ls' σ ⟨rfl, h⟩
  rw [substAll_var_l (show ([Val.unit, .loc k, .loc l] : List Val)[1]? = some (.loc k) from rfl)]
  exact bodyAtD_of_wpTS (wpTS_val ls' _ _ σ h)

end GhostEnd
