import GhostEnd.Body
import GhostEnd.Open

/-!
# GhostEnd — typed borrowers, each stop a typed segment

A borrower is `λm. M` with `Δ, x ⊏ b; m : Mut 'x T ⊢ M : F_Σ (['x] B)`. Every subterm of `M` is
typed in a context `Γ ++ [m]`: the borrow is the outermost variable, the last slot. Its value is
the lent location `ℓ` throughout, since nothing rebinds it.

`RBody Γ ml E A` is the semantic judgment of a piece `E` of a borrower. At every lend `α ⊏ @bδ`
and every closing substitution `γ ++ [ℓ]` in `𝒢⟦Γ ++ [m]⟧` at `δ[x ↦ α]`, `E` runs with the lend
open at `α` (`bodyAt`). It answers in `𝒱⟦A⟧` at `δ[x ↦ α]` with the lend still open, or stops,
and what it owes the stop is `Open` again. `ml` says whether the slot `m` is live in `E`.

**Each stop is a typed segment.** A stop is reached only at a `perform` (`rbody_perform`), and
the context around it is a stack of `let` frames `(λz. N) [·]` (`rbody_let`). Each frame's code
is a typed term `N`, closed by its context's values `γ₂ ++ [ℓ]`. That is `segment_fundamental`'s
`SegOf K N γ` for the frame `K`. At the resumption the frame's code is re-derived at the fresh
lend from its own judgment `RBody (A₁ :: Γ₂) ml₂ N A`. The frame's values are re-instantiated:

* the slot `m` holds `ℓ`, and the fresh lend's view is `𝒱⟦Mut 'x T⟧` at `δ[x ↦ α′]` at `ℓ`
  (`mutView`);
* every other live slot of a frame that spans a stop has a type free of `'x` that outlives it
  (`StopSafe`). Its relation is the same at `δ[x ↦ α′]` (`vC_extend_of_not_free`), and its
  resource lies in `[α]` (6.60), so the stop's share is in `[α]`.

**The measure.** The rules are proved by `RBody`'s own structure: each rule from its premises.
The stops' continuations are `Open` (`Body.lean`), and `open_bind` composes them by induction on
`Open`. No lifetime enters either measure.

* `rbody_ret`: a pure piece, by `fundamentalC` at `δ[x ↦ α]`;
* `rbody_perform`: `perform`, a stop, the view if any left behind;
* `rbody_let`: `M to z. N`, `N`'s context a frame carried through `M`'s stops;
* `rbody_case`: a branch on a value;
* `relend_of_rbody`: a whole borrower is `Relend`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Contexts with the borrow as the last slot -/

/-- `Γ = Γ₁, Γ₂` joins the resource: the converse of `gSepC_splitP`. -/
theorem gSepC_joinP {ls : List SRec} {δ : LSub} : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ →
    ∀ {γ : List Val} {ρ : WRes}, (gSepC ls δ Γ₁ γ ⋆ gSepC ls δ Γ₂ γ) ρ → gSepC ls δ Γ γ ρ := by
  intro Γ Γ₁ Γ₂ hsp
  induction hsp with
  | nil =>
      intro γ ρ h
      obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
      cases γ <;>
      · obtain ⟨rfl, -⟩ := h₁; obtain ⟨rfl, -⟩ := h₂
        exact ⟨eq_of_compS_empty_left hc, trivial⟩
  | left _ ih =>
      intro γ ρ h
      cases γ with
      | nil =>
          obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, ⟨rfl, -⟩⟩ := h
          exact ⟨eq_of_compS_empty_left hc, trivial⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, ⟨τ₁, τ₂, hcτ, hv, h₁⟩, h₂⟩ := h
          obtain ⟨x, hx, hxρ⟩ := compS_reassoc hcτ hc
          exact ⟨τ₁, x, hxρ, hv, ih ⟨τ₂, ρ₂, hx, h₁, h₂⟩⟩
  | right _ ih =>
      intro γ ρ h
      cases γ with
      | nil =>
          obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, ⟨rfl, -⟩⟩ := h
          exact ⟨eq_of_compS_empty_left hc, trivial⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, h₁, ⟨τ₁, τ₂, hcτ, hv, h₂⟩⟩ := h
          obtain ⟨x, hx, hxρ⟩ := compS_lcomm hcτ hc
          exact ⟨τ₁, x, hxρ, hv, ih ⟨ρ₁, τ₂, hx, h₁, h₂⟩⟩
  | dead _ ih =>
      intro γ ρ h
      cases γ with
      | nil =>
          obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, ⟨rfl, -⟩⟩ := h
          exact ⟨eq_of_compS_empty_left hc, trivial⟩
      | cons v γ' => exact ih h
  | dup hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil =>
          obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, ⟨rfl, -⟩⟩ := h
          exact ⟨eq_of_compS_empty_left hc, trivial⟩
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, ⟨τ₁, τ₂, hcτ, hv, h₁⟩, ⟨τ₃, τ₄, hcτ', hv', h₂⟩⟩ := h
          obtain rfl : τ₁ = PMap.empty := vP_empty_of_persistent hT hv
          obtain rfl : τ₃ = PMap.empty := vP_empty_of_persistent hT hv'
          obtain rfl := eq_of_compS_empty_left hcτ
          obtain rfl := eq_of_compS_empty_left hcτ'
          exact ⟨PMap.empty, ρ, compS_empty_left ρ, hv, ih ⟨_, _, hc, h₁, h₂⟩⟩

/-- The borrow's slot. -/
abbrev mSlot (x : LifeVar) (T : VTy) (ml : Bool) : Slot VTy := ⟨.mut (.var x) T, ml⟩

/-- Every slot dead. -/
def deadCtx (Γ : Ctx VTy) : Ctx VTy := Γ.map fun s => ⟨s.ty, false⟩

@[simp] theorem deadCtx_length (Γ : Ctx VTy) : (deadCtx Γ).length = Γ.length := by
  simp [deadCtx]

/-- The borrow's slot splits off a context. -/
theorem splitP_last (A : VTy) : ∀ Γ : Ctx VTy,
    Ctx.SplitP (Γ ++ [⟨A, true⟩]) (Γ ++ [⟨A, false⟩]) (deadCtx Γ ++ [⟨A, true⟩])
  | [] => .right .nil
  | ⟨_, true⟩ :: Γ => .left (splitP_last A Γ)
  | ⟨_, false⟩ :: Γ => .dead (splitP_last A Γ)

theorem sep_emp_iff {P : WProp} {ρ : WRes} : (P ⋆ emp) ρ ↔ P ρ := by
  constructor
  · rintro ⟨ρ₁, ρ₂, hc, hp, rfl, -⟩
    rwa [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  · intro hp
    exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, hp, rfl, trivial⟩

/-- A context dead but for its last slot holds that slot's relation. -/
theorem gSepC_dead_last {ls : List SRec} {δ : LSub} {A : VTy} {v : Val} :
    ∀ (Γ : Ctx VTy) (γ : List Val), γ.length = Γ.length → ∀ {ρ : WRes},
      gSepC ls δ (deadCtx Γ ++ [⟨A, true⟩]) (γ ++ [v]) ρ ↔ vC true A ls δ v ρ
  | [], [], _, ρ => by
      show (vC true A ls δ v ⋆ gSepC ls δ [] []) ρ ↔ _
      exact sep_emp_iff
  | _ :: Γ, _ :: γ, h, ρ => gSepC_dead_last Γ γ (by simpa using h)
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem liveWithin_append (Γ : Ctx VTy) (s : Slot VTy) :
    ∀ (γ : List Val) (v : Val), γ.length = Γ.length → Ctx.LiveWithin (Γ ++ [s]) (γ ++ [v]) := by
  induction Γ with
  | nil => intro γ v h; cases γ with
    | nil => trivial
    | cons _ _ => simp at h
  | cons t Γ ih => intro γ v h; cases γ with
    | nil => simp at h
    | cons w γ => exact ih γ v (by simpa using h)

/-- The borrow's view, read off its slot at `δ[x ↦ α]`: the converse of `mutView`. -/
theorem view_of_vC {x : LifeVar} {T : VTy} (hT : ¬ VFree x T) {l : BoCa.Loc} {α : Life}
    {ls : List SRec} {δ : LSub} {ρ : WRes}
    (h : vC true (.mut (.var x) T) ls (δ.extend x α) (.loc l) ρ) : viewP l T δ α ls ρ := by
  obtain ⟨α', hα', l', hs⟩ := h
  obtain ⟨hl, hm⟩ := pure_sep_iff.mp hs
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  obtain rfl : l = l' := by
    have := congrArg Subtype.val hl
    simpa [Val.loc] using this
  have e : (fun ls₀ => vC true T ls₀ (δ.extend x α)) = (fun ls₀ => vC true T ls₀ δ) :=
    funext fun ls₀ => vC_extend_of_not_free hT true ls₀ δ α
  have hm' : ptoMutS l α ls (fun ls₀ => vC true T ls₀ (δ.extend x α)) ρ := hm
  rw [e] at hm'
  exact hm'

/-! ### The judgment -/

/-- A frame that spans a stop: every live slot has a type free of `'x` that outlives it. -/
def StopSafe (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (Γ : Ctx VTy) : Prop :=
  ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty ∧ VOutlives (Δ.extend x b) (.var x) s.ty

/-- A piece's answer: `𝒱⟦A⟧` at the lend it answers at. -/
def ansR (x : LifeVar) (δ : LSub) (A : VTy) : Life → List SRec → Val → WProp :=
  fun α ls v => vC true A ls (δ.extend x α) v

/-- What the rest of a piece takes at each lend: the view if it holds `m`, else nothing. -/
def vwOf (l : BoCa.Loc) (T : VTy) (δ : LSub) (ml : Bool) : Life → List SRec → WProp :=
  if ml then viewP l T δ else fun _ _ => emp

/-- **A borrower piece.** `Δ, x ⊏ b; Γ, m : Mut 'x T ⊢ E : A` read with the lend re-lendable: at
every lend `α ⊏ @bδ`, from `𝒢⟦Γ, m⟧` at `δ[x ↦ α]` with `m ↦ ℓ`, a run with the lend open at
`α` whose stops owe `Open`. -/
def RBody (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (S : Row)
    (Γ : Ctx VTy) (ml : Bool) (E : Expr) (A : VTy) : Prop :=
  ∀ (δ : LSub), Δ.Models δ → ∀ (β : Life), b.interp δ = some β →
    ∀ (l : BoCa.Loc) (α : Life), α ⊏ β →
    ∀ (ls : List SRec) (γ : List Val) (ρ : WRes), γ.length = Γ.length →
      gDenC ls (δ.extend x α) (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ →
      bodyAt (opTable (Row.tab S δ)) l T δ (ansR x δ A)
        (Open (opTable (Row.tab S δ)) l T δ β (vwOf l T δ ml) (ansR x δ A)) α ls
        (substAll (γ ++ [Val.loc l]) E) ρ

theorem Row.Resume.linResume {S : Row} {x : LifeVar} (hS : Row.Resume S x) (δ : LSub) :
    LinResume (Row.tab S δ) := by
  intro n i en hT
  obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
  obtain ⟨ha, -, hq, -⟩ := hS o (Row.find_mem hf).1
  exact ⟨ha, hq⟩

section
variable {Tb : Table} {l : BoCa.Loc} {T : VTy} {δ : LSub} {β : Life}
  {Vw : Life → List SRec → WProp}

/-- `Open` is monotone in its answer. -/
theorem open_mono_Q (hTb : Tb.Mono) {Q Q' : Life → List SRec → Val → WProp}
    (hQ : ∀ α, α ⊏ β → ∀ ls v ρ, Q α ls v ρ → Q' α ls v ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Open Tb l T δ β Vw Q ls e ρ) : Open Tb l T δ β Vw Q' ls e ρ := by
  refine open_ind (fun ls e ρ => Open Tb l T δ β Vw Q' ls e ρ) (fun ls e ρ hF => ?_) h
  refine open_fold hTb fun α hα => box_mono (wand_mono_right fun σ hw => ?_) ρ (hF α hα)
  exact wpG_mono (fun _ _ _ hq => hq.imp (fun ⟨v, hv, hq⟩ => ⟨v, hv, hQ α hα _ _ _ hq⟩) id) hw

/-- A piece that does not hold the view runs where the view is handed: it is left behind. -/
theorem open_drop_view (hTb : Tb.Mono) (hVn : ∀ α ls ρ, Vw α ls ρ → NoOwn ρ)
    {Q : Life → List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Open Tb l T δ β (fun _ _ => emp) Q ls e ρ) : Open Tb l T δ β Vw Q ls e ρ := by
  refine open_ind (fun ls e ρ => Open Tb l T δ β Vw Q ls e ρ) (fun ls e ρ hF => ?_) h
  refine open_fold hTb fun α hα => ⟨fun ρv σ hv hcv => ?_, (hF α hα).2⟩
  have hb := (hF α hα).1 PMap.empty ρ ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
  exact wpG_garbage (wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hc, hq, hn⟩ => ⟨τ₁, τ₂, hc, hn, hq⟩)
    (wpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ h => h) σ ⟨ρ, ρv, hcv, hb, hVn α ls ρv hv⟩))

end

/-! ### Freezing and thawing a frame -/

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy}

theorem stopSafe_congr {Γ : Ctx VTy} (hs : StopSafe Δ x b Γ) (ls : List SRec) (δ : LSub)
    (α : Life) (γ : List Val) :
    gSepC ls δ (Γ ++ [mSlot x T false]) γ = gSepC ls (δ.extend x α) (Γ ++ [mSlot x T false]) γ :=
  gSepC_congr fun s hs' hl => by
    rcases List.mem_append.mp hs' with h | h
    · exact (vC_extend_of_not_free (hs s h hl).1 true ls δ α).symm
    · simp at h; subst h; simp at hl

/-- A frozen frame is in `[α]` at every lend `α ⊏ @bδ`, by 6.60. -/
theorem stopSafe_outlives {Γ : Ctx VTy} (hs : StopSafe Δ x b Γ) {δ : LSub} (hδ : Δ.Models δ)
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β) {ls : List SRec} {γ : List Val} {ρ : WRes}
    (h : gDenC ls δ (Γ ++ [mSlot x T false]) γ ρ) {α : Life} (hα : α ⊏ β) : ρ.InStratum α := by
  refine frame_outlives hδ hbx hΔx hβ (Γ' := Γ ++ [mSlot x T false]) ?_ ?_ (gDenC_iff.mp h).2 hα
  · intro s hs' hl
    rcases List.mem_append.mp hs' with h' | h'
    · exact (hs s h' hl).1
    · simp at h'; subst h'; simp at hl
  · intro s hs' hl
    rcases List.mem_append.mp hs' with h' | h'
    · exact (hs s h' hl).2
    · simp at h'; subst h'; simp at hl

/-- **Freeze a frame**: its view, if it holds `m`, is garbage, and the rest does not see `'x`. -/
theorem frame_freeze {Γ : Ctx VTy} (hs : StopSafe Δ x b Γ) (hT : ¬ VFree x T) {ml : Bool}
    {ls : List SRec} {δ : LSub} {α : Life} {γ : List Val} (hlen : γ.length = Γ.length)
    {l : BoCa.Loc} {ρ : WRes}
    (h : gDenC ls (δ.extend x α) (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ) :
    ∃ ρz ρn, ResU.CompS ρz ρn ρ ∧ gDenC ls δ (Γ ++ [mSlot x T false]) (γ ++ [Val.loc l]) ρz ∧
      NoOwn ρn := by
  obtain ⟨hlw, hg⟩ := gDenC_iff.mp h
  have hlw' := liveWithin_append Γ (mSlot x T false) γ (Val.loc l) hlen
  cases ml with
  | false =>
      refine ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, gDenC_mk hlw' ?_, noOwn_empty⟩
      rw [stopSafe_congr hs ls δ α]; exact hg
  | true =>
      obtain ⟨ρz, ρn, hc, hz, hn⟩ := gSepC_splitP (splitP_last (.mut (.var x) T) Γ) hg
      refine ⟨ρz, ρn, hc, gDenC_mk hlw' ?_, ?_⟩
      · rw [stopSafe_congr hs ls δ α]; exact hz
      · exact noOwn_ptoMutS (view_of_vC hT ((gSepC_dead_last Γ γ hlen).mp hn))

/-- **Thaw a frame** at a fresh lend: the view handed at `α′` is `m`'s, the rest as it stood. -/
theorem frame_thaw {Γ : Ctx VTy} (hs : StopSafe Δ x b Γ) (hT : ¬ VFree x T) {ml : Bool}
    {ls : List SRec} {δ : LSub} {α : Life} {γ : List Val} (hlen : γ.length = Γ.length)
    {l : BoCa.Loc} {ρv ρz ρ : WRes} (hv : vwOf l T δ ml α ls ρv)
    (hz : gDenC ls δ (Γ ++ [mSlot x T false]) (γ ++ [Val.loc l]) ρz)
    (hc : ResU.CompS ρv ρz ρ) :
    gDenC ls (δ.extend x α) (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ := by
  have hlw := liveWithin_append Γ (mSlot x T ml) γ (Val.loc l) hlen
  obtain ⟨-, hg⟩ := gDenC_iff.mp hz
  rw [stopSafe_congr hs ls δ α] at hg
  cases ml with
  | false =>
      obtain ⟨rfl, -⟩ := hv
      obtain rfl := eq_of_compS_empty_left hc
      exact gDenC_mk hlw hg
  | true =>
      refine gDenC_mk hlw (gSepC_joinP (splitP_last (.mut (.var x) T) Γ)
        ⟨ρz, ρv, ResU.CompS.comm hc, hg, (gSepC_dead_last Γ γ hlen).mpr (mutView hT hv)⟩)

end

/-! ### The rules -/

theorem substAll_cons_l (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

/-- A piece whose rest needs the view only if the whole's does. -/
theorem open_vwOf_le {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {β : Life} {ml ml' : Bool} (h : ml' = true → ml = true)
    {Q : Life → List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (hO : Open Tb l T δ β (vwOf l T δ ml') Q ls e ρ) : Open Tb l T δ β (vwOf l T δ ml) Q ls e ρ := by
  cases ml' with
  | true => rw [h rfl] at *; exact hO
  | false =>
      cases ml with
      | false => exact hO
      | true => exact open_drop_view hTb (fun _ _ _ hv => noOwn_ptoMutS hv) hO

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {S : Row}

/-- **A pure piece**, by `fundamentalC`'s semantic judgment at `δ[x ↦ α]`. -/
theorem rbody_ret (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ : Ctx VTy} {ml : Bool} {E : Expr} {A : VTy}
    (h : SemC (Δ.extend x b) (Γ ++ [mSlot x T ml]) E (.ret A)) : RBody Δ x b T S Γ ml E A := by
  intro δ hδ β hβ l α hα ls γ ρ _ hg
  exact bodyAt_of_wpTS (h (δ.extend x α) _ ls ρ (models_extend hδ hbx hΔx hβ hα) hg)

/-- **`perform`**: the stop. The argument is closed data, so its resource is in `[α]`; the owner
handed back goes to the continuation, which answers `()` at the next lend. -/
theorem rbody_perform (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hS : Row.Resume S x) {Γ : Ctx VTy} {V : Expr} {o : OpSig}
    (hf : Row.find S o.n o.i = some o)
    (h : SemV (Δ.extend x b) (Γ ++ [mSlot x T false]) V o.A) :
    RBody Δ x b T S Γ false (performE (opArgE o.n o.i V)) o.B := by
  intro δ hδ β hβ l α hα ls γ ρ _ hg
  obtain ⟨ha, -, hq, hoB, hAx, hAo⟩ := hS o (Row.find_mem hf).1
  have hTb := opTable_mono (Row.tab S δ)
  change wpG ls ((Kont.appR (.val (.prim .perform))
    (.pairR (Val.i32 o.n) (.pairR (Val.i32 o.i) .hole))).plug (substAll (γ ++ [Val.loc l]) V)) _ ρ
  refine wpG_bind_pure _ _ ls _ ρ (wpTS_mono (fun ls' v σ hv => ?_) ρ
    (h (δ.extend x α) _ ls ρ (models_extend hδ hbx hΔx hβ hα) hg))
  have hv' : vC true o.A ls' δ v σ := by rw [vC_extend_of_not_free hAx] at hv; exact hv
  refine wpG_here _ _ _ σ (Or.inr ⟨fun w ρa ρb hown hcab ρc ρd hTw hccd => ?_,
    vC_outlives (Δ := LifeCtx.empty) (a := .var x) (models_empty_any _)
      (interp_ext_self δ x α) (hAo _ _) true ls' v σ hv⟩)
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  refine Or.inl ⟨.hole, o.n, o.i, v, o.ent δ,
    pure_sep_mk ⟨rfl, rfl, by simp [Row.tab, hf], ha⟩ ⟨σ, s, hρs, hv', ?_⟩⟩
  refine ⟨fun hu => absurd (hq.symm.trans hu) (by decide),
    fun ls'' hext => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  have hBw' : vC true .unit ls'' δ w' τ₁ := by simpa [OpSig.ent, hoB] using hBw
  obtain ⟨rfl, rfl⟩ := hBw'
  have e : s = τ₂ := (ResU.CompS.functional hcτ (ResU.comp_empty_right s)).symm
  subst e
  refine ⟨s, PMap.empty, ResU.comp_empty_right s,
    ⟨w, ρa, ρc, hs, hown, vC_local true T (hext.right hs) hTw⟩, ?_⟩
  refine open_fold hTb fun α' _ => ⟨fun ρv σ' hv₀ hc' => ?_, ResU.inStratum_empty α'⟩
  obtain ⟨rfl, -⟩ := hv₀
  obtain rfl := eq_of_compS_empty_left hc'
  refine wpG_here _ _ _ _ (Or.inl ⟨Val.unit, rfl, ?_⟩)
  show vC true o.B ls'' (δ.extend x α') Val.unit PMap.empty
  rw [hoB]; exact ⟨rfl, rfl⟩

/-- **A frame that spans a stop thaws at a fresh lend.** For each closing substitution, a frozen
form `Fz` of the frame `Γ, m` exists: Kripke along `Ext`, in `[α]` at every lend `α ⊏ @bδ`. The
frame at a lend freezes to it, leaving garbage that owns nothing (its view, if any). The frozen
frame, with the view handed at a fresh lend if the frame holds `m`, is the frame at that lend.
This is what a stop asks of the values the frames around it hold. -/
def FrameThaws (Δ : LifeCtx) (x : LifeVar) (b : Lifetime.Life) (T : VTy) (Γ : Ctx VTy)
    (ml : Bool) : Prop :=
  ∀ (δ : LSub), Δ.Models δ → ∀ (β : Life), b.interp δ = some β →
    ∀ (l : BoCa.Loc) (γ : List Val), γ.length = Γ.length → ∃ Fz : List SRec → WProp,
      (∀ ls ls' ρ, Ext ls ls' ρ → Fz ls ρ → Fz ls' ρ) ∧
      (∀ ls ρ, Fz ls ρ → ∀ α, α ⊏ β → ρ.InStratum α) ∧
      (∀ α ls ρ, gDenC ls (δ.extend x α) (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ →
        ∃ ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz ls ρz ∧ NoOwn ρn) ∧
      (∀ α ls ρv ρz ρ, α ⊏ β → vwOf l T δ ml α ls ρv → Fz ls ρz → ResU.CompS ρv ρz ρ →
        gDenC ls (δ.extend x α) (Γ ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ρ)

/-- A frame whose slots other than `m` are free of `'x` and outlive it thaws (`frame_freeze`,
`frame_thaw`). -/
theorem stopSafe_thaws (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false) (hT : ¬ VFree x T)
    {Γ : Ctx VTy} (hs : StopSafe Δ x b Γ) (ml : Bool) : FrameThaws Δ x b T Γ ml := by
  intro δ hδ β hβ l γ hlen
  exact ⟨fun ls => gDenC ls δ (Γ ++ [mSlot x T false]) (γ ++ [Val.loc l]),
    fun _ _ _ he h => gDenC_local he h,
    fun _ _ h _ hα => stopSafe_outlives hs hδ hbx hΔx hβ h hα,
    fun _ _ _ h => frame_freeze hs hT hlen h,
    fun _ _ _ _ _ _ hv hz hc => frame_thaw hs hT hlen hv hz hc⟩

/-- **`M to z. N`.** `N`'s context is the frame `(λz. N) [·]` around `M`. It is carried through
`M`'s run, frozen at each of `M`'s stops, and thawed at each re-lend (`open_bind`), as
`FrameThaws` says. At `M`'s answer, `N` runs at the lend `M` answered at, from its own
judgment. -/
theorem rbody_letF (hS : Row.Resume S x) {Γ Γ₁ Γ₂ : Ctx VTy} {ml ml₁ ml₂ : Bool} {M N : Expr}
    {A₁ A : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γ₁ ++ [mSlot x T ml₁]) (Γ₂ ++ [mSlot x T ml₂]))
    (hl₁ : Γ₁.length = Γ.length) (hl₂ : Γ₂.length = Γ.length)
    (hml : ml₂ = true → ml = true ∧ ml₁ = false) (hml' : ml₂ = false → ml₁ = ml)
    (hsafe : FrameThaws Δ x b T Γ₂ ml₂)
    (hM : RBody Δ x b T S Γ₁ ml₁ M A₁) (hN : RBody Δ x b T S (⟨A₁, true⟩ :: Γ₂) ml₂ N A) :
    RBody Δ x b T S Γ ml (.app (.val (.lam N)) M) A := by
  intro δ hδ β hβ l α hα ls γ ρ hlen hg
  have hLR := hS.linResume δ
  have hTb := opTable_mono (Row.tab S δ)
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  have hlen₂ : γ.length = Γ₂.length := hlen.trans hl₂.symm
  obtain ⟨Fz, hFe, hFo, hfz, hth⟩ := hsafe δ hδ β hβ l γ hlen₂
  let K : Kont := .appR (.val (.lam (Expr.psub 1 (γ ++ [Val.loc l]) N))) .hole
  have hK : ∀ n, K.HasHnd n = false := fun n => by simp [K, Kont.HasHnd]
  let Fr : Life → List SRec → WProp := fun α' ls =>
    gDenC ls (δ.extend x α') (Γ₂ ++ [mSlot x T ml₂]) (γ ++ [Val.loc l])
  have hFs : ∀ α' ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α' ls) (Fr α' ls') :=
    fun _ _ _ hs _ h => gDenC_same hs h
  have hthaw : ∀ α' ls ρv ρz ρ, α' ⊏ β → vwOf l T δ ml α' ls ρv → Fz ls ρz →
      ResU.CompS ρv ρz ρ → ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vwOf l T δ ml₁ α' ls ρ₁ ∧ Fr α' ls ρ₂ := by
    intro α' ls' ρv ρz ρ' hα' hv hz hc'
    cases h₂ : ml₂ with
    | true =>
        obtain ⟨rfl, rfl⟩ := hml h₂
        refine ⟨PMap.empty, ρ', compS_empty_left ρ', ⟨rfl, trivial⟩, ?_⟩
        exact hth α' ls' ρv ρz ρ' hα' (by rw [h₂]; exact hv) hz hc'
    | false =>
        rw [hml' h₂]
        refine ⟨ρv, ρz, hc', hv, ?_⟩
        exact hth α' ls' PMap.empty ρz ρz hα' (by rw [h₂]; exact ⟨rfl, trivial⟩) hz
          (compS_empty_left ρz)
  have hk : ∀ α', α' ⊏ β → ∀ ls v, Entails (ansR x δ A₁ α' ls v ⋆ Fr α' ls)
      (bodyAt (opTable (Row.tab S δ)) l T δ (ansR x δ A)
        (Open (opTable (Row.tab S δ)) l T δ β (vwOf l T δ ml) (ansR x δ A)) α' ls
        (K.plug (.val v))) := by
    rintro α' hα' ls' v σ ⟨σ₁, σ₂, hcσ, hv, hfr⟩
    obtain ⟨hlw, hgs⟩ := gDenC_iff.mp hfr
    refine wpG_step (fun μ => Step1N.head (Head.beta μ _ v) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    have hb := hN δ hδ β hβ l α' hα' ls' (v :: γ) σ (by simp [hlen₂])
      (gDenC_mk hlw ⟨σ₁, σ₂, hcσ, hv, hgs⟩)
    exact bodyAt_mono hTb (fun _ _ _ h => open_vwOf_le hTb (fun h' => (hml h').1) h) σ hb
  have hfz' : ∀ α' ls ρ, Fr α' ls ρ → ∃ ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz ls ρz ∧ NoOwn ρn :=
    fun α' ls ρ h => hfz α' ls ρ h
  exact bodyAt_bind hLR K hK Fr Fz hFs hFe hFo hfz'
    (fun _ _ _ _ _ hx hz hcτ => open_bind hLR K hK Fr Fz hFs hFe hFo hfz' hthaw hk hx hz hcτ)
    hα (hk α hα) (hM δ hδ β hβ l α hα ls γ ρ₁ (hlen.trans hl₁.symm) hg₁) hg₂ hc

/-- `rbody_letF` at a frame whose slots other than `m` are free of `'x` and outlive it. -/
theorem rbody_let (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false) (hT : ¬ VFree x T)
    (hS : Row.Resume S x) {Γ Γ₁ Γ₂ : Ctx VTy} {ml ml₁ ml₂ : Bool} {M N : Expr} {A₁ A : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γ₁ ++ [mSlot x T ml₁]) (Γ₂ ++ [mSlot x T ml₂]))
    (hl₁ : Γ₁.length = Γ.length) (hl₂ : Γ₂.length = Γ.length)
    (hml : ml₂ = true → ml = true ∧ ml₁ = false) (hml' : ml₂ = false → ml₁ = ml)
    (hsafe : StopSafe Δ x b Γ₂)
    (hM : RBody Δ x b T S Γ₁ ml₁ M A₁) (hN : RBody Δ x b T S (⟨A₁, true⟩ :: Γ₂) ml₂ N A) :
    RBody Δ x b T S Γ ml (.app (.val (.lam N)) M) A :=
  rbody_letF hS hsp hl₁ hl₂ hml hml' (stopSafe_thaws hbx hΔx hT hsafe ml₂) hM hN

/-- **`case V {inj₁ z. M₁ | inj₂ z. M₂}`**: `V` runs pure, the branches' context a frame beside
it, and the branch taken runs at the same lend. -/
theorem rbody_case (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ Γs Γb : Ctx VTy} {ml mls mlb : Bool} {V M₁ M₂ : Expr} {A B C : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γs ++ [mSlot x T mls]) (Γb ++ [mSlot x T mlb]))
    (hlb : Γb.length = Γ.length) (hml : mlb = true → ml = true)
    (hV : SemV (Δ.extend x b) (Γs ++ [mSlot x T mls]) V (.sum A B))
    (h₁ : RBody Δ x b T S (⟨A, true⟩ :: Γb) mlb M₁ C)
    (h₂ : RBody Δ x b T S (⟨B, true⟩ :: Γb) mlb M₂ C) :
    RBody Δ x b T S Γ ml (.case V M₁ M₂) C := by
  intro δ hδ β hβ l α hα ls γ ρ hlen hg
  have hTb := opTable_mono (Row.tab S δ)
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  have hδα := models_extend hδ hbx hΔx hβ hα
  have hlenb : γ.length = Γb.length := hlen.trans hlb.symm
  refine wpG_bind_frame (.case .hole (Expr.psub 1 (γ ++ [Val.loc l]) M₁)
    (Expr.psub 1 (γ ++ [Val.loc l]) M₂)) _ ls (fun ls' => vC true (.sum A B) ls' (δ.extend x α))
    (fun ls' => gDenC ls' (δ.extend x α) (Γb ++ [mSlot x T mlb]) (γ ++ [Val.loc l])) _
    (fun _ hs _ h => gDenC_same hs h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV (δ.extend x α) _ ls ρ₁ hδα hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, hsum, hg₂'⟩
  obtain ⟨hlw, hgs⟩ := gDenC_iff.mp hg₂'
  rcases hsum with ⟨w, hs⟩ | ⟨w, hs⟩
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    refine wpG_step (fun μ => Step1N.head (Head.case₁ μ w _ _) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    exact bodyAt_mono hTb (fun _ _ _ h => open_vwOf_le hTb hml h) σ
      (h₁ δ hδ β hβ l α hα ls' (w :: γ) σ (by simp [hlenb]) (gDenC_mk hlw ⟨σ₁, σ₂, hcσ, hw, hgs⟩))
  · obtain ⟨rfl, hw⟩ := pure_sep_iff.mp hs
    refine wpG_step (fun μ => Step1N.head (Head.case₂ μ w _ _) rfl) ls' _ σ ?_
    rw [← substAll_cons_l]
    exact bodyAt_mono hTb (fun _ _ _ h => open_vwOf_le hTb hml h) σ
      (h₂ δ hδ β hβ l α hα ls' (w :: γ) σ (by simp [hlenb]) (gDenC_mk hlw ⟨σ₁, σ₂, hcσ, hw, hgs⟩))

/-- **`V; M`** for `V : 1`: `V` runs pure, `M`'s context a frame beside it, and `M` runs at the
same lend. -/
theorem rbody_seq (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {Γ Γ₁ Γ₂ : Ctx VTy} {ml ml₁ ml₂ : Bool} {V M : Expr} {A : VTy}
    (hsp : Ctx.SplitP (Γ ++ [mSlot x T ml]) (Γ₁ ++ [mSlot x T ml₁]) (Γ₂ ++ [mSlot x T ml₂]))
    (hl₂ : Γ₂.length = Γ.length) (hml : ml₂ = true → ml = true)
    (hV : SemV (Δ.extend x b) (Γ₁ ++ [mSlot x T ml₁]) V .unit)
    (hM : RBody Δ x b T S Γ₂ ml₂ M A) :
    RBody Δ x b T S Γ ml (.seq V M) A := by
  intro δ hδ β hβ l α hα ls γ ρ hlen hg
  have hTb := opTable_mono (Row.tab S δ)
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  have hδα := models_extend hδ hbx hΔx hβ hα
  refine wpG_bind_frame (.seq .hole (substAll (γ ++ [Val.loc l]) M)) _ ls
    (fun ls' => vC true .unit ls' (δ.extend x α))
    (fun ls' => gDenC ls' (δ.extend x α) (Γ₂ ++ [mSlot x T ml₂]) (γ ++ [Val.loc l])) _
    (fun _ hs _ h => gDenC_same hs h) ?_ ρ
    ⟨ρ₁, ρ₂, hc, hV (δ.extend x α) _ ls ρ₁ hδα hg₁, hg₂⟩
  rintro ls' - v σ ⟨σ₁, σ₂, hcσ, hu, hg₂'⟩
  obtain ⟨rfl, rfl⟩ := hu
  obtain rfl := eq_of_compS_empty_left hcσ
  refine wpG_step (fun μ => Step1N.head (Head.seq μ _) rfl) ls' _ _ ?_
  exact bodyAt_mono hTb (fun _ _ _ h => open_vwOf_le hTb hml h) _
    (hM δ hδ β hβ l α hα ls' γ _ (hlen.trans hl₂.symm) hg₂')

/-! ### The whole borrower -/

/-- A whole borrower `M`, `m` its only variable, is a piece holding the view. -/
theorem open_of_rbody (hT : ¬ VFree x T) {A : VTy} {M : Expr}
    {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (h : RBody Δ x b T S [] true M A) (l : BoCa.Loc) (ls : List SRec) :
    Open (opTable (Row.tab S δ)) l T δ β (viewP l T δ) (ansR x δ A) ls (substAll [Val.loc l] M)
      PMap.empty :=
  open_fold (opTable_mono _) fun α hα => ⟨fun ρm σ hm hc => by
    obtain rfl := eq_of_compS_empty_left hc
    exact h δ hδ β hβ l α hα ls [] _ rfl (gDenC_mk trivial (sep_emp_iff.mpr (mutView hT hm))),
    ResU.inStratum_empty α⟩

/-- A piece answering `['x] B` hands the owner back at its answer: it is `Relend`. -/
theorem relend_of_open_box {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {B : VTy}
    (hB : ¬ VFree x B) {δ : LSub} {β : Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Open Tb l T δ β (viewP l T δ) (ansR x δ (.box (.var x) B)) ls e ρ) :
    Relend Tb l T δ (finPost l T B δ) ls e ρ := by
  refine relend_of_open (β := β) hTb (open_mono_Q hTb ?_ h)
  intro α _ ls' v ρ hv
  obtain ⟨α', hα', hBr, hout⟩ := hv
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  refine ⟨fun w ρa ρb ha hcab ρc ρd hc hccd => ?_, hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  exact ⟨s, ρ, ResU.CompS.comm hρs, ⟨w, ρa, ρc, hs, ha, hc⟩,
    by rwa [vC_extend_of_not_free hB] at hBr⟩

/-- **A borrower is re-lendable.** `Δ, x ⊏ b; m : Mut 'x T ⊢ M : F_Σ(['x] B)` read as `RBody`: at
each lend the view is `m`, and the answer, boxed at the lend, hands the owner back. -/
theorem relend_of_rbody (hT : ¬ VFree x T) {B : VTy} (hB : ¬ VFree x B) {M : Expr}
    {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (h : RBody Δ x b T S [] true M (.box (.var x) B)) (l : BoCa.Loc) (ls : List SRec) :
    Relend (opTable (Row.tab S δ)) l T δ (finPost l T B δ) ls (substAll [Val.loc l] M)
      PMap.empty :=
  relend_of_open_box (opTable_mono _) hB (open_of_rbody hT hδ hβ h l ls)

/-- **O15.1's resume half for every borrower `RBody` reads.** As `withbor_of_relendOfTyped`,
from `relend_of_rbody` in place of `RelendOfTyped`. -/
theorem withbor_of_rbody {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β)
    (hT : ¬ VFree x T) {B : VTy} (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    (hSd : Row.divB S = false) {M : Expr} (hM : closedAt 1 M = true)
    (h : RBody Δ x b T S [] true M (.box (.var x) B)) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (cC (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam M), .lam⟩))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ hSd).mpr ?_
  exact withbor_relend (Row.tab S δ) (Row.tab_plainCancel S δ) hP _ v
    (relend_lam2 (opTable_mono _) hM (relend_of_rbody hT hB hδ hβ h l ls)) ρ hρ

end

end GhostEnd
