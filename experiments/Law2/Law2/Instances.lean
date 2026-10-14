import Law2.Straight
import GhostEnd.Instance

/-!
# Law2 — acceptance instances, as corollaries of `law2_straight`

Each instance is `law2_straight` at a concrete mixed stack, every hypothesis discharged. The
continuation after the yield is a term Core's typing derives, closed by the lent places; its
context is rebuilt at each re-lend from the views the lenders make afresh (`runsAt_of_typed`).

* **A borrow-holding struct, reborrowed, across a yield** (depth 2): the struct `s` holds a borrow
  `Mut 'b 1` from outside; the generator lends `s` (`'x₁`) and reborrows it (`'x₂`), yields with
  both lends open, and uses the reborrow after the resume (`struct_reborrow_spans`). Stack
  `[s@'x₂ reborrow, s@'x₁]`.
* **Depth 3, mixed**: an `imm` lend of another place inside the two (`struct_imm_spans`). Stack
  `[p@'x₃ imm, s@'x₂ reborrow, s@'x₁]`.
* **A closure capturing the nested borrow, held across the yield** (`closure_reborrow_spans`): the
  program starts in the state after the closure is built — `yield; force f` with `f`, closed by the
  reborrow's view, substituted — at the two-entry stack. Its context is rebuilt by the hereditary
  typing of the closure (`HTV.thunkF`, `htv_sound`): the closure is re-derived at the re-lent
  reading. A program that builds a closure before a stop and calls it after is
  `closure_stops_spans` (`Law2/FragInstances.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd GhostEnd.Instance
open Law2

/-! ### The setting -/

/-- The struct's payload: a borrow `Mut 'b 1` of an outer place, `'b` the variable `5`. -/
abbrev TA : VTy := .mut (.var 5) .unit

/-- `'x₂ ⊏ 'x₁`, `'x₁ ⊏ ⊤`, `'b ⊏ ⊤`. -/
abbrev ΔA : LifeCtx := ((LifeCtx.empty.extend 5 .top).extend 1 .top).extend 2 (.var 1)

/-- The outer reading: `'b` at the lifetime `1`. -/
abbrev δA : LSub := LSub.empty.extend 5 1

/-- Every entry crosses every operation. -/
abbrev tt : UInt32 → Bool := fun _ => true

/-- The struct's lend, at `'x₁`. -/
abbrev e₁ (s : BoCa.Loc) : LEnt := ⟨s, 1, TA, .mut, tt⟩

/-- Its reborrow, at `'x₂`. -/
abbrev e₂ (s : BoCa.Loc) : LEnt := ⟨s, 2, TA, .mut, tt⟩

/-- An `imm` lend of another place, at `'x₃`. -/
abbrev eI (p : BoCa.Loc) (u : Val) : LEnt := ⟨p, 3, .unit, .imm u, tt⟩

/-- `return forget to fg. fg n to z. return z`: the reborrow's view `n` (index `0`) used once. -/
abbrev useE : Expr := nfEx

theorem d_useE :
    CDerives ΔA [⟨.mut (.var 2) TA, true⟩] useE (.comp (.ret (.box (.var 2) .unit))) :=
  .bind (.right .nil) (.ret (.forgetMut (a := .var 2) (A := TA) (.cons .nil)))
    (.bind (.left (.left .nil))
      (.app (.left (.right .nil)) (.force (.here (.cons .nil))) (.there (.here .nil)))
      (.ret (.boxI (.var (.here (.cons (.cons .nil))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (.cons .nil))))))

/-- `ΔA` holds at a reading with `'x₂ ⊏ 'x₁ ⊏ ⊤` read at the stack's lifetimes. -/
theorem models_A (δ : LSub) (h5 : δ.find? 5 = some 1) {α₂ α₁ : Life} (h21 : α₂ < α₁)
    (h1 : α₁ < ⊤) : ΔA.Models ((δ.extend 1 α₁).extend 2 α₂) := by
  intro x u hu
  simp only [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, Lifetime.assocFind] at hu
  split_ifs at hu with hx2 hx1 hx5
  · subst hx2; cases hu
    refine ⟨α₂, α₁, find?_extend_self _ _ _, ?_, h21⟩
    rw [Lifetime.Life.interp_var, find?_extend_ne _ _ (by decide), find?_extend_self]; rfl
  · subst hx1; cases hu
    refine ⟨α₁, 0, ?_, rfl, h1⟩
    rw [find?_extend_ne _ _ (by decide), find?_extend_self]; rfl
  · subst hx5; cases hu
    refine ⟨1, 0, ?_, rfl, show (0 : ℕ) < 1 from Nat.zero_lt_one⟩
    rw [find?_extend_ne _ _ (by decide), find?_extend_ne _ _ (by decide), h5]

/-- The struct's payload lies above the lifetime `2`: its cell is at `'b`'s lifetime `1` or
above. -/
theorem TA_stratum (ls : List SRec) (w : Val) (ρ : WRes)
    (h : vCE (ℍ := ℍ) none true TA ls δA w ρ) : ρ.InStratum (OrderDual.toDual 2) := by
  obtain ⟨α, hα, ℓ', hsep⟩ := h
  obtain ⟨-, b, u, σ, hσ, Q, hw, ls₀, hαb, rfl, -⟩ := pure_sep_iff.mp hsep
  have hα1 : α = 1 := by
    have : (Lifetime.Life.var 5).interp δA = some 1 := rfl
    rw [this] at hα; exact (Option.some.inj hα).symm
  subst hα1
  intro l ψ e
  obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
  exact (inStratum_iff_of_mut (CellU.kind_mutOf _ _ _ _ _ _) _).mpr
    (lt_of_lt_of_le (show (OrderDual.toDual 2 : Life) < OrderDual.toDual 1 by decide) hαb)

theorem Reb_e₂ (s : BoCa.Loc) : Reb (e₂ s) [e₁ s] := by simp [Reb]

theorem not_Reb_e₁ (s : BoCa.Loc) : ¬ Reb (e₁ s) [] := by simp [Reb]

/-- **The views a re-lend of `[s@'x₂, s@'x₁]` hands**: the reborrow's; the struct's own view is
shadowed by the reborrow. -/
theorem vwS_A {s : BoCa.Loc} {ls : List SRec} {α₂ α₁ : Life} {ρv : WRes}
    (h : vwS δA [] [e₂ s, e₁ s] [true, true] [α₂, α₁] ls ρv) : viewP s TA δA α₂ ls ρv := by
  obtain ⟨a, b, hc, ha, hb⟩ := h
  obtain ⟨b₁, b₂, hcb, hb₁, hb₂⟩ := hb
  have hb₁' : b₁ = PMap.empty := by
    simp only [vis, List.mem_singleton, decide_true, Bool.not_true, Bool.and_false, vwE] at hb₁
    exact hb₁.1
  have hb₂' : b₂ = PMap.empty := hb₂.1
  subst hb₁' hb₂'
  have hb : b = PMap.empty := eq_of_compS_empty_left hcb
  subst hb
  rw [ResU.CompS.functional hc (ResU.comp_empty_right a)]
  simpa [vis, vwE] using ha

/-- **The reborrow's context, rebuilt from the view at each re-lend.** -/
theorem ctx_A {s : BoCa.Loc} {ls : List SRec} {α₂ α₁ : Life} {ρv : WRes}
    (h : viewP s TA δA α₂ ls ρv) :
    gDenC (ℍ := ℍ) ls ((δA.extend 1 α₁).extend 2 α₂) [⟨.mut (.var 2) TA, true⟩] [Val.loc s] ρv := by
  have hv : ptoMutS s α₂ ls (fun ls₀ => vCE (ℍ := ℍ) none true TA ls₀ (δA.extend 1 α₁)) ρv := by
    have e : (fun ls₀ => vCE (ℍ := ℍ) none true TA ls₀ (δA.extend 1 α₁)) =
        (fun ls₀ => vCE (ℍ := ℍ) none true TA ls₀ δA) :=
      funext fun ls₀ =>
        vC_extend_of_not_free (by simp [VFree, Lifetime.Life.mentions]) true ls₀ δA α₁
    rw [e]; exact h
  refine pure_sep_mk trivial ?_
  unfold gSepC
  rw [if_pos rfl]
  exact ⟨ρv, PMap.empty, ResU.comp_empty_right ρv,
    mutView (x := 2) (by simp [VFree, Lifetime.Life.mentions]) hv, ⟨rfl, trivial⟩⟩

theorem hQ_box (σ : LStack) (αs : List Life) (ls : List SRec) (v : Val) (ρ : WRes)
    (_ : List.IsChain (· < ·) αs)
    (h : vCE (ℍ := ℍ) none true (.box (.var 2) .unit) ls (extS δA σ αs) v ρ) :
    boxTop αs ((fun _ v => ⌜v = Val.unit⌝ : List SRec → Val → WProp) ls v) ρ := by
  obtain ⟨α, -, ⟨rfl, hv⟩, -⟩ := h
  exact ⟨⟨rfl, hv⟩, fun a _ => ResU.inStratum_empty a⟩

/-- **A borrow-holding struct, reborrowed, held across a yield (depth 2).** The struct `s` holds a
borrow `Mut 'b 1` of an outer place; the generator lends `s` at `'x₁` and reborrows it at `'x₂`,
yields with both lends open, and after the resume uses the reborrow (`useE`, closed by `s`). From
the struct's owner, the generator's body is its `ewpTS` at the row `{yield}`, handing the owner back
and answering `()`. `law2_straight` at the stack `[s@'x₂ reborrow, s@'x₁]`. -/
theorem struct_reborrow_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (chain yieldOp.n yieldOp.i [Val.i32 1] (substAll [Val.loc s] useE))
        (opTable (Row.tab [yieldOp] δA)) (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) := by
  intro ρ ho
  have hσ : MixedStack [e₂ s, e₁ s] :=
    .reborrow rfl rfl rfl rfl (.mutOther rfl (by simp) .nil)
  have hx : AllCross [e₂ s, e₁ s] (Row.tab [yieldOp] δA) := fun n i en _ e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  have hE : RunsAt (ℍ := ℍ) δA [e₂ s, e₁ s] [true, true] (fun _ v => ⌜v = Val.unit⌝)
      (substAll [Val.loc s] useE) := by
    refine runsAt_of_typed d_useE (fun αs ls' hlen hch htop ρv hv => ?_)
      (fun αs ls' v ρ' hch h => hQ_box _ αs ls' v ρ' hch h)
    match αs, hlen with
    | [α₂, α₁], _ =>
      have h21 : α₂ < α₁ := List.isChain_pair.mp hch
      exact ⟨models_A δA rfl h21 (htop α₁ (by simp)), ρv, PMap.empty,
        ResU.comp_empty_right ρv, noOwn_empty, ctx_A (vwS_A hv)⟩
  have ho' : ownersM (ℍ := ℍ) δA [e₂ s, e₁ s] ls ρ := by
    refine ⟨PMap.empty, ρ, compS_empty_left ρ, ?_, ρ, PMap.empty, ResU.comp_empty_right ρ, ?_,
      ⟨rfl, trivial⟩⟩
    · rw [if_pos (Reb_e₂ s)]; exact ⟨rfl, trivial⟩
    · rw [if_neg (not_Reb_e₁ s)]; exact ho
  have h := law2_straight (yield_linResume δA) (yield_local δA) (β := OrderDual.toDual 2) hσ hx
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact TA_stratum)
    (fun e he v hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> cases hk)
    (n := yieldOp.n) (i := yieldOp.i) (en := yieldOp.ent δA)
    (by simp [Row.tab, Row.find, yieldOp]) rfl rfl (yield_PB δA)
    (fun _ _ _ _ _ h => h) hE (ys := [Val.i32 1])
    (fun y hy ls => by
      simp only [List.mem_singleton] at hy; subst hy; exact ⟨rfl, 1, rfl⟩)
    (bs := [OrderDual.toDual 4, OrderDual.toDual 3]) rfl rfl
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> decide) ls ho'
  have hw : withOwnersM (ℍ := ℍ) δA [e₂ s, e₁ s] (fun _ v => ⌜v = Val.unit⌝) =
      fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝ := by
    simp only [withOwnersM, if_pos (Reb_e₂ s), if_neg (not_Reb_e₁ s)]; rfl
  rw [hw] at h
  exact h

/-! ### Depth 3: an `imm` lend inside the two -/

/-- `ΔA` holds at a reading that also binds `'x₃`, which `ΔA` does not mention. -/
theorem models_B (δ : LSub) (h5 : δ.find? 5 = some 1) {α₃ α₂ α₁ : Life} (h21 : α₂ < α₁)
    (h1 : α₁ < ⊤) : ΔA.Models (((δ.extend 1 α₁).extend 2 α₂).extend 3 α₃) := by
  intro x u hu
  obtain ⟨m, n, hm, hn, hlt⟩ := models_A δ h5 h21 h1 x u hu
  have hx : x ≠ 3 := by
    intro e; subst e
    simp [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, Lifetime.assocFind] at hu
  refine ⟨m, n, by rw [find?_extend_ne _ _ (Ne.symm hx)]; exact hm, ?_, hlt⟩
  have hu' : ∀ y, u.mentions y = true → y ≠ 3 := by
    intro y hy e; subst e
    simp only [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, Lifetime.assocFind] at hu
    split_ifs at hu <;> cases hu <;> simp [Lifetime.Life.mentions] at hy
  rw [← hn]
  exact interp_congr u fun y hy => find?_extend_ne _ _ (Ne.symm (hu' y hy))

/-- The views a re-lend of `[s@'x₂, s@'x₁]` hands when the places `seen` inside them are not
`s`: the reborrow's. -/
theorem vwS_A' {s : BoCa.Loc} {seen : List BoCa.Loc} (hs : s ∉ seen) {ls : List SRec}
    {α₂ α₁ : Life} {ρv : WRes}
    (h : vwS δA seen [e₂ s, e₁ s] [true, true] [α₂, α₁] ls ρv) : viewP s TA δA α₂ ls ρv := by
  obtain ⟨a, b, hc, ha, hb⟩ := h
  obtain ⟨b₁, b₂, hcb, hb₁, hb₂⟩ := hb
  have hb₁' : b₁ = PMap.empty := by
    simp only [vis, List.mem_cons, true_or, decide_true, Bool.not_true, Bool.and_false,
      vwE] at hb₁
    exact hb₁.1
  have hb₂' : b₂ = PMap.empty := hb₂.1
  subst hb₁' hb₂'
  have hb : b = PMap.empty := eq_of_compS_empty_left hcb
  subst hb
  rw [ResU.CompS.functional hc (ResU.comp_empty_right a)]
  simpa [vis, vwE, hs] using ha

theorem not_Reb_eI {s p : BoCa.Loc} (hne : p ≠ s) (u : Val) : ¬ Reb (eI p u) [e₂ s, e₁ s] := by
  simp [Reb, Ne.symm hne]

/-- **Depth 3, mixed: an `imm` lend of another place inside the reborrowed struct, across a
yield.** The generator lends `s` at `'x₁`, reborrows it at `'x₂`, lends `p` `imm` at `'x₃`, yields
with the three lends open, and after the resume uses the reborrow. `law2_straight` at the stack
`[p@'x₃ imm, s@'x₂ reborrow, s@'x₁]`; the `imm` view is dropped by the continuation. -/
theorem struct_imm_spans (s p : BoCa.Loc) (hne : p ≠ s) (u : Val) (ls : List SRec) :
    Entails (owner s TA δA ls ⋆ ownerI p u .unit δA ls)
      (ewpTS (ℍ := ℍ) ls (chain yieldOp.n yieldOp.i [Val.i32 1] (substAll [Val.loc s] useE))
        (opTable (Row.tab [yieldOp] δA))
        (fun ls v => owner s TA δA ls ⋆ (ownerI p u .unit δA ls ⋆ ⌜v = Val.unit⌝))) := by
  rintro ρ ⟨ρs, ρp, hcρ, hos, hop⟩
  have hσ : MixedStack [eI p u, e₂ s, e₁ s] :=
    .immOther rfl (by simp [hne]) (.reborrow rfl rfl rfl rfl (.mutOther rfl (by simp) .nil))
  have hx : AllCross [eI p u, e₂ s, e₁ s] (Row.tab [yieldOp] δA) := fun n i en _ e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rfl
  have hE : RunsAt (ℍ := ℍ) δA [eI p u, e₂ s, e₁ s] [true, true, true]
      (fun _ v => ⌜v = Val.unit⌝) (substAll [Val.loc s] useE) := by
    refine runsAt_of_typed d_useE (fun αs ls' hlen hch htop ρv hv => ?_)
      (fun αs ls' v ρ' hch h => hQ_box _ αs ls' v ρ' hch h)
    match αs, hlen with
    | [α₃, α₂, α₁], _ =>
      have h21 : α₂ < α₁ := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hch).2).1
      obtain ⟨ρi, ρm, hci, hi, hm⟩ := hv
      have hm' : viewP s TA δA α₂ ls' ρm := vwS_A' (seen := [p]) (by simp [Ne.symm hne]) hm
      have hi' : NoOwn ρi := by
        simp only [vis, List.not_mem_nil, decide_false, Bool.not_false, Bool.and_true, vwE] at hi
        exact noOwn_ptoImmS hi
      refine ⟨models_B δA rfl h21 (htop α₁ (by simp)), ρm, ρi, ResU.CompS.comm hci, hi', ?_⟩
      have hA := ctx_A (ℍ := ℍ) (α₁ := α₁) hm'
      obtain ⟨hl, hg⟩ := pure_sep_iff.mp hA
      refine pure_sep_mk hl ?_
      show gSepC ls' (((δA.extend 1 α₁).extend 2 α₂).extend 3 α₃) _ _ ρm
      rw [gSepC_congr (δ₁ := ((δA.extend 1 α₁).extend 2 α₂).extend 3 α₃)
        (δ₂ := (δA.extend 1 α₁).extend 2 α₂) (fun sl hsl _ => ?_)]
      · exact hg
      · simp only [List.mem_singleton] at hsl; subst hsl
        exact vC_extend_of_not_free (by simp [VFree, Lifetime.Life.mentions]) true ls' _ α₃
  have ho' : ownersM (ℍ := ℍ) δA [eI p u, e₂ s, e₁ s] ls ρ := by
    refine ⟨ρp, ρs, ResU.CompS.comm hcρ, ?_, PMap.empty, ρs, compS_empty_left ρs, ?_, ρs,
      PMap.empty, ResU.comp_empty_right ρs, ?_, ⟨rfl, trivial⟩⟩
    · rw [if_neg (not_Reb_eI hne u)]; exact hop
    · rw [if_pos (Reb_e₂ s)]; exact ⟨rfl, trivial⟩
    · rw [if_neg (not_Reb_e₁ s)]; exact hos
  have h := law2_straight (yield_linResume δA) (yield_local δA) (β := OrderDual.toDual 2) hσ hx
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · intro ls w ρ h; rw [h.1]; exact ResU.inStratum_empty _
      · exact TA_stratum
      · exact TA_stratum)
    (fun e he v hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact fun x hx => absurd hx (by simp [VFree])
      · cases hk
      · cases hk)
    (n := yieldOp.n) (i := yieldOp.i) (en := yieldOp.ent δA)
    (by simp [Row.tab, Row.find, yieldOp]) rfl rfl (yield_PB δA)
    (fun _ _ _ _ _ h => h) hE (ys := [Val.i32 1])
    (fun y hy ls => by
      simp only [List.mem_singleton] at hy; subst hy; exact ⟨rfl, 1, rfl⟩)
    (bs := [OrderDual.toDual 5, OrderDual.toDual 4, OrderDual.toDual 3]) rfl rfl
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide) ls ho'
  have hw : withOwnersM (ℍ := ℍ) δA [eI p u, e₂ s, e₁ s] (fun _ v => ⌜v = Val.unit⌝) =
      fun ls v => owner s TA δA ls ⋆ (ownerI p u .unit δA ls ⋆ ⌜v = Val.unit⌝) := by
    simp only [withOwnersM, if_neg (not_Reb_eI hne u), if_pos (Reb_e₂ s),
      if_neg (not_Reb_e₁ s)]; rfl
  rw [hw] at h
  exact h

/-! ### A closure capturing the nested borrow, held across the yield -/

/-- The closure's body, under its dead unit binder: `return forget to fg. fg n to z. return z`,
`n` the reborrow's view at index `1`. -/
abbrev MC : Expr := bindE forget (bindE (.app (.var 0) (.var 2)) (.var 0))

theorem d_MC :
    CDerives ΔA [⟨.unit, false⟩, ⟨.mut (.var 2) TA, true⟩] MC
      (.comp (.ret (.box (.var 2) .unit))) :=
  .bind (.dead (.right .nil)) (.ret (.forgetMut (a := .var 2) (A := TA) (.cons (.cons .nil))))
    (.bind (.left (.dead (.left .nil)))
      (.app (.left (.dead (.right .nil))) (.force (.here (.cons (.cons .nil))))
        (.there (.there (.here .nil))))
      (.ret (.boxI (.var (.here (.cons (.cons (.cons .nil)))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit (.cons (.cons (.cons .nil)))))))

/-- The type of the closure: `U (F ['x₂] 1)`. -/
abbrev CC : CTy := .ret (.box (.var 2) .unit)

/-- The closure, its environment the struct's place: `thunk MC` closed by `n := s`. -/
abbrev fC (s : BoCa.Loc) : Val := ⟨.lam (Expr.psub 1 [Val.loc s] MC), .lam⟩

/-- `force f`, `f` at index `0`. -/
abbrev EC : Expr := forceE CC (.var 0)

theorem d_EC : CDerives ΔA [⟨.thunk CC, true⟩] EC (.comp CC) := .force (.here .nil)

/-- **A closure capturing the nested borrow, held across the yield.** The program is the state
after the closure is built: `yield; force f`, with `f = thunk (… n …)` over the reborrow's view
substituted for the frame's variable. It yields with the two-entry stack open and `f` in its
frame, and after the resume forces `f`. The continuation's context, `f`, is rebuilt at each re-lend
by the closure's hereditary typing (`HTV.thunkF`): the closure is re-derived at the re-lent
reading, its environment the view made afresh. `law2_straight` at the stack
`[s@'x₂ reborrow, s@'x₁]`. -/
theorem closure_reborrow_spans (s : BoCa.Loc) (ls : List SRec) :
    Entails (owner s TA δA ls)
      (ewpTS (ℍ := ℍ) ls (chain yieldOp.n yieldOp.i [Val.i32 1] (substAll [fC s] EC))
        (opTable (Row.tab [yieldOp] δA)) (fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝)) := by
  intro ρ ho
  have hσ : MixedStack [e₂ s, e₁ s] :=
    .reborrow rfl rfl rfl rfl (.mutOther rfl (by simp) .nil)
  have hx : AllCross [e₂ s, e₁ s] (Row.tab [yieldOp] δA) := fun n i en _ e he => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  have hE : RunsAt (ℍ := ℍ) δA [e₂ s, e₁ s] [true, true] (fun _ v => ⌜v = Val.unit⌝)
      (substAll [fC s] EC) := by
    refine runsAt_of_typed d_EC (fun αs ls' hlen hch htop ρv hv => ?_)
      (fun αs ls' v ρ' hch h => hQ_box _ αs ls' v ρ' hch h)
    match αs, hlen with
    | [α₂, α₁], _ =>
      have h21 : α₂ < α₁ := List.isChain_pair.mp hch
      have hmod := models_A δA rfl h21 (htop α₁ (by simp))
      have hA := ctx_A (ℍ := ℍ) (α₁ := α₁) (vwS_A hv)
      obtain ⟨-, hg⟩ := pure_sep_iff.mp hA
      unfold gSepC at hg
      rw [if_pos rfl] at hg
      obtain ⟨ρn, ρe, hcn, hn, he⟩ := hg
      have he' : ρe = PMap.empty := he.1
      subst he'
      have hn' : vCE (ℍ := ℍ) none true (.mut (.var 2) TA) [] ((δA.extend 1 α₁).extend 2 α₂)
          (Val.loc s) ρn := by
        rw [vC_ls (.mut (.var 2) TA) (by simp [FOV]) [] ls']; exact hn
      have hclo : HTV (ℍ := ℍ) (.thunk CC) ((δA.extend 1 α₁).extend 2 α₂) (fC s) ρn :=
        .thunkF d_MC hmod trivial (.live rfl (.fo (by simp [FOV]) hn') .nil
          (ResU.comp_empty_right ρn))
      refine ⟨hmod, ρn, PMap.empty, hcn, noOwn_empty, ?_⟩
      refine pure_sep_mk trivial ?_
      unfold gSepC
      rw [if_pos rfl]
      exact ⟨ρn, PMap.empty, ResU.comp_empty_right ρn, htv_sound hclo ls', ⟨rfl, trivial⟩⟩
  have ho' : ownersM (ℍ := ℍ) δA [e₂ s, e₁ s] ls ρ := by
    refine ⟨PMap.empty, ρ, compS_empty_left ρ, ?_, ρ, PMap.empty, ResU.comp_empty_right ρ, ?_,
      ⟨rfl, trivial⟩⟩
    · rw [if_pos (Reb_e₂ s)]; exact ⟨rfl, trivial⟩
    · rw [if_neg (not_Reb_e₁ s)]; exact ho
  have h := law2_straight (yield_linResume δA) (yield_local δA) (β := OrderDual.toDual 2) hσ hx
    (fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> exact TA_stratum)
    (fun e he v hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> cases hk)
    (n := yieldOp.n) (i := yieldOp.i) (en := yieldOp.ent δA)
    (by simp [Row.tab, Row.find, yieldOp]) rfl rfl (yield_PB δA)
    (fun _ _ _ _ _ h => h) hE (ys := [Val.i32 1])
    (fun y hy ls => by
      simp only [List.mem_singleton] at hy; subst hy; exact ⟨rfl, 1, rfl⟩)
    (bs := [OrderDual.toDual 4, OrderDual.toDual 3]) rfl rfl
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> decide) ls ho'
  have hw : withOwnersM (ℍ := ℍ) δA [e₂ s, e₁ s] (fun _ v => ⌜v = Val.unit⌝) =
      fun ls v => owner s TA δA ls ⋆ ⌜v = Val.unit⌝ := by
    simp only [withOwnersM, if_pos (Reb_e₂ s), if_neg (not_Reb_e₁ s)]; rfl
  rw [hw] at h
  exact h

/-! ### A closure capturing a borrow of a borrow of a borrow, re-lent -/

/-- `Mut 'a (Mut 'b (Mut 'c 1))`. -/
abbrev mmm : VTy := .mut (.var 0) (.mut (.var 1) (.mut (.var 2) .unit))

/-- `thunk (return x)`, `x` the captured variable. -/
abbrev cloE : Expr := .val (.lam (.var 1))

theorem d_cloE : CDerives LifeCtx.empty [⟨mmm, true⟩] cloE (.comp (.ret (.thunk (.ret mmm)))) :=
  .ret (.thunkF (.ret (.var (.there (.here .nil)))))

/-- **A closure capturing a borrow of a borrow of a borrow re-lends**, at every re-making of the
region (every lifetime of `mmm` moved, at any depth): the thunk `λ_. return x` closed by a value of
`mmm` is related at `U (F mmm)` at the moved reading, at a re-make of the captured resource.
`relend_derivable` (Core's typing derives the thunk over a first-order context). -/
theorem closure_captures_mmm {c : Life} (θ : Restrat.Emb c) {δ : LSub} {v : Val}
    {ls : List SRec} {ρ : WRes} (hg : gDenC (ℍ := ℍ) ls δ [⟨mmm, true⟩] [v] ρ)
    (ls' : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧
      cC (ℍ := ℍ) (.ret (.thunk (.ret mmm))) ls' (mv θ δ) (substAll [v] cloE) ρ' :=
  relend_derivable θ d_cloE
    (fun s hs _ => by simp only [List.mem_singleton] at hs; subst hs; simp [FOV])
    (fun x u hu => by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at hu) hg ls'

end Law2.Inst

end
