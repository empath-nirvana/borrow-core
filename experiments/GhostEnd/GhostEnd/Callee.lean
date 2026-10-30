import GhostEnd.ClosureBody
import GhostEnd.Branch

/-!
# GhostEnd — a closure that stops while holding the lend (#262, item 3, gap 2)

`Capture.lean` forces its closure by a pure piece, after the stop. A closure whose body itself
performs, called while it holds the lend, stops *inside the callee* with the lend's cell in the
callee's environment. `fundamentalC` reads such a closure through `𝒞⟦1 ⊸ F_Σ B⟧`, whose stops
are `ewpTS`'s: the continuation is owed `∀ w. PB(w) ─⋆ ewpTS(K[w])`, a wand over the callee's
whole share, the view among it. The ghost end needs that share split into the view and a part
in `[α]` (`stopAtD`), and a wand does not expose the split. So re-deriving the closure at `δ′`
through the kernel's relation does not reach the stop. Its body has to be read as a borrower
piece.

`CloL` is that reading of a closure value: applied to `()` at every later lend, handed the view
if it holds the cell, it is a piece with the lend open (`bodyAtD`), its stops owing `OpenD`. The
environment is fixed in the closure's resource, so the relation is uniform in the lend, and a
frame holding it freezes and thaws by restricting the lend.

* `cloL_of_rbodyC` (`[lam]` at an effectful arrow): a λ over the context, whose body is an
  `RBodyC` piece, is `CloL`. The environment is frozen as typed values (`tvg_freeze`) and
  thawed at each call's lend (`tvg_thaw`).
* `cloL_call` (`[app]`): calling a `CloL` closure is a piece at the lend of the call.
* `callee_spans_yields`: a borrower that packs `m` into such a closure, yields with the closure
  in its frame, then calls it, and the callee yields again with the lend inside it. Every
  hypothesis is discharged.

The relation is not `TV`: a `CloL` closure need not be in `𝒱⟦U(1 ⊸ F_Σ B)⟧` at any `δ[x ↦ α]`,
so `tv_sound` has no case for it, and a pure piece cannot be handed one through `fundamentalC`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **A closure read with the lend re-lendable.** Its resource is in `Res_α`. Applied to `()` at
every lend `α′ ⊑ α` below `β`, at every list `Ext`-above, and handed the view if it holds the
lend's cell, it runs with the lend open at `α′`. -/
def CloL (S : Row) (δ : LSub) (l : BoCa.Loc) (T : VTy) (Q : Life → List SRec → Val → WProp)
    (β α : Life) (d : Bool) (ls : List SRec) (f : Val) : WProp := fun ρ =>
  ρ.InStratum α ∧ ∀ ls', Ext ls ls' ρ → ∀ α', α' ≤ α → α' ⊏ β →
    (vwD l T δ d α' ls' ─⋆ bodyAtD (opTable (Row.tab S δ)) l T δ Q
      (OpenD (opTable (Row.tab S δ)) l T δ Q) α' ls' (.app (.val f) (.val Val.unit))) ρ

section
variable {S : Row} {δ : LSub} {l : BoCa.Loc} {T : VTy} {Q : Life → List SRec → Val → WProp}

theorem cloL_local {β α : Life} {d : Bool} {ls ls' : List SRec} {f : Val} {ρ : WRes}
    (he : Ext ls ls' ρ) (h : CloL S δ l T Q β α d ls f ρ) : CloL S δ l T Q β α d ls' f ρ :=
  ⟨h.1, fun ls'' he' => h.2 ls'' (he.trans he')⟩

/-- A closure frozen at `α` is one at every later lend. -/
theorem cloL_mono {β α α₀ : Life} (hle : α₀ ≤ α) {d : Bool} {ls : List SRec} {f : Val}
    {ρ : WRes} (h : CloL S δ l T Q β α d ls f ρ) : CloL S δ l T Q β α₀ d ls f ρ :=
  ⟨h.1.mono hle, fun ls' he α' hα' hβ => h.2 ls' he α' (le_trans hα' hle) hβ⟩

/-- **`[app]`**: calling a `CloL` closure is a piece at the lend of the call. -/
theorem cloL_call {β α : Life} (hα : α ⊏ β) {d : Bool} {ls : List SRec} {f : Val}
    {ρz ρv ρ : WRes} (h : CloL S δ l T Q β α d ls f ρz) (hv : vwD l T δ d α ls ρv)
    (hc : ResU.CompS ρz ρv ρ) :
    bodyAtD (opTable (Row.tab S δ)) l T δ Q (OpenD (opTable (Row.tab S δ)) l T δ Q) α ls
      (.app (.val f) (.val Val.unit)) ρ :=
  h.2 ls (Ext.refl ls ρz) α le_rfl hα ρv ρ hv hc

end

section
variable {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {S : Row}

/-- **`[lam]` at an effectful arrow.** `λu. N` over the context `Γ_f, m`, its body an `RBodyC`
piece with `u : 1` in front, is a `CloL` closure: the context freezes to its environment and
what it drops, and at each call's lend the environment thaws and the body runs. -/
theorem cloL_of_rbodyC (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false) (hT : ¬ VFree x T)
    {Γf : Ctx VTy} {ml : Bool} {N : Expr}
    {Ans : LSub → BoCa.Loc → Life → List SRec → Val → WProp}
    (hN : RBodyC Δ x b T S (⟨.unit, true⟩ :: Γf) ml N Ans)
    {δ : LSub} (hδ : Δ.Models δ) {β : Life} (hβ : b.interp δ = some β) {l : BoCa.Loc}
    {α : Life} (hα : α ⊏ β) {ls : List SRec} {γ : List Val} {ρ : WRes} (ht : TabAt l α ρ)
    (hg : TVG Δ x b T δ l false α (Γf ++ [mSlot x T ml]) (γ ++ [Val.loc l]) ls false ρ) :
    ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ vwD l T δ d α ls ρn ∧
      CloL S δ l T (Ans δ l) β α d ls (Val.lam (Expr.psub 1 (γ ++ [Val.loc l]) N)) ρz := by
  obtain ⟨d, ρz, ρn, hc, hz, hn⟩ :=
    tvg_freeze hT (models_extend hδ hbx hΔx hβ hα) hg rfl rfl ht
  refine ⟨d, ρz, ρn, hc, hn, tvg_inStratum hz rfl, fun ls' he α' hle hα' ρv σ hv hcv => ?_⟩
  obtain ⟨hσ, htσ⟩ := tvg_thaw hT hle (tvg_local he hz) rfl rfl ρv σ hv hcv
  refine wpG_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ σ ?_
  rw [← substAll_cons_l]
  exact hN δ hδ β hβ l α' hα' ls' (Val.unit :: γ) σ htσ
    (.live (.atomL (Or.inr ⟨by simp [VFree], .unit⟩) ⟨rfl, rfl⟩) hσ (by simp)
      (compS_empty_left σ))

end

theorem substAll_var_l {γ : List Val} {i : Nat} {v : Val} (hv : γ[i]? = some v) :
    substAll γ (.var i) = .val v := by
  show Expr.psub 0 γ (.var i) = _
  simp only [Expr.psub, if_neg (Nat.not_lt_zero i), Nat.sub_zero, hv, Val.shift_zero]

theorem tvg_length {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {T : VTy} {δ : LSub}
    {l : BoCa.Loc} : ∀ {fz α Γ γ ls d ρ}, TVG Δ x b T δ l fz α Γ γ ls d ρ →
      γ.length = Γ.length
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, _, _, .dead h => by simp [tvg_length h]
  | _, _, _, _, _, _, _, .live _ h _ _ => by simp [tvg_length h]

end GhostEnd

/-! ### The instance -/

namespace GhostEnd.Callee
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Step1N Head performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd.Instance (yieldOp)
open GhostEnd.Branch (mS deadOf deadPD hbx hΔx hS hT hf yieldE)

/-- The callee's last segment, `m` at index `2` past two dead units. -/
def nf₃ : Expr := bindE forget (bindE (.app (.var 0) (.var 3)) (.var 0))

/-- The callee's body: `perform yield 2 to u₂. u₂; u₀; N_f`, its argument `u₀`. -/
def calleeBody : Expr := bindE (yieldE 2) (.seq (.var 0) (.seq (.var 1) nf₃))

/-- After the caller's yield: `f u`. -/
def after : Expr := .app (.var 1) (.var 0)

/-- `return (λu₀. callee) to f. perform yield 1 to u. f u`. -/
def body : Expr := bindE (.val (.lam calleeBody)) (bindE (yieldE 1) after)

theorem d_nf₃ :
    CDerives Δ₁ [⟨.unit, false⟩, ⟨.unit, false⟩, mS true] nf₃
      (.comp (.ret (.box (.var 0) .unit))) :=
  .bind (.dead (.dead (.right .nil)))
    (.ret (.forgetMut (a := .var 0) (A := .unit) (.cons (.cons (.cons .nil)))))
    (.bind (.left (.dead (.dead (.left .nil))))
      (.app (.left (.dead (.dead (.right .nil)))) (.force (.here (.cons (.cons (.cons .nil)))))
        (.there (.there (.there (.here .nil)))))
      (.ret (.boxI (.var (.here (.cons (.cons (.cons (.cons .nil))))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit
          (.cons (.cons (.cons (.cons .nil))))))))

theorem d_tail :
    CDerives Δ₁ ([⟨.unit, true⟩, ⟨.unit, true⟩] ++ [mS true]) (.seq (.var 0) (.seq (.var 1) nf₃))
      (.comp (.ret (.box (.var 0) .unit))) :=
  .unitE (.left (.right (.right .nil))) (.var (.here (.cons (.cons .nil))))
    (.unitE (.dead (.left (.right .nil))) (.var (.there (.here (.cons .nil)))) d_nf₃)

abbrev RB (Γ : Ctx VTy) (ml : Bool) (E : Expr)
    (Ans : LSub → BoCa.Loc → Life → List SRec → Val → WProp) : Prop :=
  RBodyC LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit [yieldOp] Γ ml E Ans

abbrev Q₀ : LSub → BoCa.Loc → Life → List SRec → Val → WProp := ansRC 0 (.box (.var 0) .unit)

/-- The callee: it yields with the lend open, then uses `m`. -/
theorem rb_callee : RB [⟨.unit, true⟩] true calleeBody Q₀ :=
  rbodyC_let hbx hΔx hT hS (Γ₁ := [⟨.unit, false⟩]) (Γ₂ := [⟨.unit, true⟩]) (ml₁ := false)
    (ml₂ := true) (A₁ := yieldOp.B) (.right (.right .nil))
    (rbodyC_perform hbx hΔx hS hf (fundamentalC (.lit (.i32 2) (deadPD [.unit]))))
    (rbodyC_ret hbx hΔx (fundamentalC d_tail))

/-- **The caller.** It packs `m` into the callee, yields with the callee in its frame, and calls
it at the resumed lend; the callee yields again with the lend inside it. -/
theorem rb_body : RB [] true body Q₀ := by
  intro δ hδ β hβ l α hα ls γ ρ ht hg
  have hTb := opTable_mono (Row.tab [yieldOp] δ)
  have hLR := hS.linResume δ
  obtain rfl : γ = [] := by simpa using tvg_length hg
  -- the closure: the context, frozen, behind `λu₀`
  obtain ⟨d₀, ρz₀, ρn₀, hc₀, hv₀, hclo₀⟩ :=
    cloL_of_rbodyC hbx hΔx hT rb_callee hδ hβ hα ht (Γf := []) (γ := []) hg
  let f : Val := Val.lam (Expr.psub 1 ([] ++ [Val.loc l]) calleeBody)
  let Q := Q₀ δ l
  let Fr : Life → List SRec → WProp := fun α' ls ρ =>
    ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ vwD l .unit δ d α' ls ρn ∧
      CloL [yieldOp] δ l .unit Q β α' d ls f ρz
  let Fz : Life → Bool → List SRec → WProp := fun α' d ls =>
    CloL [yieldOp] δ l .unit Q β α' d ls f
  have hvw_same : ∀ {d α' ls ls' ρ}, (∀ x, x ∈ ls' ↔ x ∈ ls) → vwD l .unit δ d α' ls ρ →
      vwD l .unit δ d α' ls' ρ := by
    intro d α' ls ls' ρ hs h
    cases d with
    | false => exact h
    | true =>
        exact view_of_vC hT (vC_local true _ (ext_of_same hs ρ) (mutView hT h))
  have hFs : ∀ α' ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (Fr α' ls) (Fr α' ls') :=
    fun _ _ _ hs _ ⟨d, ρz, ρn, hc, hv, hcl⟩ =>
      ⟨d, ρz, ρn, hc, hvw_same hs hv, cloL_local (ext_of_same hs ρz) hcl⟩
  have hFe : ∀ α' d ls ls' ρ, Ext ls ls' ρ → Fz α' d ls ρ → Fz α' d ls' ρ :=
    fun _ _ _ _ _ he h => cloL_local he h
  have hFo : ∀ α' d ls ρ, Fz α' d ls ρ → ρ.InStratum α' := fun _ _ _ _ h => h.1
  have hfz : ∀ α', α' ⊏ β → ∀ ls ρ, Fr α' ls ρ →
      ∃ d ρz ρn, ResU.CompS ρz ρn ρ ∧ Fz α' d ls ρz ∧ dropC l d ρn :=
    fun _ _ _ _ ⟨d, ρz, ρn, hc, hv, hcl⟩ => ⟨d, ρz, ρn, hc, hcl, dropC_of_vwD hv⟩
  have hthaw : ∀ β' α' d₂ ls ρv ρz ρ, α' ⊏ β' → β' ≤ β → vwD l .unit δ d₂ α' ls ρv →
      Fz β' d₂ ls ρz → ResU.CompS ρv ρz ρ → Fr α' ls ρ :=
    fun _ _ d₂ _ ρv ρz _ hα' _ hv hz hc =>
      ⟨d₂, ρz, ρv, ResU.CompS.comm hc, hv, cloL_mono (le_of_lt hα') hz⟩
  let K : Kont := .appR (.val (.lam (Expr.psub 1 (f :: ([] ++ [Val.loc l])) after))) .hole
  have hK : ∀ n, K.HasHnd n = false := fun n => by simp [K, Kont.HasHnd]
  -- after the caller's yield: `f u`, the call at the resumed lend
  have hk : ∀ α', α' ⊏ β → ∀ ls v, Entails (ansTV LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit
      yieldOp.B δ l α' ls v ⋆ Fr α' ls)
      (bodyAtD (opTable (Row.tab [yieldOp] δ)) l .unit δ Q
        (OpenD (opTable (Row.tab [yieldOp] δ)) l .unit δ Q) α' ls (K.plug (.val v))) := by
    rintro α' hα' ls' v σ ⟨σ₁, σ₂, hcσ, ⟨hv, -⟩, ⟨d, ρz, ρn, hcf, hvw, hcl⟩⟩
    obtain ⟨rfl, rfl⟩ : v = Val.unit ∧ σ₁ = PMap.empty := by
      have hs := (tv_sound (models_extend hδ hbx hΔx hβ hα')).1 hv rfl rfl
      exact ⟨hs.2, hs.1⟩
    obtain rfl := eq_of_compS_empty_left hcσ
    refine wpG_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ _ ?_
    rw [← substAll_cons_l]
    have e : substAll (Val.unit :: f :: ([] ++ [Val.loc l])) after =
        .app (.val f) (.val Val.unit) := by
      show Expr.app (Expr.psub 0 _ (.var 1)) (Expr.psub 0 _ (.var 0)) = _
      rw [← substAll, ← substAll, substAll_var_l (i := 1) (v := f) rfl,
        substAll_var_l (i := 0) (v := Val.unit) rfl]
    rw [e]
    exact cloL_call hα' hcl hvw hcf
  -- the caller: `λu₀`'s value, then its yield with the closure in the frame
  change wpG ls (.app (.val (.lam (Expr.psub 1 ([] ++ [Val.loc l]) (bindE (yieldE 1) after))))
    (.val f)) _ ρ
  refine wpG_step (fun μ => Step1N.head (Head.beta μ _ f) rfl) ls _ ρ ?_
  rw [← substAll_cons_l]
  change wpG ls (K.plug (substAll ([f] ++ [Val.loc l]) (yieldE 1))) _ ρ
  have hy := rbodyC_perform (Γ := [⟨.unit, false⟩]) hbx hΔx hS hf
    (fundamentalC (.lit (.i32 1) (deadPD [.unit]))) δ hδ β hβ l α hα ls [f] PMap.empty
    (tabAt_empty l α) (.dead (.dead .nil))
  exact bodyAtD_bind hLR K hK Fr Fz hFs hFe hFo (hfz α hα)
    (fun d₁ d₂ _ _ _ _ _ hnd hx hz hcτ =>
      openD_bind hLR K hK β Fr Fz hFs hFe hFo hfz hthaw hk (le_of_lt hα) hnd hx hz hcτ)
    (hk α hα) hy ⟨d₀, ρz₀, ρn₀, hc₀, hv₀, hclo₀⟩ (compS_empty_left ρ)

/-- **A closure that stops while holding the lend.** From `ℓ ↦ v ⋆ 𝒱⟦1⟧(v)`, the program is in
`𝒞⟦F_{yield} (Ref 1 ⊗ 1)⟧`, at every assignment and record list. -/
theorem callee_spans_yields (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true .unit ls δ v)
      (cC (CTy.effOf [yieldOp] (.tensor (.ref .unit) .unit)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam body), .lam⟩))) := by
  have hδ : LifeCtx.empty.Models δ := fun x u h => by
    simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  obtain ⟨β, hβ⟩ : ∃ β, LifeCtx.empty.meetOfDom.interp δ = some β :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)
  refine withbor_of_rbodyC hδ hβ hT (by simp [VFree]) (βP := ⊤) ?_ (by decide) (by decide) rb_body l v ls
  intro ls w σ h
  rw [h.1]; exact ResU.inStratum_empty _

end GhostEnd.Callee
