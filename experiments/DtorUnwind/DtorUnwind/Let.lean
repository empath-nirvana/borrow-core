import Core.Fundamental
import Core.Records

/-!
# Destructors on the unwind: `[let]` after resource CBPV

Congard, Munch-Maccagnoni and Douence, *Linear Effects, Exceptions, and Resource Safety* (ESOP
2026, arXiv 2510.23517v2), §4.3, translate the resource CBPV's `let` into the ordered calculus as

    ⟦let x = t in u⟧ ≝ let s = π₁⟦t⟧ in δ(s, x.⟦u⟧, e. raise_Γ(e))
    raise^P_Γ(e)    ≝ let e′ = unwind_Γ(e) in ι₂ e′
    unwind_{Γ,x:A}(e) ≝ … drop_A x; unwind_Γ(e)          drop_ctx_{Γ,x:A} ≝ drop_A x; drop_ctx_Γ

The continuation's context `Γ` is dropped, right to left, on the exceptional branch, and the error
is passed on unchanged. Our kernel has the pieces:

| paper | here |
|---|---|
| `δ(s, x.⟦u⟧, e. raise_Γ(e))`, the error case of the strength of `T(− ⊕ E)` | `thenE N D M`, the frame `ubind (λx. N, λ_. D)`; its machine step `[finalise]` is `ubind (N, D) K[raise p] ↦ D (); raise p` |
| `drop_A : 1 ⟜ A`, an object `A → T I` of `C/TI` | a λ-value `λx. b : A ⊸ F_{Σ_D} 1` typed in every dead context (`Dtors`) |
| `drop_ctx_Γ`, right to left | `dropCtxE ds k`: slot `k` (the most recently bound) first, then `k + 1`, … |
| `unwind_Γ(e)`, `e` returned unchanged | `[finalise]` re-raises `p` after `D ()` |
| destructors never fail | `¬ Σ_D.Cancels`: every operation of the destructors' row must resume |
| `E` carries no resources | `[raise]`'s `hd : o.A.OwnFree` (unchanged) |

`CDerives.effLetD` is the rule, derived from `[then]` (`CDerives.effThen`): no constructor is
added to `CDerives`, so `fundamentalC`, `adequacyC` and `adequacyD` are unchanged and cover it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Destructors for a context -/

/-- **A destructor for each slot of a context, at the row `Σ_D`.** A dead slot, or a live slot of
persistent type, needs none (`none`). A live slot of type `T` gets a λ-value `λx. b`, the paper's
`drop_T : 1 ⟜ T`, at `T ⊸ F_{Σ_D} 1` in every dead context: a closed function, an object of
`C/TI` with `T` the ambient row `Σ_D`. -/
inductive Dtors (Δ : LifeCtx) (SD : Row) : Ctx VTy → List (Option Expr) → Prop where
  | nil : Dtors Δ SD [] []
  /-- A consumed rest of the context needs no destructors. -/
  | tail {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Dtors Δ SD Γ []
  | dead {T : VTy} {Γ : Ctx VTy} {ds : List (Option Expr)} :
      Dtors Δ SD Γ ds → Dtors Δ SD (⟨T, false⟩ :: Γ) (none :: ds)
  | pers {T : VTy} {Γ : Ctx VTy} {ds : List (Option Expr)} (hT : T.Persistent) :
      Dtors Δ SD Γ ds → Dtors Δ SD (⟨T, true⟩ :: Γ) (none :: ds)
  | drop {T : VTy} {Γ : Ctx VTy} {ds : List (Option Expr)} {b : Expr}
      (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
        CDerives Δ Γ' (.val (.lam b)) (.comp (.arr T (CTy.effOf SD .unit)))) :
      Dtors Δ SD Γ ds → Dtors Δ SD (⟨T, true⟩ :: Γ) (some b :: ds)

/-- **`drop_ctx`**: the destructors of `ds` applied to the slots from `k` on, the slot `k` first.
In a context `Γ₂`, slot `0` is the variable bound last, so the slots are dropped in the reverse
order of their binding (last in, first out). Each application is bound, and its unit result is a
new slot `0`, so the next slot is at `k + 2`. -/
def dropCtxE : List (Option Expr) → Nat → Expr
  | [], _ => .val .unit
  | none :: ds, k => dropCtxE ds (k + 1)
  | some b :: ds, k => .app (.val (.lam (dropCtxE ds (k + 2)))) (.app (.val (.lam b)) (.var k))

/-- **Last in, first out**: the first destructor `drop_ctx` runs is the one of slot `k`, the
variable bound last; the rest run after it returns. -/
theorem dropCtxE_some (b : Expr) (ds : List (Option Expr)) (k : Nat) :
    dropCtxE (some b :: ds) k = bindE (.app (.val (.lam b)) (.var k)) (dropCtxE ds (k + 2)) :=
  rfl

/-! ### Context lemmas -/

theorem split_kill_append {X X₁ X₂ : Ctx VTy} (h : Ctx.Split X X₁ X₂) :
    ∀ P : Ctx VTy, Ctx.Split (P ++ X) (kill P ++ X₁) (P ++ X₂)
  | [] => h
  | ⟨_, true⟩ :: P => .right (split_kill_append h P)
  | ⟨_, false⟩ :: P => .dead (split_kill_append h P)

theorem soloP_kill_append {T : VTy} (Γ : Ctx VTy) :
    ∀ P : Ctx VTy, Ctx.SoloP (kill P ++ ⟨T, true⟩ :: kill Γ) P.length T
  | [] => .here (kill_dead Γ).toP
  | ⟨_, _⟩ :: P => .there (soloP_kill_append Γ P)

theorem deadP_append' {P Γ : Ctx VTy} (hP : Ctx.DeadP P) (hΓ : Ctx.DeadP Γ) :
    Ctx.DeadP (P ++ Γ) := by
  induction hP with
  | nil => exact hΓ
  | cons _ ih => exact .cons ih
  | drop hT _ ih => exact .drop hT ih

theorem deadP_snoc {P : Ctx VTy} (hP : Ctx.DeadP P) {s : Slot VTy}
    (hs : s.live = false ∨ s.ty.Persistent) : Ctx.DeadP (P ++ [s]) := by
  obtain ⟨T, l⟩ := s
  refine deadP_append' hP ?_
  cases l with
  | false => exact .cons .nil
  | true =>
      rcases hs with h | h
      · cases h
      · exact .drop h .nil

/-- A row whose every operation must resume has no unrestricted operation. -/
theorem Row.not_unr_of_not_cancels {S : Row} (h : ¬ S.Cancels) : ¬ S.Unr :=
  fun ⟨o, ho, hq⟩ => h ⟨o, ho, by rw [hq]; decide⟩

/-- A row whose every operation must resume has no unrestricted operation at any depth: a
capturable operation is not `lin`. -/
theorem Row.not_unrD_of_not_cancels {S : Row} (h : ¬ S.Cancels) : ¬ S.UnrD := by
  rintro ⟨o, ho, hq | ⟨hc, -⟩⟩
  · exact h ⟨o, ho, by rw [hq]; decide⟩
  · refine h ⟨o, ho, fun hl => ?_⟩
    simp [capB, hl] at hc

/-! ### `drop_ctx` is typed -/

/-- **`drop_ctx` is a `CDerives` derivation** at `F_{Σ_D} 1`, for a row of destructors that never
fail (`¬ Σ_D.Cancels`): each destructor is bound by `[let]` at `Σ_D`, whose `hW` is then vacuous,
so the slots not yet dropped may stay live across it. The prefix `P` is the part of the context
already consumed: dead slots and the units the destructors returned. -/
theorem dropCtx_derives {Δ : LifeCtx} {SD : Row} (hSD : ¬ SD.Cancels) :
    ∀ {Γ : Ctx VTy} {ds : List (Option Expr)}, Dtors Δ SD Γ ds →
      ∀ {P : Ctx VTy}, Ctx.DeadP P →
        CDerives Δ (P ++ Γ) (dropCtxE ds P.length) (.comp (CTy.effOf SD .unit))
  | _, _, .nil, P, hP => by
      simp only [List.append_nil, dropCtxE]
      exact .effSub (RowLe.nil SD) (.ret (.unitI hP))
  | _, _, .tail h, P, hP => by
      simp only [dropCtxE]
      exact .effSub (RowLe.nil SD) (.ret (.unitI (deadP_append' hP h.toP)))
  | ⟨T, false⟩ :: Γ, none :: ds, .dead hd, P, hP => by
      have ih := dropCtx_derives hSD hd (P := P ++ [⟨T, false⟩]) (deadP_snoc hP (.inl rfl))
      simpa [dropCtxE, List.append_assoc] using ih
  | ⟨T, true⟩ :: Γ, none :: ds, .pers hT hd, P, hP => by
      have ih := dropCtx_derives hSD hd (P := P ++ [⟨T, true⟩]) (deadP_snoc hP (.inr hT))
      simpa [dropCtxE, List.append_assoc] using ih
  | ⟨T, true⟩ :: Γ, some b :: ds, .drop hb hd, P, hP => by
      have hs : Ctx.Split (P ++ ⟨T, true⟩ :: Γ) (kill P ++ ⟨T, true⟩ :: kill Γ)
          (P ++ ⟨T, false⟩ :: Γ) := split_kill_append (.left (split_kill Γ)) P
      have ih := dropCtx_derives hSD hd (P := ⟨.unit, true⟩ :: (P ++ [⟨T, false⟩]))
        (.drop rfl (deadP_snoc hP (.inl rfl)))
      have hlen : (⟨VTy.unit, true⟩ :: (P ++ [⟨T, false⟩])).length = P.length + 2 := by simp
      rw [hlen] at ih
      simp only [List.cons_append, List.append_assoc] at ih
      show CDerives Δ (P ++ ⟨T, true⟩ :: Γ)
        (.app (.val (.lam (dropCtxE ds (P.length + 2)))) (.app (.val (.lam b)) (.var P.length)))
        (.comp (CTy.effOf SD .unit))
      refine .effLet (A := .unit) hs.toP (fun hc => absurd hc hSD)
        (fun hu => absurd hu (Row.not_unr_of_not_cancels hSD)) ?_ ih
      exact .app (split_kill _).toP (hb _ (kill_dead _)) (soloP_kill_append Γ P)

/-! ### The rule -/

/-- `let x = M in N` with the continuation's context dropped on the unwind:
`M then x. N unwind drop_ctx`, `drop_ctx` under `[then]`'s dead binder.  -/
def letDE (ds : List (Option Expr)) (N M : Expr) : Expr := thenE N (dropCtxE ds 1) M

/-- **`[let-dtor]`: `[let]` at any row, its continuation's context held across `M` with
destructors.** The paper's `let t` translation (§4.3) at `[then]`: the finaliser is `drop_ctx`
of the continuation's context `Γ₂`, so a raise in `M`, or a cancel of a continuation captured in
`M`, runs every live owned slot's destructor, last bound first, and passes the error on.

Against `[let]` (`CDerives.effLet`): `hW : Σ.Cancels → Γ₂.OwnFree` is gone, replaced by a
destructor for every live slot of `Γ₂` that is not persistent (`hds`), at a row `Σ_D ≤ Σ` whose
operations all resume (`hSDc`, destructors never fail) and which does not hold `Div` (`hSDd`).
`hfin` is `[then]`'s: the cancel row of each capturable operation and cancellable wait of `Σ`
records `Σ_D`, since a cancel there unwinds through the destructors. `hNZ`, `hUq` are `[then]`'s
conditions on the row. -/
theorem CDerives.effLetD {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S SD : Row} {ds : List (Option Expr)}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hDS : RowLe SD S) (hSDc : ¬ SD.Cancels) (hSDd : Row.divB SD = false)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hds : Dtors Δ SD Γ₂ ds)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (letDE ds N M) (.comp (CTy.effOf S B)) := by
  have hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) (dropCtxE ds 1) (.comp (CTy.effOf SD .unit)) :=
    dropCtx_derives hSDc hds (P := [⟨.unit, false⟩]) (.cons .nil)
  refine .effThen (SM := S) (SD := SD) hs hNZ hUq hU (RowLe.refl S) hDS ?_ ?_ hSDd hM hN hD
  · intro n i o o' hf hf' hr
    rw [hf] at hf'; cases hf'
    exact hfin n i o hf hr
  · exact fun h => absurd h (Row.not_unrD_of_not_cancels hSDc)

/-- **`[let-dtor]` is sound**: `fundamentalC` at its derivation, no hypothesis added. -/
theorem effLetD_sound {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S SD : Row} {ds : List (Option Expr)}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hDS : RowLe SD S) (hSDc : ¬ SD.Cancels) (hSDd : Row.divB SD = false)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hds : Dtors Δ SD Γ₂ ds)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    SemC Δ Γ (letDE ds N M) (CTy.effOf S B) :=
  fundamentalC (j := .comp _) (CDerives.effLetD hs hNZ hUq hU hDS hSDc hSDd hfin hds hM hN)

/-- `hfin` holds at a row with no capturable operation and no cancellable wait: every row of
errors and must-resume operations. -/
theorem hfin_of_noRead {S SD : Row} (h : ∀ o ∈ S, o.finRead = false) :
    ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin :=
  fun _ _ o hf hr => by rw [h o (Row.find_mem hf).1] at hr; cases hr

end BoCa.Fig16.LogRel.Core.DtorUnwind

end
