import Core.Fundamental
import Core.Records
import Core.Dtor

/-!
# Core — `[let-dtor]`: effectful destructors on every exit  `[spec §62]`

`[let]` (`CDerives.effLet`) keeps the continuation's context `Γ₂` live across `M` only where `M`'s
row cannot abort or every live slot of `Γ₂` is own-free (`hW`). `[let-dtor]` lifts that refusal:
each live slot of `Γ₂` that is not persistent carries a **destructor**, a closed function
`λx. b : T ⊸ F_{Σ_D} 1` that may perform operations of a row `Σ_D ≤ Σ`, and the term is
`M then x. N unwind drop_ctx`, with `drop_ctx` running those destructors, the slot bound last
first. So every exit of `M` runs the live context's destructors in reverse order of binding:

| exit of `M` | what runs `drop_ctx` |
|---|---|
| return | `N` itself (it owns `Γ₂`) |
| raise | `[finalise]`: `ubind (N, D) K[raise p] ↦ D (); raise p` (`letDE_finalise`) |
| cancel (a raise of name `0`, a resume with *cancelled*) | `[finalise-cancel]` (`letDE_finaliseCancel`) |
| early close of a loop | the step's *close*, the state's destructor (`Core/LetDtorLoop.lean`) |

After Congard, Munch-Maccagnoni and Douence (*Linear Effects, Exceptions, and Resource Safety*,
ESOP 2026, §4.3), whose translation of the resource CBPV's `let` is
`let s = π₁⟦t⟧ in δ(s, x.⟦u⟧, e. raise_Γ(e))` with `raise_Γ(e)` dropping `Γ` right to left:

| paper | here |
|---|---|
| `δ(s, x.⟦u⟧, e. raise_Γ(e))` | `thenE N D M`, the frame `ubind (λx. N, λ_. D)` |
| `drop_A : 1 ⟜ A`, an object `A → T I` of `C/TI` | `λx. b : A ⊸ F_{Σ_D} 1` typed in every dead context (`Dtors`) |
| `drop_ctx_Γ`, right to left | `dropCtxE ds k`: slot `k` (the variable bound last) first |
| `unwind_Γ(e)`, `e` passed on unchanged | `[finalise]` re-raises `p` after `D ()` |
| destructors never fail | `¬ Σ_D.Cancels` |
| `E` carries no resources | `[raise]`'s `hd : o.A.OwnFree` |

**A derived form, not a constructor.** `[let-dtor]` is `[then]` (`CDerives.effThen`) at the
finaliser `drop_ctx`, which is itself a `CDerives` derivation (`dropCtx_derives`). So no
constructor is added to `CDerives`: `fundamentalC`, `adequacyC` and `adequacyD` cover it with no
new compatibility lemma, and every induction over `CDerives` (`CDerivesAt`, `CDerivesP`, `Tied`,
`PinDerives`, the totality results) already has its case, `[then]`'s.

**The premises and their reasons.**
- `hSDc : ¬ Σ_D.Cancels`: a destructor does not fail. Each destructor is bound by `[let]` at
  `Σ_D` inside `drop_ctx`, with the slots not yet dropped live across it; a destructor that
  raised would abandon them, which `[let]`'s `hW` refuses.
- `hSDd : Σ_D` does not hold `Div`: `[then]`'s finaliser terminates (decision 69). A cancel run
  is a least fixed point and reaches the finaliser; a finaliser that loops would leave it.
  `CDerives.effLetDDiv` drops `hSDd` when `M`'s row captures nothing.
- `hfin`: the cancel row of each capturable operation and cancellable wait of `Σ` records `Σ_D`
  (`[then]`'s `hfin`): a cancel there unwinds through the destructors, which may perform `Σ_D`.

`[let]` itself is unchanged: its term `M to x. N` has no unwind frame, so a raise in `M` would
abandon `Γ₂`, and `hW` stays its side condition. A context whose live slots all have derived drops
(§12, `HasDtor`) gets its destructors from `dtorE` (`Dtors.ofHasDtor`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Destructors for a context -/

/-- **A destructor for each slot of a context, at the row `Σ_D`.** A dead slot, or a live slot of
persistent type, needs none (`none`). A live slot of type `T` gets a λ-value `λx. b`, the paper's
`drop_T : 1 ⟜ T`, at `T ⊸ F_{Σ_D} 1` in every dead context: a closed function.  `[spec §62]` -/
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
In a context, slot `0` is the variable bound last, so the slots are dropped in the reverse order
of their binding (last in, first out). Each application is bound, and its unit result is a new
slot `0`, so the next slot is at `k + 2`.  `[spec §62]` -/
def dropCtxE : List (Option Expr) → Nat → Expr
  | [], _ => .val .unit
  | none :: ds, k => dropCtxE ds (k + 1)
  | some b :: ds, k => .app (.val (.lam (dropCtxE ds (k + 2)))) (.app (.val (.lam b)) (.var k))

/-- **Last in, first out**: the first destructor `drop_ctx` runs is the one of slot `k`, the
variable bound last; the rest run after it returns.  `[spec §62]` -/
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
already consumed: dead slots and the units the destructors returned.  `[spec §62]` -/
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
`M then x. N unwind drop_ctx`, `drop_ctx` under `[then]`'s dead binder.  `[spec §62]` -/
def letDE (ds : List (Option Expr)) (N M : Expr) : Expr := thenE N (dropCtxE ds 1) M

/-- **`[let-dtor]`: `[let]` at any row, its continuation's context held across `M` with
destructors.** The finaliser is `drop_ctx` of the continuation's context `Γ₂`, so a raise in `M`,
or a cancel of a continuation captured in `M`, runs every live owned slot's destructor, last bound
first, and passes the error on.

Against `[let]` (`CDerives.effLet`): `hW : Σ.Cancels → Γ₂.OwnFree` is replaced by a destructor
for every live slot of `Γ₂` that is not persistent (`hds`), at a row `Σ_D ≤ Σ` whose operations
all resume (`hSDc`: destructors never fail) and which does not hold `Div` (`hSDd`: destructors
terminate). `hfin` is `[then]`'s: the cancel row of each capturable operation and cancellable wait
of `Σ` records `Σ_D`, since a cancel there unwinds through the destructors. `hNZ`, `hUq` are
`[then]`'s conditions on the row, and `hU` asks `Γ₂` persistent where `Σ` has an unrestricted
operation at some depth.

Derived from `[then]`, no constructor added.  `[spec §62]` -/
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

/-- **`[let-dtor]` is sound**: `fundamentalC` at its derivation, no hypothesis added.
`[spec §62]` -/
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

/-- **`[let-dtor]` with destructors that may loop**: `effLetD` without `hSDd`, by `[then]`'s
`effThenDiv`, when the bound computation's row has no capturable operation (`hcap`): no cancel
run reaches the frame, and a raise reaches it on the ordinary unwind, at `Σ`, which then holds
`Div`. The destructors still never fail (`¬ Σ_D.Cancels`).  `[spec §62]` -/
theorem CDerives.effLetDDiv {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S SD : Row} {ds : List (Option Expr)}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hDS : RowLe SD S) (hSDc : ¬ SD.Cancels)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hcap : ∀ o ∈ S, capB o.q o.B = false)
    (hds : Dtors Δ SD Γ₂ ds)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (letDE ds N M) (.comp (CTy.effOf S B)) := by
  have hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) (dropCtxE ds 1) (.comp (CTy.effOf SD .unit)) :=
    dropCtx_derives hSDc hds (P := [⟨.unit, false⟩]) (.cons .nil)
  refine .effThenDiv (SM := S) (SD := SD) hs hNZ hUq hU (RowLe.refl S) hDS ?_ ?_ hcap hM hN hD
  · intro n i o o' hf hf' hr
    rw [hf] at hf'; cases hf'
    exact hfin n i o hf hr
  · exact fun h => absurd h (Row.not_unrD_of_not_cancels hSDc)

/-- `hfin` holds at a row with no capturable operation and no cancellable wait: every row of
errors and must-resume operations.  `[spec §62]` -/
theorem hfin_of_noRead {S SD : Row} (h : ∀ o ∈ S, o.finRead = false) :
    ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin :=
  fun _ _ o hf hr => by rw [h o (Row.find_mem hf).1] at hr; cases hr

/-! ### Destructors from derived drops -/

/-- A consumed context needs no destructors: one `none` per slot. -/
theorem Dtors.ofDead {Δ : LifeCtx} {SD : Row} :
    ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → Dtors Δ SD Γ (List.replicate Γ.length none)
  | [], _ => .nil
  | _ :: _, .cons h => .dead (Dtors.ofDead h)

/-- The derived drop of §12 as a `[let-dtor]` destructor: `λx. dtorE T x`. -/
def derivedDropB (T : VTy) : Expr := .app (dtorE T) (.var 0)

/-- **A derived drop is a destructor at every row**: `λx. dtorE T x : T ⊸ F_{Σ_D} 1`, pure, in
every dead context.  `[spec §12, §62]` -/
theorem derivedDropB_derives {Δ : LifeCtx} {T : VTy} (hT : HasDtor T) (SD : Row) (Γ : Ctx VTy)
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam (derivedDropB T))) (.comp (.arr T (CTy.effOf SD .unit))) :=
  .lam (.effSub (RowLe.nil SD) (.ret (.lolliE (split_kill' _).toP (.var (.here hΓ.toP))
    (dtor_wf hT (kill_dead _)))))

/-- **Every context whose live slots are persistent or have derived drops has destructors** at
every row: the derived drop (`derivedDropB`) for each live slot that is not persistent. So
`[let-dtor]` holds such a context across an abortive `M`, where `[let]`'s `hW` asks it own-free.
`[spec §12, §62]` -/
theorem Dtors.ofHasDtor {Δ : LifeCtx} {SD : Row} :
    ∀ {Γ : Ctx VTy}, (∀ s ∈ Γ, s.live = true → s.ty.Persistent ∨ HasDtor s.ty) →
      Dtors Δ SD Γ (Γ.map fun s =>
        if s.live && !s.ty.persistent then some (derivedDropB s.ty) else none)
  | [], _ => .nil
  | ⟨T, false⟩ :: Γ, h => by
      simpa using Dtors.dead (T := T) (Dtors.ofHasDtor (Γ := Γ)
        (fun s hs hl => h s (List.mem_cons_of_mem _ hs) hl))
  | ⟨T, true⟩ :: Γ, h => by
      have ih := Dtors.ofHasDtor (Δ := Δ) (SD := SD) (Γ := Γ)
        (fun s hs hl => h s (List.mem_cons_of_mem _ hs) hl)
      by_cases hp : T.persistent = true
      · simpa [hp] using Dtors.pers (T := T) hp ih
      · have hd : HasDtor T := (h ⟨T, true⟩ (by simp) rfl).resolve_left hp
        simpa [hp] using Dtors.drop (derivedDropB_derives hd SD) ih

end BoCa.Fig16.LogRel.Core

end
