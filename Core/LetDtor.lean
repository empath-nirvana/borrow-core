import Core.Fundamental
import Core.Records
import Core.Dtor
import Core.Splits

/-!
# Core — `[let-dtor]`: effectful destructors on every exit  `[spec §62]`

`[let]` (`CDerivesIn.effLet`) keeps the continuation's context `Γ₂` live across `M` only where `M`'s
row cannot abort or every live slot of `Γ₂` is own-free (`hW`). `[let-dtor]` lifts that refusal:
each live slot of `Γ₂` that is not persistent is dropped, on the unwind, by **the destructor of its
type**, `drop_T : T ⊸ F_{Σ_D} 1`, a closed function that may perform operations of a row
`Σ_D ≤ Σ`. The term is `M then x. N unwind drop_ctx`, with `drop_ctx` running those destructors,
the slot bound last first.

**Destructors by type** (`dropOf`). One destructor per type, a function of the type and of the
program's declaration `decl` at the opaque types:

| type | `drop_T` |
|---|---|
| `A ⊗ B` | `λp. let (x, y) = p in drop_B y; drop_A x` (`tensorDropB`) |
| `A ⊕ B` | `λs. case s {inl x → drop_A x | inr y → drop_B y}` (`sumDropB`) |
| `Opq k` | the declared destructor `decl k` |
| `U(C & D)` | `λk. k.2`, the second component (`closeDropB`) |
| any other `T` with a derived drop (§12, `HasDtor`) | `λx. dtorE T x` (`derivedDropB`) |

So two frames, and a loop's *close*, that drop a value of the same type run the same destructor.
`DropOk` is the condition under which `drop_T` is typed at `Σ_D` (`DropOk.derives`), and every type
with a derived drop satisfies it at every row and declaration (`DropOk.ofHasDtor`).

After Congard, Munch-Maccagnoni and Douence (*Linear Effects, Exceptions, and Resource Safety*,
ESOP 2026, §4.3), whose translation of the resource CBPV's `let` is
`let s = π₁⟦t⟧ in δ(s, x.⟦u⟧, e. raise_Γ(e))` with `raise_Γ(e)` dropping `Γ` right to left:

| paper | here |
|---|---|
| `δ(s, x.⟦u⟧, e. raise_Γ(e))` | `thenE N D M`, the frame `ubind (λx. N, λ_. D)` |
| `drop_A : 1 ⟜ A`, an object `A → T I` of `C/TI` | `drop_A = dropOf decl A : A ⊸ F_{Σ_D} 1`, closed |
| `drop_{A⊗B}`, `drop_{A⊕B}` componentwise | `tensorDropB`, `sumDropB` |
| `↓N = N & 1`, `drop_{↓N} = π₂` | `closeDropB` at `U(C & F_{Σ_F} 1)` |
| `drop_ctx_Γ`, right to left | `dropCtxE ds k`: slot `k` (the variable bound last) first |
| `unwind_Γ(e)`, `e` passed on unchanged | `[finalise]` re-raises `p` after `D ()` |
| `delete` releases without fail | `hSDc : ¬ Σ_D.Cancels` |
| `E` carries no resources | `[raise]`'s `hd : o.A.OwnFree` |

The order inside `drop_{A⊗B}` (the second component first) is ours, chosen to agree with
`drop_ctx`, which drops the variable bound last first.

**A derived form, not a constructor.** `[let-dtor]` is `[then]` (`CDerivesIn.effThen`) at the
finaliser `drop_ctx`, which is itself a `CDerives` derivation (`dropCtx_derives`). So no
constructor is added to `CDerives`: `fundamentalC`, `adequacyC` and `adequacyD` cover it with no
new compatibility lemma, and every induction over `CDerives` (`CDerivesAt`, `CDerivesP`, `Tied`,
`PinDerives`, the totality results) already has its case, `[then]`'s.

**The premises and their reasons.**
- `hSDc : ¬ Σ_D.Cancels`: a destructor does not fail, the paper's `delete`, which "releases without
  fail". Each destructor is bound by `[let]` at `Σ_D` inside `drop_ctx`, with the slots not yet
  dropped live across it; a destructor that raised would abandon them, which `[let]`'s `hW`
  refuses. What a destructor that can fail should do is *Open* (SPEC §62).
- `hSDd : Σ_D` does not hold `Div`: `[then]`'s premise `hSD`. `then_compatC` is a proof in the
  total relation, which reads the finaliser's run as a terminating one: a cancel run is a least
  fixed point and reaches the finaliser. `Div` stays out of the destructor machinery;
  `CDerives.effLetDDiv` drops `hSDd` where `M`'s row has no capturable operation, by `[then]`'s
  `effThenDiv`.
- `hfin`: `[then]`'s, at `M`'s row `Σ_M ≤ Σ`: the cancel row of each capturable operation and
  cancellable wait of `Σ_M` records `Σ_D`, since a cancel there unwinds through the destructors.
- `hNZ`, `hUq`, `hU`: `[then]`'s conditions on the row and on `Γ₂`.

`[let]` is the instance with no destructor to run on the unwind: `Core/LetDtorLet.lean` relates
the two (`letDE_none_*`, `effLet_as_effLetD`) and says what keeps `[let]` a rule of its own.
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

/-! ### The derived drop as a destructor -/

/-- The derived drop of §12 as a `[let-dtor]` destructor: `λx. dtorE T x`. -/
def derivedDropB (T : VTy) : Expr := .app (dtorE T) (.var 0)

/-- **A derived drop is a destructor at every row**: `λx. dtorE T x : T ⊸ F_{Σ_D} 1`, pure, in
every dead context.  `[spec §12, §62]` -/
theorem derivedDropB_derives {Δ : LifeCtx} {T : VTy} (hT : HasDtor T) (SD : Row) (Γ : Ctx VTy)
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam (derivedDropB T))) (.comp (.arr T (CTy.effOf SD .unit))) :=
  .lam (.effSub (RowLe.nil SD) (.ret (.lolliE (split_kill' _).toP (.var (.here hΓ.toP))
    (dtor_wf hT (kill_dead _)))))


/-! ### Destructors by type -/

/-- `drop_{A⊗B} = λp. let (x, y) = p in drop_B y; drop_A x`, for `drop_A = λx. a` and
`drop_B = λy. b`: the second component, bound last by `let (x, y)`, first.  `[spec §62]` -/
def tensorDropB (a b : Expr) : Expr :=
  .letpair (.var 0) (bindE (.app (.val (.lam b)) (.var 0)) (.app (.val (.lam a)) (.var 2)))

/-- `drop_{A⊕B} = λs. case s {inl x → drop_A x | inr y → drop_B y}`.  `[spec §62]` -/
def sumDropB (a b : Expr) : Expr :=
  .case (.var 0) (.app (.val (.lam a)) (.var 0)) (.app (.val (.lam b)) (.var 0))

/-- `drop_{U(C & D)} = λk. k.2`: the paper's `drop_{↓N} = π₂` at `↓N = N & 1`.  `[spec §62]` -/
def closeDropB : Expr := .app (.var 0) (.val (.inj₂ .unit))

/-- The types whose destructor `dropOf` builds by their former: `⊗`, `⊕`, the opaque types (read
from the declaration) and `U(C & D)`. -/
def structB : VTy → Bool
  | .tensor _ _ => true
  | .sum _ _ => true
  | .opq _ => true
  | .thunk (.amp _ _) => true
  | _ => false

open Classical in
/-- **The destructor of a type**, `drop_T`, as the body of `λx. drop_T`: structural at `⊗` and
`⊕`, the declaration `decl k` at an opaque type `Opq k`, the second component at `U(C & D)`, and
the derived drop of §12 at every other type that has one. `none`: the type has no destructor.
One destructor per type and declaration.  `[spec §12, §62]` -/
noncomputable def dropOf (decl : Opaque → Option Expr) : VTy → Option Expr
  | .tensor A B =>
      match dropOf decl A, dropOf decl B with
      | some a, some b => some (tensorDropB a b)
      | _, _ => none
  | .sum A B =>
      match dropOf decl A, dropOf decl B with
      | some a, some b => some (sumDropB a b)
      | _, _ => none
  | .opq k => decl k
  | .thunk (.amp _ _) => some closeDropB
  | T => if HasDtor T then some (derivedDropB T) else none

theorem dropOf_tensor {decl : Opaque → Option Expr} {A B : VTy} {a b : Expr}
    (ha : dropOf decl A = some a) (hb : dropOf decl B = some b) :
    dropOf decl (.tensor A B) = some (tensorDropB a b) := by
  simp [dropOf, ha, hb]

theorem dropOf_sum {decl : Opaque → Option Expr} {A B : VTy} {a b : Expr}
    (ha : dropOf decl A = some a) (hb : dropOf decl B = some b) :
    dropOf decl (.sum A B) = some (sumDropB a b) := by
  simp [dropOf, ha, hb]

theorem dropOf_derived {decl : Opaque → Option Expr} {T : VTy} (hs : structB T = false)
    (hT : HasDtor T) : dropOf decl T = some (derivedDropB T) := by
  cases T with
  | thunk C => cases C <;> simp_all [dropOf, structB]
  | _ => simp_all [dropOf, structB]

/-- **`drop_T` is typed at `Σ_D`**: the condition, by the type's former. At an opaque type the
declared destructor is typed (`hb`); at `U(C & F_{Σ_F} 1)`, `Σ_F ≤ Σ_D`; at every type `dropOf`
reads by its derived drop, `HasDtor`.  `[spec §62]` -/
inductive DropOk (Δ : LifeCtx) (SD : Row) (decl : Opaque → Option Expr) : VTy → Prop where
  | tensor {A B : VTy} : DropOk Δ SD decl A → DropOk Δ SD decl B → DropOk Δ SD decl (.tensor A B)
  | sum {A B : VTy} : DropOk Δ SD decl A → DropOk Δ SD decl B → DropOk Δ SD decl (.sum A B)
  | opq {k : Opaque} {b : Expr} (hk : decl k = some b)
      (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
        CDerives Δ Γ' (.val (.lam b)) (.comp (.arr (.opq k) (CTy.effOf SD .unit)))) :
      DropOk Δ SD decl (.opq k)
  | close {C : CTy} {SF : Row} (hF : RowLe SF SD) :
      DropOk Δ SD decl (.thunk (.amp C (CTy.effOf SF .unit)))
  | derived {T : VTy} (hs : structB T = false) (hT : HasDtor T) : DropOk Δ SD decl T

theorem tensorDropB_derives {Δ : LifeCtx} {SD : Row} (hSD : ¬ SD.Cancels) {A B : VTy}
    {a b : Expr}
    (ha : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam a)) (.comp (.arr A (CTy.effOf SD .unit))))
    (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr B (CTy.effOf SD .unit))))
    (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam (tensorDropB a b))) (.comp (.arr (.tensor A B) (CTy.effOf SD .unit))) := by
  refine .lam (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .effLet (A := .unit) (.left (.right (.dead (deadSplit hΓ)))) (fun h => absurd h hSD)
    (fun h => absurd h (Row.not_unr_of_not_cancels hSD)) ?_ ?_
  · exact .app (split_kill _).toP (hb _ (kill_dead _)) (.here (by cdead))
  · exact .app (split_kill _).toP (ha _ (kill_dead _)) (.skip rfl (.there (.here (by cdead))))

theorem sumDropB_derives {Δ : LifeCtx} {SD : Row} {A B : VTy} {a b : Expr}
    (ha : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam a)) (.comp (.arr A (CTy.effOf SD .unit))))
    (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr B (CTy.effOf SD .unit))))
    (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam (sumDropB a b))) (.comp (.arr (.sum A B) (CTy.effOf SD .unit))) := by
  refine .lam (.sumE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_ ?_)
  · exact .app (split_kill _).toP (ha _ (kill_dead _)) (.here (by cdead))
  · exact .app (split_kill _).toP (hb _ (kill_dead _)) (.here (by cdead))

theorem closeDropB_derives {Δ : LifeCtx} {SD SF : Row} {C : CTy} (hF : RowLe SF SD)
    (Γ : Ctx VTy) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam closeDropB))
      (.comp (.arr (.thunk (.amp C (CTy.effOf SF .unit))) (CTy.effOf SD .unit))) :=
  .lam (.effSub hF (.proj₂ (.force (C := .amp C (CTy.effOf SF .unit)) (.here hΓ.toP))))

/-- **The destructor of a type is typed**: under `DropOk`, `dropOf decl T` is a destructor
`λx. b : T ⊸ F_{Σ_D} 1` in every dead context, for a row of destructors that never fail.
`[spec §62]` -/
theorem DropOk.derives {Δ : LifeCtx} {SD : Row} {decl : Opaque → Option Expr}
    (hSD : ¬ SD.Cancels) {T : VTy} (h : DropOk Δ SD decl T) :
    ∃ b, dropOf decl T = some b ∧ ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr T (CTy.effOf SD .unit))) := by
  induction h with
  | tensor _ _ iha ihb =>
      obtain ⟨a, ha, hda⟩ := iha
      obtain ⟨b, hb, hdb⟩ := ihb
      exact ⟨_, dropOf_tensor ha hb, tensorDropB_derives hSD hda hdb⟩
  | sum _ _ iha ihb =>
      obtain ⟨a, ha, hda⟩ := iha
      obtain ⟨b, hb, hdb⟩ := ihb
      exact ⟨_, dropOf_sum ha hb, sumDropB_derives hda hdb⟩
  | opq hk hb => exact ⟨_, hk, hb⟩
  | close hF => exact ⟨_, rfl, closeDropB_derives hF⟩
  | derived hs hT => exact ⟨_, dropOf_derived hs hT, derivedDropB_derives hT SD⟩

/-- **A type with a derived drop has a destructor** at every row and declaration: its structural
destructor at `⊗`, `⊕` and `U(C & F 1)`, its derived drop elsewhere.  `[spec §12, §62]` -/
theorem DropOk.ofHasDtor {Δ : LifeCtx} {SD : Row} {decl : Opaque → Option Expr} :
    ∀ {T : VTy}, HasDtor T → DropOk Δ SD decl T
  | _, .tensor ha hb => .tensor (DropOk.ofHasDtor ha) (DropOk.ofHasDtor hb)
  | _, .sum ha hb => .sum (DropOk.ofHasDtor ha) (DropOk.ofHasDtor hb)
  | _, .close => .close (SF := []) (RowLe.nil SD)
  | _, h@.unit => .derived rfl h
  | _, h@.zero => .derived rfl h
  | _, h@.int => .derived rfl h
  | _, h@.unk => .derived rfl h
  | _, h@.bang => .derived rfl h
  | _, h@.imm => .derived rfl h
  | _, h@.mut => .derived rfl h
  | _, h@(.box _) => .derived rfl h
  | _, h@(.ref _) => .derived rfl h
  | _, h@(.mu _ _ _ _) => .derived rfl h
  | _, h@(.nu _ _ _) => .derived rfl h
  | _, h@(.array _) => .derived rfl h
  | _, h@.arrayImm => .derived rfl h
  | _, h@.arrayMut => .derived rfl h

/-- **The destructors of a context**, by type: `drop_T` for each live slot that is not persistent,
`none` for the rest.  `[spec §62]` -/
noncomputable def ctxDrops (decl : Opaque → Option Expr) (Γ : Ctx VTy) : List (Option Expr) :=
  Γ.map fun s => if s.live && !s.ty.persistent then dropOf decl s.ty else none

theorem ctxDrops_dead {decl : Opaque → Option Expr} :
    ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ctxDrops decl Γ = List.replicate Γ.length none
  | [], _ => rfl
  | _ :: _, .cons h => by
      simp only [ctxDrops, List.map_cons, Bool.false_and, List.length_cons,
        List.replicate_succ]
      exact congrArg _ (ctxDrops_dead h)

theorem ctxDrops_cons_live {decl : Opaque → Option Expr} {T : VTy} {b : Expr} (Γ : Ctx VTy)
    (hp : T.persistent = false) (hb : dropOf decl T = some b) :
    ctxDrops decl (⟨T, true⟩ :: Γ) = some b :: ctxDrops decl Γ := by
  simp [ctxDrops, hp, hb]

theorem ctxDrops_cons_pers {decl : Opaque → Option Expr} {T : VTy} (Γ : Ctx VTy)
    (hp : T.Persistent) : ctxDrops decl (⟨T, true⟩ :: Γ) = none :: ctxDrops decl Γ := by
  simp [ctxDrops, hp]

/-- **A context whose live slots are persistent or have a destructor has `Dtors`**, by type. -/
theorem Dtors.ofDrops {Δ : LifeCtx} {SD : Row} {decl : Opaque → Option Expr}
    (hSD : ¬ SD.Cancels) :
    ∀ {Γ : Ctx VTy}, (∀ s ∈ Γ, s.live = true → s.ty.Persistent ∨ DropOk Δ SD decl s.ty) →
      Dtors Δ SD Γ (ctxDrops decl Γ)
  | [], _ => .nil
  | ⟨T, false⟩ :: Γ, h => by
      have ih := Dtors.ofDrops (Δ := Δ) hSD (Γ := Γ)
        (fun s hs hl => h s (List.mem_cons_of_mem _ hs) hl)
      simpa [ctxDrops] using Dtors.dead (T := T) ih
  | ⟨T, true⟩ :: Γ, h => by
      have ih := Dtors.ofDrops (Δ := Δ) hSD (Γ := Γ)
        (fun s hs hl => h s (List.mem_cons_of_mem _ hs) hl)
      by_cases hp : T.persistent = true
      · rw [ctxDrops_cons_pers Γ hp]
        exact Dtors.pers hp ih
      · obtain ⟨b, hb, hd⟩ := ((h ⟨T, true⟩ (by simp) rfl).resolve_left hp).derives hSD
        rw [ctxDrops_cons_live Γ (by simpa using hp) hb]
        exact Dtors.drop hd ih

/-! ### The rule -/

/-- `M then x. N unwind drop_ctx(ds)`: the frame at an explicit list of destructors, `drop_ctx`
under `[then]`'s dead binder.  `[spec §62]` -/
def letDE (ds : List (Option Expr)) (N M : Expr) : Expr := thenE N (dropCtxE ds 1) M

/-- **`let x = M in N` with the continuation's context dropped on the unwind**, each slot by the
destructor of its type: `letDE (ctxDrops decl Γ₂) N M`.  `[spec §62]` -/
noncomputable def letDT (decl : Opaque → Option Expr) (Γ₂ : Ctx VTy) (N M : Expr) : Expr :=
  letDE (ctxDrops decl Γ₂) N M

/-- `[then]`'s `hfin` at `Σ_M = Σ`, from the cancel rows of `Σ` themselves. -/
theorem hfin_self {S SD : Row}
    (h : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin) :
    ∀ n i o o', Row.find S n i = some o → Row.find S n i = some o' → o.finRead = true →
      ThenLe o.fin SD o'.fin := by
  intro n i o o' hf hf' hr
  rw [hf] at hf'; cases hf'
  exact h n i o hf hr

/-- `hfin` holds at a row `Σ_M` with no capturable operation and no cancellable wait: every row of
errors and must-resume operations.  `[spec §62]` -/
theorem hfin_of_noRead {SM S SD : Row} (h : ∀ o ∈ SM, o.finRead = false) :
    ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' → o.finRead = true →
      ThenLe o.fin SD o'.fin :=
  fun _ _ o _ hf _ hr => by rw [h o (Row.find_mem hf).1] at hr; cases hr

/-- **`[let-dtor]`: `[let]` at any row, its continuation's context held across `M` with the
destructors of its types.** The finaliser is `drop_ctx` of `Γ₂`, so a raise in `M`, or a cancel of a
continuation captured in `M`, runs every live owned slot's destructor, `drop_T` of its type `T`
(`dropOf decl T`), last bound first, and passes the error on.

Against `[let]` (`CDerivesIn.effLet`): `hW : Σ.Cancels → Γ₂.OwnFree` is replaced by a destructor for
every live slot of `Γ₂` that is not persistent (`hds`, `DropOk`), at a row `Σ_D ≤ Σ` whose
operations all resume (`hSDc`) and which does not hold `Div` (`hSDd`). `M` is at `Σ_M ≤ Σ`, as in
`[then]`, and `hfin` is `[then]`'s: the cancel row of each capturable operation and cancellable
wait of `Σ_M` records `Σ_D`. `hNZ`, `hUq` are `[then]`'s conditions on the row, and `hU` asks `Γ₂`
persistent where `Σ` has an unrestricted operation at some depth.

Derived from `[then]`, no constructor added.  `[spec §62]` -/
theorem CDerives.effLetD {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S SM SD : Row} {decl : Opaque → Option Expr}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S) (hSDc : ¬ SD.Cancels) (hSDd : Row.divB SD = false)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      o.finRead = true → ThenLe o.fin SD o'.fin)
    (hds : ∀ s ∈ Γ₂, s.live = true → s.ty.Persistent ∨ DropOk Δ SD decl s.ty)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf SM A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (letDT decl Γ₂ N M) (.comp (CTy.effOf S B)) := by
  have hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) (dropCtxE (ctxDrops decl Γ₂) 1)
      (.comp (CTy.effOf SD .unit)) :=
    dropCtx_derives hSDc (Dtors.ofDrops hSDc hds) (P := [⟨.unit, false⟩]) (.cons .nil)
  exact .effThen hs hNZ hUq hU hMS hDS hfin
    (fun h => absurd h (Row.not_unrD_of_not_cancels hSDc)) hSDd hM hN hD

/-- **`[let-dtor]` is sound**: `fundamentalC` at its derivation, no hypothesis added.
`[spec §62]` -/
theorem effLetD_sound {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S SM SD : Row} {decl : Opaque → Option Expr}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S) (hSDc : ¬ SD.Cancels) (hSDd : Row.divB SD = false)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      o.finRead = true → ThenLe o.fin SD o'.fin)
    (hds : ∀ s ∈ Γ₂, s.live = true → s.ty.Persistent ∨ DropOk Δ SD decl s.ty)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf SM A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    SemC Δ Γ (letDT decl Γ₂ N M) (CTy.effOf S B) :=
  fundamentalC (j := .comp _)
    (CDerives.effLetD hs hNZ hUq hU hMS hDS hSDc hSDd hfin hds hM hN)

/-- **`[let-dtor]` with destructors that may loop**: `effLetD` without `hSDd`, by `[then]`'s
`effThenDiv`, when the bound computation's row has no capturable operation (`hcap`): no cancel
run reaches the frame, and a raise reaches it on the ordinary unwind, at `Σ`, which then holds
`Div`. The destructors still never fail (`¬ Σ_D.Cancels`).  `[spec §62]` -/
theorem CDerives.effLetDDiv {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S SM SD : Row} {decl : Opaque → Option Expr}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hMS : RowLe SM S) (hDS : RowLe SD S) (hSDc : ¬ SD.Cancels)
    (hfin : ∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      o.finRead = true → ThenLe o.fin SD o'.fin)
    (hcap : ∀ o ∈ SM, capB o.q o.B = false)
    (hds : ∀ s ∈ Γ₂, s.live = true → s.ty.Persistent ∨ DropOk Δ SD decl s.ty)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf SM A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (letDT decl Γ₂ N M) (.comp (CTy.effOf S B)) := by
  have hD : CDerives Δ (⟨.unit, false⟩ :: Γ₂) (dropCtxE (ctxDrops decl Γ₂) 1)
      (.comp (CTy.effOf SD .unit)) :=
    dropCtx_derives hSDc (Dtors.ofDrops hSDc hds) (P := [⟨.unit, false⟩]) (.cons .nil)
  exact .effThenDiv hs hNZ hUq hU hMS hDS hfin
    (fun h => absurd h (Row.not_unrD_of_not_cancels hSDc)) hcap hM hN hD

/-! ### Destructors from derived drops -/

/-- A consumed context needs no destructors: one `none` per slot. -/
theorem Dtors.ofDead {Δ : LifeCtx} {SD : Row} :
    ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → Dtors Δ SD Γ (List.replicate Γ.length none)
  | [], _ => .nil
  | _ :: _, .cons h => .dead (Dtors.ofDead h)

/-- **A context whose live slots are persistent or have derived drops** satisfies `[let-dtor]`'s
`hds` at every row and declaration. So `[let-dtor]` holds such a context across an abortive `M`,
where `[let]`'s `hW` asks it own-free.  `[spec §12, §62]` -/
theorem hds_ofHasDtor {Δ : LifeCtx} {SD : Row} {decl : Opaque → Option Expr} {Γ : Ctx VTy}
    (h : ∀ s ∈ Γ, s.live = true → s.ty.Persistent ∨ HasDtor s.ty) :
    ∀ s ∈ Γ, s.live = true → s.ty.Persistent ∨ DropOk Δ SD decl s.ty :=
  fun s hs hl => (h s hs hl).imp_right DropOk.ofHasDtor

end BoCa.Fig16.LogRel.Core

end
