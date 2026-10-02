import GhostEnd.Nested
import GhostEnd.ImmLend
import GhostEnd.RLCompat

/-!
# GhostEnd — D16.1, the lend-stack-indexed relation, and GFP (D16.2) (#279)

`docs/effects-tr/16-regress.md` §16.4 sketches the stacked relation `vRL_σ`/`cRL_σ` and states
GFP over it. §16.5 reads it as needing no recursive domain, "a reading of a definition not yet
written". This file writes it.

## The recursion

`vRLs σ`, `cRLs σ` and `effRetS σ` are one `mutual` block, **structurally recursive on the type**
(`termination_by structural`). The stack `σ` is a fixed parameter of the block. The substitution
`δ` (extended at `∀`) and the lifetime vector `αs` (re-lent at `U`) are indices. Each clause refers
to the relation only at a strict subterm of its type:

* `U C`: `RelendableS` of `cRLs σ C`;
* `⊗`, `⊕`, `!`, `[@a]`, `Ref`: `vRLs σ` at the components;
* `F A`: `wpTS` answering in `vRLs σ A`; `F_Σ R`: the piece `bodyS`/`OpenS` at Σ's table,
  answering in `effRetS σ R`, which reaches `vRLs σ A` at `R`'s answer type;
* `A ⊸ C`: `vRLs σ A` (left of `─⋆`) and `cRLs σ C`; `&`, `∀` at the components;
* every other former, and `ν`: the kernel's `vC`/`cC` at `δ_σ(αs)` (`extS`).

The stack-dependent parts take the relation only through a predicate argument and never mention
it otherwise: `RelendableS` (the `U` clause), `RelendableN` (the continuation of a stop that keeps
lends open), `ghostS` (what a stop owes the lenders it crosses), and `OpenS`, a least fixed point
over its own continuation variable `X`, which occurs only positively (`openFS_mono`). No predicate
is defined in terms of itself at the same type, and nothing is stored in the world. So D16.1 needs
no recursive domain: §16.5's reading is now this definition's elaboration.

## The components, fixed

§16.4 leaves the exact forms of `Relendable_σ`, `OpenD_σ` and `TabAt_σ` open ("#268's item 3, and
of their `imm` entries item 2"). They are fixed here as the stacked forms of the proved
single-lend objects:

* **The stack.** `LEnt` is `(ℓ, x, T, k)` with `k` `mut` or `imm v` (6.64 fixes the value), and
  `cross`, the names whose stops cross this lend: its lender's row. Stacks and lifetime vectors
  are innermost first, so `σ·new` is `new :: σ`. `δ_σ(αs)` is `extS δ σ αs`.
* **Views.** `vwS` hands the view of each entry its drop flag asks for, `ℓ ↦ M_α` (`viewP`) or
  `ℓ ↦ I_α` (`ptoImmS`). An entry whose place an inner entry lends again (a reborrow, `withbor`
  (3)) is shadowed: its view was unfolded by 6.66 and the piece cannot hold it.
* **Re-lend.** `ReLend αs' αs`: pointwise `α′ᵢ ⊑ αᵢ`, in nesting order.
* **`RelendableS`**: the resource splits into the views it dropped and a part strictly above the
  outermost lend that, at every extension and every re-lend, handed the views, is in `P`. At one
  entry it is `Relendable` (`RLCompat.lean`); at `[]` it is the kernel's `U` clause
  (`relendableS_nil`).
* **Stops** (`stopS`). An operation of the name `n` stops at depth `depth σ n`, the number of
  innermost entries whose lender's row holds `n`. It ghost-ends those entries (their views are
  dropped, `ghostS` hands the innermost owner back and the rest owes the outermost of them) and
  keeps the others open, owing a continuation re-lendable over them (`RelendableN`). Depth `|σ|`
  is D16.1's "stop at the lenders' row"; depth `0` is its "stop at a row handled inside"; a depth
  between is a handler that sits between two lenders, which D16.1 reaches as "a stop inside an
  inner lend is at an extension `σ·τ`", read from the inner lend's side.
* **`OpenS`** is `OpenD` over vectors: each re-lend of the ghost-ended entries is pointwise below
  the lifetimes just ended and below the entries kept open.
* **`TabAtS`**: `TabAt` at the innermost and outermost lends.

## What is proved

* **`σ = []`**: `vRLs [] = vC`, `cRLs [] = cC`, `gRLs [] = gDenC` up to `↔` (`vRLs_nil`,
  `cRLs_nil`, `gRLs_nil`), so `GFPAt [] ↔` the conclusion of `fundamentalC` (`gfpAt_nil_iff`),
  and `GFPAt []` holds (`gfpAt_nil`).
* **The stacked `U` clause**: `[force]` (`force_RLs`), the slot thawing by construction
  (`relendableS_thunk`), and `thunk` over a re-lendable context (`thunkF_RLs`, `thunkE_RLs`).
* **The `withbor` rows at `σ·new`, `|σ| = 1`**: D16.1's piece at the stack `[new, outer]`, stopping
  at the lenders' row, is #268's `NestRelend` when `new` reborrows `outer`'s place
  (`nestRelend_of_openS`) and `NestRelend₂` when it lends another place (`nestRelend₂_of_openS`).
  So the commutation lemmas fold the extended stack back: `withbor_reborrow_RLs`
  (`nested_relend`) and `withbor_other_RLs` (`nested₂_relend`), and at the outer lender
  `withbor_reborrow_spans`, `withbor_other_spans`.
* **Every hypothesis discharged**: a reborrow callback that yields once with both lends open,
  written as D16.1's piece (`openS_yield`, `openS_val`), gives its `ewpTS` beside the outer owner
  (`withbor_reborrow_spans_yield`). A stop of D16.1's piece at the lenders' row is inhabited.

GFP itself (D16.2) is stated (`GFP`, `GFPAt`), not proved.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Stacks, lifetime vectors, views -/

/-- The kind of a lend: `mut` (6.65), or `imm` at the value 6.64 fixes. -/
inductive LKind where
  | mut
  | imm (v : Val)

/-- **An entry of the lend stack**: the lent place `ℓ`, the lifetime variable `x`, the payload
type `T`, the kind, and the names whose stops cross this lend (its lender's row). -/
structure LEnt where
  l : BoCa.Loc
  x : LifeVar
  T : VTy
  k : LKind
  cross : UInt32 → Bool

/-- A lend stack, innermost first: `σ·new` is `new :: σ`. -/
abbrev LStack := List LEnt

/-- `δ_σ(αs) = δ[x₁ ↦ α₁, …, xₙ ↦ αₙ]`, the vectors innermost first. -/
def extS (δ : LSub) : LStack → List Life → LSub
  | e :: σ, α :: αs => (extS δ σ αs).extend e.x α
  | _, _ => δ

/-- The depth of a stop of the name `n`: the innermost entries whose lender's row holds `n`. -/
def depth (σ : LStack) (n : UInt32) : Nat := (σ.takeWhile fun e => e.cross n).length

/-- The operations of `Tab` that stop at depth `k`. -/
def tabK (σ : LStack) (k : Nat) (Tab : OpTab) : OpTab :=
  fun n i => if depth σ n = k then Tab n i else none

/-- The view of one entry, if its drop flag asks for it. -/
def vwE (δ : LSub) (e : LEnt) : Bool → Life → List SRec → WProp
  | false, _, _ => emp
  | true, α, ls => match e.k with
    | .mut => viewP e.l e.T δ α ls
    | .imm _ => ptoImmS e.l α ls (fun ls₀ => vC true e.T ls₀ δ)

/-- An entry is shadowed when an inner entry lends its place again. -/
def vis (seen : List BoCa.Loc) (e : LEnt) (d : Bool) : Bool := d && !decide (e.l ∈ seen)

/-- The views of a stack at a lifetime vector, `seen` the places of the entries inside it. -/
def vwS (δ : LSub) : List BoCa.Loc → LStack → List Bool → List Life → List SRec → WProp
  | _, [], [], [], _ => emp
  | seen, e :: σ, d :: ds, α :: αs, ls =>
      vwE δ e (vis seen e d) α ls ⋆ vwS δ (e.l :: seen) σ ds αs ls
  | _, _, _, _, _ => fun _ => False

/-- What a stop dropped at one entry: a single cell of its kind at its place, or nothing. -/
def dropE (e : LEnt) : Bool → WProp
  | false => emp
  | true => fun ρ => ∃ ψ, ρ = ResU.single e.l ψ ∧
      ψ.kind = (match e.k with | .mut => Kind.mut | .imm _ => Kind.imm)

/-- What a stop dropped across a stack. -/
def dropS : List BoCa.Loc → LStack → List Bool → WProp
  | _, [], [] => emp
  | seen, e :: σ, d :: ds => dropE e (vis seen e d) ⋆ dropS (e.l :: seen) σ ds
  | _, _, _ => fun _ => False

/-- The share is strictly above the outermost lend of the vector (no condition at `[]`). -/
def stratS (αs : List Life) (ρ : WRes) : Prop := ∀ a ∈ αs.getLast?, ρ.InStratum a

/-- `[top αs] P`. -/
def boxTop (αs : List Life) (P : WProp) : WProp := fun ρ => P ρ ∧ stratS αs ρ

/-- **A re-lend**: pointwise `α′ᵢ ⊑ αᵢ`, in nesting order (innermost first, each strictly below
the next). -/
def ReLend (αs' αs : List Life) : Prop := List.Forall₂ (· ≤ ·) αs' αs ∧ List.IsChain (· < ·) αs'

/-- **`Relendable_σ`.** The resource splits into the views it dropped and a part strictly above
the outermost lend that, at every extension of the list and every re-lend, handed the views, is in
`P`. -/
def RelendableS (δ : LSub) (seen : List BoCa.Loc) (σ : LStack) (P : List Life → List SRec → WProp)
    (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ seen σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ ls', Ext ls ls' ρz → ∀ αs', ReLend αs' αs → (vwS δ seen σ ds αs' ls' ─⋆ P αs' ls') ρz

/-- `Relendable_σ` at one list: the continuation of a stop that keeps `σ` open, whose list the
table already extends. -/
def RelendableN (δ : LSub) (seen : List BoCa.Loc) (σ : LStack) (P : List Life → WProp)
    (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ seen σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ αs', ReLend αs' αs → (vwS δ seen σ ds αs' ls ─⋆ P αs') ρz

/-- The owner an entry's lender holds: 6.65's `∃w. ℓ ↦ w ⋆ 𝒱⟦T⟧(w)`, 6.64's `ℓ ↦ v ⋆ 𝒱⟦T⟧(v)`. -/
def ownerE (δ : LSub) (e : LEnt) (ls : List SRec) : WProp := match e.k with
  | .mut => owner e.l e.T δ ls
  | .imm v => ownerI e.l v e.T δ ls

/-- The exit of an entry's lender, handing its owner back: 6.65's and 6.64's postcondition shape. -/
def ownWandE (δ : LSub) (e : LEnt) (ls : List SRec) (R : WProp) : WProp := match e.k with
  | .mut => ownWand e.l e.T δ ls R
  | .imm v => ptoOwn e.l v ─⋆ (vC true e.T ls δ v ─⋆ R)

/-- **What a stop owes the lenders it crosses**, innermost first: in `[α_inner]`, handed the
innermost owner back, the owner beside a part in `[α_outer]` that owes `R`. The shape of `nestF`
and `nestF₂` at two entries; at one entry it gives `stopAtD`'s. -/
def ghostS (δ : LSub) : LStack → List Life → List SRec → WProp → WProp
  | e :: _, α :: αs, ls, R => box α (ownWandE δ e ls (ownerE δ e ls ⋆ boxTop (α :: αs) R))
  | _, _, _, R => R

/-! ### The piece: `OpenD_σ` -/

/-- The continuation a stop owes: indexed by its depth, its drops, the lifetimes it ended, and
the lifetimes of the entries it kept open. -/
abbrev XT := Nat → List Bool → List Life → List Life → List SRec → Expr → WProp

/-- **A stop with the stack open at `αs`.** Of depth `k`: the views of the innermost `k` entries
dropped, those lenders owed `ghostS`, the table's continuation re-lendable over the rest. -/
def stopS (δ : LSub) (σ : LStack) (Tab : OpTab) (X : XT) (αs : List Life) (ls : List SRec)
    (t : Expr) : WProp :=
  ex fun k => ex fun ds => dropS [] (σ.take k) ds ⋆
    ghostS δ (σ.take k) (αs.take k) ls
      (opTable (tabK σ k Tab) ls t fun ls' e' =>
        RelendableN δ ((σ.take k).map LEnt.l) (σ.drop k)
          (fun αo => X k ds (αs.take k) αo ls' e') (αs.drop k) ls')

/-- One run with the stack open at `αs`: an answer in `Q αs`, the stack still open, or a stop. -/
def bodyS (δ : LSub) (σ : LStack) (Tab : OpTab) (Q : List Life → List SRec → Val → WProp)
    (X : XT) (αs : List Life) : List SRec → Expr → WProp :=
  fun ls e => wpG ls e fun ls'' t ρ => valPost (Q αs) ls'' t ρ ∨ stopS δ σ Tab X αs ls'' t ρ

/-- One unfolding: the ghost-ended entries re-lent, each below the lifetime it ended and below the
entries kept open, the share in `[top]` and handed the views its drops ask for. -/
def openFS (δ : LSub) (σ : LStack) (Tab : OpTab) (Q : List Life → List SRec → Val → WProp)
    (X : XT) : XT := fun k ds αi αo ls e ρ =>
  ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) (αi' ++ αo) →
    boxTop αi' (vwS δ [] (σ.take k) ds αi' ls ─⋆ bodyS δ σ Tab Q X (αi' ++ αo) ls e) ρ

/-- **`OpenD_σ`**: the least fixed point of `openFS`, written in `Prop` as `ewpTS` is. -/
def OpenS (δ : LSub) (σ : LStack) (Tab : OpTab) (Q : List Life → List SRec → Val → WProp) :
    XT := fun k ds αi αo ls e ρ =>
  ∀ X : XT, (∀ k ds αi αo ls e ρ, openFS δ σ Tab Q X k ds αi αo ls e ρ → X k ds αi αo ls e ρ) →
    X k ds αi αo ls e ρ

/-- The operation table of `F_Σ R`'s outermost layer, the operation types read at `δ` (closed
data, SPEC §19). -/
def rowTab (n i : UInt32) (q : Qual) (A B : VTy) (C : CTy) (δ : LSub) : OpTab :=
  OpTab.ext n i ⟨q, B.isZero && q != .lin, fun ls v => vC true A ls δ v,
    fun ls v => vC true B ls δ v⟩ (effTab C δ)

/-! ### D16.1 -/

mutual
/-- **`vRL_σ`**, D16.1's value relation at the stack `σ`, the lends at `αs`. Structural on the
type; `σ` is a parameter. -/
def vRLs (σ : LStack) : LSub → VTy → List Life → List SRec → Val → WProp
  | δ, .thunk C, αs, ls, f =>
      RelendableS δ [] σ (fun αs' ls' => cRLs σ δ C αs' ls' (forceE C (.val f))) αs ls
  | δ, .tensor A B, αs, ls, v => ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
      vRLs σ δ A αs ls v₁ ⋆ vRLs σ δ B αs ls v₂
  | δ, .sum A B, αs, ls, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLs σ δ A αs ls v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLs σ δ B αs ls v₂)
  | δ, .bang A, αs, ls, v => fun ρ => ρ = PMap.empty ∧ vRLs σ δ A αs ls v ρ
  | δ, .box a A, αs, ls, v => atLife (extS δ σ αs) a fun α => box α (vRLs σ δ A αs ls v)
  | δ, .ref A, αs, ls, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLs σ δ A αs ls v'
  | δ, A, αs, ls, v => vC true A ls (extS δ σ αs) v
termination_by structural _ A => A
/-- **`cRL_σ`**, D16.1's computation relation. At `F_Σ R` the piece `OpenD_σ` at Σ's table. -/
def cRLs (σ : LStack) : LSub → CTy → List Life → List SRec → Expr → WProp
  | δ, .ret B, αs, ls, e => wpTS ls e fun ls'' v => vRLs σ δ B αs ls'' v
  | δ, .eff n i q A B C, αs, ls, e =>
      bodyS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetS σ δ C αs' ls v)
        (OpenS δ σ (rowTab n i q A B C δ) (fun αs' ls v => effRetS σ δ C αs' ls v)) αs ls e
  | δ, .arr A C, αs, ls, e => fun ρ =>
      ∀ v, (vRLs σ δ A αs ls v ─⋆ cRLs σ δ C αs ls (.app e (.val v))) ρ
  | δ, .amp C D, αs, ls, e => fun ρ =>
      cRLs σ δ C αs ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLs σ δ D αs ls (.app e (.val (.inj₂ .unit))) ρ
  | _, .top, _, _, _ => fun _ => True
  | δ, .all x c C, αs, ls, e => fun ρ =>
      ∀ α, (⌜LtLife (extS δ σ αs) c α⌝ ─⋆ cRLs σ (δ.extend x α) C αs ls (.app e (.val .unit))) ρ
  | δ, .nu C, αs, ls, e => cC (.nu C) ls (extS δ σ αs) e
termination_by structural _ C => C
/-- The answer relation of `F_Σ R` at the stack: `vRL_σ R`. -/
def effRetS (σ : LStack) : LSub → CTy → List Life → List SRec → Val → WProp
  | δ, .ret A, αs => fun ls v => vRLs σ δ A αs ls v
  | δ, .eff _ _ _ _ _ C, αs => effRetS σ δ C αs
  | _, _, _ => fun _ _ _ => False
termination_by structural _ C => C
end

/-- `⊛_{x ∈ dom(Γ)} vRL_σ(Γ(x))`. -/
def gSepRLs (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) :
    Ctx VTy → List Val → WProp
  | [], _ => emp
  | _ :: _, [] => emp
  | s :: Γ, v :: γ =>
      if s.live then vRLs σ δ s.ty αs ls v ⋆ gSepRLs σ δ αs ls Γ γ else gSepRLs σ δ αs ls Γ γ

/-- `𝒢RL_σ⟦Γ⟧`. -/
def gRLs (σ : LStack) (δ : LSub) (αs : List Life) (ls : List SRec) (Γ : Ctx VTy)
    (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepRLs σ δ αs ls Γ γ

/-- **`TabAt_σ`**: every borrow cell is at a lifetime `⊒` the innermost lend, and every one away
from the stack's places strictly above the outermost. No condition at `[]`. -/
def TabAtS (σ : LStack) (αs : List Life) (ρ : WRes) : Prop :=
  (∀ a ∈ αs.head?, ρ.InStratum (↓a)) ∧
    ∀ a ∈ αs.getLast?, ∀ k ψ, k ∉ σ.map LEnt.l → ρ.get k = some ψ → ψ.InStratum a

/-- A stack well formed in `Δ`: its variables are in `Δ` and distinct. -/
def LStack.WF (σ : LStack) (Δ : LifeCtx) : Prop :=
  (∀ e ∈ σ, ∃ u, Δ.find? e.x = some u) ∧ (σ.map LEnt.x).Nodup

/-- The computation type a judgment is read at: `return V` at `F A`. -/
def jdgCty : Jdg → CTy
  | .val A => .ret A
  | .comp C => C

/-- **GFP (D16.2) at the stack `σ`.** Every derivation, at every lifetime vector in nesting order
whose assignment models `Δ`, from the table and `𝒢RL_σ⟦Γ⟧`, is in `cRL_σ`. -/
def GFPAt (σ : LStack) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerives Δ Γ e j → σ.WF Δ →
    ∀ (δ : LSub) (αs : List Life), αs.length = σ.length → List.IsChain (· < ·) αs →
      Δ.Models (extS δ σ αs) → ∀ (ls : List SRec) (γ : List Val) (ρ : WRes),
        TabAtS σ αs ρ → gRLs σ δ αs ls Γ γ ρ → cRLs σ δ (jdgCty j) αs ls (substAll γ e) ρ

/-- **GFP (D16.2)**: at every stack. -/
def GFP : Prop := ∀ σ : LStack, GFPAt σ

/-! ### Monotonicity: `X` occurs positively in `openFS` -/

section
variable {δ : LSub}

theorem boxTop_mono {αs : List Life} {P P' : WProp} (h : Entails P P') :
    Entails (boxTop αs P) (boxTop αs P') := fun ρ hp => ⟨h ρ hp.1, hp.2⟩

theorem ownWandE_mono {e : LEnt} {ls : List SRec} {R R' : WProp} (h : Entails R R') :
    Entails (ownWandE δ e ls R) (ownWandE δ e ls R') := by
  obtain ⟨l, x, T, k, cr⟩ := e
  cases k with
  | «mut» => exact ownWand_mono h
  | imm v => exact fun _ hw ρa ρb ha hc => wand_mono_right h ρb (hw ρa ρb ha hc)

theorem ghostS_mono {R R' : WProp} (h : Entails R R') :
    ∀ (σ : LStack) (αs : List Life) (ls : List SRec),
      Entails (ghostS δ σ αs ls R) (ghostS δ σ αs ls R')
  | _ :: _, _ :: _, _ => box_mono (ownWandE_mono fun _ ⟨a, b, hc, ha, hb⟩ =>
      ⟨a, b, hc, ha, boxTop_mono h b hb⟩)
  | [], _, _ => h
  | _ :: _, [], _ => h

theorem relendableN_mono {seen : List BoCa.Loc} {σ : LStack} {P P' : List Life → WProp}
    (h : ∀ αs, Entails (P αs) (P' αs)) {αs : List Life} {ls : List SRec} :
    Entails (RelendableN δ seen σ P αs ls) (RelendableN δ seen σ P' αs ls) := by
  rintro ρ ⟨ds, ρz, ρn, hc, hn, hz, hth⟩
  exact ⟨ds, ρz, ρn, hc, hn, hz, fun αs' hr => wand_mono_right (h αs') ρz (hth αs' hr)⟩

variable {σ : LStack} {Tab : OpTab} {Q : List Life → List SRec → Val → WProp}

theorem stopS_mono {X X' : XT} (hX : ∀ k ds αi αo ls e ρ, X k ds αi αo ls e ρ → X' k ds αi αo ls e ρ)
    {αs : List Life} {ls : List SRec} {t : Expr} :
    Entails (stopS δ σ Tab X αs ls t) (stopS δ σ Tab X' αs ls t) := by
  rintro ρ ⟨k, ds, ρ₁, ρ₂, hc, hd, hg⟩
  refine ⟨k, ds, ρ₁, ρ₂, hc, hd, ghostS_mono (fun τ h => ?_) _ _ _ ρ₂ hg⟩
  exact opTable_mono _ _ _ _ _ _ (fun _ _ _ h' => relendableN_mono
    (fun _ _ h'' => hX _ _ _ _ _ _ _ h'') _ h') h

theorem bodyS_mono {X X' : XT} (hX : ∀ k ds αi αo ls e ρ, X k ds αi αo ls e ρ → X' k ds αi αo ls e ρ)
    {αs : List Life} {ls : List SRec} {e : Expr} :
    Entails (bodyS δ σ Tab Q X αs ls e) (bodyS δ σ Tab Q X' αs ls e) :=
  fun _ h => wpG_mono (fun _ _ _ hq => hq.imp id (stopS_mono hX _)) h

/-- **Positivity**: the continuation variable occurs only positively in one unfolding. -/
theorem openFS_mono {X X' : XT} (hX : ∀ k ds αi αo ls e ρ, X k ds αi αo ls e ρ → X' k ds αi αo ls e ρ)
    {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr} :
    Entails (openFS δ σ Tab Q X k ds αi αo ls e) (openFS δ σ Tab Q X' k ds αi αo ls e) :=
  fun _ h αi' h₁ h₂ => boxTop_mono (wand_mono_right (bodyS_mono hX)) _ (h αi' h₁ h₂)

theorem openS_fold {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : openFS δ σ Tab Q (OpenS δ σ Tab Q) k ds αi αo ls e ρ) :
    OpenS δ σ Tab Q k ds αi αo ls e ρ :=
  fun X hX => hX _ _ _ _ _ _ ρ (openFS_mono (fun _ _ _ _ _ _ _ h' => h' X hX) ρ h)

theorem openS_unfold {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : OpenS δ σ Tab Q k ds αi αo ls e ρ) :
    openFS δ σ Tab Q (OpenS δ σ Tab Q) k ds αi αo ls e ρ :=
  h (openFS δ σ Tab Q (OpenS δ σ Tab Q))
    (fun _ _ _ _ _ _ _ h' => openFS_mono (fun _ _ _ _ _ _ _ h'' => openS_fold h'') _ h')

end

/-! ### At `σ = []`: the kernel's relation -/

section
variable {δ : LSub}

theorem emp_iff {ρ : WRes} : emp ρ ↔ ρ = PMap.empty := ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem vwS_nil {seen : List BoCa.Loc} {ds : List Bool} {αs : List Life} {ls : List SRec}
    {ρ : WRes} (h : vwS δ seen [] ds αs ls ρ) : ds = [] ∧ αs = [] ∧ ρ = PMap.empty := by
  cases ds <;> cases αs <;> first | exact ⟨rfl, rfl, h.1⟩ | exact absurd h id

theorem stratS_nil (ρ : WRes) : stratS [] ρ := by simp [stratS]

theorem reLend_nil {αs' : List Life} (h : ReLend αs' []) : αs' = [] :=
  List.forall₂_nil_right_iff.mp h.1

theorem reLend_nil_nil : ReLend [] [] := ⟨List.Forall₂.nil, List.IsChain.nil⟩

/-- **`Relendable_[]` is the kernel's `U` clause**: Kripke along `Ext`, nothing dropped. -/
theorem relendableS_nil {seen : List BoCa.Loc} {P : List Life → List SRec → WProp}
    {ls : List SRec} {ρ : WRes} :
    RelendableS δ seen [] P [] ls ρ ↔ ∀ ls', Ext ls ls' ρ → P [] ls' ρ := by
  constructor
  · rintro ⟨ds, ρz, ρn, hc, hn, -, hth⟩ ls' he
    obtain ⟨rfl, -, rfl⟩ := vwS_nil hn
    obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
    exact hth ls' he [] reLend_nil_nil PMap.empty _ ⟨rfl, trivial⟩ (ResU.comp_empty_right _)
  · intro h
    refine ⟨[], ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨rfl, trivial⟩, stratS_nil ρ,
      fun ls' he αs' hr ρv σ hv hcv => ?_⟩
    obtain rfl := reLend_nil hr
    obtain ⟨-, -, rfl⟩ := vwS_nil hv
    rw [ResU.CompS.functional hcv (ResU.comp_empty_right ρ)]
    exact h ls' he

/-- `Relendable_[]` at one list is the predicate itself. -/
theorem relendableN_nil {seen : List BoCa.Loc} {P : List Life → WProp} {ls : List SRec}
    {ρ : WRes} : RelendableN δ seen [] P [] ls ρ ↔ P [] ρ := by
  constructor
  · rintro ⟨ds, ρz, ρn, hc, hn, -, hth⟩
    obtain ⟨rfl, -, rfl⟩ := vwS_nil hn
    obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
    exact hth [] reLend_nil_nil PMap.empty _ ⟨rfl, trivial⟩ (ResU.comp_empty_right _)
  · intro h
    refine ⟨[], ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨rfl, trivial⟩, stratS_nil ρ,
      fun αs' hr ρv σ hv hcv => ?_⟩
    obtain rfl := reLend_nil hr
    obtain ⟨-, -, rfl⟩ := vwS_nil hv
    rw [ResU.CompS.functional hcv (ResU.comp_empty_right ρ)]
    exact h

theorem tabK_nil_zero (Tab : OpTab) : tabK [] 0 Tab = Tab := by
  funext n i; simp [tabK, depth]

theorem opTable_none {T : OpTab} (hT : ∀ n i, T n i = none) {ls : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} : ¬ opTable T ls t Φ ρ := by
  rintro (⟨K, n, i, v, en, ρ₁, ρ₂, -, ⟨-, -, -, hT', -⟩, -⟩ | ⟨K, n, i, v, en, ρ₁, ρ₂, -, ⟨-, -, -, hT', -⟩, -⟩)
  · rw [hT] at hT'; cases hT'
  · rw [hT] at hT'; cases hT'

/-- **A stop at `[]`** is a stop of the table, owing the next unfolding at no lend. -/
theorem stopS_nil {Tab : OpTab} {X : XT} {ls : List SRec} {t : Expr} {ρ : WRes} :
    stopS δ [] Tab X [] ls t ρ ↔ opTable Tab ls t (fun ls' e' => X 0 [] [] [] ls' e') ρ := by
  constructor
  · rintro ⟨k, ds, ρ₁, ρ₂, hc, hd, hg⟩
    simp only [List.take_nil, List.drop_nil, List.map_nil] at hd hg
    obtain rfl : ds = [] := by cases ds with | nil => rfl | cons _ _ => exact absurd hd id
    obtain rfl := hd.1
    rw [eq_of_compS_empty_left hc]
    cases k with
    | zero =>
        rw [tabK_nil_zero] at hg
        exact opTable_mono _ _ _ _ _ _ (fun _ _ _ h => relendableN_nil.mp h) hg
    | succ k => exact absurd hg (opTable_none fun n i => by simp [tabK, depth])
  · intro h
    refine ⟨0, [], PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, trivial⟩, ?_⟩
    show opTable (tabK [] 0 Tab) ls t _ ρ
    rw [tabK_nil_zero]
    exact opTable_mono _ _ _ _ _ _ (fun _ _ _ h => relendableN_nil.mpr h) h

variable {Tab : OpTab} {Q : List Life → List SRec → Val → WProp}

/-- One unfolding at no lend is one run. -/
theorem openFS_nil {X : XT} {ls : List SRec} {e : Expr} {ρ : WRes} :
    openFS δ [] Tab Q X 0 [] [] [] ls e ρ ↔ bodyS δ [] Tab Q X [] ls e ρ := by
  constructor
  · intro h
    have := (h [] List.Forall₂.nil List.IsChain.nil).1 PMap.empty ρ ⟨rfl, trivial⟩
      (ResU.comp_empty_right ρ)
    exact this
  · intro h αi' hαi _
    obtain rfl := List.forall₂_nil_right_iff.mp hαi
    refine ⟨fun ρv σ hv hcv => ?_, stratS_nil ρ⟩
    obtain rfl := hv.1
    rw [ResU.CompS.functional hcv (ResU.comp_empty_right ρ)]
    exact h

/-- **The piece at `[]` is the kernel's `ewpTS`**: two inductions on the two least fixed
points. -/
theorem bodyS_nil_iff {Q' : List SRec → Val → WProp} (hQ : ∀ ls v ρ, Q [] ls v ρ ↔ Q' ls v ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} :
    bodyS δ [] Tab Q (OpenS δ [] Tab Q) [] ls e ρ ↔ ewpTS ls e (opTable Tab) Q' ρ := by
  constructor
  · intro h
    have hO : OpenS δ [] Tab Q 0 [] [] [] ls e ρ := openS_fold (openFS_nil.mpr h)
    refine hO (fun k ds αi αo ls e ρ => k = 0 → ds = [] → αi = [] → αo = [] →
      ewpTS ls e (opTable Tab) Q' ρ) ?_ rfl rfl rfl rfl
    rintro k ds αi αo ls e ρ hF rfl rfl rfl rfl
    refine ewp_fold (opTable_mono Tab) (wpG_mono (fun ls' t ρ' hq => ?_) (openFS_nil.mp hF))
    rcases hq with ⟨v, rfl, hv⟩ | hs
    · exact Or.inl ⟨v, rfl, (hQ _ _ _).mp hv⟩
    · exact Or.inr (opTable_mono _ _ _ _ _ _ (fun _ _ _ h => h rfl rfl rfl rfl) (stopS_nil.mp hs))
  · intro h
    refine ewp_ind (fun ls e ρ => bodyS δ [] Tab Q (OpenS δ [] Tab Q) [] ls e ρ)
      (fun ls e ρ hS => wpG_mono (fun ls' t ρ' hq => ?_) hS) h
    rcases hq with ⟨v, rfl, hv⟩ | hs
    · exact Or.inl ⟨v, rfl, (hQ _ _ _).mpr hv⟩
    · exact Or.inr (stopS_nil.mpr (opTable_mono _ _ _ _ _ _
        (fun _ _ _ h => openS_fold (openFS_nil.mpr h)) hs))

end

mutual
/-- **`vRL_[] = vC`.** -/
theorem vRLs_nil : ∀ (δ : LSub) (A : VTy), vRLs [] δ A [] = fun ls v => vC true A ls δ v
  | δ, .thunk C => by
      funext ls f; funext ρ
      show RelendableS δ [] [] (fun αs' ls' => cRLs [] δ C αs' ls' (forceE C (.val f))) [] ls ρ = _
      rw [propext relendableS_nil, cRLs_nil δ C]; rfl
  | δ, .tensor A B => by
      funext ls v
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆
        vRLs [] δ A [] ls v₁ ⋆ vRLs [] δ B [] ls v₂) = _
      rw [vRLs_nil δ A, vRLs_nil δ B]; rfl
  | δ, .sum A B => by
      funext ls v
      show BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRLs [] δ A [] ls v₁)
        (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRLs [] δ B [] ls v₂) = _
      rw [vRLs_nil δ A, vRLs_nil δ B]; rfl
  | δ, .bang A => by
      funext ls v
      show (fun ρ => ρ = PMap.empty ∧ vRLs [] δ A [] ls v ρ) = _
      rw [vRLs_nil δ A]; rfl
  | δ, .box a A => by
      funext ls v
      show atLife (extS δ [] []) a (fun α => box α (vRLs [] δ A [] ls v)) = _
      rw [vRLs_nil δ A]; rfl
  | δ, .ref A => by
      funext ls v
      show (ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vRLs [] δ A [] ls v') = _
      rw [vRLs_nil δ A]; rfl
  | _, .unit => rfl
  | _, .zero => rfl
  | _, .imm _ _ => rfl
  | _, .mut _ _ => rfl
  | _, .unk => rfl
  | _, .tvar _ => rfl
  | _, .mu _ => rfl
  | _, .int _ => rfl
  | _, .fam _ => rfl
  | _, .opq _ => rfl
termination_by structural _ A => A
/-- **`cRL_[] = cC`.** -/
theorem cRLs_nil : ∀ (δ : LSub) (C : CTy), cRLs [] δ C [] = fun ls e => cC C ls δ e
  | δ, .ret B => by
      funext ls e
      show wpTS ls e (fun ls'' v => vRLs [] δ B [] ls'' v) = _
      rw [vRLs_nil δ B]; rfl
  | δ, .eff n i q A B C => by
      funext ls e ρ
      exact propext (bodyS_nil_iff (Q' := effRet C δ)
        (fun ls v ρ => by rw [effRetS_nil δ C]))
  | δ, .arr A C => by
      funext ls e
      show (fun ρ => ∀ v, (vRLs [] δ A [] ls v ─⋆ cRLs [] δ C [] ls (.app e (.val v))) ρ) = _
      rw [vRLs_nil δ A, cRLs_nil δ C]; rfl
  | δ, .amp C D => by
      funext ls e
      show (fun ρ => cRLs [] δ C [] ls (.app e (.val (.inj₁ .unit))) ρ ∧
        cRLs [] δ D [] ls (.app e (.val (.inj₂ .unit))) ρ) = _
      rw [cRLs_nil δ C, cRLs_nil δ D]; rfl
  | _, .top => rfl
  | δ, .all x c C => by
      have ih := fun α : Life => cRLs_nil (δ.extend x α) C
      funext ls e
      show (fun ρ => ∀ α : Life, (⌜LtLife (extS δ [] []) c α⌝ ─⋆
        cRLs [] (δ.extend x α) C [] ls (.app e (.val .unit))) ρ) = _
      simp only [ih]; rfl
  | _, .nu _ => rfl
termination_by structural _ C => C
/-- The answer relation at `[]` is the kernel's. -/
theorem effRetS_nil : ∀ (δ : LSub) (C : CTy), effRetS [] δ C [] = effRet C δ
  | δ, .ret A => by
      show (fun ls v => vRLs [] δ A [] ls v) = _
      rw [vRLs_nil δ A]; rfl
  | δ, .eff _ _ _ _ _ C => effRetS_nil δ C
  | _, .arr _ _ => rfl
  | _, .amp _ _ => rfl
  | _, .top => rfl
  | _, .all _ _ _ => rfl
  | _, .nu _ => rfl
termination_by structural _ C => C
end

theorem gSepRLs_nil (δ : LSub) (ls : List SRec) :
    ∀ (Γ : Ctx VTy) (γ : List Val), gSepRLs [] δ [] ls Γ γ = gSepC ls δ Γ γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      simp only [gSepRLs, gSepC, gSepRLs_nil δ ls Γ γ, vRLs_nil]

theorem gRLs_nil (δ : LSub) (ls : List SRec) (Γ : Ctx VTy) (γ : List Val) :
    gRLs [] δ [] ls Γ γ = gDenC ls δ Γ γ := by
  simp only [gRLs, gDenC, gSepRLs_nil]

/-- **GFP at `σ = []` is the fundamental property.** -/
theorem gfpAt_nil_iff :
    GFPAt [] ↔ ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerives Δ Γ e j → SemJ Δ Γ e j := by
  have hwf : ∀ Δ : LifeCtx, LStack.WF [] Δ := fun _ => ⟨by simp, List.nodup_nil⟩
  have htab : ∀ ρ, TabAtS [] [] ρ := fun _ => ⟨by simp, by simp⟩
  have hsem : ∀ Δ Γ e j, SemJ Δ Γ e j ↔ ∀ δ γ (ls : List SRec) ρ, Δ.Models δ →
      gDenC ls δ Γ γ ρ → cC (jdgCty j) ls δ (substAll γ e) ρ := by
    intro Δ Γ e j; cases j <;> rfl
  constructor
  · intro H Δ Γ e j h
    refine (hsem Δ Γ e j).mpr fun δ γ ls ρ hδ hg => ?_
    have := H Δ Γ e j h (hwf Δ) δ [] rfl List.IsChain.nil hδ ls γ ρ (htab ρ)
      (by rw [gRLs_nil]; exact hg)
    rwa [cRLs_nil] at this
  · intro H Δ Γ e j h _ δ αs hlen _ hδ ls γ ρ _ hg
    obtain rfl : αs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [cRLs_nil]
    rw [gRLs_nil] at hg
    exact (hsem Δ Γ e j).mp (H Δ Γ e j h) δ γ ls ρ hδ hg

/-- **GFP holds at `σ = []`**: it is `fundamentalC`. -/
theorem gfpAt_nil : GFPAt [] := gfpAt_nil_iff.mpr fun _ _ _ _ h => fundamentalC h

/-! ### The stacked `U` clause: `[force]` and `thunk` -/

section
variable {σ : LStack} {δ : LSub}

theorem reLend_refl {αs : List Life} (h : List.IsChain (· < ·) αs) : ReLend αs αs :=
  ⟨List.forall₂_same.mpr fun _ _ => le_rfl, h⟩

theorem forall₂_le_trans : ∀ {a b c : List Life}, List.Forall₂ (· ≤ ·) a b →
    List.Forall₂ (· ≤ ·) b c → List.Forall₂ (· ≤ ·) a c
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons h₁ t₁, .cons h₂ t₂ => .cons (le_trans h₁ h₂) (forall₂_le_trans t₁ t₂)

theorem reLend_trans {a b c : List Life} (h₁ : ReLend a b) (h₂ : ReLend b c) : ReLend a c :=
  ⟨forall₂_le_trans h₁.1 h₂.1, h₁.2⟩

theorem getLast?_le : ∀ {a b : List Life}, List.Forall₂ (· ≤ ·) a b →
    ∀ x ∈ a.getLast?, ∃ y ∈ b.getLast?, x ≤ y
  | [], [], .nil, _, h => by simp at h
  | [x], [y], .cons h .nil, x', hx => by
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hx
      subst hx; exact ⟨y, rfl, h⟩
  | _ :: x₂ :: a, _ :: y₂ :: b, .cons _ t, x', hx => by
      simpa only [List.getLast?_cons_cons] using getLast?_le t x' (by simpa using hx)

/-- A share strictly above the outermost lend is strictly above it at every re-lend. -/
theorem stratS_mono {αs' αs : List Life} (hr : ReLend αs' αs) {ρ : WRes} (h : stratS αs ρ) :
    stratS αs' ρ := fun x hx => by
  obtain ⟨y, hy, hle⟩ := getLast?_le hr.1 x hx
  exact (h y hy).mono hle

/-- **`[force]` at the stack**: the `U` clause at the re-lend `αs′ = αs`, the dropped views handed
back. -/
theorem force_RLs {C : CTy} {αs : List Life} (hc : List.IsChain (· < ·) αs) {ls : List SRec}
    {f : Val} {ρ : WRes} (h : vRLs σ δ (.thunk C) αs ls f ρ) :
    cRLs σ δ C αs ls (forceE C (.val f)) ρ := by
  obtain ⟨ds, ρz, ρn, hcomp, hn, -, hth⟩ := h
  exact hth ls (Ext.refl ls ρz) αs (reLend_refl hc) ρn ρ hn hcomp

/-- **A `U` slot thaws by construction, at the stack**: frozen at `αs` and re-lent at any `αs′`,
it is a `vRL_σ` value at `αs′`. -/
theorem relendableS_thunk {C : CTy} {αs : List Life} {ls : List SRec} {f : Val} {ρ : WRes}
    (h : vRLs σ δ (.thunk C) αs ls f ρ) :
    RelendableS δ [] σ (fun αs' ls' => vRLs σ δ (.thunk C) αs' ls' f) αs ls ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := h
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  exact ⟨ds, ρz, ρv, hcv, hv, stratS_mono hr hz,
    fun ls'' he' αs'' hr' => hth ls'' (he.trans he') αs'' (reLend_trans hr' hr)⟩

/-- **`thunk M : U (F A)` at the stack**: a closure over a re-lendable context is in `vRL_σ`, its
body read at every re-lend from the thawed context. -/
theorem thunkF_RLs {G : List Life → List SRec → WProp} {M : Expr} {A : VTy} {γ : List Val}
    {αs : List Life} {ls : List SRec} {ρ : WRes} (hG : RelendableS δ [] σ G αs ls ρ)
    (hM : ∀ αs', ReLend αs' αs → ∀ ls' τ, G αs' ls' τ →
      cRLs σ δ (.ret A) αs' ls' (substAll (Val.unit :: γ) M) τ) :
    vRLs σ δ (.thunk (.ret A)) αs ls (Val.lam (Expr.psub 1 γ M)) ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := hG
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  refine wpTS_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← substAll_cons_l]
  exact hM αs' hr ls' τ (hth ls' he αs' hr ρv τ hv hcv)

/-- **`thunk M : U (F_Σ R)` at the stack**: as `thunkF_RLs`, the body a piece at Σ's table. -/
theorem thunkE_RLs {G : List Life → List SRec → WProp} {M : Expr} {n i : UInt32} {q : Qual}
    {A B : VTy} {C : CTy} {γ : List Val} {αs : List Life} {ls : List SRec} {ρ : WRes}
    (hG : RelendableS δ [] σ G αs ls ρ)
    (hM : ∀ αs', ReLend αs' αs → ∀ ls' τ, G αs' ls' τ →
      cRLs σ δ (.eff n i q A B C) αs' ls' (substAll (Val.unit :: γ) M) τ) :
    vRLs σ δ (.thunk (.eff n i q A B C)) αs ls (Val.lam (Expr.psub 1 γ M)) ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := hG
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ls' he αs' hr ρv τ hv hcv => ?_⟩
  refine wpG_step (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls' _ τ ?_
  rw [← substAll_cons_l]
  exact hM αs' hr ls' τ (hth ls' he αs' hr ρv τ hv hcv)

end

/-! ### The `withbor` rows at `σ·new`: D16.1's piece is #268's nested piece -/

section withbor
variable {δ : LSub} {Tab : OpTab}

theorem dropE_noOwn {e : LEnt} {d : Bool} {ρ : WRes} (h : dropE e d ρ) : NoOwn ρ := by
  cases d with
  | false => obtain ⟨rfl, -⟩ := h; exact noOwn_empty
  | true =>
      obtain ⟨ψ, rfl, hk⟩ := h
      obtain ⟨l, x, T, k, cr⟩ := e
      cases k <;> exact ResU.restrict_single_other (by simp only at hk; rw [hk]; simp)

theorem dropS_noOwn : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {ρ : WRes},
    dropS seen σ ds ρ → NoOwn ρ
  | _, [], [], _, h => by obtain ⟨rfl, -⟩ := h; exact noOwn_empty
  | _, _ :: _, _ :: _, _, ⟨_, _, hc, h₁, h₂⟩ => noOwn_compS hc (dropE_noOwn h₁) (dropS_noOwn h₂)
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

theorem dropS_length : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {ρ : WRes},
    dropS seen σ ds ρ → ds.length = σ.length
  | _, [], [], _, _ => rfl
  | _, _ :: _, _ :: _, _, ⟨_, _, _, _, h₂⟩ => by simp [dropS_length h₂]
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

/-- A garbage part beside a run's start joins its leftover. -/
theorem wpG_absorb {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} {X g Y : WRes}
    (h : wpG ls e Q X) (hg : NoOwn g) (hc : ResU.CompS X g Y) : wpG ls e Q Y :=
  wpG_garbage (wpG_mono (fun _ _ _ ⟨τ₁, τ₂, hcτ, hq, hn⟩ => ⟨τ₁, τ₂, hcτ, hn, hq⟩)
    (wpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ h => h) Y ⟨X, g, hc, h, hg⟩))

/-- `#268`'s nested post at the inner lend `α₂` of `ℓ′`, the outer at `α₁`. -/
def NPost (l' : BoCa.Loc) (T' : VTy) (δ : LSub) (Qa : List SRec → Val → WProp) (Tb : Table)
    (Y : List SRec → Expr → WProp) (α₂ α₁ : Life) (ls : List SRec) (t : Expr) : WProp :=
  box α₂ (ownWand l' T' δ ls (owner l' T' δ ls ⋆
    box α₁ (fun σ => valPost Qa ls t σ ∨ Tb ls t Y σ)))

theorem depth_two {cri : UInt32 → Bool} {l' : BoCa.Loc} {xi : LifeVar} {T' : VTy} {eo : LEnt}
    {n : UInt32} (h₁ : cri n = true) (h₂ : eo.cross n = true) :
    depth [⟨l', xi, T', .mut, cri⟩, eo] n = 2 := by
  simp [depth, List.takeWhile, h₁, h₂]

theorem tabK_two {σ : LStack} (hd : ∀ n i en, Tab n i = some en → depth σ n = 2) :
    tabK σ 2 Tab = Tab := by
  funext n i
  unfold tabK
  cases hT : Tab n i with
  | none => split <;> rfl
  | some en => rw [if_pos (hd n i en hT)]

theorem tabK_ne {σ : LStack} (hd : ∀ n i en, Tab n i = some en → depth σ n = 2) {k : Nat}
    (hk : k ≠ 2) : ∀ n i, tabK σ k Tab n i = none := by
  intro n i
  unfold tabK
  cases hT : Tab n i with
  | none => split <;> rfl
  | some en => rw [if_neg (by rw [hd n i en hT]; exact fun h => hk h.symm)]

/-- **A run's postcondition at `[new, outer]`, read as `#268`'s nested post.** Every stop of the
table crosses both lends, so only depth `2` stops occur: they ghost-end both, and are `nestF`'s
stop. An answer is the callback's: the new lend ends, the outer's stratum. Dropped views are
garbage. -/
theorem post_nest {l' : BoCa.Loc} {xi : LifeVar} {T' : VTy} {cri : UInt32 → Bool} {eo : LEnt}
    (hcross : ∀ n i en, Tab n i = some en → cri n = true ∧ eo.cross n = true)
    {Qa : List SRec → Val → WProp} {M : XT} {Y : List SRec → Expr → WProp} {α₂ α₁ : Life}
    (hMY : ∀ ds' ls' e' ρ', ds'.length = 2 → M 2 ds' [α₂, α₁] [] ls' e' ρ' → Y ls' e' ρ')
    {ls'' : List SRec} {t : Expr} {τ : WRes}
    (hq : valPost (fun ls v => ghostS δ [⟨l', xi, T', .mut, cri⟩, eo] [α₂, α₁] ls (Qa ls v))
        ls'' t τ ∨ stopS δ [⟨l', xi, T', .mut, cri⟩, eo] Tab M [α₂, α₁] ls'' t τ) :
    ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ τ ∧ NoOwn τ₂ ∧
      NPost l' T' δ Qa (opTable Tab) Y α₂ α₁ ls'' t τ₁ := by
  have hd : ∀ n i en, Tab n i = some en → depth [⟨l', xi, T', .mut, cri⟩, eo] n = 2 :=
    fun n i en h => depth_two (hcross n i en h).1 (hcross n i en h).2
  have hb1 : ∀ {R R' : WProp}, Entails R R' → Entails (boxTop [α₂, α₁] R) (box α₁ R') :=
    fun h ρ hp => ⟨h ρ hp.1, hp.2 α₁ rfl⟩
  rcases hq with ⟨v, rfl, hv⟩ | ⟨k, ds', ρ₁, ρ₂, hc, hdr, hg⟩
  · refine ⟨τ, PMap.empty, ResU.comp_empty_right τ, noOwn_empty, ?_⟩
    exact box_mono (ownWand_mono fun _ ⟨a, b, hc, ha, hb⟩ =>
      ⟨a, b, hc, ha, hb1 (fun _ h => Or.inl ⟨v, rfl, h⟩) b hb⟩) τ hv
  · refine ⟨ρ₂, ρ₁, ResU.CompS.comm hc, dropS_noOwn hdr, ?_⟩
    rcases k with _ | _ | _ | k
    · exact absurd hg (opTable_none (tabK_ne hd (by decide)))
    · exact box_mono (ownWand_mono fun _ ⟨a, b, hc, ha, hb⟩ =>
        ⟨a, b, hc, ha, (opTable_none (tabK_ne hd (by decide)) hb.1).elim⟩) ρ₂ hg
    · have hlen : ds'.length = 2 := dropS_length hdr
      rw [tabK_two hd] at hg
      exact box_mono (ownWand_mono fun _ ⟨a, b, hc, ha, hb⟩ =>
        ⟨a, b, hc, ha, hb1 (fun _ h => Or.inr (opTable_mono _ _ _ _ _ _
          (fun ls' e' ρ' hR => hMY ds' ls' e' ρ' hlen (relendableN_nil.mp hR)) h)) b hb⟩) ρ₂ hg
    · exact box_mono (ownWand_mono fun _ ⟨a, b, hc, ha, hb⟩ =>
        ⟨a, b, hc, ha, (opTable_none (tabK_ne hd (by omega)) hb.1).elim⟩) ρ₂ hg

/-- The views a re-lend hands a reborrow stack: the inner entry's only, the outer shadowed. -/
theorem vwS_reb {l : BoCa.Loc} {xi xo : LifeVar} {T To : VTy} {ko : LKind}
    {cri cro : UInt32 → Bool} {d₂ d₁ : Bool} {α₂ α₁ : Life} {ls : List SRec} {ρ : WRes}
    (h : vwE δ ⟨l, xi, T, .mut, cri⟩ d₂ α₂ ls ρ) :
    vwS δ [] [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, To, ko, cro⟩] [d₂, d₁] [α₂, α₁] ls ρ := by
  show (vwE δ _ (vis [] ⟨l, xi, T, .mut, cri⟩ d₂) α₂ ls ⋆
    (vwE δ _ (vis [l] ⟨l, xo, To, ko, cro⟩ d₁) α₁ ls ⋆ emp)) ρ
  have h₀ : vis [] ⟨l, xi, T, .mut, cri⟩ d₂ = d₂ := by simp [vis]
  have h₁ : vis [l] ⟨l, xo, To, ko, cro⟩ d₁ = false := by simp [vis]
  rw [h₀, h₁]
  exact ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, PMap.empty, PMap.empty,
    ResU.comp_empty_right _, ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩

/-- The views a re-lend hands a stack of two places: both. -/
theorem vwS_two {l' l : BoCa.Loc} (hne : l' ≠ l) {xi xo : LifeVar} {T' T : VTy}
    {cri cro : UInt32 → Bool} {d₂ d₁ : Bool} {α₂ α₁ : Life} {ls : List SRec} {ρ₂ ρ₁ ρ : WRes}
    (h₂ : vwE δ ⟨l', xi, T', .mut, cri⟩ d₂ α₂ ls ρ₂) (h₁ : vwE δ ⟨l, xo, T, .mut, cro⟩ d₁ α₁ ls ρ₁)
    (hc : ResU.CompS ρ₂ ρ₁ ρ) :
    vwS δ [] [⟨l', xi, T', .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] [d₂, d₁] [α₂, α₁] ls ρ := by
  show (vwE δ _ (vis [] ⟨l', xi, T', .mut, cri⟩ d₂) α₂ ls ⋆
    (vwE δ _ (vis [l'] ⟨l, xo, T, .mut, cro⟩ d₁) α₁ ls ⋆ emp)) ρ
  have h₀ : vis [] ⟨l', xi, T', .mut, cri⟩ d₂ = d₂ := by simp [vis]
  have h₁' : vis [l'] ⟨l, xo, T, .mut, cro⟩ d₁ = d₁ := by simp [vis, Ne.symm hne]
  rw [h₀, h₁']
  exact ⟨ρ₂, ρ₁, hc, h₂, ρ₁, PMap.empty, ResU.comp_empty_right _, h₁, ⟨rfl, trivial⟩⟩

/-- A view handed at a re-lend: fed to the piece if its flag asks for it, else left as garbage. -/
theorem view_split {e : LEnt} (he : e.k = .mut) {d : Bool} {α : Life} {ls : List SRec}
    {ρv : WRes} (hv : viewP e.l e.T δ α ls ρv) :
    ∃ a g, ResU.CompS a g ρv ∧ vwE δ e d α ls a ∧ NoOwn g := by
  cases d with
  | true =>
      refine ⟨ρv, PMap.empty, ResU.comp_empty_right ρv, ?_, noOwn_empty⟩
      obtain ⟨l, x, T, k, cr⟩ := e; subst he; exact hv
  | false => exact ⟨PMap.empty, ρv, compS_empty_left ρv, ⟨rfl, trivial⟩, noOwn_ptoMutS hv⟩

/-- **The reborrow (`withbor` (3)) at `σ·new`**: D16.1's piece at `[new, outer]`, `new` lending
`outer`'s place again and every stop of the callback's row crossing both, is `NestRelend`. By
induction on `OpenS`: each unfolding at the outer lend `α₁` and the inner `α₂ ⊏ α₁` is one
`openFS` at the re-lend `[α₂, α₁]`. -/
theorem nestRelend_of_openS {l : BoCa.Loc} {T : VTy} {xi xo : LifeVar} {To : VTy} {ko : LKind}
    {cri cro : UInt32 → Bool} (hcross : ∀ n i en, Tab n i = some en → cri n = true ∧ cro n = true)
    {Qa : List SRec → Val → WProp} {d₂ d₁ : Bool} {a₂ a₁ : Life} (ha : a₂ < a₁)
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenS δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, To, ko, cro⟩] Tab
      (fun αs ls v => ghostS δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, To, ko, cro⟩] αs ls (Qa ls v))
      2 [d₂, d₁] [a₂, a₁] [] ls e ρ) :
    NestRelend (opTable Tab) l T δ Qa ls e ρ := by
  refine h (fun k ds αi αo ls e ρ => k = 2 → αo = [] → ds.length = 2 →
      (∃ b₂ b₁, αi = [b₂, b₁] ∧ b₂ < b₁) → NestRelend (opTable Tab) l T δ Qa ls e ρ)
    ?_ rfl rfl rfl ⟨a₂, a₁, rfl, ha⟩
  rintro k ds αi αo ls e ρ hF rfl rfl hlen ⟨b₂, b₁, rfl, hb⟩
  obtain ⟨d₂, d₁, rfl⟩ : ∃ d₂ d₁, ds = [d₂, d₁] := by
    match ds, hlen with
    | [d₂, d₁], _ => exact ⟨d₂, d₁, rfl⟩
  refine nestRelend_fold (opTable_mono Tab) ⟨b₂, fun α₁ hα₁ => ?_⟩
  have hrun : ∀ α₂, α₂ < α₁ → _ := fun α₂ (h₂ : α₂ < α₁) =>
    hF [α₂, α₁] (.cons (lt_trans h₂ hα₁) (.cons (lt_trans hα₁ hb) .nil))
      (List.isChain_pair.mpr h₂)
  have hz : ρ.InStratum α₁ := (hrun _ (down_lt α₁)).2 α₁ rfl
  refine ⟨fun α₂ h₂ => ⟨fun ρv τ hv hcv => ?_, hz.mono (le_of_lt h₂)⟩, hz⟩
  have hgo : ∀ a W, vwE δ ⟨l, xi, T, .mut, cri⟩ d₂ α₂ ls a → ResU.CompS ρ a W →
      wpG ls e (fun ls'' t => NPost l T δ Qa (opTable Tab) (NestRelend (opTable Tab) l T δ Qa)
        α₂ α₁ ls'' t) W := fun a W ha hc =>
    wpG_garbage (wpG_mono (fun ls'' t τ' hq => post_nest hcross
      (fun ds' ls' e' ρ' hl hM => hM rfl rfl hl ⟨α₂, α₁, rfl, h₂⟩) hq)
      ((hrun α₂ h₂).1 a W (vwS_reb ha) hc))
  obtain ⟨a, g, hag, ha, hg⟩ := view_split (e := ⟨l, xi, T, .mut, cri⟩) rfl (d := d₂) hv
  obtain ⟨W, hW, hWτ⟩ := compS_reassoc' hag hcv
  exact wpG_absorb (hgo a W ha hW) hg hWτ

/-- **A lend of another place (`withbor` (1)–(2)) at `σ·new`**: D16.1's piece at `[new, outer]`,
`new` lending `ℓ′ ≠ ℓ` and every stop crossing both, is `NestRelend₂`. -/
theorem nestRelend₂_of_openS {l' l : BoCa.Loc} (hne : l' ≠ l) {T' T : VTy} {xi xo : LifeVar}
    {cri cro : UInt32 → Bool} (hcross : ∀ n i en, Tab n i = some en → cri n = true ∧ cro n = true)
    {Qa : List SRec → Val → WProp} {d₂ d₁ : Bool} {a₂ a₁ : Life} (ha : a₂ < a₁)
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenS δ [⟨l', xi, T', .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] Tab
      (fun αs ls v => ghostS δ [⟨l', xi, T', .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] αs ls (Qa ls v))
      2 [d₂, d₁] [a₂, a₁] [] ls e ρ) :
    NestRelend₂ (opTable Tab) l T δ l' T' Qa ls e ρ := by
  refine h (fun k ds αi αo ls e ρ => k = 2 → αo = [] → ds.length = 2 →
      (∃ b₂ b₁, αi = [b₂, b₁] ∧ b₂ < b₁) → NestRelend₂ (opTable Tab) l T δ l' T' Qa ls e ρ)
    ?_ rfl rfl rfl ⟨a₂, a₁, rfl, ha⟩
  rintro k ds αi αo ls e ρ hF rfl rfl hlen ⟨b₂, b₁, rfl, hb⟩
  obtain ⟨d₂, d₁, rfl⟩ : ∃ d₂ d₁, ds = [d₂, d₁] := by
    match ds, hlen with
    | [d₂, d₁], _ => exact ⟨d₂, d₁, rfl⟩
  refine nestRelend₂_fold (opTable_mono Tab) ⟨b₂, fun α₁ hα₁ => ?_⟩
  have hrun : ∀ α₂, α₂ < α₁ → _ := fun α₂ (h₂ : α₂ < α₁) =>
    hF [α₂, α₁] (.cons (lt_trans h₂ hα₁) (.cons (lt_trans hα₁ hb) .nil))
      (List.isChain_pair.mpr h₂)
  have hz : ρ.InStratum α₁ := (hrun _ (down_lt α₁)).2 α₁ rfl
  refine ⟨fun α₂ h₂ => ⟨fun ρv' τ₁ hv' hc₁ ρv τ hv hc => ?_, hz.mono (le_of_lt h₂)⟩, hz⟩
  have hgo : ∀ a₂' a₁' W₁ W, vwE δ ⟨l', xi, T', .mut, cri⟩ d₂ α₂ ls a₂' →
      vwE δ ⟨l, xo, T, .mut, cro⟩ d₁ α₁ ls a₁' → ResU.CompS ρ a₂' W₁ → ResU.CompS W₁ a₁' W →
      wpG ls e (fun ls'' t => NPost l' T' δ Qa (opTable Tab)
        (NestRelend₂ (opTable Tab) l T δ l' T' Qa) α₂ α₁ ls'' t) W := by
    intro a₂' a₁' W₁ W h₂' h₁' hc₂ hc₁'
    obtain ⟨w, hw, hρw⟩ := compS_reassoc hc₂ hc₁'
    exact wpG_garbage (wpG_mono (fun ls'' t τ' hq => post_nest hcross
      (fun ds' ls' e' ρ' hl hM => hM rfl rfl hl ⟨α₂, α₁, rfl, h₂⟩) hq)
      ((hrun α₂ h₂).1 w W (vwS_two hne h₂' h₁' hw) hρw))
  obtain ⟨a₂', g₂, hag₂, ha₂, hg₂⟩ := view_split (e := ⟨l', xi, T', .mut, cri⟩) rfl (d := d₂) hv'
  obtain ⟨a₁', g₁, hag₁, ha₁, hg₁⟩ := view_split (e := ⟨l, xo, T, .mut, cro⟩) rfl (d := d₁) hv
  -- `τ = ((ρ ● a₂′) ● a₁′) ● g₁ ● g₂`
  obtain ⟨W₁, hW₁, hW₁τ₁⟩ := compS_reassoc' hag₂ hc₁
  obtain ⟨V, hV, hVτ⟩ := compS_exch hW₁τ₁ hc
  obtain ⟨W, hW, hWV⟩ := compS_reassoc' hag₁ hV
  exact wpG_absorb (wpG_absorb (hgo a₂' a₁' W₁ W ha₂ ha₁ hW₁ hW) hg₁ hWV) hg₂ hVτ

/-- **The `withbor` (3) row at `σ·new`, `|σ| = 1`**: the stack folds back by `nested_relend`. -/
theorem withbor_reborrow_RLs (hLR : LinResume Tab) {l : BoCa.Loc} {T : VTy} {β : Life}
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) {xi xo : LifeVar} {To : VTy}
    {ko : LKind} {cri cro : UInt32 → Bool}
    (hcross : ∀ n i en, Tab n i = some en → cri n = true ∧ cro n = true)
    {Qa : List SRec → Val → WProp} {d₂ d₁ : Bool} {a₂ a₁ : Life} (ha : a₂ < a₁)
    {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenS δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, To, ko, cro⟩] Tab
      (fun αs ls v => ghostS δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, To, ko, cro⟩] αs ls (Qa ls v))
      2 [d₂, d₁] [a₂, a₁] [] ls e ρ) :
    Relend (opTable Tab) l T δ (fun ls v => owner l T δ ls ⋆ Qa ls v) ls e ρ :=
  nested_relend Tab hLR l T δ β hP Qa (nestRelend_of_openS hcross ha h)

/-- **The `withbor` (1)–(2) row at `σ·new`, `|σ| = 1`**: the stack folds back by
`nested₂_relend`, the owner of `ℓ′` beside the piece. -/
theorem withbor_other_RLs (hLR : LinResume Tab) {l' l : BoCa.Loc} (hne : l' ≠ l) {T' T : VTy}
    {β' : Life} (hP' : ∀ ls w σ, vC true T' ls δ w σ → σ.InStratum β') {xi xo : LifeVar}
    {cri cro : UInt32 → Bool} (hcross : ∀ n i en, Tab n i = some en → cri n = true ∧ cro n = true)
    {Qa : List SRec → Val → WProp} {d₂ d₁ : Bool} {a₂ a₁ : Life} (ha : a₂ < a₁)
    {ls : List SRec} {e : Expr} {ρo ρ ρt : WRes} (ho : owner l' T' δ ls ρo)
    (h : OpenS δ [⟨l', xi, T', .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] Tab
      (fun αs ls v => ghostS δ [⟨l', xi, T', .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] αs ls (Qa ls v))
      2 [d₂, d₁] [a₂, a₁] [] ls e ρ) (hc : ResU.CompS ρo ρ ρt) :
    Relend (opTable Tab) l T δ (fun ls v => owner l T δ ls ⋆ (owner l' T' δ ls ⋆ Qa ls v))
      ls e ρt :=
  nested₂_relend Tab hLR l T δ l' T' β' hP' Qa ho (nestRelend₂_of_openS hne hcross ha h) hc

/-- The reborrow row at the outer lender: the outer owner beside D16.1's piece at `[new, outer]`
gives the piece's `ewpTS` (`nested_spans`). -/
theorem withbor_reborrow_spans (hLR : LinResume Tab) {l : BoCa.Loc} {T : VTy} {β : Life}
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) {xi xo : LifeVar} {To : VTy}
    {ko : LKind} {cri cro : UInt32 → Bool}
    (hcross : ∀ n i en, Tab n i = some en → cri n = true ∧ cro n = true)
    {Qa : List SRec → Val → WProp} {d₂ d₁ : Bool} {a₂ a₁ : Life} (ha : a₂ < a₁)
    (ls : List SRec) (e : Expr) :
    Entails (owner l T δ ls ⋆ OpenS δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, To, ko, cro⟩] Tab
      (fun αs ls v => ghostS δ [⟨l, xi, T, .mut, cri⟩, ⟨l, xo, To, ko, cro⟩] αs ls (Qa ls v))
      2 [d₂, d₁] [a₂, a₁] [] ls e)
      (ewpTS ls e (opTable Tab) (fun ls v => owner l T δ ls ⋆ Qa ls v)) := by
  rintro ρ ⟨ρo, ρr, hc, ho, hr⟩
  exact nested_spans Tab hLR l T δ β hP Qa ls e ρ
    ⟨ρo, ρr, hc, ho, nestRelend_of_openS hcross ha hr⟩

/-- The row of another place at the outer lender (`nested₂_spans`). -/
theorem withbor_other_spans (hLR : LinResume Tab) {l' l : BoCa.Loc} (hne : l' ≠ l) {T' T : VTy}
    {β β' : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β)
    (hP' : ∀ ls w σ, vC true T' ls δ w σ → σ.InStratum β') {xi xo : LifeVar}
    {cri cro : UInt32 → Bool} (hcross : ∀ n i en, Tab n i = some en → cri n = true ∧ cro n = true)
    {Qa : List SRec → Val → WProp} {d₂ d₁ : Bool} {a₂ a₁ : Life} (ha : a₂ < a₁)
    (ls : List SRec) (e : Expr) :
    Entails (owner l T δ ls ⋆ (owner l' T' δ ls ⋆
      OpenS δ [⟨l', xi, T', .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] Tab
        (fun αs ls v => ghostS δ [⟨l', xi, T', .mut, cri⟩, ⟨l, xo, T, .mut, cro⟩] αs ls (Qa ls v))
        2 [d₂, d₁] [a₂, a₁] [] ls e))
      (ewpTS ls e (opTable Tab) (fun ls v => owner l T δ ls ⋆ (owner l' T' δ ls ⋆ Qa ls v))) := by
  rintro ρ ⟨ρo, ρr, hc, ho, ρo', ρn, hc', ho', hn⟩
  exact nested₂_spans Tab hLR l T δ β hP l' T' β' hP' Qa ls e ρ
    ⟨ρo, ρr, hc, ho, ρo', ρn, hc', ho', nestRelend₂_of_openS hne hcross ha hn⟩

end withbor

/-! ### Every hypothesis discharged: a reborrow callback yielding with both lends open -/

section inst
variable {δ : LSub}

theorem vwE_noOwn {e : LEnt} {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwE δ e d α ls ρ) : NoOwn ρ := by
  cases d with
  | false => obtain ⟨rfl, -⟩ := h; exact noOwn_empty
  | true =>
      obtain ⟨l, x, T, k, cr⟩ := e
      cases k with
      | «mut» => exact noOwn_ptoMutS h
      | imm v => exact noOwn_ptoImmS h

theorem vwS_noOwn : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {αs : List Life}
    {ls : List SRec} {ρ : WRes}, vwS δ seen σ ds αs ls ρ → NoOwn ρ
  | _, [], [], [], _, _, h => by obtain ⟨rfl, -⟩ := h; exact noOwn_empty
  | _, _ :: _, _ :: _, _ :: _, _, _, ⟨_, _, hc, h₁, h₂⟩ =>
      noOwn_compS hc (vwE_noOwn h₁) (vwS_noOwn h₂)
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

theorem dropE_of_vwE {e : LEnt} {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwE δ e d α ls ρ) : dropE e d ρ := by
  cases d with
  | false => exact h
  | true =>
      obtain ⟨l, x, T, k, cr⟩ := e
      cases k with
      | «mut» => exact dropC_of_view h
      | imm v => obtain ⟨s, u, σ, hs, ls₀, rfl, -⟩ := h; exact ⟨_, rfl, rfl⟩

theorem vwS_length : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {αs : List Life}
    {ls : List SRec} {ρ : WRes}, vwS δ seen σ ds αs ls ρ → ds.length = σ.length ∧ αs.length = σ.length
  | _, [], [], [], _, _, _ => ⟨rfl, rfl⟩
  | _, _ :: _, _ :: _, _ :: _, _, _, ⟨_, _, _, _, h₂⟩ => by
      simp [(vwS_length h₂).1, (vwS_length h₂).2]
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

/-- **The views a re-lend hands are what a stop drops.** -/
theorem dropS_of_vwS : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool} {αs : List Life}
    {ls : List SRec} {ρ : WRes}, vwS δ seen σ ds αs ls ρ → dropS seen σ ds ρ
  | _, [], [], [], _, _, h => h
  | _, _ :: _, _ :: _, _ :: _, _, _, ⟨a, b, hc, h₁, h₂⟩ =>
      ⟨a, b, hc, dropE_of_vwE h₁, dropS_of_vwS h₂⟩
  | _, [], [], _ :: _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, h => h.elim

variable {σ : LStack} {Tab : OpTab} {Q : List Life → List SRec → Val → WProp}

/-- `OpenD_σ` is closed under a pure step in front. -/
theorem openS_step {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e e' : Expr}
    (hs : ∀ μ : Heap, Step1N μ e μ e') {ρ : WRes} (h : OpenS δ σ Tab Q k ds αi αo ls e' ρ) :
    OpenS δ σ Tab Q k ds αi αo ls e ρ :=
  openS_fold fun αi' h₁ h₂ => boxTop_mono (wand_mono_right (wpG_step hs ls _)) ρ
    (openS_unfold h αi' h₁ h₂)

/-- **A callback at an answer**, at a two-entry stack: the views are left behind and the answer
is the callback's. -/
theorem openS_val {l' : BoCa.Loc} {xi : LifeVar} {T' : VTy} {cri : UInt32 → Bool} {eo : LEnt}
    {Qa : List SRec → Val → WProp} {u : Val} (hu : ∀ ls, Qa ls u PMap.empty)
    (ds : List Bool) (αi : List Life) (ls : List SRec) :
    OpenS δ [⟨l', xi, T', .mut, cri⟩, eo] Tab
      (fun αs ls v => ghostS δ [⟨l', xi, T', .mut, cri⟩, eo] αs ls (Qa ls v))
      2 ds αi [] ls (.val u) PMap.empty := by
  refine openS_fold fun αi' hαi _ => ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
  rw [eq_of_compS_empty_left hc]
  obtain ⟨α₂, α₁, rfl⟩ : ∃ α₂ α₁, αi' = [α₂, α₁] := by
    have hl : αi'.length = 2 := (vwS_length hw).2
    match αi', hl with
    | [α₂, α₁], _ => exact ⟨α₂, α₁, rfl⟩
  refine wpG_garbage (wpG_here ls _ _ w ⟨PMap.empty, w, compS_empty_left w, vwS_noOwn hw,
    Or.inl ⟨u, rfl, ?_⟩⟩)
  refine ⟨fun w₀ ρa ρb ha hcab ρc ρd hv hccd => ?_, ResU.inStratum_empty α₂⟩
  rw [eq_of_compS_empty_left hcab] at hccd
  exact ⟨ρd, PMap.empty, ResU.comp_empty_right ρd, ⟨w₀, ρa, ρc, hccd, ha, hv⟩,
    hu ls, fun a _ => ResU.inStratum_empty a⟩

/-- **A callback at a yield crossing both lends**, at a two-entry stack: both views are dropped
(both lends ghost-ended), the inner owner is handed back beside the stop, and the continuation is
D16.1's piece again, re-lent below both. The yield is linear and resuming. -/
theorem openS_yield {l' : BoCa.Loc} {xi : LifeVar} {T' : VTy} {cri : UInt32 → Bool} {eo : LEnt}
    {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en) (hd : depth [⟨l', xi, T', .mut, cri⟩, eo] n = 2)
    (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {Qa : List SRec → Val → WProp} {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    (h : ∀ ls ds αi, OpenS δ [⟨l', xi, T', .mut, cri⟩, eo] Tab
      (fun αs ls v => ghostS δ [⟨l', xi, T', .mut, cri⟩, eo] αs ls (Qa ls v))
      2 ds αi [] ls rest PMap.empty)
    (ds : List Bool) (αi : List Life) (ls : List SRec) :
    OpenS δ [⟨l', xi, T', .mut, cri⟩, eo] Tab
      (fun αs ls v => ghostS δ [⟨l', xi, T', .mut, cri⟩, eo] αs ls (Qa ls v))
      2 ds αi [] ls (yieldSeq n i y rest) PMap.empty := by
  refine openS_fold fun αi' hαi _ => ⟨fun w W hw hc => ?_, fun a _ => ResU.inStratum_empty a⟩
  rw [eq_of_compS_empty_left hc]
  obtain ⟨α₂, α₁, rfl⟩ : ∃ α₂ α₁, αi' = [α₂, α₁] := by
    have hl : αi'.length = 2 := (vwS_length hw).2
    match αi', hl with
    | [α₂, α₁], _ => exact ⟨α₂, α₁, rfl⟩
  have hT2 : tabK [⟨l', xi, T', .mut, cri⟩, eo] 2 Tab n i = some en := by
    simp [tabK, hd, hTn]
  refine wpG_here ls _ _ w (Or.inr ⟨2, ds, w, PMap.empty, ResU.comp_empty_right w,
    dropS_of_vwS hw, ?_⟩)
  refine ⟨fun w₀ ρa ρb hown hcab ρc ρd hv hccd => ?_, ResU.inStratum_empty α₂⟩
  rw [eq_of_compS_empty_left hcab] at hccd
  refine ⟨ρd, PMap.empty, ResU.comp_empty_right ρd, ⟨w₀, ρa, ρc, hccd, hown, hv⟩, ?_,
    fun a _ => ResU.inStratum_empty a⟩
  refine Or.inl ⟨.seq .hole rest, n, i, y, en, pure_sep_mk ⟨rfl, rfl, hT2, ha⟩
    ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, hy ls, ?_⟩⟩
  refine ⟨fun _ => rfl, fun ls' _ => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  rw [eq_of_compS_empty_left hcτ]
  exact relendableN_nil.mpr
    (openS_step (fun μ => Step1N.head (Head.seq μ rest) rfl) (h ls' ds [α₂, α₁]))

open GhostEnd.Instance in
/-- **Every hypothesis discharged.** A reborrow callback that yields once with both lends open,
then returns `()`, at the row `{yield : I32 ↠ 1}`, written as D16.1's piece at `[new, outer]`:
the outer owner beside it gives its `ewpTS`, through `nestRelend_of_openS` and
`nested_relend`. -/
theorem withbor_reborrow_spans_yield (l : BoCa.Loc) (ls : List SRec) :
    Entails (owner l .unit δ ls)
      (ewpTS ls (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.val .unit))
        (opTable (Row.tab [yieldOp] δ)) (fun ls v => owner l .unit δ ls ⋆ ⌜v = Val.unit⌝)) := by
  have hLR : LinResume (Row.tab [yieldOp] δ) := by
    intro n i en hT
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    obtain ⟨hm, -, -⟩ := Row.find_mem hf
    simp only [List.mem_singleton] at hm
    subst hm
    exact ⟨rfl, rfl⟩
  have hP : ∀ ls w σ, vC true VTy.unit ls δ w σ → σ.InStratum ⊤ :=
    fun _ _ σ h => by rw [h.1]; exact ResU.inStratum_empty _
  let tt : UInt32 → Bool := fun _ => true
  intro ρ ho
  refine withbor_reborrow_spans hLR hP (xi := 1) (xo := 0) (To := .unit) (ko := .mut)
    (cri := tt) (cro := tt) (fun _ _ _ _ => ⟨rfl, rfl⟩) (d₂ := true) (d₁ := false)
    (a₂ := OrderDual.toDual 2) (a₁ := OrderDual.toDual 1)
    (show (2 : ℕ) > 1 from by decide) ls _ ρ ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ho, ?_⟩
  refine openS_yield (en := yieldOp.ent δ) (by simp [Row.tab, Row.find, yieldOp])
    (by simp [depth, tt]) rfl rfl ?_ (fun ls => ⟨rfl, 1, rfl⟩)
    (fun ls ds αi => openS_val (fun _ => ⟨rfl, rfl⟩) ds αi ls) _ _ ls
  intro ls w σ h
  simp only [OpSig.ent, yieldOp] at h
  exact ⟨h.2, h.1⟩

end inst

end GhostEnd
