import Core.Fundamental
import Core.TreePoolSpawnProgs

/-!
# #791's end goal at the tree relation: the statements  `[spec §62]`

`docs/new-core/goal-791.md` is the map. This file states, as elaborating `def … : Prop`, what #791
must prove, planned backwards from its end:

* **§1. The new rules.** Core's lend constants run their callback at a pure row (`withbor2`,
  `withbor3`, `withload`, `sliceBorrowM`) or at a row of abortive operations only (the unwinding
  forms, `Row.Unwind`). No rule of `CDerives` lets a lend's callback suspend. The rules #791 adds
  are the unwinding forms with `Row.Unwind` relaxed to `Row.Suspend` (non-abortive operations
  allowed, unrestricted ones not), plus the field reborrow `Mut @a (Ref A) ↝ Mut 'x A` the hardest
  case needs, which Core has no rule for (`withborFE`). They are listed as data (`Const791`); a
  program uses them as constants closed over a context (`ctx791`), so no judgment is added.
* **§2. The interpretation** `vT`/`cT`/`gT`/`SemJT` over `STy`/`SCmp`, the minimum the statements
  read. Formers outside #791's fragment (`μ`, type variables, `ν`) are read as empty.
* **§3. The top statements**: `Goal791Top` (a closed program at `F 1`, its scheduler typed inside
  it) and `Goal791Sched` (a task at a row, the scheduler at the program's top, through
  `poolSchedAdequacyT`).
* **§4. The rule-level statements**: one compatibility statement per rule the top needs.
* **§5. The hardest case** as a closed program and its two closed statements.
* **§6. Candidates A and B**: the relation-level statements each needs.
* **§7. Feasibility**: refuting configurations and small lemmas.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Goal791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.LogRel (substAll)
open BoCa.BoLo (hndE hndVal freeE Kont performE opPayload)

/-! ## §1. The new rules -/

/-- **The clauses `Row.Suspend` asks of a cancel row's layers**, recursively: each layer named,
not unrestricted, its payload and answer types free of `'x` and outliving every lifetime, and the
cancel row of each capturable layer likewise. A cancel run under a live lend stops at these
layers, so they meet what the row's own operations meet. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.SuspendC (x : LifeVar) : CTy → Prop
  | .eff n _ q A B fin _ C =>
      (q ≠ .unr ∧ n ≠ 0 ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ (∀ Δ a, VOutlives Δ a A) ∧
        (∀ Δ a, VOutlives Δ a B) ∧ (capB q B = true → SuspendC x fin)) ∧ SuspendC x C
  | _ => True

/-- **The row of a callback that may suspend inside a borrow of `'x`**: `Row.Unwind` without its
abort clause. Every operation is named, not unrestricted (a continuation resumed twice would lend
twice: SPEC §62, "Typing: suspension"), and its payload and answer types are free of `'x` and
outlive every lifetime; a capturable operation's cancel row meets the same clauses
(`CTy.SuspendC`). Decidable on the row given `VFree` and `VOutlives`. -/
def _root_.BoCa.Fig16.LogRel.Core.Row.Suspend (S : Row) (x : LifeVar) : Prop :=
  ∀ o ∈ S, o.q ≠ .unr ∧ o.n ≠ 0 ∧ ¬ VFree x o.A ∧ ¬ VFree x o.B ∧ (∀ Δ a, VOutlives Δ a o.A) ∧
    (∀ Δ a, VOutlives Δ a o.B) ∧ (capB o.q o.B = true → o.fin.SuspendC x)

theorem _root_.BoCa.Fig16.LogRel.Core.Row.Suspend.of_unwind {S : Row} {x : LifeVar} (h : S.Unwind x)
    (hq : ∀ o ∈ S, o.q ≠ .unr) : S.Suspend x := fun o ho =>
  ⟨hq o ho, (h o ho).2.1, (h o ho).2.2.1,
    by rw [OpSig.B_zero (h o ho).1]; exact id, (h o ho).2.2.2,
    by rw [OpSig.B_zero (h o ho).1]; exact fun _ _ => .zero,
    by rw [OpSig.B_zero (h o ho).1]; simp [capB, VTy.isZero]⟩

/-- **The field reborrow** `λr. λf. (f [] (load r)) then b. (r, b) unwind d r`: the callback gets
the boxed field's location, read out of the borrowed cell. `withborUE` with the source replaced
by its content. -/
def withborFE (d : Expr) : Expr :=
  .val (.lam (.val (.lam (thenE (.pair (.var 2) (.var 0)) (.app d (.var 2))
    (.app (.app (.var 0) (.val .unit)) (.app (.val (.prim .load)) (.var 1)))))))

/-- `withborFE` is a value. -/
def withborFV (d : Expr) : Val := ⟨withborFE d, .lam⟩

/-- `Mut @a (Ref A) ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a (Ref A) ⊗ B)`. -/
def withborFSTy (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) :
    VTy :=
  withborUTy (.mut a (.ref A)) (cbUTy x bnd (.mut (.var x) A) B S) S (.tensor (.mut a (.ref A)) B)

/-- **The constants #791 adds**, as data: each is an unwinding form whose callback row may
suspend. `w2` is `withbor2U`, `w3` `withbor3U`, `wl` `withloadU`, `sm` `sliceBorrowMU`, each with
`Row.Suspend` for `Row.Unwind`; `wF` is the field reborrow. -/
inductive Const791 where
  | w2 (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
  | w3 (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
  | wF (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
  | wl (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row)
  | sm (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)

/-- The constant's type. -/
def Const791.ty : Const791 → VTy
  | .w2 x bnd A B S _ => withbor2UTy x bnd A B S
  | .w3 a x bnd A B S _ => withbor3UTy a x bnd A B S
  | .wF a x bnd A B S _ => withborFSTy a x bnd A B S
  | .wl a x bnd A B S => withloadUTy a x bnd A B S
  | .sm x bnd A B S _ => sliceBorrowMUTy x bnd A B S

/-- The constant's value. -/
def Const791.val : Const791 → Val
  | .w2 _ _ _ _ _ d => withborUV d
  | .w3 _ _ _ _ _ _ d => withborUV d
  | .wF _ _ _ _ _ _ d => withborFV d
  | .wl _ _ _ _ _ _ => withloadV
  | .sm _ _ _ _ _ d => withborUV d

/-- **The rule's premises, at the empty lifetime context**: the corresponding `CDerives`
constructor's (`withbor2U`, `withbor3U`, `withloadU`, `sliceBorrowMU`), `hS : S.Unwind x` read as
`S.Suspend x`; the finaliser closed and typed. The field reborrow's are `withbor3U`'s at
`Mut @a (Ref A)`.

The first conjunct, `LifeCtx.empty.Defines bnd`, is where Core's rules get the callback bound's
interpretation: they fix the bound to `Δ.meetOfDom`, which every `δ ⊨ Δ` interprets
(`Lifetime.Life.interp_defined_of_wf`, `Lifetime.meetOfDomL_wf`; `withbor2U_compatX`,
`Core/EffBorrow.lean`). The constants take any bound, so they carry the definedness as a premise;
`defines_meetOfDom_empty` shows Core's bound meets it. -/
def Const791.OK : Const791 → Prop
  | .w2 x bnd A B S d => LifeCtx.empty.Defines bnd ∧
      (∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b A) ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend x ∧ closedAt 0 d = true ∧
      CDerives LifeCtx.empty [] d (.val (.lolli (.ref A) .unit))
  | .w3 a x bnd A B S d => LifeCtx.empty.Defines bnd ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend x ∧ closedAt 0 d = true ∧
      CDerives LifeCtx.empty [] d (.val (.lolli (.mut a A) .unit))
  | .wF a x bnd A B S d => LifeCtx.empty.Defines bnd ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend x ∧ closedAt 0 d = true ∧
      CDerives LifeCtx.empty [] d (.val (.lolli (.mut a (.ref A)) .unit))
  | .wl _ x bnd A B S => LifeCtx.empty.Defines bnd ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend x
  | .sm x bnd A B S d => LifeCtx.empty.Defines bnd ∧
      (∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b A) ∧
      (∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b B) ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend x ∧ closedAt 0 d = true ∧
      CDerives LifeCtx.empty [] d (.val (.lolli (.array A) .unit))

/-- **Core's bound meets `Const791.OK`'s first conjunct**: `LifeCtx.empty.meetOfDom`, the bound
Core's rules fix at the empty context, is defined at every `δ`. -/
theorem defines_meetOfDom_empty : LifeCtx.empty.Defines LifeCtx.empty.meetOfDom :=
  fun _ hδ => Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)

/-- The context a program using the constants `cs` is typed in: each constant at `!` of its
type, live. -/
def ctx791 (cs : List Const791) : Ctx VTy := cs.map fun c => ⟨.bang c.ty, true⟩

/-- The values closing it. -/
def vals791 (cs : List Const791) : List Val := cs.map Const791.val

/-! ## §2. The interpretation -/

/-- The frame condition every interpretation is read at: a valid frame. It meets
`poolSchedAdequacyT`'s premises on `Fb` and `Fe` (`fv_base`, `fv_present`). -/
def FV : TFrame := fun _ ρf => ResUT.Valid ρf

theorem fv_base : ∀ (w : TWd) ρf, ResUT.Valid ρf → FV w ρf := fun _ _ h => h

theorem fv_present : ∀ (w : TWd) ρf, fdMask (fun _ => False) w ρf → FV w ρf := fun _ _ h => h.1

/-- **`F A` at a table**: a bare `cerwpT` run at every index up to the one read, owning no
records, at the frame conditions `FV`. Downward closed by its form. -/
def SCmp.retAt (Tb : TableT) (τ : STy) : SCmp where
  P n w ls e ρ := ∀ m, m ≤ n → cerwpT (ℍ := ℍ) Tb (postOf τ) FV FV m w ls [] e ρ
  down _ _ _ _ _ h m hm := h m (Nat.le_succ_of_le hm)

/-- The computation type of the formers outside the fragment: empty. -/
def SCmp.none : SCmp where
  P _ _ _ _ _ := False
  down _ _ _ _ _ h := h

/-- **An operation's entry at the tree**: the qualifier; abortive as Core's (`B` empty, not `lin`);
payload and answer read at their value types; the cancel branch owed where Core's `capB` reads a
cancel row (D15); the resumer guarantee the scheduler's (`fdJoinT`). -/
def entT (q : Qual) (B : VTy) (τA τB : STy) : OpEntT where
  q := q
  abort := B.isZero && q != .lin
  PA := fun n w ls v ρ => τA.P n w ls v ρ
  PBv := fun _ n w ls a σ => τB.P n w ls a σ
  fin := capB q B
  fd := fdJoinT
  oc := fun _ _ => True

/-- One more entry of a table. -/
def extTab (n i : UInt32) (en : OpEntT) (T : OpTabT) : OpTabT :=
  fun m j => if m = n ∧ j = i then some en else T m j

/-- A store code for a value type, where it has one (E1: `Mut`'s payload is a code). -/
def toCode (δ : LSub) : VTy → Option KTy
  | .unit => some .unit
  | .sum A B => match toCode δ A, toCode δ B with
    | some a, some b => some (.sum a b)
    | _, _ => none
  | .imm a A => match a.interp δ, toCode δ A with
    | some α, some c => some (.imm (OrderDual.toDual α) c)
    | _, _ => none
  | .mut a A => match a.interp δ, toCode δ A with
    | some α, some c => some (.mut (OrderDual.toDual α) c)
    | _, _ => none
  | .box a A => match a.interp δ, toCode δ A with
    | some α, some c => some (.box (OrderDual.toDual α) c)
    | _, _ => none
  | .ref A => (toCode δ A).map .ref
  | _ => none

mutual
/-- **`𝒱⟦A⟧δ` at the tree**, over `STy`'s formers. `Mut` at a payload with a store code (E1),
empty otherwise (#790). `μ` and type variables are outside #791's fragment and read as empty
(I11). A lifetime term with no interpretation at `δ` reads as empty. -/
def vT : VTy → LSub → STy
  | .unit, _ => STy.unit
  | .tensor A B, δ => STy.tensor (vT A δ) (vT B δ)
  | .zero, _ => STy.zero
  | .sum A B, δ => STy.sum (vT A δ) (vT B δ)
  | .thunk C, δ => STy.thunkC (cT C δ) (fun v => forceE C (.val v))
  | .ref A, δ => STy.ref (vT A δ)
  | .imm a A, δ => match a.interp δ with
    | some α => STy.imm (OrderDual.toDual α) (vT A δ)
    | none => STy.zero
  | .mut a A, δ => match a.interp δ, toCode δ A with
    | some α, some c => STy.mut (OrderDual.toDual α) c
    | _, _ => STy.zero
  | .box a A, δ => match a.interp δ with
    | some α => STy.box (OrderDual.toDual α) (vT A δ)
    | none => STy.zero
  | .bang A, δ => STy.bang (vT A δ)
  | .unk, _ => STy.unk
  | .tvar _, _ => STy.zero
  | .mu _, _ => STy.zero
  | .int wd, _ => STy.int wd
  | .fam L, δ => STy.fam (vT L δ)
  | .opq k, _ => STy.opq k
/-- **`𝒞⟦C⟧δ` at the tree.** `F_Σ R` is a run at the table of the row's layers, each entry
`entT`; `F A` the same at the empty table. `ν` is outside the fragment (I10). -/
def cT : CTy → LSub → SCmp
  | .ret A, δ => SCmp.retAt (opTableT OpTabT.empty) (vT A δ)
  | .arr A C, δ => SCmp.arr (vT A δ) (cT C δ)
  | .amp C D, δ => SCmp.amp (cT C δ) (cT D δ)
  | .top, _ => SCmp.top
  | .all x c C, δ => match c.interp δ with
    | some γ => SCmp.all (OrderDual.toDual γ) (fun α => cT C (δ.extend x (OrderDual.ofDual α)))
    | none => SCmp.none
  | .nu _, _ => SCmp.none
  | .eff n i q A B _ _ C, δ =>
      SCmp.retAt (opTableT (extTab n i (entT q B (vT A δ) (vT B δ)) (tabT C δ))) (retT C δ)
/-- The table of a row's layers below the top one. -/
def tabT : CTy → LSub → OpTabT
  | .eff n i q A B _ _ C, δ => extTab n i (entT q B (vT A δ) (vT B δ)) (tabT C δ)
  | _, _ => OpTabT.empty
/-- The answer type of a row's layers. -/
def retT : CTy → LSub → STy
  | .ret A, δ => vT A δ
  | .eff _ _ _ _ _ _ _ C, δ => retT C δ
  | _, _ => STy.zero
end

/-- **`𝒢⟦Γ⟧δγ` at the tree**: the live slots' values over a split of the resource. -/
def gT (δ : LSub) : Ctx VTy → List Val → TEnv
  | [], _ => fun _ _ _ ρ => ρ = PMap.empty
  | _ :: _, [] => fun _ _ _ ρ => ρ = PMap.empty
  | s :: Γ, v :: γ => if s.live then
      fun n w ls ρ => ∃ ρ₁ ρ₂ : TRes w.K, ResUT.CompS ρ₁ ρ₂ ρ ∧ (vT s.ty δ).P n w ls v ρ₁ ∧
        gT δ Γ γ n w ls ρ₂
    else gT δ Γ γ

/-- A judgment's computation type: `val A` is `F A`. -/
def jdgC : Jdg → CTy
  | .val A => .ret A
  | .comp C => C

/-- **`Δ; Γ ⊨ e : j` at the tree**, at every world, list and index, from every covered resource
meeting the context. `Δ.Models δ` is the chain's reading of lifetime contexts (I2: not restated
at a cactus). -/
def SemJT (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg) : Prop :=
  ∀ (δ : LSub) (γ : List Val) (n : Nat) (w : TWd) (ls : List (SRecT w.K)) (ρ : TRes w.K),
    Δ.Models δ → Ctx.LiveWithin Γ γ → gT δ Γ γ n w ls ρ → CovR (sem w.Θ) w.K ρ →
      (cT (jdgC j) δ).P n w ls (substAll γ e) ρ

/-- The scheduler's table for a task at the row `S`. -/
def rowTab (S : Row) : OpTabT := tabT (CTy.effOf S .unit) LSub.empty

/-! ## §3. The top statements -/

/-- **#791's end goal, closed programs.** Every program typed at `F 1` from the constants `cs`
(each meeting its rule's premises) is safe, leak-free, or diverges. A program that suspends
handles its operations inside itself, so its scheduler is a typed handler (#792's `[handle]`). -/
def Goal791Top : Prop :=
  ∀ (cs : List Const791), (∀ c ∈ cs, c.OK) → ∀ e : Expr,
    CDerives LifeCtx.empty (ctx791 cs) e (.comp (.ret .unit)) →
      OrDiverges (ℍ := ℍ) (substAll (vals791 cs) e)

/-- **#791's end goal under a scheduler at the top**, the form `poolSchedAdequacyT` reaches today:
a task typed at `F_Σ 1` from the constants, run by a scheduler meeting `SchedOKT` at the row's
table, its answers functions of its state, is safe, leak-free, or diverges. The scheduler is not
typed (`SchedOKT` is semantic). -/
def Goal791Sched : Prop :=
  ∀ (cs : List Const791), (∀ c ∈ cs, c.OK) → ∀ (S : Row) (e₀ : Expr),
    CDerives LifeCtx.empty (ctx791 cs) e₀ (.comp (CTy.effOf S .unit)) →
    ∀ (n₀ : UInt32) (qs hr hs : Val) (Q : TPostV) (Inv : List StoredJ → Prop),
      (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) → Inv [] →
      SchedOKT (ℍ := ℍ) (rowTab S) n₀ qs hr hs (postOf (retT (CTy.effOf S .unit) LSub.empty))
        (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv) →
      OrDiverges (ℍ := ℍ)
        (.app (hndE (hndVal n₀ qs hr hs) (substAll (vals791 cs) e₀))
          (stateVal (hndVal n₀ qs hr hs) []).1)

/-! ### What the top statements decompose into -/

/-- **The fundamental property at the tree**, over the existing judgment. -/
def FundamentalT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (j : Jdg), CDerives Δ Γ e j → SemJT (ℍ := ℍ) Δ Γ e j

/-- **The new constants are values of their types**, at `!`: the rule-level content of §1. -/
def ConstsT : Prop :=
  ∀ c : Const791, c.OK → ∀ (δ : LSub) (n : Nat) (w : TWd) (ls : List (SRecT w.K)),
    (vT (.bang c.ty) δ).P n w ls c.val PMap.empty

/-- **The adequacy bridge** (checklist I16): a closed run of `F 1` at the tree is `OrDiverges`. -/
def BridgeT : Prop :=
  ∀ e : Expr, (∀ P n, (cT (.ret .unit) LSub.empty).P n (w₀ P) [] e
    (PMap.empty : TRes (WCactus.ofParent P))) → OrDiverges (ℍ := ℍ) e


/-! ## §4. The rule-level statements

Each is the tree reading of one `CDerives` constructor: from the constructor's premises, `SemJT` of
its conclusion. The borrow constants are leaves (`Ctx.DeadP Γ`), so their statements read no
induction hypothesis. The chain lemma each ports is named in the docstring. -/

/-- `withbor (2)`: `Ref A` lent as `Mut 'x A` to a pure callback (`withbor2_compatX`,
`Core/Compatibility.lean`; 6.65). -/
def Withbor2T : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → Δ.find? x = none →
    (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) → ¬ VFree x A → ¬ VFree x B →
    SemJT (ℍ := ℍ) Δ Γ withbor (.val (BoCa.Fig16.LogRel.Core.axWithbor2Ty x Δ.meetOfDom A B))

/-- `withbor (3)`: `Mut @a A` reborrowed as `Mut 'x A` (`withbor3_compatX`; 6.66 then 6.65). -/
def Withbor3T : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ →
    Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemJT (ℍ := ℍ) Δ Γ withbor (.val (BoCa.Fig16.LogRel.Core.axWithbor3Ty a x Δ.meetOfDom A B))

/-- `withload`: `Imm @a A` reborrowed as `Imm̲ 'x A` (`withload_compatX`; the reborrow,
`TWNT.reb`/`rebDeep`). -/
def WithloadT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ →
    Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    SemJT (ℍ := ℍ) Δ Γ withload (.val (BoCa.Fig16.LogRel.Core.axWithloadTy a x Δ.meetOfDom A B))

/-- `withswap`: the Anti-Frame for a pure callback (`withswap_compatX`; 6.66). -/
def WithswapT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy), Ctx.DeadP Γ →
    SemJT (ℍ := ℍ) Δ Γ withswap (.val (BoCa.Fig16.LogRel.Core.axWithswapTy a A B))

/-- `slice_borrow_mut` (`sliceBorrowM_compatX`, `Core/Slices.lean`; family lends). -/
def SliceBorrowMT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ →
    (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) → (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) →
    ¬ VFree x A → ¬ VFree x B →
    SemJT (ℍ := ℍ) Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B))

/-- `slice_borrow_imm`. -/
def SliceBorrowIT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (x : LifeVar), Ctx.DeadP Γ → VScoped Δ A →
    (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) → (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) →
    ¬ VFree x A → ¬ VFree x B →
    SemJT (ℍ := ℍ) Δ Γ withbor (.val (sliceBorrowITy x Δ.meetOfDom A B))

/-- `withbor (2)`, unwinding (`withbor2U_compatX`, `Core/EffBorrow.lean`): the callback's row is
abortive only; a raise ends the lend and runs `d` on the source. Needs abortive stops at
`cerwpT` (I5). -/
def Withbor2UT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar), Ctx.DeadP Γ →
    Δ.find? x = none → (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) → ¬ VFree x A → ¬ VFree x B →
    S.Unwind x → closedAt 0 d = true → CDerives Δ Γ d (.val (.lolli (.ref A) .unit)) →
    SemJT (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))

/-- `withbor (3)`, unwinding (`withbor3U_compatX`). -/
def Withbor3UT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
    (x : LifeVar), Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B → S.Unwind x →
    closedAt 0 d = true → CDerives Δ Γ d (.val (.lolli (.mut a A) .unit)) →
    SemJT (ℍ := ℍ) Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S))

/-- **The new rules**, one statement per constant: it is a value of `!` its type. -/
def ConstT (c : Const791) : Prop :=
  c.OK → ∀ (δ : LSub) (n : Nat) (w : TWd) (ls : List (SRecT w.K)),
    (vT (.bang c.ty) δ).P n w ls c.val PMap.empty

/-- `withbor (2)` at a suspending row: the Mut Frame across stops (`erwp_M_frame`,
`StopFrameN.lean` on `tree-inv`). -/
def Withbor2ST : Prop := ∀ x bnd A B S d, ConstT (ℍ := ℍ) (.w2 x bnd A B S d)
/-- `withbor (3)` at a suspending row: the Anti-Frame and the Mut Frame across stops
(`erwp_withbor3`, `AntiStopN.lean`). -/
def Withbor3ST : Prop := ∀ a x bnd A B S d, ConstT (ℍ := ℍ) (.w3 a x bnd A B S d)
/-- The field reborrow at a suspending row: the Anti-Frame on the record, a Mut Frame on the
field (`erwp_withbor3` with the inner frame at a cell of the content). Core has the chain
relation's lemma and no typing rule. -/
def WithborFST : Prop := ∀ a x bnd A B S d, ConstT (ℍ := ℍ) (.wF a x bnd A B S d)
/-- `withload` at a suspending row (`erwp_reborrow`, `erwp_reborrowDeep`). -/
def WithloadST : Prop := ∀ a x bnd A B S, ConstT (ℍ := ℍ) (.wl a x bnd A B S)
/-- `slice_borrow_mut` at a suspending row. -/
def SliceBorrowMST : Prop := ∀ x bnd A B S d, ConstT (ℍ := ℍ) (.sm x bnd A B S d)

/-- `forget : Mut @a A ⊸ 1` (`releaseMut`): the `mut` token leaves. Every callback of a `mut`
lend ends by it or abandons its borrow at a raise, since `['x] B` holds no cell at `'x`. -/
def ReleaseMutT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A : VTy), Ctx.DeadP Γ →
    SemJT (ℍ := ℍ) Δ Γ forget (.val (BoCa.Fig16.LogRel.Core.axForgetMutTy a A))

/-- `⊑mut`. -/
def MutSubT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (a b : Lifetime.Life) (A : VTy),
    SemJT (ℍ := ℍ) Δ Γ e (.val (.mut b A)) → Δ.EntailsLe a b → SemJT (ℍ := ℍ) Δ Γ e (.val (.mut a A))

/-- `[perform]` at a non-abortive operation. -/
def EffPerformT : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (V : Expr) (S : Row) (o : OpSig), Row.find S o.n o.i = some o →
    o.abort = false → o.rc = false → SemJT (ℍ := ℍ) Δ Γ V (.val o.A) →
    SemJT (ℍ := ℍ) Δ Γ (BoCa.BoLo.performE (opArgE o.n o.i V)) (.comp (CTy.effOf S o.B))

/-- `[let]` at a row: the continuation of a stop holds the live context, own-free where the row
cancels (`hW`), so a `Mut 'x A` may be live across a cancellable stop. Bind across stops (I4). -/
def EffLetT : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M N : Expr) (A B : VTy) (S : Row), Ctx.SplitP Γ Γ₁ Γ₂ →
    (S.Cancels → Γ₂.OwnFree) → (S.Unr → Ctx.Banged Γ₂) →
    SemJT (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf S A)) →
    SemJT (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)) →
    SemJT (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B))

/-! ## §5. The hardest case -/

open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs (parkE spawnE cancelE progOf)
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn (TJ qsS hsS InvS hs_schedOK)
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack (QV QS stackRet)

/-- `let x = M in N`. -/
def letE (M N : Expr) : Expr := .app (.lam N) M

/-- `alloc e`. -/
def allocE (e : Expr) : Expr := .app (.val (.prim .alloc)) e

/-- The record's finaliser: `λr. let k = load r in free r; free k`. -/
def dRec : Val := Val.lam (letE (.app (.val (.prim .load)) (.var 0)) (letE (freeE (.var 1))
  (freeE (.var 1))))

/-- The reborrow's finaliser: `forget`. -/
def dFwd : Val := Val.lam (.val .unit)

/-- `x := v`. -/
def storeE (x v : Expr) : Expr := .app (.app (.val (.prim .store)) x) v

/-- The value task A writes through the field's borrow. -/
def vField : Val := Val.i32 7

/-- **The field's borrow, held across `park`, then written**: `λ_. λu. park; u := 7; forget u`. -/
def cbField : Val := Val.lam (.val (Val.lam (letE parkE
  (letE (storeE (.var 1) (.val vField)) (.app forget (.var 2))))))

/-- **A write through the record's borrow**: a fresh box stored in the record, the old one freed:
`let o = !v in let b = alloc () in v := b; free o`. -/
def writeRecE : Expr :=
  letE (.app (.val (.prim .load)) (.var 0)) (letE (allocE (.val .unit))
    (letE (storeE (.var 2) (.var 0)) (freeE (.var 2))))

/-- **The record's borrow**: `λ_. λv. writeRec v; let (v′, _) = withborF dFwd v cbField in
forget v′`. The field reborrowed is the fresh box's. -/
def cbRec : Val := Val.lam (.val (Val.lam (letE writeRecE
  (letE (.app (.app (.val (withborFV (.val dFwd))) (.var 1)) (.val cbField))
    (.letpair (.var 0) (.app forget (.var 1)))))))

/-- **Task A**: `c ↦ own(loc k) ● k ↦ own(())`; a `mut` lend of `c` (`withbor (2)`, unwinding,
at `park`'s row); through it a fresh box `k′` stored in `c` and `k` freed; then the field reborrow
of `k′` (`withborF`), held across `park` and written through after it; both ended; `dRec` frees
`c` and `k′`. -/
def taskA : Expr :=
  letE (allocE (.val .unit)) (letE (allocE (.var 0))
    (letE (.app (.app (.val (withborUV (.val dRec))) (.var 0)) (.val cbRec))
      (.letpair (.var 0) (.app (.val dRec) (.var 1)))))

/-- The value the other task writes through its borrow. -/
def vB : Val := Val.i32 5

/-- The other task's borrow: `λ_. λu. u := 5; forget u`. -/
def cbB : Val := Val.lam (.val (Val.lam
  (letE (storeE (.var 0) (.val vB)) (.app forget (.var 1)))))

/-- The other task's finaliser: `λr. free r`. -/
def dB : Val := Val.lam (freeE (.var 0))

/-- **The other task's body**, then `tail`: `park (); let a = alloc () in let (a′, _) =
withborU dB a cbB in free a′; tail`. Its cell is allocated and lent `mut` after its `park`, so
under `HS` (a spawned child runs first; `park` swaps with the top ready task) the lend opens and
ends while task A is parked. -/
def bodyB (tail : Expr) : Expr :=
  letE parkE (letE (allocE (.val .unit))
    (letE (.app (.app (.val (withborUV (.val dB))) (.var 0)) (.val cbB))
      (.letpair (.var 0) (letE (freeE (.var 1)) tail))))

/-- **The other task**: `bodyB ()`. -/
def thB : Val := Val.lam (bodyB (.val .unit))

/-- **The other task, then the canceller**: `bodyB (cancel ())`. When it cancels, task A is the
top ready task. -/
def thBC : Val := Val.lam (bodyB cancelE)

/-- The root: spawn `B` (`thB`), then run `A`. `B` runs first and parks; `A` runs to the `park`
inside the field's borrow; `B` resumes, opens its lend, writes, ends it and frees its cell; then
`A` resumes and writes through the field's borrow. -/
def rootMut : Expr := letE (spawnE thB) taskA

/-- The cancel variant: spawn `B` (`thBC`), then run `A`. As in `rootMut`, `B`'s lend opens and
ends while `A` is parked; then `B` cancels `A` while `A` holds the field's borrow. -/
def rootMutC : Expr := letE (spawnE thBC) taskA

def progMut : Expr := progOf rootMut
def progMutC : Expr := progOf rootMutC

/-- **The hardest case, resumed**: closed, under the spawn scheduler `HS`. -/
def HardestCase791 : Prop := OrDiverges (ℍ := ℍ) progMut

/-- **The hardest case, cancelled.** -/
def HardestCase791C : Prop := OrDiverges (ℍ := ℍ) progMutC

/-- **The root's statement at the scheduler's table**, the form `progLoan_safe` proves its
root at. -/
def RootAt (root : Expr) : Prop :=
  ∀ (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)),
    cerwpT (ℍ := ℍ) (opTableT (TJ (ℍ := ℍ))) QV Fb F n w ls [] root PMap.empty

/-- The closed statements follow from the root's through `poolSchedAdequacyT`, every premise
of it discharged as for `progLoan_safe`. -/
theorem hardest_of_root (h : RootAt (ℍ := ℍ) rootMut) : HardestCase791 (ℍ := ℍ) :=
  poolSchedAdequacyT beforeP TJ nP qsS stackRet hsS QV QS InvS _ _ rootMut
    (fun _ _ _ _ _ _ h => h.2.2) (fun _ h => by cases h) hs_schedOK (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) fun n => h n _ _ _ _

theorem hardestC_of_root (h : RootAt (ℍ := ℍ) rootMutC) : HardestCase791C (ℍ := ℍ) :=
  poolSchedAdequacyT beforeP TJ nP qsS stackRet hsS QV QS InvS _ _ rootMutC
    (fun _ _ _ _ _ _ h => h.2.2) (fun _ h => by cases h) hs_schedOK (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) fun n => h n _ _ _ _

/-- **The scoped variant** (condition C1): the scheduler inside the record's lend. The record's
borrow is held across `park` by `A`; the field is reborrowed and its borrow ended within one
segment. `S₁` is the root's own program under the scheduler `H`, run as the callback. -/
def taskScoped (H : Val) (S₁ : Expr) : Expr :=
  letE (allocE (.val .unit)) (letE (allocE (.var 0))
    (letE (.app (.app withbor (.var 0)) (.val (Val.lam (.val (Val.lam (hndE H S₁))))))
      (.letpair (.var 0) (.app (.val dRec) (.var 1)))))


/-! ## §6. The two candidates' relation-level statements

### Candidate A: Core's fold-and-seal, over a garbage part and a pinned store typing

The garbage part is `roots-791`'s (`Core/TreeRoots.lean` on that branch), restated here so the
statements elaborate on `tree-core`. -/

/-- `NoOwn` at the tree carrier. -/
def NoOwnT {K : WCactus} (ρ : TRes K) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.own

/-- A postcondition read at the end without its garbage (Core's `ρ′ ● ρ⁺`). -/
def garbP (Q : TPost) : TPost := fun k w ls O t ρ' =>
  ∃ ρ₁ g : TRes w.K, ResUT.CompS ρ₁ g ρ' ∧ NoOwnT g ∧ Q k w ls O t ρ₁

/-- **`twp` with a garbage part** (`roots-791`'s `twpG`): from every start adding own-free
garbage beside `ρ`, a run whose end is read without its garbage. `EndT` is unchanged. -/
def twpG (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K) : Prop :=
  ∀ g ρg : TRes w.K, NoOwnT g → ResUT.CompS ρ g ρg → twp (ℍ := ℍ) F (garbP Q) n w ls O e ρg

/-- **`cerwpT` over `twpG`.** -/
def cerwpTG (Tb : TableT) (Q : TPostV) (Fb : TFrame) : TFrame → Nat → (w : TWd) →
    List (SRecT w.K) → List (FrameRecT w.K) → Expr → TRes w.K → Prop
  | F, n, w, ls, O, e => twpG (ℍ := ℍ) F (cerwpPostT Tb Q (fun F' w' O' k' ls' e' =>
      if _h : k' < n then cerwpTG Tb Q Fb F' k' w' ls' O' e' else fun _ => False) Fb) n w ls O e
termination_by _ n => n

/-- **Pinned extension** (`roots-791`'s `TWd.PinExt`): `TWd.Ext`, and every location the carried
resource holds a cell at keeps its code. A location nothing holds may be re-typed (a freed
location reused). Candidate A reads `twp`, `EndT`, `contShareT` and `STy.Mono` at it in place of
`TWd.Ext`. -/
def PinExt (w w' : TWd) (ρ : TRes w.K) : Prop :=
  w.Ext w' ρ ∧ ∀ l ψ, ρ.get l = some ψ → w'.Θ l = w.Θ l

/-- The cell's invariant read off its location's code (E1). -/
def codeP (w : TWd) (A : KTy) (b : TSet) : BoCa.Val → SPropST BoCa.Loc BoCa.Val w.K b :=
  fun u r => (A.interp w.Θ).P w.K u r.val

/-- **Core's `MFPost`** (`WpN.lean:604` on `tree-inv`) read without the garbage: the part read lies
in `Res_α`, and the borrow handed back as `ℓ ↦ own(u)` beside content in the code meets `Q`. -/
def MFPostG (l : BoCa.Loc) (α : Life) (A : KTy) (Q : TPostV) : TPostV := fun k w ls O v ρ' =>
  ρ'.InStratum (TSet.single α) ∧
  ∀ (u : BoCa.Val) (Y : TRes w.K), ResUT.CompS ρ' (ResUT.single l (CellUT.ownOf u)) Y →
    ∀ σ, (A.interp w.Θ).P w.K u σ → ∀ Z, ResUT.CompS Y σ Z → Q k w ls O v Z

/-- **The Anti-Frame's callback post**, read without the garbage: the end world types `ℓ` at `A`
(Core's fixed `Φ ℓ`), the end holds `ℓ ↦ own(u) ● σ′` with `σ′` in the code, and the rest beside
the resealed cell `ℓ ↦ mut(b, u, σ′, P̂)` meets `Q`. (`tree-791`'s `MFPostTK` composed the end with a
second `ℓ ↦ own(u)`, which the end already holds; that composite is undefined, so it held
vacuously, `mfPostT_of_get`.) -/
def MFPostGK (l : BoCa.Loc) (b : TSet) (A : KTy) (Q : TPostV) : TPostV := fun k w ls O v ρ' =>
  w.Θ l = some A ∧ ∃ (u : BoCa.Val) (σ' ρ'' X : TRes w.K), (A.interp w.Θ).P w.K u σ' ∧
    ResUT.CompS (ResUT.single l (CellUT.ownOf u)) σ' X ∧ ResUT.CompS ρ'' X ρ' ∧
    ∀ (_ : Fact (w.K.Anti b)) (hs : σ'.InStratum b) (hw : codeP w A b u ⟨σ', hs⟩) (Z : TRes w.K),
      ResUT.CompS ρ'' (ResUT.single l (CellUT.mutOf b u σ' hs (codeP w A b) hw)) Z →
        Q k w ls O v Z

/-- No non-abortive entry is unrestricted (decided option (b), `scope-791.md` appendix). -/
def KeepsShare (T : OpTabT) : Prop :=
  ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr

/-- `CellFold` (`AntiStopN.lean:224`) at the tree: the share holds `ℓ ↦ own(u)` beside content
in the code. -/
def CellFoldT (l : BoCa.Loc) (A : KTy) : (w : TWd) → TRes w.K → Prop := fun w ρ =>
  ∃ (u : BoCa.Val) (χ R rest : TRes w.K), (A.interp w.Θ).P w.K u χ ∧
    ResUT.CompS (ResUT.single l (CellUT.ownOf u)) rest ρ ∧ ResUT.CompS χ R rest

/-- `opTableT`'s stops, the continuation's share guarded. -/
def opTableGT (T : OpTabT) (G : (w : TWd) → TRes w.K → Prop) : TableT := fun F k w ls O t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntT),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.abort = false ∧ en.oc w O ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧
      en.PA k w ls v ρa ∧ G w ρk ∧ contShareT en F k w ls O K v Ψ ρk

/-- **A1. The Mut Frame within a segment** (6.65 at `twpG`, `wpTS_M_frameX`): the lender's run
from `ℓ ↦ own(v) ● ρ_P ● ρ_b`, given the borrowed run from `ρ_b ● ℓ ↦ mut(α, v, ρ_P, P̂)` at
`MFPostG`. `ρ_b ∈ Res_D` with `K.DownOf D {α}` (the frame outlives the lend, `houtb`); `F.Mono`
(the frame condition carried to the start, `CerwpTMFrameM`'s approved premise). Needed by C1, C2
and C3. -/
def TwpGMFrame : Prop :=
  ∀ (F : TFrame) (Q : TPostV) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (α : Life)
    [Fact (w.K.Anti (TSet.single α))] (D : TSet) (v : BoCa.Val) (ρP ρlP ρb ρ : TRes w.K)
    (hP : ρP.InStratum (TSet.single α)) (hw : codeP w A (TSet.single α) v ⟨ρP, hP⟩),
    F.Mono → w.K.DownOf D (TSet.single α) → ρb.InStratum D → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρP ρlP → ResUT.CompS ρlP ρb ρ →
    (∀ BM, ResUT.CompS ρb (ResUT.single l (CellUT.mutOf (TSet.single α) v ρP hP
        (codeP w A (TSet.single α)) hw)) BM →
      twpG (ℍ := ℍ) F (fun k w' ls' O' t ρ' => ∃ u : Val, t = u.1 ∧ MFPostG l α A Q k w' ls' O' u ρ')
        n w ls O e BM) →
    twpG (ℍ := ℍ) F (fun k w' ls' O' t ρ' => ∃ u : Val, t = u.1 ∧ Q k w' ls' O' u ρ') n w ls O e ρ

/-- **A2. The Anti-Frame within a segment** (6.66 at `twpG`, `wpTS_M_antiFrameX`): the callback
gets `ℓ ↦ own(v) ● σ_P` and ends with the cell's code kept (`MFPostGK`). -/
def TwpGAntiFrame : Prop :=
  ∀ (F : TFrame) (Q : TPostV) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (b : TSet)
    [Fact (w.K.Anti b)] (v : BoCa.Val) (σP ρa ρ : TRes w.K)
    (hP : σP.InStratum b) (hw : codeP w A b v ⟨σP, hP⟩),
    F.Mono → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.mutOf b v σP hP (codeP w A b) hw)) ρa ρ →
    (∀ W X, ResUT.CompS σP (ResUT.single l (CellUT.ownOf v)) W → ResUT.CompS ρa W X →
      twpG (ℍ := ℍ) F (fun k w' ls' O' t ρ' => ∃ u : Val, t = u.1 ∧
        MFPostGK l b A Q k w' ls' O' u ρ') n w ls O e X) →
    twpG (ℍ := ℍ) F (fun k w' ls' O' t ρ' => ∃ u : Val, t = u.1 ∧ Q k w' ls' O' u ρ') n w ls O e ρ

/-- **A3. The Mut Frame across stops** (`erwp_M_frame`, `StopFrameN.lean:320`, with the
cancellable case of option (b)): the content folded at every stop and lent again at the resume
and at the cancel branch. Needed by C2 and C3, not by C1. -/
def CerwpTGMFrame : Prop :=
  ∀ (T : OpTabT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (α : Life)
    [Fact (w.K.Anti (TSet.single α))] (D : TSet) (v : BoCa.Val) (ρP ρlP ρb ρ : TRes w.K)
    (hP : ρP.InStratum (TSet.single α)) (hw : codeP w A (TSet.single α) v ⟨ρP, hP⟩),
    KeepsShare T → F.Mono → Fb.Mono →
    (∀ m i en, T m i = some en → ∀ v' : Val, ∀ (w' : TWd) (O' : List (FrameRecT w'.K)),
      TFrame.Mono (fdAt en v' Fb O')) →
    w.K.DownOf D (TSet.single α) → ρb.InStratum D → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρP ρlP → ResUT.CompS ρlP ρb ρ →
    (∀ BM, ResUT.CompS ρb (ResUT.single l (CellUT.mutOf (TSet.single α) v ρP hP
        (codeP w A (TSet.single α)) hw)) BM →
      cerwpTG (ℍ := ℍ) (opTableT T) (MFPostG l α A Q) Fb F n w ls O e BM) →
    cerwpTG (ℍ := ℍ) (opTableT T) Q Fb F n w ls O e ρ

/-- **A4. The Anti-Frame across stops** (`erwp_M_antiFrame`, `AntiStopN.lean:257`): the cell
sealed at every stop, under the guard `CellFoldT` on the stop's share. -/
def CerwpTGAntiFrame : Prop :=
  ∀ (T : OpTabT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (A : KTy) (b : TSet)
    [Fact (w.K.Anti b)] (v : BoCa.Val) (σP ρa ρ : TRes w.K)
    (hP : σP.InStratum b) (hw : codeP w A b v ⟨σP, hP⟩),
    KeepsShare T → F.Mono → Fb.Mono → w.Θ l = some A →
    ResUT.CompS (ResUT.single l (CellUT.mutOf b v σP hP (codeP w A b) hw)) ρa ρ →
    (∀ W X, ResUT.CompS σP (ResUT.single l (CellUT.ownOf v)) W → ResUT.CompS ρa W X →
      cerwpTG (ℍ := ℍ) (opTableGT T (CellFoldT l A)) (MFPostGK l b A Q) Fb F n w ls
        O e X) →
    cerwpTG (ℍ := ℍ) (opTableT T) Q Fb F n w ls O e ρ

/-- **A5. Top-level adequacy at the garbage layer**: as `TopAdequacyT`, the result holding
nothing **and the run owning no records**. Without `O = []` it is refused by `roots-791`'s
`twpG_ends_record_live` (a live lend record, its view left as garbage, its cell in memory). -/
def TopAdequacyG : Prop :=
  ∀ (P : ParentFn) (Q : TPostV) (P₀ : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty ∧ O = [] ∧ ls = []) →
    (∀ n, cerwpTG (ℍ := ℍ) (opTableT OpTabT.empty) Q (fun _ ρf => ρf = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) n (w₀ P) [] [] P₀ (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) P₀

/-- **A6. Garbage is reclaimed at an empty record list** (Core's `reclaim`): an own-free part
of a world with no records lowers to nothing. A5's content. -/
def ReclaimT : Prop :=
  ∀ (w : TWd) (W g ρ : TRes w.K) (μ : BoCa.Loc → Option BoCa.Val), NoOwnT g →
    ResUT.CompS ρ g W → RecInv w W [] [] → WInv w W μ → g = PMap.empty

/-! ### Candidate B: the pinned borrow

The `mut` lend opens a record, as an `imm` lend does (D14), that pins the cell's code; the `mut`
cell rides in the continuation's share; the lend's end takes it back; cancel hands it back
through the cancel branch. -/

/-- **B1. A `mut` lend record pins its cell's code**: the location typing coverage reads, the
records' codes over the world's. A `mut` cell at a recorded location is covered at the record's
code whatever the world's store typing says there. -/
def semRec (Θ : CodeTy) {K : WCactus} (rs : List (FrameRecT K)) : LocTy := fun l =>
  match rs.find? (fun r => decide (r.le = l)) with
  | some r => some (r.T.interp Θ)
  | none => sem Θ l

/-- **B2. The lend's end takes the token back**: at `twp` (no garbage), a run holding the token
`ℓ ↦ mut(…)` ends a run that holds nothing, its frame holding nothing at `ℓ`, the memory still
holding `ℓ`. Not refuted in Lean: a refutation needs a valid start world holding a `mut` token
(`TWNT.alloc` then `TWNT.mutFold`, with its validity and lowering), which is not built here.
`endT_drop_frees` is the step it would close with. -/
def TokenBackT : Prop :=
  ∀ (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (e : Expr) (l : BoCa.Loc) (ρ : TRes w.K),
    (∀ k w' ls' O' t ρ', Q k w' ls' O' t ρ' → ρ' = PMap.empty) →
    (∃ ψ, ρ.get l = some ψ ∧ ψ.kind = .mut) → twp (ℍ := ℍ) F Q n w ls O e ρ

/-! ## §7. Feasibility -/

/-- **Two cells at one location compose only as `imm` copies**: the lender can hold nothing at
`ℓ` beside the borrower's `mut` token. So candidate B's "the lend's end takes the token back"
has no piece of the lender at `ℓ` to merge it with: it needs a carrier clause for it, or the
token kept in the run until the end (a garbage part). -/
theorem compS_both_imm {K : WCactus} {a b c : TRes K} {l : BoCa.Loc} {ψ₁ ψ₂ : TCell K}
    (h : ResUT.CompS a b c) (h₁ : a.get l = some ψ₁) (h₂ : b.get l = some ψ₂) :
    ψ₁.kind = Kind.imm := by
  rcases ResUT.Comp.get h l with ⟨f, -, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
  · rw [h₁] at f; cases f
  · rw [h₂] at f; cases f
  · rw [h₁] at f; cases f
  · rw [h₁] at f₁
    cases f₁
    obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, -, -⟩ := hC
    exact (by rw [e₁]; rfl)

/-- **An end holding nothing frees every location its frame holds nothing at.** At `EndT`, if
the postcondition forces the run's end resource empty and the frame's flattening holds nothing
at `ℓ`, the end memory misses `ℓ`. So at `twp`, with `EndT` as it stands (no garbage), a run
that holds a location's only cell (a `mut` token) and does not free it never ends holding nothing:
`forget` of a `mut` borrow (`ReleaseMutT`) and candidate B's hand-back (`TokenBackT`) both need
the token kept somewhere the end world reads. -/
theorem endT_drop_frees {Q : TPost} {k : Nat} {w₀ : TWd} {ρ₀ : TRes w₀.K}
    {O₀ : List (FrameRecT w₀.K)} {ρf : TRes w₀.K} {psF : List (FrameRecT w₀.K)} {μ' : BoCa.BoLo.Heap}
    {t : Expr} {l : BoCa.Loc}
    (hQ : ∀ k w' ls' O' t ρ', Q k w' ls' O' t ρ' → ρ' = PMap.empty) (hv : ResUT.Valid ρf)
    (hn : NoneAt (· = l) ρf) (h : EndT Q k w₀ ρ₀ O₀ ρf psF μ' t) : μ' l = none := by
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', hE, hrf, -, -, hc', -, -, hI', hq, -⟩ := h
  obtain rfl := hQ _ _ _ _ _ _ hq
  obtain rfl := ResUT.CompS.functional hc' (ResUT.compS_empty_right _)
  have hn' := NoneAt.rr hE.1 hv hrf hn
  obtain ⟨σ, hσ, hμ⟩ := hI'.2
  rw [hμ l, hn' σ hσ l rfl]
  rfl

/-- **Scoped suspension is Core's rows**: a row that unwinds and holds no unrestricted
operation suspends. Condition C1 types its lends at `Row.Unwind` (or the pure row), so it needs
no new constant. -/
theorem suspend_of_unwind {S : Row} {x : LifeVar} (h : S.Unwind x)
    (hq : ∀ o ∈ S, o.q ≠ .unr) : S.Suspend x := Row.Suspend.of_unwind h hq

end BoCa.Fig16.Tree.Wp.Goal791

end
