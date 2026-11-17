import Core.Fundamental

/-!
# The constants #791 adds, and the judgment's computation type  `[spec §62]`

The suspending lends are data (`Const791`), closed over a context (`ctx791`) as constants, so
no judgment is added; `Row.Suspend` is the row their callbacks run at. The chain
(`Core/Chain/`) reads them at its own relation.
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

/-- **The clauses `Row.Suspend` asks of a cancel row's layers**, recursively: each layer not
unrestricted, its payload and answer types free of `'x` and outliving the callback's bound
`@bnd` at the lifetime context `Δ`, and the cancel row of each capturable layer likewise. A cancel
run under a live lend stops at these layers, so they meet what the row's own operations meet.
`[spec §62]` -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.SuspendC (Δ : LifeCtx) (x : LifeVar) (bnd : Lifetime.Life) :
    CTy → Prop
  | .eff _ _ q A B fin _ C =>
      (q ≠ .unr ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ VOutlives Δ bnd A ∧
        VOutlives Δ bnd B ∧ (capB q B = true → SuspendC Δ x bnd fin)) ∧
      SuspendC Δ x bnd C
  | _ => True

/-- **The row of a callback that may suspend inside a borrow of `'x ⊏ @bnd`**, at the lifetime
context `Δ` the bound is read at: `Row.Unwind` without its abort clause, its outliving clause
relative to the lend. Every operation is named (the finaliser frame's re-raise reads `n ≠ 0`,
`erwp_ubindClaimRT`), not unrestricted (a continuation resumed twice would lend twice: SPEC §62,
"Typing: suspension"); its payload and answer types are free of `'x` and outlive `@bnd` at `Δ`,
so at every `δ ⊨ Δ` their values lie in the stratum of every lend `α ⊏ @bnd` (`OpTabN.LendOKCR`'s
`pa`/`pb`, Core's `LendOK`), and a fresh lend leaves their reading unchanged (`vN_add_eq_bnd`); a
capturable operation's cancel row meets the same clauses (`CTy.SuspendC`). Decidable on the row
given `VFree` and `VOutlives`.

At the empty context a defined bound is closed, so it is `⊤` (`interp_top_of_defines_empty`), and
the outliving clauses put every payload and answer in `Res_⊤`, consistent with every view
(`erwp_claimX`). At such a bound `VOutlives ∅ bnd T` excludes exactly the types with, outside a
box or `!`, one of: `Imm @b A` or `Mut @b A` (they need `∅ ⊨ @bnd ⊏ @b`, and no `@b` is strictly
longer than `⊤`); a thunk `U C` or `Unk` (no outliving rule); a box `[@b] A` at a `@b` with a
variable (`∅ ⊨ @bnd ⊑ @b` asks `@b` defined at the empty substitution). A box `[@b] A` at a
closed `@b`, whatever `A` holds (`[@⊤] U C` included), and `! A` pass. At a context with
variables, a payload may hold a borrow `Imm @b A` of a lend `@b` that `Δ` places strictly above
`@bnd`. `[spec §62]` -/
def _root_.BoCa.Fig16.LogRel.Core.Row.Suspend (S : Row) (Δ : LifeCtx) (x : LifeVar)
    (bnd : Lifetime.Life) : Prop :=
  ∀ o ∈ S, o.q ≠ .unr ∧ o.n ≠ 0 ∧ ¬ VFree x o.A ∧ ¬ VFree x o.B ∧
    VOutlives Δ bnd o.A ∧ VOutlives Δ bnd o.B ∧
    (capB o.q o.B = true → o.fin.SuspendC Δ x bnd)

theorem _root_.BoCa.Fig16.LogRel.Core.Row.Suspend.of_unwind {S : Row} {Δ : LifeCtx} {x : LifeVar}
    {bnd : Lifetime.Life} (h : S.Unwind x) (hq : ∀ o ∈ S, o.q ≠ .unr) : S.Suspend Δ x bnd :=
  fun o ho =>
  ⟨hq o ho, (h o ho).2.1, (h o ho).2.2.1,
    by rw [OpSig.B_zero (h o ho).1]; exact id, (h o ho).2.2.2 _ _,
    by rw [OpSig.B_zero (h o ho).1]; exact .zero,
    by rw [OpSig.B_zero (h o ho).1]; simp [capB, VTy.isZero]⟩

/-- **A property of every answer of a cancel row's layers**, recursively through the cancel rows
of capturable layers. `[spec §62]` -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.AnsC (P : VTy → Prop) : CTy → Prop
  | .eff _ _ q _ B fin _ C => (P B ∧ (capB q B = true → AnsC P fin)) ∧ AnsC P C
  | _ => True

/-- **A property of every answer of a row**, its capturable operations' cancel rows included
(`CTy.AnsC`). `Const791.OKAt` asks it at `VOutlives ∅ b` for a closed `b`: the answers outlive a
closed bound, so they lie in `Res_⊤` and are consistent with every view. `[spec §62]` -/
def _root_.BoCa.Fig16.LogRel.Core.Row.AnsC (P : VTy → Prop) (S : Row) : Prop :=
  ∀ o ∈ S, P o.B ∧ (capB o.q o.B = true → o.fin.AnsC P)

/-- At the empty context, a cancel row's `SuspendC` gives its answers' outliving clause. -/
theorem ansC_of_suspendC {x : LifeVar} {bnd : Lifetime.Life} :
    ∀ F : CTy, F.SuspendC LifeCtx.empty x bnd → F.AnsC (VOutlives LifeCtx.empty bnd)
  | .eff _ _ _ _ _ fin _ C, ⟨⟨_, _, _, _, hB, hfin⟩, hC⟩ =>
      ⟨⟨hB, fun hcap => ansC_of_suspendC fin (hfin hcap)⟩, ansC_of_suspendC C hC⟩
  | .ret _, _ | .arr _ _, _ | .amp _ _, _ | .top, _ | .all _ _ _, _ | .nuSys _ _ _, _ => trivial

/-- At the empty context, `Row.Suspend` gives its answers' outliving clause. -/
theorem ansC_of_suspend {S : Row} {x : LifeVar} {bnd : Lifetime.Life}
    (h : S.Suspend LifeCtx.empty x bnd) : S.AnsC (VOutlives LifeCtx.empty bnd) := fun o ho =>
  ⟨(h o ho).2.2.2.2.2.1, fun hcap => ansC_of_suspendC _ ((h o ho).2.2.2.2.2.2 hcap)⟩

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
`Row.Suspend` for `Row.Unwind`; `wF` is the field reborrow. `poly 'y @b c` is `c` under the
lifetime binder `'y ⊏ @b`, so a constant's types may name the lifetimes of its own context.
`[spec §62]` -/
inductive Const791 where
  | w2 (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
  | w3 (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
  | wF (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
  | wl (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row)
  | sm (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row) (d : Expr)
  | poly (y : LifeVar) (b : Lifetime.Life) (c : Const791)

/-- The constant's type: a lend constant's rule type, under `∀'y ⊏ @b` (`VTy.all`) at each
binder. `[spec §62]` -/
def Const791.ty : Const791 → VTy
  | .w2 x bnd A B S _ => withbor2UTy x bnd A B S
  | .w3 a x bnd A B S _ => withbor3UTy a x bnd A B S
  | .wF a x bnd A B S _ => withborFSTy a x bnd A B S
  | .wl a x bnd A B S => withloadUTy a x bnd A B S
  | .sm x bnd A B S _ => sliceBorrowMUTy x bnd A B S
  | .poly y b c => VTy.all y b c.ty

/-- The constant's value: a lend constant's term, under `λ_.` (`Λ.`) at each binder.
`[spec §62]` -/
def Const791.val : Const791 → Val
  | .w2 _ _ _ _ _ d => withborUV d
  | .w3 _ _ _ _ _ _ d => withborUV d
  | .wF _ _ _ _ _ _ d => withborFV d
  | .wl _ _ _ _ _ _ => withloadV
  | .sm _ _ _ _ _ d => withborUV d
  | .poly _ _ c => Val.lam c.val.1

/-- **The constant's value closed by the externs' values `γx`**: each finaliser `d`, typed at the
externs' context, under the closing substitution `d[γx]`. At `γx = []` it is `Const791.val`
(`Const791.valAt_nil`).  `[spec §72]` -/
def Const791.valAt (γx : List Val) : Const791 → Val
  | .w2 _ _ _ _ _ d => withborUV (substAll γx d)
  | .w3 _ _ _ _ _ _ d => withborUV (substAll γx d)
  | .wF _ _ _ _ _ _ d => withborFV (substAll γx d)
  | .wl _ _ _ _ _ _ => withloadV
  | .sm _ _ _ _ _ d => withborUV (substAll γx d)
  | .poly _ _ c => Val.lam (c.valAt γx).1

/-- At no externs the closed value is the constant's value.  `[spec §72]` -/
theorem Const791.valAt_nil : ∀ c : Const791, c.valAt [] = c.val
  | .w2 .. | .w3 .. | .wF .. | .sm .. => by
      simp only [Const791.valAt, Const791.val, substAll, BoCa.Adequacy.psub_nil]
  | .wl .. => rfl
  | .poly _ _ c => by simp only [Const791.valAt, Const791.val, Const791.valAt_nil c]

/-- **The rule's premises, at the lifetime context `Δ`**: a lend constant's are the
corresponding `CDerives` constructor's (`withbor2U`, `withbor3U`, `withloadU`, `sliceBorrowMU`) at
`Δ`, `hS : S.Unwind x` read as `S.Suspend Δ x bnd`; the finaliser typed at `Δ` and the externs'
context `Γx` (its slots persistent, closed by the externs' values, `Const791.valAt`), and closed
above `Γx`. At `Γx = []` the finaliser is closed and typed at the empty context. The
field reborrow's are `withbor3U`'s at `Mut @a (Ref A)`. A binder's are `allI`'s side conditions
(the bound and `Δ`'s bounds do not mention `'y`), its body's read at `Δ, 'y ⊏ @b`.

The first conjunct, `Δ.Defines bnd`, is where Core's rules get the callback bound's
interpretation: they fix the bound to `Δ.meetOfDom`, which every `δ ⊨ Δ` interprets
(`Lifetime.Life.interp_defined_of_wf`, `Lifetime.meetOfDomL_wf`; `withbor2U_compatX`,
`Core/EffBorrow.lean`). The constants take any bound, so they carry the definedness as a premise;
`defines_meetOfDom_empty` shows Core's bound meets it at the empty context.

The answers are read at a closed bound (`Row.AnsC` at `VOutlives ∅ b`, `∅ ⊨ @b`): an answer then
lies in `Res_⊤` and is consistent with every view, which discharges the answer's move between the
lender's view and the lend's (`AnsViewG`). At the empty context this is `Row.Suspend`'s own answer
clause (`ansC_of_suspend`). `[spec §62]` -/
def Const791.OKAt : LifeCtx → Ctx VTy → Const791 → Prop
  | Δ, Γx, .w2 x bnd A B S d => Δ.Defines bnd ∧
      (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend Δ x bnd ∧
      (∃ b, LifeCtx.empty.Defines b ∧ S.AnsC (VOutlives LifeCtx.empty b)) ∧
      closedAt Γx.length d = true ∧ CDerives Δ Γx d (.val (.lolli (.ref A) .unit))
  | Δ, Γx, .w3 a x bnd A B S d => Δ.Defines bnd ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend Δ x bnd ∧
      (∃ b, LifeCtx.empty.Defines b ∧ S.AnsC (VOutlives LifeCtx.empty b)) ∧
      closedAt Γx.length d = true ∧ CDerives Δ Γx d (.val (.lolli (.mut a A) .unit))
  | Δ, Γx, .wF a x bnd A B S d => Δ.Defines bnd ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend Δ x bnd ∧
      (∃ b, LifeCtx.empty.Defines b ∧ S.AnsC (VOutlives LifeCtx.empty b)) ∧
      closedAt Γx.length d = true ∧ CDerives Δ Γx d (.val (.lolli (.mut a (.ref A)) .unit))
  | Δ, _, .wl _ x bnd A B S => Δ.Defines bnd ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend Δ x bnd
  | Δ, Γx, .sm x bnd A B S d => Δ.Defines bnd ∧
      (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧
      (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend Δ x bnd ∧
      (∃ b, LifeCtx.empty.Defines b ∧ S.AnsC (VOutlives LifeCtx.empty b)) ∧
      closedAt Γx.length d = true ∧ CDerives Δ Γx d (.val (.lolli (.array A) .unit))
  | Δ, Γx, .poly y b c => b.mentions y = false ∧
      (∀ z u, Δ.find? z = some u → u.mentions y = false) ∧ c.OKAt (Δ.extend y b) Γx

/-- **The rule's premises** of a constant used by a closed program: `Const791.OKAt` at the empty
context, at no externs. `[spec §62]` -/
def Const791.OK (c : Const791) : Prop := c.OKAt LifeCtx.empty []

/-- **At no externs a lend's finaliser clause is closed and typed at the empty context**: the
clause `OKAt` read before the externs' context (here at `w2`; the other lends alike).
`[spec §72]` -/
theorem Const791.okAt_nil_w2 {Δ : LifeCtx} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} :
    (Const791.w2 x bnd A B S d).OKAt Δ [] ↔ Δ.Defines bnd ∧
      (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧
      ¬ VFree x A ∧ ¬ VFree x B ∧ S.Suspend Δ x bnd ∧
      (∃ b, LifeCtx.empty.Defines b ∧ S.AnsC (VOutlives LifeCtx.empty b)) ∧
      closedAt 0 d = true ∧ CDerives Δ [] d (.val (.lolli (.ref A) .unit)) := Iff.rfl

/-- **Core's bound meets `Const791.OK`'s first conjunct**: `LifeCtx.empty.meetOfDom`, the bound
Core's rules fix at the empty context, is defined at every `δ`. -/
theorem defines_meetOfDom_empty : LifeCtx.empty.Defines LifeCtx.empty.meetOfDom :=
  fun _ hδ => Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)

/-- A lifetime defined at the empty substitution has no variable, so it is `⊤` at every `δ`. -/
theorem interp_top_of_interp_empty : ∀ (b : Lifetime.Life) (n : Nat),
    b.interp ⟨[]⟩ = some n → ∀ δ : LSub, b.interp δ = some Lifetime.SLife.top
  | .var _, _, h, _ => by simp [Lifetime.Life.interp, LSub.find?, Lifetime.assocFind] at h
  | .top, _, _, _ => rfl
  | .join a b, _, h, δ => by
      simp only [Lifetime.Life.interp, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, m', hm', -⟩ := h
      simp [Lifetime.Life.interp, interp_top_of_interp_empty a m hm δ,
        interp_top_of_interp_empty b m' hm' δ, Lifetime.SLife.join, Lifetime.SLife.top]
  | .meet a b, _, h, δ => by
      simp only [Lifetime.Life.interp, Option.bind_eq_some_iff] at h
      obtain ⟨m, hm, m', hm', -⟩ := h
      simp [Lifetime.Life.interp, interp_top_of_interp_empty a m hm δ,
        interp_top_of_interp_empty b m' hm' δ, Lifetime.SLife.meet, Lifetime.SLife.top]

/-- **A lifetime defined at the empty context is `⊤`**: `Defines` quantifies over every `δ`, the
empty one included, so the lifetime has no variable. -/
theorem interp_top_of_defines_empty {b : Lifetime.Life} (h : LifeCtx.empty.Defines b)
    (δ : LSub) : b.interp δ = some Lifetime.SLife.top := by
  obtain ⟨n, hn⟩ := h ⟨[]⟩ (fun _ _ h => by
    simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h)
  exact interp_top_of_interp_empty b n hn δ

/-- The context a program using the constants `cs` is typed in: each constant at `!` of its
type, live. -/
def ctx791 (cs : List Const791) : Ctx VTy := cs.map fun c => ⟨.bang c.ty, true⟩

/-- The values closing it. -/
def vals791 (cs : List Const791) : List Val := cs.map Const791.val

/-- At no externs the constants' closed values are their values.  `[spec §72]` -/
theorem Const791.map_valAt_nil (cs : List Const791) :
    cs.map (fun c => c.valAt []) = vals791 cs := by
  simp only [vals791, Const791.valAt_nil]

/-- A judgment's computation type: `val A` is `F A`. -/
def jdgC : Jdg → CTy
  | .val A => .ret A
  | .comp C => C

/-- **Scoped suspension is Core's rows**: a row that unwinds and holds no unrestricted
operation suspends. Condition C1 types its lends at `Row.Unwind` (or the pure row), so it needs
no new constant. -/
theorem suspend_of_unwind {S : Row} {Δ : LifeCtx} {x : LifeVar} {bnd : Lifetime.Life}
    (h : S.Unwind x) (hq : ∀ o ∈ S, o.q ≠ .unr) : S.Suspend Δ x bnd := Row.Suspend.of_unwind h hq

end BoCa.Fig16.Tree.Wp.Goal791

end
