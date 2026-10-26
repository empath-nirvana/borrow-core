import Rewrite.Admission
import Rewrite.Guard
import Rewrite.ReadBack

/-!
# Rewrite — R1, tail  `[spec §54]`

R1 (#680, the scope's §R1, both cells: counts `1` and `1?`) eliminates a name `n` whose every
node is the tail-resuming rule's (`effHandleT`) and which the admission admits
(`Rewrite/Admission.lean`). Each work `g_j`, the node's typed answering function for the operation
`j`, becomes a declaration of the program; each `perform` of `n.j` a direct call of it; and the
node, which no `perform` of `n` then reaches, is removed:

```
work_{n.j} : !U(A_j ⊸ F_{Σ_N} B_j) = g_j                 (a declaration: the node's typed work)
perform_{n.j} V : F_Σ B_j     ↦  f <- return (unbang work_{n.j}); (force f) V   (F_{Σ_N} B_j ≤ F_⟦Σ⟧)
handle_n e with (h, gs)       ↦  a <- e; hf <- return (unbang h); (force hf) a
⟦Σ⟧ = (Σ ∖ n) ++ (Σ_N ∖ Σ)   at a row holding n; every other row's operations translated
```

The rows translate uniformly (`trRow1`, and every returner chain by `tC`); every other constructor
is homomorphic (`homLayer`). At a count `1?` the rule's clause never cancels its continuation, so
the `1?` cell has the same schema: the count does not enter a direct call. A clause the node holds
is a work of `tc`, never rebuilt from an erased clause (S-R1-3); the work is closed, so no handler
value is copied into it (S-R1-2); no frame of the source is removed but the node's own (its
handled computation is free of `n` once every `perform` of `n` is a call).

**Binders.** R1 moves whole typed subterms (a work, a `perform`'s argument, a removed node's
handled computation and answer clause), each node's `TInfo` with it, so every source binder keeps
its name, id and declaration; the binders it writes are its own (`%R1`) and carry no id.

**Laws.** Per `perform`: `tail_resume_direct` (`Core/DivHandleLastRuns.lean`), under `tailH`, the
value an `effHandleT` node runs as, at a work that performs nothing (every work the licence admits,
`Σ_N = []`). The node's
removal over a computation that performs no operation of `n`: `HandleTransparent` [ours]. The
checker's clause conversion: `ClauseTailReplace` [ours].
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count Jdg)
open BoCa.Fig16.LogRel.Core.Check (TExpr TInfo)

/-- The keys `(n, i)` of a returner chain's operations. -/
def chainKeys : CTy → List (UInt32 × UInt32)
  | .eff m i _ _ _ _ _ C => (m, i) :: chainKeys C
  | _ => []

/-- The operations of the works' row `Σ_N` a row whose keys are `ks` does not hold. Unreachable while
the licence admits only works at `Σ_N = []` (#693), as is `stackOps` and `tChain`'s arm that uses it:
kept for the translation's general form `(Σ ∖ n) ++ (Σ_N ∖ Σ)`. -/
def TailName.extra (a : TailName) (ks : List (UInt32 × UInt32)) : Row :=
  a.SN.filter fun o => !ks.contains (o.n, o.i)

/-- `Σ_N`'s operations `os` stacked over `C`. -/
def stackOps (os : Row) (C : CTy) : CTy := os.foldr (fun o D => .eff o.n o.i o.cnt o.wld o.A o.B o.fin D) C

mutual
/-- `⟦A⟧` at a value type: homomorphic. -/
def tV (a : TailName) : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (tV a A) (tV a B)
  | .zero => .zero
  | .sum A B => .sum (tV a A) (tV a B)
  | .thunk C => .thunk (tC a C)
  | .ref A => .ref (tV a A)
  | .imm l A => .imm l (tV a A)
  | .mut l A => .mut l (tV a A)
  | .box l A => .box l (tV a A)
  | .bang A => .bang (tV a A)
  | .unk => .unk
  | .tvar k => .tvar k
  | .mu A => .mu (tV a A)
  | .int w => .int w
  | .fam L => .fam (tV a L)
  | .opq k => .opq k
/-- `⟦C⟧` at a computation type: homomorphic but at a returner chain holding `n`, whose
operations of `n` are removed and under whose answer the works' row's operations it does not hold
are stacked (`tChain`). -/
def tC (a : TailName) : CTy → CTy
  | .ret A => .ret (tV a A)
  | .arr A C => .arr (tV a A) (tC a C)
  | .amp C D => .amp (tC a C) (tC a D)
  | .top => .top
  | .all x b C => .all x b (tC a C)
  | .nu C => .nu (tC a C)
  | .eff m i c w A B fin C =>
    let has := m == a.n || chainHas a.n C
    let ks := (m, i) :: chainKeys C
    if m == a.n then tChain a has ks C
    else .eff m i c w (tV a A) (tV a B) (tC a fin) (tChain a has ks C)
/-- The rest of a returner chain, `has` when the whole chain holds an operation of `n`, `ks` the
whole chain's keys. -/
def tChain (a : TailName) (has : Bool) (ks : List (UInt32 × UInt32)) : CTy → CTy
  | .eff m i c w A B fin C =>
    if m == a.n then tChain a has ks C
    else .eff m i c w (tV a A) (tV a B) (tC a fin) (tChain a has ks C)
  | .ret R => if has then stackOps (a.extra ks) (.ret (tV a R)) else .ret (tV a R)
  | .arr A C => .arr (tV a A) (tC a C)
  | .amp C D => .amp (tC a C) (tC a D)
  | .top => .top
  | .all x b C => .all x b (tC a C)
  | .nu C => .nu (tC a C)
end

/-- An operation's signature, translated. -/
def trOp1 (a : TailName) (o : OpSig) : OpSig :=
  { o with A := tV a o.A, B := tV a o.B, fin := tC a o.fin }

/-- **`⟦Σ⟧`**: at a row holding `n`, its other operations translated, then the works' row's
operations it does not hold; otherwise its operations translated. -/
def trRow1 (a : TailName) (S : Row) : Row :=
  if S.any (·.n == a.n) then
    (S.filter (·.n != a.n)).map (trOp1 a) ++ a.extra (S.map fun o => (o.n, o.i))
  else S.map (trOp1 a)

/-- The translation, as `homLayer` reads it. -/
def TailName.tyMap (a : TailName) : TyMap := ⟨tV a, tC a, trRow1 a, trOp1 a⟩

/-- The name R1 gives the binders it writes; the read-back numbers each by its depth. -/
def r1B : String := "%R1"

/-- The name of the work of `n.j`. -/
def workName (n : UInt32) (j : Nat) : String := s!"%R1work{n}.{j}"

/-- What R1's run records, and the fault it plants. -/
structure TlStats where
  seed : Seed := .none
  /-- The `!`-introductions of the works R1 places at its calls, one work's at each call (G-bang):
  each is the source's persistent work. -/
  bangs : Nat := 0
  performs : Nat := 0
  handles : Nat := 0
  /-- The source binders of the subterms R1 drops (each removed node's works' tuple), by their
  handles: `π` maps to `inv(R1, work)` those that are no binder of a declared work (`rules`). -/
  inv : List SrcBinder := []
  /-- `π` from each `perform` to its call: the `perform`'s id (`#P…`, which the call's binder
  carries) and operation, whose work the call targets (G-call). -/
  calls : List (String × UInt32 × UInt32) := []

/-- R1's monad. -/
abbrev TlM := StateT TlStats (Except String)

/-- The `!`-introductions, copies and forgets of a typed term (`isBangIntro`), every `use` body
included, as the guard counts them. -/
def bangsIn : Nat → TExpr → Except String Nat
  | 0, _ => throw "R1: a term nested too deeply to count"
  | f + 1, t => do
    let here := if isBangIntro t then 1 else 0
    t.children.foldlM (init := here) fun n (_, c) => do pure (n + (← bangsIn f c))

/-- The handles of the source binders of a typed term (`SrcBinder.ofNode`), every `use` body
included. -/
def nodeBinders : Nat → TExpr → Except String (List SrcBinder)
  | 0, _ => throw "R1: a term nested too deeply"
  | f + 1, t => do
    t.children.foldlM (init := SrcBinder.ofNode t) fun acc (_, c) => do
      pure (acc ++ (← nodeBinders f c))

/-- `h a`: the answer clause `h : !U(A ⊸ C)` applied to the variable `k : A`:
`hf <- return (unbang h); (force hf) k`. -/
def applyAt1 (sp : Frontend.Span) (h : TExpr) (k : Nat) (A : VTy) (C : CTy) : TExpr :=
  let U : VTy := .thunk (.arr A C)
  .bind { sp, binders := [r1B] } (.comp C) U C noMasks (retAt sp U (.bangE (infoAt sp) (.val U) U h))
    (.app (infoAt sp) (.comp C) (k + 1) A C noMasks (.force (infoAt sp) (.comp (.arr A C)) 0 (.arr A C)))

/-- The planted fault `weakenLin`: the first binding of a typed term declared `linear` loses its
declaration. -/
def unLin : Nat → TExpr → StateT Bool (Except String) TExpr
  | 0, _ => throw "R1: a term nested too deeply"
  | f + 1, t => do
    if !(← get) && t.info.lin then
      set true
      return t.setInfo { t.info with lin := false }
    homLayer ⟨id, id, id, id⟩ (unLin f) t

/-- **A `perform` of `n.j`** at the row `S`, its argument `c'` rewritten: a call of the work
`w` (the declaration `wd`, named `nm`), `F_{Σ_N} B ≤ F_{⟦Σ⟧} B`. An argument that is a variable is
passed as it is; another is bound first, written at the operation's argument type. -/
def performCall (a : TailName) (sp : Frontend.Span) (pid : String) (S : Row) (w : TExpr) (wd : Nat)
    (nm : String) (c' : TExpr) (seed : Seed) : Except String TExpr := do
  let .val W := w.jdg | throw "R1: a work at a computation type"
  let .bang U := W | throw "R1: a work's type is not `!U(A ⊸ F_{Σ_N} B)`"
  let .thunk (.arr A' CW) := U | throw "R1: a work's type is not `!U(A ⊸ F_{Σ_N} B)`"
  let some (SN', B') := Frontend.Check.effRow? CW | throw "R1: a work does not answer `F_{Σ_N} B`"
  let S' := trRow1 a S
  let use := TExpr.use (infoAt sp) (.val W) nm wd [] none w
  let call (k : Nat) : TExpr :=
    liftTo sp SN' S' B' (.app (infoAt sp) (.comp CW) k A' CW noMasks
      (.force (infoAt sp) (.comp (.arr A' CW)) 0 (.arr A' CW)))
  -- The planted control `dropAnswer`: the work's answer dropped, the argument answered.
  let body (k : Nat) : TExpr :=
    if seed == .dropAnswer then
      bindAt sp r1B S' B' A' (call k) (liftTo sp [] S' A' (retAt sp A' (varAt sp (k + 1) A')))
    else call k
  let C : CTy := CTy.effOf S' B'
  let withF (k : Nat) : TExpr :=
    -- The call's binder carries its `perform`'s id (`#P…`): `π` from `perform` to call (G-call).
    .bind { sp, binders := [s!"{r1B}#P{pid}"] } (.comp C) U C noMasks
      (retAt sp U (.bangE (infoAt sp) (.val U) U use)) (body (k + 1))
  match c' with
  | .var _ _ k _ => pure (withF k)
  | _ =>
    -- `[perform]` checks its argument at the operation's argument type: the binding writes it there.
    let cv := c'.setInfo { c'.info with asc := true }
    pure (.bind { sp, binders := [r1B] } (.comp C) A' C noMasks (retAt sp A' cv) (withF 0))

/-- **R1 over a typed term**, for the name `a` whose works are `ws` (translated), the `j`-th the
declaration `base + j`: the rules above at `n`'s nodes and `perform`s, homomorphic on every other
node (`homLayer`). A node of `n` that is not the rule's, a `raise` of `n`, and a loop node at a row
holding `n` (R7: no producer) are hard errors. -/
def tl (a : TailName) (ws : List TExpr) (base : Nat) (others : List (Nat × String × TExpr) := []) :
    Nat → TExpr → TlM TExpr
  | 0, _ => throw "R1: a term nested too deeply"
  | f + 1, t => do
    let m := a.tyMap
    let has (S : Row) := S.any (·.n == a.n)
    let seed := (← get).seed
    match t with
    | .effPerform i _ S o c =>
      if o.n != a.n then homLayer m (tl a ws base others f) t else
      let j := o.i.toNat
      let jw := if seed == .wrongWork && ws.length > 1 then (j + 1) % ws.length else j
      let some w := ws[jw]? | throw s!"R1: a `perform` of {o.n}.{o.i}, which has no work"
      -- The planted fault `wrongName`: the call of another name's work, of R1's earlier names.
      let (wd, wn, w) := match seed, others.head? with
        | .wrongName, some (d, nm, w') => (d, nm, w')
        | _, _ => (base + jw, workName a.n jw, w)
      let c' ← tl a ws base others f c
      let b ← bangsIn fuel w
      let some pid := (i.binders.head?).bind performIdOf?
        | throw s!"R1: a `perform` of {o.n}.{o.i} with no id"
      modify fun st => { st with bangs := st.bangs + b, performs := st.performs + 1,
                                 calls := st.calls ++ [(pid, o.n, o.i)] }
      performCall a i.sp pid S w wd wn c' seed
    | .effHandleT i _ S _ _ _ nm A R _ _ _ tc te =>
      if nm != a.n || seed == .keepNode then homLayer m (tl a ws base others f) t else
      let .tensorI _ _ _ _ _ tr tw := tc | throw "R1: a handler's pair is not a pair"
      -- The node's works are dropped with it (the first node's are the declarations): their
      -- binders' handles go to `π`'s `inv(R1, work)`.
      let dropped ← nodeBinders fuel tw
      modify fun st => { st with inv := st.inv ++ dropped }
      let tr' ← tl a ws base others f tr
      let te' ← tl a ws base others f te
      let sp := i.sp
      let S' := trRow1 a S
      let A' := tV a A
      let R' := tV a R
      let C := CTy.effOf S' R'
      modify fun st => { st with handles := st.handles + 1 }
      -- `[handle]` checks its handled computation at `F_{n::Σ} A`; the rule writes `e` at that
      -- type's translation, `F_{⟦Σ⟧} A`, where the node held it.
      let te'' := te'.setInfo { te'.info with asc := true }
      pure (bindAt sp r1B S' A' R' te'' (applyAt1 sp (tr'.shift 1 0) 0 A' C))
    | .effHandleV _ _ _ _ _ nm .. | .effHandleVB _ _ _ _ _ nm .. | .effHandleL _ _ _ _ _ _ _ nm .. =>
      if nm == a.n then throw s!"R1: a node of the name {a.n} that is not the tail-resuming rule's"
      else homLayer m (tl a ws base others f) t
    | .effRaise _ _ _ o _ _ =>
      if o.n == a.n then throw s!"R1: a `raise` of the name {a.n}, which has no abortive operation"
      else homLayer m (tl a ws base others f) t
    | .iterate _ _ S .. | .divFuel _ _ S .. | .reify _ _ S .. =>
      if has S then throw "R7: no producer (a loop node at a row holding a name R1 rewrites)"
      else homLayer m (tl a ws base others f) t
    | _ => homLayer m (tl a ws base others f) t

/-! ### A node the licence leaves -/

/-- **The rule's clause of the operation `j`, as a `[handle]` clause** (`tailClause j (q == 0) Hc`):
`λ(x, κ). (λw. κ.1 w) (g_j x)` at a non-abortive operation, `λx. g_j x` at an abortive one, `g_j`
the variable `g` (bound outside the node: the tuple's `j`-th component, a `!` value). -/
def ruleClause (sp : Frontend.Span) (S : Row) (R : VTy) (F : CTy) (g : Nat) (o : Count × VTy × VTy) :
    TExpr :=
  let (q, A, B) := o
  let C := CTy.effOf S R
  let gw (k : Nat) (U : VTy) (body : TExpr) : TExpr :=
    -- `gw <- return (unbang g); body`, `g` at the slot `k`.
    .bind { sp, binders := [r1B] } (.comp C) U C noMasks
      (retAt sp U (.bangE (infoAt sp) (.val U) U (varAt sp k (.bang U)))) body
  if q == .zero then
    -- At `x :: Γ`: `g` at `g + 1`; after `gw`, `x` at `1`.
    let U : VTy := .thunk (.arr A C)
    let call := TExpr.app (infoAt sp) (.comp C) 1 A C noMasks
      (.force (infoAt sp) (.comp (.arr A C)) 0 (.arr A C))
    let Cw : CTy := .arr A C
    .bangThunkV (infoAt sp) (.val (.bang (.thunk Cw))) Cw
      (.lam { sp, name := r1B } (.comp Cw) A C (gw (g + 1) U call))
  else
    let K := BoCa.Fig16.LogRel.Core.kTy S R q.toQual B F
    let D : CTy := match K with
      | .thunk (.amp _ D) => D
      | _ => .top
    let CB : CTy := .arr B C
    let FB : CTy := CTy.effOf [] B
    let U : VTy := .thunk (.arr A FB)
    -- At `k :: x :: p :: Γ`: `g` at `g + 3`; after `gw`, `x` at `2`; after `w`, `k` at `2`.
    let resume := TExpr.app (infoAt sp) (.comp C) 0 B C noMasks
      (.proj₁ (infoAt sp) (.comp CB) CB D (.force (infoAt sp) (.comp (.amp CB D)) 2 (.amp CB D)))
    let callW := TExpr.app (infoAt sp) (.comp FB) 2 A FB noMasks
      (.force (infoAt sp) (.comp (.arr A FB)) 0 (.arr A FB))
    let body := TExpr.bind { sp, binders := [r1B] } (.comp C) B C noMasks callW resume
    let P : VTy := .tensor A K
    let Cw : CTy := .arr P C
    .bangThunkV (infoAt sp) (.val (.bang (.thunk Cw))) Cw
      (.lam { sp, name := r1B } (.comp Cw) P C
        (.tensorE { sp, binders := [r1B, r1B] } (.comp C) A K C noMasks (varAt sp 0 P)
          (gw (g + 3) U body)))

/-- The rule's clauses, as a tuple, the `j`-th's `g` at the slot `2 (e - 1 - j) + 1`. -/
def ruleClauses (sp : Frontend.Span) (S : Row) (R : VTy) (fs : Nat → CTy) (e : Nat) :
    List (Count × VTy × VTy) → Nat → TExpr
  | [], _ => .unitI (infoAt sp) (.val .unit)
  | o :: E, j =>
    .tensorI (infoAt sp) (.val .unit) .unit .unit noMasks
      (ruleClause sp S R (fs j) (2 * (e - 1 - j) + 1) o) (ruleClauses sp S R fs e E (j + 1))

/-- The works' tuple taken apart, `k` components on (`let (g, r) = v; …`), then `body`. -/
def takeApart (sp : Frontend.Span) (C : CTy) : Nat → TExpr → TExpr → TExpr
  | 0, _, body => body
  | k + 1, v, body =>
    .tensorE { sp, binders := [r1B, r1B] } (.comp C) .unit .unit C noMasks v
      (takeApart sp C k (varAt sp 0 .unit) body)

/-- **A node of a name the licence leaves** (`tToV`), written as the `[handle]` node it erases to:
its works' tuple taken apart (`takeApart`: each work a `!` value, bound outside the node); its
clauses the rule's own (`tailClause`, `ruleClause`), each over its work; its answer clause and
handled computation as they are. The kernel's re-check types it as `[handle]`'s, and no node of the
rule reaches the conversion. Records the clauses' `!`-introductions (G-bang). -/
def tToV (n : UInt32) : Nat → TExpr → TlM TExpr
  | 0, _ => throw "R1: a term nested too deeply"
  | f + 1, t => do
    match t with
    | .effHandleT i j S _ E fs nm A R u site ins tc te =>
      if nm != n then homLayer ⟨id, id, id, id⟩ (tToV n f) t else
      let .tensorI ti _ _ _ _ tr tw := tc | throw "R1: a handler's pair is not a pair"
      let tr' ← tToV n f tr
      let tw' ← tToV n f tw
      let te' ← tToV n f te
      let e := E.length
      let cls := ruleClauses i.sp S R fs e E 0
      modify fun st => { st with bangs := st.bangs + e, handles := st.handles + 1 }
      let tc' := TExpr.tensorI ti (.val .unit) .unit .unit noMasks (tr'.shift (2 * e) 0) cls
      let node := TExpr.effHandleV i j S E fs nm A R u (E.map BoCa.Fig16.LogRel.Core.ClauseKinds.tailKind)
        site ins tc' (te'.shift (2 * e) 0)
      pure (takeApart i.sp (CTy.effOf S R) e tw' node)
    | _ => homLayer ⟨id, id, id, id⟩ (tToV n f) t

mutual
/-- The planted fault `eraseOther`: the row of every `&`'s second component emptied, a codata
thunk's finish among them. -/
def eraseFinV : VTy → VTy
  | .tensor A B => .tensor (eraseFinV A) (eraseFinV B)
  | .sum A B => .sum (eraseFinV A) (eraseFinV B)
  | .thunk C => .thunk (eraseFinC C)
  | .ref A => .ref (eraseFinV A)
  | .imm l A => .imm l (eraseFinV A)
  | .mut l A => .mut l (eraseFinV A)
  | .box l A => .box l (eraseFinV A)
  | .bang A => .bang (eraseFinV A)
  | .mu A => .mu (eraseFinV A)
  | .fam L => .fam (eraseFinV L)
  | A => A
def eraseFinC : CTy → CTy
  | .ret A => .ret (eraseFinV A)
  | .arr A C => .arr (eraseFinV A) (eraseFinC C)
  | .amp C D => .amp (eraseFinC C) (dropChain D)
  | .top => .top
  | .all x b C => .all x b (eraseFinC C)
  | .nu C => .nu (eraseFinC C)
  | .eff m i c w A B fin C => .eff m i c w (eraseFinV A) (eraseFinV B) (eraseFinC fin) (eraseFinC C)
/-- A returner chain's operations removed. -/
def dropChain : CTy → CTy
  | .eff _ _ _ _ _ _ _ C => dropChain C
  | C => eraseFinC C
end

/-- The fault `eraseOther` over a typed term. -/
def eraseFin : Nat → TExpr → Except String TExpr
  | 0, _ => throw "R1: a term nested too deeply"
  | f + 1, t => homLayer ⟨eraseFinV, eraseFinC, fun S => S.map fun o =>
      { o with A := eraseFinV o.A, B := eraseFinV o.B, fin := eraseFinC o.fin },
      fun o => { o with A := eraseFinV o.A, B := eraseFinV o.B, fin := eraseFinC o.fin }⟩
      (eraseFin f) t

/-- The planted fault `dropWorkBinder`: the first binding of a typed term whose binder carries an
id loses it (`%R1`): the source binder has no image. -/
def stripId : Nat → TExpr → StateT Bool (Except String) TExpr
  | 0, _ => throw "R1: a term nested too deeply"
  | f + 1, t => do
    if !(← get) then
      match t with
      | .bind i .. | .effLet i .. =>
        if ((i.binders.head?).bind idOf?).isSome then
          set true
          return t.setInfo { i with binders := [r1B] }
      | _ => pure ()
    homLayer ⟨id, id, id, id⟩ (stripId f) t

/-- **R1's pass for the name `a`**: its works translated (the planted fault `weakenLin` applied to
them), each the declaration `base + j`; the typed term `t` and the earlier works `prev` rewritten.
Returns the term, the earlier works rewritten, and the name's works. -/
def r1Pass (a : TailName) (base : Nat) (t : TExpr) (prev : List (Nat × String × TExpr)) :
    TlM (TExpr × List (Nat × String × TExpr) × List (Nat × String × TExpr)) := do
  let ws ← a.works.mapM (tl a [] base [] fuel)
  let ws ← if (← get).seed == .weakenLin then
      let (ws', _) ← (ws.mapM (unLin fuel)).run false
      pure ws'
    else pure ws
  let ws ← if (← get).seed == .dropWorkBinder then
      let (ws', _) ← (ws.mapM (stripId fuel)).run false
      pure ws'
    else pure ws
  let t' ← tl a ws base prev fuel t
  let t' ← if (← get).seed == .eraseOther then eraseFin fuel t' else pure t'
  let prev' ← prev.mapM fun (d, nm, w) => do pure (d, nm, ← tl a ws base [] fuel w)
  pure (t', prev', ws.zipIdx.map fun (w, j) => (base + j, workName a.n j, w))

/-- The R1 works a typed term uses (`use` nodes of a declaration from `workBase`), every `use` body
included. -/
def worksUsed : Nat → TExpr → Except String (List Nat)
  | 0, _ => throw "R1: a term nested too deeply"
  | f + 1, t => do
    let here := match t with
      | .use _ _ _ d _ _ _ => if d ≥ workBase then [d] else []
      | _ => []
    t.children.foldlM (init := here) fun acc (_, c) => do pure (acc ++ (← worksUsed f c))

end Rewrite
