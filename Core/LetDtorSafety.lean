import Core.LetDtor
import Core.EffMachine
import Core.EffPrograms
import Core.DivRuntime
import Core.Closed

/-!
# Core — what a `[let-dtor]` frame guarantees, and resource safety  `[spec §62]`

**The run of one frame, per exit** (`[let-dtor]`'s term at a closing substitution `γ`, the values
of its context; `dropChain ds γ` is `drop_ctx` with each slot's value in place):

| exit of `M` | proved |
|---|---|
| raise `p` | `letDE_raise_run`: the frame reaches `dropChain ds γ; raise p`, whose first redex is the destructor of slot `0`, the variable bound last (`dropChain_some`); `dropChain_run`: if each destructor's run returns where it runs, they run in that order and `raise p` goes on unchanged (`letDE_raise_reraise`) |
| cancel | `letDE_cancel_run`: the frame reaches `cfin c (dropChain ds γ)`; with each destructor returning, the cancel goes on (`letDE_cancel_reraise`) |
| return `w` | `letDE_return_run`: the frame is discarded and `N` runs with `w` and the slots' values, no destructor run: `N` owns `Γ₂`, and its derivation consumes each live slot |

That each destructor's run returns where it runs is the hypothesis of `dropChain_run`
(`DropsReturn`), not derived here. `hSDc` and `hSDd` are why it is expected (a destructor neither
raises nor loops), and `resourceSafety` gives that the whole run reaches a value; deriving the
per-destructor statement from the relation is not done. The reverse order is within one frame
only: a program-wide statement that releases follow the reverse order of allocation is not made,
since `CDerives` has exchange (`Ctx.SplitP` interleaves freely) and a program may free its cells in
any order it writes.

**`resourceSafety`** is `adequacyD` read over cells. For every closed `CDerives` program at a
persistent answer, every run from the empty memory, under every allocator, continues to a value at
the empty memory (every cell it allocated is freed), and every `free ℓ` it reaches at an
evaluation position finds `ℓ` allocated (`step1_free_iff`), so its step removes `ℓ` and no cell is
freed twice. `[let-dtor]` is a derived form, so `resourceSafety` covers every program it types;
it says nothing about destructors as such. It sees memory only: a host resource counts as closed
only if its handle owns a cell and its type is linear with `close` its one eliminator, as the file
handle of `Core/LetDtorFiles.lean`.

That each allocation is released exactly once follows informally: an allocation picks a location
the memory does not hold (`step1_alloc_iff`), a release removes the one it frees, and the run
starts and ends at the empty memory. No theorem counts releases.

**At `[tickSig]`** (`rtSafety`): under the runtime's handler, every configuration a run of a
closed program at the row `{tick}` reaches is a value or steps, and every `free` it reaches finds
its cell, on terminating and diverging runs alike (`runtime_every_run`): progress and no double
free, without leak freedom.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core.EffPrograms (adequacyD_obs)
open BoCa.BoLo (Heap Steps Step1 Head Kont freeE raiseE hndE opPayload cancelVal cfinE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Resource safety** of every closed program at a persistent answer, `adequacyD` read over
cells: every run from the empty memory continues to a value at the empty memory (every cell
allocated is freed), and every release it reaches finds its cell allocated (none is freed twice).
`[spec §62]` -/
theorem resourceSafety {e : Expr} {A : VTy} (hA : A.Persistent)
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ e₁) :
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs hA h hs
  refine ⟨⟨v, hv⟩, fun K ℓ he => ?_⟩
  cases hv with
  | refl =>
      have hc : IsVal (K.plug (freeE (.val (Val.loc ℓ)))) := by rw [← he]; exact v.2
      have := K.isVal_of_plug hc
      cases this
  | more hst _ =>
      rw [he] at hst
      obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).mp hst
      exact ⟨u, hu⟩

/-- **The raise exit runs `drop_ctx`**: a raise `p` (not a cancel) reaching the `[let-dtor]` frame
through a context `K'` that catches nothing of its name steps to `drop_ctx`, then the same raise
(`[finalise]`).  `[spec §62]` -/
theorem letDE_finalise (μ : Heap) (ds : List (Option Expr)) (N : Expr) (n i : UInt32) (v : Val)
    (K K' : Kont) (hn : n ≠ 0) (hK : K'.Catches n = false) :
    Step1 (ℍ := ℍ) μ (K.plug (letDE ds N (K'.plug (raiseE (.val (opPayload n i v)))))) μ
      (K.plug (.seq (.app (.val (.lam (dropCtxE ds 1))) (.val .unit))
        (raiseE (.val (opPayload n i v))))) :=
  ⟨K, _, _, rfl, rfl, Head.ufin μ (.lam N) (.lam (dropCtxE ds 1)) n i v K' hn hK⟩

/-- **The cancel exit runs `drop_ctx`**: a cancel reaching the `[let-dtor]` frame runs `drop_ctx`
under `cfin`, which passes the cancel on when it returns (`[finalise-cancel]`).  `[spec §62]` -/
theorem letDE_finaliseCancel (μ : Heap) (ds : List (Option Expr)) (N : Expr) (err : Option Val)
    (K K' : Kont) (hK : K'.Catches 0 = false) :
    Step1 (ℍ := ℍ) μ (K.plug (letDE ds N (K'.plug (raiseE (.val (cancelVal err)))))) μ
      (K.plug (cfinE (cancelVal err) (.app (.val (.lam (dropCtxE ds 1))) (.val .unit)))) :=
  ⟨K, _, _, rfl, rfl, Head.ufinC μ (.lam N) (.lam (dropCtxE ds 1)) err K' hK⟩

/-- **Safety at `[tickSig]`, with no termination**: every configuration a run of `hnd rtH M`
reaches is a value or steps, and a `free` at an evaluation position finds its cell. Progress and
no double free; not leak freedom.  `[spec §14, §62]` -/
theorem rtSafety {M : Expr} {A : VTy}
    (h : CDerives LifeCtx.empty [] M (.comp (CTy.effOf [tickSig] A))) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (hndE DivRuntime.rtH M) μ₁ e₁) :
    (IsVal e₁ ∨ ∃ μ₂ e₂, Step1 (ℍ := ℍ) μ₁ e₁ μ₂ e₂) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u) := by
  have hgo := runtime_every_run h hs
  refine ⟨hgo, fun K ℓ he => ?_⟩
  subst he
  rcases hgo with hv | ⟨μ₂, e₂, hst⟩
  · have := K.isVal_of_plug hv
    cases this
  · obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).mp hst
    exact ⟨u, hu⟩

/-! ### The run of one frame -/

/-- **`drop_ctx` with the slots' values in place**: the destructor of each slot that has one,
applied to its value, the slot `0` first, each bound so that the next waits for it. -/
def dropChain : List (Option Expr) → List Val → Expr
  | [], _ => .val .unit
  | none :: ds, γ => dropChain ds γ.tail
  | some _ :: _, [] => .val .unit
  | some b :: ds, v :: γ => bindE (.app (.val (.lam b)) (.val v)) (dropChain ds γ)

/-- **Last in, first out**: the chain's first redex is the destructor of slot `0`, the variable
bound last, at its value; the rest waits for it.  `[spec §62]` -/
theorem dropChain_some (b : Expr) (ds : List (Option Expr)) (v : Val) (γ : List Val) :
    dropChain (some b :: ds) (v :: γ) = bindE (.app (.val (.lam b)) (.val v)) (dropChain ds γ) :=
  rfl

theorem closedAt_dropChain :
    ∀ {ds : List (Option Expr)} {γ : List Val}, (∀ b, some b ∈ ds → closedAt 1 b = true) →
      (∀ v ∈ γ, closedAt 0 v.1 = true) → closedAt 0 (dropChain ds γ) = true
  | [], _, _, _ => rfl
  | none :: ds, γ, hb, hγ => by
      refine closedAt_dropChain (ds := ds) (fun b h => hb b (List.mem_cons_of_mem _ h)) ?_
      intro v hv; exact hγ v (List.mem_of_mem_tail hv)
  | some _ :: _, [], _, _ => rfl
  | some b :: ds, v :: γ, hb', hγ => by
      have h1 := hb' b (by simp)
      have h2 := closedAt_dropChain (ds := ds) (γ := γ)
        (fun b h => hb' b (List.mem_cons_of_mem _ h)) (fun w hw => hγ w (List.mem_cons_of_mem _ hw))
      have h3 := hγ v (by simp)
      simp only [dropChain, bindE, closedAt, Bool.and_eq_true]
      exact ⟨closedAt_of_zero h2 1, h1, h3⟩

/-- **The closing substitution turns `drop_ctx` into the chain**: under `c` binders, the slots
from `j` on take their values from `γ`. -/
theorem psub_dropCtxE {γ : List Val} (hγ : ∀ v ∈ γ, closedAt 0 v.1 = true) :
    ∀ (ds : List (Option Expr)) (c j : Nat), (∀ b, some b ∈ ds → closedAt 1 b = true) →
      j + ds.length ≤ γ.length → Expr.psub c γ (dropCtxE ds (c + j)) = dropChain ds (γ.drop j)
  | [], _, _, _, _ => rfl
  | none :: ds, c, j, hb, hl => by
      simp only [dropCtxE, List.length_cons] at hl ⊢
      rw [show c + j + 1 = c + (j + 1) by omega,
        psub_dropCtxE hγ ds c (j + 1) (fun b h => hb b (List.mem_cons_of_mem _ h)) (by omega)]
      simp [dropChain, List.tail_drop]
  | some b :: ds, c, j, hb, hl => by
      simp only [List.length_cons] at hl
      have hj : j < γ.length := by omega
      rw [List.drop_eq_getElem_cons hj]
      have hv := hγ γ[j] (List.getElem_mem hj)
      have ih := psub_dropCtxE hγ ds (c + 1) (j + 1)
        (fun b h => hb b (List.mem_cons_of_mem _ h)) (by omega)
      rw [show c + 1 + (j + 1) = c + j + 2 by omega] at ih
      have hb0 := psub_closedAt b (j := c + 1) γ (hb b (by simp)) (by omega)
      simp only [dropCtxE, dropChain, bindE, Expr.psub, Val.lam, ih, hb0]
      simp [List.getElem?_eq_getElem hj, val_shift_closed hv]

/-- The frame of `[let-dtor]` at the closing substitution `γ`. -/
theorem substAll_letDE (ds : List (Option Expr)) (N M : Expr) (γ : List Val) :
    substAll γ (letDE ds N M) =
      BoCa.BoLo.ubindE (.pair (.lam (Expr.psub 1 γ N)) (.lam (Expr.psub 1 γ (dropCtxE ds 1))))
        (Expr.psub 0 γ M) := rfl

/-- `ubind (N, D) □`, the frame's evaluation context. -/
def frameK (N D : Expr) : Kont := .appR (.app (.val (.prim .ubind)) (.val (.pair (.lam N) (.lam D)))) .hole

theorem frameK_plug (N D e : Expr) :
    (frameK N D).plug e = BoCa.BoLo.ubindE (.pair (.lam N) (.lam D)) e := rfl

/-- The side conditions of a frame's run: closed values, closed destructors, a value per slot. -/
structure FrameOk (ds : List (Option Expr)) (γ : List Val) : Prop where
  vals : ∀ v ∈ γ, closedAt 0 v.1 = true
  dtors : ∀ b, some b ∈ ds → closedAt 1 b = true
  len : ds.length ≤ γ.length

theorem FrameOk.chain {ds : List (Option Expr)} {γ : List Val} (h : FrameOk ds γ) :
    Expr.psub 1 γ (dropCtxE ds 1) = dropChain ds γ := by
  simpa using psub_dropCtxE h.vals ds 1 0 h.dtors (by simpa using h.len)

theorem FrameOk.closed {ds : List (Option Expr)} {γ : List Val} (h : FrameOk ds γ) :
    closedAt 0 (dropChain ds γ) = true :=
  closedAt_dropChain h.dtors h.vals

/-- **The raise exit of one frame**: if `M`, at `γ`, reaches a raise `p` (not a cancel) through a
context `K'` that catches nothing of its name, the frame reaches `dropChain ds γ; raise p`: the
destructors of the slots, the slot bound last first, then the same raise.  `[spec §62]` -/
theorem letDE_raise_run {μ μ' : Heap} {ds : List (Option Expr)} {N M : Expr} {γ : List Val}
    (hok : FrameOk ds γ) (K K' : Kont) {n i : UInt32} {v : Val} (hn : n ≠ 0)
    (hK : K'.Catches n = false)
    (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 γ M) μ' (K'.plug (raiseE (.val (opPayload n i v))))) :
    Steps (ℍ := ℍ) μ (K.plug (substAll γ (letDE ds N M))) μ'
      (K.plug (.seq (dropChain ds γ) (raiseE (.val (opPayload n i v))))) := by
  rw [substAll_letDE]
  have h1 := Steps.plug (K.comp (frameK (Expr.psub 1 γ N) (Expr.psub 1 γ (dropCtxE ds 1)))) hM
  simp only [Kont.plug_comp, frameK_plug] at h1
  refine h1.trans (.more ⟨K, _, _, rfl, rfl, Head.ufin μ' _ _ n i v K' hn hK⟩ (.one ?_))
  refine ⟨K.comp (.seq .hole (raiseE (.val (opPayload n i v)))), _, _, ?_, ?_,
    Head.beta μ' (Expr.psub 1 γ (dropCtxE ds 1)) .unit⟩
  · simp [Kont.plug_comp, Kont.plug]
  · rw [hok.chain, subst_closedAt _ _ hok.closed (Nat.zero_le 0)]
    simp [Kont.plug_comp, Kont.plug]

/-- **The cancel exit of one frame**: a cancel reaching the frame through a context that catches
nothing of name `0` runs the chain under `cfin`, which passes the cancel on when it returns.
`[spec §62]` -/
theorem letDE_cancel_run {μ μ' : Heap} {ds : List (Option Expr)} {N M : Expr} {γ : List Val}
    (hok : FrameOk ds γ) (K K' : Kont) {err : Option Val} (hK : K'.Catches 0 = false)
    (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 γ M) μ' (K'.plug (raiseE (.val (cancelVal err))))) :
    Steps (ℍ := ℍ) μ (K.plug (substAll γ (letDE ds N M))) μ'
      (K.plug (cfinE (cancelVal err) (dropChain ds γ))) := by
  rw [substAll_letDE]
  have h1 := Steps.plug (K.comp (frameK (Expr.psub 1 γ N) (Expr.psub 1 γ (dropCtxE ds 1)))) hM
  simp only [Kont.plug_comp, frameK_plug] at h1
  refine h1.trans (.more ⟨K, _, _, rfl, rfl, Head.ufinC μ' _ _ err K' hK⟩ (.one ?_))
  refine ⟨K.comp (.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) .hole), _, _, ?_, ?_,
    Head.beta μ' (Expr.psub 1 γ (dropCtxE ds 1)) .unit⟩
  · simp [Kont.plug_comp, Kont.plug, cfinE]
  · rw [hok.chain, subst_closedAt _ _ hok.closed (Nat.zero_le 0)]
    simp [Kont.plug_comp, Kont.plug, cfinE]

/-- **The return exit of one frame**: if `M` returns `w`, the frame is discarded (`[then]`) and `N`
runs with `w` and the slots' values; no destructor runs, and `N` owns the slots.  `[spec §62]` -/
theorem letDE_return_run {μ μ' : Heap} {ds : List (Option Expr)} {N M : Expr} {γ : List Val}
    (K : Kont) {w : Val} (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 γ M) μ' (.val w)) :
    Steps (ℍ := ℍ) μ (K.plug (substAll γ (letDE ds N M))) μ'
      (K.plug ((Expr.psub 1 γ N).subst 0 w)) := by
  rw [substAll_letDE]
  have h1 := Steps.plug (K.comp (frameK (Expr.psub 1 γ N) (Expr.psub 1 γ (dropCtxE ds 1)))) hM
  simp only [Kont.plug_comp, frameK_plug] at h1
  exact h1.trans (.more ⟨K, _, _, rfl, rfl, Head.uthen μ' _ _ w⟩
    (.one ⟨K, _, _, rfl, rfl, Head.beta μ' _ w⟩))

/-- **Each destructor of the chain returns where it runs**: at the slot `0`, the destructor's
body at its value runs, in the context `K` and before the rest of the chain, to `()`; then the
rest. The hypothesis of `dropChain_run`.  `[spec §62]` -/
inductive DropsReturn (K : Kont) : Heap → List (Option Expr) → List Val → Heap → Prop where
  | nil (μ : Heap) (γ : List Val) : DropsReturn K μ [] γ μ
  | none {μ μ' : Heap} {ds : List (Option Expr)} {γ : List Val} :
      DropsReturn K μ ds γ.tail μ' → DropsReturn K μ (none :: ds) γ μ'
  | some {μ μ₁ μ' : Heap} {b : Expr} {ds : List (Option Expr)} {v : Val} {γ : List Val}
      (h : Steps (ℍ := ℍ) μ (K.plug (bindE (b.subst 0 v) (dropChain ds γ))) μ₁
        (K.plug (bindE (.val .unit) (dropChain ds γ)))) :
      DropsReturn K μ₁ ds γ μ' → DropsReturn K μ (some b :: ds) (v :: γ) μ'

/-- **The chain runs each destructor in turn**: where each returns, the chain runs them, the
slot bound last first, and returns `()`.  `[spec §62]` -/
theorem dropChain_run {K : Kont} {μ μ' : Heap} {ds : List (Option Expr)} {γ : List Val} :
    DropsReturn (ℍ := ℍ) K μ ds γ μ' → (∀ b, some b ∈ ds → closedAt 1 b = true) →
      (∀ v ∈ γ, closedAt 0 v.1 = true) →
      Steps (ℍ := ℍ) μ (K.plug (dropChain ds γ)) μ' (K.plug (.val .unit)) := by
  intro h
  induction h with
  | nil μ γ => intro _ _; exact .refl _ _
  | none _ ih =>
      intro hb hγ
      exact ih (fun b h => hb b (List.mem_cons_of_mem _ h))
        (fun v hv => hγ v (List.mem_of_mem_tail hv))
  | @some μ μ₁ μ' b ds v γ hrun _ ih =>
      intro hb hγ
      have hb' : ∀ b', some b' ∈ ds → closedAt 1 b' = true :=
        fun b' h => hb b' (List.mem_cons_of_mem _ h)
      have hγ' : ∀ w ∈ γ, closedAt 0 w.1 = true := fun w hw => hγ w (List.mem_cons_of_mem _ hw)
      have hcl := closedAt_dropChain hb' hγ'
      have hstep : Step1 (ℍ := ℍ) μ (K.plug (dropChain (some b :: ds) (v :: γ))) μ
          (K.plug (bindE (b.subst 0 v) (dropChain ds γ))) :=
        ⟨K.comp (.appR (.val (.lam (dropChain ds γ))) .hole), _, _,
          by simp [Kont.plug_comp, Kont.plug, dropChain, bindE],
          by simp [Kont.plug_comp, Kont.plug, bindE], Head.beta μ b v⟩
      refine .more hstep (hrun.trans ?_)
      refine .more ⟨K, _, _, rfl, rfl, Head.beta μ₁ (dropChain ds γ) .unit⟩ ?_
      rw [subst_closedAt _ _ hcl (Nat.zero_le 0)]
      exact ih hb' hγ'

/-- **The raise exit, completed**: where each destructor returns, the frame runs them, the slot
bound last first, and then the same raise `p` goes on.  `[spec §62]` -/
theorem letDE_raise_reraise {μ μ' μ'' : Heap} {ds : List (Option Expr)} {N M : Expr}
    {γ : List Val} (hok : FrameOk ds γ) (K K' : Kont) {n i : UInt32} {v : Val} (hn : n ≠ 0)
    (hK : K'.Catches n = false)
    (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 γ M) μ' (K'.plug (raiseE (.val (opPayload n i v)))))
    (hd : DropsReturn (ℍ := ℍ) (K.comp (.seq .hole (raiseE (.val (opPayload n i v))))) μ' ds γ μ'') :
    Steps (ℍ := ℍ) μ (K.plug (substAll γ (letDE ds N M))) μ''
      (K.plug (raiseE (.val (opPayload n i v)))) := by
  refine (letDE_raise_run hok K K' hn hK hM).trans ?_
  have h2 := dropChain_run hd hok.dtors hok.vals
  simp only [Kont.plug_comp, Kont.plug] at h2
  exact h2.trans (.one ⟨K, _, _, rfl, rfl, Head.seq μ'' _⟩)

/-- **The cancel exit, completed**: where each destructor returns, the frame runs them and the
cancel goes on (`[cfin-ret]`).  `[spec §62]` -/
theorem letDE_cancel_reraise {μ μ' μ'' : Heap} {ds : List (Option Expr)} {N M : Expr}
    {γ : List Val} (hok : FrameOk ds γ) (K K' : Kont) {err : Option Val}
    (hK : K'.Catches 0 = false)
    (hM : Steps (ℍ := ℍ) μ (Expr.psub 0 γ M) μ' (K'.plug (raiseE (.val (cancelVal err)))))
    (hd : DropsReturn (ℍ := ℍ)
      (K.comp (.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) .hole)) μ' ds γ μ'') :
    Steps (ℍ := ℍ) μ (K.plug (substAll γ (letDE ds N M))) μ''
      (K.plug (raiseE (.val (cancelVal err)))) := by
  refine (letDE_cancel_run hok K K' hK hM).trans ?_
  have h2 := dropChain_run hd hok.dtors hok.vals
  simp only [Kont.plug_comp, Kont.plug] at h2
  exact h2.trans (.one ⟨K, _, _, rfl, rfl, Head.cfret μ'' err .unit⟩)

end BoCa.Fig16.LogRel.Core

end
