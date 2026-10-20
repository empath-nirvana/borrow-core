import Frames.Rules

/-!
# Frames — the target theorems

Four statements, each of them one induction over `FDerives` or a composition with Core's own
theorems:

1. **Elaboration** (`FDerives.elab`): every frame's elaborated term is a `CDerives` derivation at
   the frame type. One case per frame rule; it needs the dead-binder weakening of `CDerives`
   (`CDerives.shift_dead`, obligation O1).
2. **Conservativity** (`frame_sound`, `frame_adequacy`, `core_conservative`): nothing of Core is
   changed, so `fundamentalC`, `adequacyC` and `adequacyD` cover every frame through its
   elaboration, and a Core computation embedded as a frame runs as it did.
3. **Accounting** (`accounting`): every exit of a well-typed frame hands back each of its slots,
   the same slot at the same position, exactly once; one induction over `FDerives`.
4. **Agreement with §19** (`frame_handled`, `frame_unwind_leakfree`): `raise` and abort leave a
   frame by §19's unwinding, through Core's own `[handle]` and `[then]`; the frame adds no rule
   for them.

Proofs that are not cheap are enumerated `sorry`s, each with a note on what it needs. The rest
are proved, to show the statements well-formed and not vacuous (`not_returns_swap`: a Core term
at the frame type that swaps two slots satisfies the typing and fails the accounting).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### O1: the weakening the elaboration needs -/

/-- **O1.** A derivation stays one under a new dead binder at the front, its term shifted: Core's
`CDerives.insert_dead` at `Γa = []`, `Γd = [⟨T, false⟩]`. -/
theorem CDerives.shift_dead {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (T : VTy)
    (h : CDerives Δ Γ e j) : CDerives Δ (⟨T, false⟩ :: Γ) (e.shift 1 0) j :=
  Core.CDerives.insert_dead (Γd := [⟨T, false⟩]) (.cons .nil) h [] Γ rfl

/-! ### 1. Elaboration -/

/-- **Elaboration**: a frame is a `CDerives` derivation at its frame type. -/
theorem FDerives.elab {Δ : LifeCtx} {Γ : Ctx VTy} {Φ : List FBlock} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy} (hΦ : ∀ b ∈ Φ, b.Wf Δ)
    (h : FDerives Δ Γ Φ Ps e S E A) : CDerives Δ Γ e (.comp (frTy S Ps E A)) := by
  induction h with
  | core hS hP hN =>
      -- `lam` over `effThenA`: `M = N↑` by O1; the continuation `(π, inl x)` by `tensorI` and
      -- `effSub` from `F`; the finaliser `dtor_Π π` by `dtor_wf` at `SlotsOk.hasDtor`.
      sorry
  | exit hk hV =>
      -- `lam` over `effSub (RowLe.nil)` of `ret (tensorI (var 0) (inj₂ (injAt k V↑)))`, the
      -- injection typed by induction on `k` against `E[k]? = some (l, B)` (`sumTy_get`); O1 for `V↑`.
      sorry
  | bind hs hW hU hM hN ihM ihN =>
      -- `lam` over `effLet`: `M↑ π` by `app` and O1; the continuation by `tensorE`, `sumE`,
      -- `app` twice on `N`'s elaboration shifted by 5 (O1, five times).
      sorry
  | case hs hV h₁ h₂ ih₁ ih₂ =>
      -- `lam` over `sumE`, each arm `app` twice on the arm's elaboration shifted by 2 (O1).
      sorry
  | «catch» hs hW hU hM hH ihM ihH =>
      -- as `bind`, with a second `sumE` on `⊕((l, B) :: E) = B ⊕ ⊕E`: the head summand to `H`.
      sorry
  | under hS hQ hM ih =>
      -- `lam`, `tensorE` on `π`, `effThenA` with the finaliser `dtor_Q q`.
      sorry
  | use src x hx hS hS' hP hsrc hB hN =>
      -- `withbor2U`/`withbor3U` at `src` (its `hS : S.Unwind x`, `LendOk`), `force` and `app`
      -- twice, `effThenA` with `dtor_Π ρ`; `effThen` at `Σ_M = Σ`.
      sorry
  | lend src x hx hS hsrc hΓx hfree hM ih =>
      -- the callback: `allI` at `'x` (`hΓx`), `lam`, the inner frame by `ih` under O1, `forget`
      -- at `Mut 'x A`, `boxI` (`'x ⊏ ⊓Δ`, and `hfree`: the slots and exits do not mention `'x`);
      -- then as `use`.
      sorry
  | new hs hA hV hM ih =>
      -- `alloc`, `ret`, `effSub`; `effLet` over the pair `(c, π)`; `free` and `dtor_wf` at `Ref A`.
      sorry
  | loopCount hs hs₁ hp hn hs0 hM ih =>
      -- `countTry (slots ⊗ S₀) (slots ⊗ (B ⊕ ⊕E))` and `lolliE`; the step by `bangThunkF` over
      -- `Persistent Γ₂`, its body by `tensorE` twice and `app` thrice on `ih` under O1.
      sorry
  | loopIter hdiv hs hp hS₀ hs0 hM ih =>
      -- `iterate S (slots ⊗ S₀) (slots ⊗ (B ⊕ ⊕E)) (slots ⊗ 1)` at `hdiv`; the step by
      -- `bangThunkV`, `withI`, its `close` by `dtor_wf` at `S₀`.
      sorry
  | callBlock hk hj =>
      -- `lam`, `app` twice: the block from `hΦ` (`FBlock.Wf`, `bangE`, closed so unshifted).
      sorry
  | sub hle h ih =>
      -- `lam` over `effSub hle` of `e↑ π` (O1).
      sorry

/-! ### 2. Conservativity -/

/-- **Frames are sound** at Core's own relation: `fundamentalC` at the elaboration. Nothing in
the relation, the model or `CDerives` is changed for frames. -/
theorem frame_sound {Δ : LifeCtx} {Γ : Ctx VTy} {Φ : List FBlock} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy} (hΦ : ∀ b ∈ Φ, b.Wf Δ)
    (h : FDerives Δ Γ Φ Ps e S E A) : SemC Δ Γ e (frTy S Ps E A) :=
  fundamentalC (FDerives.elab hΦ h)

/-- A closed frame over no slots, run on `()`. -/
def runFrameE (e : Expr) : Expr := .app (.val (.lam (.app (sh 1 e) (.var 0)))) (.val .unit)

/-- The run of a closed frame is a Core computation. -/
theorem runFrame_derives {Φ : List FBlock} {e : Expr} {A : VTy}
    (hΦ : ∀ b ∈ Φ, b.Wf LifeCtx.empty) (h : FDerives LifeCtx.empty [] Φ [] e [] [] A) :
    CDerives LifeCtx.empty [] (runFrameE e) (.comp (.ret (.tensor .unit (exitsTy A [])))) :=
  .bind (Γ₁ := []) (Γ₂ := []) .nil (.ret (.unitI .nil))
    (.app (Γ₁ := [⟨.unit, false⟩]) (Γ₂ := [⟨.unit, true⟩]) (.right .nil)
      (CDerives.shift_dead .unit (FDerives.elab hΦ h)) (.here .nil))

/-- **Adequacy for frames**, `adequacyD_obs` unchanged: every run of a closed frame program at a
persistent answer, from the empty memory, continues to a value at the empty memory. -/
theorem frame_adequacy {Φ : List FBlock} {e : Expr} {A : VTy} (hA : A.Persistent)
    (hΦ : ∀ b ∈ Φ, b.Wf LifeCtx.empty) (h : FDerives LifeCtx.empty [] Φ [] e [] [] A)
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem (runFrameE e) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls, vP (.tensor .unit (exitsTy A [])) ls LSub.empty v PMap.empty := by
  have hp : (VTy.tensor .unit (exitsTy A [])).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, exitsTy, ExitRow.sumTy, Bool.true_and,
      Bool.and_true]
    exact hA
  exact EffPrograms.adequacyD_obs hp (runFrame_derives hΦ h) hs

/-- **A Core computation is a frame, and runs as it did.** On every run, `core N` on the slots
`π` reaches `(π, inl v)` exactly when `N` reaches `v`, at the same memory.
`sorry`: `[then]`'s step (`Head.ubind` at a value) after the β step; the converse by
determinism of the frames around `N` (`head_det_eff`) and `Kont` plugging. -/
theorem core_conservative (Ps : List VTy) (N : Expr) (hN : closedAt 0 N = true) (π : Val)
    (μ μ' : Heap) (v : Val) :
    Steps μ N μ' (.val v) ↔
      Steps μ (.app (coreE Ps N) (.val π)) μ' (.val (Val.pair π (Val.inj₁ v))) := by
  sorry

/-- **No Core rule is touched**: the frame judgment's `core` rule takes every `CDerives`
computation, so a program that uses no frame is its own `CDerives` derivation, and every Core
theorem holds of it unchanged (the library is not edited; `make gate`'s kernel counts and goldens
check that). Stated as the embedding at a frame over no slots and no exits. -/
theorem core_embeds {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {S : Row} {A : VTy} (Φ : List FBlock)
    (hS : FRow S) (hN : CDerives Δ Γ N (.comp (CTy.effOf S A))) :
    FDerives Δ Γ Φ [] (coreE [] N) S [] A :=
  .core hS (fun _ h => absurd h List.not_mem_nil) hN

/-! ### 3. Accounting -/

/-- One step of the accounting invariant `R` at `t`: every run from `t` that reaches a value
reaches `(π, x)`, the slots `π` themselves beside an exit tag; and every run that stops at an
operation no handler in it handles (a `Div` tick, an outer handler's operation) is resumed, at
every answer, into a term of `R`. A run that stops at a `raise` leaves by §19's unwinding
(`frame_unwind_leakfree`). -/
def RetsStep (π : Val) (R : Expr → Prop) (t : Expr) : Prop :=
  (∀ (μ μ' : Heap) (w : Val), Steps μ t μ' (.val w) → ∃ x : Val, w = Val.pair π x) ∧
  (∀ (μ μ' : Heap) (K : Kont) (n i : UInt32) (v : Val),
    Steps μ t μ' (K.plug (performE (.val (opPayload n i v)))) → K.HasHnd n = false →
    ∀ w : Val, R (K.plug (.val w)))

/-- **The slots come back**, coinductively: `t` is in an invariant closed under `RetsStep`. It is
a greatest fixed point because a div loop stops at a tick at every turn, forever. A unary
property of machine runs at one value `π`; it reads no type and no resource. -/
def Rets (π : Val) (t : Expr) : Prop :=
  ∃ R : Expr → Prop, R t ∧ ∀ t', R t' → RetsStep π R t'

/-- A frame term hands back the slots it is given, whatever they are. -/
def Returns (e : Expr) : Prop := ∀ π : Val, Rets π (.app e (.val π))

/-- A block hands back the slots on every argument. -/
def FBlock.Returns (b : FBlock) : Prop := ∀ a : Val, Frames.Returns (.app (.val b.v) (.val a))

/-- **Accounting**: every exit of a well-typed frame returns each of its slots exactly once, the
same slot at the same position. ONE induction over `FDerives`; each case uses only its premises'
induction hypotheses. A rule added to `FDerives` fails this proof until its case is written.

Each case's `sorry` names the machine facts it needs. None mentions two frame rules: a case
needs its own term's steps and the hypothesis of each premise. -/
theorem accounting {Δ : LifeCtx} {Γ : Ctx VTy} {Φ : List FBlock} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy} (hΦ : ∀ b ∈ Φ, b.Returns)
    (h : FDerives Δ Γ Φ Ps e S E A) : ∀ γ : List Val, Returns (substAll γ e) := by
  induction h with
  | core hS hP hN =>
      -- β, then `[then]`: the invariant is `{ubind ((π, inl ·), dtor π) t | every t}`; at a value
      -- `x` the continuation answers `(π, inl x)`; at a stop of `t` the resumption is
      -- `ubind (…) K_t[w]`, again in the invariant. No induction on `N`.
      sorry
  | exit hk hV =>
      -- β; the payload is a value term (ANF) once closed, so the answer is `(π, inr (inj_k v))`;
      -- a value-judgment term's call-by-value calls (`lolliE`) do not see `π`.
      sorry
  | bind hs hW hU hM hN ihM ihN =>
      -- the invariant is `ihM`'s invariant under the `let` frame, union `ihN`'s at each answer:
      -- `M` answers `(π, r)`; `inl a`: `ihN` at `π` (the same `π`); `inr e`: `(π, inr e)`.
      sorry
  | case hs hV h₁ h₂ ih₁ ih₂ =>
      -- the scrutinee is a value; the arm's hypothesis at `π`.
      sorry
  | «catch» hs hW hU hM hH ihM ihH =>
      -- `ihM` at `π`, then `ihH` at `π` on the head exit; the other answers pass with `π`.
      sorry
  | under hS hQ hM ih =>
      -- `π = (q, ρ)`; `ih` at `ρ` gives `(ρ, r)`; the answer `((q, ρ), r) = (π, r)`.
      sorry
  | use src x hx hS hS' hP hsrc hB hN =>
      -- `π = (p, ρ)`; `withborU`'s term answers `(p, b)` with the source `p` itself
      -- (`withborUE`'s body `(r, b)`); the answer `((p, ρ), inl b) = (π, inl b)`.
      sorry
  | lend src x hx hS hsrc hΓx hfree hM ih =>
      -- `π = (p, ρ)`; in the callback `ih` at `(b, ρ)` gives `((b, ρ), r)`, so the callback
      -- answers `(ρ, r)`; `withborU` hands back `p`; the answer `((p, ρ), r)`.
      sorry
  | new hs hA hV hM ih =>
      -- `alloc` gives `c`; `ih` at `(c, π)` gives `((c, π), r)`; the answer `(π, _)`.
      sorry
  | loopCount hs hs₁ hp hn hs0 hM ih =>
      -- induction on the steps left of `count_try` (`countTryNext`, `wpTS_countTry`'s head
      -- step): each turn is `ih` at `π`, answering `inl (π, s')` or `inr (π, x)`, so the state
      -- holds `π` at every turn.
      sorry
  | loopIter hdiv hs hp hS₀ hs0 hM ih =>
      -- the invariant: `iterate` at a state `(π, s)`, and each turn under it (`ih`'s invariant);
      -- a tick is a stop resumed into the next turn; `close` answers `(π, ())`. The greatest
      -- fixed point is what lets a loop that ticks forever satisfy it.
      sorry
  | callBlock hk hj =>
      -- `hΦ` at the block and the argument `γ[j]`.
      sorry
  | sub hle h ih =>
      -- β; then `ih` at `π`: `subE e π` runs `e π`.
      sorry

/-- Blocks built from frames return their slots: a block of the program typed by `FDerives`
satisfies the hypothesis `accounting` asks of `Φ`. -/
theorem block_returns {Δ : LifeCtx} {Φ : List FBlock} {B : VTy} {Ps : List VTy} {e : Expr}
    {S : Row} {E : ExitRow} {A : VTy} (hΦ : ∀ b ∈ Φ, b.Returns)
    (h : FDerives Δ [⟨B, true⟩] Φ Ps e S E A) :
    FBlock.Returns ⟨Val.lam e, B, S, Ps, E, A⟩ := by
  -- β at the argument `a`, then `accounting` at `γ = [a]` (`substAll [a] e = e[a/0]`).
  sorry

/-! ### 4. Agreement with §19: raise and abort -/

/-- **A frame is handled by Core's own `[handle]`.** A frame at a row with the operations of
`n`, run on no slots, under a handler of `n`: the handled computation is a `CDerives` derivation
by `effHandleV`, so raise and abort out of a frame are §19's `[unwind]`/`[finalise]`, with no
frame rule for them. -/
theorem frame_handled {Φ : List FBlock} {e H : Expr} {S : Row} {Eff : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} (hΦ : ∀ b ∈ Φ, b.Wf LifeCtx.empty)
    (h : FDerives LifeCtx.empty [] Φ [] e (Row.ofEff n Eff 0 ++ S) [] A)
    (hH : H.ValFormIn [])
    (hc : CDerives LifeCtx.empty [] H
      (.val (.tensor (retTy S (.tensor .unit (exitsTy A [])) R) (clausesTy S R Eff finsNil))))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : Eff.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n Eff 0 ++ S) = false) :
    CDerives LifeCtx.empty [] (hndExpr n (Eff.map Prod.fst) H (runFrameE e))
      (.comp (CTy.effOf S R)) := by
  -- `effHandleV` at the split `[] = [], []`, with the handled computation `runFrameE e`: the
  -- `[let]` of `()` at the handled row (`effLet`, nothing in its context) over `app` of the
  -- elaboration under O1. `sorry`: that `effLet` at the row (`runFrame_derives` is its pure case).
  sorry

/-- **Leak freedom across a raise.** Every run of a closed, handled frame program at a persistent
answer, from the empty memory, continues to a value at the empty memory, whether or not the frame
raised: every slot the frame owned was finalised, once, by §19's unwinding (the holders'
`[then]` finalisers and the unwinding borrow constants). `adequacyD_obs` unchanged. -/
theorem frame_unwind_leakfree {Φ : List FBlock} {e H : Expr} {Eff : List (Qual × VTy × VTy)}
    {n : UInt32} {A R : VTy} (hR : R.Persistent) (hΦ : ∀ b ∈ Φ, b.Wf LifeCtx.empty)
    (h : FDerives LifeCtx.empty [] Φ [] e (Row.ofEff n Eff 0) [] A)
    (hH : H.ValFormIn [])
    (hc : CDerives LifeCtx.empty [] H
      (.val (.tensor (retTy [] (.tensor .unit (exitsTy A [])) R) (clausesTy [] R Eff finsNil))))
    (hn0 : n ≠ 0) (hlen : Eff.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n Eff 0 ++ []) = false)
    {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (hndExpr n (Eff.map Prod.fst) H (runFrameE e)) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧ ∃ ls, vP R ls LSub.empty v PMap.empty := by
  have h' : FDerives LifeCtx.empty [] Φ [] e (Row.ofEff n Eff 0 ++ []) [] A := by
    simpa using h
  exact EffPrograms.adequacyD_obs hR
    (frame_handled hΦ h' hH hc hn0 (fun _ h => absurd h List.not_mem_nil) hlen hdv) hs

end BoCa.Fig16.LogRel.Core.Frames

end
