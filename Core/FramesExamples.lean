import Core.FramesTheorems
import Core.Run

/-!
# Core — frames: examples  `[spec §47]`

- `swapE` is a Core term at a frame type over two slots of one type that hands them back
  swapped. It is a `CDerives` derivation at the frame type (`swap_derives`), and it fails the
  accounting (`not_returns_swap`): typing at `Fr Σ Π E A` alone does not give the accounting,
  and the frame rules, which never hand `π` to Core code, do.
- `nested` is a frame derivation of depth 4 (`new` ⊃ `catch` ⊃ `loopCount` ⊃ `case` ⊃ `exit`)
  whose innermost exit leaves two catchers out: the `break` of the loop, and an exit past the
  loop to the `catch` around it. Its accounting is `accounting` at it, with no case of its own
  (`nested_returns`).
- `moveJoin` is a slot whose content is moved out and, on one arm of a case, put back: the arms
  leave the cell in two states, joined into `Ref i32 ⊕ Ref 1` by `widen`, and the cell's release
  at the end of its scope reads the tag (`moveJoin_derives`, `moveJoin_returns`).
- `not_bindOne`: the single-`Π_out` frame type does not compose under `bind`. A move out with an
  exit, then a put back, typed by a `bind` at one state, makes a closed program at a persistent
  answer whose run hands out the hole's `()` as an `i32`, against adequacy. The two-state `bind`
  types the same frames (`movePut_derives`, `moveExitCaught_derives`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Non-vacuity: a well-typed swap -/

/-- Two cells of `1`. -/
abbrev twoCells : List VTy := [.ref .unit, .ref .unit]

/-- `λπ. let (a, ρ) = π; let (b, u) = ρ; inl ((b, (a, u)), ())`. -/
def swapE : Expr :=
  .lam (.letpair (.var 0) (.letpair (.var 0)
    (.inj₁ (.pair (.pair (.var 1) (.pair (.var 3) (.var 0))) (.val .unit)))))

/-- The swap is typed at the frame type over two cells. -/
theorem swap_derives :
    CDerives LifeCtx.empty [] swapE (.comp (frTy [] twoCells twoCells twoCells [] .unit)) := by
  show CDerives LifeCtx.empty [] (.val (.lam _)) (.comp (.arr _ (.ret _)))
  refine .lam (.tensorE (.left .nil) (.var (.here .nil)) ?_)
  refine .tensorE (.left (.right (.dead .nil))) (.var (.here (.cons (.cons .nil)))) ?_
  refine .ret (.sumI₁ (.tensorI (.left (.left (.dead (.left (.dead .nil))))) ?_
    (.unitI (.cons (.cons (.cons (.cons (.cons .nil))))))))
  refine .tensorI (.right (.left (.dead (.right (.dead .nil)))))
    (.var (.there (.here (.cons (.cons (.cons .nil)))))) ?_
  exact .tensorI (.right (.dead (.dead (.left (.dead .nil)))))
    (.var (.there (.there (.there (.here (.cons .nil))))))
    (.var (.here (.cons (.cons (.cons (.cons .nil))))))

/-- Two distinct cells as slots. -/
def twoLocs : Val := Val.pair (Val.loc 0) (Val.pair (Val.loc 1) Val.unit)

/-- The swapped answer. -/
def swapped : Val :=
  Val.inj₁ (Val.pair (Val.pair (Val.loc 1) (Val.pair (Val.loc 0) Val.unit)) Val.unit)

/-- The swap's run: β and two `let`s. -/
theorem swap_runs (μ : Heap) : Steps μ (.app swapE (.val twoLocs)) μ (.val swapped) := by
  refine .more (Step1.head (Head.beta μ _ twoLocs)) ?_
  refine .more (Step1.head (Head.letpair μ (Val.loc 0) (Val.pair (Val.loc 1) Val.unit) _)) ?_
  refine .more (Step1.head (Head.letpair μ (Val.loc 1) Val.unit _)) ?_
  exact .refl _ _

/-- **The accounting is not a consequence of typing**: the swap is typed at the frame type and
does not hand back its slots. -/
theorem not_returns_swap : ¬ Returns (ℍ := ℍ) swapE := by
  intro h
  obtain ⟨R, hR, hinv⟩ := h twoLocs
  obtain ⟨hval, -⟩ := hinv _ hR
  obtain ⟨π', x, hπ, hx | hx⟩ := hval _ _ _ (swap_runs (ℍ := ℍ) (fun _ => none))
  · have := congrArg Subtype.val hx
    simp only [swapped, Val.inj₁, Val.pair, Expr.inj₁.injEq, Expr.pair.injEq] at this
    obtain ⟨h₁, -⟩ := this
    have h₂ : slotCells π'.1 = slotCells twoLocs.1 := hπ
    rw [← h₁] at h₂
    simp [slotCells, twoLocs, Val.pair, Val.loc] at h₂
  · have := congrArg Subtype.val hx
    simp [swapped, Val.inj₁, Val.inj₂, Val.pair] at this

/-! ### A nesting of depth 4 -/

/-- `let mut c = (); 'out: { loop[3] { case s { inl _ → break 'loop () | inr _ → exit 'out () } } }`
written as frames: `new () (catch (bind (loopCount 3 s₀ (case s (exit 0 ()) (exit 1 ()))) …) h)`.
The loop's turn sees the exits `[break 'loop, exit 'out]`; `exit 1` crosses the loop and lands
at the `catch`. -/
def nestedTurn : Expr :=
  caseE (.var 0) (exitE 0 (.val .unit)) (exitE 1 (.val .unit))

/-- The loop's state: `1 ⊕ 1`. -/
abbrev bit : VTy := .sum .unit .unit

theorem nestedTurn_derives (Ps : List VTy) :
    FDerives LifeCtx.empty [⟨bit, true⟩, ⟨.int .w32, true⟩] [] Ps Ps Ps nestedTurn []
      [(0, .unit), (1, .unit)] bit := by
  refine .case (A := .unit) (B := .unit) (Γs := [⟨bit, true⟩, ⟨.int .w32, false⟩])
    (Γb := [⟨bit, false⟩, ⟨.int .w32, true⟩]) (.left (.right .nil)) ?_ ?_ ?_
  · exact .var (.here (.cons .nil))
  · exact .exit (k := 0) (l := 0) (B := .unit) rfl
      (.unitI (.drop rfl (.cons (.drop rfl .nil))))
  · exact .exit (k := 1) (l := 1) (B := .unit) rfl
      (.unitI (.drop rfl (.cons (.drop rfl .nil))))

/-- The loop, three turns from `inl ()`. -/
def nestedLoop : Expr :=
  loopCountE [.keep] (Val.i32 3).1 (.inj₁ (.val .unit)) nestedTurn

theorem nestedLoop_derives :
    FDerives LifeCtx.empty [] [] [.ref .unit] [.ref .unit] [.ref .unit] nestedLoop [] [(1, .unit)]
      (.sum bit .unit) :=
  .loopCount (Γ₁ := []) (Γn := []) (Γs := []) (Γ₂ := []) .nil .nil
    (fun _ h => absurd h List.not_mem_nil) (.cons .keep .nil) (.lit (.i32 3) .nil)
    (.sumI₁ (.unitI .nil)) (nestedTurn_derives _)

/-- After the loop, `'out`'s handler, and the frame: `new () (catch nestedLoop (core (return ())))`,
the loop's answer dropped by the `catch`'s normal arm. -/
def nested : Expr :=
  newE (.full .unit) (.ref .unit) (.val .unit)
    (catchE [] (bindE [(1, .unit)] [] nestedLoop (coreE [.ref .unit] (.val .unit)))
      (coreE [.ref .unit] (.val .unit)))

theorem frow_nil : FRow [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩

theorem slotsOk_cell : SlotsOk [.ref .unit] := by
  intro P hP
  simp only [List.mem_singleton] at hP
  subst hP
  exact .ref .unit

/-- **The depth-4 nesting is a frame**: `new ⊃ catch ⊃ bind ⊃ loopCount ⊃ case ⊃ exit`. -/
theorem nested_derives :
    FDerives LifeCtx.empty [] [] [] [] [] nested [] [] (.tensor .unit .unit) := by
  refine .new (Γ₁ := []) (Γ₂ := []) (q := .full .unit) .nil .unit .unit (.ref .unit) (.unitI .nil) ?_
  refine .catch (Γ₁ := []) (Γ₂ := []) (l := 1) (B := .unit) .nil
    (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) ?_ ?_
  · refine .bind (Γ₁ := []) (Γ₂ := []) .nil
      (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
      (.inr fun _ h => absurd h List.not_mem_nil) nestedLoop_derives ?_
    exact .core frow_nil slotsOk_cell (.ret (.unitI (.drop rfl .nil)))
  · exact .core frow_nil slotsOk_cell (.ret (.unitI (.drop rfl .nil)))

/-- **Its accounting is the general theorem's**: no case of its own. -/
theorem nested_returns : Returns (ℍ := ℍ) nested := by
  have h := accounting (ℍ := ℍ) (fun _ h => absurd h List.not_mem_nil) nested_derives []
  simpa [substAll, Adequacy.psub_nil] using h

/-- **And it runs to a value at the empty memory**, by `frame_adequacy`. -/
theorem nested_adequate {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (runFrameE nested) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls, vP (ansTy [] [] (.tensor .unit .unit) []) ls LSub.empty v PMap.empty :=
  frame_adequacy rfl nested_derives hs

/-! ### Typestate: a move out, a put back on one arm, the join -/

/-- `let mut c = 7; let x = take c; case b { inl _ → put c x | inr _ → () }; …`: the cell is
moved out of (`swap c ()`), put back on the first arm (`swap c x`, widened to the first state)
and left empty on the second (widened to the second); the cell's release at its scope's end
reads the tag. -/
def moveArms : Expr :=
  caseE (.var 1)
    (widenE [.inl] [.inl] (swapSE (.var 1)))
    (widenE [.inr] [.inr] (coreE [.ref .unit] (.val .unit)))

def moveJoin : Expr :=
  newE (.sum (.full .i32) (.full .unit)) (.sum (.ref .i32) (.ref .unit)) (Val.i32 7).1
    (bindE [] [⟨bit, true⟩] (swapSE (.val .unit)) moveArms)

/-- The cell in two states. -/
abbrev twoStates : VTy := .sum (.ref .i32) (.ref .unit)

theorem moveArms_derives :
    FDerives LifeCtx.empty [⟨.i32, true⟩, ⟨bit, true⟩] [] [.ref .unit] [twoStates] [twoStates]
      moveArms [] [] .unit := by
  refine .case (A := .unit) (B := .unit) (Γs := [⟨.i32, false⟩, ⟨bit, true⟩])
    (Γb := [⟨.i32, true⟩, ⟨bit, false⟩]) (.right (.left .nil)) (.var (.there (.here .nil))) ?_ ?_
  · refine .widen (Pn := [.ref .i32]) (X := [.ref .i32]) (.cons .inl .nil) (.cons .inl .nil) ?_
    exact .swap .int (.var (by csoloP))
  · refine .widen (Pn := [.ref .unit]) (X := [.ref .unit]) (.cons .inr .nil) (.cons .inr .nil) ?_
    exact .core frow_nil slotsOk_cell
      (.ret (.unitI (.drop rfl (.drop rfl (.cons .nil)))))

/-- **A typestate slot is a frame**: `new ⊃ bind ⊃ (swap; case ⊃ widen ⊃ swap | widen ⊃ core)`,
the cell's state at its normal exit `Ref i32 ⊕ Ref 1`, its content handed out as `i32 ⊕ 1`. -/
theorem moveJoin_derives :
    FDerives LifeCtx.empty [⟨bit, true⟩] [] [] [] [] moveJoin [] [] (.tensor .unit (.sum .i32 .unit)) := by
  refine .new (Γ₁ := [⟨bit, false⟩]) (Γ₂ := [⟨bit, true⟩]) (q := .sum (.full .i32) (.full .unit))
    (.right .nil) .int ⟨.int, .unit⟩ (.sum (.ref .int) (.ref .unit)) (.lit (.i32 7) (.cons .nil)) ?_
  refine .bind (Γ₁ := [⟨bit, false⟩]) (Γ₂ := [⟨bit, true⟩]) (.right .nil)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil)
    (.inl rfl) ?_ moveArms_derives
  exact .swap .unit (.unitI (.cons .nil))

/-- **Its accounting is the general theorem's**: the cell comes back on every exit, whatever its
state. -/
theorem moveJoin_returns (b : Val) : Returns (ℍ := ℍ) (substAll [b] moveJoin) :=
  accounting (ℍ := ℍ) (fun _ h => absurd h List.not_mem_nil) moveJoin_derives [b]

/-! ### Why the normal exit and the local exits have a state each

The single-`Π_out` form of the frame type, `Π ⊸ F_Σ (Π_out ⊗ (A ⊕ ⊕E))`, is `frTy S P Po Po E A`
(the slots distributed over the sum): one state for the normal exit and every exit. Its `bind`
would type `M; N` at `N`'s state, `P₀ → P₂ / P₂`, from `M : P₀ → P₁ / P₁` and `N : P₁ → P₂ / P₂`.
An exit of `M` skips `N` and leaves at `P₁`, so that typing claims a state the slots are not in.
`moveExit` moves a cell's content out and exits with the cell empty (`Ref 1`); `putBack` fills it
again (`Ref i32`). Both are single-state frames (`moveExit_derives`, `putBack_derives`). Composed
by the single-state `bind`, caught by a handler that leaves the slot as it is, and closed by `new`,
they make a closed program typed at a persistent answer whose run hands out the empty cell's
content `()` as an `i32` (`moveExitPut_runs`), against adequacy: `not_bindOne`. With a state for
each exit kind, `bind` composes the same frames at `[Ref i32] → [Ref i32] / [Ref 1]`, and the
handler is typed from `Ref 1` (`movePut_derives`, `moveExitCaught_derives`). -/

/-- The row of one local exit, with no payload. -/
abbrev rowX : ExitRow := [(0, .unit)]

/-- `let x = take c; exit 0 ()`: the content moved out (`swap c ()`), then an exit with the cell
empty. -/
def moveExit : Expr := bindE rowX [] (swapSE (.val .unit)) (exitE 0 (.val .unit))

/-- `moveExit` is a frame with one state, `Ref 1`, at the normal exit and at the exits. -/
theorem moveExit_derives :
    FDerives LifeCtx.empty [] [] [.ref .i32] [.ref .unit] [.ref .unit] moveExit [] rowX .i32 :=
  .bind (Γ₁ := []) (Γ₂ := []) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil) (.inr fun _ h => absurd h List.not_mem_nil)
    (.swap .unit (.unitI .nil))
    (.exit (k := 0) (l := 0) (B := .unit) rfl (.unitI (.drop rfl .nil)))

/-- `put c x`: the empty cell filled again (`swap c x`), at any exit state. -/
def putBack : Expr := swapSE (.var 0)

theorem putBack_derives (X : List VTy) :
    FDerives LifeCtx.empty [⟨.i32, true⟩] [] [.ref .unit] [.ref .i32] X putBack [] rowX .unit :=
  .swap .int (.var (.here .nil))

/-- `moveExit; putBack`. -/
def movePut : Expr := bindE rowX [] moveExit putBack

/-- **The two-state `bind` composes them**: normal exit `Ref i32` (put back), exits `Ref 1` (the
exit of `moveExit`, before the put back). -/
theorem movePut_derives :
    FDerives LifeCtx.empty [] [] [.ref .i32] [.ref .i32] [.ref .unit] movePut [] rowX .unit :=
  .bind (Γ₁ := []) (Γ₂ := []) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil) (.inr fun _ h => absurd h List.not_mem_nil)
    moveExit_derives (putBack_derives _)

/-- The handler of the two-state program: the exit's empty cell filled with `7`. -/
def fill7 : Expr := swapSE (Val.i32 7).1

/-- `let mut c = 7; catch movePut (_. fill7)`, at the two states: the handler is typed from the
exits' state `Ref 1`, so it must fill the cell, and the cell is released full. -/
def moveExitCaught : Expr :=
  newE (.full .i32) (.ref .unit) (Val.i32 7).1 (catchE [] movePut fill7)

theorem moveExitCaught_derives :
    FDerives LifeCtx.empty [] [] [] [] [] moveExitCaught [] [] (.tensor .unit .i32) := by
  refine .new (Γ₁ := []) (Γ₂ := []) (q := .full .i32) .nil .int .int (.ref .unit)
    (.lit (.i32 7) .nil) ?_
  refine .catch (Γ₁ := []) (Γ₂ := []) (l := 0) (B := .unit) .nil
    (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) movePut_derives ?_
  exact .swap .int (.lit (.i32 7) (.drop rfl .nil))

/-- Its accounting is the general theorem's. -/
theorem moveExitCaught_returns : Returns (ℍ := ℍ) moveExitCaught := by
  have h := accounting (ℍ := ℍ) (fun _ h => absurd h List.not_mem_nil) moveExitCaught_derives []
  simpa [substAll, Adequacy.psub_nil] using h

/-- And every run reaches a value at the empty memory. -/
theorem moveExitCaught_adequate {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (runFrameE moveExitCaught) μ₁ e₁) :
    ∃ v, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls, vP (ansTy [] [] (.tensor .unit .i32) []) ls LSub.empty v PMap.empty :=
  frame_adequacy rfl moveExitCaught_derives hs

/-- **The single-state `bind`**: from single-state frames `M : P₀ → P₁ / P₁` and
`N : P₁ → P₂ / P₂`, the composite typed at `N`'s state, `P₀ → P₂ / P₂`, under `bind`'s side
conditions. -/
def BindOne : Prop :=
  ∀ {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Φ : List FBlock} {P₀ P₁ P₂ : List VTy} {eM eN : Expr}
    {S : Row} {E : ExitRow} {A B : VTy},
    Ctx.SplitP Γ Γ₁ Γ₂ → (S.Weak → Γ₂.Drops) → (S.Unr → Persistent Γ₂) → (E = [] ∨ CtxDtor Γ₂) →
    FDerives Δ Γ₁ Φ P₀ P₁ P₁ eM S E A → FDerives Δ (⟨A, true⟩ :: Γ₂) Φ P₁ P₂ P₂ eN S E B →
    CDerives Δ Γ (bindE E Γ₂ eM eN) (.comp (frTy S P₀ P₂ P₂ E B))

/-- The handler of the single-state program: nothing, the slot left as the single state says it
is (`Ref i32`). -/
def leave : Expr := coreE [.ref .i32] (.val .unit)

/-- `let mut c = 7; catch movePut (_. leave)`. -/
def moveExitPut : Expr :=
  newE (.full .i32) (.ref .i32) (Val.i32 7).1 (catchE [] movePut leave)

/-- The answer of `moveExitPut`'s run: the released cell's content is `()`, the hole `moveExit`
left. -/
def holeOut : Val := Val.inj₁ (Val.pair Val.unit (Val.pair Val.unit Val.unit))

/-- **`moveExitPut` runs to `inl ((), ((), ()))`** at the empty memory. -/
theorem moveExitPut_runs :
    Steps (ℍ := ℍ) Adequacy.emptyMem (runFrameE moveExitPut) Adequacy.emptyMem (.val holeOut) :=
  runM_val (k := 300) (m := []) (m' := []) rfl

/-- **The single-`Π_out` form does not compose under `bind`.** -/
theorem not_bindOne : ¬ BindOne := by
  intro hb
  letI : BoCa.HostIs BoCa.wasmHost := ⟨⟩
  have hC := hb (Δ := LifeCtx.empty) (Γ₁ := []) (Γ₂ := []) (Φ := []) .nil
    (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
    (.inr fun _ h => absurd h List.not_mem_nil) moveExit_derives (putBack_derives [.ref .i32])
  have hL : FDerives LifeCtx.empty [⟨.unit, true⟩] [] [.ref .i32] [.ref .i32] [.ref .i32] leave
      [] [] .unit :=
    .core frow_nil (fun P hP => by simp only [List.mem_singleton] at hP; subst hP; exact .ref .int)
      (.ret (.unitI (.drop rfl .nil)))
  have hK := elab_catch (Γ₁ := []) (Γ₂ := []) (l := 0) (B := .unit) .nil
    (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) hC (FDerives.elab hL)
  have hP := elab_new (Γ₁ := []) (Γ₂ := []) (q := .full .i32) (Q' := .ref .i32) .nil .int
    (.ref .int) (.lit (.i32 7) .nil) hK
  obtain ⟨v, hs, ls, hv⟩ :=
    EffPrograms.adequacyD_obs (ℍ := BoCa.wasmHost) rfl (runFrameC_derives hP)
      (moveExitPut_runs (ℍ := BoCa.wasmHost))
  obtain ⟨-, rfl⟩ := steps_from_val hs
  simp [holeOut, ansTy, slotsTy, vCE, CellSt.content, BoLo.or, BoLo.ex, BoLo.sep, BoLo.pure, Val.inj₁, Val.pair,
    Val.unit, Val.IsInt, Val.i32, Val.inj₂, Subtype.mk.injEq] at hv

end BoCa.Fig16.LogRel.Core.Frames

end
