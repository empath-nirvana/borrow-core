import Frames.Theorems

/-!
# Frames — examples: the accounting is not vacuous, and a nesting of depth 4

- `swapE` is a Core term at a frame type over two slots of one type that hands them back
  swapped. It is a `CDerives` derivation at the frame type (`swap_derives`), and it fails the
  accounting (`not_returns_swap`): typing at `Fr Σ Π E A` alone does not give the accounting,
  and the frame rules, which never hand `π` to Core code, do.
- `nested` is a frame derivation of depth 4 (`new` ⊃ `catch` ⊃ `loopCount` ⊃ `case` ⊃ `exit`)
  whose innermost exit leaves two catchers out: the `break` of the loop, and an exit past the
  loop to the `catch` around it. Its accounting is `accounting` at it, with no case of its own
  (`nested_returns`).
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

/-- `λπ. let (a, ρ) = π; let (b, u) = ρ; ((b, (a, u)), inl ())`. -/
def swapE : Expr :=
  .lam (.letpair (.var 0) (.letpair (.var 0)
    (.pair (.pair (.var 1) (.pair (.var 3) (.var 0))) (.inj₁ (.val .unit)))))

/-- The swap is typed at the frame type over two cells. -/
theorem swap_derives : CDerives LifeCtx.empty [] swapE (.comp (frTy [] twoCells [] .unit)) := by
  show CDerives LifeCtx.empty [] (.val (.lam _)) (.comp (.arr _ (.ret _)))
  refine .lam (.tensorE (.left .nil) (.var (.here .nil)) ?_)
  refine .tensorE (.left (.right (.dead .nil))) (.var (.here (.cons (.cons .nil)))) ?_
  refine .ret (.tensorI (.left (.left (.dead (.left (.dead .nil))))) ?_
    (.sumI₁ (.unitI (.cons (.cons (.cons (.cons (.cons .nil))))))))
  refine .tensorI (.right (.left (.dead (.right (.dead .nil)))))
    (.var (.there (.here (.cons (.cons (.cons .nil)))))) ?_
  exact .tensorI (.right (.dead (.dead (.left (.dead .nil)))))
    (.var (.there (.there (.there (.here (.cons .nil))))))
    (.var (.here (.cons (.cons (.cons (.cons .nil))))))

/-- Two distinct cells as slots. -/
def twoLocs : Val := Val.pair (Val.loc 0) (Val.pair (Val.loc 1) Val.unit)

/-- The swapped answer. -/
def swapped : Val :=
  Val.pair (Val.pair (Val.loc 1) (Val.pair (Val.loc 0) Val.unit)) (Val.inj₁ Val.unit)

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
  obtain ⟨x, hx⟩ := hval _ _ _ (swap_runs (ℍ := ℍ) (fun _ => none))
  have := congrArg Subtype.val hx
  simp [swapped, twoLocs, Val.pair, Val.loc] at this

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
    FDerives LifeCtx.empty [⟨bit, true⟩, ⟨.int .w32, true⟩] [] Ps nestedTurn []
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
  loopCountE (Val.i32 3).1 (.inj₁ (.val .unit)) nestedTurn

theorem nestedLoop_derives (Ps : List VTy) :
    FDerives LifeCtx.empty [] [] Ps nestedLoop [] [(1, .unit)] (.sum bit .unit) :=
  .loopCount (Γ₁ := []) (Γn := []) (Γs := []) (Γ₂ := []) .nil .nil
    (fun _ h => absurd h List.not_mem_nil) (.lit (.i32 3) .nil)
    (.sumI₁ (.unitI .nil)) (nestedTurn_derives Ps)

/-- After the loop, `'out`'s handler, and the frame: `new () (catch nestedLoop (core (return ())))`,
the loop's answer dropped by the `catch`'s normal arm. -/
def nested : Expr :=
  newE .unit (.val .unit)
    (catchE (bindE nestedLoop (coreE [.ref .unit] (.val .unit))) (coreE [.ref .unit] (.val .unit)))

theorem frow_nil : FRow [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩

theorem slotsOk_cell : SlotsOk [.ref .unit] := by
  intro P hP
  simp only [List.mem_singleton] at hP
  subst hP
  exact .ref .unit

/-- **The depth-4 nesting is a frame**: `new ⊃ catch ⊃ bind ⊃ loopCount ⊃ case ⊃ exit`. -/
theorem nested_derives :
    FDerives LifeCtx.empty [] [] [] nested [] [] (.tensor .unit .unit) := by
  refine .new (Γ₁ := []) (Γ₂ := []) .nil .unit (.unitI .nil) ?_
  refine .catch (Γ₁ := []) (Γ₂ := []) (l := 1) (B := .unit) .nil
    (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
    ?_ ?_
  · refine .bind (Γ₁ := []) (Γ₂ := []) .nil
      (fun _ => fun _ h => absurd h List.not_mem_nil) (fun _ => fun _ h => absurd h List.not_mem_nil)
      (nestedLoop_derives _) ?_
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
      ∃ ls, vP (.tensor .unit (exitsTy (.tensor .unit .unit) [])) ls LSub.empty v PMap.empty :=
  frame_adequacy rfl (fun _ h => absurd h List.not_mem_nil) nested_derives hs

end BoCa.Fig16.LogRel.Core.Frames

end
