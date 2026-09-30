import HandlersAsBorrows.Sharing

/-!
# A program of the fragment, translated, proved safe, and run

One handler with state `B = 1 ⊕ 1` and an operation `flip : 1 → B` that answers the current
state and stores its negation.  Two blocks are defined in its scope, and each performs `flip`;
the program calls both:

    handle_B {F ⇒
      def f = {u ⇒ F(u)};
      def g = {u ⇒ F(u)};
      val a = f(());
      val b = g(());
      …a, b…
    } with state inj₁ (), clause (s, u) ⇒ case s {x ⇒ (inj₂ x, inj₁ u) | y ⇒ (inj₁ u, inj₂ y)}

The two blocks use one stateful capability.  Neither captures it: each receives the environment
at its call, so the second call sees the state the first one left (`sharedPair_eval`: the
answers are `inj₁ ()` then `inj₂ ()`).

`[about ours]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace HandlersAsBorrows.Xi
open BoCa BoCa.Lifetime BoCa.Programs

/-- `1 ⊕ 1`. -/
abbrev VB : VTy := .sum .unit .unit

/-- The clause of `flip`: `(s, u) ⇒ case s {x ⇒ (inj₂ x, inj₁ u) | y ⇒ (inj₁ u, inj₂ y)}`. -/
def flipClause : Stmt :=
  .split (.var 0) (.case (.var 1) (.ret (.pair (.inj₂ (.var 0)) (.inj₁ (.var 2))))
    (.ret (.pair (.inj₁ (.var 2)) (.inj₂ (.var 0)))))

theorem x_flipClause : XDerives [] [⟨.pair VB .unit, true⟩] flipClause (.pair VB VB) :=
  .split (A₁ := VB) (A₂ := .unit) (.left .nil) (.var (.here .nil))
    (.case (A₁ := .unit) (A₂ := .unit) (.right (.left (.dead (.dead .nil))))
      (.var (.there (.here (.cons (.cons .nil)))))
      (.ret (.pair (.left (.dead (.right (.dead (.dead (.dead .nil))))))
        (.inj₂ (.var (.here (.cons (.cons (.cons (.cons (.cons .nil))))))))
        (.inj₁ (.var (.there (.there (.here (.cons (.cons (.cons .nil))))))))))
      (.ret (.pair (.right (.dead (.left (.dead (.dead (.dead .nil))))))
        (.inj₁ (.var (.there (.there (.here (.cons (.cons (.cons .nil))))))))
        (.inj₂ (.var (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))))))

/-- The handled statement, around a final statement `fin` that sees `b` at `0` and `a` at `2`. -/
def sharedBody (fin : Stmt) : Stmt :=
  .defn (.op 0 (.var 0)) (.defn (.op 1 (.var 0)) (.val (.call 1 .unit) (.val (.call 0 .unit) fin)))

/-- The environment inside the two block definitions. -/
abbrev K₂ : List Entry := [.blk .unit VB, .blk .unit VB, .cap VB .unit VB]

theorem deadSplit {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Ctx.Split Γ Γ Γ := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .dead ih

/-- The six consumed slots below `a`. -/
theorem dead6 : Ctx.Dead ([pad, pad, pad, pad, pad, pad] : Ctx VTy) :=
  .cons (.cons (.cons (.cons (.cons (.cons .nil)))))

theorem x_sharedBody {fin : Stmt} {C : VTy}
    (hfin : XDerives K₂ (⟨VB, true⟩ :: pad :: ⟨VB, true⟩ :: [pad, pad, pad, pad, pad, pad]) fin C) :
    XDerives [.cap VB .unit VB] [pad, pad, pad] (sharedBody fin) C :=
  .defn (.op rfl (.var (.here (.cons .nil))))
    (.defn (.op rfl (.var (.here (.cons .nil))))
      (.val (A := VB) (deadSplit (.cons (.cons (.cons (.cons (.cons .nil))))))
        (.call rfl (.unit (.cons (.cons (.cons (.cons (.cons .nil)))))))
        (.val (A := VB) (.right (deadSplit dead6))
          (.call rfl (.unit (.cons dead6)))
          hfin)))

/-- The program, around `fin`. -/
def shared (fin : Stmt) : Stmt := .handle VB (.inj₁ .unit) flipClause (sharedBody fin)

theorem x_shared {fin : Stmt} {C : VTy}
    (hfin : XDerives K₂ (⟨VB, true⟩ :: pad :: ⟨VB, true⟩ :: [pad, pad, pad, pad, pad, pad]) fin C) :
    XDerives [] [] (shared fin) C :=
  .handle .nil (.inj₁ (.unit .nil)) x_flipClause (x_sharedBody hfin)

/-- Return both answers. -/
def sharedPair : Stmt := shared (.ret (.pair (.var 2) (.var 0)))

theorem x_sharedPair : XDerives [] [] sharedPair (.pair VB VB) :=
  x_shared (.ret (.pair (.right (.dead (.left (deadSplit dead6)))) (.var (.there (.there (.here dead6))))
    (.var (.here (.cons (.cons dead6))))))

/-- Consume both answers and return `()`. -/
def sharedUnit : Stmt :=
  shared (.case (.var 2) (.drop (.var 0) (.case (.var 2) (.ret (.var 0)) (.ret (.var 0))))
    (.drop (.var 0) (.case (.var 2) (.ret (.var 0)) (.ret (.var 0)))))

theorem x_sharedUnit : XDerives [] [] sharedUnit .unit := by
  have br : XDerives K₂ (⟨.unit, true⟩ :: pad :: ⟨VB, true⟩ :: pad :: ⟨VB, false⟩ ::
      [pad, pad, pad, pad, pad, pad])
      (.drop (.var 0) (.case (.var 2) (.ret (.var 0)) (.ret (.var 0)))) .unit :=
    .drop (.left (.dead (.right (.dead (.dead (deadSplit dead6))))))
      (.var (.here (.cons (.cons (.cons (.cons dead6))))))
      (.case (A₁ := .unit) (A₂ := .unit) (.dead (.dead (.left (.dead (.dead (deadSplit dead6))))))
        (.var (.there (.there (.here (.cons (.cons dead6))))))
        (.ret (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons dead6)))))))))
        (.ret (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons dead6))))))))))
  exact x_shared (.case (A₁ := .unit) (A₂ := .unit) (.right (.dead (.left (deadSplit dead6))))
    (.var (.there (.there (.here dead6)))) br br)

/-- **Effect safety, instance**: the translation runs to `()` and frees the handler's state. -/
theorem sharedUnit_safe :
    BoLo.Steps Adequacy.emptyMem (prog sharedUnit) Adequacy.emptyMem (.val .unit) :=
  effect_safety x_sharedUnit

theorem sharedUnit_eval : unitNoLeak (eval (prog sharedUnit)) = true := by decide

/-- The interpreter's answers: `f` sees `inj₁ ()`, then `g` sees the flipped `inj₂ ()`, and no
cell is left. -/
theorem sharedPair_eval :
    (match eval (prog sharedPair) with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

end HandlersAsBorrows.Xi
