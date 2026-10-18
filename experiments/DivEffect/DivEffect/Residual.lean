import DivEffect.Safety

/-!
# DivEffect — the residual  (§4.1, unknown 2)

A loop that holds a resource with no destructor, closed by `div_fuel 3`, hands it back.

    prog  =  c ← alloc 0;
             r ← div_fuel 3 (tick () to n. case n { next → iterate (f, c) | close → inr c });
             case r { inl b → b | inr c' → free c' }

    f c   =  ⟨ x ← load c; store c (x + 1); return (inr c),   return c ⟩

The cell `c` is the loop's state and its residual (`R = ref ℕ`): the step's close hands it back,
and nothing drops it.  The loop never finishes (`B = 0`), so `div_fuel 3` closes it: the tick
continuation is resumed with *close*, a resume of the linear `κ`, not a cancel.  The program
frees the cell it is handed and answers its content: the number of turns that ran.  The tick in
front of the loop is §3.2's placement at the empty row (a forward move to the loop's head), so
three answers *next* run three turns, as `div_fuel 3` observes three times today.

* `prog_every_run`: every run, under every allocator, continues to a value, a count, at the
  empty memory: the cell came back and was freed.  By `fuel_total`, `cwp_iterate` and `cwp_bind`,
  the state's relation the cell at any count (`cellP`), the step proved at it directly.
* `Run.lean` runs `prog` at the source, closure and flat stages and as WebAssembly, each
  printing `inr (inr (inr (inl ())))` (three) and `live 0`.

Not here: a tied derivation (`CDerivesAt`) of `prog`.  `iterate` and `div_fuel` are constants
with their own rules in the design, and `CDerives` has no rule for them; the derivation is B1's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The program -/

/-- The step: `λc. λsel. case sel { next → x ← load c; store c (inr x); inr c | close → c }`. -/
def cellStep : Val :=
  .lam (.val (.lam (.case (.var 0)
    (.app (.val (.lam (.seq (.app (.app (.val (.prim .store)) (.var 3)) (.inj₂ (.var 0)))
      (.inj₂ (.var 3)))))
      (.app (.val (.prim .load)) (.var 2)))
    (.var 2))))

/-- The loop's body, the cell `c` at `0`: `tick () to n. case n { next → iterate (f, c) |
close → inr c }`. -/
def loopB (d : UInt32) : Val :=
  .lam (.app (.val (.lam (.case (.var 0)
      (.app (.val (iterV d)) (.pair (.val cellStep) (.var 2)))
      (.inj₂ (.var 2)))))
    (tickE d))

/-- The end: `λr. case r { inl b → b | inr c' → free c' }`. -/
def finV : Val := .lam (.case (.var 0) (.var 0) (.app (.val (.prim .free)) (.var 0)))

/-- `λc. fin (div_fuel n (loop c))`. -/
def progB (d : UInt32) (n : ℕ) : Val :=
  .lam (.app (.val finV) ((fuelK (natV n)).plug (hndE (fuelH d) (.app (.val (loopB d)) (.var 0)))))

/-- **The program.** -/
def prog (d : UInt32) (n : ℕ) : Expr :=
  .app (.val (progB d n)) (.app (.val (.prim .alloc)) (.val (natV 0)))

/-! ### The steps -/

theorem cellStep_next (ℓ : Loc) :
    PureSteps (obsN cellStep (.loc ℓ))
      (.app (.val (.lam (.seq (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.inj₂ (.var 0)))
        (.inj₂ (.val (.loc ℓ)))))) (.app (.val (.prim .load)) (.val (.loc ℓ)))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  simp only [cellStep, Kont.plug]
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  simp
  exact .refl

theorem cellStep_close (ℓ : Loc) : PureSteps (obsC cellStep (.loc ℓ)) (.val (.loc ℓ)) := by
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  simp only [cellStep, Kont.plug]
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  simp
  exact .refl

theorem loopB_steps (d : UInt32) (ℓ : Loc) :
    PureSteps (.app (.val (loopB d)) (.val (.loc ℓ)))
      ((Kont.appR (.val (.lam (.case (.var 0)
        (.app (.val (iterV d)) (.pair (.val cellStep) (.val (.loc ℓ))))
        (.inj₂ (.val (.loc ℓ)))))) .hole).plug (tickE d)) := by
  refine (PureSteps.beta _ _).trans ?_
  have hc : closedAt 0 (iterV d).1 = true := selfV_closed (iterB_closed d)
  have hs : closedAt 0 cellStep.1 = true := rfl
  have ht : closedAt 0 (tickE d) = true := rfl
  try simp only [loopB]
  generalize iterV d = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc, closed_subst hs, closed_shift hs,
    subst_closedAt _ _ ht, Kont.plug]
  exact .refl

theorem loopK_next (d : UInt32) (ℓ : Loc) :
    PureSteps ((Kont.appR (.val (.lam (.case (.var 0)
        (.app (.val (iterV d)) (.pair (.val cellStep) (.val (.loc ℓ))))
        (.inj₂ (.val (.loc ℓ)))))) .hole).plug (.val nextV)) (iterE d cellStep (.loc ℓ)) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl).trans ?_
  have hc : closedAt 0 (iterV d).1 = true := selfV_closed (iterB_closed d)
  have hs : closedAt 0 cellStep.1 = true := rfl
  simp only [iterE]
  generalize iterV d = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc, closed_subst hs, closed_shift hs]
  exact .refl

theorem loopK_close (d : UInt32) (ℓ : Loc) :
    PureSteps ((Kont.appR (.val (.lam (.case (.var 0)
        (.app (.val (iterV d)) (.pair (.val cellStep) (.val (.loc ℓ))))
        (.inj₂ (.val (.loc ℓ)))))) .hole).plug (.val closeV)) (.val (Val.inj₂ (.loc ℓ))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ .unit _ _) rfl).trans ?_
  have hc : closedAt 0 (iterV d).1 = true := selfV_closed (iterB_closed d)
  generalize iterV d = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc]
  exact .refl

theorem prog_steps (d : UInt32) (n : ℕ) (ℓ : Loc) :
    PureSteps (.app (.val (progB d n)) (.val (.loc ℓ)))
      (.app (.val finV) (fuelE d n (.app (.val (loopB d)) (.val (.loc ℓ))))) := by
  refine (PureSteps.beta _ _).trans ?_
  have hn := natV_closed n
  have hb : closedAt 0 (loopB d).1 = true := by
    have h1 : closedAt 3 (iterV d).1 = true := closedAt_mono _ (selfV_closed (iterB_closed d)) (by omega)
    simp [loopB, closedAt, h1, tickE, BoCa.BoLo.performE, BoCa.BoLo.opPayload, Val.pair,
      Val.i32, cellStep]
  have hf : closedAt 0 (fuelH d).1 = true := rfl
  have hfin : closedAt 0 finV.1 = true := rfl
  have hk : closedAt 0 apK.1 = true := rfl
  simp [fuelE, fuelK, Kont.plug, closed_subst hn, closed_subst hb, closed_subst hf,
    closed_subst hfin, closed_subst hk, hndE]
  exact .refl

/-! ### The relation -/

/-- The loop's state: the cell, at any count. -/
def cellP : List SRec → Val → WProp := fun _ s ρ => ∃ ℓ k, s = .loc ℓ ∧ ptoOwn ℓ (natV k) ρ

/-- The empty row. -/
abbrev T0 : OpTab := Row.tab ([] : Row) LSub.empty

theorem T0_none (n i : UInt32) : T0 n i = none := by simp only [T0, rowTab_nil]; rfl

/-- The step at the cell: a turn adds one to the count and answers the next state; the close
hands the cell back. -/
theorem cellStep_ok (d : UInt32) {ls : List SRec} {s : Val} {ρ : WRes} (hs : cellP ls s ρ) :
    cwp LSub.empty d T0 (stepPost (fun _ _ _ => False) cellP) ls (obsN cellStep s) ρ ∧
      cwp LSub.empty d T0 cellP ls (obsC cellStep s) ρ := by
  obtain ⟨ℓ, k, rfl, hp⟩ := hs
  refine ⟨cwp_of_ewp (ewp_of_wp (opTable_mono _) ?_), cwp_of_ewp (ewp_of_wp (opTable_mono _) ?_)⟩
  · refine wpTS_pureSteps (cellStep_next ℓ) ls _ ρ ?_
    refine wpTS_bind (.appR (.val (.lam _)) .hole) _ ls _ ρ ?_
    refine wpTS_load ls ℓ (natV k) _ ρ ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, hp, ?_⟩
    intro σ₁ σ₂ hσ₁ hc
    rw [eq_of_compS_empty_left hc]
    refine wpTS_lolli ls _ (natV k) _ σ₁ ?_
    simp only [Expr.subst, Val.val_shift]
    refine wpTS_bind (.seq .hole _) _ ls _ σ₁ ?_
    refine wpTS_store ls ℓ (natV k) (natV (k + 1)) _ σ₁
      ⟨σ₁, PMap.empty, ResU.comp_empty_right σ₁, hσ₁, ?_⟩
    intro τ₁ τ₂ hτ₁ hc'
    rw [eq_of_compS_empty_left hc']
    refine wpTS_head (fun μ => Head.seq μ _) rfl ls _ τ₁ ?_
    exact wpTS_val ls (Val.inj₂ (.loc ℓ)) _ τ₁ (Or.inr ⟨.loc ℓ, rfl, ℓ, k + 1, rfl, hτ₁⟩)
  · exact wpTS_pureSteps (cellStep_close ℓ) ls _ ρ (wpTS_val ls _ _ ρ ⟨ℓ, k, rfl, hp⟩)

theorem cellP_ext : ∀ ls ls' s ρ, Ext ls ls' ρ → cellP ls s ρ → cellP ls' s ρ :=
  fun _ _ _ _ _ h => h

/-- **The loop body is in `cwp`**: the tick in front, then `iterate`, its residual the cell. -/
theorem loop_cwp (d : UInt32) (ls : List SRec) (ℓ : Loc) (k : ℕ) :
    cwp LSub.empty d T0 (stepPost (fun _ _ _ => False) cellP) ls (.app (.val (loopB d)) (.val (.loc ℓ)))
      (ResU.single ℓ (CellU.ownOf (natV k))) := by
  have hPC : T0.PlainCancel := Row.tab_plainCancel _ _
  have hTd : T0 d 0 = none := T0_none d 0
  refine cwp_pureSteps (loopB_steps d ℓ) ?_
  refine cwp_bind hTd _ (fun n => by simp [Kont.HasHnd]) (fun n => by simp [Kont.Catches])
    (fun _ => ptoOwn ℓ (natV k)) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun n i en h => by rw [T0_none] at h; cases h) (fun n i en h => by rw [T0_none] at h; cases h)
    (fun n i en h => by rw [T0_none] at h; cases h) (fun ls w ρ => vC true nextTy ls LSub.empty w ρ) _
    ?_ (cwp_tick hTd (fun _ _ _ h => h) ls) (ρ₂ := ResU.single ℓ (CellU.ownOf (natV k))) rfl
    (compS_empty_left _)
  rintro ls' w σ ⟨σ₁, σ₂, hc, hw₀, hF⟩
  obtain ⟨hw, h0⟩ := vC_next hw₀
  subst h0
  have hF' : σ₂ = ResU.single ℓ (CellU.ownOf (natV k)) := hF
  subst hF'
  rw [eq_of_compS_empty_left hc]
  rcases hw with h | h <;> subst h
  · exact cwp_pureSteps (loopK_next d ℓ) (cwp_iterate hTd hPC cellStep _ _ cellP
      (fun ls s ρ hs => cellStep_ok d hs) cellP_ext ⟨ℓ, k, rfl, rfl⟩)
  · exact cwp_pureSteps (loopK_close d ℓ) (cwp_of_ewp (ewp_val (opTable_mono _)
      (Or.inr ⟨.loc ℓ, rfl, ℓ, k, rfl, rfl⟩)))

/-- **Every run of the program** (§4.1 unknown 2), under every allocator, from the empty memory,
continues to a count at the empty memory: `div_fuel n` closed the loop, the close handed the
cell back, and the program freed it. -/
theorem prog_every_run (d : UInt32) (n : ℕ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (prog d n) μ₁ e₁) :
    ∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v) ∧ ∃ k, v = natV k := by
  have hPC : T0.PlainCancel := Row.tab_plainCancel _ _
  refine theorem32D _ _ ?_ hs
  refine wpTS_bind (.appR (.val (progB d n)) .hole) _ [] _ PMap.empty ?_
  refine wpTS_alloc [] (natV 0) _ PMap.empty (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [eq_of_compS_empty_left hc]
  refine wpTS_pureSteps (prog_steps d n ℓ) [] _ σ₁ ?_
  refine wpTS_bind (.appR (.val finV) .hole) _ [] _ σ₁ ?_
  have he := fuel_total (fun i => T0_none d i) hPC n (hp ▸ loop_cwp d [] ℓ 0)
  have hwp := ewp_bot.mp (ewp_mono (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ h => (opTable_empty (by simp only [T0, rowTab_nil] at h; exact h)).elim)
    (fun _ _ _ h => h) he)
  refine wpTS_mono (fun ls v ρ hv => ?_) σ₁ hwp
  rcases hv with ⟨b, -, hb⟩ | ⟨c, rfl, ℓ', k, rfl, hc'⟩
  · exact hb.elim
  · refine wpTS_lolli ls _ _ _ ρ ?_
    refine wpTS_head (fun μ => Head.case₂ μ _ _ _) rfl ls _ ρ ?_
    refine wpTS_free ls ℓ' (natV k) _ ρ ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, hc', ?_⟩
    exact ⟨rfl, k, rfl⟩

end BoCa.Fig16.LogRel.Core.DivEffect

end
