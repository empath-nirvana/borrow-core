import Core.StreamPrograms
import Core.Chain.Adequacy791N

/-!
# #855 K4: a loop state at one code type across three steps  `[spec §68]`

The unit stream over a cell (`Core/StreamPrograms.lean`'s `takeCloseR`), built by `unfoldK` and
observed by `nuOutK`, so that the loop state keeps the code type
`T = Code⟨etaCode C; !G ⊗ (Ref 1 ⊗ 1)⟩ (Stream 1)` across every step:

    s ← alloc ();                    -- s : Ref 1
    h ← unfold stepR;                -- h : Code⟨hCode C; !G ⊗ 1⟩ (Ref 1 ⊸ F T)    (unfoldK)
    x ← h s;                         -- x : T
    p ← x π₁; let (u, x) = p in u;   -- x π₁ : F(1 ⊗ T)                            (nuOutK)
    p ← x π₁; let (u, x) = p in u;
    p ← x π₁; let (u, x) = p in u;
    x π₂                             -- x π₂ : F 1, `close` frees the cell         (nuOutK)

`C = streamBody 1`, `G = U(Ref 1 ⊸ F(1 ⊗ Ref 1) & F 1)`. The state `x` is read at `T` before
each of the three observations and at the close; no step erases it to `U(Stream 1)`.

* `d_progK`: the program is typed at `F 1` in the empty context.
* `progK_runs` (`adequacyC`): it runs from the empty memory to `()` and the empty memory.
* `progK_orDiverges` (`goal791N`): at the chain's relation, it is safe, leak-free, or diverges,
  from `HandlerLawN`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.CodeLoop855N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791)
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N (goal791N HandlerLawN)

/-! ### The types -/

/-- The stream's body, `F(1 ⊗ X) & F 1`. -/
abbrev Cs : CTy := CTy.streamBody .unit

/-- The state, a cell. -/
abbrev Ss : VTy := .ref .unit

/-- The step's type, `U(Ref 1 ⊸ F(1 ⊗ Ref 1) & F 1)`. -/
abbrev Gs : VTy := .thunk (stepSC .unit Ss)

/-- **The loop state's type**, `Code⟨etaCode C; !G ⊗ (Ref 1 ⊗ 1)⟩ (Stream 1)`. -/
abbrev Ts : VTy := codeTy Cs Gs Ss

/-- `unfold stepR`'s type, `Code⟨hCode C; !G ⊗ 1⟩ (Ref 1 ⊸ F T)`. -/
abbrev Hs : VTy := .code (hCode Cs) (hEnv Gs) (.arr Ss (.ret Ts))

theorem hGs : Gs.forceTy = some (.arr Ss (Cs.instT Ss)) := by
  simp only [VTy.forceTy, CTy.streamBody_instT]

/-! ### The derivations -/

/-- **`nuOutK` at the stream**: the state read at `F(1 ⊗ T) & F 1`.  `[spec §68]` -/
theorem d_obs {Γ : Ctx VTy} {i : Nat} (h : Ctx.SoloP Γ i Ts) :
    CDerives LifeCtx.empty Γ (.var i) (.comp (.amp (.ret (.tensor .unit Ts)) (.ret .unit))) := by
  have d := CDerives.nuOutK (Δ := LifeCtx.empty) (CTy.streamBody_nuOk .unit) hGs
    (CTy.BindsFresh.of_hasAll rfl Ss) (CTy.BindsFresh.of_hasAll rfl Gs) h
  rwa [CTy.streamBody_instT] at d

/-- `x : T` (index 0) observed `n` times, then closed; the rest of each observation is bound at
`T` again.  `[spec §68]` -/
theorem d_takeK : ∀ (n : ℕ) {Γ : Ctx VTy}, Ctx.Dead Γ →
    CDerives LifeCtx.empty (⟨Ts, true⟩ :: Γ) (takeE n) (.comp (.ret .unit))
  | 0, _, hΓ => .proj₂ (d_obs (.here hΓ))
  | n + 1, _, hΓ =>
      .bind (.left (deadSplit hΓ)) (.proj₁ (d_obs (.here hΓ)))
        (.tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
          (.unitE (.right (.left (.dead (.dead (deadSplit hΓ))))) (.var (.there (.here (.cons (.cons hΓ)))))
            (d_takeK n (.cons (.cons (.cons hΓ))))))

/-- **`unfoldK` at the stream**: `unfold : !G ⊸ !Hs`.  `[spec §68]` -/
theorem d_unfoldK {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerives LifeCtx.empty Γ (.val (unfoldV Cs)) (.val (.lolli (.bang Gs) (.bang Hs))) :=
  .unfoldK Cs Gs Ss (CTy.streamBody_nuOk .unit) hGs (CTy.BindsFresh.of_hasAll rfl Ss) hΓ

/-- The program: allocate the cell, `unfold stepR`, apply it to the cell, observe `n` times,
close. -/
def progK (n : ℕ) : Expr :=
  bindE (.app (.val (.prim .alloc)) (.val .unit))
    (bindE (.app (.val (unfoldV Cs)) (.val stepR))
      (bindE (.app (.var 0) (.var 1)) (takeE n)))

/-- **The program is typed at `F 1`**, the state at `T` across every observation.
`[spec §68]` -/
theorem d_progK (n : ℕ) : CDerives LifeCtx.empty [] (progK n) (.comp (.ret .unit)) :=
  .bind .nil (.ret (.lolliE .nil (.unitI .nil) (.alloc .nil)))
    (.bind (.right .nil)
      (.ret (.bangE (.lolliE (deadSplit (.cons .nil)) (d_stepR (.cons .nil)) (d_unfoldK (.cons .nil)))))
      (.bind (.left (.left .nil))
        (.app (.left (.right .nil)) (.force (T := Hs) (.here (.cons .nil)) rfl)
          (.there (.here .nil)))
        (d_takeK n (.cons (.cons .nil)))))

/-! ### The conclusions -/

/-- **`progK 3` runs** from the empty memory to `()` and the empty memory (`adequacyC`).
`[spec §68]` -/
theorem progK_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem (progK 3) Adequacy.emptyMem (.val .unit) :=
  adequacyC (d_progK 3)

/-- **`Goal791N`'s premises at `progK 3`**, at no constant.  `[spec §68]` -/
theorem goal791N_premises_progK :
    (∀ c ∈ ([] : List Const791), c.OK) ∧
      CDerives LifeCtx.empty (ctx791 []) (progK 3) (.comp (.ret .unit)) :=
  ⟨fun _ h => absurd h List.not_mem_nil, d_progK 3⟩

/-- **`Goal791N` at `progK 3`**: the loop over a code-typed state, three observations and the
close, is safe, leak-free, or diverges, from `HandlerLawN`.  `[spec §68]` -/
theorem progK_orDiverges (h : HandlerLawN (ℍ := ℍ)) :
    OrDiverges (ℍ := ℍ) (substAll (vals791 []) (progK 3)) :=
  goal791N h [] goal791N_premises_progK.1 (progK 3) goal791N_premises_progK.2

end BoCa.Fig16.LogRel.Core.Chain.SI.CodeLoop855N

end
