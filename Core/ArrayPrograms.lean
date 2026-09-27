import Core.IntPrograms
import Core.Dtor

/-!
# Core — a program over an array  `[spec §9]`

One closed `CDerives` derivation, run by adequacy at every host (`arrProg_runs`) and by the
interpreter at `wasmHost` (`arrProg_eval`, kernel-checked by `decide`):

    a ← array_new (3, λi. i + 10);          -- [10, 11, 12]
    (a, old) ← array_replace (a, (1, 42));  -- old = inl 11; a = [10, 42, 12]
    (a, n) ← array_size a;                  -- n = 3
    array_free (λx. (), a);                 -- the three cells freed
    (old, n)

Observed: `(inl 11, 3)` and no cell left, so `tab` placed three cells filled from the tabulator,
`idx` found cell `1`, and `drop` freed every cell.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `λi. i + 10`. -/
def tab10V : Val := .lam (hop (.bin .w32 .add) (.pair (.var 0) (i32E 10)))

theorem d_tab10 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val tab10V) (.val (.bang (.lolli .i32 .i32))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret (.lolliE (.left (deadSplit hΓ))
    (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (d_i32 10 (Ctx.Dead.cons hΓ).toP))
    (.bangE (.hostOp _ (Ctx.Dead.cons hΓ).toP)))))

/-- `λx. ()`, the consumer of an `I32`. -/
def dropI32V : Val := .lam (.val .unit)

theorem d_dropI32 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val dropI32V) (.val (.bang (.lolli .i32 .unit))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret (.unitI (.drop rfl hΓ.toP))))

/-- The program. -/
def arrProg : Expr :=
  bindE (.app (.val (.prim .tab)) (.pair (i32E 3) (.val tab10V)))
    (.letpair (.app (.val replaceV) (.pair (.var 0) (.pair (i32E 1) (i32E 42))))
      (.letpair (.app (.val sizeV) (.var 1))
        (.seq (.app (.val (.prim .drop)) (.pair (.val dropI32V) (.var 1)))
          (.pair (.var 2) (.var 0)))))

theorem arrProg_derives :
    CDerives LifeCtx.empty [] arrProg (.comp (.ret (.tensor (.sum .i32 .i32) .i32))) := by
  refine .ret (bindP (A := .array .i32) ?_ ?_)
  · exact appP (pairP (d_i32 3 (by cdeadP)) (d_tab10 (by cdead))) (.bangE (.arrNew .i32 (by cdeadP)))
  · refine letP (A := .array .i32) (B := .sum .i32 .i32) ?_ ?_
    · exact appP (pairP (.var (by csoloP)) (pairP (d_i32 1 (by cdeadP)) (d_i32 42 (by cdeadP))))
        (.bangE (.arrReplace .i32 (by cdeadP)))
    · refine letP (A := .array .i32) (B := .i32) ?_ ?_
      · exact appP (.var (by csoloP)) (.bangE (.arrSize .i32 (by cdeadP)))
      · refine .seqV (partP_split (.app (.val (.prim .drop)) (.pair (.val dropI32V) (.var 1))) 0 _)
          ?_ ?_
        · refine appP (.tensorI (split_kill _).toP (d_dropI32 (kill_dead _)) (.var (by csoloP)))
            (.bangE (.arrFree .i32 (by cdeadP)))
        · exact pairP (.var (by csoloP)) (.var (by csoloP))

/-- **The program runs at every host**: from the empty memory to a value of
`(I32 ⊕ I32) ⊗ I32`, and the empty memory. -/
theorem arrProg_runs : ∃ v : Val,
    BoCa.BoLo.Steps Adequacy.emptyMem arrProg Adequacy.emptyMem (.val v) := by
  have hwp : wpTS [] arrProg (fun _ _ => Fig16.BoLo.pure True) (PMap.empty : WRes) :=
    wpTS_mono (fun _ v ρ hv => ⟨vP_empty_of_persistent rfl hv, trivial⟩) PMap.empty
      (wp_of_derives arrProg_derives)
  obtain ⟨v, hsteps, -⟩ := theorem32 arrProg _ hwp
  exact ⟨v, hsteps⟩

/-- `(inl n, m)` as two integers, when the run ends with no cell left. -/
def arrOf : Outcome → Option (UInt32 × UInt32)
  | .value ⟨.pair (.inj₁ a) b, _⟩ false => do pure (← i32Of a, ← i32Of b)
  | _ => none

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: the old element `11` and the length `3`, no cell left. -/
theorem arrProg_eval : arrOf (eval arrProg) = some (11, 3) := by decide

end BoCa.Fig16.LogRel.Core

end
