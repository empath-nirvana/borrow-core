import Core.Chain.Borrow834N

/-!
# The Mut Anti-Frame at an unwinding row  `[spec §19, §62]`

Core's `withbor3U_compatX` and `withloadU_compatX` (`Core/EffBorrow.lean`), step by step, at the
per-lend world, any `Δ` and a `Row.Unwind x` row. Every entry of such a row's table is abortive
(`tabUN_abort`), so the callback's stops are raises and nothing is resumed under the
borrow. This file holds the anti-frame and an unwinding row with an unrestricted operation; the
rules at `SemJN` are in `UnwindKW835N`.

* `erwp_M_antiFrameU`: the Mut Anti-Frame at an unwinding row (Core's `ewpTS_M_antiFrameU`),
  `erwp_M_antiFrameCR` at the row's own table as its twin. The twin guards no stop; only the
  raises' claim (`hRin`/`hRout`) remains, and the cancel obligations are vacuous.
* `withbor3U_sem`, `withbor3U_compatN`: `withbor3S_compat`'s steps with the bound `Δ.meetOfDom`,
  the callback's table the lender's (`tabUN_eq_add`), the anti-frame `erwp_M_antiFrameU`,
  the claim consistent (`erwp_claimX_abort`), the finaliser frame at a raise (`erwp_ubindRaise`,
  `fin_claimMN`).
* `withloadU_sem`, `withloadU_compatN`: `withloadS_compat`'s steps, 6.150 across the row's raises
  (`withload_rebT`, `erwp_rebGen`). An unwinding row may hold an unrestricted operation; it is
  abortive, so it never resumes and the reborrow is never re-entered through it
  (`OpTabN.RebOKR.entry` reads only resumable entries). The row's table admits the reborrow at
  every `β` (`tabUN_rebOKR`) and has no cancel obligation (`tabUN_rebClosed`) (`unrRaiseRow`,
  `unrRaiseRow_unwind`: such a row).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-- A table is its own twin. -/
theorem OpTabN.Twin.refl (T : OpTabN) : T.Twin T :=
  fun _ _ en h => ⟨en, h, rfl, rfl, rfl, rfl, rfl⟩

/-- **The Mut Anti-Frame at a table whose every entry is abortive** (Core's
`ewpTS_M_antiFrameU`): `erwp_M_antiFrameCR` with the table its own twin. No stop is resumable, so
the guard reads no stop and no cancel obligation is transferred; at a raise the claim is sealed
again into the source's entry and carried out (`hRout`). -/
theorem erwp_M_antiFrameU {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true)
    {G : ShareG} (hG : ∀ k ls ρ, G k ls ρ → CellFold l β F k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β F k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : F k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (F k) hw)))
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableGR T G Rin) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableR T Rout) Q n ls e ρ :=
  erwp_M_antiFrameCR hΦ hF (OpTabN.Twin.refl T)
    (fun m i en h ha => by rw [hab m i en h] at ha; cases ha) hG hRin hRout
    (fun m i en _ h _ ha => by rw [hab m i en h] at ha; cases ha)

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head ubindE)

/-! ### An unwinding row with an unrestricted operation -/

/-- **An unwinding row whose one operation is unrestricted**: `raise : 1 ↠^unr 0`. Its table's
entry has `q = unr`, so the reborrow's table condition must leave abortive entries free. -/
def unrRaiseRow : Row := [{ n := 1, i := 0, q := .unr, A := .unit, B := .zero }]

theorem unrRaiseRow_unwind (x : LifeVar) : unrRaiseRow.Unwind x := by
  intro o ho
  simp only [unrRaiseRow, List.mem_singleton] at ho
  subst ho
  exact ⟨rfl, by decide, id, fun _ _ => .unit⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
