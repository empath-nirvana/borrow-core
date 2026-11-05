import Core.Chain.SI.HeapX
import Core.Chain.SI.HandleN

/-!
# A task that lends its own cell across its own stop, at `erwpX`  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 2b. The task

    lendProg = (λc. park; free c) (alloc ())

starts ghost-free, at the empty mask. It mints `[κ]_1`, allocates `c`, and opens a counted `imm`
lend of `c` (`erwpX_lendOpen`, taken into the stop's mask by `erwpX_lendOpenStop`), then stops at
`park` with the lend open: its continuation resumes at the mask `{(c, lend κ)}`, which the stop
names. In that later segment the lend is ended (`erwpX_lendEnd`) holding `[α]_1`, and `c` is
freed. Under a fixed per-task mask this task could run only at the empty mask (`MaskAuth.zero`),
where no lend is held across a stop.

The table `parkTab` allows a stop at `K[park]` that owes its continuation at `()` at the same share
and list below the index: the stop as a scheduler sees it, before any scheduler is chosen.
`lendProg_erwpX` holds at every index, with no hypotheses.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.LendAcrossProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload freeE)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- `park`: operation `7`, at `()`. -/
def parkE : Expr := performE (.val (opPayload 7 0 Val.unit))

/-- `park; free c`, `c` the bound variable. -/
def bodyP : Expr := .seq parkE (freeE (.var 0))

/-- **The task**: `(λc. park; free c) (alloc ())`. -/
def lendProg : Expr := .app (.val (Val.lam bodyP)) (.app (.val (.prim .alloc)) (.val Val.unit))

/-- **The stop at `park`**: no handler for it in `K`, and the continuation owed at `()`, at the
same share and list, below the index. -/
def parkTab : TableX := fun _ _ _ k ls t Ψ x =>
  ∃ K : Kont, t = K.plug parkE ∧ K.HasHnd 7 = false ∧
    ∀ k', k' < k → Ψ k' ls (K.plug (.val Val.unit)) x

theorem parkTab_local : parkTab.Local := by
  rintro M M' C k ls t Ψ Ψ' x hΨ ⟨K, rfl, hK, h⟩
  exact ⟨K, rfl, hK, fun k' hk' => hΨ k' hk' _ _ _ (h k' hk')⟩

theorem parkTab_down : parkTab.Down := by
  rintro M M' C k ls t Ψ x ⟨K, rfl, hK, h⟩
  exact ⟨K, rfl, hK, fun k' hk' => h k' (by omega)⟩

/-- The empty location typing. -/
def Φ₀ : LocFam := fun _ => none

theorem Φ₀_down : Φ₀.Down := fun _ _ _ h => by cases h

/-- `()`, owning no cell. -/
def QX : PostX := fun _ _ _ v x => v = Val.unit ∧ x.1 = PMap.empty

theorem QX_down : QX.Down := fun _ _ _ _ _ h => h

/-- The lend's type and substitution: the payload is `()`. -/
def δ₀ : BoCa.Lifetime.LSub := ⟨[]⟩

/-- **The segment after the stop**, at the mask the stop named: the lend ended holding `[α]_1`,
then `c` freed. -/
theorem lendProg_after {k : Nat} (c : Loc) (κ A : Life)
    {h : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes)} {BI : WRes}
    (hBI : ResU.CompS (PMap.empty : WRes)
      (ResU.single c (CellU.immOf (LSet.singleton A) Val.unit PMap.empty h)) BI) :
    erwpX (ℍ := ℍ) Φ₀ (insert (c, Auth.lend κ) ∅) parkTab QX k
      [((⟨c, Val.unit, PMap.empty, .unk, δ₀⟩ : FrameRec), A)]
      (.seq (.val Val.unit) (freeE (.val (Val.loc c))))
      (BI, 0 + GRes.life κ + GRes.life A) := by
  refine erwpX_lendEnd Mask.mem_lendLocs_insert _ (List.mem_singleton.mpr rfl)
    (ls' := []) (fun x => ⟨fun h => absurd h List.not_mem_nil,
      fun ⟨h₁, h₂⟩ => absurd (by rw [List.mem_singleton.mp h₁]) h₂⟩) hBI (not_carries_empty A)
    (ResU.hash_symm (ResU.hash_empty_right (ResU.valid_single_own c Val.unit)))
    (fun m a hma => by
      rcases Set.mem_insert_iff.mp hma with e | e
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e; simp [Auth.Held]
      · exact absurd e (by simp))
    (fun ρo hρo => ?_)
  obtain rfl : ρo = ResU.single c (CellU.ownOf Val.unit) := eq_of_compS_empty_left hρo
  refine erwpX_det Φ₀_down parkTab_down QX_down
    (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  exact erwpX_free (Kc := .hole) Φ₀_down parkTab_local c Val.unit (ResU.comp_empty_right _)
    (erwpX_val (fun _ => ⟨rfl, rfl⟩))

/-- **The task lends the cell it allocated across its own stop**, from the empty resource at the
empty mask, at every index, with no hypotheses. -/
theorem lendProg_erwpX (n : Nat) :
    erwpX (ℍ := ℍ) Φ₀ ∅ parkTab QX n [] lendProg ((PMap.empty : WRes), 0) := by
  refine erwpX_mint (fun κ _ _ => ?_)
  show erwpX (ℍ := ℍ) Φ₀ ∅ parkTab QX n []
    ((Kont.appR (.val (Val.lam bodyP)) .hole).plug (.app (.val (.prim .alloc)) (.val Val.unit)))
    _
  refine erwpX_alloc Φ₀_down parkTab_local _ Val.unit (fun c ρ' hc => ?_)
  obtain rfl : ResU.single c (CellU.ownOf Val.unit) = ρ' := ResU.eq_of_comp_empty_right hc
  refine erwpX_det Φ₀_down parkTab_down QX_down
    (fun μ => step1Only_plug (Head.beta μ bodyP (Val.loc c)) rfl .hole) ?_
  have e : Kont.hole.plug (bodyP.subst 0 (Val.loc c)) =
      (Kont.seq .hole (freeE (.val (Val.loc c)))).plug parkE := by
    simp only [bodyP, parkE, Kont.plug, Expr.subst, performE, freeE]
    rfl
  rw [e]
  refine erwpX_lendOpenStop c κ .unk δ₀ (fun _ h => h.elim) Val.unit ⟨rfl, trivial⟩ _ []
    (by simp) (ResU.comp_empty_right _) (fun A _ _ _ h BI hBI => ?_)
  refine rwpGX_here (final_opPlug (r := false) (payloadName_opPayload 7 0 Val.unit)
    (by simp [OpFree, Kont.HasHnd])) (fun C => ⟨Set.mem_insert _ _, _, rfl,
      by simp [Kont.HasHnd], fun k' hk' => ?_⟩)
  simp only [erwpXC, hk', if_true]
  exact lendProg_after c κ A hBI

end BoCa.Fig16.LogRel.Core.Chain.SI.LendAcrossProg

end
