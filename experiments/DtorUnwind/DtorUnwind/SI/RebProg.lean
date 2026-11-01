import DtorUnwind.SI.CanonRef
import DtorUnwind.SI.ILendProg

/-!
# The test: a reborrow of a borrowed field live across a `yield`, under a scheduler that
stores `κ`, around a loop with no bound — `OrDiverges`, with no fuel

    progReb = hnd_Div rtH (hnd_Y yStore (
                (λe. (λd. (λc. iterate (fR, c)) (alloc d)) (alloc u₀)) (alloc ())))

    fR = λs. λb. case b { next → (λx. y (); !x) (!s); inr s | close → () }

The cell `c` holds `d`, a `ref` to a thunk `u₀`; the cell `e` belongs to the thunk. Each turn
lends `c` `imm` at `A` (`erwp_I_frame`), loads `d` through the lend, and reborrows the field at
`β = ↓A` (`erwp_reborrow`): the reborrow of `d` is live across `y`, whose `κ` the scheduler stores
in a cell, takes back and resumes; after the resume the reborrow reads `d`, and both borrows end.

The escrow of the record is `d ↦ own(u₀) ● e ↦ own(())` at `ref (thunk ⊤)`: round 8's escrow.
Its image at `d` has witness `∅` or `e ↦ own(())`; the template fixes one, and the proof works at
whichever it is.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI.RebProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI.LendProg
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI.ILendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)
open BoCa.Lifetime (LSub LifeVar)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- **`T2` may be stopped at under a live reborrow at any lifetime.** -/
theorem T2_rebOK (β : Life) : T2.RebOK β where
  entry := (T2_lendOK β).entry
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases ent_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases ent_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      intro l ψ hl; simp at hl

/-- The record's type: a `ref` to a thunk. -/
def rT : VTy := .ref (.thunk .top)

theorem rT_free (x : LifeVar) : ¬ VFree x rT := by simp [rT, VFree, CFree]

/-- The thunk. -/
def u₀ : Val := Stage1.idV

/-- `ag` of one `imm` cell with an empty witness. -/
theorem agW_single_imm_empty (l : Loc) (s : LSet) (v : Val)
    (h : ResU.InStratum s.join (PMap.empty : WRes)) :
    AgW (ResU.single l (CellU.immOf s v PMap.empty h))
      (ResU.single l (CellU.immOf s v PMap.empty h)) :=
  AgW.single_imm ⟨PMap.empty, PMap.empty, DeepReborrow.agW_empty, DeepReborrow.exR_empty,
    ResU.comp_empty_right _⟩ (ResU.comp_empty_right _)

/-- The shape of a reborrow at `ref (thunk ⊤)`: one `imm` cell at the root, any witness. -/
theorem imageShape_rT (δ : LSub) (x : LifeVar) (β : Life) (d : Loc) (v : Val) (w : WRes)
    (h : w.InStratum (LSet.singleton β).join) :
    vShape (rT.immReborrow (.var x)) (δ.extend x β) (.loc d)
      (ResU.single d (CellU.immOf (LSet.singleton β) v w h)) := by
  refine ⟨β, ?_, d, pure_sep_mk rfl ⟨LSet.singleton β, v, w, h, rfl, trivial, le_refl _⟩⟩
  simp [BoCa.Lifetime.Life.interp, find?_extend_self]
  rfl

/-- The record of the turn's lend. -/
def recR (c d : Loc) (R₀ : WRes) : FrameRec := ⟨c, .loc d, R₀, rT, δ₀⟩

/-- **The template exists** for the escrow `d ↦ own(u₀) ● e ↦ own(())`: the image with witness
`∅` is typed. -/
theorem recR_tmpl {c d e : Loc} {R₀ : WRes}
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀) :
    TmplSpec (recR c d R₀) (tmpl (recR c d R₀)) := by
  refine tmpl_spec ⟨_, ⊤, 0, rT_free 0,
    reb_pair_at hR₀ (ResU.single_get_self _ _) ⟨_, hR₀⟩ (single_del_self _ _)
      (inStratum_empty _),
    imageShape_rT δ₀ 0 ⊤ d u₀ _ _, _, agW_single_imm_empty d _ u₀ _⟩

theorem R₀_inStratum {d e : Loc} {R₀ : WRes} (β : Life)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀) :
    R₀.InStratum β :=
  ResU.CompS.inStratum hR₀ (ResU.inStratum_single d (by simp)) (ResU.inStratum_single e (by simp))

/-- The lend's payload: the escrow. -/
def PR (d : Loc) (R₀ : WRes) : List SRec → Val → WProp := fun _ v ρ => v = .loc d ∧ ρ = R₀

/-- The lend's end: the turn's resource. -/
def Qt (c d : Loc) (R₀ : WRes) : PostN :=
  fun _ _ _ ρ => ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) R₀ ρ

/-- `!ℓ`. -/
def ldR (l : Loc) : Expr := .app (.val (.prim .load)) (.val (Val.loc l))

/-- **The reborrowed computation**: from the canonical image alone, `y ()` stops with the image
in its continuation's share; after the resume the image reads `d` (6.143 at the index) and is
dropped. -/
theorem rebBody_ok {Φ : LocFam} (c d : Loc) (R₀ : WRes) (A β : Life) (k : Nat)
    (ls : List SRec) (Bχ : WRes)
    (hpto : ptoImm d β (fun _ _ => True) Bχ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (RebPost β (IFPost c (.loc d) (PR d R₀) A (Qt c d R₀))) k ls
      (.seq Stage1.yE (ldR d)) Bχ := by
  refine erwp_perform (T := T2) (en := yEnt) (K := .seq .hole (ldR d)) (by simp [Kont.HasHnd])
    (by simp [T2]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_of_rwp (rwp_dump (rwp_load_I ls' d β (fun _ _ => True) _ ⟨_, PMap.empty,
    ResU.comp_empty_right _, hpto, fun v ρc X hc hX => ?_⟩))
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, u', σ, hs, rfl, -, -⟩ := hc
  refine ⟨noOwn_single_imm d _ _ _ _, ⟨⟨fun ρl Y hl hY ρv Z hv hZ => ?_, inStratum_empty A⟩,
    inStratum_empty β⟩⟩
  obtain ⟨-, rfl⟩ := hv
  subst hl
  obtain rfl := eq_of_compS_empty_left hY
  exact hZ

/-- `λx. y (); !x`. -/
def lamX : Val := Val.lam (.seq Stage1.yE (.app (.val (.prim .load)) (.var 0)))

/-- The lent computation: `(λx. y (); !x) (!c)`. -/
def lendRE (c : Loc) : Expr := .app (.val lamX) (ldR c)

/-- **The lent computation**: loads `d` through the `imm` lend (6.143 at the index), then
reborrows the field at `β = ↓A` across `y` (`erwp_reborrow`, at the canonical image). -/
theorem lendR_ok {Φ : LocFam} (hΦ : Φ.Down) (c d e : Loc) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀)
    (A : Life) (houtP : R₀.InStratum A) (k : Nat) (ls : List SRec) (hA : ∀ x ∈ ls, x.2 ⊐ A)
    (ds : List FrameRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty
      (ResU.single c (CellU.immOf (LSet.singleton A) (.loc d) R₀ houtP)) BI) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (IFPost c (.loc d) (PR d R₀) A (Qt c d R₀)) k
      (frameList (recR c d R₀) ds A ls) (lendRE c) BI := by
  obtain rfl := eq_of_compS_empty_left hBI
  set lsF := frameList (recR c d R₀) ds A ls with hlsF
  have hplug : lendRE c = (Kont.appR (.val lamX) .hole).plug (ldR c) := rfl
  rw [hplug]
  refine erwp_bindR hΦ (opTableN_local T2) _ (rwp_load_I lsF c A
    (fun v σ => v = .loc d ∧ σ = R₀) _ ⟨_, PMap.empty, ResU.comp_empty_right _,
      ⟨LSet.singleton A, .loc d, R₀, houtP, rfl, ⟨rfl, rfl⟩, le_refl _⟩,
      fun v ρc X hc hX => ?_⟩)
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, v', σ, hs, rfl, hsep, -⟩ := hc
  obtain ⟨rfl, ⟨rfl, hσ⟩⟩ := pure_sep_iff.mp hsep
  subst σ
  generalize k - 1 = k'
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.seq Stage1.yE (.app (.val (.prim .load)) (.var 0)))) = .seq Stage1.yE (ldR d) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, ldR, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.loc, Expr.val, Val.prim]
  rw [e₁]
  -- the reborrow of the field, at `β = ↓A`
  have hS := recR_tmpl (c := c) hR₀
  have hRβ := R₀_inStratum (↓A) hR₀
  have hshape := canon_ref (r := recR c d R₀) (S := .thunk .top) rfl
    (x := 0) (by simp [VFree, CFree]) hS hRβ
    (fun ℓ h => ⟨u₀, by rw [show ℓ = d from (BoCa.Val.loc_inj.mp h).symm]; exact pair_get_left hR₀⟩)
  have hr : recR c d R₀ ∈ rsOf lsF := by rw [hlsF, rsOf_frameList]; exact List.mem_cons_self
  have hβls : ∀ y ∈ lsF, y.2 ⊐ ↓A := by
    intro y hy
    simp only [hlsF, frameList, List.mem_cons, List.mem_append, List.mem_map] at hy
    rcases hy with rfl | ⟨d', -, rfl⟩ | hy
    · exact Life.down_sqsubset A
    · exact Life.down_sqsubset A
    · exact lt_trans (Life.down_sqsubset A) (hA y hy)
  refine erwp_reborrow (recR c d R₀) 0 (rT_free 0) hS hRβ hshape (T2_rebOK (↓A)) k₀ lsF _
    PMap.empty _ (ResU.comp_empty_right _) (inStratum_empty _) hr hβls (fun Bχ hBχ => ?_)
  obtain rfl := eq_of_compS_empty_left hBχ
  obtain ⟨β', hint, ℓ, hk⟩ := hshape
  obtain ⟨hv, hpto⟩ := pure_sep_iff.mp hk
  have hℓ : ℓ = d := (BoCa.Val.loc_inj.mp hv).symm
  subst ℓ
  have hβ' : β' = ↓A := by
    simp [BoCa.Lifetime.Life.interp, find?_extend_self] at hint
    exact (Option.some.inj hint).symm
  subst hβ'
  exact rebBody_ok c d R₀ A _ k₀ lsF _ hpto

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI.RebProg

end
