import Core.Chain.SI.CanonRef
import Core.Chain.SI.ILendProg

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

The escrow of the record is `d ↦ own(u₀) ● e ↦ own(())` at `ref (thunk ⊤)`: the escrow of `not_rebReentryAgreeN`'s
configuration.
Its image at `d` has witness `∅` or `e ↦ own(())`; the template fixes one, and the proof works at
whichever it is.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.RebProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg
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
def u₀ : Val := FileProg.idV

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

/-- The record of a lend of `c ↦ own(d)` at `ref S`. -/
def recRS (S : VTy) (c d : Loc) (R₀ : WRes) : FrameRec := ⟨c, .loc d, R₀, .ref S, δ₀⟩

/-- The record of the turn's lend. -/
def recR (c d : Loc) (R₀ : WRes) : FrameRec := recRS (.thunk .top) c d R₀

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
  fun _ _ w ρ => w = Val.unit ∧ ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) R₀ ρ

/-- `!ℓ`. -/
def ldR (l : Loc) : Expr := .app (.val (.prim .load)) (.val (Val.loc l))

/-- `λz. ()`: the loaded thunk is discarded. -/
def discardV : Val := Val.lam (.val .unit)

/-- `(λz. ()) (!d)`. -/
def useR (d : Loc) : Expr := .app (.val discardV) (ldR d)

/-- **The reborrowed computation**: from the canonical image alone, `y ()` stops with the image
in its continuation's share; after the resume the image reads `d` (6.143 at the index), the
thunk read is discarded, and the image is released. -/
theorem rebBody_ok {Φ : LocFam} (hΦ : Φ.Down) (c d : Loc) (R₀ : WRes) (A β : Life) (k : Nat)
    (ls : List SRec) (Bχ : WRes) (P : Val → WProp)
    (hpto : ptoImm d β P Bχ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (RebPost β (IFPost c (.loc d) (PR d R₀) A (Qt c d R₀))) k ls
      (.seq FileProg.yE (useR d)) Bχ := by
  refine erwp_perform (T := T2) (en := yEnt) (K := .seq .hole (useR d)) (by simp [Kont.HasHnd])
    (by simp [T2]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  have hplug : useR d = (Kont.appR (.val discardV) .hole).plug (ldR d) := rfl
  rw [hplug]
  refine erwp_bindR hΦ (opTableN_local T2) (Kont.appR (.val discardV) .hole) (rwp_load_I ls' d β P _
    ⟨_, PMap.empty, ResU.comp_empty_right _, hpto, fun v ρc X hc hX => ?_⟩)
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, u', σ, hs, rfl, -, -⟩ := hc
  generalize k₀ - 1 = k₁
  cases k₁ with
  | zero => exact erwp_zero
  | succ k₂ =>
  refine erwp_step (opTableN_local T2) (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 v (.val Val.unit)) = (Val.unit).1 := by
    simp [Expr.subst, Kont.plug, Val.unit, Expr.val]
  rw [e₁]
  refine erwp_garbage (compS_empty_left _) (noOwn_single_imm d _ _ _ _) (erwp_val ?_)
  refine ⟨⟨fun ρl Y hl hY ρv Z hv hZ => ?_, inStratum_empty A⟩, inStratum_empty β⟩
  obtain ⟨-, rfl⟩ := hv
  subst hl
  obtain rfl := eq_of_compS_empty_left hY
  exact ⟨rfl, hZ⟩

/-- `λx. y (); (λz. ()) (!x)`. -/
def lamX : Val := Val.lam (.seq FileProg.yE (.app (.val discardV) (.app (.val (.prim .load)) (.var 0))))

/-- The lent computation: `(λx. y (); (λz. ()) (!x)) (!c)`. -/
def lendRE (c : Loc) : Expr := .app (.val lamX) (ldR c)

/-- **The lent computation, at every payload type**: loads `d` through the `imm` lend (6.143 at
the index), then reborrows the field at `β = ↓A` across `y` (`erwp_reborrow`, at the canonical
image). The record is at `ref S` for any closed `S` (a thunk, an opaque type, the type a type
variable was instantiated at); the template exists once one image is handed (`hex`, as
`tmpl_exists` gives it at the first entry). -/
theorem lendRG_ok {Φ : LocFam} (hΦ : Φ.Down) (S : VTy) (hSc : ∀ x, ¬ VFree x S) (c d : Loc)
    (u : Val) (RS R₀ : WRes) (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u)) RS R₀)
    (hex : ∃ χ, TmplSpec (recRS S c d R₀) χ)
    (A : Life) (houtP : R₀.InStratum A) (k : Nat) (ls : List SRec)
    (ds : List FrameRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty
      (ResU.single c (CellU.immOf (LSet.singleton A) (.loc d) R₀ houtP)) BI) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (IFPost c (.loc d) (PR d R₀) A (Qt c d R₀)) k
      (frameList (recRS S c d R₀) ds A ls) (lendRE c) BI := by
  obtain rfl := eq_of_compS_empty_left hBI
  set lsF := frameList (recRS S c d R₀) ds A ls with hlsF
  have hplug : lendRE c = (Kont.appR (.val lamX) .hole).plug (ldR c) := rfl
  rw [hplug]
  refine erwp_bindR hΦ (opTableN_local T2) _ (rwp_load_I lsF c A
    (fun v σ => v = .loc d ∧ σ = R₀) _ ⟨_, PMap.empty, ResU.comp_empty_right _,
      ⟨LSet.singleton A, .loc d, R₀, houtP, rfl, ⟨rfl, rfl⟩, le_refl _⟩,
      fun v ρc X hc hX => ?_⟩)
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, v', σ, hs, rfl, hsep, hAs⟩ := hc
  obtain ⟨rfl, ⟨rfl, hσ⟩⟩ := pure_sep_iff.mp hsep
  subst σ
  generalize k - 1 = k'
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.seq FileProg.yE (.app (.val discardV) (.app (.val (.prim .load)) (.var 0))))) =
      .seq FileProg.yE (useR d) := by
    simp [Expr.subst, Kont.plug, FileProg.yE, useR, discardV, ldR, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₁]
  -- the reborrow of the field, at `β = ↓A`
  have hS := tmpl_spec hex
  have hRβ : R₀.InStratum (↓A) := fun m ψ e =>
    CellU.InStratum.mono (Life.down_sqsubset A).le (houtP m ψ e)
  have hshape := canon_ref (r := recRS S c d R₀) (S := S) rfl (x := 0) (hSc 0) hS hRβ
    (fun ℓ h => ⟨u, by
      rw [show ℓ = d from (BoCa.Val.loc_inj.mp h).symm]
      exact (ResU.CompS.get_left_of_ne_imm hR₀ (ResU.single_get_self _ _) (by simp)).2⟩)
  have hr : recRS S c d R₀ ∈ rsOf lsF := by rw [hlsF, rsOf_frameList]; exact List.mem_cons_self
  refine erwp_reborrow (recRS S c d R₀) 0 (hSc 0) hS hRβ hshape (down_le_of_meet hAs)
    (T2_rebOK (↓A)) k₀ lsF _ PMap.empty _ (ResU.comp_empty_right _) (inStratum_empty _) hr
    (fun Bχ hBχ => ?_)
  obtain rfl := eq_of_compS_empty_left hBχ
  obtain ⟨β', hint, ℓ, hk⟩ := hshape
  obtain ⟨hv, hpto⟩ := pure_sep_iff.mp hk
  have hℓ : ℓ = d := (BoCa.Val.loc_inj.mp hv).symm
  subst ℓ
  have hβ' : β' = ↓A := by
    simp [BoCa.Lifetime.Life.interp, find?_extend_self] at hint
    exact (Option.some.inj hint).symm
  subst hβ'
  exact rebBody_ok hΦ c d R₀ A _ k₀ lsF _ _ hpto

/-- **The lent computation** at the thunk payload: `lendRG_ok` at `S := thunk ⊤`, the template
from the image with witness `∅` (`recR_tmpl`). -/
theorem lendR_ok {Φ : LocFam} (hΦ : Φ.Down) (c d e : Loc) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀)
    (A : Life) (houtP : R₀.InStratum A) (k : Nat) (ls : List SRec)
    (ds : List FrameRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty
      (ResU.single c (CellU.immOf (LSet.singleton A) (.loc d) R₀ houtP)) BI) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (IFPost c (.loc d) (PR d R₀) A (Qt c d R₀)) k
      (frameList (recR c d R₀) ds A ls) (lendRE c) BI :=
  lendRG_ok hΦ (.thunk .top) (fun x => by simp [VFree, CFree]) c d u₀ _ R₀ hR₀
    ⟨_, recR_tmpl (c := c) hR₀⟩ A houtP k ls ds BI hBI

/-! ### The turn -/

/-- The loop's invariant: the state is `c ↦ own(d)` with `d ↦ own(u₀) ● e ↦ own(())`. -/
def IR : Val → WProp := fun s ρ => ∃ (c d e : Loc) (R₀ : WRes), s = Val.loc c ∧
  ResU.CompS (ResU.single d (CellU.ownOf u₀)) (ResU.single e (CellU.ownOf .unit)) R₀ ∧
  ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) R₀ ρ

theorem IR_closed : ∀ s ρ, IR s ρ → closedAt 0 s.1 = true := by
  rintro s ρ ⟨c, -, -, -, rfl, -⟩
  rfl

/-- `λs. λb. case b {next → (λx. y (); !x) (!s); inr s | close → ()}`. -/
def fR : Val :=
  Val.lam (.lam (.case (.var 0) (.seq (.app (.val lamX) (.app (.val (.prim .load)) (.var 2)))
    (.inj₂ (.var 2))) (.val .unit)))

/-- **A turn**: three steps to `(λx. y (); !x) (!c); inr c`, the lend of `c` by `erwp_I_frame`
at a lifetime below the list's records, inside it the reborrow of the field, then `inr c`. -/
theorem turnR_ok {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IR s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (turnPostN IR QZ) k ls
      (.app (.app (.val fR) (.val s)) (.val nextV)) ρ := by
  obtain ⟨c, d, e, R₀, rfl, hR₀, hρ⟩ := hI
  have hD := opTableN_down T2_down
  have hTP : (turnPostN IR QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc c)
      (.lam (.case (.var 0) (.seq (.app (.val lamX) (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, lamX, discardV, lendRE, ldR, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, lamX, discardV, lendRE, ldR, FileProg.yE, performE, opPayload, Val.pair,
      Val.i32, Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (lendRE c) (.inj₂ (.val (Val.loc c))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc c)))).plug (lendRE c) := by
    simp [Expr.subst, Kont.plug, lamX, discardV, lendRE, ldR, FileProg.yE, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₃]
  refine erwp_bind_le (Q' := Qt c d R₀) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin T2_fin _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨hv, hσ⟩
    obtain rfl : v = Val.unit := hv
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc c)) (.inr ⟨Val.loc c, rfl, c, d, e, R₀, rfl, hR₀, hσ⟩)
  · -- the lend of `c`, at a lifetime below every record of the list
    obtain ⟨A, -⟩ := exists_fresh ls
    have hshape : vShape rT δ₀ (.loc d) R₀ :=
      ⟨d, u₀, pure_sep_mk rfl ⟨_, _, hR₀, rfl, trivial⟩⟩
    have hadm : AdmWf rT δ₀ := fun y hy => by simp [rT, VFree, CFree] at hy
    have hex : ExS R₀ R₀ := (ExS.split hR₀).mpr ⟨_, _, ExW.single_own d u₀,
      ExW.single_own e Val.unit, hR₀⟩
    obtain ⟨ds, hds⟩ := lineage_list (r := recR c d R₀) hshape hadm hex
    have houtP : R₀.InStratum A := R₀_inStratum A hR₀
    exact erwp_I_frame c rT δ₀ hadm (.loc d) (PR d R₀)
      (fun _ ρ' h => by obtain ⟨-, rfl⟩ := h; exact hshape)
      (fun _ _ _ _ h => h) (T2_ilendOK A) (fun _ _ _ _ _ _ h => h) k ls (lendRE c)
      R₀ _ PMap.empty ρ houtP (inStratum_empty A) ⟨rfl, rfl⟩ hρ
      (ResU.comp_empty_right _) ds hds
      (lendR_ok hΦ c d e R₀ hR₀ A houtP k ls ds)

/-! ### The program -/

/-- `(λc. iterate (fR, c))`. -/
def lamC : Val := Val.lam (.app (.val (.prim .iterate)) (.pair (.val fR) (.var 0)))

/-- `(λd. lamC (alloc d))`. -/
def lamD : Val := Val.lam (.app (.val lamC) (.app (.val (.prim .alloc)) (.var 0)))

/-- `(λe. lamD (alloc u₀))`. -/
def lamE : Val := Val.lam (.app (.val lamD) (.app (.val (.prim .alloc)) (.val u₀)))

/-- `lamE (alloc ())`. -/
def bodyR : Expr := .app (.val lamE) (.app (.val (.prim .alloc)) (.val Val.unit))

/-- `hnd_Div rtH (hnd_Y yStore bodyR)`. -/
def progReb : Expr := hndE DivRuntime.rtH (hndE yH bodyR)

theorem bodyR_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN T2) QZ n [] bodyR (PMap.empty : WRes) := by
  have hD := opTableN_down T2_down
  have hL := opTableN_local T2
  -- `e`
  refine erwp_alloc Φ₀_down hL (.appR (.val lamE) .hole) Val.unit (fun e σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₁ : Kont.hole.plug (Expr.subst 0 (Val.loc e)
      (.app (.val lamD) (.app (.val (.prim .alloc)) (.val u₀)))) =
      (Kont.appR (.val lamD) .hole).plug (.app (.val (.prim .alloc)) (.val u₀)) := by
    simp [Expr.subst, Kont.plug, lamD, lamC, fR, lamX, discardV, u₀, FileProg.idV, FileProg.yE,
      performE, opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₁]
  -- `d`
  refine erwp_alloc Φ₀_down hL (.appR (.val lamD) .hole) u₀ (fun d τ₁ τ₂ hcd hcd' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₂ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.val lamC) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val lamC) .hole).plug (.app (.val (.prim .alloc)) (.val (Val.loc d))) := by
    simp [Expr.subst, Kont.plug, lamC, fR, lamX, discardV, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₂]
  -- `c`
  refine erwp_alloc Φ₀_down hL (.appR (.val lamC) .hole) (Val.loc d)
    (fun c υ₁ υ₂ hcc hcc' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₃ : Kont.hole.plug (Expr.subst 0 (Val.loc c)
      (.app (.val (.prim .iterate)) (.pair (.val fR) (.var 0)))) = iterateE fR (Val.loc c) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fR.1 = true from rfl) (Nat.zero_le _)]
  rw [h₃]
  subst hcell hcd hcc
  exact erwp_iterate Φ₀_down T2_down (OpTabN.ctxClosed_of_fin T2_fin _) QZ_down rfl (I := IR)
    (en := tickEnt) (by simp [T2, T1, FileProg.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IR_closed
    (fun k s ls ρ hI => turnR_ok Φ₀_down k s ls ρ hI) _ _ _ _
    ⟨c, d, e, _, rfl, ResU.CompS.comm hcd', ResU.CompS.comm hcc'⟩

theorem progReb_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progReb (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yH Φ₀_down n [] _ _ (bodyR_ok n))

/-- **The reborrow test.** On every turn of a loop with no bound, a cell is lent `imm`, a field
of it (a `ref` to a thunk, whose escrow holds a cell of the thunk's) is reborrowed at a shorter
lifetime, and the reborrow is live across `y`, under a scheduler that stores the continuation in
a cell and resumes it, under the runtime's `Div` handler: every configuration a run reaches is a
value or steps, a value only at the empty memory, and every `free` finds its cell. No fuel. -/
theorem progReb_orDiverges : OrDiverges (ℍ := ℍ) progReb :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progReb_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.RebProg

end
