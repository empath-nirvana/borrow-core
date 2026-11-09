import Core.Chain.Inst791N
import Core.Chain.Adequacy791N

/-!
# #844 Tier 1: an outer lend's borrow yielded across an inner suspending lend  `[spec §62]`

A closed instance of `goal791N` at a lifetime-polymorphic constant whose callback bound is a
variable and whose payload borrows an enclosing lend. A parser lends a scratch cell while it
yields borrows of its outer input to a consumer outside the scratch lend:

    r ← alloc (); (r, ()) ← withbor1U r (Λ'3. λi.                 -- the input, lent imm
      s ← alloc (); (s, ()) ← withbor2U s (Λ'4. λc.               -- the scratch cell, '4 ⊏ '3
        handle_yield (
          (c, ()) ← nestC ['3] ['4] c (Λ'0. λm. yield i; forget m); forget c)
        with H; ['4] ());
      free s; ['3] ()); free r

* `nestC`: `Λ'1 ⊏ ⊤. Λ'2 ⊏ '1. withbor3U` at `∀'0 ⊏ '2`, its row `yield : Imm '1 1 ↠^cancel 1`;
  `nestC_ok` is `Const791.OK`.
* `'3` and `'4` are the callback variables of Core's lends `withbor1U` and `withbor2U` at the
  empty row; `nestC` is instantiated by `allEV` at `'3 ⊏ ⊤` and `'4 ⊏ '3`, so the suspending
  lend's callback bound is `'4` and its payload `Imm '3 1` is the outer lend's borrow.
* The handler of `yield` sits inside both Core lends and outside the suspending one. `hRes`
  resumes `κ`, `hCan` cancels it; each releases the payload with `forget`.
* `d_progRes`, `d_progCan`: the programs are typed at `F 1` from `nestC`; `progRes_orDiverges`,
  `progCan_orDiverges`: `goal791N` concludes their adequacy from `HandlerLawN`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Nest844N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791)
open BoCa.BoLo (performE)
open BoCa.Programs (alloc' free')
open BoCa.Fig16.LogRel.Core.CancelIntercept (idV)
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N (dRelease dRelease_closed polyCtx polyCtx_lt
  goal791N HandlerLawN)

/-! ### The constant -/

/-- The name of `yield`. -/
abbrev yN : UInt32 := 7

/-- `yield : Imm '1 1 ↠^cancel 1`, its cancel row `F 1`. -/
def ySig : OpSig := ⟨yN, 0, .cancel, .imm (.var 1) .unit, .unit, .ret .unit, false⟩

/-- **The suspending constant**: `Λ'1 ⊏ ⊤. Λ'2 ⊏ '1. withbor3U` reborrowing `Mut '2 1` at
`∀'0 ⊏ '2`, its callback row `[yield]`, whose payload `Imm '1 1` borrows the enclosing `'1`;
finalised by `forget`.  `[spec §62]` -/
def nestC : Const791 :=
  .poly 1 .top (.poly 2 (.var 1) (.w3 (.var 2) 0 (.var 2) .unit .unit [ySig] dRelease))

/-- `[yield]` suspends at `polyCtx` under `'0 ⊏ '2`: its payload `Imm '1 1` outlives `'2`, and
its cancel row `F 1` has no layer. -/
theorem ySig_suspend : Row.Suspend [ySig] polyCtx 0 (.var 2) := by
  intro o ho
  simp only [List.mem_singleton] at ho
  subst ho
  exact ⟨by simp [ySig], by decide, by simp [ySig, VFree, Lifetime.Life.mentions], id,
    .imm polyCtx_lt, .unit, fun _ => trivial⟩

/-- **`nestC` meets `Const791.OK`**: its callback bound is the variable `'2`, its payload a
borrow at `'1`, its answer `1`.  `[spec §62]` -/
theorem nestC_ok : nestC.OK := by
  refine ⟨rfl, fun _ _ h => by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h,
    rfl, fun z u h => ?_, ?_⟩
  · rw [LifeCtx.find?_extend] at h
    by_cases h1 : (1 : LifeVar) = z
    · rw [if_pos h1] at h; cases h; rfl
    · rw [if_neg h1] at h; simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  refine ⟨fun δ hδ => ?_, id, id, ySig_suspend,
    ⟨.top, fun _ _ => ⟨_, rfl⟩, fun o ho => ?_⟩, dRelease_closed, .releaseMut .nil⟩
  · obtain ⟨m, -, hm, -⟩ := hδ 2 (.var 1) (by simp [LifeCtx.find?_extend])
    exact ⟨m, hm⟩
  · simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨.unit, fun _ => trivial⟩

/-! ### The lifetime contexts and `nestC`'s instance -/

/-- The outer callback's context: `'3 ⊏ ⊤`. -/
abbrev ΔO : LifeCtx := LifeCtx.empty.extend 3 LifeCtx.empty.meetOfDom
/-- The scratch callback's context: `'3 ⊏ ⊤, '4 ⊏ '3 ⊓ ⊤`. -/
abbrev ΔM : LifeCtx := ΔO.extend 4 ΔO.meetOfDom
/-- The suspending lend's callback context: `…, '0 ⊏ '4`. -/
abbrev ΔI : LifeCtx := ΔM.extend 0 (.var 4)

theorem ΔM_lt_top : ΔM.EntailsLt (.var 3) .top :=
  BoCa.Programs.entailsLt_of_bound (u := LifeCtx.empty.meetOfDom) rfl
    (fun _ _ h => ⟨_, h, le_rfl⟩)

theorem ΔM_lt_43 : ΔM.EntailsLt (.var 4) (.var 3) :=
  BoCa.Programs.entailsLt_of_bound (u := ΔO.meetOfDom) rfl
    (fun _ _ h => BoCa.Programs.interp_meet_left h)

/-- `yield` at the outer lend: `Imm '3 1 ↠^cancel 1`. -/
def ySigI : OpSig := ⟨yN, 0, .cancel, .imm (.var 3) .unit, .unit, .ret .unit, false⟩

/-- The handled operations. -/
abbrev yE : List (Qual × VTy × VTy) := [(.cancel, .imm (.var 3) .unit, .unit)]

theorem rowI_eq : Row.ofEff yN yE 0 = [ySigI] := rfl

/-- `nestC`'s type at `'1 := '3`. -/
theorem nestC_inst₁ : (VTy.all 2 (.var 1)
      (withbor3UTy (.var 2) 0 (.var 2) .unit .unit [ySig])).instLife 1 (.var 3) =
    VTy.all 2 (.var 3) (withbor3UTy (.var 2) 0 (.var 2) .unit .unit
      [⟨yN, 0, .cancel, .imm (.var 3) .unit, .unit, .ret .unit, false⟩]) := by
  decide

/-- `nestC`'s type at `'1 := '3`, `'2 := '4`. -/
theorem nestC_inst₂ : (withbor3UTy (.var 2) 0 (.var 2) .unit .unit
      [⟨yN, 0, .cancel, .imm (.var 3) .unit, .unit, .ret .unit, false⟩]).instLife 2 (.var 4) =
    withbor3UTy (.var 4) 0 (.var 4) .unit .unit [ySigI] := by
  decide

/-! ### Splits by the variables a subterm uses -/

section
variable {Δ : LifeCtx} {Γ : Ctx VTy}

theorem bindW {M N : Expr} {A : VTy} {C : CTy}
    (hM : CDerives Δ (part M 0 Γ).1 M (.comp (.ret A)))
    (hN : CDerives Δ (⟨A, true⟩ :: (part M 0 Γ).2) N (.comp C)) :
    CDerives Δ Γ (bindE M N) (.comp C) :=
  .bind (part_split M 0 Γ) hM hN

theorem effLetW {M N : Expr} {A B : VTy} {S : Row}
    (hW : S.Cancels → (part M 0 Γ).2.OwnFree) (hU : S.Unr → Ctx.Banged (part M 0 Γ).2)
    (hM : CDerives Δ (part M 0 Γ).1 M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: (part M 0 Γ).2) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (bindE M N) (.comp (CTy.effOf S B)) :=
  .effLet (part_split M 0 Γ) hW hU hM hN

theorem letpairW {V M : Expr} {A B : VTy} {C : CTy}
    (hV : CDerives Δ (part V 0 Γ).1 V (.val (.tensor A B)))
    (hM : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: (part V 0 Γ).2) M (.comp C)) :
    CDerives Δ Γ (.letpair V M) (.comp C) :=
  .tensorE (part_split V 0 Γ) hV hM

theorem seqCW {V M : Expr} {C : CTy} (hV : CDerives Δ (part V 0 Γ).1 V (.val .unit))
    (hM : CDerives Δ (part V 0 Γ).2 M (.comp C)) : CDerives Δ Γ (.seq V M) (.comp C) :=
  .unitE (part_split V 0 Γ) hV hM

theorem appVW {M : Expr} {i : Nat} {A : VTy} {C : CTy}
    (hM : CDerives Δ (part M 0 Γ).1 M (.comp (.arr A C)))
    (hx : Ctx.SoloP (part M 0 Γ).2 i A) : CDerives Δ Γ (.app M (.var i)) (.comp C) :=
  .app (part_split M 0 Γ) hM hx

/-- A callback `thunk Λ. λx. body` at `∀'x ⊏ @b`, capturing its context. -/
theorem callbackCapU {body : Expr} {x : LifeVar} {b : Lifetime.Life} {L B : VTy} {S : Row}
    (hbx : b.mentions x = false) (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : CDerives (Δ.extend x b) (⟨L, true⟩ :: ⟨.unit, false⟩ :: Γ) body
      (.comp (CTy.effOf S (.box (.var x) B)))) :
    CDerives Δ Γ (.val (.lam (.val (.lam body)))) (.val (cbUTy x b L B S)) :=
  .thunkV rfl (.allI hbx hΔx hΓx (.lam h))

end

/-! ### The program -/

/-- The suspending lend's type at `'3`, `'4`. -/
abbrev TP : VTy := withbor3UTy (.var 4) 0 (.var 4) .unit .unit [ySigI]

/-- The suspending lend's callback: `Λ'0. λm. yield i; forget m; ['0] ()`, `i` the outer
borrow (index 7 in its body). -/
def cbI : Expr :=
  .val (.lam (.val (.lam (bindE (performE (opArgE yN 0 (.var 7)))
    (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit)))))))

/-- The handled body: `p ← nestC [] []; cb ← cbI; (c, u) ← p c cb; u; forget c`, in the
scratch callback's context `c, _, wM, s, i, _, wO, r, nestC`. -/
def hBody : Expr :=
  bindE (.app (.app (.var 8) (.val .unit)) (.val .unit))
    (bindE cbI
      (bindE (.app (.app (.var 1) (.var 2)) (.var 0))
        (.letpair (.var 0) (.seq (.var 0) (.app forget (.var 1))))))

/-- The resuming clause: `λp. let (a, k) = p; u ← forget a; (k (inj₁ ())) u`. -/
def clRes : Val :=
  Val.lam (.letpair (.var 0)
    (bindE (.app forget (.var 1)) (.app (.app (.var 1) (.val (Val.inj₁ Val.unit))) (.var 0))))

/-- The cancelling clause: `λp. let (a, k) = p; forget a; k (inj₂ ())`. -/
def clCan : Val :=
  Val.lam (.letpair (.var 0) (.seq (.app forget (.var 1)) (.app (.var 0) (.val (Val.inj₂ Val.unit)))))

/-- The handler tuple: `h_ret = λx. x` and the clause `cl`. -/
def hnd (cl : Val) : Expr := .pair (.val idV) (.pair (.val cl) (.val .unit))

/-- The scratch callback: `Λ'4. λc. handle_yield hBody with H; ['4] ()`. -/
def cbM (H : Expr) : Expr :=
  .val (.lam (.val (.lam (.seq (hndExpr yN (yE.map Prod.fst) H hBody) (.val .unit)))))

/-- The outer callback: `Λ'3. λi. s ← alloc (); (s, u) ← withbor2U s (cbM H); u; free s;
['3] ()`. -/
def cbO (H : Expr) : Expr :=
  .val (.lam (.val (.lam
    (bindE (.app alloc' (.val .unit))
      (bindE (withborUE free')
        (bindE (cbM H)
          (bindE (.app (.app (.var 1) (.var 2)) (.var 0))
            (.letpair (.var 0) (.seq (.var 0) (.seq (.app free' (.var 1)) (.val .unit)))))))))))

/-- **The program**: `r ← alloc (); (r, u) ← withbor1U r (cbO H); u; free r`.  `[spec §62]` -/
def prog (H : Expr) : Expr :=
  bindE (.app alloc' (.val .unit))
    (bindE (withborUE free')
      (bindE (cbO H)
        (bindE (.app (.app (.var 1) (.var 2)) (.var 0))
          (.letpair (.var 0) (.seq (.var 0) (.app free' (.var 1)))))))

/-! ### Typing -/

theorem nestC_noFree {y : LifeVar} (hy : 3 ≤ y) : ¬ VFree y (.bang nestC.ty) :=
  fun h => by
    have : (VTy.bang nestC.ty).lifeBound = 3 := by decide
    exact absurd (this ▸ lt_vLifeBound h : y < 3) (Nat.not_lt.mpr hy)

theorem ownFree_part_snd (e : Expr) :
    ∀ {i : Nat} {Γ : Ctx VTy}, Γ.OwnFree → (part e i Γ).2.OwnFree
  | _, [], _ => fun _ hs => absurd hs List.not_mem_nil
  | i, ⟨T, true⟩ :: Γ, h => by
      have ih := ownFree_part_snd e (i := i + 1) (Γ := Γ) (fun s hs => h s (.tail _ hs))
      intro s hs hl
      simp only [part, if_true] at hs
      split_ifs at hs <;>
        rcases List.mem_cons.mp hs with rfl | hs <;>
        first | exact absurd hl Bool.false_ne_true | exact ih s hs hl |
          exact h _ (List.mem_cons_self ..) rfl
  | i, ⟨T, false⟩ :: Γ, h => by
      have ih := ownFree_part_snd e (i := i + 1) (Γ := Γ) (fun s hs => h s (.tail _ hs))
      intro s hs hl
      simp only [part] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact absurd hl Bool.false_ne_true
      · exact ih s hs hl

/-- An own-free type, by its head formers. -/
def ownFreeB : VTy → Bool
  | .unit | .zero | .unk | .int _ | .bang _ | .imm _ _ | .mut _ _ => true
  | .tensor A B | .sum A B => ownFreeB A && ownFreeB B
  | _ => false

theorem ownFree_of_B : ∀ {A : VTy}, ownFreeB A = true → A.OwnFree
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .unk, _ => .unk
  | .int w, _ => .int w
  | .bang A, _ => .bang A
  | .imm a A, _ => .imm a A
  | .mut a A, _ => .mut a A
  | .tensor _ _, h => by
      simp only [ownFreeB, Bool.and_eq_true] at h
      exact .tensor (ownFree_of_B h.1) (ownFree_of_B h.2)
  | .sum _ _, h => by
      simp only [ownFreeB, Bool.and_eq_true] at h
      exact .sum (ownFree_of_B h.1) (ownFree_of_B h.2)

theorem ctxOwnFree_of : ∀ {Γ : Ctx VTy}, Γ.all (fun s => !s.live || ownFreeB s.ty) = true →
    Γ.OwnFree
  | [], _ => fun _ hs => absurd hs List.not_mem_nil
  | s₀ :: Γ, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs
      · rw [hl] at h; exact ownFree_of_B (by simpa using h.1)
      · exact ctxOwnFree_of h.2 s hs hl

theorem rowI_not_unr : ¬ Row.Unr [ySigI] := by
  rintro ⟨o, ho, h⟩; simp only [List.mem_singleton] at ho; subst ho; cases h

theorem d_cbI {Γ : Ctx VTy} (hΓ : Γ = [⟨TP, false⟩, ⟨.mut (.var 4) .unit, false⟩,
      ⟨.unit, false⟩, ⟨withbor2UTy 4 ΔO.meetOfDom .unit .unit [], false⟩, ⟨.ref .unit, false⟩,
      ⟨.imm (.var 3) .unit, true⟩, ⟨.unit, false⟩,
      ⟨withbor1UTy 3 LifeCtx.empty.meetOfDom .unit .unit [], false⟩, ⟨.ref .unit, false⟩,
      ⟨.bang nestC.ty, false⟩]) :
    CDerives ΔM Γ cbI (.val (cbUTy 0 (.var 4) (.mut (.var 0) .unit) .unit [ySigI])) := by
  subst hΓ
  refine callbackCapU rfl (fun y u h => ?_) (fun s hs hl => ?_) ?_
  · simp only [LifeCtx.find?_extend] at h
    split_ifs at h <;> first | (cases h; rfl) |
      simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd hl Bool.false_ne_true | simp [VFree, Lifetime.Life.mentions]
  refine effLetW (fun _ s hs hl => ?_) (fun h => absurd h rowI_not_unr)
    (.effPerform (o := ySigI) rfl rfl rfl (.var (by csolo))) ?_
  · exact ownFree_part_snd _ (ctxOwnFree_of rfl) s hs hl
  exact seqCW (.var (by csolo)) (seqCW (appW (.var (by csolo)) (.releaseMut (by cdead)))
    (.effSub (S := []) (RowLe.nil _) (.ret (.boxI (.unitI (by cdead))
      ⟨LifeCtx.defines_of_wf rfl, fun s hs hl =>
        dead_noLive (P := fun s => VOutlives _ _ s.ty) (by cdead) s hs hl⟩))))

/-- The handled body's context: `c, _, wM, s, i, _, wO, r, nestC`, live `c`, `i`, `nestC`. -/
abbrev ΓH : Ctx VTy :=
  [⟨.mut (.var 4) .unit, true⟩, ⟨.unit, false⟩, ⟨withbor2UTy 4 ΔO.meetOfDom .unit .unit [], false⟩,
    ⟨.ref .unit, false⟩, ⟨.imm (.var 3) .unit, true⟩, ⟨.unit, false⟩,
    ⟨withbor1UTy 3 LifeCtx.empty.meetOfDom .unit .unit [], false⟩, ⟨.ref .unit, false⟩,
    ⟨.bang nestC.ty, true⟩]

/-- `nestC ['3] ['4] : TP`, by `allEV` at `'3 ⊏ ⊤` and `'4 ⊏ '3`. -/
theorem d_nestInst {Γ : Ctx VTy} {i : Nat} (h : Ctx.SoloP Γ i (.bang nestC.ty)) :
    CDerives ΔM Γ (.app (.app (.var i) (.val .unit)) (.val .unit)) (.val TP) := by
  have h₁ : CDerives ΔM Γ (.app (.var i) (.val .unit))
      (.val ((VTy.all 2 (.var 1) (withbor3UTy (.var 2) 0 (.var 2) .unit .unit [ySig])).instLife 1
        (.var 3))) := .allEV (.bangE (.var h)) ΔM_lt_top
  rw [nestC_inst₁] at h₁
  have h₂ := CDerives.allEV h₁ ΔM_lt_43
  rwa [nestC_inst₂] at h₂

/-- The suspending lend's callback type. -/
abbrev cbITy : VTy := cbUTy 0 (.var 4) (.mut (.var 0) .unit) .unit [ySigI]

/-- **The handled body** at the row `[yield]`. -/
theorem d_hBody : CDerives ΔM ΓH hBody (.comp (CTy.effOf [ySigI] .unit)) := by
  refine bindW (.ret (d_nestInst (by csolo))) ?_
  refine bindW (.ret (d_cbI rfl)) ?_
  refine effLetW (fun _ => ctxOwnFree_of rfl) (fun h => absurd h rowI_not_unr)
    (A := .tensor (.mut (.var 4) .unit) .unit)
    (appVW (appVW (.force (T := .thunk _) (C := .arr (.mut (.var 4) .unit) (.arr cbITy
      (CTy.effOf [ySigI] (.tensor (.mut (.var 4) .unit) .unit))))  ?_ rfl) ?_) ?_) ?_
  · csolo
  · csolo
  · csolo
  exact letpairW (.var (by csolo)) (seqCW (.var (by csolo))
    (.effSub (RowLe.nil _) (.ret (appW (.var (by csolo)) (.releaseMut (by cdead))))))

/-- The clauses' type at the handler of `yield`. -/
abbrev clTy : VTy := clauseTy [] .unit (.cancel, .imm (.var 3) .unit, .unit) (.ret .unit)

/-- **The resuming clause** releases the payload and resumes `κ`. -/
theorem d_clRes {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val clRes) (.val clTy) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine letpairW (.var (by csolo)) ?_
  refine bindW (.ret (appW (.var (by csolo)) (.releaseImm (by cdead)))) ?_
  exact appVW (.proj₁ (.force (T := .thunk _) (C := .amp (.arr .unit (CTy.effOf [] .unit)) (.ret .unit))
    (by csolo) rfl)) (by csolo)

/-- **The cancelling clause** releases the payload and cancels `κ`. -/
theorem d_clCan {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val clCan) (.val clTy) := by
  refine .bangThunkV (dead_noLive hΓ) rfl (.lam ?_)
  refine letpairW (.var (by csolo)) ?_
  exact seqCW (appW (.var (by csolo)) (.releaseImm (by cdead)))
    (.proj₂ (.force (T := .thunk _) (C := .amp (.arr .unit (CTy.effOf [] .unit)) (.ret .unit)) (by csolo) rfl))

/-- **The handler of `yield`** around the handled body, at `F 1`. -/
theorem d_hnd {cl : Val} (hcl : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives ΔM Γ (.val cl) (.val clTy))
    {Γ : Ctx VTy} (hΓ : Γ = ΓH) :
    CDerives ΔM Γ (hndExpr yN (yE.map Prod.fst) (hnd cl) hBody) (.comp (.ret .unit)) := by
  subst hΓ
  exact .effHandleV (cs := rcsNil) (E := yE) (fs := finsNil) (S := []) (A := .unit)
    (split_kill ΓH).toP (kill_dead _).toP (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI (deadSplit (kill_dead _)) (CancelIntercept.d_idVΓ (kill_dead _) [] .unit)
      (.tensorI (deadSplit (kill_dead _)) (hcl (kill_dead _)) (.unitI (kill_dead _).toP)))
    (by decide) (by simp) (by simp) rfl d_hBody

/-- The scratch lend's callback type: `∀'4 ⊏ '3 ⊓ ⊤. Mut '4 1 ⊸ F(['4] 1)`. -/
abbrev cbMTy : VTy := cbUTy 4 ΔO.meetOfDom (.mut (.var 4) .unit) .unit []

/-- The outer lend's callback type: `∀'3 ⊏ ⊤. Imm '3 1 ⊸ F(['3] 1)`. -/
abbrev cbOTy : VTy := cbUTy 3 LifeCtx.empty.meetOfDom (.imm (.var 3) .unit) .unit []

/-- **The scratch callback**, capturing the outer borrow `i` and `nestC`. -/
theorem d_cbM {cl : Val} (hcl : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives ΔM Γ (.val cl) (.val clTy))
    {Γ : Ctx VTy} (hΓ : Γ = [⟨withbor2UTy 4 ΔO.meetOfDom .unit .unit [], false⟩,
      ⟨.ref .unit, false⟩, ⟨.imm (.var 3) .unit, true⟩, ⟨.unit, false⟩,
      ⟨withbor1UTy 3 LifeCtx.empty.meetOfDom .unit .unit [], false⟩, ⟨.ref .unit, false⟩,
      ⟨.bang nestC.ty, true⟩]) :
    CDerives ΔO Γ (cbM (hnd cl)) (.val cbMTy) := by
  subst hΓ
  refine callbackCapU rfl (fun y u h => ?_) (fun s hs hl => ?_) ?_
  · simp only [LifeCtx.find?_extend] at h
    split_ifs at h <;> first | (cases h; rfl) |
      simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd hl Bool.false_ne_true | exact nestC_noFree (by decide) |
        simp [VFree, Lifetime.Life.mentions]
  exact .unitE (.left (.dead (.dead (.dead (.left (.dead (.dead (.dead (.left .nil)))))))))
    (.ofRet (d_hnd hcl rfl)) (.ret (.boxI (.unitI (by cdead))
    ⟨LifeCtx.defines_of_wf rfl, fun s hs hl =>
      dead_noLive (P := fun s => VOutlives _ _ s.ty) (by cdead) s hs hl⟩))

/-- **The outer callback**: allocates the scratch cell and lends it to the scratch callback. -/
theorem d_cbO {cl : Val} (hcl : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives ΔM Γ (.val cl) (.val clTy))
    {Γ : Ctx VTy} (hΓ : Γ = [⟨withbor1UTy 3 LifeCtx.empty.meetOfDom .unit .unit [], false⟩,
      ⟨.ref .unit, false⟩, ⟨.bang nestC.ty, true⟩]) :
    CDerives LifeCtx.empty Γ (cbO (hnd cl)) (.val cbOTy) := by
  subst hΓ
  refine callbackCapU rfl (fun y u h => ?_) (fun s hs hl => ?_) ?_
  · simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;>
      first | exact absurd hl Bool.false_ne_true | exact nestC_noFree (by decide)
  refine bindW (.ret (appW (.unitI (by cdead)) (.alloc (by cdead)))) ?_
  refine bindW (.ret (.withbor2U (A := .unit) (B := .unit) 4 (by cdead) rfl ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩ id id
    (fun _ h => absurd h List.not_mem_nil) (by decide) (.free (by cdead)))) ?_
  refine .bind (.right (.right (.left (.dead (.dead (.dead (.left .nil))))))) (.ret (d_cbM hcl rfl)) ?_
  refine bindW (A := .tensor (.ref .unit) .unit)
    (appVW (appVW (.force (T := .thunk _) (C := .arr (.ref .unit) (.arr cbMTy
      (CTy.effOf [] (.tensor (.ref .unit) .unit)))) ?_ rfl) ?_) ?_) ?_
  · csolo
  · csolo
  · csolo
  exact letpairW (.var (by csolo)) (seqCW (.var (by csolo))
    (seqCW (appW (.var (by csolo)) (.free (by cdead))) (.ret (.boxI (.unitI (by cdead))
      ⟨LifeCtx.defines_of_wf rfl, fun s hs hl =>
        dead_noLive (P := fun s => VOutlives _ _ s.ty) (by cdead) s hs hl⟩))))

/-- **The program is typed at `F 1` from `nestC`**, at either clause.  `[spec §62]` -/
theorem d_prog {cl : Val} (hcl : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives ΔM Γ (.val cl) (.val clTy)) :
    CDerives LifeCtx.empty (ctx791 [nestC]) (prog (hnd cl)) (.comp (.ret .unit)) := by
  refine bindW (.ret (appW (.unitI (by cdead)) (.alloc (by cdead)))) ?_
  refine bindW (.ret (.withbor1U (A := .unit) (B := .unit) 3 (by cdead) rfl (fun _ h => h.elim) id id
    (fun _ h => absurd h List.not_mem_nil) (by decide) (.free (by cdead)))) ?_
  refine .bind (.right (.right (.left .nil))) (.ret (d_cbO hcl rfl)) ?_
  refine bindW (A := .tensor (.ref .unit) .unit)
    (appVW (appVW (.force (T := .thunk _) (C := .arr (.ref .unit) (.arr cbOTy
      (CTy.effOf [] (.tensor (.ref .unit) .unit)))) ?_ rfl) ?_) ?_) ?_
  · csolo
  · csolo
  · csolo
  exact letpairW (.var (by csolo)) (seqCW (.var (by csolo))
    (.ret (appW (.var (by csolo)) (.free (by cdead)))))

/-! ### `Goal791N` at the two programs -/

/-- **The resumed program**: the handler of `yield` releases the outer borrow and resumes `κ`. -/
def progRes : Expr := prog (hnd clRes)

/-- **The cancelled program**: the handler of `yield` releases the outer borrow and cancels `κ`;
the suspending lend's finaliser releases the scratch borrow. -/
def progCan : Expr := prog (hnd clCan)

/-- **Every premise of `Goal791N` holds at `progRes`.**  `[spec §62]` -/
theorem goal791N_premises_res :
    (∀ c ∈ [nestC], c.OK) ∧
      CDerives LifeCtx.empty (ctx791 [nestC]) progRes (.comp (.ret .unit)) :=
  ⟨by simpa using nestC_ok, d_prog fun h => d_clRes h⟩

/-- **Every premise of `Goal791N` holds at `progCan`.**  `[spec §62]` -/
theorem goal791N_premises_can :
    (∀ c ∈ [nestC], c.OK) ∧
      CDerives LifeCtx.empty (ctx791 [nestC]) progCan (.comp (.ret .unit)) :=
  ⟨by simpa using nestC_ok, d_prog fun h => d_clCan h⟩

/-- **`Goal791N` at `progRes`**: the run that yields the outer borrow across the suspending lend
and resumes is safe, leak-free, or diverges, from `HandlerLawN`.  `[spec §62]` -/
theorem progRes_orDiverges (h : HandlerLawN (ℍ := ℍ)) :
    OrDiverges (ℍ := ℍ) (substAll (vals791 [nestC]) progRes) :=
  goal791N h [nestC] goal791N_premises_res.1 progRes goal791N_premises_res.2

/-- **`Goal791N` at `progCan`**: the run that yields the outer borrow across the suspending lend
and cancels is safe, leak-free, or diverges, from `HandlerLawN`.  `[spec §62]` -/
theorem progCan_orDiverges (h : HandlerLawN (ℍ := ℍ)) :
    OrDiverges (ℍ := ℍ) (substAll (vals791 [nestC]) progCan) :=
  goal791N h [nestC] goal791N_premises_can.1 progCan goal791N_premises_can.2

end BoCa.Fig16.LogRel.Core.Chain.SI.Nest844N

end
