import Core.Chain.SI.ILendProg
import Core.Chain.SI.AntiStopN

/-!
# The test: the handler lends its own cell `imm` and resumes `κ` inside the lend, the borrow
as the answer, `κ` holding a live `mut` lend — `OrDiverges`, with no fuel

    progHL = hnd_Div rtH (hnd_Y yLend ((λc. iterate (fT, c)) (alloc 1)))

    fT     = λs. λb. case b { next → (λ_. s := 5) (y ()); inr s | close → () }
    yLend  = λ(v, κ). let (k, d) = (κ, alloc ()) in (λx. free d; x) (k.1 d)

The task is `progLend`'s, the answer discarded by an application: each turn lends its cell `mut`
at `A₀` to `(λ_. s := 5) (y ())`, so the stored
continuation holds that lend, folded (`erwp_M_frame`). The scheduler's clause allocates a cell `d`
of its own, lends it `imm` (`erwp_I_frame`), and resumes `κ` **inside** that lend with `d` as the
answer; when `κ` returns, it frees `d`. The run never returns: `κ` loops, its next `y` is handled
by the clause again, inside the first clause's lend, and so on; every frame stays open and every
handler frame's record stays on the list.

* **(a) A resume inside the handler's own lend.** When `κ`'s share outlives `xTop`, the longest
  lifetime, the clause lends at `xTop`, longer than the task's live lend at `A₀`; otherwise at a
  lifetime below the share (`ResU.exists_stratum`, 6.64's H11). In the first case the list `κ` is
  resumed at carries a record longer than `A₀` that the stop's list lacks: `Ext` at the borrowed
  continuation's share refuses it (`resume_not_ext`), a list with the stop's members cannot
  carry it, and `extF` allows it
  (`extF_of_addAt`).
* **(b) The borrow as the answer.** In the first case the clause passes the `imm` cell of `d` to
  `κ` with the location (`yAns`'s second disjunct): the capability crosses into the task's live
  `mut` lend, whose re-lend takes it into its frame (`LendOK.pb`: no shorter than `A₀`). In the
  second it passes the location alone. The split is on `κ`'s share, the only fact the clause reads
  of `κ` (`KapRelN`); the program is the same in both cases. In this program the share holds only
  the task's folded cell, an `own` cell, so the first case is the one runs reach.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.HandlerLendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)
open BoCa.Lifetime (LSub)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The tables -/

/-- The task's lend's lifetime. -/
def A₀ : Life := OrderDual.toDual 1

/-- The longest lifetime, longer than the task's lend. -/
def xTop : Life := OrderDual.toDual 0

theorem A₀_lt_xTop : A₀ ⊏ xTop := show (0 : Nat) < 1 from Nat.zero_lt_one

/-- The handler's borrow of `d` at `y`. -/
def immD (y : Life) : CellU Loc Val :=
  CellU.immOf (LSet.singleton y) Val.unit PMap.empty (inStratum_empty _)

/-- `y`'s answer: a location, with an `imm` borrow of it no shorter than `A₀`, or alone. -/
def yAns : Nat → List SRec → Val → WProp := fun _ _ w σ =>
  ∃ d, w = Val.loc d ∧ (σ = PMap.empty ∨ ∃ y, A₀ ⊑ y ∧ σ = ResU.single d (immD y))

/-- `y : 1 ↠^lin Loc`, resumed under `extF`. -/
def yEntH : OpEntN := ⟨.lin, false, unitP, yAns, none, extF⟩

/-- Under both handlers: `y` and the tick. -/
def T2H : OpTabN := fun m i => if m = 6 ∧ i = 0 then some yEntH else T1 m i

theorem T2H_cases {m i : UInt32} {en : OpEntN} (h : T2H m i = some en) :
    (m = 6 ∧ i = 0 ∧ en = yEntH) ∨ (m = divEff ∧ i = 0 ∧ en = tickEnt) := by
  unfold T2H at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (T1_cases h)

theorem entH_cases {m i : UInt32} {en : OpEntN} (h : T2H m i = some en) :
    en = yEntH ∨ en = tickEnt := by
  rcases T2H_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem T2H_down : T2H.Down where
  pa := fun _ _ en h _ _ _ _ hA => by rcases entH_cases h with he | he <;> subst he <;> exact hA
  fin := fun _ _ en P h hP => by rcases entH_cases h with rfl | rfl <;> cases hP
  wcl := fun _ _ en h => by rcases entH_cases h with rfl | rfl <;> exact extF_left

theorem T2H_fin : ∀ m i en, T2H m i = some en → en.fin = none := fun _ _ en h => by
  rcases entH_cases h with rfl | rfl <;> rfl

theorem T1_fin : ∀ m i en, T1 m i = some en → en.fin = none := fun _ _ en h => by
  rw [(T1_cases h).2.2]; rfl

theorem yAns_noOwn {k : Nat} {ls : List SRec} {w : Val} {σ : WRes} (h : yAns k ls w σ) :
    NoOwn σ := by
  obtain ⟨d, -, rfl | ⟨y, -, rfl⟩⟩ := h
  · exact noOwn_empty
  · exact noOwn_single_imm d _ _ _ _

/-- **`T2H` may be stopped at under a live `mut` lend at `A₀`**: the answer's borrow is at `A₀`,
no shorter than the lend. -/
theorem T2H_lendOK : T2H.LendOK A₀ where
  entry := fun _ _ en h => by rcases entH_cases h with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases entH_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases entH_cases h with rfl | rfl
    · obtain ⟨d, -, rfl | ⟨y, hy, rfl⟩⟩ := hB
      · intro l ψ hl; simp at hl
      · refine ResU.inStratum_single d ?_
        show (↓A₀) < (LSet.singleton y).meet
        exact lt_of_lt_of_le (Life.down_sqsubset A₀) hy
    · obtain ⟨-, rfl⟩ := hB
      intro l ψ hl; simp at hl

/-- **`T1` may be stopped at under a live `imm` lend at any lifetime.** -/
theorem T1_ilendOK (x : Life) : T1.ILendOK x where
  entry := fun _ _ en h => by rw [(T1_cases h).2.2]; exact ⟨rfl, rfl, rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rw [(T1_cases h).2.2] at hA
    obtain ⟨-, rfl⟩ := hA
    intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    rw [(T1_cases h).2.2] at hB
    obtain ⟨-, rfl⟩ := hB
    intro l ψ hl; simp at hl
  paExt := fun _ _ en h _ _ _ _ _ _ hA => by rw [(T1_cases h).2.2] at hA ⊢; exact hA
  pbExt := fun _ _ en h _ _ _ _ _ _ hB => by rw [(T1_cases h).2.2] at hB ⊢; exact hB

/-! ### The task: `progLend`'s turn, at `T2H` -/

/-- `s := 5` under `λ_`, `s` the loop's state. -/
def wrE' : Expr := .app (.app (.val (.prim .store)) (.var 3)) (.val (Val.i32 5))

/-- `λs. λb. case b {next → (λ_. s := 5) (y ()); inr s | close → ()}`. -/
def fTH : Val :=
  Val.lam (.lam (.case (.var 0) (.seq (.app (.lam wrE') Stage1.yE) (.inj₂ (.var 2))) (.val .unit)))

/-- The lent computation: `(λ_. ℓ := 5) (y ())`. -/
def lendEH (l : Loc) : Expr := .app (.lam (wrL l)) Stage1.yE

/-- **The borrowed computation**: `y ()` stops with the lend live; after the resume the answer
(with its borrow, if any) is garbage, and the borrow writes. -/
theorem lendH_ok {Φ : LocFam} (hΦ : Φ.Down) (l : Loc) (u : Val) (k : Nat)
    (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A₀ u PMap.empty (inStratum_empty A₀)
      (famF A₀ k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ.set l A₀ (famF A₀)) (opTableN T2H) (MFPost l A₀ (famF A₀) (Qlend l)) k ls
      (lendEH l) BM := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A₀)
  have hFl : Φ.set l A₀ (famF A₀) l = some ⟨A₀, famF A₀⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_perform (T := T2H) (en := yEntH) (K := .appR (.lam (wrL l)) .hole)
    (by simp [Kont.HasHnd]) (by simp [T2H]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  refine erwp_garbage hXB (yAns_noOwn (k := k') (ls := ls') hB) ?_
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2H) (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 w (wrL l)) = wrL l := by
    simp [Expr.subst, Kont.plug, wrL, Val.storeV, Val.loc, Val.i32, Expr.val]
  rw [e]
  refine erwp_of_rwp (rwp_dump (rwp_M_antiFrame hΦ' hFl (ResU.comp_empty_right _) ?_))
  intro W X hW hX
  obtain rfl := eq_of_compS_empty_left hW
  obtain rfl := eq_of_compS_empty_left hX
  refine rwp_store ls' l u (Val.i32 5) _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ?_⟩
  intro ρ₁ ρ₂ h₁ hc
  subst h₁
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨Val.i32 5, PMap.empty, inStratum_empty A₀, rfl, PMap.empty, PMap.empty,
    ResU.comp_empty_right _, ResU.comp_empty_right _, fun X hX => ?_⟩
  obtain rfl := eq_of_compS_empty_left hX
  refine ⟨noOwn_single_mut l, inStratum_empty A₀, fun w Y hY σ ⟨hσ, hF⟩ Z hZ => ?_⟩
  have hσ0 : σ = PMap.empty := hF
  subst hσ0
  obtain rfl := eq_of_compS_empty_left hY
  obtain rfl := ResU.CompS.functional hZ (ResU.comp_empty_right _)
  exact ⟨rfl, w, rfl⟩

/-- **A turn**, as `turn_ok`: the `mut` lend at `A₀` around `(λ_. ℓ := 5) (y ())`. -/
theorem turnH_ok {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IL s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T2H) (turnPostN IL QZ) k ls
      (.app (.app (.val fTH) (.val s)) (.val nextV)) ρ := by
  obtain ⟨l, u, rfl, rfl⟩ := hI
  have hD := opTableN_down T2H_down
  have hTP : (turnPostN IL QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc l)
      (.lam (.case (.var 0) (.seq (.app (.lam wrE') Stage1.yE) (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (lendEH l) (.inj₂ (.val (Val.loc l)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, Stage1.yE, wrE', wrL, lendEH, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, Val.storeV, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (lendEH l) (.inj₂ (.val (Val.loc l)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (lendEH l) (.inj₂ (.val (Val.loc l)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, lendEH, performE, opPayload, Val.pair, Val.i32,
      Val.unit, nextV, Val.inj₁, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (lendEH l) (.inj₂ (.val (Val.loc l))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc l)))).plug (lendEH l) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, lendEH, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₃]
  refine erwp_bind_le (Q' := Qlend l) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin T2H_fin _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, w, rfl⟩
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, l, w, rfl, rfl⟩)
  · exact erwp_M_frame (famF_down A₀) T2H_lendOK k k le_rfl ls (lendEH l) u PMap.empty _
      PMap.empty _ (inStratum_empty A₀) (inStratum_empty _) (famF A₀ k) (fun _ _ h => h) rfl
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) (lendH_ok hΦ l u k ls)

/-! ### The scheduler's clause: a lend of its own cell around the resume -/

/-- `(λx. free d; x)`, `d` the bound cell. -/
def frE : Expr := .lam (.seq (freeE (.var 1)) (.var 0))

/-- The clause's body after `let (k, d) = …`: `(λx. free d; x) (k.1 d)`. -/
def innerE : Expr := .app frE (.app (.app (.var 1) (.val (Val.inj₁ .unit))) (.var 0))

/-- `λ(v, κ). let (k, d) = (κ, alloc ()) in (λx. free d; x) (k.1 d)`. -/
def clLend : Val :=
  Val.lam (.letpair (.var 0)
    (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerE))

/-- The lend's end: `d` owned again. -/
def Qd (d : Loc) : PostN := fun _ _ _ ρ => ptoOwn d Val.unit ρ

/-- After the resume returns: free `d`, return the value. -/
theorem erwp_frE {Φ : LocFam} (hΦ : Φ.Down) (d : Loc) (k : Nat) (ls : List SRec) (x : Val)
    (ρ : WRes) (h : ptoOwn d Val.unit ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T1) QZ k ls
      (.app (.lam (.seq (freeE (.val (Val.loc d))) (.var 0))) (.val x)) ρ := by
  have hD := opTableN_down T1_down
  refine erwp_det hΦ hD QZ_down
    (fun μ => step1Only_plug (Head.beta μ _ x) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 x (.seq (freeE (.val (Val.loc d))) (.var 0))) =
      (Kont.seq .hole x.1).plug (freeE (.val (Val.loc d))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.loc, Expr.val, Val.prim]
  rw [e]
  refine erwp_free hΦ (opTableN_local T1) _ d Val.unit
    ⟨ρ, PMap.empty, ResU.comp_empty_right _, h, ?_⟩
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [Kont.plug_hole]
  exact erwp_val rfl

/-- The record of the handler's lend of `d`. -/
abbrev recH (d : Loc) : FrameRec := ⟨d, Val.unit, PMap.empty, .unk, δ₀⟩

/-- **The clause's lend around the resume.** At a lifetime `x` with `κ`'s share `ρκ` in
`Res_x`: `d` lent `imm` at `x` (`erwp_I_frame`) to `κ.1 d`, at the list with the lend's records
pushed. With `pass` (the lend no shorter than `A₀`), the answer carries the borrow; otherwise the
borrow is garbage. At the end `d` is owned again. -/
theorem lendResume_ok {Φ : LocFam} (κ : Val) (pass : Bool) (x : Life)
    (hpx : pass = true → A₀ ⊑ x) (d : Loc) (k : Nat) (ls : List SRec) (ρκ ρ : WRes)
    (hx : ρκ.InStratum x)
    (hK : KapRelN (ℍ := ℍ) Φ (opTableN T1) QZ yEntH none (k + 1) ls κ ρκ)
    (hρ : ResU.CompS ρκ (ResU.single d (CellU.ownOf Val.unit)) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T1) (fun k' ls' w ρ' => Qd d k' ls' w ρ') k ls
      (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val (Val.loc d))) ρ := by
  have hshape : vShape .unk δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
  have hadm : AdmWf .unk δ₀ := fun _ h => h.elim
  obtain ⟨ds, hds⟩ := lineage_list (r := recH d) hshape hadm
    (ExW.empty_of_all_imm (fun _ _ h => by simp at h))
  refine erwp_I_frame d .unk δ₀ hadm Val.unit PU (fun _ ρ h => ⟨h, trivial⟩)
    (fun _ _ _ _ h => h) (T1_ilendOK x) (fun _ _ _ _ _ _ h => h) k ls _
    PMap.empty _ ρκ ρ (inStratum_empty x) hx rfl (ResU.comp_empty_right _)
    (ResU.CompS.comm hρ) ds hds (fun BI hBI => ?_)
  -- the resume, at the list with the handler's records pushed
  have hwc : yEntH.wc ls (frameList (recH d) ds x ls) ρκ :=
    extF_of_addAt (addAt_frameList _ ds x ls) ρκ
  have hres := (hK.2 _ hwc k (Nat.lt_succ_self k)).1 (Val.loc d)
  refine erwp_mono (Tb := opTableN T1) (Q := QZ) (fun k' ls' w ρ' h => ?_) (opTableN_local T1)
    _ _ _ _ ?_
  · -- `κ` returned owning nothing: `d` owned again
    have h' : ρ' = PMap.empty := h
    subst h'
    refine ⟨fun ρ₁ ρ₂ h₁ hc ρ₃ ρ₄ h₃ hc' => ?_, inStratum_empty x⟩
    obtain rfl := eq_of_compS_empty_left hc
    have h₃' : ρ₃ = PMap.empty := h₃
    subst h₃'
    obtain rfl := ResU.CompS.functional hc' (ResU.comp_empty_right _)
    exact h₁
  · cases pass with
    | true =>
        -- the borrow is the answer's
        exact hres _ BI ⟨d, rfl, Or.inr ⟨x, hpx rfl, rfl⟩⟩ hBI
    | false =>
        -- the location alone; the borrow is garbage
        exact erwp_garbage hBI (noOwn_single_imm d _ _ _ _)
          (hres PMap.empty ρκ ⟨d, rfl, Or.inl rfl⟩ (ResU.comp_empty_right _))

/-- **The clause.** Two steps to `let (k, d) = (κ, alloc ())`, the allocation, two steps to
`(λx. free d; x) (κ.1 d)`; the resume under the lend of `d` (`lendResume_ok`): at `xTop`, longer
than the task's lend, passing the borrow, when `κ`'s share outlives `xTop`; below the share,
passing the location alone, otherwise; then `free d`. -/
theorem erwp_clLend {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) (ls : List SRec) (v κ : Val)
    (ρ : WRes) (hK : KapRelN (ℍ := ℍ) Φ (opTableN T1) QZ yEntH none k ls κ ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T1) QZ k ls (.app (.val clLend) (.pair (.val v) κ.1)) ρ := by
  have hL := opTableN_local T1
  have hD := opTableN_down T1_down
  cases k with
  | zero => exact erwp_zero
  | succ k₀ =>
  have e₀ : (.app (.val clLend) (.pair (.val v) κ.1) : Expr) =
      Kont.hole.plug (.app (.val clLend) (.val (Val.pair v κ))) := rfl
  rw [e₀]
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair v κ) (.letpair (.var 0)
      (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerE))) =
      Kont.hole.plug (.letpair (.val (Val.pair v κ))
        (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerE)) := by
    simp [Kont.plug, Expr.subst, innerE, frE, freeE, Val.inj₁, Val.unit, Val.prim, Expr.val]
  rw [e₁]
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.letpair μ _ _ _) rfl .hole) ?_
  have e₂ : Expr.subst 0 v (Expr.subst 0 (κ.shift 1 0)
      (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerE)) =
      (Kont.letpair (Kont.pairR κ .hole) innerE).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    simp only [Expr.subst, if_true, Val.val_shift, Kont.plug]
    rw [Expr.subst_shift 0 0 0 v _ le_rfl le_rfl, Expr.shift_zero]
    simp [innerE, frE, freeE, Expr.subst, Val.inj₁, Val.unit, Val.prim, Expr.val]
  rw [Kont.plug_hole, e₂]
  refine erwp_alloc hΦ hL _ Val.unit (fun d σ₁ σ₂ hcell hc => ?_)
  subst hcell
  rw [show k₀ + 1 - 1 = k₀ from rfl]
  have e₃ : (Kont.letpair (Kont.pairR κ .hole) innerE).plug (.val (Val.loc d)) =
      Kont.hole.plug (.letpair (.val (Val.pair κ (Val.loc d))) innerE) := rfl
  rw [e₃]
  cases k₀ with
  | zero => exact erwp_zero
  | succ k₁ =>
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.letpair μ _ _ _) rfl .hole) ?_
  have e₄ : Expr.subst 0 κ (Expr.subst 0 ((Val.loc d).shift 1 0) innerE) =
      (Kont.appR (.lam (.seq (freeE (.val (Val.loc d))) (.var 0))) .hole).plug
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val (Val.loc d))) := by
    simp [innerE, frE, freeE, Expr.subst, Expr.shift, Kont.plug, Val.inj₁, Val.unit, Val.prim,
      Val.loc, Expr.val, Val.shift]
  rw [Kont.plug_hole, e₄]
  refine erwp_bind_le (Q' := fun k' ls' w ρ' => Qd d k' ls' w ρ') hΦ _
    (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches])
    (OpTabN.ctxClosed_of_fin T1_fin _) (k₁ + 1)
    (fun k' ls' w ρ' _ h => erwp_frE hΦ d k' ls' w ρ' h) (k₁ + 1) le_rfl ls _ _ ?_
  by_cases hS : ρ.InStratum xTop
  · exact lendResume_ok κ true xTop (fun _ => A₀_lt_xTop.le) d (k₁ + 1) ls ρ σ₂ hS hK hc
  · obtain ⟨x, hx⟩ := ResU.exists_stratum ρ
    exact lendResume_ok κ false x (fun h => by cases h) d (k₁ + 1) ls ρ σ₂ hx hK hc

/-- **The resume list is outside `Ext` at the borrowed continuation's share.** The handler's
lend at `xTop` pushes a record longer than the task's live lend at `A₀`; `Ext`'s lifetime clause at
a share holding the lent cell `mut` at `A₀` keeps the records longer than `A₀` exactly. -/
theorem resume_not_ext (ls : List SRec) (ds : List FrameRec) (d l : Loc) (ρ : WRes)
    (ψ : CellU Loc Val) (hd : (recH d, xTop) ∉ ls) (hρ : ρ.get l = some ψ)
    (hk : ψ.kind = Kind.mut) (hat : ψ.at = A₀) :
    ¬ Ext ls (frameList (recH d) ds xTop ls) ρ := by
  intro h
  have := (h.2 A₀ ⟨l, ψ, hρ, by rw [hk]; simp, le_of_eq hat⟩ (recH d, xTop) A₀_lt_xTop).mpr
    (by simp [frameList])
  exact hd this

/-! ### The handlers and the program -/

/-- `hnd_Y yLend`: the scheduler, `y` must-resume, its clause `clLend`. -/
def yHL : Val := hndVal 6 (qualsVal [.lin]) Stage1.idV (Val.pair clLend .unit)

theorem erwp_yHL {Φ : LocFam} (hΦ : Φ.Down) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T2H) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T1) QZ n ls (hndE yHL e) ρ := by
  refine erwp_handle hΦ T2H T1 T2H_down T1_down 6 (fun m i hm => by simp [T2H, hm]) _ _ _ QZ QZ
    QZ_down ?_ (fun _ => none) (fun _ en _ _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV hΦ T1_down hv) ?_
  · intro i en hT _
    rcases T2H_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · exact Stage1.capTag_one .lin
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT
    rcases T2H_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · refine ⟨clLend, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_, fun h => by cases h⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      exact erwp_clLend hΦ k ls v κ ρ hK
    · exact absurd h6.symm Stage1.divEff_ne6

/-- `(λc. iterate (fTH, c)) (alloc 1)`. -/
def bodyH : Expr :=
  .app (.val (Val.lam (.app (.val (.prim .iterate)) (.pair (.val fTH) (.var 0)))))
    (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

/-- `hnd_Div rtH (hnd_Y yLend bodyH)`. -/
def progHL : Expr := hndE DivRuntime.rtH (hndE yHL bodyH)

theorem bodyH_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN T2H) QZ n [] bodyH (PMap.empty : WRes) := by
  have hD := opTableN_down T2H_down
  refine erwp_alloc Φ₀_down (opTableN_local T2H) (.appR (.val (Val.lam
    (.app (.val (.prim .iterate)) (.pair (.val fTH) (.var 0))))) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (.app (.val (.prim .iterate)) (.pair (.val fTH) (.var 0)))) = iterateE fTH (Val.loc l) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fTH.1 = true from rfl) (Nat.zero_le _)]
  rw [e]
  exact erwp_iterate Φ₀_down T2H_down (OpTabN.ctxClosed_of_fin T2H_fin _) QZ_down rfl (I := IL)
    (en := tickEnt) (by simp [T2H, T1, Stage1.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IL_closed
    (fun k s ls ρ hI => turnH_ok Φ₀_down k s ls ρ hI) _ _ _ _ ⟨l, Val.i32 1, rfl, hcell⟩

theorem progHL_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progHL (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yHL Φ₀_down n [] _ _ (bodyH_ok n))

/-- **Tests (a) and (b).** A task holding a `mut` lend across `y`, on every turn of a loop with no
bound, resumed by a scheduler that lends a cell of its own `imm` and resumes the continuation
inside that lend, passing the cell as the answer, its borrow with it whenever the continuation's
share outlives the task's lend; under the runtime's `Div` handler. Every configuration a run
reaches is a value or steps, a value only at the empty memory, and every `free` finds its cell. No
fuel, no condition on the list the continuation is resumed at beyond `extF`. -/
theorem progHL_orDiverges : OrDiverges (ℍ := ℍ) progHL :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progHL_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.HandlerLendProg

end
