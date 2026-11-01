import DtorUnwind.SI.ForestLendProg
import DtorUnwind.SI.ILendProg
import DtorUnwind.SI.AntiStopN

/-!
# The forest test, round 7's configuration: the scheduler resumes `κ` inside an `imm` lend of
its own

    progH = hnd_Div rtH (
              hnd_Y yImm (                         -- y : 1 ↠^lin 1, resumed at ExtK A
                (λc. iterate (fT, c)) (alloc 1)))  -- each turn: mut lend of c at A across y

    yImm = λ(v, κ). (λd. κ.1 (inj₁ ()) (); free d) (alloc ())

The task is `SI/LendProg.lean`'s. The scheduler's clause allocates a cell `d` of its own, lends
it `imm` at a fresh `α ⊑ A` (the logical Imm Frame, `erwp_I_frame`), and resumes `κ` inside that
lend: `κ` carries the task's `mut` lend at `A`, opened before the scheduler's frame. The resumed
task ticks with the scheduler's frame live (the frame is across the runtime's stops), and its
next `y` is handled by the re-installed scheduler inside the frame, which nests another frame.
Each resume is at the list with the scheduler's frame added: `ExtK A` holds there
(`extK_add`), `sameW` does not (`not_sameW_add`). `progH_orDiverges`: `OrDiverges`, no fuel.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI.ForestHandlerProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI.LendProg
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI.ForestLendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)
open BoCa.Lifetime (LSub)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The tables: `y` at `ExtK A`, the tick at `sameW` -/

def T2H (A : Life) : OpTabN := fun m i => if m = 6 ∧ i = 0 then some (yEntK A) else T1 m i

theorem T2H_cases {A : Life} {m i : UInt32} {en : OpEntN} (h : T2H A m i = some en) :
    (m = 6 ∧ i = 0 ∧ en = yEntK A) ∨ (m = divEff ∧ i = 0 ∧ en = tickEnt) := by
  unfold T2H at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (T1_cases h)

theorem entH_cases {A : Life} {m i : UInt32} {en : OpEntN} (h : T2H A m i = some en) :
    en = yEntK A ∨ en = tickEnt := by
  rcases T2H_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem T2H_down (A : Life) : (T2H A).Down where
  pa := fun _ _ en h _ _ _ _ hA => by rcases entH_cases h with he | he <;> subst he <;> exact hA
  fin := fun _ _ en P h hP => by rcases entH_cases h with rfl | rfl <;> cases hP
  wcl := fun _ _ en h => by
    rcases entH_cases h with rfl | rfl
    · exact extK_left
    · exact sameW_left

theorem T2H_fin (A : Life) : ∀ m i en, T2H A m i = some en → en.fin = none := fun _ _ en h => by
  rcases entH_cases h with rfl | rfl <;> rfl

/-- **`T2H A` may be stopped at under a live `mut` lend at `A`.** -/
theorem T2H_lendOKK (A : Life) : (T2H A).LendOKK A where
  entry := fun _ _ en h => by
    rcases entH_cases h with rfl | rfl
    · exact ⟨rfl, rfl, wcUnfold_extK le_rfl⟩
    · exact ⟨rfl, rfl, wcUnfold_sameW A⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases entH_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases entH_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      intro l ψ hl; simp at hl

/-- **`T1` may be stopped at under a live `imm` lend at any lifetime**: the runtime's tick. -/
theorem T1_ilendOK (α : Life) : T1.ILendOK α where
  entry := fun _ _ en h => by obtain ⟨-, -, rfl⟩ := T1_cases h; exact ⟨rfl, rfl, rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    obtain ⟨-, -, rfl⟩ := T1_cases h
    obtain ⟨-, rfl⟩ := hA
    intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    obtain ⟨-, -, rfl⟩ := T1_cases h
    obtain ⟨-, rfl⟩ := hB
    intro l ψ hl; simp at hl
  paExt := fun _ _ en h _ _ _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := T1_cases h; exact hA
  pbExt := fun _ _ en h _ _ _ _ _ _ hB => by obtain ⟨-, -, rfl⟩ := T1_cases h; exact hB

/-! ### The scheduler's clause: a frame of its own, `κ` resumed inside it -/

/-- `(λ_. free d) (κ.1 (inj₁ ()) ())`, under `λd`; `κ` the enclosing `letpair`'s second
variable. -/
def clB : Expr :=
  .app (.lam (freeE (.var 1))) (.app (.app (.var 1) (.val (Val.inj₁ .unit))) (.val .unit))

/-- `λ(v, κ). (λd. (λ_. free d) (κ.1 (inj₁ ()) ())) (alloc ())`. -/
def clImm : Val :=
  Val.lam (.letpair (.var 0) (.app (.lam clB) (.app (.val (.prim .alloc)) (.val Val.unit))))

/-- The resume, `κ.1 (inj₁ ()) ()`. -/
def resE (κ : Val) : Expr := .app (.app κ.1 (.val (Val.inj₁ .unit))) (.val .unit)

theorem T1_fin : ∀ m i en, T1 m i = some en → en.fin = none := fun _ _ en h => by
  rw [(T1_cases h).2.2]; rfl

/-- The scheduler's cell `d` after the clause: owned, holding `()`. -/
def Qd (d : Loc) : PostN := fun _ _ _ ρ => ptoOwn d Val.unit ρ

/-- **The scheduler's clause.** Three free steps and the allocation of `d`; then `κ` resumed
inside the logical Imm Frame of `d` at `α`, chosen below every tag of the list, below every cell
of `κ`'s share, and below `A`; the resume is at the list with the frame's records added, where
`ExtK A` holds (`extK_add`); then `free d`. -/
theorem erwp_clImm {Φ : LocFam} (hΦ : Φ.Down) (A : Life) {k : Nat} {ls : List SRec}
    {v κ : Val} {ρ : WRes}
    (hK : ∀ ls', ExtK A ls ls' ρ → ∀ k', k' < k →
      (∀ w : Val, ((yEntK A).PB k' ls' w ─⋆
        erwp (ℍ := ℍ) Φ (opTableN T1) QZ k' ls' (.app (.app κ.1 (.val (Val.inj₁ .unit)))
          (.val w))) ρ)) :
    erwp (ℍ := ℍ) Φ (opTableN T1) QZ k ls (.app (.val clImm) (.pair (.val v) κ.1)) ρ := by
  have hL := opTableN_local T1
  have hD := opTableN_down T1_down
  cases k with
  | zero => exact erwp_zero
  | succ k₀ =>
  have e₀ : (.app (.val clImm) (.pair (.val v) κ.1) : Expr) =
      Kont.hole.plug (.app (.val clImm) (.val (Val.pair v κ))) := rfl
  rw [e₀]
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e₁ : Expr.subst 0 (Val.pair v κ)
      (.letpair (.var 0) (.app (.lam clB) (.app (.val (.prim .alloc)) (.val Val.unit)))) =
      Kont.hole.plug (.letpair (.val (Val.pair v κ))
        (.app (.lam clB) (.app (.val (.prim .alloc)) (.val Val.unit)))) := by
    simp [Kont.plug, Expr.subst, clB, freeE, Val.inj₁, Val.unit, Val.prim]
  rw [Kont.plug_hole, e₁]
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.letpair μ _ _ _) rfl .hole) ?_
  set clB' : Expr :=
    .app (.lam (freeE (.var 1))) (.app (.app (κ.1.shift 1 0) (.val (Val.inj₁ .unit))) (.val .unit))
    with hclB'
  have e₂ : Expr.subst 0 v (Expr.subst 0 (κ.shift 1 0)
      (.app (.lam clB) (.app (.val (.prim .alloc)) (.val Val.unit)))) =
      (Kont.appR (.lam clB') .hole).plug (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    simp only [Expr.subst, clB, freeE, Kont.plug, hclB']
    simp [Val.inj₁, Val.unit, Val.prim, Val.shift, Expr.subst, Expr.shift_shift]
    exact Expr.subst_shift 1 0 1 _ _ (by omega) (by omega)
  rw [Kont.plug_hole, e₂]
  refine erwp_alloc hΦ hL _ Val.unit (fun d σ₁ σ₂ hcell hc => ?_)
  have hcell' : σ₁ = ResU.single d (CellU.ownOf Val.unit) := hcell
  subst hcell'
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 (Val.loc d) clB') =
      (Kont.appR (.lam (freeE (.val (Val.loc d)))) .hole).plug (resE κ) := by
    simp only [hclB', Expr.subst, Kont.plug, resE, freeE]
    simp [Val.inj₁, Val.unit, Val.loc, Val.prim, Expr.subst]
    rw [Expr.subst_shift 0 0 0 _ _ le_rfl le_rfl, Expr.shift_zero]
    exact ⟨rfl, rfl⟩
  rw [e₃]
  refine erwp_bind_le (Q' := Qd d) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin T1_fin _) k₀ ?_ k₀ le_rfl ls _ _ ?_
  · rintro k' ls' w σ - hσ
    refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
    have e₄ : Expr.subst 0 w (freeE (.val (Val.loc d))) =
        Kont.hole.plug (freeE (.val (Val.loc d))) := by
      simp [freeE, Expr.subst, Kont.plug, Val.loc, Val.prim]
    rw [e₄]
    refine erwp_free hΦ hL .hole d Val.unit ⟨σ, PMap.empty, ResU.comp_empty_right σ, hσ, ?_⟩
    exact erwp_val (v := Val.unit) rfl
  · -- the scheduler's frame: `d` lent `imm` at `α`, `κ` resumed inside it
    obtain ⟨a, ha⟩ := exists_fresh ls
    obtain ⟨b, hb⟩ := ResU.exists_stratum ρ
    have hαA : min (min a b) A ≤ A := min_le_right _ _
    have hαa : min (min a b) A ≤ a := (min_le_left _ _).trans (min_le_left _ _)
    have hαb : min (min a b) A ≤ b := (min_le_left _ _).trans (min_le_right _ _)
    set α : Life := min (min a b) A with hαdef
    have hρα : ρ.InStratum α := fun m ψ e => CellU.InStratum.mono hαb (hb m ψ e)
    have hAtag : ∀ x ∈ ls, x.2 ⊐ α := fun x hx => lt_of_le_of_lt hαa (ha x hx)
    have hshape : vShape .unk ILendProg.δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
    have hadm : AdmWf .unk ILendProg.δ₀ := fun _ h => h.elim
    obtain ⟨ds, hds⟩ := lineage_list (r := ⟨d, Val.unit, PMap.empty, .unk, ILendProg.δ₀⟩)
      hshape hadm (ExW.empty_of_all_imm (fun _ _ h => by simp at h))
    refine erwp_I_frame d .unk ILendProg.δ₀ hadm Val.unit ILendProg.PU
      (fun _ ρ h => ⟨h, trivial⟩) (fun _ _ _ _ h => h) (T1_ilendOK α)
      (fun _ _ _ _ _ _ h => h) k₀ ls (resE κ) PMap.empty _ ρ _ (inStratum_empty α) hρα rfl
      (ResU.comp_empty_right _) (ResU.CompS.comm hc) hAtag ds hds (fun BI hBI => ?_)
    -- the resume is at the list with the frame's records: `ExtK A` holds there
    have hwc : ExtK A ls (frameList ⟨d, Val.unit, PMap.empty, .unk, ILendProg.δ₀⟩ ds α ls) ρ :=
      extK_add hαA (addAt_frameList _ ds α ls) hρα
    have h0 := hK _ hwc k₀ (by omega) Val.unit PMap.empty ρ ⟨rfl, rfl⟩ (ResU.comp_empty_right ρ)
    refine erwp_mono (fun k' ls' w σ hq => ?_) (fun k ls t Ψ Ψ' ρ hΨ h => hL k ls t Ψ Ψ' ρ hΨ h)
      _ _ _ _ (erwp_garbage hBI (noOwn_single_imm _ _ _ _ _) h0)
    have hσ : σ = PMap.empty := hq
    subst hσ
    refine ⟨fun σ₁ σ₂ h₁ hc₁ σ₃ σ₄ h₃ hc₃ => ?_, inStratum_empty α⟩
    obtain rfl := eq_of_compS_empty_left hc₁
    have h₃' : σ₃ = PMap.empty := h₃
    subst h₃'
    obtain rfl := ResU.CompS.functional hc₃ (ResU.comp_empty_right _)
    exact h₁

/-! ### The scheduler -/

/-- `hnd_Y yImm`: `y` must-resume, its clause `clImm`. -/
def yHI : Val := hndVal 6 (qualsVal [.lin]) Stage1.idV (Val.pair clImm .unit)

theorem erwp_yHI {Φ : LocFam} (hΦ : Φ.Down) (A : Life) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN (T2H A)) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T1) QZ n ls (hndE yHI e) ρ := by
  refine erwp_handle hΦ (T2H A) T1 (T2H_down A) T1_down 6
    (fun m i hm => by simp [T2H, hm]) _ _ _ QZ QZ
    QZ_down ?_ (fun _ => none) (fun _ en _ _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV hΦ T1_down hv) ?_
  · intro i en hT _
    rcases T2H_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · exact Stage1.capTag_one .lin
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT
    rcases T2H_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · refine ⟨clImm, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_, fun h => by cases h⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      exact erwp_clImm hΦ A (fun ls' hw k' hk' => (hK ls' hw k' hk').1)
    · exact absurd h6.symm Stage1.divEff_ne6

/-! ### The task, at `T2H A` -/

/-- The borrowed computation `y (); ℓ := 5` (`lend_ok` at `T2H A`). -/
theorem lend_okH {Φ : LocFam} (hΦ : Φ.Down) (l : Loc) (A : Life) (u : Val) (k : Nat)
    (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN (T2H A)) (MFPost l A (famF A) (Qlend l)) k ls
      (lendE l) BM := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  have hFl : Φ.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_perform (T := T2H A) (en := yEntK A) (K := .seq .hole (wrL l))
    (by simp [Kont.HasHnd]) (by simp [T2H]) rfl rfl
    (compS_empty_left _) ⟨rfl, rfl⟩ (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local (T2H A)) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp_of_rwp (rwp_dump (rwp_M_antiFrame hΦ' hFl (ResU.comp_empty_right _) ?_))
  intro W X hW hX
  obtain rfl := eq_of_compS_empty_left hW
  obtain rfl := eq_of_compS_empty_left hX
  refine rwp_store ls' l u (Val.i32 5) _ ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, ?_⟩
  intro ρ₁ ρ₂ h₁ hc
  subst h₁
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨Val.i32 5, PMap.empty, inStratum_empty A, rfl, PMap.empty, PMap.empty,
    ResU.comp_empty_right _, ResU.comp_empty_right _, fun X hX => ?_⟩
  obtain rfl := eq_of_compS_empty_left hX
  refine ⟨noOwn_single_mut l, inStratum_empty A, fun w Y hY σ ⟨hσ, hF⟩ Z hZ => ?_⟩
  have hσ0 : σ = PMap.empty := hF
  subst hσ0
  obtain rfl := eq_of_compS_empty_left hY
  obtain rfl := ResU.CompS.functional hZ (ResU.comp_empty_right _)
  exact ⟨rfl, w, rfl⟩

/-- **A turn**, the lend by `erwp_M_frameK`. -/
theorem turn_okH {Φ : LocFam} (hΦ : Φ.Down) (A : Life) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IL s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN (T2H A)) (turnPostN IL QZ) k ls
      (.app (.app (.val fT) (.val s)) (.val nextV)) ρ := by
  obtain ⟨l, u, rfl, rfl⟩ := hI
  have hD := opTableN_down (T2H_down A)
  have hTP : (turnPostN IL QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc l)
      (.lam (.case (.var 0) (.seq (.seq Stage1.yE wrE) (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, Stage1.yE, wrE, wrL, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.lam, Val.loc, Val.storeV, Expr.val, Val.prim, Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, performE, opPayload, Val.pair, Val.i32,
      Val.unit, nextV, Val.inj₁, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (.seq Stage1.yE (wrL l)) (.inj₂ (.val (Val.loc l))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc l)))).plug (lendE l) := by
    simp [Expr.subst, Kont.plug, Stage1.yE, wrL, lendE, performE, opPayload, Val.pair, Val.i32,
      Val.unit, Val.loc, Val.storeV, Expr.val, Val.prim]
  rw [e₃]
  refine erwp_bind_le (Q' := Qlend l) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin (T2H_fin A) _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, w, rfl⟩
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, l, w, rfl, rfl⟩)
  · exact erwp_M_frameK (famF_down A) (T2H_lendOKK A) k k le_rfl ls (lendE l) u PMap.empty _
      PMap.empty _ (inStratum_empty A) (inStratum_empty _) (famF A k) (fun _ _ h => h) rfl
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) (lend_okH hΦ l A u k ls)

/-! ### The program -/

theorem body_okH (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN (T2H A)) QZ n [] LendProg.bodyL (PMap.empty : WRes) := by
  have hD := opTableN_down (T2H_down A)
  refine erwp_alloc Φ₀_down (opTableN_local (T2H A)) (.appR (.val (Val.lam
    (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0))))) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0)))) = iterateE fT (Val.loc l) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fT.1 = true from rfl) (Nat.zero_le _)]
  rw [e]
  exact erwp_iterate Φ₀_down (T2H_down A) (OpTabN.ctxClosed_of_fin (T2H_fin A) _) QZ_down rfl
    (I := IL) (en := tickEnt)
    (by simp [T2H, T1, Stage1.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IL_closed
    (fun k s ls ρ hI => turn_okH Φ₀_down A k s ls ρ hI) _ _ _ _ ⟨l, Val.i32 1, rfl, hcell⟩

/-- `hnd_Div rtH (hnd_Y yImm bodyL)`. -/
def progH : Expr := hndE DivRuntime.rtH (hndE yHI LendProg.bodyL)

theorem progH_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progH (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yHI Φ₀_down A n [] _ _ (body_okH A n))

/-- **The forest test, round 7's configuration.** The task holds a `mut` lend at `A` across `y`;
the scheduler resumes its continuation inside an `imm` lend of its own cell, opened after the
task's lend and at a lifetime below it, at a list `sameW` refuses; the resumed task ticks under
that lend and yields again inside it. Every configuration a run reaches is a value or steps, a
value only at the empty memory, and every `free` finds its cell. No fuel. -/
theorem progH_orDiverges : LoopAwait.OrDiverges (ℍ := ℍ) progH :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) (progH_ok (OrderDual.toDual 3))

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI.ForestHandlerProg

end
