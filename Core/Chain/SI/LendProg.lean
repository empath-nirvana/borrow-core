import Core.Chain.SI.LoopN
import Core.Chain.SI.Programs

/-!
# Unknown 1, the test: a `mut` lend live across a `yield`, under a scheduler that stores `κ`,
around a loop with no bound — `OrDiverges`, with no fuel, at `erwp` over Core's worlds

    progLend = hnd_Div rtH (                          -- the runtime: every tick answered next
                 hnd_Y yStore (                       -- the scheduler; y : 1 ↠^lin 1
                   (λc. iterate (fT, c)) (alloc 1)))  -- the cell, and the loop over it

    fT = λs. λb. case b { next → (y (); s := 5); inr s | close → () }

Each turn lends the cell `mut` to `y (); s := 5`: the lend is live across `y`, whose `κ` the
scheduler stores in a cell, takes back and resumes; after the resume the borrow writes, and the
lend ends. The lend is the logical Mut Frame (`erwp_M_frame`, `SI/StopFrameN.lean`): the term is
not cut at the `y`. `progLend_orDiverges`: every configuration a run reaches is a value or steps,
a value only at the empty memory, and every `free` finds its cell.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The tables -/

/-- `()`, owning nothing. -/
def unitP : Nat → List SRec → Val → WProp := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty

/-- *next*, owning nothing: the runtime never closes the loop. -/
def nextP : Nat → List SRec → Val → WProp := fun _ _ w ρ => w = nextV ∧ ρ = PMap.empty

/-- `tick : 1 ↠^lin Next`, resumed under `extF`. -/
def tickEnt : OpEntN := ⟨.lin, false, unitP, nextP, none, extF⟩

/-- `y : 1 ↠^lin 1`, resumed under `extF`. -/
def yEnt : OpEntN := ⟨.lin, false, unitP, unitP, none, extF⟩

/-- Under the scheduler: the tick. -/
def T1 : OpTabN := fun m i => if m = divEff ∧ i = 0 then some tickEnt else none

/-- Under both handlers: `y` and the tick. -/
def T2 : OpTabN := fun m i => if m = 6 ∧ i = 0 then some yEnt else T1 m i

theorem T1_cases {m i : UInt32} {en : OpEntN} (h : T1 m i = some en) :
    m = divEff ∧ i = 0 ∧ en = tickEnt := by
  unfold T1 at h
  split_ifs at h with h₁
  · exact ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩

theorem T2_cases {m i : UInt32} {en : OpEntN} (h : T2 m i = some en) :
    (m = 6 ∧ i = 0 ∧ en = yEnt) ∨ (m = divEff ∧ i = 0 ∧ en = tickEnt) := by
  unfold T2 at h
  split_ifs at h with h₁
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr (T1_cases h)

theorem ent_cases {m i : UInt32} {en : OpEntN} (h : T2 m i = some en) :
    en = yEnt ∨ en = tickEnt := by
  rcases T2_cases h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem T1_sub {m i : UInt32} {en : OpEntN} (h : T1 m i = some en) : T2 m i = some en := by
  obtain ⟨rfl, rfl, rfl⟩ := T1_cases h
  simp [T2, T1, Stage1.divEff_ne6]

theorem T2_down : T2.Down where
  pa := fun _ _ en h _ _ _ _ hA => by rcases ent_cases h with he | he <;> subst he <;> exact hA
  fin := fun _ _ en P h hP => by
    rcases ent_cases h with rfl | rfl <;> cases hP
  wcl := fun _ _ en h => by rcases ent_cases h with rfl | rfl <;> exact extF_left

theorem T1_down : T1.Down where
  pa := fun _ _ en h _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := T1_cases h; exact hA
  fin := fun _ _ en P h hP => by rw [(T1_cases h).2.2] at hP; cases hP
  wcl := fun _ _ en h => by rw [(T1_cases h).2.2]; exact extF_left

theorem empty_down : OpTabN.empty.Down where
  pa := fun _ _ _ h => by cases h
  fin := fun _ _ _ _ h => by cases h
  wcl := fun _ _ _ h => by cases h

theorem T2_fin : ∀ m i en, T2 m i = some en → en.fin = none := fun _ _ en h => by
  rcases ent_cases h with rfl | rfl <;> rfl

/-- **`T2` may be stopped at under a live lend at any lifetime**: both operations are
must-resume, resumed under `extF`, and pass nothing in or out. -/
theorem T2_lendOK (A : Life) : T2.LendOK A where
  entry := fun _ _ en h => by rcases ent_cases h with rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩
  pa := fun _ _ en h _ _ _ ρ hA => by
    rcases ent_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hA
      intro l ψ hl; simp at hl
  pb := fun _ _ en h _ _ _ ρ hB => by
    rcases ent_cases h with rfl | rfl <;>
    · obtain ⟨-, rfl⟩ := hB
      intro l ψ hl; simp at hl

/-! ### The clauses at `erwp` -/

/-- Owning nothing. -/
def QZ : PostN := fun _ _ _ ρ => ρ = PMap.empty

theorem QZ_down : QZ.Down := fun _ _ _ _ h => h

/-- `λx. x` returns its argument, owning nothing. -/
theorem erwp_idV {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down) {k : Nat}
    {ls : List SRec} {v : Val} {ρ : WRes} (h : ρ = PMap.empty) :
    erwp (ℍ := ℍ) Φ (opTableN T) QZ k ls (.app (.val Stage1.idV) (.val v)) ρ := by
  refine erwp_det hΦ (opTableN_down hTD) QZ_down
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 v (.var 0)) = v.1 := by simp [Expr.subst, Kont.plug]
  rw [e]
  exact erwp_val h

/-- **The runtime's clause** `λ(v, κ). κ.1 next`: two steps to the resume, the first paid. -/
theorem erwp_resumeCl {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down) {Q : PostN}
    (hQ : Q.Down) {w : Val} (hw : closedAt 0 w.1 = true) {k : Nat} {ls : List SRec}
    {v κ : Val} {ρ : WRes}
    (h : ∀ k', k' < k → erwp (ℍ := ℍ) Φ (opTableN T) Q k' ls
      (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w)) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (.app (.val (Stage1.resumeCl w)) (.pair (.val v) κ.1)) ρ := by
  cases k with
  | zero => exact erwp_zero
  | succ k₀ =>
  have e₀ : (.app (.val (Stage1.resumeCl w)) (.pair (.val v) κ.1) : Expr) =
      Kont.hole.plug (.app (.val (Stage1.resumeCl w)) (.val (Val.pair v κ))) := rfl
  rw [e₀]
  refine erwp_step (opTableN_local T) (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e₁ : Expr.subst 0 (Val.pair v κ)
      (.letpair (.var 0) (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val w))) =
      Kont.hole.plug (.letpair (.val (Val.pair v κ))
        (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val w))) := by
    simp [Kont.plug, Expr.subst, subst_closedAt _ _ hw (Nat.zero_le _), Val.inj₁, Val.unit]
  rw [e₁]
  refine erwp_det hΦ (opTableN_down hTD) hQ (fun μ => step1Only_plug (Head.letpair μ _ _ _) rfl .hole) ?_
  have e₂ : Expr.subst 0 v (Expr.subst 0 (κ.shift 1 0)
      (.app (.app (.var 0) (.val (Val.inj₁ .unit))) (.val w))) =
      Kont.hole.plug (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w)) := by
    simp only [Expr.subst, if_true, Val.val_shift, Kont.plug]
    rw [Expr.subst_shift 0 0 0 v _ le_rfl le_rfl, Expr.shift_zero,
      subst_closedAt _ _ hw (Nat.zero_le _), subst_closedAt _ _ hw (Nat.zero_le _)]
    rfl
  rw [e₂]
  exact h k₀ (by omega)

/-- **Storing `κ`** (`storeCl_steps` at `erwp`): `κ` put in a fresh cell, owned; the
allocation is paid. -/
theorem erwp_storeCl {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down) {Q : PostN}
    (hQ : Q.Down) {B : Expr} (hB : closedAt 1 B = true) {k : Nat} {ls : List SRec}
    {v κ : Val} {ρ : WRes}
    (h : ∀ ℓ' : Loc, (ptoOwn ℓ' κ ─⋆
      erwp (ℍ := ℍ) Φ (opTableN T) Q (k - 1) ls (B.subst 0 (Val.loc ℓ'))) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (.app (.val (Stage1.storeCl B)) (.pair (.val v) κ.1)) ρ := by
  have hL := opTableN_local T
  have hD := opTableN_down hTD
  have e₀ : (.app (.val (Stage1.storeCl B)) (.pair (.val v) κ.1) : Expr) =
      Kont.hole.plug (.app (.val (Stage1.storeCl B)) (.val (Val.pair v κ))) := rfl
  rw [e₀]
  refine erwp_det hΦ hD hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e₁ : Expr.subst 0 (Val.pair v κ)
      (.letpair (.var 0) (.app (.val (Val.lam B)) (.app (.val (.prim .alloc)) (.var 0)))) =
      Kont.hole.plug (.letpair (.val (Val.pair v κ))
        (.app (.val (Val.lam B)) (.app (.val (.prim .alloc)) (.var 0)))) := by
    simp [Kont.plug, Expr.subst, subst_closedAt _ _ hB (by omega : 1 ≤ 3), Val.lam]
  rw [Kont.plug_hole, e₁]
  refine erwp_det hΦ hD hQ (fun μ => step1Only_plug (Head.letpair μ _ _ _) rfl .hole) ?_
  have e₂ : Expr.subst 0 v (Expr.subst 0 (κ.shift 1 0)
      (.app (.val (Val.lam B)) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val (Val.lam B)) .hole).plug (.app (.val (.prim .alloc)) (.val κ)) := by
    simp only [Expr.subst, if_true, Val.val_shift, Kont.plug, Val.val_lam]
    rw [Expr.subst_shift 0 0 0 v _ le_rfl le_rfl, Expr.shift_zero,
      subst_closedAt _ _ hB (by omega : 1 ≤ 1), subst_closedAt _ _ hB (by omega : 1 ≤ 1)]
    rfl
  rw [Kont.plug_hole, e₂]
  refine erwp_alloc hΦ hL _ κ (fun ℓ' σ₁ σ₂ hcell hc => ?_)
  refine erwp_det hΦ hD hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  exact h ℓ' σ₁ σ₂ hcell hc

/-- **The scheduler's clause** `λ(v, κ). (λc. (free c).1 ()) (alloc κ)`: `κ` stored in a fresh
cell, taken back and resumed; the allocation and the release are paid. -/
theorem erwp_clStore {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down) {Q : PostN}
    (hQ : Q.Down) {k : Nat} {ls : List SRec} {v κ : Val} {ρ : WRes}
    (h : ∀ k', k' < k → erwp (ℍ := ℍ) Φ (opTableN T) Q k' ls
      (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val .unit)) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (.app (.val Stage1.clStore) (.pair (.val v) κ.1)) ρ := by
  have hL := opTableN_local T
  cases k with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_storeCl hΦ hTD hQ rfl (fun ℓ' σ₁ σ₂ hcell hc => ?_)
  have e : Expr.subst 0 (Val.loc ℓ')
      (.app (.app (freeE (.var 0)) (.val (Val.inj₁ .unit))) (.val .unit)) =
      (Kont.appL (Kont.appL .hole (Val.inj₁ .unit)) .unit).plug (freeE (.val (Val.loc ℓ'))) := by
    simp [Expr.subst, Kont.plug, freeE, Val.inj₁, Val.unit, Val.loc]
  rw [e]
  refine erwp_free hΦ hL _ ℓ' κ ⟨σ₁, ρ, ResU.CompS.comm hc, hcell, ?_⟩
  exact h _ (by omega)

/-! ### The handlers -/

/-- `hnd_Y yStore`: the scheduler, `y` must-resume. -/
def yH : Val := hndVal 6 (qualsVal [.lin]) Stage1.idV (Val.pair Stage1.clStore .unit)

theorem erwp_yH {Φ : LocFam} (hΦ : Φ.Down) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T2) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T1) QZ n ls (hndE yH e) ρ := by
  refine erwp_handle hΦ T2 T1 T2_down T1_down 6 (fun m i hm => by simp [T2, hm]) _ _ _ QZ QZ
    QZ_down ?_ (fun _ => none) (fun _ en _ _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV hΦ T1_down hv) ?_
  · intro i en hT _
    rcases T2_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · exact Stage1.capTag_one .lin
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT
    rcases T2_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · refine ⟨Stage1.clStore, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
        fun h => by cases h⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      refine erwp_clStore hΦ T1_down QZ_down fun k' hk' => ?_
      exact (hK ls (extF_refl ls _) k' hk').1 Val.unit PMap.empty ρ ⟨rfl, rfl⟩
        (ResU.comp_empty_right ρ)
    · exact absurd h6.symm Stage1.divEff_ne6

theorem nextV_closed : closedAt 0 nextV.1 = true := rfl

theorem erwp_rtH {Φ : LocFam} (hΦ : Φ.Down) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T1) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) QZ n ls (hndE DivRuntime.rtH e) ρ := by
  refine erwp_handle hΦ T1 OpTabN.empty T1_down empty_down divEff
    (fun m i hm => by simp [T1, hm, OpTabN.empty]) _ _ _ QZ QZ QZ_down ?_ (fun _ => none)
    (fun _ en _ _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV hΦ empty_down hv) ?_
  · intro i en hT _
    obtain ⟨-, rfl, rfl⟩ := T1_cases hT
    exact Stage1.capTag_one .lin
  · intro i en hT
    obtain ⟨-, rfl, rfl⟩ := T1_cases hT
    refine ⟨DivRuntime.rtC, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
      fun h => by cases h⟩
    obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, -, hK⟩ := hsep
    obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
    rw [Stage1.rtC_eq]
    refine erwp_resumeCl hΦ empty_down QZ_down nextV_closed fun k' hk' => ?_
    exact (hK ls (extF_refl ls _) k' hk').1 nextV PMap.empty ρ ⟨rfl, rfl⟩
      (ResU.comp_empty_right ρ)

/-! ### The turn: a `mut` lend across `y` -/

/-- `s := 5`, `s` the loop's state, under `λs. λb. case b {x. …}`. -/
def wrE : Expr := .app (.app (.val (.prim .store)) (.var 2)) (.val (Val.i32 5))

/-- `λs. λb. case b {next → (y (); s := 5); inr s | close → ()}`. -/
def fT : Val :=
  Val.lam (.lam (.case (.var 0) (.seq (.seq Stage1.yE wrE) (.inj₂ (.var 2))) (.val .unit)))

/-- `ℓ := 5`. -/
def wrL (l : Loc) : Expr := .app (.val (Val.storeV (Val.loc l))) (.val (Val.i32 5))

/-- The lent computation: `y (); ℓ := 5`. -/
def lendE (l : Loc) : Expr := .seq Stage1.yE (wrL l)

/-- The cell's family: an integer, owning nothing. -/
def famF (A : Life) : Nat → Val → SPropS Loc Val A := fun _ _ r => r.1 = PMap.empty

theorem famF_down (A : Life) : DownFam A (famF A) := fun _ _ _ h => h

theorem inStratum_empty (A : Life) : ResU.InStratum A (PMap.empty : WRes) :=
  fun _ _ h => by rw [PMap.empty_get] at h; cases h

/-- The lend's end: `()`, and the cell owned again. -/
def Qlend (l : Loc) : PostN := fun _ _ v ρ => v = Val.unit ∧ ∃ w, ptoOwn l w ρ

/-- `rwpG_garbage` at `rwp`: the final resource set aside as garbage when it owns nothing. -/
theorem rwp_dump {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwp (ℍ := ℍ) Φ (fun k ls' v X => NoOwn X ∧ Q k ls' v PMap.empty) n ls e ρ) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  rw [rwp_iff_rwpG] at h ⊢
  refine rwpG_garbage (rwpG_mono (fun k ls' t X ⟨v, hv, hno, hq⟩ =>
    ⟨PMap.empty, X, compS_empty_left X, hno, v, hv, hq⟩) h)

theorem noOwn_single_mut (l : Loc) {A : Life} {v : Val} {χ : WRes} {h : χ.InStratum A}
    {P : Val → SPropS Loc Val A} {hw : P v ⟨χ, h⟩} :
    NoOwn (ResU.single l (CellU.mutOf A v χ h P hw)) := by
  refine noOwn_iff.mpr fun m ψ hm => ?_
  by_cases hml : m = l
  · subst hml
    rw [ResU.single_get_self] at hm
    cases Option.some.inj hm
    rw [CellU.kind_mutOf]
    exact fun h => Kind.noConfusion h
  · rw [ResU.single_get_ne _ hml] at hm; exact absurd hm (by simp)

/-- **The borrowed computation**: from the borrow alone, `y ()` stops with the borrow live in
its continuation; after the resume the borrow writes through the Mut Anti-Frame (6.66 at the
index) and is released. -/
theorem lend_ok {Φ : LocFam} (hΦ : Φ.Down) (l : Loc) (A : Life) (u : Val) (k : Nat)
    (ls : List SRec) (BM : WRes)
    (hBM : ResU.CompS PMap.empty (ResU.single l (CellU.mutOf A u PMap.empty (inStratum_empty A)
      (famF A k) rfl)) BM) :
    erwp (ℍ := ℍ) (Φ.set l A (famF A)) (opTableN T2) (MFPost l A (famF A) (Qlend l)) k ls
      (lendE l) BM := by
  have hΦ' := LocFam.set_down (l := l) hΦ (famF_down A)
  have hFl : Φ.set l A (famF A) l = some ⟨A, famF A⟩ := by simp [LocFam.set]
  obtain rfl := eq_of_compS_empty_left hBM
  refine erwp_perform (T := T2) (en := yEnt) (K := .seq .hole (wrL l)) (by simp [Kont.HasHnd]) (by simp [T2]) rfl rfl
    (compS_empty_left _) ⟨rfl, rfl⟩ (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
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

/-- The loop's invariant: the state is a location the turn owns. -/
def IL : Val → WProp := fun s ρ => ∃ l u, s = Val.loc l ∧ ptoOwn l u ρ

theorem IL_closed : ∀ s ρ, IL s ρ → closedAt 0 s.1 = true := by
  rintro s ρ ⟨l, u, rfl, -⟩
  rfl

/-- **A turn**: three steps to `(y (); ℓ := 5); inr ℓ`, the lend by `erwp_M_frame` around
`y (); ℓ := 5`, then `inr ℓ`. -/
theorem turn_ok {Φ : LocFam} (hΦ : Φ.Down) (A : Life) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IL s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (turnPostN IL QZ) k ls
      (.app (.app (.val fT) (.val s)) (.val nextV)) ρ := by
  obtain ⟨l, u, rfl, rfl⟩ := hI
  have hD := opTableN_down T2_down
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
  refine erwp_bind_le (Q' := Qlend l) hΦ _ (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches])
    (OpTabN.ctxClosed_of_fin T2_fin _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨rfl, w, rfl⟩
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc l)) (.inr ⟨Val.loc l, rfl, l, w, rfl, rfl⟩)
  · -- the lend
    exact erwp_M_frame (famF_down A) (T2_lendOK A) k k le_rfl ls (lendE l) u PMap.empty _
      PMap.empty _ (inStratum_empty A) (inStratum_empty _) (famF A k) (fun _ _ h => h) rfl
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) (lend_ok hΦ l A u k ls)

/-! ### The program -/

/-- `(λc. iterate (fT, c)) (alloc 1)`. -/
def bodyL : Expr :=
  .app (.val (Val.lam (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0)))))
    (.app (.val (.prim .alloc)) (.val (Val.i32 1)))

/-- `hnd_Div rtH (hnd_Y yStore bodyL)`. -/
def progLend : Expr := hndE DivRuntime.rtH (hndE yH bodyL)

/-- The empty location typing. -/
def Φ₀ : LocFam := fun _ => none

theorem Φ₀_down : Φ₀.Down := fun _ _ _ h => by cases h

theorem body_ok (A : Life) (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN T2) QZ n [] bodyL (PMap.empty : WRes) := by
  have hD := opTableN_down T2_down
  refine erwp_alloc Φ₀_down (opTableN_local T2) (.appR (.val (Val.lam
    (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0))))) .hole) (Val.i32 1)
    (fun l σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 (Val.loc l)
      (.app (.val (.prim .iterate)) (.pair (.val fT) (.var 0)))) = iterateE fT (Val.loc l) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fT.1 = true from rfl) (Nat.zero_le _)]
  rw [e]
  exact erwp_iterate Φ₀_down T2_down (OpTabN.ctxClosed_of_fin T2_fin _) QZ_down rfl (I := IL) (en := tickEnt)
    (by simp [T2, T1, Stage1.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IL_closed
    (fun k s ls ρ hI => turn_ok Φ₀_down A k s ls ρ hI) _ _ _ _ ⟨l, Val.i32 1, rfl, hcell⟩

theorem progLend_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progLend (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yH Φ₀_down n [] _ _ (body_ok 0 n))

/-- **Unknown 1, the test.** A cell lent `mut` across `y` on every turn of a loop with no
bound, under a scheduler that stores the continuation in a cell and resumes it, under the
runtime's `Div` handler: every configuration a run reaches is a value or steps, a value only at
the empty memory, and every `free` finds its cell. No fuel. -/
theorem progLend_orDiverges : OrDiverges (ℍ := ℍ) progLend :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progLend_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.LendProg

end
