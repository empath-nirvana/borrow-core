import DtorUnwind.SI.CaptureScope
import DtorUnwind.SI.CaptureAdequacy

/-!
# The test: a task spawned inside an `imm` lend borrows from its parent across `y`; a scheduler
stores both; the lend ends after the join — `OrDiverges`, with no fuel

    main = let c = alloc () in
           r₁ = hnd_P (spawn (λ_. y (); !c); join(c))   -- the parent, the lend open around it
           (f, κ_p) from r₁                             -- the spawn: both stored in cells
           r₂ = hnd_C (f ())                            -- the child: stops at `y`, κ_c stored
           r₃ = κ_p ()                                  -- the parent runs to the join, κ′_p stored
           r₄ = κ_c ()                                  -- the child reads `!c` and returns
           r₅ = κ′_p ()                                 -- the parent: the lend ends
           free c

The parent's lend of `c` is the logical scope (`cerwp_scope`) around `spawn f; join(c)`: entered
before the spawn, left open at the spawn and the join (the child holds the borrow, so nothing is
folded), ended at the join's resume. The child holds the borrow across its `y`, stored by the
scheduler as `κ_c`, while the parent's continuation, with the lend open in it, is stored as
`κ_p`. The scheduler hands the child's borrow back in the join's answer, and resumes the parent
with nothing at `c` outside it (`joinFd`).

Each handler hands its continuation out (`cerwp_gen`); the scheduler's code dispatches on the
event, an unexpected one diverging.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI.CrossProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ccatchE kappaC)
open BoCa.Lifetime (LSub)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The child -/

/-- `y ()`, the child's operation. -/
def yE : Expr := performE (.val (opPayload 8 0 Val.unit))

/-- `!ℓ`. -/
def ldL (l : Loc) : Expr := .app (.val (.prim .load)) (.val (Val.loc l))

/-- `λ_. y (); !ℓ`. -/
def fchild (l : Loc) : Val := Val.lam (.seq yE (ldL l))

/-- The borrows a task leaves: none, or one `imm` cell with an empty witness. -/
def LeftV (ρ : WRes) : Prop :=
  ρ = PMap.empty ∨ ∃ (m : Loc) (s : LSet) (u : Val) (h : ResU.InStratum s.join (PMap.empty : WRes)),
    ρ = ResU.single m (CellU.immOf s u PMap.empty h)

/-- What a cancel of the child leaves: `()`, its borrows, no records. -/
def Qleft : PostCV := fun _ _ O v ρ => O = [] ∧ v = Val.unit ∧ LeftV ρ

/-- What the child returns: its borrows, no records. -/
def Qchild : PostCV := fun _ _ O _ ρ => O = [] ∧ LeftV ρ

/-- The child's cancel obligation: the cancel run caught at `ccatch`. -/
def Pcan : Nat → List SRec → Expr → WProp := fun k ls e ρ =>
  ∀ F, cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qleft F k ls [] (ccatchE e) ρ

/-- `y : 1 ↠^cancel 1`. -/
def yEnt : OpEntC :=
  { q := .cancel, abort := false, PA := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty,
    PB := fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, fin := some (Pcan (ℍ := ℍ)),
    wc := extF, fd := fun _ _ => True,
    PBv := fun _ _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty }

/-- The child's table. -/
def TC : OpTabC := fun m i => if m = 8 ∧ i = 0 then some (yEnt (ℍ := ℍ)) else none

theorem TC_some {m i : UInt32} {en : OpEntC} (h : TC (ℍ := ℍ) m i = some en) :
    m = 8 ∧ i = 0 ∧ en = yEnt (ℍ := ℍ) := by
  unfold TC at h
  split_ifs at h with h₁
  exact ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩

theorem Qleft_down : Qleft.Down := fun _ _ _ _ _ h => h
theorem Qchild_down : Qchild.Down := fun _ _ _ _ _ h => h

theorem TC_down : (TC (ℍ := ℍ)).Down where
  pa := fun _ _ en h _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := TC_some h; exact hA
  fin := fun _ _ en P h hP k ls e ρ hk => by
    obtain ⟨-, -, rfl⟩ := TC_some h
    cases hP
    exact fun F => cerwp_le (opTableC_local _) (opTableC_down opTabC_emptyC_down) Qleft_down
      (Nat.le_succ k) (hk F)

theorem leftV_single {m : Loc} {s : LSet} {u : Val} {h : ResU.InStratum s.join (PMap.empty : WRes)} :
    LeftV (ResU.single m (CellU.immOf s u PMap.empty h)) := .inr ⟨m, s, u, h, rfl⟩

/-- **The child**: from one borrow, `y` stops with the borrow in the continuation's share; resumed,
it reads through the borrow and returns it; cancelled, the cancel run returns it. -/
theorem child_ok (l : Loc) {s : LSet} {u : Val} {h : ResU.InStratum s.join (PMap.empty : WRes)}
    (F : WRes → Prop) (n : Nat) (ls : List SRec) :
    cerwp (ℍ := ℍ) (opTableC (TC (ℍ := ℍ))) Qchild F n ls []
      (.app (.val (fchild l)) (.val Val.unit))
      (ResU.single l (CellU.immOf s u PMap.empty h)) := by
  have hL := opTableC_local (TC (ℍ := ℍ))
  have hD := opTableC_down (TC_down (ℍ := ℍ))
  refine cerwp_det hD Qchild_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.seq yE (ldL l))) =
      (Kont.seq .hole (ldL l)).plug (performE (.val (opPayload 8 0 Val.unit))) := by
    simp [Expr.subst, Kont.plug, yE, ldL, performE, opPayload, Val.pair, Val.i32, Val.unit,
      Val.loc, Expr.val, Val.prim]
  rw [e]
  refine cerwp_perform (T := TC (ℍ := ℍ)) (en := yEnt (ℍ := ℍ)) (Kont.seq .hole (ldL l))
    (by simp [Kont.HasHnd]) (by simp [TC]) rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun hq => by simp [yEnt] at hq) (fun ls' _ k' hk' w σ₁ σ₂ hB hc => ?_)
    (fun ls' _ _ P hP => ?_)
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
    refine cerwp_det hD Qchild_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact cerwp_loadI hL .hole l (ResU.comp_empty_right _)
      (cerwp_val ⟨rfl, leftV_single⟩)
  · cases hP
    intro F'
    show cerwp (ℍ := ℍ) _ _ _ _ _ _ (ccatchE ((Kont.seq .hole (ldL l)).dead.plug
      (raiseE (.val (cancelVal none))))) _
    refine cerwp_det (opTableC_down opTabC_emptyC_down) Qleft_down
      (fun μ => step1Only_plug (Head.cancel μ (Kont.seq .hole (ldL l)).dead
        (by simp [Kont.dead, Kont.Catches])) rfl .hole) ?_
    exact cerwp_val ⟨rfl, rfl, leftV_single⟩

/-! ### The parent -/

/-- What `spawn` passes: one borrow, and a closure that runs as the child from it. -/
def PAspawn : Nat → List SRec → Val → WProp := fun k _ f ρ =>
  ∃ (m : Loc) (s : LSet) (u : Val) (h : ResU.InStratum s.join (PMap.empty : WRes)),
    ρ = ResU.single m (CellU.immOf s u PMap.empty h) ∧
    ∀ k', k' ≤ k → ∀ ls' F, cerwp (ℍ := ℍ) (opTableC (TC (ℍ := ℍ))) Qchild F k' ls' []
      (.app (.val f) (.val Val.unit)) ρ

/-- `spawn : (1 → 1) ↠^lin 1`, the borrow passed out. -/
def spawnEnt : OpEntN :=
  { q := .lin, abort := false, PA := PAspawn (ℍ := ℍ),
    PB := fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, fin := none, wc := extF }

/-- The body's table. -/
def TPin : OpTabN := fun m i => if m = 7 ∧ i = 0 then some (spawnEnt (ℍ := ℍ)) else none

/-- The parent's table: `spawn`, and the join. -/
def TP : OpTabC := fun m i =>
  if m = 7 ∧ i = 0 then some (liftEnt (spawnEnt (ℍ := ℍ)))
  else if m = 7 ∧ i = 1 then some joinEnt else none

theorem TPin_some {m i : UInt32} {en : OpEntN} (h : TPin (ℍ := ℍ) m i = some en) :
    m = 7 ∧ i = 0 ∧ en = spawnEnt (ℍ := ℍ) := by
  unfold TPin at h
  split_ifs at h with h₁
  exact ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩

theorem TP_some {m i : UInt32} {en : OpEntC} (h : TP (ℍ := ℍ) m i = some en) :
    (m = 7 ∧ i = 0 ∧ en = liftEnt (spawnEnt (ℍ := ℍ))) ∨ (m = 7 ∧ i = 1 ∧ en = joinEnt) := by
  unfold TP at h
  split_ifs at h with h₁ h₂
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr ⟨h₂.1, h₂.2, (Option.some.inj h).symm⟩

theorem TP_tabs : ScopeTabs (TPin (ℍ := ℍ)) (TP (ℍ := ℍ)) 7 1 where
  inner := fun m i en h => by
    obtain ⟨rfl, rfl, rfl⟩ := TPin_some h
    exact ⟨rfl, rfl, rfl, fun _ _ _ _ hB => hB.2, by simp [TP]⟩
  join := by simp [TP]

theorem TP_down : (TP (ℍ := ℍ)).Down where
  pa := fun _ _ en h k ls v ρ hA => by
    rcases TP_some h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · obtain ⟨m, s, u, hs, e, hk⟩ := hA
      exact ⟨m, s, u, hs, e, fun k' hk' => hk k' (by omega)⟩
    · exact hA
  fin := fun _ _ en P h hP => by
    rcases TP_some h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> cases hP

/-- `spawn (λ_. y (); !ℓ)`. -/
def spawnE (l : Loc) : Expr := performE (.val (opPayload 7 0 (fchild l)))

/-- The parent: `spawn (λ_. y (); !ℓ); join(ℓ)`, the lend open around it. -/
def parentE (l : Loc) : Expr := (seqK 7 1 l).plug (spawnE l)

/-- The body's postcondition: `()`, holding its copy of the borrow or nothing. -/
def Q₀ (l : Loc) (A : Life) : PostN := fun _ _ w ρ =>
  w = Val.unit ∧ (ρ = viewA l Val.unit A ∨ ρ = PMap.empty)

/-- The parent's postcondition: `()`, the cell owned again, no records. -/
def Qsc (l : Loc) : PostCV := fun _ _ O w ρ =>
  w = Val.unit ∧ ρ = ResU.single l (CellU.ownOf Val.unit) ∧ ∀ q, q ∉ O

theorem Qsc_down (l : Loc) : (Qsc l).Down := fun _ _ _ _ _ h => h

/-- The empty location typing. -/
def Φe : LocFam := fun _ => none

/-- **The body**: `spawn f` passes one copy of the borrow to the child and keeps one. -/
theorem body_ok (l : Loc) (A : Life) (n : Nat) (ls : List SRec) :
    erwp0 (ℍ := ℍ) Φe (opTableN (TPin (ℍ := ℍ))) (Q₀ l A) n ls (spawnE l) (viewA l Val.unit A) := by
  refine erwp0_perform (T := TPin (ℍ := ℍ)) (en := spawnEnt (ℍ := ℍ)) .hole (by simp [Kont.HasHnd])
    (by simp [TPin]) rfl rfl (compS_imm_dup l _ Val.unit PMap.empty (inStratumE A))
    ⟨l, _, Val.unit, inStratumE A, rfl, fun k' _ ls' F => child_ok l F k' ls'⟩
    (fun ls' _ k' _ w σ₁ σ₂ hB hc => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  exact erwp0_val ⟨rfl, .inl rfl⟩

/-- The empty lifetime substitution. -/
def δ₀ : LSub := ⟨[]⟩

/-- **The parent**: the lend scope around the body. From `ℓ ↦ own(())`, owning no record: the
parent returns `()` with the cell owned again and no record left. -/
theorem parent_ok (l : Loc) (A : Life) (F : WRes → Prop) (n : Nat) (ls : List SRec) :
    cerwp (ℍ := ℍ) (opTableC (TP (ℍ := ℍ))) (Qsc l) F n ls [] (parentE l)
      (ResU.single l (CellU.ownOf Val.unit)) := by
  have hshape : vShape .unk δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
  have hadm : AdmWf .unk δ₀ := fun _ h => h.elim
  obtain ⟨ds, hds⟩ := lineage_list (r := recP l Val.unit .unk δ₀) hshape hadm
    (ExW.empty_of_all_imm (fun _ _ h => by simp [recP, PMap.empty_get] at h))
  refine cerwp_scope (Φ := Φe) (Q₀ := Q₀ l A) l Val.unit .unk δ₀ hadm hshape A 7 1 (TP_down (ℍ := ℍ))
    (TP_tabs (ℍ := ℍ)) (Qsc_down l) (fun _ _ _ _ h => h.1) [] ?_ n F ls (spawnE l)
    PMap.empty _ (inStratumE A) (ResU.comp_empty_right _) (ResU.valid_single_own l _) ds hds
    (fun BI hBI => ?_)
  · intro k k₀ ls₀ ls' O' w₀ π ρout _ hq hO' hc
    obtain ⟨-, hπ | hπ⟩ := hq
    · subst hπ
      rw [viewA_del] at hc
      obtain rfl := eq_of_compS_empty_left hc
      exact ⟨rfl, rfl, fun q hq => by
        obtain ⟨h₁, h₂⟩ := (hO' q).mp hq
        rcases List.mem_cons.mp h₁ with h | h
        · exact h₂ h
        · simp at h⟩
    · subst hπ
      have : ResU.del (PMap.empty : WRes) l = PMap.empty := by
        refine PMap.ext fun m => ?_
        by_cases hm : m = l
        · subst hm; rw [ResU.del_get_self]; rfl
        · rw [ResU.del_get_ne _ hm]
      rw [this] at hc
      obtain rfl := eq_of_compS_empty_left hc
      exact ⟨rfl, rfl, fun q hq => by
        obtain ⟨h₁, h₂⟩ := (hO' q).mp hq
        rcases List.mem_cons.mp h₁ with h | h
        · exact h₂ h
        · simp at h⟩
  · obtain rfl := eq_of_compS_empty_left hBI
    exact body_ok l A n _

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI.CrossProg

end
