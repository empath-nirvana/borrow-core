import Core.Chain.SI.CaptureScope
import Core.Chain.SI.CaptureAdequacy

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

namespace BoCa.Fig16.LogRel.Core.Chain.SI.CrossProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
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

/-- `y : 1 ↠^cancel 1`, resumed at any list. -/
def yEnt : OpEntC :=
  { q := .cancel, abort := false, PA := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty,
    PB := fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, fin := some (Pcan (ℍ := ℍ)),
    wc := fun _ _ _ => True, fd := fun _ _ => True,
    PBv := fun _ _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, oc := fun O => O = [] }

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
    (by simp [Kont.HasHnd]) (by simp [TC]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
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

/-- `spawn : (1 → 1) ↠^lin 1`, the borrow passed out, resumed at any list. -/
def spawnEnt : OpEntN :=
  { q := .lin, abort := false, PA := PAspawn (ℍ := ℍ),
    PB := fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, fin := none, wc := fun _ _ _ => True }

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
    exact ⟨rfl, rfl, fun _ _ _ _ _ _ _ => trivial, fun _ _ _ _ hB => hB.2, by simp [TP]⟩
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

/-! ### The handlers: each hands the stopped task out, its continuation stored in a cell -/

/-- `alloc e`. -/
def allocE (e : Expr) : Expr := .app (.val (.prim .alloc)) e

/-- `κ` as a value. -/
def kV (b : Bool) (ℓ : Loc) (H : Val) (K : Kont) : Val := ⟨kappaC b ℓ H K, IsVal.lam⟩

/-- The answer clause: `λv. inj₂ v`. -/
def retV : Val := Val.lam (.inj₂ (.var 0))

/-- `spawn`'s clause: `λ(f, κ). inj₁ (inj₁ (alloc f, alloc κ))`. -/
def c₀ : Val :=
  Val.lam (.letpair (.var 0) (.inj₁ (.inj₁ (.pair (allocE (.var 1)) (allocE (.var 0))))))

/-- The join's clause: `λ(_, κ). inj₁ (inj₂ (alloc κ))`. -/
def c₁ : Val := Val.lam (.letpair (.var 0) (.inj₁ (.inj₂ (allocE (.var 0)))))

/-- `y`'s clause: `λ(_, κ). inj₁ (alloc κ)`. -/
def cy : Val := Val.lam (.letpair (.var 0) (.inj₁ (allocE (.var 0))))

/-- The parent's handler. -/
def HP : Val := hndVal 7 (qualsVal [.lin, .lin]) retV (Val.pair c₀ (Val.pair c₁ Val.unit))

/-- The child's handler. -/
def HC : Val := hndVal 8 (qualsVal [.cancel]) retV (Val.pair cy Val.unit)

/-- A continuation stored in the cell `ℓ_κ`: `κ` owns its cell `ℓ_c`, and its share resumes the
handled computation at every answer, owning `O`, under `F` and the entry's frame condition. -/
def KapStored (Tin : OpTabC) (Qin : PostCV) (H : Val) (en : OpEntC) (F : WRes → Prop)
    (k : Nat) (ls : List SRec) (O : List FrameRec) (v : Val) (ℓκ : Loc) : WProp := fun ρ =>
  ∃ (ℓc : Loc) (K : Kont) (ρk ρ₁ : WRes) (k₀ : Nat), k ≤ k₀ ∧
    ResU.CompS (ResU.single ℓκ (CellU.ownOf (kV (cellCancel en.q) ℓc H K)))
      (ResU.single ℓc (CellU.ownOf Val.unit)) ρ₁ ∧
    ResU.CompS ρ₁ ρk ρ ∧
    contShareC en F k₀ ls O K v (cerwpC (ℍ := ℍ) (opTableC Tin) Qin k₀) ρk

/-- What a run of the parent under `HP` hands the scheduler. -/
def QP (l : Loc) (F : WRes → Prop) : PostCV := fun k ls O r ρ =>
  (∃ v : Val, r = Val.inj₂ v ∧ Qsc l k ls O v ρ) ∨
  (∃ (ℓf ℓκ : Loc) (f : Val) (ρ₁ ρa ρ₂ : WRes),
    r = Val.inj₁ (Val.inj₁ (Val.pair (Val.loc ℓf) (Val.loc ℓκ))) ∧
    ResU.CompS (ResU.single ℓf (CellU.ownOf f)) ρa ρ₁ ∧ PAspawn (ℍ := ℍ) k ls f ρa ∧
    ResU.CompS ρ₁ ρ₂ ρ ∧
    KapStored (ℍ := ℍ) (TP (ℍ := ℍ)) (Qsc l) HP (liftEnt (spawnEnt (ℍ := ℍ))) F k ls O f ℓκ ρ₂) ∨
  (∃ (ℓκ m : Loc), r = Val.inj₁ (Val.inj₂ (Val.loc ℓκ)) ∧
    KapStored (ℍ := ℍ) (TP (ℍ := ℍ)) (Qsc l) HP joinEnt F k ls O (Val.loc m) ℓκ ρ)

/-- What a run of the child under `HC` hands the scheduler. -/
def QC (F : WRes → Prop) : PostCV := fun k ls O r ρ =>
  (∃ v : Val, r = Val.inj₂ v ∧ Qchild k ls O v ρ) ∨
  (∃ ℓκ : Loc, r = Val.inj₁ (Val.loc ℓκ) ∧ O = [] ∧
    KapStored (ℍ := ℍ) (TC (ℍ := ℍ)) Qchild HC (yEnt (ℍ := ℍ)) F k ls O Val.unit ℓκ ρ)

theorem kapStored_down {Tin : OpTabC} {Qin : PostCV} {H : Val} {en : OpEntC}
    {F : WRes → Prop} {k : Nat} {ls : List SRec} {O : List FrameRec} {v : Val} {ℓκ : Loc}
    {ρ : WRes} (h : KapStored (ℍ := ℍ) Tin Qin H en F (k + 1) ls O v ℓκ ρ) :
    KapStored (ℍ := ℍ) Tin Qin H en F k ls O v ℓκ ρ := by
  obtain ⟨ℓc, K, ρk, ρ₁, k₀, hk, h₁, h₂, h₃⟩ := h
  exact ⟨ℓc, K, ρk, ρ₁, k₀, by omega, h₁, h₂, h₃⟩

theorem QP_down (l : Loc) (F : WRes → Prop) : (QP (ℍ := ℍ) l F).Down := by
  intro k ls O r ρ h
  rcases h with h | ⟨ℓf, ℓκ, f, ρ₁, ρa, ρ₂, e, h₁, ⟨m, s, u, hs, ea, hk⟩, h₃, h₄⟩ | ⟨ℓκ, m, e, h⟩
  · exact .inl h
  · exact .inr (.inl ⟨ℓf, ℓκ, f, ρ₁, ρa, ρ₂, e, h₁, ⟨m, s, u, hs, ea, fun k' hk' => hk k' (by omega)⟩,
      h₃, kapStored_down h₄⟩)
  · exact .inr (.inr ⟨ℓκ, m, e, kapStored_down h⟩)

theorem QC_down (F : WRes → Prop) : (QC (ℍ := ℍ) F).Down := by
  intro k ls O r ρ h
  rcases h with h | ⟨ℓκ, e, hO, h⟩
  · exact .inl h
  · exact .inr ⟨ℓκ, e, hO, kapStored_down h⟩

theorem clauseAt0 (c r : Val) : clauseAt (Val.pair c r).1 (0 : UInt32).toNat = some c := by
  simp [clauseAt, Val.pair, c.2]

theorem clauseAt1 (c c' r : Val) :
    clauseAt (Val.pair c (Val.pair c' r)).1 (1 : UInt32).toNat = some c' := by
  simp [clauseAt, Val.pair, c'.2]

/-- `κ` after the clause's `letpair`: the substitution leaves it. -/
theorem kV_subst (κ f : Val) : Expr.subst 0 f (Expr.shift 1 0 κ.1) = κ.1 := by
  rw [Expr.subst_shift 0 0 0 f _ le_rfl le_rfl, Expr.shift_zero]

/-- **The answer clause** `λv. inj₂ v`: one step. -/
theorem cerwp_retV {Q : PostCV} (hQ : Q.Down) {F : WRes → Prop} {k : Nat} {ls : List SRec}
    {O : List FrameRec} {v : Val} {ρ : WRes} (h : Q k ls O (Val.inj₂ v) ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Q F k ls O (.app (.val retV) (.val v)) ρ := by
  refine cerwp_det (opTableC_down opTabC_emptyC_down) hQ
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 v (.inj₂ (.var 0))) = (Val.inj₂ v).1 := by
    simp [Expr.subst, Kont.plug, Val.inj₂]
  rw [e]
  exact cerwp_val h

/-- Five resources rearranged: `((a ● k) ● c) ● f ● κ = (f ● a) ● ((κ ● c) ● k)`. -/
theorem rearr5 {a k c f κ ak ρ ρ' ρ'' : WRes} (hak : ResU.CompS a k ak) (hc : ResU.CompS ak c ρ)
    (h1 : ResU.CompS ρ f ρ') (h2 : ResU.CompS ρ' κ ρ'') :
    ∃ ρ₁ ρ₂ ρ₃, ResU.CompS f a ρ₁ ∧ ResU.CompS κ c ρ₃ ∧ ResU.CompS ρ₃ k ρ₂ ∧
      ResU.CompS ρ₁ ρ₂ ρ'' := by
  obtain ⟨x1, hx1, h⟩ := compS_reassoc hak hc
  obtain ⟨x2, hx2, h'⟩ := compS_exch h h1
  obtain ⟨x3, hx3, h''⟩ := compS_reassoc h' h2
  obtain ⟨x4, hx4, hx3'⟩ := compS_exch hx1 hx3
  obtain ⟨x5, hx5, hx5'⟩ := compS_exch (ResU.CompS.comm hx4) hx3'
  exact ⟨x2, x3, x5, ResU.CompS.comm hx2, hx5, hx5', h''⟩

/-- Four resources rearranged: `((a ● k) ● c) ● κ = (κ ● c) ● k` when `a = ∅`. -/
theorem rearr4 {k c κ ak ρ ρ' : WRes} (hak : ResU.CompS PMap.empty k ak)
    (hc : ResU.CompS ak c ρ) (h1 : ResU.CompS ρ κ ρ') :
    ∃ ρ₃, ResU.CompS κ c ρ₃ ∧ ResU.CompS ρ₃ k ρ' := by
  obtain rfl := eq_of_compS_empty_left hak
  obtain ⟨x, hx, h⟩ := compS_reassoc hc h1
  exact ⟨x, ResU.CompS.comm hx, ResU.CompS.comm h⟩

/-- **`spawn`'s clause**: `f` and `κ` stored in fresh cells; the payload, the stored closure and
the stored continuation handed to the scheduler. -/
theorem spawnCl_ok (l : Loc) (F : WRes → Prop) {k : Nat} {ls : List SRec} {O : List FrameRec}
    {f : Val} {ℓc : Loc} {K : Kont} {ρa ρk ρak ρ : WRes}
    (hA : PAspawn (ℍ := ℍ) k ls f ρa)
    (hsh : contShareC (liftEnt (spawnEnt (ℍ := ℍ))) F k ls O K f
      (cerwpC (ℍ := ℍ) (opTableC (TP (ℍ := ℍ))) (Qsc l) k) ρk)
    (hak : ResU.CompS ρa ρk ρak) (hc : ResU.CompS ρak (ResU.single ℓc (CellU.ownOf Val.unit)) ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QP (ℍ := ℍ) l F) F (k - 1) ls O
      (.app (.val c₀) (.pair (.val f) (kappaC false ℓc HP K))) ρ := by
  have hD := opTableC_down opTabC_emptyC_down
  have hL := opTableC_local OpTabC.emptyC
  have hQ := QP_down (ℍ := ℍ) l F
  set κV := kV false ℓc HP K with hκV
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.pair f κV)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair f κV)
      (.letpair (.var 0) (.inj₁ (.inj₁ (.pair (allocE (.var 1)) (allocE (.var 0))))))) =
      Kont.hole.plug (.letpair (.val (Val.pair f κV))
        (.inj₁ (.inj₁ (.pair (allocE (.var 1)) (allocE (.var 0)))))) := by
    simp [Expr.subst, Kont.plug, allocE]
  rw [e₁]
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.letpair μ f κV _) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f (Expr.subst 0 (κV.shift 1 0)
      (.inj₁ (.inj₁ (.pair (allocE (.var 1)) (allocE (.var 0))))))) =
      (Kont.inj₁ (Kont.inj₁ (Kont.pairL .hole (allocE κV.1)))).plug
        (.app (.val (.prim .alloc)) (.val f)) := by
    simp only [Expr.subst, allocE, Kont.plug, if_true, Val.val_shift]
    rw [kV_subst]
    simp [Expr.subst]
  rw [e₂]
  refine cerwp_allocX hL _ f (fun ℓf ρ' hc₁ => ?_)
  have e₃ : (Kont.inj₁ (Kont.inj₁ (Kont.pairL .hole (allocE κV.1)))).plug (.val (Val.loc ℓf)) =
      (Kont.inj₁ (Kont.inj₁ (Kont.pairR (Val.loc ℓf) .hole))).plug
        (.app (.val (.prim .alloc)) (.val κV)) := rfl
  rw [e₃]
  refine cerwp_allocX hL _ κV (fun ℓκ ρ'' hc₂ => ?_)
  have e₄ : (Kont.inj₁ (Kont.inj₁ (Kont.pairR (Val.loc ℓf) .hole))).plug (.val (Val.loc ℓκ)) =
      (Val.inj₁ (Val.inj₁ (Val.pair (Val.loc ℓf) (Val.loc ℓκ)))).1 := rfl
  rw [e₄]
  obtain ⟨ρ₁, ρ₂, ρ₃, h₁, h₃, h₂, h₁₂⟩ := rearr5 hak hc hc₁ hc₂
  obtain ⟨m, s, u, hs, ea, hk⟩ := hA
  exact cerwp_val (.inr (.inl ⟨ℓf, ℓκ, f, ρ₁, ρa, ρ₂, rfl, h₁,
    ⟨m, s, u, hs, ea, fun k' hk' => hk k' (by omega)⟩, h₁₂,
    ⟨ℓc, K, ρk, ρ₃, k, by omega, h₃, h₂, hsh⟩⟩))

/-- **The join's clause**: `κ` stored in a fresh cell. -/
theorem joinCl_ok (l : Loc) (F : WRes → Prop) {k : Nat} {ls : List SRec} {O : List FrameRec}
    {v : Val} {ℓc : Loc} {K : Kont} {ρa ρk ρak ρ : WRes}
    (hA : joinEnt.PA k ls v ρa)
    (hsh : contShareC joinEnt F k ls O K v
      (cerwpC (ℍ := ℍ) (opTableC (TP (ℍ := ℍ))) (Qsc l) k) ρk)
    (hak : ResU.CompS ρa ρk ρak) (hc : ResU.CompS ρak (ResU.single ℓc (CellU.ownOf Val.unit)) ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QP (ℍ := ℍ) l F) F (k - 1) ls O
      (.app (.val c₁) (.pair (.val v) (kappaC false ℓc HP K))) ρ := by
  have hD := opTableC_down opTabC_emptyC_down
  have hL := opTableC_local OpTabC.emptyC
  have hQ := QP_down (ℍ := ℍ) l F
  obtain ⟨⟨m, rfl⟩, rfl⟩ := hA
  set κV := kV false ℓc HP K with hκV
  refine cerwp_det hD hQ
    (fun μ => step1Only_plug (Head.beta μ _ (Val.pair (Val.loc m) κV)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair (Val.loc m) κV)
      (.letpair (.var 0) (.inj₁ (.inj₂ (allocE (.var 0)))))) =
      Kont.hole.plug (.letpair (.val (Val.pair (Val.loc m) κV))
        (.inj₁ (.inj₂ (allocE (.var 0))))) := by
    simp [Expr.subst, Kont.plug, allocE]
  rw [e₁]
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.letpair μ (Val.loc m) κV _) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 (Val.loc m) (Expr.subst 0 (κV.shift 1 0)
      (.inj₁ (.inj₂ (allocE (.var 0)))))) =
      (Kont.inj₁ (Kont.inj₂ .hole)).plug (.app (.val (.prim .alloc)) (.val κV)) := by
    simp only [Expr.subst, allocE, Kont.plug, if_true, Val.val_shift]
    rw [kV_subst]
    rfl
  rw [e₂]
  refine cerwp_allocX hL _ κV (fun ℓκ ρ' hc₁ => ?_)
  have e₃ : (Kont.inj₁ (Kont.inj₂ .hole)).plug (.val (Val.loc ℓκ)) =
      (Val.inj₁ (Val.inj₂ (Val.loc ℓκ))).1 := rfl
  rw [e₃]
  obtain ⟨ρ₃, h₃, h₂⟩ := rearr4 hak hc hc₁
  exact cerwp_val (.inr (.inr ⟨ℓκ, m, rfl, ⟨ℓc, K, ρk, ρ₃, k, by omega, h₃, h₂, hsh⟩⟩))

/-- **`y`'s clause**: `κ` stored in a fresh cell. -/
theorem yCl_ok (F : WRes → Prop) {k : Nat} {ls : List SRec} {O : List FrameRec}
    {v : Val} {ℓc : Loc} {K : Kont} {ρa ρk ρak ρ : WRes} (hO : O = [])
    (hA : (yEnt (ℍ := ℍ)).PA k ls v ρa)
    (hsh : contShareC (yEnt (ℍ := ℍ)) F k ls O K v
      (cerwpC (ℍ := ℍ) (opTableC (TC (ℍ := ℍ))) Qchild k) ρk)
    (hak : ResU.CompS ρa ρk ρak) (hc : ResU.CompS ρak (ResU.single ℓc (CellU.ownOf Val.unit)) ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QC (ℍ := ℍ) F) F (k - 1) ls O
      (.app (.val cy) (.pair (.val v) (kappaC true ℓc HC K))) ρ := by
  have hD := opTableC_down opTabC_emptyC_down
  have hL := opTableC_local OpTabC.emptyC
  have hQ := QC_down (ℍ := ℍ) F
  obtain ⟨rfl, rfl⟩ := hA
  set κV := kV true ℓc HC K with hκV
  refine cerwp_det hD hQ
    (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κV)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair Val.unit κV)
      (.letpair (.var 0) (.inj₁ (allocE (.var 0))))) =
      Kont.hole.plug (.letpair (.val (Val.pair Val.unit κV)) (.inj₁ (allocE (.var 0)))) := by
    simp [Expr.subst, Kont.plug, allocE]
  rw [e₁]
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.letpair μ Val.unit κV _) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 Val.unit (Expr.subst 0 (κV.shift 1 0)
      (.inj₁ (allocE (.var 0))))) =
      (Kont.inj₁ .hole).plug (.app (.val (.prim .alloc)) (.val κV)) := by
    simp only [Expr.subst, allocE, Kont.plug, if_true, Val.val_shift]
    rw [kV_subst]
    rfl
  rw [e₂]
  refine cerwp_allocX hL _ κV (fun ℓκ ρ' hc₁ => ?_)
  have e₃ : (Kont.inj₁ .hole).plug (.val (Val.loc ℓκ)) = (Val.inj₁ (Val.loc ℓκ)).1 := rfl
  rw [e₃]
  obtain ⟨ρ₃, h₃, h₂⟩ := rearr4 hak hc hc₁
  exact cerwp_val (.inr ⟨ℓκ, rfl, hO, ⟨ℓc, K, ρk, ρ₃, k, by omega, h₃, h₂, hsh⟩⟩)

/-- **A run of the parent under `HP`** (`cerwp_gen`): whatever it stops at, the scheduler gets
the event. -/
theorem genP (l : Loc) (F : WRes → Prop) :
    ∀ n ls O e ρ, cerwp (ℍ := ℍ) (opTableC (TP (ℍ := ℍ))) (Qsc l) F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QP (ℍ := ℍ) l F) F n ls O (hndE HP e) ρ := by
  refine cerwp_gen (QP_down l F) 7 (qualsVal [.lin, .lin]) retV (Val.pair c₀ (Val.pair c₁ Val.unit))
    (fun m i en h => ?_) (fun k ls O v ρ hv => cerwp_retV (QP_down l F) (.inl ⟨v, rfl, hv⟩))
    (fun i en h => ?_)
  · rcases TP_some h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, by simp [liftEnt, spawnEnt], by simp [capTag, qualsVal, Val.pair, Val.i32,
        Qual.tag, liftEnt, spawnEnt]⟩
    · exact ⟨rfl, by simp [joinEnt], by simp [capTag, qualsVal, Val.pair, Val.i32, Qual.tag,
        joinEnt]⟩
  · rcases TP_some h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact ⟨c₀, clauseAt0 _ _, fun k ls O v ℓ K ρa ρk ρak ρ _ hA hsh hak hc =>
        spawnCl_ok l F hA hsh hak hc⟩
    · exact ⟨c₁, clauseAt1 _ _ _, fun k ls O v ℓ K ρa ρk ρak ρ _ hA hsh hak hc =>
        joinCl_ok l F hA hsh hak hc⟩

/-- **A run of the child under `HC`.** -/
theorem genC (F : WRes → Prop) :
    ∀ n ls O e ρ, cerwp (ℍ := ℍ) (opTableC (TC (ℍ := ℍ))) Qchild F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QC (ℍ := ℍ) F) F n ls O (hndE HC e) ρ := by
  refine cerwp_gen (QC_down F) 8 (qualsVal [.cancel]) retV (Val.pair cy Val.unit)
    (fun m i en h => ?_) (fun k ls O v ρ hv => cerwp_retV (QC_down F) (.inl ⟨v, rfl, hv⟩))
    (fun i en h => ?_)
  · obtain ⟨rfl, rfl, rfl⟩ := TC_some h
    exact ⟨rfl, by simp [yEnt], by simp [capTag, qualsVal, Val.pair, Val.i32, Qual.tag, yEnt]⟩
  · obtain ⟨-, rfl, rfl⟩ := TC_some h
    exact ⟨cy, clauseAt0 _ _, fun k ls O v ℓ K ρa ρk ρak ρ hoc hA hsh hak hc => by
      exact yCl_ok F hoc hA hsh hak hc⟩

/-! ### The scheduler -/

/-- `(free κ) (inj₁ ()) ()`: take a stored continuation and resume it at `()`. -/
def resumeT (κ : Expr) : Expr := .app (.app (freeE κ) (.val (Val.inj₁ Val.unit))) (.val Val.unit)

theorem kapStored_le {Tin : OpTabC} {Qin : PostCV} {H : Val} {en : OpEntC}
    {F : WRes → Prop} {k k' : Nat} (hk : k' ≤ k) {ls : List SRec} {O : List FrameRec} {v : Val}
    {ℓκ : Loc} {ρ : WRes} (h : KapStored (ℍ := ℍ) Tin Qin H en F k ls O v ℓκ ρ) :
    KapStored (ℍ := ℍ) Tin Qin H en F k' ls O v ℓκ ρ := by
  obtain ⟨ℓc, K, ρk, ρ₁, k₀, hk₀, h₁, h₂, h₃⟩ := h
  exact ⟨ℓc, K, ρk, ρ₁, k₀, by omega, h₁, h₂, h₃⟩

/-- **Resuming a stored continuation at `()`**: the cell taken, `κ` resumed, the handled
computation run again under its handler, from the share and the answer `σ`. -/
theorem cerwp_resumeStored {Tin : OpTabC} {Qin Qout : PostCV} (hQout : Qout.Down) {H : Val}
    {en : OpEntC} {F : WRes → Prop} {k₁ : Nat} {ls₀ : List SRec} {O : List FrameRec} {v : Val}
    {ℓκ : Loc} {ρ σ ρσ : WRes}
    (hgen : ∀ n ls O e ρ, cerwp (ℍ := ℍ) (opTableC Tin) Qin (fun ρf => F ρf ∧ en.fd v ρf) n ls O
      e ρ → cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qout (fun ρf => F ρf ∧ en.fd v ρf) n ls O
        (hndE H e) ρ)
    (hst : KapStored (ℍ := ℍ) Tin Qin H en F k₁ ls₀ O v ℓκ ρ)
    (hσ : ∀ k' ls', en.PBv v k' ls' Val.unit σ) (hc : ResU.CompS ρ σ ρσ) {k : Nat} (hk : k ≤ k₁)
    {ls : List SRec} (hwc : ∀ ρk, en.wc ls₀ ls ρk) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qout (fun ρf => F ρf ∧ en.fd v ρf) k ls O
      (resumeT (.val (Val.loc ℓκ))) ρσ := by
  have hLE := opTableC_local OpTabC.emptyC
  have hDE := opTableC_down opTabC_emptyC_down
  obtain ⟨ℓc, K, ρk, ρ₁, k₀, hk₀, h₁, h₂, hsh⟩ := hst
  obtain ⟨x, hx, hxσ⟩ := compS_reassoc h₂ hc
  obtain ⟨y, hy, hyσ⟩ := compS_reassoc h₁ hxσ
  refine cerwp_freeX hLE (.appL (.appL .hole (Val.inj₁ Val.unit)) Val.unit) ℓκ _ hyσ ?_
  refine cerwp_kappaC_resume hLE hDE hQout _ ℓc H K Val.unit hy ?_
  by_cases hk2 : k - 1 - 1 = 0
  · rw [hk2]; exact cerwp_zero
  · refine hgen _ _ _ _ _ ?_
    have hcont := (hsh.2 ls (hwc ρk)).1 (k - 1 - 1) (by omega) Val.unit σ x (hσ _ _) hx
    simp only [cerwpC, show k - 1 - 1 < k₀ by omega, if_true] at hcont
    exact hcont

/-- **Cancelling a stored continuation**: the cell taken, `κ` cancelled, its cancel obligation
run. -/
theorem cerwp_cancelStored {Tin : OpTabC} {Qin Qc : PostCV} (hQc : Qc.Down) {H : Val}
    {en : OpEntC} {F F' : WRes → Prop} {k₁ : Nat} {ls₀ : List SRec} {O : List FrameRec}
    {v : Val} {ℓκ : Loc} {ρ : WRes} (hcan : en.q = .cancel)
    (hfin : ∀ k ls e ρ, (∀ P, en.fin = some P → P k ls e ρ) →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qc F' k ls O (ccatchE e) ρ)
    (hst : KapStored (ℍ := ℍ) Tin Qin H en F k₁ ls₀ O v ℓκ ρ) {k : Nat} (hk : k ≤ k₁)
    {ls : List SRec} (hwc : ∀ ρk, en.wc ls₀ ls ρk)
    (hdown : ∀ P, en.fin = some P → ∀ m k ls e ρ, m ≤ k → P k ls e ρ → P m ls e ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qc F' k ls O
      (.app (freeE (.val (Val.loc ℓκ))) (.val (Val.inj₂ Val.unit))) ρ := by
  have hLE := opTableC_local OpTabC.emptyC
  have hDE := opTableC_down opTabC_emptyC_down
  obtain ⟨ℓc, K, ρk, ρ₁, k₀, hk₀, h₁, h₂, hsh⟩ := hst
  obtain ⟨x, hx, hxσ⟩ := compS_reassoc h₁ h₂
  have hcc : cellCancel en.q = true := by rw [hcan]; rfl
  refine cerwp_freeX hLE (.appL .hole (Val.inj₂ Val.unit)) ℓκ _ hxσ ?_
  rw [show kV (cellCancel en.q) ℓc H K = kV true ℓc H K by rw [hcc]]
  refine cerwp_kappaC_cancel hLE hDE hQc ℓc H K hx ?_
  refine hfin _ _ _ _ (fun P hP => ?_)
  exact hdown P hP _ _ _ _ _ (by omega) ((hsh.2 ls (hwc ρk)).2 (by rw [hcan]; simp) P hP)


/-- The parent, the cell a variable. -/
def parentT : Expr :=
  .seq (performE (.pair (.val (Val.i32 7)) (.pair (.val (Val.i32 0))
      (.lam (.seq yE (.app (.val (.prim .load)) (.var 1)))))))
    (performE (.pair (.val (Val.i32 7)) (.pair (.val (Val.i32 1)) (.var 0))))

/-- `r₅ = κ′_p ()`, then `free c`. -/
def M5 : Expr := .case (resumeT (.var 1)) omegaE (freeE (.var 9))
/-- `r₄ = κ_c ()`. -/
def M4 : Expr := .case (resumeT (.var 2)) omegaE M5
/-- `r₃ = κ_p ()`, expecting the join. -/
def M3 : Expr := .case (resumeT (.var 1)) (.case (.var 0) omegaE M4) omegaE
/-- `r₂ = hnd_C (f ())`. -/
def M2 : Expr := .case (hndE HC (.app (freeE (.var 1)) (.val Val.unit))) M3 omegaE
/-- `r₁ = hnd_P parent`, expecting the spawn. -/
def M1 : Expr :=
  .case (hndE HP parentT) (.case (.var 0) (.letpair (.var 0) M2) omegaE) omegaE
/-- **The program.** -/
def mainE : Expr := .app (.val (Val.lam M1)) (allocE (.val Val.unit))

/-- The scheduler's result: no records, only `imm` cells. -/
def Qmain : PostCV := fun _ _ O _ ρ => O = [] ∧ AllImm ρ

theorem Qmain_down : Qmain.Down := fun _ _ _ _ _ h => h

theorem HP_closed : closedAt 0 HP.1 = true := by decide
theorem HC_closed : closedAt 0 HC.1 = true := by decide
theorem omegaE_closed : closedAt 0 omegaE = true := by decide

@[simp] theorem HP_subst (j : Nat) (s : Val) : Expr.subst j s HP.1 = HP.1 :=
  subst_closedAt _ s HP_closed (Nat.zero_le _)
@[simp] theorem HC_subst (j : Nat) (s : Val) : Expr.subst j s HC.1 = HC.1 :=
  subst_closedAt _ s HC_closed (Nat.zero_le _)
@[simp] theorem omegaE_subst (j : Nat) (s : Val) : Expr.subst j s omegaE = omegaE :=
  subst_closedAt _ s omegaE_closed (Nat.zero_le _)

@[simp] theorem loc_shift (d c : Nat) (l : Loc) : Val.shift d c (Val.loc l) = Val.loc l := rfl

@[simp] theorem prim_subst (j : Nat) (s : Val) (p : BoCa.Prim) :
    Expr.subst j s (Expr.val (Val.prim p)) = Expr.val (Val.prim p) := rfl

@[simp] theorem inj₁_shift (d c : Nat) (v : Val) :
    Val.shift d c (Val.inj₁ v) = Val.inj₁ (Val.shift d c v) := rfl
@[simp] theorem inj₂_shift (d c : Nat) (v : Val) :
    Val.shift d c (Val.inj₂ v) = Val.inj₂ (Val.shift d c v) := rfl
@[simp] theorem pair_shift (d c : Nat) (v w : Val) :
    Val.shift d c (Val.pair v w) = Val.pair (Val.shift d c v) (Val.shift d c w) := rfl
@[simp] theorem unit_shift (d c : Nat) : Val.shift d c Val.unit = Val.unit := rfl

@[simp] theorem locV_subst (j : Nat) (s : Val) (l : Loc) :
    Expr.subst j s (Expr.val (Val.loc l)) = Expr.val (Val.loc l) := rfl
@[simp] theorem unitV_subst (j : Nat) (s : Val) :
    Expr.subst j s (Expr.val Val.unit) = Expr.val Val.unit := rfl
@[simp] theorem inj₁unitV_subst (j : Nat) (s : Val) :
    Expr.subst j s (Expr.val (Val.inj₁ Val.unit)) = Expr.val (Val.inj₁ Val.unit) := rfl
@[simp] theorem inj₂unitV_subst (j : Nat) (s : Val) :
    Expr.subst j s (Expr.val (Val.inj₂ Val.unit)) = Expr.val (Val.inj₂ Val.unit) := rfl

theorem parentT_subst (l : Loc) : Expr.subst 0 (Val.loc l) parentT = parentE l := by
  simp [parentT, parentE, seqK, spawnE, joinE, fchild, yE, ldL, Expr.subst, Kont.plug, performE,
    opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Val.lam, Val.shift, Expr.shift, Expr.val,
    Val.prim]

/-- The child's borrows split into what the join hands back (those at the joined location) and the
rest, which the scheduler keeps: nothing at the joined location at any depth, only `imm` cells. -/
theorem leftV_split {ρ : WRes} (h : LeftV ρ) (m : Loc) :
    ∃ σB junk, ResU.CompS σB junk ρ ∧
      (σB = PMap.empty ∨ ∃ (s : LSet) (u : Val) (hs : ResU.InStratum s.join (PMap.empty : WRes)),
        σB = ResU.single m (CellU.immOf s u PMap.empty hs)) ∧
      (∀ τ, ResU.Flat junk τ → τ.get m = none) ∧ AllImm junk := by
  rcases h with rfl | ⟨m', s, u, hs, rfl⟩
  · refine ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, .inl rfl, fun τ hτ => ?_,
      fun _ _ h => by simp at h⟩
    rw [flat_empty_eq hτ]; rfl
  · by_cases hm : m' = m
    · subst hm
      refine ⟨_, PMap.empty, ResU.comp_empty_right _, .inr ⟨s, u, hs, rfl⟩, fun τ hτ => ?_,
        fun _ _ h => by simp at h⟩
      rw [flat_empty_eq hτ]; rfl
    · refine ⟨PMap.empty, _, compS_empty_left _, .inl rfl,
        fun τ hτ => flat_single_imm_empty hτ m (Ne.symm hm), fun x ψ hx => ?_⟩
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hx
      rfl

theorem main_ok (n : Nat) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qmain (fun ρf => ρf = PMap.empty) n [] [] mainE
      (PMap.empty : WRes) := by
  have hLE := opTableC_local OpTabC.emptyC
  have hDE := opTableC_down opTabC_emptyC_down
  refine cerwp_allocX hLE (.appR (.val (Val.lam M1)) .hole) Val.unit (fun ℓ ρ' hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine cerwp_det hDE Qmain_down (fun μ => step1Only_plug (Head.beta μ M1 (Val.loc ℓ)) rfl .hole) ?_
  simp only [M1, Expr.subst, HP_subst, omegaE_subst, hndE, Kont.plug, parentT_subst, loc_shift,
    prim_subst]
  simp (config := { decide := true }) only [if_false, Nat.reduceAdd]
  -- r₁: the parent, under `HP`, the cell its only resource
  refine cerwp_frameBindE (Q₁ := QP (ℍ := ℍ) ℓ (fun _ => True)) (F₁ := fun _ => True)
    (fun ρ => ρ = PMap.empty) (.case .hole _ omegaE) (O₁ := []) (O₂ := [])
    (fun _ h => by simp at h) (ResU.comp_empty_right _) (fun _ _ _ _ _ => trivial)
    (genP ℓ _ _ [] [] (parentE ℓ) _ (parent_ok ℓ 0 _ _ [])) rfl
    (fun k ls₁ O₁ v ρa ρb ρ' hk hq hR hc => ?_)
  subst hR
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf, ℓκ, f, ρ₁, ρv, ρ₂, rfl, h₁, hPA, h₁₂, hks⟩ | ⟨ℓκ, m, rfl, -⟩
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _
  · -- the spawn: `(f, κ_p)` in their cells
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₁_shift, pair_shift, loc_shift, Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.letpair μ (Val.loc ℓf) (Val.loc ℓκ) _) rfl .hole) ?_
    simp (config := { decide := true }) only [M2, M3, M4, M5, Expr.subst, if_true, if_false,
      Nat.reduceAdd, Nat.reduceSub, inj₁_shift, pair_shift, loc_shift, Kont.plug, omegaE_subst,
      HC_subst, prim_subst, resumeT, hndE, freeE, locV_subst, unitV_subst, inj₁unitV_subst]
    rw [List.append_nil]
    -- r₂: the child, from the stored closure and its borrow; `κ_p` kept beside it
    obtain ⟨mv, sv, uv, hsv, rfl, hchild⟩ := hPA
    refine cerwp_frameBindE (Q₁ := QC (ℍ := ℍ) (fun _ => True)) (F₁ := fun _ => True)
      (KapStored (ℍ := ℍ) (TP (ℍ := ℍ)) (Qsc ℓ) HP (liftEnt (spawnEnt (ℍ := ℍ))) (fun _ => True)
        k ls₁ O₁ f ℓκ)
      (.case .hole _ omegaE) (O₁ := []) (O₂ := O₁) (fun _ h => by simp at h) h₁₂
      (fun _ _ _ _ _ => trivial) ?_ hks (fun k₂ ls₂ O₂ v ρa ρb ρ'' hk₂ hq hR hc₂ => ?_)
    · refine genC _ _ _ _ _ _ ?_
      exact cerwp_freeX (opTableC_local _) (.appL .hole Val.unit) ℓf f h₁
        (hchild (k - 1) (by omega) ls₁ _)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓκc, rfl, rfl, hkc⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst, unitV_subst,
      inj₁unitV_subst]
    -- r₃: the parent resumed, `κ_c` kept beside it
    rw [show ([] : List FrameRec) ++ O₁ = O₁ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QP (ℍ := ℍ) ℓ (fun ρf => True ∧ True))
      (F₁ := fun ρf => True ∧ True)
      (KapStored (ℍ := ℍ) (TC (ℍ := ℍ)) Qchild HC (yEnt (ℍ := ℍ)) (fun _ => True) k₂ ls₂ []
        Val.unit ℓκc)
      (.case .hole _ omegaE) (O₁ := O₁) (O₂ := []) (fun _ _ h => by simp at h)
      (ResU.CompS.comm hc₂) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
      (cerwp_resumeStored (σ := PMap.empty) (QP_down ℓ _) (genP ℓ _) (kapStored_le hk₂ hR)
        (fun _ _ => ⟨rfl, rfl⟩) (ResU.comp_empty_right _) le_rfl (fun _ => trivial))
      hkc (fun k₃ ls₃ O₃ v ρa₃ ρb₃ ρ₃ hk₃ hq hR₃ hc₃ => ?_)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf', ℓκ', f', -, -, -, rfl, -⟩ | ⟨ℓκp, m, rfl, hkp⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
        Kont.plug, omegaE_subst]
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, inj₂_shift, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst,
      unitV_subst, inj₁unitV_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, Nat.reduceAdd, Kont.plug, omegaE_subst,
      prim_subst, locV_subst, unitV_subst, inj₁unitV_subst]
    -- r₄: the child resumed, `κ′_p` kept beside it
    rw [List.append_nil]
    refine cerwp_frameBindE (Q₁ := QC (ℍ := ℍ) (fun ρf => True ∧ True))
      (F₁ := fun ρf => True ∧ True)
      (KapStored (ℍ := ℍ) (TP (ℍ := ℍ)) (Qsc ℓ) HP joinEnt (fun ρf => True ∧ True) k₃ ls₃ O₃
        (Val.loc m) ℓκp)
      (.case .hole omegaE _) (O₁ := []) (O₂ := O₃) (fun _ h => by simp at h)
      (ResU.CompS.comm hc₃) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
      (cerwp_resumeStored (σ := PMap.empty) (QC_down _) (genC _) (kapStored_le hk₃ hR₃)
        (fun _ _ => ⟨rfl, rfl⟩) (ResU.comp_empty_right _) le_rfl (fun _ => trivial))
      hkp (fun k₄ ls₄ O₄ v ρa₄ ρb₄ ρ₄ hk₄ hq hR₄ hc₄ => ?_)
    rcases hq with ⟨v₀, rfl, hO₄, hleft⟩ | ⟨ℓκ', rfl, -, -⟩
    swap
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    subst hO₄
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, Nat.reduceAdd, Kont.plug, omegaE_subst,
      prim_subst, locV_subst, unitV_subst, inj₁unitV_subst]
    -- r₅: the parent resumed from the join, with the child's borrow of the joined location; the
    -- scheduler keeps nothing at it
    obtain ⟨σB, junk, hsj, hσB, hfree, himm⟩ := leftV_split hleft m
    obtain ⟨ρs, hsσ, hsj'⟩ := compS_exch hsj hc₄
    rw [show ([] : List FrameRec) ++ O₃ = O₃ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QP (ℍ := ℍ) ℓ (fun ρf => (True ∧ True) ∧ joinFd (Val.loc m) ρf))
      (F₁ := fun ρf => (True ∧ True) ∧ joinFd (Val.loc m) ρf) (fun ρ => ρ = junk)
      (.case .hole omegaE _) (O₁ := O₃) (O₂ := []) (fun _ _ h => by simp at h) hsj'
      (fun ρf y hρf _ hy => by
        have hρf' : ρf = PMap.empty := hρf
        subst hρf'
        obtain rfl := eq_of_compS_empty_left hy
        exact ⟨⟨trivial, trivial⟩, m, rfl, hfree⟩)
      (cerwp_resumeStored (σ := σB) (QP_down ℓ _) (genP ℓ _) (kapStored_le hk₄ hR₄)
        (fun _ _ => ⟨m, rfl, rfl, hσB⟩) (ResU.CompS.comm hsσ) le_rfl (fun _ => trivial))
      rfl (fun k₅ ls₅ O₅ v ρa₅ ρb₅ ρ₅ hk₅ hq hR₅ hc₅ => ?_)
    subst hR₅
    rcases hq with ⟨v₀, rfl, -, rfl, hO₅⟩ | ⟨-, -, -, -, -, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
    · -- the parent finished: the cell owned again, freed; the scheduler's result
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
      simp only [Expr.subst, prim_subst, locV_subst, Kont.plug]
      have hO : O₅ = [] := List.eq_nil_iff_forall_not_mem.mpr hO₅
      subst hO
      exact cerwp_freeX hLE .hole ℓ Val.unit hc₅ (cerwp_val ⟨rfl, himm⟩)
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₂_shift, loc_shift, Kont.plug, omegaE_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _

/-- **The cross-task test.** A parent lends `c` `imm` around `spawn (λ_. y (); !c); join(c)`; the
child holds the borrow across its `y`; the scheduler stores the parent's continuation (the lend
open in it) and the child's, resumes the parent to the join, then the child to its end, then the
parent with the child's borrow handed back; the lend ends and `c` is freed. Every configuration
a run reaches is a value or steps, a value only at the empty memory, and every `free` finds its
cell. No fuel. -/
theorem prog_orDiverges : OrDiverges (ℍ := ℍ) mainE :=
  cerwp_adequacy (fun _ _ _ _ _ h => h) main_ok


/-! ### The cancel: the scheduler cancels the child while the lend is live -/

/-- `κ_c` cancelled; then `r₅ = κ′_p ()` and `free c`. -/
def M4d : Expr :=
  .seq (.app (freeE (.var 2)) (.val (Val.inj₂ Val.unit)))
    (.case (resumeT (.var 0)) omegaE (freeE (.var 8)))
def M3d : Expr := .case (resumeT (.var 1)) (.case (.var 0) omegaE M4d) omegaE
def M2d : Expr := .case (hndE HC (.app (freeE (.var 1)) (.val Val.unit))) M3d omegaE
def M1d : Expr :=
  .case (hndE HP parentT) (.case (.var 0) (.letpair (.var 0) M2d) omegaE) omegaE
/-- **The program with the cancel.** -/
def mainD : Expr := .app (.val (Val.lam M1d)) (allocE (.val Val.unit))

theorem mainD_ok (n : Nat) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qmain (fun ρf => ρf = PMap.empty) n [] [] mainD
      (PMap.empty : WRes) := by
  have hLE := opTableC_local OpTabC.emptyC
  have hDE := opTableC_down opTabC_emptyC_down
  refine cerwp_allocX hLE (.appR (.val (Val.lam M1d)) .hole) Val.unit (fun ℓ ρ' hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine cerwp_det hDE Qmain_down (fun μ => step1Only_plug (Head.beta μ M1d (Val.loc ℓ)) rfl .hole) ?_
  simp only [M1d, Expr.subst, HP_subst, omegaE_subst, hndE, Kont.plug, parentT_subst, loc_shift,
    prim_subst]
  simp (config := { decide := true }) only [if_false, Nat.reduceAdd]
  -- r₁: the parent, under `HP`, the cell its only resource
  refine cerwp_frameBindE (Q₁ := QP (ℍ := ℍ) ℓ (fun _ => True)) (F₁ := fun _ => True)
    (fun ρ => ρ = PMap.empty) (.case .hole _ omegaE) (O₁ := []) (O₂ := [])
    (fun _ h => by simp at h) (ResU.comp_empty_right _) (fun _ _ _ _ _ => trivial)
    (genP ℓ _ _ [] [] (parentE ℓ) _ (parent_ok ℓ 0 _ _ [])) rfl
    (fun k ls₁ O₁ v ρa ρb ρ' hk hq hR hc => ?_)
  subst hR
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf, ℓκ, f, ρ₁, ρv, ρ₂, rfl, h₁, hPA, h₁₂, hks⟩ | ⟨ℓκ, m, rfl, -⟩
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _
  · -- the spawn: `(f, κ_p)` in their cells
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₁_shift, pair_shift, loc_shift, Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.letpair μ (Val.loc ℓf) (Val.loc ℓκ) _) rfl .hole) ?_
    simp (config := { decide := true }) only [M2d, M3d, M4d, Expr.subst, if_true, if_false,
      Nat.reduceAdd, Nat.reduceSub, inj₁_shift, pair_shift, loc_shift, Kont.plug, omegaE_subst,
      HC_subst, prim_subst, resumeT, hndE, freeE, locV_subst, unitV_subst, inj₁unitV_subst,
      inj₂unitV_subst]
    rw [List.append_nil]
    -- r₂: the child, from the stored closure and its borrow; `κ_p` kept beside it
    obtain ⟨mv, sv, uv, hsv, rfl, hchild⟩ := hPA
    refine cerwp_frameBindE (Q₁ := QC (ℍ := ℍ) (fun _ => True)) (F₁ := fun _ => True)
      (KapStored (ℍ := ℍ) (TP (ℍ := ℍ)) (Qsc ℓ) HP (liftEnt (spawnEnt (ℍ := ℍ))) (fun _ => True)
        k ls₁ O₁ f ℓκ)
      (.case .hole _ omegaE) (O₁ := []) (O₂ := O₁) (fun _ h => by simp at h) h₁₂
      (fun _ _ _ _ _ => trivial) ?_ hks (fun k₂ ls₂ O₂ v ρa ρb ρ'' hk₂ hq hR hc₂ => ?_)
    · refine genC _ _ _ _ _ _ ?_
      exact cerwp_freeX (opTableC_local _) (.appL .hole Val.unit) ℓf f h₁
        (hchild (k - 1) (by omega) ls₁ _)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓκc, rfl, rfl, hkc⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst, unitV_subst,
      inj₁unitV_subst]
    -- r₃: the parent resumed, `κ_c` kept beside it
    rw [show ([] : List FrameRec) ++ O₁ = O₁ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QP (ℍ := ℍ) ℓ (fun ρf => True ∧ True))
      (F₁ := fun ρf => True ∧ True)
      (KapStored (ℍ := ℍ) (TC (ℍ := ℍ)) Qchild HC (yEnt (ℍ := ℍ)) (fun _ => True) k₂ ls₂ []
        Val.unit ℓκc)
      (.case .hole _ omegaE) (O₁ := O₁) (O₂ := []) (fun _ _ h => by simp at h)
      (ResU.CompS.comm hc₂) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
      (cerwp_resumeStored (σ := PMap.empty) (QP_down ℓ _) (genP ℓ _) (kapStored_le hk₂ hR)
        (fun _ _ => ⟨rfl, rfl⟩) (ResU.comp_empty_right _) le_rfl (fun _ => trivial))
      hkc (fun k₃ ls₃ O₃ v ρa₃ ρb₃ ρ₃ hk₃ hq hR₃ hc₃ => ?_)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf', ℓκ', f', -, -, -, rfl, -⟩ | ⟨ℓκp, m, rfl, hkp⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
        Kont.plug, omegaE_subst]
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, inj₂_shift, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst,
      unitV_subst, inj₁unitV_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, Nat.reduceAdd, Kont.plug, omegaE_subst,
      prim_subst, locV_subst, unitV_subst, inj₁unitV_subst]
    -- r₄: the child cancelled while the lend is live, `κ′_p` kept beside it; the cancel run
    -- unwinds the child and returns its borrow
    rw [List.append_nil]
    refine cerwp_frameBindE (Q₁ := Qleft) (F₁ := fun _ => True)
      (KapStored (ℍ := ℍ) (TP (ℍ := ℍ)) (Qsc ℓ) HP joinEnt (fun ρf => True ∧ True) k₃ ls₃ O₃
        (Val.loc m) ℓκp)
      (.seq .hole _) (O₁ := []) (O₂ := O₃) (fun _ h => by simp at h)
      (ResU.CompS.comm hc₃) (fun _ _ _ _ _ => trivial)
      (cerwp_cancelStored (Qin := Qchild) Qleft_down rfl (fun _ _ _ _ h => h (Pcan (ℍ := ℍ)) rfl _)
        (kapStored_le hk₃ hR₃) le_rfl (fun _ => trivial)
        (fun P hP j k' ls' e' ρ'' hj h => by
          cases hP
          exact fun F => cerwp_le (opTableC_local _) (opTableC_down opTabC_emptyC_down)
            Qleft_down hj (h F)))
      hkp (fun k₄ ls₄ O₄ v ρa₄ ρb₄ ρ₄ hk₄ hq hR₄ hc₄ => ?_)
    obtain ⟨hO₄, rfl, hleft⟩ := hq
    subst hO₄
    refine cerwp_det hDE Qmain_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    -- r₅: the parent resumed from the join, with the child's borrow of the joined location; the
    -- scheduler keeps nothing at it
    obtain ⟨σB, junk, hsj, hσB, hfree, himm⟩ := leftV_split hleft m
    obtain ⟨ρs, hsσ, hsj'⟩ := compS_exch hsj hc₄
    rw [show ([] : List FrameRec) ++ O₃ = O₃ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QP (ℍ := ℍ) ℓ (fun ρf => (True ∧ True) ∧ joinFd (Val.loc m) ρf))
      (F₁ := fun ρf => (True ∧ True) ∧ joinFd (Val.loc m) ρf) (fun ρ => ρ = junk)
      (.case .hole omegaE _) (O₁ := O₃) (O₂ := []) (fun _ _ h => by simp at h) hsj'
      (fun ρf y hρf _ hy => by
        have hρf' : ρf = PMap.empty := hρf
        subst hρf'
        obtain rfl := eq_of_compS_empty_left hy
        exact ⟨⟨trivial, trivial⟩, m, rfl, hfree⟩)
      (cerwp_resumeStored (σ := σB) (QP_down ℓ _) (genP ℓ _) (kapStored_le hk₄ hR₄)
        (fun _ _ => ⟨m, rfl, rfl, hσB⟩) (ResU.CompS.comm hsσ) le_rfl (fun _ => trivial))
      rfl (fun k₅ ls₅ O₅ v ρa₅ ρb₅ ρ₅ hk₅ hq hR₅ hc₅ => ?_)
    subst hR₅
    rcases hq with ⟨v₀, rfl, -, rfl, hO₅⟩ | ⟨-, -, -, -, -, -, rfl, -⟩ | ⟨-, -, rfl, -⟩
    · -- the parent finished: the cell owned again, freed; the scheduler's result
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
      simp only [Expr.subst, prim_subst, locV_subst, Kont.plug]
      have hO : O₅ = [] := List.eq_nil_iff_forall_not_mem.mpr hO₅
      subst hO
      exact cerwp_freeX hLE .hole ℓ Val.unit hc₅ (cerwp_val ⟨rfl, himm⟩)
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₂_shift, loc_shift, Kont.plug, omegaE_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _


/-- **The cross-task test, the cancel.** As `prog_orDiverges`, but the scheduler cancels the child
while the parent's lend is live: the cancel unwinds the child's frames and returns the borrow the
child held, which the scheduler hands to the parent at the join. No fuel. -/
theorem progD_orDiverges : OrDiverges (ℍ := ℍ) mainD :=
  cerwp_adequacy (fun _ _ _ _ _ h => h) mainD_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.CrossProg

end
