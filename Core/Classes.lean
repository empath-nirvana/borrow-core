import Core.Dtor
import Core.EffRules
import Core.Closed
import Core.InsertDead

/-!
# Core — the two classes of value type  `[spec §10, §12, §19]`

A value type is **unrestricted** (`VTy.Persistent`) or **linear** (every other type). Contraction
(`Ctx.SplitP.dup`) and weakening (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`) are rules of `CDerives`
exactly at the unrestricted types (`Ctx.SplitP.both_live_iff`, `Ctx.DeadP.live_iff`,
`Ctx.SoloP.live_succ_iff`). A linear type may have a **derived drop** (`DerivedDrop`: `HasDtor`,
licensed by `drop_derives`) or a **derived copy** (`DerivedCopy`: the constant `copy` at `Imm`,
licensed by `copy_derives`). Neither is a further class: each is a property of a linear type.

This file adds no rule to `CDerives` and no semantic definition. It names the classes and states
the derived rules over existing rules.

| fact | statement |
|---|---|
| a derived drop is pure at the row | `dtor_wf`'s type, `HasDtor.close`, `HasDtor.nu`, `kTy_cancel_hasDtor_iff` |
| a destructor holds no operation, and a derived drop is closed | `dtorE_effFree`, `dtorE_closed` |
| a derived copy is a derivation | `copy_derives` |
| `κ` at `lin` is linear with no derived drop | `kTy_lin` |
| `κ` at the default qualifier is linear; its cancel is a derived drop exactly when pure | `kTy_cancel_linear`, `kTy_cancel_hasDtor_iff` |
| `κ` at `unr` is unrestricted | `kTy_unr` |
| the types whose destructor does nothing (the unrestricted ones and the borrows) | `forgettable_iff` |

Three rules absorb a context without using its slots, and none is a drop: `⊤` introduction
(`CDerives.topI`), `absurd` (`CDerives.zeroE`), and the abandonment of a `VTy.OwnFree` context at an
abort (`CDerives.effLet`'s `hW`, `CDerives.effRaise`'s `hd`; `vC_noOwn_of_ownFree`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LifeCtx)

/-! ### Two classes -/

/-- Unrestricted: contraction and weakening are rules of `CDerives` at `A` (`Ctx.SplitP.dup`,
`Ctx.DeadP.drop`, `Ctx.SoloP.skip`); a value holds `∅` (`vP_empty_of_persistent`).
`[spec §10]` -/
abbrev Unrestricted (A : VTy) : Prop := A.Persistent

/-- Linear: every other type. A live slot of linear type is consumed by exactly one rule that
uses it, or absorbed by `⊤`, `absurd` or an abort.  `[spec §10, §12]` -/
abbrev Linear (A : VTy) : Prop := ¬ A.Persistent

theorem unrestricted_or_linear (A : VTy) : Unrestricted A ∨ Linear A := em _

/-- Contraction is a rule exactly at unrestricted types. -/
theorem Ctx.SplitP.both_live_iff {T : VTy} {Γ Γ₁ Γ₂ : Ctx VTy} :
    Ctx.SplitP (⟨T, true⟩ :: Γ) (⟨T, true⟩ :: Γ₁) (⟨T, true⟩ :: Γ₂) ↔
      Unrestricted T ∧ Ctx.SplitP Γ Γ₁ Γ₂ := by
  constructor
  · intro h; cases h with
    | dup hT h => exact ⟨hT, h⟩
  · intro ⟨hT, h⟩; exact .dup hT h

/-- Weakening at the end of a derivation is a rule exactly at unrestricted types. -/
theorem Ctx.DeadP.live_iff {T : VTy} {Γ : Ctx VTy} :
    Ctx.DeadP (⟨T, true⟩ :: Γ) ↔ Unrestricted T ∧ Ctx.DeadP Γ := by
  constructor
  · intro h; cases h with
    | drop hT h => exact ⟨hT, h⟩
  · intro ⟨hT, h⟩; exact .drop hT h

/-- Weakening beside a variable is a rule exactly at unrestricted types. -/
theorem Ctx.SoloP.live_succ_iff {S T : VTy} {Γ : Ctx VTy} {i : Nat} :
    Ctx.SoloP (⟨S, true⟩ :: Γ) (i + 1) T ↔ Unrestricted S ∧ Ctx.SoloP Γ i T := by
  constructor
  · intro h; cases h with
    | skip hS h => exact ⟨hS, h⟩
  · intro ⟨hS, h⟩; exact .skip hS h

/-! ### The derived drop -/

/-- A linear type with a derived drop: `dtorE A : A ⊸ F 1` is a closed `CDerives` term
(`dtor_wf`), and `drop_derives` licenses every inserted drop.  `[spec §12]` -/
def DerivedDrop (A : VTy) : Prop := Linear A ∧ HasDtor A

/-! #### Every destructor holds no operation

`dtorAt` is built from `forget`, the borrow and array constants, `foldOwn` and `foldOwnG`; none
of them holds `perform`, `raise`, `hnd` or `iterate`. The lemmas follow the closedness lemmas of
`Core/FoldOwn.lean` and `Core/FoldOwnGTerm.lean`. -/

theorem bindE_effFree {M N : Expr} (hM : M.effFree = true) (hN : N.effFree = true) :
    (bindE M N).effFree = true := by
  simp [bindE, Expr.effFree, hM, hN]

theorem travO_effFree : ∀ F : FShape, (travO F).1.effFree = true
  | .leaf _ => rfl
  | .refX => rfl
  | .varX => rfl
  | .tensor F G => by
      simp [travO, bindE, Expr.effFree, travO_effFree F, travO_effFree G]
  | .sum F G => by
      simp [travO, bindE, Expr.effFree, travO_effFree F, travO_effFree G]

theorem zX_effFree {B : Expr} (hB : B.effFree = true) : (zX B).1.effFree = true := by
  simp [zX, Expr.effFree, hB]

theorem selfV_effFree {B : Expr} (hB : B.effFree = true) : (selfV B).1.effFree = true := by
  simp [selfV, Expr.effFree, zX_effFree hB]

theorem foldOwnV_effFree (F : FShape) : (foldOwnV F).1.effFree = true := by
  have hB : (fBO F).effFree = true := by
    simp [fBO, bindE, Expr.effFree, travO_effFree F]
  simp [foldOwnV, selfO, Expr.effFree, selfV_effFree hB]

namespace FoldP

theorem tagE_effFree : ∀ (k : Nat) {e : Expr}, e.effFree = true → (tagE k e).effFree = true
  | 0, _, h => h
  | k + 1, _, h => tagE_effFree k h

theorem travOf_effFree {e : Expr} (h : e.effFree = true) : (travOf e).1.effFree = true := by
  simpa [travOf, Expr.effFree] using h

theorem swap_effFree : swap.effFree = true := rfl

theorem stepV_effFree (k : Nat) {t : Val} (ht : t.1.effFree = true) :
    (stepV k t).1.effFree = true := by
  simp [stepV, stepE, bindE, Expr.effFree, ht, swap_effFree,
    tagE_effFree k (e := .inj₂ (.pair (.var 8) (.var 0))) rfl]

theorem arrE_effFree (k : Nat) {f : Val} (hf : f.1.effFree = true) :
    (arrE k f).effFree = true := by
  simp [arrE, bindE, Expr.effFree, hf, Val.i32, unitF, tagE_effFree k (e := .inj₁ .unit) rfl]

theorem callE_effFree (ks : List Bnd) (k : Bnd) : (callE ks k).effFree = true := by
  simp [callE, Expr.effFree, tagE_effFree _ (show (Expr.var 0).effFree = true from rfl)]

theorem tE_effFree (ks : List Bnd) (Bs : Stack) : ∀ A : VTy, (tE ks Bs A).effFree = true
  | .tvar _ => callE_effFree ks _
  | .tensor A B => by
      simp only [tE]; split
      · rfl
      · simp [bindE, Expr.effFree, travOf_effFree (tE_effFree ks Bs A),
          travOf_effFree (tE_effFree ks Bs B)]
  | .sum A B => by
      simp only [tE]; split
      · rfl
      · simp [bindE, Expr.effFree, travOf_effFree (tE_effFree ks Bs A),
          travOf_effFree (tE_effFree ks Bs B)]
  | .ref S => by
      simp only [tE]; split
      · rfl
      · simp [bindE, Expr.effFree, travOf_effFree (tE_effFree ks Bs S)]
  | .fam (.ref S) => by
      simp only [tE]; split
      · rfl
      · exact arrE_effFree _ (stepV_effFree _ (travOf_effFree (tE_effFree ks Bs S)))
  | .mu B => by
      simp only [tE]; split
      · rfl
      · exact callE_effFree ks _
  | .unit | .zero | .thunk _ | .imm _ _ | .mut _ _ | .box _ _ | .bang _ | .unk | .int _ | .opq _ => rfl
  | .fam .unit | .fam (.tensor _ _) | .fam .zero | .fam (.sum _ _) | .fam (.thunk _)
  | .fam (.imm _ _) | .fam (.mut _ _) | .fam (.box _ _) | .fam (.bang _) | .fam .unk
  | .fam (.tvar _) | .fam (.mu _) | .fam (.int _) | .fam (.fam _) | .fam (.opq _) => rfl

theorem travB_effFree (ks : List Bnd) : ∀ k, (travB ks k).1.effFree = true
  | .mu [] => rfl
  | .mu (B :: Bs) => travOf_effFree (tE_effFree ks (B :: Bs) B)
  | .arr _ _ => rfl

theorem projE_effFree : ∀ (n p : Nat) {e : Expr}, e.effFree = true → (projE n p e).effFree = true
  | 0, _, _, h => h
  | 1, _, _, h => h
  | _ + 2, 0, _, h => by simp [projE, Expr.effFree, h]
  | n + 2, p + 1, _, h => by
      simp only [projE, Expr.effFree, h, Bool.true_and]
      exact projE_effFree (n + 1) p rfl

theorem projV_effFree (n p : Nat) : (projV n p).1.effFree = true := by
  simp [projV, Expr.effFree, projE_effFree n p (e := .var 0) rfl]

theorem branch_effFree (ks : List Bnd) (j p : Nat) : ∀ k : Bnd, (branch ks j p k).effFree = true
  | .arr _ _ => by simp [branch, Expr.effFree, projV_effFree]
  | .mu b => by simp [branch, bindE, Expr.effFree, projV_effFree, travB_effFree]

theorem dsp_effFree (ks : List Bnd) : ∀ (r : List Bnd) (j p : Nat), (dsp ks j p r).effFree = true
  | [], _, _ => rfl
  | k :: r, j, p => by
      simp [dsp, Expr.effFree, branch_effFree, dsp_effFree ks r (j + 1) (p + 1)]

theorem selfG_effFree (ks : List Bnd) : (selfG ks).1.effFree = true :=
  selfV_effFree (by simpa [fBG, Expr.effFree] using dsp_effFree ks ks 0 0)

theorem foldOwnGV_effFree (B₀ : VTy) : (foldOwnGV B₀).1.effFree = true := by
  simp [foldOwnGV, tagE, Expr.effFree, selfG_effFree]

theorem tupE_effFree : ∀ (es : List Expr), (∀ e ∈ es, e.effFree = true) →
    (tupE es).effFree = true
  | [], _ => rfl
  | [e], h => h e (by simp)
  | e :: e' :: r, h => by
      simp only [tupE, Expr.effFree, Bool.and_eq_true]
      exact ⟨h e (by simp), tupE_effFree (e' :: r) (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

end FoldP

theorem forget_effFree : forget.effFree = true := rfl

theorem arrAlgE_effFree {d : Expr} (hd : d.effFree = true) : (arrAlgE d).effFree = true := by
  simp [arrAlgE, Expr.effFree, forget_effFree, hd]

mutual
/-- Every destructor, in either mode, holds no operation. -/
theorem dtorAt_effFree : ∀ (b : Bool) (A : VTy), (dtorAt b A).effFree = true
  | b, .tensor A B => by
      simp [dtorAt, Expr.effFree, dtorAt_effFree b A, dtorAt_effFree b B]
  | b, .sum A B => by
      simp [dtorAt, Expr.effFree, dtorAt_effFree b A, dtorAt_effFree b B]
  | b, .ref A => by
      simp only [dtorAt]; split
      · exact dtorAt_effFree true A
      · simp [bindE, Expr.effFree, dtorAt_effFree false A]
  | _, .box _ A => by simp [dtorAt, Expr.effFree, dtorAt_effFree false A]
  | b, .mu A => by
      simp only [dtorAt]; split
      · rfl
      · split
        · simp [Expr.effFree, foldOwnV_effFree, dtorAt_effFree true A]
        · have hs : ∀ e ∈ (Expr.val (.lam (.app (dtorAt true A) (.var 0))) :: algsIn A),
              e.effFree = true := by
            intro e he
            simp only [List.mem_cons] at he
            rcases he with rfl | he
            · simp [Expr.effFree, dtorAt_effFree true A]
            · exact algsIn_effFree A e he
          simp [Expr.effFree, FoldP.foldOwnGV_effFree]
          exact FoldP.tupE_effFree _ hs
  | b, .thunk C => by
      rw [dtorAt_thunk b C]
      match C with
      | .nu (.amp _ (.ret R)) => simp [dtorAt, bindE, Expr.effFree, dtorAt_effFree false R]
      | .nu (.amp _ (.arr _ _)) | .nu (.amp _ (.amp _ _)) | .nu (.amp _ .top)
      | .nu (.amp _ (.all _ _ _)) | .nu (.amp _ (.nu _)) | .nu (.amp _ (.eff _ _ _ _ _ _ _))
      | .nu (.eff _ _ _ _ _ _ _) | .eff _ _ _ _ _ _ _ | .nu (.ret _) | .nu (.arr _ _) | .nu .top
      | .nu (.all _ _ _) | .nu (.nu _) | .ret _ | .arr _ _ | .amp _ _ | .top | .all _ _ _ => rfl
  | b, .fam (.ref A) => by
      simp only [dtorAt]; split
      · rfl
      · simp [Expr.effFree, dtorAt_effFree false A]
  | _, .fam (.mut _ _) => rfl
  | _, .unit | _, .zero | _, .imm _ _ | _, .mut _ _ | _, .bang _ | _, .unk | _, .tvar _
  | _, .int _ | _, .opq _ => rfl
  | _, .fam .unit | _, .fam (.tensor _ _) | _, .fam .zero | _, .fam (.sum _ _)
  | _, .fam (.thunk _) | _, .fam (.imm _ _) | _, .fam (.box _ _) | _, .fam (.bang _)
  | _, .fam .unk | _, .fam (.tvar _) | _, .fam (.mu _) | _, .fam (.int _) | _, .fam (.fam _)
  | _, .fam (.opq _) => rfl

/-- Every algebra `algsIn` lists holds no operation. -/
theorem algsIn_effFree : ∀ (A : VTy), ∀ e ∈ algsIn A, e.effFree = true
  | .tensor A B, e, he => by
      simp only [algsIn, List.mem_append] at he
      exact he.elim (algsIn_effFree A e) (algsIn_effFree B e)
  | .sum A B, e, he => by
      simp only [algsIn, List.mem_append] at he
      exact he.elim (algsIn_effFree A e) (algsIn_effFree B e)
  | .ref S, e, he => by
      simp only [algsIn] at he
      exact algsIn_effFree S e he
  | .fam (.ref S), e, he => by
      simp only [algsIn] at he
      split at he
      · cases he
      · simp only [List.mem_cons] at he
        rcases he with rfl | he
        · simp [Expr.effFree, arrAlgE_effFree (dtorAt_effFree true S)]
        · exact algsIn_effFree S e he
  | .mu B, e, he => by
      simp only [algsIn] at he
      split at he
      · cases he
      · simp only [List.mem_cons] at he
        rcases he with rfl | he
        · simp [Expr.effFree, dtorAt_effFree true B]
        · exact algsIn_effFree B e he
  | .unit, _, he | .zero, _, he | .thunk _, _, he | .imm _ _, _, he | .mut _ _, _, he
  | .box _ _, _, he | .bang _, _, he | .unk, _, he | .tvar _, _, he | .int _, _, he
  | .opq _, _, he => by simp [algsIn] at he
  | .fam .unit, _, he | .fam (.tensor _ _), _, he | .fam .zero, _, he | .fam (.sum _ _), _, he
  | .fam (.thunk _), _, he | .fam (.imm _ _), _, he | .fam (.mut _ _), _, he
  | .fam (.box _ _), _, he | .fam (.bang _), _, he | .fam .unk, _, he | .fam (.tvar _), _, he
  | .fam (.mu _), _, he | .fam (.int _), _, he | .fam (.fam _), _, he
  | .fam (.opq _), _, he => by simp [algsIn] at he
end

/-- `dtorE A` holds no `perform`, `raise`, `hnd` or `iterate`, at every `A`: the syntactic side
condition `TiedDer.ofCDerives` (`Frontend/Check/Tied.lean`) asks of an inserted drop. It is not
the statement that a derived drop is pure at the row: that is carried by `dtor_wf`'s type
`A ⊸ F 1` at the empty row, by `HasDtor.close` and `HasDtor.nu` asking a `.ret` cancel
(`Core/Dtor.lean`), and at `κ` by `kTy_cancel_hasDtor_iff`.  `[spec §12]` -/
theorem dtorE_effFree (A : VTy) : (dtorE A).effFree = true :=
  dtorAt_effFree false A

/-- A derived drop is a closed term: `dtor_wf` types it at the empty context
(`closedAt_of_derives`).  `[spec §12]` -/
theorem dtorE_closed {A : VTy} (h : HasDtor A) : closedAt 0 (dtorE A) = true :=
  closedAt_of_derives (dtor_wf (Δ := default) h (Γ := []) .nil)

/-! ### The derived copy at `Imm` -/

/-- A linear type with a derived copy: a kernel constant duplicates it.  `[spec §9, §10]` -/
inductive DerivedCopy : VTy → Prop where
  /-- `Imm @a A`, by `copy` (`CDerives.copy`). -/
  | imm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.imm a A)
  /-- `ArrayImm @a A`, by `array_copy` (`CDerives.arrCopy`). -/
  | arrImm (a : Lifetime.Life) (A : VTy) : DerivedCopy (.fam (.imm a A))

/-- A type with a derived copy is linear. -/
theorem DerivedCopy.linear {A : VTy} (h : DerivedCopy A) : Linear A := by
  cases h <;> simp [VTy.persistent]

/-- The copy constant at a `DerivedCopy` type. -/
def copyC : VTy → Expr
  | .fam _ => .val copyV
  | _ => copy

/-- `let (x₁, x₂) = copyC A xᵢ; e`: the two copies are variables `0` and `1` of `e`, and `e`'s
other variables are the context's, past the pair's dead slot. -/
def copyE (A : VTy) (i : Nat) (e : Expr) : Expr :=
  bindE (.app (copyC A) (.var i)) (.letpair (.var 0) (e.shift 1 2))

/-- The copy constant is a derivation at every dead context. -/
theorem copyC_wf {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hA : DerivedCopy A) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (copyC A) (.val (.lolli A (.tensor A A))) := by
  cases hA with
  | imm a A => exact .copy hΓ
  | arrImm a A => exact .bangE (.arrCopy a A hΓ)

/-- **A copy is a `CDerives` derivation**: the derived rule for every inserted copy.
`[spec §9, §10]` -/
theorem copy_derives {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {i : Nat} {A : VTy} {e : Expr} {C : CTy}
    (hA : DerivedCopy A) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i A)
    (h : CDerives Δ (⟨A, true⟩ :: ⟨A, true⟩ :: Γ₂) e (.comp C)) :
    CDerives Δ Γ (copyE A i e) (.comp C) := by
  have hM : CDerives Δ Γ₁ (.app (copyC A) (.var i)) (.comp (.ret (.tensor A A))) :=
    .ret (.lolliE (split_kill' Γ₁).toP (.var hx) (copyC_wf hA (kill_dead Γ₁).toP))
  have he : CDerives Δ (⟨A, true⟩ :: ⟨A, true⟩ :: ⟨.tensor A A, false⟩ :: Γ₂) (e.shift 1 2)
      (.comp C) :=
    CDerives.insert_dead (Γd := [⟨.tensor A A, false⟩]) (.cons .nil) h
      [⟨A, true⟩, ⟨A, true⟩] Γ₂ rfl
  have hN : CDerives Δ (⟨.tensor A A, true⟩ :: Γ₂) (.letpair (.var 0) (e.shift 1 2)) (.comp C) :=
    .tensorE (.left (split_kill Γ₂).toP) (.var (.here (kill_dead Γ₂).toP)) he
  exact .bind hs hM hN

/-! ### Continuation qualifiers  `[spec §19, §27]` -/

/-- `κ` at `lin` is linear, with no derived drop: it must be resumed. -/
theorem kTy_lin {S : Row} {R B : VTy} {F : CTy} :
    Linear (kTy S R .lin B F) ∧ ¬ HasDtor (kTy S R .lin B F) := by
  refine ⟨by simp [kTy, VTy.persistent], fun h => ?_⟩
  simp only [kTy] at h
  cases h

/-- `κ` at the default qualifier is linear, with a cancel branch: the `A & 1` encoding. -/
theorem kTy_cancel_linear {S : Row} {R B : VTy} {F : CTy} : Linear (kTy S R .cancel B F) := by
  simp [kTy, VTy.persistent]

/-- The cancel of `κ` at the default qualifier is a derived drop exactly when it is pure: when
the cancel row is empty. -/
theorem kTy_cancel_hasDtor_iff {S : Row} {R B : VTy} {F : CTy} :
    HasDtor (kTy S R .cancel B F) ↔ cancelTy S F = .ret .unit := by
  simp only [kTy]
  constructor
  · intro h
    generalize hc : cancelTy S F = c at h
    cases h
    rfl
  · intro h
    rw [h]
    exact .close

/-- `κ` at `unr` is unrestricted. -/
theorem kTy_unr {S : Row} {R B : VTy} {F : CTy} : Unrestricted (kTy S R .unr B F) := rfl

/-! ### The types whose destructor does nothing -/

/-- `Forgettable` (`Core/Records.lean`) is the types that hold no owned cell and have a destructor:
`VTy.OwnFree` without the opaque host types, which have no destructor.  `[spec §12, §19]` -/
theorem forgettable_iff {A : VTy} : Forgettable A ↔ A.OwnFree ∧ HasDtor A := by
  constructor
  · intro h
    refine ⟨?_, hasDtor_of_forgettable h⟩
    induction h with
    | unit => exact .unit
    | zero => exact .zero
    | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
    | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
    | imm => exact .imm _ _
    | «mut» => exact .mut _ _
    | unk => exact .unk
    | bang => exact .bang _
    | int => exact .int _
  · intro ⟨hD, hH⟩
    induction hD with
    | unit => exact .unit
    | zero => exact .zero
    | int => exact .int
    | unk => exact .unk
    | opq => cases hH
    | bang => exact .bang
    | imm => exact .imm
    | «mut» => exact .mut
    | tensor _ _ ih₁ ih₂ =>
        cases hH with
        | tensor h₁ h₂ => exact .tensor (ih₁ h₁) (ih₂ h₂)
    | sum _ _ ih₁ ih₂ =>
        cases hH with
        | sum h₁ h₂ => exact .sum (ih₁ h₁) (ih₂ h₂)

end BoCa.Fig16.LogRel.Core

end
