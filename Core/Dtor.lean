import Core.Records
import Core.Folds
import Core.FoldOwnG

/-!
# Core — destructors  `[spec §12]`

`dtorE T : T ⊸ F 1` is a closed term for every type `T` with `HasDtor T`, and `dtor_wf` types it
in `CDerives` at every lifetime context and every dead context: it is an ordinary linear program
built from existing rules. The checker inserts `dropE T i e = (dtorE T xᵢ; e)` where an owned
value goes unused (`drop_derives`), so the elaborated term uses the value exactly once.

| type | destructor |
|---|---|
| `1`, `0`, `I32`, `I64`, `Unk`, `!A` | `forget` (the slot is persistent) |
| `Imm @a A`, `Mut @a A` | `forget` (the borrow axiom constant: ends the loan, frees nothing) |
| `A ⊗ B`, `A ⊕ B`, `[@a] A` | componentwise |
| `Ref A` | `free`, then the destructor of `A` |
| `μX. T`, `T` in `FShape` | `foldOwn` whose algebra is the destructor of `T[1/X]` |
| `μX. T`, `T` in `P`, not in `FShape` | `foldOwnG` whose algebra at each key is the destructor of the key's body at results `1` |
| `U(C & F 1)` | `close`: force, then the second projection |
| `U(νX. C & F R)`, `R` closed | `close`, then the destructor of the residual `R` |
| `Array A` | `array_free` with the destructor of `A` as the consumer |
| `ArrayImm @a A` | `array_forget` |

The first two rows are the forgettable types, whose destructor does nothing; every type of
`Forgettable` (`Core/Records.lean`) is one (`hasDtor_of_forgettable`). The other rows deallocate or
run `close` code. `U C` in general has no destructor: a thunk of `F A` or of `A ⊸ C` can only be
disposed of by running it. Nor does `μ` outside the fold class `P` (for example `X` under `U`).

The `alg` mode `dtorAt true A` is the destructor of `A⟨1⟩` (`FoldP.resO dtorAlgs`): `A` with
each recursive position (a variable, a `μ` or an array that is not closed) at its result `1`
(`algE_eqP`). At a `μ` whose body is in `FShape` (`fshapeB`) the destructor is `foldOwn`, its
algebra the `alg` mode of the body. At any other body of `P` it is `foldOwnG`, with one
algebra per key (`FoldP.keys`): the root's and every inner `μ`'s are the `alg` mode of its body,
an array key's the destructor of `1 ⊕ (1 ⊗ S⟨1⟩)` (`arrAlgE`). `algsIn` lists the inner keys'
algebras by the same recursion as `FoldP.keysIn` (`algsIn_eq`), so `dtorAt` and `algsIn` are one
mutual structural recursion on `VTy`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The shape of a `μ` body -/

/-- The `FShape` reading of a `μ` body: `Ref X` and `X` at variable `0`, `⊗` and `⊕` through,
every other type a leaf. -/
def toFShape : VTy → FShape
  | .tensor A B => .tensor (toFShape A) (toFShape B)
  | .sum A B => .sum (toFShape A) (toFShape B)
  | .ref (.tvar 0) => .refX
  | .tvar 0 => .varX
  | A => .leaf A

theorem toFShape_ty : ∀ A : VTy, (toFShape A).ty = A
  | .tensor A B => by simp [toFShape, FShape.ty, toFShape_ty A, toFShape_ty B]
  | .sum A B => by simp [toFShape, FShape.ty, toFShape_ty A, toFShape_ty B]
  | .ref (.tvar 0) => rfl
  | .ref (.tvar (_ + 1)) => rfl
  | .tvar 0 => rfl
  | .tvar (_ + 1) => rfl
  | .unit => rfl
  | .zero => rfl
  | .thunk _ => rfl
  | .ref .unit => rfl
  | .ref (.tensor _ _) => rfl
  | .ref .zero => rfl
  | .ref (.sum _ _) => rfl
  | .ref (.thunk _) => rfl
  | .ref (.ref _) => rfl
  | .ref (.imm _ _) => rfl
  | .ref (.mut _ _) => rfl
  | .ref (.box _ _) => rfl
  | .ref (.bang _) => rfl
  | .ref .unk => rfl
  | .ref (.mu _) => rfl
  | .ref (.int _) => rfl
  | .ref (.opq _) => rfl
  | .ref (.fam _) => rfl
  | .imm _ _ => rfl
  | .mut _ _ => rfl
  | .box _ _ => rfl
  | .bang _ => rfl
  | .unk => rfl
  | .mu _ => rfl
  | .int _ => rfl
  | .opq _ => rfl
  | .fam _ => rfl

/-! ### The destructors -/

/-- `FShape.WF`, decided. -/
def FShape.wfDec : FShape → Bool
  | .leaf A => FoldP.clB 0 A
  | .refX => true
  | .varX => true
  | .tensor F G => FShape.wfDec F && FShape.wfDec G
  | .sum F G => FShape.wfDec F && FShape.wfDec G

theorem FShape.wfDec_sound : ∀ F : FShape, FShape.wfDec F = true → F.WF
  | .leaf A, h => (FoldP.clB_iff 0 A).mp h
  | .refX, _ => trivial
  | .varX, _ => trivial
  | .tensor F G, h => by
      simp only [FShape.wfDec, Bool.and_eq_true] at h
      exact ⟨wfDec_sound F h.1, wfDec_sound G h.2⟩
  | .sum F G, h => by
      simp only [FShape.wfDec, Bool.and_eq_true] at h
      exact ⟨wfDec_sound F h.1, wfDec_sound G h.2⟩

/-- A `μ` body is in `FShape`: its `FShape` reading is well formed and is not `X`. -/
def fshapeB (A : VTy) : Bool :=
  FShape.wfDec (toFShape A) && match toFShape A with
    | .varX => false
    | _ => true

theorem fshapeB_sound {A : VTy} (h : fshapeB A = true) :
    (toFShape A).WF ∧ (toFShape A).Guarded := by
  simp only [fshapeB, Bool.and_eq_true] at h
  refine ⟨FShape.wfDec_sound _ h.1, ?_⟩
  have h₂ := h.2
  revert h₂
  cases toFShape A <;> simp [FShape.Guarded]

/-- `X`, the `μ`'s own variable. -/
def isX0 : VTy → Bool
  | .tvar 0 => true
  | _ => false

/-- The destructor of `1 ⊕ (1 ⊗ S)`, with `d` the destructor of `S`: an array key's algebra. -/
def arrAlgE (d : Expr) : Expr :=
  .val (.lam (.case (.var 0) (.app forget (.var 0))
    (.app (.val (.lam (.letpair (.var 0) (.seq (.app forget (.var 1)) (.app d (.var 0)))))) (.var 0))))

mutual
/-- The destructor of `T` (`alg = false`), or of `T⟨1⟩` for a position `T` of a `μ` body
(`alg = true`: `forget` at each recursive position). -/
def dtorAt : Bool → VTy → Expr
  | alg, .tensor A B => .val (.lam (.letpair (.var 0)
      (.seq (.app (dtorAt alg A) (.var 1)) (.app (dtorAt alg B) (.var 0)))))
  | alg, .sum A B => .val (.lam (.case (.var 0) (.app (dtorAt alg A) (.var 0)) (.app (dtorAt alg B) (.var 0))))
  | alg, .ref A => if alg && !FoldP.clB 0 A then dtorAt true A else
      .val (.lam (bindE (.app (.val (.prim .free)) (.var 0)) (.app (dtorAt false A) (.var 0))))
  | _, .box _ A => .val (.lam (.app (dtorAt false A) (.var 0)))
  | alg, .mu A => if alg && !FoldP.clB 0 (.mu A) then forget else
      if fshapeB A then .val (.lam (.app (.app (.val (foldOwnV (toFShape A)))
        (.val (.lam (.app (dtorAt true A) (.var 0))))) (.var 0)))
      else .val (.lam (.app (.app (.val (FoldP.foldOwnGV A))
        (FoldP.tupE (.val (.lam (.app (dtorAt true A) (.var 0))) :: algsIn A))) (.var 0)))
  | _, .thunk (.nu (.amp _ (.ret R))) => .val (.lam
      (bindE (.app (.var 0) (.val (.inj₂ .unit))) (.app (dtorAt false R) (.var 0))))
  | _, .thunk _ => .val (.lam (.app (.var 0) (.val (.inj₂ .unit))))
  | alg, .fam (.ref A) => if alg && !FoldP.clB 0 A then forget else
      .val (.lam (.app (.val (.prim .drop))
        (.pair (.val (.lam (.app (dtorAt false A) (.var 0)))) (.var 0))))
  | _, .fam (.mut _ _) => .val (.lam (elet
      (.app (.val (.prim .idx)) (.pair (.var 0) (.val (Val.i32 0xFFFFFFFF))))
      (.case (.var 0) (.app forget (.var 0)) (.var 0))))
  | _, _ => forget

/-- The algebras of the keys of a position, in the order of `FoldP.keysIn`: at a `μ` key, the
`alg` mode of its body; at an array key, the destructor of `1 ⊕ (1 ⊗ S⟨1⟩)`. -/
def algsIn : VTy → List Expr
  | .tensor A B => algsIn A ++ algsIn B
  | .sum A B => algsIn A ++ algsIn B
  | .ref S => algsIn S
  | .fam (.ref S) => if FoldP.clB 0 S then [] else
      .val (.lam (.app (arrAlgE (dtorAt true S)) (.var 0))) :: algsIn S
  | .mu B => if FoldP.clB 0 (.mu B) then [] else
      .val (.lam (.app (dtorAt true B) (.var 0))) :: algsIn B
  | _ => []
end

/-- At a thunk the destructor does not depend on the mode. -/
theorem dtorAt_thunk : ∀ (b : Bool) (C : CTy), dtorAt b (.thunk C) = dtorAt false (.thunk C)
  | _, .nu (.amp _ (.ret _)) | _, .nu (.amp _ (.arr _ _)) | _, .nu (.amp _ (.amp _ _))
  | _, .nu (.amp _ .top) | _, .nu (.amp _ (.all _ _ _)) | _, .nu (.amp _ (.nu _))
  | _, .nu (.amp _ (.eff _ _ _ _ _ _ _)) | _, .nu (.eff _ _ _ _ _ _ _) | _, .eff _ _ _ _ _ _ _
  | _, .nu (.ret _) | _, .nu (.arr _ _) | _, .nu .top | _, .nu (.all _ _ _) | _, .nu (.nu _)
  | _, .ret _ | _, .arr _ _ | _, .amp _ _ | _, .top | _, .all _ _ _ => rfl

/-- The destructor of `T`, a closed `λ`.  `[spec §12]` -/
abbrev dtorE : VTy → Expr := dtorAt false

/-- The `alg` mode: the destructor of a position of a `μ` body at results `1`. -/
abbrev algE : VTy → Expr := dtorAt true

/-- The results `1` at every key: the fold the destructor is. -/
def dtorAlgs : FoldP.Algs := ⟨fun _ => .unit, fun _ _ => .unit⟩

/-- At a closed type the two modes agree. -/
theorem algE_closed : ∀ (A : VTy), FoldP.clB 0 A = true → dtorAt true A = dtorAt false A
  | .tensor A B, h => by
      simp only [FoldP.clB, Bool.and_eq_true] at h
      simp only [dtorAt]
      rw [algE_closed A h.1, algE_closed B h.2]
  | .sum A B, h => by
      simp only [FoldP.clB, Bool.and_eq_true] at h
      simp only [dtorAt]
      rw [algE_closed A h.1, algE_closed B h.2]
  | .ref A, h => by
      simp only [FoldP.clB] at h
      simp [dtorAt, h]
  | .fam (.ref A), h => by
      simp only [FoldP.clB] at h
      simp [dtorAt, h]
  | .mu A, h => by simp [dtorAt, h]
  | .thunk C, _ => dtorAt_thunk true C
  | .tvar _, h => by simp [FoldP.clB] at h
  | .unit, _ | .zero, _ | .box _ _, _ | .bang _, _ | .unk, _ | .int _, _ | .opq _, _
  | .imm _ _, _ | .mut _ _, _ => rfl
  | .fam .unit, _ | .fam (.tensor _ _), _ | .fam .zero, _ | .fam (.sum _ _), _
  | .fam (.thunk _), _ | .fam (.imm _ _), _ | .fam (.mut _ _), _ | .fam (.box _ _), _
  | .fam (.bang _), _ | .fam .unk, _ | .fam (.tvar _), _ | .fam (.mu _), _ | .fam (.int _), _
  | .fam (.fam _), _ | .fam (.opq _), _ => rfl

/-- **The algebra is the destructor of the position at results `1`.** -/
theorem algE_eqP (Bs : FoldP.Stack) :
    ∀ A : VTy, dtorAt true A = dtorAt false (FoldP.resO dtorAlgs Bs A)
  | .tvar _ => rfl
  | .tensor A B => by
      by_cases h : FoldP.clB 0 (.tensor A B) = true
      · rw [FoldP.resO_leaf dtorAlgs Bs h]; exact algE_closed _ h
      · simp only [FoldP.resO, if_neg h]
        simp only [dtorAt]
        rw [algE_eqP Bs A, algE_eqP Bs B]
  | .sum A B => by
      by_cases h : FoldP.clB 0 (.sum A B) = true
      · rw [FoldP.resO_leaf dtorAlgs Bs h]; exact algE_closed _ h
      · simp only [FoldP.resO, if_neg h]
        simp only [dtorAt]
        rw [algE_eqP Bs A, algE_eqP Bs B]
  | .ref S => by
      by_cases h : FoldP.clB 0 S = true
      · have h' : FoldP.clB 0 (.ref S) = true := h
        rw [FoldP.resO_leaf dtorAlgs Bs h']; exact algE_closed _ h'
      · simp only [FoldP.resO, if_neg h]
        simp only [dtorAt, h, Bool.not_false, Bool.and_self, if_true]
        exact algE_eqP Bs S
  | .fam (.ref S) => by
      by_cases h : FoldP.clB 0 S = true
      · have h' : FoldP.clB 0 (.fam (.ref S)) = true := h
        rw [FoldP.resO_leaf dtorAlgs Bs h']; exact algE_closed _ h'
      · simp [FoldP.resO, h, dtorAt, dtorAlgs]
  | .mu B => by
      by_cases h : FoldP.clB 0 (.mu B) = true
      · rw [FoldP.resO_leaf dtorAlgs Bs h]; exact algE_closed _ h
      · simp [FoldP.resO, h, dtorAt, dtorAlgs]
  | .thunk C => dtorAt_thunk true C
  | .unit | .zero | .box _ _ | .bang _ | .unk | .int _ | .opq _ | .imm _ _ | .mut _ _ => rfl
  | .fam .unit | .fam (.tensor _ _) | .fam .zero | .fam (.sum _ _) | .fam (.thunk _)
  | .fam (.imm _ _) | .fam (.mut _ _) | .fam (.box _ _) | .fam (.bang _) | .fam .unk
  | .fam (.tvar _) | .fam (.mu _) | .fam (.int _) | .fam (.fam _) | .fam (.opq _) => rfl

/-- A closed type's `FShape` reading has no recursive position. -/
theorem toFShape_resO_closed (R : VTy) : ∀ {A : VTy}, FoldP.clB 0 A = true → (toFShape A).resO R = A
  | .tensor A B, h => by
      simp only [FoldP.clB, Bool.and_eq_true] at h
      simp [toFShape, FShape.resO, toFShape_resO_closed R h.1, toFShape_resO_closed R h.2]
  | .sum A B, h => by
      simp only [FoldP.clB, Bool.and_eq_true] at h
      simp [toFShape, FShape.resO, toFShape_resO_closed R h.1, toFShape_resO_closed R h.2]
  | .tvar _, h => by simp [FoldP.clB] at h
  | .ref (.tvar _), h => by simp [FoldP.clB] at h
  | .ref .unit, _ | .ref (.tensor _ _), _ | .ref .zero, _ | .ref (.sum _ _), _
  | .ref (.thunk _), _ | .ref (.ref _), _ | .ref (.imm _ _), _ | .ref (.mut _ _), _
  | .ref (.box _ _), _ | .ref (.bang _), _ | .ref .unk, _ | .ref (.mu _), _ | .ref (.int _), _
  | .ref (.opq _), _ | .ref (.fam _), _ => rfl
  | .unit, _ | .zero, _ | .thunk _, _ | .imm _ _, _ | .mut _ _, _ | .box _ _, _ | .bang _, _
  | .unk, _ | .mu _, _ | .int _, _ | .opq _, _ | .fam _, _ => rfl

/-- At a body in `FShape`, the result type at `1` is the `FShape` one. -/
theorem resO_toFShape (Bs : FoldP.Stack) :
    ∀ (A : VTy), (toFShape A).WF → FoldP.resO dtorAlgs Bs A = (toFShape A).resO .unit
  | .tensor A B, h => by
      by_cases hc : FoldP.clB 0 (.tensor A B) = true
      · rw [FoldP.resO_leaf dtorAlgs Bs hc, toFShape_resO_closed .unit hc]
      · simp only [toFShape, FShape.WF] at h
        simp only [FoldP.resO, if_neg hc, toFShape, FShape.resO, resO_toFShape Bs A h.1,
          resO_toFShape Bs B h.2]
  | .sum A B, h => by
      by_cases hc : FoldP.clB 0 (.sum A B) = true
      · rw [FoldP.resO_leaf dtorAlgs Bs hc, toFShape_resO_closed .unit hc]
      · simp only [toFShape, FShape.WF] at h
        simp only [FoldP.resO, if_neg hc, toFShape, FShape.resO, resO_toFShape Bs A h.1,
          resO_toFShape Bs B h.2]
  | .ref (.tvar 0), _ => by simp [FoldP.resO, FoldP.clB, toFShape, FShape.resO, dtorAlgs]
  | .tvar 0, _ => by simp [FoldP.resO, toFShape, FShape.resO, dtorAlgs]
  | .tvar (_ + 1), h => by simp [toFShape, FShape.WF, VTy.Cl] at h
  | .ref (.tvar (_ + 1)), h => by simp [toFShape, FShape.WF, VTy.Cl] at h
  | .ref .unit, h | .ref (.tensor _ _), h | .ref .zero, h | .ref (.sum _ _), h
  | .ref (.thunk _), h | .ref (.ref _), h | .ref (.imm _ _), h | .ref (.mut _ _), h
  | .ref (.box _ _), h | .ref (.bang _), h | .ref .unk, h | .ref (.mu _), h | .ref (.int _), h
  | .ref (.opq _), h | .ref (.fam _), h | .unit, h | .zero, h | .thunk _, h | .imm _ _, h
  | .mut _ _, h | .box _ _, h | .bang _, h | .unk, h | .mu _, h | .int _, h | .opq _, h
  | .fam _, h => by
      have hc := (FoldP.clB_iff 0 _).mpr h
      rw [FoldP.resO_leaf dtorAlgs Bs hc]
      exact (toFShape_resO_closed .unit hc).symm

/-- The algebra is the destructor of `T[1/X]`, at a body in `FShape`. -/
theorem algE_eq {A : VTy} (h : (toFShape A).WF) : algE A = dtorE ((toFShape A).resO .unit) := by
  show dtorAt true A = dtorAt false _
  rw [algE_eqP [A] A, resO_toFShape [A] A h]

/-- A body in `FShape` has no key inside it. -/
theorem keysIn_toFShape (Bs : FoldP.Stack) :
    ∀ (A : VTy), (toFShape A).WF → FoldP.keysIn Bs A = []
  | .tensor A B, h => by
      simp only [toFShape, FShape.WF] at h
      simp [FoldP.keysIn, keysIn_toFShape Bs A h.1, keysIn_toFShape Bs B h.2]
  | .sum A B, h => by
      simp only [toFShape, FShape.WF] at h
      simp [FoldP.keysIn, keysIn_toFShape Bs A h.1, keysIn_toFShape Bs B h.2]
  | .ref (.tvar 0), _ => rfl
  | .tvar _, _ => rfl
  | .ref (.tvar (_ + 1)), h => by simp [toFShape, FShape.WF, VTy.Cl] at h
  | .ref .unit, h | .ref (.tensor _ _), h | .ref .zero, h | .ref (.sum _ _), h
  | .ref (.thunk _), h | .ref (.ref _), h | .ref (.imm _ _), h | .ref (.mut _ _), h
  | .ref (.box _ _), h | .ref (.bang _), h | .ref .unk, h | .ref (.mu _), h | .ref (.int _), h
  | .ref (.opq _), h | .ref (.fam _), h | .unit, h | .zero, h | .thunk _, h | .imm _ _, h
  | .mut _ _, h | .box _ _, h | .bang _, h | .unk, h | .mu _, h | .int _, h | .opq _, h
  | .fam _, h => keysIn_closed Bs ((FoldP.clB_iff 0 _).mpr h)
where
  keysIn_closed (Bs : FoldP.Stack) : ∀ {A : VTy}, FoldP.clB 0 A = true → FoldP.keysIn Bs A = []
    | .tensor A B, h => by
        simp only [FoldP.clB, Bool.and_eq_true] at h
        simp [FoldP.keysIn, keysIn_closed Bs h.1, keysIn_closed Bs h.2]
    | .sum A B, h => by
        simp only [FoldP.clB, Bool.and_eq_true] at h
        simp [FoldP.keysIn, keysIn_closed Bs h.1, keysIn_closed Bs h.2]
    | .ref S, h => keysIn_closed Bs (A := S) h
    | .fam (.ref S), h => by simp [FoldP.keysIn, show FoldP.clB 0 S = true from h]
    | .mu B, h => by simp [FoldP.keysIn, h]
    | .tvar _, h => by simp [FoldP.clB] at h
    | .unit, _ | .zero, _ | .thunk _, _ | .imm _ _, _ | .mut _ _, _ | .box _ _, _ | .bang _, _
    | .unk, _ | .int _, _ | .opq _, _ => rfl
    | .fam .unit, _ | .fam (.tensor _ _), _ | .fam .zero, _ | .fam (.sum _ _), _
    | .fam (.thunk _), _ | .fam (.imm _ _), _ | .fam (.mut _ _), _ | .fam (.box _ _), _
    | .fam (.bang _), _ | .fam .unk, _ | .fam (.tvar _), _ | .fam (.mu _), _ | .fam (.int _), _
    | .fam (.fam _), _ | .fam (.opq _), _ => rfl

/-- The algebra of a key. -/
def keyAlg : FoldP.Bnd → Expr
  | .mu [] => .unit
  | .mu (B :: _) => .val (.lam (.app (dtorAt true B) (.var 0)))
  | .arr _ S => .val (.lam (.app (arrAlgE (dtorAt true S)) (.var 0)))

/-- `algsIn` lists the algebras of `keysIn`'s keys. -/
theorem algsIn_eq : ∀ (A : VTy) (Bs : FoldP.Stack), algsIn A = (FoldP.keysIn Bs A).map keyAlg
  | .tensor A B, Bs => by simp [algsIn, FoldP.keysIn, algsIn_eq A Bs, algsIn_eq B Bs]
  | .sum A B, Bs => by simp [algsIn, FoldP.keysIn, algsIn_eq A Bs, algsIn_eq B Bs]
  | .ref S, Bs => by simp [algsIn, FoldP.keysIn, algsIn_eq S Bs]
  | .fam (.ref S), Bs => by
      by_cases h : FoldP.clB 0 S = true
      · simp [algsIn, FoldP.keysIn, h]
      · simp [algsIn, FoldP.keysIn, h, keyAlg, algsIn_eq S Bs]
  | .mu B, Bs => by
      by_cases h : FoldP.clB 0 (.mu B) = true
      · simp [algsIn, FoldP.keysIn, h]
      · simp only [algsIn, FoldP.keysIn, if_neg h, List.map_cons, keyAlg, algsIn_eq B (B :: Bs)]
  | .unit, _ | .zero, _ | .thunk _, _ | .imm _ _, _ | .mut _ _, _ | .box _ _, _ | .bang _, _
  | .unk, _ | .int _, _ | .opq _, _ | .tvar _, _ => rfl
  | .fam .unit, _ | .fam (.tensor _ _), _ | .fam .zero, _ | .fam (.sum _ _), _
  | .fam (.thunk _), _ | .fam (.imm _ _), _ | .fam (.mut _ _), _ | .fam (.box _ _), _
  | .fam (.bang _), _ | .fam .unk, _ | .fam (.tvar _), _ | .fam (.mu _), _ | .fam (.int _), _
  | .fam (.fam _), _ | .fam (.opq _), _ => rfl

/-- The destructor of a `μ` whose body is in `FShape`: `foldOwn` with the `alg` mode. -/
theorem dtorE_mu_F {A : VTy} (h : fshapeB A = true) :
    dtorE (.mu A) = .val (.lam (.app (.app (.val (foldOwnV (toFShape A)))
      (.val (.lam (.app (algE A) (.var 0))))) (.var 0))) := by
  simp [dtorE, dtorAt, h]

/-- The destructor of a `μ` whose body is in `P` and not in `FShape`: `foldOwnG` with one algebra
per key. -/
theorem dtorE_mu_P {A : VTy} (h : fshapeB A = false) :
    dtorE (.mu A) = .val (.lam (.app (.app (.val (FoldP.foldOwnGV A))
      (FoldP.tupE ((FoldP.keys A).map keyAlg))) (.var 0))) := by
  simp only [dtorE, dtorAt, Bool.false_and, Bool.false_eq_true, if_false, h]
  rw [algsIn_eq A [A]]
  rfl

/-- An array key's algebra is the destructor of `1 ⊕ (1 ⊗ S⟨1⟩)`. -/
theorem arrAlgE_eq (T : VTy) : arrAlgE (dtorE T) = dtorE (.sum .unit (.tensor .unit T)) := rfl

/-! ### Which types have one -/

/-- `T` has a destructor: `dtorE T` consumes a value of `T`.  `[spec §12]` -/
inductive HasDtor : VTy → Prop where
  | unit : HasDtor .unit
  | zero : HasDtor .zero
  | int {w} : HasDtor (.int w)
  | unk : HasDtor .unk
  | bang {A} : HasDtor (.bang A)
  | imm {a A} : HasDtor (.imm a A)
  | «mut» {a A} : HasDtor (.mut a A)
  | tensor {A B} : HasDtor A → HasDtor B → HasDtor (.tensor A B)
  | sum {A B} : HasDtor A → HasDtor B → HasDtor (.sum A B)
  | box {a A} : HasDtor A → HasDtor (.box a A)
  /-- An owned cell: freed, then its content dropped. -/
  | ref {A} : HasDtor A → HasDtor (.ref A)
  /-- An inductive type of the fold class `P`: the owned fold with results `1`, its algebra at
  each key the destructor of the key's body (an array key's element type) at results `1`.
  `[spec §6, §12]` -/
  | mu {A} (hP : FoldP.PBody A) (h : HasDtor (FoldP.resO dtorAlgs [A] A))
      (hmu : ∀ B Bs, FoldP.Bnd.mu (B :: Bs) ∈ FoldP.keysIn [A] A →
        HasDtor (FoldP.resO dtorAlgs (B :: Bs) B))
      (harr : ∀ Bs S, FoldP.Bnd.arr Bs S ∈ FoldP.keysIn [A] A →
        HasDtor (FoldP.resO dtorAlgs Bs S)) : HasDtor (.mu A)
  /-- A computation with a `close` component. -/
  | close {C} : HasDtor (.thunk (.amp C (.ret .unit)))
  /-- Codata `νX. C & F R` whose `close` returns a closed residual `R` with a destructor:
  `close`, then the destructor of `R`.  `[spec §7, §12]` -/
  | nu {C R} (hC : (CTy.amp C (.ret R)).NuOk) (hRc : R.Cl 0) (h : HasDtor R) :
      HasDtor (.thunk (.nu (.amp C (.ret R))))
  /-- An array: each element to the destructor of `A`, then the cells freed (`array_free`).
  `[spec §9, §12]` -/
  | array {A} (h : HasDtor A) : HasDtor (.fam (.ref A))
  /-- A family of leaf views, forgotten (`array_forget`).  `[spec §9, §12]` -/
  | arrayImm {a A} : HasDtor (.fam (.imm a A))
  /-- A family of `mut` leaves, forgotten: `slice_get_mut` at an index past every family's
  length (`2³² − 1`) consumes it, and `forget` ends the leaf it would hand out.  `[spec §9, §12]` -/
  | arrayMut {a A} : HasDtor (.fam (.mut a A))

/-- **`HasDtor.mu` at `FShape`**: a body in `FShape` whose `T[1/X]` has a destructor. -/
theorem HasDtor.muF {A : VTy} (hF : (toFShape A).WF) (hG : (toFShape A).Guarded)
    (h : HasDtor ((toFShape A).resO .unit)) : HasDtor (.mu A) := by
  have hP : FoldP.PBody A := by
    have := FoldP.pBody_of_FShape hF hG
    rwa [toFShape_ty] at this
  refine .mu hP (by rwa [resO_toFShape [A] A hF]) (fun B Bs hm => ?_) (fun Bs S hm => ?_)
  · rw [keysIn_toFShape [A] A hF] at hm; cases hm
  · rw [keysIn_toFShape [A] A hF] at hm; cases hm

theorem hasDtor_of_forgettable {A : VTy} (h : Forgettable A) : HasDtor A := by
  induction h with
  | unit => exact .unit
  | zero => exact .zero
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | imm => exact .imm
  | «mut» => exact .mut
  | unk => exact .unk
  | bang => exact .bang
  | int => exact .int

/-! ### The destructors are `CDerives` derivations -/

/-- `forget : T ⊸ 1` at a persistent `T`, from `λ` and `Ctx.DeadP.drop`. -/
theorem forget_persistent {Δ : LifeCtx} {Γ : Ctx VTy} {T : VTy} (hT : T.Persistent)
    (hΓ : Ctx.Dead Γ) : CDerives Δ Γ forget (.val (.lolli T .unit)) :=
  .thunkV rfl (.lam (.ret (.unitI (.drop hT hΓ.toP))))

/-- `λx. close x : U(C & F 1) ⊸ F 1` body, from `force`/`proj₂`. -/
theorem close_body {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.thunk (.amp C (.ret .unit)), true⟩ :: Γ) (.app (.var 0) (.val (.inj₂ .unit)))
      (.comp (.ret .unit)) :=
  .proj₂ (C := C) (.force (C := .amp C (.ret .unit)) (.here hΓ.toP))

/-- The destructor of `A ⊗ B`, from the destructors of `A` and `B`. -/
theorem dtor_tensor_wf {Δ : LifeCtx} {A B : VTy}
    (ih₁ : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (dtorE A) (.val (.lolli A .unit)))
    (ih₂ : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (dtorE B) (.val (.lolli B .unit)))
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (dtorE (.tensor A B)) (.val (.lolli (.tensor A B) .unit)) :=
  .lamV (.letpairV (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
    (.seqV (.right (.left (.dead (deadSplit hΓ))))
      (.lolliE (.dead (.left (.dead (deadSplit hΓ)))) (.var (.there (.here (.cons hΓ.toP))))
        (ih₁ (.cons (.cons (.cons hΓ)))))
      (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ.toP))))
        (ih₂ (.cons (.cons (.cons hΓ)))))))

/-- The destructor of `A ⊕ B`, from the destructors of `A` and `B`. -/
theorem dtor_sum_wf {Δ : LifeCtx} {A B : VTy}
    (ih₁ : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (dtorE A) (.val (.lolli A .unit)))
    (ih₂ : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (dtorE B) (.val (.lolli B .unit)))
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (dtorE (.sum A B)) (.val (.lolli (.sum A B) .unit)) :=
  .lamV (.caseV (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
    (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP)))
      (ih₁ (.cons (.cons hΓ))))
    (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP)))
      (ih₂ (.cons (.cons hΓ)))))

/-- `λr. d r`, promoted, at `!(A ⊸ 1)`, from the destructor `d` of `A`. -/
theorem d_alg_of_dtor {Δ : LifeCtx} {A : VTy} {d : Expr}
    (ih : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ d (.val (.lolli A .unit)))
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (.lam (.app d (.var 0)))) (.val (.bang (VTy.lolli A .unit))) :=
  d_algO hΓ (.ret (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (ih (.cons hΓ))))

/-- A tuple of derivations at a dead context. -/
theorem d_tup {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {α : Type} (f : α → Expr) (g : α → VTy) :
    ∀ (ks : List α), (∀ k ∈ ks, CDerives Δ Γ (f k) (.val (g k))) →
      CDerives Δ Γ (FoldP.tupE (ks.map f)) (.val (FoldP.tupTy (ks.map g)))
  | [], _ => .unitI hΓ.toP
  | [k], h => h k (by simp)
  | k :: k' :: r, h => .tensorI (deadSplit hΓ) (h k (by simp))
      (d_tup hΓ f g (k' :: r) (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem algsOf_nil (ks : List FoldP.Bnd) : FoldP.algsOf ks [] = dtorAlgs := rfl

/-- **Every destructor is a closed `CDerives` derivation**, at every lifetime context and every
dead context.  `[spec §12]` -/
theorem dtor_wf {Δ : LifeCtx} {T : VTy} (hT : HasDtor T) :
    ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (dtorE T) (.val (.lolli T .unit)) := by
  induction hT generalizing Δ with
  | unit => intro Γ hΓ; exact forget_persistent rfl hΓ
  | zero => intro Γ hΓ; exact forget_persistent rfl hΓ
  | int => intro Γ hΓ; exact forget_persistent rfl hΓ
  | unk => intro Γ hΓ; exact forget_persistent rfl hΓ
  | bang => intro Γ hΓ; exact forget_persistent rfl hΓ
  | imm => intro Γ hΓ; exact .forgetImm hΓ.toP
  | «mut» => intro Γ hΓ; exact .forgetMut hΓ.toP
  | tensor _ _ ih₁ ih₂ => intro Γ hΓ; exact dtor_tensor_wf ih₁ ih₂ hΓ
  | sum _ _ ih₁ ih₂ => intro Γ hΓ; exact dtor_sum_wf ih₁ ih₂ hΓ
  | box _ ih =>
      intro Γ hΓ
      exact .lamV (.lolliE (.left (deadSplit hΓ)) (.boxE (.var (.here hΓ.toP)))
        (ih (.cons hΓ)))
  | ref _ ih =>
      intro Γ hΓ
      exact .lamV (.eletV (.left (deadSplit hΓ))
        (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (.free (Ctx.Dead.cons hΓ).toP))
        (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (Ctx.Dead.cons hΓ).toP))
          (ih (.cons (.cons hΓ)))))
  | @mu A hP _ _ _ ihr ihm iha =>
      intro Γ hΓ
      cases hF : fshapeB A with
      | true =>
          obtain ⟨hW, hG⟩ := fshapeB_sound hF
          rw [dtorE_mu_F hF]
          have halg : CDerives Δ (⟨.mu A, false⟩ :: Γ) (.val (.lam (.app (algE A) (.var 0))))
              (.val (algOTy (toFShape A) .unit)) := by
            simp only [algE]
            rw [algE_eqP [A] A]
            have h := d_alg_of_dtor (Δ := Δ) ihr (Γ := ⟨.mu A, false⟩ :: Γ) (.cons hΓ)
            rw [resO_toFShape [A] A hW] at h ⊢
            exact h
          have hfold : CDerives Δ (⟨.mu A, false⟩ :: Γ)
              (.app (.val (foldOwnV (toFShape A))) (.val (.lam (.app (algE A) (.var 0)))))
              (.val (.lolli (.mu A) .unit)) := by
            have h := CDerives.bangE (CDerives.lolliE (deadSplit (.cons hΓ)) halg
              (.foldOwn (toFShape A) .unit (Ctx.Dead.cons hΓ).toP hW hG))
            rwa [toFShape_ty] at h
          exact .lamV (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) hfold)
      | false =>
          rw [dtorE_mu_P hF]
          have hΓ' : Ctx.Dead (⟨.mu A, false⟩ :: Γ) := .cons hΓ
          have hkey : ∀ k ∈ FoldP.keys A, CDerives Δ (⟨.mu A, false⟩ :: Γ) (keyAlg k)
              (.val (FoldP.algTy (FoldP.algsOf (FoldP.keys A) []) k)) := by
            intro k hk
            rw [algsOf_nil]
            simp only [FoldP.keys, List.mem_cons] at hk
            rcases hk with rfl | hk
            · simp only [keyAlg]
              rw [algE_eqP [A] A]
              exact d_alg_of_dtor (Δ := Δ) ihr hΓ'
            · have hKP := FoldP.keysIn_P A [A] hP.1 k hk
              match k, hk, hKP with
              | .mu (B :: Bs), hk, _ =>
                  simp only [keyAlg]
                  rw [algE_eqP (B :: Bs) B]
                  exact d_alg_of_dtor (Δ := Δ) (ihm B Bs hk) hΓ'
              | .arr Bs S, hk, _ =>
                  have hd : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ →
                      CDerives Δ Γ (arrAlgE (algE S))
                        (.val (.lolli (.sum .unit (.tensor .unit (FoldP.resO dtorAlgs Bs S))) .unit)) := by
                    intro Γ hΓ
                    simp only [algE]
                    rw [algE_eqP Bs S, arrAlgE_eq]
                    exact dtor_sum_wf (fun h => forget_persistent rfl h)
                      (dtor_tensor_wf (fun h => forget_persistent rfl h) (iha Bs S hk)) hΓ
                  exact d_alg_of_dtor (Δ := Δ) hd hΓ'
          have htup := d_tup hΓ' keyAlg (FoldP.algTy (FoldP.algsOf (FoldP.keys A) [])) (FoldP.keys A) hkey
          have hfold : CDerives Δ (⟨.mu A, false⟩ :: Γ)
              (.app (.val (FoldP.foldOwnGV A)) (FoldP.tupE ((FoldP.keys A).map keyAlg)))
              (.val (.lolli (.mu A) .unit)) :=
            CDerives.bangE (CDerives.lolliE (deadSplit (.cons hΓ)) htup
              (.foldOwnG A [] (Ctx.Dead.cons hΓ).toP hP))
          exact .lamV (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) hfold)
  | close => intro Γ hΓ; exact .thunkV rfl (.lam (close_body hΓ))
  | @nu C R hC hRc _ ih =>
      intro Γ hΓ
      have hM := CDerives.proj₂ (Δ := Δ)
        (.nuOut hC (.force (C := .nu (.amp C (.ret R))) (.here hΓ.toP)))
      simp only [CTy.instT, VTy.inst, VTy.subst_closed0 hRc] at hM
      exact .thunkV rfl (.lam (.bind (.left (deadSplit hΓ)) hM
        (.ret (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (Ctx.Dead.cons hΓ).toP))
          (ih (.cons (.cons hΓ)))))))
  | array _ ih =>
      intro Γ hΓ
      exact .lamV (.lolliE (.left (deadSplit hΓ))
        (.tensorI (.right (deadSplit hΓ))
          (.bangThunkV (dead_noLive (Ctx.Dead.cons hΓ)) rfl
            (.lam (.ret (.lolliE (.left (.dead (deadSplit hΓ)))
              (.var (.here (Ctx.Dead.cons hΓ).toP)) (ih (.cons (.cons hΓ)))))))
          (.var (.here hΓ.toP)))
        (.bangE (.arrFree _ (Ctx.Dead.cons hΓ).toP)))
  | arrayImm => intro Γ hΓ; exact .bangE (.arrForget _ _ hΓ.toP)
  | arrayMut =>
      intro Γ hΓ
      exact .lamV (.eletV (.left (deadSplit hΓ))
        (.lolliE (.left (deadSplit hΓ))
          (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP))
            (.lit (.i32 0xFFFFFFFF) (Ctx.Dead.cons hΓ).toP))
          (.bangE (.sliceGetM _ _ (Ctx.Dead.cons hΓ).toP)))
        (.caseV (.left (deadSplit (Ctx.Dead.cons hΓ))) (.var (.here (Ctx.Dead.cons hΓ).toP))
          (.lolliE (.left (.dead (deadSplit (Ctx.Dead.cons hΓ))))
            (.var (.here (Ctx.Dead.cons (Ctx.Dead.cons hΓ)).toP))
            (.forgetMut (Ctx.Dead.cons (Ctx.Dead.cons (Ctx.Dead.cons hΓ))).toP))
          (.var (.here (Ctx.Dead.cons (Ctx.Dead.cons hΓ)).toP))))

/-! ### A borrow's destructor frees nothing -/

/-- At `Imm @a A` and `Mut @a A` the destructor is `forget = λx. ()`: dropping a borrow ends the
loan and deallocates nothing. -/
theorem dtorE_imm (a : Lifetime.Life) (A : VTy) : dtorE (.imm a A) = forget := rfl

theorem dtorE_mut (a : Lifetime.Life) (A : VTy) : dtorE (.mut a A) = forget := rfl

/-! ### Dropping a slot -/

/-- `dtorE T xᵢ; e`: the destructor of the variable `i` at `T`, before `e`. -/
def dropE (T : VTy) (i : Nat) (e : Expr) : Expr := .seq (.app (dtorE T) (.var i)) e

/-- **A drop is a `CDerives` derivation**: `unitE` over the destructor applied to the slot.
`[spec §12]` -/
theorem drop_derives {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {i : Nat} {T : VTy} {e : Expr} {C : CTy}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i T) (hT : HasDtor T)
    (h : CDerives Δ Γ₂ e (.comp C)) : CDerives Δ Γ (dropE T i e) (.comp C) :=
  .unitE hs (.lolliE (split_kill' Γ₁).toP (.var hx) (dtor_wf hT (kill_dead Γ₁))) h

end BoCa.Fig16.LogRel.Core

end
