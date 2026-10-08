import Targets.Instance.Core

/-!
# The Instance — what today's kernel does not type

Inversions of `CDerivesNU`, today's unr-free rules, each read off one induction on the derivation.
A rule whose premise has the conclusion's term (`ret`, `ofRet`, `[sub]`, `ν`'s two rules, and the
`!`, `[]`, `⊑`, `μ` value rules) is followed by an invariant on the judgement; every other rule is
told apart by its conclusion's term.

* **A-level `handle`** (`not_der_handleK`).  Our instance encodes A's `handle l H M` as the run-time
  frame `hnd (n, (h_ret, hs)) M`, its clauses values (`Inst.handleK`).  Core's `[handle]` types only
  `hndTerm n ir ic e`, whose clauses are two variables.  No derivation of `CDerivesNU` has the
  frame form, at any context and judgement.
* **One binder, two instances** (`not_der_letTwo`).  `λ_. ⟨x, x⟩`'s two components, the let-bound
  `x` read at `!U c₁` and at `!U c₂`, with `c₁ ≠ c₂` two arrow types: no derivation of
  `(λx. ⟨x, x⟩) V` has them.  A slot has one type, and every judgement a variable is read at is
  a view of that type (`der_var_inv`).
* **A variable used as a function is a `U` slot** (`der_var_arr_thunk`): a variable read at an arrow
  type is forced from a slot of type `U C`, never from `!U C`.  So A's `call x g` (`appE`) is typed
  from no slot `!U(A ⊸ F_S B)` with `S` a row with an operation (`not_der_callBang`).
* **A pure value at a resuming `unr` row** (`not_der_unit_nonNU`): `()` is typed at `F_S 1` only
  at unr-free rows `S`, since `[sub]` asks `Row.NU` of its target.
-/

noncomputable section

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU)

theorem forceE_cases (C : CTy) (e : Expr) :
    forceE C e = e ∨ forceE C e = .app e (.val .unit) := by
  cases C <;> simp [forceE]

/-- The term constants of `CDerivesNU`'s conclusions, unfolded to their head constructors, so that
a rule whose conclusion's term has another head is told apart. -/
macro "cdnu_terms" : tactic => `(tactic| (try simp_all [withPair, absurdE, copy, forget, swap,
    withbor, withload, withswap, sizeV, replaceV, arrLenV, copyV, forgetV, emptyFamV, swapV,
    Val.arr, withborUE, foldImmV, foldOwnV, foldReuseV, unfoldV, BoCa.BoLo.performE,
    BoCa.BoLo.raiseE, opArgE, thenE, hndTerm, Expr.val, Val.lam, Val.prim, Val.unit, lam2, elet]))

/-- The same, read at one hypothesis alone. -/
macro "cdnu_at " h:ident : tactic => `(tactic| (simp [withPair, absurdE, copy, forget, swap,
    withbor, withload, withswap, sizeV, replaceV, arrLenV, copyV, forgetV, emptyFamV, swapV,
    Val.arr, withborUE, foldImmV, foldOwnV, foldReuseV, unfoldV, BoCa.BoLo.performE,
    BoCa.BoLo.raiseE, opArgE, thenE, hndTerm, Expr.val, Val.lam, Val.prim, Val.unit, lam2, elet]
    at $h:ident))

/-! ### A-level `handle` -/

/-- `hnd` alone has no derivation. -/
theorem not_der_prim_hnd {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : e ≠ .prim .hnd := by
  induction h <;> intro he <;> cdnu_terms
  case force _ _ i C _ =>
    rcases forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he

theorem not_der_prim_hnd' {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} :
    ¬ CDerivesNU Δ Γ (.prim .hnd) j := fun h => not_der_prim_hnd h rfl

/-- `hnd X` alone has no derivation. -/
theorem not_der_app_hnd {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ X, e ≠ .app (.prim .hnd) X := by
  induction h <;> intro X he <;> cdnu_terms <;> (try simp_all [not_der_prim_hnd'])
  case force _ _ i C _ =>
    rcases forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he

theorem not_der_app_hnd' {Δ : LifeCtx} {Γ : Ctx VTy} {X : Expr} {j : Jdg} :
    ¬ CDerivesNU Δ Γ (.app (.prim .hnd) X) j := fun h => not_der_app_hnd h X rfl

/-- **A handler term's clauses are two variables**: `[handle]` is the only rule whose conclusion's
term is `hnd X M`. -/
theorem der_hnd_shape {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ X M, e = .app (.app (.prim .hnd) X) M →
      ∃ (n : UInt32) (qs : List Qual) (ir ic : Nat),
        X = .pair (.prim (.lit (.i32 n))) (.pair (qualsVal qs).1 (.pair (.var ir) (.var ic))) := by
  induction h <;> intro X M he <;> cdnu_terms <;> (try simp_all [not_der_app_hnd'])
  case force _ _ i C _ =>
    rcases forceE_cases C (.var i) with h | h <;> rw [h] at he <;> simp at he
  case effHandle =>
    obtain ⟨hX, -⟩ := he
    exact ⟨_, _, _, _, hX.symm⟩

/-- A list of clauses, as an expression, is a pair or `()`, never a variable. -/
theorem clausesE_ne_var (cs : List Expr) (i : Nat) : clausesE cs ≠ .var i := by
  cases cs <;> simp [clausesE]

/-- **Today's kernel types no A-level handler.**  Our instance's `handle l (hnd r cs) M` is the
run-time frame `hnd (n, (qs, (r, cs))) M` (`handleK`), its clauses a tuple of values; no derivation of
`CDerivesNU` has a conclusion of that form, at any context and judgement. -/
theorem not_der_handleK {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} (n : UInt32) (qs r : Expr)
    (cs : List Expr) (M : Expr) : ¬ CDerivesNU Δ Γ ((handleK n qs r cs).plug M) j := by
  intro h
  obtain ⟨n', qs', ir, ic, hX⟩ := der_hnd_shape h (hndValE n qs r cs) M rfl
  simp only [hndValE, Expr.pair.injEq] at hX
  exact clausesE_ne_var cs ic hX.2.2.2

/-! ### The views of a slot's type -/

/-- `Y`'s thunk: following `!`, `[a]` and `μ`'s unrolling from `Y` reaches `U c`. -/
inductive ThunkOf : VTy → CTy → Prop
  | thunk (c : CTy) : ThunkOf (.thunk c) c
  | bang {Y : VTy} {c : CTy} : ThunkOf Y c → ThunkOf (.bang Y) c
  | box {a : Lifetime.Life} {Y : VTy} {c : CTy} : ThunkOf Y c → ThunkOf (.box a Y) c
  | mu {B : VTy} {c : CTy} : ThunkOf (VTy.inst (.mu B) B) c → ThunkOf (.mu B) c

theorem ThunkOf.unique {Y : VTy} {c c' : CTy} (h : ThunkOf Y c) (h' : ThunkOf Y c') : c = c' := by
  induction h generalizing c' with
  | thunk c => cases h'; rfl
  | bang _ ih => cases h' with | bang h' => exact ih h'
  | box _ ih => cases h' with | box h' => exact ih h'
  | mu _ ih => cases h' with | mu h' => exact ih h'

/-- Two value types with the same thunk, if either has one. -/
def SameThunk (Y Z : VTy) : Prop := ∀ c, ThunkOf Y c ↔ ThunkOf Z c

theorem SameThunk.refl (Y : VTy) : SameThunk Y Y := fun _ => Iff.rfl

theorem SameThunk.symm {Y Z : VTy} (h : SameThunk Y Z) : SameThunk Z Y := fun c => (h c).symm

theorem SameThunk.trans {Y Z W : VTy} (h : SameThunk Y Z) (h' : SameThunk Z W) : SameThunk Y W :=
  fun c => (h c).trans (h' c)

theorem sameThunk_bang (Y : VTy) : SameThunk (.bang Y) Y :=
  fun _ => ⟨fun h => by cases h; assumption, .bang⟩

theorem sameThunk_box (a : Lifetime.Life) (Y : VTy) : SameThunk (.box a Y) Y :=
  fun _ => ⟨fun h => by cases h; assumption, .box⟩

theorem sameThunk_mu (B : VTy) : SameThunk (.mu B) (VTy.inst (.mu B) B) :=
  fun _ => ⟨fun h => by cases h; assumption, .mu⟩

theorem sameThunk_imm (a b : Lifetime.Life) (Y Y' : VTy) : SameThunk (.imm a Y) (.imm b Y') :=
  fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩

theorem sameThunk_mut (a b : Lifetime.Life) (Y Y' : VTy) : SameThunk (.mut a Y) (.mut b Y') :=
  fun _ => ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-! ### Unrolling `ν` -/

/-- `D` unrolls, by `νX. C ↦ C[U(νX. C)/X]`, to a type `P` holds of. -/
inductive NuUp (P : CTy → Prop) : CTy → Prop
  | base {D : CTy} : P D → NuUp P D
  | nu {C : CTy} : NuUp P C.unroll → NuUp P (.nu C)

/-- At a type that is not a `ν`, only the base holds. -/
theorem NuUp.base_of {P : CTy → Prop} {D : CTy} (hD : ∀ C, D ≠ .nu C) (h : NuUp P D) : P D := by
  cases h with
  | base h => exact h
  | nu _ => exact absurd rfl (hD _)

/-- At a `ν`, when `P` holds of no `ν`, the unrolling. -/
theorem NuUp.of_nu {P : CTy → Prop} {C : CTy} (hP : ∀ C', ¬ P (.nu C')) (h : NuUp P (.nu C)) :
    NuUp P C.unroll := by
  cases h with
  | base h => exact absurd h (hP C)
  | nu h => exact h

/-- Two computation types equal up to unrolling `ν`. -/
abbrev NuEq : CTy → CTy → Prop :=
  Relation.EqvGen (fun D D' : CTy => ∃ C, D = .nu C ∧ D' = C.unroll)

theorem NuEq.unroll (C : CTy) : NuEq (.nu C) C.unroll := .rel _ _ ⟨C, rfl, rfl⟩

/-- The type a `ν` unrolls to, in finitely many steps, that is not a `ν`. -/
inductive NuRoot : CTy → CTy → Prop
  | base {D : CTy} : (∀ C, D ≠ .nu C) → NuRoot D D
  | nu {C r : CTy} : NuRoot C.unroll r → NuRoot (.nu C) r

theorem NuRoot.unique {D r r' : CTy} (h : NuRoot D r) (h' : NuRoot D r') : r = r' := by
  induction h generalizing r' with
  | base hD => cases h' with
    | base _ => rfl
    | nu _ => exact absurd rfl (hD _)
  | nu _ ih => cases h' with
    | base hD => exact absurd rfl (hD _)
    | nu h' => exact ih h'

theorem nuRoot_nu_iff {C r : CTy} : NuRoot (.nu C) r ↔ NuRoot C.unroll r :=
  ⟨fun h => by
    cases h with
    | base hD => exact absurd rfl (hD _)
    | nu h => exact h, .nu⟩

theorem NuEq.root {D D' : CTy} (h : NuEq D D') : ∀ r, NuRoot D r ↔ NuRoot D' r := by
  induction h with
  | rel _ _ hr =>
      obtain ⟨C, rfl, rfl⟩ := hr
      exact fun _ => nuRoot_nu_iff
  | refl => exact fun _ => Iff.rfl
  | symm _ _ _ ih => exact fun r => (ih r).symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact fun r => (ih₁ r).trans (ih₂ r)

/-- **Two types equal up to `ν`, neither a `ν`, are equal.** -/
theorem NuEq.eq {D D' : CTy} (h : NuEq D D') (hD : ∀ C, D ≠ .nu C) (hD' : ∀ C, D' ≠ .nu C) :
    D = D' :=
  NuRoot.unique ((h.root D).mp (.base hD)) (.base hD')

/-! ### Rows over a type -/

theorem effOf_ne_nu (S : Row) (Y : VTy) (C : CTy) : CTy.effOf S Y ≠ .nu C := by
  cases S <;> simp [CTy.effOf]

theorem effOf_ne_amp (S : Row) (Y : VTy) (C D : CTy) : CTy.effOf S Y ≠ .amp C D := by
  cases S <;> simp [CTy.effOf]

theorem effOf_isRet (S : Row) (Y : VTy) : (CTy.effOf S Y).isRet = true := by
  cases S <;> rfl

/-! ### The judgements a variable is read at -/

theorem soloP_slot {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.SoloP Γ i A) :
    Γ[i]? = some ⟨A, true⟩ := by
  induction h with
  | here _ => rfl
  | there _ ih => simpa using ih
  | skip _ _ ih => simpa using ih

/-- The value types a variable whose slot has type `A` is read at: those with `A`'s thunk, and,
when `A` is `U C`, those with the thunk of a payload `C` unrolls to. -/
def ValInv (A Y : VTy) : Prop :=
  SameThunk Y A ∨ ∃ C S X, A = .thunk C ∧ NuEq C (CTy.effOf S X) ∧ SameThunk Y X

/-- The computation types it is read at: a row over a value type it is read at, up to `ν`; and,
when `A` is `U C`, `C`, up to `ν`. -/
def CompInv (A : VTy) (D : CTy) : Prop :=
  NuUp (fun D' => ∃ S Y, D' = CTy.effOf S Y ∧ ValInv A Y) D ∨ ∃ C, A = .thunk C ∧ NuEq C D

/-- The judgements a variable whose slot has type `A` is read at. -/
def VarInv (A : VTy) : Jdg → Prop
  | .val Y => ValInv A Y
  | .comp D => CompInv A D

theorem ValInv.of_same {A Y Y' : VTy} (h : ValInv A Y) (hs : SameThunk Y Y') : ValInv A Y' := by
  rcases h with h | ⟨C, S, X, hA, hC, hX⟩
  · exact .inl (hs.symm.trans h)
  · exact .inr ⟨C, S, X, hA, hC, hs.symm.trans hX⟩

theorem CompInv.ret {A Y : VTy} (h : ValInv A Y) : CompInv A (.ret Y) :=
  .inl (.base ⟨[], Y, rfl, h⟩)

theorem CompInv.ofRet {A Y : VTy} (h : CompInv A (.ret Y)) : ValInv A Y := by
  rcases h with h | ⟨C, hA, hC⟩
  · obtain ⟨S, Y', he, hY'⟩ := h.base_of (fun _ h => by cases h)
    obtain ⟨-, rfl⟩ := effOf_inj (S := []) he
    exact hY'
  · exact .inr ⟨C, [], Y, hA, hC, .refl Y⟩

theorem CompInv.effSub {A Y : VTy} {S S' : Row} (h : CompInv A (CTy.effOf S Y)) :
    CompInv A (CTy.effOf S' Y) := by
  rcases h with h | ⟨C, hA, hC⟩
  · obtain ⟨S₀, Y₀, he, hY₀⟩ := h.base_of (effOf_ne_nu S Y)
    obtain ⟨-, rfl⟩ := effOf_inj he
    exact .inl (.base ⟨S', Y, rfl, hY₀⟩)
  · exact .inl (.base ⟨S', Y, rfl, .inr ⟨C, S, Y, hA, hC, .refl Y⟩⟩)

theorem CompInv.nuIn {A : VTy} {C : CTy} (h : CompInv A C.unroll) : CompInv A (.nu C) := by
  rcases h with h | ⟨C₀, hA, hC⟩
  · exact .inl (.nu h)
  · exact .inr ⟨C₀, hA, .trans _ _ _ hC (.symm _ _ (NuEq.unroll C))⟩

theorem CompInv.nuOut {A : VTy} {C : CTy} (h : CompInv A (.nu C)) : CompInv A C.unroll := by
  rcases h with h | ⟨C₀, hA, hC⟩
  · exact .inl (h.of_nu (fun _ ⟨S, Y, he, _⟩ => effOf_ne_nu S Y _ he.symm))
  · exact .inr ⟨C₀, hA, .trans _ _ _ hC (NuEq.unroll C)⟩

/-- **Every judgement a variable is read at is a view of its slot's type.** -/
theorem der_var_inv {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesNU Δ Γ e j) :
    ∀ i, e = .var i → ∃ A, Γ[i]? = some ⟨A, true⟩ ∧ VarInv A j := by
  induction h
  case var =>
    rename_i hs
    intro i he
    cases he
    exact ⟨_, soloP_slot hs, .inl (.refl _)⟩
  case force =>
    rename_i i' C hs
    intro i he
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he
    · cases he
      exact ⟨_, soloP_slot hs, .inr ⟨C, rfl, .refl C⟩⟩
    · cases he
  case ret =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, CompInv.ret hI⟩
  case ofRet =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, CompInv.ofRet hI⟩
  case effSub =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, CompInv.effSub hI⟩
  case nuIn =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, CompInv.nuIn hI⟩
  case nuOut =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, CompInv.nuOut hI⟩
  case bangE =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, ValInv.of_same hI (sameThunk_bang _)⟩
  case boxI =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, ValInv.of_same hI (sameThunk_box _ _).symm⟩
  case boxE =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, ValInv.of_same hI (sameThunk_box _ _)⟩
  case immSub =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, ValInv.of_same hI (sameThunk_imm _ _ _ _)⟩
  case mutSub =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, ValInv.of_same hI (sameThunk_mut _ _ _ _)⟩
  case roll =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, ValInv.of_same hI (sameThunk_mu _).symm⟩
  case unroll =>
    rename_i ih; intro i he
    obtain ⟨A, hA, hI⟩ := ih i he
    exact ⟨A, hA, ValInv.of_same hI (sameThunk_mu _)⟩
  all_goals intro i he; cdnu_terms

/-- **A variable read at an arrow type is forced from a `U` slot.** -/
theorem der_var_arr_thunk {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A : VTy} {C : CTy}
    (h : CDerivesNU Δ Γ (.var i) (.comp (.arr A C))) : ∃ C₀, Γ[i]? = some ⟨.thunk C₀, true⟩ := by
  obtain ⟨T, hT, hI⟩ := der_var_inv h i rfl
  rcases hI with hI | ⟨C₀, rfl, -⟩
  · obtain ⟨S, Y, he, -⟩ := hI.base_of (fun _ h => by cases h)
    cases S <;> simp [CTy.effOf] at he
  · exact ⟨C₀, hT⟩

/-- Two `!U` views of one slot have one thunk, when neither is a row's or a `ν`'s. -/
theorem compInv_two_bangs {A : VTy} {c₁ c₂ : CTy} (hr₁ : c₁.isRet = false) (hn₁ : ∀ C, c₁ ≠ .nu C)
    (hr₂ : c₂.isRet = false) (hn₂ : ∀ C, c₂ ≠ .nu C)
    (h₁ : CompInv A (.ret (.bang (.thunk c₁)))) (h₂ : CompInv A (.ret (.bang (.thunk c₂)))) :
    c₁ = c₂ := by
  have t₁ : ThunkOf (.bang (.thunk c₁)) c₁ := .bang (.thunk c₁)
  have t₂ : ThunkOf (.bang (.thunk c₂)) c₂ := .bang (.thunk c₂)
  -- a view of `A` at `U c` makes `A`'s thunk `c`; a payload view is a row's payload
  have hpay : ∀ {c C S X}, c.isRet = false → (∀ C', c ≠ .nu C') → ThunkOf (.thunk C) c →
      NuEq C (CTy.effOf S X) → False := by
    intro c C S X hr hn ht hC
    cases ht
    have := hC.eq hn (effOf_ne_nu S X)
    rw [this, effOf_isRet] at hr
    cases hr
  rcases CompInv.ofRet h₁ with h₁ | ⟨C, S, X, hA, hC, hX⟩ <;>
    rcases CompInv.ofRet h₂ with h₂ | ⟨C', S', X', hA', hC', hX'⟩
  · exact ThunkOf.unique ((h₁ c₁).mp t₁) ((h₂ c₂).mp t₂)
  · subst hA'
    exact (hpay hr₁ hn₁ ((h₁ c₁).mp t₁) hC').elim
  · subst hA
    exact (hpay hr₂ hn₂ ((h₂ c₂).mp t₂) hC).elim
  · subst hA
    cases hA'
    have hXX : CTy.effOf S X = CTy.effOf S' X' :=
      NuEq.eq (.trans _ _ _ (.symm _ _ hC) hC') (effOf_ne_nu S X) (effOf_ne_nu S' X')
    obtain ⟨-, rfl⟩ := effOf_inj hXX
    exact ThunkOf.unique ((hX c₁).mp t₁) ((hX' c₂).mp t₂)

/-! ### One binder, two instances -/

theorem withPair_inj {M N M' N' : Expr} (h : withPair M N = withPair M' N') : M = M' ∧ N = N' := by
  simp only [withPair, Expr.val, Val.lam, Expr.lam.injEq, Expr.case.injEq, Expr.seq.injEq] at h
  exact ⟨h.2.1.2, h.2.2.2⟩

/-- **`⟨M, N⟩` at `C & D`**: up to `ν`, `[&I]` with `M` at `C` and `N` at `D`; at every other type
`⟨M, N⟩` is read at, no `&`. -/
theorem der_withPair_amp {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ M N D, e = withPair M N → j = .comp D →
      NuUp (fun D' => (∀ C, D' ≠ .nu C) ∧
        ((∃ C₁ C₂, D' = .amp C₁ C₂ ∧ CDerivesNU Δ (withCtx Γ) M (.comp C₁) ∧
          CDerivesNU Δ (withCtx Γ) N (.comp C₂)) ∨ ∀ C₁ C₂, D' ≠ .amp C₁ C₂)) D := by
  induction h
  case withI =>
    rename_i hM hN _ _
    intro M N D he hj
    obtain ⟨rfl, rfl⟩ := withPair_inj he
    cases hj
    exact .base ⟨fun _ h => (by cases h), .inl ⟨_, _, rfl, hM, hN⟩⟩
  case nuIn =>
    rename_i ih; intro M N D he hj
    cases hj
    exact .nu (ih M N _ he rfl)
  case nuOut =>
    rename_i ih; intro M N D he hj
    cases hj
    exact (ih M N _ he rfl).of_nu (fun _ ⟨h, _⟩ => h _ rfl)
  case ret =>
    intro M N D he hj
    cases hj
    exact .base ⟨fun _ h => (by cases h), .inr fun _ _ h => by cases h⟩
  case effSub =>
    intro M N D he hj
    cases hj
    exact .base ⟨effOf_ne_nu _ _, .inr (effOf_ne_amp _ _)⟩
  case lam =>
    intro M N D he hj
    cases hj
    exact .base ⟨fun _ h => (by cases h), .inr fun _ _ h => by cases h⟩
  case allI =>
    intro M N D he hj
    cases hj
    exact .base ⟨fun _ h => (by cases h), .inr fun _ _ h => by cases h⟩
  case force =>
    rename_i i' C _
    intro M N D he hj
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he <;> simp [withPair] at he
  all_goals intro M N D he hj; cdnu_terms

/-- **`(λx. W) (λ. b)` at `C & D`**: up to `ν`, `[bind]` or `[let]` with `W` at that type, under
a slot for `x`; at every other type `(λx. W) (λ. b)` is read at, no `&`. -/
theorem der_letLam_amp {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ W b D, e = .app (.lam W) (.lam b) → j = .comp D →
      NuUp (fun D' => (∃ A Γ₂, CDerivesNU Δ (⟨A, true⟩ :: Γ₂) W (.comp D')) ∨
        ((∀ C, D' ≠ .nu C) ∧ ∀ C₁ C₂, D' ≠ .amp C₁ C₂)) D := by
  induction h
  case bind =>
    rename_i hN _ _
    intro W b D he hj
    simp only [Expr.val, Val.lam, Expr.app.injEq, Expr.lam.injEq] at he
    obtain ⟨rfl, -⟩ := he
    cases hj
    exact .base (.inl ⟨_, _, hN⟩)
  case effLet =>
    rename_i hN _ _
    intro W b D he hj
    simp only [Expr.val, Val.lam, Expr.app.injEq, Expr.lam.injEq] at he
    obtain ⟨rfl, -⟩ := he
    cases hj
    exact .base (.inl ⟨_, _, hN⟩)
  case nuIn =>
    rename_i ih; intro W b D he hj
    cases hj
    exact .nu (ih W b _ he rfl)
  case nuOut =>
    rename_i hC _ ih; intro W b D he hj
    cases hj
    cases ih W b _ he rfl with
    | base h =>
        rcases h with ⟨A, Γ₂, hW⟩ | ⟨h, -⟩
        · exact .base (.inl ⟨A, Γ₂, .nuOut hC hW⟩)
        · exact absurd rfl (h _)
    | nu h => exact h
  case ret =>
    intro W b D he hj
    cases hj
    exact .base (.inr ⟨fun _ h => (by cases h), fun _ _ h => by cases h⟩)
  case effSub =>
    intro W b D he hj
    cases hj
    exact .base (.inr ⟨effOf_ne_nu _ _, effOf_ne_amp _ _⟩)
  case force =>
    rename_i i' C _
    intro W b D he hj
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he <;> simp at he
  all_goals intro W b D he hj; cdnu_terms

/-- **One binder, two instances: today's kernel types no let whose variable is read at two thunk
types.**  In `(λx. ⟨x, x⟩) (λ. b)`, the components read `x`, and a slot has one type, of which
each judgement `x` is read at is a view (`der_var_inv`): `!U c₁` and `!U c₂` are both views of it
only if `c₁ = c₂`, for `c₁`, `c₂` neither a row's type nor a `ν`. -/
theorem not_der_letTwo {Δ : LifeCtx} {Γ : Ctx VTy} {b : Expr} {c₁ c₂ : CTy}
    (hr₁ : c₁.isRet = false) (hn₁ : ∀ C, c₁ ≠ .nu C) (hr₂ : c₂.isRet = false)
    (hn₂ : ∀ C, c₂ ≠ .nu C) (hne : c₁ ≠ c₂) :
    ¬ CDerivesNU Δ Γ (.app (.lam (withPair (.var 2) (.var 2))) (.lam b))
      (.comp (.amp (.ret (.bang (.thunk c₁))) (.ret (.bang (.thunk c₂))))) := by
  intro h
  have h₁ := (der_letLam_amp h _ b _ rfl rfl).base_of (fun _ h => by cases h)
  rcases h₁ with ⟨A, Γ₂, hW⟩ | ⟨-, h₁⟩
  · have h₂ := (der_withPair_amp hW _ _ _ rfl rfl).base_of (fun _ h => by cases h)
    rcases h₂ with ⟨-, ⟨C₁, C₂, he, hM, hN⟩ | h₂⟩
    · cases he
      obtain ⟨T, hT, hI⟩ := der_var_inv hM 2 rfl
      obtain ⟨T', hT', hI'⟩ := der_var_inv hN 2 rfl
      rw [hT] at hT'
      cases hT'
      exact hne (compInv_two_bangs hr₁ hn₁ hr₂ hn₂ hI hI')
    · exact h₂ _ _ rfl
  · exact h₁ _ _ rfl

/-! ### `()` at a row -/

theorem row_nu_nil : Row.NU [] := fun _ _ _ h => by simp [Row.find] at h

/-- **`()` is read at a row only at an unr-free one**, up to `ν`: `[sub]` asks `Row.NU` of its
target, and `return ()` is at the empty row. -/
theorem der_unit_inv {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesNU Δ Γ e j) :
    e = .unit → ∀ D, j = .comp D →
      NuUp (fun D' => (∀ C, D' ≠ .nu C) ∧ (D' = .top ∨ ∃ S Y, D' = CTy.effOf S Y ∧ Row.NU S)) D := by
  induction h
  case topI =>
    intro _ D hj
    cases hj
    exact .base ⟨fun _ h => (by cases h), .inl rfl⟩
  case ret =>
    intro _ D hj
    cases hj
    exact .base ⟨fun _ h => (by cases h), .inr ⟨[], _, rfl, row_nu_nil⟩⟩
  case effSub =>
    rename_i hNU _ _ _
    intro _ D hj
    cases hj
    exact .base ⟨effOf_ne_nu _ _, .inr ⟨_, _, rfl, hNU⟩⟩
  case nuIn =>
    rename_i ih; intro he D hj
    cases hj
    exact .nu (ih he _ rfl)
  case nuOut =>
    rename_i ih; intro he D hj
    cases hj
    exact (ih he _ rfl).of_nu (fun _ ⟨h, _⟩ => h _ rfl)
  case force =>
    rename_i i' C _
    intro he D hj
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he <;> simp at he
  all_goals intro he D hj; cdnu_terms

/-- **Today's kernel types `()` at no row with a resuming `unr` operation.** -/
theorem not_der_unit_nonNU {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {Y : VTy} (hS : ¬ Row.NU S) :
    ¬ CDerivesNU Δ Γ .unit (.comp (CTy.effOf S Y)) := by
  intro h
  obtain ⟨-, h⟩ := (der_unit_inv h rfl _ rfl).base_of (effOf_ne_nu S Y)
  rcases h with h | ⟨S', Y', he, hS'⟩
  · cases S <;> simp [CTy.effOf] at h
  · obtain ⟨rfl, -⟩ := effOf_inj he
    exact hS hS'

/-! ### Calling a variable -/

theorem splitP_live_right {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    ∀ {k : Nat} {T : VTy}, Γ₂[k]? = some ⟨T, true⟩ → Γ[k]? = some ⟨T, true⟩ := by
  induction h with
  | nil => intro k T h; simp at h
  | left _ ih | right _ ih | dead _ ih | dup _ _ ih =>
      intro k T h
      cases k with
      | zero => simp_all
      | succ k => exact ih (by simpa using h)

theorem splitP_live_left {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    ∀ {k : Nat} {T : VTy}, Γ₁[k]? = some ⟨T, true⟩ → Γ[k]? = some ⟨T, true⟩ := by
  induction h with
  | nil => intro k T h; simp at h
  | left _ ih | right _ ih | dead _ ih | dup _ _ ih =>
      intro k T h
      cases k with
      | zero => simp_all
      | succ k => exact ih (by simpa using h)

/-- The body shapes `der_lam_body` reads: not a `&`-pair's, nor a constant's. -/
def PlainBody (N : Expr) : Prop :=
  (∀ M₁ M₂, N ≠ .case (.var 0) (.seq (.var 0) M₁) (.seq (.var 0) M₂)) ∧ (∀ c, N ≠ .lam c) ∧
    (∀ a c, N ≠ .pair a c) ∧ (∀ a c, N ≠ .letpair a c) ∧ N ≠ .unit

/-- **A λ's body is typed under one more slot.** -/
theorem der_lam_body {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerivesNU Δ Γ e j) :
    ∀ N, e = .lam N → PlainBody N → ∃ Δ' s C, CDerivesNU Δ' (s :: Γ) N (.comp C) := by
  induction h
  case lam =>
    rename_i hM _
    intro N he _
    simp only [Expr.val, Val.lam, Expr.lam.injEq] at he
    subst he
    exact ⟨_, _, _, hM⟩
  case thunkF =>
    rename_i hM _
    intro N he _
    simp only [Expr.val, Val.lam, Expr.lam.injEq] at he
    subst he
    exact ⟨_, _, _, hM⟩
  case bangThunkF =>
    rename_i hM _
    intro N he _
    simp only [Expr.val, Val.lam, Expr.lam.injEq] at he
    subst he
    exact ⟨_, _, _, hM⟩
  case allI =>
    rename_i hM _
    intro N he _
    simp only [Expr.val, Val.lam, Expr.lam.injEq] at he
    subst he
    exact ⟨_, _, _, hM⟩
  case withI =>
    intro N he hN
    simp only [withPair, Expr.val, Val.lam, Expr.lam.injEq] at he
    exact absurd he.symm (hN.1 _ _)
  case force =>
    rename_i i' C _
    intro N he _
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he <;> simp at he
  case ret => rename_i ih; exact ih
  case ofRet => rename_i ih; exact ih
  case effSub => rename_i ih; exact ih
  case nuIn => rename_i ih; exact ih
  case nuOut => rename_i ih; exact ih
  case bangE => rename_i ih; exact ih
  case boxI => rename_i ih; exact ih
  case boxE => rename_i ih; exact ih
  case immSub => rename_i ih; exact ih
  case mutSub => rename_i ih; exact ih
  case roll => rename_i ih; exact ih
  case unroll => rename_i ih; exact ih
  case thunkV => rename_i ih; exact ih
  case bangThunkV => rename_i ih; exact ih
  all_goals
    intro N he hN
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hN
    cdnu_terms
  all_goals first
    | exact absurd he.symm (h₁ _ _) | exact absurd he.symm (h₂ _)
    | exact absurd he.symm (h₃ _ _) | exact absurd he.symm (h₄ _ _) | exact absurd he.symm h₅

/-- **The body of `(λx. N) (λ. b)` is typed under one more slot**, over a part of the context. -/
theorem der_appLam_body {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ N b, e = .app (.lam N) (.lam b) → PlainBody N →
      ∃ Δ' Γ' s j', (∀ {k : Nat} {T : VTy}, Γ'[k]? = some ⟨T, true⟩ → Γ[k]? = some ⟨T, true⟩) ∧
        CDerivesNU Δ' (s :: Γ') N j' := by
  induction h
  case bind =>
    rename_i hs _ hN _ _
    intro N b he _
    simp only [Expr.val, Val.lam, Expr.app.injEq, Expr.lam.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact ⟨_, _, _, _, fun hT => splitP_live_right hs hT, hN⟩
  case effLet =>
    rename_i hs _ _ _ hN _ _
    intro N b he _
    simp only [Expr.val, Val.lam, Expr.app.injEq, Expr.lam.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact ⟨_, _, _, _, fun hT => splitP_live_right hs hT, hN⟩
  case lolliE =>
    rename_i hs _ hf _ _
    intro N b he hN
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, -⟩ := he
    obtain ⟨Δ', s, C, hd⟩ := der_lam_body hf N rfl hN
    exact ⟨Δ', _, s, _, fun hT => splitP_live_right hs hT, hd⟩
  case force =>
    rename_i i' C _
    intro N b he _
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he <;> simp at he
  case ret => rename_i ih; exact ih
  case ofRet => rename_i ih; exact ih
  case effSub => rename_i ih; exact ih
  case nuIn => rename_i ih; exact ih
  case nuOut => rename_i ih; exact ih
  case bangE => rename_i ih; exact ih
  case boxI => rename_i ih; exact ih
  case boxE => rename_i ih; exact ih
  case immSub => rename_i ih; exact ih
  case mutSub => rename_i ih; exact ih
  case roll => rename_i ih; exact ih
  case unroll => rename_i ih; exact ih
  all_goals intro N b he hN; cdnu_terms

/-- `x y`'s function `x`: forced at an arrow type, or read at a pure arrow `A ⊸ B`. -/
theorem der_app_var_var {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesNU Δ Γ e j) : ∀ k m, e = .app (.var k) (.var m) →
      (∃ Γ₁ A C, (∀ {T : VTy}, Γ₁[k]? = some ⟨T, true⟩ → Γ[k]? = some ⟨T, true⟩) ∧
        CDerivesNU Δ Γ₁ (.var k) (.comp (.arr A C))) ∨
      (∃ Γ₂ A B, (∀ {T : VTy}, Γ₂[k]? = some ⟨T, true⟩ → Γ[k]? = some ⟨T, true⟩) ∧
        CDerivesNU Δ Γ₂ (.var k) (.val (.lolli A B))) := by
  induction h
  case app =>
    rename_i hs hM _ _
    intro k m he
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact .inl ⟨_, _, _, fun hT => splitP_live_left hs hT, hM⟩
  case lolliE =>
    rename_i hs _ hf _ _
    intro k m he
    simp only [Expr.app.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact .inr ⟨_, _, _, fun hT => splitP_live_right hs hT, hf⟩
  case force =>
    rename_i i' C _
    intro k m he
    rcases forceE_cases C (.var i') with hf | hf <;> rw [hf] at he <;> simp at he
  case ret => rename_i ih; exact ih
  case ofRet => rename_i ih; exact ih
  case effSub => rename_i ih; exact ih
  case nuIn => rename_i ih; exact ih
  case nuOut => rename_i ih; exact ih
  case bangE => rename_i ih; exact ih
  case boxI => rename_i ih; exact ih
  case boxE => rename_i ih; exact ih
  case immSub => rename_i ih; exact ih
  case mutSub => rename_i ih; exact ih
  case roll => rename_i ih; exact ih
  case unroll => rename_i ih; exact ih
  all_goals intro k m he; cdnu_at he

/-- **A slot `!U(A ⊸ F_S B)`, `S` a row with an operation, is not called**: a variable is forced at
an arrow only from a `U` slot (`der_var_arr_thunk`), and is read at a pure arrow `A' ⊸ B'` only
when its thunk is `A' ⊸ F B'`, not `S`'s. -/
theorem not_der_app_varBang {Δ : LifeCtx} {Γ : Ctx VTy} {k m : Nat} {A B : VTy} {S : Row}
    (hS : S ≠ [])
    (hk : ∀ {T : VTy}, Γ[k]? = some ⟨T, true⟩ → T = .bang (.thunk (.arr A (CTy.effOf S B))))
    {j : Jdg} : ¬ CDerivesNU Δ Γ (.app (.var k) (.var m)) j := by
  intro h
  rcases der_app_var_var h k m rfl with ⟨Γ₁, A', C', hlift, hd⟩ | ⟨Γ₂, A', B', hlift, hd⟩
  · obtain ⟨C₀, hC₀⟩ := der_var_arr_thunk hd
    cases hk (hlift hC₀)
  · obtain ⟨T, hT, hI⟩ := der_var_inv hd k rfl
    cases hk (hlift hT)
    have ht : ThunkOf (.thunk (.arr A' (.ret B'))) (.arr A' (.ret B')) := .thunk _
    rcases hI with hI | ⟨C, S', X, hA, -, -⟩
    · have h' := (hI _).mp ht
      have h'' : ThunkOf (.bang (.thunk (.arr A (CTy.effOf S B)))) (.arr A (CTy.effOf S B)) :=
        .bang (.thunk _)
      have hc := ThunkOf.unique h' h''
      simp only [CTy.arr.injEq] at hc
      obtain ⟨-, hr⟩ := hc
      cases S with
      | nil => exact hS rfl
      | cons o S => simp [CTy.effOf] at hr
    · cases hA

/-- **Today's kernel calls no `!U` slot at an effectful arrow**, in A's encoding of a call
(`appE x g`: `(λy. x y) g`), `g` a λ.  The use the plan describes for E1 and E2a ("`[var]`, then
`[allR-E]` at `!U`, then `bangE`, `force` and `[app]`") has no `force` from a persistent slot: a
variable used as a function is a `U` slot. -/
theorem not_der_callBang {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {A B : VTy} {S : Row} {b : Expr}
    (hS : S ≠ []) (hi : Γ[i]? = some ⟨.bang (.thunk (.arr A (CTy.effOf S B))), true⟩) {j : Jdg} :
    ¬ CDerivesNU Δ Γ (appE (.var i) (.lam b)) j := by
  intro h
  have hN : PlainBody (.app (.var (i + 1)) (.var 0)) := by
    refine ⟨fun _ _ h => ?_, fun _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_, fun h => ?_⟩ <;>
      cases h
  have he : appE (.var i) (.lam b) = .app (.lam (.app (.var (i + 1)) (.var 0))) (.lam b) := rfl
  obtain ⟨Δ', Γ', s, j', hlift, hd⟩ := der_appLam_body h _ b he hN
  refine not_der_app_varBang (A := A) (B := B) (k := i + 1) (m := 0) hS (fun {T} hT => ?_) hd
  have := hlift (k := i) (T := T) (by simpa using hT)
  rw [hi] at this
  cases this
  rfl

end Targets.Inst

end
