import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Support.Statics.Contexts
import Core.Types
import Core.FrameRecords
import Core.World
import Core.EffDefs
import Core.DivDefs

/-!
# Core — Relation  `[spec §3, §6, §7]`

The mode-indexed CBPV relation over the typed world whose records are typed at `VTy`.

`vC b A` interprets value types and `cC C` computation types, over the tagged `wpTS`: the
Kripke quantifier over `Ext` sits at `U` only, `wpTS` at `F` only.  `b = false` is the observable
view an `Imm` payload is held at, with `U` relaxed to `True`.  The resource clauses are the
typed world's (`ptoOwn`, `ptoImmS`, `ptoMutS`, `atLife`/`box`, `ρ = ∅` at `!`, `emp` at `Unk`),
and the `Imm` clause reads the coherence `CohE` at the payload type itself.

A thunk of `F A` is `λ_. M`, forced by applying it to `()`; a thunk of any other computation
type is the λ-value that computation is, forced by using it as it stands (`forceE`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ`: a `mut` cell at `b ⊒ α` whose stored predicate is `P ls₀`, `ls₀`
having the members of `ls` strictly longer-lived than `b`; and `P` lies in `Res_b` at every
list. -/
def ptoMutS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P ls₀ ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b)) ∧ ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b

/-- `ℓ ↦ I_α 𝒱⟦S⟧(ls|⊐⊓β̄)δ`: an `imm` cell `imm(β̄, u, σ)` with `α ⊑ ⊓β̄` whose payload holds
at `ls₀`, the members of `ls` strictly longer-lived than the cell. -/
def ptoImmS (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P ls₀ u σ ∧ α ⊑ s.meet ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ s.meet)

/-- `Coh` up to `TyEq`. -/
def CohE (rs : List FrameRec) (m : Loc) (S : VTy) (δ : LSub) : Prop :=
  ∃ S₀ δ₀, TyEq S δ S₀ δ₀ ∧ Coh rs m S₀ δ₀

/-- `force`, at the computation type forced.  A thunk of `F A` is `λ_. M` and is forced by
applying it to `()`; a thunk of any other computation type is the λ-value that computation
already is, and is forced by using it as it stands.  A thunk of `F_Σ A` is forced as one of
`F A`. -/
def forceE : CTy → Expr → Expr
  | .ret _, e => .app e (.val .unit)
  | .eff _ _ _ _ _ _ _, e => .app e (.val .unit)
  | _, e => e

/-- An entry of the relation's type-variable environment: the closed type the variable stands
for (the `Imm` clause reads coherence at it) and the candidate the variable is read at, over
the mode, the record list and the value. -/
structure TEnt where
  ty : VTy
  P : Bool → List SRec → Val → WProp

/-- The environment of a closed type: every variable is empty. -/
def tEnv : Option (Nat → TEnt) → Nat → TEnt
  | none => fun n => ⟨.tvar n, fun _ _ _ _ => False⟩
  | some η => η

/-- A variable's candidate. -/
def tEnvP : Option (Nat → TEnt) → Nat → Bool → List SRec → Val → WProp
  | none, _, _, _, _ => fun _ => False
  | some η, n, b, ls, v => (η n).P b ls v

/-- The closed type a type stands for under the environment. -/
def tClose : Option (Nat → TEnt) → VTy → VTy
  | none, A => A
  | some η, A => A.subst (fun n => (η n).ty)

/-- A candidate interpretation of `νX. C` at a fixed lifetime substitution: `cC`'s signature with
`δ` applied (`νX. C` binds no lifetime, so its unfolding never changes `δ`). -/
abbrev CPred := List SRec → Expr → WProp

/-- `R ⊆ R'` pointwise. -/
def CPred.Le (R R' : CPred) : Prop := ∀ ls e, Entails (R ls e) (R' ls e)

/-- `vC true (U X)` at the candidate `R` for `X`, a computation type forced as it stands. -/
def thunkR (R : CPred) (ls : List SRec) (v : Val) : WProp := fun ρ =>
  ∀ ls', Ext ls ls' ρ → R ls' (.val v) ρ

/-- The variable `U X` of `νX. C` read at the candidate `R`: `thunkR R` in the program's mode,
`True` in the observable view (`vCE`'s `U` clauses). -/
def nuP (R : CPred) : Bool → List SRec → Val → WProp
  | true, ls, v => thunkR R ls v
  | false, _, _ => fun _ => True

/-- The environment of `C`'s value types in one unfolding of `νX. C` at the candidate `R`:
the variable `0` is `U(νX. C)`, read at `nuP R`. -/
def nuEnv (C : CTy) (R : CPred) : Nat → TEnt := VTy.scons ⟨.thunk (.nu C), nuP R⟩ (tEnv none)

mutual
/-- `𝒱⟦A⟧(ls)δ(v)` under a type-variable environment.  `full = true`: the program's relation.
`full = false`: the observable view an `Imm` payload is held at, with `U` positions relaxed to
`True`.  At a variable the environment's candidate; at `μX. A` the least fixed point
`⋂{P | A[P/X] ⊆ P}`, joint over the mode and the list and written in `Prop`
(`docs/scope-recursion.md` §2.1), empty unless `X` is outside `A`'s `Mut` payloads (§2.2) and
the `μ` is closed.  `[spec §3]` -/
def vCE : Option (Nat → TEnt) → Bool → VTy → List SRec → LSub → Val → WProp
  | _, _, .unit, _, _, v => ⌜v = .unit⌝
  | η, b, .tensor A B, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vCE η b A ls δ v₁ ⋆ vCE η b B ls δ v₂
  | _, _, .zero, _, _, _ => fun _ => False
  | η, b, .sum A B, ls, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vCE η b A ls δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vCE η b B ls δ v₂)
  | _, true, .thunk C, ls, δ, v => fun ρ =>
      ∀ ls', Ext ls ls' ρ → cC C ls' δ (forceE C (.val v)) ρ
  | _, false, .thunk _, _, _, _ => fun _ => True
  | η, _, .bang A, ls, δ, v => fun ρ => ρ = PMap.empty ∧ vCE η true A ls δ v ρ
  | η, b, .box a A, ls, δ, v => atLife δ a fun α => box α (vCE η b A ls δ v)
  | η, b, .ref A, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vCE η b A ls δ v'
  | η, _, .imm a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ ∧ CohE (rsOf ls) ℓ (tClose η A) δ⌝ ⋆
        ptoImmS ℓ α ls (fun ls₀ => vCE η false A ls₀ δ)
  | η, _, .mut a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutS ℓ α ls (fun ls₀ => vCE η true A ls₀ δ)
  | _, _, .unk, _, _, _ => emp
  | _, _, .int w, _, _, v => ⌜v.IsInt w⌝
  | _, _, .opq k, _, _, v => ⌜k.Holds v⌝
  | η, b, .tvar n, ls, _, v => tEnvP η n b ls v
  | η, b, .mu A, ls, δ, v => fun ρ => VTy.NoMut 0 A ∧ (tClose η (.mu A)).Cl 0 ∧
      ∀ P : Bool → List SRec → Val → WProp,
        (∀ b' ls' v' ρ', vCE (some (VTy.scons ⟨tClose η (.mu A), P⟩ (tEnv η))) b' A ls' δ v' ρ' →
          P b' ls' v' ρ') →
        P b ls v ρ
  | η, b, .fam L, ls, δ, v => ex fun ℓ => ex fun c => ⌜v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31⌝ ⋆
      sepRange (fun m => vCE η b L ls δ (.loc m)) ℓ c.toNat
/-- `𝒞⟦C⟧(ls)δ(e)`, curried on the connective.  At `νX. C` the greatest fixed point
`⋃{R | R ⊆ cB (nuEnv C R) C}`, written in `Prop` as `∃ R` (`docs/scope-recursion.md` §3.1), and
trivial unless `C` is positive (`CTy.NuOk`).  At `F_Σ A` the relation at the row's table is
`effWp`: `cwp`, the greatest fixed point over segments, where the row holds `Div`, and `ewpTS`
elsewhere.  `[spec §3, §7, §14, §19]` -/
def cC : CTy → List SRec → LSub → Expr → WProp
  | .ret A, ls, δ, e => wpTS ls e (fun ls'' => vCE none true A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ =>
      ∀ v, (vCE none true A ls δ v ─⋆ cC C ls δ (.app e (.val v))) ρ
  | .amp C D, ls, δ, e => fun ρ =>
      cC C ls δ (.app e (.val (.inj₁ .unit))) ρ ∧ cC D ls δ (.app e (.val (.inj₂ .unit))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α, (⌜LtLife δ c α⌝ ─⋆ cC C ls (δ.extend x α) (.app e (.val .unit))) ρ
  | .nu C, ls, δ, e => fun ρ => C.NuOk →
      ∃ R : CPred, R.Le (fun ls' e' => cB (some (nuEnv C R)) C ls' δ e') ∧ R ls e ρ
  | .eff n i q A B fin C, ls, δ, e =>
      effWp (CTy.eff n i q A B fin C).divAt (OpTab.ext n i
        ⟨q, B.isZero && q != .lin, fun ls v => vCE none true A ls δ v,
          fun ls v => vCE none true B ls δ v, if capB q B then finObl fin δ else none⟩
          (effTab C δ)) (effRet C δ) ls e
/-- The operation table of a row `F_Σ R`'s layers, each capturable entry with its cancel row's
obligation.  `[spec §19, §27]` -/
def effTab : CTy → LSub → OpTab
  | .eff n i q A B fin C, δ => OpTab.ext n i
      ⟨q, B.isZero && q != .lin, fun ls v => vCE none true A ls δ v,
        fun ls v => vCE none true B ls δ v, if capB q B then finObl fin δ else none⟩ (effTab C δ)
  | _, _ => OpTab.empty
/-- The cancel obligation of a cancel row: `none` at `⊤`; otherwise the cancel run at the table
of the row's layers (`cancelObl (effTab F δ)`, `finObl_eq`).  `[spec §27]` -/
def finObl : CTy → LSub → Option (List SRec → Expr → WProp)
  | .top, _ => none
  | .eff n i q A B fin C, δ => some (cancelObl (OpTab.ext n i
      ⟨q, B.isZero && q != .lin, fun ls v => vCE none true A ls δ v,
        fun ls v => vCE none true B ls δ v, if capB q B then finObl fin δ else none⟩
        (effTab C δ)))
  | _, _ => some (cancelObl OpTab.empty)
/-- The answer relation of a row `F_Σ R`: `𝒱⟦R⟧`.  `[spec §19]` -/
def effRet : CTy → LSub → List SRec → Val → WProp
  | .ret A, δ => fun ls v => vCE none true A ls δ v
  | .eff _ _ _ _ _ _ C, δ => effRet C δ
  | _, _ => fun _ _ _ => False
/-- The answer relation of a row `F_Σ R` under a type-variable environment: `𝒱⟦R⟧` at `η`.
`[spec §19]` -/
def effRetE : Option (Nat → TEnt) → CTy → LSub → List SRec → Val → WProp
  | η, .ret A, δ => fun ls v => vCE η true A ls δ v
  | η, .eff _ _ _ _ _ _ C, δ => effRetE η C δ
  | _, _, _ => fun _ _ _ => False
/-- One unfolding of an observation tree under a type-variable environment: `cC`'s `F`, `&` and
`F_Σ` clauses with `vCE η` at the answer; a row's operation types are closed and read without
`η`; at an observation with an argument, `cC`'s `⊸` clause with the argument read without `η`
(its type is closed).  Other formers are not observation trees (`CTy.NuLeaf`) and hold
trivially.
`[spec §7, §19, §22]` -/
def cB : Option (Nat → TEnt) → CTy → List SRec → LSub → Expr → WProp
  | η, .ret A, ls, δ, e => wpTS ls e (fun ls'' => vCE η true A ls'' δ)
  | η, .amp C D, ls, δ, e => fun ρ =>
      cB η C ls δ (.app e (.val (.inj₁ .unit))) ρ ∧ cB η D ls δ (.app e (.val (.inj₂ .unit))) ρ
  | η, .eff n i q A B fin C, ls, δ, e =>
      effWp (CTy.eff n i q A B fin C).divAt (OpTab.ext n i
        ⟨q, B.isZero && q != .lin, fun ls v => vCE none true A ls δ v,
          fun ls v => vCE none true B ls δ v, if capB q B then finObl fin δ else none⟩
          (effTab C δ)) (effRetE η C δ) ls e
  | η, .arr A D, ls, δ, e => fun ρ =>
      ∀ v, (vCE none true A ls δ v ─⋆ cB η D ls δ (.app e (.val v))) ρ
  | _, .top, _, _, _ | _, .all _ _ _, _, _, _ | _, .nu _, _, _, _ =>
      fun _ => True
end

theorem effRetE_none : ∀ (C : CTy) (δ : LSub), effRetE none C δ = effRet C δ
  | .ret _, _ => rfl
  | .eff _ _ _ _ _ _ C, δ => effRetE_none C δ
  | .arr _ _, _ | .amp _ _, _ | .top, _ | .all _ _ _, _ | .nu _, _ => rfl

/-- `𝒱⟦A⟧(ls)δ(v)`: the relation at a type read with no environment. -/
notation "vC" => vCE none

/-- The program's relation. -/
abbrev vP : VTy → List SRec → LSub → Val → WProp := vC true

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧(ls)δ(γ(x))`. -/
def gSepC (ls : List SRec) (δ : LSub) : Ctx VTy → List Val → WProp
  | [],     _      => emp
  | _ :: _, []     => emp
  | s :: Γ, v :: γ => if s.live then vC true s.ty ls δ v ⋆ gSepC ls δ Γ γ else gSepC ls δ Γ γ

/-- `𝒢⟦Γ⟧(ls)δ(γ)`. -/
def gDenC (ls : List SRec) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) : WProp :=
  ⌜Ctx.LiveWithin Γ γ⌝ ⋆ gSepC ls δ Γ γ

/-- `Δ; Γ ⊨ e : C`, at every record list.  `[spec §3]` -/
def SemC (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ δ γ (ls : List SRec) ρ, Δ.Models δ → gDenC ls δ Γ γ ρ → cC C ls δ (substAll γ e) ρ

/-- `Δ; Γ ⊨ V : A` for a value: `return V` at `F A`.  `[spec §3]` -/
abbrev SemV (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy) : Prop := SemC Δ Γ e (.ret A)

/-- `!Γ`: every live slot is at a `!` type. -/
def Ctx.Banged (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → ∃ A, s.ty = .bang A

end BoCa.Fig16.LogRel.Core

end
