import Core.Relation
import DtorUnwind.Tree.Order

/-!
# `𝒱` and `𝒞` in the tree order

Core's relation (`Core/Relation.lean`, `vCE`/`cC`) with every place it compares lifetimes
read in a `Cactus` `K` instead of the printed chain. The places, all in definitions this file
restates beside the printed ones:

* `ptoImmS` → `ptoImmT`: `α ⊑ ⊓β̄` is `α ⊑ x` at every member `x` of `β̄`; the payload's list
  `ls₀` has the records strictly above some member (`⊓β̄ ⊏ x.2`, `LSet.meet_lt_iff`).
* `ptoMutS` → `ptoMutT`: `α ⊑ b`, and `ls₀` the records strictly above `b`, in `K`. The stored
  predicate's domain stays the printed stratum `Res_b`: it is the carrier's, and the carrier
  keeps the printed chain as its allocation order (`Tree/Order.lean`).
* `box` (`[α]`, row 5.32) → `boxT`: every borrow cell strictly above `α` in `K`.
* `Ext` → `ExtT`: "a borrow cell no longer-lived than `b`" and "strictly longer-lived than
  `b`" read in `K`.
* `LtLife` (row 4.15, at `∀`) → `LtLifeT`.
* `thunkR`/`nuP`/`nuEnv` → `thunkRT`/`nuPT`/`nuEnvT`, which read `Ext`.

Everything else is used as it stands, and at `K = chainC` each restated definition is the
printed one (`ptoImmT_chainC`, `ptoMutT_chainC`, `boxT_chainC`, `extT_chainC`). Not
restated: `wpTS` and its world family `TW`/`Tagged` (records' tags are names; `FrameLife`'s
lineage clause reads `⊑`), `effWp`, and the interpretation of lifetime terms (row 2.54's
`@b₁ ⊓ @b₂`, `@b₁ ⊔ @b₂` on `ℕ`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Tree
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable (K : Cactus)

/-- `ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ` in `K`. -/
def ptoMutT (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (b : Life) (u : Val) (σ : WRes) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q u ⟨σ, h⟩) (ls₀ : List SRec),
    K.le α b ∧ ρ = ResU.single l (CellU.mutOf b u σ h Q hw) ∧ ofS Q = P ls₀ ∧
    (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ K.lt b x.2)) ∧ ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b

/-- `ℓ ↦ I_α 𝒱⟦S⟧(ls|⊐⊓β̄)δ` in `K`: `α` is below every member of `β̄`. -/
def ptoImmT (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) : WProp :=
  fun ρ => ∃ (s : LSet) (u : Val) (σ : WRes) (h : σ.InStratum s.join) (ls₀ : List SRec),
    ρ = ResU.single l (CellU.immOf s u σ h) ∧ P ls₀ u σ ∧ (∀ x, s.mem x → K.le α x) ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ ∃ y, s.mem y ∧ K.lt y x.2)

/-- `[α] P` in `K`. -/
def boxT (α : Life) (P : WProp) : WProp := fun ρ => P ρ ∧ ResU.InStratumT K α ρ

/-- `@ψ ⊑ b` in `K`: some lifetime of the borrow cell is `⊑ b`. -/
def CellAtLe : CellU Loc Val → Life → Prop
  | .own _, _ => False
  | .imm i, b => ∃ y, i.ls.mem y ∧ K.le y b
  | .mut m, b => K.le m.β b

/-- `ρ` holds a borrow cell no longer-lived than `b`, in `K`. -/
def CellInT (ρ : WRes) (b : Life) : Prop :=
  ∃ (m : Loc) (ψ : CellU Loc Val), ρ.get m = some ψ ∧ CellAtLe K ψ b

/-- `Ext` in `K`. -/
def ExtT (ls ls' : List SRec) (ρ : WRes) : Prop :=
  Keeps (rsOf ls) (rsOf ls') ρ ∧
    ∀ b, CellInT K ρ b → ∀ x : SRec, K.lt b x.2 → (x ∈ ls ↔ x ∈ ls')

/-- `α ⊏ @bδ` in `K`. -/
def LtLifeT (δ : LSub) (b : Lifetime.Life) (α : Life) : Prop :=
  ∃ β, b.interp δ = some β ∧ K.lt α β

/-- `thunkR` in `K`. -/
def thunkRT (R : CPred) (ls : List SRec) (v : Val) : WProp := fun ρ =>
  ∀ ls', ExtT K ls ls' ρ → R ls' (.val v) ρ

/-- `nuP` in `K`. -/
def nuPT (R : CPred) : Bool → List SRec → Val → WProp
  | true, ls, v => thunkRT K R ls v
  | false, _, _ => fun _ => True

/-- `nuEnv` in `K`. -/
def nuEnvT (C : CTy) (R : CPred) : Nat → TEnt := VTy.scons ⟨.thunk (.nu C), nuPT K R⟩ (tEnv none)

mutual
/-- `𝒱⟦A⟧(ls)δ(v)` under a type-variable environment.  `full = true`: the program's relation.
`full = false`: the observable view an `Imm` payload is held at, with `U` positions relaxed to
`True`.  At a variable the environment's candidate; at `μX. A` the least fixed point
`⋂{P | A[P/X] ⊆ P}`, joint over the mode and the list and written in `Prop`
(`docs/scope-recursion.md` §2.1), empty unless `X` is outside `A`'s `Mut` payloads (§2.2) and
the `μ` is closed.  `[spec §3]` -/
def vCT : Option (Nat → TEnt) → Bool → VTy → List SRec → LSub → Val → WProp
  | _, _, .unit, _, _, v => ⌜v = .unit⌝
  | η, b, .tensor A B, ls, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vCT η b A ls δ v₁ ⋆ vCT η b B ls δ v₂
  | _, _, .zero, _, _, _ => fun _ => False
  | η, b, .sum A B, ls, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vCT η b A ls δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vCT η b B ls δ v₂)
  | _, true, .thunk C, ls, δ, v => fun ρ =>
      ∀ ls', ExtT K ls ls' ρ → cCT C ls' δ (forceE C (.val v)) ρ
  | _, false, .thunk _, _, _, _ => fun _ => True
  | η, _, .bang A, ls, δ, v => fun ρ => ρ = PMap.empty ∧ vCT η true A ls δ v ρ
  | η, b, .box a A, ls, δ, v => atLife δ a fun α => boxT K α (vCT η b A ls δ v)
  | η, b, .ref A, ls, δ, v =>
      ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vCT η b A ls δ v'
  | η, _, .imm a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ ∧ CohE (rsOf ls) ℓ (tClose η A) δ⌝ ⋆
        ptoImmT K ℓ α ls (fun ls₀ => vCT η false A ls₀ δ)
  | η, _, .mut a A, ls, δ, v =>
      atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
        ptoMutT K ℓ α ls (fun ls₀ => vCT η true A ls₀ δ)
  | _, _, .unk, _, _, _ => emp
  | _, _, .int w, _, _, v => ⌜v.IsInt w⌝
  | _, _, .opq k, _, _, v => k.rel v
  | η, b, .tvar n, ls, _, v => tEnvP η n b ls v
  | η, b, .mu A, ls, δ, v => fun ρ => VTy.NoMut 0 A ∧ (tClose η (.mu A)).Cl 0 ∧
      ∀ P : Bool → List SRec → Val → WProp,
        (∀ b' ls' v' ρ', vCT (some (VTy.scons ⟨tClose η (.mu A), P⟩ (tEnv η))) b' A ls' δ v' ρ' →
          P b' ls' v' ρ') →
        P b ls v ρ
  | η, b, .fam L, ls, δ, v => ex fun ℓ => ex fun c => ⌜v = Val.arr ℓ c ∧ c.toNat < 2 ^ 31⌝ ⋆
      sepRange (fun m => vCT η b L ls δ (.loc m)) ℓ c.toNat
/-- `𝒞⟦C⟧(ls)δ(e)`, curried on the connective.  At `νX. C` the greatest fixed point
`⋃{R | R ⊆ cBT (nuEnvT K C R) C}`, written in `Prop` as `∃ R` (`docs/scope-recursion.md` §3.1), and
trivial unless `C` is positive (`CTy.NuOk`).  At `F_Σ A` the relation at the row's table is
`effWp`: `cwp`, the greatest fixed point over segments, where the row holds `Div`, and `ewpTS`
elsewhere.  `[spec §3, §7, §14, §19]` -/
def cCT : CTy → List SRec → LSub → Expr → WProp
  | .ret A, ls, δ, e => wpTS ls e (fun ls'' => vCT none true A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ =>
      ∀ v, (vCT none true A ls δ v ─⋆ cCT C ls δ (.app e (.val v))) ρ
  | .amp C D, ls, δ, e => fun ρ =>
      cCT C ls δ (.app e (.val (.inj₁ .unit))) ρ ∧ cCT D ls δ (.app e (.val (.inj₂ .unit))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α, (⌜LtLifeT K δ c α⌝ ─⋆ cCT C ls (δ.extend x α) (.app e (.val .unit))) ρ
  | .nu C, ls, δ, e => fun ρ => C.NuOk →
      ∃ R : CPred, R.Le (fun ls' e' => cBT (some (nuEnvT K C R)) C ls' δ e') ∧ R ls e ρ
  | .eff n i q A B fin rc C, ls, δ, e =>
      effWp (CTy.eff n i q A B fin rc C).divAt (OpTab.ext n i
        ⟨q, B.isZero && q != .lin, fun ls v => vCT none true A ls δ v,
          fun ls v => vCT none true B ls δ v, if capB q B then finOblT fin δ else none⟩
          (effTabT C δ)) (effRetT C δ) ls e
/-- The operation table of a row `F_Σ R`'s layers, each capturable entry with its cancel row's
obligation.  `[spec §19, §27]` -/
def effTabT : CTy → LSub → OpTab
  | .eff n i q A B fin _ C, δ => OpTab.ext n i
      ⟨q, B.isZero && q != .lin, fun ls v => vCT none true A ls δ v,
        fun ls v => vCT none true B ls δ v, if capB q B then finOblT fin δ else none⟩ (effTabT C δ)
  | _, _ => OpTab.empty
/-- The cancel obligation of a cancel row: `none` at `⊤`; otherwise the cancel run at the table
of the row's layers (`cancelObl (effTabT F δ)`, `finObl_eq` there).  `[spec §27]` -/
def finOblT : CTy → LSub → Option (List SRec → Expr → WProp)
  | .top, _ => none
  | .eff n i q A B fin _ C, δ => some (cancelObl (OpTab.ext n i
      ⟨q, B.isZero && q != .lin, fun ls v => vCT none true A ls δ v,
        fun ls v => vCT none true B ls δ v, if capB q B then finOblT fin δ else none⟩
        (effTabT C δ)))
  | _, _ => some (cancelObl OpTab.empty)
/-- The answer relation of a row `F_Σ R`: `𝒱⟦R⟧`.  `[spec §19]` -/
def effRetT : CTy → LSub → List SRec → Val → WProp
  | .ret A, δ => fun ls v => vCT none true A ls δ v
  | .eff _ _ _ _ _ _ _ C, δ => effRetT C δ
  | _, _ => fun _ _ _ => False
/-- The answer relation of a row `F_Σ R` under a type-variable environment: `𝒱⟦R⟧` at `η`.
`[spec §19]` -/
def effRetET : Option (Nat → TEnt) → CTy → LSub → List SRec → Val → WProp
  | η, .ret A, δ => fun ls v => vCT η true A ls δ v
  | η, .eff _ _ _ _ _ _ _ C, δ => effRetET η C δ
  | _, _, _ => fun _ _ _ => False
/-- One unfolding of an observation tree under a type-variable environment: `cCT`'s `F`, `&` and
`F_Σ` clauses with `vCT η` at the answer; a row's operation types are closed and read without
`η`; at an observation with an argument, `cCT`'s `⊸` clause with the argument read without `η`
(its type is closed).  Other formers are not observation trees (`CTy.NuLeaf`) and hold
trivially.
`[spec §7, §19, §22]` -/
def cBT : Option (Nat → TEnt) → CTy → List SRec → LSub → Expr → WProp
  | η, .ret A, ls, δ, e => wpTS ls e (fun ls'' => vCT η true A ls'' δ)
  | η, .amp C D, ls, δ, e => fun ρ =>
      cBT η C ls δ (.app e (.val (.inj₁ .unit))) ρ ∧ cBT η D ls δ (.app e (.val (.inj₂ .unit))) ρ
  | η, .eff n i q A B fin rc C, ls, δ, e =>
      effWp (CTy.eff n i q A B fin rc C).divAt (OpTab.ext n i
        ⟨q, B.isZero && q != .lin, fun ls v => vCT none true A ls δ v,
          fun ls v => vCT none true B ls δ v, if capB q B then finOblT fin δ else none⟩
          (effTabT C δ)) (effRetET η C δ) ls e
  | η, .arr A D, ls, δ, e => fun ρ =>
      ∀ v, (vCT none true A ls δ v ─⋆ cBT η D ls δ (.app e (.val v))) ρ
  | _, .top, _, _, _ | _, .all _ _ _, _, _, _ | _, .nu _, _, _, _ =>
      fun _ => True
end
/-! ### At the printed chain, the restated definitions are the printed ones -/

theorem ptoImmT_chainC (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoImmT Cactus.chainC l α ls P = ptoImmS l α ls P := by
  funext ρ
  apply propext
  simp only [ptoImmT, ptoImmS, Cactus.chainC_le, Cactus.chainC_lt]
  constructor
  · rintro ⟨s, u, σ, h, ls₀, e, hP, hα, hls⟩
    refine ⟨s, u, σ, h, ls₀, e, hP, (LSet.le_meet_iff s α).mpr hα, fun x => ?_⟩
    rw [hls x]; exact and_congr_right fun _ => (LSet.meet_lt_iff s x.2).symm
  · rintro ⟨s, u, σ, h, ls₀, e, hP, hα, hls⟩
    refine ⟨s, u, σ, h, ls₀, e, hP, (LSet.le_meet_iff s α).mp hα, fun x => ?_⟩
    rw [hls x]; exact and_congr_right fun _ => LSet.meet_lt_iff s x.2

theorem ptoMutT_chainC (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoMutT Cactus.chainC l α ls P = ptoMutS l α ls P := by
  funext ρ
  apply propext
  simp only [ptoMutT, ptoMutS, Cactus.chainC_le, Cactus.chainC_lt]

theorem boxT_chainC (α : Life) (P : WProp) : boxT Cactus.chainC α P = box α P := by
  funext ρ
  apply propext
  simp only [boxT, box, ResU.inStratumT_chainC]
  exact Iff.rfl

theorem cellAtLe_chainC (ψ : CellU Loc Val) (b : Life) (hk : ψ.kind ≠ Kind.own) :
    CellAtLe Cactus.chainC ψ b ↔ ψ.at ⊑ b := by
  cases ψ with
  | own _ => exact absurd rfl hk
  | imm i =>
      show (∃ y, i.ls.mem y ∧ y ≤ b) ↔ i.ls.meet ≤ b
      exact ⟨fun ⟨y, hy, h⟩ => le_trans (i.ls.meet_least y hy) h,
        fun h => ⟨_, i.ls.meet_mem, h⟩⟩
  | «mut» m => exact Iff.rfl

theorem extT_chainC (ls ls' : List SRec) (ρ : WRes) :
    ExtT Cactus.chainC ls ls' ρ ↔ Ext ls ls' ρ := by
  have hc : ∀ b, CellInT Cactus.chainC ρ b ↔ CellIn ρ b := fun b => by
    constructor
    · rintro ⟨m, ψ, e, h⟩
      have hk : ψ.kind ≠ Kind.own := by cases ψ <;> simp_all [CellAtLe, CellU.kind]
      exact ⟨m, ψ, e, hk, (cellAtLe_chainC ψ b hk).mp h⟩
    · rintro ⟨m, ψ, e, hk, h⟩
      exact ⟨m, ψ, e, (cellAtLe_chainC ψ b hk).mpr h⟩
  simp only [ExtT, Ext, hc, Cactus.chainC_lt]

end BoCa.Fig16.LogRel.Core.Tree

end
