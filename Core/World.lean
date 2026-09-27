import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Dynamics.Machine
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Notation
import Core.FrameRecords
import Core.SepRange
import Core.Alloc

/-!
# Core — World  `[spec §3, §4]`

`Support/TypedWorld`'s layer `World`, with records typed at `VTy`.  The typed worlds: value shapes `vShape`, the family `TW` of configurations the printed proofs' operations produce, tagging, and `[TR]` p. 6's `wp` over them (`wpTS`, row 5.33's repair).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Alloc ARun)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- An entry of the shape relation's type-variable environment: the closed type the variable
stands for, and the candidate predicate the variable is read at. -/
structure SEnt where
  ty : VTy
  P : Val → WProp

/-- The environment of a closed type: every variable is empty. -/
def sEnv : Option (Nat → SEnt) → Nat → SEnt
  | none => fun n => ⟨.tvar n, fun _ _ => False⟩
  | some η => η

/-- A variable's candidate. -/
def sEnvP : Option (Nat → SEnt) → Nat → Val → WProp
  | none, _, _ => fun _ => False
  | some η, n, v => (η n).P v

/-- The closed type a type stands for under the environment. -/
def sClose : Option (Nat → SEnt) → VTy → VTy
  | none, A => A
  | some η, A => A.subst (fun n => (η n).ty)

/-- `𝒱⟦A⟧`'s shape: `vC` with every `U C` position `True` (no `wp`, so no world family),
`0` empty, and the `Mut` clause asking the stored predicate to be *contained in* the shape
rather than equal to it.  A record or a `TW` premise at `vShape` mentions no `TW`.  At a type
variable the environment's candidate; at `μX. A` the least fixed point `⋂{P | A[P/X] ⊆ P}`,
written in `Prop` (`docs/scope-recursion.md` §2.1), and empty unless the `μ` is closed.
`[about ours: our wp-free payload predicate]` -/
def vShapeE : Option (Nat → SEnt) → VTy → LSub → Val → WProp
  | _, .unit, _, v => ⌜v = .unit⌝
  | η, .tensor T₁ T₂, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vShapeE η T₁ δ v₁ ⋆ vShapeE η T₂ δ v₂
  | η, .sum T₁ T₂, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vShapeE η T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vShapeE η T₂ δ v₂)
  | _, .zero, _, _ => fun _ => False
  | _, .thunk _, _, _ => fun _ => True
  | η, .box a T, δ, v => atLife δ a fun α => box α (vShapeE η T δ v)
  | η, .ref T, δ, v => ex fun ℓ => ex fun v' => ⌜v = .loc ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ vShapeE η T δ v'
  | _, .bang _, _, _ => emp
  | η, .imm a T, δ, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (vShapeE η T δ)
  | η, .mut a T, δ, v => atLife δ a fun α => ex fun ℓ => ⌜v = .loc ℓ⌝ ⋆
      fun ρ => ∃ P, ptoMut ℓ α P ρ ∧ ∀ u σ, P u σ → vShapeE η T δ u σ
  | _, .unk, _, _ => emp
  | _, .int w, _, v => ⌜v.IsInt w⌝
  | η, .tvar n, _, v => sEnvP η n v
  | η, .mu A, δ, v => fun ρ => (sClose η (.mu A)).Cl 0 ∧
      ∀ P : Val → WProp,
        (∀ v' ρ', vShapeE (some (VTy.scons ⟨sClose η (.mu A), P⟩ (sEnv η))) A δ v' ρ' → P v' ρ') →
        P v ρ
  | η, .fam L, δ, v => ex fun ℓ => ex fun c => ⌜v = Val.arr ℓ c⌝ ⋆
      sepRange (fun m => vShapeE η L δ (.loc m)) ℓ c.toNat

/-- `𝒱⟦A⟧`'s shape at a type read with no environment. -/
notation "vShape" => vShapeE none

/-!
Row 5.33 · `wp (e) {Q̂} (ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧,e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧,v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)` · `[repair]`; the printed row is in `Paper/S5_Model/Definitions.lean`.
-/
/-- `W`'s lifetimes are all `⊒ β`: `W ∈ Res_β′` at every `β′ ⊏ β`.  `W.InStratum β` with the
inequality non-strict.  `[spec §4]` -/
def StratumLe (W : WRes) (β : Life) : Prop := ∀ β', β' ⊏ β → W.InStratum β'

theorem stratumLe_of_inStratum {W : WRes} {β : Life} (h : W.InStratum β) : StratumLe W β :=
  fun _ hβ' l ψ e => CellU.InStratum.mono hβ'.le (h l ψ e)

/-- The typed world.  `TW W ps rs`: the configuration `W` — every frame together with the
resource a `wp` runs at, `[TR]` p. 6's `ρ_f ● ρ` — is reached from `∅` by the operations the
printed proofs perform, and `ps` are the frames `[TR]` 6.64 has taken and not ended, `rs` those
frames with every sub-record of their lineages.  One constructor per operation: `alloc`
(6.141), `free` (6.142), `store` (6.145), `immFrame`/`immEnd` (6.64's entry and exit, recording
the frame and its lineage and dropping them), `mutFold`/`mutUnfold` (6.65 and 6.66), and
`reb`/`rebDeep` with `rebEnd`/`rebEndDeep` (6.150's entry and exit, at a record's cell or at a
chain view of one, at any record, a sub-record included).  `reb`'s `β` is at most every lifetime
of the world (`StratumLe`); `rebDeep`'s is below every lifetime of the world, as 6.150's H11
takes it.  The typing premises are at `vShape`, `𝒱⟦T⟧`'s wp-free
shape: a premise at the program's relation would put `TW` under the negative occurrence of
`wpTS` in that relation's `⊸` clause.
`[about ours: the configurations §6 quantifies over, as a family; docs/adjudications.md §12.72]` -/
inductive TW : WRes → List FrameRec → List FrameRec → Prop
  | empty : TW PMap.empty [] []
  | alloc {W W' : WRes} {ps rs : List FrameRec} {μ : BoCa.BoLo.Heap} {l : Loc} {v : Val} :
      TW W ps rs → ResU.Lower W μ → μ l = none →
      ResU.CompS W (ResU.single l (CellU.ownOf v)) W' → ResU.Valid W' → TW W' ps rs
  | immFrame {W X Z R W' : WRes} {ps rs ds : List FrameRec} {l : Loc} {v : Val} {α : Life}
      (T : VTy) (δ : LSub) (h : R.InStratum (LSet.singleton α).join) :
      TW W ps rs → AdmWf T δ → ResU.CompS (ResU.single l (CellU.ownOf v)) R X →
      ResU.CompS X Z W → vShape T δ v R →
      ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W' →
      ResU.Valid W' → (∀ d, d ∈ ds ↔ Desc ⟨l, v, R, T, δ⟩ d) →
      TW W' (⟨l, v, R, T, δ⟩ :: ps) (⟨l, v, R, T, δ⟩ :: (ds ++ rs))
  | reb {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} (x : LifeVar) :
      TW W ps rs → r ∈ rs → W.get le = some (CellU.immOf s r.v r.R hs) →
      ¬ VFree x r.T → ResU.Reb β r.R c →
      vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
      StratumLe W β → ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs
  | rebDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc} {l₀ : Loc}
      {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join} {β : Life}
      (x : LifeVar) :
      TW W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ¬ VFree x S₀ → ResU.Reb β w₀ c →
      vShape (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ c →
      W.InStratum β → ResU.CompS W c W' → ResU.Valid W' → TW W' ps rs
  | mutFold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W →
      ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W' → ResU.Valid W' →
      TW W' ps rs
  | mutUnfold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
      {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X → ResU.CompS X Z W' → ResU.Valid W' →
      TW W' ps rs
  | free {W W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v)) W' W → ResU.Valid W' →
      TW W' ps rs
  | store {W Z W' : WRes} {ps rs : List FrameRec} {l : Loc} {v₁ v₂ : Val} :
      TW W ps rs → ResU.CompS (ResU.single l (CellU.ownOf v₁)) Z W →
      ResU.CompS (ResU.single l (CellU.ownOf v₂)) Z W' → ResU.Valid W' → TW W' ps rs
  | immEnd {W Y X' W' : WRes} {ps rs ps' rs' : List FrameRec} (r : FrameRec) {s : LSet}
      {hs : r.R.InStratum s.join} :
      TW W ps rs → r ∈ ps → ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) Y W →
      ResU.CompS (ResU.single r.le (CellU.ownOf r.v)) r.R X' → ResU.CompS X' Y W' →
      ResU.Valid W' → (∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r)) →
      (∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescR p d) → TW W' ps' rs'
  | rebEnd {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {le : Loc} {s : LSet}
      {β : Life} {hs : r.R.InStratum s.join} :
      TW W ps rs → r ∈ rs → W'.get le = some (CellU.immOf s r.v r.R hs) →
      ResU.Reb β r.R c → ResU.CompS W' (c.restrictDom r.R.exclPart) W →
      W'.InStratum β → TW W' ps rs
  | rebEndDeep {W W' c : WRes} {ps rs : List FrameRec} (r : FrameRec) {p : Option Loc}
      {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
      {β : Life} :
      TW W ps rs → r ∈ rs → Chain r.R r.T r.v p l₀ S₀ u₀ →
      W'.get l₀ = some (CellU.immOf s u₀ w₀ hs) → ResU.Reb β w₀ c →
      ResU.CompS W' (c.restrictDom w₀.exclPart) W → W'.InStratum β → TW W' ps rs

/-- A tagged list agrees with the world: each record's tag is the frame lifetime of a
record proper whose lineage holds it.  `[about ours: our tag discipline]` -/
def Tagged (W : WRes) (ps : List FrameRec) (ls : List SRec) : Prop :=
  ∀ x ∈ ls, ∃ p ∈ ps, DescR p x.1 ∧ FrameLife W p x.2

/-!
Row 4.11 · `ℰ⟦T⟧δ(v) ≜ wp (e) {𝒱⟦T⟧δ}` · `[repair]`; the printed row is in `Paper/S4_LogicalRelation/Definitions.lean`.

Row 5.33, continued.
-/
/-- `[TR]` p. 6's `wp` at a tagged typed world, with its run taken under every allocator.  The
frame quantifier ranges over the completions `ρ_f ● ρ` that are `TW` worlds at the list's
records, tagged, and the post-configuration is one too, with the same records proper and the
same list members: a record 6.64 creates inside a run is ended before the run returns.  The run
is an allocator run of every allocator `A` from every allocation count `k` (`[spec §13]`); every
other conjunct is `Fig16.BoLo.wp`'s, verbatim.  `[about ours: [TR] p. 6's wp relativised to
tagged typed worlds; docs/adjudications.md §12.72]` -/
def wpTS (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    TW fρ ps (rsOf ls) → Tagged fρ ps ls → ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      (∃ k', ARun A k μ e k' μ' (.val v)) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

/-- `wpTS` with its run taken angelically: some run of the machine.  `wpTS` implies it
(`wpTS_angelic`).  `[spec §13]` -/
def wpTSAngelic (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    TW fρ ps (rsOf ls) → Tagged fρ ps ls →
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

end BoCa.Fig16.LogRel.Core

end
