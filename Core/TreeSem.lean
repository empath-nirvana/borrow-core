import Core.TreeWpEff
import Core.Types
import Support.Model.Tree.KSem

/-!
# The relation's value types at the lifetime tree  `[spec §62]`

A value type of the step-indexed relation over the tree world (`Core/TreeWp.lean`) is `STy`: a
predicate `P n w ls v ρ` at the step index `n`, the tree world `w` (its tree `w.K` and code typing
`w.Θ`), the record list `ls` the relation reads (the open lends' records, tagged), a value and a
resource, with two laws as fields:

* **downward closed in the index** (`TVal.Down`);
* **monotone along the tree** (`TVal.Mono`): at every world extension `w.Ext w′ ρ` (the tree keeps
  every nesting, the code typing is kept where `ρ` holds a `mut` cell), on the re-reading of a
  covered `ρ` at `w′` (`RRw`), at every list `ls′` at `w′` keeping the re-readings of the records of
  `ls` that `ρ` reads (`KeepRel`, the per-branch condition of a stored continuation's share,
  `contShareT`), the value is in the type at `w′`, `ls′`. Records of `ls` that `ρ` does not read
  may be gone from `ls′`: another branch may have ended them. A value stored before a graft is a
  value of its type after it (`STy.reread`: the re-reading exists, and the value meets the type
  there at every such list).

**Why the list** (departure E3 resolved, #794). A thunk's meaning is a run of the relation, and a
run is at a list. A value type that does not read the list can only run its thunks at a list fixed
in advance, and the only list every world has is `[]`. At `[]` a run says nothing of a resource
holding a view: no world with an empty list holds an `imm` cell (`cerwpT_nil_of_imm`,
`Core/TreeSemC.lean`), so such a thunk type holds of every thunk holding a borrow, resumable or
not. Read at the list, a thunk is a run at every later list keeping the records it reads, which is
what a stored continuation's share gives (`STy.kont_of_share`, `Core/TreeSemK.lean`).

Every former is an `STy` constructor, both laws proved from the components': codes (`STy.code`),
`1`, `0`, `+`, `⊗`, `Imm`, `Mut`, `[a]`, `ref`, `!`, `Unk`, the integers, the opaque types, the
families `[L]`, thunks (`STy.thunk`), `μ` (`STy.mu`) and type variables (`STy.var`). The
computation types, `ν`, `∀` over lifetimes and thunks read at `cerwpT` are `Core/TreeSemC.lean`.
Continuation and task types are `Core/TreeSemK.lean`.

**What carries `Mut`.** `STy.mut`'s monotonicity holds by definition: its invariant is its
location's code read at the world, and `RC` re-reads it so. What carries it is that the re-read
cell's invariant is the store type at the new tree (`RC.mut_inv`), so a lender reads back a value
of the store type (`RC.mut_readback`); the re-read invariant holds wherever the old one held, on
carried resources (`RC.mut_extends`); and an invariant other than the store type is not a
re-reading (`not_rc_of_inv_ne`). Carried instead as a fixed predicate (row 5.57's extension by
falsity, `trU`), `Mut` is not monotone (`Support/Model/Tree/KSemGraft.lean`'s `trU_not_kmono`).

**Departures** (`docs/new-core/scope-782.md` §2):
* E1: `Mut`'s payload is a store code (`KTy`), not an `STy`. A cell's invariant is index-free
  (`MutT.P`), so a step-indexed payload (a thunk in a cell) needs step-indexed cell invariants,
  which the carrier does not have. Every code is an `STy` (`STy.code`). Core's `μ` keeps `X` out
  of `Mut` payloads (`VTy.NoMut`), and here it cannot be in one.
* E2: one mode. Core reads an `Imm` payload in the observable view (`vCE false`, `U` relaxed to
  `True`); here the payload is read in full.
* E3, owned records: a value's meaning reads the list but owns no records; a thunk runs owning
  none (`SCmp.ret`). A continuation that owns the records of lends its own branch opened is row 6's.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.LogRel.Core (Opaque)

/-! ### Value types -/

/-- A value predicate at the step index, the tree world and the record list. -/
abbrev TVal : Type := Nat → (w : TWd) → List (SRecT w.K) → BoCa.Val → TRes w.K → Prop

/-- Downward closed in the step index. -/
def TVal.Down (P : TVal) : Prop := ∀ n w ls v ρ, P (n + 1) w ls v ρ → P n w ls v ρ

/-- **Monotone along the tree**: at every world extension carrying `ρ`, on the re-reading of a
covered `ρ` there, at every list keeping the records of `ls` that `ρ` reads (`KeepRel`). -/
def TVal.Mono (P : TVal) : Prop :=
  ∀ n (w w' : TWd) (ls : List (SRecT w.K)) (ls' : List (SRecT w'.K)) v (ρ : TRes w.K)
    (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ →
    CovR (sem w.Θ) w.K ρ → P n w ls v ρ → P n w' ls' v ρ'

/-- **A value type of the relation at the tree**: downward closed in the index and monotone along
the tree. -/
structure STy where
  P : TVal
  down : P.Down
  mono : P.Mono

/-- Inclusion of value types. -/
def STy.Le (σ τ : STy) : Prop := ∀ n w ls v ρ, σ.P n w ls v ρ → τ.P n w ls v ρ

theorem STy.le_refl (τ : STy) : τ.Le τ := fun _ _ _ _ _ h => h

theorem STy.le_trans {σ τ υ : STy} (h₁ : σ.Le τ) (h₂ : τ.Le υ) : σ.Le υ :=
  fun n w ls v ρ h => h₂ n w ls v ρ (h₁ n w ls v ρ h)

theorem STy.down_le (τ : STy) {m n : Nat} (h : m ≤ n) :
    ∀ w ls v ρ, τ.P n w ls v ρ → τ.P m w ls v ρ := by
  induction h with
  | refl => exact fun _ _ _ _ x => x
  | step _ ih => exact fun w ls v ρ x => ih w ls v ρ (τ.down _ w ls v ρ x)

/-- **A value stored before a graft meets its type after it.** At every world extension carrying a
covered resource, the resource has a re-reading, covered at the new world, and the value is a
value of its type over it at every list keeping the records of `ls` the resource reads. -/
theorem STy.reread (τ : STy) {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)} {v : BoCa.Val}
    {ρ : TRes w.K} (hE : w.Ext w' ρ) (hc : CovR (sem w.Θ) w.K ρ) (h : τ.P n w ls v ρ) :
    ∃ ρ' : TRes w'.K, RRw (w := w) (w' := w') ρ ρ' ∧ CovR (sem w'.Θ) w'.K ρ' ∧
      ∀ ls' : List (SRecT w'.K), KeepRel w'.Θ ls ls' ρ → τ.P n w' ls' v ρ' := by
  obtain ⟨ρ', hr, hc'⟩ := RR.exists_retype hE.1 hc hE.2
  exact ⟨ρ', hr, hc', fun ls' hk => τ.mono n w w' ls ls' v ρ ρ' hE hr hk hc h⟩

/-! ### The records a resource reads, at its parts -/

/-- A location frozen in `ρ₁` is frozen in every `ρ` holding `ρ₁`'s cells. -/
theorem FrzT.of_get_sub {K : WCactus} {ρ₁ ρ : TRes K}
    (hs : ∀ m ψ, ρ₁.get m = some ψ → ρ.get m = some ψ) {m : BoCa.Loc} (h : FrzT ρ₁ m) :
    FrzT ρ m := by
  cases h with
  | imm e k => exact FrzT.imm (hs _ _ e) k
  | inImm e k hd => exact FrzT.inImm (hs _ _ e) k hd
  | inMut e k hf => exact FrzT.inMut (hs _ _ e) k hf

/-- A frozen location lies at some depth inside the resource. -/
theorem FrzT.inDom {K : WCactus} {ρ : TRes K} {m : BoCa.Loc} (h : FrzT ρ m) : InDomT ρ m := by
  induction h with
  | imm e _ => exact InDomT.top e
  | inImm e k hd => exact InDomT.wit e (by rw [k]; decide) hd
  | inMut e k _ ih => exact InDomT.wit e (by rw [k]; decide) ih

/-- A record the payload of a view reads, the view reads. -/
theorem RelFT.of_imm_res {K : WCactus} {r : FrameRecT K} {l : BoCa.Loc} {i : TImm K}
    (h : RelFT r i.res) : RelFT r (PMap.sng l (CellUT.imm i)) := by
  obtain ⟨m, hf, hm⟩ := h
  exact ⟨m, FrzT.inImm (m' := l) (ψ := CellUT.imm i) (by simp [PMap.sng_get]) rfl hf.inDom, hm⟩

theorem KeepRel.of_imm_res {K K' : WCactus} {Θ' : CodeTy} {ls : List (SRecT K)}
    {ls' : List (SRecT K')} {l : BoCa.Loc} {i : TImm K}
    (h : KeepRel Θ' ls ls' (PMap.sng l (CellUT.imm i))) : KeepRel Θ' ls ls' i.res :=
  fun r hr hrel => h r hr hrel.of_imm_res

theorem KeepRel.of_get_sub {K K' : WCactus} {Θ' : CodeTy} {ls : List (SRecT K)}
    {ls' : List (SRecT K')} {ρ₁ ρ : TRes K} (hs : ∀ m ψ, ρ₁.get m = some ψ → ρ.get m = some ψ)
    (h : KeepRel Θ' ls ls' ρ) : KeepRel Θ' ls ls' ρ₁ :=
  fun r hr ⟨m, hf, hm⟩ => h r hr ⟨m, hf.of_get_sub hs, hm⟩

theorem KeepRel.of_compS_right {K K' : WCactus} {Θ' : CodeTy} {ls : List (SRecT K)}
    {ls' : List (SRecT K')} {ρ₁ ρ₂ ρ : TRes K} (hc : ResUT.CompS ρ₁ ρ₂ ρ)
    (h : KeepRel Θ' ls ls' ρ) : KeepRel Θ' ls ls' ρ₂ :=
  KeepRel.of_compS_left (ResUT.CompS.comm hc) h

/-! ### Store codes -/

/-- **A store code as a value type**: its meaning at the world's code typing, read at the tree,
at every index and list. Monotone by `interp_retype`. -/
def STy.code (A : KTy) : STy where
  P _ w _ v ρ := (A.interp w.Θ).P w.K v ρ
  down _ _ _ _ _ h := h
  mono _ _ _ _ _ v ρ ρ' hE hr _ hc h := interp_retype A hE.1 v ρ ρ' hc hr hE.2 h

/-! ### `1`, `0`, `+`, `⊗` -/

/-- `𝒱⟦1⟧`. -/
def STy.unit : STy where
  P _ _ _ v ρ := v = BoCa.Val.unit ∧ ρ = PMap.empty
  down _ _ _ _ _ h := h
  mono := by
    rintro n w w' ls ls' v ρ ρ' - hr - - ⟨hv, rfl⟩
    exact ⟨hv, RR.of_empty hr⟩

/-- `𝒱⟦0⟧`. -/
def STy.zero : STy where
  P _ _ _ _ _ := False
  down _ _ _ _ _ h := h
  mono _ _ _ _ _ _ _ _ _ _ _ _ h := h

/-- `𝒱⟦A + B⟧`. -/
def STy.sum (τ₁ τ₂ : STy) : STy where
  P n w ls v ρ := (∃ v₁, v = BoCa.Val.inj₁ v₁ ∧ τ₁.P n w ls v₁ ρ) ∨
    (∃ v₂, v = BoCa.Val.inj₂ v₂ ∧ τ₂.P n w ls v₂ ρ)
  down := by
    rintro n w ls v ρ (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩)
    · exact Or.inl ⟨v₁, rfl, τ₁.down n w ls v₁ ρ h⟩
    · exact Or.inr ⟨v₂, rfl, τ₂.down n w ls v₂ ρ h⟩
  mono := by
    rintro n w w' ls ls' v ρ ρ' hE hr hk hc (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩)
    · exact Or.inl ⟨v₁, rfl, τ₁.mono n w w' ls ls' v₁ ρ ρ' hE hr hk hc h⟩
    · exact Or.inr ⟨v₂, rfl, τ₂.mono n w w' ls ls' v₂ ρ ρ' hE hr hk hc h⟩

/-- `𝒱⟦A ⊗ B⟧`: the two components over the parts of a composite, at the same list. Monotone
because the re-reading of a composite is the composite of the parts' re-readings
(`RR.split_retype`), and a list keeping the records the composite reads keeps those each part
reads (`KeepRel.of_compS_left`). -/
def STy.tensor (τ₁ τ₂ : STy) : STy where
  P n w ls v ρ := ∃ (v₁ v₂ : BoCa.Val) (ρ₁ ρ₂ : TRes w.K), v = BoCa.Val.pair v₁ v₂ ∧
    ResUT.CompS ρ₁ ρ₂ ρ ∧ τ₁.P n w ls v₁ ρ₁ ∧ τ₂.P n w ls v₂ ρ₂
  down := by
    rintro n w ls v ρ ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, h₁, h₂⟩
    exact ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, τ₁.down n w ls v₁ ρ₁ h₁, τ₂.down n w ls v₂ ρ₂ h₂⟩
  mono := by
    rintro n w w' ls ls' v ρ ρ' hE hr hk hc ⟨v₁, v₂, ρ₁, ρ₂, rfl, hcomp, h₁, h₂⟩
    obtain ⟨a', b', ha, hb, hc'⟩ := RR.split_retype hE.1 hcomp hc hE.2 hr
    exact ⟨v₁, v₂, a', b', rfl, hc',
      τ₁.mono n w w' ls ls' v₁ ρ₁ a' (hE.of_compS_left hcomp) ha (hk.of_compS_left hcomp)
        (hc.of_compS_left hcomp) h₁,
      τ₂.mono n w w' ls ls' v₂ ρ₂ b' (hE.of_compS_right hcomp) hb (hk.of_compS_right hcomp)
        (hc.of_compS_right hcomp) h₂⟩

/-! ### `Imm`, `Mut`, boxes, `ref` -/

/-- `𝒱⟦Imm @a A⟧`: a view `ℓ ↦ imm(β̄, u, χ)` with `a ⊑ x` at every member `x` of `β̄` read in the
current tree, and the payload `u` in `A` over the witness `χ`, at the same list. -/
def STy.imm (a : Life) (τ : STy) : STy where
  P n w ls v ρ := ∃ (l : BoCa.Loc) (i : TImm w.K), v = BoCa.Val.loc l ∧ ρ = PMap.sng l (.imm i) ∧
    (∀ x ∈ i.ls.set, w.K.le a x) ∧ τ.P n w ls i.v i.res
  down := by
    rintro n w ls v ρ ⟨l, i, rfl, rfl, hle, h⟩
    exact ⟨l, i, rfl, rfl, hle, τ.down n w ls i.v i.res h⟩
  mono := by
    rintro n w w' ls ls' v ρ ρ' hE hr hk hc ⟨l, i, rfl, rfl, hle, hP⟩
    obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
    have hci := hc.sng
    have e : (PMap.sng l (CellUT.imm i) : TRes w.K).get l = some (.imm i) := by
      simp [PMap.sng_get]
    cases hrc with
    | imm _ _ i' hs hv hdom hw =>
        cases hci with
        | imm _ _ hcw =>
            refine ⟨l, i', rfl, rfl, fun x hx => WCactus.Ext.le hE.1 (hle x (hs ▸ hx)), ?_⟩
            rw [hv]
            exact τ.mono n w w' ls ls' _ _ _ ⟨hE.1, hE.2.wit e⟩ ⟨hdom, hw⟩ hk.of_imm_res hcw hP

/-- `𝒱⟦Mut @a A⟧` at a store code `A` (departure E1): a cell `ℓ ↦ mut(β̄, u, χ, P̂)` with
`a ⊑ x` at every member of `β̄`, the location typed `A`, and the invariant `A` read at the world
(`STy.mut_iff`). Its monotonicity is `STy.code`'s, so it holds by the definitions of the code's
meaning and of `RC`, which stores the location's code read at the new tree; what carries the
contents is `RC.mut_inv`, `RC.mut_readback` and `RC.mut_extends`. -/
def STy.mut (a : Life) (A : KTy) : STy := STy.code (.mut a A)

theorem STy.mut_iff {a : Life} {A : KTy} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {v : BoCa.Val} {ρ : TRes w.K} :
    (STy.mut a A).P n w ls v ρ ↔ ∃ (l : BoCa.Loc) (m : TMut w.K), v = BoCa.Val.loc l ∧
      ρ = PMap.sng l (.mut m) ∧ w.Θ l = some A ∧ (∀ x ∈ m.ls.set, w.K.le a x) ∧
      ∀ u r, m.P u r ↔ (A.interp w.Θ).P w.K u r.toU :=
  Iff.rfl

/-- `𝒱⟦[a] A⟧` (row 5.32's box): `A`, every borrow cell strictly longer-lived than `a`. -/
def STy.box (a : Life) (τ : STy) : STy where
  P n w ls v ρ := τ.P n w ls v ρ ∧ ρ.InStratum (TSet.single a)
  down n w ls v ρ h := ⟨τ.down n w ls v ρ h.1, h.2⟩
  mono n w w' ls ls' v ρ ρ' hE hr hk hc h :=
    ⟨τ.mono n w w' ls ls' v ρ ρ' hE hr hk hc h.1, hr.inStratum hE.1 h.2⟩

/-- `𝒱⟦ref A⟧`: `ℓ ↦ own(u)` beside a resource of the payload, at the same list. -/
def STy.ref (τ : STy) : STy where
  P n w ls v ρ := ∃ (l : BoCa.Loc) (u : BoCa.Val) (ρ₁ : TRes w.K), v = BoCa.Val.loc l ∧
    ρ₁.get l = none ∧ ρ = PMap.ins ρ₁ l (.own u) ∧ τ.P n w ls u ρ₁
  down := by
    rintro n w ls v ρ ⟨l, u, ρ₁, rfl, hl, rfl, h⟩
    exact ⟨l, u, ρ₁, rfl, hl, rfl, τ.down n w ls u ρ₁ h⟩
  mono := by
    classical
    rintro n w w' ls ls' v ρ ρ' hE hr hk hc ⟨l, u, ρ₁, rfl, hl, rfl, hP⟩
    obtain ⟨ψ', e', hrc⟩ := hr.get_some (m := l) (ψ := .own u) (by simp [PMap.ins_get])
    cases hrc
    have hr₁ : RRw (w := w) (w' := w') ρ₁ (PMap.del ρ' l) := by
      refine ⟨fun m => ?_, fun m χ χ' e e'' => ?_⟩
      · rw [PMap.del_get]
        by_cases e : m = l
        · subst e; simp [hl]
        · rw [if_neg e]
          have := hr.1 m
          simp only [PMap.ins_get, if_neg e] at this
          exact this
      · rw [PMap.del_get] at e''
        by_cases em : m = l
        · rw [if_pos em] at e''; cases e''
        · rw [if_neg em] at e''
          exact hr.2 m χ χ' (by simp [PMap.ins_get, em, e]) e''
    have hne : ∀ m χ, ρ₁.get m = some χ → m ≠ l := fun m χ e h => by
      subst h; rw [hl] at e; cases e
    have hsub : ∀ m χ, ρ₁.get m = some χ → (PMap.ins ρ₁ l (CellUT.own u)).get m = some χ :=
      fun m χ e => by simp [PMap.ins_get, hne m χ e, e]
    have hc₁ : CovR (sem w.Θ) w.K ρ₁ := fun m χ e => hc m χ (hsub m χ e)
    have hag₁ : AgreeOn w.Θ w'.Θ ρ₁ := fun m hm => hE.2 m (by
      cases hm with
      | @top _ _ m₀ e =>
          exact HoldsMut.top (l := m) (m := m₀) (by simp [PMap.ins_get, hne _ _ e, e])
      | @deep _ k _ ψ e h =>
          exact HoldsMut.deep (k := k) (ψ := ψ) (by simp [PMap.ins_get, hne _ _ e, e]) h)
    refine ⟨l, u, PMap.del ρ' l, rfl, by simp [PMap.del_get], PMap.ext fun m => ?_,
      τ.mono n w w' ls ls' u ρ₁ _ ⟨hE.1, hag₁⟩ hr₁ (hk.of_get_sub hsub) hc₁ hP⟩
    rw [PMap.ins_get, PMap.del_get]
    by_cases e : m = l
    · subst e; simp [e']
    · simp [e]

/-! ### `!`, `Unk`, integers, opaque types -/

/-- `𝒱⟦!A⟧`: `A` over the empty resource. -/
def STy.bang (τ : STy) : STy where
  P n w ls v ρ := ρ = PMap.empty ∧ τ.P n w ls v ρ
  down n w ls v ρ h := ⟨h.1, τ.down n w ls v ρ h.2⟩
  mono := by
    rintro n w w' ls ls' v ρ ρ' hE hr hk hc ⟨rfl, h⟩
    exact ⟨RR.of_empty hr, τ.mono n w w' ls ls' v _ ρ' hE hr hk hc h⟩

/-- `𝒱⟦Unk⟧`: `emp`. -/
def STy.unk : STy where
  P _ _ _ _ ρ := ρ = PMap.empty
  down _ _ _ _ _ h := h
  mono := by
    rintro n w w' ls ls' v ρ ρ' - hr - - rfl
    exact RR.of_empty hr

/-- `𝒱⟦I32⟧`, `𝒱⟦I64⟧`, …: a literal of the width, over the empty resource. -/
def STy.int (wd : Width) : STy where
  P _ _ _ v ρ := v.IsInt wd ∧ ρ = PMap.empty
  down _ _ _ _ _ h := h
  mono := by
    rintro n w w' ls ls' v ρ ρ' - hr - - ⟨hv, rfl⟩
    exact ⟨hv, RR.of_empty hr⟩

/-- `𝒱⟦k⟧` at an opaque type (`Opaque.rel` at the tree): the model over the empty resource at a
host type; at `Tok` a location owning a unit cell. -/
def STy.opq (k : Opaque) : STy where
  P _ _ _ v ρ := (k.Host ∧ k.Holds v ∧ ρ = PMap.empty) ∨
    (k = .tok ∧ ∃ l : BoCa.Loc, v = BoCa.Val.loc l ∧ ρ = PMap.sng l (.own BoCa.Val.unit))
  down _ _ _ _ _ h := h
  mono := by
    rintro n w w' ls ls' v ρ ρ' - hr - - (⟨hk, hv, rfl⟩ | ⟨hk, l, rfl, rfl⟩)
    · exact Or.inl ⟨hk, hv, RR.of_empty hr⟩
    · obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
      cases hrc
      exact Or.inr ⟨hk, l, rfl, rfl⟩

/-! ### Families -/

/-- `⊛_{i<c} P(ℓ + i)` over the tree carrier: Core's `sepRange` at the tree. -/
def sepRangeT {K : WCactus} (P : BoCa.Loc → TRes K → Prop) : BoCa.Loc → Nat → TRes K → Prop
  | _, 0, ρ => ρ = PMap.empty
  | l, c + 1, ρ => ∃ ρ₁ ρ₂ : TRes K, ResUT.CompS ρ₁ ρ₂ ρ ∧ P l ρ₁ ∧ sepRangeT P (l + 1) c ρ₂

theorem sepRangeT_imp {K : WCactus} {P Q : BoCa.Loc → TRes K → Prop}
    (h : ∀ l ρ, P l ρ → Q l ρ) : ∀ (c : Nat) (l : BoCa.Loc) (ρ : TRes K),
      sepRangeT P l c ρ → sepRangeT Q l c ρ
  | 0, _, _, h₀ => h₀
  | c + 1, l, _, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ => ⟨ρ₁, ρ₂, hc, h l ρ₁ h₁, sepRangeT_imp h c (l + 1) ρ₂ h₂⟩

/-- `sepRangeT` along the tree, from its members', each read at a list keeping the records its
part reads. -/
theorem sepRangeT_mono {w w' : TWd} {ls : List (SRecT w.K)} {ls' : List (SRecT w'.K)}
    {P : BoCa.Loc → TRes w.K → Prop} {Q : BoCa.Loc → TRes w'.K → Prop}
    (h : ∀ l (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' →
      KeepRel w'.Θ ls ls' ρ → CovR (sem w.Θ) w.K ρ → P l ρ → Q l ρ') :
    ∀ (c : Nat) (l : BoCa.Loc) (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ →
      RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → CovR (sem w.Θ) w.K ρ →
      sepRangeT P l c ρ → sepRangeT Q l c ρ'
  | 0, _, _, _, _, hr, _, _, h₀ => by
      subst h₀; exact RR.of_empty hr
  | c + 1, l, _, ρ', hE, hr, hk, hc, ⟨ρ₁, ρ₂, hcomp, h₁, h₂⟩ => by
      obtain ⟨a', b', ha, hb, hc'⟩ := RR.split_retype hE.1 hcomp hc hE.2 hr
      exact ⟨a', b', hc', h l ρ₁ a' (hE.of_compS_left hcomp) ha (hk.of_compS_left hcomp)
          (hc.of_compS_left hcomp) h₁,
        sepRangeT_mono h c (l + 1) ρ₂ b' (hE.of_compS_right hcomp) hb (hk.of_compS_right hcomp)
          (hc.of_compS_right hcomp) h₂⟩

/-- `𝒱⟦[L]⟧`: `(ℓ, c)` with `c < 2³¹`, each leaf `ℓ + i` for `i < c` a value of `L` over its
own part. -/
def STy.fam (τ : STy) : STy where
  P n w ls v ρ := ∃ (l : BoCa.Loc) (c : UInt32), v = BoCa.Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
    sepRangeT (fun m => τ.P n w ls (BoCa.Val.loc m)) l c.toNat ρ
  down := by
    rintro n w ls v ρ ⟨l, c, rfl, hc, h⟩
    exact ⟨l, c, rfl, hc, sepRangeT_imp (fun m ρ => τ.down n w ls _ ρ) _ l ρ h⟩
  mono := by
    rintro n w w' ls ls' v ρ ρ' hE hr hk hcov ⟨l, c, rfl, hc, h⟩
    exact ⟨l, c, rfl, hc, sepRangeT_mono
      (fun m ρ ρ' hE hr hk hcov => τ.mono n w w' ls ls' (BoCa.Val.loc m) ρ ρ' hE hr hk hcov)
      c.toNat l ρ ρ' hE hr hk hcov h⟩

/-! ### Thunks -/

/-- **`𝒱⟦U C⟧`** for a computation predicate on values, downward closed: `C` at every world
extension carrying the thunk's resource, on its re-reading there, at every list keeping the
re-readings of the records of `ls` the resource reads (`KeepRel`). This is the resume condition of
a stored continuation's share (`contShareT`): a thunk held under a lend is forced only where the
lend's record is kept, and is forced wherever it is, whatever other branches opened or ended. The
forcing is the predicate's (`Core/TreeSemC.lean`'s `STy.thunkC`). Monotone **by definition**,
extensions, re-readings and `KeepRel` composing (`TWd.Ext.trans`, `RRw.trans`, `KeepRel.trans`):
this is not a result about the computation. -/
def STy.thunk (C : Nat → (w : TWd) → List (SRecT w.K) → BoCa.Val → TRes w.K → Prop)
    (hC : ∀ n w ls v ρ, C (n + 1) w ls v ρ → C n w ls v ρ) : STy where
  P n w ls v ρ := ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)), w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → C n w' ls' v ρ'
  down _ _ _ _ _ h w' ρ' ls' hE hr hk := hC _ w' _ _ ρ' (h w' ρ' ls' hE hr hk)
  mono _ _ _ _ _ _ _ _ hE hr hk _ h w'' ρ'' ls'' hE' hr' hk' :=
    h w'' ρ'' ls'' (hE.trans hr hE') (RRw.trans hE'.1 hr hr') (KeepRel.trans hE'.1 hr hk hk')

/-- Forcing a thunk at the world and list it is held at. -/
theorem STy.thunk_force {C : Nat → (w : TWd) → List (SRecT w.K) → BoCa.Val → TRes w.K → Prop}
    {hC : ∀ n w ls v ρ, C (n + 1) w ls v ρ → C n w ls v ρ} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {v : BoCa.Val} {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) (h : (STy.thunk C hC).P n w ls v ρ) :
    C n w ls v ρ :=
  h w ρ ls (TWd.Ext.refl w ρ) (RR.refl hc) (KeepRel.refl hls ρ)

/-! ### `μ` and type variables -/

/-- A body over a candidate, monotone in it. -/
def STy.MonoBody (Φ : STy → STy) : Prop := ∀ σ τ : STy, σ.Le τ → (Φ σ).Le (Φ τ)

/-- **`𝒱⟦μX. A⟧`**, the least fixed point `⋂{X | A[X] ⊆ X}`, over candidates that are value types.
It is downward closed and monotone for every body, because every candidate is. -/
def STy.mu (Φ : STy → STy) : STy where
  P n w ls v ρ := ∀ Y : STy, (Φ Y).Le Y → Y.P n w ls v ρ
  down n w ls v ρ h X hX := X.down n w ls v ρ (h X hX)
  mono n w w' ls ls' v ρ ρ' hE hr hk hc h X hX := X.mono n w w' ls ls' v ρ ρ' hE hr hk hc (h X hX)

theorem STy.mu_least {Φ : STy → STy} {X : STy} (hX : (Φ X).Le X) : (STy.mu Φ).Le X :=
  fun _ _ _ _ _ h => h X hX

/-- **Fold** at a monotone body. -/
theorem STy.mu_fold {Φ : STy → STy} (hΦ : STy.MonoBody Φ) : (Φ (STy.mu Φ)).Le (STy.mu Φ) :=
  fun n w ls v ρ h _ hX => hX n w ls v ρ (hΦ _ _ (STy.mu_least hX) n w ls v ρ h)

/-- **Unfold** at a monotone body. -/
theorem STy.mu_unfold {Φ : STy → STy} (hΦ : STy.MonoBody Φ) : (STy.mu Φ).Le (Φ (STy.mu Φ)) :=
  STy.mu_least (hΦ _ _ (STy.mu_fold hΦ))

/-- A type variable: an environment entry, a value type. -/
def STy.var (η : Nat → STy) (i : Nat) : STy := η i

/-- The environment with `τ` at `0`. -/
def STy.scons (τ : STy) (η : Nat → STy) : Nat → STy
  | 0 => τ
  | i + 1 => η i

theorem STy.sum_le {σ₁ σ₂ τ₁ τ₂ : STy} (h₁ : σ₁.Le τ₁) (h₂ : σ₂.Le τ₂) :
    (STy.sum σ₁ σ₂).Le (STy.sum τ₁ τ₂) := by
  rintro n w ls v ρ (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩)
  · exact Or.inl ⟨v₁, rfl, h₁ n w ls v₁ ρ h⟩
  · exact Or.inr ⟨v₂, rfl, h₂ n w ls v₂ ρ h⟩

theorem STy.tensor_le {σ₁ σ₂ τ₁ τ₂ : STy} (h₁ : σ₁.Le τ₁) (h₂ : σ₂.Le τ₂) :
    (STy.tensor σ₁ σ₂).Le (STy.tensor τ₁ τ₂) := by
  rintro n w ls v ρ ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, a, b⟩
  exact ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, h₁ n w ls v₁ ρ₁ a, h₂ n w ls v₂ ρ₂ b⟩

/-- `List A = μX. 1 + (A ⊗ X)`, the body read at the variable `0`. -/
def STy.list (τ : STy) : STy :=
  STy.mu fun X => STy.sum STy.unit (STy.tensor τ (STy.var (STy.scons X fun _ => STy.zero) 0))

theorem STy.list_body_mono (τ : STy) :
    STy.MonoBody fun X => STy.sum STy.unit (STy.tensor τ (STy.var (STy.scons X fun _ => STy.zero) 0)) :=
  fun _ _ h => STy.sum_le (STy.le_refl _) (STy.tensor_le (STy.le_refl _) h)

/-- The empty list is a value of `List A`, at every index, world and list. -/
theorem STy.list_nil (τ : STy) (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    (STy.list τ).P n w ls (BoCa.Val.inj₁ BoCa.Val.unit) PMap.empty :=
  STy.mu_fold (STy.list_body_mono τ) n w ls _ _ (Or.inl ⟨_, rfl, rfl, rfl⟩)

/-! ### What carries `Mut`: the re-read invariant is the store type -/

/-- **The invariant of a re-read `mut` cell is its location's code read at the new tree.** -/
theorem RC.mut_inv {Θ' : CodeTy} {K K' : WCactus} {l : BoCa.Loc} {m : TMut K} {m' : TMut K'}
    {A : KTy} (hA : Θ' l = some A) (h : RC (sem Θ') l (.mut m) (.mut m')) :
    ∀ u r, m'.P u r ↔ (A.interp Θ').P K' u r.toU := by
  cases h with
  | «mut» _ _ _ τ hΘ _ _ _ _ hP =>
      rw [sem_of hA] at hΘ; cases Option.some.inj hΘ; exact hP

/-- **A lender reads back a value of the store type** from a re-read cell: whatever the re-read
invariant admits is in the location's code at the new tree. -/
theorem RC.mut_readback {Θ' : CodeTy} {K K' : WCactus} {l : BoCa.Loc} {m : TMut K}
    {m' : TMut K'} {A : KTy} (hA : Θ' l = some A) (h : RC (sem Θ') l (.mut m) (.mut m'))
    {u : BoCa.Val} {r : ResT BoCa.Loc BoCa.Val K' m'.ls} (hm : m'.P u r) :
    (A.interp Θ').P K' u r.toU :=
  (RC.mut_inv hA h u r).mp hm

/-- **Rules out a re-read `mut` cell whose invariant changes under re-reading.** A cell whose
invariant is not its location's code read at the new tree, at some value and resource, is not a
re-reading: no `RC` produces it. So a lender never reads back, from a re-read cell, a value
outside the cell's store type. -/
theorem not_rc_of_inv_ne {Θ' : CodeTy} {K K' : WCactus} {l : BoCa.Loc} {m : TMut K}
    {m' : TMut K'} {A : KTy} (hA : Θ' l = some A)
    (hne : ¬ ∀ u r, m'.P u r ↔ (A.interp Θ').P K' u r.toU) :
    ¬ RC (sem Θ') l (.mut m) (.mut m') :=
  fun h => hne (RC.mut_inv hA h)

/-- **The re-read invariant holds wherever the old one held**, on carried resources: a value the
cell stored before the tree grew (at the old code typing) is admitted by the re-read cell, its
resource re-read. The re-reading keeps the location's code (`hl`). -/
theorem RC.mut_extends {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') {l : BoCa.Loc}
    {m : TMut K} {m' : TMut K'} (hc : Cov (sem Θ) K l (.mut m)) (hl : Θ' l = Θ l)
    (h : RC (sem Θ') l (.mut m) (.mut m')) {u : BoCa.Val} {r₀ : ResT BoCa.Loc BoCa.Val K m.ls}
    {r : ResT BoCa.Loc BoCa.Val K' m'.ls} (hr₀ : CovR (sem Θ) K r₀.toU)
    (hrr : RR (sem Θ') r₀.toU r.toU) (hag : AgreeOn Θ Θ' r₀.toU) (hP : m.P u r₀) : m'.P u r := by
  cases hc with
  | «mut» _ _ τ hΘ hPm _ =>
      obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hΘ
      exact (RC.mut_inv (hl.trans hA) h u r).mpr
        (interp_retype A hE u _ _ hr₀ hrr hag ((hPm u r₀).mp hP))

/-- **A `Mut` value is a `Mut` value after the tree grows, with the invariant the store type
there**: `STy.mut`'s monotonicity, and the re-read cell's invariant by `RC.mut_inv`. -/
theorem STy.mut_reread {a : Life} {A : KTy} {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)}
    {v : BoCa.Val} {ρ : TRes w.K} (hE : w.Ext w' ρ) (hc : CovR (sem w.Θ) w.K ρ)
    (h : (STy.mut a A).P n w ls v ρ) :
    ∃ (l : BoCa.Loc) (m' : TMut w'.K), v = BoCa.Val.loc l ∧
      RRw (w := w) (w' := w') ρ (PMap.sng l (.mut m')) ∧ w'.Θ l = some A ∧
      ∀ u r, m'.P u r ↔ (A.interp w'.Θ).P w'.K u r.toU := by
  obtain ⟨ρ', hr, -⟩ := RR.exists_retype hE.1 hc hE.2
  have h' : (STy.mut a A).P n w' [] v ρ' := interp_retype (.mut a A) hE.1 v ρ ρ' hc hr hE.2 h
  obtain ⟨l, m', rfl, rfl, hl, -, hP⟩ := STy.mut_iff.mp h'
  exact ⟨l, m', rfl, hr, hl, hP⟩

end BoCa.Fig16.Tree.Wp

end
