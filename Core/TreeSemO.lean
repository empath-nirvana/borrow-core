import Core.TreeSemK
import Core.TreeLend

/-!
# Value types owning records, at the lifetime tree (E3.0)

Research branch `rq1-tree`; no SPEC entry states this file yet.

`STy` (`Core/TreeSem.lean`) reads the record list `ls` and owns no records (departure E3). This
file adds the owned records `O` as an argument, beside `STy` rather than in it, so every former and
every use of `STy` is unchanged:

* **`STyO`**: a predicate `PO n w ls O v ρ`, downward closed in the index and **Kripke along the
  tree with the owned records re-read** (`TValO.Mono`): at every world extension carrying `ρ`, on
  `ρ`'s re-reading, at every list keeping the records of `ls` that `ρ` reads (`KeepRel`), and at
  the re-reading of **every** record of `O` (`RecsRR`, record by record, none dropped). `ls`'s
  records `ρ` does not read may be gone (another branch ended them); `O`'s may not: they are the
  value's own, and no other branch ends them.
* **Every `STy` is an `STyO` owning nothing** (`STy.toO`, `STy.toO_nil`): at `O = []` it is the
  `STy`, and a re-reading of `[]` is `[]` (`RecsRR.nil_left`).
* **Formers**: `[a]` (`STyO.box`), `⊗` with the records split between the components
  (`STyO.tensor`, `RecsRR.append_left`), and `U` over a computation owning records
  (`STyO.thunk`), each downward closed and Kripke.
* **`STy.kontO τB C`**, a continuation owning `O`: at every later world, list and re-reading `O′`
  of its records, applied to an answer of `τB`, a run of `C` owning `O′`. `C` is an `SCmpO`; the
  relation's instance is `SCmpO.ret`, a bare `cerwpT` run owning `O` at a frame condition read at
  the run's records (`Fo w O`, the shape of `fdAt`). Its closure properties are
  `STy.kontO_down` and `STy.kontO_mono`. At `O = []` and a computation owning nothing it is
  `STy.kont` (`STy.kontO_toO_nil`).
* **Exclusivity, where it is used** (`STyO.reread`): the law is unconditional given a re-reading
  `O′`; such a re-reading exists when the extension keeps the code of every location the records'
  escrows hold a `mut` cell at (`AgreeOn` on each escrow), which is what "no other branch ends or
  re-types `O`'s records" provides. `RecsRR.exists_retype` builds it.
* **E3.1** (`STy.kontO_of_share`, `STy.kontBoxO_of_share`): a continuation captured at a stop
  owning `O` (`contShareT … O …`) is a value of `STy.kontO` owning `O`, at the run
  `SCmpO.ret … (fdAt en v Fb)`.
* **E3.2** (`STy.kontBoxO_resume_after`): boxed, carried along an extension with its share and its
  records re-read, and resumed there, a run owning the re-read records. The re-reading of the
  records is not built from `AgreeOn`: the cactus operations give it for every branch but the
  running one (`EndT`'s `RecsRR w′.Θ psF psF′`, through `cactusT_step` and `cactusT_extend`).
* **E3.3** (`STy.kontO_exit`): the resumed run, owning the records of `imm` lends its branch
  opened (`lendRec`s), ends one of them inside the resumed branch: the lend cell goes back to
  `ℓ ↦ own(())` in the run's resource and the record leaves the run's records (`twp_lendEnd`, which
  is `EndT`'s `MaskDiff` clause at the record's mask), under the resumer's guarantee `fdJoinT`,
  which holds the frame to nothing at the owned records (`fdAt_joinT_noneAt`). `mut` lends open no
  record on the tree (`TWNT.mutFold`/`mutUnfold`), so a continuation's island is its `imm` lends.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont)

/-! ### Owned records re-read -/

/-- A re-reading of no records is no records. -/
theorem RecsRR.nil_left {K K' : WCactus} {Θ' : CodeTy} {O' : List (FrameRecT K')}
    (h : RecsRR (K := K) Θ' [] O') : O' = [] := by
  cases h; rfl

/-- A re-reading of a concatenation splits into the parts' re-readings. -/
theorem RecsRR.append_left {K K' : WCactus} {Θ' : CodeTy} {O₂ : List (FrameRecT K)} :
    ∀ {O₁ : List (FrameRecT K)} {O' : List (FrameRecT K')}, RecsRR Θ' (O₁ ++ O₂) O' →
      ∃ O₁' O₂', O' = O₁' ++ O₂' ∧ RecsRR Θ' O₁ O₁' ∧ RecsRR Θ' O₂ O₂'
  | [], O', h => ⟨[], O', rfl, List.Forall₂.nil, h⟩
  | r :: O₁, O', h => by
      rw [List.cons_append] at h
      cases h with
      | cons hr t =>
          obtain ⟨O₁', O₂', rfl, h₁, h₂⟩ := RecsRR.append_left t
          exact ⟨_ :: O₁', O₂', rfl, List.Forall₂.cons hr h₁, h₂⟩

/-! ### Value types owning records -/

/-- A value predicate at the step index, the tree world, the record list and the owned records. -/
abbrev TValO : Type :=
  Nat → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → BoCa.Val → TRes w.K → Prop

/-- Downward closed in the step index. -/
def TValO.Down (P : TValO) : Prop := ∀ n w ls O v ρ, P (n + 1) w ls O v ρ → P n w ls O v ρ

/-- **Kripke along the tree, the owned records re-read**: at every world extension carrying `ρ`,
on the re-reading of a covered `ρ` there, at every list keeping the records of `ls` that `ρ`
reads (`KeepRel`), at the re-reading of every owned record (`RecsRR`). -/
def TValO.Mono (P : TValO) : Prop :=
  ∀ n (w w' : TWd) (ls : List (SRecT w.K)) (ls' : List (SRecT w'.K)) (O : List (FrameRecT w.K))
    (O' : List (FrameRecT w'.K)) v (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    CovR (sem w.Θ) w.K ρ → P n w ls O v ρ → P n w' ls' O' v ρ'

/-- **A value type owning records**: downward closed and Kripke with the owned records re-read. -/
structure STyO where
  PO : TValO
  down : PO.Down
  mono : PO.Mono

theorem STyO.down_le (τ : STyO) {m n : Nat} (h : m ≤ n) :
    ∀ w ls O v ρ, τ.PO n w ls O v ρ → τ.PO m w ls O v ρ := by
  induction h with
  | refl => exact fun _ _ _ _ _ x => x
  | step _ ih => exact fun w ls O v ρ x => ih w ls O v ρ (τ.down _ w ls O v ρ x)

/-- Inclusion. -/
def STyO.Le (σ τ : STyO) : Prop := ∀ n w ls O v ρ, σ.PO n w ls O v ρ → τ.PO n w ls O v ρ

/-- **A value type owning nothing.** -/
def STy.toO (τ : STy) : STyO where
  PO n w ls O v ρ := O = [] ∧ τ.P n w ls v ρ
  down n w ls _ v ρ h := ⟨h.1, τ.down n w ls v ρ h.2⟩
  mono n w w' ls ls' O O' v ρ ρ' hE hr hk hO hc h := by
    obtain ⟨rfl, h⟩ := h
    exact ⟨RecsRR.nil_left hO, τ.mono n w w' ls ls' v ρ ρ' hE hr hk hc h⟩

/-- At no owned records, `τ.toO` is `τ`. -/
theorem STy.toO_nil (τ : STy) {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {v : BoCa.Val}
    {ρ : TRes w.K} : τ.toO.PO n w ls [] v ρ ↔ τ.P n w ls v ρ :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

/-- `𝒱⟦[a] A⟧` owning records: `A`, every borrow cell strictly longer-lived than `a`. -/
def STyO.box (a : Life) (τ : STyO) : STyO where
  PO n w ls O v ρ := τ.PO n w ls O v ρ ∧ ρ.InStratum (TSet.single a)
  down n w ls O v ρ h := ⟨τ.down n w ls O v ρ h.1, h.2⟩
  mono n w w' ls ls' O O' v ρ ρ' hE hr hk hO hc h :=
    ⟨τ.mono n w w' ls ls' O O' v ρ ρ' hE hr hk hO hc h.1, hr.inStratum hE.1 h.2⟩

/-- `𝒱⟦A ⊗ B⟧` owning records: the components over the parts of a composite, each owning its part
of the records. -/
def STyO.tensor (τ₁ τ₂ : STyO) : STyO where
  PO n w ls O v ρ := ∃ (v₁ v₂ : BoCa.Val) (ρ₁ ρ₂ : TRes w.K) (O₁ O₂ : List (FrameRecT w.K)),
    v = BoCa.Val.pair v₁ v₂ ∧ ResUT.CompS ρ₁ ρ₂ ρ ∧ O = O₁ ++ O₂ ∧
      τ₁.PO n w ls O₁ v₁ ρ₁ ∧ τ₂.PO n w ls O₂ v₂ ρ₂
  down := by
    rintro n w ls O v ρ ⟨v₁, v₂, ρ₁, ρ₂, O₁, O₂, rfl, hc, rfl, h₁, h₂⟩
    exact ⟨v₁, v₂, ρ₁, ρ₂, O₁, O₂, rfl, hc, rfl, τ₁.down n w ls O₁ v₁ ρ₁ h₁,
      τ₂.down n w ls O₂ v₂ ρ₂ h₂⟩
  mono := by
    rintro n w w' ls ls' O O' v ρ ρ' hE hr hk hO hc
      ⟨v₁, v₂, ρ₁, ρ₂, O₁, O₂, rfl, hcomp, rfl, h₁, h₂⟩
    obtain ⟨O₁', O₂', rfl, hO₁, hO₂⟩ := RecsRR.append_left hO
    obtain ⟨a', b', ha, hb, hc'⟩ := RR.split_retype hE.1 hcomp hc hE.2 hr
    exact ⟨v₁, v₂, a', b', O₁', O₂', rfl, hc', rfl,
      τ₁.mono n w w' ls ls' O₁ O₁' v₁ ρ₁ a' (hE.of_compS_left hcomp) ha (hk.of_compS_left hcomp)
        hO₁ (hc.of_compS_left hcomp) h₁,
      τ₂.mono n w w' ls ls' O₂ O₂' v₂ ρ₂ b' (hE.of_compS_right hcomp) hb
        (hk.of_compS_right hcomp) hO₂ (hc.of_compS_right hcomp) h₂⟩

/-- **`𝒱⟦U C⟧` owning records**: `C` at every world extension carrying the resource, on its
re-reading, at every list keeping the records the resource reads, at every re-reading of the owned
records. Kripke by definition: extensions, re-readings, `KeepRel` and `RecsRR` compose. -/
def STyO.thunk (C : TValO) (hC : C.Down) : STyO where
  PO n w ls O v ρ := ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K))
    (O' : List (FrameRecT w'.K)), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' →
      KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' → C n w' ls' O' v ρ'
  down _ _ _ _ _ _ h w' ρ' ls' O' hE hr hk hO := hC _ w' ls' O' _ ρ' (h w' ρ' ls' O' hE hr hk hO)
  mono _ _ _ _ _ _ _ _ _ _ hE hr hk hO _ h w'' ρ'' ls'' O'' hE' hr' hk' hO' :=
    h w'' ρ'' ls'' O'' (hE.trans hr hE') (RRw.trans hE'.1 hr hr') (KeepRel.trans hE'.1 hr hk hk')
      (RecsRR.trans hE'.1 hO hO')

/-- **A value stored owning records meets its type after an extension that keeps them.** At every
world extension carrying a covered resource and keeping the code of every `mut` location of the
owned records' escrows (no other branch re-types them), the resource and the records have
re-readings, and the value is of `τ` over them at every list keeping the records the resource
reads. -/
theorem STyO.reread (τ : STyO) {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {v : BoCa.Val} {ρ : TRes w.K} (hE : w.Ext w' ρ)
    (hc : CovR (sem w.Θ) w.K ρ) (hcO : ∀ r ∈ O, CovR (sem w.Θ) w.K r.R)
    (hagO : ∀ r ∈ O, AgreeOn w.Θ w'.Θ r.R) (h : τ.PO n w ls O v ρ) :
    ∃ (ρ' : TRes w'.K) (O' : List (FrameRecT w'.K)), RRw (w := w) (w' := w') ρ ρ' ∧
      CovR (sem w'.Θ) w'.K ρ' ∧ RecsRR w'.Θ O O' ∧
      ∀ ls' : List (SRecT w'.K), KeepRel w'.Θ ls ls' ρ → τ.PO n w' ls' O' v ρ' := by
  obtain ⟨ρ', hr, hc'⟩ := RR.exists_retype hE.1 hc hE.2
  obtain ⟨O', hO⟩ := RecsRR.exists_retype hE.1 hcO hagO
  exact ⟨ρ', O', hr, hc', hO, fun ls' hk => τ.mono n w w' ls ls' O O' v ρ ρ' hE hr hk hO hc h⟩

/-! ### Computation types owning records -/

/-- A predicate on terms at the index, the world, the list and the owned records. -/
abbrev CSemO : Type :=
  Nat → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → Expr → TRes w.K → Prop

/-- **A computation type owning records**: downward closed in the index. -/
structure SCmpO where
  P : CSemO
  down : ∀ n w ls O e ρ, P (n + 1) w ls O e ρ → P n w ls O e ρ

/-- A computation type owning nothing. -/
def SCmp.toO (C : SCmp) : SCmpO where
  P n w ls O e ρ := O = [] ∧ C.P n w ls e ρ
  down n w ls _ e ρ h := ⟨h.1, C.down n w ls e ρ h.2⟩

/-- **A run owning `O`**: `cerwpT` at the table `Tb`, the postcondition `Q`, the base `Fb`, and
the present frame condition read at the run's owned records (`Fo w O`, as `fdAt en v Fb O` is at
a resume). -/
def SCmpO.ret (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (Q : TPostV) (hQ : Q.Down)
    (Fb : TFrame) (Fo : (w : TWd) → List (FrameRecT w.K) → TFrame) : SCmpO where
  P n w ls O e ρ := cerwpT (ℍ := ℍ) Tb Q Fb (Fo w O) n w ls O e ρ
  down _ _ _ _ _ _ h := cerwpT_le hL hTb hQ (Nat.le_succ _) h

/-- **`𝒞⟦A ⊸ C⟧` owning records**: applied to an answer of `A` (owning none) over a resource
composed with the function's, a run of `C` owning the function's records. -/
def SCmpO.arr (τ : STy) (C : SCmpO) : SCmpO where
  P n w ls O e ρ := ∀ k, k ≤ n → ∀ (v : Val) (ρa ρ' : TRes w.K), ResUT.CompS ρ ρa ρ' →
    τ.P k w ls v ρa → C.P k w ls O (.app e (.val v)) ρ'
  down _ _ _ _ _ _ h k hk := h k (Nat.le_succ_of_le hk)

/-! ### A continuation owning records -/

/-- **`𝒱⟦U (B ⊸ C)⟧` owning `O`**: applied to an answer of `B` at every later world, list and
re-reading `O′` of its records, a run of `C` owning `O′`. -/
def STy.kontO (τB : STy) (C : SCmpO) : STyO :=
  STyO.thunk (fun n w ls O κ ρ => (SCmpO.arr τB C).P n w ls O (Expr.val κ) ρ)
    (fun n w ls O κ ρ h => (SCmpO.arr τB C).down n w ls O (Expr.val κ) ρ h)

/-- **E3.0, downward closure** of the continuation owning records. -/
theorem STy.kontO_down {τB : STy} {C : SCmpO} {m n : Nat} (hmn : m ≤ n) {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {κ : Val} {ρ : TRes w.K}
    (h : (STy.kontO τB C).PO n w ls O κ ρ) : (STy.kontO τB C).PO m w ls O κ ρ :=
  (STy.kontO τB C).down_le hmn w ls O κ ρ h

/-- **E3.0, Kripke with the owned records kept**: a continuation owning `O` at `w`, `ls` is one
owning `O′` at every extension `w′` carrying its share, on the share's re-reading, at every list
keeping the records of `ls` the share reads, `O′` the re-reading of every record of `O`. -/
theorem STy.kontO_mono {τB : STy} {C : SCmpO} {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {O : List (FrameRecT w.K)} {O' : List (FrameRecT w'.K)} {κ : Val}
    {ρ : TRes w.K} {ρ' : TRes w'.K} (hE : w.Ext w' ρ) (hr : RRw (w := w) (w' := w') ρ ρ')
    (hk : KeepRel w'.Θ ls ls' ρ) (hO : RecsRR w'.Θ O O') (hc : CovR (sem w.Θ) w.K ρ)
    (h : (STy.kontO τB C).PO n w ls O κ ρ) : (STy.kontO τB C).PO n w' ls' O' κ ρ' :=
  (STy.kontO τB C).mono n w w' ls ls' O O' κ ρ ρ' hE hr hk hO hc h

/-- **Resumed at its type**: a continuation owning `O` is applied, at every later world, list
keeping the records it reads and re-reading `O′` of its records, to an answer of `B`, a run of `C`
owning `O′`. -/
theorem STy.kontO_resume {τB : STy} {C : SCmpO} {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {O : List (FrameRecT w.K)} {O' : List (FrameRecT w'.K)} {κ : Val}
    {ρ : TRes w.K} {ρ' : TRes w'.K} (h : (STy.kontO τB C).PO n w ls O κ ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hk : KeepRel w'.Θ ls ls' ρ) (hO : RecsRR w'.Θ O O')
    {j : Nat} (hj : j ≤ n) {a : Val} {ρa σ : TRes w'.K} (hc : ResUT.CompS ρ' ρa σ)
    (ha : τB.P j w' ls' a ρa) : C.P j w' ls' O' (.app (.val κ) (.val a)) σ :=
  h w' ρ' ls' O' hE hr hk hO j hj a ρa σ hc ha

/-- **At no records, the continuation owning records is `STy.kont`.** -/
theorem STy.kontO_toO_nil {τB : STy} {C : SCmp} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {κ : Val} {ρ : TRes w.K} :
    (STy.kontO τB C.toO).PO n w ls [] κ ρ ↔ (STy.kont τB C).P n w ls κ ρ := by
  constructor
  · intro h w' ρ' ls' hE hr hk j hj a ρa σ hc ha
    exact (h w' ρ' ls' [] hE hr hk List.Forall₂.nil j hj a ρa σ hc ha).2
  · intro h w' ρ' ls' O' hE hr hk hO j hj a ρa σ hc ha
    exact ⟨RecsRR.nil_left hO, h w' ρ' ls' hE hr hk j hj a ρa σ hc ha⟩

/-- **A continuation owning records, boxed at `d`**: `[@d] U (B ⊸ C)`. -/
def STy.kontBoxO (d : Life) (τB : STy) (C : SCmpO) : STyO := STyO.box d (STy.kontO τB C)

/-! ### E3.1: a captured continuation owning records is a value of its type -/

/-- **The resume of a captured continuation owning `O` is a run owning the re-read records**, at
every extension of the stop's world, on the share's re-reading, at every list keeping the records
the share reads, at every re-reading `O′` of `O`, below the stop's index: the share's resume
(`contShareT_resume` at general `O`) and one step of `κ`'s application. -/
theorem kontO_run_of_share {Tb : TableT} (hL : Tb.Local) {Q : TPostV} {τB : STy} {en : OpEntT}
    {Fb : TFrame} {k : Nat} {w w' : TWd} {ls : List (SRecT w.K)} {ls' : List (SRecT w'.K)}
    {O : List (FrameRecT w.K)} {O' : List (FrameRecT w'.K)} {K : Kont} {v κ : Val}
    {ρ : TRes w.K} {ρ' : TRes w'.K}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ (K.plug (.val a)))
    (hB : ∀ j (w' : TWd) ls' a σ, τB.P j w' ls' a σ → en.PBv v j w' ls' a σ)
    {T : OpTabT} {Ψc : ContP}
    (h : contShareT T en Fb k w ls O K v (cerwpTC (ℍ := ℍ) Tb Q Fb k) Ψc ρ)
    (hE : w.Ext w' ρ) (hr : RRw (w := w) (w' := w') ρ ρ') (hk : KeepRel w'.Θ ls ls' ρ)
    (hO : RecsRR w'.Θ O O') {j : Nat} (hj : j < k) {a : Val} {ρa σ : TRes w'.K}
    (hc : ResUT.CompS ρ' ρa σ) (ha : τB.P j w' ls' a ρa) :
    cerwpT (ℍ := ℍ) Tb Q Fb (fdAt en v Fb O') j w' ls' O' (.app (.val κ) (.val a)) σ := by
  cases j with
  | zero => exact cerwpT_zero
  | succ j =>
      refine cerwpT_step hL (hκ a) ?_
      have hres := contShareT_resume h hE hr hk hO (k' := j) (by omega)
        (hB j w' ls' a ρa (τB.down j w' ls' a ρa ha)) hc
      simp only [cerwpTC, show j < k by omega, if_true] at hres
      exact hres

/-- **E3.1: a continuation captured owning `O` is a value of `U (B ⊸ C)` owning `O`.** The share
`ρ` of a stop at `w`, `ls`, owning the records `O` (the lends its own branch opened), owing the
relation at `Tb`, `Q`, `Fb`: `κ` is a value of `STy.kontO τB (SCmpO.ret … (fdAt en v Fb))` at `w`,
`ls`, `O`, `ρ` at every index below the stop's. -/
theorem STy.kontO_of_share {Tb : TableT} (hL : Tb.Local) (hTb : Tb.Down) {Q : TPostV}
    (hQ : Q.Down) {τB : STy} {en : OpEntT} {Fb : TFrame} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {K : Kont} {v κ : Val} {ρ : TRes w.K}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ (K.plug (.val a)))
    (hB : ∀ j (w' : TWd) ls' a σ, τB.P j w' ls' a σ → en.PBv v j w' ls' a σ)
    {T : OpTabT} {Ψc : ContP}
    (h : contShareT T en Fb k w ls O K v (cerwpTC (ℍ := ℍ) Tb Q Fb k) Ψc ρ) {n : Nat}
    (hn : n < k) :
    (STy.kontO τB (SCmpO.ret (ℍ := ℍ) Tb hL hTb Q hQ Fb
      (fun w' O' => fdAt en v Fb (w' := w') O'))).PO n w ls O κ ρ := by
  intro w' ρ' ls' O' hE hr hk hO j hj a ρa σ hc ha
  exact kontO_run_of_share hL hκ hB h hE hr hk hO (by omega) hc ha

/-- **Boxed at a lifetime its share outlives**: `[@d] U (B ⊸ C)` owning `O`. -/
theorem STy.kontBoxO_of_share {Tb : TableT} (hL : Tb.Local) (hTb : Tb.Down) {Q : TPostV}
    (hQ : Q.Down) {τB : STy} {en : OpEntT} {Fb : TFrame} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {K : Kont} {v κ : Val} {ρ : TRes w.K}
    {d : Life}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ (K.plug (.val a)))
    (hB : ∀ j (w' : TWd) ls' a σ, τB.P j w' ls' a σ → en.PBv v j w' ls' a σ)
    {T : OpTabT} {Ψc : ContP}
    (h : contShareT T en Fb k w ls O K v (cerwpTC (ℍ := ℍ) Tb Q Fb k) Ψc ρ)
    (hd : ρ.InStratum (TSet.single d)) {n : Nat} (hn : n < k) :
    (STy.kontBoxO d τB (SCmpO.ret (ℍ := ℍ) Tb hL hTb Q hQ Fb
      (fun w' O' => fdAt en v Fb (w' := w') O'))).PO n w ls O κ ρ :=
  ⟨STy.kontO_of_share hL hTb hQ hκ hB h hn, hd⟩

/-! ### E3.2: carried with its records and resumed -/

/-- **E3.2: a boxed continuation owning records, carried and resumed.** A `κ` captured owning `O`
(its share `ρ`, at the stop list `ls`), boxed at `d`, is carried to any extension `w′` of the stop's
world on the share's re-reading, at any list `ls′` keeping the records of `ls` the share reads,
**with its records re-read (`O′`)**. Other branches may have opened and ended records of their own.
There it is a value of its type owning `O′`, and resuming it at any answer of `B` is a run owning
`O′`.

The carrying premises (`hE`, `hr`, `hO`) are what the cactus operations give every branch other
than the running one (`cactusT_step`, `cactusT_extend`: `w.Ext w′ ρ`, `RRw ρ ρ′`, `RecsRR O O′`,
from `EndT`'s `RecsRR w′.Θ psF psF′` on the frame's records). Forcing at the reflexive extension
needs the list's and the records' escrows covered, which a start provides (`RecInv.cov_ls`,
`RecInv.cov_ps`). -/
theorem STy.kontBoxO_resume_after {Tb : TableT} (hL : Tb.Local) (hTb : Tb.Down) {Q : TPostV}
    (hQ : Q.Down) {τB : STy} {en : OpEntT} {Fb : TFrame} {k : Nat} {w w' : TWd}
    {ls : List (SRecT w.K)} {ls' : List (SRecT w'.K)} {O : List (FrameRecT w.K)}
    {O' : List (FrameRecT w'.K)} {K : Kont} {v κ : Val} {ρ : TRes w.K} {ρ' : TRes w'.K}
    {d : Life}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ (K.plug (.val a)))
    (hB : ∀ j (w' : TWd) ls' a σ, τB.P j w' ls' a σ → en.PBv v j w' ls' a σ)
    {T : OpTabT} {Ψc : ContP}
    (h : contShareT T en Fb k w ls O K v (cerwpTC (ℍ := ℍ) Tb Q Fb k) Ψc ρ)
    (hd : ρ.InStratum (TSet.single d)) (hc : CovR (sem w.Θ) w.K ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hk : KeepRel w'.Θ ls ls' ρ) (hO : RecsRR w'.Θ O O')
    (hls : ∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) (hcO : ∀ r ∈ O', CovR (sem w'.Θ) w'.K r.R)
    {n : Nat} (hn : n < k) :
    (STy.kontBoxO d τB (SCmpO.ret (ℍ := ℍ) Tb hL hTb Q hQ Fb
      (fun w' O' => fdAt en v Fb (w' := w') O'))).PO n w' ls' O' κ ρ' ∧
      ∀ (a : Val) (ρa σ : TRes w'.K), ResUT.CompS ρ' ρa σ → τB.P n w' ls' a ρa →
        cerwpT (ℍ := ℍ) Tb Q Fb (fdAt en v Fb O') n w' ls' O' (.app (.val κ) (.val a)) σ := by
  have hb := STy.kontBoxO_of_share hL hTb hQ hκ hB h hd hn
  have hb' := (STy.kontBoxO d τB _).mono n w w' ls ls' O O' κ ρ ρ' hE hr hk hO hc hb
  exact ⟨hb', fun a ρa σ hcσ ha => STy.kontO_resume hb'.1 (TWd.Ext.refl w' ρ')
    (RR.refl hr.cov) (KeepRel.refl hls ρ') (RecsRR.refl hcO) le_rfl hcσ ha⟩

/-! ### E3.3: the exit returns the records -/

/-- Lend records re-read to themselves at every tree. -/
theorem lendRecs_rr {K K' : WCactus} {Θ' : CodeTy} :
    ∀ Ls : List BoCa.Loc, RecsRR Θ' (Ls.map (lendRec (K := K))) (Ls.map (lendRec (K := K')))
  | [] => List.Forall₂.nil
  | l :: Ls => List.Forall₂.cons (lendRec_rr l) (lendRecs_rr Ls)

/-- **The resumer's guarantee `fdJoinT` at a run owning lend records holds nothing at their
cells**, at every world the frame is read at: the records re-read to themselves. -/
theorem fdAt_joinT_noneAt {en : OpEntT} (hfd : en.fd = fdJoinT) {v : Val} {Fb : TFrame}
    {w' : TWd} {Ls : List BoCa.Loc} {l : BoCa.Loc} (hl : l ∈ Ls) :
    ∀ w ρf, fdAt en v Fb (Ls.map (lendRec (K := w'.K))) w ρf → NoneAt (· = l) ρf := by
  intro w ρf h
  have h2 := h.2 (Ls.map (lendRec (K := w.K))) (lendRecs_rr Ls)
  rw [hfd] at h2
  exact h2.2.mono fun x hx => by
    subst hx
    exact ⟨lendRec x, List.mem_map.mpr ⟨x, hl, rfl⟩, Or.inl rfl⟩

/-- **Ending a lend inside a `cerwpT` run**: `twp_lendEnd` at the run's unfolding. The record
leaves the run's records and the list; the frame must hold nothing at the cell. -/
theorem cerwpT_lendEnd {Tb : TableT} {Q : TPostV} {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls ls₁ : List (SRecT w.K)} {O O₁ : List (FrameRecT w.K)} {e : Expr} {Z ρ ρ₁ : TRes w.K}
    {l : BoCa.Loc} {α : Life}
    (hρ : ResUT.CompS Z (viewRes α l) ρ)
    (hρ₁ : ResUT.CompS Z (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₁)
    (hvZ : ResUT.Valid Z) (hZ : NoneAt (· = l) Z)
    (hF : ∀ w' ρf, F w' ρf → NoneAt (· = l) ρf)
    (hO : ∀ x, x ∈ O ↔ x = lendRec l ∨ x ∈ O₁) (hO₁ : lendRec l ∉ O₁)
    (hls : ∀ x ∈ ls, x.1 = lendRec l ∨ x ∈ ls₁) (hls₁in : ∀ x ∈ ls₁, x ∈ ls)
    (hls₁ : ∀ x ∈ ls₁, x.1 ≠ lendRec l)
    (h : cerwpT (ℍ := ℍ) Tb Q Fb F n w ls₁ O₁ e ρ₁) :
    cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ := by
  rw [cerwpT_eq] at h ⊢
  exact twp_lendEnd hρ hρ₁ hvZ hZ hF hO hO₁ hls hls₁in hls₁ h

/-- **E3.3: the exit.** A resumed continuation's run, owning the records `Ls.map lendRec` of the
`imm` lends its branch opened, at the frame its resumer guarantees (`fdAt en v Fb`, `en.fd =
fdJoinT`), ends the lend of `ℓ ∈ Ls` inside the resumed branch: from the lend cell beside `Z` to
`ℓ ↦ own(())` beside `Z`, the run owning `O₁` (the records without `ℓ`'s) and the list without its
entries. -/
theorem STy.kontO_exit {Tb : TableT} {Q : TPostV} {en : OpEntT} (hfd : en.fd = fdJoinT)
    {v : Val} {Fb : TFrame} {n : Nat} {w : TWd} {ls ls₁ : List (SRecT w.K)}
    {Ls : List BoCa.Loc} {O₁ : List (FrameRecT w.K)} {e : Expr} {Z ρ ρ₁ : TRes w.K}
    {l : BoCa.Loc} {α : Life} (hl : l ∈ Ls)
    (hρ : ResUT.CompS Z (viewRes α l) ρ)
    (hρ₁ : ResUT.CompS Z (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₁)
    (hvZ : ResUT.Valid Z) (hZ : NoneAt (· = l) Z)
    (hO : ∀ x, x ∈ Ls.map (lendRec (K := w.K)) ↔ x = lendRec l ∨ x ∈ O₁) (hO₁ : lendRec l ∉ O₁)
    (hls : ∀ x ∈ ls, x.1 = lendRec l ∨ x ∈ ls₁) (hls₁in : ∀ x ∈ ls₁, x ∈ ls)
    (hls₁ : ∀ x ∈ ls₁, x.1 ≠ lendRec l)
    (h : cerwpT (ℍ := ℍ) Tb Q Fb (fdAt en v Fb (Ls.map (lendRec (K := w.K)))) n w ls₁ O₁ e ρ₁) :
    cerwpT (ℍ := ℍ) Tb Q Fb (fdAt en v Fb (Ls.map (lendRec (K := w.K)))) n w ls
      (Ls.map lendRec) e ρ :=
  cerwpT_lendEnd hρ hρ₁ hvZ hZ (fdAt_joinT_noneAt hfd hl) hO hO₁ hls hls₁in hls₁ h

end BoCa.Fig16.Tree.Wp

end
