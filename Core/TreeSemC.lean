import Core.TreeSem
import Support.Model.Tree.World.TInvHolds

/-!
# The relation's computation types at the lifetime tree  `[spec §62]`

The computation types of the step-indexed relation over the tree world, read at `cerwpT`
(`Core/TreeWpEff.lean`, whose carrier is `twp`). A computation type is `SCmp`: a predicate on terms
at the index, the world and the record list, downward closed. As in Core (`Core/Relation.lean`:
"the Kripke quantifier over `Ext` sits at `U` only"), a computation type reaches a value only under
`U`, and `U`'s quantifier over world extensions and lists keeping the records the thunk reads makes
the thunk monotone (`STy.thunk`).

* **Downward closure of the relation** (`cerwpT_le`): at a table that reads what is owed only
  below its index (`TableT.Local`) and is itself downward closed (`TableT.Down`), and a
  downward-closed postcondition. The operation tables (`opTableT`) are, when their entries are
  (`opTableT_down`).
* **A run at the empty list says nothing of a borrow** (`cerwpT_nil_of_imm`): no world with an
  empty list holds an `imm` cell, so every term over a resource holding a view is a run there.
  This is why `SCmp.ret` runs at the list it is read at (E3, #794).
* **The formers**: `F A` at `cerwpT` at the list (`SCmp.ret`), `A ⊸ C` (`SCmp.arr`), `C & D`
  (`SCmp.amp`), `⊤` (`SCmp.top`), `∀α ⊏ c. C` over the lifetimes below `c` in the current tree
  (`SCmp.all`), and `νX. C`, the greatest fixed point over candidates (`SCmp.nu`, fold and unfold
  at a monotone body).
* **Thunks read at the relation** (`STy.thunkC`, `STy.thunkRet`): a value type for every
  computation type, downward closed and monotone. Monotone by definition (`STy.thunk`). A thunk is
  a run at every later list keeping the records it reads: from a run at the current world when `C`
  is Kripke along `KeepRel` (`STy.thunk_intro`), from a value (`STy.thunkC_val`), from a stored
  continuation's share (`Core/TreeSemK.lean`). `F A` is Kripke along the re-reading of its list
  (`SCmp.ret_kripke`), not along `KeepRel`.

Continuation and task types are `Core/TreeSemK.lean`.

**Departures** (`docs/new-core/scope-782.md` §2): E3, owned records: `SCmp.ret` runs owning no
records (a continuation owning the records of lends its own branch opened is row 6's); E4,
`SCmp.arr` reads its argument at every index up to `n`, which downward closure at a step index
needs (Core's `cC` has no index).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-! ### Downward closure of `cerwpT` -/

/-- A postcondition over values, downward closed in its index. -/
def TPostV.Down (Q : TPostV) : Prop := ∀ n w ls O v ρ, Q (n + 1) w ls O v ρ → Q n w ls O v ρ

/-- A table downward closed in the index it stops at. -/
def TableT.Down (Tb : TableT) : Prop :=
  ∀ F k w ls O t (Ψ : ContT) ρ, Tb F (k + 1) w ls O t Ψ ρ → Tb F k w ls O t Ψ ρ

theorem cerwpPostT_down {Tb : TableT} {Q : TPostV} (hQ : Q.Down) (hTb : Tb.Down) {Ψ : ContT}
    {F : TFrame} : (cerwpPostT Tb Q Ψ F).Down := by
  rintro n w ls O t ρ (⟨v, rfl, h⟩ | h)
  · exact Or.inl ⟨v, rfl, hQ _ _ _ _ _ _ h⟩
  · exact Or.inr (hTb _ _ _ _ _ _ _ _ h)

/-- **`cerwpT` is downward closed.** What is owed below the index is read only below it
(`TableT.Local`), so the continuation relation at the larger index serves. -/
theorem cerwpT_le {Tb : TableT} (hL : Tb.Local) (hTb : Tb.Down) {Q : TPostV} (hQ : Q.Down)
    {F : TFrame} {m n : Nat} (hmn : m ≤ n) {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : cerwpT (ℍ := ℍ) Tb Q F n w ls O e ρ) : cerwpT (ℍ := ℍ) Tb Q F m w ls O e ρ := by
  rw [cerwpT_eq] at h
  exact cerwpT_fold_at hL hmn (twp_le (cerwpPostT_down hQ hTb) hmn h)

/-- An operation's entry downward closed: its payload and its cancel obligation. -/
def OpEntT.Down (en : OpEntT) : Prop :=
  (∀ n w ls v ρ, en.PA (n + 1) w ls v ρ → en.PA n w ls v ρ) ∧
    ∀ P, en.fin = some P → ∀ n w ls e ρ, P (n + 1) w ls e ρ → P n w ls e ρ

/-- **The operation tables are downward closed** when their entries are. -/
theorem opTableT_down {T : OpTabT} (hT : ∀ n i en, T n i = some en → en.Down) :
    (opTableT T).Down := by
  intro F k w ls O t Ψ ρ h
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu, hcont⟩ := h
  have hd := hT n i en h₃
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hd.1 _ _ _ _ _ hA, hu,
    fun w' ρ' ls' O' hE hr hx hO =>
    ⟨fun k' hk a σ σ' hB hcσ =>
      (hcont w' ρ' ls' O' hE hr hx hO).1 k' (by omega) a σ σ' hB hcσ,
      fun hq P hP => hd.2 P hP _ _ _ _ _ ((hcont w' ρ' ls' O' hE hr hx hO).2 hq P hP)⟩⟩

/-! ### A run at the empty list says nothing of a borrow -/

/-- **A run at the empty list, owning no records, holds of every term over a resource holding a
view.** No world whose list is empty holds an `imm` cell: the list's records are the world's
lineage (`TIT`), and every `imm` cell of the world's agreement is a record's cell or a chain
position of one (`CoverageT`). So `twp` at `[]` quantifies over no start, and holds vacuously.

This is why the value types read the list (E3, #794): a thunk type that does not read the list
runs its thunk at a list fixed in advance, `[]` the only one every world has, and then holds of
every thunk holding a borrow, stuck or not. -/
theorem cerwpT_nil_of_imm {Tb : TableT} {Q : TPostV} {F : TFrame} {n : Nat} {w : TWd}
    {e : Expr} {ρ : TRes w.K} {l : BoCa.Loc} {ψ : TCell w.K} (hl : ρ.get l = some ψ)
    (hk : ψ.kind = Kind.imm) : cerwpT (ℍ := ℍ) Tb Q F n w [] [] e ρ := by
  rw [cerwpT_eq]
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hls hO hF hf hc hS hR hI hfd
  exfalso
  cases hls
  obtain ⟨ψ₀, e₀, hrc⟩ := hr.get_some hl
  have hk₀ : ψ₀.kind = Kind.imm := by
    cases hrc <;> first | rfl | (simp [CellUT.kind] at hk)
  obtain ⟨ζ, eζ, kζ, -, -⟩ := compS_get_left' (ResUT.CompS.comm hc) e₀
  obtain ⟨σ, ex, ag, -, hag, -⟩ := hI.valid
  obtain ⟨χ, eχ, kχ, -, -⟩ := AgWT.get_imm hag eζ (kζ.trans hk₀)
  rcases hR.1.inv.2.2.2.2.2.2.2 ag hag l χ eχ kχ with ⟨r, hr, -⟩ | ⟨r, hr, -⟩ <;> cases hr

/-! ### Computation types -/

/-- A predicate on terms at the step index, the tree world and the record list. -/
abbrev CSem : Type := Nat → (w : TWd) → List (SRecT w.K) → Expr → TRes w.K → Prop

/-- Downward closed in the step index. -/
def CSem.Down (C : CSem) : Prop := ∀ n w ls e ρ, C (n + 1) w ls e ρ → C n w ls e ρ

/-- Monotone along world extension, on the re-reading, at every list keeping the records the
resource reads. -/
def CSem.Kripke (C : CSem) : Prop :=
  ∀ n (w w' : TWd) (ls : List (SRecT w.K)) (ls' : List (SRecT w'.K)) e (ρ : TRes w.K)
    (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ →
    C n w ls e ρ → C n w' ls' e ρ'

/-- **A computation type of the relation at the tree**: downward closed in the index. -/
structure SCmp where
  P : CSem
  down : P.Down

/-- Inclusion of computation types. -/
def SCmp.Le (C D : SCmp) : Prop := ∀ n w ls e ρ, C.P n w ls e ρ → D.P n w ls e ρ

/-- The postcondition of `F A`: the value in `A` at the list, the records not read. -/
def postOf (τ : STy) : TPostV := fun k w ls _ v ρ => τ.P k w ls v ρ

theorem postOf_down (τ : STy) : (postOf τ).Down := fun n w ls _ v ρ h => τ.down n w ls v ρ h

/-- **`𝒞⟦F A⟧` at `cerwpT`**, at the table `Tb` and the frame condition `F`: a run at the list,
owning no records (E3, owned records), to a value of `A` or a stop the table allows. -/
def SCmp.ret (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (F : TFrame) (τ : STy) : SCmp where
  P n w ls e ρ := cerwpT (ℍ := ℍ) Tb (postOf τ) F n w ls [] e ρ
  down _ _ _ _ _ h := cerwpT_le hL hTb (postOf_down τ) (Nat.le_succ _) h

/-- **`F A` is Kripke along the re-reading of its list** (`cerwpT_kripke`). -/
theorem SCmp.ret_kripke {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {F : TFrame} {τ : STy}
    {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)} {ls' : List (SRecT w'.K)} {e : Expr}
    {ρ : TRes w.K} {ρ' : TRes w'.K} (hE : w.Ext w' ρ) (hr : RRw (w := w) (w' := w') ρ ρ')
    (hl : SRecsRR w'.Θ ls ls') (h : (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ).P n w ls e ρ) :
    (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ).P n w' ls' e ρ' :=
  cerwpT_kripke hE hr hl List.Forall₂.nil h

/-- A value of `A`, over a covered resource, is a run of `F A`. -/
theorem SCmp.ret_val {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {F : TFrame} {τ : STy}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {v : Val} {ρ : TRes w.K}
    (hc : CovR (sem w.Θ) w.K ρ) (h : τ.P n w ls v ρ) :
    (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ).P n w ls v.1 ρ :=
  cerwpT_val fun w₀ ρ₀ _ _ hE hr hl _ =>
    τ.mono n w w₀ ls _ v ρ ρ₀ hE hr (KeepRel.of_srecsRR hl ρ) hc h

/-- **`𝒞⟦A ⊸ C⟧`**: applied to a value of `A` at the list, over a resource composed with the
function's, a run of `C` at the list, at every index up to `n` (E4). -/
def SCmp.arr (τ : STy) (C : SCmp) : SCmp where
  P n w ls e ρ := ∀ k, k ≤ n → ∀ (v : Val) (ρa ρ' : TRes w.K), ResUT.CompS ρ ρa ρ' →
    τ.P k w ls v ρa → C.P k w ls (.app e (.val v)) ρ'
  down _ _ _ _ _ h k hk := h k (Nat.le_succ_of_le hk)

/-- **`𝒞⟦C & D⟧`**: each projection a run of its component. -/
def SCmp.amp (C D : SCmp) : SCmp where
  P n w ls e ρ := C.P n w ls (.app e (.val (.inj₁ .unit))) ρ ∧
    D.P n w ls (.app e (.val (.inj₂ .unit))) ρ
  down n w ls _ ρ h := ⟨C.down n w ls _ ρ h.1, D.down n w ls _ ρ h.2⟩

theorem SCmp.amp_kripke {C D : SCmp} (hC : C.P.Kripke) (hD : D.P.Kripke) :
    (SCmp.amp C D).P.Kripke :=
  fun n w w' ls ls' _ ρ ρ' hE hr hk h =>
    ⟨hC n w w' ls ls' _ ρ ρ' hE hr hk h.1, hD n w w' ls ls' _ ρ ρ' hE hr hk h.2⟩

/-- `𝒞⟦⊤⟧`. -/
def SCmp.top : SCmp where
  P _ _ _ _ _ := True
  down _ _ _ _ _ h := h

/-- **`𝒞⟦∀α ⊏ c. C⟧`**: instantiated at every lifetime strictly below `c` in the current tree, a
run of `C` at it. -/
def SCmp.all (c : Life) (C : Life → SCmp) : SCmp where
  P n w ls e ρ := ∀ α, w.K.lt α c → (C α).P n w ls (.app e (.val .unit)) ρ
  down n w ls _ ρ h α hα := (C α).down n w ls _ ρ (h α hα)

/-! ### `ν` -/

/-- A body over a candidate, monotone in it. -/
def SCmp.MonoBody (Φ : SCmp → SCmp) : Prop := ∀ C D : SCmp, C.Le D → (Φ C).Le (Φ D)

/-- **`𝒞⟦νX. C⟧`**, the greatest fixed point `⋃{R | R ⊆ C[R]}` over candidates that are
computation types: downward closed for every body. -/
def SCmp.nu (Φ : SCmp → SCmp) : SCmp where
  P n w ls e ρ := ∃ R : SCmp, R.Le (Φ R) ∧ R.P n w ls e ρ
  down n w ls e ρ := fun ⟨R, hR, h⟩ => ⟨R, hR, R.down n w ls e ρ h⟩

theorem SCmp.nu_greatest {Φ : SCmp → SCmp} {R : SCmp} (hR : R.Le (Φ R)) : R.Le (SCmp.nu Φ) :=
  fun _ _ _ _ _ h => ⟨R, hR, h⟩

/-- **Unfold** at a monotone body. -/
theorem SCmp.nu_unfold {Φ : SCmp → SCmp} (hΦ : SCmp.MonoBody Φ) :
    (SCmp.nu Φ).Le (Φ (SCmp.nu Φ)) :=
  fun n w ls e ρ ⟨_, hR, h⟩ => hΦ _ _ (SCmp.nu_greatest hR) n w ls e ρ (hR n w ls e ρ h)

/-- **Fold** at a monotone body. -/
theorem SCmp.nu_fold {Φ : SCmp → SCmp} (hΦ : SCmp.MonoBody Φ) :
    (Φ (SCmp.nu Φ)).Le (SCmp.nu Φ) :=
  SCmp.nu_greatest (hΦ _ _ (SCmp.nu_unfold hΦ))

theorem SCmp.amp_le {C₁ C₂ D₁ D₂ : SCmp} (h₁ : C₁.Le D₁) (h₂ : C₂.Le D₂) :
    (SCmp.amp C₁ C₂).Le (SCmp.amp D₁ D₂) :=
  fun n w ls _ ρ h => ⟨h₁ n w ls _ ρ h.1, h₂ n w ls _ ρ h.2⟩

/-- A stream of `C`s, `νX. C & X`: its body is monotone, so it folds and unfolds. -/
theorem SCmp.stream_body_mono (C : SCmp) : SCmp.MonoBody fun X => SCmp.amp C X :=
  fun _ _ h => SCmp.amp_le (fun _ _ _ _ _ x => x) h

/-- `νX. C` is Kripke when the candidates it is the union of are: at every world extension, a
candidate that is Kripke carries the run. -/
theorem SCmp.nu_kripke_of {Φ : SCmp → SCmp} {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {e : Expr} {ρ : TRes w.K} {ρ' : TRes w'.K} (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hk : KeepRel w'.Θ ls ls' ρ)
    (h : ∃ R : SCmp, R.P.Kripke ∧ R.Le (Φ R) ∧ R.P n w ls e ρ) : (SCmp.nu Φ).P n w' ls' e ρ' :=
  let ⟨R, hK, hR, hP⟩ := h
  ⟨R, hR, hK n w w' ls ls' e ρ ρ' hE hr hk hP⟩

/-! ### Thunks read at the relation -/

/-- **`𝒱⟦U C⟧` for a computation type**, forced by `force`: downward closed (from `C`'s) and
monotone (by `STy.thunk`'s definition). -/
def STy.thunkC (C : SCmp) (force : Val → Expr) : STy :=
  STy.thunk (fun n w ls v ρ => C.P n w ls (force v) ρ)
    (fun n w ls v ρ h => C.down n w ls (force v) ρ h)

/-- **A thunk from a run at the current world and list**, when `C` is Kripke along `KeepRel`.
`F A` is Kripke along the re-reading of the list (`SCmp.ret_kripke`), not along `KeepRel`: a
thunk of `F A` is one at every list keeping the records it reads, which a stored continuation's
share gives (`STy.kont_of_share`, `Core/TreeSemK.lean`) and a typed `λ`'s context gives by its
monotonicity. -/
theorem STy.thunk_intro {C : SCmp} (hK : C.P.Kripke) {force : Val → Expr} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {v : Val} {ρ : TRes w.K} (h : C.P n w ls (force v) ρ) :
    (STy.thunkC C force).P n w ls v ρ :=
  fun w' ρ' ls' hE hr hk => hK n w w' ls ls' _ ρ ρ' hE hr hk h

/-- **`𝒱⟦U (F A)⟧` at `cerwpT`**: a thunk `λ_. M` forced by applying it to `()`. -/
def STy.thunkRet (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (F : TFrame) (τ : STy) : STy :=
  STy.thunkC (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ) fun v => .app (.val v) (.val .unit)

/-- **A thunk of a value computation at the relation**: a thunk whose forcing is a value of `A`
is a thunk of `F A` at the world and list it is held at, at every index. -/
theorem STy.thunkC_val {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {F : TFrame} {τ : STy}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {v u : Val} {ρ : TRes w.K}
    (hc : CovR (sem w.Θ) w.K ρ) (h : τ.P n w ls u ρ) :
    (STy.thunkC (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ) fun _ => u.1).P n w ls v ρ :=
  fun w' ρ' ls' hE hr hk => SCmp.ret_val hr.cov (τ.mono n w w' ls ls' u ρ ρ' hE hr hk hc h)

end BoCa.Fig16.Tree.Wp

end
