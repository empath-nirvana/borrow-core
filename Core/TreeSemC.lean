import Core.TreeSem
import Core.TreeHandle
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
* **The formers**: `F A` (`SCmp.ret`): a bare run of `cerwpT` at the list, owning no records, to a
  value of `A` (Core's `cC (.ret A)`, a bare `wpTS` run). Monotone in `A` (`SCmp.ret_le`, from
  `cerwpT_post_mono`) and Kripke along the re-reading of its whole list (`SCmp.ret_reread`, from
  `cerwpT_kripke`). It is not Kripke along `KeepRel` (`Obs.cerwpT_not_keepKripkeNil`,
  `Core/TreeSemObs.lean`), and nothing asks it to be: the quantifier over later lists keeping the
  records a resource reads is `U`'s (`STy.thunk`). `A ⊸ C` (`SCmp.arr`), `C & D` (`SCmp.amp`),
  `⊤` (`SCmp.top`), `∀α ⊏ c. C` over the lifetimes below `c` in the current tree (`SCmp.all`), and
  `νX. C`, the greatest fixed point over candidates (`SCmp.nu`, fold and unfold at a monotone body),
  shown at Core's body shape `F(A ⊕ U X) & F B` (`SCmp.loopBody_mono`, `SCmp.loop_nonempty`).
* **Thunks read at the relation** (`STy.thunkC`, `STy.thunkRet`): a value type for every
  computation type, downward closed and monotone by `STy.thunk`'s definition, monotone in the
  computation type (`STy.thunkC_le`). A thunk is introduced as Core's `thunkF_compatC` and
  `thunkV_compatC` introduce one: from the computation at every world and list, over the
  environment's value type, and the environment carried to the later world and list by its own
  monotonicity (`TEnv.Mono`, the tree's `gDenC_local`; `STy.env_mono` at a value type):
  `STy.thunk_intro_env` for every computation type, `STy.thunkRet_intro_env` at `F A`,
  `STy.thunkRet_lam_env` for `λ_. M` (`thunkF_compatC`'s head step), each with a corollary at an
  environment read at a value type (`STy.thunk_intro`, `STy.thunkRet_intro`, `STy.thunkRet_lam`). From
  a value (`STy.thunkC_val`); from a stored continuation's share (`Core/TreeSemK.lean`).

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
    {Fb F : TFrame} {m n : Nat} (hmn : m ≤ n) {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ) : cerwpT (ℍ := ℍ) Tb Q Fb F m w ls O e ρ := by
  rw [cerwpT_eq] at h
  exact cerwpT_fold_at hL hmn (twp_le (cerwpPostT_down hQ hTb) hmn h)

/-- **`cerwpT` is monotone in its postcondition**, by strong induction on the index: a stop the
table allows owing the continuation at the smaller postcondition, it allows owing it at the larger
(`TableT.Local`). -/
theorem cerwpT_post_mono_n {Tb : TableT} (hL : Tb.Local) {Q₁ Q₂ : TPostV}
    (hQ : ∀ k w ls O v ρ, Q₁ k w ls O v ρ → Q₂ k w ls O v ρ) {Fb : TFrame} :
    ∀ (n : Nat) (F : TFrame) (w : TWd) (ls : List (SRecT w.K)) (O : List (FrameRecT w.K))
      (e : Expr) (ρ : TRes w.K),
      cerwpT (ℍ := ℍ) Tb Q₁ Fb F n w ls O e ρ → cerwpT (ℍ := ℍ) Tb Q₂ Fb F n w ls O e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F w ls O e ρ h
  rw [cerwpT_eq] at h ⊢
  refine twp_mono_le (fun k hk w' ls' O' t ρ' ht => ?_) h
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact Or.inl ⟨v, rfl, hQ _ _ _ _ _ _ hv⟩
  · refine Or.inr (hL Fb k w' ls' O' t _ _ ρ' (fun F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpTC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) F' w'' ls'' O'' e'' ρ'' hΨ

theorem cerwpT_post_mono {Tb : TableT} (hL : Tb.Local) {Q₁ Q₂ : TPostV}
    (hQ : ∀ k w ls O v ρ, Q₁ k w ls O v ρ → Q₂ k w ls O v ρ) {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : cerwpT (ℍ := ℍ) Tb Q₁ Fb F n w ls O e ρ) : cerwpT (ℍ := ℍ) Tb Q₂ Fb F n w ls O e ρ :=
  cerwpT_post_mono_n hL hQ n F w ls O e ρ h

/-- An operation's entry downward closed: its payload. Its cancel branch is owed as a continuation
(`contShareT`), so the table's own downward closure covers it. -/
def OpEntT.Down (en : OpEntT) : Prop := ∀ n w ls v ρ, en.PA (n + 1) w ls v ρ → en.PA n w ls v ρ

/-- **The operation tables are downward closed** when their entries are. -/
theorem opTableT_down {T : OpTabT} (hT : ∀ n i en, T n i = some en → en.Down) :
    (opTableT T).Down := by
  intro F k w ls O t Ψ ρ h
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hu, hcont⟩ := h
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hT n i en h₃ _ _ _ _ _ hA, hu,
    fun w' ρ' ls' O' hE hr hx hO =>
    ⟨fun k' hk a σ σ' hB hcσ =>
      (hcont w' ρ' ls' O' hE hr hx hO).1 k' (by omega) a σ σ' hB hcσ,
      fun hq hf k' hk => (hcont w' ρ' ls' O' hE hr hx hO).2 hq hf k' (by omega)⟩⟩

/-! ### A run at the empty list says nothing of a borrow -/

/-- **A run at the empty list, owning no records, holds of every term over a resource holding a
view.** No world whose list is empty holds an `imm` cell: the list's records are the world's
lineage (`TIT`), and every `imm` cell of the world's agreement is a record's cell or a chain
position of one (`CoverageT`). So `twp` at `[]` quantifies over no start, and holds vacuously.

This is why the value types read the list (E3, #794): a thunk type that does not read the list
runs its thunk at a list fixed in advance, `[]` the only one every world has, and then holds of
every thunk holding a borrow, stuck or not. -/
theorem cerwpT_nil_of_imm {Tb : TableT} {Q : TPostV} {Fb F : TFrame} {n : Nat} {w : TWd}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} {l : BoCa.Loc} {ψ : TCell w.K}
    (hl : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm) : cerwpT (ℍ := ℍ) Tb Q Fb F n w [] O e ρ := by
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

/-- **A computation type of the relation at the tree**: downward closed in the index. -/
structure SCmp where
  P : CSem
  down : P.Down

/-- Inclusion of computation types. -/
def SCmp.Le (C D : SCmp) : Prop := ∀ n w ls e ρ, C.P n w ls e ρ → D.P n w ls e ρ

/-- The postcondition of `F A`: the value in `A` at the list, the records not read. -/
def postOf (τ : STy) : TPostV := fun k w ls _ v ρ => τ.P k w ls v ρ

theorem postOf_down (τ : STy) : (postOf τ).Down := fun n w ls _ v ρ h => τ.down n w ls v ρ h

/-! ### `F A`: a bare run at the list -/

/-- **A run of `F A` at a list**: `cerwpT` at the table `Tb`, the base frame condition `Fb` and the
present one `F`, owning no records (E3, owned records), to a value of `A` or a stop the table
allows. -/
def RunRet (Tb : TableT) (Fb F : TFrame) (τ : STy) : CSem :=
  fun n w ls e ρ => cerwpT (ℍ := ℍ) Tb (postOf τ) Fb F n w ls [] e ρ

/-- **`𝒞⟦F A⟧` at `cerwpT`**: a bare run of `F A` at the world and list it is read at (`RunRet`),
as Core's `cC (.ret A) ls e` is `wpTS ls e …` (`Core/Relation.lean`). The Kripke quantifier over
later worlds and lists is `U`'s (`STy.thunk`): a thunk of `F A` is a run at every later list
keeping the records its resource reads, and is introduced from the computation at each of them
(`STy.thunk_intro`), not from a run at the current one. -/
def SCmp.ret (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (Fb F : TFrame) (τ : STy) : SCmp where
  P := RunRet (ℍ := ℍ) Tb Fb F τ
  down _ _ _ _ _ h := cerwpT_le hL hTb (postOf_down τ) (Nat.le_succ _) h

/-- **`F A` is Kripke along the re-reading of its whole list** (`cerwpT_kripke`): at every
extension, on the re-reading of the resource, at every list re-reading the list record by record
(`SRecsRR`). Along `KeepRel`, which may leave out records the resource does not read, it is not
(`Obs.cerwpT_not_keepKripkeNil`). -/
theorem SCmp.ret_reread {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame} {τ : STy}
    {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)} {ls' : List (SRecT w'.K)} {e : Expr}
    {ρ : TRes w.K} {ρ' : TRes w'.K} (hE : w.Ext w' ρ) (hr : RRw (w := w) (w' := w') ρ ρ')
    (hl : SRecsRR w'.Θ ls ls') (h : (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F τ).P n w ls e ρ) :
    (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F τ).P n w' ls' e ρ' :=
  cerwpT_kripke hE hr hl List.Forall₂.nil h

/-- A value of `A`, over a covered resource, is a run of `F A`. -/
theorem SCmp.ret_val {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame} {τ : STy}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {v : Val} {ρ : TRes w.K}
    (hc : CovR (sem w.Θ) w.K ρ) (h : τ.P n w ls v ρ) :
    (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F τ).P n w ls v.1 ρ :=
  cerwpT_val fun w₀ ρ₀ _ _ hE₀ hr₀ hl _ =>
    τ.mono n w w₀ ls _ v ρ ρ₀ hE₀ hr₀ (KeepRel.of_srecsRR hl ρ) hc h

/-- **`F A` is monotone in `A`**: `cerwpT` is monotone in its postcondition (`twp_mono` at every
index of the unfolding, `cerwpT_post_mono`). -/
theorem SCmp.ret_le {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame} {σ τ : STy}
    (h : σ.Le τ) : (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F σ).Le (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F τ) :=
  fun _ _ _ _ _ hr => cerwpT_post_mono hL (fun k w ls _ v ρ x => h k w ls v ρ x) hr

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

/-! ### Thunks read at the relation -/

/-- **`𝒱⟦U C⟧` for a computation type**, forced by `force`: downward closed (from `C`'s) and
monotone (by `STy.thunk`'s definition). -/
def STy.thunkC (C : SCmp) (force : Val → Expr) : STy :=
  STy.thunk (fun n w ls v ρ => C.P n w ls (force v) ρ)
    (fun n w ls v ρ h => C.down n w ls (force v) ρ h)

/-- **`U` is monotone in its computation type.** -/
theorem STy.thunkC_le {C D : SCmp} (h : C.Le D) (force : Val → Expr) :
    (STy.thunkC C force).Le (STy.thunkC D force) :=
  fun _ _ _ v _ hv w' ρ' ls' hE hr hk => h _ w' ls' (force v) ρ' (hv w' ρ' ls' hE hr hk)

/-- **An environment's meaning**: a predicate on resources at the index, the world and the list,
the reading of a context at its substitution (Core's `gDenC ls δ Γ γ`). -/
abbrev TEnv : Type := Nat → (w : TWd) → List (SRecT w.K) → TRes w.K → Prop

/-- **An environment monotone along the tree**, at `TVal.Mono`'s shape: at every world extension
carrying `ρ`, on the re-reading of a covered `ρ`, at every list keeping the records of `ls` that
`ρ` reads. The tree's `gDenC_local`. -/
def TEnv.Mono (G : TEnv) : Prop :=
  ∀ n (w w' : TWd) (ls : List (SRecT w.K)) (ls' : List (SRecT w'.K)) (ρ : TRes w.K)
    (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ →
    CovR (sem w.Θ) w.K ρ → G n w ls ρ → G n w' ls' ρ'

/-- The environment `γ` read at a value type. -/
def STy.env (τΓ : STy) (γ : Val) : TEnv := fun n w ls ρ => τΓ.P n w ls γ ρ

/-- An environment read at a value type is monotone (`STy.mono`). -/
theorem STy.env_mono (τΓ : STy) (γ : Val) : (τΓ.env γ).Mono :=
  fun n w w' ls ls' ρ ρ' hE hr hk hc h => τΓ.mono n w w' ls ls' γ ρ ρ' hE hr hk hc h

/-- **A thunk from its computation at every world and list**, Core's `thunkV_compatC`, at every
monotone environment: the forcing is a run of `C` at every world and list over a covered resource
meeting the environment `G`, and `G` holds here. The thunk is forced at a later world and list
keeping the records its resource reads; `G` holds there (`hG`, the tree's `gDenC_local`), so the
forcing runs there. -/
theorem STy.thunk_intro_env {C : SCmp} {force : Val → Expr} {G : TEnv} (hG : G.Mono) {v : Val}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (hM : ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' →
      G n w' ls' ρ' → C.P n w' ls' (force v) ρ')
    (hg : G n w ls ρ) : (STy.thunkC C force).P n w ls v ρ :=
  fun w' ρ' ls' hE hr hk => hM w' ls' ρ' hr.cov (hG n w w' ls ls' ρ ρ' hE hr hk hc hg)

/-- **`STy.thunk_intro_env` at an environment read at a value type**: `γ` a value of `τΓ`. -/
theorem STy.thunk_intro {C : SCmp} {force : Val → Expr} {τΓ : STy} {γ v : Val} {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (hM : ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' →
      τΓ.P n w' ls' γ ρ' → C.P n w' ls' (force v) ρ')
    (hg : τΓ.P n w ls γ ρ) : (STy.thunkC C force).P n w ls v ρ :=
  STy.thunk_intro_env (STy.env_mono τΓ γ) hc hM hg

/-- **`𝒱⟦U (F A)⟧` at `cerwpT`**: a thunk `λ_. M` forced by applying it to `()`. -/
def STy.thunkRet (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (Fb F : TFrame) (τ : STy) : STy :=
  STy.thunkC (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F τ) fun v => .app (.val v) (.val .unit)

/-- **A thunk of `F A` from its forcing's run at every world and list** over a monotone
environment: `STy.thunk_intro_env` at `F A`. -/
theorem STy.thunkRet_intro_env {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τ : STy} {G : TEnv} (hG : G.Mono) {v : Val} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (hM : ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' →
      G n w' ls' ρ' → RunRet (ℍ := ℍ) Tb Fb F τ n w' ls' (.app (.val v) (.val .unit)) ρ')
    (hg : G n w ls ρ) : (STy.thunkRet (ℍ := ℍ) Tb hL hTb Fb F τ).P n w ls v ρ :=
  STy.thunk_intro_env hG hc hM hg

/-- **`STy.thunkRet_intro_env` at an environment read at a value type.** -/
theorem STy.thunkRet_intro {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τ τΓ : STy} {γ v : Val} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {ρ : TRes w.K}
    (hc : CovR (sem w.Θ) w.K ρ)
    (hM : ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' →
      τΓ.P n w' ls' γ ρ' → RunRet (ℍ := ℍ) Tb Fb F τ n w' ls' (.app (.val v) (.val .unit)) ρ')
    (hg : τΓ.P n w ls γ ρ) : (STy.thunkRet (ℍ := ℍ) Tb hL hTb Fb F τ).P n w ls v ρ :=
  STy.thunkRet_intro_env (STy.env_mono τΓ γ) hc hM hg

/-- **`thunk M : U (F A)`, written `λ_. M`**, Core's `thunkF_compatC`, at every monotone
environment: `M` a run of `F A` at every world and list over a covered resource meeting the
environment, the environment met here. Forcing `λ_. M` steps to `M` (`Head.beta`), the step paid
from the index. -/
theorem STy.thunkRet_lam_env {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τ : STy} {G : TEnv} (hG : G.Mono) {M : Expr} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (hM : ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' →
      G n w' ls' ρ' → RunRet (ℍ := ℍ) Tb Fb F τ n w' ls' (M.subst 0 Val.unit) ρ')
    (hg : G n w ls ρ) : (STy.thunkRet (ℍ := ℍ) Tb hL hTb Fb F τ).P n w ls (Val.lam M) ρ := by
  refine STy.thunkRet_intro_env hG hc (fun w' ls' ρ' hc' hg' => ?_) hg
  cases n with
  | zero => exact cerwpT_zero
  | succ n =>
      refine cerwpT_step hL (fun μ => ?_) (cerwpT_le hL hTb (postOf_down τ) (Nat.le_succ n)
        (hM w' ls' ρ' hc' hg'))
      simpa [BoCa.BoLo.Kont.plug] using
        step1Only_plug (ℍ := ℍ) (BoCa.BoLo.Head.beta μ M Val.unit) rfl BoCa.BoLo.Kont.hole

/-- **`STy.thunkRet_lam_env` at an environment read at a value type.** -/
theorem STy.thunkRet_lam {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τ τΓ : STy} {γ : Val} {M : Expr} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {ρ : TRes w.K}
    (hc : CovR (sem w.Θ) w.K ρ)
    (hM : ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' →
      τΓ.P n w' ls' γ ρ' → RunRet (ℍ := ℍ) Tb Fb F τ n w' ls' (M.subst 0 Val.unit) ρ')
    (hg : τΓ.P n w ls γ ρ) : (STy.thunkRet (ℍ := ℍ) Tb hL hTb Fb F τ).P n w ls (Val.lam M) ρ :=
  STy.thunkRet_lam_env (STy.env_mono τΓ γ) hc hM hg

/-- **A thunk of a value computation at the relation**: a thunk whose forcing is a value of `A`
is a thunk of `F A` at the world and list it is held at, at every index. The environment is the
value itself (`STy.thunk_intro` at `τΓ := A`). -/
theorem STy.thunkC_val {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame} {τ : STy}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {v u : Val} {ρ : TRes w.K}
    (hc : CovR (sem w.Θ) w.K ρ) (h : τ.P n w ls u ρ) :
    (STy.thunkC (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F τ) fun _ => u.1).P n w ls v ρ :=
  STy.thunk_intro (τΓ := τ) hc (fun _ _ _ hc' h' => SCmp.ret_val hc' h') h

/-! ### `ν` at Core's bodies -/

/-- **A `ν` body of Core's shape**, `F(A ⊕ U X) & F B` (`loopBody`): `X` only as `U X` inside the
`A` of an `F` leaf of an `&`-tree. -/
def SCmp.loopBody (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (Fb F : TFrame) (τA τB : STy)
    (force : Val → Expr) (X : SCmp) : SCmp :=
  SCmp.amp (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F (STy.sum τA (STy.thunkC X force)))
    (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F τB)

/-- **`loopBody` is monotone**: from `F`'s monotonicity in its value type (`SCmp.ret_le`), `+`'s
(`STy.sum_le`) and `U`'s in its computation type (`STy.thunkC_le`). So `ν` folds and unfolds at
it (`SCmp.nu_fold`, `SCmp.nu_unfold`). -/
theorem SCmp.loopBody_mono {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τA τB : STy} {force : Val → Expr} :
    SCmp.MonoBody (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F τA τB force) :=
  fun _ _ h => SCmp.amp_le
    (SCmp.ret_le (STy.sum_le (STy.le_refl τA) (STy.thunkC_le h force)))
    (fun _ _ _ _ _ x => x)

/-- **A `ν` of Core's shape unfolds**: a run of `νX. F(A ⊕ U X) & F B` is a pair of runs, the first
returning `A` or a thunk of the `ν` itself. -/
theorem SCmp.loop_unfold {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τA τB : STy} {force : Val → Expr} :
    (SCmp.nu (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F τA τB force)).Le
      (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F τA τB force
        (SCmp.nu (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F τA τB force))) :=
  SCmp.nu_unfold SCmp.loopBody_mono

/-- **A `ν` of Core's shape folds**, and is not empty: a pair of values `inj₁ a` (projection one)
and `b` (projection two) is a run of the body at any candidate, hence of the `ν`. -/
theorem SCmp.loop_fold {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τA τB : STy} {force : Val → Expr} :
    (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F τA τB force
        (SCmp.nu (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F τA τB force))).Le
      (SCmp.nu (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F τA τB force)) :=
  SCmp.nu_fold SCmp.loopBody_mono

/-- `λ_. inj₁ ()`. -/
def constInl : Val := Val.lam (.val (Val.inj₁ Val.unit))

theorem constInl_step (a : Val) (μ : BoCa.BoLo.Heap) :
    Step1Only (ℍ := ℍ) μ (.app (.val constInl) (.val a)) μ (.val (Val.inj₁ Val.unit)) := by
  have h := step1Only_plug (ℍ := ℍ) (BoCa.BoLo.Head.beta μ (.val (Val.inj₁ Val.unit)) a) rfl
    BoCa.BoLo.Kont.hole
  simpa [BoCa.BoLo.Kont.plug, Expr.subst, constInl] using h

/-- The candidate holding `λ_. inj₁ ()` over the empty resource. -/
def constCand : SCmp where
  P _ _ _ e ρ := e = (constInl).1 ∧ ρ = PMap.empty
  down _ _ _ _ _ h := h

/-- `λ_. inj₁ ()` over the empty resource, at either projection, is a run of `F (1 + _)`. -/
theorem constInl_ret {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame} {τ : STy}
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} (b : Val) :
    (SCmp.ret (ℍ := ℍ) Tb hL hTb Fb F (STy.sum STy.unit τ)).P n w ls
      (.app (.val constInl) (.val b)) PMap.empty := by
  cases n with
  | zero => exact cerwpT_zero
  | succ n =>
      refine cerwpT_step hL (constInl_step b) ?_
      exact cerwpT_val (v := Val.inj₁ Val.unit) fun _ _ _ _ _ hr₀ _ _ =>
        Or.inl ⟨_, rfl, rfl, RR.of_empty hr₀⟩

/-- **The `ν` of Core's shape is not empty**: `λ_. inj₁ ()` is a run of
`νX. F(1 ⊕ U X) & F(1 + 0)` at every index, world and list: the candidate holding it is below the
body at itself (`SCmp.nu_greatest`). -/
theorem SCmp.loop_nonempty {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {force : Val → Expr} (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    (SCmp.nu (SCmp.loopBody (ℍ := ℍ) Tb hL hTb Fb F STy.unit (STy.sum STy.unit STy.zero)
      force)).P n w ls (constInl).1 PMap.empty :=
  SCmp.nu_greatest (R := constCand) (fun _ _ _ _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨constInl_ret _, constInl_ret _⟩) n w ls _ _ ⟨rfl, rfl⟩

/-- **`STy.thunkRet_lam` met**: `λ_. inj₁ ()` is a thunk of `F (1 + A)`, at every index, world and
list, over the empty environment (`τΓ := 1`, `γ := ()`): its body `inj₁ ()` is a value of `1 + A`
over the empty resource at every world and list. -/
theorem STy.thunkRet_constInl {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {Fb F : TFrame}
    {τ : STy} (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    (STy.thunkRet (ℍ := ℍ) Tb hL hTb Fb F (STy.sum STy.unit τ)).P n w ls constInl PMap.empty :=
  STy.thunkRet_lam (τΓ := STy.unit) (γ := Val.unit) (M := .val (Val.inj₁ Val.unit))
    (fun _ _ e => by simp at e)
    (fun _ _ _ _ hg => by
      obtain ⟨-, rfl⟩ := hg
      simpa [Expr.subst, RunRet] using cerwpT_val (ℍ := ℍ) (v := Val.inj₁ Val.unit)
        (Tb := Tb) (Q := postOf (STy.sum STy.unit τ)) (Fb := Fb) (F := F) (O := [])
        fun _ _ _ _ _ hr₀ _ _ => Or.inl ⟨_, rfl, rfl, RR.of_empty hr₀⟩)
    ⟨rfl, rfl⟩

end BoCa.Fig16.Tree.Wp

end
