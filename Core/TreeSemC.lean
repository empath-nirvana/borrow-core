import Core.TreeSem

/-!
# The relation's computation types at the lifetime tree  `[spec §62]`

The computation types of the step-indexed relation over the tree world, read at `cerwpT`
(`Core/TreeWpEff.lean`, whose carrier is `twp`). A computation type is `SCmp`: a predicate on terms
at the index and the world, downward closed. As in Core (`Core/Relation.lean`: "the Kripke
quantifier over `Ext` sits at `U` only"), a computation type reaches a value only under `U`, and
`U`'s quantifier over world extensions makes the thunk monotone (`STy.thunk`).

* **Downward closure of the relation** (`cerwpT_le`): at a table that reads what is owed only
  below its index (`TableT.Local`) and is itself downward closed (`TableT.Down`), and a
  downward-closed postcondition. The operation tables (`opTableT`) are, when their entries are
  (`opTableT_down`).
* **The formers**: `F A` at `cerwpT` (`SCmp.ret`), `A ⊸ C` (`SCmp.arr`), `C & D` (`SCmp.amp`),
  `⊤` (`SCmp.top`), `∀α ⊏ c. C` over the lifetimes below `c` in the current tree (`SCmp.all`),
  and `νX. C`, the greatest fixed point over candidates (`SCmp.nu`, fold and unfold at a
  monotone body).
* **Thunks read at the relation** (`STy.thunkC`, `STy.thunkRet`): a value type for every
  computation type, downward closed and monotone. Monotone by definition (`STy.thunk`); what makes
  a thunk available from a run at the current world is the relation's Kripke rule
  (`SCmp.ret_kripke`, from `cerwpT_kripke`, and `STy.thunk_intro`): a value of `F A`'s run
  (`SCmp.ret_val`) gives a thunk of `F A` at the world it is held at (`STy.thunkC_val`).

Continuation and task types are not here: #789 designs them.

**Departures** (`docs/new-core/scope-782.md` §2): E3, `SCmp.ret` runs at the empty list owning no
records (the records a lend opens are row 6's); E4, `SCmp.arr` reads its argument at every index
up to `n`, which downward closure at a step index needs (Core's `cC` has no index).
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
    fun w' ρ' lsR ls' O' hE hr hl hx hO =>
    ⟨fun k' hk a σ σ' hB hcσ =>
      (hcont w' ρ' lsR ls' O' hE hr hl hx hO).1 k' (by omega) a σ σ' hB hcσ,
      fun hq P hP => hd.2 P hP _ _ _ _ _ ((hcont w' ρ' lsR ls' O' hE hr hl hx hO).2 hq P hP)⟩⟩

/-! ### Computation types -/

/-- A predicate on terms at the step index and the tree world. -/
abbrev CSem : Type := Nat → (w : TWd) → Expr → TRes w.K → Prop

/-- Downward closed in the step index. -/
def CSem.Down (C : CSem) : Prop := ∀ n w e ρ, C (n + 1) w e ρ → C n w e ρ

/-- Monotone along world extension, on the re-reading. -/
def CSem.Kripke (C : CSem) : Prop :=
  ∀ n (w w' : TWd) e (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → C n w e ρ → C n w' e ρ'

/-- **A computation type of the relation at the tree**: downward closed in the index. -/
structure SCmp where
  P : CSem
  down : P.Down

/-- Inclusion of computation types. -/
def SCmp.Le (C D : SCmp) : Prop := ∀ n w e ρ, C.P n w e ρ → D.P n w e ρ

/-- The postcondition of `F A`: the value in `A`, the list and the records not read. -/
def postOf (τ : STy) : TPostV := fun k w _ _ v ρ => τ.P k w v ρ

theorem postOf_down (τ : STy) : (postOf τ).Down := fun n w _ _ v ρ h => τ.down n w v ρ h

/-- **`𝒞⟦F A⟧` at `cerwpT`**, at the table `Tb` and the frame condition `F`: a run, at the empty
list owning no records (E3), to a value of `A` or a stop the table allows. -/
def SCmp.ret (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (F : TFrame) (τ : STy) : SCmp where
  P n w e ρ := cerwpT (ℍ := ℍ) Tb (postOf τ) F n w [] [] e ρ
  down _ _ _ _ h := cerwpT_le hL hTb (postOf_down τ) (Nat.le_succ _) h

/-- **`F A` is Kripke**: `cerwpT_kripke`, at the empty list and records. -/
theorem SCmp.ret_kripke {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {F : TFrame} {τ : STy} :
    (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ).P.Kripke :=
  fun _ _ _ _ _ _ hE hr h => cerwpT_kripke hE hr List.Forall₂.nil List.Forall₂.nil h

/-- A value of `A`, over a covered resource, is a run of `F A`. -/
theorem SCmp.ret_val {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {F : TFrame} {τ : STy}
    {n : Nat} {w : TWd} {v : Val} {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (h : τ.P n w v ρ) : (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ).P n w v.1 ρ :=
  cerwpT_val fun w₀ ρ₀ _ _ hE hr _ _ => τ.mono n w w₀ v ρ ρ₀ hE hr hc h

/-- **`𝒞⟦A ⊸ C⟧`**: applied to a value of `A` over a resource composed with the function's, a run
of `C`, at every index up to `n` (E4). -/
def SCmp.arr (τ : STy) (C : SCmp) : SCmp where
  P n w e ρ := ∀ k, k ≤ n → ∀ (v : Val) (ρa ρ' : TRes w.K), ResUT.CompS ρ ρa ρ' →
    τ.P k w v ρa → C.P k w (.app e (.val v)) ρ'
  down _ _ _ _ h k hk := h k (Nat.le_succ_of_le hk)

/-- **`𝒞⟦C & D⟧`**: each projection a run of its component. -/
def SCmp.amp (C D : SCmp) : SCmp where
  P n w e ρ := C.P n w (.app e (.val (.inj₁ .unit))) ρ ∧ D.P n w (.app e (.val (.inj₂ .unit))) ρ
  down n w _ ρ h := ⟨C.down n w _ ρ h.1, D.down n w _ ρ h.2⟩

theorem SCmp.amp_kripke {C D : SCmp} (hC : C.P.Kripke) (hD : D.P.Kripke) :
    (SCmp.amp C D).P.Kripke :=
  fun n w w' _ ρ ρ' hE hr h => ⟨hC n w w' _ ρ ρ' hE hr h.1, hD n w w' _ ρ ρ' hE hr h.2⟩

/-- `𝒞⟦⊤⟧`. -/
def SCmp.top : SCmp where
  P _ _ _ _ := True
  down _ _ _ _ h := h

/-- **`𝒞⟦∀α ⊏ c. C⟧`**: instantiated at every lifetime strictly below `c` in the current tree, a
run of `C` at it. -/
def SCmp.all (c : Life) (C : Life → SCmp) : SCmp where
  P n w e ρ := ∀ α, w.K.lt α c → (C α).P n w (.app e (.val .unit)) ρ
  down n w _ ρ h α hα := (C α).down n w _ ρ (h α hα)

/-! ### `ν` -/

/-- A body over a candidate, monotone in it. -/
def SCmp.MonoBody (Φ : SCmp → SCmp) : Prop := ∀ C D : SCmp, C.Le D → (Φ C).Le (Φ D)

/-- **`𝒞⟦νX. C⟧`**, the greatest fixed point `⋃{R | R ⊆ C[R]}` over candidates that are
computation types: downward closed for every body. -/
def SCmp.nu (Φ : SCmp → SCmp) : SCmp where
  P n w e ρ := ∃ R : SCmp, R.Le (Φ R) ∧ R.P n w e ρ
  down n w e ρ := fun ⟨R, hR, h⟩ => ⟨R, hR, R.down n w e ρ h⟩

theorem SCmp.nu_greatest {Φ : SCmp → SCmp} {R : SCmp} (hR : R.Le (Φ R)) : R.Le (SCmp.nu Φ) :=
  fun _ _ _ _ h => ⟨R, hR, h⟩

/-- **Unfold** at a monotone body. -/
theorem SCmp.nu_unfold {Φ : SCmp → SCmp} (hΦ : SCmp.MonoBody Φ) :
    (SCmp.nu Φ).Le (Φ (SCmp.nu Φ)) :=
  fun n w e ρ ⟨_, hR, h⟩ => hΦ _ _ (SCmp.nu_greatest hR) n w e ρ (hR n w e ρ h)

/-- **Fold** at a monotone body. -/
theorem SCmp.nu_fold {Φ : SCmp → SCmp} (hΦ : SCmp.MonoBody Φ) :
    (Φ (SCmp.nu Φ)).Le (SCmp.nu Φ) :=
  SCmp.nu_greatest (hΦ _ _ (SCmp.nu_unfold hΦ))

theorem SCmp.amp_le {C₁ C₂ D₁ D₂ : SCmp} (h₁ : C₁.Le D₁) (h₂ : C₂.Le D₂) :
    (SCmp.amp C₁ C₂).Le (SCmp.amp D₁ D₂) :=
  fun n w _ ρ h => ⟨h₁ n w _ ρ h.1, h₂ n w _ ρ h.2⟩

/-- A stream of `C`s, `νX. C & X`: its body is monotone, so it folds and unfolds. -/
theorem SCmp.stream_body_mono (C : SCmp) : SCmp.MonoBody fun X => SCmp.amp C X :=
  fun _ _ h => SCmp.amp_le (fun _ _ _ _ x => x) h

/-- `νX. C` is Kripke when the candidates it is the union of are: at every world extension, a
candidate that is Kripke carries the run. -/
theorem SCmp.nu_kripke_of {Φ : SCmp → SCmp} {n : Nat} {w w' : TWd} {e : Expr} {ρ : TRes w.K}
    {ρ' : TRes w'.K} (hE : w.Ext w' ρ) (hr : RRw (w := w) (w' := w') ρ ρ')
    (h : ∃ R : SCmp, R.P.Kripke ∧ R.Le (Φ R) ∧ R.P n w e ρ) : (SCmp.nu Φ).P n w' e ρ' :=
  let ⟨R, hK, hR, hP⟩ := h
  ⟨R, hR, hK n w w' e ρ ρ' hE hr hP⟩

/-! ### Thunks read at the relation -/

/-- **`𝒱⟦U C⟧` for a computation type**, forced by `force`: downward closed (from `C`'s) and
monotone (by `STy.thunk`'s definition). -/
def STy.thunkC (C : SCmp) (force : Val → Expr) : STy :=
  STy.thunk (fun n w v ρ => C.P n w (force v) ρ) (fun n w v ρ h => C.down n w (force v) ρ h)

/-- **A thunk from a run at the current world**: when `C` is Kripke, a run of the forced thunk
at `w` is a thunk at `w`. This is what makes `STy.thunk`'s quantifier over extensions met. -/
theorem STy.thunk_intro {C : SCmp} (hK : C.P.Kripke) {force : Val → Expr} {n : Nat} {w : TWd}
    {v : Val} {ρ : TRes w.K} (h : C.P n w (force v) ρ) : (STy.thunkC C force).P n w v ρ :=
  fun w' ρ' hE hr => hK n w w' _ ρ ρ' hE hr h

/-- **`𝒱⟦U (F A)⟧` at `cerwpT`**: a thunk `λ_. M` forced by applying it to `()`. -/
def STy.thunkRet (Tb : TableT) (hL : Tb.Local) (hTb : Tb.Down) (F : TFrame) (τ : STy) : STy :=
  STy.thunkC (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ) fun v => .app (.val v) (.val .unit)

/-- A thunk of `F A` from a run of its body at the current world (`cerwpT_kripke`). -/
theorem STy.thunkRet_intro {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {F : TFrame}
    {τ : STy} {n : Nat} {w : TWd} {v : Val} {ρ : TRes w.K}
    (h : cerwpT (ℍ := ℍ) Tb (postOf τ) F n w [] [] (.app (.val v) (.val .unit)) ρ) :
    (STy.thunkRet (ℍ := ℍ) Tb hL hTb F τ).P n w v ρ :=
  STy.thunk_intro SCmp.ret_kripke h

/-- **A thunk of a value computation at the relation**: a thunk whose forcing is a value of `A`
is a thunk of `F A` at the world it is held at, at every index. -/
theorem STy.thunkC_val {Tb : TableT} {hL : Tb.Local} {hTb : Tb.Down} {F : TFrame} {τ : STy}
    {n : Nat} {w : TWd} {v u : Val} {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (h : τ.P n w u ρ) :
    (STy.thunkC (SCmp.ret (ℍ := ℍ) Tb hL hTb F τ) fun _ => u.1).P n w v ρ :=
  STy.thunk_intro SCmp.ret_kripke (SCmp.ret_val hc h)

end BoCa.Fig16.Tree.Wp

end
