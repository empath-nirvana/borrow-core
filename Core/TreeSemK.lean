import Core.TreeSemC

/-!
# Continuation and task types at the lifetime tree  `[spec §62]`

A continuation is a thunk `U (B ⊸ C)` and a stored task is a boxed thunk `[@d] U C` (no new
former: `docs/new-core/scope-789.md` §2.4). Both are `STy`s, so downward closed and monotone along
the tree by `STy.thunk` and `STy.box`. What this file proves is that the meaning is the right one:

* **A continuation captured at a stop is a value of its type** (`STy.kont_of_share`). The relation's
  capture is the share `contShareT` (`Core/TreeWpEff.lean`): at every extension of the stop's world,
  at every list keeping the re-readings of the stop list's records the share reads (`KeepRel`), the
  continuation resumes. A thunk is read at exactly that quantifier (`STy.thunk`), so a `κ` holding
  a view of an open lend, at a stop list holding the lend's record, is a value of
  `U (B ⊸ F A)` at that list, for every answer type `B` the operation answers and every result
  type `A`. Uniform in the types, the lifetimes and the nesting of the lends: no case split.
* **Resumable after any extension at its type** (`STy.kont_resume`), and boxed at a lifetime its
  share outlives (`STy.kontBox_of_share`), carried along an extension in which other branches
  opened and ended records of their own, and resumed there (`STy.kontBox_resume_after`).
* **Tasks** (`STy.task`): a boxed thunk of any computation type, forced at every later world and
  list keeping the records it reads (`STy.task_force_after`).
* **Rules out a continuation stored past its lend** (`STy.not_kontBox_of_view`): a boxed value
  holding a view at `α` is not of `[@d] A` unless `d` is strictly below `α`. A box that admitted a
  `κ` holding a view of a lend at a lifetime the lend does not outlive is refused.

**What the resumed run owns.** `STy.kont_of_share` is at a share owning no records (`O = []`): the
lend whose view `κ` holds was opened outside the handled computation, so its record is in the stop
list. A continuation owning the records of lends its own branch opened (row 6) is not a value of a
type here: the value types own no records (departure E3, owned records).
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

/-! ### The frame of a continuation owning no records -/

/-- The frame a share owning no records resumes at: `F` and the entry's resumer guarantee at no
records. -/
def fdNil (en : OpEntT) (v : Val) (F : TFrame) : TFrame := fun w ρf => F w ρf ∧ en.fd v w [] ρf

/-- `fdAt` at no records is `fdNil`, at every world the empty list is read at. -/
theorem fdAt_nil (en : OpEntT) (v : Val) (F : TFrame) {w' : TWd} :
    fdAt en v F (w' := w') [] = fdNil en v F := by
  funext w'' ρf
  apply propext
  constructor
  · rintro ⟨hF, h⟩
    exact ⟨hF, h [] List.Forall₂.nil⟩
  · rintro ⟨hF, h⟩
    refine ⟨hF, fun O'' hO => ?_⟩
    cases hO
    exact h

/-! ### Continuation and task types -/

/-- **`𝒱⟦U (B ⊸ C)⟧`, a continuation's type**: `κ` is the function, applied to an answer of `B`
a run of `C`, at every extension and list keeping the records its resource reads. -/
def STy.kont (τB : STy) (C : SCmp) : STy := STy.thunkC (SCmp.arr τB C) Expr.val

/-- **A continuation boxed at `d`**, BOXED-κ's `[@d] K`: `[@d] U (B ⊸ C)`. -/
def STy.kontBox (d : Life) (τB : STy) (C : SCmp) : STy := STy.box d (STy.kont τB C)

/-- **A task at `d`**: `[@d] U C`, a stored suspended computation forced by `force` (`lib/async`'s
`Task`, `ν` over a `κ`). -/
def STy.task (d : Life) (C : SCmp) (force : Val → Expr) : STy := STy.box d (STy.thunkC C force)

/-- **A continuation at its type is resumed at every later world and list keeping the records it
reads**, at every answer of its answer type over a resource beside its own. -/
theorem STy.kont_resume {τB : STy} {C : SCmp} {n : Nat} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {κ : Val} {ρ : TRes w.K} {ρ' : TRes w'.K}
    (h : (STy.kont τB C).P n w ls κ ρ) (hE : w.Ext w' ρ) (hr : RRw (w := w) (w' := w') ρ ρ')
    (hk : KeepRel w'.Θ ls ls' ρ) {j : Nat} (hj : j ≤ n) {a : Val} {ρa σ : TRes w'.K}
    (hc : ResUT.CompS ρ' ρa σ) (ha : τB.P j w' ls' a ρa) :
    C.P j w' ls' (.app (.val κ) (.val a)) σ :=
  h w' ρ' ls' hE hr hk j hj a ρa σ hc ha

/-- **A task at its type is forced at every later world and list keeping the records it reads.** -/
theorem STy.task_force_after {d : Life} {C : SCmp} {force : Val → Expr} {n : Nat} {w w' : TWd}
    {ls : List (SRecT w.K)} {ls' : List (SRecT w'.K)} {t : Val} {ρ : TRes w.K} {ρ' : TRes w'.K}
    (h : (STy.task d C force).P n w ls t ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hk : KeepRel w'.Θ ls ls' ρ) :
    C.P n w' ls' (force t) ρ' :=
  h.1 w' ρ' ls' hE hr hk

/-! ### A captured continuation is a value of its type -/

/-- **A continuation captured at a stop is a value of its type.** The share `ρ` of a stop at the
world `w` and stop list `ls`, owning no records, owing the relation at the table `Tb` and the
result type `A` (`contShareT … (cerwpTC Tb (postOf A) k)`), with `κ` the function whose
application to an answer is the resumed context (`hκ`) and `B` read by the entry's answer
(`hB`): `κ` is a value of `U (B ⊸ F A)` at `w`, `ls`, `ρ` at every index below the stop's, `F A`
at the frame the share resumes at (`fdNil`).

Every type, lifetime and nesting: the proof is the share's own resume (`contShareT_resume`) at
the thunk's quantifier, which is `KeepRel`'s, and one step of `κ`'s application. -/
theorem STy.kont_of_share {Tb : TableT} (hL : Tb.Local) (hTb : Tb.Down) {τ τB : STy}
    {en : OpEntT} {F : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {K : Kont}
    {v κ : Val} {ρ : TRes w.K}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ (K.plug (.val a)))
    (hB : ∀ j (w' : TWd) ls' a σ, τB.P j w' ls' a σ → en.PBv v j w' ls' a σ)
    (h : contShareT en F k w ls [] K v (cerwpTC (ℍ := ℍ) Tb (postOf τ) k) ρ) {n : Nat}
    (hn : n < k) :
    (STy.kont τB (SCmp.ret (ℍ := ℍ) Tb hL hTb (fdNil en v F) τ)).P n w ls κ ρ := by
  intro w' ρ' ls' hE hr hk j hj a ρa σ hc ha
  show cerwpT (ℍ := ℍ) Tb (postOf τ) (fdNil en v F) j w' ls' [] (.app (.val κ) (.val a)) σ
  cases j with
  | zero => exact cerwpT_zero
  | succ j =>
      refine cerwpT_step hL (hκ a) ?_
      have hres := contShareT_resume h hE hr hk List.Forall₂.nil (k' := j) (by omega)
        (hB j w' ls' a ρa (τB.down j w' ls' a ρa ha)) hc
      simp only [cerwpTC, show j < k by omega, if_true, fdAt_nil] at hres
      exact hres

/-- **A captured continuation boxed at a lifetime its share outlives** is a value of `[@d] K`:
BOXED-κ's premise, that the share is in `Res_d` (every borrow cell strictly longer-lived than
`d`), is what the box asks. -/
theorem STy.kontBox_of_share {Tb : TableT} (hL : Tb.Local) (hTb : Tb.Down) {τ τB : STy}
    {en : OpEntT} {F : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {K : Kont}
    {v κ : Val} {ρ : TRes w.K} {d : Life}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ (K.plug (.val a)))
    (hB : ∀ j (w' : TWd) ls' a σ, τB.P j w' ls' a σ → en.PBv v j w' ls' a σ)
    (h : contShareT en F k w ls [] K v (cerwpTC (ℍ := ℍ) Tb (postOf τ) k) ρ)
    (hd : ρ.InStratum (TSet.single d)) {n : Nat} (hn : n < k) :
    (STy.kontBox d τB (SCmp.ret (ℍ := ℍ) Tb hL hTb (fdNil en v F) τ)).P n w ls κ ρ :=
  ⟨STy.kont_of_share hL hTb hκ hB h hn, hd⟩

/-- **The hardest case: a boxed continuation holding a borrow, carried and resumed.** A `κ`
captured at a stop (its share `ρ`, owning no records, at the stop list `ls`), boxed at `d`, is
carried to any extension `w′` of the stop's world, at any list `ls′` there keeping the re-readings
of the records of `ls` the share reads: records of `ls` the share does not read may have been
ended, and records opened since may be added, by other branches. There it is a value of its type
(`[@d] U (B ⊸ F A)` at `w′`, `ls′`), and resuming it at any answer of `B` is a run of `F A`. -/
theorem STy.kontBox_resume_after {Tb : TableT} (hL : Tb.Local) (hTb : Tb.Down) {τ τB : STy}
    {en : OpEntT} {F : TFrame} {k : Nat} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {K : Kont} {v κ : Val} {ρ : TRes w.K} {ρ' : TRes w'.K} {d : Life}
    (hκ : ∀ (a : Val) μ, Step1Only (ℍ := ℍ) μ (.app (.val κ) (.val a)) μ (K.plug (.val a)))
    (hB : ∀ j (w' : TWd) ls' a σ, τB.P j w' ls' a σ → en.PBv v j w' ls' a σ)
    (h : contShareT en F k w ls [] K v (cerwpTC (ℍ := ℍ) Tb (postOf τ) k) ρ)
    (hd : ρ.InStratum (TSet.single d)) (hc : CovR (sem w.Θ) w.K ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hk : KeepRel w'.Θ ls ls' ρ) {n : Nat} (hn : n < k) :
    (STy.kontBox d τB (SCmp.ret (ℍ := ℍ) Tb hL hTb (fdNil en v F) τ)).P n w' ls' κ ρ' ∧
      ∀ (a : Val) (ρa σ : TRes w'.K), ResUT.CompS ρ' ρa σ → τB.P n w' ls' a ρa →
        cerwpT (ℍ := ℍ) Tb (postOf τ) (fdNil en v F) n w' ls' [] (.app (.val κ) (.val a)) σ := by
  have hb := STy.kontBox_of_share hL hTb hκ hB h hd hn
  have hb' := (STy.kontBox d τB _).mono n w w' ls ls' κ ρ ρ' hE hr hk hc hb
  exact ⟨hb', fun a ρa σ hcσ ha => hb.1 w' ρ' ls' hE hr hk n le_rfl a ρa σ hcσ ha⟩

/-! ### Rules out: a continuation stored past its lend -/

/-- **A boxed value holding a view at `α` is not of `[@d] A` unless `d` is strictly below `α`.**
For any `A`, so for a continuation's type: a `κ` whose share holds a view of a lend at `α`, boxed
at the lend's own lifetime or at any lifetime the lend does not outlive, is not a value of its
type, at any index, world or list. A box former that did not read the stratum would admit it. -/
theorem STy.not_box_of_view {d α : Life} {τ : STy} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {v : Val} {ρ : TRes w.K} {l : BoCa.Loc} {i : TImm w.K} (hl : ρ.get l = some (.imm i))
    (hα : α ∈ i.ls.set) (hd : ¬ w.K.lt d α) : ¬ (STy.box d τ).P n w ls v ρ := fun h =>
  hd (h.2 l _ hl d (Finset.mem_singleton_self d) α hα)

/-- The continuation instance: a `κ` boxed past its lend is not of `[@d] U (B ⊸ C)`. -/
theorem STy.not_kontBox_of_view {d α : Life} {τB : STy} {C : SCmp} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {κ : Val} {ρ : TRes w.K} {l : BoCa.Loc} {i : TImm w.K}
    (hl : ρ.get l = some (.imm i)) (hα : α ∈ i.ls.set) (hd : ¬ w.K.lt d α) :
    ¬ (STy.kontBox d τB C).P n w ls κ ρ :=
  STy.not_box_of_view hl hα hd

end BoCa.Fig16.Tree.Wp

end
