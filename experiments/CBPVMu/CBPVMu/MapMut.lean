import CBPVMu.CountFree

/-!
# CBPVMu — an in-place map through a mutable borrow

`L′ = μX. 1 ⊕ Ref (N ⊗ X)`, a boxed list of numerals.  `mapInc : U(L′ ⊸ F L′)` increments
every payload in place — each cell is emptied by `swap`, its tail mapped, and the new pair
swapped back into the same cell — by recursion on the list (`vC_mu_ind`, no fuel).  A cell
holding the list is borrowed mutably (`withbor`), and the callback maps the whole list through
`withswap`.

* `wpTS_swap` (`FoldReuse.lean`): `swap ℓ v` at an owned cell, as a `wpTS` rule (6.169's steps).
* `mapInc_semV : SemV Δ [] mapInc (U(L′ ⊸ F L′))`.
* `toPure : U(L′ ⊸ F P)` frees the list into the pure list `P = μX. 1 ⊕ (N ⊗ X)`.
* `mapProg`: build `[0, 0, 0]`, put it in a cell, borrow it mutably and map it in place with
  `withswap`, end the borrow, free the cell, free the list into a pure list; it runs from the
  empty memory to a pure list and the empty memory (`mapProg_runs`), and the interpreter returns
  `[1, 1, 1]` with no cell left (`mapProg_eval`).

The derived versions are in `CommonList.lean`: over the same list with each node one block
(`μX. 1 ⊕ (Ref N ⊗ Ref X)`), `mapIncCE` and `toPureCE` are `foldOwn` of `CDerives` algebras and
`mapProgC` is one closed derivation, with no hand proof.  `mapInc` here stays the in-place map
(same cells); `mapIncCE` rebuilds the list in fresh blocks.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The types -/

/-- `1 ⊕ Ref (N ⊗ X)`. -/
def listPBody : VTy := .sum .unit (.ref (.tensor natN (.tvar 0)))

/-- `L′ = μX. 1 ⊕ Ref (N ⊗ X)`. -/
def listP : VTy := .mu listPBody

theorem listPBody_noMut : listPBody.NoMut 0 := by simp [listPBody, natN, natBody, VTy.NoMut]

theorem listP_closed : listP.Cl 0 := by
  simp [listP, listPBody, natN, natBody, VTy.Cl]

theorem listP_unroll : VTy.inst listP listPBody = .sum .unit (.ref (.tensor natN listP)) := rfl

/-- `1 ⊕ (N ⊗ X)`. -/
def pureBody : VTy := .sum .unit (.tensor natN (.tvar 0))

/-- `P = μX. 1 ⊕ (N ⊗ X)`, a list of numerals holding no cell. -/
def pureL : VTy := .mu pureBody

theorem pureBody_noMut : pureBody.NoMut 0 := by simp [pureBody, natN, natBody, VTy.NoMut]

theorem pureL_closed : pureL.Cl 0 := by
  simp [pureL, pureBody, natN, natBody, VTy.Cl]

theorem pureL_unroll : VTy.inst pureL pureBody = .sum .unit (.tensor natN pureL) := rfl

/-! ### Sizes and closed values -/

theorem num_closed : ∀ k, closedAt 0 (num k).1 = true
  | 0 => rfl
  | k + 1 => by simpa [num, closedAt] using num_closed k

/-- A value of `L′` is `inj₁ ()` or `inj₂ ℓ`: closed. -/
theorem listP_closedV {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vC b listP ls δ v ρ) : closedAt 0 v.1 = true := by
  obtain ⟨-, -, hu⟩ := vC_mu_iff.mp h
  rcases hu with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
  · obtain ⟨rfl, -, rfl⟩ := pure_sep_iff.mp hs; rfl
  · obtain ⟨rfl, ℓ, v', hs'⟩ := pure_sep_iff.mp hs
    obtain ⟨rfl, -⟩ := pure_sep_iff.mp hs'; rfl

/-! ### `mapInc` -/

/-- `let (r₂, u) = q₂ in u; inj₂ r₂`. -/
def e5 : Expr := .letpair (.var 0) (.seq (.var 0) (.inj₂ (.var 1)))

/-- `swap r₁ (inj₂ p, tl′) to q₂. e5` (`r₁` at `4`, `p` at `2`, `tl′` at `0`). -/
def e4 : Expr := bindE (.app (.app swap (.var 4)) (.pair (.inj₂ (.var 2)) (.var 0))) e5

/-- `f tl to tl′. e4`. -/
def e3 (f : Expr) : Expr := bindE (.app f (.var 0)) e4

/-- `let (r₁, c) = q in let (p, tl) = c in e3`. -/
def e2 (f : Expr) : Expr := .letpair (.var 0) (.letpair (.var 0) (e3 f))

/-- `swap r () to q. e2`. -/
def consE (f : Expr) : Expr := bindE (.app (.app swap (.var 0)) (.val .unit)) (e2 f)

/-- The body of `mapInc = Z (λself. λl. case l {inj₁ u. inj₁ u | inj₂ r. consE})`. -/
def mB : Expr := .case (.var 0) (.inj₁ (.var 0)) (consE (.var 7))

theorem mB_closed : closedAt 2 mB = true := rfl

/-- `mapInc`, a closed λ-value. -/
def mapIncV : Val := fixV mB

theorem mapIncV_closed : closedAt 0 mapIncV.1 = true := by
  simp [mapIncV, fixV, closedAt]
  rfl

abbrev selfMI : Val := selfV mB

theorem selfMI_closed : closedAt 0 selfMI.1 = true := selfV_closed mB_closed

section substs
variable {S : Val} (hS : closedAt 0 S.1 = true)
include hS

theorem mB_subst (w : Val) :
    (mB.subst 1 S).subst 0 w = .case (.val w) (.inj₁ (.var 0)) (consE (.val S)) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  have h₃ : ∀ j s, Expr.subst j s swap = swap :=
    fun j s => subst_closedAt swap s swap_closed (Nat.zero_le j)
  simp [mB, consE, e2, e3, e4, e5, bindE, Expr.subst, h₁, h₂, h₃]

end substs

/-- The postcondition of `F L′`. -/
abbrev listPQ (δ : LSub) : List SRec → Val → WProp := fun ls' v => vP listP ls' δ v

/-- **`mapInc v`** increments every payload of the list `v` in place, at every record list:
induction on a bound of the list's resource size. -/
theorem mapInc_wp : ∀ (n : Nat) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vC true listP ls δ v ρ → dsize ρ < n → ∀ ls',
      wpTS ls' (.app (.val mapIncV) (.val v)) (listPQ δ) ρ := by
  have hS := selfMI_closed
  have h₂ : ∀ j s, Expr.subst j s selfMI.1 = selfMI.1 :=
    fun j s => subst_closedAt _ s hS (Nat.zero_le j)
  have h₃ : ∀ j s, Expr.subst j s swap = swap :=
    fun j s => subst_closedAt swap s swap_closed (Nat.zero_le j)
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro ls δ v ρ hv hn ls'
    rw [mapIncV, fixV_eq mB_closed]
    refine wpTS_lolli _ _ _ _ _ ?_
    rw [mB_subst hS]
    obtain ⟨-, -, hu⟩ := vC_mu_iff.mp hv
    rcases hu with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
    · -- `inj₁ u. inj₁ u`
      obtain ⟨rfl, hρ, rfl⟩ := pure_sep_iff.mp hs
      subst hρ
      refine wpTS_sum₁ _ _ _ _ _ _ ?_
      exact wpTS_val ls' (.inj₁ .unit) _ _ (vC_roll listPBody_noMut listP_closed
        (Or.inl ⟨.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩))
    · obtain ⟨rfl, ℓ, c, hs'⟩ := pure_sep_iff.mp hs
      obtain ⟨rfl, ρ₁, ρ₂, hc, hρ₁, hP⟩ := pure_sep_iff.mp hs'
      subst hρ₁
      obtain ⟨p, tl, hs₃⟩ := hP
      obtain ⟨rfl, ρp, ρt, hcp, hp, htl⟩ := pure_sep_iff.mp hs₃
      obtain ⟨rfl, k, rfl⟩ := vC_natN hp
      have eρ₂ : ρ₂ = ρt := eq_of_compS_empty_left hcp
      subst eρ₂
      have htc := listP_closedV htl
      have hpc := num_closed k
      have hlt : dsize ρ₂ < n := lt_of_lt_of_le
        (dsize_tail_lt hc ⟨PMap.empty, ResU.comp_empty_right _⟩) (Nat.lt_succ_iff.mp hn)
      refine wpTS_sum₂ _ _ _ _ _ _ ?_
      have eA : (consE (.val selfMI)).subst 0 (Val.loc ℓ)
          = (Kont.appR (.val (.lam (e2 (.val selfMI)))) .hole).plug
              (.app (.app swap (.val (.loc ℓ))) (.val .unit)) := by
        simp [consE, e2, e3, e4, e5, bindE, Expr.subst, h₂, h₃, Kont.plug]
      rw [eA]
      refine wpTS_bind _ _ _ _ _ ?_
      refine wpTS_swap ls' ℓ (.pair (num k) tl) .unit _ _ ⟨_, ρ₂, hc, rfl, ?_⟩
      intro ρa ρb hρa hcb
      simp only [Kont.plug]
      refine wpTS_lolli _ _ _ _ _ ?_
      have hq : closedAt 0 (Val.pair (.loc ℓ) (.pair (num k) tl)).1 = true := by
        simp [closedAt, htc, hpc]
      have hq' : closedAt 0 (Val.pair (num k) tl).1 = true := by simp [closedAt, htc, hpc]
      have hpS : ∀ j s, Expr.subst j s (num k).1 = (num k).1 :=
        fun j s => subst_closedAt _ s hpc (Nat.zero_le j)
      have htS : ∀ j s, Expr.subst j s tl.1 = tl.1 :=
        fun j s => subst_closedAt _ s htc (Nat.zero_le j)
      have eB : (e2 (.val selfMI)).subst 0 (Val.pair (.loc ℓ) (.pair (num k) tl))
          = .letpair (.val (Val.pair (.loc ℓ) (.pair (num k) tl)))
              (.letpair (.var 0) (e3 (.val selfMI))) := by
        simp [e2, e3, e4, e5, bindE, Expr.subst, h₂, h₃, val_shift_closed hq]
      rw [eB]
      refine wpTS_tensor ls' (.loc ℓ) (.pair (num k) tl) _ _ ρb ?_
      have eC : ((Expr.letpair (.var 0) (e3 (.val selfMI))).subst 0
            ((Val.pair (num k) tl).shift 1 0)).subst 0 (Val.loc ℓ)
          = .letpair (.val (Val.pair (num k) tl)) (bindE (.app (.val selfMI) (.var 0))
              (bindE (.app (.app swap (.val (.loc ℓ))) (.pair (.inj₂ (.var 2)) (.var 0))) e5)) := by
        simp [e3, e4, e5, bindE, Expr.subst, Expr.shift, h₂, h₃, val_shift_closed hq', hpS, htS]
      rw [eC]
      refine wpTS_tensor ls' (num k) tl _ _ ρb ?_
      have eD : ((bindE (.app (.val selfMI) (.var 0))
              (bindE (.app (.app swap (.val (.loc ℓ))) (.pair (.inj₂ (.var 2)) (.var 0))) e5)).subst
            0 (tl.shift 1 0)).subst 0 (num k)
          = (Kont.appR (.val (.lam (bindE (.app (.app swap (.val (.loc ℓ)))
              (.pair (.inj₂ (.val (num k))) (.var 0))) e5))) .hole).plug
              (.app (.val selfMI) (.val tl)) := by
        simp [e5, bindE, Expr.subst, h₂, h₃, val_shift_closed htc, val_subst_closed htc,
          val_shift_closed hpc, Kont.plug]
      rw [eD]
      refine wpTS_bind_frame _ (.app (.val selfMI) (.val tl)) ls' (listPQ δ)
        (fun _ => ptoOwn ℓ .unit) _ (fun _ _ _ h => h) ?_ ρb
        ⟨ρ₂, ρa, hcb, wpTS_selfV mB_closed tl ls' _ ρ₂ (ih htl hlt ls'), hρa⟩
      rintro ls'' - tl' σ ⟨σ₁, σ₂, hcσ, htl', hσ₂⟩
      subst hσ₂
      simp only [Kont.plug]
      refine wpTS_lolli _ _ _ _ _ ?_
      have htc' := listP_closedV htl'
      have eE : (bindE (.app (.app swap (.val (.loc ℓ))) (.pair (.inj₂ (.val (num k))) (.var 0)))
            e5).subst 0 tl'
          = (Kont.appR (.val (.lam e5)) .hole).plug
              (.app (.app swap (.val (.loc ℓ))) (.val (Val.pair (Val.inj₂ (num k)) tl'))) := by
        simp [e5, bindE, Expr.subst, h₃, hpS, Kont.plug]
      rw [eE]
      refine wpTS_bind _ _ _ _ _ ?_
      refine wpTS_swap ls'' ℓ .unit (.pair (.inj₂ (num k)) tl') _ _
        ⟨_, σ₁, ResU.CompS.comm hcσ, rfl, ?_⟩
      intro ρc ρd hρc hcd
      simp only [Kont.plug]
      refine wpTS_lolli _ _ _ _ _ ?_
      have eF : e5.subst 0 (Val.pair (.loc ℓ) .unit)
          = .letpair (.val (Val.pair (.loc ℓ) .unit)) (.seq (.var 0) (.inj₂ (.var 1))) := by
        simp [e5, Expr.subst]
      rw [eF]
      refine wpTS_tensor ls'' (.loc ℓ) .unit _ _ ρd ?_
      have eG : ((Expr.seq (.var 0) (.inj₂ (.var 1))).subst 0 (Val.unit.shift 1 0)).subst 0
            (Val.loc ℓ) = .seq (.val .unit) (.val (.inj₂ (.loc ℓ))) := by
        simp [Expr.subst, Expr.shift]
      rw [eG]
      refine wpTS_1 _ _ _ _ ?_
      exact wpTS_val ls'' (.inj₂ (.loc ℓ)) _ _ (vC_roll listPBody_noMut listP_closed
        (Or.inr ⟨.loc ℓ, pure_sep_iff.mpr ⟨rfl, ℓ, .pair (num (k + 1)) tl',
          pure_sep_iff.mpr ⟨rfl, ρc, σ₁, ResU.CompS.comm hcd, hρc, num (k + 1), tl',
            pure_sep_iff.mpr ⟨rfl, PMap.empty, σ₁, compS_empty_left σ₁,
              vC_num true ls'' δ (k + 1), htl'⟩⟩⟩⟩))

/-- `mapInc` is a value of `U(L′ ⊸ F L′)` at `∅`. -/
theorem mapInc_vC (δ : LSub) (ls : List SRec) :
    vC true (.lolli listP listP) ls δ mapIncV PMap.empty := by
  intro ls' _ v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  exact mapInc_wp (dsize ρ₁ + 1) hv (Nat.lt_succ_self _) ls'

/-- **`mapInc : U(L′ ⊸ F L′)`**, the semantic judgment, recursion on the list. -/
theorem mapInc_semV {Δ : LifeCtx} : SemV Δ [] (.val mapIncV) (.lolli listP listP) :=
  semV_closed mapIncV_closed mapInc_vC

/-! ### `toPure` -/

/-- `free r to c. let (p, tl) = c in self tl to s. inj₂ (p, s)` (`self` at `5` inside). -/
def tpCons (f : Expr) : Expr :=
  bindE (.app (.val (.prim .free)) (.var 0))
    (.letpair (.var 0) (bindE (.app f (.var 0)) (.inj₂ (.pair (.var 2) (.var 0)))))

/-- The body of `toPure = Z (λself. λl. case l {inj₁ u. inj₁ u | inj₂ r. tpCons})`. -/
def tpB : Expr := .case (.var 0) (.inj₁ (.var 0)) (tpCons (.var 5))

theorem tpB_closed : closedAt 2 tpB = true := rfl

/-- `toPure`, a closed λ-value. -/
def toPureV : Val := fixV tpB

theorem toPureV_closed : closedAt 0 toPureV.1 = true := by
  simp [toPureV, fixV, closedAt]
  rfl

abbrev selfTP : Val := selfV tpB

theorem selfTP_closed : closedAt 0 selfTP.1 = true := selfV_closed tpB_closed

/-- The postcondition of `F P`. -/
abbrev pureQ (δ : LSub) : List SRec → Val → WProp := fun ls' v => vP pureL ls' δ v

/-- **`toPure v`** frees the list `v` into a pure list, at every record list. -/
theorem toPure_wp : ∀ (n : Nat) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vC true listP ls δ v ρ → dsize ρ < n → ∀ ls',
      wpTS ls' (.app (.val toPureV) (.val v)) (pureQ δ) ρ := by
  have hS := selfTP_closed
  have h₁ : ∀ d c, Expr.shift d c selfTP.1 = selfTP.1 :=
    fun d c => shift_closedAt _ d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s selfTP.1 = selfTP.1 :=
    fun j s => subst_closedAt _ s hS (Nat.zero_le j)
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro ls δ v ρ hv hn ls'
    rw [toPureV, fixV_eq tpB_closed]
    refine wpTS_lolli _ _ _ _ _ ?_
    have e₀ : (tpB.subst 1 selfTP).subst 0 v
        = .case (.val v) (.inj₁ (.var 0)) (tpCons (.val selfTP)) := by
      simp [tpB, tpCons, bindE, Expr.subst, h₁, h₂]
    rw [e₀]
    obtain ⟨-, -, hu⟩ := vC_mu_iff.mp hv
    rcases hu with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
    · obtain ⟨rfl, hρ, rfl⟩ := pure_sep_iff.mp hs
      subst hρ
      refine wpTS_sum₁ _ _ _ _ _ _ ?_
      exact wpTS_val ls' (.inj₁ .unit) _ _ (vC_roll pureBody_noMut pureL_closed
        (Or.inl ⟨.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩))
    · obtain ⟨rfl, ℓ, c, hs'⟩ := pure_sep_iff.mp hs
      obtain ⟨rfl, ρ₁, ρ₂, hc, hρ₁, hP⟩ := pure_sep_iff.mp hs'
      subst hρ₁
      obtain ⟨p, tl, hs₃⟩ := hP
      obtain ⟨rfl, ρp, ρt, hcp, hp, htl⟩ := pure_sep_iff.mp hs₃
      obtain ⟨rfl, k, rfl⟩ := vC_natN hp
      have eρ₂ : ρ₂ = ρt := eq_of_compS_empty_left hcp
      subst eρ₂
      have htc := listP_closedV htl
      have hpc := num_closed k
      have hpS : ∀ j s, Expr.subst j s (num k).1 = (num k).1 :=
        fun j s => subst_closedAt _ s hpc (Nat.zero_le j)
      have hq' : closedAt 0 (Val.pair (num k) tl).1 = true := by simp [closedAt, htc, hpc]
      have hlt : dsize ρ₂ < n := lt_of_lt_of_le
        (dsize_tail_lt hc ⟨PMap.empty, ResU.comp_empty_right _⟩) (Nat.lt_succ_iff.mp hn)
      refine wpTS_sum₂ _ _ _ _ _ _ ?_
      have eA : (tpCons (.val selfTP)).subst 0 (Val.loc ℓ)
          = (Kont.appR (.val (.lam (.letpair (.var 0) (bindE (.app (.val selfTP) (.var 0))
              (.inj₂ (.pair (.var 2) (.var 0))))))) .hole).plug
              (.app (.val (.prim .free)) (.val (.loc ℓ))) := by
        simp [tpCons, bindE, Expr.subst, h₂, Kont.plug]
      rw [eA]
      refine wpTS_bind _ _ _ _ _ ?_
      refine wpTS_free ls' ℓ (.pair (num k) tl) _ _ ⟨_, ρ₂, hc, rfl, ?_⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ _ _ _ ?_
      have eB : (Expr.letpair (.var 0) (bindE (.app (.val selfTP) (.var 0))
            (.inj₂ (.pair (.var 2) (.var 0))))).subst 0 (Val.pair (num k) tl)
          = .letpair (.val (Val.pair (num k) tl)) (bindE (.app (.val selfTP) (.var 0))
            (.inj₂ (.pair (.var 2) (.var 0)))) := by
        simp [bindE, Expr.subst, h₂, val_shift_closed hq']
      rw [eB]
      refine wpTS_tensor ls' (num k) tl _ _ ρ₂ ?_
      have eC : ((bindE (.app (.val selfTP) (.var 0)) (.inj₂ (.pair (.var 2) (.var 0)))).subst 0
            (tl.shift 1 0)).subst 0 (num k)
          = (Kont.appR (.val (.lam (.inj₂ (.pair (.val (num k)) (.var 0))))) .hole).plug
              (.app (.val selfTP) (.val tl)) := by
        simp [bindE, Expr.subst, h₂, val_shift_closed htc, val_subst_closed htc,
          val_shift_closed hpc, Kont.plug]
      rw [eC]
      refine wpTS_bind _ _ _ _ _ ?_
      refine wpTS_mono (fun ls'' s ρ' hs => ?_) ρ₂
        (wpTS_selfV tpB_closed tl ls' _ ρ₂ (ih htl hlt ls'))
      refine wpTS_lolli _ _ _ _ _ ?_
      have eD : (Expr.inj₂ (.pair (.val (num k)) (.var 0))).subst 0 s
          = .val (Val.inj₂ (Val.pair (num k) s)) := by
        simp [Expr.subst, hpS]
      rw [eD]
      exact wpTS_val ls'' _ _ _ (vC_roll pureBody_noMut pureL_closed
        (Or.inr ⟨.pair (num k) s, pure_sep_iff.mpr ⟨rfl, num k, s,
          pure_sep_iff.mpr ⟨rfl, PMap.empty, ρ', compS_empty_left ρ', vC_num true ls'' δ k, hs⟩⟩⟩))

/-- `toPure` is a value of `U(L′ ⊸ F P)` at `∅`. -/
theorem toPure_vC (δ : LSub) (ls : List SRec) :
    vC true (.lolli listP pureL) ls δ toPureV PMap.empty := by
  intro ls' _ v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  exact toPure_wp (dsize ρ₁ + 1) hv (Nat.lt_succ_self _) ls'

/-- A pure list holds no resource: induction on the value's size. -/
theorem vC_pureL_empty : ∀ (n : Nat) {b : Bool} {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes}, sizeOf v.1 < n → vC b pureL ls δ v ρ → ρ = PMap.empty := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro b ls δ v ρ hn hv
    obtain ⟨-, -, hu⟩ := vC_mu_iff.mp hv
    rcases hu with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
    · exact (pure_sep_iff.mp hs).2.1
    · obtain ⟨rfl, p, s, hs'⟩ := pure_sep_iff.mp hs
      obtain ⟨rfl, ρp, ρs, hc, hp, hsv⟩ := pure_sep_iff.mp hs'
      obtain ⟨rfl, -⟩ := vC_natN hp
      have hsz : sizeOf s.1 < n := by
        have : sizeOf s.1 < sizeOf (Val.inj₂ (Val.pair p s)).1 := by
          show sizeOf s.1 < sizeOf (Expr.inj₂ (Expr.pair p.1 s.1))
          simp only [Expr.inj₂.sizeOf_spec, Expr.pair.sizeOf_spec]; omega
        omega
      rw [eq_of_compS_empty_left hc]
      exact ih hsz hsv

/-! ### The program -/

/-- `inj₂ (alloc (0, e))`. -/
def consP (e : Expr) : Expr := .inj₂ (.app (.val (.prim .alloc)) (.pair (.val (num 0)) e))

theorem d_consP {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} (hΓ : Ctx.Dead Γ)
    (h : CDerives Δ Γ e (.val listP)) : CDerives Δ Γ (consP e) (.val listP) :=
  .roll listPBody_noMut listP_closed
    (.sumI₂ (.lolliE (deadSplit hΓ) (.tensorI (deadSplit hΓ) (d_num hΓ 0) h) (.alloc hΓ)))

/-- `[0, 0, 0]`. -/
def build0s : Expr := consP (consP (consP (.inj₁ (.val .unit))))

theorem d_build0s {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ build0s (.val listP) :=
  d_consP hΓ (d_consP hΓ (d_consP hΓ
    (.roll listPBody_noMut listP_closed (.sumI₁ (.unitI hΓ)))))

/-- `λl. mapInc l to l′. (l′, ())`, `mapInc` at index `5`. -/
def fME : Expr := .val (.lam (bindE (.app (.var 5) (.var 0)) (.pair (.var 0) (.val .unit))))

/-- The borrower, `mapInc` at index `2`:
`Λ. λb. withswap b fM to q. let (b′, u) = q in u; forget b′; ()`. -/
def borrowerM : Expr := .val (.lam (.val (.lam
  (bindE (.app (.app withswap (.var 0)) fME)
    (.letpair (.var 0) (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit))))))))

theorem listP_outlives (Δ : LifeCtx) (a : Lifetime.Life) : VOutlives Δ a listP :=
  .mu (.sum .unit (.ref (.tensor (natN_outlives _ _) .tvar)))

theorem d_borrowerM :
    CDerives LifeCtx.empty [⟨.ref listP, false⟩, ⟨listP, false⟩, ⟨.lolli listP listP, true⟩,
      ⟨.lolli listP pureL, false⟩] borrowerM
      (.val (VTy.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) listP) (.box (.var 0) .unit)))) := by
  refine .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy) ?_
    (.ret (.thunkV rfl (.lam ?_))))
  · intro s hs hl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact absurd hl (by simp)
    · exact absurd hl (by simp)
    · simp [VFree, CFree, listP, listPBody, natN, natBody]
    · exact absurd hl (by simp)
  refine .bind (A := .tensor (.mut (.var 0) listP) .unit)
    (.left (.dead (.dead (.dead (.left (.dead .nil)))))) ?_ ?_
  · refine .ret (.lolliE (.right (.dead (.dead (.dead (.left (.dead .nil)))))) ?_
      (.lolliE (.left (.dead (.dead (.dead (.dead (.dead .nil))))))
        (.var (.here (by repeat constructor)))
        (.withswap (a := .var 0) (A := listP) (B := .unit) (by repeat constructor))))
    refine .thunkV rfl (.lam (.bind (A := listP) (.left (.dead (.dead (.dead (.dead (.left (.dead .nil))))))) ?_ ?_))
    · exact .ret (.lolliE (.left (.dead (.dead (.dead (.dead (.right (.dead .nil)))))))
        (.var (.here (by repeat constructor)))
        (.var (.there (.there (.there (.there (.there (.here (by repeat constructor)))))))))
    · exact .ret (.tensorI (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))
        (.var (.here (by repeat constructor))) (.unitI (by repeat constructor)))
  · refine .tensorE (A := .mut (.var 0) listP) (B := .unit)
      (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))) (.var (.here (by repeat constructor))) ?_
    refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
      (.var (.here (by repeat constructor))) ?_
    refine .unitE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
      (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
        (.var (.there (.here (by repeat constructor))))
        (.forgetMut (a := .var 0) (A := listP) (by repeat constructor))) ?_
    exact .ret (.boxI (.unitI (by repeat constructor))
      ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by repeat constructor)⟩)

/-- The program, open in `mapInc` (index `0`) and `toPure` (index `1`):

    build0s to lst. alloc lst to r.
    withbor r (Λ. λb. withswap b (λl. mapInc l to l′. (l′, ())) to q.
                     let (b′, u) = q in u; forget b′; ()) to p.
    let (r′, u) = p in u; free r′ to lst′. toPure lst′                                   -/
def mapProgOpen : Expr :=
  bindE build0s (bindE (.app (.val (.prim .alloc)) (.var 0))
    (bindE (.app (.app withbor (.var 0)) borrowerM)
      (.letpair (.var 0) (.seq (.var 0)
        (bindE (.app (.val (.prim .free)) (.var 1)) (.app (.var 7) (.var 0)))))))

/-- The context of `mapInc` and `toPure`. -/
abbrev ΓM : Ctx VTy := [⟨.lolli listP listP, true⟩, ⟨.lolli listP pureL, true⟩]

theorem mapProg_derives : CDerives LifeCtx.empty ΓM mapProgOpen (.comp (.ret pureL)) := by
  refine .bind (.right (.right .nil)) (.ret (d_build0s (by repeat constructor))) ?_
  refine .bind (.left (.right (.right .nil)))
    (.ret (.lolliE (.left (.dead (.dead .nil))) (.var (.here (by repeat constructor)))
      (.alloc (A := listP) (by repeat constructor)))) ?_
  refine .bind (.left (.dead (.left (.right .nil))))
    (.ret (.lolliE (.right (.dead (.left (.dead .nil)))) d_borrowerM
      (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (by repeat constructor)))
        (.withbor2 (A := listP) (B := .unit) 0 (by repeat constructor) rfl
          ⟨LifeCtx.empty.meetOfDom, LifeCtx.defines_of_wf rfl, listP_outlives _ _⟩
          (by simp [VFree, listP, listPBody, natN, natBody]) (by simp [VFree]))))) ?_
  refine .tensorE (A := .ref listP) (B := .unit) (.left (.dead (.dead (.dead (.right .nil)))))
    (.var (.here (by repeat constructor))) ?_
  refine .unitE (.left (.right (.dead (.dead (.dead (.dead (.right .nil)))))))
    (.var (.here (by repeat constructor))) ?_
  refine .bind (.dead (.left (.dead (.dead (.dead (.dead (.right .nil)))))))
    (.ret (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead .nil)))))))
      (.var (.there (.here (by repeat constructor)))) (.free (A := listP) (by repeat constructor)))) ?_
  exact .ret (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead (.right .nil))))))))
    (.var (.here (by repeat constructor)))
    (.var (.there (.there (.there (.there (.there (.there (.there (.here .nil))))))))))

/-- The program, closed by `mapInc` and `toPure`. -/
def mapProg : Expr := substAll [mapIncV, toPureV] mapProgOpen

theorem gDenC_M (ls : List SRec) (δ : LSub) : gDenC ls δ ΓM [mapIncV, toPureV] PMap.empty :=
  gDenC_mk (by simp [Ctx.LiveWithin])
    ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, mapInc_vC δ ls,
      PMap.empty, PMap.empty, ResU.comp_empty_right _, toPure_vC δ ls, ⟨rfl, trivial⟩⟩

/-- A value of `P` from the program's run. -/
def PureOut (v : Val) : Prop := ∃ b ls δ, vC b pureL ls δ v PMap.empty

theorem mapProg_wp :
    wpTS [] mapProg (fun _ v => Fig16.BoLo.pure (PureOut v)) (PMap.empty : WRes) := by
  have h := fundamentalC mapProg_derives LSub.empty [mapIncV, toPureV] [] PMap.empty
    Adequacy.models_empty (gDenC_M [] LSub.empty)
  refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty h
  have e := vC_pureL_empty (sizeOf v.1 + 1) (Nat.lt_succ_self _) hv
  subst e
  exact ⟨rfl, true, ls, LSub.empty, hv⟩

/-- **Adequacy at the in-place map**: the program runs from the empty memory to a pure list and
the empty memory. -/
theorem mapProg_runs :
    ∃ v, PureOut v ∧ BoCa.BoLo.Steps Adequacy.emptyMem mapProg Adequacy.emptyMem (.val v) := by
  obtain ⟨v, hsteps, hv⟩ := theorem32 mapProg PureOut mapProg_wp
  exact ⟨v, hv, hsteps⟩

/-- The numerals of a pure list, if the expression is one. -/
def pureOf : Expr → Option (List Nat)
  | .inj₁ .unit => some []
  | .inj₂ (.pair p s) => do
      let k ← numOf p
      let ks ← pureOf s
      pure (k :: ks)
  | _ => none

/-- The value's numerals, when the run ends with no cell left. -/
def pureNoLeak : Outcome → Option (List Nat)
  | .value v false => pureOf v.1
  | _ => none

/-- The executable interpreter returns `[1, 1, 1]` and leaves no cell. -/
theorem mapProg_eval : pureNoLeak (eval mapProg) = some [1, 1, 1] := by decide

end BoCa.Fig16.LogRel.CBPVMu

end
