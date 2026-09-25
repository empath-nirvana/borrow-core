import Core.Count
import Core.Sized

/-!
# Core — a fuel-free borrowed fold  `[spec §6]`

`countFree = Z (λself. Λ. λl. withload l (Λ. λu. case u {inj₁ w. w; 0 | inj₂ t. self [] t to n.
inj₂ n}))` counts a borrowed list by recursion on the list itself.

The measure is the number of cells in the witness of the borrowed `imm` cell (`dsize`).  A
borrow's witness is finite (`PMap.finite`), and the view `withload` hands its callback is an
image `χ ∈ reb_β(σ)` of the loaded cell's witness `σ`: at the tail `ℓ′`, `reb_β`'s `own` clause
gives `χ(ℓ′) = imm({β}, u, q/ℓ′)` for a piece `q ≤ σ` holding `ℓ′` (`typed_image_pos`), so the
tail's witness `q/ℓ′` has strictly fewer cells than `σ` (`dsize_image_lt`).

`dsize`, `rebChooseTW_sized` and `withload_sized` are in `Sized.lean`.

* `countFree_body`: induction on a bound of `dsize`, the callback proved by hand.  The same
  function through the typing rule `foldImm`, with no hand proof, is `countFoldE`
  (`Folds.lean`).
* `countFree_semV : SemV Δ [] countFree (!U(∀'a. Imm 'a L ⊸ F N))`.
* `countFreeProg`: build a 3-cell list, borrow it, count, end the borrow, free it; it runs from
  the empty memory to a numeral and the empty memory (`countFreeProg_runs`), and the interpreter
  returns `3` with no cell left (`countFreeProg_eval`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The counter -/

/-- A numeral at the relation, holding no resource. -/
theorem vC_num (b : Bool) (ls : List SRec) (δ : LSub) : ∀ k, vC b natN ls δ (num k) PMap.empty
  | 0 => vC_roll natBody_noMut natN_closed (Or.inl ⟨.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩)
  | k + 1 => vC_roll natBody_noMut natN_closed
      (Or.inr ⟨num k, pure_sep_iff.mpr ⟨rfl, vC_num b ls δ k⟩⟩)

/-- The callback at a closed handle `S`:
`Λ. λu. case u {inj₁ w. w; 0 | inj₂ t. S [] t to n. inj₂ n}`. -/
def cbV (S : Val) : Val := .lam (.val (.lam (.case (.var 0)
    (.seq (.var 0) (.inj₁ (.val .unit)))
    (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0))))))

/-- The callback inside `countFree`'s body, the handle `self` at index `5`. -/
def cbFE : Expr := .val (.lam (.val (.lam (.case (.var 0)
    (.seq (.var 0) (.inj₁ (.val .unit)))
    (bindE (.app (.app (.var 5) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))))))

/-- The body of `countFree = Z (λself. λ_. λl. withload l cb)`. -/
def cfB : Expr := .val (.lam (.app (.app withload (.var 0)) cbFE))

theorem cfB_closed : closedAt 2 cfB = true := rfl

/-- `countFree`, a closed λ-value. -/
def countFreeV : Val := fixV cfB

theorem countFreeV_closed : closedAt 0 countFreeV.1 = true := by
  simp [countFreeV, fixV, closedAt]
  rfl

/-- The handle `countFree` recurses through. -/
abbrev selfC : Val := selfV cfB

theorem selfC_closed : closedAt 0 selfC.1 = true := selfV_closed cfB_closed

theorem cbV_closed {S : Val} (hS : closedAt 0 S.1 = true) : closedAt 0 (cbV S).1 = true := by
  simp [cbV, bindE, closedAt, closedAt_mono S.1 hS (Nat.zero_le _)]

/-- `countFree`'s body at `λl`, the handle `S` substituted. -/
def bodyL (S : Val) : Expr := .app (.app withload (.var 0)) (.val (cbV S))

theorem cfB_subst {S : Val} (hS : closedAt 0 S.1 = true) (w : Val) :
    (cfB.subst 1 S).subst 0 w = .val (.lam (bodyL S)) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  have h₃ : ∀ j s, Expr.subst j s withload = withload :=
    fun j s => subst_closedAt withload s withload_closed (Nat.zero_le j)
  simp [cfB, cbFE, bodyL, cbV, bindE, Expr.subst, h₁, h₂, h₃]

theorem bodyL_subst {S : Val} (hS : closedAt 0 S.1 = true) (ℓ : Loc) :
    (bodyL S).subst 0 (.loc ℓ) = .app (.app withload (.val (.loc ℓ))) (.val (cbV S)) := by
  have h₃ : ∀ j s, Expr.subst j s withload = withload :=
    fun j s => subst_closedAt withload s withload_closed (Nat.zero_le j)
  simp [bodyL, Expr.subst, h₃, val_subst_closed (cbV_closed hS)]

/-- The callback applied: `cbV S [] w` reaches `case w {…}`. -/
theorem cbV_app {S : Val} (hS : closedAt 0 S.1 = true) (w : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.case (.val w) (.seq (.var 0) (.inj₁ (.val .unit)))
        (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))) Q)
      (wpTS ls (.app (.app (.val (cbV S)) (.val .unit)) (.val w)) Q) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  intro ρ h
  refine wpTS_beta_in (.appL .hole w) _ Val.unit ls Q ρ ?_
  have e : (Kont.appL .hole w).plug (Expr.subst 0 Val.unit (.val (.lam (.case (.var 0)
      (.seq (.var 0) (.inj₁ (.val .unit)))
      (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))))))
      = .app (.val (.lam (.case (.var 0) (.seq (.var 0) (.inj₁ (.val .unit)))
      (bindE (.app (.app (.val S) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))))) (.val w) := by
    simp [Kont.plug, bindE, Expr.subst, h₂]
  rw [e]
  refine wpTS_lolli _ _ w Q ρ ?_
  simpa [bindE, Expr.subst, h₁, h₂] using h

/-- The borrowed list's cell witness, in the view `withload` hands over: at `inj₂ (ℓ′)` the tail's
witness has fewer cells than the loaded cell's.  `typed_image_pos` at the root `ℓ′` of the
witness `σ`. -/
theorem dsize_image_lt {β : Life} {δ : LSub} {ls : List SRec} {σ χ : WRes} {ℓ' : Loc}
    (hobs : vC false listL ls δ (.inj₂ (.loc ℓ')) σ) (hreb : ResU.Reb β σ χ)
    (hview : vC true (listL.immReborrow (.var 0)) ls (δ.extend 0 β) (.inj₂ (.loc ℓ')) χ) :
    ∀ s u σ' h, χ = ResU.single ℓ' (CellU.immOf s u σ' h) → dsize σ' < dsize σ := by
  intro s u σ' h hχ
  -- the parent's payload: `σ = ℓ′ ↦ own(v″) ● …`
  obtain ⟨-, -, hunr⟩ := vC_mu_iff.mp hobs
  rcases hunr with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
  · have := congrArg Subtype.val (pure_sep_iff.mp hs).1
    simp at this
  obtain ⟨e₂, hr⟩ := pure_sep_iff.mp hs
  have e₂' : v₂ = .loc ℓ' := by
    have := congrArg Subtype.val e₂; exact Val.ext (by simpa using this.symm)
  subst e₂'
  obtain ⟨m, v'', hs'⟩ := hr
  obtain ⟨em, ρa, ρb, hcab, hown, -⟩ := pure_sep_iff.mp hs'
  have em' : m = ℓ' := by
    have := congrArg Subtype.val em; simpa using this.symm
  subst em'
  rw [hown] at hcab
  have hσ : σ.get m = some (CellU.ownOf v'') :=
    (ResU.CompS.get_left_of_ne_imm hcab (ResU.single_get_self m _) (by simp)).2
  -- the view is an image of `σ`: `reb_β`'s `own` clause at `m`
  have hx : ¬ VFree 0 listL := by simp [VFree, listL, listBody]
  obtain ⟨q, hq, eχ, hle, hqm, -⟩ := typed_image_pos (T := listL) (S := listL) hx
    (RefPos.mu listL_closed (RefPos.sumR (RefPos.ref listL m))) hσ hreb
    (vC_vShape true _ hview)
  have eχ' : χ.get m = some (CellU.immOf s u σ' h) := by rw [hχ]; simp
  rw [eχ] at eχ'
  obtain ⟨-, -, hσ'⟩ := CellU.immOf_inj (Option.some.inj eχ')
  rw [← hσ']
  exact dsize_del_lt hle hqm

/-- The postcondition of `F N`. -/
abbrev natQ (δ : LSub) : List SRec → Val → WProp := fun ls' v => vP natN ls' δ v

/-- **The fuel-free count**, by induction on a bound of the borrowed cell's witness size:
`withload ℓ (cbV selfC)` counts the list at any borrow `ℓ : Imm a L`. -/
theorem countFree_body : ∀ (n : Nat) (a : Lifetime.Life) (δ : LSub) (ls : List SRec) (ℓ : Loc)
    (ρ : WRes), vP (.imm a listL) ls δ (.loc ℓ) ρ → WitLt ℓ ρ n →
    wpTS ls (.app (.app withload (.val (.loc ℓ))) (.val (cbV selfC))) (natQ δ) ρ := by
  intro n
  induction n with
  | zero =>
      intro a δ ls ℓ ρ hv hn
      obtain ⟨α₀, -, ℓ', hs⟩ := hv
      obtain ⟨⟨hℓ', -⟩, himm⟩ := pure_sep_iff.mp hs
      obtain ⟨s, u, σ, hσ, hρ, -⟩ := ptoImmO_toImm himm
      exact absurd (hn s u σ hσ (by
        have e : ℓ' = ℓ := by have := congrArg Subtype.val hℓ'; simpa using this.symm
        rw [hρ, e])) (Nat.not_lt_zero _)
  | succ n ih =>
      intro a δ ls ℓ ρ hv hn
      refine withload_sized (T₁ := listL) 0 (by simp [VFree, listL, listBody]) Lifetime.SLife.top
        (fun σ => dsize σ < n + 1) (natQ δ) hv hn (ResU.comp_empty_right ρ) ?_
      intro β w χ ρ' _ hview ⟨σ, hKσ, hobs, hreb⟩ hcomp
      rw [eq_of_compS_empty_left hcomp]
      refine cbV_app selfC_closed w ls _ χ ?_
      -- the view unrolls to `1 ⊕ Imm 'x L`
      have hview' := (vC_immReborrow_mu_iff (A := listBody) ⟨trivial, Nat.zero_lt_one⟩ _ true ls
        (δ.extend 0 β) w χ).mp hview
      rcases hview' with ⟨w₁, hs⟩ | ⟨t, hs⟩
      · -- `inj₁ w. w; 0`
        obtain ⟨rfl, hχ, rfl⟩ := pure_sep_iff.mp hs
        subst hχ
        refine wpTS_sum₁ _ _ _ _ _ _ ?_
        refine wpTS_1 _ _ _ _ ?_
        exact wpTS_val ls (num 0) _ _ ⟨vC_num true ls δ 0, ResU.inStratum_empty β⟩
      · -- `inj₂ t. selfC [] t to n. inj₂ n`
        obtain ⟨rfl, ht⟩ := pure_sep_iff.mp hs
        obtain ⟨ℓ', rfl⟩ : ∃ ℓ', t = Val.loc ℓ' := by
          obtain ⟨α₀, -, ℓ', hs₁⟩ := ht
          exact ⟨ℓ', (pure_sep_iff.mp hs₁).1.1⟩
        have hlt : WitLt ℓ' χ n := fun s u σ' h hχ =>
          lt_of_lt_of_le (dsize_image_lt hobs hreb hview s u σ' h hχ) (Nat.lt_succ_iff.mp hKσ)
        refine wpTS_sum₂ _ _ _ _ _ _ ?_
        have e₂ : (bindE (.app (.app (.val selfC) (.val .unit)) (.var 0)) (.inj₂ (.var 0))).subst 0
            (Val.loc ℓ') = (Kont.appR (.val (.lam (.inj₂ (.var 0)))) .hole).plug
              (.app (.app (.val selfC) (.val .unit)) (.val (.loc ℓ'))) := by
          simp [bindE, Expr.subst, val_subst_closed selfC_closed, Kont.plug]
        rw [e₂]
        refine wpTS_bind _ _ _ _ _ ?_
        refine wpTS_selfV_in cfB_closed (.appL .hole (.loc ℓ')) Val.unit ls _ χ ?_
        rw [fixV_eq cfB_closed]
        refine wpTS_beta_in (.appL .hole (.loc ℓ')) _ Val.unit ls _ χ ?_
        rw [cfB_subst selfC_closed]
        refine wpTS_lolli _ _ _ _ _ ?_
        rw [bodyL_subst selfC_closed]
        refine wpTS_mono (fun ls' v ρ' hv => ?_) χ (ih (.var 0) (δ.extend 0 β) ls ℓ' χ ht hlt)
        obtain ⟨rfl, k, rfl⟩ := vC_natN hv
        refine wpTS_lolli _ _ _ _ _ ?_
        exact wpTS_val ls' (num (k + 1)) _ _ ⟨vC_num true ls' δ (k + 1), ResU.inStratum_empty β⟩

/-- `λl. withload l (cbV selfC)` is a value of `U(Imm 'a L ⊸ F N)` at every `'a`. -/
theorem countFree_lam_vC (δ : LSub) (ls : List SRec) :
    vC true (.lolli (.imm (.var 0) listL) natN) ls δ (.lam (bodyL selfC)) PMap.empty := by
  intro ls₁ _ v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, v = Val.loc ℓ := by
    obtain ⟨α₀, -, ℓ, hs₁⟩ := hv
    exact ⟨ℓ, (pure_sep_iff.mp hs₁).1.1⟩
  refine wpTS_lolli _ _ _ _ _ ?_
  rw [bodyL_subst selfC_closed]
  obtain ⟨n, hn⟩ := witLt_exists hv
  exact countFree_body n (.var 0) δ ls₁ ℓ ρ₁ hv hn

/-- `countFree` is a value of `!U(∀'a. Imm 'a L ⊸ F N)` at `∅`. -/
theorem countFree_vC (δ : LSub) (ls : List SRec) :
    vC true countTy ls δ countFreeV PMap.empty := by
  refine ⟨rfl, ?_⟩
  intro ls₁ _ α ρ₁ ρ₂ hp hc
  obtain ⟨rfl, -⟩ := hp
  rw [eq_of_compS_empty_left hc]
  show wpTS ls₁ (.app (.val countFreeV) (.val .unit)) _ PMap.empty
  rw [countFreeV, fixV_eq cfB_closed]
  refine wpTS_lolli _ _ _ _ _ ?_
  rw [cfB_subst selfC_closed]
  exact wpTS_val _ _ _ _ (countFree_lam_vC _ _)

/-- **`countFree : !U(∀'a. Imm 'a L ⊸ F N)`**, the semantic judgment, with no fuel. -/
theorem countFree_semV {Δ : LifeCtx} : SemV Δ [] (.val countFreeV) countTy :=
  semV_closed countFreeV_closed countFree_vC

/-! ### The program -/

/-- The program, open in `countFree` (index `0`) and `freeAll` (index `1`):

    build3 to lst. alloc lst to r. return countFree to g.
    withbor r (Λ. λb. g [] b to n. n) to p. let (r′, n) = p in
    free r′ to lst′. freeAll lst′ to u. u; n                                            -/
def countFreeProgOpen : Expr :=
  bindE build3 (bindE (.app (.val (.prim .alloc)) (.var 0))
    (bindE (.var 2)
      (bindE (.app (.app withbor (.var 1)) borrowerE)
        (.letpair (.var 0)
          (bindE (.app (.val (.prim .free)) (.var 1))
            (bindE (.app (.var 8) (.var 0)) (.seq (.var 0) (.var 2))))))))

/-- The context of `countFree` and `freeAll`. -/
abbrev ΓC : Ctx VTy := [⟨countTy, true⟩, ⟨.lolli listL .unit, true⟩]

theorem countFreeProg_derives :
    CDerives LifeCtx.empty ΓC countFreeProgOpen (.comp (.ret natN)) := by
  -- `build3 to lst`
  refine .bind (.right (.right .nil)) (.ret (d_build3 (.cons (.cons .nil)))) ?_
  -- `alloc lst to r`
  refine .bind (.left (.right (.right .nil)))
    (.ret (.lolliE (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil))))
      (.alloc (A := listL) (.cons (.cons (.cons .nil)))))) ?_
  -- `return countFree to g`
  refine .bind (.right (.dead (.left (.right .nil))))
    (.ret (.var (.there (.there (.here (.cons .nil)))))) ?_
  -- `withbor r borrower to p`
  refine .bind (.left (.left (.dead (.dead (.right .nil)))))
    (.ret (.lolliE (.left (.right (.dead (.dead (.dead .nil)))))
      (d_borrowerE (by repeat constructor))
      (.lolliE (.dead (.left (.dead (.dead (.dead .nil)))))
        (.var (.there (.here (by repeat constructor))))
        (.withbor1 (A := listL) (B := natN) 0 (by repeat constructor) rfl
          (fun _ h => by simp [VFree, listL, listBody] at h)
          (by simp [VFree, listL, listBody]) (by simp [VFree, natN, natBody]))))) ?_
  -- `let (r′, n) = p in`
  refine .tensorE (A := .ref listL) (B := natN)
    (.left (.dead (.dead (.dead (.dead (.right .nil))))))
    (.var (.here (by repeat constructor))) ?_
  -- `free r′ to lst′`
  refine .bind (.right (.left (.dead (.dead (.dead (.dead (.dead (.right .nil))))))))
    (.ret (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))
      (.var (.there (.here (by repeat constructor))))
      (.free (A := listL) (by repeat constructor)))) ?_
  -- `freeAll lst′ to u`
  refine .bind (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.left .nil)))))))))
    (.ret (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.right .nil)))))))))
      (.var (.here (by repeat constructor)))
      (.var (.there (.there (.there (.there (.there (.there (.there (.there
        (.here .nil)))))))))))) ?_
  -- `u; n`
  exact .unitE (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.var (.here (by repeat constructor)))
    (.ret (.var (.there (.there (.here (by repeat constructor))))))

/-- The program, closed by `countFree` and `freeAll`. -/
def countFreeProg : Expr := substAll [countFreeV, freeAll] countFreeProgOpen

theorem gDenC_C (ls : List SRec) (δ : LSub) : gDenC ls δ ΓC [countFreeV, freeAll] PMap.empty :=
  gDenC_mk (by simp [Ctx.LiveWithin])
    ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, countFree_vC δ ls,
      PMap.empty, PMap.empty, ResU.comp_empty_right _, freeAll_vC δ ls, ⟨rfl, trivial⟩⟩

theorem countFreeProg_wp :
    wpTS [] countFreeProg (fun _ v => Fig16.BoLo.pure (∃ k, v = num k)) (PMap.empty : WRes) := by
  have h := fundamentalC countFreeProg_derives LSub.empty [countFreeV, freeAll] [] PMap.empty
    Adequacy.models_empty (gDenC_C [] LSub.empty)
  refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty h
  obtain ⟨rfl, k, rfl⟩ := vC_natN hv
  exact ⟨rfl, k, rfl⟩

/-- **Adequacy at the fuel-free count**: the program runs from the empty memory to a numeral and
the empty memory. -/
theorem countFreeProg_runs :
    ∃ k, BoCa.BoLo.Steps Adequacy.emptyMem countFreeProg Adequacy.emptyMem (.val (num k)) := by
  obtain ⟨v, hsteps, k, rfl⟩ := theorem32 countFreeProg (fun v => ∃ k, v = num k) countFreeProg_wp
  exact ⟨k, hsteps⟩

/-- The executable interpreter counts `3` and leaves no cell. -/
theorem countFreeProg_eval : numNoLeak (eval countFreeProg) = some 3 := by decide

end BoCa.Fig16.LogRel.Core

end
