import CBPVMu.Lists

/-!
# CBPVMu — a borrowed traversal of the boxed list

`N = μX. 1 ⊕ X` (unary numerals) and `count : U(∀'a. Imm 'a L ⊸ F N)` count the cells of a
list through an immutable borrow.  `count` loads the head with `withload`; the callback, at a
fresh `'x ⊏ 'a`, receives `Imm̲ 'x L = μY. 1 ⊕ Imm 'x L`, unrolls it, and at `inj₂ t` recurses on
the tail borrow `t : Imm 'x L`.

The recursion is on a fuel `k : N`, not on the list: `countN = Z (λself. λk. case k {…})`
returns, at fuel `k + 1`, a `!`-closure that calls the fuel-`k` counter inside its callback.
Each stage — `c₀` at fuel `0` (`d_c₀`) and the step at a counter `g` (`d_step`) — is a
`CDerives` derivation; `countN_wp` is induction on the fuel.

* `vC_natN`: a numeral holds no resource.
* `countN_semV`: `countN : U(N ⊸ F (!U(∀'a. Imm 'a L ⊸ F N)))`.
* `countProg`: build a 3-cell list, put it in a cell, borrow the cell immutably, count with
  fuel `3` inside the borrow, end the borrow, free the cell and the list, return the count.
  It derives at `F N` in the context `countN, freeAll` (`countProg_derives`); instantiated at
  the two recursive values it runs from the empty memory to a numeral and the empty memory
  (`countProg_runs`), and the interpreter returns `3` with no cell left (`countProg_eval`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVMu
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Numerals -/

/-- `1 ⊕ X`. -/
def natBody : VTy := .sum .unit (.tvar 0)

/-- `N = μX. 1 ⊕ X`. -/
def natN : VTy := .mu natBody

theorem natBody_noMut : natBody.NoMut 0 := ⟨trivial, trivial⟩

theorem natN_closed : natN.Cl 0 := ⟨trivial, Nat.zero_lt_one⟩

theorem natN_outlives (Δ : LifeCtx) (a : Lifetime.Life) : VOutlives Δ a natN :=
  .mu (.sum .unit .tvar)

/-- The numeral `k`. -/
def num : Nat → Val
  | 0 => Val.inj₁ Val.unit
  | k + 1 => Val.inj₂ (num k)

theorem d_num {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ∀ k, CDerives Δ Γ (.val (num k)) (.val natN)
  | 0 => .roll natBody_noMut natN_closed (.sumI₁ (.unitI hΓ))
  | k + 1 => .roll natBody_noMut natN_closed (.sumI₂ (d_num hΓ k))

/-- A value of `N` is a numeral and holds no resource: induction on the least fixed point. -/
theorem vC_natN {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vC b natN ls δ v ρ) : ρ = PMap.empty ∧ ∃ k, v = num k := by
  refine vC_mu_ind (A := natBody) (δ := δ) (fun _ _ v ρ => ρ = PMap.empty ∧ ∃ k, v = num k) ?_
    b ls v ρ h
  rintro b ls v ρ - - (⟨v₁, hs⟩ | ⟨v₂, hs⟩)
  · obtain ⟨rfl, hρ, rfl⟩ := pure_sep_iff.mp hs
    exact ⟨hρ, 0, rfl⟩
  · obtain ⟨rfl, hG⟩ := pure_sep_iff.mp hs
    obtain ⟨hρ, k, rfl⟩ := hG.2
    exact ⟨hρ, k + 1, rfl⟩

/-! ### The counter's type and its stages -/

/-- `∀'a ⊏ ⊤. Imm 'a L ⊸ F N`, as a value type. -/
abbrev countFn : VTy := VTy.all 0 LifeCtx.empty.meetOfDom (VTy.lolli (.imm (.var 0) listL) natN)

/-- `!U(∀'a ⊏ ⊤. Imm 'a L ⊸ F N)`. -/
abbrev countTy : VTy := .bang countFn

/-- The callback's type, `∀'x ⊏ 'a ⊓ ⊤. Imm̲ 'x L ⊸ ['x] N`. -/
abbrev cbTy : VTy :=
  VTy.all 1 Δ₁.meetOfDom (VTy.lolli (listL.immReborrow (.var 1)) (.box (.var 1) natN))

/-- `Δ₂ = 'a ⊏ ⊤, 'x ⊏ 'a ⊓ ⊤`: the callback's lifetime context. -/
abbrev Δ₂ : LifeCtx := Δ₁.extend 1 Δ₁.meetOfDom

/-- The load's lifetime is below `⊤`. -/
theorem entails_x_top : LifeCtx.EntailsLt Δ₂ (.var 1) LifeCtx.empty.meetOfDom := fun δ hδ => by
  obtain ⟨m, n, hm, -, hlt⟩ := hδ 1 _ rfl
  exact ⟨m, 0, hm, rfl, by simp only [Lifetime.SLife.Lt] at hlt ⊢; omega⟩

theorem persistent_cons {A : VTy} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    Persistent (⟨.bang A, true⟩ :: Γ) := by
  intro s hs hl
  cases hs with
  | head => exact ⟨A, rfl⟩
  | tail _ hs' => exact dead_noLive (P := fun s => ∃ A, s.ty = .bang A) hΓ s hs' hl

theorem persistent_dead {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) : Persistent Γ :=
  dead_noLive (P := fun s => ∃ A, s.ty = .bang A) hΓ

/-- The counter at fuel `0`: `Λ. λl. forget l; 0`. -/
def c₀V : Val := .lam (.val (.lam (.seq (.app forget (.var 0)) (.inj₁ (.val .unit)))))

theorem d_c₀ {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val c₀V) (.val countTy) :=
  .bangThunkV (persistent_dead hΓ) rfl
    (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
      (dead_noLive hΓ)
      (.ret (.thunkV rfl (.lam
        (.unitE (.left (.dead (deadSplit hΓ)))
          (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
            (.forgetImm (.cons (.cons hΓ))))
          (.ret (.roll natBody_noMut natN_closed (.sumI₁ (.unitI (.cons (.cons hΓ)))))))))))

/-- The callback at a counter `g` (index `4`):
`Λ. λu. case u {inj₁ w. w; forget g; 0 | inj₂ t. g [] t to n. inj₂ n}`. -/
def cbE : Expr := .val (.lam (.val (.lam (.case (.var 0)
    (.seq (.var 0) (.seq (.app forget (.var 5)) (.inj₁ (.val .unit))))
    (bindE (.app (.app (.var 5) (.val .unit)) (.var 0)) (.inj₂ (.var 0)))))))

theorem d_cb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ (⟨.imm (.var 0) listL, false⟩ :: ⟨.unit, false⟩ :: ⟨countTy, true⟩ :: Γ) cbE
      (.val cbTy) := by
  have hd : ∀ {T : VTy} {Γ' : Ctx VTy}, Ctx.Dead Γ' → Ctx.Dead (⟨T, false⟩ :: Γ') :=
    fun h => .cons h
  refine .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ hy => LifeCtx.Ok.bound_mentions_false (Δ := Δ₁) (by decide) rfl hy) ?_
    (.ret (.thunkV rfl (.lam ?_))))
  · intro s hs hl
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · exact absurd hl (by simp)
    · exact absurd hl (by simp)
    · simp [VFree, CFree, Lifetime.Life.mentions, listL, listBody, natN, natBody]; rfl
    · exact dead_noLive (P := fun s => ¬ VFree 1 s.ty) hΓ s hs hl
  refine .sumE (A := .unit) (B := .imm (.var 1) listL)
    (.left (.dead (.dead (.dead (.right (deadSplit hΓ))))))
    (.unroll (A := VTy.immG (.var 1) (VTy.scons listL .tvar) listBody)
      (.var (.here (hd (hd (hd (hd hΓ)))))))
    ?_ ?_
  · -- `inj₁ w. w; forget g; 0`
    refine .unitE (.left (.dead (.dead (.dead (.dead (.right (deadSplit hΓ)))))))
      (.var (.here (hd (hd (hd (hd (hd hΓ))))))) ?_
    refine .unitE (.dead (.dead (.dead (.dead (.dead (.left (deadSplit hΓ)))))))
      (.lolliE (.dead (.dead (.dead (.dead (.dead (.left (deadSplit hΓ)))))))
        (.var (.there (.there (.there (.there (.there (.here hΓ)))))))
        (.forgetBang (A := countFn) (hd (hd (hd (hd (hd (hd hΓ))))))))
      ?_
    exact .ret (.boxI (.roll natBody_noMut natN_closed
      (.sumI₁ (.unitI (hd (hd (hd (hd (hd (hd hΓ))))))))) ⟨LifeCtx.defines_of_wf rfl,
        dead_noLive (P := fun s => VOutlives Δ₂ (.var 1) s.ty) (hd (hd (hd (hd (hd (hd hΓ))))))⟩)
  · -- `inj₂ t. g [] t to n. inj₂ n`
    refine .bind (.left (.dead (.dead (.dead (.dead (.left (deadSplit hΓ)))))))
      (.ret (.lolliE (.left (.dead (.dead (.dead (.dead (.right (deadSplit hΓ)))))))
        (.var (.here (hd (hd (hd (hd (hd hΓ)))))))
        (show CDerives Δ₂ _ _ (.val (.lolli (.imm (.var 1) listL) natN)) from
          .allEV (x := 0) (b := LifeCtx.empty.meetOfDom) (a := .var 1)
            (A := VTy.lolli (.imm (.var 0) listL) natN)
            (.bangE (.var (.there (.there (.there (.there (.there (.here hΓ))))))))
            entails_x_top)))
      ?_
    exact .ret (.boxI (.roll natBody_noMut natN_closed
      (.sumI₂ (.var (.here (hd (hd (hd (hd (hd (hd hΓ))))))))))
      (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) (natN_outlives _ _)
        (hd (hd (hd (hd (hd (hd hΓ))))))))

/-- The counter at fuel `k + 1` from the counter `g` at fuel `k` (index `0`):
`Λ. λl. withload l cb`. -/
def stepV : Val := .lam (.val (.lam (.app (.app withload (.var 0)) cbE)))

theorem d_step {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty (⟨countTy, true⟩ :: Γ) (.val stepV) (.val countTy) := by
  refine .bangThunkV (persistent_cons hΓ) rfl
    (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy) ?_
      (.ret (.thunkV rfl (.lam (.ret ?_)))))
  · intro s hs hl
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · simp [VFree, CFree, Lifetime.Life.mentions]; rfl
    · exact dead_noLive (P := fun s => ¬ VFree 0 s.ty) hΓ s hs hl
  exact .lolliE (.right (.dead (.left (deadSplit hΓ)))) (d_cb hΓ)
    (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
      (.withload (a := .var 0) (A := listL) (B := natN) 1 (.cons (.cons (.cons hΓ))) rfl
        (by simp [VFree, listL, listBody]) (by simp [VFree, natN, natBody])))

/-! ### The counter at every fuel -/

/-- The body of `countN = Z (λself. λk. case k {inj₁ _. c₀ | inj₂ k′. self k′ to g. step[g]})`. -/
def countNB : Expr := .case (.var 0) (.val c₀V) (bindE (.app (.var 2) (.var 0)) (.val stepV))

theorem c₀V_closed : closedAt 0 c₀V.1 = true := rfl

theorem stepV_closed : closedAt 1 stepV.1 = true := rfl

theorem countNB_closed : closedAt 2 countNB = true := rfl

/-- `countN`, a closed λ-value. -/
def countNV : Val := fixV countNB

theorem countNV_closed : closedAt 0 countNV.1 = true := by
  simp [countNV, fixV, closedAt]
  rfl

/-- `countNB[S/self][w/k]` for a closed handle `S`. -/
theorem countNB_subst {S : Val} (hS : closedAt 0 S.1 = true) (w : Val) :
    (countNB.subst 1 S).subst 0 w
      = .case (.val w) (.val c₀V) (bindE (.app (.val S) (.var 0)) (.val stepV)) := by
  have h₁ : ∀ d c, Expr.shift d c S.1 = S.1 := fun d c => shift_closedAt S.1 d hS (Nat.zero_le c)
  have h₂ : ∀ j s, Expr.subst j s S.1 = S.1 := fun j s => subst_closedAt S.1 s hS (Nat.zero_le j)
  have h₃ : ∀ j s, Expr.subst j s c₀V.1 = c₀V.1 :=
    fun j s => subst_closedAt c₀V.1 s c₀V_closed (Nat.zero_le j)
  have h₄ : ∀ j s, Expr.subst (j + 1) s stepV.1 = stepV.1 :=
    fun j s => subst_closedAt stepV.1 s stepV_closed (Nat.le_add_left 1 j)
  simp [countNB, bindE, Expr.subst, h₁, h₂, h₃, h₄]

theorem models_empty_any (δ : LSub) : LifeCtx.empty.Models δ := fun _ _ h => by
  simp [LifeCtx.find?, LifeCtx.empty, Lifetime.assocFind] at h

theorem substAll_single (w : Val) (e : Expr) : substAll [w] e = e.subst 0 w := by
  rw [substAll, Expr.psub_cons, Adequacy.psub_nil, Val.shift_zero]

/-- **The counter at fuel `k`** is a value of `!U(∀'a. Imm 'a L ⊸ F N)`: induction on `k`, the
stages typed by `d_c₀` and `d_step` through `fundamentalC`. -/
theorem countN_wp : ∀ (k : Nat) (ls : List SRec) (δ : LSub),
    wpTS ls (.app (.val countNV) (.val (num k))) (fun ls' w => vC true countTy ls' δ w)
      PMap.empty := by
  have hS := selfV_closed countNB_closed
  intro k
  induction k with
  | zero =>
      intro ls δ
      rw [countNV, fixV_eq countNB_closed]
      refine wpTS_lolli _ _ _ _ _ ?_
      rw [countNB_subst hS]
      refine wpTS_sum₁ _ _ _ _ _ _ ?_
      rw [show (Expr.val c₀V).subst 0 Val.unit = .val c₀V from
        subst_closedAt c₀V.1 _ c₀V_closed (Nat.zero_le 0)]
      have := fundamentalC (d_c₀ .nil) δ [] ls PMap.empty (models_empty_any δ) (gDenC_nil ls δ)
      rwa [show substAll [] (.val c₀V) = .val c₀V from Adequacy.psub_nil 0 _] at this
  | succ k ih =>
      intro ls δ
      rw [countNV, fixV_eq countNB_closed]
      refine wpTS_lolli _ _ _ _ _ ?_
      rw [countNB_subst hS]
      refine wpTS_sum₂ _ _ _ _ _ _ ?_
      have e₂ : (bindE (.app (.val (selfV countNB)) (.var 0)) (.val stepV)).subst 0 (num k)
          = (Kont.appR (.val (.lam (.val stepV))) .hole).plug
              (.app (.val (selfV countNB)) (.val (num k))) := by
        have h₄ : ∀ s : Val, Expr.subst 1 s stepV.1 = stepV.1 :=
          fun s => subst_closedAt stepV.1 s stepV_closed le_rfl
        simp [bindE, Expr.subst, val_subst_closed hS, Kont.plug, h₄]
      rw [e₂]
      refine wpTS_bind _ _ _ _ _ ?_
      refine wpTS_selfV countNB_closed (num k) ls _ PMap.empty ?_
      have := ih ls δ
      rw [countNV] at this
      refine wpTS_mono (fun ls' w ρ' hw => ?_) PMap.empty this
      show wpTS ls' (.app (.val (.lam (.val stepV))) (.val w)) _ ρ'
      refine wpTS_lolli _ _ _ _ _ ?_
      have hg : gDenC ls' δ [⟨countTy, true⟩] [w] ρ' :=
        gDenC_mk (by simp [Ctx.LiveWithin]) ⟨ρ', PMap.empty, ResU.comp_empty_right ρ', hw,
          ⟨rfl, trivial⟩⟩
      have := fundamentalC (d_step .nil) δ [w] ls' ρ' (models_empty_any δ) hg
      rwa [substAll_single] at this

/-- `countN` is a value of `U(N ⊸ F (!U(∀'a. Imm 'a L ⊸ F N)))` at `∅`. -/
theorem countN_vC (δ : LSub) (ls : List SRec) :
    vC true (.lolli natN countTy) ls δ countNV PMap.empty := by
  intro ls' _ v ρ₁ ρ₂ hv hc
  obtain ⟨rfl, k, rfl⟩ := vC_natN hv
  rw [eq_of_compS_empty_left hc]
  exact countN_wp k ls' δ

/-- **`countN : U(N ⊸ F (!U(∀'a. Imm 'a L ⊸ F N)))`**, the semantic judgment. -/
theorem countN_semV {Δ : LifeCtx} : SemV Δ [] (.val countNV) (.lolli natN countTy) :=
  semV_closed countNV_closed countN_vC

/-! ### The program -/

/-- The borrower at a counter `g` (index `0`): `Λ. λb. g [] b to n. n`. -/
def borrowerE : Expr :=
  .val (.lam (.val (.lam (bindE (.app (.app (.var 2) (.val .unit)) (.var 0)) (.var 0)))))

theorem d_borrowerE {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty (⟨countTy, true⟩ :: Γ) borrowerE
      (.val (VTy.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.imm (.var 0) listL) (.box (.var 0) natN)))) := by
  refine .thunkV rfl (.allI (S := .unit) rfl
    (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy) ?_
    (.ret (.thunkV rfl (.lam ?_))))
  · intro s hs hl
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · simp [VFree, CFree, Lifetime.Life.mentions]; rfl
    · exact dead_noLive (P := fun s => ¬ VFree 0 s.ty) hΓ s hs hl
  exact .bind (.left (.dead (.left (deadSplit hΓ))))
    (.ret (.lolliE (.left (.dead (.right (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
      (show CDerives Δ₁ _ _ (.val (.lolli (.imm (.var 0) listL) natN)) from
        .allEV (x := 0) (b := LifeCtx.empty.meetOfDom) (a := .var 0)
          (A := VTy.lolli (.imm (.var 0) listL) natN)
          (.bangE (.var (.there (.there (.here hΓ))))) (fun _ hδ => hδ 0 _ rfl))))
    (.ret (.boxI (.var (.here (.cons (.cons (.cons hΓ)))))
      (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) (natN_outlives _ _) (.cons (.cons (.cons hΓ))))))

/-- The empty list, then three cells, at a dead context. -/
theorem d_cons' {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} (hΓ : Ctx.Dead Γ)
    (h : CDerives Δ Γ e (.val listL)) :
    CDerives Δ Γ (.inj₂ (.app (.val (.prim .alloc)) e)) (.val listL) :=
  .roll listBody_noMut listL_closed (.sumI₂ (.lolliE (deadSplit hΓ) h (.alloc hΓ)))

theorem d_build3 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ build3 (.val listL) :=
  d_cons' hΓ (d_cons' hΓ (d_cons' hΓ (d_nil hΓ)))

/-- The program, open in `countN` (index `0`) and `freeAll` (index `1`):

    build3 to lst. alloc lst to r. countN 3 to g.
    withbor r (Λ. λb. g [] b to n. n) to p. let (r′, n) = p in
    free r′ to lst′. freeAll lst′ to u. u; n                                            -/
def countProgOpen : Expr :=
  bindE build3 (bindE (.app (.val (.prim .alloc)) (.var 0))
    (bindE (.app (.var 2) (.val (num 3)))
      (bindE (.app (.app withbor (.var 1)) borrowerE)
        (.letpair (.var 0)
          (bindE (.app (.val (.prim .free)) (.var 1))
            (bindE (.app (.var 8) (.var 0)) (.seq (.var 0) (.var 2))))))))

/-- The context of the two recursive functions. -/
abbrev ΓF : Ctx VTy := [⟨.lolli natN countTy, true⟩, ⟨.lolli listL .unit, true⟩]

theorem countProg_derives :
    CDerives LifeCtx.empty ΓF countProgOpen (.comp (.ret natN)) := by
  -- `build3 to lst`
  refine .bind (.right (.right .nil)) (.ret (d_build3 (.cons (.cons .nil)))) ?_
  -- `alloc lst to r`
  refine .bind (.left (.right (.right .nil)))
    (.ret (.lolliE (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil))))
      (.alloc (A := listL) (.cons (.cons (.cons .nil)))))) ?_
  -- `countN 3 to g`
  refine .bind (.right (.dead (.left (.right .nil))))
    (.ret (.lolliE (.dead (.dead (.right (.dead .nil)))) (d_num (by repeat constructor) 3)
      (.var (.there (.there (.here (.cons .nil))))))) ?_
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

/-- The program, closed by `countN` and `freeAll`. -/
def countProg : Expr := substAll [countNV, freeAll] countProgOpen

theorem gDenC_F (ls : List SRec) (δ : LSub) : gDenC ls δ ΓF [countNV, freeAll] PMap.empty :=
  gDenC_mk (by simp [Ctx.LiveWithin])
    ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, countN_vC δ ls,
      PMap.empty, PMap.empty, ResU.comp_empty_right _, freeAll_vC δ ls, ⟨rfl, trivial⟩⟩

theorem countProg_wp :
    wpTS [] countProg (fun _ v => Fig16.BoLo.pure (∃ k, v = num k)) (PMap.empty : WRes) := by
  have h := fundamentalC countProg_derives LSub.empty [countNV, freeAll] [] PMap.empty
    Adequacy.models_empty (gDenC_F [] LSub.empty)
  refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty h
  obtain ⟨rfl, k, rfl⟩ := vC_natN hv
  exact ⟨rfl, k, rfl⟩

/-- **Adequacy at the borrowed traversal**: the program runs from the empty memory to a numeral
and the empty memory. -/
theorem countProg_runs :
    ∃ k, BoCa.BoLo.Steps Adequacy.emptyMem countProg Adequacy.emptyMem (.val (num k)) := by
  obtain ⟨v, hsteps, k, rfl⟩ := theorem32 countProg (fun v => ∃ k, v = num k) countProg_wp
  exact ⟨k, hsteps⟩

/-- The numeral an expression is, if it is one. -/
def numOf : Expr → Option Nat
  | .inj₁ .unit => some 0
  | .inj₂ e => (numOf e).map (· + 1)
  | _ => none

/-- The value's numeral, when the run ends with no cell left. -/
def numNoLeak : Outcome → Option Nat
  | .value v false => numOf v.1
  | _ => none

/-- The executable interpreter counts `3` and leaves no cell. -/
theorem countProg_eval : numNoLeak (eval countProg) = some 3 := by decide

end BoCa.Fig16.LogRel.CBPVMu

end
