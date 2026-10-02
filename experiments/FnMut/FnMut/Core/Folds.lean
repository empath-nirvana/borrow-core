import FnMut.Core.MapMut

/-!
# Core — programs through the fold rules  `[spec §6]`

Every function here is a `CDerives` derivation: a fold is `foldImm alg` or `foldOwn alg` with the
algebra derived by the ordinary rules, and its semantic type comes from `fundamentalC`.  No
per-program proof.

* `countFoldE = foldImm countAlg : !U(∀'a. Imm 'a L ⊸ F N)`, the borrowed count of
  `CountFree.lean`.
* `freeFoldE = foldOwn freeAlg : !U(L ⊸ F 1)`, `freeAll` of `Lists.lean`.
* `anyListE`: whether a borrowed list of booleans `μX. 1 ⊕ (B ⊗ Ref X)` holds a `true`.
* `anyTreeE`: whether a borrowed tree `μX. B ⊕ (Ref X ⊗ Ref X)` holds a `true` leaf — two
  recursive calls per node.
* Each program builds a structure, borrows it immutably, folds it inside the borrow, ends the
  borrow and frees the structure with an owned fold; each runs from the empty memory to its
  result and the empty memory (`*_runs`, by adequacy) and the interpreter agrees (`*_eval`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Shapes -/

/-- `B = 1 ⊕ 1`. -/
abbrev boolT : VTy := .sum .unit .unit

/-- `1 ⊕ Ref X`: the boxed list `L`. -/
abbrev listF : FShape := .sum (.leaf .unit) .refX

theorem listF_ty : FShape.ty listF = listBody := rfl

/-- `1 ⊕ (B ⊗ Ref X)`: a list of booleans. -/
abbrev blistF : FShape := .sum (.leaf .unit) (.tensor (.leaf boolT) .refX)

abbrev blistL : VTy := .mu blistF.ty

/-- `B ⊕ (Ref X ⊗ Ref X)`: a tree with boolean leaves. -/
abbrev btreeF : FShape := .sum (.leaf boolT) (.tensor .refX .refX)

abbrev btreeT : VTy := .mu btreeF.ty

theorem boolT_outlives (Δ : LifeCtx) (a : Lifetime.Life) : VOutlives Δ a boolT :=
  .sum .unit .unit

theorem unitT_outlives (Δ : LifeCtx) (a : Lifetime.Life) : VOutlives Δ a .unit := .unit

/-! ### Algebras -/

/-- `Λ. λr. M`, promoted, at a dead context: the shape of every algebra of `foldImm`. -/
theorem d_algI {Γ : Ctx VTy} {A R : VTy} {M : Expr} (hΓ : Ctx.Dead Γ)
    (h : CDerives (LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom)
      (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) M (.comp (.ret R))) :
    CDerives LifeCtx.empty Γ (.val (.lam (.val (.lam M))))
      (.val (.bang (VTy.all 0 LifeCtx.empty.meetOfDom (VTy.lolli A R)))) :=
  .bangThunkV (persistent_dead hΓ) rfl
    (.allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
      (dead_noLive hΓ) (.ret (.thunkV rfl (.lam h))))

/-- `λr. M`, promoted, at a dead context: the shape of every algebra of `foldOwn`. -/
theorem d_algO {Δ : LifeCtx} {Γ : Ctx VTy} {A R : VTy} {M : Expr} (hΓ : Ctx.Dead Γ)
    (h : CDerives Δ (⟨A, true⟩ :: Γ) M (.comp (.ret R))) :
    CDerives Δ Γ (.val (.lam M)) (.val (.bang (VTy.lolli A R))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam h)

/-- `case r {inj₁ u. u; 0 | inj₂ n. n + 1}`. -/
def countAlgB : Expr := .case (.var 0) (.seq (.var 0) (.inj₁ (.val .unit))) (.inj₂ (.var 0))

theorem d_countAlgB {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨.sum .unit natN, true⟩ :: Γ) countAlgB (.comp (.ret natN)) :=
  .sumE (A := .unit) (B := natN) (.left (deadSplit hΓ)) (.var (.here hΓ))
    (.unitE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ)))
      (.ret (.roll natBody_noMut natN_closed (.sumI₁ (.unitI (.cons (.cons hΓ)))))))
    (.ret (.roll natBody_noMut natN_closed (.sumI₂ (.var (.here (.cons hΓ))))))

/-- The count algebra, `!U(∀'b. 1 ⊕ N ⊸ F N)`. -/
def countAlgV : Val := .lam (.val (.lam countAlgB))

theorem d_countAlg {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val countAlgV) (.val (algTy listF 0 natN)) :=
  d_algI hΓ (d_countAlgB (.cons hΓ))

/-- `case r {inj₁ u. u | inj₂ u. u}`. -/
def freeLAlgB : Expr := .case (.var 0) (.var 0) (.var 0)

/-- The algebra freeing a list, `!U(1 ⊕ 1 ⊸ F 1)`. -/
def freeLAlgV : Val := .lam freeLAlgB

theorem d_freeLAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val freeLAlgV) (.val (algOTy listF .unit)) :=
  d_algO hΓ (.sumE (A := .unit) (B := .unit) (.left (deadSplit hΓ)) (.var (.here hΓ))
    (.ret (.var (.here (.cons hΓ)))) (.ret (.var (.here (.cons hΓ)))))

/-- `b ∨ a` at `b` = index 0, `a` = index 1: `case a {inj₁ u. u; b | inj₂ u. u; (case b {…
true})}`. -/
def orE : Expr :=
  .case (.var 1) (.seq (.var 0) (.var 1))
    (.seq (.var 0) (.case (.var 1) (.seq (.var 0) (.inj₂ (.val .unit)))
      (.seq (.var 0) (.inj₂ (.val .unit)))))

theorem d_or {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨boolT, true⟩ :: ⟨boolT, true⟩ :: Γ) orE (.comp (.ret boolT)) := by
  refine .sumE (A := .unit) (B := .unit) (.right (.left (deadSplit hΓ))) (.var (.there (.here hΓ)))
    (.unitE (.left (.right (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
      (.ret (.var (.there (.here (.cons hΓ))))))
    (.unitE (.left (.right (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ)))) ?_)
  refine .sumE (A := .unit) (B := .unit) (.dead (.left (.dead (deadSplit hΓ))))
    (.var (.there (.here (.cons hΓ)))) ?_ ?_ <;>
  exact .unitE (.left (deadSplit (.cons (.cons (.cons hΓ)))))
    (.var (.here (.cons (.cons (.cons hΓ)))))
    (.ret (.sumI₂ (.unitI (.cons (.cons (.cons (.cons hΓ)))))))

/-- `case r {inj₁ u. u; false | inj₂ p. let (a, b) = p in a ∨ b}`. -/
def anyLAlgB : Expr := .case (.var 0) (.seq (.var 0) (.inj₁ (.val .unit))) (.letpair (.var 0) orE)

/-- The search algebra for a list of booleans, `!U(∀'b. 1 ⊕ (B ⊗ B) ⊸ F B)`. -/
def anyLAlgV : Val := .lam (.val (.lam anyLAlgB))

theorem d_anyLAlg {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val anyLAlgV) (.val (algTy blistF 0 boolT)) := by
  refine d_algI hΓ (.sumE (A := .unit) (B := .tensor boolT boolT) (.left (deadSplit (.cons hΓ)))
    (.var (.here (.cons hΓ))) ?_ ?_)
  · exact .unitE (.left (.dead (deadSplit (.cons hΓ)))) (.var (.here (.cons (.cons hΓ))))
      (.ret (.sumI₁ (.unitI (.cons (.cons (.cons hΓ))))))
  · exact .tensorE (A := boolT) (B := boolT) (.left (.dead (deadSplit (.cons hΓ))))
      (.var (.here (.cons (.cons hΓ)))) (d_or (.cons (.cons (.cons hΓ))))

/-- `case r {inj₁ b. b | inj₂ p. let (x, y) = p in x ∨ y}`. -/
def anyTAlgB : Expr := .case (.var 0) (.var 0) (.letpair (.var 0) orE)

/-- The search algebra for a tree, `!U(∀'b. B ⊕ (B ⊗ B) ⊸ F B)`. -/
def anyTAlgV : Val := .lam (.val (.lam anyTAlgB))

theorem d_anyTAlg {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val anyTAlgV) (.val (algTy btreeF 0 boolT)) :=
  d_algI hΓ (.sumE (A := boolT) (B := .tensor boolT boolT) (.left (deadSplit (.cons hΓ)))
    (.var (.here (.cons hΓ))) (.ret (.var (.here (.cons (.cons hΓ)))))
    (.tensorE (A := boolT) (B := boolT) (.left (.dead (deadSplit (.cons hΓ))))
      (.var (.here (.cons (.cons hΓ)))) (d_or (.cons (.cons (.cons hΓ))))))

/-- `case r {inj₁ u. u | inj₂ p. let (a, u) = p in u; case a {inj₁ u. u | inj₂ u. u}}`. -/
def freeBLAlgB : Expr :=
  .case (.var 0) (.var 0) (.letpair (.var 0) (.seq (.var 0) (.case (.var 1) (.var 0) (.var 0))))

def freeBLAlgV : Val := .lam freeBLAlgB

theorem d_freeBLAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val freeBLAlgV) (.val (algOTy blistF .unit)) := by
  refine d_algO hΓ (.sumE (A := .unit) (B := .tensor boolT .unit) (.left (deadSplit hΓ))
    (.var (.here hΓ)) (.ret (.var (.here (.cons hΓ)))) ?_)
  refine .tensorE (A := boolT) (B := .unit) (.left (.dead (deadSplit hΓ)))
    (.var (.here (.cons hΓ))) ?_
  refine .unitE (.left (.right (deadSplit (.cons (.cons hΓ)))))
    (.var (.here (.cons (.cons (.cons hΓ))))) ?_
  exact .sumE (A := .unit) (B := .unit) (.dead (.left (deadSplit (.cons (.cons hΓ)))))
    (.var (.there (.here (.cons (.cons hΓ))))) (.ret (.var (.here (.cons (.cons (.cons (.cons hΓ)))))))
    (.ret (.var (.here (.cons (.cons (.cons (.cons hΓ)))))))

/-- `case r {inj₁ b. case b {inj₁ u. u | inj₂ u. u} | inj₂ p. let (u₁, u₂) = p in u₂; u₁}`. -/
def freeBTAlgB : Expr :=
  .case (.var 0) (.case (.var 0) (.var 0) (.var 0)) (.letpair (.var 0) (.seq (.var 0) (.var 1)))

def freeBTAlgV : Val := .lam freeBTAlgB

theorem d_freeBTAlg {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val freeBTAlgV) (.val (algOTy btreeF .unit)) := by
  refine d_algO hΓ (.sumE (A := boolT) (B := .tensor .unit .unit) (.left (deadSplit hΓ))
    (.var (.here hΓ)) ?_ ?_)
  · exact .sumE (A := .unit) (B := .unit) (.left (deadSplit (.cons hΓ)))
      (.var (.here (.cons hΓ))) (.ret (.var (.here (.cons (.cons hΓ)))))
      (.ret (.var (.here (.cons (.cons hΓ)))))
  · exact .tensorE (A := .unit) (B := .unit) (.left (.dead (deadSplit hΓ)))
      (.var (.here (.cons hΓ)))
      (.unitE (.left (.right (deadSplit (.cons (.cons hΓ)))))
        (.var (.here (.cons (.cons (.cons hΓ)))))
        (.ret (.var (.there (.here (.cons (.cons hΓ)))))))

/-! ### The folds, by the rules -/

/-- `foldImm countAlg`, the borrowed count. -/
def countFoldE : Expr := .app (.val (foldImmV listF)) (.val countAlgV)

theorem d_countFold {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ countFoldE (.val countTy) :=
  .lolliE (deadSplit hΓ) (d_countAlg hΓ)
    (.foldImm listF 0 LifeCtx.empty.meetOfDom natN hΓ ⟨trivial, trivial⟩ trivial
      (by simp [VFree, FShape.ty]) (by simp [VFree, natN, natBody]) natN_outlives)

/-- **The borrowed count's semantic type, from the Fundamental Property.** -/
theorem countFold_semV : SemV LifeCtx.empty [] countFoldE countTy := fundamentalC (d_countFold .nil)

/-- `foldOwn freeLAlg`, freeing a list. -/
def freeFoldE : Expr := .app (.val (foldOwnV listF)) (.val freeLAlgV)

theorem d_freeFold {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ freeFoldE (.val (.lolli listL .unit)) :=
  .bangE (.lolliE (deadSplit hΓ) (d_freeLAlg hΓ) (.foldOwn listF .unit hΓ ⟨trivial, trivial⟩ trivial))

/-- **`freeAll`'s semantic type, from the Fundamental Property.** -/
theorem freeFold_semV : SemV LifeCtx.empty [] freeFoldE (.lolli listL .unit) :=
  fundamentalC (d_freeFold .nil)

/-- `foldImm anyLAlg`. -/
def anyListE : Expr := .app (.val (foldImmV blistF)) (.val anyLAlgV)

/-- `!U(∀'a. Imm 'a M ⊸ F R)`. -/
abbrev fTy (M R : VTy) : VTy :=
  .bang (VTy.all 0 LifeCtx.empty.meetOfDom (VTy.lolli (.imm (.var 0) M) R))

theorem d_anyList {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ anyListE (.val (fTy blistL boolT)) :=
  .lolliE (deadSplit hΓ) (d_anyLAlg hΓ)
    (.foldImm blistF 0 LifeCtx.empty.meetOfDom boolT hΓ (by simp [FShape.WF, VTy.Cl]) trivial
      (by simp [VFree, FShape.ty]) (by simp [VFree]) boolT_outlives)

/-- `foldImm anyTAlg`. -/
def anyTreeE : Expr := .app (.val (foldImmV btreeF)) (.val anyTAlgV)

theorem d_anyTree {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ anyTreeE (.val (fTy btreeT boolT)) :=
  .lolliE (deadSplit hΓ) (d_anyTAlg hΓ)
    (.foldImm btreeF 0 LifeCtx.empty.meetOfDom boolT hΓ (by simp [FShape.WF, VTy.Cl]) trivial
      (by simp [VFree, FShape.ty]) (by simp [VFree]) boolT_outlives)

/-- `foldOwn freeBLAlg`. -/
def freeBListE : Expr := .app (.val (foldOwnV blistF)) (.val freeBLAlgV)

theorem d_freeBList {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ freeBListE (.val (.lolli blistL .unit)) :=
  .bangE (.lolliE (deadSplit hΓ) (d_freeBLAlg hΓ)
    (.foldOwn blistF .unit hΓ (by simp [FShape.WF, VTy.Cl]) trivial))

/-- `foldOwn freeBTAlg`. -/
def freeBTreeE : Expr := .app (.val (foldOwnV btreeF)) (.val freeBTAlgV)

theorem d_freeBTree {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ freeBTreeE (.val (.lolli btreeT .unit)) :=
  .bangE (.lolliE (deadSplit hΓ) (d_freeBTAlg hΓ)
    (.foldOwn btreeF .unit hΓ (by simp [FShape.WF, VTy.Cl]) trivial))

/-! ### The program -/

/-- The borrower at a fold `g` (index `0`): `Λ. λb. g [] b to n. n`, at `Imm 'x M ⊸ ['x] R`. -/
theorem d_borrowerG {M R : VTy} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (hR : ∀ Δ a, VOutlives Δ a R)
    (hinst : VTy.instLife 0 (.var 0) (VTy.lolli (.imm (.var 0) M) R) = VTy.lolli (.imm (.var 0) M) R) :
    CDerives LifeCtx.empty (⟨fTy M R, true⟩ :: Γ) borrowerE
      (.val (VTy.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.imm (.var 0) M) (.box (.var 0) R)))) := by
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
      (show CDerives Δ₁ _ _ (.val (.lolli (.imm (.var 0) M) R)) from hinst ▸
        .allEV (x := 0) (b := LifeCtx.empty.meetOfDom) (a := .var 0)
          (A := VTy.lolli (.imm (.var 0) M) R)
          (.bangE (.var (.there (.there (.here hΓ))))) (fun _ hδ => hδ 0 _ rfl))))
    (.ret (.boxI (.var (.here (.cons (.cons (.cons hΓ)))))
      (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) (hR _ _) (.cons (.cons (.cons hΓ))))))

/-- The program, open in a fold (index `0`) and a free (index `1`):

    build to s. alloc s to r. return fold to g.
    withbor r (Λ. λb. g [] b to n. n) to p. let (r′, n) = p in
    free r′ to s′. free s′ to u. u; n                                                    -/
def progOpen (build : Expr) : Expr :=
  bindE build (bindE (.app (.val (.prim .alloc)) (.var 0))
    (bindE (.var 2)
      (bindE (.app (.app withbor (.var 1)) borrowerE)
        (.letpair (.var 0)
          (bindE (.app (.val (.prim .free)) (.var 1))
            (bindE (.app (.var 8) (.var 0)) (.seq (.var 0) (.var 2))))))))

theorem d_progOpen {M R : VTy} {build : Expr}
    (hb : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ build (.val M))
    (hM : ∀ z, ¬ VFree z M) (hR0 : ∀ z, ¬ VFree z R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hinst : VTy.instLife 0 (.var 0) (VTy.lolli (.imm (.var 0) M) R) = VTy.lolli (.imm (.var 0) M) R) :
    CDerives LifeCtx.empty [⟨fTy M R, true⟩, ⟨.lolli M .unit, true⟩] (progOpen build)
      (.comp (.ret R)) := by
  -- `build to s`
  refine .bind (.right (.right .nil)) (.ret (hb (.cons (.cons .nil)))) ?_
  -- `alloc s to r`
  refine .bind (.left (.right (.right .nil)))
    (.ret (.lolliE (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil))))
      (.alloc (A := M) (.cons (.cons (.cons .nil)))))) ?_
  -- `return fold to g`
  refine .bind (.right (.dead (.left (.right .nil))))
    (.ret (.var (.there (.there (.here (.cons .nil)))))) ?_
  -- `withbor r borrower to p`
  refine .bind (.left (.left (.dead (.dead (.right .nil)))))
    (.ret (.lolliE (.left (.right (.dead (.dead (.dead .nil)))))
      (d_borrowerG (by repeat constructor) hR hinst)
      (.lolliE (.dead (.left (.dead (.dead (.dead .nil)))))
        (.var (.there (.here (by repeat constructor))))
        (.withbor1 (A := M) (B := R) 0 (by repeat constructor) rfl
          (fun y h => absurd h (hM y)) (hM 0) (hR0 0))))) ?_
  -- `let (r′, n) = p in`
  refine .tensorE (A := .ref M) (B := R)
    (.left (.dead (.dead (.dead (.dead (.right .nil))))))
    (.var (.here (by repeat constructor))) ?_
  -- `free r′ to s′`
  refine .bind (.right (.left (.dead (.dead (.dead (.dead (.dead (.right .nil))))))))
    (.ret (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))
      (.var (.there (.here (by repeat constructor))))
      (.free (A := M) (by repeat constructor)))) ?_
  -- `free s′ to u`
  refine .bind (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.left .nil)))))))))
    (.ret (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.right .nil)))))))))
      (.var (.here (by repeat constructor)))
      (.var (.there (.there (.there (.there (.there (.there (.there (.there
        (.here .nil)))))))))))) ?_
  -- `u; n`
  exact .unitE (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.var (.here (by repeat constructor)))
    (.ret (.var (.there (.there (.here (by repeat constructor))))))

/-- The closed program: `free to f. fold to g. progOpen build`. -/
def foldProg (freeE foldE build : Expr) : Expr := bindE freeE (bindE foldE (progOpen build))

theorem d_foldProg {M R : VTy} {freeE foldE build : Expr}
    (hf : CDerives LifeCtx.empty [] freeE (.val (.lolli M .unit)))
    (hg : CDerives LifeCtx.empty [⟨.lolli M .unit, false⟩] foldE (.val (fTy M R)))
    (hb : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ build (.val M))
    (hM : ∀ z, ¬ VFree z M) (hR0 : ∀ z, ¬ VFree z R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hinst : VTy.instLife 0 (.var 0) (VTy.lolli (.imm (.var 0) M) R) = VTy.lolli (.imm (.var 0) M) R) :
    CDerives LifeCtx.empty [] (foldProg freeE foldE build) (.comp (.ret R)) :=
  .bind .nil (.ret hf) (.bind (.right .nil) (.ret hg) (d_progOpen hb hM hR0 hR hinst))

/-! ### Results -/

/-- A value of `B` is a boolean and holds no resource. -/
theorem vC_boolT {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vC b boolT ls δ v ρ) : ρ = PMap.empty ∧ (v = Val.inj₁ .unit ∨ v = Val.inj₂ .unit) := by
  rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
  · obtain ⟨rfl, hρ, rfl⟩ := pure_sep_iff.mp hs
    exact ⟨hρ, Or.inl rfl⟩
  · obtain ⟨rfl, hρ, rfl⟩ := pure_sep_iff.mp hs
    exact ⟨hρ, Or.inr rfl⟩

/-- The boolean an expression is, if it is one. -/
def boolOf : Expr → Option Bool
  | .inj₁ .unit => some false
  | .inj₂ .unit => some true
  | _ => none

/-- The value's boolean, when the run ends with no cell left. -/
def boolNoLeak : Outcome → Option Bool
  | .value v false => boolOf v.1
  | _ => none

/-- A closed derivation at `F R` gives a `wpTS` at the empty list and memory. -/
theorem wp_of_derives {e : Expr} {R : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret R))) :
    wpTS [] e (fun ls v => vP R ls LSub.empty v) (PMap.empty : WRes) := by
  have hwp := fundamentalC h LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  rwa [show substAll [] e = e from Adequacy.psub_nil 0 e] at hwp

/-! ### The count, through `foldImm` and `foldOwn` -/

/-- Build a 3-cell list, borrow it, count it with `foldImm countAlg`, end the borrow, free it
with `foldOwn freeLAlg`. -/
def countFoldProg : Expr := foldProg freeFoldE countFoldE build3

theorem countFoldProg_derives :
    CDerives LifeCtx.empty [] countFoldProg (.comp (.ret natN)) :=
  d_foldProg (d_freeFold .nil) (d_countFold (.cons .nil)) d_build3
    (fun _ => by simp [VFree, listL, listBody]) (fun _ => by simp [VFree, natN, natBody])
    natN_outlives rfl

/-- **Adequacy at the derived count**: from the empty memory to a numeral and the empty
memory. -/
theorem countFoldProg_runs :
    ∃ k, BoCa.BoLo.Steps Adequacy.emptyMem countFoldProg Adequacy.emptyMem (.val (num k)) := by
  have hwp : wpTS [] countFoldProg (fun _ v => Fig16.BoLo.pure (∃ k, v = num k))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives countFoldProg_derives)
    obtain ⟨rfl, k, rfl⟩ := vC_natN hv
    exact ⟨rfl, k, rfl⟩
  obtain ⟨v, hsteps, k, rfl⟩ := theorem32 countFoldProg (fun v => ∃ k, v = num k) hwp
  exact ⟨k, hsteps⟩

theorem countFoldProg_eval : numNoLeak (eval countFoldProg) = some 3 := by decide

/-! ### Search in a list of booleans -/

/-- `inj₂ (b, alloc e)`. -/
def consB (b e : Expr) : Expr := .inj₂ (.pair b (.app (.val (.prim .alloc)) e))

theorem d_consB {Γ : Ctx VTy} {b e : Expr} (hΓ : Ctx.Dead Γ)
    (hb : CDerives LifeCtx.empty Γ b (.val boolT)) (he : CDerives LifeCtx.empty Γ e (.val blistL)) :
    CDerives LifeCtx.empty Γ (consB b e) (.val blistL) :=
  .roll (FShape.noMut_ty (F := blistF) (by simp [FShape.WF, VTy.Cl]))
    (FShape.Cl_ty (F := blistF) (by simp [FShape.WF, VTy.Cl]))
    (.sumI₂ (.tensorI (deadSplit hΓ) hb (.lolliE (deadSplit hΓ) he (.alloc hΓ))))

def falseE : Expr := .inj₁ (.val .unit)
def trueE : Expr := .inj₂ (.val .unit)

/-- `[false, true, false]`. -/
def buildB : Expr := consB falseE (consB trueE (consB falseE (.inj₁ (.val .unit))))

theorem d_buildB {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ buildB (.val blistL) :=
  d_consB hΓ (.sumI₁ (.unitI hΓ)) (d_consB hΓ (.sumI₂ (.unitI hΓ)) (d_consB hΓ (.sumI₁ (.unitI hΓ))
    (.roll (FShape.noMut_ty (F := blistF) (by simp [FShape.WF, VTy.Cl]))
      (FShape.Cl_ty (F := blistF) (by simp [FShape.WF, VTy.Cl])) (.sumI₁ (.unitI hΓ)))))

/-- Build `[false, true, false]`, borrow it, search it with `foldImm anyLAlg`, end the borrow,
free it with `foldOwn freeBLAlg`. -/
def anyListProg : Expr := foldProg freeBListE anyListE buildB

theorem anyListProg_derives :
    CDerives LifeCtx.empty [] anyListProg (.comp (.ret boolT)) :=
  d_foldProg (d_freeBList .nil) (d_anyList (.cons .nil)) d_buildB
    (fun _ => by simp [VFree, FShape.ty]) (fun _ => by simp [VFree])
    boolT_outlives rfl

theorem anyListProg_runs :
    ∃ v, BoCa.BoLo.Steps Adequacy.emptyMem anyListProg Adequacy.emptyMem (.val v) ∧
      (v = Val.inj₁ .unit ∨ v = Val.inj₂ .unit) := by
  refine theorem32 anyListProg _ (wpTS_mono (fun _ v ρ hv => ?_) PMap.empty
    (wp_of_derives anyListProg_derives))
  exact vC_boolT hv

theorem anyListProg_eval : boolNoLeak (eval anyListProg) = some true := by decide

/-! ### Search in a tree -/

/-- `inj₂ (alloc l, alloc r)`. -/
def nodeE (l r : Expr) : Expr :=
  .inj₂ (.pair (.app (.val (.prim .alloc)) l) (.app (.val (.prim .alloc)) r))

theorem btreeF_WF : btreeF.WF := by simp [FShape.WF, VTy.Cl]

theorem d_leaf {Γ : Ctx VTy} {b : Expr} (hb : CDerives LifeCtx.empty Γ b (.val boolT)) :
    CDerives LifeCtx.empty Γ (.inj₁ b) (.val btreeT) :=
  .roll (FShape.noMut_ty btreeF_WF) (FShape.Cl_ty btreeF_WF) (.sumI₁ hb)

theorem d_node {Γ : Ctx VTy} {l r : Expr} (hΓ : Ctx.Dead Γ)
    (hl : CDerives LifeCtx.empty Γ l (.val btreeT)) (hr : CDerives LifeCtx.empty Γ r (.val btreeT)) :
    CDerives LifeCtx.empty Γ (nodeE l r) (.val btreeT) :=
  .roll (FShape.noMut_ty btreeF_WF) (FShape.Cl_ty btreeF_WF)
    (.sumI₂ (.tensorI (deadSplit hΓ) (.lolliE (deadSplit hΓ) hl (.alloc hΓ))
      (.lolliE (deadSplit hΓ) hr (.alloc hΓ))))

/-- `node (leaf false) (node (leaf false) (leaf true))`. -/
def buildT : Expr := nodeE (.inj₁ falseE) (nodeE (.inj₁ falseE) (.inj₁ trueE))

theorem d_buildT {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ buildT (.val btreeT) :=
  d_node hΓ (d_leaf (.sumI₁ (.unitI hΓ)))
    (d_node hΓ (d_leaf (.sumI₁ (.unitI hΓ))) (d_leaf (.sumI₂ (.unitI hΓ))))

/-- Build the tree, borrow it, search it with `foldImm anyTAlg`, end the borrow, free it with
`foldOwn freeBTAlg`. -/
def anyTreeProg : Expr := foldProg freeBTreeE anyTreeE buildT

theorem anyTreeProg_derives :
    CDerives LifeCtx.empty [] anyTreeProg (.comp (.ret boolT)) :=
  d_foldProg (d_freeBTree .nil) (d_anyTree (.cons .nil)) d_buildT
    (fun _ => by simp [VFree, FShape.ty]) (fun _ => by simp [VFree])
    boolT_outlives rfl

theorem anyTreeProg_runs :
    ∃ v, BoCa.BoLo.Steps Adequacy.emptyMem anyTreeProg Adequacy.emptyMem (.val v) ∧
      (v = Val.inj₁ .unit ∨ v = Val.inj₂ .unit) := by
  refine theorem32 anyTreeProg _ (wpTS_mono (fun _ v ρ hv => ?_) PMap.empty
    (wp_of_derives anyTreeProg_derives))
  exact vC_boolT hv

theorem anyTreeProg_eval : boolNoLeak (eval anyTreeProg) = some true := by decide

/-! ### A head `X`: copying a borrowed numeral -/

/-- `1 ⊕ X`: the numerals `N`, recursion at a head `X`. -/
abbrev natF : FShape := .sum (.leaf .unit) .varX

theorem natF_ty : FShape.ty natF = natBody := rfl

/-- `foldImm countAlg` at `N`: `Imm 'a N ⊸ F N` copies the numeral. -/
def natCopyE : Expr := .app (.val (foldImmV natF)) (.val countAlgV)

theorem d_natCopy {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ natCopyE (.val (fTy natN natN)) :=
  .lolliE (deadSplit hΓ) (d_countAlg hΓ)
    (.foldImm natF 0 LifeCtx.empty.meetOfDom natN hΓ ⟨trivial, trivial⟩ trivial
      (by simp [VFree, FShape.ty]) (by simp [VFree, natN, natBody]) natN_outlives)

/-- `foldOwn freeLAlg` at `N`. -/
def freeNatE : Expr := .app (.val (foldOwnV natF)) (.val freeLAlgV)

theorem d_freeNat {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ freeNatE (.val (.lolli natN .unit)) :=
  .bangE (.lolliE (deadSplit hΓ) (d_freeLAlg hΓ) (.foldOwn natF .unit hΓ ⟨trivial, trivial⟩ trivial))

/-- Put `3` in a cell, borrow it, copy it through the borrow with `foldImm`, end the borrow, free
the original with `foldOwn`. -/
def natCopyProg : Expr := foldProg freeNatE natCopyE (.val (num 3))

theorem natCopyProg_derives :
    CDerives LifeCtx.empty [] natCopyProg (.comp (.ret natN)) :=
  d_foldProg (d_freeNat .nil) (d_natCopy (.cons .nil)) (fun hΓ => d_num hΓ 3)
    (fun _ => by simp [VFree, natN, natBody]) (fun _ => by simp [VFree, natN, natBody])
    natN_outlives rfl

theorem natCopyProg_runs :
    ∃ k, BoCa.BoLo.Steps Adequacy.emptyMem natCopyProg Adequacy.emptyMem (.val (num k)) := by
  have hwp : wpTS [] natCopyProg (fun _ v => Fig16.BoLo.pure (∃ k, v = num k))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives natCopyProg_derives)
    obtain ⟨rfl, k, rfl⟩ := vC_natN hv
    exact ⟨rfl, k, rfl⟩
  obtain ⟨v, hsteps, k, rfl⟩ := theorem32 natCopyProg (fun v => ∃ k, v = num k) hwp
  exact ⟨k, hsteps⟩

theorem natCopyProg_eval : numNoLeak (eval natCopyProg) = some 3 := by decide

end BoCa.Fig16.LogRel.Core

end
