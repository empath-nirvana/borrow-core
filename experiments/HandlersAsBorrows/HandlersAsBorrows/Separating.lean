import HandlersAsBorrows.Examples

/-!
# Theorem (c): a capability returned from a function and stored in a cell

Inside the handler of `flip` (state `1 ⊕ 1`), the capability object
`obj = (m, flip) : Mut 'x B ⊗ !(B ⊗ 1 ⊸ B ⊗ B)` is

1. **returned** from a first-class function `pack = λm. (m, flip)`,
2. **stored** in a heap cell `r = alloc obj`,
3. taken back out (`free r`), and its operation performed through it:

       let (c, w) = withbor (alloc (inj₁ ())) (Λ. λm.
         let obj = pack m;  let r = alloc obj;  let (m′, f) = free r;
         let (f₁, f₂) = copy f;  let (m″, b) = withswap m′ (λs. f₁ (s, ()));
         forget m″; forget f₂; b; □());
       w; case (free c) {x ⇒ x | y ⇒ y}

Ξ has no such program: blocks and capabilities "can neither be returned nor stored in data
structures" (Effekt TR §1.6), and value types have no block component (Fig. 3).  BoLo + `!` types
it (`d_sepProg`); the cell of type `Ref (Mut 'x B ⊗ !code)` is bounded by `'x` because `[]I`
checks what is live at the end of the callback (`object_not_outlives`); the Fundamental Property
makes it safe (`sepProg_runs`, by adequacy), and the interpreter runs it (`sepProg_eval`).

This separates BoLo + `!` from Ξ, **not** from System C, whose boxes store a block that captures
a capability at a type recording it (`README.md` §5).

`[about ours]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace HandlersAsBorrows.Xi
open BoCa BoCa.Lifetime BoCa.Programs

/-- `Mut 'x (1 ⊕ 1)`, `'x` the variable `0`. -/
abbrev MB : Ty := .mut (.var 0) B
/-- The clause's type `!(B ⊗ 1 ⊸ B ⊗ B)`. -/
abbrev OC : Ty := .bang (.lolli (.tensor B .unit) (.tensor B B))
/-- The capability object. -/
abbrev OBJ : Ty := .tensor MB OC

/-- `flip = λp. let (s, u) = p; case s {x ⇒ (inj₂ x, inj₁ u) | y ⇒ (inj₁ u, inj₂ y)}`. -/
def flipC : Expr :=
  lam (.letpair (.var 0) (.case (.var 1) (.pair (.inj₂ (.var 0)) (.inj₁ (.var 1)))
    (.pair (.inj₁ (.var 1)) (.inj₂ (.var 0)))))

theorem d_flipC {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ flipC OC :=
  .bangLamI hΓ.persistent rfl
    (.tensorE (T₁ := B) (T₂ := .unit) (.left hΓ.split) rfl (.var (.here hΓ))
      (.sumE (T₁ := .unit) (T₂ := .unit) (.right (.left (.dead hΓ.split))) rfl
        (.var (.there (.here (.cons hΓ))))
        (.tensorI (.left (.right (.dead (.dead hΓ.split))))
          (.sumI₂ (.var (.here (.cons (.cons (.cons hΓ))))))
          (.sumI₁ (.var (.there (.here (.cons (.cons hΓ)))))))
        (.tensorI (.right (.left (.dead (.dead hΓ.split))))
          (.sumI₁ (.var (.there (.here (.cons (.cons hΓ))))))
          (.sumI₂ (.var (.here (.cons (.cons (.cons hΓ)))))))))

/-- `pack = λm. (m, flip)`: a function that returns the capability. -/
def pack : Expr := lam (.pair (.var 0) flipC)

def sepBody : Expr :=
  elet (.app pack (.var 0))
    (elet (.app alloc' (.var 0))
      (.letpair (.app free' (.var 0))
        (.letpair (.app copy (.var 0))
          (.letpair (app2 withswap (.var 3) (lam (.app (.var 2) (.pair (.var 0) unit'))))
            (.seq (.app forget (.var 1)) (.seq (.app forget (.var 2))
              (.seq (dropB (.var 0)) unit')))))))

def sepProg : Expr :=
  .letpair (app2 withbor (.app alloc' (.inj₁ unit')) (lam (lam sepBody)))
    (.seq (.var 0) (dropB (.app free' (.var 1))))

theorem d_sepBody :
    DerivesWf D1 [⟨MB, true⟩, ⟨.unit, false⟩] sepBody (.box (.var 0) .unit) := by
  -- obj = pack m
  refine .lolliE (.left (.dead .nil))
    (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
      (.lolliI rfl (.tensorI (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil))))
        (d_flipC (.cons (.cons (.cons .nil)))))))
    (.lolliI rfl ?_)
  -- r = alloc obj; ctx: obj, m, _
  refine .lolliE (.left (.dead (.dead .nil)))
    (.lolliE (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil))))
      (.allocAx (.cons (.cons (.cons .nil)))))
    (.lolliI rfl ?_)
  -- (m′, f) = free r; ctx: r, obj, m, _
  refine .tensorE (T₁ := MB) (T₂ := OC) (.left (.dead (.dead (.dead .nil)))) rfl
    (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil)))))
      (.freeAx (.cons (.cons (.cons (.cons .nil)))))) ?_
  -- (f₁, f₂) = copy f; ctx: f, m′, r, obj, m, _
  refine .tensorE (T₁ := OC) (T₂ := OC) (.left (.right (.dead (.dead (.dead (.dead .nil)))))) rfl
    (.lolliE (.left (.dead (.dead (.dead (.dead (.dead .nil))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))
      (.copyBangAx (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))) ?_
  -- (m″, b) = withswap m′ (λs. f₁ (s, ())); ctx: f₂, f₁, f, m′, r, obj, m, _
  refine .tensorE (T₁ := MB) (T₂ := B)
    (.right (.left (.dead (.left (.dead (.dead (.dead (.dead .nil)))))))) rfl
    (.lolliE (T₁ := .lolli B (.tensor B B))
      (.dead (.left (.dead (.right (.dead (.dead (.dead (.dead .nil))))))))
      (.lolliI rfl
        (.lolliE (T₁ := .tensor B .unit)
          (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
          (.tensorI (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
            (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))
            (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))))
          (.bangE (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))))))
      (.lolliE (.dead (.dead (.dead (.left (.dead (.dead (.dead (.dead .nil))))))))
        (.var (.there (.there (.there (.here (.cons (.cons (.cons (.cons .nil)))))))))
        (.withswapAx (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))))
    ?_
  -- ctx: b, m″, f₂, f₁, f, m′, r, obj, m, _
  refine .unitE (.right (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
      (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))))
      (.forgetMutAx (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))))
    ?_
  refine .unitE (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
    (.lolliE (.dead (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))))
      (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))))
      (.forgetBangAx (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))))
    ?_
  have hd9 : Ctx.Dead ([⟨MB, false⟩, ⟨OC, false⟩, ⟨OC, false⟩, ⟨OC, false⟩, ⟨MB, false⟩,
      ⟨.ref OBJ, false⟩, ⟨OBJ, false⟩, ⟨MB, false⟩, ⟨.unit, false⟩] : Ctx Ty) :=
    .cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))
  exact .unitE (.left hd9.split) (d_dropB hd9)
    (.boxIctx (.unitI (.cons hd9)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons hd9)))

/-- **Theorem (c), typing.**  The program has a `DerivesWf` derivation at `1`. -/
theorem d_sepProg : DerivesWf LifeCtx.empty [] sepProg .unit :=
  .tensorE (T₁ := .ref B) (T₂ := .unit) .nil rfl
    (.lolliE .nil
      (.allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0) (.lolliI rfl d_sepBody))
      (.lolliE .nil (.lolliE .nil (.sumI₁ (.unitI .nil)) (.allocAx .nil))
        (.withbor2Ax .nil 0 rfl ⟨.top, LifeCtx.defines_of_wf rfl, .sum .unit .unit⟩ rfl)))
    (.unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
      (.sumE (.dead (.left .nil)) rfl
        (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))
        (.var (.here (.cons (.cons .nil)))) (.var (.here (.cons (.cons .nil))))))

/-- **Theorem (c), safety.**  By the Fundamental Property (through adequacy): the program runs
to `()`, and the handler's cell and the cell that held the capability are both freed. -/
theorem sepProg_runs : BoLo.Steps Adequacy.emptyMem sepProg Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_sepProg

theorem sepProg_eval : unitNoLeak (eval sepProg) = true := by decide

end HandlersAsBorrows.Xi
