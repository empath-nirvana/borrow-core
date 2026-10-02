import FnMut.Core.Blocks

/-!
# Core — records and variants as derived forms  `[spec §5]`

A record is a binary tree of fields, the block `Shape` of `Blocks.lean`, with no unit leaf:

    {fields of σ}   ≜  σ.valTy     (leaf A ↦ A,  node s₁ s₂ ↦ valTy s₁ ⊗ valTy s₂)
    ⟨cases of σ⟩    ≜  σ.sumTy     (leaf A ↦ A,  node s₁ s₂ ↦ sumTy s₁ ⊕ sumTy s₂)

A field or a case is named by its path in the tree (`FPath`, `false` for left).  Labels are
names only.  The owned block of a record is `σ.refTy` (`Blocks.lean`), and the one-cell
`Ref σ.valTy` is a separate type.

Every rule is a derived rule of `CDerives`, with no constructor added, so `fundamentalC`
covers it.

| form | term | rule |
|---|---|---|
| `{eᵢ}` | `tuple` | `recI` |
| `let {xᵢ} = e in b` | `recLet` | `recE` |
| `e.p`, the other fields affine | `getAt` | `getAt_wf` |
| `p e` | `injAt` | `injAt_wf` |
| `case e {p x ⇒ bₚ}` | `vcase` | `vcase_wf` (premises `Branches`) |
| read field `p` of `Imm @a {…}` | `loadField` = `withload` + `getAt` | `loadField_wf`, `loadField_sem` |
| match on `Imm @a ⟨…⟩` | `loadCase` = `withload` + `vcase` | `loadCase_wf` |
| run `g : A ⊸ A ⊗ B` on field `p` of `Mut @a {…}` | `swapField` = `withswap` + `modAt` | `swapField_wf`, `swapField_sem` |

`Affine` is the set of value types a closed term consumes (`dropT`).  `Imm̲ 'b A` is affine
when `A`'s spine of `⊗`, `⊕` and `[@a]` holds no `μ` or type variable
(`affine_immReborrow`).  The reborrowing facts are `Imm̲`, outlives, 6.131 (`reborrow_vShape`)
and 6.60 (`vC_outlives`) at `valTy`/`sumTy`, each the binary clause iterated.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Value-level derived forms

The eliminators of `CDerives` are at computation types; at a value judgment they are read
back through `ofRet`, as the embedding does. -/

/-- `λx. b : U(A ⊸ F B)` from `b : B`. -/
theorem CDerives.lamV {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A B : VTy}
    (h : CDerives Δ (⟨A, true⟩ :: Γ) M (.val B)) :
    CDerives Δ Γ (.val (.lam M)) (.val (.lolli A B)) :=
  .thunkV rfl (.lam (.ret h))

theorem CDerives.letpairV {Δ : LifeCtx} {Γ Γp Γb : Ctx VTy} {V M : Expr} {A B C : VTy}
    (hs : Ctx.SplitP Γ Γp Γb) (hV : CDerives Δ Γp V (.val (.tensor A B)))
    (hM : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γb) M (.val C)) :
    CDerives Δ Γ (.letpair V M) (.val C) :=
  .ofRet (.tensorE hs hV (.ret hM))

theorem CDerives.seqV {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {V M : Expr} {C : VTy}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hV : CDerives Δ Γ₁ V (.val .unit))
    (hM : CDerives Δ Γ₂ M (.val C)) : CDerives Δ Γ (.seq V M) (.val C) :=
  .ofRet (.unitE hs hV (.ret hM))

theorem CDerives.caseV {Δ : LifeCtx} {Γ Γs Γb : Ctx VTy} {V M₁ M₂ : Expr} {A B C : VTy}
    (hs : Ctx.SplitP Γ Γs Γb) (hV : CDerives Δ Γs V (.val (.sum A B)))
    (h₁ : CDerives Δ (⟨A, true⟩ :: Γb) M₁ (.val C))
    (h₂ : CDerives Δ (⟨B, true⟩ :: Γb) M₂ (.val C)) :
    CDerives Δ Γ (.case V M₁ M₂) (.val C) :=
  .ofRet (.sumE hs hV (.ret h₁) (.ret h₂))

/-- `let x = e in b`, written `(λx. b) e`. -/
theorem CDerives.eletV {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {e b : Expr} {A C : VTy}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (he : CDerives Δ Γ₁ e (.val A))
    (hb : CDerives Δ (⟨A, true⟩ :: Γ₂) b (.val C)) : CDerives Δ Γ (elet e b) (.val C) :=
  .lolliE hs he (.lamV hb)

/-! ### Contexts -/

/-- Every slot consumed. -/
def kill (Γ : Ctx VTy) : Ctx VTy := Γ.map fun s => ⟨s.ty, false⟩

theorem kill_dead : ∀ Γ : Ctx VTy, Ctx.Dead (kill Γ)
  | [] => .nil
  | _ :: Γ => .cons (kill_dead Γ)

/-- `Γ = •, Γ`. -/
theorem split_kill : ∀ Γ : Ctx VTy, Ctx.Split Γ (kill Γ) Γ
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .right (split_kill Γ)
  | ⟨_, false⟩ :: Γ => .dead (split_kill Γ)

/-- `Γ = Γ, •`. -/
theorem split_kill' : ∀ Γ : Ctx VTy, Ctx.Split Γ Γ (kill Γ)
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .left (split_kill' Γ)
  | ⟨_, false⟩ :: Γ => .dead (split_kill' Γ)

/-- A prefix sent to the right. -/
theorem split_append_right : ∀ (L : Ctx VTy) {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.Split Γ Γ₁ Γ₂ →
    Ctx.Split (L ++ Γ) (kill L ++ Γ₁) (L ++ Γ₂)
  | [], _, _, _, h => h
  | ⟨_, true⟩ :: L, _, _, _, h => .right (split_append_right L h)
  | ⟨_, false⟩ :: L, _, _, _, h => .dead (split_append_right L h)

/-- A variable behind a consumed prefix. -/
theorem solo_kill_append : ∀ (L : Ctx VTy) {Γ : Ctx VTy} {i : Nat} {A : VTy},
    Ctx.Solo Γ i A → Ctx.Solo (kill L ++ Γ) (L.length + i) A
  | [], _, i, _, h => by
      show Ctx.Solo _ (0 + i) _
      rw [Nat.zero_add]; exact h
  | s :: L, _, i, _, h => by
      have := Ctx.Solo.there (S := s.ty) (solo_kill_append L h)
      rw [show (s :: L).length + i = (L.length + i) + 1 by simp; omega]
      exact this

/-! ### Shapes as records and variants -/

/-- A field or case: the turns from the root, `false` for left. -/
abbrev FPath := List Bool

namespace Shape

/-- The variant of the leaves: `leaf A ↦ A`, `node s₁ s₂ ↦ sumTy s₁ ⊕ sumTy s₂`.  `[spec §5]` -/
def sumTy : Shape → VTy
  | .leaf A => A
  | .node s₁ s₂ => .sum (sumTy s₁) (sumTy s₂)

/-- A type operation applied at every leaf. -/
def map (F : VTy → VTy) : Shape → Shape
  | .leaf A => .leaf (F A)
  | .node s₁ s₂ => .node (map F s₁) (map F s₂)

/-- The leaf at a path. -/
def get? : Shape → FPath → Option VTy
  | .leaf A, [] => some A
  | .node s₁ _, false :: p => get? s₁ p
  | .node _ s₂, true :: p => get? s₂ p
  | _, _ => none

/-- Every leaf satisfies `P`. -/
def All (P : VTy → Prop) : Shape → Prop
  | .leaf A => P A
  | .node s₁ s₂ => All P s₁ ∧ All P s₂

theorem get?_map (F : VTy → VTy) :
    ∀ (σ : Shape) (p : FPath) {A : VTy}, σ.get? p = some A → (σ.map F).get? p = some (F A)
  | .leaf _, [], _, h => by simp only [get?, Option.some.injEq] at h; subst h; rfl
  | .node s₁ _, false :: p, _, h => get?_map F s₁ p h
  | .node _ s₂, true :: p, _, h => get?_map F s₂ p h
  | .leaf _, _ :: _, _, h => by simp [get?] at h
  | .node _ _, [], _, h => by simp [get?] at h

theorem all_map {P : VTy → Prop} {F : VTy → VTy} (hF : ∀ A, P (F A)) :
    ∀ σ : Shape, (σ.map F).All P
  | .leaf A => hF A
  | .node s₁ s₂ => ⟨all_map hF s₁, all_map hF s₂⟩

theorem All.mono {P Q : VTy → Prop} (h : ∀ A, P A → Q A) :
    ∀ {σ : Shape}, σ.All P → σ.All Q
  | .leaf A, hA => h A hA
  | .node _ _, ⟨h₁, h₂⟩ => ⟨All.mono h h₁, All.mono h h₂⟩

end Shape

/-! ### The reborrow metafunction, outlives and freedom at records and variants

Each is the `⊗` (resp. `⊕`) clause iterated over the tree. -/

/-- `Imm̲ 'b {fields} = {Imm̲ 'b fields}`.  `[spec §5]` -/
theorem immReborrow_valTy (b : Lifetime.Life) :
    ∀ σ : Shape, σ.valTy.immReborrow b = (σ.map (VTy.immReborrow b)).valTy
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [Shape.valTy, VTy.immReborrow, Shape.map, immReborrow_valTy b s₁,
        immReborrow_valTy b s₂]

/-- `Imm̲ 'b ⟨cases⟩ = ⟨Imm̲ 'b cases⟩`.  `[spec §5]` -/
theorem immReborrow_sumTy (b : Lifetime.Life) :
    ∀ σ : Shape, σ.sumTy.immReborrow b = (σ.map (VTy.immReborrow b)).sumTy
  | .leaf _ => rfl
  | .node s₁ s₂ => by
      simp only [Shape.sumTy, VTy.immReborrow, Shape.map, immReborrow_sumTy b s₁,
        immReborrow_sumTy b s₂]

/-- `Δ ⊢ {fields} ⊐ @a` iff every field outlives `@a`. -/
theorem outlives_valTy {Δ : LifeCtx} {a : Lifetime.Life} :
    ∀ σ : Shape, VOutlives Δ a σ.valTy ↔ σ.All (VOutlives Δ a)
  | .leaf _ => Iff.rfl
  | .node s₁ s₂ => by
      constructor
      · intro h
        cases h with
        | tensor h₁ h₂ => exact ⟨(outlives_valTy s₁).1 h₁, (outlives_valTy s₂).1 h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact .tensor ((outlives_valTy s₁).2 h₁) ((outlives_valTy s₂).2 h₂)

/-- `Δ ⊢ ⟨cases⟩ ⊐ @a` iff every case outlives `@a`. -/
theorem outlives_sumTy {Δ : LifeCtx} {a : Lifetime.Life} :
    ∀ σ : Shape, VOutlives Δ a σ.sumTy ↔ σ.All (VOutlives Δ a)
  | .leaf _ => Iff.rfl
  | .node s₁ s₂ => by
      constructor
      · intro h
        cases h with
        | sum h₁ h₂ => exact ⟨(outlives_sumTy s₁).1 h₁, (outlives_sumTy s₂).1 h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact .sum ((outlives_sumTy s₁).2 h₁) ((outlives_sumTy s₂).2 h₂)

theorem vFree_valTy {x : LifeVar} :
    ∀ σ : Shape, σ.All (fun A => ¬ VFree x A) → ¬ VFree x σ.valTy
  | .leaf _, h => h
  | .node s₁ s₂, ⟨h₁, h₂⟩ => by
      simp only [Shape.valTy, VFree, not_or]; exact ⟨vFree_valTy s₁ h₁, vFree_valTy s₂ h₂⟩

theorem vFree_sumTy {x : LifeVar} :
    ∀ σ : Shape, σ.All (fun A => ¬ VFree x A) → ¬ VFree x σ.sumTy
  | .leaf _, h => h
  | .node s₁ s₂, ⟨h₁, h₂⟩ => by
      simp only [Shape.sumTy, VFree, not_or]; exact ⟨vFree_sumTy s₁ h₁, vFree_sumTy s₂ h₂⟩

/-! ### Records -/

/-- A binary tree of terms, one per field. -/
inductive ETree where
  | leaf (e : Expr)
  | node (t₁ t₂ : ETree)

/-- `{e₁, …}`: the pairs in the shape of the tree. -/
def tuple : ETree → Expr
  | .leaf e => e
  | .node t₁ t₂ => .pair (tuple t₁) (tuple t₂)

/-- The premises of `recI`: the context split once per node. -/
inductive RecArgs (Δ : LifeCtx) : Ctx VTy → ETree → Shape → Prop where
  | leaf {Γ e A} : CDerives Δ Γ e (.val A) → RecArgs Δ Γ (.leaf e) (.leaf A)
  | node {Γ Γ₁ Γ₂ t₁ t₂ s₁ s₂} : Ctx.SplitP Γ Γ₁ Γ₂ → RecArgs Δ Γ₁ t₁ s₁ →
      RecArgs Δ Γ₂ t₂ s₂ → RecArgs Δ Γ (.node t₁ t₂) (.node s₁ s₂)

/-- Record introduction.  `[spec §5]` -/
theorem recI {Δ : LifeCtx} {Γ : Ctx VTy} {t : ETree} {σ : Shape} (h : RecArgs Δ Γ t σ) :
    CDerives Δ Γ (tuple t) (.val σ.valTy) := by
  induction h with
  | leaf he => exact he
  | node hs _ _ ih₁ ih₂ => exact .tensorI hs ih₁ ih₂

/-- The context `recLet` hands its body: the left subtree's leaves, then the right's, then the
consumed pair slots.  A leaf's slot is live. -/
def recCtx : Shape → Ctx VTy
  | .leaf A => [⟨A, true⟩]
  | .node s₁ s₂ => recCtx s₁ ++ recCtx s₂ ++ [⟨s₂.valTy, false⟩, ⟨s₁.valTy, false⟩]

/-- `let {x…} = e in body`: `let (l, r) = e`, the right subtree destructured, then the left;
a leaf is bound by `let`. -/
def recLet : Shape → Expr → Expr → Expr
  | .leaf _, e, body => elet e body
  | .node s₁ s₂, e, body =>
      .letpair e (recLet s₂ (.var 0) (recLet s₁ (.var ((recCtx s₂).length + 1)) body))

/-- Record elimination, at a computation type.  `[spec §5]` -/
theorem recE {Δ : LifeCtx} {C : CTy} :
    ∀ (σ : Shape) {Γ Γp Γb : Ctx VTy} {e body : Expr}, Ctx.SplitP Γ Γp Γb →
      CDerives Δ Γp e (.val σ.valTy) → CDerives Δ (recCtx σ ++ Γb) body (.comp C) →
      CDerives Δ Γ (recLet σ e body) (.comp C)
  | .leaf _, _, _, _, _, _, hs, he, hb => .bind hs (.ret he) hb
  | .node s₁ s₂, _, _, Γb, _, body, hs, he, hb => by
      have hv : Ctx.Solo (kill (recCtx s₂) ++ ⟨s₂.valTy, false⟩ :: ⟨s₁.valTy, true⟩ :: kill Γb)
          ((recCtx s₂).length + 1) s₁.valTy :=
        solo_kill_append (recCtx s₂) (Ctx.Solo.there (.here (kill_dead Γb)))
      have hb' : CDerives Δ (recCtx s₁ ++ (recCtx s₂ ++ ⟨s₂.valTy, false⟩ :: ⟨s₁.valTy, false⟩ :: Γb))
          body (.comp C) := by simpa [recCtx, List.append_assoc] using hb
      exact .tensorE hs he
        (recE s₂ (.left (.right (split_kill Γb))) (.var (.here (.cons (kill_dead Γb).toP)))
          (recE s₁ (split_append_right (recCtx s₂) (.dead (.left (split_kill Γb)))).toP (.var hv.toP) hb'))

/-- Record elimination, at a value type. -/
theorem recEV {Δ : LifeCtx} {T : VTy} (σ : Shape) {Γ Γp Γb : Ctx VTy} {e body : Expr}
    (hs : Ctx.SplitP Γ Γp Γb) (he : CDerives Δ Γp e (.val σ.valTy))
    (hb : CDerives Δ (recCtx σ ++ Γb) body (.val T)) :
    CDerives Δ Γ (recLet σ e body) (.val T) :=
  .ofRet (recE σ hs he (.ret hb))

/-! ### Affine types -/

/-- The value types a closed term consumes: `1`, `0`, `⊗`, `⊕`, `Imm`, `Mut`, `Unk`, `!A`. -/
inductive Affine : VTy → Prop where
  | unit : Affine .unit
  | zero : Affine .zero
  | tensor {A B} : Affine A → Affine B → Affine (.tensor A B)
  | sum {A B} : Affine A → Affine B → Affine (.sum A B)
  | imm {a A} : Affine (.imm a A)
  | «mut» {a A} : Affine (.mut a A)
  | unk : Affine .unk
  | bang {A} : Affine (.bang A)
  /-- `I32`, `I64`, dropped as persistent slots.  `[spec §8]` -/
  | int {w} : Affine (.int w)

/-- The closed consumer of an affine type. -/
def dropT : VTy → Expr
  | .unit => .val (.lam (.var 0))
  | .zero => .val (.lam (absurdE (.var 0)))
  | .tensor A B => .val (.lam (.letpair (.var 0)
      (.seq (.app (dropT A) (.var 1)) (.app (dropT B) (.var 0)))))
  | .sum A B => .val (.lam (.case (.var 0) (.app (dropT A) (.var 0)) (.app (dropT B) (.var 0))))
  | _ => forget

theorem dropT_wf {Δ : LifeCtx} {A : VTy} (hA : Affine A) :
    ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ (dropT A) (.val (.lolli A .unit)) := by
  induction hA with
  | unit => intro Γ hΓ; exact .lamV (.var (.here hΓ))
  | zero =>
      intro Γ hΓ
      exact .thunkV rfl (.lam (.zeroE (.left (deadSplit hΓ)) (.var (.here hΓ))))
  | tensor _ _ ih₁ ih₂ =>
      intro Γ hΓ
      exact .lamV (.letpairV (.left (deadSplit hΓ)) (.var (.here hΓ))
        (.seqV (.right (.left (.dead (deadSplit hΓ))))
          (.lolliE (.dead (.left (.dead (deadSplit hΓ)))) (.var (.there (.here (.cons hΓ))))
            (ih₁ (.cons (.cons (.cons hΓ)))))
          (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ))))
            (ih₂ (.cons (.cons (.cons hΓ)))))))
  | sum _ _ ih₁ ih₂ =>
      intro Γ hΓ
      exact .lamV (.caseV (.left (deadSplit hΓ)) (.var (.here hΓ))
        (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ))) (ih₁ (.cons (.cons hΓ))))
        (.lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ))) (ih₂ (.cons (.cons hΓ)))))
  | imm => intro Γ hΓ; exact .forgetImm hΓ
  | «mut» => intro Γ hΓ; exact .forgetMut hΓ
  | unk => intro Γ hΓ; exact .forgetUnk hΓ
  | bang => intro Γ hΓ; exact .forgetBang hΓ
  | int => intro Γ hΓ; exact .lamV (.unitI (.drop rfl hΓ.toP))

/-- The spine of `⊗`, `⊕` and `[@a]` holds no `μ`, no type variable and no array. -/
def VTy.SpineMuFree : VTy → Prop
  | .tensor A B => A.SpineMuFree ∧ B.SpineMuFree
  | .sum A B => A.SpineMuFree ∧ B.SpineMuFree
  | .box _ A => A.SpineMuFree
  | .tvar _ => False
  | .mu _ => False
  | .fam _ => False
  | _ => True

/-- `Imm̲ 'b A` is affine at a `μ`-free spine: `Imm̲` sends `Ref` and `Mut` to `Imm`, `U C` to
`Unk`, and strips `[@a]`. -/
theorem affine_immReborrow (b : Lifetime.Life) : ∀ A : VTy, A.SpineMuFree →
    Affine (A.immReborrow b)
  | .unit, _ => .unit
  | .int _, _ => .int
  | .zero, _ => .zero
  | .tensor A B, ⟨h₁, h₂⟩ => .tensor (affine_immReborrow b A h₁) (affine_immReborrow b B h₂)
  | .sum A B, ⟨h₁, h₂⟩ => .sum (affine_immReborrow b A h₁) (affine_immReborrow b B h₂)
  | .thunk _, _ => .unk
  | .opq _, _ => .unk
  | .ref _, _ => .imm
  | .imm _ _, _ => .imm
  | .mut _ _, _ => .imm
  | .box _ A, h => affine_immReborrow b A h
  | .bang _, _ => .bang
  | .unk, _ => .unk
  | .fam _, h => h.elim

theorem affine_valTy : ∀ σ : Shape, σ.All Affine → Affine σ.valTy
  | .leaf _, h => h
  | .node s₁ s₂, ⟨h₁, h₂⟩ => .tensor (affine_valTy s₁ h₁) (affine_valTy s₂ h₂)

/-! ### Projection -/

/-- `e.p`: the field at `p`, every other field consumed. -/
def getAt : Shape → FPath → Expr → Expr
  | .node s₁ s₂, false :: p, e =>
      .letpair e (.seq (.app (dropT s₂.valTy) (.var 0)) (getAt s₁ p (.var 1)))
  | .node s₁ s₂, true :: p, e =>
      .letpair e (.seq (.app (dropT s₁.valTy) (.var 1)) (getAt s₂ p (.var 0)))
  | _, _, e => e

/-- Projection, for a record whose fields are affine.  `[spec §5]` -/
theorem getAt_wf {Δ : LifeCtx} :
    ∀ (σ : Shape) (p : FPath) {A : VTy} {Γ : Ctx VTy} {e : Expr},
      σ.get? p = some A → σ.All Affine → CDerives Δ Γ e (.val σ.valTy) →
      CDerives Δ Γ (getAt σ p e) (.val A)
  | .leaf _, [], _, _, _, hp, _, he => by
      simp only [Shape.get?, Option.some.injEq] at hp; subst hp; exact he
  | .leaf _, _ :: _, _, _, _, hp, _, _ => by simp [Shape.get?] at hp
  | .node _ _, [], _, _, _, hp, _, _ => by simp [Shape.get?] at hp
  | .node s₁ s₂, false :: p, _, Γ, _, hp, ⟨ha₁, ha₂⟩, he => by
      have kd := kill_dead Γ
      exact .letpairV (split_kill' Γ) he
        (.seqV (.left (.right (deadSplit kd)))
          (.lolliE (.left (.dead (deadSplit kd))) (.var (.here (.cons kd)))
            (dropT_wf (affine_valTy s₂ ha₂) (.cons (.cons kd))))
          (getAt_wf s₁ p hp ha₁ (.var (.there (.here kd)))))
  | .node s₁ s₂, true :: p, _, Γ, _, hp, ⟨ha₁, ha₂⟩, he => by
      have kd := kill_dead Γ
      exact .letpairV (split_kill' Γ) he
        (.seqV (.right (.left (deadSplit kd)))
          (.lolliE (.dead (.left (deadSplit kd))) (.var (.there (.here kd)))
            (dropT_wf (affine_valTy s₁ ha₁) (.cons (.cons kd))))
          (getAt_wf s₂ p hp ha₂ (.var (.here (.cons kd)))))

/-! ### Variants -/

/-- `p e`: the injections along the path. -/
def injAt : FPath → Expr → Expr
  | [], e => e
  | false :: p, e => .inj₁ (injAt p e)
  | true :: p, e => .inj₂ (injAt p e)

theorem injAt_wf {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ (σ : Shape) (p : FPath) {A : VTy}, σ.get? p = some A → CDerives Δ Γ e (.val A) →
      CDerives Δ Γ (injAt p e) (.val σ.sumTy)
  | .leaf _, [], _, hp, he => by
      simp only [Shape.get?, Option.some.injEq] at hp; subst hp; exact he
  | .leaf _, _ :: _, _, hp, _ => by simp [Shape.get?] at hp
  | .node _ _, [], _, hp, _ => by simp [Shape.get?] at hp
  | .node s₁ _, false :: p, _, hp, he => .sumI₁ (injAt_wf s₁ p hp he)
  | .node _ s₂, true :: p, _, hp, he => .sumI₂ (injAt_wf s₂ p hp he)

/-- `case e {…}`: nested `case` in the shape of the tree, a leaf's branch bound by `let`. -/
def vcase : Expr → ETree → Expr
  | e, .leaf b => elet e b
  | e, .node t₁ t₂ => .case e (vcase (.var 0) t₁) (vcase (.var 0) t₂)

/-- The premises of `vcase_wf`.  A branch sees its payload at index 0, then the consumed
intermediate sums, innermost first, then the context. -/
inductive Branches (Δ : LifeCtx) (C : CTy) : Ctx VTy → Shape → ETree → Prop where
  | leaf {Γ A b} : CDerives Δ (⟨A, true⟩ :: Γ) b (.comp C) → Branches Δ C Γ (.leaf A) (.leaf b)
  | node {Γ s₁ s₂ t₁ t₂} : Branches Δ C (⟨s₁.sumTy, false⟩ :: Γ) s₁ t₁ →
      Branches Δ C (⟨s₂.sumTy, false⟩ :: Γ) s₂ t₂ → Branches Δ C Γ (.node s₁ s₂) (.node t₁ t₂)

/-- Variant elimination.  `[spec §5]` -/
theorem vcase_wf {Δ : LifeCtx} {C : CTy} {Γb : Ctx VTy} {σ : Shape} {t : ETree}
    (hB : Branches Δ C Γb σ t) :
    ∀ {Γ Γs : Ctx VTy} {e : Expr}, Ctx.SplitP Γ Γs Γb → CDerives Δ Γs e (.val σ.sumTy) →
      CDerives Δ Γ (vcase e t) (.comp C) := by
  induction hB with
  | leaf hb => intro Γ Γs e hs he; exact .bind hs (.ret he) hb
  | @node Γb s₁ s₂ t₁ t₂ _ _ ih₁ ih₂ =>
      intro Γ Γs e hs he
      exact .sumE hs he
        (ih₁ (.left (split_kill Γb)) (.var (.here (kill_dead Γb).toP)))
        (ih₂ (.left (split_kill Γb)) (.var (.here (kill_dead Γb).toP)))

/-! ### Reading a field through an immutable borrow -/

/-- `withload e (Λ. λr. let x = r.p in body)`, at the load lifetime `'y`. -/
def loadField (σ : Shape) (p : FPath) (y : LifeVar) (e body : Expr) : Expr :=
  .app (.app withload e)
    (.val (.lam (.val (.lam (elet (getAt (σ.map (VTy.immReborrow (.var y))) p (.var 0)) body)))))

/-- `∀I`'s side conditions for a fresh `'y ⊏ ⊓Δ` at a dead context. -/
theorem allI_fresh {Δ : LifeCtx} {Γ : Ctx VTy} {S : VTy} {M : Expr} {y : LifeVar} {C : CTy}
    (hΔ : Δ.Ok) (hy : Δ.find? y = none) (hΓ : Ctx.Dead Γ)
    (h : CDerives (Δ.extend y Δ.meetOfDom) (⟨S, false⟩ :: Γ) M (.comp C)) :
    CDerives Δ Γ (.val (.lam M)) (.comp (.all y Δ.meetOfDom C)) :=
  .allI (Lifetime.Life.mentions_false_of_wf hy (Lifetime.meetOfDomL_wf Δ.entries))
    (fun _ _ h => hΔ.bound_mentions_false hy h) (dead_noLive hΓ) h

/-- Reading field `p` of `e : Imm @a {…}`.  The body runs at `'y ⊏ ⊓Δ` with the field's image
`Imm̲ 'y A` at index 0 and returns `['y] B`; the other fields' images are consumed by
`getAt`, which needs them affine.  `[spec §5]` -/
theorem loadField_wf {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {σ : Shape} {p : FPath}
    {A : VTy} {y : LifeVar} {e body : Expr} {B : VTy} (hΔ : Δ.Ok)
    (he : CDerives Δ Γ e (.val (.imm a σ.valTy))) (hp : σ.get? p = some A)
    (haff : (σ.map (VTy.immReborrow (.var y))).All Affine)
    (hy : Δ.find? y = none) (hf₁ : ¬ VFree y σ.valTy) (hf₂ : ¬ VFree y B)
    (hb : CDerives (Δ.extend y Δ.meetOfDom)
      (⟨A.immReborrow (.var y), true⟩ :: ⟨σ.valTy.immReborrow (.var y), false⟩ ::
        ⟨.unit, false⟩ :: kill Γ) body (.val (.box (.var y) B))) :
    CDerives Δ Γ (loadField σ p y e body) (.val B) := by
  have kd := kill_dead Γ
  refine .lolliE (split_kill Γ).toP ?_ (.lolliE (split_kill' Γ).toP he (.withload y kd.toP hy hf₁ hf₂))
  refine .thunkV rfl (allI_fresh (S := .unit) hΔ hy kd (.ret (.lamV ?_)))
  refine .eletV (.left (.dead (deadSplit kd))) ?_ hb
  refine getAt_wf _ p (Shape.get?_map _ σ p hp) haff ?_
  rw [← immReborrow_valTy]
  exact .var (.here (.cons kd))

/-! ### Matching on a variant through an immutable borrow -/

/-- `withload e (Λ. λv. case v {…})`. -/
def loadCase (e : Expr) (t : ETree) : Expr :=
  .app (.app withload e) (.val (.lam (.val (.lam (vcase (.var 0) t)))))

/-- Matching on `e : Imm @a ⟨…⟩`.  Branch `p` runs at `'y ⊏ ⊓Δ` with the case's image
`Imm̲ 'y A` and returns `['y] B`.  `[spec §5]` -/
theorem loadCase_wf {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {σ : Shape} {y : LifeVar}
    {e : Expr} {t : ETree} {B : VTy} (hΔ : Δ.Ok)
    (he : CDerives Δ Γ e (.val (.imm a σ.sumTy))) (hy : Δ.find? y = none)
    (hf₁ : ¬ VFree y σ.sumTy) (hf₂ : ¬ VFree y B)
    (hB : Branches (Δ.extend y Δ.meetOfDom) (.ret (.box (.var y) B))
      (⟨σ.sumTy.immReborrow (.var y), false⟩ :: ⟨.unit, false⟩ :: kill Γ)
      (σ.map (VTy.immReborrow (.var y))) t) :
    CDerives Δ Γ (loadCase e t) (.val B) := by
  have kd := kill_dead Γ
  refine .lolliE (split_kill Γ).toP ?_ (.lolliE (split_kill' Γ).toP he (.withload y kd.toP hy hf₁ hf₂))
  refine .thunkV rfl (allI_fresh (S := .unit) hΔ hy kd (.ret (.thunkV rfl (.lam ?_))))
  refine vcase_wf hB (.left (.dead (deadSplit kd))) ?_
  rw [← immReborrow_sumTy]
  exact .var (.here (.cons kd))

/-! ### Updating a field through a mutable borrow -/

/-- `λr. …`: `g` run on the field at `p`, the record rebuilt around its result. -/
def modAt : Shape → FPath → Expr → Expr
  | .node s₁ _, false :: p, g =>
      .val (.lam (.letpair (.var 0) (.letpair (.app (modAt s₁ p g) (.var 1))
        (.pair (.pair (.var 1) (.var 2)) (.var 0)))))
  | .node _ s₂, true :: p, g =>
      .val (.lam (.letpair (.var 0) (.letpair (.app (modAt s₂ p g) (.var 0))
        (.pair (.pair (.var 3) (.var 1)) (.var 0)))))
  | _, _, g => g

theorem modAt_wf {Δ : LifeCtx} {B : VTy} {g : Expr} :
    ∀ (σ : Shape) (p : FPath) {A : VTy}, σ.get? p = some A →
      (∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ g (.val (.lolli A (.tensor A B)))) →
      ∀ {Γ : Ctx VTy}, Ctx.Dead Γ →
        CDerives Δ Γ (modAt σ p g) (.val (.lolli σ.valTy (.tensor σ.valTy B)))
  | .leaf _, [], _, hp, hg, _, D => by
      simp only [Shape.get?, Option.some.injEq] at hp; subst hp; exact hg D
  | .leaf _, _ :: _, _, hp, _, _, _ => by simp [Shape.get?] at hp
  | .node _ _, [], _, hp, _, _, _ => by simp [Shape.get?] at hp
  | .node s₁ s₂, false :: p, _, hp, hg, _, D =>
      .lamV (.letpairV (.left (deadSplit D)) (.var (.here D))
        (.letpairV (.right (.left (.dead (deadSplit D))))
          (.lolliE (.dead (.left (.dead (deadSplit D)))) (.var (.there (.here (.cons D))))
            (modAt_wf s₁ p hp hg (.cons (.cons (.cons D)))))
          (.tensorI (.right (.left (.left (.dead (.dead (deadSplit D))))))
            (.tensorI (.dead (.left (.right (.dead (.dead (deadSplit D))))))
              (.var (.there (.here (.cons (.cons (.cons D))))))
              (.var (.there (.there (.here (.cons (.cons D)))))))
            (.var (.here (.cons (.cons (.cons (.cons D)))))))))
  | .node s₁ s₂, true :: p, _, hp, hg, _, D =>
      .lamV (.letpairV (.left (deadSplit D)) (.var (.here D))
        (.letpairV (.left (.right (.dead (deadSplit D))))
          (.lolliE (.left (.dead (.dead (deadSplit D)))) (.var (.here (.cons (.cons D))))
            (modAt_wf s₂ p hp hg (.cons (.cons (.cons D)))))
          (.tensorI (.right (.left (.dead (.left (.dead (deadSplit D))))))
            (.tensorI (.dead (.right (.dead (.left (.dead (deadSplit D))))))
              (.var (.there (.there (.there (.here (.cons D))))))
              (.var (.there (.here (.cons (.cons (.cons D)))))))
            (.var (.here (.cons (.cons (.cons (.cons D)))))))))

/-- `withswap m (modAt σ p g)`. -/
def swapField (σ : Shape) (p : FPath) (m g : Expr) : Expr :=
  .app (.app withswap m) (modAt σ p g)

/-- Field-level `withswap`: `Mut @a {…} ⊸ (A ⊸ A ⊗ B) ⊸ Mut @a {…} ⊗ B`, derived.  `[spec §5]` -/
theorem swapField_wf {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {σ : Shape} {p : FPath}
    {A : VTy} {m g : Expr} {B : VTy}
    (hm : CDerives Δ Γ m (.val (.mut a σ.valTy))) (hp : σ.get? p = some A)
    (hg : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ g (.val (.lolli A (.tensor A B)))) :
    CDerives Δ Γ (swapField σ p m g) (.val (.tensor (.mut a σ.valTy) B)) :=
  .lolliE (split_kill Γ) (modAt_wf σ p hp hg (kill_dead Γ))
    (.lolliE (split_kill' Γ).toP hm (.withswap (kill_dead Γ).toP))

/-! ### Soundness: the Fundamental Property, unchanged -/

theorem loadField_sem {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {σ : Shape} {p : FPath}
    {A : VTy} {y : LifeVar} {e body : Expr} {B : VTy} (hΔ : Δ.Ok)
    (he : CDerives Δ Γ e (.val (.imm a σ.valTy))) (hp : σ.get? p = some A)
    (haff : (σ.map (VTy.immReborrow (.var y))).All Affine)
    (hy : Δ.find? y = none) (hf₁ : ¬ VFree y σ.valTy) (hf₂ : ¬ VFree y B)
    (hb : CDerives (Δ.extend y Δ.meetOfDom)
      (⟨A.immReborrow (.var y), true⟩ :: ⟨σ.valTy.immReborrow (.var y), false⟩ ::
        ⟨.unit, false⟩ :: kill Γ) body (.val (.box (.var y) B))) :
    SemV Δ Γ (loadField σ p y e body) B :=
  fundamentalC (loadField_wf hΔ he hp haff hy hf₁ hf₂ hb)

theorem swapField_sem {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {σ : Shape} {p : FPath}
    {A : VTy} {m g : Expr} {B : VTy}
    (hm : CDerives Δ Γ m (.val (.mut a σ.valTy))) (hp : σ.get? p = some A)
    (hg : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ Γ g (.val (.lolli A (.tensor A B)))) :
    SemV Δ Γ (swapField σ p m g) (.tensor (.mut a σ.valTy) B) :=
  fundamentalC (swapField_wf hm hp hg)

/-! ### The reborrowing facts at records and variants -/

/-- 6.131 at records: `[α] vShape {fields} ⊨ ↺_α vShape {Imm̲ 'x fields}`. -/
theorem reborrow_vShape_valTy {α : Life} {x : LifeVar} {δ : LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) (σ : Shape) (v : Val) :
    box α (vShape σ.valTy δ v) ⊨
      reborrow α (vShape (σ.map (VTy.immReborrow (.var x))).valTy δ v) := by
  rw [← immReborrow_valTy]; exact reborrow_vShape hδ _ v

/-- 6.131 at variants. -/
theorem reborrow_vShape_sumTy {α : Life} {x : LifeVar} {δ : LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) (σ : Shape) (v : Val) :
    box α (vShape σ.sumTy δ v) ⊨
      reborrow α (vShape (σ.map (VTy.immReborrow (.var x))).sumTy δ v) := by
  rw [← immReborrow_sumTy]; exact reborrow_vShape hδ _ v

/-- 6.60 at records: a record whose fields all outlive `@a` holds a resource in `@a`'s
stratum. -/
theorem vC_outlives_valTy {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {σ : Shape} (hσ : σ.All (VOutlives Δ a))
    (b : Bool) : ∀ ls v ρ, vC b σ.valTy ls δ v ρ → BoLo.Outlives ρ α :=
  vC_outlives hδ ha ((outlives_valTy σ).2 hσ) b

/-- 6.60 at variants. -/
theorem vC_outlives_sumTy {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {σ : Shape} (hσ : σ.All (VOutlives Δ a))
    (b : Bool) : ∀ ls v ρ, vC b σ.sumTy ls δ v ρ → BoLo.Outlives ρ α :=
  vC_outlives hδ ha ((outlives_sumTy σ).2 hσ) b

end BoCa.Fig16.LogRel.Core

end
