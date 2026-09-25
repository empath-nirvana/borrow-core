import Paper.Examples.Programs
import Support.TypedWorld.ReborrowShapes

/-!
# Records and variants as derived forms

Labelled records and variants are encoded in BoCa's own formers, and every rule below is a
derived rule of `DerivesWf`: no constructor is added, so the Fundamental Property
(`Fig16.LogRel.Typed.fundamental`) and adequacy apply to them unchanged.

    {l₁ : T₁, …, lₙ : Tₙ}      ≜  T₁ ⊗ (T₂ ⊗ (… ⊗ (Tₙ ⊗ 1)))
    ⟨l₁ : T₁ | … | lₙ : Tₙ⟩    ≜  T₁ ⊕ (T₂ ⊕ (… ⊕ Tₙ))          (n ≥ 1)

The empty record is `1`.  A variant has at least one case: BoCa has no empty type.  Labels are
names only; a field is found by its position.

| form | term | rule |
|---|---|---|
| `{l₁ = e₁, …, lₙ = eₙ}` | `tuple` | `recI` |
| `let {l₁ = x₁, …} = e in b` | `recLet` | `recE` |
| `e.lᵢ` (other fields affine) | `getAt` | `getAt_wf` |
| `lᵢ e` | `injAt` | `injAt_wf` |
| `case e {l₁ x ⇒ b₁ ∣ …}` | `vcase` | `vcase_wf` |
-/

noncomputable section

namespace BoCa.Records
open BoCa BoCa.Lifetime BoCa.Programs

/-! ## Types -/

/-- A field: a label and its type. -/
abbrev Field := String × Ty

/-- `{l₁ : T₁, …, lₙ : Tₙ} ≜ T₁ ⊗ (… ⊗ (Tₙ ⊗ 1))`. -/
def recTy : List Field → Ty
  | [] => .unit
  | f :: fs => .tensor f.2 (recTy fs)

/-- `⟨f | g₁ | … | gₙ⟩ ≜ T_f ⊕ (T_{g₁} ⊕ (… ⊕ T_{gₙ}))`; the first case is separate
because there is no empty variant. -/
def varTy (f : Field) : List Field → Ty
  | [] => f.2
  | g :: gs => .sum f.2 (varTy g gs)

/-- A type operation applied fieldwise, labels kept. -/
def mapF (F : Ty → Ty) (fs : List Field) : List Field := fs.map fun f => (f.1, F f.2)

@[simp] theorem mapF_nil (F : Ty → Ty) : mapF F [] = [] := rfl

@[simp] theorem mapF_cons (F : Ty → Ty) (f : Field) (fs : List Field) :
    mapF F (f :: fs) = (f.1, F f.2) :: mapF F fs := rfl

/-! ## The reborrow metafunction at records and variants

`Imm̲ 'b` acts fieldwise.  Neither clause is new: each is the `⊗` (resp. `⊕`) clause of
`Ty.immReborrow` (`[TR]` p. 3, row 2.49) iterated, with the `1` clause at the tail. -/

/-- `Imm̲ 'b {lᵢ : Tᵢ} = {lᵢ : Imm̲ 'b Tᵢ}`. -/
theorem immReborrow_recTy (b : Life) :
    ∀ fs, (recTy fs).immReborrow b = recTy (mapF (Ty.immReborrow b) fs)
  | [] => rfl
  | f :: fs => by
      show Ty.tensor (f.2.immReborrow b) ((recTy fs).immReborrow b) = _
      rw [immReborrow_recTy b fs]; rfl

/-- `Imm̲ 'b ⟨lᵢ : Tᵢ⟩ = ⟨lᵢ : Imm̲ 'b Tᵢ⟩`. -/
theorem immReborrow_varTy (b : Life) :
    ∀ (f : Field) (gs : List Field),
      (varTy f gs).immReborrow b = varTy (f.1, f.2.immReborrow b) (mapF (Ty.immReborrow b) gs)
  | _, [] => rfl
  | f, g :: gs => by
      show Ty.sum (f.2.immReborrow b) ((varTy g gs).immReborrow b) = _
      rw [immReborrow_varTy b g gs]; rfl

/-! ## Outlives and scoping at records and variants

`Δ ⊢ {lᵢ : Tᵢ} ⊐ @a` iff every field outlives `@a`: the `⊗` and `1` rules of `[TR]` p. 2
(rows 2.31, 2.32) iterated.  Likewise for variants with the `⊕` rule (row 2.33). -/

theorem outlives_recTy {Δ : LifeCtx} {a : Life} :
    ∀ fs : List Field, OutlivesRules Δ a (recTy fs) ↔ ∀ f ∈ fs, OutlivesRules Δ a f.2
  | [] => ⟨fun _ _ h => absurd h (by simp), fun _ => .unit⟩
  | f :: fs => by
      constructor
      · intro h
        cases h with
        | tensor h₁ h₂ =>
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hg
            · exact h₁
            · exact (outlives_recTy fs).1 h₂ g hg
      · intro h
        exact .tensor (h f (by simp)) ((outlives_recTy fs).2 fun g hg => h g (by simp [hg]))

theorem outlives_varTy {Δ : LifeCtx} {a : Life} :
    ∀ (f : Field) (gs : List Field),
      OutlivesRules Δ a (varTy f gs) ↔ OutlivesRules Δ a f.2 ∧ ∀ g ∈ gs, OutlivesRules Δ a g.2
  | f, [] => ⟨fun h => ⟨h, fun _ h => absurd h (by simp)⟩, fun h => h.1⟩
  | f, g :: gs => by
      constructor
      · intro h
        cases h with
        | sum h₁ h₂ =>
            obtain ⟨hg, hgs⟩ := (outlives_varTy g gs).1 h₂
            refine ⟨h₁, fun k hk => ?_⟩
            rcases List.mem_cons.mp hk with rfl | hk
            · exact hg
            · exact hgs k hk
      · rintro ⟨hf, hgs⟩
        exact .sum hf ((outlives_varTy g gs).2 ⟨hgs g (by simp), fun k hk => hgs k (by simp [hk])⟩)

theorem scopedB_recTy {Δ : LifeCtx} :
    ∀ fs : List Field, (recTy fs).scopedB Δ = true ↔ ∀ f ∈ fs, f.2.scopedB Δ = true
  | [] => by simp [recTy, Ty.scopedB]
  | f :: fs => by
      simp only [recTy, Ty.scopedB, Bool.and_eq_true, scopedB_recTy fs, List.mem_cons,
        forall_eq_or_imp]

theorem scopedB_varTy {Δ : LifeCtx} :
    ∀ (f : Field) (gs : List Field),
      (varTy f gs).scopedB Δ = true ↔ f.2.scopedB Δ = true ∧ ∀ g ∈ gs, g.2.scopedB Δ = true
  | f, [] => by simp [varTy]
  | f, g :: gs => by
      simp only [varTy, Ty.scopedB, Bool.and_eq_true, scopedB_varTy g gs, List.mem_cons,
        forall_eq_or_imp]

/-- `Imm̲ 'b T` is scoped wherever `T` and `'b` are. -/
theorem scopedB_immReborrow {Δ : LifeCtx} {b : Life} (hb : b.wf Δ = true) :
    ∀ T : Ty, T.scopedB Δ = true → (T.immReborrow b).scopedB Δ = true := by
  intro T
  induction T with
  | unit => intro _; rfl
  | unk => intro _; rfl
  | lolli _ _ _ _ => intro _; rfl
  | all _ _ _ _ => intro _; rfl
  | bang T _ => intro h; exact h
  | ref T _ => intro h; simp only [Ty.immReborrow, Ty.scopedB, hb, Bool.true_and]; exact h
  | imm a T _ => intro h; exact h
  | «mut» a T _ =>
      intro h; simp only [Ty.scopedB, Bool.and_eq_true] at h
      simp only [Ty.immReborrow, Ty.scopedB, hb, Bool.true_and]; exact h.2
  | box a T ih => intro h; simp only [Ty.scopedB, Bool.and_eq_true] at h; exact ih h.2
  | sum T₁ T₂ ih₁ ih₂ =>
      intro h; simp only [Ty.scopedB, Bool.and_eq_true] at h
      simp only [Ty.immReborrow, Ty.scopedB, Bool.and_eq_true]; exact ⟨ih₁ h.1, ih₂ h.2⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro h; simp only [Ty.scopedB, Bool.and_eq_true] at h
      simp only [Ty.immReborrow, Ty.scopedB, Bool.and_eq_true]; exact ⟨ih₁ h.1, ih₂ h.2⟩

/-! ## Contexts -/

/-- Every slot consumed. -/
def kill (Γ : Ctx Ty) : Ctx Ty := Γ.map fun s => ⟨s.ty, false⟩

theorem kill_dead : ∀ Γ : Ctx Ty, Ctx.Dead (kill Γ)
  | [] => .nil
  | _ :: Γ => .cons (kill_dead Γ)

/-- `Γ = •, Γ`. -/
theorem split_kill : ∀ Γ : Ctx Ty, Ctx.Split Γ (kill Γ) Γ
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .right (split_kill Γ)
  | ⟨_, false⟩ :: Γ => .dead (split_kill Γ)

/-- `Γ = Γ, •`. -/
theorem split_kill' : ∀ Γ : Ctx Ty, Ctx.Split Γ Γ (kill Γ)
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .left (split_kill' Γ)
  | ⟨_, false⟩ :: Γ => .dead (split_kill' Γ)

theorem kill_append (Γ₁ Γ₂ : Ctx Ty) : kill (Γ₁ ++ Γ₂) = kill Γ₁ ++ kill Γ₂ := List.map_append ..

/-! ## Records -/

/-- `{e₁, …, eₙ} ≜ (e₁, (…, (eₙ, ())))`. -/
def tuple : List Expr → Expr
  | [] => unit'
  | e :: es => .pair e (tuple es)

/-- The premises of `recI`: the context split once per field. -/
inductive RecArgs (Δ : LifeCtx) : Ctx Ty → List Expr → List Field → Prop where
  | nil {Γ} : Ctx.Dead Γ → RecArgs Δ Γ [] []
  | cons {Γ Γ₁ Γ₂ e es f fs} : Ctx.Split Γ Γ₁ Γ₂ → DerivesWf Δ Γ₁ e f.2 →
      RecArgs Δ Γ₂ es fs → RecArgs Δ Γ (e :: es) (f :: fs)

/-- Record introduction: `Δ; Γᵢ ⊢ eᵢ : Tᵢ` ⟹ `Δ; Γ₁,…,Γₙ ⊢ {lᵢ = eᵢ} : {lᵢ : Tᵢ}`. -/
theorem recI {Δ : LifeCtx} {Γ : Ctx Ty} {es : List Expr} {fs : List Field}
    (h : RecArgs Δ Γ es fs) : DerivesWf Δ Γ (tuple es) (recTy fs) := by
  induction h with
  | nil hΓ => exact .unitI hΓ
  | cons hs he _ ih => exact .tensorI hs he ih

/-- `let {l₁ = x₁, …, lₙ = xₙ} = e in body`: `n` nested `let (x, y) = …`, the last tail
consumed by `;`. -/
def recLet : Nat → Expr → Expr → Expr
  | 0, e, body => .seq e body
  | n + 1, e, body => .letpair e (recLet n (.var 0) body)

/-- The context `recLet` hands its body, innermost first.  Field `k` of `n` (from 1) is
at index `2(n − k) + 1`; the even positions hold the consumed tails. -/
def recCtx : List Field → Ctx Ty
  | [] => []
  | f :: fs => recCtx fs ++ [⟨recTy fs, false⟩, ⟨f.2, true⟩]

/-- Record elimination. -/
theorem recE {Δ : LifeCtx} {T : Ty} {body : Expr} :
    ∀ (fs : List Field) {Γ Γp Γb : Ctx Ty} {e : Expr}, Ctx.Split Γ Γp Γb →
      (recTy fs).scopedB Δ = true → DerivesWf Δ Γp e (recTy fs) →
      DerivesWf Δ (recCtx fs ++ Γb) body T → DerivesWf Δ Γ (recLet fs.length e body) T
  | [], _, _, _, _, hs, _, hp, hb => .unitE hs hp hb
  | f :: fs, _, _, Γb, _, hs, hwf, hp, hb => by
      have hwf' := hwf
      simp only [recTy, Ty.scopedB, Bool.and_eq_true] at hwf'
      refine .tensorE hs hwf hp ?_
      refine recE fs (Γp := ⟨recTy fs, true⟩ :: ⟨f.2, false⟩ :: kill Γb)
        (Γb := ⟨recTy fs, false⟩ :: ⟨f.2, true⟩ :: Γb)
        (.left (.right (split_kill Γb))) hwf'.2 (.var (.here (.cons (kill_dead Γb)))) ?_
      simpa [recCtx, List.append_assoc] using hb

/-! ## Affine types and projection

A type is affine here when a closed term consumes it: `1`, `⊗`, `⊕`, `Imm`, `Mut`, `Unk`
and `!T`, each through `forget` or a structural walk.  Every `Imm̲ 'b T` is affine
(`affine_immReborrow`), so a record read through an immutable borrow can be projected. -/

inductive Affine : Ty → Prop where
  | unit : Affine .unit
  | tensor {T₁ T₂} : Affine T₁ → Affine T₂ → Affine (.tensor T₁ T₂)
  | sum {T₁ T₂} : Affine T₁ → Affine T₂ → Affine (.sum T₁ T₂)
  | imm {a T} : Affine (.imm a T)
  | mut {a T} : Affine (.mut a T)
  | unk : Affine .unk
  | bang {T} : Affine (.bang T)

/-- The closed consumer of an affine type. -/
def dropT : Ty → Expr
  | .unit => lam (.var 0)
  | .tensor T₁ T₂ => lam (.letpair (.var 0) (.seq (.app (dropT T₁) (.var 1)) (.app (dropT T₂) (.var 0))))
  | .sum T₁ T₂ => lam (.case (.var 0) (.app (dropT T₁) (.var 0)) (.app (dropT T₂) (.var 0)))
  | _ => forget

theorem dropT_wf {Δ : LifeCtx} {T : Ty} (hT : Affine T) (hwf : T.scopedB Δ = true) :
    ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → DerivesWf Δ Γ (dropT T) (.lolli T .unit) := by
  induction hT with
  | unit => intro Γ hΓ; exact .lolliI rfl (.var (.here hΓ))
  | tensor _ _ ih₁ ih₂ =>
      intro Γ hΓ
      simp only [Ty.scopedB, Bool.and_eq_true] at hwf
      exact .lolliI (by simp [Ty.scopedB, hwf.1, hwf.2])
        (.tensorE (.left hΓ.split) (by simp [Ty.scopedB, hwf.1, hwf.2]) (.var (.here hΓ))
          (.unitE (.right (.left (.dead hΓ.split)))
            (.lolliE (.dead (.left (.dead hΓ.split))) (.var (.there (.here (.cons hΓ))))
              (ih₁ hwf.1 (.cons (.cons (.cons hΓ)))))
            (.lolliE (.left (.dead (.dead hΓ.split))) (.var (.here (.cons (.cons hΓ))))
              (ih₂ hwf.2 (.cons (.cons (.cons hΓ)))))))
  | sum _ _ ih₁ ih₂ =>
      intro Γ hΓ
      simp only [Ty.scopedB, Bool.and_eq_true] at hwf
      exact .lolliI (by simp [Ty.scopedB, hwf.1, hwf.2])
        (.sumE (.left hΓ.split) (by simp [Ty.scopedB, hwf.1, hwf.2]) (.var (.here hΓ))
          (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ))) (ih₁ hwf.1 (.cons (.cons hΓ))))
          (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ))) (ih₂ hwf.2 (.cons (.cons hΓ)))))
  | imm => intro Γ hΓ; exact .forgetImmAx hΓ
  | «mut» => intro Γ hΓ; exact .forgetMutAx hΓ
  | unk => intro Γ hΓ; exact .forgetUnkAx hΓ
  | bang => intro Γ hΓ; exact .forgetBangAx hΓ

/-- Every image of the reborrow metafunction is affine: `Imm̲ 'b` sends `Ref` and `Mut` to
`Imm`, functions to `Unk`, and strips `[@a]`. -/
theorem affine_immReborrow (b : Life) : ∀ T : Ty, Affine (T.immReborrow b) := by
  intro T
  induction T with
  | unit => exact .unit
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | lolli => exact .unk
  | ref => exact .imm
  | bang => exact .bang
  | imm => exact .imm
  | box _ _ ih => exact ih
  | all => exact .unk
  | «mut» => exact .imm
  | unk => exact .unk

theorem affine_recTy : ∀ fs : List Field, (∀ f ∈ fs, Affine f.2) → Affine (recTy fs)
  | [], _ => .unit
  | f :: fs, h => .tensor (h f (by simp)) (affine_recTy fs fun g hg => h g (by simp [hg]))

/-- `e.lᵢ`: the `i`-th field, every other field consumed. -/
def getAt : List Field → Nat → Expr → Expr
  | [], _, e => e
  | _ :: fs, 0, e => .letpair e (.seq (.app (dropT (recTy fs)) (.var 0)) (.var 1))
  | f :: fs, i + 1, e => .letpair e (.seq (.app (dropT f.2) (.var 1)) (getAt fs i (.var 0)))

/-- Projection, for a record whose fields are affine. -/
theorem getAt_wf {Δ : LifeCtx} :
    ∀ (fs : List Field) (i : Nat) {f : Field} {Γ : Ctx Ty} {e : Expr},
      fs[i]? = some f → (∀ g ∈ fs, Affine g.2) → (recTy fs).scopedB Δ = true →
      DerivesWf Δ Γ e (recTy fs) → DerivesWf Δ Γ (getAt fs i e) f.2
  | [], _, _, _, _, hi, _, _, _ => by simp at hi
  | g :: fs, 0, f, Γ, _, hi, haff, hwf, he => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have hwf' := hwf
      simp only [recTy, Ty.scopedB, Bool.and_eq_true] at hwf'
      exact .tensorE (split_kill' Γ) hwf he
        (.unitE (.left (.right (kill_dead Γ).split))
          (.lolliE (.left (.dead (kill_dead Γ).split)) (.var (.here (.cons (kill_dead Γ))))
            (dropT_wf (affine_recTy fs fun k hk => haff k (by simp [hk])) hwf'.2
              (.cons (.cons (kill_dead Γ)))))
          (.var (.there (.here (kill_dead Γ)))))
  | g :: fs, i + 1, f, Γ, _, hi, haff, hwf, he => by
      simp only [List.getElem?_cons_succ] at hi
      have hwf' := hwf
      simp only [recTy, Ty.scopedB, Bool.and_eq_true] at hwf'
      exact .tensorE (split_kill' Γ) hwf he
        (.unitE (.right (.left (kill_dead Γ).split))
          (.lolliE (.dead (.left (kill_dead Γ).split)) (.var (.there (.here (kill_dead Γ))))
            (dropT_wf (haff g (by simp)) hwf'.1 (.cons (.cons (kill_dead Γ)))))
          (getAt_wf fs i hi (fun k hk => haff k (by simp [hk])) hwf'.2
            (.var (.here (.cons (kill_dead Γ))))))

/-! ## Variants -/

/-- `lᵢ e`: the `i`-th injection. -/
def injAt : List Field → Nat → Expr → Expr
  | [], _, e => e
  | _ :: _, 0, e => .inj₁ e
  | _ :: gs, i + 1, e => .inj₂ (injAt gs i e)

theorem injAt_wf {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} :
    ∀ (f : Field) (gs : List Field) (i : Nat) {k : Field},
      (f :: gs)[i]? = some k → DerivesWf Δ Γ e k.2 → DerivesWf Δ Γ (injAt gs i e) (varTy f gs)
  | f, [], 0, _, hi, he => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact he
  | _, [], i + 1, _, hi, _ => by simp at hi
  | f, g :: gs, 0, _, hi, he => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi; exact .sumI₁ he
  | f, g :: gs, i + 1, _, hi, he => by
      simp only [List.getElem?_cons_succ] at hi
      exact .sumI₂ (injAt_wf g gs i hi he)

/-- `case e {l₁ x ⇒ b₁ ∣ … ∣ lₙ x ⇒ bₙ}`: nested `case`, the last case bound by `let`. -/
def vcase : Expr → List Expr → Expr
  | e, [] => e
  | e, [b] => elet e b
  | e, b :: bs => .case e b (vcase (.var 0) bs)

/-- The premises of `vcase_wf`.  Branch `k` (from 1) sees its payload at index 0, then the
`k − 1` consumed intermediate sums, then the context. -/
inductive Branches (Δ : LifeCtx) (T : Ty) : Ctx Ty → Field → List Field → List Expr → Prop where
  | one {Γ f b} : DerivesWf Δ (⟨f.2, true⟩ :: Γ) b T → Branches Δ T Γ f [] [b]
  | cons {Γ f g gs b bs} : DerivesWf Δ (⟨f.2, true⟩ :: Γ) b T →
      Branches Δ T (⟨varTy g gs, false⟩ :: Γ) g gs bs → Branches Δ T Γ f (g :: gs) (b :: bs)

/-- Variant elimination. -/
theorem vcase_wf {Δ : LifeCtx} {T : Ty} :
    ∀ {Γb : Ctx Ty} {f : Field} {gs : List Field} {bs : List Expr},
      Branches Δ T Γb f gs bs → ∀ {Γ Γs : Ctx Ty} {e : Expr}, Ctx.Split Γ Γs Γb →
      (varTy f gs).scopedB Δ = true → DerivesWf Δ Γs e (varTy f gs) →
      DerivesWf Δ Γ (vcase e bs) T := by
  intro Γb f gs bs hB
  induction hB with
  | one hb =>
      intro Γ Γs e hs hwf he
      exact .lolliE hs he (.lolliI hwf hb)
  | @cons Γb f g gs b bs hb _ ih =>
      intro Γ Γs e hs hwf he
      have hwf' := hwf
      simp only [varTy, Ty.scopedB, Bool.and_eq_true] at hwf'
      cases bs with
      | nil => cases ‹Branches _ _ _ _ _ []›
      | cons b' bs' =>
          exact .sumE hs hwf he hb
            (ih (.left (split_kill Γb)) hwf'.2 (.var (.here (kill_dead Γb))))

end BoCa.Records

end
