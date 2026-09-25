import Records.Encoding

/-!
# Borrowing records and variants

Field access through a borrow, as derived rules of `DerivesWf`, and the reborrowing facts at
record and variant types.

* `loadField` — read field `lᵢ` of an `Imm @a {…}`: `withload` at a fresh `'b ⊏ ⊓Δ`, then
  `getAt` on the loaded image.  The callback's body sees exactly `Imm̲ 'b Tᵢ`.
* `swapField` — run `g : Tᵢ ⊸ Tᵢ ⊗ T₂` on field `lᵢ` of a `Mut @a {…}`: `withswap` with
  `modAt`, which takes the record apart, applies `g` to one field and rebuilds it.

Both are compositions of the axioms `withload` / `withswap` (`[TR]` p. 3) with the record
forms, so the Fundamental Property covers them (`loadField_sem`, `swapField_sem`).

The reborrowing facts are `[TR]` 6.131 (`reborrow_vDen`) and its typed-world version
(`reborrow_vShape`) at `recTy` / `varTy`, through `immReborrow_recTy` / `immReborrow_varTy`.
-/

noncomputable section

namespace BoCa.Records
open BoCa BoCa.Lifetime BoCa.Programs

theorem getElem?_mapF (F : Ty → Ty) :
    ∀ (fs : List Field) (i : Nat) {f : Field}, fs[i]? = some f → (mapF F fs)[i]? = some (f.1, F f.2)
  | [], _, _, h => by simp at h
  | g :: fs, 0, _, h => by simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; rfl
  | _ :: fs, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h
      exact getElem?_mapF F fs i h

theorem mem_of_getElem? {fs : List Field} {i : Nat} {f : Field} (h : fs[i]? = some f) : f ∈ fs :=
  List.mem_of_getElem? h

theorem wf_var_extend (Δ : LifeCtx) (y : LifeVar) (u : Life) :
    (Life.var y).wf (Δ.extend y u) = true := by
  simp [Life.wf, LifeCtx.extend, LifeCtx.find?, assocFind]

/-! ## Reading a field through an immutable borrow -/

/-- `withload e (Λ. λr. let x = r.lᵢ in body)`, at the load lifetime `'y`. -/
def loadField (fs : List Field) (i : Nat) (y : LifeVar) (e body : Expr) : Expr :=
  app2 withload e (lam (lam (elet (getAt (mapF (Ty.immReborrow (.var y)) fs) i (.var 0)) body)))

/-- Reading field `lᵢ` of `e : Imm @a {…}`.  The body runs at `'y ⊏ ⊓Δ` with the field's
image `Imm̲ 'y Tᵢ` at index 0 and must return `['y] T₂`; the other fields' images are
consumed by `getAt`, which is possible because every `Imm̲` image is affine. -/
theorem loadField_wf {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {fs : List Field} {i : Nat}
    {f : Field} {y : LifeVar} {e body : Expr} {T₂ : Ty}
    (he : DerivesWf Δ Γ e (.imm a (recTy fs))) (hi : fs[i]? = some f)
    (hy : Δ.find? y = none)
    (hwfR : (recTy fs).scopedB (Δ.extend y Δ.meetOfDom) = true)
    (hwfT : (axWithloadTy a y Δ.meetOfDom (recTy fs) T₂).scopedB Δ = true)
    (hb : DerivesWf (Δ.extend y Δ.meetOfDom)
      (⟨f.2.immReborrow (.var y), true⟩ :: ⟨(recTy fs).immReborrow (.var y), false⟩ ::
        ⟨.unit, false⟩ :: kill Γ) body (.box (.var y) T₂)) :
    DerivesWf Δ Γ (loadField fs i y e body) T₂ := by
  have hyw := wf_var_extend Δ y Δ.meetOfDom
  have hR : (recTy fs).immReborrow (.var y) = recTy (mapF (Ty.immReborrow (.var y)) fs) :=
    immReborrow_recTy _ fs
  have hwfI : ((recTy fs).immReborrow (.var y)).scopedB (Δ.extend y Δ.meetOfDom) = true :=
    scopedB_immReborrow hyw _ hwfR
  have hwfF : (f.2.immReborrow (.var y)).scopedB (Δ.extend y Δ.meetOfDom) = true :=
    scopedB_immReborrow hyw _ ((scopedB_recTy fs).1 hwfR f (mem_of_getElem? hi))
  have hD := kill_dead Γ
  refine .lolliE (split_kill Γ) ?_ (.lolliE (split_kill' Γ) he (.withloadAx hD y hy hwfT))
  refine .allI (S := .unit) hy (meetOfDomL_wf Δ.entries) ?_ (.lolliI hwfI ?_)
  · intro s hs hl
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
    exact absurd hl (by simp)
  · refine .lolliE (.left (.dead hD.split)) ?_ (.lolliI hwfF hb)
    refine getAt_wf _ i (getElem?_mapF _ fs i hi)
      (fun g hg => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
        exact affine_immReborrow _ _) (hR ▸ hwfI) ?_
    exact hR ▸ .var (.here (.cons hD))

/-! ## Matching on a variant through an immutable borrow -/

/-- `withload e (Λ. λv. case v {l₁ x ⇒ b₁ ∣ …})`. -/
def loadCase (e : Expr) (bs : List Expr) : Expr :=
  app2 withload e (lam (lam (vcase (.var 0) bs)))

/-- Matching on `e : Imm @a ⟨…⟩`.  Branch `k` runs at `'y ⊏ ⊓Δ` with the case's image
`Imm̲ 'y Tₖ` and returns `['y] T₂`. -/
theorem loadCase_wf {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {f : Field} {gs : List Field}
    {y : LifeVar} {e : Expr} {bs : List Expr} {T₂ : Ty}
    (he : DerivesWf Δ Γ e (.imm a (varTy f gs))) (hy : Δ.find? y = none)
    (hwfV : (varTy f gs).scopedB (Δ.extend y Δ.meetOfDom) = true)
    (hwfT : (axWithloadTy a y Δ.meetOfDom (varTy f gs) T₂).scopedB Δ = true)
    (hB : Branches (Δ.extend y Δ.meetOfDom) (.box (.var y) T₂)
      (⟨(varTy f gs).immReborrow (.var y), false⟩ :: ⟨.unit, false⟩ :: kill Γ)
      (f.1, f.2.immReborrow (.var y)) (mapF (Ty.immReborrow (.var y)) gs) bs) :
    DerivesWf Δ Γ (loadCase e bs) T₂ := by
  have hyw := wf_var_extend Δ y Δ.meetOfDom
  have hV := immReborrow_varTy (.var y) f gs
  have hwfI : ((varTy f gs).immReborrow (.var y)).scopedB (Δ.extend y Δ.meetOfDom) = true :=
    scopedB_immReborrow hyw _ hwfV
  have hD := kill_dead Γ
  refine .lolliE (split_kill Γ) ?_ (.lolliE (split_kill' Γ) he (.withloadAx hD y hy hwfT))
  refine .allI (S := .unit) hy (meetOfDomL_wf Δ.entries) ?_ (.lolliI hwfI ?_)
  · intro s hs hl
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hs
    exact absurd hl (by simp)
  · exact vcase_wf hB (.left (.dead hD.split)) (hV ▸ hwfI) (hV ▸ .var (.here (.cons hD)))

/-! ## Updating a field through a mutable borrow -/

/-- `λr. let (x₁, …) = r; … let (xᵢ′, t) = g xᵢ; ((x₁, …, xᵢ′, …), t)`: `g` run on field `i`,
the record rebuilt around its result. -/
def modAt : List Field → Nat → Expr → Expr
  | [], _, _ => lam (.var 0)
  | _ :: _, 0, g =>
      lam (.letpair (.var 0) (.letpair (.app g (.var 1)) (.pair (.pair (.var 1) (.var 2)) (.var 0))))
  | _ :: fs, i + 1, g =>
      lam (.letpair (.var 0)
        (.letpair (.app (modAt fs i g) (.var 0)) (.pair (.pair (.var 3) (.var 1)) (.var 0))))

theorem modAt_wf {Δ : LifeCtx} {T₂ : Ty} {g : Expr} (hT₂ : T₂.scopedB Δ = true) :
    ∀ (fs : List Field) (i : Nat) {f : Field}, fs[i]? = some f →
      (∀ {Γ : Ctx Ty}, Ctx.Dead Γ → DerivesWf Δ Γ g (.lolli f.2 (.tensor f.2 T₂))) →
      (recTy fs).scopedB Δ = true →
      ∀ {Γ : Ctx Ty}, Ctx.Dead Γ →
        DerivesWf Δ Γ (modAt fs i g) (.lolli (recTy fs) (.tensor (recTy fs) T₂))
  | [], _, _, hi, _, _, _, _ => by simp at hi
  | k :: fs, 0, f, hi, hg, hwf, Γ, D => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have hwf' := hwf
      simp only [recTy, Ty.scopedB, Bool.and_eq_true] at hwf'
      exact .lolliI hwf
        (.tensorE (.left D.split) hwf (.var (.here D))
          (.tensorE (.right (.left (.dead D.split))) (by simp [Ty.scopedB, hwf'.1, hT₂])
            (.lolliE (.dead (.left (.dead D.split))) (.var (.there (.here (.cons D))))
              (hg (.cons (.cons (.cons D)))))
            (.tensorI (.right (.left (.left (.dead (.dead D.split)))))
              (.tensorI (.dead (.left (.right (.dead (.dead D.split)))))
                (.var (.there (.here (.cons (.cons (.cons D))))))
                (.var (.there (.there (.here (.cons (.cons D)))))))
              (.var (.here (.cons (.cons (.cons (.cons D)))))))))
  | k :: fs, i + 1, f, hi, hg, hwf, Γ, D => by
      simp only [List.getElem?_cons_succ] at hi
      have hwf' := hwf
      simp only [recTy, Ty.scopedB, Bool.and_eq_true] at hwf'
      exact .lolliI hwf
        (.tensorE (.left D.split) hwf (.var (.here D))
          (.tensorE (.left (.right (.dead D.split))) (by simp [Ty.scopedB, hwf'.2, hT₂])
            (.lolliE (.left (.dead (.dead D.split))) (.var (.here (.cons (.cons D))))
              (modAt_wf hT₂ fs i hi hg hwf'.2 (.cons (.cons (.cons D)))))
            (.tensorI (.right (.left (.dead (.left (.dead D.split)))))
              (.tensorI (.dead (.right (.dead (.left (.dead D.split)))))
                (.var (.there (.there (.there (.here (.cons D))))))
                (.var (.there (.here (.cons (.cons (.cons D)))))))
              (.var (.here (.cons (.cons (.cons (.cons D)))))))))

/-- `withswap m (modAt fs i g)`. -/
def swapField (fs : List Field) (i : Nat) (m g : Expr) : Expr := app2 withswap m (modAt fs i g)

/-- Field-level `withswap`: `Mut @a {…} ⊸ (Tᵢ ⊸ Tᵢ ⊗ T₂) ⊸ Mut @a {…} ⊗ T₂`, derived. -/
theorem swapField_wf {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {fs : List Field} {i : Nat}
    {f : Field} {m g : Expr} {T₂ : Ty}
    (hm : DerivesWf Δ Γ m (.mut a (recTy fs))) (hi : fs[i]? = some f)
    (hg : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → DerivesWf Δ Γ g (.lolli f.2 (.tensor f.2 T₂)))
    (hwf : (recTy fs).scopedB Δ = true) (hT₂ : T₂.scopedB Δ = true) :
    DerivesWf Δ Γ (swapField fs i m g) (.tensor (.mut a (recTy fs)) T₂) :=
  .lolliE (split_kill Γ) (modAt_wf hT₂ fs i hi hg hwf (kill_dead Γ))
    (.lolliE (split_kill' Γ) hm (.withswapAx (kill_dead Γ)))

/-! ## Soundness of the derived rules: the Fundamental Property, unchanged -/

open BoCa.Fig16.LogRel.Typed in
/-- `loadField` is semantically sound: 6.151 at `SemX` applied to its derivation. -/
theorem loadField_sem {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {fs : List Field} {i : Nat}
    {f : Field} {y : LifeVar} {e body : Expr} {T₂ : Ty}
    (he : DerivesWf Δ Γ e (.imm a (recTy fs))) (hi : fs[i]? = some f)
    (hy : Δ.find? y = none)
    (hwfR : (recTy fs).scopedB (Δ.extend y Δ.meetOfDom) = true)
    (hwfT : (axWithloadTy a y Δ.meetOfDom (recTy fs) T₂).scopedB Δ = true)
    (hb : DerivesWf (Δ.extend y Δ.meetOfDom)
      (⟨f.2.immReborrow (.var y), true⟩ :: ⟨(recTy fs).immReborrow (.var y), false⟩ ::
        ⟨.unit, false⟩ :: kill Γ) body (.box (.var y) T₂))
    (hΔ : Δ.Ok) (hΓ : Ctx.ScopedB Δ Γ) :
    SemX Δ Γ (loadField fs i y e body) T₂ :=
  fundamental _ _ _ _ (loadField_wf he hi hy hwfR hwfT hb) hΔ hΓ

open BoCa.Fig16.LogRel.Typed in
/-- `swapField` is semantically sound: 6.151 at `SemX` applied to its derivation. -/
theorem swapField_sem {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {fs : List Field} {i : Nat}
    {f : Field} {m g : Expr} {T₂ : Ty}
    (hm : DerivesWf Δ Γ m (.mut a (recTy fs))) (hi : fs[i]? = some f)
    (hg : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → DerivesWf Δ Γ g (.lolli f.2 (.tensor f.2 T₂)))
    (hwf : (recTy fs).scopedB Δ = true) (hT₂ : T₂.scopedB Δ = true)
    (hΔ : Δ.Ok) (hΓ : Ctx.ScopedB Δ Γ) :
    SemX Δ Γ (swapField fs i m g) (.tensor (.mut a (recTy fs)) T₂) :=
  fundamental _ _ _ _ (swapField_wf hm hi hg hwf hT₂) hΔ hΓ

/-! ## The reborrowing facts at records and variants

`[TR]` 6.131 (`↺V₁`) at `{lᵢ : Tᵢ}` and `⟨lᵢ : Tᵢ⟩`, over the literal relation and over
the typed world's shapes.  Each is the library's lemma at the encoded type, rewritten by the
fieldwise clause: the binary `⊗` / `⊕` / `1` cases of its induction are all it uses. -/

section Reborrow
open BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel

/-- `[α] 𝒱⟦{lᵢ : Tᵢ}⟧δ(v) ⊨ ↺_α 𝒱⟦{lᵢ : Imm̲ 'x Tᵢ}⟧δ(v)`. -/
theorem reborrow_vDen_recTy {α : Fig16.Life} {x : LifeVar} {δ : Lifetime.LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) (fs : List Field) (v : Val) :
    box α (vDen (recTy fs) δ v) ⊨
      reborrow α (vDen (recTy (mapF (Ty.immReborrow (.var x)) fs)) δ v) := by
  rw [← immReborrow_recTy]; exact reborrow_vDen hδ _ v

/-- `[α] 𝒱⟦⟨lᵢ : Tᵢ⟩⟧δ(v) ⊨ ↺_α 𝒱⟦⟨lᵢ : Imm̲ 'x Tᵢ⟩⟧δ(v)`. -/
theorem reborrow_vDen_varTy {α : Fig16.Life} {x : LifeVar} {δ : Lifetime.LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) (f : Field) (gs : List Field) (v : Val) :
    box α (vDen (varTy f gs) δ v) ⊨
      reborrow α (vDen (varTy (f.1, f.2.immReborrow (.var x))
        (mapF (Ty.immReborrow (.var x)) gs)) δ v) := by
  rw [← immReborrow_varTy]; exact reborrow_vDen hδ _ v

/-- The typed world's version at records. -/
theorem reborrow_vShape_recTy {α : Fig16.Life} {x : LifeVar} {δ : Lifetime.LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) (fs : List Field) (v : Val) :
    box α (Typed.vShape (recTy fs) δ v) ⊨
      reborrow α (Typed.vShape (recTy (mapF (Ty.immReborrow (.var x)) fs)) δ v) := by
  rw [← immReborrow_recTy]; exact Typed.reborrow_vShape hδ _ v

/-- The typed world's version at variants. -/
theorem reborrow_vShape_varTy {α : Fig16.Life} {x : LifeVar} {δ : Lifetime.LSub}
    (hδ : (Lifetime.Life.var x).interp δ = some α) (f : Field) (gs : List Field) (v : Val) :
    box α (Typed.vShape (varTy f gs) δ v) ⊨
      reborrow α (Typed.vShape (varTy (f.1, f.2.immReborrow (.var x))
        (mapF (Ty.immReborrow (.var x)) gs)) δ v) := by
  rw [← immReborrow_varTy]; exact Typed.reborrow_vShape hδ _ v

/-- `[TR]` 6.60 at records, in the typed world: a record whose fields all outlive `@a` holds
a resource in `@a`'s stratum. -/
theorem vX_outlives_recTy {wpX : Typed.WpOp} {Δ : LifeCtx} {δ : Lifetime.LSub} {a : Lifetime.Life} {α : Fig16.Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {fs : List Field}
    (hfs : ∀ f ∈ fs, OutlivesRules Δ a f.2) (b : Bool) :
    ∀ ls v ρ, Typed.vX wpX b (recTy fs) ls δ v ρ → BoLo.Outlives ρ α :=
  Typed.vX_outlives hδ ha ((outlives_recTy fs).2 hfs) b

end Reborrow

end BoCa.Records

end
