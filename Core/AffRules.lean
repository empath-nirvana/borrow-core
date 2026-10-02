import Core.Aff
import Core.IntPrograms

/-!
# The affine closure — the rules, derived  `[spec §22]`

Every rule here is a derivation in `CDerives`, from `nuIn`/`nuOut`, coiteration
(`unfoldN`), `withswap`, `[]I`/`[]E` and the CBPV formers.  None is a new constructor, so
`fundamentalC` and `adequacyC` cover them with no new compatibility lemma.

| rule | term | from |
|---|---|---|
| introduction | `mkE`: a state `s₀ : S`, `!` code `step : S ⊸ (A ⊸ F(B ⊗ [@c] S)) & F 1` (`d_mk`) | `unfoldN` |
| introduction outliving `@c` | `mkE` when `S` outlives `@c` (`d_mkBox`) | `unfoldN`, `[]I` |
| call | `callE f a : F(B ⊗ [@c] U(Aff^c A B))` | `nuOut`, `π₁`, application |
| close | `closeE f : F 1` | `nuOut`, `π₂` |
| call through `Mut` | `callMutE m a : Mut @a ([@c] U(Aff^c A B)) ⊗ B` | `withswap` with the call as callback |
| persistent ≤ affine | `mkE` at the state `!U(A ⊸ F B)` (`d_ofFn`) | `unfoldN`, persistence |
| affine ≤ linear | `onceE f : U(A ⊸ F B)`: call once, close the rest (`d_once`) | the above |
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable {Δ : LifeCtx}

/-! ### In, out, coiteration -/

theorem CDerives.affIn {Γ : Ctx VTy} {e : Expr} {c : Lifetime.Life} {A B : VTy} (hA : A.Cl 0)
    (h : CDerives Δ Γ e (.comp (affUnroll c A B))) : CDerives Δ Γ e (.comp (affC c A B)) :=
  .nuIn (affBody_nuOk hA c B) (by rw [affBody_unroll]; exact h)

theorem CDerives.affOut {Γ : Ctx VTy} {e : Expr} {c : Lifetime.Life} {A B : VTy} (hA : A.Cl 0)
    (h : CDerives Δ Γ e (.comp (affC c A B))) : CDerives Δ Γ e (.comp (affUnroll c A B)) := by
  rw [← affBody_unroll]; exact .nuOut (affBody_nuOk hA c B) h

/-- `unfold` at `Aff^c A B`: `!U(S ⊸ (A ⊸ F(B ⊗ [@c] S)) & F 1) ⊸ !U(S ⊸ Aff^c A B)`. -/
abbrev affUnfoldTy (c : Lifetime.Life) (A B S : VTy) : VTy :=
  .lolli (.bang (.thunk (.arr S (affStepC c A B S)))) (.bang (.thunk (.arr S (affC c A B))))

theorem CDerives.affUnfold {Γ : Ctx VTy} {c : Lifetime.Life} {A : VTy} (hA : A.Cl 0) (B S : VTy)
    (hΓ : Ctx.DeadP Γ) : CDerives Δ Γ (.val (affUnfoldV c A B)) (.val (affUnfoldTy c A B S)) := by
  have h := CDerives.unfoldN (Δ := Δ) (affBody c A B) S (affBody_nuOk hA c B) hΓ
  rwa [unfoldTy, affBody_instT] at h

/-! ### Outlives of contexts -/

theorem ctxOutlives_dead {Γ : Ctx VTy} {a : Lifetime.Life} (ha : Δ.Defines a) (hΓ : Ctx.Dead Γ) :
    CtxOutlives Δ Γ a :=
  ⟨ha, dead_noLive (P := fun s => VOutlives Δ a s.ty) hΓ⟩

theorem CtxOutlives.consDead {Γ : Ctx VTy} {a : Lifetime.Life} {T : VTy}
    (h : CtxOutlives Δ Γ a) : CtxOutlives Δ (⟨T, false⟩ :: Γ) a := by
  refine ⟨h.1, fun s hs hl => ?_⟩
  cases hs with
  | head => exact absurd hl (by simp)
  | tail _ hs' => exact h.2 s hs' hl

theorem CtxOutlives.consLive {Γ : Ctx VTy} {a : Lifetime.Life} {T : VTy} (hT : VOutlives Δ a T)
    (h : CtxOutlives Δ Γ a) : CtxOutlives Δ (⟨T, true⟩ :: Γ) a := by
  refine ⟨h.1, fun s hs hl => ?_⟩
  cases hs with
  | head => exact hT
  | tail _ hs' => exact h.2 s hs' hl

/-! ### Introduction: a closure from a state and `!` code -/

/-- The unfolded code's type, `!U(S ⊸ Aff^c A B)`. -/
abbrev affCodeT (c : Lifetime.Life) (A B S : VTy) : VTy := .bang (.thunk (.arr S (affC c A B)))

theorem d_pack {Γ : Ctx VTy} {c : Lifetime.Life} {A B S : VTy} (hA : A.Cl 0) (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨affCodeT c A B S, true⟩ :: ⟨S, true⟩ :: Γ) packE (.val (affT c A B)) := by
  have hfs : CDerives Δ (⟨.thunk (.arr S (affC c A B)), true⟩ ::
      withCtx (⟨affCodeT c A B S, false⟩ :: ⟨S, true⟩ :: Γ))
      (.app (.var 0) (.var 4)) (.comp (affC c A B)) :=
    .app (.left (.dead (.dead (.dead (.right (deadSplit hΓ))))))
      (.force (.here (.cons (.cons (.cons (.cons hΓ.toP))))))
      (.there (.there (.there (.there (.here hΓ.toP)))))
  have hf : CDerives Δ (withCtx (⟨affCodeT c A B S, true⟩ :: ⟨S, false⟩ :: Γ)) (.var 2)
      (.comp (.ret (.thunk (.arr S (affC c A B))))) :=
    .ret (.bangE (.var (.there (.there (.here (.cons hΓ.toP))))))
  have hs : Ctx.SplitP (withCtx (⟨affCodeT c A B S, true⟩ :: ⟨S, true⟩ :: Γ))
      (withCtx (⟨affCodeT c A B S, true⟩ :: ⟨S, false⟩ :: Γ))
      (withCtx (⟨affCodeT c A B S, false⟩ :: ⟨S, true⟩ :: Γ)) :=
    .dead (.dead (.left (.right (deadSplit hΓ))))
  exact .thunkV rfl (.affIn hA (.withI (.bind hs hf (.proj₁ (.affOut hA hfs)))
    (.bind hs hf (.proj₂ (.affOut hA hfs)))))

/-- The packed closure outlives `@c` when its state does: `[]I` over `f : !…` and `s : S`. -/
theorem d_packBox {Γ : Ctx VTy} {c : Lifetime.Life} {A B S : VTy} (hA : A.Cl 0) (hΓ : Ctx.Dead Γ)
    (hc : Δ.Defines c) (hS : VOutlives Δ c S) :
    CDerives Δ (⟨affCodeT c A B S, true⟩ :: ⟨S, true⟩ :: Γ) packE (.val (affBox c A B)) :=
  .boxI (d_pack hA hΓ) (.consLive .bang (.consLive hS (ctxOutlives_dead hc hΓ)))

/-- The two bindings in front of `pack`. -/
theorem d_mkPrefix {Γ Γ₁ Γ₂ : Ctx VTy} {c : Lifetime.Life} {A B S : VTy} {C : CTy} {s₀ K : Expr}
    {step : Val} (hA : A.Cl 0) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₀ : CDerives Δ Γ₁ s₀ (.val S))
    (hstep : CDerives Δ (kill (⟨S, true⟩ :: Γ₂)) (.val step)
      (.val (.bang (.thunk (.arr S (affStepC c A B S))))))
    (hK : CDerives Δ (⟨affCodeT c A B S, true⟩ :: ⟨S, true⟩ :: Γ₂) (bindE packE K) (.comp C)) :
    CDerives Δ Γ (mkE c A B s₀ step K) (.comp C) :=
  .bind hs (.ret hs₀)
    (.bind (split_kill _).toP
      (.ret (.lolliE (deadSplit (kill_dead _)) hstep (.affUnfold hA B S (kill_dead _).toP))) hK)

/-- **Introduction.**  A closure over the state `s₀ : S`, with `!` code `step`.  The state
holds whatever the closure captures, linear and borrowed parts included; the type hides `S`. -/
theorem d_mk {Γ Γ₁ Γ₂ : Ctx VTy} {c : Lifetime.Life} {A B S : VTy} {C : CTy} {s₀ K : Expr}
    {step : Val} (hA : A.Cl 0) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₀ : CDerives Δ Γ₁ s₀ (.val S))
    (hstep : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val step) (.val (.bang (.thunk (.arr S (affStepC c A B S))))))
    (hK : CDerives Δ (⟨affT c A B, true⟩ :: ⟨affCodeT c A B S, false⟩ :: ⟨S, false⟩ :: Γ₂) K
      (.comp C)) :
    CDerives Δ Γ (mkE c A B s₀ step K) (.comp C) :=
  d_mkPrefix hA hs hs₀ (hstep (kill_dead _))
    (.bind (.left (.left (split_kill Γ₂).toP)) (.ret (d_pack hA (kill_dead Γ₂))) hK)

/-- **Introduction, outliving `@c`.**  When the state outlives `@c`, so does the closure. -/
theorem d_mkBox {Γ Γ₁ Γ₂ : Ctx VTy} {c : Lifetime.Life} {A B S : VTy} {C : CTy} {s₀ K : Expr}
    {step : Val} (hA : A.Cl 0) (hc : Δ.Defines c) (hS : VOutlives Δ c S)
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₀ : CDerives Δ Γ₁ s₀ (.val S))
    (hstep : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val step) (.val (.bang (.thunk (.arr S (affStepC c A B S))))))
    (hK : CDerives Δ (⟨affBox c A B, true⟩ :: ⟨affCodeT c A B S, false⟩ :: ⟨S, false⟩ :: Γ₂) K
      (.comp C)) :
    CDerives Δ Γ (mkE c A B s₀ step K) (.comp C) :=
  d_mkPrefix hA hs hs₀ (hstep (kill_dead _))
    (.bind (.left (.left (split_kill Γ₂).toP)) (.ret (d_packBox hA (kill_dead Γ₂) hc hS)) hK)

/-- `d_mkBox` with the step typed at the one context it is used in. -/
theorem d_mkBox' {Γ Γ₁ Γ₂ : Ctx VTy} {c : Lifetime.Life} {A B S : VTy} {C : CTy} {s₀ K : Expr}
    {step : Val} (hA : A.Cl 0) (hc : Δ.Defines c) (hS : VOutlives Δ c S)
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₀ : CDerives Δ Γ₁ s₀ (.val S))
    (hstep : CDerives Δ (kill (⟨S, true⟩ :: Γ₂)) (.val step)
      (.val (.bang (.thunk (.arr S (affStepC c A B S))))))
    (hK : CDerives Δ (⟨affBox c A B, true⟩ :: ⟨affCodeT c A B S, false⟩ :: ⟨S, false⟩ :: Γ₂) K
      (.comp C)) :
    CDerives Δ Γ (mkE c A B s₀ step K) (.comp C) :=
  d_mkPrefix hA hs hs₀ hstep
    (.bind (.left (.left (split_kill Γ₂).toP)) (.ret (d_packBox hA (kill_dead Γ₂) hc hS)) hK)

/-! ### Elimination: call and close -/

/-- `f π₁ a`: call. -/
def callE (i j : Nat) : Expr := .app (.app (.var i) (.val (.inj₁ .unit))) (.var j)

/-- `f π₂`: close. -/
def closeE (i : Nat) : Expr := .app (.var i) (.val (.inj₂ .unit))

/-- **Call.**  `f : U(Aff^c A B)`, `a : A ⊢ f π₁ a : F(B ⊗ [@c] U(Aff^c A B))`. -/
theorem d_callAff {Γ Γ₁ Γ₂ : Ctx VTy} {c : Lifetime.Life} {A B : VTy} {i j : Nat} (hA : A.Cl 0)
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hf : Ctx.SoloP Γ₁ i (affT c A B)) (ha : Ctx.SoloP Γ₂ j A) :
    CDerives Δ Γ (callE i j) (.comp (.ret (.tensor B (affBox c A B)))) :=
  .app hs (.proj₁ (.affOut hA (.force hf))) ha

/-- **Close.**  `f : U(Aff^c A B) ⊢ f π₂ : F 1`. -/
theorem d_close {Γ : Ctx VTy} {c : Lifetime.Life} {A B : VTy} {i : Nat} (hA : A.Cl 0)
    (hf : Ctx.SoloP Γ i (affT c A B)) : CDerives Δ Γ (closeE i) (.comp (.ret .unit)) :=
  .proj₂ (.affOut hA (.force hf))

/-- `x to y. N` at `x : [@c] T`: `N` with the unboxed `y : T` at `0` (`[]E`). -/
theorem d_unbox {Γ Γ₁ Γ₂ : Ctx VTy} {c : Lifetime.Life} {T : VTy} {C : CTy} {i : Nat} {N : Expr}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i (.box c T))
    (hN : CDerives Δ (⟨T, true⟩ :: Γ₂) N (.comp C)) : CDerives Δ Γ (bindE (.var i) N) (.comp C) :=
  .bind hs (.ret (.boxE (.var hx))) hN

/-- Close a boxed closure: `x to y. y π₂`. -/
theorem d_closeBox {Γ : Ctx VTy} {c : Lifetime.Life} {A B : VTy} (hA : A.Cl 0) (hΓ : Ctx.Dead Γ) :
    CDerives Δ (⟨affBox c A B, true⟩ :: Γ) (bindE (.var 0) (closeE 0)) (.comp (.ret .unit)) :=
  d_unbox (.left (deadSplit hΓ)) (.here hΓ.toP) (d_close hA (.here (.cons hΓ.toP)))

/-! ### Call through a `Mut` borrow -/

/-- The callback `λbf. (bf to f. f π₁ a) to p. let (b, r) = p in (r, b)`, `a` at `j` outside. -/
def kMutE (j : Nat) : Expr :=
  bindE (bindE (.var 0) (callE 0 (j + 2))) (.letpair (.var 0) (.pair (.var 0) (.var 1)))

/-- `withswap m (λbf. …)`: call the closure behind `m : Mut @a ([@c] U Aff^c A B)`. -/
def callMutE (i j : Nat) : Expr := .app (.app withswap (.var i)) (.val (.lam (kMutE j)))

/-- **Call through `Mut`.**  `m : Mut @a ([@c] U(Aff^c A B))`, `a : A ⊢
withswap m (λbf. …) : Mut @a ([@c] U(Aff^c A B)) ⊗ B`: the closure is swapped out, called,
and its rest swapped back in, so the state persists between calls. -/
theorem d_callMut {Γ Γa Γm : Ctx VTy} {a c : Lifetime.Life} {A B : VTy} {i j : Nat} (hA : A.Cl 0)
    (hs : Ctx.SplitP Γ Γa Γm) (hm : Ctx.SoloP Γm i (.mut a (affBox c A B)))
    (ha : Ctx.Solo Γa j A) :
    CDerives Δ Γ (callMutE i j) (.val (.tensor (.mut a (affBox c A B)) B)) := by
  have hbody : CDerives Δ (⟨affBox c A B, true⟩ :: Γa) (kMutE j)
      (.comp (.ret (.tensor (affBox c A B) B))) :=
    .bind (split_kill' _).toP
      (d_unbox (.left (split_kill Γa).toP) (.here (kill_dead Γa).toP)
        (d_callAff hA (.left (.dead (split_kill Γa).toP)) (.here (.cons (kill_dead Γa).toP))
          (.there (.there ha.toP))))
      (.tensorE (.left (deadSplit (kill_dead _))) (.var (.here (kill_dead _).toP))
        (.ret (.tensorI (.left (.right (.dead (deadSplit (kill_dead _)))))
          (.var (.here (.cons (.cons (kill_dead _).toP))))
          (.var (.there (.here (.cons (kill_dead _).toP)))))))
  exact .lolliE hs (.thunkV rfl (.lam hbody))
    (.lolliE (split_kill' Γm).toP (.var hm) (.withswap (kill_dead Γm).toP))

/-! ### Persistent ≤ affine -/

/-- The step over a persistent function: `λs. ⟨λa. s a to b. (b, s), ()⟩`.  The state `s : !U(A ⊸ F B)` is
persistent: the call uses it and hands it back, `close` drops it. -/
def ofFnStep : Val :=
  .lam (withPair (.val (.lam (bindE (.app (.var 3) (.var 0)) (.pair (.var 0) (.var 4)))))
    (.val .unit))

theorem d_ofFnStep {Γ : Ctx VTy} {c : Lifetime.Life} {A B : VTy} (hc : Δ.Defines c)
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val ofFnStep)
      (.val (.bang (.thunk (.arr (.bang (.lolli A B)) (affStepC c A B (.bang (.lolli A B))))))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI (.lam ?_) (.ret ?_)))
  · refine .bind (.left (.dead (.dead (.dup rfl (deadSplit hΓ)))))
      (.ret (.lolliE (.left (.dead (.dead (.right (deadSplit hΓ)))))
        (.var (.here (.cons (.cons (.cons hΓ.toP)))))
        (.bangE (.var (.there (.there (.there (.here hΓ.toP))))))))
      (.ret (.tensorI (.left (.dead (.dead (.dead (.right (deadSplit hΓ))))))
        (.var (.here (.cons (.cons (.cons (.cons hΓ.toP))))))
        (.boxI (.var (.there (.there (.there (.there (.here hΓ.toP))))))
          (.consDead (.consDead (.consDead (.consDead (.consLive .bang
            (ctxOutlives_dead hc hΓ)))))))))
  · exact .unitI (.cons (.cons (.drop rfl hΓ.toP)))

/-- **Persistent ≤ affine** (cf. Rust's `Fn ≤ FnMut`).  A `!U(A ⊸ F B)` is an affine closure
outliving any defined `@c`: the state is persistent, so the closure is boxed at `@c`
(`d_mkBox`). -/
theorem d_ofFn {Γ Γ₁ Γ₂ : Ctx VTy} {c : Lifetime.Life} {A B : VTy} {C : CTy} {g K : Expr}
    (hA : A.Cl 0) (hc : Δ.Defines c) (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hg : CDerives Δ Γ₁ g (.val (.bang (.lolli A B))))
    (hK : CDerives Δ (⟨affBox c A B, true⟩ :: ⟨affCodeT c A B (.bang (.lolli A B)), false⟩ ::
      ⟨.bang (.lolli A B), false⟩ :: Γ₂) K (.comp C)) :
    CDerives Δ Γ (mkE c A B g ofFnStep K) (.comp C) :=
  d_mkBox hA hc .bang hs hg (fun hΓ' => d_ofFnStep hc hΓ') hK

/-! ### Affine ≤ linear -/

/-- `λa. f π₁ a to p. let (b, r) = p in r to r'. r' π₂ to u. u; b`: call once, close the rest. -/
def onceE (i : Nat) : Expr :=
  .val (.lam (bindE (callE (i + 1) 0) (.letpair (.var 0)
    (bindE (.var 0) (bindE (closeE 0) (.seq (.var 0) (.var 3)))))))

/-- **Affine ≤ linear** (cf. Rust's `FnMut ≤ FnOnce`).
`f : U(Aff^c A B) ⊢ λa. … : U(A ⊸ F B)`. -/
theorem d_once {Γ : Ctx VTy} {c : Lifetime.Life} {A B : VTy} {i : Nat} (hA : A.Cl 0)
    (hf : Ctx.Solo Γ i (affT c A B)) : CDerives Δ Γ (onceE i) (.val (.lolli A B)) := by
  refine .thunkV rfl (.lam ?_)
  refine .bind (split_kill' _).toP
    (d_callAff hA (.right (split_kill' Γ).toP) (.there hf.toP) (.here (kill_dead Γ).toP)) ?_
  refine .tensorE (.left (deadSplit (kill_dead _))) (.var (.here (kill_dead _).toP)) ?_
  refine d_unbox (.left (.right (.dead (deadSplit (kill_dead _))))) (.here (.cons (.cons
    (kill_dead _).toP))) ?_
  refine .bind (.left (.dead (.right (.dead (deadSplit (kill_dead _))))))
    (d_close hA (.here (.cons (.cons (.cons (kill_dead _).toP))))) ?_
  exact .unitE (.left (.dead (.dead (.right (.dead (deadSplit (kill_dead _)))))))
    (.var (.here (.cons (.cons (.cons (.cons (kill_dead _).toP))))))
    (.ret (.var (.there (.there (.there (.here (.cons (kill_dead _).toP)))))))

end BoCa.Fig16.LogRel.Core

end
