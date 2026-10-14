import Law2.Remake

/-!
# Law2 — closures Core's typing derives re-lend, hereditarily

Re-lending fails at `U` pointwise (`DenseCarrier/RelendRoom.lean`, `core_not_relend_kU`): a
closure related only because its argument type is empty at the reading stops being related when a
re-making opens room. A closure a typed program builds is not such a closure: it is a term Core's
typing derives, closed by values the program computed, and the fundamental property relates it at
every reading in `⟦Δ⟧`.

`HTV A δ v ρ` (hereditarily typed values) is an inductive predicate on a value and its resource:
a first-order value in the relation, a pair of such, or a thunk whose body Core's typing derives
(`[thunkF]`, `[thunkV]`) closed by a context of hereditarily typed values (`HTG`). The closure case
carries a derivation and a hereditarily typed context, never a relation at `U`. Nothing here shows
that a run produces only `HTV` values or splits its share as an `HTG` context: where a context is
`HTV`, that is a hypothesis of the theorem using it (`runsAt_of_typed`'s `hctx`). The reading (S1)
is proved at is `RSlot` (`Law2/Piece.lean`), which a borrower's own derivation establishes rule by
rule (`pj_fundamental`).

* `htv_sound`, `htg_sound`: a hereditarily typed value is in Core's relation, at every record
  list; a hereditarily typed context is in `𝒢⟦Γ⟧`.
* `htv_relend`, `htg_relend`: **at every re-making, a hereditarily typed value has a re-make that is
  hereditarily typed at the moved reading** — one induction, the closure case by the derivation's
  own `⟦Δ⟧` at the moved reading (`models_mapN_iff`), the first-order case by `relend_fov`. So
  closures re-lend at every computation type their body has, `∀` and `F` included, at any depth of
  closures inside closures.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head)
open BoCa.Lifetime (LifeVar LifeCtx LSub)

mutual
/-- **Hereditarily typed values** at the reading `δ` and resource `ρ`. -/
inductive HTV : VTy → LSub → Val → WRes → Prop
  /-- A first-order value in the relation. -/
  | fo {A : VTy} {δ : LSub} {v : Val} {ρ : WRes} :
      FOV A → vCE (ℍ := ℍ) none true A [] δ v ρ → HTV A δ v ρ
  /-- A pair of hereditarily typed values. -/
  | tensor {A B : VTy} {δ : LSub} {v₁ v₂ : Val} {ρ₁ ρ₂ ρ : WRes} :
      HTV A δ v₁ ρ₁ → HTV B δ v₂ ρ₂ → ResU.CompS ρ₁ ρ₂ ρ → HTV (.tensor A B) δ (Val.pair v₁ v₂) ρ
  /-- `thunk M : U (F A)` (`[thunkF]`), closed by a hereditarily typed context. -/
  | thunkF {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {A : VTy} {δ : LSub} {γ : List Val}
      {ρ : WRes} :
      CDerives Δ (⟨.unit, false⟩ :: Γ) M (.comp (.ret A)) → Δ.Models δ →
      Ctx.LiveWithin Γ γ → HTG Γ δ γ ρ →
      HTV (.thunk (.ret A)) δ ⟨.lam (Expr.psub 1 γ M), .lam⟩ ρ
  /-- `thunk V : U C` for a λ-value `V : C`, `C` not an `F` (`[thunkV]`), closed by a hereditarily
  typed context. -/
  | thunkV {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {C : CTy} {δ : LSub} {γ : List Val}
      {ρ : WRes} :
      C.isRet = false → CDerives Δ Γ (.val (.lam N)) (.comp C) → Δ.Models δ →
      Ctx.LiveWithin Γ γ → HTG Γ δ γ ρ →
      HTV (.thunk C) δ ⟨.lam (Expr.psub 1 γ N), .lam⟩ ρ

/-- **A hereditarily typed context**: every live slot's value hereditarily typed, the resources
composed. -/
inductive HTG : Ctx VTy → LSub → List Val → WRes → Prop
  | nil {δ : LSub} {γ : List Val} : HTG [] δ γ PMap.empty
  | noVal {s : Slot VTy} {Γ : Ctx VTy} {δ : LSub} : HTG (s :: Γ) δ [] PMap.empty
  | live {s : Slot VTy} {Γ : Ctx VTy} {δ : LSub} {v : Val} {γ : List Val} {ρ₁ ρ₂ ρ : WRes} :
      s.live = true → HTV s.ty δ v ρ₁ → HTG Γ δ γ ρ₂ → ResU.CompS ρ₁ ρ₂ ρ →
      HTG (s :: Γ) δ (v :: γ) ρ
  | dead {s : Slot VTy} {Γ : Ctx VTy} {δ : LSub} {v : Val} {γ : List Val} {ρ : WRes} :
      s.live = false → HTG Γ δ γ ρ → HTG (s :: Γ) δ (v :: γ) ρ
end

/-! ### Soundness -/

theorem substAll_cons_psub' (v : Val) (γ : List Val) (e : Expr) :
    substAll (v :: γ) e = Expr.subst 0 v (Expr.psub 1 γ e) := by
  show Expr.psub 0 (v :: γ) e = _
  rw [Expr.psub_cons 0 v γ e, Val.shift_zero]

mutual
/-- **A hereditarily typed value is in Core's relation**, at every record list. -/
theorem htv_sound : ∀ {A : VTy} {δ : LSub} {v : Val} {ρ : WRes}, HTV (ℍ := ℍ) A δ v ρ →
    ∀ ls : List SRec, vCE (ℍ := ℍ) none true A ls δ v ρ
  | _, _, _, _, .fo hA h, ls => by rw [vC_ls _ hA ls []]; exact h
  | _, _, _, _, .tensor h₁ h₂ hc, ls =>
      ⟨_, _, pure_sep_mk rfl ⟨_, _, hc, htv_sound h₁ ls, htv_sound h₂ ls⟩⟩
  | _, δ, _, ρ, .thunkF (Δ := Δ) (Γ := Γ) (M := M) (A := A) (γ := γ) hd hδ hlive hg, ls => by
      intro ls' _
      refine cC_head (.ret A) (fun μ => Head.beta μ (Expr.psub 1 γ M) Val.unit) rfl ls' δ ρ ?_
      rw [← substAll_cons_psub']
      exact (fundamentalC (ℍ := ℍ) hd : SemC Δ (⟨.unit, false⟩ :: Γ) M (.ret A)) δ
        (Val.unit :: γ) ls' ρ hδ (gDenC_dead_cons _ _ (pure_sep_mk hlive (htg_sound hg ls')))
  | _, δ, _, ρ, .thunkV (Δ := Δ) (Γ := Γ) (N := N) (C := C) (γ := γ) hC hd hδ hlive hg, ls => by
      intro ls' _
      rw [forceE_of_not_ret hC]
      exact (fundamentalC (ℍ := ℍ) hd : SemC Δ Γ (.val (.lam N)) C) δ γ ls' ρ hδ
        (pure_sep_mk hlive (htg_sound hg ls'))

/-- **A hereditarily typed context is in `⊛ 𝒱⟦Γ(x)⟧`**, at every record list. -/
theorem htg_sound : ∀ {Γ : Ctx VTy} {δ : LSub} {γ : List Val} {ρ : WRes}, HTG (ℍ := ℍ) Γ δ γ ρ →
    ∀ ls : List SRec, gSepC (ℍ := ℍ) ls δ Γ γ ρ
  | _, _, _, _, .nil, ls => by cases ‹List Val› <;> exact ⟨rfl, trivial⟩
  | _, _, _, _, .noVal, _ => ⟨rfl, trivial⟩
  | s :: Γ, δ, v :: γ, ρ, .live hl h₁ h₂ hc, ls => by
      unfold gSepC; rw [if_pos hl]
      exact ⟨_, _, hc, htv_sound h₁ ls, htg_sound h₂ ls⟩
  | s :: Γ, δ, v :: γ, ρ, .dead hl h, ls => by
      unfold gSepC; rw [if_neg (by simp [hl])]
      exact htg_sound h ls
end

/-! ### Re-lending -/

section Relend
variable {c : Life} (θ : Restrat.Emb c)

mutual
/-- **A hereditarily typed value re-lends at every re-making**, to a value hereditarily typed at
the moved reading. -/
theorem htv_relend : ∀ {A : VTy} {δ : LSub} {v : Val} {ρ : WRes}, HTV (ℍ := ℍ) A δ v ρ →
    ∃ ρ', RemakeR θ ρ ρ' ∧ HTV (ℍ := ℍ) A (mv θ δ) v ρ'
  | _, δ, v, ρ, .fo (A := A) hA h => by
      obtain ⟨ρ', hR, h'⟩ := relend_fov θ A hA [] δ v ρ h []
      exact ⟨ρ', hR, .fo hA h'⟩
  | _, _, _, _, .tensor h₁ h₂ hc => by
      obtain ⟨ρ₁', hR₁, h₁'⟩ := htv_relend h₁
      obtain ⟨ρ₂', hR₂, h₂'⟩ := htv_relend h₂
      obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc hR₁ hR₂
      exact ⟨ρ', hR, .tensor h₁' h₂' hc'⟩
  | _, δ, _, _, .thunkF (Δ := Δ) hd hδ hlive hg => by
      obtain ⟨ρ', hR, hg'⟩ := htg_relend hg
      exact ⟨ρ', hR, .thunkF hd ((θ.models_mapN_iff Δ δ).mpr hδ) hlive hg'⟩
  | _, δ, _, _, .thunkV (Δ := Δ) hC hd hδ hlive hg => by
      obtain ⟨ρ', hR, hg'⟩ := htg_relend hg
      exact ⟨ρ', hR, .thunkV hC hd ((θ.models_mapN_iff Δ δ).mpr hδ) hlive hg'⟩

/-- **A hereditarily typed context re-lends at every re-making**, slot by slot. -/
theorem htg_relend : ∀ {Γ : Ctx VTy} {δ : LSub} {γ : List Val} {ρ : WRes},
    HTG (ℍ := ℍ) Γ δ γ ρ → ∃ ρ', RemakeR θ ρ ρ' ∧ HTG (ℍ := ℍ) Γ (mv θ δ) γ ρ'
  | _, _, _, _, .nil => ⟨PMap.empty, remakeR_empty, .nil⟩
  | _, _, _, _, .noVal => ⟨PMap.empty, remakeR_empty, .noVal⟩
  | _, _, _, _, .live hl h₁ h₂ hc => by
      obtain ⟨ρ₁', hR₁, h₁'⟩ := htv_relend h₁
      obtain ⟨ρ₂', hR₂, h₂'⟩ := htg_relend h₂
      obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc hR₁ hR₂
      exact ⟨ρ', hR, .live hl h₁' h₂' hc'⟩
  | _, _, _, _, .dead hl h => by
      obtain ⟨ρ', hR, h'⟩ := htg_relend h
      exact ⟨ρ', hR, .dead hl h'⟩
end

/-- **A hereditarily typed value re-lends at every type and every record list**: its re-make is in
Core's relation at the moved reading. At `U C` this is the hereditary form of
`relend_derivable`: the closure's body is re-derived at the moved reading. -/
theorem htv_relend_vC {A : VTy} {δ : LSub} {v : Val} {ρ : WRes} (h : HTV (ℍ := ℍ) A δ v ρ)
    (ls : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ vCE (ℍ := ℍ) none true A ls (mv θ δ) v ρ' := by
  obtain ⟨ρ', hR, h'⟩ := htv_relend θ h
  exact ⟨ρ', hR, htv_sound h' ls⟩

end Relend

end Law2

end
