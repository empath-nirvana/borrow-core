import MintProbe.Shared
import MintProbe.Pointee

/-!
# Views — the shared borrow in use

* `wp_I_frame_of_mint`: `[TR]` 6.64 as printed is `wp_mint_frame` at its one cell
  (`mint_single`), so the generalisation keeps the printed rule.
* `shrV_copy`: a shared borrow duplicates (`copy`, `[TR]` 6.116 at every view).
* `derefN_sem`: `n` successive `deref`s from `Shr α (Refⁿ S)` end at `Shr α S`, at the same
  `α` throughout — a stored iterator's state keeps one type as it advances.
* `minted_projection`: at `ℓ ↦ own(ℓ₁) ● ℓ₁ ↦ own(())`, the shared borrow at `α` is
  `ptrBorrow α ℓ ℓ₁` (the first pass's configuration, `[TR]` p. 4's `Imm @a (Ref 1)`) with one
  more cell, the view `ℓ₁ ↦ imm({α}, (), ∅)`, and from it `deref ℓ` returns `𝒱⟦Imm @a 1⟧`.
  `no_view_of_pointee` says no expression does this from `ptrBorrow α ℓ ℓ₁` alone: the view is
  what the share frame adds.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.MintProbe
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.BoLo (Heap Steps Kont)
open BoCa.Lifetime (LSub)

/-! ### `[TR]` 6.64 is the one-cell instance -/

/-- `A ─⋆ (B ─⋆ C) ⊨ A ⋆ B ─⋆ C`. -/
theorem wand_uncurry (A B C : WProp) : Entails (A ─⋆ (B ─⋆ C)) ((A ⋆ B) ─⋆ C) := by
  rintro ρ h ρ₁ ρ₂ ⟨ρa, ρb, hab, ha, hb⟩ hc
  obtain ⟨x, hx, hxb⟩ := (ResU.CompS.assoc ρ ρa ρb ρ₂).mp ⟨ρ₁, hab, hc⟩
  exact h ρa x ha hx ρb ρ₂ hb hxb

/-- **`[TR]` 6.64 from the mint frame**: the printed Imm Frame, with `wp_mint_frame` at the
one cell `ℓ ↦ imm({α}, v, ρ_P̂(v))` (`mint_single`). -/
theorem wp_I_frame_of_mint (l : Loc) (P : Val → WProp) (v : Val) (e : Expr)
    (Q : Val → WProp) :
    Entails
      (ptoOwn l v ⋆ P v ⋆
        fresh (fun α => ptoImm l α P ─⋆
          wp e (fun v' => box α (ptoOwn l v ─⋆ (P v ─⋆ Q v')))))
      (wp e Q) := by
  intro ρ h
  refine wp_mint_frame (ptoOwn l v ⋆ P v) (fun α => ptoImm l α P) e Q ?_ ρ ?_
  · rintro α ρo ⟨L, ρP, hc, rfl, hP⟩ hα hvo
    have hPα : ρP.InStratum (LSet.singleton α).join := ResU.CompS.inStratum_right hc hα
    exact ⟨_, mint_single (ResU.CompS.comm hc) hvo,
      ⟨LSet.singleton α, v, ρP, hPα, rfl, hP, le_refl α⟩⟩
  · obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := sep_assoc' _ _ _ ρ h
    refine ⟨ρ₁, ρ₂, hc, h₁, ?_⟩
    obtain ⟨β, hβ⟩ := h₂
    refine ⟨β, fun α hα => ?_⟩
    obtain ⟨hw, hout⟩ := hβ α hα
    refine ⟨fun ρ₃ ρ₄ hI hc' => ?_, hout⟩
    exact wp_mono (fun v' ρ₅ ⟨hb, ho⟩ => ⟨wand_uncurry _ _ _ ρ₅ hb, ho⟩) e ρ₄
      (hw ρ₃ ρ₄ hI hc')

/-! ### Copy -/

/-- A resource of `imm` cells composes with itself to itself. -/
theorem compS_self_of_imm {ρ : WRes} (h : ∀ m ψ, ρ.get m = some ψ → ψ.kind = Kind.imm) :
    ResU.CompS ρ ρ ρ := by
  refine ResU.Comp.of_pointwise (fun _ _ _ hc => CellU.CompS.compat hc) (fun m => ?_)
  cases e : ρ.get m with
  | none => rfl
  | some ψ =>
      obtain ⟨s, hs, heta⟩ := CellU.imm_eta (h m ψ e)
      have h₃ : ψ.wit.InStratum (s ∪ s).join := by rw [LSet.union_self]; exact hs
      exact ⟨ψ, rfl, s, s, ψ.erase, ψ.wit, hs, hs, h₃, heta, heta,
        heta.trans (CellU.immOf_congr (LSet.union_self s).symm rfl rfl hs h₃)⟩

/-- The views are `imm` cells. -/
theorem shrV_imm (α : Life) (δ : LSub) :
    ∀ (T : Ty) (v : Val) (ρ : WRes), shrV α T δ v ρ →
      ∀ m ψ, ρ.get m = some ψ → ψ.kind = Kind.imm := by
  intro T
  induction T with
  | unit => rintro v ρ ⟨rfl, -⟩ m ψ e; cases e
  | tensor T₁ T₂ ih₁ ih₂ =>
      rintro v ρ ⟨v₁, v₂, p₀, Q, hp₀, ⟨rfl, -⟩, ρ₁, ρ₂, hQ, h₁, h₂⟩ m ψ e
      obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
      rcases ResU.Comp.get hQ m with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
      · rw [f] at e; cases e
      · rw [f] at e; cases Option.some.inj e; exact ih₁ v₁ ρ₁ h₁ m _ f₁
      · rw [f] at e; cases Option.some.inj e; exact ih₂ v₂ ρ₂ h₂ m _ f₂
      · rw [f] at e; cases Option.some.inj e; exact CellU.CompS.kind hC
  | sum T₁ T₂ ih₁ ih₂ =>
      rintro v ρ (⟨v₁, p₀, ρ₁, hp₀, ⟨rfl, -⟩, h₁⟩ | ⟨v₂, p₀, ρ₂, hp₀, ⟨rfl, -⟩, h₂⟩)
      · obtain rfl : ρ₁ = ρ := ResU.eq_of_comp_empty_left hp₀; exact ih₁ v₁ ρ₁ h₁
      · obtain rfl : ρ₂ = ρ := ResU.eq_of_comp_empty_left hp₀; exact ih₂ v₂ ρ₂ h₂
  | lolli _ _ _ _ => rintro v ρ ⟨rfl, -⟩ m ψ e; cases e
  | ref S ih =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, ⟨rfl, -⟩, H, V, hHV, ⟨s, w, σ, hs, rfl, -, -⟩, hV⟩ m ψ e
      obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
      rcases ResU.Comp.get hHV m with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
      · rw [f] at e; cases e
      · rw [f] at e; cases Option.some.inj e
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some f₁; rfl
      · rw [f] at e; cases Option.some.inj e; exact ih u V hV m _ f₂
      · rw [f] at e; cases Option.some.inj e; exact CellU.CompS.kind hC
  | imm _ _ _ => rintro v ρ ⟨rfl, -⟩ m ψ e; cases e
  | «mut» _ S _ =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, ⟨rfl, -⟩, ⟨s, w, σ, hs, hQ, -, -⟩⟩ m ψ e
      obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
      rw [hQ] at e
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; rfl
  | box _ S ih => exact ih
  | bang _ _ => rintro v ρ ⟨rfl, -⟩ m ψ e; cases e
  | all _ _ _ _ => rintro v ρ ⟨rfl, -⟩ m ψ e; cases e
  | unk => rintro v ρ ⟨rfl, -⟩ m ψ e; cases e

/-- **Copy**: `Shr α T(w) ⊨ Shr α T(w) ⋆ Shr α T(w)`. -/
theorem shrV_copy (α : Life) (T : Ty) (δ : LSub) (w : Val) :
    Entails (shrV α T δ w) (shrV α T δ w ⋆ shrV α T δ w) := fun ρ h =>
  ⟨ρ, ρ, compS_self_of_imm (shrV_imm α δ T w ρ h), h, h⟩

/-! ### Iterating `deref` -/

/-- `Refⁿ S`. -/
def refN : ℕ → Ty → Ty
  | 0, S => S
  | n + 1, S => .ref (refN n S)

theorem refN_succ' : ∀ (n : ℕ) (S : Ty), refN (n + 1) S = refN n (.ref S)
  | 0, _ => rfl
  | n + 1, S => by
      show Ty.ref (refN (n + 1) S) = Ty.ref (refN n (.ref S))
      rw [refN_succ' n S]

/-- `deref (deref (… e))`, `n` times. -/
def derefN : ℕ → Expr → Expr
  | 0, e => e
  | n + 1, e => .app (.val derefV) (derefN n e)

/-- **The iterator keeps its lifetime.**  `n` successive `deref`s take `Shr α (Refⁿ S)` to
`Shr α S` at the same `α`.  Through `[TR]`'s `withload`, each step is a fresh `'b`, shorter
than the last. -/
theorem derefN_sem (α : Life) (δ : LSub) :
    ∀ (n : ℕ) (S : Ty) (w : Val),
      Entails (shrDen α (refN n S) δ w) (wp (derefN n (.val w)) (shrDen α S δ)) := by
  intro n
  induction n with
  | zero => intro S w ρ h; exact wp_val w _ ρ h
  | succ n ih =>
      intro S w ρ h
      rw [refN_succ'] at h
      show wp ((Kont.appR (.val derefV) .hole).plug (derefN n (.val w))) _ ρ
      refine wp_bind _ _ _ ρ ?_
      exact wp_mono (fun w' ρ' h' => deref_sem α S δ w' ρ' h') _ ρ (ih (.ref S) w ρ h)

/-! ### The minted view, against the first pass's configuration -/

/-- **The projection at a concrete minted resource.**  At `ℓ ↦ own(ℓ₁) ● ℓ₁ ↦ own(())`, the
share frame's resource at `α` is `ptrBorrow α ℓ ℓ₁ ● V` — the first pass's configuration, a
member of `𝒱⟦Imm @a (Ref 1)⟧δ(ℓ)`, and one `imm` cell `V` at `ℓ₁` — and from it `deref ℓ`
returns a member of `𝒱⟦Imm @a 1⟧δ` at the same `α`.  Compare `no_view_of_pointee`. -/
theorem minted_projection {a : Lifetime.Life} {δ : LSub} {α : Life} (ha : a.interp δ = some α)
    {l l₁ : Loc} (hne : l ≠ l₁) :
    ∃ V Y, ResU.CompS (ptrBorrow α l l₁) V Y ∧ NoOwn V ∧
      (∀ m ψ, V.get m = some ψ → m = l₁) ∧
      wp (.app (.val derefV) (.val (Val.loc l))) (vDen (.imm a .unit) δ) Y := by
  obtain ⟨W, hW, hvW⟩ := owned_valid hne
  obtain ⟨V, Y, hY, -, hYS, hV, hdom⟩ :=
    mint_shr_of (α := α) (ResU.CompS.comm hW) (vDen_ref_unit δ l₁)
      (single_own_inStratum _ _ _) hvW
  refine ⟨V, Y, hY, shrV_noOwn α δ _ _ V hV, fun m ψ e => ?_, ?_⟩
  · obtain ⟨c, hc, -⟩ := hdom m ψ e
    exact (ResU.single_get_eq_some hc).1
  · refine wp_mono (fun w ρ h => ?_) _ Y (deref_sem α .unit δ (Val.loc l) Y hYS)
    obtain ⟨ℓ, u, p₀, Q, hp₀, ⟨rfl, hw⟩, H, Vu, hHV, ⟨s, u', σ, hs, rfl, ⟨-, hσ⟩, hle⟩,
      ⟨rfl, -⟩⟩ := h
    obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
    obtain rfl := ResU.eq_of_comp_empty_right hHV
    exact ⟨α, ha, ℓ, PMap.empty, _, ResU.comp_empty_left _, ⟨rfl, hw⟩,
      s, u', σ, hs, rfl, hσ, hle⟩

end BoCa.MintProbe

end
