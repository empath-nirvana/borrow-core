import MintProbe.Uses

/-!
# MintProbe — the grounding programs at the paper level

The probe's G1 and G2 (`kernel/999/probe-plan.md` §4), at `[TR]`'s `wp`, for every owner of the
right shape:

* **G1, the getter through two owned pointers at one lifetime** (`g1_shape`):
  - The owner is `ℓ ↦ v ⋆ 𝒱⟦Ref (Ref S)⟧δ(v)`, valid and in `Res_α`.
  - It mints a shared borrow at `α` (`mint_shr`).
  - `deref (deref ℓ)` then returns `Shr α S`, still at `α` (`derefN_sem`).
* **G2, `&&mut T → &T` at the outer lifetime** (`g2_shape`, `g2_deep`):
  - The owner is a box `ℓ ↦ t ⋆ 𝒱⟦Mut @a S⟧δ(t)`, i.e. a `Mut` held by an owned pointer, valid
    and in `Res_α`.
  - It mints, including the view of the `mut` target (`Mint.addMut`) and, below it, the views
    of what the target owns (`Reach.mutWit`).
  - `deref (load ℓ)` returns the target's value with its views, at `α` (`g2_shape`; `()` at
    `S = 1`, `g2_value`); at `S = Ref S'`, one more `deref` reads the cell the target owns, at `α` (`g2_deep`).
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

/-- **G1.** An owned `Ref (Ref S)` at `ℓ` mints a shared borrow at `α`, from which two
`deref`s reach `S` at the same `α`. -/
theorem g1_shape {α : Life} {l : Loc} {v : Val} {S : Ty} {δ : LSub} {ρo : WRes}
    (hP : (ptoOwn l v ⋆ vDen (.ref (.ref S)) δ v) ρo) (hα : ρo.InStratum α)
    (hvo : ResU.Valid ρo) :
    ∃ Y, Mint α ρo Y ∧
      wp (derefN 2 (.val (Val.loc l))) (shrDen α S δ) Y := by
  obtain ⟨Y, hM, hY⟩ := mint_shr hP hα hvo
  exact ⟨Y, hM, derefN_sem α δ 2 S (Val.loc l) Y hY⟩

/-- **G2.** A box holding a `Mut @a S` (the target `t ↦ mut(b, u, χ, 𝒱⟦S⟧)`) mints a shared
borrow at `α` that includes the view of the `mut` target and the target's own views. Loading the
box and then the target returns the target's value with its views, at the outer `α`. -/
theorem g2_shape {α : Life} {l : Loc} {v : Val} {a : Lifetime.Life} {S : Ty} {δ : LSub}
    {ρo : WRes} (hP : (ptoOwn l v ⋆ vDen (.mut a S) δ v) ρo) (hα : ρo.InStratum α)
    (hvo : ResU.Valid ρo) :
    ∃ Y, Mint α ρo Y ∧
      wp (.app (.val derefV) (.app (.val (.prim .load)) (.val (Val.loc l)))) (shrV α S δ) Y := by
  obtain ⟨Y, hM, hY⟩ := mint_shr hP hα hvo
  refine ⟨Y, hM, ?_⟩
  show wp ((Kont.appR (.val derefV) .hole).plug (.app (.val (.prim .load)) (.val (Val.loc l))))
    _ Y
  refine wp_bind _ _ _ Y ?_
  exact wp_mono (fun w ρ' h' => deref_mut_sem α a S δ w ρ' h') _ Y
    (wp_load_S α (.mut a S) δ l Y hY)

/-- In G2 at `S = 1` the value returned is `()`. -/
theorem g2_value {α : Life} {δ : LSub} {u : Val} {ρ : WRes}
    (h : shrV α .unit δ u ρ) : u = .unit := h.1

/-- **G2 below the target.**  A box holding a `Mut @a (Ref S)`: the shared borrow minted at `α`
reaches past the `mut` target into the cell the target owns, so `deref (load ℓ)` is `Shr α S`
and one more `deref` returns the stored `S` with its views, at the outer `α`. -/
theorem g2_deep {α : Life} {l : Loc} {v : Val} {a : Lifetime.Life} {S : Ty} {δ : LSub}
    {ρo : WRes} (hP : (ptoOwn l v ⋆ vDen (.mut a (.ref S)) δ v) ρo) (hα : ρo.InStratum α)
    (hvo : ResU.Valid ρo) :
    ∃ Y, Mint α ρo Y ∧
      wp (.app (.val derefV) (.app (.val derefV) (.app (.val (.prim .load))
        (.val (Val.loc l))))) (shrV α S δ) Y := by
  obtain ⟨Y, hM, hY⟩ := g2_shape hP hα hvo
  refine ⟨Y, hM, ?_⟩
  show wp ((Kont.appR (.val derefV) .hole).plug
    (.app (.val derefV) (.app (.val (.prim .load)) (.val (Val.loc l))))) _ Y
  refine wp_bind _ _ _ Y ?_
  exact wp_mono (fun w ρ' h' => deref_shr α S δ w ρ' h') _ Y hY

/-- **The deciding check, at a `mut` cell.**  A `mut` cell in the walk of an `imm` cell's
witness keeps its value across every run: `↭`'s `imm` clause pins the ancestor exactly, and
the walk under it is then a factor of the end's flattening.  `frozen_under_imm` at `ψ = mut`. -/
theorem frozen_mut_under_imm {ρ π σ τ : WRes} (hupd : ResU.UpdV ρ π) (hσ : ResU.Flat ρ σ)
    (hτ : ResU.Flat π τ) {l : Loc} {s : LSet} {v : Val} {w : WRes} {h : w.InStratum s.join}
    (hc : σ.get l = some (CellU.immOf s v w h)) {f : WRes} (hf : ResU.FlatR w f) {m : Loc}
    {b : Life} {u : Val} {χ : WRes} {hb : χ.InStratum b} {P : Val → SPropS Loc Val b}
    {hP : P u ⟨χ, hb⟩} (hm : f.get m = some (CellU.mutOf b u χ hb P hP)) :
    ∃ χ', τ.get m = some χ' ∧ χ'.erase = u := by
  obtain ⟨χ', h₁, h₂⟩ := frozen_under_imm hupd hσ hτ hc hf hm
  exact ⟨χ', h₁, by rw [h₂]; simp⟩

end BoCa.MintProbe

end
