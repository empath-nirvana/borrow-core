import MintProbe.Frame

/-!
# Views — a shared borrow that reaches through owned pointers

`shrDen α T δ` is a borrow of a `T` at `α` that carries, besides `[TR]` p. 4's cell
`ℓ ↦ Imm α 𝒱⟦T⟧δ`, a view at the same `α` of every location the value reaches through owned
pointers (`Ref`, through `⊗`, `⊕` and `[@a]`).  Each view is the cell 6.64 would make for that
pointee, `ℓ₁ ↦ imm({α}, u, ρ_u)` with `ρ_u ∈ 𝒱⟦S⟧δ(u)`, so every `imm` cell at a location
carries the witness the owning payload gives it ([CONF] 415:19).  It is RustBelt's sharing
predicate for `Box` (`&'a Box<T>` shares the pointee at `'a`) in `[TR]`'s model.

* `shrV α T δ v`: the views of the pointees of `v : T`; `shrDen α T δ = shrV α (Ref T) δ`.
* `mint_shr`: an owned `ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v)` in `Res_α` mints `shrDen α T δ (ℓ)` over itself.
* `wp_S_frame`: `[TR]` 6.64 with `shrDen` in place of `Imm` — the shared borrow is made where
  6.64 makes the plain one, from ownership, and its views end with the frame.
* `deref_sem`: `λx. load x` takes `shrDen α (Ref T)` to `shrDen α T`, at the same `α` — the
  projection `Imm 'a (Ref T) → Imm 'a T` read at `shrDen`.

`[TR]` p. 6's `wp` and its `↭` are unchanged.  A run cannot create an `imm` cell (`↭`'s clause
(1)), and none is created here during a run: the views exist from the frame's start.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.MintProbe
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.BoLo (Heap Steps)
open BoCa.Lifetime (LSub)

/-- The payload of a view: the value is `u` and the witness is in `𝒱⟦T⟧δ(u)`. -/
def viewPayload (T : Ty) (δ : LSub) (u : Val) : Val → WProp :=
  fun u' σ => u' = u ∧ vDen T δ u' σ

/-- `shrV α T δ v`: the views at `α` of the locations `v : T` reaches through owned pointers.
At `Ref T` a view of the pointee, with the pointee's own views; through `⊗`, `⊕` and `[@a]`
componentwise; at `Mut β T` a view of the `mut` target at `α` (the frozen `Mut`, theory's
derived-views §8; the target's own reach is not minted here); nothing at `1`'s value
constraint aside, and nothing behind `⊸`, `∀`, `Imm` and `Unk`.  `[about ours]` -/
def shrV (α : Life) : Ty → LSub → Val → WProp
  | .unit, _, v => ⌜v = .unit⌝
  | .tensor T₁ T₂, δ, v =>
      ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ shrV α T₁ δ v₁ ⋆ shrV α T₂ δ v₂
  | .sum T₁ T₂, δ, v =>
      BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ shrV α T₁ δ v₁)
              (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ shrV α T₂ δ v₂)
  | .ref T, δ, v =>
      ex fun ℓ => ex fun u => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (viewPayload T δ u) ⋆ shrV α T δ u
  | .box _ T, δ, v => shrV α T δ v
  | .lolli _ _, _, _ => emp
  | .all _ _ _, _, _ => emp
  | .imm _ _, _, _ => emp
  | .mut _ T, δ, v =>
      ex fun ℓ => ex fun u => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (viewPayload T δ u)
  | .bang _, _, _ => emp
  | .unk, _, _ => emp

/-- `shrDen α T δ`: a shared borrow of a `T` at `α` — the value is a location `ℓ`, with
`ℓ ↦ Imm α 𝒱⟦T⟧δ` at its value and the views of what it reaches.  `[about ours]` -/
def shrDen (α : Life) (T : Ty) (δ : LSub) : Val → WProp := shrV α (.ref T) δ

/-! ### Minting the views -/

/-- A `●`-factor is `≤` the composite. -/
theorem le_of_compS_left {a b c : WRes} (h : ResU.CompS a b c) : ResU.Le a c := ⟨b, h⟩

theorem le_of_compS_right {a b c : WRes} (h : ResU.CompS a b c) : ResU.Le b c :=
  ⟨a, ResU.CompS.comm h⟩

/-- A top-level `own` cell of a resource `≤ O` is a top-level `own` cell of `O`. -/
theorem own_of_le {P O : WRes} (h : ResU.Le P O) {m : Loc} {u : Val}
    (e : P.get m = some (CellU.ownOf u)) : O.get m = some (CellU.ownOf u) := by
  obtain ⟨r, hr⟩ := h
  exact (ResU.CompS.get_left_of_ne_imm hr e (by simp)).2

/-- Two `●`-factors hold no `own` cell at one location. -/
theorem own_disjoint {a b c : WRes} (h : ResU.CompS a b c) {m : Loc} {u : Val}
    (e : a.get m = some (CellU.ownOf u)) : b.get m = none :=
  ResU.CompatS.right_eq_none h.1 e (by simp)

/-- A non-`imm` cell of a resource `≤ O` is a top-level cell of `O`. -/
theorem nonimm_of_le {P O : WRes} (h : ResU.Le P O) {m : Loc} {c : CellU Loc Val}
    (e : P.get m = some c) (hk : c.kind ≠ Kind.imm) : O.get m = some c := by
  obtain ⟨r, hr⟩ := h
  exact (ResU.CompS.get_left_of_ne_imm hr e hk).2

/-- Two `●`-factors hold no non-`imm` cell at one location. -/
theorem nonimm_disjoint {a b c : WRes} (h : ResU.CompS a b c) {m : Loc} {x : CellU Loc Val}
    (e : a.get m = some x) (hk : x.kind ≠ Kind.imm) : b.get m = none :=
  ResU.CompatS.right_eq_none h.1 e hk

/-- The walk of a top-level `mut` cell's witness is a `○`-factor of `⦇O⦈`. -/
theorem mutWit_flatR_factor {O : WRes} (hvO : ResU.Valid O) {ℓ : Loc} {ψ : CellU Loc Val}
    (e : O.get ℓ = some ψ) (hk : ψ.kind = Kind.mut) :
    ∃ σw, ResU.FlatR ψ.wit σw ∧ ∀ σ, ResU.Flat O σ → ∃ z, ResU.CompR σw z σ := by
  obtain ⟨σ₀, eO, aO, heO, haO, hcO⟩ := hvO
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨ev, z₁, hev, hz₁⟩ := ExW.wit_le hR ResU.compLawsR (ExS.toExR heO) e hk
  obtain ⟨av, z₂, hav, hz₂⟩ := AgW.mut_wit_le haO e hk
  obtain ⟨S₁, S₂, h₁, -, h₃⟩ := (ResU.CompR.exchange₄ ev z₁ av z₂ σ₀).mp
    ⟨eO, aO, hz₁, hz₂, ResU.CompS.toCompR hcO⟩
  refine ⟨S₁, ⟨av, ev, hav, hev, ResU.CompR.comm h₁⟩, fun σ hσ => ?_⟩
  rw [ResU.Flat.functional hσ ⟨eO, aO, heO, haO, hcO⟩]
  exact ⟨S₂, h₃⟩

/-- **The views mint.**  For `v : T` owned as `P ≤ O` in `Res_α`, a mint `Y₀` over `O` that
holds none of `P`'s non-`imm` cells extends by `shrV α T δ v`'s views to a mint over `O`; the
views sit on `P`'s non-`imm` cells.  By induction on `T`: at `Ref` by `Mint.add_le`, at `Mut` by
`Mint.addMut` (the view of the `mut` target, `α ⊑ β` from `P ∈ Res_α`). -/
theorem mint_views {α : Life} {O : WRes} (hvO : ResU.Valid O) (δ : LSub) :
    ∀ (T : Ty) (v : Val) (P Y₀ : WRes), vDen T δ v P → ResU.Le P O → P.InStratum α →
      Mint α O Y₀ →
      (∀ m c, P.get m = some c → c.kind ≠ Kind.imm → Y₀.get m = none) →
      ∃ V Y, ResU.CompS Y₀ V Y ∧ Mint α O Y ∧ shrV α T δ v V ∧
        (∀ m ψ, V.get m = some ψ → ∃ c, P.get m = some c ∧ c.kind ≠ Kind.imm) := by
  intro T
  induction T with
  | unit =>
      intro v P Y₀ hP _ _ hM _
      obtain ⟨rfl, hv⟩ := hP
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, hv⟩,
        fun m ψ e => by simp at e⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨v₁, v₂, p₀, Q, hp₀Q, ⟨rfl, hv⟩, P₁, P₂, hQ, hP₁, hP₂⟩ := hP
      obtain rfl : Q = P := ResU.eq_of_comp_empty_left hp₀Q
      have hP₁O : ResU.Le P₁ Q := le_of_compS_left hQ
      have hP₂O : ResU.Le P₂ Q := le_of_compS_right hQ
      obtain ⟨V₁, Y₁, hY₁, hM₁, hV₁, hdom₁⟩ :=
        ih₁ v₁ P₁ Y₀ hP₁ (hP₁O.trans hPO) (ResU.CompS.inStratum_left hQ hPα) hM
          (fun m c e hk => hY₀ m c (nonimm_of_le hP₁O e hk) hk)
      have hY₁' : ∀ m c, P₂.get m = some c → c.kind ≠ Kind.imm → Y₁.get m = none := by
        intro m c e hk
        refine (ResU.Comp.eq_none_iff hY₁ m).mpr ⟨hY₀ m c (nonimm_of_le hP₂O e hk) hk, ?_⟩
        cases eV : V₁.get m with
        | none => rfl
        | some ψ =>
            obtain ⟨c₁, e₁, hk₁⟩ := hdom₁ m ψ eV
            rw [nonimm_disjoint hQ e₁ hk₁] at e; cases e
      obtain ⟨V₂, Y₂, hY₂, hM₂, hV₂, hdom₂⟩ :=
        ih₂ v₂ P₂ Y₁ hP₂ (hP₂O.trans hPO) (ResU.CompS.inStratum_right hQ hPα) hM₁ hY₁'
      have hV₁₂ : ResU.CompatS V₁ V₂ := ResU.Compat.of_disjoint (fun m => by
        cases e₁ : V₁.get m with
        | none => exact Or.inl rfl
        | some ψ =>
            refine Or.inr ?_
            cases e₂ : V₂.get m with
            | none => rfl
            | some χ =>
                obtain ⟨c₁, f₁, hk₁⟩ := hdom₁ m ψ e₁
                obtain ⟨c₂, f₂, -⟩ := hdom₂ m χ e₂
                rw [nonimm_disjoint hQ f₁ hk₁] at f₂; cases f₂)
      obtain ⟨V, hV⟩ := (ResU.compS_defined_iff V₁ V₂).mpr hV₁₂
      obtain ⟨Y', hY', hY'Y⟩ := (ResU.CompS.assoc Y₀ V₁ V₂ Y₂).mpr ⟨Y₁, hY₁, hY₂⟩
      rw [ResU.CompS.functional hY' hV] at hY'Y
      refine ⟨V, Y₂, hY'Y, hM₂, ⟨v₁, v₂, PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, hv⟩,
        V₁, V₂, hV, hV₁, hV₂⟩, fun m ψ e => ?_⟩
      rcases ResU.Comp.get hV m with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
      · rw [f] at e; cases e
      · obtain ⟨c, hc, hk⟩ := hdom₁ m χ f₁; exact ⟨c, nonimm_of_le hP₁O hc hk, hk⟩
      · obtain ⟨c, hc, hk⟩ := hdom₂ m χ f₂; exact ⟨c, nonimm_of_le hP₂O hc hk, hk⟩
      · obtain ⟨c, hc, hk⟩ := hdom₁ m χ₁ f₁; exact ⟨c, nonimm_of_le hP₁O hc hk, hk⟩
  | sum T₁ T₂ ih₁ ih₂ =>
      intro v P Y₀ hP hPO hPα hM hY₀
      rcases hP with ⟨v₁, p₀, P₁, hp₀, ⟨rfl, hv⟩, hP₁⟩ | ⟨v₂, p₀, P₂, hp₀, ⟨rfl, hv⟩, hP₂⟩
      · obtain rfl : P₁ = P := ResU.eq_of_comp_empty_left hp₀
        obtain ⟨V, Y, hY, hMY, hV, hdom⟩ := ih₁ v₁ P₁ Y₀ hP₁ hPO hPα hM hY₀
        exact ⟨V, Y, hY, hMY, Or.inl ⟨v₁, PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, hv⟩, hV⟩,
          hdom⟩
      · obtain rfl : P₂ = P := ResU.eq_of_comp_empty_left hp₀
        obtain ⟨V, Y, hY, hMY, hV, hdom⟩ := ih₂ v₂ P₂ Y₀ hP₂ hPO hPα hM hY₀
        exact ⟨V, Y, hY, hMY, Or.inr ⟨v₂, PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, hv⟩, hV⟩,
          hdom⟩
  | lolli T₁ T₂ _ _ =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun m ψ e => by simp at e⟩
  | ref S ih =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨ℓ, v', p₀, Q, hp₀Q, ⟨rfl, hv⟩, L, P₁, hQ, rfl, hP₁⟩ := hP
      obtain rfl : Q = P := ResU.eq_of_comp_empty_left hp₀Q
      have hLself : (ResU.single ℓ (CellU.ownOf v')).get ℓ = some (CellU.ownOf v') :=
        ResU.single_get_self _ _
      have hPℓ : Q.get ℓ = some (CellU.ownOf v') :=
        (ResU.CompS.get_left_of_ne_imm hQ hLself (by simp)).2
      have hP₁ℓ : P₁.get ℓ = none := own_disjoint hQ hLself
      have hP₁Q : ResU.Le P₁ Q := le_of_compS_right hQ
      have hP₁α : P₁.InStratum α := ResU.CompS.inStratum_right hQ hPα
      obtain ⟨Y₁, hY₁, hM₁⟩ := Mint.add_le (w := P₁) (h := hP₁α) hM hvO
        (fun eO heO => ExS.get_of_ne_imm heO (own_of_le hPO hPℓ) (by simp))
        (hY₀ ℓ _ hPℓ (by simp)) (hP₁Q.trans hPO)
      have hY₁' : ∀ m c, P₁.get m = some c → c.kind ≠ Kind.imm → Y₁.get m = none := by
        intro m c e hk
        refine (ResU.Comp.eq_none_iff hY₁ m).mpr
          ⟨hY₀ m c (nonimm_of_le hP₁Q e hk) hk, ?_⟩
        have hm : m ≠ ℓ := by rintro rfl; rw [hP₁ℓ] at e; cases e
        exact ResU.single_get_ne _ hm
      obtain ⟨V₁, Y₂, hY₂, hM₂, hV₁, hdom₁⟩ :=
        ih v' P₁ Y₁ hP₁ (hP₁Q.trans hPO) hP₁α hM₁ hY₁'
      set c := ResU.single ℓ (CellU.immOf (LSet.singleton α) v' P₁ hP₁α) with hcdef
      have hcV : ResU.CompatS c V₁ := ResU.Compat.of_disjoint (fun m => by
        by_cases hm : m = ℓ
        · subst hm
          refine Or.inr ?_
          cases e : V₁.get m with
          | none => rfl
          | some ψ => obtain ⟨c', hc', -⟩ := hdom₁ m ψ e; rw [hP₁ℓ] at hc'; cases hc'
        · exact Or.inl (ResU.single_get_ne _ hm))
      obtain ⟨V, hV⟩ := (ResU.compS_defined_iff c V₁).mpr hcV
      obtain ⟨Y', hY', hY'Y⟩ := (ResU.CompS.assoc Y₀ c V₁ Y₂).mpr ⟨Y₁, hY₁, hY₂⟩
      rw [ResU.CompS.functional hY' hV] at hY'Y
      refine ⟨V, Y₂, hY'Y, hM₂, ⟨ℓ, v', PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, hv⟩,
        c, V₁, hV, ⟨LSet.singleton α, v', P₁, hP₁α, rfl, ⟨rfl, hP₁⟩, le_refl α⟩, hV₁⟩,
        fun m ψ e => ?_⟩
      rcases ResU.Comp.get hV m with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
      · rw [f] at e; cases e
      · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some f₁; exact ⟨_, hPℓ, by simp⟩
      · obtain ⟨c', hc', hk⟩ := hdom₁ m χ f₂; exact ⟨c', nonimm_of_le hP₁Q hc' hk, hk⟩
      · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some f₁; exact ⟨_, hPℓ, by simp⟩
  | imm a S _ =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun m ψ e => by simp at e⟩
  | «mut» a S _ =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨α', -, ℓ, p₀, Q, hp₀Q, ⟨rfl, hv⟩, b, u, χ, hχ, Qp, hw, -, hQe, hQp⟩ := hP
      obtain rfl : Q = P := ResU.eq_of_comp_empty_left hp₀Q
      subst hQe
      have hPℓ : (ResU.single ℓ (CellU.mutOf b u χ hχ Qp hw)).get ℓ =
          some (CellU.mutOf b u χ hχ Qp hw) := ResU.single_get_self _ _
      have hkm : (CellU.mutOf b u χ hχ Qp hw).kind ≠ Kind.imm := by simp
      have hOℓ := nonimm_of_le hPO hPℓ hkm
      have hαb : α < b := hPα ℓ _ hPℓ
      have hχα : χ.InStratum (LSet.singleton α).join := ResU.InStratum.mono (le_of_lt hαb) hχ
      obtain ⟨σw, hfw, hfac⟩ := mutWit_flatR_factor hvO hOℓ (by simp)
      rw [CellU.wit_mutOf] at hfw
      obtain ⟨Y₁, hY₁, hM₁⟩ := Mint.addMut (h := hχα) hM hvO
        (fun eO heO => ExS.get_of_ne_imm heO hOℓ hkm) (hY₀ ℓ _ hPℓ hkm) hfw hfac
      have hd : vDen S δ u χ := by rw [← hQp]; exact ⟨hχ, hw⟩
      refine ⟨_, Y₁, hY₁, hM₁, ⟨ℓ, u, PMap.empty, _, ResU.comp_empty_left _, ⟨rfl, hv⟩,
        LSet.singleton α, u, χ, hχα, rfl, ⟨rfl, hd⟩, le_refl α⟩, fun m ψ e => ?_⟩
      obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
      exact ⟨_, hPℓ, hkm⟩
  | box a S ih =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨β, -, hPS, -⟩ := hP
      exact ih v P Y₀ hPS hPO hPα hM hY₀
  | bang S _ =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun m ψ e => by simp at e⟩
  | all x b S _ =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun m ψ e => by simp at e⟩
  | unk =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun m ψ e => by simp at e⟩

/-- **An owned value shares at `α`**, at a named decomposition `ρₒ = ℓ ↦ own(v) ● ρ_P`: the
minted resource is 6.64's cell `ℓ ↦ imm({α}, v, ρ_P)` and own-free views `V` on `ρ_P`'s `own`
cells. -/
theorem mint_shr_of {α : Life} {l : Loc} {v : Val} {T : Ty} {δ : LSub} {ρP ρo : WRes}
    (hc : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρo) (hρP : vDen T δ v ρP)
    (hPα : ρP.InStratum (LSet.singleton α).join) (hvo : ResU.Valid ρo) :
    ∃ V Y, ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v ρP hPα)) V Y ∧
      Mint α ρo Y ∧ shrDen α T δ (Val.loc l) Y ∧ shrV α T δ v V ∧
      (∀ m ψ, V.get m = some ψ → ∃ c, ρP.get m = some c ∧ c.kind ≠ Kind.imm) := by
  have hLself : (ResU.single l (CellU.ownOf v)).get l = some (CellU.ownOf v) :=
    ResU.single_get_self _ _
  have hPl : ρP.get l = none := own_disjoint hc hLself
  have hM₀ : Mint α ρo (ResU.single l (CellU.immOf (LSet.singleton α) v ρP hPα)) :=
    mint_single (ResU.CompS.comm hc) hvo
  obtain ⟨V, Y, hY, hM, hV, hdom⟩ := mint_views hvo δ T v ρP _ hρP (le_of_compS_right hc) hPα
    hM₀ (fun m c e _ => by
      have hm : m ≠ l := by rintro rfl; rw [hPl] at e; cases e
      exact ResU.single_get_ne _ hm)
  exact ⟨V, Y, hY, hM, ⟨l, v, PMap.empty, Y, ResU.comp_empty_left Y, ⟨rfl, rfl⟩, _, V, hY,
    ⟨LSet.singleton α, v, ρP, hPα, rfl, ⟨rfl, hρP⟩, le_refl α⟩, hV⟩, hV, hdom⟩

/-- **An owned value shares at `α`.**  `ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v)`, valid and in `Res_α`, mints
`shrDen α T δ (ℓ)` over itself: 6.64's cell `ℓ ↦ imm({α}, v, ρ_P̂(v))` and the views. -/
theorem mint_shr {α : Life} {l : Loc} {v : Val} {T : Ty} {δ : LSub} {ρo : WRes}
    (hP : (ptoOwn l v ⋆ vDen T δ v) ρo) (hα : ρo.InStratum α) (hvo : ResU.Valid ρo) :
    ∃ Y, Mint α ρo Y ∧ shrDen α T δ (Val.loc l) Y := by
  obtain ⟨L, ρP, hc, rfl, hρP⟩ := hP
  obtain ⟨-, Y, -, hM, hY, -⟩ := mint_shr_of hc hρP (ResU.CompS.inStratum_right hc hα) hvo
  exact ⟨Y, hM, hY⟩

/-! ### The share frame -/

/-- **The share frame** — `[TR]` 6.64 with the shared borrow:

    ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v) ⋆ (Иα. Shr α T(ℓ) ─⋆ wp(e){[α](ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v) ─⋆ Q̂)})  ⊨  wp(e){Q̂}.

`[about ours: an extension; `wp_mint_frame` at `mint_shr`]` -/
theorem wp_S_frame (l : Loc) (T : Ty) (δ : LSub) (v : Val) (e : Expr) (Q : Val → WProp) :
    Entails
      ((ptoOwn l v ⋆ vDen T δ v) ⋆
        fresh (fun α => shrDen α T δ (Val.loc l) ─⋆
          wp e (fun v' => box α ((ptoOwn l v ⋆ vDen T δ v) ─⋆ Q v'))))
      (wp e Q) :=
  wp_mint_frame _ _ e Q (fun _ _ hP hα hvo => mint_shr hP hα hvo)

/-! ### Reading through a shared borrow at its own lifetime -/

/-- **Same-lifetime load.**  Loading through `shrDen α T δ (ℓ)` returns the stored value with
its views at the same `α`: `load : Shr α T ⊸ Shr̲ α T`, where `Shr̲ α (Ref S) = Shr α S`
(`shrV`'s `Ref` clause).  The head cell `ℓ ↦ imm({α}, …)` goes to `ρ⁺` (`wp_frame_noOwn`). -/
theorem wp_load_S (α : Life) (T : Ty) (δ : LSub) (ℓ : Loc) :
    Entails (shrDen α T δ (Val.loc ℓ))
      (wp (.app (.val (.prim .load)) (.val (.loc ℓ))) (shrV α T δ)) := by
  rintro ρ ⟨ℓ', u, p₀, Q₀, hp₀, ⟨rfl, hℓ⟩, H, V, hHV, hH, hV⟩
  obtain rfl : Q₀ = ρ := ResU.eq_of_comp_empty_left hp₀
  have hℓℓ : ℓ = ℓ' := Val.loc_inj.mp hℓ
  subst hℓℓ
  refine wp_load_I_conf ℓ α (viewPayload T δ u) (shrV α T δ) Q₀ ⟨H, V, hHV, hH, ?_⟩
  rintro w ρ₁ ρ₂ ⟨s, w', σ, hs, rfl, ⟨rfl, -⟩, -⟩ hc
  refine wp_frame_noOwn (R := fun ρ => ρ = ResU.single ℓ (CellU.immOf s w' σ hs))
    (fun ρ e => e ▸ noOwn_single_imm ℓ s w' σ hs) _ _ ρ₂ ⟨_, V, ResU.CompS.comm hc, rfl, ?_⟩
  exact wp_val w _ V hV

/-- `deref ≜ λx. load x`. -/
def derefV : Val := Val.lam (.app (.prim .load) (.var 0))

/-- **The projection** `Imm 'a (Ref T) → Imm 'a T`, at `shrDen`: `deref` takes a shared borrow
of a `Ref T` at `α` to a shared borrow of the pointee at the same `α`. -/
theorem deref_sem (α : Life) (T : Ty) (δ : LSub) (w : Val) :
    Entails (shrDen α (.ref T) δ w) (wp (.app (.val derefV) (.val w)) (shrDen α T δ)) := by
  intro ρ hρ
  obtain ⟨ℓ, -, -, -, -, ⟨-, hw⟩, -⟩ := id hρ
  subst hw
  exact wp_lolli _ _ _ ρ (wp_load_S α (.ref T) δ ℓ ρ hρ)

/-- **`deref` is a closed term of type `Shr α (Ref T) ⊸ Shr α T`**: at the empty resource,
`∀w. Shr α (Ref T)(w) ─⋆ ℰ⟦Shr α T⟧(deref w)` — `𝒱⟦−⊸−⟧`'s clause (`[TR]` p. 4) with
`shrDen` at both ends. -/
theorem deref_closed (α : Life) (T : Ty) (δ : LSub) :
    (all fun w => shrDen α (.ref T) δ w ─⋆ wp (.app (.val derefV) (.val w)) (shrDen α T δ))
      PMap.empty := by
  intro w ρ₁ ρ₂ h hc
  obtain rfl : ρ₁ = ρ₂ := ResU.eq_of_comp_empty_left hc
  exact deref_sem α T δ w ρ₁ h

/-- **Load through a frozen `Mut`, at the outer lifetime.**  `shrV α (Mut β S)` at `t` is the
view `t ↦ imm({α}, u, χ)` over the `mut` target's value, with `χ ∈ 𝒱⟦S⟧δ(u)`: loading `t`
returns `u` at the outer `α` — Rust's `&'b &'a mut T → &'b T` with `'b ⊑ 'a`.  The view goes
to `ρ⁺` (`wp_frame_noOwn`); the result carries `S`'s denotation of the witness as a fact.
`[about ours]` -/
theorem wp_load_mutView (α : Life) (a : Lifetime.Life) (S : Ty) (δ : LSub) (w : Val) :
    Entails (shrV α (.mut a S) δ w)
      (wp (.app (.val (.prim .load)) (.val w)) (fun u => BoLo.pure (∃ σ, vDen S δ u σ))) := by
  rintro ρ ⟨ℓ, u, p₀, Q₀, hp₀, ⟨rfl, hw⟩, hH⟩
  obtain rfl : Q₀ = ρ := ResU.eq_of_comp_empty_left hp₀
  subst hw
  refine wp_load_I_conf ℓ α (viewPayload S δ u) (fun u' => BoLo.pure (∃ σ, vDen S δ u' σ))
    Q₀ ⟨Q₀, PMap.empty, ResU.comp_empty_right _, hH, ?_⟩
  rintro w' ρ₁ ρ₂ ⟨s, w'', σ, hs, rfl, ⟨rfl, hσ⟩, -⟩ hc
  refine wp_frame_noOwn (R := fun ρ => ρ = ResU.single ℓ (CellU.immOf s w'' σ hs))
    (fun ρ e => e ▸ noOwn_single_imm ℓ s w'' σ hs) _ _ ρ₂
    ⟨_, PMap.empty, ResU.CompS.comm hc, rfl, ?_⟩
  exact wp_val w' _ PMap.empty ⟨rfl, σ, hσ⟩

/-- `deref` at a frozen `Mut`: `λx. load x` through `shrV α (Mut β S)`. -/
theorem deref_mut_sem (α : Life) (a : Lifetime.Life) (S : Ty) (δ : LSub) (w : Val) :
    Entails (shrV α (.mut a S) δ w)
      (wp (.app (.val derefV) (.val w)) (fun u => BoLo.pure (∃ σ, vDen S δ u σ))) := by
  intro ρ hρ
  exact wp_lolli _ _ _ ρ (wp_load_mutView α a S δ w ρ hρ)

/-! ### Structure of `shrDen` -/

/-- The views are `imm` cells only. -/
theorem shrV_noOwn (α : Life) (δ : LSub) :
    ∀ (T : Ty) (v : Val) (ρ : WRes), shrV α T δ v ρ → NoOwn ρ := by
  intro T
  induction T with
  | unit => rintro v ρ ⟨rfl, -⟩; exact noOwn_empty
  | tensor T₁ T₂ ih₁ ih₂ =>
      rintro v ρ ⟨v₁, v₂, p₀, Q, hp₀, ⟨rfl, -⟩, ρ₁, ρ₂, hQ, h₁, h₂⟩
      obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
      exact noOwn_compS hQ (ih₁ v₁ ρ₁ h₁) (ih₂ v₂ ρ₂ h₂)
  | sum T₁ T₂ ih₁ ih₂ =>
      rintro v ρ (⟨v₁, p₀, ρ₁, hp₀, ⟨rfl, -⟩, h₁⟩ | ⟨v₂, p₀, ρ₂, hp₀, ⟨rfl, -⟩, h₂⟩)
      · obtain rfl : ρ₁ = ρ := ResU.eq_of_comp_empty_left hp₀; exact ih₁ v₁ ρ₁ h₁
      · obtain rfl : ρ₂ = ρ := ResU.eq_of_comp_empty_left hp₀; exact ih₂ v₂ ρ₂ h₂
  | lolli _ _ _ _ => rintro v ρ ⟨rfl, -⟩; exact noOwn_empty
  | ref S ih =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, ⟨rfl, -⟩, H, V, hHV, ⟨s, w, σ, hs, rfl, -, -⟩, hV⟩
      obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
      exact noOwn_compS hHV (noOwn_single_imm ℓ s w σ hs) (ih u V hV)
  | imm _ _ _ => rintro v ρ ⟨rfl, -⟩; exact noOwn_empty
  | «mut» _ S _ =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, ⟨rfl, -⟩, ⟨s, w, σ, hs, hQ, -, -⟩⟩
      obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
      rw [hQ]; exact noOwn_single_imm ℓ s w σ hs
  | box _ S ih => exact ih
  | bang _ _ => rintro v ρ ⟨rfl, -⟩; exact noOwn_empty
  | all _ _ _ _ => rintro v ρ ⟨rfl, -⟩; exact noOwn_empty
  | unk => rintro v ρ ⟨rfl, -⟩; exact noOwn_empty

/-- A shared borrow can be forgotten: `Shr α T(w) ⋆ wp(e){Q̂} ⊨ wp(e){Q̂}` (`[TR]` 6.149 at
every view). -/
theorem wp_S_forget (α : Life) (T : Ty) (δ : LSub) (w : Val) (e : Expr) (Q : Val → WProp) :
    Entails (shrDen α T δ w ⋆ wp e Q) (wp e Q) :=
  wp_frame_noOwn (fun ρ h => shrV_noOwn α δ (.ref T) w ρ h) e Q

/-- Shortening the lifetime: `Shr α T ⊨ Shr β T` for `β ⊑ α` (`⊑Imm`, `[TR]` 6.114 at every
view). -/
theorem shrV_mono {α β : Life} (hβ : β ⊑ α) (δ : LSub) :
    ∀ (T : Ty) (v : Val), Entails (shrV α T δ v) (shrV β T δ v) := by
  intro T
  induction T with
  | unit => intro v ρ h; exact h
  | tensor T₁ T₂ ih₁ ih₂ =>
      rintro v ρ ⟨v₁, v₂, p₀, Q, hp₀, hv, ρ₁, ρ₂, hQ, h₁, h₂⟩
      exact ⟨v₁, v₂, p₀, Q, hp₀, hv, ρ₁, ρ₂, hQ, ih₁ v₁ ρ₁ h₁, ih₂ v₂ ρ₂ h₂⟩
  | sum T₁ T₂ ih₁ ih₂ =>
      rintro v ρ (⟨v₁, p₀, ρ₁, hp₀, hv, h₁⟩ | ⟨v₂, p₀, ρ₂, hp₀, hv, h₂⟩)
      · exact Or.inl ⟨v₁, p₀, ρ₁, hp₀, hv, ih₁ v₁ ρ₁ h₁⟩
      · exact Or.inr ⟨v₂, p₀, ρ₂, hp₀, hv, ih₂ v₂ ρ₂ h₂⟩
  | lolli _ _ _ _ => intro v ρ h; exact h
  | ref S ih =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, hv, H, V, hHV, ⟨s, w, σ, hs, hH, hP, hle⟩, hV⟩
      exact ⟨ℓ, u, p₀, Q, hp₀, hv, H, V, hHV, ⟨s, w, σ, hs, hH, hP, le_trans hβ hle⟩,
        ih u V hV⟩
  | imm _ _ _ => intro v ρ h; exact h
  | «mut» _ S _ =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, hv, ⟨s, w, σ, hs, hH, hP, hle⟩⟩
      exact ⟨ℓ, u, p₀, Q, hp₀, hv, ⟨s, w, σ, hs, hH, hP, le_trans hβ hle⟩⟩
  | box _ S ih => exact ih
  | bang _ _ => intro v ρ h; exact h
  | all _ _ _ _ => intro v ρ h; exact h
  | unk => intro v ρ h; exact h

/-- **The head is `[TR]` p. 4's `Imm`.**  `Shr α T(w)` is `𝒱⟦Imm @a T⟧δ(w)` (at `@aδ = α`) and
an own-free rest, so every rule about `Imm` applies to a shared borrow once its views are
forgotten. -/
theorem shrDen_head {a : Lifetime.Life} {δ : LSub} {α : Life} (ha : a.interp δ = some α)
    (T : Ty) (w : Val) (ρ : WRes) (h : shrDen α T δ w ρ) :
    ∃ ρh ρv, ResU.CompS ρh ρv ρ ∧ vDen (.imm a T) δ w ρh ∧ NoOwn ρv := by
  obtain ⟨ℓ, u, p₀, Q, hp₀, ⟨rfl, hw⟩, H, V, hHV, ⟨s, u', σ, hs, rfl, ⟨hu, hσ⟩, hle⟩, hV⟩ := h
  obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
  exact ⟨_, V, hHV, ⟨α, ha, ℓ, PMap.empty, _, ResU.comp_empty_left _, ⟨rfl, hw⟩,
    s, u', σ, hs, rfl, hσ, hle⟩, shrV_noOwn α δ T u V hV⟩

end BoCa.MintProbe

end
