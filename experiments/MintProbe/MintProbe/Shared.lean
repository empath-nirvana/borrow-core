import MintProbe.Frame

/-!
# Views — a shared borrow that reaches through owned pointers

`shrDen α T δ` is a borrow of a `T` at `α` that carries, besides `[TR]` p. 4's cell
`ℓ ↦ Imm α 𝒱⟦T⟧δ`, a view at the same `α` of every location the value reaches through owned
pointers (`Ref`, through `⊗`, `⊕` and `[@a]`, and through a frozen `Mut` to its target and what
the target owns, `Reach`).  Each view is the cell 6.64 would make for that
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
componentwise; at `Mut β T` a view of the `mut` target at `α`, with the target's own views
(the frozen `Mut`, theory's derived-views §8: `Mut β T` is read at `α` as `Ref T`); nothing at
`1`'s value constraint aside, and nothing behind `⊸`, `∀`, `Imm` and `Unk`.  `[about ours]` -/
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
      ex fun ℓ => ex fun u => ⌜v = .loc ℓ⌝ ⋆ ptoImm ℓ α (viewPayload T δ u) ⋆ shrV α T δ u
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

/-! ### Reach: where a mint may put a view -/

/-- `Reach O P`: `P` is a part of `O`'s ownership a mint over `O` may put views on.  Every cell of
`ex(P)` is a cell of `ex(O)`, and `⦇P⦈_○` is a `○`-factor of `⦇O⦈`.  A `●`-factor of `O` reaches
(`Reach.of_le`), and so does the witness of a `mut` cell of anything that reaches
(`Reach.mutWit`): the target of a frozen `Mut` and everything it owns. -/
structure Reach (O P : WRes) : Prop where
  ex : ∀ eP, ExS P eP → ∀ eO, ExS O eO → ∀ m c, eP.get m = some c → eO.get m = some c
  exDef : ∃ eP, ExS P eP
  flat : ∃ fP, ResU.FlatR P fP ∧ ∀ σ, ResU.Flat O σ → ∃ z, ResU.CompR fP z σ

/-- `⦇Q⦈_○` is a `○`-factor of `⦇P⦈_○` when `Q ● r = P`. -/
theorem flatR_factor_of_le {Q r P fP : WRes} (hr : ResU.CompS Q r P) (hf : ResU.FlatR P fP) :
    ∃ fQ z, ResU.FlatR Q fQ ∧ ResU.CompR fQ z fP := by
  obtain ⟨a, e, ha, he, hae⟩ := hf
  obtain ⟨aQ, ar, haQ, -, hac⟩ := (AgW.split hr).mp ha
  obtain ⟨eQ, er, heQ, -, hec⟩ := (ExR.split_of_compS hr).mp he
  obtain ⟨S₁, S₂, h₁, -, h₃⟩ := (ResU.CompR.exchange₄ aQ ar eQ er fP).mp
    ⟨a, e, hac, hec, hae⟩
  exact ⟨S₁, S₂, ⟨aQ, eQ, haQ, heQ, h₁⟩, h₃⟩

/-- The exclusive walks of two `●`-factors: each one's cells are cells of the composite's walk,
at locations the other's walk does not hold. -/
theorem ex_split_cells {P₁ P₂ P eP : WRes} (h : ResU.CompS P₁ P₂ P) (heP : ExS P eP) :
    ∃ e₁ e₂, ExS P₁ e₁ ∧ ExS P₂ e₂ ∧
      (∀ m c, e₁.get m = some c → eP.get m = some c ∧ e₂.get m = none) ∧
      (∀ m c, e₂.get m = some c → eP.get m = some c ∧ e₁.get m = none) := by
  obtain ⟨e₁, e₂, h₁, h₂, hc⟩ := (ExS.split h).mp heP
  refine ⟨e₁, e₂, h₁, h₂, fun m c e => ?_, fun m c e => ?_⟩
  · have r := ResU.CompS.get_left_of_ne_imm hc e (ExS.immFree h₁ m c e)
    exact ⟨r.2, r.1⟩
  · have r := ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc) e (ExS.immFree h₂ m c e)
    exact ⟨r.2, r.1⟩

/-- The exclusive walk of a `mut` cell's witness: its cells are cells of the walk around it. -/
theorem ex_mutWit_cells {P eP : WRes} (heP : ExS P eP) {t : Loc} {ψ : CellU Loc Val}
    (e : P.get t = some ψ) (hk : ψ.kind = Kind.mut) :
    ∃ ev, ExS ψ.wit ev ∧ ∀ m c, ev.get m = some c → eP.get m = some c := by
  have hS : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ :=
    fun _ _ _ hc => CellU.CompS.compat hc
  obtain ⟨ev, z, hev, hz⟩ := ExW.wit_le hS ResU.compLawsS heP e hk
  exact ⟨ev, hev, fun m c ec =>
    (ResU.CompS.get_left_of_ne_imm hz ec (ExS.immFree hev m c ec)).2⟩

namespace Reach

/-- A valid resource reaches itself. -/
theorem self {O : WRes} (hvO : ResU.Valid O) : Reach O O := by
  obtain ⟨σ₀, eO₀, aO₀, heO₀, haO₀, hcO₀⟩ := hvO
  refine ⟨fun eP heP eO heO m c e => by rw [← ExS.functional heP heO]; exact e,
    ⟨eO₀, heO₀⟩, σ₀, ResU.six33 ⟨eO₀, aO₀, heO₀, haO₀, hcO₀⟩, fun σ hσ => ?_⟩
  rw [ResU.Flat.functional hσ ⟨eO₀, aO₀, heO₀, haO₀, hcO₀⟩]
  exact ⟨PMap.empty, ResU.comp_empty_right σ₀⟩

/-- A `●`-factor of what reaches, reaches. -/
theorem le {O P Q : WRes} (h : Reach O P) (hQP : ResU.Le Q P) : Reach O Q := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨r, hr⟩ := hQP
  obtain ⟨eP₀, heP₀⟩ := h.exDef
  obtain ⟨eQ₀, -, heQ₀, -, hc₀, -⟩ := ex_split_cells hr heP₀
  refine ⟨fun eQ heQ eO heO m c e => ?_, ⟨eQ₀, heQ₀⟩, ?_⟩
  · rw [ExS.functional heQ heQ₀] at e
    exact h.ex eP₀ heP₀ eO heO m c (hc₀ m c e).1
  · obtain ⟨fP, hfP, hfac⟩ := h.flat
    obtain ⟨fQ, z, hfQ, hz⟩ := flatR_factor_of_le hr hfP
    refine ⟨fQ, hfQ, fun σ hσ => ?_⟩
    obtain ⟨z', hz'⟩ := hfac σ hσ
    exact ResU.Comp.factor_trans hR ResU.compLawsR hz hz'

/-- A `●`-factor of a valid resource reaches. -/
theorem of_le {O P : WRes} (hvO : ResU.Valid O) (h : ResU.Le P O) : Reach O P :=
  (self hvO).le h

/-- **The deeper reach.**  The witness of a `mut` cell of what reaches, reaches: `ex(χ)` is a
`●`-factor of the walk around the cell (`ExW.wit_le`), and `⦇χ⦈_○ = ag(χ) ○ ex(χ)_○` a
`○`-factor of its flattening (`AgW.mut_wit_le`, `ExW.wit_le`, `exchange₄`). -/
theorem mutWit {O P : WRes} (h : Reach O P) {t : Loc} {ψ : CellU Loc Val}
    (e : P.get t = some ψ) (hk : ψ.kind = Kind.mut) : Reach O ψ.wit := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  obtain ⟨eP₀, heP₀⟩ := h.exDef
  obtain ⟨ev₀, hev₀, hcells⟩ := ex_mutWit_cells heP₀ e hk
  refine ⟨fun eχ heχ eO heO m c ec => ?_, ⟨ev₀, hev₀⟩, ?_⟩
  · rw [ExS.functional heχ hev₀] at ec
    exact h.ex eP₀ heP₀ eO heO m c (hcells m c ec)
  · obtain ⟨fP, ⟨aP, eP, haP, heP, hae⟩, hfac⟩ := h.flat
    obtain ⟨ev, z₁, hev, hz₁⟩ := ExW.wit_le hR ResU.compLawsR heP e hk
    obtain ⟨av, z₂, hav, hz₂⟩ := AgW.mut_wit_le haP e hk
    obtain ⟨S₁, S₂, h₁, -, h₃⟩ := (ResU.CompR.exchange₄ av z₂ ev z₁ fP).mp
      ⟨aP, eP, hz₂, hz₁, hae⟩
    refine ⟨S₁, ⟨av, ev, hav, hev, h₁⟩, fun σ hσ => ?_⟩
    obtain ⟨z, hz⟩ := hfac σ hσ
    exact ResU.Comp.factor_trans hR ResU.compLawsR h₃ hz

end Reach

/-- **The views mint.**  For `v : T` owned as `P` in `Res_α`, where `P` reaches into `O`
(`Reach O P`), a mint `Y₀` over `O` that holds none of `ex(P)`'s locations extends by
`shrV α T δ v`'s views to a mint over `O`; the views sit on `ex(P)`'s cells.  By induction on
`T`: at `Ref` by `Mint.add` (the pointee's witness reaches, `Reach.le`), at `Mut` by
`Mint.addMut` and then the target's own views (`α ⊑ β` from `P ∈ Res_α`; the target's witness
reaches, `Reach.mutWit`). -/
theorem mint_views {α : Life} {O : WRes} (hvO : ResU.Valid O) (δ : LSub) :
    ∀ (T : Ty) (v : Val) (P Y₀ : WRes), vDen T δ v P → Reach O P → P.InStratum α →
      Mint α O Y₀ →
      (∀ eP, ExS P eP → ∀ m c, eP.get m = some c → Y₀.get m = none) →
      ∃ V Y, ResU.CompS Y₀ V Y ∧ Mint α O Y ∧ shrV α T δ v V ∧
        (∀ eP, ExS P eP → ∀ m ψ, V.get m = some ψ → ∃ c, eP.get m = some c) := by
  intro T
  induction T with
  | unit =>
      intro v P Y₀ hP _ _ hM _
      obtain ⟨rfl, hv⟩ := hP
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, hv⟩,
        fun _ _ m ψ e => by simp at e⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨v₁, v₂, p₀, Q, hp₀Q, ⟨rfl, hv⟩, P₁, P₂, hQ, hP₁, hP₂⟩ := hP
      obtain rfl : Q = P := ResU.eq_of_comp_empty_left hp₀Q
      obtain ⟨eP, heP⟩ := hPO.exDef
      obtain ⟨e₁, e₂, he₁, he₂, hc₁, hc₂⟩ := ex_split_cells hQ heP
      obtain ⟨V₁, Y₁, hY₁, hM₁, hV₁, hdom₁⟩ :=
        ih₁ v₁ P₁ Y₀ hP₁ (hPO.le (le_of_compS_left hQ)) (ResU.CompS.inStratum_left hQ hPα) hM
          (fun e₁' he₁' m c e => by
            rw [ExS.functional he₁' he₁] at e
            exact hY₀ eP heP m c (hc₁ m c e).1)
      have hY₁' : ∀ e₂', ExS P₂ e₂' → ∀ m c, e₂'.get m = some c → Y₁.get m = none := by
        intro e₂' he₂' m c e
        rw [ExS.functional he₂' he₂] at e
        refine (ResU.Comp.eq_none_iff hY₁ m).mpr ⟨hY₀ eP heP m c (hc₂ m c e).1, ?_⟩
        cases eV : V₁.get m with
        | none => rfl
        | some ψ =>
            obtain ⟨c₁, f₁⟩ := hdom₁ e₁ he₁ m ψ eV
            rw [(hc₂ m c e).2] at f₁; cases f₁
      obtain ⟨V₂, Y₂, hY₂, hM₂, hV₂, hdom₂⟩ :=
        ih₂ v₂ P₂ Y₁ hP₂ (hPO.le (le_of_compS_right hQ)) (ResU.CompS.inStratum_right hQ hPα)
          hM₁ hY₁'
      have hV₁₂ : ResU.CompatS V₁ V₂ := ResU.Compat.of_disjoint (fun m => by
        cases g₁ : V₁.get m with
        | none => exact Or.inl rfl
        | some ψ =>
            refine Or.inr ?_
            cases g₂ : V₂.get m with
            | none => rfl
            | some χ =>
                obtain ⟨c₁, f₁⟩ := hdom₁ e₁ he₁ m ψ g₁
                obtain ⟨c₂, f₂⟩ := hdom₂ e₂ he₂ m χ g₂
                rw [(hc₁ m c₁ f₁).2] at f₂; cases f₂)
      obtain ⟨V, hV⟩ := (ResU.compS_defined_iff V₁ V₂).mpr hV₁₂
      obtain ⟨Y', hY', hY'Y⟩ := (ResU.CompS.assoc Y₀ V₁ V₂ Y₂).mpr ⟨Y₁, hY₁, hY₂⟩
      rw [ResU.CompS.functional hY' hV] at hY'Y
      refine ⟨V, Y₂, hY'Y, hM₂, ⟨v₁, v₂, PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, hv⟩,
        V₁, V₂, hV, hV₁, hV₂⟩, fun eP' heP' m ψ e => ?_⟩
      rw [ExS.functional heP' heP]
      rcases ResU.Comp.get hV m with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
      · rw [f] at e; cases e
      · obtain ⟨c, hc⟩ := hdom₁ e₁ he₁ m χ f₁; exact ⟨c, (hc₁ m c hc).1⟩
      · obtain ⟨c, hc⟩ := hdom₂ e₂ he₂ m χ f₂; exact ⟨c, (hc₂ m c hc).1⟩
      · obtain ⟨c, hc⟩ := hdom₁ e₁ he₁ m χ₁ f₁; exact ⟨c, (hc₁ m c hc).1⟩
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
        fun _ _ m ψ e => by simp at e⟩
  | ref S ih =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨ℓ, v', p₀, Q, hp₀Q, ⟨rfl, hv⟩, L, P₁, hQ, rfl, hP₁⟩ := hP
      obtain rfl : Q = P := ResU.eq_of_comp_empty_left hp₀Q
      have hLself : (ResU.single ℓ (CellU.ownOf v')).get ℓ = some (CellU.ownOf v') :=
        ResU.single_get_self _ _
      have hPℓ : Q.get ℓ = some (CellU.ownOf v') :=
        (ResU.CompS.get_left_of_ne_imm hQ hLself (by simp)).2
      have hP₁Q : ResU.Le P₁ Q := le_of_compS_right hQ
      have hP₁α : P₁.InStratum α := ResU.CompS.inStratum_right hQ hPα
      obtain ⟨eP, heP⟩ := hPO.exDef
      obtain ⟨eL, e₁, heL, he₁, -, hc₁⟩ := ex_split_cells hQ heP
      have heLℓ : eL.get ℓ = some (CellU.ownOf v') := ExS.get_of_ne_imm heL hLself (by simp)
      have hePℓ : eP.get ℓ = some (CellU.ownOf v') := ExS.get_of_ne_imm heP hPℓ (by simp)
      have he₁ℓ : e₁.get ℓ = none := by
        cases g : e₁.get ℓ with
        | none => rfl
        | some c => rw [(hc₁ ℓ c g).2] at heLℓ; cases heLℓ
      obtain ⟨σw, hfw, hfac⟩ := (hPO.le hP₁Q).flat
      obtain ⟨Y₁, hY₁, hM₁⟩ := Mint.add (w := P₁) (h := hP₁α) hM hvO
        (fun eO heO => hPO.ex eP heP eO heO ℓ _ hePℓ) (hY₀ eP heP ℓ _ hePℓ) hfw hfac
      have hY₁' : ∀ e₁', ExS P₁ e₁' → ∀ m c, e₁'.get m = some c → Y₁.get m = none := by
        intro e₁' he₁' m c e
        rw [ExS.functional he₁' he₁] at e
        refine (ResU.Comp.eq_none_iff hY₁ m).mpr ⟨hY₀ eP heP m c (hc₁ m c e).1, ?_⟩
        have hm : m ≠ ℓ := by rintro rfl; rw [he₁ℓ] at e; cases e
        exact ResU.single_get_ne _ hm
      obtain ⟨V₁, Y₂, hY₂, hM₂, hV₁, hdom₁⟩ :=
        ih v' P₁ Y₁ hP₁ (hPO.le hP₁Q) hP₁α hM₁ hY₁'
      set c := ResU.single ℓ (CellU.immOf (LSet.singleton α) v' P₁ hP₁α) with hcdef
      have hcV : ResU.CompatS c V₁ := ResU.Compat.of_disjoint (fun m => by
        by_cases hm : m = ℓ
        · subst hm
          refine Or.inr ?_
          cases g : V₁.get m with
          | none => rfl
          | some ψ => obtain ⟨c', hc'⟩ := hdom₁ e₁ he₁ m ψ g; rw [he₁ℓ] at hc'; cases hc'
        · exact Or.inl (ResU.single_get_ne _ hm))
      obtain ⟨V, hV⟩ := (ResU.compS_defined_iff c V₁).mpr hcV
      obtain ⟨Y', hY', hY'Y⟩ := (ResU.CompS.assoc Y₀ c V₁ Y₂).mpr ⟨Y₁, hY₁, hY₂⟩
      rw [ResU.CompS.functional hY' hV] at hY'Y
      refine ⟨V, Y₂, hY'Y, hM₂, ⟨ℓ, v', PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, hv⟩,
        c, V₁, hV, ⟨LSet.singleton α, v', P₁, hP₁α, rfl, ⟨rfl, hP₁⟩, le_refl α⟩, hV₁⟩,
        fun eP' heP' m ψ e => ?_⟩
      rw [ExS.functional heP' heP]
      rcases ResU.Comp.get hV m with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
      · rw [f] at e; cases e
      · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some f₁; exact ⟨_, hePℓ⟩
      · obtain ⟨c', hc'⟩ := hdom₁ e₁ he₁ m χ f₂; exact ⟨c', (hc₁ m c' hc').1⟩
      · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some f₁; exact ⟨_, hePℓ⟩
  | imm a S _ =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun _ _ m ψ e => by simp at e⟩
  | «mut» a S ih =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨α', -, ℓ, p₀, Q, hp₀Q, ⟨rfl, hv⟩, b, u, χ, hχ, Qp, hw, -, hQe, hQp⟩ := hP
      obtain rfl : Q = P := ResU.eq_of_comp_empty_left hp₀Q
      subst hQe
      have hPℓ : (ResU.single ℓ (CellU.mutOf b u χ hχ Qp hw)).get ℓ =
          some (CellU.mutOf b u χ hχ Qp hw) := ResU.single_get_self _ _
      have hkm : (CellU.mutOf b u χ hχ Qp hw).kind ≠ Kind.imm := by simp
      have hαb : α < b := hPα ℓ _ hPℓ
      have hχα : χ.InStratum α := ResU.InStratum.mono (le_of_lt hαb) hχ
      obtain ⟨eP, heP⟩ := hPO.exDef
      have hePℓ : eP.get ℓ = some (CellU.mutOf b u χ hχ Qp hw) := ExS.get_of_ne_imm heP hPℓ hkm
      -- the target's witness reaches
      have hχR : Reach O χ := by
        have h' := hPO.mutWit hPℓ (by simp)
        rwa [CellU.wit_mutOf] at h'
      obtain ⟨σw, hfw, hfac⟩ := hχR.flat
      obtain ⟨Y₁, hY₁, hM₁⟩ := Mint.addMut (h := hχα) hM hvO
        (fun eO heO => hPO.ex eP heP eO heO ℓ _ hePℓ) (hY₀ eP heP ℓ _ hePℓ) hfw hfac
      -- `ex(χ)`: cells of `ex(P)`, none at `ℓ` (`χ ∈ Res_b` and `ℓ`'s cell is not)
      obtain ⟨eχ, heχ, hcχ⟩ := ex_mutWit_cells heP hPℓ (by simp)
      rw [CellU.wit_mutOf] at heχ
      have heχℓ : eχ.get ℓ = none := by
        cases g : eχ.get ℓ with
        | none => rfl
        | some c =>
            have hst := BoCa.Fig16.BoLo.ExW.inStratum BoCa.Fig16.BoLo.compS_hC heχ b hχ ℓ c g
            have hc : c = CellU.mutOf b u χ hχ Qp hw := by
              have := hcχ ℓ c g; rw [hePℓ] at this; exact (Option.some.inj this).symm
            rw [hc] at hst
            exact absurd hst (lt_irrefl b)
      have hY₁' : ∀ eχ', ExS χ eχ' → ∀ m c, eχ'.get m = some c → Y₁.get m = none := by
        intro eχ' heχ' m c e
        rw [ExS.functional heχ' heχ] at e
        refine (ResU.Comp.eq_none_iff hY₁ m).mpr ⟨hY₀ eP heP m c (hcχ m c e), ?_⟩
        have hm : m ≠ ℓ := by rintro rfl; rw [heχℓ] at e; cases e
        exact ResU.single_get_ne _ hm
      have hd : vDen S δ u χ := by rw [← hQp]; exact ⟨hχ, hw⟩
      obtain ⟨V₁, Y₂, hY₂, hM₂, hV₁, hdom₁⟩ := ih u χ Y₁ hd hχR hχα hM₁ hY₁'
      set c := ResU.single ℓ (CellU.immOf (LSet.singleton α) u χ hχα) with hcdef
      have hcV : ResU.CompatS c V₁ := ResU.Compat.of_disjoint (fun m => by
        by_cases hm : m = ℓ
        · subst hm
          refine Or.inr ?_
          cases g : V₁.get m with
          | none => rfl
          | some ψ => obtain ⟨c', hc'⟩ := hdom₁ eχ heχ m ψ g; rw [heχℓ] at hc'; cases hc'
        · exact Or.inl (ResU.single_get_ne _ hm))
      obtain ⟨V, hV⟩ := (ResU.compS_defined_iff c V₁).mpr hcV
      obtain ⟨Y', hY', hY'Y⟩ := (ResU.CompS.assoc Y₀ c V₁ Y₂).mpr ⟨Y₁, hY₁, hY₂⟩
      rw [ResU.CompS.functional hY' hV] at hY'Y
      refine ⟨V, Y₂, hY'Y, hM₂, ⟨ℓ, u, PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, hv⟩,
        c, V₁, hV, ⟨LSet.singleton α, u, χ, hχα, rfl, ⟨rfl, hd⟩, le_refl α⟩, hV₁⟩,
        fun eP' heP' m ψ e => ?_⟩
      rw [ExS.functional heP' heP]
      rcases ResU.Comp.get hV m with ⟨-, -, f⟩ | ⟨χ', f₁, -, f⟩ | ⟨χ', -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ', f₁, -, -, -⟩
      · rw [f] at e; cases e
      · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some f₁; exact ⟨_, hePℓ⟩
      · obtain ⟨c', hc'⟩ := hdom₁ eχ heχ m χ' f₂; exact ⟨c', hcχ m c' hc'⟩
      · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some f₁; exact ⟨_, hePℓ⟩
  | box a S ih =>
      intro v P Y₀ hP hPO hPα hM hY₀
      obtain ⟨β, -, hPS, -⟩ := hP
      exact ih v P Y₀ hPS hPO hPα hM hY₀
  | bang S _ =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun _ _ m ψ e => by simp at e⟩
  | all x b S _ =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun _ _ m ψ e => by simp at e⟩
  | unk =>
      intro v P Y₀ _ _ _ hM _
      exact ⟨PMap.empty, Y₀, ResU.comp_empty_right Y₀, hM, ⟨rfl, trivial⟩,
        fun _ _ m ψ e => by simp at e⟩

/-- **An owned value shares at `α`**, at a named decomposition `ρₒ = ℓ ↦ own(v) ● ρ_P`: the
minted resource is 6.64's cell `ℓ ↦ imm({α}, v, ρ_P)` and own-free views `V` on cells of
`ex(ρ_P)`. -/
theorem mint_shr_of {α : Life} {l : Loc} {v : Val} {T : Ty} {δ : LSub} {ρP ρo : WRes}
    (hc : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρo) (hρP : vDen T δ v ρP)
    (hPα : ρP.InStratum (LSet.singleton α).join) (hvo : ResU.Valid ρo) :
    ∃ V Y, ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v ρP hPα)) V Y ∧
      Mint α ρo Y ∧ shrDen α T δ (Val.loc l) Y ∧ shrV α T δ v V ∧
      (∀ eP, ExS ρP eP → ∀ m ψ, V.get m = some ψ → ∃ c, eP.get m = some c) := by
  have hLself : (ResU.single l (CellU.ownOf v)).get l = some (CellU.ownOf v) :=
    ResU.single_get_self _ _
  have hM₀ : Mint α ρo (ResU.single l (CellU.immOf (LSet.singleton α) v ρP hPα)) :=
    mint_single (ResU.CompS.comm hc) hvo
  -- `ex(ρₒ) = ℓ ↦ own(v) ● ex(ρ_P)`: `ex(ρ_P)` holds nothing at `ℓ`
  obtain ⟨σo, eo, ao, heo, -, -⟩ := id hvo
  obtain ⟨eL, eP, heL, heP, -, hcP⟩ := ex_split_cells hc heo
  have heLl : eL.get l = some (CellU.ownOf v) := ExS.get_of_ne_imm heL hLself (by simp)
  obtain ⟨V, Y, hY, hM, hV, hdom⟩ := mint_views hvo δ T v ρP _ hρP
    (Reach.of_le hvo (le_of_compS_right hc)) hPα hM₀ (fun eP' heP' m c e => by
      rw [ExS.functional heP' heP] at e
      have hm : m ≠ l := by rintro rfl; rw [(hcP m c e).2] at heLl; cases heLl
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

/-- `deref` through a shared borrow: `λx. load x` takes `shrDen α T δ` to the stored value with
its views at the same `α`. -/
theorem deref_shr (α : Life) (T : Ty) (δ : LSub) (w : Val) :
    Entails (shrDen α T δ w) (wp (.app (.val derefV) (.val w)) (shrV α T δ)) := by
  intro ρ hρ
  obtain ⟨ℓ, -, -, -, -, ⟨-, hw⟩, -⟩ := id hρ
  subst hw
  exact wp_lolli _ _ _ ρ (wp_load_S α T δ ℓ ρ hρ)

/-- **The projection** `Imm 'a (Ref T) → Imm 'a T`, at `shrDen`: `deref` takes a shared borrow
of a `Ref T` at `α` to a shared borrow of the pointee at the same `α`. -/
theorem deref_sem (α : Life) (T : Ty) (δ : LSub) (w : Val) :
    Entails (shrDen α (.ref T) δ w) (wp (.app (.val derefV) (.val w)) (shrDen α T δ)) :=
  deref_shr α (.ref T) δ w

/-- **`deref` is a closed term of type `Shr α (Ref T) ⊸ Shr α T`**: at the empty resource,
`∀w. Shr α (Ref T)(w) ─⋆ ℰ⟦Shr α T⟧(deref w)` — `𝒱⟦−⊸−⟧`'s clause (`[TR]` p. 4) with
`shrDen` at both ends. -/
theorem deref_closed (α : Life) (T : Ty) (δ : LSub) :
    (all fun w => shrDen α (.ref T) δ w ─⋆ wp (.app (.val derefV) (.val w)) (shrDen α T δ))
      PMap.empty := by
  intro w ρ₁ ρ₂ h hc
  obtain rfl : ρ₁ = ρ₂ := ResU.eq_of_comp_empty_left hc
  exact deref_sem α T δ w ρ₁ h

/-- At `α`, a frozen `Mut β S` is a shared `Ref S`: the view of the target with its views. -/
theorem shrV_mut_eq (α : Life) (a : Lifetime.Life) (S : Ty) (δ : LSub) (w : Val) :
    shrV α (.mut a S) δ w = shrDen α S δ w := rfl

/-- **Load through a frozen `Mut`, at the outer lifetime.**  `shrV α (Mut β S)` at `t` is the
view `t ↦ imm({α}, u, χ)` over the `mut` target's value, with `χ ∈ 𝒱⟦S⟧δ(u)`, and `u`'s views:
loading `t` returns `u` with its views at the outer `α` — Rust's `&'b &'a mut T → &'b T` with
`'b ⊑ 'a`, and what `T` owns is shared at `'b` too.  `wp_load_S` at `S`.  `[about ours]` -/
theorem wp_load_mutView (α : Life) (a : Lifetime.Life) (S : Ty) (δ : LSub) (ℓ : Loc) :
    Entails (shrV α (.mut a S) δ (Val.loc ℓ))
      (wp (.app (.val (.prim .load)) (.val (.loc ℓ))) (shrV α S δ)) := by
  rw [shrV_mut_eq]; exact wp_load_S α S δ ℓ

/-- `deref` at a frozen `Mut`: `λx. load x` takes `shrV α (Mut β S)` to `shrV α S`, at the same
`α`. -/
theorem deref_mut_sem (α : Life) (a : Lifetime.Life) (S : Ty) (δ : LSub) (w : Val) :
    Entails (shrV α (.mut a S) δ w) (wp (.app (.val derefV) (.val w)) (shrV α S δ)) := by
  intro ρ hρ
  rw [shrV_mut_eq] at hρ
  exact deref_shr α S δ w ρ hρ

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
  | «mut» _ S ih =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, ⟨rfl, -⟩, H, V, hHV, ⟨s, w, σ, hs, rfl, -, -⟩, hV⟩
      obtain rfl : Q = ρ := ResU.eq_of_comp_empty_left hp₀
      exact noOwn_compS hHV (noOwn_single_imm ℓ s w σ hs) (ih u V hV)
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
  | «mut» _ S ih =>
      rintro v ρ ⟨ℓ, u, p₀, Q, hp₀, hv, H, V, hHV, ⟨s, w, σ, hs, hH, hP, hle⟩, hV⟩
      exact ⟨ℓ, u, p₀, Q, hp₀, hv, H, V, hHV, ⟨s, w, σ, hs, hH, hP, le_trans hβ hle⟩,
        ih u V hV⟩
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
