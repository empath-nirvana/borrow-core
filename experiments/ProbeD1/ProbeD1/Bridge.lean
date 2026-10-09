import ProbeD1.Order

/-!
# ProbeD1 — the piece at the reflexive future, and the nil slice the programs read

Two of statement 0's shared lemmas (DESIGN §4.1).

* **`openSFBridge`** (`OpenSFBridge`): the share over futures gives GhostEnd's piece at the stack
  itself. `OpenSF true` is a least fixed point over a stack-indexed continuation; instantiated at
  `X σ' := OpenS δ σ' Tab (Q σ')` its closure is `openS_fold` once each futures quantifier is read
  at the reflexive future. That reading is `relendableNF_refl`: `RelendableNF true` at the kept
  part `σ.drop k`, at its own reflexive future, is `RelendableN` at the same stack, the side
  condition on inserted entries being vacuous there. At a stop the continuation is then read at
  `σ.take k ++ σ.drop k = σ` (`List.take_append_drop`).
* **`nilSoundRet`** (`NilSoundRet`): at `σ = []` and a data answer, W's computation is Core's.
  A data type is read componentwise to its leaves, and every leaf is Core's `vC` at
  `extS δ [] [] = δ` (`vRL_data`). At `F A` the two relations are then one `wpTS`. At `F_Σ A` the
  piece at `[]` is first brought to GhostEnd's `OpenS` (at `cbpv` and `binder` through
  `bodySF_bodyS`, the bridge above), and GhostEnd's `bodyS_nil_iff` gives Core's `ewpTS`; the
  operation table is the same `opTable` at both relations (`rowTab` is `cC`'s table).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack extS vwS dropS stratS boxTop ReLend RelendableN ghostS tabK stopS
  bodyS openFS OpenS rowTab XT)

/-! ### The futures quantifiers at the reflexive future -/

/-- **`RelendableNF` at the reflexive future is `RelendableN`**: the futures quantifier taken at
the kept stack itself, where no entry is inserted. -/
theorem relendableNF_refl {fut : Bool} {δ : LSub} {inner σ : LStack}
    {P : LStack → List Life → WProp} {αs : List Life} {ls : List SRec} {ρ : WRes}
    (h : RelendableNF fut δ inner σ P αs ls ρ) :
    RelendableN δ (inner.map LEnt.l) σ (P σ) αs ls ρ := by
  obtain ⟨ds, ρz, ρn, hc, hn, hz, hth⟩ := h
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun αs' hr => hth αs' hr σ αs' ?_ ?_⟩
  · unfold FutQ; split
    · exact Relation.ReflTransGen.refl
    · rfl
  · intro e he hx
    exact absurd (List.mem_map_of_mem he) hx

/-- A stop with the share over futures is GhostEnd's stop at the stack itself, the continuation
read at the stack. -/
theorem stopSF_stopS {fut : Bool} {δ : LSub} {σ : LStack} {Tab : OpTab} {X : XTF} {Y : XT}
    (hXY : ∀ k ds αi αo ls e ρ, X σ k ds αi αo ls e ρ → Y k ds αi αo ls e ρ)
    {αs : List Life} {ls : List SRec} {t : Expr} :
    Entails (stopSF fut δ σ Tab X αs ls t) (stopS δ σ Tab Y αs ls t) := by
  rintro ρ ⟨k, ds, ρ₁, ρ₂, hc, hd, hg⟩
  refine ⟨k, ds, ρ₁, ρ₂, hc, hd, GhostEnd.ghostS_mono (fun τ h => ?_) _ _ _ ρ₂ hg⟩
  refine opTable_mono _ _ _ _ _ _ (fun ls' e' ρ' h' => ?_) h
  refine GhostEnd.relendableN_mono (fun αo ρ'' h'' => ?_) ρ' (relendableNF_refl h')
  have := hXY k ds (αs.take k) αo ls' e' ρ''
  rw [List.take_append_drop] at h''
  exact this h''

/-- One run with the share over futures is GhostEnd's run at the stack itself. -/
theorem bodySF_bodyS {fut : Bool} {δ : LSub} {Tab : OpTab}
    {Q : LStack → List Life → List SRec → Val → WProp} {X : XTF} {Y : XT} {σ : LStack}
    (hXY : ∀ k ds αi αo ls e ρ, X σ k ds αi αo ls e ρ → Y k ds αi αo ls e ρ)
    {αs : List Life} {ls : List SRec} {e : Expr} :
    Entails (bodySF fut δ Tab Q X σ αs ls e) (bodyS δ σ Tab (Q σ) Y αs ls e) :=
  fun _ h => wpG_mono (fun _ _ _ hq => hq.imp id (stopSF_stopS hXY _)) h

/-- One unfolding with the share over futures is GhostEnd's unfolding at the stack itself. -/
theorem openFSF_openFS {fut : Bool} {δ : LSub} {Tab : OpTab}
    {Q : LStack → List Life → List SRec → Val → WProp} {X : XTF} {Y : XT} {σ : LStack}
    (hXY : ∀ k ds αi αo ls e ρ, X σ k ds αi αo ls e ρ → Y k ds αi αo ls e ρ)
    {k : Nat} {ds : List Bool} {αi αo : List Life} {ls : List SRec} {e : Expr} :
    Entails (openFSF fut δ Tab Q X σ k ds αi αo ls e) (openFS δ σ Tab (Q σ) Y k ds αi αo ls e) :=
  fun _ h αi' h₁ h₂ =>
    GhostEnd.boxTop_mono (GhostEnd.wand_mono_right (bodySF_bodyS hXY)) _ (h αi' h₁ h₂)

/-- **`OpenSFBridge`**: the least fixed point with the share over futures gives GhostEnd's at the
stack itself, by its induction at `X σ' := OpenS δ σ' Tab (Q σ')`. -/
theorem openSF_openS {fut : Bool} {δ : LSub} {Tab : OpTab}
    {Q : LStack → List Life → List SRec → Val → WProp} {σ : LStack} {k : Nat} {ds : List Bool}
    {αi αo : List Life} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : OpenSF fut δ Tab Q σ k ds αi αo ls e ρ) : OpenS δ σ Tab (Q σ) k ds αi αo ls e ρ := by
  let X : XTF := fun σ' k ds αi αo ls e ρ => OpenS δ σ' Tab (Q σ') k ds αi αo ls e ρ
  refine h X ?_
  intro σ' k' ds' αi' αo' ls' e' ρ' h'
  exact GhostEnd.openS_fold
    (openFSF_openFS (X := X) (Y := OpenS δ σ' Tab (Q σ')) (fun _ _ _ _ _ _ _ h'' => h'') ρ' h')

/-- **Statement 0's shared lemma `OpenSFBridge`.** -/
theorem openSFBridge : OpenSFBridge (ℍ := ℍ) := fun _ _ _ _ _ _ _ _ _ _ _ h => openSF_openS h

/-! ### The nil slice at a data answer -/

/-- **At a data type W's value relation is the kernel's leaf reading**, at every stack: a data
type is read componentwise, and each leaf is `vC` at `extS δ σ αs`. -/
theorem vRL_data (p : Placement) (σ : LStack) (δ : LSub) (αs : List Life) :
    ∀ {k : Nat} {A : VTy}, VTy.DataB k A → ∀ (ls : List SRec) (v : Val),
      vRL p σ δ A αs ls v = vC true A ls (extS δ σ αs) v
  | _, _, .unit _, _, _ => rfl
  | _, _, .zero _, _, _ => rfl
  | _, _, .int _ _, _, _ => rfl
  | _, _, .tvar _, _, _ => rfl
  | _, _, .mu _, _, _ => rfl
  | _, _, .tensor hA hB, ls, v => by
      have eA := vRL_data p σ δ αs hA ls
      have eB := vRL_data p σ δ αs hB ls
      show (ex fun v₁ => ex fun v₂ => ⌜v = .pair v₁ v₂⌝ ⋆ vRL p σ δ _ αs ls v₁ ⋆
        vRL p σ δ _ αs ls v₂) = _
      simp only [eA, eB]; rfl
  | _, _, .sum hA hB, ls, v => by
      have eA := vRL_data p σ δ αs hA ls
      have eB := vRL_data p σ δ αs hB ls
      show BoLo.or (ex fun v₁ => ⌜v = .inj₁ v₁⌝ ⋆ vRL p σ δ _ αs ls v₁)
        (ex fun v₂ => ⌜v = .inj₂ v₂⌝ ⋆ vRL p σ δ _ αs ls v₂) = _
      simp only [eA, eB]; rfl

/-- The answer relation of `F_Σ A` at `σ = []` and a data `A` is the kernel's. -/
theorem effRet_nil_data (p : Placement) (δ : LSub) {A : VTy} (hA : A.Data) :
    ∀ (S : Row) (ls : List SRec) (v : Val),
      effRet p [] δ (CTy.effOf S A) [] ls v = Core.effRet (CTy.effOf S A) δ ls v
  | [], ls, v => by
      show vRL p [] δ A [] ls v = vC true A ls δ v
      exact vRL_data p [] δ [] hA ls v
  | o :: S, ls, v => by
      show effRet p [] δ (CTy.effOf S A) [] ls v = Core.effRet (CTy.effOf S A) δ ls v
      exact effRet_nil_data p δ hA S ls v

/-- **Statement 0's shared lemma `NilSoundRet`**: at `σ = []` and a data answer, W's computation
relation is Core's. -/
theorem nilSoundRet (p : Placement) : NilSoundRet (ℍ := ℍ) p := by
  intro δ S A ls e ρ hA h
  cases S with
  | nil =>
      show wpTS ls e (fun ls'' => vCE none true A ls'' δ) ρ
      have h' : wpTS ls e (fun ls'' v => vRL p [] δ A [] ls'' v) ρ := h
      simpa only [vRL_data p [] δ [] hA, show extS δ [] [] = δ from rfl] using h'
  | cons o S =>
      show ewpTS ls e (opTable (rowTab o.n o.i o.q o.A o.B o.fin (CTy.effOf S A) δ))
        (Core.effRet (CTy.effOf S A) δ) ρ
      have hQ : ∀ ls v ρ, effRet p [] δ (CTy.effOf S A) [] ls v ρ ↔
          Core.effRet (CTy.effOf S A) δ ls v ρ := fun ls v ρ => by
        rw [effRet_nil_data p δ hA S ls v]
      refine (GhostEnd.bodyS_nil_iff (δ := δ) hQ).mp ?_
      have h' : cRL p [] δ (.eff o.n o.i o.q o.A o.B o.fin (CTy.effOf S A)) [] ls e ρ := h
      unfold cRL at h'
      split at h'
      · exact bodySF_bodyS (fun _ _ _ _ _ _ _ h'' => openSF_openS h'') _ h'
      · exact h'

end ProbeD1

end
