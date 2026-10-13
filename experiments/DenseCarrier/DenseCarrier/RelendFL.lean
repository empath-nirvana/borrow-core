import DenseCarrier.RelendRoom
import Core.Fundamental

/-!
# DenseCarrier — what the fundamental property relates re-lends, at every type

`RelendRoom.lean` refutes re-lending at `U` with a closure related only because its argument type
is empty at the reading. The `U` clause is semantic: it says what a closure does, not where the
closure came from. A closure the fundamental property relates is a typable term closed by a
substitution, and the fundamental property relates that term at **every** reading in `⟦Δ⟧`. A
re-lending keeps `⟦Δ⟧` (`modelsD_relend`), so such a term re-lends as soon as its captured
context does — at every computation type, `U`, `⊸`, `∀` and `F` included, at any depth:

* `semD_relend`: over every lifetime order, a term related by `SemD` re-lends whenever its captured
  context re-lends;
* `relend_gDenD`: a captured context of first-order types re-lends (`relend_fov` slot by slot);
* `semD_relend_fov`: so a term `SemD` relates, over a first-order context, re-lends at every
  computation type;
* In Core (`L = Life`): `core_relend_fov` (Core's `vC` at every first-order type) and
  `core_relend_derivable` — **every term Core's typing derives** (`fundamentalC`), closed by a
  first-order context, re-lends at every computation type, at every re-slotting.

So the property that makes re-lending valid at `U` is not a pointwise property of stored
predicates (the refuting closure stores none): it is that the closure is the fundamental property's,
a property of how the configuration was built. A captured closure re-lends by the same argument when
it is itself a typable term over a context that re-lends; the hereditary version is not built here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx LSub)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-! ### `⟦Δ⟧` and the captured context -/

/-- **A re-lending keeps `⟦Δ⟧`**: it keeps the order of the reading's lifetimes. -/
theorem modelsD_relend {ι : Slots L} (R : Relend ι) {Δ : LifeCtx} {δ : LSubD L}
    (h : ModelsD Δ δ) : ModelsD Δ (δ.map R.ψ) := by
  intro x u hu
  obtain ⟨m, n, hm, hn, hlt⟩ := h x u hu
  exact ⟨R.ψ m, R.ψ n, by rw [LSubD.find?_map, hm]; rfl, R.interp_some hn, R.mono hlt⟩

/-- Every live slot of the context is at a first-order type. -/
def FOCtx (Γ : Ctx VTy) : Prop := ∀ s ∈ Γ, s.live = true → FOV s.ty

theorem emp_eq {ρ : WRes} (h : (emp : WProp) ρ) : ρ = PMap.empty := h.1

/-- **A first-order captured context re-lends**, slot by slot. -/
theorem relend_gSepD {ι : Slots L} (R : Relend ι) {ls : List SRec} {δ : LSubD L} :
    ∀ (Γ : Ctx VTy), FOCtx Γ → ∀ (γ : List Val) (ρ : WRes), gSepD (ℍ := ℍ) ι ls δ Γ γ ρ →
      ∀ ls' : List SRec, ∃ ρ', RemakeR R.θ ρ ρ' ∧ gSepD (ℍ := ℍ) ι ls' (δ.map R.ψ) Γ γ ρ'
  | [], _, γ, ρ, h, ls' => by
      obtain rfl := emp_eq h
      exact ⟨PMap.empty, remakeR_empty, by cases γ <;> exact ⟨rfl, trivial⟩⟩
  | s :: Γ, hΓ, [], ρ, h, ls' => by
      obtain rfl := emp_eq h
      exact ⟨PMap.empty, remakeR_empty, ⟨rfl, trivial⟩⟩
  | s :: Γ, hΓ, v :: γ, ρ, h, ls' => by
      have hΓ' : FOCtx Γ := fun t ht hl => hΓ t (List.mem_cons_of_mem _ ht) hl
      by_cases hl : s.live = true
      · have hs : FOV s.ty := hΓ s (List.mem_cons_self) hl
        have h' : (vD (ℍ := ℍ) ι s.ty ls δ v ⋆ gSepD (ℍ := ℍ) ι ls δ Γ γ) ρ := by
          simpa [gSepD, hl] using h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h'
        obtain ⟨ρ₁', hR₁, h₁'⟩ := relend_fov R s.ty hs ls δ v ρ₁ h₁ ls'
        obtain ⟨ρ₂', hR₂, h₂'⟩ := relend_gSepD R Γ hΓ' γ ρ₂ h₂ ls'
        obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc hR₁ hR₂
        refine ⟨ρ', hR, ?_⟩
        unfold gSepD
        rw [if_pos hl]
        exact ⟨ρ₁', ρ₂', hc', h₁', h₂'⟩
      · have h' : gSepD (ℍ := ℍ) ι ls δ Γ γ ρ := by simpa [gSepD, hl] using h
        obtain ⟨ρ', hR, h''⟩ := relend_gSepD R Γ hΓ' γ ρ h' ls'
        exact ⟨ρ', hR, by simpa [gSepD, hl] using h''⟩

theorem relend_gDenD {ι : Slots L} (R : Relend ι) {ls : List SRec} {δ : LSubD L} {Γ : Ctx VTy}
    (hΓ : FOCtx Γ) {γ : List Val} {ρ : WRes} (h : gDenD (ℍ := ℍ) ι ls δ Γ γ ρ) (ls' : List SRec) :
    ∃ ρ', RemakeR R.θ ρ ρ' ∧ gDenD (ℍ := ℍ) ι ls' (δ.map R.ψ) Γ γ ρ' := by
  obtain ⟨hlive, hs⟩ := pure_sep_iff.mp h
  obtain ⟨ρ', hR, hs'⟩ := relend_gSepD R Γ hΓ γ ρ hs ls'
  exact ⟨ρ', hR, pure_sep_mk hlive hs'⟩

/-! ### Terms the fundamental property relates -/

/-- **A term the fundamental property relates re-lends whenever its captured context does**, at
every computation type: `SemD` holds at the moved reading, which `⟦Δ⟧` admits. -/
theorem semD_relend {ι : Slots L} (R : Relend ι) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy}
    (hS : SemD (ℍ := ℍ) ι Δ Γ e C) {δ : LSubD L} {γ : List Val} {ls' : List SRec}
    {ρ ρ' : WRes} (hδ : ModelsD Δ δ) (hR : RemakeR R.θ ρ ρ')
    (hg : gDenD (ℍ := ℍ) ι ls' (δ.map R.ψ) Γ γ ρ') :
    ∃ ρ'', RemakeR R.θ ρ ρ'' ∧ cD (ℍ := ℍ) ι C ls' (δ.map R.ψ) (substAll γ e) ρ'' :=
  ⟨ρ', hR, hS _ γ ls' ρ' (modelsD_relend R hδ) hg⟩

/-- **Over a first-order captured context, a term `SemD` relates re-lends at every computation
type.** -/
theorem semD_relend_fov {ι : Slots L} (R : Relend ι) {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr}
    {C : CTy} (hS : SemD (ℍ := ℍ) ι Δ Γ e C) (hΓ : FOCtx Γ) {δ : LSubD L} {γ : List Val}
    {ls : List SRec} {ρ : WRes} (hδ : ModelsD Δ δ) (hg : gDenD (ℍ := ℍ) ι ls δ Γ γ ρ)
    (ls' : List SRec) :
    ∃ ρ', RemakeR R.θ ρ ρ' ∧ cD (ℍ := ℍ) ι C ls' (δ.map R.ψ) (substAll γ e) ρ' := by
  obtain ⟨ρ', hR, hg'⟩ := relend_gDenD R hΓ hg ls'
  exact semD_relend R hS hδ hR hg'

/-! ### In Core -/

/-- An `LSub` read as an `LSubD Life`. -/
def ofLSub (δ : LSub) : LSubD Life := ⟨δ.entries.map fun p => (p.1, OrderDual.toDual p.2)⟩

theorem toLSub_ofLSub (δ : LSub) : toLSub (ofLSub δ) = δ := by
  cases δ
  simp [toLSub, ofLSub, Function.comp_def]

/-- **Core's relation re-lends at every first-order type**, at every re-slotting: `relend_fov` at
`L = Life` and the identity placement, read through `vD_id`. -/
theorem core_relend_fov {c : Life} (θ : Restrat.Emb c) {A : VTy} (hA : FOV A) {ls : List SRec}
    {δ : LSub} {v : Val} {ρ : WRes} (h : vCE (ℍ := ℍ) none true A ls δ v ρ) (ls' : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧ vCE (ℍ := ℍ) none true A ls' (Restrat.LSub.mapN θ.toNat δ) v ρ' := by
  have hD : vD (ℍ := ℍ) Slots.id A ls (ofLSub δ) v ρ := by
    rw [vD_id A (fragV_of_fov A hA), toLSub_ofLSub]; exact h
  obtain ⟨ρ', hR, h'⟩ := relend_fov (lifeRelend θ) A hA ls (ofLSub δ) v ρ hD ls'
  refine ⟨ρ', hR, ?_⟩
  change vD (ℍ := ℍ) Slots.id A ls' ((ofLSub δ).map θ.f) v ρ' at h'
  rw [vD_id A (fragV_of_fov A hA), toLSub_map_emb, toLSub_ofLSub] at h'
  exact h'

/-- Core's captured context, first-order, re-lends. -/
theorem core_relend_gSepC {c : Life} (θ : Restrat.Emb c) {ls : List SRec} {δ : LSub} :
    ∀ (Γ : Ctx VTy), FOCtx Γ → ∀ (γ : List Val) (ρ : WRes), gSepC (ℍ := ℍ) ls δ Γ γ ρ →
      ∀ ls' : List SRec,
        ∃ ρ', RemakeR θ ρ ρ' ∧ gSepC (ℍ := ℍ) ls' (Restrat.LSub.mapN θ.toNat δ) Γ γ ρ'
  | [], _, γ, ρ, h, ls' => by
      obtain rfl := emp_eq h
      exact ⟨PMap.empty, remakeR_empty, by cases γ <;> exact ⟨rfl, trivial⟩⟩
  | s :: Γ, hΓ, [], ρ, h, ls' => by
      obtain rfl := emp_eq h
      exact ⟨PMap.empty, remakeR_empty, ⟨rfl, trivial⟩⟩
  | s :: Γ, hΓ, v :: γ, ρ, h, ls' => by
      have hΓ' : FOCtx Γ := fun t ht hl => hΓ t (List.mem_cons_of_mem _ ht) hl
      by_cases hl : s.live = true
      · have hs : FOV s.ty := hΓ s (List.mem_cons_self) hl
        have h' : (vCE (ℍ := ℍ) none true s.ty ls δ v ⋆ gSepC (ℍ := ℍ) ls δ Γ γ) ρ := by
          simpa [gSepC, hl] using h
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h'
        obtain ⟨ρ₁', hR₁, h₁'⟩ := core_relend_fov θ hs h₁ ls'
        obtain ⟨ρ₂', hR₂, h₂'⟩ := core_relend_gSepC θ Γ hΓ' γ ρ₂ h₂ ls'
        obtain ⟨ρ', hc', hR⟩ := remakeR_compS hc hR₁ hR₂
        refine ⟨ρ', hR, ?_⟩
        unfold gSepC
        rw [if_pos hl]
        exact ⟨ρ₁', ρ₂', hc', h₁', h₂'⟩
      · have h' : gSepC (ℍ := ℍ) ls δ Γ γ ρ := by simpa [gSepC, hl] using h
        obtain ⟨ρ', hR, h''⟩ := core_relend_gSepC θ Γ hΓ' γ ρ h' ls'
        exact ⟨ρ', hR, by simpa [gSepC, hl] using h''⟩

/-- **Every term Core's typing derives re-lends**, closed by a first-order context, at every
computation type and every re-slotting: the fundamental property at the re-slotted reading, which
`⟦Δ⟧` admits (`Restrat.Emb.models_mapN_iff`), with the context re-lent (`core_relend_gSepC`). -/
theorem core_relend_derivable {c : Life} (θ : Restrat.Emb c) {Δ : LifeCtx} {Γ : Ctx VTy}
    {e : Expr} {C : CTy} (hd : CDerives Δ Γ e (.comp C)) (hΓ : FOCtx Γ) {δ : LSub}
    {γ : List Val} {ls : List SRec} {ρ : WRes} (hδ : Δ.Models δ)
    (hg : gDenC (ℍ := ℍ) ls δ Γ γ ρ) (ls' : List SRec) :
    ∃ ρ', RemakeR θ ρ ρ' ∧
      cC (ℍ := ℍ) C ls' (Restrat.LSub.mapN θ.toNat δ) (substAll γ e) ρ' := by
  obtain ⟨hlive, hs⟩ := pure_sep_iff.mp hg
  obtain ⟨ρ', hR, hs'⟩ := core_relend_gSepC θ Γ hΓ γ ρ hs ls'
  exact ⟨ρ', hR, (fundamentalC (ℍ := ℍ) hd : SemC Δ Γ e C) _ γ ls' ρ'
    ((θ.models_mapN_iff Δ δ).mpr hδ) (pure_sep_mk hlive hs')⟩

end DenseCarrier

end
