import Law2.Remake

/-!
# Law2 — the typed world is closed under the stop's ghost end and the resume's re-make

The resume makes a suspended region's lends afresh: every `mut` cell of the region is re-made at
its moved lifetime, its witness re-made cell by cell, storing the predicate the relation at the
moved reading asks for (`RemakeR`). For the resumed run to be read by `wpTS`, whose frames range
over the typed world `TW`, the re-made configuration has to be a typed world.

**It is, by the typed world's own steps** (`tw_remake`). The re-make of one cell is the pair Law 2
names: the lend ended at the stop, as 6.65's exit ends it (`TW.mutUnfold`), and made afresh at the
resume, as 6.65's entry makes it (`TW.mutFold`), with the witness re-made in between. No new
constructor is needed, so `TI` holds of the re-made world by `TW.inv`, with no new preservation
lemma (`ti_remake`).

Depth is the cells' nesting: a cell's witness lies strictly above it, so its cells are at lower
levels (distance below `⊤`). The proof is one induction on a level bound, and inside it one on the
locations being re-made; a cell's witness is re-made by the induction hypothesis between its
unfold and its fold. There is no case on the depth.

The validity each step asks for is `[TR]` 6.24 (`ResU.six24`): a world is valid with a `mut` cell
exactly when it is valid with the cell unfolded, whatever the cell's lifetime and predicate.

`RemakeR` re-makes `own` and `mut` cells only, so the theorem is stated for re-makes of worlds
whose re-made part holds no `imm` cell (the fragment `relend_fov` re-lends). Re-making an `imm`
lend (6.64's records, re-slotted) is not derived here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar LifeCtx LSub)

section
variable {c : Life} {θ : Restrat.Emb c}

/-- The level of a lifetime: how far below `⊤` it is. -/
abbrev lvl (b : Life) : ℕ := OrderDual.ofDual b

/-- `W'` is `W` re-made at the locations `D`, and equal to it elsewhere. -/
def RemakeAt (θ : Restrat.Emb c) (D : List Loc) (W W' : WRes) : Prop :=
  (∀ l ∈ D, RemakeO θ (W.get l) (W'.get l)) ∧ ∀ l, l ∉ D → W'.get l = W.get l

/-- The `mut` cells of `W` at the locations `D` are at levels below `k`. -/
def MutLevels (k : ℕ) (D : List Loc) (W : WRes) : Prop :=
  ∀ l ∈ D, ∀ ψ, W.get l = some ψ → ψ.kind = Kind.mut → lvl ψ.at < k

/-- A cell of a `mut` cell's witness is at a lower level. -/
theorem wit_lvl {b : Life} {χ : WRes} (h : χ.InStratum b) {m : Loc} {ψ : CellU Loc Val}
    (e : χ.get m = some ψ) (hk : ψ.kind = Kind.mut) : lvl ψ.at < lvl b := by
  have := (inStratum_iff_of_mut hk b).mp (h m ψ e)
  exact this

/-- The domain of a resource as a duplicate-free list. -/
theorem exists_dom (ρ : WRes) : ∃ D : List Loc, D.Nodup ∧ ∀ l, l ∈ D ↔ ρ.get l ≠ none := by
  classical
  obtain ⟨d, hd⟩ := ρ.finite
  refine ⟨(d.filter fun l => (ρ.get l).isSome).dedup, List.nodup_dedup _, fun l => ?_⟩
  simp only [List.mem_dedup, List.mem_filter, Option.isSome_iff_ne_none]
  exact ⟨fun h => h.2, fun h => ⟨hd l h, h⟩⟩

/-- Two worlds equal at every location are equal. -/
theorem eq_of_remakeAt_nil {W W' : WRes} (h : RemakeAt θ [] W W') : W' = W :=
  PMap.ext fun l => h.2 l (List.not_mem_nil)

/-- `mut` cells are not `imm`, `own` cells neither. -/
theorem not_imm_of_remakeC {a b : CellU Loc Val} (h : RemakeC θ a b) : b.kind ≠ Kind.imm := by
  rw [h.kind]; exact h.kind_ne_imm

/-- **One cell re-made in a typed world**, its witness re-made by the hypothesis `hS` (re-making
at lower levels). The lend is ended (`TW.mutUnfold`), the witness re-made, and the lend made afresh
at the moved lifetime with the re-made cell's predicate (`TW.mutFold`). -/
theorem tw_cell {k : ℕ}
    (hS : ∀ (D : List Loc) (W W' : WRes) (ps rs : List FrameRec), D.Nodup → TW W ps rs →
      RemakeAt θ D W W' → MutLevels k D W → TW W' ps rs)
    {W : WRes} {ps rs : List FrameRec} {l : Loc} {ψ ψ' : CellU Loc Val} (hT : TW W ps rs)
    (hl : W.get l = some ψ) (hR : RemakeC θ ψ ψ') (hk : ψ.kind = Kind.mut → lvl ψ.at ≤ k) :
    ∃ W₁, ResU.CompS (W.del l) (ResU.single l ψ') W₁ ∧ TW W₁ ps rs := by
  have hWZ : ResU.CompS (W.del l) (ResU.single l ψ) W := ResU.del_compS hl
  cases hR with
  | own v => exact ⟨W, hWZ, hT⟩
  | «mut» hkψ hkψ' hat hv hw =>
    -- the two cells, as `mutOf`
    obtain ⟨b, v, χ, hχ, P, hwP, rfl⟩ : ∃ b v χ hχ P hwP, ψ = CellU.mutOf b v χ hχ P hwP := by
      rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, ρ, h, rfl⟩ | h
      · exact absurd hkψ (by simp)
      · exact absurd hkψ (by simp)
      · exact h
    obtain ⟨b', v', χ', hχ', P', hwP', rfl⟩ :
        ∃ b' v' χ' hχ' P' hwP', ψ' = CellU.mutOf b' v' χ' hχ' P' hwP' := by
      rcases CellU.rep ψ' with ⟨v, rfl⟩ | ⟨s, v, ρ, h, rfl⟩ | h
      · exact absurd hkψ' (by simp)
      · exact absurd hkψ' (by simp)
      · exact h
    have hvv : v = v' := hv.symm
    subst hvv
    have hRχ : RemakeR θ χ χ' := by
      intro m; have := hw m; rwa [CellU.wit_mutOf, CellU.wit_mutOf] at this
    have hlvl : lvl b ≤ k := hk (CellU.kind_mutOf _ _ _ _ _ _)
    -- the end of the lend: `TW.mutUnfold`
    have hvW : ResU.Valid W := hT.valid
    have hvψ : ResU.Valid (ResU.single l (CellU.mutOf b v χ hχ P hwP)) :=
      (ResU.Valid.split (ResU.CompS.comm hWZ) hvW).1
    have hχl : χ.get l = none := ResU.wit_get_none_of_valid_mut hvψ
    obtain ⟨X, hX⟩ := ResU.compS_own_of_valid_mut hvψ
    have hHash : ResU.Hash (W.del l) (ResU.single l (CellU.mutOf b v χ hχ P hwP)) :=
      ⟨hWZ.1, W, hWZ, hvW⟩
    obtain ⟨-, W₁, hW₁, hvW₁⟩ := (ResU.six24 (ρ := W.del l) hX).mp hHash
    have hT₁ : TW W₁ ps rs :=
      TW.mutUnfold hT (ResU.CompS.comm hWZ) (ResU.CompS.comm hX) (ResU.CompS.comm hW₁) hvW₁
    -- the witness re-made in place
    have hχ'l : χ'.get l = none := (hRχ.get_none_iff l).mpr hχl
    obtain ⟨X', hX'⟩ : ∃ X', ResU.CompS χ' (ResU.single l (CellU.ownOf v)) X' :=
      (ResU.compS_defined_iff _ _).mpr (ResU.Compat.of_disjoint fun m => by
        by_cases hm : m = l
        · exact Or.inl (hm ▸ hχ'l)
        · exact Or.inr (ResU.single_get_ne _ hm))
    have hZχ : ∀ m, χ.get m ≠ none → (W.del l).get m = none := by
      intro m hm
      cases e : (W.del l).get m with
      | none => rfl
      | some ζ =>
          exfalso
          obtain ⟨ψχ, eχ⟩ : ∃ ψχ, χ.get m = some ψχ := Option.ne_none_iff_exists'.mp hm
          have hXm : X.get m = some ψχ := by
            have hml : m ≠ l := fun h => by rw [h, hχl] at eχ; cases eχ
            rw [ResU.Comp.get_of_right_none hX (ResU.single_get_ne _ hml)]; exact eχ
          have hkχ : ψχ.kind ≠ Kind.imm := hRχ.ne_imm eχ
          exact absurd (CellU.CompatS.kinds (hW₁.1 m ζ ψχ e hXm)).2 hkχ
    obtain ⟨W₁', hW₁'⟩ : ∃ W₁', ResU.CompS (W.del l) X' W₁' :=
      (ResU.compS_defined_iff _ _).mpr (ResU.Compat.of_disjoint fun m => by
        by_cases hm : m = l
        · exact Or.inl (by rw [hm]; exact ResU.del_get_self W l)
        · by_cases hχm : χ.get m = none
          · refine Or.inr ?_
            rw [ResU.Comp.get_of_right_none hX' (ResU.single_get_ne _ hm)]
            exact (hRχ.get_none_iff m).mpr hχm
          · exact Or.inl (hZχ m hχm))
    obtain ⟨Dχ, hDχ, hmemχ⟩ := exists_dom χ
    have hget₁ : ∀ m, m ≠ l → χ.get m ≠ none → W₁.get m = χ.get m := by
      intro m hml hχm
      rw [ResU.Comp.get_of_left_none hW₁ (hZχ m hχm),
        ResU.Comp.get_of_right_none hX (ResU.single_get_ne _ hml)]
    have hget₁' : ∀ m, m ≠ l → χ.get m ≠ none → W₁'.get m = χ'.get m := by
      intro m hml hχm
      rw [ResU.Comp.get_of_left_none hW₁' (hZχ m hχm),
        ResU.Comp.get_of_right_none hX' (ResU.single_get_ne _ hml)]
    have hRA : RemakeAt θ Dχ W₁ W₁' := by
      refine ⟨fun m hm => ?_, fun m hm => ?_⟩
      · have hχm := (hmemχ m).mp hm
        have hml : m ≠ l := fun h => hχm (h ▸ hχl)
        rw [hget₁ m hml hχm, hget₁' m hml hχm]
        exact hRχ m
      · have hχm : χ.get m = none := by
          by_contra h; exact hm ((hmemχ m).mpr h)
        have hχ'm : χ'.get m = none := (hRχ.get_none_iff m).mpr hχm
        by_cases hml : m = l
        · subst hml
          rw [ResU.Comp.get_of_left_none hW₁ (ResU.del_get_self W m),
            ResU.Comp.get_of_left_none hW₁' (ResU.del_get_self W m),
            ResU.Comp.get_of_left_none hX hχm, ResU.Comp.get_of_left_none hX' hχ'm]
        · have hXm : X.get m = none := by
            rw [ResU.Comp.get_of_right_none hX (ResU.single_get_ne _ hml)]; exact hχm
          have hX'm : X'.get m = none := by
            rw [ResU.Comp.get_of_right_none hX' (ResU.single_get_ne _ hml)]; exact hχ'm
          rw [ResU.Comp.get_of_right_none hW₁ hXm, ResU.Comp.get_of_right_none hW₁' hX'm]
    have hML : MutLevels k Dχ W₁ := by
      intro m hm ζ e hkζ
      have hχm := (hmemχ m).mp hm
      have hml : m ≠ l := fun h => hχm (h ▸ hχl)
      rw [hget₁ m hml hχm] at e
      exact lt_of_lt_of_le (wit_lvl hχ e hkζ) hlvl
    have hT₁' : TW W₁' ps rs := hS Dχ W₁ W₁' ps rs hDχ hT₁ hRA hML
    -- the lend made afresh: `TW.mutFold`
    have hHash' : ResU.Hash (W.del l) X' := ⟨hW₁'.1, W₁', hW₁', hT₁'.valid⟩
    obtain ⟨-, W₂, hW₂, hvW₂⟩ := (ResU.six24 (ρ := W.del l) (P := P') (hw := hwP') hX').mpr hHash'
    exact ⟨W₂, hW₂, TW.mutFold hT₁' (ResU.CompS.comm hX') (ResU.CompS.comm hW₁')
      (ResU.CompS.comm hW₂) hvW₂⟩

/-- **Re-making at a list of locations keeps a typed world a typed world**, the `mut` cells there
at levels below `k`. Induction on `k`, inside it on the locations. -/
theorem tw_remakeAt : ∀ (k : ℕ) (D : List Loc) (W W' : WRes) (ps rs : List FrameRec),
    D.Nodup → TW W ps rs → RemakeAt θ D W W' → MutLevels k D W → TW W' ps rs := by
  intro k
  induction k with
  | zero =>
      intro D W W' ps rs _ hT hR hML
      have : W' = W := PMap.ext fun l => by
        by_cases hl : l ∈ D
        · have hO := hR.1 l hl
          cases e : W.get l with
          | none =>
              cases e' : W'.get l with
              | none => rfl
              | some _ => rw [e, e'] at hO; cases hO
          | some ψ =>
              cases e' : W'.get l with
              | none => rw [e, e'] at hO; cases hO
              | some ψ' =>
                  rw [e, e'] at hO
                  cases hO with
                  | some hab =>
                      cases hab with
                      | own v => rfl
                      | «mut» hk => exact absurd (hML l hl _ e hk) (Nat.not_lt_zero _)
        · exact hR.2 l hl
      rw [this]; exact hT
  | succ k ih =>
      intro D
      induction D with
      | nil =>
          intro W W' ps rs _ hT hR _
          rw [eq_of_remakeAt_nil hR]; exact hT
      | cons l D ihD =>
          intro W W' ps rs hnd hT hR hML
          obtain ⟨hlD, hnd'⟩ := List.nodup_cons.mp hnd
          have hO := hR.1 l (List.mem_cons_self ..)
          cases e : W.get l with
          | none =>
              rw [e] at hO
              refine ihD W W' ps rs hnd' hT ⟨fun m hm => hR.1 m (List.mem_cons_of_mem _ hm),
                fun m hm => ?_⟩ (fun m hm => hML m (List.mem_cons_of_mem _ hm))
              by_cases hml : m = l
              · subst hml; rw [e]; cases e' : W'.get m with
                | none => rfl
                | some _ => rw [e'] at hO; cases hO
              · exact hR.2 m (by simp [hml, hm])
          | some ψ =>
              rw [e] at hO
              obtain ⟨ψ', e', hRψ⟩ : ∃ ψ', W'.get l = some ψ' ∧ RemakeC θ ψ ψ' := by
                cases e' : W'.get l with
                | none => rw [e'] at hO; cases hO
                | some ψ' =>
                    rw [e'] at hO
                    cases hO with
                    | some h => exact ⟨ψ', rfl, h⟩
              obtain ⟨W₁, hW₁, hT₁⟩ := tw_cell (k := k) ih hT e hRψ
                (fun hk => Nat.le_of_lt_succ (hML l (List.mem_cons_self ..) ψ e hk))
              have hget : ∀ m, m ≠ l → W₁.get m = W.get m := fun m hm => by
                rw [ResU.Comp.get_of_right_none hW₁ (ResU.single_get_ne _ hm),
                  ResU.del_get_ne W hm]
              have hgetl : W₁.get l = some ψ' := by
                rw [ResU.Comp.get_of_left_none hW₁ (ResU.del_get_self W l),
                  ResU.single_get_self]
              refine ihD W₁ W' ps rs hnd' hT₁ ⟨fun m hm => ?_, fun m hm => ?_⟩ ?_
              · have hml : m ≠ l := fun h => hlD (h ▸ hm)
                rw [hget m hml]; exact hR.1 m (List.mem_cons_of_mem _ hm)
              · by_cases hml : m = l
                · subst hml; rw [hgetl, e']
                · rw [hget m hml]; exact hR.2 m (by simp [hml, hm])
              · intro m hm ζ eζ hkζ
                have hml : m ≠ l := fun h => hlD (h ▸ hm)
                rw [hget m hml] at eζ
                exact hML m (List.mem_cons_of_mem _ hm) ζ eζ hkζ

/-- **A re-make of a typed world is a typed world.** Every re-made `mut` cell is the end of its
lend at the stop and the lend made afresh at the moved lifetime, with its re-made witness and new
predicate: the typed world's own `mutUnfold` and `mutFold`. The records are unchanged. -/
theorem tw_remake {W W' : WRes} {ps rs : List FrameRec} (hT : TW W ps rs)
    (hR : RemakeR θ W W') : TW W' ps rs := by
  classical
  obtain ⟨D, hD, hmem⟩ := exists_dom W
  let k : ℕ := (D.map fun l => ((W.get l).map fun ψ => lvl ψ.at).getD 0).sum + 1
  refine tw_remakeAt k D W W' ps rs hD hT ⟨fun l _ => hR l, fun l hl => ?_⟩ ?_
  · have hWl : W.get l = none := by
      by_contra h; exact hl ((hmem l).mpr h)
    rw [hWl]; exact (hR.get_none_iff l).mpr hWl
  · intro l hl ψ e _
    have hle : ((W.get l).map fun ψ => lvl ψ.at).getD 0 ≤
        (D.map fun l => ((W.get l).map fun ψ => lvl ψ.at).getD 0).sum :=
      List.le_sum_of_mem (List.mem_map_of_mem hl)
    rw [e] at hle
    exact Nat.lt_succ_of_le hle

/-- **The invariant of the typed world holds at the re-made world**, by `TW.inv`: no preservation
lemma beyond the existing steps'. -/
theorem ti_remake {W W' : WRes} {ps rs : List FrameRec} (hT : TW W ps rs)
    (hR : RemakeR θ W W') : TI W' ps rs :=
  (tw_remake hT hR).inv

end

end Law2

end
