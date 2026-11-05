import Core.Chain.SI.HeapN
import Core.Chain.SI.IStopN
import Core.EffMachine

/-!
# The undone write through an `imm` copy

`scope-threads.md` §2.3. A run that holds an `imm` copy of `ℓ` at value `v` and runs
`ℓ := w; ℓ := v` ends at the memory it started from, with its resource unchanged. Every
post-configuration conjunct reads only the end of the run, so every conjunct of `rwp`'s run
clause except the access guard holds at every index and every frame (`undoneImmWrite_run`).
Between the two stores a holder of the other copy reads `w`.

The access guard G (`FrameKept`, a conjunct of `rwp`'s and `rwpG`'s run clause) is the
condition on the configurations in between: at a frame that holds the other copy
(`copy_config`), the memory after the first store disagrees with the frame's flattening at `ℓ`,
so for `w ≠ ()` the run is not in `rwp` at any index above `1` (`not_undoneImmWrite`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

namespace UndoneWrite

theorem inStratum_empty' (A : Life) : ResU.InStratum A (PMap.empty : WRes) :=
  fun _ _ h => by rw [PMap.empty_get] at h; cases h

/-- An `imm` copy of `ℓ` at `v`, borrowed at `A`, over nothing. -/
def immCopy (l : Loc) (A : Life) (v : Val) : WRes :=
  ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty (inStratum_empty' _))

/-- `ℓ := v`. -/
def storeE (l : Loc) (v : Val) : Expr := .app (.val (Val.storeV (Val.loc l))) (.val v)

/-- `ℓ := w; ℓ := v`. -/
def undoE (l : Loc) (w v : Val) : Expr := .seq (storeE l w) (storeE l v)

/-- The post: the resource handed back unchanged. -/
def undoPost (ρA : WRes) : PostN := fun _ _ _ σ => σ = ρA

/-- **`UndoneImmWrite`** (`scope-threads.md` §2.3): the undone write through an `imm` copy is in
`rwp`. -/
def UndoneImmWrite (Φ : LocFam) (l : Loc) (A : Life) (w v : Val) (n : Nat) (ls : List SRec) :
    Prop :=
  rwp (ℍ := ℍ) Φ (undoPost (immCopy l A v)) n ls (undoE l w v) (immCopy l A v)

/-- A frame over `ρ` that holds an `imm` copy of `ℓ` lowers to a memory holding its value. -/
theorem lower_immCopy {l : Loc} {A : Life} {v : Val} {ρf fρ : WRes} {μ : Heap}
    (hc : ResU.CompS ρf (immCopy l A v) fρ) (hl : ResU.Lower fρ μ) : μ l = some v := by
  obtain ⟨χ, hχ, heχ⟩ := compS_get_erase (ResU.CompS.comm hc) (ResU.single_get_self l _)
  rw [lower_get hl hχ, heχ]
  rfl

theorem storeE_allocs (l : Loc) (v : Val) : (storeE l v).allocs = false := rfl

/-- The three steps of `ℓ := w; ℓ := v`, each its configuration's only one. -/
theorem undo_steps {l : Loc} {w v u : Val} {μ : Heap} (hlu : μ l = some u) :
    Step1Only (ℍ := ℍ) μ (undoE l w v) (μ.upd l w) (.seq (.val Val.unit) (storeE l v)) ∧
    Step1Only (ℍ := ℍ) (μ.upd l w) (.seq (.val Val.unit) (storeE l v)) (μ.upd l w)
      (storeE l v) ∧
    Step1Only (ℍ := ℍ) (μ.upd l w) (storeE l v) ((μ.upd l w).upd l v) (.val Val.unit) := by
  refine ⟨?_, ?_, ?_⟩
  · exact step1Only_plug (K := Kont.seq .hole (storeE l v))
      (Head.store μ l w u hlu) (storeE_allocs l w)
  · exact step1Only_plug (K := Kont.hole) (Head.seq (μ.upd l w) (storeE l v)) rfl
  · exact step1Only_plug (K := Kont.hole)
      (Head.store (μ.upd l w) l v w (BoCa.BoLo.Heap.upd_same μ l w)) (storeE_allocs l v)

theorem upd_upd_self {μ : Heap} {l : Loc} {w v : Val} (h : μ l = some v) :
    (μ.upd l w).upd l v = μ := by
  funext k
  by_cases e : k = l
  · subst e; rw [BoCa.BoLo.Heap.upd_same, h]
  · rw [BoCa.BoLo.Heap.upd_other e, BoCa.BoLo.Heap.upd_other e]

/-- **The undone write's run clause without the guard**: from every frame, every run of
`ℓ := w; ℓ := v` shorter than the index ends at `()` with the start's memory and resource, or
steps. -/
theorem undoneImmWrite_run (Φ : LocFam) (l : Loc) (A : Life) (w v : Val) (n : Nat)
    (ls : List SRec) :
    ∀ (ρf fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash ρf (immCopy l A v) → ResU.CompS ρf (immCopy l A v) fρ →
      TWNC fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Lower fρ μ → FinDom μ →
      ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ (undoE l w v) μ' e' →
        (∀ u : Val, e' = u.1 →
          EndOK Φ (undoPost (immCopy l A v)) (n - j) ls (immCopy l A v) ρf ps μ' u) ∧
        (¬ IsVal e' → ∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'') := by
  intro ρf fρ ps μ hf hc hT htg hl _ j μ' e' _ hrun
  have hlv := lower_immCopy hc hl
  obtain ⟨s₀, s₁, s₂⟩ := undo_steps (ℍ := ℍ) (w := w) (v := v) hlv
  have nv : ∀ {e : Expr} (u : Val), ¬ IsVal e → e = u.1 → False :=
    fun u hn he => hn (he ▸ u.2)
  cases hrun with
  | refl => exact ⟨fun u hu => (nv u not_isVal_seq hu).elim, fun _ => ⟨_, _, s₀.1⟩⟩
  | more h t =>
  obtain ⟨rfl, rfl⟩ := s₀.2 _ _ h
  cases t with
  | refl => exact ⟨fun u hu => (nv u not_isVal_seq hu).elim, fun _ => ⟨_, _, s₁.1⟩⟩
  | more h t =>
  obtain ⟨rfl, rfl⟩ := s₁.2 _ _ h
  cases t with
  | refl =>
      have hnv : ¬ IsVal (storeE l v) :=
        (Head.store (μ.upd l w) l v w (BoCa.BoLo.Heap.upd_same μ l w)).not_isVal
      exact ⟨fun u hu => (nv u hnv hu).elim, fun _ => ⟨_, _, s₂.1⟩⟩
  | more h t =>
  obtain ⟨rfl, rfl⟩ := s₂.2 _ _ h
  cases t with
  | more h' _ => exact absurd h' BoLo.no_step_val
  | refl =>
  rw [upd_upd_self hlv]
  refine ⟨fun u hu => ?_, fun hn => absurd Val.unit.2 hn⟩
  obtain rfl : u = Val.unit := Subtype.ext hu.symm
  exact ⟨immCopy l A v, PMap.empty, fρ, fρ, immCopy l A v, ps, ls,
    ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)),
    ResU.comp_empty_right fρ, hl, ResU.comp_empty_right _,
    UpdVN.refl Φ _ (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, rfl⟩

/-! ### The guard refutes it

The configuration: the world `ℓ ↦ imm({A}, (), ∅)`, entered from `ℓ ↦ own(())` by
`TWNC.immFrame`, split into two copies (`compS_imm_dup`), one the run's and one the frame's. -/

/-- The record of the frozen cell. -/
def recU (l : Loc) : FrameRec := ⟨l, Val.unit, PMap.empty, .unk, ⟨[]⟩⟩

/-- **A frame holding the other copy**: every hypothesis of `rwp`'s run clause holds at the
world of the two copies. -/
theorem copy_config (l : Loc) (A : Life) :
    ∃ ls : List SRec, ∃ ps : List FrameRec,
      ResU.Hash (immCopy l A Val.unit) (immCopy l A Val.unit) ∧
      ResU.CompS (immCopy l A Val.unit) (immCopy l A Val.unit) (immCopy l A Val.unit) ∧
      TWNC (immCopy l A Val.unit) ps (rsOf ls) ∧ Tagged (immCopy l A Val.unit) ps ls ∧
      ResU.Lower (immCopy l A Val.unit) (BoCa.BoLo.Heap.upd (fun _ => none) l Val.unit) ∧
      FinDom (BoCa.BoLo.Heap.upd (fun _ => none) l Val.unit) := by
  have hshape : vShape .unk (⟨[]⟩ : BoCa.Lifetime.LSub) Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
  have hadm : AdmWf .unk (⟨[]⟩ : BoCa.Lifetime.LSub) := fun _ h => h.elim
  obtain ⟨ds, hds⟩ := lineage_list (r := recU l) hshape hadm
    (ExW.empty_of_all_imm (fun _ _ h => by simp [recU] at h))
  set W : WRes := ResU.single l (CellU.ownOf Val.unit)
  have hvW : ResU.Valid W := ResU.valid_single_own l Val.unit
  have hT : TWNC W [] (rsOf []) :=
    TWNC.alloc TWNC.empty lower_empty rfl (compS_empty_left _) hvW
  have hhW : ResU.Hash (PMap.empty : WRes) W := ResU.hash_symm (ResU.hash_empty_right hvW)
  have hhi : ResU.Hash (PMap.empty : WRes) (immCopy l A Val.unit) :=
    ResU.six34 (compS_empty_left _) hhW
  have hvi : ResU.Valid (immCopy l A Val.unit) := (hash_valid hhi).2
  have hX : ResU.CompS (ResU.single l (CellU.ownOf Val.unit)) PMap.empty W :=
    ResU.comp_empty_right _
  have hW' : ResU.CompS (immCopy l A Val.unit) PMap.empty (immCopy l A Val.unit) :=
    ResU.comp_empty_right _
  have hT' : TWNC (immCopy l A Val.unit) [recU l] (recU l :: (ds ++ rsOf [])) :=
    TWNC.immFrame (l := l) (v := Val.unit) (α := A) .unk ⟨[]⟩ (inStratum_empty' _) hT hadm
      hX (ResU.comp_empty_right _) hshape hW' hvi hds
  obtain ⟨hFL, -⟩ := frameLife_frame (ps := []) (rs := rsOf []) (T := .unk) (δ := ⟨[]⟩)
    (hα := inStratum_empty' _) hvW hX (ResU.comp_empty_right _) hW' hT.inv
  have hdup := compS_imm_dup l (LSet.singleton A) Val.unit PMap.empty (inStratum_empty' _)
  refine ⟨frameList (recU l) ds A [], [recU l], ⟨hdup.1, _, hdup, hvi⟩, hdup, ?_, ?_, ?_,
    fd_upd fd_empty l Val.unit⟩
  · rw [rsOf_frameList]; exact hT'
  · intro x hx
    simp only [frameList, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨d, hd, rfl⟩ | hx
    · exact ⟨recU l, List.mem_cons_self, DescR.refl _, hFL⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨recU l, List.mem_cons_self, ⟨q, hqd⟩, hFL⟩
    · simp at hx
  · have hLW : ResU.Lower W (BoCa.BoLo.Heap.upd (fun _ => none) l Val.unit) :=
      lower_compS_own (compS_empty_left _) lower_empty rfl
    exact (ResU.lower_swap_imm_own (compS_empty_left _) hvi hvW (compS_empty_left _) hhi
      (compS_empty_left _) hhW).mpr hLW

/-- **The guard refutes the undone write**: at the frame holding the other copy, the run's first
store leaves a memory that disagrees with the frame's flattening at `ℓ`, so `ℓ := w; ℓ := ()` is
not in `rwp` at any index above `1`, at the list of that world. -/
theorem not_undoneImmWrite (Φ : LocFam) (l : Loc) (A : Life) {w : Val} (hw : w ≠ Val.unit)
    {n : Nat} (hn : 2 ≤ n) : ∃ ls, ¬ UndoneImmWrite (ℍ := ℍ) Φ l A w Val.unit n ls := by
  obtain ⟨ls, ps, hf, hc, hT, htg, hl, hfd⟩ := copy_config l A
  refine ⟨ls, fun h => hw ?_⟩
  have hlu : BoCa.BoLo.Heap.upd (fun _ => none) l Val.unit l = some Val.unit :=
    BoCa.BoLo.Heap.upd_same _ l Val.unit
  obtain ⟨s₀, -, -⟩ := undo_steps (ℍ := ℍ) (w := w) (v := Val.unit) hlu
  obtain ⟨hkept, -, -⟩ := h _ _ ps _ hf hc hT htg hl hfd 1 _ _ (by omega) (.more s₀.1 (.refl _ _))
  -- the frame's flattening holds a cell at `ℓ`, of value `()`
  obtain ⟨σ, hσ, hμ⟩ := hl
  have hl' := hμ l
  rw [hlu] at hl'
  cases hg : σ.get l with
  | none => rw [hg] at hl'; cases hl'
  | some ψ =>
    rw [hg] at hl'
    have h1 := hkept l ψ ⟨σ, hσ, hg⟩
    rw [BoCa.BoLo.Heap.upd_same] at h1
    rw [Option.some.inj h1]
    exact (Option.some.inj hl').symm

end UndoneWrite

end BoCa.Fig16.LogRel.Core.Chain.SI

end
