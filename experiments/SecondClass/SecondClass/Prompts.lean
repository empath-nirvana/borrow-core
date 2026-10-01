import SecondClass.Restated

/-!
# SecondClass — handling at a name chosen at run time

The question (`docs/second-class-and-system-c.md` §2): can §19's native capture be indexed by a
prompt capability, a handle on a handler's prompt that is generated when the handler is
installed (Effekt's design), instead of a static name?

What this file checks is the semantic half: **the existing relation already proves handling
sound at any name that is fresh for the prompts in scope, whoever chose it.**

- A **prompt environment** `P` lists the prompts in scope, each a run-time name with its
  effect's operations; its row `P.row` is what §19's `F_Σ` reads.
- `handleAt_compatC`: if a body is sound at the row extended by a prompt `n` that is fresh for
  `P`, then handling it at `n` is sound at `P.row`. It is `handle_compatC`, whose proof uses the
  static name only through `hnS` (no operation of the outer row has the handler's name), and
  freshness is exactly `hnS` (`row_names`).
- `fresh_exists`: a fresh nonzero name exists for every prompt environment of fewer than
  `2³² − 1` prompts.

What it does not provide, and the doc's §2 states precisely:

- **a machine step that chooses the name.** Names are `UInt32` values in `hnd`'s payload, and
  nothing in the machine generates one; the step must see a supply that no compositional proof
  sees (a counter in the machine state, or names as locations);
- **a type that holds a prompt whose name is not known statically.** `cC (F_Σ A)` reads its
  table from the row `Σ`, whose names are literals; a capability type needs name variables in
  rows, interpreted by a map from name variables to run-time names beside `δ`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.SecondClass
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The prompts in scope, innermost first: each a run-time name and its effect's operations. -/
abbrev PromptEnv := List (UInt32 × List (Qual × VTy × VTy))

/-- The prompts' names. -/
def PromptEnv.names (P : PromptEnv) : List UInt32 := P.map (·.1)

/-- The row of the prompts in scope: each prompt's operations at its name. -/
def PromptEnv.row : PromptEnv → Row
  | [] => []
  | (n, E) :: P => Row.ofEff n E 0 ++ PromptEnv.row P

theorem ofEff_name (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (o : OpSig),
    o ∈ Row.ofEff n E k → o.n = n
  | [], _, _, h => by simp [Row.ofEff] at h
  | (q, A, B) :: E, k, o, h => by
      simp only [Row.ofEff, List.mem_cons] at h
      rcases h with rfl | h
      · rfl
      · exact ofEff_name n E (k + 1) o h

/-- Every operation of the row is at a name of the environment. -/
theorem row_names : ∀ (P : PromptEnv) (o : OpSig), o ∈ P.row → o.n ∈ P.names
  | [], _, h => by simp [PromptEnv.row] at h
  | (n, E) :: P, o, h => by
      simp only [PromptEnv.row, List.mem_append] at h
      simp only [PromptEnv.names, List.map_cons, List.mem_cons]
      rcases h with h | h
      · exact Or.inl (ofEff_name n E 0 o h)
      · exact Or.inr (row_names P o h)

/-- **Handling at a fresh run-time name is sound.** For any prompt environment `P` and any
nonzero name `n` that no prompt of `P` has, a body sound at `P` extended by the prompt `(n, E)` is
handled soundly at `P`. The name enters only through freshness. -/
theorem handleAt_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ Γr Γc : Ctx VTy} {e : Expr} {P : PromptEnv}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} {ir ic : Nat}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hsp₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy P.row A R)) (hc : Ctx.SoloP Γc ic (clausesTy P.row R E))
    (hn0 : n ≠ 0) (hfresh : n ∉ P.names) (hlen : E.length ≤ 2 ^ 32)
    (he : SemC Δ Γ₂ e (CTy.effOf (PromptEnv.row ((n, E) :: P)) A)) :
    SemC Δ Γ (hndTerm n ir ic e) (CTy.effOf P.row R) :=
  handle_compatC hsp hsp₁ hr hc hn0
    (fun o ho h => hfresh (h ▸ row_names P o ho)) hlen he

/-- The candidates `1, …, k`, as names. -/
def candidates (k : Nat) : List UInt32 := (List.range k).map fun j => UInt32.ofNat (j + 1)

theorem candidates_nodup {k : Nat} (hk : k < 2 ^ 32) : (candidates k).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro x hx y hy hxy
  simp only [List.mem_range] at hx hy
  have h := congrArg UInt32.toNat hxy
  rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega), UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at h
  omega

theorem candidates_ne_zero {k : Nat} (hk : k < 2 ^ 32) : ∀ x ∈ candidates k, x ≠ 0 := by
  intro x hx h
  simp only [candidates, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have h' := congrArg UInt32.toNat h
  rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at h'
  simp at h'

/-- **A fresh name exists** for every environment of fewer than `2³² − 1` prompts. -/
theorem fresh_exists (P : PromptEnv) (hP : P.length + 1 < 2 ^ 32) :
    ∃ n : UInt32, n ≠ 0 ∧ n ∉ P.names := by
  classical
  have hlt : P.names.toFinset.card < (candidates (P.length + 1)).toFinset.card := by
    rw [List.toFinset_card_of_nodup (candidates_nodup hP)]
    calc P.names.toFinset.card ≤ P.names.length := List.toFinset_card_le _
      _ = P.length := by simp [PromptEnv.names]
      _ < (candidates (P.length + 1)).length := by simp [candidates]
  obtain ⟨x, hx, hnx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [List.mem_toFinset] at hx hnx
  exact ⟨x, candidates_ne_zero hP x hx, hnx⟩

end BoCa.Fig16.LogRel.Core.SecondClass
