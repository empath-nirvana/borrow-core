import NestedFold.Spec

/-!
# NestedFold — the destructor at `P`, and the two test types

**The destructor** (design §4.1 L4, §4.3): the fold with every result `1`. `HasDtorMu B₀`
restates `HasDtor.mu` at the class `P`: the body is in the class, and each binder's `T_b⟨1⟩`
and each array binder's `1 ⊕ (1 ⊗ S⟨1⟩)` has a destructor. `dtor_spec` is `fold_spec` at
`R_b = 1`: given an algebra in `𝒱⟦!(T_b⟨1⟩ ⊸ 1)⟧` per binder, the root handle consumes a value
of `μB₀` and answers `()` at the empty resource, so every cell is freed. Turning
`HasDtor (T_b⟨1⟩)` into such an algebra is `dtor_wf` and the fundamental property, at the new
constant: not done here.

**The tests** (#719):
1. `roseA = μX. I32 ⊗ Array X`: one `μ` binder and one array binder (`X` under the array).
2. `nestA = μX. I32 ⊗ μY. 1 ⊕ (Ref X ⊗ Ref Y)`: two `μ` binders, the inner body naming the outer
   variable. `reach` lists both, one handle each.

Both bodies are in `P` by `decide` (and outside `FShape`). Each gets the generic `fold_spec`
with its algebras as hypotheses (`roseA_fold`, `nestA_fold`), and the destructor with two
concrete closed algebras, `g₀ = λp. let (x, u) = p in u : I32 ⊗ 1 ⊸ 1` and
`g₁ = λx. case x (u. u) (p. let (a, b) = p in a) : 1 ⊕ (1 ⊗ 1) ⊸ 1`, every hypothesis
discharged (`roseA_dtor`, `nestA_dtor`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.NestedFold
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub)
open Classical

/-! ### The destructor -/

/-- Results `1` at every binder; the algebra values are irrelevant to `resO`. -/
def unitAlgs : Algs where
  Res := fun _ => .unit
  alg := fun _ => .unit
  ResA := fun _ _ => .unit
  algA := fun _ _ => .unit
  alg_closed := fun _ => rfl
  algA_closed := fun _ _ => rfl

/-- **`HasDtor.mu` at the class `P`.**  `[design §4.3]` -/
def HasDtorMu (B₀ : VTy) : Prop :=
  PBody B₀ ∧ (∀ B Bs, (B :: Bs) ∈ reach B₀ → HasDtor (resO unitAlgs (B :: Bs) B)) ∧
    ∀ B Bs, (B :: Bs) ∈ reach B₀ → ∀ S ∈ aIn B,
      HasDtor (.sum .unit (.tensor .unit (resO unitAlgs (B :: Bs) S)))

/-- A closed value valid at `A ⊸ R` on every list is valid at `!(A ⊸ R)`. -/
theorem valid_bang {A R : VTy} {δ : LSub} {g : Val}
    (h : ∀ ls v σ, vP A ls δ v σ → wpTS ls (.app (.val g) (.val v)) (fun ls' => vP R ls' δ) σ) :
    ∀ ls, vC true (.bang (.lolli A R)) ls δ g PMap.empty := fun _ =>
  ⟨rfl, fun ls' _ v σ τ hv hcomp => by rw [eq_of_compS_empty_left hcomp]; exact h ls' v σ hv⟩

/-- The results of `resO` at results `1` do not depend on the algebra values. -/
theorem resO_res (G : Algs) (hR : ∀ b, G.Res b = .unit) (hRA : ∀ b S, G.ResA b S = .unit)
    (Bs : Stack) : ∀ A, resO G Bs A = resO unitAlgs Bs A
  | .tvar _ => by simp [resO, hR, unitAlgs]
  | .tensor A B => by simp [resO, resO_res G hR hRA Bs A, resO_res G hR hRA Bs B]
  | .sum A B => by simp [resO, resO_res G hR hRA Bs A, resO_res G hR hRA Bs B]
  | .ref S => by simp [resO, resO_res G hR hRA Bs S]
  | .fam (.ref S) => by simp [resO, hRA, unitAlgs]
  | .mu B => by simp [resO, hR, unitAlgs]
  | .unit | .zero | .thunk _ | .imm _ _ | .mut _ _ | .box _ _ | .bang _ | .unk | .int _
  | .opq _ => rfl
  | .fam .unit | .fam (.tensor _ _) | .fam .zero | .fam (.sum _ _) | .fam (.thunk _)
  | .fam (.imm _ _) | .fam (.mut _ _) | .fam (.box _ _) | .fam (.bang _) | .fam .unk
  | .fam (.tvar _) | .fam (.mu _) | .fam (.int _) | .fam (.fam _) | .fam (.opq _) => rfl

/-- **The destructor consumes the value.**  At results `1`, with an algebra in
`𝒱⟦!(T_b⟨1⟩ ⊸ 1)⟧` per binder and `𝒱⟦!(1 ⊕ (1 ⊗ S⟨1⟩) ⊸ 1)⟧` per array binder, the root
handle runs a value of `μB₀` to `()` at the empty resource. -/
theorem dtor_spec {B₀ : VTy} (hB : PBody B₀) (G : Algs) (δ : LSub)
    (hR : ∀ b, G.Res b = .unit) (hRA : ∀ b S, G.ResA b S = .unit)
    (halg : ∀ B Bs, (B :: Bs) ∈ reach B₀ → ∀ ls,
      vC true (.bang (.lolli (resO unitAlgs (B :: Bs) B) .unit)) ls δ (G.alg (B :: Bs)) PMap.empty)
    (harr : ∀ B Bs, (B :: Bs) ∈ reach B₀ → ∀ S ∈ aIn B, ∀ ls,
      vC true (.bang (.lolli (.sum .unit (.tensor .unit (resO unitAlgs (B :: Bs) S))) .unit)) ls δ
        (G.algA (B :: Bs) S) PMap.empty)
    (w : Val) (χ : WRes) (ls : List SRec) (hv : vP (.mu B₀) ls δ w χ) :
    wpTS ls (.app (.val (hdl (reach B₀) G [B₀])) (.val w))
      (fun _ v ρ => v = .unit ∧ ρ = PMap.empty) χ := by
  have h := fold_spec hB G δ
    (fun B Bs hm ls => by
      rw [resO_res G hR hRA, hR]; exact halg B Bs hm ls)
    (fun B Bs hm S hS ls => by
      rw [resO_res G hR hRA, hRA]; exact harr B Bs hm S hS ls)
    w χ ls hv
  rw [hR] at h
  exact wpTS_mono (fun _ v ρ hv' => ⟨hv'.2, hv'.1⟩) χ h

/-! ### The test types -/

abbrev i32 : VTy := .int .w32

/-- The body of `μX. I32 ⊗ Array X`. -/
abbrev roseB : VTy := .tensor i32 (.fam (.ref (.tvar 0)))

/-- `μX. I32 ⊗ Array X`. -/
abbrev roseA : VTy := .mu roseB

/-- The inner body `1 ⊕ (Ref X ⊗ Ref Y)`: `Y` is variable `0`, `X` variable `1`. -/
abbrev nestInner : VTy := .sum .unit (.tensor (.ref (.tvar 1)) (.ref (.tvar 0)))

/-- The body of `μX. I32 ⊗ μY. 1 ⊕ (Ref X ⊗ Ref Y)`. -/
abbrev nestB : VTy := .tensor i32 (.mu nestInner)

/-- `μX. I32 ⊗ μY. 1 ⊕ (Ref X ⊗ Ref Y)`. -/
abbrev nestA : VTy := .mu nestB

theorem roseB_P : PBody roseB := by decide
theorem nestB_P : PBody nestB := by decide

/-- Both bodies are outside `FShape`: `toFShape` reads the array and the inner `μ` as leaves,
which are not closed. -/
theorem roseB_not_FShape : ¬ (toFShape roseB).WF := by
  simp [toFShape, FShape.WF, VTy.Cl]

theorem nestB_not_FShape : ¬ (toFShape nestB).WF := by
  simp [toFShape, FShape.WF, VTy.Cl]

/-- One `μ` binder; its array is an array binder. -/
theorem reach_roseB : reach roseB = [[roseB]] := by
  simp [reach, rIn]

theorem aIn_roseB : aIn roseB = [.tvar 0] := by
  simp [aIn, clB]

/-- Two `μ` binders: the root and the inner `μY`, one handle each. -/
theorem reach_nestB : reach nestB = [[nestB], [nestInner, nestB]] := by
  simp [reach, rIn, clB]

theorem aIn_nestB : aIn nestB = [] := by simp [aIn]
theorem aIn_nestInner : aIn nestInner = [] := by simp [aIn]

/-- The result types the algebras see. -/
theorem resO_roseB (G : Algs) : resO G [roseB] roseB = .tensor i32 (G.ResA [roseB] (.tvar 0)) := by
  simp [resO, clB]

theorem resO_roseS (G : Algs) : resO G [roseB] (.tvar 0) = G.Res [roseB] := by
  simp [resO]

theorem resO_nestB (G : Algs) : resO G [nestB] nestB = .tensor i32 (G.Res [nestInner, nestB]) := by
  simp [resO, clB]

theorem resO_nestInner (G : Algs) :
    resO G [nestInner, nestB] nestInner = .sum .unit (.tensor (G.Res [nestB]) (G.Res [nestInner, nestB])) := by
  simp [resO, clB]

/-- **Test 1**: the generic fold at `μX. I32 ⊗ Array X`, with its two algebras. -/
theorem roseA_fold (G : Algs) (δ : LSub)
    (hg : ∀ ls, vC true (.bang (.lolli (.tensor i32 (G.ResA [roseB] (.tvar 0))) (G.Res [roseB])))
      ls δ (G.alg [roseB]) PMap.empty)
    (ha : ∀ ls, vC true (.bang (.lolli (.sum .unit (.tensor (G.ResA [roseB] (.tvar 0))
      (G.Res [roseB]))) (G.ResA [roseB] (.tvar 0)))) ls δ (G.algA [roseB] (.tvar 0)) PMap.empty)
    (w : Val) (χ : WRes) (ls : List SRec) (hv : vP roseA ls δ w χ) :
    wpTS ls (.app (.val (hdl (reach roseB) G [roseB])) (.val w))
      (fun ls' => vP (G.Res [roseB]) ls' δ) χ := by
  refine fold_spec roseB_P G δ (fun B Bs hm => ?_) (fun B Bs hm S hS => ?_) w χ ls hv
  · rw [reach_roseB] at hm
    simp only [List.mem_singleton, List.cons.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    unfold AlgOK; rw [resO_roseB]; exact hg
  · rw [reach_roseB] at hm
    simp only [List.mem_singleton, List.cons.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rw [aIn_roseB, List.mem_singleton] at hS
    subst hS
    unfold AlgAOK; rw [resO_roseS]; exact ha

/-- **Test 2**: the generic fold at `μX. I32 ⊗ μY. 1 ⊕ (Ref X ⊗ Ref Y)`, one algebra per
binder. -/
theorem nestA_fold (G : Algs) (δ : LSub)
    (hg₀ : ∀ ls, vC true (.bang (.lolli (.tensor i32 (G.Res [nestInner, nestB])) (G.Res [nestB])))
      ls δ (G.alg [nestB]) PMap.empty)
    (hg₁ : ∀ ls, vC true (.bang (.lolli (.sum .unit (.tensor (G.Res [nestB])
      (G.Res [nestInner, nestB]))) (G.Res [nestInner, nestB]))) ls δ (G.alg [nestInner, nestB])
      PMap.empty)
    (w : Val) (χ : WRes) (ls : List SRec) (hv : vP nestA ls δ w χ) :
    wpTS ls (.app (.val (hdl (reach nestB) G [nestB])) (.val w))
      (fun ls' => vP (G.Res [nestB]) ls' δ) χ := by
  refine fold_spec nestB_P G δ (fun B Bs hm => ?_) (fun B Bs hm S hS => ?_) w χ ls hv
  · rw [reach_nestB] at hm
    simp only [List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · unfold AlgOK; rw [resO_nestB]; exact hg₀
    · unfold AlgOK; rw [resO_nestInner]; exact hg₁
  · rw [reach_nestB] at hm
    simp only [List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [aIn_nestB] at hS; simp at hS
    · rw [aIn_nestInner] at hS; simp at hS

/-! ### The destructor at the test types, every hypothesis discharged -/

/-- `g₀ = λp. let (x, u) = p in u : I32 ⊗ 1 ⊸ 1`. -/
def g₀ : Val := .lam (.letpair (.var 0) (.var 0))

/-- `g₁ = λx. case x (u. u) (p. let (a, b) = p in a) : 1 ⊕ (1 ⊗ 1) ⊸ 1`. -/
def g₁ : Val := .lam (.case (.var 0) (.var 0) (.letpair (.var 0) (.var 1)))

theorem g₀_valid (δ : LSub) : ∀ ls, vC true (.bang (.lolli (.tensor i32 .unit) .unit)) ls δ g₀ PMap.empty := by
  refine valid_bang fun ls v σ hv => ?_
  obtain ⟨x, u, hs⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, ⟨rfl, -⟩, ⟨rfl, rfl⟩⟩ := pure_sep_iff.mp hs
  rw [ResU.CompS.functional hc (ResU.comp_empty_right _)]
  refine wpTS_lolli ls _ _ _ _ ?_
  refine wpTS_tensor ls x Val.unit _ _ _ ?_
  simp only [Expr.subst]
  exact wpTS_val ls Val.unit _ _ ⟨rfl, rfl⟩

theorem g₁_valid (δ : LSub) :
    ∀ ls, vC true (.bang (.lolli (.sum .unit (.tensor .unit .unit)) .unit)) ls δ g₁ PMap.empty := by
  refine valid_bang fun ls v σ hv => ?_
  rcases hv with ⟨u, hs⟩ | ⟨p, hs⟩
  · obtain ⟨rfl, ⟨rfl, rfl⟩⟩ := pure_sep_iff.mp hs
    refine wpTS_lolli ls _ _ _ _ ?_
    refine wpTS_sum₁ ls Val.unit _ _ _ _ ?_
    simp only [Expr.subst]
    exact wpTS_val ls Val.unit _ _ ⟨rfl, rfl⟩
  · obtain ⟨rfl, hp⟩ := pure_sep_iff.mp hs
    obtain ⟨a, b, hs'⟩ := hp
    obtain ⟨rfl, σ₁, σ₂, hc, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := pure_sep_iff.mp hs'
    rw [ResU.CompS.functional hc (ResU.comp_empty_right _)]
    refine wpTS_lolli ls _ _ _ _ ?_
    refine wpTS_sum₂ ls (Val.pair Val.unit Val.unit) _ _ _ _ ?_
    simp only [Expr.subst]
    refine wpTS_tensor ls Val.unit Val.unit _ _ _ ?_
    exact wpTS_val ls Val.unit _ _ ⟨rfl, rfl⟩

/-- The destructor's algebras: `g₀` at the root, `g₁` at every other binder and every array. -/
def dtorAlgs (root : Stack) : Algs where
  Res := fun _ => .unit
  alg := fun b => if b = root then g₀ else g₁
  ResA := fun _ _ => .unit
  algA := fun _ _ => g₁
  alg_closed := fun b => by by_cases h : b = root <;> simp [h, g₀, g₁, closedAt]
  algA_closed := fun _ _ => by simp [g₁, closedAt]

/-- **Test 1, destroyed**: a value of `μX. I32 ⊗ Array X` is consumed to `()` with no cell
left. -/
theorem roseA_dtor (δ : LSub) (w : Val) (χ : WRes) (ls : List SRec) (hv : vP roseA ls δ w χ) :
    wpTS ls (.app (.val (hdl (reach roseB) (dtorAlgs [roseB]) [roseB])) (.val w))
      (fun _ v ρ => v = .unit ∧ ρ = PMap.empty) χ := by
  refine dtor_spec roseB_P (dtorAlgs [roseB]) δ (fun _ => rfl) (fun _ _ => rfl)
    (fun B Bs hm => ?_) (fun B Bs hm S hS => ?_) w χ ls hv
  · rw [reach_roseB] at hm
    simp only [List.mem_singleton, List.cons.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rw [resO_roseB]
    simpa [dtorAlgs, unitAlgs] using g₀_valid δ
  · rw [reach_roseB] at hm
    simp only [List.mem_singleton, List.cons.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rw [aIn_roseB, List.mem_singleton] at hS
    subst hS
    rw [resO_roseS]
    simpa [dtorAlgs, unitAlgs] using g₁_valid δ

/-- **Test 2, destroyed**: a value of `μX. I32 ⊗ μY. 1 ⊕ (Ref X ⊗ Ref Y)` is consumed to `()`
with no cell left. -/
theorem nestA_dtor (δ : LSub) (w : Val) (χ : WRes) (ls : List SRec) (hv : vP nestA ls δ w χ) :
    wpTS ls (.app (.val (hdl (reach nestB) (dtorAlgs [nestB]) [nestB])) (.val w))
      (fun _ v ρ => v = .unit ∧ ρ = PMap.empty) χ := by
  refine dtor_spec nestB_P (dtorAlgs [nestB]) δ (fun _ => rfl) (fun _ _ => rfl)
    (fun B Bs hm => ?_) (fun B Bs hm S hS => ?_) w χ ls hv
  · rw [reach_nestB] at hm
    simp only [List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [resO_nestB]
      simpa [dtorAlgs, unitAlgs] using g₀_valid δ
    · rw [resO_nestInner]
      simpa [dtorAlgs, unitAlgs] using g₁_valid δ
  · rw [reach_nestB] at hm
    simp only [List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [aIn_nestB] at hS; simp at hS
    · rw [aIn_nestInner] at hS; simp at hS

/-- The two test types satisfy the restated `HasDtor.mu`. -/
theorem roseB_hasDtorMu : HasDtorMu roseB := by
  refine ⟨roseB_P, fun B Bs hm => ?_, fun B Bs hm S hS => ?_⟩
  · rw [reach_roseB] at hm
    simp only [List.mem_singleton, List.cons.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rw [resO_roseB]; exact .tensor .int .unit
  · rw [reach_roseB] at hm
    simp only [List.mem_singleton, List.cons.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    rw [aIn_roseB, List.mem_singleton] at hS
    subst hS
    rw [resO_roseS]; exact .sum .unit (.tensor .unit .unit)

theorem nestB_hasDtorMu : HasDtorMu nestB := by
  refine ⟨nestB_P, fun B Bs hm => ?_, fun B Bs hm S hS => ?_⟩
  · rw [reach_nestB] at hm
    simp only [List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [resO_nestB]; exact .tensor .int .unit
    · rw [resO_nestInner]; exact .sum .unit (.tensor .unit .unit)
  · rw [reach_nestB] at hm
    simp only [List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [aIn_nestB] at hS; simp at hS
    · rw [aIn_nestInner] at hS; simp at hS

end BoCa.Fig16.LogRel.Core.NestedFold

end
