import Core.TreeSemK

/-!
# Continuation types at the tree: instances  `[spec §62]`

Every hypothesis of `STy.kontBox_resume_after` discharged, at a lend at depth 1 and at a lend
nested two deep (depth 3), and `STy.not_kontBox_of_view` at the same `κ` boxed at its lend's own
lifetime and at the root.

The tree is the chain `0 ⊐ 1 ⊐ 2 ⊐ ⋯` (`chainP`): the lifetime `α` is nested inside every
lifetime below it as a number. `κ = λy. K[y]` with `K = [·]; ℓ` (`kontV`), captured at a stop
owning no records, its share the view `ℓ ↦ imm({α}, (), ∅)` of a lend of a unit cell at `ℓ`
(`viewR`) whose record is in the stop list. The stop list also holds records `κ` does not read;
the resume list drops them (ended by another branch) and adds one opened since, so it is not a
re-reading of the stop list (`¬ SRecsRR`), and `KeepRel` holds. Boxed at `α + 1`, strictly inside
the lend, `κ` is a value of `[@α+1] U (1 ⊸ F (Imm @α 1))` there and is resumed; boxed at `α` or at
the root it is not of that type.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.KEx
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont)

/-! ### `κ = λy. K[y]` -/

/-- `κ = λy. K[y]`, the resume branch of the continuation `[op]` hands a clause. -/
def kontV (K : Kont) : Val := Val.lam ((K.shift 1 0).plug (.var 0))

/-- **`κ a` steps to `K[a]`, and only there.** `STy.kont_of_share`'s `hκ` at `kontV`. -/
theorem kontV_step (K : Kont) (a : Val) (μ : BoCa.BoLo.Heap) :
    Step1Only (ℍ := ℍ) μ (.app (.val (kontV K)) (.val a)) μ (K.plug (.val a)) := by
  have h := step1Only_plug (ℍ := ℍ) (Head.beta μ ((K.shift 1 0).plug (.var 0)) a) rfl Kont.hole
  rw [plug_shift_subst 0 K 0 0 a (.var 0) le_rfl le_rfl, Kont.shift_zero] at h
  exact h

/-! ### The chain, the world, the view -/

/-- The chain `0 ⊐ 1 ⊐ 2 ⊐ ⋯`: each lifetime's parent is the one before it. -/
def chainP : ParentFn where
  par n := n - 1
  rank n := n
  par_zero := rfl
  rank_lt n hn := by omega

theorem chainP_inAlloc : chainP.InAlloc := fun n hn => by show n - 1 < n; omega

theorem chainP_anc (a : Nat) : ∀ k, chainP.Anc (a + k) a
  | 0 => .refl a
  | k + 1 => by
      refine .up ?_
      show chainP.Anc (a + (k + 1) - 1) a
      rw [show a + (k + 1) - 1 = a + k by omega]
      exact chainP_anc a k

/-- The world at the chain: no `mut` locations. -/
def wCh : TWd := ⟨chainP, fun _ => none, fun R _ _ => R⟩

/-- A lifetime as a node of the chain. -/
abbrev lf (n : Nat) : Life := OrderDual.toDual n

theorem lt_of_lt {a b : Nat} (h : a < b) : wCh.K.lt (lf b) (lf a) := by
  refine ⟨?_, fun e => by have := congrArg OrderDual.ofDual e; simp at this; omega⟩
  show chainP.Anc b a
  have := chainP_anc a (b - a)
  rwa [show a + (b - a) = b by omega] at this

theorem not_lt_of_le {a b : Nat} (h : b ≤ a) : ¬ wCh.K.lt (lf b) (lf a) := by
  rintro ⟨h₁, h₂⟩
  have := ParentFn.Anc.le chainP_inAlloc (show chainP.Anc b a from h₁)
  exact h₂ (by rw [show a = b by omega])

theorem empty_inStratum {K : WCactus} (s : TSet) : ResUT.InStratum s (PMap.empty : TRes K) :=
  fun _ _ e => by cases e

theorem empty_cov (Θ : CodeTy) (K : WCactus) : CovR (sem Θ) K (PMap.empty : TRes K) :=
  fun _ _ e => by cases e

/-- The view `imm({α}, (), ∅)` of a lend of a unit cell. -/
def viewI (α : Life) : TImm wCh.K :=
  ⟨TSet.single α, Val.unit, ResST.toRes ⟨PMap.empty, empty_inStratum _⟩⟩

theorem viewI_res (α : Life) : (viewI α).res = PMap.empty := ImmT.res_toRes _

/-- `κ`'s share: `ℓ ↦ imm({α}, (), ∅)`. -/
def viewR (l : BoCa.Loc) (α : Life) : TRes wCh.K := PMap.sng l (.imm (viewI α))

/-- The record of a lend of a unit cell at `ℓ`. -/
def recU (l : BoCa.Loc) : FrameRecT wCh.K := ⟨l, Val.unit, PMap.empty, KTy.unit⟩

theorem viewR_cov (l : BoCa.Loc) (α : Life) : CovR (sem wCh.Θ) wCh.K (viewR l α) := by
  intro m ψ e
  rw [viewR, PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  exact Cov.imm _ _ (by rw [viewI_res]; exact empty_cov _ _)

theorem viewR_inStratum {l : BoCa.Loc} {a d : Nat} (h : a < d) :
    (viewR l (lf a)).InStratum (TSet.single (lf d)) := by
  intro m ψ e
  rw [viewR, PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  intro x hx y hy
  have hx' : x = lf d := by simpa [TSet.single] using hx
  have hy' : y = lf a := by simpa [viewI, TSet.single] using hy
  subst hx'; subst hy'
  exact lt_of_lt h

/-- **The share reads exactly the record of its own lend.** -/
theorem relFT_viewR_iff {l m : BoCa.Loc} {α : Life} : RelFT (recU m) (viewR l α) ↔ m = l := by
  constructor
  · rintro ⟨x, hf, hx⟩
    have hxm : x = m := by
      rcases hx with hx | ⟨p, S, u, hc⟩
      · exact hx
      · exfalso
        cases hc with
        | one _ e => simp [recU] at e
        | step _ e _ => simp [recU] at e
    have hxl : x = l := by
      cases hf with
      | imm e _ =>
          rw [viewR, PMap.sng_get] at e
          split_ifs at e with h
          exact h
      | inImm e _ hd =>
          rw [viewR, PMap.sng_get] at e
          split_ifs at e with h
          cases e
          exfalso
          change InDomT (viewI α).res x at hd
          rw [viewI_res] at hd
          cases hd with
          | top e => simp at e
          | wit e _ _ => simp at e
      | inMut e k _ =>
          rw [viewR, PMap.sng_get] at e
          split_ifs at e with h
          cases e
          cases k
    exact hxm.symm.trans hxl
  · rintro rfl
    exact ⟨m, FrzT.imm (ψ := CellUT.imm (viewI α)) (by simp [viewR, PMap.sng_get]) rfl,
      Or.inl rfl⟩

/-! ### The stop's share -/

/-- The empty table. -/
def tbE : TableT := opTableT fun _ _ => none

theorem tbE_local : tbE.Local := opTableT_local _

theorem tbE_down : tbE.Down := opTableT_down fun _ _ _ h => by cases h

/-- A must-resume operation answering `()`. -/
def enU : OpEntT where
  q := .lin
  abort := false
  PA _ _ _ _ _ := True
  PBv _ k w ls a σ := STy.unit.P k w ls a σ
  fin := false
  fd _ _ _ _ := True
  oc _ _ := True

/-- `K = [·]; ℓ`: resumed at `()`, it returns the view. -/
def kRet (l : BoCa.Loc) : Kont := .seq .hole (.val (Val.loc l))

/-- `κ`'s result: `Imm @α 1`. -/
def τR (α : Life) : STy := STy.imm α STy.unit

theorem viewR_res {n : Nat} {l : BoCa.Loc} {α : Life} (ls : List (SRecT wCh.K)) :
    (τR α).P n wCh ls (Val.loc l) (viewR l α) :=
  ⟨l, viewI α, rfl, rfl, fun x hx => by
      simp only [viewI, TSet.single, Finset.mem_singleton] at hx
      subst hx; exact wCh.K.refl _,
    rfl, viewI_res α⟩

/-- **A stop's share holding the view**, at every stop index and stop list: resumed at `()` at
every extension and list keeping the records it reads, `K[()]` steps to `ℓ`, a value of
`Imm @α 1` over the re-read view. -/
theorem share_viewR (l : BoCa.Loc) (α : Life) (k : Nat) (ls : List (SRecT wCh.K)) :
    contShareT enU (fun _ _ => True) k wCh ls [] (kRet l) Val.unit
      (cerwpTC (ℍ := ℍ) tbE (postOf (τR α)) (fun _ _ => True) k) (viewR l α) := by
  unfold contShareT
  refine ⟨fun h => by simp [enU] at h, fun w' ρ' ls' O' hE hr hk hO => ?_⟩
  cases hO
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun h => absurd rfl h⟩
  obtain ⟨rfl, rfl⟩ := hB
  have e : σ' = ρ' := ResUT.CompS.functional hcσ (G.comp_empty_right ρ')
  simp only [cerwpTC, hk', if_true]
  rw [e]
  have hv' := (τR α).mono k' wCh w' ls ls' _ _ ρ' hE hr hk (viewR_cov l α) (viewR_res ls)
  cases k' with
  | zero => exact cerwpT_zero
  | succ j =>
      refine cerwpT_step tbE_local
        (fun μ => step1Only_plug (ℍ := ℍ) (Head.seq μ (.val (Val.loc l))) rfl Kont.hole) ?_
      refine cerwpT_val fun w₀ ρ₀ ls₀ O₀ hE₀ hr₀ hl₀ _ => ?_
      exact (τR α).down _ _ _ _ _ ((τR α).mono _ w' w₀ ls' ls₀ _ ρ' ρ₀ hE₀ hr₀
        (KeepRel.of_srecsRR hl₀ ρ') hr.cov hv')

/-! ### The hardest case, discharged -/

/-- **`κ` holding a view of the lend at `α`, boxed at `α + 1`, carried to a list that drops the
records it does not read and adds one, is a value of its type there and is resumed.** Every
hypothesis of `STy.kontBox_resume_after` discharged; uniform in `α`, the instances below fix
the depth. -/
theorem kontBox_view {l : BoCa.Loc} {a : Nat} {ls ls' : List (SRecT wCh.K)} {k n : Nat}
    (hn : n < k) (hk : KeepRel wCh.Θ ls ls' (viewR l (lf a))) :
    (STy.kontBox (lf (a + 1)) STy.unit
        (SCmp.ret (ℍ := ℍ) tbE tbE_local tbE_down (fun _ _ => True) (fdNil enU Val.unit fun _ _ => True)
          (τR (lf a)))).P n wCh ls' (kontV (kRet l)) (viewR l (lf a)) ∧
      ∀ (b : Val) (ρa σ : TRes wCh.K), ResUT.CompS (viewR l (lf a)) ρa σ →
        STy.unit.P n wCh ls' b ρa →
        cerwpT (ℍ := ℍ) tbE (postOf (τR (lf a))) (fun _ _ => True) (fdNil enU Val.unit fun _ _ => True) n
          wCh ls'
          [] (.app (.val (kontV (kRet l))) (.val b)) σ :=
  STy.kontBox_resume_after tbE_local tbE_down (kontV_step (kRet l)) (fun _ _ _ _ _ h => h)
    (share_viewR l (lf a) k ls) (viewR_inStratum (Nat.lt_succ_self a)) (viewR_cov l (lf a))
    (TWd.Ext.refl _ _) (RR.refl (viewR_cov l (lf a))) hk hn

theorem recRR_refl (l : BoCa.Loc) : RecRR wCh.Θ (recU l) (recU l) :=
  RecRR.refl (empty_cov _ _)

/-- **Depth 1.** The view of a lend at `1` (loc `0`); the stop list also holds another branch's
lend at loc `1`, which it ends; the resume list holds a lend at loc `2` opened since. -/
def lsD1 : List (SRecT wCh.K) := [(recU 0, lf 1), (recU 1, lf 1)]
def lsD1' : List (SRecT wCh.K) := [(recU 0, lf 1), (recU 2, lf 2)]

theorem keep_d1 : KeepRel wCh.Θ lsD1 lsD1' (viewR 0 (lf 1)) := by
  intro r hr hrel
  simp only [lsD1, rsOfT, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨recU 0, by simp [lsD1', rsOfT], recRR_refl 0⟩
  · exact absurd (relFT_viewR_iff.mp hrel) (by decide)

/-- The resume list is not a re-reading of the stop list. -/
theorem not_rr_d1 : ¬ SRecsRR wCh.Θ lsD1 lsD1' := by
  intro h
  cases h with
  | cons _ t =>
      cases t with
      | cons h₂ _ => exact absurd h₂.1.1 (by decide)

theorem kontBox_depth1 {k n : Nat} (hn : n < k) :
    (STy.kontBox (lf 2) STy.unit
        (SCmp.ret (ℍ := ℍ) tbE tbE_local tbE_down (fun _ _ => True) (fdNil enU Val.unit fun _ _ => True)
          (τR (lf 1)))).P n wCh lsD1' (kontV (kRet 0)) (viewR 0 (lf 1)) :=
  (kontBox_view (ℍ := ℍ) (k := k) hn keep_d1).1

/-- **Depth 3: a view of a lend nested two deep.** The lends at `1` (loc `1`) and `2` (loc `2`)
enclose the lend at `3` (loc `0`) whose view `κ` holds; another branch's lend at `4` (loc `5`)
is ended and one at loc `6` opened. -/
def lsD3 : List (SRecT wCh.K) := [(recU 1, lf 1), (recU 2, lf 2), (recU 0, lf 3), (recU 5, lf 4)]
def lsD3' : List (SRecT wCh.K) := [(recU 1, lf 1), (recU 2, lf 2), (recU 0, lf 3), (recU 6, lf 4)]

theorem keep_d3 : KeepRel wCh.Θ lsD3 lsD3' (viewR 0 (lf 3)) := by
  intro r hr hrel
  simp only [lsD3, rsOfT, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact absurd (relFT_viewR_iff.mp hrel) (by decide)
  · exact absurd (relFT_viewR_iff.mp hrel) (by decide)
  · exact ⟨recU 0, by simp [lsD3', rsOfT], recRR_refl 0⟩
  · exact absurd (relFT_viewR_iff.mp hrel) (by decide)

theorem not_rr_d3 : ¬ SRecsRR wCh.Θ lsD3 lsD3' := by
  intro h
  cases h with
  | cons _ t => cases t with
    | cons _ t => cases t with
      | cons _ t => cases t with
        | cons h₄ _ => exact absurd h₄.1.1 (by decide)

theorem kontBox_depth3 {k n : Nat} (hn : n < k) :
    (STy.kontBox (lf 4) STy.unit
        (SCmp.ret (ℍ := ℍ) tbE tbE_local tbE_down (fun _ _ => True) (fdNil enU Val.unit fun _ _ => True)
          (τR (lf 3)))).P n wCh lsD3' (kontV (kRet 0)) (viewR 0 (lf 3)) :=
  (kontBox_view (ℍ := ℍ) (k := k) hn keep_d3).1

/-! ### Rules out, at the same `κ` -/

/-- **`κ` boxed at its lend's own lifetime is not of its type**, at every index, world and list. -/
theorem not_kontBox_at_lend {a n : Nat} {ls : List (SRecT wCh.K)} {τB : STy} {C : SCmp} :
    ¬ (STy.kontBox (lf a) τB C).P n wCh ls (kontV (kRet 0)) (viewR 0 (lf a)) :=
  STy.not_kontBox_of_view (l := 0) (i := viewI (lf a)) (by simp [viewR, PMap.sng_get])
    (Finset.mem_singleton_self _) (not_lt_of_le le_rfl)

/-- **`κ` boxed at the root, which outlives the lend, is not of its type.** -/
theorem not_kontBox_at_root {a n : Nat} {ls : List (SRecT wCh.K)} {τB : STy} {C : SCmp} :
    ¬ (STy.kontBox (lf 0) τB C).P n wCh ls (kontV (kRet 0)) (viewR 0 (lf a)) :=
  STy.not_kontBox_of_view (l := 0) (i := viewI (lf a)) (by simp [viewR, PMap.sng_get])
    (Finset.mem_singleton_self _) (not_lt_of_le (Nat.zero_le a))

/-! ### A list-free reading admits a stuck thunk -/

/-- **At the empty list, a term that never steps, over the view, is a run** (`cerwpT_nil_of_imm`):
a thunk type running its thunks at `[]` would hold of `λ_. () ()` holding the view. -/
theorem nilRun_stuck {Q : TPostV} {Fb F : TFrame} {n : Nat} {a : Nat} :
    cerwpT (ℍ := ℍ) tbE Q Fb F n wCh [] [] BoCa.BoLo.stuckE (viewR 0 (lf a)) :=
  cerwpT_nil_of_imm (ψ := CellUT.imm (viewI (lf a))) (l := 0) (by simp [viewR, PMap.sng_get]) rfl

end BoCa.Fig16.Tree.Wp.KEx

end
