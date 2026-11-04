import Core.TreeSemK
import Core.TreeLend
import Support.Model.Tree.KSemGraft

/-!
# Continuation types at the tree: instances  `[spec §62]`

Every hypothesis of `STy.kontBox_resume_after` discharged at a proper extension of the tree, at a
lend at depth 1 and at a view nested three deep; `STy.not_kontBox_of_view` at the same `κ` boxed at
its lend's own lifetime and at the root; `STy.reread` on the nested view; and `STy.mut_reread` and
`RC.mut_extends` on round 7's `mut` cell at codes.

**The extension.** Before (`dP₀`), the lifetimes `0 ⊐ 1 ⊐ 2 ⊐ 3 ⊐ 4` are a chain and `5` is a bare
child of the root. After (`dP₁`), `5` is a child of `3`: another branch opened a lend inside the
lend at `3` (a fresh child, `ParentFn.Graft` at `5`). The extension adds the facts `5 ⊏ 3 ⊏ 2 ⊏ 1`
and removes none (`dExt`); it is proper (`dExt_proper`).

**The configuration.** `κ = λy. K[y]` with `K = [·]; ℓ` (`kontV`), captured at a stop owning no
records. Its share is a view of the lend whose record is in the stop list. The stop list also
holds a record `κ` does not read, which the resume list leaves out (another branch ended it); the
resume list adds a record at `5`, the lifetime the extension opened. So the resume list is not a
re-reading of the stop list (`¬ SRecsRR`), and `KeepRel` holds.

* Depth 1 (`kontBox_depth1`): the view `ℓ₀ ↦ imm({1}, (), ∅)` of a lend of a unit cell, boxed
  at `2`.
* Depth 3 (`kontBox_depth3`): `0 ↦ imm({3}, 2, 2 ↦ imm({2}, 1, 1 ↦ imm({1}, (), ∅)))`, a view
  whose witness holds the views of the two enclosing lends, boxed at `4`. The share reads the
  records of all three lends (`relFT_d3`) and not the fourth (`not_relFT_d3`); `KeepRel` re-reads
  the three at the new tree, their escrows re-read, and drops the fourth.

**What the instances fix.** The operation table is empty (`tbE`), so a stop of the resumed run is
refused; the operation's entry is must-resume (`q = .lin`, so its cancel branch is vacuous) and
answers `()` (`enU`, answer type `1`). The frame conditions are `True` (`Fb`) and `fdNil enU () Fb`.
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

/-! ### Trees -/

/-- The chain `0 ⊐ 1 ⊐ 2 ⊐ ⋯`: each lifetime's parent is the one before it. -/
def chainP : ParentFn where
  par n := n - 1
  rank n := n
  par_zero := rfl
  rank_lt n hn := by omega

/-- A lifetime as a node of a tree. -/
abbrev lf (n : Nat) : Life := OrderDual.toDual n

/-- Before the extension: the chain `0 ⊐ 1 ⊐ 2 ⊐ 3 ⊐ 4`, every other node a bare child of the
root. -/
def dP₀ : ParentFn where
  par n := if n ≤ 4 then n - 1 else 0
  rank n := if n ≤ 4 then n else 1
  par_zero := rfl
  rank_lt n hn := by
    show (if (if n ≤ 4 then n - 1 else 0) ≤ 4 then (if n ≤ 4 then n - 1 else 0) else 1) <
      (if n ≤ 4 then n else 1)
    split_ifs <;> omega

/-- After the extension: `5` a child of `3`, the lend another branch opened inside the lend at
`3`. -/
def dP₁ : ParentFn where
  par n := if n = 5 then 3 else if n ≤ 4 then n - 1 else 0
  rank n := if n = 5 then 4 else if n ≤ 4 then n else 1
  par_zero := rfl
  rank_lt n hn := by
    show (if (if n = 5 then 3 else if n ≤ 4 then n - 1 else 0) = 5 then 4 else
      if (if n = 5 then 3 else if n ≤ 4 then n - 1 else 0) ≤ 4 then
        (if n = 5 then 3 else if n ≤ 4 then n - 1 else 0) else 1) <
      (if n = 5 then 4 else if n ≤ 4 then n else 1)
    by_cases h5 : n = 5
    · subst h5; decide
    · by_cases h4 : n ≤ 4
      · simp only [h5, h4, if_false, if_true]
        split_ifs <;> omega
      · simp only [h5, h4, if_false]
        decide

theorem dP₀_inAlloc : dP₀.InAlloc := fun n hn => by
  show (if n ≤ 4 then n - 1 else 0) < n
  split_ifs <;> omega

theorem dP₁_inAlloc : dP₁.InAlloc := fun n hn => by
  show (if n = 5 then 3 else if n ≤ 4 then n - 1 else 0) < n
  split_ifs <;> omega

/-- `dP₁` is `dP₀` with `5`'s parent moved to `3`. -/
theorem dGraft : dP₀.Graft dP₁ 5 3 :=
  ⟨rfl, fun n hn => by show (if n = 5 then 3 else _) = _; rw [if_neg hn]; rfl⟩

theorem anc_chain {P : ParentFn} (hP : ∀ n, n ≠ 0 → n ≤ 4 → P.par n = n - 1) :
    ∀ k a, a + k ≤ 4 → P.Anc (a + k) a
  | 0, a, _ => .refl a
  | k + 1, a, h => by
      refine .up ?_
      rw [hP (a + (k + 1)) (by omega) h, show a + (k + 1) - 1 = a + k by omega]
      exact anc_chain hP k a (by omega)

theorem lt_chain {P : ParentFn} (hP : ∀ n, n ≠ 0 → n ≤ 4 → P.par n = n - 1) {a b : Nat}
    (h : a < b) (hb : b ≤ 4) : (WCactus.ofParent P).lt (lf b) (lf a) := by
  refine ⟨?_, fun e => by have := congrArg OrderDual.ofDual e; simp at this; omega⟩
  show P.Anc b a
  have := anc_chain hP (b - a) a (by omega)
  rwa [show a + (b - a) = b by omega] at this

/-- In a tree whose parents are opened first, no lifetime lies strictly inside one opened after
it. -/
theorem not_lt_of_le {P : ParentFn} (hP : P.InAlloc) {a b : Nat} (h : b ≤ a) :
    ¬ (WCactus.ofParent P).lt (lf b) (lf a) := by
  rintro ⟨h₁, h₂⟩
  have := ParentFn.Anc.le hP (show P.Anc b a from h₁)
  exact h₂ (by rw [show a = b by omega])

theorem dP₀_par {n : Nat} (h : n ≤ 4) : dP₀.par n = n - 1 := if_pos h

theorem dP₁_par {n : Nat} (h : n ≤ 4) : dP₁.par n = n - 1 := by
  show (if n = 5 then 3 else if n ≤ 4 then n - 1 else 0) = n - 1
  rw [if_neg (by omega), if_pos h]

/-- The world before the extension: no `mut` locations. -/
def wD₀ : TWd := ⟨dP₀, fun _ => none, tmplT _ (fun _ => none)⟩

/-- The world after it. -/
def wD₁ : TWd := ⟨dP₁, fun _ => none, tmplT _ (fun _ => none)⟩

theorem lt₀ {a b : Nat} (h : a < b) (hb : b ≤ 4) : wD₀.K.lt (lf b) (lf a) :=
  lt_chain (fun _ _ h => dP₀_par h) h hb

theorem lt₁ {a b : Nat} (h : a < b) (hb : b ≤ 4) : wD₁.K.lt (lf b) (lf a) :=
  lt_chain (fun _ _ h => dP₁_par h) h hb

/-- **The extension keeps every nesting**: the graft's capture point, the root, is above `3`, and
`3` is not inside `5` (`ParentFn.graft_mono`). -/
theorem dExt : wD₀.K.Ext wD₁.K := fun {_ _} h =>
  ⟨ParentFn.graft_mono dGraft (dP₀.anc_zero 3)
    (fun h => by have := ParentFn.Anc.le dP₀_inAlloc h; omega) h.1, h.2⟩

/-- **The extension is proper**: `5` lies inside `3` after it and not before. -/
theorem dExt_proper : wD₁.K.lt (lf 5) (lf 3) ∧ ¬ wD₀.K.lt (lf 5) (lf 3) := by
  refine ⟨⟨?_, fun e => by have := congrArg OrderDual.ofDual e; simp at this⟩, ?_⟩
  · show dP₁.Anc 5 3
    exact .up (.refl 3)
  · rintro ⟨h, -⟩
    change dP₀.Anc 5 3 at h
    cases h with
    | up h =>
        change dP₀.Anc 0 3 at h
        have := ParentFn.Anc.le dP₀_inAlloc h
        omega

theorem extD (ρ : TRes wD₀.K) : wD₀.Ext wD₁ ρ := ⟨dExt, fun _ _ => rfl⟩

/-! ### Views -/

theorem empty_inStratum {K : WCactus} (s : TSet) : ResUT.InStratum s (PMap.empty : TRes K) :=
  fun _ _ e => by cases e

theorem empty_cov (Θ : CodeTy) (K : WCactus) : CovR (sem Θ) K (PMap.empty : TRes K) :=
  fun _ _ e => by cases e

/-- The view `imm({α}, (), ∅)` of a lend of a unit cell, at any tree. -/
def viewI {K : WCactus} (α : Life) : TImm K :=
  ⟨TSet.single α, Val.unit, ResST.toRes ⟨PMap.empty, empty_inStratum _⟩⟩

theorem viewI_res {K : WCactus} (α : Life) : (viewI (K := K) α).res = PMap.empty :=
  ImmT.res_toRes _

/-- `ℓ ↦ imm({α}, (), ∅)`: the view a lend's opening hands out (`viewRes`). -/
def viewR {K : WCactus} (l : BoCa.Loc) (α : Life) : TRes K := PMap.sng l (.imm (viewI α))

theorem viewR_eq {K : WCactus} (l : BoCa.Loc) (α : Life) : viewR (K := K) l α = viewRes α l := rfl

/-- A single `imm` cell over a covered witness is covered. -/
theorem cov_sngImm {Θ : CodeTy} {K : WCactus} {l : BoCa.Loc} {i : TImm K}
    (h : CovR (sem Θ) K i.res) : CovR (sem Θ) K (PMap.sng l (.imm i)) := by
  intro m ψ e
  rw [PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  exact Cov.imm _ _ h

theorem viewR_cov {Θ : CodeTy} {K : WCactus} (l : BoCa.Loc) (α : Life) :
    CovR (sem Θ) K (viewR l α) :=
  cov_sngImm (by rw [viewI_res]; exact empty_cov _ _)

/-- A single `imm` cell lies in `Res_{d}` when `d` lies strictly inside each of its lifetimes. -/
theorem sngImm_inStratum {K : WCactus} {l : BoCa.Loc} {i : TImm K} {d : Life}
    (h : ∀ y ∈ i.ls.set, K.lt d y) :
    ResUT.InStratum (TSet.single d) (PMap.sng l (.imm i) : TRes K) := by
  intro m ψ e
  rw [PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  intro x hx y hy
  have hx' : x = d := by simpa [TSet.single] using hx
  subst hx'
  exact h y hy

theorem viewR_inStratum {K : WCactus} {l : BoCa.Loc} {α d : Life} (h : K.lt d α) :
    ResUT.InStratum (TSet.single d) (viewR (K := K) l α) :=
  sngImm_inStratum (i := viewI α) fun y hy => by
    have hy' : y = α := by simpa [viewI, TSet.single] using hy
    exact hy' ▸ h

/-- A single `imm` cell re-read: the same lifetimes and value, the witness re-read. -/
theorem rr_sngImm {Θ : LocTy} {K K' : WCactus} {l : BoCa.Loc} {i : TImm K} {i' : TImm K'}
    (hs : i'.ls = i.ls) (hv : i'.v = i.v) (hr : RR Θ i.res i'.res) :
    RR Θ (PMap.sng l (.imm i)) (PMap.sng l (.imm i')) :=
  RR.sng (RC.imm l i i' hs hv hr.1 hr.2)

/-! ### What a single `imm` cell freezes -/

theorem inDom_sng {K : WCactus} {l m : BoCa.Loc} {ψ : TCell K} (h : InDomT (PMap.sng l ψ) m) :
    m = l ∨ InDomT ψ.wit m := by
  cases h with
  | top e =>
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      exact Or.inl hm
  | wit e _ hd =>
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      cases e
      exact Or.inr hd

theorem not_inDom_empty {K : WCactus} {m : BoCa.Loc} : ¬ InDomT (PMap.empty : TRes K) m := by
  intro h
  cases h with
  | top e => simp at e
  | wit e _ _ => simp at e

/-- A location frozen in `ℓ ↦ imm(…, χ)` is `ℓ` or lies inside `χ`. -/
theorem frz_sngImm {K : WCactus} {l m : BoCa.Loc} {i : TImm K}
    (h : FrzT (PMap.sng l (.imm i)) m) : m = l ∨ InDomT i.res m := by
  cases h with
  | imm e _ =>
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      exact Or.inl hm
  | inImm e _ hd =>
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      cases e
      exact Or.inr hd
  | inMut e k _ =>
      rw [PMap.sng_get] at e
      split_ifs at e with hm
      cases e
      cases k

/-- A place `Coh` looks for a lend's record is the lent location. -/
theorem relAt_lendRec {K : WCactus} {l m : BoCa.Loc} (h : RelAtT (lendRec (K := K) l) m) :
    m = l := by
  rcases h with h | ⟨p, S, u, hc⟩
  · exact h
  · exfalso
    cases hc with
    | one _ e => simp [lendRec] at e
    | step _ e _ => simp [lendRec] at e

/-- **The view reads exactly the record of its own lend.** -/
theorem relFT_viewR_iff {K : WCactus} {l m : BoCa.Loc} {α : Life} :
    RelFT (lendRec (K := K) m) (viewR l α) ↔ m = l := by
  constructor
  · rintro ⟨x, hf, hx⟩
    rcases frz_sngImm hf with h | h
    · exact (relAt_lendRec hx).symm.trans h
    · rw [viewI_res] at h; exact absurd h not_inDom_empty
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

/-- `K = [·]; ℓ`: resumed at `()`, it returns `ℓ`. -/
def kRet (l : BoCa.Loc) : Kont := .seq .hole (.val (Val.loc l))

/-- The base frame condition of the instances. -/
abbrev Fb : TFrame := fun _ _ => True

/-- `F A` at the instances' table and frame conditions. -/
abbrev cRet (τ : STy) : SCmp :=
  SCmp.ret (ℍ := ℍ) tbE tbE_local tbE_down Fb (fdNil enU Val.unit Fb) τ

/-- **A stop's share holding a value of `A` at `ℓ`**, at every stop index and stop list: resumed
at `()` at every extension and list keeping the records it reads, `K[()]` steps to `ℓ`, a value
of `A` over the re-read share. At any world. -/
theorem share_val {τ : STy} {w : TWd} {l : BoCa.Loc} {ρ : TRes w.K} (hc : CovR (sem w.Θ) w.K ρ)
    (hv : ∀ n ls, τ.P n w ls (Val.loc l) ρ) (k : Nat) (ls : List (SRecT w.K)) :
    contShareT enU Fb k w ls [] (kRet l) Val.unit
      (cerwpTC (ℍ := ℍ) tbE (postOf τ) Fb k) ρ := by
  unfold contShareT
  refine ⟨fun h => by simp [enU] at h, fun w' ρ' ls' O' hE hr hk hO => ?_⟩
  cases hO
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun h => absurd rfl h⟩
  obtain ⟨rfl, rfl⟩ := hB
  have e : σ' = ρ' := ResUT.CompS.functional hcσ (G.comp_empty_right ρ')
  simp only [cerwpTC, hk', if_true]
  rw [e]
  have hv' := τ.mono k' w w' ls ls' _ _ ρ' hE hr hk hc (hv k' ls)
  cases k' with
  | zero => exact cerwpT_zero
  | succ j =>
      refine cerwpT_step tbE_local
        (fun μ => step1Only_plug (ℍ := ℍ) (Head.seq μ (.val (Val.loc l))) rfl Kont.hole) ?_
      refine cerwpT_val fun w₀ ρ₀ ls₀ O₀ hE₀ hr₀ hl₀ _ => ?_
      exact τ.down _ _ _ _ _ (τ.mono _ w' w₀ ls' ls₀ _ ρ' ρ₀ hE₀ hr₀
        (KeepRel.of_srecsRR hl₀ ρ') hr.cov hv')

/-- `κ`'s result at depth 1: `Imm @α 1`. -/
def τR (α : Life) : STy := STy.imm α STy.unit

theorem le_single {K : WCactus} {a : Life} : ∀ x ∈ (TSet.single a).set, K.le a x := fun x hx => by
  simp only [TSet.single, Finset.mem_singleton] at hx
  subst hx; exact K.refl _

theorem viewR_val {n : Nat} {w : TWd} {l : BoCa.Loc} {α : Life} (ls : List (SRecT w.K)) :
    (τR α).P n w ls (Val.loc l) (viewR l α) :=
  ⟨l, viewI α, rfl, rfl, le_single, rfl, viewI_res α⟩

/-- **A stop's share holding the view**, at every world, stop index and stop list. -/
theorem share_viewR (w : TWd) (l : BoCa.Loc) (α : Life) (k : Nat) (ls : List (SRecT w.K)) :
    contShareT enU Fb k w ls [] (kRet l) Val.unit
      (cerwpTC (ℍ := ℍ) tbE (postOf (τR α)) Fb k) (viewR l α) :=
  share_val (viewR_cov l α) (fun _ ls => viewR_val ls) k ls

/-! ### Depth 1, at the extension -/

/-- The stop list: the lend at `1` of `ℓ₀`, whose view `κ` holds, and another branch's lend of
`ℓ₁`. -/
def lsD1 (l₀ l₁ : BoCa.Loc) : List (SRecT wD₀.K) := [(lendRec l₀, lf 1), (lendRec l₁, lf 4)]

/-- The resume list: `ℓ₁`'s lend ended, a lend of `ℓ₂` opened at `5`, the lifetime the extension
opened. -/
def lsD1' (l₀ l₂ : BoCa.Loc) : List (SRecT wD₁.K) := [(lendRec l₀, lf 1), (lendRec l₂, lf 5)]

theorem keep_d1 {l₀ l₁ l₂ : BoCa.Loc} (h : l₁ ≠ l₀) :
    KeepRel wD₁.Θ (lsD1 l₀ l₁) (lsD1' l₀ l₂) (viewR l₀ (lf 1)) := by
  intro r hr hrel
  simp only [lsD1, rsOfT, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨lendRec l₀, by simp [lsD1', rsOfT], lendRec_rr l₀⟩
  · exact absurd (relFT_viewR_iff.mp hrel) h

/-- The resume list is not a re-reading of the stop list. -/
theorem not_rr_d1 {l₀ l₁ l₂ : BoCa.Loc} (h : l₁ ≠ l₂) :
    ¬ SRecsRR wD₁.Θ (lsD1 l₀ l₁) (lsD1' l₀ l₂) := by
  intro hs
  cases hs with
  | cons _ t =>
      cases t with
      | cons h₂ _ => exact h h₂.1.1.symm

theorem cov_lsD1' (l₀ l₂ : BoCa.Loc) : ∀ x ∈ lsD1' l₀ l₂, CovR (sem wD₁.Θ) wD₁.K x.1.R := by
  intro x hx
  simp only [lsD1', List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact empty_cov _ _

/-- **Depth 1: `κ` holding the view of the lend at `1`, boxed at `2`, carried along the
extension to a list that leaves out a record it does not read and adds one at `5`, is a value of
`[@2] U (1 ⊸ F (Imm @1 1))` there and is resumed.** Every hypothesis of
`STy.kontBox_resume_after` discharged; the view re-read is the view (`rr_view`). -/
theorem kontBox_depth1 {l₀ l₁ l₂ : BoCa.Loc} (h : l₁ ≠ l₀) {k n : Nat} (hn : n < k) :
    (STy.kontBox (lf 2) STy.unit (cRet (ℍ := ℍ) (τR (lf 1)))).P n wD₁ (lsD1' l₀ l₂)
        (kontV (kRet l₀)) (viewR l₀ (lf 1)) ∧
      ∀ (b : Val) (ρa σ : TRes wD₁.K), ResUT.CompS (viewR l₀ (lf 1)) ρa σ →
        CovR (sem wD₁.Θ) wD₁.K σ → STy.unit.P n wD₁ (lsD1' l₀ l₂) b ρa →
        cerwpT (ℍ := ℍ) tbE (postOf (τR (lf 1))) Fb (fdNil enU Val.unit Fb) n wD₁ (lsD1' l₀ l₂) []
          (.app (.val (kontV (kRet l₀))) (.val b)) σ :=
  STy.kontBox_resume_after tbE_local tbE_down (kontV_step (kRet l₀)) (fun _ _ _ _ _ h => h)
    (share_viewR (ℍ := ℍ) wD₀ l₀ (lf 1) k (lsD1 l₀ l₁)) (viewR_inStratum (lt₀ (by omega) (by omega)))
    (viewR_cov l₀ (lf 1)) (extD _) (by rw [viewR_eq, viewR_eq]; exact rr_view) (keep_d1 h)
    (cov_lsD1' l₀ l₂) hn

/-! ### Depth 3: a view whose witness holds the enclosing views -/

/-- Lifetimes `1 ⊐ 2 ⊐ 3`: the facts the nested views' strata ask. -/
structure Nest (K : WCactus) : Prop where
  h₂₁ : K.lt (lf 2) (lf 1)
  h₃₂ : K.lt (lf 3) (lf 2)

theorem nest₀ : Nest wD₀.K := ⟨lt₀ (by omega) (by omega), lt₀ (by omega) (by omega)⟩

theorem nest₁ : Nest wD₁.K := ⟨lt₁ (by omega) (by omega), lt₁ (by omega) (by omega)⟩

/-- The view of the outermost lend, of a unit cell at `ℓ = 1`: `1 ↦ imm({1}, (), ∅)`. -/
def v1 (K : WCactus) : TRes K := viewR 1 (lf 1)

/-- The view of the lend at `2` of `ℓ = 2`, which holds `1` and its view: `2 ↦ imm({2}, 1, v1)`. -/
def i2 {K : WCactus} (h : Nest K) : TImm K :=
  ⟨TSet.single (lf 2), Val.loc 1, ResST.toRes ⟨v1 K, viewR_inStratum h.h₂₁⟩⟩

def v2 {K : WCactus} (h : Nest K) : TRes K := PMap.sng 2 (.imm (i2 h))

theorem i2_ls {K : WCactus} (h : Nest K) : ∀ y ∈ (i2 h).ls.set, K.lt (lf 3) y := fun y hy => by
  have hy' : y = lf 2 := by simpa [i2, TSet.single] using hy
  exact hy' ▸ h.h₃₂

/-- `κ`'s share: the view of the lend at `3` of `ℓ = 0`, which holds `2` and its view:
`0 ↦ imm({3}, 2, v2)`. -/
def i3 {K : WCactus} (h : Nest K) : TImm K :=
  ⟨TSet.single (lf 3), Val.loc 2, ResST.toRes ⟨v2 h, sngImm_inStratum (i2_ls h)⟩⟩

def v3 {K : WCactus} (h : Nest K) : TRes K := PMap.sng 0 (.imm (i3 h))

theorem i2_res {K : WCactus} (h : Nest K) : (i2 h).res = v1 K := ImmT.res_toRes _

theorem i3_res {K : WCactus} (h : Nest K) : (i3 h).res = v2 h := ImmT.res_toRes _

theorem v2_cov {Θ : CodeTy} {K : WCactus} (h : Nest K) : CovR (sem Θ) K (v2 h) :=
  cov_sngImm (by rw [i2_res]; exact viewR_cov _ _)

theorem v3_cov {Θ : CodeTy} {K : WCactus} (h : Nest K) : CovR (sem Θ) K (v3 h) :=
  cov_sngImm (by rw [i3_res]; exact v2_cov h)

theorem v1_rr {Θ : LocTy} {K K' : WCactus} : RR Θ (v1 K) (v1 K') := by
  unfold v1; rw [viewR_eq, viewR_eq]; exact rr_view

theorem v2_rr {Θ : LocTy} {K K' : WCactus} (h : Nest K) (h' : Nest K') :
    RR Θ (v2 h) (v2 h') :=
  rr_sngImm rfl rfl (by rw [i2_res, i2_res]; exact v1_rr)

/-- **The nested view at the new tree is its re-reading.** -/
theorem v3_rr {Θ : LocTy} {K K' : WCactus} (h : Nest K) (h' : Nest K') :
    RR Θ (v3 h) (v3 h') :=
  rr_sngImm rfl rfl (by rw [i3_res, i3_res]; exact v2_rr h h')

/-- `κ`'s result at depth 3: `Imm @3 (Imm @2 (Imm @1 1))`. -/
def τR3 : STy := STy.imm (lf 3) (STy.imm (lf 2) (STy.imm (lf 1) STy.unit))

theorem v3_val {n : Nat} {w : TWd} (h : Nest w.K) (ls : List (SRecT w.K)) :
    τR3.P n w ls (Val.loc 0) (v3 h) :=
  ⟨0, i3 h, rfl, rfl, le_single, 2, i2 h, rfl, i3_res h, le_single, 1, viewI (lf 1), rfl,
    i2_res h, le_single, rfl, viewI_res _⟩

/-- The records of the lends at `2` and `3`, each the lent cell's contents as escrow: `ℓ = 2`
holding `1` beside `v1`, `ℓ = 0` holding `2` beside `v2`. The lend at `1` is of a unit cell
(`lendRec 1`). -/
def r2 (K : WCactus) : FrameRecT K := ⟨2, Val.loc 1, v1 K, KTy.imm (lf 1) KTy.unit⟩

def r0 {K : WCactus} (h : Nest K) : FrameRecT K :=
  ⟨0, Val.loc 2, v2 h, KTy.imm (lf 2) (KTy.imm (lf 1) KTy.unit)⟩

/-- The stop list: the three lends (lifetimes `1`, `2`, `3`) and another branch's lend of `ℓ₅`
at `4`. -/
def lsD3 (l₅ : BoCa.Loc) : List (SRecT wD₀.K) :=
  [(lendRec 1, lf 1), (r2 _, lf 2), (r0 nest₀, lf 3), (lendRec l₅, lf 4)]

/-- The resume list: `ℓ₅`'s lend ended; a lend of `ℓ₆` opened at `5`. -/
def lsD3' (l₆ : BoCa.Loc) : List (SRecT wD₁.K) :=
  [(lendRec 1, lf 1), (r2 _, lf 2), (r0 nest₁, lf 3), (lendRec l₆, lf 5)]

/-- The locations frozen in the nested view: `0`, `2` and `1`. -/
theorem frz_v3 {K : WCactus} (h : Nest K) {m : BoCa.Loc} (hf : FrzT (v3 h) m) :
    m = 0 ∨ m = 2 ∨ m = 1 := by
  rcases frz_sngImm hf with e | hd
  · exact Or.inl e
  rw [i3_res] at hd
  rcases inDom_sng hd with e | hd
  · exact Or.inr (Or.inl e)
  change InDomT (i2 h).res m at hd
  rw [i2_res] at hd
  rcases inDom_sng hd with e | hd
  · exact Or.inr (Or.inr e)
  change InDomT (viewI (K := K) (lf 1)).res m at hd
  rw [viewI_res] at hd
  exact absurd hd not_inDom_empty

/-- **The share reads the records of all three lends.** -/
theorem relFT_d3 {K : WCactus} (h : Nest K) :
    RelFT (lendRec 1) (v3 h) ∧ RelFT (r2 K) (v3 h) ∧ RelFT (r0 h) (v3 h) := by
  have e₀ : (v3 h).get 0 = some (.imm (i3 h)) := by simp [v3, PMap.sng_get]
  have d₂ : InDomT (CellUT.imm (i3 h)).wit 2 := by
    change InDomT (i3 h).res 2
    rw [i3_res]
    exact InDomT.top (ψ := .imm (i2 h)) (by simp [v2, PMap.sng_get])
  have d₁ : InDomT (CellUT.imm (i3 h)).wit 1 := by
    change InDomT (i3 h).res 1
    rw [i3_res]
    refine InDomT.wit (m' := 2) (ψ := .imm (i2 h)) (by simp [v2, PMap.sng_get])
      (by simp [CellUT.kind]) ?_
    change InDomT (i2 h).res 1
    rw [i2_res]
    exact InDomT.top (ψ := .imm (viewI (lf 1))) (by simp [v1, viewR, PMap.sng_get])
  exact ⟨⟨1, FrzT.inImm e₀ rfl d₁, Or.inl rfl⟩, ⟨2, FrzT.inImm e₀ rfl d₂, Or.inl rfl⟩,
    ⟨0, FrzT.imm e₀ rfl, Or.inl rfl⟩⟩

/-- **The share does not read the fourth record.** -/
theorem not_relFT_d3 {K : WCactus} (h : Nest K) {l₅ : BoCa.Loc} (h₅ : l₅ ≠ 0 ∧ l₅ ≠ 2 ∧ l₅ ≠ 1) :
    ¬ RelFT (lendRec l₅) (v3 h) := by
  rintro ⟨m, hf, hx⟩
  have e := relAt_lendRec hx
  subst e
  rcases frz_v3 h hf with e | e | e
  · exact h₅.1 e
  · exact h₅.2.1 e
  · exact h₅.2.2 e

/-- **`KeepRel` re-reads the three records at the new tree, their escrows re-read, and drops the
fourth.** -/
theorem keep_d3 {l₅ l₆ : BoCa.Loc} (h₅ : l₅ ≠ 0 ∧ l₅ ≠ 2 ∧ l₅ ≠ 1) :
    KeepRel wD₁.Θ (lsD3 l₅) (lsD3' l₆) (v3 nest₀) := by
  intro r hr hrel
  simp only [lsD3, rsOfT, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨lendRec 1, by simp [lsD3', rsOfT], lendRec_rr 1⟩
  · exact ⟨r2 _, by simp [lsD3', rsOfT], rfl, rfl, rfl, v1_rr⟩
  · exact ⟨r0 nest₁, by simp [lsD3', rsOfT], rfl, rfl, rfl, v2_rr nest₀ nest₁⟩
  · exact absurd hrel (not_relFT_d3 nest₀ h₅)

theorem not_rr_d3 {l₅ l₆ : BoCa.Loc} (h : l₅ ≠ l₆) : ¬ SRecsRR wD₁.Θ (lsD3 l₅) (lsD3' l₆) := by
  intro hs
  cases hs with
  | cons _ t => cases t with
    | cons _ t => cases t with
      | cons _ t => cases t with
        | cons h₄ _ => exact h h₄.1.1.symm

theorem cov_lsD3' (l₆ : BoCa.Loc) : ∀ x ∈ lsD3' l₆, CovR (sem wD₁.Θ) wD₁.K x.1.R := by
  intro x hx
  simp only [lsD3', List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact empty_cov _ _
  · exact viewR_cov _ _
  · exact v2_cov nest₁
  · exact empty_cov _ _

/-- **Depth 3: `κ` holding the view of the lend at `3` whose witness holds the views of the lends
at `2` and `1`, boxed at `4`, carried along the extension to a list that re-reads the three
records, drops a fourth and adds one at `5`, is a value of
`[@4] U (1 ⊸ F (Imm @3 (Imm @2 (Imm @1 1))))` there and is resumed.** -/
theorem kontBox_depth3 {l₅ l₆ : BoCa.Loc} (h₅ : l₅ ≠ 0 ∧ l₅ ≠ 2 ∧ l₅ ≠ 1) {k n : Nat}
    (hn : n < k) :
    (STy.kontBox (lf 4) STy.unit (cRet (ℍ := ℍ) τR3)).P n wD₁ (lsD3' l₆) (kontV (kRet 0))
        (v3 nest₁) ∧
      ∀ (b : Val) (ρa σ : TRes wD₁.K), ResUT.CompS (v3 nest₁) ρa σ →
        CovR (sem wD₁.Θ) wD₁.K σ → STy.unit.P n wD₁ (lsD3' l₆) b ρa →
        cerwpT (ℍ := ℍ) tbE (postOf τR3) Fb (fdNil enU Val.unit Fb) n wD₁ (lsD3' l₆) []
          (.app (.val (kontV (kRet 0))) (.val b)) σ :=
  STy.kontBox_resume_after tbE_local tbE_down (kontV_step (kRet 0)) (fun _ _ _ _ _ h => h)
    (share_val (ℍ := ℍ) (w := wD₀) (v3_cov nest₀) (fun _ ls => v3_val nest₀ ls) k (lsD3 l₅))
    (sngImm_inStratum (i := i3 nest₀) fun y hy => by
      have hy' : y = lf 3 := by simpa [i3, TSet.single] using hy
      exact hy' ▸ lt₀ (a := 3) (b := 4) (by omega) (by omega))
    (v3_cov nest₀) (extD _) (v3_rr nest₀ nest₁) (keep_d3 h₅) (cov_lsD3' l₆) hn

/-- **`STy.reread` at the extension, on the nested view**: its re-reading exists, is covered, and
is a value of `Imm @3 (Imm @2 (Imm @1 1))` at every list keeping the records it reads; it is the
nested view at the new tree (`RR.func`). -/
theorem reread_v3 {n : Nat} (ls : List (SRecT wD₀.K)) :
    ∃ ρ' : TRes wD₁.K, RRw (w := wD₀) (w' := wD₁) (v3 nest₀) ρ' ∧ ρ' = v3 nest₁ ∧
      CovR (sem wD₁.Θ) wD₁.K ρ' ∧
      ∀ ls' : List (SRecT wD₁.K), KeepRel wD₁.Θ ls ls' (v3 nest₀) →
        τR3.P n wD₁ ls' (Val.loc 0) ρ' := by
  obtain ⟨ρ', hr, hc, h⟩ := STy.reread τR3 (extD _) (v3_cov nest₀) (v3_val (n := n) nest₀ ls)
  exact ⟨ρ', hr, RR.func hr (v3_rr nest₀ nest₁), hc, h⟩

/-! ### Rules out, at the same `κ` -/

/-- **`κ` boxed at its lend's own lifetime is not of its type**, at every index and list. -/
theorem not_kontBox_at_lend {a n : Nat} {ls : List (SRecT wD₀.K)} {τB : STy} {C : SCmp} :
    ¬ (STy.kontBox (lf a) τB C).P n wD₀ ls (kontV (kRet 0)) (viewR 0 (lf a)) :=
  STy.not_kontBox_of_view (l := 0) (i := viewI (lf a)) (by simp [viewR, PMap.sng_get])
    (Finset.mem_singleton_self _) (not_lt_of_le dP₀_inAlloc le_rfl)

/-- **`κ` boxed at the root, which outlives the lend, is not of its type.** -/
theorem not_kontBox_at_root {a n : Nat} {ls : List (SRecT wD₀.K)} {τB : STy} {C : SCmp} :
    ¬ (STy.kontBox (lf 0) τB C).P n wD₀ ls (kontV (kRet 0)) (viewR 0 (lf a)) :=
  STy.not_kontBox_of_view (l := 0) (i := viewI (lf a)) (by simp [viewR, PMap.sng_get])
    (Finset.mem_singleton_self _) (not_lt_of_le dP₀_inAlloc (Nat.zero_le a))

/-! ### A list-free reading admits a stuck thunk -/

/-- **At the empty list, a term that never steps, over the view, is a run** (`cerwpT_nil_of_imm`):
a thunk type running its thunks at `[]` would hold of `λ_. () ()` holding the view. -/
theorem nilRun_stuck {Q : TPostV} {Fb' F : TFrame} {n : Nat} {a : Nat} :
    cerwpT (ℍ := ℍ) tbE Q Fb' F n wD₀ [] [] BoCa.BoLo.stuckE (viewR 0 (lf a)) :=
  cerwpT_nil_of_imm (ψ := CellUT.imm (viewI (lf a))) (l := 0) (by simp [viewR, PMap.sng_get]) rfl

/-! ### Round 7 at codes: `STy.mut_reread` and `RC.mut_extends` at the graft -/

/-- `1 + Imm @α 1` as a store code: round 7's contents type (`τc`). -/
def cC : KTy := .sum .unit (.imm αL .unit)

open Classical in
/-- The code typing: `ℓ₁ = 1` stores `1 + Imm @α 1`. -/
def ΘC : CodeTy := fun l => if l = 1 then some cC else none

theorem ΘC_one : ΘC 1 = some cC := by simp [ΘC]

theorem cC_interp : cC.interp ΘC = τc := rfl

/-- Round 7 before the graft (`beforeP`: `α`, `β` siblings) and after (`graftP`: `α` inside `β`). -/
def wR₀ : TWd := ⟨beforeP, ΘC, tmplT _ ΘC⟩

def wR₁ : TWd := ⟨graftP, ΘC, tmplT _ ΘC⟩

/-- The task's cell before the graft, `1 ↦ mut({α}, inj₁ (), ∅, 1 + Imm @α 1 read at K₀)`. -/
def cellC : TMut K₀ :=
  ⟨TSet.single αL, anti_single K₀ αL, Val.inj₁ Val.unit,
    ResST.toRes ⟨PMap.empty, empty_inStratum _⟩, fun u r => τc.P K₀ u r.toU, by
      rw [ResST.toU_toRes]; exact τc_inj₁ K₀⟩

def ρC : TRes wR₀.K := PMap.sng 1 (.mut cellC)

theorem cellC_res : cellC.res = PMap.empty := ResST.toU_toRes _

theorem ρC_cov : CovR (sem wR₀.Θ) wR₀.K ρC := by
  intro m ψ e
  rw [ρC, PMap.sng_get] at e
  split_ifs at e with hm
  cases e
  subst hm
  refine Cov.mut 1 _ (cC.interp ΘC) (sem_of ΘC_one) (fun _ _ => Iff.rfl) ?_
  change CovR _ _ cellC.res
  rw [cellC_res]; exact empty_cov _ _

/-- The task's cell is a value of `Mut @α (1 + Imm @α 1)` before the graft. -/
theorem ρC_mut {n : Nat} {ls : List (SRecT wR₀.K)} :
    (STy.mut αL cC).P n wR₀ ls (Val.loc 1) ρC :=
  STy.mut_iff.mpr ⟨1, cellC, rfl, rfl, ΘC_one, le_single, fun _ _ => Iff.rfl⟩

theorem extR (ρ : TRes wR₀.K) : wR₀.Ext wR₁ ρ := ⟨graftExt, AgreeOn.refl _ _⟩

/-- **Round 7 at codes.** Along the graft `beforeP → graftP` (proper: `α ⊏ β` after, not before),
the task's `mut` cell at `ℓ₁` is re-read (`STy.mut_reread`) to a cell whose invariant is
`1 + Imm @α 1` read at the new tree. The re-read invariant admits the value stored before the
graft over its re-read resource (`RC.mut_extends`), and admits the handler's borrow at `β`
(`inj₂ ℓ₂`), which the cell's code read before the graft refuses (`round7_refused_before`). -/
theorem round7_codes {n : Nat} {ls : List (SRecT wR₀.K)} :
    ∃ m' : TMut wR₁.K, RRw (w := wR₀) (w' := wR₁) ρC (PMap.sng 1 (.mut m')) ∧
      (∀ u r, m'.P u r ↔ (cC.interp wR₁.Θ).P wR₁.K u r.toU) ∧
      (∀ r : ResT BoCa.Loc BoCa.Val wR₁.K m'.ls, r.toU = PMap.empty →
        m'.P (Val.inj₁ Val.unit) r) ∧
      (∀ r : ResT BoCa.Loc BoCa.Val wR₁.K m'.ls, r.toU = borrowAt wR₁.K 2 Val.unit →
        m'.P (Val.inj₂ (Val.loc 2)) r) ∧
      ¬ (cC.interp wR₀.Θ).P wR₀.K (Val.inj₂ (Val.loc 2)) (borrowAt wR₀.K 2 Val.unit) := by
  obtain ⟨l, m', hl, hr, -, hP⟩ := STy.mut_reread (extR _) ρC_cov (ρC_mut (n := n) (ls := ls))
  obtain rfl : l = 1 := (Val.loc_inj.mp hl).symm
  obtain ⟨ψ', e', hrc⟩ := RR.of_sng hr
  have hψ : ψ' = .mut m' := by
    have := congrArg (fun ρ : TRes wR₁.K => ρ.get 1) e'
    simpa [PMap.sng_get] using this.symm
  subst hψ
  refine ⟨m', hr, hP, fun r hr₀ => ?_, fun r hb => ?_, round7_refused_before⟩
  · have hc₀ : Cov (sem wR₀.Θ) wR₀.K 1 (.mut cellC) := ρC_cov 1 _ (by simp [ρC, PMap.sng_get])
    have e₀ : cellC.ρ.toU = PMap.empty := cellC_res
    have hrr : RR (sem ΘC) cellC.ρ.toU r.toU := by rw [e₀, hr₀]; exact RR.empty
    exact RC.mut_extends (Θ := ΘC) (Θ' := ΘC) graftExt hc₀ rfl hrc (r₀ := cellC.ρ)
      (by rw [e₀]; exact empty_cov _ _) hrr (fun _ _ => rfl) cellC.hw
  · exact (hP _ r).mpr (by rw [hb]; exact round7_admitted_after)

end BoCa.Fig16.Tree.Wp.KEx

end
