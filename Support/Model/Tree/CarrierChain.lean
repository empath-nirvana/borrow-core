import Support.Model.Tree.CarrierRes

/-!
# At the chain, the tree-stratified carrier is the printed one

`WCactus.chain` is the printed order (row 5.9) with the printed measure (row 5.58). At it:

* finite lifetime sets are the printed `LSet`s (`TSet.toLSet`, `LSet.toTSet`, inverse);
* `Above S T` is `⊔S ⊏ ⊓T` (`chain_above_iff`), so the tree stratum of `S` is the printed
  stratum of `⊔S`, and `Res_ᾱ` is the printed `Res_{⊔ᾱ}`;
* an antichain is a singleton (`chain_anti_iff`), and clause 3's `min({α} ∪ {β})` is `{α ⊓ β}`
  (`chain_minS_single`);
* the two unions are isomorphic: `ΦU : CellUT chain → CellU` and `ΨU : CellU → CellUT chain`,
  mutually inverse (`ΦU_ΨU`, `ΨU_ΦU`), built by well-founded recursion on the two measures;
  `ΦU` sends `imm(ᾱ, v, ρ)` to `imm(ᾱ, v, ΦU ρ)` and `mut({β}, v, ρ, P̂)` to `mut(β, v, ΦU ρ, P̂)`
  (`ΦU_immOf`, `ΦU_mutOf`), and preserves and reflects the strata, the tags, the values, the
  witnesses, `▶◀`, `●` and `○` (`Tree/CarrierChainOps.lean`).
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-! ### Finite lifetime sets are the printed `LSet`s -/

/-- A finite set as a printed `LSet`: `⊔ᾱ` its greatest member, `⊓ᾱ` its least. -/
def TSet.toLSet (s : TSet) : LSet where
  mem x := x ∈ s.set
  join := s.set.max' s.ne
  meet := s.set.min' s.ne
  join_mem := Finset.max'_mem _ _
  meet_mem := Finset.min'_mem _ _
  join_greatest _ hx := Finset.le_max' _ _ hx
  meet_least _ hx := Finset.min'_le _ _ hx

/-- `⊔ᾱ`. -/
abbrev TSet.jn (s : TSet) : Life := s.toLSet.join

open Classical in
/-- A printed `LSet` is finite: its members lie between `⊔ᾱ` and `⊓ᾱ` in `ℕ`. -/
def TSet.ofLSet (L : LSet) : TSet where
  set := ((Finset.range (OrderDual.ofDual L.meet + 1)).image OrderDual.toDual).filter L.mem
  ne := ⟨L.join, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨OrderDual.ofDual L.join,
    Finset.mem_range.mpr (Nat.lt_succ_of_le (L.meet_le_join)), rfl⟩, L.join_mem⟩⟩

theorem TSet.mem_ofLSet {L : LSet} {x : Life} : x ∈ (TSet.ofLSet L).set ↔ L.mem x := by
  classical
  unfold TSet.ofLSet
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨OrderDual.ofDual x, Nat.lt_succ_of_le (L.meet_least x h), rfl⟩, h⟩

theorem TSet.toLSet_ofLSet (L : LSet) : (TSet.ofLSet L).toLSet = L :=
  LSet.ext fun _ => TSet.mem_ofLSet

theorem TSet.ofLSet_toLSet (s : TSet) : TSet.ofLSet s.toLSet = s :=
  TSet.ext (Finset.ext fun _ => TSet.mem_ofLSet)

@[simp] theorem TSet.mem_toLSet {s : TSet} {x : Life} : s.toLSet.mem x ↔ x ∈ s.set := Iff.rfl

theorem TSet.toLSet_union (s t : TSet) : (s ∪ t).toLSet = s.toLSet ∪ t.toLSet :=
  LSet.ext fun x => by
    show x ∈ (s ∪ t).set ↔ (x ∈ s.set ∨ x ∈ t.set)
    simp

theorem TSet.jn_single (a : Life) : (TSet.single a).jn = a := Finset.max'_singleton a

theorem TSet.toLSet_single (a : Life) : (TSet.single a).toLSet = LSet.singleton a :=
  LSet.ext fun x => by
    show x ∈ ({a} : Finset Life) ↔ x = a
    simp

/-! ### The order at the chain -/

open WCactus

/-- `T` above `S` at the chain: `⊔S ⊏ ⊓T`. -/
theorem chain_above_iff {S T : TSet} : chain.Above S T ↔ S.jn < T.toLSet.meet := by
  constructor
  · intro h
    exact (chain_lt _ _).mp (h _ (Finset.max'_mem S.set S.ne) _ (Finset.min'_mem T.set T.ne))
  · intro h x hx y hy
    exact (chain_lt _ _).mpr (lt_of_le_of_lt (Finset.le_max' _ _ hx)
      (lt_of_lt_of_le h (Finset.min'_le _ _ hy)))

/-- At the chain an antichain is a singleton. -/
theorem chain_anti_iff {s : TSet} : chain.Anti s ↔ s = TSet.single s.jn := by
  constructor
  · intro h
    refine TSet.ext (Finset.ext fun x => ?_)
    simp only [TSet.single_set, Finset.mem_singleton]
    constructor
    · intro hx
      have hle : x ≤ s.jn := Finset.le_max' _ _ hx
      rcases lt_or_eq_of_le hle with hlt | e
      · exact absurd ((chain_lt _ _).mpr hlt) (h x hx _ (Finset.max'_mem s.set s.ne))
      · exact e
    · rintro rfl; exact Finset.max'_mem s.set s.ne
  · intro e x hx y hy hxy
    rw [e] at hx hy
    simp only [TSet.single_set, Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact Cactus.lt_irrefl _ _ hxy

theorem chain_anti_single (a : Life) : chain.Anti (TSet.single a) := by
  intro x hx y hy hxy
  simp only [TSet.single_set, Finset.mem_singleton] at hx hy
  subst hx; subst hy
  exact Cactus.lt_irrefl _ _ hxy

/-- Clause 3's lifetime set at the chain: `min({α} ∪ {β}) = {α ⊓ β}`. -/
theorem chain_minS_single (a b : Life) :
    chain.minS (TSet.single a ∪ TSet.single b) = TSet.single (a ⊓ b) := by
  refine TSet.ext (Finset.ext fun x => ?_)
  rw [chain.mem_minS]
  simp only [TSet.union_set, TSet.single_set, Finset.mem_union, Finset.mem_singleton,
    chain_lt]
  constructor
  · rintro ⟨hx | hx, hmin⟩ <;> subst hx
    · rcases le_total x b with h | h
      · exact (inf_eq_left.mpr h).symm
      · rcases lt_or_eq_of_le h with h | h
        · exact absurd h (hmin b (Or.inr rfl))
        · rw [h, inf_idem]
    · rcases le_total a x with h | h
      · rcases lt_or_eq_of_le h with h | h
        · exact absurd h (hmin a (Or.inl rfl))
        · rw [h, inf_idem]
      · exact (inf_eq_right.mpr h).symm
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rcases le_total a b with h | h
      · exact Or.inl (inf_eq_left.mpr h)
      · exact Or.inr (inf_eq_right.mpr h)
    · rintro y (rfl | rfl) hlt
      · exact absurd (inf_le_left : y ⊓ b ≤ y) (not_le.mpr hlt)
      · exact absurd (inf_le_right : a ⊓ y ≤ y) (not_le.mpr hlt)

/-! ### `ΦU`: the tree carrier at the chain into the printed one -/

variable {Loc Val : Type}

theorem ResU.inStratum_map {α : Life} {X : Type} (f : X → CellU Loc Val)
    (hf : ∀ x, (f x).InStratum α) (ρ : PMap Loc X) : ResU.InStratum α (ρ.map f) := by
  intro l ψ e
  rw [PMap.map_get] at e
  cases h : ρ.get l with
  | none => rw [h] at e; exact absurd e (by simp)
  | some x =>
      rw [h] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact e ▸ hf x

theorem ResUT.inStratum_map {K : WCactus} {S : TSet} {X : Type} (f : X → CellUT Loc Val K)
    (hf : ∀ x, (f x).InStratum S) (ρ : PMap Loc X) : ResUT.InStratum S (ρ.map f) := by
  intro l ψ e
  rw [PMap.map_get] at e
  cases h : ρ.get l with
  | none => rw [h] at e; exact absurd e (by simp)
  | some x =>
      rw [h] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact e ▸ hf x

theorem PMap.map_map {X Y Z : Type} (f : X → Y) (g : Y → Z) (ρ : PMap Loc X) :
    (ρ.map f).map g = ρ.map (g ∘ f) :=
  PMap.ext fun l => by simp only [PMap.map_get, Option.map_map]

theorem PMap.map_congr {X Y : Type} {f g : X → Y} (ρ : PMap Loc X)
    (h : ∀ l x, ρ.get l = some x → f x = g x) : ρ.map f = ρ.map g :=
  PMap.ext fun l => by
    simp only [PMap.map_get]
    cases e : ρ.get l with
    | none => rfl
    | some x => simp [h l x e]

theorem PMap.map_id' {X : Type} (ρ : PMap Loc X) : ρ.map id = ρ :=
  PMap.ext fun l => by simp

variable (Loc Val) in
/-- The motive of `Φ`: a map out of `Cell_S` at the chain landing in the printed stratum
`⊔S`. -/
def PhiM (S : TSet) : Type :=
  {f : CellT Loc Val chain S → CellU Loc Val // ∀ ψ, (f ψ).InStratum S.jn}

theorem jn_lt_jn {S s : TSet} (hs : chain.Above S s) : S.jn < s.jn :=
  lt_of_lt_of_le (chain_above_iff.mp hs) s.toLSet.meet_le_join

/-- One layer of `Φ`. -/
def phiLayer (S : TSet) (rec : ∀ T, chain.Above S T → PhiM Loc Val T) :
    CellTF Loc Val chain S (fun T _ => CellT Loc Val chain T) → CellU Loc Val
  | .own v => .own v
  | .imm s hs v ρ =>
      CellU.immOf s.toLSet v (ρ.map (rec s hs).1) (ResU.inStratum_map _ (rec s hs).2 ρ)
  | .mut s hs _ v ρ P hw =>
      CellU.mutOf s.jn v (ρ.map (rec s hs).1) (ResU.inStratum_map _ (rec s hs).2 ρ)
        (fun w r => ∃ r₀ : ResT Loc Val chain s, r₀.map (rec s hs).1 = r.val ∧ P w r₀)
        ⟨ρ, rfl, hw⟩

theorem phiLayer_inStratum (S : TSet) (rec : ∀ T, chain.Above S T → PhiM Loc Val T)
    (x : CellTF Loc Val chain S (fun T _ => CellT Loc Val chain T)) :
    (phiLayer S rec x).InStratum S.jn := by
  cases x with
  | own v => exact trivial
  | imm s hs v ρ => exact chain_above_iff.mp hs
  | «mut» s hs a v ρ P hw => exact jn_lt_jn hs

def phiF (S : TSet) (rec : ∀ T, chain.Above S T → PhiM Loc Val T) : PhiM Loc Val S :=
  ⟨fun ψ => phiLayer S rec ψ.toF, fun ψ => phiLayer_inStratum S rec ψ.toF⟩

/-- `Φ_S : Cell_S → Cell`, at the chain. -/
def Phi : ∀ S, PhiM Loc Val S := WellFounded.fix chain.above_wf phiF

theorem Phi_eq (S : TSet) : Phi (Loc := Loc) (Val := Val) S = phiF S (fun T _ => Phi T) :=
  WellFounded.fix_eq chain.above_wf phiF S

/-- `ΦU` on the union. -/
def ΦU : CellUT Loc Val chain → CellU Loc Val
  | .own v => .own v
  | .imm i => CellU.immOf i.ls.toLSet i.v (i.ρ.map (Phi i.ls).1)
      (ResU.inStratum_map _ (Phi i.ls).2 i.ρ)
  | .mut m => CellU.mutOf m.ls.jn m.v (m.ρ.map (Phi m.ls).1)
      (ResU.inStratum_map _ (Phi m.ls).2 m.ρ)
      (fun w r => ∃ r₀ : ResT Loc Val chain m.ls, r₀.map (Phi m.ls).1 = r.val ∧ m.P w r₀)
      ⟨m.ρ, rfl, m.hw⟩

/-- `Φ_S` is `ΦU` on the stratum. -/
theorem Phi_apply {S : TSet} (ψ : CellT Loc Val chain S) : (Phi S).1 ψ = ΦU ψ.toU := by
  rw [Phi_eq]
  show phiLayer S (fun T _ => Phi T) ψ.toF = ΦU (CellTF.toU ψ.toF)
  generalize ψ.toF = x
  cases x <;> rfl

theorem Phi_map {S : TSet} (ρ : ResT Loc Val chain S) : ρ.map (Phi S).1 = ρ.toU.map ΦU := by
  unfold ResT.toU
  rw [PMap.map_map]
  exact PMap.map_congr ρ fun _ ψ _ => Phi_apply ψ

/-! ### `ΨU`: the printed carrier into the tree carrier at the chain -/

variable (Loc Val) in
/-- The motive of `Ψ`: a map out of the printed `Cell_α` landing in the tree stratum `{α}`. -/
def PsiM (a : Life) : Type :=
  {g : Cell Loc Val a → CellUT Loc Val chain // ∀ c, (g c).InStratum (TSet.single a)}

theorem above_single_toTSet {a : Life} {L : LSet} (h : a < L.meet) :
    chain.Above (TSet.single a) (TSet.ofLSet L) := by
  intro x hx y hy
  simp only [TSet.single_set, Finset.mem_singleton] at hx
  subst hx
  exact (chain_lt _ _).mpr (lt_of_lt_of_le h (L.meet_least y (TSet.mem_ofLSet.mp hy)))

theorem above_single_single {a b : Life} (h : a < b) :
    chain.Above (TSet.single a) (TSet.single b) := by
  intro x hx y hy
  simp only [TSet.single_set, Finset.mem_singleton] at hx hy
  subst hx; subst hy
  exact (chain_lt _ _).mpr h

/-- A cell above `⊔ᾱ` is above every member of `ᾱ`. -/
theorem inStratum_toTSet_of_join {L : LSet} {ψ : CellUT Loc Val chain}
    (h : ψ.InStratum (TSet.single L.join)) : ψ.InStratum (TSet.ofLSet L) :=
  h.mono fun x hx => ⟨L.join, Finset.mem_singleton_self _,
    L.join_greatest x (TSet.mem_ofLSet.mp hx)⟩

/-- One layer of `Ψ`. -/
def psiLayer (a : Life) (rec : ∀ b, a < b → PsiM Loc Val b) :
    CellF Loc Val a (fun b _ => Cell Loc Val b) → CellUT Loc Val chain
  | .own v => .own v
  | .imm i =>
      CellUT.immOf (TSet.ofLSet i.ls) i.v
        (i.ρ.map (rec i.ls.join (lt_of_lt_of_le i.hls i.ls.meet_le_join)).1)
        (ResUT.inStratum_map _ (fun c => inStratum_toTSet_of_join
          ((rec i.ls.join (lt_of_lt_of_le i.hls i.ls.meet_le_join)).2 c)) i.ρ)
  | .mut m =>
      CellUT.mutOf (TSet.single m.β) m.v (m.ρ.map (rec m.β m.hβ).1)
        (ResUT.inStratum_map _ (rec m.β m.hβ).2 m.ρ)
        (fun w r => ∃ r₀ : Res Loc Val m.β, r₀.map (rec m.β m.hβ).1 = r.val ∧ m.P w r₀)
        ⟨m.ρ, rfl, m.hw⟩

theorem psiLayer_inStratum (a : Life) (rec : ∀ b, a < b → PsiM Loc Val b)
    (x : CellF Loc Val a (fun b _ => Cell Loc Val b)) :
    (psiLayer a rec x).InStratum (TSet.single a) := by
  cases x with
  | own v => exact trivial
  | imm i => exact above_single_toTSet i.hls
  | «mut» m => exact above_single_single m.hβ

def psiF (a : Life) (rec : ∀ b, a < b → PsiM Loc Val b) : PsiM Loc Val a :=
  ⟨fun c => psiLayer a rec c.toF, fun c => psiLayer_inStratum a rec c.toF⟩

/-- `Ψ_α : Cell_α → Cell`, printed into the tree at the chain. -/
def Psi : ∀ a, PsiM Loc Val a :=
  WellFounded.fix (invImage OrderDual.ofDual Nat.lt_wfRel).wf psiF

theorem Psi_eq (a : Life) : Psi (Loc := Loc) (Val := Val) a = psiF a (fun b _ => Psi b) :=
  WellFounded.fix_eq (invImage OrderDual.ofDual Nat.lt_wfRel).wf psiF a

/-- `ΨU` on the union. -/
def ΨU : CellU Loc Val → CellUT Loc Val chain
  | .own v => .own v
  | .imm i =>
      CellUT.immOf (TSet.ofLSet i.ls) i.v (i.ρ.map (Psi i.ls.join).1)
        (ResUT.inStratum_map _ (fun c => inStratum_toTSet_of_join ((Psi i.ls.join).2 c)) i.ρ)
  | .mut m =>
      CellUT.mutOf (TSet.single m.β) m.v (m.ρ.map (Psi m.β).1)
        (ResUT.inStratum_map _ (Psi m.β).2 m.ρ)
        (fun w r => ∃ r₀ : Res Loc Val m.β, r₀.map (Psi m.β).1 = r.val ∧ m.P w r₀)
        ⟨m.ρ, rfl, m.hw⟩

theorem Psi_apply {a : Life} (c : Cell Loc Val a) : (Psi a).1 c = ΨU c.toU := by
  rw [Psi_eq]
  show psiLayer a (fun b _ => Psi b) c.toF = ΨU (CellF.toU c.toF)
  generalize c.toF = x
  cases x <;> rfl

theorem Psi_map {a : Life} (ρ : Res Loc Val a) : ρ.map (Psi a).1 = ρ.toU.map ΨU := by
  unfold Res.toU
  rw [PMap.map_map]
  exact PMap.map_congr ρ fun _ c _ => Psi_apply c

/-! ### `ΦU` and `ΨU` on the constructors -/

theorem MutT.mutOf_eta {K : WCactus} (m : MutT Loc Val K) :
    @CellUT.mutOf _ _ _ m.ls ⟨m.anti⟩ m.v m.res CellUT.wit_inStratum_mut (fun w r => m.P w r.toRes)
      (by show m.P m.v (ResST.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩)
          rw [show ResST.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩ = m.ρ from ResT.toRes_toS m.ρ]
          exact m.hw) = .mut m := by
  show CellUT.mut _ = CellUT.mut m
  refine congrArg CellUT.mut (MutT.ext' rfl rfl ?_ ?_)
  · simp only [heq_eq_eq]; exact ResT.toRes_toS m.ρ
  · simp only [heq_eq_eq]
    funext v r
    show m.P v r.toS.toRes = m.P v r
    rw [ResT.toRes_toS]

theorem MutU.res_inStratum (m : MutU Loc Val) : ResU.InStratum m.β m.res := m.ρ.toU_inStratum

theorem ImmU.res_inStratum (i : ImmU Loc Val) : ResU.InStratum i.ls.join i.res :=
  i.ρ.toU_inStratum

theorem ImmU.immOf_eta' (i : ImmU Loc Val) :
    CellU.immOf i.ls i.v i.res (ImmU.res_inStratum i) = .imm i := ImmU.immOf_eta i

theorem ImmT.immOf_eta' {K : WCactus} (i : ImmT Loc Val K) :
    CellUT.immOf i.ls i.v i.res CellUT.wit_inStratum_imm = .imm i := ImmT.immOf_eta i

theorem MutU.mutOf_eta (m : MutU Loc Val) :
    CellU.mutOf m.β m.v m.res (MutU.res_inStratum m) (fun w r => m.P w r.toRes)
      (by show m.P m.v (ResS.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩)
          rw [show ResS.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩ = m.ρ from Res.toRes_toS m.ρ]
          exact m.hw) = .mut m := by
  show CellU.mut _ = CellU.mut m
  refine congrArg CellU.mut (MutU.ext rfl rfl ?_ ?_)
  · simp only [heq_eq_eq]; exact Res.toRes_toS m.ρ
  · simp only [heq_eq_eq]
    funext v r
    show m.P v r.toS.toRes = m.P v r
    rw [Res.toRes_toS]

theorem ΦU_inStratum {S : TSet} {ψ : CellUT Loc Val chain} (h : ψ.InStratum S) :
    (ΦU ψ).InStratum S.jn := by
  cases ψ with
  | own v => exact trivial
  | imm i => exact chain_above_iff.mp h
  | «mut» m => exact jn_lt_jn h

theorem ΨU_inStratum {a : Life} {c : CellU Loc Val} (h : c.InStratum a) :
    (ΨU c).InStratum (TSet.single a) := by
  cases c with
  | own v => exact trivial
  | imm i => exact above_single_toTSet h
  | «mut» m => exact above_single_single h

theorem ΦU_inStratum_iff {S : TSet} {ψ : CellUT Loc Val chain} :
    (ΦU ψ).InStratum S.jn ↔ ψ.InStratum S := by
  refine ⟨fun h => ?_, ΦU_inStratum⟩
  cases ψ with
  | own v => exact trivial
  | imm i => exact chain_above_iff.mpr h
  | «mut» m =>
      have hlt : S.jn < m.ls.jn := h
      intro x hx y hy
      have hy' : y = m.ls.jn := by
        have e := chain_anti_iff.mp m.anti
        rw [e] at hy
        simpa using hy
      subst hy'
      exact (chain_lt _ _).mpr (lt_of_le_of_lt (Finset.le_max' _ _ hx) hlt)

theorem ΦU_map_inStratum {S : TSet} {ρ : ResUT Loc Val chain} (h : ρ.InStratum S) :
    ResU.InStratum S.jn (ρ.map ΦU) := by
  intro l ψ e
  rw [PMap.map_get] at e
  cases f : ρ.get l with
  | none => rw [f] at e; exact absurd e (by simp)
  | some x =>
      rw [f] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact e ▸ ΦU_inStratum (h l x f)

theorem ΨU_map_inStratum {a : Life} {ρ : ResU Loc Val} (h : ρ.InStratum a) :
    ResUT.InStratum (TSet.single a) (ρ.map ΨU) := by
  intro l ψ e
  rw [PMap.map_get] at e
  cases f : ρ.get l with
  | none => rw [f] at e; exact absurd e (by simp)
  | some x =>
      rw [f] at e
      simp only [Option.map_some, Option.some.injEq] at e
      exact e ▸ ΨU_inStratum (h l x f)

/-- `ΦU(imm(ᾱ, v, ρ)) = imm(ᾱ, v, ΦU ρ)`. -/
theorem ΦU_immOf (s : TSet) (v : Val) (ρ : ResUT Loc Val chain) (h : ρ.InStratum s) :
    ΦU (CellUT.immOf s v ρ h) = CellU.immOf s.toLSet v (ρ.map ΦU) (ΦU_map_inStratum h) := by
  show CellU.immOf s.toLSet v ((ResST.toRes ⟨ρ, h⟩).map (Phi s).1) _ = _
  refine CellU.immOf_congr rfl rfl ?_ _ _
  rw [Phi_map, ResST.toU_toRes]

/-- `mut` congruence in the printed carrier, with the witness rewritten too. -/
theorem CellU.mutOf_congr' {b b' : Life} (e : b = b') {v : Val} {ρ ρ' : ResU Loc Val}
    (eρ : ρ = ρ') (h : ρ.InStratum b) (h' : ρ'.InStratum b')
    (P : Val → SPropS Loc Val b) (P' : Val → SPropS Loc Val b')
    (hP : P v ⟨ρ, h⟩) (hP' : P' v ⟨ρ', h'⟩)
    (eP : ∀ (r : ResU Loc Val) (hr : r.InStratum b) (hr' : r.InStratum b') (w : Val),
        P w ⟨r, hr⟩ ↔ P' w ⟨r, hr'⟩) :
    CellU.mutOf b v ρ h P hP = CellU.mutOf b' v ρ' h' P' hP' := by
  subst eρ
  exact CellU.mutOf_congr e v ρ h h' P P' hP hP' eP

/-- `mut` congruence in the tree carrier, with the witness rewritten too. -/
theorem CellUT.mutOf_congr' {K : WCactus} {s s' : TSet} (e : s = s') [Fact (K.Anti s)]
    [Fact (K.Anti s')] {v : Val} {ρ ρ' : ResUT Loc Val K} (eρ : ρ = ρ') (h : ρ.InStratum s)
    (h' : ρ'.InStratum s') (P : Val → SPropST Loc Val K s) (P' : Val → SPropST Loc Val K s')
    (hP : P v ⟨ρ, h⟩) (hP' : P' v ⟨ρ', h'⟩)
    (eP : ∀ (r : ResUT Loc Val K) (hr : r.InStratum s) (hr' : r.InStratum s') (w : Val),
        P w ⟨r, hr⟩ ↔ P' w ⟨r, hr'⟩) :
    CellUT.mutOf s v ρ h P hP = CellUT.mutOf s' v ρ' h' P' hP' := by
  subst eρ
  exact CellUT.mutOf_congr e v ρ h h' P P' hP hP' eP

/-- `ΦU(mut(β̄, v, ρ, P̂)) = mut(⊔β̄, v, ΦU ρ, P̂ ∘ ΦU⁻¹)`. -/
theorem ΦU_mutOf (s : TSet) [Fact (chain.Anti s)] (v : Val) (ρ : ResUT Loc Val chain)
    (h : ρ.InStratum s) (P : Val → SPropST Loc Val chain s) (hw : P v ⟨ρ, h⟩) :
    ΦU (CellUT.mutOf s v ρ h P hw) =
      CellU.mutOf s.jn v (ρ.map ΦU) (ΦU_map_inStratum h)
        (fun w r => ∃ (r₀ : ResUT Loc Val chain) (h₀ : r₀.InStratum s),
          r₀.map ΦU = r.val ∧ P w ⟨r₀, h₀⟩) ⟨ρ, h, rfl, hw⟩ := by
  have eρ : (ResST.toRes ⟨ρ, h⟩).map (Phi s).1 = ρ.map ΦU := by
    rw [Phi_map, ResST.toU_toRes]
  have eP : ∀ (r : ResU Loc Val) (hr : r.InStratum s.jn) (hr' : r.InStratum s.jn) (w : Val),
      (∃ r₀ : ResT Loc Val chain s, r₀.map (Phi s).1 = r ∧ P w r₀.toS) ↔
      (∃ (r₀ : ResUT Loc Val chain) (h₀ : r₀.InStratum s), r₀.map ΦU = r ∧ P w ⟨r₀, h₀⟩) := by
    intro r _ _ w
    constructor
    · rintro ⟨r₀, e, hP⟩
      exact ⟨r₀.toU, r₀.toU_inStratum, by rw [← Phi_map]; exact e, hP⟩
    · rintro ⟨r₀, h₀, e, hP⟩
      refine ⟨ResST.toRes ⟨r₀, h₀⟩, ?_, ?_⟩
      · rw [Phi_map, ResST.toU_toRes]; exact e
      · rw [ResST.toS_toRes]; exact hP
  exact CellU.mutOf_congr' (b := s.jn) (b' := s.jn) rfl (v := v)
    (ρ := (ResST.toRes ⟨ρ, h⟩).map (Phi s).1) (ρ' := ρ.map ΦU) eρ
    (ResU.inStratum_map _ (Phi s).2 _) (ΦU_map_inStratum h)
    (fun w r => ∃ r₀ : ResT Loc Val chain s, r₀.map (Phi s).1 = r.val ∧ P w r₀.toS)
    (fun w r => ∃ (r₀ : ResUT Loc Val chain) (h₀ : r₀.InStratum s),
      r₀.map ΦU = r.val ∧ P w ⟨r₀, h₀⟩)
    ⟨ResST.toRes ⟨ρ, h⟩, rfl, by rw [ResST.toS_toRes]; exact hw⟩ ⟨ρ, h, rfl, hw⟩
    (fun r hr hr' w => eP r hr hr' w)

theorem ΨU_map_inStratum_ofLSet {L : LSet} {ρ : ResU Loc Val} (h : ρ.InStratum L.join) :
    ResUT.InStratum (TSet.ofLSet L) (ρ.map ΨU) :=
  fun l ψ e => inStratum_toTSet_of_join (ΨU_map_inStratum h l ψ e)

/-- `ΨU(imm(ᾱ, v, ρ)) = imm(ᾱ, v, ΨU ρ)`. -/
theorem ΨU_immOf (L : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum L.join) :
    ΨU (CellU.immOf L v ρ h) =
      CellUT.immOf (TSet.ofLSet L) v (ρ.map ΨU) (ΨU_map_inStratum_ofLSet h) := by
  refine CellUT.immOf_congr rfl rfl ?_ _ _
  show (ResS.toRes ⟨ρ, h⟩).map (Psi L.join).1 = ρ.map ΨU
  rw [Psi_map, ResS.toU_toRes]

/-- `ΨU(mut(β, v, ρ, P̂)) = mut({β}, v, ΨU ρ, P̂ ∘ ΨU⁻¹)`. -/
theorem ΨU_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    ΨU (CellU.mutOf b v ρ h P hw) =
      CellUT.mutOf (TSet.single b) v (ρ.map ΨU) (ΨU_map_inStratum h)
        (fun w r => ∃ (r₀ : ResU Loc Val) (h₀ : r₀.InStratum b),
          r₀.map ΨU = r.val ∧ P w ⟨r₀, h₀⟩) ⟨ρ, h, rfl, hw⟩ := by
  have eρ : (ResS.toRes ⟨ρ, h⟩).map (Psi b).1 = ρ.map ΨU := by
    rw [Psi_map, ResS.toU_toRes]
  have eP : ∀ (r : ResUT Loc Val chain) (hr hr' : r.InStratum (TSet.single b)) (w : Val),
      (∃ r₀ : Res Loc Val b, r₀.map (Psi b).1 = r ∧ P w r₀.toS) ↔
      (∃ (r₀ : ResU Loc Val) (h₀ : r₀.InStratum b), r₀.map ΨU = r ∧ P w ⟨r₀, h₀⟩) := by
    intro r _ _ w
    constructor
    · rintro ⟨r₀, e, hP⟩
      exact ⟨r₀.toU, r₀.toU_inStratum, by rw [← Psi_map]; exact e, hP⟩
    · rintro ⟨r₀, h₀, e, hP⟩
      refine ⟨ResS.toRes ⟨r₀, h₀⟩, ?_, ?_⟩
      · rw [Psi_map, ResS.toU_toRes]; exact e
      · rw [ResS.toS_toRes]; exact hP
  exact CellUT.mutOf_congr' (s := TSet.single b) (s' := TSet.single b) rfl (v := v)
    (ρ := (ResS.toRes ⟨ρ, h⟩).map (Psi b).1) (ρ' := ρ.map ΨU) eρ
    (ResUT.inStratum_map _ (Psi b).2 _) (ΨU_map_inStratum h)
    (fun w r => ∃ r₀ : Res Loc Val b, r₀.map (Psi b).1 = r.val ∧ P w r₀.toS)
    (fun w r => ∃ (r₀ : ResU Loc Val) (h₀ : r₀.InStratum b), r₀.map ΨU = r.val ∧ P w ⟨r₀, h₀⟩)
    ⟨ResS.toRes ⟨ρ, h⟩, rfl, by rw [ResS.toS_toRes]; exact hw⟩ ⟨ρ, h, rfl, hw⟩
    (fun r hr hr' w => eP r hr hr' w)

/-! ### The round trips -/

theorem roundT {T : TSet} {r : ResUT Loc Val chain} (hr : r.InStratum T)
    (H : ∀ c : CellUT Loc Val chain, c.InStratum T → ΨU (ΦU c) = c) :
    (r.map ΦU).map ΨU = r := by
  rw [PMap.map_map]
  conv_rhs => rw [← PMap.map_id' r]
  exact PMap.map_congr r fun l c e => H c (hr l c e)

theorem roundP {b : Life} {r : ResU Loc Val} (hr : r.InStratum b)
    (H : ∀ d : CellU Loc Val, d.InStratum b → ΦU (ΨU d) = d) :
    (r.map ΨU).map ΦU = r := by
  rw [PMap.map_map]
  conv_rhs => rw [← PMap.map_id' r]
  exact PMap.map_congr r fun l c e => H c (hr l c e)

/-- `ΨU (ΦU ψ) = ψ`, given it on the stratum of `ψ`'s witness. -/
theorem ΨU_ΦU_of (ψ : CellUT Loc Val chain)
    (H : ∀ T, ψ.lsOf = some T → ∀ c : CellUT Loc Val chain, c.InStratum T → ΨU (ΦU c) = c) :
    ΨU (ΦU ψ) = ψ := by
  cases ψ with
  | own v => rfl
  | imm i =>
      have Hi := H i.ls rfl
      rw [← ImmT.immOf_eta' i, ΦU_immOf, ΨU_immOf]
      exact CellUT.immOf_congr (TSet.ofLSet_toLSet i.ls) rfl
        (roundT i.ρ.toU_inStratum Hi) _ _
  | «mut» m =>
      have Hm := H m.ls rfl
      have : Fact (chain.Anti m.ls) := ⟨m.anti⟩
      rw [← MutT.mutOf_eta m, ΦU_mutOf, ΨU_mutOf]
      refine CellUT.mutOf_congr' (chain_anti_iff.mp m.anti).symm
        (roundT m.ρ.toU_inStratum Hm) _ _ _ _ _ _ ?_
      intro r hr hr' w
      constructor
      · rintro ⟨r₀, h₀, e₀, r₁, h₁, e₁, hP⟩
        have er : r = r₁ := by
          have e₀' : r₀.map ΨU = r := e₀
          have e₁' : r₁.map ΦU = r₀ := e₁
          rw [← e₀', ← e₁']; exact roundT h₁ Hm
        subst er
        exact hP
      · intro hP
        exact ⟨r.map ΦU, ΦU_map_inStratum hr', roundT hr' Hm, r, hr', rfl, hP⟩

/-- The stratum of a printed cell's witness. -/
def CellU.payAt : CellU Loc Val → Option Life
  | .own _ => none
  | .imm i => some i.ls.join
  | .mut m => some m.β

/-- `ΦU (ΨU c) = c`, given it on the stratum of `c`'s witness. -/
theorem ΦU_ΨU_of (c : CellU Loc Val)
    (H : ∀ b, CellU.payAt c = some b → ∀ d : CellU Loc Val, d.InStratum b → ΦU (ΨU d) = d) :
    ΦU (ΨU c) = c := by
  cases c with
  | own v => rfl
  | imm i =>
      have Hi := H i.ls.join rfl
      rw [← ImmU.immOf_eta' i, ΨU_immOf, ΦU_immOf]
      exact CellU.immOf_congr (TSet.toLSet_ofLSet i.ls) rfl
        (roundP i.ρ.toU_inStratum Hi) _ _
  | «mut» m =>
      have Hm := H m.β rfl
      rw [← MutU.mutOf_eta m, ΨU_mutOf, ΦU_mutOf]
      refine CellU.mutOf_congr' (TSet.jn_single m.β) (roundP m.ρ.toU_inStratum Hm)
        _ _ _ _ _ _ ?_
      intro r hr hr' w
      constructor
      · rintro ⟨r₀, h₀, e₀, r₁, h₁, e₁, hP⟩
        have er : r = r₁ := by
          have e₀' : r₀.map ΦU = r := e₀
          have e₁' : r₁.map ΨU = r₀ := e₁
          rw [← e₀', ← e₁']; exact roundP h₁ Hm
        subst er
        exact hP
      · intro hP
        refine ⟨r.map ΨU, ΨU_map_inStratum hr', roundP hr' Hm, r, hr', rfl, hP⟩

theorem ΨU_ΦU_strat (S : TSet) :
    ∀ c : CellUT Loc Val chain, c.InStratum S → ΨU (ΦU c) = c := by
  induction S using chain.above_wf.induction with
  | _ S ih =>
      intro c hc
      refine ΨU_ΦU_of c fun T hT d hd => ih T ?_ d hd
      cases c with
      | own v => exact absurd hT (by simp [CellUT.lsOf])
      | imm i => cases hT; exact hc
      | «mut» m => cases hT; exact hc

/-- **`ΨU ∘ ΦU = id`.** -/
theorem ΨU_ΦU (ψ : CellUT Loc Val chain) : ΨU (ΦU ψ) = ψ :=
  ΨU_ΦU_of ψ fun T _ c hc => ΨU_ΦU_strat T c hc

theorem ΦU_ΨU_strat (a : Life) :
    ∀ d : CellU Loc Val, d.InStratum a → ΦU (ΨU d) = d := by
  induction a using (invImage OrderDual.ofDual Nat.lt_wfRel).wf.induction with
  | _ a ih =>
      intro d hd
      refine ΦU_ΨU_of d fun b hb e he => ih b ?_ e he
      cases d with
      | own v => exact absurd hb (by simp [CellU.payAt])
      | imm i =>
          cases hb
          exact (lt_of_lt_of_le hd i.ls.meet_le_join : a < i.ls.join)
      | «mut» m => cases hb; exact (hd : a < m.β)

/-- **`ΦU ∘ ΨU = id`.** -/
theorem ΦU_ΨU (c : CellU Loc Val) : ΦU (ΨU c) = c :=
  ΦU_ΨU_of c fun b _ d hd => ΦU_ΨU_strat b d hd

/-- The tree-stratified carrier at the chain is the printed carrier. -/
def chainEquiv : CellUT Loc Val chain ≃ CellU Loc Val where
  toFun := ΦU
  invFun := ΨU
  left_inv := ΨU_ΦU
  right_inv := ΦU_ΨU

end BoCa.Fig16.Tree

end
