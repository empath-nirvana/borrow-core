import Support.Model.Tree.Carrier

/-!
# `▶◀`, `●`, `⋈` and `○` on the tree-stratified carrier

Rows 5.13–5.16 over `CellUT K`, and the cell-level laws the printed proofs of Lemmas 6.2 and 6.3
rest on (`Support/Model/Composition.lean`, `Support/Model/Algebra.lean`), each by the printed
proof.

**Row 5.16 clause 3, restated.** `mut(β̄₁, v, ρ, P̂) ○ mut(β̄₂, v, ρ, Q̂) = mut(min(β̄₁ ∪ β̄₂), v, ρ,
P̂ ∧ Q̂)`, `P̂ ∧ Q̂` read on `Res_{min(β̄₁ ∪ β̄₂)}` as the printed `SPropS.conj` reads it on
`Res_{α ⊓ β}`: each conjunct extended by falsity outside its own stratum (row 5.57). The
printed proof of 6.3 cites "associativity of `⊓`" for this clause; here it is
`WCactus.minS_assoc`. Clauses (1) and (3) agree at equal cells because `β̄` is an antichain
(`WCactus.minS_self`), as the printed ones agree by `α ⊓ α = α`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type} {K : WCactus}

/-! ### Row 5.57 in the tree: `SProp_S ⊆ SProp_{S'}` -/

/-- Extension by falsity outside `Res_s`. -/
def SPropST.embed {s s' : TSet} (P : Val → SPropST Loc Val K s) : Val → SPropST Loc Val K s' :=
  fun v r => ∃ h : r.val.InStratum s, P v ⟨r.val, h⟩

/-- `P̂ ∧ Q̂`, the invariant clause 3 builds, at the stratum `min(β̄₁ ∪ β̄₂)`. -/
def SPropST.conj {s t : TSet} (P : Val → SPropST Loc Val K s) (Q : Val → SPropST Loc Val K t) :
    Val → SPropST Loc Val K (K.minS (s ∪ t)) :=
  fun v r => SPropST.embed P v r ∧ SPropST.embed Q v r

theorem SPropST.conj_holds {s t : TSet} {P : Val → SPropST Loc Val K s}
    {Q : Val → SPropST Loc Val K t} {v : Val} {ρ : ResUT Loc Val K}
    (hs : ρ.InStratum s) (ht : ρ.InStratum t) (hP : P v ⟨ρ, hs⟩) (hQ : Q v ⟨ρ, ht⟩) :
    SPropST.conj P Q v ⟨ρ, hs.minUnion ht⟩ := ⟨⟨hs, hP⟩, ⟨ht, hQ⟩⟩

/-- `(P̂ ∧ Q̂) ∧ R̂` and `P̂ ∧ (Q̂ ∧ R̂)` are the same subset of `Res`. -/
theorem SPropST.conj_assoc {s t u : TSet} (P : Val → SPropST Loc Val K s)
    (Q : Val → SPropST Loc Val K t) (T : Val → SPropST Loc Val K u) (r : ResUT Loc Val K)
    (hr : r.InStratum (K.minS (K.minS (s ∪ t) ∪ u)))
    (hr' : r.InStratum (K.minS (s ∪ K.minS (t ∪ u)))) (w : Val) :
    SPropST.conj (SPropST.conj P Q) T w ⟨r, hr⟩ ↔
      SPropST.conj P (SPropST.conj Q T) w ⟨r, hr'⟩ := by
  simp only [SPropST.conj, SPropST.embed]
  constructor
  · rintro ⟨⟨_, ⟨h₁, hp⟩, ⟨h₂, hq⟩⟩, ⟨h₃, ht⟩⟩
    exact ⟨⟨h₁, hp⟩, ⟨h₂.minUnion h₃, ⟨h₂, hq⟩, ⟨h₃, ht⟩⟩⟩
  · rintro ⟨⟨h₁, hp⟩, ⟨_, ⟨h₂, hq⟩, ⟨h₃, ht⟩⟩⟩
    exact ⟨⟨h₁.minUnion h₂, ⟨h₁, hp⟩, ⟨h₂, hq⟩⟩, ⟨h₃, ht⟩⟩

theorem SPropST.conj_comm {s t : TSet} (P : Val → SPropST Loc Val K s)
    (Q : Val → SPropST Loc Val K t) (r : ResUT Loc Val K)
    (hr : r.InStratum (K.minS (s ∪ t))) (hr' : r.InStratum (K.minS (t ∪ s))) (w : Val) :
    SPropST.conj P Q w ⟨r, hr⟩ ↔ SPropST.conj Q P w ⟨r, hr'⟩ :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ### Rows 5.13 and 5.15: `▶◀` and `●` -/

/-- `ψ₁ ▶◀ ψ₂` (row 5.13). -/
def CellUT.CompatS (ψ₁ ψ₂ : CellUT Loc Val K) : Prop :=
  ∃ (s₁ s₂ : TSet) (v : Val) (ρ : ResUT Loc Val K)
    (h₁ : ρ.InStratum s₁) (h₂ : ρ.InStratum s₂),
    ψ₁ = CellUT.immOf s₁ v ρ h₁ ∧ ψ₂ = CellUT.immOf s₂ v ρ h₂

/-- `ψ₁ ● ψ₂ = ψ` (row 5.15), as a graph. -/
def CellUT.CompS (ψ₁ ψ₂ ψ : CellUT Loc Val K) : Prop :=
  ∃ (s₁ s₂ : TSet) (v : Val) (ρ : ResUT Loc Val K)
    (h₁ : ρ.InStratum s₁) (h₂ : ρ.InStratum s₂) (h₃ : ρ.InStratum (s₁ ∪ s₂)),
    ψ₁ = CellUT.immOf s₁ v ρ h₁ ∧ ψ₂ = CellUT.immOf s₂ v ρ h₂ ∧
    ψ = CellUT.immOf (s₁ ∪ s₂) v ρ h₃

theorem ImmT.immOf_eta (i : ImmT Loc Val K) :
    CellUT.immOf i.ls i.v i.res i.ρ.toU_inStratum = .imm i := by
  show CellUT.imm _ = CellUT.imm i
  refine congrArg CellUT.imm (ImmT.ext' rfl rfl ?_)
  simp only [heq_eq_eq]
  exact ResT.toRes_toS i.ρ

theorem CellUT.CompatS.imm_imm {i₁ i₂ : ImmT Loc Val K}
    (h : CellUT.CompatS (.imm i₁) (.imm i₂)) : i₁.v = i₂.v ∧ i₁.res = i₂.res := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  rw [← ImmT.immOf_eta i₁] at e₁
  rw [← ImmT.immOf_eta i₂] at e₂
  obtain ⟨-, hv₁, hρ₁⟩ := CellUT.immOf_inj e₁
  obtain ⟨-, hv₂, hρ₂⟩ := CellUT.immOf_inj e₂
  exact ⟨hv₁.trans hv₂.symm, hρ₁.trans hρ₂.symm⟩

theorem CellUT.CompatS.symm {ψ₁ ψ₂ : CellUT Loc Val K} (h : ψ₁.CompatS ψ₂) :
    ψ₂.CompatS ψ₁ := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  exact ⟨s₂, s₁, v, ρ, h₂, h₁, e₂, e₁⟩

theorem CellUT.CompatS.kinds {ψ₁ ψ₂ : CellUT Loc Val K} (h : ψ₁.CompatS ψ₂) :
    ψ₁.kind = Kind.imm ∧ ψ₂.kind = Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  exact ⟨by rw [e₁]; rfl, by rw [e₂]; rfl⟩

/-- `ψ₁ ● ψ₂` as a function of its `▶◀` guard. -/
def CellUT.compS : (ψ₁ ψ₂ : CellUT Loc Val K) → ψ₁.CompatS ψ₂ → CellUT Loc Val K
  | .imm i₁, .imm i₂, h =>
      CellUT.immOf (i₁.ls ∪ i₂.ls) i₁.v i₁.res
        (by
          have e : i₁.res = i₂.res := (CellUT.CompatS.imm_imm h).2
          have k₂ : ResUT.InStratum i₂.ls i₁.res := by
            rw [e]; exact i₂.ρ.toU_inStratum
          exact ResUT.inStratum_union_iff.mpr ⟨i₁.ρ.toU_inStratum, k₂⟩)
  | .own _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellUT.immOf] at e)
  | .mut _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellUT.immOf] at e)
  | .imm _, .own _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellUT.immOf] at e)
  | .imm _, .mut _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellUT.immOf] at e)

theorem CellUT.compS_spec : ∀ (ψ₁ ψ₂ : CellUT Loc Val K) (h : ψ₁.CompatS ψ₂),
    CellUT.CompS ψ₁ ψ₂ (CellUT.compS ψ₁ ψ₂ h)
  | .imm i₁, .imm i₂, h => by
      have hv : i₁.v = i₂.v := (CellUT.CompatS.imm_imm h).1
      have hρ : i₁.res = i₂.res := (CellUT.CompatS.imm_imm h).2
      have k₁ : ResUT.InStratum i₁.ls i₁.res := i₁.ρ.toU_inStratum
      have k₂ : ResUT.InStratum i₂.ls i₁.res := by rw [hρ]; exact i₂.ρ.toU_inStratum
      refine ⟨i₁.ls, i₂.ls, i₁.v, i₁.res, k₁, k₂, ResUT.inStratum_union_iff.mpr ⟨k₁, k₂⟩,
        (ImmT.immOf_eta i₁).symm, ?_, rfl⟩
      exact ((CellUT.immOf_congr rfl hv hρ k₂ i₂.ρ.toU_inStratum).trans
        (ImmT.immOf_eta i₂)).symm
  | .own _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellUT.immOf] at e)
  | .mut _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellUT.immOf] at e)
  | .imm _, .own _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellUT.immOf] at e)
  | .imm _, .mut _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellUT.immOf] at e)

/-- `●` is single-valued. -/
theorem CellUT.CompS.functional {ψ₁ ψ₂ ψ ψ' : CellUT Loc Val K}
    (h : CellUT.CompS ψ₁ ψ₂ ψ) (h' : CellUT.CompS ψ₁ ψ₂ ψ') : ψ = ψ' := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  obtain ⟨t₁, t₂, w, σ, m₁, m₂, m₃, f₁, f₂, f₃⟩ := h'
  obtain ⟨hs₁, hv₁, hρ₁⟩ := CellUT.immOf_inj (e₁.symm.trans f₁)
  obtain ⟨hs₂, -, -⟩ := CellUT.immOf_inj (e₂.symm.trans f₂)
  subst hs₁; subst hs₂; subst hv₁; subst hρ₁
  rw [e₃, f₃]

theorem CellUT.compS_immOf {s₁ s₂ : TSet} {v : Val} {ρ : ResUT Loc Val K}
    {h₁ : ρ.InStratum s₁} {h₂ : ρ.InStratum s₂}
    (h : CellUT.CompatS (CellUT.immOf s₁ v ρ h₁) (CellUT.immOf s₂ v ρ h₂))
    (h₃ : ρ.InStratum (s₁ ∪ s₂)) :
    CellUT.compS _ _ h = CellUT.immOf (s₁ ∪ s₂) v ρ h₃ :=
  CellUT.CompS.functional (CellUT.compS_spec _ _ h) ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩

theorem CellUT.CompS.compat {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ψ₁.CompatS ψ₂ := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, -, e₁, e₂, -⟩ := h
  exact ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩

/-- `ψ ● ψ = ψ`. -/
theorem CellUT.compS_self (ψ : CellUT Loc Val K) (h : ψ.CompatS ψ) : CellUT.compS ψ ψ h = ψ := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := CellUT.compS_spec ψ ψ h
  obtain ⟨hs, -, -⟩ := CellUT.immOf_inj (e₁.symm.trans e₂)
  subst hs
  rw [e₃, e₁]
  exact CellUT.immOf_congr (TSet.union_self s₁) rfl rfl k₃ k₁

/-- `●` is commutative on cells: "`∪` is commutative". -/
theorem CellUT.CompS.comm {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    CellUT.CompS ψ₂ ψ₁ ψ := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := h
  have hu : s₁ ∪ s₂ = s₂ ∪ s₁ := TSet.union_comm s₁ s₂
  refine ⟨s₂, s₁, v, ρ, h₂, h₁, hu ▸ h₃, e₂, e₁, ?_⟩
  rw [e₃]
  exact CellUT.immOf_congr hu rfl rfl h₃ _

/-- `●` is associative on cells: "associativity follows from the associativity of `∪`". -/
theorem CellUT.compS_assoc (ψ₁ ψ₂ ψ₃ ω : CellUT Loc Val K) :
    (∃ χ, CellUT.CompS ψ₂ ψ₃ χ ∧ CellUT.CompS ψ₁ χ ω) ↔
    (∃ υ, CellUT.CompS ψ₁ ψ₂ υ ∧ CellUT.CompS υ ψ₃ ω) := by
  constructor
  · rintro ⟨χ, ⟨t₂, t₃, v, ρ, k₂, k₃, k₂₃, e₂, e₃, eχ⟩,
      ⟨s₁, s', u, σ, m₁, m', m'', f₁, fχ, fω⟩⟩
    obtain ⟨hs, hv, hρ⟩ := CellUT.immOf_inj (eχ.symm.trans fχ)
    subst hs; subst hv; subst hρ
    have h₁₂ : ρ.InStratum (s₁ ∪ t₂) := ResUT.inStratum_union_iff.mpr ⟨m₁, k₂⟩
    refine ⟨CellUT.immOf (s₁ ∪ t₂) v ρ h₁₂,
      ⟨s₁, t₂, v, ρ, m₁, k₂, h₁₂, f₁, e₂, rfl⟩,
      ⟨s₁ ∪ t₂, t₃, v, ρ, h₁₂, k₃, ?_, rfl, e₃, ?_⟩⟩
    · exact (TSet.union_assoc s₁ t₂ t₃) ▸ m''
    · rw [fω]
      exact CellUT.immOf_congr (TSet.union_assoc s₁ t₂ t₃).symm rfl rfl m'' _
  · rintro ⟨υ, ⟨s₁, t₂, v, ρ, m₁, k₂, m₁₂, f₁, e₂, eυ⟩,
      ⟨s', t₃, u, σ, m', k₃, m'', fυ, e₃, fω⟩⟩
    obtain ⟨hs, hv, hρ⟩ := CellUT.immOf_inj (eυ.symm.trans fυ)
    subst hs; subst hv; subst hρ
    have h₂₃ : ρ.InStratum (t₂ ∪ t₃) := ResUT.inStratum_union_iff.mpr ⟨k₂, k₃⟩
    refine ⟨CellUT.immOf (t₂ ∪ t₃) v ρ h₂₃,
      ⟨t₂, t₃, v, ρ, k₂, k₃, h₂₃, e₂, e₃, rfl⟩,
      ⟨s₁, t₂ ∪ t₃, v, ρ, m₁, h₂₃, ?_, f₁, rfl, ?_⟩⟩
    · exact (TSet.union_assoc s₁ t₂ t₃).symm ▸ m''
    · rw [fω]
      exact CellUT.immOf_congr (TSet.union_assoc s₁ t₂ t₃) rfl rfl m'' _

theorem CellUT.CompS.erase {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ψ.erase = ψ₁.erase ∧ ψ.erase = ψ₂.erase := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := h
  subst e₁; subst e₂; subst e₃
  exact ⟨rfl, rfl⟩

theorem CellUT.CompS.kind {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ψ.kind = Kind.imm := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := h
  rw [e₃]; rfl

theorem CellUT.CompS.wit {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ψ.wit = ψ₁.wit ∧ ψ.wit = ψ₂.wit := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := h
  subst e₁; subst e₂; subst e₃
  simp

/-! ### Row 5.16: `○`, clause 3 restated -/

/-- `ψ₁ ○ ψ₂ = ψ`, as a graph. -/
inductive CellUT.CompR : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop where
  /-- (1) `ψ₁` if `ψ₁ = ψ₂`. -/
  | same (ψ : CellUT Loc Val K) : CellUT.CompR ψ ψ ψ
  /-- (2) `ψ₁ ● ψ₂` if `ψ₁ ▶◀ ψ₂`. -/
  | strict {ψ₁ ψ₂ : CellUT Loc Val K} (h : ψ₁.CompatS ψ₂) :
      CellUT.CompR ψ₁ ψ₂ (CellUT.compS ψ₁ ψ₂ h)
  /-- (3) `mut(min(β̄₁ ∪ β̄₂), v, ρ, P̂ ∧ Q̂)`. -/
  | mutMut (s t : TSet) [Fact (K.Anti s)] [Fact (K.Anti t)] (v : Val) (ρ : ResUT Loc Val K)
      (hs : ρ.InStratum s) (ht : ρ.InStratum t)
      (P : Val → SPropST Loc Val K s) (Q : Val → SPropST Loc Val K t)
      (hP : P v ⟨ρ, hs⟩) (hQ : Q v ⟨ρ, ht⟩) :
      CellUT.CompR (CellUT.mutOf s v ρ hs P hP) (CellUT.mutOf t v ρ ht Q hQ)
        (CellUT.mutOf (K.minS (s ∪ t)) v ρ (hs.minUnion ht) (SPropST.conj P Q)
          (SPropST.conj_holds hs ht hP hQ))
  /-- (4), `i = 1`. -/
  | mutOwn (s : TSet) [Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K) (hs : ρ.InStratum s)
      (P : Val → SPropST Loc Val K s) (hP : P v ⟨ρ, hs⟩) :
      CellUT.CompR (CellUT.mutOf s v ρ hs P hP) (CellUT.ownOf v)
        (CellUT.mutOf s v ρ hs P hP)
  /-- (4), `i = 2`. -/
  | ownMut (s : TSet) [Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K) (hs : ρ.InStratum s)
      (P : Val → SPropST Loc Val K s) (hP : P v ⟨ρ, hs⟩) :
      CellUT.CompR (CellUT.ownOf v) (CellUT.mutOf s v ρ hs P hP)
        (CellUT.mutOf s v ρ hs P hP)
  /-- (5), `i = 1`, against `own(v)`. -/
  | immOwn (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s) :
      CellUT.CompR (CellUT.immOf s v ρ h) (CellUT.ownOf v) (CellUT.immOf s v ρ h)
  /-- (5), `i = 2`, against `own(v)`. -/
  | ownImm (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s) :
      CellUT.CompR (CellUT.ownOf v) (CellUT.immOf s v ρ h) (CellUT.immOf s v ρ h)
  /-- (5), `i = 1`, against `mut(β̄, v, ρ, P̂)`. -/
  | immMut (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s)
      (b : TSet) [Fact (K.Anti b)] (hb : ρ.InStratum b) (P : Val → SPropST Loc Val K b)
      (hP : P v ⟨ρ, hb⟩) :
      CellUT.CompR (CellUT.immOf s v ρ h) (CellUT.mutOf b v ρ hb P hP)
        (CellUT.immOf s v ρ h)
  /-- (5), `i = 2`, against `mut(β̄, v, ρ, P̂)`. -/
  | mutImm (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s)
      (b : TSet) [Fact (K.Anti b)] (hb : ρ.InStratum b) (P : Val → SPropST Loc Val K b)
      (hP : P v ⟨ρ, hb⟩) :
      CellUT.CompR (CellUT.mutOf b v ρ hb P hP) (CellUT.immOf s v ρ h)
        (CellUT.immOf s v ρ h)

/-- `ψ₁ ⋈ ψ₂`, the domain of `○` (row 5.14, read as in the printed carrier). -/
def CellUT.CompatR (ψ₁ ψ₂ : CellUT Loc Val K) : Prop := ∃ ψ, CellUT.CompR ψ₁ ψ₂ ψ

/-- Clauses (1) and (3) agree at two equal `mut` cells: `min(β̄ ∪ β̄) = β̄` for an antichain,
where the printed proof has `α ⊓ α = α`. -/
theorem CellUT.compR_same_mutMut (s : TSet) [Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K)
    (hs : ρ.InStratum s) (P : Val → SPropST Loc Val K s) (hP : P v ⟨ρ, hs⟩) :
    CellUT.mutOf (K.minS (s ∪ s)) v ρ (hs.minUnion hs) (SPropST.conj P P)
        (SPropST.conj_holds hs hs hP hP)
      = CellUT.mutOf s v ρ hs P hP := by
  refine CellUT.mutOf_congr (K.minS_self Fact.out) v ρ _ _ _ _ _ _ ?_
  intro r hr hr' w
  constructor
  · rintro ⟨⟨k, hk⟩, -⟩; exact hk
  · intro hw; exact ⟨⟨hr', hw⟩, ⟨hr', hw⟩⟩

/-- A weak inversion for `○`, as printed (`CellU.CompR.inv`). -/
theorem CellUT.CompR.inv {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    (ψ₁ = ψ₂ ∧ ψ = ψ₁)
    ∨ (∃ k : ψ₁.CompatS ψ₂, ψ = CellUT.compS ψ₁ ψ₂ k)
    ∨ (∃ (s t : TSet) (_ : Fact (K.Anti s)) (_ : Fact (K.Anti t)) (v : Val) (ρ : ResUT Loc Val K)
        (hs : ρ.InStratum s) (ht : ρ.InStratum t)
        (P : Val → SPropST Loc Val K s) (Q : Val → SPropST Loc Val K t)
        (hP : P v ⟨ρ, hs⟩) (hQ : Q v ⟨ρ, ht⟩),
        ψ₁ = CellUT.mutOf s v ρ hs P hP ∧ ψ₂ = CellUT.mutOf t v ρ ht Q hQ ∧
        ψ = CellUT.mutOf (K.minS (s ∪ t)) v ρ (hs.minUnion ht)
              (SPropST.conj P Q) (SPropST.conj_holds hs ht hP hQ))
    ∨ (ψ = ψ₁ ∧ ψ₂.kind = Kind.own ∧ ψ₁.kind ≠ Kind.own)
    ∨ (ψ = ψ₂ ∧ ψ₁.kind = Kind.own ∧ ψ₂.kind ≠ Kind.own)
    ∨ (ψ = ψ₁ ∧ ψ₁.kind = Kind.imm ∧ ψ₂.kind = Kind.mut)
    ∨ (ψ = ψ₂ ∧ ψ₁.kind = Kind.mut ∧ ψ₂.kind = Kind.imm) := by
  cases h with
  | same χ => exact Or.inl ⟨rfl, rfl⟩
  | strict k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | mutMut s t v ρ hs ht P Q hP hQ =>
      exact Or.inr (Or.inr (Or.inl ⟨s, t, inferInstance, inferInstance, v, ρ, hs, ht, P, Q, hP, hQ,
        rfl, rfl, rfl⟩))
  | mutOwn =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩)))
  | ownMut =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩))))
  | immOwn =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩)))
  | ownImm =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by simp⟩))))
  | immMut =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))))
  | mutImm =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))))

/-- Clause (3) applied to two cells that clause (1) also matches. -/
theorem CellUT.compR_mutMut_of_eq {s t : TSet} [Fact (K.Anti s)] [Fact (K.Anti t)] {v : Val}
    {ρ : ResUT Loc Val K} {hs : ρ.InStratum s} {ht : ρ.InStratum t}
    {P : Val → SPropST Loc Val K s} {Q : Val → SPropST Loc Val K t}
    {hP : P v ⟨ρ, hs⟩} {hQ : Q v ⟨ρ, ht⟩}
    (e : CellUT.mutOf s v ρ hs P hP = CellUT.mutOf t v ρ ht Q hQ) :
    CellUT.mutOf (K.minS (s ∪ t)) v ρ (hs.minUnion ht) (SPropST.conj P Q)
        (SPropST.conj_holds hs ht hP hQ)
      = CellUT.mutOf t v ρ ht Q hQ := by
  obtain ⟨hst, -, -, hPQ⟩ := CellUT.mutOf_injSet e
  subst hst
  have hPQ' : P = Q := funext fun w => funext fun r => propext (hPQ r.val r.property r.property w)
  subst hPQ'
  exact CellUT.compR_same_mutMut s v ρ ht P hQ

/-- Clause (3) is determined by its two operands. -/
theorem CellUT.compR_mutMut_det {s t s' t' : TSet} [Fact (K.Anti s)] [Fact (K.Anti t)]
    [Fact (K.Anti s')] [Fact (K.Anti t')] {v v' : Val} {ρ ρ' : ResUT Loc Val K}
    {hs : ρ.InStratum s} {ht : ρ.InStratum t} {hs' : ρ'.InStratum s'} {ht' : ρ'.InStratum t'}
    {P : Val → SPropST Loc Val K s} {Q : Val → SPropST Loc Val K t}
    {P' : Val → SPropST Loc Val K s'} {Q' : Val → SPropST Loc Val K t'}
    {hP : P v ⟨ρ, hs⟩} {hQ : Q v ⟨ρ, ht⟩} {hP' : P' v' ⟨ρ', hs'⟩} {hQ' : Q' v' ⟨ρ', ht'⟩}
    (e1 : CellUT.mutOf s v ρ hs P hP = CellUT.mutOf s' v' ρ' hs' P' hP')
    (e2 : CellUT.mutOf t v ρ ht Q hQ = CellUT.mutOf t' v' ρ' ht' Q' hQ') :
    CellUT.mutOf (K.minS (s ∪ t)) v ρ (hs.minUnion ht) (SPropST.conj P Q)
        (SPropST.conj_holds hs ht hP hQ)
      = CellUT.mutOf (K.minS (s' ∪ t')) v' ρ' (hs'.minUnion ht')
          (SPropST.conj P' Q') (SPropST.conj_holds hs' ht' hP' hQ') := by
  obtain ⟨hss, hv, hρ, hPP⟩ := CellUT.mutOf_injSet e1
  subst hss; subst hv; subst hρ
  have hPP' : P = P' :=
    funext fun w => funext fun r => propext (hPP r.val r.property r.property w)
  subst hPP'
  obtain ⟨htt, -, -, hQQ⟩ := CellUT.mutOf_injSet e2
  subst htt
  have hQQ' : Q = Q' :=
    funext fun w => funext fun r => propext (hQQ r.val r.property r.property w)
  subst hQQ'
  rfl

set_option maxHeartbeats 1000000 in
/-- `○` is single-valued: its clauses overlap only at (1)/(2) and (1)/(3), and agree there. -/
theorem CellUT.CompR.functional {ψ₁ ψ₂ ψ ψ' : CellUT Loc Val K}
    (h : CellUT.CompR ψ₁ ψ₂ ψ) (h' : CellUT.CompR ψ₁ ψ₂ ψ') : ψ = ψ' := by
  have H := h.inv
  have H' := h'.inv
  clear h h'
  rcases H with ⟨e12, rfl⟩ | ⟨k, rfl⟩ |
      ⟨s, t, as, at_, v, ρ, hs, ht, P, Q, hP, hQ, rfl, e2, rfl⟩ |
      ⟨rfl, ka, kb⟩ | ⟨rfl, ka, kb⟩ | ⟨rfl, ka, kb⟩ | ⟨rfl, ka, kb⟩ <;>
    rcases H' with ⟨f12, rfl⟩ | ⟨k', rfl⟩ |
        ⟨s', t', as', at', v', ρ', hs', ht', P', Q', hP', hQ', g1, g2, rfl⟩ |
      ⟨rfl, ma, mb⟩ | ⟨rfl, ma, mb⟩ | ⟨rfl, ma, mb⟩ | ⟨rfl, ma, mb⟩ <;>
    first
      | rfl
      | simp_all
      | skip
  case inl.inr.inl => exact (CellUT.compS_self _ _).symm
  case inl.inr.inr.inl => exact (CellUT.compR_mutMut_of_eq e12).symm
  case inr.inl.inl => exact CellUT.compS_self _ _
  case inr.inl.inr.inr.inl => exact absurd (CellUT.CompatS.kinds k).1 (by rw [g1]; simp)
  case inr.inl.inr.inr.inr.inl => exact absurd (CellUT.CompatS.kinds k).2 (by rw [ma]; simp)
  case inr.inl.inr.inr.inr.inr.inl =>
    exact absurd (CellUT.CompatS.kinds k).1 (by rw [ma]; simp)
  case inr.inr.inl.inl => exact CellUT.compR_mutMut_of_eq f12
  case inr.inr.inl.inr.inl => exact absurd (CellUT.CompatS.kinds k').1 (by simp)
  case inr.inr.inl.inr.inr.inl => exact CellUT.compR_mutMut_det g1 e2.symm
  case inr.inr.inr.inl.inr.inl =>
    exact absurd (CellUT.CompatS.kinds k').2 (by rw [ka]; simp)
  case inr.inr.inr.inr.inl.inr.inl =>
    exact absurd (CellUT.CompatS.kinds k').1 (by rw [ka]; simp)
  case inr.inl.inr.inr.inr.inr.inr.inl =>
    exact absurd (CellUT.CompatS.kinds k).2 (by rw [mb]; simp)
  case inr.inl.inr.inr.inr.inr.inr.inr =>
    exact absurd (CellUT.CompatS.kinds k).1 (by rw [ma]; simp)
  case inr.inr.inr.inr.inr.inl.inr.inl =>
    exact absurd (CellUT.CompatS.kinds k').2 (by rw [kb]; simp)
  case inr.inr.inr.inr.inr.inr.inr.inl =>
    exact absurd (CellUT.CompatS.kinds k').1 (by rw [ka]; simp)

theorem CellUT.compS_comm (ψ₁ ψ₂ : CellUT Loc Val K) (h : ψ₁.CompatS ψ₂) :
    CellUT.compS ψ₁ ψ₂ h = CellUT.compS ψ₂ ψ₁ h.symm :=
  CellUT.CompS.functional (CellUT.compS_spec ψ₁ ψ₂ h) (CellUT.compS_spec ψ₂ ψ₁ h.symm).comm

/-- `○` is commutative on cells: "`ψᵢ` is invariant under changing the order of the cells". -/
theorem CellUT.CompR.comm {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    CellUT.CompR ψ₂ ψ₁ ψ := by
  cases h with
  | same => exact CellUT.CompR.same _
  | strict k => exact (CellUT.compS_comm _ _ k) ▸ CellUT.CompR.strict k.symm
  | mutMut s t v ρ hs ht P Q hP hQ =>
      have := CellUT.CompR.mutMut t s v ρ ht hs Q P hQ hP
      refine (?_ : CellUT.mutOf (K.minS (t ∪ s)) v ρ _ (SPropST.conj Q P) _
        = CellUT.mutOf (K.minS (s ∪ t)) v ρ _ (SPropST.conj P Q) _) ▸ this
      refine CellUT.mutOf_congr (K.minS_union_comm t s) v ρ _ _ _ _ _ _ ?_
      intro r hr hr' w
      exact SPropST.conj_comm Q P r hr hr' w
  | mutOwn s v ρ hs P hP => exact .ownMut s v ρ hs P hP
  | ownMut s v ρ hs P hP => exact .mutOwn s v ρ hs P hP
  | immOwn s v ρ hs => exact .ownImm s v ρ hs
  | ownImm s v ρ hs => exact .immOwn s v ρ hs
  | immMut s v ρ hs b hb P hP => exact .mutImm s v ρ hs b hb P hP
  | mutImm s v ρ hs b hb P hP => exact .immMut s v ρ hs b hb P hP

theorem CellUT.CompatR.symm {ψ₁ ψ₂ : CellUT Loc Val K} (h : ψ₁.CompatR ψ₂) : ψ₂.CompatR ψ₁ :=
  ⟨h.choose, h.choose_spec.comm⟩

theorem CellUT.CompatR.of_compatS {ψ₁ ψ₂ : CellUT Loc Val K} (h : ψ₁.CompatS ψ₂) :
    ψ₁.CompatR ψ₂ := ⟨_, CellUT.CompR.strict h⟩

/-- Every clause of `○` composes cells over a common value. -/
theorem CellUT.CompR.erase {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    ψ₁.erase = ψ₂.erase ∧ ψ.erase = ψ₁.erase := by
  cases h with
  | same χ => exact ⟨rfl, rfl⟩
  | strict k =>
      obtain ⟨e₁, e₂⟩ := CellUT.CompS.erase (CellUT.compS_spec _ _ k)
      exact ⟨e₁.symm.trans e₂, e₁⟩
  | mutMut => exact ⟨rfl, rfl⟩
  | mutOwn => exact ⟨rfl, rfl⟩
  | ownMut => exact ⟨rfl, rfl⟩
  | immOwn => exact ⟨rfl, rfl⟩
  | ownImm => exact ⟨rfl, rfl⟩
  | immMut => exact ⟨rfl, rfl⟩
  | mutImm => exact ⟨rfl, rfl⟩

/-- Every clause of `○` on two non-`own` cells composes them over a common witness. -/
theorem CellUT.CompR.wit {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    (k₁ : ψ₁.kind ≠ Kind.own) (k₂ : ψ₂.kind ≠ Kind.own) : ψ₁.wit = ψ₂.wit := by
  cases h with
  | same χ => rfl
  | strict k =>
      obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := k
      rw [e₁, e₂, CellUT.wit_immOf, CellUT.wit_immOf]
  | mutMut => rw [CellUT.wit_mutOf, CellUT.wit_mutOf]
  | mutOwn => exact absurd rfl k₂
  | ownMut => exact absurd rfl k₁
  | immOwn => exact absurd rfl k₂
  | ownImm => exact absurd rfl k₁
  | immMut => rw [CellUT.wit_immOf, CellUT.wit_mutOf]
  | mutImm => rw [CellUT.wit_mutOf, CellUT.wit_immOf]

/-! ### Associativity of `○` on cells, `[TR]` Lemma 6.3's `○` case -/

/-- Clause (2): two `imm` cells over one `v` and `ρ` compose to the union. -/
theorem CellUT.compR_immImm (s t : TSet) (v : Val) (ρ : ResUT Loc Val K)
    (hs : ρ.InStratum s) (ht : ρ.InStratum t) (hst : ρ.InStratum (s ∪ t)) :
    CellUT.CompR (CellUT.immOf s v ρ hs) (CellUT.immOf t v ρ ht)
      (CellUT.immOf (s ∪ t) v ρ hst) := by
  have k : CellUT.CompatS (CellUT.immOf s v ρ hs) (CellUT.immOf t v ρ ht) :=
    ⟨s, t, v, ρ, hs, ht, rfl, rfl⟩
  exact (CellUT.compS_immOf k hst) ▸ CellUT.CompR.strict k

theorem CellUT.compR_own_left {v : Val} {ψ ω : CellUT Loc Val K}
    (h : CellUT.CompR (CellUT.ownOf v) ψ ω) : ω = ψ := by
  cases h with
  | same => rfl
  | strict k => exact absurd (CellUT.CompatS.kinds k).1 (by simp)
  | ownMut => rfl
  | ownImm => rfl

theorem CellUT.compR_own_right {v : Val} {ψ ω : CellUT Loc Val K}
    (h : CellUT.CompR ψ (CellUT.ownOf v) ω) : ω = ψ := by
  cases h with
  | same => rfl
  | strict k => exact absurd (CellUT.CompatS.kinds k).2 (by simp)
  | mutOwn => rfl
  | immOwn => rfl

theorem CellUT.compR_own_left_of_erase {v : Val} {ψ : CellUT Loc Val K}
    (h : ψ.erase = v) : CellUT.CompR (CellUT.ownOf v) ψ ψ := by
  rcases CellUT.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ρ, hs, rfl⟩ | ⟨b, ab, w, ρ, hb, P, hP, rfl⟩ <;>
    simp only [CellUT.erase_ownOf, CellUT.erase_immOf, CellUT.erase_mutOf] at h <;> subst h
  · exact CellUT.CompR.same _
  · exact CellUT.CompR.ownImm _ _ _ _
  · exact CellUT.CompR.ownMut _ _ _ _ _ _

theorem CellUT.compR_own_right_of_erase {v : Val} {ψ : CellUT Loc Val K}
    (h : ψ.erase = v) : CellUT.CompR ψ (CellUT.ownOf v) ψ := by
  rcases CellUT.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ρ, hs, rfl⟩ | ⟨b, ab, w, ρ, hb, P, hP, rfl⟩ <;>
    simp only [CellUT.erase_ownOf, CellUT.erase_immOf, CellUT.erase_mutOf] at h <;> subst h
  · exact CellUT.CompR.same _
  · exact CellUT.CompR.immOwn _ _ _ _
  · exact CellUT.CompR.mutOwn _ _ _ _ _ _

/-- `[TR]` p. 7, the `○` case at `ψ₁ = own(v)`. -/
theorem CellUT.compR_assoc_own_left {v : Val} {ψ₂ ψ₃ χ ω : CellUT Loc Val K}
    (h₂₃ : CellUT.CompR ψ₂ ψ₃ χ) (h₁χ : CellUT.CompR (CellUT.ownOf v) χ ω) :
    ∃ υ, CellUT.CompR (CellUT.ownOf v) ψ₂ υ ∧ CellUT.CompR υ ψ₃ ω := by
  have hω : ω = χ := CellUT.compR_own_left h₁χ
  subst hω
  refine ⟨ψ₂, CellUT.compR_own_left_of_erase ?_, h₂₃⟩
  have e₁ := (CellUT.CompR.erase h₁χ).1
  have e₂ := (CellUT.CompR.erase h₂₃).2
  simp only [CellUT.erase_ownOf] at e₁
  exact (e₂.symm.trans e₁.symm)

/-- `[TR]` p. 7, the `○` case at `ψ₂ = own(v)`. -/
theorem CellUT.compR_assoc_own_mid {v : Val} {ψ₁ ψ₃ χ ω : CellUT Loc Val K}
    (h₂₃ : CellUT.CompR (CellUT.ownOf v) ψ₃ χ) (h₁χ : CellUT.CompR ψ₁ χ ω) :
    ∃ υ, CellUT.CompR ψ₁ (CellUT.ownOf v) υ ∧ CellUT.CompR υ ψ₃ ω := by
  have hχ : χ = ψ₃ := CellUT.compR_own_left h₂₃
  subst hχ
  refine ⟨ψ₁, CellUT.compR_own_right_of_erase ?_, h₁χ⟩
  have e₁ := (CellUT.CompR.erase h₁χ).1
  have e₂ := (CellUT.CompR.erase h₂₃).1
  simp only [CellUT.erase_ownOf] at e₂
  exact e₁.trans e₂.symm

/-- `[TR]` p. 7, the `○` case at `ψ₃ = own(v)`. -/
theorem CellUT.compR_assoc_own_right {v : Val} {ψ₁ ψ₂ χ ω : CellUT Loc Val K}
    (h₂₃ : CellUT.CompR ψ₂ (CellUT.ownOf v) χ) (h₁χ : CellUT.CompR ψ₁ χ ω) :
    ∃ υ, CellUT.CompR ψ₁ ψ₂ υ ∧ CellUT.CompR υ (CellUT.ownOf v) ω := by
  have hχ : χ = ψ₂ := CellUT.compR_own_right h₂₃
  subst hχ
  refine ⟨ω, h₁χ, CellUT.compR_own_right_of_erase ?_⟩
  have e₁ := (CellUT.CompR.erase h₁χ).2
  have e₂ := (CellUT.CompR.erase h₁χ).1
  have e₃ := (CellUT.CompR.erase h₂₃).1
  simp only [CellUT.erase_ownOf] at e₃
  exact e₁.trans (e₂.trans e₃)

theorem CellUT.kind_immOf_ne_own {s : TSet} {v : Val} {ρ : ResUT Loc Val K}
    {h : ρ.InStratum s} : (CellUT.immOf s v ρ h).kind ≠ Kind.own :=
  fun hk => Kind.noConfusion hk

theorem CellUT.kind_mutOf_ne_own {s : TSet} [Fact (K.Anti s)] {v : Val} {ρ : ResUT Loc Val K}
    {h : ρ.InStratum s} {P : Val → SPropST Loc Val K s} {hw : P v ⟨ρ, h⟩} :
    (CellUT.mutOf s v ρ h P hw).kind ≠ Kind.own :=
  fun hk => Kind.noConfusion hk

/-- The `○` case of `[TR]` Lemma 6.3 (pp. 6–7) at the cell level, left to right, by the
printed case split on `ψ₁`, `ψ₂`, `ψ₃`. -/
theorem CellUT.compR_assoc_forward {ψ₁ ψ₂ ψ₃ χ ω : CellUT Loc Val K}
    (h₂₃ : CellUT.CompR ψ₂ ψ₃ χ) (h₁χ : CellUT.CompR ψ₁ χ ω) :
    ∃ υ, CellUT.CompR ψ₁ ψ₂ υ ∧ CellUT.CompR υ ψ₃ ω := by
  rcases CellUT.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s, v₁, σ, ks, rfl⟩ | ⟨a, aa, v₁, σ, ka, P, hP, rfl⟩
  · exact CellUT.compR_assoc_own_left h₂₃ h₁χ
  · rcases CellUT.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨t, v₂, ρ, kt, rfl⟩ | ⟨b, ab, v₂, ρ, kb, Q, hQ, rfl⟩
    · exact CellUT.compR_assoc_own_mid h₂₃ h₁χ
    · rcases CellUT.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ |
          ⟨c, ac, v₃, τ, kc, T, hT, rfl⟩
      · exact CellUT.compR_assoc_own_right h₂₃ h₁χ
      · -- `imm ○ (imm ○ imm)`: three unions, reassociated.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_immOf_ne_own CellUT.kind_immOf_ne_own
        simp only [CellUT.erase_immOf] at ev
        simp only [CellUT.wit_immOf] at ew
        subst ev; subst ew
        have ktu : ρ.InStratum (t ∪ u) := ResUT.inStratum_union_iff.mpr ⟨kt, ku⟩
        have hχ : χ = CellUT.immOf (t ∪ u) v₂ ρ ktu :=
          CellUT.CompR.functional h₂₃ (CellUT.compR_immImm t u v₂ ρ kt ku ktu)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_immOf_ne_own CellUT.kind_immOf_ne_own).symm
        simp only [CellUT.erase_immOf] at ev'
        simp only [CellUT.wit_immOf] at ew'
        subst ev'; subst ew'
        have kstu : ρ.InStratum (s ∪ (t ∪ u)) := ResUT.inStratum_union_iff.mpr ⟨ks, ktu⟩
        have hω : ω = CellUT.immOf (s ∪ (t ∪ u)) v₂ ρ kstu :=
          CellUT.CompR.functional h₁χ (CellUT.compR_immImm s (t ∪ u) v₂ ρ ks ktu kstu)
        subst hω
        have kst : ρ.InStratum (s ∪ t) := ResUT.inStratum_union_iff.mpr ⟨ks, kt⟩
        refine ⟨CellUT.immOf (s ∪ t) v₂ ρ kst, CellUT.compR_immImm s t v₂ ρ ks kt kst, ?_⟩
        have kstu' : ρ.InStratum ((s ∪ t) ∪ u) := ResUT.inStratum_union_iff.mpr ⟨kst, ku⟩
        have h := CellUT.compR_immImm (s ∪ t) u v₂ ρ kst ku kstu'
        rwa [CellUT.immOf_congr (TSet.union_assoc s t u) rfl rfl kstu' kstu] at h
      · -- `imm ○ (imm ○ mut)`: the `mut` is absorbed on both sides.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_immOf_ne_own CellUT.kind_mutOf_ne_own
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellUT.immOf t v₂ ρ kt :=
          CellUT.CompR.functional h₂₃ (CellUT.CompR.immMut t v₂ ρ kt c kc T hT)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_immOf_ne_own CellUT.kind_immOf_ne_own).symm
        simp only [CellUT.erase_immOf] at ev'
        simp only [CellUT.wit_immOf] at ew'
        subst ev'; subst ew'
        have kst : ρ.InStratum (s ∪ t) := ResUT.inStratum_union_iff.mpr ⟨ks, kt⟩
        have hω : ω = CellUT.immOf (s ∪ t) v₂ ρ kst :=
          CellUT.CompR.functional h₁χ (CellUT.compR_immImm s t v₂ ρ ks kt kst)
        subst hω
        exact ⟨CellUT.immOf (s ∪ t) v₂ ρ kst, CellUT.compR_immImm s t v₂ ρ ks kt kst,
          CellUT.CompR.immMut (s ∪ t) v₂ ρ kst c kc T hT⟩
    · rcases CellUT.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ |
          ⟨c, ac, v₃, τ, kc, T, hT, rfl⟩
      · exact CellUT.compR_assoc_own_right h₂₃ h₁χ
      · -- `imm ○ (mut ○ imm)`: the `mut` is absorbed on both sides.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_mutOf_ne_own CellUT.kind_immOf_ne_own
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellUT.immOf u v₂ ρ ku :=
          CellUT.CompR.functional h₂₃ (CellUT.CompR.mutImm u v₂ ρ ku b kb Q hQ)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_immOf_ne_own CellUT.kind_immOf_ne_own).symm
        simp only [CellUT.erase_immOf] at ev'
        simp only [CellUT.wit_immOf] at ew'
        subst ev'; subst ew'
        have ksu : ρ.InStratum (s ∪ u) := ResUT.inStratum_union_iff.mpr ⟨ks, ku⟩
        have hω : ω = CellUT.immOf (s ∪ u) v₂ ρ ksu :=
          CellUT.CompR.functional h₁χ (CellUT.compR_immImm s u v₂ ρ ks ku ksu)
        subst hω
        exact ⟨CellUT.immOf s v₂ ρ ks, CellUT.CompR.immMut s v₂ ρ ks b kb Q hQ,
          CellUT.compR_immImm s u v₂ ρ ks ku ksu⟩
      · -- `imm ○ (mut ○ mut)`: the `imm` is the result either way.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_mutOf_ne_own CellUT.kind_mutOf_ne_own
        simp only [CellUT.erase_mutOf] at ev
        simp only [CellUT.wit_mutOf] at ew
        subst ev; subst ew
        have kbc : ρ.InStratum (K.minS (b ∪ c)) := kb.minUnion kc
        have hQT : SPropST.conj Q T v₂ ⟨ρ, kbc⟩ := SPropST.conj_holds kb kc hQ hT
        have hχ : χ = CellUT.mutOf (K.minS (b ∪ c)) v₂ ρ kbc
            (SPropST.conj Q T) hQT :=
          CellUT.CompR.functional h₂₃ (CellUT.CompR.mutMut b c v₂ ρ kb kc Q T hQ hT)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_immOf_ne_own CellUT.kind_mutOf_ne_own).symm
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev'
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellUT.immOf s v₂ ρ ks :=
          CellUT.CompR.functional h₁χ
            (CellUT.CompR.immMut s v₂ ρ ks _ kbc (SPropST.conj Q T) hQT)
        subst hω
        exact ⟨CellUT.immOf s v₂ ρ ks, CellUT.CompR.immMut s v₂ ρ ks b kb Q hQ,
          CellUT.CompR.immMut s v₂ ρ ks c kc T hT⟩
  · rcases CellUT.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨t, v₂, ρ, kt, rfl⟩ | ⟨b, ab, v₂, ρ, kb, Q, hQ, rfl⟩
    · exact CellUT.compR_assoc_own_mid h₂₃ h₁χ
    · rcases CellUT.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ |
          ⟨c, ac, v₃, τ, kc, T, hT, rfl⟩
      · exact CellUT.compR_assoc_own_right h₂₃ h₁χ
      · -- `mut ○ (imm ○ imm)`: the `mut` is absorbed on both sides.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_immOf_ne_own CellUT.kind_immOf_ne_own
        simp only [CellUT.erase_immOf] at ev
        simp only [CellUT.wit_immOf] at ew
        subst ev; subst ew
        have ktu : ρ.InStratum (t ∪ u) := ResUT.inStratum_union_iff.mpr ⟨kt, ku⟩
        have hχ : χ = CellUT.immOf (t ∪ u) v₂ ρ ktu :=
          CellUT.CompR.functional h₂₃ (CellUT.compR_immImm t u v₂ ρ kt ku ktu)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_mutOf_ne_own CellUT.kind_immOf_ne_own).symm
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev'
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellUT.immOf (t ∪ u) v₂ ρ ktu :=
          CellUT.CompR.functional h₁χ (CellUT.CompR.mutImm (t ∪ u) v₂ ρ ktu a ka P hP)
        subst hω
        exact ⟨CellUT.immOf t v₂ ρ kt, CellUT.CompR.mutImm t v₂ ρ kt a ka P hP,
          CellUT.compR_immImm t u v₂ ρ kt ku ktu⟩
      · -- `mut ○ (imm ○ mut)`: the `imm` is the result either way.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_immOf_ne_own CellUT.kind_mutOf_ne_own
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellUT.immOf t v₂ ρ kt :=
          CellUT.CompR.functional h₂₃ (CellUT.CompR.immMut t v₂ ρ kt c kc T hT)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_mutOf_ne_own CellUT.kind_immOf_ne_own).symm
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev'
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellUT.immOf t v₂ ρ kt :=
          CellUT.CompR.functional h₁χ (CellUT.CompR.mutImm t v₂ ρ kt a ka P hP)
        subst hω
        exact ⟨CellUT.immOf t v₂ ρ kt, CellUT.CompR.mutImm t v₂ ρ kt a ka P hP,
          CellUT.CompR.immMut t v₂ ρ kt c kc T hT⟩
    · rcases CellUT.rep ψ₃ with ⟨v₃, rfl⟩ | ⟨u, v₃, τ, ku, rfl⟩ |
          ⟨c, ac, v₃, τ, kc, T, hT, rfl⟩
      · exact CellUT.compR_assoc_own_right h₂₃ h₁χ
      · -- `mut ○ (mut ○ imm)`: the `imm` is the result either way.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_mutOf_ne_own CellUT.kind_immOf_ne_own
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew
        subst ev; subst ew
        have hχ : χ = CellUT.immOf u v₂ ρ ku :=
          CellUT.CompR.functional h₂₃ (CellUT.CompR.mutImm u v₂ ρ ku b kb Q hQ)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_mutOf_ne_own CellUT.kind_immOf_ne_own).symm
        simp only [CellUT.erase_immOf, CellUT.erase_mutOf] at ev'
        simp only [CellUT.wit_immOf, CellUT.wit_mutOf] at ew'
        subst ev'; subst ew'
        have hω : ω = CellUT.immOf u v₂ ρ ku :=
          CellUT.CompR.functional h₁χ (CellUT.CompR.mutImm u v₂ ρ ku a ka P hP)
        subst hω
        exact ⟨CellUT.mutOf (K.minS (a ∪ b)) v₂ ρ (ka.minUnion kb)
            (SPropST.conj P Q) (SPropST.conj_holds ka kb hP hQ),
          CellUT.CompR.mutMut a b v₂ ρ ka kb P Q hP hQ,
          CellUT.CompR.mutImm u v₂ ρ ku _ (ka.minUnion kb) (SPropST.conj P Q)
            (SPropST.conj_holds ka kb hP hQ)⟩
      · -- `mut ○ (mut ○ mut)`: associativity of `min ∘ ∪` (the printed `⊓`) and of `∧`.
        have ev := (CellUT.CompR.erase h₂₃).1
        have ew := CellUT.CompR.wit h₂₃ CellUT.kind_mutOf_ne_own CellUT.kind_mutOf_ne_own
        simp only [CellUT.erase_mutOf] at ev
        simp only [CellUT.wit_mutOf] at ew
        subst ev; subst ew
        have kbc : ρ.InStratum (K.minS (b ∪ c)) := kb.minUnion kc
        have hQT : SPropST.conj Q T v₂ ⟨ρ, kbc⟩ := SPropST.conj_holds kb kc hQ hT
        have hχ : χ = CellUT.mutOf (K.minS (b ∪ c)) v₂ ρ kbc
            (SPropST.conj Q T) hQT :=
          CellUT.CompR.functional h₂₃ (CellUT.CompR.mutMut b c v₂ ρ kb kc Q T hQ hT)
        subst hχ
        have ev' := ((CellUT.CompR.erase h₁χ).1).symm
        have ew' :=
          (CellUT.CompR.wit h₁χ CellUT.kind_mutOf_ne_own CellUT.kind_mutOf_ne_own).symm
        simp only [CellUT.erase_mutOf] at ev'
        simp only [CellUT.wit_mutOf] at ew'
        subst ev'; subst ew'
        have kabc : ρ.InStratum (K.minS (a ∪ K.minS (b ∪ c))) := ka.minUnion kbc
        have hPQT : SPropST.conj P (SPropST.conj Q T) v₂ ⟨ρ, kabc⟩ :=
          SPropST.conj_holds ka kbc hP hQT
        have hω : ω = CellUT.mutOf (K.minS (a ∪ K.minS (b ∪ c))) v₂ ρ kabc
            (SPropST.conj P (SPropST.conj Q T)) hPQT :=
          CellUT.CompR.functional h₁χ
            (CellUT.CompR.mutMut a _ v₂ ρ ka kbc P (SPropST.conj Q T) hP hQT)
        subst hω
        have kab : ρ.InStratum (K.minS (a ∪ b)) := ka.minUnion kb
        have hPQ : SPropST.conj P Q v₂ ⟨ρ, kab⟩ := SPropST.conj_holds ka kb hP hQ
        refine ⟨CellUT.mutOf (K.minS (a ∪ b)) v₂ ρ kab (SPropST.conj P Q) hPQ,
          CellUT.CompR.mutMut a b v₂ ρ ka kb P Q hP hQ, ?_⟩
        have kabc' : ρ.InStratum (K.minS (K.minS (a ∪ b) ∪ c)) := kab.minUnion kc
        have hPQT' : SPropST.conj (SPropST.conj P Q) T v₂ ⟨ρ, kabc'⟩ :=
          SPropST.conj_holds kab kc hPQ hT
        have h := CellUT.CompR.mutMut _ c v₂ ρ kab kc (SPropST.conj P Q) T
          hPQ hT
        rwa [CellUT.mutOf_congr (K.minS_assoc a b c) v₂ ρ kabc' kabc
          (SPropST.conj (SPropST.conj P Q) T) (SPropST.conj P (SPropST.conj Q T)) hPQT' hPQT
          (fun r hr hr' w => SPropST.conj_assoc P Q T r hr hr' w)] at h

/-- `○` is associative on cells, as a Kleene equality. -/
theorem CellUT.compR_assoc (ψ₁ ψ₂ ψ₃ ω : CellUT Loc Val K) :
    (∃ χ, CellUT.CompR ψ₂ ψ₃ χ ∧ CellUT.CompR ψ₁ χ ω) ↔
    (∃ υ, CellUT.CompR ψ₁ ψ₂ υ ∧ CellUT.CompR υ ψ₃ ω) := by
  constructor
  · rintro ⟨χ, h₂₃, h₁χ⟩
    exact CellUT.compR_assoc_forward h₂₃ h₁χ
  · rintro ⟨υ, h₁₂, hυ₃⟩
    obtain ⟨χ, hχ, hω⟩ := CellUT.compR_assoc_forward h₁₂.comm hυ₃.comm
    exact ⟨χ, hχ.comm, hω.comm⟩

end BoCa.Fig16.Tree

end
