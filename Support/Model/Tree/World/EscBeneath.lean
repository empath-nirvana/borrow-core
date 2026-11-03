import Support.Model.Tree.World.FdEscBranch

/-!
# `EscBeneathT`

`EscBeneathT` (`TreeWp/FdEscBranch.lean`) is the case of the escrow's frame condition that
`fd_esc_of_branch` does not derive: a non-`imm` cell of the aliasable walk of the other branches
`ρ_rest` at a location where a lineage member `d` of the record proper `p` holds a non-`imm` cell.
It is derived here (`escBeneathT`), from three facts:

* **One owner for every exclusive cell of an escrow** (`TWNT.exclUnique`): two records whose
  escrows hold a non-`imm` cell at one location are one record. This is `ChainInv`'s
  own-uniqueness clause at every non-`imm` kind. Records' escrows are fixed data, so only
  `immFrame` adds to it: the new lineage's exclusive cells are in `ex(R)` (as in `ti_frame`'s
  `newEx`, `newUnique`), the old records' in `ag(W)` (`ExIn`), and `ex(W)_●` misses `ag(W)`.
* **One parent per lineage record** (`ExclUniqueT.parent`), so two ancestors of one record are
  comparable (`desc_comparable`).
* **The innermost view above a cell lies in the record's lineage.** The cell of `ag(ρ_rest)` sits
  beneath a borrow of `ρ_rest` (`agW_nonimm_beneath`). Above it either only `mut` cells lead to the
  top, and then it is in `ex(W)_●` (`xpath_ex`), which misses `ag(W)`'s view of the lineage
  (`le_view_cellAt`); or there is an innermost `imm` cell `V`, with only `mut` cells below it
  (`cellAt_split`). `V` is in `ag(W)` (`cellAt_imm_icp`), so `Coverage` classifies it: a record's
  cell over its escrow, or a chain view, whose witness is a part of the record's escrow
  (`chain_view_le`, by `DeepInv` along the chain). The `mut` path below `V` is a lineage path of
  that record (`xpath_linPath`), ending at the record owning the cell, which is `d`. So `V`'s
  record is comparable with `p`; `p` is no sub-record (`NoMut`), so `V`'s location is `p`'s or a
  lineage location of `p`, where `FrameLifeT` puts its lifetimes inside the frame `α`, while the
  strata put them on the branch `n` (`cellAt_onBranch`), not inside `α`.

The hypothesis `ζ.kind = own → χ.kind = own` of `EscBeneathT` is not read.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-! ### One owner for every exclusive cell of an escrow -/

/-- The non-`imm` cells of the records' escrows are each one record's. -/
def ExclUniqueT (rs : List (FrameRecT K)) : Prop :=
  ∀ r₁ ∈ rs, ∀ r₂ ∈ rs, ∀ x (ζ₁ ζ₂ : TCell K), r₁.R.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm →
    r₂.R.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm → r₁ = r₂

/-- **`ExclUniqueT` is an invariant of `TWNT`.** -/
theorem TWNT.exclUnique {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (h : TWNT K Θ tc W ps rs) : ExclUniqueT rs := by
  induction h with
  | empty => intro r₁ h₁; simp at h₁
  | alloc _ _ _ _ _ ih => exact ih
  | @immFrame K Θ tc W X Z R W' ps rs ds l v α T hα hW₀ hX hW hden hW' hv hds ih =>
      have hTI := hW₀.inv
      have hvW := hW₀.valid
      obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW
      obtain ⟨eR, heR, hRW, -⟩ := frame_ex hX hW heW
      have newEx : ∀ d, DescRT ⟨l, v, R, T⟩ d → ∀ x (ζ : TCell K), d.R.get x = some ζ →
          ζ.kind ≠ Kind.imm → eR.get x = some ζ := by
        rintro d ⟨p, hp⟩ x ζ e k
        exact xpath_ex heR hp.xpath e k
      have mem' : ∀ x, x ∈ (⟨l, v, R, T⟩ :: (ds ++ rs) : List (FrameRecT K)) →
          DescRT ⟨l, v, R, T⟩ x ∨ x ∈ rs := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl (DescRT.refl _)
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨p, -, hp⟩ := (hds x).mp hx; exact Or.inl ⟨p, hp⟩
          · exact Or.inr hx
      intro r₁ h₁ r₂ h₂ x ζ₁ ζ₂ e₁ k₁ e₂ k₂
      have oldAg : ∀ r ∈ rs, ∀ ζ : TCell K, r.R.get x = some ζ → ζ.kind ≠ Kind.imm →
          ∃ ξ, aW.get x = some ξ :=
        fun r hr ζ e k => exIn_support (TI.exIn hTI hr) e k aW haW
      have newNone : ∀ d, DescRT ⟨l, v, R, T⟩ d → ∀ ζ : TCell K, d.R.get x = some ζ →
          ζ.kind ≠ Kind.imm → ∀ ξ, aW.get x = some ξ → False :=
        fun d hd ζ e k ξ ea => ex_ag_disjoint hvW heW haW (hRW x ζ (newEx d hd x ζ e k) k) ea
      rcases mem' r₁ h₁ with hd₁ | hr₁ <;> rcases mem' r₂ h₂ with hd₂ | hr₂
      · obtain ⟨p₁, hp₁⟩ := hd₁
        obtain ⟨p₂, hp₂⟩ := hd₂
        have hpp := xpath_unique heR hp₁.xpath hp₂.xpath e₁ k₁ e₂ k₂
        subst hpp
        exact hp₁.functional hden hp₂
      · obtain ⟨ξ, eξ⟩ := oldAg r₂ hr₂ ζ₂ e₂ k₂
        exact (newNone r₁ hd₁ ζ₁ e₁ k₁ ξ eξ).elim
      · obtain ⟨ξ, eξ⟩ := oldAg r₁ hr₁ ζ₁ e₁ k₁
        exact (newNone r₂ hd₂ ζ₂ e₂ k₂ ξ eξ).elim
      · exact ih r₁ hr₁ r₂ hr₂ x ζ₁ ζ₂ e₁ k₁ e₂ k₂
  | reb _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih
  | mutFold _ _ _ _ _ ih => exact ih
  | mutUnfold _ _ _ _ _ ih => exact ih
  | free _ _ _ ih => exact ih
  | store _ _ _ _ ih => exact ih
  | immEnd r hW₀ hr hc hX' hW' hv hps hrs ih =>
      have sub : ∀ d, d ∈ _ → d ∈ _ := fun d hd => by
        obtain ⟨p, hp, hpd⟩ := (hrs d).mp hd
        exact (hW₀.inv.2.2.2.2.2.2.1 d).mpr ⟨p, ((hps p).mp hp).1, hpd⟩
      intro r₁ h₁ r₂ h₂ x ζ₁ ζ₂ e₁ k₁ e₂ k₂
      exact ih r₁ (sub r₁ h₁) r₂ (sub r₂ h₂) x ζ₁ ζ₂ e₁ k₁ e₂ k₂
  | rebEnd _ _ _ _ _ _ _ ih => exact ih
  | rebEndDeep _ _ _ _ _ _ _ _ ih => exact ih
  | reread _ _ _ _ _ hrs _ ih =>
      intro r₁' h₁ r₂' h₂ x ζ₁' ζ₂' e₁ k₁ e₂ k₂
      obtain ⟨r₁, hr₁, rr₁⟩ := forall₂_mem_right hrs h₁
      obtain ⟨r₂, hr₂, rr₂⟩ := forall₂_mem_right hrs h₂
      obtain ⟨ζ₁, f₁, c₁⟩ := rr₁.2.2.2.get_some' e₁
      obtain ⟨ζ₂, f₂, c₂⟩ := rr₂.2.2.2.get_some' e₂
      obtain rfl := ih r₁ hr₁ r₂ hr₂ x ζ₁ ζ₂ f₁ (by rw [← c₁.kind]; exact k₁) f₂
        (by rw [← c₂.kind]; exact k₂)
      exact RecRR.func rr₁ rr₂

/-- **One parent per lineage record.** -/
theorem ExclUniqueT.parent {rs : List (FrameRecT K)} (hU : ExclUniqueT rs) {r₁ r₂ e : FrameRecT K}
    (h₁ : r₁ ∈ rs) (h₂ : r₂ ∈ rs) (s₁ : SubRecT r₁ e) (s₂ : SubRecT r₂ e) : r₁ = r₂ := by
  obtain ⟨-, ζ₁, e₁, k₁, -⟩ := s₁
  obtain ⟨-, ζ₂, e₂, k₂, -⟩ := s₂
  exact hU r₁ h₁ r₂ h₂ e.le ζ₁ ζ₂ e₁ (by rw [k₁]; simp) e₂ (by rw [k₂]; simp)

/-! ### Lineages -/

theorem LinPathT.append {a b c : FrameRecT K} {q₁ q₂ : List BoCa.Loc} (h₁ : LinPathT a q₁ b)
    (h₂ : LinPathT b q₂ c) : LinPathT a (q₁ ++ q₂) c := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact .cons hs (ih h₂)

/-- The last step of a nonempty lineage path, with the path before it. -/
theorem LinPathT.unsnoc {r d : FrameRecT K} {q : List BoCa.Loc} (h : LinPathT r q d)
    (hq : q ≠ []) : ∃ q' d', q'.length + 1 = q.length ∧ LinPathT r q' d' ∧ SubRecT d' d := by
  induction h with
  | nil r => exact absurd rfl hq
  | @cons r d₁ e q hs t ih =>
      cases t with
      | nil => exact ⟨[], r, rfl, .nil r, hs⟩
      | cons hs' t' =>
          obtain ⟨q', d', hl, hp, hsd⟩ := ih (by simp)
          exact ⟨d₁.le :: q', d', by simp [hl], .cons hs hp, hsd⟩

/-- **Two ancestors of one record are comparable**, when every record has one parent. -/
theorem desc_comparable {rs : List (FrameRecT K)} (hU : ExclUniqueT rs)
    (hcl : ∀ r ∈ rs, ∀ d, DescRT r d → d ∈ rs) :
    ∀ n (r p d : FrameRecT K) (q₁ q₂ : List BoCa.Loc), q₁.length + q₂.length ≤ n → r ∈ rs →
      p ∈ rs → LinPathT r q₁ d → LinPathT p q₂ d → DescRT p r ∨ DescRT r p := by
  intro n
  induction n with
  | zero =>
      intro r p d q₁ q₂ hn hr hp h₁ h₂
      have : q₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      obtain rfl := h₁.inv_nil
      exact Or.inl ⟨q₂, h₂⟩
  | succ n ih =>
      intro r p d q₁ q₂ hn hr hp h₁ h₂
      by_cases e₁ : q₁ = []
      · subst e₁; obtain rfl := h₁.inv_nil; exact Or.inl ⟨q₂, h₂⟩
      by_cases e₂ : q₂ = []
      · subst e₂; obtain rfl := h₂.inv_nil; exact Or.inr ⟨q₁, h₁⟩
      obtain ⟨q₁', d₁, l₁, t₁, s₁⟩ := h₁.unsnoc e₁
      obtain ⟨q₂', d₂, l₂, t₂, s₂⟩ := h₂.unsnoc e₂
      obtain rfl := hU.parent (hcl r hr d₁ ⟨q₁', t₁⟩) (hcl p hp d₂ ⟨q₂', t₂⟩) s₁ s₂
      exact ih r p d₁ q₁' q₂' (by omega) hr hp t₁ t₂

/-- The records of a `TIT` world are closed under lineage. -/
theorem TIT.desc_closed {Θ : CodeTy} {W : TRes K} {ps rs : List (FrameRecT K)}
    (h : TIT K Θ W ps rs) : ∀ r ∈ rs, ∀ d, DescRT r d → d ∈ rs := by
  rintro r hr d ⟨q, hq⟩
  obtain ⟨p, hp, q', hq'⟩ := (h.2.2.2.2.2.2.1 r).mp hr
  exact (h.2.2.2.2.2.2.1 d).mpr ⟨p, hp, _, hq'.append hq⟩

/-- **A `mut` path from a typed record's escrow is a lineage path.** -/
theorem xpath_linPath (Θ : CodeTy) :
    ∀ (path : List BoCa.Loc) {r : FrameRecT K} {σ : TRes K}, (r.T.interp Θ).P K r.v r.R →
      XPath r.R path σ → ∃ e, LinPathT r path e ∧ e.R = σ := by
  intro path
  induction path with
  | nil =>
      intro r σ _ hx
      cases hx
      exact ⟨r, .nil r, rfl⟩
  | cons m q ih =>
      intro r σ hR hx
      cases hx with
      | @cons _ _ _ ψ _ e km t =>
          obtain ⟨S, hg, -⟩ := mut_gposT Θ r.T hR e km
          have hs : SubRecT r ⟨m, ψ.erase, ψ.wit, S⟩ := ⟨hg, ψ, e, km, rfl, rfl⟩
          obtain ⟨e', he', rfl⟩ := ih (r := ⟨m, ψ.erase, ψ.wit, S⟩) (hs.typed hR) t
          exact ⟨e', .cons hs he', rfl⟩

/-! ### Paths of `mut` cells -/

theorem xpath_le {q R : TRes K} (hle : ResUT.Le q R) {path : List BoCa.Loc} {σ : TRes K}
    (hp : XPath q path σ) {x : BoCa.Loc} {ζ : TCell K} (e : σ.get x = some ζ)
    (k : ζ.kind ≠ Kind.imm) : ∃ σ', XPath R path σ' ∧ σ'.get x = some ζ := by
  obtain ⟨τ, hτ⟩ := hle
  cases hp with
  | nil => exact ⟨R, .nil R, (ResUT.CompS.get_left_of_ne_imm hτ e k).2⟩
  | cons em km t =>
      exact ⟨σ, .cons (ResUT.CompS.get_left_of_ne_imm hτ em (by rw [km]; simp)).2 km t, e⟩

theorem xpath_del {q : TRes K} {l : BoCa.Loc} {path : List BoCa.Loc} {σ : TRes K}
    (hp : XPath (q.del l) path σ) {x : BoCa.Loc} {ζ : TCell K} (e : σ.get x = some ζ) :
    ∃ σ', XPath q path σ' ∧ σ'.get x = some ζ := by
  cases hp with
  | nil =>
      refine ⟨q, .nil q, ?_⟩
      by_cases hx : x = l
      · subst hx; simp at e
      · rwa [ResUT.del_get_ne _ hx] at e
  | @cons _ _ m ψ _ em km t =>
      by_cases hm : m = l
      · subst hm; simp at em
      · rw [ResUT.del_get_ne _ hm] at em
        exact ⟨σ, .cons em km t, e⟩

theorem CellAt.not_own_wit {χ : TCell K} (hk : χ.kind = Kind.own) {y : BoCa.Loc} {ψ : TCell K}
    (h : CellAt χ.wit y ψ) : False := by
  cases χ with
  | own => exact CellAt.not_empty h
  | imm => cases hk
  | «mut» => cases hk

/-- **The innermost view above a cell**: a cell at depth is reached from the top by `mut` cells
only, or lies beneath an innermost `imm` cell by `mut` cells only. -/
theorem cellAt_split {ρ : TRes K} {x : BoCa.Loc} {ψ : TCell K} (h : CellAt ρ x ψ) :
    (∃ q σ, XPath ρ q σ ∧ σ.get x = some ψ) ∨
    (∃ (m : BoCa.Loc) (V : TCell K), CellAt ρ m V ∧ V.kind = Kind.imm ∧
      ∃ q σ, XPath V.wit q σ ∧ σ.get x = some ψ) := by
  induction h with
  | top e => exact Or.inl ⟨[], _, .nil _, e⟩
  | @nest ρ m y χ ψ e hc ih =>
      rcases ih with ⟨q, σ, hq, eσ⟩ | ⟨m₁, V, hV, kV, q, σ, hq, eσ⟩
      · cases hk : χ.kind with
        | «mut» => exact Or.inl ⟨m :: q, σ, .cons e hk hq, eσ⟩
        | imm => exact Or.inr ⟨m, χ, .top e, hk, q, σ, hq, eσ⟩
        | own => exact (CellAt.not_own_wit hk hc).elim
      · exact Or.inr ⟨m₁, V, .nest e hV, kV, q, σ, hq, eσ⟩

/-- **A view at depth shows in the aliasable walk**, over its value and witness, with its
lifetimes. -/
theorem cellAt_imm_icp {W : TRes K} {m : BoCa.Loc} {V : TCell K} (h : CellAt W m V) :
    ∀ {aW : TRes K}, AgWT W aW → ICp aW m V := by
  induction h with
  | top e => intro aW haW; exact icpAt_agW haW _ _ e
  | @nest ρ m₀ y χ ψ e hc ih =>
      intro aW haW
      cases hk : χ.kind with
      | own => exact (CellAt.not_own_wit hk hc).elim
      | imm =>
          obtain ⟨ev, av, p, z, -, hav, hp, hz⟩ := AgWT.imm_wit_le haW e hk
          exact icp_trans (ih hav) (icpAt_trans (icpAt_right hp _) (icpAt_left hz _))
      | «mut» =>
          obtain ⟨av, z, hav, hz⟩ := AgWT.mut_wit_le haW e hk
          exact icp_trans (ih hav) (icpAt_left hz _)

/-- The strata put every cell at depth of a resource on its top cells' branch. -/
theorem cellAt_onBranch {n : Life} {ρ : TRes K} (h : OnBranchResT K n ρ) {x : BoCa.Loc}
    {ψ : TCell K} (hc : CellAt ρ x ψ) : CellAboveT K n ψ := by
  induction hc with
  | top e => exact h _ _ e
  | nest e _ ih => exact ih (h _ _ e).wit

/-! ### Chain views -/

/-- `ChainT` with its number of steps. -/
inductive ChainD (R : TRes K) : KTy → BoCa.Val → Option BoCa.Loc → BoCa.Loc → KTy → BoCa.Val →
    Nat → Prop
  | one {T : KTy} {v : BoCa.Val} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val} :
      RefPosT T v l S → R.get l = some (CellUT.ownOf u) → ChainD R T v none l S u 0
  | step {T : KTy} {v : BoCa.Val} {l₁ : BoCa.Loc} {S₁ : KTy} {u₁ : BoCa.Val}
      {p : Option BoCa.Loc} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val} {n : Nat} :
      RefPosT T v l₁ S₁ → R.get l₁ = some (CellUT.ownOf u₁) → ChainD R S₁ u₁ p l S u n →
      ChainD R T v (some (p.getD l₁)) l S u (n + 1)

theorem ChainT.depth {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc} {l : BoCa.Loc}
    {S : KTy} {u : BoCa.Val} (h : ChainT R T v p l S u) : ∃ n, ChainD R T v p l S u n := by
  induction h with
  | one hp e => exact ⟨0, .one hp e⟩
  | step hp e _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .step hp e hn⟩

theorem ChainD.chain {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc} {l : BoCa.Loc}
    {S : KTy} {u : BoCa.Val} {n : Nat} (h : ChainD R T v p l S u n) : ChainT R T v p l S u := by
  induction h with
  | one hp e => exact .one hp e
  | step hp e _ ih => exact .step hp e ih

/-- `chain_lastT` with the number of steps: the parent's chain is one step shorter. -/
theorem ChainD.last {R : TRes K} {T : KTy} {v : BoCa.Val} {p : Option BoCa.Loc} {l : BoCa.Loc}
    {S : KTy} {u : BoCa.Val} {n : Nat} (h : ChainD R T v p l S u n) :
    ∀ l₀, p = some l₀ → ∃ m p₀ S₀ u₀, n = m + 1 ∧ ChainD R T v p₀ l₀ S₀ u₀ m := by
  induction h with
  | one _ _ => intro l₀ e; cases e
  | @step T v l₁ S₁ u₁ p l S u n hp e₁ t ih =>
      intro l₀ e
      cases p with
      | none =>
          simp only [Option.getD_none, Option.some.injEq] at e
          subst e
          cases t with
          | one _ _ => exact ⟨0, none, S₁, u₁, rfl, .one hp e₁⟩
      | some l₀' =>
          simp only [Option.getD_some, Option.some.injEq] at e
          subst e
          obtain ⟨m, p₀, S₀, u₀, rfl, h₀⟩ := ih l₀' rfl
          exact ⟨m + 1, some (p₀.getD l₁), S₀, u₀, rfl, .step hp e₁ h₀⟩

/-- **A chain view's witness is a part of the record's escrow**, its location deleted:
`DeepInv` along the chain. -/
theorem chain_view_le {Θ : CodeTy} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hTI : TIT K Θ W ps rs) {r : FrameRecT K} (hr : r ∈ rs) {a : TRes K} (ha : AgWT W a) :
    ∀ n p l S u, ChainD r.R r.T r.v p l S u n → ∀ ψ : TCell K, a.get l = some ψ →
      ψ.kind ≠ Kind.own → ∃ q, ResUT.Le q r.R ∧ (∃ ζ, q.get l = some ζ) ∧ ψ.wit = q.del l := by
  intro n
  induction n with
  | zero =>
      intro p l S u hc ψ e hk
      cases p with
      | none => exact (hTI.1.1 r hr none l S u hc.chain a ha ψ e hk).2.2.2.1 rfl
      | some l₀ => obtain ⟨m, -, -, -, hm, -⟩ := hc.last l₀ rfl; omega
  | succ n ih =>
      intro p l S u hc ψ e hk
      cases p with
      | none => exact (hTI.1.1 r hr none l S u hc.chain a ha ψ e hk).2.2.2.1 rfl
      | some l₀ =>
          obtain ⟨m, p₀, S₀, u₀, hm, h₀⟩ := hc.last l₀ rfl
          obtain rfl : m = n := by omega
          obtain ⟨ψ₀, e₀, k₀, q, hq, hql, hw⟩ :=
            (hTI.1.1 r hr _ l S u hc.chain a ha ψ e hk).2.2.2.2 l₀ rfl
          obtain ⟨q₀, hq₀, ⟨ζ₀, eζ₀⟩, hw₀⟩ := ih p₀ l₀ S₀ u₀ h₀ ψ₀ e₀ k₀
          refine ⟨q, ResUT.Le.trans hq ?_, hql, hw⟩
          rw [hw₀]
          exact ResUT.Le.trans ⟨_, ResUT.del_compS eζ₀⟩ hq₀

/-! ### The innermost view -/

/-- **The innermost view above a lineage cell is the record's, or at a lineage location of it.**
A non-`imm` cell of `ag(ρ_rest)`, for `ρ_rest` a part of `W`, at a location where a lineage member
`d` of the record proper `p` holds a non-`imm` cell, sits beneath an `imm` cell `V` of `ρ_rest`
(at depth) whose location is `p`'s or a lineage location of `p`. -/
theorem innermost_view {Θ : CodeTy} {tc : TChoice K} {W ρo ρrest : TRes K}
    {ps rs : List (FrameRecT K)} {p : FrameRecT K} (hT : TWNT K Θ tc W ps rs) (hp : p ∈ ps)
    (hW : ResUT.CompS ρo ρrest W) {d : FrameRecT K} (hd : DescRT p d) {x : BoCa.Loc}
    {ζ : TCell K} (eζ : d.R.get x = some ζ) (kζ : ζ.kind ≠ Kind.imm) {ar : TRes K}
    (har : AgWT ρrest ar) {χ : TCell K} (eχ : ar.get x = some χ) (kχ : χ.kind ≠ Kind.imm) :
    ∃ (m₁ : BoCa.Loc) (V : TCell K), CellAt ρrest m₁ V ∧ V.kind = Kind.imm ∧
      (m₁ = p.le ∨ LinLocT p m₁) := by
  have hTI := hT.inv
  have hv := hT.valid
  have hU := hT.exclUnique
  have hcl := hTI.desc_closed
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  have hprs : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, [], .nil p⟩
  have hdrs : d ∈ rs := hcl p hprs d hd
  obtain ⟨pd, hpd⟩ := hd
  obtain ⟨m, χ', hm, hχ', ψ₀, c₀, k₀, -⟩ := agW_nonimm_beneath har x χ eχ kχ
  have hk₀ : ψ₀.kind ≠ Kind.imm := by rw [k₀]; exact kχ
  have c₁ : CellAt ρrest x ψ₀ := .nest hm c₀
  have hxR : CellAt p.R x ζ := hpd.cellAt (fun y φ e => .top e) x ζ eζ
  obtain ⟨ζW, eζW⟩ := le_view_cellAt hT hp hxR haW
  rcases cellAt_split c₁ with ⟨q, σ, hq, eσ⟩ | ⟨m₁, V, hV, kV, q, σ, hq, eσ⟩
  · -- `mut` cells only from the top: the cell is in `ex(W)_●`
    obtain ⟨σ', hq', eσ'⟩ := xpath_le ⟨ρo, ResUT.CompS.comm hW⟩ hq eσ hk₀
    obtain ⟨σW, eW, aW', heW, -, -⟩ := hv
    exact (ex_ag_disjoint hT.valid heW haW (xpath_ex heW hq' eσ' hk₀) eζW).elim
  · refine ⟨m₁, V, hV, kV, ?_⟩
    obtain ⟨a₁, a₂, -, ha₂, hcW⟩ := (AgWT.split hW).mp haW
    obtain ⟨V', eV', kV', -, wV', -⟩ :=
      icp_trans (cellAt_imm_icp hV ha₂) (icpAt_right hcW m₁) kV
    -- a proper ancestor of `p` would make `p.le` a `mut` cell at depth
    have notSub : ∀ r ∈ rs, ∀ q', q' ≠ [] → LinPathT r q' p → False := by
      intro r hr q' hq' hpath
      obtain ⟨r', hr', hsub⟩ := hpath.last hq'
      obtain ⟨-, ζr, eζr, kζr, -⟩ := hsub
      exact hTI.2.2.2.2.2.1.1 p hp
        ((hTI.recs_cellAt hv (hcl r hr r' hr') _ _ eζr).mutAt kζr)
    rcases hTI.2.2.2.2.2.2.2 aW haW m₁ V' eV' kV' with ⟨r, hr, hle, -, hwr⟩ |
        ⟨r, hr, pc, S, u, hc⟩
    · -- `V` is a record's cell over its escrow
      rw [← wV', hwr] at hq
      obtain ⟨e, he, rfl⟩ := xpath_linPath Θ q (hTI.1.2.2.2.1 r hr) hq
      obtain rfl := hU _ (hcl r hr _ ⟨q, he⟩) d hdrs x ψ₀ ζ eσ hk₀ eζ kζ
      rcases desc_comparable hU hcl _ r p _ q pd le_rfl hr hprs he hpd with hpr | hrp
      · rcases hpr.cases with rfl | ⟨pp, hpp, hpath⟩
        · exact Or.inl hle
        · obtain ⟨r', hr', hsub⟩ := hpath.last hpp
          obtain ⟨-, ζr, eζr, kζr, -⟩ := hsub
          exact Or.inr ⟨r', hr', ζr, hle ▸ eζr, by rw [kζr]; simp⟩
      · rcases hrp.cases with rfl | ⟨pp, hpp, hpath⟩
        · exact Or.inl hle
        · exact (notSub r hr pp hpp hpath).elim
    · -- `V` is a chain view: its witness is a part of the record's escrow
      obtain ⟨nc, hcD⟩ := hc.depth
      obtain ⟨qq, hqq, -, hqd⟩ :=
        chain_view_le hTI hr haW nc pc m₁ S u hcD V' eV' (by rw [kV']; simp)
      rw [← wV', hqd] at hq
      obtain ⟨σ₁, hq₁, eσ₁⟩ := xpath_del hq eσ
      obtain ⟨σ₂, hq₂, eσ₂⟩ := xpath_le hqq hq₁ eσ₁ hk₀
      obtain ⟨e, he, rfl⟩ := xpath_linPath Θ q (hTI.1.2.2.2.1 r hr) hq₂
      obtain rfl := hU _ (hcl r hr _ ⟨q, he⟩) d hdrs x ψ₀ ζ eσ₂ hk₀ eζ kζ
      have hown := hc.own
      rcases desc_comparable hU hcl _ r p _ q pd le_rfl hr hprs he hpd with hpr | hrp
      · exact Or.inr ⟨r, hpr, _, hown, by simp⟩
      · rcases hrp.cases with rfl | ⟨pp, hpp, hpath⟩
        · exact Or.inr ⟨_, ⟨[], .nil _⟩, _, hown, by simp⟩
        · exact (notSub r hr pp hpp hpath).elim

/-! ### The theorem -/

/-- **`EscBeneathT`.** -/
theorem escBeneathT : EscBeneathT := by
  intro K Θ tc W ρo ρrest ps rs p α n hT hp hW hFL hbr hnα d hd x ζ eζ kζ ar har χ eχ kχ _
  obtain ⟨m₁, V, hV, kV, hloc⟩ := innermost_view hT hp hW hd eζ kζ har eχ kχ
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  obtain ⟨a₁, a₂, -, ha₂, hcW⟩ := (AgWT.split hW).mp haW
  obtain ⟨V', eV', kV', -, -, lV'⟩ :=
    icp_trans (cellAt_imm_icp hV ha₂) (icpAt_right hcW m₁) kV
  obtain ⟨sV, hsV, hηV⟩ := CellUT.imm_eta kV
  have hlsV : V.lsOfI = some sV := by rw [hηV]; exact CellUT.lsOfI_immOf _ _ _ _
  have hlsV' : V.lsOf = some sV := by rw [hηV]; exact CellUT.lsOf_immOf _ _ _ _
  obtain ⟨y, hy⟩ := sV.ne
  obtain ⟨tV, htV⟩ := lsOf_of_imm kV'
  have hyV' : y ∈ tV.set := lV' sV tV hlsV htV y hy
  have hny : K.le n y := cellAt_onBranch hbr hV sV hlsV' y hy
  rcases hloc with h | hl
  · subst h
    exact hnα (hFL.1 aW haW V' tV eV' htV y hyV' ▸ hny)
  · exact hnα (K.trans hny (hFL.2 aW haW m₁ hl V' tV eV' htV y hyV'))

/-! ### The escrow's frame condition -/

/-- **`FdEscOfBranchT`.** -/
theorem fdEscOfBranch : FdEscOfBranchT :=
  fun _ _ _ _ _ _ _ _ _ _ _ hT hp hW hFL hbr hnα _ hτ =>
    ⟨fd_le_of_branch hT hp hW hFL hbr hnα hτ,
      fun _ heR _ hx => fd_esc_of_branch escBeneathT hT hp hW hFL hbr hnα hτ heR hx⟩

/-- **The other branches at their points, none inside `α`, hold nothing the lend lends.** -/
theorem fdEsc_of_points {Θ : CodeTy} {tc : TChoice K}
    {W : TRes K} {ps rs : List (FrameRecT K)} {p : FrameRecT K} {α : Life}
    (hT : TWNT K Θ tc W ps rs) (hp : p ∈ ps) (hFL : FrameLifeT K W p α) :
    ∀ {bs : List (TRes K)} {ns : List Life},
      List.Forall₂ (fun b n => OnBranchResT K n b) bs ns → (∀ n ∈ ns, ¬ K.le n α) →
      ∀ {ρo ρf : TRes K}, CompAllT bs ρf → ResUT.CompS ρo ρf W →
        NoneAt (escLocs p.le p.R) ρf := by
  intro bs ns hpts
  induction hpts with
  | nil =>
      intro _ ρo ρf hC _
      cases hC
      exact noneAt_empty _
  | @cons b n bs ns hbn _ ih =>
      intro hns ρo ρf hC hW
      cases hC with
      | @cons _ _ ρf' _ hC' hc =>
      have hv := hT.valid
      have hvf := (ResUT.Valid.split hW hv).2
      obtain ⟨hvb, hvf'⟩ := ResUT.Valid.split hc hvf
      obtain ⟨y, -, hyW⟩ := reassoc_out hW hc
      have hb : NoneAt (escLocs p.le p.R) b := fdEsc_iff_noneAt.mp
        (fdEscOfBranch _ _ _ _ _ _ _ _ _ _ _ hT hp hyW hFL hbn (hns n List.mem_cons_self))
      obtain ⟨y', -, hyW'⟩ := reassoc_out hW (ResUT.CompS.comm hc)
      exact NoneAt.compS hc hvb hvf' hb
        (ih (fun m hm => hns m (List.mem_cons_of_mem _ hm)) hC' hyW')

end BoCa.Fig16.Tree.Wp

end
