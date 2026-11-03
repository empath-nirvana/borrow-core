import DtorUnwind.TreeWp.ImmEndEsc
import DtorUnwind.Tree.CarrierGraftEx

/-!
# The escrow's frame condition and the cactus invariant

`FdEsc ℓ R Y` (`TreeWp/ImmEndEsc.lean`) is what `immEnd` asks of the rest of the world: `Y`'s
flattening holds nothing at the lent location `ℓ` nor at any location of `ex(R)`. At a resume of
the task owning the record, `Y` is the other branches.

**`CactusInvT` does not give it** (`cactusT_not_fdEsc`). Two branches: the parent holds
`ℓ ↦ imm({α}, loc m, m ↦ own(()))` and owns the record; a child holds the record's canonical
image at `β ⊏ α`, `m ↦ imm({β}, (), ∅)`, and owns nothing. Every clause of `CactusInvT` holds
(`cactusT_config`): the world is the branches' composition, the records proper are the parent's,
`RecInv` (the configuration is a `TWNT` world at the world's choice, tagged at `α`) and `WInv`
(covered, lowering to the memory `ℓ ↦ loc m, m ↦ ()`). The child's resource fails `FdEsc` at `m`,
so the join's condition at the escrow (`JoinReadyEscT`) fails at the parent's resume. This is the
state of program (b) after a child reborrows the parent's `imm` lend and before the join.

**What separates it is the branch.** `CactusInvT` records no branch point. The join's frame
condition at `ℓ` was derived on `tree-life` (`joinFd_of_branch`) from two hypotheses beside
`TWNC`: every cell of the other branches' flattening is on their branch `n` (`hbr`), and `n` is
not inside the lend (`¬ n ⊑ α`, `hnα`). In the configuration the child's branch is inside the
lend for every branch point its flattening sits on (`config_branch_inside`): its image is at
`β ⊑ α`, as `RebRecLeT` makes every image of a lineage location. So at the configuration `hnα`
fails (`config_branch_hyps`: `hbr` holds at the child's point `β`, and `β ⊑ α`), and nothing in
`CactusInvT` carries `hbr`.

`FdEscOfBranchT` states `FdEsc` from `TWNT`, the frame's lifetime and the two branch hypotheses:
the statement a cactus invariant carrying branch points, with the join read as `¬ n ⊑ α`, would
give. It is not derived here.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-! ### Branches -/

/-- A cell is on `n`'s branch: every lifetime it carries is `n` or nested above it
(`Tree/Frame.lean`'s `CellAbove`, over the tree carrier). -/
def CellAboveT (K : WCactus) (n : Life) (ψ : TCell K) : Prop :=
  ∀ s, ψ.lsOf = some s → ∀ x ∈ s.set, K.le n x

/-- Every cell of `ρ` is on `n`'s branch (`OnBranchRes` over the tree carrier). -/
def OnBranchResT (K : WCactus) (n : Life) (ρ : TRes K) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → CellAboveT K n ψ

/-! ### The configuration -/

/-- The tree: `β = 1` nested in `α = 2`. -/
abbrev KC : WCactus := K₁

/-- `α`, the parent's lend. -/
abbrev αC : Life := OrderDual.toDual 2

/-- `β`, the child's reborrow. -/
abbrev βC : Life := OrderDual.toDual 1

theorem βC_lt_αC : KC.lt βC αC := K₁_lt

/-- The world: the tree, the empty store typing, the `Classical` template choice. -/
abbrev wC : TWd := ⟨graftP, fun _ => none, tmplT KC (fun _ => none)⟩

/-- `ℓ = 1`, `m = 2`. -/
abbrev ℓC : BoCa.Loc := 1
abbrev mC : BoCa.Loc := 2

theorem ℓC_ne_mC : ℓC ≠ mC := by decide

/-- The parent's resource: the lent cell. -/
def parentRes : TRes KC := ResUT.single ℓC (lendCell αC mC)

/-- The child's resource: the canonical image. -/
def childRes : TRes KC := viewRes βC mC

/-- The branches: the parent owning the record, the child owning nothing. -/
def bsC : List (TBranch wC.K) := [(parentRes, [recE ℓC mC]), (childRes, [])]

/-- The list: the record, tagged at `α`. -/
def lsC : List (SRecT wC.K) := [(recE ℓC mC, αC)]

/-- The world's aliasable walk at `ℓ` and `m`: the lent cell, and the image. -/
theorem ag_config {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) {a : TRes KC}
    (ha : AgWT W a) :
    a.get ℓC = some (lendCell αC mC) ∧ a.get mC = some (viewCell βC) := by
  obtain ⟨a₃, ac, ha₃, hac, hc⟩ := (AgWT.split hW).mp ha
  obtain rfl := ag_view hac
  obtain ⟨hl, hm⟩ := ag_lend ℓC_ne_mC ha₃
  refine ⟨(ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ ℓC_ne_mC)).trans hl, ?_⟩
  rcases ResUT.Comp.get hc mC with ⟨f, -, -⟩ | ⟨χ, -, f, -⟩ | ⟨χ, f, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, e, hC⟩
  · rw [hm] at f; cases f
  · rw [viewRes, ResUT.single_get_self] at f; cases f
  · rw [hm] at f; cases f
  · rw [hm] at f₁; cases Option.some.inj f₁
    rw [viewRes, ResUT.single_get_self] at f₂; cases Option.some.inj f₂
    rw [e, CellUT.CompR.functional hC (CellUT.CompR.ownImm _ _ _ _)]
    rfl

/-- The record's lineage locations: `m` only (`ref 1` has no `Mut` position). -/
theorem linLoc_config {x : BoCa.Loc} (h : LinLocT (recE (K := KC) ℓC mC) x) : x = mC := by
  obtain ⟨d, ⟨p, hp⟩, ζ, eζ, -⟩ := h
  cases hp with
  | nil => exact (ResUT.single_get_eq_some eζ).1
  | cons hs hp' =>
      rename_i d' p'
      exact absurd ⟨_, List.cons_ne_nil _ _, LinPathT.cons hs (LinPathT.nil d')⟩
        (recE_no_desc ℓC mC d')

/-- The record's frame is at `α`: its view is the lent cell, and the image at its lineage
location is at `β ⊑ α`. -/
theorem frameLife_config {W : TRes KC} (hW : ResUT.CompS parentRes childRes W) :
    FrameLifeT KC W (recE ℓC mC) αC := by
  refine ⟨fun a ha ζ t e ht y hy => ?_, fun a ha x hx ψ s e hs y hy => ?_⟩
  · change a.get ℓC = some ζ at e
    rw [(ag_config hW ha).1] at e
    cases Option.some.inj e
    change some (TSet.single αC) = some t at ht
    cases Option.some.inj ht
    simpa [TSet.single_set] using hy
  · obtain rfl := linLoc_config hx
    rw [(ag_config hW ha).2] at e
    cases Option.some.inj e
    change some (TSet.single βC) = some s at hs
    cases Option.some.inj hs
    simp only [TSet.single_set, Finset.mem_singleton] at hy
    subst hy
    exact βC_lt_αC.1

/-- A covered `imm` cell over a covered witness. -/
theorem cov_imm_of_wit {Θ : LocTy} {K : WCactus} {l : BoCa.Loc} {ψ : TCell K}
    (hk : ψ.kind = Kind.imm) (hw : CovR Θ K ψ.wit) : Cov Θ K l ψ := by
  rcases CellUT.rep' ψ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, _, v, χ, hb, P, hP, rfl⟩
  · simp [CellUT.kind, CellUT.ownOf] at hk
  · exact .imm _ _ hw
  · simp [CellUT.kind, CellUT.mutOf] at hk

/-- **The configuration meets every clause of `CactusInvT`.** -/
theorem cactusT_config :
    ∃ (W : TRes wC.K) (μ : BoCa.Loc → Option BoCa.Val),
      ResUT.CompS parentRes childRes W ∧
      CactusInvT wC bsC W [recE ℓC mC] lsC μ := by
  obtain ⟨W, hW, hT⟩ := twnt_config (K := KC) (fun _ => none) βC_lt_αC ℓC_ne_mC
  obtain ⟨σ, hσ⟩ := hT.valid
  refine ⟨W, fun x => (σ.get x).map CellUT.erase, hW, ?_, ?_, ?_, ⟨hT, ?_⟩, ?_, ⟨σ, hσ, fun _ => rfl⟩⟩
  · exact .cons (.cons .nil (ResUT.compS_empty_right _)) hW
  · intro p; simp [bsC]
  · simp [bsC, Apart]
  · intro x hx
    simp only [lsC, List.mem_singleton] at hx
    subst hx
    exact ⟨recE ℓC mC, List.mem_singleton_self _, ⟨[], .nil _⟩, frameLife_config hW⟩
  · intro x ψ e
    have hk : ψ.kind = Kind.imm := by
      rcases compS_back hW e with ⟨ψ₀, e₀, k₀, -⟩ | ⟨ψ₀, e₀, k₀, -⟩
      · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
        exact k₀.symm.trans (CellUT.kind_immOf _ _ _ _)
      · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
        exact k₀.symm.trans (CellUT.kind_immOf _ _ _ _)
    refine cov_imm_of_wit hk fun y χ ey => ?_
    rcases compS_back hW e with ⟨ψ₀, e₀, -, w₀⟩ | ⟨ψ₀, e₀, -, w₀⟩
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
      have ew : (lendCell (K := KC) αC mC).wit = escR mC := CellUT.wit_immOf _ _ _ _
      rw [← w₀, ew, escR] at ey
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some ey
      exact .own _ _
    · obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e₀
      have ew : (viewCell (K := KC) βC).wit = PMap.empty := CellUT.wit_immOf _ _ _ _
      rw [← w₀, ew] at ey
      simp at ey

/-- **`CactusInvT` does not give the escrow's frame condition at a resume**: at a configuration
meeting every clause of `CactusInvT`, the parent's other branch (the child) fails `FdEsc` at the
record's location and escrow, so `JoinReadyEscT` fails. -/
theorem cactusT_not_fdEsc :
    ∃ (W : TRes wC.K) (μ : BoCa.Loc → Option BoCa.Val),
      CactusInvT wC bsC W [recE ℓC mC] lsC μ ∧
      ¬ FdEsc (recE (K := KC) ℓC mC).le (recE (K := KC) ℓC mC).R childRes ∧
      ¬ JoinReadyEscT (bsC.drop 1) (recE (K := KC) ℓC mC).le (recE (K := KC) ℓC mC).R := by
  obtain ⟨W, μ, -, hI⟩ := cactusT_config
  refine ⟨W, μ, hI, config_not_fdEsc, fun hJ => config_not_fdEsc (hJ childRes ?_)⟩
  exact .cons .nil (ResUT.compS_empty_right _)

/-- **The child's branch is inside the lend**: for every branch point `n` the child's flattening
sits on, `n ⊑ α`. So `joinFd_of_branch`'s `¬ n ⊑ α` is what fails at the configuration. -/
theorem config_branch_inside {n : Life}
    (hbr : ∀ τ, ResUT.Flat childRes τ → OnBranchResT KC n τ) : KC.le n αC := by
  obtain ⟨τ, hτ⟩ := valid_view (K := KC) βC mC
  have hf := hτ
  rw [flat_view hτ] at hf
  have := hbr _ hf mC (viewCell βC) (ResUT.single_get_self _ _) (TSet.single βC)
    (by rw [viewCell]; rfl) βC (by simp [TSet.single_set])
  exact KC.trans this βC_lt_αC.1

/-! ### The statement with branch points -/

/-- **The escrow's frame condition from branch points**, the statement that closes `FdEsc` once
the cactus records each branch's point: at a `TWNT` world, for a record proper `p` whose frame is
at `α`, a part `ρ_rest` of the world whose flattening is on a branch `n` not inside `α` holds
nothing at `p`'s location nor at its escrow's exclusive locations. `joinFd_of_branch`'s
hypotheses (`tree-life`), read at `FdEsc`. Not derived here. -/
def FdEscOfBranchT : Prop :=
  ∀ (K : WCactus) (Θ : CodeTy) (tc : TChoice K) (W ρo ρrest : TRes K)
    (ps rs : List (FrameRecT K)) (p : FrameRecT K) (α n : Life),
    TWNT K Θ tc W ps rs → p ∈ ps → ResUT.CompS ρo ρrest W → FrameLifeT K W p α →
    (∀ τ, ResUT.Flat ρrest τ → OnBranchResT K n τ) → ¬ K.le n α → FdEsc p.le p.R ρrest

/-- At the configuration, `FdEscOfBranchT`'s hypotheses hold but for `¬ n ⊑ α`, at the child's
own branch point `β`. -/
theorem config_branch_hyps :
    (∀ τ, ResUT.Flat childRes τ → OnBranchResT KC βC τ) ∧ KC.le βC αC := by
  refine ⟨fun τ hτ => ?_, βC_lt_αC.1⟩
  obtain rfl := flat_view hτ
  intro l ψ e s hs x hx
  obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
  change some (TSet.single βC) = some s at hs
  cases Option.some.inj hs
  simp only [TSet.single_set, Finset.mem_singleton] at hx
  subst hx
  exact KC.refl _

end BoCa.Fig16.Tree.Wp

end
