import Core.Chain.SI.MFrameK
import Core.Chain.SI.IStopRaiseN
import Core.Chain.SI.IStopF

/-!
# The Imm Frame across Kripke stops  `[spec §19, §27, §62]`

`docs/new-core/scope-835-iframes.md`. The `imm` lend frames (`erwp_I_frame` and its variants) at
`erwpK`, the stop choosing its floor (`SI/ErwpK.lean`). Every variant is one strong induction on
the index with three cases, each the existing one:

* **a return**: 6.64's end, the post read at the world the borrowed run chose;
* **a stop**: the borrow folded into the continuation's share (6.116, `iFoldV`); the lender's stop
  chooses its floor and owes its continuation at the worlds `y` its entry allows;
  `OpTabK.IFoldTwin` gives the borrowed entry's order at the borrowed share and the frame's
  invariant at `y`, where the frame is re-entered, lent again at the same `A`, by induction on the
  index; a cancellable stop's cancel obligation is the lender's by `hcan`, read at `y`;
* **a raise** (a `raise` or a cancel's `raise`): no continuation is owed, so no world is read; the
  case is the existing one (`IRaiseFold`).

`erwpK_I_frameGen` is that induction over any inner raise table `RI` and outer raise table `RO`,
with the lender's stops guarded by `G`. The variants (`Core/Chain/IFrameK835N.lean`) are its
instances.

**The typed world.** `ifoldTwin_owed` discharges `IFoldTwin` at `KW`: the lender's entries owe
along `KW.Owed` at the lender's world `x`, the borrowed run's along `KW.Owed` at the lend's world
`x.lendImm r A` (`Θ` with the record `(r, A)`, the view unchanged, the floor `A`). The lender's stop
chooses the floor `min f x.lo` for a borrowed stop at the floor `f ≤ A`:

* `ExtP` across the `imm` fold at any floor `f ≤ A` (`LocTy.ExtP.immFoldAt`): `ExtP` at the
  lender's share is `ExtP` at the borrowed share of the world with the record;
* the view consistent with the borrowed share (`consistentX_ifold`), from the validity of `π` and
  of the lender's post resource (`rwpG_I_frameGV`);
* `FoldInv A` at the resumption world from `KW.Owed`'s clause at every floor at or above the
  stop's.

**The share transfer.** `LocTy.ExtP.share`: `ExtP` at a share gives `ExtP` at a second share
whose borrow cells no longer-lived than the floor are dominated by the first's (`CellIn` inner `a`
→ `CellIn` outer `a`), `extF_fold`'s shape. The anti-frames read it (`SI/AFrameK.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable {ι : Type}

/-! ### The conditions on the tables -/

/-- `OpTabN.ILendOKR` and `OpTabN.ILendOKC` over a world index: the non-abortive entries not
unrestricted and resumed under `extF`; payloads and answers in `Res_A`, stable along `Ext`, at
every world. -/
structure OpTabK.ILendOKCR (T : OpTabK ι) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → ρ.InStratum A
  paExt : ∀ m i en, T m i = some en → ∀ k ls₁ ls₂ v (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PA k ls₁ v ρ → en.PA k ls₂ v ρ
  pbExt : ∀ m i en, T m i = some en → ∀ y k ls₁ ls₂ w (ρ : WRes), Ext ls₁ ls₂ ρ →
    en.PB y k ls₁ w ρ → en.PB y k ls₂ w ρ

/-- **The lender's table across the `imm` fold, at the floor-choosing stop.** `To` is `Ti`'s twin;
at the shares of the fold (`iFoldV`'s: `ρ_k ● ρ_p = X`, `X ● ρᵢ = Xᵢ`, the lender's share
`Xᵢ/ℓ ● ρ_ℓ ● ρ_P̂(v)`, both `Xᵢ` and the lender's share valid), for every floor `f` a borrowed stop
may choose, the lender's stop may choose a floor `f'` with every world its entry allows at `f'` at
the lender's share one the borrowed entry allows at `f` at the borrowed share, and one where `Inv`
holds. -/
def OpTabK.IFoldTwin (Inv : ι → Prop) (lo lo' : Life) (Ti To : OpTabK ι) (l : Loc) (A : Life)
    (v : Val) (ρP ρlP : WRes) (houtP : ρP.InStratum A) : Prop :=
  ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
    (en.abort = false → ∀ (ρk ρp X Xi ρkL : WRes), ResU.CompS ρk ρp X →
      ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi →
      ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi →
      ResU.CompS (Xi.del l) ρlP ρkL → ResU.Valid Xi → ResU.Valid ρkL →
      ∀ f, f ≤ lo → ∃ f', f' ≤ lo' ∧ ∀ y, en'.wk f' y ρkL → en.wk f y ρk ∧ Inv y)

theorem OpTabK.IFoldTwin.twin {Inv : ι → Prop} {lo lo' : Life} {Ti To : OpTabK ι} {l : Loc}
    {A : Life} {v : Val} {ρP ρlP : WRes} {houtP : ρP.InStratum A}
    (h : Ti.IFoldTwin Inv lo lo' To l A v ρP ρlP houtP) : Ti.Twin To := by
  intro m i en hTe
  obtain ⟨en', h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h m i en hTe
  exact ⟨en', h₁, h₂, h₃, h₄, h₅, h₆⟩

/-- **The cancel obligations across the `imm` fold** (`ICan` at every resumption world where `Inv`
holds, the only worlds the frame re-enters at): a cancellable stop's, the borrowed run's at the
frame's list and the borrowed share, is the lender's at the caller's list and the lender's share. -/
def ICanK (Inv : ι → Prop) (Ti To : ι → OpTabK ι) (l : Loc) (Ty : VTy) (δ : LSub) (A : Life)
    (v : Val) (ρP ρlP : WRes) (houtP : ρP.InStratum A) (ds : List FrameRec) : Prop :=
  ∀ x, Inv x → ∀ m i en en', Ti x m i = some en → To x m i = some en' → en.abort = false →
    en.q ≠ .lin → ∀ y, Inv y → ∀ k lsO (K : Kont) (ρk ρp X Xi ρkL : WRes),
      NoOwn ρp → ResU.CompS ρk ρp X →
      ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi →
      ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi →
      (Xi.del l).InStratum A → ResU.CompS (Xi.del l) ρlP ρkL →
      cancelOKK en y k (frameList ⟨l, v, ρP, Ty, δ⟩ ds A lsO) K ρk → cancelOKK en' y k lsO K ρkL

/-- A table of must-resume stops has no cancel obligation to carry. -/
theorem icanK_of_lin {Inv : ι → Prop} {Ti To : ι → OpTabK ι} {l : Loc} {Ty : VTy} {δ : LSub}
    {A : Life} {v : Val} {ρP ρlP : WRes} {houtP : ρP.InStratum A} {ds : List FrameRec}
    (hlin : ∀ x m i en, Ti x m i = some en → en.abort = false → en.q = .lin) :
    ICanK Inv Ti To l Ty δ A v ρP ρlP houtP ds := by
  intro x _ m i en _ hT _ ha hq
  exact absurd (hlin x m i en hT ha) hq

/-- **A raise across the `imm` fold**: a raise of the borrowed run at `RI`, at the frame's list, the
borrow garbage, is a raise of the lender at `RO` at the caller's list. A raise owes no
continuation, so it reads no world. -/
def IRaiseFold (l : Loc) (v : Val) (ρP ρlP : WRes) (A : Life) (houtP : ρP.InStratum A)
    (RI RO : TableK ι) : Prop :=
  ∀ k ls'' ls t (Ψ Ψ' : ContK ι) (ρ' ρp π Y : WRes), RI k ls'' t Ψ ρ' → NoOwn ρp →
    ResU.CompS ρ' ρp π →
    ResU.CompS (π.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) π →
    (π.del l).InStratum A → ResU.CompS (π.del l) ρlP Y →
    (∀ R Z, ResU.CompS R Z Y → R.InStratum A →
      (∀ ψ : CellU Loc Val, R.get l = some ψ → ψ.kind ≠ Kind.imm) → Ext ls'' ls R) →
    ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ RO k ls t Ψ' ρ'L

/-- **The Imm Frame builds no stop outside `Sched`**: when the borrowed table's resuming entries
are at names in `Sched` (the restriction's (S1)), `IFoldTwin` holds of the part of the lender's
table at those names and its raises (`OpTabK.schedPart`). -/
theorem OpTabK.IFoldTwin.schedPart {Inv : ι → Prop} {lo lo' : Life} {Ti To : OpTabK ι} {l : Loc}
    {A : Life} {v : Val} {ρP ρlP : WRes} {houtP : ρP.InStratum A}
    (h : Ti.IFoldTwin Inv lo lo' To l A v ρP ρlP houtP) {Sched : UInt32 → Prop}
    (hS : ∀ m i en, Ti m i = some en → en.abort = false → Sched m) :
    Ti.IFoldTwin Inv lo lo' (To.schedPart Sched) l A v ρP ρlP houtP := by
  classical
  intro m i en hTe
  obtain ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, h₆⟩ := h m i en hTe
  refine ⟨en', ?_, h₁, h₂, h₃, h₄, h₅, h₆⟩
  unfold OpTabK.schedPart
  rw [hTe']
  simp only
  rw [if_neg]
  rintro ⟨ha, hn⟩
  exact hn (hS m i en hTe (h₂ ▸ ha))

/-! ### The fold at a stop -/

/-- **`iFold`, with the fold's resource a part of `π`**: `ρ_a ● Xᵢ = π`, so `Xᵢ` is valid where
`π` is. -/
theorem iFoldV {l : Loc} {A : Life} {v : Val} {ρP ρlP ρa ρk ρp ρ' π Y : WRes}
    {houtP : ρP.InStratum A} (hρa : ρa.InStratum A) (hcak : ResU.CompS ρa ρk ρ')
    (h9 : ResU.CompS ρ' ρp π) (hnoρp : NoOwn ρp)
    (hGc : ResU.CompS (π.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) π)
    (hπdA : (π.del l).InStratum A) (hY : ResU.CompS (π.del l) ρlP Y) :
    ∃ (X Xi ρkL : WRes), ρa.get l = none ∧ ResU.CompS ρa ρkL Y ∧
      ResU.CompS (Xi.del l) ρlP ρkL ∧ (Xi.del l).InStratum A ∧ ResU.CompS ρk ρp X ∧
      ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi ∧
      ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi ∧
      ResU.CompS ρa Xi π ∧
      ∀ σB ρbB BI', ResU.CompS (Xi.del l) σB ρbB →
        ResU.CompS ρbB (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI' →
        ∃ Xk g, ResU.CompS ρk σB Xk ∧ ResU.CompS Xk g BI' ∧ NoOwn g := by
  obtain ⟨X, Xi, ρkL, hρal, haY, hkL, hXdA, hX, hXi, hXid, hre⟩ :=
    iFold hρa hcak h9 hnoρp hGc hπdA hY
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  refine ⟨X, Xi, ρkL, hρal, haY, hkL, hXdA, hX, hXi, hXid, ?_, hre⟩
  obtain ⟨X', hX', haX'⟩ := (ResU.CompS.assoc ρa ρk ρp π).mpr ⟨ρ', hcak, h9⟩
  obtain rfl : X = X' := ResU.CompS.functional hX hX'
  obtain ⟨π₂, hπ₂, hπ₂i⟩ := (ResU.CompS.assoc (π.del l) ρi ρi π).mp
    ⟨ρi, compS_imm_dup l _ v ρP houtP, hGc⟩
  obtain rfl : π = π₂ := ResU.CompS.functional hGc hπ₂
  obtain ⟨Xi', hXi', haXi⟩ := (ResU.CompS.assoc ρa X ρi π).mpr ⟨π, haX', hπ₂i⟩
  obtain rfl : Xi = Xi' := ResU.CompS.functional hXi hXi'
  exact haXi

/-! ### The frame -/

/-- **The Imm Frame across Kripke stops, over any raise tables.** `ℓ ↦ v ⋆ P̂(ls)(v) ⋆ ρ_b`, lent
`imm` at `A` to a computation in `erwpK` from `ρ_b ● ρᵢ` at `frameList p ds A ls`, that may stop at
the borrowed table (`Ti`'s stops at the floor bound `flI`, raises at `RI`) with the lend live: the
computation is in `erwpK`, its stops at `To`'s, guarded by `G`, at the floor bound `flO`, its raises
at `RO`.

At a return, 6.64, the post at the world the borrowed run chose. At a stop, the borrow folded into
the continuation's share (6.116); `IFoldTwin` gives the lender's floor, and at every world `y` the
lender's entry allows there the borrowed continuation at `y` and `Inv y`; the frame is re-entered
at `y`, lent again at `A`, at the index the resume is at. A cancellable stop's cancel obligation is
the lender's by `hcan`, read at `y`. The guard holds of the folded share by `hG`. A raise is
`hR`. -/
theorem erwpK_I_frameGen {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} (l : Loc)
    (Ty : VTy) (δ : LSub) (hadm : AdmWf Ty δ) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δ v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δ⟩ d)
    {flI flO : ι → Life} {Ti To : ι → OpTabK ι} {G : ι → ShareG} {RI RO : ι → TableK ι}
    (hT : ∀ x, (Ti x).ILendOKCR A)
    (hTT : ∀ x, Inv x → (Ti x).IFoldTwin Inv (flI x) (flO x) (To x) l A v ρP ρlP houtP)
    (hcan : ICanK Inv Ti To l Ty δ A v ρP ρlP houtP ds)
    (hG : ∀ x, Inv x → ∀ k ls (Xi ρkL : WRes), ResU.CompS (Xi.del l) ρlP ρkL → G x k ls ρkL)
    (hR : ∀ x, Inv x → IRaiseFold l v ρP ρlP A houtP (RI x) (RO x))
    {Q : ι → PostN} (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    ∀ n (x : ι), Inv x → ∀ ls e (ρb ρ : WRes), ρb.InStratum A → P ls v ρP →
      ResU.CompS ρlP ρb ρ →
      (∀ BI, ResU.CompS ρb (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) BI →
        erwpK (ℍ := ℍ) V Φ
          (fun y k ls t Ψ => BoLo.or (performStopK (flI y) (Ti y) k ls t Ψ) (RI y k ls t Ψ))
          (fun y => IFPost l v P A (Q y)) x n (frameList ⟨l, v, ρP, Ty, δ⟩ ds A ls) e BI) →
      erwpK (ℍ := ℍ) V Φ
        (fun y k ls t Ψ => BoLo.or (performStopGK (flO y) (To y) (G y) k ls t Ψ) (RO y k ls t Ψ))
        Q x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρb ρ houtb hPv hcρ hA
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have houtlP : ρlP.InStratum A := inStratum_ownP hclP houtP
  rw [erwpK_eq]
  refine rwpG_I_frameGV l Ty δ hadm v houtP houtb hclP hcρ (hPshape ls ρP hPv) hds ?_
    (fun BI hBI => by
      have h := hA BI hBI
      rw [erwpK_eq] at h
      exact h)
  intro k hk ls'' t ρ' ρp π Y hQin hnoρp h9 hls'' hGc hπdA hY hext hNX hvπ hvY
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  have hls''add : AddAt ls ls'' A :=
    ⟨fun x hx => (hls'' x).mpr ((addAt_frameList _ ds A ls).1 x hx),
     fun x hx hn => (addAt_frameList _ ds A ls).2 x ((hls'' x).mp hx) hn⟩
  rcases hQin with ⟨w, rfl, y₀, hy₀, hwand', houtρ'⟩ | ⟨K, m, i, v₀, en, hp⟩ | hr
  · -- a return: 6.64's end, the post at the world the borrowed run chose
    have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame houtρ' h9 hπl
    have hppl : ρp.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
      (ResU.Comp.get_of_left_none h9 hρ'l).symm.trans hπl
    have hpd : ResU.CompS (ρp.del l) ρi ρp := ResU.del_compS hppl
    obtain ⟨G', hG', hGi⟩ := (ResU.CompS.assoc ρ' (ρp.del l) ρi π).mp ⟨ρp, hpd, h9⟩
    have hGl : G'.get l = none :=
      (ResU.Comp.eq_none_iff hG' l).mpr ⟨hρ'l, ResU.del_get_self _ _⟩
    obtain rfl : G' = π.del l := eq_del_of_compS_single hGi hGl
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) ρlP Y).mpr ⟨_, hG', hY⟩
    obtain ⟨R, hR', hRY⟩ :=
      (ResU.CompS.assoc ρ' ρlP (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨X, hX, hXR⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v)) ρP R).mp ⟨ρlP, hclP, hR'⟩
    have hPv'' : P ls'' v ρP := hPloc ls ls'' ρP (extF_of_addAt hls''add ρP) hPv
    have hQ'' : Q y₀ k ls'' w R := (hwand' _ X rfl hX) ρP R hPv'' hXR
    have hRα : R.InStratum A := inStratum_compS hR' houtρ' houtlP
    have hRl : ∀ ψ : CellU Loc Val, R.get l = some ψ → ψ.kind ≠ Kind.imm := by
      intro ψ eψ
      obtain ⟨ψ₁, eψ₁, kψ₁, -⟩ := compS_get_right' hR'
        ((ResU.CompS.get_left_of_ne_imm hclP (ResU.single_get_self _ _) (by simp)).2)
      rw [eψ] at eψ₁; cases Option.some.inj eψ₁
      rw [kψ₁]; simp
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, y₀, hy₀, hQ y₀ k ls'' ls w R (hext R _ hRY hRα hRl) hQ''⟩⟩
  · -- a stop: the borrow folded into the lender's share, owed at every world the lender allows
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := (hT x).entry m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc', hwk⟩ := hTT x hx m i en hTe
    have hρa := (hT x).pa m i en hTe _ _ _ _ hPA
    obtain ⟨X, Xi, ρkL, hρal, haY, hkL, hXdA, hX, hXi, hXid, haXi, hre⟩ :=
      iFoldV hρa hcak h9 hnoρp hGc hπdA hY
    have hvXi : ResU.Valid Xi := (ResU.Valid.split haXi hvπ).2
    have hvkL : ResU.Valid ρkL := (ResU.Valid.split haY hvY).2
    obtain ⟨f', hf', hwk'⟩ := hwk ha ρk ρp X Xi ρkL hX hXi hXid hkL hvXi hvkL f hf
    have hPAo : en.PA k ls v₀ ρa := (hT x).paExt m i en hTe k ls'' ls v₀ ρa
      (hext ρa ρkL haY hρa (fun ψ h => by rw [hρal] at h; cases h)) hPA
    have hwcl : ∀ lsO, en'.wc ls lsO ρkL → extF ls lsO ρkL := by
      intro lsO he; rw [hwc', hwc] at he; exact he
    have hwcI : ∀ lsO, extF ls lsO ρkL →
        en.wc ls'' (frameList ⟨l, v, ρP, Ty, δ⟩ ds A lsO) ρk := by
      intro lsO he'
      rw [hwc]
      exact extF_ifold hX hXi (ResU.compS_single_get_self (ResU.CompS.comm hXid)
        (ResU.del_get_self _ _)) hkL hclP hNX hls'' he'
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPAo, hG x hx k ls Xi ρkL hkL, fun hu' => absurd (hq'.symm.trans hu') hq, f', hf',
        fun y hy lsO he => ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)⟩
    · -- the world the lender's continuation is resumed at, read at the borrowed share
      obtain ⟨hyi, hyInv⟩ := hwk' y hy
      simp only [erwpCK, show k' < n by omega, if_true]
      rw [hPB'] at hB
      have he' := hwcl lsO he
      obtain ⟨ρbB, hρbB, hWXB⟩ :=
        (ResU.CompS.assoc ρlP (Xi.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
      have hσBA : σB.InStratum A := (hT x).pb m i en hTe _ _ _ _ _ hB
      refine ih k' (by omega) y hyInv lsO _ ρbB XB (inStratum_compS hρbB hXdA hσBA)
        (hPloc ls lsO ρP (extF_right hclP (extF_right hkL he')) hPv) hWXB (fun BI' hBI' => ?_)
      have hB' : en.PB y k' (frameList ⟨l, v, ρP, Ty, δ⟩ ds A lsO) w σB :=
        (hT x).pbExt m i en hTe y k' lsO _ w σB (ext_add (addAt_frameList _ ds A lsO) hσBA) hB
      obtain ⟨Xk, g, hXk, hXkg, hg⟩ := hre σB ρbB BI' hρbB hBI'
      have hc := (hcont y hyi _ (hwcI lsO he')).1 k' hk' w σB Xk hB' hXk
      simp only [erwpCK, show k' < n by omega, if_true] at hc
      exact erwpK_garbage hXkg hg hc
    · -- a cancellable stop: the cancel obligation is the lender's, at the resumption world
      obtain ⟨hyi, hyInv⟩ := hwk' y hy
      have he' := hwcl lsO he
      have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan x hx m i en en' hTe hTe' ha hql' y hyInv k lsO K ρk ρp X Xi ρkL hnoρp hX hXi hXid
        hXdA hkL ((hcont y hyi _ (hwcI lsO he')).2 hql')
  · -- a raise: no continuation is owed
    obtain ⟨ρ'L, ρpL, hc, hno, hr'⟩ := hR x hx k ls'' ls t _ (erwpCK (ℍ := ℍ) V Φ
      (fun y k ls t Ψ => BoLo.or (performStopGK (flO y) (To y) (G y) k ls t Ψ) (RO y k ls t Ψ))
      Q n) ρ' ρp π Y hr hnoρp h9 hGc hπdA hY hext
    exact ⟨ρ'L, ρpL, hc, hno, Or.inr (Or.inr hr')⟩

/-! ### The raise cases -/

/-- A table with no abortive entry has no raise. -/
theorem iraiseFold_absurd {l : Loc} {v : Val} {ρP ρlP : WRes} {A : Life}
    {houtP : ρP.InStratum A} {T : OpTabK ι}
    (hab : ∀ m i en, T m i = some en → en.abort = false) (RO : TableK ι) :
    IRaiseFold l v ρP ρlP A houtP (raiseStopK T) RO := by
  intro k ls'' ls t Ψ Ψ' ρ' ρp π Y hr
  obtain ⟨K, m, i, v₀, en, hp⟩ := hr
  obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
  exact absurd ha (by rw [hab m i en hTe]; simp)

/-- **A `raise`, the cell and payload the claim it carries** (`erwp_I_frameR`'s case). -/
theorem iraiseFold_claim {l : Loc} {v : Val} {ρP ρlP : WRes} {A : Life}
    {houtP : ρP.InStratum A} (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {Ti To : OpTabK ι} (hTw : Ti.Twin To) (hT : Ti.ILendOKCR A) :
    IRaiseFold l v ρP ρlP A houtP (raiseStopK Ti) (raiseStopRK To (claimI l v ρP)) := by
  intro k ls'' ls t Ψ Ψ' ρ' ρp π Y hr hnoρp h9 hGc hπdA hY hext
  obtain ⟨K, m, i, v₀, en, hp⟩ := hr
  obtain ⟨⟨rfl, hK, hTe, ha⟩, τa, τn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
  obtain ⟨en', hTe', -, hab', hPA'', -, -⟩ := hTw m i en hTe
  have hρa := hT.pa m i en hTe _ _ _ _ hPA
  obtain ⟨X, Xi, ρkL, hρal, haY, hkL, -, hX, hXi, -, -⟩ :=
    iFold hρa hcan h9 hnoρp hGc hπdA hY
  have hnoXi : NoOwn Xi :=
    noOwn_compS hXi (noOwn_compS hX hnn hnoρp) (noOwn_single_imm l _ _ _ _)
  have hPA' : en.PA k ls v₀ τa := hT.paExt m i en hTe k ls'' ls v₀ τa
    (hext τa ρkL haY hρa (fun ψ h => by rw [hρal] at h; cases h)) hPA
  obtain ⟨D, hD, hDY⟩ := (ResU.CompS.assoc τa (Xi.del l) ρlP Y).mp ⟨ρkL, hkL, haY⟩
  exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty,
    ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨D, ρlP, hDY,
      ⟨τa, Xi.del l, hD, ⟨hPA'' ▸ hPA', hnA⟩, noOwn_del hnoXi l⟩, hclP⟩⟩⟩

/-- **A `raise` already carrying `R`, the cell and payload joining it** (`erwp_I_frameRR`'s
case). -/
theorem iraiseFold_claimR {l : Loc} {v : Val} {ρP ρlP : WRes} {A : Life}
    {houtP : ρP.InStratum A} (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {Ti To : OpTabK ι} (hTw : Ti.Twin To) (hT : Ti.ILendOKCR A) {R : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → ρ.InStratum A) :
    IRaiseFold l v ρP ρlP A houtP (raiseStopRK Ti R)
      (raiseStopRK To (fun k => claimI l v ρP k ⋆ R k)) := by
  intro k ls'' ls t Ψ Ψ' ρ' ρp π Y hr hnoρp h9 hGc hπdA hY hext
  obtain ⟨K, m, i, v₀, en, hp⟩ := hr
  obtain ⟨⟨rfl, hK, hTe, ha⟩, τ0, τR, hc0R, ⟨τa, τn, hcan, ⟨hPA, hnA⟩, hnn⟩, hRk⟩ :=
    pure_sep_iff.mp hp
  obtain ⟨en', hTe', -, hab', hPA'', -, -⟩ := hTw m i en hTe
  have hρa := hT.pa m i en hTe _ _ _ _ hPA
  obtain ⟨t1, ht1, hρ't1⟩ := compS_exch hcan hc0R
  have hρa' : t1.InStratum A := inStratum_compS ht1 hρa (hR _ _ hRk)
  obtain ⟨X, Xi, ρkL, hρal, haY, hkL, -, hX, hXi, -, -⟩ :=
    iFold hρa' hρ't1 h9 hnoρp hGc hπdA hY
  have hnoXi : NoOwn Xi :=
    noOwn_compS hXi (noOwn_compS hX hnn hnoρp) (noOwn_single_imm l _ _ _ _)
  obtain ⟨bc, hbc, hτaY⟩ := compS_reassoc ht1 haY
  have hτal : τa.get l = none := ((ResU.Comp.eq_none_iff ht1 l).mp hρal).1
  have hPA' : en.PA k ls v₀ τa := hT.paExt m i en hTe k ls'' ls v₀ τa
    (hext τa bc hτaY hρa (fun ψ h => by rw [hτal] at h; cases h)) hPA
  obtain ⟨ac, hac, hbc'⟩ := compS_lcomm hkL hbc
  obtain ⟨D, hD, hDY⟩ := compS_reassoc' hbc' hτaY
  exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty,
    ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨D, ac, hDY,
      ⟨τa, Xi.del l, hD, ⟨hPA'' ▸ hPA', hnA⟩, noOwn_del hnoXi l⟩,
      ⟨ρlP, τR, ResU.CompS.comm hac, hclP, hRk⟩⟩⟩⟩

/-- **A cancel's `raise`, the cell and payload the claim** (`erwp_I_frame_cancelRun`'s case): the
borrowed table has no abortive entry, so the cancel raises no error. -/
theorem icancelFold_claim {l : Loc} {v : Val} {ρP ρlP : WRes} {A : Life}
    {houtP : ρP.InStratum A} (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {Ti To : OpTabK ι} (hab : ∀ m i en, Ti m i = some en → en.abort = false) :
    IRaiseFold l v ρP ρlP A houtP (cancelRaiseK Ti) (cancelRaiseRK To (claimI l v ρP)) := by
  intro k ls'' ls t Ψ Ψ' ρ' ρp π Y hr hnoρp h9 hGc hπdA hY _
  obtain ⟨K, err, hp⟩ := hr
  obtain ⟨⟨rfl, hK⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
  cases err with
  | some E =>
      obtain ⟨m, j', w', en, he⟩ := herr
      obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
      exact absurd ha (by rw [hab _ _ en hTe]; simp)
  | none =>
  obtain rfl : τa = PMap.empty := herr.1
  obtain rfl := eq_of_compS_empty_left hcab
  have hnoπ : NoOwn π := noOwn_compS h9 hnb hnoρp
  exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty,
    ⟨K, none, pure_sep_mk ⟨rfl, hK⟩ ⟨π.del l, ρlP, hY,
      ⟨PMap.empty, π.del l, compS_empty_left _, emp_empty, noOwn_del hnoπ l⟩, hclP⟩⟩⟩

/-! ### The constant world -/

/-- `OpTabN.ILendOKR` at the lifted table. -/
theorem OpTabN.ILendOKR.liftK {T : OpTabN} {A : Life} (h : T.ILendOKR A) :
    (liftTabK T).ILendOKCR A where
  entry m i en hT ha := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact ⟨by show en₀.q ≠ .unr; rw [(h.entry m i en₀ h₀ ha).1]; decide,
      (h.entry m i en₀ h₀ ha).2⟩
  pa m i en hT := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pa m i en₀ h₀
  pb m i en hT _ := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pb m i en₀ h₀
  paExt m i en hT := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.paExt m i en₀ h₀
  pbExt m i en hT _ := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pbExt m i en₀ h₀

theorem OpTabN.ILendOK.toR {T : OpTabN} {A : Life} (h : T.ILendOK A) : T.ILendOKR A :=
  ⟨fun m i en hT _ => (h.entry m i en hT).2, h.pa, h.pb, h.paExt, h.pbExt⟩

/-- `OpTabN.ILendOKC` at the lifted table. -/
theorem OpTabN.ILendOKC.liftK {T : OpTabN} {A : Life} (h : T.ILendOKC A) :
    (liftTabK T).ILendOKCR A where
  entry m i en hT _ := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact (h.entry m i en₀ h₀).2
  pa m i en hT := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pa m i en₀ h₀
  pb m i en hT _ := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pb m i en₀ h₀
  paExt m i en hT := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.paExt m i en₀ h₀
  pbExt m i en hT _ := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pbExt m i en₀ h₀

/-- **`IFoldTwin` at one world**: a twin of the lifted table, every world allowed. -/
theorem ifoldTwin_lift {T T' : OpTabN} (hTw : T.Twin T') (lo : Life) (l : Loc) (A : Life)
    (v : Val) (ρP ρlP : WRes) (houtP : ρP.InStratum A) :
    (liftTabK T).IFoldTwin (fun _ => True) lo lo (liftTabK T') l A v ρP ρlP houtP := by
  intro m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', hq, ha, hPA, hPB, hwc⟩ := hTw m i en₀ h₀
  refine ⟨liftEntK en₀', liftTabK_of_some h₀', hq, ha, hPA, ?_, hwc,
    fun _ _ _ _ _ _ _ _ _ _ _ _ f hf => ⟨f, hf, fun _ _ => ⟨trivial, trivial⟩⟩⟩
  show (fun _ => en₀'.PB) = fun _ => en₀.PB
  rw [hPB]

/-- `erwp_I_frameT`'s `hcan` at one world. -/
theorem icanK_lift {T T' : OpTabN} {l : Loc} {Ty : VTy} {δ : LSub} {A : Life} {v : Val}
    {ρP ρlP : WRes} {houtP : ρP.InStratum A} {ds : List FrameRec}
    (hcan : ICan T T' l Ty δ A v ρP ρlP houtP ds) :
    ICanK (fun _ : Unit => True) (fun _ => liftTabK T) (fun _ => liftTabK T') l Ty δ A v ρP ρlP
      houtP ds := by
  intro _ _ m i en en' hT hT' _ hq _ _ k lsO K ρk ρp X Xi ρkL hno hX hXi hXid hXdA hkL
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some hT'
  intro hc
  exact (cancelOKK_liftEntK en₀' k lsO K ρkL).mpr (hcan m i en₀ en₀' h₀ h₀' hq k lsO K ρk ρp X Xi
    ρkL hno hX hXi hXid hXdA hkL ((cancelOKK_liftEntK en₀ k _ K ρk).mp hc))

/-! ### The typed world -/

/-- `Θ'.above a = Θ.above a` is kept by adding the same record to both. -/
theorem LocTy.above_addImm_congr {Θ Θ' : LocTy} {a : Life} (x : SRec)
    (h : Θ'.above a = Θ.above a) : (Θ'.addImm x).above a = (Θ.addImm x).above a := by
  refine LocTy.ext' (fun l b => ?_) ?_
  · have := congrArg (fun Θ₀ : LocTy => Θ₀ l b) h
    simpa only [LocTy.above_apply, LocTy.addImm_apply] using this
  · have := congrArg LocTy.imm h
    simp only [LocTy.above_imm, LocTy.addImm_imm] at this ⊢
    rw [List.filter_cons, List.filter_cons, this]

/-- **`ExtP` across the `imm` fold at a floor at or below the lend's.** The analogue of
`LocTy.ExtP.foldAt` for an `imm` lend: the lend's world adds the record `(r, A)` and no key. A
public extension of the lender's world at `f` at the lender's share `ρo` is a public extension at
`f` of the lend's world at the borrowed share `ρi`, when `A` is fresh, no record is lent at `A`, and
the borrowed share's borrow cells shorter-lived than `A` are the lender's. -/
theorem LocTy.ExtP.immFoldAt {Θ Θ' : LocTy} {f A : Life} (hfA : f ≤ A) {ρo ρi : WRes}
    (h : Θ.ExtP f Θ' ρo) (hfr : Θ.Fresh A) (hI : ∀ x ∈ Θ.imm, x.2 ≠ A)
    (hc : ∀ a, a < A → CellIn ρi a → CellIn ρo a) (r : FrameRec) :
    (Θ.addImm (r, A)).ExtP f (Θ'.addImm (r, A)) ρi := by
  refine ⟨⟨fun l₀ a G hG _ => ?_, fun x hx hcx => ?_⟩, fun l₀ b hb => h.2.1 l₀ b hb, ?_⟩
  · rw [LocTy.addImm_apply] at hG
    have hAa : A < a := hfr l₀ a (by rw [hG]; simp)
    refine ⟨by rw [LocTy.addImm_apply, h.2.1 l₀ a (lt_of_le_of_lt hfA hAa)]; exact hG, ?_⟩
    exact LocTy.above_addImm_congr _ (h.above_eq (le_trans hfA (le_of_lt hAa)))
  · rw [LocTy.addImm_imm] at hx ⊢
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    refine List.mem_cons_of_mem _ ?_
    rcases lt_or_ge f x.2 with hfx | hfx
    · have hm : x ∈ Θ.imm.filter (fun x => decide (f < x.2)) :=
        List.mem_filter.mpr ⟨hx, by simpa using hfx⟩
      rw [← h.2.2] at hm
      exact (List.mem_filter.mp hm).1
    · have hlt : x.2 < A := lt_of_le_of_ne (le_trans hfx hfA) (hI x hx)
      exact h.1.2 x hx (hc _ hlt hcx)
  · simp only [LocTy.addImm_imm, List.filter_cons]
    rw [h.2.2]

/-- **The share transfer**: `ExtP` at a share `ρo` gives `ExtP` at a share `ρi` whose borrow cells
no longer-lived than the floor are dominated by `ρo`'s (`extF_fold`'s shape). Above the floor
`ExtP` reads no share. -/
theorem LocTy.ExtP.share {lo : Life} {Θ Θ' : LocTy} {ρo ρi : WRes} (h : Θ.ExtP lo Θ' ρo)
    (hc : ∀ a, a ≤ lo → CellIn ρi a → CellIn ρo a) : Θ.ExtP lo Θ' ρi := by
  refine ⟨⟨fun l₀ a G hG hca => ?_, fun x hx hcx => ?_⟩, h.2.1, h.2.2⟩
  · rcases lt_or_ge lo a with hla | hla
    · exact ⟨by rw [h.2.1 l₀ a hla]; exact hG, h.above_eq (le_of_lt hla)⟩
    · exact h.1.1 l₀ a G hG (hc a hla hca)
  · rcases lt_or_ge lo x.2 with hlx | hlx
    · have hm : x ∈ Θ.imm.filter (fun x => decide (lo < x.2)) :=
        List.mem_filter.mpr ⟨hx, by simpa using hlx⟩
      rw [← h.2.2] at hm
      exact (List.mem_filter.mp hm).1
    · exact h.1.2 x hx (hc _ hlx hcx)

/-- **`ExtP` at a floor `f ≤ A` across the `imm` fold at a frame's shares**: the lender's share
`ρkL = Xᵢ/ℓ ● ρ_ℓ ● ρ_P̂(v)` and the borrowed one `ρk ⊆ X`, `X ● ρᵢ = Xᵢ`, `ρᵢ` the cell lent at
`A`. -/
theorem extP_ifoldFrameAt {Θ Θ' : LocTy} {f A : Life} (hfA : f ≤ A) (hfr : Θ.Fresh A)
    (hI : ∀ x ∈ Θ.imm, x.2 ≠ A) (r : FrameRec) {l : Loc} {v : Val} {ρP ρlP : WRes}
    {houtP : ρP.InStratum A} {ρk ρp X Xi ρkL : WRes} (hX : ResU.CompS ρk ρp X)
    (hXi : ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi)
    (hXid : ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi)
    (hkL : ResU.CompS (Xi.del l) ρlP ρkL) (h : Θ.ExtP f Θ' ρkL) :
    (Θ.addImm (r, A)).ExtP f (Θ'.addImm (r, A)) ρk := by
  refine h.immFoldAt hfA hfr hI (fun a ha hca => ?_) r
  obtain ⟨m, φ, e, hk, hle⟩ := CellIn.of_left hXi (CellIn.of_left hX hca)
  by_cases hm : m = l
  · subst hm
    have hXil : Xi.get m = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
      ResU.compS_single_get_self (ResU.CompS.comm hXid) (ResU.del_get_self _ _)
    rw [hXil] at e
    cases Option.some.inj e
    change A ≤ a at hle
    exact absurd (lt_of_le_of_lt hle ha) (lt_irrefl _)
  · exact CellIn.of_left hkL ⟨m, φ, by rw [ResU.del_get_ne _ hm]; exact e, hk, hle⟩

/-- **The world of an `imm` lend of `r` at `A`**: the record `(r, A)` added, the view unchanged,
the floor `A`. -/
def KW.lendImm (x : KW) (r : FrameRec) (A : Life) : KW :=
  ⟨x.Θ.addImm (r, A), x.c, A⟩

/-- The world with a record is one an interpretation runs at. -/
theorem LocTy.ok_addImm {Θ : LocTy} (hΘ : Θ.OK) (x : SRec) : (Θ.addImm x).OK :=
  ⟨fun l' b F h => hΘ.1 l' b F h, let ⟨N, hN⟩ := hΘ.2; ⟨N, fun l' b h => hN l' b h⟩⟩

/-- `FoldInv g` at the world with a record at `A ≠ g`. -/
theorem LocTy.FoldInv.addImm {Θ : LocTy} {g : Life} (h : Θ.FoldInv g) (r : FrameRec) {A : Life}
    (hgA : A ≠ g) : (Θ.addImm (r, A)).FoldInv g :=
  ⟨fun l b hb => h.1 l b hb, fun z hz => by
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hgA
    · exact h.2 z hz⟩

theorem LocTy.FoldInv.of_addImm {Θ : LocTy} {g A : Life} {r : FrameRec}
    (h : (Θ.addImm (r, A)).FoldInv g) : A ≠ g ∧ Θ.FoldInv g :=
  ⟨h.2 (r, A) List.mem_cons_self, fun l b hb => h.1 l b hb,
    fun z hz => h.2 z (List.mem_cons_of_mem _ hz)⟩

/-- An `imm` cell is consistent with every view: its exclusive walk is empty. -/
theorem consistentX_single_imm (c : Loc → Option Life) (l : Loc) (s : LSet) (v : Val) (χ : WRes)
    (h : χ.InStratum s.join) : ConsistentX c (ResU.single l (CellU.immOf s v χ h)) := by
  intro e he x ψ hg _
  obtain rfl : e = PMap.empty := ExS.functional he (ExW.empty_of_all_imm fun m ψ e => by
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
    exact CellU.kind_immOf _ _ _ _)
  cases hg

/-- **The view is consistent with the borrowed share** of an `imm` fold when it is with the
lender's share, both `Xᵢ` and the lender's share valid. -/
theorem consistentX_ifold {c : Loc → Option Life} {l : Loc} {A : Life} {v : Val} {ρP ρlP : WRes}
    {houtP : ρP.InStratum A} {ρk ρp X Xi ρkL : WRes} (hX : ResU.CompS ρk ρp X)
    (hXi : ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi)
    (hXid : ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi)
    (hkL : ResU.CompS (Xi.del l) ρlP ρkL) (hvXi : ResU.Valid Xi) (hvkL : ResU.Valid ρkL)
    (hc : ConsistentX c ρkL) : ConsistentX c ρk := by
  have hcXi := consistentX_compS hXid (consistentX_left hkL hc hvkL)
    (consistentX_single_imm c l _ v ρP houtP)
  have hvX : ResU.Valid X := (ResU.Valid.split hXi hvXi).1
  exact consistentX_left hX (consistentX_left hXi hcXi hvXi) hvX

/-- **The typed `imm` fold across a Kripke stop, at the floor the borrowed stop chose.** The
lender's stop at `x`, at a floor `f′ ≤ f`, `f ≤ A` the borrowed stop's, owes its continuation at `y`
(`KW.Owed`), and `FoldInv A` held at `x`. Then the lend's world at `y` is owed by the lend's world at
`x` at the floor `f`, at the borrowed share, and `y` keeps `FoldInv A`. -/
theorem kw_owed_ifoldAt {x y : KW} {r : FrameRec} {A : Life} (hx : x.Θ.FoldInv A) {f f' : Life}
    (hfA : f ≤ A) (hf' : f' ≤ f) {l : Loc} {v : Val} {ρP ρlP : WRes} {houtP : ρP.InStratum A}
    {ρk ρp X Xi ρkL : WRes} (hX : ResU.CompS ρk ρp X)
    (hXi : ResU.CompS X (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi)
    (hXid : ResU.CompS (Xi.del l) (ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP)) Xi)
    (hkL : ResU.CompS (Xi.del l) ρlP ρkL) (hvXi : ResU.Valid Xi) (hvkL : ResU.Valid ρkL)
    (hy : x.Owed f' y ρkL) :
    (x.lendImm r A).Owed f (y.lendImm r A) ρk ∧ y.Θ.FoldInv A := by
  refine ⟨⟨?_, LocTy.ok_addImm hy.2.1 _, consistentX_ifold hX hXi hXid hkL hvXi hvkL hy.2.2.1,
    le_rfl, fun g hfg hg => ?_⟩, hy.2.2.2.2 A (le_trans hf' hfA) hx⟩
  · exact (extP_ifoldFrameAt (le_trans hf' hfA) hx.1 hx.2 r hX hXi hXid hkL hy.1).mono hf'
  · obtain ⟨hAg, hg'⟩ := LocTy.FoldInv.of_addImm hg
    exact LocTy.FoldInv.addImm (hy.2.2.2.2 g (le_trans hf' hfg) hg') r hAg

/-- **`IFoldTwin` at the typed world.** The lender's entries owe along `KW.Owed` at the lender's
world `x`; the borrowed run's, at the lend's world (`KW.lendImm`); `FoldInv A` holds at `x`. A
borrowed stop at a floor `f ≤ A` is the lender's stop at `min f x.lo`, and the frame's invariant is
`FoldInv A`. -/
theorem ifoldTwin_owed {x : KW} {r : FrameRec} {A : Life} (hx : x.Θ.FoldInv A) {l : Loc}
    {v : Val} {ρP ρlP : WRes} {houtP : ρP.InStratum A} {Ti To : OpTabK KW}
    (hTw : ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, (x.lendImm r A).Owed f (z.lendImm r A) ρ → en.wk f z ρ) ∧
        (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ))) :
    Ti.IFoldTwin (fun y => y.Θ.FoldInv A) A x.lo To l A v ρP ρlP houtP := by
  intro m i en hTe
  obtain ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, hwk⟩ := hTw m i en hTe
  refine ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, fun ha ρk ρp X Xi ρkL hX hXi hXid hkL hvXi hvkL f hf =>
    ⟨min f x.lo, min_le_right _ _, fun y hy => ?_⟩⟩
  obtain ⟨hin, hout⟩ := hwk ha
  obtain ⟨h, hyA⟩ := kw_owed_ifoldAt (r := r) hx hf (min_le_left _ _) hX hXi hXid hkL hvXi hvkL
    (hout _ _ _ hy)
  exact ⟨hin _ _ _ h, hyA⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
