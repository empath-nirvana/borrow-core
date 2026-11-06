import Core.Chain.SI.ErwpK
import Core.Chain.SI.StopFrameN
import Core.Chain.SI.StopRaiseN
import Core.Chain.SI.StopCancelN
import Core.Chain.SI.AntiStopN
import Core.Chain.Reborrow791N

/-!
# The Mut Frame across Kripke stops  `[spec §19, §27, §62]`

`docs/new-core/scope-835-mframes.md`. The `mut` lend frames (`erwp_M_frame` and its variants) at
`erwpK`, the stop choosing its floor (`SI/ErwpK.lean`). Every variant is one strong induction on
the index with three cases, each the existing one:

* **a return**: 6.65's end, the post read at the world the borrowed run chose;
* **a stop**: the borrow folded into the continuation's share; the lender's stop chooses its floor
  and owes its continuation at the worlds `y` its entry allows; `OpTabK.FoldTwin` gives the
  borrowed entry's order at the borrowed share and the frame's invariant at `y`, where the frame is
  re-entered by induction on the index; a cancellable stop's cancel obligation is the lender's by
  `hcan`, read at `y`;
* **a raise** (a `raise` or a cancel's `raise`): no continuation is owed, so no world is read; the
  case is the existing one (`hR`).

`erwpK_M_frameGen` is that induction over any inner raise table `RI` and outer raise table `RO`,
with the lender's stops guarded by `G` (`opTableG`'s guard, `True` where there is none). The
variants (`Core/Chain/MFrameK835N.lean`) are its instances.

**The typed world.** `foldTwin_owed` discharges `FoldTwin` at `KW`: the lender's entries owe along
`KW.Owed` at the lender's world `x`, the borrowed run's along `KW.Owed` at the lend's world
`x.lend ℓ A F` (`Θ + (ℓ, A)`, the view at `ℓ` set to `A`, the floor `A`). The lender's stop chooses
the floor `min f x.lo` for a borrowed stop at the floor `f ≤ A`:

* `ExtP` across the fold at any floor `f ≤ A` (`LocTy.ExtP.foldAt`, `LocTy.ExtP.fold`'s proof with
  the floor read below the lend);
* the inner world's view consistent with the borrowed share (`consistentX_fold`), from the
  validity of the two post resources (`rwpG_M_frameGV`);
* `FoldInv A` at the resumption world from `KW.Owed`'s clause at every floor at or above the
  stop's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

variable {ι : Type}

/-! ### Tables at a world index -/

/-- `opTableG`'s perform stops at the Kripke stop: the continuation's share guarded by `G`. -/
def performStopGK (lo : Life) (T : OpTabK ι) (G : ShareG) : TableK ι := fun k ls t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntK ι) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆
        (en.PA k ls v ⋆ fun ρ => G k ls ρ ∧ contShareK en lo k ls K Ψ ρ)

/-- `raiseStopR` over a world index: a `raise` carrying `R`; it reads no world. -/
def raiseStopRK (T : OpTabK ι) (R : Nat → WProp) : TableK ι := fun k ls t _ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntK ι) =>
      ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
        T n i = some en ∧ en.abort = true⌝ ⋆
        (((fun ρ => en.PA k ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ) ⋆ R k)

/-- `errOkN` over a world index. -/
def errOkK (T : OpTabK ι) (k : Nat) (ls : List SRec) : Option Val → WProp
  | none => BoLo.emp
  | some E => ex fun (m : UInt32) => ex fun (j : UInt32) => ex fun (w : Val) =>
      ex fun (en : OpEntK ι) =>
        ⌜E = opPayload m j w ∧ T m j = some en ∧ en.abort = true⌝ ⋆
          fun ρ => en.PA k ls w ρ ∧ NoOwn ρ

/-- `cancelTabN`'s cancel `raise` over a world index; it reads no world. -/
def cancelRaiseK (T : OpTabK ι) : TableK ι := fun k ls t _ =>
  ex fun (K : Kont) => ex fun (err : Option Val) =>
    ⌜t = K.plug (raiseE (.val (cancelVal err))) ∧ K.Catches 0 = false⌝ ⋆
      (errOkK T k ls err ⋆ fun ρ => NoOwn ρ)

/-- `cancelTabR`'s cancel `raise`, carrying `R`, over a world index. -/
def cancelRaiseRK (T : OpTabK ι) (R : Nat → WProp) : TableK ι := fun k ls t _ =>
  ex fun (K : Kont) => ex fun (err : Option Val) =>
    ⌜t = K.plug (raiseE (.val (cancelVal err))) ∧ K.Catches 0 = false⌝ ⋆
      ((errOkK T k ls err ⋆ fun ρ => NoOwn ρ) ⋆ R k)

/-- `opTableR` at the floor bound `lo`. -/
def opTableRK (lo : Life) (T : OpTabK ι) (R : Nat → WProp) : TableK ι := fun k ls t Ψ =>
  BoLo.or (performStopK lo T k ls t Ψ) (raiseStopRK T R k ls t Ψ)

/-- `opTableG` at the floor bound `lo`. -/
def opTableGK (lo : Life) (T : OpTabK ι) (G : ShareG) : TableK ι := performStopGK lo T G

/-- `opTableGR` at the floor bound `lo`. -/
def opTableGRK (lo : Life) (T : OpTabK ι) (G : ShareG) (R : Nat → WProp) : TableK ι :=
  fun k ls t Ψ => BoLo.or (performStopGK lo T G k ls t Ψ) (raiseStopRK T R k ls t Ψ)

/-- `cancelTabN` at the floor bound `lo`, the stop first. -/
def cancelTabK (lo : Life) (T : OpTabK ι) : TableK ι := fun k ls t Ψ =>
  BoLo.or (performStopK lo T k ls t Ψ) (cancelRaiseK T k ls t Ψ)

/-- `cancelTabR` at the floor bound `lo`, the stop first. -/
def cancelTabRK (lo : Life) (T : OpTabK ι) (R : Nat → WProp) : TableK ι := fun k ls t Ψ =>
  BoLo.or (performStopK lo T k ls t Ψ) (cancelRaiseRK T R k ls t Ψ)

/-- `cancelTabGR` at the floor bound `lo`, the stop first. -/
def cancelTabGRK (lo : Life) (T : OpTabK ι) (G : ShareG) (R : Nat → WProp) : TableK ι :=
  fun k ls t Ψ => BoLo.or (performStopGK lo T G k ls t Ψ) (cancelRaiseRK T R k ls t Ψ)

/-- An unguarded stop is a stop guarded by `True`, and conversely. -/
theorem performStopGK_true_iff (lo : Life) (T : OpTabK ι) (k : Nat) (ls : List SRec) (t : Expr)
    (Ψ : ContK ι) (ρ : WRes) :
    performStopGK lo T (fun _ _ _ => True) k ls t Ψ ρ ↔ performStopK lo T k ls t Ψ ρ := by
  constructor
  · rintro ⟨K, n, i, v, en, h⟩
    obtain ⟨hp, ρa, ρk, hc, hA, -, hcs⟩ := pure_sep_iff.mp h
    exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hcs⟩⟩
  · rintro ⟨K, n, i, v, en, h⟩
    obtain ⟨hp, ρa, ρk, hc, hA, hcs⟩ := pure_sep_iff.mp h
    exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, trivial, hcs⟩⟩

theorem performStopGK_local (lo : Life) (T : OpTabK ι) (G : ShareG) :
    (performStopGK lo T G).Local := by
  intro k ls t Ψ Ψ' ρ hΨ ⟨K, n, i, v, en, h⟩
  obtain ⟨hp, ρa, ρk, hc, hA, hG, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hG, hu, f, hf, fun y hy ls' he =>
    ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ y k' hk _ _ _ ((hcont y hy ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
      (hcont y hy ls' he).2⟩⟩⟩

/-- A table whose second disjunct reads no continuation is local when its first is. -/
theorem or_local {Tb₁ Tb₂ : TableK ι} (h₁ : Tb₁.Local)
    (h₂ : ∀ k ls t (Ψ Ψ' : ContK ι) ρ, Tb₂ k ls t Ψ ρ → Tb₂ k ls t Ψ' ρ) :
    TableK.Local (fun k ls t Ψ => BoLo.or (Tb₁ k ls t Ψ) (Tb₂ k ls t Ψ) : TableK ι) := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with h | h
  · exact Or.inl (h₁ k ls t Ψ Ψ' ρ hΨ h)
  · exact Or.inr (h₂ k ls t Ψ Ψ' ρ h)

/-! ### The conditions on the tables -/

/-- `OpTabN.LendOKCR` over a world index: the non-abortive entries not unrestricted and resumed
under `extF`; what passes out outlives `A`, what passes in holds nothing shorter, at every world. -/
structure OpTabK.LendOKCR (T : OpTabK ι) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → ρ.InStratum (↓A)

/-- `OpTabN.Twin` over a world index: `T′` has `T`'s entries up to their orders and cancel
obligations. -/
def OpTabK.Twin (T T' : OpTabK ι) : Prop :=
  ∀ m i en, T m i = some en → ∃ en', T' m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc

/-- **The lender's table across the fold, at the floor-choosing stop.** `To` is `Ti`'s twin; at
the shares of a fold at `ℓ` (`extF_fold`'s, both post resources valid), for every floor `f` a
borrowed stop may choose, the lender's stop may choose a floor `f'` with every world its entry
allows at `f'` at the lender's share one the borrowed entry allows at `f` at the borrowed share,
and one where `Inv` holds. -/
def OpTabK.FoldTwin (Inv : ι → Prop) (lo lo' : Life) (Ti To : OpTabK ι) (l : Loc) (A : Life) :
    Prop :=
  ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
    (en.abort = false → ∀ (ρk ρp Z W'' ρkL χ : WRes) (v : Val) (hχ : χ.InStratum A)
      (P : Val → SPropS Loc Val A) (hw : P v ⟨χ, hχ⟩), ResU.CompS ρk ρp Z →
      Z.get l = some (CellU.mutOf A v χ hχ P hw) →
      ResU.CompS χ (ResU.single l (CellU.ownOf v)) W'' → ResU.CompS (Z.del l) W'' ρkL →
      ResU.Valid Z → ResU.Valid ρkL →
      ∀ f, f ≤ lo → ∃ f', f' ≤ lo' ∧ ∀ y, en'.wk f' y ρkL → en.wk f y ρk ∧ Inv y)

theorem OpTabK.FoldTwin.twin {Inv : ι → Prop} {lo lo' : Life} {Ti To : OpTabK ι} {l : Loc}
    {A : Life} (h : Ti.FoldTwin Inv lo lo' To l A) : Ti.Twin To := by
  intro m i en hTe
  obtain ⟨en', h₁, h₂, h₃, h₄, h₅, h₆, -⟩ := h m i en hTe
  exact ⟨en', h₁, h₂, h₃, h₄, h₅, h₆⟩

/-! ### The frame -/

/-- **The Mut Frame across Kripke stops, over any raise tables.** `ℓ ↦ v ⋆ ρ_P ⋆ ρ_b`, lent at
`A` with the stored predicate `P̂ ⊆ F j`, `j ≥ n`, to a computation in `erwpK` at
`Φ[ℓ ↦ (A, F)]` that may stop at the borrowed table (`Ti`'s stops at the floor bound `flI`,
raises at `RI`) with the lend live: the computation is in `erwpK` at `Φ`, its stops at `To`'s,
guarded by `G`, at the floor bound `flO`, its raises at `RO`.

At a return, 6.65, the post at the world the borrowed run chose. At a stop, the borrow folded
into the continuation's share; `FoldTwin` gives the lender's floor, and at every world `y` the
lender's entry allows there the borrowed continuation at `y` and `Inv y`; the frame is
re-entered at `y` at the index the resume is at. A cancellable stop's cancel obligation is the
lender's by `hcan`, read at `y`. The guard holds of the folded share by `hG`. A raise is `hR`. -/
theorem erwpK_M_frameGen {V : ι → ι → Prop} {Φ : ι → LocFam} {Inv : ι → Prop} {l : Loc}
    {A : Life} {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {flI flO : ι → Life}
    {Ti To : ι → OpTabK ι} {G : ι → ShareG} {RI RO : ι → TableK ι}
    (hT : ∀ x, (Ti x).LendOKCR A)
    (hTT : ∀ x, Inv x → (Ti x).FoldTwin Inv (flI x) (flO x) (To x) l A)
    (hcan : ∀ x, Inv x → ∀ m i en en', Ti x m i = some en → To x m i = some en' →
      en.abort = false → en.q ≠ .lin →
      ∀ y k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes)
        (hχ : χ.InStratum A) (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKK en y k ls K ρk → cancelOKK en' y k ls K ρkL)
    (hG : ∀ x, Inv x → ∀ k ls (Z W'' ρkL : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
      (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
      (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
      ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
      G x k ls ρkL)
    (hR : ∀ x, Inv x → ∀ k ls' t (Ψ Ψ' : ContK ι) (ρ' ρp X : WRes), RI x k ls' t Ψ ρ' →
      NoOwn ρp → ResU.CompS ρ' ρp X → X.InStratum (↓A) →
      ∀ (v'' : Val) (χ : WRes) (hχ : χ.InStratum A) (P'' : Val → SPropS Loc Val A)
        (hw'' : P'' v'' ⟨χ, hχ⟩), (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
      ResU.CompS (X.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X →
      ∀ W'', ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' →
      ∀ Y, ResU.CompS (X.del l) W'' Y →
      ∃ ρ'L ρpL, ResU.CompS ρ'L ρpL Y ∧ NoOwn ρpL ∧ RO x k ls' t Ψ' ρ'L)
    {Q : ι → PostN} :
    ∀ n j, n ≤ j → ∀ (x : ι), Inv x → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes)
      (houtP : ρP.InStratum A), ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwpK (ℍ := ℍ) V (fun y => (Φ y).set l A F)
          (fun y k ls t Ψ => BoLo.or (performStopK (flI y) (Ti y) k ls t Ψ) (RI y k ls t Ψ))
          (fun y => MFPost l A F (Q y)) x n ls e BM) →
      erwpK (ℍ := ℍ) V Φ
        (fun y k ls t Ψ => BoLo.or (performStopGK (flO y) (To y) (G y) k ls t Ψ) (RO y k ls t Ψ))
        Q x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwpK_eq]
  refine rwpG_M_frameGV hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwpK_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY hvX hvY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, y₀, hy₀, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ | hr
  · -- a return: 6.65's end, the post at the world the borrowed run chose
    rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR', hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR'⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, y₀, hy₀, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · -- a stop: the borrow folded into the lender's share, owed at every world the lender allows
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := (hT x).entry m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc', hwk⟩ := hTT x hx m i en hTe
    have hρa := (hT x).pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc ρa ρk ρp X).mpr ⟨ρ', hcak, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Z.del l) W'' Y).mpr ⟨_, hD, hY⟩
    have hdZd : (Z.del l).InStratum (↓A) :=
      ResU.CompS.inStratum_left hZd (ResU.CompS.inStratum_right haZ hdX)
    have hvZ : ResU.Valid Z := (ResU.Valid.split haZ hvX).2
    have hvkL : ResU.Valid ρkL := (ResU.Valid.split haY hvY).2
    obtain ⟨f', hf', hwk'⟩ := hwk ha ρk ρp Z W'' ρkL χ v'' hχ P'' hw'' hZ hZl hW'' hkL hvZ hvkL f hf
    have he' : ∀ ls'', en'.wc ls' ls'' ρkL → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW''
        hkL he
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPA, hG x hx k ls' Z W'' ρkL v'' χ hχ P'' hw'' hPk hW'' hkL,
        fun hu' => absurd (hq'.symm.trans hu') hq, f', hf', fun y hy ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)⟩
    · -- the world the lender's continuation is resumed at, read at the borrowed share
      obtain ⟨hyi, hyInv⟩ := hwk' y hy
      simp only [erwpCK, show k' < n by omega, if_true]
      rw [hPB'] at hB
      obtain ⟨ρbB, hρbB, hWXB⟩ :=
        (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
      have hdB : ρbB.InStratum (↓A) :=
        inStratum_compS hρbB hdZd ((hT x).pb m i en hTe _ _ _ _ _ hB)
      refine ih k' (by omega) k (le_of_lt hk') y hyInv ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk
        hw'' (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
      obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
        (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
      obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
        (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
          ⟨s1, ResU.CompS.comm hs1, hZds1⟩
      obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
      obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
      obtain ⟨Xk, hXk, hXkp⟩ :=
        (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
      have hc := (hcont y hyi ls'' (he' ls'' he)).1 k' hk' w σB Xk hB hXk
      simp only [erwpCK, show k' < n by omega, if_true] at hc
      exact erwpK_garbage hXkp hnoρp hc
    · -- a cancellable stop: the cancel obligation is the lender's, at the resumption world
      obtain ⟨hyi, -⟩ := hwk' y hy
      have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan x hx m i en en' hTe hTe' ha hql' y k ls'' K ρk ρp Z ρkL W'' v'' χ hχ P'' hw''
        hnoρp hZ hZd hdZd hPk hW'' hkL ((hcont y hyi ls'' (he' ls'' he)).2 hql')
  · -- a raise: no continuation is owed
    obtain ⟨ρ'L, ρpL, hc, hno, hr'⟩ := hR x hx k ls' t _ (erwpCK (ℍ := ℍ) V Φ
      (fun y k ls t Ψ => BoLo.or (performStopGK (flO y) (To y) (G y) k ls t Ψ) (RO y k ls t Ψ))
      Q n) ρ' ρp X hr hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
    exact ⟨ρ'L, ρpL, hc, hno, Or.inr (Or.inr hr')⟩

/-! ### The typed world -/

/-- **`ExtP` across the fold at a floor at or below the lend's.** `LocTy.ExtP.fold`'s proof, the
floor `f ≤ A` read where it reads `A`: a public extension of the lender's world at `f` is a public
extension at `f` of the lend's world, at the borrowed share. -/
theorem LocTy.ExtP.foldAt {Θ Θ' : LocTy} {f A : Life} (hfA : f ≤ A) {ρo ρi : WRes}
    (h : Θ.ExtP f Θ' ρo) (hfr : Θ.Fresh A) (hI : ∀ x ∈ Θ.imm, x.2 ≠ A)
    (hc : ∀ a, a < A → CellIn ρi a → CellIn ρo a) (l : Loc) (F : Nat → Val → SPropS Loc Val A) :
    (Θ.add l A F).ExtP f (Θ'.add l A F) ρi := by
  refine ⟨⟨fun l₀ a G hG _ => ?_, fun x hx hcx => ?_⟩, fun l₀ b hb => ?_, ?_⟩
  · by_cases ha : a = A
    · subst ha
      by_cases hl : l₀ = l
      · subst hl
        rw [LocTy.add_self] at hG
        refine ⟨by rw [LocTy.add_self]; exact hG, ?_⟩
        rw [LocTy.above_add _ _ (lt_irrefl a), LocTy.above_add _ _ (lt_irrefl a)]
        exact h.above_eq hfA
      · rw [LocTy.add_other Θ hl] at hG
        exact absurd (hfr l₀ a (by rw [hG]; simp)) (lt_irrefl _)
    · rw [LocTy.add_keep Θ l F l₀ ha] at hG
      have hAa : A < a := hfr l₀ a (by rw [hG]; simp)
      refine ⟨by rw [LocTy.add_keep Θ' l F l₀ ha, h.2.1 l₀ a (lt_of_le_of_lt hfA hAa)]; exact hG,
        ?_⟩
      rw [LocTy.above_add _ _ (not_lt_of_gt hAa), LocTy.above_add _ _ (not_lt_of_gt hAa)]
      exact h.above_eq (le_trans hfA (le_of_lt hAa))
  · change x ∈ Θ.imm at hx
    change x ∈ Θ'.imm
    rcases lt_or_ge A x.2 with hA | hA
    · have hm : x ∈ Θ.imm.filter (fun x => decide (f < x.2)) :=
        List.mem_filter.mpr ⟨hx, by simpa using lt_of_le_of_lt hfA hA⟩
      rw [← h.2.2] at hm
      exact (List.mem_filter.mp hm).1
    · have hlt : x.2 < A := lt_of_le_of_ne hA (hI x hx)
      exact h.1.2 x hx (hc _ hlt hcx)
  · by_cases hbA : b = A
    · subst hbA
      by_cases hl : l₀ = l
      · subst hl; rw [LocTy.add_self, LocTy.add_self]
      · rw [LocTy.add_other Θ' hl, LocTy.add_other Θ hl]; exact h.2.1 l₀ b hb
    · rw [LocTy.add_keep _ _ _ _ hbA, LocTy.add_keep _ _ _ _ hbA]; exact h.2.1 l₀ b hb
  · simp only [LocTy.add_imm]
    exact h.2.2

/-- **`ExtP` at a floor `f ≤ A` across the fold at a frame's shares** (`extP_foldFrame` at `f`):
the lender's share `ρkL = Z/ℓ ● W″` and the borrowed one `ρk ⊆ Z`, `Z`'s cell at `ℓ` lent at `A`. -/
theorem extP_foldFrameAt {Θ Θ' : LocTy} {f A : Life} (hfA : f ≤ A) (hfr : Θ.Fresh A)
    (hI : ∀ x ∈ Θ.imm, x.2 ≠ A) {l : Loc} (F : Nat → Val → SPropS Loc Val A)
    {ρk ρp Z W'' ρkL : WRes} {ψ : CellU Loc Val} (hZ : ResU.CompS ρk ρp Z)
    (hZl : Z.get l = some ψ) (hat : ψ.at = A) (hkL : ResU.CompS (Z.del l) W'' ρkL)
    (h : Θ.ExtP f Θ' ρkL) : (Θ.add l A F).ExtP f (Θ'.add l A F) ρk := by
  refine h.foldAt hfA hfr hI (fun a ha hca => ?_) l F
  obtain ⟨m, φ, e, hk, hle⟩ := CellIn.of_left hZ hca
  by_cases hm : m = l
  · subst hm
    rw [hZl] at e
    cases Option.some.inj e
    rw [hat] at hle
    exact absurd (lt_of_le_of_lt hle ha) (lt_irrefl _)
  · exact CellIn.of_left hkL ⟨m, φ, by rw [ResU.del_get_ne _ hm]; exact e, hk, hle⟩

/-- **The world of a `mut` lend at `ℓ`, `A`**: the key `(ℓ, A)` added, the view at `ℓ` set to `A`,
the floor `A`. Its view is the relation's `Φ.set ℓ A F` (`LocTy.view_add`). -/
def KW.lend (x : KW) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) : KW :=
  ⟨x.Θ.add l A F, setLife x.c l A, A⟩

theorem KW.lend_view (x : KW) (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) :
    (x.lend l A F).Θ.view (x.lend l A F).c = (x.Θ.view x.c).set l A F :=
  LocTy.view_add x.Θ x.c l A F

/-- `FoldInv g` at the lend's world: `g` below the lend, and `FoldInv g` at the lender's. -/
theorem LocTy.FoldInv.of_add {Θ : LocTy} {l : Loc} {A g : Life}
    {F : Nat → Val → SPropS Loc Val A} (h : (Θ.add l A F).FoldInv g) : g < A ∧ Θ.FoldInv g := by
  have hgA : g < A := h.1 l A (by rw [LocTy.add_self]; simp)
  refine ⟨hgA, fun x b hb => ?_, h.2⟩
  by_cases hbA : b = A
  · subst hbA; exact hgA
  · exact h.1 x b (by rw [LocTy.add_keep _ _ _ _ hbA]; exact hb)

theorem LocTy.FoldInv.add {Θ : LocTy} {g A : Life} (h : Θ.FoldInv g) (hgA : g < A) (l : Loc)
    (F : Nat → Val → SPropS Loc Val A) : (Θ.add l A F).FoldInv g :=
  ⟨LocTy.fresh_add h.1 le_rfl hgA l F, h.2⟩

/-- The lend's world is one an interpretation runs at. -/
theorem LocTy.ok_add {Θ : LocTy} (hΘ : Θ.OK) (l : Loc) {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) : (Θ.add l A F).OK := by
  refine ⟨LocTy.down_add hΘ.1 l hF, ?_⟩
  obtain ⟨N, hN, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓A)
  exact ⟨N, LocTy.fresh_add hfr le_rfl (lt_of_le_of_lt hN (Life.down_sqsubset A)) l F⟩

/-- **The lend's view is consistent with the borrowed share** when the lender's view is consistent
with the lender's share, at a fold at `ℓ` with both resources valid: the borrowed share is part
of `Z = Z/ℓ ● ℓ ↦ mut(A, v, χ)`, `Z/ℓ` and `χ` parts of the lender's share, and the view at `ℓ` is
`A`. -/
theorem consistentX_fold {c : Loc → Option Life} {l : Loc} {A : Life} {ρk ρp Z W'' ρkL χ : WRes}
    {v : Val} {hχ : χ.InStratum A} {P : Val → SPropS Loc Val A} {hw : P v ⟨χ, hχ⟩}
    (hZ : ResU.CompS ρk ρp Z) (hZl : Z.get l = some (CellU.mutOf A v χ hχ P hw))
    (hW'' : ResU.CompS χ (ResU.single l (CellU.ownOf v)) W'') (hkL : ResU.CompS (Z.del l) W'' ρkL)
    (hvZ : ResU.Valid Z) (hvkL : ResU.Valid ρkL) (hc : ConsistentX c ρkL) :
    ConsistentX (setLife c l A) ρk := by
  have hZd := ResU.del_compS hZl
  have hkm : (CellU.mutOf A v χ hχ P hw).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hcD : ConsistentX c (Z.del l) := consistentX_left hkL hc hvkL
  have hvW : ResU.Valid W'' := (ResU.Valid.split hkL hvkL).2
  have hcχ : ConsistentX c χ := consistentX_left hW'' (consistentX_right hkL hc hvkL) hvW
  have hvm : ResU.Valid (ResU.single l (CellU.mutOf A v χ hχ P hw)) :=
    (ResU.Valid.split hZd hvZ).2
  have hcD' := consistentX_setLife hcD
    (exS_none_of_part (ResU.CompS.comm hZd) hvZ (ResU.single_get_self _ _) hkm) A
  have hcm : ConsistentX (setLife c l A) (ResU.single l (CellU.mutOf A v χ hχ P hw)) :=
    consistentX_single_mut (consistentX_setLife hcχ (exS_wit_none hvm) A) (by simp [setLife])
  exact consistentX_left hZ (consistentX_compS hZd hcD' hcm) hvZ

/-- **The typed fold across a Kripke stop, at the floor the borrowed stop chose.** The lender's
stop at `x`, at a floor `f′ ≤ f`, `f ≤ A` the borrowed stop's, owes its continuation at `y`
(`KW.Owed`), and `FoldInv A` held at `x`. Then the lend's world at `y` is owed by the lend's world
at `x` at the floor `f`, at the borrowed share, and `y` keeps `FoldInv A`, so the frame can be
re-entered there. -/
theorem kw_owed_foldAt {x y : KW} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) (hx : x.Θ.FoldInv A) {f f' : Life} (hfA : f ≤ A) (hf' : f' ≤ f)
    {ρk ρp Z W'' ρkL χ : WRes} {v : Val} {hχ : χ.InStratum A} {P : Val → SPropS Loc Val A}
    {hw : P v ⟨χ, hχ⟩} (hZ : ResU.CompS ρk ρp Z) (hZl : Z.get l = some (CellU.mutOf A v χ hχ P hw))
    (hW'' : ResU.CompS χ (ResU.single l (CellU.ownOf v)) W'') (hkL : ResU.CompS (Z.del l) W'' ρkL)
    (hvZ : ResU.Valid Z) (hvkL : ResU.Valid ρkL) (hy : x.Owed f' y ρkL) :
    (x.lend l A F).Owed f (y.lend l A F) ρk ∧ y.Θ.FoldInv A := by
  refine ⟨⟨?_, LocTy.ok_add hy.2.1 l hF, consistentX_fold hZ hZl hW'' hkL hvZ hvkL hy.2.2.1,
    le_rfl, fun g hfg hg => ?_⟩, hy.2.2.2.2 A (le_trans hf' hfA) hx⟩
  · exact (extP_foldFrameAt (le_trans hf' hfA) hx.1 hx.2 F hZ hZl (CellU.at_mutOf _ _ _ _ _ _)
      hkL hy.1).mono hf'
  · obtain ⟨hgA, hg'⟩ := LocTy.FoldInv.of_add hg
    exact LocTy.FoldInv.add (hy.2.2.2.2 g (le_trans hf' hfg) hg') hgA l F

/-- **`FoldTwin` at the typed world.** The lender's entries owe along `KW.Owed` at the lender's
world `x`; the borrowed run's, at the lend's world (`KW.lend`); `FoldInv A` holds at `x`. A
borrowed stop at a floor `f ≤ A` is the lender's stop at `min f x.lo`, and the frame's invariant
is `FoldInv A`. -/
theorem foldTwin_owed {x : KW} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) (hx : x.Θ.FoldInv A) {Ti To : OpTabK KW}
    (hTw : ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, (x.lend l A F).Owed f (z.lend l A F) ρ → en.wk f z ρ) ∧
        (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ))) :
    Ti.FoldTwin (fun y => y.Θ.FoldInv A) A x.lo To l A := by
  intro m i en hTe
  obtain ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, hwk⟩ := hTw m i en hTe
  refine ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, fun ha ρk ρp Z W'' ρkL χ v hχ P hw hZ hZl hW'' hkL hvZ
    hvkL f hf => ⟨min f x.lo, min_le_right _ _, fun y hy => ?_⟩⟩
  obtain ⟨hin, hout⟩ := hwk ha
  obtain ⟨h, hyA⟩ := kw_owed_foldAt hF hx hf (min_le_left _ _) hZ hZl hW'' hkL hvZ hvkL
    (hout _ _ _ hy)
  exact ⟨hin _ _ _ h, hyA⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
