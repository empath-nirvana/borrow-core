import Core.Chain.SI.MutSemN

/-!
# Unknown 1, the cancel case: a `mut` lend live across a cancellable stop

**Not a transcription.** At a stop of a cancellable operation the continuation owes a cancel
run (`cancelOKN`): the dead continuation `K†[raise cancel]`, ending at the cancel's `raise`
owning nothing (`cancelTabN`). Inside a lend, the borrowed continuation's cancel run ends owning
nothing but the borrow, which is garbage. The lender's, from the folded share, ends holding the
lent cell again: `ℓ ↦ own(w) ● σ`, `σ` the content in the family. A cancel run that owns
nothing cannot carry it, and a lend is not a runtime frame, so nothing on the unwind releases
it. So the lender's cancel run ends at a cancel's `raise` carrying the lend's claim
(`claimR`) beside what owns nothing: `cancelTabR T R` is `cancelTabN T` with the `raise`
carrying `R`. A finaliser frame around the lend that consumes the claim turns it back into an
ordinary cancel run (step 3).

* `erwp_M_frame_cancelRun`: the Mut Frame over a cancel run, from `cancelTabN T1` inside to
  `cancelTabR T1 (claimR ℓ A F)` outside. At the cancel's `raise` the borrow is folded and the
  cell is the claim; at a finaliser's (must-resume) stop, as in `erwp_M_frame`.
* `erwp_M_frameT`: `erwp_M_frame` for a table with cancellable entries, whose conclusion is at a
  twin table `T′` with the cancel obligations of the lender (`hcan`), and `claimT`, the twin
  whose cancellable entries' obligation is the cancel run at `cancelTabR` (`claimT_can`, by the
  cancel-run frame).

Soundness: the lender's cancel run is the borrowed one with the borrow folded at every stop,
exactly as at a stop of `erwp_M_frame`; the claim is the resource 6.65 returns to the lender at a
return, now returned at the cancel's `raise` instead.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-- **The lend's claim**: the cell owned again, its content in the family's member at the
index. -/
def claimR (l : Loc) (A : Life) (F : Nat → Val → SPropS Loc Val A) : Nat → WProp :=
  fun k ρ => ∃ (w : Val) (σ : WRes) (hσ : σ.InStratum A), F k w ⟨σ, hσ⟩ ∧
    ResU.CompS (ResU.single l (CellU.ownOf w)) σ ρ

/-- `cancelTabN` with the cancel's `raise` carrying `R` beside what owns nothing. -/
def cancelTabR (T : OpTabN) (R : Nat → WProp) : TableN := fun k ls t Ψ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (err : Option Val) =>
      ⌜t = K.plug (raiseE (.val (cancelVal err))) ∧ K.Catches 0 = false⌝ ⋆
        ((errOkN T k ls err ⋆ fun ρ => NoOwn ρ) ⋆ R k))
    (performStopN T k ls t Ψ)

theorem cancelTabR_local (T : OpTabN) (R : Nat → WProp) : (cancelTabR T R).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with h | ⟨K, n, i, v, en, h⟩
  · exact Or.inl h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, fun ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont ls' he).2⟩⟩⟩

/-- `emp` holds of `∅`. -/
theorem emp_empty : BoLo.emp (PMap.empty : WRes) := ⟨rfl, trivial⟩

/-- **The Mut Frame over a cancel run.** -/
theorem erwp_M_frame_cancelRun {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T : OpTabN} (hT : T.LendOK A) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabN T) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabR T (claimR l A F)) (fun _ _ _ _ => False) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwp_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, -, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: the borrow folded, the cell is the claim
    obtain ⟨⟨rfl, hK⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    cases err with
    | some E =>
        obtain ⟨m, j', w', en, he⟩ := herr
        obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
        exact absurd ha (by rw [(hT.entry _ _ en hTe).1]; simp)
    | none =>
    obtain rfl : τa = PMap.empty := herr.1
    obtain rfl := eq_of_compS_empty_left hcab
    have hnoX : NoOwn X := noOwn_compS h9 hnb hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, none, pure_sep_mk ⟨rfl, hK⟩ ⟨X.del l, W'', hY,
        ⟨PMap.empty, X.del l, compS_empty_left _, emp_empty, noOwn_del hnoX l⟩,
        v'', χ, hs, hFk, ResU.CompS.comm hW''⟩⟩)⟩
  · -- a finaliser's stop: as in `erwp_M_frame`
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
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
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)⟩
    simp only [erwpC, show k' < n by omega, if_true]
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hdB : ρbB.InStratum (↓A) :=
      inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
    refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
      (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
    have he' : en.wc ls' ls'' ρk := by rw [hwc] at he ⊢; exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL he
    obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
    obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
        ⟨s1, ResU.CompS.comm hs1, hZds1⟩
    obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
    obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
    obtain ⟨Xk, hXk, hXkp⟩ := (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
    have hc := (hcont ls'' he').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkp hnoρp hc

/-! ### The frame across a cancellable stop -/

/-- A table whose stops may be taken under a live `mut` lend at `A`, cancellable entries
included: non-abortive, not unrestricted, resumed under `extF`; what passes out outlives
`A`, what passes in holds nothing shorter. -/
structure OpTabN.LendOKC (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

/-- `T′` has `T`'s entries up to their cancel obligations. -/
def OpTabN.Twin (T T' : OpTabN) : Prop :=
  ∀ m i en, T m i = some en → ∃ en', T' m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc

/-- **Mut Frame at `erwp` across stops, cancellable ones included.** The lender's stops are at
the twin table `T′`, whose cancel obligations the lender meets from the borrowed
continuation's, with the borrow folded (`hcan`). -/
theorem erwp_M_frameT {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKC A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL)
    {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableN T') Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwp_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT' m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
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
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPA, fun hu' => absurd (hq'.symm.trans hu') hq, fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩)⟩
    · simp only [erwpC, show k' < n by omega, if_true]
      rw [hPB'] at hB
      obtain ⟨ρbB, hρbB, hWXB⟩ :=
        (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
      have hdB : ρbB.InStratum (↓A) :=
        inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
      refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
        (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
      have he' : en.wc ls' ls'' ρk := by rw [hwc', hwc] at he; rw [hwc]; exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL he
      obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
        (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
      obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
        (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
          ⟨s1, ResU.CompS.comm hs1, hZds1⟩
      obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
      obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
      obtain ⟨Xk, hXk, hXkp⟩ :=
        (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
      have hc := (hcont ls'' he').1 k' hk' w σB Xk hB hXk
      simp only [erwpC, show k' < n by omega, if_true] at hc
      exact erwp_garbage hXkp hnoρp hc
    · have he' : en.wc ls' ls'' ρk := by rw [hwc', hwc] at he; rw [hwc]; exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL he
      have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan m i en en' hTe hTe' hql' k ls'' K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hnoρp hZ
        hZd hdZd hPk hW'' hkL ((hcont ls'' he').2 hql')
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

/-! ### The twin whose cancel runs end at the claim -/

/-- The cancel run ending at the claim. -/
def cancelOblRN (Φ : LocFam) (T₁ : OpTabN) (R : Nat → WProp) :
    Nat → List SRec → Expr → WProp :=
  fun k ls e => erwp (ℍ := ℍ) Φ (cancelTabR T₁ R) (fun _ _ _ _ => False) k ls e

/-- `T` with every cancellable entry's obligation replaced by the cancel run at
`cancelTabR T₁ R`. -/
def OpTabN.claimT (T : OpTabN) (Φ : LocFam) (T₁ : OpTabN) (R : Nat → WProp) : OpTabN :=
  fun m i => (T m i).map fun en =>
    if en.q = .cancel then
      OpEntN.mk en.q en.abort en.PA en.PB (some (@cancelOblRN ℍ _ Φ T₁ R)) en.wc
    else en

theorem claimT_twin (T : OpTabN) (Φ : LocFam) (T₁ : OpTabN) (R : Nat → WProp) :
    T.Twin (@OpTabN.claimT ℍ _ T Φ T₁ R) := by
  intro m i en h
  refine ⟨if en.q = .cancel then
      OpEntN.mk en.q en.abort en.PA en.PB (some (@cancelOblRN ℍ _ Φ T₁ R)) en.wc else en,
    by simp [OpTabN.claimT, h], ?_⟩
  by_cases hq : en.q = .cancel <;> simp [hq]

/-- **The lender's cancel obligations at `claimT`**: the borrowed continuation's cancel run, at
`cancelOblN Φ T₁` (read at `Φ[ℓ ↦ (A, F)]` by `erwp_extΦ`, with the garbage added), framed by
`erwp_M_frame_cancelRun`. `Φ ℓ = none`: the lender owns `ℓ`. -/
theorem claimT_can {Φ : LocFam} {l : Loc} (hΦl : Φ l = none) {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T₁ : OpTabN}
    (hT₁ : T₁.LendOK A)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel → en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    (hq : ∀ m i en, T m i = some en → en.q ≠ .unr) :
    ∀ m i en en', T m i = some en → @OpTabN.claimT ℍ _ T Φ T₁ (claimR l A F) m i = some en' →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL := by
  intro m i en en' hT hT' hql k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hno hZ hZd hdZd hPk hW''
    hkL hc
  have hqc : en.q = .cancel := by
    have := hq m i en hT
    cases h : en.q <;> simp_all
  simp only [OpTabN.claimT, hT, Option.map_some, hqc, if_true, Option.some.injEq] at hT'
  subst hT'
  intro P' hP'
  simp only [Option.some.injEq] at hP'
  subst hP'
  have hin := hc _ (hfin m i en hT hqc)
  refine erwp_M_frame_cancelRun hF hT₁ k k le_rfl ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk
    hw'' (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  exact erwp_extΦ (LocFam.ext_set hΦl A F) (LocFam.immLe_set Φ l A F) (cancelTabN_local T₁) _ _ _ _
    (erwp_garbage hZ hno hin)

/-- **Mut Frame at `erwp` across stops, cancellable stops included**: the lender's stops are at
`claimT`, whose cancel runs end carrying the lend's claim. -/
theorem erwp_M_frameC {Φ : LocFam} {l : Loc} (hΦl : Φ l = none) {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T₁ : OpTabN} (hT : T.LendOKC A)
    (hT₁ : T₁.LendOK A)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁)) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableN (@OpTabN.claimT ℍ _ T Φ T₁ (claimR l A F))) Q n ls e ρ :=
  erwp_M_frameT hF hT (claimT_twin T Φ T₁ _)
    (claimT_can hΦl hF hT₁ hfin (fun m i en h => (hT.entry m i en h).2.1))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
