import Core.Chain.RelBase791N

/-!
# The suspending `mut` lend over the chain relation  `[spec §62]`

The frames a `mut` lend needs when its callback's row is `Row.Suspend`: every operation named,
none unrestricted, abortive ones (raises), must-resume ones and cancellable ones all allowed. The
chain relation has the Mut Frame across stops for raises with must-resume stops
(`erwp_M_frameR`, `SI/StopRaiseN.lean`) and for cancellable stops without raises
(`erwp_M_frameT`, `SI/StopCancelN.lean`); here they are one lemma, by the same strong induction
on the index, each case the existing one:

* `erwp_M_frameCR`: the Mut Frame across stops whose table may have abortive, must-resume and
  cancellable entries. At a return, 6.65; at a stop, the borrow folded into the continuation's
  share and lent again at the resume (`erwp_M_frame`'s case); at a cancellable stop the cancel
  obligation is the lender's (`hcan`, `erwp_M_frameT`'s case); at a `raise`, the borrow folded and
  the cell the claim the `raise` carries (`erwp_M_frameR`'s case). The lender's stops are at a
  twin table `T′`, its raises carrying the claim (`opTableR`).

The lender's cancel obligations and the finaliser frame are in `Core/Chain/Cancel791N.lean` and
`Core/Chain/ClaimKW835N.lean`, where each cancel run runs at its own cancel row's table; the
compatibility of `withbor (2)` at a suspending row (`withbor2S_compat`) is in
`Core/Chain/CancelKW835N.lean`. This file also holds the terms and rows the lend's instances read
(`NFv`, `DFv`, `cbRelease`, `unitThunk`, `closingOp`, `hardestRow`); the configurations at
`vN`/`cN` are in `Core/Chain/ConfigsKW835N.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-- **A table whose stops may be taken under a live `mut` lend at `A`, raises and cancellable
stops included**: every non-abortive entry not unrestricted and resumed under `extF`; what passes
out outlives `A`, what passes in holds nothing shorter. -/
structure OpTabN.LendOKCR (T : OpTabN) (A : Life) : Prop where
  entry : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF
  pa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A
  pb : ∀ m i en, T m i = some en → ∀ k ls w (ρ : WRes), en.PB k ls w ρ → ρ.InStratum (↓A)

/-- **Mut Frame at `erwp` across stops: raises, must-resume and cancellable stops.** -/
theorem erwp_M_frameCR {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A) (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
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
      erwp (ℍ := ℍ) Φ (opTableR T' (claimR l A F)) Q n ls e ρ := by
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
  · -- a return: 6.65's end
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
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · -- a stop: the borrow folded into the continuation's share, lent again at the resume
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hq, hwc⟩ := hT.entry m i en hTe ha
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
      have he' : en.wc ls' ls'' ρk := by
        rw [hwc', hwc] at he; rw [hwc]
        exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW''
          hkL he
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
    · have he' : en.wc ls' ls'' ρk := by
        rw [hwc', hwc] at he; rw [hwc]
        exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW''
          hkL he
      have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan m i en en' hTe hTe' ha hql' k ls'' K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hnoρp hZ
        hZd hdZd hPk hW'' hkL ((hcont ls'' he').2 hql')
  · -- a `raise`: the borrow folded, the cell the claim the `raise` carries
    obtain ⟨⟨rfl, hK, hTe, ha⟩, τa, τn, hcan', ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTT' m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc τa τn ρp X).mpr ⟨ρ', hcan', h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc τa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    have hnoZ : NoOwn Z := noOwn_compS hZ hnn hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨X.del l, W'', hY,
        ⟨τa, Z.del l, hD, ⟨hPA' ▸ hPA, hnA⟩, noOwn_del hnoZ l⟩,
        v'', χ, hs, hFk, ResU.CompS.comm hW''⟩⟩)⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

/-! ## Terms and rows of the suspending `mut` lend -/

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC)
open BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791 (rwp_det'')
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (empty_lendOK noOwn_single_mut)
open BoCa.BoLo (Heap Kont ubindE Head)

/-- `rwp_mono` reading the postcondition at the indices the runs leave, `≤ n`. -/
theorem rwp_mono_le {Φ : LocFam} {P Q : PostN} {n : Nat}
    (hPQ : ∀ k, k ≤ n → ∀ ls v ρ, P k ls v ρ → Q k ls v ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwp (ℍ := ℍ) Φ P n ls e ρ) : rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
  obtain ⟨hval, hprog⟩ := h ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun
  refine ⟨fun v hv => ?_, hprog⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := hval v hv
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    hPQ _ (Nat.sub_le n j) _ _ _ h₁₃⟩

/-- A run at the empty table never stops: it is an `rwp` run. -/
theorem rwp_of_erwp_empty {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e ρ) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  rw [erwp_eq] at h
  refine rwp_iff_rwpG.mpr (rwpG_mono (fun k ls t ρ ht => ?_) h)
  rcases ht with ht | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact ht
  · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp; cases hT
  · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp; cases hT

theorem OpTabN.Twin.trans {T₁ T₂ T₃ : OpTabN} (h₁ : T₁.Twin T₂) (h₂ : T₂.Twin T₃) :
    T₁.Twin T₃ := fun m i en h => by
  obtain ⟨en₂, h₂', a1, b1, c1, d1, e1⟩ := h₁ m i en h
  obtain ⟨en₃, h₃', a2, b2, c2, d2, e2⟩ := h₂ m i en₂ h₂'
  exact ⟨en₃, h₃', a2.trans a1, b2.trans b1, c2.trans c1, d2.trans d1, e2.trans e1⟩

/-- `withborU`'s `then`: `λb. (ℓ, b)`. -/
def NFv (l : Loc) : Val := Val.lam (.pair (.val (Val.loc l)) (.var 0))

/-- `withborU`'s `unwind`: `λ_. d ℓ`. -/
def DFv (d : Expr) (l : Loc) : Val := Val.lam (.app d (.val (Val.loc l)))

/-! ### The callback type is inhabited -/

/-- The callback `λ_. λu. ()`: it releases the borrow at once. -/
def cbRelease : Val := Val.lam (.val (Val.lam (.val .unit)))

/-! ### The answer clause: where the frame's stratum premise is not met -/

/-- The thunk `λ_. ()`. -/
def unitThunk : Val := Val.lam (.val .unit)

/-! ### The cancel-row clause admits cleanup that performs -/

/-- A cancellable operation `1 ↠^cancel 1` whose cancel row performs a must-resume operation
`1 ↠^lin 1` (cleanup that closes a resource, say). -/
def closingOp (n i n' i' : UInt32) : OpSig :=
  ⟨n, i, .cancel, .unit, .unit, .eff n' i' .lin .unit .unit (.ret .unit) false (.ret .unit), false⟩

/-- **`Row.Suspend` admits a cancel row with a layer**: the row of `closingOp` suspends, so the
cancel-row clause does not rule out cleanup that performs. -/
theorem suspend_closingOp (x : LifeVar) (bnd : Lifetime.Life) {n i n' i' : UInt32} (hn : n ≠ 0) :
    Row.Suspend [closingOp n i n' i'] x bnd := by
  intro o ho
  simp only [List.mem_singleton] at ho
  subst ho
  refine ⟨by simp [closingOp], hn, id, id, .unit, .unit, fun _ => ?_⟩
  exact ⟨⟨by simp, id, id, .unit, .unit, fun _ => trivial⟩, trivial⟩

/-! ### The hardest case's callback row -/

/-- `park` as the scheduler's table `TJN` types it (`enParkN`, `Core/Chain/PoolSpawnN.lean`):
`1 ↠^cancel 1` at `nP`'s operation `0`, its cancel row pure. -/
def parkSig : OpSig := ⟨BoCa.Fig16.Tree.Wp.SchedProgs.Park.nP, 0, .cancel, .unit, .unit,
  .ret .unit, false⟩

/-- **The row of the hardest case's lend callbacks** (`Core/TreeGoal791.lean` §5, the program
`Core/Chain/Hardest791N.lean` proves): `cbRec` and `cbField` perform `park` (`parkE`) while
holding the record's and the field's borrows, and nothing else. -/
def hardestRow : Row := [parkSig]

/-- **The hardest case's callback row suspends**, at every borrow variable and bound. -/
theorem hardestRow_suspend (x : LifeVar) (bnd : Lifetime.Life) : hardestRow.Suspend x bnd := by
  intro o ho
  simp only [hardestRow, List.mem_singleton] at ho
  subst ho
  exact ⟨by simp [parkSig], by decide, id, id, .unit, .unit, fun _ => trivial⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
