import Core.Chain.Lend791N

/-!
# A suspending lend whose cancel rows perform  `[spec §62]`

A capturable operation's cancel row may have layers: cleanup that performs (closing a file in
the consume glue a raise or cancel runs) stops at them. Under a live `mut` lend the cancel run
then stops while the borrow is live, so the cancel row meets `Row.Suspend`'s clauses
(`CTy.SuspendC`), and the lender's cancel run is the borrowed one with the borrow folded at
every stop, ending at the cancel's `raise` carrying the lend's claim. The lemmas here are the
pieces of that argument that do not read the relation; `CancelKW835N` and `ClaimKW835N` assemble
the suspending lend at `SemJN` from them.

* `errOkN_inStratum`, `errOkN_twin`: a cancel run's error payload is an abortive entry's payload,
  and is one at a twin table.
* `erwp_M_frame_cancelRunCR`: the Mut Frame over a cancel run at a table with abortive,
  must-resume and cancellable entries (`OpTabN.LendOKCR`), its nested cancel obligations
  transferred by a premise (`hcan`, as `erwp_M_frameCR`'s).
* `erwp_of_valid`: a run may assume its resource valid.
* `CTy.LayerOf`, `CTy.cdepth`, `layer_cdepth`, `layer_suspend`, `entN_capB`: a row's layers, how
  deep cancel rows nest, and a suspending row's layers meeting its clauses.
* `claimX`: the claim, consistent with the view.
* `suspendC_effOf`: `Row.Suspend` is `CTy.SuspendC` of the row's computation type.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

/-! ### Error payloads of a cancel run -/

/-- A cancel run's error payload is an abortive entry's payload. -/
theorem errOkN_inStratum {T : OpTabN} {A : Life}
    (hpa : ∀ m i en, T m i = some en → ∀ k ls v (ρ : WRes), en.PA k ls v ρ → ρ.InStratum A) :
    ∀ {k : Nat} {ls : List SRec} {err : Option Val} {ρ : WRes}, errOkN T k ls err ρ →
      ρ.InStratum A
  | _, _, none, _, h => by obtain rfl := h.1; exact ResU.inStratum_empty A
  | _, _, some _, _, h => by
      obtain ⟨_, _, _, en, he⟩ := h
      obtain ⟨⟨-, hTe, -⟩, hPA, -⟩ := pure_sep_iff.mp he
      exact hpa _ _ _ hTe _ _ _ _ hPA

/-- An error payload at a twin. -/
theorem errOkN_twin {T T' : OpTabN} (hTT' : T.Twin T') :
    ∀ {k : Nat} {ls : List SRec} {err : Option Val} {ρ : WRes}, errOkN T k ls err ρ →
      errOkN T' k ls err ρ
  | _, _, none, _, h => h
  | _, _, some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTT' m j en hTe
      exact ⟨m, j, w, en', pure_sep_mk ⟨hE, hTe', hab'.trans ha⟩ ⟨hPA' ▸ hPA, hn⟩⟩

/-! ### The Mut Frame over a cancel run that stops -/

/-- **The Mut Frame over a cancel run whose table has abortive, must-resume and cancellable
entries.** At the cancel's `raise` (with or without an error payload, which outlives `A`) the
borrow is folded and the cell is the claim; at a stop the borrow is folded into the
continuation's share and lent again at the resume (`erwp_M_frameCR`'s case), a cancellable
stop's cancel obligation the lender's by `hcan`. -/
theorem erwp_M_frame_cancelRunCR {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T' : OpTabN} (hT : T.LendOKCR A)
    (hTT' : T.Twin T')
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A)
        (P'' : Val → SPropS Loc Val A) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓A) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (F k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL) :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (cancelTabN T) (fun _ _ _ _ => False) n ls e BM) →
      erwp (ℍ := ℍ) Φ (cancelTabR T' (claimR l A F)) (fun _ _ _ _ => False) n ls e ρ := by
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
    have hρa := errOkN_inStratum hT.pa herr
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc τa τb ρp X).mpr ⟨ρ', hcab, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc τa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    have hnoZ : NoOwn Z := noOwn_compS hZ hnb hnoρp
    obtain ⟨hs, hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
    exact ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inl
      ⟨K, err, pure_sep_mk ⟨rfl, hK⟩ ⟨X.del l, W'', hY,
        ⟨τa, Z.del l, hD, errOkN_twin hTT' herr, noOwn_del hnoZ l⟩,
        v'', χ, hs, hFk, ResU.CompS.comm hW''⟩⟩)⟩
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
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr (Or.inr
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

/-- A run may assume its resource valid: every frame it is run in makes it part of a valid
world. -/
theorem erwp_of_valid {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : ResU.Valid ρ → erwp (ℍ := ℍ) Φ Tb Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp_eq]
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  have h' := h (ResU.Valid.split hc hT.valid).2
  rw [erwp_eq] at h'
  exact h' ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC interp_top_of_defines_empty)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### A row's layers -/

/-- A layer of a row: its qualifier, payload, answer and cancel row. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.LayerOf : CTy → Qual → VTy → VTy → CTy → Prop
  | .eff _ _ q A B fin _ C, q', A', B', fin' =>
      (q' = q ∧ A' = A ∧ B' = B ∧ fin' = fin) ∨ LayerOf C q' A' B' fin'
  | _, _, _, _, _ => False

/-- How deep cancel rows nest. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.cdepth : CTy → Nat
  | .eff _ _ _ _ _ fin _ C => max (cdepth fin + 1) (cdepth C)
  | _ => 0

theorem layer_cdepth : ∀ (F : CTy) {q : Qual} {A B : VTy} {fin : CTy}, F.LayerOf q A B fin →
    fin.cdepth < F.cdepth
  | .eff _ _ _ _ _ fin₀ _ C, q, A, B, fin, h => by
      simp only [CTy.LayerOf] at h
      simp only [CTy.cdepth]
      rcases h with ⟨-, -, -, rfl⟩ | h
      · omega
      · have := layer_cdepth C h; omega
  | .ret _, _, _, _, _, h => h.elim
  | .arr _ _, _, _, _, _, h => h.elim
  | .amp _ _, _, _, _, _, h => h.elim
  | .top, _, _, _, _, h => h.elim
  | .all _ _ _, _, _, _, _, h => h.elim
  | .nuSys _ _ _, _, _, _, _, h => h.elim

/-- A layer of a row meeting `CTy.SuspendC` meets its clauses. -/
theorem layer_suspend {Δ : LifeCtx} {x : LifeVar} {bnd : Lifetime.Life} :
    ∀ (F : CTy), F.SuspendC Δ x bnd →
    ∀ {q : Qual} {A B : VTy} {fin : CTy}, F.LayerOf q A B fin →
    q ≠ .unr ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ VOutlives Δ bnd A ∧
      VOutlives Δ bnd B ∧ (capB q B = true → fin.SuspendC Δ x bnd)
  | .eff _ _ q₀ A₀ B₀ fin₀ _ C, ⟨h, hC⟩, q, A, B, fin, hL => by
      simp only [CTy.LayerOf] at hL
      rcases hL with ⟨rfl, rfl, rfl, rfl⟩ | hL
      · exact h
      · exact layer_suspend C hC hL
  | .ret _, _, _, _, _, _, h => h.elim
  | .arr _ _, _, _, _, _, _, h => h.elim
  | .amp _ _, _, _, _, _, _, h => h.elim
  | .top, _, _, _, _, _, h => h.elim
  | .all _ _ _, _, _, _, _, _, h => h.elim
  | .nuSys _ _ _, _, _, _, _, _, h => h.elim

theorem entN_capB {q : Qual} {B : VTy} {PA PB : Nat → Val → WRes → Prop}
    {fin : Option (Nat → List SRec → Expr → WProp)}
    (ha : (entN q B PA PB fin).abort = false) (hq : (entN q B PA PB fin).q ≠ .lin) :
    capB q B = true := by
  simp only [entN] at ha hq
  simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨hq, ?_⟩
  cases hB : B.isZero
  · rfl
  · simp [hB, hq] at ha

/-! ### The claim with the view's consistency -/

/-- **The claim, consistent with the view.** The finaliser consumes the claim by `d`'s judgment,
whose argument clause reads a view consistent with the argument (`fin_claim`). -/
def claimX (R : Nat → WProp) (c : Loc → Option Life) : Nat → WProp :=
  fun k ρ => R k ρ ∧ ConsistentX c ρ

/-! ### The suspending lend's row -/

/-- `Row.Suspend` is `CTy.SuspendC` of the row's computation type. -/
theorem suspendC_effOf {S : Row} {Δ : LifeCtx} {x : LifeVar} {bnd : Lifetime.Life}
    (hS : S.Suspend Δ x bnd) (R : VTy) : (CTy.effOf S R).SuspendC Δ x bnd := by
  induction S with
  | nil => trivial
  | cons o S ih =>
      obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := hS o (List.mem_cons_self ..)
      exact ⟨⟨h1, h3, h4, h5, h6, h7⟩,
        ih (fun o' ho' => hS o' (List.mem_cons_of_mem _ ho'))⟩

/-- A layer of a row meeting `CTy.AnsC P` has its answer in `P`, and its cancel row meets
`CTy.AnsC P` where it is capturable.  `[spec §62]` -/
theorem layer_ans {P : VTy → Prop} : ∀ (F : CTy), F.AnsC P →
    ∀ {q : Qual} {A B : VTy} {fin : CTy}, F.LayerOf q A B fin →
    P B ∧ (capB q B = true → fin.AnsC P)
  | .eff _ _ q₀ A₀ B₀ fin₀ _ C, ⟨h, hC⟩, q, A, B, fin, hL => by
      simp only [CTy.LayerOf] at hL
      rcases hL with ⟨rfl, rfl, rfl, rfl⟩ | hL
      · exact h
      · exact layer_ans C hC hL
  | .ret _, _, _, _, _, _, h => h.elim
  | .arr _ _, _, _, _, _, _, h => h.elim
  | .amp _ _, _, _, _, _, _, h => h.elim
  | .top, _, _, _, _, _, h => h.elim
  | .all _ _ _, _, _, _, _, _, h => h.elim
  | .nuSys _ _ _, _, _, _, _, _, h => h.elim

/-- `Row.AnsC` is `CTy.AnsC` of the row's computation type.  `[spec §62]` -/
theorem ansC_effOf {P : VTy → Prop} {S : Row} (hS : S.AnsC P) (R : VTy) :
    (CTy.effOf S R).AnsC P := by
  induction S with
  | nil => trivial
  | cons o S ih =>
      exact ⟨hS o (List.mem_cons_self ..), ih (fun o' ho' => hS o' (List.mem_cons_of_mem _ ho'))⟩

/-- `CTy.AnsC` is monotone in the property.  `[spec §62]` -/
theorem ansC_mono {P P' : VTy → Prop} (hP : ∀ B, P B → P' B) : ∀ F : CTy, F.AnsC P → F.AnsC P'
  | .eff _ _ _ _ _ fin _ C, ⟨⟨hB, hfin⟩, hC⟩ =>
      ⟨⟨hP _ hB, fun hcap => ansC_mono hP fin (hfin hcap)⟩, ansC_mono hP C hC⟩
  | .ret _, _ | .arr _ _, _ | .amp _ _, _ | .top, _ | .all _ _ _, _ | .nuSys _ _ _, _ => trivial

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
