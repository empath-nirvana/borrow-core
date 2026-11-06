import Core.Chain.Lend791N

/-!
# A suspending lend whose cancel rows perform  `[spec §62]`

A capturable operation's cancel row may have layers: cleanup that performs (closing a file in
the consume glue a raise or cancel runs) stops at them. Under a live `mut` lend the cancel run
then stops while the borrow is live, so the cancel row meets `Row.Suspend`'s clauses
(`CTy.SuspendC`), and the lender's cancel run is the borrowed one with the borrow folded at
every stop, ending at the cancel's `raise` carrying the lend's claim. Each cancel run runs at its
own cancel row's table.

* `erwp_M_frame_cancelRunCR`: the Mut Frame over a cancel run at a table with abortive,
  must-resume and cancellable entries (`OpTabN.LendOKCR`), its nested cancel obligations
  transferred by a premise (`hcan`, as `erwp_M_frameCR`'s).
* `tabR`/`finR`: a row's table with every capturable entry's cancel obligation the cancel run at
  the cancel row's own table, ending at the claim, recursively: the lender's twin of the
  callback's `tabN`.
* `tabR_can`: the transfer `hcan` asks, by induction on the cancel row.
* `erwp_ubind_cancelRunCR`: the finaliser frame over a cancel run at `cancelTabR (tabR …)`, ending
  at `cancelTabN (tabN …)`: `D` consumes the claim at the cancel's `raise`, with or without an
  error payload; a nested cancel run passes the frame by the same lemma one level down.
* `erwp_ubindClaimRT`: the finaliser frame around a body at `opTableR (tabR …)`.
* `withbor2S_compat`: the suspending lend, its premises those of the rule.
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

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### The lender's twin: every cancel run at its cancel row's table, ending at the claim -/

mutual
/-- **The lender's table of a row's layers**: `tabN`'s entries, every capturable one's cancel
obligation the cancel run at its cancel row's own table (`tabR` of the cancel row) ending at `R`. -/
def tabR (R : Nat → WProp) : CTy → LSub → LocFam → OpTabN
  | .eff m i q A B fin _ C, δ, Φ => extTabN m i
      (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ k v ρ)
        (finR R fin δ Φ))
      (tabR R C δ Φ)
  | _, _, _ => OpTabN.empty
/-- The lender's cancel obligation of a cancel row: `none` at `⊤`; otherwise the cancel run at
the row's `tabR`, ending at `R`. -/
def finR (R : Nat → WProp) : CTy → LSub → LocFam → Option (Nat → List SRec → Expr → WProp)
  | .top, _, _ => none
  | .eff m i q A B fin _ C, δ, Φ => some (cancelOblRN (ℍ := ℍ) Φ (extTabN m i
      (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ k v ρ)
        (finR R fin δ Φ))
      (tabR R C δ Φ)) R)
  | .ret _, _, Φ => some (cancelOblRN (ℍ := ℍ) Φ OpTabN.empty R)
  | .arr _ _, _, Φ => some (cancelOblRN (ℍ := ℍ) Φ OpTabN.empty R)
  | .amp _ _, _, Φ => some (cancelOblRN (ℍ := ℍ) Φ OpTabN.empty R)
  | .all _ _ _, _, Φ => some (cancelOblRN (ℍ := ℍ) Φ OpTabN.empty R)
  | .nu _, _, Φ => some (cancelOblRN (ℍ := ℍ) Φ OpTabN.empty R)
end

theorem finR_eq (R : Nat → WProp) {F : CTy} (hF : F ≠ .top) (δ : LSub) (Φ : LocFam) :
    finR (ℍ := ℍ) R F δ Φ = some (cancelOblRN (ℍ := ℍ) Φ (tabR (ℍ := ℍ) R F δ Φ) R) := by
  cases F <;> simp_all [finR, tabR]

theorem finN_eq {F : CTy} (hF : F ≠ .top) (δ : LSub) (Φ : LocFam) :
    finN (ℍ := ℍ) F δ Φ = some (cancelOblN (ℍ := ℍ) Φ (tabN (ℍ := ℍ) F δ Φ)) := by
  cases F <;> simp_all [finN, tabN]

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
  | .nu _, _, _, _, _, h => h.elim

/-- A layer of a row meeting `CTy.SuspendC` meets its clauses. -/
theorem layer_suspend {x : LifeVar} : ∀ (F : CTy), F.SuspendC x → ∀ {q : Qual} {A B : VTy}
    {fin : CTy}, F.LayerOf q A B fin →
    q ≠ .unr ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ (∀ Δ a, VOutlives Δ a A) ∧ (∀ Δ a, VOutlives Δ a B) ∧
      (capB q B = true → fin.SuspendC x)
  | .eff _ _ q₀ A₀ B₀ fin₀ _ C, ⟨⟨h1, _, h3, h4, h5, h6, h7⟩, hC⟩, q, A, B, fin, h => by
      simp only [CTy.LayerOf] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩ | h
      · exact ⟨h1, h3, h4, h5, h6, h7⟩
      · exact layer_suspend C hC h
  | .ret _, _, _, _, _, _, h => h.elim
  | .arr _ _, _, _, _, _, _, h => h.elim
  | .amp _ _, _, _, _, _, _, h => h.elim
  | .top, _, _, _, _, _, h => h.elim
  | .all _ _ _, _, _, _, _, _, h => h.elim
  | .nu _, _, _, _, _, _, h => h.elim

/-- **An entry of `tabN` is a layer's, and `tabR` has the layer's entry at the same key.** -/
theorem tab_lookupN : ∀ (F : CTy) {δ₁ : LSub} {Φ₁ : LocFam} {m j : UInt32} {en : OpEntN},
    tabN (ℍ := ℍ) F δ₁ Φ₁ m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₁ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ₁ k v ρ)
        (finN (ℍ := ℍ) fin δ₁ Φ₁) ∧
      ∀ (R : Nat → WProp) (δ₂ : LSub) (Φ₂ : LocFam), tabR (ℍ := ℍ) R F δ₂ Φ₂ m j =
        some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) B δ₂ k v ρ) (finR (ℍ := ℍ) R fin δ₂ Φ₂))
  | .eff m₀ i₀ q A B fin rc C, δ₁, Φ₁, m, j, en, h => by
      simp only [tabN] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R δ₂ Φ₂ => by
          simp only [tabR, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupN C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R δ₂ Φ₂ => by
          simp only [tabR, extTabN, if_neg hmj]; exact hR R δ₂ Φ₂⟩
  | .ret _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .top, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h

/-- **An entry of `tabR` is a layer's, and `tabN` has the layer's entry at the same key.** -/
theorem tab_lookupR (R : Nat → WProp) : ∀ (F : CTy) {δ₂ : LSub} {Φ₂ : LocFam} {m j : UInt32}
    {en : OpEntN}, tabR (ℍ := ℍ) R F δ₂ Φ₂ m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ₂ k v ρ)
        (finR (ℍ := ℍ) R fin δ₂ Φ₂) ∧
      ∀ (δ₁ : LSub) (Φ₁ : LocFam), tabN (ℍ := ℍ) F δ₁ Φ₁ m j =
        some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₁ k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) B δ₁ k v ρ) (finN (ℍ := ℍ) fin δ₁ Φ₁))
  | .eff m₀ i₀ q A B fin rc C, δ₂, Φ₂, m, j, en, h => by
      simp only [tabR] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun δ₁ Φ₁ => by
          simp only [tabN, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hN⟩ := tab_lookupR R C h
        exact ⟨q', A', B', fin', .inr hL, he, fun δ₁ Φ₁ => by
          simp only [tabN, extTabN, if_neg hmj]; exact hN δ₁ Φ₁⟩
  | .ret _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .top, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h

/-- **The callback's table and the lender's twin agree but for the cancel obligations**: they
differ in `'x`, which no layer's types mention. -/
theorem tabN_tabR_twin {x : LifeVar} {α : Life} {F : CTy} (hF : F.SuspendC x) (R : Nat → WProp)
    (δ : LSub) (Φ₁ Φ₂ : LocFam) :
    (tabN (ℍ := ℍ) F (δ.extend x α) Φ₁).Twin (tabR (ℍ := ℍ) R F δ Φ₂) := by
  intro m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupN F h
  obtain ⟨-, hA, hB, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R δ Φ₂, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hA δ α]
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hB δ α]

/-- The lender's twin and the table at the same `δ` and `Φ` agree but for the cancel
obligations. -/
theorem tabR_tabN_twin (R : Nat → WProp) (F : CTy) (δ : LSub) (Φ : LocFam) :
    (tabR (ℍ := ℍ) R F δ Φ).Twin (tabN (ℍ := ℍ) F δ Φ) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hN⟩ := tab_lookupR R F h
  exact ⟨_, hN δ Φ, rfl, rfl, rfl, rfl, rfl⟩

/-- **A cancel row meeting `CTy.SuspendC` may be stopped at under the lend at `α`.** -/
theorem tabN_lendOKCR_C {x : LifeVar} {α : Life} {F : CTy} (hF : F.SuspendC x) (δ : LSub)
    (Φ : LocFam) : (tabN (ℍ := ℍ) F (δ.extend x α) Φ).LendOKCR α where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    exact vN_outlives (Δ := LifeCtx.empty) (a := .var x) (models_empty_any _)
      (interp_ext_self δ x α) ((layer_suspend F hF hL).2.2.2.1 _ _) k v ρ hp
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    exact (vN_outlives (Δ := LifeCtx.empty) (a := .var x) (models_empty_any _)
      (interp_ext_self δ x α) ((layer_suspend F hF hL).2.2.2.2.1 _ _) k w ρ hp).mono
      (Life.down_sqsubset α).le

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

/-- **The lender's cancel obligations, from the callback's**, by induction on how deep cancel
rows nest: at a capturable entry, the callback's cancel run at its cancel row's table, framed by
`erwp_M_frame_cancelRunCR` at that table, its own nested cancel obligations by the induction. -/
theorem tabR_can {x : LifeVar} {α : Life} {δ : LSub} {Φ : LocFam} {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x →
    ∀ m i en en', tabN (ℍ := ℍ) F (δ.extend x α) (Φ.set l α Fam) m i = some en →
      tabR (ℍ := ℍ) (claimR l α Fam) F δ Φ m i = some en' → en.abort = false →
      en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρp Z ρkL W'' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum α)
        (P'' : Val → SPropS Loc Val α) (hw'' : P'' v'' ⟨χ, hχ⟩),
        NoOwn ρp → ResU.CompS ρk ρp Z →
        ResU.CompS (Z.del l) (ResU.single l (CellU.mutOf α v'' χ hχ P'' hw'')) Z →
        (Z.del l).InStratum (↓α) →
        (∀ u r, SPropS.toU (P'' u) r → SPropS.toU (Fam k u) r) →
        ResU.CompS χ (ResU.single l (CellU.ownOf v'')) W'' → ResU.CompS (Z.del l) W'' ρkL →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρkL := by
  intro d
  induction d with
  | zero =>
      intro F hd hF m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupN F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF m i en en' h h' ha hql k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw'' hno hZ hZd hdZd
    hPk hW'' hkL hc
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupN F h
  rw [hR] at h'
  cases Option.some.inj h'
  have hcap := entN_capB ha hql
  have hfin := (layer_suspend F hF hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entN, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finR] at hP'
  rw [finR_eq _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hc _ (finN_eq htop _ _)
  refine erwp_M_frame_cancelRunCR hFam (tabN_lendOKCR_C hfin δ _) (tabN_tabR_twin hfin _ δ _ Φ)
    (ih fin hfd hfin) k k le_rfl ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  exact erwp_garbage hZ hno hin

/-- A cancel run's error payload at `tabN`, read at a lower index and any list. -/
theorem errOkN_tabN_le {F : CTy} {δ : LSub} {Φ : LocFam} {k k' : Nat} (hk : k' ≤ k)
    {ls ls' : List SRec} : ∀ {err : Option Val} {ρ : WRes},
    errOkN (tabN (ℍ := ℍ) F δ Φ) k ls err ρ → errOkN (tabN (ℍ := ℍ) F δ Φ) k' ls' err ρ
  | none, _, h => h
  | some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupN F hTe
      exact ⟨m, j, w, _, pure_sep_mk ⟨hE, hTe, ha⟩ ⟨vN_le hk hPA, hn⟩⟩

/-- **The finaliser frame over a cancel run that stops, its cancel runs at their rows' tables.**
Under `ubind (N, D)`, a cancel run at the lender's twin `tabR`, ending at the cancel's `raise`
carrying `R`, is a cancel run at `tabN` ending owning nothing: at the `raise`,
`[finalise-cancel]` runs `cfin (cancel err) (D ())`, `D` consumes `R` beside the error payload,
and `[cfin-ret]` re-raises; at a stop the frame passes into the continuation, and a cancellable
stop's cancel run, at its cancel row's `tabR`, passes the frame by the induction on how deep
cancel rows nest. -/
theorem erwp_ubind_cancelRunCR {Φ : LocFam} (hΦ : Φ.Down) {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    (δ : LSub) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → ∀ n ls x ρ,
      erwp (ℍ := ℍ) Φ (cancelTabR (tabR (ℍ := ℍ) R F δ Φ) R) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN (tabN (ℍ := ℍ) F δ Φ)) (fun _ _ _ _ => False) n ls
        ((ubK N D).plug x) ρ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro F hFd
  have hL := cancelTabR_local (tabR (ℍ := ℍ) R F δ Φ) R
  have hPD := erwpPost_down (cancelTabN_down (tabN_down F δ Φ hΦ)) falsePost_down
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls x ρ h
  rw [erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, hf⟩ | ⟨K', err, hp⟩ | ⟨K₁, m, i, v, en', hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: `[finalise-cancel]`, `D` consumes the claim, `[cfin-ret]`
    obtain ⟨⟨rfl, hK'⟩, y1, y2, hy, hy1, hR⟩ := pure_sep_iff.mp hp
    have hy1' : (errOkN (tabN (ℍ := ℍ) F δ Φ) k ls' err ⋆ fun ρ => NoOwn ρ) y1 := by
      obtain ⟨τa, τb, hcab, herr, hnb⟩ := hy1
      exact ⟨τa, τb, hcab, errOkN_twin (tabR_tabN_twin R F δ Φ) herr, hnb⟩
    refine rwpG_det hΦ (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ N D err K' hK') rfl .hole) ?_
    rw [Kont.plug_hole, ← cfK_plug]
    refine rwpG_bind hΦ (cfK _) ?_
    have hDr := rwpG_frame (fun _ τ => (errOkN (tabN (ℍ := ℍ) F δ Φ) k ls' err ⋆
        fun ρ => NoOwn ρ) τ) (fun _ _ _ _ h => h) (ResU.CompS.comm hy)
      (rwp_iff_rwpG.mp (hD k ls' y2 hR)) hy1'
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, rfl⟩, hσb⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.cfret μ err w) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal err))) :=
      final_opPlug (payloadName_cancelVal err) (by simp [OpFree, Kont.Catches])
    obtain ⟨τa, τb, hcab, herr, hnb⟩ := hσb
    exact rwpG_here hfin (Or.inr (Or.inl ⟨.hole, err, pure_sep_mk ⟨rfl, rfl⟩
      ⟨τa, τb, hcab, errOkN_tabN_le (by omega) herr, hnb⟩⟩))
  · -- a stop passes the frame; a cancellable one's cancel run through the frame
    obtain ⟨⟨rfl, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, hLy, rfl, hN⟩ := tab_lookupR R F hT'
    have hT := hN δ Φ
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨(ubK N D).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hql P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) _ _ _ hc
    · have hcap := entN_capB ha hql
      simp only [entN, hcap, if_true] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finN] at hP
      rw [finN_eq htop] at hP
      cases Option.some.inj hP
      have hin := (hcont ls'' he).2 hql _ (by simp only [entN, hcap, if_true]; exact finR_eq R htop δ Φ)
      show erwp (ℍ := ℍ) Φ (cancelTabN (tabN (ℍ := ℍ) fin δ Φ)) (fun _ _ _ _ => False) k ls''
        (((ubK N D).comp K₁).dead.plug _) ρk
      rw [dead_comp, ubK_dead, Kont.plug_comp]
      have hfd := layer_cdepth F hLy
      exact ihd fin.cdepth (by omega) fin le_rfl k ls'' _ ρk hin

/-- **The finaliser frame around a body at the lender's twin `opTableR (tabR …) R`**: `[then]`
at a return; at a stop the frame passes outward, a cancellable stop's cancel run through
`erwp_ubind_cancelRunCR`; at a `raise`, `[finalise]` runs `D ()`, which consumes the claim. -/
theorem erwp_ubindClaimRT {Φ : LocFam} (hΦ : Φ.Down) {F : CTy} {δ : LSub}
    (hTr : ∀ m i en, tabN (ℍ := ℍ) F δ Φ m i = some en → en.abort = true → m ≠ 0)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → rwp (ℍ := ℍ) Φ (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN (tabN (ℍ := ℍ) F δ Φ)) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableR (tabR (ℍ := ℍ) R F δ Φ) R) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN (tabN (ℍ := ℍ) F δ Φ)) Qout n ls (ubindE (.pair N D) M) ρ := by
  have hL := opTableR_local (tabR (ℍ := ℍ) R F δ Φ) R
  have hTD := tabN_down F δ Φ hΦ
  have hPD := erwpPost_down (opTableN_down hTD) hQout
  have hD' : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ :=
    fun k ls ρ h => rwp_mono (fun _ _ _ _ h => h.2) (hD k ls ρ h)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls M ρ h
  rw [← ubK_plug, erwp_eq]
  refine rwpG_bind hΦ (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en', hp⟩ | ⟨K₁, m, i, v, en', hp⟩
  · -- `[then]`
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det hΦ (hPD _) hstep
      (erwp_unfold_at (opTableN_local _) hk (hN k ls' v σ hv))
  · -- a stop passes the frame; a cancellable one's cancel run through the frame
    obtain ⟨⟨rfl, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, hLy, rfl, hNt⟩ := tab_lookupR R F hT'
    have hT := hNt δ Φ
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, _, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hql P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) _ _ _ hc
    · have hcap := entN_capB ha hql
      simp only [entN, hcap, if_true] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finN] at hP
      rw [finN_eq htop] at hP
      cases Option.some.inj hP
      have hin := (hcont ls'' he).2 hql _
        (by simp only [entN, hcap, if_true]; exact finR_eq R htop δ Φ)
      show erwp (ℍ := ℍ) Φ (cancelTabN (tabN (ℍ := ℍ) fin δ Φ)) (fun _ _ _ _ => False) k ls''
        (((ubK N D).comp K₁).dead.plug _) ρk
      rw [dead_comp, ubK_dead, Kont.plug_comp]
      exact erwp_ubind_cancelRunCR hΦ N D hD' δ fin.cdepth fin le_rfl k ls'' _ ρk hin
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim
    obtain ⟨⟨rfl, hK₁, hT', hab⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, -, rfl, hNt⟩ := tab_lookupR R F hT'
    have hT := hNt δ Φ
    have hm0 := hTr m i _ hT hab
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind hΦ _ ?_
    have hDr := rwpG_frame
      (fun _ τ => ((fun ρ => vN (ℍ := ℍ) A δ k v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
      (fun _ _ _ _ h => h) (ResU.CompS.comm hcσ)
      (rwp_iff_rwpG.mp (hD k ls' ρR hR)) ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ', ⟨w, rfl, rfl, rfl⟩, ⟨τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ'
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, _,
        pure_sep_mk ⟨rfl, rfl, hT, hab⟩ ⟨τa, τn, hcτ, ⟨vN_le (by omega) hPAτ, hnτ⟩, hnn'⟩⟩))

/-! ### The suspending lend -/

/-- A row's table does not read its base. -/
theorem tabN_effOf_base (S : Row) (R₁ R₂ : VTy) (δ : LSub) (Φ : LocFam) :
    tabN (ℍ := ℍ) (CTy.effOf S R₁) δ Φ = tabN (ℍ := ℍ) (CTy.effOf S R₂) δ Φ := by
  induction S with
  | nil => rfl
  | cons o S ih => simp only [CTy.effOf, tabN, ih]

/-- `Row.Suspend` is `CTy.SuspendC` of the row's computation type. -/
theorem suspendC_effOf {S : Row} {x : LifeVar} (hS : S.Suspend x) (R : VTy) :
    (CTy.effOf S R).SuspendC x := by
  induction S with
  | nil => trivial
  | cons o S ih =>
      exact ⟨hS o (List.mem_cons_self ..), ih (fun o' ho' => hS o' (List.mem_cons_of_mem _ ho'))⟩

/-- **`withbor (2)` at a suspending row is a value of `!` its type**: `withborU d`, at
`Ref A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)` with `Σ` a `Row.Suspend x`
row: the rule-level form of a `mut` borrow held across a suspension, cleanup that performs
included.

The source cell `ℓ ↦ own(w₀) ● σ₀` is lent at a lifetime `α` chosen below the bound, `σ₀`'s
stratum and the callback's (`ResU.exists_stratum`), at the family of `A`'s values; the callback
runs at `Φ[ℓ ↦ (α, 𝒱⟦A⟧)]` from the borrow (`erwp_M_frameCR`), its stops folding the borrow into
the continuation's share; its raises end at the lend's claim, and its cancel runs, each at its
cancel row's own table, end there too (`tabR_can`); the finaliser frame
`then b. (ℓ, b) unwind d ℓ` consumes the claim with `d` (`erwp_ubindClaimRT`, `fin_claim`).

Premises, and the rule that supplies each: `hA`, `hB`, `hS`, `hdc` are `withbor2U`'s with
`Row.Suspend` for `Row.Unwind` (`Const791.OK`); `hd` is the fundamental property at `d`'s
derivation, the premise `CDerives Δ Γ d (Ref A ⊸ 1)` read semantically. -/
theorem withbor2S_compat {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row} {d : Expr}
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Suspend x) (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.ref A) .unit))) (δ : LSub)
    (n : Nat) : vN (ℍ := ℍ) (.bang (withbor2UTy x bnd A B S)) δ n (withborUV d) PMap.empty := by
  refine ⟨rfl, fun Φ hΦ ls => ?_⟩
  intro k hk u ρu ρ' hc hu
  obtain rfl := eq_of_compS_empty_left hc
  intro k' hk' f ρf ρ'' hc' hf
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := hu
  rw [cN_effOf]
  set Fo := CTy.effOf S (.tensor (.ref A) B) with hFo
  set T := tabN (ℍ := ℍ) Fo δ Φ with hTdef
  have hTd : T.Down := tabN_down _ δ Φ hΦ
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ k v ρ h
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFv l) (DFv d l)) (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, Expr.loc,
      subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the lend's lifetime: below the bound, the source's content's stratum and the callback's
  obtain ⟨γ, hγ⟩ := (hf Φ hΦ ls).1
  obtain ⟨βP, hβP⟩ := ResU.exists_stratum σ₀
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  set α : Life := ↓(βP ⊓ βf ⊓ γ) with hαdef
  have hαlt : α < βP ⊓ βf ⊓ γ := Life.down_sqsubset _
  have houtP : σ₀.InStratum α := hβP.mono (hαlt.le.trans (inf_le_left.trans inf_le_left))
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ bnd α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  have hwit : vN (ℍ := ℍ) A δ' k w₀ σ₀ := by rw [hAδ]; exact hw₀
  set Fam : Nat → Val → SPropS Loc Val α := fun j u r => vN (ℍ := ℍ) A δ' j u r.1 with hFam
  set Φ' := Φ.set l α Fam with hΦ'
  set Rc := claimR l α Fam with hRc
  have hFS : Fo.SuspendC x := suspendC_effOf hS _
  have hbase : tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Φ' = tabN (ℍ := ℍ) Fo δ' Φ' :=
    tabN_effOf_base S _ _ δ' Φ'
  have hTw : (tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Φ').Twin
      (tabR (ℍ := ℍ) Rc Fo δ Φ) := by
    rw [hbase]; exact tabN_tabR_twin hFS Rc δ Φ' Φ
  have hcan := tabR_can (ℍ := ℍ) (δ := δ) (Φ := Φ) (l := l) (vN_fam_down A δ' α) Fo.cdepth Fo
    le_rfl hFS
  rw [← hbase] at hcan
  have hM := erwp_M_frameCR (Φ := Φ) (l := l) (A := α) (F := Fam) (vN_fam_down A δ' α)
    (tabN_lendOKCR hS _ δ Φ') hTw hcan
    (Q := fun k _ b ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ k (Val.pair (Val.loc l) b) ρ)
    k' k hk' ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ ρ' ρf ρ'' houtP
    houtf (Fam k) (fun _ _ h => h) hwit hcl hc' (fun BM hBM => ?_)
  · refine erwp_ubindClaimRT hΦ (F := Fo) (δ := δ)
      (fun m i en h _ => by obtain ⟨o, ho, rfl, -⟩ := tabN_effOf_some h; exact (hS o ho).2.1)
      (NFv l) (DFv d l) (fun k ls ρ hR => fin_claim hdc hd hAδ hΦ hR) hQo
      (fun k ls b ρ hq => ?_) k' ls _ ρ'' hM
    refine erwp_det hΦ (opTableN_down hTd) hQo
      (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, NFv]
    exact erwp_val (v := Val.pair (Val.loc l) b) hq
  · -- the callback, at `α`, from the borrow
    have h1 := (hf Φ' (LocFam.set_down hΦ (vN_fam_down A δ' α)) ls).2 α hLt
    have h2 := h1 k' le_rfl (Val.loc l) _ BM hBM
      ⟨α, interp_ext_self δ x α, l, w₀, σ₀, houtP, k, hwit, hk', rfl, rfl⟩
    rw [cN_effOf] at h2
    refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN (ℍ := ℍ) A δ k w σ := by rw [← hAδ]; exact hFσ
    have hbB' : vN (ℍ := ℍ) B δ k b ρ' := by rw [← hBδ]; exact hbB
    exact ⟨Val.loc l, b, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩

/-- **`ConstN` for `withbor (2)` at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_w2 (hF : FundamentalN (ℍ := ℍ)) {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} : ConstN (ℍ := ℍ) (.w2 x bnd A B S d) := by
  rintro ⟨-, hA, hB, hS, hdc, hder⟩ δ n
  exact withbor2S_compat hA hB hS hdc (hF _ _ _ _ hder) δ n

/-! ### The cancel-row clause admits cleanup that performs -/

/-- A cancellable operation `1 ↠^cancel 1` whose cancel row performs a must-resume operation
`1 ↠^lin 1` (cleanup that closes a resource, say). -/
def closingOp (n i n' i' : UInt32) : OpSig :=
  ⟨n, i, .cancel, .unit, .unit, .eff n' i' .lin .unit .unit (.ret .unit) false (.ret .unit), false⟩

/-- **`Row.Suspend` admits a cancel row with a layer**: the row of `closingOp` suspends, so the
cancel-row clause does not rule out cleanup that performs. -/
theorem suspend_closingOp (x : LifeVar) {n i n' i' : UInt32} (hn : n ≠ 0) (hn' : n' ≠ 0) :
    Row.Suspend [closingOp n i n' i'] x := by
  intro o ho
  simp only [List.mem_singleton] at ho
  subst ho
  refine ⟨by simp [closingOp], hn, id, id, fun _ _ => .unit, fun _ _ => .unit, fun _ => ?_⟩
  exact ⟨⟨by simp, hn', id, id, fun _ _ => .unit, fun _ _ => .unit, fun _ => trivial⟩, trivial⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
