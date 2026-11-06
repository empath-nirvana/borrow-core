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

/-- A run may assume its resource valid: every frame it is run in makes it part of a valid
world. -/
theorem erwp_of_valid {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : ResU.Valid ρ → erwp (ℍ := ℍ) Φ Tb Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp_eq]
  intro ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun hfin
  have h' := h (ResU.Valid.split hc hT.valid).2
  rw [erwp_eq] at h'
  exact h' ρf fρ ps μ hf hc hT htg hl hfd j μ' e' hj hrun hfin

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
/-- **The lender's table of a row's layers**, at the world `Θ` and the view `c`: `tabN`'s entries,
every capturable one's cancel obligation the cancel run at its cancel row's own table (`tabR` of
the cancel row) ending at `R`. -/
def tabR (R : Nat → WProp) : CTy → LSub → LocTy → (Loc → Option Life) → OpTabN
  | .eff m i q A B fin _ C, δ, Θ, c => extTabN m i
      (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)
        (finR R fin δ Θ c))
      (tabR R C δ Θ c)
  | _, _, _, _ => OpTabN.empty
/-- The lender's cancel obligation of a cancel row: `none` at `⊤`; otherwise the cancel run at
the view and the row's `tabR`, ending at `R`. -/
def finR (R : Nat → WProp) : CTy → LSub → LocTy → (Loc → Option Life) →
    Option (Nat → List SRec → Expr → WProp)
  | .top, _, _, _ => none
  | .eff m i q A B fin _ C, δ, Θ, c => some (cancelOblRN (ℍ := ℍ) (Θ.view c) (extTabN m i
      (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ)
        (finR R fin δ Θ c))
      (tabR R C δ Θ c)) R)
  | .ret _, _, Θ, c => some (cancelOblRN (ℍ := ℍ) (Θ.view c) OpTabN.empty R)
  | .arr _ _, _, Θ, c => some (cancelOblRN (ℍ := ℍ) (Θ.view c) OpTabN.empty R)
  | .amp _ _, _, Θ, c => some (cancelOblRN (ℍ := ℍ) (Θ.view c) OpTabN.empty R)
  | .all _ _ _, _, Θ, c => some (cancelOblRN (ℍ := ℍ) (Θ.view c) OpTabN.empty R)
  | .nu _, _, Θ, c => some (cancelOblRN (ℍ := ℍ) (Θ.view c) OpTabN.empty R)
end

theorem finR_eq (R : Nat → WProp) {F : CTy} (hF : F ≠ .top) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) :
    finR (ℍ := ℍ) R F δ Θ c = some (cancelOblRN (ℍ := ℍ) (Θ.view c) (tabR (ℍ := ℍ) R F δ Θ c) R) := by
  cases F <;> simp_all [finR, tabR]

theorem finN_eq {F : CTy} (hF : F ≠ .top) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    finN (ℍ := ℍ) F δ Θ c = some (cancelOblN (ℍ := ℍ) (Θ.view c) (tabN (ℍ := ℍ) F δ Θ c)) := by
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
theorem layer_suspend {x : LifeVar} {bnd : Lifetime.Life} : ∀ (F : CTy), F.SuspendC x bnd →
    ∀ {q : Qual} {A B : VTy} {fin : CTy}, F.LayerOf q A B fin →
    q ≠ .unr ∧ ¬ VFree x A ∧ ¬ VFree x B ∧ VOutlives LifeCtx.empty bnd A ∧
      VOutlives LifeCtx.empty bnd B ∧ B.exclMutFree = true ∧ (capB q B = true → fin.SuspendC x bnd)
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
  | .nu _, _, _, _, _, _, h => h.elim

/-- **An entry of `tabN` is a layer's, and every `tabR` has the layer's entry at the same key.** -/
theorem tab_lookupN : ∀ (F : CTy) {δ₁ : LSub} {Θ₁ : LocTy} {c₁ : Loc → Option Life}
    {m j : UInt32} {en : OpEntN},
    tabN (ℍ := ℍ) F δ₁ Θ₁ c₁ m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₁ Θ₁ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) B δ₁ Θ₁ k v ρ) (finN (ℍ := ℍ) fin δ₁ Θ₁ c₁) ∧
      ∀ (R : Nat → WProp) (δ₂ : LSub) (Θ₂ : LocTy) (c₂ : Loc → Option Life),
        tabR (ℍ := ℍ) R F δ₂ Θ₂ c₂ m j =
          some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ Θ₂ k v ρ)
            (fun k v ρ => vN (ℍ := ℍ) B δ₂ Θ₂ k v ρ) (finR (ℍ := ℍ) R fin δ₂ Θ₂ c₂))
  | .eff m₀ i₀ q A B fin rc C, δ₁, Θ₁, c₁, m, j, en, h => by
      simp only [tabN] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R δ₂ Θ₂ c₂ => by
          simp only [tabR, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupN C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R δ₂ Θ₂ c₂ => by
          simp only [tabR, extTabN, if_neg hmj]; exact hR R δ₂ Θ₂ c₂⟩
  | .ret _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .top, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, _, h => by simp [tabN, OpTabN.empty] at h

/-- **An entry of `tabR` is a layer's; `tabN` and `tabR` at every claim have the layer's entry at
the same key.** -/
theorem tab_lookupR (R : Nat → WProp) : ∀ (F : CTy) {δ₂ : LSub} {Θ₂ : LocTy}
    {c₂ : Loc → Option Life} {m j : UInt32} {en : OpEntN},
    tabR (ℍ := ℍ) R F δ₂ Θ₂ c₂ m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ Θ₂ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) B δ₂ Θ₂ k v ρ) (finR (ℍ := ℍ) R fin δ₂ Θ₂ c₂) ∧
      (∀ (δ₁ : LSub) (Θ₁ : LocTy) (c₁ : Loc → Option Life), tabN (ℍ := ℍ) F δ₁ Θ₁ c₁ m j =
        some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₁ Θ₁ k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) B δ₁ Θ₁ k v ρ) (finN (ℍ := ℍ) fin δ₁ Θ₁ c₁))) ∧
      ∀ R' : Nat → WProp, tabR (ℍ := ℍ) R' F δ₂ Θ₂ c₂ m j =
        some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ₂ Θ₂ k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) B δ₂ Θ₂ k v ρ) (finR (ℍ := ℍ) R' fin δ₂ Θ₂ c₂))
  | .eff m₀ i₀ q A B fin rc C, δ₂, Θ₂, c₂, m, j, en, h => by
      simp only [tabR] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun δ₁ Θ₁ c₁ => by
          simp only [tabN, extTabN, if_pos hmj], fun R' => by
          simp only [tabR, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hN, hR'⟩ := tab_lookupR R C h
        exact ⟨q', A', B', fin', .inr hL, he, fun δ₁ Θ₁ c₁ => by
          simp only [tabN, extTabN, if_neg hmj]; exact hN δ₁ Θ₁ c₁, fun R' => by
          simp only [tabR, extTabN, if_neg hmj]; exact hR' R'⟩
  | .ret _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .top, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, _, h => by simp [tabR, OpTabN.empty] at h

/-- **The callback's table and the lender's twin agree but for the cancel obligations**: they
differ in `'x`, which no layer's types mention, and in the world, which the layers' types,
outliving the bound, read alike (`hΘ`, `vN_add_eq_bnd` at a lend below the bound). -/
theorem tabN_tabR_twin {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {F : CTy}
    (hF : F.SuspendC x bnd) (R : Nat → WProp)
    (δ : LSub) (Θ₁ Θ₂ : LocTy) (c₁ c₂ : Loc → Option Life)
    (hΘ : ∀ A : VTy, VOutlives LifeCtx.empty bnd A → vN (ℍ := ℍ) A δ Θ₁ = vN (ℍ := ℍ) A δ Θ₂) :
    (tabN (ℍ := ℍ) F (δ.extend x α) Θ₁ c₁).Twin (tabR (ℍ := ℍ) R F δ Θ₂ c₂) := by
  intro m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupN F h
  obtain ⟨-, hA, hB, hOA, hOB, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R δ Θ₂ c₂, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hA δ α, hΘ A hOA]
  · simp only [entN, vN_extend_of_not_free (ℍ := ℍ) hB δ α, hΘ B hOB]

/-- The lender's twin and the table at the same world and view agree but for the cancel
obligations. -/
theorem tabR_tabN_twin (R : Nat → WProp) (F : CTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) : (tabR (ℍ := ℍ) R F δ Θ c).Twin (tabN (ℍ := ℍ) F δ Θ c) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hN, -⟩ := tab_lookupR R F h
  exact ⟨_, hN δ Θ c, rfl, rfl, rfl, rfl, rfl⟩

/-- The lender's twins at two claims agree but for the cancel obligations. -/
theorem tabR_tabR_twin (R R' : Nat → WProp) (F : CTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) : (tabR (ℍ := ℍ) R F δ Θ c).Twin (tabR (ℍ := ℍ) R' F δ Θ c) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, -, hR'⟩ := tab_lookupR R F h
  exact ⟨_, hR' R', rfl, rfl, rfl, rfl, rfl⟩

/-- **A cancel row meeting `CTy.SuspendC` may be stopped at under a lend at `α ⊏ @bnd`.** -/
theorem tabN_lendOKCR_C {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {F : CTy}
    (hF : F.SuspendC x bnd) (δ : LSub) (hLt : LtLife δ bnd α)
    (Θ : LocTy) (c : Loc → Option Life) : (tabN (ℍ := ℍ) F (δ.extend x α) Θ c).LendOKCR α where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    obtain ⟨-, hA, -, hOA, -⟩ := layer_suspend F hF hL
    have hp' : vN (ℍ := ℍ) A (δ.extend x α) Θ k v ρ := hp
    rw [vN_extend_of_not_free hA] at hp'
    exact vN_inStratum_bnd hOA hLt hp'
  pb := fun m i en h k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupN F h
    obtain ⟨-, -, hB, -, hOB, -⟩ := layer_suspend F hF hL
    have hp' : vN (ℍ := ℍ) B (δ.extend x α) Θ k w ρ := hp
    rw [vN_extend_of_not_free hB] at hp'
    exact (vN_inStratum_bnd hOB hLt hp').mono (Life.down_sqsubset α).le

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
rows nest. The callback's table is at the world with the lend at a fresh `α` and the view moved
there; the lender's at the world and view without it. At a capturable entry, the callback's
cancel run at its cancel row's table, framed by `erwp_M_frame_cancelRunCR` at that table (the
callback's view is the relation's `Φ.set`, `LocTy.view_add`), its own nested cancel obligations by
the induction. -/
theorem tabR_can {x : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub} {Θ : LocTy}
    (hf : Θ.Fresh α) (hLt : LtLife δ bnd α) {c : Loc → Option Life} {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
    ∀ m i en en', tabN (ℍ := ℍ) F (δ.extend x α) (Θ.add l α Fam) (setLife c l α) m i = some en →
      tabR (ℍ := ℍ) (claimR l α Fam) F δ Θ c m i = some en' → en.abort = false →
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
  have hfin := (layer_suspend F hF hL).2.2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entN, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finR] at hP'
  rw [finR_eq _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hc _ (finN_eq htop _ _ _)
  refine erwp_M_frame_cancelRunCR (Φ := Θ.view c) hFam
    (tabN_lendOKCR_C hfin δ hLt (Θ.add l α Fam) (setLife c l α))
    (tabN_tabR_twin hfin _ δ (Θ.add l α Fam) Θ (setLife c l α) c
      (fun A' hO => vN_add_eq_bnd hO δ hLt hf l Fam))
    (ih fin hfd hfin) k k le_rfl ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  rw [← LocTy.view_add]
  exact erwp_garbage hZ hno hin

/-- A cancel run's error payload at `tabN`, read at a lower index and any list. -/
theorem errOkN_tabN_le {F : CTy} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {k k' : Nat}
    (hk : k' ≤ k) {ls ls' : List SRec} : ∀ {err : Option Val} {ρ : WRes},
    errOkN (tabN (ℍ := ℍ) F δ Θ c) k ls err ρ → errOkN (tabN (ℍ := ℍ) F δ Θ c) k' ls' err ρ
  | none, _, h => h
  | some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupN F hTe
      exact ⟨m, j, w, _, pure_sep_mk ⟨hE, hTe, ha⟩ ⟨vN_le hk hPA, hn⟩⟩

/-! ### The claim with the view's consistency -/

/-- **The claim, consistent with the view.** The finaliser consumes the claim by `d`'s judgment,
whose argument clause reads a view consistent with the argument (`fin_claim`). -/
def claimX (R : Nat → WProp) (c : Loc → Option Life) : Nat → WProp :=
  fun k ρ => R k ρ ∧ ConsistentX c ρ

/-- **A cancel run at the lender's twin carries the view's consistency to its claim.** A run from
a resource consistent with `c` returns consistent resources (`rwpG_consistentXV`), so the claim a
`raise` carries is consistent; a stop's continuation is resumed from its share, consistent, and
an answer, whose type holds no `mut` cell on the exclusive walk (`CTy.SuspendC`), is consistent
with every view (`consistentX_of_exclMutFree`); a cancellable stop's cancel run is one at its cancel row's table, by the
induction on how deep cancel rows nest. -/
theorem erwp_cancelRun_claimX {x : LifeVar} {bnd : Lifetime.Life} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {R : Nat → WProp} :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
    ∀ n ls e ρ, ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabR (tabR (ℍ := ℍ) R F δ Θ c) R) (fun _ _ _ _ => False)
        n ls e ρ →
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabR (tabR (ℍ := ℍ) (claimX R c) F δ Θ c) (claimX R c))
        (fun _ _ _ _ => False) n ls e ρ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro F hFd hF n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ hc h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with ⟨_, _, hf⟩ | ⟨K', err, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: the claim is part of a consistent resource
    obtain ⟨hpure, y1, y2, hy, hy1, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨τa, τb, hcab, herr, hnb⟩ := hy1
    exact Or.inr (Or.inl ⟨K', err, pure_sep_mk hpure ⟨y1, y2, hy,
      ⟨τa, τb, hcab, errOkN_twin (tabR_tabR_twin R _ F δ Θ c) herr, hnb⟩, hR,
      consistentX_right hy hcσ hvσ⟩⟩)
  · -- a stop: its share is consistent, and so is every answer
    obtain ⟨⟨hpt, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, hLy, rfl, -, hR₂⟩ := tab_lookupR R F hT'
    have hck : ConsistentX c ρk := consistentX_right hcak hcσ hvσ
    obtain ⟨-, -, -, -, -, hMF, hfinS⟩ := layer_suspend F hF hLy
    refine Or.inr (Or.inr ⟨K₁, m, i, v, _, pure_sep_mk ⟨hpt, hK₁, hR₂ (claimX R c), ha⟩
      ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
        fun hql P hP => ?_⟩⟩⟩)
    · have hc' := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) _ _ _
        (consistentX_compS hcτ hck (consistentX_of_exclMutFree B hMF δ Θ k' w τ₁ hB c)) hc'
    · have hcap := entN_capB ha hql
      have hfS := hfinS hcap
      simp only [entN, hcap, if_true] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finR] at hP
      rw [finR_eq _ htop] at hP
      cases Option.some.inj hP
      have hin := (hcont ls'' he).2 hql _
        (by simp only [entN, hcap, if_true]; exact finR_eq R htop δ Θ c)
      have hfd := layer_cdepth F hLy
      exact ihd fin.cdepth (by omega) fin le_rfl hfS k ls'' _ ρk hck hin

/-- **A body at the lender's twin carries the view's consistency to its claim**: as
`erwp_cancelRun_claimX`, at a `raise` the claim beside the payload. -/
theorem erwp_claimX {x : LifeVar} {bnd : Lifetime.Life} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {R : Nat → WProp} {F : CTy} (hF : F.SuspendC x bnd) {Q : PostN} :
    ∀ n ls e ρ, ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR (tabR (ℍ := ℍ) R F δ Θ c) R) Q n ls e ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR (tabR (ℍ := ℍ) (claimX R c) F δ Θ c) (claimX R c)) Q
        n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ hc h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with hv | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact Or.inl hv
  · -- a stop: its share is consistent, and so is every answer
    obtain ⟨⟨hpt, hK₁, hT', ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, hLy, rfl, -, hR₂⟩ := tab_lookupR R F hT'
    have hck : ConsistentX c ρk := consistentX_right hcak hcσ hvσ
    obtain ⟨-, -, -, -, -, hMF, hfinS⟩ := layer_suspend F hF hLy
    refine Or.inr (Or.inl ⟨K₁, m, i, v, _, pure_sep_mk ⟨hpt, hK₁, hR₂ (claimX R c), ha⟩
      ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
        fun hql P hP => ?_⟩⟩⟩)
    · have hc' := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) _ _ _
        (consistentX_compS hcτ hck (consistentX_of_exclMutFree B hMF δ Θ k' w τ₁ hB c)) hc'
    · have hcap := entN_capB ha hql
      have hfS := hfinS hcap
      simp only [entN, hcap, if_true] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finR] at hP
      rw [finR_eq _ htop] at hP
      cases Option.some.inj hP
      have hin := (hcont ls'' he).2 hql _
        (by simp only [entN, hcap, if_true]; exact finR_eq R htop δ Θ c)
      exact erwp_cancelRun_claimX fin.cdepth fin le_rfl hfS k ls'' _ ρk hck hin
  · -- a `raise`: the claim is part of a consistent resource
    obtain ⟨⟨hpt, hK₁, hT', hab⟩, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, -, rfl, -, hR₂⟩ := tab_lookupR R F hT'
    exact Or.inr (Or.inr ⟨K₁, m, i, v, _, pure_sep_mk ⟨hpt, hK₁, hR₂ (claimX R c), hab⟩
      ⟨σ₁, ρR, hcσR, hpa, hR, consistentX_right hcσR hcσ hvσ⟩⟩)

/-! ### The finaliser frame at the view -/

/-- **The finaliser frame over a cancel run that stops, its cancel runs at their rows' tables.**
Under `ubind (N, D)`, a cancel run at the lender's twin `tabR`, ending at the cancel's `raise`
carrying `R`, is a cancel run at `tabN` ending owning nothing: at the `raise`,
`[finalise-cancel]` runs `cfin (cancel err) (D ())`, `D` consumes `R` beside the error payload,
and `[cfin-ret]` re-raises; at a stop the frame passes into the continuation, and a cancellable
stop's cancel run, at its cancel row's `tabR`, passes the frame by the induction on how deep
cancel rows nest. -/
theorem erwp_ubind_cancelRunCR {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life}
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) (Θ.view c) (fun _ _ _ ρ' => ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ)
    (δ : LSub) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → ∀ n ls x ρ,
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabR (tabR (ℍ := ℍ) R F δ Θ c) R) (fun _ _ _ _ => False)
        n ls x ρ →
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabN (tabN (ℍ := ℍ) F δ Θ c)) (fun _ _ _ _ => False) n ls
        ((ubK N D).plug x) ρ := by
  have hΦ := LocTy.view_down hΘ c
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro F hFd
  have hL := cancelTabR_local (tabR (ℍ := ℍ) R F δ Θ c) R
  have hPD := erwpPost_down (cancelTabN_down (tabN_down F δ Θ hΘ c)) falsePost_down
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
    have hy1' : (errOkN (tabN (ℍ := ℍ) F δ Θ c) k ls' err ⋆ fun ρ => NoOwn ρ) y1 := by
      obtain ⟨τa, τb, hcab, herr, hnb⟩ := hy1
      exact ⟨τa, τb, hcab, errOkN_twin (tabR_tabN_twin R F δ Θ c) herr, hnb⟩
    refine rwpG_det hΦ (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ N D err K' hK') rfl .hole) ?_
    rw [Kont.plug_hole, ← cfK_plug]
    refine rwpG_bind hΦ (cfK _) ?_
    have hDr := rwpG_frame (fun _ τ => (errOkN (tabN (ℍ := ℍ) F δ Θ c) k ls' err ⋆
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
    obtain ⟨q, A, B, fin, hLy, rfl, hN, -⟩ := tab_lookupR R F hT'
    have hT := hN δ Θ c
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
      have hin := (hcont ls'' he).2 hql _
        (by simp only [entN, hcap, if_true]; exact finR_eq R htop δ Θ c)
      show erwp (ℍ := ℍ) (Θ.view c) (cancelTabN (tabN (ℍ := ℍ) fin δ Θ c)) (fun _ _ _ _ => False)
        k ls'' (((ubK N D).comp K₁).dead.plug _) ρk
      rw [dead_comp, ubK_dead, Kont.plug_comp]
      have hfd := layer_cdepth F hLy
      exact ihd fin.cdepth (by omega) fin le_rfl k ls'' _ ρk hin

/-- **The finaliser frame around a body at the lender's twin `opTableR (tabR …) R`**: `[then]`
at a return; at a stop the frame passes outward, a cancellable stop's cancel run through
`erwp_ubind_cancelRunCR`; at a `raise`, `[finalise]` runs `D ()`, which consumes the claim. -/
theorem erwp_ubindClaimRT {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life} {F : CTy}
    {δ : LSub}
    (hTr : ∀ m i en, tabN (ℍ := ℍ) F δ Θ c m i = some en → en.abort = true → m ≠ 0)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → rwp (ℍ := ℍ) (Θ.view c)
      (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) F δ Θ c)) Qout k ls
        (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) (Θ.view c) (opTableR (tabR (ℍ := ℍ) R F δ Θ c) R) Qin n ls M ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) F δ Θ c)) Qout n ls
        (ubindE (.pair N D) M) ρ := by
  have hΦ := LocTy.view_down hΘ c
  have hL := opTableR_local (tabR (ℍ := ℍ) R F δ Θ c) R
  have hTD := tabN_down F δ Θ hΘ c
  have hPD := erwpPost_down (opTableN_down hTD) hQout
  have hD' : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) (Θ.view c) (fun _ _ _ ρ' => ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ :=
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
    obtain ⟨q, A, B, fin, hLy, rfl, hNt, -⟩ := tab_lookupR R F hT'
    have hT := hNt δ Θ c
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
        (by simp only [entN, hcap, if_true]; exact finR_eq R htop δ Θ c)
      show erwp (ℍ := ℍ) (Θ.view c) (cancelTabN (tabN (ℍ := ℍ) fin δ Θ c)) (fun _ _ _ _ => False)
        k ls'' (((ubK N D).comp K₁).dead.plug _) ρk
      rw [dead_comp, ubK_dead, Kont.plug_comp]
      exact erwp_ubind_cancelRunCR hΘ N D hD' δ fin.cdepth fin le_rfl k ls'' _ ρk hin
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim
    obtain ⟨⟨rfl, hK₁, hT', hab⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨q, A, B, fin, -, rfl, hNt, -⟩ := tab_lookupR R F hT'
    have hT := hNt δ Θ c
    have hm0 := hTr m i _ hT hab
    refine rwpG_det hΦ (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind hΦ _ ?_
    have hDr := rwpG_frame
      (fun _ τ => ((fun ρ => vN (ℍ := ℍ) A δ Θ k v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
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
theorem tabN_effOf_base (S : Row) (R₁ R₂ : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    tabN (ℍ := ℍ) (CTy.effOf S R₁) δ Θ c = tabN (ℍ := ℍ) (CTy.effOf S R₂) δ Θ c := by
  induction S with
  | nil => rfl
  | cons o S ih => simp only [CTy.effOf, tabN, ih]

/-- `Row.Suspend` is `CTy.SuspendC` of the row's computation type. -/
theorem suspendC_effOf {S : Row} {x : LifeVar} {bnd : Lifetime.Life} (hS : S.Suspend x bnd)
    (R : VTy) : (CTy.effOf S R).SuspendC x bnd := by
  induction S with
  | nil => trivial
  | cons o S ih =>
      obtain ⟨h1, -, h3, h4, h5, h6, h7, h8⟩ := hS o (List.mem_cons_self ..)
      exact ⟨⟨h1, h3, h4, h5, h6, h7, h8⟩,
        ih (fun o' ho' => hS o' (List.mem_cons_of_mem _ ho'))⟩

/-- **`withbor (2)` at a suspending row is a value of `!` its type**: `withborU d`, at
`Ref A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Ref A ⊗ B)` with `Σ` a `Row.Suspend x bnd`
row: the rule-level form of a `mut` borrow held across a suspension, cleanup that performs
included.

At the world `Θ` and view `c` the source cell `ℓ ↦ own(w₀) ● σ₀` is lent at a lifetime `α` fresh
for `Θ` (`LocTy.exists_fresh`) and below the bound, the side condition's `@bδ` and the callback's
stratum: by `[TR]` 6.60 at `⊢ A ⊒ @b` every value of `A` is in `Res_α` (`vN_outlivesLe`), the
borrow's uniform conjunct and the content's stratum (Core's `withbor2U_compatX`); the
callback runs at the world `Θ + (ℓ, α) ↦ famL α 𝒱⟦A⟧ Θ` and the view moved to `α` at `ℓ`, which is
the relation's `Φ[ℓ ↦ (α, …)]` (`LocTy.view_add`), from the borrow (`lend_mutL`), consistent
(`consistentX_compS`); its stops fold the borrow into the continuation's share
(`erwp_M_frameCR`), its table the lender's twin at `Θ` (`tabN_tabR_twin`, the row's types
outliving the bound, `vN_add_eq_bnd`); its raises end at the lend's claim, and its cancel runs,
each at its cancel row's own table, end there too (`tabR_can`); the claim is consistent with `c`
(`erwp_claimX`); the finaliser frame `then b. (ℓ, b) unwind d ℓ` consumes it with `d`
(`erwp_ubindClaimRT`, `fin_claim`). The callback's result `['x] B` returns to the world without
the lend by `vN_local`.

Premises, and the rule that supplies each: `hbnd` is the bound's definedness, which Core's rule
gets from its bound `Δ.meetOfDom` (`Const791.OK`); `hO`, `hA`, `hB`, `hS`, `hdc` are `withbor2U`'s with
`Row.Suspend` for `Row.Unwind` (`Const791.OK`); `hd` is the fundamental property at `d`'s
derivation, the premise `CDerives Δ Γ d (Ref A ⊸ 1)` read semantically. -/
theorem withbor2S_compat {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row} {d : Expr}
    (hbnd : LifeCtx.empty.Defines bnd) (hO : ∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b A)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Suspend x bnd) (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.ref A) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withbor2UTy x bnd A B S)) δ Θ₀ n (withborUV d) PMap.empty := by
  refine ⟨rfl, fun Θ₁ _ _ c₁ _ ls => ?_⟩
  intro Θ₂ _ _ c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro Θ hE₃ hΘ c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, w₀, σ₀, rfl, hcl, hw₀⟩ := vN_le hk' (vN_extR _ δ k u ρu hE₃ hu)
  rw [cN_effOf]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.ref A) B) with hFo
  set T := tabN (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
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
  -- the parts of the start are consistent with the view, and miss `ℓ` in their exclusive walks
  have hvu : ResU.Valid ρu := (ResU.Valid.split hc' hv'').1
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_right hcl (consistentX_left hc' hcon hv'') hvu
  have hko : (CellU.ownOf (Loc := Loc) w₀).kind ≠ Kind.imm := by simp
  have hown : ρu.get l = some (CellU.ownOf w₀) :=
    (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
  -- the lend's lifetime: fresh, below the bound, the source's content's stratum and the callback's
  obtain ⟨γ, hγ⟩ := hbnd δ (models_empty_any _)
  -- `[TR]` 6.60 at the side condition `⊢ A ⊒ @b`: every value of `A` below `@bδ`
  obtain ⟨b, hdef, hOb⟩ := hO
  obtain ⟨βP, hβP⟩ : ∃ β : Life, b.interp δ = some β := hdef δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(βP ⊓ βf ⊓ γ))
  have hαlt : α < βP ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαP : α < βP := lt_of_lt_of_le hαlt (inf_le_left.trans inf_le_left)
  have hunif : ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ' j u r →
      r.InStratum α :=
    vN_outlivesLe (models_empty_any _) hβP hαP hOb
  have houtP : σ₀.InStratum α := hunif Θ k' w₀ σ₀ hw₀
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ bnd α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP
  set Fam : Nat → Val → SPropS Loc Val α := famL α P Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam k' w₀ ⟨σ₀, houtP⟩ := (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact hw₀)
  -- the callback's world and view
  set Θ' := Θ.add l α Fam with hΘ'
  set c' := setLife c l α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l Fam⟩⟩
  have hview : Θ'.view c' = (Θ.view c).set l α Fam := LocTy.view_add Θ c l α Fam
  have hcf' : ConsistentX c' ρf := consistentX_setLife hcf (exS_none_of_part hc' hv'' hown hko) α
  have hcσ' : ConsistentX c' σ₀ :=
    consistentX_setLife hcσ (exS_none_of_part hcl hvu (ResU.single_get_self _ _) hko) α
  set Rc := claimR l α Fam with hRc
  have hFS : Fo.SuspendC x bnd := suspendC_effOf hS _
  have hbase : tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Θ' c' =
      tabN (ℍ := ℍ) Fo δ' Θ' c' := tabN_effOf_base S _ _ δ' Θ' c'
  have hTw : (tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Θ' c').Twin
      (tabR (ℍ := ℍ) Rc Fo δ Θ c) := by
    rw [hbase]
    exact tabN_tabR_twin hFS Rc δ Θ' Θ c' c (fun A' hO => vN_add_eq_bnd hO δ hLt hfr l Fam)
  have hcan := tabR_can (ℍ := ℍ) (δ := δ) hfr hLt (c := c) (l := l) hFamD Fo.cdepth Fo le_rfl
    hFS
  rw [← hbase] at hcan
  have hM := erwp_M_frameCR (Φ := Θ.view c) (l := l) (A := α) (F := Fam) hFamD
    (tabN_lendOKCR hS _ δ hLt Θ' c') hTw hcan
    (Q := fun k _ b ρ => vN (ℍ := ℍ) (.tensor (.ref A) B) δ Θ k (Val.pair (Val.loc l) b) ρ)
    k' k' le_rfl ls (.app (.app (.val f) (.val .unit)) (.val (Val.loc l))) w₀ σ₀ ρu ρf ρ''
    houtP houtf (Fam k') (fun _ _ h => h) hwit hcl hc' (fun BM hBM => ?_)
  · have hM' := erwp_claimX (c := c) hFS k' ls _ ρ'' hcon hM
    refine erwp_ubindClaimRT hΘ.1 (F := Fo) (δ := δ) (c := c)
      (fun m i en h _ => by obtain ⟨o, ho, rfl, -⟩ := tabN_effOf_some h; exact (hS o ho).2.1)
      (NFv l) (DFv d l) (fun k ls ρ hR => ?_) hQo (fun k ls b ρ hq => ?_) k' ls _ ρ'' hM'
    · obtain ⟨⟨w, σ, hσ, hF, hclm⟩, hcR⟩ := hR
      exact fin_claim hdc hd hAδ hΘ ⟨w, σ, hσ, (vN_above A δ' Θ hσ).mp hF, hclm⟩ hcR
    · refine erwp_det hΦ (opTableN_down hTd) hQo
        (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
      simp [Kont.plug, Expr.subst, NFv]
      exact erwp_val (v := Val.pair (Val.loc l) b) hq
  · -- the callback, at the lend's world and view, from the borrow
    rw [← hview]
    have h1 := (hf Θ' ((LocTy.extA_add hfr l Fam).extR ρf) hOK' c' hcf' ls) α hLt
    have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' k' (Val.loc l)
        (ResU.single l (CellU.mutOf α w₀ σ₀ houtP (Fam k') hwit)) :=
      ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l α P le_rfl houtP hwit,
        fun Θ'' j u r h => hunif Θ'' j u r (by rw [← hAδ]; exact h)⟩
    have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
      (consistentX_single_mut hcσ' (by simp [hc'def, setLife]))
    have h2 := h1 Θ' (LocTy.extR_refl _ _) hOK' c' k' le_rfl (Val.loc l) _ BM hBM hcell hcBM
    rw [cN_effOf] at h2
    refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) k' ls _ BM h2
    obtain ⟨β, hβ, hbB, hst⟩ := hb
    rw [interp_ext_self] at hβ
    cases Option.some.inj hβ
    refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ => ?_⟩
    obtain ⟨Wc, hWc, hZ'⟩ :=
      (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf w)) σ Z).mpr ⟨Y, hY, hZ⟩
    have hwσ : vN (ℍ := ℍ) A δ Θ k w σ := by
      rw [← hAδ]; exact (vN_above A δ' Θ hσ).mp hFσ
    have hbB' : vN (ℍ := ℍ) B δ Θ k b ρ' :=
      vN_local B δ Θ l α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
    exact ⟨Val.loc l, b, Wc, ρ', rfl, ResU.CompS.comm hZ', ⟨l, w, σ, rfl, hWc, hwσ⟩, hbB'⟩

/-- **`ConstN` for `withbor (2)` at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_w2 (hF : FundamentalN (ℍ := ℍ)) {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} : ConstN (ℍ := ℍ) (.w2 x bnd A B S d) := by
  rintro ⟨hbnd, hO, hA, hB, hS, hdc, hder⟩ δ Θ n _
  exact withbor2S_compat hbnd hO hA hB hS hdc (hF _ _ _ _ hder) δ Θ n

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
