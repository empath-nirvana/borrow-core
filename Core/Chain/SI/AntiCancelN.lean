import Core.Chain.SI.AntiStopN
import Core.Chain.SI.UbindN
import Core.Chain.SI.LendProg

/-!
# The Mut Anti-Frame across a cancellable stop

**Not a transcription.** At a cancellable stop the continuation owes a cancel run
(`cancelOKN`). Inside an anti-frame the callback's cancel run starts from the opened cell; it
ends at the cancel's `raise` carrying the cell's claim, `ℓ ↦ own(w) ● χ` with `χ` in the family
(`claimR`, the claim the Mut Frame's cancel run carries, `SI/StopCancelN.lean`). The anti-frame's
cancel run starts from the sealed cell and runs the callback's: at the `raise` the claim is
sealed again, `ℓ ↦ mut(β, w, χ, F k)`, which owns nothing, so the anti-frame's cancel run ends
at an ordinary cancel `raise` (`erwp_M_antiFrame_cancelRun`). So an anti-frame consumes the claim
a lend inside it leaves, and turns a `claimT` table back into the plain one
(`erwp_M_antiFrameC`).

The other pieces: the Mut Frame's fold recorded at a cancellable stop (`erwp_M_frameTF`), the
cancel obligation of a lend read at the borrowed run's location typing (`claimT_canS`), the frame
across cancellable stops (`erwpG_frameT`, with `erwp_frame_cancelRun`), and twin tables
(`opTableG_twinC`).

The cancel runs here perform nothing (`cancelTabR OpTabN.empty`): a finaliser that performs on
the cancel path is not covered (as in `SI/FinPerformN.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### Twin tables -/

/-- `T′` has `T`'s entries, with cancel obligations at least as weak. -/
def OpTabN.TwinC (T T' : OpTabN) : Prop :=
  ∀ m i en, T m i = some en → ∃ en', T' m i = some en' ∧ en'.q = en.q ∧
    en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
    ∀ k ls K ρ, cancelOKN en k ls K ρ → cancelOKN en' k ls K ρ

/-- A guarded stop at a twin with a weaker guard. -/
theorem opTableG_twinC {T T' : OpTabN} (hTT : T.TwinC T') {G G' : ShareG}
    (hG : ∀ k ls ρ, G k ls ρ → G' k ls ρ) :
    ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      opTableG T G k ls t Ψ ρ → opTableG T' G' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h⟩ := opTableG_local T G k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hGk, hu, hcont⟩ := pure_sep_iff.mp h
  obtain ⟨en', h₃', hq, hab, hPA, hPB, hwc, hcan⟩ := hTT n i en h₃
  refine ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab.trans h₄⟩ ⟨ρa, ρk, hc, hPA ▸ hA,
    hG _ _ _ hGk, fun hu' => hu (hq ▸ hu'), fun ls' he => ?_⟩⟩
  rw [hwc] at he
  refine ⟨fun k' hk' w => hPB ▸ (hcont ls' he).1 k' hk' w, fun hq' => ?_⟩
  exact hcan k ls' K ρk ((hcont ls' he).2 (hq ▸ hq'))

/-! ### Cancel runs: claims weakened, framed -/

/-- A cancel run's claim weakened. -/
theorem erwp_cancelRun_mono {Φ : LocFam} {T₁ : OpTabN} {R R' : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → R' k ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (cancelTabR T₁ R) (fun _ _ _ _ => False) n ls e ρ →
      erwp (ℍ := ℍ) Φ (cancelTabR T₁ R') (fun _ _ _ _ => False) n ls e ρ := by
  refine erwp_mono (fun _ _ _ _ h => h) fun k ls t Ψ Ψ' ρ hΨ h => ?_
  rcases cancelTabR_local T₁ R k ls t Ψ Ψ' ρ hΨ h with ⟨K, err, hp⟩ | h
  · obtain ⟨hc, y1, y2, hy, he, hRk⟩ := pure_sep_iff.mp hp
    exact Or.inl ⟨K, err, pure_sep_mk hc ⟨y1, y2, hy, he, hR _ _ hRk⟩⟩
  · exact Or.inr h

/-- **The frame over a cancel run that performs nothing**: the frame rides to the cancel's
`raise`, beside the claim. -/
theorem erwp_frame_cancelRun {Φ : LocFam} {R : Nat → WProp} (R₂ : WProp) :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → R₂ ρ₂ →
      erwp (ℍ := ℍ) Φ (cancelTabR OpTabN.empty R) (fun _ _ _ _ => False) n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (cancelTabR OpTabN.empty (fun k => R k ⋆ R₂)) (fun _ _ _ _ => False)
        n ls e ρ := by
  intro n ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_)
    (rwpG_frame (fun _ => R₂) (fun _ _ _ _ h => h) hc h hR₂)
  rcases ht with ⟨_, _, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact hf.elim
  · obtain ⟨hpur, y1, y2, hy, he, hRk⟩ := pure_sep_iff.mp hp
    obtain ⟨y2', hy2', hy'⟩ := compS_reassoc hy hσ
    exact Or.inr (Or.inl ⟨K, err, pure_sep_mk hpur ⟨y1, y2', hy', he, y2, σ₂, hy2', hRk, hσ₂⟩⟩)
  · exact absurd (pure_sep_iff.mp hp).1.2.2.1 (by simp [OpTabN.empty])

/-! ### The anti-frame over a cancel run -/

/-- **The Mut Anti-Frame over a cancel run.** The callback's cancel run, from the opened cell,
ends at a cancel's `raise` carrying the cell's claim; from the sealed cell the run ends at an
ordinary cancel `raise`: the claim sealed again, owning nothing (`rwpG_M_antiFrameG` at the
`raise`). -/
theorem erwp_M_antiFrame_cancelRun {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) (n : Nat) (ls : List SRec)
    (e : Expr) (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat)
    (hwit : F j v ⟨σP, hstr⟩) (ρa ρ : WRes)
    (hsplit : ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ)
    (hA : ∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
      erwp (ℍ := ℍ) Φ (cancelTabR OpTabN.empty (claimR l β F)) (fun _ _ _ _ => False) n ls e X) :
    erwp (ℍ := ℍ) Φ (cancelTabN OpTabN.empty) (fun _ _ _ _ => False) n ls e ρ := by
  rw [erwp_eq]
  refine rwpG_M_antiFrameG hΦ hF hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ⟨_, _, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact hf.elim
  · obtain ⟨hpur, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, w, σ, hσ, hFk, hc⟩ :=
      pure_sep_iff.mp hp
    -- `ρ′ = ℓ ↦ own(w) ● (σ ● y₁)`
    obtain ⟨rest, hrest, hρ'⟩ := compS_lcomm hc hy
    refine ⟨w, σ, hσ, hFk, y1, rest, hρ', ResU.CompS.comm hrest, fun X hX => ?_⟩
    obtain ⟨τbm, hτbm, hX'⟩ := compS_reassoc hcab hX
    exact Or.inr (Or.inl ⟨K, err, pure_sep_mk hpur ⟨τa, τbm, hX', herr,
      noOwn_compS hτbm hnb (LendProg.noOwn_single_mut l)⟩⟩)
  · exact absurd (pure_sep_iff.mp hp).1.2.2.1 (by simp [OpTabN.empty])

/-! ### The anti-frame across cancellable stops -/

/-- **Mut Anti-Frame at `erwp`, across stops, cancellable ones included.** The callback's
table is `claimT T Φ ∅ (claimR ℓ β F)`: its cancellable stops owe a cancel run ending at the
cell's claim; the anti-frame's stops, at `T`, owe the cancel run `T` asks
(`cancelOblN Φ ∅`), which is the callback's with the cell sealed at the `raise`
(`erwp_M_antiFrame_cancelRun`). -/
theorem erwp_M_antiFrameC {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T : OpTabN}
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ OpTabN.empty))
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableG (@OpTabN.claimT ℍ _ T Φ OpTabN.empty (claimR l β F))
          (CellFold l β F)) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_eq]
  refine rwpG_M_antiFrameG hΦ hF hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ⟨v', rfl, w, σ', h', hw', R, rest, h1, h2, hQ⟩ | ⟨K, m, i, v₀, en', hp⟩
  · exact ⟨w, σ', h', hw', R, rest, h1, h2, fun X hX => Or.inl ⟨v', rfl, hQ X hX⟩⟩
  obtain ⟨⟨rfl, hK, hTe', ha'⟩, ρa', ρk, hcak, hPA, ⟨w, σ', h', hw', R, rest, hk1, hk2⟩, -,
    hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨en, hTe, hen⟩ := claimT_some hTe'
  have hsame : en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧
      en'.wc = en.wc := by
    subst hen; by_cases hq : en.q = .cancel <;> simp [hq]
  obtain ⟨hq', hab', hPA', hPB', hwc'⟩ := hsame
  have ha : en.abort = false := hab' ▸ ha'
  obtain ⟨hqu, hwc⟩ := hT m i en hTe ha
  obtain ⟨y, hy1, hy2⟩ := compS_lcomm hk1 hcak
  obtain ⟨R', hR', hσR'⟩ := compS_lcomm hk2 hy1
  refine ⟨w, σ', h', hw', R', y, hy2, hσR', fun X hX => ?_⟩
  obtain ⟨ρk', hRk, hX'⟩ := compS_reassoc hR' hX
  -- `X₀ = R ● σ_B ● σ′ ● ℓ ↦ own(w)` is `ρ_k ● σ_B`
  have hback : ∀ (σB ac X₀ W : WRes), ResU.CompS R σB ac →
      ResU.CompS σ' (ResU.single l (CellU.ownOf w)) W → ResU.CompS ac W X₀ →
      ResU.CompS ρk σB X₀ := by
    intro σB ac X₀ W hac hW hX₀
    obtain ⟨t, ht1, ht2⟩ := compS_reassoc hac hX₀
    obtain ⟨ac3, hac3, hW3⟩ := compS_lcomm (ResU.CompS.comm ht1) ht2
    obtain ⟨WR, hWR, hX₀'⟩ := compS_reassoc' hac3 hW3
    obtain ⟨ac2, hac2, hac2W⟩ := compS_exch hW hWR
    obtain rfl : ac2 = rest := ResU.CompS.functional hac2 hk2
    obtain rfl : WR = ρk := ResU.CompS.functional (ResU.CompS.comm hac2W) hk1
    exact hX₀'
  refine Or.inr (Or.inl ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa', ρk', hX',
    hPA' ▸ hPA, fun hu => absurd hu hqu, fun ls'' he => ⟨fun k' hk' w' σB XB hB hXB => ?_,
      fun hql P hP => ?_⟩⟩⟩)
  · simp only [erwpC, show k' < n by omega, if_true]
    have he' : en'.wc ls' ls'' ρk := by
      rw [hwc', hwc]; rw [hwc] at he
      exact extF_seal hk1 hk2 hRk (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) he
    obtain ⟨ac, hac, hacX⟩ := compS_exch hRk hXB
    refine ih k' (by omega) ls'' _ w σ' h' k hw' ac XB (ResU.CompS.comm hacX)
      fun W X₀ hW hX₀ => ?_
    have hc := (hcont ls'' he').1 k' (by omega) w' σB X₀ (hPB' ▸ hB) (hback σB ac X₀ W hac hW hX₀)
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact hc
  · -- the cancel run: the callback's, the cell sealed at its `raise`
    have hqc : en.q = .cancel := by cases h : en.q <;> simp_all
    rw [hfin m i en hTe hqc] at hP
    cases hP
    have he' : en'.wc ls' ls'' ρk := by
      rw [hwc', hwc]; rw [hwc] at he
      exact extF_seal hk1 hk2 hRk (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) he
    have hcan := (hcont ls'' he').2 (hq' ▸ hql)
    subst hen
    simp only [hqc, if_true] at hcan
    have hrun := hcan _ rfl
    exact erwp_M_antiFrame_cancelRun hΦ hF k ls'' _ w σ' h' k hw' R ρk' (ResU.CompS.comm hRk)
      fun W X₀ hW hX₀ => by
        obtain rfl : X₀ = ρk := by
          have h0 := hback PMap.empty R X₀ W (ResU.comp_empty_right R) hW hX₀
          exact ResU.CompS.functional h0 (ResU.comp_empty_right ρk)
        exact hrun

/-! ### The Mut Frame's fold at a cancellable stop -/

/-- **`erwp_M_frameT` with its stops guarded by the fold** (`erwp_M_frameF` with cancellable
entries). -/
theorem erwp_M_frameTF {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
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
      erwp (ℍ := ℍ) Φ (opTableG T' (CellFold l A F)) Q n ls e ρ := by
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
    have hfold : CellFold l A F k ls' ρkL := by
      obtain ⟨hχ', hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
      obtain ⟨ac, hac, hacl⟩ := compS_exch hW'' (ResU.CompS.comm hkL)
      exact ⟨v'', χ, hχ', hFk, Z.del l, ac, ResU.CompS.comm hacl, hac⟩
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr
      ⟨K, m, i, v₀, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρkL, haY,
        hPA' ▸ hPA, hfold, fun hu' => absurd (hq'.symm.trans hu') hq, fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hql => ?_⟩⟩⟩⟩
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

/-- **`claimT_can` with the borrowed run's cancel obligation read at its own location typing**
`Φ[ℓ ↦ (A, F)]`: what a borrowed run whose cancel runs open `ℓ`'s cell (an anti-frame inside the
lend) needs. -/
theorem claimT_canS {Φ : LocFam} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) {T T₁ : OpTabN}
    (hT₁ : T₁.LendOK A)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) (Φ.set l A F) T₁))
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
  exact erwp_garbage hZ hno hin

/-! ### The frame across cancellable stops -/

/-- **The frame at `erwp` at a guarded table, across cancellable stops**: `erwpG_frame` with the
twin `T′`, whose cancel obligations are `T`'s with the frame added (`hcan`). -/
theorem erwpG_frameT {Φ : LocFam} {T T' : OpTabN}
    (hT : ∀ m i en, T m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    (hTT' : T.Twin T') (R₂ : WProp)
    (hcan : ∀ m i en en', T m i = some en → T' m i = some en' → en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk σ₂ ρk₂ : WRes), ResU.CompS ρk σ₂ ρk₂ → R₂ σ₂ →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρk₂)
    {G : ShareG} {Q : PostN} :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → R₂ ρ₂ →
      erwp (ℍ := ℍ) Φ (opTableG T G) Q n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (opTableG T' (G.sep fun _ => R₂)) (fun k ls' v => Q k ls' v ⋆ R₂) n ls e
        ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_)
    (rwpG_frame (fun _ => R₂) (fun _ _ _ _ h => h) hc h hR₂)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, rfl, σ₁, σ₂, hσ, hv, hσ₂⟩
  obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hA, hG, -, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨hqu, hwc⟩ := hT m i en hTe ha
  obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT' m i en hTe
  obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
  refine Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩ ⟨ρa, ρk₂, haσ,
    hPA' ▸ hA, ⟨ρk, σ₂, hk₂, hG, hσ₂⟩, fun hu' => absurd (hq' ▸ hu') hqu, fun ls'' he =>
      ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩
  · have he' : en.wc ls' ls'' ρk := by rw [hwc]; rw [hwc', hwc] at he; exact extF_left _ _ _ _ _ hk₂ he
    obtain ⟨y, hy, hyτ⟩ := compS_exch hk₂ hcτ
    have hc' := (hcont ls'' he').1 k' hk' w τ₁ y (hPB' ▸ hB) hy
    simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
    exact ih k' (by omega) ls'' _ y σ₂ τ₂ hyτ hσ₂ hc'
  · have he' : en.wc ls' ls'' ρk := by rw [hwc]; rw [hwc', hwc] at he; exact extF_left _ _ _ _ _ hk₂ he
    exact hcan m i en en' hTe hTe' (hq' ▸ hql) k ls'' K ρk σ₂ ρk₂ hk₂ hσ₂
      ((hcont ls'' he').2 (hq' ▸ hql))

end BoCa.Fig16.LogRel.Core.Chain.SI

end
