import Core.Chain.Goal791N
import Core.Chain.TabKW835N
import Core.Chain.FrameListK835N

/-!
# The `n`-cell Mut Frame at the typed tables  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §7. Core's `wpG_M_frameList` across stops, raises and layered
cancel runs, at `KW`: the list induction over the Mut Frame at an incoming claim
(`erwpK_M_frameCRR`, `FamCancel836N.lean`'s `erwp_M_frameCRR` at a world), each frame's step
discharged from the typed tables.

* **The run is indexed by the outermost lender's worlds.** A world map `g` follows the lends the
  frames took (`KW.LendMap`: the identity, or a lend after one): frame `j`'s lender owes at
  `g y`, its callback at `(g y).lend ℓⱼ αⱼ Fⱼ`, and its location family is `g y`'s view.
* **The lender's twin under `g`** (`tabRK R vr g F δ`) is each frame's table: the payload and the
  answer read at the index world, the order and the cancel runs at `g`'s world.
* **The step** (`erwpK_M_frameCRR_listKW`) is `erwpK_M_frameCRR` with every premise from the
  tables: `LendOKCR` (`tabRK_lendOKCR`), the twin across the fold under `g` (`foldTwin_owedG`,
  `tabRK_foldTwinR`), `CanFold` (`tabRK_canRK`); the claim joined to the
  inner frames' by `tabRK_finLe`.
* **The cells at `vN`** (`claimL`, `listPostN`, `mutLeafN`): the places' cells and the frames'
  post read at `cN`'s value relation; the tables are the lender's twin at `vN`.
* **The list** (`erwpK_M_frameListKW`): each lifetime fresh, below every `imm` record
  (`LocTy.exists_foldInv`, the frame's invariant `FoldInv αⱼ` at `g x`), below the frame's rest,
  `β`, `β′` and the bound.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### The lender's twin under a world map -/

/-- **An entry of `tabRK` is a layer's, and every `tabRK` has the layer's entry at the same
key.** -/
theorem tab_lookupRK : ∀ (F : CTy) {R : Nat → WProp} {vr : VRel} {g : KW → KW}
    {δ : LSub} {x : KW} {m j : UInt32} {en : OpEntK KW},
    tabRK (ℍ := ℍ) R vr g F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vr A δ x.Θ k v ρ)
        (fun y k v ρ => vr B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finRK (ℍ := ℍ) R vr g fin δ) (fun f y ρ => (g x).Owed f (g y) ρ) ∧
      ∀ (R₂ : Nat → WProp) (g₂ : KW → KW) (δ₂ : LSub) (x₂ : KW),
        tabRK (ℍ := ℍ) R₂ vr g₂ F δ₂ x₂ m j =
          some (entNK q B (fun k v ρ => vr A δ₂ x₂.Θ k v ρ)
            (fun y k v ρ => vr B δ₂ y.Θ k v ρ ∧ ConsistentX y.c ρ)
            (finRK (ℍ := ℍ) R₂ vr g₂ fin δ₂)
            (fun f y ρ => (g₂ x₂).Owed f (g₂ y) ρ))
  | .eff m₀ i₀ q A B fin rc C, R, vr, g, δ, x, m, j, en, h => by
      simp only [tabRK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R₂ g₂ δ₂ x₂ => by
          simp only [tabRK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupRK C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R₂ g₂ δ₂ x₂ => by
          simp only [tabRK, extTabK, if_neg hmj]; exact hR R₂ g₂ δ₂ x₂⟩
  | .ret _, _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, _, h => by simp [tabRK, OpTabK.empty] at h

/-- **The frame's callback table may be stopped at under a lend at `α ⊏ @bnd`, at the typed
world**. -/
theorem tabRK_lendOKCR {vr : VRel} (hv : ValRelOK vr) {xv : LifeVar} {bnd : Lifetime.Life}
    {α : Life} {F : CTy} (hF : F.SuspendC xv bnd) (R : Nat → WProp) (g : KW → KW) (δ : LSub)
    (hLt : LtLife δ bnd α) (x : KW) : (tabRK (ℍ := ℍ) R vr g F δ x).LendOKCR α where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupRK F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupRK F h
    exact hv.inStratum (layer_suspend F hF hL).2.2.2.1 hLt hp
  pb := fun m i en h y k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupRK F h
    exact (hv.inStratum (layer_suspend F hF hL).2.2.2.2.1 hLt hp.1).mono
      (Life.down_sqsubset α).le

/-- **The frame's callback table and its lender's twin across the fold, under a world map**: the
callback's entries owe at the lend's world after `g`, the lender's at `g`'s world. They agree but
for the cancel obligations; a world the lend's order owes is one the callback's entry owes, and a
world the lender's entry owes is one `KW.Owed` owes. -/
theorem tabRK_foldTwinR {F : CTy} {vr : VRel} (R R' : Nat → WProp)
    (g : KW → KW) (δ : LSub) (l : Loc) {α : Life} (Fam : Nat → Val → SPropS Loc Val α) (x : KW) :
    ∀ m i en, tabRK (ℍ := ℍ) R vr (fun y => (g y).lend l α Fam) F δ x m i = some en →
      ∃ en', tabRK (ℍ := ℍ) R' vr g F δ x m i = some en' ∧
        en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        (en.abort = false →
          (∀ f z ρ, ((g x).lend l α Fam).Owed f ((g z).lend l α Fam) ρ → en.wk f z ρ) ∧
          (∀ f z ρ, en'.wk f z ρ → (g x).Owed f (g z) ρ)) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hR⟩ := tab_lookupRK F h
  exact ⟨_, hR R' g δ x, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨fun f z ρ hz => hz,
    fun f z ρ hz => hz⟩⟩

/-- **`FoldTwin` at the typed world, under a world map** (`foldTwin_owed` with the lender at
`g x`): the lender's entries owe along `KW.Owed` at `g`'s world, the borrowed run's at the lend's
world after `g`; `FoldInv A` holds at `g x`. The frame's invariant is `FoldInv A` at `g y`. -/
theorem foldTwin_owedG {g : KW → KW} {x : KW} {l : Loc} {A : Life}
    {F : Nat → Val → SPropS Loc Val A} (hF : DownFam A F) (hx : (g x).Θ.FoldInv A)
    {Ti To : OpTabK KW}
    (hTw : ∀ m i en, Ti m i = some en → ∃ en', To m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, ((g x).lend l A F).Owed f ((g z).lend l A F) ρ → en.wk f z ρ) ∧
        (∀ f z ρ, en'.wk f z ρ → (g x).Owed f (g z) ρ))) :
    Ti.FoldTwin (fun y => (g y).Θ.FoldInv A) A (g x).lo To l A := by
  intro m i en hTe
  obtain ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, hwk⟩ := hTw m i en hTe
  refine ⟨en', hTe', h₁, h₂, h₃, h₄, h₅, fun ha ρk ρp Z W'' ρkL χ v hχ P hw hZ hZl hW'' hkL hvZ
    hvkL f hf => ⟨min f (g x).lo, min_le_right _ _, fun y hy => ?_⟩⟩
  obtain ⟨hin, hout⟩ := hwk ha
  obtain ⟨h, hyA⟩ := kw_owed_foldAt hF hx hf (min_le_left _ _) hZ hZl hW'' hkL hvZ hvkL
    (hout _ _ _ hy)
  exact ⟨hin _ _ _ h, hyA⟩

/-- **The lender's cancel obligations from the frame's callback's, under a world map**
(the premise `CanFold`), by induction on how deep cancel rows nest. At a
capturable entry, the callback's cancel run at its cancel row's twin, ending at `R`, is framed by
`erwpK_M_frame_cancelRunCRR` at the cancel row's tables (`FoldTwin` by `foldTwin_owedG`), its own
nested cancel obligations by the induction. -/
theorem tabRK_canRK {vr : VRel} (hv : ValRelOK vr) {xv : LifeVar} {bnd : Lifetime.Life}
    {α : Life} {δ : LSub}
    (hLt : LtLife δ bnd α) {l : Loc} {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam)
    {R : Nat → WProp} (hR : ∀ k ρ, R k ρ → ρ.InStratum α) (g : KW → KW) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd →
      CanFold (fun y : KW => (g y).Θ.FoldInv α)
        (fun x => tabRK (ℍ := ℍ) R vr (fun y => (g y).lend l α Fam) F δ x)
        (fun x => tabRK (ℍ := ℍ) (fun k => claimR l α Fam k ⋆ R k) vr g F δ x) l α Fam := by
  intro d
  induction d with
  | zero =>
      intro F hd hF x _ m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupRK F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF x _ m i en en' h h' ha hql y hy k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw''
    hno hZ hZd hdZd hPk hW'' hkL hc
  obtain ⟨q, A, B, fin, hL, rfl, hR'⟩ := tab_lookupRK F h
  simp only at h'
  rw [hR'] at h'
  cases Option.some.inj h'
  have hcap : capB q B = true := by
    simp only [entNK] at ha hql
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨hql, ?_⟩
    cases hB : B.isZero
    · rfl
    · simp [hB, hql] at ha
  have hfin := (layer_suspend F hF hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entNK, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finRK] at hP'
  rw [finRK_eq _ _ _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hc _ (finRK_eq _ _ _ htop _)
  have hM := erwpK_M_frame_cancelRunCRR (ℍ := ℍ) (V := KW.PostK)
    (Φ := fun z => (g z).Θ.view (g z).c) (Inv := fun y : KW => (g y).Θ.FoldInv α)
    (flI := fun _ => α) (flO := fun z => (g z).lo)
    (Ti := fun x => tabRK (ℍ := ℍ) R vr (fun y => (g y).lend l α Fam) fin δ x)
    (To := fun x => tabRK (ℍ := ℍ) (fun k => claimR l α Fam k ⋆ R k) vr g fin δ x)
    hFam (fun x => tabRK_lendOKCR hv hfin R _ δ hLt x) (ih fin hfd hfin) hR
    (fun x hx => foldTwin_owedG hFam hx (tabRK_foldTwinR R _ g δ l Fam x))
  refine hM k k le_rfl y hy ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  have hΦ : (fun z : KW => ((g z).Θ.view (g z).c).set l α Fam) =
      fun z : KW => ((g z).lend l α Fam).Θ.view ((g z).lend l α Fam).c :=
    funext fun z => (KW.lend_view (g z) l α Fam).symm
  rw [hΦ]
  exact erwpK_garbage hZ hno hin

/-! ### A weaker claim -/

section FinLe
variable {ι : Type}

/-- **One table's entries are another's but for weaker cancel obligations** (`OpTabN.Le` over a
world index, the orders the same). -/
def _root_.BoCa.Fig16.LogRel.Core.Chain.SI.OpTabK.FinLe (T T' : OpTabK ι) : Prop :=
  ∀ m i en, T m i = some en → ∃ en', T' m i = some en' ∧ en'.q = en.q ∧ en'.abort = en.abort ∧
    en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ en'.wk = en.wk ∧
    ∀ P', en'.fin = some P' → ∃ P, en.fin = some P ∧ ∀ y k ls e ρ, P y k ls e ρ → P' y k ls e ρ

theorem performStopK_finLe {lo : Life} {T T' : OpTabK ι} (hT : T.FinLe T') :
    ∀ k ls t (Ψ Ψ' : ContK ι) ρ, (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
      performStopK lo T k ls t Ψ ρ → performStopK lo T' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ ⟨K, n, i, v, en, hp⟩
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨en', h₃', hq, hab, hPA, hPB, hwc, hwk, hfl⟩ := hT n i en h₃
  refine ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩ ⟨ρa, ρk, hc, hPA ▸ hA,
    fun hu' => hu (hq.symm.trans hu'), f, hf, fun y hy ls' he => ?_⟩⟩
  rw [hwk] at hy
  rw [hwc] at he
  refine ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_, fun hq' P' hP' => ?_⟩
  · rw [hPB] at hB
    exact hΨ y k' hk' _ _ _ ((hcont y hy ls' he).1 k' hk' w σ₁ σ₂ hB hcσ)
  · obtain ⟨P, hP, hPP⟩ := hfl P' hP'
    exact hPP _ _ _ _ _ ((hcont y hy ls' he).2 (hq ▸ hq') P hP)

theorem errOkK_finLe {T T' : OpTabK ι} (hT : T.FinLe T') :
    ∀ {k : Nat} {ls : List SRec} {err : Option Val} {ρ : WRes}, errOkK T k ls err ρ →
      errOkK T' k ls err ρ
  | _, _, none, _, h => h
  | _, _, some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      obtain ⟨en', hTe', -, hab', hPA', -⟩ := hT m j en hTe
      exact ⟨m, j, w, en', pure_sep_mk ⟨hE, hTe', hab' ▸ ha⟩ ⟨hPA' ▸ hPA, hn⟩⟩

/-- **`opTableRK` widened along `FinLe` and a weaker claim.** -/
theorem opTableRK_finLe {lo : Life} {T T' : OpTabK ι} (hT : T.FinLe T') {R R' : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → R' k ρ) :
    ∀ k ls t (Ψ Ψ' : ContK ι) ρ, (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
      opTableRK lo T R k ls t Ψ ρ → opTableRK lo T' R' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with h | ⟨K, n, i, v, en, hp⟩
  · exact Or.inl (performStopK_finLe hT k ls t Ψ Ψ' ρ hΨ h)
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρ₁, ρ₂, hc, ⟨ρa, ρn, hcn, ⟨hPA, hnA⟩, hnn⟩, hRk⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨en', h₃', -, hab, hPA', -⟩ := hT n i en h₃
    exact Or.inr ⟨K, n, i, v, en', pure_sep_mk ⟨h₁, h₂, h₃', hab ▸ h₄⟩
      ⟨ρ₁, ρ₂, hc, ⟨ρa, ρn, hcn, ⟨hPA' ▸ hPA, hnA⟩, hnn⟩, hR _ _ hRk⟩⟩

/-- **`cancelTabRK` widened along `FinLe` and a weaker claim.** -/
theorem cancelTabRK_finLe {lo : Life} {T T' : OpTabK ι} (hT : T.FinLe T') {R R' : Nat → WProp}
    (hR : ∀ k ρ, R k ρ → R' k ρ) :
    ∀ k ls t (Ψ Ψ' : ContK ι) ρ, (∀ y k', k' < k → ∀ ls e ρ, Ψ y k' ls e ρ → Ψ' y k' ls e ρ) →
      cancelTabRK lo T R k ls t Ψ ρ → cancelTabRK lo T' R' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with h | ⟨K, err, hp⟩
  · exact Or.inl (performStopK_finLe hT k ls t Ψ Ψ' ρ hΨ h)
  · obtain ⟨hc, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hRk⟩ := pure_sep_iff.mp hp
    exact Or.inr ⟨K, err, pure_sep_mk hc ⟨y1, y2, hy, ⟨τa, τb, hcab, errOkK_finLe hT herr, hnb⟩,
      hR _ _ hRk⟩⟩

end FinLe

/-- **The lender's twin is monotone in its claim, at the typed world**: at a
weaker claim every cancel run, at every depth, ends at the weaker claim. -/
theorem tabRK_finLe {R R' : Nat → WProp} (hR : ∀ k ρ, R k ρ → R' k ρ) (g : KW → KW)
    (δ : LSub) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → ∀ (vr : VRel) x,
      (tabRK (ℍ := ℍ) R vr g F δ x).FinLe (tabRK (ℍ := ℍ) R' vr g F δ x) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F hd vr x m i en h
  obtain ⟨q, A, B, fin, hL, rfl, hR'⟩ := tab_lookupRK F h
  refine ⟨_, hR' R' g δ x, rfl, rfl, rfl, rfl, rfl, rfl, fun P' hP' => ?_⟩
  simp only [entNK] at hP' ⊢
  by_cases hcap : capB q B = true
  · rw [if_pos hcap] at hP' ⊢
    by_cases htop : fin = .top
    · subst htop; simp [finRK] at hP'
    rw [finRK_eq _ _ _ htop] at hP' ⊢
    cases Option.some.inj hP'
    have hfd := layer_cdepth F hL
    refine ⟨_, rfl, fun y k ls e ρ h' => ?_⟩
    exact erwpK_mono (fun _ _ h => h) (fun _ _ _ _ _ h => h)
      (fun z => cancelTabRK_finLe (ih fin.cdepth (by omega) fin le_rfl _ z) hR) k y ls e ρ h'
  · rw [if_neg hcap] at hP'; cases hP'

/-! ### The step and the list -/

/-- **The world maps of the frames' lends**: the identity, or a lend after one. -/
inductive _root_.BoCa.Fig16.LogRel.Core.Chain.SI.KW.LendMap : (KW → KW) → Prop
  | id : KW.LendMap fun y => y
  | lend {g : KW → KW} (h : KW.LendMap g) (l : Loc) (α : Life)
      (F : Nat → Val → SPropS Loc Val α) : KW.LendMap fun y => (g y).lend l α F

/-! ### The cells at `vN` -/

/-- **The composite claim of a family's frames** at `vN`: the cells owned again, each holding a
member of `A` at the world `Θ`. -/
def claimL (A : VTy) (δ : LSub) (Θ : LocTy) (I : List Loc) : Nat → WProp :=
  fun k => sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I

/-- The post of a family's frames at `Θ`: the cells owned again beside the callback's answer. -/
def listPostN (A : VTy) (δ : LSub) (Ψ : LocTy → PostN) (Θ : LocTy) (I : List Loc) : PostN :=
  fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
    sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂

/-- **A `mut` leaf at `α`** at the world `Θ`, at `vN`: the cell at some `b ⊒ α` holding a member
of the payload stored at the world's key `(ℓ, b)`. -/
def mutLeafN (A : VTy) (δ : LSub) (α : Life) (Θ : LocTy) (n : Nat) (m : Loc) : WProp := fun ρ =>
  ∃ b : Life, α ≤ b ∧ mutL b (fun Θ' j u r => vN (ℍ := ℍ) A δ Θ' j u r) Θ n (Val.loc m) ρ ∧
    ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ' j u r → r.InStratum b

/-- An owned leaf lies in every stratum below its payload's. -/
theorem ownLeafN_inStratum {A : VTy} {δ : LSub} {β α : Life} (hαβ : α ≤ β)
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β) {Θ : LocTy} {n : Nat}
    {m : Loc} {ρ : WRes} (h : vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m) ρ) : ρ.InStratum α := by
  obtain ⟨l, u, σ, -, hc, hu⟩ := h
  exact inStratum_compS hc (ResU.inStratum_single_own α l u) ((hunif _ _ _ _ hu).mono hαβ)

/-- **The table of the frames at the typed world**, after the lends `g`: the row's lender's twin
under `g`, at `g`'s floor, its raises and cancel runs ending at the claim of the cells `I` at
`Θ`. -/
def tabListK (A : VTy) (δ : LSub) (F : CTy) (Θ : LocTy) (g : KW → KW)
    (I : List Loc) : KW → TableK KW :=
  fun y => opTableRK (g y).lo
    (tabRK (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ I) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
      g F δ y)
    (claimL (ℍ := ℍ) A δ Θ I)

theorem tabListK_local (A : VTy) (δ : LSub) (F : CTy) (Θ : LocTy)
    (g : KW → KW) (I : List Loc) (y : KW) : (tabListK (ℍ := ℍ) A δ F Θ g I y).Local :=
  or_local (performStopK_local _ _) (raiseStopRK_free _ _)

/-- **One frame of the list at the typed tables**: the lend
of `ℓ` at `α` after the lends `g`, from the table at the inner world to the table at the outer
one. Every premise of `erwpK_M_frameCRR` is discharged from the tables (`tabRK_lendOKCR`,
`tabRK_canRK`, `foldTwin_owedG` with `tabRK_foldTwinR`); the claim is joined to the inner frames'
by `tabRK_finLe`. The frame's invariant is `FoldInv α` at `g y`. -/
theorem erwpK_M_frameCRR_listKW {V : KW → KW → Prop} {A : VTy} {δ : LSub} {β : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β) {xv : LifeVar}
    {bnd : Lifetime.Life} {F : CTy} (hF : F.SuspendC xv bnd) (Ψ : LocTy → PostN) (g : KW → KW)
    (Θ : LocTy) (ℓ : Loc) {α : Life}
    (hLt : LtLife δ bnd α) (hαβ : α ≤ β) (I : List Loc) :
    KFrame (ℍ := ℍ) V (fun y => (g y).Θ.view (g y).c) (fun y => (g y).Θ.FoldInv α) ℓ α
      (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
      (tabListK (ℍ := ℍ) A δ F (Θ.add ℓ α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ))
        (fun y => (g y).lend ℓ α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)) I)
      (tabListK (ℍ := ℍ) A δ F Θ g (ℓ :: I))
      (fun _ => MFPost ℓ α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
        (listPostN (ℍ := ℍ) A δ Ψ Θ (ℓ :: I)))
      (fun _ => listPostN (ℍ := ℍ) A δ Ψ Θ (ℓ :: I)) := by
  set Fm : Nat → Val → SPropS Loc Val α :=
    famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ with hFm
  have hFmD : DownFam α Fm := vN_fam_down A δ α Θ
  set Θ₁ := Θ.add ℓ α Fm with hΘ₁
  have hRs : ∀ k ρ', claimL (ℍ := ℍ) A δ Θ₁ I k ρ' → ρ'.InStratum α := fun k ρ' h =>
    sepList_closed (ResU.inStratum_empty α) (fun _ _ _ hc a b => inStratum_compS hc a b)
      (fun m τ hm => ownLeafN_inStratum hαβ hunif hm) h
  have hcl' : ∀ k ρ', (claimR ℓ α Fm k ⋆ claimL (ℍ := ℍ) A δ Θ₁ I k) ρ' →
      claimL (ℍ := ℍ) A δ Θ (ℓ :: I) k ρ' := by
    rintro k ρ' ⟨ρ₁, ρ₂, hc12, ⟨w, σ', hσ', hFσ, hcw⟩, hr⟩
    refine ⟨ρ₁, ρ₂, hc12, ⟨ℓ, w, σ', rfl, hcw, (vN_above A δ Θ hσ').mp hFσ⟩, ?_⟩
    exact sepList_mono_down (R := fun τ => τ.InStratum α)
      (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
        ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
      (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α Fm k _ τ hτ hm) (hRs k ρ₂ hr) hr
  have hM := erwpK_M_frameCRR (ℍ := ℍ) (V := V) (Φ := fun y => (g y).Θ.view (g y).c)
    (Inv := fun y => (g y).Θ.FoldInv α) (flI := fun _ => α) (flO := fun y => (g y).lo)
    (Ti := fun x => tabRK (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ₁ I)
      (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
      (fun y => (g y).lend ℓ α Fm) F δ x)
    (To := fun x => tabRK (ℍ := ℍ) (fun k => claimR ℓ α Fm k ⋆ claimL (ℍ := ℍ) A δ Θ₁ I k)
      (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) g F δ x)
    (Q := fun _ => listPostN (ℍ := ℍ) A δ Ψ Θ (ℓ :: I)) hFmD
    (fun x => tabRK_lendOKCR valRelOK_vN hF _ _ δ hLt x)
    (tabRK_canRK valRelOK_vN hLt hFmD hRs g F.cdepth F le_rfl hF)
    hRs (fun x hx => foldTwin_owedG hFmD hx (tabRK_foldTwinR _ _ g δ ℓ Fm x))
  exact KFrame.conv hM (fun _ => or_local (performStopK_local _ _) (raiseStopRK_free _ _))
    (fun y k ls t Ψ' ρ h => opTableRK_finLe (tabRK_finLe hcl' g δ F.cdepth F le_rfl _ y) hcl' k ls t
      Ψ' Ψ' ρ (fun _ _ _ _ _ _ h => h) h)

/-- **One Mut Frame per place, around one expression, at the typed tables, the lends taken read
by a predicate `Lm`**: the list induction, the run indexed by the
outermost lender's worlds, after the lends `g` the frames before took, `Lm g` kept by every
lend below the bound and `β′` (`hLm`), each frame `erwpK_M_frameCRR_listKW`. Frame
`j` lends its leaf at `αⱼ`, fresh and below every `imm` record of `g x` (`LocTy.exists_foldInv`),
below the frame's rest, `β`, `β′` and the bound, as in the original. -/
theorem erwpK_M_frameListKWP {V : KW → KW → Prop} {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    {xv : LifeVar} {bnd : Lifetime.Life} {mb : Life} (hmb : bnd.interp δ = some mb) {F : CTy}
    (hF : F.SuspendC xv bnd)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) (x : KW) (Lm : (KW → KW) → Prop)
    (hLm : ∀ g, Lm g → ∀ (ℓ : Loc) (α : Life) (Fm : Nat → Val → SPropS Loc Val α),
      LtLife δ bnd α → α ≤ β' → Lm fun y => (g y).lend ℓ α Fm) :
    ∀ (I : List Loc) (g : KW → KW), Lm g → ∀ (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      (g x).Θ.OK → ConsistentX (g x).c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ (g x).Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ g', Lm g' → (g x).Θ.ExtA (g' x).Θ →
        (g' x).Θ.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α (g' x).Θ n) I ρm →
          ResU.CompS ρH ρm ρ' → ConsistentX (g' x).c ρ' →
          erwpK (ℍ := ℍ) V (fun y => (g' y).Θ.view (g' y).c)
            (tabListK (ℍ := ℍ) A δ F (g' x).Θ g' []) (fun _ => Ψ (g' x).Θ) x n ls e ρ') →
      erwpK (ℍ := ℍ) V (fun y => (g y).Θ.view (g y).c) (tabListK (ℍ := ℍ) A δ F (g x).Θ g I)
        (fun _ => listPostN (ℍ := ℍ) A δ Ψ (g x).Θ I) x n ls e ρ
  | [], g, hg, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ] at hc ⊢
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 g hg (LocTy.extA_refl _) hΘ PMap.empty ρH
        ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hc
      exact erwpK_mono (fun _ _ h => h) (fun _ k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩)
        (fun y k ls t Ψ Ψ' ρ hΨ h => tabListK_local A δ F _ g [] y k ls t Ψ Ψ' ρ hΨ h)
        n x ls e ρH h
  | ℓ :: I, g, hg, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      obtain ⟨Fr, hFr, hρ⟩ := compS_reassoc hc0 hcρ
      refine erwpK_of_valid fun hv => ?_
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hko : (CellU.ownOf (Loc := Loc) u).kind ≠ Kind.imm := by simp
      have hown : ρ0.get ℓ = some (CellU.ownOf u) :=
        (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
      have hcF : ConsistentX (g x).c Fr := consistentX_right hρ hc hv
      have hcσ : ConsistentX (g x).c σ := consistentX_right hcl (consistentX_left hρ hc hv) hvρ0
      -- the outer frame's lifetime: fresh, below every `imm` record, the frame's rest, `β`, `β′`
      -- and the bound
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum Fr
      obtain ⟨α₁, hα₁le, hfi⟩ := LocTy.exists_foldInv hΘ.2 (↓(βF ⊓ β ⊓ β' ⊓ mb))
      have hfr : (g x).Θ.Fresh α₁ := hfi.1
      have hα₁lt : α₁ < βF ⊓ β ⊓ β' ⊓ mb := lt_of_le_of_lt hα₁le (Life.down_sqsubset _)
      have hα₁F : α₁ ≤ βF := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
      have hα₁β : α₁ ≤ β := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
      have hα₁β' : α₁ ≤ β' := hα₁lt.le.trans (inf_le_left.trans inf_le_right)
      have hα₁mb : α₁ < mb := lt_of_lt_of_le hα₁lt inf_le_right
      have hLt : LtLife δ bnd α₁ := ⟨mb, hmb, hα₁mb⟩
      set P : CPredL := fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P (g x).Θ with hFm
      have houtP : σ.InStratum α₁ := (hunif (g x).Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum (↓α₁) := hβF.mono ((Life.down_sqsubset α₁).le.trans hα₁F)
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above A δ (g x).Θ houtP).mpr hu
      have hFmD : DownFam α₁ Fm := vN_fam_down A δ α₁ (g x).Θ
      set g₁ : KW → KW := fun y => (g y).lend ℓ α₁ Fm with hg₁
      have hg₁L : Lm g₁ := hLm g hg ℓ α₁ Fm hLt hα₁β'
      have hOK₁ : (g₁ x).Θ.OK := LocTy.ok_add hΘ ℓ hFmD
      have hE₁ : (g x).Θ.ExtA (g₁ x).Θ := LocTy.extA_add hfr ℓ Fm
      have hcF₁ : ConsistentX (g₁ x).c Fr :=
        consistentX_setLife hcF (exS_none_of_part hρ hv hown hko) α₁
      have hcσ₁ : ConsistentX (g₁ x).c σ :=
        consistentX_setLife hcσ (exS_none_of_part hcl hvρ0 (ResU.single_get_self _ _) hko) α₁
      refine erwpK_M_frameCRR_listKW hunif hF Ψ g (g x).Θ ℓ hLt hα₁β I n n le_rfl x hfi ls e
        u σ ρ0 Fr ρ houtP houtb (Fm n) (fun _ _ h => h) hwit hcl hρ (fun BM hBM => ?_)
      have hΦ₁ : (fun y => ((g y).Θ.view (g y).c).set ℓ α₁ Fm) =
          fun y => (g₁ y).Θ.view (g₁ y).c :=
        funext fun y => (KW.lend_view (g y) ℓ α₁ Fm).symm
      rw [hΦ₁]
      -- `BM = ρr ● R`, `R = ρH ● cell`
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hFr hBM
      have hcBM : ConsistentX (g₁ x).c BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hg₁, KW.lend, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ (g₁ x).Θ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA (.ref A) δ hE₁ n _ τ h) hrest
      refine erwpK_mono (fun _ _ h => h) (fun _ k ls' v ρ' h => ?_)
        (fun y k ls t Ψ Ψ' ρ hΨ h => tabListK_local A δ F _ g₁ I y k ls t Ψ Ψ' ρ hΨ h) n x ls
        e BM
        (erwpK_M_frameListKWP hunif hmb hF Ψ hΨs hΨl e ls x Lm hLm I g₁ hg₁L n ρr R BM
          (βR ⊓ α₁ ⊓ γ) hOK₁ hcBM hBMR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt
            (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ (g x).Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local (.ref A) δ (g x).Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl (g x).Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN (ℍ := ℍ) A δ (g x).Θ k w σ' := (vN_above A δ (g x).Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro g' hg' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN (ℍ := ℍ) A δ α₂ (g' x).Θ n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL (g x).Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 g' hg' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

/-- **One Mut Frame per place, around one expression, at the typed tables**: `erwpK_M_frameListKWP`
at `KW.LendMap`. Frame `j` lends its leaf at `αⱼ`, fresh and below every `imm` record of `g x`
(`LocTy.exists_foldInv`), below the frame's rest, `β`, `β′` and the bound, as in the original. -/
theorem erwpK_M_frameListKW {V : KW → KW → Prop} {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    {xv : LifeVar} {bnd : Lifetime.Life} {mb : Life} (hmb : bnd.interp δ = some mb) {F : CTy}
    (hF : F.SuspendC xv bnd)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) (x : KW) :
    ∀ (I : List Loc) (g : KW → KW), KW.LendMap g → ∀ (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      (g x).Θ.OK → ConsistentX (g x).c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ (g x).Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ g', KW.LendMap g' → (g x).Θ.ExtA (g' x).Θ →
        (g' x).Θ.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α (g' x).Θ n) I ρm →
          ResU.CompS ρH ρm ρ' → ConsistentX (g' x).c ρ' →
          erwpK (ℍ := ℍ) V (fun y => (g' y).Θ.view (g' y).c)
            (tabListK (ℍ := ℍ) A δ F (g' x).Θ g' []) (fun _ => Ψ (g' x).Θ) x n ls e ρ') →
      erwpK (ℍ := ℍ) V (fun y => (g y).Θ.view (g y).c) (tabListK (ℍ := ℍ) A δ F (g x).Θ g I)
        (fun _ => listPostN (ℍ := ℍ) A δ Ψ (g x).Θ I) x n ls e ρ :=
  erwpK_M_frameListKWP hunif hmb hF Ψ hΨs hΨl e ls x KW.LendMap
    (fun _ hg ℓ α Fm _ _ => KW.LendMap.lend hg ℓ α Fm)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
