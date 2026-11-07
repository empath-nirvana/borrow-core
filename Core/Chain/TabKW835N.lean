import Core.Chain.TabK835N
import Core.Chain.AFrameK835N
import Core.Chain.IFrameK835N
import Core.Chain.RFrameK835N

/-!
# The typed tables at `KW` wired to the anti-frames, the guarded Mut Frame and the reborrows
`[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §7. The frames of `scope-835-iframes.md` and the guarded Mut
Frame of `scope-835-mframes.md` at the typed tables, every premise read off the tables:

* **the lender's guarded twin** `tabGK` / `finGK` (`tabG` / `finG` at a world): `tabRK`'s entries,
  every capturable one's cancel run at its cancel row's own guarded table (`cancelOblGK`);
* **the guarded Mut Frame** (`erwp_M_frameCRG` at `KW`, the Mut Frame inside an anti-frame):
  `LendOKCR` (`tabNK_lendOKCR`), the twin across the fold (`tabNK_foldTwinG`) and `CanFold`
  (`tabGK_canK`, `tabG_can` at `KW`), in `erwpK_M_frameCRG_tab`;
* **the anti-frame** (`erwp_M_antiFrameCR` at `KW`): the entries' shape (`tabGK_afok`), the twin
  across the seal (`tabGK_sealTw`) and `ASealCan` (`tabRK_canAK`, `tabR_canA` at `KW`), in
  `erwpK_M_antiFrameCR_tab`;
* **the reborrow** (`erwp_rebGen` at `KW`): `RebOKR` (`tabNK_rebOKR_K`), the twin
  (`tabNK_rebTw`) and `RebCanK` (`tabNK_rebCanK`, `tab_rebClosed` at `KW`), in
  `erwpK_rebGen_tab`.

Each cancel transfer is by induction on how deep cancel rows nest, its step the frame's cancel run
at the cancel row's tables at `KW`. The entries of the cancel row of a scheduler entry owe along
`KW.Owed` (`finSched`), so every transfer's lender entry owes along `KW.Owed`; the rows' resuming
layers are at scheduler names (`CTy.SchedOnly`, the restriction's (S1)).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel (LtLife)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont performE raiseE cancelVal opPayload)

/-! ### The lender's guarded twin at the typed world -/

/-- **The cancel run at a guarded table, ending at a claim, at the typed world** (`cancelOblGN`):
at the view and the floor of `g y`, its stops at `T`'s entries guarded by `G`. -/
def cancelOblGK (g : KW → KW) (T : KW → OpTabK KW) (G : ShareG) (R : Nat → WProp) :
    KW → Nat → List SRec → Expr → WProp :=
  fun y k ls e => erwpK (ℍ := ℍ) KW.PostK (fun z => (g z).Θ.view (g z).c)
    (fun z => cancelTabGRK (g z).lo (T z) G R) (fun _ _ _ _ _ => False) y k ls e

mutual
/-- **The lender's guarded table at the typed world** (`tabG`): `tabRK`'s entries, every
capturable one's cancel run at its cancel row's own guarded table, ending at `R`. -/
def tabGK (R : Nat → WProp) (G : ShareG) (S : UInt32 → Prop) (g : KW → KW) :
    CTy → LSub → KW → OpTabK KW
  | .eff m i q A B fin _ C, δ, x => extTabK m i
      (entNK q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN₀ (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finGK R G (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ))
      (tabGK R G S g C δ x)
  | _, _, _ => OpTabK.empty
/-- The guarded cancel obligation of a cancel row at the typed world (`finG`): `none` at `⊤`. -/
def finGK (R : Nat → WProp) (G : ShareG) (S : UInt32 → Prop) (g : KW → KW) : CTy → LSub →
    Option (KW → Nat → List SRec → Expr → WProp)
  | .top, _ => none
  | .eff m i q A B fin _ C, δ => some (cancelOblGK (ℍ := ℍ) g (fun x => extTabK m i
      (entNK q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN₀ (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finGK R G (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ))
      (tabGK R G S g C δ x)) G R)
  | .ret _, _ => some (cancelOblGK (ℍ := ℍ) g (fun _ => OpTabK.empty) G R)
  | .arr _ _, _ => some (cancelOblGK (ℍ := ℍ) g (fun _ => OpTabK.empty) G R)
  | .amp _ _, _ => some (cancelOblGK (ℍ := ℍ) g (fun _ => OpTabK.empty) G R)
  | .all _ _ _, _ => some (cancelOblGK (ℍ := ℍ) g (fun _ => OpTabK.empty) G R)
  | .nu _, _ => some (cancelOblGK (ℍ := ℍ) g (fun _ => OpTabK.empty) G R)
end

theorem finGK_eq (R : Nat → WProp) (G : ShareG) (S : UInt32 → Prop) (g : KW → KW) {F : CTy}
    (hF : F ≠ .top) (δ : LSub) :
    finGK (ℍ := ℍ) R G S g F δ =
      some (cancelOblGK (ℍ := ℍ) g (fun x => tabGK (ℍ := ℍ) R G S g F δ x) G R) := by
  cases F <;> simp_all [finGK, tabGK]

/-- **An entry of `tabNK` is a layer's, and every `tabGK` has the layer's entry at the same
key.** -/
theorem tab_lookupNGK : ∀ (F : CTy) {S : UInt32 → Prop} {g : KW → KW} {δ : LSub} {x : KW}
    {m j : UInt32} {en : OpEntK KW},
    tabNK (ℍ := ℍ) S g F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN₀ (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finNK (ℍ := ℍ) (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ) ∧
      ∀ (R : Nat → WProp) (G : ShareG) (S₂ : UInt32 → Prop) (g₂ : KW → KW) (δ₂ : LSub)
        (x₂ : KW),
        tabGK (ℍ := ℍ) R G S₂ g₂ F δ₂ x₂ m j =
          some (entNK q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ₂ x₂.Θ k v ρ)
            (fun y k v ρ => vN₀ (ℍ := ℍ) B δ₂ y.Θ k v ρ ∧ ConsistentX y.c ρ)
            (finGK (ℍ := ℍ) R G (finSched S₂ m) g₂ fin δ₂)
            (fun f y ρ => (g₂ x₂).OwedS S₂ m f (g₂ y) ρ))
  | .eff m₀ i₀ q A B fin rc C, S, g, δ, x, m, j, en, h => by
      simp only [tabNK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R G S₂ g₂ δ₂ x₂ => by
          simp only [tabGK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupNGK C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R G S₂ g₂ δ₂ x₂ => by
          simp only [tabGK, extTabK, if_neg hmj]; exact hR R G S₂ g₂ δ₂ x₂⟩
  | .ret _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h

/-- **An entry of `tabGK` is a layer's, and every `tabRK` has the layer's entry at the same
key.** -/
theorem tab_lookupGK : ∀ (F : CTy) {R : Nat → WProp} {G : ShareG} {S : UInt32 → Prop}
    {g : KW → KW} {δ : LSub} {x : KW} {m j : UInt32} {en : OpEntK KW},
    tabGK (ℍ := ℍ) R G S g F δ x m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entNK q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ x.Θ k v ρ)
        (fun y k v ρ => vN₀ (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finGK (ℍ := ℍ) R G (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ) ∧
      ∀ R' : Nat → WProp, tabRK (ℍ := ℍ) R' S g F δ x m j =
        some (entNK q B (fun k v ρ => vN₀ (ℍ := ℍ) A δ x.Θ k v ρ)
          (fun y k v ρ => vN₀ (ℍ := ℍ) B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
          (finRK (ℍ := ℍ) R' (finSched S m) g fin δ) (fun f y ρ => (g x).OwedS S m f (g y) ρ))
  | .eff m₀ i₀ q A B fin rc C, R, G, S, g, δ, x, m, j, en, h => by
      simp only [tabGK] at h
      unfold extTabK at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        obtain ⟨rfl, rfl⟩ := hmj
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R' => by
          simp only [tabRK, extTabK, and_self, if_true]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupGK C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R' => by
          simp only [tabRK, extTabK, if_neg hmj]; exact hR R'⟩
  | .ret _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, _, _, h => by simp [tabGK, OpTabK.empty] at h

/-- **A resuming entry of a restricted row's guarded table is at a scheduler name.** -/
theorem tabGK_sched {S : UInt32 → Prop} : ∀ {F : CTy}, F.SchedOnly S → ∀ {R : Nat → WProp}
    {G : ShareG} {g : KW → KW} {δ : LSub} {x : KW} {m j : UInt32} {en : OpEntK KW},
    tabGK (ℍ := ℍ) R G S g F δ x m j = some en → en.abort = false → S m
  | .eff m₀ i₀ q A B fin rc C, hS, R, G, g, δ, x, m, j, en, h, ha => by
      simp only [tabGK] at h
      rcases extTabK_some h with ⟨rfl, -, rfl⟩ | h
      · exact hS.1 ha
      · exact tabGK_sched hS.2 h ha
  | .ret _, _, _, _, _, _, _, _, _, _, h, _ => by simp [tabGK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, _, _, _, _, h, _ => by simp [tabGK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, _, _, _, _, h, _ => by simp [tabGK, OpTabK.empty] at h
  | .top, _, _, _, _, _, _, _, _, _, h, _ => by simp [tabGK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, _, _, _, _, h, _ => by simp [tabGK, OpTabK.empty] at h
  | .nu _, _, _, _, _, _, _, _, _, _, h, _ => by simp [tabGK, OpTabK.empty] at h

/-! ### The guarded Mut Frame at the typed tables -/

/-- **The callback's table and the lender's guarded twin across the fold, at the typed world**
(`tabN_tabG_twin` at `KW`, `tabNK_foldTwin` with the guarded twin). -/
theorem tabNK_foldTwinG {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {F : CTy}
    (hF : F.SuspendC xv bnd) {S : UInt32 → Prop} (hS : F.SchedOnly S) (R : Nat → WProp)
    (G : ShareG) (δ : LSub) (l : Loc) (Fam : Nat → Val → SPropS Loc Val α) (x : KW) :
    ∀ m i en, tabNK (ℍ := ℍ) S (·.lend l α Fam) F (δ.extend xv α) x m i = some en →
      ∃ en', tabGK (ℍ := ℍ) R G S id F δ x m i = some en' ∧
        en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        (en.abort = false →
          (∀ f z ρ, (x.lend l α Fam).Owed f (z.lend l α Fam) ρ → en.wk f z ρ) ∧
          (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)) := by
  intro m i en h
  have hm := tabNK_sched hS h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNGK F h
  obtain ⟨-, hA, hB, -, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R G S id δ x, rfl, rfl, ?_, ?_, rfl, fun ha => ⟨fun f z ρ hz => hz.owedS,
    fun f z ρ hz => hz.owed (hm ha)⟩⟩
  · simp only [entNK, vN_extend_of_not_free₀ (ℍ := ℍ) hA δ α]
  · simp only [entNK, vN_extend_of_not_free₀ (ℍ := ℍ) hB δ α]

/-- **The lender's guarded cancel obligations from the callback's, at the typed world**
(`tabG_can` at `KW`, the premise `CanFold` of the guarded Mut Frame), by induction on how deep
cancel rows nest. At a capturable entry, the callback's cancel run at its cancel row's table,
indexed by the lender's worlds at the lend's world, framed by `erwpK_M_frame_cancelRunCRG` at the
cancel row's tables (`FoldTwin` by `foldTwin_owed`, the cancel row being the scheduler's,
`finSched`), its own nested cancel obligations by the induction. -/
theorem tabGK_canK {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub}
    (hLt : LtLife δ bnd α) {l : Loc} {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd → ∀ (S : UInt32 → Prop),
      F.SchedOnly S →
      CanFold (fun y : KW => y.Θ.FoldInv α)
        (fun x => tabNK (ℍ := ℍ) S (·.lend l α Fam) F (δ.extend xv α) x)
        (fun x => tabGK (ℍ := ℍ) (claimR l α Fam) (CellFold l α Fam) S id F δ x) l α Fam := by
  intro d
  induction d with
  | zero =>
      intro F hd hF S _ x _ m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupNK F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF S hS x _ m i en en' h h' ha hql y hy k ls K ρk ρp Z ρkL W'' v'' χ hχ P'' hw''
    hno hZ hZd hdZd hPk hW'' hkL hc
  have hm := tabNK_sched hS h ha
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNGK F h
  simp only at h'
  rw [hR] at h'
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
  have hfS : fin.SchedOnly (finSched S m) := CTy.schedOnly_of_all (fun _ => Or.inl hm) fin
  intro P' hP'
  simp only [entNK, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finGK] at hP'
  rw [finGK_eq _ _ _ _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hc _ (finNK_eq _ _ htop _)
  have hM := erwpK_M_frame_cancelRunCRG (ℍ := ℍ) (V := KW.PostK)
    (Φ := fun z => z.Θ.view z.c) (Inv := fun y : KW => y.Θ.FoldInv α) (flI := fun _ => α)
    (flO := fun z => z.lo)
    (Ti := fun x => tabNK (ℍ := ℍ) (finSched S m) (·.lend l α Fam) fin (δ.extend xv α) x)
    (To := fun x => tabGK (ℍ := ℍ) (claimR l α Fam) (CellFold l α Fam) (finSched S m) id fin δ x)
    hFam (fun x => tabNK_lendOKCR hfin _ _ δ hLt x) (ih fin hfd hfin _ hfS)
    (fun x hx => foldTwin_owed hFam hx (tabNK_foldTwinG hfin hfS _ _ δ l Fam x))
  refine hM k k le_rfl y hy ls _ v'' χ W'' (Z.del l) ρkL hχ hdZd P'' hPk hw''
    (ResU.CompS.comm hW'') (ResU.CompS.comm hkL) (fun BM hBM => ?_)
  obtain rfl := ResU.CompS.functional hBM hZd
  have hΦ : (fun z : KW => (z.Θ.view z.c).set l α Fam) =
      fun z : KW => (z.lend l α Fam).Θ.view (z.lend l α Fam).c :=
    funext fun z => (KW.lend_view z l α Fam).symm
  rw [hΦ]
  exact erwpK_garbage hZ hno hin

/-- **The guarded Mut Frame at the typed tables** (`erwp_M_frameCRG` at `KW`): the callback's
table is the row's `tabNK` at the lend's world; the lender's is the guarded twin `tabGK`, its stops
guarded by the fold, ending at the lend's claim. Every premise of `erwpK_M_frameCRG` is discharged:
`LendOKCR` (`tabNK_lendOKCR`), `CanFold` (`tabGK_canK`) and the twin across the fold
(`foldTwin_owed`, `tabNK_foldTwinG`). -/
theorem erwpK_M_frameCRG_tab {V : KW → KW → Prop} {Φ : KW → LocFam} {xv : LifeVar}
    {bnd : Lifetime.Life} {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) {l : Loc}
    {Fam : Nat → Val → SPropS Loc Val α} (hFam : DownFam α Fam) {F : CTy}
    (hF : F.SuspendC xv bnd) {S : UInt32 → Prop} (hS : F.SchedOnly S) {Q : KW → PostN} :
    KFrame (ℍ := ℍ) V Φ (fun y => y.Θ.FoldInv α) l α Fam
      (fun y => opTableK α (tabNK (ℍ := ℍ) S (·.lend l α Fam) F (δ.extend xv α) y))
      (fun y => opTableGRK y.lo
        (tabGK (ℍ := ℍ) (claimR l α Fam) (CellFold l α Fam) S id F δ y) (CellFold l α Fam)
        (claimR l α Fam))
      (fun y => MFPost l α Fam (Q y)) Q :=
  erwpK_M_frameCRG (flI := fun _ => α) (flO := fun y => y.lo) hFam
    (fun x => tabNK_lendOKCR hF S _ δ hLt x) (tabGK_canK hLt hFam F.cdepth F le_rfl hF S hS)
    (fun x hx => foldTwin_owed hFam hx (tabNK_foldTwinG hF hS _ _ δ l Fam x))

/-! ### The anti-frame at the typed tables -/

/-- A row meeting `CTy.SuspendC` may be stopped at under an anti-frame (`tabG_afok` at `KW`). -/
theorem tabGK_afok {xv : LifeVar} {bnd : Lifetime.Life} {F : CTy} (hF : F.SuspendC xv bnd)
    (R : Nat → WProp) (G : ShareG) (S : UInt32 → Prop) (g : KW → KW) (δ : LSub) :
    ∀ x m i en, tabGK (ℍ := ℍ) R G S g F δ x m i = some en → en.abort = false →
      en.q ≠ .unr ∧ en.wc = extF := by
  intro x m i en h _
  obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupGK F h
  exact ⟨(layer_suspend F hF hL).1, rfl⟩

/-- **The callback's guarded table and the anti-frame's twin across the seal, at the typed
world.** Both are at the anti-frame's own world: they agree but for the cancel obligations, a
world `KW.Owed` owes is one the callback's entry owes, and, the row's resuming layers being at
scheduler names (`hS`), a world the anti-frame's entry owes is one `KW.Owed` owes. -/
theorem tabGK_sealTw {F : CTy} {S : UInt32 → Prop} (hS : F.SchedOnly S) (Rin Rout : Nat → WProp)
    (G : ShareG) (δ : LSub) (x : KW) :
    ∀ m i en, tabGK (ℍ := ℍ) Rin G S id F δ x m i = some en → ∃ en',
      tabRK (ℍ := ℍ) Rout S id F δ x m i = some en' ∧
      en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, x.Owed f z ρ → en.wk f z ρ) ∧ (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)) := by
  intro m i en h
  have hm := tabGK_sched hS h
  obtain ⟨q, A, B, fin, -, rfl, hR⟩ := tab_lookupGK F h
  exact ⟨_, hR Rout, rfl, rfl, rfl, rfl, rfl, fun ha => ⟨fun f z ρ hz => hz.owedS,
    fun f z ρ hz => hz.owed (hm ha)⟩⟩

/-- **The anti-frame's cancel obligations from the guarded twin's, at the typed world**
(`tabR_canA` at `KW`, the premise `ASealCan`), by induction on how deep cancel rows nest. At a
capturable entry the inner cancel run, from the opened cell at its cancel row's guarded table, is
the anti-frame's cancel run from the sealed cell at that row's `tabRK`
(`erwpK_M_antiFrame_cancelRunCR` at `KW`, `SealTwin` by `sealTwin_owed`), at the resumption world,
where the anti-frame's invariant holds; its own nested cancel obligations by the induction. -/
theorem tabRK_canAK {xv : LifeVar} {bnd : Lifetime.Life} {l : Loc} {β : Life}
    {Fo : Nat → Val → SPropS Loc Val β} {G : ShareG}
    (hG : ∀ k ls ρ, G k ls ρ → CellFold l β Fo k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β Fo k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : Fo k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (Fo k) hw))) (δ : LSub) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd → ∀ (S : UInt32 → Prop),
      F.SchedOnly S →
      ASealCan (KW.SealInv l β Fo) (fun x => tabGK (ℍ := ℍ) Rin G S id F δ x)
        (fun x => tabRK (ℍ := ℍ) Rout S id F δ x) l β Fo := by
  intro d
  induction d with
  | zero =>
      intro F hd hF S _ x _ m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupGK F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF S hS x _ m i en en' h h' ha hql y hy k ls K w σ hσ hw R ρk' hsplit hc
  have hm := tabGK_sched hS h ha
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupGK F h
  simp only at h'
  rw [hR Rout] at h'
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
  have hfS : fin.SchedOnly (finSched S m) := CTy.schedOnly_of_all (fun _ => Or.inl hm) fin
  intro P' hP'
  simp only [entNK, hcap, if_true] at hP' hc
  by_cases htop : fin = .top
  · subst htop; simp [finRK] at hP'
  rw [finRK_eq _ _ _ htop] at hP'
  cases Option.some.inj hP'
  have hM := erwpK_M_antiFrame_cancelRunCR (ℍ := ℍ) (V := KW.PostK)
    (Φ := fun z => z.Θ.view z.c) (Inv := KW.SealInv l β Fo) (flI := fun z => z.lo)
    (flO := fun z => z.lo)
    (Ti := fun x => tabGK (ℍ := ℍ) Rin G (finSched S m) id fin δ x)
    (To := fun x => tabRK (ℍ := ℍ) Rout (finSched S m) id fin δ x)
    (fun x hx => LocTy.view_down hx.1.1 x.c) (fun x hx => kw_seal_view x hx)
    (tabGK_afok hfin Rin G _ id δ)
    (fun x hx => sealTwin_owed hx.2.1 (tabGK_sealTw hfS Rin Rout G δ x)) hG hRin hRout
    (ih fin hfd hfin _ hfS)
  refine hM k y hy ls _ w σ hσ k hw R ρk' hsplit fun W X hW hX => ?_
  exact hc W X hW hX _ (finGK_eq _ _ _ _ htop _)

/-- **The Mut Anti-Frame at the typed tables** (`erwp_M_antiFrameCR` at `KW`): the callback's
table is the row's guarded twin `tabGK`, the anti-frame's the lender's twin `tabRK`, both at the
anti-frame's world. Every premise of `erwpK_M_antiFrameCR_KW` is discharged from the tables: the
entries' shape (`tabGK_afok`), the twin across the seal (`tabGK_sealTw`) and `ASealCan`
(`tabRK_canAK`). `hG`, `hRin`, `hRout` are the original's premises on the guard and the claims. -/
theorem erwpK_M_antiFrameCR_tab {V : KW → KW → Prop} {xv : LifeVar} {bnd : Lifetime.Life}
    {l : Loc} {β : Life} {Fo : Nat → Val → SPropS Loc Val β} {F : CTy} (hF : F.SuspendC xv bnd)
    {S : UInt32 → Prop} (hS : F.SchedOnly S) (δ : LSub) {G : ShareG}
    (hG : ∀ k ls ρ, G k ls ρ → CellFold l β Fo k ls ρ)
    {Rin Rout : Nat → WProp} (hRin : ∀ k ρ, Rin k ρ → claimR l β Fo k ρ)
    (hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : Fo k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (Fo k) hw))) {Q : KW → PostN} :
    AKFrame (ℍ := ℍ) V (fun y => y.Θ.view y.c) (KW.SealInv l β Fo) l β Fo
      (fun y => opTableGRK y.lo (tabGK (ℍ := ℍ) Rin G S id F δ y) G Rin)
      (fun y => opTableRK y.lo (tabRK (ℍ := ℍ) Rout S id F δ y) Rout)
      (fun y => AFPost l β Fo (Q y)) Q :=
  erwpK_M_antiFrameCR_KW (tabGK_afok hF Rin G S id δ)
    (fun x _ => tabGK_sealTw hS Rin Rout G δ x) hG hRin hRout
    (tabRK_canAK hG hRin hRout δ F.cdepth F le_rfl hF S hS)

/-! ### The reborrow at the typed tables -/

/-- **A row meeting `CTy.SuspendC` may be stopped at under a reborrow at `β ⊏ @bnd`, at the typed
world** (`tabN_rebOKR` at `KW`). -/
theorem tabNK_rebOKR_K {xv : LifeVar} {bnd : Lifetime.Life} {β : Life} {F : CTy}
    (hF : F.SuspendC xv bnd) (S : UInt32 → Prop) (g : KW → KW) (δ : LSub)
    (hLt : LtLife δ bnd β) (x : KW) : (tabNK (ℍ := ℍ) S g F δ x).RebOKR β where
  entry := fun m i en h _ => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    exact vN_inStratum_bnd₀ (layer_suspend F hF hL).2.2.2.1 hLt hp
  pb := fun m i en h y k ls w ρ hp => by
    obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    exact vN_inStratum_bnd₀ (layer_suspend F hF hL).2.2.2.2.1 hLt hp.1

/-- **The table twins itself across the reborrow, at the typed world**: a world `KW.Owed` owes is
one an entry owes, and, the row's resuming layers being at scheduler names (`hS`), a world an entry
owes is one `KW.Owed` owes. -/
theorem tabNK_rebTw {F : CTy} {S : UInt32 → Prop} (hS : F.SchedOnly S) (δ : LSub) (x : KW) :
    ∀ m i en, tabNK (ℍ := ℍ) S id F δ x m i = some en → ∃ en',
      tabNK (ℍ := ℍ) S id F δ x m i = some en' ∧
      en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (en.abort = false →
        (∀ f z ρ, x.Owed f z ρ → en.wk f z ρ) ∧ (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)) := by
  intro m i en h
  have hm := tabNK_sched hS h
  obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupNK F h
  exact ⟨_, h, rfl, rfl, rfl, rfl, rfl, fun ha => ⟨fun f z ρ hz => hz.owedS,
    fun f z ρ hz => hz.owed (hm ha)⟩⟩

/-- **The cancel obligations of a restricted row's table are closed under a reborrow, at the
typed world** (`tab_rebClosed` at `KW`, the premise `RebCanK`), by induction on how deep cancel
rows nest: each is a cancel run at its cancel row's table, closed by `erwpK_rebGen_cancelRun` at
`KW` (`RebTwin` by `rebTwin_owed`), whose own cancel obligations are closed by the induction. -/
theorem tabNK_rebCanK {xv : LifeVar} {bnd : Lifetime.Life} {δ : LSub} {β : Life}
    (hLt : LtLife δ bnd β) {le : Loc} {s : LSet} {v : Val} {R : WRes}
    {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop}
    (hE : ∀ x : KW, RebEntryGP (ℍ := ℍ) (x.Θ.view x.c) β (ResU.single le (CellU.immOf s v R hs))
      χ R Ok (fun w Y => ResU.Valid w ∧ ResU.Valid Y))
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd → ∀ (S : UInt32 → Prop),
      F.SchedOnly S →
      RebCanK (fun _ : KW => True) (fun x => tabNK (ℍ := ℍ) S id F δ x)
        (fun x => tabNK (ℍ := ℍ) S id F δ x) β (ResU.single le (CellU.immOf s v R hs)) χ R Ok := by
  have hχsplit := ResU.restrictDom_split hreb
  have hχimm : NoOwn (χ.restrictDom (R.restrict Kind.imm)) :=
    noOwn_of_imm fun m ψ e => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv e)
  intro d
  induction d with
  | zero =>
      intro F hd hF S _ x _ m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupNK F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF S hS x _ m i en en' h h' ha hql y k ls K ρk ρp w ψ Ks hnp hkw hsplit hψβ hKs hok
    hc
  simp only at h h'
  rw [h] at h'
  cases Option.some.inj h'
  have hm := tabNK_sched hS h ha
  obtain ⟨q, A, B, fin, hL, rfl, -⟩ := tab_lookupNK F h
  have hcap : capB q B = true := by
    simp only [entNK] at ha hql
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    refine ⟨hql, ?_⟩
    cases hB : B.isZero
    · rfl
    · simp [hB, hql] at ha
  have hfin := (layer_suspend F hF hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  have hfS : fin.SchedOnly (finSched S m) := CTy.schedOnly_of_all (fun _ => Or.inl hm) fin
  intro P hP
  simp only [entNK, hcap, if_true] at hP hc
  by_cases htop : fin = .top
  · subst htop; simp [finNK] at hP
  rw [finNK_eq _ _ htop] at hP
  cases Option.some.inj hP
  have hin := hc _ (finNK_eq _ _ htop _)
  have hM := erwpK_rebGen_cancelRun (ℍ := ℍ) (V := KW.PostK)
    (Φ := fun z => z.Θ.view z.c) (Inv := fun _ : KW => True) (flI := fun z => z.lo)
    (flO := fun z => z.lo)
    (Ti := fun x => tabNK (ℍ := ℍ) (finSched S m) id fin δ x)
    (To := fun x => tabNK (ℍ := ℍ) (finSched S m) id fin δ x)
    (fun x _ => hE x) hreb hOk (fun x => tabNK_rebOKR_K hfin _ id δ hLt x)
    (fun x _ => rebTwin_owed hreb (tabNK_rebTw hfS δ x)) (ih fin hfd hfin _ hfS)
  refine hM k y trivial ls _ ψ Ks (ResU.CompS.comm hKs) hψβ hok (fun Bχ hBχ => ?_)
  obtain ⟨Xk, g, hXk, hXkg, hg⟩ :=
    rebReentry_split (σB := PMap.empty) (ResU.comp_empty_right ψ) hBχ hχsplit hsplit hkw hnp
      hχimm
  obtain rfl := ResU.CompS.functional hXk (ResU.comp_empty_right ρk)
  exact erwpK_garbage hXkg hg hin

/-- **The reborrow at the typed tables** (`erwp_rebGen` at `KW`): the borrowed run and the lender
stop at the row's `tabNK` at the same world. Every table premise of `erwpK_rebGen` is discharged:
`RebOKR` (`tabNK_rebOKR_K`), the twin (`rebTwin_owed`, `tabNK_rebTw`) and `RebCanK`
(`tabNK_rebCanK`). `hE`, `hreb`, `hOk` are the original's premises on the reborrow's entry; `hE`
holds at every view (`rebEntryGV_top`, `rebEntryGV_deep`). -/
theorem erwpK_rebGen_tab {V : KW → KW → Prop} {xv : LifeVar} {bnd : Lifetime.Life} {δ : LSub}
    {β : Life} (hLt : LtLife δ bnd β) {le : Loc} {s : LSet} {v : Val} {R : WRes}
    {hs : R.InStratum s.join} {χ : WRes} {Ok : List SRec → Prop}
    (hE : ∀ x : KW, RebEntryGP (ℍ := ℍ) (x.Θ.view x.c) β (ResU.single le (CellU.immOf s v R hs))
      χ R Ok (fun w Y => ResU.Valid w ∧ ResU.Valid Y))
    (hreb : ResU.Reb β R χ)
    (hOk : ∀ (ls ls'' lsO : List SRec) (ψ Ks : WRes), Ok ls → (∀ y, y ∈ ls'' ↔ y ∈ ls) →
      ResU.CompS ψ (ResU.single le (CellU.immOf s v R hs)) Ks → extF ls'' lsO Ks → Ok lsO)
    {F : CTy} (hF : F.SuspendC xv bnd) {S : UInt32 → Prop} (hS : F.SchedOnly S)
    {Q : KW → PostN} :
    RKFrame (ℍ := ℍ) V (fun y => y.Θ.view y.c) (fun _ => True) β
      (ResU.single le (CellU.immOf s v R hs)) χ Ok
      (fun y => opTableK y.lo (tabNK (ℍ := ℍ) S id F δ y))
      (fun y => opTableK y.lo (tabNK (ℍ := ℍ) S id F δ y)) (fun y => RebPost β (Q y)) Q :=
  erwpK_rebGen (flI := fun y => y.lo) (flO := fun y => y.lo) (fun x _ => hE x) hreb hOk
    (fun x => tabNK_rebOKR_K hF S id δ hLt x)
    (fun x _ => rebTwin_owed hreb (tabNK_rebTw hS δ x))
    (tabNK_rebCanK hLt hE hreb hOk F.cdepth F le_rfl hF S hS)

/-! ### The Imm Frame at the typed tables -/

/-- **The callback's table may be stopped at under an `imm` lend at `A ⊏ @bnd`, at the typed
world** (`ILendOKCR` at `KW`): the payload and the answer at every resumption world in `Res_A`,
neither reading the record list. -/
theorem tabNK_ilendOKCR {xv : LifeVar} {bnd : Lifetime.Life} {A : Life} {F : CTy}
    (hF : F.SuspendC xv bnd) (S : UInt32 → Prop) (g : KW → KW) (δ : LSub)
    (hLt : LtLife δ bnd A) (x : KW) : (tabNK (ℍ := ℍ) S g F (δ.extend xv A) x).ILendOKCR A where
  entry := fun m i en h _ => by
    obtain ⟨q, A', B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    exact ⟨(layer_suspend F hF hL).1, rfl⟩
  pa := fun m i en h k ls v ρ hp => by
    obtain ⟨q, A', B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    obtain ⟨-, hA, -, hOA, -⟩ := layer_suspend F hF hL
    have hp' : vN₀ (ℍ := ℍ) A' (δ.extend xv A) x.Θ k v ρ := hp
    rw [vN_extend_of_not_free₀ hA] at hp'
    exact vN_inStratum_bnd₀ hOA hLt hp'
  pb := fun m i en h y k ls w ρ hp => by
    obtain ⟨q, A', B, fin, hL, rfl, -⟩ := tab_lookupNK F h
    obtain ⟨-, -, hB, -, hOB, -⟩ := layer_suspend F hF hL
    have hp' : vN₀ (ℍ := ℍ) B (δ.extend xv A) y.Θ k w ρ := hp.1
    rw [vN_extend_of_not_free₀ hB] at hp'
    exact vN_inStratum_bnd₀ hOB hLt hp'
  paExt := fun m i en h k ls₁ ls₂ v ρ _ hp => by
    obtain ⟨q, A', B, fin, -, rfl, -⟩ := tab_lookupNK F h
    exact hp
  pbExt := fun m i en h y k ls₁ ls₂ w ρ _ hp => by
    obtain ⟨q, A', B, fin, -, rfl, -⟩ := tab_lookupNK F h
    exact hp

/-- **The callback's table and the lender's twin across the `imm` fold, at the typed world**
(`tabNK_foldTwin` for an `imm` lend): the callback's entries, indexed by the lender's worlds, owe at
the lend's world (`KW.lendImm`); the lender's at its own. -/
theorem tabNK_ifoldTwin {xv : LifeVar} {bnd : Lifetime.Life} {A : Life} {F : CTy}
    (hF : F.SuspendC xv bnd) {S : UInt32 → Prop} (hS : F.SchedOnly S) (Rr : Nat → WProp)
    (δ : LSub) (r : FrameRec) (x : KW) :
    ∀ m i en, tabNK (ℍ := ℍ) S (·.lendImm r A) F (δ.extend xv A) x m i = some en →
      ∃ en', tabRK (ℍ := ℍ) Rr S id F δ x m i = some en' ∧
        en'.q = en.q ∧ en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        (en.abort = false →
          (∀ f z ρ, (x.lendImm r A).Owed f (z.lendImm r A) ρ → en.wk f z ρ) ∧
          (∀ f z ρ, en'.wk f z ρ → x.Owed f z ρ)) := by
  intro m i en h
  have hm := tabNK_sched hS h
  obtain ⟨q, A', B, fin, hL, rfl, hR⟩ := tab_lookupNK F h
  obtain ⟨-, hA, hB, -, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR Rr S id δ x, rfl, rfl, ?_, ?_, rfl, fun ha => ⟨fun f z ρ hz => hz.owedS,
    fun f z ρ hz => hz.owed (hm ha)⟩⟩
  · simp only [entNK, vN_extend_of_not_free₀ (ℍ := ℍ) hA δ A]
  · simp only [entNK, vN_extend_of_not_free₀ (ℍ := ℍ) hB δ A]

/-- A row whose every layer is must-resume. -/
def _root_.BoCa.Fig16.LogRel.Core.CTy.LinOnly : CTy → Prop
  | .eff _ _ q _ _ _ _ C => q = .lin ∧ CTy.LinOnly C
  | _ => True

/-- An entry of a must-resume row's table is must-resume and not abortive. -/
theorem tabNK_linOnly {S : UInt32 → Prop} {g : KW → KW} {δ : LSub} {x : KW} :
    ∀ {F : CTy}, F.LinOnly → ∀ {m j : UInt32} {en : OpEntK KW},
      tabNK (ℍ := ℍ) S g F δ x m j = some en → en.q = .lin ∧ en.abort = false
  | .eff m₀ i₀ q A B fin rc C, hL, m, j, en, h => by
      simp only [tabNK] at h
      rcases extTabK_some h with ⟨rfl, -, rfl⟩ | h
      · simp [entNK, hL.1]
      · exact tabNK_linOnly hL.2 h
  | .ret _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .top, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h
  | .nu _, _, _, _, _, h => by simp [tabNK, OpTabK.empty] at h

/-- **The Imm Frame at the typed tables, every layer must-resume** (`erwp_I_frame` at `KW`): the
callback's table is the row's `tabNK` at the lend's world (`KW.lendImm`), indexed by the lender's
worlds; the lender's is the twin `tabRK` at its own world. Every premise of `erwpK_I_frameT_KW` is
discharged: `ILendOKCR` (`tabNK_ilendOKCR`), no abortive entry and `ICanK` (`tabNK_linOnly`,
`icanK_of_lin`), and the twin across the fold (`tabNK_ifoldTwin`). -/
theorem erwpK_I_frame_tab {V : KW → KW → Prop} {Φ : KW → LocFam} (l : Loc) (Ty : VTy)
    (δr : LSub) (hadm : AdmWf Ty δr) (v : Val) (P : List SRec → Val → WProp)
    (hPshape : ∀ ls ρ, P ls v ρ → vShape Ty δr v ρ)
    (hPloc : ∀ ls₁ ls₂ ρ, extF ls₁ ls₂ ρ → P ls₁ v ρ → P ls₂ v ρ)
    {A : Life} {ρP ρlP : WRes} (houtP : ρP.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP)
    {ds : List FrameRec} (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, ρP, Ty, δr⟩ d)
    {xv : LifeVar} {bnd : Lifetime.Life} {δ : LSub} (hLt : LtLife δ bnd A) {F : CTy}
    (hF : F.SuspendC xv bnd) (hlin : F.LinOnly) {S : UInt32 → Prop} (hS : F.SchedOnly S)
    (Rr : Nat → WProp) {Q : KW → PostN}
    (hQ : ∀ y k ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q y k ls₁ w ρ → Q y k ls₂ w ρ) :
    IKFrame (ℍ := ℍ) V Φ (fun y => y.Θ.FoldInv A) l Ty δr v P A ρP ρlP houtP ds
      (fun y => opTableK A
        (tabNK (ℍ := ℍ) S (·.lendImm ⟨l, v, ρP, Ty, δr⟩ A) F (δ.extend xv A) y))
      (fun y => opTableK y.lo (tabRK (ℍ := ℍ) Rr S id F δ y))
      (fun y => IFPost l v P A (Q y)) Q :=
  erwpK_I_frameT_KW l Ty δr hadm v P hPshape hPloc houtP hclP hds
    (fun x => tabNK_ilendOKCR hF S _ δ hLt x)
    (fun _ _ _ _ h => (tabNK_linOnly hlin h).2)
    (icanK_of_lin fun _ _ _ _ h _ => (tabNK_linOnly hlin h).1)
    (fun x _ => tabNK_ifoldTwin hF hS Rr δ _ x) hQ

end BoCa.Fig16.LogRel.Core.Chain.SI

end
