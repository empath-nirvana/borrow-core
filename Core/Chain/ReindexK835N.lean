import Core.Chain.Goal791N

/-!
# A run re-indexed along a world map  `[spec §19, §27]`

`docs/new-core/scope-835-tables.md` §10.3. A lend's callback is a thunk of the relation at the
typed world: `cN` at the lend's world, its tables indexed by its own worlds. The Mut Frame reads
the callback's run indexed by the lender's worlds, at the tables under the lend's world map
(`KW.lend`). `erwpK_comap` moves a run along a world map `g`: a run from `g x`, indexed by `ι`, is
a run from `x`, indexed by `ι′`, when the location family at `y` is the one at `g y`, every post
at a world `g x` reaches is one at a world `x` reaches, and every stop at `g y`'s table is a stop
at `y`'s whose continuation is owed only at the images of the worlds it is owed at.

The callback's table step (`tabNK_lend_comap`, `erwpK_lend_comap`) is `erwpK_comap` at
`g = (·.lend ℓ α F)`: a stop at the callback's own table `tabN F δ′` at the lend's world is a stop
at `tabNK vN g F δ′`, the table the Mut Frame reads. The payload and the answer move between the
lend's world and the index world (`vN_lend_eq`: the lend's variable unread, `vN_add_eq` below the
bound), the answer's view by `consistentX_of_outlivesN` (the constants' bound is closed), the
order is the same, and each cancel obligation moves by `erwpK_comap` again, by induction on how
deep cancel rows nest.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

/-- **`erwpK` along a world map, at the worlds an invariant holds at.** A run from `g x` over `ι`
is one from `x` over `ι′`, at `x` with `Inv x`: the location family at `y` is `Φ (g y)`; a post at
a world `g x` reaches is one at a world `x` reaches; a stop at `g y`'s table, `Inv y`, is one at
`y`'s, its continuation owed at `y′` (with `Inv y′`) wherever the first owes it at `g y′`. -/
theorem erwpK_comap {ι ι' : Type} (g : ι' → ι) (Inv : ι' → Prop) {V : ι → ι → Prop}
    {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN} {V' : ι' → ι' → Prop}
    {Φ' : ι' → LocFam} {Tb' : ι' → TableK ι'} {Q' : ι' → PostN} (hΦ : ∀ y, Φ' y = Φ (g y))
    (hQ : ∀ x, Inv x → ∀ y k ls v ρ, V (g x) y → Q y k ls v ρ → ∃ y', V' x y' ∧ Q' y' k ls v ρ)
    (hT : ∀ y, Inv y → ∀ k ls t (Ψ : ContK ι) (Ψ' : ContK ι') ρ,
      (∀ y' k', k' < k → Inv y' → ∀ ls e ρ, Ψ (g y') k' ls e ρ → Ψ' y' k' ls e ρ) →
      Tb (g y) k ls t Ψ ρ → Tb' y k ls t Ψ' ρ) :
    ∀ n x, Inv x → ∀ ls e ρ, erwpK (ℍ := ℍ) V Φ Tb Q (g x) n ls e ρ →
      erwpK (ℍ := ℍ) V' Φ' Tb' Q' x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x hx ls e ρ h
  rw [erwpK_eq] at h ⊢
  rw [hΦ x]
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, y, hy, hq⟩ | ht
  · obtain ⟨y', hy', hq'⟩ := hQ x hx y _ _ _ _ hy hq
    exact Or.inl ⟨v, hv, y', hy', hq'⟩
  · refine Or.inr (hT x hx k ls' t _ _ σ (fun y' k' hk' hy' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpCK, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) y' hy' _ _ _ hΨ

/-- **Adding a lend at `α` is an extension at a resource in `Res_α`**, fresh or not: such a
resource reads only keys above `α`, which the lend leaves as they are (`LocTy.extR_of_add`'s
converse). -/
theorem LocTy.extR_add (Θ : LocTy) (l₀ : Loc) {α : Life} (F : Nat → Val → SPropS Loc Val α)
    {ρ : WRes} (hρ : ρ.InStratum α) : Θ.ExtR (Θ.add l₀ α F) ρ := by
  refine ⟨fun l a G hG hc => ?_, fun x hx _ => hx⟩
  have hαa : α < a := hc.of_stratum hρ
  rw [LocTy.add_keep Θ l₀ F l (ne_of_gt hαa)]
  exact ⟨hG, LocTy.above_add Θ l₀ (not_lt_of_gt hαa) F⟩

open Goal791N in
/-- **A lend below a bound is invisible to `𝒱⟦A⟧` of an `A` outliving the bound**, at every
world (`vN_add_eq_bnd` without freshness): the value's resource is in `Res_α`
(`vN_inStratum_bnd`), where adding and dropping the lend are both extensions. -/
theorem vN_add_eq {A : VTy} {bnd : Lifetime.Life}
    (hO : VOutlives BoCa.Lifetime.LifeCtx.empty bnd A) (δ : BoCa.Lifetime.LSub) {α : Life}
    (hLt : LogRel.LtLife δ bnd α) (Θ : LocTy) (l : Loc) (F : Nat → Val → SPropS Loc Val α) :
    vN (ℍ := ℍ) A δ (Θ.add l α F) = vN (ℍ := ℍ) A δ Θ := by
  funext n v ρ
  exact propext ⟨fun h => vN_local A δ Θ l α F n v ρ (vN_inStratum_bnd hO hLt h) h,
    fun h => vN_extR A δ n v ρ (LocTy.extR_add Θ l F (vN_inStratum_bnd hO hLt h)) h⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (interp_top_of_defines_empty)
open BoCa.BoLo (Kont performE raiseE cancelVal opPayload)

/-! ### The callback's table step -/

/-- **An answer of a type outliving a closed bound is consistent with every view**: the bound is
`⊤`, the value's resource in `Res_⊤` (`vN_outlives`), which holds no borrow cell
(`consistentX_of_top`). -/
theorem consistentX_of_outlivesN {bnd : Lifetime.Life} (hbnd : LifeCtx.empty.Defines bnd)
    {B : VTy} (hOB : VOutlives LifeCtx.empty bnd B) {δ : LSub} {Θ : LocTy} {k : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) B δ Θ k v ρ) (c : Loc → Option Life) : ConsistentX c ρ :=
  consistentX_of_top (vN_outlives (models_empty_any _) (interp_top_of_defines_empty hbnd δ) hOB
    Θ k v ρ h) c

/-- **A layer's types read alike at the lend's world and the lender's**: the lend's variable is
not mentioned (`vN_extend_of_not_free`) and the lend lies below the bound the type outlives
(`vN_add_eq`). -/
theorem vN_lend_eq {xv : LifeVar} {bnd : Lifetime.Life} {A : VTy} (hA : ¬ VFree xv A)
    (hO : VOutlives LifeCtx.empty bnd A) {δ : LSub} {α : Life} (hLt : LtLife δ bnd α) (y : KW)
    (l : Loc) (Fam : Nat → Val → SPropS Loc Val α) :
    vN (ℍ := ℍ) A (δ.extend xv α) (y.lend l α Fam).Θ = vN (ℍ := ℍ) A (δ.extend xv α) y.Θ := by
  rw [vN_extend_of_not_free hA]
  exact vN_add_eq hO δ hLt y.Θ l Fam

/-- **An entry of the callback's own table at the lend's world is an entry of its table under
the lend's world map, at the same key**: same qualifier, abortiveness and order, the payload moved
from the lend's world to the index world (`vN_lend_eq`). -/
theorem tabNK_lend_entry {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub}
    (hLt : LtLife δ bnd α) (l : Loc) (Fam : Nat → Val → SPropS Loc Val α) {F : CTy}
    (hF : F.SuspendC xv bnd) {y : KW} {n i : UInt32} {en : OpEntK KW}
    (h : tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F (δ.extend xv α)
      (y.lend l α Fam) n i = some en) :
    ∃ en', tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (·.lend l α Fam) F
        (δ.extend xv α) y n i = some en' ∧ en'.q = en.q ∧ en'.abort = en.abort ∧
      ∀ k ls v ρ, en.PA k ls v ρ → en'.PA k ls v ρ := by
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNNK F h
  obtain ⟨-, hA, -, hOA, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR _ y, rfl, rfl, fun k ls v ρ hp => ?_⟩
  have hp' : vN (ℍ := ℍ) A (δ.extend xv α) (y.lend l α Fam).Θ k v ρ := hp
  rw [vN_lend_eq hA hOA hLt y l Fam] at hp'
  exact hp'

/-- **The error a cancel raise carries, at the callback's tables**: an abortive entry's payload at
the lend's world is one under the lend's world map. -/
theorem errOkK_lend {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub}
    (hLt : LtLife δ bnd α) (l : Loc) (Fam : Nat → Val → SPropS Loc Val α) {F : CTy}
    (hF : F.SuspendC xv bnd) (y : KW) {k : Nat} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes},
      errOkK (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F (δ.extend xv α)
        (y.lend l α Fam)) k ls err ρ →
      errOkK (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (·.lend l α Fam) F
        (δ.extend xv α) y) k ls err ρ
  | none, _, h => h
  | some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      obtain ⟨en', h', -, hab, hPA'⟩ := tabNK_lend_entry hLt l Fam hF hTe
      exact ⟨m, j, w, en', pure_sep_mk ⟨hE, h', hab ▸ ha⟩ ⟨hPA' _ _ _ _ hPA, hn⟩⟩

/-- **The callback's table step** (`erwpK_comap`'s `hT` at `g = (·.lend ℓ α F)`): a stop at the
callback's own table at the lend's world is a stop at its table under the lend's world map. The
payload and the answer move between the lend's world and the index world by `vN_lend_eq`; the
answer's view by `consistentX_of_outlivesN` (the bound closed); the order is the same; the cancel
obligations move by `erwpK_comap` again, by induction on how deep cancel rows nest. -/
theorem tabNK_lend_comap {xv : LifeVar} {bnd : Lifetime.Life} (hbnd : LifeCtx.empty.Defines bnd)
    {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) (l : Loc) (Fam : Nat → Val → SPropS Loc Val α) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd →
      ∀ (lo : Life) (y : KW) k ls t (Ψ Ψ' : ContK KW) ρ,
        (∀ y' k', k' < k → ∀ ls e ρ, Ψ (y'.lend l α Fam) k' ls e ρ → Ψ' y' k' ls e ρ) →
        performStopK lo (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F
          (δ.extend xv α) (y.lend l α Fam)) k ls t Ψ ρ →
        performStopK lo (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
          (·.lend l α Fam) F (δ.extend xv α) y) k ls t Ψ' ρ := by
  intro d
  induction d with
  | zero =>
      intro F hd hF lo y k ls t Ψ Ψ' ρ _ h
      obtain ⟨K, n, i, v, en, h⟩ := h
      obtain ⟨⟨-, -, h₃, -⟩, -⟩ := pure_sep_iff.mp h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupNNK F h₃
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF lo y k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNNK F h₃
  obtain ⟨-, hnA, hnB, hOA, hOB, hfinS⟩ := layer_suspend F hF hL
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  refine ⟨K, n, i, v, _, pure_sep_mk ⟨h₁, h₂, hR (·.lend l α Fam) y, h₄⟩
    ⟨ρa, ρk, hc, ?_, hu, f, hf, fun y' hy' ls' he => ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_,
      fun hq P hP => ?_⟩⟩⟩
  · have hp : vN (ℍ := ℍ) A (δ.extend xv α) (y.lend l α Fam).Θ k v ρa := hA
    rw [vN_lend_eq hnA hOA hLt y l Fam] at hp
    exact hp
  · have hB' : vN (ℍ := ℍ) B (δ.extend xv α) y'.Θ k' w σ₁ := hB.1
    have hBs : vN (ℍ := ℍ) B (δ.extend xv α) (y'.lend l α Fam).Θ k' w σ₁ := by
      rw [vN_lend_eq hnB hOB hLt y' l Fam]; exact hB'
    exact hΨ y' k' hk' _ _ _ ((hcont (y'.lend l α Fam) hy' ls' he).1 k' hk' w σ₁ σ₂
      ⟨hBs, consistentX_of_outlivesN hbnd hOB hBs _⟩ hcσ)
  · simp only [entNK] at hP hq
    by_cases hcap : capB q B = true
    · rw [if_pos hcap] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finNK] at hP
      rw [finNK_eq _ _ htop] at hP
      cases Option.some.inj hP
      have hfin := hfinS hcap
      have hs := (hcont (y'.lend l α Fam) hy' ls' he).2 hq _
        (by simp only [entNK, if_pos hcap]; exact finNK_eq _ _ htop _)
      refine erwpK_comap (ℍ := ℍ) (fun z : KW => z.lend l α Fam) (fun _ => True)
        (fun _ => rfl) (fun _ _ _ _ _ _ _ _ hq => hq.elim) ?_ k y' trivial ls' _ ρk hs
      intro z _ k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁ hΨ₁ h₁
      rcases h₁ with h₁ | ⟨K₁, err, h₁⟩
      · exact Or.inl (ih fin hfd hfin _ z k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁
          (fun y'' k'' hk'' ls'' e'' ρ'' h => hΨ₁ y'' k'' hk'' trivial ls'' e'' ρ'' h) h₁)
      · obtain ⟨hK, hr⟩ := pure_sep_iff.mp h₁
        obtain ⟨τ₁, τ₂, hτ, he₁, hn⟩ := hr
        exact Or.inr ⟨K₁, err, pure_sep_mk hK ⟨τ₁, τ₂, hτ, errOkK_lend hLt l Fam hfin z he₁, hn⟩⟩
    · rw [if_neg hcap] at hP; cases hP

/-- **The callback's run under the lend's world map** (`erwpK_comap` at `g = (·.lend ℓ α F)`): the
callback's run at its own table, from the lend's world, is its run indexed by the lender's worlds,
at its table under the lend's world map, its location family the lend's world's view, its floor
the lend's. Every stop moves by `tabNK_lend_comap`, every raise by `tabNK_lend_entry`; the posts
are moved by `hQ`. -/
theorem erwpK_lend_comap {xv : LifeVar} {bnd : Lifetime.Life} (hbnd : LifeCtx.empty.Defines bnd)
    {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) (l : Loc) (Fam : Nat → Val → SPropS Loc Val α)
    {F : CTy} (hF : F.SuspendC xv bnd) {Q Q' : KW → PostN}
    (hQ : ∀ x y k ls v ρ, KW.PostK (x.lend l α Fam) y → Q y k ls v ρ →
      ∃ y', KW.PostK x y' ∧ Q' y' k ls v ρ) :
    ∀ n x ls e ρ,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN F (δ.extend xv α) z)) Q (x.lend l α Fam) n ls e ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun y => (y.lend l α Fam).Θ.view (y.lend l α Fam).c)
        (fun y => opTableK α (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
          (·.lend l α Fam) F (δ.extend xv α) y)) Q' x n ls e ρ := by
  intro n x ls e ρ h
  simp only [← tabNK_vN] at h
  refine erwpK_comap (ℍ := ℍ) (fun z : KW => z.lend l α Fam) (fun _ => True) (fun _ => rfl)
    (fun x _ y k ls v ρ hy hq => hQ x y k ls v ρ hy hq) ?_ n x trivial ls e ρ h
  intro z _ k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁ hΨ₁ h₁
  rcases h₁ with h₁ | ⟨K₁, m, j, w, en, h₁⟩
  · exact Or.inl (tabNK_lend_comap hbnd hLt l Fam F.cdepth F le_rfl hF α z k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁
      (fun y'' k'' hk'' ls'' e'' ρ'' h => hΨ₁ y'' k'' hk'' trivial ls'' e'' ρ'' h) h₁)
  · obtain ⟨⟨hE, hK, hTe, ha⟩, hr⟩ := pure_sep_iff.mp h₁
    obtain ⟨en', h', -, hab, hPA'⟩ := tabNK_lend_entry hLt l Fam hF hTe
    obtain ⟨τ₁, τ₂, hτ, ⟨hPA, hnA⟩, hn⟩ := hr
    exact Or.inr ⟨K₁, m, j, w, en', pure_sep_mk ⟨hE, hK, h', hab ▸ ha⟩
      ⟨τ₁, τ₂, hτ, ⟨hPA' _ _ _ _ hPA, hnA⟩, hn⟩⟩

/-- **The Mut Frame at `cN`'s tables, its callback a run at its own table from the lend's world**
(`erwpK_M_frameCR_tab` at `vN`, its callback moved by `erwpK_lend_comap`): the callback is read as
a thunk of `cN` reads it, at `tabN F δ′` from `x.lend ℓ α F`, its posts `Qc`; the lender runs at
its twin `tabRK` at `vN`, ending at the lend's claim. -/
theorem erwpK_M_frameCR_cN {xv : LifeVar} {bnd : Lifetime.Life} (hbnd : LifeCtx.empty.Defines bnd)
    {α : Life} {δ : LSub} (hLt : LtLife δ bnd α) {l : Loc} {Fam : Nat → Val → SPropS Loc Val α}
    (hFam : DownFam α Fam) {F : CTy} (hF : F.SuspendC xv bnd) {Q Qc : KW → PostN}
    (hQ : ∀ x k ls v ρ, Qc (x.lend l α Fam) k ls v ρ → MFPost l α Fam (Q x) k ls v ρ) :
    ∀ n j, n ≤ j → ∀ (x : KW), x.Θ.FoldInv α → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes)
      (houtP : ρP.InStratum α), ρb.InStratum (↓α) → ∀ (P : Val → SPropS Loc Val α),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (Fam j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf α v ρP houtP P hwit)) BM →
        erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
          (fun z => opTableK z.lo (tabN F (δ.extend xv α) z)) Qc (x.lend l α Fam) n ls e BM) →
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun y => opTableRK y.lo (tabRK (ℍ := ℍ) (claimR l α Fam)
          (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F δ y) (claimR l α Fam)) Q x n ls e ρ := by
  intro n j hnj x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hcl hcρ hcb
  refine erwpK_M_frameCR_tab (ℍ := ℍ) valRelOK_vN (V := KW.PostK) (Φ := fun z => z.Θ.view z.c)
    hLt hFam hF (Q := Q) n j hnj x hx ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hcl hcρ
    (fun BM hBM => ?_)
  have hΦ : (fun y : KW => (y.Θ.view y.c).set l α Fam) =
      fun y : KW => (y.lend l α Fam).Θ.view (y.lend l α Fam).c :=
    funext fun y => (KW.lend_view y l α Fam).symm
  rw [hΦ]
  refine erwpK_lend_comap hbnd hLt l Fam hF (Q := Qc) (Q' := fun y => MFPost l α Fam (Q y))
    (fun x' y k ls v ρ hy hq => ⟨x', rfl, ?_⟩) n x ls e BM (hcb BM hBM)
  have hy' : y = x'.lend l α Fam := hy
  subst hy'
  exact hQ x' k ls v ρ hq

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
