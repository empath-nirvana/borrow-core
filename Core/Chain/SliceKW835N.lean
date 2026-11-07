import Core.Chain.WithloadSKW835N
import Core.Chain.FamOpsKW835N

/-!
# `slice_borrow_mut` at a suspending row, at the typed world  `[spec §62]`

`FamCancel836N`'s `sliceBorrowMS_compat` at `SemJN`, step for step: the `n`-cell Mut Frame at the
typed tables (`erwpK_M_frameListKWP`), its lends below the bound (`KW.LendMapB`); the callback, a
thunk of `cN` at the innermost lend's world, read at the lender's worlds under the frames' lends
(`erwpK_lendMapB_comap`); the lender at the floor no higher than the cells' stratum (`erwpK_flr`,
`LendInv`); the composite claim, the array, consistent with the view of the world it is raised at
(`erwpK_claimXK`), consumed with `d` (`erwpK_ubindClaimRWK`, `fin_claimArr`).
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
open BoCa.BoLo (Heap Kont Head ubindE performE raiseE cancelVal opPayload)

/-! ### Lends below the bound -/

/-- **The world maps of lends below a bound**: the identity, or a lend at `α ⊏ @bnd`, `α ≤ c`,
after one. -/
inductive _root_.BoCa.Fig16.LogRel.Core.Chain.SI.KW.LendMapB (δ : LSub) (bnd : Lifetime.Life)
    (c : Life) : (KW → KW) → Prop
  | id : KW.LendMapB δ bnd c fun y => y
  | lend {g : KW → KW} (h : KW.LendMapB δ bnd c g) (l : Loc) (α : Life) (hLt : LtLife δ bnd α)
      (hc : α ≤ c) (F : Nat → Val → SPropS Loc Val α) :
      KW.LendMapB δ bnd c fun y => (g y).lend l α F

/-- The floor after lends no higher than `c` is no higher than `c`. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Chain.SI.KW.LendMapB.lo_le {δ : LSub} {bnd : Lifetime.Life} {c : Life} {g : KW → KW}
    (hg : KW.LendMapB δ bnd c g) {y : KW} (hy : y.lo ≤ c) : (g y).lo ≤ c := by
  cases hg with
  | id => exact hy
  | lend _ l α _ hc F => exact hc

/-- **A type outliving the bound reads alike across lends below it** (`vN_add_eq`, along the
lends). -/
theorem vN_lendMapB_eq {A : VTy} {bnd : Lifetime.Life} (hO : VOutlives LifeCtx.empty bnd A)
    {δ : LSub} {c : Life} {g : KW → KW} (hg : KW.LendMapB δ bnd c g) (y : KW) :
    vN (ℍ := ℍ) A δ (g y).Θ = vN (ℍ := ℍ) A δ y.Θ := by
  induction hg with
  | id => rfl
  | lend _ l α hLt _ F ih =>
      show vN (ℍ := ℍ) A δ (LocTy.add _ l α F) = _
      rw [vN_add_eq hO δ hLt _ l F, ih]

/-- **An entry of the callback's own table at the lends' world is the lender's twin's under the
lends, at the same key**: same qualifier and abortiveness, the payload moved from the lends'
world to the index world (`vN_extend_of_not_free`, `vN_lendMapB_eq`). -/
theorem tabNK_lendMapB_entry {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub}
    {c : Life} {g : KW → KW} (hg : KW.LendMapB δ bnd c g) (R₀ : Nat → WProp) {F : CTy}
    (hF : F.SuspendC xv bnd) {y : KW} {n i : UInt32} {en : OpEntK KW}
    (h : tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F (δ.extend xv α)
      (g y) n i = some en) :
    ∃ en', tabRK (ℍ := ℍ) R₀ (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) g F δ y n i = some en' ∧
      en'.q = en.q ∧ en'.abort = en.abort ∧ ∀ k ls v ρ, en.PA k ls v ρ → en'.PA k ls v ρ := by
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNK F h
  obtain ⟨-, hA, -, hOA, -, -⟩ := layer_suspend F hF hL
  refine ⟨_, hR R₀ g δ y, rfl, rfl, fun k ls v ρ hp => ?_⟩
  have hp' : vN (ℍ := ℍ) A (δ.extend xv α) (g y).Θ k v ρ := hp
  rw [vN_extend_of_not_free hA, vN_lendMapB_eq hOA hg y] at hp'
  exact hp'

/-- The error a cancel raise carries, from the callback's tables to the lender's twin under the
lends. -/
theorem errOkK_lendMapB {xv : LifeVar} {bnd : Lifetime.Life} {α : Life} {δ : LSub}
    {c : Life} {g : KW → KW} (hg : KW.LendMapB δ bnd c g) (R₀ : Nat → WProp) {F : CTy}
    (hF : F.SuspendC xv bnd) (y : KW) {k : Nat} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes},
      errOkK (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F (δ.extend xv α)
        (g y)) k ls err ρ →
      errOkK (tabRK (ℍ := ℍ) R₀ (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) g F δ y) k ls err ρ
  | none, _, h => h
  | some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      obtain ⟨en', h', -, hab, hPA'⟩ := tabNK_lendMapB_entry hg R₀ hF hTe
      exact ⟨m, j, w, en', pure_sep_mk ⟨hE, h', hab ▸ ha⟩ ⟨hPA' _ _ _ _ hPA, hn⟩⟩

/-- **The callback's table step under the lends** (`erwpK_comap`'s `hT` at a `KW.LendMapB` map
`g`, `tabNK_lend_comap` along several lends): a stop at the callback's own table at the lends'
world is a stop at the lender's twin under the lends, its claim `R₀` owning nothing, at the worlds an
invariant `J` kept along `KW.Owed` at floors no higher than the world's holds at. The payload and
the answer move between the lends' world and the index world (`vN_lendMapB_eq`); the answer's view
by `consistentX_of_outlivesN`; the order is the same; each cancel obligation moves by
`erwpK_comap` again, by induction on how deep cancel rows nest. -/
theorem tabNK_lendMapB_comap {xv : LifeVar} {bnd : Lifetime.Life}
    (hbnd : LifeCtx.empty.Defines bnd) {α : Life} {δ : LSub} {c : Life} {g : KW → KW}
    (hg : KW.LendMapB δ bnd c g) (R₀ : Nat → WProp) (hR₀ : ∀ k, R₀ k PMap.empty)
    {J : KW → Prop} (hJ : ∀ z : KW, J z → ∀ f, f ≤ z.lo → ∀ z' ρ, z.Owed f z' ρ → J z') :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC xv bnd →
      ∀ (y : KW), J (g y) → ∀ k ls t (Ψ Ψ' : ContK KW) ρ,
        (∀ y' k', k' < k → J (g y') → ∀ ls e ρ, Ψ (g y') k' ls e ρ → Ψ' y' k' ls e ρ) →
        performStopK (g y).lo (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F
          (δ.extend xv α) (g y)) k ls t Ψ ρ →
        performStopK (g y).lo (tabRK (ℍ := ℍ) R₀ (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) g F
          δ y) k ls t Ψ' ρ := by
  intro d
  induction d with
  | zero =>
      intro F hd hF y _ k ls t Ψ Ψ' ρ _ h
      obtain ⟨K, n, i, v, en, h⟩ := h
      obtain ⟨⟨-, -, h₃, -⟩, -⟩ := pure_sep_iff.mp h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupNK F h₃
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hF y hJy k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupNK F h₃
  obtain ⟨-, hnA, hnB, hOA, hOB, hfinS⟩ := layer_suspend F hF hL
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  refine ⟨K, n, i, v, _, pure_sep_mk ⟨h₁, h₂, hR R₀ g δ y, h₄⟩
    ⟨ρa, ρk, hc, ?_, hu, f, hf, fun y' hy' ls' he => ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_,
      fun hq P hP => ?_⟩⟩⟩
  · have hp : vN (ℍ := ℍ) A (δ.extend xv α) (g y).Θ k v ρa := hA
    rw [vN_extend_of_not_free hnA, vN_lendMapB_eq hOA hg y] at hp
    exact hp
  · have hB' : vN (ℍ := ℍ) B δ y'.Θ k' w σ₁ := hB.1
    have hBs : vN (ℍ := ℍ) B (δ.extend xv α) (g y').Θ k' w σ₁ := by
      rw [vN_extend_of_not_free hnB, vN_lendMapB_eq hOB hg y']; exact hB'
    exact hΨ y' k' hk' (hJ (g y) hJy f hf (g y') ρk hy') _ _ _
      ((hcont (g y') hy' ls' he).1 k' hk' w σ₁ σ₂ ⟨hBs, consistentX_of_outlivesN hbnd hOB hBs _⟩
        hcσ)
  · simp only [entNK] at hP hq
    by_cases hcap : capB q B = true
    · rw [if_pos hcap] at hP
      by_cases htop : fin = .top
      · subst htop; simp [finRK] at hP
      rw [finRK_eq _ _ _ htop] at hP
      cases Option.some.inj hP
      have hfin := hfinS hcap
      have hs := (hcont (g y') hy' ls' he).2 hq _
        (by simp only [entNK, if_pos hcap]; exact finNK_eq _ _ htop _)
      refine erwpK_comap (ℍ := ℍ) g (fun z => J (g z))
        (fun _ => rfl) (fun _ _ _ _ _ _ _ _ hq => hq.elim) ?_ k y'
        (hJ (g y) hJy f hf (g y') ρk hy') ls' _ ρk hs
      intro z hz k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁ hΨ₁ h₁
      rcases h₁ with h₁ | ⟨K₁, err, h₁⟩
      · exact Or.inl (ih fin hfd hfin z hz k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁
          (fun y'' k'' hk'' hJ'' ls'' e'' ρ'' h => hΨ₁ y'' k'' hk'' hJ'' ls'' e'' ρ'' h) h₁)
      · obtain ⟨hK, hr⟩ := pure_sep_iff.mp h₁
        obtain ⟨τ₁, τ₂, hτ, he₁, hn⟩ := hr
        exact Or.inr ⟨K₁, err, pure_sep_mk hK ⟨ρ₁, PMap.empty, ResU.comp_empty_right ρ₁,
          ⟨τ₁, τ₂, hτ, errOkK_lendMapB hg R₀ hfin z he₁, hn⟩, hR₀ k₁⟩⟩
    · rw [if_neg hcap] at hP; cases hP

/-- **The callback's run under the lends** (`erwpK_comap` at a `KW.LendMapB` map `g`): the
callback's run at its own table, from the lends' world, is its run indexed by the lender's worlds,
at the lender's twin under the lends, its claim `R₀` owning nothing, its location family the lends'
world's view. Every stop moves by `tabNK_lendMapB_comap`, every raise by `tabNK_lendMapB_entry`;
the posts are moved by `hQ`. -/
theorem erwpK_lendMapB_comap {xv : LifeVar} {bnd : Lifetime.Life}
    (hbnd : LifeCtx.empty.Defines bnd) {α : Life} {δ : LSub} {c : Life} {g : KW → KW}
    (hg : KW.LendMapB δ bnd c g) (R₀ : Nat → WProp) (hR₀ : ∀ k, R₀ k PMap.empty)
    {J : KW → Prop} (hJ : ∀ z : KW, J z → ∀ f, f ≤ z.lo → ∀ z' ρ, z.Owed f z' ρ → J z')
    {F : CTy} (hF : F.SuspendC xv bnd) {Q Q' : KW → PostN}
    (hQ : ∀ x, J (g x) → ∀ y k ls v ρ, KW.PostK (g x) y → Q y k ls v ρ →
      ∃ y', KW.PostK x y' ∧ Q' y' k ls v ρ) :
    ∀ n x, J (g x) → ∀ ls e ρ,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) id F
          (δ.extend xv α) z)) Q (g x) n ls e ρ →
      erwpK (ℍ := ℍ) KW.PostK (fun y => (g y).Θ.view (g y).c)
        (fun y => opTableRK (g y).lo (tabRK (ℍ := ℍ) R₀
          (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) g F δ y) R₀) Q' x n ls e ρ := by
  intro n x hx ls e ρ h
  refine erwpK_comap (ℍ := ℍ) g (fun z => J (g z)) (fun _ => rfl) hQ ?_ n x hx ls e ρ h
  intro z hz k₁ ls₁ t₁ Ψ₁ Ψ₁' ρ₁ hΨ₁ h₁
  rcases h₁ with h₁ | ⟨K₁, m, j, w, en, h₁⟩
  · exact Or.inl (tabNK_lendMapB_comap hbnd hg R₀ hR₀ hJ F.cdepth F le_rfl hF z hz k₁ ls₁ t₁ Ψ₁
      Ψ₁' ρ₁ hΨ₁ h₁)
  · obtain ⟨⟨hE, hK, hTe, ha⟩, hr⟩ := pure_sep_iff.mp h₁
    obtain ⟨en', h', -, hab, hPA'⟩ := tabNK_lendMapB_entry hg R₀ hF hTe
    obtain ⟨τ₁, τ₂, hτ, ⟨hPA, hnA⟩, hn⟩ := hr
    exact Or.inr ⟨K₁, m, j, w, en', pure_sep_mk ⟨hE, hK, h', hab ▸ ha⟩
      ⟨ρ₁, PMap.empty, ResU.comp_empty_right ρ₁, ⟨τ₁, τ₂, hτ, ⟨hPA' _ _ _ _ hPA, hnA⟩, hn⟩,
        hR₀ k₁⟩⟩

/-! ### `slice_borrow_mut` at a suspending row -/

/-- **The finaliser consumes the source array, at `SemJN`** (`fin_claimArr₀`): `d`'s judgment at
`Array A ⊸ 1`, applied to the array owned again. -/
theorem fin_claimArr {A : VTy} {d : Expr} (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.array A) .unit))) {δ : LSub}
    {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {a : Val} {k : Nat} {ls : List SRec}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.array A) δ Θ k a ρ) (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) (Θ.view c) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val (DFa d a)) (.val .unit)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  obtain ⟨l, cn, rfl, -, -⟩ := id h
  refine Hardest791.rwp_det'' (Q := fun _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) hΦ
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.app d (.val (Val.arr l cn)))) =
      (Kont.appL .hole (Val.arr l cn)).plug d := by
    simp [Kont.plug, Expr.subst, subst_closedAt d (s := _) hdc (Nat.zero_le _), subst_arr]
  rw [e]
  refine rwp_bind hΦ _ ?_
  have hd0 := hd δ [] Θ c k ls PMap.empty (models_empty_any _) hΘ (consistentX_empty c) trivial rfl
  rw [show substAll [] d = d from psub_closedAt d [] hdc (Nat.zero_le 0)] at hd0
  have hfr := rwp_frame (fun _ τ => τ = ρ) (fun _ _ _ _ h => h) (compS_empty_left ρ)
    (rwp_of_erwp_empty (erwp_of_cN_ret hd0)) rfl
  refine rwp_mono_le (fun k' hk' ls' v τ hv => ?_) (rwp_consistentXV hfr hc)
  obtain ⟨⟨τ₁, τ₂, hcτ, hP, rfl⟩, hcτ', hvτ⟩ := hv
  have := hP Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_left hcτ hcτ' hvτ) ls'
    c k' le_rfl (Val.arr l cn) τ₂ τ hcτ (vN_le hk' h) hcτ'
  exact rwp_of_erwp_empty (erwp_of_cN_ret this)

/-- **`slice_borrow_mut` at a suspending row is a value of `!` its type, at `SemJN`**
(`sliceBorrowMS_compat₀` at the typed world): `withborU d` at
`Array A ⊸ (∀'x ⊏ @bnd. [Mut 'x A] ⊸ F_Σ(['x] B)) ⊸ F_Σ(Array A ⊗ B)`, `Σ` a
`Row.Suspend x bnd` row, cleanup that performs included.

`withbor2S_compat`'s structure with the `n`-cell frame (`erwpK_M_frameListKWP`, its lends below
the bound, `KW.LendMapB`): the payloads' stratum and the result's from the side conditions by 6.60
at `↓@bδ` (`vN_outlivesLe`); the lender at the floor no higher than both (`erwpK_flr_tabN`), its
worlds `LendInv`; the callback, at the innermost lifetime `α`, receives the family `[Mut 'x A]`
(`vN_mutLeaf` at each leaf), runs as a thunk of `cN` at the lends' world and is read at the
lender's worlds (`erwpK_lendMapB_comap`); the composite claim, the cells owned again at `Θ`
(`claimL`), is the array at every world `LendInv` holds at (`vN_above`); it is consistent with the
view of the world it is raised at (`erwpK_claimXK`), and the finaliser frame
`then b. (a, b) unwind d a` consumes it with `d` (`erwpK_ubindClaimRWK`, `fin_claimArr`).

Premises as `sliceBorrowMS_compat₀`'s; `hd` is `d`'s judgment at `SemJN`. -/
theorem sliceBorrowMS_compat {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy} {S : Row}
    {d : Expr} (hbnd : LifeCtx.empty.Defines bnd)
    (hOA : ∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b A)
    (hOB : ∃ b, LifeCtx.empty.Defines b ∧ VOutlivesLe LifeCtx.empty b B)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Suspend x bnd) (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.array A) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (sliceBorrowMUTy x bnd A B S)) δ Θ₀ n (withborUV d) PMap.empty := by
  refine ⟨rfl, fun Θ _ hΘ c₁ _ ls => ?_⟩
  intro c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  intro c k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l, cn, rfl, hn, hs⟩ := vN_le hk' hu
  rw [cN_effOf]
  intro lo
  refine erwpK_of_valid fun hv'' => ?_
  set Fo := CTy.effOf S (.tensor (.array A) B) with hFo
  set Qo : KW → PostN := fun z k _ v ρ => vN (ℍ := ℍ) (.tensor (.array A) B) δ z.Θ k v ρ
    with hQo
  have hQoD : ∀ z, (Qo z).Down := fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  -- the side conditions: the payloads' and the result's strata (6.60 at `↓@bδ`)
  obtain ⟨a, hdefa, hOa⟩ := hOA
  obtain ⟨βP, hβP⟩ := hdefa δ (models_empty_any _)
  have hunif : ∀ Θ j w r, vN (ℍ := ℍ) A δ Θ j w r → r.InStratum (↓βP) :=
    vN_outlivesLe (models_empty_any _) hβP (Life.down_sqsubset βP) hOa
  obtain ⟨b, hdefb, hOb⟩ := hOB
  obtain ⟨βB, hβB⟩ := hdefb δ (models_empty_any _)
  have hBs : ∀ Θ j w r, vN (ℍ := ℍ) B δ Θ j w r → r.InStratum (↓βB) :=
    vN_outlivesLe (models_empty_any _) hβB (Life.down_sqsubset βB) hOb
  obtain ⟨mb, hmb⟩ := hbnd δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  have hAδ : ∀ α, vN (ℍ := ℍ) A (δ.extend x α) = vN (ℍ := ℍ) A δ :=
    fun α => vN_extend_of_not_free hA δ α
  have hBδ : ∀ α, vN (ℍ := ℍ) B (δ.extend x α) = vN (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free hB δ α
  have hFS : Fo.SuspendC x bnd := suspendC_effOf hS _
  set I := rangeLocs l cn.toNat with hI
  -- the lender's floor: no higher than the cells' and the result's strata
  set fa : Life := (↓βP) ⊓ (↓βB) with hfa
  have hfaP : fa ≤ ↓βP := inf_le_left
  have hfaB : fa ≤ ↓βB := inf_le_right
  -- a value at `Θ` in `Res_fa` is one at every world `LendInv Θ fa` holds at
  have hmove : ∀ (T : VTy) (z : KW), LendInv Θ fa z → ∀ k (v : Val) (ρ : WRes), ρ.InStratum fa →
      vN (ℍ := ℍ) T δ Θ k v ρ → vN (ℍ := ℍ) T δ z.Θ k v ρ := by
    intro T z hz k v ρ hρ h
    have h' := (vN_above T δ Θ hρ).mpr h
    rw [← hz.2.2] at h'
    exact (vN_above T δ z.Θ hρ).mp h'
  -- the cells owned again at `Θ` are cells owned again at every such world
  have hcells : ∀ (z : KW), LendInv Θ fa z → ∀ k ρ,
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ →
      ρ.InStratum fa ∧ sepList (fun m => vN (ℍ := ℍ) (.ref A) δ z.Θ k (Val.loc m)) I ρ := by
    intro z hz k ρ h
    have hρ : ρ.InStratum fa := sepList_closed (ResU.inStratum_empty fa)
      (fun _ _ _ hc a b => inStratum_compS hc a b)
      (fun m τ hm => ownLeafN_inStratum hfaP hunif hm) h
    exact ⟨hρ, sepList_mono_down (R := fun τ => τ.InStratum fa)
      (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
        ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
      (fun m τ hτ hm => hmove _ z hz k _ τ hτ hm) hρ h⟩
  set x₁ : KW := KW.flr fa ⟨Θ, c, lo⟩ with hx₁
  have hx₁I : LendInv Θ fa x₁ := ⟨hΘ, min_le_right _ _, rfl⟩
  refine erwpK_flr_tabN fa (Q := Qo) (fun _ _ _ _ _ h => h) k' ⟨Θ, c, lo⟩ ls _ ρ'' ?_
  have hΦ₁ : (x₁.Θ.view x₁.c).Down := LocTy.view_down hΘ.1 c
  have hTd₁ : (opTableK x₁.lo (tabN (ℍ := ℍ) Fo δ x₁)).Down :=
    opTableK_downI (tabN_downI_OK Fo δ x₁)
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQoD
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl (.appL .hole f)) ?_
  refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQoD
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.arr l cn))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app (Expr.var 1))))) =
      ubindE (.pair (NFa (Val.arr l cn)) (DFa d (Val.arr l cn)))
        (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) := by
    simp [Kont.plug, Expr.subst, thenE, ubindE, NFa, DFa, Val.pair,
      Val.lam, Expr.val, Val.prim, shift_arr, subst_arr,
      subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the frames, the composite claim the array
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => vN (ℍ := ℍ) B δ Θ k v ρ
  have hM := erwpK_M_frameListKWP (ℍ := ℍ) (V := KW.PostK) hunif hmb hFS Ψ
    (fun Θ k _ v ρ hw => hBs Θ k v ρ hw)
    (fun Θ l₀ α F k _ v ρ hρ hw => vN_local B δ Θ l₀ α F k v ρ hρ hw)
    (.app (.app (.val f) (.val .unit)) (.val (Val.arr l cn))) ls x₁ (KW.LendMapB δ bnd (↓βB))
    (fun g hg ℓ α Fm hLt hαc => KW.LendMapB.lend hg ℓ α hLt hαc Fm) I (fun y => y)
    KW.LendMapB.id
    k' ρu ρf ρ'' (mb ⊓ βf) hΘ hcon hc' (by rw [← sepRange_eq_sepList]; exact hs)
    (fun α hα => ⟨hβf.mono (le_of_lt (lt_of_lt_of_le hα inf_le_right)), ?_⟩)
  · -- the claim consistent, the finaliser frame consuming it at the world it is raised at
    have hM' := erwpK_claimXK k' x₁ ls _ ρ'' hcon hM
    have hfin := erwpK_ubindClaimRWK (ℍ := ℍ) valRelOK_vN
      (RW := claimXK (claimL (ℍ := ℍ) A δ Θ I)) (Inv := LendInv Θ fa)
      (fun z hz => LocTy.view_down hz.1.1 z.c) lendInv_owed (F := Fo) (δ := δ)
      (tabN_suspend_raise hS _ δ) (NFa (Val.arr l cn)) (DFa d (Val.arr l cn)) ?_ hQoD ?_ k' x₁
      hx₁I ls _ ρ'' hM'
    · simpa only [tabNK_vN] using hfin
    · rintro z hz j ls' ρ ⟨hR, hcR⟩
      obtain ⟨-, hR'⟩ := hcells z hz j ρ hR
      exact fin_claimArr hdc hd hz.1 ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact hR'⟩
        hcR
    · intro z hz j ls' bv ρ hq
      obtain ⟨ρ₁, ρ₂, hc12, ho, hb⟩ := hq
      have hTdz : (opTableK z.lo (tabNK (ℍ := ℍ) (fun A δ Θ k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
          id Fo δ z)).Down := opTableK_downI (tabNK_downI valRelOK_vN id Fo δ z)
      refine erwpK_det (Φ := fun z : KW => z.Θ.view z.c) (x := z) (LocTy.view_down hz.1.1 z.c)
        hTdz hQoD (fun μ => step1Only_plug (Head.beta μ _ bv) rfl .hole) ?_
      simp [Kont.plug, Expr.subst]
      obtain ⟨-, ho'⟩ := hcells z hz j ρ₁ ho
      have hb' : vN (ℍ := ℍ) B δ z.Θ j bv ρ₂ :=
        hmove B z hz j bv ρ₂ ((hBs Θ j bv ρ₂ hb).mono hfaB) hb
      exact erwpK_val (KW.postK_refl z) (v := Val.pair (Val.arr l cn) bv)
        ⟨Val.arr l cn, bv, ρ₁, ρ₂, rfl, hc12,
          ⟨l, cn, rfl, hn, by rw [sepRange_eq_sepList]; exact ho'⟩, hb'⟩
  -- the callback, at the frames' world and view, from the leaves at `α`
  intro g' hg' hE hOK'' ρm ρ₃ hml hcomp hc''
  refine erwpK_of_valid fun hv₃ => ?_
  have hLt : LtLife δ bnd α := ⟨mb, hmb, lt_of_lt_of_le hα inf_le_left⟩
  have hcf : ConsistentX (g' x₁).c ρf := consistentX_left hcomp hc'' hv₃
  have hfam : vN (ℍ := ℍ) (.sliceMut (.var x) A) (δ.extend x α) (g' x₁).Θ k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn, by
      rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_mutLeaf hA h) hml⟩
  have h1 := (hf (g' x₁).Θ (hE.extR ρf) hOK'' (g' x₁).c hcf ls) α hLt
  have h2 := h1 (g' x₁).c k' le_rfl (Val.arr l cn) _ ρ₃ hcomp hfam hc''
  rw [cN_effOf] at h2
  have h3 := h2 (g' x₁).lo
  simp only [tabN_effOf_base S (.box (.var x) B) (.tensor (.array A) B), ← tabNK_vN] at h3
  -- the callback's worlds: the floor no higher than the innermost lend's, the location typing
  -- above it the innermost lend world's
  set a₀ := (g' x₁).lo with ha₀
  have ha₀B : a₀ ≤ ↓βB := hg'.lo_le (le_trans (min_le_right _ _) hfaB)
  set J : KW → Prop := fun z => z.lo ≤ a₀ ∧ z.Θ.above a₀ = (g' x₁).Θ.above a₀ with hJdef
  have hJ : ∀ z : KW, J z → ∀ f, f ≤ z.lo → ∀ z' ρ, z.Owed f z' ρ → J z' := fun z hz f hf z' ρ hz' =>
    ⟨le_trans hz'.2.2.2.1 hz.1, (hz'.1.above_eq (le_trans hf hz.1)).trans hz.2⟩
  exact erwpK_lendMapB_comap (ℍ := ℍ) hbnd hg' (claimL (ℍ := ℍ) A δ (g' x₁).Θ [])
    (fun _ => ⟨rfl, trivial⟩) hJ hFS (Q := fun z k _ v ρ => vN (ℍ := ℍ) (.box (.var x) B)
      (δ.extend x α) z.Θ k v ρ) (Q' := fun _ => Ψ (g' x₁).Θ)
    (fun x' hx' y k ls v ρ hy hq => ⟨x', KW.postK_refl x', by
      have hy' : y = g' x' := hy
      subst hy'
      obtain ⟨β, hβ, hbB, -⟩ := hq
      rw [interp_ext_self] at hβ
      cases Option.some.inj hβ
      rw [vN_extend_of_not_free hB] at hbB
      have hρ : ρ.InStratum a₀ := (hBs _ k v ρ hbB).mono ha₀B
      show vN (ℍ := ℍ) B δ (g' x₁).Θ k v ρ
      have h₁ := (vN_above B δ (g' x').Θ hρ).mpr hbB
      rw [hx'.2] at h₁
      exact (vN_above B δ (g' x₁).Θ hρ).mp h₁⟩) k' x₁ ⟨le_rfl, rfl⟩ ls _ ρ₃ h3

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
