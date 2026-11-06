import Core.Chain.TabK835N

/-!
# The `n`-cell Mut Frame at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-tables.md` §4. `erwp_M_frameListCRN` and `erwp_M_frameListRN`
(`FamCancel836N.lean`) are one list induction, each step a Mut Frame. `erwpK_M_frameList` is that
induction at `erwpK` over any world index: the run at the world `x`, its location family
`Φ Θ c` and its tables `TbL Θ c I` read at the location typing and the view the frames before it
reached and at the cells not yet lent; each step the frame `hstep` from the table at the inner
world to the table at the outer one, at `x` (`KFrame` with the invariant `· = x`). The lifetime of
each frame is chosen fresh and below the frame's rest, `β`, `β′` and `mb`, as in the originals.

Each original statement is proved again, word for word, from `erwpK_M_frameList` at one world
(`erwp_M_frameListCRN_of_K`, `erwp_M_frameListRN_of_K`): the step is the original's, the frame
(`erwp_M_frameCRR` / `erwp_M_frameRR`) and the claim joined to the inner frames' (`tabR_le`,
`OpTabN.Sub.le`), read at one world by `erwp_eq_erwpK`.
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

variable {ι : Type}

/-- A run at `erwpK` may assume its resource valid (`erwp_of_valid`). -/
theorem erwpK_of_valid {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ResU.Valid ρ → erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ := by
  rw [erwpK_eq]
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin
  have h' := h (ResU.Valid.split hc hT.valid).2
  rw [erwpK_eq] at h'
  exact h' ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun hfin

/-- The post of a family's frames at `Θ`: the cells owned again beside the callback's answer. -/
def listPostN (A : VTy) (δ : LSub) (Ψ : LocTy → PostN) (Θ : LocTy) (I : List Loc) : PostN :=
  fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
    sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂

/-- **One Mut Frame per place, around one expression, at `erwpK`** (`erwp_M_frameListCRN`,
`erwp_M_frameListRN`): the list induction, each frame's step `hstep`. -/
theorem erwpK_M_frameList {V : ι → ι → Prop} {A : VTy} {δ : LSub} {β β' mb : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (Φ : LocTy → (Loc → Option Life) → ι → LocFam)
    (hΦ : ∀ (Θ : LocTy) c (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) y,
      Φ (Θ.add l α F) (setLife c l α) y = (Φ Θ c y).set l α F)
    (TbL : LocTy → (Loc → Option Life) → List Loc → ι → TableK ι)
    (hTbL : ∀ Θ c I y, (TbL Θ c I y).Local)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) (x : ι)
    (hstep : ∀ (Θ : LocTy) (c : Loc → Option Life) (l : Loc) (α : Life) (I : List Loc),
      Θ.Fresh α → α < mb → α ≤ β →
      KFrame (ℍ := ℍ) V (Φ Θ c) (· = x) l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
        (TbL (Θ.add l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)) (setLife c l α) I)
        (TbL Θ c (l :: I))
        (fun _ => MFPost l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
          (listPostN (ℍ := ℍ) A δ Ψ Θ (l :: I)))
        (fun _ => listPostN (ℍ := ℍ) A δ Ψ Θ (l :: I))) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' →
          erwpK (ℍ := ℍ) V (Φ Θ' c') (TbL Θ' c' []) (fun _ => Ψ Θ') x n ls e ρ') →
      erwpK (ℍ := ℍ) V (Φ Θ c) (TbL Θ c I) (fun _ => listPostN (ℍ := ℍ) A δ Ψ Θ I) x n ls e ρ
  | [], Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ] at hc ⊢
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 Θ c (LocTy.extA_refl Θ) hΘ PMap.empty ρH
        ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hc
      exact erwpK_mono (fun _ _ h => h) (fun _ k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩)
        (fun y k ls t Ψ Ψ' ρ hΨ h => hTbL Θ c [] y k ls t Ψ Ψ' ρ hΨ h) n x ls e ρH h
  | ℓ :: I, Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      obtain ⟨Fr, hFr, hρ⟩ := compS_reassoc hc0 hcρ
      refine erwpK_of_valid fun hv => ?_
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hko : (CellU.ownOf (Loc := Loc) u).kind ≠ Kind.imm := by simp
      have hown : ρ0.get ℓ = some (CellU.ownOf u) :=
        (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
      have hcF : ConsistentX c Fr := consistentX_right hρ hc hv
      have hcσ : ConsistentX c σ := consistentX_right hcl (consistentX_left hρ hc hv) hvρ0
      -- the outer frame's lifetime: fresh, below the frame's rest, `β`, `β′` and `mb`
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum Fr
      obtain ⟨α₁, hα₁le, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(βF ⊓ β ⊓ β' ⊓ mb))
      have hα₁lt : α₁ < βF ⊓ β ⊓ β' ⊓ mb := lt_of_le_of_lt hα₁le (Life.down_sqsubset _)
      have hα₁F : α₁ ≤ βF := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
      have hα₁β : α₁ ≤ β := hα₁lt.le.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
      have hα₁β' : α₁ ≤ β' := hα₁lt.le.trans (inf_le_left.trans inf_le_right)
      have hα₁mb : α₁ < mb := lt_of_lt_of_le hα₁lt inf_le_right
      set P : CPredL := fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P Θ with hFm
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have houtb : Fr.InStratum (↓α₁) := hβF.mono ((Life.down_sqsubset α₁).le.trans hα₁F)
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above A δ Θ houtP).mpr hu
      have hFmD : DownFam α₁ Fm := vN_fam_down A δ α₁ Θ
      set Θ₁ := Θ.add ℓ α₁ Fm with hΘ₁
      set c₁ := setLife c ℓ α₁ with hc₁
      have hOK₁ : Θ₁.OK := by
        obtain ⟨N, hN⟩ := hΘ.2
        exact ⟨LocTy.down_add hΘ.1 ℓ hFmD, ⟨min N (↓α₁), LocTy.fresh_add hN (min_le_left _ _)
          (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α₁)) ℓ Fm⟩⟩
      have hE₁ : Θ.ExtA Θ₁ := LocTy.extA_add hfr ℓ Fm
      have hcF₁ : ConsistentX c₁ Fr :=
        consistentX_setLife hcF (exS_none_of_part hρ hv hown hko) α₁
      have hcσ₁ : ConsistentX c₁ σ :=
        consistentX_setLife hcσ (exS_none_of_part hcl hvρ0 (ResU.single_get_self _ _) hko) α₁
      refine hstep Θ c ℓ α₁ I hfr hα₁mb hα₁β n n le_rfl x rfl ls e u σ ρ0 Fr ρ houtP houtb
        (Fm n) (fun _ _ h => h) hwit hcl hρ (fun BM hBM => ?_)
      have hΦ₁ : (fun y => (Φ Θ c y).set ℓ α₁ Fm) = Φ Θ₁ c₁ :=
        funext fun y => (hΦ Θ c ℓ α₁ Fm y).symm
      rw [hΦ₁]
      -- `BM = ρr ● R`, `R = ρH ● cell`
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hFr hBM
      have hcBM : ConsistentX c₁ BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hc₁, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA (.ref A) δ hE₁ n _ τ h) hrest
      refine erwpK_mono (fun _ _ h => h) (fun _ k ls' v ρ' h => ?_)
        (fun y k ls t Ψ Ψ' ρ hΨ h => hTbL Θ₁ c₁ I y k ls t Ψ Ψ' ρ hΨ h) n x ls e BM
        (erwpK_M_frameList hunif Φ hΦ TbL hTbL Ψ hΨs hΨl e ls x hstep I Θ₁ c₁ n ρr R BM
          (βR ⊓ α₁ ⊓ γ) hOK₁ hcBM hBMR hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt
            (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN (ℍ := ℍ) A δ Θ k w σ' := (vN_above A δ Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro Θ' c' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN (ℍ := ℍ) A δ α₂ Θ' n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 Θ' c' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

/-! ### The original statements at one world -/

/-- `erwp_M_frameListCRN` from `erwpK_M_frameList` at one world: each step the frame
`erwp_M_frameCRR` at the lender's twin, its claim joined to the inner frames' (`tabR_le`). -/
theorem erwp_M_frameListCRN_of_K {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    {x : LifeVar} {bnd : Lifetime.Life} (hbnd : LifeCtx.empty.Defines bnd) {mb : Life}
    (hmb : bnd.interp δ = some mb) {F : CTy} (hF : F.SuspendC x bnd)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' →
          erwp (ℍ := ℍ) (Θ'.view c')
            (opTableR (tabR (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ' []) F δ Θ' c')
              (claimL (ℍ := ℍ) A δ Θ' [])) (Ψ Θ') n ls e ρ') →
      erwp (ℍ := ℍ) (Θ.view c)
        (opTableR (tabR (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ I) F δ Θ c) (claimL (ℍ := ℍ) A δ Θ I))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ := by
  intro I Θ c n ρo ρH ρ γ hΘ hc hcρ ho hH
  have hstep : ∀ (Θ : LocTy) (c : Loc → Option Life) (l : Loc) (α : Life) (I : List Loc),
      Θ.Fresh α → α < mb → α ≤ β →
      KFrame (ℍ := ℍ) (fun _ _ => True) (fun _ : Unit => Θ.view c) (· = ()) l α
        (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
        (fun _ => liftTb (opTableR (tabR (ℍ := ℍ) (claimL (ℍ := ℍ) A δ
          (Θ.add l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)) I) F δ
          (Θ.add l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)) (setLife c l α))
          (claimL (ℍ := ℍ) A δ
            (Θ.add l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)) I)))
        (fun _ => liftTb (opTableR (tabR (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ (l :: I)) F δ Θ c)
          (claimL (ℍ := ℍ) A δ Θ (l :: I))))
        (fun _ => MFPost l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
          (listPostN (ℍ := ℍ) A δ Ψ Θ (l :: I)))
        (fun _ => listPostN (ℍ := ℍ) A δ Ψ Θ (l :: I)) := by
    intro Θ c ℓ α₁ I hfr hα₁mb hα₁β n j hjn _ _ ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP
      hcρ hA
    have hLt : LtLife δ bnd α₁ := ⟨mb, hmb, hα₁mb⟩
    set Fm : Nat → Val → SPropS Loc Val α₁ :=
      famL α₁ (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ with hFm
    have hFmD : DownFam α₁ Fm := vN_fam_down A δ α₁ Θ
    set Θ₁ := Θ.add ℓ α₁ Fm with hΘ₁
    set c₁ := setLife c ℓ α₁ with hc₁
    have hRs : ∀ k ρ', claimL (ℍ := ℍ) A δ Θ₁ I k ρ' → ρ'.InStratum α₁ := fun k ρ' h =>
      sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
        (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) h
    have hcl' : ∀ k ρ', (claimR ℓ α₁ Fm k ⋆ claimL (ℍ := ℍ) A δ Θ₁ I k) ρ' →
        claimL (ℍ := ℍ) A δ Θ (ℓ :: I) k ρ' := by
      rintro k ρ' ⟨ρ₁, ρ₂, hc12, ⟨w, σ', hσ', hFσ, hcw⟩, hr⟩
      refine ⟨ρ₁, ρ₂, hc12, ⟨ℓ, w, σ', rfl, hcw, (vN_above A δ Θ hσ').mp hFσ⟩, ?_⟩
      exact sepList_mono_down (R := fun τ => τ.InStratum α₁)
        (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
          ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
        (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) (hRs k ρ₂ hr) hr
    have hM := erwp_M_frameCRR (Φ := Θ.view c) (l := ℓ) (A := α₁) (F := Fm) hFmD
      (tabR_lendOKCR_C hF (claimL (ℍ := ℍ) A δ Θ₁ I) δ hLt Θ₁ c₁)
      (tabR_tabR_twinW hbnd hF (claimL (ℍ := ℍ) A δ Θ₁ I) (fun k => claimR ℓ α₁ Fm k ⋆
        claimL (ℍ := ℍ) A δ Θ₁ I k) δ Θ₁ Θ c₁ c
        (fun A' hO => vN_add_eq_bnd hO δ hLt hfr ℓ Fm))
      (tabR_canR hbnd hfr hLt hFmD hRs F.cdepth F le_rfl hF) hRs
      (Q := listPostN (ℍ := ℍ) A δ Ψ Θ (ℓ :: I))
      n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ
      (fun BM hBM => by simpa only [erwp_eq_erwpK] using hA BM hBM)
    have h := erwp_opTableR_le (tabR_le hcl' δ Θ c F.cdepth F le_rfl) hcl' n ls e ρ hM
    simpa only [erwp_eq_erwpK] using h
  have h := erwpK_M_frameList (ι := Unit) (V := fun _ _ => True) (mb := mb) hunif
    (fun Θ c _ => Θ.view c) (fun Θ c l α F _ => LocTy.view_add Θ c l α F)
    (fun Θ c I _ => liftTb (opTableR (tabR (ℍ := ℍ) (claimL (ℍ := ℍ) A δ Θ I) F δ Θ c)
      (claimL (ℍ := ℍ) A δ Θ I)))
    (fun _ _ _ _ => liftTb_local (opTableR_local _ _)) Ψ hΨs hΨl e ls () hstep I Θ c n ρo ρH ρ
    γ hΘ hc hcρ ho (fun α hα => ⟨(hH α hα).1, fun Θ' c' hE hOK ρm ρ' hm hcomp hc' => by
      simpa only [erwp_eq_erwpK] using (hH α hα).2 Θ' c' hE hOK ρm ρ' hm hcomp hc'⟩)
  rw [erwp_eq_erwpK]
  exact h

/-- `erwp_M_frameListRN` from `erwpK_M_frameList` at one world: each step the frame
`erwp_M_frameRR` at the table `τ`, which reads no fresh key. -/
theorem erwp_M_frameListRN_of_K {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (τ : LocTy → (Loc → Option Life) → OpTabN)
    (hτ : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) c,
      Θ.Fresh α → τ (Θ.add l α F) (setLife c l α) = τ Θ c)
    (hτok : ∀ Θ c α, (τ Θ c).LendOKR α)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' →
          erwp (ℍ := ℍ) (Θ'.view c') (opTableR (τ Θ' c') (claimL (ℍ := ℍ) A δ Θ' []))
            (Ψ Θ') n ls e ρ') →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR (τ Θ c) (claimL (ℍ := ℍ) A δ Θ I))
        (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
          sepList (fun m => vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ := by
  intro I Θ c n ρo ρH ρ γ hΘ hc hcρ ho hH
  have hstep : ∀ (Θ : LocTy) (c : Loc → Option Life) (l : Loc) (α : Life) (I : List Loc),
      Θ.Fresh α → α < β → α ≤ β →
      KFrame (ℍ := ℍ) (fun _ _ => True) (fun _ : Unit => Θ.view c) (· = ()) l α
        (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
        (fun _ => liftTb (opTableR (τ (Θ.add l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ))
          (setLife c l α)) (claimL (ℍ := ℍ) A δ
            (Θ.add l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)) I)))
        (fun _ => liftTb (opTableR (τ Θ c) (claimL (ℍ := ℍ) A δ Θ (l :: I))))
        (fun _ => MFPost l α (famL α (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ)
          (listPostN (ℍ := ℍ) A δ Ψ Θ (l :: I)))
        (fun _ => listPostN (ℍ := ℍ) A δ Ψ Θ (l :: I)) := by
    intro Θ c ℓ α₁ I hfr _ hα₁β n j hjn _ _ ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
    set Fm : Nat → Val → SPropS Loc Val α₁ :=
      famL α₁ (fun Θ' j w r => vN (ℍ := ℍ) A δ Θ' j w r) Θ with hFm
    have hFmD : DownFam α₁ Fm := vN_fam_down A δ α₁ Θ
    set Θ₁ := Θ.add ℓ α₁ Fm with hΘ₁
    have hRs : ∀ k ρ', claimL (ℍ := ℍ) A δ Θ₁ I k ρ' → ρ'.InStratum α₁ := fun k ρ' h =>
      sepList_closed (ResU.inStratum_empty α₁) (fun _ _ _ hc a b => inStratum_compS hc a b)
        (fun m τ hm => ownLeafN_inStratum hα₁β hunif hm) h
    have hcl' : ∀ k ρ', (claimR ℓ α₁ Fm k ⋆ claimL (ℍ := ℍ) A δ Θ₁ I k) ρ' →
        claimL (ℍ := ℍ) A δ Θ (ℓ :: I) k ρ' := by
      rintro k ρ' ⟨ρ₁, ρ₂, hc12, ⟨w, σ', hσ', hFσ, hcw⟩, hr⟩
      refine ⟨ρ₁, ρ₂, hc12, ⟨ℓ, w, σ', rfl, hcw, (vN_above A δ Θ hσ').mp hFσ⟩, ?_⟩
      exact sepList_mono_down (R := fun τ => τ.InStratum α₁)
        (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
          ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
        (fun m τ hτ hm => vN_local (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) (hRs k ρ₂ hr) hr
    have hM := erwp_M_frameRR (Φ := Θ.view c) (l := ℓ) (A := α₁) (F := Fm) hFmD
      (hτok Θ c α₁) hRs (Q := listPostN (ℍ := ℍ) A δ Ψ Θ (ℓ :: I))
      n j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ (fun BM hBM => by
        have h := hA BM hBM
        rw [hτ Θ ℓ α₁ Fm c hfr] at h
        simpa only [erwp_eq_erwpK] using h)
    have h := erwp_opTableR_le (OpTabN.Sub.le fun _ _ _ h => h) hcl' n ls e ρ hM
    simpa only [erwp_eq_erwpK] using h
  have h := erwpK_M_frameList (ι := Unit) (V := fun _ _ => True) (mb := β) hunif
    (fun Θ c _ => Θ.view c) (fun Θ c l α F _ => LocTy.view_add Θ c l α F)
    (fun Θ c I _ => liftTb (opTableR (τ Θ c) (claimL (ℍ := ℍ) A δ Θ I)))
    (fun _ _ _ _ => liftTb_local (opTableR_local _ _)) Ψ hΨs hΨl e ls () hstep I Θ c n ρo ρH ρ
    γ hΘ hc hcρ ho (fun α hα => ⟨(hH α hα).1, fun Θ' c' hE hOK ρm ρ' hm hcomp hc' => by
      simpa only [erwp_eq_erwpK] using (hH α hα).2 Θ' c' hE hOK ρm ρ' hm hcomp hc'⟩)
  rw [erwp_eq_erwpK]
  exact h

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
