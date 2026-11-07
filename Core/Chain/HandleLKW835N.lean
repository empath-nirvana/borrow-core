import Core.Chain.HandleTKW835N
import Core.Chain.HandleL835N

/-!
# `[handle-last]` at the typed world  `[spec §14, §19, §27, §51]`

Core's `handleL_compatC` (`Core/DivHandleLast.lean`) at the relation at `KW`: `erwp_handle_last`
(Core's `ewp_handle_last`) at `erwpK` and `handleL_compatN` at `SemJN`, over `HandleL835N`'s
steps.

* `worksTy_atN`, `exitsTy_atN`: the works and the exits read at `vN`.
* `erwp_handle_last`: `erwpK_handle_leI` at the handled row's table pre-passed by `erwpK_postPA`,
  `κ`'s cancel branch at the table of the operation's own cancel row. A clause pays its `β` step and
  runs its work at its row from the floor `f` the handled stop chose (`erwpK_flr_tabN`), under the
  finaliser frame (`erwpK_frame_then_tabKW`), whose frame is `κ`'s relation with the world reached
  owed from the clause's at `f` (as at `erwp_handle_tail`). The finaliser `κ.2 ()` cancels `κ`
  there; the frame's answer `inl y` resumes `κ` at `y` where the value is posted, and `inr z`
  cancels `κ` under the exit's frame (`erwpK_frame_plain_orI`), `z` carried to each world the cancel
  run resumes at, then runs the exit at `z` there.
* `handleL_compatN`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal clauseAt capTag)

/-! ### The works and the exits -/

/-- **The works at `vN`** (Core's `worksTy_at`). -/
theorem worksTy_atN {S SW : Row} {R : VTy} {Xs : Nat → VTy} {δ : LSub} {Θ : LocTy} {k : Nat} :
    ∀ (E : List (Qual × VTy × VTy)) (j₀ : Nat) {vc : Val} {ρ : WRes},
      vN (ℍ := ℍ) (worksTy S SW R Xs E j₀) δ Θ k vc ρ →
      ∀ j (h : j < E.length), ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vN (ℍ := ℍ) (workTy S SW R (Xs (j₀ + j)) E[j]) δ Θ k g PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, j₀, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, ρ₁, ρ₂, rfl, -, hg, hr⟩ := h
      have he : ρ₁ = PMap.empty := vN_empty_of_persistent _ (workTy_persistent S SW R _ o) hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            by simpa using he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := worksTy_atN E (j₀ + 1) hr j (by simpa using hj)
          refine ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), ?_⟩
          rw [show j₀ + (j + 1) = j₀ + 1 + j by omega]
          simpa using hg'

/-- **The exits at `vN`** (Core's `exitsTy_at`). -/
theorem exitsTy_atN {S : Row} {R : VTy} {Xs : Nat → VTy} {δ : LSub} {Θ : LocTy} {k : Nat} :
    ∀ (E : List (Qual × VTy × VTy)) (j₀ : Nat) {vc : Val} {ρ : WRes},
      vN (ℍ := ℍ) (exitsTy S R Xs E j₀) δ Θ k vc ρ →
      ∀ j, j < E.length → ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vN (ℍ := ℍ) (exitTy S R (Xs (j₀ + j))) δ Θ k g PMap.empty
  | [], _, _, _, _, j, h => by simp at h
  | o :: E, j₀, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, ρ₁, ρ₂, rfl, -, hg, hr⟩ := h
      have he : ρ₁ = PMap.empty := vN_empty_of_persistent (exitTy S R (Xs j₀)) rfl hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            by simpa using he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := exitsTy_atN E (j₀ + 1) hr j (by simpa using hj)
          refine ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), ?_⟩
          rw [show j₀ + (j + 1) = j₀ + 1 + j by omega]
          simpa using hg'

/-! ### `cN`'s tables -/

/-- A row's table at the typed world does not read the answer type (`tabF_effOf_ret`). -/
theorem tabN_effOf_retK (S : Row) (A B : VTy) (δ : LSub) :
    tabN (ℍ := ℍ) (CTy.effOf S A) δ = tabN (ℍ := ℍ) (CTy.effOf S B) δ := by
  funext x
  rw [tabN_eq, tabN_eq, tabF_effOf_ret]

/-- The table of a cancel row is the table of its layers (`tabF_rowOf`). -/
theorem tabN_rowOfK (F : CTy) (δ : LSub) :
    tabN (ℍ := ℍ) F δ = tabN (ℍ := ℍ) (CTy.effOf F.rowOf .unit) δ := by
  funext x
  rw [tabN_eq, tabN_eq, tabF_rowOf]

/-! ### The handler -/

section
variable {δ : LSub} {Θ : LocTy} {c : Loc → Option Life} {S SW : Row}
  {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy} {n : UInt32} {A R : VTy}

/-- **A `[handle-last]` handler at the typed world** (Core's `ewp_handle_last`): `erwpK_handle_leI`
at the handled row's table pre-passed by `erwpK_postPA`, `κ`'s cancel branch at the table of the
operation's own cancel row. A clause pays its `β` step and runs its work at its row, from the floor
`f` the handled stop chose (`erwpK_flr_tabN`), under the finaliser frame (`erwpK_frame_then_tabKW`);
its frame is `κ`'s relation, the world reached owed from the clause's at `f`, carried across each
stop of the work at a floor no higher than `f`. The finaliser `κ.2 ()` cancels `κ` at the world it
runs at; the frame's answer `inl y` resumes `κ` at the world it is posted at, and `inr z` cancels
`κ` there under the exit's frame (`erwpK_frame_plain_orI`), then runs the exit at `z` at the world
the cancel run returns at. -/
theorem erwp_handle_last (hΘ : Θ.OK) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hNZ : S.NZ) (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
    (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
    (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
    {vr vw vn : Val} {N : Nat}
    (hVr : vN (ℍ := ℍ) (retTy S A R) δ Θ N vr PMap.empty)
    (hVw : vN (ℍ := ℍ) (worksTy S SW R Xs E 0) δ Θ N vw PMap.empty)
    (hVn : vN (ℍ := ℍ) (exitsTy S R Xs E 0) δ Θ N vn PMap.empty) {lo : Life} {ls : List SRec}
    {e : Expr} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ z))
      (fun z k _ v ρ => vN (ℍ := ℍ) A δ z.Θ k v ρ) ⟨Θ, c, lo⟩ N ls e ρ)
    (hc : ConsistentX c ρ) :
    erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
      (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S R) δ z))
      (fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) ⟨Θ, c, lo⟩ N ls
      (hndE (lastH n E vr vw vn) e) ρ := by
  set Tin : KW → OpTabK KW := fun z =>
    tabN (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs ++ S) A) δ z with hTin
  set Tout : KW → OpTabK KW := fun z => tabN (ℍ := ℍ) (CTy.effOf S R) δ z with hTout
  have hQout : ∀ z : KW, PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) :=
    fun z k _ v ρ h => vN_down _ δ z.Θ k v ρ h
  have hVt : ∀ x y z : KW, KW.PostK x y → KW.PostK y z → KW.PostK x z :=
    fun _ _ _ (h₁ : _ = _) (h₂ : _ = _) => h₂.trans h₁
  have h' := erwpK_postPA (ℍ := ℍ) (V := KW.PostK) (fl := fun z : KW => z.lo) (T := Tin)
    (c := fun z : KW => z.c) (I := fun z : KW => z.Θ.OK) (P := postOK)
    (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en (tabF_of_tabN hT) y k ls w ρ hB)
    (fun x m i en hT f y ρ hy _ => (tabN_wkC δ _ x m i en hT f y ρ hy).2.2.1)
    (fun x m i en hT f y ρ hy => (tabN_wkC δ _ x m i en hT f y ρ hy).2.1)
    (fun x m i en hT f _ y ρ hP hcx hx => by
      obtain ⟨o, -, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT)
      exact KW.owed_of_post hP.1 hx f hcx)
    (fun x y (h : y = x) => by rw [h]) (fun x y (h : y = x) hx => h ▸ hx) n N ⟨Θ, c, lo⟩ ls e ρ
    h hc hΘ
  refine erwpK_handle_leI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
    (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo) hVt
    (fun z hz => LocTy.view_down hz.1 z.c) (fun x y (h : y = x) => by rw [h]) N
    (fun z => (Tin z).withPAP z.c z.Θ.OK (postOK z) n) Tout
    (fun x _ => OpTabK.withPAP_downAt ⟨(tabN_downI_OK _ δ x).pa, (tabN_downI_OK _ δ x).fin⟩)
    (fun x _ => opTableK_downI (tabN_downI_OK _ δ x))
    (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
    n (fun x m i hm => by rw [OpTabK.withPAP_ne _ hm]; exact tabN_ofEff_neK A R δ x hm)
    (qualsVal (E.map Prod.fst)) vr ⟨lastTuple E 0 (.val vw) (.val vn), isVal_lastTuple _ _ E 0⟩
    _ _ hQout ?_ ?_ ?_ (fun i => some (fun z => tabN (ℍ := ℍ) (fs i.toNat) δ z)) ?_
    KW.postK_refl ?_ ?_ ?_ ?_ N le_rfl ⟨Θ, c, lo⟩ hΘ ls e ρ h'
  · intro x i en hT _
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    exact capTag_ofEffK hnS hlen i en₀ hT₀
  · intro x m i en hT ls₁ ls₂ ρ₁ ρ₂ ρ₀ hc₁ he
    obtain ⟨en₀, hT₀, -, -, -, -, hwc, -⟩ := OpTabK.withPAP_inv hT
    rw [hwc] at he ⊢
    exact tabF_wcl (tabF_of_tabN hT₀) hc₁ he
  · intro x i en hT _ f y ρ₁ ρ₂ ρ₀ hc₁ hv₁ hy
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    exact hy.imp (tabF_wkLeft (rdN_ok δ) (tabF_of_tabN hT₀) hc₁ hv₁) id
  · -- `κ`'s cancel branch: the entry's own cancel obligation
    intro x i en hT ha hq Tk hTk
    obtain ⟨en₀, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_selfK hnS hlen hT₀
    simp only [hji, Option.some.injEq] at hTk
    subst hTk
    exact ⟨fun z => tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (fs j) z,
      entF_fin_of (R := rdN (ℍ := ℍ) δ) (μ' := ()) (m := n) (A := E[j].2.1) (x := x)
        (capB_of_entN ha hq) (hFin j hj).1,
      fun z m i en h => by show tabN _ _ _ _ _ = _; rw [tabN_eq]; exact h, fun z _ => opTableK_downI (tabN_downI_OK _ δ z)⟩
  · intro x m i en hT _ f y ρ₁ hy
    obtain ⟨en₀, hT₀, -, -, -, -, -, -, hwk⟩ := OpTabK.withPAP_inv hT
    rcases hwk f y ρ₁ hy with hy' | hy'
    · exact (tabN_wkC δ _ x m i en₀ hT₀ f y ρ₁ hy').2.1
    · exact hy'.2
  · intro i Tk hTk z m j en hT _ f y ρ₁ hy
    simp only [Option.some.injEq] at hTk
    subst hTk
    exact (tabN_wkC δ _ z m j en hT f y ρ₁ hy).2.1
  · -- `[ret]`: `h_ret` at the value, at the world it is posted at
    rintro x k hk ls' v σ ⟨⟨hv, hcv⟩, hxOK⟩
    obtain ⟨-, hr⟩ := vN_extR (retTy S A R) δ N vr PMap.empty (LocTy.extR_empty Θ x.Θ) hVr
    exact (cN_effOf S R δ x.Θ x.c k ls' _ σ).mp (hr x.Θ (LocTy.extR_refl _ _) hxOK x.c
      (consistentX_empty _) ls' x.c k hk v σ σ (compS_empty_left σ) hv hcv) x.lo
  · intro x i en' hT
    obtain ⟨en, hT₀, rfl⟩ := OpTabK.withPAP_self hT
    obtain ⟨j, hj, hji, -, rfl⟩ := tabN_ofEff_selfK hnS hlen hT₀
    obtain ⟨g, hg, hVg⟩ := worksTy_atN E 0
      (vN_extR (worksTy S SW R Xs E 0) δ N vw PMap.empty (LocTy.extR_empty Θ x.Θ) hVw) j hj
    obtain ⟨nfv, hnf, hVnf⟩ := exitsTy_atN E 0
      (vN_extR (exitsTy S R Xs E 0) δ N vn PMap.empty (LocTy.extR_empty Θ x.Θ) hVn) j hj
    rw [Nat.zero_add] at hVg hVnf
    refine ⟨⟨lastClause j (E[j].2.2.isZero && E[j].1 != .lin) (.val vw) (.val vn),
      isVal_lastClause _ _ _ _⟩, by rw [hji, clauseAt_lastTuple _ _ E 0 j hj]; simp,
      fun ha k hk ls' v κ σ hσ => ?_, fun ha k hk ls' v σ hσ => ?_⟩
    · -- the clause pays its `β` step, then runs its work under the finaliser frame
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = false := ha
      have hq := last_cancel hCancel hj ha'
      obtain ⟨-, hFS, -, hFth, hFP, hFX⟩ := hFin j hj
      simp only [workTy, ha'] at hVg
      show erwpK (ℍ := ℍ) _ _ _ _ x k ls' (.app (lastClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vw) (.val vn)) (.pair (.val v) κ.1)) σ
      rw [ha']
      obtain ⟨σa, σk, hck, ⟨hA', hcA, hxOK⟩, hu, f, hf, hκ⟩ := hσ
      simp only [hji] at hκ
      cases k with
      | zero => exact erwpK_zero
      | succ k₀ =>
      refine erwpK_step (fun _ => opTableK_local _ _) (e' := Expr.subst 0 (Val.pair v κ) _)
        (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl .hole) ?_
      -- the rest runs from the floor the handled stop chose
      refine erwpK_flr_tabN (F := CTy.effOf S R) (δ := δ) f
        (Q := fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) (fun _ _ _ _ _ h => h) k₀ x ls' _ σ ?_
      have hx'OK : (x.flr f).Θ.OK := hxOK
      have hΦ' : ((x.flr f).Θ.view (x.flr f).c).Down := LocTy.view_down hxOK.1 x.c
      have hTd' : (opTableK (x.flr f).lo (Tout (x.flr f))).Down :=
        opTableK_downI (tabN_downI_OK _ δ _)
      refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x.flr f) hΦ' hTd' hQout
        (lastClause_steps_body j vw vn g v κ hg) ?_
      -- the work's run at `Σ_W`, consistent with the view
      obtain ⟨-, hgr⟩ := hVg
      have hy := hgr x.Θ (LocTy.extR_refl _ _) hxOK x.c (consistentX_empty _) ls' x.c k₀
        (by omega) v σa σa (compS_empty_left σa) (vN_down _ δ x.Θ k₀ v σa hA') hcA
      have hy' := (cN_effOf SW (.sum E[j].2.2 (Xs j)) δ x.Θ x.c k₀ ls' _ σa).mp hy (x.flr f).lo
      have hy'' := erwpK_consistentAns (c := fun z : KW => z.c)
        (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en (tabF_of_tabN hT) y k ls w ρ hB)
        (fun x m i en hT f y ρ hy _ => (tabN_wkC δ _ x m i en hT f y ρ hy).2.2.1)
        (fun x y (h : y = x) => by rw [h]) k₀ k₀ le_rfl (x.flr f) ls' _ σa hy' hcA
      rw [tabN_effOf_retK SW _ .unit] at hy''
      show erwpK (ℍ := ℍ) _ _ (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf S R) δ z)) _ _ _ _
        _ _
      rw [tabN_effOf_retK S R .unit]
      -- the frame: `κ`'s relation, the world reached owed from the clause's at `f`
      set en₁ := ((rdN (ℍ := ℍ) δ).ent () n E[j].1 E[j].2.1 E[j].2.2
        (finF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () (fs j)) x).withPAP x.c x.Θ.OK (postOK x) with hen₁
      set Fr : KW → List SRec → WProp := fun y ls₁ τ => y.lo ≤ f ∧ en₁.wk f y τ ∧
        ∀ y', en₁.wk f y' τ → ∀ ls₂, en₁.wc ls₁ ls₂ τ → ∀ k', k' < k₀ + 1 →
          (∀ w : Val, (en₁.PB y' k' ls₂ w ─⋆ erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
            (fun z => opTableK z.lo (Tout z)) (fun z k _ v ρ => vN (ℍ := ℍ) R δ z.Θ k v ρ) y' k'
            ls₂ (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) τ) ∧
          (en₁.q ≠ .lin → ∀ Tk, some (fun z => tabN (ℍ := ℍ) (fs j) δ z) = some Tk →
            erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c) (fun z => opTableK z.lo (Tk z))
              (fun _ => unitPost) y' k' ls₂ (.app κ.1 (.val (Val.inj₂ .unit))) τ) with hFr
      have hFext : ∀ y ls₁ ls₂ τ, extF ls₁ ls₂ τ → Fr y ls₁ τ → Fr y ls₂ τ := by
        rintro y ls₁ ls₂ τ he ⟨hlo, hwk, hk'⟩
        exact ⟨hlo, hwk, fun y' hy' ls₃ he' => hk' y' hy' ls₃ (extF_trans he he')⟩
      have hOKwk : ∀ y τ, en₁.wk f y τ → y.Θ.OK := by
        rintro y τ (h | h)
        · exact h.2.1
        · exact h.2
      refine erwpK_frame_then_tabKW (δ := δ) S SW (fs j).rowOf hNZ hSW hFS hFth hFP
        (lastN j κ vn) (lastD κ) Fr
        (fun _ ls₁ ls₂ hs τ hF => hFext _ ls₁ ls₂ τ (extF_of_same hs τ) hF) ?_
        (fun hu => absurd hu hSu) (Qd := fun _ => unitPost)
        (fun _ _ _ v ρ hv => ⟨hv.2, hv.1 ▸ noOwn_empty⟩) k₀ ?_ _ _ hQout ?_ k₀ le_rfl (x.flr f)
        hxOK.1 ls' _ σa hy'' σk σ
        ⟨min_le_right _ _, Or.inr ⟨⟨rfl, rfl, min_le_left _ _⟩, hxOK⟩, hκ⟩ hck
      · -- the frame across a stop of the work, at a floor no higher than `f`
        rintro _ m x₁ f₁ y ls₁ ls₂ ρ₁ τ ρ₁' hf₁ hc₁ hv₁ hy he ⟨hlo, hwk, hk'⟩
        have hy₁ : x₁.Owed f₁ y ρ₁' := hy
        have hyτ : x₁.Owed f y τ :=
          (hy₁.left (ResU.CompS.comm hc₁) hv₁).floor_le (le_trans hf₁ hlo)
        refine hFext y ls₁ ls₂ τ (extF_right hc₁ he)
          ⟨le_trans hy₁.2.2.2.1 hlo, Or.inl ?_, hk'⟩
        rcases hwk with hw | ⟨hpost, -⟩
        · exact KW.Owed.trans hw hyτ
        · exact KW.Owed.of_post hpost hyτ
      · -- the finaliser `κ.2 ()` cancels `κ` at its cancel row's table
        rintro x₁ hx₁ k hk ls₁ ρ₁ ⟨-, hwk, hk'⟩
        refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x₁)
          (LocTy.view_down hx₁ x₁.c) (opTableK_downI (tabN_downI _ δ x₁))
          (fun _ => unitPost_down) (lastD_steps κ) ?_
        rw [← tabN_rowOfK]
        exact (hk' x₁ hwk ls₁ (extF_refl ls₁ ρ₁) k (by omega)).2 hq _ rfl
      · -- the frame's answer
        rintro x₁ - k hk ls₁ w τ ⟨τ₁, τ₂, hcτ, ⟨-, hw, hcw, -⟩, -, hwk, hk'⟩
        have hx₁OK : x₁.Θ.OK := hOKwk x₁ τ₂ hwk
        have hΦ₁ : (x₁.Θ.view x₁.c).Down := LocTy.view_down hx₁OK.1 x₁.c
        have hTd₁ : (opTableK x₁.lo (tabN (ℍ := ℍ) (CTy.effOf S .unit) δ x₁)).Down :=
          opTableK_downI (tabN_downI_OK _ δ _)
        rcases hw with ⟨y, rfl, hy⟩ | ⟨z, rfl, hz⟩
        · -- `inl y` resumes `κ` at `y`
          refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQout
            (lastN_inl j κ vn y) ?_
          rw [← tabN_effOf_retK S R .unit]
          exact (hk' x₁ hwk ls₁ (extF_refl ls₁ τ₂) k (by omega)).1 y τ₁ τ ⟨hy, hcw⟩
            (ResU.CompS.comm hcτ)
        · -- `inr z` cancels `κ` beside `z`, then runs the exit at `z`
          refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x₁) hΦ₁ hTd₁ hQout
            (lastN_inr j κ vn z) ?_
          have hcan := (hk' x₁ hwk ls₁ (extF_refl ls₁ τ₂) k (by omega)).2 hq _ rfl
          have hcan' := erwpK_idxLe k k le_rfl x₁ ls₁ _ τ₂ hcan
          refine erwpK_frame_plain_orI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
            (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo) hVt
            (fun z hz => LocTy.view_down hz.1 z.c) (fun x y (h : y = x) => by rw [h])
            (fun x y (h : y = x) hx => h ▸ hx)
            (T := fun z => tabN (ℍ := ℍ) (fs j) δ z)
            (T' := fun z => tabN (ℍ := ℍ) (CTy.effOf S .unit) δ z)
            (fun z => by
              have h := tabF_le_of_rowLe (ℍ := ℍ) (rdN (ℍ := ℍ) δ) hFS () .unit .unit z
              rw [← tabF_rowOf, ← tabN_eq, ← tabN_eq] at h; exact h)
            (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
            (exitK j vn z) (exitK_plain j vn z).1 (exitK_plain j vn z).2
            (fun y _ τ' => vN (ℍ := ℍ) (Xs j) δ y.Θ k z τ' ∧ ConsistentX y.c τ' ∧ y.Θ.OK)
            (fun _ _ _ _ _ h => h) (fun x y (h : y = x) _ _ hF => h ▸ hF)
            (fun x m i en hT f y ρ hy => (tabN_wkC δ _ x m i en hT f y ρ hy).2.1)
            (fun x m i en hT ls₁ ls₂ ρ₁ σ₁ ρ₁' hc₁ he₁ => tabF_wcl (tabF_of_tabN hT) hc₁ he₁)
            (fun x m i en hT f y ρ₁ σ₁ ρ₁' hc₁ hv₁ hy =>
              tabF_wkLeft (rdN_ok δ) (tabF_of_tabN hT) hc₁ hv₁ hy)
            (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ ?_ _ _ ?_ k x₁ hx₁OK ls₁ _ τ₂ hcan'
            τ₁ τ ⟨hz, hcw, hx₁OK⟩ (ResU.CompS.comm hcτ)
          · rintro x₂ m i en hT f₂ - y ls₂ ρ₂ σ₂ ρ₂' hc₂ hv₂ hy₂ ⟨hzv, -, -⟩
            have h₂ : x₂.Owed f₂ y ρ₂' := tabN_wkC δ _ x₂ m i en hT f₂ y ρ₂' hy₂
            exact ⟨vN_extR _ δ k z σ₂ (h₂.1.extR.right hc₂) hzv,
              consistentX_right hc₂ h₂.2.2.1 hv₂, h₂.2.1⟩
          · rintro x₂ m i en₂ hT₂ ha₂ ls₂ τ' ⟨hτ, -, -⟩
            obtain ⟨o, hf, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT₂)
            refine vN_noOwn_of_ownFree (hFX ⟨o, (Row.find_mem hf).1, ?_⟩) hτ
            simp only [RowRd.ent, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha₂
            exact ha₂.2
          · rintro x₂ m i en₂ hT₂ hq₂
            obtain ⟨o, hf, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT₂)
            exact absurd hq₂ (find_not_unr hFS hSu hf)
          · rintro x₂ m i en₂ hT₂ - hq₂ y k' ls₂ K₁ ρ' τ' ρ'' hcan₁ ⟨hτ, -, hyOK⟩ hc'
            obtain ⟨o, hf, rfl⟩ := tabF_rowOf_find (tabF_of_tabN hT₂)
            exact entF_plain (rdN_ok δ) _ (exitK_plain j vn z).1 ((exitK_plain j vn z).2 0)
              (vN_noOwn_of_ownFree (hFX ⟨o, (Row.find_mem hf).1, hq₂⟩) hτ) o hyOK.1 hcan₁ hc'
          · rintro y hyOK k' ls₂ w' τ' ⟨τa, τb, hcab, ⟨hk'', hw'⟩, ⟨hz', hcz', -⟩⟩
            obtain ⟨rfl, rfl⟩ := hw'
            rw [eq_of_compS_empty_left hcab]
            refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := y)
              (LocTy.view_down hyOK.1 y.c) (opTableK_downI (tabN_downI_OK _ δ _)) hQout
              (exitK_steps j vn z nfv hnf) ?_
            obtain ⟨-, hnr⟩ := vN_extR _ δ N nfv PMap.empty (LocTy.extR_empty x.Θ y.Θ) hVnf
            rw [← tabN_effOf_retK S R .unit]
            exact (cN_effOf S R δ y.Θ y.c k' ls₂ _ τb).mp (hnr y.Θ (LocTy.extR_refl _ _) hyOK
              y.c (consistentX_empty _) ls₂ y.c k' (by omega) z τb τb (compS_empty_left τb)
              (vN_le hk'' hz') hcz') y.lo
    · -- an abortive operation: the clause runs its work `w v` at the outer row
      have ha' : (E[j].2.2.isZero && E[j].1 != .lin) = true := ha
      simp only [workTy, ha'] at hVg
      show erwpK (ℍ := ℍ) _ _ _ _ x k ls' (.app (lastClause j (E[j].2.2.isZero && E[j].1 != .lin)
        (.val vw) (.val vn)) (.val v)) σ
      rw [ha', lastClause_abort]
      obtain ⟨hA', hcA, hxOK⟩ := hσ
      refine erwpK_pureSteps (Φ := fun z : KW => z.Θ.view z.c) (x := x)
        (LocTy.view_down hxOK.1 x.c) (opTableK_downI (tabN_downI_OK _ δ _)) hQout
        (tailClauseA_steps j vw g v hg) ?_
      obtain ⟨-, hgr⟩ := hVg
      exact (cN_effOf S R δ x.Θ x.c k ls' _ σ).mp (hgr x.Θ (LocTy.extR_refl _ _) hxOK x.c
        (consistentX_empty _) ls' x.c k hk v σ σ (compS_empty_left σ) hA' hcA) x.lo

end

/-- **`[handle-last]` at `SemJN`** (Core's `handleL_compatC`): the handler's values are read off its
run at the run's start (`erwp_val_post`); the handled computation runs at its row's table from the
part of the resource consistent with the view (`gN_splitC`), at every floor, and the handler is
`erwp_handle_last`. -/
theorem handleL_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Hr Hw Hn e : Expr} {S SW : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {Xs : Nat → VTy} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁)
    (hHw : Hw.ValFormIn Γ₁) (hHn : Hn.ValFormIn Γ₁)
    (hc : SemJN (ℍ := ℍ) Δ Γ₁ (.pair Hr (.pair Hw Hn))
      (.val (.tensor (retTy S A R) (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0)))))
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hNZ : S.NZ) (hCancel : ∀ o ∈ E, o.1 = .cancel ∨ (o.2.2.isZero && o.1 != .lin) = true)
    (hSW : RowLe SW S) (hSu : ¬ S.UnrD)
    (hFin : ∀ j, j < E.length → LastFinOK S SW (fs j) (Xs j))
    (he : SemJN (ℍ := ℍ) Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A))) :
    SemJN (ℍ := ℍ) Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (lastTuple E 0 Hw Hn)) e)
      (.comp (CTy.effOf S R)) := by
  intro δ γ Θ c N ls ρ hδ hΘ hcρ hlw hg
  refine (cN_effOf S R δ Θ c N ls _ ρ).mpr fun lo => erwpK_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂, -, hc₂⟩ := gN_splitC hsp hg hcρ hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hρ₁ : ρ₁ = PMap.empty := gN_deadP hd hg₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ (.pair Hr (.pair Hw Hn))) :=
    isVal_psub_valFormIn hlw₁ (.pair hHr (.pair hHw hHn))
  have hH' : erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
      (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (retTy S A R)
        (.tensor (worksTy S SW R Xs E 0) (exitsTy S R Xs E 0))) δ Θ k v ρ) N ls
      (⟨substAll γ (.pair Hr (.pair Hw Hn)), hval⟩ : Val).1 PMap.empty :=
    erwp_of_cN_ret (hc δ γ Θ c N ls PMap.empty hδ hΘ (consistentX_empty c) hlw₁ hg₁)
  have hE' := (cN_effOf _ A δ Θ c N ls _ ρ₂).mp (he δ γ Θ c N ls ρ₂ hδ hΘ hc₂ hlw₂ hg₂) lo
  show erwpK (ℍ := ℍ) _ _ _ _ _ N ls
    (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) (.pair Hr (lastTuple E 0 Hw Hn)) e)) ρ₂
  rw [psub_hndExpr]
  simp only [Expr.psub]
  rw [show Expr.psub 0 γ (lastTuple E 0 Hw Hn) = lastTuple E 0 (substAll γ Hw) (substAll γ Hn) from
    lastTuple_psub γ Hw Hn E 0]
  -- the handler's values, read off its run at the run's start
  rw [erwpK_eq]
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ls', ρ', -, hv'⟩ := erwp_val_post (by omega) hH'
    (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg hI hl hfd
  obtain ⟨vr, vwn, σ₁, σ₂, hpair, -, hVr, hVwn⟩ := hv'
  have hσ₁ : σ₁ = PMap.empty := vN_empty_of_persistent _ (retTy_persistent S A R) hVr
  subst hσ₁
  obtain ⟨vw, vn, τ₁, τ₂, hpair', -, hVw, hVn⟩ := hVwn
  have hτ₁ : τ₁ = PMap.empty := vN_empty_of_persistent _ (worksTy_persistent S SW R Xs E 0) hVw
  have hτ₂ : τ₂ = PMap.empty := vN_empty_of_persistent _ (exitsTy_persistent S R Xs E 0) hVn
  subst hτ₁ hτ₂
  have hHe : substAll γ (.pair Hr (.pair Hw Hn)) = (Val.pair vr vwn).1 :=
    congrArg Subtype.val hpair
  rw [hpair'] at hHe
  simp only [substAll, Expr.psub, Val.pair] at hHe
  obtain ⟨h₁, h₂⟩ := Expr.pair.inj hHe
  obtain ⟨h₃, h₄⟩ := Expr.pair.inj h₂
  have hH := erwp_handle_last (fs := fs) hΘ hnS hlen hNZ hSW hSu hCancel hFin hVr hVw hVn hE' hc₂
  rw [erwpK_eq] at hH
  rw [h₁, show substAll γ Hw = vw.1 from h₃, show substAll γ Hn = vn.1 from h₄] at hrun
  exact hH ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
