import Core.Chain.EffKW835N

/-!
# `[let]` and `[await]` at the typed world  `[spec §14, §19, §27]`

Core's `let_compatC` and `await_compatC` (`Core/EffFin.lean`) at `SemJN` (`let_compatN`,
`let_compatN_persist`, `await_compatN`), step for step, over `Let835N`'s consistency lemmas. `[let]`
is the plain frame around `M` (`erwpK_frame_plainI`, read at the worlds whose location typing is
`OK`), the frame the context of `N` at the frame's world and view:

* `M`'s values are consistent with the view of the world they are posted at, across its
  resumptions (`erwpK_consistentAns`): a row's table reads its answers at the resumption world's
  view (`RowRd.ent`'s `PB`), and an entry owes only worlds whose view the share is consistent
  with (`KW.Owed`);
* at a stop the frame moves to the world the continuation is resumed at, along the order the
  entry owes (`gN_extR` at the part, `consistentX_right`), as `gNFrame_carryKW` moves `[then]`'s;
* a cancel passes the frame by `entF_plain`; an abortive or unrestricted entry leaves it owning
  nothing (`gN_noOwn`, `gN_persistent`).

`N`'s judgment is then read at the world `M`'s value is posted at.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

variable {ι M : Type}

/-- A row's table over a world index does not read the answer type. -/
theorem tabF_effOf_ret (R : RowRd ι M) (μ : M) (S : Row) (A B : VTy) :
    tabF (ℍ := ℍ) R μ (CTy.effOf S A) = tabF (ℍ := ℍ) R μ (CTy.effOf S B) := by
  induction S with
  | nil => funext x; simp [CTy.effOf, tabF]
  | cons o S ih => funext x; simp only [CTy.effOf, tabF]; rw [ih]

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

/-- **A row's table at the typed world reads its answers at the resumption world's view**. -/
theorem tabF_ansC (δ : LSub) (G : CTy) (x : KW) (m i : UInt32) (en : OpEntK KW)
    (hT : tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () G x m i = some en) (y : KW) (k : Nat)
    (ls : List SRec) (w : Val) (ρ : WRes) (hB : en.PB y k ls w ρ) : ConsistentX y.c ρ := by
  obtain ⟨o, -, rfl⟩ := tabF_rowOf_find hT
  exact hB.2

/-- An entry of a row's table at the typed world owes only worlds whose view its share is
consistent with. -/
theorem tabF_wkC (δ : LSub) (G : CTy) (x : KW) (m i : UInt32) (en : OpEntK KW)
    (hT : tabF (ℍ := ℍ) (rdN (ℍ := ℍ) δ) () G x m i = some en) (f : Life) (y : KW) (ρ : WRes)
    (hy : en.wk f y ρ) : y.Θ.OK ∧ ConsistentX y.c ρ ∧ x.Θ.ExtR y.Θ ρ := by
  obtain ⟨o, -, rfl⟩ := tabF_rowOf_find hT
  have hy' : x.Owed f y ρ := hy
  exact ⟨hy'.2.1, hy'.2.2.1, hy'.1.extR⟩

/-- **`[let]`'s frame at the typed world**: the context of `N` at the frame's world, consistent
with its view, at a world whose location typing is `OK`. -/
def letFrN (δ : LSub) (Γ : Ctx VTy) (γ : List Val) (n : Nat) : KW → List SRec → WProp :=
  fun x _ σ => gN (ℍ := ℍ) δ x.Θ Γ γ n σ ∧ ConsistentX x.c σ ∧ x.Θ.OK

/-- **`[let]`** (Core's `let_compatC`): `erwpK_frame_plainI` around `M` with the context of `N` as
the frame, its cancels carried by `entF_plain`, left behind owning nothing where the row cancels
(`hW`), empty at an unrestricted row (`hU`). `N`'s judgment is read at the world `M`'s value is
posted at and its view, from `M`'s value beside the frame: `M`'s value is consistent with that
view across its resumptions (`erwpK_consistentAns`, the row's answers read at the resumption
world's view, `tabF_ansC`). -/
theorem let_compatN {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Cancels → Γ₂.OwnFree) (hU : S.Unr → Ctx.Banged Γ₂)
    (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    SemJN (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine (cN_effOf_tabF S B δ Θ c n ls _ ρ).mpr fun lo => erwpK_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, hc₂⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hM' := (cN_effOf_tabF S A δ Θ c n ls _ ρ₁).mp (hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁) lo
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S A B] at hM'
  have hM'' := erwpK_consistentAns (c := fun z : KW => z.c)
    (fun x m i en hT y k ls w ρ hB => tabF_ansC δ _ x m i en hT y k ls w ρ hB)
    (fun x m i en hT f y ρ hy _ => (tabF_wkC δ _ x m i en hT f y ρ hy).2.1)
    (fun x y (h : y = x) => by rw [h]) n n le_rfl (⟨Θ, c, lo⟩ : KW) ls _ ρ₁ hM' hc₁
  have hK : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).HasHnd m = false :=
    fun _ => by simp [Kont.HasHnd]
  have hC : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).Catches m = false :=
    fun _ => by simp [Kont.Catches]
  change erwpK (ℍ := ℍ) _ _ _ _ _ n ls
    ((Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).plug (substAll γ M)) ρ
  refine erwpK_frame_plainI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
    (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo)
    (fun _ _ _ (h₁ : _ = _) (h₂ : _ = _) => h₂.trans h₁) (fun z hz => LocTy.view_down hz.1 z.c)
    (fun x y (h : y = x) => by rw [h]) (fun x y (h : y = x) hx => h ▸ hx)
    (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
    _ hK hC (letFrN δ Γ₂ γ n) (fun _ _ _ _ _ h => h) (fun x y (h : y = x) _ _ hF => h ▸ hF)
    (fun x m i en hT f y ρ hy => (tabF_wkC δ _ x m i en hT f y ρ hy).1)
    (fun x m i en hT ls ls' ρ σ ρ' hc' he => tabF_wcl hT hc' he)
    (fun x m i en hT f y ρ σ ρ' hc' hv' hy => tabF_wkLeft (rdN_ok δ) hT hc' hv' hy)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ ?_ _ _ ?_ n (⟨Θ, c, lo⟩ : KW) hΘ ls _ ρ₁ hM'' ρ₂ ρ
    ⟨hg₂, hc₂, hΘ⟩ hcρ
  · rintro x m i en hT f y ls ρ' σ ρ'' hc' hv' hy ⟨hσ, -, -⟩
    obtain ⟨hyOK, hyc, hE⟩ := tabF_wkC δ _ x m i en hT f y ρ'' hy
    exact ⟨gN_extR (hE.right hc') hσ, consistentX_right hc' hyc hv', hyOK⟩
  · rintro x m i en hT ha ls' σ ⟨h, -, -⟩
    obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
    refine gN_noOwn (hW ⟨o, (Row.find_mem hf).1, ?_⟩) h
    simp only [RowRd.ent, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
    exact ha.2
  · rintro x m i en hT hq ls' σ ⟨h, -, -⟩
    obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
    exact gN_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · rintro x m i en hT ha hq y k ls' K₁ ρ' σ ρ'' hcan ⟨hσ, -, hyOK⟩ hc'
    obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
    exact entF_plain (rdN_ok δ) _ hK (hC 0) (gN_noOwn (hW ⟨o, (Row.find_mem hf).1, hq⟩) hσ) o
      hyOK.1 hcan hc'
  · rintro y hy k ls' v σ ⟨σ₁, σ₂, hcσ, ⟨hkn, hv, hcv, -⟩, hg₂', hc₂', -⟩
    refine (cN_effOf_tabF S B δ y.Θ y.c k ls' _ σ).mp ?_ y.lo
    refine cN_head (CTy.effOf S B) δ y.Θ hy.1 y.c k ls' σ .hole _ _
      (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
      from (substAll_cons_psub v γ N).symm]
    exact hN δ (v :: γ) y.Θ y.c k ls' σ hδ hy (consistentX_compS hcσ hcv hc₂') hlw₂
      (gN_live_cons hcσ hv (gN_le hkn hg₂'))

/-- **`[let]` binding a persistent type** (Core's `let_compatC`, the bound value owning nothing):
`M`'s value holds `∅`, so the resource `N` starts from is the frame's, consistent with the view
of the frame's world; no premise on the row's answers is read. -/
theorem let_compatN_persist {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {S : Row}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Cancels → Γ₂.OwnFree) (hU : S.Unr → Ctx.Banged Γ₂)
    (hA : A.Persistent)
    (hM : SemJN (ℍ := ℍ) Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : SemJN (ℍ := ℍ) Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    SemJN (ℍ := ℍ) Δ Γ (.app (.val (.lam N)) M) (.comp (CTy.effOf S B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  refine (cN_effOf_tabF S B δ Θ c n ls _ ρ).mpr fun lo => erwpK_of_valid fun hv => ?_
  obtain ⟨ρ₁, ρ₂, hcρ, hg₁, hg₂, hc₁, hc₂⟩ := gN_splitC hsp hg hc hv
  obtain ⟨hlw₁, hlw₂⟩ := hsp.liveWithin hlw
  have hM' := (cN_effOf_tabF S A δ Θ c n ls _ ρ₁).mp (hM δ γ Θ c n ls ρ₁ hδ hΘ hc₁ hlw₁ hg₁) lo
  rw [tabF_effOf_ret (rdN (ℍ := ℍ) δ) () S A B] at hM'
  have hM'' := erwpK_idxLe n n le_rfl (⟨Θ, c, lo⟩ : KW) ls _ ρ₁ hM'
  have hK : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).HasHnd m = false :=
    fun _ => by simp [Kont.HasHnd]
  have hC : ∀ m, (Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).Catches m = false :=
    fun _ => by simp [Kont.Catches]
  change erwpK (ℍ := ℍ) _ _ _ _ _ n ls
    ((Kont.appR (.val (.lam (Expr.psub 1 γ N))) .hole).plug (substAll γ M)) ρ
  refine erwpK_frame_plainI (V := KW.PostK) (Φ := fun z : KW => z.Θ.view z.c)
    (Inv := fun z : KW => z.Θ.OK) (fl := fun z : KW => z.lo)
    (fun _ _ _ (h₁ : _ = _) (h₂ : _ = _) => h₂.trans h₁) (fun z hz => LocTy.view_down hz.1 z.c)
    (fun x y (h : y = x) => by rw [h]) (fun x y (h : y = x) hx => h ▸ hx)
    (fun x y (h : y = x) => by subst h; exact fun _ _ _ _ _ h => h)
    _ hK hC (letFrN δ Γ₂ γ n) (fun _ _ _ _ _ h => h) (fun x y (h : y = x) _ _ hF => h ▸ hF)
    (fun x m i en hT f y ρ hy => (tabF_wkC δ _ x m i en hT f y ρ hy).1)
    (fun x m i en hT ls ls' ρ σ ρ' hc' he => tabF_wcl hT hc' he)
    (fun x m i en hT f y ρ σ ρ' hc' hv' hy => tabF_wkLeft (rdN_ok δ) hT hc' hv' hy)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ ?_ _ _ ?_ n (⟨Θ, c, lo⟩ : KW) hΘ ls _ ρ₁ hM'' ρ₂ ρ
    ⟨hg₂, hc₂, hΘ⟩ hcρ
  · rintro x m i en hT f y ls ρ' σ ρ'' hc' hv' hy ⟨hσ, -, -⟩
    obtain ⟨hyOK, hyc, hE⟩ := tabF_wkC δ _ x m i en hT f y ρ'' hy
    exact ⟨gN_extR (hE.right hc') hσ, consistentX_right hc' hyc hv', hyOK⟩
  · rintro x m i en hT ha ls' σ ⟨h, -, -⟩
    obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
    refine gN_noOwn (hW ⟨o, (Row.find_mem hf).1, ?_⟩) h
    simp only [RowRd.ent, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
    exact ha.2
  · rintro x m i en hT hq ls' σ ⟨h, -, -⟩
    obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
    exact gN_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · rintro x m i en hT ha hq y k ls' K₁ ρ' σ ρ'' hcan ⟨hσ, -, hyOK⟩ hc'
    obtain ⟨o, hf, rfl⟩ := tabF_effOf_some_find hT
    exact entF_plain (rdN_ok δ) _ hK (hC 0) (gN_noOwn (hW ⟨o, (Row.find_mem hf).1, hq⟩) hσ) o
      hyOK.1 hcan hc'
  · rintro y hy k ls' v σ ⟨σ₁, σ₂, hcσ, ⟨hkn, hv⟩, hg₂', hc₂', -⟩
    obtain rfl := vN_empty_of_persistent _ hA hv
    rw [eq_of_compS_empty_left hcσ]
    refine (cN_effOf_tabF S B δ y.Θ y.c k ls' _ σ₂).mp ?_ y.lo
    refine cN_head (CTy.effOf S B) δ y.Θ hy.1 y.c k ls' σ₂ .hole _ _
      (fun μ => Head.beta μ (Expr.psub 1 γ N) v) rfl ?_
    rw [show Kont.hole.plug (Expr.subst 0 v (Expr.psub 1 γ N)) = substAll (v :: γ) N
      from (substAll_cons_psub v γ N).symm]
    exact hN δ (v :: γ) y.Θ y.c k ls' σ₂ hδ hy hc₂' hlw₂
      (gN_live_cons (compS_empty_left σ₂) hv (gN_le hkn hg₂'))


/-- **`[await-c]` at `SemJN`** (Core's `await_compatC`): `[perform]` of the cancellable `a`, then
a `case` whose `inl` arm returns and whose `inr` arm raises the cancel target `c`, each by its own
compatibility lemma, under `[let]`. The bound answer is at `1 + 1`, persistent, so the `[let]` is
`let_compatN_persist`. -/
theorem await_compatN {Δ : LifeCtx} {S : Row} {n : UInt32} {a c : OpSig}
    (hfa : Row.find S n 0 = some a) (ha : a.Cancellable) (haA : a.A = .unit)
    (hfc : Row.find S n 1 = some c) (hc : c.CancelTarget) :
    SemJN (ℍ := ℍ) Δ [] (awaitE n) (.comp (CTy.effOf S .unit)) := by
  obtain ⟨-, han, hai⟩ := Row.find_mem hfa
  obtain ⟨-, hcn, hci⟩ := Row.find_mem hfc
  obtain ⟨-, hq, hB⟩ := ha
  obtain ⟨-, hcab, hcA⟩ := hc
  have hna : a.abort = false := by simp [OpSig.abort, hq]
  have hunit : SemJN (ℍ := ℍ) Δ [] (.val .unit) (.val a.A) := by
    rw [haA]
    intro δ γ Θ c' n' ls ρ _ _ _ _ hg
    obtain rfl : ρ = PMap.empty := hg
    exact cN_ret_of (erwp_val (v := Val.unit) ⟨rfl, rfl⟩)
  have hP : SemJN (ℍ := ℍ) Δ [] (performE (opArgE n 0 (.val .unit)))
      (.comp (CTy.effOf S (.sum .unit .unit))) := by
    have h := perform_compatN (Δ := Δ) (Γ := []) (V := .val .unit) (o := a)
      (by rw [han, hai]; exact hfa) hna hunit
    rw [han, hai, hB] at h; exact h
  have h₁ : SemJN (ℍ := ℍ) Δ [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩] (.var 0)
      (.comp (CTy.effOf S .unit)) :=
    sub_compatN (S := []) (RowLe.nil S) (var_compatN (.here (.cons .nil)))
  have h₂ : SemJN (ℍ := ℍ) Δ [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩]
      (raiseE (opArgE n 1 (.var 0))) (.comp (CTy.effOf S .unit)) := by
    have h := raise_compatN (Δ := Δ) (Γ := [⟨.unit, true⟩, ⟨.sum .unit .unit, false⟩])
      (V := .var 0) (o := c) (B := .unit) (by rw [hcn, hci]; exact hfc) hcab
      (fun _ _ _ _ _ h => vN_noOwn_of_ownFree (by rw [hcA]; exact .unit) h)
      (by rw [hcA]; exact var_compatN (.here (.cons .nil)))
    rw [hcn, hci] at h; exact h
  exact let_compatN_persist .nil (fun _ s hs => absurd hs List.not_mem_nil)
    (fun _ s hs => absurd hs List.not_mem_nil) (by decide) hP
    (sumE_compatN (.left .nil) (var_compatN (.here .nil)) h₁ h₂)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
