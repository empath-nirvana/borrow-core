import GhostEnd.Instance
import GhostEnd.Handle
import Core.EffBorrow

/-!
# GhostEnd — drop at an affine yield: the unwinding `withbor` at a resuming row

At an affine yield the continuation may be cancelled instead of resumed. The lend was ended by
the freeze, and 6.65's exit handed the owner `ℓ ↦ w ⋆ 𝒱⟦T⟧(w)` back into the stop's share. A
cancel must dispose of it. The bare `withbor` frame has no finaliser. The unwinding form

    withborU d = λr. λf. (f [] r) then b. (r, b) unwind d r

runs `d r` when the callback unwinds (`Core/EffBorrow.lean`). It is proved there at an abortive
row (`withbor2U_compatX`). Here it is lifted to a row whose operations resume, as 6.65 was lifted
(`ewpTS_M_frameR`):

* `opTableO`: the callback's stops, the owner handed back. Resumed, the share (owner included)
  owes the continuation. Cancelled, the share splits: the callback's part cancels as its own
  context unwinds, and the owner is left for the finaliser.
* `ewp_then_owner`: the frame `ubind (N, D) [·]` around a callback whose stops are `opTableO`'s.
  A stop of the whole is the callback's stop under the frame. At a cancel, the callback's part
  unwinds and then the finaliser runs on the owner, under `cfin` (`cancel_then`).
* `withborR_compat`: `withborU d ℓ f` at the row's table, from a re-lendable callback
  (`Relend` at `opTableO`, `ewpTS_M_frameR`), `d : Ref T ⊸ 1`.
* `relendO_yield`, `withborR_spans_yields_cC`: a straight-line borrower whose yields are affine;
  T15.5's drop clause has its premise.

Disposing of the owner needs nothing new: the cancel happens at a list `Ext`-above the stop's,
the owner is Kripke there (`vC_local`), and the lend is not re-opened, so `d` receives the owner
outright. What the cancel asks of the borrower is that its frozen share unwinds: its frames drop.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Every operation of the table resumes, and none is unrestricted. -/
def ResumeAff (Tab : OpTab) : Prop :=
  ∀ n i en, Tab n i = some en → en.abort = false ∧ en.q ≠ .unr

/-- **A callback's stop under the unwinding frame**, the owner handed back: at every extension,
resumed it owes `Φ`, and cancelled it splits into the callback's cancel and the owner. -/
def opTableO (Tab : OpTab) (l : BoCa.Loc) (T : VTy) (δ : LSub) : Table := fun ls t Φ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEnt) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        Tab n i = some en ∧ en.abort = false⌝ ⋆
      (en.PA ls v ⋆ fun ρ => ∀ ls', Ext ls ls' ρ →
        (∀ w : Val, (en.PB ls' w ─⋆ Φ ls' (K.plug (.val w))) ρ) ∧
        (en.q ≠ .lin → (cancelOwed ls' K ⋆ owner l T δ ls') ρ))

theorem opTableO_mono (Tab : OpTab) (l : BoCa.Loc) (T : VTy) (δ : LSub) :
    (opTableO Tab l T δ).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨hp, ρ₁, ρ₂, hc, hA, hk⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρ₁, ρ₂, hc, hA, fun ls' he =>
    ⟨fun w σ₁ σ₂ hB hcσ => hΦ _ _ _ ((hk ls' he).1 w σ₁ σ₂ hB hcσ), (hk ls' he).2⟩⟩⟩

/-- **The unwinding frame around a callback at a resuming row.** As `ewp_frame_then`, but the
frame (the owner) is not carried through the callback's run: the callback holds it lent, and each
stop hands it back (`opTableO`). Resumed, it goes back to the callback's continuation. Cancelled,
the callback's context unwinds and the finaliser `D` runs on it (`cancel_then`). -/
theorem ewp_then_owner (Tab : OpTab) (hRA : ResumeAff Tab) (Nv Dv : Val) (l : BoCa.Loc) (T : VTy)
    (δ : LSub) {Qd : List SRec → Val → WProp} (hQd : ∀ ls v ρ, Qd ls v ρ → NoOwn ρ)
    (hD : ∀ ls, Entails (owner l T δ ls)
      (ewpTS ls (.app (.val Dv) (.val .unit)) (opTable OpTab.empty) Qd))
    (Q₁ Q : List SRec → Val → WProp)
    (hk : ∀ ls v, Entails (Q₁ ls v) (ewpTS ls ((ubindK Nv Dv).plug (.val v)) (opTable Tab) Q)) :
    ∀ {ls : List SRec} {e : Expr} {ρ : WRes}, ewpTS ls e (opTableO Tab l T δ) Q₁ ρ →
      ewpTS ls ((ubindK Nv Dv).plug e) (opTable Tab) Q ρ := by
  have hOs : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (owner l T δ ls) (owner l T δ ls') :=
    fun _ _ hs _ ⟨w, ρa, ρb, hc, ho, hv⟩ => ⟨w, ρa, ρb, hc, ho, vC_local true T (ext_of_same hs ρb) hv⟩
  intro ls e ρ h
  refine ewp_ind (fun ls e ρ => ewpTS ls ((ubindK Nv Dv).plug e) (opTable Tab) Q ρ) ?_ h
  intro ls e ρ hs
  refine ewp_fold (opTable_mono Tab) (wpG_bind (ubindK Nv Dv) e ls _ ρ ?_)
  refine wpG_mono (fun ls' t σ ht => ?_) hs
  rcases ht with ⟨v, rfl, hv⟩ | hp
  · exact ewp_unfold (opTable_mono Tab) (hk ls' v σ hv)
  refine wpG_here _ _ _ σ (Or.inr ?_)
  obtain ⟨K₁, n, i, v, en, hp⟩ := hp
  obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hPA, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨-, hq⟩ := hRA n i en hT
  refine Or.inl ⟨(ubindK Nv Dv).comp K₁, n, i, v, en,
    pure_sep_mk ⟨(Kont.plug_comp _ _ _).symm, ?_, hT, ha⟩
    ⟨ρa, ρk, hcak, hPA, fun hu => absurd hu hq, fun ls'' he => ⟨?_, fun hq' => ?_⟩⟩⟩
  · rw [hasHnd_comp, hK₁]; rfl
  · intro w τ₁ τ₂ hB hcτ
    rw [Kont.plug_comp]
    exact (hcont ls'' he).1 w τ₁ τ₂ hB hcτ
  · obtain ⟨ρc, ρo, hco, hcan, ho⟩ := (hcont ls'' he).2 hq'
    show ewpTS _ _ _ _ _
    rw [dead_comp, dead_ubindK, Kont.plug_comp]
    exact cancel_then (fun _ _ _ h => by simp [OpTab.empty] at h) Nv Dv (owner l T δ) hOs hQd hD
      hcan ho hco

/-- **`withborU` at a resuming row.** `withborU d ℓ f` from `ℓ ↦ v ⋆ 𝒱⟦T⟧(v)`, the callback
re-lendable at `opTableO` (6.65 at a resuming table, `ewpTS_M_frameR`) and `d : Ref T ⊸ 1` the
finaliser. At a return the source is paired with the answer; at a resumption the callback is
re-lent; at a cancel the callback unwinds and `d` disposes of the owner. -/
theorem withborR_compat (Tab : OpTab) (hRA : ResumeAff Tab) {d : Expr} (hdc : closedAt 0 d = true)
    {T B : VTy} {δ : LSub} {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    (hd : ∀ ls, wpTS ls d (fun ls'' => vP (.lolli (.ref T) .unit) ls'' δ) PMap.empty)
    (f : Val) (l : BoCa.Loc) (v : Val) (ls : List SRec)
    (hR : Relend (opTableO Tab l T δ) l T δ (finPost l T B δ) ls
      (.app (.app (.val f) (.val .unit)) (.val (.loc l))) PMap.empty) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (ewpTS ls (.app (.app (.val (withborUV d)) (.val (.loc l))) (.val f)) (opTable Tab)
        (fun ls r => vC true (.tensor (.ref T) B) ls δ r)) := by
  intro ρ hρ
  refine withborUE_beta (opTable_mono _) hdc (.loc l) rfl f ?_
  have hcb := ewpTS_M_frameR (opTableO Tab l T δ) (opTableO_mono Tab l T δ) l T δ βP hP
    (finPost l T B δ) ls _ ρ ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨v, hρ⟩, hR⟩
  refine ewp_then_owner Tab hRA _ _ l T δ
    (Qd := fun ls v => vP .unit ls δ v) (fun _ _ _ h => by obtain ⟨rfl, -⟩ := h; exact noOwn_empty)
    (fun ls σ ho => ?_) (finPost l T B δ) _ ?_ hcb
  · obtain ⟨w, ρl, ρP, hcl, hl, hw⟩ := ho
    exact ewp_of_wp (opTable_mono _) (fin_run hdc rfl hd ls σ
      ⟨l, w, pure_sep_mk rfl ⟨ρl, ρP, hcl, hl, hw⟩⟩)
  · rintro ls' r σ ⟨so, sb, hcs, ⟨w, ρl, ρP, hcl, hl, hw⟩, hBr⟩
    refine ewp_ret_pair (opTable_mono _) (.loc l) rfl _ r ?_
    exact ⟨Val.loc l, r, pure_sep_mk rfl
      ⟨so, sb, hcs, ⟨l, w, pure_sep_mk rfl ⟨ρl, ρP, hcl, hl, hw⟩⟩, hBr⟩⟩

/-- **An affine yield with the lend open.** As `relend_yield`, at `opTableO`: the frozen share is
the frame `Fr` (which owns nothing, so it is left behind when the continuation is cancelled) and
the owner the frame handed back. Resumed, the owner and the rest are owed; cancelled, the context
`·; rest` unwinds at once and the owner is left for the finaliser. -/
theorem relendO_yield (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en)
    (ha : en.abort = false)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {l : BoCa.Loc} {T : VTy} {δ : LSub} {Q : List SRec → Val → WProp}
    (Fr : List SRec → WProp) (hFe : ∀ ls ls' ρ, Ext ls ls' ρ → Fr ls ρ → Fr ls' ρ)
    {β : Life} (hFo : ∀ ls ρ, Fr ls ρ → ∀ α, α ⊏ β → ρ.InStratum α)
    (hFn : ∀ ls ρ, Fr ls ρ → NoOwn ρ)
    {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    (h : ∀ ls ρ, Fr ls ρ → Relend (opTableO Tab l T δ) l T δ Q ls rest ρ) (ls : List SRec)
    (ργ : WRes) (hF : Fr ls ργ) :
    Relend (opTableO Tab l T δ) l T δ Q ls (yieldSeq n i y rest) ργ := by
  have hTb := opTableO_mono Tab l T δ
  refine relend_fold hTb ⟨β, fun α hα => ⟨fun ρm ρ₂ hm hc => ?_, hFo ls ργ hF α hα⟩⟩
  refine freeze_at ρ₂ ⟨ρm, ργ, ResU.CompS.comm hc, hm, ?_⟩
  refine ⟨fun w ρa ρb hown hcab ρc ρd hv hccd => Or.inr ⟨.seq .hole rest, n, i, y, en,
    pure_sep_mk ⟨rfl, rfl, hTn, ha⟩ ⟨PMap.empty, ρd, compS_empty_left ρd, hy ls, ?_⟩⟩,
    hFo ls ργ hF α hα⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcab hccd
  intro ls' hext
  have ho : owner l T δ ls' s :=
    ⟨w, ρa, ρc, hs, hown, vC_local true T ((hext.right hρs).right hs) hv⟩
  refine ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun _ => ⟨ργ, s, hρs, ?_, ho⟩⟩
  · obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
    obtain rfl : τ₂ = ρd := ResU.CompS.functional hcτ (ResU.comp_empty_right ρd)
    refine ⟨s, ργ, ResU.CompS.comm hρs, ho, ?_⟩
    exact relend_step hTb (fun μ => Step1N.head (Head.seq μ rest) rfl)
      (h ls' ργ (hFe ls ls' ργ (hext.left hρs) hF))
  · refine (ewp_abortive (cancelTab_abortive OpTab.empty)).mpr (wpG_here _ _ _ _ (Or.inr ?_))
    exact ⟨.seq .hole rest, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, ργ, compS_empty_left ργ, ⟨rfl, trivial⟩, hFn ls ργ hF⟩⟩

/-- A straight-line borrower `yield y₁; …; yield yₙ; N_f` is re-lendable at `opTableO`, its yields
affine or linear. -/
theorem relendO_chain {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β) {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    {Nf : Expr} (hN : SemC (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.ret (.box (.var x) B)))
    (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en) (ha : en.abort = false)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty) (l : BoCa.Loc) :
    ∀ (ys : List Val), (∀ y ∈ ys, ∀ ls, en.PA ls y PMap.empty) → ∀ ls,
      Relend (opTableO Tab l T δ) l T δ (finPost l T B δ) ls
        (chain n i ys (substAll [Val.loc l] Nf)) PMap.empty
  | [], _, ls =>
      relend_fin (Γ' := []) hδ hbx hΔx hβ hT hB (fun _ h => absurd h (by simp))
        (fun _ h => absurd h (by simp)) hN _ (opTableO_mono Tab l T δ) l ls [] PMap.empty
        (gDenC_nil ls δ)
  | y :: ys, hys, ls =>
      relendO_yield Tab hTn ha hPB (fun _ ρ => ρ = PMap.empty) (fun _ _ _ _ h => h)
        (β := β) (fun _ _ h _ _ => by rw [h]; exact ResU.inStratum_empty _)
        (fun _ _ h => by rw [h]; exact noOwn_empty) (hys y List.mem_cons_self)
        (fun ls' ρ hρ => hρ ▸ relendO_chain hδ hbx hΔx hβ hT hB hN Tab hTn ha hPB l ys
          (fun y' hy' => hys y' (List.mem_cons_of_mem _ hy')) ls') ls PMap.empty rfl

/-- **O15.1 with an affine yield, at the kernel's relation.** A row `Σ` of resuming operations,
none unrestricted and none abortive, whose `yield` is answered at `1`: the unwinding `withbor`
with finaliser `d : Ref T ⊸ 1` lends `ℓ` to a straight-line borrower spanning the yields, and the
program is in `𝒞⟦F_Σ (Ref T ⊗ B)⟧`. The continuation at each yield may be cancelled. -/
theorem withborR_spans_yields_cC {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β) {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    {Nf : Expr} (hNf : closedAt 1 Nf = true)
    (hN : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.comp (.ret (.box (.var x) B))))
    {d : Expr} (hdc : closedAt 0 d = true)
    (hd : ∀ ls, wpTS ls d (fun ls'' => vP (.lolli (.ref T) .unit) ls'' δ) PMap.empty)
    (S : Row) (hRA : ∀ o ∈ S, o.abort = false ∧ o.q ≠ .unr)
    (o : OpSig) (hf : Row.find S o.n o.i = some o) (hoB : o.B = .unit)
    (ys : List Val) (hys : ∀ y ∈ ys, closedAt 0 y.1 = true)
    (hy : ∀ y ∈ ys, ∀ ls, vC true o.A ls δ y PMap.empty)
    (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (cC (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app (.val (withborUV d)) (.val (.loc l))) (.val (cbV o.n o.i ys Nf)))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ).mpr ?_
  have hRA' : ResumeAff (Row.tab S δ) := by
    intro n i en hT
    obtain ⟨o', hf', rfl⟩ := Row.tab_some hT
    exact hRA o' (Row.find_mem hf').1
  have hTn : Row.tab S δ o.n o.i = some (o.ent δ) := by simp [Row.tab, hf]
  have ha : (o.ent δ).abort = false := (hRA o (Row.find_mem hf).1).1
  refine withborR_compat (Row.tab S δ) hRA' hdc hP hd _ l v ls ?_ ρ hρ
  refine relend_cbV (opTableO_mono _ _ _ _) o.n o.i ys hys hNf ?_
  refine relendO_chain hδ hbx hΔx hβ hT hB (fundamentalC hN) (Row.tab S δ) hTn ha ?_ l ys hy ls
  intro ls' w σ h
  simp only [OpSig.ent, hoB] at h
  exact ⟨h.2, h.1⟩

/-- **The affine lend spanning the yields, as a semantic judgment** at `r : Ref T`, the finaliser
`d` a closed term of `Ref T ⊸ 1`. -/
theorem withborR_spans_yields_sem {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life}
    (hb : Δ.Defines b) (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T)
    {Nf : Expr} (hNf : closedAt 1 Nf = true)
    (hN : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.comp (.ret (.box (.var x) B))))
    {d : Expr} (hdc : closedAt 0 d = true) (hd : SemV Δ [] d (.lolli (.ref T) .unit))
    (S : Row) (hRA : ∀ o ∈ S, o.abort = false ∧ o.q ≠ .unr)
    (o : OpSig) (hf : Row.find S o.n o.i = some o) (hoB : o.B = .unit)
    (ys : List Val) (hys : ∀ y ∈ ys, closedAt 0 y.1 = true)
    (hy : ∀ δ, ∀ y ∈ ys, ∀ ls, vC true o.A ls δ y PMap.empty)
    (hcb : closedAt 0 (cbV o.n o.i ys Nf).1 = true) :
    SemC Δ [⟨.ref T, true⟩]
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (cbV o.n o.i ys Nf)))
      (CTy.effOf S (.tensor (.ref T) B)) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg
  cases γ with
  | nil => exact absurd hlen (by simp [Ctx.LiveWithin])
  | cons vr γ' =>
    obtain ⟨ρ₁, ρ₂, hc, hv, hρ₂, -⟩ := hgs
    subst hρ₂
    obtain rfl : ρ = ρ₁ := ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)
    obtain ⟨ℓ, v', hs⟩ := hv
    obtain ⟨rfl, hrest⟩ := pure_sep_iff.mp hs
    have hsub : substAll (Val.loc ℓ :: γ')
        (.app (.app (.val (withborUV d)) (.var 0)) (.val (cbV o.n o.i ys Nf)))
        = .app (.app (.val (withborUV d)) (.val (.loc ℓ))) (.val (cbV o.n o.i ys Nf)) := by
      have hw : Expr.psub 0 (Val.loc ℓ :: γ') (withborUV d).1 = (withborUV d).1 :=
        psub_closedAt _ _ (withborUE_closed hdc) le_rfl
      have hc' : Expr.psub 0 (Val.loc ℓ :: γ') (cbV o.n o.i ys Nf).1 = (cbV o.n o.i ys Nf).1 :=
        psub_closedAt _ _ hcb le_rfl
      show Expr.psub 0 _ _ = _
      simp only [Expr.psub]
      rw [show Expr.val (withborUV d) = (withborUV d).1 from rfl, hw,
        show Expr.val (cbV o.n o.i ys Nf) = (cbV o.n o.i ys Nf).1 from rfl, hc']
      simp [Val.shift_zero, Expr.val]
    rw [hsub]
    obtain ⟨β, hβ⟩ := hb δ hδ
    obtain ⟨b', hdef, hO⟩ := hside
    obtain ⟨β', hb'⟩ := hdef δ hδ
    have hP : ∀ ls' w σ', vC true T ls' δ w σ' → σ'.InStratum (Life.down β') :=
      fun ls' w σ' h => vC_outlivesLe hδ hb' hO true ls' w σ' h _ (Life.down_sqsubset β')
    have hd' : ∀ ls', wpTS ls' d (fun ls'' => vP (.lolli (.ref T) .unit) ls'' δ) PMap.empty := by
      intro ls'
      have h := hd δ [] ls' PMap.empty hδ (gDenC_nil ls' δ)
      rwa [show substAll [] d = d from BoCa.Adequacy.psub_nil 0 d] at h
    exact withborR_spans_yields_cC hδ hbx hΔx hβ hT hB hP hNf hN hdc hd' S hRA o hf hoB ys
      hys (hy δ) ℓ v' ls ρ hrest

/-- **Under the kernel's `[handle]`, at an affine yield.** The body is handed to `handle_compatC`
unchanged, so the clause receives `κ` at the kernel's continuation type for an affine operation
(`kTy`): it may resume `κ` or drop it (`close`), which is T15.5's drop clause's premise. -/
theorem handleR_spans_yields {Δ : LifeCtx} {Γ Γ₁ Γr Γc : Ctx VTy} {S' : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {R : VTy} {ir ic : Nat}
    {x : LifeVar} {b : Lifetime.Life}
    (hb : Δ.Defines b) (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    (hside : ∃ b', Δ.Defines b' ∧ VOutlivesLe Δ b' T)
    {Nf : Expr} (hNf : closedAt 1 Nf = true)
    (hN : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.comp (.ret (.box (.var x) B))))
    {d : Expr} (hdc : closedAt 0 d = true) (hd : SemV Δ [] d (.lolli (.ref T) .unit))
    (hRA : ∀ o ∈ Row.ofEff n E 0 ++ S', o.abort = false ∧ o.q ≠ .unr)
    (o : OpSig) (hf : Row.find (Row.ofEff n E 0 ++ S') o.n o.i = some o) (hoB : o.B = .unit)
    (ys : List Val) (hys : ∀ y ∈ ys, closedAt 0 y.1 = true)
    (hy : ∀ δ, ∀ y ∈ ys, ∀ ls, vC true o.A ls δ y PMap.empty)
    (hcb : closedAt 0 (cbV o.n o.i ys Nf).1 = true)
    (hsp : Ctx.SplitP Γ Γ₁ [⟨.ref T, true⟩]) (hsp₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S' (.tensor (.ref T) B) R))
    (hc : Ctx.SoloP Γc ic (clausesTy S' R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S', o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) :
    SemC Δ Γ (hndTerm n (E.map Prod.fst) ir ic
      (.app (.app (.val (withborUV d)) (.var 0)) (.val (cbV o.n o.i ys Nf)))) (CTy.effOf S' R) :=
  handle_compatC hsp hsp₁ hr hc hn0 hnS hlen
    (withborR_spans_yields_sem hb hbx hΔx hT hB hside hNf hN hdc hd _ hRA o hf hoB ys hys hy
      hcb)

namespace Drop
open GhostEnd.Instance (nfEx d_nfEx ys)

/-- `yield : I32 ↠ 1`, affine and resuming. -/
def yieldAff : OpSig := ⟨7, 0, .aff, .int .w32, .unit⟩

/-- **A lend spanning two affine yields**, every hypothesis discharged. The finaliser is
`free : Ref 1 ⊸ 1`. -/
theorem spans_two_affine_yields (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true .unit ls δ v)
      (cC (CTy.effOf [yieldAff] (.tensor (.ref .unit) .unit)) ls δ
        (.app (.app (.val (withborUV (.val (.prim .free)))) (.val (.loc l)))
          (.val (cbV yieldAff.n yieldAff.i ys nfEx)))) := by
  have hδ : LifeCtx.empty.Models δ := fun x u h => by
    simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  obtain ⟨β, hβ⟩ : ∃ β, LifeCtx.empty.meetOfDom.interp δ = some β :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)
  refine withborR_spans_yields_cC (Δ := LifeCtx.empty) (x := 0) hδ (by decide)
    (fun y u h => by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h) hβ
    (by simp [VFree]) (by simp [VFree]) (βP := ⊤) ?_ (by decide) d_nfEx (by decide) ?_
    [yieldAff] ?_ yieldAff (by simp [Row.find, yieldAff]) rfl ys
    (by simp [ys]; decide) ?_ l v ls
  · intro ls w σ h
    rw [h.1]; exact ResU.inStratum_empty _
  · intro ls'
    have h := fundamentalC (ℍ := ℍ) (CDerives.free (Δ := LifeCtx.empty) (Γ := []) (A := .unit) .nil)
      δ [] ls' PMap.empty hδ (gDenC_nil ls' δ)
    rwa [show substAll [] (Expr.val (Val.prim .free)) = .val (.prim .free) from
      BoCa.Adequacy.psub_nil 0 _] at h
  · intro o ho
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨by decide, by decide⟩
  · intro y hy ls
    simp only [ys, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨rfl, 1, rfl⟩
    · exact ⟨rfl, 2, rfl⟩

end Drop

end GhostEnd
