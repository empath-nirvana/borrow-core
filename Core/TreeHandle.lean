import Core.TreeHeap
import Core.EffRules

/-!
# A scheduler handler at the step-indexed relation over the tree world  `[spec §62]`

`[handle]` at `cerwpT` over the tree, for the handler a program runs at its top (the scheduler):
the handled computation at `cerwpT` at a table `T` whose operations are all the handler's, the
handler's clauses at the empty table. It is `SI/HandleN.lean`'s `erwp_handle` (spike, chain
world) re-proved at `twp`: by induction on the index, with no `hdv` premise, `κ` resumed at
`k′ < k` by the induction hypothesis. What the tree adds is the frame.

**The frame at a resume.** `contShareT` resumes a stored continuation under frames meeting
`fdAt en v F O′`: the stored branch's frame condition and the entry's `fd` at the records it owns
there. A clause that resumes `κ` beside a state it keeps puts that state in the resumed run's
frame. The clause is told what the frame of the resumed run must avoid as a set of locations `M`
(`fdMask M`: valid, and nothing at `M` at any depth): the lent and escrow locations of every record
the branch has owned at a resume (`recMask`). The table's `fd` must follow from that (`fdJoinT`),
and so does the stored branch's frame condition, by induction (`cerwpT_schedHandle`'s `hFe`).

**What the frame avoids is learnt at the stop** (`twp_bind_fd`). A run whose frame avoids the
masks of the records it starts with ends with a frame that avoids the masks of the records it ends
with: where a mask was added, `EndT`'s `MaskDiff` clause says the frame holds nothing; elsewhere
the frame is the start's re-read (`noneAt_recMask_end`). So a record the run opened during the
segment is avoided by the frame as soon as it exists: this is how the clause that receives `κ` at
the stop knows that its own frame holds nothing of the stopped branch's lends.

The cancel steps of `κ` (`twpE_kappa_cancel`, `twpE_kappaC_cancel`) and its cell
(`twpE_kappaCell`, `twpE_kappaC_resume`) are the spike's `erwp_kappa_*` at `twp`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE freeE)

/-! ### Frames that avoid a set of locations -/

/-- **The frame avoids `M`**: it is valid and its flattening holds nothing at `M`. -/
def fdMask (M : BoCa.Loc → Prop) : TFrame := fun _ ρf => ResUT.Valid ρf ∧ NoneAt M ρf

/-- Avoiding a set of locations is kept by re-reading. -/
theorem fdMask_mono (M : BoCa.Loc → Prop) : (fdMask M).Mono := by
  intro w w' ρ ρ' hE hr ⟨hv, hn⟩
  exact ⟨WitRel.ResUT.Valid.sim (W := rrRel _ _ _) hv hr.rsim, NoneAt.rr hE.1 hv hr hn⟩

theorem fdMask_empty (M : BoCa.Loc → Prop) (w : TWd) : fdMask M w (PMap.empty : TRes w.K) :=
  ⟨⟨_, flat_empty⟩, noneAt_empty M⟩

theorem fdMask_le {M M' : BoCa.Loc → Prop} (h : ∀ x, M x → M' x) {w : TWd} {ρf : TRes w.K}
    (hf : fdMask M' w ρf) : fdMask M w ρf :=
  ⟨hf.1, hf.2.mono h⟩

/-- **The resumer's guarantee at a join**: the frame holds nothing at the lent locations and the
escrows' exclusive locations of the records the resumed run owns. -/
def fdJoinT : BoCa.Val → (w : TWd) → List (FrameRecT w.K) → TRes w.K → Prop :=
  fun _ w O ρf => fdMask (recMask O) w ρf

/-- Conjunction of frame conditions. -/
def TFrame.and (F G : TFrame) : TFrame := fun w ρf => F w ρf ∧ G w ρf

theorem TFrame.and_mono {F G : TFrame} (hF : F.Mono) (hG : G.Mono) : (F.and G).Mono :=
  fun w w' ρ ρ' hE hr h => ⟨hF w w' ρ ρ' hE hr h.1, hG w w' ρ ρ' hE hr h.2⟩

/-! ### What the frame avoids at the end of a run -/

/-- **A record the run holds at its end is avoided by the frame** (item 4 of #781 slice (d)): the
frame at the start avoided the masks of the records the run started with; at the end the frame is
the start's re-read, and where the end's masks add a location `EndT`'s `MaskDiff` clause says the
frame holds nothing there. A lend the run opened during the segment is one such location. -/
theorem noneAt_recMask_end {K K' : WCactus} {Θ : LocTy} (hE : K.Ext K') {O₀ : List (FrameRecT K)}
    {O' : List (FrameRecT K')} {ρf : TRes K} {ρf' : TRes K'} (hv : ResUT.Valid ρf)
    (hr : RR Θ ρf ρf') (h₀ : NoneAt (recMask O₀) ρf)
    (hd : NoneAt (MaskDiff (recMask O₀) (recMask O')) ρf') : NoneAt (recMask O') ρf' := by
  refine ((NoneAt.rr hE hv hr h₀).or hd).mono fun x hx => ?_
  by_cases h : recMask O₀ x
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨hx, h⟩)

/-- **Bind, the continuation told what the frame avoids.** As `twp_bind`; the run of `e` is at
a frame condition `Fe` that every `F`-frame meets, the `F`-frames avoid the masks of the records
`e` starts with (`hJ`), and the continuation from `K[t]` is at `F` with the frame avoiding the
masks of the records the run of `e` ended with (`noneAt_recMask_end`). -/
theorem twp_bind_fd {F Fe : TFrame} (hFm : F.Mono) (hFe : ∀ w ρf, F w ρf → Fe w ρf)
    {P Q : TPost} (K : Kont) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hJ : ∀ w₀ ρf, F w₀ ρf → NoneAt (recMask O) ρf)
    (he : twp (ℍ := ℍ) Fe P n w ls O e ρ)
    (hk : ∀ k, k ≤ n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t
      (ρ' : TRes w'.K), P k w' ls' O' t ρ' →
      twp (ℍ := ℍ) (F.and (fdMask (recMask O'))) Q k w' ls' O' (K.plug t) ρ') :
    twp (ℍ := ℍ) F Q n w ls O (K.plug e) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' E hj hrun hfin
  have go : ∀ j₁ j₂ μ₁ t, j₁ + j₂ = j → StepsN (ℍ := ℍ) j₁ μ e μ₁ t → Final (ℍ := ℍ) μ₁ t →
      StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E → EndT Q (n - j) w₀ ρ₀ O₀ ρf psF μ' E := by
    intro j₁ j₂ μ₁ t hjj hrun₁ hfin₁ hrun₂
    obtain ⟨w₁, ρf₁, ρ₁, fρ₁, psF₁, ps₁, O₁, ls₁, g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
        g₁₁⟩ := he w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO (hFe _ _ hF) hf hc hS hR hI hfd j₁ μ₁ t
        (by omega) hrun₁ hfin₁
    have hcov : CovR (sem w₁.Θ) w₁.K ρ₁ := cov_of_comp g₄ g₇
    have hJ₀ : NoneAt (recMask O₀) ρf := (hJ w₀ ρf hF).mono fun x hx => (recMask_rr hO x).mpr hx
    have hF₁ : (F.and (fdMask (recMask O₁))) w₁ ρf₁ :=
      ⟨hFm _ _ _ _ g₀ g₁ hF, covf_valid g₄ g₇,
        noneAt_recMask_end g₀.1 (covf_valid hc hI) g₁ hJ₀ g₁₀⟩
    obtain ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, k₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀,
        k₁₁⟩ := hk (n - j₁) (Nat.sub_le _ _) w₁ ls₁ O₁ t ρ₁ g₈ w₁ ρ₁ ρf₁ fρ₁ ls₁ O₁ ps₁ psF₁ μ₁
        (TWd.Ext.refl _ _) (RR.refl hcov) (SRecsRR.refl g₆.cov_ls)
        (RecsRR.refl fun r hr => g₆.cov_ps r (g₅.left r hr)) hF₁ (ResUT.hash_symm g₃) g₄ g₅ g₆
        g₇ (fd_stepsN hrun₁ hfd) j₂ μ' E (by omega) hrun₂ hfin
    refine ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, g₀.trans g₁ k₀, RRw.trans k₀.1 g₁ k₁,
      g₂.trans k₀.1 k₂, k₃, k₄, k₅, k₆, k₇, ?_, UpdX.trans k₀.1 g₉ k₉, ?_, g₁₁.trans g₉ k₁₁⟩
    · rwa [show n - j₁ - j₂ = n - j by omega] at k₈
    · have hf₂ : NoneAt (MaskDiff (recMask O₀) (recMask O₁)) ρf₂ :=
        g₁₀.rr k₀.1 (covf_valid g₄ g₇) k₁
      exact (hf₂.or k₁₀).mono fun x hx => maskDiff_trans x hx
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    exact go j 0 μ' e' (by omega) hrun' hfin' (.refl _ _)
  · exact go j₁ j₂ μ₁ t hjj hrun₁ hirr hrun₂

/-! ### The top-level table -/

/-- A value in `Q`. -/
def valPost (Q : TPostV) : TPost := fun k w ls O t ρ => ∃ v : Val, t = v.1 ∧ Q k w ls O v ρ

/-- A postcondition over values, downward closed in the index. -/
def TPostV.Down (Q : TPostV) : Prop := ∀ n w ls O v ρ, Q (n + 1) w ls O v ρ → Q n w ls O v ρ

theorem valPost_down {Q : TPostV} (hQ : Q.Down) : (valPost Q).Down :=
  fun _ _ _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hQ _ _ _ _ _ _ hq⟩

/-- **At the empty table `cerwpT` is `twp` at its values**: nothing stops. -/
theorem cerwpTE_iff {Q : TPostV} {F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q F n w ls O e ρ ↔
      twp (ℍ := ℍ) F (valPost Q) n w ls O e ρ := by
  rw [cerwpT_eq]
  constructor
  · refine fun h => twp_mono (fun _ _ _ _ _ _ ht => ?_) h
    rcases ht with ht | ht
    · exact ht
    · exact (opTableT_empty_false ht).elim
  · exact fun h => twp_mono (fun _ _ _ _ _ _ ht => Or.inl ht) h

/-! ### Allocation at the run's own world -/

/-- An `own` cell holds no `mut` cell. -/
theorem not_holdsMut_own {K : WCactus} {l l' : BoCa.Loc} {v : BoCa.Val} :
    ¬ HoldsMut (ResUT.single l' (CellUT.ownOf (K := K) v)) l := by
  intro h
  cases h with
  | top e => obtain ⟨-, h⟩ := ResUT.single_get_eq_some e; cases h
  | deep e h =>
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
      cases h with
      | top e' => simp [CellUT.ownOf, CellUT.wit] at e'
      | deep e' _ => simp [CellUT.ownOf, CellUT.wit] at e'

/-- A `mut` cell a composite with an `own` cell holds is held by the other part. -/
theorem holdsMut_of_compS_own {K : WCactus} {a y : TRes K} {l' : BoCa.Loc} {v : BoCa.Val}
    (hc : ResUT.CompS a (ResUT.single l' (CellUT.ownOf v)) y) {l : BoCa.Loc}
    (h : HoldsMut y l) : HoldsMut a l := by
  classical
  have hal : a.get l' = none := ResUT.compatS_single_own (ResUT.CompatS.symm hc.1)
  have hyl : y.get l' = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hc hal, ResUT.single_get_self]
  cases h with
  | @top _ _ m e =>
      by_cases hk : l = l'
      · subst hk; rw [hyl] at e; cases e
      · rw [ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ hk)] at e
        exact .top e
  | @deep _ k _ ψ e h =>
      by_cases hk : k = l'
      · subst hk; rw [hyl] at e; cases e
        cases h with
        | top e' => simp [CellUT.ownOf, CellUT.wit] at e'
        | deep e' _ => simp [CellUT.ownOf, CellUT.wit] at e'
      · rw [ResUT.Comp.get_of_right_none hc (ResUT.single_get_ne _ hk)] at e
        exact .deep e h


/-- **Allocation at `twp`, read at the run's own world**: `twp_alloc` with the continuation at
the resource the run holds, every cell it may allocate at. -/
theorem twp_alloc_here {F : TFrame} {Q : TPost} (hQ : Q.Down) (Kc : Kont) (v : BoCa.Val)
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : ∀ (l : BoCa.Loc) (ρ₁ : TRes w.K), ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ₁ →
      twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.val (.loc l))) ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.app (.val (.prim .alloc)) (.val v))) ρ := by
  classical
  refine twp_alloc hQ Kc v fun w₀ ρ₀ ls₀ O₀ hE hr hl hO l ρ₁₀ hc₀ => ?_
  have hl₀ : ρ₀.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hc₀.1)
  have hlw : ρ.get l = none := (hr.1 l).mpr hl₀
  obtain ⟨ρ₁, hρ₁⟩ := (ResUT.compS_defined_iff ρ (ResUT.single l (CellUT.ownOf v))).mpr
    (compatS_single_of_get_noneT hlw)
  have hrs : RR (sem w₀.Θ) (ResUT.single l (CellUT.ownOf (K := w.K) v))
      (ResUT.single l (CellUT.ownOf (K := w₀.K) v)) := by
    refine ⟨fun m => ?_, fun m ψ ψ' e e' => ?_⟩
    · by_cases hm : m = l
      · subst hm; simp
      · simp only [ResUT.single_get_ne _ hm]
    · obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
      exact RC.own _ _
  obtain ⟨ρ₁', hc', hr'⟩ := RR.compS hr hrs hρ₁
  obtain rfl := ResUT.CompS.functional hc' hc₀
  have hE₁ : w.Ext w₀ ρ₁ := ⟨hE.1, fun m hm => hE.2 m (holdsMut_of_compS_own hρ₁ hm)⟩
  exact twp_kripke hE₁ hr' hl hO (h l ρ₁ hρ₁)

end BoCa.Fig16.Tree.Wp

end
