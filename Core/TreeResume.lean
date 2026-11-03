import Core.TreeHeadlines

/-!
# A stored continuation stays resumable across another branch's run  `[spec §62]`

**The guarantee.** A continuation `κ` the scheduler holds (`KapSchedT`, at its stop's world `w₁`,
stop list `ls₁`, records `O₁` and share `ρ₁`) beside a branch that runs (`twp`, stepping and
opening and ending lends of its own, to an `EndT` end) can still be resumed after that run, at the
world `w′` and the list `ls′` the run ends in, through `KapSchedT`'s own resume clause
(`contShareT_resume` for a bare share). The only condition on the run is that **it owns no record
when it starts** (`twp … ls [] e ρ`): every record it ends is one it opened during the run. The
resume premises are all derived: the share and `κ`'s records re-read by the frame
(`twp_frame`), the stop list re-read and kept by the run's end list (`twp_keepsList`), and
`extFT` at that re-reading because it keeps every record (`extFT_of_sub`).

**The key step, `twp_keepsList`**: a run that owns no record at its start ends at a list holding
the re-reading of every record of its start list (`SRecsIn`). Each record of the start list is in
the lineage of a record proper (`TIT`'s lineage closure at the start); the run owns none, so that
record proper is the frame's (`SplitT`); `EndT` re-reads the frame's records into the end's records
proper (`RecsRR psF psF′`, `SplitT ps′ O′ psF′`); a lineage path is re-read
(`LinPathT.rr_fwd`); and the end list is the lineage closure of the end's records proper (`TIT`
at the end). No case split on what the run did: it may open, end and re-type anything of its own.

**Why the whole list and not only the records the share reads.** `contShareT` and `KapSchedT`
resume at a re-reading of the *whole* stop list (`SRecsRR ls₁ lsR`). A record of `ls₁` that the
run owns may be ended and its escrow's `mut` locations re-typed, and then no re-reading of `ls₁`
exists at the end at all; so the ownership condition is on every record of the list, not on those
`κ`'s share reads (`ExtLT`, R4). With every record kept, `extFT lsR ls′` holds at every share
(`extFT_of_sub`), so R4 is not needed for this theorem.

**What the condition rules out.** A runner that owns a record of `κ`'s stop list: in particular
the lender of a lend `κ`'s share holds a view of. Whether such a run leaves `κ` resumable is not
derived here, and no obstruction is verified. What is derived (`kapStored_end_refused`, R2 at the
stored branch): in a configuration of the cactus invariant, such a runner cannot validly end a lend
while `κ`'s share holds part of it.

**Existence of re-readings** (`RecRR.exists_retype`, `RecsRR.exists_retype`,
`SRecsRR.exists_retype`): a record list covered at a world has a re-reading at every extension
whose code typing agrees with the world's on the escrows' `mut` cells. The agreement is supplied
when each record's lend cell is held by a resource the extension carries (`RecsRR.exists_held`):
a lend cell's witness is the escrow (`LeInvT`), and `TWd.Ext` carries `AgreeOn` of the carried
resource to every witness at depth.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

/-! ### Re-readings of record lists exist -/

/-- **A record has a re-reading** at every tree extension whose code typing agrees with the
record's world on its escrow's `mut` cells. -/
theorem RecRR.exists_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') (r : FrameRecT K)
    (hc : CovR (sem Θ) K r.R) (hag : AgreeOn Θ Θ' r.R) :
    ∃ r' : FrameRecT K', RecRR Θ' r r' := by
  obtain ⟨R', hR', -⟩ := RR.exists_retype hE hc hag
  exact ⟨⟨r.le, r.v, R', r.T⟩, rfl, rfl, rfl, hR'⟩

/-- **A record list has a re-reading**, under the same conditions on every escrow. -/
theorem RecsRR.exists_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K')
    {rs : List (FrameRecT K)} (hc : ∀ r ∈ rs, CovR (sem Θ) K r.R)
    (hag : ∀ r ∈ rs, AgreeOn Θ Θ' r.R) : ∃ rs' : List (FrameRecT K'), RecsRR Θ' rs rs' := by
  induction rs with
  | nil => exact ⟨[], .nil⟩
  | cons r rs ih =>
      obtain ⟨r', hr'⟩ := RecRR.exists_retype (K' := K') hE r (hc r List.mem_cons_self)
        (hag r List.mem_cons_self)
      obtain ⟨rs', hrs'⟩ := ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))
        (fun q hq => hag q (List.mem_cons_of_mem _ hq))
      exact ⟨r' :: rs', .cons hr' hrs'⟩

/-- **A tagged list has a re-reading**, tags kept. -/
theorem SRecsRR.exists_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K')
    {ls : List (SRecT K)} (hc : ∀ x ∈ ls, CovR (sem Θ) K x.1.R)
    (hag : ∀ x ∈ ls, AgreeOn Θ Θ' x.1.R) : ∃ ls' : List (SRecT K'), SRecsRR Θ' ls ls' := by
  induction ls with
  | nil => exact ⟨[], .nil⟩
  | cons x ls ih =>
      obtain ⟨r', hr'⟩ := RecRR.exists_retype (K' := K') hE x.1 (hc x List.mem_cons_self)
        (hag x List.mem_cons_self)
      obtain ⟨ls', hls'⟩ := ih (fun q hq => hc q (List.mem_cons_of_mem _ hq))
        (fun q hq => hag q (List.mem_cons_of_mem _ hq))
      exact ⟨(r', x.2) :: ls', .cons ⟨hr', rfl⟩ hls'⟩

/-- **The agreement from a carried resource**: a record whose lend cell a resource `ρ` holds at
the top has its escrow inside that cell's witness, so an extension carrying `ρ` agrees on it. -/
theorem RecsRR.exists_held {w w' : TWd} {ρ : TRes w.K} (hE : w.Ext w' ρ)
    {rs : List (FrameRecT w.K)} (hc : ∀ r ∈ rs, CovR (sem w.Θ) w.K r.R)
    (hheld : ∀ r ∈ rs, ∃ ψ : TCell w.K, ρ.get r.le = some ψ ∧ ψ.wit = r.R) :
    ∃ rs' : List (FrameRecT w'.K), RecsRR w'.Θ rs rs' :=
  RecsRR.exists_retype hE.1 hc fun r hr => by
    obtain ⟨ψ, e, hw⟩ := hheld r hr
    rw [← hw]; exact hE.2.wit e

/-! ### A list carried into another -/

/-- **Every record of `ls` has its re-reading in `ls′`.** Tags are not compared: a resume reads the
stop list through `SRecsRR` (tags kept by construction, `SRecsIn.exists_srecsRR`) and the resume
list through `extFT`, which reads records only. -/
def SRecsIn {K K' : WCactus} (Θ' : CodeTy) (ls : List (SRecT K)) (ls' : List (SRecT K')) :
    Prop :=
  ∀ r ∈ rsOfT ls, ∃ r' ∈ rsOfT ls', RecRR Θ' r r'

theorem SRecsIn.of_srecsRR {K K' : WCactus} {Θ' : CodeTy} {ls : List (SRecT K)}
    {ls' : List (SRecT K')} (h : SRecsRR Θ' ls ls') : SRecsIn Θ' ls ls' :=
  fun _ hr => h.mem_fwd hr

theorem SRecsIn.refl {K : WCactus} {Θ : CodeTy} {ls : List (SRecT K)}
    (h : ∀ x ∈ ls, CovR (sem Θ) K x.1.R) : SRecsIn (K' := K) Θ ls ls :=
  .of_srecsRR (SRecsRR.refl h)

theorem SRecsIn.trans {K₁ K₂ K₃ : WCactus} (hE : K₂.Ext K₃) {Θ₂ Θ₃ : CodeTy}
    {ls₁ : List (SRecT K₁)} {ls₂ : List (SRecT K₂)} {ls₃ : List (SRecT K₃)}
    (h : SRecsIn Θ₂ ls₁ ls₂) (h' : SRecsIn Θ₃ ls₂ ls₃) : SRecsIn Θ₃ ls₁ ls₃ := fun r hr => by
  obtain ⟨r₂, h₂, e₂⟩ := h r hr
  obtain ⟨r₃, h₃, e₃⟩ := h' r₂ h₂
  exact ⟨r₃, h₃, RecRR.trans hE e₂ e₃⟩

/-- **A list carried into `ls′` has a re-reading whose records are all in `ls′`.** -/
theorem SRecsIn.exists_srecsRR {K K' : WCactus} {Θ' : CodeTy} {ls' : List (SRecT K')} :
    ∀ {ls : List (SRecT K)}, SRecsIn Θ' ls ls' →
      ∃ lsR : List (SRecT K'), SRecsRR Θ' ls lsR ∧ ∀ r ∈ rsOfT lsR, r ∈ rsOfT ls'
  | [], _ => ⟨[], .nil, fun _ h => by simp [rsOfT] at h⟩
  | x :: ls, h => by
      obtain ⟨r', hr', e⟩ := h x.1 (by simp [rsOfT])
      obtain ⟨lsR, hR, hsub⟩ := SRecsIn.exists_srecsRR (ls := ls)
        (fun r hr => h r (by simp only [rsOfT, List.map_cons, List.mem_cons] at hr ⊢; exact Or.inr hr))
      refine ⟨(r', x.2) :: lsR, .cons ⟨e, rfl⟩ hR, fun r hr => ?_⟩
      simp only [rsOfT, List.map_cons, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact hr'
      · exact hsub r hr

/-! ### Records a run keeps -/

/-- **A record in the lineage of a frame record is kept**: at an end where the frame's records are
re-read into the records proper, its re-reading is in the end's list. -/
theorem keep_frameRooted {K K' : WCactus} {Θ' : CodeTy} {tc' : TChoice K'} {W' : TRes K'}
    {psF : List (FrameRecT K)} {psF' ps' O' : List (FrameRecT K')} {ls' : List (SRecT K')}
    (hF : RecsRR Θ' psF psF') (hS : SplitT ps' O' psF') (hT : TWNT K' Θ' tc' W' ps' (rsOfT ls'))
    {r : FrameRecT K} (hr : ∃ p ∈ psF, DescRT p r) : ∃ r' ∈ rsOfT ls', RecRR Θ' r r' := by
  obtain ⟨p, hp, path, hpath⟩ := hr
  obtain ⟨p', hp', hpp'⟩ := forall₂_mem_left hF hp
  obtain ⟨r', hrr', hpath'⟩ := hpath.rr_fwd hpp'
  exact ⟨r', (hT.inv.2.2.2.2.2.2.1 r').mpr ⟨p', hS.right p' hp', path, hpath'⟩, hrr'⟩

/-- **A record of the list whose roots are all the frame's is rooted in the frame**: the list is
the lineage closure of the records proper (`TIT`). -/
theorem frameRooted_of_notRunner {K : WCactus} {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps O psF : List (FrameRecT K)} {ls : List (SRecT K)} (hS : SplitT ps O psF)
    (hT : TWNT K Θ tc W ps (rsOfT ls)) {r : FrameRecT K} (hr : r ∈ rsOfT ls)
    (hO : ∀ p ∈ O, ¬ DescRT p r) : ∃ p ∈ psF, DescRT p r := by
  obtain ⟨p, hp, hd⟩ := (hT.inv.2.2.2.2.2.2.1 r).mp hr
  rcases (hS.1 p).mp hp with h | h
  · exact (hO p h hd).elim
  · exact ⟨p, h, hd⟩

/-- **A run that owns no record at its start keeps every record of its start list**: it ends at a
world extending its start's tree, at a list holding the re-reading of every record of `ls`. -/
theorem twp_keepsList {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {e : Expr} {ρ : TRes w.K} (h : twp (ℍ := ℍ) F Q n w ls [] e ρ) :
    twp (ℍ := ℍ) F (fun k w' ls' O' t ρ' =>
      Q k w' ls' O' t ρ' ∧ w.K.Ext w'.K ∧ SRecsIn w'.Θ ls ls') n w ls [] e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  cases hO
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ := h w₀ ρ₀ ρf fρ ls₀ [] ps psF μ hE hr hl .nil hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  refine ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇,
    ⟨g₈, WCactus.Ext.trans hE.1 g₀.1, fun r hr' => ?_⟩, g₉, g₁₀, g₁₁⟩
  obtain ⟨r₀, hr₀, e₀⟩ := hl.mem_fwd hr'
  obtain ⟨r', hr'', e'⟩ := keep_frameRooted g₂ g₅ g₆.1
    (frameRooted_of_notRunner hS hR.1 hr₀ (fun _ h => by cases h))
  exact ⟨r', hr'', RecRR.trans g₀.1 e₀ e'⟩

/-! ### Resuming at a list the stop list is carried into -/

/-- **A share resumed at any list its stop list is carried into**: the re-reading of the stop list
exists there (`SRecsIn.exists_srecsRR`) and `extFT` admits the list, which keeps all of it. -/
theorem contShareT_resume_in {en : OpEntT} {F : TFrame} {k : Nat} {w w' : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ls' : List (SRecT w'.K)}
    {O' : List (FrameRecT w'.K)} {K : Kont} {v : Val} {Ψ : ContT} {ρ : TRes w.K}
    {ρ' : TRes w'.K} (h : contShareT en F k w ls O K v Ψ ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hl : SRecsIn w'.Θ ls ls') (hO : RecsRR w'.Θ O O')
    {k' : Nat} (hk : k' < k) {a : Val} {σ σ' : TRes w'.K} (hB : en.PBv v k' w' ls' a σ)
    (hc : ResUT.CompS ρ' σ σ') : Ψ (fdAt en v F O') w' O' k' ls' (K.plug (.val a)) σ' := by
  obtain ⟨lsR, hlR, hsub⟩ := hl.exists_srecsRR
  exact contShareT_resume h hE hr hlR (extFT_of_sub hsub ρ') hO hk hB hc

/-- **`κ` held at a later world**: captured at `w₁` (`KapSchedT`), its share and records re-read at
`w`, its stop list carried into `w`'s list `ls`. -/
def KapAtT (Qout : TPostV) (M : BoCa.Loc → Prop) (en : OpEntT) (k : Nat) (v κ : Val) (w : TWd)
    (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (ρ : TRes w.K) : Prop :=
  ∃ (w₁ : TWd) (ls₁ : List (SRecT w₁.K)) (O₁ : List (FrameRecT w₁.K)) (ρ₁ : TRes w₁.K),
    KapSchedT (ℍ := ℍ) Qout M en k w₁ ls₁ O₁ v κ ρ₁ ∧ w₁.Ext w ρ₁ ∧
      RRw (w := w₁) (w' := w) ρ₁ ρ ∧ RecsRR w.Θ O₁ O ∧ SRecsIn w.Θ ls₁ ls

/-- At its stop, `κ` is held there. -/
theorem KapAtT.of_stop {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat} {v κ : Val}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : KapSchedT (ℍ := ℍ) Qout M en k w ls O v κ ρ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) (hO : ∀ r ∈ O, CovR (sem w.Θ) w.K r.R) :
    KapAtT (ℍ := ℍ) Qout M en k v κ w ls O ρ :=
  ⟨w, ls, O, ρ, h, TWd.Ext.refl _ _, RR.refl hcov, RecsRR.refl hO, SRecsIn.refl hls⟩

/-- **`κ` held at `w` is resumed at `w`, at its list `ls`**, at every answer the entry accepts,
under every frame condition whose frames avoid `M`. -/
theorem KapAtT.resume {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat} {v κ : Val}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : KapAtT (ℍ := ℍ) Qout M en k v κ w ls O ρ) {k' : Nat} (hk : k' < k) {a : Val}
    {σ σ' : TRes w.K} (hB : en.PBv v k' w ls a σ) (hc : ResUT.CompS ρ σ σ') {F' : TFrame}
    (hF'm : F'.Mono) (hF'M : ∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout F' k' w ls O
      (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val a)) σ' := by
  obtain ⟨w₁, ls₁, O₁, ρ₁, hK, hE, hr, hO, hl⟩ := h
  obtain ⟨lsR, hlR, hsub⟩ := hl.exists_srecsRR
  exact hK.2 w ρ lsR ls O hE hr hlR (extFT_of_sub hsub ρ) hO k' hk a σ σ' hB hc F' hF'm hF'M

/-- `κ` held at `w` is held at every extension of `w`, its list carried. -/
theorem KapAtT.kripke {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat} {v κ : Val}
    {w w' : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    {ls' : List (SRecT w'.K)} {O' : List (FrameRecT w'.K)} {ρ' : TRes w'.K}
    (h : KapAtT (ℍ := ℍ) Qout M en k v κ w ls O ρ) (hE : w.Ext w' ρ)
    (hr : RRw (w := w) (w' := w') ρ ρ') (hO : RecsRR w'.Θ O O') (hl : SRecsIn w'.Θ ls ls') :
    KapAtT (ℍ := ℍ) Qout M en k v κ w' ls' O' ρ' := by
  obtain ⟨w₁, ls₁, O₁, ρ₁, hK, hE₁, hr₁, hO₁, hl₁⟩ := h
  exact ⟨w₁, ls₁, O₁, ρ₁, hK, hE₁.trans hr₁ hE, RRw.trans hE.1 hr₁ hr, hO₁.trans hE.1 hO,
    hl₁.trans hE.1 hl⟩

/-! ### The resumability theorem -/

/-- **Another branch's run keeps a stored continuation resumable.** `κ` is held at `w` with its
list `ls` (`KapAtT`), its share `ρκ` and records `Oκ` beside a run of `e` from `ρ₁` that owns no
record at its start. At every end of the run, at the world `w′` and list `ls′` it ends in, the run's
part is in `P` and `κ` is held there (`KapAtT` at `w′`, `ls′`), so `KapAtT.resume` resumes it.

The frame obligation `hF` and the coverage `hcov` are `twp_frame`'s. -/
theorem twp_keepsKap {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {k : Nat} {v κ : Val}
    {F F₁ : TFrame} {P : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {Oκ : List (FrameRecT w.K)} {e : Expr} {ρ₁ ρκ ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρκ ρ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hF : ∀ (w₀ : TWd) (ρf ρ₂₀ y : TRes w₀.K), w.Ext w₀ ρκ → RRw (w := w) (w' := w₀) ρκ ρ₂₀ →
      F w₀ ρf → ResUT.CompS ρf ρ₂₀ y → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls [] e ρ₁) (hκ : KapAtT (ℍ := ℍ) Qout M en k v κ w ls Oκ ρκ) :
    twp (ℍ := ℍ) F (fun k₁ w' ls' O' t ρ' => ∃ (O₁ O₂ : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = O₁ ++ O₂ ∧ ResUT.CompS a b ρ' ∧ P k₁ w' ls' O₁ t a ∧
        KapAtT (ℍ := ℍ) Qout M en k v κ w' ls' O₂ b) n w ls Oκ e ρ := by
  obtain ⟨w₁, ls₁, O₁, ρκ₁, hK, hE₁, hr₁, hO₁, hl₁⟩ := hκ
  let R : TRProp := fun w' O ρ' =>
    w₁.Ext w' ρκ₁ ∧ RRw (w := w₁) (w' := w') ρκ₁ ρ' ∧ RecsRR w'.Θ O₁ O
  have hRm : R.Mono := fun _ _ _ _ _ _ hE hr hO ⟨a, b, c⟩ =>
    ⟨a.trans b hE, RRw.trans hE.1 b hr, c.trans hE.1 hO⟩
  have h := twp_frame (R := R) hRm (O₁ := []) (O₂ := Oκ) (fun _ h => by cases h) hcρ hcov hF
    (twp_keepsList hwp) ⟨hE₁, hr₁, hO₁⟩
  refine twp_mono (fun k₁ w' ls' O' t ρ' hp => ?_) h
  obtain ⟨Oa, Ob, a, b, hO', hc, ⟨hP, hKx, hls⟩, hRb⟩ := hp
  exact ⟨Oa, Ob, a, b, hO', hc, hP, w₁, ls₁, O₁, ρκ₁, hK, hRb.1, hRb.2.1, hRb.2.2,
    hl₁.trans hKx hls⟩

/-! ### Where it must refuse: R2 at the stored branch -/

/-- **A lend a stored `κ`'s share holds part of is not ended.** In a configuration of the cactus
invariant where `κ` is a branch `(ρκ, Oκ)` and its share fails `FdEsc` at a record proper `p`, the
lender's piece `ℓ ↦ own(v) ● R` composes with no rest of the world containing `κ` to a valid world.
It is R2 (`r2_endBlockedByHolder`) at `b := (ρκ, Oκ)`: the runner `twp_keepsKap` excludes (one
owning a record of `κ`'s list) is, when that record is a lend `κ` holds part of, a runner whose
end of it no valid configuration admits. -/
theorem kapStored_end_refused {w : TWd} {bs : List (TBranch w.K)} {ns : List Life}
    {W : TRes w.K} {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : Heap}
    (hI : CactusInvT w bs ns W ps ls μ) {ρκ : TRes w.K} {Oκ : List (FrameRecT w.K)}
    (hκ : (ρκ, Oκ) ∈ bs) {p : FrameRecT w.K} (hp : p ∈ ps) (hfd : ¬ FdEsc p.le p.R ρκ)
    {s : TSet} (hs : p.R.InStratum s) {Y Yr X' : TRes w.K}
    (hW : ResUT.CompS (ResUT.single p.le (CellUT.immOf s p.v p.R hs)) Y W)
    (hY : ResUT.CompS ρκ Yr Y)
    (hX : ResUT.CompS (ResUT.single p.le (CellUT.ownOf p.v)) p.R X') :
    ¬ ∃ W', ResUT.CompS X' Y W' ∧ ResUT.Valid W' :=
  r2_endBlockedByHolder w bs ns W ps ls μ hI (ρκ, Oκ) hκ p hp hfd s hs Y Yr X' hW hY hX

end BoCa.Fig16.Tree.Wp

end
