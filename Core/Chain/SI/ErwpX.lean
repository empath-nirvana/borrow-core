import Core.Chain.SI.ErwpN
import Core.Chain.SI.XRes

/-!
# The one relation: `erwp` over `WRes × GRes` at a mask  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 1, with the mask an index of the relation, as in Iris's
`WP_E e {Q}`. `erwpX Φ M Tb Q n ls e x` is `erwp`'s definition (`SI/ErwpN.lean`) over
`XRes = WRes × GRes` at the mask `M`.

**The run (`rwpGX`).** Frames range over `XRes`. At the start the frame and the resource compose
validly and are each `WF_C` at the world's counted set `C`; the resource is `MaskShallow` at `M`
(`ρ_P = ∅` at masked locations) and holds `M`'s authorities (`MaskAuth`); the frame holds only
copies at a location lent across stops (`MaskOff`).

**The end (`EndOKX`).** `EndOKG`'s conjuncts, with `↭` read outside `M` (`UpdVNm Φ k M.locs`);
the end ghost `g′` and the garbage's `gp` compose validly with the frame's (a change from the start
is frame-preserving because the end composes with the same frame); at the end world's counted set
`C′`, the end and the garbage are `WF_C′`, and the frame carries no lifetime counted at `C′` and
not at `C` (`NewNotCarried`), which with the frame's `WF_C` at the start is its `WF_C′`; the end and
the end with its garbage are `MaskShallow` at `M`, and the end holds `M`'s authorities; the
garbage holds only copies at a location lent across stops (`MaskOff`). The records and the list
are as at the start off the locations lent across stops (`RecAgree`, `ListAgree`). `C′` is passed
to the post.

**The guard.** Every run keeps the frame's world (`FrameKept xf.1`, the access guard G of
`rwpG`): the ghost part has no memory.

**The mask is fixed for the run**: bind composes at `M` (`UpdVNm.trans` at `M ∪ M = M`). The mask
grows and shrinks only at a lend's open and end (`SI/LendX.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-- A proposition over the one relation's resources. -/
abbrev XProp : Type := XRes → Prop

/-- A postcondition over terms, at the counted set and the index. -/
abbrev PostGX : Type := Set Life → Nat → List SRec → Expr → XProp

theorem ghost_ac₁ (a b c : GRes) : a + b + c = a + (c + b) := by
  ext <;> simp <;> ring

theorem ghost_ac₂ (a b c d : GRes) : a + b + (c + d) = a + (c + (b + d)) := by
  ext <;> simp <;> ring

/-- **`EndOK` at the one relation.** -/
def EndOKX (Φ : LocFam) (M : Mask) (Q : PostGX) (k : Nat) (ls : List SRec) (x xf : XRes)
    (ps : List FrameRec) (μ' : Heap) (t : Expr) : Prop :=
  ∃ (ρ' ρp fρ' fρ'p π : WRes) (g' gp : GRes) (ps' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' xf.1 ∧ ResU.CompS xf.1 ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
    ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
    ResU.CompS ρ' ρp π ∧ UpdVNm Φ k M.locs x.1 π ∧ NoOwn ρp ∧
    TWNC fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
    RecAgree M ps' ps ∧ ListAgree M ls' ls ∧
    (xf.2 + (g' + gp)).Valid ∧
    NewNotCarried (xf.2 + x.2).counted (xf.2 + (g' + gp)).counted xf.1 ∧
    WFC (xf.2 + (g' + gp)).counted (ρ', g') ∧ WFC (xf.2 + (g' + gp)).counted (ρp, gp) ∧
    MaskShallow M.locs ρ' ∧ MaskShallow M.locs π ∧ MaskAuth M g' ∧ MaskOff M ρp ∧
    Q (xf.2 + (g' + gp)).counted k ls' t (ρ', g')

/-- **`wpG` at the step index over `WRes × GRes`, at the mask `M`.** -/
def rwpGX (Φ : LocFam) (M : Mask) (Q : PostGX) (n : Nat) (ls : List SRec) (e : Expr) : XProp :=
  fun x =>
    ∀ (xf : XRes) (fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash xf.1 x.1 → ResU.CompS xf.1 x.1 fρ → (xf.2 + x.2).Valid →
      WFC (xf.2 + x.2).counted xf → WFC (xf.2 + x.2).counted x →
      MaskShallow M.locs x.1 → MaskAuth M x.2 → MaskOff M xf.1 →
      TWNC fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Lower fρ μ → FinDom μ →
      ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' →
        FrameKept xf.1 μ' ∧ (Final (ℍ := ℍ) μ' e' → EndOKX Φ M Q (n - j) ls x xf ps μ' e')

/-- `rwpGX` at the frames whose world counts exactly `C`: what a continuation entered at a
world of counted set `C` owes. -/
def rwpGXat (Φ : LocFam) (M : Mask) (Q : PostGX) (n : Nat) (ls : List SRec) (e : Expr)
    (C : Set Life) : XProp :=
  fun x =>
    ∀ (xf : XRes) (fρ : WRes) (ps : List FrameRec) (μ : Heap), (xf.2 + x.2).counted = C →
      ResU.Hash xf.1 x.1 → ResU.CompS xf.1 x.1 fρ → (xf.2 + x.2).Valid →
      WFC (xf.2 + x.2).counted xf → WFC (xf.2 + x.2).counted x →
      MaskShallow M.locs x.1 → MaskAuth M x.2 → MaskOff M xf.1 →
      TWNC fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Lower fρ μ → FinDom μ →
      ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' →
        FrameKept xf.1 μ' ∧ (Final (ℍ := ℍ) μ' e' → EndOKX Φ M Q (n - j) ls x xf ps μ' e')

/-- G at a run's end: the post-configuration keeps the frame's world. -/
theorem EndOKX.frameKept {Φ : LocFam} {M : Mask} {Q : PostGX} {k : Nat} {ls : List SRec}
    {x xf : XRes} {ps : List FrameRec} {μ' : Heap} {t : Expr}
    (h : EndOKX Φ M Q k ls x xf ps μ' t) : FrameKept xf.1 μ' := by
  obtain ⟨_, _, fρ', fρ'p, _, _, _, _, _, _, h₂, h₃, h₄, h₅, _⟩ := h
  exact ((frameKept_lower h₅).of_compS h₄ (by obtain ⟨σ, hσ, -⟩ := h₅; exact ⟨σ, hσ⟩)).of_compS
    h₂ (hash_valid h₃).2

theorem rwpGX.at {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec} {e : Expr}
    {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M Q n ls e x) (C : Set Life) :
    rwpGXat (ℍ := ℍ) Φ M Q n ls e C x :=
  fun xf fρ ps μ _ => h xf fρ ps μ

/-! ### Downward closure and monotonicity -/

def PostGX.Down (Q : PostGX) : Prop := ∀ C n ls t x, Q C (n + 1) ls t x → Q C n ls t x

theorem PostGX.Down.le {Q : PostGX} (hQ : Q.Down) {m k : Nat} (h : m ≤ k) :
    ∀ C ls t x, Q C k ls t x → Q C m ls t x := by
  induction h with
  | refl => exact fun _ _ _ _ x => x
  | step _ ih => exact fun C ls t x h => ih C ls t x (hQ _ _ _ _ _ h)

theorem EndOKX.mono {Φ : LocFam} {M : Mask} {P Q : PostGX} {k k' : Nat} (hΦ : Φ.Down)
    (hk : k' ≤ k) {t : Expr} (hPQ : ∀ C ls x, P C k ls t x → Q C k' ls t x) {ls : List SRec}
    {x xf : XRes} {ps : List FrameRec} {μ' : Heap} (h : EndOKX Φ M P k ls x xf ps μ' t) :
    EndOKX Φ M Q k' ls x xf ps μ' t := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₁₉', h₂₀⟩ := h
  exact ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇.down hΦ hk, h₈, h₉,
    h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₁₉', hPQ _ _ _ h₂₀⟩

theorem rwpGX_le {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (hQ : Q.Down) {m n : Nat}
    (hmn : m ≤ n) {ls : List SRec} {e : Expr} {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M Q n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q m ls e x := by
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun
  have hr := h xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' (by omega) hrun
  exact ⟨hr.1, fun hfin => (hr.2 hfin).mono hΦ
    (by omega) (fun C _ y hy => hQ.le (by omega) C _ _ y hy)⟩

/-- `rwpGX_mono` reading the postcondition at the indices the runs leave, `≤ n`. -/
theorem rwpGX_mono_le {Φ : LocFam} {M : Mask} {P Q : PostGX} {n : Nat}
    (hPQ : ∀ C k, k ≤ n → ∀ ls t x, P C k ls t x → Q C k ls t x)
    {ls : List SRec} {e : Expr} {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M P n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun
  have hr := h xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun
  refine ⟨hr.1, fun hfin => ?_⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₁₉', h₂₀⟩ := hr.2 hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₁₉', hPQ _ _ (by omega) _ _ _ h₂₀⟩

theorem rwpGX_mono {Φ : LocFam} {M : Mask} {P Q : PostGX}
    (hPQ : ∀ C k ls t x, P C k ls t x → Q C k ls t x) {n : Nat}
    {ls : List SRec} {e : Expr} {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M P n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e x :=
  rwpGX_mono_le (fun C k _ => hPQ C k) h

/-! ### Final terms and steps -/

theorem rwpGX_zero {Φ : LocFam} {M : Mask} {Q : PostGX} {ls : List SRec} {e : Expr}
    {x : XRes} : rwpGX (ℍ := ℍ) Φ M Q 0 ls e x := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j _ _ hj
  omega

/-- **A final term in the postcondition.** -/
theorem rwpGX_here {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec} {e : Expr}
    {x : XRes} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : ∀ C, Q C n ls e x) : rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh hau _ hT htg hl hfd j μ' e' hj hrun
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  refine ⟨frameKept_of_lower hc hl, fun _ => ?_⟩
  have hvρ : ResU.Valid x.1 := (hash_valid hf).2
  refine ⟨x.1, PMap.empty, fρ, fρ, x.1, x.2, 0, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), ResU.comp_empty_right _, hl,
    ResU.comp_empty_right _, UpdVNm.refl Φ _ _ hvρ, noOwn_empty, hT, htg, RecAgree.refl _ _,
    ListAgree.refl _ _, ?_, ?_, ?_, ?_, hsh, ?_, hau, maskOff_emptyRes _, ?_⟩
  · simpa using hv
  · intro α h₁ h₂; simp at h₁; exact absurd h₁ h₂
  · simpa using hwx
  · intro α _ hc'; exact absurd hc' (not_carries_empty α)
  · simpa using hsh
  · simpa using h _

/-- **A final term in the postcondition**, at the world it was reached at. -/
theorem rwpGXat_here {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec}
    {e : Expr} {C : Set Life} {x : XRes} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : Q C n ls e x) : rwpGXat (ℍ := ℍ) Φ M Q n ls e C x := by
  intro xf fρ ps μ hC hf hc hv hwf hwx hsh hau _ hT htg hl hfd j μ' e' hj hrun
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  refine ⟨frameKept_of_lower hc hl, fun _ => ?_⟩
  have hvρ : ResU.Valid x.1 := (hash_valid hf).2
  refine ⟨x.1, PMap.empty, fρ, fρ, x.1, x.2, 0, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), ResU.comp_empty_right _, hl,
    ResU.comp_empty_right _, UpdVNm.refl Φ _ _ hvρ, noOwn_empty, hT, htg, RecAgree.refl _ _,
    ListAgree.refl _ _, ?_, ?_, ?_, ?_, hsh, ?_, hau, maskOff_emptyRes _, ?_⟩
  · simpa using hv
  · intro α h₁ h₂; simp at h₁; exact absurd h₁ h₂
  · simpa using hwx
  · intro α _ hc'; exact absurd hc' (not_carries_empty α)
  · simpa using hsh
  · simp only [GRes.add_zero]; rw [hC]; simpa using h

/-- **A step that is its configuration's only one, for free.** -/
theorem rwpGX_det {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (hQ : Q.Down) {n : Nat}
    {ls : List SRec} {e e' : Expr} {x : XRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : rwpGX (ℍ := ℍ) Φ M Q n ls e' x) : rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' E hj hrun
  cases hrun with
  | refl => exact ⟨frameKept_of_lower a₂ a₁₁, fun hfin => absurd (hdet _).1 (hfin _ e')⟩
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ hs
      have hr := h xf fρ ps _ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j' μ' E (by omega) t
      exact ⟨hr.1, fun hfin => (hr.2 hfin).mono hΦ
        (by omega) (fun C _ y hy => hQ.le (by omega) C _ _ y hy)⟩

/-! ### Bind at a fixed mask -/

/-- `rwpG_compose` at the one relation: the first run's end, then the continuation's run at the
frame together with the first run's garbage. The two `↭`s compose at `M ∪ M = M`. -/
theorem rwpGX_compose {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (K : Kont)
    {k₁ : Nat} {ls : List SRec} {x xf : XRes} {ps : List FrameRec} {μ₁ : Heap} {t : Expr}
    (hwf₀ : WFC (xf.2 + x.2).counted xf) (hoff₀ : MaskOff M xf.1)
    (hend : EndOKX Φ M (fun C k ls' t => rwpGXat (ℍ := ℍ) Φ M Q k ls' (K.plug t) C) k₁ ls x xf
      ps μ₁ t)
    (hfd₁ : FinDom μ₁) {j₂ : Nat} {μ' : Heap} {E : Expr} (hj : j₂ < k₁)
    (hrun : StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E) :
    FrameKept xf.1 μ' ∧ (Final (ℍ := ℍ) μ' E → EndOKX Φ M Q (k₁ - j₂) ls x xf ps μ' E) := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₆, h₇, h₉, hA, hB, hT', htg',
    hps', hls', hV, hN, hW', hWp, hS', hSπ, hAu, hOff, hC⟩ := hend
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp xf.1 ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS xf.1 ρp z := ResU.CompS.comm hzp
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  have hvz : z.Valid := (hash_valid hz).1
  have hG₁ : xf.2 + gp + g' = xf.2 + (g' + gp) := ghost_ac₁ _ _ _
  -- the continuation's premises, at the frame `(ρ_f ● ρp, g_f + gp)`
  have hV₂ : (xf.2 + gp + g').Valid := by rw [hG₁]; exact hV
  have hWf₂ : WFC (xf.2 + gp + g').counted (z, xf.2 + gp) := by
    rw [hG₁]; exact wfc_comp hfz (wfc_grow hwf₀ hN) hWp
  have hW₂ : WFC (xf.2 + gp + g').counted (ρ', g') := by rw [hG₁]; exact hW'
  have hr := hC (z, xf.2 + gp) fρ'p ps' μ₁ (by show (xf.2 + gp + g').counted = _; rw [hG₁]) hz
    hzY hV₂ hWf₂ hW₂ hS' hAu (maskOff_comp hfz hoff₀ hOff) hT' htg' h₇ hfd₁ j₂ μ' E hj hrun
  -- the continuation's frame `ρ_f ● ρp` keeps `ρ_f`
  refine ⟨hr.1.of_compS hfz hvz, fun hfin => ?_⟩
  obtain ⟨ρ'', ρpp, Y'', Y''p, π'', g'', gpp, ps'', ls'', k₁', k₂, k₃, k₆, k₇, k₉, kA, kB, kT,
    ktg, kps, kls, kV, kN, kW, kWp, kS', kSπ, kAu, kOff, kC⟩ := hr.2 hfin
  -- the W part, as `rwpG_compose`
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hfz (ResU.hash_symm k₁')
  obtain ⟨F, hF, hFp⟩ := compS_exch hfz k₂
  obtain ⟨ZZ, hZZ, hZF⟩ := (hash_shift ρpp ρp F).mp ⟨Y'', ResU.CompS.comm hFp, k₃⟩
  have hZZ' : ResU.CompS ρp ρpp ZZ := ResU.CompS.comm hZZ
  obtain ⟨ZZ₀, hZZ₀, hFZ₀⟩ := compS_reassoc hFp k₆
  have hFZ : ResU.CompS F ZZ Y''p := by
    rwa [ResU.CompS.functional hZZ₀ hZZ'] at hFZ₀
  obtain ⟨-, hpρ'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hfz k₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm k₃)
  obtain ⟨π₀, hπ₀, hpπ₀⟩ := (hash_shift ρp ρ'' ρpp).mpr ⟨d, hd, hdp⟩
  have hpπ : ResU.Hash ρp π'' := by rwa [ResU.CompS.functional hπ₀ k₉] at hpπ₀
  obtain ⟨Yn, hYn, -⟩ := hpπ.2
  obtain ⟨ZZ₁, hZZ₁, hρ''Z₀⟩ := compS_lcomm k₉ hYn
  have hρ''Z : ResU.CompS ρ'' ZZ Yn := by
    rwa [ResU.CompS.functional hZZ₁ hZZ'] at hρ''Z₀
  -- the ghost part
  have hG₂ : xf.2 + gp + (g'' + gpp) = xf.2 + (g'' + (gp + gpp)) := ghost_ac₂ _ _ _ _
  have hSp : MaskShallow M.locs ρp := maskShallow_right h₉ hA.2.2 hSπ
  refine ⟨ρ'', ZZ, F, Y''p, Yn, g'', gp + gpp, ps'', ls'', ResU.hash_symm hfρ'', hF, hZF, hFZ,
    k₇, hρ''Z, ?_, noOwn_compS hZZ' hB kB, kT, ktg, kps.trans hps', kls.trans hls', ?_, ?_, ?_,
    ?_, kS', maskShallow_comp hYn hSp kSπ, kAu, maskOff_comp hZZ' hOff kOff, ?_⟩
  · have := UpdVNm.trans hΦ (Nat.sub_le k₁ j₂) hA
      (updVNm_frame (ResU.CompS.comm h₉) hYn (ResU.hash_symm hpρ') hpπ hS' kSπ kA)
    rwa [Set.union_self] at this
  · rw [← hG₂]; exact kV
  · intro α hα hα₀
    by_cases h₁α : α ∈ (xf.2 + (g' + gp)).counted
    · exact hN α h₁α hα₀
    · rw [← hG₂] at hα
      rw [← hG₁] at h₁α
      exact fun hc => kN α hα h₁α (carries_comp_left hfz hvz hc)
  · rw [← hG₂]; exact kW
  · have hWp₂ : WFC (xf.2 + gp + (g'' + gpp)).counted (ρp, gp) := by
      refine wfc_grow (C := (xf.2 + gp + g').counted) (by rw [hG₁]; exact hWp)
        (fun α hα hα₁ hc => ?_)
      exact kN α hα hα₁ (carries_comp_right hfz hvz hc)
    rw [← hG₂]; exact wfc_comp hZZ' hWp₂ kWp
  · rw [← hG₂]; exact kC

/-- **Bind at any final term, at a fixed mask.** -/
theorem rwpGX_bind {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (K : Kont) {n : Nat}
    {ls : List SRec} {e : Expr} {x : XRes}
    (hw : rwpGX (ℍ := ℍ) Φ M (fun C k ls' t => rwpGXat (ℍ := ℍ) Φ M Q k ls' (K.plug t) C) n ls e
      x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls (K.plug e) x := by
  classical
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' E hj hrun
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hr := hw xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun'
    refine ⟨hr.1, fun hfin => ?_⟩
    have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    have h := (rwpGX_compose hΦ K a₄ a₈ (hr.2 hfin')
      (fd_stepsN hrun' a₁₂) (j₂ := 0) (by omega) (.refl _ _)).2 hfin
    simpa using h
  · have h := rwpGX_compose hΦ K a₄ a₈
      ((hw xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j₁ μ₁ t (by omega) hrun₁).2 hirr)
      (fd_stepsN hrun₁ a₁₂) (j₂ := j₂) (by omega) hrun₂
    rwa [show n - j₁ - j₂ = n - j by omega] at h

/-! ### The frame -/

/-- Two parts each carry their own fractions: every lifetime the pair counts that a part carries,
that part holds a fraction of. -/
def WFSplit (x₁ x₂ : XRes) : Prop :=
  ∀ α, 0 < (x₁.2 + x₂.2).tok α →
    (Carries x₁.1 α → 0 < x₁.2.tok α) ∧ (Carries x₂.1 α → 0 < x₂.2.tok α)

/-- The separating conjunction over `XRes`. -/
def sepX (P R : XProp) : XProp := fun x =>
  ∃ (ρ₁ ρ₂ : WRes) (g₁ g₂ : GRes), ResU.CompS ρ₁ ρ₂ x.1 ∧ x.2 = g₁ + g₂ ∧ P (ρ₁, g₁) ∧
    R (ρ₂, g₂)

/-- **The frame at any final term.** The framed part carries its own fractions (`WFSplit`), and the
inner part holds the mask's authorities. -/
theorem rwpGX_frame {Φ : LocFam} {M : Mask} {P : PostGX} (R : List SRec → XProp)
    (hR : ∀ ls ls', ListAgree M ls' ls → ∀ x, R ls x → R ls' x) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ₁ ρ₂ ρ : WRes} {g₁ g₂ : GRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hsplit : WFSplit (ρ₁, g₁) (ρ₂, g₂)) (hau₁ : MaskAuth M g₁) (hoff₂ : MaskOff M ρ₂)
    (hwp : rwpGX (ℍ := ℍ) Φ M P n ls e (ρ₁, g₁)) (hR₂ : R ls (ρ₂, g₂)) :
    rwpGX (ℍ := ℍ) Φ M (fun C k ls' t => sepX (P C k ls' t) (R ls')) n ls e (ρ, g₁ + g₂) := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh _ hoff hT htg hl hfd j μ' e' hj hrun
  obtain ⟨y, hy, hy₁⟩ := (hash_shift xf.1 ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  have hvρ : ρ.Valid := (hash_valid hf).2
  have hvy : y.Valid := (hash_valid hy₁).1
  have hG : xf.2 + g₂ + g₁ = xf.2 + (g₁ + g₂) := ghost_ac₁ _ _ _
  have hwx₁ : ∀ α, α ∈ (xf.2 + (g₁ + g₂)).counted → Carries ρ₁ α → 0 < g₁.tok α :=
    fun α hα hc₁ => (hsplit α (hwx α hα (carries_comp_left hcρ hvρ hc₁))).1 hc₁
  have hwx₂ : WFC (xf.2 + (g₁ + g₂)).counted (ρ₂, g₂) :=
    fun α hα hc₂ => (hsplit α (hwx α hα (carries_comp_right hcρ hvρ hc₂))).2 hc₂
  have a₃ : (xf.2 + g₂ + g₁).Valid := by rw [hG]; exact hv
  have a₄ : WFC (xf.2 + g₂ + g₁).counted (y, xf.2 + g₂) := by
    rw [hG]; exact wfc_comp hy hwf hwx₂
  have a₅ : WFC (xf.2 + g₂ + g₁).counted (ρ₁, g₁) := by rw [hG]; exact hwx₁
  have hsh₁ : MaskShallow M.locs ρ₁ := maskShallow_left hcρ hvρ hsh
  have hsh₂ : MaskShallow M.locs ρ₂ := maskShallow_right hcρ hvρ hsh
  have hr := hwp (y, xf.2 + g₂) fρ ps μ hy₁ hyfρ a₃ a₄ a₅ hsh₁ hau₁ (maskOff_comp hy hoff hoff₂)
    hT htg hl hfd j μ' e' hj hrun
  -- the inner frame `ρ_f ● ρ₂` keeps `ρ_f`
  refine ⟨hr.1.of_compS hy hvy, fun hfin => ?_⟩
  obtain ⟨ρ', ρp, Y', Y'p, π', g', gp, ps', ls', g₁', g₂', g₃, g₆, g₇, g₉, gA, gB, gT, gtg, gps,
    gls, gV, gN, gW, gWp, gS', gSπ, gAu, gOff, gC⟩ := hr.2 hfin
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂'
  obtain ⟨W₀, hW₀, hWf₀⟩ := (hash_shift ρ' ρ₂ xf.1).mp ⟨y, ResU.CompS.comm hy, g₁'⟩
  have hWf : ResU.Hash W xf.1 := by
    rwa [ResU.CompS.functional (ResU.CompS.comm hW₀) hW] at hWf₀
  obtain ⟨-, hWp⟩ := ResU.Hash.split hfW (ResU.hash_symm g₃)
  obtain ⟨πW, hπW, h₂π₀⟩ := (hash_shift ρ₂ ρ' ρp).mpr ⟨W, hW, hWp⟩
  have h₂π : ResU.Hash ρ₂ π' := by rwa [ResU.CompS.functional hπW g₉] at h₂π₀
  obtain ⟨πn, hπn, -⟩ := h₂π.2
  obtain ⟨Wn, hWn, hWπ₀⟩ := compS_reassoc' g₉ hπn
  have hWπ : ResU.CompS W ρp πn := by
    rwa [ResU.CompS.functional hWn hW] at hWπ₀
  have hGe : xf.2 + g₂ + (g' + gp) = xf.2 + (g' + g₂ + gp) := by ext <;> simp <;> ring
  have hNy : NewNotCarried (xf.2 + (g₁ + g₂)).counted (xf.2 + (g' + g₂ + gp)).counted y := by
    rw [← hG, ← hGe]; exact gN
  refine ⟨W, ρp, Y', Y'p, πn, g' + g₂, gp, ps', ls', hWf, hfW, g₃, g₆, g₇, hWπ, ?_, gB, gT, gtg,
    gps, gls, ?_, fun α hα hα₀ hc => hNy α hα hα₀ (carries_comp_left hy hvy hc), ?_, ?_,
    maskShallow_comp (ResU.CompS.comm hW) gS' hsh₂, maskShallow_comp hπn hsh₂ gSπ,
    gAu.add_right ?_, gOff, ρ', ρ₂, g', g₂, ResU.CompS.comm hW, rfl, ?_, hR ls ls' gls _ hR₂⟩
  · exact updVNm_frame (ResU.CompS.comm hcρ) hπn
      ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, hvρ⟩ h₂π hsh₁ gSπ gA
  · rw [← hGe]; exact gV
  · have hW₂ : WFC (xf.2 + (g' + g₂ + gp)).counted (ρ₂, g₂) :=
      wfc_grow hwx₂ (fun α hα hα₀ hc => hNy α hα hα₀ (carries_comp_right hy hvy hc))
    have hW₁ : WFC (xf.2 + (g' + g₂ + gp)).counted (ρ', g') := by rw [← hGe]; exact gW
    exact wfc_comp (ResU.CompS.comm hW) hW₁ hW₂
  · rw [← hGe]; exact gWp
  · have : (xf.2 + (g' + g₂ + gp)).Valid := by rw [← hGe]; exact gV
    exact (GRes.Valid.right (GRes.Valid.left (by rwa [← GRes.add_assoc] at this)))
  · rw [← hGe]; exact gC

/-! ### The relation -/

/-- A postcondition over values, at the counted set and the index. -/
abbrev PostX : Type := Set Life → Nat → List SRec → Val → XProp

/-- What a stop owes, at every index and list. -/
abbrev ContX : Type := Nat → List SRec → Expr → XProp

/-- A protocol table: the stop at `t`, at the counted set and the index `k`, owing `Ψ`. -/
abbrev TableX : Type := Set Life → Nat → List SRec → Expr → ContX → XProp

def valPostX (Q : PostX) : PostGX := fun C k ls t x => ∃ v : Val, t = v.1 ∧ Q C k ls v x

/-- A value in `Q`, or a stop the table allows. -/
def erwpXPost (Tb : TableX) (Q : PostX) (Ψ : ContX) : PostGX :=
  fun C k ls t x => valPostX Q C k ls t x ∨ Tb C k ls t Ψ x

/-- **The one relation**: `erwp` over `WRes × GRes` at the mask `M`. -/
def erwpX (Φ : LocFam) (M : Mask) (Tb : TableX) (Q : PostX) : Nat → List SRec → Expr → XProp
  | n, ls, e => rwpGX (ℍ := ℍ) Φ M (erwpXPost Tb Q (fun k' ls' e' =>
      if _h : k' < n then erwpX Φ M Tb Q k' ls' e' else fun _ => False)) n ls e
termination_by n => n

/-- What `erwpX` at `N` owes below it. -/
def erwpXC (Φ : LocFam) (M : Mask) (Tb : TableX) (Q : PostX) (N : Nat) : ContX :=
  fun k' ls' e' => if k' < N then erwpX (ℍ := ℍ) Φ M Tb Q k' ls' e' else fun _ => False

theorem erwpX_eq (Φ : LocFam) (M : Mask) (Tb : TableX) (Q : PostX) (n : Nat) (ls : List SRec)
    (e : Expr) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e =
      rwpGX (ℍ := ℍ) Φ M (erwpXPost Tb Q (erwpXC (ℍ := ℍ) Φ M Tb Q n)) n ls e := by
  rw [erwpX]
  congr 1

/-- A table reads what is owed only below the index it stops at. -/
def TableX.Local (Tb : TableX) : Prop :=
  ∀ C k ls t (Ψ Ψ' : ContX) x, (∀ k', k' < k → ∀ ls e y, Ψ k' ls e y → Ψ' k' ls e y) →
    Tb C k ls t Ψ x → Tb C k ls t Ψ' x

/-- A table is downward closed in its index. -/
def TableX.Down (Tb : TableX) : Prop := ∀ C k ls t Ψ x, Tb C (k + 1) ls t Ψ x → Tb C k ls t Ψ x

def PostX.Down (Q : PostX) : Prop := ∀ C n ls v x, Q C (n + 1) ls v x → Q C n ls v x

theorem erwpX_unfold_at {Φ : LocFam} {M : Mask} {Tb : TableX} (hTb : Tb.Local) {Q : PostX}
    {n N : Nat} (hnN : n ≤ N) {ls : List SRec} {e : Expr} {x : XRes}
    (h : erwpX (ℍ := ℍ) Φ M Tb Q n ls e x) :
    rwpGX (ℍ := ℍ) Φ M (erwpXPost Tb Q (erwpXC (ℍ := ℍ) Φ M Tb Q N)) n ls e x := by
  rw [erwpX_eq] at h
  refine rwpGX_mono_le (fun C k hk ls' t y ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb C k ls' t _ _ y (fun k' hk' ls'' e'' y' hΨ => ?_) ht)
    simp only [erwpXC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem erwpX_fold_at {Φ : LocFam} {M : Mask} {Tb : TableX} (hTb : Tb.Local) {Q : PostX}
    {n N : Nat} (hnN : n ≤ N) {ls : List SRec} {e : Expr} {x : XRes}
    (h : rwpGX (ℍ := ℍ) Φ M (erwpXPost Tb Q (erwpXC (ℍ := ℍ) Φ M Tb Q N)) n ls e x) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e x := by
  rw [erwpX_eq]
  refine rwpGX_mono_le (fun C k hk ls' t y ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb C k ls' t _ _ y (fun k' hk' ls'' e'' y' hΨ => ?_) ht)
    simp only [erwpXC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem erwpXPost_down {Tb : TableX} (hTb : Tb.Down) {Q : PostX} (hQ : Q.Down) (Ψ : ContX) :
    (erwpXPost Tb Q Ψ).Down := by
  intro C k ls t x h
  rcases h with ⟨v, hv, hq⟩ | h
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ _ hq⟩
  · exact Or.inr (hTb _ _ _ _ _ _ h)

theorem erwpX_zero {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {ls : List SRec}
    {e : Expr} {x : XRes} : erwpX (ℍ := ℍ) Φ M Tb Q 0 ls e x := by
  rw [erwpX_eq]; exact rwpGX_zero

/-- **`erwpX` is downward closed.** -/
theorem erwpX_le {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hTb : Tb.Local)
    (hTd : Tb.Down) {Q : PostX} (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n) {ls : List SRec}
    {e : Expr} {x : XRes} (h : erwpX (ℍ := ℍ) Φ M Tb Q n ls e x) :
    erwpX (ℍ := ℍ) Φ M Tb Q m ls e x :=
  erwpX_fold_at hTb hmn (rwpGX_le hΦ (erwpXPost_down hTd hQ _) hmn (erwpX_unfold_at hTb le_rfl h))

/-- **A deterministic step in front of an `erwpX`, for free.** -/
theorem erwpX_det {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hTd : Tb.Down)
    {Q : PostX} (hQ : Q.Down) {n : Nat} {ls : List SRec} {e e' : Expr} {x : XRes}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : erwpX (ℍ := ℍ) Φ M Tb Q n ls e' x) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e x := by
  rw [erwpX_eq] at h ⊢
  exact rwpGX_det hΦ (erwpXPost_down hTd hQ _) hdet h

/-- **A value in the postcondition.** -/
theorem erwpX_val {Φ : LocFam} {M : Mask} {Tb : TableX} {Q : PostX} {n : Nat} {ls : List SRec}
    {v : Val} {x : XRes} (h : ∀ C, Q C n ls v x) : erwpX (ℍ := ℍ) Φ M Tb Q n ls v.1 x := by
  rw [erwpX_eq]
  exact rwpGX_here (fun μ => final_val μ v) (fun C => Or.inl ⟨v, rfl, h C⟩)

/-- A table is closed under a context `K` around the stopped term: a stop at `t` owing `Ψ` is a
stop at `K[t]` owing `Ψ'` whenever `Ψ'` covers `Ψ` with `K` put back. -/
def TableX.CtxClosed (Tb : TableX) (K : Kont) : Prop :=
  ∀ C k ls t (Ψ Ψ' : ContX) x,
    (∀ k', k' < k → ∀ ls' e y, Ψ k' ls' e y → Ψ' k' ls' (K.plug e) y) →
    Tb C k ls t Ψ x → Tb C k ls (K.plug t) Ψ' x ∧ ∀ μ, Final (ℍ := ℍ) μ (K.plug t)

/-- **Bind at `erwpX`, at a fixed mask**: a context around a computation whose stops the table
carries through `K`. A value continues in the context; a stop owes the context's continuation,
covered by induction on the index. -/
theorem erwpX_bind {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hL : Tb.Local)
    {Q Q' : PostX} (K : Kont) (hK : TableX.CtxClosed (ℍ := ℍ) Tb K)
    (hcont : ∀ C k ls (v : Val) x, Q' C k ls v x →
      erwpX (ℍ := ℍ) Φ M Tb Q k ls (K.plug v.1) x) :
    ∀ n ls e x, erwpX (ℍ := ℍ) Φ M Tb Q' n ls e x →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls (K.plug e) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e x h
  rw [erwpX_eq]
  refine rwpGX_bind hΦ K ?_
  refine rwpGX_mono_le (fun C k hk ls' t y ht => ?_) (erwpX_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · exact (erwpX_unfold_at hL hk (hcont C k ls' v y hv)).at C
  · obtain ⟨ht', hfin⟩ := hK C k ls' t _ (erwpXC (ℍ := ℍ) Φ M Tb Q n) y
      (fun k' hk' ls'' e'' z hz => by
        simp only [erwpXC, show k' < n by omega, if_true] at hz ⊢
        exact ih k' (by omega) _ _ _ hz) ht
    exact rwpGXat_here hfin (Or.inr ht')

end BoCa.Fig16.LogRel.Core.Chain.SI

end
