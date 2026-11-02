import DtorUnwind.TreeWp.World
import DtorUnwind.SI.RwpG

/-!
# `crwpG` over the tree world: `twp`

`SI/Capture.lean`'s `crwpG F Q n ls O e ρ`, read at a world `w` of `TreeWp/World.lean`. What
changes, each forced by the world growing:

* **The frame is quantified over the tree world.** A run starts at any extension `w₀` of `w`,
  from the re-reading `ρ₀` of `ρ` there (`RRw`): a stored continuation is resumed after the tree
  grew under it (a graft) and its cells' invariants were re-read (`Tree/KSem.lean`). This makes
  `twp` monotone along world extension by construction (`twp_kripke`), as a Kripke relation is.
* **The world at the end extends the world at the start**, and the frame at the end is the
  frame at the start re-read there (`EndT`). A run that opens a lend adds a child to `K`; a run
  that resumes a stored task inside a newer lend grafts it; neither touches the frame's cells
  other than by re-reading them.
* **Records are not carried.** `crwpG` owns records `O` so that a lend left open at a stop can be
  ended where it is resumed: `TWNC.immEnd` reads that the record is a record proper. The tree
  world has no records list; what ending a lend reads of the rest of the world is that the frame
  holds nothing at the lent location, and that is the frame condition `F` (as `cerwp`'s `fd`
  already reads it at a join). `Split`, `TWNC`, `Tagged` and the list `ls` go; the tags' role
  (which lifetime a record is at) is `K` itself.
* **The world invariant** is `WInv` (covered by `Θ`, types carried along growth, lowering to the
  memory) in place of `TWNC ∧ Tagged ∧ Lower`.

What the rules ask in exchange: a frame condition and a resource framed beside a run must be
carried along re-reading (`TFrame.Mono`, `TRProp.Mono`). At `RR.refl` (no growth) both are
trivial.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.BoLo (Heap Step1 Head Kont)

/-- A frame condition, at every world. -/
abbrev TFrame : Type := (w : TWd) → TRes w.K → Prop

/-- A resource predicate, at every world. -/
abbrev TRProp : Type := (w : TWd) → TRes w.K → Prop

/-- A postcondition over terms: at a step index, a world, a term. -/
abbrev TPost : Type := Nat → (w : TWd) → Expr → TRes w.K → Prop

/-- Carried along re-reading. -/
def TRProp.Mono (R : TRProp) : Prop :=
  ∀ (w w' : TWd) (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' → RRw (w := w) (w' := w') ρ ρ' →
    R w ρ → R w' ρ'

/-- A frame condition carried along re-reading. -/
abbrev TFrame.Mono (F : TFrame) : Prop := TRProp.Mono F

/-- **The post-configuration**: a world `w′` extending the run's world `w₀`, the frame `ρ_f`
re-read there, the run's resource beside it, the world invariant. -/
def EndT (Q : TPost) (k : Nat) (w₀ : TWd) (ρf : TRes w₀.K) (μ' : Heap) (t : Expr) : Prop :=
  ∃ (w' : TWd) (ρf' ρ' fρ' : TRes w'.K), w₀.Ext w' ∧ RRw (w := w₀) (w' := w') ρf ρf' ∧
    ResUT.Hash ρ' ρf' ∧ ResUT.CompS ρf' ρ' fρ' ∧ WInv w' fρ' μ' ∧ Q k w' t ρ'

/-- **`crwpG` over the tree world.** -/
def twp (F : TFrame) (Q : TPost) (n : Nat) (w : TWd) (e : Expr) (ρ : TRes w.K) : Prop :=
  ∀ (w₀ : TWd) (ρ₀ ρf fρ : TRes w₀.K) (μ : Heap), w.Ext w₀ → RRw (w := w) (w' := w₀) ρ ρ₀ →
    F w₀ ρf → ResUT.Hash ρf ρ₀ → ResUT.CompS ρf ρ₀ fρ → WInv w₀ fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' → Final (ℍ := ℍ) μ' e' →
      EndT Q (n - j) w₀ ρf μ' e'

/-! ### Basic facts -/

theorem EndT.mono {P Q : TPost} {k k' : Nat} {t : Expr}
    (hPQ : ∀ w ρ, P k w t ρ → Q k' w t ρ) {w₀ : TWd} {ρf : TRes w₀.K} {μ' : Heap}
    (h : EndT P k w₀ ρf μ' t) : EndT Q k' w₀ ρf μ' t := by
  obtain ⟨w', ρf', ρ', fρ', h₀, h₁, h₂, h₃, h₄, h₅⟩ := h
  exact ⟨w', ρf', ρ', fρ', h₀, h₁, h₂, h₃, h₄, hPQ _ _ h₅⟩

theorem twp_zero {F : TFrame} {Q : TPost} {w : TWd} {e : Expr} {ρ : TRes w.K} :
    twp (ℍ := ℍ) F Q 0 w e ρ := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ j _ _ hj
  omega

theorem twp_mono_le {F : TFrame} {P Q : TPost} {n : Nat}
    (hPQ : ∀ k, k ≤ n → ∀ w t ρ, P k w t ρ → Q k w t ρ) {w : TWd} {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F P n w e ρ) : twp (ℍ := ℍ) F Q n w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j μ' e' hj hrun hfin
  exact (h w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j μ' e' hj hrun hfin).mono
    (fun _ _ x => hPQ _ (by omega) _ _ _ x)

theorem twp_mono {F : TFrame} {P Q : TPost} (hPQ : ∀ k w t ρ, P k w t ρ → Q k w t ρ)
    {n : Nat} {w : TWd} {e : Expr} {ρ : TRes w.K} (h : twp (ℍ := ℍ) F P n w e ρ) :
    twp (ℍ := ℍ) F Q n w e ρ :=
  twp_mono_le (fun k _ => hPQ k) h

/-- A stronger frame condition. -/
theorem twp_frameCond {F F' : TFrame} (hF : ∀ w ρf, F' w ρf → F w ρf) {Q : TPost} {n : Nat}
    {w : TWd} {e : Expr} {ρ : TRes w.K} (h : twp (ℍ := ℍ) F Q n w e ρ) :
    twp (ℍ := ℍ) F' Q n w e ρ :=
  fun w₀ ρ₀ ρf fρ μ hE hr hF' => h w₀ ρ₀ ρf fρ μ hE hr (hF w₀ ρf hF')

/-- A postcondition downward closed in its index. -/
def TPost.Down (Q : TPost) : Prop := ∀ n w t ρ, Q (n + 1) w t ρ → Q n w t ρ

theorem TPost.Down.le {Q : TPost} (hQ : Q.Down) {m k : Nat} (h : m ≤ k) :
    ∀ w t ρ, Q k w t ρ → Q m w t ρ := by
  induction h with
  | refl => exact fun _ _ _ x => x
  | step _ ih => exact fun w t ρ x => ih w t ρ (hQ _ _ _ _ x)

/-- **`twp` is downward closed.** -/
theorem twp_le {F : TFrame} {Q : TPost} (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n) {w : TWd}
    {e : Expr} {ρ : TRes w.K} (h : twp (ℍ := ℍ) F Q n w e ρ) : twp (ℍ := ℍ) F Q m w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j μ' e' hj hrun hfin
  exact (h w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j μ' e' (by omega) hrun hfin).mono
    (fun _ _ x => hQ.le (by omega) _ _ _ x)

/-- **`twp` is monotone along world extension**: by construction, the frame being quantified
over the extensions. -/
theorem twp_kripke {F : TFrame} {Q : TPost} {n : Nat} {w w₁ : TWd} {e : Expr} {ρ : TRes w.K}
    {ρ₁ : TRes w₁.K} (hE : w.Ext w₁) (hr : RRw (w := w) (w' := w₁) ρ ρ₁)
    (h : twp (ℍ := ℍ) F Q n w e ρ) : twp (ℍ := ℍ) F Q n w₁ e ρ₁ := by
  intro w₀ ρ₀ ρf fρ μ hE₀ hr₀
  exact h w₀ ρ₀ ρf fρ μ (hE.trans hE₀) (RRw.trans hE₀ hr hr₀)

/-- The resource of a run, part of a world in the invariant, is covered. -/
theorem cov_of_comp {w : TWd} {ρf ρ fρ : TRes w.K} {μ : Heap} (hc : ResUT.CompS ρf ρ fρ)
    (hI : WInv w fρ μ) : CovR w.Θ w.K ρ :=
  CovR.of_compS_right hc hI.1

theorem covf_of_comp {w : TWd} {ρf ρ fρ : TRes w.K} {μ : Heap} (hc : ResUT.CompS ρf ρ fρ)
    (hI : WInv w fρ μ) : CovR w.Θ w.K ρf :=
  CovR.of_compS_left hc hI.1

/-- **A final term in the postcondition**, at every extension of the world. -/
theorem twp_here {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {e : Expr} {ρ : TRes w.K}
    (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K), w.Ext w₀ → RRw (w := w) (w' := w₀) ρ ρ₀ → Q n w₀ e ρ₀) :
    twp (ℍ := ℍ) F Q n w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr _ hf hc hI _ j μ' e' hj hrun _
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  exact ⟨w₀, ρf, ρ₀, fρ, TWd.Ext.refl _, RR.refl ((covf_of_comp hc hI).mono (LocTy.Le.refl _)),
    ResUT.hash_symm hf, hc, hI, by simpa using h w₀ ρ₀ hE hr⟩

/-- **A step that is its configuration's only one, for free.** -/
theorem twp_det {F : TFrame} {Q : TPost} (hQ : Q.Down) {n : Nat} {w : TWd} {e e' : Expr}
    {ρ : TRes w.K} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : twp (ℍ := ℍ) F Q n w e' ρ) : twp (ℍ := ℍ) F Q n w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet _).1 (hfin _ e')
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ hs
      exact (h w₀ ρ₀ ρf fρ _ hE hr hF hf hc hI hfd j' μ' E (by omega) t hfin).mono
        (fun _ _ x => hQ.le (by omega) _ _ _ x)

/-- **A step that is its configuration's only one, paid by the index.** -/
theorem twp_step {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {e e' : Expr} {ρ : TRes w.K}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : twp (ℍ := ℍ) F Q n w e' ρ) :
    twp (ℍ := ℍ) F Q (n + 1) w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet μ).1 (hfin μ e')
  | @more j' μ μ₁ μ' e e₁ E hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet μ).2 _ _ hs
      have := h w₀ ρ₀ ρf fρ _ hE hr hF hf hc hI hfd j' μ' E (by omega) t hfin
      rwa [show n + 1 - (j' + 1) = n - j' by omega]

/-! ### Bind -/

/-- **Bind at any final term**: a run of `e` to a final term `t`, then the continuation from
`K[t]` at the world the run ended at, under the frame re-read there. The frame condition is
carried along the re-reading (`hFm`), as `crwpG_bind`'s is carried unchanged. -/
theorem twp_bind {F : TFrame} (hFm : F.Mono) {Q : TPost} (K : Kont) {n : Nat} {w : TWd}
    {e : Expr} {ρ : TRes w.K}
    (hw : twp (ℍ := ℍ) F (fun k w' t => twp (ℍ := ℍ) F Q k w' (K.plug t)) n w e ρ) :
    twp (ℍ := ℍ) F Q n w (K.plug e) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j μ' E hj hrun hfin
  have go : ∀ j₁ j₂ μ₁ t, j₁ + j₂ = j → StepsN (ℍ := ℍ) j₁ μ e μ₁ t → Final (ℍ := ℍ) μ₁ t →
      StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E → EndT Q (n - j) w₀ ρf μ' E := by
    intro j₁ j₂ μ₁ t hjj hrun₁ hfin₁ hrun₂
    obtain ⟨w₁, ρf₁, ρ₁, fρ₁, g₀, g₁, g₂, g₃, g₄, g₅⟩ :=
      hw w₀ ρ₀ ρf fρ μ hE hr hF hf hc hI hfd j₁ μ₁ t (by omega) hrun₁ hfin₁
    have hcov : CovR w₁.Θ w₁.K ρ₁ := cov_of_comp g₃ g₄
    obtain ⟨w₂, ρf₂, ρ₂, fρ₂, k₀, k₁, k₂, k₃, k₄, k₅⟩ :=
      g₅ w₁ ρ₁ ρf₁ fρ₁ μ₁ (TWd.Ext.refl _) (RR.refl hcov) (hFm _ _ _ _ g₀ g₁ hF)
        (ResUT.hash_symm g₂) g₃ g₄ (fd_stepsN hrun₁ hfd) j₂ μ' E (by omega) hrun₂ hfin
    refine ⟨w₂, ρf₂, ρ₂, fρ₂, g₀.trans k₀, RRw.trans k₀ g₁ k₁, k₂, k₃, k₄, ?_⟩
    rwa [show n - j₁ - j₂ = n - j by omega] at k₅
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    exact go j 0 μ' e' (by omega) hrun' hfin' (.refl _ _)
  · exact go j₁ j₂ μ₁ t hjj hrun₁ hirr hrun₂

/-! ### Reassociation -/

theorem reassoc_out {K : WCactus} {ρf ρ₀ fρ ρ₁ ρ₂ : TRes K} (hc : ResUT.CompS ρf ρ₀ fρ)
    (h₀ : ResUT.CompS ρ₁ ρ₂ ρ₀) : ∃ y, ResUT.CompS ρf ρ₂ y ∧ ResUT.CompS y ρ₁ fρ :=
  (ResUT.CompS.assoc ρf ρ₂ ρ₁ fρ).mp ⟨ρ₀, ResUT.CompS.comm h₀, hc⟩

theorem reassoc_in {K : WCactus} {ρf ρ₂ y ρ₁ fρ : TRes K} (hy : ResUT.CompS ρf ρ₂ y)
    (hc : ResUT.CompS y ρ₁ fρ) : ∃ ρ', ResUT.CompS ρ₁ ρ₂ ρ' ∧ ResUT.CompS ρf ρ' fρ := by
  obtain ⟨x, hx, hfx⟩ := (ResUT.CompS.assoc ρf ρ₂ ρ₁ fρ).mpr ⟨y, hy, hc⟩
  exact ⟨x, ResUT.CompS.comm hx, hfx⟩

/-- A composite of a valid world's parts is `#`. -/
theorem hash_of_inv {w : TWd} {a b y : TRes w.K} {μ : Heap} (hc : ResUT.CompS a b y)
    (hI : WInv w y μ) : ResUT.Hash a b :=
  ResUT.Hash.of_compS hc hI.valid

/-! ### The frame -/

/-- `P ⋆ R` over terms, at a world. -/
def TPost.sep (P : TPost) (R : TRProp) : TPost := fun k w t ρ =>
  ∃ a b, ResUT.CompS a b ρ ∧ P k w t a ∧ R w b

/-- **The frame**: a resource `ρ₂` in `R` kept beside the run. Forced beside `crwpG_frame`: `R`
is carried along re-reading (`hR`), and the framed resource is covered at its world (`hcov`), so
that its parts have re-readings at every extension. -/
theorem twp_frame {F F₁ : TFrame} {P : TPost} {R : TRProp} (hR : R.Mono) {n : Nat} {w : TWd}
    {e : Expr} {ρ₁ ρ₂ ρ : TRes w.K} (hcρ : ResUT.CompS ρ₁ ρ₂ ρ) (hcov : CovR w.Θ w.K ρ)
    (hF : ∀ (w₀ : TWd) (ρf ρ₂₀ y : TRes w₀.K), w.Ext w₀ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      F w₀ ρf → ResUT.CompS ρf ρ₂₀ y → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w e ρ₁) (hR₂ : R w ρ₂) :
    twp (ℍ := ℍ) F (P.sep R) n w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr hFρ hf hc hI hfd j μ' e' hj hrun hfin
  have hM₀ : MonoΘ w₀.Θ := hI.2.1.monoΘ
  obtain ⟨ρ₁₀, ρ₂₀, h₁₀, h₂₀, hc₀⟩ := RR.split hE.1 hM₀ hcρ (hcov.mono hE.2) hr
  obtain ⟨y, hy, hyf⟩ := reassoc_out hc hc₀
  obtain ⟨w', y', ρ₁', fρ', g₀, g₁, g₂, g₃, g₄, g₅⟩ :=
    hwp w₀ ρ₁₀ y fρ μ hE h₁₀ (hF w₀ ρf ρ₂₀ y hE h₂₀ hFρ hy) (hash_of_inv hyf hI) hyf hI hfd
      j μ' e' hj hrun hfin
  have hM' : MonoΘ w'.Θ := g₄.2.1.monoΘ
  obtain ⟨ρf', ρ₂', hf', h₂', hy'⟩ :=
    RR.split g₀.1 hM' hy ((covf_of_comp hyf hI).mono g₀.2) g₁
  obtain ⟨ρ', hρ', hfρ'⟩ := reassoc_in hy' g₃
  have hR₂₀ : R w₀ ρ₂₀ := hR _ _ _ _ hE h₂₀ hR₂
  exact ⟨w', ρf', ρ', fρ', g₀, hf', ResUT.hash_symm (hash_of_inv hfρ' g₄), hfρ', g₄,
    ρ₁', ρ₂', hρ', g₅, hR _ _ _ _ g₀ h₂' hR₂₀⟩

/-! ### World changes at the start of a run -/

/-- **The tree grows at the start of a segment**: at whichever extension the run starts at, the
world may be extended further (a fresh child, a graft), and the run continues there from the
re-reading. The frame condition is carried along. -/
theorem twp_extend {F : TFrame} (hFm : F.Mono) {Q : TPost} {n : Nat} {w : TWd} {e : Expr}
    {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K), w.Ext w₀ → RRw (w := w) (w' := w₀) ρ ρ₀ →
      ∃ w₁ : TWd, w₀.Ext w₁ ∧ MonoUp w₁.Θ ∧
        ∀ ρ₁ : TRes w₁.K, RRw (w := w₀) (w' := w₁) ρ₀ ρ₁ → twp (ℍ := ℍ) F Q n w₁ e ρ₁) :
    twp (ℍ := ℍ) F Q n w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr hFρ hf hc hI hfd j μ' e' hj hrun hfin
  obtain ⟨w₁, hE₁, hM₁, hw₁⟩ := h w₀ ρ₀ hE hr
  obtain ⟨fρ₁, hfr, hI₁⟩ := hI.reread hE₁ hM₁
  obtain ⟨ρf₁, ρ₀₁, hf₁, h₀₁, hc₁⟩ := RR.split hE₁.1 hM₁.monoΘ hc (hI.1.mono hE₁.2) hfr
  obtain ⟨w', ρf', ρ', fρ', g₀, g₁, g₂, g₃, g₄, g₅⟩ :=
    hw₁ ρ₀₁ h₀₁ w₁ ρ₀₁ ρf₁ fρ₁ μ (TWd.Ext.refl _) (RR.refl (cov_of_comp hc₁ hI₁))
      (hFm _ _ _ _ hE₁ hf₁ hFρ) (hash_of_inv hc₁ hI₁) hc₁ hI₁ hfd j μ' e' hj hrun hfin
  exact ⟨w', ρf', ρ', fρ', hE₁.trans g₀, RRw.trans g₀ hf₁ g₁, g₂, g₃, g₄, g₅⟩

/-- **The resource changes at the start of a segment**, under every frame meeting `F`, keeping
the world invariant and the memory: a lend opened, a lend ended. -/
theorem twp_update {F : TFrame} {Q : TPost} {n : Nat} {w : TWd} {e : Expr} {ρ ρ₁ : TRes w.K}
    (hup : ∀ (w₀ : TWd) (ρ₀ ρf fρ : TRes w₀.K) (μ : Heap), w.Ext w₀ →
      RRw (w := w) (w' := w₀) ρ ρ₀ → F w₀ ρf → ResUT.Hash ρf ρ₀ → ResUT.CompS ρf ρ₀ fρ →
      WInv w₀ fρ μ → ∃ ρ₁₀ fρ₁ : TRes w₀.K, RRw (w := w) (w' := w₀) ρ₁ ρ₁₀ ∧
        ResUT.Hash ρf ρ₁₀ ∧ ResUT.CompS ρf ρ₁₀ fρ₁ ∧ WInv w₀ fρ₁ μ)
    (h : twp (ℍ := ℍ) F Q n w e ρ₁) : twp (ℍ := ℍ) F Q n w e ρ := by
  intro w₀ ρ₀ ρf fρ μ hE hr hFρ hf hc hI hfd j μ' e' hj hrun hfin
  obtain ⟨ρ₁₀, fρ₁, h₁, h₂, h₃, h₄⟩ := hup w₀ ρ₀ ρf fρ μ hE hr hFρ hf hc hI
  exact h w₀ ρ₁₀ ρf fρ₁ μ hE h₁ hFρ h₂ h₃ h₄ hfd j μ' e' hj hrun hfin

end BoCa.Fig16.Tree.Wp

end
