import Core.Chain.SI.ErwpN

/-!
# Capture as its own operation: `crwpG`

**Not a transcription.** `rwpG` (`SI/RwpG.lean`) asks, at every configuration a run ends at, the
post-configuration `[TR]` p. 6's `wp` asks at a return: the same records proper, the same list
members, `ρ ↭ π`. A stop is such a configuration, so a frame open at a stop must be ended there:
the lender folds the lent cell back into the continuation's share (`SI/IStopN.lean`,
`SI/StopFrameN.lean`) and lends it again at the resume. A borrow handed to another task cannot be
folded back: the other task holds it.

`crwpG` is `rwpG` with three changes, each forced by keeping a frame open across a stop.

* **Records are owned.** A run starts owning the records `O` and ends owning `O′`; the frame's
  records `psF` are kept (`Split ps O psF` before, `Split ps′ O′ psF` after). A frame opened and
  left open at a stop is a record the stop's continuation owns; ending it (`TWNC.immEnd`) needs
  the record to be a record proper at the resume. The list conditions used so far (`extF`,
  `Tagged`) give that the record is in the lineage of a record proper, not that it is one; I have
  not derived the stronger fact from them and have not verified that it fails. Ownership is what
  the resumer hands back.
* **No garbage.** The post-configuration has no `ρ⁺`: everything the run holds at the end is in
  the postcondition's resource. A borrow set aside into `ρ⁺` at a stop would sit in every later
  frame, and the lender, at a later segment, could not take it back; at a return `ρ⁺` is the
  postcondition's to keep (`crwpG_of_rwpG` puts it there).
* **Frames are qualified.** The frame quantifier ranges over frames satisfying `F`. A lend ended
  in a segment the scheduler resumed needs that segment's frame to hold no cell at the lent
  location: that is a fact about every other stored continuation, which only the resumer knows.

The `↭` check is omitted: it is read by a lender of the same run at its end (6.29), and here a
lend that is ended in the run it was opened in is proved at `rwpG` (`crwpG_of_rwpG`); a lend left
open at a stop changes the lent cell from `own` to `imm`, which `↭` refuses.

`crwpG_bind`, `crwpG_frame`, `crwpG_det`, `crwpG_step` are `rwpG`'s, simpler: with no `ρ⁺`, the
continuation of a bind runs under the same frame.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-- The records proper `ps` are the computation's `O` and the frame's `psF`, disjoint. -/
def Split (ps O psF : List FrameRec) : Prop :=
  (∀ p, p ∈ ps ↔ p ∈ O ∨ p ∈ psF) ∧ ∀ p ∈ O, p ∉ psF

/-- A postcondition over terms, at a step index, the list and the records owned. -/
abbrev PostC : Type := Nat → List SRec → List FrameRec → Expr → WProp

/-- The post-configuration under the frame `ρ_f`, whose records are `psF`, at the memory `μ′`. -/
def EndC (Q : PostC) (k : Nat) (ρf : WRes) (psF : List FrameRec) (μ' : Heap) (t : Expr) : Prop :=
  ∃ (ρ' fρ' : WRes) (ps' O' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Lower fρ' μ' ∧ Split ps' O' psF ∧
    TWNC fρ' ps' (rsOf ls') ∧ Tagged fρ' ps' ls' ∧ Q k ls' O' t ρ'

/-- **`wpG` at the step index, with owned records, no garbage and qualified frames.** -/
def crwpG (F : WRes → Prop) (Q : PostC) (n : Nat) (ls : List SRec) (O : List FrameRec)
    (e : Expr) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps psF : List FrameRec) (μ : Heap),
    F ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → Split ps O psF →
    TWNC fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Lower fρ μ → FinDom μ →
    ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' → Final (ℍ := ℍ) μ' e' →
      EndC Q (n - j) ρf psF μ' e'

/-! ### Basic facts -/

theorem EndC.mono {P Q : PostC} {k k' : Nat} {t : Expr}
    (hPQ : ∀ ls O ρ, P k ls O t ρ → Q k' ls O t ρ) {ρf : WRes} {psF : List FrameRec}
    {μ' : Heap} (h : EndC P k ρf psF μ' t) : EndC Q k' ρf psF μ' t := by
  obtain ⟨ρ', fρ', ps', O', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  exact ⟨ρ', fρ', ps', O', ls', h₁, h₂, h₃, h₄, h₅, h₆, hPQ _ _ _ h₇⟩

theorem crwpG_zero {F : WRes → Prop} {Q : PostC} {ls : List SRec} {O : List FrameRec}
    {e : Expr} {ρ : WRes} : crwpG (ℍ := ℍ) F Q 0 ls O e ρ := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ j _ _ hj
  omega

/-- `crwpG` reading the postcondition at the indices runs leave, `≤ n`. -/
theorem crwpG_mono_le {F : WRes → Prop} {P Q : PostC} {n : Nat}
    (hPQ : ∀ k, k ≤ n → ∀ ls O t ρ, P k ls O t ρ → Q k ls O t ρ)
    {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : crwpG (ℍ := ℍ) F P n ls O e ρ) : crwpG (ℍ := ℍ) F Q n ls O e ρ := by
  intro ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  exact (h ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' e' hj hrun hfin).mono
    (fun _ _ _ x => hPQ _ (by omega) _ _ _ _ x)

theorem crwpG_mono {F : WRes → Prop} {P Q : PostC}
    (hPQ : ∀ k ls O t ρ, P k ls O t ρ → Q k ls O t ρ) {n : Nat}
    {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : crwpG (ℍ := ℍ) F P n ls O e ρ) : crwpG (ℍ := ℍ) F Q n ls O e ρ :=
  crwpG_mono_le (fun k _ => hPQ k) h

/-- A stronger frame condition. -/
theorem crwpG_frameCond {F F' : WRes → Prop} (hF : ∀ ρf, F' ρf → F ρf) {Q : PostC} {n : Nat}
    {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : crwpG (ℍ := ℍ) F Q n ls O e ρ) : crwpG (ℍ := ℍ) F' Q n ls O e ρ :=
  fun ρf fρ ps psF μ hF' => h ρf fρ ps psF μ (hF ρf hF')

/-- A postcondition over terms is downward closed. -/
def PostC.Down (Q : PostC) : Prop := ∀ n ls O t ρ, Q (n + 1) ls O t ρ → Q n ls O t ρ

theorem PostC.Down.le {Q : PostC} (hQ : Q.Down) {m k : Nat} (h : m ≤ k) :
    ∀ ls O t ρ, Q k ls O t ρ → Q m ls O t ρ := by
  induction h with
  | refl => exact fun _ _ _ _ x => x
  | step _ ih => exact fun ls O t ρ x => ih ls O t ρ (hQ _ _ _ _ _ x)

/-- **`crwpG` is downward closed.** -/
theorem crwpG_le {F : WRes → Prop} {Q : PostC} (hQ : Q.Down) {m n : Nat} (hmn : m ≤ n)
    {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : crwpG (ℍ := ℍ) F Q n ls O e ρ) : crwpG (ℍ := ℍ) F Q m ls O e ρ := by
  intro ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  exact (h ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' e' (by omega) hrun hfin).mono
    (fun _ _ _ x => hQ.le (by omega) _ _ _ _ x)

/-- **A final term in the postcondition.** -/
theorem crwpG_here {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} {e : Expr} {ρ : WRes} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : Q n ls O e ρ) : crwpG (ℍ := ℍ) F Q n ls O e ρ := by
  intro ρf fρ ps psF μ _ hf hc hS hT htg hl _ j μ' e' hj hrun _
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  exact ⟨ρ, fρ, ps, O, ls, ResU.hash_symm hf, hc, hl, hS, hT, htg, by simpa using h⟩

/-- **A step that is its configuration's only one, for free.** -/
theorem crwpG_det {F : WRes → Prop} {Q : PostC} (hQ : Q.Down) {n : Nat} {ls : List SRec}
    {O : List FrameRec} {e e' : Expr} {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : crwpG (ℍ := ℍ) F Q n ls O e' ρ) : crwpG (ℍ := ℍ) F Q n ls O e ρ := by
  intro ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet _).1 (hfin _ e')
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ hs
      exact (h ρf fρ ps psF _ hF hf hc hS hT htg hl hfd j' μ' E (by omega) t hfin).mono
        (fun _ _ _ x => hQ.le (by omega) _ _ _ _ x)

/-- **A step that is its configuration's only one, paid by the index.** -/
theorem crwpG_step {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} {e e' : Expr} {ρ : WRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : crwpG (ℍ := ℍ) F Q n ls O e' ρ) : crwpG (ℍ := ℍ) F Q (n + 1) ls O e ρ := by
  intro ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' E hj hrun hfin
  cases hrun with
  | refl => exact absurd (hdet μ).1 (hfin μ e')
  | @more j' μ μ₁ μ' e e₁ E hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet μ).2 _ _ hs
      have := h ρf fρ ps psF _ hF hf hc hS hT htg hl hfd j' μ' E (by omega) t hfin
      rwa [show n + 1 - (j' + 1) = n - j' by omega]

/-! ### Bind -/

/-- **Bind at any final term**: a run of `e` to a final term `t`, then the continuation from
`K[t]`, under the same frame. -/
theorem crwpG_bind {F : WRes → Prop} {Q : PostC} (K : Kont) {n : Nat} {ls : List SRec}
    {O : List FrameRec} {e : Expr} {ρ : WRes}
    (hw : crwpG (ℍ := ℍ) F (fun k ls' O' t => crwpG (ℍ := ℍ) F Q k ls' O' (K.plug t)) n ls O e ρ) :
    crwpG (ℍ := ℍ) F Q n ls O (K.plug e) ρ := by
  classical
  intro ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' E hj hrun hfin
  have go : ∀ j₁ j₂ μ₁ t, j₁ + j₂ = j → StepsN (ℍ := ℍ) j₁ μ e μ₁ t → Final (ℍ := ℍ) μ₁ t →
      StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E → EndC Q (n - j) ρf psF μ' E := by
    intro j₁ j₂ μ₁ t hjj hrun₁ hfin₁ hrun₂
    obtain ⟨ρ₁, fρ₁, ps₁, O₁, ls₁, g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩ :=
      hw ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j₁ μ₁ t (by omega) hrun₁ hfin₁
    have h := g₇ ρf fρ₁ ps₁ psF μ₁ hF (ResU.hash_symm g₁) g₂ g₄ g₅ g₆ g₃
      (fd_stepsN hrun₁ hfd) j₂ μ' E (by omega) hrun₂ hfin
    rwa [show n - j₁ - j₂ = n - j by omega] at h
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    exact go j 0 μ' e' (by omega) hrun' hfin' (.refl _ _)
  · exact go j₁ j₂ μ₁ t hjj hrun₁ hirr hrun₂

/-! ### The frame -/

/-- **The frame**: a resource `ρ₂` in `R` and records `O₂` the framed run does not own; the run's
frame condition `F₁` holds of every outer frame meeting `F`, with `ρ₂` added. -/
theorem crwpG_frame {F F₁ : WRes → Prop} {P : PostC} (R : List SRec → WRes → Prop)
    (hR : ∀ ls ls' ρ, R ls ρ → R ls' ρ) {n : Nat} {ls : List SRec} {O₁ O₂ : List FrameRec}
    (hO : ∀ p ∈ O₁, p ∉ O₂) {e : Expr} {ρ₁ ρ₂ ρ : WRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hF : ∀ ρf y, F ρf → ResU.Hash ρf ρ → ResU.CompS ρf ρ₂ y → F₁ y)
    (hwp : crwpG (ℍ := ℍ) F₁ P n ls O₁ e ρ₁) (hR₂ : R ls ρ₂) :
    crwpG (ℍ := ℍ) F (fun k ls' O' t => fun ρ' => ∃ O₁', O' = O₁' ++ O₂ ∧
      (P k ls' O₁' t ⋆ R ls') ρ') n ls (O₁ ++ O₂) e ρ := by
  intro ρf fρ ps psF μ hFρ hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  have hS₁ : Split ps O₁ (O₂ ++ psF) := by
    refine ⟨fun p => ?_, fun p hp hp' => ?_⟩
    · rw [hS.1 p, List.mem_append, List.mem_append]; tauto
    · rcases List.mem_append.mp hp' with h | h
      · exact hO p hp h
      · exact hS.2 p (List.mem_append_left _ hp) h
  obtain ⟨ρ', fρ', ps', O₁', ls', g₁, g₂, g₃, g₄, g₅, g₆, g₇⟩ :=
    hwp y fρ ps (O₂ ++ psF) μ (hF ρf y hFρ hf hy) hy₁ hyfρ hS₁ hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  have hvW : ResU.Valid fρ' := by obtain ⟨σ, hσ, -⟩ := g₃; exact ⟨σ, hσ⟩
  refine ⟨W, fρ', ps', O₁' ++ O₂, ls', ⟨(ResU.CompS.comm hfW).1, fρ', ResU.CompS.comm hfW, hvW⟩,
    hfW, g₃, ⟨fun p => ?_, fun p hp hp' => ?_⟩, g₅, g₆, O₁', rfl, ρ', ρ₂, ResU.CompS.comm hW, g₇,
    hR ls ls' ρ₂ hR₂⟩
  · rw [g₄.1 p, List.mem_append, List.mem_append]; tauto
  · rcases List.mem_append.mp hp with h | h
    · exact g₄.2 p h (List.mem_append_right _ hp')
    · exact hS.2 p (List.mem_append_right _ h) hp'

/-! ### A world update before the run -/

/-- **A world update at the start of a segment**: a change of the world under every frame that
keeps the memory, then a run from the changed resource, list and records. -/
theorem crwpG_update {F : WRes → Prop} {Q : PostC} {n : Nat} {ls ls₁ : List SRec}
    {O O₁ : List FrameRec} {e : Expr} {ρ ρ₁ : WRes}
    (hup : ∀ (ρf fρ : WRes) (ps psF : List FrameRec) (μ : Heap), F ρf → ResU.Hash ρf ρ →
      ResU.CompS ρf ρ fρ → Split ps O psF → TWNC fρ ps (rsOf ls) → Tagged fρ ps ls →
      ResU.Lower fρ μ → ∃ (fρ₁ : WRes) (ps₁ : List FrameRec), ResU.Hash ρf ρ₁ ∧
        ResU.CompS ρf ρ₁ fρ₁ ∧ Split ps₁ O₁ psF ∧ TWNC fρ₁ ps₁ (rsOf ls₁) ∧
        Tagged fρ₁ ps₁ ls₁ ∧ ResU.Lower fρ₁ μ)
    (h : crwpG (ℍ := ℍ) F Q n ls₁ O₁ e ρ₁) : crwpG (ℍ := ℍ) F Q n ls O e ρ := by
  intro ρf fρ ps psF μ hF hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨fρ₁, ps₁, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hup ρf fρ ps psF μ hF hf hc hS hT htg hl
  exact h ρf fρ₁ ps₁ psF μ hF h₁ h₂ h₃ h₄ h₅ h₆ hfd j μ' e' hj hrun hfin

/-! ### `rwpG` lifts -/

/-- The postcondition `rwpG`'s `Q` lifts to: the garbage kept in the resource, the records
unchanged. -/
def liftG (Q : PostG) (O : List FrameRec) : PostC := fun k ls O' t ρ =>
  O' = O ∧ ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ NoOwn ρ₂ ∧ Q k ls t ρ₁

/-- **`rwpG` is `crwpG`** at the lifted postcondition, at every frame condition and every owned
list, at a location typing with no `imm` records: a run of `rwpG` keeps every record proper, so
it keeps the frame's. -/
theorem crwpG_of_rwpG {Φ : LocFam} (hΦI : Φ.imm = []) {F : WRes → Prop} {Q : PostG} {n : Nat}
    {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) :
    crwpG (ℍ := ℍ) F (liftG Q O) n ls O e ρ := by
  intro ρf fρ ps psF μ _ hf hc hS hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, -, h₈, h₉, h₁₀, h₁₁, -, h₁₃⟩ :=
    h ρf fρ ps μ hf hc hT htg (ImmTieL.of_nil hΦI ls) hl hfd j μ' e' hj hrun hfin
  obtain ⟨π₁, hπ₁, hfπ⟩ := (ResU.CompS.assoc ρf ρ' ρp fρ'p).mpr ⟨fρ', h₂, h₄⟩
  cases ResU.CompS.functional h₆ hπ₁
  have hv : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h₅; exact ⟨σ, hσ⟩
  refine ⟨π, fρ'p, ps', O, ls', ⟨(ResU.CompS.comm hfπ).1, fρ'p, ResU.CompS.comm hfπ, hv⟩, hfπ,
    h₅, ⟨fun p => (h₁₁ p).trans (hS.1 p), hS.2⟩, h₉, h₁₀, rfl, ρ', ρp, h₆, h₈, h₁₃⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
