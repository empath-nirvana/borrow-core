import Core.Chain.SI.ErwpN
import Core.Chain.SI.LoanX.XRes
import Core.Chain.SI.LoanX.FrameKept

/-!
# The one relation: `erwp` over `WRes × GRes` at a mask  `[spec §62]`

`docs/new-core/scope-owned-scalar-kernel.md`, stages 1 and 2, with the mask an index of the relation, as in
Iris's `WP_E e {Q}`. `erwpX Φ M Tb Q n ls e x` is `erwp`'s definition (`SI/ErwpN.lean`) over
`XRes = WRes × GRes` at the mask `M`.

**The run (`rwpGX`).** Frames range over `XRes`. At the start the frame and the resource compose
validly and are each `WF_C` at the world's counted set `C`; the resource is `MaskShallow` at `M`
(`ρ_P = ∅` at masked locations) and holds `M`'s authorities (`MaskAuth`); the frame holds only
copies at a location lent across stops (`MaskOff`).

**The end (`EndOKX`)** names the mask `M′` the run's continuation resumes at. Its conjuncts are
`EndOKG`'s, with `↭` read outside `M ∪ M′` (`UpdVNm Φ k (M ∪ M′).locs`); the end ghost `g′` and the
garbage's `gp` compose validly with the frame's (a change from the start is frame-preserving
because the end composes with the same frame); at the end world's counted set `C′`, the end and the
garbage are `WF_C′`, and the frame carries no lifetime counted at `C′` and not at `C`
(`NewNotCarried`), which with the frame's `WF_C` at the start is its `WF_C′`; the end is
`MaskShallow` at `M′` and holds `M′`'s authorities, and the end with its garbage is `MaskShallow` at
`M ∪ M′`; the garbage holds only copies at a location `M′` lends across stops (`MaskOff`), and no
borrow at a location `M` lends `mut` across stops (`NoBorrowAt`). What `M′`
masks and `M` does not (`M.fresh M′`) the frame does not hold (`FlatNone`), and the start is
shallow there. The records and the list are as at the start off the locations `M ∪ M′` lends
across stops (`RecAgree`, `ListAgree`). `M′` and `C′` are passed to the post.

**The frame at ends.** A run speaks at its final configurations only, as main `rwpG`: the
frame's world is kept at a segment's end and at a stop (`EndOKX.frameKept`), not at every step.
The per-step access guard G is not part of this relation
(`docs/new-core/scope-owned-scalar-kernel.md`, "Dropped: per-step access guard G (threads)").

**The mask within a segment is fixed**: bind continues a value at `M` (`UpdVNm.trans` at
`M ∪ M = M`), and a value is reached at `M′ = M` (`valPostX`). **A stop chooses its continuation's
mask** (`erwpXPost`): `erwpX` at `M` owes, at a stop to resume at `M′`, `erwpX` at `M′` below the
index. The table sees both masks (`TableX`).
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

/-- A postcondition over terms, at the mask the run's continuation resumes at, the counted set and
the index. -/
abbrev PostGX : Type := Mask → Set Life → Nat → List SRec → Expr → XProp

theorem ghost_ac₁ (a b c : GRes) : a + b + c = a + (c + b) := by
  ext <;> simp <;> ring

theorem ghost_ac₂ (a b c d : GRes) : a + b + (c + d) = a + (c + (b + d)) := by
  ext <;> simp <;> ring

/-- **`EndOK` at the one relation**, the continuation resumed at `M′`. -/
def EndOKX (Φ : LocFam) (M : Mask) (Q : PostGX) (k : Nat) (ls : List SRec) (x xf : XRes)
    (ps : List FrameRec) (μ' : Heap) (t : Expr) : Prop :=
  ∃ (M' : Mask) (ρ' ρp fρ' fρ'p π : WRes) (g' gp : GRes) (ps' : List FrameRec) (ls' : List SRec),
    ResU.Hash ρ' xf.1 ∧ ResU.CompS xf.1 ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
    ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
    ResU.CompS ρ' ρp π ∧ UpdVNm Φ k (M ∪ M').locs x.1 π ∧ NoOwn ρp ∧
    TWNC fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
    RecAgree (M ∪ M') ps' ps ∧ ListAgree (M ∪ M') ls' ls ∧
    (xf.2 + (g' + gp)).Valid ∧
    NewNotCarried (xf.2 + x.2).counted (xf.2 + (g' + gp)).counted xf.1 ∧
    WFC (xf.2 + (g' + gp)).counted (ρ', g') ∧ WFC (xf.2 + (g' + gp)).counted (ρp, gp) ∧
    MaskShallow M'.locs ρ' ∧ MaskShallow (M ∪ M').locs π ∧ MaskAuth M' g' ∧ MaskOff M' ρp ∧
    MaskShallow (M'.locs \ M.locs) x.1 ∧ FlatNone (M.fresh M') xf.1 ∧
    NoBorrowAt M.mloanLocs ρp ∧ Q M' (xf.2 + (g' + gp)).counted k ls' t (ρ', g')

/-- **`wpG` at the step index over `WRes × GRes`, at the mask `M`.** -/
def rwpGX (Φ : LocFam) (M : Mask) (Q : PostGX) (n : Nat) (ls : List SRec) (e : Expr) : XProp :=
  fun x =>
    ∀ (xf : XRes) (fρ : WRes) (ps : List FrameRec) (μ : Heap),
      ResU.Hash xf.1 x.1 → ResU.CompS xf.1 x.1 fρ → (xf.2 + x.2).Valid →
      WFC (xf.2 + x.2).counted xf → WFC (xf.2 + x.2).counted x →
      MaskShallow M.locs x.1 → MaskAuth M x.2 → MaskOff M xf.1 →
      TWNC fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Lower fρ μ → FinDom μ →
      ∀ j μ' e', j < n → StepsN (ℍ := ℍ) j μ e μ' e' →
        Final (ℍ := ℍ) μ' e' → EndOKX Φ M Q (n - j) ls x xf ps μ' e'

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
        Final (ℍ := ℍ) μ' e' → EndOKX Φ M Q (n - j) ls x xf ps μ' e'

/-- G at a run's end: the post-configuration keeps the frame's world. -/
theorem EndOKX.frameKept {Φ : LocFam} {M : Mask} {Q : PostGX} {k : Nat} {ls : List SRec}
    {x xf : XRes} {ps : List FrameRec} {μ' : Heap} {t : Expr}
    (h : EndOKX Φ M Q k ls x xf ps μ' t) : FrameKept xf.1 μ' := by
  obtain ⟨_, _, _, fρ', fρ'p, _, _, _, _, _, _, h₂, h₃, h₄, h₅, _⟩ := h
  exact ((frameKept_lower h₅).of_compS h₄ (by obtain ⟨σ, hσ, -⟩ := h₅; exact ⟨σ, hσ⟩)).of_compS
    h₂ (hash_valid h₃).2

theorem rwpGX.at {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec} {e : Expr}
    {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M Q n ls e x) (C : Set Life) :
    rwpGXat (ℍ := ℍ) Φ M Q n ls e C x :=
  fun xf fρ ps μ _ => h xf fρ ps μ

/-! ### Downward closure and monotonicity -/

def PostGX.Down (Q : PostGX) : Prop := ∀ M' C n ls t x, Q M' C (n + 1) ls t x → Q M' C n ls t x

theorem PostGX.Down.le {Q : PostGX} (hQ : Q.Down) {m k : Nat} (h : m ≤ k) :
    ∀ M' C ls t x, Q M' C k ls t x → Q M' C m ls t x := by
  induction h with
  | refl => exact fun _ _ _ _ _ x => x
  | step _ ih => exact fun M' C ls t x h => ih M' C ls t x (hQ _ _ _ _ _ _ h)

theorem EndOKX.mono {Φ : LocFam} {M : Mask} {P Q : PostGX} {k k' : Nat} (hΦ : Φ.Down)
    (hk : k' ≤ k) {t : Expr} (hPQ : ∀ M' C ls x, P M' C k ls t x → Q M' C k' ls t x)
    {ls : List SRec} {x xf : XRes} {ps : List FrameRec} {μ' : Heap}
    (h : EndOKX Φ M P k ls x xf ps μ' t) : EndOKX Φ M Q k' ls x xf ps μ' t := by
  obtain ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁, h₂₂, h₂₄, h₂₃⟩ := h
  exact ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇.down hΦ hk, h₈,
    h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁, h₂₂, h₂₄, hPQ _ _ _ _ h₂₃⟩

/-- `EndOKX` at another postcondition, at the same index. -/
theorem EndOKX.post {Φ : LocFam} {M : Mask} {P Q : PostGX} {k : Nat} {t : Expr}
    (hPQ : ∀ M' C ls x, P M' C k ls t x → Q M' C k ls t x)
    {ls : List SRec} {x xf : XRes} {ps : List FrameRec} {μ' : Heap}
    (h : EndOKX Φ M P k ls x xf ps μ' t) : EndOKX Φ M Q k ls x xf ps μ' t := by
  obtain ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
    h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁, h₂₂, h₂₄, h₂₃⟩ := h
  exact ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈,
    h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉, h₂₀, h₂₁, h₂₂, h₂₄, hPQ _ _ _ _ h₂₃⟩

theorem rwpGX_le {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (hQ : Q.Down) {m n : Nat}
    (hmn : m ≤ n) {ls : List SRec} {e : Expr} {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M Q n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q m ls e x := by
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun
  have hr := h xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' (by omega) hrun
  exact fun hfin => (hr hfin).mono hΦ
    (by omega) (fun M' C _ y hy => hQ.le (by omega) M' C _ _ y hy)

/-- `rwpGX_mono` reading the postcondition at the indices the runs leave, `≤ n`. -/
theorem rwpGX_mono_le {Φ : LocFam} {M : Mask} {P Q : PostGX} {n : Nat}
    (hPQ : ∀ M' C k, k ≤ n → ∀ ls t x, P M' C k ls t x → Q M' C k ls t x)
    {ls : List SRec} {e : Expr} {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M P n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun
  have hr := h xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun
  exact fun hfin => (hr hfin).post (fun M' C _ y hy => hPQ M' C _ (by omega) _ _ y hy)

theorem rwpGX_mono {Φ : LocFam} {M : Mask} {P Q : PostGX}
    (hPQ : ∀ M' C k ls t x, P M' C k ls t x → Q M' C k ls t x) {n : Nat}
    {ls : List SRec} {e : Expr} {x : XRes} (h : rwpGX (ℍ := ℍ) Φ M P n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls e x :=
  rwpGX_mono_le (fun M' C k _ => hPQ M' C k) h

/-! ### Final terms and steps -/

theorem rwpGX_zero {Φ : LocFam} {M : Mask} {Q : PostGX} {ls : List SRec} {e : Expr}
    {x : XRes} : rwpGX (ℍ := ℍ) Φ M Q 0 ls e x := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j _ _ hj
  omega

/-- The end of a run of no steps, at the start's mask. -/
theorem endOKX_refl {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec} {e : Expr}
    {x xf : XRes} {fρ : WRes} {ps : List FrameRec} {μ : Heap} (hf : ResU.Hash xf.1 x.1)
    (hc : ResU.CompS xf.1 x.1 fρ) (hv : (xf.2 + x.2).Valid) (hwx : WFC (xf.2 + x.2).counted x)
    (hsh : MaskShallow M.locs x.1) (hau : MaskAuth M x.2) (hT : TWNC fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) (hl : ResU.Lower fρ μ) (h : Q M (xf.2 + x.2).counted n ls e x) :
    EndOKX Φ M Q n ls x xf ps μ e := by
  have hvρ : ResU.Valid x.1 := (hash_valid hf).2
  refine ⟨M, x.1, PMap.empty, fρ, fρ, x.1, x.2, 0, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), ResU.comp_empty_right _, hl,
    ResU.comp_empty_right _, UpdVNm.refl Φ _ _ hvρ, noOwn_empty, hT, htg,
    RecAgree.refl _ _, ListAgree.refl _ _, ?_, ?_, ?_, ?_, hsh, ?_, hau, maskOff_emptyRes _, ?_,
    ?_, noBorrowAt_emptyRes _, ?_⟩
  · simpa using hv
  · intro α h₁ h₂; simp at h₁; exact absurd h₁ h₂
  · simpa using hwx
  · intro α _ hc'; exact absurd hc' (not_carries_empty α)
  · rw [Set.union_self]; exact hsh
  · rw [Set.sdiff_self]; exact maskShallow_empty _
  · rw [Mask.fresh_self]; exact flatNone_empty _
  · simpa using h

/-- **A final term in the postcondition**, at the run's mask. -/
theorem rwpGX_here {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec} {e : Expr}
    {x : XRes} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : ∀ C, Q M C n ls e x) : rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh hau _ hT htg hl hfd j μ' e' hj hrun
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  exact fun _ => by
    simpa using endOKX_refl (n := n - 0) hf hc hv hwx hsh hau hT htg hl (h _)

/-- **A final term in the postcondition**, at the world it was reached at. -/
theorem rwpGXat_here {Φ : LocFam} {M : Mask} {Q : PostGX} {n : Nat} {ls : List SRec}
    {e : Expr} {C : Set Life} {x : XRes} (hfin : ∀ μ, Final (ℍ := ℍ) μ e)
    (h : Q M C n ls e x) : rwpGXat (ℍ := ℍ) Φ M Q n ls e C x := by
  intro xf fρ ps μ hC hf hc hv hwf hwx hsh hau _ hT htg hl hfd j μ' e' hj hrun
  cases hrun with
  | more hs _ => exact absurd hs (hfin _ _ _)
  | refl =>
  refine fun _ => ?_
  rw [← hC] at h
  simpa using endOKX_refl (n := n - 0) hf hc hv hwx hsh hau hT htg hl h

/-- **A step that is its configuration's only one, for free.** -/
theorem rwpGX_det {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (hQ : Q.Down) {n : Nat}
    {ls : List SRec} {e e' : Expr} {x : XRes} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : rwpGX (ℍ := ℍ) Φ M Q n ls e' x) : rwpGX (ℍ := ℍ) Φ M Q n ls e x := by
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' E hj hrun
  cases hrun with
  | refl => exact fun hfin => absurd (hdet _).1 (hfin _ e')
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := (hdet _).2 _ _ hs
      have hr := h xf fρ ps _ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j' μ' E (by omega) t
      exact fun hfin => (hr hfin).mono hΦ
        (by omega) (fun M' C _ y hy => hQ.le (by omega) M' C _ _ y hy)

/-! ### Bind at a fixed mask -/

/-- `ρ` shallow at `A ∪ B`, from `A` and `B \ A`. -/
theorem maskShallow_union_diff {A B : Set Loc} {ρ : WRes} (hA : MaskShallow A ρ)
    (hB : MaskShallow (B \ A) ρ) : MaskShallow (A ∪ B) ρ := by
  intro l hl
  by_cases h : l ∈ A
  · exact hA l h
  · exact hB l ⟨hl.resolve_left h, h⟩

/-- What bind owes at the end of the bound run: a value continued in `K` at the run's mask, or a
stop, which `K` keeps final, ending the composite where the run ended. -/
def bindPostX (Φ : LocFam) (M : Mask) (Q : PostGX) (K : Kont) : PostGX :=
  fun M' C k ls' t x =>
    (M' = M ∧ rwpGXat (ℍ := ℍ) Φ M Q k ls' (K.plug t) C x) ∨
    ((∀ μ, Final (ℍ := ℍ) μ (K.plug t)) ∧ Q M' C k ls' (K.plug t) x)

/-- `rwpG_compose` at the one relation: the first run's end, then the continuation's run at the
frame together with the first run's garbage. The two `↭`s compose at `M ∪ (M ∪ M′) = M ∪ M′`. -/
theorem rwpGX_compose {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (K : Kont)
    {k₁ : Nat} {ls : List SRec} {x xf : XRes} {ps : List FrameRec} {μ₁ : Heap} {t : Expr}
    (_hsh₀ : MaskShallow M.locs x.1) (hwf₀ : WFC (xf.2 + x.2).counted xf) (hoff₀ : MaskOff M xf.1)
    (hend : EndOKX Φ M (bindPostX (ℍ := ℍ) Φ M Q K) k₁ ls x xf ps μ₁ t)
    (hfd₁ : FinDom μ₁) {j₂ : Nat} {μ' : Heap} {E : Expr} (hj : j₂ < k₁)
    (hrun : StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E) :
    Final (ℍ := ℍ) μ' E → EndOKX Φ M Q (k₁ - j₂) ls x xf ps μ' E := by
  obtain ⟨M₁, ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₆, h₇, h₉, hA, hB, hT', htg',
    hps', hls', hV, hN, hW', hWp, hS', hSπ, hAu, hOff, hSx, hFx, hNB, hC⟩ := hend
  rcases hC with ⟨hM₁, hC⟩ | ⟨hfinK, hQ⟩
  swap
  · -- a stop: the composite ends where the bound run ended
    cases hrun with
    | more hs _ => exact absurd hs (hfinK _ _ _)
    | refl =>
    have hend' : EndOKX Φ M Q k₁ ls x xf ps μ₁ (K.plug t) :=
      ⟨M₁, ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₆, h₇, h₉, hA, hB, hT', htg',
        hps', hls', hV, hN, hW', hWp, hS', hSπ, hAu, hOff, hSx, hFx, hNB, hQ⟩
    exact fun _ => by simpa using hend'
  subst M₁
  rw [Set.union_self] at hA hps' hls' hSπ
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
  intro hfin
  obtain ⟨M₂, ρ'', ρpp, Y'', Y''p, π'', g'', gpp, ps'', ls'', k₁', k₂, k₃, k₆, k₇, k₉, kA, kB,
    kT, ktg, kps, kls, kV, kN, kW, kWp, kS', kSπ, kAu, kOff, kSx, kFx, kNB, kC⟩ := hr hfin
  -- what `M₂` masks newly the frame `ρ_f ● ρp` does not hold, so neither part does
  have kFxf : FlatNone (M.fresh M₂) xf.1 := FlatNone.left hfz hvz kFx
  have kFp : FlatNone (M.fresh M₂) ρp := FlatNone.right hfz hvz kFx
  have hdiff : M₂.locs \ M.locs ⊆ M.fresh M₂ := fun l hl => Or.inl hl
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
  have hSp₂ : MaskShallow (M ∪ M₂).locs ρp := by
    rw [Mask.locs_union]
    exact maskShallow_union_diff hSp (kFp.maskShallow.mono hdiff)
  have hS'₂ : MaskShallow (M ∪ M₂).locs ρ' := by
    rw [Mask.locs_union]; exact maskShallow_union_diff hS' kSx
  refine ⟨M₂, ρ'', ZZ, F, Y''p, Yn, g'', gp + gpp, ps'', ls'', ResU.hash_symm hfρ'', hF, hZF,
    hFZ, k₇, hρ''Z, ?_, noOwn_compS hZZ' hB kB, kT, ktg,
    kps.trans (hps'.mono (Mask.lendLocs_mono Set.subset_union_left)),
    kls.trans (hls'.mono (Mask.lendLocs_mono Set.subset_union_left)), ?_, ?_, ?_,
    ?_, kS', maskShallow_comp hYn hSp₂ kSπ, kAu,
    maskOff_comp hZZ' (maskOff_fresh hOff kFp) kOff, ?_, kFxf, noBorrowAt_comp hZZ' hNB kNB, ?_⟩
  · have := UpdVNm.trans hΦ (Nat.sub_le k₁ j₂) hA
      (updVNm_frame (ResU.CompS.comm h₉) hYn (ResU.hash_symm hpρ') hpπ hS'₂ kSπ kA)
    exact this.mono (Set.union_subset (Mask.locs_mono Set.subset_union_left) le_rfl)
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
  · -- the start is shallow where `M₂` masks newly: `↭` carries an `imm` cell there to the end
    intro l ⟨hl, hlM⟩ s v χ hh hf
    have hπl := (hA.1.1 l hlM s v χ hh).mp hf
    rcases flatAt_comp_imm_split h₉ hπl s.join_mem with ⟨s₁, h₁', hf₁, -⟩ | ⟨s₂, h₂', hf₂, -⟩
    · exact kSx l ⟨hl, hlM⟩ s₁ v χ h₁' hf₁
    · exact absurd hf₂ (kFp l (Or.inl ⟨hl, hlM⟩) _)
  · rw [← hG₂]; exact kC

/-- **Bind at any final term, at a fixed mask.** -/
theorem rwpGX_bind {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Q : PostGX} (K : Kont) {n : Nat}
    {ls : List SRec} {e : Expr} {x : XRes}
    (hw : rwpGX (ℍ := ℍ) Φ M (bindPostX (ℍ := ℍ) Φ M Q K) n ls e x) :
    rwpGX (ℍ := ℍ) Φ M Q n ls (K.plug e) x := by
  classical
  intro xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' E hj hrun
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hr := hw xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j μ' e' hj hrun'
    refine fun hfin => ?_
    have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    have h := (rwpGX_compose hΦ K a₆ a₄ a₈ (hr hfin')
      (fd_stepsN hrun' a₁₂) (j₂ := 0) (by omega) (.refl _ _)) hfin
    simpa using h
  · have h := rwpGX_compose hΦ K a₆ a₄ a₈
      ((hw xf fρ ps μ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ j₁ μ₁ t (by omega) hrun₁) hirr)
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

/-- **The frame at any final term**, the framed predicate closed under the lists the inner
postcondition can be reached at. The framed part carries its own fractions (`WFSplit`), and the
inner part holds the mask's authorities. -/
theorem rwpGX_frame_post {Φ : LocFam} {M : Mask} {P : PostGX} (R : List SRec → XProp) {n : Nat}
    {ls : List SRec} {e : Expr}
    (hR : ∀ M' C k ls' t y, P M' C k ls' t y → ListAgree (M ∪ M') ls' ls → ∀ x, R ls x →
      R ls' x)
    {ρ₁ ρ₂ ρ : WRes} {g₁ g₂ : GRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hsplit : WFSplit (ρ₁, g₁) (ρ₂, g₂)) (hau₁ : MaskAuth M g₁) (hoff₂ : MaskOff M ρ₂)
    (hwp : rwpGX (ℍ := ℍ) Φ M P n ls e (ρ₁, g₁)) (hR₂ : R ls (ρ₂, g₂)) :
    rwpGX (ℍ := ℍ) Φ M (fun M' C k ls' t => sepX (P M' C k ls' t) (R ls')) n ls e
      (ρ, g₁ + g₂) := by
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
  intro hfin
  obtain ⟨M', ρ', ρp, Y', Y'p, π', g', gp, ps', ls', g₁', g₂', g₃, g₆, g₇, g₉, gA, gB, gT, gtg,
    gps, gls, gV, gN, gW, gWp, gS', gSπ, gAu, gOff, gSx, gFx, gNB, gC⟩ := hr hfin
  -- what `M′` masks newly the inner frame `ρ_f ● ρ₂` does not hold
  have gFf : FlatNone (M.fresh M') xf.1 := FlatNone.left hy hvy gFx
  have gF₂ : FlatNone (M.fresh M') ρ₂ := FlatNone.right hy hvy gFx
  have hdiff : M'.locs \ M.locs ⊆ M.fresh M' := fun l hl => Or.inl hl
  have hsh₂' : MaskShallow (M ∪ M').locs ρ₂ := by
    rw [Mask.locs_union]; exact maskShallow_union_diff hsh₂ (gF₂.maskShallow.mono hdiff)
  have hsh₁' : MaskShallow (M ∪ M').locs ρ₁ := by
    rw [Mask.locs_union]; exact maskShallow_union_diff hsh₁ gSx
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
  refine ⟨M', W, ρp, Y', Y'p, πn, g' + g₂, gp, ps', ls', hWf, hfW, g₃, g₆, g₇, hWπ, ?_, gB, gT,
    gtg, gps, gls, ?_, fun α hα hα₀ hc => hNy α hα hα₀ (carries_comp_left hy hvy hc), ?_, ?_,
    maskShallow_comp (ResU.CompS.comm hW) gS' (maskShallow_fresh hsh₂ gF₂),
    maskShallow_comp hπn hsh₂' gSπ, gAu.add_right ?_, gOff, ?_, gFf, gNB,
    ρ', ρ₂, g', g₂, ResU.CompS.comm hW, rfl, ?_, hR _ _ _ _ _ _ gC gls _ hR₂⟩
  · exact updVNm_frame (ResU.CompS.comm hcρ) hπn
      ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, hvρ⟩ h₂π hsh₁' gSπ gA
  · rw [← hGe]; exact gV
  · have hW₂ : WFC (xf.2 + (g' + g₂ + gp)).counted (ρ₂, g₂) :=
      wfc_grow hwx₂ (fun α hα hα₀ hc => hNy α hα hα₀ (carries_comp_right hy hvy hc))
    have hW₁ : WFC (xf.2 + (g' + g₂ + gp)).counted (ρ', g') := by rw [← hGe]; exact gW
    exact wfc_comp (ResU.CompS.comm hW) hW₁ hW₂
  · rw [← hGe]; exact gWp
  · have : (xf.2 + (g' + g₂ + gp)).Valid := by rw [← hGe]; exact gV
    exact (GRes.Valid.right (GRes.Valid.left (by rwa [← GRes.add_assoc] at this)))
  · exact maskShallow_comp hcρ gSx (gF₂.maskShallow.mono hdiff)
  · rw [← hGe]; exact gC

/-- **The frame at any final term.** The framed predicate is closed under the lists that agree off
the locations lent across stops at the run's mask and the stop's. -/
theorem rwpGX_frame {Φ : LocFam} {M : Mask} {P : PostGX} (R : List SRec → XProp)
    (hR : ∀ M' ls ls', ListAgree (M ∪ M') ls' ls → ∀ x, R ls x → R ls' x) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ₁ ρ₂ ρ : WRes} {g₁ g₂ : GRes} (hcρ : ResU.CompS ρ₁ ρ₂ ρ)
    (hsplit : WFSplit (ρ₁, g₁) (ρ₂, g₂)) (hau₁ : MaskAuth M g₁) (hoff₂ : MaskOff M ρ₂)
    (hwp : rwpGX (ℍ := ℍ) Φ M P n ls e (ρ₁, g₁)) (hR₂ : R ls (ρ₂, g₂)) :
    rwpGX (ℍ := ℍ) Φ M (fun M' C k ls' t => sepX (P M' C k ls' t) (R ls')) n ls e
      (ρ, g₁ + g₂) :=
  rwpGX_frame_post R (fun M' _ _ ls' _ _ _ h => hR M' ls ls' h) hcρ hsplit hau₁ hoff₂ hwp hR₂

/-! ### The relation -/

/-- A postcondition over values, at the counted set and the index. -/
abbrev PostX : Type := Set Life → Nat → List SRec → Val → XProp

/-- What a stop owes, at every index and list. -/
abbrev ContX : Type := Nat → List SRec → Expr → XProp

/-- A protocol table: the stop at `t` of a segment at the mask `M`, its continuation resumed at
`M′`, at the counted set and the index `k`, owing `Ψ`. -/
abbrev TableX : Type := Mask → Mask → Set Life → Nat → List SRec → Expr → ContX → XProp

/-- A value in `Q`, reached at the run's mask `M`. -/
def valPostX (M : Mask) (Q : PostX) : PostGX := fun M' C k ls t x =>
  M' = M ∧ ∃ v : Val, t = v.1 ∧ Q C k ls v x

/-- A value in `Q` at the segment's mask, or a stop the table allows, owing what is owed at the
mask its continuation resumes at. -/
def erwpXPost (M : Mask) (Tb : TableX) (Q : PostX) (Ψ : Mask → ContX) : PostGX :=
  fun M' C k ls t x => valPostX M Q M' C k ls t x ∨ Tb M M' C k ls t (Ψ M') x

/-- **The one relation**: `erwp` over `WRes × GRes` at the mask `M`. A stop's continuation is
owed at the mask the stop resumes it at. -/
def erwpX (Φ : LocFam) : Mask → TableX → PostX → Nat → List SRec → Expr → XProp
  | M, Tb, Q, n, ls, e => rwpGX (ℍ := ℍ) Φ M (erwpXPost M Tb Q (fun M' k' ls' e' =>
      if _h : k' < n then erwpX Φ M' Tb Q k' ls' e' else fun _ => False)) n ls e
termination_by _ _ _ n => n

/-- What `erwpX` at `N` owes below it, at the mask `M′`. -/
def erwpXC (Φ : LocFam) (Tb : TableX) (Q : PostX) (N : Nat) : Mask → ContX :=
  fun M' k' ls' e' => if k' < N then erwpX (ℍ := ℍ) Φ M' Tb Q k' ls' e' else fun _ => False

theorem erwpX_eq (Φ : LocFam) (M : Mask) (Tb : TableX) (Q : PostX) (n : Nat) (ls : List SRec)
    (e : Expr) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e =
      rwpGX (ℍ := ℍ) Φ M (erwpXPost M Tb Q (erwpXC (ℍ := ℍ) Φ Tb Q n)) n ls e := by
  rw [erwpX]
  congr 1

/-- A table reads what is owed only below the index it stops at. -/
def TableX.Local (Tb : TableX) : Prop :=
  ∀ M M' C k ls t (Ψ Ψ' : ContX) x, (∀ k', k' < k → ∀ ls e y, Ψ k' ls e y → Ψ' k' ls e y) →
    Tb M M' C k ls t Ψ x → Tb M M' C k ls t Ψ' x

/-- A table is downward closed in its index. -/
def TableX.Down (Tb : TableX) : Prop :=
  ∀ M M' C k ls t Ψ x, Tb M M' C (k + 1) ls t Ψ x → Tb M M' C k ls t Ψ x

def PostX.Down (Q : PostX) : Prop := ∀ C n ls v x, Q C (n + 1) ls v x → Q C n ls v x

theorem erwpX_unfold_at {Φ : LocFam} {M : Mask} {Tb : TableX} (hTb : Tb.Local) {Q : PostX}
    {n N : Nat} (hnN : n ≤ N) {ls : List SRec} {e : Expr} {x : XRes}
    (h : erwpX (ℍ := ℍ) Φ M Tb Q n ls e x) :
    rwpGX (ℍ := ℍ) Φ M (erwpXPost M Tb Q (erwpXC (ℍ := ℍ) Φ Tb Q N)) n ls e x := by
  rw [erwpX_eq] at h
  refine rwpGX_mono_le (fun M' C k hk ls' t y ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb M M' C k ls' t _ _ y (fun k' hk' ls'' e'' y' hΨ => ?_) ht)
    simp only [erwpXC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem erwpX_fold_at {Φ : LocFam} {M : Mask} {Tb : TableX} (hTb : Tb.Local) {Q : PostX}
    {n N : Nat} (hnN : n ≤ N) {ls : List SRec} {e : Expr} {x : XRes}
    (h : rwpGX (ℍ := ℍ) Φ M (erwpXPost M Tb Q (erwpXC (ℍ := ℍ) Φ Tb Q N)) n ls e x) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls e x := by
  rw [erwpX_eq]
  refine rwpGX_mono_le (fun M' C k hk ls' t y ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb M M' C k ls' t _ _ y (fun k' hk' ls'' e'' y' hΨ => ?_) ht)
    simp only [erwpXC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem erwpXPost_down {M : Mask} {Tb : TableX} (hTb : Tb.Down) {Q : PostX} (hQ : Q.Down)
    (Ψ : Mask → ContX) : (erwpXPost M Tb Q Ψ).Down := by
  intro M' C k ls t x h
  rcases h with ⟨hM, v, hv, hq⟩ | h
  · exact Or.inl ⟨hM, v, hv, hQ _ _ _ _ _ hq⟩
  · exact Or.inr (hTb _ _ _ _ _ _ _ _ h)

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
  exact rwpGX_here (fun μ => final_val μ v) (fun C => Or.inl ⟨rfl, v, rfl, h C⟩)

/-- A table is closed under a context `K` around the stopped term: a stop at `t` owing `Ψ` is a
stop at `K[t]` owing `Ψ'` whenever `Ψ'` covers `Ψ` with `K` put back. -/
def TableX.CtxClosed (Tb : TableX) (K : Kont) : Prop :=
  ∀ M M' C k ls t (Ψ Ψ' : ContX) x,
    (∀ k', k' < k → ∀ ls' e y, Ψ k' ls' e y → Ψ' k' ls' (K.plug e) y) →
    Tb M M' C k ls t Ψ x → Tb M M' C k ls (K.plug t) Ψ' x ∧ ∀ μ, Final (ℍ := ℍ) μ (K.plug t)

/-- **Bind at `erwpX`**: a context around a computation whose stops the table carries through
`K`. A value continues in the context at the segment's mask; a stop owes the context's
continuation at the mask it resumes at, covered by induction on the index. The continuation of a
value is owed at every mask, since a value of a later segment is reached at that segment's. -/
theorem erwpX_bind {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableX} (hL : Tb.Local)
    {Q Q' : PostX} (K : Kont) (hK : TableX.CtxClosed (ℍ := ℍ) Tb K)
    (hcont : ∀ M C k ls (v : Val) x, Q' C k ls v x →
      erwpX (ℍ := ℍ) Φ M Tb Q k ls (K.plug v.1) x) :
    ∀ n M ls e x, erwpX (ℍ := ℍ) Φ M Tb Q' n ls e x →
      erwpX (ℍ := ℍ) Φ M Tb Q n ls (K.plug e) x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M ls e x h
  rw [erwpX_eq]
  refine rwpGX_bind hΦ K ?_
  refine rwpGX_mono_le (fun M' C k hk ls' t y ht => ?_) (erwpX_unfold_at hL le_rfl h)
  rcases ht with ⟨rfl, v, rfl, hv⟩ | ht
  · exact Or.inl ⟨rfl, (erwpX_unfold_at hL hk (hcont M' C k ls' v y hv)).at C⟩
  · obtain ⟨ht', hfin⟩ := hK M M' C k ls' t _ (erwpXC (ℍ := ℍ) Φ Tb Q n M') y
      (fun k' hk' ls'' e'' z hz => by
        simp only [erwpXC, show k' < n by omega, if_true] at hz ⊢
        exact ih k' (by omega) _ _ _ _ hz) ht
    exact Or.inr ⟨hfin, Or.inr ht'⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
