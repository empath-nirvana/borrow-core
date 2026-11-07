import Core.Chain.SI.StopFrameN

/-!
# The Mut Anti-Frame (`[TR]` 6.66) live across a stop, at `erwp`

**Not a transcription.** `[TR]` 6.66 opens a `mut` cell `ℓ ↦ mut(β, v, ρ_v, P̂)` for a run that
returns: the callback runs on `ℓ ↦ own(v) ● ρ_v`, and at its end hands back `ℓ ↦ own(w) ● ρ′_v`
with `ρ′_v ∈ P̂(w)`, which is sealed again. Across a stop the post-configuration `ρ ↭ π` is asked
at the stop too, and at the stop the cell is `own` in `π` and `mut` in `ρ`.

## The design: seal at the stop, reopen at the resume

At a stop the anti-frame does at the stop what 6.66's proof does at the return: the cell is
sealed, `ℓ ↦ own(w) ● ρ′_v` replaced by `ℓ ↦ mut(β, w, ρ′_v, F k)` (`rwpG_M_antiFrameG`, the
printed proof at any final term, where `rwp_M_antiFrame` has it at a value). The sealed cell goes
into the continuation's share; when the continuation is resumed at `k′ < k`, the anti-frame opens
it again (`erwp_M_antiFrame` at `k′`, by induction on the index). It is the Mut Frame's fold
(`erwp_M_frame`, `SI/StopFrameN.lean`) one level up: the Mut Frame folds `mut → own` at a stop, the anti-frame
seals `own → mut`.

The seal needs, at the stop, the content `ρ′_v` in the family: the callback must stop only with
the cell in a state the family admits. That is a condition on the continuation's share, which
`opTableN` does not carry; `opTableG T G` is `opTableN T`'s perform stops with a guard `G` on the
share. The callback of the anti-frame runs at `opTableG T (CellFold ℓ β F)`.

The guard is produced where the cell's content is restored at a stop: by a Mut Frame of the
opened cell (`[TR]` 6.174, `withbor3`), whose fold at the stop gives `ℓ ↦ own(v″) ● χ` with `χ` in
the inner lend's family (`erwp_M_frameF`), or of a cell inside the content (a boxed field), with
the opened cell framed (`erwpG_frame`).

## Conditions

The table's non-abortive entries are must-resume and resumed under `extF` (`AFOK`): an
abortive stop returns nothing to the anti-frame, a discarded continuation never gives the sealed
cell back to the lender, and the world condition is read at the share before and after the seal.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### The seal at any final term -/

/-- `AFPost` over terms: the cell's content handed back at the index's member, and the seal
handed on. -/
def AFPostG (l : Loc) (β : Life) (F : Nat → Val → SPropS Loc Val β) (Q : PostG) : PostG :=
  fun k ls' t ρ' => ∃ (w : Val) (σ' : WRes) (h' : σ'.InStratum β) (hw' : F k w ⟨σ', h'⟩)
    (R rest : WRes), ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρ' ∧
    ResU.CompS σ' R rest ∧
    ∀ X, ResU.CompS R (ResU.single l (CellU.mutOf β w σ' h' (F k) hw')) X → Q k ls' t X

/-- `AFPostG`, the seal handed on only at a valid resource. -/
def AFPostGV (l : Loc) (β : Life) (F : Nat → Val → SPropS Loc Val β) (Q : PostG) : PostG :=
  fun k ls' t ρ' => ∃ (w : Val) (σ' : WRes) (h' : σ'.InStratum β) (hw' : F k w ⟨σ', h'⟩)
    (R rest : WRes), ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρ' ∧
    ResU.CompS σ' R rest ∧
    ∀ X, ResU.CompS R (ResU.single l (CellU.mutOf β w σ' h' (F k) hw')) X → ResU.Valid X →
      Q k ls' t X

/-- **Mut Anti-Frame at any final term** (`[TR]` 6.66's proof at `rwpG`): `rwp_M_antiFrame`'s
proof, read at the final term the run reached instead of at a value. The sealed resource it hands
the callback's post is valid (`AFPostGV`). -/
theorem rwpG_M_antiFrameGV {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {Q : PostG} {n : Nat}
    {ls : List SRec} {e : Expr} {v : Val} {σP : WRes} {hstr : σP.InStratum β} {j : Nat}
    {hwit : F j v ⟨σP, hstr⟩} {ρa ρ : WRes}
    (hsplit : ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ)
    (hA : ∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
      rwpG (ℍ := ℍ) Φ (AFPostGV l β F Q) n ls e X) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  classical
  intro ρf sρ ps μ hH2 hsρ hT htg hI hlow hfd jr μ' e' hj hrun hfin
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  obtain ⟨hvm, hva⟩ := ResU.Valid.split hsplit hvρ
  obtain ⟨W, hW⟩ := ResU.compS_own_of_valid_mut hvm
  have hmaH : ResU.Hash (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa :=
    ⟨hsplit.1, ρ, hsplit, hvρ⟩
  have haW : ResU.Hash ρa W := (ResU.six24 hW).mp (ResU.hash_symm hmaH)
  have hvW : ResU.Valid W := by
    obtain ⟨-, s, hs, hv⟩ := haW; exact (ResU.Valid.split hs hv).2
  obtain ⟨hmf, haf⟩ := ResU.Hash.split hsplit (ResU.hash_symm hH2)
  have hfW : ResU.Hash ρf W := (ResU.six24 hW).mp (ResU.hash_symm hmf)
  obtain ⟨X, hX⟩ := (ResU.compS_defined_iff ρa W).mpr haW.1
  have hfX : ResU.Hash ρf X := ResU.hash_of_pairwise (ResU.hash_symm haf) haW hfW hX
  have hwpX := hA W X hW hX
  obtain ⟨fρ, h4, hvfρ⟩ := hfX.2
  obtain ⟨FA, hFA⟩ := (ResU.compS_defined_iff ρf ρa).mpr (ResU.hash_symm haf).1
  obtain ⟨FA₁, hFA₁, hFAmc⟩ :=
    (ResU.CompS.assoc ρf ρa (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) sρ).mp
      ⟨ρ, ResU.CompS.comm hsplit, hsρ⟩
  obtain rfl : FA = FA₁ := ResU.CompS.functional hFA hFA₁
  obtain ⟨FA₂, hFA₂, hFAWc⟩ := (ResU.CompS.assoc ρf ρa W fρ).mp ⟨X, hX, h4⟩
  obtain rfl : FA = FA₂ := ResU.CompS.functional hFA hFA₂
  have hFAm : ResU.Hash FA (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) :=
    ResU.hash_symm (ResU.hash_of_pairwise hmf (ResU.hash_symm haf) hmaH hFA)
  have hFAW : ResU.Hash FA W :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hfW) (ResU.hash_symm haf)
      (ResU.hash_symm haW) hFA)
  have hTin : TWNC fρ ps (rsOf ls) :=
    TWNC.mutUnfold hT (ResU.CompS.comm hFAmc) (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) (ResU.CompS.comm hFAmc) a).mp
      ha) htg
  have hlowin : ResU.Lower fρ μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hFAmc hFAm hFAWc hFAW).mp hlow
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps'', ls'', h1, h2, h3, h6, h7, h9, h10, h11, hT'', htg'',
    hps'', hls'', h12⟩ := hwpX ρf fρ ps μ hfX h4 hTin htgin hI hlowin hfd jr μ' e' hj hrun hfin
  obtain ⟨w, σ', h', hw', ρb, rest, hcr, hcr2, hb⟩ := h12
  obtain ⟨W'', hW''₁, hW''₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf w)) σ' ρb ρ').mp ⟨rest, hcr2, hcr⟩
  have hW'' : ResU.CompS σ' (ResU.single l (CellU.ownOf w)) W'' := ResU.CompS.comm hW''₁
  have hvρ' : ResU.Valid ρ' := by
    obtain ⟨-, s, hs, hv⟩ := h1; exact (ResU.Valid.split hs hv).1
  have hvW'' : ResU.Valid W'' := (ResU.Valid.split hW''₂ hvρ').1
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    ResU.valid_single_mut_of_wit hW'' hvW''
  have hW''b : ResU.Hash W'' ρb := ⟨hW''₂.1, ρ', hW''₂, hvρ'⟩
  have hbm'' : ResU.Hash ρb (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''b)
  obtain ⟨RB, hRB⟩ := (ResU.compS_defined_iff ρb
    (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw'))).mpr hbm''.1
  obtain ⟨hfp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hW''p, hbp⟩ := ResU.Hash.split hW''₂ hρ'p
  obtain ⟨hW''f, hbf⟩ := ResU.Hash.split hW''₂ h1
  have hpm'' : ResU.Hash ρp (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''p)
  have hfm'' : ResU.Hash ρf (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''f)
  have hfRB : ResU.Hash ρf RB :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbm'' hfm'' hRB
  obtain ⟨FRB, hFRB⟩ := (ResU.compS_defined_iff ρf RB).mpr hfRB.1
  obtain ⟨BP, hBP⟩ := (ResU.compS_defined_iff ρb ρp).mpr hbp.1
  have hpRB : ResU.Hash ρp RB :=
    ResU.hash_of_pairwise (ResU.hash_symm hbp) hbm'' hpm'' hRB
  have hpFRB : ResU.Hash ρp FRB :=
    ResU.hash_of_pairwise (ResU.hash_symm hfp) hfRB hpRB hFRB
  obtain ⟨FRBp, hFRBp⟩ := (ResU.compS_defined_iff FRB ρp).mpr (ResU.hash_symm hpFRB).1
  obtain ⟨π', hπ'⟩ := (ResU.compS_defined_iff RB ρp).mpr (ResU.hash_symm hpRB).1
  obtain ⟨FW, hFW, hFWb⟩ := (ResU.CompS.assoc ρf W'' ρb fρ').mp ⟨ρ', hW''₂, h2⟩
  obtain ⟨BP₁, hBP₁, hFWBP⟩ := (ResU.CompS.assoc FW ρb ρp fρ'p).mpr ⟨fρ', hFWb, h6⟩
  obtain rfl : BP = BP₁ := ResU.CompS.functional hBP hBP₁
  obtain ⟨WBP, hWBP, hfWBP⟩ := (ResU.CompS.assoc ρf W'' BP fρ'p).mpr ⟨FW, hFW, hFWBP⟩
  obtain ⟨FB, hFB, hFBW⟩ :=
    (ResU.CompS.assoc ρf BP W'' fρ'p).mp ⟨WBP, ResU.CompS.comm hWBP, hfWBP⟩
  obtain ⟨π'₁, hπ'₁, hfπ'⟩ := (ResU.CompS.assoc ρf RB ρp FRBp).mpr ⟨FRB, hFRB, hFRBp⟩
  obtain rfl : π' = π'₁ := ResU.CompS.functional hπ' hπ'₁
  obtain ⟨MP, hMP, hbMP⟩ := (ResU.CompS.assoc ρb (ResU.single l
    (CellU.mutOf β w σ' h' (F (n - jr)) hw')) ρp π').mpr ⟨RB, hRB, hπ'⟩
  obtain ⟨BP₂, hBP₂, hBPm⟩ := (ResU.CompS.assoc ρb ρp
    (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) π').mp
      ⟨MP, ResU.CompS.comm hMP, hbMP⟩
  obtain rfl : BP = BP₂ := ResU.CompS.functional hBP hBP₂
  obtain ⟨FB₁, hFB₁, hFBm⟩ :=
    (ResU.CompS.assoc ρf BP (ResU.single l
      (CellU.mutOf β w σ' h' (F (n - jr)) hw')) FRBp).mp ⟨π', hBPm, hfπ'⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  have hfBP : ResU.Hash ρf BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbp hfp hBP
  have hmBP : ResU.Hash (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbm'') hbp
      (ResU.hash_symm hpm'') hBP
  have hFBm' : ResU.Hash FB (ResU.single l (CellU.mutOf β w σ' h' (F (n - jr)) hw')) :=
    ResU.hash_symm (ResU.hash_of_pairwise
      (ResU.hash_symm hfm'') hfBP hmBP hFB)
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hFBW' : ResU.Hash FB W'' := ⟨hFBW.1, fρ'p, hFBW, hvfρ'p⟩
  have hmem₂ : ResU.Lower FRBp μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFBm hFBm' hFBW hFBW').mpr h7
  obtain ⟨BPW, hBPW₁, hBPW₂⟩ := (ResU.CompS.assoc W'' ρb ρp π).mpr ⟨ρ', hW''₂, h9⟩
  obtain rfl : BP = BPW := ResU.CompS.functional hBP hBPW₁
  have hvπ' : ResU.Valid π' := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hpRB
    exact ResU.CompS.functional hs hπ' ▸ hv
  have hupd : UpdN Φ (n - jr) ρ π' :=
    six28N hΦ hF le_rfl hW hW'' (ResU.CompS.comm hsplit) hBPm hX (ResU.CompS.comm hBPW₂)
      hvρ hvπ' h10.2.1 h10.2.2 h10.1
  have hvFRBp : ResU.Valid FRBp := by obtain ⟨σ, hσ, -⟩ := hmem₂; exact ⟨σ, hσ⟩
  have hTout : TWNC FRBp ps'' (rsOf ls'') :=
    TWNC.mutFold hT'' hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) hvFRBp
  have htgout : Tagged FRBp ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) a).mpr ha) htg''
  exact ⟨RB, ρp, FRB, FRBp, π', ps'', ls'', ResU.hash_symm hfRB, hFRB, hpFRB, hFRBp, hmem₂,
    hπ', ⟨hupd, hvρ, hvπ'⟩, h11, hTout, htgout, hps'', hls'', hb RB hRB (ResU.Valid.split hπ' hvπ').1⟩

/-- **Mut Anti-Frame at any final term** (`rwpG_M_antiFrameGV`, the sealed resource's validity
not read). -/
theorem rwpG_M_antiFrameG {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {Q : PostG} {n : Nat}
    {ls : List SRec} {e : Expr} {v : Val} {σP : WRes} {hstr : σP.InStratum β} {j : Nat}
    {hwit : F j v ⟨σP, hstr⟩} {ρa ρ : WRes}
    (hsplit : ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ)
    (hA : ∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
      rwpG (ℍ := ℍ) Φ (AFPostG l β F Q) n ls e X) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ :=
  rwpG_M_antiFrameGV hΦ hF hsplit fun W X hW hX =>
    rwpG_mono (fun _ _ _ _ ⟨w, σ', h', hw', R, rest, h1, h2, hQ⟩ =>
      ⟨w, σ', h', hw', R, rest, h1, h2, fun X hX _ => hQ X hX⟩) (hA W X hW hX)

/-! ### Guarded tables -/

/-- A guard on a stop's continuation share, at the index and list of the stop. -/
abbrev ShareG : Type := Nat → List SRec → WRes → Prop

/-- **`opTableN T`'s perform stops whose continuation share satisfies `G`.** -/
def opTableG (T : OpTabN) (G : ShareG) : TableN := fun k ls t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntN) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆
        (en.PA k ls v ⋆ fun ρ => G k ls ρ ∧ contShareN en k ls K Ψ ρ)

/-- A guard is downward closed in the index. -/
def ShareG.Down (G : ShareG) : Prop := ∀ k ls ρ, G (k + 1) ls ρ → G k ls ρ

theorem opTableG_local (T : OpTabN) (G : ShareG) : (opTableG T G).Local := by
  intro k ls t Ψ Ψ' ρ hΨ ⟨K, n, i, v, en, h⟩
  obtain ⟨hp, ρa, ρk, hc, hA, hG, hu, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hG, hu, fun ls' he =>
    ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
      (hcont ls' he).2⟩⟩⟩

theorem opTableG_down {T : OpTabN} (hT : T.Down) {G : ShareG} (hG : G.Down) :
    (opTableG T G).Down := by
  intro k ls t Ψ ρ ⟨K, n, i, v, en, h⟩
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hGk, hu, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
    hT.pa _ _ _ h₃ _ _ _ _ hA, hG _ _ _ hGk, hu, fun ls' he =>
    ⟨fun k' hk => (hcont ls' he).1 k' (by omega), fun hq P hP =>
      hT.fin _ _ _ _ h₃ hP _ _ _ _ ((hcont ls' he).2 hq P hP)⟩⟩⟩

/-- A guarded stop is a stop of `opTableN`. -/
theorem opTableG_le_N {T : OpTabN} {G : ShareG} {k : Nat} {ls : List SRec} {t : Expr}
    {Ψ : ContN} {ρ : WRes} (h : opTableG T G k ls t Ψ ρ) : opTableN T k ls t Ψ ρ := by
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨hp, ρa, ρk, hc, hA, -, hu, hcont⟩ := pure_sep_iff.mp h
  exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, hcont⟩⟩

/-- **The cell `ℓ` sealable in the share**: `ℓ ↦ own(w) ● χ ● R` with `χ` in `F k`. -/
def CellFold (l : Loc) (β : Life) (F : Nat → Val → SPropS Loc Val β) : ShareG :=
  fun k _ ρ => ∃ (w : Val) (χ : WRes) (h : χ.InStratum β) (_ : F k w ⟨χ, h⟩) (R rest : WRes),
    ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρ ∧ ResU.CompS χ R rest

theorem cellFold_down {l : Loc} {β : Life} {F : Nat → Val → SPropS Loc Val β}
    (hF : DownFam β F) : (CellFold l β F).Down :=
  fun _ _ _ ⟨w, χ, h, hw, R, rest, h1, h2⟩ => ⟨w, χ, h, hF _ w _ hw, R, rest, h1, h2⟩

/-- **The tables an anti-frame may stop at**: every non-abortive entry is must-resume and
resumed under `extF`. -/
def OpTabN.AFOK (T : OpTabN) : Prop :=
  ∀ m i en, T m i = some en → en.abort = false → en.q = .lin ∧ en.wc = extF

/-- **`extF` across the seal.** The callback's share is `ℓ ↦ own(w) ● σ′ ● R`; the sealed share is
`R ● ℓ ↦ mut(β, w, σ′)`. A location frozen in `σ′` is frozen in the sealed cell's witness. -/
theorem extF_seal {ls ls' : List SRec} {l : Loc} {w : Val} {rest σ' R ρk ρk' : WRes}
    {ψ : CellU Loc Val} (hk1 : ResU.CompS (ResU.single l (CellU.ownOf w)) rest ρk)
    (hk2 : ResU.CompS σ' R rest) (hRk : ResU.CompS R (ResU.single l ψ) ρk')
    (hψ : ψ.kind = Kind.mut) (hwit : ψ.wit = σ') (h : extF ls ls' ρk') : extF ls ls' ρk := by
  intro r hr ⟨m, hf, hm⟩
  refine h r hr ⟨m, ?_, hm⟩
  rcases hf.split hk1 with hf | hf
  · exact absurd hf not_frz_single_own
  rcases hf.split hk2 with hf | hf
  · exact Frz.of_compS_right hRk (Frz.inMut (ResU.single_get_self _ _) hψ (hwit ▸ hf))
  · exact Frz.of_compS_left hRk hf

/-! ### The anti-frame across stops -/

/-- **Mut Anti-Frame at `erwp`, across stops.** The cell `ℓ ↦ mut(β, v, ρ_v, F j)`, `Φ ℓ = (β, F)`,
opened for a callback in `erwp` at `opTableG T (CellFold ℓ β F)`: at a return, 6.66; at a stop,
the cell sealed at the member of the stop's index and put into the continuation's share; at the
resume, opened again at the index the resume is at, by induction on the index. -/
theorem erwp_M_antiFrame {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {F : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, F⟩) {T : OpTabN} (hT : T.AFOK)
    {Q : PostN} :
    ∀ n ls e (v : Val) (σP : WRes) (hstr : σP.InStratum β) (j : Nat) (hwit : F j v ⟨σP, hstr⟩)
      (ρa ρ : WRes),
      ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (F j) hwit)) ρa ρ →
      (∀ W X, ResU.CompS σP (ResU.single l (CellU.ownOf v)) W → ResU.CompS ρa W X →
        erwp (ℍ := ℍ) Φ (opTableG T (CellFold l β F)) (AFPost l β F Q) n ls e X) →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e v σP hstr j hwit ρa ρ hsplit hA
  rw [erwp_eq]
  refine rwpG_M_antiFrameG hΦ hF hsplit fun W X hW hX => ?_
  have h := hA W X hW hX
  rw [erwp_eq] at h
  refine rwpG_mono_le (fun k hk ls' t ρ' ht => ?_) h
  rcases ht with ⟨v', rfl, w, σ', h', hw', R, rest, h1, h2, hQ⟩ | ⟨K, m, i, v₀, en, hp⟩
  · exact ⟨w, σ', h', hw', R, rest, h1, h2, fun X hX => Or.inl ⟨v', rfl, hQ X hX⟩⟩
  -- a stop: seal the cell in the continuation's share
  obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa', ρk, hcak, hPA, ⟨w, σ', h', hw', R, rest, hk1, hk2⟩, -,
    hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨hq, hwc⟩ := hT m i en hTe ha
  -- `ρ′ = ℓ ↦ own(w) ● (σ′ ● (ρ_a ● R))`
  obtain ⟨y, hy1, hy2⟩ := compS_lcomm hk1 hcak
  obtain ⟨R', hR', hσR'⟩ := compS_lcomm hk2 hy1
  refine ⟨w, σ', h', hw', R', y, hy2, hσR', fun X hX => ?_⟩
  obtain ⟨ρk', hRk, hX'⟩ := compS_reassoc hR' hX
  refine Or.inr (Or.inl ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa', ρk', hX', hPA,
    fun hu => absurd (hq.symm.trans hu) (by simp), fun ls'' he =>
      ⟨fun k' hk' w' σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩)
  simp only [erwpC, show k' < n by omega, if_true]
  have he' : en.wc ls' ls'' ρk := by
    rw [hwc] at he ⊢
    exact extF_seal hk1 hk2 hRk (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) he
  obtain ⟨ac, hac, hacX⟩ := compS_exch hRk hXB
  refine ih k' (by omega) ls'' _ w σ' h' k hw' ac XB (ResU.CompS.comm hacX)
    fun W X₀ hW hX₀ => ?_
  -- `X₀ = (R ● σ_B) ● (σ′ ● ℓ ↦ own(w)) = ρ_k ● σ_B`
  obtain ⟨t, ht1, ht2⟩ := compS_reassoc hac hX₀
  obtain ⟨ac3, hac3, hW3⟩ := compS_lcomm (ResU.CompS.comm ht1) ht2
  obtain ⟨WR, hWR, hX₀'⟩ := compS_reassoc' hac3 hW3
  obtain ⟨ac2, hac2, hac2W⟩ := compS_exch hW hWR
  obtain rfl : ac2 = rest := ResU.CompS.functional hac2 hk2
  obtain rfl : WR = ρk := ResU.CompS.functional (ResU.CompS.comm hac2W) hk1
  have hc := (hcont ls'' he').1 k' (by omega) w' σB X₀ hB hX₀'
  simp only [erwpC, show k' < n by omega, if_true] at hc
  exact hc

/-! ### The Mut Frame's fold, recorded at the stop -/

/-- **Mut Frame at `erwp`, across stops, its stops guarded by the fold**: `erwp_M_frame` with
the fact its fold establishes at each stop kept in the table: the lent cell is `own` in the
continuation's share with its content in the family at the stop's index. -/
theorem erwp_M_frameF {Φ : LocFam} {l : Loc} {A : Life} {F : Nat → Val → SPropS Loc Val A}
    (hF : DownFam A F) {T : OpTabN} (hT : T.LendOK A) {Q : PostN} :
    ∀ n j, n ≤ j → ∀ ls e (v : Val) (ρP ρlP ρb ρ : WRes) (houtP : ρP.InStratum A),
      ρb.InStratum (↓A) → ∀ (P : Val → SPropS Loc Val A),
      (∀ u r, SPropS.toU (P u) r → SPropS.toU (F j u) r) → ∀ (hwit : P v ⟨ρP, houtP⟩),
      ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP → ResU.CompS ρlP ρb ρ →
      (∀ BM, ResU.CompS ρb (ResU.single l (CellU.mutOf A v ρP houtP P hwit)) BM →
        erwp (ℍ := ℍ) (Φ.set l A F) (opTableN T) (MFPost l A F Q) n ls e BM) →
      erwp (ℍ := ℍ) Φ (opTableG T (CellFold l A F)) Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro j hjn ls e v ρP ρlP ρb ρ houtP houtb P hPF hwit hclP hcρ hA
  rw [erwp_eq]
  refine rwpG_M_frameG hF hjn houtP houtb hPF hwit hclP hcρ ?_ (fun BM hBM => by
    have h := hA BM hBM
    rw [erwp_eq] at h
    exact h)
  intro k hk ls' t ρ' ρp X hQin hnoρp h9 hdX v'' χ hχ P'' hw'' hPk hsplit W'' hW'' Y hY
  have hkm'' : (CellU.mutOf A v'' χ hχ P'' hw'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hXl : X.get l = some (CellU.mutOf A v'' χ hχ P'' hw'') :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hsplit) (ResU.single_get_self _ _) hkm'').2
  rcases hQin with ⟨w, rfl, houtρ', hwand⟩ | ⟨K, m, i, v₀, en, hp⟩ | ⟨K, m, i, v₀, en, hp⟩
  · -- a return: 6.65's end -- the borrow is garbage, the content read back in `F k`
    rcases ResU.CompS.get_split_of_ne_imm h9 hXl hkm'' with ⟨hg, -⟩ | ⟨-, hgp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hpd := ResU.del_compS hgp
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨ρp, hpd, h9⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨Z1, hZ1, hρ'Z1⟩ := (ResU.CompS.assoc ρ' (ρp.del l) W'' Y).mpr ⟨_, hD, hY⟩
    obtain ⟨R, hR, hRY⟩ :=
      (ResU.CompS.assoc ρ' W'' (ρp.del l) Y).mp ⟨Z1, ResU.CompS.comm hZ1, hρ'Z1⟩
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
    exact ⟨R, ρp.del l, hRY, noOwn_del hnoρp l,
      Or.inl ⟨w, rfl, hwand v'' y hy₁ χ (hPk v'' χ ⟨hχ, hw''⟩) R hy₂⟩⟩
  · -- a stop: the borrow is in the continuation's share; fold it there
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hPA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨-, hq, hwc⟩ := hT.entry m i en hTe
    have hρa := hT.pa m i en hTe _ _ _ _ hPA
    obtain ⟨Z, hZ, haZ⟩ := (ResU.CompS.assoc ρa ρk ρp X).mpr ⟨ρ', hcak, h9⟩
    rcases ResU.CompS.get_split_of_ne_imm haZ hXl hkm'' with ⟨hg, -⟩ | ⟨-, hZl⟩
    · exfalso
      have hcon := hρa l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    have hZd := ResU.del_compS hZl
    obtain ⟨D, hD, hDm⟩ := (ResU.CompS.assoc ρa (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) X).mp ⟨Z, hZd, haZ⟩
    obtain rfl : D = X.del l := compS_single_cancel hkm'' hDm hsplit
    obtain ⟨ρkL, hkL, haY⟩ := (ResU.CompS.assoc ρa (Z.del l) W'' Y).mpr ⟨_, hD, hY⟩
    have hdZd : (Z.del l).InStratum (↓A) :=
      ResU.CompS.inStratum_left hZd (ResU.CompS.inStratum_right haZ hdX)
    have hfold : CellFold l A F k ls' ρkL := by
      obtain ⟨hχ', hFk⟩ := hPk v'' χ ⟨hχ, hw''⟩
      obtain ⟨ac, hac, hacl⟩ := compS_exch hW'' (ResU.CompS.comm hkL)
      exact ⟨v'', χ, hχ', hFk, Z.del l, ac, ResU.CompS.comm hacl, hac⟩
    refine ⟨Y, PMap.empty, ResU.comp_empty_right _, noOwn_empty, Or.inr
      ⟨K, m, i, v₀, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρkL, haY, hPA, hfold,
        fun hu' => absurd (hq.symm.trans hu') (by simp), fun ls'' he =>
          ⟨fun k' hk' w σB XB hB hXB => ?_, fun hq' => absurd hq hq'⟩⟩⟩⟩
    simp only [erwpC, show k' < n by omega, if_true]
    -- the frame of the second segment: `Z/ℓ ● σ_B`
    obtain ⟨ρbB, hρbB, hWXB⟩ :=
      (ResU.CompS.assoc W'' (Z.del l) σB XB).mpr ⟨ρkL, ResU.CompS.comm hkL, hXB⟩
    have hdB : ρbB.InStratum (↓A) :=
      inStratum_compS hρbB hdZd (hT.pb m i en hTe _ _ _ _ hB)
    refine ih k' (by omega) k (le_of_lt hk') ls'' _ v'' χ W'' ρbB XB hχ hdB P'' hPk hw''
      (ResU.CompS.comm hW'') hWXB (fun BM' hBM' => ?_)
    -- the borrowed continuation, at the frame, with the garbage `ρ⁺` added
    have he' : en.wc ls' ls'' ρk := by
      rw [hwc] at he ⊢
      exact extF_fold hZ hZl (CellU.kind_mutOf _ _ _ _ _ _) (CellU.wit_mutOf _ _ _ _ _ _) hW'' hkL he
    obtain ⟨s1, hs1, hZds1⟩ := (ResU.CompS.assoc (Z.del l) σB
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) BM').mpr ⟨ρbB, hρbB, hBM'⟩
    obtain ⟨Z', hZ', hZ'σ⟩ := (ResU.CompS.assoc (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ P'' hw'')) σB BM').mp
        ⟨s1, ResU.CompS.comm hs1, hZds1⟩
    obtain rfl : Z = Z' := ResU.CompS.functional hZd hZ'
    obtain ⟨s2, hs2, hks2⟩ := (ResU.CompS.assoc ρk ρp σB BM').mpr ⟨Z, hZ, hZ'σ⟩
    obtain ⟨Xk, hXk, hXkp⟩ := (ResU.CompS.assoc ρk σB ρp BM').mp ⟨s2, ResU.CompS.comm hs2, hks2⟩
    have hc := (hcont ls'' he').1 k' hk' w σB Xk hB hXk
    simp only [erwpC, show k' < n by omega, if_true] at hc
    exact erwp_garbage hXkp hnoρp hc
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT.entry m i en hTe).1]; simp)

/-! ### Monotonicity, guards and frames -/

/-- **`erwp` is monotone in its postcondition and its table**, the table read below the index. -/
theorem erwp_mono {Φ : LocFam} {Tb Tb' : TableN} {Q Q' : PostN}
    (hQ : ∀ k ls v ρ, Q k ls v ρ → Q' k ls v ρ)
    (hT : ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      Tb k ls t Ψ ρ → Tb' k ls t Ψ' ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ Tb Q n ls e ρ → erwp (ℍ := ℍ) Φ Tb' Q' n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, hq⟩ | ht
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ hq⟩
  · refine Or.inr (hT k ls' t _ _ σ (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) _ _ _ hΨ

/-- A guard weakened. -/
theorem opTableG_mono {T : OpTabN} {G G' : ShareG} (hG : ∀ k ls ρ, G k ls ρ → G' k ls ρ) :
    ∀ k ls t (Ψ Ψ' : ContN) ρ, (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) →
      opTableG T G k ls t Ψ ρ → opTableG T G' k ls t Ψ' ρ := by
  intro k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h⟩ := opTableG_local T G k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨hp, ρa, ρk, hc, hA, hGk, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hG _ _ _ hGk, hcont⟩⟩

/-- A guard and a frame beside it. -/
def ShareG.sep (G : ShareG) (R : List SRec → WProp) : ShareG := fun k ls ρ =>
  ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ G k ls ρ₁ ∧ R ls ρ₂

/-- **The frame at `erwp` at a guarded table** (`[TR]` 6.146 across must-resume stops, as
`erwp_frameL`): the frame goes into each stop's continuation share beside the guarded part, and
is taken back at the resume. A guarded table has no `raise` stop, so the frame may own. -/
theorem erwpG_frame {Φ : LocFam} {T : OpTabN} (hT : T.AFOK) {G : ShareG} {Q : PostN}
    (R : List SRec → WProp)
    (hR : ∀ ls ls' ρ, extF ls ls' ρ → R ls ρ → R ls' ρ) :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → R ls ρ₂ →
      erwp (ℍ := ℍ) Φ (opTableG T G) Q n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (opTableG T (G.sep R)) (fun k ls' v => Q k ls' v ⋆ R ls') n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_)
    (rwpG_frame R (fun ls ls' hs ρ => hR ls ls' ρ (extF_of_same hs ρ)) hc h hR₂)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, rfl, σ₁, σ₂, hσ, hv, hσ₂⟩
  obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hA, hG, -, hcont⟩ := pure_sep_iff.mp hp
  obtain ⟨hql, hwc⟩ := hT m i en hTe ha
  obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
  refine Or.inr ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hTe, ha⟩ ⟨ρa, ρk₂, haσ, hA,
    ⟨ρk, σ₂, hk₂, hG, hσ₂⟩, fun hu' => absurd (hql.symm.trans hu') (by simp), fun ls'' he =>
      ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' => absurd hql hq'⟩⟩⟩
  have he' : en.wc ls' ls'' ρk := by rw [hwc] at he ⊢; exact extF_left _ _ _ _ _ hk₂ he
  have hls : extF ls' ls'' σ₂ := by rw [hwc] at he; exact extF_right hk₂ he
  obtain ⟨y, hy, hyτ⟩ := compS_exch hk₂ hcτ
  have hc' := (hcont ls'' he').1 k' hk' w τ₁ y hB hy
  simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
  exact ih k' (by omega) ls'' _ y σ₂ τ₂ hyτ (hR ls' ls'' σ₂ hls hσ₂) hc'

/-- **The final resource set aside as garbage at `erwp`** when it owns nothing (`rwpG_garbage`, at
every value the run returns). -/
theorem erwp_dump {Φ : LocFam} {Tb : TableN} (hL : Tb.Local) {Q : PostN} :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ Tb (fun k ls' v X => NoOwn X ∧ Q k ls' v PMap.empty) n ls e ρ →
      erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  rw [erwp_eq] at h ⊢
  refine rwpG_garbage (rwpG_mono_le (fun k hk ls' t X ht => ?_) h)
  rcases ht with ⟨v, hv, hno, hq⟩ | ht
  · exact ⟨PMap.empty, X, compS_empty_left X, hno, Or.inl ⟨v, hv, hq⟩⟩
  · refine ⟨X, PMap.empty, ResU.comp_empty_right X, noOwn_empty,
      Or.inr (hL k ls' t _ _ X (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)⟩
    simp only [erwpC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) _ _ _ hΨ

/-- `erwp_mono` with the postcondition and the table read at the indices up to `N`. -/
theorem erwp_mono_le {Φ : LocFam} {Tb Tb' : TableN} {Q Q' : PostN} (N : Nat)
    (hQ : ∀ k, k ≤ N → ∀ ls v ρ, Q k ls v ρ → Q' k ls v ρ)
    (hT : ∀ k, k ≤ N → ∀ ls t (Ψ Ψ' : ContN) ρ,
      (∀ k', k' < k → ∀ ls e ρ, Ψ k' ls e ρ → Ψ' k' ls e ρ) → Tb k ls t Ψ ρ → Tb' k ls t Ψ' ρ) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ Tb Q n ls e ρ → erwp (ℍ := ℍ) Φ Tb' Q' n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN ls e ρ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) h
  rcases ht with ⟨v, hv, hq⟩ | ht
  · exact Or.inl ⟨v, hv, hQ _ (by omega) _ _ _ hq⟩
  · refine Or.inr (hT k (by omega) ls' t _ _ σ (fun k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [erwpC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) (by omega) _ _ _ hΨ

/-! ### `[TR]` 6.174 (`withbor3`) across stops -/

/-- **`[TR]` 6.174's proof at `erwp`, across stops**: the Mut Anti-Frame at `ℓ ↦ mut(β, v, ρ_v, F_o j)`,
then the Mut Frame of the opened cell at `α` with the family `F_i`, the callback holding the
reborrow `ℓ ↦ mut(α, …)` across stops. At a stop the Mut Frame folds the cell back to `own` with
its content in `F_i k` (`erwp_M_frameF`), which is in `F_o k` (`hoi`): the anti-frame's guard.

`hstrα`, `hwi` and `hoi` are what the printed proof reads off the borrow in hand: Core's
`withbor3_compatX` takes `MutFrame`'s stratum from the `Mut` value (`hunif`), and both families
are `𝒱⟦T₁⟧δ`, so the content opened is in the inner family and the content handed back is in the
outer one. -/
theorem erwp_withbor3 {Φ : LocFam} (hΦ : Φ.Down) {l : Loc} {β : Life}
    {Fo : Nat → Val → SPropS Loc Val β} (hF : Φ l = some ⟨β, Fo⟩) {α : Life}
    {Fi : Nat → Val → SPropS Loc Val α} (hFi : DownFam α Fi) {T : OpTabN} (hTl : T.LendOK α)
    (hTa : T.AFOK)
    (hoi : ∀ k v χ (h : χ.InStratum α), Fi k v ⟨χ, h⟩ → ∃ h' : χ.InStratum β, Fo k v ⟨χ, h'⟩)
    {Q : PostN} (n : Nat) (ls : List SRec) (e : Expr) (v : Val) (σP : WRes)
    (hstr : σP.InStratum β) (j : Nat) (hjn : n ≤ j) (hwit : Fo j v ⟨σP, hstr⟩)
    (hstrα : σP.InStratum α) (hwi : Fi j v ⟨σP, hstrα⟩) (ρa ρ : WRes)
    (hρa : ρa.InStratum (↓α))
    (hsplit : ResU.CompS (ResU.single l (CellU.mutOf β v σP hstr (Fo j) hwit)) ρa ρ)
    (hA : ∀ BM, ResU.CompS ρa (ResU.single l (CellU.mutOf α v σP hstrα (Fi j) hwi)) BM →
      erwp (ℍ := ℍ) (Φ.set l α Fi) (opTableN T) (MFPost l α Fi (AFPost l β Fo Q)) n ls e BM) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  refine erwp_M_antiFrame hΦ hF hTa n ls e v σP hstr j hwit ρa ρ hsplit fun W X hW hX => ?_
  refine erwp_mono (fun _ _ _ _ h => h) (opTableG_mono fun k ls' ρ' h => ?_) _ _ _ _
    (erwp_M_frameF hFi hTl n j hjn ls e v σP W ρa X hstrα hρa (Fi j) (fun _ _ h => h) hwi
      (ResU.CompS.comm hW) (ResU.CompS.comm hX) hA)
  obtain ⟨w, χ, h, hw, R, rest, h1, h2⟩ := h
  obtain ⟨h', hw'⟩ := hoi k w χ h hw
  exact ⟨w, χ, h', hw', R, rest, h1, h2⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end
