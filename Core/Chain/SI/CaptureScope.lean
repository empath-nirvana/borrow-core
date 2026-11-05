import Core.Chain.SI.Uncapture
import Core.Chain.SI.CaptureGen

/-!
# A lend scope across tasks: the Imm Frame left open at stops, ended after a join

**Not a transcription.** `[TR]` 6.64 is a lemma about a run that returns. This file carries it
across stops without folding: the lend is entered as 6.64 enters it (`capture_world`), every stop
of the borrowed run is a stop of the lender with the world as it is (the lent cell `imm`, its
record proper and owned by the stopped branch), and the lend is ended as 6.64 ends it, after the
body, in the segment resumed from a join (`uncapture_world`). The borrowed run's payloads may
hold the borrow: a spawned task carries it away.

## What the printed proof gives, and where

At the end of every segment of the borrowed run, the lender reads that segment's
post-configuration as 6.64's proof reads the run's at its end: `ρ_o ↭ ρ′` (the run's `↭` with
the lender's copy of the borrow beside it, 6.48), then **6.29** (`ρ′ = ρ′/ℓ ● ρᵢ`), the
stratification `@(ρ′/ℓ) ⊐ α` (`six29_borrows_offN`), and **6.38** at `ρ′ := ρ′/ℓ`, `ρ⁺ := ρᵢ`
(`ρ′/ℓ # ℓ ↦ own(v)`). At a stop that is carried to the resume as the scope's invariant
(`ScopeInv`): the next segment starts from `Y ● ρᵢ` with `@Y ⊐ α` and `Y # ℓ ↦ own(v)`, which is
6.64's entry condition (`ρ_b` in `Res_α`, `ρ_b # ρ_ℓ`). At the last segment it gives
`uncapture_world` its hypotheses. 6.39 is not used: `↭` is not asked across a lend left open.

## What is new

* **The body ends at a join.** The scope's term is `e; join(ℓ)`. The lend can end only when no
  other computation holds a borrow of `ℓ`; that is a fact about every other stored continuation,
  which only the resumer knows. The join's entry asks it of the resumer's frame (`joinFd`: the
  frame's flattening holds nothing at `ℓ`) and answers with the borrows of `ℓ` the joined tasks
  held (`joinPBv`). The resumed segment is the scope's last, so the frame condition is read where
  the lend ends.
* **The lender keeps a copy of the borrow** (6.116, `ρᵢ = ρᵢ ● ρᵢ`) beside every segment of the
  borrowed run, so 6.29 finds the borrow at the end of the segment whatever the run did with its
  own copies, and the next segment starts from `Y ● ρᵢ`.
* **No fold at a stop.** The share keeps `ℓ ↦ imm(α, v, ∅)` and the record; nothing about the
  payload is asked (`ILendOK`'s `PA ∈ Res_α` is gone).

Restrictions: the lent cell's payload is empty (`ρ_P = ∅`), the borrowed run's operations are
must-resume with empty answers, and the run is at `erwp0` (no garbage: what it holds at a stop is
in the payload or the share).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)
open BoCa.Lifetime (LSub)

/-! ### Flattenings -/

/-- The flattening of one `imm` cell with an empty witness holds only that location. -/
theorem flat_single_imm_empty {m : Loc} {s : LSet} {u : Val}
    {h : ResU.InStratum s.join (PMap.empty : WRes)} {τ : WRes}
    (hτ : ResU.Flat (ResU.single m (CellU.immOf s u PMap.empty h)) τ) :
    ∀ x, x ≠ m → τ.get x = none := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  have he0 : e = PMap.empty := ExS.functional he (ExW.empty_of_all_imm (fun x ψ hx => by
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hx; exact CellU.kind_immOf _ _ _ _))
  obtain ⟨ev, av, p, hev, hav, hp, hpa⟩ := AgW.single_imm_inv ha
  obtain rfl : ev = PMap.empty := ExR.functional hev exW_empty
  obtain rfl : av = PMap.empty := AgW.functional hav agW_empty
  obtain rfl : p = PMap.empty := ResU.CompR.functional hp (ResU.comp_empty_right _)
  obtain rfl : a = ResU.single m (CellU.immOf s u PMap.empty h) :=
    ResU.CompR.functional hpa (ResU.comp_empty_right _)
  subst he0
  obtain rfl := eq_of_compS_empty_left hc
  intro x hx
  exact ResU.single_get_ne _ hx

/-- The flattening of the empty resource is empty. -/
theorem flat_empty_eq {τ : WRes} (hτ : ResU.Flat (PMap.empty : WRes) τ) : τ = PMap.empty := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  obtain rfl : e = PMap.empty := ExS.functional he exW_empty
  obtain rfl : a = PMap.empty := AgW.functional ha agW_empty
  exact (eq_of_compS_empty_left hc).trans rfl

/-- **A resource whose flattening holds nothing at `m` is compatible with `m ↦ own(u)`.** -/
theorem hash_own_of_flatFree {ρ : WRes} {m : Loc} (hv : ResU.Valid ρ)
    (hfree : ∀ τ, ResU.Flat ρ τ → τ.get m = none) (u : Val) :
    ResU.Hash ρ (ResU.single m (CellU.ownOf u)) := by
  obtain ⟨τ, hτ⟩ := hv
  have hm := hfree τ hτ
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single m (CellU.ownOf u))).mpr
    (compatS_single_of_get_none (get_eq_none_of_flat hτ hm))
  obtain ⟨τ', hτ'⟩ := (ResU.compS_defined_iff τ (ResU.single m (CellU.ownOf u))).mpr
    (compatS_single_of_get_none hm)
  exact ⟨hx.1, x, hx, τ', (flat_compS_own hx).mpr ⟨τ, hτ, hτ'⟩⟩

/-! ### The scope's objects -/

theorem inStratumE (A : Life) : ResU.InStratum A (PMap.empty : WRes) :=
  fun _ _ h => by rw [PMap.empty_get] at h; cases h

/-- The borrow: `ℓ ↦ imm({α}, v, ∅)`. -/
def viewA (l : Loc) (v : Val) (A : Life) : WRes :=
  ResU.single l (CellU.immOf (LSet.singleton A) v PMap.empty (inStratumE A))

/-- The lend's record. -/
def recP (l : Loc) (v : Val) (T : VTy) (δ : LSub) : FrameRec := ⟨l, v, PMap.empty, T, δ⟩

/-- `join(ℓ)`. -/
def joinE (nJ iJ : UInt32) (l : Loc) : Expr := performE (.val (opPayload nJ iJ (Val.loc l)))

/-- The scope's continuation after the body: `[·]; join(ℓ)`. -/
def seqK (nJ iJ : UInt32) (l : Loc) : Kont := .seq .hole (joinE nJ iJ l)

/-- **The join's frame condition**: the flattening of the resumer's frame holds nothing at the
location the join names. No other computation holds a borrow of it, at any depth. -/
def joinFd : Val → WRes → Prop := fun v ρf =>
  ∃ m, v = Val.loc m ∧ ∀ τ, ResU.Flat ρf τ → τ.get m = none

/-- **The join's answer**: `()`, with the borrows of the named location the joined tasks held —
none, or one `imm` cell there with an empty witness. -/
def joinPBv : Val → Nat → List SRec → Val → WProp := fun v _ _ w σ =>
  ∃ m, v = Val.loc m ∧ w = Val.unit ∧ (σ = PMap.empty ∨
    ∃ (s : LSet) (u : Val) (h : ResU.InStratum s.join (PMap.empty : WRes)),
      σ = ResU.single m (CellU.immOf s u PMap.empty h))

/-- The join's entry: must-resume, a location as payload, owning nothing. -/
def joinEnt : OpEntC :=
  { q := .lin, abort := false, PA := fun _ _ v ρ => (∃ m, v = Val.loc m) ∧ ρ = PMap.empty,
    PB := fun _ _ _ _ => False, fin := none, wc := fun _ _ _ => True,
    fd := joinFd, PBv := joinPBv, oc := fun _ => True }

/-- What the lender carries from one segment to the next. -/
def ScopeInv (l : Loc) (v : Val) (A : Life) (ρo : WRes) : Prop :=
  ∃ Y, ResU.CompS Y (viewA l v A) ρo ∧ Y.InStratum A ∧
    ResU.Hash Y (ResU.single l (CellU.ownOf v))

/-! ### The cell at the lent location -/

/-- A part of `imm({α}, v, ∅)` has only `α` in its lifetimes. -/
theorem imm_part_mem {ψ₁ ψ₂ : CellU Loc Val} {A : Life} {v : Val}
    {h : ResU.InStratum (LSet.singleton A).join (PMap.empty : WRes)}
    (hc : CellU.CompS ψ₁ ψ₂ (CellU.immOf (LSet.singleton A) v PMap.empty h)) :
    ∃ (s : LSet) (h₂ : ResU.InStratum s.join (PMap.empty : WRes)),
      ψ₂ = CellU.immOf s v PMap.empty h₂ ∧ ∀ x, s.mem x → x = A := by
  obtain ⟨s₁, s₂, v', ρ, h₁, h₂, h₃, rfl, rfl, e⟩ := hc
  obtain ⟨es, ev, eρ⟩ := CellU.immOf_inj e
  subst ev eρ
  refine ⟨s₂, h₂, rfl, fun x hx => ?_⟩
  have hm : (s₁ ∪ s₂).mem x := Or.inr hx
  rw [← es] at hm
  exact hm

/-- **The share keeps the borrow at its top level.** The whole holds `imm({α}, v, ∅)` at `ℓ`; a
part that composes with the borrow holds that cell at `ℓ` too. -/
theorem share_cell {ρa ρs ρ' ρk : WRes} {l : Loc} {v : Val} {A : Life}
    (h1 : ResU.CompS ρa ρs ρ') (h2 : ResU.CompS ρk (viewA l v A) ρs)
    (h3 : ρ'.get l = some (CellU.immOf (LSet.singleton A) v PMap.empty (inStratumE A))) :
    ρs.get l = some (CellU.immOf (LSet.singleton A) v PMap.empty (inStratumE A)) := by
  set cA := CellU.immOf (LSet.singleton A) v PMap.empty (inStratumE A) with hcA
  -- the share's cell at `ℓ` has `α` among its lifetimes
  have hsh : ∃ (s : LSet) (h : ResU.InStratum s.join (PMap.empty : WRes)),
      ρs.get l = some (CellU.immOf s v PMap.empty h) ∧ s.mem A := by
    rcases ResU.Comp.get h2 l with ⟨-, e₂, -⟩ | ⟨ψ, -, e₂, -⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, -, e₂, e, hc⟩
    · rw [viewA, ResU.single_get_self] at e₂; cases e₂
    · rw [viewA, ResU.single_get_self] at e₂; cases e₂
    · rw [viewA, ResU.single_get_self] at e₂
      cases Option.some.inj e₂
      exact ⟨_, _, e, rfl⟩
    · rw [viewA, ResU.single_get_self] at e₂
      cases Option.some.inj e₂
      obtain ⟨s₁, s₂, v', ρ, k₁, k₂, k₃, rfl, e₂', rfl⟩ := hc
      obtain ⟨es, ev, eρ⟩ := CellU.immOf_inj e₂'
      subst ev eρ
      exact ⟨_, _, e, Or.inr (es ▸ rfl)⟩
  obtain ⟨s, hs, es, hA⟩ := hsh
  -- and only `α`
  have hall : ∀ x, s.mem x → x = A := by
    rcases ResU.Comp.get h1 l with ⟨-, e₂, -⟩ | ⟨ψ, -, e₂, -⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, -, e₂, e, hc⟩
    · rw [es] at e₂; cases e₂
    · rw [es] at e₂; cases e₂
    · rw [es] at e₂; rw [h3] at e
      cases Option.some.inj e₂
      obtain ⟨-, -, -⟩ := CellU.immOf_inj (Option.some.inj e)
      intro x hx
      have := (CellU.immOf_inj (Option.some.inj e)).1
      rw [← this] at hx
      exact hx
    · rw [es] at e₂; rw [h3] at e
      cases Option.some.inj e₂
      cases Option.some.inj e
      obtain ⟨s', h', e', hs'⟩ := imm_part_mem hc
      obtain ⟨es', -, -⟩ := CellU.immOf_inj e'
      subst es'
      exact hs'
  rw [es]
  congr 1
  exact CellU.immOf_congr (lset_eq_singleton hA hall) rfl rfl _ _

/-! ### The scope -/

/-- The scope's tables: the borrowed run's operations are must-resume, with empty answers, their
world condition passing to a part of the share (`OpTabN.Down.wcl`), and the lender's table has
them lifted and the join at `(n_J, i_J)`. -/
structure ScopeTabs (Tin : OpTabN) (Tout : OpTabC) (nJ iJ : UInt32) : Prop where
  inner : ∀ m i en, Tin m i = some en → en.abort = false ∧ en.q = .lin ∧
    (∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → en.wc ls ls' ρ → en.wc ls ls' ρ₁) ∧
    (∀ k ls w σ, en.PB k ls w σ → σ = PMap.empty) ∧ Tout m i = some (liftEnt en)
  join : Tout nJ iJ = some joinEnt

theorem viewA_del (l : Loc) (v : Val) (A : Life) : (viewA l v A).del l = PMap.empty := by
  refine PMap.ext fun m => ?_
  by_cases hml : m = l
  · subst hml; rw [ResU.del_get_self]; rfl
  · rw [ResU.del_get_ne _ hml, viewA, ResU.single_get_ne _ hml]; rfl

/-- **The scope, from inside**: the lend already open, its record owned, the lender holding the
borrow beside the borrowed run (`ρ_o = ρ_in ● ρᵢ`, `ScopeInv`). By induction on the index: each
segment of the body ends at a stop of the lender, the share keeping the borrow and the record,
or at the body's value, then the join; the join's resume ends the lend. -/
theorem cerwp_scopeK {Φ : LocFam} (l : Loc) (v : Val) (T : VTy) (δ : LSub)
    (A : Life) (nJ iJ : UInt32) {Tin : OpTabN} {Tout : OpTabC} (hToutD : Tout.Down)
    (hTabs : ScopeTabs Tin Tout nJ iJ) {Q₀ : PostN} {Qout : PostCV} (hQout : Qout.Down)
    (hQ₀u : ∀ k ls (w : Val) ρ, Q₀ k ls w ρ → w = Val.unit)
    (O : List FrameRec)
    (hpost : ∀ k k₀ ls₀ ls' O' (w₀ : Val) π ρout, k ≤ k₀ → Q₀ k₀ ls₀ w₀ π →
      (∀ q, q ∈ O' ↔ q ∈ O ∧ q ≠ recP l v T δ) →
      ResU.CompS (π.del l) (ResU.single l (CellU.ownOf v)) ρout → Qout k ls' O' Val.unit ρout) :
    ∀ n (F : WRes → Prop) ls e (ρin ρo : WRes), recP l v T δ ∈ O →
      ResU.CompS ρin (viewA l v A) ρo → ScopeInv l v A ρo →
      erwp0 (ℍ := ℍ) Φ (opTableN Tin) Q₀ n ls e ρin →
      cerwp (ℍ := ℍ) (opTableC Tout) Qout F n ls O ((seqK nJ iJ l).plug e) ρo := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F ls e ρin ρo hpO hcin hinv h
  obtain ⟨Y, hY, hYA, hYo⟩ := hinv
  have hLout := opTableC_local Tout
  have hDout := opTableC_down hToutD
  set ρi : WRes := viewA l v A with hρi
  set p : FrameRec := recP l v T δ with hp
  rw [cerwp_eq]
  refine crwpG_bind (seqK nJ iJ l) ?_
  refine crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_)
    (crwpG_of_rwpG0_frame (F := F) (O := O) (erwp0_unfold_at (opTableN_local Tin) le_rfl h) hcin)
  obtain ⟨hOO, hls', π, hπ, hπc, hupd⟩ := ht
  subst O'
  -- 6.29 and 6.38 at the segment's end, the lender's copy beside the run
  have hW : ResU.CompS (PMap.empty : WRes) (ResU.single l (CellU.ownOf v))
      (ResU.single l (CellU.ownOf v)) := compS_empty_left _
  have hGc : ResU.CompS (ρ'.del l) ρi ρ' := six29N hYA hW hYo hY hupd
  obtain ⟨σπ, hσπ⟩ := hupd.2.2
  have hoff := (six29_borrows_offN hYA hW hYo hY hupd hσπ).2
  have hπdA : (ρ'.del l).InStratum A := by
    intro m ψ hm
    by_cases hml : m = l
    · subst hml; rw [ResU.del_get_self] at hm; exact absurd hm (by simp)
    · rw [ResU.del_get_ne _ hml] at hm
      exact ResU.flat_inStratum_inv_at hσπ (fun φ hφ => hoff m hml φ hφ) hm
  obtain ⟨G₀, hG₀, hGW⟩ := six38N (ρ' := ρ'.del l) (ρp := ρi) hW hYo
    ⟨hGc.1, ρ', hGc, ⟨σπ, hσπ⟩⟩ hYA hπdA (noOwn_single_imm l _ _ _ _) hY hGc hupd
  rw [viewA_del] at hG₀
  obtain rfl : ρ'.del l = G₀ := ResU.CompS.functional (ResU.comp_empty_right _) hG₀
  have hρ'l : ρ'.get l =
      some (CellU.immOf (LSet.singleton A) v PMap.empty (inStratumE A)) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  rcases hπ with ⟨w₀, rfl, hq₀⟩ | ⟨K₁, m, i, v₀, en, hpp⟩ | ⟨K₁, m, i, v₀, en, hpp⟩
  · -- the body returned: `(); join(ℓ)` steps to the join, a stop
    obtain rfl := hQ₀u _ _ _ _ hq₀
    refine cerwp_unfold_at hLout hk ?_
    refine cerwp_det hDout hQout (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    refine cerwp_perform (T := Tout) (F := F) .hole (m := nJ) (i := iJ) (v := Val.loc l)
      (en := joinEnt) (by simp [Kont.HasHnd]) hTabs.join rfl trivial (compS_empty_left ρ')
      ⟨⟨l, rfl⟩, rfl⟩ (fun h => by simp [joinEnt] at h)
      (fun ls_r _ k' hk' w σB X hB hX => ?_) (fun _ _ hq => absurd rfl hq)
    -- the join's resume: the lend ends
    obtain ⟨m', hm', rfl, hσB⟩ := hB
    obtain rfl : l = m' := by
      have := congrArg Subtype.val hm'
      simpa [Val.loc, Expr.val, Val.prim] using this
    set S : WRes := ρ'.del l with hS
    -- the resource is `S ● ℓ ↦ imm(s, v, ∅)`
    obtain ⟨s, hs, hres⟩ : ∃ (s : LSet) (hs : ResU.InStratum s.join (PMap.empty : WRes)),
        ResU.CompS S (ResU.single l (CellU.immOf s v PMap.empty hs)) X := by
      rcases hσB with rfl | ⟨s', u, h', rfl⟩
      · obtain rfl := ResU.CompS.functional hX (ResU.comp_empty_right _)
        exact ⟨_, _, hGc⟩
      · -- the joined tasks' borrow: the same cell, so the same value
        have hcomp := hX.1 l _ _ hρ'l (ResU.single_get_self _ _)
        obtain ⟨s₁, s₂, v', ρ₀, h₁, h₂, e₁, e₂⟩ := hcomp
        obtain ⟨-, hv₁, -⟩ := CellU.immOf_inj e₁
        obtain ⟨-, hu₂, -⟩ := CellU.immOf_inj e₂
        rw [show u = v from hu₂.trans hv₁.symm] at hX
        have h₃ : ResU.InStratum ((LSet.singleton A) ∪ s').join (PMap.empty : WRes) :=
          inStratumE _
        have hcell := ResU.compS_single_imm l (LSet.singleton A) s' v PMap.empty
          (inStratumE A) h' h₃
        obtain ⟨x, hx, hXx⟩ := (ResU.CompS.assoc S ρi
          (ResU.single l (CellU.immOf s' v PMap.empty h')) X).mpr ⟨ρ', hGc, hX⟩
        obtain rfl := ResU.CompS.functional hx hcell
        exact ⟨_, _, hXx⟩
    -- the lender's resource after the end, the list and the records
    obtain ⟨lsF, hlsF⟩ : ∃ lsF : List SRec, ∀ x, x ∈ lsF ↔ x ∈ ls_r ∧ x.1 ≠ p :=
      ⟨ls_r.filter (fun x => decide (x.1 ≠ p)), fun x => by simp⟩
    obtain ⟨OF, hOF⟩ : ∃ OF : List FrameRec, ∀ q, q ∈ OF ↔ q ∈ O ∧ q ≠ p :=
      ⟨O.filter (fun q => decide (q ≠ p)), fun q => by simp⟩
    obtain ⟨ρout, hρout⟩ := (ResU.compS_defined_iff S (ResU.single l (CellU.ownOf v))).mpr
      hGW.1
    have hSπ : S = π.del l := by
      have h := ResU.CompS.del hπc l
      rw [viewA_del] at h
      exact ResU.CompS.functional h (ResU.comp_empty_right _)
    rw [cerwp_eq]
    refine crwpG_update (ρ₁ := ρout) (O₁ := OF) (ls₁ := lsF) (fun ρf fρ ps psF μ hFf hf hcf hSp
      hT htg hlow => ?_) (crwpG_here (fun μ => final_val μ Val.unit)
        (Or.inl ⟨Val.unit, rfl, hpost k' k ls' lsF OF Val.unit π ρout (by omega) hq₀ hOF
          (hSπ ▸ hρout)⟩))
    obtain ⟨-, m'', hm'', hfree⟩ := hFf
    obtain rfl : l = m'' := by
      have := congrArg Subtype.val hm''
      simpa [Val.loc, Expr.val, Val.prim] using this
    have hpps : p ∈ ps := (hSp.1 p).mpr (Or.inl hpO)
    obtain ⟨ρres', W', ps', hρres', hfres', hcW', hps', hT', htg', hlow'⟩ :=
      uncapture_world (T := T) (δ := δ) hpps hres hcf hT htg hlow
        (hash_own_of_flatFree (hash_valid hf).1 hfree v) hGW lsF hlsF
    obtain rfl := ResU.CompS.functional hρres' hρout
    refine ⟨W', ps', hfres', hcW', ⟨fun q => ?_, fun q hq hqF => hSp.2 q ((hOF q).mp hq).1 hqF⟩,
      hT', htg', hlow'⟩
    rw [hps' q, hSp.1 q, hOF q]
    have hne : ∀ q, q ∈ psF → q ≠ p := fun q hq e => hSp.2 p hpO (e ▸ hq)
    constructor
    · rintro ⟨h₁ | h₁, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr h₁
    · rintro (⟨h₁, h₂⟩ | h₁)
      · exact ⟨Or.inl h₁, h₂⟩
      · exact ⟨Or.inr h₁, hne q h₁⟩
  · -- a stop of the body: the lender's stop, the share keeping the borrow and the record
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, -, hcont⟩ := pure_sep_iff.mp hpp
    obtain ⟨-, hq, hwc, hPB, hTo⟩ := hTabs.inner m i en hT
    obtain ⟨ρs, hks, has⟩ := compS_reassoc hcak hπc
    have hK : ((seqK nJ iJ l).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp]; simp [seqK, Kont.HasHnd, hK₁]
    rw [← Kont.plug_comp]
    refine crwpG_here (final_opPlug (r := false) (payloadName_opPayload m i v₀) hK) (Or.inr
      ⟨(seqK nJ iJ l).comp K₁, m, i, v₀, liftEnt en, pure_sep_mk ⟨rfl, hK, hTo, ha, trivial⟩
        ⟨ρa, ρs, has, hA, fun hu => absurd hu (by simp [liftEnt, hq]), fun ls_r he =>
          ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_, fun hq' => absurd hq hq'⟩⟩⟩)
    have hσ₁ : σ₁ = PMap.empty := hPB _ _ _ _ hB
    subst hσ₁
    have hσ₂ : σ₂ = ρs := ResU.CompS.functional hcσ (ResU.comp_empty_right _)
    subst σ₂
    simp only [cerwpC, show k' < n by omega, if_true]
    rw [Kont.plug_comp]
    have he' : en.wc ls' ls_r ρk := hwc _ _ _ _ _ hks he
    have hc := (hcont ls_r he').1 k' hk' w PMap.empty ρk hB (ResU.comp_empty_right _)
    simp only [erwp0C, show k' < n by omega, if_true] at hc
    have hdel := ResU.CompS.del has l
    refine ih k' (by omega) _ ls_r (K₁.plug (.val w)) ρk ρs hpO hks
      ⟨ρs.del l, ResU.del_compS (share_cell has hks hρ'l),
        ResU.CompS.inStratum_right hdel hπdA, (ResU.Hash.split hdel hGW).2⟩ hc
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hpp
    exact absurd ha (by rw [(hTabs.inner m i en hT).1]; simp)

/-- **The lend scope** (`[TR]` 6.64 across stops, ended after a join). `ℓ ↦ own(v) ⋆ ρ_b`, the
payload empty, `ρ_b` in `Res_α`, lent `imm` at `α` to a body in `erwp0` from `ρ_b ● ρᵢ` at
`frameList p ds α ls`: the scope `e; join(ℓ)` is in `cerwp`. The entry is 6.64's
(`capture_world`), the record joining the records the scope owns; then `cerwp_scopeK` with the
lender's copy of the borrow beside the body (6.116). -/
theorem cerwp_scope {Φ : LocFam} (l : Loc) (v : Val) (T : VTy) (δ : LSub) (hadm : AdmWf T δ)
    (hshape : vShape T δ v PMap.empty) (A : Life) (nJ iJ : UInt32) {Tin : OpTabN}
    {Tout : OpTabC} (hToutD : Tout.Down) (hTabs : ScopeTabs Tin Tout nJ iJ) {Q₀ : PostN}
    {Qout : PostCV} (hQout : Qout.Down) (hQ₀u : ∀ k ls (w : Val) ρ, Q₀ k ls w ρ → w = Val.unit)
    (O : List FrameRec)
    (hpost : ∀ k k₀ ls₀ ls' O' (w₀ : Val) π ρout, k ≤ k₀ → Q₀ k₀ ls₀ w₀ π →
      (∀ q, q ∈ O' ↔ q ∈ recP l v T δ :: O ∧ q ≠ recP l v T δ) →
      ResU.CompS (π.del l) (ResU.single l (CellU.ownOf v)) ρout → Qout k ls' O' Val.unit ρout)
    (n : Nat) (F : WRes → Prop) (ls : List SRec) (e : Expr) (ρb ρ : WRes)
    (houtb : ρb.InStratum A) (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v)) ρb ρ)
    (hvρ : ResU.Valid ρ) (ds : List FrameRec) (hds : ∀ d, d ∈ ds ↔ Desc (recP l v T δ) d)
    (h : ∀ BI, ResU.CompS ρb (viewA l v A) BI →
      erwp0 (ℍ := ℍ) Φ (opTableN Tin) Q₀ n (frameList (recP l v T δ) ds A ls) e BI) :
    cerwp (ℍ := ℍ) (opTableC Tout) Qout F n ls O ((seqK nJ iJ l).plug e) ρ := by
  have hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) (PMap.empty : WRes)
      (ResU.single l (CellU.ownOf v)) := ResU.comp_empty_right _
  have hbo : ResU.Hash ρb (ResU.single l (CellU.ownOf v)) :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hbi : ResU.Hash ρb (viewA l v A) := ResU.six34 (compS_empty_left _) hbo
  obtain ⟨BI, hBI⟩ := (ResU.compS_defined_iff ρb (viewA l v A)).mpr hbi.1
  -- the lender's copy: `ρ_b ● ρᵢ ● ρᵢ = ρ_b ● ρᵢ` (6.116)
  have hdup : ResU.CompS BI (viewA l v A) BI := by
    obtain ⟨y, hy, hyB⟩ := (ResU.CompS.assoc ρb (viewA l v A) (viewA l v A) BI).mp
      ⟨viewA l v A, compS_imm_dup l _ v PMap.empty (inStratumE A), hBI⟩
    rwa [ResU.CompS.functional hy hBI] at hyB
  rw [cerwp_eq]
  refine crwpG_update (ρ₁ := BI) (O₁ := recP l v T δ :: O)
    (ls₁ := frameList (recP l v T δ) ds A ls)
    (fun ρf fρ ps psF μ _ hf hc hS hT htg hlow => ?_) ?_
  · obtain ⟨BI', fρ', hBI', hfB, hcB, hS', hT', htg', hlow'⟩ :=
      capture_world l T δ hadm v (inStratumE A) hclP hcρ hshape hds hf hc hS hT htg hlow
    have e : BI' = BI := ResU.CompS.functional hBI' hBI
    subst e
    exact ⟨fρ', _, hfB, hcB, hS', hT', htg', hlow'⟩
  · rw [← cerwp_eq]
    exact cerwp_scopeK l v T δ A nJ iJ hToutD hTabs hQout hQ₀u _ hpost n F _ e BI BI
      List.mem_cons_self hdup ⟨ρb, hBI, houtb, hbo⟩ (h BI hBI)


end BoCa.Fig16.LogRel.Core.Chain.SI

end
