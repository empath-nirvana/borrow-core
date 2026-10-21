import Core.FrameRules
import Core.EffDefs

/-!
# Core — the effectful `wp`  `[spec §19]`

`wpG` is `wpTS` with its run ending at an arbitrary term `t` and the postcondition over that
term (`SPEC.md` §19, *Semantics*). A postcondition that admits only values gives `wpTS`
(`wpTS_iff_wpG`); one that also admits a stopped operation gives the final configurations of an
effectful computation.

**The frames at `wpG`.** `[TR]` Theorems 6.64, 6.65 and 6.66 hold at `wpG` by the proofs of
`Core/FrameRules.lean`, which never inspect the term the run ends at (`wpG_I_frameX`,
`wpG_M_frameX`, `wpG_M_antiFrameX`). So a frame ends at a stopped operation exactly as at a
return. That is the LIFO frame lemma an unwinding operation needs (§19, *Theorems* 3).

**`ewpTS`.** `ewpTS ls e Π Q` is the least fixed point over `wpG` of "answer in `Q`, or stop at
a term the protocol table `Π` admits, owing `Π`'s continuations". `Π` is abstract here: a
relation between a stopped term and the continuations it owes. §19's concrete tables, over
`perform`/`raise`, are stage 3's. The stage-2 facts:

* `ewp_unfold`/`ewp_fold`/`ewp_ind`: the fixed point, at a monotone table;
* `ewp_bot`: at the empty table `ewpTS = wpTS`;
* `ewp_of_wp`: a pure computation is effectful at every table;
* `ewp_mono`: monotone in the table and the postcondition;
* `ewp_abortive`: at an abortive table (no continuation owed) `ewpTS` is `wpG` once;
* `ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU`: the three frames over `ewpTS` at an
  abortive table, the LIFO frame lemmas of §19.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Alloc ARun Step1N)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `wpTS` is `wpG` at a postcondition over values. -/
theorem wpTS_iff_wpG (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) (ρ : WRes) :
    wpTS ls e Q ρ ↔ wpG ls e (valPost Q) ρ := by
  constructor
  · intro h ρf fρ ps h1 h2 h3 h4 A k
    obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h2 h3 h4 A k
    exact ⟨ρ', ρp, fρ', fρ'p, π, .val v, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, a12, a13, a14, v, rfl, a15⟩
  · intro h ρf fρ ps h1 h2 h3 h4 A k
    obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, a12, a13, a14, v, rfl, a15⟩ := h ρf fρ ps h1 h2 h3 h4 A k
    exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, a12, a13, a14, a15⟩

/-- `wpG` is monotone in its postcondition. -/
theorem wpG_mono {ls : List SRec} {e : Expr} {Q Q' : List SRec → Expr → WProp}
    (hQ : ∀ ls t ρ, Q ls t ρ → Q' ls t ρ) {ρ : WRes} (h : wpG ls e Q ρ) : wpG ls e Q' ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h2 h3 h4 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, hQ _ _ _ a15⟩

/-- **Garbage at the end of a run.** A part of the final resource with no `own` cell may be left
behind, joining the run's leftover `ρ⁺`.  This is what an unwind does to the continuation it
abandons (`SPEC.md` §19). -/
theorem wpG_garbage {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} {ρ : WRes}
    (h : wpG ls e (fun ls' t ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧ NoOwn ρ₂ ∧ Q ls' t ρ₁) ρ) :
    wpG ls e Q ρ := by
  intro ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', g1, g2, g3, g5, g6, g7, g8, g9, gA, gB,
    gT, gtg, gps, gls, ρ₁, ρ₂, hc, hno, hQ⟩ := h ρf fρ ps h1 h2 h3 h4 A k
  obtain ⟨hf₁, -⟩ := ResU.Hash.split hc g1
  obtain ⟨F, hF, hF₂⟩ := (ResU.CompS.assoc ρf ρ₁ ρ₂ fρ').mp ⟨ρ', hc, g2⟩
  obtain ⟨Z, hZ, hFZ⟩ := (ResU.CompS.assoc F ρ₂ ρp fρ'p).mpr ⟨fρ', hF₂, g6⟩
  obtain ⟨Z', hZ', h₁Z⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρp π).mpr ⟨ρ', hc, g9⟩
  cases ResU.CompS.functional hZ' hZ
  have hv : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := g7; exact ⟨σ, hσ⟩
  refine ⟨ρ₁, Z, F, fρ'p, π, t, μ, μ', ps', ls', hf₁, hF,
    ⟨(ResU.CompS.comm hFZ).1, fρ'p, ResU.CompS.comm hFZ, hv⟩, g5, hFZ, g7, g8, h₁Z, gA,
    noOwn_compS hZ hno gB, gT, gtg, gps, gls, hQ⟩

/-! ### The `imm` lend's cell, list and end, at a given lifetime  `[spec §48]` -/

/-- A record's lineage as a list, chosen once: the lists of its proper sub-records are equal up to
the order of their members, and a lend that ends at a stop and lends again uses this one.  -/
def lineageOf (r : FrameRec) : List FrameRec :=
  open Classical in
  if h : ∃ ds : List FrameRec, ∀ d, d ∈ ds ↔ Desc r d then h.choose else []

theorem lineageOf_spec {r : FrameRec} (h : ∃ ds : List FrameRec, ∀ d, d ∈ ds ↔ Desc r d) :
    ∀ d, d ∈ lineageOf r ↔ Desc r d := by
  classical
  unfold lineageOf; rw [dif_pos h]; exact h.choose_spec

/-- A single cell that is not `own` carries no `own` cell. -/
theorem noOwn_single_mut (l : BoCa.Loc) (ψ : CellU BoCa.Loc BoCa.Val) (hk : ψ.kind ≠ Kind.own) :
    NoOwn (ResU.single l ψ) := by
  refine noOwn_iff.mpr fun m φ hm => ?_
  by_cases hml : m = l
  · subst hml
    rw [ResU.single_get_self] at hm
    cases Option.some.inj hm
    exact hk
  · rw [ResU.single_get_ne _ hml] at hm; exact absurd hm (by simp)


/-- Off `ℓ`, a part of a resource is in a stratum where the whole is. -/
theorem del_inStratum_left {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {α : Life} {l : BoCa.Loc}
    (hρ : (ρ.del l).InStratum α) : (ρ₁.del l).InStratum α := by
  intro m ψ e
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rw [ResU.del_get_ne _ hm] at e
    exact ResU.CompS.inStratum_left_at h
      (fun φ hφ => hρ m φ (by rw [ResU.del_get_ne _ hm]; exact hφ)) e


/-- The cell an `imm` lend of `ℓ` at `A` holds: `ℓ ↦ imm({A}, v, ρ_P)`. -/
def immCell (l : BoCa.Loc) (A : Life) (v : Val) (ρP : WRes) (h : ρP.InStratum A) : WRes :=
  ResU.single l (CellU.immOf (LSet.singleton A) v ρP h)

/-- The lists an `imm` lend of the record `p` at `A` runs its callback at, from the caller's
`ls`: `ls` with `p` and its lineage at `A`, up to the order of the records. -/
def ImmList (p : FrameRec) (A : Life) (ls ls' : List SRec) : Prop :=
  ∀ x, x ∈ ls' ↔ (x = (p, A) ∨ (∃ d, Desc p d ∧ x = (d, A)) ∨ x ∈ ls)

theorem immList_frameList {p : FrameRec} {ds : List FrameRec} {A : Life} {ls : List SRec}
    (hds : ∀ d, d ∈ ds ↔ Desc p d) : ImmList p A ls (frameList p ds A ls) := by
  intro x
  simp only [frameList, List.mem_cons, List.mem_append, List.mem_map]
  constructor
  · rintro (rfl | ⟨d, hd, rfl⟩ | hx)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨d, (hds d).mp hd, rfl⟩)
    · exact Or.inr (Or.inr hx)
  · rintro (rfl | ⟨d, hd, rfl⟩ | hx)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨d, (hds d).mpr hd, rfl⟩)
    · exact Or.inr (Or.inr hx)

/-- `ImmList` is read up to the members of both lists. -/
theorem ImmList.same {p : FrameRec} {A : Life} {ls ls' ls₂ ls₂' : List SRec}
    (h : ImmList p A ls ls') (h₁ : ∀ x, x ∈ ls₂ ↔ x ∈ ls) (h₂ : ∀ x, x ∈ ls₂' ↔ x ∈ ls') :
    ImmList p A ls₂ ls₂' := fun x => (h₂ x).trans ((h x).trans (by rw [h₁ x]))

theorem ImmList.addAt {p : FrameRec} {A : Life} {ls ls' : List SRec} (h : ImmList p A ls ls') :
    AddAt ls ls' A := by
  refine ⟨fun x hx => (h x).mpr (Or.inr (Or.inr hx)), fun x hx hn => ?_⟩
  rcases (h x).mp hx with rfl | ⟨d, -, rfl⟩ | h'
  · rfl
  · rfl
  · exact absurd h' hn

theorem ImmList.record {p : FrameRec} {A : Life} {ls ls' : List SRec} (h : ImmList p A ls ls') :
    ∃ r ∈ rsOf ls', r.le = p.le ∧ r.T = p.T ∧ r.δ = p.δ :=
  ⟨p, mem_rsOf.mpr ⟨A, (h _).mpr (Or.inl rfl)⟩, rfl, rfl, rfl⟩

/-- An `imm` cell of `A` beside a resource puts it outside `Res_A`. -/
theorem immCell_not_inStratum {l : BoCa.Loc} {A : Life} {v : Val} {ρP ρ₁ ρ' : WRes}
    {h : ρP.InStratum A} (hc : ResU.CompS ρ₁ (immCell l A v ρP h) ρ') (hs : ρ'.InStratum A) :
    False := by
  have key : ∀ (s : LSet) (w : Val) (χ : WRes) (hχ : χ.InStratum s.join),
      (CellU.immOf s w χ hχ).InStratum A → s.mem A → False := fun s w χ hχ hin hmem =>
    absurd (s.meet_least A hmem) (not_le_of_gt ((CellU.inStratum_immOf A s w χ hχ).mp hin))
  have hn : (immCell l A v ρP h).get l = some (CellU.immOf (LSet.singleton A) v ρP h) :=
    ResU.single_get_self _ _
  rcases ResU.Comp.get hc l with ⟨-, f₂, -⟩ | ⟨ψ, -, f₂, -⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, -, f₂, f, hcomp⟩
  · rw [hn] at f₂; cases f₂
  · rw [hn] at f₂; cases f₂
  · rw [hn] at f₂; cases f₂
    exact key _ _ _ _ (hs l _ f) rfl
  · rw [hn] at f₂; cases f₂
    obtain ⟨s₁, s₂, w, ρw, hh₁, hh₂, hh₃, rfl, he₂, rfl⟩ := hcomp
    obtain ⟨hs₂, -, -⟩ := CellU.immOf_inj he₂
    exact key _ _ _ _ (hs l _ f) (Or.inr (by rw [← hs₂]; rfl))

/-- A singleton is the only lifetime set inside it. -/
theorem LSet.eq_singleton_of_mem {s : LSet} {A : Life} (h : ∀ x, s.mem x → x = A) :
    s = LSet.singleton A := by
  have hj : s.join = A := h _ s.join_mem
  have hm : s.meet = A := h _ s.meet_mem
  have hmem : s.mem = fun x => x = A := by
    funext x
    exact propext ⟨h x, fun e => by subst e; rw [← hj]; exact s.join_mem⟩
  cases s with
  | mk mem join meet join_mem meet_mem jg ml =>
    simp only at hj hm hmem
    subst hj hm hmem
    rfl

/-- **6.27's stratum with the `imm` cell set aside**: if `ρ ∈ Res_A` and
`ρ ● ℓ ↦ imm({A}, v, ρ_v) ↭ ρ′`, then `ρ′/ℓ ∈ Res_A` (6.50 at one location). -/
theorem six27I {l : BoCa.Loc} {A : Life} {v : Val} {ρ ρv M ρ' : WRes} {h : ρv.InStratum A}
    (hout : ρ.InStratum A) (hM : ResU.CompS ρ (immCell l A v ρv h) M) (hu : ResU.UpdV M ρ') :
    (ρ'.del l).InStratum A := by
  intro m ψ e
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rw [ResU.del_get_ne _ hm] at e
    have hdM : M.InStratum (↓A) :=
      BoLo.inStratum_comp (BoLo.compS_hC (↓A)) hM
        (fun m ψ e => CellU.InStratum.mono (le_of_lt (Life.down_sqsubset A)) (hout m ψ e))
        (ResU.inStratum_single l ((CellU.inStratum_immOf (↓A) _ v ρv h).mpr
          (Life.down_sqsubset A)))
    have hoff : M.get m = ρ.get m := by
      have hn : (immCell l A v ρv h).get m = none := ResU.single_get_ne _ hm
      rcases ResU.Comp.get hM m with ⟨f₁, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, -⟩ |
          ⟨χ₁, χ₂, χ, -, f₂, -, -⟩
      · rw [f, f₁]
      · rw [f, f₁]
      · rw [hn] at f₂; cases f₂
      · rw [hn] at f₂; cases f₂
    exact ResU.updV_outlives_at hdM hu (fun φ hφ => hout m φ (by rw [← hoff]; exact hφ)) e

/-- **The end of an `imm` lend's run**, the cell the share holds set aside with the leftover: at
the end of a run from `ρ_b ● ℓ ↦ imm({A}, v, ρ_P)`, `ρ_b ∈ Res_A`, the share is `ρ₁` beside the
cell, or `ρ₁` itself where it has left the cell behind, and `ρ₁ ∈ Res_A`.  6.29 keeps the cell
whole in the world, and a part of `ℓ ↦ imm({A}, …)` at `ℓ` is that cell. -/
theorem wpG_immEnd {l : BoCa.Loc} {A : Life} {v : Val} {ρP ρb ρlP BI : WRes}
    {houtP : ρP.InStratum A} (houtb : ρb.InStratum A)
    (hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP) (hH12 : ResU.Hash ρb ρlP)
    (hBI : ResU.CompS ρb (immCell l A v ρP houtP) BI) {ls : List SRec} {e : Expr}
    {Y : List SRec → Expr → WProp} (h : wpG ls e Y BI) :
    wpG ls e (fun ls' t ρ₁ => ∃ ρ', Y ls' t ρ' ∧ ρ₁.InStratum A ∧
      ((ρ'.get l = none ∧ ρ₁ = ρ') ∨ ResU.CompS ρ₁ (immCell l A v ρP houtP) ρ')) BI := by
  refine wpG_garbage ?_
  intro ρf fρ ps h1 h2 h3 h4 Al k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, a15⟩ := h ρf fρ ps h1 h2 h3 h4 Al k
  refine ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
    a11, a12, a13, a14, ?_⟩
  have hπ := ResU.six29 houtb hlPcell hH12 hBI a9
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hπ) (ResU.del_get_self _ _)
  have hstr : (π.del l).InStratum A := six27I houtb hBI a9
  have h₁str : (ρ'.del l).InStratum A := del_inStratum_left a8 hstr
  cases hg : ρ'.get l with
  | none =>
      have hd : ρ'.del l = ρ' := by
        apply PMap.ext; intro m
        by_cases hm : m = l
        · subst hm; rw [ResU.del_get_self, hg]
        · rw [ResU.del_get_ne _ hm]
      exact ⟨ρ', PMap.empty, ResU.comp_empty_right ρ', noOwn_empty, ρ', a15, hd ▸ h₁str,
        Or.inl ⟨hg, rfl⟩⟩
  | some c =>
      -- the share's cell at `ℓ` is a part of `ℓ ↦ imm({A}, …)`, so it is that cell
      have hc : c = CellU.immOf (LSet.singleton A) v ρP houtP := by
        rcases ResU.Comp.get a8 l with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
            ⟨ψ₁, ψ₂, ψ, f₁, -, f, hcomp⟩
        · rw [hg] at f₁; cases f₁
        · rw [hg] at f₁; cases f₁; rw [hπl] at f; exact (Option.some.inj f).symm
        · rw [hg] at f₁; cases f₁
        · rw [hg] at f₁; cases f₁
          rw [hπl] at f; cases f
          obtain ⟨s₁, s₂, w, ρw, hh₁, hh₂, hh₃, rfl, rfl, he⟩ := hcomp
          obtain ⟨hs, hw, hρw⟩ := CellU.immOf_inj he
          have hs₁ : s₁ = LSet.singleton A := LSet.eq_singleton_of_mem fun x hx => by
            have : (s₁ ∪ s₂).mem x := Or.inl hx
            rw [← hs] at this; exact this
          subst hs₁ hw hρw
          rfl
      subst hc
      have hdc := ResU.del_compS hg
      exact ⟨ρ'.del l, ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP), hdc,
        noOwn_single_mut _ _ (fun c => Kind.noConfusion c), ρ', a15,
        h₁str, Or.inr hdc⟩

/-! ### Theorem 6.64 (Imm Frame) at the typed world; record in `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` -/
/-- What the end of an `imm` lend hands its frame: the callback's post `Y` at its share `ρ′` and
the list `ls″` it ended at, which has the frame's records (`ImmList`); the share less the cell,
`ρ₁`, which is `ρ′` where the share has left the cell behind; and the frame's resource
`R = ρ₁ ● ℓ ↦ own(v) ● ρ_P`, at which `ls″` steps back to the caller's list.  `[spec §48]` -/
def ExitPostI (l : BoCa.Loc) (T : VTy) (δ : LSub) (A : Life) (v : Val) (ρP : WRes)
    (houtP : ρP.InStratum A) (ρlP : WRes) (ls : List SRec) (Y : List SRec → Expr → WProp) :
    List SRec → Expr → WProp := fun lsE t R =>
  ∃ (ls'' : List SRec) (ρ' ρ₁ : WRes), Y ls'' t ρ' ∧ ImmList ⟨l, v, ρP, T, δ⟩ A ls ls'' ∧
    ((ρ'.get l = none ∧ ρ₁ = ρ') ∨ ResU.CompS ρ₁ (immCell l A v ρP houtP) ρ') ∧
    ResU.CompS ρ₁ ρlP R ∧ Ext ls'' lsE R

/-- **`[TR]` Theorem 6.64 (`Imm Frame`) at `wpG`, at a given lifetime.**  The printed proof with
H4's lifetime `A` given (`houtP`, `houtb`, `hAtag` are what H4 establishes), the callback run at
every list with the frame's records from the cell the entry builds, the cell its share holds at
the end set aside with the leftover, and the end reporting the callback's post (`ExitPostI`).  The
printed lemma is `wpG_I_frameX`, at the lifetime H4 chooses.  `[spec §19, §48]` -/
theorem wpG_I_frameAt (l : BoCa.Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (e : Expr) (ls : List SRec) (A : Life) (ρP ρb ρlP ρ : WRes) (hPv : vC true T ls δ v ρP)
    (houtP : ρP.InStratum A) (houtb : ρb.InStratum A) (hAtag : ∀ x ∈ ls, x.2 ⊐ A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (Y : List SRec → Expr → WProp)
    (hcb : ∀ BI, ResU.CompS ρb (immCell l A v ρP houtP) BI →
      wpG (frameList ⟨l, v, ρP, T, δ⟩ (lineageOf ⟨l, v, ρP, T, δ⟩) A ls) e Y BI) :
    wpG ls e (ExitPostI l T δ A v ρP houtP ρlP ls Y) ρ := by
  classical
  intro ρf sρ ps hH3 hsρ hT htg alc kc
  have hTI := hT.inv
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  have houtlP : ResU.InStratum A ρlP :=
    BoLo.inStratum_comp (BoLo.compS_hC A) hclP (ResU.inStratum_single_own A l v) houtP
  -- the "fictional" `ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`, well formed by H10
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  -- H12-H17: the compatibility block
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρi := ResU.six34 hlPcell hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρi := ResU.six34 hlPcell (ResU.hash_symm hlPf)
  obtain ⟨BI, hBI⟩ := (ResU.compS_defined_iff ρb ρi).mpr hH13.1
  have hH17 : ResU.Hash ρf BI :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBI
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  -- the worlds at the two ends of the frame step
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb ρi fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- the record and its lineage
  set p : FrameRec := ⟨l, v, ρP, T, δ⟩ with hpdef
  have hshape : vShape T δ v ρP := vC_vShape true T hPv
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvsρ
  obtain ⟨eR, heR, -, -⟩ := frame_ex hclP (ResU.CompS.comm hFBl) heW
  have hds : ∀ d, d ∈ lineageOf p ↔ Desc p d :=
    lineageOf_spec ⟨_, (lineage_list (r := p) hshape hadm heR).choose_spec⟩
  set ds := lineageOf p with hdsdef
  set ls' : List SRec := frameList p ds A ls with hls'def
  have hadd : AddAt ls ls' A := addAt_frameList p ds A ls
  -- entry: `TW.immFrame`, and the tags
  have hTin : TW fρ (p :: ps) (rsOf ls') := by
    rw [hls'def, rsOf_frameList]
    exact TW.immFrame T δ houtP hT hadm hclP (ResU.CompS.comm hFBl) hshape
      (ResU.CompS.comm hFBi) hvfρ hds
  obtain ⟨hFLnew, hFLold⟩ :=
    frameLife_frame T δ hvsρ hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBi) hTI
  have htgin : Tagged fρ (p :: ps) ls' := by
    intro x hx
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at hx
    rcases hx with rfl | ⟨d, hd, rfl⟩ | hx
    · exact ⟨p, List.mem_cons_self, DescR.refl p, hFLnew⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨p, List.mem_cons_self, ⟨q, hqd⟩, hFLnew⟩
    · obtain ⟨q, hq, hqd, hfq⟩ := htg x hx
      exact ⟨q, List.mem_cons_of_mem _ hq, hqd, hFLold q hq x.2 hfq⟩
  -- H18: the callback, at the fictional borrow, at the list with the frame's records; the cell
  -- its share holds at its end is set aside with the leftover (`wpG_immEnd`)
  have hImm : ImmList p A ls ls' := immList_frameList hds
  have hwpBI := wpG_immEnd houtb hlPcell hH12 hBI (hcb BI hBI)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpBI ρf fρ (p :: ps) hH17 h4 hTin htgin alc kc
  -- H24 and H25: the share less the cell is in `Res_A`
  obtain ⟨ρ'₀, hY, houtρ', hcase⟩ := h12
  -- H27
  obtain ⟨hfρp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  -- H26: 6.29 with H11 and H12 and H21, then "by H24, `ℓ ∉ dom(ρ′)`"
  obtain ⟨hGsplit, hGiH, hGc⟩ :=
    ResU.six38_steps_one_two hlPcell hH12 hρ'p houtb houtρ' hBI h9 h10
  -- H28: 6.38 with H12 and H27 and H11 and H24 and H22 and H21
  obtain ⟨G₀, hG₀, hH28⟩ :=
    ResU.six38 hlPcell hH12 hρ'p houtb houtρ' h11 hBI h9 h10
  obtain rfl : π.del l = G₀ := ResU.CompS.functional hGsplit hG₀
  -- `ρ⁺ = ρ⁺/ℓ ● ρᵢ`
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame houtρ' h9 hπl
  have hppl : ρp.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    (ResU.Comp.get_of_left_none h9 hρ'l).symm.trans hπl
  have hpd : ResU.CompS (ρp.del l) ρi ρp := ResU.del_compS hppl
  -- H29-H33: the second compatibility block
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρp)
  obtain ⟨hPDρ', -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'lPh, hPDlP⟩ := ResU.Hash.split hGsplit hH28
  have hflP : ResU.Hash ρf ρlP := ResU.hash_symm hlPf
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ' ρlP).mpr hρ'lPh.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm h1) hρ'lPh hflP hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (ρp.del l) R :=
    ResU.hash_of_pairwise hPDρ' hρ'lPh hPDlP hR
  have hPDFR : ResU.Hash (ρp.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ :=
    (ResU.compS_defined_iff FR (ρp.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ :=
    (ResU.compS_defined_iff R (ρp.del l)).mpr (ResU.hash_symm hPDR).1
  -- H34: the two memories, by 6.26 under a frame (6.8)
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBI : ResU.Valid BI := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvi : ResU.Valid ρi := (ResU.Valid.split hBI hvBI).2
  have hFBiH : ResU.Hash FB ρi :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm
      (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFBi hFBiH hFBl hFBlH).mp h5
  -- and at the other end of the run
  obtain ⟨FP, hFP, hFPi⟩ :=
    (ResU.CompS.assoc fρ' (ρp.del l) ρi fρ'p).mp ⟨ρp, hpd, h6⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (ρp.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ' ρlP (ρp.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨D₁, hD₁, hDlP⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l) ρlP RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : π.del l = D₁ := ResU.CompS.functional hGsplit hD₁
  obtain ⟨FPD, hFPD, hFPDlP⟩ :=
    (ResU.CompS.assoc ρf (π.del l) ρlP FRP).mp ⟨RP, hDlP, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ' (ρp.del l) FP).mpr ⟨fρ', h2, hFP⟩
  obtain rfl : π.del l = FP₁ := ResU.CompS.functional hGsplit hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hFPiH : ResU.Hash FP ρi := ⟨hFPi.1, fρ'p, hFPi, hvfρ'p⟩
  have hFPlH : ResU.Hash FP ρlP := ⟨hFPDlP.1, FRP, hFPDlP, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFPi hFPiH hFPDlP hFPlH).mp h7
  -- H35: `ρ ↭ ρ′ ● ρ⁺/ℓ ● ρ_ℓ ● ρ_P̂(v)`, by 6.39 with H12 and H28 and H21
  obtain ⟨w₁, w₂, hw₁, hw₂, hupdw⟩ := ResU.six39 hclP hH12 hH28 hBI hGc h10
  obtain rfl : ρ = w₁ := ResU.CompS.functional (ResU.CompS.comm hcρ) hw₁
  obtain rfl : RP = w₂ := ResU.CompS.functional hDlP hw₂
  -- G6: `ρ⁺/ℓ` is still own-free
  have hno : BoLo.NoOwn (ρp.del l) := by
    refine PMap.ext fun x => ?_
    cases hgg : ((ρp.del l).restrict Kind.own).get x with
    | none => simp
    | some ψ =>
        exfalso
        obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
        by_cases hx : x = l
        · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
        · rw [ResU.del_get_ne _ hx] at hdd
          have hcc : (ρp.restrict Kind.own).get x = some ψ :=
            ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
          rw [h11] at hcc
          simp at hcc
  -- the inner run's list has the frame's records; `p` is one of its records proper
  have hls''add : AddAt ls ls'' A :=
    ⟨fun x hx => (hls'' x).mpr (hadd.1 x hx),
     fun x hx hn => hadd.2 x ((hls'' x).mp hx) hn⟩
  obtain ⟨aF, haF⟩ := agW_of_valid hvfρ'p
  -- the frame cell `ρᵢ` sits in the final inner world, with its witness `ρ_P̂(v)`
  have hρiF : ResU.Le ρi fρ'p := ⟨FP, ResU.CompS.comm hFPi⟩
  obtain ⟨ζl, tl, eζl, htl, hAl⟩ := ag_ls_of_le hρiF haF (ResU.single_get_self _ _)
    (CellU.lsOf_immOf _ _ _ _) (show (LSet.singleton A).mem A from rfl)
  have hpps : p ∉ ps := by
    intro hp
    obtain ⟨ψ, eψ, -⟩ := hTI.2.1 p hp aW haW
    have Wl : sρ.get l = some (CellU.ownOf v) :=
      (ResU.CompS.get_right_of_ne_imm hFBl (ResU.CompS.get_left_of_ne_imm hclP
        (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
    exact ex_ag_disjoint hvsρ heW haW (ExS.get_of_ne_imm heW Wl (by simp)) eψ
  have hp'' : p ∈ ps'' := (hps'' p).mpr List.mem_cons_self
  obtain ⟨α', hα'⟩ := hT''.linLife p hp''
  have hαA : A = α' := frameLife_eq hα' haF eζl htl hAl
  subst hαA
  -- the frame's resource steps back to the caller's list (`ext_drop`): `R` holds no view at
  -- `p`'s lineage
  have hRα : R.InStratum A := (outlives_comp hR A).mpr ⟨houtρ', houtlP⟩
  have hicpR : ∀ m, ICpAt aF R m := by
    intro m
    have hρ' : ICpAt aF ρ' m :=
      icpAt_trans (icpAt_right (ResU.CompS.toCompR h2) m)
        (icpAt_trans (icpAt_left (ResU.CompS.toCompR h6) m) (icpAt_agW haF m))
    obtain ⟨ψl, eψl, kψl, wψl, rψl⟩ := compS_get_right' hFPi (ResU.single_get_self _ _)
    obtain ⟨sl, hsl, hψl⟩ := CellU.imm_eta (kψl.trans (CellU.kind_immOf _ _ _ _))
    rw [hψl] at eψl
    obtain ⟨e₀, a₀, -, ha₀, icp₀⟩ := escrow_icp haF eψl
    have hwl : ψl.wit = ρP := wψl.trans (CellU.wit_immOf _ _ _ _)
    rw [hwl] at ha₀
    have hρP : ICpAt aF ρP m := icpAt_trans (icpAt_agW ha₀ m) (icp₀ m)
    exact icpAt_comp (ResU.CompS.toCompR hR) hρ'
      (icpAt_comp (ResU.CompS.toCompR hclP)
        (icpAt_of_immFree (fun x ψ e => by
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; simp) m) hρP)
  have hRl : ∀ ψ : CellU Loc Val, R.get p.le = some ψ → ψ.kind ≠ Kind.imm := by
    intro ψ eψ
    obtain ⟨ψ₁, eψ₁, kψ₁, -⟩ := compS_get_right' hR
      ((ResU.CompS.get_left_of_ne_imm hclP (ResU.single_get_self _ _) (by simp)).2)
    rw [eψ] at eψ₁; cases Option.some.inj eψ₁
    rw [kψ₁]; simp
  have hkeep : ∀ r ∈ rsOf ls'', Rel r R → r ∈ rsOf ls := by
    intro r hr hrel
    obtain ⟨t, ht⟩ := mem_rsOf.mp hr
    have ht' := (hls'' _).mp ht
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at ht'
    rcases ht' with h | ⟨d, hd, h⟩ | h
    · cases h
      exact (not_rel_lineage hα' haF hicpR hRα hRl (DescR.refl p) hrel).elim
    · cases h
      obtain ⟨q, hq, hqd⟩ := (hds _).mp hd
      exact (not_rel_lineage hα' haF hicpR hRα hRl ⟨q, hqd⟩ hrel).elim
    · exact mem_rsOf.mpr ⟨t, h⟩
  have hQls : ExitPostI l T δ A v ρP houtP ρlP ls Y ls v' R :=
    ⟨ls'', ρ'₀, ρ', hY, ImmList.same hImm (fun _ => Iff.rfl) hls'', hcase, hR,
      ext_drop hls''add hRα hkeep⟩
  -- exit: `TW.immEnd` at `p`, back to the caller's records
  have hTout : TW FRP ps (rsOf ls) :=
    TW.immEnd p hT'' hp'' (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPDlP) hvFRP
      (fun r' => ⟨fun h => ⟨(hps'' r').mpr (List.mem_cons_of_mem _ h),
        fun e => hpps (e ▸ h)⟩, fun ⟨h, hne⟩ => by
          rcases List.mem_cons.mp ((hps'' r').mp h) with e | h'
          · exact absurd e hne
          · exact h'⟩)
      hTI.2.2.2.2.2.2.1
  obtain ⟨aOut, haOut⟩ := agW_of_valid hvFRP
  have backOut : ∀ a', AgW FRP a' → ∀ m, ICpAt aF a' m := by
    intro a' ha' m
    obtain ⟨aσ, aY, eR', aR, pR, heR', -, hpR, hcp, hσY, hRY⟩ :=
      end_walks (ResU.CompS.comm hFPi) hclP (ResU.CompS.comm hFPDlP) haF ha'
    exact icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
  have htgout : Tagged FRP ps ls := by
    intro x hx
    obtain ⟨q, hq, hqd, hfq⟩ := htg'' x ((hls'' x).mpr (hadd.1 x hx))
    have hqp : q ≠ p := by
      rintro rfl
      have := frameLife_eq hfq haF eζl htl hAl
      have hxA := hAtag x hx
      rw [← this] at hxA
      exact lt_irrefl _ hxA
    have hq' : q ∈ ps := by
      rcases List.mem_cons.mp ((hps'' q).mp hq) with e | h
      · exact absurd e hqp
      · exact h
    exact ⟨q, hq', hqd, frameLife_back hfq (fun a' ha' =>
      ⟨aF, haF, backOut a' ha' _, fun m _ => backOut a' ha' m⟩)⟩
  exact ⟨R, ρp.del l, FR, FRP, RP, v', μ, μ', ps, ls,
    ResU.hash_symm hfR, hFR, hPDFR, hmem₁, hFRP, hmem₂, h8, hRP,
    hupdw, hno, hTout, htgout, fun _ => Iff.rfl, fun _ => Iff.rfl, hQls⟩


/-- `[TR]` Theorem 6.64 (`Imm Frame`) at `wpG`, the run ending at any final term:

    ℓ ↦ v ⋆ 𝒱⟦T⟧(ls)δ(v) ⋆ (⋔α. ∀ ls′ ⊇_α ls. Imm α 𝒱⟦T⟧δ ─⋆ wp_{ls′}(e){[α] (ℓ ↦ v ─⋆
        𝒱⟦T⟧δ(v) ─⋆ Q̂)})  ⊨  wp_{ls}(e){Q̂}

`wpG_I_frameAt` at the lifetime H4 chooses; at the end the box puts the cell in the leftover.
`[variant: P̂ ≔ vC⟦T⟧δ, the record's type; `hadm` is `TW.immFrame`'s premise; `hQ` (`Q̂`
stable along `Ext`, which at the relation is `vC_local`) is added; the callee is also handed
the record its frame made]` -/
theorem wpG_I_frameX (l : BoCa.Loc) (T : VTy) (δ : LSub) (hadm : AdmWf T δ) (v : Val)
    (e : Expr) (ls : List SRec) (Q : List SRec → Expr → WProp)
    (hQ : ∀ ls₁ ls₂ (w : Expr) ρ, Ext ls₁ ls₂ ρ → Q ls₁ w ρ → Q ls₂ w ρ) :
    Entails
      (ptoOwn l v ⋆ vC true T ls δ v ⋆
        fresh (fun α ρ => ∀ ls', AddAt ls ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = T ∧ r.δ = δ) →
          (ptoImmS l α ls' (fun ls₀ => vC true T ls₀ δ) ─⋆
            wpG ls' e (fun ls'' v' => box α (ptoOwn l v ─⋆ (vC true T ls'' δ v ─⋆ Q ls'' v')))) ρ))
      (wpG ls e Q) := by
  intro ρ hH2
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ vC true T ls δ v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4, taken also below every tag of the list
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  set A : Life := b₀ ⊓ (↓γ) with hAdef
  have hAγ : A ⊏ γ := lt_of_le_of_lt inf_le_right (Life.down_sqsubset γ)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx => lt_of_le_of_lt inf_le_left (hb₀ x hx)
  obtain ⟨hbody, houtρ⟩ := hγ A hAγ
  -- 6.104 splits the box over the `⋆`
  obtain ⟨ρlP, ρb, hcρ, hlP, hwand⟩ := hbody
  obtain ⟨hlPv, houtlP⟩ := hlP
  obtain ⟨ρl, ρP, hclP, hpl, hPv⟩ := hlPv
  subst hpl
  have houtP : ResU.InStratum A ρP := ResU.CompS.inStratum_right hclP houtlP
  have houtb : ResU.InStratum A ρb := ResU.CompS.inStratum_right hcρ houtρ
  refine wpG_mono (Q := ExitPostI l T δ A v ρP houtP ρlP ls
      (fun ls'' v' => box A (ptoOwn l v ─⋆ (vC true T ls'' δ v ─⋆ Q ls'' v'))))
    (fun lsE t R hx => ?_) (wpG_I_frameAt l T δ hadm v e ls A ρP ρb ρlP ρ hPv houtP
      houtb hAtag hclP hcρ _ fun BI hBI => ?_)
  · obtain ⟨ls'', ρ', ρ₁, hY, hI'', hcase, hR, hext⟩ := hx
    rcases hcase with ⟨-, rfl⟩ | hc1
    · obtain ⟨X, hX, hXR⟩ :=
        (ResU.CompS.assoc ρ₁ (ResU.single l (CellU.ownOf v)) ρP R).mp ⟨ρlP, hclP, hR⟩
      have hPv'' : vC true T ls'' δ v ρP :=
        vC_local true T (ext_add hI''.addAt houtP) hPv
      exact hQ ls'' lsE t R hext ((hY.1 _ X rfl hX) ρP R hPv'' hXR)
    · -- the cell is not in `Res_A`, which the box asks of the share
      exact (immCell_not_inStratum hc1 hY.2).elim
  · -- the borrow handed to the body is at the caller's list (`⊐ α`)
    have hadd : AddAt ls (frameList ⟨l, v, ρP, T, δ⟩ (lineageOf ⟨l, v, ρP, T, δ⟩) A ls) A :=
      addAt_frameList _ _ _ _
    have hrec : ∃ r ∈ rsOf (frameList ⟨l, v, ρP, T, δ⟩ (lineageOf ⟨l, v, ρP, T, δ⟩) A ls),
        r.le = l ∧ r.T = T ∧ r.δ = δ :=
      ⟨_, by rw [rsOf_frameList]; exact List.mem_cons_self, rfl, rfl, rfl⟩
    have hcell : ptoImmS l A (frameList ⟨l, v, ρP, T, δ⟩ (lineageOf ⟨l, v, ρP, T, δ⟩) A ls)
        (fun ls₀ => vC true T ls₀ δ) (immCell l A v ρP houtP) := by
      refine ⟨LSet.singleton A, v, ρP, houtP, ls, rfl, hPv, le_refl _, fun x => ?_⟩
      refine ⟨fun hx => ⟨hadd.1 x hx, hAtag x hx⟩, fun ⟨hx, hxA⟩ => ?_⟩
      by_contra hn
      have := hadd.2 x hx hn
      rw [this] at hxA
      exact lt_irrefl _ hxA
    exact hwand _ hadd hrec _ BI hcell hBI

/-! ### Theorem 6.65 (Mut Frame) at the typed world; record in `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` -/

/-- The predicate a lend of `ℓ : Ref T` stores, at the list `ls` and lifetime `A`. -/
def QsAt (T : VTy) (δ : LSub) (ls : List SRec) (A : Life) : Val → SPropS BoCa.Loc BoCa.Val A :=
  fun w r => vC true T ls δ w r.1

/-- The cell a lend of `ℓ` at `A` holds: `ℓ ↦ mut(A, v, ρ_P, 𝒱⟦T⟧δ)`. -/
def viewCell (l : BoCa.Loc) (T : VTy) (δ : LSub) (ls : List SRec) (A : Life) (v : Val)
    (ρP : WRes) (h : ρP.InStratum A) (hw : vC true T ls δ v ρP) : WRes :=
  ResU.single l (CellU.mutOf A v ρP h (QsAt T δ ls A) hw)

/-- What the end of a lent run hands the frame: the callback's post `Y` at its share `ρ′`; the
value `v″` and payload `χ` the lend leaves in the cell; the share less the cell, `ρ₁`, which is
`ρ′` when the share no longer holds the cell; and the frame's resource `ρ₁ ● ℓ ↦ own(v″) ● χ`. -/
def ExitPost (l : BoCa.Loc) (T : VTy) (δ : LSub) (A : Life) (ls : List SRec)
    (Y : List SRec → Expr → WProp) : List SRec → Expr → WProp := fun ls'' t R =>
  ∃ (ρ' : WRes) (v'' : Val) (χ : WRes) (hχ : χ.InStratum A) (hw : QsAt T δ ls A v'' ⟨χ, hχ⟩)
    (ρ₁ y : WRes),
    Y ls'' t ρ' ∧ vC true T ls'' δ v'' χ ∧
    ((ρ'.get l = none ∧ ρ₁ = ρ') ∨
      ResU.CompS ρ₁ (ResU.single l (CellU.mutOf A v'' χ hχ (QsAt T δ ls A) hw)) ρ') ∧
    ResU.CompS ρ₁ (ResU.single l (CellU.ownOf v'')) y ∧ ResU.CompS y χ R

/-- **`[TR]` Theorem 6.65 (`Mut Frame`) at `wpG`, at a given lifetime.**  The printed proof with
H4's lifetime `A` given (`houtP`, `houtb` are what H4 establishes), the callback run from
the cell the entry builds, and the end reporting what the lend hands back (`ExitPost`): the value
and payload left in the cell, and whether the share at the end still held the cell, which then
joins the leftover.  The printed lemma is `wpG_M_frameX`, at the lifetime H4 chooses; a lend
held across a graded stop ends at the stop and lends again at `A` (`Core/EffLend.lean`).
`[spec §19, §48]` -/
theorem wpG_M_frameAt (l : BoCa.Loc) (T : VTy) (δ : LSub) (A : Life) (v : Val) (e : Expr)
    (ls : List SRec)
    (ρP ρb ρlP ρ : WRes) (hPv : vC true T ls δ v ρP) (houtP : ρP.InStratum A)
    (houtb : ρb.InStratum A)
    (hclP : ResU.CompS (ResU.single l (CellU.ownOf v)) ρP ρlP) (hcρ : ResU.CompS ρlP ρb ρ)
    (Y : List SRec → Expr → WProp)
    (hcb : ∀ BM, ResU.CompS ρb (viewCell l T δ ls A v ρP houtP hPv) BM → wpG ls e Y BM) :
    wpG ls e (ExitPost l T δ A ls Y) ρ := by
  classical
  intro ρf sρ ps hH3 hsρ hT htg alc kc
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  set Qs : Val → SPropS BoCa.Loc BoCa.Val A := QsAt T δ ls A with hQs
  have hwit : Qs v ⟨ρP, houtP⟩ := hPv
  set ρm : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.mutOf A v ρP houtP Qs hwit) with hρm
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- H12-H17: the compatibility block
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρm := (ResU.six24 hlPcell).mpr hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρm :=
    (ResU.six24 hlPcell).mpr (ResU.hash_symm hlPf)
  obtain ⟨BM, hBM⟩ := (ResU.compS_defined_iff ρb ρm).mpr hH13.1
  have hH17 : ResU.Hash ρf BM :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBM
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBm⟩ := (ResU.CompS.assoc ρf ρb ρm fρ).mp ⟨BM, hBM, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- entry: `TW.mutFold`
  have hTin : TW fρ ps (rsOf ls) :=
    TW.mutFold hT hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) a).mpr ha) htg
  -- H18: the wand, at the fictional borrow
  have hwpBM := hcb BM hBM
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpBM ρf fρ ps hH17 h4 hTin htgin alc kc
  -- H26: 6.27 -- the borrow is still at the top level of `ρ′ ● ρ⁺`
  obtain ⟨v'', χ, hχ, hwit'', hsplit''⟩ := ResU.six27 houtb hBM h10
  have hπl : π.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rw [ResU.Comp.get_of_left_none hsplit'' (ResU.del_get_self _ _)]
    exact ResU.single_get_self _ _
  have hkm'' : (CellU.mutOf A v'' χ hχ Qs hwit'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  -- the share keeps the view or has left it behind; either way it goes to the leftover
  obtain ⟨ρ₁, ρ₂, hc₁₂, hno₂, hρ₁l, hcase⟩ : ∃ ρ₁ ρ₂ : WRes, ResU.CompS ρ₁ ρ₂ ρ' ∧ NoOwn ρ₂ ∧
      ρ₁.get l = none ∧ ((ρ'.get l = none ∧ ρ₁ = ρ') ∨
        ResU.CompS ρ₁ (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) ρ') := by
    cases hg : ρ'.get l with
    | none => exact ⟨ρ', PMap.empty, ResU.CompS.comm (compS_empty_left ρ'), noOwn_empty, hg,
        Or.inl ⟨rfl, rfl⟩⟩
    | some c =>
        have hk : c.kind ≠ Kind.imm := by
          rcases ResU.CompS.get_split_of_ne_imm h9 hπl hkm'' with ⟨hg', -⟩ | ⟨hg', -⟩
          · rw [hg] at hg'; cases Option.some.inj hg'; exact hkm''
          · rw [hg] at hg'; cases hg'
        have hcπ := (ResU.CompS.get_left_of_ne_imm h9 hg hk).2
        rw [hπl] at hcπ
        cases Option.some.inj hcπ
        exact ⟨ρ'.del l, _, ResU.del_compS hg, noOwn_single_mut _ _ (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c), ResU.del_get_self _ _,
          Or.inr (ResU.del_compS hg)⟩
  -- the leftover with the view: `wpG_garbage`'s reassociation
  obtain ⟨hf₁, -⟩ := ResU.Hash.split hc₁₂ h1
  obtain ⟨F₁, hF₁, hF₁₂⟩ := (ResU.CompS.assoc ρf ρ₁ ρ₂ fρ').mp ⟨ρ', hc₁₂, h2⟩
  obtain ⟨Z, hZ, hFZ⟩ := (ResU.CompS.assoc F₁ ρ₂ ρp fρ'p).mpr ⟨fρ', hF₁₂, h6⟩
  obtain ⟨Z', hZ', h₁Z⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρp π).mpr ⟨ρ', hc₁₂, h9⟩
  cases ResU.CompS.functional hZ' hZ
  have hvf : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have h3' : ResU.Hash Z F₁ := ⟨(ResU.CompS.comm hFZ).1, fρ'p, ResU.CompS.comm hFZ, hvf⟩
  have h11' : NoOwn Z := noOwn_compS hZ hno₂ h11
  have hppl : Z.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rcases ResU.CompS.get_split_of_ne_imm h₁Z hπl hkm'' with ⟨hg, -⟩ | ⟨-, hp⟩
    · rw [hρ₁l] at hg; cases hg
    · exact hp
  have hpd : ResU.CompS (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) Z := ResU.del_compS hppl
  obtain ⟨RPD, hRPD, hRPDm⟩ :=
    (ResU.CompS.assoc ρ₁ (Z.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) π).mp ⟨Z, hpd, h₁Z⟩
  have hvπ : ResU.Valid π := h10.2.2
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    (ResU.Valid.split hRPDm hvπ).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  have hRPDmH : ResU.Hash RPD (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hRPDm.1, π, hRPDm, hvπ⟩
  have hH27 : ResU.Hash RPD W'' := (ResU.six24 hW'').mp hRPDmH
  obtain ⟨hfρ', hρ'p⟩ := ResU.Hash.split hF₁ (ResU.hash_symm h3')
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρ')
  obtain ⟨hρ'PD, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'W'', hPDW''⟩ := ResU.Hash.split hRPD hH27
  have hfm'' : ResU.Hash ρf W'' :=
    (ResU.six24 hW'').mp (ResU.hash_symm (ResU.Hash.split hpd (ResU.hash_symm hfρ')).2)
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ₁ W'').mpr hρ'W''.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm hf₁) hρ'W'' hfm'' hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (Z.del l) R :=
    ResU.hash_of_pairwise hρ'PD hρ'W'' hPDW'' hR
  have hPDFR : ResU.Hash (Z.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ := (ResU.compS_defined_iff FR (Z.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ := (ResU.compS_defined_iff R (Z.del l)).mpr (ResU.hash_symm hPDR).1
  -- H33: the two memories, by 6.25 under a frame (6.8)
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBM : ResU.Valid BM := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvmm : ResU.Valid ρm := (ResU.Valid.split hBM hvBM).2
  have hFBmH : ResU.Hash FB ρm :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_mut_own hlPcell hvmm hvlP hFBm hFBmH hFBl hFBlH).mp h5
  obtain ⟨FP, hFP, hFPm⟩ := (ResU.CompS.assoc F₁ (Z.del l)
    (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) fρ'p).mp ⟨Z, hpd, hFZ⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (Z.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ₁ W'' (Z.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨RPD₁, hRPD₁, hRPDW⟩ :=
    (ResU.CompS.assoc ρ₁ (Z.del l) W'' RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : RPD = RPD₁ := ResU.CompS.functional hRPD hRPD₁
  obtain ⟨FPD, hFPD, hFPDW⟩ :=
    (ResU.CompS.assoc ρf RPD W'' FRP).mp ⟨RP, hRPDW, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ₁ (Z.del l) FP).mpr ⟨F₁, hF₁, hFP⟩
  obtain rfl : RPD = FP₁ := ResU.CompS.functional hRPD hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hvW'' : ResU.Valid W'' := by
    obtain ⟨-, s, hs, hv⟩ := hH27; exact (ResU.Valid.split hs hv).2
  have hFPmH : ResU.Hash FP (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hFPm.1, fρ'p, hFPm, hvfρ'p⟩
  have hFPWH : ResU.Hash FP W'' := ⟨hFPDW.1, FRP, hFPDW, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFPm hFPmH hFPDW hFPWH).mp h7
  -- H34: `ρ ↭ ρ′ ● ρ''_v ● ℓ ↦ own(v'') ● ρ⁺/ℓ`, by 6.28
  have hvRP : ResU.Valid RP := by
    obtain ⟨-, s, hs, hv⟩ := hH27
    exact ResU.CompS.functional hs hRPDW ▸ hv
  have hupd : ResU.Upd ρ RP :=
    (ResU.six28 hlPcell hW'' hBM hRPDm (ResU.CompS.comm hcρ) hRPDW
      hvBM hvπ hvρ hvRP).mp h10.1
  have hno : BoLo.NoOwn (Z.del l) := by
    refine PMap.ext fun x => ?_
    cases hgg : ((Z.del l).restrict Kind.own).get x with
    | none => simp
    | some ψ =>
        exfalso
        obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
        by_cases hx : x = l
        · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
        · rw [ResU.del_get_ne _ hx] at hdd
          have hcc : (Z.restrict Kind.own).get x = some ψ :=
            ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
          rw [h11'] at hcc
          simp at hcc
  -- exit: `TW.mutUnfold`
  have hTout : TW FRP ps'' (rsOf ls'') :=
    TW.mutUnfold hT'' (ResU.CompS.comm hFPm) (ResU.CompS.comm hW'')
      (ResU.CompS.comm hFPDW) hvFRP
  have htgout : Tagged FRP ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW'') (ResU.CompS.comm hFPDW) (ResU.CompS.comm hFPm) a).mp
      ha) htg''
  -- H35: the callback's wand, at the value the run leaves in the cell, read at the list the
  -- run returns
  have hχv : vC true T ls'' δ v'' χ :=
    vC_local true T (ext_of_same hls'' χ) (show vC true T ls δ v'' χ from hwit'')
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc ρ₁ (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
  have hQ : ExitPost l T δ A ls Y ls'' v' R :=
    ⟨ρ', v'', χ, hχ, hwit'', ρ₁, y, h12, hχv, hcase, hy₁, hy₂⟩
  exact ⟨R, Z.del l, FR, FRP, RP, v', μ, μ', ps'', ls'',
    ResU.hash_symm hfR, hFR, hPDFR, hmem₁, hFRP, hmem₂, h8, hRP,
    ⟨hupd, hvρ, hvRP⟩, hno, hTout, htgout, hps'', hls'', hQ⟩

/-- `[TR]` Theorem 6.65 (`Mut Frame`) at `wpG`, the run ending at any final term: if `𝒱⟦T⟧δ ⊨ [β]𝒱⟦T⟧δ` at every
list, then

    ℓ ↦ v ⋆ 𝒱⟦T⟧(ls)δ(v) ⋆ (⋔α. Mut α 𝒱⟦T⟧δ ─⋆ wp_{ls}(e){[α] ∀v′. ℓ ↦ v′ ─⋆ 𝒱⟦T⟧δ(v′) ─⋆ Q̂})
      ⊨  wp_{ls}(e){Q̂}

`wpG_M_frameAt` at the lifetime H4 chooses; at the end the box puts the cell in the leftover.
`[variant: P̂ ≔ vC⟦T⟧δ; the premise `P̂ ⊨ [β]P̂` at every list, the family's reading]` -/
theorem wpG_M_frameX (l : BoCa.Loc) (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (v : Val) (e : Expr) (ls : List SRec)
    (Q : List SRec → Expr → WProp) :
    Entails
      (ptoOwn l v ⋆ vC true T ls δ v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆
          wpG ls e (fun ls'' v' =>
            box α (all fun w => ptoOwn l w ─⋆ (vC true T ls'' δ w ─⋆ Q ls'' v')))))
      (wpG ls e Q) := by
  intro ρ hH2
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ vC true T ls δ v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4: a lifetime shorter than `γ`, `β` and every tag
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  set A : Life := b₀ ⊓ (↓(γ ⊓ β)) with hAdef
  have hAγ : A ⊏ γ :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left)
  have hAβ : A ⊏ β :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx => lt_of_le_of_lt inf_le_left (hb₀ x hx)
  obtain ⟨hbody, houtρ⟩ := hγ A hAγ
  -- 6.104 splits the box over the `⋆`
  obtain ⟨ρlP, ρb, hcρ, hlP, hwand⟩ := hbody
  obtain ⟨hlPv, houtlP⟩ := hlP
  obtain ⟨ρl, ρP, hclP, hpl, hPv⟩ := hlPv
  subst hpl
  -- H10 and H11
  have houtP : ResU.InStratum A ρP := ResU.CompS.inStratum_right hclP houtlP
  have houtb : ResU.InStratum A ρb := ResU.CompS.inStratum_right hcρ houtρ
  have hunif : ∀ ls' w σ, vC true T ls' δ w σ → ResU.InStratum A σ := fun ls' w σ h m ψ hm =>
    CellU.InStratum.mono (le_of_lt hAβ) (hP ls' w σ h m ψ hm)
  have hofS : BoLo.ofS (QsAt T δ ls A) = fun w => vC true T ls δ w := by
    funext w σ
    exact propext ⟨fun h => h.2, fun h => ⟨hunif ls w σ h, h⟩⟩
  -- the "fictional" `ρ_m = ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`, well formed by H4
  obtain ⟨hwit, hcellm⟩ := ptoMutX_create (l := l) (α := A) (le_refl A) hofS hAtag
    hunif houtP hPv
  refine wpG_mono (fun ls'' t R hx => ?_) (wpG_M_frameAt l T δ A v e ls ρP ρb ρlP ρ hPv
    houtP houtb hclP hcρ _ fun BM hBM => hwand _ BM hcellm hBM)
  obtain ⟨ρ', v'', χ, hχ, hw, ρ₁, y, hY, hχv, hcase, hy₁, hy₂⟩ := hx
  rcases hcase with ⟨-, rfl⟩ | hc1
  · exact hY.1 v'' _ y rfl hy₁ χ R hχv hy₂
  · -- the cell is not in `Res_A`, which the box asks of the share
    exfalso
    have hg := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc1)
      (ResU.single_get_self _ _) (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)).2
    have := hY.2 l _ hg
    rw [CellU.inStratum_mutOf] at this
    exact lt_irrefl _ this

/-! ### Theorem 6.66 (Anti Frame) at the typed world; record in `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` -/
/-- `[TR]` Theorem 6.66 (`Anti Frame`) at `wpG`, the run ending at any final term:

    ℓ ↦ Mut α 𝒱⟦T⟧δ ⋆ (∀v. ℓ ↦ v ─⋆ 𝒱⟦T⟧(ls)δ(v) ─⋆
        wp_{ls}(e){∃v. ℓ ↦ v ⋆ 𝒱⟦T⟧δ(v) ⋆ (ℓ ↦ Mut α 𝒱⟦T⟧δ ─⋆ Q̂)})  ⊨  wp_{ls}(e){Q̂}

`[variant: P̂ ≔ vC⟦T⟧δ]` -/
theorem wpG_M_antiFrameX (l : BoCa.Loc) (α : Life) (T : VTy) (δ : LSub) (e : Expr)
    (ls : List SRec) (Q : List SRec → Expr → WProp) :
    Entails
      (ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ⋆
        (all fun v => ptoOwn l v ─⋆ (vC true T ls δ v ─⋆
          wpG ls e (fun ls'' v' => ex fun w =>
            ptoOwn l w ⋆ vC true T ls'' δ w ⋆
              (ptoMutS l α ls'' (fun ls₀ => vC true T ls₀ δ) ─⋆ Q ls'' v')))))
      (wpG ls e Q) := by
  classical
  intro ρ hH1 ρf sρ ps hH2 hsρ hT htg alc kc
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH2 hsρ
  obtain ⟨ρm, ρa, hsplit, hM, hA⟩ := hH1
  obtain ⟨β, v, σP, hstr, Qs, hwit, ls₀, hαβ, hρm, hofS, hls₀, hunif⟩ := hM
  subst hρm
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  obtain ⟨hvm, hva⟩ := ResU.Valid.split hsplit hvρ
  obtain ⟨W, hW⟩ := ResU.compS_own_of_valid_mut hvm
  have hmaH : ResU.Hash (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) ρa :=
    ⟨hsplit.1, ρ, hsplit, hvρ⟩
  have haW : ResU.Hash ρa W := (ResU.six24 hW).mp (ResU.hash_symm hmaH)
  have hvW : ResU.Valid W := by
    obtain ⟨-, s, hs, hv⟩ := haW; exact (ResU.Valid.split hs hv).2
  obtain ⟨hmf, haf⟩ := ResU.Hash.split hsplit (ResU.hash_symm hH2)
  have hfW : ResU.Hash ρf W := (ResU.six24 hW).mp (ResU.hash_symm hmf)
  obtain ⟨X, hX⟩ := (ResU.compS_defined_iff ρa W).mpr haW.1
  have hfX : ResU.Hash ρf X := ResU.hash_of_pairwise (ResU.hash_symm haf) haW hfW hX
  -- the content handed out, read at the current list
  have hPv : vC true T ls δ v σP := by
    have h₀ : vC true T ls₀ δ v σP := by
      have : BoLo.ofS Qs v σP := ⟨hstr, hwit⟩
      rw [hofS] at this; exact this
    exact vC_local true T (ext_stored_current hstr le_rfl hls₀) h₀
  obtain ⟨A₁, hA₁, hA₂⟩ :=
    (ResU.CompS.assoc ρa (ResU.single l (CellU.ownOf v)) σP X).mp
      ⟨W, ResU.CompS.comm hW, hX⟩
  have hwpX := (hA v _ A₁ rfl hA₁) σP X hPv hA₂
  obtain ⟨fρ, h4, hvfρ⟩ := hfX.2
  -- the frame `ρ_f ● ρ_a` the first memory is read over
  obtain ⟨FA, hFA⟩ := (ResU.compS_defined_iff ρf ρa).mpr (ResU.hash_symm haf).1
  obtain ⟨FA₁, hFA₁, hFAmc⟩ :=
    (ResU.CompS.assoc ρf ρa (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) sρ).mp
      ⟨ρ, ResU.CompS.comm hsplit, hsρ⟩
  obtain rfl : FA = FA₁ := ResU.CompS.functional hFA hFA₁
  obtain ⟨FA₂, hFA₂, hFAWc⟩ := (ResU.CompS.assoc ρf ρa W fρ).mp ⟨X, hX, h4⟩
  obtain rfl : FA = FA₂ := ResU.CompS.functional hFA hFA₂
  -- entry: `TW.mutUnfold`
  have hTin : TW fρ ps (rsOf ls) :=
    TW.mutUnfold hT (ResU.CompS.comm hFAmc) (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW) (ResU.CompS.comm hFAWc) (ResU.CompS.comm hFAmc) a).mp
      ha) htg
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpX ρf fρ ps hfX h4 hTin htgin alc kc
  obtain ⟨v'', ρl'', rest, hcr, hl'', hrest⟩ := h12
  subst hl''
  obtain ⟨ρPv'', ρb, hcr2, hPv'', hb⟩ := hrest
  -- the content handed back: in `Res_β` by `P̂ : Val → SProp_β`, and written into the
  -- unchanged stored predicate
  have hstr'' : ResU.InStratum β ρPv'' := hunif ls'' v'' ρPv'' hPv''
  obtain ⟨W'', hW''₁, hW''₂⟩ :=
    (ResU.CompS.assoc (ResU.single l (CellU.ownOf v'')) ρPv'' ρb ρ').mp ⟨rest, hcr2, hcr⟩
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hleP : ResU.Le ρPv'' fρ'p :=
    (le_of_compS_right hW''₁).trans ((le_of_compS_left hW''₂).trans
      ((le_of_compS_right h2).trans (le_of_compS_left h6)))
  have hlb : LifeBound ls'' ρPv'' β := lifeBound_of_tagged hvfρ'p htg'' hleP hstr''
  have hls₀'' : ∀ x, x ∈ ls₀ ↔ (x ∈ ls'' ∧ x.2 ⊐ β) := fun x => by
    rw [hls₀ x, hls'' x]
  obtain ⟨hwit'', hcell''⟩ := ptoMutX_write (l := l) (Q := Qs) hαβ hofS hls₀'' hunif hstr''
    hPv'' hlb
  have hW'' : ResU.CompS ρPv'' (ResU.single l (CellU.ownOf v'')) W'' :=
    ResU.CompS.comm hW''₁
  have hvρ' : ResU.Valid ρ' := by
    obtain ⟨-, s, hs, hv⟩ := h1; exact (ResU.Valid.split hs hv).1
  have hvW'' : ResU.Valid W'' := (ResU.Valid.split hW''₂ hvρ').1
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    ResU.valid_single_mut_of_wit hW'' hvW''
  -- H20-H23: the compatibility results for the borrowed resource after the run
  have hW''b : ResU.Hash W'' ρb := ⟨hW''₂.1, ρ', hW''₂, hvρ'⟩
  have hbm'' : ResU.Hash ρb (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''b)
  obtain ⟨RB, hRB⟩ := (ResU.compS_defined_iff ρb
    (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit''))).mpr hbm''.1
  obtain ⟨hfp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hW''p, hbp⟩ := ResU.Hash.split hW''₂ hρ'p
  obtain ⟨hW''f, hbf⟩ := ResU.Hash.split hW''₂ h1
  have hpm'' : ResU.Hash ρp (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    (ResU.six24 hW'').mpr (ResU.hash_symm hW''p)
  have hfm'' : ResU.Hash ρf (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
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
  have hFAm : ResU.Hash FA (ResU.single l (CellU.mutOf β v σP hstr Qs hwit)) :=
    ResU.hash_symm (ResU.hash_of_pairwise hmf (ResU.hash_symm haf) hmaH hFA)
  have hFAW : ResU.Hash FA W :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hfW) (ResU.hash_symm haf)
      (ResU.hash_symm haW) hFA)
  obtain ⟨FW, hFW, hFWb⟩ := (ResU.CompS.assoc ρf W'' ρb fρ').mp ⟨ρ', hW''₂, h2⟩
  obtain ⟨BP₁, hBP₁, hFWBP⟩ := (ResU.CompS.assoc FW ρb ρp fρ'p).mpr ⟨fρ', hFWb, h6⟩
  obtain rfl : BP = BP₁ := ResU.CompS.functional hBP hBP₁
  obtain ⟨WBP, hWBP, hfWBP⟩ := (ResU.CompS.assoc ρf W'' BP fρ'p).mpr ⟨FW, hFW, hFWBP⟩
  obtain ⟨FB, hFB, hFBW⟩ :=
    (ResU.CompS.assoc ρf BP W'' fρ'p).mp ⟨WBP, ResU.CompS.comm hWBP, hfWBP⟩
  obtain ⟨π'₁, hπ'₁, hfπ'⟩ := (ResU.CompS.assoc ρf RB ρp FRBp).mpr ⟨FRB, hFRB, hFRBp⟩
  obtain rfl : π' = π'₁ := ResU.CompS.functional hπ' hπ'₁
  obtain ⟨MP, hMP, hbMP⟩ := (ResU.CompS.assoc ρb (ResU.single l
    (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) ρp π').mpr ⟨RB, hRB, hπ'⟩
  obtain ⟨BP₂, hBP₂, hBPm⟩ := (ResU.CompS.assoc ρb ρp
    (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) π').mp
      ⟨MP, ResU.CompS.comm hMP, hbMP⟩
  obtain rfl : BP = BP₂ := ResU.CompS.functional hBP hBP₂
  obtain ⟨FB₁, hFB₁, hFBm⟩ :=
    (ResU.CompS.assoc ρf BP (ResU.single l
      (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) FRBp).mp ⟨π', hBPm, hfπ'⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  have hfBP : ResU.Hash ρf BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hbp hfp hBP
  have hmBP : ResU.Hash (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) BP :=
    ResU.hash_of_pairwise (ResU.hash_symm hbm'') hbp
      (ResU.hash_symm hpm'') hBP
  have hFBm' : ResU.Hash FB (ResU.single l (CellU.mutOf β v'' ρPv'' hstr'' Qs hwit'')) :=
    ResU.hash_symm (ResU.hash_of_pairwise
      (ResU.hash_symm hfm'') hfBP hmBP hFB)
  have hFBW' : ResU.Hash FB W'' := ⟨hFBW.1, fρ'p, hFBW, hvfρ'p⟩
  -- H24: the two memories, by 6.25 under a frame (6.8)
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_mut_own hW hvm hvW hFAmc hFAm hFAWc hFAW).mpr h5
  have hmem₂ : ResU.Lower FRBp μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFBm hFBm' hFBW hFBW').mpr h7
  -- H25: `ρ ↭ ρ_b ● ρ''_m ● ρ_p`, by 6.28
  obtain ⟨BPW, hBPW₁, hBPW₂⟩ := (ResU.CompS.assoc W'' ρb ρp π).mpr ⟨ρ', hW''₂, h9⟩
  obtain rfl : BP = BPW := ResU.CompS.functional hBP hBPW₁
  have hvπ' : ResU.Valid π' := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hpRB
    exact ResU.CompS.functional hs hπ' ▸ hv
  have hupd : ResU.Upd ρ π' :=
    (ResU.six28 hW hW'' (ResU.CompS.comm hsplit) hBPm hX (ResU.CompS.comm hBPW₂)
      hvρ hvπ' h10.2.1 h10.2.2).mpr h10.1
  -- exit: `TW.mutFold`
  have hvFRBp : ResU.Valid FRBp := by obtain ⟨σ, hσ, -⟩ := hmem₂; exact ⟨σ, hσ⟩
  have hTout : TW FRBp ps'' (rsOf ls'') :=
    TW.mutFold hT'' hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) hvFRBp
  have htgout : Tagged FRBp ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag hW''₁ (ResU.CompS.comm hFBW) (ResU.CompS.comm hFBm) a).mpr ha) htg''
  -- H26: the callback hands the borrow back
  have hQ : Q ls'' v' RB := hb _ RB hcell'' hRB
  exact ⟨RB, ρp, FRB, FRBp, π', v', μ, μ', ps'', ls'',
    ResU.hash_symm hfRB, hFRB, hpFRB, hmem₁, hFRBp, hmem₂, h8, hπ',
    ⟨hupd, hvρ, hvπ'⟩, h11, hTout, htgout, hps'', hls'', hQ⟩

/-! ### The effectful `wp` -/

theorem ewpStep_mono {Tb : Table} (hTb : Tb.Mono) {Q : List SRec → Val → WProp}
    {P P' : List SRec → Expr → WProp} (hP : ∀ ls e ρ, P ls e ρ → P' ls e ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpStep Tb Q P ls e ρ) : ewpStep Tb Q P' ls e ρ :=
  wpG_mono (fun ls' t ρ' hq => hq.imp id (hTb ls' t P P' ρ' hP)) h

/-- Induction on the fixed point. -/
theorem ewp_ind {Tb : Table} {Q : List SRec → Val → WProp} (P : List SRec → Expr → WProp)
    (hP : ∀ ls e ρ, ewpStep Tb Q P ls e ρ → P ls e ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e Tb Q ρ) : P ls e ρ :=
  h P hP

theorem ewp_fold {Tb : Table} (hTb : Tb.Mono) {Q : List SRec → Val → WProp} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : ewpStep Tb Q (fun ls e => ewpTS ls e Tb Q) ls e ρ) :
    ewpTS ls e Tb Q ρ := by
  intro P hP
  exact hP ls e ρ (ewpStep_mono hTb (fun ls' e' ρ' h' => h' P hP) h)

theorem ewp_unfold {Tb : Table} (hTb : Tb.Mono) {Q : List SRec → Val → WProp} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : ewpTS ls e Tb Q ρ) :
    ewpStep Tb Q (fun ls e => ewpTS ls e Tb Q) ls e ρ :=
  h (fun ls e ρ => ewpStep Tb Q (fun ls e => ewpTS ls e Tb Q) ls e ρ)
    (fun _ _ _ h' => ewpStep_mono hTb (fun _ _ _ h'' => ewp_fold hTb h'') h')

/-- **`ewpTS` at the empty table is `wpTS`.** -/
theorem ewp_bot {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes} :
    ewpTS ls e Table.bot Q ρ ↔ wpTS ls e Q ρ := by
  have hm : Table.bot.Mono := fun _ _ _ _ _ _ h => h
  constructor
  · intro h
    refine (wpTS_iff_wpG ls e Q ρ).mpr (wpG_mono (fun ls' t ρ' hq => ?_) (ewp_unfold hm h))
    rcases hq with hq | hq
    · exact hq
    · exact hq.elim
  · intro h
    exact ewp_fold hm (wpG_mono (fun _ _ _ hq => Or.inl hq) ((wpTS_iff_wpG ls e Q ρ).mp h))

/-- **A pure computation is effectful at every table.** -/
theorem ewp_of_wp {Tb : Table} (hTb : Tb.Mono) {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : wpTS ls e Q ρ) : ewpTS ls e Tb Q ρ :=
  ewp_fold hTb (wpG_mono (fun _ _ _ hq => Or.inl hq) ((wpTS_iff_wpG ls e Q ρ).mp h))

/-- A value answers at once. -/
theorem ewp_val {Tb : Table} (hTb : Tb.Mono) {ls : List SRec} {v : Val}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : Q ls v ρ) : ewpTS ls (.val v) Tb Q ρ :=
  ewp_of_wp hTb (wpTS_val ls v Q ρ h)

/-- **Monotone in the table and the postcondition.** -/
theorem ewp_mono {Tb Tb' : Table} (hTb' : Tb'.Mono)
    (hsub : ∀ ls t Φ ρ, Tb ls t Φ ρ → Tb' ls t Φ ρ)
    {Q Q' : List SRec → Val → WProp} (hQ : ∀ ls v ρ, Q ls v ρ → Q' ls v ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpTS ls e Tb Q ρ) : ewpTS ls e Tb' Q' ρ :=
  ewp_ind (fun ls e ρ => ewpTS ls e Tb' Q' ρ)
    (fun ls' e' ρ' h' => ewp_fold hTb' (wpG_mono (fun ls'' t ρ'' hq => by
      rcases hq with ⟨v, rfl, hv⟩ | hq
      · exact Or.inl ⟨v, rfl, hQ _ _ _ hv⟩
      · exact Or.inr (hsub _ _ _ _ hq)) h')) h

/-- The postcondition of an abortive computation: a value in `Q`, or a stop the table allows,
owing nothing. -/
def ewpPost (Tb : Table) (Q : List SRec → Val → WProp) : List SRec → Expr → WProp :=
  fun ls t ρ => valPost Q ls t ρ ∨ Tb ls t (fun _ _ _ => False) ρ

/-- **At an abortive table `ewpTS` is `wpG` once.** -/
theorem ewp_abortive {Tb : Table} (hTb : Tb.Abortive) {ls : List SRec} {e : Expr}
    {Q : List SRec → Val → WProp} {ρ : WRes} :
    ewpTS ls e Tb Q ρ ↔ wpG ls e (ewpPost Tb Q) ρ := by
  constructor
  · intro h
    exact wpG_mono (fun ls' t ρ' hq => hq.imp id (hTb ls' t _ _ ρ')) (ewp_unfold hTb.mono h)
  · intro h
    exact ewp_fold hTb.mono (wpG_mono (fun ls' t ρ' hq => hq.imp id (hTb ls' t _ _ ρ')) h)

/-! ### The LIFO frame lemmas

A frame around a computation that may stop at an abortive operation ends at the stop exactly as
at a return: the frames at `wpG` do not inspect the term the run ends at.  So an unwinding
operation crosses a borrow's scope without T1: the lend ends when the callback stops, the
lender regains the place, and the stop continues outward (`SPEC.md` §19, *Theorems* 3). -/

/-- `[TR]` 6.64 over `ewpTS` at an abortive table. -/
theorem ewpTS_I_frameU (Tb : Table) (hTb : Tb.Abortive) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (hadm : AdmWf T δ) (v : Val) (e : Expr) (ls : List SRec) (Q : List SRec → Val → WProp)
    (hQ : ∀ ls₁ ls₂ (w : Expr) ρ, Ext ls₁ ls₂ ρ → ewpPost Tb Q ls₁ w ρ → ewpPost Tb Q ls₂ w ρ) :
    Entails
      (ptoOwn l v ⋆ vC true T ls δ v ⋆
        fresh (fun α ρ => ∀ ls', AddAt ls ls' α →
          (∃ r ∈ rsOf ls', r.le = l ∧ r.T = T ∧ r.δ = δ) →
          (ptoImmS l α ls' (fun ls₀ => vC true T ls₀ δ) ─⋆
            wpG ls' e (fun ls'' t =>
              box α (ptoOwn l v ─⋆ (vC true T ls'' δ v ─⋆ ewpPost Tb Q ls'' t)))) ρ))
      (ewpTS ls e Tb Q) :=
  fun ρ h => (ewp_abortive hTb).mpr (wpG_I_frameX l T δ hadm v e ls (ewpPost Tb Q) hQ ρ h)

/-- `[TR]` 6.65 over `ewpTS` at an abortive table. -/
theorem ewpTS_M_frameU (Tb : Table) (hTb : Tb.Abortive) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (β : Life) (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (v : Val) (e : Expr)
    (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails
      (ptoOwn l v ⋆ vC true T ls δ v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆
          wpG ls e (fun ls'' t =>
            box α (all fun w => ptoOwn l w ─⋆ (vC true T ls'' δ w ─⋆ ewpPost Tb Q ls'' t)))))
      (ewpTS ls e Tb Q) :=
  fun ρ h => (ewp_abortive hTb).mpr (wpG_M_frameX l T δ β hP v e ls (ewpPost Tb Q) ρ h)

/-- `[TR]` 6.66 over `ewpTS` at an abortive table. -/
theorem ewpTS_M_antiFrameU (Tb : Table) (hTb : Tb.Abortive) (l : BoCa.Loc) (α : Life) (T : VTy)
    (δ : LSub) (e : Expr) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails
      (ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ⋆
        (all fun v => ptoOwn l v ─⋆ (vC true T ls δ v ─⋆
          wpG ls e (fun ls'' t => ex fun w =>
            ptoOwn l w ⋆ vC true T ls'' δ w ⋆
              (ptoMutS l α ls'' (fun ls₀ => vC true T ls₀ δ) ─⋆ ewpPost Tb Q ls'' t)))))
      (ewpTS ls e Tb Q) :=
  fun ρ h => (ewp_abortive hTb).mpr (wpG_M_antiFrameX l α T δ e ls (ewpPost Tb Q) ρ h)

/-! ### Steps and bind at `wpG` and `ewpTS` -/

/-- One pure step in front of a `wpG`. -/
theorem wpG_step {e e' : Expr} (h : ∀ μ : Heap, Step1N μ e μ e') (ls : List SRec)
    (Q : List SRec → Expr → WProp) : Entails (wpG ls e' Q) (wpG ls e Q) := by
  intro ρ hw ρf fρ ps hf hc hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, h₉, hA, hB,
    hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇,
    ⟨j, ARun.cons (h μ) h₈⟩, h₉, hA, hB, hT', htg', hps, hls, hC⟩

/-- `[TR]` 6.135 (`wp-bind`) at `wpG`: a run to any term `t`, then the continuation from `K[t]`.
`wpTS_bind`'s proof, which never inspects the term the first run ends at. -/
theorem wpG_bind (K : Kont) (e : Expr) (ls : List SRec) (Q : List SRec → Expr → WProp) :
    Entails (wpG ls e fun ls' t => wpG ls' (K.plug t) Q) (wpG ls (K.plug e) Q) := by
  intro ρ hw ρf fρ ps hf h₄ hT htg A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j₁, h₈⟩, h₉,
    hA, hB, hT', htg', hps', hls', hC⟩ := hw ρf fρ ps hf h₄ hT htg A k
  obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρ').mp ⟨fρ', h₂, h₃⟩
  have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
  obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
  have hzY : ResU.CompS z ρ' fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
  obtain ⟨ρ'', ρpp, Y'', Y''p, π'', v', ν, ν', ps'', ls'', k₁, k₂, k₃, k₅, k₆, k₇, ⟨j₂, k₈⟩,
    k₉, kA, kB, kT, ktg, kps, kls, kC⟩ := hC z fρ'p ps' hz hzY hT' htg' A j₁
  obtain ⟨hfρ'', -⟩ := ResU.Hash.split hfz (ResU.hash_symm k₁)
  obtain ⟨F, hF, hFp⟩ := compS_exch hfz k₂
  obtain ⟨ZZ, hZZ, hZF⟩ := (hash_shift ρpp ρp F).mp ⟨Y'', ResU.CompS.comm hFp, k₃⟩
  have hZZ' : ResU.CompS ρp ρpp ZZ := ResU.CompS.comm hZZ
  obtain ⟨ZZ₀, hZZ₀, hFZ₀⟩ := compS_reassoc hFp k₆
  have hFZ : ResU.CompS F ZZ Y''p := by
    rwa [ResU.CompS.functional hZZ₀ hZZ'] at hFZ₀
  have hν : ν = μ' := ResU.Lower.functional k₅ h₇
  obtain ⟨-, hpρ'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
  obtain ⟨d, hd, hfd⟩ := compS_reassoc hfz k₂
  obtain ⟨-, hdp⟩ := ResU.Hash.split hfd (ResU.hash_symm k₃)
  obtain ⟨π₀, hπ₀, hpπ₀⟩ := (hash_shift ρp ρ'' ρpp).mpr ⟨d, hd, hdp⟩
  have hpπ : ResU.Hash ρp π'' := by rwa [ResU.CompS.functional hπ₀ k₉] at hpπ₀
  obtain ⟨Yn, hYn, -⟩ := hpπ.2
  obtain ⟨ZZ₁, hZZ₁, hρ''Z₀⟩ := compS_lcomm k₉ hYn
  have hρ''Z : ResU.CompS ρ'' ZZ Yn := by
    rwa [ResU.CompS.functional hZZ₁ hZZ'] at hρ''Z₀
  refine ⟨ρ'', ZZ, F, Y''p, Yn, v', μ, ν', ps'', ls'', ResU.hash_symm hfρ'', hF, hZF,
    h₅, hFZ, k₇, ⟨j₂, (h₈.plug K).trans (hν ▸ k₈)⟩, hρ''Z, ?_,
    noOwn_compS hZZ' hB kB, kT, ktg, fun p => (kps p).trans (hps' p),
    fun x => (kls x).trans (hls' x), kC⟩
  exact ResU.UpdV.trans hA
    (updV_frame (ResU.CompS.comm h₉) hYn (ResU.hash_symm hpρ') hpπ kA)

/-- Bind a pure prefix in front of a `wpG`. -/
theorem wpG_bind_pure (K : Kont) (e : Expr) (ls : List SRec) (Q : List SRec → Expr → WProp) :
    Entails (wpTS ls e fun ls' v => wpG ls' (K.plug (.val v)) Q) (wpG ls (K.plug e) Q) := by
  intro ρ h
  refine wpG_bind K e ls Q ρ (wpG_mono (fun ls' t ρ' ht => ?_) ((wpTS_iff_wpG _ _ _ _).mp h))
  obtain ⟨v, rfl, hv⟩ := ht
  exact hv

/-- A pure prefix in front of a `wpG`, framing `R` through its run: `wpTS_bind_frame` at `wpG`. -/
theorem wpG_bind_frame (K : Kont) (e : Expr) (ls : List SRec) (P : List SRec → Val → WProp)
    (R : List SRec → WProp) (Q : List SRec → Expr → WProp)
    (hR : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls'))
    (h : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails ((P ls' v) ⋆ R ls') (wpG ls' (K.plug (.val v)) Q)) :
    Entails ((wpTS ls e P) ⋆ R ls) (wpG ls (K.plug e) Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hwp, hRρ⟩
  refine wpG_bind_pure K e ls Q ρ
    (wpTS_ramify ls e P (fun ls' v => wpG ls' (K.plug (.val v)) Q) ρ ?_)
  refine ⟨ρ₁, ρ₂, hc, hwp, ?_⟩
  intro ls' hls v σ₁ σ₂ hP hcs
  exact h ls' hls v σ₂ ⟨σ₁, ρ₂, ResU.CompS.comm hcs, hP, hR ls' hls ρ₂ hRρ⟩

/-- One pure step in front of an `ewpTS`. -/
theorem ewp_step {Tb : Table} (hTb : Tb.Mono) {e e' : Expr} (h : ∀ μ : Heap, Step1N μ e μ e')
    (ls : List SRec) (Q : List SRec → Val → WProp) : Entails (ewpTS ls e' Tb Q) (ewpTS ls e Tb Q) :=
  fun ρ h' => ewp_fold hTb (wpG_step h ls _ ρ (ewp_unfold hTb h'))

/-- A pure prefix in front of an `ewpTS`, framing `R` through its run.  `[spec §19]` -/
theorem ewp_bind_pure_frame {Tb : Table} (hTb : Tb.Mono) (K : Kont) (e : Expr) (ls : List SRec)
    (P : List SRec → Val → WProp) (R : List SRec → WProp) (Q : List SRec → Val → WProp)
    (hR : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls'))
    (h : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ v,
      Entails ((P ls' v) ⋆ R ls') (ewpTS ls' (K.plug (.val v)) Tb Q)) :
    Entails ((wpTS ls e P) ⋆ R ls) (ewpTS ls (K.plug e) Tb Q) :=
  fun ρ h' => ewp_fold hTb (wpG_bind_frame K e ls P R _ hR
    (fun ls' hls v σ hσ => ewp_unfold hTb (h ls' hls v σ hσ)) ρ h')

/-- A stop at an operation is monotone in the continuations it owes. -/
theorem performStop_mono (T : OpTab) : (performStop T).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨hp, h⟩ := pure_sep_iff.mp h
  refine ⟨K, n, i, v, en, pure_sep_mk hp ?_⟩
  obtain ⟨ρ₁, ρ₂, hc, hA, hk, hK⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hA, hk, fun ls' hext => ⟨fun w σ₁ σ₂ hB hcσ => ?_, (hK ls' hext).2⟩⟩
  exact hΦ _ _ _ ((hK ls' hext).1 w σ₁ σ₂ hB hcσ)

/-- The protocol table of an operation table is monotone in the continuations it owes. -/
theorem opTable_mono (T : OpTab) : (opTable T).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with h | h
  · exact Or.inl (performStop_mono T ls t Φ Φ' ρ hΦ h)
  · exact Or.inr h

/-- The table of a cancel run is monotone in the continuations it owes. -/
theorem cancelTab_mono (T : OpTab) : (cancelTab T).Mono := by
  intro ls t Φ Φ' ρ hΦ h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (performStop_mono T ls t Φ Φ' ρ hΦ h)

/-- A run of no steps: the term is where `wpG` ends.  `wpTS_val`'s proof at any term. -/
theorem wpG_here (ls : List SRec) (e : Expr) (Q : List SRec → Expr → WProp) :
    Entails (Q ls e) (wpG ls e Q) := by
  intro ρ hQ ρf fρ ps hf hc hT htg A k
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hc
  exact ⟨ρ, PMap.empty, fρ, fρ, ρ, e, μ, μ, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), hμ,
    ResU.comp_empty_right fρ, hμ, ⟨k, .refl _ _ _⟩, ResU.comp_empty_right ρ,
    (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-- One head step in front of a `wpG`. -/
theorem wpG_head {e e' : Expr} (h : ∀ μ : Heap, Head μ e μ e') (hn : e.allocs = false)
    (ls : List SRec) (Q : List SRec → Expr → WProp) : Entails (wpG ls e' Q) (wpG ls e Q) :=
  wpG_step (fun μ => Step1N.head (h μ) hn) ls Q

/-- `[TR]` 6.146 (`wp-ramify`) at `wpG`: `wpTS_ramify`'s proof. -/
theorem wpG_ramify (ls : List SRec) (e : Expr) (P Q : List SRec → Expr → WProp) :
    Entails (sep (wpG ls e P)
      (fun ρ => ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ t, wand (P ls' t) (Q ls' t) ρ))
      (wpG ls e Q) := by
  rintro ρ ⟨ρ₁, ρ₂, hcρ, hwp, hwand⟩ ρf fρ ps hf hc hT htg A k
  obtain ⟨y, hy, hy₁⟩ := (hash_shift ρf ρ₂ ρ₁).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  obtain ⟨ρ', ρp, Y', Y'p, π', v, μ, μ', ps', ls', g₁, g₂, g₃, g₅, g₆, g₇, g₈, g₉,
    gA, gB, gT, gtg, gps, gls, gC⟩ := hwp y fρ ps hy₁ hyfρ hT htg A k
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  obtain ⟨W₀, hW₀, hWf₀⟩ := (hash_shift ρ' ρ₂ ρf).mp ⟨y, ResU.CompS.comm hy, g₁⟩
  have hWf : ResU.Hash W ρf := by
    rwa [ResU.CompS.functional (ResU.CompS.comm hW₀) hW] at hWf₀
  obtain ⟨-, hWp⟩ := ResU.Hash.split hfW (ResU.hash_symm g₃)
  obtain ⟨πW, hπW, h₂π₀⟩ := (hash_shift ρ₂ ρ' ρp).mpr ⟨W, hW, hWp⟩
  have h₂π : ResU.Hash ρ₂ π' := by rwa [ResU.CompS.functional hπW g₉] at h₂π₀
  obtain ⟨πn, hπn, -⟩ := h₂π.2
  obtain ⟨Wn, hWn, hWπ₀⟩ := compS_reassoc' g₉ hπn
  have hWπ : ResU.CompS W ρp πn := by
    rwa [ResU.CompS.functional hWn hW] at hWπ₀
  refine ⟨W, ρp, Y', Y'p, πn, v, μ, μ', ps', ls', hWf, hfW, g₃, g₅, g₆, g₇, g₈,
    hWπ, ?_, gB, gT, gtg, gps, gls, hwand ls' gls v ρ' W gC hW⟩
  exact updV_frame (ResU.CompS.comm hcρ) hπn
    ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, (hash_valid hf).2⟩ h₂π gA

/-- A frame through a `wpG`, carried to the returned list by `hR`. -/
theorem wpG_frame {ls : List SRec} {e : Expr} {Q : List SRec → Expr → WProp} (R : List SRec → WProp)
    (hR : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → Entails (R ls) (R ls')) :
    Entails (wpG ls e Q ⋆ R ls) (wpG ls e fun ls' t => Q ls' t ⋆ R ls') := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hw, hr⟩
  refine wpG_ramify ls e Q _ ρ ⟨ρ₁, ρ₂, hc, hw, fun ls' hls t σ₁ σ₂ hq hcσ => ?_⟩
  exact ⟨σ₁, ρ₂, ResU.CompS.comm hcσ, hq, hR ls' hls ρ₂ hr⟩


end BoCa.Fig16.LogRel.Core

end
