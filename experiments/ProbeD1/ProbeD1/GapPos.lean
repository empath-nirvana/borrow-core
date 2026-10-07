import ProbeD1.GapRows

/-!
# ProbeD1 — the position-`∀` (`GAP.md` §3)

The direction given with the task, made exact: the `∀` over lifetimes read at every position of
the finite order of lifetimes in play, each position realised by a fresh lifetime inserted there.
`GAP.md` §3.2 gives two readings; this file proves the lemmas both are designed with.

* **Reading (B), `AllPosJ`**: the clause read at every instantiation of the stack, the views
  handed back, then at every lifetime below the bound.
  - **Every cut below the stack's cut is realised by an instantiation** (`instRealisesCut`,
    `instRealisesCut_at`): the shift by one at the cut's upper end, lifted to the stack's cut, and
    the lifetime just below that end. No source-side stretch: the realisation is an instantiation
    of the stack, the configuration W's re-lend reaches.
  - **No instantiation opens a cut at or above the stack's cut** (`inst_closed_above`): every one
    fixes each lifetime there, so two adjacent lifetimes there stay adjacent.
  - **At `σ = []` it is Core's clause, both ways** (`allPosJNil`).
  - **It gives the `ℕ`-`∀` at the stack itself** (`allPosJSelf`).
  - **It is carried along an instantiation by transport** (`allPosJTransport`): a realisation at the
    instantiated index is one at the composite instantiation (`instComp`). This is the "`∀` by
    transport" step, for every body.
* **Reading (A), `CutAllC`**: Core's relation at every renaming of the configuration by an embedding
  fixing `⊤`. It implies Core's clause at `σ = []` by the identity renaming (`cutAllNilSound`, with
  `relRU_id`: the identity embedding moves no cell and no stored invariant); the converse is
  refuted (`not_coreAllImpCutAll`, `GapWitness.lean`). So (A)'s agreement with Core is one-way.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack extS stratS)

/-! ### Realising a cut -/

/-- **Every cut below the stack's cut is realised at an instantiation**: the shift by one at the
cut's upper end `hi`, lifted to `c`, moves everything below `hi` down by one and fixes everything
at or above it; the lifetime just below `hi` then stands between the two sides. -/
theorem instRealisesCut : InstRealisesCut := by
  intro L c lo hi hlh hhc _
  refine ⟨Restrat.Emb.lift (Restrat.Emb.shift hi 1) hhc,
    OrderDual.toDual (OrderDual.ofDual hi + 1), fun a _ => ⟨fun hal => ?_, fun hha => ?_⟩⟩
  · have hah : a < hi := lt_of_le_of_lt hal hlh
    show OrderDual.ofDual (OrderDual.toDual (OrderDual.ofDual hi + 1)) <
      OrderDual.ofDual (Restrat.Emb.shift hi 1 a)
    rw [Restrat.Emb.shift_apply_lt hah]
    have : OrderDual.ofDual hi < OrderDual.ofDual a := hah
    simp only [OrderDual.ofDual_toDual]
    omega
  · have hfix : Restrat.Emb.lift (Restrat.Emb.shift hi 1) hhc a = a :=
      (Restrat.Emb.shift hi 1).fix a hha
    rw [hfix]
    show OrderDual.ofDual a < OrderDual.ofDual (OrderDual.toDual (OrderDual.ofDual hi + 1))
    have : OrderDual.ofDual a ≤ OrderDual.ofDual hi := hha
    simp only [OrderDual.ofDual_toDual]
    omega

/-- **`instRealisesCut` at a stack**: the realising re-stratification is an instantiation of the
stack (`InstAt`), at the stack's cut. -/
theorem instRealisesCut_at {αs : List Life} {c : Life} (hc : cutOf αs = some c) (L : List Life)
    {lo hi : Life} (hlh : lo < hi) (hhc : hi ≤ c) (hL : ∀ a ∈ L, a ≤ lo ∨ hi ≤ a) :
    ∃ (ι : Inst) (α : Life), InstAt αs ι ∧
      ∀ a ∈ L, (a ≤ lo → ι.life1 a < α) ∧ (hi ≤ a → α < ι.life1 a) := by
  obtain ⟨θ, α, h⟩ := instRealisesCut L c lo hi hlh hhc hL
  exact ⟨Inst.ofEmb θ, α, fun c' θ' he => by cases he; exact hc, h⟩

/-- **No instantiation opens a cut at or above the stack's cut**: it fixes both ends, so a lifetime
strictly between their images is strictly between the ends themselves. -/
theorem inst_closed_above {αs : List Life} {c : Life} (hc : cutOf αs = some c) {ι : Inst}
    (hat : InstAt αs ι) {lo hi : Life} (hlo : c ≤ lo) (hhi : c ≤ hi) {α : Life}
    (h₁ : ι.life1 lo < α) (h₂ : α < ι.life1 hi) : lo < α ∧ α < hi := by
  rcases ι with _ | ⟨c', θ⟩
  · exact ⟨h₁, h₂⟩
  · have hc' : c' = c := Option.some.inj ((hat c' θ rfl).symm.trans hc)
    subst hc'
    have e₁ : Inst.life1 (some ⟨c', θ⟩) lo = lo := θ.fix lo hlo
    have e₂ : Inst.life1 (some ⟨c', θ⟩) hi = hi := θ.fix hi hhi
    rw [e₁] at h₁; rw [e₂] at h₂
    exact ⟨h₁, h₂⟩

/-! ### Reading (B) at the empty stack and at the stack itself -/

theorem instAt_nil_eq {ι : Inst} (h : InstAt [] ι) : ι = none := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · exact absurd (h c θ rfl) (by simp [cutOf])

theorem instAt_none (αs : List Life) : InstAt αs (none : Inst) := fun _ _ h => by cases h

theorem Inst.life_none (αs : List Life) : Inst.life none αs = αs := List.map_id' αs

/-- **At `σ = []` the position-`∀` is Core's clause, both ways**: the empty stack has no cut, so
the only instantiation is the identity, and there are no views. -/
theorem allPosJNil : AllPosJNil := by
  intro δ c P ls ρ
  constructor
  · rintro ⟨ds, ρz, ρn, hc, hn, -, H⟩
    cases ds with
    | cons d ds => exact hn.1.elim
    | nil =>
        have hn0 : ρn = PMap.empty := hn.1.1
        subst hn0
        have hz : ρ = ρz := eq_of_compS_empty_left (ResU.CompS.comm hc)
        subst hz
        exact H none (instAt_none []) (fun a ha => absurd ha List.not_mem_nil) PMap.empty ρ
          ⟨⟨rfl, trivial⟩, pvlNil _ _ _⟩ hc
  · intro h
    refine ⟨[], ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨⟨rfl, trivial⟩, pvlNil _ _ _⟩,
      fun a ha => absurd ha (by simp), fun ι hat _ ρv τ hv hcv => ?_⟩
    obtain rfl := instAt_nil_eq hat
    have hv0 : ρv = PMap.empty := hv.1.1
    subst hv0
    rw [show τ = ρ from ResU.CompS.functional hcv (ResU.comp_empty_right ρ)]
    exact h

/-- **The position-`∀` gives the `ℕ`-`∀` at the stack itself**: the identity instantiation, the
views handed back as they were dropped. -/
theorem allPosJSelf : AllPosJSelf := by
  intro δ σ c P αs ls ρ _ hro h α
  obtain ⟨ds, ρz, ρn, hc, hn, -, H⟩ := h
  have H' := H none (instAt_none αs) (by rw [Inst.life_none]; exact hro)
  rw [Inst.life_none] at H'
  exact H' ρn ρ hn hc α

/-! ### Reading (B) by transport -/

/-- **The position-`∀` is carried along an instantiation, by transport**: at an instantiation `ι`
of the stack, with the views handed back, it holds at the instantiated index. A realisation there,
an instantiation `ι₂` of the instantiated stack, is the composite `ι₂ ∘ ι` of the stack
(`instComp`), the readings, lend lifetimes and records composed with it; the retained part stays
above the instantiated outermost lend (`stratS_inst`). -/
theorem allPosJTransport : AllPosJTransport := by
  intro δ σ c P αs ls ρ _ h
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat _ ρv τ hv hcv => ?_⟩
  refine ⟨ds, ρz, ρv, hcv, hv, stratS_inst ι hz, fun ι₂ hat₂ hro₂ ρv₂ τ₂ hv₂ hcv₂ => ?_⟩
  obtain ⟨ι₃, hat₃, hsub, hlife, hrecs⟩ := instComp αs ι ι₂ hat hat₂
  have hl₃ : ι₃.life αs = ι₂.life (ι.life αs) := by
    simp only [Inst.life, List.map_map]
    exact List.map_congr_left fun a _ => hlife a
  have := H ι₃ hat₃ (by rw [hl₃, hrecs]; exact hro₂) ρv₂ τ₂ (by rw [hl₃, hsub, hrecs]; exact hv₂)
    hcv₂
  rw [hl₃, hsub, hrecs] at this
  exact this

/-! ### Reading (A): the identity renaming -/

namespace Restrat.Emb
variable {c : Life} {Loc Val : Type}

/-- An embedding that moves no lifetime moves no set of lifetimes. -/
theorem mapL_of_fixAll (e : _root_.Restrat.Emb c) (hfix : ∀ x, e x = x) (s : LSet) :
    e.mapL s = s := by
  refine _root_.Restrat.Emb.lset_ext (fun y => ?_) (hfix _) (hfix _)
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [hfix x]
  · intro hy
    exact ⟨y, hy, hfix y⟩

/-- **An embedding that moves no lifetime moves no cell**, stored invariants included: by
well-founded induction on the stratum, as `relU_of_inStratum_aux`, with no cut. -/
theorem relU_of_fixAll_aux (e : _root_.Restrat.Emb c) (hfix : ∀ x, e x = x) :
    ∀ α : Life, ∀ ψ : CellU Loc Val, ψ.InStratum α → e.relU ψ = ψ := by
  intro α
  induction α using (invImage OrderDual.ofDual Nat.lt_wfRel).wf.induction with
  | _ α ih =>
    intro ψ hψ
    have resFix : ∀ β, α < β → ∀ χ : ResU Loc Val, χ.InStratum β → e.relRU χ = χ := by
      intro β hβ χ hχ
      refine PMap.ext fun l => ?_
      rw [_root_.Restrat.Emb.relRU_get]
      cases hl : χ.get l with
      | none => rfl
      | some φ => exact congrArg some (ih β hβ φ (hχ l φ hl))
    rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, h, rfl⟩ | ⟨b, v, χ, h, P, hw, rfl⟩
    · rfl
    · have hs : α < s.meet := hψ
      have hj : α < s.join := lt_of_lt_of_le hs s.meet_le_join
      have hχ : e.relRU χ = χ := resFix s.join hj χ h
      rw [e.relU_immOf]
      exact CellU.immOf_congr (mapL_of_fixAll e hfix s) rfl hχ _ _
    · have hb : α < b := hψ
      have hχ : e.relRU χ = χ := resFix b hb χ h
      rw [e.relU_mutOf]
      refine _root_.Restrat.Emb.mutOf_congr' (hfix b) hχ fun r hr hr' w => ⟨?_, ?_⟩
      · rintro ⟨r₀, h₀, hP⟩
        have h₀' : e.relRU r₀.val = r := h₀
        rw [resFix b hb r₀.val r₀.property] at h₀'
        have : r₀ = ⟨r, hr'⟩ := Subtype.ext h₀'
        rwa [← this]
      · intro hP
        exact ⟨⟨r, hr'⟩, resFix b hb r hr', hP⟩

/-- Every cell is in some stratum: one just below its lifetime. -/
theorem cellU_inStratum_some (ψ : CellU Loc Val) : ∃ α : Life, ψ.InStratum α := by
  cases ψ with
  | own v => exact ⟨⊤, trivial⟩
  | imm i =>
      refine ⟨OrderDual.toDual (OrderDual.ofDual i.ls.meet + 1), ?_⟩
      show OrderDual.ofDual i.ls.meet < OrderDual.ofDual i.ls.meet + 1
      omega
  | «mut» m =>
      refine ⟨OrderDual.toDual (OrderDual.ofDual m.β + 1), ?_⟩
      show OrderDual.ofDual m.β < OrderDual.ofDual m.β + 1
      omega

theorem relRU_of_fixAll (e : _root_.Restrat.Emb c) (hfix : ∀ x, e x = x) (ρ : ResU Loc Val) :
    e.relRU ρ = ρ := by
  refine PMap.ext fun l => ?_
  rw [_root_.Restrat.Emb.relRU_get]
  cases hl : ρ.get l with
  | none => rfl
  | some φ =>
      obtain ⟨α, hα⟩ := cellU_inStratum_some φ
      exact congrArg some (relU_of_fixAll_aux e hfix α φ hα)

/-- **The identity embedding moves no cell.** -/
theorem relRU_id (ρ : ResU Loc Val) : (_root_.Restrat.Emb.id c).relRU ρ = ρ :=
  relRU_of_fixAll _ (fun _ => rfl) ρ

end Restrat.Emb

theorem mapN_id_eq (δ : LSub) : Restrat.LSub.mapN (Restrat.Emb.id (⊤ : Life)).toNat δ = δ :=
  mapN_eq_self fun _ _ => rfl

theorem srecRestrat_id (x : SRec) : Targets.srecRestrat (Restrat.Emb.id (⊤ : Life)) x = x := by
  obtain ⟨⟨le, v, R, T, δ⟩, t⟩ := x
  unfold Targets.srecRestrat FrameRec.restrat
  rw [Restrat.Emb.relRU_id, mapN_id_eq]
  rfl

theorem map_srecRestrat_id (ls : List SRec) :
    ls.map (Targets.srecRestrat (Restrat.Emb.id (⊤ : Life))) = ls := by
  induction ls with
  | nil => rfl
  | cons x t ih => rw [List.map_cons, srecRestrat_id, ih]

/-- **Reading (A) implies Core's clause at `σ = []`**: the identity renaming, which moves no
reading, record or cell. With `not_coreAllImpCutAll`, (A)'s agreement with Core is one-way. -/
theorem cutAllNilSound : CutAllNilSound (ℍ := ℍ) := by
  intro C ls δ e ρ h
  have h' := h (Restrat.Emb.id ⊤)
  rwa [map_srecRestrat_id, mapN_id_eq, Restrat.Emb.relRU_id] at h'

end ProbeD1

end
