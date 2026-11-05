import Core.Chain.SI.HeapX
import Core.Chain.SI.HandleN

/-!
# A handler at `erwpX`: `erwpX_handle_le`  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 2b. `erwp_handle_le`'s proof (`SI/HandleN.lean`) at the
one relation, over an operation table whose predicates read `XRes` (`OpEntX`, `opTableX`).

**The table at a mask.** A stop at an operation names the mask its continuation resumes at
(`erwpXPost`). An entry with `remask = false` stops only at the segment's own mask; one with
`remask = true` may name another (a scheduler's `park`, whose task resumes in a later segment).
A handler resumes what it catches inside its own segment, so the operations of the handler's name
are entries with `remask = false`: `κ` resumes the handled continuation at the handler's mask.
An operation of another name passes outward at the mask it named.

**What is covered.** `[ret]`; an operation of the handler's name that must be resumed (`lin`),
whose `κ` owns its cell (`kappaCell`), allocated at the `[op]` step and released at the resume
(`erwpX_kappaCell`, `erwpX_kappaC_resume`, from `erwpX_alloc` and `erwpX_free`); an operation of
another name, which passes outward with the handler reinstalled in its continuation, its cancel
obligation carried. The table has no abortive operations, and a caught operation is not
cancellable: `erwp_ccatch` at the one relation is not built.

By induction on the index, at every mask: a stop of the handled run resumes at the mask it named,
which the induction hypothesis covers below the index.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

/-! ### Tables over `XRes` -/

/-- `ρ ● ρ₁ = ρ₂` over `XRes`: the worlds compose and the ghosts add. -/
def CompX (x y z : XRes) : Prop := ResU.CompS x.1 y.1 z.1 ∧ z.2 = x.2 + y.2

/-- `P –⋆ R` over `XRes`, in `[TR]`'s composition order. -/
def wandX (P R : XProp) : XProp := fun x => ∀ y z, P y → CompX x y z → R z

/-- `OpEntN` over `XRes`, with whether a stop at it may resume at another mask. -/
structure OpEntX where
  q : Qual
  /-- A stop at this entry may name a mask other than its segment's. -/
  remask : Bool
  PA : Nat → List SRec → Val → XProp
  PB : Nat → List SRec → Val → XProp
  fin : Option (Nat → List SRec → Expr → XProp)
  wc : List SRec → List SRec → XRes → Prop

abbrev OpTabX := UInt32 → UInt32 → Option OpEntX

/-- `cancelOK` over `XRes`. -/
def cancelOKX (en : OpEntX) (k : Nat) (ls : List SRec) (K : Kont) : XProp := fun x =>
  ∀ P, en.fin = some P → P k ls (K.dead.plug (raiseE (.val (cancelVal none)))) x

/-- `contShare` over `XRes`: resumed at every answer in `PB` at every `k′ < k`, at every world
the entry's `wc` allows. -/
def contShareX (en : OpEntX) (k : Nat) (ls : List SRec) (K : Kont) (Ψ : ContX) : XProp :=
  fun x =>
    (en.q = .unr → x.1 = PMap.empty) ∧
    ∀ ls', en.wc ls ls' x →
      (∀ k', k' < k → ∀ w : Val, wandX (en.PB k' ls' w) (Ψ k' ls' (K.plug (.val w))) x) ∧
      (en.q ≠ .lin → cancelOKX en k ls' K x)

/-- **`performStop` at a mask**: a stop at `K[perform p]`, `K` with no handler for `p`'s name, at
an entry of the table that allows the continuation's mask `M′`. -/
def opTableX (T : OpTabX) : TableX := fun M M' _ k ls t Ψ x =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntX),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    (en.remask = true ∨ M' = M) ∧ sepX (en.PA k ls v) (contShareX en k ls K Ψ) x

/-- An operation table's predicates read at the current index are downward closed. -/
structure OpTabX.Down (T : OpTabX) : Prop where
  pa : ∀ n i en, T n i = some en → ∀ k ls v x, en.PA (k + 1) ls v x → en.PA k ls v x
  fin : ∀ n i en P, T n i = some en → en.fin = some P → ∀ k ls e x, P (k + 1) ls e x →
    P k ls e x
  /-- The world condition passes to a part of the share. -/
  wcl : ∀ n i en, T n i = some en → ∀ ls ls' (x₁ x₂ x : XRes), CompX x₁ x₂ x →
    en.wc ls ls' x → en.wc ls ls' x₁

theorem opTableX_local (T : OpTabX) : (opTableX T).Local := by
  rintro M M' C k ls t Ψ Ψ' x hΨ ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, ga, gk, hc, hg, hA,
    hu, hcont⟩
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, ga, gk, hc, hg, hA, hu, fun ls' he =>
    ⟨fun k' hk w y z hB hcz => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w y z hB hcz),
      (hcont ls' he).2⟩⟩

theorem opTableX_down {T : OpTabX} (hT : T.Down) : (opTableX T).Down := by
  rintro M M' C k ls t Ψ x ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, ga, gk, hc, hg, hA, hu,
    hcont⟩
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, ga, gk, hc, hg, hT.pa _ _ _ h₃ _ _ _ _ hA, hu,
    fun ls' he => ⟨fun k' hk => (hcont ls' he).1 k' (by omega), fun hq P hP =>
      hT.fin _ _ _ _ h₃ hP _ _ _ _ ((hcont ls' he).2 hq P hP)⟩⟩

/-! ### `κ` -/

/-- `KapRelN` over `XRes`, at a mask: resumed at every answer in `PB` at every `k′ < k`, as the
handled continuation at the handler's mask `M`. -/
def KapRelX (Φ : LocFam) (M : Mask) (Tb : TableX) (Q : PostX) (en : OpEntX) (k : Nat)
    (ls : List SRec) (κ : Val) : XProp := fun x =>
  ∀ ls', en.wc ls ls' x → ∀ k', k' < k → ∀ w : Val,
    wandX (en.PB k' ls' w)
      (erwpX (ℍ := ℍ) Φ M Tb Q k' ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) x

/-- **The capture cell's allocation, at `erwpX`** (`erwp_kappaCell`). -/
theorem erwpX_kappaCell {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hL : Tb.Local)
    (hTd : Tb.Down) {Q : PostX} (hQ : Q.Down) (hasCancel : Bool) (H : Val) (K : Kont)
    (Kc : Kont) {n : Nat} {ls : List SRec} {ρ : WRes} {g : GRes}
    (h : ∀ (ℓ : Loc) (ρ' : WRes), ResU.CompS (ResU.single ℓ (CellU.ownOf Val.unit)) ρ ρ' →
      erwpX (ℍ := ℍ) Φ M Tb Q (n - 1) ls (Kc.plug (kappaC hasCancel ℓ H K)) (ρ', g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls (Kc.plug (kappaCell hasCancel H K)) (ρ, g) := by
  have e : Kc.plug (kappaCell hasCancel H K) =
      (Kc.comp (.appR (.val (.lam (BoLo.kappaCBody hasCancel H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine erwpX_alloc hΦ hL _ Val.unit (fun ℓ ρ' hc => ?_)
  rw [Kont.plug_comp]
  refine erwpX_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc ℓ)) rfl Kc) ?_
  rw [kappaCBody_subst]
  exact h ℓ ρ' hc

/-- **Resuming a `κ` that owns a cell, at `erwpX`** (`erwp_kappaC_resume`): the cell is released,
one step, and `hnd H K[w]` runs at the index left. -/
theorem erwpX_kappaC_resume {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hL : Tb.Local)
    (hTd : Tb.Down) {Q : PostX} (hQ : Q.Down) (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont)
    (w : Val) {k : Nat} {ls : List SRec} {ρ ρ₂ : WRes} {g : GRes}
    (hcρ : ResU.CompS (ResU.single ℓ (CellU.ownOf Val.unit)) ρ₂ ρ)
    (h : erwpX (ℍ := ℍ) Φ M Tb Q (k - 1) ls (hndE H (K.plug (.val w))) (ρ₂, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q k ls
      (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) (ρ, g) := by
  refine erwpX_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole w)) ?_
  refine erwpX_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole w)) ?_
  refine erwpX_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwpX_free hΦ hL (Kont.appL (Kont.seq .hole _) w) ℓ Val.unit hcρ ?_
  refine erwpX_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwpX_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

/-! ### The handler -/

/-- **A handler at `erwpX`, its clauses asked at the stops up to `N`** (`[handle]`), by induction
on the index, at every mask. The operations of the handler's name are must-resume entries that
stop at their segment's mask (`remask = false`); the return clause and the operation clauses are
asked at every mask a segment of the handled run is at, since a stop of another name may resume
the run at another. -/
theorem erwpX_handle_le {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (Tin Tout : OpTabX)
    (hTinD : Tin.Down) (hTout : Tout.Down) (n₀ : UInt32)
    (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val) (Qin Qout : PostX)
    (hQout : Qout.Down)
    (hlin : ∀ i en, Tin n₀ i = some en → en.q = .lin ∧ en.remask = false)
    (hq : ∀ i en, Tin n₀ i = some en → capTag qs.1 i.toNat = en.q.tag)
    (hret : ∀ M C k, k ≤ N → ∀ ls v x, Qin C k ls v x →
      erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout k ls (.app (.val hr) (.val v)) x)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      ∀ M k, k ≤ N → ∀ ls v (κ : Val) x,
        sepX (en.PA k ls v) (KapRelX (ℍ := ℍ) Φ M (opTableX Tout) Qout en k ls κ) x →
        erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) x) :
    ∀ n, n ≤ N → ∀ M ls e x, erwpX (ℍ := ℍ) Φ M (opTableX Tin) Qin n ls e x →
      erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) x := by
  have hLin := opTableX_local Tin
  have hLout := opTableX_local Tout
  have hDout := opTableX_down hTout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN M ls e x h
  have hPD := erwpXPost_down (M := M) hDout hQout (erwpXC (ℍ := ℍ) Φ (opTableX Tout) Qout n)
  set H := hndVal n₀ qs hr hs with hH
  rw [erwpX_eq]
  show rwpGX (ℍ := ℍ) Φ M _ n ls ((hndK H).plug e) x
  refine rwpGX_bind hΦ (hndK H) ?_
  refine rwpGX_mono_le (fun M' C k hk ls' t y ht => ?_) (erwpX_unfold_at hLin le_rfl h)
  -- what the continuations of the handled run are owed, read through the induction hypothesis
  have hcontIH : ∀ M'' k', k' < k → ∀ ls'' e'' τ,
      erwpXC (ℍ := ℍ) Φ (opTableX Tin) Qin n M'' k' ls'' e'' τ →
      erwpXC (ℍ := ℍ) Φ (opTableX Tout) Qout n M'' k' ls'' (hndE H e'') τ := by
    intro M'' k' hk' ls'' e'' τ hc
    simp only [erwpXC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) (by omega) M'' ls'' e'' τ hc
  rcases ht with ⟨hM', v, rfl, hv⟩ | ht
  · -- `[ret]`
    subst M'
    exact Or.inl ⟨rfl, (rwpGX_det hΦ hPD
      (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (erwpX_unfold_at hLout hk (hret M C k (by omega) ls' v y hv))).at C⟩
  obtain ⟨K₁, m, i, v, en, rfl, hK₁, hT, hrm, ρa, ρk, ga, gk, hcak, hg, hA, hu, hcont⟩ := ht
  by_cases hm : m = n₀
  · -- `[op]` at the handler's name: the clause, with `κ` owning its cell
    subst hm
    obtain ⟨hql, hrf⟩ := hlin i en hT
    have hMM : M' = M := by rw [hrf] at hrm; simpa using hrm
    subst M'
    obtain ⟨c, hc, hna⟩ := hop i en hT
    refine Or.inl ⟨rfl, (rwpGX_det hΦ hPD
      (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_).at C⟩
    rw [hq i en hT, kappaAt_tag, hql]
    obtain ⟨y₁, y₂⟩ := y
    simp only at hcak hg
    subst hg
    refine erwpX_unfold_at hLout hk (erwpX_kappaCell hΦ hLout hDout hQout false H K₁
      (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₂ hc₂ => ?_))
    -- the cell beside the continuation's share
    obtain ⟨z, hz₁, hz₂⟩ := compS_reassoc hcak (ResU.CompS.comm hc₂)
    have hA' : en.PA (k - 1) ls' v (ρa, ga) := by
      cases k with
      | zero => exact hA
      | succ k₀ => exact hTinD.pa _ _ _ hT _ _ _ _ hA
    refine hna M (k - 1) (by omega) ls' v ⟨_, isVal_kappaC _ ℓ H K₁⟩ (σ₂, ga + gk)
      ⟨ρa, z, ga, gk, hz₂, rfl, hA', ?_⟩
    intro ls'' he k' hk' w y z' hB hcz
    -- the continuation's share is the part beside the cell
    have hzk : CompX (ρk, gk) (ResU.single ℓ (CellU.ownOf Val.unit), 0) (z, gk) :=
      ⟨hz₁, by simp⟩
    have he' := hTinD.wcl _ _ _ hT _ _ _ _ _ hzk he
    obtain ⟨hcz₁, hcz₂⟩ := hcz
    simp only at hcz₁ hcz₂
    obtain ⟨u, hu₁, hu₂⟩ := compS_exch hz₁ hcz₁
    have h₁ := hcontIH M k' (by omega) _ _ _
      ((hcont ls'' he').1 k' (by omega) w y (u, gk + y.2) hB ⟨hu₁, rfl⟩)
    simp only [erwpXC, show k' < n by omega, if_true] at h₁
    obtain ⟨z'₁, z'₂⟩ := z'
    simp only at hcz₂ hu₂ ⊢
    subst hcz₂
    exact erwpX_kappaC_resume hΦ hLout hDout hQout _ ℓ H K₁ w (ResU.CompS.comm hu₂)
      (erwpX_le hΦ hLout hDout hQout (Nat.sub_le k' 1) h₁)
  · -- an operation of another name passes outward, at the mask it named
    have hKo : ((hndK H).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
    have ht' : (hndK H).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((hndK H).comp K₁).plug (performE (.val (opPayload m i v))) := by
      rw [Kont.plug_comp]
    refine Or.inr ⟨by rw [ht']; exact final_opPlug (r := false) (payloadName_opPayload m i v) hKo,
      Or.inr ?_⟩
    rw [ht']
    refine ⟨(hndK H).comp K₁, m, i, v, en, rfl, hKo, (hTin m i hm) ▸ hT, hrm, ρa, ρk, ga, gk,
      hcak, hg, hA, hu, fun ls'' he => ⟨fun k' hk' w y₁ z hB hcz => ?_, fun hq' => ?_⟩⟩
    · rw [Kont.plug_comp]
      exact hcontIH M' k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w y₁ z hB hcz)
    · intro P hP
      show P k ls'' (((hndK H).comp K₁).dead.plug _) (ρk, gk)
      rw [dead_comp, dead_hndK]
      exact (hcont ls'' he).2 hq' P hP

/-- **A handler at `erwpX`** (`[handle]`): `erwpX_handle_le` at `N = n`. -/
theorem erwpX_handle {Φ : LocFam} (hΦ : Φ.Down) (Tin Tout : OpTabX) (hTinD : Tin.Down)
    (hTout : Tout.Down) (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i)
    (qs hr hs : Val) (Qin Qout : PostX) (hQout : Qout.Down)
    (hlin : ∀ i en, Tin n₀ i = some en → en.q = .lin ∧ en.remask = false)
    (hq : ∀ i en, Tin n₀ i = some en → capTag qs.1 i.toNat = en.q.tag)
    (hret : ∀ M C k ls v x, Qin C k ls v x →
      erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout k ls (.app (.val hr) (.val v)) x)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      ∀ M k ls v (κ : Val) x,
        sepX (en.PA k ls v) (KapRelX (ℍ := ℍ) Φ M (opTableX Tout) Qout en k ls κ) x →
        erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) x) :
    ∀ n M ls e x, erwpX (ℍ := ℍ) Φ M (opTableX Tin) Qin n ls e x →
      erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) x :=
  fun n => erwpX_handle_le hΦ n Tin Tout hTinD hTout n₀ hTin qs hr hs Qin Qout hQout hlin hq
    (fun M C k _ => hret M C k)
    (fun i en hT => by
      obtain ⟨c, hc, h₁⟩ := hop i en hT
      exact ⟨c, hc, fun M k _ => h₁ M k⟩) n le_rfl

end BoCa.Fig16.LogRel.Core.Chain.SI

end
