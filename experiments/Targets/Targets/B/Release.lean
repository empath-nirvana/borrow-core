import Targets.Base.RunProps
import Targets.Base.Machine

/-!
# System B — release, as lemmas about runs (RESTRUCTURE §2.4; finding #2)

**`ReleasedOnceAll` is a tautology about runs**, not a guarantee.  It assumes its conclusion:
`NoReuse` gives at-most-once and `Final`'s empty memory gives at-least-once, so it holds at every
typing system (`releasedOnceAll`), and `ReleasedOnceOfSound` uses neither of its premises
`SafeRuns`, `Terminates`.  It is kept as a lemma about runs.  The guarantee is B4 (a complete run
at a data answer ends with the memory empty: at-least-once) with B5 (`ReleasedOnceReuse`,
`Targets/B/Guarantees.lean`: at-most-once on runs that reuse locations, every run the image of a
bump run).  `releasedOnce_of_ends` gives B5's `ReleasedOnce` of the bump run, and `bump_follows` builds the
bump run from a complete run, given the step-for-step simulation.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- D9's machine lemma, as stated: on every complete run that reuses no location, every cell is
released once.  Its premises `SafeRuns` and `Terminates` are unused (`releasedOnceOfSound`): the
conclusion is the occupancy argument of `releasedOnce_of_ends`, a lemma about runs. -/
def ReleasedOnceOfSound : Prop :=
  ∀ (P : Platform) (A : VTy) (e : Expr), SafeRuns (ℍ := ℍ) P A e → Terminates (ℍ := ℍ) P A e →
    ∀ cs, PRun (ℍ := ℍ) P (init P e :: cs) → NoReuse (init P e :: cs) →
      (∀ c, (init P e :: cs).getLast? = some c → Final P A c) → ReleasedOnce (init P e :: cs)

/-- **A tautology about runs** (finding #2), not a guarantee and not in done: on every complete run
that reuses no location, of every program T1 covers, every cell is released once.  `NoReuse` gives
at-most-once and `Final`'s empty memory at-least-once, so it holds at every typing system
(`releasedOnceAll`).  The guarantee is B4 with B5 (`ReleasedOnceReuse`). -/
def ReleasedOnceAll (J : TypingJ) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet (ℍ := ℍ) Γ γ →
    ∀ cs, PRun (ℍ := ℍ) P (init P (substAll γ e) :: cs) →
      NoReuse (init P (substAll γ e) :: cs) →
      (∀ c, (init P (substAll γ e) :: cs).getLast? = some c → Final P A c) →
      ReleasedOnce (init P (substAll γ e) :: cs)


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)

section Occupancy
variable {P : Platform} (cs : List (Conf P)) (ℓ : Loc)

/-- `ℓ` is occupied at the run's `k`-th configuration. -/
def Occ (k : Nat) : Prop := ∃ c, cs[k]? = some c ∧ (c.μ ℓ).isSome

/-- `ℓ` is vacant at the run's `k`-th configuration. -/
def Vac (k : Nat) : Prop := ∃ c, cs[k]? = some c ∧ c.μ ℓ = none

variable {cs ℓ}

theorem not_occ_vac {k : Nat} (h₁ : Occ cs ℓ k) (h₂ : Vac cs ℓ k) : False := by
  obtain ⟨c, hc, hs⟩ := h₁
  obtain ⟨c', hc', hn⟩ := h₂
  rw [hc] at hc'; cases hc'; simp [hn] at hs

theorem getElem?_pred {k : Nat} {c : Conf P} (h : cs[k + 1]? = some c) :
    ∃ c', cs[k]? = some c' := by
  have hk : k + 1 < cs.length := (List.getElem?_eq_some_iff.mp h).1
  exact ⟨cs[k], List.getElem?_eq_getElem (by omega)⟩

/-- Between a vacancy and a later occupancy, an allocation. -/
theorem rise_between {a : Nat} : ∀ {b : Nat}, Vac cs ℓ a → Occ cs ℓ b → a ≤ b →
    ∃ k, a ≤ k ∧ k < b ∧ Allocated cs k ℓ
  | 0, ha, hb, hab => by
      obtain rfl : a = 0 := by omega
      exact (not_occ_vac hb ha).elim
  | b + 1, ha, hb, hab => by
      by_cases he : a = b + 1
      · subst he; exact (not_occ_vac hb ha).elim
      obtain ⟨c', hc', hs⟩ := hb
      obtain ⟨c, hc⟩ := getElem?_pred hc'
      cases hcb : c.μ ℓ with
      | none => exact ⟨b, by omega, by omega, c, c', hc, hc', hcb, hs⟩
      | some v =>
          obtain ⟨k, h₁, h₂, h₃⟩ := rise_between ha ⟨c, hc, by simp [hcb]⟩ (by omega)
          exact ⟨k, h₁, by omega, h₃⟩

/-- Between an occupancy and a later vacancy, a release. -/
theorem fall_between {a : Nat} : ∀ {b : Nat}, Occ cs ℓ a → Vac cs ℓ b → a ≤ b →
    ∃ j, a ≤ j ∧ j < b ∧ Released cs j ℓ
  | 0, ha, hb, hab => by
      obtain rfl : a = 0 := by omega
      exact (not_occ_vac ha hb).elim
  | b + 1, ha, hb, hab => by
      by_cases he : a = b + 1
      · subst he; exact (not_occ_vac ha hb).elim
      obtain ⟨c', hc', hn⟩ := hb
      obtain ⟨c, hc⟩ := getElem?_pred hc'
      cases hcb : c.μ ℓ with
      | none =>
          obtain ⟨j, h₁, h₂, h₃⟩ := fall_between ha ⟨c, hc, hcb⟩ (by omega)
          exact ⟨j, h₁, by omega, h₃⟩
      | some v => exact ⟨b, by omega, by omega, c, c', hc, hc', by simp [hcb], hn⟩

end Occupancy

/-- **Exactly-once release** on a run vacant everywhere at both ends that reuses no location. -/
theorem releasedOnce_of_ends {P : Platform} {cs : List (Conf P)}
    (h₀ : ∀ c, cs[0]? = some c → ∀ ℓ, c.μ ℓ = none)
    (hN : ∀ c, cs.getLast? = some c → ∀ ℓ, c.μ ℓ = none) (hR : NoReuse cs) :
    ReleasedOnce cs := by
  refine ⟨fun ℓ k hk => ?_, fun ℓ j hj => ?_⟩
  · obtain ⟨c, c', hc, hc', -, hs⟩ := hk
    have hlen : k + 1 < cs.length := (List.getElem?_eq_some_iff.mp hc').1
    have hlast : cs[cs.length - 1]? = cs.getLast? := by
      rw [List.getLast?_eq_getElem?]
    obtain ⟨d, hd⟩ : ∃ d, cs.getLast? = some d := by
      cases h : cs.getLast? with
      | none => simp at h; subst h; simp at hlen
      | some d => exact ⟨d, rfl⟩
    obtain ⟨j, -, -, hj⟩ := fall_between (cs := cs) (ℓ := ℓ) (a := k + 1) (b := cs.length - 1)
      ⟨c', hc', hs⟩ ⟨d, by rw [hlast, hd], hN d hd ℓ⟩ (by omega)
    refine ⟨j, hj, fun j' hj' => ?_⟩
    by_contra hne
    have key : ∀ {j₁ j₂ : Nat}, j₁ < j₂ → Released cs j₁ ℓ → Released cs j₂ ℓ → False := by
      intro j₁ j₂ hlt h₁ h₂
      obtain ⟨-, e₁, -, he₁, -, hn₁⟩ := id h₁
      obtain ⟨e₂, -, he₂, -, hs₂, -⟩ := id h₂
      obtain ⟨k', hk₁, hk₂, hk⟩ := rise_between (cs := cs) (ℓ := ℓ) ⟨e₁, he₁, hn₁⟩ ⟨e₂, he₂, hs₂⟩
        (by omega)
      exact hR j₁ k' ℓ (by omega) h₁ hk
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key h hj' hj
    · exact key h hj hj'
  · obtain ⟨c, -, hc, -, hs, -⟩ := hj
    obtain ⟨c₀, hc₀⟩ : ∃ c₀, cs[0]? = some c₀ := by
      have : j < cs.length := (List.getElem?_eq_some_iff.mp hc).1
      exact ⟨cs[0], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨k, -, hk, hA⟩ := rise_between (cs := cs) (ℓ := ℓ) (a := 0) ⟨c₀, hc₀, h₀ c₀ hc₀ ℓ⟩
      ⟨c, hc, hs⟩ (Nat.zero_le _)
    exact ⟨k, hk, hA⟩

theorem init_vacant {P : Platform} (e : Expr) (cs : List (Conf P)) :
    ∀ c, (init P e :: cs)[0]? = some c → ∀ ℓ, c.μ ℓ = none := by
  intro c hc ℓ
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
  subst hc; rfl

theorem final_vacant {P : Platform} {A : VTy} {cs : List (Conf P)}
    (hF : ∀ c, cs.getLast? = some c → Final P A c) :
    ∀ c, cs.getLast? = some c → ∀ ℓ, c.μ ℓ = none := by
  intro c hc ℓ
  obtain ⟨-, -, -, hμ⟩ := hF c hc
  rw [hμ]; rfl

/-- **`ReleasedOnceOfSound`** (D9's machine lemma). -/
theorem releasedOnceOfSound : ReleasedOnceOfSound (ℍ := ℍ) := by
  intro P A e _ _ cs _ hR hF
  exact releasedOnce_of_ends (init_vacant e cs) (final_vacant hF) hR

/-- **`ReleasedOnceAll J`**, at every typing system: a tautology about runs. -/
theorem releasedOnceAll (J : TypingJ) : ReleasedOnceAll (ℍ := ℍ) J := by
  intro P _ Γ γ S A e _ _ _ _ cs _ hR hF
  exact releasedOnce_of_ends (init_vacant _ cs) (final_vacant hF) hR

end Targets

/-! ## The bump run follows a complete run (RESTRUCTURE §2.4)

B3's progress at the bump run: wherever a complete run of a safe program steps, the bump run from the
same start is not stuck, and `BumpSim` makes its step the given step's preimage, allocating only
locations that no earlier configuration of it names.  So the bump run follows the given run to its
end, with the same length, and ends `Final` where the given run does.  `releasedOnceReuse_of_bumpSim`
(`Targets/B/Routes.lean`) closes B5 from this with `releasedOnce_of_ends`. -/

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Step1 no_step_val)

/-- The locations a term mentions, as a list. -/
def locsOf : Expr → List Loc
  | .loc ℓ => [ℓ]
  | .var _ => []
  | .unit => []
  | .prim _ => []
  | .pair a b => locsOf a ++ locsOf b
  | .seq a b => locsOf a ++ locsOf b
  | .letpair a b => locsOf a ++ locsOf b
  | .app a b => locsOf a ++ locsOf b
  | .inj₁ a => locsOf a
  | .inj₂ a => locsOf a
  | .lam a => locsOf a
  | .case a b c => locsOf a ++ locsOf b ++ locsOf c

theorem mem_locsOf {ℓ : Loc} {e : Expr} (h : e.MentionsLoc ℓ) : ℓ ∈ locsOf e := by
  induction e with
  | loc ℓ' => simp only [Expr.MentionsLoc] at h; simp [locsOf, h]
  | var _ | unit | prim _ => exact h.elim
  | pair a b iha ihb | seq a b iha ihb | letpair a b iha ihb | app a b iha ihb =>
    rcases h with h | h
    · exact List.mem_append_left _ (iha h)
    · exact List.mem_append_right _ (ihb h)
  | inj₁ a ih | inj₂ a ih | lam a ih => exact ih h
  | case a b c iha ihb ihc =>
    rcases h with h | h | h
    · exact List.mem_append_left _ (List.mem_append_left _ (iha h))
    · exact List.mem_append_left _ (List.mem_append_right _ (ihb h))
    · exact List.mem_append_right _ (ihc h)

/-- The names of a configuration whose heap's domain lies in `d`. -/
def namedList (μ : Heap) (e : Expr) (d : List Loc) : List Loc :=
  d ++ locsOf e ++ d.flatMap (fun m => match μ m with | some v => locsOf v.1 | none => [])

theorem mem_namedList {μ : Heap} {e : Expr} {d : List Loc} (hd : ∀ l, μ l ≠ none → l ∈ d)
    {ℓ : Loc} (h : Named μ e ℓ) : ℓ ∈ namedList μ e d := by
  rcases h with h | h | ⟨m, v, hm, hv⟩
  · have hne : μ ℓ ≠ none := by intro h'; simp [h'] at h
    exact List.mem_append_left _ (List.mem_append_left _ (hd ℓ hne))
  · exact List.mem_append_left _ (List.mem_append_right _ (mem_locsOf h))
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨m, hd m (by simp [hm]), ?_⟩)
    simp only [hm]
    exact mem_locsOf hv

/-- A head step keeps the heap's domain finite. -/
theorem finDom_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') :
    FinDom μ → FinDom μ' := by
  rintro ⟨d, hd⟩
  cases h with
  | alloc v ℓ _ =>
    refine ⟨ℓ :: d, fun k hk => ?_⟩
    by_cases hkl : k = ℓ
    · simp [hkl]
    · exact List.mem_cons_of_mem _ (hd k (by simpa [Heap.upd, hkl] using hk))
  | free ℓ v _ =>
    refine ⟨d, fun k hk => hd k ?_⟩
    by_cases hkl : k = ℓ
    · simp [Heap.del, hkl] at hk
    · simpa [Heap.del, hkl] using hk
  | store ℓ v w _ =>
    refine ⟨ℓ :: d, fun k hk => ?_⟩
    by_cases hkl : k = ℓ
    · simp [hkl]
    · exact List.mem_cons_of_mem _ (hd k (by simpa [Heap.upd, hkl] using hk))
  | tab c f ℓ _ =>
    refine ⟨(List.range (arrLen c).toNat).map (ℓ + ·) ++ d, fun k hk => ?_⟩
    by_cases hkl : ℓ ≤ k ∧ k < ℓ + (arrLen c).toNat
    · obtain ⟨h₁, h₂⟩ := hkl
      exact List.mem_append_left _ (List.mem_map.mpr
        ⟨k - ℓ, List.mem_range.mpr (Nat.sub_lt_left_of_lt_add h₁ h₂), Nat.add_sub_cancel' h₁⟩)
    · exact List.mem_append_right _ (hd k (by simpa [Heap.fill, hkl] using hk))
  | _ => exact ⟨d, hd⟩

/-- A step under a platform keeps the heap's domain finite. -/
theorem finDom_pstep {P : Platform} {c c' : Conf P} (h : PStep (ℍ := ℍ) P c c')
    (hf : FinDom c.μ) : FinDom c'.μ := by
  cases h with
  | mach hs => obtain ⟨_, _, _, -, -, hh⟩ := hs; exact finDom_head hh hf
  | plat _ _ _ => exact hf

/-- A configuration at a value takes no step. -/
theorem not_pstep_of_val {P : Platform} {c c' : Conf P} {w : Val} (h : c.e = w.1) :
    ¬ PStep (ℍ := ℍ) P c c' := by
  intro hs
  cases hs with
  | mach hs =>
    simp only at h
    rw [h] at hs
    exact no_step_val hs
  | plat _ _ _ =>
    simp only at h
    exact plug_perform_ne_val _ _ _ h

/-- A data value mentions no location. -/
theorem noLoc_of_dataVal {A : VTy} {v : Val} (h : DataVal A v) : ∀ ℓ, ¬ v.1.MentionsLoc ℓ := by
  induction h with
  | unit => intro ℓ h; exact h
  | int hi => intro ℓ h; obtain ⟨c, hc⟩ := hi.val; rw [hc] at h; exact h
  | pair _ _ ih₁ ih₂ => intro ℓ h; rcases h with h | h; exacts [ih₁ ℓ h, ih₂ ℓ h]
  | inj₁ _ ih => exact ih
  | inj₂ _ ih => exact ih
  | roll _ ih => exact ih

theorem noLoc_of_mapLoc {g : Loc → Loc} {e : Expr} (h : ∀ ℓ, ¬ (e.mapLoc g).MentionsLoc ℓ) :
    ∀ ℓ, ¬ e.MentionsLoc ℓ := by
  induction e with
  | loc ℓ' => exact absurd rfl (h (g ℓ'))
  | var _ | unit | prim _ => intro ℓ h'; exact h'
  | pair a b iha ihb | seq a b iha ihb | letpair a b iha ihb | app a b iha ihb =>
    intro ℓ h'
    rcases h' with h' | h'
    · exact iha (fun m hm => h m (Or.inl hm)) ℓ h'
    · exact ihb (fun m hm => h m (Or.inr hm)) ℓ h'
  | inj₁ a ih | inj₂ a ih | lam a ih => exact ih h
  | case a b c iha ihb ihc =>
    intro ℓ h'
    rcases h' with h' | h' | h'
    · exact iha (fun m hm => h m (Or.inl hm)) ℓ h'
    · exact ihb (fun m hm => h m (Or.inr (Or.inl hm))) ℓ h'
    · exact ihc (fun m hm => h m (Or.inr (Or.inr hm))) ℓ h'

theorem mapLoc_of_noLoc {g : Loc → Loc} {e : Expr} (h : ∀ ℓ, ¬ e.MentionsLoc ℓ) :
    e.mapLoc g = e := by
  induction e with
  | loc ℓ' => exact absurd rfl (h ℓ')
  | var _ | unit | prim _ => rfl
  | pair a b iha ihb | seq a b iha ihb | letpair a b iha ihb | app a b iha ihb =>
    simp only [Expr.mapLoc]
    rw [iha (fun m hm => h m (Or.inl hm)), ihb (fun m hm => h m (Or.inr hm))]
  | inj₁ a ih | inj₂ a ih | lam a ih => simp only [Expr.mapLoc]; rw [ih h]
  | case a b c iha ihb ihc =>
    simp only [Expr.mapLoc]
    rw [iha (fun m hm => h m (Or.inl hm)), ihb (fun m hm => h m (Or.inr (Or.inl hm))),
      ihc (fun m hm => h m (Or.inr (Or.inr hm)))]

theorem mapLoc_id (e : Expr) : e.mapLoc id = e := by
  induction e <;> simp_all [Expr.mapLoc]

theorem push_emptyMem (g : Loc → Loc) : Heap.push g Adequacy.emptyMem = Adequacy.emptyMem := by
  funext ℓ'
  simp [Heap.push, Adequacy.emptyMem]

theorem push_isSome {g : Loc → Loc} {μ : Heap} {ℓ : Loc} (h : (μ ℓ).isSome) :
    (Heap.push g μ (g ℓ)).isSome := by
  have hex : ∃ ℓ₀, g ℓ₀ = g ℓ ∧ (μ ℓ₀).isSome := ⟨ℓ, rfl, h⟩
  simp only [Heap.push, dif_pos hex, Option.isSome_map]
  exact (Classical.choose_spec hex).2

/-- `Final` transfers back along a relation: a data value mentions no location, and a heap pushed
to the empty memory is empty. -/
theorem final_of_relAt {P : Platform} {A : VTy} {g : Loc → Loc} {cA cB : Conf P}
    (hR : RelAt g cA cB) (hF : Final P A cA) : Final P A cB := by
  obtain ⟨-, he, hμ, -⟩ := hR
  obtain ⟨v, hv, hd, hm⟩ := hF
  have hmap : cB.e.mapLoc g = v.1 := he.symm.trans hv
  have hnl : ∀ ℓ, ¬ cB.e.MentionsLoc ℓ := noLoc_of_mapLoc (hmap ▸ noLoc_of_dataVal hd)
  refine ⟨v, (mapLoc_of_noLoc hnl).symm.trans hmap, hd, ?_⟩
  funext ℓ
  cases hc : cB.μ ℓ with
  | none => rfl
  | some x =>
    have hs := push_isSome (g := g) (μ := cB.μ) (ℓ := ℓ) (by simp [hc])
    rw [← hμ, hm] at hs
    simp [Adequacy.emptyMem] at hs

theorem relAt_init {P : Platform} (e : Expr) : RelAt id (init P e) (init P e) :=
  ⟨Set.injOn_id _, (mapLoc_id e).symm, (push_emptyMem id).symm, rfl⟩

theorem named_init {P : Platform} {e : Expr} {ℓ : Loc} (h : Named (init P e).μ (init P e).e ℓ) :
    ℓ ∈ locsOf e := by
  rcases h with h | h | ⟨m, v, hm, -⟩
  · simp [init, Adequacy.emptyMem] at h
  · exact mem_locsOf h
  · simp [init, Adequacy.emptyMem] at hm

/-- A bump run reuses nothing. -/
theorem noReuse_of_bump {P : Platform} {cs : List (Conf P)} (h : Bump cs) : NoReuse cs := by
  intro j k ℓ hjk hR hA
  obtain ⟨c, -, hc, -, hs, -⟩ := hR
  exact h k ℓ hA j c hjk.le hc (Or.inl hs)

/-- **The bump run follows a complete run.**  From configurations related by `g`, where the bump
side is reachable from the start, has a finite heap and names nothing outside `Y`, the bump run
takes a step wherever the given run does (`SafeRuns`'s progress, and `BumpSim`), allocates outside
`Y` and outside every name of its earlier configurations, and ends `Final` where the given run
does. -/
theorem bump_follows (hS : BumpSim (ℍ := ℍ)) {P : Platform} {A : VTy} {e : Expr}
    (hsafe : SafeRuns (ℍ := ℍ) P A e) :
    ∀ (cs : List (Conf P)) (cA cB : Conf P) (g : Loc → Loc) (Y : Finset Loc),
      PRun (ℍ := ℍ) P (cA :: cs) → (∀ c, (cA :: cs).getLast? = some c → Final P A c) →
      RelAt g cA cB → BlocksAffine g cB.μ cB.e → PSteps (ℍ := ℍ) P (init P e) cB →
      FinDom cB.μ → (∀ ℓ, Named cB.μ cB.e ℓ → ℓ ∈ Y) →
      ∃ (cs' : List (Conf P)) (gs : ℕ → Loc → Loc), cs'.length = cs.length ∧
        PRun (ℍ := ℍ) P (cB :: cs') ∧
        (∀ k ℓ, Allocated (cB :: cs') k ℓ →
          ℓ ∉ Y ∧ ∀ j c, j ≤ k → (cB :: cs')[j]? = some c → ¬ Named c.μ c.e ℓ) ∧
        (∀ c, (cB :: cs').getLast? = some c → Final P A c) ∧
        ∀ k (cA' cB' : Conf P), (cA :: cs)[k]? = some cA' → (cB :: cs')[k]? = some cB' →
          RelAt (gs k) cA' cB' := by
  intro cs
  induction cs with
  | nil =>
    intro cA cB g Y _ hF hR _ _ _ _
    refine ⟨[], fun _ => g, rfl, .one cB, ?_, ?_, ?_⟩
    · rintro k ℓ ⟨c, c', -, hc', -⟩
      simp at hc'
    · intro c hc
      simp only [List.getLast?_singleton, Option.some.injEq] at hc
      subst hc
      exact final_of_relAt hR (hF cA (by simp))
    · intro k cA' cB' h₁ h₂
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
        subst h₁; subst h₂; exact hR
      | succ k => simp at h₁
  | cons cA₁ cs₁ ih =>
    intro cA cB g Y hrun hF hR hB hreach hfin hY
    cases hrun with
    | cons hstepA hrun₁ =>
      have hprog : ∃ cB'', PStep (ℍ := ℍ) P cB cB'' := by
        rcases hsafe cB hreach with ⟨v, hv, -, -⟩ | h
        · exact absurd hstepA (not_pstep_of_val (w := v.mapLoc g) (by rw [hR.2.1, hv]; rfl))
        · exact h
      obtain ⟨cB₁, g₁, hstepB, hfresh, -, hR₁, hB₁⟩ := hS P Y g cA cA₁ cB hR hB hstepA hprog
      obtain ⟨d₁, hd₁⟩ := finDom_pstep hstepB hfin
      obtain ⟨cs₁', gs₁, hlen, hrun', hbump, hF', hrel⟩ :=
        ih cA₁ cB₁ g₁ (Y ∪ (namedList cB₁.μ cB₁.e d₁).toFinset) hrun₁
          (fun c hc => hF c (by simpa using hc)) hR₁ hB₁ (hreach.tail hstepB) ⟨d₁, hd₁⟩
          (fun ℓ hn => Finset.mem_union_right _ (List.mem_toFinset.mpr (mem_namedList hd₁ hn)))
      refine ⟨cB₁ :: cs₁', fun k => Nat.casesOn k g gs₁, by simp [hlen], .cons hstepB hrun', ?_,
        fun c hc => hF' c (by simpa using hc), ?_⟩
      · intro k ℓ hA
        cases k with
        | zero =>
          obtain ⟨c, c', hc, hc', hn, hs⟩ := hA
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hc hc'
          subst hc; subst hc'
          obtain ⟨hnN, hnY⟩ := hfresh ℓ hn hs
          refine ⟨hnY, fun j c hj hc => ?_⟩
          obtain rfl : j = 0 := by omega
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
          subst hc; exact hnN
        | succ k =>
          have hA' : Allocated (cB₁ :: cs₁') k ℓ := by
            obtain ⟨c, c', hc, hc', hn, hs⟩ := hA
            exact ⟨c, c', by simpa using hc, by simpa using hc', hn, hs⟩
          obtain ⟨hnY₁, hnN⟩ := hbump k ℓ hA'
          refine ⟨fun h => hnY₁ (Finset.mem_union_left _ h), fun j c hj hc => ?_⟩
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
            subst hc; exact fun hn => hnY₁ (Finset.mem_union_left _ (hY ℓ hn))
          | succ j => exact hnN j c (by omega) (by simpa using hc)
      · intro k cA' cB' h₁ h₂
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
          subst h₁; subst h₂; exact hR
        | succ k => exact hrel k cA' cB' (by simpa using h₁) (by simpa using h₂)

end Targets

end
