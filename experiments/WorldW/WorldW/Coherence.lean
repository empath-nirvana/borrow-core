import WorldW.Refold

/-!
# WorldW — two closures of one resource (F-CLOSE's invariant)

**World: the W-draft.** About our `Close` (DESIGN §1.2, §2), not about OQ-9 (a).

Two chains `Close τ π π₁` and `Close τ π π₂` are walked together. At every point both states are
refolds of one unfolded resource `U`, by refold lists of one shape (`close_pair`). The shape list
after the whole of `τ` is a function of `τ` alone (`pendAfter`): an anti entry appends its
refold, and a 6.65 entry at the same place removes it.

Each step of the two chains is one of:
* a 6.64 or 6.65 step away from the pending places, which both chains lift to the same step on `U`
  (`refolds_replace`);
* a 6.65 step at a pending place, which undoes that refold in both chains (`refolds_unfold`);
* an anti step, which appends a refold (each chain its own split);
* a 6.150 step, which both chains lift to `U ⊟ image` (`refolds_sub`; the pin is spent here);
* a marker, which does nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The pending refolds as a function of the list -/

/-- One entry's effect on the pending refolds' shapes. -/
def pendStep (S : List Shape) : OEnt → List Shape
  | .anti l _ β _ _ P => S ++ [⟨l, β, P⟩]
  | .mut l _ _ _ => S.filter (fun s => s.l != l)
  | _ => S

/-- The pending refolds' shapes after closing a list. -/
def pendAfter : List Shape → List OEnt → List Shape
  | S, [] => S
  | S, e :: τ => pendAfter (pendStep S e) τ

/-- Every pending refold's split meets its pin against the entries still to close. -/
def PinsOK (A : List Fold) (τ : List OEnt) : Prop := ∀ f ∈ A, AntiPin f.l τ f.ρP

theorem antiPin_tail {l : BoCa.Loc} {e : OEnt} {τ : List OEnt} {ρP : WRes}
    (h : AntiPin l (e :: τ) ρP) (he : e.isMutAt l = false) : AntiPin l τ ρP := by
  intro e' he' β' hβ' m ψ hm
  refine h e' ?_ β' hβ' m ψ hm
  rw [List.takeWhile_cons, if_pos (by simp [he])]
  exact List.mem_cons_of_mem _ he'

theorem pinsOK_tail {A : List Fold} {e : OEnt} {τ : List OEnt} (h : PinsOK A (e :: τ))
    (he : ∀ f ∈ A, e.isMutAt f.l = false) : PinsOK A τ :=
  fun f hf => antiPin_tail (h f hf) (he f hf)

/-- The pin read at the head entry: a reborrow closed next is outside every pending split. -/
theorem antiPin_head {l : BoCa.Loc} {e : OEnt} {τ : List OEnt} {ρP : WRes}
    (h : AntiPin l (e :: τ) ρP) (he : e.isMutAt l = false) {β : Life}
    (hβ : e.rebLife? = some β) : ∀ m ψ, ρP.get m = some ψ → ¬ CellU.ImmAt ψ β :=
  h e (by rw [List.takeWhile_cons, if_pos (by simp [he])]; exact List.mem_cons_self) β hβ

theorem places_eq {A₁ A₂ : List Fold} (h : A₁.map Fold.shape = A₂.map Fold.shape) :
    A₁.map Fold.l = A₂.map Fold.l := by
  have e : ∀ A : List Fold, A.map Fold.l = (A.map Fold.shape).map Shape.l := by
    intro A; rw [List.map_map]; rfl
  rw [e, e, h]

/-! ### Refolds away from their places -/

/-- Away from every refold's place, a non-`imm` cell of the start stays at the top or is taken
into a split, and an empty place stays empty. -/
theorem refolds_persist : ∀ {A : List Fold} {y π : WRes} {m : BoCa.Loc}, Refolds y A π →
    (∀ g ∈ A, g.l ≠ m) →
    (y.get m = none → π.get m = none) ∧
    (∀ ψ, y.get m = some ψ → ψ.kind ≠ Kind.imm → π.get m = some ψ ∨ π.get m = none)
  | [], _, _, _, h, _ => by
      rw [refolds_nil_iff] at h; subst h
      exact ⟨id, fun ψ h _ => Or.inl h⟩
  | g :: A, y, π, m, h, hA => by
      obtain ⟨z, hg, hz⟩ := refolds_cons_iff.mp h
      obtain ⟨ih₁, ih₂⟩ := refolds_persist hz (fun g' hg' => hA g' (List.mem_cons_of_mem _ hg'))
      obtain ⟨w, hs, hw, Y, rest, hY, hy, hzr, -⟩ := hg
      have hgm : g.l ≠ m := hA g List.mem_cons_self
      have hzm : ∀ o, rest.get m = o → z.get m = o := fun o e => by
        rw [compS_get_right hzr (single_get_none _ (Ne.symm hgm)), e]
      refine ⟨fun hn => ih₁ (hzm none ?_), fun ψ hψ hk => ?_⟩
      · exact ((ResU.Comp.eq_none_iff hy m).mp hn).2
      · rcases ResU.Comp.get hy m with ⟨-, -, e⟩ | ⟨φ, e₁, e₂, e⟩ | ⟨φ, e₁, e₂, e⟩ |
            ⟨ψ₁, ψ₂, φ, e₁, e₂, e, hcc⟩
        · rw [hψ] at e; exact absurd e (by simp)
        · exact Or.inr (ih₁ (hzm none e₂))
        · rw [hψ] at e; cases Option.some.inj e
          exact ih₂ ψ (hzm _ e₂) hk
        · rw [hψ] at e; cases Option.some.inj e
          exact absurd (CellU.CompS.kind hcc) hk

/-- At a refold's place, the end holds that refold's `mut` cell or nothing. -/
theorem refolds_at_place {A : List Fold} {U π : WRes} (h : Refolds U A π) {f : Fold}
    (hf : f ∈ A) : π.get f.l = none ∨ ∃ ψ, π.get f.l = some ψ ∧ ψ.kind = Kind.mut := by
  obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hf
  have hnd := refolds_nodup h
  rw [List.map_append, List.map_cons, List.nodup_append] at hnd
  have h₂ : ∀ g ∈ A₂, g.l ≠ f.l := fun g hg e =>
    (List.nodup_cons.mp hnd.2.1).1 (e ▸ List.mem_map_of_mem (f := Fold.l) hg)
  obtain ⟨x, -, hx⟩ := refolds_append.mp h
  obtain ⟨y, hfy, hy⟩ := refolds_cons_iff.mp hx
  obtain ⟨v, hs, hw, hyl⟩ := closeEAnti_get_mut hfy
  obtain ⟨-, hp⟩ := refolds_persist hy h₂
  rcases hp _ hyl kind_mutOf_ne with e | e
  · exact Or.inr ⟨_, e, CellU.kind_mutOf _ _ _ _ _ _⟩
  · exact Or.inl e

/-- No refold sits at a place where the end holds a cell that is not `mut`. -/
theorem refolds_off_place {A : List Fold} {U π : WRes} (h : Refolds U A π) {m : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (hm : π.get m = some ψ) (hk : ψ.kind ≠ Kind.mut) :
    ∀ f ∈ A, f.l ≠ m := by
  rintro f hf rfl
  rcases refolds_at_place h hf with e | ⟨φ, e, hφ⟩
  · rw [hm] at e; exact absurd e (by simp)
  · rw [hm] at e; cases Option.some.inj e; exact hk hφ

/-! ### One step of two chains -/

theorem kind_immOf_ne_mut {s : LSet} {v : Val} {w : WRes} {h : w.InStratum s.join} :
    (CellU.immOf s v w h).kind ≠ Kind.mut := by
  rw [CellU.kind_immOf]; exact fun c => Kind.noConfusion c

/-- **One step of two chains over one list keeps the invariant.** -/
theorem close_step {e : OEnt} {τr : List OEnt} {π₁ π₂ π₁' π₂' U : WRes} {A₁ A₂ : List Fold}
    (h₁ : CloseE τr e π₁ π₁') (h₂ : CloseE τr e π₂ π₂') (hr₁ : Refolds U A₁ π₁)
    (hr₂ : Refolds U A₂ π₂) (hsh : A₁.map Fold.shape = A₂.map Fold.shape)
    (hp₁ : PinsOK A₁ (e :: τr)) (hp₂ : PinsOK A₂ (e :: τr)) :
    ∃ U' A₁' A₂', Refolds U' A₁' π₁' ∧ Refolds U' A₂' π₂' ∧
      A₁'.map Fold.shape = pendStep (A₁.map Fold.shape) e ∧
      A₂'.map Fold.shape = pendStep (A₂.map Fold.shape) e ∧ PinsOK A₁' τr ∧ PinsOK A₂' τr := by
  classical
  have hpl := places_eq hsh
  cases e with
  | imm r =>
      obtain ⟨p, α⟩ := r
      obtain ⟨hh₁, X₁, hg₁, hX₁, hc₁, hv₁⟩ := h₁
      obtain ⟨hh₂, X₂, hg₂, hX₂, hc₂, hv₂⟩ := h₂
      cases ResU.CompS.functional hX₂ hX₁
      have hXm := compS_single_nonimm_get hX₁ (kind_ownOf_ne p.v)
      obtain ⟨U₁, -, hU₁, hr₁'⟩ :=
        refolds_replace hXm (refolds_off_place hr₁ hg₁ kind_immOf_ne_mut) hr₁ hg₁ hc₁ hv₁
      obtain ⟨U₂, -, hU₂, hr₂'⟩ :=
        refolds_replace hXm (refolds_off_place hr₂ hg₂ kind_immOf_ne_mut) hr₂ hg₂ hc₂ hv₂
      cases ResU.CompS.functional hU₂ hU₁
      exact ⟨U₁, A₁, A₂, hr₁', hr₂', rfl, rfl, pinsOK_tail hp₁ (fun _ _ => rfl),
        pinsOK_tail hp₂ (fun _ _ => rfl)⟩
  | «mut» l α T δ =>
      obtain ⟨v₁, χ₁, k₁, Q₁, hw₁, X₁, hg₁, hX₁, hc₁, hv₁⟩ := h₁
      obtain ⟨v₂, χ₂, k₂, Q₂, hw₂, X₂, hg₂, hX₂, hc₂, hv₂⟩ := h₂
      by_cases hmem : ∃ f ∈ A₁, f.l = l
      · -- the 6.65 step undoes the pending refold at `l`
        have hmem₂ : ∃ g ∈ A₂, g.l = l := by
          obtain ⟨f, hf, hfl⟩ := hmem
          have : l ∈ A₂.map Fold.l := hpl ▸ (hfl ▸ List.mem_map_of_mem (f := Fold.l) hf)
          obtain ⟨g, hg, hgl⟩ := List.mem_map.mp this
          exact ⟨g, hg, hgl⟩
        refine ⟨U, A₁.filter (fun g => g.l != l), A₂.filter (fun g => g.l != l),
          refolds_unfold hr₁ hmem hg₁ hX₁ hc₁ hv₁, refolds_unfold hr₂ hmem₂ hg₂ hX₂ hc₂ hv₂,
          ?_, ?_, ?_, ?_⟩
        · show _ = (A₁.map Fold.shape).filter _
          rw [List.filter_map]; rfl
        · show _ = (A₂.map Fold.shape).filter _
          rw [List.filter_map]; rfl
        · refine pinsOK_tail (fun f hf => hp₁ f (List.mem_of_mem_filter hf)) (fun f hf => ?_)
          have := (List.mem_filter.mp hf).2
          simp only [bne_iff_ne, ne_eq] at this
          simp [OEnt.isMutAt, Ne.symm this]
        · refine pinsOK_tail (fun f hf => hp₂ f (List.mem_of_mem_filter hf)) (fun f hf => ?_)
          have := (List.mem_filter.mp hf).2
          simp only [bne_iff_ne, ne_eq] at this
          simp [OEnt.isMutAt, Ne.symm this]
      · -- the 6.65 step away from the pending places lifts to `U`
        have hA₁ : ∀ f ∈ A₁, f.l ≠ l := fun f hf e => hmem ⟨f, hf, e⟩
        have hA₂ : ∀ g ∈ A₂, g.l ≠ l := fun g hg e =>
          hmem (by
            have : l ∈ A₁.map Fold.l := hpl ▸ (e ▸ List.mem_map_of_mem (f := Fold.l) hg)
            obtain ⟨f, hf, hfl⟩ := List.mem_map.mp this
            exact ⟨f, hf, hfl⟩)
        obtain ⟨U₁, hU₁g, hU₁, hr₁'⟩ :=
          refolds_replace (compS_single_nonimm_get hX₁ (kind_ownOf_ne v₁)) hA₁ hr₁ hg₁ hc₁ hv₁
        obtain ⟨U₂, hU₂g, hU₂, hr₂'⟩ :=
          refolds_replace (compS_single_nonimm_get hX₂ (kind_ownOf_ne v₂)) hA₂ hr₂ hg₂ hc₂ hv₂
        have he := Option.some.inj (hU₁g.symm.trans hU₂g)
        obtain ⟨rfl, rfl, rfl⟩ := CellU.mutOf_inj he
        cases ResU.CompS.functional hX₂ hX₁
        cases ResU.CompS.functional hU₂ hU₁
        have hS : ∀ A : List Fold, (∀ f ∈ A, f.l ≠ l) →
            (A.map Fold.shape).filter (fun s => s.l != l) = A.map Fold.shape := by
          intro A hA
          refine List.filter_eq_self.mpr fun s hs => ?_
          obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hs
          simpa [Fold.shape] using hA f hf
        refine ⟨U₁, A₁, A₂, hr₁', hr₂', (hS A₁ hA₁).symm, (hS A₂ hA₂).symm, ?_, ?_⟩
        · exact pinsOK_tail hp₁ (fun f hf => by simp [OEnt.isMutAt, Ne.symm (hA₁ f hf)])
        · exact pinsOK_tail hp₂ (fun f hf => by simp [OEnt.isMutAt, Ne.symm (hA₂ f hf)])
  | anti l α β T δ P =>
      obtain ⟨ρP₁, hpin₁, ha₁⟩ := h₁
      obtain ⟨ρP₂, hpin₂, ha₂⟩ := h₂
      refine ⟨U, A₁ ++ [⟨l, β, P, ρP₁⟩], A₂ ++ [⟨l, β, P, ρP₂⟩],
        refolds_snoc hr₁ ha₁, refolds_snoc hr₂ ha₂, ?_, ?_, ?_, ?_⟩
      · simp [pendStep, Fold.shape]
      · simp [pendStep, Fold.shape]
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact antiPin_tail (hp₁ f hf) rfl
        · rw [List.mem_singleton] at hf; subst hf; exact hpin₁
      · intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact antiPin_tail (hp₂ f hf) rfl
        · rw [List.mem_singleton] at hf; subst hf; exact hpin₂
  | reb l₀ s w σR hs β χ =>
      obtain ⟨hreb, hle₁, hsk₁, hv₁⟩ := h₁
      obtain ⟨-, hle₂, hsk₂, hv₂⟩ := h₂
      have hex := ResU.reb_restrictDom_exclPart_empty hreb
      have himg := fun m ψ hm => reb_img_single (m := m) (ψ := ψ) hreb hm
      obtain ⟨U₁, hleU, hskU₁, hr₁'⟩ := refolds_sub hex himg
        (fun f hf => antiPin_head (hp₁ f hf) rfl rfl) hr₁ hle₁ hsk₁ hv₁
      obtain ⟨U₂, -, hskU₂, hr₂'⟩ := refolds_sub hex himg
        (fun f hf => antiPin_head (hp₂ f hf) rfl rfl) hr₂ hle₂ hsk₂ hv₂
      cases ResU.SubKeep.functional (subLe_of_le hleU) hskU₂ hskU₁
      exact ⟨U₁, A₁, A₂, hr₁', hr₂', rfl, rfl, pinsOK_tail hp₁ (fun _ _ => rfl),
        pinsOK_tail hp₂ (fun _ _ => rfl)⟩
  | hnd n h =>
      have e₁ : π₁' = π₁ := h₁
      have e₂ : π₂' = π₂ := h₂
      subst e₁ e₂
      exact ⟨U, A₁, A₂, hr₁, hr₂, rfl, rfl, pinsOK_tail hp₁ (fun _ _ => rfl),
        pinsOK_tail hp₂ (fun _ _ => rfl)⟩

theorem closePre_cons_inv {e : OEnt} {τ τ₂ : List OEnt} {π π' : WRes}
    (h : ClosePre (e :: τ) τ₂ π π') : ∃ π₁, CloseE (τ ++ τ₂) e π π₁ ∧ ClosePre τ τ₂ π₁ π' := by
  cases h with
  | cons h₁ h₂ => exact ⟨_, h₁, h₂⟩

theorem closePre_nil_inv {τ₂ : List OEnt} {π π' : WRes} (h : ClosePre [] τ₂ π π') : π' = π := by
  cases h; rfl

/-- **Two chains over one list keep the invariant to the end.** -/
theorem close_pair : ∀ {τ τ₂ : List OEnt} {π₁ π₁' : WRes}, ClosePre τ τ₂ π₁ π₁' →
    ∀ {π₂ π₂' U : WRes} {A₁ A₂ : List Fold}, ClosePre τ τ₂ π₂ π₂' →
    Refolds U A₁ π₁ → Refolds U A₂ π₂ → A₁.map Fold.shape = A₂.map Fold.shape →
    PinsOK A₁ (τ ++ τ₂) → PinsOK A₂ (τ ++ τ₂) →
    ∃ U' A₁' A₂', Refolds U' A₁' π₁' ∧ Refolds U' A₂' π₂' ∧
      A₁'.map Fold.shape = pendAfter (A₁.map Fold.shape) τ ∧
      A₂'.map Fold.shape = pendAfter (A₂.map Fold.shape) τ := by
  intro τ τ₂ π₁ π₁' h
  induction h with
  | nil τ₂ π =>
      intro π₂ π₂' U A₁ A₂ h₂ hr₁ hr₂ _ _ _
      rw [closePre_nil_inv h₂]
      exact ⟨U, A₁, A₂, hr₁, hr₂, rfl, rfl⟩
  | @cons e τ τ₂ π π₁ π' hstep _ ih =>
      intro π₂ π₂' U A₁ A₂ h₂ hr₁ hr₂ hsh hp₁ hp₂
      obtain ⟨π₂m, hstep₂, hrest₂⟩ := closePre_cons_inv h₂
      obtain ⟨Um, A₁m, A₂m, hr₁m, hr₂m, hs₁, hs₂, hp₁m, hp₂m⟩ :=
        close_step hstep hstep₂ hr₁ hr₂ hsh hp₁ hp₂
      obtain ⟨U', A₁', A₂', hr₁', hr₂', hs₁', hs₂'⟩ :=
        ih hrest₂ hr₁m hr₂m (by rw [hs₁, hs₂, hsh]) hp₁m hp₂m
      exact ⟨U', A₁', A₂', hr₁', hr₂', by rw [hs₁', hs₁]; rfl, by rw [hs₂', hs₂]; rfl⟩

/-! ### The pending places of a list -/

/-- `m` is the place of an anti entry of `τ` that no later 6.65 entry of `τ` at `m` unfolds. -/
def PendingAt (τ : List OEnt) (m : BoCa.Loc) : Prop :=
  ∃ i, ∃ hi : i < τ.length, ∃ α β T δ P, τ[i] = .anti m α β T δ P ∧
    ∀ e ∈ τ.drop (i + 1), e.isMutAt m = false

theorem pendAfter_keep : ∀ {τ : List OEnt} {S : List Shape} {s : Shape}, s ∈ S →
    (∀ e ∈ τ, e.isMutAt s.l = false) → s ∈ pendAfter S τ
  | [], _, _, hs, _ => hs
  | e :: τ, S, s, hs, hτ => by
      show s ∈ pendAfter (pendStep S e) τ
      refine pendAfter_keep ?_ (fun e' he' => hτ e' (List.mem_cons_of_mem _ he'))
      have he := hτ e List.mem_cons_self
      cases e with
      | anti l α β T δ P => exact List.mem_append_left _ hs
      | «mut» l α T δ =>
          refine List.mem_filter.mpr ⟨hs, ?_⟩
          simp only [OEnt.isMutAt, beq_eq_false_iff_ne, ne_eq] at he
          simpa using Ne.symm he
      | imm _ => exact hs
      | reb _ _ _ _ _ _ _ => exact hs
      | hnd _ _ => exact hs

/-- The refold of a pending anti entry is among the pending shapes. -/
theorem pendAfter_mem : ∀ {τ : List OEnt} {S : List Shape} (i : Nat) (hi : i < τ.length)
    {l : BoCa.Loc} {α β : Life} {T : VTy} {δ : LSub} {P : Val → SPropS BoCa.Loc Val β},
    τ[i] = .anti l α β T δ P → (∀ e ∈ τ.drop (i + 1), e.isMutAt l = false) →
    (⟨l, β, P⟩ : Shape) ∈ pendAfter S τ
  | [], _, i, hi, _, _, _, _, _, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | e :: τ, S, 0, _, l, α, β, T, δ, P, he, hτ => by
      simp only [List.getElem_cons_zero] at he
      subst he
      show (⟨l, β, P⟩ : Shape) ∈ pendAfter (pendStep S (.anti l α β T δ P)) τ
      exact pendAfter_keep (List.mem_append_right _ (List.mem_singleton_self _))
        (by simpa using hτ)
  | e :: τ, S, i + 1, hi, l, α, β, T, δ, P, he, hτ => by
      simp only [List.getElem_cons_succ] at he
      show (⟨l, β, P⟩ : Shape) ∈ pendAfter (pendStep S e) τ
      exact pendAfter_mem i (by simpa using hi) he (by simpa using hτ)

/-- A pending shape's place is a pending place of the list, or a place of the start never
unfolded. -/
theorem pendAfter_places : ∀ {τ : List OEnt} {S : List Shape} {m : BoCa.Loc},
    m ∈ (pendAfter S τ).map Shape.l →
    (m ∈ S.map Shape.l ∧ ∀ e ∈ τ, e.isMutAt m = false) ∨ PendingAt τ m
  | [], S, m, h => Or.inl ⟨h, fun _ h => absurd h List.not_mem_nil⟩
  | e :: τ, S, m, h => by
      rcases pendAfter_places (τ := τ) (S := pendStep S e) h with ⟨hm, hτ⟩ | ⟨i, hi, α, β, T, δ, P, he, hτ⟩
      · cases e with
        | anti l α β T δ P =>
            simp only [pendStep, List.map_append, List.map_cons, List.map_nil,
              List.mem_append, List.mem_singleton] at hm
            rcases hm with hm | rfl
            · exact Or.inl ⟨hm, fun e he => by
                rcases List.mem_cons.mp he with rfl | he
                · rfl
                · exact hτ e he⟩
            · exact Or.inr ⟨0, by simp, α, β, T, δ, P, rfl, by simpa using hτ⟩
        | «mut» l α T δ =>
            simp only [pendStep] at hm
            obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
            obtain ⟨hs, hsl⟩ := List.mem_filter.mp hs
            refine Or.inl ⟨List.mem_map_of_mem hs, fun e he => ?_⟩
            rcases List.mem_cons.mp he with rfl | he
            · simp only [bne_iff_ne, ne_eq] at hsl
              simp only [OEnt.isMutAt, beq_eq_false_iff_ne, ne_eq]
              exact Ne.symm hsl
            · exact hτ e he
        | imm _ =>
            exact Or.inl ⟨hm, fun e he => by
              rcases List.mem_cons.mp he with rfl | he
              · rfl
              · exact hτ e he⟩
        | reb _ _ _ _ _ _ _ =>
            exact Or.inl ⟨hm, fun e he => by
              rcases List.mem_cons.mp he with rfl | he
              · rfl
              · exact hτ e he⟩
        | hnd _ _ =>
            exact Or.inl ⟨hm, fun e he => by
              rcases List.mem_cons.mp he with rfl | he
              · rfl
              · exact hτ e he⟩
      · exact Or.inr ⟨i + 1, by simpa using hi, α, β, T, δ, P, by simpa using he,
          by simpa using hτ⟩

end WorldW

end
