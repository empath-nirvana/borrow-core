import Core.DivHandleLast
import Core.DivDrive

/-!
# Core — `[handle-last]`'s erasure laws  `[spec §51]`

The backend calls a `[handle-last]` work where its operation is performed:
`hnd H K[perform (n, (i, v))]` becomes `hnd H K[case (w v) {inl y → y | inr z → X}]`, the work
`w` run inside `K` and under the node (`directK`).  These are the laws that licence it, about the
machine's runs of the clause the rule writes (`lastClause`).

**The cell.**  The handled run allocates `κ`'s cell `ℓ` at `[op]` and frees it when `κ` is resumed
or cancelled; the direct run allocates none.  So the direct run is asked to leave one location
`ℓ` free at every memory it passes (`StepsOff`), and then runs as well beside `ℓ` holding `()`
(`StepsOff.upd`): no step reads, writes, frees or allocates a location it does not name or
choose, and `ℓ` is none of those.

**T-B1** (`last_resume_direct`): the work runs directly to `inl y`.  The handled run and the direct
run both reach `K₀[hnd H K[y]]`, at the memory the direct work run ends at.

**T-B1′** (`last_cancel_direct`): the work runs directly to `inr z`.  The handled run reaches
`K₀[(λ_. nf z) (ccatch K†[raise ⊥])]` at that memory: `K`'s cancel run (`kappaC_cancel`), its
handler frames dead and its finalisers kept, in the site's outer context, and then the exit.  The
direct run reaches its own `inr` arm there.  When `K`'s cancel run answers `()`, the handled run
reaches the exit `nf z` in `K₀` (`last_cancel_exit`).

**T-B2** (`last_perform_direct`): the work performs operations of names a predicate `P` holds of,
each answered in place by a handler in `K₀` (`WorkRun`): the two runs are matched segment by
segment.  Between performs the work's run is the direct run (`StepsOff`); at a perform, the outer
handler's answer is uniform in the continuation it captures (`WorkRun.op`'s `hans`), so it answers
both the handled run's continuation `ubind (N, D) [·]` and the direct run's `hnd H K[case [·] …]`
(`work_run_ctx`).  The direct run is the handled one when no name of `P` is `n` or has a handler
in `K`.  An outer tail clause (`tail_clause_answers`) and an outer `[handle-last]` clause whose
work resumes (`last_clause_answers`) answer in place (`answers_in_place`); the second is the
pipe-fusion case, and nests.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE hndVal ccatchE cancelVal
  kappaC clauseAt capTag)

/-! ### A location the run leaves free -/

theorem heap_upd_comm {μ : Heap} {ℓ ℓ' : Loc} (h : ℓ ≠ ℓ') (u u' : Val) :
    (μ.upd ℓ u).upd ℓ' u' = (μ.upd ℓ' u').upd ℓ u := by
  funext k
  by_cases h₁ : k = ℓ
  · subst h₁; simp [Heap.upd, h]
  · by_cases h₂ : k = ℓ'
    · subst h₂; simp [Heap.upd, h₁]
    · simp [Heap.upd, h₁, h₂]

theorem heap_del_upd {μ : Heap} {ℓ : Loc} (h : μ ℓ = none) (u : Val) : (μ.upd ℓ u).del ℓ = μ := by
  funext k
  by_cases h₁ : k = ℓ
  · subst h₁; simp [Heap.del, h]
  · simp [Heap.del, Heap.upd, h₁]

theorem heap_del_upd_comm {μ : Heap} {ℓ ℓ' : Loc} (h : ℓ ≠ ℓ') (u : Val) :
    (μ.del ℓ').upd ℓ u = (μ.upd ℓ u).del ℓ' := by
  funext k
  by_cases h₁ : k = ℓ
  · subst h₁; simp [Heap.del, Heap.upd, h]
  · by_cases h₂ : k = ℓ'
    · subst h₂; simp [Heap.del, Heap.upd, h₁]
    · simp [Heap.del, Heap.upd, h₁, h₂]

/-- **A head step beside a free location**: a step from a memory that does not hold `ℓ` to one
that does not hold it is a step beside `ℓ` holding any `u`. -/
theorem head_upd_off {μ μ' : Heap} {a a' : Expr} {ℓ : Loc} (u : Val) (h : Head (ℍ := ℍ) μ a μ' a')
    (h0 : μ ℓ = none) (h1 : μ' ℓ = none) : Head (ℍ := ℍ) (μ.upd ℓ u) a (μ'.upd ℓ u) a' := by
  cases h with
  | alloc v ℓ₀ hf =>
      have hne : ℓ ≠ ℓ₀ := fun he => by subst he; simp at h1
      rw [← heap_upd_comm hne]
      exact .alloc _ v ℓ₀ (by simp [Heap.upd, Ne.symm hne, hf])
  | free ℓ₀ v hv =>
      have hne : ℓ ≠ ℓ₀ := fun he => by subst he; rw [h0] at hv; cases hv
      rw [heap_del_upd_comm hne]
      exact .free _ ℓ₀ v (by simp [Heap.upd, Ne.symm hne, hv])
  | load ℓ₀ v hv =>
      have hne : ℓ ≠ ℓ₀ := fun he => by subst he; rw [h0] at hv; cases hv
      exact .load _ ℓ₀ v (by simp [Heap.upd, Ne.symm hne, hv])
  | store ℓ₀ v w hw =>
      have hne : ℓ ≠ ℓ₀ := fun he => by subst he; rw [h0] at hw; cases hw
      rw [← heap_upd_comm hne]
      exact .store _ ℓ₀ v w (by simp [Heap.upd, Ne.symm hne, hw])
  | tab c f ℓ₀ hf =>
      have hout : ¬ (ℓ₀ ≤ ℓ ∧ ℓ < ℓ₀ + (BoCa.arrLen c).toNat) := by
        intro hin; simp [Heap.fill, hin] at h1
      have he : (μ.fill ℓ₀ (BoCa.arrLen c).toNat .unit).upd ℓ u =
          (μ.upd ℓ u).fill ℓ₀ (BoCa.arrLen c).toNat .unit := by
        funext k
        by_cases h₁ : k = ℓ
        · subst h₁; simp [Heap.fill, Heap.upd, hout]
        · simp [Heap.fill, Heap.upd, h₁]
      rw [he]
      refine .tab _ c f ℓ₀ fun i hi => ?_
      have hne : ℓ₀ + i ≠ ℓ := by
        intro h'; apply hout; rw [← h']
        exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩
      simp [Heap.upd, hne, hf i hi]
  | beta => exact .beta _ _ _
  | seq => exact .seq _ _
  | letpair => exact .letpair _ _ _ _
  | case₁ => exact .case₁ _ _ _ _
  | case₂ => exact .case₂ _ _ _ _
  | host op v r hr => exact .host _ op v r hr
  | idx => exact .idx _ _ _ _
  | split => exact .split _ _ _ _
  | drop => exact .drop _ _ _ _
  | count => exact .count _ _ _ _ _
  | countTry => exact .countTry _ _ _ _ _
  | boundedFix => exact .boundedFix _ _ _ _
  | iterate => exact .iterate _ _ _
  | hret => exact .hret _ _ _ _ _ _
  | hop n i qs hr hs c v K hc hK => exact .hop _ n i qs hr hs c v K hc hK
  | hunwind n i qs hr hs c v K hc hK => exact .hunwind _ n i qs hr hs c v K hc hK
  | uthen => exact .uthen _ _ _ _
  | ufin N D n i v K hn hK => exact .ufin _ N D n i v K hn hK
  | ufinC N D err K hK => exact .ufinC _ N D err K hK
  | cfret => exact .cfret _ _ _
  | cferr err m j w K hm hK => exact .cferr _ err m j w K hm hK
  | cfcancel err err' K hK => exact .cfcancel _ err err' K hK
  | cancel K hK => exact .cancel _ K hK
  | creraise E K hK => exact .creraise _ E K hK
  | cancelTo n qs hr hs k K hK => exact .cancelTo _ n qs hr hs k K hK

theorem step1_upd_off {μ μ' : Heap} {e e' : Expr} {ℓ : Loc} (u : Val)
    (h : Step1 (ℍ := ℍ) μ e μ' e') (h0 : μ ℓ = none) (h1 : μ' ℓ = none) :
    Step1 (ℍ := ℍ) (μ.upd ℓ u) e (μ'.upd ℓ u) e' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  exact ⟨K, a, a', rfl, rfl, head_upd_off u hh h0 h1⟩

/-- A run each of whose memories leaves `ℓ` free.  `[spec §51]` -/
inductive StepsOff (ℓ : Loc) : Heap → Expr → Heap → Expr → Prop where
  | refl {μ : Heap} (e : Expr) (h : μ ℓ = none) : StepsOff ℓ μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h : μ ℓ = none) (s : Step1 (ℍ := ℍ) μ e μ₁ e₁)
      (t : StepsOff ℓ μ₁ e₁ μ' e') : StepsOff ℓ μ e μ' e'

namespace StepsOff

theorem left {ℓ : Loc} {μ μ' : Heap} {e e' : Expr} (h : StepsOff (ℍ := ℍ) ℓ μ e μ' e') :
    μ ℓ = none := by
  cases h with
  | refl _ h => exact h
  | more h _ _ => exact h

theorem right {ℓ : Loc} {μ μ' : Heap} {e e' : Expr} (h : StepsOff (ℍ := ℍ) ℓ μ e μ' e') :
    μ' ℓ = none := by
  induction h with
  | refl _ h => exact h
  | more _ _ _ ih => exact ih

theorem toSteps {ℓ : Loc} {μ μ' : Heap} {e e' : Expr} (h : StepsOff (ℍ := ℍ) ℓ μ e μ' e') :
    Steps (ℍ := ℍ) μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more _ s _ ih => exact .more s ih

/-- **The run beside `ℓ`**: a run that leaves `ℓ` free runs as well with `ℓ` holding `u`. -/
theorem upd {ℓ : Loc} {μ μ' : Heap} {e e' : Expr} (u : Val) (h : StepsOff (ℍ := ℍ) ℓ μ e μ' e') :
    Steps (ℍ := ℍ) (μ.upd ℓ u) e (μ'.upd ℓ u) e' := by
  induction h with
  | refl => exact .refl _ _
  | more h0 s t ih => exact .more (step1_upd_off u s h0 t.left) ih

theorem plug {ℓ : Loc} {μ μ' : Heap} {e e' : Expr} (K : Kont) (h : StepsOff (ℍ := ℍ) ℓ μ e μ' e') :
    StepsOff (ℍ := ℍ) ℓ μ (K.plug e) μ' (K.plug e') := by
  induction h with
  | refl _ h => exact .refl _ h
  | more h0 s _ ih => exact .more h0 (s.plug K) ih

end StepsOff

/-- A run from `μ` to `μ'`, and the same run beside `ℓ` holding `()`, `ℓ` free at both ends.
`[spec §51]` -/
def Beside (ℓ : Loc) (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  μ ℓ = none ∧ μ' ℓ = none ∧ Steps (ℍ := ℍ) μ e μ' e' ∧
    Steps (ℍ := ℍ) (μ.upd ℓ Val.unit) e (μ'.upd ℓ Val.unit) e'

theorem StepsOff.beside {ℓ : Loc} {μ μ' : Heap} {e e' : Expr} (h : StepsOff (ℍ := ℍ) ℓ μ e μ' e') :
    Beside (ℍ := ℍ) ℓ μ e μ' e' :=
  ⟨h.left, h.right, h.toSteps, h.upd Val.unit⟩

namespace Beside

theorem plug {ℓ : Loc} {μ μ' : Heap} {e e' : Expr} (K : Kont) (h : Beside (ℍ := ℍ) ℓ μ e μ' e') :
    Beside (ℍ := ℍ) ℓ μ (K.plug e) μ' (K.plug e') :=
  ⟨h.1, h.2.1, h.2.2.1.plug K, h.2.2.2.plug K⟩

theorem trans {ℓ : Loc} {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (h : Beside (ℍ := ℍ) ℓ μ e μ₁ e₁)
    (h' : Beside (ℍ := ℍ) ℓ μ₁ e₁ μ' e') : Beside (ℍ := ℍ) ℓ μ e μ' e' :=
  ⟨h.1, h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩

theorem pure {ℓ : Loc} {μ : Heap} {e e' : Expr} (h : PureSteps e e') (h0 : μ ℓ = none) :
    Beside (ℍ := ℍ) ℓ μ e μ e' :=
  ⟨h0, h0, DivDrive.pure_steps h μ, DivDrive.pure_steps h _⟩

end Beside

/-! ### The work's run, segment by segment -/

/-- **The work's run** from `e` to the answer `r`, in the outer context `K₀`, `ℓ` free throughout:
stretches of the direct run (`StepsOff`), and performs of operations of a name `m` with `P m`,
each answered in place at `b` by a handler in `K₀`, uniformly in the continuation it captures
(`hans`).  `[spec §51]` -/
inductive WorkRun (P : UInt32 → Prop) (ℓ : Loc) (K₀ : Kont) : Heap → Expr → Heap → Val → Prop where
  | done {μ μ' : Heap} {e : Expr} {r : Val} (h : StepsOff (ℍ := ℍ) ℓ μ e μ' (.val r)) :
      WorkRun P ℓ K₀ μ e μ' r
  | op {μ μ₁ μ₂ μ' : Heap} {e : Expr} {r : Val} {m i : UInt32} {u b : Val} {Kw : Kont}
      (hm : P m) (hKw : Kw.HasHnd m = false)
      (h : StepsOff (ℍ := ℍ) ℓ μ e μ₁ (Kw.plug (performE (.val (opPayload m i u)))))
      (hans : ∀ Kc : Kont, Kc.HasHnd m = false →
        Beside (ℍ := ℍ) ℓ μ₁ (K₀.plug (Kc.plug (performE (.val (opPayload m i u))))) μ₂
          (K₀.plug (Kc.plug (.val b))))
      (t : WorkRun P ℓ K₀ μ₂ (Kw.plug (.val b)) μ' r) : WorkRun P ℓ K₀ μ e μ' r

/-- **The two-run argument**: the work's run is a run in every continuation `Kc` inside `K₀` that
has no handler of a name of `P`, and beside `ℓ`.  `[spec §51]` -/
theorem work_run_ctx {P : UInt32 → Prop} {ℓ : Loc} {K₀ : Kont} {μ μ' : Heap} {e : Expr} {r : Val}
    (hw : WorkRun (ℍ := ℍ) P ℓ K₀ μ e μ' r) :
    ∀ Kc : Kont, (∀ m, P m → Kc.HasHnd m = false) →
      Beside (ℍ := ℍ) ℓ μ (K₀.plug (Kc.plug e)) μ' (K₀.plug (Kc.plug (.val r))) := by
  induction hw with
  | done h =>
      intro Kc _
      have := h.beside.plug (K₀.comp Kc)
      simpa [Kont.plug_comp] using this
  | @op μ μ₁ μ₂ μ' e r m i u b Kw hm hKw h hans t ih =>
      intro Kc hKc
      have h₁ := h.beside.plug (K₀.comp Kc)
      have h₂ := hans (Kc.comp Kw) (by rw [hasHnd_comp, hKc m hm, hKw]; rfl)
      simp only [Kont.plug_comp] at h₁ h₂
      exact h₁.trans (h₂.trans (ih Kc hKc))

theorem WorkRun.left {P : UInt32 → Prop} {ℓ : Loc} {K₀ : Kont} {μ μ' : Heap} {e : Expr} {r : Val}
    (hw : WorkRun (ℍ := ℍ) P ℓ K₀ μ e μ' r) : μ ℓ = none := by
  cases hw with
  | done h => exact h.left
  | op _ _ h _ _ => exact h.left

/-! ### The site -/

/-- The direct call's frame at the site: `case [·] {inl y → y | inr z → X}`.  `[spec §51]` -/
def directK (X : Expr) : Kont := .case .hole (.var 0) X

/-- The handled run up to the work: `[op]` allocates `κ`'s cell `ℓ`, and the clause runs the work
under the finaliser frame. -/
theorem last_start {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32} {qs hr hs c vw vn g v : Val}
    {j : Nat} {K K₀ : Kont} (hc : clauseAt hs.1 i.toNat = some c)
    (hcl : c.1 = lastClause j false (.val vw) (.val vn)) (htag : capTag qs.1 i.toNat = Qual.cancel.tag)
    (hK : K.HasHnd n = false) (hg : PureSteps (pickE j (.val vw)) (.val g)) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))))
      (μ.upd ℓ Val.unit)
      (K₀.plug ((ubindK (lastN j ⟨kappaC true ℓ (hndVal n qs hr hs) K, isVal_kappaC _ _ _ _⟩ vn)
        (lastD ⟨kappaC true ℓ (hndVal n qs hr hs) K, isVal_kappaC _ _ _ _⟩)).plug
          (.app (.val g) (.val v)))) := by
  have h₁ := catch_cell (ℍ := ℍ) hℓ (qs := qs) (hr := hr) v (q := .cancel) (by decide) hc hK htag K₀
  refine h₁.trans ?_
  have h₂ := lastClause_steps j vw vn g v ⟨kappaC true ℓ (hndVal n qs hr hs) K, isVal_kappaC _ _ _ _⟩ hg
  have e : Expr.app (Expr.val c) (.pair (.val v) (kappaC (cellCancel .cancel) ℓ (hndVal n qs hr hs) K)) =
      .app (lastClause j false (.val vw) (.val vn))
        (.val (Val.pair v ⟨kappaC true ℓ (hndVal n qs hr hs) K, isVal_kappaC _ _ _ _⟩)) := by
    rw [show Expr.val c = c.1 from rfl, hcl]; rfl
  rw [e]
  exact DivDrive.pure_steps (h₂.plug K₀) _

/-- **T-B2, the erasure law at a work that performs.**  At a `[handle-last]` node's clause `c` of a
cancellable operation, a work whose run performs only operations answered in place by handlers
outside the node (`WorkRun`), of names that are not `n` and have no handler in `K`:
- **resume** (`inl y`): the handled run and the direct run both reach `K₀[hnd H K[y]]`;
- **cancel** (`inr z`): the handled run reaches `K`'s cancel run followed by the exit,
  `K₀[(λ_. nf z) (ccatch K†[raise ⊥])]`, and the direct run its `inr` arm `X[z]` in place;

each at the memory the work's run ends at.  `[spec §51]` -/
theorem last_perform_direct {P : UInt32 → Prop} {μ μ' : Heap} {ℓ : Loc} {n i : UInt32}
    {qs hr hs c vw vn g v : Val} {j : Nat} {K K₀ : Kont} (X : Expr)
    (hc : clauseAt hs.1 i.toNat = some c) (hcl : c.1 = lastClause j false (.val vw) (.val vn))
    (htag : capTag qs.1 i.toNat = Qual.cancel.tag) (hK : K.HasHnd n = false)
    (hg : PureSteps (pickE j (.val vw)) (.val g)) (hP : ∀ m, P m → m ≠ n ∧ K.HasHnd m = false) :
    (∀ y : Val, WorkRun (ℍ := ℍ) P ℓ K₀ μ (.app (.val g) (.val v)) μ' (Val.inj₁ y) →
      Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))))
        μ' (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (.val y)))) ∧
      Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug ((directK X).plug
          (.app (.val g) (.val v)))))) μ' (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (.val y))))) ∧
    (∀ z : Val, WorkRun (ℍ := ℍ) P ℓ K₀ μ (.app (.val g) (.val v)) μ' (Val.inj₂ z) →
      Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))))
        μ' (K₀.plug ((exitK j vn z).plug
          (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))))) ∧
      Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug ((directK X).plug
          (.app (.val g) (.val v)))))) μ'
        (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (X.subst 0 z))))) := by
  set H := hndVal n qs hr hs
  set κ : Val := ⟨kappaC true ℓ H K, isVal_kappaC _ _ _ _⟩
  -- the handled run's continuation of the work, and the direct run's
  have hKh : ∀ m, P m → (ubindK (lastN j κ vn) (lastD κ)).HasHnd m = false :=
    fun m _ => by simp [Kont.HasHnd, Val.pair, Expr.val]
  have hKd : ∀ m, P m → ((hndK H).comp (K.comp (directK X))).HasHnd m = false := by
    intro m hm
    obtain ⟨hmn, hKm⟩ := hP m hm
    rw [hasHnd_comp, hasHnd_comp, hKm, hndK_hasHnd]
    simp [directK, Kont.HasHnd, Ne.symm hmn]
  have hplugd : ∀ e : Expr, K₀.plug (((hndK H).comp (K.comp (directK X))).plug e) =
      K₀.plug (hndE H (K.plug ((directK X).plug e))) := by
    intro e; simp only [Kont.plug_comp]; rfl
  refine ⟨fun y hw => ?_, fun z hw => ?_⟩
  · have hh := work_run_ctx hw _ hKh
    have hd := work_run_ctx hw _ hKd
    rw [hplugd, hplugd] at hd
    refine ⟨?_, ?_⟩
    · refine (last_start (K₀ := K₀) hw.left hc hcl htag hK hg).trans (hh.2.2.2.trans ?_)
      refine (DivDrive.pure_steps ((lastN_inl j κ vn y).plug K₀) _).trans ?_
      have := kappaC_resume (ℍ := ℍ) (μ := μ'.upd ℓ Val.unit) (ℓ := ℓ) (by simp) true H K y K₀
      rwa [heap_del_upd hh.2.1] at this
    · refine hd.2.2.1.trans (.one ?_)
      have := (Step1.head (Head.case₁ (ℍ := ℍ) μ' y (.var 0) X)).plug (K₀.comp ((hndK H).comp K))
      simpa [Kont.plug_comp, directK, Kont.plug, hndE, Expr.subst] using this
  · have hh := work_run_ctx hw _ hKh
    have hd := work_run_ctx hw _ hKd
    rw [hplugd, hplugd] at hd
    refine ⟨?_, ?_⟩
    · refine (last_start (K₀ := K₀) hw.left hc hcl htag hK hg).trans (hh.2.2.2.trans ?_)
      refine (DivDrive.pure_steps ((lastN_inr j κ vn z).plug K₀) _).trans ?_
      have := kappaC_cancel (ℍ := ℍ) (μ := μ'.upd ℓ Val.unit) (ℓ := ℓ) (by simp) H K
        (K₀.comp (exitK j vn z))
      rw [heap_del_upd hh.2.1, Kont.plug_comp, Kont.plug_comp] at this
      exact this
    · refine hd.2.2.1.trans (.one ?_)
      have := (Step1.head (Head.case₂ (ℍ := ℍ) μ' z (.var 0) X)).plug (K₀.comp ((hndK H).comp K))
      simpa [Kont.plug_comp, directK, Kont.plug, hndE, Expr.subst] using this

/-- **T-B1, the erasure law at a work that resumes `κ` last.**  When the work, called directly,
runs to `inl y` leaving `κ`'s cell `ℓ` free, the perform under the node and the direct call
`case (w v) {inl y → y | inr z → X}` in its place both reach `K₀[hnd H K[y]]`, at the memory the
work's run ends at.  `[spec §51]` -/
theorem last_resume_direct {μ μ' : Heap} {ℓ : Loc} {n i : UInt32} {qs hr hs c vw vn g v y : Val}
    {j : Nat} {K K₀ : Kont} (X : Expr)
    (hc : clauseAt hs.1 i.toNat = some c) (hcl : c.1 = lastClause j false (.val vw) (.val vn))
    (htag : capTag qs.1 i.toNat = Qual.cancel.tag) (hK : K.HasHnd n = false)
    (hg : PureSteps (pickE j (.val vw)) (.val g))
    (hw : StepsOff (ℍ := ℍ) ℓ μ (.app (.val g) (.val v)) μ' (.val (Val.inj₁ y))) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))))
      μ' (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (.val y)))) ∧
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug ((directK X).plug
        (.app (.val g) (.val v)))))) μ' (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (.val y)))) :=
  (last_perform_direct (P := fun _ => False) X hc hcl htag hK hg (fun _ h => h.elim)).1 y
    (.done hw)

/-- **T-B1′, the erasure law at a work that cancels `κ` last.**  When the work, called directly,
runs to `inr z` leaving `κ`'s cell `ℓ` free, the perform under the node reaches `K`'s cancel run,
`K`'s handler frames dead and its finalisers kept, in the site's outer context and followed by the
exit, `K₀[(λ_. nf z) (ccatch K†[raise ⊥])]`; the direct call reaches its `inr` arm in place; both
at the memory the work's run ends at.  `[spec §51]` -/
theorem last_cancel_direct {μ μ' : Heap} {ℓ : Loc} {n i : UInt32} {qs hr hs c vw vn g v z : Val}
    {j : Nat} {K K₀ : Kont} (X : Expr)
    (hc : clauseAt hs.1 i.toNat = some c) (hcl : c.1 = lastClause j false (.val vw) (.val vn))
    (htag : capTag qs.1 i.toNat = Qual.cancel.tag) (hK : K.HasHnd n = false)
    (hg : PureSteps (pickE j (.val vw)) (.val g))
    (hw : StepsOff (ℍ := ℍ) ℓ μ (.app (.val g) (.val v)) μ' (.val (Val.inj₂ z))) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))))
      μ' (K₀.plug ((exitK j vn z).plug (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))))) ∧
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug ((directK X).plug
        (.app (.val g) (.val v)))))) μ'
      (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (X.subst 0 z)))) :=
  (last_perform_direct (P := fun _ => False) X hc hcl htag hK hg (fun _ h => h.elim)).2 z
    (.done hw)

/-- **T-B1′'s exit**: when `K`'s cancel run answers `()`, the perform under the node reaches the
exit `nf z` in the site's outer context.  `[spec §51]` -/
theorem last_cancel_exit {μ μ' μ'' : Heap} {ℓ : Loc} {n i : UInt32} {qs hr hs c vw vn g gn v z : Val}
    {j : Nat} {K K₀ : Kont}
    (hc : clauseAt hs.1 i.toNat = some c) (hcl : c.1 = lastClause j false (.val vw) (.val vn))
    (htag : capTag qs.1 i.toNat = Qual.cancel.tag) (hK : K.HasHnd n = false)
    (hg : PureSteps (pickE j (.val vw)) (.val g)) (hn : PureSteps (pickE j (.val vn)) (.val gn))
    (hw : StepsOff (ℍ := ℍ) ℓ μ (.app (.val g) (.val v)) μ' (.val (Val.inj₂ z)))
    (hcan : Steps (ℍ := ℍ) μ' (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) μ''
      (.val .unit)) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))))
      μ'' (K₀.plug (.app (.val gn) (.val z))) := by
  refine ((last_cancel_direct (.val .unit) hc hcl htag hK hg hw).1.trans
    ((hcan.plug ((exitK j vn z))).plug K₀)).trans ?_
  exact DivDrive.pure_steps ((exitK_steps j vn z gn hn).plug K₀) _

/-! ### `[cancel-to]` reaches T-B1′'s configuration -/

/-- The exit `λ_. nf z` of `exitK`, as a value. -/
def exitV (j : Nat) (vn z : Val) : Val :=
  Val.lam (.app (pickE j ((Expr.val vn).shift 1 0)) (.val (z.shift 1 0)))

theorem exitK_eq (j : Nat) (vn z : Val) : exitK j vn z = .appR (.val (exitV j vn z)) .hole := rfl

/-- **`[cancel-to]` is T-B1′ in one step**: `hnd H K[cancelTo_n (λ_. nf z)]` steps once, with no
`κ` cell, to `ccatch (K†[raise ⊥]); (λ_. nf z) ()`, the cancel run of `K` that
`last_cancel_direct`'s post-state `(λ_. nf z) (ccatch K†[raise ⊥])` holds, followed by the same
exit.  When `K`'s cancel run answers `()`, both reach the exit `(λ_. nf z) ()` in `K₀`, at the same
memory.  `[spec §51]` -/
theorem cancelTo_last_cancel {μ μ' : Heap} {n : UInt32} {qs hr hs vn z : Val} {j : Nat}
    {K K₀ : Kont} (hK : K.HasHnd n = false)
    (hcan : Steps (ℍ := ℍ) μ (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) μ'
      (.val .unit)) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs)
        (K.plug (BoCa.BoLo.cancelToE (.val (BoCa.BoLo.cancelToPayload n (exitV j vn z)))))))
      μ' (K₀.plug ((exitK j vn z).plug (.val .unit))) ∧
    Steps (ℍ := ℍ) μ (K₀.plug ((exitK j vn z).plug
        (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))))
      μ' (K₀.plug ((exitK j vn z).plug (.val .unit))) := by
  refine ⟨?_, (hcan.plug (exitK j vn z)).plug K₀⟩
  refine .more ⟨K₀, _, _, rfl, rfl, Head.cancelTo μ n qs hr hs (exitV j vn z) K hK⟩ ?_
  refine ((hcan.plug (.seq .hole (.app (.val (exitV j vn z)) (.val .unit)))).plug K₀).trans ?_
  exact .more ⟨K₀, .seq (.val Val.unit) ((exitK j vn z).plug (.val .unit)), _, rfl, rfl,
    Head.seq μ' _⟩ (.refl _ _)

/-! ### Outer handlers that answer in place -/

/-- **An outer handler answers in place**: a handler `H'` of `m` in `K₀ = K₁[hnd H' K₂[·]]`, at an
operation with a cell, whose clause at the argument `u` and any `κ` runs, beside `ℓ`, to `κ`'s
resume at `b`, answers the perform at `b` in every continuation `Kc` free of `m`: `WorkRun.op`'s
`hans`.  `κ`'s cell `ℓ'` is not `ℓ`.  `[spec §51]` -/
theorem answers_in_place {μ₁ μ₂ : Heap} {ℓ ℓ' : Loc} (hne : ℓ ≠ ℓ') (h1 : μ₁ ℓ' = none)
    (h2 : μ₂ ℓ' = none) {m i : UInt32} {qs hr hs c u b : Val} {q : Qual} (hq : q ≠ .unr)
    {K₁ K₂ : Kont} (hc : clauseAt hs.1 i.toNat = some c) (htag : capTag qs.1 i.toNat = q.tag)
    (hK₂ : K₂.HasHnd m = false)
    (hrun : ∀ κ : Val, Beside (ℍ := ℍ) ℓ (μ₁.upd ℓ' Val.unit)
      (K₁.plug (.app (.val c) (.pair (.val u) (.val κ)))) (μ₂.upd ℓ' Val.unit)
      (K₁.plug (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val b)))) :
    ∀ Kc : Kont, Kc.HasHnd m = false →
      Beside (ℍ := ℍ) ℓ μ₁ ((K₁.comp ((hndK (hndVal m qs hr hs)).comp K₂)).plug
          (Kc.plug (performE (.val (opPayload m i u))))) μ₂
        ((K₁.comp ((hndK (hndVal m qs hr hs)).comp K₂)).plug (Kc.plug (.val b))) := by
  intro Kc hKc
  set H := hndVal m qs hr hs
  have hK : (K₂.comp Kc).HasHnd m = false := by rw [hasHnd_comp, hK₂, hKc]; rfl
  have hp : ∀ e : Expr, (K₁.comp ((hndK H).comp K₂)).plug (Kc.plug e) =
      K₁.plug (hndE H ((K₂.comp Kc).plug e)) := by
    intro e; simp only [Kont.plug_comp]; rfl
  rw [hp, hp]
  set κ : Val := ⟨kappaC (cellCancel q) ℓ' H (K₂.comp Kc), isVal_kappaC _ _ _ _⟩
  have hr := hrun κ
  have hμ₁ : μ₁ ℓ = none := by simpa [Heap.upd, hne] using hr.1
  have hμ₂ : μ₂ ℓ = none := by simpa [Heap.upd, hne] using hr.2.1
  refine ⟨hμ₁, hμ₂, ?_, ?_⟩
  · refine (catch_cell (ℍ := ℍ) h1 u hq hc hK htag K₁).trans (hr.2.2.1.trans ?_)
    have := kappaC_resume (ℍ := ℍ) (μ := μ₂.upd ℓ' Val.unit) (ℓ := ℓ') (by simp) (cellCancel q) H
      (K₂.comp Kc) b K₁
    rwa [heap_del_upd h2] at this
  · have h1' : (μ₁.upd ℓ Val.unit) ℓ' = none := by simp [Heap.upd, Ne.symm hne, h1]
    refine (catch_cell (ℍ := ℍ) h1' u hq hc hK htag K₁).trans ?_
    rw [heap_upd_comm hne]
    refine hr.2.2.2.trans ?_
    have := kappaC_resume (ℍ := ℍ) (μ := (μ₂.upd ℓ' Val.unit).upd ℓ Val.unit) (ℓ := ℓ')
      (by simp [Heap.upd, Ne.symm hne]) (cellCancel q) H (K₂.comp Kc) b K₁
    rwa [← heap_del_upd_comm hne, heap_del_upd h2] at this

/-- An outer tail clause (`effHandleT`'s) whose answering function runs beside `ℓ` to `b` resumes
`κ` at `b`, for every `κ`.  `[spec §51]` -/
theorem tail_clause_answers {μa μb : Heap} {ℓ : Loc} {j : Nat} {c vc g u b : Val} {K₁ : Kont}
    (hcl : c.1 = tailClause j false (.val vc)) (hg : PureSteps (pickE j (.val vc)) (.val g))
    (hrun : Beside (ℍ := ℍ) ℓ μa (.app (.val g) (.val u)) μb (.val b)) (κ : Val) :
    Beside (ℍ := ℍ) ℓ μa (K₁.plug (.app (.val c) (.pair (.val u) (.val κ)))) μb
      (K₁.plug (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val b))) := by
  have e : Expr.app (Expr.val c) (.pair (.val u) (.val κ)) =
      .app (tailClause j false (.val vc)) (.val (Val.pair u κ)) := by
    rw [show Expr.val c = c.1 from rfl, hcl]; rfl
  rw [e]
  refine (Beside.pure ((tailClause_steps j vc g u κ hg).plug K₁) hrun.1).trans ?_
  have hw := hrun.plug (K₁.comp (resK κ))
  rw [Kont.plug_comp, Kont.plug_comp] at hw
  refine hw.trans ?_
  have := Beside.pure (ℍ := ℍ) ((resK_steps κ b).plug K₁) hrun.2.1
  simpa [Kont.plug_comp] using this

/-- **An outer `[handle-last]` clause whose work resumes**, its work's own run a `WorkRun` in `K₁`,
resumes `κ` at `b`, for every `κ`: the pipe-fusion case, which nests.  `[spec §51]` -/
theorem last_clause_answers {P : UInt32 → Prop} {μa μb : Heap} {ℓ : Loc} {j : Nat}
    {c vw vn g u b : Val} {K₁ : Kont}
    (hcl : c.1 = lastClause j false (.val vw) (.val vn)) (hg : PureSteps (pickE j (.val vw)) (.val g))
    (hrun : WorkRun (ℍ := ℍ) P ℓ K₁ μa (.app (.val g) (.val u)) μb (Val.inj₁ b)) (κ : Val) :
    Beside (ℍ := ℍ) ℓ μa (K₁.plug (.app (.val c) (.pair (.val u) (.val κ)))) μb
      (K₁.plug (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val b))) := by
  have e : Expr.app (Expr.val c) (.pair (.val u) (.val κ)) =
      .app (lastClause j false (.val vw) (.val vn)) (.val (Val.pair u κ)) := by
    rw [show Expr.val c = c.1 from rfl, hcl]; rfl
  rw [e]
  have hr := work_run_ctx hrun (ubindK (lastN j κ vn) (lastD κ))
    (fun m _ => by simp [Kont.HasHnd, Val.pair, Expr.val])
  refine (Beside.pure ((lastClause_steps j vw vn g u κ hg).plug K₁) hr.1).trans (hr.trans ?_)
  exact Beside.pure ((lastN_inl j κ vn b).plug K₁) hr.2.1

end BoCa.Fig16.LogRel.Core
