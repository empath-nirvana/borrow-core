import Spike670.Builders

/-!
# #670 — slice 1: the derivation-following conversion is linear

For each node of the pure fragment that `conv` converts by following the derivation (a leaf,
a split by the masks, a binder, an injection, …), its output meets `Post`: it consumes exactly the
live variables of its context (or ends unreachable), and binds each variable once, from the
counter. The node's children are assumed to meet `Spec` (the induction hypothesis).

The hypotheses taken from the program:
- `s.mach.isEmpty`: no machine operations (SPEC §49), so `conv` does not start a machine;
- `hD`: the variables the node's split copies satisfy `D`. `copy_slots_persistent` discharges
  it from the kernel's `Ctx.SplitP` and the masks' relation `SplitMasks`.

Nothing else is read from the kernel: the masks' length and their agreement with dead slots, and
a leaf's slot being live, are checked by the conversion itself (it throws otherwise).
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

variable {D : Var → Prop}

theorem liveF_cons_some (x : Var) (c : Ctx) : liveF (some x :: c) = insert x (liveF c) := by
  simp [liveF, live]

theorem liveF_cons_none (c : Ctx) : liveF (none :: c) = liveF c := by
  simp [liveF, live]

theorem live_cons_some (x : Var) (c : Ctx) : live (some x :: c) = x :: live c := by
  simp [live]

theorem live_cons_none (c : Ctx) : live (none :: c) = live c := by
  simp [live]

/-- The parts of a split, each well formed, disjoint, below the counter. -/
structure SplitOut (D : Var → Prop) (ctx : Ctx) (s : CState) (pre : Tm → Tm) (c₁ c₂ : Ctx)
    (s₁ : CState) : Prop where
  grows : Grows s s₁
  wf₁ : WF c₁ s₁
  wf₂ : WF c₂ s₁
  disj : ∀ y ∈ live c₁, y ∉ live c₂
  /-- A term consuming both parts, binding at or above `s₁.next`, is wrapped into one consuming
  `ctx`. -/
  wrap : ∀ s' t, Grows s₁ s' → PostG D (liveF c₁ ∪ liveF c₂) s₁.next s' t →
    Post D ctx s (pre t) s'

theorem splitOut {ctx : Ctx} {u : Masks} {rule : String} {s s₁ : CState} {pre : Tm → Tm}
    {c₁ c₂ : Ctx} (h : Ok (splitCtx ctx u rule) s (pre, c₁, c₂) s₁) (hw : WF ctx s)
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x) : SplitOut D ctx s pre c₁ c₂ s₁ := by
  obtain ⟨g, -, -, n₁, n₂, dj, lt, -, hpre, hbnd⟩ := splitCtx_spec h hw.1 hw.2 hD
  refine ⟨g, ⟨n₁, fun y hy => lt y (by simp [hy])⟩, ⟨n₂, fun y hy => lt y (by simp [hy])⟩, dj, ?_⟩
  intro s' t g' ⟨⟨Δ, hl, hc⟩, nd, rg⟩
  refine ⟨g.trans g', ⟨⟨Δ, ?_, hc⟩, ?_, ?_⟩⟩
  · have := hpre ∅ t Δ (by simp) (by simpa using hl)
    simpa using this
  · obtain ⟨K, hK, nK, rK⟩ := hbnd t
    rw [hK, List.nodup_append]
    refine ⟨nK, nd, fun a ha b hb => ?_⟩
    rintro rfl; have := (rK a ha).2; have := (rg a hb).1; vomega
  · obtain ⟨K, hK, nK, rK⟩ := hbnd t
    rw [hK]; intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · have h1 := rK y hy; have := g'.next; exact ⟨h1.1, by vomega⟩
    · have h1 := rg y hy; have := g.next; exact ⟨by vomega, h1.2⟩

/-- **The copy set is persistent.** A slot both masks hold sits, in the kernel's context, at a
persistent type (`SplitMasks.both_persistent`): the copies a split makes are of values the
kernel lets it duplicate. -/
theorem copy_slots_persistent {Γ Γ₁ Γ₂ : BoCa.Ctx VTy} {u : Masks} {ctx : Ctx}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hm : u.Rel Γ₁ Γ₂) :
    ∀ x ∈ bothVars (ctx.zip u.ms), ∃ (k : Nat) (sl : BoCa.Slot VTy), ctx[k]? = some (some x) ∧
      Γ[k]? = some sl ∧
      sl.ty.Persistent := by
  intro x hx
  simp only [bothVars, List.mem_filterMap] at hx
  obtain ⟨⟨o, a, b⟩, hmem, he⟩ := hx
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hmem
  rcases o with _ | y <;> rcases a <;> rcases b <;> simp at he
  subst he
  have hk₁ : k < ctx.length := by simp at hk; omega
  have hk₂ : k < u.ms.length := by simp at hk; omega
  rw [List.getElem_zip] at hke
  simp only [Prod.mk.injEq] at hke
  obtain ⟨h₁, h₂⟩ := hke
  have e₁ : u.u₁.getD k false = true := by simp [Masks.u₁, hk₂, h₂]
  have e₂ : u.u₂.getD k false = true := by simp [Masks.u₂, hk₂, h₂]
  obtain ⟨sl, hsl, -, hp⟩ := SplitMasks.both_persistent hs hm k e₁ e₂
  exact ⟨k, sl, by simp [hk₁, h₁], hsl, hp⟩

/-! ### Composition -/

/-- `case sv x b₁ y b₂`, each arm closed over its binder and `Γ`. -/
theorem postG_case {Γ : Finset Var} {sv x y : Var} {b₁ b₂ : Tm} {lo : Nat} {s' : CState}
    (hsv : sv ∉ Γ) (h₁ : PostG D (insert x Γ) lo s' b₁) (h₂ : PostG D (insert y Γ) lo s' b₂)
    (hx : lo ≤ x ∧ x < s'.next) (hy : lo ≤ y ∧ y < s'.next)
    (hxn : x ∉ bnd b₁ ∧ x ∉ bnd b₂ ∧ x ≠ y) (hyn : y ∉ bnd b₁ ∧ y ∉ bnd b₂)
    (hdj : ∀ a ∈ bnd b₁, a ∉ bnd b₂) :
    PostG D (insert sv Γ) lo s' (.case sv x b₁ y b₂) := by
  obtain ⟨⟨Δ₁, l₁, c₁⟩, n₁, r₁⟩ := h₁
  obtain ⟨⟨Δ₂, l₂, c₂⟩, n₂, r₂⟩ := h₂
  have e : (insert sv Γ).erase sv = Γ := Finset.erase_insert hsv
  refine ⟨?_, ?_, ?_⟩
  · have hj : ∃ Δ, Join Δ₁ Δ₂ Δ ∧ Closed Δ := by
      rcases c₁ with rfl | rfl <;> rcases c₂ with rfl | rfl
      · exact ⟨none, rfl, .inl rfl⟩
      · exact ⟨some ∅, rfl, .inr rfl⟩
      · exact ⟨some ∅, rfl, .inr rfl⟩
      · exact ⟨some ∅, ⟨rfl, rfl⟩, .inr rfl⟩
    obtain ⟨Δ, hj, hc⟩ := hj
    exact ⟨Δ, .case (by simp) (by rw [e]; exact l₁) (by rw [e]; exact l₂) hj, hc⟩
  · simp only [bnd, List.nodup_cons, List.mem_append, List.mem_cons, not_or, List.nodup_append]
    exact ⟨⟨hxn.1, hxn.2.2, hxn.2.1⟩, n₁, ⟨hyn.2, n₂⟩, fun a ha b hb => by
      rcases hb with hb | hb
      · intro hab; rw [hab, hb] at ha; exact hyn.1 ha
      · intro hab; rw [hab] at ha; exact hdj b ha hb⟩
  · intro z hz
    simp only [bnd, List.mem_cons, List.mem_append] at hz
    rcases hz with rfl | hz | rfl | hz
    · exact hx
    · exact r₁ z hz
    · exact hy
    · exact r₂ z hz

end Backend2.Spike670

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

theorem PostG.lower {D : Var → Prop} {Γ : Finset Var} {lo lo' : Nat} {s' : CState} {t : Tm}
    (h : PostG D Γ lo s' t) (hl : lo' ≤ lo) : PostG D Γ lo' s' t :=
  ⟨h.closed, h.nodup, fun y hy => ⟨le_trans hl (h.range y hy).1, (h.range y hy).2⟩⟩

theorem ok_get' {s s' b : CState} (h : Ok (get : CM CState) s b s') : b = s ∧ s' = s := ok_get h

/-- `conv`'s prologue at a node: the node recorded, the state read, and with no machine
operation (`hm`), the node's own conversion. -/
syntax "open_conv " ident ident ident ident : tactic
macro_rules
  | `(tactic| open_conv $h $hm $s1 $hk) => `(tactic| (
      rw [conv.eq_def] at $h:ident; simp only at $h:ident
      obtain ⟨_, $s1:ident, hrf, $h:ident⟩ := ok_bind $h:ident
      have $hk:ident : Keeps _ $s1:ident := ok_readFact hrf
      obtain ⟨_, _, hget, $h:ident⟩ := ok_bind $h:ident
      obtain ⟨hd, hs⟩ := ok_get' hget
      rw [hd, hs] at $h:ident
      have hmm : (CState.mach $s1:ident).isEmpty = true := ($hk:ident).2 ▸ $hm:ident
      simp only [machNode, hmm, Bool.not_true, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte] at $h:ident))

variable {D : Var → Prop}

theorem WF.keeps {ctx : Ctx} {s s₁ : CState} (hw : WF ctx s) (hk : Keeps s s₁) : WF ctx s₁ :=
  ⟨hw.1, fun y hy => hk.1 ▸ hw.2 y hy⟩

theorem WF.grows {ctx : Ctx} {s s₁ : CState} (hw : WF ctx s) (hk : Grows s s₁) : WF ctx s₁ :=
  ⟨hw.1, fun y hy => by have := hw.2 y hy; have := hk.next; vomega⟩

/-! ### Leaves -/

theorem node_var {fuel : Nat} {ctx : Ctx} {info j i A} {s s' : CState} {tm : Tm}
    (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.var info j i A)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  split at h
  · rename_i x hx
    obtain ⟨rfl, hs⟩ := ok_pure h
    rw [hs]
    have hp : PostG D {x} s₁.next s₁ (.var x) := by
      simpa using (postG_ops (D := D) (xs := [x]) rfl (List.nodup_singleton x) :
        PostG D [x].toFinset s₁.next s₁ (.var x))
    have := post_leaf_some (hw.keeps hk) hx hp
    exact ⟨hk.grows, by rw [← hk.1]; exact this.2⟩
  · exact (ok_throw h).elim

/-! ### `sumE`: a split, the scrutinee named, an arm per summand -/

/-- The scrutinee's continuation at `sumE`: two fresh binders, an arm each over the right part. -/
theorem sumE_cont {fuel : Nat} {c₂ : Ctx} {aT bT : LTy} {t₁ t₂ : TExpr}
    (IH₁ : Spec D (fun c => conv fuel c t₁)) (IH₂ : Spec D (fun c => conv fuel c t₂))
    (hw₂ : WF c₂ s₀) :
    ∀ sv s₁ b s₂, sv ∉ liveF c₂ → sv < s₁.next → s₀.next ≤ s₁.next → s₁.mach.isEmpty = true →
      Ok (do
        let x ← fresh aT; let y ← fresh bT
        return Tm.case sv x (← conv fuel (some x :: c₂) t₁) y (← conv fuel (some y :: c₂) t₂))
        s₁ b s₂ →
      Grows s₁ s₂ ∧ PostG D (insert sv (liveF c₂)) s₁.next s₂ b := by
  intro sv s₁ b s₂ hsv hlt hle hm h
  obtain ⟨x, sa, hx, h⟩ := ok_bind h
  obtain ⟨rfl, hxn, hxm⟩ := ok_fresh hx
  obtain ⟨y, sb, hy, h⟩ := ok_bind h
  obtain ⟨rfl, hyn, hym⟩ := ok_fresh hy
  obtain ⟨b₁, sc, h₁, h⟩ := ok_bind h
  obtain ⟨b₂, sd, h₂, h⟩ := ok_bind h
  obtain ⟨rfl, hsd⟩ := ok_pure h
  rw [hsd]
  have wfx : ∀ v (st : CState), v < st.next → (∀ z ∈ live c₂, z < v) → WF (some v :: c₂) st :=
    fun v st hv hz => ⟨by rw [live_cons_some]; exact List.nodup_cons.2 ⟨fun hh => by
        have := hz v hh; vomega, hw₂.1⟩,
      fun z hz' => by
        rw [live_cons_some] at hz'; rcases List.mem_cons.1 hz' with rfl | hz'
        · exact hv
        · have := hz z hz'; vomega⟩
  have hc2 : ∀ z ∈ live c₂, z < s₁.next := fun z hz => by have := hw₂.2 z hz; vomega
  obtain ⟨g₁, p₁⟩ := IH₁ _ sb b₁ sc (wfx _ sb (by vomega) hc2) (by rw [hym, hxm]; exact hm) h₁
  obtain ⟨g₂, p₂⟩ := IH₂ _ sc b₂ sd (wfx _ sc (by have := g₁.next; vomega)
    (fun z hz => by have := hc2 z hz; vomega)) (by rw [g₁.mach, hym, hxm]; exact hm) h₂
  rw [liveF_cons_some] at p₁ p₂
  have gn₁ := g₁.next; have gn₂ := g₂.next
  refine ⟨⟨by vomega, by rw [g₂.mach, g₁.mach, hym, hxm]⟩, ?_⟩
  have q₁ : PostG D (insert s₁.next (liveF c₂)) s₁.next sd b₁ :=
    ⟨p₁.closed, p₁.nodup, fun z hz => ⟨by have := (p₁.range z hz).1; vomega,
      by have := (p₁.range z hz).2; vomega⟩⟩
  have q₂ : PostG D (insert sa.next (liveF c₂)) s₁.next sd b₂ := p₂.lower (by vomega)
  refine postG_case hsv q₁ q₂ ⟨le_refl _, by vomega⟩ ⟨by vomega, by vomega⟩
    ⟨fun hh => ?_, fun hh => ?_, by vomega⟩ ⟨fun hh => ?_, fun hh => ?_⟩ (fun a ha hb => ?_)
  · have := (p₁.range _ hh).1; vomega
  · have := (p₂.range _ hh).1; vomega
  · have := (p₁.range _ hh).1; vomega
  · have := (p₂.range _ hh).1; vomega
  · have := (p₁.range _ ha).2; have := (p₂.range _ hb).1; vomega

/-- **`sumE`.** -/
theorem node_sumE {fuel : Nat} {ctx : Ctx} {info j A B C u tV t₁ t₂} {s s' : CState} {tm : Tm}
    (IHV : Spec D (fun c => conv fuel c tV)) (IH₁ : Spec D (fun c => conv fuel c t₁))
    (IH₂ : Spec D (fun c => conv fuel c t₂))
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x)
    (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.sumE info j A B C u tV t₁ t₂)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  obtain ⟨⟨pre, c₁, c₂⟩, s₂, hsp, h⟩ := ok_bind h
  obtain ⟨aT, s₃, hv₁, h⟩ := ok_bind h
  obtain ⟨bT, s₄, hv₂, h⟩ := ok_bind h
  obtain ⟨e, s₅, hc, h⟩ := ok_bind h
  obtain ⟨r, s₆, hb, h⟩ := ok_bind h
  obtain ⟨rfl, hs₆⟩ := ok_pure h
  rw [hs₆]
  have hmm : s₁.mach.isEmpty = true := hk.2 ▸ hm
  have sp := splitOut hsp (hw.keeps hk) hD
  have k₄ : Keeps s₂ s₄ := (ok_vty hv₁).trans (ok_vty hv₂)
  have hm₄ : s₄.mach.isEmpty = true := by rw [k₄.2, sp.grows.mach]; exact hmm
  obtain ⟨gV, pV⟩ := IHV c₁ s₄ e s₅ (sp.wf₁.keeps k₄) hm₄ hc
  have wf₂ := sp.wf₂.keeps k₄
  obtain ⟨g, p⟩ := post_bindTm (Γ₁ := liveF c₁) (Γ₂ := liveF c₂) hb pV gV.next
    (fun y hy => by have := sp.wf₁.2 y (mem_liveF.1 hy); have := gV.next; rw [k₄.1] at *; vomega)
    (fun y hy => by have := wf₂.2 y (mem_liveF.1 hy); vomega)
    (fun y hy hy' => sp.disj y (mem_liveF.1 hy') (mem_liveF.1 hy))
    (fun x s₁' b s₂' hx hlt hle hmach hk' => sumE_cont IH₁ IH₂ wf₂ x s₁' b s₂' hx hlt
      (by have := gV.next; vomega) (by rw [hmach, gV.mach]; exact hm₄) hk')
  have := sp.wrap s₆ r ((k₄.grows.trans gV).trans g) (p.lower (by rw [k₄.1]))
  exact ⟨hk.grows.trans this.1, by rw [← hk.1]; exact this.2⟩

end Backend2.Spike670
