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

/-! ### The common shape: split, the left part's value named, the right part's continuation -/

/-- The continuation's contract: with the bound variable `x` fresh and the right part well
formed, it consumes both. -/
def ContSpec (D : Var → Prop) (c₂ : Ctx) (lo : Nat) (k : Var → CM Tm) : Prop :=
  ∀ x s₁ b s₂, x ∉ liveF c₂ → x < s₁.next → lo ≤ s₁.next → s₁.mach.isEmpty = true →
    WF c₂ s₁ → Ok (k x) s₁ b s₂ → Grows s₁ s₂ ∧ PostG D (insert x (liveF c₂)) s₁.next s₂ b

/-- **Split, then `bindTm` of the left part's conversion.** -/
theorem post_split_bind {fuel : Nat} {ctx : Ctx} {u : Masks} {rule : String} {tV : TExpr}
    {T : LTy} {k : Var → CM Tm} {s₁ s₂ sA sB sC s' : CState} {pre : Tm → Tm} {c₁ c₂ : Ctx}
    {e r : Tm}
    (IHV : Spec D (fun c => conv fuel c tV)) (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x)
    (hw : WF ctx s₁) (hm : s₁.mach.isEmpty = true)
    (hsp : Ok (splitCtx ctx u rule) s₁ (pre, c₁, c₂) s₂) (hkA : Keeps s₂ sA)
    (hc : Ok (conv fuel c₁ tV) sA e sB) (hkB : Keeps sB sC) (hb : Ok (bindTm e T k) sC r s')
    (hk : ContSpec D c₂ sB.next k) : Post D ctx s₁ (pre r) s' := by
  have sp := splitOut hsp hw hD
  have hmA : sA.mach.isEmpty = true := by rw [hkA.2, sp.grows.mach]; exact hm
  obtain ⟨gV', pV'⟩ := IHV c₁ sA e sB (sp.wf₁.keeps hkA) hmA hc
  have gV : Grows sA sC := gV'.trans hkB.grows
  have pV : PostG D (liveF c₁) sA.next sC e :=
    ⟨pV'.closed, pV'.nodup, fun y hy => ⟨(pV'.range y hy).1, hkB.1 ▸ (pV'.range y hy).2⟩⟩
  have wf₂ := sp.wf₂.keeps hkA
  obtain ⟨g, p⟩ := post_bindTm (Γ₁ := liveF c₁) (Γ₂ := liveF c₂) hb pV gV.next
    (fun y hy => by have := sp.wf₁.2 y (mem_liveF.1 hy); have := gV.next; rw [hkA.1] at *; vomega)
    (fun y hy => by have := wf₂.2 y (mem_liveF.1 hy); vomega)
    (fun y hy hy' => sp.disj y (mem_liveF.1 hy') (mem_liveF.1 hy))
    (fun x s₁' b s₂' hx hlt hle hmach hk' => hk x s₁' b s₂' hx hlt
      (by have := hkB.1; vomega)
      (by rw [hmach, gV.mach]; exact hmA) (wf₂.grows (gV.trans ⟨hle, hmach⟩)) hk')
  exact sp.wrap s' r ((hkA.grows.trans gV).trans g) (p.lower (by rw [hkA.1]))

/-- A continuation that keeps the counter, then is `conv (some x :: c₂) t`. -/
theorem contSpec_conv {fuel : Nat} {c₂ : Ctx} {t : TExpr} {lo : Nat} {kf : Var → CM Tm}
    (IH : Spec D (fun c => conv fuel c t))
    (hpre : ∀ x s b s₂, Ok (kf x) s b s₂ →
      ∃ s₃, Keeps s s₃ ∧ Ok (conv fuel (some x :: c₂) t) s₃ b s₂) :
    ContSpec D c₂ lo kf := by
  intro x s₁ b s₂ hx hlt hle hm hw h
  obtain ⟨s₃, k, h₂⟩ := hpre _ _ _ _ h
  have hw' : WF (some x :: c₂) s₃ := ⟨by
      rw [live_cons_some]; exact List.nodup_cons.2 ⟨fun hh => hx (mem_liveF.2 hh), hw.1⟩,
    fun z hz => by
      rw [live_cons_some] at hz; rw [k.1]
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hlt
      · exact hw.2 z hz⟩
  obtain ⟨g, p⟩ := IH _ s₃ b s₂ hw' (by rw [k.2]; exact hm) h₂
  rw [liveF_cons_some] at p
  exact ⟨k.grows.trans g, p.lower (by rw [k.1])⟩

/-! ### The split nodes -/

/-- **`bind`** (`convBind`): `x <- M; N`. -/
theorem node_bind {fuel : Nat} {ctx : Ctx} {info j A C u tM tN} {s s' : CState} {tm : Tm}
    (IHM : Spec D (fun c => conv fuel c tM)) (IHN : Spec D (fun c => conv fuel c tN))
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.bind info j A C u tM tN)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  simp only [convBind] at h
  obtain ⟨⟨pre, c₁, c₂⟩, s₂, hsp, h⟩ := ok_bind h
  obtain ⟨e, s₃, hc, h⟩ := ok_bind h
  obtain ⟨aT, s₄, hv, h⟩ := ok_bind h
  obtain ⟨r, s₅, hb, h⟩ := ok_bind h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have k₄ := ok_vty hv
  have := post_split_bind IHM hD (hw.keeps hk) hm₁ hsp (Keeps.refl _) hc k₄ hb
    (contSpec_conv IHN fun x s b s₂ h => by
      split at h
      · obtain ⟨_, s₆, h₁, h₂⟩ := ok_bind h
        obtain ⟨_, s₇, h₃, h₄⟩ := ok_bind h₂
        refine ⟨s₇, (show Keeps _ _ from ok_readFact h₁).trans ?_, h₄⟩
        rw [ok_modify h₃]; exact ⟨rfl, rfl⟩
      · exact ⟨s, Keeps.refl _, h⟩)
  exact ⟨hk.grows.trans this.1, by rw [← hk.1]; exact this.2⟩

/-- `x` bound, then `drop`-free use: the continuation `b` given, with `x` consumed by its own
rule. A helper for the binder rules below: `PostG` at `insert x Γ` from the body's `PostG` at the
body's own context. -/
theorem wf_cons {c : Ctx} {x : Var} {s : CState} (hw : WF c s) (hx : x ∉ liveF c)
    (hlt : x < s.next) : WF (some x :: c) s :=
  ⟨by rw [live_cons_some]; exact List.nodup_cons.2 ⟨fun hh => hx (mem_liveF.2 hh), hw.1⟩,
   fun z hz => by
     rw [live_cons_some] at hz
     rcases List.mem_cons.1 hz with rfl | hz
     · exact hlt
     · exact hw.2 z hz⟩

/-- **`unitE`**: `let () = V; M`. -/
theorem node_unitE {fuel : Nat} {ctx : Ctx} {info j C u tV tM} {s s' : CState} {tm : Tm}
    (IHV : Spec D (fun c => conv fuel c tV)) (IHM : Spec D (fun c => conv fuel c tM))
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.unitE info j C u tV tM)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨⟨pre, c₁, c₂⟩, s₂, hsp, h⟩ := ok_bind h
  obtain ⟨e, s₃, hc, h⟩ := ok_bind h
  obtain ⟨r, s₅, hb, h⟩ := ok_bind h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := post_split_bind IHV hD (hw.keeps hk) hm₁ hsp (Keeps.refl _) hc (Keeps.refl _) hb ?_
  · exact ⟨hk.grows.trans this.1, by rw [← hk.1]; exact this.2⟩
  intro v sa b sb hv hlt hle hma hwa h
  obtain ⟨bM, sc, h₁, h₂⟩ := ok_bind h
  obtain ⟨rfl, hsb⟩ := ok_pure h₂
  rw [hsb]
  obtain ⟨g, ⟨⟨Δ, l, cl⟩, nd, rg⟩⟩ := IHM c₂ sa bM sc hwa hma h₁
  refine ⟨g, ⟨⟨Δ, .drop (by simp) (by rw [Finset.erase_insert hv]; exact l), cl⟩, nd, rg⟩⟩

/-- **`zeroE`**: `absurd V`; the right part is never reached. -/
theorem node_zeroE {fuel : Nat} {ctx : Ctx} {info j C u tV} {s s' : CState} {tm : Tm}
    (IHV : Spec D (fun c => conv fuel c tV))
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.zeroE info j C u tV)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨⟨pre, c₁, c₂⟩, s₂, hsp, h⟩ := ok_bind h
  obtain ⟨e, s₃, hc, h⟩ := ok_bind h
  obtain ⟨r, s₅, hb, h⟩ := ok_bind h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := post_split_bind IHV hD (hw.keeps hk) hm₁ hsp (Keeps.refl _) hc (Keeps.refl _) hb ?_
  · exact ⟨hk.grows.trans this.1, by rw [← hk.1]; exact this.2⟩
  intro v sa b sb hv hlt hle hma hwa h
  obtain ⟨rfl, rfl⟩ := ok_pure h
  exact ⟨Grows.refl _, ⟨⟨none, .absurd (by simp), .inl rfl⟩, by simp [bnd], by simp [bnd]⟩⟩

/-- **`tensorE`**: `let (x, y) = V; M`. -/
theorem node_tensorE {fuel : Nat} {ctx : Ctx} {info j A B C u tV tM} {s s' : CState} {tm : Tm}
    (IHV : Spec D (fun c => conv fuel c tV)) (IHM : Spec D (fun c => conv fuel c tM))
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.tensorE info j A B C u tV tM)) s tm s') :
    Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨⟨pre, c₁, c₂⟩, s₂, hsp, h⟩ := ok_bind h
  obtain ⟨aT, s₃, hv₁, h⟩ := ok_bind h
  obtain ⟨bT, s₄, hv₂, h⟩ := ok_bind h
  obtain ⟨e, s₅, hc, h⟩ := ok_bind h
  obtain ⟨r, s₆, hb, h⟩ := ok_bind h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := post_split_bind IHV hD (hw.keeps hk) hm₁ hsp ((ok_vty hv₁).trans (ok_vty hv₂)) hc
    (Keeps.refl _) hb ?_
  · exact ⟨hk.grows.trans this.1, by rw [← hk.1]; exact this.2⟩
  intro p sa b sb hp hlt hle hma hwa h
  obtain ⟨x, sx, hx, h⟩ := ok_bind h
  obtain ⟨rfl, hxn, hxm⟩ := ok_fresh hx
  obtain ⟨y, sy, hy, h⟩ := ok_bind h
  obtain ⟨rfl, hyn, hym⟩ := ok_fresh hy
  obtain ⟨bM, sc, h₁, h₂⟩ := ok_bind h
  obtain ⟨rfl, hsb⟩ := ok_pure h₂
  rw [hsb]
  have hxc : sa.next ∉ liveF c₂ := fun hh => by have := hwa.2 _ (mem_liveF.1 hh); vomega
  have hyc : sx.next ∉ liveF c₂ := fun hh => by have := hwa.2 _ (mem_liveF.1 hh); vomega
  have hw' : WF (some sx.next :: some sa.next :: c₂) sy :=
    wf_cons (wf_cons (hwa.grows ⟨by vomega, hym.trans hxm⟩) hxc (by vomega))
      (by rw [liveF_cons_some]; simp only [Finset.mem_insert, not_or]; exact ⟨by vomega, hyc⟩)
      (by vomega)
  obtain ⟨g, ⟨⟨Δ, l, cl⟩, nd, rg⟩⟩ := IHM _ sy bM sc hw' (by rw [hym, hxm]; exact hma) h₁
  rw [liveF_cons_some, liveF_cons_some] at l
  have gn := g.next
  refine ⟨⟨by vomega, by rw [g.mach, hym, hxm]⟩, ⟨⟨Δ, .letpair (by simp) ?_, cl⟩, ?_, ?_⟩⟩
  · rw [Finset.erase_insert hp]; exact l
  · simp only [bnd, List.nodup_cons]
    exact ⟨fun hh => by
        simp at hh; rcases hh with hh | hh
        · vomega
        · have := (rg _ hh).1; vomega,
      fun hh => by have := (rg _ hh).1; vomega, nd⟩
  · intro z hz
    simp only [bnd, List.mem_cons] at hz
    rcases hz with rfl | rfl | hz
    · exact ⟨le_refl _, by vomega⟩
    · exact ⟨by vomega, by vomega⟩
    · have := rg z hz; exact ⟨by vomega, this.2⟩

/-- **`tensorI`**: `(V₁, V₂)`, each part's value named. -/
theorem node_tensorI {fuel : Nat} {ctx : Ctx} {info j A B u t₁ t₂} {s s' : CState} {tm : Tm}
    (IH₁ : Spec D (fun c => conv fuel c t₁)) (IH₂ : Spec D (fun c => conv fuel c t₂))
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.tensorI info j A B u t₁ t₂)) s tm s') :
    Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨⟨pre, c₁, c₂⟩, s₂, hsp, h⟩ := ok_bind h
  obtain ⟨rT, s₃, hr, h⟩ := ok_bind h
  split at h
  swap; · exact (ok_throw h).elim
  rename_i aT bT
  obtain ⟨e, s₅, hc, h⟩ := ok_bind h
  obtain ⟨r, s₆, hb, h⟩ := ok_bind h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := post_split_bind IH₁ hD (hw.keeps hk) hm₁ hsp (ok_repJ hr) hc (Keeps.refl _) hb ?_
  · exact ⟨hk.grows.trans this.1, by rw [← hk.1]; exact this.2⟩
  intro a sa b sb ha hlt hle hma hwa h
  obtain ⟨e₂, sc, h₁, h₂⟩ := ok_bind h
  obtain ⟨g₂, p₂⟩ := IH₂ c₂ sa e₂ sc hwa hma h₁
  obtain ⟨g, p⟩ := post_bindTm (Γ₁ := liveF c₂) (Γ₂ := {a}) h₂ p₂ g₂.next
    (fun y hy => by have := hwa.2 y (mem_liveF.1 hy); have := g₂.next; vomega)
    (fun y hy => by simp at hy; subst hy; exact hlt)
    (fun y hy hy' => by simp at hy; subst hy; exact ha hy')
    (fun bv sd bt se hbv hlt' hle' hmd hkd => by
      obtain ⟨rfl, hse⟩ := ok_pure hkd
      rw [hse]
      have hab : a ≠ bv := fun e => hbv (by simp [e])
      refine ⟨Grows.refl _, ?_⟩
      have := postG_ops (D := D) (lo := sd.next) (s' := sd) (t := .pair a bv) rfl
        (by simp [hab])
      convert this using 1
      ext z; simp [or_comm])
  refine ⟨g₂.trans g, ?_⟩
  convert p using 1
  ext z; simp [or_comm]

/-! ### Leaves, injections, erased nodes -/

theorem postG_unit {lo : Nat} {s' : CState} : PostG D ∅ lo s' .unit := by
  simpa using (postG_ops (D := D) (xs := []) (lo := lo) (s' := s') (t := .unit) rfl List.nodup_nil)

theorem postG_lit {lo : Nat} {s' : CState} {c : BoCa.IntLit} : PostG D ∅ lo s' (.lit c) := by
  simpa using (postG_ops (D := D) (xs := []) (lo := lo) (s' := s') (t := .lit c) rfl
    List.nodup_nil)

/-- **`unitI`**: `()`, every live slot dropped. -/
theorem node_unitI {fuel : Nat} {ctx : Ctx} {info j} {s s' : CState} {tm : Tm}
    (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.unitI info j)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := post_leaf_none (D := D) (hw.keeps hk) postG_unit
  exact ⟨hk.grows, by rw [← hk.1]; exact this.2⟩

/-- **`lit`**: a literal, every live slot dropped. -/
theorem node_lit {fuel : Nat} {ctx : Ctx} {info j c} {s s' : CState} {tm : Tm}
    (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.lit info j c)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  have := post_leaf_none (D := D) (hw.keeps hk) (postG_lit (c := c))
  exact ⟨hk.grows, by rw [← hk.1]; exact this.2⟩

/-- **`sumI₁`**: `inl V`. -/
theorem node_sumI₁ {fuel : Nat} {ctx : Ctx} {info j A B c} {s s' : CState} {tm : Tm}
    (IH : Spec D (fun c' => conv fuel c' c)) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.sumI₁ info j A B c)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨rT, s₂, hr, h⟩ := ok_bind h
  split at h
  swap; · exact (ok_throw h).elim
  obtain ⟨e, s₃, hc, h⟩ := ok_bind h
  have k₂ := ok_repJ hr
  obtain ⟨g, p⟩ := IH ctx s₂ e s₃ (hw.keeps (hk.trans k₂)) (by rw [k₂.2]; exact hm₁) hc
  obtain ⟨g', p'⟩ := post_bindTm (Γ₁ := liveF ctx) (Γ₂ := ∅) h p g.next
    (fun y hy => by have := hw.2 y (mem_liveF.1 hy); have := g.next; rw [k₂.1, hk.1] at *; vomega)
    (by simp) (by simp)
    (fun x sd b se _ _ _ _ hkd => by
      obtain ⟨rfl, hse⟩ := ok_pure hkd
      rw [hse]
      refine ⟨Grows.refl _, ?_⟩
      simpa using (postG_ops (D := D) (xs := [x]) (lo := sd.next) (s' := sd)
        (t := .inj false x) rfl (List.nodup_singleton x)))
  refine ⟨(hk.grows.trans k₂.grows).trans (g.trans g'), ?_⟩
  simpa [k₂.1, hk.1] using p'

/-- **`allE`**: an instantiation is its operand. -/
theorem node_allE {fuel : Nat} {ctx : Ctx} {info j x b S C c} {s s' : CState} {tm : Tm}
    (IH : Spec D (fun c' => conv fuel c' c)) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.allE info j x b S C c)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨_, s₂, hr, h⟩ := ok_bind h
  have k₂ : Keeps s₁ s₂ := ok_readFact hr
  obtain ⟨g, p⟩ := IH ctx s₂ tm s' (hw.keeps (hk.trans k₂)) (by rw [k₂.2]; exact hm₁) h
  exact ⟨(hk.trans k₂).grows.trans g, by rw [← (hk.trans k₂).1]; exact p⟩

/-- **`allI`**: `Λ. M` is `M`, at the binder's dead slot. -/
theorem node_allI {fuel : Nat} {ctx : Ctx} {info j x b S C c} {s s' : CState} {tm : Tm}
    (IH : Spec D (fun c' => conv fuel c' c)) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.allI info j x b S C c)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  split at h
  swap; · obtain ⟨_, _, h', _⟩ := ok_bind h; exact (ok_throw h').elim
  obtain ⟨_, s₃, hr, h⟩ := ok_bind h
  have k₃ : Keeps s₁ s₃ := ok_readFact hr
  have hw' : WF (none :: ctx) s₃ := by
    have := hw.keeps (hk.trans k₃); exact ⟨by rw [live_cons_none]; exact this.1,
      fun y hy => this.2 y (by rwa [live_cons_none] at hy)⟩
  obtain ⟨g, p⟩ := IH _ s₃ tm s' hw' (by rw [k₃.2]; exact hm₁) h
  rw [liveF_cons_none] at p
  exact ⟨(hk.trans k₃).grows.trans g, by rw [← (hk.trans k₃).1]; exact p⟩

/-- **`nilDead`**: the term at the empty context, every live slot dropped. -/
theorem node_nilDead {fuel : Nat} {ctx : Ctx} {info j j' c} {s s' : CState} {tm : Tm}
    (IH : Spec D (fun c' => conv fuel c' c)) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.nilDead info j j' c)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨_, s₂, hr, h⟩ := ok_bind h
  have k₂ : Keeps s₁ s₂ := ok_readFact hr
  obtain ⟨e, s₃, hc, h⟩ := ok_bind h
  obtain ⟨rfl, hs⟩ := ok_pure h
  rw [hs]
  obtain ⟨g, p⟩ := IH [] s₂ e s₃ ⟨List.nodup_nil, by simp [live]⟩ (by rw [k₂.2]; exact hm₁) hc
  have := post_drops hw.1 (by simp [liveF, live]) p
  refine ⟨(hk.trans k₂).grows.trans g, ?_⟩
  rw [← (hk.trans k₂).1]
  simpa [liveF, live] using this

/-! ### `app`: the argument read from the right part, the function from the left -/

/-- `leaf c (some i) b` at a larger owned set: `b` consumes slot `i`'s variable and `Γ`. -/
theorem postG_leaf_some {cc : Ctx} {i : Nat} {x : Var} {Γ : Finset Var} {lo : Nat} {s' : CState}
    {b : Tm} (hn : (live cc).Nodup) (hx : cc[i]? = some (some x)) (hΓ : ∀ y ∈ Γ, y ∉ live cc)
    (hb : PostG D (insert x Γ) lo s' b) : PostG D (liveF cc ∪ Γ) lo s' (leaf cc (some i) b) := by
  obtain ⟨n, hxo, hiff⟩ := leaf_others hx hn
  have := post_drops n (fun y hy h => by
    rcases Finset.mem_insert.1 h with rfl | h
    · exact hxo hy
    · exact hΓ y h ((hiff y).2 (.inl hy))) hb
  convert this using 1
  · ext y; simp only [Finset.mem_union, mem_liveF, hiff y, Finset.mem_insert, List.mem_toFinset]
    tauto
  · rfl

/-- **`app`**: `M x`. A λ in function position is its body at the argument (no closure made);
otherwise the closure is made and called. -/
theorem node_app {fuel : Nat} {ctx : Ctx} {info j i A C u tM} {s s' : CState} {tm : Tm}
    (IHM : Spec D (fun c => conv fuel c tM))
    (IHB : ∀ i' j' A' C' body, headOf 64 tM = .lam i' j' A' C' body →
      Spec D (fun c => conv fuel c body))
    (hD : ∀ x ∈ bothVars (ctx.zip u.ms), D x) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.app info j i A C u tM)) s tm s') : Post D ctx s tm s' := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨⟨pre, c₁, c₂⟩, s₂, hsp, h⟩ := ok_bind h
  have sp := splitOut hsp (hw.keeps hk) hD
  have hm₂ : s₂.mach.isEmpty = true := by rw [sp.grows.mach]; exact hm₁
  split at h
  swap; · exact (ok_throw h).elim
  rename_i x hx
  have hxc₂ : x ∈ live c₂ := by
    simp only [live, List.mem_filterMap, id]; exact ⟨_, List.mem_of_getElem? hx, rfl⟩
  have hxc₁ : x ∉ liveF c₁ := fun hh => sp.disj x (mem_liveF.1 hh) hxc₂
  have hc₁ : ∀ y ∈ liveF c₁, y ∉ live c₂ := fun y hy => sp.disj y (mem_liveF.1 hy)
  -- The term `X` consumes `x` and the left part; `leaf` drops the rest of the right part.
  suffices H : ∃ X s₃, Ok (pure (pre (leaf c₂ (some i) X)) : CM Tm) s₃ tm s' ∧ Grows s₂ s₃ ∧
      PostG D (insert x (liveF c₁)) s₂.next s₃ X by
    obtain ⟨X, s₃, hp, g, pX⟩ := H
    obtain ⟨rfl, hs⟩ := ok_pure hp
    rw [hs]
    have := sp.wrap s₃ _ g (by
      have := postG_leaf_some (cc := c₂) sp.wf₂.1 hx hc₁ pX
      rwa [Finset.union_comm] at this)
    exact ⟨hk.grows.trans this.1, by rw [← hk.1]; exact this.2⟩
  split at h
  · rename_i i' j' A' C' body hh
    obtain ⟨e, s₃, hc, h⟩ := ok_bind h
    obtain ⟨g, p⟩ := IHB i' j' A' C' body hh _ s₂ e s₃
      (wf_cons sp.wf₁ hxc₁ (sp.wf₂.2 x hxc₂)) hm₂ hc
    rw [liveF_cons_some] at p
    exact ⟨e, s₃, h, g, p⟩
  · obtain ⟨fT, s₃, hr, h⟩ := ok_bind h
    obtain ⟨f, s₄, hf, h⟩ := ok_bind h
    obtain ⟨rfl, hfn, hfm⟩ := ok_fresh hf
    obtain ⟨e, s₅, hc, h⟩ := ok_bind h
    have k₃ := ok_repJ hr
    obtain ⟨g, p⟩ := IHM c₁ s₄ e s₅ (sp.wf₁.grows ⟨by rw [hfn, k₃.1]; vomega, hfm.trans k₃.2⟩)
      (by rw [hfm, k₃.2]; exact hm₂) hc
    have hxs : x < s₂.next := sp.wf₂.2 x hxc₂
    have gn := g.next
    refine ⟨_, s₅, h, (k₃.grows.trans ⟨by vomega, hfm⟩).trans g, ?_⟩
    have happ : PostG D (insert s₃.next {x}) s₄.next s₅ (.app s₃.next x) := by
      have := postG_ops (D := D) (lo := s₄.next) (s' := s₅) (t := .app s₃.next x)
        (xs := [s₃.next, x]) rfl (by simp; intro e; rw [k₃.1] at e; vomega)
      convert this using 1; simp
    refine ⟨?_, ?_, ?_⟩
    · have := LinL.letv_closed (x := s₃.next) p.closed happ.closed (Γ₂ := {x})
        (fun y hy => by
          simp at hy; subst hy
          exact ⟨hxc₁, fun hb => by have := (p.range _ hb).1; rw [hfn, k₃.1] at this; vomega⟩)
      convert this using 1; ext z; simp [or_comm]
    · simp only [bnd, List.nodup_cons, List.append_nil]
      exact ⟨fun hb => by have := (p.range _ hb).1; vomega, p.nodup⟩
    · intro z hz
      simp only [bnd, List.mem_cons, List.append_nil] at hz
      rcases hz with rfl | hz
      · exact ⟨by rw [k₃.1], by vomega⟩
      · have := p.range z hz; exact ⟨by rw [k₃.1] at *; vomega, this.2⟩

end Backend2.Spike670
