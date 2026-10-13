import ProbeD1.R1Owed

/-!
# ProbeD1 — the persistence box: a persistent thunk at every instantiation and reserved-name push

`vRLM`'s `!` clause reads a persistent thunk at every instantiation of the stack, every list the
instantiated lifetimes keep outside, and every finite sequence of own pushes at the empty resource
under reserved names (`PBox`, `BoxStep`, `R1.lean`). No `binder0` clause pushes under a reserved
name: the pushes are a new reach of the `!` clause. This file proves what the box needs and
gives.

* **The world facts** (`BoxIdx`, `boxIdx_inst`, `boxIdx_steps`): an index `SemSM` reads stays one
  along an instantiation and along the box's pushes, every pushed entry under a reserved name.
  `StackJBase` follows at every judgement scoped in `Δ` (`stackJBase_of_boxIdx`), and `StackJ`
  where the stack's variables are distinct (`stackJ_of_boxIdx`).
* **The box is transitive** (`boxSteps_inst`, `pBox_worldB`): the box's pushes instantiated are
  pushes at the instantiated reading, and an instantiation of an instantiated stack is one of the
  stack (`instComp`); at the empty stack, the instantiation of a pushed stack fixes the reading.
  So a value in the box at a stack is in the box at every world the box reaches.
* **A persistent context is carried to every box world** (`gRLM_boxWorld`): a persistent thunk by
  its box, persistent data reaching no `U` by the thaw at the empty resource and the `U`-free push.
* **The two `!U` introductions** (`bangThunkFRowM`, `bangThunkVRowM`, `statement0UFullM`): the
  thunk at every box world is the `U` row's conclusion there, from the premise at that world with
  the persistent context carried there. The rows take the context to be carried by the box
  (`PersistentBoxed`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)
open BoCa.BoLo (Step1N Head)

/-! ### Readings -/

/-- A variable the reading does not bind is no key of its list. -/
theorem not_key_of_find_none {δ : LSub} {x : LifeVar} (h : δ.find? x = none) :
    ∀ p ∈ δ.entries, p.1 ≠ x := by
  obtain ⟨l⟩ := δ
  induction l with
  | nil => intro p hp; simp at hp
  | cons q t ih =>
      intro p hp
      have h' : (if q.1 = x then some q.2 else BoCa.Lifetime.assocFind x t) = none := h
      split at h'
      · exact absurd h' (by simp)
      · rename_i hq
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hq
        · exact ih h' p hp

/-- **No binding was made before a variable the reading does not bind.** -/
theorem boundBefore_of_find_none {δ : LSub} {x : LifeVar} (h : δ.find? x = none) :
    boundBefore x δ = [] := by
  unfold boundBefore
  have hall : ∀ p ∈ δ.entries, (p.1 != x) = true := fun p hp => by
    simpa using not_key_of_find_none h p hp
  rw [List.dropWhile_eq_nil_iff.mpr hall]
  rfl

/-- **A lifetime term that has a value does not mention a variable the reading does not bind.** -/
theorem mentions_false_of_interp {s : LSub} {z : LifeVar} (hz : s.find? z = none) :
    ∀ (u : Lifetime.Life) (n : ℕ), u.interp s = some n → u.mentions z = false
  | .var y, n, h => by
      simp only [Lifetime.Life.mentions, beq_eq_false_iff_ne]
      rintro rfl
      rw [Lifetime.Life.interp_var, hz] at h
      exact absurd h (by simp)
  | .top, _, _ => rfl
  | .join a b, n, h => by
      simp only [Lifetime.Life.interp] at h
      cases ha : a.interp s with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some m =>
          cases hb : b.interp s with
          | none => rw [ha, hb] at h; exact absurd h (by simp)
          | some k =>
              simp only [Lifetime.Life.mentions, Bool.or_eq_false_iff]
              exact ⟨mentions_false_of_interp hz a m ha, mentions_false_of_interp hz b k hb⟩
  | .meet a b, n, h => by
      simp only [Lifetime.Life.interp] at h
      cases ha : a.interp s with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some m =>
          cases hb : b.interp s with
          | none => rw [ha, hb] at h; exact absurd h (by simp)
          | some k =>
              simp only [Lifetime.Life.mentions, Bool.or_eq_false_iff]
              exact ⟨mentions_false_of_interp hz a m ha, mentions_false_of_interp hz b k hb⟩

/-- **`Δ`'s models survive binding a variable the reading did not bind**: such a variable is no
variable of `Δ`, and no bound of `Δ` that has a value mentions it. -/
theorem models_extend_fresh {Δ : LifeCtx} {s : LSub} {z : LifeVar} {a : Life}
    (hMod : Δ.Models s) (hz : s.find? z = none) : Δ.Models (s.extend z a) := by
  intro y u hy
  obtain ⟨m, n, hm, hn, hl⟩ := hMod y u hy
  have hzy : z ≠ y := by rintro rfl; rw [hz] at hm; exact absurd hm (by simp)
  refine ⟨m, n, by rw [find?_extend_ne _ _ hzy]; exact hm, ?_, hl⟩
  rw [interp_extend_of_not_mentions (mentions_false_of_interp hz u n hn)]
  exact hn

/-- A variable of `Δ` is read by every reading that models `Δ`. -/
theorem find_some_of_models {Δ : LifeCtx} {s : LSub} {y : LifeVar} {u : Lifetime.Life}
    (hMod : Δ.Models s) (hy : Δ.find? y = some u) : s.find? y ≠ none := by
  obtain ⟨m, -, hm, -⟩ := hMod y u hy
  rw [hm]; simp

/-- **A box step's variable is no variable of `Δ`**: the stack's reading does not read it. -/
theorem delta_none_of_fresh {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life} {x : LifeVar}
    (hMod : Δ.Models (extS δ σ αs)) (hσ : x ∉ σ.map LEnt.x) (hδ : δ.find? x = none) :
    Δ.find? x = none := by
  cases hΔ : Δ.find? x with
  | none => rfl
  | some u =>
      exact absurd (by rw [extS_find_not_mem δ σ αs x hσ, hδ]) (find_some_of_models hMod hΔ)

/-- A variable the pushed stack's reading binds, other than the pushed one, is the stack's or the
reading's. -/
theorem find_push_cases {δ : LSub} {σ : LStack} {αs : List Life} {e : LEnt} {a : Life}
    {y : LifeVar} (h : (extS δ (e :: σ) (a :: αs)).find? y ≠ none) (hy : e.x ≠ y) :
    y ∈ σ.map LEnt.x ∨ δ.find? y ≠ none := by
  rw [extS_push_find δ e σ a αs hy] at h
  by_cases hm : y ∈ σ.map LEnt.x
  · exact Or.inl hm
  · exact Or.inr (by rwa [extS_find_not_mem δ σ αs y hm] at h)

/-- **An instantiation keeps a lend fresh below the reading.** -/
theorem subFresh_inst {δ : LSub} {a : Life} (ι : Inst) (h : SubFresh δ a) :
    SubFresh (ι.sub δ) (ι.life1 a) := by
  rcases ι with _ | ⟨c, θ⟩
  · exact h
  · intro p hp
    simp only [Inst.sub, Restrat.LSub.mapN, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    show θ a < OrderDual.toDual (θ.toNat q.2)
    rw [Restrat.Emb.toNat_toDual]
    exact θ.lt_iff.mpr (h q hq)

/-- An instantiation keeps a variable unread. -/
theorem find_sub_none {δ : LSub} {x : LifeVar} (ι : Inst) (h : δ.find? x = none) :
    (ι.sub δ).find? x = none := by
  rw [Inst.find?_sub, h]; rfl

/-! ### One box step -/

/-- **A box step, unfolded.** -/
theorem boxStep_inv {δ : LSub} {ls : List SRec} {s s' : Stk} (h : BoxStep δ ls s s') :
    ∃ (e : LEnt) (a : Life), s' = (e :: s.1, a :: s.2) ∧ OwnOKI δ s.1 s.2 e a PMap.empty ∧
      a < ⊤ ∧ NsVar e.x ∧ δ.find? e.x = none ∧ ¬ VFree e.x e.T ∧ RecsOutside (a :: s.2) ls ∧
      SubFresh δ a := by
  cases h with
  | push e a hok htop hns hδ hself hro hsf => exact ⟨e, a, rfl, hok, htop, hns, hδ, hself, hro, hsf⟩

/-- **A box sequence only pushes**: the stack it reaches is its start with entries in front, and
the lifetimes likewise, one per entry. -/
theorem boxSteps_append {δ : LSub} {ls : List SRec} {s s' : Stk}
    (h : Relation.ReflTransGen (BoxStep δ ls) s s') :
    ∃ (τ : LStack) (αt : List Life), αt.length = τ.length ∧ s'.1 = τ ++ s.1 ∧ s'.2 = αt ++ s.2 := by
  induction h with
  | refl => exact ⟨[], [], rfl, rfl, rfl⟩
  | tail _ hst ih =>
      obtain ⟨τ, αt, hl, h₁, h₂⟩ := ih
      obtain ⟨e, a, rfl, -⟩ := boxStep_inv hst
      exact ⟨e :: τ, a :: αt, by simp [hl], by simp [h₁], by simp [h₂]⟩

/-! ### The index facts along the box -/

/-- **The index facts a box world keeps**, at `Δ`: the stack in shape (blocks admitted) and below
`⊤`, the records outside the lends, the reading's bindings outside them, `Δ`'s models, every entry
named by a variable of `Δ` or by a reserved name, and every payload type reading `Δ`'s variables or
the stack's. -/
structure BoxIdx (Δ : LifeCtx) (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) :
    Prop where
  ok : StackOKB σ αs
  ob : OuterBelowTop αs
  ro : RecsOutside αs ls
  so : SubOutside σ αs δ
  md : Δ.Models (extS δ σ αs)
  kind : ∀ e ∈ σ, (∃ u, Δ.find? e.x = some u) ∨ NsVar e.x
  pay : ∀ e ∈ σ, ∀ y, VFree y e.T → (∃ u, Δ.find? y = some u) ∨ y ∈ σ.map LEnt.x

/-- **The index facts at an instantiation.** -/
theorem boxIdx_inst {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life} {ls ls' : List SRec}
    {ι : Inst} (h : BoxIdx Δ δ σ αs ls) (hro : RecsOutside (ι.life αs) ls') :
    BoxIdx Δ (ι.sub δ) σ (ι.life αs) ls' :=
  ⟨h.ok.inst ι, outerBelowTop_inst ι h.ob, hro, subOutsideInst σ αs δ ι h.so,
    instModels Δ δ σ αs ι h.md, h.kind, h.pay⟩

/-- **The index facts along one box step**, the reading mapping only `Δ`'s variables. -/
theorem boxIdx_step {Δ : LifeCtx} {δ : LSub} {ls : List SRec} {σ σ' : LStack}
    {αs αs' : List Life} (hSD : SubDom δ Δ) (h : BoxIdx Δ δ σ αs ls)
    (hst : BoxStep δ ls (σ, αs) (σ', αs')) : BoxIdx Δ δ σ' αs' ls := by
  obtain ⟨e, a, he, hok, htop, hns, hδ, hself, hro, hsf⟩ := boxStep_inv hst
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hΔe : Δ.find? e.x = none := delta_none_of_fresh h.md hok.var hδ
  refine ⟨stackOKB_push h.ok hok.chain hok.var, ?_, hro, ?_, ?_, ?_, ?_⟩
  · intro o ho
    cases hαs : αs with
    | nil => rw [hαs] at ho; simp at ho; subst ho; exact htop
    | cons b bs =>
        rw [hαs] at ho
        exact h.ob o (by rw [hαs]; simpa [List.getLast?_cons_cons] using ho)
  · intro e' a' hm p hp
    rcases List.mem_cons.mp hm with he' | hm
    · simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      rw [boundBefore_of_find_none hδ] at hp; simp at hp
    · exact h.so e' a' hm p hp
  · exact models_extend_fresh h.md (by rw [extS_find_not_mem δ σ αs e.x hok.var, hδ])
  · intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact Or.inr hns
    · exact h.kind e' he'
  · intro e' he' y hy
    rcases List.mem_cons.mp he' with rfl | he'
    · have hyx : e'.x ≠ y := fun h' => hself (h' ▸ hy)
      rcases find_push_cases (hok.pay y hy) hyx with hm | hd
      · exact Or.inr (List.mem_cons_of_mem _ hm)
      · obtain ⟨u, hu⟩ := hSD y hd
        exact Or.inl ⟨u, hu⟩
    · rcases h.pay e' he' y hy with hu | hm
      · exact Or.inl hu
      · exact Or.inr (List.mem_cons_of_mem _ hm)

/-- **The index facts along a box sequence.** -/
theorem boxIdx_steps {Δ : LifeCtx} {δ : LSub} {ls : List SRec} (hSD : SubDom δ Δ) {s s' : Stk}
    (hst : Relation.ReflTransGen (BoxStep δ ls) s s') (h : BoxIdx Δ δ s.1 s.2 ls) :
    BoxIdx Δ δ s'.1 s'.2 ls := by
  induction hst with
  | refl => exact h
  | tail _ hst₁ ih => exact boxIdx_step hSD ih hst₁

/-- **`StackJBase` at a box world**: every entry is of `StackJ`'s first two kinds, a reserved name
off `Δ` being read by no type scoped in `Δ`. -/
theorem stackJBase_of_boxIdx {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life}
    {ls : List SRec} {Γ : Ctx VTy} {C : CTy} (h : BoxIdx Δ δ σ αs ls) (hSc : Scoped Δ Γ C) :
    StackJBase σ αs δ Δ Γ C := by
  refine ⟨h.pay, fun e he => ?_⟩
  rcases h.kind e he with hΔ | hns
  · exact Or.inl hΔ
  · by_cases hΔ : ∃ u, Δ.find? e.x = some u
    · exact Or.inl hΔ
    · have hΔ' : Δ.find? e.x = none := by
        cases h' : Δ.find? e.x with
        | none => rfl
        | some u => exact absurd ⟨u, h'⟩ hΔ
      refine Or.inr (Or.inl ⟨hns, hΔ', fun hC => ?_, fun s hs hl hv => ?_⟩)
      · exact hΔ (hSc.1 e.x hC)
      · exact hΔ (hSc.2 s hs hl e.x hv)

/-- **`StackJ` at a box world whose stack has distinct variables** (`StackJBaseIff`). -/
theorem stackJ_of_boxIdx {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    {Γ : Ctx VTy} {C : CTy} (h : BoxIdx Δ δ σ αs ls) (hSc : Scoped Δ Γ C)
    (hnd : (σ.map LEnt.x).Nodup) : StackJ σ αs δ Δ Γ C :=
  ((stackJBaseIff σ αs δ Δ Γ C hnd).1).mp (stackJBase_of_boxIdx h hSc)

/-- **A box step's variable is no variable of `Δ`, so no type scoped in `Δ` reads it.** -/
theorem boxStep_var_off {Δ : LifeCtx} {δ : LSub} {ls : List SRec} {σ σ' : LStack}
    {αs αs' : List Life} (h : BoxIdx Δ δ σ αs ls) (hst : BoxStep δ ls (σ, αs) (σ', αs')) :
    ∃ (e : LEnt) (a : Life), σ' = e :: σ ∧ αs' = a :: αs ∧ Δ.find? e.x = none ∧
      e.x ∉ σ.map LEnt.x ∧ δ.find? e.x = none ∧ OwnOKI δ σ αs e a PMap.empty ∧
      SubFresh δ a ∧ RecsOutside (a :: αs) ls := by
  obtain ⟨e, a, he, hok, -, -, hδ, -, hro, hsf⟩ := boxStep_inv hst
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨e, a, rfl, rfl, delta_none_of_fresh h.md hok.var hδ, hok.var, hδ, hok, hsf, hro⟩

/-! ### The box is transitive -/

/-- `RecsOutside` at a vector gives it at a suffix. -/
theorem recsOutside_suffix {αt αs : List Life} {ls : List SRec}
    (h : RecsOutside (αt ++ αs) ls) : RecsOutside αs ls :=
  fun a ha => h a (List.mem_append_right _ ha)

/-- **A box step instantiated is a box step at the instantiated reading**: an instantiation is
strictly monotone, so the push stays below the stack and fresh below the reading. -/
theorem boxStep_inst {δ : LSub} {ls ls' : List SRec} {σ σ' : LStack} {αs αs' : List Life}
    (ι : Inst) (hst : BoxStep δ ls (σ, αs) (σ', αs')) (hro : RecsOutside (ι.life αs') ls') :
    BoxStep (ι.sub δ) ls' (σ, ι.life αs) (σ', ι.life αs') := by
  obtain ⟨e, a, he, hok, htop, hns, hδ, hself, -, hsf⟩ := boxStep_inv hst
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hok' : OwnOKI (ι.sub δ) σ (ι.life αs) e (ι.life1 a) PMap.empty :=
    ⟨⟨List.isChain_map_of_isChain _ (fun _ _ h => ι.life1_lt_iff.mpr h) hok.chain,
      ResU.inStratum_empty _, hok.var, hok.place, fun y hy => by
        have h := hok.pay y hy
        show (extS (ι.sub δ) (e :: σ) (ι.life (a :: αs))).find? y ≠ none
        rw [extS_inst, Inst.find?_sub]
        cases hf : (extS δ (e :: σ) (a :: αs)).find? y with
        | none => exact absurd hf h
        | some m => simp⟩, hok.placeFree⟩
  exact BoxStep.push e (ι.life1 a) hok' (lt_of_le_of_lt (ι.life1_le a) htop) hns
    (find_sub_none ι hδ) hself hro (subFresh_inst ι hsf)

/-- **A box sequence instantiated is a box sequence at the instantiated reading.** -/
theorem boxSteps_inst {δ : LSub} {ls ls' : List SRec} (ι : Inst) {s s' : Stk}
    (hst : Relation.ReflTransGen (BoxStep δ ls) s s') (hro : RecsOutside (ι.life s'.2) ls') :
    Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (s.1, ι.life s.2) (s'.1, ι.life s'.2) := by
  induction hst with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
      obtain ⟨e, a, hc, -⟩ := boxStep_inv hbc
      have hro' : RecsOutside (ι.life b.2) ls' := by
        rw [hc] at hro
        exact fun a' ha' => hro a' (List.mem_cons_of_mem _ ha')
      refine (ih hro').tail ?_
      have hbc' : BoxStep δ _ (b.1, b.2) (c.1, c.2) := hbc
      exact boxStep_inst ι hbc' hro

/-- **A box sequence's new lifetimes are fresh below the reading.** -/
theorem boxSteps_subFresh {δ : LSub} {ls : List SRec} {s s' : Stk}
    (hst : Relation.ReflTransGen (BoxStep δ ls) s s') : ∀ a ∈ s'.2, a ∈ s.2 ∨ SubFresh δ a := by
  induction hst with
  | refl => exact fun a ha => Or.inl ha
  | @tail b c _ hbc ih =>
      obtain ⟨e, a₀, hc, -, -, -, -, -, -, hsf⟩ := boxStep_inv hbc
      intro a ha
      rw [hc] at ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inr hsf
      · exact ih a ha

/-- **At the empty stack, an instantiation of a box world fixes the reading**: its cut is just above
the outermost pushed lend, and every value of the reading is above that lend. -/
theorem inst_sub_fix_of_fresh {δ : LSub} {αs : List Life} {ι : Inst} (hat : InstAt αs ι)
    (hf : ∀ a ∈ αs, SubFresh δ a) : ι.sub δ = δ := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · obtain ⟨o, ho, hc⟩ := cutOf_eq.mp (hat c θ rfl)
    have hoα : o ∈ αs := List.mem_of_getLast? ho
    show Restrat.LSub.mapN θ.toNat δ = δ
    refine mapN_eq_self fun p hp => ?_
    show OrderDual.ofDual (θ (OrderDual.toDual p.2)) = p.2
    rw [θ.fix _ (hc ▸ cut_le_of_lt (hf o hoα p hp))]
    rfl

/-- **The box is transitive**: a value in the box at a stack is in the box at every world the box
reaches from there. The reached world's instantiations are, after the reaching instantiation, ones
of the stack (`instComp`); at the empty stack the reached world's instantiation fixes the reading
(`inst_sub_fix_of_fresh`). -/
theorem pBox_worldB {C : CTy} {δ : LSub} {σ σ' : LStack} {αs αs' : List Life} {ls' : List SRec}
    {P : LStack → LSub → List Life → List SRec → Prop} {ι : Inst}
    (hbox : PBox (.thunk C) δ σ αs P) (hat : InstAt αs ι)
    (hst : Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs')) :
    PBox (.thunk C) (ι.sub δ) σ' αs' P := by
  intro ι' hat' ls'' hro'' σ'' αs'' hst''
  have hst' := boxSteps_inst ι' hst hro''
  obtain ⟨τ, αt, hlt, hσ', hαs'⟩ := boxSteps_append hst
  simp only at hσ' hαs'
  by_cases hαs : αs = []
  · subst hαs
    have hι : ι = none := instAt_nil_eq hat
    subst hι
    have hfresh : ∀ a ∈ αs', SubFresh δ a := fun a ha => by
      rcases boxSteps_subFresh hst a ha with h | h
      · simp [Inst.life] at h
      · exact h
    have hfix : ι'.sub δ = δ := inst_sub_fix_of_fresh hat' hfresh
    have hst₁ : Relation.ReflTransGen (BoxStep δ ls'') (σ, []) (σ', ι'.life αs') := by
      have := hst'
      simp only [Inst.sub_none, Inst.life, List.map_nil] at this
      rwa [hfix] at this
    have hst₂ : Relation.ReflTransGen (BoxStep δ ls'') (σ', ι'.life αs') (σ'', αs'') := by
      simpa [Inst.sub_none, hfix] using hst''
    have hcomb : Relation.ReflTransGen (BoxStep (Inst.sub none δ) ls'') (σ, Inst.life none [])
        (σ'', αs'') := hst₁.trans hst₂
    have := hbox none (fun c θ h => by cases h) ls'' (fun a ha => by simp [Inst.life] at ha)
      σ'' αs'' hcomb
    show P σ'' (ι'.sub δ) αs'' ls''
    rw [hfix]
    exact this
  · have hat'' : InstAt (ι.life αs) ι' := by
      intro c θ h
      rw [← hat' c θ h, hαs', cutOf, cutOf, List.getLast?_append]
      have hne : ι.life αs ≠ [] := by simpa [Inst.life] using hαs
      obtain ⟨o, ho⟩ := List.getLast?_isSome.mpr hne |> Option.isSome_iff_exists.mp
      rw [ho]
      rfl
    obtain ⟨ι₃, hat₃, hsub, hlife, -⟩ := instComp αs ι ι' hat hat''
    have hl₃ : ι₃.life αs = ι'.life (ι.life αs) := by
      simp only [Inst.life, List.map_map]
      exact List.map_congr_left fun a _ => hlife a
    have hro₃ : RecsOutside (ι₃.life αs) ls'' := by
      rw [hl₃]
      rw [hαs', Inst.life, List.map_append] at hro''
      exact recsOutside_suffix hro''
    have hcomb : Relation.ReflTransGen (BoxStep (ι₃.sub δ) ls'') (σ, ι₃.life αs) (σ'', αs'') := by
      rw [hl₃, hsub]
      exact hst'.trans hst''
    have := hbox ι₃ hat₃ ls'' hro₃ σ'' αs'' hcomb
    rwa [hsub] at this

/-! ### A persistent context at a box world -/

/-- `pBox_worldB` at a stack in shape (its proof reads no shape). -/
theorem pBox_world {C : CTy} {δ : LSub} {σ σ' : LStack} {αs αs' : List Life} {ls' : List SRec}
    {P : LStack → LSub → List Life → List SRec → Prop} {ι : Inst} (_hok : StackOK σ αs)
    (hbox : PBox (.thunk C) δ σ αs P) (hat : InstAt αs ι)
    (hst : Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs')) :
    PBox (.thunk C) (ι.sub δ) σ' αs' P :=
  pBox_worldB (ι := ι) hbox hat hst

/-- **Views at the empty resource hold at every reading, lifetimes and list**: every visible flag
is off. -/
theorem vwSW_empty_transfer {s s' : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack}
    {ds : List Bool} {αs αs' : List Life} {ls ls' : List SRec}, αs'.length = αs.length →
    vwSW s seen σ ds αs ls PMap.empty → vwSW s' seen σ ds αs' ls' PMap.empty
  | _, [], [], [], [], _, _, _, h => h
  | seen, e :: σ, d :: ds, α :: αs, α' :: αs', ls, ls', hl, ⟨a, r, hc, ha, hr⟩ => by
      have ha0 := eq_empty_of_compS_left hc
      have hr0 := eq_empty_of_compS_right hc
      subst ha0 hr0
      refine ⟨PMap.empty, PMap.empty, hc, ?_, vwSW_empty_transfer (by simpa using hl) hr⟩
      cases hvis : vis seen e d
      · exact vwEW_off s' e α' ls'
      · rw [hvis] at ha
        obtain ⟨ψ, hψ, -⟩ := vwE_single ha.1
        have := congrArg (fun r => PMap.get r e.l) hψ
        simp at this
  | _, [], [], _ :: _, _, _, _, _, h => h.elim
  | _, [], _ :: _, [], _, _, _, _, h => h.elim
  | _, [], _ :: _, _ :: _, _, _, _, _, h => h.elim
  | _, _ :: _, [], [], _, _, _, _, h => h.elim
  | _, _ :: _, [], _ :: _, _, _, _, _, h => h.elim
  | _, _ :: _, _ :: _, [], _, _, _, _, h => h.elim
  | _, [], [], [], _ :: _, _, _, hl, _ => by simp at hl
  | _, _ :: _, _ :: _, _ :: _, [], _, _, hl, _ => by simp at hl

/-- **The clause at the empty resource, at an instantiation and any list**: nothing is retained
or dropped, so every list extends the instantiated one, and the views handed are empty. -/
theorem relendJ_empty_inst {δ : LSub} {σ : LStack} {P : LSub → List Life → List SRec → WProp}
    {αs : List Life} {ls : List SRec} {ι : Inst} (hat : InstAt αs ι) (ls' : List SRec)
    (hro : RecsOutside (ι.life αs) ls') (h : RelendJ δ σ P αs ls PMap.empty) :
    P (ι.sub δ) (ι.life αs) ls' PMap.empty := by
  obtain ⟨ds, ρz, ρn, hc, hn, -, H⟩ := h
  have hz0 := eq_empty_of_compS_left hc
  have hn0 := eq_empty_of_compS_right hc
  subst hz0 hn0
  exact H ι hat ls'
    ⟨fun r _ hrel => absurd hrel not_rel_empty, fun b hb => absurd hb not_cellIn_empty⟩
    (fun x _ hr => absurd hr not_rel_empty) (fun x _ hr => absurd hr not_rel_empty)
    hro PMap.empty PMap.empty
    ⟨vwSW_empty_transfer (Inst.life_length ι αs) hn.1, placeViewsL_empty⟩
    (ResU.comp_empty_right _)

/-- **Persistent data reaching no `U` along a box sequence**: each push is the `U`-free push at
the empty resource; its variable is no variable of `Δ`, so neither the data's type nor any
entry's payload type reads it. -/
theorem uFree_boxSteps {Δ : LifeCtx} {δ : LSub} {ls : List SRec} {B : VTy} (hSD : SubDom δ Δ)
    (hu : UFreeM B) (hB : ∀ y, VFree y B → ∃ u, Δ.find? y = some u) {v : Val} {s s' : Stk}
    (hst : Relation.ReflTransGen (BoxStep δ ls) s s') (hidx : BoxIdx Δ δ s.1 s.2 ls)
    (h : vRLM (ℍ := ℍ) .binder0 none s.1 δ B s.2 ls v PMap.empty) :
    vRLM (ℍ := ℍ) .binder0 none s'.1 δ B s'.2 ls v PMap.empty := by
  induction hst with
  | refl => exact h
  | @tail b c hsb hbc ih =>
      have hb := boxIdx_steps hSD hsb hidx
      have hbc' : BoxStep δ ls (b.1, b.2) (c.1, c.2) := hbc
      obtain ⟨e, a, hσ, hα, hΔe, hσe, hδe, hok, hsf, -⟩ := boxStep_var_off hb hbc'
      rw [hσ, hα]
      refine monoOwnUFree_go_len .binder0 e a B none none b.1 δ b.2 ls v PMap.empty hu
        (envPushNone b.1 δ b.2 ls e a) hb.ok.1 hok.chain hsf (fun e' he' hx => ?_)
        (fun hx => ?_) ⟨tab_empty _ _, placeViewsL_empty, hok.placeFree, ResU.inStratum_empty _⟩
        ih
      · rcases hb.pay e' he' e.x hx with ⟨u, hu'⟩ | hm
        · rw [hΔe] at hu'; exact absurd hu' (by simp)
        · exact hσe hm
      · obtain ⟨u, hu'⟩ := hB e.x hx
        rw [hΔe] at hu'; exact absurd hu' (by simp)

/-- **One persistent slot at a box world**: a persistent thunk by its box (`pBox_world` for the box
there), persistent data reaching no `U` by the thaw at the empty resource and the `U`-free
push. -/
theorem slot_boxWorld {Δ : LifeCtx} {δ : LSub} {σ σ' : LStack} {αs αs' : List Life}
    {ls ls' : List SRec} {B : VTy} {v : Val} {ι : Inst} (hSD : SubDom δ Δ)
    (hB : (∃ C, B = .thunk C) ∨ UFreeM B) (hBΔ : ∀ y, VFree y B → ∃ u, Δ.find? y = some u)
    (hidx : BoxIdx Δ δ σ αs ls) (hat : InstAt αs ι) (hro : RecsOutside (ι.life αs) ls')
    (hst : Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs'))
    (h : vRLM (ℍ := ℍ) .binder0 none σ δ (.bang B) αs ls v PMap.empty) :
    vRLM (ℍ := ℍ) .binder0 none σ' (ι.sub δ) (.bang B) αs' ls' v PMap.empty := by
  obtain ⟨-, hv, hbox⟩ := h
  rcases hB with ⟨C, rfl⟩ | hu
  · exact ⟨rfl, hbox ι hat ls' hro σ' αs' hst, pBox_worldB hbox hat hst⟩
  · refine ⟨rfl, ?_, pBox_of_not_thunk fun C hC => by subst hC; exact hu⟩
    have hv' := relendJ_empty_inst hat ls' hro
      (relendMValue_len B δ σ αs ls v PMap.empty hidx.ok.1 hidx.ob hidx.ro (tab_empty _ _)
        placeViewsL_empty hv)
    exact uFree_boxSteps (subDom_inst ι hSD) hu hBΔ hst (boxIdx_inst hidx hro) hv'

/-- **A persistent context at a box world**, slot by slot at the empty resource. -/
theorem gSepRLM_boxWorld {Δ : LifeCtx} {δ : LSub} {σ σ' : LStack} {αs αs' : List Life}
    {ls ls' : List SRec} {ι : Inst} (hSD : SubDom δ Δ) (hidx : BoxIdx Δ δ σ αs ls)
    (hat : InstAt αs ι) (hro : RecsOutside (ι.life αs) ls')
    (hst : Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs')) :
    ∀ (Γ : Ctx VTy) (γ : List Val), PersistentBoxed Γ →
      (∀ s ∈ Γ, s.live = true → VScoped Δ s.ty) →
      gSepRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ PMap.empty →
      gSepRLM (ℍ := ℍ) .binder0 σ' (ι.sub δ) αs' ls' Γ γ PMap.empty
  | [], γ, _, _, h => by cases γ <;> exact h
  | _ :: _, [], _, _, h => h
  | s :: Γ, v :: γ, hP, hSc, h => by
      have hP' : PersistentBoxed Γ := fun s' hs' hl => hP s' (List.mem_cons_of_mem _ hs') hl
      have hSc' : ∀ s' ∈ Γ, s'.live = true → VScoped Δ s'.ty :=
        fun s' hs' hl => hSc s' (List.mem_cons_of_mem _ hs') hl
      by_cases hl : s.live = true
      · simp only [gSepRLM, hl, if_true] at h ⊢
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        have e₁ := eq_empty_of_compS_left hc
        have e₂ := eq_empty_of_compS_right hc
        subst e₁ e₂
        obtain ⟨B, hBt, hB⟩ := hP s List.mem_cons_self hl
        have hBΔ : ∀ y, VFree y B → ∃ u, Δ.find? y = some u := fun y hy =>
          hSc s List.mem_cons_self hl y (by rw [hBt]; exact hy)
        rw [hBt] at h₁ ⊢
        exact ⟨PMap.empty, PMap.empty, hc,
          slot_boxWorld hSD hB hBΔ hidx hat hro hst h₁,
          gSepRLM_boxWorld hSD hidx hat hro hst Γ γ hP' hSc' h₂⟩
      · simp only [gSepRLM, hl] at h ⊢
        exact gSepRLM_boxWorld hSD hidx hat hro hst Γ γ hP' hSc' h

/-- **A persistent context at a box world**, at `gRLM`. -/
theorem gRLM_boxWorld {Δ : LifeCtx} {δ : LSub} {σ σ' : LStack} {αs αs' : List Life}
    {ls ls' : List SRec} {ι : Inst} {Γ : Ctx VTy} {γ : List Val} (hSD : SubDom δ Δ)
    (hidx : BoxIdx Δ δ σ αs ls) (hat : InstAt αs ι) (hro : RecsOutside (ι.life αs) ls')
    (hst : Relation.ReflTransGen (BoxStep (ι.sub δ) ls') (σ, ι.life αs) (σ', αs'))
    (hP : PersistentBoxed Γ) (hSc : ∀ s ∈ Γ, s.live = true → VScoped Δ s.ty)
    (h : gRLM (ℍ := ℍ) .binder0 σ δ αs ls Γ γ PMap.empty) :
    gRLM (ℍ := ℍ) .binder0 σ' (ι.sub δ) αs' ls' Γ γ PMap.empty := by
  obtain ⟨hlw, hgs⟩ := pure_sep_iff.mp h
  exact pure_sep_mk hlw (gSepRLM_boxWorld hSD hidx hat hro hst Γ γ hP hSc hgs)

/-! ### The two `!U` introductions -/

/-- **The index facts at the conclusion's index of a `!U` row**, blocks admitted: the judgement's
type is no `∀`, so every entry is of `StackJ`'s first two kinds. -/
theorem boxIdx_of_indexB {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    {Γ : Ctx VTy} {B : VTy} (hok : StackOKB σ αs) (hob : OuterBelowTop αs)
    (hJ : StackJBase σ αs δ Δ Γ (.ret B)) (hMod : Δ.Models (extS δ σ αs))
    (hro : RecsOutside αs ls) (hso : SubOutside σ αs δ) : BoxIdx Δ δ σ αs ls :=
  ⟨hok, hob, hro, hso, hMod, stackJBase_kinds_of_notAll hJ (fun _ _ _ h => by cases h), hJ.1⟩

/-- **The index facts at the conclusion's index of a `!U` row**: the judgement's type is no `∀`,
so every entry is of `StackJ`'s first two kinds. -/
theorem boxIdx_of_index {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    {Γ : Ctx VTy} {B : VTy} (hok : StackOK σ αs) (hob : OuterBelowTop αs)
    (hJ : StackJ σ αs δ Δ Γ (.ret B)) (hMod : Δ.Models (extS δ σ αs)) (hro : RecsOutside αs ls)
    (hso : SubOutside σ αs δ) : BoxIdx Δ δ σ αs ls :=
  boxIdx_of_indexB (stackOKB_of_ok σ αs hok) hob (stackJBase_of_stackJ hJ) hMod hro hso

/-- **`BangThunkFRowM binder0`.** The context is persistent, so it, and the thunk, hold nothing. At
the stack the thunk is the `U` row's (`thunkF_U_MB`). At every world of the box the context is
carried there (`gRLM_boxWorld`), the index facts hold there (`boxIdx_steps`,
`stackJBase_of_boxIdx`), and the thunk is the `U` row's there, from the premise at that world. -/
theorem bangThunkFRowM : BangThunkFRowM (ℍ := ℍ) .binder0 := by
  intro Δ Γ M A hP hPB hM hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  have hρ : ρ = PMap.empty := gSepRLM_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  subst hρ
  have hBL' : BindersLow (⟨.unit, false⟩ :: Γ) (.ret A) := ⟨hBL.1, fun s hs hl => by
    rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hBL.2 s hs hl⟩
  have hSc' : Scoped Δ (⟨.unit, false⟩ :: Γ) (.ret A) := ⟨hSc.1, fun s hs hl => by
    rcases List.mem_cons.mp hs with rfl | hs
    · simp at hl
    · exact hSc.2 s hs hl⟩
  have hJ' : StackJBase σ αs δ Δ (⟨.unit, false⟩ :: Γ) (.ret A) :=
    stackJBase_body hJ.1 (fun _ _ _ h => by cases h) (fun _ h => h) fun _ => ctxAvoids_dead
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ PMap.empty
  refine wpTS_val _ _ _ _ ⟨rfl, thunkF_U_MB hM hBL' hSc' hok hob hJ' hSD hMod hro hso ht hpv hg,
    fun ι hat ls' hro' σ' αs' hst => ?_⟩
  have hidx₀ := boxIdx_of_indexB hok hob hJ.1 hMod hro hso
  have hidx := boxIdx_steps (subDom_inst ι hSD) hst (boxIdx_inst hidx₀ hro')
  exact thunkF_U_MB hM hBL' hSc' hidx.ok hidx.ob (stackJBase_of_boxIdx hidx hSc')
    (subDom_inst ι hSD) hidx.md hidx.ro hidx.so (tab_empty _ _) placeViewsL_empty
    (gRLM_boxWorld hSD hidx₀ hat hro' hst hPB hSc.2 hg)

/-- **`BangThunkVRowM binder0`**, as `bangThunkFRowM`. -/
theorem bangThunkVRowM : BangThunkVRowM (ℍ := ℍ) .binder0 := by
  intro Δ Γ N C hP hPB hC _ hN hBL hSc δ σ αs ls γ ρ hok hob hJ hSD hMod hro hso ht hpv hg
  have hρ : ρ = PMap.empty := gSepRLM_persistent Γ γ ρ hP (pure_sep_iff.mp hg).2
  subst hρ
  have hJ' : StackJBase σ αs δ Δ Γ C :=
    stackJBase_body hJ.1 (fun _ _ _ h => by cases h) (fun _ h => h) fun _ h => h
  show wpTS ls (.val (.lam (Expr.psub 1 γ N))) _ PMap.empty
  refine wpTS_val _ _ _ _ ⟨rfl, thunkV_U_MB hC hN hBL hSc hok hob hJ'
    (stackJBase_kinds_of_notAll hJ.1 (fun _ _ _ h => by cases h)) hSD hMod hro hso ht hpv hg,
    fun ι hat ls' hro' σ' αs' hst => ?_⟩
  have hidx₀ := boxIdx_of_indexB hok hob hJ.1 hMod hro hso
  have hidx := boxIdx_steps (subDom_inst ι hSD) hst (boxIdx_inst hidx₀ hro')
  exact thunkV_U_MB hC hN hBL hSc hidx.ok hidx.ob (stackJBase_of_boxIdx hidx hSc) hidx.kind
    (subDom_inst ι hSD) hidx.md hidx.ro hidx.so (tab_empty _ _) placeViewsL_empty
    (gRLM_boxWorld hSD hidx₀ hat hro' hst hPB hSc.2 hg)

/-- **The `U` side of statement 0 at `binder0`, at `vRLM`, at every context** (`Statement0UFullM`):
R1 closed at `binder0`, the `!U` rows at the persistence box. -/
theorem statement0UFullM : Statement0UFullM (ℍ := ℍ) .binder0 :=
  ⟨thawInstM, ctxRelendsAllM, thunkFRowM, thunkVRowM, bangThunkFRowM, bangThunkVRowM⟩

end ProbeD1

end
