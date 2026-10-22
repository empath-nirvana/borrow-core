import Spike670.Slice1

/-!
# #670 — slice 1: closure capture

`mkClos` (`Backend2/Convert.lean`) makes a closure of a code of its own over the live slots of the
context (`envOf`). `mkClos_spec`: the closure term consumes exactly the context's live variables,
and the function it sets for the code takes the captured values (renamed fresh) and the argument,
and its body consumes them all.
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

variable {D : Var → Prop}

/-- A function whose body consumes its parameters, each bound once. -/
def FnBodyOK (D : Var → Prop) (d : Fn) : Prop :=
  d.params.Nodup ∧ ClosedL D d.params.toFinset d.body ∧ (bnd d.body).Nodup ∧
    ∀ y ∈ bnd d.body, y ∉ d.params

theorem keeps_of_eq {s s' : CState} (h₁ : s'.next = s.next) (h₂ : s'.mach = s.mach) :
    Keeps s s' := ⟨h₁, h₂⟩

theorem ok_addFn {f : Fn} {s s' : CState} {i : Nat} (h : Ok (addFn f) s i s') : Keeps s s' := by
  have := ok_modifyGet h; simp only [Prod.mk.injEq] at this; rw [this.2]; exact ⟨rfl, rfl⟩

theorem ok_reserveFn {n : String} {s s' : CState} {i : Nat} (h : Ok (reserveFn n) s i s') :
    Keeps s s' := ok_addFn h

theorem ok_setFn {i : Nat} {f : Fn} {s s' : CState} {u : Unit} (h : Ok (setFn i f) s u s') :
    Keeps s s' := by rw [ok_modify h]; exact ⟨rfl, rfl⟩

theorem ok_addCode {c : Code} {s s' : CState} {i : Nat} (h : Ok (addCode c) s i s') :
    Keeps s s' := by
  have := ok_modifyGet h; simp only [Prod.mk.injEq] at this; rw [this.2]; exact ⟨rfl, rfl⟩

theorem ok_mapM_tyOf : ∀ {xs : List Var} {s s' : CState} {ts : List LTy},
    Ok (xs.mapM tyOf) s ts s' → s' = s
  | [], s, s', ts, h => by simp only [List.mapM_nil] at h; exact (ok_pure h).2
  | x :: xs, s, s', ts, h => by
    simp only [List.mapM_cons] at h
    obtain ⟨_, s₁, h₁, h₂⟩ := ok_bind h
    obtain ⟨_, s₂, h₃, h₄⟩ := ok_bind h₂
    rw [(ok_pure h₄).2, ok_mapM_tyOf h₃, ok_tyOf h₁]

theorem ok_outsideSite {act : CM α} {s s' : CState} {r : α} {sites : List (List LTy × String)}
    (h : Ok (outsideSite act) s (r, sites) s') :
    ∃ s₁ s₂, Keeps s s₁ ∧ Ok act s₁ r s₂ ∧ Keeps s₂ s' := by
  simp only [outsideSite] at h
  obtain ⟨_, a₁, h₁, h⟩ := ok_bind h
  obtain ⟨_, a₂, h₂, h⟩ := ok_bind h
  obtain ⟨_, a₃, h₃, h⟩ := ok_bind h
  obtain ⟨r', a₄, h₄, h⟩ := ok_bind h
  obtain ⟨_, a₅, h₅, h⟩ := ok_bind h
  obtain ⟨_, a₆, h₆, h⟩ := ok_bind h
  obtain ⟨hr, hs⟩ := ok_pure h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, -⟩ := hr
  have e₁ := (ok_get h₁).2; have e₂ := (ok_get h₂).2; have e₅ := (ok_get h₅).2
  refine ⟨a₃, a₄, ?_, h₄, ?_⟩
  · rw [ok_modify h₃, e₂, e₁]; exact ⟨rfl, rfl⟩
  · rw [hs, ok_modify h₆, e₅]; exact ⟨rfl, rfl⟩

/-- `closOf`: the closure itself, or a call of a variant's builder, over the same values. -/
theorem ok_closOf {c : Nat} {k : LCTy} {outer : List Var} {inner : List (List LTy × String)}
    {s s' : CState} {tm : Tm} (h : Ok (closOf c k outer inner) s tm s') :
    (tm = .clos c outer ∨ ∃ mk, tm = .call mk outer) ∧ Keeps s s' := by
  simp only [closOf] at h
  obtain ⟨_, a₁, h₁, h⟩ := ok_bind h
  obtain ⟨hd, he⟩ := ok_get h₁
  rw [hd, he] at h
  split at h
  · obtain ⟨mk, a₂, h₂, h⟩ := ok_bind h
    obtain ⟨_, a₃, h₃, h⟩ := ok_bind h
    obtain ⟨_, a₄, h₄, h⟩ := ok_bind h
    obtain ⟨_, a₅, h₅, h⟩ := ok_bind h
    obtain ⟨rfl, hs⟩ := ok_pure h
    refine ⟨.inr ⟨mk, rfl⟩, ?_⟩
    rw [hs]
    have e₃ := ok_mapM_tyOf h₃
    have k₄ : Keeps a₃ a₄ := by rw [ok_modify h₄]; exact ⟨rfl, rfl⟩
    rw [e₃] at k₄
    exact ((ok_reserveFn h₂).trans k₄).trans (ok_readFact h₅)
  · obtain ⟨rfl, rfl⟩ := ok_pure h
    exact ⟨.inl rfl, Keeps.refl _⟩

/-- **`envOf`**: the outer values are the live slots; the code's context renames each to a fresh
variable, the code's parameters. -/
theorem ok_envOf {ctx : Ctx} {s s' : CState} {outer inner : List Var} {ctx' : Ctx}
    (h : Ok (envOf ctx) s (outer, inner, ctx') s') :
    Grows s s' ∧ outer = live ctx ∧ live ctx' = inner ∧ inner.Nodup ∧
      ∀ y ∈ inner, s.next ≤ y ∧ y < s'.next := by
  simp only [envOf] at h
  obtain ⟨⟨o, i, c⟩, s₁, hfor, h⟩ := ok_bind h
  obtain ⟨hr, hs⟩ := ok_pure h
  simp only [Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl, rfl⟩ := hr
  rw [hs]
  have I := forIn_rule ctx _ (fun pfx (b : Array Var × Array Var × Array (Option Var)) st =>
      Grows s st ∧ b.1.toList = live pfx ∧ live b.2.2.toList = b.2.1.toList ∧ b.2.1.toList.Nodup ∧
      ∀ y ∈ b.2.1.toList, s.next ≤ y ∧ y < st.next) ?step ctx [] (#[], #[], #[]) s _ s₁ (by simp)
    ⟨Grows.refl s, by simp [live], by simp [live], by simp, by simp⟩ hfor
  · exact I
  case step =>
    intro pfx a rest b st r st' _ hI hf
    obtain ⟨o, i, c⟩ := b
    obtain ⟨g, ho, hc, hn, hr⟩ := hI
    simp only at hf ho hc hn hr
    cases a with
    | none =>
      obtain ⟨rfl, rfl⟩ := ok_pure hf
      exact ⟨_, rfl, g, by simpa [live] using ho, by simpa [live] using hc, hn, hr⟩
    | some x =>
      obtain ⟨x', s₂, h₁, h₂⟩ := ok_bind hf
      obtain ⟨rfl, hn', hm'⟩ := ok_freshLike h₁
      obtain ⟨d, s₃, h₃, h₄⟩ := ok_bind h₂
      obtain ⟨hd, he⟩ := ok_get h₃
      rw [hd, he] at h₄
      have hfin : r = .yield (o.push x, i.push st.next, c.push (some st.next)) ∧ Keeps s₂ st' := by
        split at h₄
        · obtain ⟨_, s₄, h₅, h₆⟩ := ok_bind h₄
          obtain ⟨rfl, rfl⟩ := ok_pure h₆
          rw [ok_modify h₅]; exact ⟨rfl, rfl, rfl⟩
        · obtain ⟨rfl, rfl⟩ := ok_pure h₄; exact ⟨rfl, Keeps.refl _⟩
      obtain ⟨rfl, k⟩ := hfin
      have gn := g.next
      refine ⟨_, rfl, ⟨by rw [k.1, hn']; vomega, by rw [k.2, hm', g.mach]⟩, ?_, ?_, ?_, ?_⟩
      · simp [ho, live]
      · rw [Array.toList_push, live_snoc, hc]; simp
      · simp only [Array.toList_push, List.nodup_append, hn, List.nodup_singleton, true_and,
          List.mem_singleton]
        intro a ha b hb; subst hb; have := (hr a ha).2; intro e; subst e; vomega
      · intro y hy
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · have := hr y hy; exact ⟨this.1, by rw [k.1, hn']; vomega⟩
        · exact ⟨gn, by rw [k.1, hn']; vomega⟩

/-- The closure term, over `outer = live ctx`: consumes the context. -/
theorem post_closTerm {ctx : Ctx} {s s' : CState} {tm : Tm} {c : Nat}
    (hw : WF ctx s) (g : Grows s s') (ht : tm = .clos c (live ctx) ∨ ∃ mk, tm = .call mk (live ctx)) :
    Post D ctx s tm s' := by
  refine ⟨g, ?_⟩
  rcases ht with rfl | ⟨mk, rfl⟩
  · exact postG_ops (xs := live ctx) rfl hw.1
  · exact postG_ops (xs := live ctx) rfl hw.1

/-- **`mkClos`**: the closure consumes exactly the context's live variables, and the function
set for its code consumes its parameters: the captured values, renamed, and the argument. -/
theorem mkClos_spec {name : String} {ctx : Ctx} {k : LCTy} {param : Option LTy} {ret : LTy}
    {body : Ctx → CM Tm} {s s' : CState} {tm : Tm}
    (hbody : ∀ ctx' s₁ b s₂, WF ctx' s₁ → s₁.mach.isEmpty = true → Ok (body ctx') s₁ b s₂ →
      Post D ctx' s₁ b s₂)
    (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (mkClos name ctx k param ret body) s tm s') :
    Post D ctx s tm s' ∧ ∃ fi d s₁ s₂ u, Ok (setFn fi d) s₁ u s₂ ∧ FnBodyOK D d := by
  simp only [mkClos] at h
  obtain ⟨⟨outer, inner, ctx'⟩, s₁, h₁, h⟩ := ok_bind h
  obtain ⟨g₁, rfl, hli, hni, hri⟩ := ok_envOf h₁
  obtain ⟨fi, s₂, h₂, h⟩ := ok_bind h
  have k₂ := ok_reserveFn h₂
  have hm₂ : s₂.mach.isEmpty = true := by rw [k₂.2, g₁.mach]; exact hm
  cases param with
  | some pt =>
    obtain ⟨pv, s₃, h₃, h⟩ := ok_bind h
    obtain ⟨rfl, hn₃, hm₃⟩ := ok_fresh h₃
    obtain ⟨⟨b, sites⟩, s₄, h₄, h⟩ := ok_bind h
    obtain ⟨sa, sb, ka, hb, kb⟩ := ok_outsideSite h₄
    obtain ⟨_, s₅, h₅, h⟩ := ok_bind h
    obtain ⟨c, s₆, h₆, h⟩ := ok_bind h
    obtain ⟨ht, k₇⟩ := ok_closOf h
    have hinner : ∀ y ∈ inner, y < s₂.next := fun y hy => by
      have := (hri y hy).2; rw [k₂.1]; exact this
    have hwb : WF (some s₂.next :: ctx') sa := by
      refine ⟨?_, fun y hy => ?_⟩
      · rw [live_cons_some, hli]
        exact List.nodup_cons.2 ⟨fun hh => by have := hinner _ hh; vomega, hni⟩
      · rw [live_cons_some, hli] at hy
        rw [ka.1, hn₃]
        rcases List.mem_cons.1 hy with rfl | hy
        · vomega
        · have := hinner y hy; vomega
    obtain ⟨gb, ⟨⟨Δ, l, cl⟩, nd, rg⟩⟩ := hbody _ sa b sb hwb (by rw [ka.2, hm₃]; exact hm₂) hb
    rw [liveF_cons_some] at l
    have gs : Grows s s' := ((((g₁.trans k₂.grows).trans ⟨by vomega, hm₃⟩).trans ka.grows).trans
      (gb.trans kb.grows)).trans (((ok_setFn h₅).trans (ok_addCode h₆)).trans k₇).grows
    refine ⟨post_closTerm hw gs ht, fi, _, _, _, _, h₅, ?_, ?_, nd, ?_⟩
    · simp only [List.nodup_append, hni, List.nodup_singleton, true_and, List.mem_singleton]
      intro a ha b hb e; rw [hb] at e; rw [e] at ha; have := hinner _ ha; vomega
    · refine ⟨Δ, ?_, cl⟩
      convert l using 1
      ext z; simp [liveF, hli]
    · intro y hy hp
      have := (rg y hy).1
      rw [ka.1, hn₃] at this
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · have := hinner y hp; vomega
      · vomega
  | none =>
    obtain ⟨⟨b, sites⟩, s₄, h₄, h⟩ := ok_bind h
    obtain ⟨sa, sb, ka, hb, kb⟩ := ok_outsideSite h₄
    obtain ⟨_, s₅, h₅, h⟩ := ok_bind h
    obtain ⟨c, s₆, h₆, h⟩ := ok_bind h
    obtain ⟨ht, k₇⟩ := ok_closOf h
    have hinner : ∀ y ∈ inner, y < s₂.next := fun y hy => by
      have := (hri y hy).2; rw [k₂.1]; exact this
    have hwb : WF ctx' sa := by
      refine ⟨by rw [hli]; exact hni, fun y hy => ?_⟩
      rw [hli] at hy; rw [ka.1]; exact hinner y hy
    obtain ⟨gb, ⟨⟨Δ, l, cl⟩, nd, rg⟩⟩ := hbody _ sa b sb hwb (by rw [ka.2]; exact hm₂) hb
    have gs : Grows s s' := (((g₁.trans k₂.grows).trans ka.grows).trans
      (gb.trans kb.grows)).trans (((ok_setFn h₅).trans (ok_addCode h₆)).trans k₇).grows
    refine ⟨post_closTerm hw gs ht, fi, _, _, _, _, h₅, hni, ⟨Δ, ?_, cl⟩, nd, ?_⟩
    · convert l using 1
      ext z; simp [liveF, hli]
    · intro y hy hp
      have := (rg y hy).1
      rw [ka.1] at this
      have := hinner y hp; vomega

/-- A code's body, with no machine operation, is `conv`'s. -/
theorem convBody_spec {fuel : Nat} {t : TExpr} (IH : Spec D (fun c => conv fuel c t)) :
    ∀ ctx' s₁ b s₂, WF ctx' s₁ → s₁.mach.isEmpty = true → Ok (convBody fuel ctx' t) s₁ b s₂ →
      Post D ctx' s₁ b s₂ := by
  intro ctx' s₁ b s₂ hw hm h
  simp only [convBody] at h
  obtain ⟨d, s₃, h₁, h⟩ := ok_bind h
  obtain ⟨hd, he⟩ := ok_get h₁
  rw [hd, he, hm] at h
  simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h
  exact IH ctx' s₁ b s₂ hw hm h

theorem ok_answerOf {t : LTy} {s s' : CState} {r : Option LTy × LTy} (h : Ok (answerOf t) s r s') :
    s' = s := by
  unfold answerOf at h
  split at h
  · split at h
    · obtain ⟨_, s₁, h₁, h₂⟩ := ok_bind h
      have e₁ : s₁ = s := by unfold answerOf.repC at h₁; split at h₁ <;> exact (ok_pure h₁).2
      rw [(ok_pure h₂).2, e₁]
    · exact (ok_pure h).2
    · exact (ok_throw h).elim
  · exact (ok_throw h).elim

theorem ok_repK : ∀ {k : LCTy} {s s' : CState} {r : LTy}, Ok (repK k) s r s' → s' = s
  | .ret _, _, _, _, h => (ok_pure h).2
  | .arr _ k, _, _, _, h => ok_repK (k := k) h
  | .top, _, _, _, h => (ok_pure h).2
  | .amp _ _, _, _, _, h => (ok_pure h).2
  | .nu _, _, _, _, h => (ok_pure h).2

/-- **`lam`**: a closure of a code of its own over the live slots; its function takes them and the
argument. -/
theorem node_lam {fuel : Nat} {ctx : Ctx} {info j A C c} {s s' : CState} {tm : Tm}
    (IH : Spec D (fun c' => conv fuel c' c)) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.lam info j A C c)) s tm s') :
    Post D ctx s tm s' ∧ ∃ fi d s₁ s₂ u, Ok (setFn fi d) s₁ u s₂ ∧ FnBodyOK D d := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨rT, s₂, h₁, h⟩ := ok_bind h
  split at h
  swap; · exact (ok_throw h).elim
  obtain ⟨ar, s₃, h₂, h⟩ := ok_bind h
  obtain ⟨aT, s₄, h₃, h⟩ := ok_bind h
  have k₄ : Keeps s₁ s₄ := ((ok_repJ h₁).trans (ok_answerOf h₂ ▸ Keeps.refl _)).trans (ok_vty h₃)
  obtain ⟨p, rest⟩ := mkClos_spec (convBody_spec IH) (hw.keeps (hk.trans k₄))
    (by rw [k₄.2]; exact hm₁) h
  exact ⟨⟨(hk.trans k₄).grows.trans p.1, by rw [← (hk.trans k₄).1]; exact p.2⟩, rest⟩

/-- **`thunkF`**: a closure of a code of its own, taking no argument. -/
theorem node_thunkF {fuel : Nat} {ctx : Ctx} {info j A c} {s s' : CState} {tm : Tm}
    (IH : Spec D (fun c' => conv fuel c' c)) (hw : WF ctx s) (hm : s.mach.isEmpty = true)
    (h : Ok (conv (fuel + 1) ctx (.thunkF info j A c)) s tm s') :
    Post D ctx s tm s' ∧ ∃ fi d s₁ s₂ u, Ok (setFn fi d) s₁ u s₂ ∧ FnBodyOK D d := by
  open_conv h hm s₁ hk
  have hm₁ : s₁.mach.isEmpty = true := hk.2 ▸ hm
  obtain ⟨rT, s₂, h₁, h⟩ := ok_bind h
  split at h
  swap; · exact (ok_throw h).elim
  obtain ⟨rr, s₃, h₂, h⟩ := ok_bind h
  have k₃ : Keeps s₁ s₃ := (ok_repJ h₁).trans (ok_repK h₂ ▸ Keeps.refl _)
  obtain ⟨p, rest⟩ := mkClos_spec (fun c' s b s' hw hm hb => by
      have := convBody_spec IH (none :: c') s b s' ⟨by rw [live_cons_none]; exact hw.1,
        fun y hy => hw.2 y (by rwa [live_cons_none] at hy)⟩ hm hb
      rwa [Post, liveF_cons_none] at this)
    (hw.keeps (hk.trans k₃)) (by rw [k₃.2]; exact hm₁) h
  exact ⟨⟨(hk.trans k₃).grows.trans p.1, by rw [← (hk.trans k₃).1]; exact p.2⟩, rest⟩

end Backend2.Spike670
