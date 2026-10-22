import Spike670.Kappa

/-!
# #670 — slice 1: the closure's function is linear

`mkClos_fnsOK`: if every function so far consumes its parameters, so does every function after
`mkClos`, provided the body's conversion keeps that (the induction hypothesis on functions).
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

variable {D : Var → Prop}

theorem same_envOf {ctx : Ctx} {s s' : CState} {r : List Var × List Var × Ctx}
    (h : Ok (envOf ctx) s r s') : SameFns s s' := by
  simp only [envOf] at h
  obtain ⟨b, s₁, hfor, h⟩ := ok_bind h
  rw [(ok_pure h).2]
  refine forIn_rule ctx _ (fun _ _ st => SameFns s st) ?_ ctx [] _ s _ s₁ (by simp)
    (SameFns.refl s) hfor
  intro pfx a rest b st r st' _ hI hf
  cases a with
  | none => obtain ⟨rfl, rfl⟩ := ok_pure hf; exact ⟨_, rfl, hI⟩
  | some x =>
    obtain ⟨x', s₂, h₁, h₂⟩ := ok_bind hf
    have e₁ : SameFns st s₂ := by
      obtain ⟨_, s₃, h₃, h₄⟩ := ok_bind h₁
      rw [ok_tyOf h₃] at h₄; exact same_fresh h₄
    obtain ⟨d, s₃, h₃, h₄⟩ := ok_bind h₂
    obtain ⟨hd, he⟩ := ok_get h₃
    rw [hd, he] at h₄
    split at h₄
    · obtain ⟨_, s₄, h₅, h₆⟩ := ok_bind h₄
      obtain ⟨rfl, hs⟩ := ok_pure h₆
      refine ⟨_, rfl, hI.trans (e₁.trans ?_)⟩
      rw [hs, ok_modify h₅]; rfl
    · obtain ⟨rfl, hs⟩ := ok_pure h₄
      exact ⟨_, rfl, hI.trans (e₁.trans (by rw [hs]; rfl))⟩

theorem fns_outsideSite {act : CM α} {s s' : CState} {r : α} {sites : List (List LTy × String)}
    (h : Ok (outsideSite act) s (r, sites) s') :
    ∃ s₁ s₂, Keeps s s₁ ∧ SameFns s s₁ ∧ Ok act s₁ r s₂ ∧ Keeps s₂ s' ∧ SameFns s₂ s' := by
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
  refine ⟨a₃, a₄, ?_, ?_, h₄, ?_, ?_⟩
  · rw [ok_modify h₃, e₂, e₁]; exact ⟨rfl, rfl⟩
  · unfold SameFns; rw [ok_modify h₃, e₂, e₁]
  · rw [hs, ok_modify h₆, e₅]; exact ⟨rfl, rfl⟩
  · unfold SameFns; rw [hs, ok_modify h₆, e₅]

theorem fns_closOf {c : Nat} {k : LCTy} {outer : List Var} {inner : List (List LTy × String)}
    {s s' : CState} {tm : Tm} (hF : AllFnsOK D s) (h : Ok (closOf c k outer inner) s tm s') :
    AllFnsOK D s' := by
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
    rw [hs]
    have e₄ : SameFns a₂ a₄ := by unfold SameFns; rw [ok_modify h₄, ok_mapM_tyOf h₃]
    have e₅ : SameFns a₄ a₅ := by unfold SameFns; rw [ok_modify h₅]
    exact ((hF.reserveFn h₂).same e₄).same e₅
  · obtain ⟨rfl, rfl⟩ := ok_pure h; exact hF

/-- **The closure's function consumes its parameters.** -/
theorem mkClos_fnsOK {name : String} {ctx : Ctx} {k : LCTy} {param : Option LTy} {ret : LTy}
    {body : Ctx → CM Tm} {s s' : CState} {tm : Tm}
    (hbody : ∀ ctx' s₁ b s₂, WF ctx' s₁ → s₁.mach.isEmpty = true → Ok (body ctx') s₁ b s₂ →
      Post D ctx' s₁ b s₂)
    (hbodyF : ∀ ctx' s₁ b s₂, AllFnsOK D s₁ → Ok (body ctx') s₁ b s₂ → AllFnsOK D s₂)
    (hw : WF ctx s) (hm : s.mach.isEmpty = true) (hF : AllFnsOK D s)
    (h : Ok (mkClos name ctx k param ret body) s tm s') : AllFnsOK D s' := by
  simp only [mkClos] at h
  obtain ⟨⟨outer, inner, ctx'⟩, s₁, h₁, h⟩ := ok_bind h
  have F₁ := hF.same (same_envOf h₁)
  obtain ⟨g₁, rfl, hli, hni, hri⟩ := ok_envOf h₁
  obtain ⟨fi, s₂, h₂, h⟩ := ok_bind h
  have F₂ := F₁.reserveFn h₂
  have k₂ := ok_reserveFn h₂
  have hm₂ : s₂.mach.isEmpty = true := by rw [k₂.2, g₁.mach]; exact hm
  have hinner : ∀ y ∈ inner, y < s₂.next := fun y hy => by
    have := (hri y hy).2; rw [k₂.1]; exact this
  cases param with
  | some pt =>
    obtain ⟨pv, s₃, h₃, h⟩ := ok_bind h
    obtain ⟨rfl, hn₃, hm₃⟩ := ok_fresh h₃
    have F₃ := F₂.same (same_fresh h₃)
    obtain ⟨⟨b, sites⟩, s₄, h₄, h⟩ := ok_bind h
    obtain ⟨sa, sb, ka, fa, hb, kb, fb⟩ := fns_outsideSite h₄
    obtain ⟨_, s₅, h₅, h⟩ := ok_bind h
    obtain ⟨c, s₆, h₆, h⟩ := ok_bind h
    have Fb := (hbodyF _ _ _ _ (F₃.same fa) hb).same fb
    refine fns_closOf ((?_ : AllFnsOK D s₅).same (same_addCode h₆)) h
    refine Fb.setFn ?_ h₅
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
    refine ⟨?_, ⟨Δ, ?_, cl⟩, nd, ?_⟩
    · simp only [List.nodup_append, hni, List.nodup_singleton, true_and, List.mem_singleton]
      intro a ha b hb e; rw [hb] at e; rw [e] at ha; have := hinner _ ha; vomega
    · convert l using 1
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
    obtain ⟨sa, sb, ka, fa, hb, kb, fb⟩ := fns_outsideSite h₄
    obtain ⟨_, s₅, h₅, h⟩ := ok_bind h
    obtain ⟨c, s₆, h₆, h⟩ := ok_bind h
    have Fb := (hbodyF _ _ _ _ (F₂.same fa) hb).same fb
    refine fns_closOf ((?_ : AllFnsOK D s₅).same (same_addCode h₆)) h
    refine Fb.setFn ?_ h₅
    have hwb : WF ctx' sa := by
      refine ⟨by rw [hli]; exact hni, fun y hy => ?_⟩
      rw [hli] at hy; rw [ka.1]; exact hinner y hy
    obtain ⟨gb, ⟨⟨Δ, l, cl⟩, nd, rg⟩⟩ := hbody _ sa b sb hwb (by rw [ka.2]; exact hm₂) hb
    refine ⟨hni, ⟨Δ, ?_, cl⟩, nd, ?_⟩
    · convert l using 1
      ext z; simp [liveF, hli]
    · intro y hy hp
      have := (rg y hy).1
      rw [ka.1] at this
      have := hinner y hp; vomega

end Backend2.Spike670
