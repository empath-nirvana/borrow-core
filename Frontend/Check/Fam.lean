import Frontend.Check.Decide

/-!
# Frontend — Check — families of contexts

The checker's linearity bookkeeping (syntax-core §7, §11). A subterm is checked once against
the types `T` of every slot in scope and reports two masks over the slots:

* `u`, the slots it **uses**: the variables it consumes;
* `w`, the slots it may **absorb**: live slots it can be given without using them. A
  persistent slot can be dropped at a leaf (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`); every slot
  can be absorbed by `⟨⟩` (`topI` holds at any context) and by `absurd` (`zeroE`'s `Γ₂`).

It returns a derivation at **every** liveness `L` with `u ⊆ L ⊆ u ∪ w` (`Btw u w L`): that
is the Hodas–Miller input/output reading with ⊤-slack, with the output context `L` chosen by
the enclosing rule instead of threaded. `Fam T P` packages the masks and the family of proofs
`∀ L, Btw u w L → P L`; the operations below build it one `CDerives` premise at a time:

| operation | rule premise it discharges |
|---|---|
| `Fam.dead`, `Fam.deadStrict`, `Fam.var`, `Fam.top` | `Ctx.DeadP`, `Ctx.Dead`, `Ctx.SoloP`, none |
| `Fam.split` | `Ctx.SplitP Γ Γ₁ Γ₂` (a persistent slot used on both sides goes to both) |
| `Fam.merge` | the same context for both `case` arms or both `⟨,⟩` components |
| `Fam.popLive`, `Fam.popDead` | a binder's slot, live or dead |
| `Fam.restrict` | a premise on every live slot: `CtxOutlives`, `Persistent`, `allI`'s `hΓx` |
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Lifetime

/-- The context with slot types `T` and liveness `L`. -/
def mkCtx : List VTy → List Bool → Ctx VTy
  | A :: T, l :: L => ⟨A, l⟩ :: mkCtx T L
  | _, _ => []

/-- `u ⊆ L ⊆ u ∪ w`, pointwise, the three masks of one length. -/
inductive Btw : List Bool → List Bool → List Bool → Prop where
  | nil : Btw [] [] []
  | cons {u w l : Bool} {us ws ls : List Bool} (h₁ : u = true → l = true)
      (h₂ : l = true → u = true ∨ w = true) (h : Btw us ws ls) :
      Btw (u :: us) (w :: ws) (l :: ls)

theorem Btw.length {u w L : List Bool} (h : Btw u w L) : L.length = u.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- A family of derivations: masks `u`, `w` over `T`, and `P L` at every `L` between them. -/
structure Fam (T : List VTy) (P : List Bool → Prop) where
  u : List Bool
  w : List Bool
  hu : u.length = T.length
  hw : w.length = T.length
  d : ∀ L, Btw u w L → P L

/-! ### Mask operations -/

def orL : List Bool → List Bool → List Bool
  | a :: as, b :: bs => (a || b) :: orL as bs
  | _, _ => []

def andL : List Bool → List Bool → List Bool
  | a :: as, b :: bs => (a && b) :: andL as bs
  | _, _ => []

/-- `a ⊆ b`, pointwise. -/
def subL : List Bool → List Bool → Bool
  | a :: as, b :: bs => (!a || b) && subL as bs
  | _, _ => true

theorem orL_length : ∀ {a b : List Bool}, a.length = b.length → (orL a b).length = a.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [orL, List.length_cons] at h ⊢; rw [orL_length (by omega)]

theorem andL_length : ∀ {a b : List Bool}, a.length = b.length → (andL a b).length = a.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [andL, List.length_cons] at h ⊢; rw [andL_length (by omega)]

/-- Every slot `false`. -/
def noneL (T : List VTy) : List Bool := T.map (fun _ => false)

/-- Every slot `true`. -/
def allL (T : List VTy) : List Bool := T.map (fun _ => true)

/-- The persistent slots. -/
def persL (T : List VTy) : List Bool := T.map VTy.persistent

/-- Only slot `i`. -/
def oneL (T : List VTy) (i : Nat) : List Bool := (List.range T.length).map (· == i)

/-- The slots whose type satisfies `p`. -/
def predL (p : VTy → Bool) (T : List VTy) : List Bool := T.map p

/-- A slot used on both sides is persistent. -/
def overlapOK : List VTy → List Bool → List Bool → Bool
  | A :: T, a :: as, b :: bs => (!(a && b) || A.persistent) && overlapOK T as bs
  | _, _, _ => true

/-- Every used slot satisfies `p`. -/
def usedSat (p : VTy → Bool) : List VTy → List Bool → Bool
  | A :: T, a :: as => (!a || p A) && usedSat p T as
  | _, _ => true

/-! ### Leaves -/

theorem btw_none_deadP : ∀ {T : List VTy} {L : List Bool}, Btw (noneL T) (persL T) L →
    Ctx.DeadP (mkCtx T L)
  | [], [], _ => .nil
  | A :: T, l :: L, .cons _ h₂ h => by
      cases l with
      | false => exact .cons (btw_none_deadP h)
      | true =>
          have : A.persistent = true := by simpa using h₂ rfl
          exact .drop this (btw_none_deadP h)

theorem btw_none_dead : ∀ {T : List VTy} {L : List Bool}, Btw (noneL T) (noneL T) L →
    Ctx.Dead (mkCtx T L)
  | [], [], _ => .nil
  | A :: T, l :: L, .cons _ h₂ h => by
      cases l with
      | false => exact .cons (btw_none_dead h)
      | true => simp at h₂

theorem noneL_length (T : List VTy) : (noneL T).length = T.length := by simp [noneL]
theorem allL_length (T : List VTy) : (allL T).length = T.length := by simp [allL]
theorem persL_length (T : List VTy) : (persL T).length = T.length := by simp [persL]
theorem predL_length (p : VTy → Bool) (T : List VTy) : (predL p T).length = T.length := by
  simp [predL]
theorem oneL_length (T : List VTy) (i : Nat) : (oneL T i).length = T.length := by simp [oneL]

/-- A context consumed up to persistent slots (`Ctx.DeadP`): a constant, `()`, a literal. -/
def Fam.dead (T : List VTy) : Fam T (fun L => Ctx.DeadP (mkCtx T L)) :=
  ⟨noneL T, persL T, noneL_length T, persL_length T, fun _ h => btw_none_deadP h⟩

/-- A context with every slot dead (`Ctx.Dead`), for the derived forms stated with it. -/
def Fam.deadStrict (T : List VTy) : Fam T (fun L => Ctx.Dead (mkCtx T L)) :=
  ⟨noneL T, noneL T, noneL_length T, noneL_length T, fun _ h => btw_none_dead h⟩

/-- Any context: `⟨⟩`. -/
def Fam.top (T : List VTy) : Fam T (fun _ => True) :=
  ⟨noneL T, allL T, noneL_length T, allL_length T, fun _ _ => trivial⟩

theorem oneL_cons_zero (A : VTy) (T : List VTy) : oneL (A :: T) 0 = true :: noneL T := by
  simp only [oneL, noneL, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.ext_getElem <;> simp

theorem oneL_cons_succ (A : VTy) (T : List VTy) (i : Nat) :
    oneL (A :: T) (i + 1) = false :: oneL T i := by
  simp only [oneL, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.ext_getElem <;> simp

theorem btw_one_soloP : ∀ {T : List VTy} {i : Nat} {A : VTy} {L : List Bool},
    T[i]? = some A → Btw (oneL T i) (persL T) L → Ctx.SoloP (mkCtx T L) i A
  | [], _, _, _, h, _ => by simp at h
  | B :: T, 0, A, L, h, hb => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rw [oneL_cons_zero] at hb
      cases hb with
      | cons h₁ _ h => rw [h₁ rfl]; exact .here (btw_none_deadP h)
  | B :: T, i + 1, A, L, h, hb => by
      simp only [List.getElem?_cons_succ] at h
      rw [oneL_cons_succ] at hb
      cases hb with
      | @cons _ _ l _ _ _ _ h₂ hb' =>
          cases l with
          | false => exact .there (btw_one_soloP h hb')
          | true =>
              have : B.persistent = true := by simpa using h₂ rfl
              exact .skip this (btw_one_soloP h hb')

/-- A variable leaf (`Ctx.SoloP`): slot `i`, of type `A`, the other live slots persistent. -/
def Fam.var (T : List VTy) (i : Nat) (A : VTy) (h : T[i]? = some A) :
    Fam T (fun L => Ctx.SoloP (mkCtx T L) i A) :=
  ⟨oneL T i, persL T, oneL_length T i, persL_length T, fun _ hb => btw_one_soloP h hb⟩

/-! ### Transport -/

def Fam.map {T : List VTy} {P Q : List Bool → Prop} (f : ∀ L, P L → Q L) (F : Fam T P) :
    Fam T Q :=
  ⟨F.u, F.w, F.hu, F.hw, fun L h => f L (F.d L h)⟩

/-! ### Splitting -/

/-- The split of one slot: both sides at a slot both use, else the user, else the side that
can absorb it. -/
def choose (a b c l : Bool) : Bool × Bool :=
  if l then (if a && b then (true, true) else if a then (true, false)
    else if b then (false, true) else if c then (true, false) else (false, true))
  else (false, false)

/-- The pointwise split of `L` for uses `u₁`, `u₂` and absorption `w₁`. -/
def chooseL : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | a :: as, b :: bs, c :: cs, l :: ls =>
      ((choose a b c l).1 :: (chooseL as bs cs ls).1, (choose a b c l).2 :: (chooseL as bs cs ls).2)
  | _, _, _, _ => ([], [])

theorem split_lemma : ∀ (T : List VTy) (u₁ w₁ u₂ w₂ L : List Bool),
    u₁.length = T.length → w₁.length = T.length → u₂.length = T.length → w₂.length = T.length →
    overlapOK T u₁ u₂ = true → Btw (orL u₁ u₂) (orL w₁ w₂) L →
    Ctx.SplitP (mkCtx T L) (mkCtx T (chooseL u₁ u₂ w₁ L).1) (mkCtx T (chooseL u₁ u₂ w₁ L).2) ∧
    Btw u₁ w₁ (chooseL u₁ u₂ w₁ L).1 ∧ Btw u₂ w₂ (chooseL u₁ u₂ w₁ L).2
  | [], [], [], [], [], [], _, _, _, _, _, .nil => ⟨.nil, .nil, .nil⟩
  | A :: T, a :: u₁, c :: w₁, b :: u₂, d :: w₂, l :: L, h1, h2, h3, h4, hov, hb => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3 h4
      simp only [overlapOK, Bool.and_eq_true] at hov
      simp only [orL] at hb
      cases hb with
      | cons k₁ k₂ hb =>
      obtain ⟨ih₁, ih₂, ih₃⟩ := split_lemma T u₁ w₁ u₂ w₂ L h1 h2 h3 h4 hov.2 hb
      simp only [chooseL, mkCtx]
      refine ⟨?_, .cons ?_ ?_ ih₂, .cons ?_ ?_ ih₃⟩ <;>
        cases a <;> cases b <;> cases c <;> cases d <;> cases l <;>
        simp_all [choose]
      all_goals first
        | exact .left ih₁ | exact .right ih₁ | exact .dead ih₁
        | exact .dup (by simpa using hov.1) ih₁
  | [], _ :: _, _, _, _, _, h1, _, _, _, _, _ => by simp at h1
  | [], [], _ :: _, _, _, _, _, h2, _, _, _, _ => by simp at h2
  | [], [], [], _ :: _, _, _, _, _, h3, _, _, _ => by simp at h3
  | [], [], [], [], _ :: _, _, _, _, _, h4, _, _ => by simp at h4
  | [], [], [], [], [], _ :: _, _, _, _, _, _, hb => by cases hb
  | _ :: _, [], _, _, _, _, h1, _, _, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, _, _, h2, _, _, _, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _, h3, _, _, _ => by simp at h3
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, h4, _, _ => by simp at h4
  | _ :: _, _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, hb => by
      simp only [orL] at hb; cases hb

/-- `Ctx.SplitP`: the uses of the two sides are disjoint up to persistent slots. -/
def Fam.split {T : List VTy} {P Q : List Bool → Prop} (F₁ : Fam T P) (F₂ : Fam T Q)
    (hov : overlapOK T F₁.u F₂.u = true) :
    Fam T (fun L => ∃ L₁ L₂, Ctx.SplitP (mkCtx T L) (mkCtx T L₁) (mkCtx T L₂) ∧ P L₁ ∧ Q L₂) :=
  ⟨orL F₁.u F₂.u, orL F₁.w F₂.w, by rw [orL_length (F₁.hu.trans F₂.hu.symm)]; exact F₁.hu,
    by rw [orL_length (F₁.hw.trans F₂.hw.symm)]; exact F₁.hw, fun L hb => by
      obtain ⟨hs, h₁, h₂⟩ := split_lemma T F₁.u F₁.w F₂.u F₂.w L F₁.hu F₁.hw F₂.hu F₂.hw hov hb
      exact ⟨_, _, hs, F₁.d _ h₁, F₂.d _ h₂⟩⟩

/-! ### Merging -/

theorem merge_lemma : ∀ (u₁ w₁ u₂ w₂ L : List Bool),
    u₁.length = w₁.length → u₁.length = u₂.length → u₁.length = w₂.length →
    subL u₁ (orL u₂ w₂) = true → subL u₂ (orL u₁ w₁) = true →
    Btw (orL u₁ u₂) (andL (orL u₁ w₁) (orL u₂ w₂)) L → Btw u₁ w₁ L ∧ Btw u₂ w₂ L
  | [], [], [], [], [], _, _, _, _, _, .nil => ⟨.nil, .nil⟩
  | a :: u₁, c :: w₁, b :: u₂, d :: w₂, l :: L, h1, h2, h3, s₁, s₂, hb => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2 h3
      simp only [subL, orL, Bool.and_eq_true] at s₁ s₂
      simp only [orL, andL] at hb
      cases hb with
      | cons k₁ k₂ hb =>
      obtain ⟨ih₁, ih₂⟩ := merge_lemma u₁ w₁ u₂ w₂ L h1 h2 h3 s₁.2 s₂.2 hb
      refine ⟨.cons ?_ ?_ ih₁, .cons ?_ ?_ ih₂⟩ <;>
        cases a <;> cases b <;> cases c <;> cases d <;> cases l <;> simp_all
  | [], _ :: _, _, _, _, h1, _, _, _, _, _ => by simp at h1
  | [], [], _ :: _, _, _, _, h2, _, _, _, _ => by simp at h2
  | [], [], [], _ :: _, _, _, _, h3, _, _, _ => by simp at h3
  | [], [], [], [], _ :: _, _, _, _, _, _, hb => by cases hb
  | _ :: _, [], _, _, _, h1, _, _, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, _, h2, _, _, _, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h3, _, _, _ => by simp at h3
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, _, _, _, _, hb => by
      simp only [orL, andL] at hb; cases hb

/-- Two premises at one context: a slot one side uses, the other uses or can absorb. -/
def Fam.merge {T : List VTy} {P Q : List Bool → Prop} (F₁ : Fam T P) (F₂ : Fam T Q)
    (s₁ : subL F₁.u (orL F₂.u F₂.w) = true) (s₂ : subL F₂.u (orL F₁.u F₁.w) = true) :
    Fam T (fun L => P L ∧ Q L) :=
  ⟨orL F₁.u F₂.u, andL (orL F₁.u F₁.w) (orL F₂.u F₂.w),
    by rw [orL_length (F₁.hu.trans F₂.hu.symm)]; exact F₁.hu,
    by rw [andL_length, orL_length (F₁.hu.trans F₁.hw.symm)]; exact F₁.hu
       rw [orL_length (F₁.hu.trans F₁.hw.symm), orL_length (F₂.hu.trans F₂.hw.symm),
         F₁.hu, F₂.hu],
    fun L hb => by
      obtain ⟨h₁, h₂⟩ := merge_lemma F₁.u F₁.w F₂.u F₂.w L (F₁.hu.trans F₁.hw.symm)
        (F₁.hu.trans F₂.hu.symm) (F₁.hu.trans F₂.hw.symm) s₁ s₂ hb
      exact ⟨F₁.d L h₁, F₂.d L h₂⟩⟩

/-! ### Binders -/

/-- Close a live binder: its slot is used, or can be absorbed. -/
def Fam.popLive {A : VTy} {T : List VTy} {P : List Bool → Prop} (F : Fam (A :: T) P) :
    Option (Fam T (fun L => P (true :: L))) :=
  match F with
  | ⟨u₀ :: us, w₀ :: ws, hu, hw, d⟩ =>
      if h : (u₀ || w₀) = true then
        some ⟨us, ws, by simpa using hu, by simpa using hw, fun L hb =>
          d (true :: L) (.cons (fun _ => rfl) (fun _ => by simpa using h) hb)⟩
      else none
  | ⟨[], _, hu, _, _⟩ => absurd hu (by simp)
  | ⟨_ :: _, [], _, hw, _⟩ => absurd hw (by simp)

/-- Close a dead binder: its slot is not used. -/
def Fam.popDead {A : VTy} {T : List VTy} {P : List Bool → Prop} (F : Fam (A :: T) P) :
    Option (Fam T (fun L => P (false :: L))) :=
  match F with
  | ⟨u₀ :: us, _ :: ws, hu, hw, d⟩ =>
      if h : u₀ = false then
        some ⟨us, ws, by simpa using hu, by simpa using hw, fun L hb =>
          d (false :: L) (.cons (fun h' => by rw [h] at h'; exact h') (fun h' => absurd h' (by simp)) hb)⟩
      else none
  | ⟨[], _, hu, _, _⟩ => absurd hu (by simp)
  | ⟨_ :: _, [], _, hw, _⟩ => absurd hw (by simp)

/-- Whether the head slot is used or absorbable; for error messages. -/
def Fam.headAbsorbs {A : VTy} {T : List VTy} {P : List Bool → Prop} (F : Fam (A :: T) P) : Bool :=
  (F.u.headD false) || (F.w.headD false)

/-! ### A premise on every live slot -/

theorem restrict_lemma (p : VTy → Bool) : ∀ (T : List VTy) (u w L : List Bool),
    u.length = T.length → w.length = T.length →
    usedSat p T u = true → Btw u (andL w (predL p T)) L →
    Btw u w L ∧ ∀ s ∈ mkCtx T L, s.live = true → p s.ty = true
  | [], [], [], [], _, _, _, .nil => ⟨.nil, by simp [mkCtx]⟩
  | A :: T, a :: u, c :: w, l :: L, h1, h2, hs, hb => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      simp only [usedSat, Bool.and_eq_true] at hs
      simp only [andL, predL, List.map_cons] at hb
      cases hb with
      | cons k₁ k₂ hb =>
      obtain ⟨ih₁, ih₂⟩ := restrict_lemma p T u w L h1 h2 hs.2 (by simpa [predL] using hb)
      refine ⟨.cons k₁ ?_ ih₁, ?_⟩
      · intro hl; rcases k₂ hl with h | h
        · exact Or.inl h
        · simp only [Bool.and_eq_true] at h; exact Or.inr h.1
      · intro s hsm hlive
        simp only [mkCtx, List.mem_cons] at hsm
        rcases hsm with rfl | hsm
        · simp only at hlive ⊢
          rcases k₂ hlive with h | h
          · simpa [h] using hs.1
          · simp only [Bool.and_eq_true] at h; exact h.2
        · exact ih₂ s hsm hlive
  | [], _ :: _, _, _, h1, _, _, _ => by simp at h1
  | [], [], _ :: _, _, _, h2, _, _ => by simp at h2
  | [], [], [], _ :: _, _, _, _, hb => by cases hb
  | _ :: _, [], _, _, h1, _, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, _ :: _, [], _, _, _, hb => by simp only [andL, predL, List.map_cons] at hb; cases hb

/-- A premise on every live slot, decided by `p`: every used slot satisfies it, and only
slots satisfying it are absorbed. -/
def Fam.restrict (p : VTy → Bool) {T : List VTy} {P : List Bool → Prop} (F : Fam T P)
    (hs : usedSat p T F.u = true) :
    Fam T (fun L => P L ∧ ∀ s ∈ mkCtx T L, s.live = true → p s.ty = true) :=
  ⟨F.u, andL F.w (predL p T), F.hu, by rw [andL_length (by rw [F.hw, predL_length])]; exact F.hw,
    fun L hb => by
      obtain ⟨h₁, h₂⟩ := restrict_lemma p T F.u F.w L F.hu F.hw hs hb
      exact ⟨F.d L h₁, h₂⟩⟩

/-! ### The whole context -/

/-- Every slot live: each is used or absorbed. -/
theorem btw_allL : ∀ (T : List VTy) (u w : List Bool), u.length = T.length →
    w.length = T.length → subL (allL T) (orL u w) = true → Btw u w (allL T)
  | [], [], [], _, _, _ => .nil
  | _ :: T, a :: u, c :: w, h1, h2, hs => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      simp only [allL, List.map_cons, orL, subL, Bool.not_true, Bool.false_or,
        Bool.and_eq_true, Bool.or_eq_true] at hs
      exact .cons (fun _ => rfl) (fun _ => hs.1) (btw_allL T u w h1 h2 hs.2)
  | [], _ :: _, _, h1, _, _ => by simp at h1
  | [], [], _ :: _, _, h2, _ => by simp at h2
  | _ :: _, [], _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], _, h2, _ => by simp at h2

end BoCa.Fig16.LogRel.Core.Check
