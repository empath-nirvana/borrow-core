import Core.CodeNu
import Core.Compat

/-!
# Core — the code rules' side conditions and compatibility lemmas  `[spec §68]`

`codeI` types a closure `λM : U C` at its code type `Code⟨capNorm (λM); Γ.capTy (λM)⟩ C`;
`codeIB` the same under `!`; `erase` and `eraseB` forget the code. Their side conditions:

* `Ctx.capTy Γ e`: the tensor of `Γ`'s slot types at `capVars e`, in rank order, ending in `1`;
* `Ctx.CapOK Γ e`: every captured slot is live, and every live slot `e` does not capture is
  persistent (`Ctx.capOK`, a decidable test).

The compatibility lemmas at `SemC`:

* `codeI_compatC`: the code conjunct is `lam_psub_capNorm` (the closed thunk is the code at the
  captured values) and `gSepC_capTyOf` (the captured values' tuple is in `𝒱⟦Γ.capTy (λM)⟧` at the
  context's whole resource, the uncaptured live slots being persistent and so at `∅`); the `U C`
  conjunct is the premise's value at the same resource (`vC_thunk_of_wpTS`: forcing it is a bind
  at the value's own run, `cC_bind`).
* `codeIB_compatC`: the same over `!Γ`, at `∅`.
* `erase_compatC`, `eraseB_compatC`: the `U C` conjunct (`wpTS_mono`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The side conditions -/

/-- The type of `Γ`'s slot `i`, `1` past its end.  `[spec §68]` -/
def Ctx.slotTy (Γ : Ctx VTy) (i : Nat) : VTy := (Γ[i]?.map Slot.ty).getD .unit

/-- The tensor of `Γ`'s slot types at the indices `L`, in order, ending in `1`.  `[spec §68]` -/
def Ctx.capTyOf (Γ : Ctx VTy) : List Nat → VTy
  | [] => .unit
  | i :: is => .tensor (Ctx.slotTy Γ i) (Ctx.capTyOf Γ is)

/-- **The environment type of `e` in `Γ`**: the captured slots' types in rank order, ending in
`1`.  `[spec §68]` -/
def Ctx.capTy (Γ : Ctx VTy) (e : Expr) : VTy := Ctx.capTyOf Γ (Expr.capVars e)

/-- The test of `Ctx.CapOK`: every captured slot is live, and every live slot of `Γ` that `e` does
not capture is persistent.  `[spec §68]` -/
def Ctx.capOK (Γ : Ctx VTy) (e : Expr) : Bool :=
  (Expr.capVars e).all (fun i => (Γ[i]?.map Slot.live).getD false) &&
    (List.range Γ.length).all fun i =>
      (Γ[i]?.map fun s => !s.live || (Expr.capVars e).contains i || s.ty.persistent).getD true

/-- **`codeI`'s side condition**: every captured slot is live, and every live slot of `Γ` that
`e` does not capture is persistent.  `[spec §68]` -/
abbrev Ctx.CapOK (Γ : Ctx VTy) (e : Expr) : Prop := Ctx.capOK Γ e = true

theorem Ctx.CapOK.live {Γ : Ctx VTy} {e : Expr} (h : Ctx.CapOK Γ e) :
    ∀ i ∈ Expr.capVars e, ∃ s, Γ[i]? = some s ∧ s.live = true := by
  intro i hi
  unfold Ctx.CapOK Ctx.capOK at h
  rw [Bool.and_eq_true] at h
  have h₁ := List.all_eq_true.mp h.1 i hi
  cases hs : Γ[i]? with
  | none => rw [hs] at h₁; simp at h₁
  | some s => rw [hs] at h₁; exact ⟨s, rfl, by simpa using h₁⟩

theorem Ctx.CapOK.persistent {Γ : Ctx VTy} {e : Expr} (h : Ctx.CapOK Γ e) :
    ∀ i s, Γ[i]? = some s → s.live = true → i ∉ Expr.capVars e → s.ty.Persistent := by
  intro i s hs hl hn
  have hlt : i < Γ.length := (List.getElem?_eq_some_iff.mp hs).1
  unfold Ctx.CapOK Ctx.capOK at h
  rw [Bool.and_eq_true] at h
  have h₂ := List.all_eq_true.mp h.2 i (List.mem_range.mpr hlt)
  rw [hs] at h₂
  simp only [Option.map_some, Option.getD_some, hl, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, List.contains_iff_mem] at h₂
  rcases h₂ with h₂ | h₂
  · exact absurd (by simpa using h₂) hn
  · exact h₂

/-- `Ctx.CapOK` from its two clauses. -/
theorem Ctx.CapOK.mk {Γ : Ctx VTy} {e : Expr}
    (hl : ∀ i ∈ Expr.capVars e, ∃ s, Γ[i]? = some s ∧ s.live = true)
    (hp : ∀ i s, Γ[i]? = some s → s.live = true → i ∉ Expr.capVars e → s.ty.Persistent) :
    Ctx.CapOK Γ e := by
  unfold Ctx.CapOK Ctx.capOK
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.mpr fun i hi => ?_, List.all_eq_true.mpr fun i _ => ?_⟩
  · obtain ⟨s, hs, hl'⟩ := hl i hi
    simp [hs, hl']
  · cases hs : Γ[i]? with
    | none => rfl
    | some s =>
        simp only [Option.map_some, Option.getD_some, Bool.or_eq_true, Bool.not_eq_true',
          List.contains_iff_mem]
        by_cases hl' : s.live = true
        · by_cases hm : i ∈ Expr.capVars e
          · exact .inl (.inr (by simpa using hm))
          · exact .inr (hp i s hs hl' hm)
        · exact .inl (.inl (by simpa using hl'))

/-- **The side conditions along an embedding of contexts**: a renaming `r` of the captures
(`capVars e' = (capVars e).map r`) that reads each slot of `Γ` at the same slot of `Γ'`, every
live slot of `Γ'` being such an image, keeps `Ctx.CapOK` and the environment type.  `[spec §68]` -/
theorem Ctx.CapOK.embed {Γ Γ' : Ctx VTy} {e e' : Expr} {r : Nat → Nat}
    (hcv : Expr.capVars e' = (Expr.capVars e).map r)
    (hr : ∀ i s, Γ[i]? = some s → Γ'[r i]? = some s)
    (hback : ∀ j s, Γ'[j]? = some s → s.live = true → ∃ i, r i = j ∧ Γ[i]? = some s)
    (h : Ctx.CapOK Γ e) : Ctx.CapOK Γ' e' ∧ Ctx.capTy Γ' e' = Ctx.capTy Γ e := by
  refine ⟨Ctx.CapOK.mk (fun j hj => ?_) (fun j s hs hl hn => ?_), ?_⟩
  · rw [hcv] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    obtain ⟨s, hs, hl⟩ := h.live i hi
    exact ⟨s, hr i s hs, hl⟩
  · obtain ⟨i, rfl, hs'⟩ := hback j s hs hl
    refine h.persistent i s hs' hl fun hm => hn ?_
    rw [hcv]; exact List.mem_map.mpr ⟨i, hm, rfl⟩
  · unfold Ctx.capTy
    rw [hcv]
    have key : ∀ L : List Nat, (∀ i ∈ L, ∃ s, Γ[i]? = some s) →
        Ctx.capTyOf Γ' (L.map r) = Ctx.capTyOf Γ L := by
      intro L
      induction L with
      | nil => intro _; rfl
      | cons i is ih =>
          intro hL
          obtain ⟨s, hs⟩ := hL i List.mem_cons_self
          simp only [List.map_cons, Ctx.capTyOf, Ctx.slotTy, hr i s hs, hs,
            ih (fun k hk => hL k (List.mem_cons_of_mem _ hk))]
    exact key _ fun i hi => (h.live i hi).imp fun _ h => h.1

/-- The side conditions at a context extended by dead slots at its end.  `[spec §68]` -/
theorem Ctx.CapOK.append {Γ Γ' : Ctx VTy} {e : Expr} (hd : ∀ s ∈ Γ', s.live = false)
    (h : Ctx.CapOK Γ e) : Ctx.CapOK (Γ ++ Γ') e ∧ Ctx.capTy (Γ ++ Γ') e = Ctx.capTy Γ e :=
  Ctx.CapOK.embed (r := id) (by simp)
    (fun i s hs => by
      show (Γ ++ Γ')[i]? = some s
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hs).1]; exact hs)
    (fun j s hs hl => by
      by_cases hj : j < Γ.length
      · exact ⟨j, rfl, by rwa [List.getElem?_append_left hj] at hs⟩
      · rw [List.getElem?_append_right (Nat.le_of_not_lt hj)] at hs
        rw [hd s (List.mem_of_getElem? hs)] at hl; cases hl)
    h

/-- The side conditions at a context with dead slots inserted, the term shifted past them.
`[spec §68]` -/
theorem Ctx.CapOK.insert {Γa Γd Γb : Ctx VTy} {e : Expr} (hd : ∀ s ∈ Γd, s.live = false)
    (h : Ctx.CapOK (Γa ++ Γb) e) :
    Ctx.CapOK (Γa ++ Γd ++ Γb) (Expr.shift Γd.length Γa.length e) ∧
      Ctx.capTy (Γa ++ Γd ++ Γb) (Expr.shift Γd.length Γa.length e) = Ctx.capTy (Γa ++ Γb) e := by
  have hsh : Expr.shift Γd.length Γa.length e = Expr.ren (shiftIdx Γd.length Γa.length) 0 e := by
    simpa using Expr.shift_eq_ren Γd.length Γa.length e 0
  rw [hsh]
  refine Ctx.CapOK.embed (Expr.capVars_ren (shiftIdx_strictOrd _ _) e) (fun i s hs => ?_)
    (fun j s hs hl => ?_) h
  · unfold shiftIdx
    by_cases hi : i < Γa.length
    · rw [if_pos hi, List.append_assoc, List.getElem?_append_left hi]
      rwa [List.getElem?_append_left hi] at hs
    · rw [if_neg hi, List.getElem?_append_right (by simp only [List.length_append]; omega),
        show i + Γd.length - (Γa ++ Γd).length = i - Γa.length by
          simp only [List.length_append]; omega]
      rwa [List.getElem?_append_right (by omega)] at hs
  · by_cases hj : j < Γa.length
    · refine ⟨j, by simp [shiftIdx, hj], ?_⟩
      rw [List.append_assoc, List.getElem?_append_left hj] at hs
      rwa [List.getElem?_append_left hj]
    · by_cases hj' : j < Γa.length + Γd.length
      · rw [List.append_assoc, List.getElem?_append_right (by omega),
          List.getElem?_append_left (by omega)] at hs
        rw [hd s (List.mem_of_getElem? hs)] at hl; cases hl
      · refine ⟨j - Γd.length, by unfold shiftIdx; rw [if_neg (by omega)]; omega, ?_⟩
        rw [List.getElem?_append_right (by simp only [List.length_append]; omega),
          show j - (Γa ++ Γd).length = j - Γd.length - Γa.length by
            simp only [List.length_append]; omega] at hs
        rwa [List.getElem?_append_right (by omega)]

/-! ### The captures are sorted -/

theorem sortIns_pairwise (x : Nat) :
    ∀ l : List Nat, l.Pairwise (· < ·) → (sortIns x l).Pairwise (· < ·)
  | [], _ => List.pairwise_singleton _ _
  | y :: ys, h => by
      simp only [sortIns]
      split
      · rename_i hxy
        refine List.Pairwise.cons (fun z hz => ?_) h
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hxy
        · exact Nat.lt_trans hxy (List.rel_of_pairwise_cons h hz)
      · split
        · exact h
        · rename_i hxy hne
          refine List.Pairwise.cons (fun z hz => ?_) (sortIns_pairwise x ys h.of_cons)
          rcases (mem_sortIns z x ys).mp hz with rfl | hz
          · omega
          · exact List.rel_of_pairwise_cons h hz

/-- **The captures are in increasing order**, without repeats.  `[spec §68]` -/
theorem Expr.capVars_pairwise (e : Expr) : (Expr.capVars e).Pairwise (· < ·) := by
  unfold Expr.capVars
  induction Expr.occs 0 e with
  | nil => exact List.Pairwise.nil
  | cons x xs ih => exact sortIns_pairwise x _ ih

/-! ### The captured values compose to the environment -/

/-- A live slot is within the substitution. -/
theorem Ctx.LiveWithin.lt {τ σ : Type} : ∀ {Γ : Ctx τ} {γ : List σ} {i : Nat} {s : Slot τ},
    Ctx.LiveWithin Γ γ → Γ[i]? = some s → s.live = true → i < γ.length
  | [], _, _, _, _, hs, _ => by simp at hs
  | t :: Γ, [], 0, s, hw, hs, hl => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
      subst hs; exact absurd hl hw.1
  | t :: Γ, [], i + 1, s, hw, hs, hl => by
      simp only [List.getElem?_cons_succ] at hs
      exact absurd (Ctx.LiveWithin.lt (γ := ([] : List σ)) hw.2 hs hl) (Nat.not_lt_zero _)
  | t :: Γ, v :: γ, 0, s, _, _, _ => by simp
  | t :: Γ, v :: γ, i + 1, s, hw, hs, hl => by
      simp only [List.getElem?_cons_succ] at hs
      simpa using Ctx.LiveWithin.lt (γ := γ) hw hs hl

theorem Ctx.capTyOf_tail {Γ : Ctx VTy} {s : Slot VTy} :
    ∀ L : List Nat, (∀ i ∈ L, 0 < i) → Ctx.capTyOf (s :: Γ) L = Ctx.capTyOf Γ (L.map (· - 1))
  | [], _ => rfl
  | i :: is, h => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := h i List.mem_cons_self; omega⟩
      simp only [Ctx.capTyOf, List.map_cons, Nat.add_sub_cancel, Ctx.slotTy,
        List.getElem?_cons_succ]
      rw [Ctx.capTyOf_tail is (fun k hk => h k (List.mem_cons_of_mem _ hk))]

theorem capVals_tail {v : Val} {γ : List Val} :
    ∀ L : List Nat, (∀ i ∈ L, 0 < i) →
      L.map (fun i => (v :: γ).getD i Val.unit) = (L.map (· - 1)).map (fun i => γ.getD i Val.unit)
  | [], _ => rfl
  | i :: is, h => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by have := h i List.mem_cons_self; omega⟩
      simp only [List.map_cons, Nat.add_sub_cancel, List.getD_cons_succ]
      rw [capVals_tail is (fun k hk => h k (List.mem_cons_of_mem _ hk))]

theorem pairwise_pred {L : List Nat} (h : L.Pairwise (· < ·)) (hp : ∀ i ∈ L, 0 < i) :
    (L.map (· - 1)).Pairwise (· < ·) :=
  List.pairwise_map.mpr (h.imp_of_mem fun ha hb hab => by
    have := hp _ ha; have := hp _ hb; omega)

/-- **The captured slots' values compose to the environment tuple** at the context's whole
resource: the slots at `L` (sorted, live) hold `𝒱⟦Γ.capTyOf L⟧` of their values' tuple, and every
other live slot is persistent, so at `∅`.  `[spec §68]` -/
theorem gSepC_capTyOf {ls : List SRec} {δ : LSub} : ∀ (Γ : Ctx VTy) (γ : List Val) (L : List Nat)
    (ρ : WRes), L.Pairwise (· < ·) → (∀ i ∈ L, ∃ s, Γ[i]? = some s ∧ s.live = true) →
    (∀ i s, Γ[i]? = some s → s.live = true → i ∉ L → s.ty.Persistent) →
    Ctx.LiveWithin Γ γ → gSepC ls δ Γ γ ρ →
    vC true (Ctx.capTyOf Γ L) ls δ (tupleV (L.map fun i => γ.getD i Val.unit)) ρ
  | [], γ, L, ρ, _, hc, _, _, hg => by
      have hL : L = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        obtain ⟨s, hs, -⟩ := hc i hi; simp at hs
      subst hL
      have hρ : ρ = PMap.empty := by cases γ <;> exact hg.1
      exact ⟨hρ, rfl⟩
  | s :: Γ, [], L, ρ, _, hc, _, hw, hg => by
      have hL : L = [] := List.eq_nil_iff_forall_not_mem.mpr fun i hi => by
        obtain ⟨s', hs, hl⟩ := hc i hi
        exact absurd (Ctx.LiveWithin.lt hw hs hl) (Nat.not_lt_zero _)
      subst hL
      exact ⟨hg.1, rfl⟩
  | ⟨T, l⟩ :: Γ, v :: γ, L, ρ, hp, hc, hper, hw, hg => by
      by_cases h0 : 0 ∈ L
      · -- the head slot is captured: `L = 0 :: L'`
        obtain ⟨L', rfl⟩ : ∃ L', L = 0 :: L' := by
          cases L with
          | nil => simp at h0
          | cons a L' =>
              rcases List.mem_cons.mp h0 with h | h
              · exact ⟨L', by rw [h]⟩
              · exact absurd (List.rel_of_pairwise_cons hp h) (Nat.not_lt_zero _)
        have hpos : ∀ i ∈ L', 0 < i := fun i hi => List.rel_of_pairwise_cons hp hi
        obtain ⟨s₀, hs₀, hl₀⟩ := hc 0 List.mem_cons_self
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hs₀
        subst hs₀
        simp only at hl₀
        subst hl₀
        obtain ⟨ρ₁, ρ₂, hcρ, hv, hrest⟩ := hg
        have ih := gSepC_capTyOf Γ γ (L'.map (· - 1)) ρ₂ (pairwise_pred hp.of_cons hpos)
          (fun j hj => by
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
            obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := hpos i hi; omega⟩
            simpa using hc (k + 1) (List.mem_cons_of_mem _ hi))
          (fun j s hs hl hn => hper (j + 1) s (by simpa using hs) hl (by
            intro hm
            rcases List.mem_cons.mp hm with h | h
            · omega
            · exact hn (List.mem_map.mpr ⟨j + 1, h, by simp⟩)))
          hw hrest
        rw [← Ctx.capTyOf_tail L' hpos, ← capVals_tail L' hpos] at ih
        refine ⟨v, _, pure_sep_mk rfl ⟨ρ₁, ρ₂, hcρ, ?_, ih⟩⟩
        simpa [Ctx.capTyOf, Ctx.slotTy] using hv
      · -- the head slot is not captured: it is dead, or persistent at `∅`
        have hpos : ∀ i ∈ L, 0 < i := fun i hi => Nat.pos_of_ne_zero (fun h => h0 (h ▸ hi))
        have hrest : gSepC ls δ Γ γ ρ := by
          cases l with
          | false => exact hg
          | true =>
              exact (gSepC_cons_persistent (hper 0 ⟨T, true⟩ rfl rfl h0) hg).2
        have ih := gSepC_capTyOf Γ γ (L.map (· - 1)) ρ (pairwise_pred hp hpos)
          (fun j hj => by
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
            obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := hpos i hi; omega⟩
            simpa using hc (k + 1) hi)
          (fun j s hs hl hn => hper (j + 1) s (by simpa using hs) hl (by
            intro hm
            exact hn (List.mem_map.mpr ⟨j + 1, hm, by simp⟩)))
          hw hrest
        rwa [← Ctx.capTyOf_tail L hpos, ← capVals_tail L hpos] at ih

/-- **`codeI`'s semantic step**: under `Ctx.CapOK`, the captured values `capEnv e γ` are in
`𝒱⟦Γ.capTy e⟧` at the context's whole resource.  `[spec §68]` -/
theorem gSepC_capTy {ls : List SRec} {δ : LSub} {Γ : Ctx VTy} {γ : List Val} {ρ : WRes}
    {e : Expr} (hok : Ctx.CapOK Γ e) (hw : Ctx.LiveWithin Γ γ) (hg : gSepC ls δ Γ γ ρ) :
    vC true (Ctx.capTy Γ e) ls δ (tupleV (Expr.capEnv e γ)) ρ :=
  gSepC_capTyOf Γ γ _ ρ (Expr.capVars_pairwise e) hok.live
    (fun i s hs hl hn => hok.persistent i s hs hl hn) hw hg

/-- Under `Ctx.CapOK`, the free variables of `e` are within the substitution. -/
theorem Ctx.CapOK.occs_lt {Γ : Ctx VTy} {γ : List Val} {e : Expr} (hok : Ctx.CapOK Γ e)
    (hw : Ctx.LiveWithin Γ γ) : ∀ i ∈ Expr.occs 0 e, i < γ.length := fun i hi => by
  obtain ⟨s, hs, hl⟩ := hok.live i (Expr.mem_capVars.mpr hi)
  exact Ctx.LiveWithin.lt hw hs hl

/-! ### A value at `U C`, at its own resource -/

/-- `force` as a frame around the forced value. -/
theorem forceE_plug (C : CTy) : ∃ K : Kont, ∀ e, forceE C e = K.plug e := by
  cases C with
  | ret A => exact ⟨.appL .hole Val.unit, fun _ => rfl⟩
  | eff n i q A B fin rc C => exact ⟨.appL .hole Val.unit, fun _ => rfl⟩
  | _ => exact ⟨.hole, fun _ => rfl⟩

/-- **A value that runs to `𝒱⟦U C⟧` at every extension of the list is in `𝒱⟦U C⟧`**: forcing it
is a bind at its own run (`cC_bind`). -/
theorem vC_thunk_of_wpTS {ls : List SRec} {δ : LSub} {C : CTy} {w : Val} {ρ : WRes}
    {P : List SRec → Val → WProp} (hP : ∀ l v σ, P l v σ → vC true (.thunk C) l δ v σ)
    (hw : ∀ ls', Ext ls ls' ρ → wpTS ls' (.val w) P ρ) : vC true (.thunk C) ls δ w ρ := by
  intro ls' hext
  obtain ⟨K, hK⟩ := forceE_plug C
  rw [hK]
  refine cC_bind C K (.val w) ls' δ P (fun _ => emp) (fun _ _ _ h => h) ?_ ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, hw ls' hext, rfl, trivial⟩
  rintro l - v σ ⟨σ₁, σ₂, hc, hv, he⟩
  rw [he.1] at hc
  rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁), ← hK]
  exact hP l v σ₁ hv l (Ext.refl _ _)

/-! ### The compatibility lemmas -/

/-- **`codeI`'s compatibility**: a closure at `U C` is at its code type, under `Ctx.CapOK`.  The
code conjunct: the closed thunk is `capNorm (λM)` at `capEnv (λM) γ` (`lam_psub_capNorm`), whose
tuple is in `𝒱⟦Γ.capTy (λM)⟧` at the whole resource (`gSepC_capTy`).  The `U C` conjunct: the
premise's value at the same resource (`vC_thunk_of_wpTS`).  `[spec §68]` -/
theorem codeI_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy}
    (h : SemV Δ Γ (.val (.lam M)) (.thunk C)) (hok : Ctx.CapOK Γ (.lam M)) :
    SemV Δ Γ (.val (.lam M)) (.code (Expr.capNorm (.lam M)) (Ctx.capTy Γ (.lam M)) C) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hw, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _ ⟨⟨Expr.capEnv (.lam M) γ, ?_, gSepC_capTy hok hw hgs⟩, ?_⟩
  · exact Expr.lam_psub_capNorm M γ (hok.occs_lt hw)
  · exact vC_thunk_of_wpTS (fun _ _ _ h => h) fun ls' hext => h δ γ ls' ρ hδ (gDenC_local hext hg)

/-- **`codeIB`'s compatibility**: `codeI` under `!`, over `!Γ` (`gSepC_persistent`: at `∅`).
`[spec §68]` -/
theorem codeIB_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr} {C : CTy} (hp : Ctx.Banged Γ)
    (h : SemV Δ Γ (.val (.lam M)) (.bang (.thunk C))) (hok : Ctx.CapOK Γ (.lam M)) :
    SemV Δ Γ (.val (.lam M)) (.bang (.code (Expr.capNorm (.lam M)) (Ctx.capTy Γ (.lam M)) C)) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨hw, hgs⟩ := gDenC_iff.mp hg
  show wpTS ls (.val (.lam (Expr.psub 1 γ M))) _ ρ
  refine wpTS_val _ _ _ _
    ⟨gSepC_persistent hp hgs, ⟨Expr.capEnv (.lam M) γ, ?_, gSepC_capTy hok hw hgs⟩, ?_⟩
  · exact Expr.lam_psub_capNorm M γ (hok.occs_lt hw)
  · exact vC_thunk_of_wpTS (fun _ _ _ h => h.2) fun ls' hext =>
      h δ γ ls' ρ hδ (gDenC_local hext hg)

/-- **`erase`'s compatibility**: the `U C` conjunct.  `[spec §68]` -/
theorem erase_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {N : Expr} {E : VTy} {C : CTy}
    (h : SemV Δ Γ e (.code N E C)) : SemV Δ Γ e (.thunk C) := fun δ γ ls ρ hδ hg =>
  wpTS_mono (fun _ _ _ hv => hv.2) ρ (h δ γ ls ρ hδ hg)

/-- **`eraseB`'s compatibility**: the `U C` conjunct under `!`.  `[spec §68]` -/
theorem eraseB_compatC {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {N : Expr} {E : VTy} {C : CTy}
    (h : SemV Δ Γ e (.bang (.code N E C))) : SemV Δ Γ e (.bang (.thunk C)) :=
  fun δ γ ls ρ hδ hg => wpTS_mono (fun _ _ _ hv => ⟨hv.1, hv.2.2⟩) ρ (h δ γ ls ρ hδ hg)

end BoCa.Fig16.LogRel.Core

end
