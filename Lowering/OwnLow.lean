import Lowering.OwnSem
import Lowering.LowRen

/-!
# Lowering — `own`'s output is low  `[spec §54]`

**On the pure fragment `own` lands in the low subset** (`own_lowersInto`): every binder, every
captured variable and every context variable of its output is consumed exactly once on every
path, and no effect primitive is left. The proof reads `own`'s output node by node:

- a part of a split consumes exactly the live slots its mask gives it (`ExactP`), so a slot
  neither part receives is dropped once, a slot both receive is copied once and each copy read by
  one part (`exact_copies`, `exact_splitE`), and every other live slot is read by one part;
- a leaf reads its variable and drops the others (`exact_leafE`).

A part's leaves read only slots its mask holds (`agreeAt`), because the typed split rules make a
split's masks cover its parts (`Covers`, SPEC §55) and a binder typed dead is never mentioned
(`CDerivesP.mentions_live`): `agreeAt_of_typed`. `coverage_excludes_missT` is a term whose masks
`SplitMasks` admits but which coverage excludes, and at which `own`'s output reads a binder twice.

`own_dupChecked_low` is a checked `main` meeting the hypotheses: `return (λx. (x, x))`, whose
copy `own` writes (`own_dupChecked`).
-/

namespace Lowering
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (closedAt)
open BoCa.Lifetime (LifeCtx)
open Frontend.Check (Checked)

/-! ### Consuming exactly a set of slots -/

/-- `e` consumes each slot `P` holds once on every path and mentions it, and mentions no other. -/
def ExactP (P : Nat → Prop) (e : Expr) : Prop :=
  ∀ k, (P k → once (occ e k) = true ∧ mentions e k = true) ∧ (¬ P k → mentions e k = false)

theorem ExactP.congr {P Q : Nat → Prop} {e : Expr} (h : ExactP P e) (hPQ : ∀ k, P k ↔ Q k) :
    ExactP Q e := fun k => ⟨fun hq => (h k).1 ((hPQ k).mpr hq), fun hq => (h k).2 (fun hp => hq ((hPQ k).mp hp))⟩

theorem ExactP.zero {P : Nat → Prop} {e : Expr} (h : ExactP P e) {k : Nat} (hk : ¬ P k) :
    ZeroU (occ e k) := zeroU_of_not_mentions ((h k).2 hk)

/-- A closed term consumes nothing. -/
theorem exact_closed {e : Expr} (h : closedAt 0 e = true) : ExactP (fun _ => False) e :=
  fun _ => ⟨fun h => h.elim, fun _ => mentions_of_closedAt h (Nat.zero_le _)⟩

theorem exact_var (i : Nat) : ExactP (· = i) (.var i) := by
  intro k
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · subst hk; simp [occ_var, once, mentions, Uses.one]
  · simp [mentions]; omega

/-- **Renaming moves the consumed slots.** -/
theorem exact_ren {P : Nat → Prop} {e : Expr} {ρ : Nat → Nat} (hρ : Function.Injective ρ)
    (h : ExactP P e) : ExactP (fun j => ∃ i, P i ∧ ρ i = j) (ren ρ e) := by
  intro j
  refine ⟨fun ⟨i, hi, hj⟩ => ?_, fun hj => ?_⟩
  · subst hj
    rw [occ_ren hρ, mentions_ren hρ]
    exact (h i).1 hi
  · by_cases hr : ∃ i, ρ i = j
    · obtain ⟨i, rfl⟩ := hr
      rw [mentions_ren hρ]
      exact (h i).2 fun hi => hj ⟨i, hi, rfl⟩
    · exact mentions_ren_out e fun i hi => hr ⟨i, hi⟩

/-- Two parts in sequence, consuming disjoint slots. -/
theorem exact_seqO {P Q : Nat → Prop} {a b e : Expr} (ha : ExactP P a) (hb : ExactP Q b)
    (hd : ∀ k, ¬ (P k ∧ Q k)) (hocc : ∀ k, occ e k = seqO (occ a k) (occ b k))
    (hm : ∀ k, mentions e k = (mentions a k || mentions b k)) : ExactP (fun k => P k ∨ Q k) e := by
  intro k
  rw [hocc, hm]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rcases hk with hp | hq
    · have hnq : ¬ Q k := fun hq => hd k ⟨hp, hq⟩
      exact ⟨seqO_one_zero ((ha k).1 hp).1 (hb.zero hnq), by simp [((ha k).1 hp).2]⟩
    · have hnp : ¬ P k := fun hp => hd k ⟨hp, hq⟩
      exact ⟨seqO_zero_one (ha.zero hnp) ((hb k).1 hq).1, by simp [((hb k).1 hq).2]⟩
  · simp [(ha k).2 (fun h => hk (.inl h)), (hb k).2 (fun h => hk (.inr h))]

/-- **A `λ` whose body consumes its binder**: it consumes the body's other slots, each once. -/
theorem exact_lam {P : Nat → Prop} {b : Expr} (hb : ExactP P b) :
    ExactP (fun k => P (k + 1)) (.lam b) := by
  intro k
  rw [occ_lam]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · have := (hb (k + 1)).1 hk
    simp [this.2, once, mentions]
  · exact (hb (k + 1)).2 hk

theorem explicitC_lam {P : Nat → Prop} {b : Expr} (hx : ExplicitC b) (hb : ExactP P b) (h0 : P 0) :
    ExplicitC (.lam b) :=
  .lam hx ((hb 0).1 h0).1 fun j hj => by
    by_cases hp : P (j + 1)
    · exact ((hb (j + 1)).1 hp).1
    · rw [(hb (j + 1)).2 hp] at hj; exact absurd hj (by simp)

/-- `(); e` at the dead binder `0`: the binder consumed. -/
theorem exact_seq_var0 {P : Nat → Prop} {M : Expr} (hM : ExactP P M) (h0 : ¬ P 0) :
    ExactP (fun k => k = 0 ∨ P k) (.seq (.var 0) M) :=
  exact_seqO (exact_var 0) hM (fun _ ⟨h, hp⟩ => h0 (h ▸ hp)) (fun _ => rfl) (fun _ => rfl)

/-! ### Drops -/

theorem exact_dropE {P : Nat → Prop} {e : Expr} {k : Nat} (he : ExactP P e) (hk : ¬ P k) :
    ExactP (fun j => j = k ∨ P j) (dropE k e) := by
  have hf : ExactP (· = k) (.app forget (.var k)) :=
    exact_seqO (exact_var k) (exact_closed (e := forget) rfl) (fun _ h => h.2)
      (fun _ => rfl) (fun j => by simp [mentions, Bool.or_comm]) |>.congr (by simp)
  exact exact_seqO hf he (fun j ⟨h, hp⟩ => hk (h ▸ hp)) (fun _ => rfl) (fun _ => rfl)

theorem exact_dropsE {P : Nat → Prop} {e : Expr} :
    ∀ {ks : List Nat}, ks.Nodup → (∀ k ∈ ks, ¬ P k) → ExactP P e →
      ExactP (fun j => j ∈ ks ∨ P j) (dropsE ks e)
  | [], _, _, he => he.congr (by simp)
  | k :: ks, hn, hk, he => by
      have hn' := List.nodup_cons.mp hn
      have ih := exact_dropsE hn'.2 (fun j hj => hk j (by simp [hj])) he
      refine (exact_dropE ih ?_).congr (fun j => by simp [or_assoc])
      rintro (h | h)
      · exact hn'.1 h
      · exact hk k (by simp) h

theorem explicitC_dropsE {e : Expr} (he : ExplicitC e) :
    ∀ ks : List Nat, ExplicitC (dropsE ks e)
  | [] => he
  | k :: ks => .seq (.app (.const (LowConst.node (.forgetBang default (.val .unit) .unit) rfl) rfl)
      (.var k)) (explicitC_dropsE he ks)

theorem effFreeB_dropsE {e : Expr} (he : effFreeB e = true) : ∀ ks : List Nat,
    effFreeB (dropsE ks e) = true
  | [] => he
  | _ :: ks => by simp [dropsE, dropE, effFreeB, forget, unit'] at *; exact effFreeB_dropsE he ks

theorem liveIdx_nodup (L : List Bool) : (liveIdx L).Nodup :=
  (List.nodup_range).filter _

theorem mem_liveIdx {L : List Bool} {k : Nat} : k ∈ liveIdx L ↔ lv L k = true := by
  simp only [liveIdx, List.mem_filter, List.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    by_contra hk
    simp [lv, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ k)] at h

/-- **A leaf**: it reads `keep`, and drops every other live slot. -/
theorem exact_leafE {L : List Bool} {keep : Option Nat} {e : Expr} {P : Nat → Prop}
    (he : ExactP P e) (hP : ∀ k, P k ↔ keep = some k) (hkeep : ∀ k, keep = some k → lv L k = true) :
    ExactP (fun k => lv L k = true) (leafE L keep e) := by
  refine (exact_dropsE ((liveIdx_nodup L).filter _) (fun k hk => ?_) he).congr fun k => ?_
  · rw [hP]; simp only [List.mem_filter] at hk
    intro h; apply absurd h.symm; simpa using hk.2
  · simp only [List.mem_filter, mem_liveIdx, hP]
    constructor
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hkeep k h
    · intro h
      by_cases hk : keep = some k
      · exact .inr hk
      · refine .inl ⟨h, ?_⟩
        simp only [bne_iff_ne, ne_eq]
        exact fun h' => hk h'.symm

/-! ### Binders -/

/-- A `let` whose body consumes its two binders. -/
theorem exact_letpair {P Q : Nat → Prop} {a b : Expr} (ha : ExactP P a) (hb : ExactP Q b)
    (hd : ∀ k, ¬ (P k ∧ Q (k + 2))) : ExactP (fun k => P k ∨ Q (k + 2)) (.letpair a b) := by
  intro k
  rw [occ_letpair]
  simp only [mentions]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rcases hk with hp | hq
    · exact ⟨seqO_one_zero ((ha k).1 hp).1 (hb.zero fun hq => hd k ⟨hp, hq⟩),
        by simp [((ha k).1 hp).2]⟩
    · exact ⟨seqO_zero_one (ha.zero fun hp => hd k ⟨hp, hq⟩) ((hb (k + 2)).1 hq).1,
        by simp [((hb (k + 2)).1 hq).2]⟩
  · simp [(ha k).2 (fun h => hk (.inl h)), (hb (k + 2)).2 (fun h => hk (.inr h))]

/-- A `case` whose arms each consume their binder and the same slots. -/
theorem exact_case {P Q : Nat → Prop} {s a b : Expr} (hs : ExactP P s) (ha : ExactP Q a)
    (hb : ExactP Q b) (h0 : Q 0) (hd : ∀ k, ¬ (P k ∧ Q (k + 1))) :
    ExactP (fun k => P k ∨ Q (k + 1)) (.case s a b) := by
  have hna : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE) := by
    rintro ⟨rfl, -⟩
    have := ((ha 0).1 h0).2
    simp [BoLo.stuckE, mentions] at this
  intro k
  rw [occ_case, if_neg hna]
  simp only [mentions]
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rcases hk with hp | hq
    · refine ⟨seqO_one_zero ((hs k).1 hp).1 ?_, by simp [((hs k).1 hp).2]⟩
      exact joinO_zero (ha.zero fun hq => hd k ⟨hp, hq⟩) (hb.zero fun hq => hd k ⟨hp, hq⟩)
    · exact ⟨seqO_zero_one (hs.zero fun hp => hd k ⟨hp, hq⟩)
        (joinO_one ((ha (k + 1)).1 hq).1 ((hb (k + 1)).1 hq).1), by simp [((ha (k + 1)).1 hq).2]⟩
  · simp [(hs k).2 (fun h => hk (.inl h)), (ha (k + 1)).2 (fun h => hk (.inr h)),
      (hb (k + 1)).2 (fun h => hk (.inr h))]

/-- `absurd` consumes its scrutinee's slots: its path ends there. -/
theorem exact_absurdL {P : Nat → Prop} {s : Expr} (hs : ExactP P s) : ExactP P (absurdL s) := by
  intro k
  rw [occ_absurdL]
  simp only [absurdL, mentions, BoLo.stuckE]
  refine ⟨fun hk => ⟨seqO_halt_one ((hs k).1 hk).1, by simp [((hs k).1 hk).2]⟩, fun hk => ?_⟩
  simp [(hs k).2 hk, mentions]

/-! ### Copies -/

/-- **A node at a split** at its parts' renamings: explicit, free of effect primitives, and
consuming the images of its parts' slots, whenever the renamings are injective and keep the
parts' slots apart. -/
def GoodNode (F : Node) (P₁ P₂ : Nat → Prop) : Prop :=
  ∀ ρ₁ ρ₂, Function.Injective ρ₁ → Function.Injective ρ₂ →
    (∀ i j, P₁ i → P₂ j → ρ₁ i ≠ ρ₂ j) →
    ExplicitC (F ρ₁ ρ₂) ∧ effFreeB (F ρ₁ ρ₂) = true ∧
      ExactP (fun k => (∃ i, P₁ i ∧ ρ₁ i = k) ∨ (∃ i, P₂ i ∧ ρ₂ i = k)) (F ρ₁ ρ₂)

theorem cpL_injective (c : Nat) : Function.Injective (cpL c) := by
  intro a b h; simp only [cpL] at h; split_ifs at h <;> omega

theorem cpR_injective (c : Nat) : Function.Injective (cpR c) := by
  intro a b h; simp only [cpR] at h; split_ifs at h <;> omega

theorem lowConst_copy' : LowConst copy := LowConst.node (.copyBang default (.val .unit) .unit) rfl

/-- **The copies**: each slot both parts read is copied once, its copies read once each. -/
theorem exact_copies : ∀ (ks : List Nat) (off : Nat) (F : Node) (P₁ P₂ : Nat → Prop),
    GoodNode F P₁ P₂ → (ks.map (· + off)).Nodup → (∀ k ∈ ks, P₁ (k + off) ∧ P₂ (k + off)) →
    (∀ i, P₁ i → P₂ i → i ∈ ks.map (· + off)) →
    ExplicitC (copiesE off ks F) ∧ effFreeB (copiesE off ks F) = true ∧
      ExactP (fun k => P₁ k ∨ P₂ k) (copiesE off ks F)
  | [], off, F, P₁, P₂, hF, _, _, hsh => by
      obtain ⟨hx, he, hex⟩ := hF id id Function.injective_id Function.injective_id
        (fun i j h₁ h₂ hij => by
          simp only [id] at hij; subst hij; simpa using hsh i h₁ h₂)
      exact ⟨hx, he, hex.congr fun k => by simp⟩
  | k :: ks, off, F, P₁, P₂, hF, hn, hks, hsh => by
      set c := k + off with hc
      obtain ⟨hP₁c, hP₂c⟩ := hks k (by simp)
      have hn' : c ∉ ks.map (· + off) ∧ (ks.map (· + off)).Nodup := by
        simpa [List.map_cons, List.nodup_cons, hc] using hn
      let P₁' : Nat → Prop := fun j => j = 1 ∨ ∃ i, P₁ i ∧ i ≠ c ∧ i + 2 = j
      let P₂' : Nat → Prop := fun j => j = 0 ∨ ∃ i, P₂ i ∧ i ≠ c ∧ i + 2 = j
      have hP₁' : ∀ j, P₁' j ↔ ∃ i, P₁ i ∧ cpL c i = j := fun j => by
        simp only [P₁', cpL]
        constructor
        · rintro (rfl | ⟨i, hi, hic, rfl⟩)
          · exact ⟨c, hP₁c, by simp⟩
          · exact ⟨i, hi, by simp [hic]⟩
        · rintro ⟨i, hi, rfl⟩
          by_cases hic : i = c
          · simp [hic]
          · exact .inr ⟨i, hi, hic, by simp [hic]⟩
      have hP₂' : ∀ j, P₂' j ↔ ∃ i, P₂ i ∧ cpR c i = j := fun j => by
        simp only [P₂', cpR]
        constructor
        · rintro (rfl | ⟨i, hi, hic, rfl⟩)
          · exact ⟨c, hP₂c, by simp⟩
          · exact ⟨i, hi, by simp [hic]⟩
        · rintro ⟨i, hi, rfl⟩
          by_cases hic : i = c
          · simp [hic]
          · exact .inr ⟨i, hi, hic, by simp [hic]⟩
      have hF' : GoodNode (fun r₁ r₂ => F (r₁ ∘ cpL c) (r₂ ∘ cpR c)) P₁' P₂' := by
        intro ρ₁ ρ₂ h₁ h₂ hd
        obtain ⟨hx, he, hex⟩ := hF (ρ₁ ∘ cpL c) (ρ₂ ∘ cpR c) (h₁.comp (cpL_injective c))
          (h₂.comp (cpR_injective c)) (fun i j hi hj => hd _ _ ((hP₁' _).mpr ⟨i, hi, rfl⟩)
            ((hP₂' _).mpr ⟨j, hj, rfl⟩))
        refine ⟨hx, he, hex.congr fun m => ?_⟩
        constructor
        · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
          · exact .inl ⟨_, (hP₁' _).mpr ⟨i, hi, rfl⟩, rfl⟩
          · exact .inr ⟨_, (hP₂' _).mpr ⟨i, hi, rfl⟩, rfl⟩
        · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
          · obtain ⟨i, hi, rfl⟩ := (hP₁' j).mp hj; exact .inl ⟨i, hi, rfl⟩
          · obtain ⟨i, hi, rfl⟩ := (hP₂' j).mp hj; exact .inr ⟨i, hi, rfl⟩
      have ih := exact_copies ks (off + 2) _ P₁' P₂' hF'
        (by
          have : ks.map (· + (off + 2)) = (ks.map (· + off)).map (· + 2) := by
            simp [List.map_map, Function.comp_def, Nat.add_assoc]
          rw [this]; exact hn'.2.map (fun a b h => by omega))
        (fun k' hk' => by
          have hne : k' + off ≠ c := fun h => hn'.1 (h ▸ List.mem_map_of_mem hk')
          obtain ⟨h₁, h₂⟩ := hks k' (by simp [hk'])
          exact ⟨.inr ⟨_, h₁, hne, by omega⟩, .inr ⟨_, h₂, hne, by omega⟩⟩)
        (by
          rintro j (rfl | ⟨i, hi, hic, rfl⟩) (h | ⟨i', hi', hic', h⟩)
          · exact absurd h (by decide)
          · omega
          · omega
          · have hii : i' = i := by omega
            subst hii
            have := hsh i' hi hi'
            simp only [List.map_cons, List.mem_cons] at this
            rcases this with h | h
            · exact absurd h hic
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
              exact List.mem_map.mpr ⟨a, ha, by omega⟩)
      obtain ⟨hx, he, hex⟩ := ih
      refine ⟨.letpair (.app (.const lowConst_copy' rfl) (.var _)) hx ?_ ?_, ?_, ?_⟩
      · exact ((hex 0).1 (.inr (.inl rfl))).1
      · exact ((hex 1).1 (.inl (.inl rfl))).1
      · show effFreeB (.letpair (.app copy (.var c)) _) = true
        simp only [effFreeB, Bool.and_eq_true]
        exact ⟨⟨rfl, trivial⟩, he⟩
      · have hcp : ExactP (· = c) (.app copy (.var c)) :=
          (exact_seqO (exact_var c) (exact_closed (e := copy) rfl) (fun _ h => h.2)
            (fun _ => rfl) (fun j => by simp [mentions, Bool.or_comm])).congr (by simp)
        refine (exact_letpair hcp hex ?_).congr fun m => ?_
        · rintro m ⟨rfl, (h | ⟨i, -, hic, h⟩) | (h | ⟨i, -, hic, h⟩)⟩ <;> omega
        · by_cases hm : m = c
          · subst hm
            exact ⟨fun _ => .inl hP₁c, fun _ => .inl rfl⟩
          · simp only [hm, false_or, P₁', P₂']
            constructor
            · rintro ((h | ⟨i, hi, -, h⟩) | (h | ⟨i, hi, -, h⟩))
              · omega
              · exact .inl (by rw [show m = i by omega]; exact hi)
              · omega
              · exact .inr (by rw [show m = i by omega]; exact hi)
            · rintro (h | h)
              · exact .inl (.inr ⟨m, h, hm, rfl⟩)
              · exact .inr (.inr ⟨m, h, hm, rfl⟩)

/-! ### A thunk's `λ` -/

theorem CTy.unroll_isRet {C : CTy} (hC : C.NuOk) : (CTy.unroll C).isRet = false := by
  cases C <;> simp_all [CTy.NuOk, CTy.isRet, CTy.unroll, CTy.instT]

/-- **`own` keeps a `λ` a `λ`**: a computation other than an `F` whose erasure is a `λ` lowers
to a `λ`. -/
theorem own_lam {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg} (h : TDerivesP Δ Γ t j) :
    ∀ (L : List Bool) (C : CTy) (N : Expr), j = .comp C → C.isRet = false →
      t.erase = .lam N → ∃ N', ownAt L t = .lam N' := by
  induction h with
  | lam => intro L C N _ _ _; exact ⟨_, rfl⟩
  | withI => intro L C N _ _ _; exact ⟨_, rfl⟩
  | allI => intro L C N _ _ _; exact ⟨_, rfl⟩
  | ret => intro L C N hj hC _; cases hj; simp [CTy.isRet] at hC
  | nuIn hC₀ _ ih =>
      intro L C N hj _ he; cases hj; exact ih L _ N rfl (CTy.unroll_isRet hC₀) he
  | nuOut _ _ ih => intro L C N hj _ he; exact ih L _ N rfl rfl he
  | litFn _ _ _ ih | divLit _ _ _ ih | walk _ _ _ ih => intro L C N hj hC he; exact ih L C N hj hC he
  | walkGet _ _ ih | selfCall _ _ ih | lendCell _ _ ih | nuEta _ _ ih | use _ _ ih =>
      intro L C N hj hC he; exact ih L C N hj hC he
  | force =>
      intro L C N hj hC he
      cases hj
      simp only [TExpr.erase, forceE_of_not_ret hC] at he; cases he
  | _ =>
      intro L C N hj _ he
      first
        | (cases hj; done)
        | (simp [TExpr.erase, absurdE] at he; done)
        | exact ⟨N, (rfl : ownAt L _ = _).trans he⟩

/-! ### A node at a split -/

theorem lv_part_iff {L : List Bool} {u : Nat → Bool} {k : Nat} :
    lv (part L u) k = true ↔ lv L k = true ∧ u k = true := by
  refine ⟨lv_part, fun ⟨h₁, h₂⟩ => ?_⟩
  have hk := mem_liveIdx.mpr h₁
  simp only [liveIdx, List.mem_filter, List.mem_range] at hk
  simp only [lv, part, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk.1]
  simpa [lv, List.getD_eq_getElem?_getD] using And.intro h₁ h₂

/-- **A node at a split**: the drops and copies around it consume exactly the node's live slots. -/
theorem exact_splitE {L : List Bool} {u₁ u₂ : Nat → Bool} {F : Node}
    (hF : GoodNode F (fun k => lv (part L u₁) k = true) (fun k => lv (part L u₂) k = true)) :
    ExplicitC (splitE L u₁ u₂ F) ∧ effFreeB (splitE L u₁ u₂ F) = true ∧
      ExactP (fun k => lv L k = true) (splitE L u₁ u₂ F) := by
  obtain ⟨hx, he, hex⟩ := exact_copies ((liveIdx L).filter fun k => u₁ k && u₂ k) 0 F _ _ hF
    (by simpa using (liveIdx_nodup L).filter _)
    (fun k hk => by
      simp only [List.mem_filter, mem_liveIdx, Bool.and_eq_true] at hk
      exact ⟨lv_part_iff.mpr ⟨hk.1, hk.2.1⟩, lv_part_iff.mpr ⟨hk.1, hk.2.2⟩⟩)
    (fun i h₁ h₂ => by
      rw [lv_part_iff] at h₁ h₂
      simp [mem_liveIdx, h₁.1, h₁.2, h₂.2])
  refine ⟨explicitC_dropsE hx _, effFreeB_dropsE he _, ?_⟩
  refine (exact_dropsE ((liveIdx_nodup L).filter _) (fun k hk => ?_) hex).congr fun k => ?_
  · simp only [List.mem_filter, mem_liveIdx, Bool.and_eq_true, Bool.not_eq_true'] at hk
    rintro (h | h) <;> rw [lv_part_iff] at h
    · rw [h.2] at hk; exact absurd hk.2.1 (by simp)
    · rw [h.2] at hk; exact absurd hk.2.2 (by simp)
  · simp only [List.mem_filter, mem_liveIdx, Bool.and_eq_true, lv_part_iff]
    constructor
    · rintro (h | h | h)
      · exact h.1
      · exact h.1
      · exact h.1
    · intro h
      cases h₁ : u₁ k <;> cases h₂ : u₂ k <;> simp_all

/-! ### The nodes' templates -/

/-- What `own` gives a part: explicit, free of effect primitives, consuming its live slots. -/
def Lowered (P : Nat → Prop) (e : Expr) : Prop := ExplicitC e ∧ effFreeB e = true ∧ ExactP P e

theorem img_liftR {P : Nat → Prop} {ρ : Nat → Nat} {k : Nat} :
    (∃ i, P i ∧ liftR ρ i = k + 1) ↔ ∃ i, P (i + 1) ∧ ρ i = k := by
  constructor
  · rintro ⟨i, hi, h⟩
    cases i with
    | zero => simp [liftR] at h
    | succ i => exact ⟨i, hi, by simpa [liftR] using h⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i + 1, hi, rfl⟩

theorem img_liftR0 {P : Nat → Prop} {ρ : Nat → Nat} : (∃ i, P i ∧ liftR ρ i = 0) ↔ P 0 := by
  constructor
  · rintro ⟨i, hi, h⟩
    cases i with
    | zero => exact hi
    | succ i => simp [liftR] at h
  · intro h; exact ⟨0, h, rfl⟩

/-- A part under one binder its body consumes, renamed: a `λ` consuming the part's image. -/
theorem lowered_lam_ren {P : Nat → Prop} {e : Expr} (he : Lowered P e) (h0 : P 0) {ρ : Nat → Nat}
    (hρ : Function.Injective ρ) :
    Lowered (fun k => ∃ i, P (i + 1) ∧ ρ i = k) (.lam (ren (liftR ρ) e)) := by
  obtain ⟨hx, hf, hex⟩ := he
  have hl := liftR_injective hρ
  have hr := exact_ren hl hex
  refine ⟨explicitC_lam (hx.ren hl) hr ⟨0, h0, rfl⟩, by simpa [effFreeB, effFreeB_ren] using hf, ?_⟩
  exact (exact_lam hr).congr fun k => img_liftR

theorem lowered_ren {P : Nat → Prop} {e : Expr} (he : Lowered P e) {ρ : Nat → Nat}
    (hρ : Function.Injective ρ) : Lowered (fun k => ∃ i, P i ∧ ρ i = k) (ren ρ e) :=
  ⟨he.1.ren hρ, by rw [effFreeB_ren]; exact he.2.1, exact_ren hρ he.2.2⟩

theorem disj_of {P₁ P₂ : Nat → Prop} {ρ₁ ρ₂ : Nat → Nat} (hd : ∀ i j, P₁ i → P₂ j → ρ₁ i ≠ ρ₂ j)
    (k : Nat) : ¬ ((∃ i, P₁ i ∧ ρ₁ i = k) ∧ (∃ i, P₂ i ∧ ρ₂ i = k)) :=
  fun ⟨⟨i, hi, h₁⟩, ⟨j, hj, h₂⟩⟩ => hd i j hi hj (h₁.trans h₂.symm)

/-- `(e₁, e₂)`. -/
theorem good_pair {P₁ P₂ : Nat → Prop} {e₁ e₂ : Expr} (h₁ : Lowered P₁ e₁) (h₂ : Lowered P₂ e₂) :
    GoodNode (fun r₁ r₂ => .pair (ren r₁ e₁) (ren r₂ e₂)) P₁ P₂ := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  obtain ⟨x₂, f₂, e₂'⟩ := lowered_ren h₂ i₂
  exact ⟨.pair x₁ x₂, by simp [effFreeB, f₁, f₂],
    exact_seqO e₁' e₂' (disj_of hd) (fun _ => rfl) (fun _ => rfl)⟩

/-- `e₁; e₂`. -/
theorem good_seq {P₁ P₂ : Nat → Prop} {e₁ e₂ : Expr} (h₁ : Lowered P₁ e₁) (h₂ : Lowered P₂ e₂) :
    GoodNode (fun r₁ r₂ => .seq (ren r₁ e₁) (ren r₂ e₂)) P₁ P₂ := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  obtain ⟨x₂, f₂, e₂'⟩ := lowered_ren h₂ i₂
  exact ⟨.seq x₁ x₂, by simp [effFreeB, f₁, f₂],
    exact_seqO e₁' e₂' (disj_of hd) (fun _ => rfl) (fun _ => rfl)⟩

/-- `f a`, the argument the first part. -/
theorem good_app {P₁ P₂ : Nat → Prop} {a f : Expr} (h₁ : Lowered P₁ a) (h₂ : Lowered P₂ f) :
    GoodNode (fun r₁ r₂ => .app (ren r₂ f) (ren r₁ a)) P₁ P₂ := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  obtain ⟨x₂, f₂, e₂'⟩ := lowered_ren h₂ i₂
  exact ⟨.app x₂ x₁, by simp [effFreeB, f₁, f₂],
    exact_seqO e₁' e₂' (disj_of hd) (fun _ => rfl) (fun _ => by simp [mentions, Bool.or_comm])⟩

/-- `M x`, `M` the first part. -/
theorem good_appVar {P₁ : Nat → Prop} {M : Expr} {i : Nat} (h₁ : Lowered P₁ M) :
    GoodNode (fun r₁ r₂ => .app (ren r₁ M) (ren r₂ (.var i))) P₁ (· = i) := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  obtain ⟨x₂, f₂, e₂'⟩ := lowered_ren ⟨.var i, rfl, exact_var i⟩ i₂
  refine ⟨.app x₁ x₂, by simp [effFreeB, f₁, f₂], ?_⟩
  refine (exact_seqO e₂' e₁' (fun k h => disj_of hd k ⟨h.2, h.1⟩) (fun _ => rfl)
    (fun _ => by simp [mentions, Bool.or_comm])).congr fun k => or_comm

/-- `(λx. N) M`. -/
theorem good_bind {P₁ P₂ : Nat → Prop} {M N : Expr} (h₁ : Lowered P₁ M)
    (h₂ : Lowered (fun k => k = 0 ∨ (∃ i, k = i + 1 ∧ P₂ i)) N) :
    GoodNode (fun r₁ r₂ => .app (.lam (ren (liftR r₂) N)) (ren r₁ M)) P₁ P₂ := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  obtain ⟨x₂, f₂, e₂'⟩ := lowered_lam_ren h₂ (.inl rfl) i₂
  refine ⟨.app x₂ x₁, by simp only [effFreeB] at f₂ ⊢; simp [f₁, f₂], ?_⟩
  refine (exact_seqO e₁' (e₂'.congr fun k => ?_) (disj_of hd) (fun _ => rfl)
    (fun _ => by simp [mentions, Bool.or_comm]))
  simp

/-- `let (x, y) = V; M`. -/
theorem good_letpair {P₁ P₂ : Nat → Prop} {V M : Expr} (h₁ : Lowered P₁ V)
    (h₂ : Lowered (fun k => k = 0 ∨ k = 1 ∨ (∃ i, k = i + 2 ∧ P₂ i)) M) :
    GoodNode (fun r₁ r₂ => .letpair (ren r₁ V) (ren (liftR (liftR r₂)) M)) P₁ P₂ := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  have hl := liftR_injective (liftR_injective i₂)
  obtain ⟨x₂, f₂, e₂'⟩ := lowered_ren h₂ hl
  refine ⟨.letpair x₁ x₂ ((e₂' 0).1 ⟨0, .inl rfl, rfl⟩).1 ((e₂' 1).1 ⟨1, .inr (.inl rfl), rfl⟩).1,
    by simp [effFreeB, f₁, f₂], ?_⟩
  have hc : ∀ k, (∃ i, (i = 0 ∨ i = 1 ∨ ∃ i', i = i' + 2 ∧ P₂ i') ∧ liftR (liftR ρ₂) i = k + 2) ↔
      ∃ i, P₂ i ∧ ρ₂ i = k := fun k => by
    constructor
    · rintro ⟨i, hi, h⟩
      rcases i with _ | _ | i
      · simp [liftR] at h
      · simp [liftR] at h
      · simp only [liftR, Nat.add_right_cancel_iff] at h
        rcases hi with h' | h' | ⟨i', h', hp⟩
        · omega
        · omega
        · exact ⟨i, by rw [show i = i' by omega]; exact hp, h⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i + 2, .inr (.inr ⟨i, rfl, hi⟩), rfl⟩
  refine (exact_letpair e₁' e₂' fun k ⟨h, h'⟩ => disj_of hd k ⟨h, (hc k).mp h'⟩).congr fun k => ?_
  rw [hc]

/-- `case V {x. M₁ | y. M₂}`. -/
theorem good_case {P₁ P₂ : Nat → Prop} {V M₁ M₂ : Expr} (h₁ : Lowered P₁ V)
    (ha : Lowered (fun k => k = 0 ∨ (∃ i, k = i + 1 ∧ P₂ i)) M₁)
    (hb : Lowered (fun k => k = 0 ∨ (∃ i, k = i + 1 ∧ P₂ i)) M₂) :
    GoodNode (fun r₁ r₂ => .case (ren r₁ V) (ren (liftR r₂) M₁) (ren (liftR r₂) M₂)) P₁ P₂ := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  have hl := liftR_injective i₂
  obtain ⟨xa, fa, ea⟩ := lowered_ren ha hl
  obtain ⟨xb, fb, eb⟩ := lowered_ren hb hl
  refine ⟨.case x₁ xa xb ((ea 0).1 ⟨0, .inl rfl, rfl⟩).1 ((eb 0).1 ⟨0, .inl rfl, rfl⟩).1,
    by simp [effFreeB, f₁, fa, fb], ?_⟩
  have hc : ∀ k, (∃ i, (i = 0 ∨ ∃ i', i = i' + 1 ∧ P₂ i') ∧ liftR ρ₂ i = k + 1) ↔
      ∃ i, P₂ i ∧ ρ₂ i = k := fun k => by
    rw [img_liftR]; simp
  refine (exact_case e₁' ea eb ⟨0, .inl rfl, rfl⟩
    fun k ⟨h, h'⟩ => disj_of hd k ⟨h, (hc k).mp h'⟩).congr fun k => ?_
  rw [hc]

/-- `absurd V`. -/
theorem good_absurd {P₁ : Nat → Prop} {V : Expr} (h₁ : Lowered P₁ V) :
    GoodNode (fun r₁ _ => absurdL (ren r₁ V)) P₁ (fun _ => False) := by
  intro ρ₁ ρ₂ i₁ _ _
  obtain ⟨x₁, f₁, e₁'⟩ := lowered_ren h₁ i₁
  exact ⟨.absurd x₁, by simp [absurdL, effFreeB, f₁, BoLo.stuckE], (exact_absurdL e₁').congr (by simp)⟩

theorem GoodNode.congr {F : Node} {P₁ P₂ Q₁ Q₂ : Nat → Prop} (h : GoodNode F P₁ P₂)
    (h₁ : ∀ k, Q₁ k ↔ P₁ k) (h₂ : ∀ k, Q₂ k ↔ P₂ k) : GoodNode F Q₁ Q₂ := by
  intro ρ₁ ρ₂ i₁ i₂ hd
  obtain ⟨x, f, e⟩ := h ρ₁ ρ₂ i₁ i₂ fun i j hi hj => hd i j ((h₁ i).mpr hi) ((h₂ j).mpr hj)
  exact ⟨x, f, e.congr fun k => by simp only [h₁, h₂]⟩

/-! ### The other nodes -/

theorem lowered_congr {P Q : Nat → Prop} {e : Expr} (h : Lowered P e) (hPQ : ∀ k, P k ↔ Q k) :
    Lowered Q e := ⟨h.1, h.2.1, h.2.2.congr hPQ⟩

theorem lv_cons_succ (b : Bool) (L : List Bool) (k : Nat) : lv (b :: L) (k + 1) = lv L k := by
  simp [lv]

theorem lv_cons_zero (b : Bool) (L : List Bool) : lv (b :: L) 0 = b := by simp [lv]

theorem lv_true_iff (L : List Bool) (k : Nat) :
    lv (true :: L) k = true ↔ k = 0 ∨ ∃ i, k = i + 1 ∧ lv L i = true := by
  cases k <;> simp [lv]

theorem lv_true2_iff (L : List Bool) (k : Nat) :
    lv (true :: true :: L) k = true ↔ k = 0 ∨ k = 1 ∨ ∃ i, k = i + 2 ∧ lv L i = true := by
  rcases k with _ | _ | k <;> simp [lv]

theorem lowered_inj₁ {P : Nat → Prop} {e : Expr} (h : Lowered P e) : Lowered P (.inj₁ e) :=
  ⟨.inj₁ h.1, h.2.1, fun k => by rw [occ_inj₁]; exact h.2.2 k⟩

theorem lowered_inj₂ {P : Nat → Prop} {e : Expr} (h : Lowered P e) : Lowered P (.inj₂ e) :=
  ⟨.inj₂ h.1, h.2.1, fun k => by rw [occ_inj₂]; exact h.2.2 k⟩

/-- `M v` at a closed value `v`. -/
theorem lowered_appClosed {P : Nat → Prop} {M a : Expr} (h : Lowered P M) (ha : ExplicitC a)
    (hc : closedAt 0 a = true) (hf : effFreeB a = true) : Lowered P (.app M a) :=
  ⟨.app h.1 ha, by simp [effFreeB, h.2.1, hf],
    (exact_seqO (exact_closed hc) h.2.2 (fun _ h => h.1) (fun _ => rfl)
      (fun _ => by simp [mentions, Bool.or_comm])).congr (by simp)⟩

/-- `λx. M`, its binder live. -/
theorem lowered_lam {L : List Bool} {M : Expr} (h : Lowered (fun k => lv (true :: L) k = true) M) :
    Lowered (fun k => lv L k = true) (.lam M) :=
  ⟨explicitC_lam h.1 h.2.2 (by simp [lv]), h.2.1, (exact_lam h.2.2).congr fun k => by
    rw [lv_cons_succ]⟩

/-- `λu. (u; M)`, the binder dead in `M` and consumed by `(); …`. -/
theorem lowered_lamSeq {L : List Bool} {M : Expr}
    (h : Lowered (fun k => lv (false :: L) k = true) M) :
    Lowered (fun k => lv L k = true) (.lam (.seq (.var 0) M)) := by
  have hs := exact_seq_var0 h.2.2 (by simp [lv])
  refine ⟨explicitC_lam (.seq (.var 0) h.1) hs (.inl rfl), by simp [effFreeB, h.2.1],
    (exact_lam hs).congr fun k => ?_⟩
  simp [lv_cons_succ]

/-- `⟨M, N⟩`, each component at the two dead binders. -/
theorem lowered_withPair {L : List Bool} {M N : Expr}
    (hM : Lowered (fun k => lv (false :: false :: L) k = true) M)
    (hN : Lowered (fun k => lv (false :: false :: L) k = true) N) :
    Lowered (fun k => lv L k = true) (withPair M N) := by
  have h0 : ¬ lv (false :: false :: L) 0 = true := by simp [lv]
  have hsM := exact_seq_var0 hM.2.2 h0
  have hsN := exact_seq_var0 hN.2.2 h0
  have hc := exact_case (exact_var 0) hsM hsN (.inl rfl) fun k ⟨hk, h⟩ => by
    subst hk; rcases h with h | h
    · exact absurd h (by decide)
    · simp [lv] at h
  have hx : ExplicitC (.case (.var 0) (.seq (.var 0) M) (.seq (.var 0) N)) :=
    .case (.var 0) (.seq (.var 0) hM.1) (.seq (.var 0) hN.1) ((hsM 0).1 (.inl rfl)).1
      ((hsN 0).1 (.inl rfl)).1
  refine ⟨explicitC_lam hx hc (.inl rfl), by simp [withPair, effFreeB, hM.2.1, hN.2.1],
    (exact_lam hc).congr fun k => ?_⟩
  simp [lv]

theorem lowered_forceE {L : List Bool} {C : CTy} {i : Nat} (hi : lv L i = true) :
    Lowered (fun k => lv L k = true) (leafE L (some i) (forceE C (.var i))) := by
  have hf : ExplicitC (forceE C (.var i)) ∧ effFreeB (forceE C (.var i)) = true ∧
      ExactP (· = i) (forceE C (.var i)) := by
    cases C
    all_goals first
      | exact ⟨.var i, rfl, exact_var i⟩
      | exact ⟨.app (.var i) .unit, rfl, (exact_seqO (exact_closed (e := .unit) rfl) (exact_var i)
          (fun _ h => h.1) (fun _ => rfl) (fun _ => by simp [mentions, forceE])).congr
          (by simp)⟩
  exact ⟨explicitC_dropsE hf.1 _, effFreeB_dropsE hf.2.1 _,
    exact_leafE hf.2.2 (fun k => by simp [eq_comm]) (fun k hk => by cases hk; exact hi)⟩

theorem lowered_leaf_closed {L : List Bool} {e : Expr} (hx : ExplicitC e) (hf : effFreeB e = true)
    (hc : closedAt 0 e = true) : Lowered (fun k => lv L k = true) (leafE L none e) :=
  ⟨explicitC_dropsE hx _, effFreeB_dropsE hf _,
    exact_leafE (exact_closed hc) (fun k => by simp) (fun k hk => by cases hk)⟩

/-- A constant: its erasure, its context's live slots dropped. -/
theorem lowered_const {L : List Bool} {t : TExpr}
    (he : ownAt L t = if constNode t then leafE L none t.erase else t.erase)
    (hp : pureT t = (constNode t && effFreeB t.erase)) (hpt : pureT t = true)
    (hcl : constNode t = true → closedAt 0 t.erase = true) :
    Lowered (fun k => lv L k = true) (ownAt L t) := by
  rw [hp, Bool.and_eq_true] at hpt
  rw [he, if_pos hpt.1]
  exact lowered_leaf_closed (.const (LowConst.node t hpt.1) (hcl hpt.1)) hpt.2 (hcl hpt.1)

/-- **A constant of the kernel is closed**: the destructors and a block's borrow by their typed
rules' premises. -/
theorem constNode_closed (t : TExpr) (hc : constNode t = true)
    (hd : ∀ i j A, t = .dtor i j A → closedAt 0 (dtorE A) = true)
    (hs : ∀ i j σ c T, (t = .withborSM i j σ c T ∨ t = .withborSI i j σ c T) →
      closedAt 0 (withborS σ) = true) : closedAt 0 t.erase = true := by
  cases t
  case foldImm => exact foldImmV_closed _
  case foldOwn => exact foldOwnV_closed _
  case foldReuse => exact foldReuseV_closed _
  case unfoldN => exact unfoldV_closed _
  case allocS => exact allocS_closed _
  case freeS => exact freeS_closed _
  case divFuel => exact divFuelV_closed
  case dtor => exact hd _ _ _ rfl
  case withborSM => exact hs _ _ _ _ _ (.inl rfl)
  case withborSI => exact hs _ _ _ _ _ (.inr rfl)
  all_goals first
    | (cases hc; done)
    | rfl

/-! ### The induction -/

/-- **`own` lowers the pure fragment into the low subset**, at every live-slot flow along which
the masks agree with the leaves. -/
theorem own_lowered {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg} (h : TDerivesP Δ Γ t j) :
    ∀ L, pureT t = true → agreeAt L t = true → Lowered (fun k => lv L k = true) (ownAt L t) := by
  induction h with
  | var _ =>
      intro L _ ha
      exact ⟨explicitC_dropsE (.var _) _, effFreeB_dropsE rfl _,
        exact_leafE (exact_var _) (fun k => by simp [eq_comm]) (fun k hk => by cases hk; exact ha)⟩
  | unitI _ => intro L _ _; exact lowered_leaf_closed .unit rfl rfl
  | topI => intro L _ _; exact lowered_leaf_closed .unit rfl rfl
  | force _ => intro L _ ha; exact lowered_forceE ha
  | tensorI hs hm _ h₁ h₂ ih₁ ih₂ =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact exact_splitE (good_pair (ih₁ _ hp.1 ha.1) (ih₂ _ hp.2 ha.2))
  | unitE hs hm _ hV hM ihV ihM =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact exact_splitE (good_seq (ihV _ hp.1 ha.1) (ihM _ hp.2 ha.2))
  | lolliE hs hm _ ha' hf ihA ihF =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact exact_splitE (good_app (ihA _ hp.1 ha.1) (ihF _ hp.2 ha.2))
  | bind hs hm _ hM hN ihM ihN =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact exact_splitE (good_bind (ihM _ hp.1 ha.1)
        (lowered_congr (ihN _ hp.2 ha.2) fun k => lv_true_iff _ k))
  | tensorE hs hm _ hV hM ihV ihM =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact exact_splitE (good_letpair (ihV _ hp.1 ha.1)
        (lowered_congr (ihM _ hp.2 ha.2) fun k => lv_true2_iff _ k))
  | sumE hs hm _ hV h₁ h₂ ihV ih₁ ih₂ =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact exact_splitE (good_case (ihV _ hp.1.1 ha.1.1)
        (lowered_congr (ih₁ _ hp.1.2 ha.1.2) fun k => lv_true_iff _ k)
        (lowered_congr (ih₂ _ hp.2 ha.2) fun k => lv_true_iff _ k))
  | zeroE hs hm _ hV ih =>
      intro L hp ha
      simp only [pureT, agreeAt] at hp ha
      exact exact_splitE ((good_absurd (ih _ hp ha)).congr (fun _ => Iff.rfl)
        fun k => by simp [lv_part_iff])
  | app hs hm _ hM hx ih =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact exact_splitE ((good_appVar (i := _) (ih _ hp ha.1.1)).congr (fun _ => Iff.rfl)
        fun k => by
          rw [lv_part_iff]
          simp only [argMask, Bool.and_eq_true, beq_iff_eq]
          constructor
          · rintro ⟨-, h, -⟩; exact h
          · rintro rfl; exact ⟨ha.1.2, rfl, ha.2⟩)
  | sumI₁ _ ih => intro L hp ha; exact lowered_inj₁ (ih L hp ha)
  | sumI₂ _ ih => intro L hp ha; exact lowered_inj₂ (ih L hp ha)
  | thunkF _ ih => intro L hp ha; exact lowered_lamSeq (ih _ hp ha)
  | allI _ _ _ _ ih => intro L hp ha; exact lowered_lamSeq (ih _ hp ha)
  | bangThunkF _ _ ih => intro L hp ha; exact lowered_lamSeq (ih _ hp ha)
  | lam _ ih => intro L hp ha; exact lowered_lam (ih _ hp ha)
  | withI _ _ ihM ihN =>
      intro L hp ha
      simp only [pureT, agreeAt, Bool.and_eq_true] at hp ha
      exact lowered_withPair (ihM _ hp.1 ha.1) (ihN _ hp.2 ha.2)
  | thunkV hC h q ih =>
      intro L hp ha
      obtain ⟨N', hN⟩ := own_lam h L _ _ rfl hC q
      show Lowered _ (match ownAt L _ with | .lam N => .lam N | _ => _)
      have := ih L hp ha
      rw [hN] at this ⊢
      exact this
  | bangThunkV _ hC h q ih =>
      intro L hp ha
      obtain ⟨N', hN⟩ := own_lam h L _ _ rfl hC q
      show Lowered _ (match ownAt L _ with | .lam N => .lam N | _ => _)
      have := ih L hp ha
      rw [hN] at this ⊢
      exact this
  | proj₁ _ ih => intro L hp ha; exact lowered_appClosed (ih L hp ha) (.inj₁ .unit) rfl rfl
  | proj₂ _ ih => intro L hp ha; exact lowered_appClosed (ih L hp ha) (.inj₂ .unit) rfl rfl
  | allE _ _ ih => intro L hp ha; exact lowered_appClosed (ih L hp ha) .unit rfl rfl
  | allEV _ _ ih => intro L hp ha; exact lowered_appClosed (ih L hp ha) .unit rfl rfl
  | ret _ ih | bangE _ ih | boxE _ ih | ofRet _ ih | unroll _ ih => exact ih
  | boxI _ _ ih | immSub _ _ ih | mutSub _ _ ih | nuIn _ _ ih | nuOut _ _ ih => exact ih
  | roll _ _ _ ih => exact ih
  | litFn _ _ _ ih | divLit _ _ _ ih | walk _ _ _ ih => exact ih
  | walkGet _ _ ih | selfCall _ _ ih | lendCell _ _ ih | nuEta _ _ ih | use _ _ ih => exact ih
  | _ =>
      intro L hp _
      exact lowered_const rfl rfl hp fun hc => constNode_closed _ hc
        (fun _ _ _ h => by cases h <;> assumption)
        (fun _ _ _ _ _ h => by rcases h with h | h <;> cases h <;> assumption)

/-! ### The masks agree with the leaves -/

/-- A slot a term under a pushed binder mentions past it is live in `b :: L` where it is in `L`. -/
theorem lv_push {L : List Bool} {e : Expr}
    (h0 : ClauseKinds.mentions 0 e = true → False)
    (hs : ∀ k, ClauseKinds.mentions (k + 1) e = true → lv L k = true) :
    ∀ k, ClauseKinds.mentions k e = true → lv (false :: L) k = true
  | 0, hk => (h0 hk).elim
  | k + 1, hk => by rw [lv_cons_succ]; exact hs k hk

theorem lv_pushT {L : List Bool} {e : Expr}
    (hs : ∀ k, ClauseKinds.mentions (k + 1) e = true → lv L k = true) :
    ∀ k, ClauseKinds.mentions k e = true → lv (true :: L) k = true
  | 0, _ => rfl
  | k + 1, hk => by rw [lv_cons_succ]; exact hs k hk

theorem lv_pushT2 {L : List Bool} {e : Expr}
    (hs : ∀ k, ClauseKinds.mentions (k + 2) e = true → lv L k = true) :
    ∀ k, ClauseKinds.mentions k e = true → lv (true :: true :: L) k = true
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, hk => by rw [lv_cons_succ, lv_cons_succ]; exact hs k hk

/-- **The masks agree with the leaves** on every typed term of the pure fragment, along a flow of
live slots that holds every slot the term mentions: a split's masks cover its parts (`Covers`,
a premise of the typed split rules), and a binder typed dead is never mentioned
(`CDerivesP.mentions_live`).  `[spec §55]` -/
theorem agreeAt_of_typed {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg}
    (h : TDerivesP Δ Γ t j) : ∀ L, pureT t = true →
      (∀ k, ClauseKinds.mentions k t.erase = true → lv L k = true) → agreeAt L t = true := by
  induction h with
  | var _ =>
      intro L _ hL; exact hL _ (by simp [TExpr.erase, ClauseKinds.mentions])
  | @force _ _ i C _ =>
      intro L _ hL
      exact hL i (by cases C <;> simp [TExpr.erase, forceE, ClauseKinds.mentions])
  | tensorI _ _ hcv _ _ ih₁ ih₂ | unitE _ _ hcv _ _ ih₁ ih₂ =>
      intro L hp hL
      simp only [pureT, Bool.and_eq_true] at hp
      simp only [agreeAt, Bool.and_eq_true]
      exact ⟨ih₁ _ hp.1 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.1 k hk⟩,
        ih₂ _ hp.2 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.2 k hk⟩⟩
  | lolliE _ _ hcv _ _ ih₁ ih₂ =>
      intro L hp hL
      simp only [pureT, Bool.and_eq_true] at hp
      simp only [agreeAt, Bool.and_eq_true]
      exact ⟨ih₁ _ hp.1 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.1 k hk⟩,
        ih₂ _ hp.2 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.2 k hk⟩⟩
  | bind _ _ hcv _ _ ihM ihN =>
      intro L hp hL
      simp only [pureT, Bool.and_eq_true] at hp
      simp only [agreeAt, Bool.and_eq_true]
      refine ⟨ihM _ hp.1 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.1 k hk⟩,
        ihN _ hp.2 (lv_pushT fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, Expr.val, Val.lam, hk]), hcv.2 k hk⟩)⟩
  | tensorE _ _ hcv _ _ ihV ihM =>
      intro L hp hL
      simp only [pureT, Bool.and_eq_true] at hp
      simp only [agreeAt, Bool.and_eq_true]
      refine ⟨ihV _ hp.1 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.1 k hk⟩,
        ihM _ hp.2 (lv_pushT2 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.2 k hk⟩)⟩
  | sumE _ _ hcv _ _ _ ihV ih₁ ih₂ =>
      intro L hp hL
      simp only [pureT, Bool.and_eq_true] at hp
      simp only [agreeAt, Bool.and_eq_true]
      refine ⟨⟨ihV _ hp.1.1 fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.1 k hk⟩,
        ih₁ _ hp.1.2 (lv_pushT fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.2.1 k hk⟩)⟩,
        ih₂ _ hp.2 (lv_pushT fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.2.2 k hk⟩)⟩
  | zeroE _ _ hcv _ ih =>
      intro L hp hL
      simp only [pureT] at hp
      simp only [agreeAt]
      exact ih _ hp fun k hk => lv_part_iff.mpr
        ⟨hL k (by simp [TExpr.erase, absurdE, ClauseKinds.mentions, hk]), hcv k hk⟩
  | @app _ _ _ _ i _ _ _ _ _ _ _ hcv _ _ ih =>
      intro L hp hL
      simp only [pureT] at hp
      simp only [agreeAt, Bool.and_eq_true]
      refine ⟨⟨ih _ hp fun k hk => lv_part_iff.mpr
          ⟨hL k (by simp [TExpr.erase, ClauseKinds.mentions, hk]), hcv.1 k hk⟩,
        hL i (by simp [TExpr.erase, ClauseKinds.mentions])⟩,
        hcv.2 i (by simp [ClauseKinds.mentions])⟩
  | thunkF hT ih | allI _ _ _ hT ih | bangThunkF _ hT ih =>
      intro L hp hL
      simp only [pureT] at hp
      simp only [agreeAt]
      exact ih _ hp (lv_push
        (fun h0 => Ctx.not_liveAt_dead (hT.erase.mentions_live 0 h0))
        fun k hk => hL k (by simp [TExpr.erase, ClauseKinds.mentions, Expr.val, Val.lam, hk]))
  | lam _ ih =>
      intro L hp hL
      simp only [pureT] at hp
      simp only [agreeAt]
      exact ih _ hp (lv_pushT fun k hk =>
        hL k (by simp [TExpr.erase, ClauseKinds.mentions, Expr.val, Val.lam, hk]))
  | @withI _ Γ' _ _ _ _ _ hM hN ihM ihN =>
      intro L hp hL
      simp only [pureT, Bool.and_eq_true] at hp
      simp only [agreeAt, Bool.and_eq_true]
      have hw : ∀ (e : Expr), (∀ k, ClauseKinds.mentions k e = true → Ctx.LiveAt (withCtx Γ') k) →
          (∀ k, ClauseKinds.mentions (k + 2) e = true → lv L k = true) →
          ∀ k, ClauseKinds.mentions k e = true → lv (false :: false :: L) k = true := by
        intro e hl hs k hk
        match k, hk with
        | 0, hk => exact (Ctx.not_liveAt_dead (hl 0 hk)).elim
        | 1, hk => exact absurd (hl 1 hk) (by simp [Ctx.LiveAt, withCtx])
        | k + 2, hk => rw [lv_cons_succ, lv_cons_succ]; exact hs k hk
      exact ⟨ihM _ hp.1 (hw _ hM.erase.mentions_live fun k hk =>
          hL k (by simp [TExpr.erase, withPair, ClauseKinds.mentions, Expr.val, Val.lam, hk])),
        ihN _ hp.2 (hw _ hN.erase.mentions_live fun k hk =>
          hL k (by simp [TExpr.erase, withPair, ClauseKinds.mentions, Expr.val, Val.lam, hk]))⟩
  | thunkV _ _ _ ih | bangThunkV _ _ _ _ ih =>
      intro L hp hL
      simp only [pureT] at hp
      exact ih L hp hL
  | sumI₁ _ ih | sumI₂ _ ih | ret _ ih | bangE _ ih | boxI _ _ ih | boxE _ ih | immSub _ _ ih
  | mutSub _ _ ih | ofRet _ ih | roll _ _ _ ih | unroll _ ih | nuIn _ _ ih | nuOut _ _ ih
  | proj₁ _ ih | proj₂ _ ih | allE _ _ ih | allEV _ _ ih
  | litFn _ _ _ ih | divLit _ _ _ ih | walk _ _ _ ih | walkGet _ _ ih | selfCall _ _ ih
  | lendCell _ _ ih | nuEta _ _ ih | use _ _ ih =>
      intro L hp hL
      simp only [pureT] at hp
      simp only [agreeAt]
      exact ih L hp fun k hk => hL k (by
        simp [TExpr.erase, ClauseKinds.mentions, Expr.val, Val.inj₁, Val.inj₂, Val.unit, hk])
  | _ => intro L _ _; rfl

/-- The pure fragment has no relaxed rule. -/
theorem relaxedFree_of_pureT {Δ : LifeCtx} {Γ : Ctx VTy} {t : TExpr} {j : Jdg}
    (h : TDerivesP Δ Γ t j) : pureT t = true → relaxedFree t = true := by
  induction h <;> intro hp <;> first
    | rfl
    | cases hp
    | (simp only [pureT, relaxedFree, Bool.and_eq_true] at hp ⊢; simp_all)

/-- **`own` lands in the low subset** on the pure fragment: every closed `main` whose typed term
is in `pureT` lowers to a low term, with no effect primitive. Its masks agree with its leaves
(`agreeAt_of_typed`): the typed split rules make them cover their parts (`Covers`). -/
theorem own_lowersInto :
    LowersIntoOn (fun _ => noSite) (fun c => c.ctx = [] ∧ pureT c.t = true) own := by
  rintro c ⟨hΓ, hp⟩
  have hown : own c.t = ownAt [] c.t := by
    unfold own; rw [if_pos (relaxedFree_of_pureT c.typedP hp)]
  have ha : agreeAt [] c.t = true := agreeAt_of_typed c.typedP [] hp fun k hk => by
    have hl := c.typedP.erase.mentions_live k hk
    rw [hΓ] at hl
    exact absurd hl (Ctx.liveAt_nil k)
  rw [hown, hΓ]
  obtain ⟨hx, hf, hex⟩ := own_lowered c.typedP [] hp ha
  exact ⟨hx.explicit, effFreeB_sound hf, fun j hj => absurd hj (Nat.not_lt_zero _),
    fun j _ => (hex j).2 (by simp [lv])⟩

/-! ### Witnesses -/

/-- `λx. (x, x)` at `x : I32`: the split of a pair gives `x` to both components, and both masks
hold it. -/
def dupT : TExpr :=
  .lam default (.comp (.arr (.int .w32) (.ret (.tensor (.int .w32) (.int .w32))))) (.int .w32)
    (.ret (.tensor (.int .w32) (.int .w32)))
    (.ret default (.comp (.ret (.tensor (.int .w32) (.int .w32)))) (.tensor (.int .w32) (.int .w32))
      (.tensorI default (.val (.tensor (.int .w32) (.int .w32))) (.int .w32) (.int .w32)
        ⟨[(true, true)]⟩ (.var default (.val (.int .w32)) 0 (.int .w32))
        (.var default (.val (.int .w32)) 0 (.int .w32))))

/-- `return (λx. (x, x))`, a computation of `F (U(I32 ⊸ F(I32 ⊗ I32)))`. -/
def dupMain : TExpr :=
  .ret default (.comp (.ret (.thunk (.arr (.int .w32) (.ret (.tensor (.int .w32) (.int .w32)))))))
    (.thunk (.arr (.int .w32) (.ret (.tensor (.int .w32) (.int .w32)))))
    (.thunkV default (.val (.thunk (.arr (.int .w32) (.ret (.tensor (.int .w32) (.int .w32))))))
      (.arr (.int .w32) (.ret (.tensor (.int .w32) (.int .w32)))) dupT)

theorem dupSplit : Ctx.SplitP [⟨.int .w32, true⟩] [⟨.int .w32, true⟩] [⟨.int .w32, true⟩] :=
  .dup rfl .nil

theorem dupMasks : (Masks.mk [(true, true)]).Rel [⟨.int .w32, true⟩] [⟨.int .w32, true⟩] :=
  .cons (fun _ => rfl) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) .nil

theorem dupMain_typedAt (Ξ : EffCtx) :
    TDerivesAt Ξ LifeCtx.empty [] dupMain (.comp (.ret (.thunk (.arr (.int .w32)
      (.ret (.tensor (.int .w32) (.int .w32))))))) :=
  .ret (.thunkV rfl (.lam (.ret (.tensorI dupSplit dupMasks ⟨Covers.var rfl, Covers.var rfl⟩
    (.var (.here .nil)) (.var (.here .nil))))) rfl)

theorem dupMain_typedP :
    TDerivesP LifeCtx.empty [] dupMain (.comp (.ret (.thunk (.arr (.int .w32)
      (.ret (.tensor (.int .w32) (.int .w32))))))) :=
  .ret (.thunkV rfl (.lam (.ret (.tensorI dupSplit dupMasks ⟨Covers.var rfl, Covers.var rfl⟩
    (.var (.here .nil)) (.var (.here .nil))))) rfl)

/-- The checked `main` `return (λx. (x, x))`. -/
def dupChecked : Checked where
  ctx := []
  t := dupMain
  C := .ret (.thunk (.arr (.int .w32) (.ret (.tensor (.int .w32) (.int .w32)))))
  sigs := []
  ok := rfl
  pins := []
  tied := ⟨fun _ Ξ _ => dupMain_typedAt Ξ, dupMain_typedP⟩
  cells := []
  cellsOk := rfl

/-- `own` writes `dupChecked`'s copy: `λx. let (x₁, x₂) = copy x in (x₁, x₂)`. -/
theorem own_dupChecked :
    own dupChecked.t = .lam (.letpair (.app copy (.var 0)) (.pair (.var 1) (.var 0))) := by
  show own dupMain = _
  decide

/-- **Non-vacuity**: `dupChecked` meets `own_lowersInto`'s hypotheses, so `own`'s output is in
the relation (`own_lowerSem`) and low, its copy explicit. -/
theorem own_dupChecked_low : LowExpr noSite 0 (own dupChecked.t) :=
  own_lowersInto dupChecked ⟨rfl, by show pureT dupMain = true; decide⟩

/-- `λx. (x, ())` at `x : 1`, the split giving `x` to the pair's first component and both masks
empty. -/
def missT : TExpr :=
  .lam default (.comp (.arr .unit (.ret (.tensor .unit .unit)))) .unit (.ret (.tensor .unit .unit))
    (.ret default (.comp (.ret (.tensor .unit .unit))) (.tensor .unit .unit)
      (.tensorI default (.val (.tensor .unit .unit)) .unit .unit ⟨[(false, false)]⟩
        (.var default (.val .unit) 0 .unit) (.unitI default (.val .unit))))

/-- **Coverage is the premise that excludes `missT`**: its masks are related to its split's
contexts (`SplitMasks`, which asks only that a slot a mask holds be live), but the first mask does
not cover the variable the first component reads, so it is not a typed derivation. Its masks do not
agree with its leaves, and `own`'s output there reads `x` twice: dropped at the split, read by the
first component. -/
theorem coverage_excludes_missT :
    (Masks.mk [(false, false)]).Rel [⟨.unit, true⟩] [⟨.unit, false⟩] ∧
      ¬ TDerivesP LifeCtx.empty [] missT (.comp (.arr .unit (.ret (.tensor .unit .unit)))) ∧
      pureT missT = true ∧ agreeAt [] missT = false ∧
      own missT = .lam (.seq (.app forget (.var 0)) (.pair (.var 0) .unit)) ∧
      once (occ (.seq (.app forget (.var 0)) (.pair (.var 0) .unit)) 0) = false := by
  refine ⟨.cons (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ h => absurd h (by decide)) .nil, ?_, by decide, by decide, by decide, by decide⟩
  intro h
  cases h with
  | lam h =>
    cases h with
    | ret h =>
      cases h with
      | tensorI _ _ hcv _ _ =>
        exact absurd (hcv.1 0 (by simp [TExpr.erase, ClauseKinds.mentions])) (by decide)

end Lowering

