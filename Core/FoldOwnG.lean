import Core.FoldOwnGTerm
import Core.CountFold

/-!
# Core — the general owned fold as a typing rule  `[spec §6]`

`foldOwnG : Algs ⊸ !U(μX. T ⊸ F R₀)` for every body `T` in the class `P` (`FoldClass.lean`),
consuming the structure. `Algs` is the tuple of the algebras, one per key of `μX. T` (`keys`):
`!U(T_b⟨R⟩ ⊸ F R_b)` at a `μ` key with body `T_b`, `!U(1 ⊕ (R_a ⊗ S⟨R⟩) ⊸ F R_a)` at an array
key of element type `S`. The results `R_b` are any value types (`algsOf`).

**The proof.**
- `trav_spec` is induction on the position `A ∈ P`, one case per former, with an environment of
  handles: the call of a `μ` key `b` on a value `w` of its closed type is `s (tag b w)`, and
  `IHL s n K r` says every such call meets its spec at every measure below `(n, K, r)`,
  lexicographically: `n` bounds the value's cells (`dsize`), `K` its size, `r` the key's rank,
  the size of its body. The measure drops at every call: at a variable after `⊗`/`⊕`, the value
  is smaller, since a body's head is not a variable (`Hd`); after `Ref` or an array slot, the
  content has fewer cells (`dsize_tail_lt`); at an inner `μ`, at the same value, the inner body
  is smaller.
- `arr_spec`: the array action, a `count` loop whose invariant holds the accumulator, the
  emptied slots and the slots not yet visited.
- `selfG_run`: at the tag of the key `k`, the fixed point runs `k`'s branch.
- `hs_all` is strong induction on `n`, then `K`, then `r`.
- `foldOwnG_compatX`: the rule is sound, with the algebras taken out of the run-time tuple.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.FoldP
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub LifeCtx)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

-- Every reduction below normalises with one list of substitution facts; not every step uses each.
set_option linter.unusedSimpArgs false

/-! ### Reduction of the traversal -/

theorem travOf_app (e : Expr) (s w : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((e.subst 1 (s.shift 1 0)).subst 0 w) Q)
      (wpTS ls (.app (.app (.val (travOf e)) (.val s)) (.val w)) Q) := by
  intro ρ hw
  refine wpTS_beta_in (.appL .hole w) _ s ls Q ρ ?_
  exact wpTS_lolli ls _ w Q ρ hw

theorem tagE_subst : ∀ (k : Nat) (j : Nat) (s : Val) (e : Expr),
    (tagE k e).subst j s = tagE k (e.subst j s)
  | 0, _, _, _ => rfl
  | k + 1, j, s, e => by simp [tagE, tagE_subst k j s e]

theorem tagE_val : ∀ (k : Nat) (w : Val), tagE k (.val w) = (tagV k w).1
  | 0, _ => rfl
  | k + 1, w => by simp [tagE, tagV, tagE_val k w]

theorem tagE_inj₂_pair (k : Nat) (a b : Val) :
    tagE k (.inj₂ (.pair (.val a) (.val b))) = (tagV k (.inj₂ (.pair a b))).1 :=
  tagE_val k (.inj₂ (.pair a b))

theorem tagE_inj₁_unit (k : Nat) : tagE k (.inj₁ .unit) = (tagV k (.inj₁ .unit)).1 :=
  tagE_val k (.inj₁ .unit)

theorem callE_subst (ks : List Bnd) (k : Bnd) (s w : Val) :
    ((callE ks k).subst 1 (s.shift 1 0)).subst 0 w = .app (.val s) (.val (tagV (ks.idxOf k) w)) := by
  simp [callE, tagE_subst, subst_shift_succ, tagE_val]

theorem tensor_subst (t₁ t₂ s v₁ v₂ : Val) (h₁ : closedAt 0 t₁.1 = true)
    (h₂ : closedAt 0 t₂.1 = true) :
    (((Expr.letpair (.var 0)
        (bindE (.app (.app (.val t₁) (.var 3)) (.var 1))
          (bindE (.app (.app (.val t₂) (.var 4)) (.var 1))
            (.pair (.var 1) (.var 0))))).subst 1 (s.shift 1 0)).subst 0 (Val.pair v₁ v₂))
      = .letpair (.val (Val.pair v₁ v₂))
          (bindE (.app (.app (.val t₁) (.val (s.shift 2 0))) (.var 1))
            (bindE (.app (.app (.val t₂) (.val (s.shift 3 0))) (.var 1))
              (.pair (.var 1) (.var 0)))) := by
  simp [bindE, closed_subst h₁, closed_subst h₂, subst_shift_succ]

theorem tensor_body (t₁ t₂ s v₁ v₂ : Val) (h₁ : closedAt 0 t₁.1 = true)
    (h₂ : closedAt 0 t₂.1 = true) :
    ((bindE (.app (.app (.val t₁) (.val (s.shift 2 0))) (.var 1))
        (bindE (.app (.app (.val t₂) (.val (s.shift 3 0))) (.var 1))
          (.pair (.var 1) (.var 0)))).subst 0 (v₂.shift 1 0)).subst 0 v₁
      = (Kont.appR (.val (.lam (bindE (.app (.app (.val t₂) (.val (s.shift 1 0)))
          (.val (v₂.shift 1 0))) (.pair (.var 1) (.var 0))))) .hole).plug
          (.app (.app (.val t₁) (.val s)) (.val v₁)) := by
  simp [bindE, Kont.plug, closed_subst h₁, closed_subst h₂, subst_shift_succ]

theorem tensor_body₂ (t₂ s v₂ r₁ : Val) (h₂ : closedAt 0 t₂.1 = true) :
    (bindE (.app (.app (.val t₂) (.val (s.shift 1 0))) (.val (v₂.shift 1 0)))
        (.pair (.var 1) (.var 0))).subst 0 r₁
      = (Kont.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole).plug
          (.app (.app (.val t₂) (.val s)) (.val v₂)) := by
  simp [bindE, Kont.plug, closed_subst h₂, subst_shift_succ]

theorem sum_subst (t₁ t₂ s w : Val) (h₁ : closedAt 0 t₁.1 = true)
    (h₂ : closedAt 0 t₂.1 = true) :
    ((Expr.case (.var 0)
        (bindE (.app (.app (.val t₁) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
        (bindE (.app (.app (.val t₂) (.var 2)) (.var 0)) (.inj₂ (.var 0)))).subst 1 (s.shift 1 0)).subst 0 w
      = .case (.val w)
          (bindE (.app (.app (.val t₁) (.val (s.shift 1 0))) (.var 0)) (.inj₁ (.var 0)))
          (bindE (.app (.app (.val t₂) (.val (s.shift 1 0))) (.var 0)) (.inj₂ (.var 0))) := by
  simp [bindE, closed_subst h₁, closed_subst h₂, subst_shift_succ]

theorem sum_branch (t s v : Val) (ht : closedAt 0 t.1 = true)
    (inj : Expr → Expr) (hinj : ∀ j s e, Expr.subst j s (inj e) = inj (Expr.subst j s e)) :
    (bindE (.app (.app (.val t) (.val (s.shift 1 0))) (.var 0)) (inj (.var 0))).subst 0 v
      = (Kont.appR (.val (.lam (inj (.var 0)))) .hole).plug
          (.app (.app (.val t) (.val s)) (.val v)) := by
  simp [bindE, Kont.plug, closed_subst ht, subst_shift_succ, hinj]

theorem ref_subst (t s w : Val) (ht : closedAt 0 t.1 = true) :
    ((bindE (.app (.val (.prim .free)) (.var 0))
        (.app (.app (.val t) (.var 2)) (.var 0))).subst 1 (s.shift 1 0)).subst 0 w
      = (Kont.appR (.val (.lam (.app (.app (.val t) (.val (s.shift 1 0))) (.var 0)))) .hole).plug
          (.app (.val (.prim .free)) (.val w)) := by
  simp [bindE, Kont.plug, closed_subst ht, subst_shift_succ]

theorem ref_body (t s v : Val) (ht : closedAt 0 t.1 = true) :
    (Expr.app (.app (.val t) (.val (s.shift 1 0))) (.var 0)).subst 0 v
      = .app (.app (.val t) (.val s)) (.val v) := by
  simp [closed_subst ht, subst_shift_succ]

/-! ### The dispatch -/

section
variable (ks : List Bnd)

/-- A branch with the fixed point `sv` and the algebras substituted: `g` is the algebras as
seen where the payload is variable `0`. -/
def branchV (sv g : Val) (p : Nat) : Bnd → Expr
  | .arr _ _ => .app (.app (.val (projV ks.length p)) (.val g)) (.var 0)
  | k => bindE (.app (.app (.val (travB ks k))
        (.val (.lam (.app (.app (.val sv) (.val (g.shift 1 0))) (.var 0))))) (.var 0))
      (.app (.app (.val (projV ks.length p)) (.val (g.shift 1 0))) (.var 0))

/-- The dispatch with the fixed point and the algebras substituted: `g` is the algebras as seen
where the scrutinee is variable `0`. -/
def dspV (sv : Val) : Val → Nat → List Bnd → Expr
  | _, _, [] => .var 0
  | g, p, k :: r => .case (.var 0) (branchV ks sv (g.shift 1 0) p k) (dspV sv (g.shift 1 0) (p + 1) r)

theorem branch_subst {sv : Val} (hsv : closedAt 0 sv.1 = true) (gs : Val) (j p : Nat) :
    ∀ k : Bnd, ((branch ks j p k).subst (j + 3) sv).subst (j + 2) (gs.shift (j + 2) 0)
      = branchV ks sv (gs.shift (j + 2) 0) p k
  | .arr _ _ => by
      simp [branch, branchV, closed_subst (projV_closed _ _)]
  | .mu _ => by
      simp [branch, branchV, bindE, closed_subst (projV_closed _ _), closed_subst (travB_closed _ _),
        closed_shift hsv, closed_subst hsv]

theorem subst_var0_succ (j : Nat) (v : Val) : (Expr.var 0).subst (j + 1) v = .var 0 := by
  simp [Expr.subst]

theorem dsp_subst {sv : Val} (hsv : closedAt 0 sv.1 = true) (gs : Val) :
    ∀ (r : List Bnd) (j p : Nat), ((dsp ks j p r).subst (j + 2) sv).subst (j + 1) (gs.shift (j + 1) 0)
      = dspV ks sv (gs.shift (j + 1) 0) p r
  | [], j, _ => by
      simp only [dsp, dspV, subst_var0_succ]
  | k :: r, j, p => by
      have ih := dsp_subst hsv gs r (j + 1) (p + 1)
      have hb := branch_subst ks hsv gs j p k
      simp only [dsp, dspV, Expr.subst, val_shift_closed hsv, Val.shift_shift, subst_var0_succ]
      have e₃ : 1 + (j + 1) = j + 2 := by omega
      rw [e₃]
      simp only [show j + 2 + 1 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega,
        show j + 1 + 2 = j + 3 by omega] at ih ⊢
      rw [hb, ih]
      simp [Expr.subst]

theorem branchV_subst {sv : Val} (hsv : closedAt 0 sv.1 = true) (g v : Val) (p m : Nat)
    (hm : 1 ≤ m) : ∀ k : Bnd,
    (branchV ks sv (g.shift (m + 1) 0) p k).subst m v = branchV ks sv (g.shift m 0) p k
  | .arr _ _ => by
      simp [branchV, closed_subst (projV_closed _ _), subst_shift_succ]
      intro h; omega
  | .mu _ => by
      simp [branchV, bindE, closed_subst (projV_closed _ _), closed_subst (travB_closed _ _),
        closed_subst hsv, subst_shift_succ]
      refine ⟨?_, fun h => by omega⟩
      rw [show 1 + (m + 1) = (m + 1) + 1 by omega, subst_shift_succ _ _ (le_refl _),
        show 1 + m = m + 1 by omega]

theorem dspV_subst {sv : Val} (hsv : closedAt 0 sv.1 = true) (g : Val) :
    ∀ (r : List Bnd) (v : Val) (p m : Nat), 1 ≤ m →
      (dspV ks sv (g.shift (m + 1) 0) p r).subst m v = dspV ks sv (g.shift m 0) p r
  | [], _, _, m, hm => by
      simp only [dspV, Expr.subst]
      rw [if_neg (by omega), if_neg (by omega)]
  | k :: r, v, p, m, hm => by
      have ih := dspV_subst hsv g r (v.shift 1 0) (p + 1) (m + 1) (by omega)
      have hb := branchV_subst ks hsv g (v.shift 1 0) p (m + 1) (by omega) k
      simp only [dspV, Expr.subst, Val.shift_shift] at ih hb ⊢
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + (m + 1) = m + 1 + 1 := by omega
      have e' : 1 + m = m + 1 := by omega
      rw [e, e', hb, ih]

/-- At the tag of the `i`-th key, the dispatch runs that key's branch. -/
theorem dspV_run {sv : Val} (hsv : closedAt 0 sv.1 = true) (g w : Val) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    ∀ (r : List Bnd) (p i : Nat) (k : Bnd), r[i]? = some k →
      Entails (wpTS ls ((branchV ks sv (g.shift 1 0) (p + i) k).subst 0 w) Q)
        (wpTS ls ((dspV ks sv (g.shift 1 0) p r).subst 0 (tagV i w)) Q)
  | [], _, _, _, h => by simp at h
  | c :: r, p, 0, k, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      intro ρ hw
      have e : (dspV ks sv (g.shift 1 0) p (c :: r)).subst 0 (tagV 0 w)
          = .case (.val (.inj₁ w)) (branchV ks sv (g.shift 1 0) p c)
              (dspV ks sv (g.shift 1 0) (p + 1) r) := by
        have hb := branchV_subst ks hsv g ((tagV 0 w).shift 1 0) p 1 le_rfl c
        have hd := dspV_subst ks hsv g r ((tagV 0 w).shift 1 0) (p + 1) 1 le_rfl
        simp only [dspV, Expr.subst, if_pos, Val.shift_shift, tagV] at hb hd ⊢
        rw [hb, hd]
      rw [e]
      exact wpTS_sum₁ ls w _ _ Q ρ (by simpa using hw)
  | c :: r, p, i + 1, k, h => by
      simp only [List.getElem?_cons_succ] at h
      intro ρ hw
      have e : (dspV ks sv (g.shift 1 0) p (c :: r)).subst 0 (tagV (i + 1) w)
          = .case (.val (.inj₂ (tagV i w))) (branchV ks sv (g.shift 1 0) p c)
              (dspV ks sv (g.shift 1 0) (p + 1) r) := by
        have hb := branchV_subst ks hsv g ((tagV (i + 1) w).shift 1 0) p 1 le_rfl c
        have hd := dspV_subst ks hsv g r ((tagV (i + 1) w).shift 1 0) (p + 1) 1 le_rfl
        simp only [dspV, Expr.subst, if_pos, Val.shift_shift, tagV] at hb hd ⊢
        rw [hb, hd]
      rw [e]
      refine wpTS_sum₂ ls (tagV i w) _ _ Q ρ ?_
      exact dspV_run hsv g w ls Q r (p + 1) i k h ρ (by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hw)

/-- **The dispatch.**  At the tag of the `i`-th key `k`, the fixed point at the algebras `gs`
runs `k`'s branch. -/
theorem selfG_run (gs w : Val) (i : Nat) (k : Bnd) (hk : ks[i]? = some k) (ls : List SRec)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls ((branchV ks (selfG ks) (gs.shift 1 0) i k).subst 0 w) Q)
      (wpTS ls (.app (.app (.val (selfG ks)) (.val gs)) (.val (tagV i w))) Q) := by
  intro ρ hw
  refine wpTS_selfV_in (fBG_closed ks) (.appL .hole (tagV i w)) gs ls Q ρ ?_
  rw [fixV_eq (fBG_closed ks)]
  refine wpTS_beta_in (.appL .hole (tagV i w)) _ gs ls Q ρ ?_
  have e : ((fBG ks).subst 1 (selfG ks)).subst 0 gs
      = .val (.lam (dspV ks (selfG ks) (gs.shift 1 0) 0 ks)) := by
    have h := dsp_subst ks (selfG_closed ks) gs ks 0 0
    have hc : (selfG ks).shift 1 0 = selfG ks := val_shift_closed (selfG_closed ks) 1 0
    show (Expr.subst 0 gs (Expr.subst 1 (selfG ks) (Expr.lam (dsp ks 0 0 ks))))
      = Expr.lam (dspV ks (selfG ks) (gs.shift 1 0) 0 ks)
    simp only [Expr.subst, hc]
    simpa using h
  change wpTS ls ((Kont.appL .hole (tagV i w)).plug (((fBG ks).subst 1 (selfG ks)).subst 0 gs)) Q ρ
  rw [e]
  simp only [Kont.plug]
  refine wpTS_lolli ls _ (tagV i w) Q ρ ?_
  exact dspV_run ks (selfG_closed ks) gs w ls Q ks 0 i k hk ρ (by simpa using hw)

/-- The handle applied is the fixed point at the algebras. -/
theorem hG_app (gs x : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.app (.val (selfG ks)) (.val gs)) (.val x)) Q)
      (wpTS ls (.app (.val (hG ks gs)) (.val x)) Q) := by
  intro ρ hw
  refine wpTS_lolli ls _ x Q ρ ?_
  simpa [closed_subst (selfG_closed ks), subst_shift_succ] using hw

/-- A `μ` key's branch: the traversal of its body with the handle, then its algebra. -/
theorem branchV_mu (gs w : Val) (p : Nat) (b : Stack) :
    (branchV ks (selfG ks) (gs.shift 1 0) p (.mu b)).subst 0 w
      = (Kont.appR (.val (.lam (.app (.app (.val (projV ks.length p)) (.val (gs.shift 1 0)))
          (.var 0)))) .hole).plug (.app (.app (.val (travB ks (.mu b))) (.val (hG ks gs))) (.val w)) := by
  simp [branchV, bindE, Kont.plug, hG, closed_subst (projV_closed _ _),
    closed_subst (travB_closed _ _), closed_subst (selfG_closed ks), subst_shift_succ]

/-- An array key's branch: its algebra. -/
theorem branchV_arr (gs w : Val) (p : Nat) (Bs : Stack) (S : VTy) :
    (branchV ks (selfG ks) (gs.shift 1 0) p (.arr Bs S)).subst 0 w
      = .app (.app (.val (projV ks.length p)) (.val gs)) (.val w) := by
  simp [branchV, closed_subst (projV_closed _ _), subst_shift_succ]

end

/-! ### The algebras out of the tuple -/

/-- Substitution passes to the tuple projected: the rest of `projE` is closed under its
binders. -/
theorem projE_subst_gen : ∀ (n p j : Nat) (v : Val) (e : Expr),
    (projE n p e).subst j v = projE n p (e.subst j v)
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | _ + 2, 0, j, v, e => by
      simp only [projE, Expr.subst]
      rw [if_neg (by omega), if_neg (by omega)]
  | n + 2, p + 1, j, v, e => by
      simp only [projE, Expr.subst]
      congr 1
      exact subst_closedAt _ _ (projE_closed (n + 1) p (e := .var 0) (j := 1) rfl) (by omega)

theorem projE_subst (n p : Nat) (v : Val) : (projE n p (.var 0)).subst 0 v = projE n p (.val v) := by
  rw [projE_subst_gen]; simp

/-- The `p`-th component of a tuple, by pure steps. -/
theorem proj_red : ∀ (vs : List Val) (p : Nat) (a : Val), vs[p]? = some a →
    ∀ (ls : List SRec) (Q : List SRec → Val → WProp),
    Entails (Q ls a) (wpTS ls (projE vs.length p (.val (tupV vs))) Q)
  | [], _, _, h, _, _ => by simp at h
  | [b], p, a, h, ls, Q => by
      intro ρ hw
      have hp : p = 0 := by
        cases p with
        | zero => rfl
        | succ p => simp at h
      subst hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact wpTS_val ls b Q ρ hw
  | b :: c :: rest, 0, a, h, ls, Q => by
      intro ρ hw
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp only [List.length_cons, projE, tupV]
      refine wpTS_tensor ls b (tupV (c :: rest)) _ _ ρ ?_
      simp only [Expr.subst]
      simpa using wpTS_val ls b Q ρ hw
  | b :: c :: rest, p + 1, a, h, ls, Q => by
      intro ρ hw
      simp only [List.getElem?_cons_succ] at h
      have ih := proj_red (c :: rest) p a h ls Q ρ hw
      simp only [List.length_cons, projE, tupV]
      refine wpTS_tensor ls b (tupV (c :: rest)) _ _ ρ ?_
      rw [projE_subst, projE_subst_gen]
      simpa [subst_shift_succ] using ih

/-- **The `p`-th algebra of the tuple**, applied. -/
theorem proj_run (vs : List Val) (p : Nat) (a : Val) (h : vs[p]? = some a) (r : Val)
    (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.val a) (.val r)) Q)
      (wpTS ls (.app (.app (.val (projV vs.length p)) (.val (tupV vs))) (.val r)) Q) := by
  intro ρ hw
  refine wpTS_beta_in (.appL .hole r) _ _ ls Q ρ ?_
  rw [projE_subst]
  refine wpTS_bind (.appL .hole r) _ ls Q ρ ?_
  exact proj_red vs p a h ls _ ρ (by simpa [Kont.plug] using hw)

/-! ### The counted loop with an invariant -/

/-- **The loop with an invariant.**  From `I i` at `i ≤ len(n)`, `count` runs to `I (len n)`,
given that the step takes `I i` to `I (i + 1)` below the bound. -/
theorem countLoop_inv (f : Val) (n : UInt32) (I : Nat → List SRec → Val → WProp)
    (hstep : ∀ i : UInt32, i < arrLen n → ∀ ls s, Entails (I i.toNat ls s)
      (wpTS ls (.app (.val f) (.val (Val.pair (Val.i32 i) s))) (fun ls' => I (i.toNat + 1) ls'))) :
    ∀ (k : Nat) (i : UInt32) (ls : List SRec) (s : Val) (ρ : WRes),
      (arrLen n).toNat - i.toNat = k → i.toNat ≤ (arrLen n).toNat → I i.toNat ls s ρ →
      wpTS ls (.app (.val (.prim .count))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))))
        (fun ls' => I (arrLen n).toNat ls') ρ := by
  intro k
  induction k with
  | zero =>
      intro i ls s ρ hk hle hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      unfold countNext
      rw [if_neg hi]
      have e : i.toNat = (arrLen n).toNat := by omega
      rw [← e]
      exact wpTS_val ls s _ ρ hs
  | succ k ih =>
      intro i ls s ρ hk hle hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      unfold countNext
      rw [if_pos hi]
      refine wpTS_bind
        (.appR (.val (.prim .count)) (.pairR f (.pairR (Val.i32 n) (.pairR (Val.i32 (i + 1)) .hole))))
        (.app (.val f) (.val (Val.pair (Val.i32 i) s))) ls _ ρ ?_
      refine wpTS_mono (fun ls' v σ hv => ?_) ρ (hstep i hi ls s ρ hs)
      have hv' : I (i + 1).toNat ls' v σ := by rw [hi1]; exact hv
      exact ih (i + 1) ls' v σ (by omega) (by omega) hv'

/-! ### The owned traversal of an array -/

theorem arr_closed (ℓ : Loc) (N : UInt32) : closedAt 0 (Val.arr ℓ N).1 = true := rfl

/-- An algebra applied: `g r` runs to a value of `R`. -/
theorem alg_app {A R : VTy} {δ : LSub} {g r : Val} {ρ : WRes} {ls : List SRec}
    (hg : ∀ ls, vC true (.bang (.lolli A R)) ls δ g PMap.empty) (hr : vP A ls δ r ρ) :
    wpTS ls (.app (.val g) (.val r)) (fun ls' => vP R ls' δ) ρ := by
  obtain ⟨-, hthunk⟩ := hg ls
  exact hthunk ls (Ext.refl _ _) r ρ ρ hr (ResU.CompS.comm (ResU.comp_empty_right ρ))

section
variable {S' RS RA : VTy} {δ : LSub}

/-- The slots `ℓ, …, ℓ + k − 1` of an array of `Ref S'`. -/
abbrev slots (S' : VTy) (ls : List SRec) (δ : LSub) (ℓ : Loc) (k : Nat) : WProp :=
  sepRange (fun m => vP (.ref S') ls δ (.loc m)) ℓ k

/-- **The loop's invariant** before the `k`-th step: the accumulator, the slots already
emptied (each a cell holding `()`), and the slots not yet visited, below the bound. -/
def ArrInv (S' RA : VTy) (δ : LSub) (w s : Val) (ℓ : Loc) (N : Nat) (n : Nat) (k : Nat)
    (ls : List SRec) (st : Val) : WProp := fun ρ =>
  ∃ acc, st = Val.pair acc (Val.pair w s) ∧
    (vP RA ls δ acc ⋆ (sepRange todoP ℓ k ⋆
      fun ρ' => slots S' ls δ (ℓ + k) (N - k) ρ' ∧ dsize ρ' ≤ n)) ρ

theorem slots_same {S' : VTy} {ls ls' : List SRec} {δ : LSub} (hls : ∀ x, x ∈ ls' ↔ x ∈ ls)
    {ℓ : Loc} {k : Nat} {ρ : WRes} (h : slots S' ls δ ℓ k ρ) : slots S' ls' δ ℓ k ρ :=
  sepRange_mono' (fun _ _ h => vP_same hls h) h

/-- **One step of the loop.** -/
theorem step_spec (k : Nat) {t s : Val} (ht : closedAt 0 t.1 = true) {n : Nat} {ℓ : Loc}
    {N : UInt32} (hN : N.toNat < 2 ^ 31)
    (hS : ∀ v ρ ls, vP S' ls δ v ρ → dsize ρ < n →
      wpTS ls (.app (.app (.val t) (.val s)) (.val v)) (fun ls' => vP RS ls' δ) ρ)
    (hgA : ∀ ls x ρ, vP (.sum .unit (.tensor RA RS)) ls δ x ρ →
      wpTS ls (.app (.val s) (.val (tagV k x))) (fun ls' => vP RA ls' δ) ρ)
    (i : UInt32) (hi : i < arrLen N) (ls : List SRec) (st : Val) :
    Entails (ArrInv S' RA δ (Val.arr ℓ N) s ℓ N.toNat n i.toNat ls st)
      (wpTS ls (.app (.val (stepV k t)) (.val (Val.pair (Val.i32 i) st)))
        (fun ls' => ArrInv S' RA δ (Val.arr ℓ N) s ℓ N.toNat n (i.toNat + 1) ls')) := by
  rintro ρ ⟨acc, rfl, ρa, ρr, hc, hacc, ρd, ρs, hcr, htodo, hsl, hdr⟩
  rw [arrLen_of_bound hN] at hi
  have hiN : i.toNat < N.toNat := UInt32.lt_iff_toNat_lt.mp hi
  have esub : N.toNat - i.toNat = (N.toNat - (i.toNat + 1)) + 1 := by omega
  rw [esub] at hsl
  unfold slots at hsl
  rw [sepRange_succ] at hsl
  obtain ⟨ρsl, ρre, hcs, hslot, hrest⟩ := hsl
  obtain ⟨l', v, hsv⟩ := hslot
  obtain ⟨el, ρc, ρb, hcb, hown, hv⟩ := pure_sep_iff.mp hsv
  have hl' : l' = ℓ + i.toNat := (Val.loc_inj.mp el).symm
  subst hl'
  have hlt : dsize ρb < n := by
    have h₁ : dsize ρb < dsize ρsl := by
      rw [hown] at hcb
      exact dsize_tail_lt hcb ⟨PMap.empty, ResU.comp_empty_right _⟩
    have h₂ := dsize_le_left hcs
    omega
  have hre : dsize ρre ≤ n := le_trans (dsize_le_right hcs) hdr
  -- the pure steps to the `idx`
  refine wpTS_lolli ls _ _ _ ρ ?_
  simp only [stepE]
  refine wpTS_tensor ls (Val.i32 i) (Val.pair acc (Val.pair (Val.arr ℓ N) s)) _ _ ρ ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ]
  refine wpTS_tensor ls acc (Val.pair (Val.arr ℓ N) s) _ _ ρ ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ]
  refine wpTS_tensor ls (Val.arr ℓ N) s _ _ ρ ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- `idx`, then the `inj₁` branch
  refine wpTS_bind (.case .hole _ _)
    (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ N) (Val.i32 i)))) ls _ ρ ?_
  refine wpTS_idx ls ℓ N i _ ρ ?_
  rw [idxAns_lt ℓ hi]
  refine wpTS_val ls _ _ ρ ?_
  simp only [Kont.plug]
  refine wpTS_sum₁ ls (Val.loc (ℓ + i.toNat)) _ _ _ ρ ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, swap_subst, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- the resource: `ρ = ρc ● (ρa ● (ρd ● (ρb ● ρre)))`
  obtain ⟨bre, hbre, hcbre⟩ := compS_reassoc hcb hcs
  obtain ⟨X, hX, hcX⟩ := compS_lcomm hcbre hcr
  obtain ⟨Y, hY, hcY⟩ := compS_lcomm hcX hc
  -- take the slot's value out
  refine wpTS_bind (.appR (.val (.lam _)) .hole)
    (.app (.app swap (.val (.loc (ℓ + i.toNat)))) (.val .unit)) ls _ ρ ?_
  refine wpTS_swap ls _ v .unit _ ρ ⟨ρc, Y, hcY, hown, ?_⟩
  intro σa σ hσa hcσ
  simp only [Kont.plug]
  refine wpTS_lolli _ _ _ _ _ ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  refine wpTS_tensor ls (.loc (ℓ + i.toNat)) v _ _ σ ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  -- `σ = ρb ● (ρa ● ((ρd ● σa) ● ρre))`
  obtain ⟨Xσ, hXσ, hcXσ⟩ := compS_reassoc hY hcσ
  obtain ⟨dσ, hdσ, hcdσ⟩ := compS_exch hX hXσ
  obtain ⟨dre, hdre, hcdre⟩ := compS_lcomm hbre hcdσ
  obtain ⟨F, hF, hcF⟩ := compS_lcomm hcdre hcXσ
  have htodo' : sepRange todoP ℓ (i.toNat + 1) dσ :=
    sepRange_append hdσ htodo ⟨σa, PMap.empty, ResU.comp_empty_right σa, hσa, ⟨rfl, trivial⟩⟩
  -- the value's traversal, framing `acc ⋆ (emptied ⋆ rest)`
  refine wpTS_bind_frame (.appR (.val (.lam _)) .hole) (.app (.app (.val t) (.val s)) (.val v)) ls
    (fun ls' => vP RS ls' δ)
    (fun ls' => vP RA ls' δ acc ⋆ (sepRange todoP ℓ (i.toNat + 1) ⋆ fun ρ' =>
      slots S' ls' δ (ℓ + i.toNat + 1) (N.toNat - (i.toNat + 1)) ρ' ∧ dsize ρ' ≤ n)) _
    (fun ls' hls ρ' ⟨x₁, x₂, hx, h₁, x₃, x₄, hx', h₂, h₃, h₄⟩ =>
      ⟨x₁, x₂, hx, vP_same hls h₁, x₃, x₄, hx', h₂, slots_same hls h₃, h₄⟩)
    ?_ σ ⟨ρb, F, hcF, hS v ρb ls hv hlt, ρa, dre, hF, hacc, dσ, ρre, hdre, htodo', hrest, hre⟩
  rintro ls' hls r σ' ⟨σ₁, σ₂, hcσ', hr, τa, τre, hcτ, hacc', τd, τs, hcτs, htd, hrest', hre'⟩
  simp only [Kont.plug]
  refine wpTS_lolli ls' _ r _ σ' ?_
  simp [bindE, tagE_subst, closed_subst ht, closed_shift ht, subst_shift_succ,
    closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  rw [tagE_inj₂_pair]
  -- the algebra at `inj₂ (acc, r)`, framing the emptied slots and the rest
  obtain ⟨Z, hZ, hσZ⟩ := compS_reassoc' hcτ hcσ'
  refine wpTS_bind_frame (.appR (.val (.lam _)) .hole)
    (.app (.val s) (.val (tagV k (Val.inj₂ (Val.pair acc r))))) ls'
    (fun ls'' => vP RA ls'' δ)
    (fun ls'' => sepRange todoP ℓ (i.toNat + 1) ⋆ fun ρ' =>
      slots S' ls'' δ (ℓ + i.toNat + 1) (N.toNat - (i.toNat + 1)) ρ' ∧ dsize ρ' ≤ n) _
    (fun ls'' hls' ρ' ⟨x₃, x₄, hx', h₂, h₃, h₄⟩ => ⟨x₃, x₄, hx', h₂, slots_same hls' h₃, h₄⟩)
    ?_ σ' ⟨Z, τre, hσZ, hgA ls' _ Z (Or.inr ⟨Val.pair acc r, pure_sep_iff.mpr ⟨rfl,
      ⟨acc, r, pure_sep_iff.mpr ⟨rfl, τa, σ₁, ResU.CompS.comm hZ, hacc', hr⟩⟩⟩⟩), τd, τs, hcτs,
      htd, hrest', hre'⟩
  rintro ls'' hls'' acc' τ ⟨τ₁, τ₂, hcτ', hacc'', hrest''⟩
  simp only [Kont.plug]
  refine wpTS_lolli ls'' _ acc' _ τ ?_
  simp [subst_shift_succ, closed_shift (arr_closed ℓ N), closed_subst (arr_closed ℓ N)]
  refine wpTS_val ls'' (Val.pair acc' (Val.pair (Val.arr ℓ N) s)) _ τ ?_
  refine ⟨acc', rfl, τ₁, τ₂, hcτ', hacc'', ?_⟩
  rwa [show ℓ + (i.toNat + 1) = ℓ + i.toNat + 1 by lomega]

/-- `λ_. ()` consumes `1`. -/
theorem unitF_valid (ls : List SRec) (δ : LSub) :
    vP (.bang (.lolli .unit .unit)) ls δ unitF PMap.empty := by
  refine ⟨rfl, fun ls' _ v σ τ hv hcomp => ?_⟩
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨rfl, rfl⟩ := hv
  refine wpTS_lolli ls' _ _ _ _ ?_
  exact wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩

/-- An emptied slot is a leaf of `Array 1`. -/
theorem todo_done {ls : List SRec} {δ : LSub} {ℓ : Loc} {k : Nat} {ρ : WRes}
    (h : sepRange todoP ℓ k ρ) : sepRange (doneP .unit ls δ) ℓ k ρ :=
  sepRange_mono' (fun m ρ' hm => ⟨m, .unit, pure_sep_iff.mpr ⟨rfl, ρ', PMap.empty,
    ResU.comp_empty_right _, hm, rfl, rfl⟩⟩) h

/-- **The owned traversal of an array**, given the traversal of a slot's value at every
resource below the bound and the array key's algebra through the handle. -/
theorem arr_spec (k : Nat) {t s : Val} (ht : closedAt 0 t.1 = true) {n : Nat}
    (hS : ∀ v ρ ls, vP S' ls δ v ρ → dsize ρ < n →
      wpTS ls (.app (.app (.val t) (.val s)) (.val v)) (fun ls' => vP RS ls' δ) ρ)
    (hgA : ∀ ls x ρ, vP (.sum .unit (.tensor RA RS)) ls δ x ρ →
      wpTS ls (.app (.val s) (.val (tagV k x))) (fun ls' => vP RA ls' δ) ρ)
    (w : Val) (χ : WRes) (ls : List SRec) (hw : vP (.fam (.ref S')) ls δ w χ) (hn : dsize χ ≤ n) :
    wpTS ls (.app (.app (.val (travOf (arrE k (stepV k t)))) (.val s)) (.val w))
      (fun ls' => vP RA ls' δ) χ := by
  obtain ⟨ℓ, N, rfl, hN, hsl⟩ := vP_fam_iff.mp hw
  have hf := stepV_closed k ht
  refine travOf_app _ s _ ls _ χ ?_
  simp [arrE, bindE, tagE_subst, subst_shift_succ, closed_subst hf, closed_shift hf,
    closed_subst unitF_closed, closed_shift unitF_closed]
  refine wpTS_tensor ls (Val.loc ℓ) (Val.i32 N) _ _ χ ?_
  simp [bindE, tagE_subst, subst_shift_succ, closed_subst hf, closed_shift hf,
    closed_subst unitF_closed, closed_shift unitF_closed, Val.i32]
  rw [tagE_inj₁_unit]
  -- the seed, framing the slots
  refine wpTS_bind_frame (.appR (.val (.lam _)) .hole) (.app (.val s) (.val (tagV k (.inj₁ .unit))))
    ls (fun ls' => vP RA ls' δ)
    (fun ls' ρ' => slots S' ls' δ ℓ N.toNat ρ' ∧ dsize ρ' ≤ n) _
    (fun ls' hls ρ' ⟨h₂, h₃⟩ => ⟨slots_same hls h₂, h₃⟩)
    ?_ χ ⟨PMap.empty, χ, compS_empty_left χ,
      hgA ls _ _ (Or.inl ⟨Val.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩), hsl, hn⟩
  rintro ls' hls acc₀ σ ⟨σ₁, σ₂, hcσ, hacc₀, hsl₀, hn₀⟩
  simp only [Kont.plug]
  refine wpTS_lolli ls' _ acc₀ _ σ ?_
  simp [subst_shift_succ, closed_subst hf, closed_shift hf, closed_subst unitF_closed,
    closed_shift unitF_closed]
  -- the loop
  refine wpTS_bind (.appR (.val (.lam _)) .hole)
    (.app (.val (.prim .count)) (.val (Val.pair (stepV k t) (Val.pair (Val.i32 N)
      (Val.pair (Val.i32 0) (Val.pair acc₀ (Val.pair (Val.arr ℓ N) s))))))) ls' _ σ ?_
  have hloop := countLoop_inv (stepV k t) N
    (fun j ls st => ArrInv S' RA δ (Val.arr ℓ N) s ℓ N.toNat n j ls st)
    (fun i hi ls st => step_spec k ht hN hS hgA i hi ls st)
    _ 0 ls' (Val.pair acc₀ (Val.pair (Val.arr ℓ N) s)) σ rfl (Nat.zero_le _)
    ⟨acc₀, rfl, σ₁, σ₂, hcσ, hacc₀, PMap.empty, σ₂, compS_empty_left σ₂, ⟨rfl, trivial⟩,
      by simpa using hsl₀, hn₀⟩
  refine wpTS_mono (fun l₂ st ρ hst => ?_) σ hloop
  rw [arrLen_of_bound hN] at hst
  obtain ⟨acc, rfl, ρ₁, ρ₂, hc, hacc, ρd, ρs, hcr, htodo, hsl', -⟩ := hst
  rw [Nat.sub_self] at hsl'
  obtain ⟨rfl, -⟩ := hsl'
  rw [ResU.CompS.functional hcr (ResU.comp_empty_right ρd)] at hc
  simp only [Kont.plug]
  refine wpTS_lolli l₂ _ _ _ ρ ?_
  refine wpTS_tensor l₂ acc (Val.pair (Val.arr ℓ N) s) _ _ ρ ?_
  simp [subst_shift_succ, closed_subst unitF_closed, closed_shift unitF_closed]
  refine wpTS_tensor l₂ (Val.arr ℓ N) s _ _ ρ ?_
  simp [subst_shift_succ, closed_subst unitF_closed, closed_shift unitF_closed,
    closed_subst (arr_closed ℓ N), closed_shift (arr_closed ℓ N)]
  -- `drop` the emptied array, framing the accumulator
  refine wpTS_bind_frame (.appR (.val (.lam _)) .hole)
    (.app (.val (.prim .drop)) (.val (Val.pair unitF (Val.arr ℓ N)))) l₂
    (fun l₃ => vP .unit l₃ δ) (fun l₃ => vP RA l₃ δ acc) _
    (fun l₃ hls ρ' h => vP_same hls h) ?_ ρ
    ⟨ρd, ρ₁, ResU.CompS.comm hc, wpTS_dropStep l₂ unitF ℓ N _ ρd
      (dropFill_wp unitF ℓ (unitF_valid l₂ δ) N.toNat 0 l₂ ρd (fun _ => Iff.rfl)
        (by simpa using todo_done htodo)), hacc⟩
  rintro l₃ - u τ ⟨τ₁, τ₂, hcτ, ⟨rfl, rfl⟩, hacc'⟩
  simp only [Kont.plug]
  refine wpTS_lolli l₃ _ _ _ τ ?_
  simp [subst_shift_succ]
  rw [← eq_of_compS_empty_left hcτ] at hacc'
  exact wpTS_val l₃ acc _ _ hacc'

end

/-! ### The traversal's spec, by induction on `P` -/

section
variable (ks : List Bnd) (G : Algs) (δ : LSub)

/-- **The call of the `μ` key `B :: Bs`** on a value of its closed type with at most `n` cells
and size at most `K`. -/
def HS (s : Val) (B : VTy) (Bs : Stack) (n K : Nat) : Prop :=
  ∀ w χ ls, sizeOf w.1 ≤ K → vP (closedOf B Bs) ls δ w χ → dsize χ ≤ n →
    wpTS ls (.app (.val s) (.val (tagV (ks.idxOf (.mu (B :: Bs))) w)))
      (fun ls' => vP (G.Res (B :: Bs)) ls' δ) χ

/-- The lexicographic order on `(n, K, r)`. -/
def Lt3 (n' K' r' n K r : Nat) : Prop := n' < n ∨ (n' = n ∧ (K' < K ∨ (K' = K ∧ r' < r)))

/-- **The environment of handles**: every listed `μ` key's call meets its spec below
`(n, K, r)`. -/
def IHL (s : Val) (n K r : Nat) : Prop :=
  ∀ B Bs, .mu (B :: Bs) ∈ ks → Anc ks (B :: Bs) → ∀ n' K', Lt3 n' K' (sizeOf B) n K r →
    HS ks G δ s B Bs n' K'

/-- The algebra of every listed array key, through the handle: `1 ⊕ (R_a ⊗ S⟨R⟩) ⊸ R_a`. -/
def AH (s : Val) : Prop :=
  ∀ Bs S, .arr Bs S ∈ ks → ∀ ls x ρ,
    vP (.sum .unit (.tensor (G.ResA Bs S) (resO G Bs S))) ls δ x ρ →
    wpTS ls (.app (.val s) (.val (tagV (ks.idxOf (.arr Bs S)) x)))
      (fun ls' => vP (G.ResA Bs S) ls' δ) ρ

theorem IHL.down {s : Val} {n K r n' : Nat} (h : IHL ks G δ s n K r) (hn : n' < n) (K' r' : Nat) :
    IHL ks G δ s n' K' r' := fun B Bs hm ha n'' K'' hlt =>
  h B Bs hm ha n'' K'' (Or.inl (by rcases hlt with h | ⟨rfl, -⟩ <;> omega))

/-- A closed position: the value itself. -/
theorem leaf_spec (s : Val) (Bs : Stack) {A : VTy} (hA : clB 0 A = true) (w : Val) (χ : WRes)
    (ls : List SRec) (hv : vP (A.subst (env Bs)) ls δ w χ) :
    wpTS ls (.app (.app (.val (trav ks Bs A)) (.val s)) (.val w))
      (fun ls' => vP (resO G Bs A) ls' δ) χ := by
  refine travOf_app _ s w ls _ χ ?_
  rw [tE_leaf ks Bs hA]
  have e : ((Expr.var 0).subst 1 (s.shift 1 0)).subst 0 w = .val w := by simp [Expr.subst]
  rw [e, resO_leaf G Bs hA]
  rw [VTy.subst_closed0 ((clB_iff 0 A).mp hA)] at hv
  exact wpTS_val ls w _ χ hv

/-- **The generic owned traversal**, by induction on the position `A ∈ P`. -/
theorem trav_spec (s : Val) (hAH : AH ks G δ s) :
    ∀ (A : VTy) (Bs : Stack) (n K r : Nat), IHL ks G δ s n K r → P Bs.length A →
      sizeOf A ≤ r → Anc ks Bs → (∀ c ∈ keysIn Bs A, c ∈ ks) →
      ∀ w χ ls, sizeOf w.1 ≤ K → (Hd A ∨ sizeOf w.1 < K) →
        vP (A.subst (env Bs)) ls δ w χ → dsize χ ≤ n →
        wpTS ls (.app (.app (.val (trav ks Bs A)) (.val s)) (.val w))
          (fun ls' => vP (resO G Bs A) ls' δ) χ
  | .tvar i, Bs, n, K, r, hI, hP, _, hA, _, w, χ, ls, _, hhd, hv, hn => by
      have hi : i < Bs.length := hP
      have hlt : sizeOf w.1 < K := by
        rcases hhd with h | h
        · rcases h with h | h
          · exact absurd h (Nat.not_lt_zero _)
          · exact h.elim
        · exact h
      have e := List.drop_eq_getElem_cons hi
      set B' := Bs[i]
      set Bs' := Bs.drop (i + 1)
      have hm : Bnd.mu (B' :: Bs') ∈ ks := e ▸ hA i hi
      have ha : Anc ks (B' :: Bs') := e ▸ anc_drop hA i
      have hH := hI B' Bs' hm ha n (sizeOf w.1) (Or.inr ⟨rfl, Or.inl hlt⟩)
      refine travOf_app _ s w ls _ χ ?_
      simp only [tE]
      rw [callE_subst ks _ s w, e]
      have hv' : vP (closedOf B' Bs') ls δ w χ := by
        rw [← env_drop Bs i B' Bs' e]; exact hv
      simp only [resO, e]
      exact hH w χ ls le_rfl hv' hn
  | .tensor A₁ A₂, Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, ls, hK, _, hv, hn => by
      by_cases hcl : clB 0 (.tensor A₁ A₂) = true
      · exact leaf_spec ks G δ s Bs hcl w χ ls hv
      obtain ⟨v₁, v₂, hs'⟩ := hv
      obtain ⟨hw, χ₁, χ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs'
      subst hw
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      have hr₁ : sizeOf A₁ ≤ r := by simp at hr; omega
      have hr₂ : sizeOf A₂ ≤ r := by simp at hr; omega
      have hk₁ : ∀ c ∈ keysIn Bs A₁, c ∈ ks := fun c h => hk c (by simp [keysIn, h])
      have hk₂ : ∀ c ∈ keysIn Bs A₂, c ∈ ks := fun c h => hk c (by simp [keysIn, h])
      have ht₁ := trav_closed ks Bs A₁
      have ht₂ := trav_closed ks Bs A₂
      refine travOf_app _ s _ ls _ χ ?_
      simp only [tE, if_neg hcl]
      rw [tensor_subst _ _ s v₁ v₂ ht₁ ht₂]
      refine wpTS_tensor ls v₁ v₂ _ _ χ ?_
      rw [tensor_body _ _ s v₁ v₂ ht₁ ht₂]
      simp only [resO, if_neg hcl]
      refine wpTS_bind_frame _ _ ls (fun ls' r => vP (resO G Bs A₁) ls' δ r)
        (fun ls' ρ => vP (A₂.subst (env Bs)) ls' δ v₂ ρ ∧ dsize ρ ≤ n)
        _ (fun ls' hls ρ hρ => ⟨vP_same hls hρ.1, hρ.2⟩) ?_ χ
        ⟨χ₁, χ₂, hc, trav_spec s hAH A₁ Bs n K r hI hP.1 hr₁ hA hk₁ v₁ χ₁ ls (le_of_lt hs₁)
          (Or.inr hs₁) h₁ (le_trans (dsize_le_left hc) hn), h₂, le_trans (dsize_le_right hc) hn⟩
      rintro ls' hls r₁ σ ⟨σ₁, σ₂, hcσ, hr₁', hv₂, hn₂⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₁ _ σ ?_
      rw [tensor_body₂ _ s v₂ r₁ ht₂]
      refine wpTS_bind_frame _ _ ls' (fun ls'' r => vP (resO G Bs A₂) ls'' δ r)
        (fun ls'' => vP (resO G Bs A₁) ls'' δ r₁)
        _ (fun ls'' hls' ρ hρ => vP_same hls' hρ) ?_ σ
        ⟨σ₂, σ₁, ResU.CompS.comm hcσ, trav_spec s hAH A₂ Bs n K r hI hP.2 hr₂ hA hk₂ v₂ σ₂ ls'
          (le_of_lt hs₂) (Or.inr hs₂) hv₂ hn₂, hr₁'⟩
      rintro ls'' - r₂ τ ⟨τ₁, τ₂, hcτ, hr₂', hr₁''⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₂ _ τ ?_
      rw [tensor_body₃]
      exact wpTS_val ls'' _ _ τ
        ⟨r₁, r₂, pure_sep_iff.mpr ⟨rfl, τ₂, τ₁, ResU.CompS.comm hcτ, hr₁'', hr₂'⟩⟩
  | .sum A₁ A₂, Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, ls, hK, _, hv, hn => by
      by_cases hcl : clB 0 (.sum A₁ A₂) = true
      · exact leaf_spec ks G δ s Bs hcl w χ ls hv
      have hr₁ : sizeOf A₁ ≤ r := by simp at hr; omega
      have hr₂ : sizeOf A₂ ≤ r := by simp at hr; omega
      have hk₁ : ∀ c ∈ keysIn Bs A₁, c ∈ ks := fun c h => hk c (by simp [keysIn, h])
      have hk₂ : ∀ c ∈ keysIn Bs A₂, c ∈ ks := fun c h => hk c (by simp [keysIn, h])
      have ht₁ := trav_closed ks Bs A₁
      have ht₂ := trav_closed ks Bs A₂
      refine travOf_app _ s _ ls _ χ ?_
      simp only [tE, if_neg hcl]
      rw [sum_subst _ _ s w ht₁ ht₂]
      simp only [resO, if_neg hcl]
      rcases hv with ⟨v, hs'⟩ | ⟨v, hs'⟩
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs'
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine wpTS_sum₁ ls v _ _ _ χ ?_
        rw [sum_branch _ s v ht₁ Expr.inj₁ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (trav_spec s hAH A₁ Bs n K r hI hP.1 hr₁ hA hk₁ v χ ls (le_of_lt hsz) (Or.inr hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₁ r) _ ρ (Or.inl ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs'
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine wpTS_sum₂ ls v _ _ _ χ ?_
        rw [sum_branch _ s v ht₂ Expr.inj₂ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (trav_spec s hAH A₂ Bs n K r hI hP.2 hr₂ hA hk₂ v χ ls (le_of_lt hsz) (Or.inr hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₂ r) _ ρ (Or.inr ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)
  | .ref S, Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, ls, _, _, hv, hn => by
      by_cases hcl : clB 0 (.ref S) = true
      · exact leaf_spec ks G δ s Bs hcl w χ ls hv
      have hcl' : ¬ clB 0 S = true := hcl
      have hrS : sizeOf S ≤ r := by simp at hr; omega
      have htS := trav_closed ks Bs S
      obtain ⟨ℓ, v', hs'⟩ := hv
      obtain ⟨rfl, ρa, ρb, hc, hown, hM⟩ := pure_sep_iff.mp hs'
      have hlt : dsize ρb < n := by
        rw [hown] at hc
        exact lt_of_lt_of_le (dsize_tail_lt hc ⟨PMap.empty, ResU.comp_empty_right _⟩) hn
      refine travOf_app _ s _ ls _ χ ?_
      simp only [tE, if_neg hcl']
      rw [ref_subst _ s _ htS]
      refine wpTS_bind _ _ ls _ χ ?_
      refine wpTS_free ls ℓ v' _ χ ⟨ρa, ρb, hc, hown, ?_⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ v' _ ρb ?_
      rw [ref_body _ s v' htS]
      simp only [resO, if_neg hcl']
      exact trav_spec s hAH S Bs (dsize ρb) (sizeOf v'.1 + 1) r (hI.down ks G δ hlt _ _) hP hrS hA
        hk v' ρb ls (Nat.le_succ _) (Or.inr (Nat.lt_succ_self _)) hM le_rfl
  | .fam (.ref S), Bs, n, K, r, hI, hP, hr, hA, hk, w, χ, ls, _, _, hv, hn => by
      by_cases hcl : clB 0 S = true
      · exact leaf_spec ks G δ s Bs (A := .fam (.ref S)) hcl w χ ls hv
      have hrS : sizeOf S ≤ r := by simp at hr; omega
      have hmA : Bnd.arr Bs S ∈ ks := hk _ (by simp [keysIn, hcl])
      have hk' : ∀ c ∈ keysIn Bs S, c ∈ ks := fun c h => hk c (by simp [keysIn, hcl, h])
      simp only [trav, tE, if_neg hcl, resO]
      exact arr_spec (ks.idxOf (.arr Bs S)) (trav_closed ks Bs S)
        (fun v ρ ls' hv' hlt => trav_spec s hAH S Bs (dsize ρ) (sizeOf v.1 + 1) r
          (hI.down ks G δ (lt_of_lt_of_le hlt le_rfl) _ _) hP hrS hA hk' v ρ ls' (Nat.le_succ _)
          (Or.inr (Nat.lt_succ_self _)) hv' le_rfl)
        (hAH Bs S hmA) w χ ls hv hn
  | .mu B, Bs, n, K, r, hI, _, hr, hA, hk, w, χ, ls, hK, _, hv, hn => by
      by_cases hcl : clB 0 (.mu B) = true
      · exact leaf_spec ks G δ s Bs hcl w χ ls hv
      have hm : Bnd.mu (B :: Bs) ∈ ks := hk _ (by simp [keysIn, hcl])
      have hrB : sizeOf B < r := by simp at hr; omega
      have hH := hI B Bs hm (anc_cons hm hA) n K (Or.inr ⟨rfl, Or.inr ⟨rfl, hrB⟩⟩)
      refine travOf_app _ s w ls _ χ ?_
      simp only [tE, if_neg hcl]
      rw [callE_subst ks _ s w]
      simp only [resO, if_neg hcl]
      exact hH w χ ls hK hv hn
  | .unit, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .zero, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .thunk _, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .imm _ _, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .mut _ _, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .box _ _, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .bang _, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .unk, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .int _, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .opq _, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam .unit, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.tensor _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam .zero, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.sum _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.thunk _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.imm _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.mut _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.box _ _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.bang _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam .unk, Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.tvar _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.mu _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.int _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.fam _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.opq _), Bs, _, _, _, _, hP, _, _, _, w, χ, ls, _, _, hv, _ =>
      leaf_spec ks G δ s Bs (by exact (clB_iff 0 _).mpr hP) w χ ls hv

/-- The algebra at the position `p` of the tuple `gs`, applied: `A ⊸ R`. -/
def ProjOK (gs : Val) (p : Nat) (A R : VTy) : Prop :=
  ∀ ls r ρ, vP A ls δ r ρ →
    wpTS ls (.app (.app (.val (projV ks.length p)) (.val gs)) (.val r)) (fun ls' => vP R ls' δ) ρ

/-- Every listed key's algebra is in the tuple, at the key's first position. -/
def AlgsOK (gs : Val) : Prop :=
  (∀ B Bs, .mu (B :: Bs) ∈ ks →
    ProjOK ks δ gs (ks.idxOf (.mu (B :: Bs))) (resO G (B :: Bs) B) (G.Res (B :: Bs))) ∧
  ∀ Bs S, .arr Bs S ∈ ks →
    ProjOK ks δ gs (ks.idxOf (.arr Bs S)) (.sum .unit (.tensor (G.ResA Bs S) (resO G Bs S)))
      (G.ResA Bs S)

/-- The array keys' algebras through the handle. -/
theorem ah_of_algs {gs : Val} (h : AlgsOK ks G δ gs) : AH ks G δ (hG ks gs) := by
  intro Bs S hm ls x ρ hx
  refine hG_app ks gs _ ls _ ρ ?_
  refine selfG_run ks gs x _ (.arr Bs S) (List.getElem?_idxOf hm) ls _ ρ ?_
  rw [branchV_arr]
  exact h.2 Bs S hm ls x ρ hx

/-- The call of the `μ` key `B :: Bs` at the fixed point itself, at the algebras `gs`. -/
def HSel (gs : Val) (B : VTy) (Bs : Stack) (n K : Nat) : Prop :=
  ∀ w χ ls, sizeOf w.1 ≤ K → vP (closedOf B Bs) ls δ w χ → dsize χ ≤ n →
    wpTS ls (.app (.app (.val (selfG ks)) (.val gs)) (.val (tagV (ks.idxOf (.mu (B :: Bs))) w)))
      (fun ls' => vP (G.Res (B :: Bs)) ls' δ) χ

theorem hs_of_sel {gs : Val} {B : VTy} {Bs : Stack} {n K : Nat} (h : HSel ks G δ gs B Bs n K) :
    HS ks G δ (hG ks gs) B Bs n K := fun w χ ls a b c => hG_app ks gs _ ls _ χ (h w χ ls a b c)

/-- One unrolling of the `μ` key `B :: Bs`: the dispatch, the traversal of the body, the
algebra. -/
theorem hs_step (hok : KeysOK ks) {gs : Val} (halg : AlgsOK ks G δ gs)
    {B : VTy} {Bs : Stack} {n K : Nat} (hm : .mu (B :: Bs) ∈ ks) (ha : Anc ks (B :: Bs))
    (hI : IHL ks G δ (hG ks gs) n K (sizeOf B)) : HSel ks G δ gs B Bs n K := by
  intro w χ ls hK hv hn
  obtain ⟨hP, hH, hk⟩ := hok.1 B Bs hm
  refine selfG_run ks gs w _ (.mu (B :: Bs)) (List.getElem?_idxOf hm) ls _ χ ?_
  rw [branchV_mu]
  refine wpTS_bind _ _ ls _ χ ?_
  have hv' : vP (B.subst (env (B :: Bs))) ls δ w χ := by
    rw [← inst_closedOf]; exact (vC_unfold hv).2.2
  refine wpTS_mono (fun ls' r ρ hr => ?_) χ
    (trav_spec ks G δ (hG ks gs) (ah_of_algs ks G δ halg) B (B :: Bs) n K (sizeOf B) hI hP le_rfl
      ha hk w χ ls hK (Or.inl hH) hv' hn)
  simp only [Kont.plug]
  refine wpTS_lolli _ _ r _ ρ ?_
  have e : (Expr.app (.app (.val (projV ks.length (ks.idxOf (.mu (B :: Bs))))) (.val (gs.shift 1 0)))
      (.var 0)).subst 0 r = .app (.app (.val (projV ks.length (ks.idxOf (.mu (B :: Bs))))) (.val gs))
        (.val r) := by
    simp [closed_subst (projV_closed _ _), subst_shift_succ]
  rw [e]
  exact halg.1 B Bs hm ls' r ρ hr

/-- **Every `μ` key's call meets its spec**, at every measure: strong induction on the cells,
then the value's size, then the key's rank. -/
theorem hs_all (hok : KeysOK ks) {gs : Val} (halg : AlgsOK ks G δ gs) :
    ∀ n K B Bs, .mu (B :: Bs) ∈ ks → Anc ks (B :: Bs) → HSel ks G δ gs B Bs n K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro K
    induction K using Nat.strong_induction_on with
    | _ K ihK =>
      suffices H : ∀ r B Bs, sizeOf B = r → .mu (B :: Bs) ∈ ks → Anc ks (B :: Bs) →
          HSel ks G δ gs B Bs n K from fun B Bs => H _ B Bs rfl
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ihr =>
        intro B Bs hr hm ha
        refine hs_step ks G δ hok halg hm ha ?_
        intro B' Bs' hm' ha' n' K' hlt
        refine hs_of_sel ks G δ ?_
        rcases hlt with h | ⟨rfl, h | ⟨rfl, h⟩⟩
        · exact ihn n' h K' B' Bs' hm' ha'
        · exact ihK K' h B' Bs' hm' ha'
        · exact ihr (sizeOf B') (hr ▸ h) B' Bs' rfl hm' ha'

end

/-- **The owned fold of `μB₀`**, for every body `B₀` in the class `P`: at the root's tag, the
fixed point takes a value of `μB₀` to a value of the root's result, given each key's algebra. -/
theorem fold_spec {B₀ : VTy} (hB : PBody B₀) (G : Algs) (δ : LSub) {gs : Val}
    (halg : AlgsOK (keys B₀) G δ gs) (w : Val) (χ : WRes) (ls : List SRec)
    (hv : vP (.mu B₀) ls δ w χ) :
    wpTS ls (.app (.app (.val (selfG (keys B₀))) (.val gs)) (.val (tagV 0 w)))
      (fun ls' => vP (G.Res [B₀]) ls' δ) χ := by
  have h := hs_all (keys B₀) G δ (keys_ok hB) halg (dsize χ) (sizeOf w.1) B₀ [] (root_mem B₀)
    (anc_root B₀)
  rw [← closedOf_root] at hv
  have h' := h w χ ls le_rfl hv le_rfl
  rwa [root_idx] at h'

/-! ### The rule -/

/-- The results of the keys, from a list in the order of the keys: a key's result is the entry
at its first position. -/
def algsOf (ks : List Bnd) (Rs : List VTy) : Algs :=
  ⟨fun b => Rs.getD (ks.idxOf (.mu b)) .unit, fun Bs S => Rs.getD (ks.idxOf (.arr Bs S)) .unit⟩

/-- The type of the tuple of `μB₀`'s algebras, at the results `Rs`. -/
def algsTy (B₀ : VTy) (Rs : List VTy) : VTy :=
  tupTy ((keys B₀).map (algTy (algsOf (keys B₀) Rs)))

/-- **`foldOwnG`'s type**: `Algs ⊸ !U(μB₀ ⊸ F R₀)`.  `[spec §6]` -/
def foldGTy (B₀ : VTy) (Rs : List VTy) : VTy :=
  .lolli (algsTy B₀ Rs) (.bang (.lolli (.mu B₀) ((algsOf (keys B₀) Rs).Res [B₀])))

/-- Every algebra's type holds the empty resource. -/
theorem algTy_empty (G : Algs) (k : Bnd) {ls : List SRec} {δ : LSub} {v : Val} {σ : WRes}
    (h : vP (algTy G k) ls δ v σ) : σ = PMap.empty := by
  match k, h with
  | .mu [], h => exact h.1
  | .mu (_ :: _), h => exact h.1
  | .arr _ _, h => exact h.1

/-- A tuple of values of types holding the empty resource: its components. -/
theorem tup_split {ls : List SRec} {δ : LSub} :
    ∀ (As : List VTy) (g : Val) (ρ : WRes),
      (∀ A ∈ As, ∀ v σ, vP A ls δ v σ → σ = PMap.empty) → vP (tupTy As) ls δ g ρ →
      ρ = PMap.empty ∧ ∃ vs, g = tupV vs ∧ vs.length = As.length ∧
        ∀ (p : Nat) (a : Val) (A : VTy), vs[p]? = some a → As[p]? = some A → vP A ls δ a PMap.empty
  | [], g, ρ, _, h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, [], rfl, rfl, fun p a A h => by simp at h⟩
  | [A], g, ρ, hA, h => by
      have hρ := hA A (by simp) g ρ h
      subst hρ
      refine ⟨rfl, [g], rfl, rfl, fun p a A' h₁ h₂ => ?_⟩
      cases p with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁ h₂
          subst h₁; subst h₂; exact h
      | succ p => simp at h₁
  | A :: B :: r, g, ρ, hA, h => by
      obtain ⟨a, g', hs⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs
      have e₁ := hA A (by simp) a ρ₁ h₁
      subst e₁
      obtain ⟨e₂, vs, rfl, hlen, hvs⟩ :=
        tup_split (B :: r) g' ρ₂ (fun A' hA' => hA A' (List.mem_cons_of_mem _ hA')) h₂
      subst e₂
      refine ⟨eq_empty_of_compS_empty hc, a :: vs, ?_, by simp [hlen],
        fun p a' A' h₁' h₂' => ?_⟩
      · cases vs with
        | nil => simp at hlen
        | cons c vs => rfl
      · cases p with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁' h₂'
            subst h₁'; subst h₂'; exact h₁
        | succ p => exact hvs p a' A' (by simpa using h₁') (by simpa using h₂')

/-- The algebras out of a tuple valid at the keys' algebra types. -/
theorem algsOK_of_tuple (ks : List Bnd) (G : Algs) (δ : LSub) (vs : List Val) {ls₀ : List SRec}
    (hlen : vs.length = ks.length)
    (hvs : ∀ (p : Nat) (a : Val) (A : VTy), vs[p]? = some a → (ks.map (algTy G))[p]? = some A →
      vP A ls₀ δ a PMap.empty) :
    AlgsOK ks G δ (tupV vs) := by
  have hget : ∀ k ∈ ks, ∃ a, vs[ks.idxOf k]? = some a ∧
      ∀ ls, vP (algTy G k) ls δ a PMap.empty := by
    intro k hk
    have hlt : ks.idxOf k < vs.length := hlen ▸ List.idxOf_lt_length_of_mem hk
    obtain ⟨a, ha⟩ : ∃ a, vs[ks.idxOf k]? = some a := ⟨_, List.getElem?_eq_getElem hlt⟩
    refine ⟨a, ha, fun ls => vC_local true _ (ext_empty ls₀ ls) (hvs _ a _ ha ?_)⟩
    simp [List.getElem?_idxOf hk]
  have hrun : ∀ k ∈ ks, ∀ A R, algTy G k = .bang (.lolli A R) →
      ProjOK ks δ (tupV vs) (ks.idxOf k) A R := by
    intro k hk A R hA ls r ρ hr
    obtain ⟨a, ha, hva⟩ := hget k hk
    rw [hA] at hva
    rw [← hlen]
    exact proj_run vs _ a ha r ls _ ρ (alg_app hva hr)
  exact ⟨fun B Bs hm => hrun _ hm _ _ rfl, fun Bs S hm => hrun _ hm _ _ rfl⟩

theorem foldOwnGV_subst (B₀ : VTy) (gs : Val) :
    Expr.subst 0 gs (.val (.lam (.app (.app (.val (selfG (keys B₀))) (.var 1)) (tagE 0 (.var 0)))))
      = .val (.lam (.app (.app (.val (selfG (keys B₀))) (.val (gs.shift 1 0))) (tagE 0 (.var 0)))) := by
  simp [tagE, closed_subst (selfG_closed _)]

/-- **The general owned fold is sound.**  `foldOwnG : Algs ⊸ !U(μB₀ ⊸ F R₀)` at every body `B₀`
of the class `P` and every list of results.  `[spec §6]` -/
theorem foldOwnG_compatX {Δ : LifeCtx} {Γ : Ctx VTy} (B₀ : VTy) (hB : PBody B₀) (Rs : List VTy)
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val (foldOwnGV B₀)) (foldGTy B₀ Rs) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed (foldOwnGV_closed B₀)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ gs ρ₁ τ₀ hv₁ hcomp
  obtain ⟨hρ₁, vs, rfl, hlen, hvs⟩ := tup_split _ gs ρ₁
    (fun A hA v σ hv => by
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hA
      exact algTy_empty _ k hv) hv₁
  subst hρ₁
  have halg := algsOK_of_tuple (keys B₀) (algsOf (keys B₀) Rs) δ vs (by simpa using hlen) hvs
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ _ _ _ ?_
  rw [foldOwnGV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ?_⟩
  intro ls₂ _ v ρ₂ τ hv hc
  rw [eq_of_compS_empty_left hc]
  refine wpTS_lolli _ _ v _ _ ?_
  have e : Expr.subst 0 v (.app (.app (.val (selfG (keys B₀))) (.val ((tupV vs).shift 1 0)))
      (tagE 0 (.var 0))) = .app (.app (.val (selfG (keys B₀))) (.val (tupV vs))) (.val (tagV 0 v)) := by
    simp [tagE, tagV, closed_subst (selfG_closed _), subst_shift_succ]
  rw [e]
  exact fold_spec hB _ δ halg v ρ₂ ls₂ hv

end BoCa.Fig16.LogRel.Core.FoldP

end
