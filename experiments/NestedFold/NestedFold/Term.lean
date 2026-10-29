import NestedFold.Class

/-!
# NestedFold — the generated owned traversal

One generator, an action per former (#595's design §4.3, own column). `tE ks G Bs A` is the
body of the traversal of a position `A` under the binders `Bs`, with `s` (variable `1`) the
recursive call and `w` (variable `0`) the value:

| former | action |
|---|---|
| closed leaf | `w` |
| `tvar i` | `s (tag (Bs.drop i) w)`: the handle of the variable's binder |
| `⊗`, `⊕` | componentwise |
| `Ref S` | `free w`, then the traversal of `S` |
| `[Ref S]` | a `count` loop over the slots: `idx`, `free` the slot, traverse `S`, step `g_a`; seed `g_a (inj₁ ())` |
| `μB` | `s (tag (B :: Bs) w)`: the handle of the inner binder |

The handle of binder `b` is `λw. s (tag b w)`: `s` is one Z combinator (`selfD`) whose body
dispatches on the tag, Bekič's simultaneous fixed point. The tag of `b` is its index in the
list `ks` of binders, as nested injections (`tagV`); the branch of `b` runs the traversal of
`b`'s body and then `b`'s algebra. An array keeps its state `(acc, (w, s))` in the loop, so the
step `stepV` is a closed value.

The algebras are closed values given with the type (`Algs`): `Res`/`alg` per `μ` binder and
`ResA`/`algA` per array binder, keyed by the binder and the element type. `resO` is the
traversal's result type: `A` with each binder's result at its positions.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.NestedFold
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)
open Classical

/-- The algebras, one per binder: results and closed algebra values. -/
structure Algs where
  /-- The result of a `μ` binder. -/
  Res : Stack → VTy
  /-- The algebra of a `μ` binder. -/
  alg : Stack → Val
  /-- The result of an array binder: its binder and its element type. -/
  ResA : Stack → VTy → VTy
  /-- The algebra of an array binder. -/
  algA : Stack → VTy → Val
  alg_closed : ∀ b, closedAt 0 (alg b).1 = true
  algA_closed : ∀ b S, closedAt 0 (algA b S).1 = true

/-- `λs. λw. e`. -/
def travOf (e : Expr) : Val := .lam (.val (.lam e))

/-- The tag of index `k`: `inj₂ᵏ (inj₁ e)`. -/
def tagE : Nat → Expr → Expr
  | 0, e => .inj₁ e
  | k + 1, e => .inj₂ (tagE k e)

def tagV : Nat → Val → Val
  | 0, w => .inj₁ w
  | k + 1, w => .inj₂ (tagV k w)

/-- One step of the array loop, at the state `(i, (acc, (w, s)))`: the `i`-th slot of `w` is
freed, its content traversed by `t` with the handle `s`, and `g (inj₂ (acc, r))` is the next
accumulator. -/
def stepE (t g : Val) : Expr :=
  .letpair (.var 0)
    (.letpair (.var 0)
      (.letpair (.var 0)
        (.case (.app (.val (.prim .idx)) (.pair (.var 1) (.var 5)))
          (bindE (.app (.val (.prim .free)) (.var 0))
            (bindE (.app (.app (.val t) (.var 2)) (.var 0))
              (bindE (.app (.val g) (.inj₂ (.pair (.var 6) (.var 0))))
                (.pair (.var 0) (.pair (.var 5) (.var 4))))))
          (.pair (.var 4) (.pair (.var 2) (.var 1))))))

def stepV (t g : Val) : Val := .lam (stepE t g)

/-- The array action (handle `1`, array `0`): seed `g (inj₁ ())`, then `count` from `0` to the
length with the state `(acc, (w, s))`, then the accumulator. -/
def arrE (g f : Val) : Expr :=
  .letpair (.var 0)
    (bindE (.app (.val g) (.inj₁ .unit))
      (bindE (.app (.val (.prim .count)) (.pair (.val f) (.pair (.var 1)
          (.pair (.val (Val.i32 0)) (.pair (.var 0) (.pair (.var 3) (.var 4)))))))
        (.letpair (.var 0) (.var 1))))

section
variable (ks : List Stack) (G : Algs)

/-- The call of the handle of binder `b` on the value. -/
def callE (b : Stack) : Expr := .app (.var 1) (tagE (ks.idxOf b) (.var 0))

/-- **The traversal's body**, by recursion on the position. -/
def tE (Bs : Stack) : VTy → Expr
  | .tvar i => callE ks (Bs.drop i)
  | .tensor A B => if clB 0 (.tensor A B) then .var 0 else
      .letpair (.var 0)
        (bindE (.app (.app (.val (travOf (tE Bs A))) (.var 3)) (.var 1))
          (bindE (.app (.app (.val (travOf (tE Bs B))) (.var 4)) (.var 1))
            (.pair (.var 1) (.var 0))))
  | .sum A B => if clB 0 (.sum A B) then .var 0 else
      .case (.var 0)
        (bindE (.app (.app (.val (travOf (tE Bs A))) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
        (bindE (.app (.app (.val (travOf (tE Bs B))) (.var 2)) (.var 0)) (.inj₂ (.var 0)))
  | .ref S => if clB 0 S then .var 0 else
      bindE (.app (.val (.prim .free)) (.var 0))
        (.app (.app (.val (travOf (tE Bs S))) (.var 2)) (.var 0))
  | .fam (.ref S) => if clB 0 S then .var 0 else
      arrE (G.algA Bs S) (stepV (travOf (tE Bs S)) (G.algA Bs S))
  | .mu B => if clB 0 (.mu B) then .var 0 else callE ks (B :: Bs)
  | _ => .var 0

/-- The traversal of a position, a closed value `λs. λw. …`. -/
abbrev trav (Bs : Stack) (A : VTy) : Val := travOf (tE ks G Bs A)

/-- The result type: `A` with each binder's result at its positions. -/
def resO (Bs : Stack) : VTy → VTy
  | .tvar i => G.Res (Bs.drop i)
  | .tensor A B => if clB 0 (.tensor A B) then .tensor A B else .tensor (resO Bs A) (resO Bs B)
  | .sum A B => if clB 0 (.sum A B) then .sum A B else .sum (resO Bs A) (resO Bs B)
  | .ref S => if clB 0 S then .ref S else resO Bs S
  | .fam (.ref S) => if clB 0 S then .fam (.ref S) else G.ResA Bs S
  | .mu B => if clB 0 (.mu B) then .mu B else G.Res (B :: Bs)
  | A => A

/-- The traversal of a binder's body. -/
def travB : Stack → Val
  | [] => travOf (.var 0)
  | B :: Bs => trav ks G (B :: Bs) B

/-- The dispatch on the tag, with the fixed point at variable `j`: the branch of `b` runs
`travB b` and then `alg b`. -/
def dsp : Nat → List Stack → Expr
  | _, [] => .var 0
  | j, b :: r => .case (.var 0)
      (bindE (.app (.app (.val (travB ks G b)) (.var (j + 1))) (.var 0)) (.app (.val (G.alg b)) (.var 0)))
      (dsp (j + 1) r)

/-- **The recursive call**, Bekič's simultaneous fixed point over the binders `ks`. -/
def selfD : Val := selfV (dsp ks G 1 ks)

/-- The handle of binder `b`. -/
def hdl (b : Stack) : Val := .lam (.app (.val (selfD ks G)) (tagE (ks.idxOf b) (.var 0)))

end

/-! ### Closedness -/

theorem tagE_closed : ∀ (k : Nat) {e : Expr} {j : Nat}, closedAt j e = true →
    closedAt j (tagE k e) = true
  | 0, _, _, h => h
  | k + 1, _, _, h => tagE_closed k h

theorem travOf_closed {e : Expr} (h : closedAt 2 e = true) : closedAt 0 (travOf e).1 = true := by
  simpa [travOf, closedAt] using h

theorem stepV_closed {t g : Val} (ht : closedAt 0 t.1 = true) (hg : closedAt 0 g.1 = true) :
    closedAt 0 (stepV t g).1 = true := by
  simp [stepV, stepE, bindE, closedAt, closedAt_mono _ ht (Nat.zero_le _),
    closedAt_mono _ hg (Nat.zero_le _)]

theorem arrE_closed {g f : Val} (hg : closedAt 0 g.1 = true) (hf : closedAt 0 f.1 = true) :
    closedAt 2 (arrE g f) = true := by
  simp [arrE, bindE, closedAt, closedAt_mono _ hg (Nat.zero_le _),
    closedAt_mono _ hf (Nat.zero_le _), Val.i32]

theorem callE_closed (ks : List Stack) (b : Stack) : closedAt 2 (callE ks b) = true := by
  simp [callE, closedAt, tagE_closed _ (show closedAt 2 (.var 0) = true by rfl)]

theorem tE_closed (ks : List Stack) (G : Algs) (Bs : Stack) :
    ∀ A : VTy, closedAt 2 (tE ks G Bs A) = true
  | .tvar i => callE_closed ks _
  | .tensor A B => by
      simp only [tE]; split
      · rfl
      · simp [bindE, closedAt, closedAt_mono _ (travOf_closed (tE_closed ks G Bs A)) (Nat.zero_le _),
          closedAt_mono _ (travOf_closed (tE_closed ks G Bs B)) (Nat.zero_le _)]
  | .sum A B => by
      simp only [tE]; split
      · rfl
      · simp [bindE, closedAt, closedAt_mono _ (travOf_closed (tE_closed ks G Bs A)) (Nat.zero_le _),
          closedAt_mono _ (travOf_closed (tE_closed ks G Bs B)) (Nat.zero_le _)]
  | .ref S => by
      simp only [tE]; split
      · rfl
      · simp [bindE, closedAt, closedAt_mono _ (travOf_closed (tE_closed ks G Bs S)) (Nat.zero_le _)]
  | .fam (.ref S) => by
      simp only [tE]; split
      · rfl
      · exact arrE_closed (G.algA_closed _ _)
          (stepV_closed (travOf_closed (tE_closed ks G Bs S)) (G.algA_closed _ _))
  | .mu B => by
      simp only [tE]; split
      · rfl
      · exact callE_closed ks _
  | .unit | .zero | .thunk _ | .imm _ _ | .mut _ _ | .box _ _ | .bang _ | .unk | .int _ | .opq _ => rfl
  | .fam .unit | .fam (.tensor _ _) | .fam .zero | .fam (.sum _ _) | .fam (.thunk _)
  | .fam (.imm _ _) | .fam (.mut _ _) | .fam (.box _ _) | .fam (.bang _) | .fam .unk
  | .fam (.tvar _) | .fam (.mu _) | .fam (.int _) | .fam (.fam _) | .fam (.opq _) => rfl

theorem trav_closed (ks : List Stack) (G : Algs) (Bs : Stack) (A : VTy) :
    closedAt 0 (trav ks G Bs A).1 = true := travOf_closed (tE_closed ks G Bs A)

theorem travB_closed (ks : List Stack) (G : Algs) : ∀ b, closedAt 0 (travB ks G b).1 = true
  | [] => rfl
  | B :: Bs => trav_closed ks G (B :: Bs) B

theorem dsp_closed (ks : List Stack) (G : Algs) :
    ∀ (r : List Stack) (j : Nat), closedAt (j + 1) (dsp ks G j r) = true
  | [], j => by simp [dsp, closedAt]
  | b :: r, j => by
      have h₁ := dsp_closed ks G r (j + 1)
      have h₂ := closedAt_mono _ (G.alg_closed b) (Nat.zero_le (j + 3))
      have h₃ := closedAt_mono _ (travB_closed ks G b) (Nat.zero_le (j + 2))
      have h₂' : closedAt (j + 1 + 1) (Val.lam ((G.alg b).1.app (Expr.var 0))).1 = true := by
        simp [closedAt, h₂]
      simp only [dsp, bindE, closedAt, Bool.and_eq_true, decide_eq_true_eq, h₁, h₃, h₂',
        true_and, and_true]
      exact ⟨by omega, by omega, by omega⟩

theorem selfD_closed (ks : List Stack) (G : Algs) : closedAt 0 (selfD ks G).1 = true :=
  selfV_closed (dsp_closed ks G ks 1)

/-- A closed position's body is `w`. -/
theorem tE_leaf (ks : List Stack) (G : Algs) (Bs : Stack) :
    ∀ {A : VTy}, clB 0 A = true → tE ks G Bs A = .var 0
  | .tvar _, h => by simp [clB] at h
  | .tensor _ _, h => by simp only [tE, if_pos h]
  | .sum _ _, h => by simp only [tE, if_pos h]
  | .ref _, h => by simp only [clB] at h; simp only [tE, if_pos h]
  | .fam (.ref _), h => by simp only [clB] at h; simp only [tE, if_pos h]
  | .mu _, h => by simp only [tE, if_pos h]
  | .unit, _ | .zero, _ | .thunk _, _ | .imm _ _, _ | .mut _ _, _ | .box _ _, _ | .bang _, _
  | .unk, _ | .int _, _ | .opq _, _ => rfl
  | .fam .unit, _ | .fam (.tensor _ _), _ | .fam .zero, _ | .fam (.sum _ _), _
  | .fam (.thunk _), _ | .fam (.imm _ _), _ | .fam (.mut _ _), _ | .fam (.box _ _), _
  | .fam (.bang _), _ | .fam .unk, _ | .fam (.tvar _), _ | .fam (.mu _), _ | .fam (.int _), _
  | .fam (.fam _), _ | .fam (.opq _), _ => rfl

/-- A closed position's result is itself. -/
theorem resO_leaf (G : Algs) (Bs : Stack) :
    ∀ {A : VTy}, clB 0 A = true → resO G Bs A = A
  | .tvar _, h => by simp [clB] at h
  | .tensor _ _, h => by simp only [resO, if_pos h]
  | .sum _ _, h => by simp only [resO, if_pos h]
  | .ref _, h => by simp only [clB] at h; simp only [resO, if_pos h]
  | .fam (.ref _), h => by simp only [clB] at h; simp only [resO, if_pos h]
  | .mu _, h => by simp only [resO, if_pos h]
  | .unit, _ | .zero, _ | .thunk _, _ | .imm _ _, _ | .mut _ _, _ | .box _ _, _ | .bang _, _
  | .unk, _ | .int _, _ | .opq _, _ => rfl
  | .fam .unit, _ | .fam (.tensor _ _), _ | .fam .zero, _ | .fam (.sum _ _), _
  | .fam (.thunk _), _ | .fam (.imm _ _), _ | .fam (.mut _ _), _ | .fam (.box _ _), _
  | .fam (.bang _), _ | .fam .unk, _ | .fam (.tvar _), _ | .fam (.mu _), _ | .fam (.int _), _
  | .fam (.fam _), _ | .fam (.opq _), _ => rfl

/-! ### Reduction -/

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

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

theorem callE_subst (ks : List Stack) (b : Stack) {s : Val} (hs : closedAt 0 s.1 = true) (w : Val) :
    ((callE ks b).subst 1 (s.shift 1 0)).subst 0 w = .app (.val s) (.val (tagV (ks.idxOf b) w)) := by
  simp [callE, tagE_subst, closed_shift hs, closed_subst hs, tagE_val]

/-- The `⊗` action, after the pair is taken apart. -/
theorem tensor_subst (t₁ t₂ s v₁ v₂ : Val) (h₁ : closedAt 0 t₁.1 = true)
    (h₂ : closedAt 0 t₂.1 = true) (hs : closedAt 0 s.1 = true) :
    (((Expr.letpair (.var 0)
        (bindE (.app (.app (.val t₁) (.var 3)) (.var 1))
          (bindE (.app (.app (.val t₂) (.var 4)) (.var 1))
            (.pair (.var 1) (.var 0))))).subst 1 (s.shift 1 0)).subst 0 (Val.pair v₁ v₂))
      = .letpair (.val (Val.pair v₁ v₂))
          (bindE (.app (.app (.val t₁) (.val s)) (.var 1))
            (bindE (.app (.app (.val t₂) (.val s)) (.var 1))
              (.pair (.var 1) (.var 0)))) := by
  simp [bindE, closed_subst h₁, closed_subst h₂, closed_shift hs, closed_subst hs]

theorem tensor_body (t₁ t₂ s v₁ v₂ : Val) (h₁ : closedAt 0 t₁.1 = true)
    (h₂ : closedAt 0 t₂.1 = true) (hs : closedAt 0 s.1 = true) :
    ((bindE (.app (.app (.val t₁) (.val s)) (.var 1))
        (bindE (.app (.app (.val t₂) (.val s)) (.var 1))
          (.pair (.var 1) (.var 0)))).subst 0 (v₂.shift 1 0)).subst 0 v₁
      = (Kont.appR (.val (.lam (bindE (.app (.app (.val t₂) (.val s)) (.val (v₂.shift 1 0)))
          (.pair (.var 1) (.var 0))))) .hole).plug
          (.app (.app (.val t₁) (.val s)) (.val v₁)) := by
  simp [bindE, Kont.plug, closed_subst h₁, closed_subst h₂, closed_subst hs, subst_shift_succ]

theorem tensor_body₂ (t₂ s v₂ r₁ : Val) (h₂ : closedAt 0 t₂.1 = true) (hs : closedAt 0 s.1 = true) :
    (bindE (.app (.app (.val t₂) (.val s)) (.val (v₂.shift 1 0)))
        (.pair (.var 1) (.var 0))).subst 0 r₁
      = (Kont.appR (.val (.lam (.pair (.val (r₁.shift 1 0)) (.var 0)))) .hole).plug
          (.app (.app (.val t₂) (.val s)) (.val v₂)) := by
  simp [bindE, Kont.plug, closed_subst h₂, closed_subst hs, subst_shift_succ]

theorem sum_subst (t₁ t₂ s w : Val) (h₁ : closedAt 0 t₁.1 = true)
    (h₂ : closedAt 0 t₂.1 = true) (hs : closedAt 0 s.1 = true) :
    ((Expr.case (.var 0)
        (bindE (.app (.app (.val t₁) (.var 2)) (.var 0)) (.inj₁ (.var 0)))
        (bindE (.app (.app (.val t₂) (.var 2)) (.var 0)) (.inj₂ (.var 0)))).subst 1 (s.shift 1 0)).subst 0 w
      = .case (.val w)
          (bindE (.app (.app (.val t₁) (.val s)) (.var 0)) (.inj₁ (.var 0)))
          (bindE (.app (.app (.val t₂) (.val s)) (.var 0)) (.inj₂ (.var 0))) := by
  simp [bindE, closed_subst h₁, closed_subst h₂, closed_shift hs, closed_subst hs]

theorem sum_branch (t s v : Val) (ht : closedAt 0 t.1 = true) (hs : closedAt 0 s.1 = true)
    (inj : Expr → Expr) (hinj : ∀ j s e, Expr.subst j s (inj e) = inj (Expr.subst j s e)) :
    (bindE (.app (.app (.val t) (.val s)) (.var 0)) (inj (.var 0))).subst 0 v
      = (Kont.appR (.val (.lam (inj (.var 0)))) .hole).plug
          (.app (.app (.val t) (.val s)) (.val v)) := by
  simp [bindE, Kont.plug, closed_subst ht, closed_subst hs, hinj]

theorem ref_subst (t s w : Val) (ht : closedAt 0 t.1 = true) (hs : closedAt 0 s.1 = true) :
    ((bindE (.app (.val (.prim .free)) (.var 0))
        (.app (.app (.val t) (.var 2)) (.var 0))).subst 1 (s.shift 1 0)).subst 0 w
      = (Kont.appR (.val (.lam (.app (.app (.val t) (.val s)) (.var 0)))) .hole).plug
          (.app (.val (.prim .free)) (.val w)) := by
  simp [bindE, Kont.plug, closed_subst ht, closed_shift hs, closed_subst hs]

theorem ref_body (t s v : Val) (ht : closedAt 0 t.1 = true) (hs : closedAt 0 s.1 = true) :
    (Expr.app (.app (.val t) (.val s)) (.var 0)).subst 0 v = .app (.app (.val t) (.val s)) (.val v) := by
  simp [closed_subst ht, closed_subst hs]

theorem alg_subst (g r : Val) (hg : closedAt 0 g.1 = true) :
    (Expr.app (.val g) (.var 0)).subst 0 r = .app (.val g) (.val r) := by
  simp [closed_subst hg]

end BoCa.Fig16.LogRel.Core.NestedFold

end
