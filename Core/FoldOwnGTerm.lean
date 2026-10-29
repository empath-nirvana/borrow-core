import Core.FoldClass

/-!
# Core — the general owned fold: the term  `[spec §6]`

One generator, an action per former. `tE ks Bs A` is the body of the traversal of a position `A`
under the binders `Bs`, with `s` (variable `1`) the recursive call and `w` (variable `0`) the
value:

| former | action |
|---|---|
| closed leaf | `w` |
| `tvar i` | `s (tag (mu (Bs.drop i)) w)`: the handle of the variable's binder |
| `⊗`, `⊕` | componentwise |
| `Ref S` | `free w`, then the traversal of `S` |
| `[Ref S]` | a `count` loop over the slots: `idx`, take the slot's value out (`swap` with `()`), traverse it, step the algebra `s (tag (arr Bs S) (inj₂ (acc, r)))`; seed `s (tag (arr Bs S) (inj₁ ()))`; then `drop` the emptied array, its buffer at once |
| `μB` | `s (tag (mu (B :: Bs)) w)`: the handle of the inner binder |

The recursive call `s = λx. self gs x` is one Z combinator (`selfG`) whose body dispatches on the
tag, Bekič's simultaneous fixed point over the keys `ks`. The tag of a key is its index in `ks`
(the first, `ks.idxOf`), as nested injections (`tagV`). The branch of a `μ` key runs the
traversal of its body and then its algebra; the branch of an array key runs its algebra. The
algebras are the run-time tuple `gs`, one per key in the order of `ks` (`projV n p` takes the
`p`-th of `n`). An array keeps its state `(acc, (w, s))` in the loop, so the step `stepV` is a
closed value.

`resO G Bs A` is the traversal's result type: `A` with each key's result (`Algs`) at its
positions. `foldOwnGV B₀ = λgs. λw. self gs (tag (mu [B₀]) w)`, a closed value.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.FoldP
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)

/-- The results of the keys: of a `μ` key and of an array key. -/
structure Algs where
  /-- The result of a `μ` key. -/
  Res : Stack → VTy
  /-- The result of an array key: its stack and its element type. -/
  ResA : Stack → VTy → VTy

/-- `λs. λw. e`. -/
def travOf (e : Expr) : Val := .lam (.val (.lam e))

/-- The tag of index `k`: `inj₂ᵏ (inj₁ e)`. -/
def tagE : Nat → Expr → Expr
  | 0, e => .inj₁ e
  | k + 1, e => .inj₂ (tagE k e)

def tagV : Nat → Val → Val
  | 0, w => .inj₁ w
  | k + 1, w => .inj₂ (tagV k w)

/-- `λ_. ()`, the consumer the emptied array is dropped with. -/
def unitF : Val := .lam (.val .unit)

/-- One step of the array loop, at the state `(i, (acc, (w, s)))`: the `i`-th slot of `w` is
emptied by `swap` with `()`, its value traversed by `t` with the handle `s`, and the algebra of
the key `k`, `s (tag k (inj₂ (acc, r)))`, is the next accumulator. -/
def stepE (k : Nat) (t : Val) : Expr :=
  .letpair (.var 0)
    (.letpair (.var 0)
      (.letpair (.var 0)
        (.case (.app (.val (.prim .idx)) (.pair (.var 1) (.var 5)))
          (bindE (.app (.app swap (.var 0)) (.val .unit))
            (.letpair (.var 0)
              (bindE (.app (.app (.val t) (.var 4)) (.var 0))
                (bindE (.app (.var 5) (tagE k (.inj₂ (.pair (.var 8) (.var 0)))))
                  (.pair (.var 0) (.pair (.var 7) (.var 6)))))))
          (.pair (.var 4) (.pair (.var 2) (.var 1))))))

def stepV (k : Nat) (t : Val) : Val := .lam (stepE k t)

/-- The array action of the key `k` (handle `1`, array `0`): seed `s (tag k (inj₁ ()))`, then
`count` from `0` to the length with the state `(acc, (w, s))`, then `drop` the emptied array the
state hands back and answer the accumulator. -/
def arrE (k : Nat) (f : Val) : Expr :=
  .letpair (.var 0)
    (bindE (.app (.var 3) (tagE k (.inj₁ .unit)))
      (bindE (.app (.val (.prim .count)) (.pair (.val f) (.pair (.var 1)
          (.pair (.val (Val.i32 0)) (.pair (.var 0) (.pair (.var 3) (.var 4)))))))
        (.letpair (.var 0)
          (.letpair (.var 0)
            (bindE (.app (.val (.prim .drop)) (.pair (.val unitF) (.var 1)))
              (.var 4))))))

section
variable (ks : List Bnd)

/-- The call of the handle of the key `k` on the value. -/
def callE (k : Bnd) : Expr := .app (.var 1) (tagE (ks.idxOf k) (.var 0))

/-- **The traversal's body**, by recursion on the position. -/
def tE (Bs : Stack) : VTy → Expr
  | .tvar i => callE ks (.mu (Bs.drop i))
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
      arrE (ks.idxOf (.arr Bs S)) (stepV (ks.idxOf (.arr Bs S)) (travOf (tE Bs S)))
  | .mu B => if clB 0 (.mu B) then .var 0 else callE ks (.mu (B :: Bs))
  | _ => .var 0

/-- The traversal of a position, a closed value `λs. λw. …`. -/
abbrev trav (Bs : Stack) (A : VTy) : Val := travOf (tE ks Bs A)

/-- The traversal of a `μ` key's body. -/
def travB : Bnd → Val
  | .mu (B :: Bs) => trav ks (B :: Bs) B
  | _ => travOf (.var 0)

end

/-- The result type: `A` with each key's result at its positions. -/
def resO (G : Algs) (Bs : Stack) : VTy → VTy
  | .tvar i => G.Res (Bs.drop i)
  | .tensor A B => if clB 0 (.tensor A B) then .tensor A B else .tensor (resO G Bs A) (resO G Bs B)
  | .sum A B => if clB 0 (.sum A B) then .sum A B else .sum (resO G Bs A) (resO G Bs B)
  | .ref S => if clB 0 S then .ref S else resO G Bs S
  | .fam (.ref S) => if clB 0 S then .fam (.ref S) else G.ResA Bs S
  | .mu B => if clB 0 (.mu B) then .mu B else G.Res (B :: Bs)
  | A => A

/-! ### The algebras: a tuple -/

/-- A right-nested tuple of values. -/
def tupV : List Val → Val
  | [] => .unit
  | [a] => a
  | a :: b :: r => .pair a (tupV (b :: r))

/-- A right-nested tuple of expressions. -/
def tupE : List Expr → Expr
  | [] => .unit
  | [a] => a
  | a :: b :: r => .pair a (tupE (b :: r))

/-- A right-nested tensor of types. -/
def tupTy : List VTy → VTy
  | [] => .unit
  | [A] => A
  | A :: B :: r => .tensor A (tupTy (B :: r))

/-- The `p`-th of an `n`-tuple. -/
def projE : Nat → Nat → Expr → Expr
  | 0, _, e => e
  | 1, _, e => e
  | _ + 2, 0, e => .letpair e (.var 1)
  | n + 2, p + 1, e => .letpair e (projE (n + 1) p (.var 0))

/-- `λg. projE n p g`. -/
def projV (n p : Nat) : Val := .lam (projE n p (.var 0))

/-- The algebra's type at a key: `!U(B⟨R⟩ ⊸ F R_b)` at a `μ` key with body `B`, and
`!U(1 ⊕ (R_a ⊗ S⟨R⟩) ⊸ F R_a)` at an array key of element type `S`. -/
def algTy (G : Algs) : Bnd → VTy
  | .mu [] => .unit
  | .mu (B :: Bs) => .bang (.lolli (resO G (B :: Bs) B) (G.Res (B :: Bs)))
  | .arr Bs S => .bang (.lolli (.sum .unit (.tensor (G.ResA Bs S) (resO G Bs S))) (G.ResA Bs S))

/-! ### The dispatch and the fold -/

section
variable (ks : List Bnd)

/-- The branch of the key `k` at the position `p` of `ks`, under `j` enclosing `case`s: the
payload is variable `0`, the algebras `gs` variable `j + 2`, the fixed point variable `j + 3`. -/
def branch (j p : Nat) : Bnd → Expr
  | .arr _ _ => .app (.app (.val (projV ks.length p)) (.var (j + 2))) (.var 0)
  | k => bindE (.app (.app (.val (travB ks k))
        (.val (.lam (.app (.app (.var (j + 4)) (.var (j + 3))) (.var 0))))) (.var 0))
      (.app (.app (.val (projV ks.length p)) (.var (j + 3))) (.var 0))

/-- The dispatch on the tag. -/
def dsp : Nat → Nat → List Bnd → Expr
  | _, _, [] => .var 0
  | j, p, k :: r => .case (.var 0) (branch ks j p k) (dsp (j + 1) (p + 1) r)

/-- The fixed point's body: `λgs. λx. dsp`, with the fixed point at variable `1`. -/
def fBG : Expr := .val (.lam (dsp ks 0 0 ks))

/-- **The recursive call**, Bekič's simultaneous fixed point over the keys `ks`. -/
def selfG : Val := selfV (fBG ks)

/-- The handle at the algebras `gs`: `λx. self gs x`. -/
def hG (gs : Val) : Val := .lam (.app (.app (.val (selfG ks)) (.val (gs.shift 1 0))) (.var 0))

end

/-- **The general owned fold**, `λgs. λw. self gs (tag (mu [B₀]) w)`.  `[spec §6]` -/
def foldOwnGV (B₀ : VTy) : Val :=
  .lam (.val (.lam (.app (.app (.val (selfG (keys B₀))) (.var 1)) (tagE 0 (.var 0)))))

/-! ### Closedness -/

theorem tagE_closed : ∀ (k : Nat) {e : Expr} {j : Nat}, closedAt j e = true →
    closedAt j (tagE k e) = true
  | 0, _, _, h => h
  | k + 1, _, _, h => tagE_closed k h

theorem travOf_closed {e : Expr} (h : closedAt 2 e = true) : closedAt 0 (travOf e).1 = true := by
  simpa [travOf, closedAt] using h

theorem swap_closedAt (j : Nat) : closedAt j swap = true := closedAt_mono _ swap_closed (Nat.zero_le _)

theorem stepV_closed (k : Nat) {t : Val} (ht : closedAt 0 t.1 = true) :
    closedAt 0 (stepV k t).1 = true := by
  simp [stepV, stepE, bindE, closedAt, closedAt_mono _ ht (Nat.zero_le _), swap_closedAt,
    tagE_closed k (e := .inj₂ (.pair (.var 8) (.var 0))) (j := 12) (by simp [closedAt])]

theorem unitF_closed : closedAt 0 unitF.1 = true := rfl

theorem arrE_closed (k : Nat) {f : Val} (hf : closedAt 0 f.1 = true) :
    closedAt 2 (arrE k f) = true := by
  simp [arrE, bindE, closedAt, closedAt_mono _ hf (Nat.zero_le _), Val.i32, unitF,
    tagE_closed k (e := .inj₁ .unit) (j := 4) rfl]

theorem callE_closed (ks : List Bnd) (k : Bnd) : closedAt 2 (callE ks k) = true := by
  simp [callE, closedAt, tagE_closed _ (show closedAt 2 (.var 0) = true by rfl)]

theorem tE_closed (ks : List Bnd) (Bs : Stack) :
    ∀ A : VTy, closedAt 2 (tE ks Bs A) = true
  | .tvar i => callE_closed ks _
  | .tensor A B => by
      simp only [tE]; split
      · rfl
      · simp [bindE, closedAt, closedAt_mono _ (travOf_closed (tE_closed ks Bs A)) (Nat.zero_le _),
          closedAt_mono _ (travOf_closed (tE_closed ks Bs B)) (Nat.zero_le _)]
  | .sum A B => by
      simp only [tE]; split
      · rfl
      · simp [bindE, closedAt, closedAt_mono _ (travOf_closed (tE_closed ks Bs A)) (Nat.zero_le _),
          closedAt_mono _ (travOf_closed (tE_closed ks Bs B)) (Nat.zero_le _)]
  | .ref S => by
      simp only [tE]; split
      · rfl
      · simp [bindE, closedAt, closedAt_mono _ (travOf_closed (tE_closed ks Bs S)) (Nat.zero_le _)]
  | .fam (.ref S) => by
      simp only [tE]; split
      · rfl
      · exact arrE_closed _ (stepV_closed _ (travOf_closed (tE_closed ks Bs S)))
  | .mu B => by
      simp only [tE]; split
      · rfl
      · exact callE_closed ks _
  | .unit | .zero | .thunk _ | .imm _ _ | .mut _ _ | .box _ _ | .bang _ | .unk | .int _ | .opq _ => rfl
  | .fam .unit | .fam (.tensor _ _) | .fam .zero | .fam (.sum _ _) | .fam (.thunk _)
  | .fam (.imm _ _) | .fam (.mut _ _) | .fam (.box _ _) | .fam (.bang _) | .fam .unk
  | .fam (.tvar _) | .fam (.mu _) | .fam (.int _) | .fam (.fam _) | .fam (.opq _) => rfl

theorem trav_closed (ks : List Bnd) (Bs : Stack) (A : VTy) :
    closedAt 0 (trav ks Bs A).1 = true := travOf_closed (tE_closed ks Bs A)

theorem travB_closed (ks : List Bnd) : ∀ k, closedAt 0 (travB ks k).1 = true
  | .mu [] => rfl
  | .mu (B :: Bs) => trav_closed ks (B :: Bs) B
  | .arr _ _ => rfl

theorem projE_closed : ∀ (n p : Nat) {e : Expr} {j : Nat}, closedAt j e = true →
    closedAt j (projE n p e) = true
  | 0, _, _, _, h => h
  | 1, _, _, _, h => h
  | _ + 2, 0, _, _, h => by simp [projE, closedAt, h]
  | n + 2, p + 1, _, j, h => by
      simp only [projE, closedAt, h, Bool.true_and]
      exact projE_closed (n + 1) p (j := j + 2) rfl

theorem projV_closed (n p : Nat) : closedAt 0 (projV n p).1 = true := by
  simp [projV, closedAt, projE_closed n p (e := .var 0) (j := 1) rfl]

theorem branch_closed (ks : List Bnd) (j p : Nat) :
    ∀ k : Bnd, closedAt (j + 4) (branch ks j p k) = true
  | .arr _ _ => by
      simp [branch, closedAt, closedAt_mono _ (projV_closed _ p) (Nat.zero_le _)]
  | .mu b => by
      simp [branch, bindE, closedAt, closedAt_mono _ (projV_closed _ p) (Nat.zero_le _),
        closedAt_mono _ (travB_closed ks _) (Nat.zero_le _)]

theorem dsp_closed (ks : List Bnd) :
    ∀ (r : List Bnd) (j p : Nat), closedAt (j + 3) (dsp ks j p r) = true
  | [], j, _ => by simp [dsp, closedAt]
  | k :: r, j, p => by
      have h₁ := dsp_closed ks r (j + 1) (p + 1)
      have h₂ := branch_closed ks j p k
      simp only [dsp, closedAt, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by omega, h₂⟩, h₁⟩

theorem fBG_closed (ks : List Bnd) : closedAt 2 (fBG ks) = true := by
  simpa [fBG, closedAt] using dsp_closed ks ks 0 0

theorem selfG_closed (ks : List Bnd) : closedAt 0 (selfG ks).1 = true :=
  selfV_closed (fBG_closed ks)

theorem foldOwnGV_closed (B₀ : VTy) : closedAt 0 (foldOwnGV B₀).1 = true := by
  simp [foldOwnGV, tagE, closedAt, closedAt_mono _ (selfG_closed _) (Nat.zero_le _)]

/-- A closed position's body is `w`. -/
theorem tE_leaf (ks : List Bnd) (Bs : Stack) :
    ∀ {A : VTy}, clB 0 A = true → tE ks Bs A = .var 0
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

end BoCa.Fig16.LogRel.Core.FoldP

end
