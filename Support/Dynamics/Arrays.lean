import Paper.S1_Syntax.Definitions
import Support.Syntax.Terms
import Support.Dynamics.Host

/-!
# Support — Dynamics — Arrays  `[spec §9]`

The terms the array steps of the machine produce. An array is the value `(ℓ, n)`: a base
location and a length `n : I32`; its `i`-th leaf is the location `ℓ + i`.

- `tab (c, f)` places `len(c)` cells holding `()` at fresh consecutive locations and continues
  as `tabFill`, which stores `f i` in the `i`-th cell and returns the array.
- `idx ((ℓ, n), i)` answers `idxAns ℓ n i`: `inj₁ (ℓ + i)` when `i < n` (unsigned), else `inj₂ ()`.
- `split ((ℓ, n), i)` answers `splitAns ℓ n i`: `inj₁ ((ℓ, i), (ℓ + i, n − i))` when `i ≤ n`
  (unsigned), else `inj₂ (ℓ, n)`. The machine subtracts, so every host splits alike.
- `drop (f, (ℓ, n))` continues as `dropFill`, which frees each cell in index order and hands its
  contents to `f`.

`len(c)` is `c` when `c < 2³¹` and `0` otherwise, so a negative length is the empty array.
-/

namespace BoCa

/-- `len(c)`: the length of the array `tab (c, f)` makes.  `[spec §9]` -/
def arrLen (c : UInt32) : UInt32 := if c < 0x80000000 then c else 0

/-- The array value `(ℓ, n)`.  `[spec §9]` -/
def Val.arr (ℓ : Loc) (n : UInt32) : Val := .pair (.loc ℓ) (.i32 n)

theorem Val.arr_inj {ℓ ℓ' : Loc} {n n' : UInt32} (h : Val.arr ℓ n = Val.arr ℓ' n') :
    ℓ = ℓ' ∧ n = n' := by
  have hv := congrArg Subtype.val h
  simp only [Val.arr, Val.pair, Val.loc, Val.i32, Expr.pair.injEq, Expr.loc.injEq, Expr.prim.injEq,
    Prim.lit.injEq, IntLit.i32.injEq] at hv
  exact hv

/-- `store (ℓ+i) (f i); …; store (ℓ+i+k−1) (f (i+k−1)); (ℓ, n)`.  `[spec §9]` -/
def tabFill (f : Val) (ℓ : Loc) (n : UInt32) : Nat → Nat → Expr
  | _, 0 => .val (Val.arr ℓ n)
  | i, k + 1 =>
      .seq (.app (.app (.val (.prim .store)) (.val (.loc (ℓ + i))))
              (.app (.val f) (.val (Val.i32 (UInt32.ofNat i)))))
        (tabFill f ℓ n (i + 1) k)

/-- `f (free (ℓ+i)); …; f (free (ℓ+i+k−1)); ()`.  `[spec §9]` -/
def dropFill (f : Val) (ℓ : Loc) : Nat → Nat → Expr
  | _, 0 => .val .unit
  | i, k + 1 =>
      .seq (.app (.val f) (.app (.val (.prim .free)) (.val (.loc (ℓ + i)))))
        (dropFill f ℓ (i + 1) k)

/-- One step of `count (f, (n, (i, s)))`: while `i < len(n)`, apply `f` to `(i, s)` and count on
    from `i + 1`; then answer `s`. The counter is the machine's, so every host counts alike.
    `[spec §16]` -/
def countNext (f : Val) (n i : UInt32) (s : Val) : Expr :=
  if i < arrLen n then
    .app (.val (.prim .count)) (.pair (.val f) (.pair (.val (.i32 n))
      (.pair (.val (.i32 (i + 1))) (.app (.val f) (.val (.pair (.i32 i) s))))))
  else .val s

/-- One step of `count_try (f, (n, (i, s)))`: while `i < len(n)`, apply `f` to `(i, s)`; on
    `inj₁ s′` count on from `i + 1` with `s′`, on `inj₂ e` answer `inj₂ e`; at the bound answer
    `inj₁ s`. The branches bind the step's answer, so `f` is shifted past that binder. The counter
    is the machine's, as `count`'s.  `[spec §16]` -/
def countTryNext (f : Val) (n i : UInt32) (s : Val) : Expr :=
  if i < arrLen n then
    .case (.app (.val f) (.val (.pair (.i32 i) s)))
      (.app (.val (.prim .countTry)) (.pair (.val (f.shift 1 0)) (.pair (.val (.i32 n))
        (.pair (.val (.i32 (i + 1))) (.var 0)))))
      (.inj₂ (.var 0))
  else .val (.inj₁ s)

/-- The answer of `idx ((ℓ, n), i)`: the `i`-th leaf when `i < n`, unsigned; else `inj₂ ()`.
    `[spec §9]` -/
def idxAns (ℓ : Loc) (n i : UInt32) : Val :=
  if i < n then .inj₁ (.loc (ℓ + i.toNat)) else .inj₂ .unit

/-- The answer of `split ((ℓ, n), i)`: the parts `(ℓ, i)` and `(ℓ + i, n − i)` when `i ≤ n`,
    unsigned; else the family back.  `[spec §9]` -/
def splitAns (ℓ : Loc) (n i : UInt32) : Val :=
  if i ≤ n then .inj₁ (.pair (Val.arr ℓ i) (Val.arr (ℓ + i.toNat) (n - i))) else .inj₂ (Val.arr ℓ n)

end BoCa
