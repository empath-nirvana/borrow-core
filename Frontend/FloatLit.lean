/-!
# Frontend — float literals  `[spec §37]`

A decimal `m × 10^e` as the bits of the nearest binary32 or binary64 float, ties to even: exact
arithmetic on `Nat`, so every literal is correctly rounded. Past the largest finite float it is
`inf`; below half the least subnormal, `0`.
-/

namespace Frontend

/-- A binary format: `p` significand bits (with the hidden one), exponent bias `bias`. -/
structure FloatFmt where
  p : Nat
  bias : Nat

def FloatFmt.f32 : FloatFmt := ⟨24, 127⟩
def FloatFmt.f64 : FloatFmt := ⟨53, 1023⟩

/-- `⌊log₂ (num / den)⌋` for positive `num`, `den`. -/
def floorLog2 (num den : Nat) : Int :=
  let e : Int := (Nat.log2 num : Int) - (Nat.log2 den : Int)
  -- `num / den` is in `[2^(e-1), 2^(e+1))`.
  let geq : Bool := if e ≥ 0 then num ≥ den * 2 ^ e.toNat else num * 2 ^ (-e).toNat ≥ den
  if geq then e else e - 1

/-- The bits of the float nearest `num / den`, positive. -/
def ratToBits (F : FloatFmt) (num den : Nat) : Nat :=
  let emin : Int := 1 - F.bias
  let emax : Int := F.bias
  let infBits := (2 * F.bias + 1) * 2 ^ (F.p - 1)
  if num = 0 then 0 else
  let E := max (floorLog2 num den) emin
  let sh : Int := E - (F.p - 1 : Nat)
  let (N, D) := if sh ≥ 0 then (num, den * 2 ^ sh.toNat) else (num * 2 ^ (-sh).toNat, den)
  let q := N / D
  let r := N % D
  let q := if 2 * r > D || (2 * r = D && q % 2 = 1) then q + 1 else q
  let (q, E) := if q = 2 ^ F.p then (q / 2, E + 1) else (q, E)
  if E > emax then infBits
  else if q < 2 ^ (F.p - 1) then q
  else ((E + F.bias).toNat) * 2 ^ (F.p - 1) + (q - 2 ^ (F.p - 1))

/-- The bits of the float nearest `m × 10^e`. An exponent far past the format's range is cut
to one that still overflows (or underflows) the same way. -/
def decToBits (F : FloatFmt) (m : Nat) (e : Int) : Nat :=
  let digits : Int := (toString m).length
  let lim : Int := 400 + digits
  let e := if e > lim then lim else if e < -lim - 400 then -lim - 400 else e
  if e ≥ 0 then ratToBits F (m * 10 ^ e.toNat) 1 else ratToBits F m (10 ^ (-e).toNat)

/-- A float literal's text, `d…[.d…][e[±]d…]`, as `m × 10^e`. -/
def decOfText (s : String) : Nat × Int :=
  let cs := s.toList
  let (mant, ex) := match cs.findIdx? (fun c => c == 'e' || c == 'E') with
    | some i => (cs.take i, cs.drop (i + 1))
    | none => (cs, [])
  let (ip, fp) := match mant.findIdx? (· == '.') with
    | some i => (mant.take i, mant.drop (i + 1))
    | none => (mant, [])
  let digs := (ip ++ fp).foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0
  let (neg, ed) := match ex with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ev : Int := ed.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0
  (digs, (if neg then -ev else ev) - fp.length)

end Frontend

namespace Frontend

/-! Spot checks of the rounding, by the kernel. -/

-- `0.1`, at both widths.
example : decToBits .f64 1 (-1) = 0x3FB999999999999A := by decide +kernel
example : decToBits .f32 1 (-1) = 0x3DCCCCCD := by decide +kernel
-- `2^53 + 1` ties to even, down; `2^53 + 3` up.
example : decToBits .f64 9007199254740993 0 = 0x4340000000000000 := by decide +kernel
example : decToBits .f64 9007199254740995 0 = 0x4340000000000002 := by decide +kernel
-- The greatest float, and past it.
example : decToBits .f64 17976931348623157 292 = 0x7FEFFFFFFFFFFFFF := by decide +kernel
example : decToBits .f64 1 400 = 0x7FF0000000000000 := by decide +kernel
-- The least subnormal, and below half of it.
example : decToBits .f64 5 (-324) = 1 := by decide +kernel
example : decToBits .f64 24703282292062327 (-340) = 0 := by decide +kernel
example : decOfText "2.5e-3" = (25, -4) := by decide +kernel

end Frontend
