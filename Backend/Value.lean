import Support.Syntax.Integers

/-!
# Backend — observable values

The printable form of a result, shared by every stage: `Support`'s interpreter, the closure-IR
and flat-IR interpreters, and the compiled program (whose printer, generated per layout type in
`Backend/Flat/Lower.lean`, writes the same text). Integers print as their unsigned bit pattern in the syntax of
`docs/syntax-core.md` §8a; a function (a `λ`, a primitive, a partial `store`) prints as `<fun>`
and a location as `<loc>`, since neither has a machine-independent spelling.
-/

namespace Backend

/-- A result value, as far as it is observable. -/
inductive PV where
  | unit
  | i32 (n : UInt32)
  | i64 (n : UInt64)
  | u8 (n : UInt8)
  | pair (a b : PV)
  | inj (right : Bool) (a : PV)
  | fn
  | loc
  deriving Repr, BEq, Inhabited

mutual
/-- `inl`/`inr` take their operand as an atom: an injection is parenthesized. -/
def PV.renderAtom : PV → String
  | .inj r a => "(" ++ PV.renderInj r a ++ ")"
  | v => PV.render v

def PV.renderInj (r : Bool) (a : PV) : String :=
  (if r then "inr " else "inl ") ++ PV.renderAtom a

def PV.render : PV → String
  | .unit => "()"
  | .i32 n => s!"i32[{n.toNat}]"
  | .i64 n => s!"i64[{n.toNat}]"
  | .u8 n => s!"u8[{n.toNat}]"
  | .pair a b => "(" ++ PV.render a ++ ", " ++ PV.render b ++ ")"
  | .inj r a => PV.renderInj r a
  | .fn => "<fun>"
  | .loc => "<loc>"
end

/-- What a stage writes: the program's standard output followed by the report, and its standard
error. -/
structure Output where
  out : ByteArray
  err : ByteArray

/-- The program's output bytes, then the report. -/
def Output.mk' (out err : ByteArray) (report : String) : Output := ⟨out ++ report.toUTF8, err⟩

/-- What every stage prints for a finished run: the value, then the number of live objects
after the value has been dropped. The source counts cells; the compiled stages count every
object, so a leaked cell also counts the structure it holds. The two counts are zero together. -/
def report (v : PV) (live : Nat) : String :=
  v.render ++ "\nlive " ++ toString live ++ "\n"

/-! ### The clock and the arguments at the interpreters  `[spec §34]` -/

/-- The descriptor of the arguments' stream: the content of the `args` cell, which every stage
reads from the arguments, not from a host stream. -/
def argsFd : UInt32 := 0xFFFFFFFF

/-- The model's time after a sleep of `ns` nanoseconds at time `t`: `t` when `ns ≤ 0`, else
`t + ns`, saturating at `2^63 − 1` (SPEC §34, `Core/Stdio.lean`'s `clock_sleep`). -/
def sleptNs (t ns : UInt64) : UInt64 :=
  if ns.toInt64 ≤ 0 then t
  else
    let s := t + ns
    if s.toInt64 < t.toInt64 then 0x7fffffffffffffff else s

/-- The arguments' stream: each argument's bytes followed by `0`. -/
def argsBytes (args : List String) : List UInt8 :=
  args.flatMap fun a => a.toUTF8.toList ++ [0]

end Backend
