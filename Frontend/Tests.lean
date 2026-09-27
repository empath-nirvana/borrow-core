import Frontend.Parser
import Frontend.Print
/-!
# Frontend — Tests

Small cases of the parser and of the round-trip property `(parse (print t)).strip = t.strip`,
checked by the kernel (`decide +kernel`: the kernel evaluates the lexer, the parser and the
printer; no `native_decide`). The corpus (`scripts/parse-corpus.sh`) checks the same property
on whole programs by running `bcc parse`.
-/

namespace Frontend.Tests

open Frontend

/-- `s` parses to `t` up to spans. -/
def parsesTo {α} [BEq α] (p : String → Except Error α) (strip : α → α) (s : String) (t : α) :
    Bool :=
  match p s with
  | .ok a => strip a == t
  | .error _ => false

/-- `s` parses, and printing and re-parsing the result gives it back up to spans. -/
def roundTrips {α} [BEq α] (p : String → Except Error α) (strip : α → α) (pp : α → String)
    (s : String) : Bool :=
  match p s with
  | .ok a => match p (pp a) with
    | .ok b => strip b == strip a
    | .error _ => false
  | .error _ => false

def rejects {α} (p : String → Except Error α) (s : String) : Bool :=
  match p s with
  | .ok _ => false
  | .error _ => true

private def n : Span := .none

/-! ### Precedence (syntax-core §4, §6.5) -/

/-- `S -o F (A + S) & F 1` is `S -o ((F (A + S)) & (F 1))`. -/
theorem prec_amp :
    parsesTo parseCTy CTy.strip "S -o F (A + S) & F 1"
      (.arr n (.name n "S") (.amp n (.ret n (.sum n (.name n "A") (.name n "S"))) (.ret n (.unit n))))
      = true := by decide +kernel

/-- `imm 'a Nat * Nat` is `(imm 'a Nat) * Nat`. -/
theorem prec_imm :
    parsesTo parseVTy VTy.strip "imm 'a Nat * Nat"
      (.tensor n (.imm n (.var n "a") (.name n "Nat")) (.name n "Nat")) = true := by
  decide +kernel

/-- `F A * B` is a sort error. -/
theorem sort_error : rejects parseVTy "F A * B" = true := by decide +kernel

/-- `force f s .1` is `((force f) s).1`. -/
theorem prec_spine :
    parsesTo parseComp Comp.strip "force f s .1"
      (.proj n true (.app n (.force n ⟨"f", n⟩) ⟨"s", n⟩)) = true := by decide +kernel

/-- `roll inr n` is `roll (inr n)`. -/
theorem prec_prefix :
    parsesTo parseVal Val.strip "roll inr n" (.roll n (.inr n (.var n "n"))) = true := by
  decide +kernel

/-- `f['y]` is a `def` at a type argument; `f ['y]` is an instantiation. -/
theorem brackets :
    parsesTo parseVal Val.strip "f [top] x"
      (.app n (.inst n (.var n "f") (.top n)) (.var n "x")) = true ∧
    parsesTo parseVal Val.strip "f[A]" (.defApp n "f" [.name n "A"]) = true := by
  decide +kernel

/-- `'a /\ 'b \/ top` is `('a /\ 'b) \/ top`. -/
theorem prec_life :
    parsesTo parseVTy VTy.strip "box ('a /\\ 'b \\/ top) 1"
      (.box n (.join n (.meet n (.var n "a") (.var n "b")) (.top n)) (.unit n)) = true := by
  decide +kernel

/-! ### Round trips -/

theorem rt_val : roundTrips parseVal Val.strip (Val.pp · 0 0)
    "roll (inr (x, boxed['a] (unbang f) ['b] y))" = true := by decide +kernel

theorem rt_comp : roundTrips parseComp Comp.strip (Comp.pp · 0 0)
    "x <- (force f).1; case x { inl u -> return u | inr v -> < return v, <> > }" = true := by
  decide +kernel

theorem rt_linear : roundTrips parseComp Comp.strip (Comp.pp · 0 0)
    "linear x <- return (); linear y : 1 <- return x; return y" = true := by
  decide +kernel

theorem rt_ty : roundTrips parseVTy VTy.strip (VTy.pp · 0)
    "!U (Nat -o F (all 'y < top. imm 'y Nat => Nat) & top) * mu X. 1 + ref X" = true := by
  decide +kernel

theorem rt_array : roundTrips parseVTy VTy.strip (VTy.pp · 0)
    "array (ref i32) * array_imm 'a i32 => ref array i32" = true := by
  decide +kernel

theorem rt_program : roundTrips parseProgram Program.strip Program.pp
    "type Nat = mu X. 1 + X
     shape Node = node (leaf Nat) (leaf (ref Nat))
     def one : Nat = roll (inr (roll (inl ())))
     def id[A] : A => A = thunkv fun (x : A) -> return x
     extern e : !(1 => 1)
     main : F Nat = r <- return (alloc_s[Node] (one, alloc[Nat] one)); let (a, b) = r; return (id[Nat] a)"
    = true := by decide +kernel

end Frontend.Tests
