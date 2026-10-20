import Backend.Flat.Syntax
import Backend.Flat.Host

/-!
# Backend — flat IR to LLVM IR  `[spec §40]`

Each flat-IR function `k` is the LLVM function `@f{k}`, `internal`, of the C calling convention,
over `i64` parameters. Its locals are `alloca`s of the entry block (`%l{i}`,
the parameters stored in, every other local `0`, as the flat-IR interpreter starts them), which
`clang -O2`'s `mem2reg` turns into SSA values. Every expression is computed as an `i64` word in
argument order, as the flat-IR interpreter evaluates it; a 32-bit operand is the word's low half,
and a 32-bit result is zero-extended.

- **Results.** A function of no result returns `void`, of one an `i64`, of up to `regResults`
  an anonymous struct of `i64`s by value (in registers: `x0`–`x7` on AArch64), and of more
  `void`, with the results written through a pointer passed as its first parameter (`%out`). The
  caller passes an `alloca` of its entry block there; a tail call passes its own `%out` on.
- **Tail calls.** A flat-IR tail call is `musttail call`, then `ret` of its value, which LLVM
  guarantees is a jump when the caller's and callee's prototypes match. The functions joined by
  tail calls are a *class* (`classArity`), and every function of a class takes the class's most
  parameters, the missing ones `poison`; their results already agree, since a flat-IR tail call
  passes the caller's on. So a tail call's stack arguments are the caller's own, and no call
  pops what another pushed. (`tailcc`, which lets prototypes differ, has the callee pop its
  arguments, and Apple clang 21's AArch64 code for it corrupts the stack: `Backend/README.md`,
  Native.)
- **Addresses.** Words are real pointers (`inttoptr`/`ptrtoint`). The program's data is the
  global `@bc_data`; `Exp.data off` is its address plus `off`. A function's frame slots are one
  `alloca` of its frame's words, given back when it returns or tail-calls.
- **Host operations** compute SPEC's answer with no undefined behaviour and no poison: shift
  amounts are masked, `ctlz`/`cttz` are defined at zero, a division or `trunc` with no answer
  branches to `llvm.trap` (the flat IR tests first, SPEC §39, so no run reaches it), `rem_s` by
  `-1` divides by `1`, float-to-integer conversions are the saturating intrinsics, and `min`,
  `max` are `llvm.minimum`, `llvm.maximum`. No instruction carries `nsw`, `nuw` or fast-math flags.
-/

namespace Backend.Native
open BoCa Backend.Flat

/-- The most results a function returns by value on target `triple`: those LLVM returns in
registers there (`x0`–`x7` on AArch64; `rax`, `rdx`, `rcx`, `r8` on x86-64). A wider return is
through a pointer, since LLVM's own demotion of a wide return to `sret` is refused under
`musttail`. -/
def regResults (triple : String) : Nat :=
  if triple.startsWith "arm64" || triple.startsWith "aarch64" then 8
  else if triple.startsWith "x86_64" then 4
  else 1

structure Ctx where
  fns : Array Fn
  wide : Nat
  cnt : Bool
  /-- Each function's parameters in LLVM: the most of its tail-call class (`classArity`). -/
  arity : Array Nat

structure St where
  n : Nat := 0
  body : Array String := #[]
  allocas : Array String := #[]
  trapUsed : Bool := false

abbrev EM := ReaderT Ctx (StateT St (Except String))

/-- A word as an LLVM `i64` constant: two's complement, signed. -/
def lit (n : UInt64) : String :=
  if n.toNat < 2 ^ 63 then toString n.toNat else "-" ++ toString (2 ^ 64 - n.toNat)

def ins (s : String) : EM Unit := modify fun st => { st with body := st.body.push ("  " ++ s) }

def fresh (p : String := "t") : EM String := do
  let st ← get
  set { st with n := st.n + 1 }
  pure s!"{p}{st.n}"

/-- An instruction with a result: its name. -/
def val (rhs : String) : EM String := do
  let v ← fresh
  ins s!"%{v} = {rhs}"
  pure s!"%{v}"

def startBlock (l : String) : EM Unit :=
  modify fun st => { st with body := st.body.push (l ++ ":") }

/-- A block nothing branches to: what follows a terminator. -/
def deadBlock : EM Unit := do startBlock (← fresh "dead")

/-- Go on only when `bad` is false; at `true`, the function's trap block. -/
def trapIf (bad : String) : EM Unit := do
  modify fun st => { st with trapUsed := true }
  let ok ← fresh "ok"
  ins s!"br i1 {bad}, label %trap, label %{ok}"
  startBlock ok

def resTy (wide r : Nat) : String :=
  if r == 0 || r > wide then "void"
  else if r == 1 then "i64"
  else "{" ++ ", ".intercalate (List.replicate r "i64") ++ "}"

/-- The pointer at word `off` of the address `a`. -/
def ptrAt (a : String) (off : Nat) : EM String := do
  let a ← if off == 0 then pure a else val s!"add i64 {a}, {8 * off}"
  val s!"inttoptr i64 {a} to ptr"

/-! ### Host operations -/

def lo32 (v : String) : EM String := val s!"trunc i64 {v} to i32"
def zext32 (v : String) : EM String := val s!"zext i32 {v} to i64"
def zbit (v : String) : EM String := val s!"zext i1 {v} to i64"

/-- An integer width's LLVM type. -/
def ity : Width → EM String
  | .w32 => pure "i32"
  | .w64 => pure "i64"
  | _ => throw "native: an integer operation at a width that is not i32 or i64"

def iarg (w : Width) (v : String) : EM String := match w with
  | .w32 => lo32 v
  | _ => pure v

def ires (w : Width) (v : String) : EM String := match w with
  | .w32 => zext32 v
  | _ => pure v

def fty : FWidth → String
  | .f32 => "float"
  | .f64 => "double"

def fsuf : FWidth → String
  | .f32 => "f32"
  | .f64 => "f64"

/-- A float's bits as the float. -/
def fin (f : FWidth) (v : String) : EM String := match f with
  | .f32 => do val s!"bitcast i32 {← lo32 v} to float"
  | .f64 => val s!"bitcast i64 {v} to double"

/-- A float as its bits, an `f32`'s zero-extended. -/
def fout (f : FWidth) (v : String) : EM String := match f with
  | .f32 => do zext32 (← val s!"bitcast float {v} to i32")
  | .f64 => val s!"bitcast double {v} to i64"

def iwTy : IWidth → String
  | .i32 => "i32"
  | .i64 => "i64"

def iwRes (i : IWidth) (v : String) : EM String := match i with
  | .i32 => zext32 v
  | .i64 => pure v

def iwArg (i : IWidth) (v : String) : EM String := match i with
  | .i32 => lo32 v
  | .i64 => pure v

/-- A float constant given by the bits of a flat-IR constant. -/
def fconstOf (f : FWidth) : Exp → EM String
  | .c32 n => val s!"bitcast i32 {n.toNat} to {fty f}"
  | .c64 n => match f with
    | .f32 => val s!"bitcast i32 {n.toNat % 2 ^ 32} to float"
    | .f64 => val s!"bitcast i64 {lit n} to double"
  | _ => throw "native: a float bound that is not a constant"

def binIns : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .and => "and" | .or => "or"
  | .xor => "xor" | .shl => "shl" | .shr_s => "ashr" | .shr_u => "lshr"
  | .rotl => "fshl" | .rotr => "fshr"

def relIns : RelOp → String
  | .eq => "eq" | .ne => "ne" | .lt_s => "slt" | .lt_u => "ult" | .le_s => "sle"
  | .le_u => "ule" | .gt_s => "sgt" | .gt_u => "ugt" | .ge_s => "sge" | .ge_u => "uge"

/-- IEEE 754's comparisons: ordered, but for `ne`, which a NaN makes true (SPEC §37). -/
def frelIns : FRelOp → String
  | .eq => "oeq" | .ne => "une" | .lt => "olt" | .gt => "ogt" | .le => "ole" | .ge => "oge"

def sxIns : Sx → String
  | .s => "s"
  | .u => "u"

/-- Host operation `o` on its operands' words (SPEC §8, §37): its result's word. -/
def hostOp (o : HostOp) (vs : List String) : EM String := do
  match o, vs with
  | .bin w b, [a, c] => do
    let t ← ity w
    let bits := if w == .w32 then 31 else 63
    let a ← iarg w a
    let c ← iarg w c
    let r ← match b with
      | .shl | .shr_s | .shr_u => do
        -- The amount is taken modulo the width (SPEC §8): never LLVM's poison.
        let m ← val s!"and {t} {c}, {bits}"
        val s!"{binIns b} {t} {a}, {m}"
      | .rotl | .rotr => val s!"call {t} @llvm.{binIns b}.{t}({t} {a}, {t} {a}, {t} {c})"
      | _ => val s!"{binIns b} {t} {a}, {c}"
    ires w r
  | .div w d, [a, c] => do
    let t ← ity w
    let a ← iarg w a
    let c ← iarg w c
    let zero ← val s!"icmp eq {t} {c}, 0"
    let r ← match d with
      | .div_s => do
        let mn := if w == .w32 then "-2147483648" else "-9223372036854775808"
        let isMin ← val s!"icmp eq {t} {a}, {mn}"
        let isM1 ← val s!"icmp eq {t} {c}, -1"
        let ov ← val s!"and i1 {isMin}, {isM1}"
        trapIf (← val s!"or i1 {zero}, {ov}")
        val s!"sdiv {t} {a}, {c}"
      | .div_u => do trapIf zero; val s!"udiv {t} {a}, {c}"
      | .rem_u => do trapIf zero; val s!"urem {t} {a}, {c}"
      | .rem_s => do
        trapIf zero
        -- `MIN % -1` is `0` (SPEC §8), where LLVM's `srem` is undefined; any `x % -1` is
        -- `x % 1`.
        let isM1 ← val s!"icmp eq {t} {c}, -1"
        let c' ← val s!"select i1 {isM1}, {t} 1, {t} {c}"
        val s!"srem {t} {a}, {c'}"
    ires w r
  | .un w u, [a] => do
    let t ← ity w
    let a ← iarg w a
    let r ← match u with
      | .clz => val s!"call {t} @llvm.ctlz.{t}({t} {a}, i1 false)"
      | .ctz => val s!"call {t} @llvm.cttz.{t}({t} {a}, i1 false)"
      | .popcnt => val s!"call {t} @llvm.ctpop.{t}({t} {a})"
      | .extend8_s => do val s!"sext i8 {← val s!"trunc {t} {a} to i8"} to {t}"
      | .extend16_s => do val s!"sext i16 {← val s!"trunc {t} {a} to i16"} to {t}"
    ires w r
  | .eqz w, [a] => do
    let t ← ity w
    zbit (← val s!"icmp eq {t} {← iarg w a}, 0")
  | .rel w r, [a, c] => do
    let t ← ity w
    let a ← iarg w a
    let c ← iarg w c
    zbit (← val s!"icmp {relIns r} {t} {a}, {c}")
  | .wrap, [a] | .extend_u, [a] => val s!"and i64 {a}, 4294967295"
  | .extend_s, [a] | .extend32_s, [a] => do val s!"sext i32 {← lo32 a} to i64"
  | .wrap8, [a] | .extend8_u, [a] => val s!"and i64 {a}, 255"
  | .fbin f b, [a, c] => do
    let t := fty f
    let a ← fin f a
    let c ← fin f c
    let r ← match b with
      | .add => val s!"fadd {t} {a}, {c}"
      | .sub => val s!"fsub {t} {a}, {c}"
      | .mul => val s!"fmul {t} {a}, {c}"
      | .div => val s!"fdiv {t} {a}, {c}"
      | .min => val s!"call {t} @llvm.minimum.{fsuf f}({t} {a}, {t} {c})"
      | .max => val s!"call {t} @llvm.maximum.{fsuf f}({t} {a}, {t} {c})"
      | .copysign => val s!"call {t} @llvm.copysign.{fsuf f}({t} {a}, {t} {c})"
    fout f r
  | .fun1 f u, [a] => do
    let t := fty f
    let a ← fin f a
    let intr (n : String) : EM String := val s!"call {t} @llvm.{n}.{fsuf f}({t} {a})"
    let r ← match u with
      | .abs => intr "fabs"
      | .neg => val s!"fneg {t} {a}"
      | .sqrt => intr "sqrt"
      | .ceil => intr "ceil"
      | .floor => intr "floor"
      | .trunc => intr "trunc"
      | .nearest => intr "roundeven"
    fout f r
  | .frel f r, [a, c] => do
    let a ← fin f a
    let c ← fin f c
    zbit (← val s!"fcmp {frelIns r} {fty f} {a}, {c}")
  | .convert f i sx, [a] => do
    let a ← iwArg i a
    fout f (← val s!"{sxIns sx}itofp {iwTy i} {a} to {fty f}")
  | .trunc i f sx, [a] => do
    -- Partial: where the integer part does not fit, or at a NaN, no answer (Wasm's range,
    -- `Flat.truncRange`); in range it is the saturating conversion's.
    let x ← fin f a
    let (loOp, lo, hi) := truncRange i f sx
    let lo ← fconstOf f lo
    let hi ← fconstOf f hi
    let okLo ← val s!"fcmp {frelIns loOp} {fty f} {x}, {lo}"
    let okHi ← val s!"fcmp olt {fty f} {x}, {hi}"
    let ok ← val s!"and i1 {okLo}, {okHi}"
    trapIf (← val s!"xor i1 {ok}, true")
    iwRes i (← val s!"call {iwTy i} @llvm.fpto{sxIns sx}i.sat.{iwTy i}.{fsuf f}({fty f} {x})")
  | .trunc_sat i f sx, [a] => do
    let x ← fin f a
    iwRes i (← val s!"call {iwTy i} @llvm.fpto{sxIns sx}i.sat.{iwTy i}.{fsuf f}({fty f} {x})")
  | .demote, [a] => do fout .f32 (← val s!"fptrunc double {← fin .f64 a} to float")
  | .promote, [a] => do fout .f64 (← val s!"fpext float {← fin .f32 a} to double")
  | .reinterpret_i _, [a] | .reinterpret_f _, [a] => pure a
  | _, _ => throw "native: a host operation's arity"

/-- The intrinsics the host operations call. -/
def intrinsics : List String :=
  let ints := ["i32", "i64"]
  let fls := [("float", "f32"), ("double", "f64")]
  ints.flatMap (fun t =>
    [s!"declare {t} @llvm.fshl.{t}({t}, {t}, {t})", s!"declare {t} @llvm.fshr.{t}({t}, {t}, {t})",
     s!"declare {t} @llvm.ctlz.{t}({t}, i1)", s!"declare {t} @llvm.cttz.{t}({t}, i1)",
     s!"declare {t} @llvm.ctpop.{t}({t})"]) ++
  fls.flatMap (fun (t, s) =>
    ["minimum", "maximum", "copysign"].map (fun n => s!"declare {t} @llvm.{n}.{s}({t}, {t})") ++
    ["fabs", "sqrt", "ceil", "floor", "trunc", "roundeven"].map
      (fun n => s!"declare {t} @llvm.{n}.{s}({t})") ++
    ints.flatMap (fun i => ["s", "u"].map
      (fun x => s!"declare {i} @llvm.fpto{x}i.sat.{i}.{s}({t})"))) ++
  ["declare void @llvm.trap() cold noreturn nounwind"]

/-! ### Expressions and statements -/

def statName : Nat → String
  | 0 => "@bc_allocs"
  | 1 => "@bc_indirect"
  | _ => "@bc_copies"

/-- An expression's word, `fp` the frame's base. -/
def expr (fp : String) : Exp → EM String
  | .loc i => val s!"load i64, ptr %l{i}"
  | .c64 n => pure (lit n)
  | .c32 n => pure (toString n.toNat)
  | .load a off => do
    let p ← ptrAt (← expr fp a) off
    val s!"load i64, ptr {p}, align 8"
  | .load8 a => do
    let p ← ptrAt (← expr fp a) 0
    let b ← val s!"load i8, ptr {p}, align 1"
    val s!"zext i8 {b} to i64"
  | .load32 a => do
    let p ← ptrAt (← expr fp a) 0
    let b ← val s!"load i32, ptr {p}, align 4"
    val s!"zext i32 {b} to i64"
  | .op o args => do hostOp o (← exprs fp args)
  | .alloc w => do val s!"call i64 @bc_alloc(i64 {← expr fp w})"
  | .slot off _ => val s!"add i64 {fp}, {8 * off}"
  | .live => val "load i64, ptr @bc_live"
  | .getc fd => do val s!"call i64 @bc_getc(i64 {← expr fp fd})"
  | .getv fd a k => do
    let fd ← expr fp fd
    let a ← expr fp a
    let k ← expr fp k
    val s!"call i64 @bc_getv(i64 {fd}, i64 {a}, i64 {k})"
  | .now c => do val s!"call i64 @bc_now(i64 {← expr fp c})"
  | .stat k => val s!"load i64, ptr {statName k}"
  | .data off => do
    let p ← val s!"getelementptr i8, ptr @bc_data, i64 {off}"
    val s!"ptrtoint ptr {p} to i64"
where
  exprs (fp : String) : List Exp → EM (List String)
    | [] => pure []
    | e :: es => do
      let v ← expr fp e
      let vs ← exprs fp es
      pure (v :: vs)

/-- The arguments of a call of `g`: `vs`, then `poison` up to `g`'s class's parameters. The
call's result pointer, if any, is `out`. -/
def callArgs (g : Nat) (out : Option String) (vs : List String) : EM String := do
  let n := ((← read).arity[g]?).getD vs.length
  let pads := List.replicate (n - vs.length) "i64 poison"
  pure (", ".intercalate ((out.map ("ptr " ++ ·)).toList ++ vs.map ("i64 " ++ ·) ++ pads))

/-- Add one to a counter. -/
def bump (g : String) : EM Unit := do
  let v ← val s!"load i64, ptr {g}"
  let w ← val s!"add i64 {v}, 1"
  ins s!"store i64 {w}, ptr {g}"

/-- The callee `g`, checked against the call's arguments. -/
def callee (g nargs : Nat) : EM Fn := do
  let some gf := (← read).fns[g]? | throw s!"native: no function {g}"
  if gf.params != nargs then throw s!"native: {gf.name} takes {gf.params} arguments, not {nargs}"
  pure gf

/-- Return the words `vs` from a function of `vs.length` results. -/
def retWith (vs : List String) : EM Unit := do
  let wide := (← read).wide
  let r := vs.length
  if r == 0 then ins "ret void"
  else if r == 1 then ins s!"ret i64 {vs.headD "0"}"
  else if r > wide then
    for (v, i) in vs.zipIdx do
      let p ← val s!"getelementptr i64, ptr %out, i64 {i}"
      ins s!"store i64 {v}, ptr {p}, align 8"
    ins "ret void"
  else
    let t := resTy wide r
    let mut acc := "poison"
    for (v, i) in vs.zipIdx do
      acc ← val s!"insertvalue {t} {acc}, i64 {v}, {i}"
    ins s!"ret {t} {acc}"

/-- A statement of a function of `results` results whose frame's base is `fp`. -/
def stmt (fp : String) (results : Nat) : Stmt → EM Unit
  | .set i e => do
    let v ← expr fp e
    ins s!"store i64 {v}, ptr %l{i}"
  | .store a off v => do
    let a ← expr fp a
    let v ← expr fp v
    let p ← ptrAt a off
    ins s!"store i64 {v}, ptr {p}, align 8"
  | .store8 a v => do
    let a ← expr fp a
    let v ← expr fp v
    let p ← ptrAt a 0
    let b ← val s!"trunc i64 {v} to i8"
    ins s!"store i8 {b}, ptr {p}, align 1"
  | .store32 a v => do
    let a ← expr fp a
    let v ← expr fp v
    let p ← ptrAt a 0
    let b ← val s!"trunc i64 {v} to i32"
    ins s!"store i32 {b}, ptr {p}, align 4"
  | .free a => do ins s!"call void @bc_free(i64 {← expr fp a})"
  | .unslot _ => pure ()
  | .out b => do ins s!"call void @bc_putc(i64 1, i64 {← expr fp b})"
  | .putc fd b => do
    let fd ← expr fp fd
    let b ← expr fp b
    ins s!"call void @bc_putc(i64 {fd}, i64 {b})"
  | .putv fd a k => do
    let fd ← expr fp fd
    let a ← expr fp a
    let k ← expr fp k
    ins s!"call void @bc_putv(i64 {fd}, i64 {a}, i64 {k})"
  | .sleep c ns => do
    let c ← expr fp c
    let ns ← expr fp ns
    ins s!"call void @bc_sleep(i64 {c}, i64 {ns})"
  | .ite c t e => do
    let v ← expr fp c
    let b ← val s!"icmp ne i64 {v}, 0"
    let lt ← fresh "then"
    let le ← fresh "else"
    let lj ← fresh "join"
    ins s!"br i1 {b}, label %{lt}, label %{le}"
    startBlock lt
    block fp results t
    ins s!"br label %{lj}"
    startBlock le
    block fp results e
    ins s!"br label %{lj}"
    startBlock lj
  | .switch e cs d => do
    let v ← expr fp e
    let lj ← fresh "join"
    let ld ← fresh "default"
    let mut ls : Array String := #[]
    for _ in cs do ls := ls.push (← fresh "case")
    let arms := String.join (ls.toList.zipIdx.map fun (l, i) => s!" i64 {i}, label %{l}")
    ins s!"switch i64 {v}, label %{ld} [{arms} ]"
    cases fp results lj ls.toList cs
    startBlock ld
    block fp results d
    ins s!"br label %{lj}"
    startBlock lj
  | .call ds g args => do
    let vs ← expr.exprs fp args
    let gf ← callee g vs.length
    if gf.results != ds.length then
      throw s!"native: {gf.name} answers {gf.results} results, not {ds.length}"
    let wide := (← read).wide
    let r := ds.length
    let t := resTy wide r
    if r == 0 then ins s!"call void @f{g}({← callArgs g none vs})"
    else if r > wide then
      let buf ← fresh "buf"
      modify fun st => { st with allocas := st.allocas.push s!"  %{buf} = alloca [{r} x i64], align 8" }
      ins s!"call void @f{g}({← callArgs g (some s!"%{buf}") vs})"
      for (dst, i) in ds.zipIdx do
        let p ← val s!"getelementptr i64, ptr %{buf}, i64 {i}"
        let w ← val s!"load i64, ptr {p}, align 8"
        ins s!"store i64 {w}, ptr %l{dst}"
    else
      let rv ← val s!"call {t} @f{g}({← callArgs g none vs})"
      if r == 1 then ins s!"store i64 {rv}, ptr %l{ds.headD 0}"
      else
        for (dst, i) in ds.zipIdx do
          let w ← val s!"extractvalue {t} {rv}, {i}"
          ins s!"store i64 {w}, ptr %l{dst}"
  | .ret es => do
    let vs ← expr.exprs fp es
    if vs.length != results then throw s!"native: a return of {vs.length} results, not {results}"
    retWith vs
    deadBlock
  | .tailCall g args => do
    let vs ← expr.exprs fp args
    let gf ← callee g vs.length
    if gf.results != results then
      throw s!"native: a tail call of {gf.name}, of {gf.results} results, from a function of {results}"
    let wide := (← read).wide
    let t := resTy wide results
    if results == 0 then
      ins s!"musttail call void @f{g}({← callArgs g none vs})"
      ins "ret void"
    else if results > wide then
      ins s!"musttail call void @f{g}({← callArgs g (some "%out") vs})"
      ins "ret void"
    else
      let rv ← val s!"musttail call {t} @f{g}({← callArgs g none vs})"
      ins s!"ret {t} {rv}"
    deadBlock
  | .tick => do if (← read).cnt then bump "@bc_indirect"
  | .tickCopy => do if (← read).cnt then bump "@bc_copies"
  | .tickBound => pure ()
  | .status c => do ins s!"call void @bc_status(i64 {← expr fp c})"
  | .trap => do
    ins "call void @llvm.trap()"
    ins "unreachable"
    deadBlock
where
  block (fp : String) (results : Nat) : List Stmt → EM Unit
    | [] => pure ()
    | s :: ss => do stmt fp results s; block fp results ss
  cases (fp : String) (results : Nat) (lj : String) : List String → List (List Stmt) → EM Unit
    | l :: ls, c :: cs => do
      startBlock l
      block fp results c
      ins s!"br label %{lj}"
      cases fp results lj ls cs
    | _, _ => pure ()

/-- Function `k`'s definition. -/
def lowerFn (k : Nat) (f : Fn) : EM (List String) := do
  modify fun st => { st with body := #[], allocas := #[], trapUsed := false }
  let wide := (← read).wide
  let fp := if f.frame == 0 then "0" else "%fp"
  stmt.block fp f.results f.body
  ins "unreachable"
  let st ← get
  let n := ((← read).arity[k]?).getD f.params
  let ps := (if f.results > wide then ["ptr %out"] else []) ++ (List.range n).map (s!"i64 %a{·}")
  let locals := (List.range (f.params + f.locals)).flatMap fun i =>
    [s!"  %l{i} = alloca i64, align 8",
     s!"  store i64 {if i < f.params then s!"%a{i}" else "0"}, ptr %l{i}"]
  let frame := if f.frame == 0 then [] else
    [s!"  %frame = alloca [{f.frame} x i64], align 8", "  %fp = ptrtoint ptr %frame to i64"]
  let trap := if st.trapUsed then ["trap:", "  call void @llvm.trap()", "  unreachable"] else []
  pure ([s!"; {f.name}",
    s!"define internal {resTy wide f.results} @f{k}({", ".intercalate ps}) nounwind \{",
    "entry:"] ++ locals ++ frame ++ st.allocas.toList ++ ["  br label %body", "body:"] ++
    st.body.toList ++ trap ++ ["}", ""])

/-! ### Tail-call classes -/

/-- The functions a statement tail-calls. -/
def tailCallees : Stmt → List Nat
  | .tailCall g _ => [g]
  | .ite _ t e => blockCallees t ++ blockCallees e
  | .switch _ cs d => casesCallees cs ++ blockCallees d
  | _ => []
where
  blockCallees : List Stmt → List Nat
    | [] => []
    | s :: ss => tailCallees s ++ blockCallees ss
  casesCallees : List (List Stmt) → List Nat
    | [] => []
    | c :: cs => blockCallees c ++ casesCallees cs

/-- The root of `i` in the union-find `parent`. -/
def findRoot (parent : Array Nat) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [0:parent.size] do
    let q := parent.getD j j
    if q == j then return j
    j := q
  return j

/-- Each function's parameters in LLVM: the most of any function of its *tail-call class*, the
functions joined by tail calls (in either direction). A tail call is then between functions of one
prototype, which `musttail` requires under the C convention, and the callee's stack arguments
are the caller's own. -/
def classArity (fns : Array Fn) : Array Nat := Id.run do
  let mut parent : Array Nat := Array.range fns.size
  for (f, k) in fns.toList.zipIdx do
    for g in tailCallees.blockCallees f.body do
      let a := findRoot parent k
      let b := findRoot parent g
      if a != b then parent := parent.set! a b
  let mut most : Array Nat := Array.replicate fns.size 0
  for (f, k) in fns.toList.zipIdx do
    let r := findRoot parent k
    most := most.set! r (max (most.getD r 0) f.params)
  pure ((Array.range fns.size).map fun k => most.getD (findRoot parent k) 0)

/-- The data's bytes as an LLVM string constant. -/
def dataConst (bs : Array UInt8) : String :=
  let hex (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (55 + d)
  "c\"" ++ String.join (bs.toList.map fun b =>
    "\\" ++ (hex (b.toNat / 16)).toString ++ (hex (b.toNat % 16)).toString) ++ "\""

/-- The runtime's declarations (`Backend/Native/Runtime.lean`). -/
def runtimeDecls : List String := [
  "@bc_live = external global i64",
  "@bc_allocs = external global i64",
  "@bc_indirect = external global i64",
  "@bc_copies = external global i64",
  "declare void @bc_init(ptr, i64)",
  "declare i64 @bc_alloc(i64)",
  "declare void @bc_free(i64)",
  "declare void @bc_putc(i64, i64)",
  "declare void @bc_putv(i64, i64, i64)",
  "declare i64 @bc_getc(i64)",
  "declare i64 @bc_getv(i64, i64, i64)",
  "declare i64 @bc_now(i64)",
  "declare void @bc_sleep(i64, i64)",
  "declare void @bc_status(i64)"]

/-- The program as LLVM IR text for target `triple`; with `cnt`, every dispatched call and
counted copy adds one to the runtime's count. `bc_entry` (the C calling convention) gives the
runtime the data's bounds and runs the entry. -/
def printProg (p : Prog) (triple : String) (cnt : Bool := false) : Except String String := do
  let some e := p.fns[p.entry]? | throw "native: no entry function"
  if e.params != 0 || e.results != 0 then throw "native: the entry takes or answers words"
  let ctx : Ctx := { fns := p.fns, wide := regResults triple, cnt, arity := classArity p.fns }
  let go : EM (List String) := do
    let mut ls : List String := []
    for (f, k) in p.fns.toList.zipIdx do
      ls := ls ++ (← lowerFn k f)
    pure ls
  let (fns, _) ← (go.run ctx).run {}
  let L := p.data.size
  let data := if L == 0 then "@bc_data = internal global [8 x i8] zeroinitializer, align 8"
    else s!"@bc_data = internal global [{L} x i8] {dataConst p.data}, align 8"
  let entry := ["define void @bc_entry() nounwind {",
    s!"  call void @bc_init(ptr @bc_data, i64 {L})",
    s!"  call void @f{p.entry}({", ".intercalate (List.replicate (ctx.arity.getD p.entry 0) "i64 poison")})",
    "  ret void", "}"]
  let lines := ["; borrow-core: native code from the flat IR (Backend/Native/Lower.lean)", data] ++
    runtimeDecls ++ intrinsics ++ [""] ++ fns ++ entry
  pure ("\n".intercalate lines ++ "\n")

end Backend.Native
