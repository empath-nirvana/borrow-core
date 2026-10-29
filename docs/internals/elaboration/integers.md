# Integers and host operations

The surface's operators at the numbers are these operations ([Values, functions and
numbers](../../../book/src/guide/basics.md#numbers)); this chapter writes them as the core does. `i32` and `i64`
are WebAssembly's integers. They are persistent: an integer variable can be used
any number of times.

## Literals

`i32[n]` and `i64[n]` are literals. `n` is decimal or `0x` hexadecimal, with no sign, and is read
modulo 2³² or 2⁶⁴, so `i32[0xFFFFFFFF]` is −1 as a signed number. Values print unsigned.

## Operations

`host[op]` is one of WebAssembly's integer instructions, with the width as a suffix: `add32`,
`div_s64`, `lt_u32`. Its type is `!(A => B)`, so it is called as `(unbang host[op]) V`. A common
idiom is a `def` for the operations a program uses often:

```text
def plus : i32 * i32 => i32 = unbang host[add32]
```

At each width `w` (`32` or `64`):

| group | operations | type at `i32` |
|---|---|---|
| binary | `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `shr_s`, `shr_u`, `rotl`, `rotr` | `i32 * i32 => i32` |
| partial | `div_s`, `div_u`, `rem_s`, `rem_u` | `i32 * i32 => i32 + 1` |
| unary | `clz`, `ctz`, `popcnt`, `extend8_s`, `extend16_s` | `i32 => i32` |
| tests | `eqz` | `i32 => 1 + 1` |
| | `eq`, `ne`, `lt_s`, `lt_u`, `le_s`, `le_u`, `gt_s`, `gt_u`, `ge_s`, `ge_u` | `i32 * i32 => 1 + 1` |

and the conversions `wrap` (`i64 => i32`), `extend_s` and `extend_u` (`i32 => i64`), and
`extend32_s` (`i64 => i64`), written without a suffix.

- **Tests** return `1 + 1`, with `inr ()` for true and `inl ()` for false.
- **Partial operations** return `inl n`, or `inr ()` where WebAssembly would trap: a zero divisor,
  or `INT_MIN / -1` for `div_s`. A trap would abandon the program's linear resources, so the
  program decides what to do instead.

```bc
def plus : i32 * i32 => i32 = unbang host[add32]

main : F i32 =
  x <- return i32[40];
  y <- return i32[0x2];
  s <- return (plus (x, y));
  w <- return ((unbang host[wrap]) i64[4294967301]);
  case (unbang host[lt_s32]) (s, i32[100]) {
    inl u -> return w
  | inr u ->
      d <- return ((unbang host[div_s32]) (s, i32[7]));
      case d { inl q -> return q | inr t -> return i32[0xFFFFFFFF] }
  }
-- answer: i32[6]
```

`42 < 100` is true, so the `inr` arm runs and returns `42 / 7`.

The surface's `a / b` and `a % b` are these partial operations followed by a test: `inr ()`
raises `Fail[DivError]` ([Errors](../../../book/src/guide/errors.md#division), SPEC §39), and a division by a
nonzero literal is the operation alone.

## Bytes and floats

`u8` is the byte: the literal `u8[n]` (read modulo 2⁸), and `b'c'`, which the lexer reads as
`u8[n]`. Its operations are its conversions, `host[wrap8]` (`i32 => u8`, the low 8 bits) and
`host[extend8_u]` (`u8 => i32`); a surface operator at `u8` works at `i32` and narrows back.

`f32` and `f64` are IEEE 754 floats, persistent like the integers. The core literal is the bit
pattern, `f64[4617315517961601024]` for `5.0`, and the operations are WebAssembly's float
instructions, named with `_` for `.`: `host[f64_add]`, `host[f32_sqrt]`, `host[f64_lt]`,
`host[f64_convert_i32_s]`, `host[i32_trunc_f64_s]`. A truncation to an integer that WebAssembly
would trap on returns `inr ()`; the `trunc_sat` forms saturate instead. Every NaN an arithmetic
operation produces is the canonical positive NaN, at every engine, so every program prints one
output (SPEC §37).

## Nothing about arithmetic is assumed

The proofs never look at what an operation computes. The machine applies operations through a
*host*, and every theorem holds for every host. The Lean interpreter and the compiled program use
WebAssembly's definitions; that the two agree is tested (`corpus/int-ops.bc` covers every group
at both widths), not proved.
