# Frontend: the core syntax

A lexer, parser and printer for the textual core language of `docs/syntax-core.md` (draft 1,
with §8a integers). Checking and erasure to `CDerives` derivations are not here yet; the AST
keeps written names, and resolving them is the checker's work (syntax-core §1, §3, §6.3).

    lake exe bcc parse <file>   parse, then print, re-parse and compare the ASTs up to spans
    lake exe bcc print <file>   print in the canonical ASCII spelling
    scripts/parse-corpus.sh     every corpus/*.bc parses and round-trips; every
                                corpus/fail/*.bc fails with the message on its `-- expect:` line

| file | contents |
|---|---|
| `Syntax.lean` | the AST: `Life`, `VTy`/`CTy`/`Shape`, `Const`, `Val`/`Comp`, `Decl`, `Program`; every node has a `Span`; `strip` erases spans |
| `Lexer.lean` | tokens of §2, with line:column spans; Unicode spellings read as their ASCII tokens |
| `Consts.lean` | bracket signatures of the constants (§8, §8a, §9) and host-operation names, with `Const.ofArgs_toArgs` and `hostOpOfName_name` |
| `Parser.lean` | recursive descent for §3–§6 and §10; types parsed to `RTy` then sorted into `VTy`/`CTy` |
| `Print.lean` | the printer, parenthesizing by the precedence levels of §4 and §6.5 |
| `Tests.lean` | precedence cases and round trips checked by the kernel (`decide +kernel`) |
| `Main.lean` | `bcc` |

`Frontend/` imports only `Support.Syntax.Integers` (for `Width`, `IntLit`, `HostOp`) and
itself. `scripts/check-hygiene.sh` scans it and checks that it imports nothing outside the
library.

## Termination without `partial`

The lexer recurses on fuel equal to the input length plus one; each step consumes at least one
character. Every parsing function takes a fuel argument and recurses structurally on it,
passing `fuel - 1` to each callee and to the next iteration of each loop (suffixes, lists,
declarations). Fuel therefore bounds the depth of the call tree; along any chain of calls only a
bounded number of calls happen before a token is consumed, and the entry point supplies
`16 × (tokens + 1)`. Running out is reported as an error ("expression nested too deeply"), not
assumed impossible. Because the recursion is structural, the kernel can evaluate the parser,
which is how `Tests.lean` checks its cases.

## Round trip

`(parse (print t)).strip = t.strip`. `bcc parse` checks it on every file it accepts, so the
corpus runner checks it on the whole corpus. `Tests.lean` checks it on small values,
computations, types and one program by `decide +kernel`. It is not proved for all ASTs.

## Choices beyond draft 1

Where draft 1 is silent or ambiguous about parsing, the parser does the following.

1. **`name[…]` vs `V [@]`.** A `[` written directly after a lower-case name, with no space,
   opens a `def`'s type arguments (`take[Nat]`). Anywhere else, `[` after a value or
   computation is lifetime instantiation (`(unbang f) ['y]`, `f ['y]`). Constants take their
   brackets with or without a space.
2. **Prefix type formers take a prefix expression**, not only an atom: `!U (…)` is `!(U (…))`
   and `ref imm 'a A` is `ref (imm 'a A)`. `imm 'a Nat * Nat` is still `(imm 'a Nat) * Nat`
   (§4). The lifetime argument of `imm`/`mut`/`box`/`view`/`fam` is a lifetime atom.
3. **Binders on the right of an infix type operator** extend to the right without parentheses:
   `A * mu X. B` is `A * (mu X. B)`. The printer parenthesizes them anyway.
4. **`-o` and `=>` share one level** and associate to the right; the sort pass rejects
   ill-sorted mixtures.
5. **Sorts are checked in a pass after parsing** (§4: "Sorts are checked after parsing"):
   `F A * B` is reported at the parse stage as "`F A` is a computation type, but a value type
   is expected here". A `type` abbreviation is a value type.
6. **`stream` and `str`** are both accepted for the stream former (§4 grammar vs its prefix
   list); the printer writes `stream`. Terms use `stream_in`/`stream_out` (§6.2).
7. **Tuples are pairs.** `(V, W, Z)` is rejected; write `(V, (W, Z))` (§1, no sugar).
8. **`case` arms come in the order `inl`, `inr`**, without a leading `|`.
9. **Binding forms as operands.** The value of `let … = V;`, the scrutinee of `case V {`, the
   computation of `x <- M;` and the contents of parentheses, pair components and `<M, N>`
   components are full expressions, so a binding form may appear there (it ends at the `;`,
   `{`, `,`, `)` or `>`). The operand of a prefix keyword (`return`, `inl`, `unbang`, `run`,
   …) and an argument in a spine must be parenthesized if it is a binding form (§6.5).
10. **`.1` / `.2`** are the token `.` followed by the integer `1` or `2`; whitespace may
    separate them (`force f s .1`).
11. **`<>`** is the tokens `<` `>`; whitespace may separate them.
12. **Reserved words.** All keywords of types, terms and declarations, every constant and
    derived-form keyword (`alloc`, `free`, `copy`, `swap`, `host`, …), `val`, `block`, `leaf`,
    `node`, `str`, and `main` are reserved as lower-case names; `U`, `F`, `Fun` as upper-case
    names. `main` has to be reserved: a `def` body ends where the next declaration begins.
13. **Names are not resolved.** A lower-case name is `Val.var` whether it is a variable or a
    `def`; an upper-case name in a type is `VTy.name` whether it is `mu`-bound, an
    abbreviation or a `def` parameter. In a fold's `F` argument, `X` is such a name.
14. **Declarations.** At most one `main`; a library file may have none. Declaration order is
    not checked by the parser (the checker enforces "earlier" for `type`, `shape` and `def`).
    `def` parameters are upper-case names.
15. **Integer literals** are decimal or `0x`/`0X` hexadecimal with no sign and no separators,
    and `i32[n]`/`i64[n]` is stored as `IntLit` reduced modulo 2^32 / 2^64 at parse time. The
    types `1` and `0` are the integer tokens `1` and `0`.
16. **Host operation names** are the Wasm instruction name with the width as a suffix
    (`add32`, `div_s32`, `lt_u64`, `eqz64`, `extend8_s32`), and `wrap`, `extend_s`,
    `extend_u`, `extend32_s` bare.
17. **Lexical details.** `-o` is one token even before a letter; `--` starts a comment
    everywhere; `⊓Δ` is `dom` and `⊓` alone is `/\`; `Imm̲` (with U+0332) is `view`. Only the
    Unicode spellings of the §2 table are accepted (no `→`, `⇒`).
