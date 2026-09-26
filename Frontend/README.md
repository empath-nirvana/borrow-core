# Frontend: the core syntax

A lexer, parser, printer and type checker for the textual core language of
`docs/syntax-core.md` (draft 1, with §8a integers). The checker elaborates a program to a BoLo
`Expr` together with a `CDerives` derivation of it (`Frontend/Check/`, below).

    lake exe bcc parse <file>   parse, then print, re-parse and compare the ASTs up to spans
    lake exe bcc print <file>   print in the canonical ASCII spelling
    lake exe bcc check <file>   type-check: print each declaration's type, or the first error
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

## The checker (`Frontend/Check/`)

`CDerives` (`Core/Fundamental.lean`) is the specification, and the checker is derived from it:
every step applies one `CDerives` constructor, so what the checker returns is a derivation.

| file | contents |
|---|---|
| `Check/Decide.lean` | `DecidableEq` on `VTy`, `CTy`, `Expr`; a `Bool` decider for each side condition, with its soundness lemma |
| `Check/Fam.lean` | linearity: masks `u` (used), `w` (absorbable) and a derivation at every liveness `L` between them |
| `Check/Elab.lean` | surface types, lifetimes and shapes to `Core`'s, and a printer back |
| `Check/Rules.lean` | one builder per `CDerives` constructor |
| `Check/Steps.lean` | the environment, messages, and the steps shared by the checker's cases |
| `Check/Consts.lean` | constants and derived forms |
| `Check/Checker.lean` | the bidirectional checker, `synV`/`chkV`/`synC`/`chkC` |
| `Check/Program.lean` | declarations, `main`, and the soundness theorems |

**Soundness.** `checkProgram p = .ok r` with `r.main = some c` gives
`CDerives LifeCtx.empty c.ctx c.e (.comp c.C)` (`checkProgram_sound`): `c.e` is `main`'s
erasure, `c.ctx` its externs, all live. `checked_sem` is the Fundamental Property at it
(`SemC ∅ c.ctx c.e c.C`, at every host) and `checked_runs` is adequacy for a closed
`main : F 1`. The derivation is a field of the result, built by the rule builders from the
checked premises; there is nothing else to prove.

**Linearity** (syntax-core §7, §11). Each subterm is checked against the types `T` of every slot
in scope and reports which slots it uses (`u`) and which live slots it can take without using
(`w`: persistent slots, dropped at leaves; every slot, under `<>` and `absurd`). Its result is a
derivation at every liveness `L` with `u ⊆ L ⊆ u ∪ w`. The enclosing rule picks `L`: a split
gives each side its uses and routes an unused live slot to a side that absorbs it; a `case` or
`<,>` needs one `L` for both parts. This is the input/output reading with ⊤-slack, with the
output chosen by the enclosing rule instead of threaded. Premises on every live slot
(`CtxOutlives`, `Persistent`, `allI`'s `hΓx`) restrict what may be absorbed.

**Constants and derived forms** (syntax-core §8, §8a, §9) are one constructor or one Lean theorem
each (`Check/Consts.lean`): `alloc`…`withswap`, `fold_imm`/`fold_own`/`fold_reuse` with the shape
decoded by §5's `dec`, `fixd`, `unfold_s`, `i32[n]`/`i64[n]`, `host[op]`, and `alloc_s`,
`free_s`, `withbor_s_*`, `withbor_f2_*` (`d_allocS`, `d_freeS`, `withborS{M,I}_wf`,
`withbor{M,I}2_wf`) and `shorten_*` (`shortenE_wf`). Binder arguments are numbered `Δ.freshVar`
(§3); `withbor_f2`'s internal `'a`, `'b` are `Δ.freshVar` and `Δ.freshVar + 1` (§9).
