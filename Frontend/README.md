# Frontend: the core syntax

A lexer, parser, printer and type checker for the textual core language of
`docs/syntax-core.md` (draft 1, with §8a integers and §8b arrays). The checker elaborates a program to a BoLo
`Expr` together with a `CDerives` derivation of it (`Frontend/Check/`, below).

    lake exe bcc parse <file>   parse, then print, re-parse and compare the ASTs up to spans
    lake exe bcc print <file>   print in the canonical ASCII spelling
    lake exe bcc check <file>   type-check: print each declaration's type, or the first error
    lake exe bcc compile|run|interp …   the backend (`Backend/README.md`)
    scripts/parse-corpus.sh     every corpus/*.bc parses and round-trips; every
                                corpus/fail/*.bc fails with the message on its `-- expect:` line

| file | contents |
|---|---|
| `Syntax.lean` | the AST: `Life`, `VTy`/`CTy`/`Shape`, `Const`, `Val`/`Comp`, `Decl`, `Program`; every node has a `Span`; `strip` erases spans |
| `Lexer.lean` | tokens of §2, with line:column spans; Unicode spellings read as their ASCII tokens |
| `Consts.lean` | bracket signatures of the constants (§8, §8a, §8b, §9) and host-operation names, with `Const.ofArgs_toArgs` and `hostOpOfName_name` |
| `Parser.lean` | recursive descent for §3–§6 and §10; types parsed to `RTy` then sorted into `VTy`/`CTy` |
| `Print.lean` | the printer, parenthesizing by the precedence levels of §4 and §6.5 |
| `Tests.lean` | precedence cases and round trips checked by the kernel (`decide +kernel`) |
| `Main.lean` | `bcc` |

The lexer, parser and printer import only `Support.Syntax.Integers` (for `Width`, `IntLit`,
`HostOp`) and each other; the checker imports `Core`, and `Main.lean` the backend.
`scripts/check-hygiene.sh` scans `Frontend/` and checks that it imports nothing outside the
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
   list); the printer writes `stream`. `delay_in`/`stream_in` and `delay_out`/`stream_out` are
   read as `nu_in` and `nu_out`, which the printer writes (§6.2).
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
12. **Reserved words.** All keywords of types, terms and declarations (including `linear`,
    SPEC §12), every constant and
    derived-form keyword (`alloc`, `free`, `copy`, `swap`, `host`, …), `val`, `block`, `leaf`,
    `node`, `str`, and `main` are reserved as lower-case names; `U`, `F`, `Fun` as upper-case
    names. `main` has to be reserved: a `def` body ends where the next declaration begins.
13. **Names are not resolved.** A lower-case name is `Val.var` whether it is a variable or a
    `def`; an upper-case name in a type is `VTy.name` whether it is `mu`-bound, an
    abbreviation or a `def` parameter. In a fold's `F` argument, `X` is such a name. Before
    the sugar is elaborated, `Frontend/Elab/Hygiene.lean` renames every local named as a
    declaration (other than the capabilities `stdin`, `stdout`, `stderr`) and every control
    handler's parameter to a fresh `hy{n}_{x}`, so code the elaboration moves between scopes
    neither captures a user's variable nor is captured by one (#481).
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
18. **Effects (SPEC §19).** A row is written after `F`: `F[3.0 aff A ~> B, 3.1 lin 1 ~> i32] T`,
    each entry the operation `i` of the name `n` (`n.i`), its qualifier and `A ~> B`; `F[] T` is
    read as `F T`, and the printer writes an empty row so. `lin`, `aff` and `unr` are read as
    qualifiers inside a row only, and are not reserved; `~>` is a token. The computations are
    `perform[n.i] V` and `abort[n.i] V` (prefix forms, operands as `return`'s),
    `handle_with[n](hr, hc) M` (`M` an operand: a binding form is parenthesized) and the binding
    `x <- M unwind (D); N` (also `x : A <- M unwind (D); N`). The unwinding borrows take the
    callback's row as their last bracket argument, `[n.i q A ~> B, …]`: `withbor1u['x, A, B, [ROW]]`,
    `withbor2u['x, @b, A, B, [ROW]]`, `withbor3u[@a, 'x, A, B, [ROW]]`,
    `withloadu[@a, 'x, A, B, [ROW]]`, `slice_borrow_mut_u['x, @b, A, B, [ROW]]`,
    `slice_borrow_imm_u['x, @b, A, B, [ROW]]`. `perform`, `abort`, `handle_with`, `unwind` and the
    six constants are reserved (`handle` is not: the corpus names a `def` so).
19. **Computation parameters and `|>` (SPEC §33).** `(A => B with E₁, E₂[T])`, in parentheses,
    is a function type with a provided row (`VTy.rowed`, its row the effect instances applied to
    the empty name); the printer always parenthesizes it. `|>` is the operator of the lowest precedence, below `||`,
    associating to the left; its right operand, the stage, is a prefix expression (a spine). `e |>
    s` is the node `VSugar.pipe` applied to the pair of `e` and `s`, printed in parentheses, and
    `Frontend/Elab/Effects.lean` elaborates it by the stage.
20. **`poly` (SPEC §36).** `poly f[T]<'a, …>(x: A, …) -> B` with no `=` declares a family;
    `poly f[P, …]<'h, …> at H = S` a case, its body a statement sequence as a `fn`'s; `poly (+) at
    H = S` a case of an operator's family (`(+)` read as `op_add`, …). `at` is a word here, not a
    keyword, so it stays a name elsewhere. The printer writes `poly def f[T] : A = V` and `poly def
    f[P, …]<'h, …> at H = V`, which the parser reads back. A load `borrow imm *g { … }` keeps `*g`
    as its place, which hands nothing back (`Val.rebinds` is `_`).
21. **Names of handlers and of a row's entries (SPEC §38).** `with n = h(…) { S }` names the
    handler (`VSugar.handle`'s last field); `n.op` with no space around the `.` is
    `VSugar.named n op`, applied to the operation's argument; a written row's entry may be named,
    `with src: E`, the names kept beside the entries (`Mark.row`'s third field). The printer writes
    each back as it is read.

## The checker (`Frontend/Check/`)

`CDerives` (`Core/Fundamental.lean`) is the specification, and the checker is derived from it:
every step applies one `CDerives` constructor (or one Core theorem concluding a `CDerives`
judgment, for the derived forms of syntax-core §9), so what the checker returns is a derivation.

    lake exe bcc check <file>     print each declaration's type, or the first error
    scripts/check-corpus.sh       corpus/*.bc check (except `-- check: parse-only`);
                                  corpus/reject/*.bc are rejected with their `-- expect:` message

| file | contents |
|---|---|
| `Check/Decide.lean` | `DecidableEq` on `VTy` and `CTy` (on `Expr`, `Core/LetCopy.lean`'s); a `Bool` decider for each side condition, with its soundness lemma |
| `Check/Fam.lean` | linearity: masks of used and absorbable slots, and a derivation at every liveness between them |
| `Check/Elab.lean` | surface lifetimes, types and shapes to `Core`'s; a printer back |
| `Check/Tied.lean` | tied derivations (SPEC §19, decision R): `TiedAt`, and the checker's derivations `TiedDer p s` (SPEC §29: of `CDerivesP`, and tied when the list `p` of relaxed rules used is empty), one lemma per rule the builders apply, and the program's effect context (`effCtxOf`, `sigsOkB`) |
| `Check/Pin.lean` | R1, the relaxed lend (SPEC §29): `withbor2r`'s builder `rLendR`, and the deciders `Row.resumeOB`, `noThunkB` |
| `Check/Rules.lean` | one builder per `CDerives` constructor, and `rDrop` (SPEC §12) |
| `Check/Steps.lean` | the environment, messages, the deciders of fold shapes and destructors, the drops, and the steps shared by the checker's cases |
| `Check/Consts.lean` | constants (§8, §8a, §8b) and derived forms (§9) |
| `Check/Checker.lean` | the bidirectional checker, `synV`/`chkV`/`synC`/`chkC` |
| `Check/TExpr.lean` | the typed term (generated by `scripts/gen-pin.py`): one node per rule application, its rule's arguments (types, rows, lifetimes, qualifiers), its judgment, its source, a split's use mask; `erase`, the term the rule concludes with |
| `Check/TDerives.lean` | `TDerivesAt`/`TDerivesP` (generated): `CDerivesAt`/`CDerivesP` over the typed term, and their projections to the erasure |
| `Check/TTied.lean` | `TTied`: the tied typed derivation the checker returns, one builder per rule, and its projection to `TiedDer` at the erasure |
| `Check/Copies.lean` | the check `checkProgram` runs last, on the typed terms: a use that the compiled program copies deep (a persistent variable of recursive data, used again later) must be written `clone(x)` (`implicitCopy`, SPEC §10, decision 39) |
| `Check/Program.lean` | declarations, `main` (its typed term `t`, `Checked.e := t.erase`), and the soundness theorems |
| `Check/CrossCheck.lean` | erasures compared with `Core/`'s hand-written terms, by kernel evaluation |
| `Sugar.lean` | the sugar, elaborated before checking and decided by types (`Elab/Meta.lean`): draft 0's surface forms that need types (`Val.sugar`: literals, string literals, operators, `alloc(e)`, `clone(x)`, blocks and closures, borrow blocks, on buffers and literals too, and a buffer's `filler[A]`; `surfDecl`, decision 37); ambient capabilities in `main`, lends `&mut x` and `&x` (`lendCall`, decision 38), `for` (SPEC §11); divergence inferred, `total`/`div` markers, direct-style div calls as delay binds, specialization at a callback's type (SPEC §14) |
| `Elab/Respan.lean` | `respan`: generated syntax at the span of the sugar that produced it |
| `Elab/Meta.lean` | typing contexts for the sugar (`TCx`: the program as written, typed by inference), loops and iterators read off types, and metavariables that annotate bindings of injections (`fillProgram`) |
| `Elab/Match.lean` | first-order matching of a type against a pattern whose placeholders are type parameters (generic calls, decision 45) |
| `Elab/Instances.lean` | the type arguments of each operation's instance and of each template call, typed at the declaration's own types before effects are resolved (SPEC §38); the integer divisions that can fail, at their operands' width (SPEC §39) |
| `Elab/Divisions.lean` | each division that can fail written as the checked division and a `raise` of `Fail[DivError]`, before rows are inferred (SPEC §39) |
| `Elab/Effects.lean` | effects and handlers (SPEC §18–§21, §30–§34, §38): every operation resolved to the handler of its instance, rows, copies, handler sites |
| `Elab/Tir.lean` | the sugar's inference nodes: one node per node of a term, with its type, binders (identity, type, class) and effect (`docs/typed-elaboration.md` §1.1) |
| `Elab/Infer.lean` | the sugar's inference (`TCx.tyV`): a term's type, bidirectionally, in the environment the checker uses; the checker's synthesis answers for the core's substitutions |
| `Elab/Pipeline.lean` | the pipeline `checkProgram` runs: the sugar, and errors in generated code named by their sugar (`renderError`) |
| `Elab/LoopLend.lean` | borrow scopes over loops, per observation (SPEC §14): a borrow block whose body loops, `let r = &x` over a loop, and a div function over a borrow, rewritten so that each step borrows the owner again (`hook`, `lentDef`) |
| `Check/Externs.lean` | the standard externs with their roles, models and assurance levels; the `run_io` wrapper; `IORun` (SPEC §11) |

### Soundness

    theorem checkProgram_soundP {p : Program} {r : Report} {c : Checked}
        (h : checkProgram p = .ok r) (hc : r.main = some c) :
        CDerivesP LifeCtx.empty c.ctx c.t.erase (.comp c.C)

    theorem checkProgram_sound {p : Program} {r : Report} {c : Checked}
        (h : checkProgram p = .ok r) (hc : r.main = some c) (hp : c.pins = []) :
        CDerives LifeCtx.empty c.ctx c.t.erase (.comp c.C)

    theorem checkProgram_tiedAt {p : Program} {r : Report} {c : Checked}
        (h : checkProgram p = .ok r) (hc : r.main = some c) (hp : c.pins = []) :
        CDerivesAt c.Ξ LifeCtx.empty c.ctx c.t.erase (.comp c.C) ∧ c.Ξ.NoUnrExn

`c.t` is `main`'s typed term (`Check/TExpr.lean`): one node per rule application, with its rule's
arguments, its judgment and its source. `c.e := c.t.erase` is `main`'s erasure, the term the
backend compiles; `checkProgram_typed` gives the typed derivation itself (`TDerivesP`, and
`TDerivesAt` with `checkProgram_typedAt`), which projects to the ones above. `c.C` is `main`'s type
and `c.ctx` its externs, the last declared at index 0, all live. `c.pins` lists the relaxed rules (SPEC §29) the derivation uses, and `bcc check` prints
it: `assurance: unconditional` when it is empty, which is `hp`, and `assurance: PinLaw (R1 at
L:C, …)` otherwise. `checked_sem` is the Fundamental Property at it (`SemC ∅ c.ctx c.t.erase c.C`, at
every host), and `checked_runs` adequacy for a closed `main : F 1`, both at `hp`;
`checked_sem_pin` and `checked_runs_pin` are the same for every checked program, under `PinLaw`.

    theorem checkProgram_letPoly {p : Program} {r : Report} {c : Checked}
        (h : checkProgram p = .ok r) (hc : r.main = some c) {b : Expr} {j : Jdg}
        (hcl : closedAt 0 (Val.lam b).1 = true) (hV : CDerivesAt c.Ξ LifeCtx.empty [] (.val (.lam b)) j) :
        CDerivesAt c.Ξ LifeCtx.empty c.ctx (.app (.val (.lam (c.t.erase.unfill b 0))) (.val (.lam b)))
          (.comp c.C)

A `def` is checked at each of its uses (§10), so `main`'s erasure holds a function at each use:
the copy, which is `[let-poly]`'s premise term (SPEC §18 *Rows*, §24 *Theorems*). For a closed
λ-value typed at the empty context, the theorem gives the rule's derivation of the let that binds
it once, its body `main`'s erasure with the λ-value's occurrences replaced by the bound variable
(`Expr.unfill`, `Core/LetCopy.lean`). The checker does not emit `[let-poly]`.

**Tied derivations** (SPEC §19, decision R). Every derivation the checker builds is tied: it is
`CDerivesAt Ξ` (`Core/Tied.lean`) at every effect context `Ξ` at which the rows it reads at
`[perform]`, `[raise]` and `[handle]` are (`TiedDer`, `Check/Tied.lean`), and `checkProgram_tied`
reads that off. `checkMain` decides that those rows give each operation one signature, of a
nonzero name, and none unrestricted answering `0` (`sigsOkB`), and the program's effect context
`c.Ξ` is the one they give (`effCtxOf`). A constant holds no operation, so its derivation is tied
at every context (`CDerivesAt.ofEffFree`, decided by `Expr.effFree`).

**How derivations are represented.** The checker returns, for each subterm, a `Res Δ T j`: the
typed term `t`, the rows `sigs` its derivations read at `[perform]`, `[raise]` and `[handle]`, the
relaxed rules `pins` they use, and a `Fam`, which holds masks `u` (the slots the subterm uses) and
`w` (the live slots it can be given without using them) over the slot types `T`, and a proof of
`TTied pins sigs Δ (mkCtx T L) t j` for every liveness `L` with `u ⊆ L ⊆ u ∪ w`. The typed term is
data: the derivation's skeleton, one node per rule application, built by the same builder that
applies the rule. A `Res` is built only by the rule builders of `Rules.lean`/`Consts.lean`, each of
which builds its node and applies its typed rule to the premises' proofs, with its side conditions
discharged by the soundness lemmas of `Decide.lean`. So the theorems above read the `tied` field
of the result; there is no separate proof. The derivations are proofs, erased at run time: `bcc`
runs the checker compiled, and `CrossCheck.lean` runs it in the kernel. `TExpr`, `TDerivesAt` and
`TDerivesP` are generated from `CDerivesAt` and `CDerivesP` (`scripts/gen-pin.py`).

**Linearity** (syntax-core §7, §11). `w` holds the persistent slots at every leaf
(`Ctx.DeadP.drop`, `Ctx.SoloP.skip`) and every slot under `<>` and `absurd` (⊤-slack). The
enclosing rule chooses `L`: a split (`Ctx.SplitP`) gives each side its uses, a slot used by both
sides only if it is persistent, and routes an unused live slot to a side that absorbs it; a
`case` or `<,>` needs one `L` for both parts, so each part's uses must be used or absorbed by the
other (`Fam.merge`); a binder's slot must be used or absorbed when its scope closes. A premise on
every live slot (`CtxOutlives`, `Persistent`, `allI`'s `hΓx`) is checked on the used slots and
restricts what may be absorbed. This is Hodas–Miller's input/output reading with the output
chosen by the enclosing rule instead of threaded.

**Implicit destructors** (SPEC §12). `Env.own` marks the slots **owed** to the computation
being checked: variables bound by `x <- M; N`, `let (x, y) = V; M`, a `case` arm or `fun` whose
type has a destructor (`hasDtorB`, sound for `HasDtor` by `dtorB_sound`), is not persistent, and
whose binder is not `linear`. What is owed flows into tail positions: the body of `<-` and `let`
(less what the head or `V` used), both `case` arms, both `<,>` components, `fun`/`Fun` bodies,
`nu_in` and ascriptions. The head `M` of `x <- M; N` is owed the owed variables it
mentions by name (`mentionsC`). A value, and so every computation inside one, starts with
nothing owed. At a terminal computation (`Comp.terminal`), the checker checks it with nothing
owed, then wraps the result in `dtorE A xᵢ; …` for each owed slot `i` it neither used nor
absorbed, the lowest index outermost (`dropOwed`). Each wrap is `rDrop`, which applies
`drop_derives` (`Core/Dtor.lean`: `unitE` over `lolliE` of the variable and `dtor_wf`) to a split
of the variable leaf and the computation, so the result is still a `Res`, and
`checkProgram_sound` is unchanged. The erasure contains the calls, and the backend compiles them
as ordinary code. A binder whose variable is left unconsumed is reported with its reason: `linear`,
or a type with no destructor. A `case` or `<,>` whose parts differ in a variable with no
destructor names that type.

**Cross-check.** `CrossCheck.lean` proves by `decide +kernel` that the ten `def`s of §13.1
erase to `countAlgV`, `natCopyE`, `freeLAlgV`, `freeNatE`, `addAlgV`, `addE`, `sumAlgV`,
`sumCE`, `freeCAlgV` and `freeCE`, and that `corpus/sum-prog-exact.bc` and
`corpus/count-down-exact.bc` check at the empty context and erase to `sumProg` and
`countDownProg`; `sumProg_derives_bcc` and `countDownProg_derives_bcc` re-derive those
judgments from `bcc`'s derivations. The parser runs at elaboration time (`bcc_program%`): parsing
these files in the kernel takes more than ten minutes.

### Incompleteness

These are the known ways a derivation can exist that the checker does not find. Each is a limit
of the search; none is a change to `CDerives`.

1. **Modes** (§11). `inl`, `inr`, `roll` and `absurd` only check. A form that synthesizes needs
   its parts to synthesize: an unannotated `x <- M; N` needs `M` to, the first arm of a `case`
   and the first component of a `<,>` must synthesize when the whole is synthesized (the second
   is checked against it), and a pair synthesizes only if both components do. There is no
   unification; an ascription or `x : A <- M` supplies the type.
2. **Types are compared by `=`**, with no α-conversion of lifetime binders (§3). In particular
   a synthesized `Fun` gets the binder `Δ.freshVar`; checked against `forall 'x < @b. C` it takes
   the type's binder.
3. **The non-syntax-directed rules apply only where written**: `ret`, `ofRet`, `bangE`, `boxE`,
   `immSub`/`mutSub`, `roll`/`unroll`, `nuIn`/`nuOut` apply at
   `return`, `run`, `unbang`, `unbox`, `:>`, `roll`/`unroll` and the `nu_in`/`nu_out`
   keywords, never implicitly (§14).
4. **Lifetime entailment** (`ordB`, §12 item 1) is sound and searches only the structural rules:
   reflexivity, `⊤` on the right, a variable through its bound, and `⊓`/`⊔` on either side. It
   does not use distributivity (`('x ⊔ 'y) ⊓ 'z ⊑ ('x ⊓ 'z) ⊔ ('y ⊓ 'z)` is not found), and it
   never concludes from an unsatisfiable `Δ`. `Δ ⊨ @a` is decided by `Life.wf`, which is
   complete except when `⟦Δ⟧ = ∅`. `VOutlives` (`outlivesB`) is complete relative to `ordB`.
5. **Derived forms stated at `Ctx.Dead`** (`alloc_s`, `free_s`, `withbor_s_*`, `withbor_f2_*`)
   absorb no slot, persistent or not: a persistent variable must be dropped elsewhere.
6. **Def type parameters** are elaborated at the use and substituted as elaborated types (§10
   says textually); a `def` with parameters is checked only at its uses.
7. **Fuel.** The checker's call tree is bounded at depth 2^20, type elaboration at 2^16.
8. **Drops only along tail positions** (SPEC §12). A value never drops: a variable consumed on
   one path of a computation inside a value (`run M`, `thunk M`, the scrutinee of `case`) must be
   consumed on every path of it. Apart from tail positions, only the head of `x <- M; N` is owed
   what it mentions. The head `M` of an application `M x`, a projection or an instantiation is
   part of a terminal computation, so a `case` there must balance its arms by itself.
9. **Externs are not owed.** `main` must consume every non-persistent extern, with or without a
   destructor.

### Effects (SPEC §19)

The checker applies §19's rules (`Core/Fundamental.lean`) through the builders `rEffSub`,
`rPerform`, `rRaise`, `rEffLet`, `rEffThen` and `rEffHandle` (`Rules.lean`) and the six unwinding
borrows (`synConstU`, `Consts.lean`); their side conditions are decided by `rowLeB`, `Row.nzB`,
`Row.uniqB`, `Row.weakB`, `Row.unrB`, `Row.unwindB`, `dropB` and `CTy.effLeafB`
(`Decide.lean`), each with its soundness lemma.

* **The current row.** `Env.row` is the row of the returner chain `F_Σ B` a computation is checked
  against (`Env.atC`); `perform[n.i] V` and `abort[n.i] V` look their operation up in it
  (`findOp`). A value has no row (`Env.forVal`), so a computation synthesized inside a value
  (`thunkv fun …` with no type expected) cannot perform: ascribe it.
* **Conversion.** Where a synthesized type meets an expected one (`convC`), `F_Σ′ A` is accepted at
  `F_Σ A` when `Σ′ ⊆ Σ` (`rowLeB`), by `[sub]`; `return V` checks at `F_Σ A` the same way.
* **Effectful binds.** `x <- M; N` whose head synthesizes `F_Σ′ A` with `Σ′` nonempty is at the
  current row `Σ` (or `Σ′`, when none is set), `M` lifted by `[sub]`. At a row with no weakening
  (every operation `lin`) it is `[let]`; when every slot `N` uses drops (`dropB`), and is a `!`
  type at an unrestricted row, `[let]` with the family restricted to those slots; otherwise
  `[then]`, with the finaliser `finalOf`: the destructors (SPEC §12, `rDrop`) of the
  non-persistent slots `N` uses, at `F 1` (SPEC §24: a finaliser lets no raise escape). A slot
  with no destructor there is an error naming it. An annotated head `x : A <- M` at a nonempty
  row is checked at `F A` first, and at `F_Σ A` only when that fails. `x <- M unwind (D); N` is
  `[then]` with the `D` written; both `N` and `D` are owed what the binding is owed.
* **Handlers.** `handle_with[n](hr, hc) M` reads `A`, `Σ` and `R` off `hr : !U(A -o F_Σ R)`
  (`retRead`) and the operations `E` off the clauses' type (`clausesRead`, checked equal to
  `clausesTy Σ R E`); an abortive clause `!U(A -o F_Σ R)` is read as the affine operation
  `A ↠^aff 0` (`aff` and `unr` give it the same clause type). `M` is checked at
  `F_{ofEff n E 0 ++ Σ} A`. When a clause's argument is `A ⊗ [@d] κ`, `κ` a continuation's type,
  the clauses are read as BOXED-κ's first (`clausesReadBoxed`, `clausesTyB Σ R d E`; SPEC §28):
  then `@d` must be defined, every non-abortive answer type of the handled row must outlive it
  (`ansOutlivesB`), and so must every slot `M` uses, and the derivation is `rEffHandleB`'s.
* **Unwinding borrows.** The finaliser is the source's destructor `dtorE` (`forget` at a `mut`
  source, the cell's and the array's otherwise), closed by evaluation; the derivation is
  `dtor_wf` at a dead context, so these constants absorb no slot (as item 5 of the
  incompleteness).
* **One signature per operation** (decision R). `rPerform` and `rRaise` read their row, and
  `rEffHandle` its handled row, into the result's `sigs`; `checkMain` rejects a `main` whose rows
  give one operation two signatures, or an operation of the name `0` (`sigsOkB`, `sigsErr`).
* **Abortive operations are affine** (SPEC §18, decision 63). A row entry `n.i unr A ~> 0` is
  rejected where it is written (`elabRow`), and so is an unrestricted operation answering `0` among
  `main`'s rows.
* **Effectful blocks and stored continuations** (SPEC §30). A block's copy has its parameter at
  `!U(A -o F_Σ B)`, and the call's argument is bound at that type (`a : P <- return W`), so the
  block written in place is checked at its row. A surface handler's clause that boxes `κ` gives
  the site the clause tuple `clausesTyB Σ R ⊤ E`, read as BOXED-κ's above.
* **Callbacks `λ_. M`** (SPEC §26). `fun (x : 1) -> M` at `1 -o F_Σ B` whose body does not use
  `x` is `[λ-dead]` (`lamIt`, `rLamDead`): the body is checked under the binder's slot as for
  `[λ]`, and the slot is closed dead instead of live. A rule inside the body whose premise takes
  only `!` slots (a `!` promotion, `[let]` at an unrestricted row) then does not meet the binder.

### Standard I/O (SPEC §11)

`checkProgram` first elaborates the program (`Elab.elaborate`, which runs `Sugar.elaborate`).
Its `Report` carries that elaboration (`Report.el`): the backend reads the program the checker
checked from it, and never elaborates again. Whether `main` is served `Fail[DivError]` (SPEC §39)
is on the checked `main` (`Checked.exits`). In the sugar, a program that declares no externs and whose `main` names a capability gets `lib/io.bc` (read when `bcc` starts: `Sugar.library`), the
capability externs, and a `main` that hands them back at every terminal; `for x in bytes c { M };
N` becomes a loop by `unfold` built from a template whose holes are filled with the program's own
syntax, and whose own nodes carry the span of the `for`; `&mut c` becomes a binding that rebinds
`c`. Everything the checker sees is ordinary core. An error the checker reports at the span of a
sugar is in code generated for it, and the message says so.
`bcc desugar` prints it, and `corpus/sugar/` pairs each sugar with its core form
(`scripts/check-sugar.sh`).

`input` and `output` are the opaque types `VTy.opq`. `checkExterns` matches a program's externs
with the table of standard externs by name and type. A `main` with capabilities must have type
`F (Caps ⊗ A)`, or `F (U (loop (Caps ⊗ A) (Caps ⊗ B)))` to run until it finishes; `run_io` then
maps the loop, taking the outputs back when it finishes or closes. `ioWrapper` prints `run_io` as source (the harness's externs and a `main` that
makes the capabilities, runs `main`'s body with them bound to their names and takes them back),
parses it and checks it; `ioRunOf` gives every extern of the wrapper its model by type
(`modelsOf`), with the proof `io_every_run` asks for. `IORun.every_run` is that theorem at the
checked wrapper.

The deciders for `VFree`, `Cl`, `NoMut`, `CTy.NuOk`, `VScoped`, `FShape.WF`/`Guarded`, `plainV`,
`Shape.plain`, `Δ.Ok`, `Δ.find? x = none`, `C.isRet`, `FamSide.hinst` and foldImm's
`∀ Δ' a, VOutlives Δ' a R` (`outlivesAllB`, §12 item 2) are complete.

### Choices beyond draft 1

1. `nu_in M` also synthesizes, when `M`'s type is the unrolling of a `nu` type whose thunk
   `U (nu X. C)` occurs in it (`CTy.nuThunks`); for example `F (A + U (delay A)) & F 1`.
2. `unbang V` checked against `A` checks `V` against `!A`.
3. `Fun` checked against a `forall` type takes the type's binder number (item 2 above).
4. `main`'s context is every `extern` of the file, in declaration order. A `def` sees the
   persistent externs declared before it (SPEC §11): at its declaration it is checked at them,
   and at a use it sees `main`'s slots of them and nothing else of the use site. A capability
   is not persistent, so no `def` sees one.
5. Messages print lifetime variables by their source names where they are in scope, and as
   `'lN` (the `LifeVar` number `N`) otherwise.
