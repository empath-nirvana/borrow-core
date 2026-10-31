# Scope: #746 step 4 (F3) — the stack machine's hand-over as a local assertion

**Kernel target.** F3 rests on one named `UNPROVED:` assertion, `Backend2.StackKHandOver`, whose
content is the stack machine's hand-over and nothing else: at a `stackK` drop the dropped `k` is
`clos kc [a]`, the `k` that takes over is `clos kc [base]`, `base` is at or below `a` on the task
stack, and the frames from the top down to `a` are written, so `clos kc [base]` takes them over.
`Lint` checks the static half of the premise at each drop node, from the node alone. The decision
(user, 2026-10-31): "A′ is fine for now". #755 (task stacks in the kernel) is the route to a
proof.

## Rules

1. **The assertion is about configurations of the LIR interpreter.** It quantifies over the
   interpreter's states `s` at a `stackK` drop node that a run of the program reaches
   (`Interp.Visits`), and concludes the hand-over relation at `s` (`Interp.HandOver`). Its
   conclusion reads only the node, the state's variables and the current task stack.
2. **Its scope is the code `Convert` generates.** An arbitrary LIR program can carry a `stackK`
   node over any closure, so the statement is about the programs `lirOf` produces; a negative
   test shows a program `Lint` accepts whose run fails the hand-over (the interpreter refuses
   it), which is why the scope cannot be all programs.
3. **The node carries its premise.** A `stackK` drop's body is `let k₂ = clos kc [base] in …`:
   the drop is structurally tied to the `k` that takes over and its address. `Lint` checks that
   shape, that `kc` is a `&` code each of whose functions takes one address, that the dropped
   variable and `k₂` are both at `kc`'s closure type, and that `base` is an address. No variable
   set is read.
4. **What follows is proved.** Under the hand-over, the frames the dropped `k` stands for are
   among those `k₂` stands for, and the drop's own step changes no object, cell or stack.
5. **The interpreter checks the hand-over on every run** at each `stackK` drop, and refuses a run
   that fails it, so the gate's LIR stage checks it on every program it runs.
6. **Trust reporting.** `bcc trusted` lists `StackKHandOver` at each function with a `stackK`
   drop, as it lists `PinLaw` at each relaxed rule. `PinSites` cites it for `DropRule.stackK`.

## Not done

- No kernel rule for the drop; no type for the task stack; no proof of the assertion (#755).
- No change to what compiles or to the code the stack machine runs.

## Deleted

`Prog.stackKs`, `CState.stackKs` and its threading in `Convert`, `Lint.dropsAt`'s variable
argument, `Backend2.StackKSound`, `Tm.dropsStackK`.

## Tempting shortcuts → STOP

| Shortcut | Why not |
|---|---|
| Keep a set of variables or sites that may drop at `stackK` | program-shaped |
| State the assertion as "the program's run ends with no object left" | whole-program, not the hand-over |
| Widen it to any closure over an address, or any `&` code | beyond the stack machine's hand-over |
| A cell per level so a type licenses the drop | an allocation per level |
| Any other copy or drop of a linear or owed value | HARD STOP |
