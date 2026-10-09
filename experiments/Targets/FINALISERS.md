# Finalisers that raise: the typing of `[then]` (decisions of 2026-10-08)

The design for G1–G4 of the finaliser unit. It reads the decided algebra
(`research/effects/src/decisions.md`, *The decided algebra* and *Hard stop*) and the user's five
decisions of 2026-10-08:

1. a cancel is not interceptable;
2. a finaliser's raise of a name handled **outside** the cancelled region propagates to the live
   handlers and reaches the canceller as an ordinary raise (`prog₃`, `cancel-reraised`);
3. a finaliser's raise of a name handled **only inside** the region is a **type error** (`prog`,
   `cancel-suppressed`), a typing rule and not a runtime seal;
4. of several finaliser errors the first wins (policy);
5. option A (`[then]`'s finaliser at `F 1`) is lifted.

Design only: no proof, no change to `Core/`, BoLo, SPEC, the machine or the relation. Branch
`tier1-effects`. The rejected `guard` stash is read for nothing here.

## 0. Outcome

> **STOP: ALGEBRA (G1, narrow; not yet machine-checked).**
> - **Law.** Finalisers follow `finally`'s law; "a finaliser's raise of a name handled outside the
>   cancelled region propagates to the live handlers" (decision 2), read with SPEC §19 *Names*: re-entry
>   of one site "meets the nearest enclosing instance of that name".
> - **Change.** With the machine unchanged, `[cfin-raise]` suppresses by **name**: `m ∈ N`, where
>   `N = c :: K.hndNames` is fixed when `κ` is captured. `K` includes the frames *below* the fired
>   finaliser, those its `M` installed around the operation. If a site is re-entered there and the
>   finaliser raises its name, the machine drops the error, while `finally`'s law sends it to the
>   live outer instance. A typing in which no typed run drops an error must reject that program (§3.6,
>   `P_re`), and no decision records the rejection. Option A rejects it today, and §27 as designed
>   keeps rejecting it.
> - **Programs affected.** A finaliser that raises the name of a site its `M` re-enters around an
>   operation whose continuation a cancel tears down (`P_re`, §3.6). No kernel, corpus or (E)
>   program is of this class.
> - **Decision needed.** (a) Record the by-name reading of decision 3: "a finaliser may not raise a
>   name of which the cancelled continuation holds a handler". §27 is then as designed. Or (b)
>   change the machine in a later unit: `[finalise-cancel]` removes from `N` the names of the frames
>   it drops, and the lowering's mask does the same. §27 then drops its `pass` annotation, and `P_re`
>   types and propagates. Under (a) no program changes status. Under (b), §27 built under (a) loses
>   `pass` and nothing else.
> - **Evidence to build before this stops anything:** `P_re`'s term and its run (interpreter, or
>   `runM` by `rfl`), which drops the error; after §27, its rejection.

The rest of the unit, under reading (a):

- **G1 cannot be a `[then]`-only rule** (§2.1). `e7b 1 2` and `e7c 1 2` have the same `[then]`
  subterm, and its row holds the same set of entries in each. With `[sub]` and `[handle]` as they
  are, a typing of that subterm types both programs. A row threaded down the derivation fails at λ
  boundaries (§2.2).
- **The rule (SPEC §27)** annotates each *capturable* row entry with `fin` (the names the finalisers
  of the continuation it hands may raise) and `pass` (names no handler of that continuation has).
  `[then]` types `D` at an abortive sub-row `S_D` with `names(S_D) ⊆ pass` and `⊆ fin`. `[handle] n`
  asks `n ∉ fin` and `n ∉ pass` of every capturable entry it forwards, and `n ∉ fin` of its own.
  The three checks mirror the three parts of `N`. Machine, terms and counts are unchanged, and so
  are `fundamentalC`'s, `adequacyC`'s and `adequacyD`'s statements. Every existing derivation types
  at the default annotations.
- **G2.** `CfinQuiet` is false under §27 (`e7b` reaches `[cfin-raise]`). Algebraicity is proved
  outright once a kept error is observed by its label and operation (§5.2, a reading).
  `CancelsNoCtl` holds under §27, and a guard proxy derives it (§5.3). "No `[cfin-raise]` of a name
  in `N`" is what §27 guarantees, and proving it at runs needs a typing of configurations; it is on
  no tier-1 premise.
- **G3.** `e7a`, `e7b`, `e7d`, `e8a`, `e8b` and `e9`'s three programs type at `J₁`. `e7c` is
  rejected (decision 3), so E7 is restated: E7c's typing conjunct becomes its rejection.
- **G4.** AT08 reads `κ` out of its cell with `swap`, puts the copy back, reads it again with
  `free`, and resumes both. The copy's slot is used twice, which `kTy` at `lin`/`aff` (not
  persistent) refuses. A `withswap` form would be refused first, by `withbor`'s outlives side
  condition (a thunk has no outlives rule).
- **A lowering finding** (§3.9). The backend's cancel mask is the set of handler sites *reachable*
  from the cancelled handler's body, wider than `N`. Under §27 it would suppress an error the
  machine keeps. No program today does this. The lowering must reject or refine it.

## 1. What a finaliser's raise meets at a cancel (SPEC §19, as built)

The machine (`Paper/S3_Dynamics/Definitions.lean`, `Head`):

    [op]               hnd (c, H) K[perform (c, v)] ↦ h_op (v, κ),     cancel branch of κ:
                       ccatch (hnd (c, H) K[raise (⊥, (N, none))]),  N = c :: K.hndNames
    [finalise-cancel]  ubind (N', D) K'[raise (⊥, s)] ↦ cfin s (D ())                    (ufinC)
    [cfin-raise]       cfin (N, err) K''[raise (m, v)] ↦ raise (⊥, (N, errNext N err m v))  (cferr)
                       errNext: err if err ≠ none; none if m ∈ N; (m, v) otherwise
    [cancel]           ccatch K[raise (⊥, (N, none))] ↦ ()
    [cancel-raise]     ccatch K[raise (⊥, (N, E))] ↦ raise E                              (creraise)

Write the captured context around the fired finaliser's frame as `K = K₁[ubind (N', D) K₂]`. Then
`N = {c} ∪ names(K₁) ∪ names(K₂)`:

- **`c`**, the capturing handler;
- **`K₁`**: the handlers that enclose the `[then]` inside the region (*above* `D`);
- **`K₂`**: the handlers that `D`'s `M` installed around the operation (*below* `D`; the cancel's
  unwind drops them before `D` fires).

So a finaliser's error at a cancel is dropped exactly when its name is in `N`. The decisions read
off this:

- **Decision 3:** no typed run reaches the middle case of `errNext`. Every name a fired finaliser
  lets escape is outside `N`.
- **Decision 2:** the third case then keeps the error. `[cancel-raise]` raises it at the canceller,
  whose type is `κ`'s cancel entry `F_{S_c} 1` (`S_c` is `c`'s outer row), so a live handler or
  the runner receives it.
- **Decision 4:** the first case is the first-wins policy, unchanged.
- **Decision 1:** a cancel is a raise of `⊥`, and no handler is named `⊥` (`0`). Once finalisers
  may raise, §3.4 is what keeps a cancel from being intercepted.

## 2. Why the rule cannot live in `[then]` alone

### 2.1 The separation lemma

`e7b lw lo = toResult lo (timeoutH lw (bodyF lw (raise lo)))` and
`e7c lw li = timeoutH lw (toResult li (bodyF lw (raise li)))` (`A/Programs.lean`). At `lw = 1` and
`lo = li = 2`, both hold the same `[then]` term `T = bodyF 1 (raise 2 0 ())`, in the empty context,
at a row whose entries are `1 : wait` and `2 : exn`. Only the order of the two handlers outside `T`
differs. `[sub]` (`RowLe`) reorders a row freely, and `[handle]` reads only its body's conclusion.
So a derivation of `T` at `[1, 2]` gives `e7b 1 2`, and the same derivation, `[sub]` to `[2, 1]`,
`[handle] 2` and `[handle] 1`, gives `e7c 1 2`.

**Lemma to machine-check first (G1.0):** `e7c_of_then`. With Core's `effSub` and `effHandleV` as
they are, any derivation of `T` at a row holding exactly those two entries gives one of `e7c 1 2`.
Decision 3 rejects `e7c` and G3 accepts `e7b`, so `[sub]`, `[handle]` or the types must carry
information. A rule confined to `[then]` cannot.

### 2.2 Alternatives that carry the information, and where each fails

- **A row threaded down the derivation** (an index `L` of `CDerives`: the handler names installed
  inside the current function body around the position; `[handle] n` pushes `n`; the kill set is
  `L`'s prefix through the outermost capturing name of `M`).
  - It types E7–E9 and `cancelKept`, and rejects `prog` and `e7c`.
  - It cannot see past a λ: a λ-body runs at its call site, so it is typed at `L = []`. Take a
    callback `λ_. ((wait (); M) then x. N unwind raise e)`, run by `timeout` inside `handle e`. It
    is lawful (`e` is outside the canceller), but the capturing name is outside the callback, so `D`
    may raise nothing.
  - So it keeps option A's rejection of lawful programs with no decision recording it (hard stop 4).
  - It cannot see `K₂` when `M` calls a function (§3.6), and it re-indexes every rule of `CDerives`.
- **Numeric order of names** (`[handle] n` asks `n` above every capturing name of its outer row;
  `D` raises only names below every capturing name of `M`).
  - It is sound, but a program that nests two capturing sites in both orders (a scheduler inside a
    generator and a generator inside the scheduler, same names) has no order. Hard stop 4.
- **A runtime seal** (the stashed `guard` frame). Decision 3 forbids it, and it is hard stop 3.

The information that decides a finaliser's raise flows **up** to the handlers, through function
types. So it belongs in the rows of computation types.

## 3. The rule: cancel annotations on rows (SPEC §27, Entry 26)

### 3.1 Annotations

- A row entry `o = ⟨n, i, q, A, B⟩` is **capturable** when `o.abort = false ∧ o.q ≠ lin`: its
  continuation has a cancel branch (`aff`, `unr`).
- Each row entry carries two name lists, read only at capturable entries:
  - **`o.fin`**: the names that a finaliser may let escape, for the finalisers held by a
    continuation this computation hands at `o`.
  - **`o.pass`**: names that **no** handler frame held by such a continuation has, from the
    operation up to this computation's top. A raise of such a name passes every one of them.
- Defaults are `[]` (no information) for both. The relation does not read them: `OpSig.ent`
  ignores them, and `effTab (CTy.effOf S R)` is `Row.tab (strip S)`.
- As built: two fields on `OpSig` and on `CTy.eff` (`eff n i q A B fin pass C`), `CTy.effOf` passing
  them, and `strip` erasing them.

### 3.2 The rules

    [sub]     S ≤ S′:  every entry of S is S′'s at its key (Row.find), its fin ⊆ the other's fin,
              its pass ⊇ the other's pass. Annotations move outward only by growing fin and
              shrinking pass.

    Γ = Γ₁, Γ₂   Δ; Γ₁ ⊢ M : F_{S_M} A   S_M ≤ S   Δ; x : A, Γ₂ ⊢ N : F_S B   Δ; x̸, Γ₂ ⊢ D : F_{S_D} 1
    strip S_D ≤ (strip S)^abort      (S_D: abortive operations of S only)
    for every capturable o ∈ S_M:   names(S_D) ⊆ o.pass   and   names(S_D) ⊆ S(o).fin
    ───────────────────────────────────────────────────────────────────────────── [then]
    Δ; Γ ⊢ M then x. N unwind D : F_S B            (with §19's hNZ, hUq, hU)

    §24's [handle], its body at F_{(n)↑E^ann ⊙ S} A, and:
    for every capturable o ∈ S:                     n ∉ o.fin   and   n ∉ o.pass
    for every capturable o ∈ (n)↑E^ann (n's own):   n ∉ o.fin
    ───────────────────────────────────────────────────────────── [handle]
    Δ; Γ ⊢ hnd (n, H) e : F_S R

- **`Σ_esc` is `S_D`**: the abortive operations of the `[then]`'s row whose names pass the
  handlers below `D` (`pass` of `M`'s capturable entries) and are recorded for the handlers above
  (`fin`).
- `S(o)` is `S`'s entry at `o`'s key. `S_M ≤ S` already gives `S(o).fin ⊇ o.fin` and
  `S(o).pass ⊆ o.pass`.
- **Every other rule passes rows unchanged**, `[perform]` and `[raise]` at any annotations.
  `[handle]` keeps its body and outer row sharing `S`, as today. The clauses (`clausesTy S R E`)
  and `κ`'s type (`kTy S R q B`) are at that shared, annotated `S`. So a resumed `κ` carries the
  body's `fin` and the handler names excluded from `pass`, and a clause's finaliser around a resume
  is checked against them.
- **Sharing `S` adds no rejection.**
  - At `[handle] n`, `S`'s `fin` also holds names raised by finalisers outside the handler: in its
    clauses, or in the continuation of a `[let]` around it. None of them can be `n`, since `n ∉ S`
    (`hnS`).
  - Inside the body, the entries of `S` (the operations `n` forwards) have `pass` without `n`. Take
    a `[then]` inside the body whose `D` raises `n`.
    - If its `M` performs one of those operations, `n` is above `D` in that capture's region.
      `[handle] n` then rejects it by `n ∉ fin` in any case.
    - If its `M` captures only to handlers inside `n`'s body, `D` is checked against those
      handlers' entries, whose `pass` may hold `n`, and it types.

### 3.3 Why a typed finaliser never raises a dead handler's name

At a cancel of `κ` captured at a capturable `o = (c, i)` with `K = K₁[ubind (N', D) K₂]`:

- **`K₂` (below `D`).** Each handler frame of `K₂` comes from a `[handle] h` inside `M` that
  forwards `o` (the operation was performed inside it), so `h ∉ o.pass` there. `pass` only shrinks
  outward, so `h ∉ o.pass` of `S_M`, while `[then]` asks `names(S_D) ⊆ o.pass`.
- **`K₁` (above `D`).** `[then]` puts `names(S_D)` into `fin` of `o`, and `fin` only grows outward.
  Each handler frame of `K₁` is a `[handle] h` whose body holds the `[then]` and forwards `o`, so
  `h ∉ fin` there.
- **`c`.** `[handle] c` asks `c ∉ fin` of its own capturable entries.

So `names(S_D) ∩ N = ∅`, and `errNext`'s middle case is never reached through `D`. The kept error's
name is in the `[then]`'s row, outside `N`, hence in `S_c`. `κ`'s cancel entry is typed at
`F_{S_c} 1`, so the canceller's context has its handler (decision 2). This argument reads the
typing at the configuration where the cancel fires. Its machine-checked form is §5.1's
`CfinRegionQuiet`.

The functions in between are covered: a function's body contributes its `fin` and `pass` to its
arrow's row, the call's row inherits them by `[sub]`, and the caller's `[handle]`s check them. So
`timeout` (let-bound and substituted, or typed at the callback's annotated row) checks a callback's
finalisers against the handlers around it.

### 3.4 What escapes `D`: abortive operations only

`S_D` holds abortive operations only. This is what `then_compatC` (`Core/EffRules.lean`) supports
semantically (`ewp_frame_then`, `cancel_then`, `ewp_cfin` take `D` at an abort-only table `Ta ≤ T`).
It is also what decision 1 needs while the machine is unchanged:

- **Scenario NC.** A finaliser under `cfin (N, err)` performs a control operation of a live
  handler `h` outside the region. `h` captures a context holding the `cfin` and the `ccatch`.
- If `h`'s clause cancels it while `err ≠ none`, `[cfin-raise]` at the `⊥` raise keeps `err` and
  drops `h`'s cancel state (`errNext`'s first case). `[cancel-raise]` then raises `err` inside
  `h`'s cancelled region, where a dying handler catches it.
- So `h`'s cancel would be intercepted.

A finaliser's control operation stays SPEC §19 *Open* (K3). Option A rejected it too. This is a
reading to confirm (below), not a stop: the decided algebra gives such an operation no meaning
under a cancel.

### 3.5 The lawful finalisers type

Annotations are written `⟨fin | pass⟩` at the capturable entry.

- **`e7b lw lo`.** `M = wait (); ret tt` at `[lw:wait⟨∅ | {lo}⟩]` (a `perform` takes any
  annotation). `D = raise lo`, `S_D = [lo:exn]`. `[then]`: `{lo} ⊆ pass`, giving
  `fin_lw = {lo}`. `[handle] lw`: `lw ∉ {lo}`. `[handle] lo` forwards nothing capturable.
- **`e7d`.** `[then]₁` (`D₁` raises `la`) inside `[then]₂` (`D₂` raises `lb`). The `perform` takes
  `pass ⊇ {la, lb}`, giving `fin_lw = {la, lb}`. `[handle] lw`: `lw ∉ fin`. `la` and `lb` are
  handled outside `lw`. The run keeps `la` and suppresses `lb` (first wins, decision 4), with the
  trace `finTr la ++ finTr lb` and the answer `inr ()`.
- **`e9c`.** `M = gen9 ly` (two `yield`s), `D` raises `lo`. `pass_ly ∋ lo`, `fin_ly = {lo}`.
  `[handle] ly` (`stash`): `ly ∉ fin`. The cancel runs in the closure after the handler returned,
  inside `toResult lo`.
- **`e7a`, `e8a`.** `D = ret ()`, `S_D = []`.
- **`e8b`.** `M = raise la`, which has no capturable entry, so `D` may raise any abortive
  operation of the row (`lb`). Supersession gives `inl (inr ())`.
- **`cancelKept`** (kernel `cancel-reraised`). `M = perform 1` (unr, capturable), `D` raises `3`.
  - `pass_1 = {3}`, `fin_1 = {3}`.
  - `[handle] 2` forwards op 1: `2 ∉ fin_1`, `2 ∉ pass_1`.
  - `[handle] 1`: `1 ∉ fin_1`. `[handle] 3` is outside.
  - `prog₃` itself has no type at all: `H₃`'s answer clause `id` answers `1`, its clause `inj₂ ()`.
    `cancelKept` exists for that reason.

### 3.6 What it rejects

- **`prog`** (`cancel-suppressed`; decision 3).
  - `D` raises `2`, so `fin_1 ∋ 2` for the capturable `(1, 0)`. Its tag is `unr`, so it is
    capturable whatever the derivation does.
  - `[handle] 2` forwards it and asks `2 ∉ fin_1`.
  - `[sub]` only grows `fin`, and `[then]` is the only rule at a `ubind` term (`der_then`).
- **`e7c lw li`** (decision 3): `[handle] li` forwards `lw`'s `wait` with `li ∈ fin`.
- **`P_re`** (the STOP item, §0):

      f    = λ_. hnd (3, H₃ᵢ) (perform (1, (0, ())))          -- the inner instance of 3, around the capture
      P_re = hnd (3, H₃ₒ) (hnd (1, H₁) ((f ()) then x. x unwind raise (3, (0, ()))))

  - `H₁` cancels `κ` (as `prog`'s `c₁` does). `H₃ₒ` answers `inr ()` on a raise, `inl` otherwise.
  - Run: `N = [1, 3]`, because `3`'s inner frame is in `K₂`. `[cfin-raise]` drops the error, and
    the program answers `inl ()`.
  - `finally`'s law: `3`'s nearest live instance from `D` is `H₃ₒ`, so the answer is `inr ()`.
  - §27: `f`'s `[handle] 3` gives `3 ∉ pass_1`, and the caller's `[then]` asks `{3} ⊆ pass_1`, so it
    rejects `P_re`.
  - A typing without `pass` would type `P_re`, and a typed run would drop an error.
- **A finaliser's control operation** (§3.4). Option A rejected it; K3 is open.

Nothing typed today loses its type: at `fin = pass = []` the new premises of `[handle]` hold
(`n ∉ []`), and `[then]` at `S_D = []` asks nothing.

### 3.7 The `CDerives` change and `fundamentalC`'s cases

- **`CDerives`.**
  - `effThen` gets the premises of §3.2: `S_M` and `S_D`, the two row inclusions, and the
    annotation conditions.
  - `effHandleV` gets its two annotation premises.
  - `effSub`'s `RowLe` becomes the annotated order of §3.2.
  - Theorems keep the old shapes for every existing use: `CDerives.effThenA` (§24's rule, `D` at
    `F 1`, `S_M = S`) and `CDerives.effHandleV₀`/`effHandle` (default annotations). The checker's
    `rEffThen` and `rEffHandle` call these.
- **`fundamentalC`.**
  - `effThen`: `then_compatC hs hNZ hUq hU (sub_compatC hM≤ ihM) ihN (sub_compatC hD≤ ihD)`, both
    `sub`s on stripped rows (`strip S_D ≤ (strip S).abortOnly`).
  - `effHandleV`: `handleV_compatC` at the stripped rows.
  - `effSub`: `sub_compatC` on the stripped `RowLe`.
  - One lemma, `cC_effOf_strip`: `cC (CTy.effOf S R) = cC (CTy.effOf (strip S) R)`, since `effTab`
    and `effRet` ignore annotations.
  - No new semantics: §27 restricts the typing below what `then_compatC` already proves sound.
- **Statements.** `fundamentalC`, `adequacyC`, `adequacyD`, `adequacyD_obs` and every compatibility
  lemma keep their statements.

### 3.8 What does not change

- The machine (`Paper/`), `Support/`'s interpreter, `wpTS`, `wpG`, `ewpTS`, `opTable`, `cancelTab`,
  `errOk`, `contShare`, `KapRel`, and every term.
- So the kernel programs, their answers and `corpus/kernel-counts.expected`, and the corpus and its
  goldens.
- The checker still types drop glue at `F 1` (through `effThenA`), so no corpus program changes.
- No BoLo definition and no borrow rule. The borrow unwinding constants' callbacks are at
  `Row.Unwind` rows, which have no capturable entry.
- The cost is mechanical but wide: about 120 pattern sites on `CTy.eff` and `OpSig` in `Core/`,
  `Frontend/Check/` and `experiments/Targets/` (`CDerivesAt`, `ORow`, the inversions). At `J₁` the
  A-level `F ε A` hides annotations existentially, and [sub] composes them.

### 3.9 The lowering

The backend keeps the error a finaliser raises whose name is not in the handler's **mask**: the
names of the handler sites reachable from the cancelled handler's body (`masks`,
`Backend/Clos/Capture.lean`). It rejects a cancel "under a handler reached from its own body" only
for control handlers (`hs`).

- **`P_re`.** The mask agrees with `N` (`3` is reachable), and both suppress.
- **Scenario L** (§27 types it; the machine keeps the error).
  - An abortive site `h` is handled outside the canceller, and `M` reaches `h`'s site again, but
    not around the captured operation (`(g (); wait ()) then … unwind raise h`, where `g` installs
    `h`).
  - The mask holds `h`, so the compiled program would drop the error.
- No kernel or corpus program is of this class. Before a kernel program of the class is added,
  `masks` must be read per capture point, or the rejection extended to every site whose name a
  cancel's finaliser may raise. This goes into §27 *Lowering*.

### 3.10 SPEC edits

- **§27** (Entry 26): *Motivation* (the five decisions), *Typing* (§3.1–3.2), *Semantics* (none
  new; §3.7), *Theorems*, *Programs* (§4), *Lowering* (§3.9), *Open*: `P_re` under reading (a), a
  finaliser's control operation (K3), `κ`'s cancel entry at `F_{S.abortOnly} 1` (it would let a
  finaliser cancel a `κ` whose handler sits under a capturing one), and `CfinRegionQuiet`.
- **§19 *Typing*.** The `[then]` line points at §27, and the paragraph "A finaliser lets no
  operation escape it" is rewritten.
- **§19 *Cancels*.** "An error of a name in `N` … is suppressed" now says that no typed finaliser's
  raise reaches this case (§27). The machine rule stays.
- **§19 *Finalisers that perform operations*.** The finaliser now may raise outside the region.
- **§24's `[then]`.** Marked superseded by §27.
- *Status*.

## 4. Programs whose typing changes

| program | before (option A) | after (§27) | run |
|---|---|---|---|
| `prog` (`cancel-suppressed`) | no derivation (D raises) | **rejected** (decision 3); listed among the Shapes in `Backend/Kernel.lean`; its kernel entry, answer and counts unchanged | unchanged (`prog_run`) |
| `prog₃` | no type (answer clauses disagree) | no type (same reason) | `prog₃_run` |
| `cancelKept` (`cancel-reraised`) | no derivation (D raises) | **typed** at `F (1 ⊕ 1)`; `adequacyD` applies | unchanged, `inr ()` |
| `progH` | in the rejected stash only | would type (`S_D = []`; its finaliser handles its raise); not added: a new kernel entry is not needed | — |
| `P_re` | rejected | rejected (the STOP item) | drops the error |
| E7a, E8a, E9a, E9b | typed (no finaliser, or `D = ret ()`) | typed | as stated |
| E7b, E7d, E8b, E9c | not typed (`D` raises; `FinRaise.lean`) | **typed** at `J₁` | as stated in `A/Expressiveness.lean` |
| E7c | not typed | **rejected** (decision 3); E7 restated (§6) | — |
| corpus, other kernel programs, `Core/EffPrograms.lean`, `EffExamples.lean` | typed | typed at default annotations | unchanged |

## 5. G2: the two hypotheses

### 5.1 `CfinQuiet`: false as stated; what §27 guarantees instead

- **False under §27.** `CfinQuiet` (`Instance/AlgSim.lean`) says no configuration a typed program
  reaches is at a `[cfin-raise]` step. `e7b`, typed at `J₁` under §27, reaches
  `cfin s (raise (lo, …))` at `ΞA`. To build: `not_cfinQuiet_J₁`, by the run (`runM`/`look`).
- **Restated: `CfinRegionQuiet`.** No configuration a typed program reaches is at a `[cfin-raise]`
  of a name in its cancel state's `N`. This is what §27 guarantees (§3.3).
- **Its proof at runs reads the typing at the firing configuration.**
  - Core's relation is big-step: `wpG` sees a run's end, and the suppressing step is an ordinary
    step, not a stuck one.
  - So no Core lemma carries `ewp_cfin`'s view of `D` (an abort-only table) to a configuration of
    a run.
  - A typing of configurations (route 8.2, `RowRoute`) would carry it, but its review did not
    accept it (TIER1-PLAN §4).
  - Status: **OPEN**, and not a premise of tier 1 (§5.2, §5.3).

### 5.2 Algebraicity: proved outright, a kept error observed by its label

- **What `CfinQuiet` was used for.** Its only use is `AlgGood.cfin`, which gives `hpay` to
  `ostep_sim` and `labelOf_start` (`Instance/AlgSim.lean:1279, 1366`).
- **The step is already related.** `AlgRel.head` relates `[cfin-raise]` at related redexes. Both
  sides have the same `N` and the same `m`, and AlgRel-related `err` and `w`, so `errNext` takes the
  same branch on both.
- **Only the label differs.** It is `finEnd (errOf m j w)` on one side and `… w′` on the other, and
  `w`, `w′` are related, not equal, when they hold a λ.
- **Typing does not make kept values λ-free.** A raise's argument type is `Drop`, which includes
  `!U C`. At an effect context with an `unr` resuming operation, a finaliser can raise a `!U` value
  holding an `unr κ`, and that `κ` holds the law's frames, so `w ≠ w′` as terms. (Not built. At
  such a context it would make the law, observing kept values, false, so the reading below would be
  needed for "every effect context", not a convenience.)
- **Plan (a reading, with F2's).**
  - `Ev.start` reads `finEnd (some (m, j, w))` as the kept error's label and operation, without
    its value, as F2 reads `fire D` as `fire ()`.
  - Why: the kept value is re-raised at the canceller and handed to a live handler, which is where
    the run uses it. Its use shows in the answer and the `io` events, at data.
  - Then `labelOf_start` and `ostep_sim` drop `hpay`, and `AlgGood` drops `cfin`. **`I.algLaw_J₁`
    holds with no hypothesis at every effect context.**
  - `algLaw_algAffProg` and the refutations of `AlgLawCode` stay.
- **Alternative.** Keep the observation and assume `CfinLamFree` (kept values hold no λ). It is
  not derivable without configuration typing. Not recommended.

### 5.3 `CancelsNoCtl`: holds under §27; derived by a guard proxy

- **Why it holds.**
  - A captured context holds a `cfin` or `ccatch` frame only if an operation performed inside a
    running finaliser escaped it. Inside a `ccatch`, only finalisers run (`ufinC`, `cfret`); the
    borrow constants' finalisers are `ubind` frames too.
  - §27 types `D` at an abortive row, so `D`'s relation stops at no `perform` (`opTable_abortive`).
  - A kept error is raised only by `[cancel-raise]`, after the `ccatch` is gone.
- **The route** (new; no machine change, no configuration typing):
  1. **`guardFin e`**: every finaliser `λ_. D` of `e`, the borrow constants' `d` included
     (`withborUE d ↦ withborUE (λr. guard (d r))`), becomes `λ_. guard D`. Here `guard` wraps `D`
     in a handler for each name of a handler site of `e` that has a control operation. A capture
     happens only at such a site, and there are finitely many. Each guard's control clauses are
     stuck (`λ_. () ()`), its abortive clauses re-raise, and its answer clause is the identity.
  2. **`ewp_guard`**: a handler whose body's table has no entry for its control operations
     catches none of them, and re-raises its abortive ones. So `guard D` has `D`'s relation. This
     comes from `ewp_handle`'s induction, with the absent cases.
  3. **`fundamentalC_guard`**: `CDerives Δ Γ e j → SemJ Δ Γ (guardFin e) j`. This is
     `fundamentalC`'s induction with each compatibility lemma at the guarded subterms; the `[then]`
     case uses `ewp_guard`. Then Core's relation at `guardFin P` makes every run of it safe, under
     the runner's platform, as `plain_reach` and `platStart_safe` do for `P`.
  4. **`GuardRel`** (as `AlgRel`, stuttering): the runs of `P` and `guardFin P` step alike, except
     for the guards' administrative steps. A step of `P` that performs out of a running finaliser
     is, on the guarded side, a catch by a guard followed by a stuck clause. This contradicts step
     3.
  5. So no run of a typed program performs out of a running finaliser, and the context of every
     cancelled `κ` holds no `cfin` and no `ccatch`.
- **What it reuses.** `AlgSim.lean`'s pattern (relation, `plug_inv`, `head`, forward and back runs),
  `fundamentalC`'s cases, `ewp_handle`'s proof, and `det_ourInst`/`plug_decomp`/`head_det`.
- **Byproduct.** The control-operation half of `FinRowsAt` at `J₁`.
- **Size.** About `AlgSim`'s (2000 lines). If that is too much, `CancelsNoCtl` stays a stated
  hypothesis, as today.

### 5.4 S5's endings (bringing it into line)

- **Today.** SProps reads `Cancellation noFinRaise`. Its premise (`FinRow noFinRaise` of the frozen
  finalisers) speaks only of finalisers at the pure row, so it stays true under §27 but says nothing
  about decision 2.
- **Restatement.** `NoIntercept` reads `FinRow` and `FinEnd` at "labels outside the cancelled
  region" (`¬ Region l K`), and `UnwindOrder` at every label (supersession). `keep`'s first-wins is
  unchanged.
- **Proof.** The `ended`-with-an-error and `superseded` branches of `cancel_pfx`/`unwind_pfx` need
  one fact: a closed finaliser at an abortive row runs to `()` or to an escaping raise of its row
  (adequacy at an abortive table). These branches are untranscribed today ("S5 at a set of endings
  other than `noFinRaise`"). Recommended; it can follow G1–G4.

## 6. G3: E7, E8, E9 at `J₁`

- **E7 restated** (into line with decision 3). `CancelPolicy` keeps E7a, E7b and E7d (typings and
  runs as stated). E7c's two conjuncts become `∀ C, ¬ S.der [] (S.e7c lw la) C`. Docstring: "E7c: a
  finaliser that raises a label the cancelled region handles is rejected". E8 and E9 are unchanged.
- **Derivations at `J₁`.** In the tied kernel with §27 (§3.5), and at A-level as `noColouring_J₁`
  does (`labelsAt`, `der_*_J₁`).
- **Runs.** By `runM` and `rfl`, as `I.accepts_J₁` does:
  - E7b: `inr ()`, trace `finTr lo`;
  - E7d: `inr ()`, trace `finTr la ++ finTr lb`;
  - E8b: `inl (inr ())`, trace `[fire (raise lb)]`;
  - E9c: `inr ()`, trace `finTr lo`.
- **E7c's rejection.** One inversion through `[handle] li` (`lw`'s `wait` is forwarded and
  `li ∈ fin`). It reuses `FinRaise.lean`'s `derAt_hnd`, `derAt_then` and `derAt_let_arg`, re-aimed.
- **Status.**
  - E7, E8 and E9 are PROVED at every admissible effect context.
  - `FinRaise.lean`'s refutations (`not_der_e7b_J₁` …, `not_eProps_J₁`) are of option A and are
    false at `J₁` under §27, so they are replaced, as is `I.not_tier1_J₁`, whose proof reads them.
  - `EProps` at `J₁` is then **not refuted**. E2a–c, E3, and E10's `retry` and loop are not derived
    (no obstruction verified). E5 and E2d are proved only where no `exn` signature, or no
    operation, is `unr`.
  - `status_eProps_J₁` and `status_tier1_J₁` are rewritten accordingly.

## 7. G4: AT08 rejected by the continuation rule

- **Program.** "A continuation in a shared cell, read twice", with `load` (which has no rule)
  replaced by the cell's typed reads, `swap` and `free`:

      op (_, k) ⇒ c ← alloc k;
                   (c, k₁) ← swap c ();        -- read κ out, leave ()
                   (c, u)  ← swap c k₁;        -- put the copy back: k₁ moves into the cell
                   k₂ ← free c;                -- read it out again
                   u; resume k₁ (); resume k₂ ()

  (`handleWith 5 .lin … fooE`, as `at08` is.)
- **Why only the continuation rule rejects it.** `alloc`, `swap` and `free` are at any payload, and
  so at `κ`'s type. Every step types but one: `k₁` is used by the second `swap` and again by
  `resume`. So its slot is live on both sides of a split and must be persistent, and `kTy` at `lin`
  and `aff` is a thunk of an `&`, which is not. Were `κ` persistent, the program would type.
- **The rejection** (`not_der_at08`, at Core's kernel and the tied one). It follows the shape of
  `not_der_at05` and `not_der_at13`:
  - the clause tuple and `der_lam` give the clause body;
  - `der_bind` through `alloc` gives the cell's content type, a view of `κ`'s slot type (`kview`);
  - `der_app` at `swap` gives `k₁`'s slot at that type;
  - `der_seq`/`der_bind` give the split with `k₁` live on both sides;
  - `splitP_both` gives persistence, which `kview_not` refutes.
- **Not the `withswap` form.** Reading through a `Mut` lend (`withbor` (2), then `withswap` with the
  duplicating callback `λk. (k, k)`) is refused first by `withbor`'s side condition
  `Δ ⊢ A ⊒ @b`. `VOutlivesR` has no rule for a thunk (SPEC §19: `U(F_Σ A)` has no outlives rule),
  so that form would not test the continuation rule.

## 8. The hard stop, step by step

| step | (1) law | (2) kernel/corpus behaviour | (3) runtime block | (4) rejects a lawful program | (5) weakens a target |
|---|---|---|---|---|---|
| G1.0 separation lemma, `P_re` run | no | no | no | no | no |
| G1 §27 | no: it implements decisions 2–4 | no: terms, machine and counts unchanged; `prog` only moves to the Shapes | no | **`P_re` class: STOP: ALGEBRA (§0)**. `prog` and `e7c`: decision 3. A finaliser's control operation: K3, decision 1 (reading) | no |
| G2 `CfinQuiet` restated, `AlgLaw` outright | no | no | no | no | the kept-error observation: a reading (§5.2), needed at contexts with `unr` resuming operations |
| G2 `CancelsNoCtl` by the proxy | no | no | no | no | no |
| G2 S5's endings | no | no | no | no | into line (decision 2) |
| G3 E7 restated | no | no | no | E7c: decision 3 | into line (decision 3) |
| G4 AT08 | no | no | no | AT08 was rejected already; now for its stated reason | into line with AT08's intent |

## 9. Order of work and size

1. **G1.0** (small): `e7c_of_then`; `P_re`'s term and run. Then the user's decision on §0.
2. **G1** (large, mechanical): the annotations on `OpSig`/`CTy.eff`, the rules, the old-shape
   theorems, `fundamentalC`'s three cases and `cC_effOf_strip`, the checker, Targets' `CDerivesAt`
   and its inversions. SPEC §27 and the §19/§24 edits. `cancelKept`'s derivation; `prog`'s
   rejection (Targets, reusing `Rej`'s inversions); `prog` listed as a Shape.
3. **G3** (medium): E7 restated; E7–E9 at `J₁`; E7c's rejection; status.
4. **G4** (medium): AT08's program and rejection.
5. **G2** (`AlgLaw`: small; proxy: large; S5's endings: medium–large).
6. TIER1-PLAN outcome, register rows, `Status.lean`; then `make gate` once, as the separate stage.

## 10. What `I.tier1_J₁_of_ESU` needs after this unit

| premise | after G1–G4 |
|---|---|
| `hE`: A's (E) properties at every admissible `Ξ` | E7 (restated), E8, E9: PROVED. **Still open:** E2a–c and E10's `retry` (a function at `!U C` forced); E3 and E10's loop (`unfold`'s stepped value); E5 and E2d at contexts with an `unr` `exn` or `unr` operation |
| `hS4`: S4 | PROVED (re-checked after G1's mechanical edits) |
| `hC`: S5 (`noFinRaise`) | PROVED given `CancelsNoCtl`; `CancelsNoCtl` by the proxy (§5.3), or still a hypothesis; restated endings optional (§5.4) |
| `hU`: S6 | OPEN: `OnlyOwnerFrees`, `NoDanglingUse` (not this unit) |
| `Accepts`, `Rejects` | PROVED; AT08 restated (G4) |

`I.not_tier1_J₁` no longer holds as proved, so tier 1 at `J₁` is **open, not refuted**. Beside done:
`AlgLaw` is proved outright under §5.2's reading. `CfinRegionQuiet` (the decided "no silently
dropped error", at runs) is OPEN behind configuration typing.

## Readings for the user to confirm

1. **§0:** the by-name reading of decision 3 (a), or the machine change (b).
2. A finaliser lets escape abortive operations only; a control operation stays K3 (§3.4, decision 1).
3. E7's restatement: E7c is a rejection (§6).
4. Algebraicity observes a kept error by its label and operation (§5.2), beside F2's reading of
   `fire D`.
5. S5's endings are region-relative (§5.4).
6. The lowering's mask is refined, or rejects scenario L, before such a kernel program is added
   (§3.9).

## Unspent hypotheses, unused results, untranscribed in the run-up

- **Unspent.**
  - `then_compatC` already proves a finaliser at the whole abortive row sound. §27 spends none of
    that semantic slack: the restriction is the algebra's, not the relation's.
  - `κ`'s cancel entry at `F_{S_c} 1` is wider than its runs need (abortive operations only).
- **Unused uniqueness results.** `det_ourInst` and `rstep_det` are read by no step of G1. G2's
  proxy reads `plug_decomp` and `head_det`, as `rstep_bwd` does.
- **Untranscribed in the run-up.** The separation lemma; `P_re` and scenario L as terms; S5 at
  endings other than `noFinRaise`; `ewp_guard`; configuration typing (route 8.2, not accepted), the
  only route found to `CfinRegionQuiet`.
