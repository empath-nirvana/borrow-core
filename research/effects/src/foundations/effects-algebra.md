# The effects algebra (part 1 of 2)

> **Status: draft for review. Not decided.** This page states the effect theory **on its own,
> with no borrows**. Part 2, [the interaction algebra](interaction-algebra.md), adds BoLo and
> derives the interaction from both. Each law carries where it stands today, so the gaps are
> visible.

Sources, consolidated here:
- the effect model's law suite (`docs/effect-model.md` §3.1, checked off-kernel);
- the decided algebra (`decisions.md`);
- System A's properties (`experiments/Targets/A`, proved at `J₁` = Core's typing);
- SPEC §18–§19, §24–§27.

Status key:
- **Core:** proved at Core / `J₁`.
- **Model:** checked or proved only in `EffModel` / `EffModelRel`.
- **Open:** stated, not proved.
- **Missing:** not stated anywhere.

## 1. Signature

**Computations.** Call-by-push-value: value types `A`, computation types `C`, `F_Σ A`, `U C`,
`A ⊸ C`, `!`, and the CBPV β/η equations.

**An effect** is a named signature: operations `op : A ↠^q B`.
- `q ∈ {lin, aff, unr}` is the continuation's qualifier. `unr` is tolerated and never designed
  for (multi-shot is ignored).
- `B = 0` is **abortive**: the operation has no continuation.
- An operation is **answering** if its handler is always tail-resumptive (SPEC §18).

**Rows** `Σ` are finite sets of **static per-site names** `n : E`. Rows are polymorphic: rank 1,
let-polymorphism (`letPoly`). ☐ *Rank is open; see OA4.*

**Terms:**
- `perform_n op v`
- `raise_n op v`
- `handle_n M with H`, where `H = (return x ↦ N; op x κ ↦ N_op …)`; deep
- handler values
- `M then x. N unwind D`, a finaliser
- `κ = ⟨resume, cancel⟩`

## 2. Equations

### 2.1 Algebraicity (operations commute with evaluation frames)

| law | statement | status |
|---|---|---|
| A1 sequencing | `(op v; y.M) to z. N = op v; y.(M to z. N)` | Model (L1a); Core: `AlgLaw` with a finaliser's start observed, proved given `KeptLamFree`, which fails at the admissible context `ΞT` (frame-deadness run, M3) |
| A1 application, projection | `(op v; y.M) w = op v; y.(M w)`, and the same at `π` | Model (L1a) |
| A2 abort | `raise e to z. N = raise e`; `(raise e) w = raise e` | Model (L1a, arity 0) |
| A3 abort through a finaliser | `K[raise e] = D_K; raise e` | Model; Core: the finally law, see §2.4 |

### 2.2 Handler laws (deep)

| law | statement | status |
|---|---|---|
| H-ret | `handle (return v) with H = N[v/x]` | Model; Core: S4 |
| H-op | `handle (op_h v; y.M) = N_op[v, λy. handle M]` | Model; Core: S4 at the capture cell (F1) |
| H-fwd | `handle_h (op_l v; y.M) = op_l v; y. handle_h M` for `l ≠ h` | Model; Core: S4 |
| H-fwd abort | `handle_h raise_f = raise_f` | Model; Core: S4 |
| tail | a tail-resumptive clause is a call (answering effects) | Core: `TailLaw` OPEN |
| η | `handle M with (return x ↦ return x; op ↦ op …) = M` | `EtaHold` / `EtaLin` OPEN |

### 2.3 Names, scoping and combination

| law | statement | status |
|---|---|---|
| N1 no accidental handling | a site handles only its own name; `fwrap`'s handler is invisible to its callback | Core: E6 (schema form); relational form T3 `Tunnel` Missing |
| N2 sum | effects of different names combine freely; rows are sums | Model (sum); Core: S1 `RowAlgebra` |
| N3 tensor | operations answered by **disjoint capabilities** commute | Model (tensor) |
| N4 absorption | `log m; raise = raise` holds exactly when `Fail` is outside a writer `Log` | Model (L4) |
| N5 ν laws | idem-ν, ν/ν, ν/op, new-ν | Model only. Static names make these elaboration facts; whether they are kernel laws is open (OA3) |

### 2.4 Finalisation and cancellation

| law | statement | status |
|---|---|---|
| F1 finally | `(raise e) then x.N unwind D = D (); raise e` | decided; Core: `then_compatC` at the pure row; with effects: §27, frame-deadness run |
| F2 cancel is not interceptable | the region's handlers are dead; the canceller sees `()` | decided; Core: S5 no-interception (restated under frame deadness) |
| F3 frame deadness | dead frames catch nothing; finaliser effects reach the nearest **live** instance | decided; Core: the machine (frame-deadness run, M1) |
| F4 order | a cancel finalises innermost first, and every finaliser runs | Core: S5 unwind half |
| F5 errors | a finaliser's raise propagates; one with no live handler is a type error; first error wins (policy) | decided; Core: §27 typing (M2); "no typed run drops an error" in M3 |

### 2.5 Linearity of continuations

| law | statement | status |
|---|---|---|
| L1 use | a `lin` `κ` is resumed exactly once; an `aff` `κ` is resumed once **or** cancelled once | Core: S6 reduced to `OnlyOwnerFrees` and `NoDanglingUse`, OPEN |
| L2 no forget | dropping an affine `κ` is its cancel; a `lin` `κ` cannot be dropped | decided (SPEC §19) |
| L3 independence | an `aff`/`unr` continuation may not capture `lin` state (the single rule behind multi-shot persistence) | Model (the independence principle) |

## 3. Derived theorems (what the laws are for)

| theorem | meaning | status |
|---|---|---|
| T-safety | every performed or raised operation has a live handler | Core: S2/S3 (`EffSafe`); typed runs |
| T-handler | handlers are homomorphisms out of the free model, so H-ret/H-op/H-fwd determine them | Missing as a stated theorem: no free-model statement |
| T-leak | runs end with empty memory, continuations included | Core: leak freedom at `J₁` |
| T-colour | one typing of a higher-order function serves every row (no function colouring) | Core: E1 |

## 4. Open in the algebra itself (boxed)

- ☐ **OA1, the free model.** No page defines the free model of the theory or states handlers as
  its homomorphisms (T-handler). Without it, "the laws determine the semantics" is a slogan.
- ☐ **OA2, answering effects.** Are they a sub-theory (operations with a tail-resumptive model)
  or a separate structure (comodels/runners)? The algebra should decide this. *Recommendation:*
  try the sub-theory first; reach for comodels only if an equation forces it.
- ☐ **OA3, names.** With static per-site names, are the ν laws kernel equations or elaboration
  facts?
- ☐ **OA4, rank of row polymorphism.** Rank 1 today. If programs pass row-polymorphic functions
  as arguments, the algebra needs `∀ρ` as a type former.
- ☐ **OA5, η.** `EtaHold` / `EtaLin` open; decide whether η is owed.
- ☐ **OA6, Model-only laws.** N3 tensor, N4 absorption and L3 independence are checked only
  off-kernel; each needs a Core statement or an explicit drop.

## 5. What "done" means for part 1

1. Every row above is stated at Core.
2. Every law is either proved at Core or dropped by decision.
3. The free model and T-handler are stated.
4. OA2 and OA3 are settled from the equations, not by choosing a paradigm.

Part 2 (BoLo) then adds the lend equations and the two interaction statements, and derives what
the joint model must be.
