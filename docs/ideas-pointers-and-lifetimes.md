# Ideas: pointers, smart pointers, cycles, non-lexical lifetimes

Brainstorm, not design. Nothing here is decided or tested in Lean unless it cites an
experiment. Recorded 2026-09-25.

## Family borrows: deref as a path step

In the model an owned `Ref T` is `ℓ ↦ own(v) ● ρ`: the pointee's resource sits beside the
pointer cell. Nesting appears only when a frame is taken, because `withbor`/`withload` pack
everything reachable into the frame cell's witness. Every same-lifetime obstruction so far
(`experiments/Projection`, `Relaxed`, `FrameEnd`: `imm_view_rejected`, `mut_view_rejected`)
comes from that packing.

Idea: treat an owning pointer as a path step (as Rust treats `*b` as a place), and borrow a
structure as the family of every cell it reaches, each framed individually at one lifetime.

- Families of leaves at one lifetime are already derivable (`experiments/Places`,
  `experiments/LeafPlaces`).
- For recursive data the family has dynamic size and is built by a fold
  (`experiments/CBPVMu` borrowed fold).
- The family's type is data, e.g. `μX. 1 ⊕ (Mut 'a N ⊗ X)`; handing out elements one at a
  time is `IterMut`.
- No cell's witness contains another's, so the view-rejection lemmas do not apply.
- Possibly no model change: only the elaboration of a surface `&mut` borrow differs.

Cost: one frame per cell unless frames erase (dream property C7). The lender's shape must be
reassembled when the borrow ends; the fold supplies it.

Probe: `borrowAll : Ref L ⊸ (∀'a. MutFam 'a L ⊸ [a] T) ⊸ Ref L ⊗ T` built by fold; iterate
the family element by element; return and free the list.

## Smart pointers

| Rust | Here | Notes |
|---|---|---|
| `Box<T>` | owned `Ref T`, deref as a path step | family borrows above |
| `&T`/`&mut T` through a `Box` | family borrow | or option B (`docs/scope-deep-freeze.md`) for `Imm` |
| `Rc<T>`, immutable | shared ownership with a count | immutable after creation, so acyclic; leak freedom kept |
| `Rc<RefCell<T>>` | shared plus interior mutability | permits cycles, which leak; see below |
| `Cell<T>`, `T: Copy` | shared cell with a type invariant | close to ML references and to `mut`'s `P̂`; smallest step into interior mutability |
| `RefCell<T>` | runtime borrow flag | the flag behaves like a dynamic lifetime token |
| `GhostCell` / brands | permission separate from data: a brand token unlocks all cells of the brand | proved in RustBelt (Yanovski et al., ICFP 2021); here the brand is a `Mut` over a region |
| arenas, indices | `alloc` as a handler handing out `Mut 'r` | graphs by index avoid pointers |
| raw pointers | [CONF] §5 future work (gradual typing) | later |

## Cycles without giving up leak freedom

Rust made `mem::forget` safe because `Rc<RefCell<T>>` cycles leak. Two layers could keep the
guarantee:

1. **Modes.** Cycle-capable shared cells live at a mode with weakening (unrestricted, or
   linear with a derived drop). Adjoint logic's independence principle then forbids them from
   containing linear values. A cycle may leak memory but never a linear resource (files, locks,
   linear obligations). Compare Rust's proposed `Leak` auto-trait.
2. **Regions.** Shared mutable cells are allocated only in an arena `'r`, and the arena is
   linear. Cycles live inside something that is freed wholesale when its scope ends, so memory
   does not leak either (Tofte–Talpin regions; `alloc` as a handler).

A global unrestricted heap with shared cells could be omitted, or later placed behind an
explicit capability, like divergence.

Model cost: a new cell kind, a duplicable handle to a cell whose contents satisfy an invariant
(like `mut` without exclusivity). The arena owns every such cell, which keeps it in the
linear accounting.

Probe: an arena as a linear resource whose handler hands out duplicable shared cells holding
only `!` or `Imm` contents; build a two-node cycle; show the program ends with empty memory.

## Non-lexical lifetimes

BoLo's lifetimes are lexical: borrows are callbacks and lifetimes form a stack (`'b ⊏ 'a`).
NLL splits into three features:

1. **End at last use** (RFC 2094 problem case #1). Mostly elaboration: the surface compiler
   chooses each callback's extent. No model change when live ranges nest. Non-nested overlaps
   (lender reused after one borrow's last use while a later borrow is live) are not directly
   expressible; how often real code needs them is open.
2. **Flow-sensitive / conditional** (Polonius, problem case #3, e.g. `get_mut` or insert).
   Typed `Mut 'a M ⊸ Mut 'a V ⊕ Mut 'a M`. Works for places (sub-family at one lifetime);
   through pointers it is the same open problem as `&mut` through a pointer, which family
   borrows may address.
3. **Truly non-lexical** (lifetime tokens, as in RustBelt's lifetime logic). Lifetimes stop
   being a stack; the typed world, reborrows and frame records assume nesting. A large model
   change, to be paid only if programs require it.

Probe: write RFC 2094's problem cases and a few Polonius cases (conditional return, borrows
across loop iterations, two-phase `v.push(v.len())`) in the core with nested callbacks, and
classify each as expressible, blocked by pointer projection, or needing non-nested lifetimes.
