# Prior art: the iteration matrix

This is a literature survey for `docs/iteration-design.md` (PR #133). It records what other work
establishes about the matrix of polarity (data/codata) × direction (push/pull), and about the two
gaps in it. It decides nothing. Sections 1–8 are findings; §9 lists at most five candidate ideas,
each labelled as a hypothesis.

It does not repeat `docs/iteration-design.md` §6 (Rust, Lean, Clojure, GHC fusion, Koka, Effekt,
Go, Nystrom, Kiselyov et al.'s stream fusion). It also does not repeat
`docs/prior-art-borrow-splitting.md` (RustBelt's LftL-bor-split and fracture, the laws L1–L5) or
`docs/prior-art-effects-coeffects.md` (Granule and coeffects as a home for borrowing). Where it
goes deeper on the same source, it says so.

**Conventions.**
- Every source was fetched on 2026-09-30 with a generic User-Agent. PDFs were converted with
  `pdftotext -layout`.
- Text in quotation marks is verbatim from that extraction.
- Where extraction garbled a glyph (⊸, ◊, ⊢, subscripts), the restoration is noted at the quote.
- A quote is cited by the section or page the source prints.
- Sources that could not be fetched are listed in §10, and nothing is taken from them.

**The matrix under test.**

| | push (the producer drives) | pull (the consumer drives) |
|---|---|---|
| **data** | fold: the structure calls a step | descent: the consumer holds the rest (`match`, a cursor) |
| **codata** | yield to a handler or sink | `next` on a state machine |

**The two gaps.**
- **(a)** `μ` has no data–pull eliminator.
- **(b)** Under a borrow, both `μ` cells are blocked by one fact: a view through a `Ref` to the
  tail is taken at a strictly shorter lifetime. This is `pSpec_succ` (`Core/FoldImm.lean`) and
  SPEC §5 Open (`experiments/FrameEnd`, `imm_view_rejected`).

---

## 0. Summary

1. **Nobody draws exactly this 2×2, but three sources draw its direction half with costs.**
   - Lippmeier et al. give operators in "polarity versions". Of these, a pull→push drain is free,
     and push→pull "must introduce a buffer".
   - Bernardy & Svenningsson type the four stream polarities linearly and name the cost of each
     composition: matched polarities are synchronous and free, two pulls need a loop, and two
     pushes need threads and a buffer.
   - `pipes` names fold (request), unfold (respond), push and pull as four categories on one type.

   Hinze's papers state the polarity half: `μ → ν` is free, and `ν → μ` "typically involves
   imposing some depth bound". Our axes and crossing costs match all of these (§1, §4).
2. **Descent has a standard proof rule and a standard owned implementation.** The proof rule is
   Tuerk's loop specification rule and Charguéraud's `islocal` loop formula. Both frame away the
   processed prefix, so no list segment appears. The owned implementation is Hofmann's
   `list_destr`/◊ and FP²'s `match!`, which consume and reuse cells in order with no view of the
   tail. McBride's `lit` types the step with the tail at usage 0. So for **owned** lists, gap (a)
   is a missing constant, not a missing idea (§3).
3. **On the step through a pointer to a tail, every system read is looser than our encoding.**
   - RustBelt's instruction S-deref-bor-own keeps the outer κ at `&κ own τ → &κ τ`.
   - RustHorn has `P ∘ own = P`.
   - NLL generates no constraint at a `Box` deref.
   - Cyclone keeps the tail in one region.
   - BoLo prints no `μ`, and says nothing about lists. It keeps a nested `Imm` at its own
     lifetime (`Imm 'b (Imm a T) ≜ Imm a T`, rule ⟲M). The fresh lifetime appears only at a
     linear `Ref`/`Mut`.

   So the shrinking lifetime is a consequence of our reaching the tail through `Ref` and reading
   `Imm̲ 'b (Ref T) ≜ Imm 'b T` once per level. It is not a statement BoLo prints about lists (§5).
4. **`for` as a handler of `yield` reduces to a loop with an early-exit step, and the prior art
   agrees.**
   - Kiselyov argues that a "left-fold-like combinator with premature termination" is the optimal
     traversal interface, because the enumerator frees resources on both exits.
   - Lean elaborates `for` to `forIn … ForInStep.yield/done`.
   - Rust's `try_fold` takes `ControlFlow`.
   - Koka compiles a tail-resumptive operation as "a regular function".

   The one argument against lowering `for` to `try_fold` is Rust's: it cannot trust the producer
   to stop after `Break`. That argument is answered by linearity: once the step returns `R`, there
   is no `S` left to continue with (§7).
5. **Grades did not yield a new construct.**
   - Graded iteration makes the step's grade the data's length only when the length is a type
     index (BLL `N_x`, Granule's `Vec n`).
   - Graded promotion multiplies the captured context, so a step used `n` times cannot capture a
     linear resource. BGMZ's `fix` forces the grade to ∞.
   - Every system read keeps the step closed or `!`, and threads linear state through the
     accumulator, as we do.

   What grades do fit: continuation shot-ness (0/1/ω), which Tang et al. make a per-operation
   annotation; and FP²'s `fip(n)` and Hofmann's ◊ as per-cell capacity tokens (§6).
6. **Lists and arrays meet at the iterated separating conjunction.**
   - Reynolds relates `list α (i, j)` to iterated `∗` over an address sequence.
   - Tuerk frames `list(t, …)` and `array(a+i, n−i, …)` by the same rule.
   - Our own `wpTS_I_frameList` quantifies over an arbitrary `I : List Loc` with a per-location
     type. Consecutive locations are not what the array proof uses.

   What a list lacks is a leaf type whose relation does not own the next node (§8).

---

## 1. Who draws the table

| source | axes it draws | cells it fills | crossing costs it names |
|---|---|---|---|
| Lippmeier, Mackay, Robinson (FHPC 2016) | direction (sources vs sinks), per operator | codata push and pull | drain free; push→pull a buffer; 8 polarity versions of a 3-leg fold |
| Bernardy & Svenningsson (IFL 2015; later Hask-LL draft) | direction × dataflow (Src, Snk, CoSrc, CoSnk), linearly typed | codata push and pull | matched: none; pull+pull: a loop or schedule; push+push: threads and a buffer |
| `pipes` (Gonzalez) | fold/unfold × push/pull as five categories | all four, on one type (`Proxy`) | `reflect` is the duality |
| Claessen, Sheeran, Svensson (DAMP 2012); Svensson & Svenningsson (FHPC 2014) | push and pull *arrays* | data push and pull | pull→push "cheap … subject to fusion"; push→pull "storing all elements to memory" |
| linear-base `Data.Array.Polarized` | push and pull arrays, linearly typed | data push and pull | conversions allocate nothing except `Push.alloc` |
| Kay (Balisage 2009) | push vs pull filters | codata | four push→pull costs: whole buffer, threads with a cyclic buffer, coroutines, JSP inversion |
| Hinze (SCP 2013); Hinze et al. (WGP 2012) | μ vs ν | the polarity crossings | μ→ν free; ν→μ needs a depth bound; a distributive law gives one arrow μF→νG two ways |
| Downen, Sullivan, Ariola, Peyton Jones (ESOP 2019) | data encoded as codata | data push (`WalkTree`) and data pull (`CaseTree`) as methods | none |
| Hancock, Pattinson, Ghani (LMCS 2009) | ν over μ | a productive processor with finite reads between writes | composition is cut elimination, lazy or greedy; no buffer |
| Gibbons (SCP 2007) | fold then unfold | the push→pull boundary | the streaming condition gives a one-place buffer instead of an unbounded one |

### 1.1 Lippmeier, Mackay, Robinson, "Polarized Data Parallel Data Flow", FHPC 2016

Read: http://benl.ouroborus.net/papers/2016-polarized/dpdf-FHPC2016-preprint.pdf (abstract, §2–§2.6,
§4).

- Abstract: "Our constant space guarantee is achieved by observing that binary stream operators
  can be provided in several polarity versions. Each polarity version uses a different combination
  of stream sources and sinks, and some versions allow constant space execution while others do
  not."
- §2.3: "The drainP operator requires no buffering because all data pulled from the source is
  immediately pushed to the sink. On the other hand, if we invert the polarities of drainP we
  arrive at the natural assignment for a primitive buffering operator. Any operator that accepts
  data via a single argument sink and produces the same data via a result source must introduce a
  buffer".
- §2.3: "the converse dup_iii operator is not implementable without requiring unbounded
  buffering."
- §2.5: "There are a total of 8 polarity versions for a 3-leg operator such as folds." Also: "We
  refer to a polarity version that can be expressed as a composition with drainP as an active
  version".

**For us.** This is `iteration-design.md` §4.2 with a different vocabulary:
- `drainP` is our drain, and the only "active" operator.
- The inverted `drainP` is our `buffer[k]`.
- Its polarity versions are the per-cell adapter question (§9 of the design).

It has no data/codata axis: every stream is effectful and of unknown length.

The companion paper (Lippmeier, Chakravarty, Keller, Robinson, Haskell 2013,
https://benl.ouroborus.net/papers/2013-series/flow-Haskell2013-rev1.pdf, related work) gives the
condition under which no buffer is needed: "every series in the cycle must have the same rate".
That is our capacity-1 class.

### 1.2 Bernardy & Svenningsson, "On the Duality of Streams: How Can Linear Types Help to Solve the Lazy IO Problem?"

Read: https://jyp.github.io/pdf/Organ-HaskeLL.pdf. This is the authors' later Hask-LL draft
(header "© 2016"), not the IFL 2015 proceedings copy. The Chalmers copy returned HTML. Read in
full, §1–§7.5.

In the quotes below, ⊸ is restored: extraction printed it as "(".

- **Types.** §3.2: `data Source a where Nil :: Source a; Cons :: a ⊸ N (Sink a) ⊸ Source a`.
  §7.5, in session-type form: `Source a = 1 ⊕ (a ⊗ N (Sink a))`, `Sink a = 1 ⊕ N (Source a)`.
- §1: "Sources provide data on-demand, while sinks decide when they are ready to consume data.
  This is an instance of the push/pull duality. In general, push-streams control the flow of
  computation, while pull-streams respond to it. We will see that this polarization does not need
  to match the flow of data: for example we support data sources with push-flavor, called
  co-sources (CoSrc)."
- §6.4: "In sum, we can classify streams according to polarity: • Pull: source and co-sinks •
  Push: sinks and co-sources We then have three situations when composing stream processors: 1.
  Matching polarities (one pull, one push). In this case behavior is synchronous; no concurrency
  appears. 2. Two pull streams. In this case an explicit loop must process the streams. … 3. Two
  push streams. In this case the streams must run in independent threads, and the programmer
  needs to make a choice for the communication buffer."
- §6.4: "Therefore, when programming with streams, one should consume push types when one can,
  and pull ones when one must. Conversely, one should produce pull types when one can, and push
  ones when one must."
- §7.3: "the need for buffering (or the scheduling opportunities) are clearly indicated by the
  type system, as mismatching polarities."
- §6.3, push→pull: `chanBuffer :: CoSrc a ⊸ Src a`, `boundedChanBuffer :: Int → CoSrc a ⊸ Src a`,
  `varBuffer :: a → CoSrc a ⊸ Src a`, each with threads.

**For us.** This is the closest source to our direction axis under linear types. Three points
carry over:
- **Direction is control, not dataflow.** A co-source pushes data the consumer asked for. This
  supports treating direction as its own axis.
- **Its cost table is ours, and it says when a crossing is free.** A drain is "matching
  polarities". A `zip` is "two pull streams" plus a loop. A push→pull boundary is "two push
  streams" plus a buffer, and on one thread that is our suspension.
- **Its rule of thumb is a design rule for our library:** consume push, produce pull. It says
  which cell an adapter should live in.

It has no μ/ν axis: `Nil`/`Full` end a stream, but finiteness is not typed.

One inconsistency in the source is reported as printed: the introduction says "sources cannot be
demultiplexed, but co-sources can", while §6.1 implements `dmux` on a `Src` and says
"multiplexing sources cannot be implemented while respecting synchronicity".

### 1.3 `pipes` (Gabriella Gonzalez), `Pipes.Core` and `Pipes.Tutorial`

Read: https://hackage.haskell.org/package/pipes/docs/Pipes-Core.html and …/Pipes-Tutorial.html.

- Core: "The Proxy type sits at the intersection of five separate categories, four of which are
  named after their identity". The table lists `respond`, `request`, `push`, `pull` and `return`.
- Core: "The respond category closely corresponds to the generator design pattern." `(/>/)`:
  "Compose two unfolds, creating a new unfold". "The request category closely corresponds to the
  iteratee design pattern." `(\>\)`: "Compose two folds, creating a new fold". "The pull category
  is the dual of the push category".
- Tutorial: "(for producer body) loops over (producer), substituting each yield in (producer) with
  (body)." And: "The return value of the input Producer matches the return value of the result,
  therefore for must loop over the entire Producer and not skip anything."

**For us.** `pipes` has all four compositions on one type, and `for` is respond composition (a
handler of `yield`). Its `for` **cannot stop early**, by its type. Early exit happens only through
pull composition (`>->`). That is a direct argument for putting `⊕ R` in the step rather than
reading `for` as a pure `yield` substitution (§7).

### 1.4 Push and pull arrays

- **Claessen, Sheeran, Svensson, DAMP 2012.** Read: https://svenssonjoel.github.io/writing/expressive.pdf
  (§1, §2, §2.1, §4).
  - §1: "The arrays described so far, with an indexing function and a length, have been nicknamed
    Pull arrays".
  - §2.1: "Going in the other direction, from a Push array to a Pull array, is a costly operation;
    it involves writing all the elements to GPU memory".
- **Svensson & Svenningsson, "Defunctionalizing Push Arrays", FHPC 2014.** Read:
  https://svenssonjoel.github.io/writing/defuncEmb.pdf (§1, §2.3, the conversion passage).
  - §1: "Push arrays, on the other hand, encode their own iteration schema … A consumer of a Push
    array provides a write-function that is instantiated into the body of the Push array's
    predefined iteration schema."
  - §1: "Some operations, like indexing, can be implemented efficiently for Pull arrays but not
    for Push arrays. Other operations, such as concatenation, are more efficient on Push arrays".
  - Conversion: "Converting a Pull array to a Push array is cheap and is also subject to fusion."
    And: "Converting a Push array to a Pull array, however, requires computing and storing all
    elements to memory."
- **linear-base 0.8.1, `Data.Array.Polarized`.** Read on Hackage.
  - "Polarized arrays are arrays with one of two polarities or directions: push or pull."
  - "A pull array is one that it's easy to "pull" from and read. These arrays work nicely as
    arguments to functions and we can fold, map, zip, and split these easily."
  - "A push array is a finished result that we do not want to allocate just yet."
  - `Pull.foldr :: (a %1 -> b %1 -> b) -> b %1 -> Array a %1 -> b` and
    `Pull.uncons :: Array a %1 -> Maybe (a, Array a)`.

**For us.** These fill the data row in both directions.
- Their pull array is our data-with-a-cursor (index plus length).
- Their push array is our push producer (a template over its consumer's write).
- The conversions cost the same as ours: pull→push is free and fuses; push→pull is a `collect`.
- Their operation split (index, zip, halve are "pully"; `++` and interleave are "pushy") is
  §9 of the design.
- linear-base's `Pull.uncons` is the data–pull eliminator for arrays. Its step is unrestricted
  (`->`), with linear arguments, which is our "step is `!`".

### 1.5 Kay, "You Pull, I'll Push: on the Polarity of Pipelines", Balisage 2009

Read: https://www.balisage.net/Proceedings/vol3/html/Kay01/BalisageVol3-Kay01.html. The first
fetch was refused, so it was re-fetched with a full browser User-Agent string that carried no
identifiers. Read: the sections on component styles, branching and merging, the push-pull
conflict, coroutines, and JSP inversion.

- "a push component can readily send its output to more than one destination, whereas a pull
  component can readily read data from more than one source. … By its nature, a push pipeline
  cannot handle multiple streamed inputs, nor can a pull pipeline handle multiple streamed
  outputs."
- "there is a polarity change from push to pull, and this is typically handled by allocating
  memory to hold the complete tree."
- "Handling the push-pull conflict using multiple threads … is actually overkill. … we don't
  really need threads at all: we need coroutines."
- JSP: "Jackson recognized that the intermediate file could be eliminated if, instead of the
  second phase of processing owning its own control loop, it were rearranged to be called by the
  first program every time another record became available. JSP refers to this rearrangement as an
  inversion. … inversion was a mechanical transformation of a program text that could be performed
  by a compiler."

**For us.** This is the most complete catalogue of push→pull costs. Its four costs map onto ours:
- a whole buffer is our `collect`;
- threads with a cyclic buffer are §4.5's channel;
- coroutines are our `suspend`;
- JSP inversion is our generator elaboration (SPEC §15: one state machine per body).

The fan-out/fan-in asymmetry is our `zip` pull, `unzip` push.

---

## 2. The push cells

### 2.1 Data–push: a fold, and a fold that stops

The design's K0′ step `S ⊗ A ⇒ S ⊕ E` is covered by §7. Two further sources bear on it.

**Obstinacy.** Colson's primary papers could not be fetched. A secondary summary was read:
Palazzo & Roversi, arXiv 2402.19012 (https://arxiv.org/pdf/2402.19012), p. 1.
- "Colson and others [Col96; CF98] studied the efficiency of Primitive Recursive Functions (PRF),
  proving their ultimate obstinacy property. It means that many algorithms cannot be efficiently
  implemented by any term of PRF."
- "LOOP is "obstinate" because its iterations cannot be interrupted as soon as necessary. They
  must unfold to their end … Matos shows how to tame LOOP "obstinacy" by extending LOOP with
  conditional breaks".

**For us:** SPEC §16 Open ("a finished state is carried to the bound") is this obstinacy, and the
`⊕ R` in the step is Matos's conditional break.

**Gibbons & Oliveira, "The Essence of the Iterator Pattern", JFP 2009.** Read:
https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf (abstract, §1, §4.1).
- §1: "An alternative INTERNAL ITERATOR approach assigns responsibility for managing the traversal
  to the collection instead of the client … it is not possible for the iteration to affect the
  order in which elements are accessed, nor to terminate the iteration early."

**For us:** `traverse` unifies lists, trees and arrays, but in the push cell only. The paper sets
the pull cell aside explicitly. It also names the two things push lacks: early exit, which a
`⊕ R` step recovers, and order control, which only descent gives.

### 2.2 Codata–push: yield to a sink

Covered by §1.2 (sinks and co-sources), §1.3 (`pipes`' respond category) and §7 (handlers).
Kiselyov's iteratees are the consumer side of this cell.

**Kiselyov, "Iteratees", FLOPS 2012.** Read: https://okmij.org/ftp/Haskell/Iteratee/describe.pdf
(abstract, §1–§3).
- §2: "data I a = Done a | GetC (LChar → I a)"
- §2: "One may think of en pair as 'splitting' (or duplicating) the stream. In reality en pair
  does no copying or buffering: it receives a chunk and passes it to its two argument iteratees."
- §3: "en str s (Done x) ≡ return (Done x) regardless of s."

**For us:** the law `en s (Done x) = return (Done x)` is "a stopped step is never fed again",
which a linear `S ⊕ R` makes a typing fact. Fan-out to two consumers is free in push (Kay's
asymmetry again).

---

## 3. The pull cells

### 3.1 Codata–pull: `next`

Our cell is `νX. C` with `unfold` (SPEC §7). Two sources refine it.

**Downen, Sullivan, Ariola, Peyton Jones, "Codata in Action", ESOP 2019.** Read:
https://www.pauldownen.com/publications/esop2019.pdf (§1, §2.1–§2.2, §3).
- §2.2: "the main obstacle is that the control of how to drive the next step of the
  algorithm—whether to continue or not—lies with the consumer."
- §3: "Note how this encoding differs from the one that was given in Section 2.1 since the
  CaseTree method is non-recursive whereas the WalkTree method was recursive, in order to model a
  depth-first search traversal of the tree."

**For us:** `CaseTree` (one match) and `WalkTree` (a visitor, i.e. a fold) are our data–pull and
data–push cells, both exposed as codata methods. Data–pull is one unrolling, handed to the
consumer.

**Downen, Johnson-Freyd, Ariola, "Structures for Structural Recursion", ICFP 2015.** Read:
https://pauldownen.com/publications/structure-recursion.pdf (§1, §4, §4.1, §4.2).
- §1: "the copattern approach [2, 3] represents inductive types as data and co-inductive types as
  co-data."
- §4: "Even worse, the "infinite data structures" in Example 3 do not have as clear of a concept
  of "termination:" zeroes and concatenation could go on forever, if they are not given a bound to
  stop."
- §4.2 gives a sized codata type. Extraction printed ⊢ as a backtick; it is restored here:
  `codata Stream(i : Ord, a : ?) by noetherian recursion on i where Head : | Stream(i, a) ⊢ a;
  Tail : | Stream(i, a) ⊢_{j<i} Stream(j, a)`.

**For us:** an index-bounded codata type is the typed form of our codata→data crossing (fuel,
`take`, `driveE n`). `iteration-design.md` §6.8 already records Agda's sized types and does not propose them.

### 3.2 Data–pull: descent, and gap (a)

**The proof rule: frame away the processed prefix.**

**Tuerk, "Local Reasoning about While-Loops", VSTTE 2010 Theory Workshop.** Read:
https://privat.thomas-tuerk.de/assets/talks/vstte10.pdf, the whole 6-page paper; it prints no page
numbers.
- §1, the loop specification for list length:
  ```
  loop_spec [list(t,data)] {
      while (t != NULL) { t = t->tl; r = r + 1; }
    } [list(old(t),data) * (r = old(r) + length(data))]
  ```
  With: "The list-segment between c and t is handled implicitly."
- §2, the rule (the rule bar is written `——`):
  ```
  LOOP SPECIFICATION RULE
  ∀x. {¬c ∧ P (x)} p2 {Q(x)}
  ∀x, prog. ∀y. {P (y)} prog {Q(y)} −→ {c ∧ P (x)} p1 ; prog {Q(x)}
  ——
  ∀x. {P (x)} while c do p1 done; p2 {Q(x)}
  ```
  With: "The extended while rule allows to choose for each loop iteration a different
  instantiation. So, I is still some kind of inductive property of the loop, but strictly speaking
  no invariant any more."
- §3.1: "As a rule of thumb, loop invariants express what the loop has already done, whereas loop
  specifications express what it will still do." And, for arrays: "pre: array(a + i, n − i, data)
  post: array(a + old(i), n − old(i), map (+1) data)".
- §3.4: "For lists, the partial datastructure is a list-segment and for arrays it is an array."

Tuerk's thesis (Cambridge TR UCAM-CL-TR-799, 2011, https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-799.pdf,
§2.3.2–2.3.3, p. 35) states the same rule as a translation to recursion:
- "A program while cond prog1; prog2 can easily be translated in a new recursive function whilefun
  with body if cond { prog1; whilefun } else prog2."
- On an iterative tree sum: "Most tools use complicated constructs like the magic-wand operator.
  Holfoot can avoid this by using a loop specification and local reasoning".

The formal HOL rules on p. 82 did not survive extraction and are not quoted.

**Charguéraud, CFML.**
- "Characteristic Formulae for the Verification of Imperative Programs", ICFP 2011, §3.7. Read:
  https://www.chargueraud.org/research/2011/cfml/main.pdf.
  - "At every iteration of this loop, one cell is traversed. This cell may be framed out from the
    reasoning about the subsequent iterations, thanks to the assumption "islocal R". Such an
    application of the frame rule makes it possible to verify the list trasversal using only the
    simple list representation predicate, avoiding the need to involve the listsegment
    representation predicate."
  - The for-loop formula indexes the loop's relation by the counter, `∀S. (∀i. islocal (S i)) ∧ …`.
- "Separation Logic for Sequential Programs (Functional Pearl)", ICFP 2020, §6. Read:
  https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf.
  - "Doing so would not be possible with a reasoning rule that imposes a loop invariant to be
    valid both at the entry point and exit point of the loop body. Indeed, such a loop invariant
    would necessarily involve the description of a list segment."
  - Intro: "The inductive reasoning rule for loops allows applying the frame rule over the
    remaining iterations of a loop. This rule typically saves the need to introduce list segments
    or tree contexts in the statement of loop invariants."

**The alternative: a magic wand for the prefix.**

**Schwerhoff & Summers, "Lightweight Support for Magic Wands in an Automatic Verifier", ECOOP 2015.**
Read: LIPIcs 37:614–638 (Dagstuhl PDF), §1–§2.
- §2.2: "this magic wand instance represents the following promise: "if you give up permission to
  the remainder of the list (starting from xs), I will give you back permission to the entire list
  structure (starting from ys)"."
- Fig. 3 caption: "The magic wand instance covers permissions to the prefix of the list (starting
  at ys) that has already been traversed by the loop."

**For us.** There are two ways to type a descent's state.
- **Invariant style.** The state holds the rest *and* a give-back for the prefix
  (`rest ⋆ (rest −∗ whole)`). That is a borrow of the tail whose expiry returns the whole list,
  and every iteration re-packages the wand one level deeper. This is exactly our nesting of
  `withload` scopes, one per step.
- **Specification style** (Tuerk, Charguéraud). The loop is read as tail recursion over the rest,
  and each iteration instantiates the spec at a different `x`. The prefix is never named.

The second style is available to us whenever the prefix need not be *returned*: for an owned
list whose cells are consumed, and for a push fold. For a *borrowed* list, the prefix is what the
lender gets back. That is gap (b), and §5 takes it up.

**The owned implementation: consume and reuse.**

**Hofmann, "A type system for bounded space and functional in-place update", Nordic J. Computing
7, 2000.** Read: http://web.cs.ucla.edu/~palsberg/tba/papers/hofmann-njc00.pdf (abstract, §1, §2.1,
§3). Extraction printed ◊ as "3"; it is restored here.
- §3, p. 12, rule List-Elim: "Γ ⊢Σ e : L(A)   ∆ ⊢Σ enil : B   ∆, d:◊, h:A, t:L(A) ⊢Σ econs : B
  ⟹ Γ, ∆ ⊢Σ match e with nil⇒enil | cons(d, h, t)⇒econs : B"
- §2.1: "The destructor function list destr() … returns a structure containing … head and tail of
  l, as well as a pointer to a heap location capable of storing a list node (d). … must not
  anymore refer to the argument of list destr; it has been “destroyed”."

**Lorenzen, Leijen, Swierstra, "FP²: Fully in-Place Functional Programming", ICFP 2023.** Read:
https://webspace.science.uu.nl/~swier004/publications/2023-icfp.pdf (abstract, §1.1–§1.3, §2, §3).
- Abstract: "We describe a linear fully in-place (FIP) calculus where we prove that we can always
  execute such functions in a way that requires no (de)allocation and uses constant stack space."
- §1.2: "the reuse of the zipper nodes corresponds to the usual "pointer-reversal" techniques
  [Schorr and Waite 1967]".
- §3: "A tzipper<a,b> stores fragments of the input tree in-order … We can now map over the tree
  in-order without using heap- or stack space by reusing the tzipper nodes." §3.1: "the zipper is
  just the defunctionalization of the closures".
- §2, on `bmatch`: "the borrowed match bmatch can only match on borrowed variables and such match
  can only be used to inspect values without creating fresh reuse credits."

**McBride, "Clowns to the Left of me, Jokers to the Right" (POPL 2008 pearl; the 2007 preprint
was read).** Read: http://strictlypositive.org/CJ.pdf (abstract, §1, §4.1).
- Abstract: "fold-like operations over the recursive data structure it induces can be expressed by
  tail recursion alone."
- §4.1: "The point, after all, is to turn a higher-order recursive program into a tail-recursive
  machine. We need some kind of stack."

**McBride, "I Got Plenty o' Nuttin'", 2016.** Read:
https://personal.cis.strath.ac.uk/conor.mcbride/PlentyO-CR.pdf, §5.
- "ω lit : (0 X : ∗, 0 P : (0 x : List X) → ∗) → (1 n : P (nil X)) → (ω c : (1 x : X, 0 xs : List
  X, 1 p : P xs) → P (cons X x xs)) → (1 xs : List X) → P xs"
- "In the cons case the tail xs has been reconsituted as p but remains contemplated in types."

**For us.** For an **owned** list, descent is already expressible cell by cell. `unroll` and a
consuming load give the head and the owned rest; that is Hofmann's `list_destr` without the ◊.
With `foldReuse`'s `Ref 1` hole it becomes ◊ itself. What is missing is only a **driver**. A
consumer-driven loop needs a bound, and with data the bound is the data: descent runs at most
`size` steps.

These sources give two shapes for that driver:
- **Left to right** (FP²'s `reverse-acc`, a loop in the tail position): the step gets the head and
  the loop keeps the rest. This is §9's C2.
- **Right to left with the rest in scope** (a paramorphism). The step gets the tail at usage 0 and
  the recursive result at 1 (McBride's `lit`); Meertens's `para` is the unrestricted version.
  - **Meertens, "Paramorphisms", Formal Aspects of Computing 4, 1992.** Read:
    https://www.kestrel.edu/people/meertens/publications/papers/Paramorphisms.pdf; a scan with
    noisy OCR.
  - §1: "it is essentially the same as the standard pattern used in the so-called elimination
    rules for a data type in constructive type theory".

Dissection (McBride) is the general statement: every fold over a polynomial functor has a
tail-recursive machine whose stack is a list of dissections. For a list, that stack is the
reversed prefix. It is the same object as the magic wand's prefix, as data.

---

## 4. Crossings and their costs

| crossing | our operation | prior art, with its stated cost |
|---|---|---|
| pull → push | drain | Lippmeier `drainP`: "requires no buffering"; Bernardy–Svenningsson: "Matching polarities … synchronous; no concurrency" |
| push → pull | `through`, `buffer[k]`, `collect`, `suspend` | Lippmeier: "must introduce a buffer"; Bernardy–Svenningsson: threads and a buffer; Kay: four costs (§1.5); Claessen et al.: "writing all the elements to GPU memory" |
| data → codata | forget finiteness | Hinze (SCP 2013) §9: "The initial algebra can always be embedded in the final coalgebra, using either a fold or an unfold"; Hinze et al. (WGP 2012) §2: "we can always go the other way and embed the least into the greatest with a function upcast" |
| codata → data | fuel, `take` | Hinze (SCP 2013) §9: "The other way round has to be programmed explicitly, which typically involves imposing some depth bound to ensure termination"; WGP 2012: "in general this is a lossy operation" |
| push+push → one pull (`zip` of two folds) | `suspend` one side | Launchbury et al.: hyperfunctions `H a b = H b a -> b`, "Clearly no set-theoretic solution exists"; Hinze (SCP 2013) §5.4: "The two arguments of x are destructed in lock-step … it should be sufficient to focus on one argument" |

### 4.1 Gibbons, "Metamorphisms: Streaming Representation-Changers", SCP 2007

Read: https://www.cs.ox.ac.uk/jeremy.gibbons/publications/metamorphisms-scp.pdf, the Elsevier
preprint of 10 January 2005 (abstract, §1, §3.1, §3.3, §4.1, §4.4, §7.1–§7.2).

- Abstract: "A metamorphism is the opposite composition, an unfold after a fold … under certain
  conditions fusion is possible: some of the work of the unfold can be done before all of the work
  of the fold is complete."
- §4.1, Definition 1: "The 'streaming condition' for f and g is: for all a, b, c and c′, f c = Just
  (b, c′) ⇒ f (g c a) = Just (b, g c′ a)". And: "In other words, 'the next output produced' is
  invariant under consuming another input."
- §4.1: "The left-hand side is a two-stage copying process with an unbounded intermediate buffer,
  and the right-hand side a one-stage copying queue with a one-place buffer."
- §3.3, sorting: "there is no hope for streaming: the second phase cannot possibly make any
  progress until the entire input is read".
- §4.4: "The streaming process should therefore switch into a final 'flushing' phase when all the
  input has been consumed."
- §7.1: "List-oriented streaming relies essentially on foldl, which does not generalize in any
  straightforward way to other datatypes."

**For us.** A metamorphism is a push consumer (a fold) feeding a pull producer (an unfold), which
is exactly our push→pull boundary. The streaming condition is a **checkable law** under which that
boundary needs a one-place buffer instead of a `collect`.

Our `through` covers the case where one step emits at most one output (a Mealy stage). The
streaming condition covers a stage whose state accumulates (radix conversion, a reformatter) but
whose next output is stable under more input. The flushing phase is our `close` and the finishing
value of a `gen`. Sorting is the canonical crossing that must `collect`.

### 4.2 Hinze et al., a distributive law between fold and unfold

**Hinze, James, Harper, Wu, Magalhães, "Sorting with Bialgebras and Distributive Laws", WGP 2012.**
Read: https://www.cs.ox.ac.uk/ralf.hinze/publications/WGP12.pdf (§1–§3.2).
- §2: "This suggests that a and c are both instances of some function s :: F (G x) → G (F x) that
  is parametric in x."
- §3: "we will read its type as a so-called distributive law—it distributes the head of a list
  over the head of an ordered list."
- §3.2: "given a distributive law such as swap, there are two ways to turn it into a sorting
  function, µList → νList: as a fold of an unfold, and an unfold of a fold. … There is a unique
  arrow from initial to final, and our two sorting algorithms are simply dual ways of describing
  it."

**Hinze, Wu, Gibbons, "Conjugate Hylomorphisms", POPL 2015.** Read the preprint,
https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Hylomorphisms.pdf, §1.
- "we can restrict ourselves to so-called recursive coalgebras [6]—those that by definition yield
  unique solutions to the hylo equation, whatever the algebra."

**For us.** A natural transformation `s : F(G x) → G(F x)` gives one arrow `μF → νG`, computed
either push-first (a fold whose algebra unfolds) or pull-first (an unfold whose coalgebra folds).
This is the only printed *distribution law* between our two rows that we found. It concerns
polarity, not borrowing.

For iteration it says: a data→codata pipeline stage (an `iter` built from a list) has two
elaborations, and they agree when the stage is a distributive law. A hylomorphism (codata producer,
data consumer) is total without fuel exactly when the producer is a recursive coalgebra. This is a
typing condition we do not have; we have fuel.

### 4.3 Hancock, Pattinson, Ghani, "Representations of Stream Processors Using Nested Fixed Points", LMCS 2009

Read: https://arxiv.org/pdf/0905.4813 (Introduction, §1.2, §3, §4, §5).

- Intro: "inductive and coinductive definitions are sometimes nested within each other (as in (ν
  X) (µ Y ) B × X + Y^A )". Extraction flattened the exponent `Y^A`.
- §3: "T_A B = (µ X) B + X^A" and "P_A B = (ν X) T_A (B × X)."
- §4: "Can we directly program such an r from p and q? Yes! In fact, in at least two different
  ways, one 'lazy', or demand driven, and the other 'greedy', or data driven. The computation is
  reminiscent of cut-elimination in proof theory".
- §4.1: "In this form of composition, priority is given to the postponent's desire to produce
  output. No input is consumed until both the postponent and preponent are reading."
- §4.1: "Unfortunately we currently have little of substance to say about how these forms of
  composition are related."

**For us.** `νX. μY. (A → Y) + (B × X)` is a pipeline stage whose run of reads between two writes
is **data** (`μ`, finite), inside a codata (`ν`) of writes. That is F4 ("a generator's skips are
unbounded") fixed by type: a `filter`-like stage over a finite input has finitely many skips
before each output, and the μ makes that a type fact.

The two compositions are our two directions:
- lazy composition is pull;
- greedy composition is push.

Both need no buffer, because composition is cut elimination on the trees. See §9's C5.

### 4.4 Launchbury, Krstic, Sauerwein, "Coroutining Folds with Hyperfunctions", EPTCS 129, 2013

Read: https://arxiv.org/pdf/1309.5135 (§2–§6, §8, §10).
- §3.3: "It became accepted folklore that zip cannot be defined as a fold on both branches at the
  same time. While this is true if we are restricted to ground terms or first-order functions, it
  is not true if we move to the the world of hyperfunctions."
- §4.1: "the general form of the type equation that needs to be solved is H a b = H b a -> b …
  Clearly no set-theoretic solution exists for these".
- §3.2: "while foldr and foldl are mutually definable on flat structures such as arrays, they are
  not at all dual in the world of partial structures such as lazy lists."
- §10: "In stream fusion, lists are represented as (non-recursive) state-machine stream
  processors, and it turns out to be quite feasible to fuse these state-machines together,
  including for the case of zip."

**For us.** `zip` of two push producers needs a type with `X` on the left of its own arrow, which
is outside our positivity for both `μ` and `ν`. So `zip` stays in the pull cell, as the design
already has it. The §3.2 remark is our situation exactly: for arrays, foldl and foldr are both
available (a counted loop in either order); for lists only the right fold is primitive.

---

## 5. Borrowed sources: the distribution law each cell needs, and gap (b)

### 5.1 The laws, per cell

Borrowing is a modality on the source. For each cell, the law needed for `Imm 'a` of a source is:

| cell | law needed for a borrowed source | arrays today | lists today | nearest prior art |
|---|---|---|---|---|
| data–push | the step receives each element view at one lifetime `'x`, and the result may mention `'x` | yes: `slice_borrow_imm` lends `[Imm 'x A]`; `array_get` hands out `Imm 'x A` at the family's lifetime | `foldImm`: each level at a fresh `'y`, so `R` must outlive every lifetime | RustHorn `P ∘ own = P`; RustBelt S-deref-bor-own |
| data–pull | the rest of the view has one type across steps: `Imm 'x (rest) → 1 ⊕ (Imm 'x A ⊗ Imm 'x (rest))` | yes: `slice_split_imm` at the family's lifetime | no: the tail view is one level deeper each step | Aeneas: fixpoint "up to loan and region identifier substitution"; NLL: reassignment kills the old loans |
| codata–pull | an element lent per observation, dead at the next | the per-observation lend (SPEC §14) | same, once a list iterator exists | Swift SE-0516: element lifetime ends "on the next call to `nextSpan()`" |
| codata–push | the element lent for one call of the step | array push over `count_fold` | through `foldImm` only | Hylo yield-once subscripts; Swift SE-0474 |

In both codata rows, what the prior art says the per-element borrow costs is that `R` may not
capture the element. SE-0516: "a method like `first(where:)` cannot be implemented in an extension
on `Iterable`, because the selected element's lifetime is tied to the iterator created within the
method." In both data rows the element can escape into `R`, and only at the family's lifetime.
That is exactly what arrays have and lists lack.

### 5.2 What other systems do at `&'a Box<Node> → &'a Node`

**RustBelt (Jung, Jourdan, Krebbers, Dreyer, POPL 2018).** Read:
https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf (§4.2–§4.3), the appendix
https://plv.mpi-sws.org/rustbelt/popl18/appendix.pdf (§5.1, the typing rules), and Jung's thesis
https://research.ralfj.de/phd/thesis-screen.pdf (ch. 9 pp. 127–128, ch. 12 p. 190).

- Appendix, instruction rule S-deref-bor-own, with premise `κ alive`. It concludes that
  dereferencing `p ◁ &κ_μ own_n τ` gives `x ◁ &κ_μ τ`: the same κ. The companion
  S-deref-bor-mut, with `κ ⊑ κ'`, gives `&κ_μ τ` from `&κ_μ &κ'_mut τ`: the outer κ. The
  extraction garbled the rule glyphs, so the rule is given here as structure, not quoted.
- Appendix §5.1: "a shared reference to an owned pointer or mutable reference consists of two
  parts: First of all, the outer pointer is shared. This is a straight-forward fractured borrow
  such that everybody gets a read-only permission to dereference the outer pointer."
- Thesis ch. 12, p. 190: "The solution, then, is to “delay” executing ty-share: delayed sharing …
  Effectively, when we share a data structure with lots of nested owned references, sharing of the
  inner parts (the ones behind a pointer indirection) is done lazily."
- Thesis ch. 9, p. 128: "And if the inner reference is instead an owned pointer, then it does not
  even have a lifetime to worry about."

**What pays for it.** `own τ`'s sharing predicate at κ is a fractured borrow of the outer cell at
κ, plus a view shift that produces `τ.shr(κ, …)` at the **same** κ one step later. The ▷ is paid by
the physical dereference.

This is `docs/prior-art-borrow-splitting.md` §2.2's structure, applied down a pointer chain rather
than across a product. The model reads ownership per location, so a shared view of the whole list
is a fractured borrow at each cell. That is the array family's shape.

**RustHorn (Matsushita, Tsukada, Kobayashi, ESOP 2020).** Read: https://arxiv.org/pdf/2002.09002
(§3, Example 4).
- The deref rule: "let y = ∗x : (Γ+{x: P P′ T}, A) → (Γ+{y: (P∘P′) T}, A)" with "P ◦ own = own ◦ P
  := P".
- Example 4, `take_some<'a>(mxs: &'a mut List) -> &'a mut i32`: the recursive call on the tail is
  at the same `'a`. "A crucial technique used here is subdivision of a mutable reference".

**RustHornBelt (Matsushita, Denis, Jourdan, Dreyer, PLDI 2022).** Read:
https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf (§2, §3.1).
- "fn next<𝛼,T>(it: &mut IterMut<𝛼,T>) -> Option<&𝛼 mut T>" and "With iterated application of
  next, it is possible to convert the mutable iterator into a bunch of mutable references to the
  individual elements of the vector, which can all be used simultaneously".

**NLL, RFC 2094.** Read: https://raw.githubusercontent.com/rust-lang/rfcs/master/text/2094-nll.md
("Problem case #4", "Reborrow constraints").
- Problem case #4: "This most commonly arises when writing a loop that progressively "walks down" a
  data structure."
- "we compute the supporting prefixes of `lv_b`, and find every deref lvalue `*lv` in the set where
  `lv` is a reference with lifetime `'a`. We then add a constraint `('a: 'b) @ P`".
- "whenever we see an assignment `lv = <rvalue>` in MIR, we can clear all loans where the borrowed
  path `lv_loan` has `lv` as a prefix."

A `Box` deref is not a reference with a lifetime, so it adds no constraint. A reborrow asks
`'a: 'b`, which is outlives-or-equal, not strictly shorter.

**Polonius.** Read: https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/.
- "'a – which I will be calling a region – instead corresponds to a set of loans".

**Aeneas.** Read: Ho & Protzenko, ICFP 2022 (https://arxiv.org/pdf/2206.07185, §2–§4), and Ho,
Fromherz, Protzenko, ICFP 2024, long version (https://arxiv.org/pdf/2404.02680, §5.2, App. F).
- (2022) Fig. 4 caption: "Boxes behave like regular ADT constructors".
- (2024) §5.2: "its reborrow inside a loop is a characteristic pattern when iterating over
  recursive data structures in Rust". Also: "using state inclusion to determine if a given state is
  a fixpoint is not sufficient … Our main observation is that it is actually sufficient to consider
  a fixpoint up to loan and region identifier substitution."
- (2024) §5.2: "we do not claim that our approach terminates."

Each `&mut` step mints a fresh loan and region abstraction, as ours does. The loop state gets one
type because the fixpoint is taken up to renaming of those identifiers, and the old abstractions
are merged into one.

**Prusti (Astrauskas, Müller, Poli, Summers, OOPSLA 2019).** Read:
https://pm.inf.ethz.ch/publications/AstrauskasMuellerPoliSummers19.pdf (§4.2–§4.3).
- "the separation logic magic wand connective … lets us formally model the remainder capabilities
  resulting from a reborrow".
- "We use similar techniques to handle reborrows inside loops (for example, when a Rust reference
  is used to traverse a recursive heap data structure) in order to generate the required loop
  invariants at the Viper level completely automatically."

**Cyclone (Grossman et al., PLDI 2002).** Read:
https://www.cs.umd.edu/projects/cyclone/papers/cyclone-regions.pdf (§2.2–§2.3).
- "struct Lst<ρ1 ,ρ2 > { int*ρ1 hd; struct Lst<ρ1 ,ρ2 > *ρ2 tl; };"

The tail stays in region ρ2 at every step.

**Mezzo (Pottier & Protzenko, ICFP 2013).** Read:
http://gallium.inria.fr/~fpottier/publis/pottier-protzenko-mezzo.pdf (§2.2–§2.3).
- "in the tail-recursive approach, the “loop invariant” is the type of the recursive function …
  This type is reasonably natural and does not involve list segments."

**Oxide (Weiss, Gierczak, Patterson, Ahmed, arXiv 1903.00982).** Read §3.4–§3.5 and §4.
- Oxide has no `Box`, and its evaluation excludes "(1) heap allocation". It types a loop by an
  environment invariant under the body, with provenances as loan sets.

### 5.3 BoLo itself

The ACM PDF returned a Cloudflare challenge. The repository copy of `[CONF]` (`3764117.pdf` in
`borrow_lang`) was read instead: §2.4–§2.5, Fig. 8, Fig. 13b, §4.1, §4.4 and §5.

- Fig. 8: "Δ ⊢ withload : Imm a T1 ⊸ (∀ 'b < ⊓Δ. Imm 'b T1 ⊸ ['b] T2 ) ⊸ T2" and "Imm 'b (Ref T) ≜
  Imm 'b T      Imm 'b (Imm a T) ≜ Imm a T" and "Imm 'b (Mut a T) ≜ Imm 'b T". The first `Imm`
  on each left-hand side is the reborrow operator `Imm̲`; extraction dropped the underline.
- §2.4: "withload … forbids nested linear references from being accessed at full strength;
  instead, they will only be accessible as new immutable borrows."
- §2.4: "in the case of a nested borrow, aliases to the inner borrow Imm a T are allowed to exist
  anyway".
- §4.4: "its exclusive locations are marked imm at the given lifetime 𝛼 and its imm locations are
  preserved at their original lifetimes." Rule ⟲M keeps an `imm` cell at its own lifetime set.
- §5: "Pure constructs, like records or variants, would be straightforward to add … though one
  would likely wish to add corresponding reborrowing rules."

The type grammar has no `μ`, and the text does not discuss iterating a list.

**What this means for gap (b).** BoLo prints a fresh lifetime at a *linear* `Ref` or `Mut` under
an `Imm`. It prints no fresh lifetime at an *existing* `imm` cell. Our list is
`μX. 1 ⊕ (A ⊗ Ref X)`, so its tail is a linear `Ref`, and our `Imm̲` at `μ`
(`docs/scope-recursion.md` §2.4) keeps the payload of `Imm 'b L` unreborrowed. That clause is
forced by clause (5), and it is what makes the next level need another `withload`.

The question the prior art raises is therefore not whether BoLo's relation is stricter than
RustBelt's. It is whether **our choice of how a borrowed list is viewed** forces a view per level,
where a view that reborrows the whole spine once would not. RustBelt answers this with a sharing
predicate defined per type. BoLo's own machinery has one relevant piece: `reb_α` (`[TR]` p. 5)
already turns each owned cell of a witness into its own `imm` cell at α
(`docs/prior-art-borrow-splitting.md` §0). §9's C3 states this as a hypothesis.

Nothing in this section is derived.

---

## 6. Linearity and usage

The user's question: are we using linearity and usage? Four sub-questions follow, with what the
literature says on each.

### 6.1 Is totality a finite grade on the step?

**Girard, Scedrov, Scott, "Bounded Linear Logic", TCS 1992.** Read:
https://www.site.uottawa.ca/~phil/papers/BLL.1992.pdf; a scan with poor OCR.
- §1, p. 5: "BLL features bounded-reuse operators !ₓA, which intuitively mean that the datum A is
  stored in the memory and may be referenced up to x times." The subscript is restored.
- §5, p. 31: "Our definition of Nₓ follows the same pattern, except that access to the “successor”
  function is allowed only up to x times".
- Lemma 6.2 (the Iteration Lemma) is OCR-garbled. Its step premise has an empty left-hand side,
  so the step is closed; the lemma text is not quoted.

**Dal Lago & Hofmann, "Bounded Linear Logic, Revisited", LMCS 2010.** Read:
https://arxiv.org/pdf/0904.2675 (§2.8–§2.9).
- p. 14: "there is a proof πpA of Np , !y<p (A{y/x} ⊸ A{y + 1/x}), A{0/x} ⊢ A{p/x}."
- §2.9: "in presence of unbounded quantification, QBAL would immediately become unsound."

**Orchard, Liepelt, Eades, "Quantitative Program Reasoning with Graded Modal Types", ICFP 2019.**
Read: https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf (§2–§3, §8–§9), and the
Granule StdLib `Vec.gr` on GitHub.
- StdLib: `foldr : forall {a b : Type, n : Nat} . (a -> b -> b) [n] -> b -> Vec n a -> b`.
- §9: "we can combine grading with indexed types to give an even more precise specification for
  map as ∀ a b : Type, n : Nat . (a → b) [n] → Vec n a → Vec n b." On an unindexed list the type is
  "(a → b) [] → List a → List b".

**Brunel, Gaboardi, Mazza, Zdancewic, "A Core Quantitative Coeffect Calculus", ESOP 2014.** Read:
https://www.cis.upenn.edu/~stevez/papers/BGMZ14.pdf (§2, Fig. 2).
- Rule fix: "[Γ], x : [A]p ⊢ e : A   1 + q·p ≤ q ⟹ q·[Γ] ⊢ fix x.e : A". And: "Note that for every
  p ∈ R the element ∞ satisfies this condition."

**For us.** Yes, in a precise and limited sense.
- A step whose grade is the data's length is a finite grade, but only when the length is in the
  type (`N_x`, `Vec n`).
- Unrestricted recursion forces ∞ (BGMZ's `1 + q·p ≤ q` has no finite solution in ℕ for p ≥ 1).
- With our unindexed `μ`, the grade is an existential `n`, which QBAL's §2.9 warns about.

So "push over data is total, pull over codata is ω" is expressible as grades. It would cost
length-indexed types, which the design already declined (`iteration-design.md` §6.8, Agda sized types). Our
existing statement, that the fold's structure bounds its step, says the same thing without
indices.

### 6.2 Can a graded step capture a linear resource?

In every system read, no.
- Granule's promotion rule `pr`: "[Γ] ⊢ t : A ⟹ r · [Γ] ⊢ [t] : □r A", "requires that all the
  input requirements for t are provided r times over" (§3, p. 110:8).
- Linear Haskell (Bernardy et al., POPL 2018, https://arxiv.org/pdf/1710.09756), §3, rule app:
  "if the multiplicity π on u’s function arrow is ω, then the function consumes its argument not
  once but ω times, so all u’s free variables must also be used with multiplicity ω." Its `foldl`
  threads a linear array: "Thus each call to write returns a (logically) new array, so that the
  array is single-threaded, by foldl, through the sequence of writes" (§2.2).
- Hofmann, "Linear types and non-size-increasing polynomial time computation", Inf. & Comp. 2003
  (read via scholar.archive.org). §4.1, p. 63: "If h0 or h1 increase the size by a constant (as
  would be the case if they were allowed to contain variables) then itN(g, h0, h1) would multiply
  the size by that constant".
- Alves, Fernández, Florido, Mackie, "Linear Recursion" (https://arxiv.org/pdf/1001.3368), §1:
  "System L … captures exactly the class of primitive recursive functions (PR), if iterators use
  only closed linear functions".
- Tang, Hillerström, Lindley, Morris, "Soundly Handling Linearity", POPL 2024
  (https://arxiv.org/pdf/2307.09383), §2.2: "a control-flow-linear context can capture linear
  resources; a control-flow-unlimited context cannot."
- Clean Language Report 2.2, ch. 9, §9.4.1: "it is not permitted to discard its uniqueness".
- Rust's `FnMut` captures by `&mut`, a borrow, not by grade.

**For us.** F5 (closures capture only `!` values) is the literature's rule, not a gap. A step
entered `n` times needs its captures `n` times over. The two ways around it are ours already:
- thread the resource through the state;
- or, as a candidate, lend it to the step for each call (Rust's `FnMut`, FP²'s borrowed `^f`).

A `for` body elaborated in place (F5's last sentence) is a control-flow-linear context per
iteration, which is why it may touch what the loop threads.

### 6.3 Does linearity give in-order descent of an owned list?

Yes. See §3.2: Hofmann's List-Elim with `d:◊`, FP²'s `match!` and `reverse-acc`, and Perceus's
FBIP. Perceus (Reinking, Xie, de Moura, Leijen, PLDI 2021, https://xnning.github.io/papers/perceus.pdf,
§2.6): "the visitor structure is effectively overlaid over the tree nodes while traversing the
tree."

What this gives us is the **owned** half of gap (a), with no borrow. It also gives in-place
rebuilding when the step's output replaces the element, which is FP²'s `map` and our `foldReuse`
read left to right.

### 6.4 Are shot-ness and capacity grades?

- **Shot-ness is.** Tang et al. annotate each operation's continuation linear or unlimited ("An
  operation signature 𝐴 ↠𝑌 𝐵 is annotated with a linearity 𝑌"). OCaml 5 (Sivaramakrishnan et al.,
  PLDI 2021, https://arxiv.org/pdf/2104.00250, §3.1): "This also holds true for other use cases
  such as generators and coroutines. Hence, our continuations are one-shot".
  `docs/ideas-handlers-and-borrows.md` already has this table (0: exit, 1: generators, ω:
  backtracking), and the literature agrees with it.
- **Capacity: partly.** FP² has `fip(n)` ("allows the function to allocate at most a constant n
  constructors"), and Hofmann's ◊ is a per-cell token. No source read frames a buffer's capacity
  as a usage grade; that framing is ours. Kiselyov et al.'s "linear stream" (design §6.10) is
  the nearest: one output per state advance.

---

## 7. `for` as a driving effect, and why it reduces to a loop with an exit

### 7.1 The handler reading

- **`pipes`**: `for producer body` substitutes each `yield` with `body` (§1.3). It is respond
  composition, and it cannot stop early.
- **Koka** (book, https://koka-lang.github.io/koka/doc/book.html):
  - §2.3's generator is `ctl yield(i : int) : bool` and the producer
    `Cons(x,xx) -> if yield(x) then traverse(xx) else ()`.
  - §3.4.3: "when the operation is a tail-resumptive fun, it calls it directly as a regular
    function … there is no need to yield upward to the handler, capture the stack, and eventually
    resume again. This gives fun (and val) operations a performance cost very similar to virtual
    method calls".
  - §3.4.11: `finally` "is always executed when either returning normally, or when unwinding for a
    non-resuming operation."
- **OCaml 5** manual, ch. 24 (https://ocaml.org/manual/5.2/effects.html):
  - §24.4: "The invert function takes an iter function (a producer that pushes elements to the
    consumer) and returns a sequence (where the consumer has the control)."
  - §24.5: "Not resuming continuations will leak the memory allocated for the fibers as well as any
    resources that the suspended computation may hold."
- **Ullrich & de Moura, "'do' Unchained", ICFP 2022** (https://lean-lang.org/papers/do.pdf):
  - §4: "The main translation rule (D5) introduces two exception effects using runCatch: one for
    break outside, and one for continue inside a call to a collection-polymorphic forM".
  - §5.2: "Even after specializing a forM instance, the specialized function would still allocate
    transient pairs for storing the updated mutable variables, and Except objects. … We addressed
    this issue by using CPS versions of StateT and ExceptT monad transformers."

**For us.** A loop body resumes the producer once, immediately (continue), or never (break).
- The first is Koka's tail-resumptive `fun`: a direct call.
- The second is an exit. With the result returned *to the producer* as `⊕ R`, it is a direct
  call too, and the producer runs its own finaliser on that branch.

A continuation is captured only at a push→pull inversion (OCaml's `invert`), which is our
`suspend`. So the handler reading adds nothing a step `S ⊗ A ⇒ S ⊕ R` does not already give. The
Koka example is that step with `S = 1` and `R = 1`. Lean's paper shows the naive `Except` encoding
allocated per iteration until specialization and CPS removed it; our specialization (SPEC §14)
is that step.

### 7.2 Source-driven loops with an early-exit step

| system | step | who finalises on exit | read at |
|---|---|---|---|
| Kiselyov, "Towards the best collection API" | `seed -> val -> Either seed seed` | the enumerator | okmij.org/ftp/papers/LL3-collections-enumerators.txt |
| Lean 4 `ForIn` | `α → β → m (ForInStep β)` | the instance | `src/Init/Core.lean`; reference manual, Iteration |
| Rust `try_fold` | `FnMut(B, Item) -> R: Try<Output = B>` (`ControlFlow<R, B>`) | nobody: `&mut self`, "resumable after hitting an error" | doc.rust-lang.org |
| Clojure `reduced` | a tagged accumulator | the process calls completion "exactly once" | clojure.org/reference/transducers |
| Racket `for` | `#:break`, `#:final` guards; `call/ec` | the form | docs.racket-lang.org |
| Common Lisp `loop` | `while`/`until` (run `finally`), `thereis`/`return-from` (skip it) | `unwind-protect` | CLHS §6.1.4 |
| Zig | `break v`; `else` on exhaustion | the loop | ziglang.org documentation, §while, §for |
| Haskell | `foldr` with a lazy second argument; `foldlM` in `Either` | GC | `Data.Foldable` |

Quotes:
- **Kiselyov**, abstract: "This article presents a design of the overall optimal collection
  traversal interface, which is based on a left-fold-like combinator with premature termination.
  We argue from the practical standpoint that such an interface is superior: in efficiency; in ease
  of programming; in more predictable resource utilization and avoidance of resource leaks."
  - "If the iteratee returns Left seed'', the enumerator immediately stops further iterations,
    frees all the resources, and returns seed'' as the final result."
  - "Like cursors and streams, generators are demand-driven. … Therefore, like cursors generators
    leak resources: it is not clear when the iteration should be assumed terminated".
- **Lean**, `Init/Core.lean`: "`ForInStep.done` is produced by uses of `break` or `return` in the
  loop body." And: "`ForInStep.yield` is produced by `continue` and by reaching the bottom of the
  loop body."
- **Rust**, `ControlFlow`: "Used to tell an operation whether it should exit early or go on as
  usual." `try_fold`, Note to Implementors: "This is a &mut self method, so iteration needs to be
  resumable after hitting an error here."
- **Rust internals**, "More about step_by" (https://internals.rust-lang.org/t/more-about-step-by/12436,
  posts 6–11, May 2020):
  - CAD97: "Rust cannot desugar … to use try_fold … because control flow of try_fold is controlled
    by the user and thus unreliable."
  - steffahn describes a fix with a non-`Clone` state token, so the loop "cannot continue executing
    the loop anymore after the first time it did break or return".
- **Clojure**: "If a step function returns a reduced value, the transducible process must not
  supply any more inputs to the step function." And: "a transducer step function that uses a nested
  reduce must check for and convey reduced values when they are encountered. (See the
  implementation of cat for an example.)"
- **CLHS §6.1.4**: "Since always, never, and thereis use the return-from special operator to
  terminate iteration, any finally clause that is supplied is not evaluated when exit occurs due to
  any of these constructs."
- **Zig**: "break, like return, accepts a value parameter. This is the result of the while
  expression. When you break from a while loop, the else branch is not evaluated."
- **`Data.Foldable`**: "if any of the (f e) ignore their second argument, the fold stops there, with
  the remaining elements unused."

**For us.** Four points:
- **The shape is established.** Our `S ⊗ A ⇒ S ⊕ R` generalises Kiselyov's `Either seed seed` and
  Lean's `ForInStep β` to a separate exit type. Lean puts `return`'s value into the state; a
  separate `R` does not need that.
- **The obligation "stop feeding after exit" is a protocol everywhere else,** enforced by nobody
  (Rust, Clojure) or by convention (Lean). With `S` linear and the step's `R` branch holding no
  `S`, it is a typing fact. That removes the one objection to lowering `for` to the internal
  loop.
- **Finalisation belongs to the producer on both branches** (Kiselyov). A `⊕ R` exit must hand
  back or drop what the producer holds (the rest of an owned list, a `gen`'s residual). Rust's
  `&mut self` keeps the iterator, and Lisp needs `unwind-protect`, because neither says who owns
  the rest.
- **Adapters are step → step,** and a nested source must convey the exit (Clojure's `cat`). That
  is `flat_map`'s obligation in B′ (design §7.2).

### 7.3 Borrowing the element for one step

- **Hylo spec**, §Yield statements (https://raw.githubusercontent.com/hylo-lang/specification/main/spec.md):
  "Control comes back to the subscript once after the last use of the yielded projection at the
  call site". And §for: "The loop iterates over all elements produced by the iterator, unless it is
  exited early via a break or a return statement."
- **Swift SE-0474**, "Yielding accessors": "it must be possible for the compiler to guarantee there
  is exactly one yield on every path."
- **Swift SE-0516**, "Iterable": "the elements accessed via that span also have an exclusive access
  dependency, with lifetimes ending on the next call to `nextSpan()`".
- **Rust GATs stabilization post** (blog.rust-lang.org, 2022-10-28), on a lending `Filter`:
  "error[E0499]: cannot borrow `self.iter` as mutable more than once at a time … This is a known
  limitation in the current borrow checker".

**For us.** A push step `S ⊗ Imm 'y A ⇒ S ⊕ R`, with `'y` fresh per call and `S`, `R` free of
`'y`, is the yield-once projection without a coroutine: the producer keeps its frame and calls the
step. A lending `filter` is a problem in pull (Rust) and not in push, because the borrow is scoped
to one call. This is the cell where our `foldImm` restriction (`R` outlives every lifetime) is
already the right law for the element: the element dies with the step. What it must not also
forbid is `R` mentioning the *family's* lifetime (§5.1).

---

## 8. Lists and arrays as one thing

- **Reynolds, "Separation Logic", LICS 2002** (https://www.cs.cmu.edu/~jcr/seplogic.pdf, §5, §7).
  - §5: "list a·α (i, k) = ∃j. i → a, j ∗ list α (j, k)" and "list α·β (i, k) ⇔ ∃j. list α (i, j)
    ∗ list β (j, k)".
  - §7: "Somewhat surprisingly, iterated separating conjunction is useful for making assertions
    about structures that do not involve arrays. For example, the connection between our list and
    Bornat's listN is given by list α (i, j) ⇔ ∃σ. #σ = #α ∧ (listN σ (i, j) ∗ …". The iterated-∗
    operator after it did not survive extraction.
- **Tuerk**, §3.4: "For lists, the partial datastructure is a list-segment and for arrays it is an
  array." His rule frames both the same way (§3.2).
- **RustBelt** reads ownership per location, and a shared view of an owned chain is a fractured
  borrow per cell (§5.2).
- **FP²'s `bmatch`**: the children of a borrowed scrutinee join the flat borrowed set Δ. That set
  is not indexed by lifetime.
- **Our own proof** (read in this repository): `wpTS_I_frameList` (`Core/SliceFrames.lean:283`)
  is stated for an arbitrary `I : List Loc` and a per-location leaf type `T : Loc → VTy`. It
  frames one Imm Frame per location, each at its own lifetime strictly below the last, with the
  callback below all of them. Nothing in its statement asks the locations to be consecutive.

**For us.** The literature's answer to "arrays and lists the same" is the iterated separating
conjunction over the cells, with the links as values (Reynolds's `listN`). SPEC §9 already reads
an array as `⊛_{i<n}`.

What separates a list from an array in our model is not the location arithmetic. It is that the
owned list's relation at `Ref X` owns the next node. So a per-node leaf view whose witness is
"this node's element" does not follow from `Imm̲` as it stands. The frame-list proof accepts any
list of locations, if there is a leaf type whose relation stops at the link. §9's C3 states this.

---

## 9. Candidate pretty ideas

These are **hypotheses**. None is derived, none has been tried in Lean, and no obstruction to any
of them has been verified. Each states what would have to be checked and what it would cost. They
are ordered by cost, cheapest first, and the first two follow the user's "it's just a loop with
early exit".

### C1. One loop shape, one constant per cell: `S ⊗ A ⇒ S ⊕ R`, with the producer finalising the exit

**Statement.** Every driving construct takes a persistent step `!(S ⊗ A ⇒ S ⊕ R)`, a first
state, and the source. It answers `S ⊕ (R ⊗ Rest)`: the last state on exhaustion, or the exit with
whatever of the source is not consumed, handed back. The instances:

| cell | constant | `Rest` | totality |
|---|---|---|---|
| count, owned array, borrowed family | K0′ `count_try` over the length | `1` (the array is threaded in `S`, or is a family view) | total |
| owned `μ` | `list_try` (C2) | the unconsumed owned tail | total, by size |
| codata | a drain with exit | the source's `close` residual after `close` | div |

- Adapters are `step → step`. A nested source conveys its inner exit (Clojure's `cat`).
- `for x in V { M }` elaborates to the constant of `V`'s cell, with `break e` as `inr` and the
  loop's `else` as the `S` branch (Zig).
- `M`'s own effects (I/O, errors) are not part of `R`. They escape by forwarding, as a body's
  effects do today.

**What to check.**
- The step's `inr` branch holds no `S`. That is "stop feeding" as a typing fact (§7.2).
- `count_try`'s machine step exits on `inr`, and its `wp` is `countLoop_wp` with one more case.
- The codata drain runs `close` on exit (SPEC §7's destructor path).

**Cost.**
- `count_try`: one machine step and one compatibility lemma, as K0 cost (SPEC §16).
- The drain: library code over `unfold` and `close`.
- `list_try`: see C2.
- The elaboration of `for` per cell: frontend only.

**Prior art:** Kiselyov, Lean `ForIn`, Rust `try_fold` and the internals thread, Clojure,
Zig (§7.2).

### C2. Descent with exit on owned `μ`, left to right, by consuming cells

**Statement.** For `L = μX. 1 ⊕ (A ⊗ Ref X)`:

    list_try : !(!(S ⊗ A ⇒ S ⊕ R) ⊗ (L ⊗ S) ⇒ S ⊕ (R ⊗ L))

- Each step unrolls the head cell, loads it, and frees it: Hofmann's `list_destr`.
- It hands the element to the step, and continues on the tail or exits with the tail.

A `foldReuse`-shaped variant hands the emptied cell back with the step's output, so a map
rebuilds in place: FP²'s `reverse-acc`, or its tree zipper, in the general case. For `Mut 'a L`,
`withswap` takes the list out, runs the rebuilding variant, and stores the result back.

**What to check.**
- Totality: by the list's size, as `foldOwn`'s termination is (SPEC §6).
- The loop state never mentions the prefix. Tuerk's rule is the proof shape: the `wp` is a
  specification over "the rest", instantiated at each step's tail, not an invariant with a
  segment.
- Whether it is derivable from `foldOwn`. The left fold via a right fold builds `U(S ⊸ F(S ⊕ R))`
  closures, one per node, that capture the node's element. F5 forbids that capture, and the
  closures allocate. So it is expected to be a constant, not derivable. **Not verified.**

**Cost.** A constant with its machine step or Z-term, its `CDerives` rule, and one compatibility
lemma by induction on the size. No kernel type change. It fills gap (a) for owned and `Mut`-swapped
lists, and for trees only through a zipper type, which C2 does not include.

### C3. A borrowed list is a family of node views at one lifetime

**Statement.** Borrowing an **owned** list lends its spine as a family, as `slice_borrow_imm`
lends an owned array:

    list_borrow_imm : List A ⊸ (∀'x ⊏ ⊓Δ. LView 'x A ⊸ ['x] B) ⊸ List A ⊗ B

`LView 'x A` has one type at every depth:
- `next : LView 'x A ⇒ 1 ⊕ (Imm 'x A ⊗ LView 'x A)` is descent with a fixed state type;
- `array_get`'s analogue hands out `Imm 'x A` at the family's lifetime.

Two routes to its soundness, both unverified:
- **(a) Frames per node.** Use `wpTS_I_frameList` over the spine's locations. The missing piece
  is a leaf type whose relation at node `k` owns the element and **not** node `k+1`: the link read
  as an address, as in Reynolds's `listN`. The frame lemma's statement does not require
  consecutive locations (§8).
- **(b) One `withload`, deep.** A view type for `μ` in which a recursive `Ref X` position is read
  as a view of the reborrowed tail at the same `'b`, instead of `Imm 'b L`. Its soundness would
  rest on `reb_α` turning each owned cell of the witness into its own top-level `imm` cell at α.
  That is the same per-location shape as the array family, and RustBelt's sharing predicate for
  `own τ` is the precedent. It must be checked against `imm_view_rejected`. That lemma excludes a
  view below an *existing* `imm` cell; whether a reborrow image made at one `withload` is such a
  view is the question to settle.

**What it would give.** Gap (b) for lists, in both `μ` cells:
- `foldImm` with a result that may mention `'x`;
- descent with a fixed state type;
- a list iterator whose state is `LView 'x A` (SPEC §7 Open, lifetime-indexed iteration).

It would also make a list and an array the same thing from iteration's point of view: a family of
leaf views at one lifetime.

**Cost.**
- (a): a new view type former (or an abbreviation over an address type, which BoCa does not
  have), its relation clause, and a frame-list proof over a linked spine. A `VTy` former costs
  about 100 match arms across `Core/` (`CLAUDE.md`, growth discipline).
- (b): a kernel change to `Imm̲` at `μ`, plus 6.131 at the new clause
  (`docs/scope-recursion.md` §2.4 names that proof as the main risk of `μ`).
- Either route must first be checked against `experiments/FrameEnd`. **This is the one candidate
  that could fail on a model fact, and whether it does is not known.**

### C4. The crossing law: matched polarities cost nothing; a mismatch costs the step's output multiplicity, or the streaming condition

**Statement.**
- A composition whose polarities match (a pull source into a push consumer, i.e. a drain) needs
  no buffer (Bernardy–Svenningsson case 1; Lippmeier's `drainP`).
- A push→pull boundary needs a buffer of capacity equal to the most outputs one step of the push
  stage can emit (design §4.2).
- For an accumulating stage (Gibbons's metamorphism), capacity 1 suffices exactly when the
  streaming condition holds.
- Library rule: consume push, produce pull (Bernardy–Svenningsson §6.4).

**What to check.**
- That the `boundaries` count (design §4.4) is invariant under the choice between `through` and a
  streaming stage.
- Which of `lib/adapters.bc`'s stages meet the streaming condition.

**Cost.** Nothing in the kernel. At most a derived type for "at most `k` outputs" (a bounded family
or `B ⊕ 1` nested `k` times), and a library annotation. This is mostly a *name and a law* for what
the design already does.

### C5. A productive generator as `ν` over `μ`

**Statement.** Type a stage that reads a finite input between outputs as
`νX. μY. (reads ⇒ Y) ⊕ (B ⊗ U X) ⊕ …` (Hancock–Pattinson–Ghani). The skips between two outputs
are then data, and each "next element" is a total computation.
- It fixes F4 by type for `filter`-like stages over a data input.
- Its two compositions (lazy, greedy) are pull and push, and neither needs a buffer.

**What to check.**
- The relation at a nested fixed point: `μ` inside a `ν` observation, which SPEC §7's `NuOk`
  excludes ("X is never under … a μ").
- Whether `unfold`'s map along `X`'s positions extends through a `μ`.
- Whether the two compositions agree. The authors say: "we currently have little of substance to
  say about how these forms of composition are related."

**Cost.** A kernel change: positivity for `ν` and the relation at `μ`-inside-`ν`, with
`fundamentalC` re-checked. This is the most expensive candidate, and it buys only the typing of
productivity.

### Considered and not proposed

- **`for` as a handler of `yield`.** It reduces to C1 (§7.1). Handlers are needed only at an
  inversion, which is `suspend`.
- **Graded steps.** A finite grade on the step needs length indices. A graded step cannot capture
  linear resources (§6.1–§6.2). What survives is the vocabulary: 0/1/ω for exit, generator and
  backtracking continuations.
- **Hyperfunctions for `zip` of two folds.** Outside our positivity (§4.4).
- **Aeneas's fixpoint up to region renaming.** It gives a borrowed-list loop one state type by
  quotienting lifetimes, but in a symbolic checker, with no termination claim. In our setting, the
  same effect is C3's single lifetime.
- **A distributive-law elaboration of data→codata stages** (Hinze et al.). It is correct and it
  concerns polarity only; it does not touch the gaps.

---

## 10. Not read, or not verified

Nothing is taken from these.

- **Blocked or failed fetches.**
  - The ACM PDFs: BoLo (the repository copy was read instead), Conjugate Hylomorphisms (preprint
    read), Granule (author copy read), FP² (author copy read), Prusti (ETH copy read), Xie et
    al., "Effect handlers, evidently" (ICFP 2020), and Xie & Leijen, "Generalized evidence
    passing" (ICFP 2021).
  - Meijer, "Your Mouse is a Database" (403).
  - Creusot (HAL block page).
  - Bruggeman, Waddell & Dybvig (PLDI 1996).
  - Tree Borrows.
  - Veedrac's post on Rust iterators (quoted only second-hand, in the internals thread).
  - The Chalmers copy of Bernardy & Svenningsson (the later draft was read).
- **Garbled, so structure only.**
  - Tuerk's formal HOL loop rules (thesis p. 82).
  - The BLL storage rule and the full text of the Iteration Lemma.
  - RustBelt's S-deref rules.
  - Meertens's para formula.
- **Not attempted.**
  - Munch-Maccagnoni.
  - Zeilberger's thesis (only the abstract of "On the unity of duality" was read; it has no
    sentence on iteration).
  - Hinze, Magalhães & Wu, "A duality of sorts".
  - conduit.
  - Kammar, Lindley & Oury, "Handlers in Action".
  - Effekt's stream library beyond the design's §6.5.
  - Hillerström & Lindley on shallow handlers.
  - Scala capture checking.
  - Vale.
  - Protzenko's thesis.
  - Blom & Huisman.
  - Danvy & Nielsen.
  - Linear zippers in Linear Haskell or Rust.
  - Colson's primary papers (a secondary summary was read).
- **Verus** (https://arxiv.org/pdf/2303.05491) was read and has no passage on iterating a
  borrowed list.
- **Racordon et al.** (JOT 2022) was read and has no material on `yield` or subscripts.
- **No follow-up by Wagner, Ahmed or Marshall** on borrowing and recursive types was searched for.
