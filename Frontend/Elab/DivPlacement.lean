/-!
# Frontend — Elab — the placement of ticks  `[spec §14]`

The `Div` elaboration (`Frontend/Sugar.lean`, *The `Div` elaboration*) places a tick where an
observation of the loop value the previous elaboration made ended (SPEC §14, *The placement*).
This module states that placement over the schema of div bodies and proves that the two agree:
for every run of a body, the loop value of the new elaboration (`reify` of it) and the loop value
of the previous one (the per-body state machine) have the same segments, the same events in each,
and the same ends (`sim_loop`).

**The schema.** A run of a div body is the path one execution takes through it (`Run`): the
events it performs in order (an operation of its row, a call of an extern), the loops it enters
with the run of each turn, the calls in direct style it makes (of a div function placed as it is,
of one placed for the empty row from a body at a row, or of a loop written in core), and how it
ends. A turn ends at its back edge (`next`), leaves its loop for what follows (`exit`, a `break`
or the loop's end), or leaves the body (`ret`, a `return` from inside the loop). A run is finite:
an infinite run is the limit of its prefixes, each of which is the prefix of a finite run, and
both elaborations' traces are computed prefix by prefix.

**The traces.** A loop value's observable behaviour along a run is its *trace*: the events of
its creation, then, for each observation, a boundary followed by the events of that observation.
The two elaborations are transcribed as functions from runs to traces:

* `oldTrace`, the per-body state machine (the elaboration before B2, `mGoto`, `mCall`, `dret`,
  `mAssemble`): at the empty row the body runs its code up to its first point when it is called,
  every move to a loop's head or to a call is a skip (a boundary), a move to a join is a call,
  and a terminal before any point is the loop that finishes at its first observation; at a row
  the body runs nothing when called, a move forward is a call, and a move back to a loop's head is
  a skip. A call is a point whose observations observe the callee's loop.
* `newTrace`, the `Div` elaboration and `reify`: a tick is a boundary. At the empty row the body
  ticks at each move forward to a loop's head (`eIter`), at each back edge (`iterate`'s own), and
  before a terminal before any loop or call (`eFinish`); `reify` runs the body to its first tick.
  At a row the body ticks only at back edges, and the loop value of a call starts with a back edge
  (`eStart`). A call at the body's placement is a call; one placed for the empty row from a row,
  and a loop written in core, are drained (`eDrain`): the loop value's observations are the
  drain's turns, so its boundaries, but the first, are the drain's back edges.

`sim_loop` is `oldTrace = newTrace` at both placements, for every run. It is a statement about
the placements as these functions transcribe them; that the kernel terms each elaboration emits
have these traces is the content of the transcriptions, not of this theorem.
-/

namespace Frontend.Elab.DivPlacement

/-- The trace of a loop value: events `ev a`, and the boundary `bd` that ends one observation and
starts the next. -/
inductive Tr (α : Type) where
  | ev (a : α)
  | bd
  deriving DecidableEq, Repr

mutual
/-- One run of a div body, the path an execution takes. -/
inductive Run (α : Type) where
  /-- The body finishes: a terminal. -/
  | fin
  /-- An event, then the rest. -/
  | ev (a : α) (k : Run α)
  /-- A loop, entered: the runs of its turns, the last of which leaves it; then, when the last
  turn leaves the loop (not the body), what follows. -/
  | loop (ts : Turns α) (k : Run α)
  /-- A call in direct style of a div function placed as the caller is: the callee's run, then
  what follows. -/
  | call (r : Run α) (k : Run α)
  /-- A call, from a body at a row, of a div function placed for the empty row: the callee's
  run, then what follows. -/
  | cross (r : Run α) (k : Run α)
  /-- A call of a loop written in core, drained: its observations (the events of each, the last
  finishing it), then what follows. -/
  | core (obs : List (List α)) (k : Run α)

/-- The runs of a loop's turns: each but the last goes back to the head. -/
inductive Turns (α : Type) where
  /-- The last turn: it leaves the loop. -/
  | last (t : Turn α)
  /-- A turn that ends at the back edge, then the next ones. -/
  | more (t : Turn α) (ts : Turns α)

/-- One turn of a loop. -/
inductive Turn (α : Type) where
  /-- The end of the body, or `continue`: the back edge. -/
  | next
  /-- `break`, or the loop's end: what follows the loop runs. -/
  | exit
  /-- `return`: the body finishes from inside the loop. -/
  | ret
  | ev (a : α) (k : Turn α)
  | loop (ts : Turns α) (k : Turn α)
  | call (r : Run α) (k : Turn α)
  | cross (r : Run α) (k : Turn α)
  | core (obs : List (List α)) (k : Turn α)
end

variable {α : Type}

open Tr

/-- A loop written in core, drained: its observations' events, a boundary between two. -/
def coreTr : List (List α) → List (Tr α)
  | [] => []
  | [o] => o.map ev
  | o :: os => o.map ev ++ bd :: coreTr os

/-- A trace without its first boundary: the events before it, then the rest. -/
def dropFirst : List (Tr α) → List (Tr α)
  | [] => []
  | bd :: t => t
  | ev a :: t => ev a :: dropFirst t

/-! ### The previous elaboration: the per-body state machine -/

mutual
/-- The trace of the machine of a body along a run. `row`: the body is at a row. `pre`: no point
has been reached (the code runs when the function is called, at the empty row). -/
def oldRun (row pre : Bool) : Run α → List (Tr α)
  -- A terminal before any point, at the empty row, is the loop that finishes at its first
  -- observation (`dret`); otherwise it finishes the observation it is in.
  | .fin => if pre && !row then [bd] else []
  | .ev a k => ev a :: oldRun row pre k
  -- A loop's head: at the empty row the move to it is a skip (before any point, the end of the
  -- call); at a row a move forward is a call.
  | .loop ts k => (if row then [] else [bd]) ++ oldTurns row ts (oldRun row false k)
  -- A call is a point holding the callee's loop. At the empty row the callee's code before its
  -- first point runs at the call, and the move to the point is a skip: the callee's loop value,
  -- the point's skip in place of its creation's end. At a row the move is a call, and the point
  -- observes the callee at once: its loop value without its creation's end.
  | .call r k =>
    (if row then dropFirst (bd :: oldRun row false r) else oldRun row true r) ++ oldRun row false k
  -- A call of an empty-row function at a row: its code before its first point runs at the call,
  -- and the point observes it at once.
  | .cross r k => dropFirst (oldRun false true r) ++ oldRun row false k
  -- A call of a loop written in core: a point observing it.
  | .core obs k => (if row then [] else [bd]) ++ coreTr obs ++ oldRun row false k

/-- The trace of a loop's turns, then `after`, what follows the loop when it leaves it. -/
def oldTurns (row : Bool) : Turns α → List (Tr α) → List (Tr α)
  | .last t, after => oldTurn row t after after
  -- The move back to the head is a skip.
  | .more t ts, after => oldTurn row t (bd :: oldTurns row ts after) after

/-- The trace of one turn: `next` goes on to `back`, `exit` to `after`, `ret` finishes. -/
def oldTurn (row : Bool) : Turn α → List (Tr α) → List (Tr α) → List (Tr α)
  | .next, back, _ => back
  | .exit, _, after => after
  | .ret, _, _ => []
  | .ev a k, back, after => ev a :: oldTurn row k back after
  | .loop ts k, back, after =>
    (if row then [] else [bd]) ++ oldTurns row ts (oldTurn row k back after)
  | .call r k, back, after =>
    (if row then dropFirst (bd :: oldRun row false r) else oldRun row true r) ++ oldTurn row k back after
  | .cross r k, back, after => dropFirst (oldRun false true r) ++ oldTurn row k back after
  | .core obs k, back, after => (if row then [] else [bd]) ++ coreTr obs ++ oldTurn row k back after
end

/-- A body's loop value in the previous elaboration: at the empty row its code before its first
point is its creation; at a row it runs nothing when called. -/
def oldValue (row : Bool) (r : Run α) : List (Tr α) :=
  if row then bd :: oldRun row false r else oldRun row true r

/-! ### The `Div` elaboration -/

mutual
/-- The ticks of the `Div` elaboration of a body along a run (`eWalk`), at a row or not, `pre`
before any loop or call. -/
def newRun (row pre : Bool) : Run α → List (Tr α)
  -- `eFinish`: at the empty row, a tick before a terminal that no loop or call precedes.
  | .fin => if pre && !row then [bd] else []
  | .ev a k => ev a :: newRun row pre k
  -- `iterate`, entered after a tick at the empty row (`eIter`).
  | .loop ts k => (if row then [] else [bd]) ++ newTurns row ts (newRun row false k)
  -- A call at the body's placement is a call: the callee's ticks are the caller's (`eCall`).
  | .call r k => newRun row (!row) r ++ newRun row false k
  -- `reify` of the call runs it to its first tick, and the drain observes the rest (`eDrain`),
  -- its first turn with no tick before it, at a row.
  | .cross r k => dropFirst (newRun false true r) ++ newRun row false k
  -- The drain of a loop written in core (`eDrain`): entered after a tick at the empty row.
  | .core obs k => (if row then [] else [bd]) ++ coreTr obs ++ newRun row false k

def newTurns (row : Bool) : Turns α → List (Tr α) → List (Tr α)
  | .last t, after => newTurn row t after after
  -- `iterate`'s tick at the back edge.
  | .more t ts, after => newTurn row t (bd :: newTurns row ts after) after

def newTurn (row : Bool) : Turn α → List (Tr α) → List (Tr α) → List (Tr α)
  | .next, back, _ => back
  | .exit, _, after => after
  | .ret, _, _ => []
  | .ev a k, back, after => ev a :: newTurn row k back after
  | .loop ts k, back, after =>
    (if row then [] else [bd]) ++ newTurns row ts (newTurn row k back after)
  | .call r k, back, after => newRun row (!row) r ++ newTurn row k back after
  | .cross r k, back, after => dropFirst (newRun false true r) ++ newTurn row k back after
  | .core obs k, back, after => (if row then [] else [bd]) ++ coreTr obs ++ newTurn row k back after
end

/-- A body's loop value in the `Div` elaboration: at the empty row, `reify` of it, which runs it to
its first tick; at a row, `reify` of its start (`eStart`), whose first back edge comes before any
event. -/
def newValue (row : Bool) (r : Run α) : List (Tr α) :=
  if row then bd :: newRun row false r else newRun row true r

/-! ### The agreement -/

mutual
/-- The traces of a body agree on every run, at both placements and at every `pre`. -/
theorem run_eq (row pre : Bool) : ∀ r : Run α, oldRun row pre r = newRun row pre r
  | .fin => by simp [oldRun, newRun]
  | .ev a k => by simp [oldRun, newRun, run_eq row pre k]
  | .loop ts k => by simp [oldRun, newRun, turns_eq row ts, run_eq row false k]
  | .call r k => by
    cases row <;> simp [oldRun, newRun, dropFirst, run_eq false true r,
      run_eq true false r, run_eq false false k, run_eq true false k]
  | .cross r k => by simp [oldRun, newRun, run_eq false true r, run_eq row false k]
  | .core obs k => by simp [oldRun, newRun, run_eq row false k]

theorem turns_eq (row : Bool) : ∀ (ts : Turns α) (after : List (Tr α)),
    oldTurns row ts after = newTurns row ts after
  | .last t, after => by simp [oldTurns, newTurns, turn_eq row t]
  | .more t ts, after => by simp [oldTurns, newTurns, turn_eq row t, turns_eq row ts]

theorem turn_eq (row : Bool) : ∀ (t : Turn α) (back after : List (Tr α)),
    oldTurn row t back after = newTurn row t back after
  | .next, _, _ => by simp [oldTurn, newTurn]
  | .exit, _, _ => by simp [oldTurn, newTurn]
  | .ret, _, _ => by simp [oldTurn, newTurn]
  | .ev a k, back, after => by simp [oldTurn, newTurn, turn_eq row k]
  | .loop ts k, back, after => by simp [oldTurn, newTurn, turns_eq row ts, turn_eq row k]
  | .call r k, back, after => by
    cases row <;> simp [oldTurn, newTurn, dropFirst, run_eq false true r,
      run_eq true false r, turn_eq false k, turn_eq true k]
  | .cross r k, back, after => by simp [oldTurn, newTurn, run_eq false true r, turn_eq row k]
  | .core obs k, back, after => by simp [oldTurn, newTurn, turn_eq row k]
end

/-- **`sim_loop`**: along every run of a div body, at the empty row and at a row, the loop value of
the `Div` elaboration (`reify` of the body, or of its start at a row) has the trace of the loop
value of the per-body state machine: the same events, in order, in the same observations, with
the same ends. Under `div_fuel n`, which observes a loop value `n` times, or a pull consumer, which
sees each observation, the two give the same answers and the same effects in order.  `[spec §14]` -/
theorem sim_loop (row : Bool) (r : Run α) : oldValue row r = newValue row r := by
  cases row <;> simp [oldValue, newValue, run_eq]

end Frontend.Elab.DivPlacement
