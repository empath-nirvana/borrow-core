import Frontend.Syntax

/-!
# Frontend — Elab — the pipe connector's glue  `[spec §75]`

A stream chain `s₀ ∘ s₁ ∘ … ∘ s_{n−1}` runs on one connector, assembled per chain from
`lib/pipe.bc`'s pieces (SPEC §75 Part B, Assembly(n) §1): `pipe_step`, `pipe_stop` (through
`pipe_with_stop`), `pipe_with_stop`, `pipe_handoff`, `pipe_forward` and `pipe_finish`, each a
definition over one stage's or one wire's types, used here at the stage's types, rows and sites.
This module writes only the **glue**, as core text:

* the tuple of the stage states and the running stage with its input, a sum over the stages;
* the frame lists, each nested `pipe_with_stop`s, the most downstream innermost, in one cancel
  region at the site `c` (`core-pipe-close`'s form): `close_others_i` around `pipe_step` of `i`,
  `close_all` around `pipe_forward`, and `close_up_i`, the region of `stop()` by `i`, whose first
  error, reified outside it, the stage raises at its `stop()`, under `close_down_i`, the frame list
  of `i` and the stages downstream of it, for a cancel from outside. The frames are shared: one function per stage
  and direction installs that stage's frame around the rest of the chain (`io_dn{j}`, `io_up{i}`),
  and each list is one region around one such chain, so the frames are linear in the stages;
* per-stage getters and setters (`io_get{i}`, `io_set{i}`), between turns only, so that a turn
  touches the states of the stages it changes and no others;
* one `unfold` whose turn calls the running stage's `pipe_step` and dispatches on its event,
  as Assembly(n) §1's glue does, and whose close is `close_all`.

The glue has no pipe semantics of its own: every stage's state is taken, stored and stopped by a
piece, and the kernel checks each piece's instance. The types, rows and sites are what the typed
elaboration read off each stage as elaborated (`Stage`); nothing here infers them.
-/

namespace Frontend.Elab.Connector

/-- An abortive operation of a site whose errors a stage's `stop()` raises, in the handler that
reifies them: its payload's type and its summand of `KP` (SPEC §75).  `[spec §75]` -/
inductive Reify where
  | pay (A : String) (k : Nat)
  deriving Inhabited

/-- One stage as the typed elaboration read it, each type and row printed as core text: the items
`A` and end `K` of the wire into it, the items `B` of the wire out of it, its result `R`, its
forwarded operation's argument `OA`; its rows (SPEC §75, `lib/pipe.bc`): `sg` what it performs
besides its sites, `cy`, `cn`, `cp`, `cf` the cancel rows of its four operations, `lr`, `lc` its
loop's turn and close rows; its sites; and its state before it runs, its loop (`ready`).  `[spec §75]` -/
structure Stage where
  A : String
  K : String
  B : String
  R : String
  OA : String
  sg : String
  cy : String
  cn : String
  cp : String
  cf : String
  lr : String
  lc : String
  y : Nat
  s : Nat
  f : Nat
  ready : String
  /-- The outer operation it forwards: its site and its cancel row, as the chain's row has it. -/
  fwd : Option (Nat × String) := none
  /-- The payloads of its own abortive operations, a sum of `np` summands, `0` with none: its
  `stop()` answers `1 + KP`, `inr` the first error of the region that closed its upstream, which
  it raises at its `stop()` (SPEC §75).  `[spec §75]` -/
  KP : String := "0"
  np : Nat := 0
  /-- The sites of the upstream's abortive operations whose first error its `stop()` raises, the
  innermost first: each with its operations' payload types and their summands of `KP`, and the row
  of that handler's answer, the region's cancel row without the sites handled so far.
  Payloads own nothing today; under #1061 the answer owns the payload, and its one raise at the
  `stop()` consumes it.  `[spec §75]` -/
  reify : List (Nat × List Reify × String) := []
  /-- The last stage of a generator's chain: the site of the `Yield` around the chain and its
  operation's cancel row, at which the connector performs each item under `close_all`.
  `[spec §75]` -/
  gen : Option (Nat × String) := none
  deriving Inhabited

/-- A chain: its stages, the region's site `c` and its operation's cancel row `cc` (what any stage
performs when stopped, each operation once: a region's call is the computation of an `unwind`, whose
row has each operation once), the row `G` the chain runs at, and a suffix that makes its local names
its own.  `[spec §75]` -/
structure Conn where
  stages : List Stage
  c : Nat
  cc : String
  G : String
  sfx : String
  /-- The chain is a `for`'s generator: the `for`'s site, the variable it threads and its type. The
  glue performs the site's operation with each item of the last stage, `(b, w)`, answering the next
  `w`, which it keeps between turns and never across that operation.  `[spec §75]` -/
  out : Option (Nat × String × String) := none
  /-- `connect(CHAIN)`: the chain answers its last stage's result with its rest, the stages above
  the last as a stored generator of the wire into it (`pull`).  `[spec §75]` -/
  rest : Bool := false
  /-- The glue of a chain's rest: a stored generator of its last stage's items.  `[spec §75]` -/
  pull : Bool := false

/-- `F[r] A`, or `F A` at the empty row.  `[spec §75]` -/
def fAt (r A : String) : String := if r.isEmpty then s!"F ({A})" else s!"F[{r}] ({A})"

/-- Rows joined, the empty ones left out.  `[spec §75]` -/
def rowCat (rs : List String) : String := ", ".intercalate (rs.filter (!·.isEmpty))

/-- A right-nested tuple of the parts.  `[spec §75]` -/
def tup : List String → String
  | [] => "()"
  | [a] => a
  | a :: rest => s!"({a}, {tup rest})"

/-- A right-nested product of the types.  `[spec §75]` -/
def prod : List String → String
  | [] => "1"
  | [a] => a
  | a :: rest => s!"({a}) * ({prod rest})"

/-- A right-nested sum of the types.  `[spec §75]` -/
def sum : List String → String
  | [] => "0"
  | [a] => a
  | a :: rest => s!"({a}) + ({sum rest})"

/-- The `j`-th injection of `v` into a right-nested sum of `n` summands.  `[spec §75]` -/
def inj (j n : Nat) (v : String) : String :=
  if n ≤ 1 then v
  else if j == 0 then s!"inl {v}"
  else s!"inr ({inj (j - 1) (n - 1) v})"

/-- The stage's row arguments, in `lib/pipe.bc`'s order: `sg, cy, cn, cp, cf, lr, lc`.  `[spec §75]` -/
def Stage.rows (st : Stage) : String :=
  ", ".intercalate ([st.sg, st.cy, st.cn, st.cp, st.cf, st.lr, st.lc].map (s!"row ({·})"))

/-- The stage's arguments to a piece over its types: types, rows, sites.  `[spec §75]` -/
def Stage.args (st : Stage) : String :=
  s!"{st.A}, {st.K}, {st.KP}, {st.B}, {st.R}, {st.OA}, {st.rows}, site {st.y}, site {st.s}, site {st.f}"

/-- The stage's state type, `lib/pipe.bc`'s `PipeSt`.  `[spec §75]` -/
def Stage.stTy (st : Stage) : String := s!"PipeSt[{st.args}]"

/-- The stage's rest type, `PipeRest`.  `[spec §75]` -/
def Stage.restTy (st : Stage) : String := s!"PipeRest[{st.args}]"

/-- The stage's loop, as a state's `Ready`.  `[spec §75]` -/
def Stage.loopTy (st : Stage) : String := s!"PipeLoop[{st.R}, row ({st.lr}), row ({st.lc})]"

/-- The input of a turn of the stage, `(1 + KP) + (A + K)`.  `[spec §75]` -/
def Stage.inTy (st : Stage) : String := s!"(1 + {st.KP}) + ({st.A} + {st.K})"

/-- `v` taken apart into the names `xs`, a right-nested tuple, by one `let` per pair; `tmp` names
the inner tuples.  `[spec §75]` -/
def destr (xs : List String) (v tmp : String) : String :=
  let rec go : List String → String → Nat → String
    | [], v, _ => s!"let () = {v};"
    | [x], v, _ => s!"{x} <- return {v};"
    | x :: rest, v, k => s!"let ({x}, {tmp}{k}) = {v}; " ++ go rest s!"{tmp}{k}" (k + 1)
  go xs v 0

/-- A call of the piece `f` (a `!` value) at the argument `a`, as a computation.  `[spec §75]` -/
def call (f a : String) (k : String) : String :=
  s!"(io_fn{k} <- return (unbang {f}); io_ar{k} <- return ({a}); force io_fn{k} io_ar{k})"

/-- The glue of the chain, as core text: a computation that binds the connector's maker
`io_cw{sfx} : !(Q => U Lw)` and calls it in direct style on `q`, the tuple of what the stages'
states capture (of type `Q`), answering the last stage's result. The caller marks the call as a
frame's (`Sugar.markFrameCall`), so that the body around it runs it as the loop it is. With `tail`,
what follows the maker's binding instead: a `for` over the chain, whose generator the maker's call
is.  `[spec §75]` -/
def build (cn : Conn) (fvs : List (String × String)) (tail : Option String)
    (sub : Option (String × String × String)) : String × String × String := Id.run do
  let ss := cn.stages.toArray
  let n := ss.size
  let sfx := cn.sfx
  let G := cn.G
  -- The regions: one cancel row for the region's operation, what any stage performs when stopped.
  let cc := cn.cc
  let regOp := s!"{cn.c}.0 cancel[{cc}] 1 ~> 1"
  let regRow := rowCat [regOp, cc]
  let Rlast := match cn.out with
    | some (_, _, W) => s!"({W}) * ({ss[n - 1]!.R})"
    | none => ss[n - 1]!.R
  let hasW := cn.out.isSome
  let W := match cn.out with
    | some (_, _, W) => W
    | none => "1"
  -- The stage states: `suf j`, the right-nested tuple of the states of `j … n−1`, and `pre i`, the
  -- left-nested tuple of those of `0 … i−1`. The hole of stage `i`, `hole i`, is `pre i` beside
  -- `suf (i+1)`: the states of every stage but `i`, which is `close_others_i`'s argument.
  let stT (j : Nat) : String := ss[j]!.stTy
  let sufTy (j : Nat) : String := prod ((List.range (n - j)).map fun k => stT (j + k))
  let preTy (i : Nat) : String :=
    ((List.range i).map stT).foldl (fun acc t => if acc.isEmpty then t else s!"({acc}) * ({t})") ""
  let pairTy (a b : Option String) : String := match a, b with
    | none, none => "1"
    | some a, none => a
    | none, some b => b
    | some a, some b => s!"({a}) * ({b})"
  let pairV (a b : Option String) : String := match a, b with
    | none, none => "()"
    | some a, none => a
    | none, some b => b
    | some a, some b => s!"({a}, {b})"
  let optPre (i : Nat) : Option String := if i == 0 then none else some (preTy i)
  let optSuf (j : Nat) : Option String := if j ≥ n then none else some (sufTy j)
  let holeTy (i : Nat) : String := pairTy (optPre i) (optSuf (i + 1))
  let Sx := sufTy 0
  let SW := if hasW then s!"({Sx}) * ({W})" else Sx
  let GS := s!"({SW}) * ({sum (cn.stages.map (·.inTy))})"
  -- `connect`: the result beside the rest, the maker of whose glue is `sub`'s.
  let Rlast := match sub with
    | some (_, LwS, _) => s!"({Rlast}) * (U ({LwS}))"
    | none => Rlast
  let lastSt := ss[n - 1]!
  let Obs := if cn.pull then s!"(({lastSt.B}) * ({GS})) + (({lastSt.R}) + ({GS}))"
    else s!"({Rlast}) + ({GS})"
  let Lw := if cn.pull then s!"nu Z. {fAt G s!"(({lastSt.B}) * U Z) + (({lastSt.R}) + U Z)"} & {fAt G "1"}"
    else s!"nu Z. {fAt G s!"({Rlast}) + U Z"} & {fAt G "1"}"
  let sv (i : Nat) : String := s!"io_s{i}_{sfx}"
  let Kty := s!"U (1 -o {fAt regRow "1"})"
  let kStop (x : String) : String :=
    s!"thunkv fun (io_pz{x}_{sfx} : 1) -> (perform[{cn.c}.0] io_pz{x}_{sfx} : {fAt regRow "1"})"
  let wsArgs (st : Stage) : String :=
    s!"{st.A}, {st.K}, {st.KP}, {st.B}, {st.R}, {st.OA}, 1, {st.rows}, row ({cc}), row ({cc}), site {st.y}, site {st.s}, site {st.f}, site {cn.c}"
  let ws (j : Nat) : String := s!"pipe_with_stop[{wsArgs ss[j]!}]"
  let mut defs := s!"io_chr_{sfx} : !U (1 -o {fAt cc "1"}) <- return (!thunkv fun (io_cv_{sfx} : 1) -> return io_cv_{sfx});
io_chc_{sfx} : !U (1 * U ((1 -o {fAt cc "1"}) & {fAt (rowCat [cc, cc]) "1"}) -o {fAt cc "1"}) * 1 <- return
  ((!thunkv fun (io_cp_{sfx} : 1 * U ((1 -o {fAt cc "1"}) & {fAt (rowCat [cc, cc]) "1"})) ->
     let (io_cu_{sfx}, io_ck_{sfx}) = io_cp_{sfx}; let () = io_cu_{sfx}; (force io_ck_{sfx}).2), ());\n"
  -- The shared frames. Each installs one stage's `withStop` (`pipe_with_stop`, one `unwind` frame)
  -- and runs its continuation inside it, and does nothing else; none is a region. `io_dn{j}` is
  -- the frames of `j … n−1` around the region's operation, the most downstream innermost: stage
  -- `j`'s frame around `io_dn{j+1}`. `io_up{i}` is the frames of `0 … i−1` around a continuation:
  -- `io_up{i−1}` around stage `i−1`'s frame. Each state is captured where its frame is installed.
  for j' in List.range n do
    let j := n - 1 - j'
    let inner := if j + 1 == n then kStop s!"d{j}"
      else s!"thunkv fun (io_dw{j}_{sfx} : 1) -> let () = io_dw{j}_{sfx}; {call s!"io_dn{j + 1}_{sfx}" s!"io_dr{j}_{sfx}" s!"dn{j}_{sfx}"}"
    let bind := if j + 1 == n then s!"io_ds{j}_{sfx} <- return io_dx{j}_{sfx};"
      else s!"let (io_ds{j}_{sfx}, io_dr{j}_{sfx}) = io_dx{j}_{sfx};"
    defs := defs ++ s!"io_dn{j}_{sfx} : !U ({sufTy j} -o {fAt regRow "1"}) <- return (!thunkv fun (io_dx{j}_{sfx} : {sufTy j}) ->
    {bind} {call (ws j) s!"io_ds{j}_{sfx}, {inner}" s!"wd{j}_{sfx}"});\n"
  for i in (List.range n).drop 1 do
    let body := if i == 1 then call (ws 0) s!"io_ua{i}_{sfx}, io_uk{i}_{sfx}" s!"wu{i}_{sfx}"
      else s!"let (io_uq{i}_{sfx}, io_us{i}_{sfx}) = io_ua{i}_{sfx};
      {call s!"io_up{i - 1}_{sfx}" s!"io_uq{i}_{sfx}, thunkv fun (io_uw{i}_{sfx} : 1) -> let () = io_uw{i}_{sfx}; {call (ws (i - 1)) s!"io_us{i}_{sfx}, io_uk{i}_{sfx}" s!"wu{i}_{sfx}"}" s!"up{i}_{sfx}"}"
    defs := defs ++ s!"io_up{i}_{sfx} : !U (({preTy i}) * ({Kty}) -o {fAt regRow "1"}) <- return (!thunkv fun (io_ux{i}_{sfx} : ({preTy i}) * ({Kty})) ->
    let (io_ua{i}_{sfx}, io_uk{i}_{sfx}) = io_ux{i}_{sfx}; {body});\n"
  -- The frame lists, each one region at `c` around one chain of the shared frames.
  let listDef (name ty body : String) : String :=
    s!"{name} : !U ({ty} -o {fAt cc "1"}) <- return (!thunkv fun (io_pl_{sfx} : {ty}) ->
    handle_with[{cn.c}](io_chr_{sfx}, io_chc_{sfx}) ({body}));\n"
  -- An empty frame list stops nothing.
  let noneDef (name : String) : String :=
    s!"{name} : !U (1 -o {fAt cc "1"}) <- return (!thunkv fun (io_pl_{sfx} : 1) -> return io_pl_{sfx});\n"
  defs := defs ++ listDef s!"io_call_{sfx}" Sx (call s!"io_dn0_{sfx}" s!"io_pl_{sfx}" s!"la_{sfx}")
  for i in List.range n do
    let co := s!"io_co{i}_{sfx}"
    defs := defs ++ (if n == 1 then noneDef co
      else if i == 0 then listDef co (holeTy i) (call s!"io_dn1_{sfx}" s!"io_pl_{sfx}" s!"lo{i}_{sfx}")
      else if i + 1 == n then listDef co (holeTy i) (call s!"io_up{i}_{sfx}" s!"io_pl_{sfx}, {kStop s!"o{i}"}" s!"lo{i}_{sfx}")
      else listDef co (holeTy i) s!"let (io_pa_{sfx}, io_pb_{sfx}) = io_pl_{sfx};
      {call s!"io_up{i}_{sfx}" s!"io_pa_{sfx}, thunkv fun (io_pw_{sfx} : 1) -> let () = io_pw_{sfx}; {call s!"io_dn{i + 1}_{sfx}" s!"io_pb_{sfx}" s!"ld{i}_{sfx}"}" s!"lo{i}_{sfx}"}")
    if i > 0 then
      defs := defs ++ listDef s!"io_cu{i}_{sfx}" (preTy i) (call s!"io_up{i}_{sfx}" s!"io_pl_{sfx}, {kStop s!"u{i}"}" s!"lu{i}_{sfx}")
      defs := defs ++ listDef s!"io_cd{i}_{sfx}" (sufTy i) (call s!"io_dn{i}_{sfx}" s!"io_pl_{sfx}" s!"lc{i}_{sfx}")
  -- The per-stage getters and setters, used between turns only: `io_get{i}` takes the states
  -- apart into stage `i`'s and its hole, `io_set{i}` puts a state into the hole of stage `i`.
  -- Each goes through the one of the stage above, so each is constant-size.
  for i in (List.range n).drop 1 do
    let a := s!"io_ga{i}_{sfx}"
    let h := s!"io_gh{i}_{sfx}"
    let first := if i == 1 then s!"let ({a}, {h}) = io_gx{i}_{sfx};"
      else s!"io_gy{i}_{sfx} <- {call s!"io_get{i - 1}_{sfx}" s!"io_gx{i}_{sfx}" s!"gg{i}_{sfx}"}; let ({a}, {h}) = io_gy{i}_{sfx};"
    -- `h` is `pre (i−1)` beside `suf i`; `suf i` is stage `i`'s state beside `suf (i+1)`.
    let (hp, r) := if i == 1 then ("", h) else (s!"io_gp{i}_{sfx}", s!"io_gr{i}_{sfx}")
    let splitH := if i == 1 then "" else s!"let ({hp}, {r}) = {h};"
    let (b, r2, splitR) := if i + 1 == n then (r, none, "")
      else (s!"io_gb{i}_{sfx}", some s!"io_gs{i}_{sfx}", s!"let (io_gb{i}_{sfx}, io_gs{i}_{sfx}) = {r};")
    let newPre := if i == 1 then a else s!"({hp}, {a})"
    defs := defs ++ s!"io_get{i}_{sfx} : !U ({Sx} -o F (({stT i}) * ({holeTy i}))) <- return (!thunkv fun (io_gx{i}_{sfx} : {Sx}) ->
    {first} {splitH} {splitR} return ({b}, {pairV (some newPre) r2}));\n"
    -- `set i (h, x)`: `h` is `pre i` (`pre (i−1)` beside stage `i−1`'s state `s`) beside `suf (i+1)`;
    -- it is `set (i−1)` of `(pre (i−1), (x, suf (i+1)))` and `s`.
    let sp := s!"io_sp{i}_{sfx}"
    let (pv, rv, splitS) := if i + 1 == n then (sp, none, "")
      else (s!"io_sq{i}_{sfx}", some s!"io_sr{i}_{sfx}", s!"let (io_sq{i}_{sfx}, io_sr{i}_{sfx}) = {sp};")
    let sufI := pairV (some s!"io_sx{i}_{sfx}") rv
    let setBody := if i == 1 then s!"return ({pv}, {sufI})"
      else s!"let (io_sa{i}_{sfx}, io_sb{i}_{sfx}) = {pv}; {call s!"io_set{i - 1}_{sfx}" s!"(io_sa{i}_{sfx}, {sufI}), io_sb{i}_{sfx}" s!"ss{i}_{sfx}"}"
    defs := defs ++ s!"io_set{i}_{sfx} : !U ((({holeTy i}) * ({stT i})) -o F ({Sx})) <- return (!thunkv fun (io_sv{i}_{sfx} : ({holeTy i}) * ({stT i})) ->
    let ({sp}, io_sx{i}_{sfx}) = io_sv{i}_{sfx}; {splitS} {setBody});\n"
  -- The states with stage `i`'s put into its hole `h`, a computation.
  let setE (i : Nat) (h x k : String) : String :=
    if i == 0 then s!"return {pairV (some x) (if n == 1 then none else some h)}"
    else call s!"io_set{i}_{sfx}" s!"{h}, {x}" k
  -- The stage upstream stopped by `stop()` ends; one above it is never run again, and is left a
  -- loop that runs nothing (`pipe_idle`). `io_id{i}` is `pre i` of such loops.
  let idle (j : Nat) : String :=
    let sj := ss[j]!
    let body := s!"nu X. {fAt sj.lr s!"({sj.R}) + U X"} & {fAt sj.lc "1"}"
    let mk := s!"io_ig{j}_{sfx} <- return (unbang (unfold[{body}, 1] pipe_idle[{sj.R}, row ({sj.lr}), row ({sj.lc})])); io_iz{j}_{sfx} <- return ()"
    s!"(inl (thunkv nu_in < {mk}; (nu_out (force io_ig{j}_{sfx} io_iz{j}_{sfx})).1, {mk}; (nu_out (force io_ig{j}_{sfx} io_iz{j}_{sfx})).2 >) : {sj.stTy})"
  for i in (List.range (n - 1)).drop 1 do
    let body := if i == 1 then s!"return {idle 0}"
      else s!"io_iy{i}_{sfx} <- {call s!"io_id{i - 1}_{sfx}" "()" s!"ii{i}_{sfx}"}; return (io_iy{i}_{sfx}, {idle (i - 1)})"
    defs := defs ++ s!"io_id{i}_{sfx} : !U (1 -o F ({preTy i})) <- return (!thunkv fun (io_ia{i}_{sfx} : 1) ->
    let () = io_ia{i}_{sfx}; {body});\n"
  let withW (sx w : String) : String := if hasW then s!"({sx}, {w})" else sx
  let next (sx turn : String) : String :=
    if cn.pull then s!"return (inr (inr ({withW sx s!"io_ow_{sfx}"}, {turn})) : {Obs})"
    else s!"return (inr ({withW sx s!"io_ow_{sfx}"}, {turn}) : {Obs})"
  -- The next turn after the states `comp` computes.
  let nextC (comp turn k : String) : String := s!"io_nx{k}_{sfx} <- {comp}; {next s!"io_nx{k}_{sfx}" turn}"
  let turnTo (j : Nat) (v : String) : String :=
    s!"({inj j n v} : {sum (cn.stages.map (·.inTy))})"
  -- A left-nested tuple of the states of `0 … k−1` taken apart into their names.
  let rec lsplit (k : Nat) (v : String) : String := match k with
    | 0 => ""
    | 1 => s!"{sv 0} <- return {v};"
    | k + 1 => s!"let (io_lq{k}_{sfx}, {sv k}) = {v}; " ++ lsplit k s!"io_lq{k}_{sfx}"
  let mut arms : List String := []
  for i in List.range n do
    let st := ss[i]!
    let last := i + 1 == n
    let ev := s!"io_e{i}_{sfx}"
    let h := s!"io_h{i}_{sfx}"
    let hp := s!"io_hp{i}_{sfx}"
    let hs := s!"io_hs{i}_{sfx}"
    let preV : Option String := if i == 0 then none else some hp
    let sufV : Option String := if last then none else some hs
    -- The hole taken apart, in an arm that needs its parts.
    let splitHole : String := match preV, sufV with
      | some p, some s => s!"let ({p}, {s}) = {h};"
      | some p, none => s!"{p} <- return {h};"
      | none, some s => s!"{s} <- return {h};"
      | none, none => s!"let () = {h};"
    let getS := if i == 0 then
        (if n == 1 then s!"{sv 0} <- return io_sx_{sfx};" else s!"let ({sv 0}, {h}) = io_sx_{sfx};")
      else s!"io_gt{i}_{sfx} <- {call s!"io_get{i}_{sfx}" s!"io_sx_{sfx}" s!"gt{i}_{sfx}"}; let ({sv i}, {h}) = io_gt{i}_{sfx};"
    let stepCall := call s!"pipe_step[{st.args}]" s!"{sv i}, io_in{i}_{sfx}" s!"st{i}_{sfx}"
    let coCall := call s!"io_co{i}_{sfx}" (if n == 1 then "()" else h) s!"co{i}_{sfx}"
    -- `close_all` on the states with stage `i`'s put: the setter only builds the tuple (its body
    -- takes pairs apart and makes them, and performs nothing), so in a finaliser it runs nothing
    -- but `close_all`.
    let callAll (x k : String) : String := s!"(io_ca{k}_{sfx} <- {setE i h x s!"cs{k}_{sfx}"}; {call s!"io_call_{sfx}" s!"io_ca{k}_{sfx}" s!"ca{k}_{sfx}"})"
    -- Yield(b, κ) and Return(k): to the stage downstream (`pipe_handoff`), or the end. Stage `i`
    -- and the one downstream change: the states are `set (i+1)` of `(pre i, t)` and `suf (i+2)`.
    let handoff (v : String) : String :=
      let dn := ss[i + 1]!
      let (s1, rest, splitN) := if i + 2 == n then (hs, none, "")
        else (s!"io_hn{i}_{sfx}", some s!"io_hr{i}_{sfx}", s!"let (io_hn{i}_{sfx}, io_hr{i}_{sfx}) = {hs};")
      let hc := call s!"pipe_handoff[{st.loopTy}, {st.restTy}, {st.restTy}, {st.B}, {st.R}, {dn.KP}, {dn.stTy}]"
        s!"({v} : {st.B} * {st.restTy} + {st.R}), {s1}" s!"h{i}_{sfx}"
      let pre1 := pairV preV (some s!"io_t{i}_{sfx}")
      s!"{splitHole} {splitN}
                io_hd{i}_{sfx} <- {hc};
                let (io_t{i}_{sfx}, io_ri{i}_{sfx}) = io_hd{i}_{sfx}; let (io_ip{i}_{sfx}, io_tn{i}_{sfx}) = io_ri{i}_{sfx};
                {nextC (call s!"io_set{i + 1}_{sfx}" s!"{pairV (some pre1) rest}, io_tn{i}_{sfx}" s!"hs{i}_{sfx}") (turnTo (i + 1) s!"io_ip{i}_{sfx}") s!"h{i}"}"
    let yieldArm := if last && st.gen.isSome then match st.gen with
        | some (ng, co) =>
          -- A generator's chain: the item goes to the `Yield` around the chain, under
          -- `close_all`, as a forwarded operation does; the stage resumes the next turn.
          let sy := s!"io_sy{i}_{sfx}"
          let fw := call s!"pipe_forward[{st.B}, row ({co}), row ({G}), site {ng}]" s!"io_b{i}_{sfx}" s!"gy{i}_{sfx}"
          s!"let (io_b{i}_{sfx}, io_ky{i}_{sfx}) = io_yk{i}_{sfx};
                {sy} : {st.stTy} <- return (inr (inr (inl io_ky{i}_{sfx})));
                io_gu{i}_{sfx} <- {fw} unwind {callAll sy s!"g{i}"};
                let () = io_gu{i}_{sfx};
                {nextC (setE i h sy s!"ng{i}_{sfx}") (turnTo i "inl (inl ())") s!"g{i}"}"
        | none => ""
      else if last then match cn.out with
        | some (nf, _, W) =>
          -- A `for`'s generator: the item goes out with the threaded value, which comes back in
          -- the site's answer; `close_all` stops every stage if the `for` drops the continuation.
          let sy := s!"io_sy{i}_{sfx}"
          s!"let (io_b{i}_{sfx}, io_ky{i}_{sfx}) = io_yk{i}_{sfx};
                {sy} : {st.stTy} <- return (inr (inr (inl io_ky{i}_{sfx})));
                io_wo{i}_{sfx} : ({st.B}) * ({W}) <- return (io_b{i}_{sfx}, io_ow_{sfx});
                io_w2{i}_{sfx} <- (perform[{nf}.0] io_wo{i}_{sfx}) unwind {callAll sy s!"y{i}"};
                io_ny{i}_{sfx} <- {setE i h sy s!"ny{i}_{sfx}"};
                return (inr (({s!"io_ny{i}_{sfx}"}, io_w2{i}_{sfx}), {turnTo i "inl (inl ())"}) : {Obs})"
        | none => if cn.pull then
          -- A chain's rest: the last stage's item is the stored generator's.
          s!"let (io_b{i}_{sfx}, io_ky{i}_{sfx}) = io_yk{i}_{sfx};
                io_ny{i}_{sfx} <- {setE i h s!"(inr (inr (inl io_ky{i}_{sfx})) : {st.stTy})" s!"ny{i}_{sfx}"};
                return (inl (io_b{i}_{sfx}, ({withW s!"io_ny{i}_{sfx}" s!"io_ow_{sfx}"}, {turnTo i "inl (inl ())"})) : {Obs})"
          else
          s!"let (io_b{i}_{sfx}, io_ky{i}_{sfx}) = io_yk{i}_{sfx}; let _ = io_b{i}_{sfx};
                {nextC (setE i h s!"(inr (inr (inl io_ky{i}_{sfx})) : {st.stTy})" s!"ny{i}_{sfx}") (turnTo i "inl (inl ())") s!"y{i}"}"
      else handoff s!"inl io_yk{i}_{sfx}"
    let returnArm := if last && cn.pull then
        s!"io_v{i}_{sfx} <- {coCall}; let () = io_v{i}_{sfx};
                return (inr (inl io_r{i}_{sfx}) : {Obs})"
      else if last && sub.isSome then
        -- `connect`: the stages above the last are its rest, which goes on where they are. Its
        -- glue takes their states right-nested; the hole has them left-nested.
        let m := n - 1
        let ups := (List.range m).map sv
        let subTurn := s!"({inj (n - 2) (n - 1) "inl (inl ())"} : {sum ((cn.stages.take (n - 1)).map (·.inTy))})"
        s!"{lsplit m h}
                io_rs{i}_{sfx} <- return ((unbang io_rw_{sfx}r) ({tup ups}, {subTurn}));
                return (inl (io_r{i}_{sfx}, io_rs{i}_{sfx}) : {Obs})"
      else if last then
        let fin := call s!"pipe_finish[{st.R}, row ({G})]"
          s!"io_r{i}_{sfx}, (thunkv fun (io_fw_{sfx} : 1) -> {call s!"io_co{i}_{sfx}" (if n == 1 then "()" else h) s!"fco{i}_{sfx}"} : U (1 -o {fAt G "1"}))" s!"fin{i}_{sfx}"
        let res := if hasW then s!"(io_ow_{sfx}, io_v{i}_{sfx})" else s!"io_v{i}_{sfx}"
        s!"io_v{i}_{sfx} <- {fin}; return (inl {res} : {Obs})"
      else handoff s!"inr io_r{i}_{sfx}"
    let skipArm := nextC (setE i h s!"(inl io_bl{i}_{sfx} : {st.stTy})" s!"nb{i}_{sfx}") (turnTo i "inl (inl ())") s!"b{i}"
    -- Next(κ): stored; the stage upstream runs, or, when it has ended, the end again. Stage `i`
    -- and the one upstream change: the states are `set (i−1)` of `(pre (i−1), (t, suf (i+1)))`.
    let nextArm := if i == 0 then
        nextC (setE i h s!"(inr (inl io_kn{i}_{sfx}) : {st.stTy})" s!"nn{i}_{sfx}") (turnTo i "inr (inr ())") s!"n{i}"
      else
        let upSt := ss[i - 1]!
        let t := s!"(inr (inl io_kn{i}_{sfx}) : {st.stTy})"
        let su := sv (i - 1)
        let (pq, splitP) := if i == 1 then (none, s!"{su} <- return {hp};")
          else (some s!"io_hq{i}_{sfx}", s!"let (io_hq{i}_{sfx}, {su}) = {hp};")
        let hUp := pairV pq (some (pairV (some t) sufV))
        let put (x turn k : String) : String :=
          nextC (setE (i - 1) hUp s!"({x} : {upSt.stTy})" s!"nu{k}{i}_{sfx}") turn s!"u{k}{i}"
        let keep (ctor k : String) : String := put ctor (turnTo (i - 1) "inl (inl ())") k
        s!"{splitHole} {splitP}
                  case {su} \{
                    inl io_ua{i}_{sfx} -> {keep s!"inl io_ua{i}_{sfx}" "a"}
                  | inr io_ub{i}_{sfx} -> case io_ub{i}_{sfx} \{
                      inl io_uc{i}_{sfx} -> {keep s!"inr (inl io_uc{i}_{sfx})" "c"}
                    | inr io_ud{i}_{sfx} -> case io_ud{i}_{sfx} \{
                        inl io_ue{i}_{sfx} -> {keep s!"inr (inr (inl io_ue{i}_{sfx}))" "e"}
                      | inr io_uk{i}_{sfx} -> {put s!"inr (inr (inr io_uk{i}_{sfx}))" (turnTo i s!"inr (inr io_uk{i}_{sfx})") "k"}
                      }
                    }
                  }"
    -- Stop(κ): the stages upstream stopped in one region (`close_up_i`); the stage resumes with
    -- the region's outcome, `inl ()`, or `inr` the payload of its first error, which the stage
    -- raises at its `stop()` (Assembly(n) rev 2.6), wherever that `stop()` is written (in a helper
    -- too: the re-raise is elaborated at the call, through the stage's `Stream` site). Every
    -- stage with a `Stream` site has this arm; `KP` holds every abortive operation of the stages
    -- upstream, and each site of one is reified by a handler outside the region, answering the
    -- payload's injection into `KP`. Only a
    -- cancel from outside, landing in the region, runs the finaliser `close_down_i`, which stops
    -- the stage and those downstream of it: the stage's state is live across the region.
    -- That finaliser is a typing obligation (`[then]` needs the live state consumed on a cancel).
    -- The surface does not reach it: a cancel lands there only at an upstream cleanup's
    -- forwarded operation, which is refused (`connectorV`, `reject/pipe-fin-forwarded.bc`).
    -- Reached from core text, the order is Thm X's absorbed-cleanup clause (SPEC §19 *Cancels*,
    -- `[cfin-cancel]`): the region completes, its first error kept, and `close_down_i` then
    -- stops the stage and those downstream, downstream-first.
    let stopArm := if i == 0 then
        nextC (setE i h s!"(inr (inr (inl io_ks{i}_{sfx})) : {st.stTy})" s!"ns{i}_{sfx}") (turnTo i "inl (inl ())") s!"s{i}"
      else
        let t := s!"io_ts{i}_{sfx}"
        let sufI := pairV (some t) sufV
        let X := s!"1 + {st.KP}"
        let upCall := call s!"io_cu{i}_{sfx}" hp s!"cu{i}_{sfx}"
        let dnCall := call s!"io_cd{i}_{sfx}" sufI s!"cd{i}_{sfx}"
        let reified := st.reify.foldl (fun body (site, ops, rowAfter) =>
          let ans := s!"!U ({X} -o {fAt rowAfter s!"({X})"})"
          let cl := ops.map fun
            | .pay A k => s!"(!thunkv fun (io_re_{sfx} : {A}) -> return (inr ({inj k st.np s!"io_re_{sfx}"}) : {X}))"
          let clTy := prod ((ops.map fun
            | .pay A _ => s!"!U ({A} -o {fAt rowAfter s!"({X})"})") ++ ["1"])
          s!"handle_with[{site}](((!thunkv fun (io_ro_{sfx} : {X}) -> return io_ro_{sfx}) : {ans}), ({tup (cl ++ ["()"])} : {clTy})) ({body})")
          s!"(io_sq{i}_{sfx} <- {upCall}; return (inl io_sq{i}_{sfx} : {X}))"
        let (idleV, idleMk) := if i == 1 then (none, "")
          else (some s!"io_il{i}_{sfx}", s!"io_il{i}_{sfx} <- {call s!"io_id{i - 1}_{sfx}" "()" s!"il{i}_{sfx}"};")
        let ended := s!"(inr (inr (inr ())) : {ss[i - 1]!.stTy})"
        s!"{splitHole}
                    {t} : {st.stTy} <- return (inr (inr (inl io_ks{i}_{sfx})));
                    io_su{i}_{sfx} : {X} <- {reified} unwind {dnCall};
                    {idleMk}
                    {nextC (setE (i - 1) (pairV idleV (some sufI)) ended s!"ns{i}_{sfx}") (turnTo i s!"inl io_su{i}_{sfx}") s!"s{i}"}"
    -- Fwd(a, κ): stored (`AtFwd`); the connector performs the outer operation under `close_all`,
    -- so that a cancel there stops every stage downstream-first; the stage resumes the next turn.
    let fwdArm := match st.fwd with
      | some (nOut, co) =>
        let sf := s!"io_sf{i}_{sfx}"
        let fw := call s!"pipe_forward[{st.OA}, row ({co}), row ({G}), site {nOut}]" s!"io_fa{i}_{sfx}" s!"fw{i}_{sfx}"
        s!"let (io_fa{i}_{sfx}, io_fk{i}_{sfx}) = io_fy{i}_{sfx};
              {sf} : {st.stTy} <- return (inr (inr (inl io_fk{i}_{sfx})));
              io_fr{i}_{sfx} <- {fw} unwind {callAll sf s!"f{i}"};
              let () = io_fr{i}_{sfx};
              {nextC (setE i h sf s!"nf{i}_{sfx}") (turnTo i "inl (inl ())") s!"f{i}"}"
      | none => s!"let (io_fa{i}_{sfx}, io_fk{i}_{sfx}) = io_fy{i}_{sfx}; let _ = io_fa{i}_{sfx};
              {nextC (setE i h s!"(inr (inr (inl io_fk{i}_{sfx})) : {st.stTy})" s!"nf{i}_{sfx}") (turnTo i "inl (inl ())") s!"f{i}"}"
    let arm := s!"{getS}
          {ev} <- {stepCall} unwind {coCall};
          case {ev} \{
            inl io_ea{i}_{sfx} -> case io_ea{i}_{sfx} \{
                inl io_yk{i}_{sfx} -> {yieldArm}
              | inr io_rl{i}_{sfx} -> case io_rl{i}_{sfx} \{
                  inl io_r{i}_{sfx} -> {returnArm}
                | inr io_bl{i}_{sfx} -> {skipArm}
                }
              }
          | inr io_eb{i}_{sfx} -> case io_eb{i}_{sfx} \{
                inl io_ec{i}_{sfx} -> case io_ec{i}_{sfx} \{
                    inl io_kn{i}_{sfx} -> {nextArm}
                  | inr io_ks{i}_{sfx} -> {stopArm}
                  }
              | inr io_fy{i}_{sfx} -> {fwdArm}
              }
          }"
    arms := arms ++ [arm]
  -- The dispatch on the running stage: a `case` per summand of the turn.
  let rec dispatch (v : String) (i : Nat) : List String → String
    | [] => "return ()"
    | [a] => s!"io_in{i}_{sfx} <- return {v};\n          {a}"
    | a :: rest => s!"case {v} \{
        inl io_in{i}_{sfx} -> {a}
      | inr io_tr{i}_{sfx} -> {dispatch s!"io_tr{i}_{sfx}" (i + 1) rest}
      }"
  let bindSW := if hasW then s!"let (io_sx_{sfx}, io_ow_{sfx}) = io_ss_{sfx};" else s!"io_sx_{sfx} <- return io_ss_{sfx};"
  let turnFn := s!"io_turn_{sfx} : !U ({GS} -o {fAt G Obs} & {fAt G "1"}) <- return (!thunkv fun (io_g_{sfx} : {GS}) ->
    < let (io_ss_{sfx}, io_tn_{sfx}) = io_g_{sfx}; {bindSW}
      {dispatch s!"io_tn_{sfx}" 0 arms},
      let (io_ss_{sfx}, io_tn_{sfx}) = io_g_{sfx}; let _ = io_tn_{sfx}; {bindSW} {if hasW then s!"let _ = io_ow_{sfx};" else ""}
      {call s!"io_call_{sfx}" s!"io_sx_{sfx}" s!"cl_{sfx}"} >);\n"
  let ready := withW (tup (cn.stages.map (·.ready))) (match cn.out with
    | some (_, w, _) => w
    | none => "()")
  let Q := prod (fvs.map (·.2))
  let q := tup (fvs.map (·.1))
  if cn.pull then
    -- The maker of a chain's rest: it takes the states and the turn as they are.
    let mk := s!"io_rw_{sfx} : !({GS} => U ({Lw})) <- return (!thunkv fun (io_st_{sfx} : {GS}) ->
  {defs}{turnFn}io_f_{sfx} <- return (unbang (unfold[{Lw}, {GS}] io_turn_{sfx}));
  return (thunkv nu_in < (nu_out (force io_f_{sfx} io_st_{sfx})).1, (nu_out (force io_f_{sfx} io_st_{sfx})).2 >));\n"
    return (mk, Lw, GS)
  let subDef := match sub with
    | some (d, _, _) => d
    | none => ""
  let body := s!"io_cw_{sfx} : !({Q} => U ({Lw})) <- return (!thunkv fun (io_q_{sfx} : {Q}) ->
  {destr (fvs.map (·.1)) s!"io_q_{sfx}" s!"io_qt_{sfx}_"}
  {subDef}{defs}{turnFn}io_st_{sfx} : {GS} <- return ({ready}, {turnTo (n - 1) "inl (inl ())"});
  io_f_{sfx} <- return (unbang (unfold[{Lw}, {GS}] io_turn_{sfx}));
  return (thunkv nu_in < (nu_out (force io_f_{sfx} io_st_{sfx})).1, (nu_out (force io_f_{sfx} io_st_{sfx})).2 >));
{tail.getD s!"io_pipe_j_{sfx} : {Rlast} <- return ((unbang io_cw_{sfx}) {q});
return io_pipe_j_{sfx}"}"
  pure (body, Lw, GS)

/-- The glue of the chain (`build`); for `connect`, with the glue of its rest, the stages above the
last, a stored generator of the wire into it.  `[spec §75]` -/
def glue (cn : Conn) (fvs : List (String × String)) (tail : Option String := none) : String :=
  let sub := if cn.rest && cn.stages.length ≥ 2 then
      some (build { cn with stages := cn.stages.dropLast, sfx := cn.sfx ++ "r", rest := false,
                            pull := true, out := none } [] none none)
    else none
  (build cn fvs tail sub).1

/-- The argument the connector's maker takes: the tuple of what the stages' states capture.
`[spec §75]` -/
def makerArg (fvs : List (String × String)) : String := tup (fvs.map (·.1))

end Frontend.Elab.Connector
