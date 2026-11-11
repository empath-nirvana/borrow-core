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
  `close_all` around `pipe_forward`, and `close_up_i`, the region of `stop()` by `i`, under the
  frame list of `i` and the stages downstream of it;
* one `unfold` whose turn calls the running stage's `pipe_step` and dispatches on its event,
  as Assembly(n) §1's glue does, and whose close is `close_all`.

The glue has no pipe semantics of its own: every stage's state is taken, stored and stopped by a
piece, and the kernel checks each piece's instance. The types, rows and sites are what the typed
elaboration read off each stage as elaborated (`Stage`); nothing here infers them.
-/

namespace Frontend.Elab.Connector

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

/-- `F[r] A`, or `F A` at the empty row. -/
def fAt (r A : String) : String := if r.isEmpty then s!"F ({A})" else s!"F[{r}] ({A})"

/-- Rows joined, the empty ones left out. -/
def rowCat (rs : List String) : String := ", ".intercalate (rs.filter (!·.isEmpty))

/-- A right-nested tuple of the parts. -/
def tup : List String → String
  | [] => "()"
  | [a] => a
  | a :: rest => s!"({a}, {tup rest})"

/-- A right-nested product of the types. -/
def prod : List String → String
  | [] => "1"
  | [a] => a
  | a :: rest => s!"({a}) * ({prod rest})"

/-- A right-nested sum of the types. -/
def sum : List String → String
  | [] => "0"
  | [a] => a
  | a :: rest => s!"({a}) + ({sum rest})"

/-- The `j`-th injection of `v` into a right-nested sum of `n` summands. -/
def inj (j n : Nat) (v : String) : String :=
  if n ≤ 1 then v
  else if j == 0 then s!"inl {v}"
  else s!"inr ({inj (j - 1) (n - 1) v})"

/-- The stage's row arguments, in `lib/pipe.bc`'s order: `sg, cy, cn, cp, cf, lr, lc`. -/
def Stage.rows (st : Stage) : String :=
  ", ".intercalate ([st.sg, st.cy, st.cn, st.cp, st.cf, st.lr, st.lc].map (s!"row ({·})"))

/-- The stage's arguments to a piece over its types: types, rows, sites. -/
def Stage.args (st : Stage) : String :=
  s!"{st.A}, {st.K}, {st.B}, {st.R}, {st.OA}, {st.rows}, site {st.y}, site {st.s}, site {st.f}"

/-- The stage's state type, `lib/pipe.bc`'s `PipeSt`. -/
def Stage.stTy (st : Stage) : String := s!"PipeSt[{st.args}]"

/-- The stage's event type, `PipeEv`. -/
def Stage.evTy (st : Stage) : String := s!"PipeEv[{st.args}]"

/-- The stage's rest type, `PipeRest`. -/
def Stage.restTy (st : Stage) : String := s!"PipeRest[{st.args}]"

/-- The stage's loop, as a state's `Ready`. -/
def Stage.loopTy (st : Stage) : String := s!"PipeLoop[{st.R}, row ({st.lr}), row ({st.lc})]"

/-- The input of a turn of the stage, `1 + (A + K)`. -/
def Stage.inTy (st : Stage) : String := s!"1 + ({st.A} + {st.K})"

/-- `v` taken apart into the names `xs`, a right-nested tuple, by one `let` per pair; `tmp` names
the inner tuples. -/
def destr (xs : List String) (v tmp : String) : String :=
  let rec go : List String → String → Nat → String
    | [], v, _ => s!"let () = {v};"
    | [x], v, _ => s!"{x} <- return {v};"
    | x :: rest, v, k => s!"let ({x}, {tmp}{k}) = {v}; " ++ go rest s!"{tmp}{k}" (k + 1)
  go xs v 0

/-- A call of the piece `f` (a `!` value) at the argument `a`, as a computation. -/
def call (f a : String) (k : String) : String :=
  s!"(io_fn{k} <- return (unbang {f}); io_ar{k} <- return ({a}); force io_fn{k} io_ar{k})"

/-- The glue of the chain, as core text: a computation that binds the connector's maker
`io_cw{sfx} : !(Q => U Lw)` and calls it in direct style on `q`, the tuple of what the stages'
states capture (of type `Q`), answering the last stage's result. The caller marks the call as a
frame's (`Sugar.markFrameCall`), so that the body around it runs it as the loop it is.
`[spec §75]` -/
def glue (cn : Conn) (fvs : List (String × String)) : String := Id.run do
  let ss := cn.stages.toArray
  let n := ss.size
  let sfx := cn.sfx
  let G := cn.G
  -- The regions: one cancel row for the region's operation, what any stage performs when stopped.
  let cc := cn.cc
  let regOp := s!"{cn.c}.0 cancel[{cc}] 1 ~> 1"
  let regRow := rowCat [regOp, cc]
  let Rlast := ss[n - 1]!.R
  let Sts := cn.stages.map (·.stTy)
  let GS := s!"({prod Sts}) * ({sum (cn.stages.map (·.inTy))})"
  let Lw := s!"nu Z. {fAt G s!"({Rlast}) + U Z"} & {fAt G "1"}"
  let sv (i : Nat) : String := s!"io_s{i}_{sfx}"
  -- A frame list over the stages `js` (outermost first), one region.
  let wsArgs (st : Stage) : String :=
    s!"{st.A}, {st.K}, {st.B}, {st.R}, {st.OA}, 1, {st.rows}, row ({cc}), row ({cc}), site {st.y}, site {st.s}, site {st.f}, site {cn.c}"
  let rec frames (js : List Nat) (k : Nat) : String := match js with
    | [] => s!"(perform[{cn.c}.0] io_w{k}_{sfx} : {fAt regRow "1"})"
    | j :: rest =>
      call s!"pipe_with_stop[{wsArgs ss[j]!}]"
        s!"{sv j}, thunkv fun (io_w{k + 1}_{sfx} : 1) -> {frames rest (k + 1)}" s!"w{j}_{k}_{sfx}"
  let listDef (name : String) (js : List Nat) : String :=
    let ty := prod (js.map fun j => ss[j]!.stTy)
    s!"{name} : !U ({ty} -o {fAt cc "1"}) <- return (!thunkv fun (io_pl_{sfx} : {ty}) ->
    {destr (js.map sv) s!"io_pl_{sfx}" s!"io_plt_{sfx}_"}
    handle_with[{cn.c}](io_chr_{sfx}, io_chc_{sfx}) ({frames js 0}));\n"
  let others (i : Nat) : List Nat := (List.range n).filter (· != i)
  let down (i : Nat) : List Nat := (List.range n).filter (· ≥ i)
  let up (i : Nat) : List Nat := (List.range i)
  let mut defs := s!"io_chr_{sfx} : !U (1 -o {fAt cc "1"}) <- return (!thunkv fun (io_cv_{sfx} : 1) -> return io_cv_{sfx});
io_chc_{sfx} : !U (1 * U ((1 -o {fAt cc "1"}) & {fAt (rowCat [cc, cc]) "1"}) -o {fAt cc "1"}) * 1 <- return
  ((!thunkv fun (io_cp_{sfx} : 1 * U ((1 -o {fAt cc "1"}) & {fAt (rowCat [cc, cc]) "1"})) ->
     let (io_cu_{sfx}, io_ck_{sfx}) = io_cp_{sfx}; let () = io_cu_{sfx}; (force io_ck_{sfx}).2), ());\n"
  defs := defs ++ listDef s!"io_call_{sfx}" (List.range n)
  for i in List.range n do
    defs := defs ++ listDef s!"io_co{i}_{sfx}" (others i)
    if i > 0 then
      defs := defs ++ listDef s!"io_cu{i}_{sfx}" (up i)
      defs := defs ++ listDef s!"io_cd{i}_{sfx}" (down i)
  -- The states as a tuple with stage `i`'s replaced by `t`.
  let states (i : Nat) (t : String) : String :=
    tup ((List.range n).map fun j => if j == i then t else sv j)
  let next (stTup turn : String) : String := s!"return (inr ({stTup}, {turn}) : ({Rlast}) + ({GS}))"
  let turnTo (j : Nat) (v : String) : String :=
    s!"({inj j n v} : {sum (cn.stages.map (·.inTy))})"
  let othersTup (i : Nat) : String := tup ((others i).map sv)
  let mut arms : List String := []
  for i in List.range n do
    let st := ss[i]!
    let last := i + 1 == n
    let ev := s!"io_e{i}_{sfx}"
    let stepCall := call s!"pipe_step[{st.args}]" s!"{sv i}, io_in{i}_{sfx}" s!"st{i}_{sfx}"
    let coCall := call s!"io_co{i}_{sfx}" (othersTup i) s!"co{i}_{sfx}"
    -- Yield(b, κ) and Return(k): to the stage downstream (`pipe_handoff`), or the end.
    let handoff (v : String) : String :=
      let dn := ss[i + 1]!
      let h := call s!"pipe_handoff[{st.loopTy}, {st.restTy}, {st.restTy}, {st.B}, {st.R}, {dn.stTy}]"
        s!"({v} : {st.B} * {st.restTy} + {st.R}), {sv (i + 1)}" s!"h{i}_{sfx}"
      s!"io_h{i}_{sfx} <- {h};
                let (io_t{i}_{sfx}, io_ri{i}_{sfx}) = io_h{i}_{sfx}; let (io_ip{i}_{sfx}, io_tn{i}_{sfx}) = io_ri{i}_{sfx};
                {next (tup ((List.range n).map fun j => if j == i then s!"io_t{i}_{sfx}" else if j == i + 1 then s!"io_tn{i}_{sfx}" else sv j)) (turnTo (i + 1) s!"io_ip{i}_{sfx}")}"
    let yieldArm := if last then
        s!"let (io_b{i}_{sfx}, io_ky{i}_{sfx}) = io_yk{i}_{sfx}; let _ = io_b{i}_{sfx};
                {next (states i s!"(inr (inr (inl io_ky{i}_{sfx})) : {st.stTy})") (turnTo i "inl ()")}"
      else handoff s!"inl io_yk{i}_{sfx}"
    let returnArm := if last then
        let fin := call s!"pipe_finish[{st.R}, row ({G})]"
          s!"io_r{i}_{sfx}, (thunkv fun (io_fw_{sfx} : 1) -> {call s!"io_co{i}_{sfx}" (othersTup i) s!"fco{i}_{sfx}"} : U (1 -o {fAt G "1"}))" s!"fin{i}_{sfx}"
        s!"io_v{i}_{sfx} <- {fin}; return (inl io_v{i}_{sfx} : ({Rlast}) + ({GS}))"
      else handoff s!"inr io_r{i}_{sfx}"
    let skipArm := next (states i s!"(inl io_bl{i}_{sfx} : {st.stTy})") (turnTo i "inl ()")
    -- Next(κ): stored; the stage upstream runs, or, when it has ended, the end again.
    let nextArm := if i == 0 then
        next (states i s!"(inr (inl io_kn{i}_{sfx}) : {st.stTy})") (turnTo i "inr (inr ())")
      else
        let upSt := ss[i - 1]!
        let t := s!"(inr (inl io_kn{i}_{sfx}) : {st.stTy})"
        let keep (ctor : String) : String :=
          next (tup ((List.range n).map fun j => if j == i then t else if j == i - 1 then s!"({ctor} : {upSt.stTy})" else sv j))
            (turnTo (i - 1) "inl ()")
        s!"case {sv (i - 1)} \{
                    inl io_ua{i}_{sfx} -> {keep s!"inl io_ua{i}_{sfx}"}
                  | inr io_ub{i}_{sfx} -> case io_ub{i}_{sfx} \{
                      inl io_uc{i}_{sfx} -> {keep s!"inr (inl io_uc{i}_{sfx})"}
                    | inr io_ud{i}_{sfx} -> case io_ud{i}_{sfx} \{
                        inl io_ue{i}_{sfx} -> {keep s!"inr (inr (inl io_ue{i}_{sfx}))"}
                      | inr io_uk{i}_{sfx} -> {next (tup ((List.range n).map fun j => if j == i then t else if j == i - 1 then s!"(inr (inr (inr io_uk{i}_{sfx})) : {upSt.stTy})" else sv j)) (turnTo i s!"inr (inr io_uk{i}_{sfx})")}
                      }
                    }
                  }"
    -- Stop(κ): the stages upstream stopped in one region (`close_up_i`), under the frame list of
    -- the stage and those downstream of it; then the stage resumes with `()`.
    let stopArm := if i == 0 then
        next (states i s!"(inr (inr (inl io_ks{i}_{sfx})) : {st.stTy})") (turnTo i "inl ()")
      else
        let t := s!"io_ts{i}_{sfx}"
        let upCall := call s!"io_cu{i}_{sfx}" (tup ((up i).map sv)) s!"cu{i}_{sfx}"
        let dnCall := call s!"io_cd{i}_{sfx}" (tup ((down i).map fun j => if j == i then t else sv j)) s!"cd{i}_{sfx}"
        -- The stage upstream ends with `()`, its residual (`stop()` is at `K = 1`); a stage above it
        -- is never run again, and is left a loop that runs nothing (`pipe_idle`).
        let idle (j : Nat) : String :=
          let sj := ss[j]!
          let body := s!"nu X. {fAt sj.lr s!"({sj.R}) + U X"} & {fAt sj.lc "1"}"
          let mk := s!"io_ig{j}_{sfx} <- return (unbang (unfold[{body}, 1] pipe_idle[{sj.R}, row ({sj.lr}), row ({sj.lc})])); io_iz{j}_{sfx} <- return ()"
          s!"(inl (thunkv nu_in < {mk}; (nu_out (force io_ig{j}_{sfx} io_iz{j}_{sfx})).1, {mk}; (nu_out (force io_ig{j}_{sfx} io_iz{j}_{sfx})).2 >) : {sj.stTy})"
        let ended := (List.range n).map fun j =>
          if j + 1 < i then idle j else if j + 1 == i then s!"(inr (inr (inr ())) : {ss[j]!.stTy})"
          else if j == i then t else sv j
        s!"{t} : {st.stTy} <- return (inr (inr (inl io_ks{i}_{sfx})));
                    io_su{i}_{sfx} <- {upCall} unwind {dnCall};
                    let () = io_su{i}_{sfx};
                    {next (tup ended) (turnTo i "inr (inr ())")}"
    -- Fwd(a, κ): not yet given a forwarded operation; stored, and the stage resumes.
    let fwdArm := s!"let (io_fa{i}_{sfx}, io_fk{i}_{sfx}) = io_fy{i}_{sfx}; let _ = io_fa{i}_{sfx};
              {next (states i s!"(inr (inr (inl io_fk{i}_{sfx})) : {st.stTy})") (turnTo i "inl ()")}"
    let arm := s!"{ev} <- {stepCall} unwind {coCall};
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
  let turnFn := s!"io_turn_{sfx} : !U ({GS} -o {fAt G s!"({Rlast}) + ({GS})"} & {fAt G "1"}) <- return (!thunkv fun (io_g_{sfx} : {GS}) ->
    < let (io_ss_{sfx}, io_tn_{sfx}) = io_g_{sfx}; {destr ((List.range n).map sv) s!"io_ss_{sfx}" s!"io_sst_{sfx}_"}
      {dispatch s!"io_tn_{sfx}" 0 arms},
      let (io_ss_{sfx}, io_tn_{sfx}) = io_g_{sfx}; let _ = io_tn_{sfx};
      {call s!"io_call_{sfx}" s!"io_ss_{sfx}" s!"cl_{sfx}"} >);\n"
  let ready := tup (cn.stages.map (·.ready))
  let Q := prod (fvs.map (·.2))
  let q := tup (fvs.map (·.1))
  let body := s!"io_cw_{sfx} : !({Q} => U ({Lw})) <- return (!thunkv fun (io_q_{sfx} : {Q}) ->
  {destr (fvs.map (·.1)) s!"io_q_{sfx}" s!"io_qt_{sfx}_"}
  {defs}{turnFn}io_st_{sfx} : {GS} <- return ({ready}, {turnTo (n - 1) "inl ()"});
  io_f_{sfx} <- return (unbang (unfold[{Lw}, {GS}] io_turn_{sfx}));
  return (thunkv nu_in < (nu_out (force io_f_{sfx} io_st_{sfx})).1, (nu_out (force io_f_{sfx} io_st_{sfx})).2 >));
io_pipe_j_{sfx} : {Rlast} <- return ((unbang io_cw_{sfx}) {q});
return io_pipe_j_{sfx}"
  pure body

end Frontend.Elab.Connector
