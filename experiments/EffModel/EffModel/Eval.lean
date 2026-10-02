import EffModel.Syntax

/-!
# EffModel — a definitional interpreter

A CK machine: a control (a term in an environment, or a value being returned) and a stack of
frames. Effects are the stack's business:

- an operation on instance `i` finds the nearest frame for `i`;
  - a **runner** frame (a lend) answers by calling the co-operation on the capability's state,
    in place: no continuation is captured (the comodel–model tensor, Plotkin & Power 2008);
  - a **handler** frame captures the frames above it, and itself, as a continuation `κ`, then runs
    the clause below it (Plotkin & Pretnar's deep handler);
- a `using` frame owns a resource; returning through it runs the destructor;
- **cancelling** `κ` runs the destructors of the frames it holds, innermost first, and nothing
  else: no handler in `κ` sees it (Congard, Munch-Maccagnoni & Douence; Ahman & Bauer's signals).
  An abortive operation cancels `κ` before its clause runs. A resuming clause that ends without
  resuming `κ`, and without returning a value that holds it, cancels it when it ends.

Instances are numbers from a counter (`ν`). Nothing observable exposes a number.
-/

namespace EffModel

inductive Val where
  | unit
  | int (n : Int)
  | bool (b : Bool)
  | pair (a b : Val)
  | inl (a : Val)
  | inr (a : Val)
  | clo (env : List (String × Val)) (M : Tm)
  | rclo (env : List (String × Val)) (f : String) (M : Tm)
  | inst (n : Nat)
  | cap (n : Nat)
  | kont (n : Nat)
  | res (n : Nat)
  | ticket (n : Nat)
  deriving Repr, Inhabited

abbrev Env := List (String × Val)

inductive Frame where
  | arg (v : Val)
  | bind (env : Env) (x : String) (N : Tm)
  | prj (first : Bool)
  | handle (i : Nat) (env : Env) (h : Hnd)
  | runner (i : Nat) (cell : Nat)
  | coopRet (cell : Nat)
  | fin (n : Nat)
  | clauseEnd (k : Nat)
  deriving Repr, Inhabited

/-- What the world sees. -/
inductive Event where
  | out (n : Int)
  | acq (n : Nat)
  | use (n : Nat)
  | free (n : Nat)
  | punch (n : Nat)
  deriving DecidableEq, Repr

inductive Outcome where
  | ret (v : String)
  | unhandled (op : String)
  | stuck (msg : String)
  | fuel
  deriving DecidableEq, Repr

/-- The observable of a run: the outcome, the world's trace, and what was left unreleased. -/
structure Obs where
  out : Outcome
  trace : List Event
  leaks : List String
  deriving DecidableEq, Repr

structure Cell where
  env : Env
  co : Hnd
  state : Val
  live : Bool

inductive KStatus where
  | fresh | used | cancelled
  deriving DecidableEq

structure Kont where
  frames : List Frame
  mode : Mode
  status : KStatus

inductive Ctl where
  | eval (M : Tm) (env : Env)
  | ret (v : Val)

structure St where
  ctl : Ctl
  stack : List Frame := []
  cells : List (Nat × Cell) := []
  konts : List (Nat × Kont) := []
  next : Nat := 0
  trace : List Event := []

inductive Step where
  | next (s : St)
  | done (o : Outcome) (s : St)

/-! ## Helpers -/

mutual
def Val.mentions (k : Nat) : Val → Bool
  | .kont n => n == k
  | .pair a b => a.mentions k || b.mentions k
  | .inl a | .inr a => a.mentions k
  | .clo env _ | .rclo env _ _ => envMentions k env
  | _ => false
def envMentions (k : Nat) : List (String × Val) → Bool
  | [] => false
  | (_, v) :: rest => v.mentions k || envMentions k rest
end

def Val.render : Val → String
  | .unit => "()"
  | .int n => toString n
  | .bool b => toString b
  | .pair a b => s!"({a.render}, {b.render})"
  | .inl a => s!"inl {a.render}"
  | .inr a => s!"inr {a.render}"
  | .clo _ _ | .rclo _ _ _ => "<thunk>"
  | .inst _ => "<inst>"
  | .cap _ => "<cap>"
  | .kont _ => "<kont>"
  | .res _ => "<res>"
  | .ticket _ => "<ticket>"

def evalV (env : Env) : Tm → Option Val
  | .var x => env.lookup x
  | .unit => some .unit
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .pair a b => do pure (.pair (← evalV env a) (← evalV env b))
  | .inl a _ => do pure (.inl (← evalV env a))
  | .inr _ b => do pure (.inr (← evalV env b))
  | .thunk _ M => some (.clo env M)
  | .fix f _ _ M => some (.rclo env f M)
  | _ => none

def Hnd.retCl : Hnd → String × Tm
  | .ret x M => (x, M)
  | .cl _ _ _ _ rest => rest.retCl

def Hnd.find (o : String) : Hnd → Option (String × String × Tm)
  | .ret _ _ => none
  | .cl o' p k M rest => if o' == o then some (p, k, M) else rest.find o

def opSig (sigs : Sigs) (o : String) : Option OpSig :=
  sigs.findSome? (fun (_, ops) => ops.find? (·.name == o))

/-- The argument waiting for a function, past the frames that only watch returns. -/
def popArg : List Frame → Option (Val × List Frame)
  | .arg v :: st => some (v, st)
  | .clauseEnd k :: st => (popArg st).map fun (v, st') => (v, .clauseEnd k :: st')
  | _ => none

def popPrj : List Frame → Option (Bool × List Frame)
  | .prj b :: st => some (b, st)
  | .clauseEnd k :: st => (popPrj st).map fun (b, st') => (b, .clauseEnd k :: st')
  | _ => none

/-- The nearest frame for instance `i`, and its depth. -/
def findFrame (i : Nat) : List Frame → Nat → Option (Nat × Frame)
  | [], _ => none
  | f :: st, d =>
      match f with
      | .handle j _ _ | .runner j _ => if i == j then some (d, f) else findFrame i st (d + 1)
      | _ => findFrame i st (d + 1)

def St.out (s : St) (e : Event) : St := { s with trace := e :: s.trace }

/-- Cancel a continuation: run the destructors it holds, innermost first. -/
def St.cancel (s : St) (k : Nat) : St :=
  match s.konts.lookup k with
  | none => s
  | some kt =>
      let s := kt.frames.foldl (fun s f => match f with | .fin n => s.out (.free n) | _ => s) s
      { s with konts := s.konts.map (fun p => if p.1 == k then (k, { kt with status := .cancelled })
                                               else p) }

def St.setCell (s : St) (n : Nat) (c : Cell) : St :=
  { s with cells := s.cells.map (fun p => if p.1 == n then (n, c) else p) }

def St.fresh (s : St) : Nat × St := (s.next, { s with next := s.next + 1 })

/-! ## The step -/

def retTo (s : St) (v : Val) : Step :=
  match s.stack with
  | [] => .done (.ret v.render) s
  | .bind env x N :: st => .next { s with ctl := .eval N ((x, v) :: env), stack := st }
  | .handle _ env h :: st =>
      let (x, N) := h.retCl
      .next { s with ctl := .eval N ((x, v) :: env), stack := st }
  | .runner _ _ :: st => .next { s with ctl := .ret v, stack := st }
  | .coopRet n :: st =>
      match v, s.cells.lookup n with
      | .pair w s', some c => .next { (s.setCell n { c with state := s' }) with ctl := .ret w, stack := st }
      | _, _ => .done (.stuck "a co-operation did not answer a pair") s
  | .fin n :: st => .next { (s.out (.free n)) with ctl := .ret v, stack := st }
  | .clauseEnd k :: st =>
      let s' := match s.konts.lookup k with
        | some kt => if kt.status == KStatus.fresh && !v.mentions k then s.cancel k else s
        | none => s
      .next { s' with ctl := .ret v, stack := st }
  | _ :: _ => .done (.stuck "a value where a function or a record was expected") s

def evalStep (sigs : Sigs) (s : St) (M : Tm) (env : Env) : Step :=
  let val (t : Tm) (k : Val → Step) : Step :=
    match evalV env t with
    | some v => k v
    | none => .done (.stuck "an ill-formed value") s
  let go (M : Tm) (env : Env) (st : List Frame) : Step := .next { s with ctl := .eval M env, stack := st }
  let ret (v : Val) (s : St) : Step := .next { s with ctl := .ret v }
  match M with
  | .ret v => val v fun v => ret v s
  | .bind M x N => go M env (.bind env x N :: s.stack)
  | .lam x _ M =>
      match popArg s.stack with
      | some (v, st) => go M ((x, v) :: env) st
      | none => if s.stack.all (fun f => match f with | .clauseEnd _ => true | _ => false)
                then .done (.ret "<fun>") s else .done (.stuck "a function returned") s
  | .app M v => val v fun v => go M env (.arg v :: s.stack)
  | .force v => val v fun
      | .clo env' M => go M env' s.stack
      | .rclo env' f M => go M ((f, .rclo env' f M) :: env') s.stack
      | .kont k =>
          match popArg s.stack, s.konts.lookup k with
          | some (w, st), some kt =>
              if kt.status != KStatus.fresh && !kt.mode.c then
                .done (.stuck "a continuation resumed twice, or after it was cancelled") s
              else
                let konts := s.konts.map (fun p => if p.1 == k then (k, { kt with status := .used })
                                                   else p)
                .next { s with ctl := .ret w, stack := kt.frames ++ st, konts }
          | _, _ => .done (.stuck "a continuation forced without an argument") s
      | _ => .done (.stuck "force of a non-thunk") s
  | .rcd M N =>
      match popPrj s.stack with
      | some (b, st) => go (if b then M else N) env st
      | none => .done (.ret "<record>") s
  | .prj b M => go M env (.prj b :: s.stack)
  | .split v x y M => val v fun
      | .pair a b => go M ((y, b) :: (x, a) :: env) s.stack
      | _ => .done (.stuck "split of a non-pair") s
  | .case v x M y N => val v fun
      | .inl a => go M ((x, a) :: env) s.stack
      | .inr b => go N ((y, b) :: env) s.stack
      | _ => .done (.stuck "case of a non-sum") s
  | .ite v M N => val v fun
      | .bool true => go M env s.stack
      | .bool false => go N env s.stack
      | _ => .done (.stuck "if of a non-bool") s
  | .absurd _ _ => .done (.stuck "absurd") s
  | .prim p a b => val a fun a => val b fun b =>
      match a, b with
      | .int m, .int n =>
          ret (match p with
            | .add => .int (m + n) | .sub => .int (m - n)
            | .lt => .bool (decide (m < n)) | .eq => .bool (m == n)) s
      | _, _ => .done (.stuck "prim of non-ints") s
  | .emit v => val v fun
      | .int n => ret .unit (s.out (.out n))
      | _ => .done (.stuck "emit of a non-int") s
  | .op x o v y M => val (.var x) fun xi => val v fun v =>
      match xi with
      | .inst i =>
          match findFrame i s.stack 0 with
          | none => .done (.unhandled o) s
          | some (_, .runner _ n) =>
              match s.cells.lookup n with
              | some c =>
                  if !c.live then .done (.stuck "a lent capability used after its owner consumed it") s else
                  match c.co.find o with
                  | some (p, _, body) =>
                      .next { s with ctl := .eval body ((p, .pair v c.state) :: c.env),
                                     stack := .coopRet n :: .bind env y M :: s.stack }
                  | none => .done (.unhandled o) s
              | none => .done (.stuck "a runner without a capability") s
          | some (d, f@(.handle _ henv h)) =>
              match h.find o, opSig sigs o with
              | some (p, k, body), some sg =>
                  let (kid, s) := s.fresh
                  let frames := .bind env y M :: (s.stack.take d ++ [f])
                  let rest := s.stack.drop (d + 1)
                  let s := { s with konts := (kid, ⟨frames, sg.k, KStatus.fresh⟩) :: s.konts }
                  let env' := (k, .kont kid) :: (p, v) :: henv
                  if sg.abortive then
                    .next { (s.cancel kid) with ctl := .eval body env', stack := rest }
                  else
                    .next { s with ctl := .eval body env', stack := .clauseEnd kid :: rest }
              | _, _ => .done (.unhandled o) s
          | some _ => .done (.stuck "not a handler frame") s
      | _ => .done (.stuck "an operation on a non-instance") s
  | .handle x _ h _ _ M =>
      let (i, s) := s.fresh
      .next { s with ctl := .eval M ((x, .inst i) :: env), stack := .handle i env h :: s.stack }
  | .handleAt x h _ _ M => val (.var x) fun
      | .inst i => go M env (.handle i env h :: s.stack)
      | _ => .done (.stuck "handleAt of a non-instance") s
  | .nu x _ _ M =>
      let (i, s) := s.fresh
      .next { s with ctl := .eval M ((x, .inst i) :: env) }
  | .ieq x y => val (.var x) fun a => val (.var y) fun b =>
      match a, b with
      | .inst i, .inst j => ret (.bool (i == j)) s
      | _, _ => .done (.stuck "ieq of non-instances") s
  | .newcap _ _ co v => val v fun v =>
      let (n, s) := s.fresh
      ret (.cap n) { s with cells := (n, ⟨env, co, v, true⟩) :: s.cells }
  | .getcap v => val v fun
      | .cap n =>
          match s.cells.lookup n with
          | some c =>
              if c.live then ret c.state (s.setCell n { c with live := false })
              else .done (.stuck "a capability consumed twice") s
          | none => .done (.stuck "no such capability") s
      | _ => .done (.stuck "getcap of a non-capability") s
  | .lend c x M => val (.var c) fun
      | .cap n =>
          let (i, s) := s.fresh
          .next { s with ctl := .eval M ((x, .inst i) :: env), stack := .runner i n :: s.stack }
      | _ => .done (.stuck "lend of a non-capability") s
  | .using x n M =>
      let s := s.out (.acq n)
      .next { s with ctl := .eval M ((x, .res n) :: env), stack := .fin n :: s.stack }
  | .use v => val v fun
      | .res n => ret .unit (s.out (.use n))
      | _ => .done (.stuck "use of a non-resource") s
  | .drop w => val w fun w =>
      let ks := s.konts.filter (fun (i, kt) => kt.status == KStatus.fresh && w.mentions i)
      ret .unit (ks.foldl (fun s (i, _) => s.cancel i) s)
  | .ticket n => ret (.ticket n) s
  | .punch v => val v fun
      | .ticket n => ret .unit (s.out (.punch n))
      | _ => .done (.stuck "punch of a non-ticket") s
  | .rlam _ _ M => go M env s.stack
  | .rapp M _ => go M env s.stack
  | _ => .done (.stuck "a value in computation position") s

def step (sigs : Sigs) (s : St) : Step :=
  match s.ctl with
  | .ret v => retTo s v
  | .eval M env => evalStep sigs s M env

def loop (sigs : Sigs) : Nat → St → Outcome × St
  | 0, s => (.fuel, s)
  | n + 1, s =>
      match step sigs s with
      | .next s' => loop sigs n s'
      | .done o s' => (o, s')

/-- Resources acquired and not freed, and capabilities never consumed. -/
def leaks (s : St) : List String :=
  let tr := s.trace.reverse
  let acq := tr.filterMap (fun e => match e with | .acq n => some n | _ => none)
  let freed := tr.filterMap (fun e => match e with | .free n => some n | _ => none)
  let res := acq.filter (fun n => acq.count n > freed.count n) |>.eraseDups
  let caps := s.cells.filter (·.2.live) |>.length
  let dbl := freed.filter (fun n => freed.count n > acq.count n) |>.eraseDups
  res.map (s!"res {·}") ++ dbl.map (s!"res {·} freed twice") ++ (if caps == 0 then [] else [s!"{caps} live capabilities"])

/-- Run a closed program. -/
def run (sigs : Sigs) (M : Tm) (fuel : Nat := 20000) : Obs :=
  let (o, s) := loop sigs fuel { ctl := .eval M [] }
  ⟨o, s.trace.reverse, leaks s⟩

end EffModel
