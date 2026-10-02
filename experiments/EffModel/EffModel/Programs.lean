import EffModel.Prelude

/-!
# EffModel — the programs that broke us

Each program is typed by `typecheck` and run by `run`, with no rule written for it. The
expected observable is stated next to it.
-/

namespace EffModel

/-! ## Types used below -/

def bFail : Bound := ⟨Mode.aff, false⟩
def bTick : Bound := ⟨Mode.aff, false⟩
def bCtr : Bound := Bound.none

/-- A callback: `U(1 ⇒ρ F int)`. -/
def cbT (ρ : Row) : VTy := .thunk Mode.unr [] (.arr "u" .unit ρ (.F .int))
/-- A function that takes a callback: `U(cb ρ ⇒ρ F int)`. -/
def hofT (ρ : Row) : VTy := .thunk Mode.unr [] (.arr "k" (cbT ρ) ρ (.F .int))
/-- A job for a policy: given a `Tick` and a `Fail` instance, it may tick, fail, and do `ρ`. -/
def jobT (ρ : Row) : VTy :=
  .thunk Mode.unr [] (.arr "t" (.inst "Tick" bTick) []
    (.arr "f" (.inst "Fail" bFail) (.i "t" :: .i "f" :: ρ) (.F .int)))
/-- A policy: runs a job, answering `-1` when it gives up. -/
def polC (ρ : Row) : CTy := .arr "g" (jobT ρ) ρ (.F .int)
def polT : VTy := .thunk Mode.unr [] (.allR "r" Bound.top [] (polC [.r "r"]))

/-- `with newcap c := 0 { lend c as x { M } }`, then emit the final state and answer `M`'s. -/
def withCounter (c x : String) (M : Tm) : Tm :=
  .bind (.newcap "Ctr" .int coCtr (n 0)) c
    (.bind (.lend c x M) "res"
      (.bind (.getcap (v c)) "st" (emitThen (v "st") (.ret (v "res")))))

/-! ## 1. `retry` over a lent capability -/

/-- `retry : ∀r. int ⇒ U((f : Fail) ⇒[f, r] F int) ⇒[r] F (int + 1)`, recursive. -/
def retryC : CTy :=
  .allR "r" Bound.top []
    (.arr "nt" .int []
      (.arr "g" (.thunk Mode.unr [] (.arr "f" (.inst "Fail" bFail) [.i "f", .r "r"] (.F .int)))
        [.r "r"] (.F (.sum .int .unit))))

def retry : Tm :=
  .fix "retry" [] retryC (.rlam "r" Bound.top (.lam "nt" .int (.lam "g"
    (.thunk Mode.unr [] (.arr "f" (.inst "Fail" bFail) [.i "f", .r "r"] (.F .int)))
    (.bind (.handle "f2" "Fail" (hOpt .int) [] (.F (.sum .int .unit)) (.app (.force (v "g")) (v "f2")))
      "res"
      (.case (v "res") "a" (.ret (.inl (v "a") .unit)) "_"
        (.bind (.prim .eq (v "nt") (n 0)) "z"
          (.ite (v "z") (.ret (.inr .int .unit))
            (.bind (sub (v "nt") (n 1)) "n1"
              (.app (.app (.rapp (.force (v "retry")) [.r "r"]) (v "n1")) (v "g"))))))))))

/-- Each attempt increments the lent counter and fails until it reads 3. The counter's state
survives each failed attempt: the capability is lent from outside the `Fail` handler. -/
def pRetry : Tm :=
  withCounter "c" "x"
    (.app (.app (.rapp (.force retry) [.i "x"]) (n 5))
      (.thunk Mode.unr (.lam "f" (.inst "Fail" bFail)
        (inc "x" (get "x" "g" (.bind (.prim .lt (v "g") (n 3)) "b"
          (.ite (v "b") (raise "f") (.ret (v "g")))))))))

/-! ## 2. Callbacks that take callbacks -/

/-- `twice : ∀r. U(cb r ⇒r F int)`: calls its callback twice and adds. -/
def twice : Tm :=
  .thunk Mode.unr (.rlam "r" Bound.top (.lam "k" (cbT [.r "r"])
    (.bind (call (v "k") .unit) "a" (.bind (call (v "k") .unit) "b" (add (v "a") (v "b"))))))

/-- `around : ∀r. U(hof (r, l) ⇒ cb r ⇒(r, l) F int)`: hands `h` a callback that logs to `l`
and then calls `k`. A callback that takes a callback, given a callback. -/
def around : Tm :=
  .thunk Mode.unr (.rlam "r" Bound.top (.lam "h" (hofT [.r "r", .i "l"]) (.lam "k" (cbT [.r "r"])
    (.app (.force (v "h"))
      (.thunk Mode.unr (.lam "u" .unit (log "l" (n 100) (.app (.force (v "k")) (v "u")))))))))

def pCallbacks : Tm :=
  .handle "l" "Log" hPrint [] (.F .int)
    (.bind (.ret twice) "tw" (.bind (.ret around) "ar"
      (withCounter "c" "x"
        (.app
          (.app (.rapp (.force (v "ar")) [.i "x"])
            (.thunk Mode.unr (.rapp (.force (v "tw")) [.i "x", .i "l"])))
          (.thunk Mode.unr (.lam "u" .unit (inc "x" (get "x" "g" (.ret (v "g"))))))))))

/-! ## 3. Storing and returning a computation -/

/-- `mk : (x : Ctr) ⇒ F (U[x] F int)`: returns a computation over the instance it is given. -/
def mkTicker : Tm :=
  .thunk Mode.unr (.lam "x" (.inst "Ctr" bCtr)
    (.ret (.thunk Mode.unr (inc "x" (get "x" "g" (.ret (v "g")))))))

def pStore : Tm :=
  withCounter "c" "x"
    (.bind (.app (.force mkTicker) (v "x")) "t"
      (.bind (.ret (.pair (v "t") (n 10))) "p"
        (.split (v "p") "t1" "k"
          (.bind (.force (v "t1")) "a" (.bind (.force (v "t1")) "b"
            (.bind (add (v "a") (v "b")) "s" (add (v "s") (v "k"))))))))

/-! ## 4. A retry/timeout policy value -/

/-- Retry up to `nt` more times; each attempt gets fresh `Tick` and `Fail` instances. -/
def retryPolN : Tm :=
  .fix "rp" [] (.allR "r" Bound.top [] (.arr "nt" .int [] (polC [.r "r"])))
    (.rlam "r" Bound.top (.lam "nt" .int (.lam "g" (jobT [.r "r"])
      (.bind (.handle "t" "Tick" hTickIgnore [] (.F (.sum .int .unit))
          (.handle "f" "Fail" (hOpt .int) [] (.F (.sum .int .unit))
            (.app (.app (.force (v "g")) (v "t")) (v "f"))))
        "res"
        (.case (v "res") "a" (.ret (v "a")) "_"
          (.bind (.prim .eq (v "nt") (n 0)) "z"
            (.ite (v "z") (.ret (n (-1)))
              (.bind (sub (v "nt") (n 1)) "n1"
                (.app (.app (.rapp (.force (v "rp")) [.r "r"]) (v "n1")) (v "g"))))))))))

/-- A policy built at run time from a number: retry `k` times. -/
def mkRetry : Tm :=
  .thunk Mode.unr (.lam "k" .int (.ret (.thunk Mode.unr (.rlam "r" Bound.top
    (.app (.rapp (.force retryPolN) [.r "r"]) (v "k"))))))

/-- A policy built at run time from a number: a timeout of `b` ticks. -/
def mkTimeout : Tm :=
  .thunk Mode.unr (.lam "b" .int (.ret (.thunk Mode.unr (.rlam "r" Bound.top
    (.lam "g" (jobT [.r "r"])
      (.bind
        (.app (.handle "t" "Tick" hTimeout [] (.arr "b" .int [.r "r"] (.F (.sum .int .unit)))
            (.handle "f" "Fail" (hOpt .int) [] (.F (.sum .int .unit))
              (.app (.app (.force (v "g")) (v "t")) (v "f"))))
          (v "b"))
        "res" (.case (v "res") "a" (.ret (v "a")) "_" (.ret (n (-1))))))))))

/-- A job: counts its attempts on the lent counter, ticks three times, fails on its first
attempt. -/
def job : Tm :=
  .thunk Mode.unr (.lam "t" (.inst "Tick" bTick) (.lam "f" (.inst "Fail" bFail)
    (inc "x" (get "x" "g" (tick "t" (tick "t" (tick "t"
      (.bind (.prim .lt (v "g") (n 2)) "b" (.ite (v "b") (raise "f") (.ret (v "g")))))))))))

/-- Three policies stored in data, chosen by a flag, applied to the same job. -/
def pPolicy : Tm :=
  withCounter "c" "x"
    (.bind (.app (.force mkRetry) (n 2)) "pr"
    (.bind (.app (.force mkTimeout) (n 5)) "pt5"
    (.bind (.app (.force mkTimeout) (n 1)) "pt1"
    (.bind (.ret (.pair (v "pr") (.pair (v "pt5") (v "pt1")))) "pols"
    (.split (v "pols") "p1" "rest" (.split (v "rest") "p2" "p3"
      (.bind (.app (.rapp (.force (v "p1")) [.i "x"]) job) "r1"
      (.bind (.app (.rapp (.force (v "p2")) [.i "x"]) job) "r2"
      (.bind (.app (.rapp (.force (v "p3")) [.i "x"]) job) "r3"
        (emitThen (v "r1") (emitThen (v "r2") (emitThen (v "r3") (.ret (n 0))))))))))))))

/-! ## 5. A reader object: `next : Log`, `close : Fail` -/

/-- A record of two methods over a lent counter, each with its own row. -/
def reader : Tm :=
  .thunk Mode.unr (.rcd
    (inc "x" (get "x" "g" (log "l" (v "g") (.ret (v "g")))))
    (raise "f"))

def pReader : Tm :=
  withCounter "c" "x"
    (.handle "f" "Fail" (hOpt .int) [] (.F (.sum .int .unit))
      (.handle "l" "Log" hPrint [] (.F .int)
        (.bind (.ret reader) "rd"
          (.bind (.prj true (.force (v "rd"))) "a"
          (.bind (.prj true (.force (v "rd"))) "b"
          (.bind (.prj false (.force (v "rd"))) "_c"
            (add (v "a") (v "b"))))))))

/-! ## 6. A recursion that logs and yields -/

def countdown : Tm :=
  .fix "cd" [] (.arr "k" .int [.i "l", .i "y"] (.F .int))
    (.lam "k" .int (.bind (.prim .eq (v "k") (n 0)) "z"
      (.ite (v "z") (.ret (n 0))
        (log "l" (v "k") (yld "y" (v "k")
          (.bind (sub (v "k") (n 1)) "k1"
            (.bind (.app (.force (v "cd")) (v "k1")) "r" (add (v "r") (v "k")))))))))

/-- Logs printed as they happen; yields summed by a handler into a function type, the total
emitted at the end. -/
def pRecursion : Tm :=
  .handle "l" "Log" hPrint [] (.F .int)
    ((yieldSum.wrap "y" .int [.i "l"] (.app (.force countdown) (n 3))).get!.1)

/-! ## 7. A generator holding a resource across `yield`

The resource is owned by a `using` frame inside the generator. The frame is in every
continuation captured at a `yield`. So:

- a **push** consumer that stops early drops the continuation, which cancels it, which runs the
  frame's destructor (`take`);
- a **pull** consumer gets the generator as a stream (`hStream` returns the continuation); the
  stream is linear, so it must be pulled to its end or dropped, and dropping it cancels the
  continuation it holds.
-/

def gen : Tm :=
  .using "r" 1 (yld "y" (n 1) (seq (.use (v "r")) (yld "y" (n 2) (seq (.use (v "r")) (.ret (n 0))))))

def pGenTake : Tm := .app (.handle "y" "Yield" hTake [] (takeC []) gen) (n 1)

def pGenPullOne : Tm :=
  .bind (.handle "y" "Yield" hStream [] streamC gen) "s0"
    (.case (v "s0") "a" (.ret (v "a")) "q"
      (.split (v "q") "p" "rest" (emitThen (v "p") (seq (.drop (v "rest")) (.ret (n 0))))))

/-- Pull a stream to its end, emitting each element. -/
def pullAll : Tm :=
  .fix "pull" [] (.arr "s" (.stream [] .int) [] (.F .int))
    (.lam "s" (.stream [] .int) (.bind (.force (v "s")) "o"
      (.case (v "o") "a" (.ret (v "a")) "q"
        (.split (v "q") "p" "rest" (emitThen (v "p") (.app (.force (v "pull")) (v "rest")))))))

def pGenPullAll : Tm :=
  .bind (.handle "y" "Yield" hStream [] streamC gen) "s0"
    (.case (v "s0") "a" (.ret (v "a")) "q"
      (.split (v "q") "p" "rest" (emitThen (v "p") (.app (.force pullAll) (v "rest")))))

/-! ## No accidental handling, as a program -/

/-- `hof` handles a `Fail` of its own around the callback it is given. The callback fails on the
caller's instance, which `hof` cannot name: the caller's handler answers. -/
def hof : Tm :=
  .thunk Mode.unr (.rlam "r" Bound.top (.lam "g" (cbT [.r "r"])
    (.handle "f2" "Fail" (hDefault (n 0)) [] (.F .int) (call (v "g") .unit))))

def pAbstraction : Tm :=
  .handle "f" "Fail" (hDefault (n 7)) [] (.F .int)
    (.app (.rapp (.force hof) [.i "f"]) (.thunk Mode.unr (.lam "u" .unit (raise "f"))))

/-! ## The table -/

structure Prog where
  name : String
  term : Tm
  expect : Obs

open Event in
def programs : List Prog := [
  ⟨"retry over a lent capability", pRetry, ⟨.ret "inl 3", [out 3], []⟩⟩,
  ⟨"callbacks taking callbacks", pCallbacks, ⟨.ret "3", [out 100, out 100, out 2], []⟩⟩,
  ⟨"storing and returning a computation", pStore, ⟨.ret "13", [out 2], []⟩⟩,
  ⟨"a retry/timeout policy value", pPolicy, ⟨.ret "0", [out 2, out 3, out (-1), out 4], []⟩⟩,
  ⟨"a reader object (next: Log, close: Fail)", pReader, ⟨.ret "inr ()", [out 1, out 2, out 2], []⟩⟩,
  ⟨"a recursion that logs and yields", pRecursion, ⟨.ret "6", [out 3, out 2, out 1, out 6], []⟩⟩,
  ⟨"a generator holding a resource, push, stopped early", pGenTake,
    ⟨.ret "inr ()", [acq 1, out 1, use 1, free 1], []⟩⟩,
  ⟨"a generator holding a resource, pulled once and dropped", pGenPullOne,
    ⟨.ret "0", [acq 1, out 1, free 1], []⟩⟩,
  ⟨"a generator holding a resource, pulled to its end", pGenPullAll,
    ⟨.ret "0", [acq 1, out 1, use 1, out 2, use 1, free 1], []⟩⟩,
  ⟨"no accidental handling", pAbstraction, ⟨.ret "7", [], []⟩⟩]

def Prog.typed (p : Prog) : Bool := accepts sigs p.term
def Prog.runsAsExpected (p : Prog) : Bool := run sigs p.term == p.expect

end EffModel
