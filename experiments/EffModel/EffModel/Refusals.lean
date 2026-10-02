import EffModel.Programs

/-!
# EffModel — what linearity must refuse

Each refusal is a program the typing rejects, with the rule that rejects it, beside a control:
the nearest program that is accepted and runs. Where running the rejected program shows the harm,
that run is recorded too.
-/

namespace EffModel

def newCtr (c : String) (M : Tm) : Tm := .bind (.newcap "Ctr" .int coCtr (n 0)) c M

structure Refusal where
  name : String
  rejected : Tm
  /-- A fragment of the expected message: names the rule. -/
  rule : String
  control : Tm
  controlObs : Obs

def Refusal.refused (r : Refusal) : Bool :=
  ((rejection sigs r.rejected).splitOn r.rule).length > 1

def Refusal.controlOK (r : Refusal) : Bool :=
  accepts sigs r.control && run sigs r.control == r.controlObs

/-! ## 1. Duplicating an owned computation -/

/-- A thunk that consumes the capability is linear: forcing it twice is two uses. -/
def dupForcedTwice : Tm :=
  newCtr "c" (.bind (.ret (.thunk Mode.lin (.getcap (v "c")))) "t"
    (.bind (.force (v "t")) "a" (.bind (.force (v "t")) "b" (add (v "a") (v "b")))))

/-- Nor can it be made unrestricted: independence. -/
def dupPromoted : Tm :=
  newCtr "c" (.bind (.ret (.thunk Mode.unr (.getcap (v "c")))) "t" (.force (v "t")))

def dupControl : Tm :=
  newCtr "c" (.bind (.ret (.thunk Mode.lin (.getcap (v "c")))) "t" (.force (v "t")))

/-! ## 2. Multi-shot over a linear context -/

def multiLinear : Tm :=
  .handle "ch" "Choose" hAllSum [] (.F .int)
    (newCtr "c" (.bind (.op "ch" "choose" .unit "b" (.ret (v "b"))) "b2"
      (.bind (.getcap (v "c")) "s" (.ite (v "b2") (.ret (v "s")) (.ret (n 1))))))

def multiControl : Tm :=
  .handle "ch" "Choose" hAllSum [] (.F .int)
    (.bind (.ret (n 5)) "k" (.bind (.op "ch" "choose" .unit "b" (.ret (v "b"))) "b2"
      (.ite (v "b2") (.ret (v "k")) (.ret (n 1)))))

/-! ## 3. A suspended continuation holding a lend (T1) -/

/-- Consume a stream's first step: answer its result or its first element, dropping the rest. -/
def firstOf (s : Tm) : Tm :=
  .case s "a" (.ret (v "a")) "q" (.split (v "q") "p" "rest" (seq (.drop (v "rest")) (.ret (v "p"))))

/-- A stream handler keeps the continuation of `yield`; the continuation holds the lend. The
capability is owned outside the handler, so T1 is the only rule that applies. -/
def t1Lend : Tm :=
  newCtr "c"
    (.bind (.handle "y" "Yield" hStream [] streamC (.lend "c" "x" (yld "y" (n 1) (inc "x" (.ret (n 0))))))
      "s0" (.bind (.getcap (v "c")) "s" (firstOf (v "s0"))))

/-- The same through a callback: the lend's body only calls `g`, whose row says it yields. -/
def t1Callback : Tm :=
  newCtr "c"
    (.bind (.handle "y" "Yield" hStream [] streamC
        (.bind (.ret (.thunk Mode.unr (.lam "u" .unit (yld "y" (n 1) (.ret (n 0)))))) "g"
          (.lend "c" "x" (inc "x" (call (v "g") .unit)))))
      "s0" (.bind (.getcap (v "c")) "s" (firstOf (v "s0"))))

/-- The harm, untyped: the stream escapes the lend; the owner consumes the capability; pulling
the stream resumes inside the ended lend. -/
def t1Harm : Tm :=
  newCtr "c"
    (.bind (.handle "y" "Yield" hStream [] streamC
        (.lend "c" "x" (yld "y" (n 1) (inc "x" (get "x" "g" (.ret (v "g")))))))
      "s0"
      (.bind (.getcap (v "c")) "st"
        (.case (v "s0") "a" (.ret (v "a")) "q"
          (.split (v "q") "p" "rest" (.bind (.force (v "rest")) "o" (firstOf (v "o")))))))

/-- Control: a consumer that resumes in place (tail-resumptive) does not keep the continuation. -/
def t1Control : Tm :=
  newCtr "c"
    (.bind (.handle "y" "Yield" hYieldPrint [] (.F .int)
        (.lend "c" "x" (yld "y" (n 1) (inc "x" (get "x" "g" (.ret (v "g")))))))
      "a" (.bind (.getcap (v "c")) "s" (add (v "s") (v "a"))))

/-! ## 4. An owned value with no destructor across an affine operation -/

/-- The consumer takes one element and stops, dropping the continuation that holds `c`. -/
def noDtor : Tm :=
  .app (.handle "y" "Yield" hTake [] (takeC [])
    (newCtr "c" (yld "y" (n 1) (yld "y" (n 2) (.getcap (v "c")))))) (n 1)

/-- The same across an abortive one. -/
def noDtorAbort : Tm :=
  .handle "f" "Fail" (hDefault (n 0)) [] (.F .int)
    (newCtr "c" (.bind (raise "f") "q" (.getcap (v "c"))))

/-- Control: a resource with a destructor (a `using` frame) crosses the same operation, and a
consumer that stops early runs the destructor. -/
def dtorControl : Tm := pGenTake

/-! ## The relevant mode (σ = {C}) -/

/-- A ticket may not be dropped. -/
def ticketDropped : Tm := .bind (.ticket 1) "t" (.ret (n 0))
/-- A ticket may be used twice. -/
def ticketTwice : Tm := .bind (.ticket 1) "t" (seq (.punch (v "t")) (seq (.punch (v "t")) (.ret (n 0))))
/-- A continuation that may be dropped (affine) may not capture a ticket. -/
def ticketAffine : Tm :=
  .handle "y" "Yield" hYieldPrint [] (.F .int)
    (.bind (.ticket 1) "t" (yld "y" (n 1) (seq (.punch (v "t")) (.ret (n 0)))))
/-- A continuation resumed at least once (relevant) may. -/
def hAgain : Hnd :=
  .cl "again" "p" "k" (seq (call (v "k") .unit) (call (v "k") .unit)) (.ret "a" (.ret (n 0)))
def ticketRelevant : Tm :=
  .handle "g" "Again" hAgain [] (.F .int)
    (.bind (.ticket 1) "t" (.op "g" "again" .unit "_" (seq (.punch (v "t")) (.ret (n 0)))))

/-! ## Scope -/

/-- A computation over a lent instance cannot leave the lend. -/
def escapeLend : Tm :=
  newCtr "c" (.bind (.lend "c" "x" (.ret (.thunk Mode.unr (inc "x" (.ret (n 0)))))) "t"
    (.bind (.getcap (v "c")) "s" (.ret (n 0))))

/-- A lent place is not usable while lent. -/
def useWhileLent : Tm := newCtr "c" (.lend "c" "x" (.getcap (v "c")))

def refusals : List Refusal := [
  ⟨"duplicating an owned computation (forced twice)", dupForcedTwice, "grade: t", dupControl,
    ⟨.ret "0", [], []⟩⟩,
  ⟨"duplicating an owned computation (promoted to !)", dupPromoted, "independence: c", dupControl,
    ⟨.ret "0", [], []⟩⟩,
  ⟨"multi-shot over a linear context", multiLinear, "independence: c", multiControl,
    ⟨.ret "6", [], []⟩⟩,
  ⟨"a suspended continuation holding a lend (T1)", t1Lend, "T1", t1Control,
    ⟨.ret "2", [.out 1], []⟩⟩,
  ⟨"a suspended continuation holding a lend (T1), through a callback", t1Callback, "T1",
    t1Control, ⟨.ret "2", [.out 1], []⟩⟩,
  ⟨"an owned value with no destructor across an affine operation", noDtor, "independence: c",
    dtorControl, ⟨.ret "inr ()", [.acq 1, .out 1, .use 1, .free 1], []⟩⟩,
  ⟨"an owned value with no destructor across an abortive operation", noDtorAbort,
    "independence: c", dtorControl, ⟨.ret "inr ()", [.acq 1, .out 1, .use 1, .free 1], []⟩⟩,
  ⟨"a relevant value dropped", ticketDropped, "grade: t", ticketTwice,
    ⟨.ret "0", [.punch 1, .punch 1], []⟩⟩,
  ⟨"a relevant value captured by an affine continuation", ticketAffine, "independence: t",
    ticketRelevant, ⟨.ret "0", [.punch 1, .punch 1], []⟩⟩,
  ⟨"a computation over a lent instance leaving the lend", escapeLend, "scope", pStore,
    ⟨.ret "13", [.out 2], []⟩⟩,
  ⟨"a lent place used while lent", useWhileLent, "borrow", pStore, ⟨.ret "13", [.out 2], []⟩⟩]

end EffModel
