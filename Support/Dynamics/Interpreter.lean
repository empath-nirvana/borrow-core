import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Syntax.Terms
import Support.Dynamics.Host
import Support.Dynamics.Arrays

/-!
# Support — Dynamics — Interpreter

`[about ours]`.  An executable interpreter — memories as association lists, a step function, a fuelled run — which `[TR]` does not print (it gives a relation) and which no result of the paper uses.
-/

noncomputable section

namespace BoCa

/-!
### 3.10 · `Mem ∋ µ : Loc ⇀ Val` (the executable counterpart) · [TR] p. 3 · `[repair]`

The `next` field makes `BoCa.step`'s allocation deterministic where `alloc↦` is nondeterministic in `ℓ` (`docs/adjudications.md` W2, D8). The printed map is `BoCa.BoLo.Heap`.
-/
structure Mem where
  cells : List (Loc × Val)
  next  : Loc
  deriving Repr

def Mem.empty : Mem := ⟨[], 0⟩

def Mem.get? (μ : Mem) (ℓ : Loc) : Option Val :=
  μ.cells.find? (·.1 = ℓ) |>.map (·.2)

def Mem.alloc (μ : Mem) (v : Val) : Loc × Mem :=
  (μ.next, ⟨(μ.next, v) :: μ.cells, μ.next + 1⟩)

/-- `n` cells holding `v` at `next, …, next + n − 1`: the block `tab` places.  `[spec §9]` -/
def Mem.allocN (μ : Mem) (n : Nat) (v : Val) : Loc × Mem :=
  (μ.next, ⟨(List.range n).map (fun i => (μ.next + i, v)) ++ μ.cells, μ.next + n⟩)

def Mem.free (μ : Mem) (ℓ : Loc) : Mem :=
  { μ with cells := μ.cells.filter (·.1 ≠ ℓ) }

def Mem.set (μ : Mem) (ℓ : Loc) (v : Val) : Mem :=
  { μ with cells := μ.cells.map fun c => if c.1 = ℓ then (ℓ, v) else c }

/-- `μ[d+k ↦ μ(s+k) | k < n]`, every cell read before any is written, or `none` when a cell of
either range is missing: the write of `sliceCopy`, `Heap.copy`'s counterpart.  `[spec §74]` -/
def Mem.copy? (μ : Mem) (d s n : Nat) : Option Mem :=
  match (List.range n).mapM (fun k => μ.get? (s + k)) with
  | none => none
  | some vs =>
    if (List.range n).all (fun k => (μ.get? (d + k)).isSome) then
      some ((List.range n).zip vs |>.foldl (fun m (k, v) => m.set (d + k) v) μ)
    else none

/-- Non-empty memory at the end of a run is a leak — the bug in Fig. 2b. -/
def Mem.leaked (μ : Mem) : Bool := !μ.cells.isEmpty

inductive Stuck where
  | unboundVar | notAFunction | notAPair | notASum | notAUnit
  | useAfterFree | badPrimArg | badHostArg
  /-- A `perform` or `raise` no handler catches (`[spec §19]`). -/
  | unhandled
  deriving DecidableEq, Repr

/-- The operation a stopped term holds: `perform`, `raise` (`[spec §19]`) or `cancelTo`
(`[spec §51]`). -/
inductive OpKind where
  | perform | raise | cancelTo
  deriving DecidableEq, Repr

inductive Step where
  | next  (μ : Mem) (e : Expr)
  | value (v : Val)
  | stuck (r : Stuck)
  /-- The term is `K[perform p]`, `K[raise p]` or `K[cancelTo p]` (by `kind`), `K` catching
  nothing of it: a stopped operation, for a frame outside to catch (`[spec §19, §51]`). -/
  | op (kind : OpKind) (K : BoLo.Kont) (p : Val)

/-!
### 3.37 · — no printed counterpart; the print gives a relation — · [TR] p. 4 · `[repair]`

A deterministic executable machine where the print gives a relation, with the `K; e` and `injᵢ K` congruences. Nothing in the `wp` development depends on it. `docs/adjudications.md` W2, D8 (determinism), §12.42 (the congruences), §12.1 (evaluation order).
-/
/-- Apply a primitive value to one argument.

    `alloc`, `free` and `load` are saturated by it; `store` is not, and what one
    argument builds is `[TR]` p. 1's printed value `store v` — which is that
    application, so `delta` returns it as a value rather than stepping to one.
    Every value whose head is a primitive appears on the left, so `step` needs
    no arity test: the grammar already says how many arguments each production
    still wants. A host operation is applied by `H.call` (`[spec §8]`); the array steps
    allocate a block at `next` (`[spec §9]`). -/
def delta (H : Host) (μ : Mem) : Expr → Val → Step
  | .prim .alloc,   v => let (ℓ, μ') := μ.alloc v; .next μ' (.loc ℓ)
  | .prim .free,    ⟨.loc ℓ, _⟩ =>
      match μ.get? ℓ with
      | some v => .next (μ.free ℓ) v.val
      | none   => .stuck .useAfterFree
  | .prim .load,    ⟨.loc ℓ, _⟩ =>
      match μ.get? ℓ with
      | some v => .next μ v.val
      | none   => .stuck .useAfterFree
  | .prim .store,   v => .value (.storeV v)
  | .app (.prim .store) (.loc ℓ), v =>
      match μ.get? ℓ with
      | some _ => .next (μ.set ℓ v) .unit
      | none   => .stuck .useAfterFree
  | .prim (.host op), v =>
      match H.call op v with
      | some r => .next μ r.val
      | none   => .stuck .badHostArg
  | .prim .tab, ⟨.pair (.prim (.lit (.i32 c))) f, h⟩ =>
      let (ℓ, μ') := μ.allocN (arrLen c).toNat .unit
      .next μ' (tabFill ⟨f, h.pair_right⟩ ℓ (arrLen c) 0 (arrLen c).toNat)
  | .prim .idx, ⟨.pair (.pair (.loc ℓ) (.prim (.lit (.i32 n)))) (.prim (.lit (.i32 i))), _⟩ =>
      .next μ (idxAns ℓ n i).val
  | .prim .split, ⟨.pair (.pair (.loc ℓ) (.prim (.lit (.i32 n)))) (.prim (.lit (.i32 i))), _⟩ =>
      .next μ (splitAns ℓ n i).val
  | .prim .sliceCopy, ⟨.pair (.pair (.loc ℓd) (.prim (.lit (.i32 nd))))
        (.pair (.prim (.lit (.i32 di))) (.pair (.pair (.loc ℓs) (.prim (.lit (.i32 ns))))
          (.pair (.prim (.lit (.i32 si))) (.prim (.lit (.i32 len)))))), _⟩ =>
      if copyOk nd di ns si len then
        match μ.copy? (ℓd + di.toNat) (ℓs + si.toNat) len.toNat with
        | some μ' => .next μ' (copyAns ℓd nd di ns si len).val
        | none => .stuck .useAfterFree
      else .next μ (copyAns ℓd nd di ns si len).val
  | .prim .drop, ⟨.pair f (.pair (.loc ℓ) (.prim (.lit (.i32 n)))), h⟩ =>
      .next μ (dropFill ⟨f, h.pair_left⟩ ℓ 0 n.toNat)
  | .prim .count, ⟨.pair f (.pair (.prim (.lit (.i32 n))) (.pair (.prim (.lit (.i32 i))) s)), h⟩ =>
      .next μ (countNext ⟨f, h.pair_left⟩ n i ⟨s, h.pair_right.pair_right.pair_right⟩)
  | .prim .countTry, ⟨.pair f (.pair (.prim (.lit (.i32 n))) (.pair (.prim (.lit (.i32 i))) s)), h⟩ =>
      .next μ (countTryNext ⟨f, h.pair_left⟩ n i ⟨s, h.pair_right.pair_right.pair_right⟩)
  | .prim .boundedFix, ⟨.pair s (.pair (.prim (.lit (.i32 k))) a), h⟩ =>
      .next μ (boundedFixNext ⟨s, h.pair_left⟩ k ⟨a, h.pair_right.pair_right⟩)
  | .prim .iterate, ⟨.pair f s, h⟩ =>
      .next μ (iterNext ⟨f, h.pair_left⟩ ⟨s, h.pair_right⟩)
  | _, _ => .stuck .badPrimArg

/-! ### Handlers, operations and finalisers  `[spec §19]`

The capture steps of `Head` (`hret`, `hop`, `hunwind`, `uthen`, `ufin`, `ufinC`, `cfret`,
`cferr`, `cfcancel`, `cancel`, `creraise`, and §51's `cancelTo`), executable: a `perform`, `raise`
or `cancelTo` stops (`Step.op`), the stop passes outward through the frames that do not catch it,
and the first that does reduces. -/

/-- `e` is a value, decided. -/
def isValB : Expr → Bool
  | .unit | .lam _ | .loc _ | .prim _ => true
  | .pair a b => isValB a && isValB b
  | .inj₁ a | .inj₂ a => isValB a
  | .app (.prim .store) a => isValB a
  | _ => false

theorem isVal_of_isValB : ∀ e : Expr, isValB e = true → IsVal e
  | .unit, _ => .unit
  | .lam _, _ => .lam
  | .loc _, _ => .loc
  | .prim _, _ => .prim
  | .pair a b, h => by
      simp only [isValB, Bool.and_eq_true] at h
      exact .pair (isVal_of_isValB a h.1) (isVal_of_isValB b h.2)
  | .inj₁ a, h => .inj₁ (isVal_of_isValB a h)
  | .inj₂ a, h => .inj₂ (isVal_of_isValB a h)
  | .app (.prim .store) a, h => .storeV (isVal_of_isValB a h)
  | .var _, h | .seq _ _, h | .letpair _ _, h | .case _ _ _, h => by simp [isValB] at h
  | .app (.var _) _, h | .app .unit _, h | .app (.pair _ _) _, h | .app (.inj₁ _) _, h
  | .app (.inj₂ _) _, h | .app (.lam _) _, h | .app (.loc _) _, h | .app (.seq _ _) _, h
  | .app (.app _ _) _, h | .app (.letpair _ _) _, h | .app (.case _ _ _) _, h => by
      simp [isValB] at h
  | .app (.prim .alloc) _, h | .app (.prim .free) _, h | .app (.prim .load) _, h
  | .app (.prim (.host _)) _, h | .app (.prim (.lit _)) _, h | .app (.prim .tab) _, h
  | .app (.prim .idx) _, h | .app (.prim .split) _, h | .app (.prim .drop) _, h
  | .app (.prim .count) _, h | .app (.prim .countTry) _, h | .app (.prim .boundedFix) _, h
  | .app (.prim .iterate) _, h | .app (.prim .sliceCopy) _, h
  | .app (.prim .perform) _, h
  | .app (.prim .raise) _, h | .app (.prim .hnd) _, h | .app (.prim .ubind) _, h
  | .app (.prim .ccatch) _, h | .app (.prim .cfin) _, h
  | .app (.prim .cancelTo) _, h => by simp [isValB] at h

/-- The value of a term that is one. -/
def valOf? (e : Expr) : Option Val :=
  if h : isValB e = true then some ⟨e, isVal_of_isValB e h⟩ else none

/-- The `i`-th clause of a right-nested tuple of clauses, as `BoLo.clauseAt` but decided. -/
def clauseOf : Expr → Nat → Option Val
  | .pair c _, 0 => valOf? c
  | .pair _ r, i + 1 => clauseOf r i
  | _, _ => none

/-- The error of an `errVal`. -/
def errOf : Expr → Option (Option Val)
  | .inj₁ .unit => some none
  | .inj₂ e => (valOf? e).map some
  | _ => none

/-- What the frame `f [·]` makes of the stopped `K[perform p]` (`r = false`) or `K[raise p]`
(`r = true`): a step when it catches it, or the stop passed outward. -/
def catchOpPR (μ : Mem) (f : Expr) (r : Bool) (K : BoLo.Kont) (p : Val) : Step :=
  let pass := Step.op (if r then .raise else .perform) (.appR f K) p
  match f, p.1 with
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) (.pair qs (.pair hr hs))),
      .pair (.prim (.lit (.i32 n))) (.pair (.prim (.lit (.i32 i))) v) =>
    if n = m then
      match valOf? (.pair (.prim (.lit (.i32 m))) (.pair qs (.pair hr hs))), clauseOf hs i.toNat,
        valOf? v with
      | some H, some c, some w =>
        if r then .next μ (.app (.val c) (.val w))
        else .next μ (.app (.val c) (.pair (.val w) (BoLo.kappaAt (BoLo.capTag qs i.toNat) H K)))
      | _, _, _ => .stuck .badPrimArg
    else pass
  | .app (.prim .ubind) (.pair _ d), .pair (.prim (.lit (.i32 n))) _ =>
    if r then
      match valOf? d with
      | some D =>
        if n = 0 then .next μ (BoLo.cfinE p (.app (.val D) (.val .unit)))
        else .next μ (.seq (.app (.val D) (.val .unit)) (BoLo.raiseE (.val p)))
      | none => .stuck .badPrimArg
    else pass
  | .prim .ccatch, .pair (.prim (.lit (.i32 0))) (.pair _ err) =>
    if r then
      match errOf err with
      | some none => .next μ (.val .unit)
      | some (some E) => .next μ (BoLo.raiseE (.val E))
      | none => .stuck .badPrimArg
    else pass
  | .app (.prim .cfin) (.pair _ (.pair _ err)),
      .pair (.prim (.lit (.i32 m))) (.pair (.prim (.lit (.i32 j))) w) =>
    if r then
      match errOf err with
      | some e =>
        if m = 0 then
          match errOf w with
          | some e' => .next μ (BoLo.raiseE (.val (BoLo.cancelVal (e.or e'))))
          | none => .stuck .badPrimArg
        else
          match valOf? w with
          | some w' => .next μ (BoLo.raiseE (.val (BoLo.cancelVal (BoLo.errNext e m j w'))))
          | none => .stuck .badPrimArg
      | none => .stuck .badPrimArg
    else pass
  | _, _ => pass

/-- What the frame `f [·]` makes of the stopped `K[cancelTo (n, k)]`: `[cancel-to]` at a handler
of `n`, `ccatch (K†[raise (0, (0, none))]); k ()`; every other frame passes it outward.
`[spec §51]` -/
def catchCancelTo (μ : Mem) (f : Expr) (K : BoLo.Kont) (p : Val) : Step :=
  let pass := Step.op .cancelTo (.appR f K) p
  match f, p.1 with
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) _), .pair (.prim (.lit (.i32 n))) k =>
    if n = m then
      match valOf? k with
      | some kv =>
        .next μ (.seq (BoLo.ccatchE (K.dead.plug (BoLo.raiseE (.val (BoLo.cancelVal none)))))
          (.app (.val kv) (.val .unit)))
      | none => .stuck .badPrimArg
    else pass
  | _, _ => pass

/-- What the frame `f [·]` makes of the stopped operation `K[op p]`: a step when it catches it,
or the stop passed outward.  `[spec §19, §51]` -/
def catchOp (μ : Mem) (f : Expr) (r : OpKind) (K : BoLo.Kont) (p : Val) : Step :=
  match r with
  | .perform => catchOpPR μ f false K p
  | .raise => catchOpPR μ f true K p
  | .cancelTo => catchCancelTo μ f K p

/-- The frame's reduction when the term in it is a value: `[ret]`, `[then]`, `[cfin-ret]`, and
`perform`/`raise`/`cancelTo` stopping. -/
def effApp? (μ : Mem) (f : Expr) (v : Val) : Option Step :=
  match f with
  | .app (.prim .hnd) (.pair _ (.pair _ (.pair hr _))) =>
      (valOf? hr).map fun h => .next μ (.app (.val h) (.val v))
  | .app (.prim .ubind) (.pair nn _) => (valOf? nn).map fun N => .next μ (.app (.val N) (.val v))
  | .app (.prim .cfin) s => (valOf? s).map fun st => .next μ (BoLo.raiseE (.val st))
  | .prim .perform => some (.op .perform .hole v)
  | .prim .raise => some (.op .raise .hole v)
  | .prim .cancelTo => some (.op .cancelTo .hole v)
  | _ => none

/-- One step of call-by-value reduction.

    Evaluation order follows the evaluation contexts of the technical report
    (§3 Dynamics):

      K ::= [] | (K, e) | (v, K) | let (x,y) = K in e
          | case K {inj₁ x. e₁ | inj₂ y. e₂} | e K | K v

    Pairs are left-to-right (`(K,e)` before `(v,K)`); application is
    argument-first: the frame `e K` evaluates the argument, then `K v` the
    function.  It adds the frames `K; e` and `injᵢ K` (§12.42).

    A pair of values is the value pair, so `.value` is returned directly; the
    same holds of `injᵢ v` and of `store v`.

    `seq` fires at `()` and nowhere else, as `1↦` prints it. -/
def step (H : Host) (μ : Mem) : Expr → Step
  | .var _  => .stuck .unboundVar
  | .unit   => .value .unit
  | .lam b  => .value (.lam b)
  | .loc ℓ  => .value (.loc ℓ)
  | .prim p => .value (.prim p)

  | .pair e₁ e₂ =>
    match step H μ e₁ with
    | .value v₁    => match step H μ e₂ with
                      | .value v₂    => .value (.pair v₁ v₂)
                      | .next μ' e₂' => .next μ' (.pair e₁ e₂')
                      | .stuck r     => .stuck r
                      | .op r K p    => .op r (.pairR v₁ K) p
    | .next μ' e₁' => .next μ' (.pair e₁' e₂)
    | .stuck r     => .stuck r
    | .op r K p    => .op r (.pairL K e₂) p

  | .inj₁ e => match step H μ e with
    | .value v    => .value (.inj₁ v)
    | .next μ' e' => .next μ' (.inj₁ e')
    | .stuck r    => .stuck r
    | .op r K p   => .op r (.inj₁ K) p

  | .inj₂ e => match step H μ e with
    | .value v    => .value (.inj₂ v)
    | .next μ' e' => .next μ' (.inj₂ e')
    | .stuck r    => .stuck r
    | .op r K p   => .op r (.inj₂ K) p

  | .seq e₁ e₂ => match step H μ e₁ with
    | .value ⟨.unit, _⟩ => .next μ e₂
    | .value _          => .stuck .notAUnit
    | .next μ' e₁'      => .next μ' (.seq e₁' e₂)
    | .stuck r          => .stuck r
    | .op r K p         => .op r (.seq K e₂) p

  | .letpair e₁ e₂ => match step H μ e₁ with
    | .value ⟨.pair a b, h⟩ =>
        .next μ ((e₂.subst 0 (Val.shift 1 0 ⟨b, h.pair_right⟩)).subst 0 ⟨a, h.pair_left⟩)
    | .value _     => .stuck .notAPair
    | .next μ' e₁' => .next μ' (.letpair e₁' e₂)
    | .stuck r     => .stuck r
    | .op r K p    => .op r (.letpair K e₂) p

  | .case e e₁ e₂ => match step H μ e with
    | .value ⟨.inj₁ a, h⟩ => .next μ (e₁.subst 0 ⟨a, h.inj₁_inv⟩)
    | .value ⟨.inj₂ a, h⟩ => .next μ (e₂.subst 0 ⟨a, h.inj₂_inv⟩)
    | .value _            => .stuck .notASum
    | .next μ' e'         => .next μ' (.case e' e₁ e₂)
    | .stuck r            => .stuck r
    | .op r K p           => .op r (.case K e₁ e₂) p

  | .app f a => match step H μ a with
    | .value v    => match effApp? μ f v with
                     | some st => st
                     | none =>
                       match step H μ f with
                       | .value w    => match w.val with
                                        | .lam b      => .next μ (b.subst 0 v)
                                        | .prim p     => delta H μ (.prim p) v
                                        | .app f' a'  => delta H μ (.app f' a') v
                                        | _           => .stuck .notAFunction
                       | .next μ' f' => .next μ' (.app f' a)
                       | .stuck r    => .stuck r
                       | .op r K p   => .op r (.appL K v) p
    | .next μ' a' => .next μ' (.app f a')
    | .stuck r    => .stuck r
    | .op r K p   => catchOp μ f r K p

/-! ### `step`, executably

`step` at a value rebuilds the value, node by node, to answer `.value`. `stepFast` answers a
value with the term itself (`valOf?`), and steps every other term as `step` does;
`step_eq_stepFast` proves the two equal, so compiled code runs `stepFast` in `step`'s place
(`@[csimp]`). Every statement still reads `step`. -/

/-- `step` at a value answers the value. -/
theorem step_of_isVal (H : Host) (μ : Mem) : ∀ {e : Expr} (h : IsVal e),
    step H μ e = .value ⟨e, h⟩
  | _, .unit | _, .lam | _, .loc | _, .prim => rfl
  | _, .pair h₁ h₂ => by simp only [step, step_of_isVal H μ h₁, step_of_isVal H μ h₂]; rfl
  | _, .inj₁ h => by simp only [step, step_of_isVal H μ h]; rfl
  | _, .inj₂ h => by simp only [step, step_of_isVal H μ h]; rfl
  | _, .storeV h => by simp only [step, step_of_isVal H μ h, effApp?, delta]; rfl

/-- `step`, answering a value without rebuilding it. -/
def stepFast (H : Host) (μ : Mem) (e : Expr) : Step :=
  match valOf? e with
  | some v => .value v
  | none =>
  match e with
  | .var _  => .stuck .unboundVar
  | .unit   => .value .unit
  | .lam b  => .value (.lam b)
  | .loc ℓ  => .value (.loc ℓ)
  | .prim p => .value (.prim p)

  | .pair e₁ e₂ =>
    match stepFast H μ e₁ with
    | .value v₁    => match stepFast H μ e₂ with
                      | .value v₂    => .value (.pair v₁ v₂)
                      | .next μ' e₂' => .next μ' (.pair e₁ e₂')
                      | .stuck r     => .stuck r
                      | .op r K p    => .op r (.pairR v₁ K) p
    | .next μ' e₁' => .next μ' (.pair e₁' e₂)
    | .stuck r     => .stuck r
    | .op r K p    => .op r (.pairL K e₂) p

  | .inj₁ e => match stepFast H μ e with
    | .value v    => .value (.inj₁ v)
    | .next μ' e' => .next μ' (.inj₁ e')
    | .stuck r    => .stuck r
    | .op r K p   => .op r (.inj₁ K) p

  | .inj₂ e => match stepFast H μ e with
    | .value v    => .value (.inj₂ v)
    | .next μ' e' => .next μ' (.inj₂ e')
    | .stuck r    => .stuck r
    | .op r K p   => .op r (.inj₂ K) p

  | .seq e₁ e₂ => match stepFast H μ e₁ with
    | .value ⟨.unit, _⟩ => .next μ e₂
    | .value _          => .stuck .notAUnit
    | .next μ' e₁'      => .next μ' (.seq e₁' e₂)
    | .stuck r          => .stuck r
    | .op r K p         => .op r (.seq K e₂) p

  | .letpair e₁ e₂ => match stepFast H μ e₁ with
    | .value ⟨.pair a b, h⟩ =>
        .next μ ((e₂.subst 0 (Val.shift 1 0 ⟨b, h.pair_right⟩)).subst 0 ⟨a, h.pair_left⟩)
    | .value _     => .stuck .notAPair
    | .next μ' e₁' => .next μ' (.letpair e₁' e₂)
    | .stuck r     => .stuck r
    | .op r K p    => .op r (.letpair K e₂) p

  | .case e e₁ e₂ => match stepFast H μ e with
    | .value ⟨.inj₁ a, h⟩ => .next μ (e₁.subst 0 ⟨a, h.inj₁_inv⟩)
    | .value ⟨.inj₂ a, h⟩ => .next μ (e₂.subst 0 ⟨a, h.inj₂_inv⟩)
    | .value _            => .stuck .notASum
    | .next μ' e'         => .next μ' (.case e' e₁ e₂)
    | .stuck r            => .stuck r
    | .op r K p           => .op r (.case K e₁ e₂) p

  | .app f a => match stepFast H μ a with
    | .value v    => match effApp? μ f v with
                     | some st => st
                     | none =>
                       match stepFast H μ f with
                       | .value w    => match w.val with
                                        | .lam b      => .next μ (b.subst 0 v)
                                        | .prim p     => delta H μ (.prim p) v
                                        | .app f' a'  => delta H μ (.app f' a') v
                                        | _           => .stuck .notAFunction
                       | .next μ' f' => .next μ' (.app f' a)
                       | .stuck r    => .stuck r
                       | .op r K p   => .op r (.appL K v) p
    | .next μ' a' => .next μ' (.app f a')
    | .stuck r    => .stuck r
    | .op r K p   => catchOp μ f r K p

theorem stepFast_eq (H : Host) (μ : Mem) : ∀ e : Expr, stepFast H μ e = step H μ e := by
  intro e
  induction e with
  | var => simp [stepFast, step, valOf?, isValB]
  | unit | lam | loc | prim =>
    unfold stepFast; split
    · rename_i v hv
      simp only [valOf?] at hv; split at hv <;> simp at hv; subst hv; rfl
    · rfl
  | pair _ _ ih₁ ih₂ | seq _ _ ih₁ ih₂ | letpair _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ =>
    unfold stepFast; split
    · rename_i v hv
      simp only [valOf?] at hv; split at hv <;> simp at hv; subst hv
      exact (step_of_isVal H μ _).symm
    · simp only [step, ih₁, ih₂]
  | inj₁ _ ih | inj₂ _ ih =>
    unfold stepFast; split
    · rename_i v hv
      simp only [valOf?] at hv; split at hv <;> simp at hv; subst hv
      exact (step_of_isVal H μ _).symm
    · simp only [step, ih]
  | case _ _ _ ih₀ _ _ =>
    unfold stepFast; split
    · rename_i v hv
      simp only [valOf?] at hv; split at hv <;> simp at hv; subst hv
      exact (step_of_isVal H μ _).symm
    · simp only [step, ih₀]

@[csimp] theorem step_eq_stepFast : @step = @stepFast := by
  funext H μ e; exact (stepFast_eq H μ e).symm

/-- Outcome of a bounded run. Fuel keeps everything total. -/
inductive Outcome where
  | value   (v : Val) (leaked : Bool)
  | stuck   (r : Stuck)
  | timeout
  deriving Repr

def run (H : Host) : Nat → Mem → Expr → Outcome
  | 0,     _, _ => .timeout
  | n + 1, μ, e =>
    match step H μ e with
    | .value v    => .value v μ.leaked
    | .next μ' e' => run H n μ' e'
    | .stuck r    => .stuck r
    | .op _ _ _   => .stuck .unhandled

/-- A bounded run from the empty memory, at the host `H` (Wasm's by default, `[spec §8]`). -/
def eval (e : Expr) (H : Host := wasmHost) : Outcome := run H 1000 Mem.empty e

end BoCa

end
