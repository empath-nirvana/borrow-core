import EffModelRel.Obstruction

/-!
# EffModelRel — a `Mut` cell holding a rebased continuation (#249 step 2)

The cell lemma, in a semantic model small enough to see it whole. A **place** is a cell that a
computation creates, resumes in place and drops: it holds a **generator**, a suspended
computation that, when resumed, runs to its next element and leaves a new generator, its rest
(phase B's stream: a continuation captured at `yield`, with its `cancel` as the drop). The model
has resources (acquire, free) and places; it has no handlers, because a stored generator has
already handled its own yields.

- **Strata.** Places are stratified by **level**. A tree at level `L` may create, resume and drop
  only places of level `L`; a place of level `L + 1` holds a generator whose trees are at level
  `L` (`St`). So the contents of a place never touch a place of its own level, in particular not
  the place itself: **the cell's stratum excludes it**. Level is the lifetime stratum of BoLo's
  `Mut_α` cells, whose predicate is at a strictly later stratum. The domain and the run are
  defined by recursion on the level, then on the tree (`runK`); nothing is step-indexed.
- **The invariant at the cell's level** (`VSt`): a place of level `L + 1` holds a generator whose
  pull, run at level `L`, answers done or an element and a rest that again satisfies `VSt`, and
  whose drop disposes of what it owns. It is a least fixed point at each level, and refers only to
  level `L`.
- **The cell lemma** (`adequacy`, cases `pnext` and `pdrop`). *Resume*: the content is taken out
  (the place is busy), its pull runs at the level below, under fresh names (`acq` and `pnew` take
  the world's next name), and the rest is put back: it satisfies the invariant again because the
  invariant is a fixed point (re-rebasing is the generator's own type). *Drop*: the content is
  taken out and its drop runs to completion, freeing what it owns. A tree cannot resume a place
  whose content is running: its token is held by the frame that resumed it.
- **Safety** (`cell_safety`): a safe closed tree at any level runs without getting stuck, holds
  nothing at the end, and every resource and place still live is owned by the content of a
  live place.
- **Without strata** (`no_place_store`): if a tree could read the content of a place as a value
  of a type of trees, as phase B's denotation reads a cell, the type of trees would retract onto
  its own function space. No set does (Cantor), which is T15's obstruction (`no_negative_domain`)
  again. The world-run here avoids storing trees in trees; strata avoid running a content inside
  itself.
-/

namespace EffCell

/-! ## Tokens -/

inductive Tok where
  /-- An owned resource. -/
  | res (r : Nat)
  /-- A borrow of a resource: it may be used, not freed. -/
  | use (r : Nat)
  /-- An owned resource that is lent: it may be neither used nor freed until it is reclaimed. -/
  | rsv (r : Nat)
  /-- A place of level `L` whose content gives back the borrows of `B` when dropped. -/
  | pl (L c : Nat) (B : List Nat)
deriving DecidableEq

def Own : Type := Tok → Nat

namespace Own
instance : Add Own := ⟨fun a b t => a t + b t⟩
instance : OfNat Own 0 := ⟨fun _ => 0⟩
def one (t : Tok) : Own := fun t' => if t' = t then 1 else 0

@[simp] theorem add_apply (a b : Own) (t : Tok) : (a + b) t = a t + b t := rfl
@[simp] theorem zero_apply (t : Tok) : (0 : Own) t = 0 := rfl
@[simp] theorem one_apply (t t' : Tok) : one t t' = if t' = t then 1 else 0 := rfl

theorem ext {a b : Own} (h : ∀ t, a t = b t) : a = b := funext h
theorem add_comm (a b : Own) : a + b = b + a := ext fun _ => Nat.add_comm _ _
theorem add_assoc (a b c : Own) : a + b + c = a + (b + c) := ext fun _ => Nat.add_assoc _ _ _
@[simp] theorem zero_add (a : Own) : 0 + a = a := ext fun _ => Nat.zero_add _
@[simp] theorem add_zero (a : Own) : a + 0 = a := ext fun _ => Nat.add_zero _
theorem add_right_comm (a b c : Own) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]
end Own

/-- The borrows a list of resources names. -/
def useOf : List Nat → Own
  | [] => 0
  | r :: B => useOf B + Own.one (.use r)

theorem useOf_pl (B : List Nat) (L c : Nat) (B' : List Nat) : useOf B (.pl L c B') = 0 := by
  induction B with
  | nil => rfl
  | cons r B ih => simp [useOf, ih]

theorem useOf_res (B : List Nat) (r : Nat) : useOf B (.res r) = 0 := by
  induction B with
  | nil => rfl
  | cons r' B ih => simp [useOf, ih]

theorem useOf_rsv (B : List Nat) (r : Nat) : useOf B (.rsv r) = 0 := by
  induction B with
  | nil => rfl
  | cons r' B ih => simp [useOf, ih]

/-! ## Trees, generators, levels -/

inductive Ev where
  | out (n : Int)
  | acq (ℓ : Nat)
  | free (ℓ : Nat)
  | touch (ℓ : Nat)
  | mk
  | fin
deriving DecidableEq, Repr

/-- Trees over the contents `St` of the places they may touch. -/
inductive KF (St : Type) (X : Type) : Type where
  | ret (x : X)
  | out (n : Int) (k : KF St X)
  /-- Acquire a fresh resource with label `ℓ`. -/
  | acq (ℓ : Nat) (k : Nat → KF St X)
  | free (r : Nat) (k : KF St X)
  /-- Use a resource: it must be live. -/
  | touch (r : Nat) (k : KF St X)
  /-- Lend a resource for a while: the owner keeps it reserved, a borrow may use it. -/
  | lend (r : Nat) (k : KF St X)
  /-- End the loan: the reservation and the borrow make the resource owned again. -/
  | reclaim (r : Nat) (k : KF St X)
  /-- A fresh place holding `v`, which gives back the borrows of `B` when dropped (a type
  annotation: the run ignores it). -/
  | pnew (B : List Nat) (v : St) (k : Nat → KF St X)
  /-- Resume the generator in place `c`: done, or its next element. -/
  | pnext (c : Nat) (k : Option Int → KF St X)
  /-- Drop the generator in place `c` and free the place. -/
  | pdrop (c : Nat) (k : KF St X)

/-- A generator over trees that touch places holding `St`: pull it, or drop it. -/
inductive Gen (St : Type) : Type where
  | mk (pull : KF St (Option (Int × Gen St))) (drop : KF St Unit)

/-- The contents of the places a tree at level `L` touches: generators whose trees are at level
`L - 1`. Nothing is stored at level `0`. -/
@[reducible] def St : Nat → Type
  | 0 => Empty
  | L + 1 => Gen (St L)

/-- The generator that is done. -/
def Gen.done {St' : Type} : Gen St' := .mk (.ret none) (.ret ())

/-! ## The world and the run -/

inductive PSt where
  | free
  | live (L : Nat) (B : List Nat) (v : St L)
  /-- Its content has been taken out and is running. -/
  | busy (L : Nat) (B : List Nat)

/-- The world. `lent` and the places' return sets are ghost state: the run never reads them. -/
structure Wd where
  next : Nat
  res : Nat → Option Nat
  lent : Nat → Bool
  pl : Nat → PSt
  trace : List Ev

def upd {α : Type} (f : Nat → α) (a : Nat) (v : α) : Nat → α := fun x => if x = a then v else f x

@[simp] theorem upd_same {α : Type} (f : Nat → α) (a : Nat) (v : α) : upd f a v a = v := by simp [upd]
theorem upd_ne {α : Type} (f : Nat → α) {a x : Nat} (v : α) (h : x ≠ a) : upd f a v x = f x := by
  simp [upd, h]

namespace Wd
def init : Wd := ⟨0, fun _ => none, fun _ => false, fun _ => .free, []⟩
def emit (w : Wd) (e : Ev) : Wd := { w with trace := e :: w.trace }
def acquire (w : Wd) (ℓ : Nat) : Wd :=
  { w with
    next := w.next + 1
    res := upd w.res w.next (some ℓ)
    lent := upd w.lent w.next false
    trace := .acq ℓ :: w.trace }
def release (w : Wd) (r ℓ : Nat) : Wd :=
  { w with res := upd w.res r none, trace := .free ℓ :: w.trace }
def place (w : Wd) (L : Nat) (B : List Nat) (v : St L) : Wd :=
  { w with next := w.next + 1, pl := upd w.pl w.next (.live L B v), trace := .mk :: w.trace }
def setLent (w : Wd) (r : Nat) (b : Bool) : Wd := { w with lent := upd w.lent r b }
def setPl (w : Wd) (c : Nat) (p : PSt) : Wd := { w with pl := upd w.pl c p }
end Wd

/-- The run of a tree at level `L + 1`, given the run at level `L` for the contents of its
places. Structural on the tree. -/
def runS (L : Nat) (lower : ∀ {Y : Type}, KF (St L) Y → Wd → Option (Y × Wd)) {X : Type} :
    KF (Gen (St L)) X → Wd → Option (X × Wd)
  | .ret x, w => some (x, w)
  | .out n k, w => runS L lower k (w.emit (.out n))
  | .acq ℓ k, w => runS L lower (k w.next) (w.acquire ℓ)
  | .free r k, w =>
      match w.res r with
      | some ℓ => runS L lower k (w.release r ℓ)
      | none => none
  | .touch r k, w =>
      match w.res r with
      | some ℓ => runS L lower k (w.emit (.touch ℓ))
      | none => none
  | .lend r k, w => runS L lower k (w.setLent r true)
  | .reclaim r k, w => runS L lower k (w.setLent r false)
  | .pnew B v k, w => runS L lower (k w.next) (w.place (L + 1) B v)
  | .pnext c k, w =>
      match w.pl c with
      | .live L' B v =>
          if h : L' = L + 1 then
            match (cast (congrArg St h) v : Gen (St L)) with
            | .mk p _ =>
                match lower p (w.setPl c (.busy (L + 1) B)) with
                | some (none, w') => runS L lower (k none) (w'.setPl c (.live (L + 1) B Gen.done))
                | some (some (n, g), w') =>
                    runS L lower (k (some n)) (w'.setPl c (.live (L + 1) B g))
                | none => none
          else none
      | _ => none
  | .pdrop c k, w =>
      match w.pl c with
      | .live L' B v =>
          if h : L' = L + 1 then
            match (cast (congrArg St h) v : Gen (St L)) with
            | .mk _ d =>
                match lower d (w.setPl c (.busy (L + 1) B)) with
                | some ((), w') => runS L lower k ((w'.setPl c .free).emit .fin)
                | none => none
          else none
      | _ => none

/-- The run at level `0`: no place holds anything there. -/
def run0 {X : Type} : KF (St 0) X → Wd → Option (X × Wd)
  | .ret x, w => some (x, w)
  | .out n k, w => run0 k (w.emit (.out n))
  | .acq ℓ k, w => run0 (k w.next) (w.acquire ℓ)
  | .free r k, w =>
      match w.res r with
      | some ℓ => run0 k (w.release r ℓ)
      | none => none
  | .touch r k, w =>
      match w.res r with
      | some ℓ => run0 k (w.emit (.touch ℓ))
      | none => none
  | .lend r k, w => run0 k (w.setLent r true)
  | .reclaim r k, w => run0 k (w.setLent r false)
  | .pnew _ v _, _ => (v : Empty).elim
  | .pnext _ _, _ => none
  | .pdrop _ _, _ => none

/-- **The run**, by recursion on the level. -/
def runK : (L : Nat) → {X : Type} → KF (St L) X → Wd → Option (X × Wd)
  | 0, _, t, w => run0 t w
  | L + 1, _, t, w => runS L (fun t' w' => runK L t' w') t w

/-! ## Safe trees, and the invariant of a place -/

/-- Safe trees at level `lvl`, whose new places hold contents satisfying `V`, given what they
give back. -/
inductive TS {St' : Type} (V : List Nat → Own → St' → Prop) (lvl : Nat) {X : Type}
    (P : Own → X → Prop) : Own → KF St' X → Prop where
  | ret {O : Own} {x : X} : P O x → TS V lvl P O (.ret x)
  | out {O : Own} {n : Int} {k : KF St' X} : TS V lvl P O k → TS V lvl P O (.out n k)
  | acq {O : Own} {ℓ : Nat} {k : Nat → KF St' X} :
      (∀ r, TS V lvl P (O + Own.one (.res r)) (k r)) → TS V lvl P O (.acq ℓ k)
  | free {O : Own} {r : Nat} {k : KF St' X} :
      TS V lvl P O k → TS V lvl P (O + Own.one (.res r)) (.free r k)
  | touch {O : Own} {r : Nat} {k : KF St' X} :
      O (.res r) ≠ 0 ∨ O (.use r) ≠ 0 → TS V lvl P O k → TS V lvl P O (.touch r k)
  | lend {O : Own} {r : Nat} {k : KF St' X} :
      TS V lvl P (O + Own.one (.rsv r) + Own.one (.use r)) k →
      TS V lvl P (O + Own.one (.res r)) (.lend r k)
  | reclaim {O : Own} {r : Nat} {k : KF St' X} :
      TS V lvl P (O + Own.one (.res r)) k →
      TS V lvl P (O + Own.one (.rsv r) + Own.one (.use r)) (.reclaim r k)
  | pnew {O Ov : Own} {B : List Nat} {v : St'} {k : Nat → KF St' X} :
      V B Ov v → (∀ c, TS V lvl P (O + Own.one (.pl lvl c B)) (k c)) →
      TS V lvl P (O + Ov) (.pnew B v k)
  | pnext {O : Own} {c : Nat} {B : List Nat} {k : Option Int → KF St' X} :
      O (.pl lvl c B) ≠ 0 → (∀ a, TS V lvl P O (k a)) → TS V lvl P O (.pnext c k)
  | pdrop {O : Own} {c : Nat} {B : List Nat} {k : KF St' X} :
      TS V lvl P (O + useOf B) k → TS V lvl P (O + Own.one (.pl lvl c B)) (.pdrop c k)

/-- A generator's pull answers done, owning just the borrows it gives back, or an element and a
rest in `Q`. -/
def GenLeaf {St' : Type} (B : List Nat) (Q : Own → Gen St' → Prop) :
    Own → Option (Int × Gen St') → Prop
  | O, none => O = useOf B
  | O, some (_, g) => Q O g

/-- The generators whose pull and drop are safe, giving back the borrows of `B`, as the least
predicate closed under one unfolding. -/
def GenS {St' : Type} (V : List Nat → Own → St' → Prop) (lvl : Nat) (B : List Nat) (O : Own)
    (g : Gen St') : Prop :=
  ∀ Q : Own → Gen St' → Prop,
    (∀ O p d, TS V lvl (GenLeaf B Q) O p → TS V lvl (fun O' (_ : Unit) => O' = useOf B) O d →
      Q O (.mk p d)) → Q O g

/-- **The invariant of a place at level `L`**: what its content may hold, given what it gives
back when dropped. -/
def VSt : (L : Nat) → List Nat → Own → St L → Prop
  | 0, _, _, v => (v : Empty).elim
  | L + 1, B, O, g => GenS (VSt L) L B O g

theorem TS.mapP {St' : Type} {V : List Nat → Own → St' → Prop} {lvl : Nat} {X : Type}
    {P P' : Own → X → Prop} {O : Own} {t : KF St' X} (h : TS V lvl P O t)
    (hP : ∀ O x, P O x → P' O x) : TS V lvl P' O t := by
  induction h with
  | ret hx => exact .ret (hP _ _ hx)
  | out _ ih => exact .out ih
  | acq _ ih => exact .acq ih
  | free _ ih => exact .free ih
  | touch hu _ ih => exact .touch hu ih
  | lend _ ih => exact .lend ih
  | reclaim _ ih => exact .reclaim ih
  | pnew hv _ ih => exact .pnew hv ih
  | pnext hc _ ih => exact .pnext hc ih
  | pdrop _ ih => exact .pdrop ih

theorem GenLeaf.map {St' : Type} {B : List Nat} {Q Q' : Own → Gen St' → Prop}
    (h : ∀ O g, Q O g → Q' O g) : ∀ O x, GenLeaf B Q O x → GenLeaf B Q' O x
  | _, none, hx => hx
  | _, some (_, _), hx => h _ _ hx

theorem GenS.intro {St' : Type} {V : List Nat → Own → St' → Prop} {lvl : Nat} {B : List Nat}
    {O : Own} {p d} (hp : TS V lvl (GenLeaf B (GenS V lvl B)) O p)
    (hd : TS V lvl (fun O' (_ : Unit) => O' = useOf B) O d) : GenS V lvl B O (.mk p d) :=
  fun Q hQ => hQ O p d (hp.mapP (GenLeaf.map (fun _ _ hs => hs Q hQ))) hd

/-- The cell's invariant unfolds: a safe pull whose rest is again safe, and a safe drop. -/
theorem GenS.unf {St' : Type} {V : List Nat → Own → St' → Prop} {lvl : Nat} {B : List Nat}
    {O : Own} {p d} (h : GenS V lvl B O (.mk p d)) :
    TS V lvl (GenLeaf B (GenS V lvl B)) O p ∧ TS V lvl (fun O' (_ : Unit) => O' = useOf B) O d := by
  have := h (fun O g => match g with
      | .mk p d => TS V lvl (GenLeaf B (GenS V lvl B)) O p ∧
          TS V lvl (fun O' (_ : Unit) => O' = useOf B) O d)
    (fun O p d hp hd => ⟨hp.mapP (GenLeaf.map (fun O g hg => by
      cases g with | mk p' d' => exact GenS.intro hg.1 hg.2)), hd⟩)
  exact this

theorem GenS.done {St' : Type} {V : List Nat → Own → St' → Prop} {lvl : Nat} {B : List Nat} :
    GenS V lvl B (useOf B) (Gen.done (St' := St')) :=
  GenS.intro (.ret rfl) (.ret rfl)

/-! ## The world invariant -/

/-- The tokens the contents of the places below `n` own. -/
def tot (Ov : Nat → Own) : Nat → Own
  | 0 => 0
  | n + 1 => tot Ov n + Ov n

/-- The place is live or busy at level `L`, giving back `B`. -/
def PSt.at (L : Nat) (B : List Nat) : PSt → Bool
  | .live L' B' _ => decide (L' = L) && decide (B' = B)
  | .busy L' B' => decide (L' = L) && decide (B' = B)
  | .free => false

/-- What the content of a place owns. -/
def PlInv : PSt → Own → Prop
  | .live L B v, O => VSt L B O v
  | _, O => O = 0

/-- The world's live resources and places, one token each: a live resource is owned, or lent
(reserved, and borrowed). -/
def phys (w : Wd) : Own := fun t =>
  match t with
  | .res r => ((w.res r).isSome && !(w.lent r)).toNat
  | .use r => ((w.res r).isSome && w.lent r).toNat
  | .rsv r => ((w.res r).isSome && w.lent r).toNat
  | .pl L c B => ((w.pl c).at L B).toNat

/-- **The world invariant**, for a run holding `O` inside frames holding `F`, with `Ov` what each
place's content owns. Every live resource and place has exactly one token, held by the run, a
frame or a content (`acct`); a busy place's token is held by a frame, the one running its
content. -/
structure Inv (O F : Own) (Ov : Nat → Own) (w : Wd) : Prop where
  cont : ∀ c, PlInv (w.pl c) (Ov c)
  acct : O + F + tot Ov w.next = phys w
  fresh : ∀ n, w.next ≤ n → w.res n = none ∧ w.pl n = .free
  busy : ∀ L B c, w.pl c = .busy L B → F (.pl L c B) ≠ 0
  nb0 : ∀ c B, w.pl c ≠ .busy 0 B

/-- What a run leaves alone: the places a frame holds, and no place newly busy. -/
def Fr (F : Own) (w : Wd) (Ov : Nat → Own) (w' : Wd) (Ov' : Nat → Own) : Prop :=
  (∀ L c B, F (.pl L c B) ≠ 0 → w'.pl c = w.pl c ∧ Ov' c = Ov c) ∧
  (∀ L B c, w'.pl c = .busy L B → w.pl c = .busy L B) ∧ w.next ≤ w'.next

theorem Fr.refl (F : Own) (w : Wd) (Ov : Nat → Own) : Fr F w Ov w Ov :=
  ⟨fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ h => h, Nat.le_refl _⟩

theorem Fr.trans {F : Own} {w₁ w₂ w₃ : Wd} {O₁ O₂ O₃ : Nat → Own} (h₁ : Fr F w₁ O₁ w₂ O₂)
    (h₂ : Fr F w₂ O₂ w₃ O₃) : Fr F w₁ O₁ w₃ O₃ :=
  ⟨fun L c B hc => ⟨((h₂.1 L c B hc).1).trans (h₁.1 L c B hc).1,
    ((h₂.1 L c B hc).2).trans (h₁.1 L c B hc).2⟩,
   fun L B c hb => h₁.2.1 L B c (h₂.2.1 L B c hb), Nat.le_trans h₁.2.2 h₂.2.2⟩

/-- A step that touches no place. -/
theorem Fr.noPl {F : Own} {w w' : Wd} {Ov : Nat → Own} (hp : w'.pl = w.pl) (hn : w.next ≤ w'.next) :
    Fr F w Ov w' Ov :=
  ⟨fun _ _ _ _ => ⟨by rw [hp], rfl⟩, fun _ _ _ hb => by rw [hp] at hb; exact hb, hn⟩

/-- A run's result: its answer and tokens satisfy `P`, the invariant holds, and the frames'
places are as they were. -/
def Post {X : Type} (P : Own → X → Prop) (F : Own) (w : Wd) (Ov : Nat → Own) (x : X) (w' : Wd) :
    Prop :=
  ∃ O' Ov', P O' x ∧ Inv O' F Ov' w' ∧ Fr F w Ov w' Ov'

theorem Post.pre {X : Type} {P : Own → X → Prop} {F : Own} {w w₁ w' : Wd} {Ov Ov₁ : Nat → Own}
    {x : X} (h₁ : Fr F w Ov w₁ Ov₁) (h : Post P F w₁ Ov₁ x w') : Post P F w Ov x w' :=
  let ⟨O', Ov', hP, hI, hF⟩ := h; ⟨O', Ov', hP, hI, h₁.trans hF⟩

/-! ### Sums -/

theorem tot_ext {Ov Ov' : Nat → Own} : ∀ n, (∀ c, c < n → Ov c = Ov' c) → tot Ov n = tot Ov' n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [tot]; rw [tot_ext n (fun c hc => h c (by omega)), h n (by omega)]

theorem tot_upd (Ov : Nat → Own) (c : Nat) (X : Own) :
    ∀ n, c < n → tot (upd Ov c X) n + Ov c = tot Ov n + X
  | 0, h => absurd h (by omega)
  | n + 1, h => by
      simp only [tot]
      by_cases hc : c = n
      · subst hc
        rw [tot_ext c (fun c' hc' => upd_ne _ _ (by omega)), upd_same]
        rw [Own.add_right_comm]
      · rw [upd_ne _ _ (Ne.symm hc), Own.add_right_comm, tot_upd Ov c X n (by omega),
          Own.add_right_comm]

theorem tot_upd_ge (Ov : Nat → Own) {c : Nat} (X : Own) {n : Nat} (h : n ≤ c) :
    tot (upd Ov c X) n = tot Ov n :=
  tot_ext n (fun c' hc' => upd_ne _ _ (by omega))

theorem Own.add_left_cancel {a b c : Own} (h : c + a = c + b) : a = b :=
  Own.ext fun t => by have := congrFun h t; simp at this; omega

theorem Own.add_right_cancel {a b c : Own} (h : a + c = b + c) : a = b :=
  Own.ext fun t => by have := congrFun h t; simp at this; omega

/-- An equation of tokens, checked token by token. -/
macro "own_eq" : tactic =>
  `(tactic| exact Own.ext (fun t => by simp only [Own.add_apply, Own.zero_apply]; omega))

/-! ### The world's steps -/

theorem phys_emit (w : Wd) (e : Ev) : phys (w.emit e) = phys w := rfl

theorem phys_acquire {w : Wd} (hf : w.res w.next = none) (ℓ : Nat) :
    phys (w.acquire ℓ) = phys w + Own.one (.res w.next) := by
  funext t; cases t with
  | res r =>
      show (((upd w.res w.next (some ℓ)) r).isSome && !(upd w.lent w.next false r)).toNat = _
      by_cases hr : r = w.next
      · subst hr; simp [phys, hf]
      · simp [upd, hr, phys]
  | use r =>
      show (((upd w.res w.next (some ℓ)) r).isSome && (upd w.lent w.next false r)).toNat = _
      by_cases hr : r = w.next
      · subst hr; simp [phys, hf]
      · simp [upd, hr, phys]
  | rsv r =>
      show (((upd w.res w.next (some ℓ)) r).isSome && (upd w.lent w.next false r)).toNat = _
      by_cases hr : r = w.next
      · subst hr; simp [phys, hf]
      · simp [upd, hr, phys]
  | pl L c B => simp [phys, Wd.acquire]

theorem phys_release {w : Wd} {r ℓ : Nat} (he : w.res r = some ℓ) (hl : w.lent r = false) :
    phys (w.release r ℓ) + Own.one (.res r) = phys w := by
  funext t; cases t with
  | res r' =>
      show ((upd w.res r none r').isSome && !(w.lent r')).toNat + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | use r' =>
      show ((upd w.res r none r').isSome && (w.lent r')).toNat + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | rsv r' =>
      show ((upd w.res r none r').isSome && (w.lent r')).toNat + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | pl L c B => simp [phys, Wd.release]

theorem phys_lend {w : Wd} {r ℓ : Nat} (he : w.res r = some ℓ) (hl : w.lent r = false) :
    phys (w.setLent r true) + Own.one (.res r) =
      phys w + Own.one (.rsv r) + Own.one (.use r) := by
  funext t; cases t with
  | res r' =>
      show ((w.res r').isSome && !(upd w.lent r true r')).toNat + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | use r' =>
      show ((w.res r').isSome && (upd w.lent r true r')).toNat + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | rsv r' =>
      show ((w.res r').isSome && (upd w.lent r true r')).toNat + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | pl L c B => simp [phys, Wd.setLent]

theorem phys_reclaim {w : Wd} {r ℓ : Nat} (he : w.res r = some ℓ) (hl : w.lent r = true) :
    phys (w.setLent r false) + Own.one (.rsv r) + Own.one (.use r) =
      phys w + Own.one (.res r) := by
  funext t; cases t with
  | res r' =>
      show ((w.res r').isSome && !(upd w.lent r false r')).toNat + _ + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | use r' =>
      show ((w.res r').isSome && (upd w.lent r false r')).toNat + _ + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | rsv r' =>
      show ((w.res r').isSome && (upd w.lent r false r')).toNat + _ + _ = _
      by_cases hr : r' = r
      · subst hr; simp [phys, he, hl]
      · simp [upd, hr, phys]
  | pl L c B => simp [phys, Wd.setLent]

theorem phys_place {w : Wd} (hf : w.pl w.next = .free) (L : Nat) (B : List Nat) (v : St L) :
    phys (w.place L B v) = phys w + Own.one (.pl L w.next B) := by
  funext t; cases t with
  | res r => simp [phys, Wd.place]
  | use r => simp [phys, Wd.place]
  | rsv r => simp [phys, Wd.place]
  | pl L' c B' =>
      show ((upd w.pl w.next (.live L B v) c).at L' B').toNat = _
      by_cases hc : c = w.next
      · subst hc
        simp only [upd_same, phys, hf, PSt.at, Own.add_apply, Own.one_apply]
        by_cases hL : L' = L
        · subst hL
          by_cases hB : B' = B
          · subst hB; simp
          · simp [hB, Ne.symm hB]
        · simp [hL, Ne.symm hL]
      · simp [upd, hc, phys]

/-- Changing a place's state without changing its level or return set leaves the accounting
alone. -/
theorem phys_setPl {w : Wd} {c : Nat} {p : PSt} (h : ∀ L B, p.at L B = (w.pl c).at L B) :
    phys (w.setPl c p) = phys w := by
  funext t; cases t with
  | res r => rfl
  | use r => rfl
  | rsv r => rfl
  | pl L c' B =>
      show ((upd w.pl c p c').at L B).toNat = ((w.pl c').at L B).toNat
      by_cases hc : c' = c
      · subst hc; rw [upd_same, h L B]
      · rw [upd_ne _ _ hc]

theorem phys_setPl_free {w : Wd} {c L : Nat} {B : List Nat} (h : w.pl c = .busy L B) :
    phys (w.setPl c .free) + Own.one (.pl L c B) = phys w := by
  funext t; cases t with
  | res r => simp [phys, Wd.setPl]
  | use r => simp [phys, Wd.setPl]
  | rsv r => simp [phys, Wd.setPl]
  | pl L' c' B' =>
      show ((upd w.pl c .free c').at L' B').toNat + (if Tok.pl L' c' B' = Tok.pl L c B then 1 else 0) =
        ((w.pl c').at L' B').toNat
      by_cases hc : c' = c
      · subst hc; rw [upd_same, h]
        by_cases hL : L' = L
        · subst hL
          by_cases hB : B' = B
          · subst hB; simp [PSt.at]
          · simp [PSt.at, hB, Ne.symm hB]
        · simp [PSt.at, hL, Ne.symm hL]
      · rw [upd_ne _ _ hc]; simp [hc]

/-! ### Facts about the invariant -/

theorem Inv.ov_free {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {c : Nat}
    (hc : ∀ L B v, w.pl c ≠ .live L B v) : Ov c = 0 := by
  have := h.cont c
  generalize hp : w.pl c = p at this hc
  cases p with
  | live L B v => exact absurd rfl (hc L B v)
  | busy _ _ => exact this
  | free => exact this

theorem Inv.lt_next {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {c : Nat}
    (hc : w.pl c ≠ .free) : c < w.next :=
  Nat.lt_of_not_le (fun hn => hc (h.fresh c hn).2)

/-- A token is held by at most one owner. -/
theorem Inv.le_one {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) (t : Tok) :
    O t + F t + tot Ov w.next t ≤ 1 := by
  have := congrFun h.acct t
  simp only [Own.add_apply] at this
  rw [this]; cases t <;> simp only [phys] <;> exact Bool.toNat_le _

theorem Inv.at_of {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {L c : Nat}
    {B : List Nat} (hO : O (.pl L c B) ≠ 0) : (w.pl c).at L B = true := by
  have := congrFun h.acct (.pl L c B)
  simp only [Own.add_apply, phys] at this
  cases hb : (w.pl c).at L B
  · rw [hb] at this; simp at this; omega
  · rfl

/-- A token the run holds is held by no frame. -/
theorem Inv.not_frame {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {t : Tok}
    (hO : O t ≠ 0) : F t = 0 := by
  have := h.le_one t; omega

theorem Inv.emit {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) (e : Ev) :
    Inv O F Ov (w.emit e) :=
  ⟨h.cont, h.acct, h.fresh, h.busy, h.nb0⟩

theorem Inv.acquire {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) (ℓ : Nat) :
    Inv (O + Own.one (.res w.next)) F Ov (w.acquire ℓ) ∧ Fr F w Ov (w.acquire ℓ) Ov := by
  have hf := h.fresh w.next (Nat.le_refl _)
  have hOv : Ov w.next = 0 := h.ov_free (fun L B v e => by rw [hf.2] at e; cases e)
  refine ⟨⟨h.cont, ?_, fun n hn => ?_, h.busy, h.nb0⟩, Fr.noPl rfl (by simp [Wd.acquire])⟩
  · rw [phys_acquire hf.1, ← h.acct]
    show O + Own.one (.res w.next) + F + (tot Ov w.next + Ov w.next) = _
    rw [hOv]
    own_eq
  · simp only [Wd.acquire] at hn ⊢
    have := h.fresh n (by omega)
    exact ⟨by rw [upd_ne _ _ (by omega)]; exact this.1, this.2⟩

/-- An owned token for `r` means `r` is live and not lent. -/
theorem Inv.res_live {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {r : Nat}
    (hO : O (.res r) ≠ 0) : ∃ ℓ, w.res r = some ℓ ∧ w.lent r = false := by
  have := congrFun h.acct (.res r)
  simp only [Own.add_apply, phys] at this
  cases e : w.res r with
  | none => rw [e] at this; simp at this; omega
  | some ℓ =>
      refine ⟨ℓ, rfl, ?_⟩
      cases hl : w.lent r
      · rfl
      · rw [e, hl] at this; simp at this; omega

/-- A borrow of `r` means `r` is live and lent. -/
theorem Inv.use_live {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {r : Nat}
    (hO : O (.use r) ≠ 0) : ∃ ℓ, w.res r = some ℓ ∧ w.lent r = true := by
  have := congrFun h.acct (.use r)
  simp only [Own.add_apply, phys] at this
  cases e : w.res r with
  | none => rw [e] at this; simp at this; omega
  | some ℓ =>
      refine ⟨ℓ, rfl, ?_⟩
      cases hl : w.lent r
      · rw [e, hl] at this; simp at this; omega
      · rfl

theorem Inv.release {O F : Own} {Ov : Nat → Own} {w : Wd} {r : Nat}
    (h : Inv (O + Own.one (.res r)) F Ov w) :
    ∃ ℓ, w.res r = some ℓ ∧ Inv O F Ov (w.release r ℓ) ∧ Fr F w Ov (w.release r ℓ) Ov := by
  obtain ⟨ℓ, e, hl⟩ := h.res_live (r := r) (by simp)
  have hrn : r < w.next := Nat.lt_of_not_le (fun hn => by rw [(h.fresh r hn).1] at e; cases e)
  refine ⟨ℓ, e, ⟨h.cont, ?_, fun n hn => ?_, h.busy, h.nb0⟩, Fr.noPl rfl (Nat.le_refl _)⟩
  · apply Own.add_right_cancel (c := Own.one (.res r))
    rw [phys_release e hl, ← h.acct]
    show O + F + tot Ov w.next + Own.one (.res r) = _
    own_eq
  · simp only [Wd.release] at hn ⊢
    have := h.fresh n hn
    exact ⟨by rw [upd_ne _ _ (by omega)]; exact this.1, this.2⟩

theorem Inv.lend {O F : Own} {Ov : Nat → Own} {w : Wd} {r : Nat}
    (h : Inv (O + Own.one (.res r)) F Ov w) :
    Inv (O + Own.one (.rsv r) + Own.one (.use r)) F Ov (w.setLent r true) ∧
      Fr F w Ov (w.setLent r true) Ov := by
  obtain ⟨ℓ, e, hl⟩ := h.res_live (r := r) (by simp)
  refine ⟨⟨h.cont, ?_, h.fresh, h.busy, h.nb0⟩, Fr.noPl rfl (Nat.le_refl _)⟩
  apply Own.add_right_cancel (c := Own.one (.res r))
  rw [phys_lend e hl, ← h.acct]
  show O + Own.one (.rsv r) + Own.one (.use r) + F + tot Ov w.next + Own.one (.res r) = _
  own_eq

theorem Inv.reclaim {O F : Own} {Ov : Nat → Own} {w : Wd} {r : Nat}
    (h : Inv (O + Own.one (.rsv r) + Own.one (.use r)) F Ov w) :
    Inv (O + Own.one (.res r)) F Ov (w.setLent r false) ∧ Fr F w Ov (w.setLent r false) Ov := by
  obtain ⟨ℓ, e, hl⟩ := h.use_live (r := r) (by simp)
  refine ⟨⟨h.cont, ?_, h.fresh, h.busy, h.nb0⟩, Fr.noPl rfl (Nat.le_refl _)⟩
  apply Own.add_right_cancel (c := Own.one (.rsv r) + Own.one (.use r))
  have := phys_reclaim e hl
  rw [Own.add_assoc] at this
  rw [this, ← h.acct]
  show O + Own.one (.res r) + F + tot Ov w.next + (Own.one (.rsv r) + Own.one (.use r)) = _
  own_eq

theorem Inv.place {O Ov₀ F : Own} {Ov : Nat → Own} {w : Wd} {L : Nat} {B : List Nat} {v : St L}
    (h : Inv (O + Ov₀) F Ov w) (hv : VSt L B Ov₀ v) :
    Inv (O + Own.one (.pl L w.next B)) F (upd Ov w.next Ov₀) (w.place L B v) ∧
      Fr F w Ov (w.place L B v) (upd Ov w.next Ov₀) := by
  have hf := h.fresh w.next (Nat.le_refl _)
  have hOv : Ov w.next = 0 := h.ov_free (fun L B v e => by rw [hf.2] at e; cases e)
  have htot : tot (upd Ov w.next Ov₀) (w.next + 1) = tot Ov w.next + Ov₀ := by
    simp only [tot]; rw [upd_same, tot_upd_ge _ _ (Nat.le_refl _)]
  have hF0 : ∀ L' B', F (.pl L' w.next B') = 0 := by
    intro L' B'
    have := congrFun h.acct (.pl L' w.next B')
    simp only [Own.add_apply, phys, hf.2, PSt.at] at this
    simp at this; omega
  refine ⟨⟨fun c => ?_, ?_, fun n hn => ?_, fun L' B' c hb => ?_, fun c B' hb => ?_⟩,
    fun L' c B' hc => ⟨?_, ?_⟩, fun L' B' c hb => ?_, by simp [Wd.place]⟩
  · simp only [Wd.place]
    by_cases hc : c = w.next
    · subst hc; rw [upd_same, upd_same]; exact hv
    · rw [upd_ne _ _ hc, upd_ne _ _ hc]; exact h.cont c
  · rw [phys_place hf.2, ← h.acct]
    show O + Own.one (.pl L w.next B) + F + tot (upd Ov w.next Ov₀) (w.next + 1) = _
    rw [htot]
    own_eq
  · simp only [Wd.place] at hn ⊢
    have := h.fresh n (by omega)
    exact ⟨this.1, by rw [upd_ne _ _ (by omega)]; exact this.2⟩
  · simp only [Wd.place] at hb
    by_cases hc : c = w.next
    · subst hc; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ hc] at hb; exact h.busy L' B' c hb
  · simp only [Wd.place] at hb
    by_cases hc : c = w.next
    · subst hc; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ hc] at hb; exact h.nb0 c B' hb
  · have hne : c ≠ w.next := fun e => by subst e; exact hc (hF0 L' B')
    simp only [Wd.place]; rw [upd_ne _ _ hne]
  · have hne : c ≠ w.next := fun e => by subst e; exact hc (hF0 L' B')
    rw [upd_ne _ _ hne]
  · simp only [Wd.place] at hb
    by_cases hc : c = w.next
    · subst hc; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ hc] at hb; exact hb

/-! ### Resuming and dropping: taking the content out and putting it back -/

/-- Take the content of a live place out, to run it: the place is busy, the run that resumed it
holds its token as a frame, and the content's tokens become the running tokens. -/
theorem Inv.takeOut {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {c L : Nat}
    {B : List Nat} {v : St (L + 1)} (hc : w.pl c = .live (L + 1) B v)
    (hO : O (.pl (L + 1) c B) ≠ 0) :
    Inv (Ov c) (O + F) (upd Ov c 0) (w.setPl c (.busy (L + 1) B)) := by
  have hcn : c < w.next := h.lt_next (by rw [hc]; exact PSt.noConfusion)
  have hat : ∀ L' B', PSt.at L' B' (.busy (L + 1) B) = (w.pl c).at L' B' := fun L' B' => by
    rw [hc]; rfl
  refine ⟨fun c' => ?_, ?_, fun n hn => ?_, fun L' B' c' hb => ?_, fun c' B' hb => ?_⟩
  · simp only [Wd.setPl]
    by_cases e : c' = c
    · subst e; rw [upd_same, upd_same]; rfl
    · rw [upd_ne _ _ e, upd_ne _ _ e]; exact h.cont c'
  · rw [phys_setPl hat, ← h.acct]
    show Ov c + (O + F) + tot (upd Ov c 0) w.next = O + F + tot Ov w.next
    have := tot_upd Ov c 0 w.next hcn
    rw [Own.add_zero] at this
    rw [← this]
    own_eq
  · simp only [Wd.setPl] at hn
    have := h.fresh n hn
    exact ⟨this.1, by simp only [Wd.setPl]; rw [upd_ne _ _ (by omega)]; exact this.2⟩
  · simp only [Wd.setPl] at hb
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb; cases hb
      simp only [Own.add_apply]; omega
    · rw [upd_ne _ _ e] at hb
      have := h.busy L' B' c' hb
      simp only [Own.add_apply]; omega
  · simp only [Wd.setPl] at hb
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ e] at hb; exact h.nb0 c' B' hb

/-- Put a content back into its busy place. -/
theorem Inv.putBack {O O' F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O' (O + F) Ov w) {c L : Nat}
    {B : List Nat} (hc : w.pl c = .busy (L + 1) B) {g : St (L + 1)} (hg : VSt (L + 1) B O' g)
    (hb : ∀ L' B' c', w.pl c' = .busy L' B' → c' ≠ c → F (.pl L' c' B') ≠ 0) :
    Inv O F (upd Ov c O') (w.setPl c (.live (L + 1) B g)) := by
  have hcn : c < w.next := h.lt_next (by rw [hc]; exact PSt.noConfusion)
  have hOv : Ov c = 0 := h.ov_free (fun L B v e => by rw [hc] at e; cases e)
  have hat : ∀ L' B', PSt.at L' B' (.live (L + 1) B g) = (w.pl c).at L' B' := fun L' B' => by
    rw [hc]; rfl
  refine ⟨fun c' => ?_, ?_, fun n hn => ?_, fun L' B' c' hb' => ?_, fun c' B' hb' => ?_⟩
  · simp only [Wd.setPl]
    by_cases e : c' = c
    · subst e; rw [upd_same, upd_same]; exact hg
    · rw [upd_ne _ _ e, upd_ne _ _ e]; exact h.cont c'
  · rw [phys_setPl hat, ← h.acct]
    show O + F + tot (upd Ov c O') w.next = O' + (O + F) + tot Ov w.next
    have := tot_upd Ov c O' w.next hcn
    rw [hOv, Own.add_zero] at this
    rw [this]
    own_eq
  · simp only [Wd.setPl] at hn
    have := h.fresh n hn
    exact ⟨this.1, by simp only [Wd.setPl]; rw [upd_ne _ _ (by omega)]; exact this.2⟩
  · simp only [Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact hb L' B' c' hb' e
  · simp only [Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact h.nb0 c' B' hb'

/-- Free a busy place whose content has been dropped; what the drop gave back joins the run. -/
theorem Inv.freePl {O O₁ F : Own} {Ov : Nat → Own} {w : Wd} {c L : Nat} {B : List Nat}
    (h : Inv O₁ (O + Own.one (.pl (L + 1) c B) + F) Ov w) (hc : w.pl c = .busy (L + 1) B)
    (hb : ∀ L' B' c', w.pl c' = .busy L' B' → c' ≠ c → F (.pl L' c' B') ≠ 0) (e : Ev) :
    Inv (O + O₁) F Ov ((w.setPl c .free).emit e) := by
  refine ⟨fun c' => ?_, ?_, fun n hn => ?_, fun L' B' c' hb' => ?_, fun c' B' hb' => ?_⟩
  · simp only [Wd.emit, Wd.setPl]
    by_cases e : c' = c
    · subst e; rw [upd_same]; exact h.ov_free (fun L B v e' => by rw [hc] at e'; cases e')
    · rw [upd_ne _ _ e]; exact h.cont c'
  · apply Own.add_right_cancel (c := Own.one (.pl (L + 1) c B))
    rw [phys_emit, phys_setPl_free hc, ← h.acct]
    show O + O₁ + F + tot Ov w.next + Own.one (.pl (L + 1) c B) =
      O₁ + (O + Own.one (.pl (L + 1) c B) + F) + tot Ov w.next
    own_eq
  · simp only [Wd.emit, Wd.setPl] at hn
    have := h.fresh n hn
    exact ⟨this.1, by simp only [Wd.emit, Wd.setPl]; rw [upd_ne _ _ (by
      have := h.lt_next (c := c) (by rw [hc]; exact PSt.noConfusion); omega)]; exact this.2⟩
  · simp only [Wd.emit, Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact hb L' B' c' hb' e
  · simp only [Wd.emit, Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact h.nb0 c' B' hb'

/-- A frame holds no token of a place the run holds. -/
theorem Inv.frame_ne {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {c L : Nat}
    {B : List Nat} {v : St L} (hp : w.pl c = .live L B v) (hc : O (.pl L c B) ≠ 0) (L' : Nat)
    (B' : List Nat) : F (.pl L' c B') = 0 := by
  by_cases hL : L' = L ∧ B' = B
  · obtain ⟨rfl, rfl⟩ := hL; exact h.not_frame hc
  · have := congrFun h.acct (.pl L' c B')
    simp only [Own.add_apply, phys, hp, PSt.at] at this
    have h0 : (decide (L = L') && decide (B = B')) = false := by
      by_cases h1 : L = L'
      · subst h1; simp only [decide_true, Bool.true_and, decide_eq_false_iff_not]
        exact fun h2 => hL ⟨rfl, h2.symm⟩
      · simp [h1]
    rw [h0] at this; simp at this; omega

/-- Around a resume or a drop: what the frames hold is untouched, and nothing is newly busy. -/
theorem Fr.around {O F : Own} {Ov Ov' : Nat → Own} {w w' : Wd} {c L : Nat} {B : List Nat}
    {v : St L} {p : PSt} {X : Own} (hI : Inv O F Ov w) (hp : w.pl c = .live L B v)
    (hc : O (.pl L c B) ≠ 0)
    (hF' : Fr (O + F) (w.setPl c (.busy L B)) (upd Ov c 0) w' Ov') (hpf : ∀ L' B', p ≠ .busy L' B') :
    Fr F w Ov (w'.setPl c p) (upd Ov' c X) := by
  refine ⟨fun L' c' B' hc' => ?_, fun L' B' c' hb => ?_, hF'.2.2⟩
  · have hne : c' ≠ c := fun e => by subst e; exact hc' (hI.frame_ne hp hc L' B')
    have h1 := hF'.1 L' c' B' (by simp only [Own.add_apply]; omega)
    simp only [Wd.setPl] at h1 ⊢
    rw [upd_ne _ _ hne, upd_ne _ _ hne, h1.1, h1.2, upd_ne _ _ hne, upd_ne _ _ hne]
    exact ⟨rfl, rfl⟩
  · simp only [Wd.setPl] at hb
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb; exact absurd hb (hpf L' B')
    · rw [upd_ne _ _ e] at hb
      have := hF'.2.1 L' B' c' hb
      simp only [Wd.setPl] at this; rwa [upd_ne _ _ e] at this

theorem Fr.ofSum {O F : Own} {w w' : Wd} {Ov Ov' : Nat → Own} (h : Fr (O + F) w Ov w' Ov')
    {c L : Nat} {B : List Nat} (hc : O (.pl L c B) ≠ 0) : w'.pl c = w.pl c ∧ Ov' c = Ov c :=
  h.1 L c B (by simp only [Own.add_apply]; omega)

/-! ## Adequacy: safe trees run safely -/

theorem Inv.touch {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {r : Nat}
    (hu : O (.res r) ≠ 0 ∨ O (.use r) ≠ 0) : ∃ ℓ, w.res r = some ℓ := by
  rcases hu with hu | hu
  · obtain ⟨ℓ, e, -⟩ := h.res_live hu; exact ⟨ℓ, e⟩
  · obtain ⟨ℓ, e, -⟩ := h.use_live hu; exact ⟨ℓ, e⟩

theorem adequacy0 {X : Type} {P : Own → X → Prop} {O : Own} {t : KF (St 0) X}
    (h : TS (VSt 0) 0 P O t) : ∀ (F : Own) (Ov : Nat → Own) (w : Wd), Inv O F Ov w →
    ∃ x w', run0 t w = some (x, w') ∧ Post P F w Ov x w' := by
  induction h with
  | ret hx => intro F Ov w hI; exact ⟨_, w, rfl, _, Ov, hx, hI, Fr.refl _ _ _⟩
  | out _ ih =>
      intro F Ov w hI
      obtain ⟨x, w', hr, hp⟩ := ih F Ov _ (hI.emit _)
      exact ⟨x, w', hr, hp.pre (Fr.refl _ _ _)⟩
  | @acq O ℓ k _ ih =>
      intro F Ov w hI
      obtain ⟨hI', hF⟩ := hI.acquire ℓ
      obtain ⟨x, w', hr, hp⟩ := ih w.next F Ov _ hI'
      exact ⟨x, w', hr, hp.pre hF⟩
  | @free O r k _ ih =>
      intro F Ov w hI
      obtain ⟨ℓ, he, hI', hF⟩ := hI.release
      obtain ⟨x, w', hr, hp⟩ := ih F Ov _ hI'
      refine ⟨x, w', ?_, hp.pre hF⟩
      simp only [run0, he]; exact hr
  | @touch O r k hu _ ih =>
      intro F Ov w hI
      obtain ⟨ℓ, he⟩ := hI.touch hu
      obtain ⟨x, w', hr, hp⟩ := ih F Ov _ (hI.emit _)
      refine ⟨x, w', ?_, hp.pre (Fr.refl _ _ _)⟩
      simp only [run0, he]; exact hr
  | @lend O r k _ ih =>
      intro F Ov w hI
      obtain ⟨hI', hF⟩ := hI.lend
      obtain ⟨x, w', hr, hp⟩ := ih F Ov _ hI'
      exact ⟨x, w', hr, hp.pre hF⟩
  | @reclaim O r k _ ih =>
      intro F Ov w hI
      obtain ⟨hI', hF⟩ := hI.reclaim
      obtain ⟨x, w', hr, hp⟩ := ih F Ov _ hI'
      exact ⟨x, w', hr, hp.pre hF⟩
  | @pnew O Ov₀ B v k _ _ _ => exact (v : Empty).elim
  | @pnext O c B k hc _ _ =>
      intro F Ov w hI
      have hat := hI.at_of hc
      exfalso
      revert hat
      cases hp : w.pl c with
      | free => intro hat; cases hat
      | busy L' B' =>
          intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp; exact hI.nb0 c B hp
      | live L' B' v =>
          intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp; exact (v : Empty).elim
  | @pdrop O c B k _ _ =>
      intro F Ov w hI
      have hc : (O + Own.one (.pl 0 c B)) (.pl 0 c B) ≠ 0 := by simp
      have hat := hI.at_of hc
      exfalso
      revert hat
      cases hp : w.pl c with
      | free => intro hat; cases hat
      | busy L' B' =>
          intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp; exact hI.nb0 c B hp
      | live L' B' v =>
          intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp; exact (v : Empty).elim

/-- **Adequacy** (the cell lemma in its `pnext` and `pdrop` cases). A safe tree at level `L`, in a
world satisfying the invariant, runs to an answer: never stuck, never resuming a busy place, and
the invariant holds after, with the frames' places untouched. -/
theorem adequacy : (L : Nat) → ∀ {X : Type} {P : Own → X → Prop} {O : Own} {t : KF (St L) X},
    TS (VSt L) L P O t → ∀ (F : Own) (Ov : Nat → Own) (w : Wd), Inv O F Ov w →
    ∃ x w', runK L t w = some (x, w') ∧ Post P F w Ov x w'
  | 0, _, _, _, _, h => adequacy0 h
  | L + 1, X, P, O, t, h => by
      induction h with
      | ret hx => intro F Ov w hI; exact ⟨_, w, rfl, _, Ov, hx, hI, Fr.refl _ _ _⟩
      | out _ ih =>
          intro F Ov w hI
          obtain ⟨x, w', hr, hp⟩ := ih F Ov _ (hI.emit _)
          exact ⟨x, w', hr, hp.pre (Fr.refl _ _ _)⟩
      | @acq O ℓ k _ ih =>
          intro F Ov w hI
          obtain ⟨hI', hF⟩ := hI.acquire ℓ
          obtain ⟨x, w', hr, hp⟩ := ih w.next F Ov _ hI'
          exact ⟨x, w', hr, hp.pre hF⟩
      | @free O r k _ ih =>
          intro F Ov w hI
          obtain ⟨ℓ, he, hI', hF⟩ := hI.release
          obtain ⟨x, w', hr, hp⟩ := ih F Ov _ hI'
          refine ⟨x, w', ?_, hp.pre hF⟩
          show runS L _ (.free r k) w = _
          simp only [runS, he]; exact hr
      | @touch O r k hu _ ih =>
          intro F Ov w hI
          obtain ⟨ℓ, he⟩ := hI.touch hu
          obtain ⟨x, w', hr, hp⟩ := ih F Ov _ (hI.emit _)
          refine ⟨x, w', ?_, hp.pre (Fr.refl _ _ _)⟩
          show runS L _ (.touch r k) w = _
          simp only [runS, he]; exact hr
      | @lend O r k _ ih =>
          intro F Ov w hI
          obtain ⟨hI', hF⟩ := hI.lend
          obtain ⟨x, w', hr, hp⟩ := ih F Ov _ hI'
          exact ⟨x, w', hr, hp.pre hF⟩
      | @reclaim O r k _ ih =>
          intro F Ov w hI
          obtain ⟨hI', hF⟩ := hI.reclaim
          obtain ⟨x, w', hr, hp⟩ := ih F Ov _ hI'
          exact ⟨x, w', hr, hp.pre hF⟩
      | @pnew O Ov₀ B v k hv _ ih =>
          intro F Ov w hI
          obtain ⟨hI', hF⟩ := hI.place hv
          obtain ⟨x, w', hr, hp⟩ := ih w.next F _ _ hI'
          exact ⟨x, w', hr, hp.pre hF⟩
      | @pnext O c B k hc _ ih =>
          intro F Ov w hI
          have hat := hI.at_of hc
          revert hat
          cases hp : w.pl c with
          | free => intro hat; cases hat
          | busy L' B' =>
              intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp
              exact absurd (hI.not_frame hc) (hI.busy _ _ c hp)
          | live L' B' v =>
              intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp
              cases v with
              | mk pl dr =>
                have hv : VSt (L + 1) B (Ov c) (Gen.mk pl dr) := by
                  have := hI.cont c; rw [hp] at this; exact this
                obtain ⟨hpull, -⟩ := GenS.unf hv
                obtain ⟨leaf, w', hr, O', Ov', hleaf, hI', hF'⟩ :=
                  adequacy L hpull (O + F) (upd Ov c 0) _ (hI.takeOut hp hc)
                have hw'c : w'.pl c = .busy (L + 1) B := by
                  have := (hF'.ofSum hc).1; simp only [Wd.setPl, upd_same] at this; exact this
                have hbusy : ∀ L'' B'' c'', w'.pl c'' = .busy L'' B'' → c'' ≠ c →
                    F (.pl L'' c'' B'') ≠ 0 := fun L'' B'' c'' hb hne => by
                  have h1 := hF'.2.1 L'' B'' c'' hb
                  simp only [Wd.setPl] at h1; rw [upd_ne _ _ hne] at h1
                  exact hI.busy L'' B'' c'' h1
                cases leaf with
                | none =>
                    have hO' : O' = useOf B := hleaf
                    subst hO'
                    have hI₂ := hI'.putBack hw'c (g := Gen.done) GenS.done hbusy
                    obtain ⟨x, w'', hr', hp'⟩ := ih none F _ _ hI₂
                    refine ⟨x, w'', ?_, hp'.pre (Fr.around hI hp hc hF'
                      (fun _ _ => PSt.noConfusion))⟩
                    show runS L _ (.pnext c k) w = _
                    simp only [runS, hp, dite_true, cast_eq]
                    rw [show runK L pl (w.setPl c (.busy (L + 1) B)) = some (none, w') from hr]
                    exact hr'
                | some ng =>
                    obtain ⟨n, g⟩ := ng
                    have hI₂ := hI'.putBack hw'c (g := g) hleaf hbusy
                    obtain ⟨x, w'', hr', hp'⟩ := ih (some n) F _ _ hI₂
                    refine ⟨x, w'', ?_, hp'.pre (Fr.around hI hp hc hF'
                      (fun _ _ => PSt.noConfusion))⟩
                    show runS L _ (.pnext c k) w = _
                    simp only [runS, hp, dite_true, cast_eq]
                    rw [show runK L pl (w.setPl c (.busy (L + 1) B)) = some (some (n, g), w')
                      from hr]
                    exact hr'
      | @pdrop O c B k _ ih =>
          intro F Ov w hI
          have hc : (O + Own.one (.pl (L + 1) c B)) (.pl (L + 1) c B) ≠ 0 := by simp
          have hat := hI.at_of hc
          revert hat
          cases hp : w.pl c with
          | free => intro hat; cases hat
          | busy L' B' =>
              intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp
              exact absurd (hI.not_frame hc) (hI.busy _ _ c hp)
          | live L' B' v =>
              intro hat; simp [PSt.at] at hat; obtain ⟨rfl, hB⟩ := hat; rw [hB] at hp
              cases v with
              | mk pl dr =>
                have hv : VSt (L + 1) B (Ov c) (Gen.mk pl dr) := by
                  have := hI.cont c; rw [hp] at this; exact this
                obtain ⟨-, hdrop⟩ := GenS.unf hv
                obtain ⟨u, w', hr, O', Ov', hO', hI', hF'⟩ :=
                  adequacy L hdrop _ (upd Ov c 0) _ (hI.takeOut hp hc)
                have hO'B : O' = useOf B := hO'
                subst hO'B
                have hw'c : w'.pl c = .busy (L + 1) B := by
                  have := (hF'.ofSum hc).1; simp only [Wd.setPl, upd_same] at this; exact this
                have hOv'c : Ov' c = 0 := by
                  have := (hF'.ofSum hc).2; simp only [upd_same] at this; exact this
                have hbusy : ∀ L'' B'' c'', w'.pl c'' = .busy L'' B'' → c'' ≠ c →
                    F (.pl L'' c'' B'') ≠ 0 := fun L'' B'' c'' hb hne => by
                  have h1 := hF'.2.1 L'' B'' c'' hb
                  simp only [Wd.setPl] at h1; rw [upd_ne _ _ hne] at h1
                  exact hI.busy L'' B'' c'' h1
                have hI₂ := Inv.freePl hI' hw'c hbusy .fin
                obtain ⟨x, w'', hr', hp'⟩ := ih F _ _ hI₂
                have hupd : upd Ov' c 0 = Ov' := funext fun c' => by
                  by_cases e : c' = c
                  · subst e; rw [upd_same, hOv'c]
                  · rw [upd_ne _ _ e]
                have hFr : Fr F w Ov ((w'.setPl c .free).emit .fin) Ov' := by
                  have := Fr.around (X := 0) (p := .free) hI hp hc hF' (fun _ _ => PSt.noConfusion)
                  rw [hupd] at this
                  exact this
                refine ⟨x, w'', ?_, hp'.pre hFr⟩
                show runS L _ (.pdrop c k) w = _
                simp only [runS, hp, dite_true, cast_eq]
                rw [show runK L dr (w.setPl c (.busy (L + 1) B)) = some ((), w') by cases u; exact hr]
                exact hr'

/-! ## Safety: nothing stuck, nothing left -/

/-- A content owns places only below its own level. -/
def Below (ℓ : Nat) (O : Own) : Prop := ∀ ℓ' c B, ℓ ≤ ℓ' → O (.pl ℓ' c B) = 0

theorem Below.add {ℓ : Nat} {a b : Own} (ha : Below ℓ a) (hb : Below ℓ b) : Below ℓ (a + b) :=
  fun ℓ' c B h => by simp only [Own.add_apply, ha ℓ' c B h, hb ℓ' c B h]

theorem Below.left {ℓ : Nat} {a b : Own} (h : Below ℓ (a + b)) : Below ℓ a :=
  fun ℓ' c B hl => by have := h ℓ' c B hl; simp only [Own.add_apply] at this; omega

theorem Below.mono {ℓ ℓ' : Nat} (hl : ℓ ≤ ℓ') {a : Own} (h : Below ℓ a) : Below ℓ' a :=
  fun ℓ'' c B h' => h ℓ'' c B (by omega)

theorem Below.one {ℓ : Nat} {t : Tok} (ht : ∀ ℓ' c B, ℓ ≤ ℓ' → t ≠ .pl ℓ' c B) :
    Below ℓ (Own.one t) := fun ℓ' c B h => by
  simp only [Own.one_apply]; split
  · rename_i e; exact absurd e.symm (ht ℓ' c B h)
  · rfl

theorem Below.useOf {ℓ : Nat} (B : List Nat) : Below ℓ (useOf B) := fun ℓ' c B' _ => useOf_pl B _ _ _

mutual
/-- **Strata order ownership**: the content of a place at level `ℓ` owns places only below it. -/
theorem VSt.below : (ℓ : Nat) → ∀ {B : List Nat} {O : Own} {v : St ℓ}, VSt ℓ B O v → Below ℓ O
  | 0, _, _, v, _ => (v : Empty).elim
  | ℓ + 1, _, _, .mk _ d, h => TS.below_drop ℓ (GenS.unf h).2

/-- A drop at level `ℓ`, which must dispose of everything but what it gives back, owns places
only up to level `ℓ`. -/
theorem TS.below_drop (ℓ : Nat) {B : List Nat} {O : Own} {d : KF (St ℓ) Unit}
    (h : TS (VSt ℓ) ℓ (fun O' (_ : Unit) => O' = useOf B) O d) : Below (ℓ + 1) O := by
  induction h with
  | ret hx => subst hx; exact Below.useOf B
  | out _ ih => exact ih
  | acq _ ih => exact (ih 0).left
  | free _ ih => exact ih.add (Below.one (fun _ _ _ _ => Tok.noConfusion))
  | touch _ _ ih => exact ih
  | lend _ ih => exact ih.left.left.add (Below.one (fun _ _ _ _ => Tok.noConfusion))
  | reclaim _ ih =>
      exact (ih.left.add (Below.one (fun _ _ _ _ => Tok.noConfusion))).add
        (Below.one (fun _ _ _ _ => Tok.noConfusion))
  | pnew hv _ ih => exact (ih 0).left.add ((VSt.below ℓ hv).mono (Nat.le_succ ℓ))
  | pnext _ _ ih => exact ih none
  | pdrop _ ih =>
      exact ih.left.add (Below.one (fun ℓ' c B h e => by cases e; omega))
end

theorem tot_pos {Ov : Nat → Own} {t : Tok} : ∀ n, tot Ov n t ≠ 0 → ∃ c, c < n ∧ Ov c t ≠ 0
  | 0, h => absurd rfl h
  | n + 1, h => by
      simp only [tot, Own.add_apply] at h
      by_cases h' : tot Ov n t = 0
      · exact ⟨n, by omega, by omega⟩
      · obtain ⟨c, hc, hc'⟩ := tot_pos n h'; exact ⟨c, by omega, hc'⟩

theorem tot_zero {Ov : Nat → Own} (h : ∀ c, Ov c = 0) : ∀ n, tot Ov n = 0
  | 0 => rfl
  | n + 1 => by simp only [tot, tot_zero h n, h n, Own.add_zero]

theorem Inv.init : Inv 0 0 (fun _ => 0) Wd.init :=
  ⟨fun _ => rfl, funext (fun t => by cases t <;> rfl), fun _ _ => ⟨rfl, rfl⟩,
   fun _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

/-- The level of a place's state, `0` when free. -/
def PSt.lvl : PSt → Nat
  | .live L _ _ => L
  | .busy L _ => L
  | .free => 0

theorem PSt.at_lvl {p : PSt} {L : Nat} {B : List Nat} (h : p.at L B = true) : p.lvl = L := by
  cases p <;> simp [PSt.at, PSt.lvl] at h ⊢ <;> exact h.1

/-- A bound on the levels of the places below `n`. -/
def lvlBound (w : Wd) : Nat → Nat
  | 0 => 0
  | n + 1 => max (lvlBound w n) ((w.pl n).lvl + 1)

theorem lt_lvlBound (w : Wd) : ∀ n c, c < n → (w.pl c).lvl < lvlBound w n
  | 0, _, h => absurd h (by omega)
  | n + 1, c, h => by
      simp only [lvlBound]
      by_cases e : c = n
      · subst e; omega
      · have := lt_lvlBound w n c (by omega); omega

/-- With no run and no frame holding anything, nothing is live: the highest live place would
have no owner, since a content owns places only below its level. -/
theorem Inv.empty {Ov : Nat → Own} {w : Wd} (h : Inv 0 0 Ov w) :
    (∀ c, w.pl c = .free) ∧ (∀ r, w.res r = none) := by
  have key : ∀ n ℓ, lvlBound w w.next ≤ ℓ + n → ∀ c B, (w.pl c).at ℓ B = false := by
    intro n
    induction n with
    | zero =>
        intro ℓ hℓ c B
        cases hat : (w.pl c).at ℓ B
        · rfl
        · have hlv := PSt.at_lvl hat
          have hc : c < w.next := h.lt_next (fun e => by rw [e] at hat; cases hat)
          have := lt_lvlBound w w.next c hc
          omega
    | succ n ih =>
        intro ℓ hℓ c B
        cases hat : (w.pl c).at ℓ B
        · rfl
        · exfalso
          have hacct := congrFun h.acct (.pl ℓ c B)
          simp only [Own.add_apply, Own.zero_apply, Nat.zero_add, phys, hat] at hacct
          obtain ⟨c₂, -, hc₂⟩ := tot_pos w.next (show tot Ov w.next (.pl ℓ c B) ≠ 0 by
            rw [hacct]; decide)
          have hcont := h.cont c₂
          generalize hp₂ : w.pl c₂ = p₂ at hcont
          cases p₂ with
          | free => rw [hcont] at hc₂; exact hc₂ rfl
          | busy _ _ => rw [hcont] at hc₂; exact hc₂ rfl
          | live ℓ₂ B₂ v₂ =>
              have hlt : ℓ < ℓ₂ :=
                Nat.lt_of_not_le (fun hle => hc₂ (VSt.below ℓ₂ hcont ℓ c B hle))
              have := ih ℓ₂ (by omega) c₂ B₂
              rw [hp₂] at this; simp [PSt.at] at this
  have hfree : ∀ c, w.pl c = .free := fun c => by
    cases e : w.pl c with
    | free => rfl
    | live L B v =>
        have h2 := key (lvlBound w w.next) L (by omega) c B
        rw [e] at h2; simp [PSt.at] at h2
    | busy L B =>
        have h2 := key (lvlBound w w.next) L (by omega) c B
        rw [e] at h2; simp [PSt.at] at h2
  refine ⟨hfree, fun r => ?_⟩
  have hz : tot Ov w.next = 0 := tot_zero (fun c => h.ov_free (fun L B v e => by
    rw [hfree c] at e; cases e)) w.next
  have h1 := congrFun h.acct (.res r)
  have h2 := congrFun h.acct (.use r)
  simp only [Own.add_apply, Own.zero_apply, hz, phys] at h1 h2
  cases e : w.res r with
  | none => rfl
  | some _ =>
      rw [e] at h1 h2
      cases hl : w.lent r <;> rw [hl] at h1 h2 <;> simp at h1 h2

/-- **Safety of the cell model.** A safe closed tree at any level, owning nothing at the start
and required to own nothing at the end, runs to an answer from the empty world: it never gets
stuck (no use or free of a dead resource, no resume or drop of a dead or busy place), and at the
end every resource has been freed and every place dropped, including the places that contents
created and owned. -/
theorem cell_safety (L : Nat) {X : Type} (t : KF (St L) X)
    (h : TS (VSt L) L (fun O (_ : X) => O = 0) 0 t) :
    ∃ x w', runK L t Wd.init = some (x, w') ∧ (∀ c, w'.pl c = .free) ∧ (∀ r, w'.res r = none) := by
  obtain ⟨x, w', hr, O', Ov', hO', hI', -⟩ := adequacy L h 0 _ _ Inv.init
  subst hO'
  exact ⟨x, w', hr, hI'.empty⟩

/-! ## Without strata -/

/-- **The obstruction without strata.** Phase B's denotation reads a cell's content as a value
(`Act.rd`). A tree type in which a node reads a place holding a continuation over the same trees,
`rd : ((Unit → T) → T) → T` with its inverse, retracts onto its own function space `T → T`; no type
with a map that moves every element does (Lawvere's form of Cantor). This is
`no_negative_domain` (T15) again. -/
theorem no_place_store (T : Type) (rd : ((Unit → T) → T) → T) (un : T → ((Unit → T) → T))
    (h : ∀ k, un (rd k) = k) (flip : T → T) (hflip : ∀ t, flip t ≠ t) : False :=
  let φ : T → T → T := fun t x => un t (fun _ => x)
  let d : T → T := fun x => flip (φ x x)
  let t₀ : T := rd (fun g => d (g ()))
  have h₀ : φ t₀ t₀ = d t₀ := by
    show un (rd (fun g => d (g ()))) (fun _ => t₀) = d t₀
    rw [h]
  hflip (φ t₀ t₀) h₀.symm

/-- The obstruction at phase B's own trees of booleans. -/
theorem no_place_store_tree {S : EffRel.Sig} (rd : ((Unit → EffRel.Tree S Bool) → EffRel.Tree S Bool) →
    EffRel.Tree S Bool) (un : EffRel.Tree S Bool → ((Unit → EffRel.Tree S Bool) → EffRel.Tree S Bool))
    (h : ∀ k, un (rd k) = k) : False :=
  no_place_store _ rd un h EffRel.flipT EffRel.flipT_ne

end EffCell
