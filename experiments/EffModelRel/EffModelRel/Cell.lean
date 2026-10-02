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
  | res (r : Nat)
  | pl (L c : Nat)
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

/-! ## Trees, generators, levels -/

inductive Ev where
  | out (n : Int)
  | acq (ℓ : Nat)
  | free (ℓ : Nat)
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
  /-- A fresh place holding `v`. -/
  | pnew (v : St) (k : Nat → KF St X)
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
  | live (L : Nat) (v : St L)
  /-- Its content has been taken out and is running. -/
  | busy (L : Nat)

structure Wd where
  next : Nat
  res : Nat → Option Nat
  pl : Nat → PSt
  trace : List Ev

def upd {α : Type} (f : Nat → α) (a : Nat) (v : α) : Nat → α := fun x => if x = a then v else f x

@[simp] theorem upd_same {α : Type} (f : Nat → α) (a : Nat) (v : α) : upd f a v a = v := by simp [upd]
theorem upd_ne {α : Type} (f : Nat → α) {a x : Nat} (v : α) (h : x ≠ a) : upd f a v x = f x := by
  simp [upd, h]

namespace Wd
def init : Wd := ⟨0, fun _ => none, fun _ => .free, []⟩
def emit (w : Wd) (e : Ev) : Wd := { w with trace := e :: w.trace }
def acquire (w : Wd) (ℓ : Nat) : Wd :=
  { w with next := w.next + 1, res := upd w.res w.next (some ℓ), trace := .acq ℓ :: w.trace }
def release (w : Wd) (r ℓ : Nat) : Wd :=
  { w with res := upd w.res r none, trace := .free ℓ :: w.trace }
def place (w : Wd) (L : Nat) (v : St L) : Wd :=
  { w with next := w.next + 1, pl := upd w.pl w.next (.live L v), trace := .mk :: w.trace }
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
  | .pnew v k, w => runS L lower (k w.next) (w.place (L + 1) v)
  | .pnext c k, w =>
      match w.pl c with
      | .live L' v =>
          if h : L' = L + 1 then
            match (cast (congrArg St h) v : Gen (St L)) with
            | .mk p _ =>
                match lower p (w.setPl c (.busy (L + 1))) with
                | some (none, w') => runS L lower (k none) (w'.setPl c (.live (L + 1) Gen.done))
                | some (some (n, g), w') => runS L lower (k (some n)) (w'.setPl c (.live (L + 1) g))
                | none => none
          else none
      | _ => none
  | .pdrop c k, w =>
      match w.pl c with
      | .live L' v =>
          if h : L' = L + 1 then
            match (cast (congrArg St h) v : Gen (St L)) with
            | .mk _ d =>
                match lower d (w.setPl c (.busy (L + 1))) with
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
  | .pnew v _, _ => (v : Empty).elim
  | .pnext _ _, _ => none
  | .pdrop _ _, _ => none

/-- **The run**, by recursion on the level. -/
def runK : (L : Nat) → {X : Type} → KF (St L) X → Wd → Option (X × Wd)
  | 0, _, t, w => run0 t w
  | L + 1, _, t, w => runS L (fun t' w' => runK L t' w') t w

/-! ## Safe trees, and the invariant of a place -/

/-- Safe trees at level `lvl`, whose new places hold contents satisfying `V`. -/
inductive TS {St' : Type} (V : Own → St' → Prop) (lvl : Nat) {X : Type} (P : Own → X → Prop) :
    Own → KF St' X → Prop where
  | ret {O : Own} {x : X} : P O x → TS V lvl P O (.ret x)
  | out {O : Own} {n : Int} {k : KF St' X} : TS V lvl P O k → TS V lvl P O (.out n k)
  | acq {O : Own} {ℓ : Nat} {k : Nat → KF St' X} :
      (∀ r, TS V lvl P (O + Own.one (.res r)) (k r)) → TS V lvl P O (.acq ℓ k)
  | free {O : Own} {r : Nat} {k : KF St' X} :
      TS V lvl P O k → TS V lvl P (O + Own.one (.res r)) (.free r k)
  | pnew {O Ov : Own} {v : St'} {k : Nat → KF St' X} :
      V Ov v → (∀ c, TS V lvl P (O + Own.one (.pl lvl c)) (k c)) → TS V lvl P (O + Ov) (.pnew v k)
  | pnext {O : Own} {c : Nat} {k : Option Int → KF St' X} :
      O (.pl lvl c) ≠ 0 → (∀ a, TS V lvl P O (k a)) → TS V lvl P O (.pnext c k)
  | pdrop {O : Own} {c : Nat} {k : KF St' X} :
      TS V lvl P O k → TS V lvl P (O + Own.one (.pl lvl c)) (.pdrop c k)

/-- A generator's pull answers done, owning nothing, or an element and a rest in `Q`. -/
def GenLeaf {St' : Type} (Q : Own → Gen St' → Prop) : Own → Option (Int × Gen St') → Prop
  | O, none => O = 0
  | O, some (_, g) => Q O g

/-- The generators whose pull and drop are safe, as the least predicate closed under one
unfolding. -/
def GenS {St' : Type} (V : Own → St' → Prop) (lvl : Nat) (O : Own) (g : Gen St') : Prop :=
  ∀ Q : Own → Gen St' → Prop,
    (∀ O p d, TS V lvl (GenLeaf Q) O p → TS V lvl (fun O' (_ : Unit) => O' = 0) O d → Q O (.mk p d)) →
    Q O g

/-- **The invariant of a place at level `L`**: what its content may hold. -/
def VSt : (L : Nat) → Own → St L → Prop
  | 0, _, v => (v : Empty).elim
  | L + 1, O, g => GenS (VSt L) L O g

theorem TS.mapP {St' : Type} {V : Own → St' → Prop} {lvl : Nat} {X : Type} {P P' : Own → X → Prop}
    {O : Own} {t : KF St' X} (h : TS V lvl P O t) (hP : ∀ O x, P O x → P' O x) :
    TS V lvl P' O t := by
  induction h with
  | ret hx => exact .ret (hP _ _ hx)
  | out _ ih => exact .out ih
  | acq _ ih => exact .acq ih
  | free _ ih => exact .free ih
  | pnew hv _ ih => exact .pnew hv ih
  | pnext hc _ ih => exact .pnext hc ih
  | pdrop _ ih => exact .pdrop ih

theorem GenLeaf.map {St' : Type} {Q Q' : Own → Gen St' → Prop} (h : ∀ O g, Q O g → Q' O g) :
    ∀ O x, GenLeaf Q O x → GenLeaf Q' O x
  | _, none, hx => hx
  | _, some (_, _), hx => h _ _ hx

theorem GenS.intro {St' : Type} {V : Own → St' → Prop} {lvl : Nat} {O : Own} {p d}
    (hp : TS V lvl (GenLeaf (GenS V lvl)) O p) (hd : TS V lvl (fun O' (_ : Unit) => O' = 0) O d) :
    GenS V lvl O (.mk p d) :=
  fun Q hQ => hQ O p d (hp.mapP (GenLeaf.map (fun _ _ hs => hs Q hQ))) hd

/-- The cell's invariant unfolds: a safe pull whose rest is again safe, and a safe drop. -/
theorem GenS.unf {St' : Type} {V : Own → St' → Prop} {lvl : Nat} {O : Own} {p d}
    (h : GenS V lvl O (.mk p d)) :
    TS V lvl (GenLeaf (GenS V lvl)) O p ∧ TS V lvl (fun O' (_ : Unit) => O' = 0) O d := by
  have := h (fun O g => match g with
      | .mk p d => TS V lvl (GenLeaf (GenS V lvl)) O p ∧ TS V lvl (fun O' (_ : Unit) => O' = 0) O d)
    (fun O p d hp hd => ⟨hp.mapP (GenLeaf.map (fun O g hg => by
      cases g with | mk p' d' => exact GenS.intro hg.1 hg.2)), hd⟩)
  exact this

theorem GenS.done {St' : Type} {V : Own → St' → Prop} {lvl : Nat} :
    GenS V lvl 0 (Gen.done (St' := St')) :=
  GenS.intro (.ret rfl) (.ret rfl)

/-! ## The world invariant -/

/-- The tokens the contents of the places below `n` own. -/
def tot (Ov : Nat → Own) : Nat → Own
  | 0 => 0
  | n + 1 => tot Ov n + Ov n

/-- The place is live or busy at level `L`. -/
def PSt.at (L : Nat) : PSt → Bool
  | .live L' _ => decide (L' = L)
  | .busy L' => decide (L' = L)
  | .free => false

/-- What the content of a place owns. -/
def PlInv : PSt → Own → Prop
  | .live L v, O => VSt L O v
  | _, O => O = 0

/-- The world's live resources and places, one token each. -/
def phys (w : Wd) : Own := fun t =>
  match t with
  | .res r => (w.res r).isSome.toNat
  | .pl L c => ((w.pl c).at L).toNat

/-- **The world invariant**, for a run holding `O` inside frames holding `F`, with `Ov` what each
place's content owns. Every live resource and place has exactly one token, held by the run, a
frame or a content (`acct`); a busy place's token is held by a frame, the one running its
content. -/
structure Inv (O F : Own) (Ov : Nat → Own) (w : Wd) : Prop where
  cont : ∀ c, PlInv (w.pl c) (Ov c)
  acct : O + F + tot Ov w.next = phys w
  fresh : ∀ n, w.next ≤ n → w.res n = none ∧ w.pl n = .free
  busy : ∀ L c, w.pl c = .busy L → F (.pl L c) ≠ 0
  nb0 : ∀ c, w.pl c ≠ .busy 0

/-- What a run leaves alone: the places a frame holds, and no place newly busy. -/
def Fr (F : Own) (w : Wd) (Ov : Nat → Own) (w' : Wd) (Ov' : Nat → Own) : Prop :=
  (∀ L c, F (.pl L c) ≠ 0 → w'.pl c = w.pl c ∧ Ov' c = Ov c) ∧
  (∀ L c, w'.pl c = .busy L → w.pl c = .busy L) ∧ w.next ≤ w'.next

theorem Fr.refl (F : Own) (w : Wd) (Ov : Nat → Own) : Fr F w Ov w Ov :=
  ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ h => h, Nat.le_refl _⟩

theorem Fr.trans {F : Own} {w₁ w₂ w₃ : Wd} {O₁ O₂ O₃ : Nat → Own} (h₁ : Fr F w₁ O₁ w₂ O₂)
    (h₂ : Fr F w₂ O₂ w₃ O₃) : Fr F w₁ O₁ w₃ O₃ :=
  ⟨fun L c hc => ⟨((h₂.1 L c hc).1).trans (h₁.1 L c hc).1, ((h₂.1 L c hc).2).trans (h₁.1 L c hc).2⟩,
   fun L c hb => h₁.2.1 L c (h₂.2.1 L c hb), Nat.le_trans h₁.2.2 h₂.2.2⟩

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

/-! ### The world's steps -/

theorem phys_emit (w : Wd) (e : Ev) : phys (w.emit e) = phys w := rfl

theorem phys_acquire {w : Wd} (hf : w.res w.next = none) (ℓ : Nat) :
    phys (w.acquire ℓ) = phys w + Own.one (.res w.next) := by
  funext t; cases t with
  | res r =>
      simp only [phys, Wd.acquire, Own.add_apply, Own.one_apply]
      by_cases hr : r = w.next
      · subst hr; simp [upd, hf]
      · simp [upd, hr]
  | pl L c => rfl

theorem phys_release {w : Wd} {r ℓ : Nat} (he : w.res r = some ℓ) :
    phys (w.release r ℓ) + Own.one (.res r) = phys w := by
  funext t; cases t with
  | res r' =>
      simp only [phys, Wd.release, Own.add_apply, Own.one_apply]
      by_cases hr : r' = r
      · subst hr; simp [upd, he]
      · simp [upd, hr]
  | pl L c =>
      show ((w.pl c).at L).toNat + (if Tok.pl L c = Tok.res r then 1 else 0) =
        ((w.pl c).at L).toNat
      simp

theorem phys_place {w : Wd} (hf : w.pl w.next = .free) (L : Nat) (v : St L) :
    phys (w.place L v) = phys w + Own.one (.pl L w.next) := by
  funext t; cases t with
  | res r =>
      show (w.res r).isSome.toNat = (w.res r).isSome.toNat + (if Tok.res r = Tok.pl L w.next then 1 else 0)
      simp
  | pl L' c =>
      simp only [phys, Wd.place, Own.add_apply, Own.one_apply]
      by_cases hc : c = w.next
      · subst hc; rw [hf]
        by_cases hL : L' = L
        · subst hL; simp [upd, PSt.at]
        · simp [upd, PSt.at, Ne.symm hL, hL]
      · simp [upd, hc]

/-- Changing a place's state without changing its level leaves the accounting alone. -/
theorem phys_setPl {w : Wd} {c : Nat} {p : PSt} (h : ∀ L, p.at L = (w.pl c).at L) :
    phys (w.setPl c p) = phys w := by
  funext t; cases t with
  | res r => rfl
  | pl L c' =>
      show ((upd w.pl c p c').at L).toNat = ((w.pl c').at L).toNat
      by_cases hc : c' = c
      · subst hc; rw [upd_same, h L]
      · rw [upd_ne _ _ hc]

theorem phys_setPl_free {w : Wd} {c L : Nat} (h : w.pl c = .busy L) :
    phys (w.setPl c .free) + Own.one (.pl L c) = phys w := by
  funext t; cases t with
  | res r =>
      show (w.res r).isSome.toNat + (if Tok.res r = Tok.pl L c then 1 else 0) = (w.res r).isSome.toNat
      simp
  | pl L' c' =>
      show ((upd w.pl c .free c').at L').toNat + (if Tok.pl L' c' = Tok.pl L c then 1 else 0) =
        ((w.pl c').at L').toNat
      by_cases hc : c' = c
      · subst hc; rw [upd_same, h]
        by_cases hL : L' = L
        · subst hL; simp [PSt.at]
        · simp [PSt.at, hL, Ne.symm hL]
      · rw [upd_ne _ _ hc]; simp [hc]

/-! ### Facts about the invariant -/

theorem Inv.ov_free {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {c : Nat}
    (hc : ∀ L v, w.pl c ≠ .live L v) : Ov c = 0 := by
  have := h.cont c
  generalize hp : w.pl c = p at this hc
  cases p with
  | live L v => exact absurd rfl (hc L v)
  | busy _ => exact this
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
    (hO : O (.pl L c) ≠ 0) : (w.pl c).at L = true := by
  have := congrFun h.acct (.pl L c)
  simp only [Own.add_apply, phys] at this
  cases hb : (w.pl c).at L
  · rw [hb] at this; simp at this; omega
  · rfl

theorem Inv.emit {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) (e : Ev) :
    Inv O F Ov (w.emit e) :=
  ⟨h.cont, h.acct, h.fresh, h.busy, h.nb0⟩

theorem Inv.acquire {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) (ℓ : Nat) :
    Inv (O + Own.one (.res w.next)) F Ov (w.acquire ℓ) ∧ Fr F w Ov (w.acquire ℓ) Ov := by
  have hf := h.fresh w.next (Nat.le_refl _)
  have hOv : Ov w.next = 0 := h.ov_free (fun L v e => by rw [hf.2] at e; cases e)
  refine ⟨⟨h.cont, ?_, fun n hn => ?_, h.busy, h.nb0⟩,
    ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ hb => hb, by simp [Wd.acquire]⟩⟩
  · rw [phys_acquire hf.1, ← h.acct]
    show O + Own.one (.res w.next) + F + (tot Ov w.next + Ov w.next) = _
    rw [hOv]
    exact Own.ext fun t => by simp only [Own.add_apply, Own.zero_apply]; omega
  · simp only [Wd.acquire] at hn ⊢
    have := h.fresh n (by omega)
    exact ⟨by rw [upd_ne _ _ (by omega)]; exact this.1, this.2⟩

theorem Inv.release {O F : Own} {Ov : Nat → Own} {w : Wd} {r : Nat}
    (h : Inv (O + Own.one (.res r)) F Ov w) :
    ∃ ℓ, w.res r = some ℓ ∧ Inv O F Ov (w.release r ℓ) ∧ Fr F w Ov (w.release r ℓ) Ov := by
  have hr := congrFun h.acct (.res r)
  simp only [Own.add_apply, Own.one_apply, if_true, phys] at hr
  cases e : w.res r with
  | none => rw [e] at hr; simp at hr
  | some ℓ =>
      have hrn : r < w.next := Nat.lt_of_not_le (fun hn => by rw [(h.fresh r hn).1] at e; cases e)
      refine ⟨ℓ, rfl, ⟨h.cont, ?_, fun n hn => ?_, h.busy, h.nb0⟩,
        ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ hb => hb, Nat.le_refl _⟩⟩
      · apply Own.add_right_cancel (c := Own.one (.res r))
        rw [phys_release e, ← h.acct]
        show O + F + tot Ov w.next + Own.one (.res r) = _
        exact Own.ext fun t => by simp only [Own.add_apply]; omega
      · simp only [Wd.release] at hn ⊢
        have := h.fresh n hn
        exact ⟨by rw [upd_ne _ _ (by omega)]; exact this.1, this.2⟩

theorem Inv.place {O Ov₀ F : Own} {Ov : Nat → Own} {w : Wd} {L : Nat} {v : St L}
    (h : Inv (O + Ov₀) F Ov w) (hv : VSt L Ov₀ v) :
    Inv (O + Own.one (.pl L w.next)) F (upd Ov w.next Ov₀) (w.place L v) ∧
      Fr F w Ov (w.place L v) (upd Ov w.next Ov₀) := by
  have hf := h.fresh w.next (Nat.le_refl _)
  have hOv : Ov w.next = 0 := h.ov_free (fun L v e => by rw [hf.2] at e; cases e)
  have htot : tot (upd Ov w.next Ov₀) (w.next + 1) = tot Ov w.next + Ov₀ := by
    simp only [tot]; rw [upd_same, tot_upd_ge _ _ (Nat.le_refl _)]
  have hF0 : ∀ L', F (.pl L' w.next) = 0 := by
    intro L'
    have := congrFun h.acct (.pl L' w.next)
    simp only [Own.add_apply, phys, hf.2, PSt.at] at this
    simp at this; omega
  refine ⟨⟨fun c => ?_, ?_, fun n hn => ?_, fun L' c hb => ?_, fun c hb => ?_⟩,
    fun L' c hc => ⟨?_, ?_⟩, fun L' c hb => ?_, by simp [Wd.place]⟩
  · simp only [Wd.place]
    by_cases hc : c = w.next
    · subst hc; rw [upd_same, upd_same]; exact hv
    · rw [upd_ne _ _ hc, upd_ne _ _ hc]; exact h.cont c
  · rw [phys_place hf.2, ← h.acct]
    show O + Own.one (.pl L w.next) + F + tot (upd Ov w.next Ov₀) (w.next + 1) = _
    rw [htot]
    exact Own.ext fun t => by simp only [Own.add_apply]; omega
  · simp only [Wd.place] at hn ⊢
    have := h.fresh n (by omega)
    exact ⟨this.1, by rw [upd_ne _ _ (by omega)]; exact this.2⟩
  · simp only [Wd.place] at hb
    by_cases hc : c = w.next
    · subst hc; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ hc] at hb; exact h.busy L' c hb
  · simp only [Wd.place] at hb
    by_cases hc : c = w.next
    · subst hc; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ hc] at hb; exact h.nb0 c hb
  · have hne : c ≠ w.next := fun e => by subst e; exact hc (hF0 L')
    simp only [Wd.place]; rw [upd_ne _ _ hne]
  · have hne : c ≠ w.next := fun e => by subst e; exact hc (hF0 L')
    rw [upd_ne _ _ hne]
  · simp only [Wd.place] at hb
    by_cases hc : c = w.next
    · subst hc; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ hc] at hb; exact hb

/-! ### Resuming and dropping: taking the content out and putting it back -/

/-- Take the content of a live place out, to run it: the place is busy, the run that resumed it
holds its token as a frame, and the content's tokens become the running tokens. -/
theorem Inv.takeOut {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {c L : Nat}
    {v : St (L + 1)} (hc : w.pl c = .live (L + 1) v) (hO : O (.pl (L + 1) c) ≠ 0) :
    Inv (Ov c) (O + F) (upd Ov c 0) (w.setPl c (.busy (L + 1))) := by
  have hcn : c < w.next := h.lt_next (by rw [hc]; exact PSt.noConfusion)
  have hat : ∀ L', PSt.at L' (.busy (L + 1)) = (w.pl c).at L' := fun L' => by rw [hc]; rfl
  refine ⟨fun c' => ?_, ?_, fun n hn => ?_, fun L' c' hb => ?_, fun c' hb => ?_⟩
  · simp only [Wd.setPl]
    by_cases e : c' = c
    · subst e; rw [upd_same, upd_same]; rfl
    · rw [upd_ne _ _ e, upd_ne _ _ e]; exact h.cont c'
  · rw [phys_setPl hat, ← h.acct]
    show Ov c + (O + F) + tot (upd Ov c 0) w.next = O + F + tot Ov w.next
    have := tot_upd Ov c 0 w.next hcn
    rw [Own.add_zero] at this
    rw [← this]
    exact Own.ext fun t => by simp only [Own.add_apply]; omega
  · simp only [Wd.setPl] at hn
    have := h.fresh n hn
    exact ⟨this.1, by simp only [Wd.setPl]; rw [upd_ne _ _ (by omega)]; exact this.2⟩
  · simp only [Wd.setPl] at hb
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb; cases hb
      simp only [Own.add_apply]; omega
    · rw [upd_ne _ _ e] at hb
      have := h.busy L' c' hb
      simp only [Own.add_apply]; omega
  · simp only [Wd.setPl] at hb
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb; cases hb
    · rw [upd_ne _ _ e] at hb; exact h.nb0 c' hb

/-- Put a content back into its busy place. -/
theorem Inv.putBack {O O' F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O' (O + F) Ov w) {c L : Nat}
    (hc : w.pl c = .busy (L + 1)) {g : St (L + 1)} (hg : VSt (L + 1) O' g)
    (hb : ∀ L' c', w.pl c' = .busy L' → c' ≠ c → F (.pl L' c') ≠ 0) :
    Inv O F (upd Ov c O') (w.setPl c (.live (L + 1) g)) := by
  have hcn : c < w.next := h.lt_next (by rw [hc]; exact PSt.noConfusion)
  have hOv : Ov c = 0 := h.ov_free (fun L v e => by rw [hc] at e; cases e)
  have hat : ∀ L', PSt.at L' (.live (L + 1) g) = (w.pl c).at L' := fun L' => by rw [hc]; rfl
  refine ⟨fun c' => ?_, ?_, fun n hn => ?_, fun L' c' hb' => ?_, fun c' hb' => ?_⟩
  · simp only [Wd.setPl]
    by_cases e : c' = c
    · subst e; rw [upd_same, upd_same]; exact hg
    · rw [upd_ne _ _ e, upd_ne _ _ e]; exact h.cont c'
  · rw [phys_setPl hat, ← h.acct]
    show O + F + tot (upd Ov c O') w.next = O' + (O + F) + tot Ov w.next
    have := tot_upd Ov c O' w.next hcn
    rw [hOv, Own.add_zero] at this
    rw [this]
    exact Own.ext fun t => by simp only [Own.add_apply]; omega
  · simp only [Wd.setPl] at hn
    have := h.fresh n hn
    exact ⟨this.1, by simp only [Wd.setPl]; rw [upd_ne _ _ (by omega)]; exact this.2⟩
  · simp only [Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact hb L' c' hb' e
  · simp only [Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact h.nb0 c' hb'

/-- Free a busy place whose content has been dropped. -/
theorem Inv.freePl {O F : Own} {Ov : Nat → Own} {w : Wd} {c L : Nat}
    (h : Inv 0 (O + Own.one (.pl (L + 1) c) + F) Ov w) (hc : w.pl c = .busy (L + 1))
    (hb : ∀ L' c', w.pl c' = .busy L' → c' ≠ c → F (.pl L' c') ≠ 0) (e : Ev) :
    Inv O F Ov ((w.setPl c .free).emit e) := by
  refine ⟨fun c' => ?_, ?_, fun n hn => ?_, fun L' c' hb' => ?_, fun c' hb' => ?_⟩
  · simp only [Wd.emit, Wd.setPl]
    by_cases e : c' = c
    · subst e; rw [upd_same]; exact h.ov_free (fun L v e' => by rw [hc] at e'; cases e')
    · rw [upd_ne _ _ e]; exact h.cont c'
  · apply Own.add_right_cancel (c := Own.one (.pl (L + 1) c))
    rw [phys_emit, phys_setPl_free hc, ← h.acct]
    show O + F + tot Ov w.next + Own.one (.pl (L + 1) c) = 0 + (O + Own.one (.pl (L + 1) c) + F) +
      tot Ov w.next
    exact Own.ext fun t => by simp only [Own.add_apply, Own.zero_apply]; omega
  · simp only [Wd.emit, Wd.setPl] at hn
    have := h.fresh n hn
    exact ⟨this.1, by simp only [Wd.emit, Wd.setPl]; rw [upd_ne _ _ (by
      have := h.lt_next (c := c) (by rw [hc]; exact PSt.noConfusion); omega)]; exact this.2⟩
  · simp only [Wd.emit, Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact hb L' c' hb' e
  · simp only [Wd.emit, Wd.setPl] at hb'
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb'; cases hb'
    · rw [upd_ne _ _ e] at hb'; exact h.nb0 c' hb'

/-- A token the run holds is held by no frame. -/
theorem Inv.not_frame {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {t : Tok}
    (hO : O t ≠ 0) : F t = 0 := by
  have := h.le_one t; omega

/-- A frame holds no token of a place the run holds. -/
theorem Inv.frame_ne {O F : Own} {Ov : Nat → Own} {w : Wd} (h : Inv O F Ov w) {c L : Nat}
    {v : St L} (hp : w.pl c = .live L v) (hc : O (.pl L c) ≠ 0) (L' : Nat) : F (.pl L' c) = 0 := by
  by_cases hL : L' = L
  · subst hL; exact h.not_frame hc
  · have := congrFun h.acct (.pl L' c)
    simp only [Own.add_apply, phys, hp, PSt.at] at this
    simp [Ne.symm hL] at this; omega

/-- Around a resume or a drop: what the frames hold is untouched, and nothing is newly busy. -/
theorem Fr.around {O F : Own} {Ov Ov' : Nat → Own} {w w' : Wd} {c L : Nat} {v : St L} {p : PSt}
    {X : Own} (hI : Inv O F Ov w) (hp : w.pl c = .live L v) (hc : O (.pl L c) ≠ 0)
    (hF' : Fr (O + F) (w.setPl c (.busy L)) (upd Ov c 0) w' Ov') (hpf : ∀ L', p ≠ .busy L') :
    Fr F w Ov (w'.setPl c p) (upd Ov' c X) := by
  refine ⟨fun L' c' hc' => ?_, fun L' c' hb => ?_, hF'.2.2⟩
  · have hne : c' ≠ c := fun e => by subst e; exact hc' (hI.frame_ne hp hc L')
    have h1 := hF'.1 L' c' (by simp only [Own.add_apply]; omega)
    simp only [Wd.setPl] at h1 ⊢
    rw [upd_ne _ _ hne, upd_ne _ _ hne, h1.1, h1.2, upd_ne _ _ hne, upd_ne _ _ hne]
    exact ⟨rfl, rfl⟩
  · simp only [Wd.setPl] at hb
    by_cases e : c' = c
    · subst e; rw [upd_same] at hb; exact absurd hb (hpf L')
    · rw [upd_ne _ _ e] at hb
      have := hF'.2.1 L' c' hb
      simp only [Wd.setPl] at this; rwa [upd_ne _ _ e] at this

theorem Fr.ofSum {O F : Own} {w w' : Wd} {Ov Ov' : Nat → Own} (h : Fr (O + F) w Ov w' Ov')
    {c L : Nat} (hc : O (.pl L c) ≠ 0) : w'.pl c = w.pl c ∧ Ov' c = Ov c :=
  h.1 L c (by simp only [Own.add_apply]; omega)

/-! ## Adequacy: safe trees run safely -/

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
  | @pnew O Ov₀ v k _ _ _ => exact (v : Empty).elim
  | @pnext O c k hc _ _ =>
      intro F Ov w hI
      have hat := hI.at_of hc
      exfalso
      revert hat
      cases hp : w.pl c with
      | free => intro hat; cases hat
      | busy L' =>
          intro hat; simp [PSt.at] at hat; subst hat; exact hI.nb0 c hp
      | live L' v =>
          intro hat; simp [PSt.at] at hat; subst hat; exact (v : Empty).elim
  | @pdrop O c k _ _ =>
      intro F Ov w hI
      have hc : (O + Own.one (.pl 0 c)) (.pl 0 c) ≠ 0 := by simp
      have hat := hI.at_of hc
      exfalso
      revert hat
      cases hp : w.pl c with
      | free => intro hat; cases hat
      | busy L' =>
          intro hat; simp [PSt.at] at hat; subst hat; exact hI.nb0 c hp
      | live L' v =>
          intro hat; simp [PSt.at] at hat; subst hat; exact (v : Empty).elim

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
      | @pnew O Ov₀ v k hv _ ih =>
          intro F Ov w hI
          obtain ⟨hI', hF⟩ := hI.place hv
          obtain ⟨x, w', hr, hp⟩ := ih w.next F _ _ hI'
          exact ⟨x, w', hr, hp.pre hF⟩
      | @pnext O c k hc _ ih =>
          intro F Ov w hI
          have hat := hI.at_of hc
          revert hat
          cases hp : w.pl c with
          | free => intro hat; cases hat
          | busy L' =>
              intro hat; simp [PSt.at] at hat; subst hat
              exact absurd (hI.not_frame hc) (hI.busy _ c hp)
          | live L' v =>
              intro hat; simp [PSt.at] at hat; subst hat
              cases v with
              | mk pl dr =>
                have hv : VSt (L + 1) (Ov c) (Gen.mk pl dr) := by
                  have := hI.cont c; rw [hp] at this; exact this
                obtain ⟨hpull, -⟩ := GenS.unf hv
                obtain ⟨leaf, w', hr, O', Ov', hleaf, hI', hF'⟩ :=
                  adequacy L hpull (O + F) (upd Ov c 0) _ (hI.takeOut hp hc)
                have hw'c : w'.pl c = .busy (L + 1) := by
                  have := (hF'.ofSum hc).1; simp only [Wd.setPl, upd_same] at this; exact this
                have hOv'c : Ov' c = 0 := by
                  have := (hF'.ofSum hc).2; simp only [upd_same] at this; exact this
                have hbusy : ∀ L'' c'', w'.pl c'' = .busy L'' → c'' ≠ c →
                    F (.pl L'' c'') ≠ 0 := fun L'' c'' hb hne => by
                  have h1 := hF'.2.1 L'' c'' hb
                  simp only [Wd.setPl] at h1; rw [upd_ne _ _ hne] at h1
                  exact hI.busy L'' c'' h1
                cases leaf with
                | none =>
                    have hO'0 : O' = 0 := hleaf
                    subst hO'0
                    have hI₂ := hI'.putBack hw'c (g := Gen.done) GenS.done hbusy
                    obtain ⟨x, w'', hr', hp'⟩ := ih none F _ _ hI₂
                    refine ⟨x, w'', ?_, hp'.pre (Fr.around hI hp hc hF' (fun _ => PSt.noConfusion))⟩
                    show runS L _ (.pnext c k) w = _
                    simp only [runS, hp, dite_true, cast_eq]
                    rw [show runK L pl (w.setPl c (.busy (L + 1))) = some (none, w') from hr]
                    exact hr'
                | some ng =>
                    obtain ⟨n, g⟩ := ng
                    have hI₂ := hI'.putBack hw'c (g := g) hleaf hbusy
                    obtain ⟨x, w'', hr', hp'⟩ := ih (some n) F _ _ hI₂
                    refine ⟨x, w'', ?_, hp'.pre (Fr.around hI hp hc hF' (fun _ => PSt.noConfusion))⟩
                    show runS L _ (.pnext c k) w = _
                    simp only [runS, hp, dite_true, cast_eq]
                    rw [show runK L pl (w.setPl c (.busy (L + 1))) = some (some (n, g), w') from hr]
                    exact hr'
      | @pdrop O c k _ ih =>
          intro F Ov w hI
          have hc : (O + Own.one (.pl (L + 1) c)) (.pl (L + 1) c) ≠ 0 := by simp
          have hat := hI.at_of hc
          revert hat
          cases hp : w.pl c with
          | free => intro hat; cases hat
          | busy L' =>
              intro hat; simp [PSt.at] at hat; subst hat
              exact absurd (hI.not_frame hc) (hI.busy _ c hp)
          | live L' v =>
              intro hat; simp [PSt.at] at hat; subst hat
              cases v with
              | mk pl dr =>
                have hv : VSt (L + 1) (Ov c) (Gen.mk pl dr) := by
                  have := hI.cont c; rw [hp] at this; exact this
                obtain ⟨-, hdrop⟩ := GenS.unf hv
                obtain ⟨u, w', hr, O', Ov', hO', hI', hF'⟩ :=
                  adequacy L hdrop _ (upd Ov c 0) _ (hI.takeOut hp hc)
                have hO'0 : O' = 0 := hO'
                subst hO'0
                have hw'c : w'.pl c = .busy (L + 1) := by
                  have := (hF'.ofSum hc).1; simp only [Wd.setPl, upd_same] at this; exact this
                have hOv'c : Ov' c = 0 := by
                  have := (hF'.ofSum hc).2; simp only [upd_same] at this; exact this
                have hbusy : ∀ L'' c'', w'.pl c'' = .busy L'' → c'' ≠ c →
                    F (.pl L'' c'') ≠ 0 := fun L'' c'' hb hne => by
                  have h1 := hF'.2.1 L'' c'' hb
                  simp only [Wd.setPl] at h1; rw [upd_ne _ _ hne] at h1
                  exact hI.busy L'' c'' h1
                have hI₂ := Inv.freePl hI' hw'c hbusy .fin
                obtain ⟨x, w'', hr', hp'⟩ := ih F _ _ hI₂
                have hupd : upd Ov' c 0 = Ov' := funext fun c' => by
                  by_cases e : c' = c
                  · subst e; rw [upd_same, hOv'c]
                  · rw [upd_ne _ _ e]
                have hFr : Fr F w Ov ((w'.setPl c .free).emit .fin) Ov' := by
                  have := Fr.around (X := 0) (p := .free) hI hp hc hF' (fun _ => PSt.noConfusion)
                  rw [hupd] at this
                  exact this
                refine ⟨x, w'', ?_, hp'.pre hFr⟩
                show runS L _ (.pdrop c k) w = _
                simp only [runS, hp, dite_true, cast_eq]
                rw [show runK L dr (w.setPl c (.busy (L + 1))) = some ((), w') by cases u; exact hr]
                exact hr'

/-! ## Safety: nothing stuck, nothing left -/

/-- A content owns places only below its own level. -/
def Below (ℓ : Nat) (O : Own) : Prop := ∀ ℓ' c, ℓ ≤ ℓ' → O (.pl ℓ' c) = 0

theorem Below.add {ℓ : Nat} {a b : Own} (ha : Below ℓ a) (hb : Below ℓ b) : Below ℓ (a + b) :=
  fun ℓ' c h => by simp only [Own.add_apply, ha ℓ' c h, hb ℓ' c h]

theorem Below.left {ℓ : Nat} {a b : Own} (h : Below ℓ (a + b)) : Below ℓ a :=
  fun ℓ' c hl => by have := h ℓ' c hl; simp only [Own.add_apply] at this; omega

theorem Below.mono {ℓ ℓ' : Nat} (hl : ℓ ≤ ℓ') {a : Own} (h : Below ℓ a) : Below ℓ' a :=
  fun ℓ'' c h' => h ℓ'' c (by omega)

theorem Below.res {ℓ r : Nat} : Below ℓ (Own.one (.res r)) := fun _ _ _ => by simp

theorem Below.pl {ℓ c : Nat} : Below (ℓ + 1) (Own.one (.pl ℓ c)) := fun ℓ' c' h => by
  simp only [Own.one_apply]; split
  · rename_i e; cases e; omega
  · rfl

mutual
/-- **Strata order ownership**: the content of a place at level `ℓ` owns places only below it. -/
theorem VSt.below : (ℓ : Nat) → ∀ {O : Own} {v : St ℓ}, VSt ℓ O v → Below ℓ O
  | 0, _, v, _ => (v : Empty).elim
  | ℓ + 1, _, .mk _ d, h => TS.below_drop ℓ (GenS.unf h).2

/-- A drop at level `ℓ`, which must dispose of everything, owns places only up to level `ℓ`. -/
theorem TS.below_drop (ℓ : Nat) {O : Own} {d : KF (St ℓ) Unit}
    (h : TS (VSt ℓ) ℓ (fun O' (_ : Unit) => O' = 0) O d) : Below (ℓ + 1) O := by
  induction h with
  | ret hx => subst hx; exact fun _ _ _ => rfl
  | out _ ih => exact ih
  | acq _ ih => exact (ih 0).left
  | free _ ih => exact ih.add Below.res
  | pnew hv _ ih => exact (ih 0).left.add ((VSt.below ℓ hv).mono (Nat.le_succ ℓ))
  | pnext _ _ ih => exact ih none
  | pdrop _ ih => exact ih.add Below.pl
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
   fun _ _ h => (by cases h), fun _ h => (by cases h)⟩

/-- The level of a place's state, `0` when free. -/
def PSt.lvl : PSt → Nat
  | .live L _ => L
  | .busy L => L
  | .free => 0

theorem PSt.at_lvl {p : PSt} {L : Nat} (h : p.at L = true) : p.lvl = L := by
  cases p <;> simp [PSt.at, PSt.lvl] at h ⊢ <;> exact h

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
  have key : ∀ n ℓ, lvlBound w w.next ≤ ℓ + n → ∀ c, (w.pl c).at ℓ = false := by
    intro n
    induction n with
    | zero =>
        intro ℓ hℓ c
        cases hat : (w.pl c).at ℓ
        · rfl
        · have hlv := PSt.at_lvl hat
          have hc : c < w.next := h.lt_next (fun e => by rw [e] at hat; cases hat)
          have := lt_lvlBound w w.next c hc
          omega
    | succ n ih =>
        intro ℓ hℓ c
        cases hat : (w.pl c).at ℓ
        · rfl
        · exfalso
          have hacct := congrFun h.acct (.pl ℓ c)
          simp only [Own.add_apply, Own.zero_apply, Nat.zero_add, phys, hat] at hacct
          obtain ⟨c₂, -, hc₂⟩ := tot_pos w.next (show tot Ov w.next (.pl ℓ c) ≠ 0 by
            rw [hacct]; decide)
          have hcont := h.cont c₂
          generalize hp₂ : w.pl c₂ = p₂ at hcont
          cases p₂ with
          | free => rw [hcont] at hc₂; exact hc₂ rfl
          | busy _ => rw [hcont] at hc₂; exact hc₂ rfl
          | live ℓ₂ v₂ =>
              have hlt : ℓ < ℓ₂ := Nat.lt_of_not_le (fun hle => hc₂ (VSt.below ℓ₂ hcont ℓ c hle))
              have := ih ℓ₂ (by omega) c₂
              rw [hp₂] at this; simp [PSt.at] at this
  have hfree : ∀ c, w.pl c = .free := fun c => by
    have := key 0 ((w.pl c).lvl + lvlBound w w.next) (by omega) c
    have h2 := key (lvlBound w w.next) (w.pl c).lvl (by omega) c
    cases e : w.pl c with
    | free => rfl
    | live L v => rw [e] at h2; simp [PSt.at, PSt.lvl] at h2
    | busy L => rw [e] at h2; simp [PSt.at, PSt.lvl] at h2
  refine ⟨hfree, fun r => ?_⟩
  have hz : tot Ov w.next = 0 := tot_zero (fun c => h.ov_free (fun L v e => by
    rw [hfree c] at e; cases e)) w.next
  have := congrFun h.acct (.res r)
  simp only [Own.add_apply, Own.zero_apply, hz, phys] at this
  cases e : w.res r with
  | none => rfl
  | some _ => rw [e] at this; simp at this

/-- **Safety of the cell model.** A safe closed tree at any level, owning nothing at the start
and required to own nothing at the end, runs to an answer from the empty world: it never gets
stuck (no free of a dead resource, no resume or drop of a dead or busy place), and at the end
every resource has been freed and every place dropped, including the places that contents
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
