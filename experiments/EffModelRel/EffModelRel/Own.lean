import EffModelRel.Examples

/-!
# EffModelRel — ownership, and safe trees

Unary resource safety is stated with **tokens**. A `using` frame's resource and an owned
capability are tokens; a computation owns a multiset of them. The tree predicate `TS` says what a
tree does with what it owns:

- acquiring and creating add a token; freeing and consuming remove one; reading and writing a
  cell need its token. A resource handle is second class: its frame owns it, and `use` checks
  nothing;
- an operation's continuation keeps everything owned. If a handler may drop it (`q.w`), its
  destructors `d` must free exactly what it owns (`DropOK`); if a handler may copy it (`q.c`),
  it must own nothing;
- an abort drops its continuation: its destructors free exactly what it owns.

`Safe` runs a tree against the world with a ghost multiset of live tokens: every free, use,
read and consume finds its token, and a run that returns has the tokens its answer accounts for.
For a closed program of ground type that is nothing: no leak, and every finaliser ran once.
-/

namespace EffRel

variable {S : Sig}

inductive Kind where
  | res
  | cap (g : G)
deriving DecidableEq

/-- Ownership: how many tokens of each kind for each name. -/
def Own : Type := Kind → Nat → Nat

namespace Own
def zero : Own := fun _ _ => 0
def add (a b : Own) : Own := fun k n => a k n + b k n
def one (k : Kind) (n : Nat) : Own := fun k' n' => if k' = k ∧ n' = n then 1 else 0
instance : Add Own := ⟨add⟩
instance : OfNat Own 0 := ⟨zero⟩

@[simp] theorem add_apply (a b : Own) (k n) : (a + b) k n = a k n + b k n := rfl
@[simp] theorem zero_apply (k n) : (0 : Own) k n = 0 := rfl

theorem ext {a b : Own} (h : ∀ k n, a k n = b k n) : a = b := funext fun k => funext fun n => h k n

theorem add_comm (a b : Own) : a + b = b + a := ext fun _ _ => Nat.add_comm _ _
theorem add_assoc (a b c : Own) : a + b + c = a + (b + c) := ext fun _ _ => Nat.add_assoc _ _ _
@[simp] theorem zero_add (a : Own) : 0 + a = a := ext fun _ _ => Nat.zero_add _
@[simp] theorem add_zero (a : Own) : a + 0 = a := ext fun _ _ => Nat.add_zero _

theorem add_eq_zero {a b : Own} (h : a + b = 0) : a = 0 ∧ b = 0 :=
  ⟨ext fun k n => by have := congrFun (congrFun h k) n; simp at this ⊢; omega,
   ext fun k n => by have := congrFun (congrFun h k) n; simp at this ⊢; omega⟩

theorem one_ne_zero (k : Kind) (n : Nat) : (one k n) k n ≠ 0 := by simp [one]

theorem add_right_cancel {a b c : Own} (h : a + c = b + c) : a = b :=
  ext fun k n => by have := congrFun (congrFun h k) n; simp at this; omega

theorem add_left_cancel {a b c : Own} (h : c + a = c + b) : a = b :=
  ext fun k n => by have := congrFun (congrFun h k) n; simp at this; omega
end Own

/-! ## Destructors, cancels, actions -/

/-- Running these destructors frees exactly what is owned. -/
inductive DropOK : Own → List Dtor → Prop where
  | nil : DropOK 0 []
  | free : DropOK O d → DropOK (O + Own.one .res r) (.free ℓ r :: d)

/-- What a continuation captured at an operation of qualifier `q` may own. -/
def CancelOK (q : Mode) (O : Own) (d : List Dtor) : Prop :=
  (q.c = true → O = 0 ∧ d = []) ∧ (q.w = true → DropOK O d)

/-- An action's effect on ownership. Allocation is the `nuAcq`/`nuNew` constructors of `TS`. -/
inductive ActOK : {g : G} → Act g → Own → Own → Prop where
  | out {n : Int} {O : Own} : ActOK (.out n) O O
  | free {ℓ r : Nat} {O : Own} : ActOK (.free ℓ r) (O + Own.one .res r) O
  | use {ℓ r : Nat} {O : Own} : ActOK (.use ℓ r) O O
  | kill {c : Nat} {g : G} {O : Own} : ActOK (.kill c g) (O + Own.one (.cap g) c) O
  | rd {c : Nat} {g : G} {O : Own} : O (.cap g) c ≠ 0 → ActOK (.rd c g) O O
  | wr {c : Nat} {g : G} {v : g.den} {O : Own} : O (.cap g) c ≠ 0 → ActOK (.wr c ⟨g, v⟩) O O

/-- **Safe trees.** `bnd` bounds the qualifier of every operation the tree performs, by instance
and effect; `P` is what the leaf's value and the remaining tokens must satisfy. -/
inductive TS (bnd : Nat → S.E → Mode) (P : Own → X → Prop) : Own → Tree S X → Prop where
  | ret : P O x → TS bnd P O (.ret x)
  | op {i : Nat} {e : S.E} {o : S.O e} {v : (S.arg e o).den}
      {k : (S.res e o).den → Tree S X} {d : List Dtor} :
      (bnd i e).ge (S.q e o) = true → CancelOK (S.q e o) O d → (∀ y, TS bnd P O (k y)) →
      TS bnd P O (.op i e o v k d)
  | ab {i : Nat} {e : S.E} {a : S.A e} {v : (S.aarg e a).den} {d : List Dtor} :
      (bnd i e).ge Mode.aff = true → DropOK O d → TS bnd P O (.ab i e a v d)
  | nu {k : Nat → Tree S X} : (∀ n, TS bnd P O (k n)) → TS bnd P O (.nu k)
  /-- A new capability: a fresh name and its token. -/
  | nuNew {s : Nat → GVal} {k : Nat → Unit → Tree S X} :
      (∀ n y, TS bnd P (O + Own.one (.cap (s n).1) n) (k n y)) →
      TS bnd P O (.nu (fun n => .act (.new n (s n)) (k n)))
  /-- A new resource: a fresh name and its token. -/
  | nuAcq {ℓ : Nat} {k : Nat → Unit → Tree S X} :
      (∀ n y, TS bnd P (O + Own.one .res n) (k n y)) →
      TS bnd P O (.nu (fun n => .act (.acq ℓ n) (k n)))
  | act {g : G} {a : Act g} {k : g.den → Tree S X} {O' : Own} :
      ActOK a O O' → (∀ y, TS bnd P O' (k y)) → TS bnd P O (.act a k)

/-! ## Running safely: the ghost run -/

/-- The world and the live tokens. -/
structure SW where
  w : Wd
  live : Own

/-- An action, checked against the live tokens. -/
def Act.sexec : {g : G} → Act g → SW → Option (g.den × SW)
  | _, .out n, ⟨w, L⟩ => some ((), ⟨w.emit (.out n), L⟩)
  | _, .acq ℓ r, ⟨w, L⟩ => some ((), ⟨w.emit (.acq ℓ), L + Own.one .res r⟩)
  | _, .free ℓ r, ⟨w, L⟩ =>
      if L .res r = 0 then none else some ((), ⟨w.emit (.free ℓ), fun k n =>
        if k = .res ∧ n = r then L k n - 1 else L k n⟩)
  | _, .use ℓ _, ⟨w, L⟩ => some ((), ⟨w.emit (.use ℓ), L⟩)
  | _, .new c s, ⟨w, L⟩ => some ((), ⟨(w.set c (some s)).emit .mk, L + Own.one (.cap s.1) c⟩)
  | _, .rd c g, ⟨w, L⟩ =>
      if L (.cap g) c = 0 then none else (w.get c g).map (fun v => (v, ⟨w, L⟩))
  | _, .wr c s, ⟨w, L⟩ =>
      if L (.cap s.1) c = 0 then none else (w.store c).map (fun _ => ((), ⟨w.set c (some s), L⟩))
  | _, .kill c g, ⟨w, L⟩ =>
      if L (.cap g) c = 0 then none else (w.get c g).map (fun v => (v, ⟨(w.set c none).emit .fin,
        fun k n => if k = .cap g ∧ n = c then L k n - 1 else L k n⟩))

/-- A run that never fails an action; if it returns, its answer and live tokens satisfy `P`. An
operation that reaches the top is not this predicate's business (see `docs/effect-model.md`). -/
def Tree.Safe (P : Own → X → Prop) : Tree S X → SW → Prop
  | .ret x, s => P s.live x
  | .op .., _ => True
  | .ab .., _ => True
  | .nu k, s => (k s.w.next).Safe P ⟨{ s.w with next := s.w.next + 1 }, s.live⟩
  | .act a k, s =>
      match a.sexec s with
      | none => False
      | some (y, s') => (k y).Safe P s'

/-! ## Adequacy: safe trees run safely -/

/-- The run's invariant: the live tokens are the tree's; every capability token names a live
cell of its type, at most once; names not yet allocated carry nothing. -/
structure SInv (O : Own) (s : SW) : Prop where
  live : s.live = O
  cell : ∀ g c, O (.cap g) c ≠ 0 → O (.cap g) c = 1 ∧ ∃ v, s.w.store c = some ⟨g, v⟩
  fresh : ∀ k n, s.w.next ≤ n → O k n = 0 ∧ s.w.store n = none

theorem Own.sub_one {O' : Own} {k : Kind} {r : Nat} :
    (fun k' n => if k' = k ∧ n = r then (O' + Own.one k r) k' n - 1 else (O' + Own.one k r) k' n) = O' :=
  funext fun k' => funext fun n => by
    by_cases h : k' = k ∧ n = r
    · rw [if_pos h]; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; simp [Own.one]
    · rw [if_neg h]; simp [Own.one, h]

theorem Wd.get_some {w : Wd} {c : Nat} {g : G} {v : g.den} (h : w.store c = some ⟨g, v⟩) :
    w.get c g = some v := by simp [Wd.get, h]

theorem adequacyU {bnd : Nat → S.E → Mode} {P : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS bnd P O t) : ∀ s, SInv O s → t.Safe P s := by
  induction h with
  | ret hx => intro s hs; simp only [Tree.Safe]; rw [hs.live]; exact hx
  | op => intro _ _; trivial
  | ab => intro _ _; trivial
  | @nu O k _ ih =>
      intro s hs
      apply ih
      exact ⟨hs.live, hs.cell, fun k' n hn => hs.fresh k' n (by simp at hn; omega)⟩
  | @nuNew O sf k _ ih =>
      intro s hs
      simp only [Tree.Safe, Act.sexec]
      have hf := hs.fresh
      apply ih
      refine ⟨by simp [hs.live], fun g c hc => ?_, fun k' n hn => ?_⟩
      · by_cases hcN : c = s.w.next
        · subst hcN
          have h0 : ∀ g', O (.cap g') s.w.next = 0 := fun g' => (hf _ _ (Nat.le_refl _)).1
          have hg : g = (sf s.w.next).1 := by
            by_cases hne : g = (sf s.w.next).1
            · exact hne
            · exfalso; apply hc; simp [Own.one, h0, hne]
          subst hg
          exact ⟨by simp [Own.one, h0], (sf s.w.next).2, by simp [Wd.emit, Wd.set]⟩
        · have hc' : O (.cap g) c ≠ 0 := by simpa [Own.one, hcN] using hc
          obtain ⟨h1, v, hv⟩ := hs.cell g c hc'
          exact ⟨by simpa [Own.one, hcN] using h1, v, by simp [Wd.emit, Wd.set, hcN, hv]⟩
      · simp only [Wd.emit, Wd.set] at hn
        have h1 := hf k' n (by omega)
        have hne : n ≠ s.w.next := by omega
        refine ⟨by simp [Own.one, h1.1, hne], by simp [Wd.emit, Wd.set, hne, h1.2]⟩
  | @nuAcq O ℓ k _ ih =>
      intro s hs
      simp only [Tree.Safe, Act.sexec]
      have hf := hs.fresh
      apply ih
      refine ⟨by simp [hs.live], fun g c hc => ?_, fun k' n hn => ?_⟩
      · have hc' : O (.cap g) c ≠ 0 := by simpa [Own.one] using hc
        obtain ⟨h1, v, hv⟩ := hs.cell g c hc'
        exact ⟨by simpa [Own.one] using h1, v, by simpa [Wd.emit] using hv⟩
      · simp only [Wd.emit] at hn
        have h1 := hf k' n (by omega)
        have hne : n ≠ s.w.next := by omega
        exact ⟨by simp [Own.one, h1.1, hne], by simpa [Wd.emit] using h1.2⟩
  | @act O g a k O' ha _ ih =>
      intro s hs
      obtain ⟨w, L⟩ := s
      obtain ⟨hl, hc, hf⟩ := hs
      simp only at hl hc hf; subst hl
      cases ha with
      | out => exact ih () _ ⟨rfl, hc, hf⟩
      | @free ℓ r _ =>
          simp only [Tree.Safe, Act.sexec]
          have : (O' + Own.one .res r) .res r ≠ 0 := by simp [Own.one]
          rw [if_neg this]
          refine ih () _ ⟨Own.sub_one, fun g c h0 => ?_, fun k' n hn => ?_⟩
          · obtain ⟨h1, v, hv⟩ := hc g c (by simpa [Own.one] using h0)
            exact ⟨by simpa [Own.one] using h1, v, by simpa [Wd.emit] using hv⟩
          · have := hf k' n (by simpa [Wd.emit] using hn)
            exact ⟨by have h2 := this.1; simp [Own.one] at h2; exact h2.1, by simpa [Wd.emit] using this.2⟩
      | @use ℓ r _ =>
          simp only [Tree.Safe, Act.sexec]
          exact ih () _ ⟨rfl, hc, fun k' n hn => by simpa [Wd.emit] using hf k' n (by simpa [Wd.emit] using hn)⟩
      | @kill c g _ =>
          simp only [Tree.Safe, Act.sexec]
          have hc0 : (O' + Own.one (.cap g) c) (.cap g) c ≠ 0 := by simp [Own.one]
          rw [if_neg hc0]
          obtain ⟨h1, v, hv⟩ := hc g c hc0
          rw [Wd.get_some hv]
          simp only [Option.map_some]
          refine ih v _ ⟨Own.sub_one, fun g' c' h0 => ?_, fun k' n hn => ?_⟩
          · have hO : (O' + Own.one (.cap g) c) (.cap g') c' ≠ 0 := by
              simp [Own.one]; intro h; exact absurd h h0
            obtain ⟨h2, v', hv'⟩ := hc g' c' hO
            have hne : ¬ (g' = g ∧ c' = c) := by
              rintro ⟨rfl, rfl⟩; simp [Own.one] at h1; exact h0 h1
            refine ⟨by simpa [Own.one, hne] using h2, v', ?_⟩
            have : c' ≠ c := by
              intro hcc; subst hcc
              have : g' = g := by rw [hv] at hv'; cases hv'; rfl
              exact hne ⟨this, rfl⟩
            simp [Wd.emit, Wd.set, this, hv']
          · simp only [Wd.emit, Wd.set] at hn
            have := hf k' n hn
            refine ⟨by have h2 := this.1; simp [Own.one] at h2; exact h2.1, ?_⟩
            have : n ≠ c := by
              intro hnc; subst hnc; have := (hf (.cap g) _ hn).1; simp [Own.one] at this
            simp [Wd.emit, Wd.set, this, (hf k' n hn).2]
      | @rd c g _ hr =>
          simp only [Tree.Safe, Act.sexec]; rw [if_neg hr]
          obtain ⟨_, v, hv⟩ := hc g c hr
          rw [Wd.get_some hv]
          exact ih v _ ⟨rfl, hc, hf⟩
      | @wr c g v _ hr =>
          simp only [Tree.Safe, Act.sexec]; rw [if_neg hr]
          obtain ⟨_, v', hv⟩ := hc g c hr
          rw [hv]; simp only [Option.map_some]
          refine ih () _ ⟨rfl, fun g' c' h0 => ?_, fun k' n hn => ?_⟩
          · obtain ⟨h2, v'', hv''⟩ := hc g' c' h0
            refine ⟨h2, ?_⟩
            by_cases hcc : c' = c
            · subst hcc; rw [hv] at hv''; cases hv''; exact ⟨v, by simp [Wd.set]⟩
            · exact ⟨v'', by simp [Wd.set, hcc, hv'']⟩
          · have : n ≠ c := by intro hnc; subst hnc; exact hr (hf (.cap g) _ hn).1
            exact ⟨(hf k' n hn).1, by simp [Wd.set, this, (hf k' n hn).2]⟩

end EffRel
