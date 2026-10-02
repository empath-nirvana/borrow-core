import EffModelRel.Cell

/-!
# EffModelRel — the cell model at work: a generator across yields, and T1

- **A generator holding a resource across its yields** (`ownProg`): created owning the resource,
  stored in a place, resumed twice, dropped; the drop frees the resource. Safe
  (`ownProg_safe`), and its run is computed (`ownProg_run`).
- **T1 as bookkeeping** (`borProg`, `harmProg`). A resource is lent, and the borrow is captured by a
  generator stored in a place: the place's return set names the borrow, so the place must be
  dropped, giving the borrow back, before the loan ends (`reclaim`), and only then may the owner
  free the resource. `borProg` keeps that order and is safe (`borProg_safe`). `harmProg` frees
  the resource while the generator still holds the borrow, then resumes it: the run is stuck
  (`harmProg_stuck`), so no safety derivation exists (`harmProg_not_safe`). The continuation
  holding the borrow is bounded by the loan because what it holds must be given back, and that
  is the place's drop.
-/

namespace EffCell

theorem TS.cast {St' : Type} {V : List Nat → Own → St' → Prop} {lvl : Nat} {X : Type}
    {P : Own → X → Prop} {O O' : Own} {t : KF St' X} (h : O = O') (ht : TS V lvl P O t) :
    TS V lvl P O' t := h ▸ ht

/-! ## A generator holding a resource across its yields -/

def og0 (r : Nat) : Gen (St 0) := .mk (.free r (.ret none)) (.free r (.ret ()))
def og1 (r : Nat) : Gen (St 0) := .mk (.ret (some (2, og0 r))) (.free r (.ret ()))
def og2 (r : Nat) : Gen (St 0) := .mk (.ret (some (1, og1 r))) (.free r (.ret ()))

/-- Acquire, store the generator owning the resource, resume it twice, drop it. -/
def ownProg : KF (St 1) (Option Int × Option Int) :=
  .acq 7 (fun r => .pnew [] (og2 r) (fun c => .pnext c (fun a => .pnext c (fun b =>
    .pdrop c (.ret (a, b))))))

theorem ownProg_run : (runK 1 ownProg Wd.init).map (fun p => (p.1, p.2.trace.reverse)) =
    some ((some 1, some 2), [.acq 7, .mk, .free 7, .fin]) := by decide

theorem og_safe (r : Nat) : VSt 1 [] (Own.one (.res r)) (og2 r) := by
  have hdrop : TS (VSt 0) 0 (fun O' (_ : Unit) => O' = useOf []) (Own.one (.res r))
      (.free r (.ret ())) :=
    TS.cast (Own.zero_add _) (.free (.ret rfl))
  have h0 : GenS (VSt 0) 0 [] (Own.one (.res r)) (og0 r) :=
    GenS.intro (TS.cast (Own.zero_add _) (.free (.ret rfl))) hdrop
  have h1 : GenS (VSt 0) 0 [] (Own.one (.res r)) (og1 r) := GenS.intro (.ret h0) hdrop
  exact GenS.intro (.ret h1) hdrop

theorem ownProg_safe : TS (VSt 1) 1 (fun O _ => O = 0) 0 ownProg := by
  refine .acq (fun r => ?_)
  refine TS.cast (O := 0 + Own.one (.res r)) rfl (.pnew (O := 0) (og_safe r) (fun c => ?_))
  refine .pnext (B := []) (by simp) (fun a => .pnext (B := []) (by simp) (fun b => ?_))
  exact TS.cast (O := 0 + Own.one (.pl 1 c [])) rfl (.pdrop (.ret (by simp [useOf])))

/-- By `cell_safety`: the run ends with nothing live. -/
example : ∃ x w', runK 1 ownProg Wd.init = some (x, w') ∧ (∀ c, w'.pl c = .free) ∧
    (∀ r, w'.res r = none) := cell_safety 1 ownProg ownProg_safe

/-! ## T1: a generator holding a borrow -/

/-- A generator that uses the borrowed resource once, and holds the borrow until it is given
back. -/
def bg0 : Gen (St 0) := .mk (.ret none) (.ret ())
def bg1 (r : Nat) : Gen (St 0) := .mk (.touch r (.ret (some (1, bg0)))) (.ret ())

/-- Acquire; lend; store the generator, which captures the borrow; resume it; drop it (the borrow
comes back); end the loan; free. -/
def borProg : KF (St 1) (Option Int) :=
  .acq 7 (fun r => .lend r (.pnew [r] (bg1 r) (fun c => .pnext c (fun a =>
    .pdrop c (.reclaim r (.free r (.ret a)))))))

/-- The harm: free the resource while the generator still holds its borrow, then resume it. -/
def harmProg : KF (St 1) (Option Int) :=
  .acq 7 (fun r => .lend r (.pnew [r] (bg1 r) (fun c => .free r (.pnext c (fun a =>
    .pdrop c (.ret a))))))

theorem borProg_run : (runK 1 borProg Wd.init).map (fun p => (p.1, p.2.trace.reverse)) =
    some (some 1, [.acq 7, .mk, .touch 7, .fin, .free 7]) := by decide

theorem harmProg_stuck : runK 1 harmProg Wd.init = none := by decide

theorem bg_safe (r : Nat) : VSt 1 [r] (Own.one (.use r)) (bg1 r) := by
  have hu : Own.one (.use r) = useOf [r] := (Own.zero_add _).symm
  have h0 : GenS (VSt 0) 0 [r] (Own.one (.use r)) bg0 :=
    GenS.intro (.ret hu) (.ret hu)
  exact GenS.intro (.touch (.inr (by simp)) (.ret h0)) (.ret hu)

theorem borProg_safe : TS (VSt 1) 1 (fun O _ => O = 0) 0 borProg := by
  refine .acq (fun r => ?_)
  refine TS.cast (O := 0 + Own.one (.res r)) rfl (.lend ?_)
  refine TS.cast (O := (0 + Own.one (.rsv r)) + Own.one (.use r)) rfl
    (.pnew (bg_safe r) (fun c => ?_))
  refine .pnext (B := [r]) (by simp) (fun a => ?_)
  refine .pdrop ?_
  refine TS.cast (O := 0 + Own.one (.rsv r) + Own.one (.use r)) ?_ (.reclaim ?_)
  · show 0 + Own.one (.rsv r) + Own.one (.use r) = 0 + Own.one (.rsv r) + (useOf [] + Own.one (.use r))
    simp [useOf]
  · exact .free (.ret rfl)

/-- **T1, refused.** No safety derivation exists for the program that frees a resource while a
stored continuation holds its borrow. -/
theorem harmProg_not_safe : ¬ TS (VSt 1) 1 (fun O _ => O = 0) 0 harmProg := fun h => by
  obtain ⟨x, w', hr, -⟩ := cell_safety 1 harmProg h
  rw [harmProg_stuck] at hr; cases hr

end EffCell
