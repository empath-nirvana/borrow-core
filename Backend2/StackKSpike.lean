import Backend2.Lint
import Backend2.Convert

/-!
# Backend2 — spike: a type for a stack machine's level `k` that does not own its frame (#746)

The question: can the `k` a stack machine's step receives (`k'`, `genStackMach`'s `stack step`)
and the one a point's `mk` receives (`kv`) be typed so that a drop rule read on the type alone
(`Lint.dropsAt`, every rule but `stackK`) admits their drop?

What this file states, each by Lean:
- every drop rule but `stackK` reads the type and nothing else (`dropsAt_type_only`);
- a suspension's `k` is at `OutInfo.kTy`, one type for every receiver of the machine's outcome
  (`sPay_kTy`): the step of a level and the stored BOXED-κ site at the base both receive a summand
  of `F.sPay`;
- no rule but `stackK` admits a drop at `kTy` (`kTy_no_type_rule`);
- an existing type that a rule does drop, a borrow of a cell holding the closure
  (`.mut (kTy …)`, the rule `forget`), is at hand (`mut_kTy_forget`);
- `StackKTypeLicence`, the obstruction: a type-read rule admitting the level's `k` admits every
  variable at `kTy`, the site's `κ`'s `k` among them (`licence_drops_site_k`), which the kernel
  types as must-resume or cancellable.
-/

namespace Backend2.StackKSpike
open Backend2

/-- Every drop rule but `stackK` reads the variable's type alone: not the variable, not the
program. -/
theorem dropsAt_type_only {r : DropRule} (hr : r ≠ .stackK) (p q : Prog) (x y : Var) (t : LTy) :
    Lint.dropsAt p x r t = Lint.dropsAt q y r t := by
  cases r <;> simp_all [Lint.dropsAt]

/-- A suspension's summand at the machine operation `(key, a, b, cp)` holds the argument and a `k`
at `F.kTy b cp`. The step's `k'` and a stored site's `k` are both read off `F.sPay`. -/
theorem sPay_kTy (F : OutInfo) {key : Key} {a b : LTy} {cp : Option Pay}
    (h : (key, a, b, cp) ∈ F.ms) : (key, LTy.pair a (F.kTy b cp)) ∈ F.sPay :=
  List.mem_map.mpr ⟨_, h, rfl⟩

/-- No rule but `stackK` admits a drop at a suspended computation's type. -/
theorem kTy_no_type_rule (F : OutInfo) (b : LTy) (cp : Option Pay) {r : DropRule}
    (hr : r ≠ .stackK) (p : Prog) (x : Var) : Lint.dropsAt p x r (F.kTy b cp) = false := by
  cases r <;> simp_all [Lint.dropsAt, OutInfo.kTy, LTy.persistent, LTy.unbang, LCTy.unbang]

/-- The existing borrow at a closure type: a `mut` borrow of a cell holding `k` is dropped at the
rule `forget`. Typing the level's `k` so needs the cell it borrows, owned by something else. -/
theorem mut_kTy_forget (F : OutInfo) (b : LTy) (cp : Option Pay) (p : Prog) (x : Var) :
    Lint.dropsAt p x .forget (.mut (F.kTy b cp)) = true := by
  simp [Lint.dropsAt, LTy.unbang]

/-- **The obstruction.** A drop rule read on the type that admits a level's `k` at the type a
suspension carries it at (`F.kTy`, `sPay_kTy`). -/
def StackKTypeLicence : Prop :=
  ∃ r : DropRule, r ≠ .stackK ∧ ∀ (F : OutInfo) (b : LTy) (cp : Option Pay),
    ∃ (p : Prog) (x : Var), Lint.dropsAt p x r (F.kTy b cp) = true

/-- Such a rule admits the drop of every variable of every program at `F.kTy`: the stored
site's `κ`'s `k`, received at the same summand of `F.sPay`, among them. -/
theorem licence_drops_site_k (h : StackKTypeLicence) :
    ∃ r : DropRule, r ≠ .stackK ∧ ∀ (F : OutInfo) (b : LTy) (cp : Option Pay) (q : Prog) (y : Var),
      Lint.dropsAt q y r (F.kTy b cp) = true := by
  obtain ⟨r, hr, hl⟩ := h
  refine ⟨r, hr, fun F b cp q y => ?_⟩
  obtain ⟨p, x, hx⟩ := hl F b cp
  rw [dropsAt_type_only hr q p y x]; exact hx

/-- And no existing rule is one: `StackKTypeLicence` fails for the rules on main. -/
theorem no_licence_today : ¬ StackKTypeLicence := by
  rintro ⟨r, hr, hl⟩
  obtain ⟨p, x, hx⟩ := hl { ty := .unit, r := .unit, pay := [], ms := [] } .unit none
  rw [kTy_no_type_rule _ _ _ hr] at hx; cases hx

end Backend2.StackKSpike
