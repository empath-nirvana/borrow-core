import Core.ClauseNames
import Core.RaiseNames

/-!
# Core — the frames a handled computation may hold  `[spec §19]`

Condition 2 of the direct call of a tail-resumptive clause (`docs/effect-lowering.md` §2.3) is
`UnhandledIn Σ K` (`Core/ClauseNames.lean`): no frame of the continuation `K` between a
`perform` and its handler catches a name of the clause's row `Σ`. This file gives the frames
`K` may hold, as a fact of the term the program runs.

* `HIn` is a set of frames by what they catch: the names of handler frames, whether a finaliser
  (`ubind`, `cfin`, which catch every raise), and whether a handler frame whose name is not a
  literal (which may be of any name). A cancel delimiter `ccatch` catches the name `0`.
* `Expr.hin e` is every frame `e` holds, anywhere in it: at a `handle` node's handled
  computation, the record of the names handled inside it.
* `Expr.pn e` is the names `e` may perform: a handler frame is captured into a continuation only
  by an operation of its name.
* `Expr.fl e` is what may **flow**: the frames of the code a value of `e` holds (the body of a
  `λ` that is not applied in place), and the frames of every handled computation (a continuation
  captures them). A `λ` applied in place, `(λx. N) M` (a `let`), runs where it stands, and its
  body counts as the code around it.
* `flows e₀` is `e₀.fl`, the names a run may perform (`performed e₀`: `e₀.pn` and `Div`'s, which a
  loop performs), the name of a handler frame a continuation captures being among them, and `0`,
  whose `ccatch` every continuation's cancel holds.

**The flow invariant** (`steps_flowInv`, `steps_flows`): in a run of `e₀` from a memory that holds
no code, what flows from every configuration and every value of its memory is within `flows e₀`,
and what they perform within `performed e₀`. A head step keeps a term's flow, frames and names
performed within a bound holding its redex's and the values it reads (`head_fl`, `head_hin`,
`head_pn`), and a context keeps them (`plug_le`, `plug_pn_le`).

**The run invariant** (`steps_frame_of_node`): every handler frame a run reaches has the name of a
handle node of `e₀`, or `0`, or `e₀` holds a handler whose name is not a literal. Its proof is the
same argument at `hin` (`steps_hin`).

**The theorem** (`steps_unhandledIn`): at every configuration of such a run that holds
`hnd H K[p]`, `K`'s frames are within `flows e₀`, so a row `Σ` none of whose names `flows e₀` may
catch is unhandled in `K`.
-/

namespace BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Heap Head Step1 Steps hndE performE)

/-! ### Sets of frames -/

/-- **A set of frames, by what they catch**: the names of handler frames; whether a finaliser
(`ubind`, `cfin`), which catches every raise; whether a handler frame whose name is not a literal,
which may be of any name.  `[spec §19]` -/
structure HIn where
  names : List UInt32 := []
  fin : Bool := false
  any : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace HIn

instance : Append HIn := ⟨fun a b => ⟨a.names ++ b.names, a.fin || b.fin, a.any || b.any⟩⟩

@[simp] theorem names_append (a b : HIn) : (a ++ b).names = a.names ++ b.names := rfl
@[simp] theorem fin_append (a b : HIn) : (a ++ b).fin = (a.fin || b.fin) := rfl
@[simp] theorem any_append (a b : HIn) : (a ++ b).any = (a.any || b.any) := rfl

/-- The one handler frame of the name `m`. -/
def one (m : UInt32) : HIn := ⟨[m], false, false⟩

/-- A frame of any name. -/
def top : HIn := ⟨[], false, true⟩

/-- A finaliser. -/
def final : HIn := ⟨[], true, false⟩

/-- `a` within `b`: every frame of `a` is one `b` allows. -/
def Le (a b : HIn) : Prop :=
  (a.any = true → b.any = true) ∧ (a.fin = true → b.fin = true ∨ b.any = true) ∧
    ∀ m ∈ a.names, m ∈ b.names ∨ b.any = true

instance : LE HIn := ⟨Le⟩

/-- **May catch a raise of `m`**: a handler frame of `m`, a finaliser, or a frame of any name. -/
def Catches (h : HIn) (m : UInt32) : Prop := m ∈ h.names ∨ h.fin = true ∨ h.any = true

/-- **May hold a handler frame of `m`**. -/
def HasHnd (h : HIn) (m : UInt32) : Prop := m ∈ h.names ∨ h.any = true

theorem le_refl (a : HIn) : a ≤ a := ⟨id, .inl, fun _ h => .inl h⟩

theorem le_trans {a b c : HIn} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  obtain ⟨a₁, a₂, a₃⟩ := h₁
  obtain ⟨b₁, b₂, b₃⟩ := h₂
  refine ⟨fun h => b₁ (a₁ h), fun h => ?_, fun m hm => ?_⟩
  · rcases a₂ h with h | h
    · exact b₂ h
    · exact .inr (b₁ h)
  · rcases a₃ m hm with h | h
    · exact b₃ m h
    · exact .inr (b₁ h)

theorem le_append_left (a b : HIn) : a ≤ a ++ b :=
  ⟨fun h => by simp [h], fun h => .inl (by simp [h]), fun m hm => .inl (by simp [hm])⟩

theorem le_append_right (a b : HIn) : b ≤ a ++ b :=
  ⟨fun h => by simp [h], fun h => .inl (by simp [h]), fun m hm => .inl (by simp [hm])⟩

theorem append_le {a b c : HIn} (h₁ : a ≤ c) (h₂ : b ≤ c) : a ++ b ≤ c := by
  obtain ⟨a₁, a₂, a₃⟩ := h₁
  obtain ⟨b₁, b₂, b₃⟩ := h₂
  refine ⟨fun h => ?_, fun h => ?_, fun m hm => ?_⟩
  · simp only [any_append, Bool.or_eq_true] at h
    rcases h with h | h
    · exact a₁ h
    · exact b₁ h
  · simp only [fin_append, Bool.or_eq_true] at h
    rcases h with h | h
    · exact a₂ h
    · exact b₂ h
  · simp only [names_append, List.mem_append] at hm
    rcases hm with h | h
    · exact a₃ m h
    · exact b₃ m h

theorem append_mono {a b c d : HIn} (h₁ : a ≤ c) (h₂ : b ≤ d) : a ++ b ≤ c ++ d :=
  append_le (le_trans h₁ (le_append_left _ _)) (le_trans h₂ (le_append_right _ _))

theorem empty_le (a : HIn) : ({} : HIn) ≤ a :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ h => by cases h⟩

/-- A set with a frame of any name allows every set. -/
theorem le_of_any {a b : HIn} (h : b.any = true) : a ≤ b :=
  ⟨fun _ => h, fun _ => .inr h, fun _ _ => .inr h⟩

theorem top_le_iff {b : HIn} : top ≤ b ↔ b.any = true :=
  ⟨fun h => h.1 rfl, fun h => le_of_any h⟩

theorem Catches.mono {a b : HIn} (h : a ≤ b) {m : UInt32} (hm : a.Catches m) : b.Catches m := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  rcases hm with hm | hm | hm
  · rcases h₃ m hm with h | h
    · exact .inl h
    · exact .inr (.inr h)
  · rcases h₂ hm with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · exact .inr (.inr (h₁ hm))

theorem HasHnd.mono {a b : HIn} (h : a ≤ b) {m : UInt32} (hm : a.HasHnd m) : b.HasHnd m := by
  obtain ⟨h₁, -, h₃⟩ := h
  rcases hm with hm | hm
  · exact h₃ m hm
  · exact .inr (h₁ hm)

theorem Catches.one (m : UInt32) : (one m).Catches m := .inl (List.mem_singleton.mpr rfl)

/-- **May catch a raise of `m`**, decided. -/
def catchesB (h : HIn) (m : UInt32) : Bool := h.names.contains m || h.fin || h.any

theorem catchesB_iff {h : HIn} {m : UInt32} : h.catchesB m = true ↔ h.Catches m := by
  simp [catchesB, Catches, or_assoc]

end HIn

/-! ### The frames a term holds -/

/-- The frame a primitive is the head of: a handler (`hnd`, whose name is its argument's), a
finaliser (`ubind`, `cfin`), or a cancel delimiter (`ccatch`, of the name `0`). -/
def primHin : Prim → HIn
  | .hnd => HIn.top
  | .ubind | .cfin => HIn.final
  | .ccatch => HIn.one 0
  | _ => {}

/-- **The frames a term holds**, anywhere in it: a handler frame `hnd (m, …)` at a literal name
`m` is of `m`; any other occurrence of `hnd` may be a handler of any name; `ubind` and `cfin` are
finalisers, `ccatch` a cancel delimiter.  `[spec §19]` -/
def _root_.BoCa.Expr.hin : Expr → HIn
  | .var _ | .unit | .loc _ => {}
  | .prim p => primHin p
  | .pair a b | .seq a b | .letpair a b => a.hin ++ b.hin
  | .case a b c => a.hin ++ b.hin ++ c.hin
  | .inj₁ a | .inj₂ a | .lam a => a.hin
  | .app f x => match f, x with
      | .prim .hnd, .pair (.prim (.lit (.i32 m))) X => HIn.one m ++ X.hin
      | f, x => f.hin ++ x.hin

/-- `(m, X)`'s frames as a handler's name and the rest of its value: of the name `m` when it is a
literal, otherwise of any name. -/
def hndArg : Expr → HIn
  | .pair (.prim (.lit (.i32 m))) X => HIn.one m ++ X.hin
  | x => HIn.top ++ x.hin

/-- The term is the primitive `hnd`. -/
def isHnd : Expr → Bool
  | .prim .hnd => true
  | _ => false

theorem isHnd_iff {f : Expr} : isHnd f = true ↔ f = .prim .hnd := by
  constructor
  · intro h; unfold isHnd at h; split at h <;> simp_all
  · rintro rfl; rfl

theorem _root_.BoCa.Expr.hin_app (f x : Expr) :
    (Expr.app f x).hin = if isHnd f then hndArg x else f.hin ++ x.hin := by
  cases f <;> try rfl
  rename_i p
  cases p <;> try rfl
  cases x <;> try rfl
  rename_i a X
  cases a <;> try rfl
  rename_i q
  cases q <;> try rfl
  rename_i c
  cases c <;> rfl

/-- **What may flow from a term**: the frames of the code a value of it holds and of the
computations a continuation may capture. A `λ` holds its body's frames; a `λ` applied in place,
`(λx. N) M`, runs where it stands, and only what flows from `N` and `M` does; a handler frame
`hnd (m, …) M` holds what flows from its value and every frame of `M`, which a continuation
captured at it holds; the head `hnd (m, H)` of a handler frame holds what flows from `H`; a
finaliser frame and a cancel delimiter hold what flows from their parts. A primitive that heads a
frame may head one anywhere it is applied.  `[spec §19]` -/
def _root_.BoCa.Expr.fl : Expr → HIn
  | .var _ | .unit | .loc _ => {}
  | .prim p => primHin p
  | .lam b => b.hin
  | .pair a b | .seq a b | .letpair a b => a.fl ++ b.fl
  | .case a b c => a.fl ++ b.fl ++ c.fl
  | .inj₁ a | .inj₂ a => a.fl
  | .app f x => match f with
      | .lam b => b.fl ++ x.fl
      | .prim .hnd => match x with
          | .pair (.prim (.lit (.i32 _))) X => X.fl
          | x => HIn.top ++ x.fl
      | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) X) => X.fl ++ x.hin
      | .app (.prim .ubind) N => N.fl ++ x.fl
      | .app (.prim .cfin) s => s.fl ++ x.fl
      | .prim .ccatch => x.fl
      | f => f.fl ++ x.fl

namespace HIn

theorem append_assoc (a b c : HIn) : a ++ b ++ c = a ++ (b ++ c) := by
  show HIn.mk ((a.names ++ b.names) ++ c.names) ((a.fin || b.fin) || c.fin) ((a.any || b.any) || c.any)
    = HIn.mk (a.names ++ (b.names ++ c.names)) (a.fin || (b.fin || c.fin)) (a.any || (b.any || c.any))
  rw [List.append_assoc, Bool.or_assoc, Bool.or_assoc]

theorem le_append_of_le_left {a b c : HIn} (h : a ≤ b) : a ≤ b ++ c :=
  le_trans h (le_append_left _ _)

theorem le_append_of_le_right {a b c : HIn} (h : a ≤ c) : a ≤ b ++ c :=
  le_trans h (le_append_right _ _)

theorem top_le (a : HIn) : a ≤ top ++ a := le_append_right _ _

theorem le_top_append (a b : HIn) : a ≤ top ++ b := le_of_any (by simp [top])

end HIn

open HIn in
/-- **What flows is within the frames held**. -/
theorem fl_le_hin (e : Expr) : e.fl ≤ e.hin := by
  induction e using Expr.fl.induct with
  | case1 | case2 | case3 => exact empty_le _
  | case4 p => exact le_refl _
  | case5 b => exact le_refl _
  | case6 a b iha ihb | case7 a b iha ihb | case8 a b iha ihb =>
      exact append_mono iha ihb
  | case9 a b c iha ihb ihc => exact append_mono (append_mono iha ihb) ihc
  | case10 a ih | case11 a ih => exact ih
  | case12 x b ihb ihx => exact append_mono ihb ihx
  | case13 n X ih =>
      simp only [Expr.fl, Expr.hin]
      exact le_append_of_le_right ih
  | case14 x hx ih =>
      rw [Expr.hin_app]
      simp only [isHnd, if_true]
      rw [Expr.fl]
      · unfold hndArg
        split
        · exact absurd rfl (hx _ _)
        · exact append_mono (le_refl _) ih
      · exact hx
  | case15 x n X ihX =>
      simp only [Expr.fl, Expr.hin]
      exact append_mono (le_append_of_le_right ihX) (le_refl _)
  | case16 x N ihN ihx | case17 x N ihN ihx =>
      simp only [Expr.fl, Expr.hin]
      exact append_mono (le_append_of_le_right ihN) ihx
  | case18 x ihx =>
      simp only [Expr.fl, Expr.hin]
      exact le_append_of_le_right ihx
  | case19 x f h1 h2 h3 h4 h5 h6 ihf ihx =>
      rw [Expr.fl, Expr.hin_app]
      · rw [if_neg (fun h => h2 (isHnd_iff.mp h))]
        exact append_mono ihf ihx
      all_goals assumption

/-! ### Values, shifts and substitutions -/

/-- The term is a handler's head `hnd (m, X)` at a literal name. -/
def isHndLit : Expr → Bool
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) _) => true
  | _ => false

/-- The term is a literal name and a rest, `(m, X)`. -/
def isLitPair : Expr → Bool
  | .pair (.prim (.lit (.i32 _))) _ => true
  | _ => false

open HIn

/-- `hndArg` at a pair that is not a literal name and a rest: a frame of any name. -/
theorem hndArg_of_not {x : Expr} (h : isLitPair x = false) : hndArg x = HIn.top ++ x.hin := by
  unfold hndArg
  split
  · simp [isLitPair] at h
  · rfl

theorem hin_app_le (f x : Expr) : (Expr.app f x).hin ≤ f.hin ++ x.hin := by
  rw [Expr.hin_app]
  split
  · rename_i h
    rw [isHnd_iff.mp h]
    exact le_of_any (by simp [Expr.hin, primHin, top])
  · exact le_refl _

theorem hin_app_eq {f x : Expr} (h : isHnd f = false) : (Expr.app f x).hin = f.hin ++ x.hin := by
  rw [Expr.hin_app, if_neg (by simp [h])]

/-- A value's code is all of it that flows. -/
theorem _root_.BoCa.IsVal.hin_le_fl {v : Expr} (h : IsVal v) : v.hin ≤ v.fl := by
  induction h with
  | unit | loc | prim | lam => exact le_refl _
  | pair _ _ ih₁ ih₂ => exact append_mono ih₁ ih₂
  | inj₁ _ ih | inj₂ _ ih => exact ih
  | storeV _ ih =>
      show _ ++ _ ≤ _ ++ _
      exact append_mono (le_refl _) ih

theorem isLitPair_shift (x : Expr) (d c : Nat) : isLitPair (x.shift d c) = isLitPair x := by
  match x with
  | .var i => simp only [Expr.shift]; split <;> rfl
  | .pair (.var i) b => simp only [Expr.shift]; split <;> rfl
  | .pair (.prim p) b => cases p <;> try rfl
                         rename_i c; cases c <;> rfl
  | .pair .unit _ | .pair (.pair _ _) _ | .pair (.inj₁ _) _ | .pair (.inj₂ _) _ | .pair (.lam _) _
  | .pair (.loc _) _ | .pair (.seq _ _) _ | .pair (.letpair _ _) _ | .pair (.case _ _ _) _
  | .pair (.app _ _) _ => rfl
  | .unit | .inj₁ _ | .inj₂ _ | .lam _ | .loc _ | .prim _ | .seq _ _ | .letpair _ _ | .case _ _ _
  | .app _ _ => rfl

theorem isHnd_shift (f : Expr) (d c : Nat) : isHnd (f.shift d c) = isHnd f := by
  cases f <;> try rfl
  simp only [Expr.shift]; split <;> rfl

/-- **A shift keeps the frames held.** -/
theorem hin_shift (d : Nat) : ∀ (e : Expr) (c : Nat), (e.shift d c).hin = e.hin
  | .var i, c => by simp only [Expr.shift]; split <;> rfl
  | .unit, _ | .loc _, _ | .prim _, _ => rfl
  | .pair a b, c => by simp only [Expr.shift, Expr.hin, hin_shift d a, hin_shift d b]
  | .seq a b, c => by simp only [Expr.shift, Expr.hin, hin_shift d a, hin_shift d b]
  | .letpair a b, c => by simp only [Expr.shift, Expr.hin, hin_shift d a, hin_shift d b]
  | .case a b e, c => by
      simp only [Expr.shift, Expr.hin, hin_shift d a, hin_shift d b, hin_shift d e]
  | .inj₁ a, c => by simp only [Expr.shift, Expr.hin, hin_shift d a]
  | .inj₂ a, c => by simp only [Expr.shift, Expr.hin, hin_shift d a]
  | .lam a, c => by simp only [Expr.shift, Expr.hin, hin_shift d a]
  | .app f x, c => by
      simp only [Expr.shift]
      rw [Expr.hin_app, Expr.hin_app, isHnd_shift, hin_shift d f, hin_shift d x]
      split
      · cases hx : isLitPair x
        · rw [hndArg_of_not (by rw [isLitPair_shift]; exact hx), hndArg_of_not hx, hin_shift d x]
        · match x, hx with
          | .pair (.prim (.lit (.i32 m))) X, _ =>
              simp only [Expr.shift, hndArg, hin_shift d X]
      · rfl

theorem hin_shift_val (v : Val) (d c : Nat) : (v.shift d c).1.hin = v.1.hin :=
  hin_shift d v.1 c

theorem append_le_iff {a b c : HIn} : a ++ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
  ⟨fun h => ⟨le_trans (le_append_left a b) h, le_trans (le_append_right a b) h⟩,
    fun h => append_le h.1 h.2⟩

theorem one_le_iff {m : UInt32} {c : HIn} : one m ≤ c ↔ m ∈ c.names ∨ c.any = true := by
  constructor
  · intro h; exact h.2.2 m (List.mem_singleton.mpr rfl)
  · intro h
    refine ⟨fun h' => by simp [one] at h', fun h' => by simp [one] at h', fun k hk => ?_⟩
    rw [List.mem_singleton.mp hk]; exact h

/-! ### An application's frames -/

/-- What flows from an application, by its function part. -/
def flApp (f x : Expr) : HIn := match f with
  | .lam b => b.fl ++ x.fl
  | .prim .hnd => match x with
      | .pair (.prim (.lit (.i32 _))) X => X.fl
      | x => HIn.top ++ x.fl
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) X) => X.fl ++ x.hin
  | .app (.prim .ubind) N => N.fl ++ x.fl
  | .app (.prim .cfin) s => s.fl ++ x.fl
  | .prim .ccatch => x.fl
  | f => f.fl ++ x.fl

theorem fl_app (f x : Expr) : (Expr.app f x).fl = flApp f x := by
  rw [Expr.fl.eq_def]; rfl

/-- What flows from a function part applied to a value: a `λ`'s body; the rest of a handler's
head; a finaliser's or a cancel's parts. -/
def fh (f : Expr) : HIn := match f with
  | .lam b => b.fl
  | .prim .hnd => HIn.top
  | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) X) => X.fl
  | .app (.prim .ubind) N => N.fl
  | .app (.prim .cfin) s => s.fl
  | .prim .ccatch => {}
  | f => f.fl

theorem fl_prim_hnd_app (Y : Expr) : (Expr.app (.prim .hnd) Y).fl =
    match Y with
    | .pair (.prim (.lit (.i32 _))) X => X.fl
    | x => HIn.top ++ x.fl := by
  rw [fl_app]; rfl

theorem fl_hnd_lit (m : UInt32) (X : Expr) :
    (Expr.app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) X)).fl = X.fl := by
  rw [fl_app]; rfl

theorem fl_hnd_app (m : UInt32) (X x : Expr) :
    (Expr.app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) X)) x).fl = X.fl ++ x.hin := by
  rw [fl_app]; rfl

theorem fl_prim_app (p : Prim) (N : Expr) (hp : p ≠ .hnd) (hc : p ≠ .ccatch) :
    (Expr.app (.prim p) N).fl = primHin p ++ N.fl := by
  rw [fl_app]; cases p <;> first | rfl | exact absurd rfl hp | exact absurd rfl hc

theorem fl_hnd_nonlit {Y : Expr} (h : isLitPair Y = false) :
    (Expr.app (.prim .hnd) Y).fl = HIn.top ++ Y.fl := by
  rw [fl_prim_hnd_app]
  split
  · simp [isLitPair] at h
  · rfl

theorem any_top_append (a : HIn) : (HIn.top ++ a).any = true := by simp [HIn.top]

/-- **An application's flow, from its parts'**, when its function part is not a handler's head:
the head of a handler frame adds its body's frames. -/
theorem app_fl_le {f : Expr} (x : Expr) (h : isHndLit f = false) :
    (Expr.app f x).fl ≤ f.fl ++ x.fl := by
  rw [fl_app]; unfold flApp
  split
  · exact append_mono (fl_le_hin _) (le_refl _)
  · exact le_of_any (by simp [Expr.fl, primHin, HIn.top])
  · simp [isHndLit] at h
  · rw [fl_prim_app _ _ (by decide) (by decide)]
    exact append_mono (le_append_right _ _) (le_refl _)
  · rw [fl_prim_app _ _ (by decide) (by decide)]
    exact append_mono (le_append_right _ _) (le_refl _)
  · exact le_append_right _ _
  · exact le_refl _

theorem fh_le_fl (f : Expr) : fh f ≤ f.fl := by
  unfold fh
  split
  · exact fl_le_hin _
  · exact le_refl _
  · rw [fl_hnd_lit]; exact le_refl _
  · rw [fl_prim_app _ _ (by decide) (by decide)]; exact le_append_right _ _
  · rw [fl_prim_app _ _ (by decide) (by decide)]; exact le_append_right _ _
  · exact empty_le _
  · exact le_refl _

/-- An application's flow holds its function part's, as one, and its argument's, when the
function part is not `hnd` itself. -/
theorem app_fl_ge {f : Expr} (x : Expr) (h : isHnd f = false) :
    fh f ≤ (Expr.app f x).fl ∧ x.fl ≤ (Expr.app f x).fl := by
  rw [fl_app]; unfold flApp fh
  split
  · exact ⟨le_append_left _ _, le_append_right _ _⟩
  · simp [isHnd] at h
  · exact ⟨le_append_left _ _, le_append_of_le_right (fl_le_hin _)⟩
  · exact ⟨le_append_left _ _, le_append_right _ _⟩
  · exact ⟨le_append_left _ _, le_append_right _ _⟩
  · exact ⟨empty_le _, le_refl _⟩
  · exact ⟨le_append_left _ _, le_append_right _ _⟩

/-- An application to a value flows its function part's flow as one, and the value's. -/
theorem app_val_le (f : Expr) {v : Expr} (hv : IsVal v) : (Expr.app f v).fl ≤ fh f ++ v.fl := by
  rw [fl_app]; unfold flApp fh
  split
  · exact le_refl _
  · exact le_of_any (by simp [HIn.top])
  · exact append_mono (le_refl _) hv.hin_le_fl
  · exact le_refl _
  · exact le_refl _
  · exact le_append_right _ _
  · exact le_refl _

theorem fl_app_plain {f x : Expr} (h1 : ∀ b, f = .lam b → False) (h2 : f = .prim .hnd → False)
    (h3 : ∀ n X, f = .app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) X) → False)
    (h4 : ∀ N, f = .app (.prim .ubind) N → False) (h5 : ∀ s, f = .app (.prim .cfin) s → False)
    (h6 : f = .prim .ccatch → False) : (Expr.app f x).fl = f.fl ++ x.fl := by
  rw [fl_app]; unfold flApp
  split
  · exact (h1 _ rfl).elim
  · exact (h2 rfl).elim
  · exact (h3 _ _ rfl).elim
  · exact (h4 _ rfl).elim
  · exact (h5 _ rfl).elim
  · exact (h6 rfl).elim
  · rfl

theorem fl_ubind_app (N x : Expr) :
    (Expr.app (.app (.prim .ubind) N) x).fl = N.fl ++ x.fl := by rw [fl_app]; rfl

theorem fl_cfin_app (N x : Expr) :
    (Expr.app (.app (.prim .cfin) N) x).fl = N.fl ++ x.fl := by rw [fl_app]; rfl

theorem fl_ccatch_app (x : Expr) : (Expr.app (.prim .ccatch) x).fl = x.fl := by rw [fl_app]; rfl

theorem fl_lam_app (b x : Expr) : (Expr.app (.lam b) x).fl = b.fl ++ x.fl := by rw [fl_app]; rfl

theorem le_of_le_any {a V : HIn} (h : a ≤ V) (ha : a.any = true) : V.any = true := h.1 ha

/-- **A substitution keeps the frames held within a bound** that holds the value's. -/
theorem hin_subst {V : HIn} (e : Expr) : ∀ (j : Nat) (v : Val), e.hin ≤ V → v.1.hin ≤ V →
    (e.subst j v).hin ≤ V := by
  induction e using Expr.hin.induct with
  | case1 i =>
      intro j v _ hv
      simp only [Expr.subst]
      split
      · exact hv
      · split <;> exact empty_le _
  | case2 | case3 | case4 => intro _ _ he _; exact he
  | case5 a b iha ihb | case6 a b iha ihb =>
      intro j v he hv
      simp only [Expr.hin, append_le_iff] at he
      simp only [Expr.subst, Expr.hin, append_le_iff]
      exact ⟨iha j v he.1 hv, ihb j v he.2 hv⟩
  | case7 a b iha ihb =>
      intro j v he hv
      simp only [Expr.hin, append_le_iff] at he
      simp only [Expr.subst, Expr.hin, append_le_iff]
      exact ⟨iha j v he.1 hv, ihb _ _ he.2 (by rw [hin_shift_val]; exact hv)⟩
  | case8 a b c iha ihb ihc =>
      intro j v he hv
      simp only [Expr.hin, append_le_iff] at he
      simp only [Expr.subst, Expr.hin, append_le_iff]
      exact ⟨⟨iha j v he.1.1 hv, ihb _ _ he.1.2 (by rw [hin_shift_val]; exact hv)⟩,
        ihc _ _ he.2 (by rw [hin_shift_val]; exact hv)⟩
  | case9 a ih | case10 a ih =>
      intro j v he hv
      simp only [Expr.hin] at he
      simp only [Expr.subst, Expr.hin]
      exact ih j v he hv
  | case11 a ih =>
      intro j v he hv
      simp only [Expr.hin] at he
      simp only [Expr.subst, Expr.hin]
      exact ih _ _ he (by rw [hin_shift_val]; exact hv)
  | case12 m X ih =>
      intro j v he hv
      simp only [Expr.hin, append_le_iff] at he
      simp only [Expr.subst, Expr.hin, append_le_iff]
      exact ⟨he.1, ih j v he.2 hv⟩
  | case13 f x hfx ihf ihx =>
      intro j v he hv
      simp only [Expr.subst]
      refine le_trans (hin_app_le _ _) ?_
      rw [Expr.hin_app] at he
      split at he
      · rename_i hf
        have hf := isHnd_iff.mp hf
        subst hf
        have hx : isLitPair x = false := by
          cases hx : isLitPair x
          · rfl
          · match x, hx with
            | .pair (.prim (.lit (.i32 m))) X, _ => exact absurd rfl (hfx m X rfl)
        rw [hndArg_of_not hx] at he
        exact le_of_any (le_of_le_any he (any_top_append _))
      · rw [append_le_iff] at he ⊢
        exact ⟨ihf j v he.1 hv, ihx j v he.2 hv⟩

/-- A substitution makes a handler's head only of a handler's head, or of a frame of any name. -/
theorem hndLit_subst {f : Expr} {j : Nat} {v : Val} (h : isHndLit (f.subst j v) = true) :
    isHndLit f = true ∨ f.fl.any = true ∨ v.1.hin.any = true := by
  match f with
  | .var i =>
      simp only [Expr.subst] at h
      split at h
      · exfalso
        have hv := v.2
        revert h hv
        generalize v.1 = w
        intro h hv
        match w, h with
        | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) _), _ =>
            have := (isVal_app_iff.mp hv).1; cases this
      · split at h <;> simp [isHndLit] at h
  | .app g Y =>
      simp only [Expr.subst] at h
      match g, Y with
      | .prim .hnd, .pair (.prim (.lit (.i32 _))) _ => exact .inl rfl
      | .prim .hnd, .var i =>
          right; left
          rw [fl_hnd_nonlit rfl]; exact any_top_append _
      | .prim .hnd, .pair (.var i) _ =>
          right; left
          rw [fl_hnd_nonlit rfl]; exact any_top_append _
      | .var i, Y =>
          right; right
          simp only [Expr.subst] at h
          split at h
          · revert h
            generalize v.1 = w
            intro h
            match w, h with
            | .prim .hnd, _ => simp [Expr.hin, primHin, HIn.top]
          · split at h <;> simp [isHndLit] at h
      | .prim .hnd, .unit | .prim .hnd, .loc _ | .prim .hnd, .prim _ | .prim .hnd, .inj₁ _
      | .prim .hnd, .inj₂ _ | .prim .hnd, .lam _ | .prim .hnd, .seq _ _
      | .prim .hnd, .letpair _ _ | .prim .hnd, .case _ _ _ | .prim .hnd, .app _ _ =>
          simp [Expr.subst, isHndLit] at h
      | .prim .hnd, .pair .unit _ | .prim .hnd, .pair (.loc _) _ | .prim .hnd, .pair (.inj₁ _) _
      | .prim .hnd, .pair (.inj₂ _) _ | .prim .hnd, .pair (.lam _) _
      | .prim .hnd, .pair (.seq _ _) _ | .prim .hnd, .pair (.letpair _ _) _
      | .prim .hnd, .pair (.case _ _ _) _ | .prim .hnd, .pair (.app _ _) _
      | .prim .hnd, .pair (.pair _ _) _ =>
          simp [Expr.subst, isHndLit] at h
      | .prim .hnd, .pair (.prim q) _ =>
          left
          cases q <;> simp [Expr.subst, isHndLit] at h ⊢
          rename_i c; cases c <;> simp at h ⊢
      | .prim (.lit _), _ | .prim .alloc, _ | .prim .free, _ | .prim .load, _ | .prim .store, _
      | .prim (.host _), _ | .prim .tab, _ | .prim .idx, _ | .prim .drop, _ | .prim .split, _
      | .prim .count, _ | .prim .countTry, _ | .prim .boundedFix, _ | .prim .iterate, _
      | .prim .perform, _ | .prim .raise, _ | .prim .ubind, _ | .prim .ccatch, _
      | .prim .cfin, _ => simp [Expr.subst, isHndLit] at h
      | .unit, _ | .loc _, _ | .pair _ _, _ | .inj₁ _, _ | .inj₂ _, _ | .lam _, _ | .seq _ _, _
      | .letpair _ _, _ | .case _ _ _, _ | .app _ _, _ => simp [Expr.subst, isHndLit] at h
  | .unit | .loc _ | .prim _ | .pair _ _ | .inj₁ _ | .inj₂ _ | .lam _ | .seq _ _ | .letpair _ _
  | .case _ _ _ => simp [Expr.subst, isHndLit] at h

/-- **A substitution keeps what flows within a bound** that holds the value's frames. -/
theorem fl_subst {V : HIn} (e : Expr) : ∀ (j : Nat) (v : Val), e.fl ≤ V → v.1.hin ≤ V →
    (e.subst j v).fl ≤ V := by
  induction e using Expr.fl.induct with
  | case1 i =>
      intro j v _ hv
      simp only [Expr.subst]
      split
      · exact le_trans (fl_le_hin _) hv
      · split <;> exact empty_le _
  | case2 | case3 | case4 => intro _ _ he _; exact he
  | case5 b =>
      intro j v he hv
      simp only [Expr.fl] at he
      simp only [Expr.subst, Expr.fl]
      exact hin_subst b _ _ he (by rw [hin_shift_val]; exact hv)
  | case6 a b iha ihb | case7 a b iha ihb =>
      intro j v he hv
      simp only [Expr.fl, append_le_iff] at he
      simp only [Expr.subst, Expr.fl, append_le_iff]
      exact ⟨iha j v he.1 hv, ihb j v he.2 hv⟩
  | case8 a b iha ihb =>
      intro j v he hv
      simp only [Expr.fl, append_le_iff] at he
      simp only [Expr.subst, Expr.fl, append_le_iff]
      exact ⟨iha j v he.1 hv, ihb _ _ he.2 (by rw [hin_shift_val]; exact hv)⟩
  | case9 a b c iha ihb ihc =>
      intro j v he hv
      simp only [Expr.fl, append_le_iff] at he
      simp only [Expr.subst, Expr.fl, append_le_iff]
      exact ⟨⟨iha j v he.1.1 hv, ihb _ _ he.1.2 (by rw [hin_shift_val]; exact hv)⟩,
        ihc _ _ he.2 (by rw [hin_shift_val]; exact hv)⟩
  | case10 a ih | case11 a ih =>
      intro j v he hv
      simp only [Expr.fl] at he
      simp only [Expr.subst, Expr.fl]
      exact ih j v he hv
  | case12 x b ihb ihx =>
      intro j v he hv
      rw [fl_lam_app, append_le_iff] at he
      simp only [Expr.subst]
      rw [fl_lam_app, append_le_iff]
      exact ⟨ihb _ _ he.1 (by rw [hin_shift_val]; exact hv), ihx j v he.2 hv⟩
  | case13 n X ih =>
      intro j v he hv
      rw [fl_hnd_lit] at he
      simp only [Expr.subst]
      rw [fl_hnd_lit]
      exact ih j v he hv
  | case14 x hx _ =>
      intro j v he _
      have hl : isLitPair x = false := by
        cases h : isLitPair x
        · rfl
        · match x, h with
          | .pair (.prim (.lit (.i32 m))) X, _ => exact absurd rfl (hx m X)
      rw [fl_hnd_nonlit hl] at he
      exact le_of_any (le_of_le_any he (any_top_append _))
  | case15 x n X ihX =>
      intro j v he hv
      rw [fl_hnd_app, append_le_iff] at he
      simp only [Expr.subst]
      rw [fl_hnd_app, append_le_iff]
      exact ⟨ihX j v he.1 hv, hin_subst x j v he.2 hv⟩
  | case16 x N ihN ihx =>
      intro j v he hv
      rw [fl_ubind_app, append_le_iff] at he
      simp only [Expr.subst]
      rw [fl_ubind_app, append_le_iff]
      exact ⟨ihN j v he.1 hv, ihx j v he.2 hv⟩
  | case17 x N ihN ihx =>
      intro j v he hv
      rw [fl_cfin_app, append_le_iff] at he
      simp only [Expr.subst]
      rw [fl_cfin_app, append_le_iff]
      exact ⟨ihN j v he.1 hv, ihx j v he.2 hv⟩
  | case18 x ihx =>
      intro j v he hv
      rw [fl_ccatch_app] at he
      simp only [Expr.subst]
      rw [fl_ccatch_app]
      exact ihx j v he hv
  | case19 x f h1 h2 h3 h4 h5 h6 ihf ihx =>
      intro j v he hv
      rw [fl_app_plain h1 h2 h3 h4 h5 h6, append_le_iff] at he
      simp only [Expr.subst]
      by_cases hV : V.any = true
      · exact le_of_any hV
      · have hl : isHndLit (f.subst j v) = false := by
          cases hl : isHndLit (f.subst j v)
          · rfl
          · rcases hndLit_subst hl with h | h | h
            · match f, h with
              | .app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) X), _ => exact (h3 n X rfl).elim
            · exact absurd (le_of_le_any he.1 h) hV
            · exact absurd (le_of_le_any hv h) hV
        exact le_trans (app_fl_le _ hl) (append_le (ihf j v he.1 hv) (ihx j v he.2 hv))

/-! ### Contexts -/

/-- **A redex's shape**: a sequence, a pair's or a sum's elimination, or an application whose
function part is not the head of a handler, a finaliser or a cancel's finaliser. -/
def PlainB : Expr → Bool
  | .seq _ _ | .letpair _ _ | .case _ _ _ => true
  | .app (.prim .hnd) _ | .app (.prim .ubind) _ | .app (.prim .cfin) _ => false
  | .app _ _ => true
  | _ => false

theorem plainB_not_prim {a : Expr} (h : PlainB a = true) (p : Prim) : a ≠ .prim p := by
  rintro rfl; simp [PlainB] at h

theorem plainB_fh {a : Expr} (h : PlainB a = true) : fh a = a.fl := by
  unfold fh
  split <;> simp_all [PlainB]

theorem fh_pair (a b : Expr) : fh (.pair a b) = (Expr.pair a b).fl := rfl
theorem fh_seq (a b : Expr) : fh (.seq a b) = (Expr.seq a b).fl := rfl
theorem fh_letpair (a b : Expr) : fh (.letpair a b) = (Expr.letpair a b).fl := rfl
theorem fh_case (a b c : Expr) : fh (.case a b c) = (Expr.case a b c).fl := rfl
theorem fh_inj₁ (a : Expr) : fh (.inj₁ a) = (Expr.inj₁ a).fl := rfl
theorem fh_inj₂ (a : Expr) : fh (.inj₂ a) = (Expr.inj₂ a).fl := rfl

/-- An application's flow as a function part, by its own function part. -/
theorem fh_app (f Z : Expr) : fh (.app f Z) = match f with
    | .prim .hnd => (match Z with
        | .pair (.prim (.lit (.i32 _))) X => X.fl
        | _ => (Expr.app (.prim .hnd) Z).fl)
    | .prim .ubind => Z.fl
    | .prim .cfin => Z.fl
    | f => (Expr.app f Z).fl := by
  unfold fh
  split
  · rename_i h; cases h
  · rename_i h; cases h
  · rename_i n X h; cases h; rfl
  · rename_i N h; cases h; rfl
  · rename_i N h; cases h; rfl
  · rename_i h; cases h
  · rename_i h1 h2 h3 h4 h5 h6
    split
    · split
      · rename_i n X; exact (h3 n X rfl).elim
      · rfl
    · exact (h4 Z rfl).elim
    · exact (h5 Z rfl).elim
    · rfl

theorem fh_app_of_not_prim {f : Expr} (Z : Expr) (h : ∀ p, f ≠ .prim p) :
    fh (.app f Z) = (Expr.app f Z).fl := by
  rw [fh_app]
  split
  · exact absurd rfl (h _)
  · exact absurd rfl (h _)
  · exact absurd rfl (h _)
  · rfl

theorem plug_not_prim {a : Expr} (ha : PlainB a = true) :
    ∀ (K : Kont) (p : Prim), K.plug a ≠ .prim p
  | .hole, p => plainB_not_prim ha p
  | .pairL .., _ | .pairR .., _ | .letpair .., _ | .case .., _ | .appR .., _ | .appL .., _
  | .seq .., _ | .inj₁ _, _ | .inj₂ _, _ => by simp [Kont.plug]

theorem isHnd_plug {a : Expr} (ha : PlainB a = true) (K : Kont) : isHnd (K.plug a) = false := by
  cases h : isHnd (K.plug a)
  · rfl
  · exact absurd (isHnd_iff.mp h) (plug_not_prim ha K _)

theorem isLitPair_pair {x e : Expr} (h : isLitPair (.pair x e) = true) :
    ∃ m, x = .prim (.lit (.i32 m)) := by
  match x, h with
  | .prim (.lit (.i32 m)), _ => exact ⟨m, rfl⟩

/-- A context fills a literal name and a rest only where it is the rest's: `(m, K)`. -/
theorem plug_litPair {a : Expr} (ha : PlainB a = true) :
    ∀ {K : Kont}, isLitPair (K.plug a) = true →
      ∃ (m : UInt32) (K' : Kont), K = .pairR (Val.i32 m) K'
  | .hole, h => by
      exfalso
      match a, h, ha with
      | .pair _ _, _, ha => simp [PlainB] at ha
  | .pairL K' e, h => by
      exfalso
      obtain ⟨m, hm⟩ := isLitPair_pair h
      exact plug_not_prim ha K' _ hm
  | .pairR v K', h => by
      obtain ⟨m, hm⟩ := isLitPair_pair h
      exact ⟨m, K', by congr; exact Val.ext hm⟩
  | .letpair .., h | .case .., h | .appR .., h | .appL .., h | .seq .., h | .inj₁ _, h
  | .inj₂ _, h => by simp [Kont.plug, isLitPair] at h

theorem hin_pair_lit (m : UInt32) (Y : Expr) :
    (Expr.pair (Val.i32 m).1 Y).hin = {} ++ Y.hin := rfl

theorem fl_pair_lit (m : UInt32) (Y : Expr) :
    (Expr.pair (Val.i32 m).1 Y).fl = {} ++ Y.fl := rfl

theorem empty_append (a : HIn) : ({} : HIn) ++ a = a := by
  show HIn.mk ([] ++ a.names) (false || a.fin) (false || a.any) = a
  simp

/-- **A context keeps a bound**: replacing a redex by a term that keeps the bound on what flows
from it and on its frames keeps the bound on what flows from the context and its frames.
`[spec §19]` -/
theorem plug_le {V : HIn} {a a' : Expr} (ha : PlainB a = true) (hfl : a.fl ≤ V → a'.fl ≤ V)
    (hhin : a.hin ≤ V → a'.hin ≤ V) : ∀ K : Kont,
      ((K.plug a).fl ≤ V → (K.plug a').fl ≤ V) ∧ ((K.plug a).hin ≤ V → (K.plug a').hin ≤ V) ∧
        (fh (K.plug a) ≤ V → fh (K.plug a') ≤ V) := by
  intro K
  induction K with
  | hole =>
      refine ⟨hfl, hhin, fun h => le_trans (fh_le_fl _) (hfl ?_)⟩
      simpa only [Kont.plug, plainB_fh ha] using h
  | pairL K e ih =>
      have h₁ : ∀ x, (Expr.pair x e).fl ≤ V ↔ x.fl ≤ V ∧ e.fl ≤ V := fun x => by
        simp only [Expr.fl, append_le_iff]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Kont.plug, h₁] at h ⊢; exact ⟨ih.1 h.1, h.2⟩
      · simp only [Kont.plug, Expr.hin, append_le_iff] at h ⊢; exact ⟨ih.2.1 h.1, h.2⟩
      · simp only [Kont.plug, fh_pair, h₁] at h ⊢; exact ⟨ih.1 h.1, h.2⟩
  | pairR v K ih =>
      have h₁ : ∀ x, (Expr.pair v.1 x).fl ≤ V ↔ v.1.fl ≤ V ∧ x.fl ≤ V := fun x => by
        simp only [Expr.fl, append_le_iff]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Kont.plug, Expr.val, h₁] at h ⊢; exact ⟨h.1, ih.1 h.2⟩
      · simp only [Kont.plug, Expr.val, Expr.hin, append_le_iff] at h ⊢; exact ⟨h.1, ih.2.1 h.2⟩
      · simp only [Kont.plug, Expr.val, fh_pair, h₁] at h ⊢; exact ⟨h.1, ih.1 h.2⟩
  | letpair K e ih =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Kont.plug, Expr.fl, append_le_iff] at h ⊢; exact ⟨ih.1 h.1, h.2⟩
      · simp only [Kont.plug, Expr.hin, append_le_iff] at h ⊢; exact ⟨ih.2.1 h.1, h.2⟩
      · simp only [Kont.plug, fh_letpair, Expr.fl, append_le_iff] at h ⊢; exact ⟨ih.1 h.1, h.2⟩
  | case K e₁ e₂ ih =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Kont.plug, Expr.fl, append_le_iff] at h ⊢; exact ⟨⟨ih.1 h.1.1, h.1.2⟩, h.2⟩
      · simp only [Kont.plug, Expr.hin, append_le_iff] at h ⊢; exact ⟨⟨ih.2.1 h.1.1, h.1.2⟩, h.2⟩
      · simp only [Kont.plug, fh_case, Expr.fl, append_le_iff] at h ⊢
        exact ⟨⟨ih.1 h.1.1, h.1.2⟩, h.2⟩
  | seq K e ih =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Kont.plug, Expr.fl, append_le_iff] at h ⊢; exact ⟨ih.1 h.1, h.2⟩
      · simp only [Kont.plug, Expr.hin, append_le_iff] at h ⊢; exact ⟨ih.2.1 h.1, h.2⟩
      · simp only [Kont.plug, fh_seq, Expr.fl, append_le_iff] at h ⊢; exact ⟨ih.1 h.1, h.2⟩
  | inj₁ K ih =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Kont.plug, Expr.fl] at h ⊢; exact ih.1 h
      · simp only [Kont.plug, Expr.hin] at h ⊢; exact ih.2.1 h
      · simp only [Kont.plug, fh_inj₁, Expr.fl] at h ⊢; exact ih.1 h
  | inj₂ K ih =>
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [Kont.plug, Expr.fl] at h ⊢; exact ih.1 h
      · simp only [Kont.plug, Expr.hin] at h ⊢; exact ih.2.1 h
      · simp only [Kont.plug, fh_inj₂, Expr.fl] at h ⊢; exact ih.1 h
  | appL K v ih =>
      have hZ := plug_not_prim ha K
      have hn := isHnd_plug ha K
      have hfl' : (Kont.appL K v).plug a = .app (K.plug a) v.1 := rfl
      have hfl'' : (Kont.appL K v).plug a' = .app (K.plug a') v.1 := rfl
      have flb : ((Kont.appL K v).plug a).fl ≤ V → ((Kont.appL K v).plug a').fl ≤ V := by
        intro h
        rw [hfl'] at h; rw [hfl'']
        have ⟨g₁, g₂⟩ := app_fl_ge v.1 hn
        exact le_trans (app_val_le _ v.2) (append_le (ih.2.2 (le_trans g₁ h)) (le_trans g₂ h))
      refine ⟨flb, fun h => ?_, fun h => ?_⟩
      · rw [hfl'] at h; rw [hfl'']
        rw [hin_app_eq hn, append_le_iff] at h
        exact le_trans (hin_app_le _ _) (append_le (ih.2.1 h.1) h.2)
      · rw [hfl', fh_app_of_not_prim _ hZ] at h
        exact le_trans (fh_le_fl _) (flb (by rw [hfl']; exact h))
  | appR f K ih =>
      have hp : (Kont.appR f K).plug a = .app f (K.plug a) := rfl
      have hp' : (Kont.appR f K).plug a' = .app f (K.plug a') := rfl
      rw [hp, hp']
      -- the handler's name and rest, when `K` fills a literal name's rest
      have lit_case : ∀ (P : Expr → HIn), (∀ m Y, P (.pair (Val.i32 m).1 Y) = Y.fl) →
          (∀ Z, isLitPair Z = false → (HIn.top ++ Z.fl ≤ P Z)) →
          P (K.plug a) ≤ V → P (K.plug a') ≤ V := by
        intro P hP hN h
        cases hl : isLitPair (K.plug a)
        · exact le_of_any (le_of_le_any (le_trans (hN _ hl) h) (any_top_append _))
        · obtain ⟨m, K', rfl⟩ := plug_litPair ha hl
          simp only [Kont.plug, Expr.val] at h ⊢
          rw [hP] at h ⊢
          have := ih.1
          simp only [Kont.plug, Expr.val, fl_pair_lit, empty_append] at this
          exact this h
      have flb : (Expr.app f (K.plug a)).fl ≤ V → (Expr.app f (K.plug a')).fl ≤ V := by
        intro h
        rw [fl_app] at h ⊢; unfold flApp at h ⊢
        split at h
        · rw [append_le_iff] at h ⊢; exact ⟨h.1, ih.1 h.2⟩
        · exact lit_case (fun Z => match Z with
              | .pair (.prim (.lit (.i32 _))) X => X.fl
              | x => HIn.top ++ x.fl) (fun _ _ => rfl)
            (fun Z hZ => by
              split
              · simp [isLitPair] at hZ
              · exact le_refl _) h
        · rw [append_le_iff] at h ⊢; exact ⟨h.1, ih.2.1 h.2⟩
        · rw [append_le_iff] at h ⊢; exact ⟨h.1, ih.1 h.2⟩
        · rw [append_le_iff] at h ⊢; exact ⟨h.1, ih.1 h.2⟩
        · exact ih.1 h
        · rw [append_le_iff] at h ⊢; exact ⟨h.1, ih.1 h.2⟩
      refine ⟨flb, fun h => ?_, fun h => ?_⟩
      · rw [Expr.hin_app] at h ⊢
        split at h
        · rename_i hf
          rw [if_pos hf]
          cases hl : isLitPair (K.plug a)
          · rw [hndArg_of_not hl] at h
            exact le_of_any (le_of_le_any h (any_top_append _))
          · obtain ⟨m, K', rfl⟩ := plug_litPair ha hl
            simp only [Kont.plug, Expr.val, Val.i32, hndArg] at h ⊢
            rw [append_le_iff] at h ⊢
            refine ⟨h.1, ?_⟩
            have := ih.2.1
            simp only [Kont.plug, Expr.val, Val.i32] at this
            have e₁ : ∀ Y, (Expr.pair (.prim (.lit (.i32 m))) Y).hin = {} ++ Y.hin := fun _ => rfl
            rw [e₁, e₁, empty_append, empty_append] at this
            exact this h.2
        · rename_i hf
          rw [if_neg hf]
          rw [append_le_iff] at h ⊢; exact ⟨h.1, ih.2.1 h.2⟩
      · rw [fh_app] at h ⊢
        split at h
        · exact lit_case (fun Z => match Z with
              | .pair (.prim (.lit (.i32 _))) X => X.fl
              | _ => (Expr.app (.prim .hnd) Z).fl) (fun _ _ => rfl)
            (fun Z hZ => by
              split
              · simp [isLitPair] at hZ
              · rw [fl_hnd_nonlit hZ]; exact le_refl _) h
        · exact ih.1 h
        · exact ih.1 h
        · exact flb h

/-- **What flows from a redex flows from its context's filling**. -/
theorem plug_fl_ge {V : HIn} {a : Expr} (ha : PlainB a = true) : ∀ K : Kont,
    ((K.plug a).fl ≤ V → a.fl ≤ V) ∧ (fh (K.plug a) ≤ V → a.fl ≤ V) := by
  intro K
  induction K with
  | hole => exact ⟨id, fun h => by simpa only [Kont.plug, plainB_fh ha] using h⟩
  | pairL K e ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · simp only [Kont.plug, fh_pair, Expr.fl, append_le_iff] at h; exact ih.1 h.1
  | pairR v K ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · simp only [Kont.plug, fh_pair, Expr.fl, append_le_iff] at h; exact ih.1 h.2
  | letpair K e ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · simp only [Kont.plug, fh_letpair, Expr.fl, append_le_iff] at h; exact ih.1 h.1
  | case K e₁ e₂ ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · simp only [Kont.plug, fh_case, Expr.fl, append_le_iff] at h; exact ih.1 h.1.1
  | seq K e ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · simp only [Kont.plug, fh_seq, Expr.fl, append_le_iff] at h; exact ih.1 h.1
  | inj₁ K ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · simp only [Kont.plug, fh_inj₁, Expr.fl] at h; exact ih.1 h
  | inj₂ K ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
      · simp only [Kont.plug, fh_inj₂, Expr.fl] at h; exact ih.1 h
  | appL K v ih =>
      have hZ := plug_not_prim ha K
      have hn := isHnd_plug ha K
      have flb : ((Kont.appL K v).plug a).fl ≤ V → a.fl ≤ V := fun h =>
        ih.2 (le_trans (app_fl_ge v.1 hn).1 h)
      refine ⟨flb, fun h => flb ?_⟩
      have hp : (Kont.appL K v).plug a = .app (K.plug a) v.1 := rfl
      rw [hp, fh_app_of_not_prim _ hZ] at h
      rw [hp]; exact h
  | appR f K ih =>
      have hp : (Kont.appR f K).plug a = .app f (K.plug a) := rfl
      rw [hp]
      have lit_case : ∀ (P : Expr → HIn), (∀ m Y, P (.pair (Val.i32 m).1 Y) = Y.fl) →
          (∀ Z, isLitPair Z = false → (HIn.top ++ Z.fl ≤ P Z)) →
          P (K.plug a) ≤ V → a.fl ≤ V := by
        intro P hP hN h
        cases hl : isLitPair (K.plug a)
        · exact le_of_any (le_of_le_any (le_trans (hN _ hl) h) (any_top_append _))
        · obtain ⟨m, K', rfl⟩ := plug_litPair ha hl
          simp only [Kont.plug, Expr.val] at h
          rw [hP] at h
          have := ih.1
          simp only [Kont.plug, Expr.val, fl_pair_lit, empty_append] at this
          exact this h
      have flb : (Expr.app f (K.plug a)).fl ≤ V → a.fl ≤ V := by
        intro h
        rw [fl_app] at h; unfold flApp at h
        split at h
        · rw [append_le_iff] at h; exact ih.1 h.2
        · exact lit_case (fun Z => match Z with
              | .pair (.prim (.lit (.i32 _))) X => X.fl
              | x => HIn.top ++ x.fl) (fun _ _ => rfl)
            (fun Z hZ => by
              split
              · simp [isLitPair] at hZ
              · exact le_refl _) h
        · rw [append_le_iff] at h; exact ih.1 (le_trans (fl_le_hin _) h.2)
        · rw [append_le_iff] at h; exact ih.1 h.2
        · rw [append_le_iff] at h; exact ih.1 h.2
        · exact ih.1 h
        · rw [append_le_iff] at h; exact ih.1 h.2
      refine ⟨flb, fun h => ?_⟩
      rw [fh_app] at h
      split at h
      · exact lit_case (fun Z => match Z with
            | .pair (.prim (.lit (.i32 _))) X => X.fl
            | _ => (Expr.app (.prim .hnd) Z).fl) (fun _ _ => rfl)
          (fun Z hZ => by
            split
            · simp [isLitPair] at hZ
            · rw [fl_hnd_nonlit hZ]; exact le_refl _) h
      · exact ih.1 h
      · exact ih.1 h
      · exact flb h

/-- A term that is neither a literal name and a rest nor `hnd` itself. -/
def NonLit (e : Expr) : Prop := isLitPair e = false ∧ isHnd e = false

theorem PlainB.nonLit {a : Expr} (ha : PlainB a = true) : NonLit a := by
  refine ⟨?_, ?_⟩
  · cases h : isLitPair a
    · rfl
    · match a, h, ha with
      | .pair _ _, _, ha => simp [PlainB] at ha
  · cases h : isHnd a
    · rfl
    · exact absurd (isHnd_iff.mp h) (plainB_not_prim ha _)

theorem isHnd_plug_nonLit {e : Expr} (he : NonLit e) (K : Kont) : isHnd (K.plug e) = false := by
  cases K <;> first | exact he.2 | rfl

/-- `hin (f Z)` holds `Z`'s frames. -/
theorem hin_app_ge (f Z : Expr) : Z.hin ≤ (Expr.app f Z).hin := by
  rw [Expr.hin_app]
  split
  · unfold hndArg
    split
    · exact append_le (empty_le _) (le_append_right _ _)
    · exact le_append_right _ _
  · exact le_append_right _ _

theorem hin_app_ge_fun {f : Expr} (Z : Expr) (h : isHnd f = false) : f.hin ≤ (Expr.app f Z).hin := by
  rw [hin_app_eq h]; exact le_append_left _ _

/-- **A term's frames are within its context's filling's**. -/
theorem plug_hin_ge {e : Expr} (he : NonLit e) : ∀ K : Kont, e.hin ≤ (K.plug e).hin := by
  intro K
  induction K with
  | hole => exact le_refl _
  | pairL K _ ih | letpair K _ ih | seq K _ ih =>
      exact le_trans ih (le_append_left _ _)
  | case K _ _ ih => exact le_trans ih (le_trans (le_append_left _ _) (le_append_left _ _))
  | pairR _ K ih => exact le_trans ih (le_append_right _ _)
  | inj₁ K ih | inj₂ K ih => exact ih
  | appR f K ih => exact le_trans ih (hin_app_ge _ _)
  | appL K v ih =>
      exact le_trans ih (hin_app_ge_fun _ (isHnd_plug_nonLit he K))

/-- **A frame that catches `m` is among the frames held**. -/
theorem catches_hin {m : UInt32} : ∀ {K : Kont} (e : Expr), K.Catches m = true →
    (K.plug e).hin.Catches m
  | .hole, _, h => by simp [Kont.Catches] at h
  | .pairL K _, e, h | .letpair K _, e, h | .seq K _, e, h =>
      Catches.mono (le_append_left _ _) (catches_hin e h)
  | .case K _ _, e, h =>
      Catches.mono (le_trans (le_append_left _ _) (le_append_left _ _)) (catches_hin e h)
  | .pairR _ K, e, h => Catches.mono (le_append_right _ _) (catches_hin e h)
  | .inj₁ K, e, h | .inj₂ K, e, h => catches_hin (K := K) e h
  | .appL K v, e, h => by
      simp only [Kont.Catches] at h
      have := catches_hin (K := K) e h
      cases K with
      | hole => simp [Kont.Catches] at h
      | _ =>
        exact Catches.mono (hin_app_ge_fun _ (by simp [Kont.plug, isHnd])) this
  | .appR f K, e, h => by
      simp only [Kont.Catches, Bool.or_eq_true] at h
      rcases h with h | h
      · have hf : f.hin.Catches m := by
          split at h
          · rename_i n X
            simp only [beq_iff_eq] at h
            subst h
            show (HIn.one n ++ X.hin).Catches n
            exact Catches.mono (le_append_left _ _) (Catches.one n)
          · rename_i N
            show (HIn.final ++ N.hin).Catches m
            exact .inr (.inl (by simp [HIn.final]))
          · simp only [beq_iff_eq] at h
            subst h
            exact Catches.one 0
          · rename_i N
            show (HIn.final ++ N.hin).Catches m
            exact .inr (.inl (by simp [HIn.final]))
          · cases h
        have hn : isHnd f = false := by
          cases hf' : isHnd f
          · rfl
          · rw [isHnd_iff.mp hf'] at h; simp at h
        exact Catches.mono (hin_app_ge_fun _ hn) hf
      · exact Catches.mono (hin_app_ge _ _) (catches_hin e h)

/-! ### The names a term may perform -/

/-- The operations a primitive may perform: `perform` applied to a name that is not a literal
may perform any. -/
def primPn : Prim → HIn
  | .perform => HIn.top
  | _ => {}

/-- **The names a term may perform**: `perform (m, …)` at a literal name `m`; any other occurrence
of `perform` may perform any name. A handler frame is captured only by an operation of its name.
`[spec §19]` -/
def _root_.BoCa.Expr.pn : Expr → HIn
  | .var _ | .unit | .loc _ => {}
  | .prim p => primPn p
  | .pair a b | .seq a b | .letpair a b => a.pn ++ b.pn
  | .case a b c => a.pn ++ b.pn ++ c.pn
  | .inj₁ a | .inj₂ a | .lam a => a.pn
  | .app f x => match f, x with
      | .prim .perform, .pair (.prim (.lit (.i32 m))) X => HIn.one m ++ X.pn
      | f, x => f.pn ++ x.pn

/-- `(m, X)` as an operation's payload: of the name `m` when it is a literal. -/
def pnArg : Expr → HIn
  | .pair (.prim (.lit (.i32 m))) X => HIn.one m ++ X.pn
  | x => HIn.top ++ x.pn

/-- The term is the primitive `perform`. -/
def isPerform : Expr → Bool
  | .prim .perform => true
  | _ => false

theorem isPerform_iff {f : Expr} : isPerform f = true ↔ f = .prim .perform := by
  constructor
  · intro h; unfold isPerform at h; split at h <;> simp_all
  · rintro rfl; rfl

theorem _root_.BoCa.Expr.pn_app (f x : Expr) :
    (Expr.app f x).pn = if isPerform f then pnArg x else f.pn ++ x.pn := by
  cases f <;> try rfl
  rename_i p
  cases p <;> try rfl
  cases x <;> try rfl
  rename_i a X
  cases a <;> try rfl
  rename_i q
  cases q <;> try rfl
  rename_i c
  cases c <;> rfl

theorem pnArg_of_not {x : Expr} (h : isLitPair x = false) : pnArg x = HIn.top ++ x.pn := by
  unfold pnArg
  split
  · simp [isLitPair] at h
  · rfl

theorem pn_app_le (f x : Expr) : (Expr.app f x).pn ≤ f.pn ++ x.pn := by
  rw [Expr.pn_app]
  split
  · rename_i h
    rw [isPerform_iff.mp h]
    exact le_of_any (by simp [Expr.pn, primPn, top])
  · exact le_refl _

theorem pn_app_eq {f x : Expr} (h : isPerform f = false) : (Expr.app f x).pn = f.pn ++ x.pn := by
  rw [Expr.pn_app, if_neg (by simp [h])]

theorem pn_app_ge (f Z : Expr) : Z.pn ≤ (Expr.app f Z).pn := by
  rw [Expr.pn_app]
  split
  · unfold pnArg
    split
    · exact append_le (empty_le _) (le_append_right _ _)
    · exact le_append_right _ _
  · exact le_append_right _ _

theorem pn_app_ge_fun {f : Expr} (Z : Expr) (h : isPerform f = false) :
    f.pn ≤ (Expr.app f Z).pn := by
  rw [pn_app_eq h]; exact le_append_left _ _

theorem isPerform_shift (f : Expr) (d c : Nat) : isPerform (f.shift d c) = isPerform f := by
  cases f <;> try rfl
  simp only [Expr.shift]; split <;> rfl

theorem pn_shift (d : Nat) : ∀ (e : Expr) (c : Nat), (e.shift d c).pn = e.pn
  | .var i, c => by simp only [Expr.shift]; split <;> rfl
  | .unit, _ | .loc _, _ | .prim _, _ => rfl
  | .pair a b, c => by simp only [Expr.shift, Expr.pn, pn_shift d a, pn_shift d b]
  | .seq a b, c => by simp only [Expr.shift, Expr.pn, pn_shift d a, pn_shift d b]
  | .letpair a b, c => by simp only [Expr.shift, Expr.pn, pn_shift d a, pn_shift d b]
  | .case a b e, c => by
      simp only [Expr.shift, Expr.pn, pn_shift d a, pn_shift d b, pn_shift d e]
  | .inj₁ a, c => by simp only [Expr.shift, Expr.pn, pn_shift d a]
  | .inj₂ a, c => by simp only [Expr.shift, Expr.pn, pn_shift d a]
  | .lam a, c => by simp only [Expr.shift, Expr.pn, pn_shift d a]
  | .app f x, c => by
      simp only [Expr.shift]
      rw [Expr.pn_app, Expr.pn_app, isPerform_shift, pn_shift d f, pn_shift d x]
      split
      · cases hx : isLitPair x
        · rw [pnArg_of_not (by rw [isLitPair_shift]; exact hx), pnArg_of_not hx, pn_shift d x]
        · match x, hx with
          | .pair (.prim (.lit (.i32 m))) X, _ =>
              simp only [Expr.shift, pnArg, pn_shift d X]
      · rfl

theorem pn_shift_val (v : Val) (d c : Nat) : (v.shift d c).1.pn = v.1.pn := pn_shift d v.1 c

/-- **A substitution keeps the names performed within a bound** that holds the value's. -/
theorem pn_subst {V : HIn} (e : Expr) : ∀ (j : Nat) (v : Val), e.pn ≤ V → v.1.pn ≤ V →
    (e.subst j v).pn ≤ V := by
  induction e using Expr.pn.induct with
  | case1 i =>
      intro j v _ hv
      simp only [Expr.subst]
      split
      · exact hv
      · split <;> exact empty_le _
  | case2 | case3 | case4 => intro _ _ he _; exact he
  | case5 a b iha ihb | case6 a b iha ihb =>
      intro j v he hv
      simp only [Expr.pn, append_le_iff] at he
      simp only [Expr.subst, Expr.pn, append_le_iff]
      exact ⟨iha j v he.1 hv, ihb j v he.2 hv⟩
  | case7 a b iha ihb =>
      intro j v he hv
      simp only [Expr.pn, append_le_iff] at he
      simp only [Expr.subst, Expr.pn, append_le_iff]
      exact ⟨iha j v he.1 hv, ihb _ _ he.2 (by rw [pn_shift_val]; exact hv)⟩
  | case8 a b c iha ihb ihc =>
      intro j v he hv
      simp only [Expr.pn, append_le_iff] at he
      simp only [Expr.subst, Expr.pn, append_le_iff]
      exact ⟨⟨iha j v he.1.1 hv, ihb _ _ he.1.2 (by rw [pn_shift_val]; exact hv)⟩,
        ihc _ _ he.2 (by rw [pn_shift_val]; exact hv)⟩
  | case9 a ih | case10 a ih =>
      intro j v he hv
      simp only [Expr.pn] at he
      simp only [Expr.subst, Expr.pn]
      exact ih j v he hv
  | case11 a ih =>
      intro j v he hv
      simp only [Expr.pn] at he
      simp only [Expr.subst, Expr.pn]
      exact ih _ _ he (by rw [pn_shift_val]; exact hv)
  | case12 m X ih =>
      intro j v he hv
      simp only [Expr.pn, append_le_iff] at he
      simp only [Expr.subst, Expr.pn, append_le_iff]
      exact ⟨he.1, ih j v he.2 hv⟩
  | case13 f x hfx ihf ihx =>
      intro j v he hv
      simp only [Expr.subst]
      refine le_trans (pn_app_le _ _) ?_
      rw [Expr.pn_app] at he
      split at he
      · rename_i hf
        have hf := isPerform_iff.mp hf
        subst hf
        have hx : isLitPair x = false := by
          cases hx : isLitPair x
          · rfl
          · match x, hx with
            | .pair (.prim (.lit (.i32 m))) X, _ => exact absurd rfl (hfx m X rfl)
        rw [pnArg_of_not hx] at he
        exact le_of_any (le_of_le_any he (any_top_append _))
      · rw [append_le_iff] at he ⊢
        exact ⟨ihf j v he.1 hv, ihx j v he.2 hv⟩

theorem isPerform_plug {a : Expr} (ha : PlainB a = true) (K : Kont) :
    isPerform (K.plug a) = false := by
  cases h : isPerform (K.plug a)
  · rfl
  · exact absurd (isPerform_iff.mp h) (plug_not_prim ha K _)

/-- **A context keeps a bound on the names performed**. -/
theorem plug_pn_le {V : HIn} {a a' : Expr} (ha : PlainB a = true)
    (hpn : a.pn ≤ V → a'.pn ≤ V) : ∀ K : Kont, (K.plug a).pn ≤ V → (K.plug a').pn ≤ V := by
  intro K
  induction K with
  | hole => exact hpn
  | pairL K e ih | letpair K e ih | seq K e ih =>
      intro h
      simp only [Kont.plug, Expr.pn, append_le_iff] at h ⊢; exact ⟨ih h.1, h.2⟩
  | pairR v K ih =>
      intro h
      simp only [Kont.plug, Expr.val, Expr.pn, append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩
  | case K e₁ e₂ ih =>
      intro h
      simp only [Kont.plug, Expr.pn, append_le_iff] at h ⊢; exact ⟨⟨ih h.1.1, h.1.2⟩, h.2⟩
  | inj₁ K ih | inj₂ K ih =>
      intro h
      simp only [Kont.plug, Expr.pn] at h ⊢; exact ih h
  | appL K v ih =>
      intro h
      have hp : (Kont.appL K v).plug a = .app (K.plug a) v.1 := rfl
      have hp' : (Kont.appL K v).plug a' = .app (K.plug a') v.1 := rfl
      rw [hp] at h; rw [hp']
      rw [pn_app_eq (isPerform_plug ha K), append_le_iff] at h
      exact le_trans (pn_app_le _ _) (append_le (ih h.1) h.2)
  | appR f K ih =>
      intro h
      have hp : (Kont.appR f K).plug a = .app f (K.plug a) := rfl
      have hp' : (Kont.appR f K).plug a' = .app f (K.plug a') := rfl
      rw [hp] at h; rw [hp']
      rw [Expr.pn_app] at h ⊢
      split at h
      · rename_i hf
        rw [if_pos hf]
        cases hl : isLitPair (K.plug a)
        · rw [pnArg_of_not hl] at h
          exact le_of_any (le_of_le_any h (any_top_append _))
        · obtain ⟨m, K', rfl⟩ := plug_litPair ha hl
          simp only [Kont.plug, Expr.val, Val.i32, pnArg] at h ⊢
          rw [append_le_iff] at h ⊢
          refine ⟨h.1, ?_⟩
          have := ih
          simp only [Kont.plug, Expr.val, Val.i32] at this
          have e₁ : ∀ Y, (Expr.pair (.prim (.lit (.i32 m))) Y).pn = {} ++ Y.pn := fun _ => rfl
          rw [e₁, e₁, empty_append, empty_append] at this
          exact this h.2
      · rename_i hf
        rw [if_neg hf]
        rw [append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩

/-- **A term's names performed are within its context's filling's**. -/
theorem plug_pn_ge {e : Expr} (he : PlainB e = true) : ∀ K : Kont, e.pn ≤ (K.plug e).pn := by
  intro K
  induction K with
  | hole => exact le_refl _
  | pairL K _ ih | letpair K _ ih | seq K _ ih =>
      exact le_trans ih (le_append_left _ _)
  | case K _ _ ih => exact le_trans ih (le_trans (le_append_left _ _) (le_append_left _ _))
  | pairR _ K ih => exact le_trans ih (le_append_right _ _)
  | inj₁ K ih | inj₂ K ih => exact ih
  | appR f K ih => exact le_trans ih (pn_app_ge _ _)
  | appL K v ih =>
      exact le_trans ih (pn_app_ge_fun _ (isPerform_plug he K))

/-! ### A context's frames, at any filling -/

/-- **A filling no frame reads**: neither a primitive (a frame's head) nor a pair (a handler's name
and rest). -/
def Hole (a : Expr) : Prop := (∀ p, a ≠ .prim p) ∧ ∀ x y, a ≠ .pair x y

theorem hole_var (i : Nat) : Hole (.var i) := ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem hole_app (f x : Expr) : Hole (.app f x) := ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem PlainB.hole {a : Expr} (ha : PlainB a = true) : Hole a :=
  ⟨plainB_not_prim ha, fun x y h => by subst h; simp [PlainB] at ha⟩

theorem hole_plug_not_prim {a : Expr} (ha : Hole a) : ∀ (K : Kont) (p : Prim), K.plug a ≠ .prim p
  | .hole, p => ha.1 p
  | .pairL .., _ | .pairR .., _ | .letpair .., _ | .case .., _ | .appR .., _ | .appL .., _
  | .seq .., _ | .inj₁ _, _ | .inj₂ _, _ => by simp [Kont.plug]

theorem isHnd_plug_hole {a : Expr} (ha : Hole a) (K : Kont) : isHnd (K.plug a) = false := by
  cases h : isHnd (K.plug a)
  · rfl
  · exact absurd (isHnd_iff.mp h) (hole_plug_not_prim ha K _)

theorem hole_plug_litPair {a : Expr} (ha : Hole a) :
    ∀ {K : Kont}, isLitPair (K.plug a) = true →
      ∃ (m : UInt32) (K' : Kont), K = .pairR (Val.i32 m) K'
  | .hole, h => by
      exfalso
      match a, h, ha with
      | .pair _ _, _, ha => exact ha.2 _ _ rfl
  | .pairL K' e, h => by
      exfalso
      obtain ⟨m, hm⟩ := isLitPair_pair h
      exact hole_plug_not_prim ha K' _ hm
  | .pairR v K', h => by
      obtain ⟨m, hm⟩ := isLitPair_pair h
      exact ⟨m, K', by congr; exact Val.ext hm⟩
  | .letpair .., h | .case .., h | .appR .., h | .appL .., h | .seq .., h | .inj₁ _, h
  | .inj₂ _, h => by simp [Kont.plug, isLitPair] at h

/-- **A context's frames, at another filling**: replacing a filling no frame reads keeps the bound
on the frames held, when the new filling's frames are within it. -/
theorem plug_hin_le {V : HIn} {a a' : Expr} (ha : Hole a) (hhin : a.hin ≤ V → a'.hin ≤ V) :
    ∀ K : Kont, (K.plug a).hin ≤ V → (K.plug a').hin ≤ V := by
  intro K
  induction K with
  | hole => exact hhin
  | pairL K e ih | letpair K e ih | seq K e ih =>
      intro h
      simp only [Kont.plug, Expr.hin, append_le_iff] at h ⊢; exact ⟨ih h.1, h.2⟩
  | pairR v K ih =>
      intro h
      simp only [Kont.plug, Expr.val, Expr.hin, append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩
  | case K e₁ e₂ ih =>
      intro h
      simp only [Kont.plug, Expr.hin, append_le_iff] at h ⊢; exact ⟨⟨ih h.1.1, h.1.2⟩, h.2⟩
  | inj₁ K ih | inj₂ K ih =>
      intro h
      simp only [Kont.plug, Expr.hin] at h ⊢; exact ih h
  | appL K v ih =>
      intro h
      have hp : (Kont.appL K v).plug a = .app (K.plug a) v.1 := rfl
      have hp' : (Kont.appL K v).plug a' = .app (K.plug a') v.1 := rfl
      rw [hp] at h; rw [hp']
      rw [hin_app_eq (isHnd_plug_hole ha K), append_le_iff] at h
      exact le_trans (hin_app_le _ _) (append_le (ih h.1) h.2)
  | appR f K ih =>
      intro h
      have hp : (Kont.appR f K).plug a = .app f (K.plug a) := rfl
      have hp' : (Kont.appR f K).plug a' = .app f (K.plug a') := rfl
      rw [hp] at h; rw [hp']
      rw [Expr.hin_app] at h ⊢
      split at h
      · rename_i hf
        rw [if_pos hf]
        cases hl : isLitPair (K.plug a)
        · rw [hndArg_of_not hl] at h
          exact le_of_any (le_of_le_any h (any_top_append _))
        · obtain ⟨m, K', rfl⟩ := hole_plug_litPair ha hl
          simp only [Kont.plug, Expr.val, Val.i32, hndArg] at h ⊢
          rw [append_le_iff] at h ⊢
          refine ⟨h.1, ?_⟩
          have := ih
          simp only [Kont.plug, Expr.val, Val.i32] at this
          have e₁ : ∀ Y, (Expr.pair (.prim (.lit (.i32 m))) Y).hin = {} ++ Y.hin := fun _ => rfl
          rw [e₁, e₁, empty_append, empty_append] at this
          exact this h.2
      · rename_i hf
        rw [if_neg hf]
        rw [append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩

/-- **A dead region holds a part of the region's frames.** -/
theorem plug_hin_dead {V : HIn} {a : Expr} (ha : Hole a) :
    ∀ K : Kont, (K.plug a).hin ≤ V → (K.dead.plug a).hin ≤ V := by
  intro K
  induction K with
  | hole => exact id
  | pairL K e ih | letpair K e ih | seq K e ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.hin, append_le_iff] at h ⊢; exact ⟨ih h.1, h.2⟩
  | pairR v K ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.val, Expr.hin, append_le_iff] at h ⊢
      exact ⟨h.1, ih h.2⟩
  | case K e₁ e₂ ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.hin, append_le_iff] at h ⊢
      exact ⟨⟨ih h.1.1, h.1.2⟩, h.2⟩
  | inj₁ K ih | inj₂ K ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.hin] at h ⊢; exact ih h
  | appL K v ih =>
      intro h
      have hp : (Kont.appL K v).plug a = .app (K.plug a) v.1 := rfl
      have hp' : (Kont.appL K v).dead.plug a = .app (K.dead.plug a) v.1 := rfl
      rw [hp] at h; rw [hp']
      rw [hin_app_eq (isHnd_plug_hole ha K), append_le_iff] at h
      exact le_trans (hin_app_le _ _) (append_le (ih h.1) h.2)
  | appR f K ih =>
      intro h
      have hp : (Kont.appR f K).plug a = .app f (K.plug a) := rfl
      rw [hp] at h
      simp only [Kont.dead]
      split
      · exact ih (le_trans (hin_app_ge _ _) h)
      · show (Expr.app f (K.dead.plug a)).hin ≤ V
        rw [Expr.hin_app] at h ⊢
        split at h
        · rename_i hf
          rw [if_pos hf]
          cases hl : isLitPair (K.plug a)
          · rw [hndArg_of_not hl] at h
            exact le_of_any (le_of_le_any h (any_top_append _))
          · obtain ⟨m, K', rfl⟩ := hole_plug_litPair ha hl
            simp only [Kont.dead, Kont.plug, Expr.val, Val.i32, hndArg] at h ⊢
            rw [append_le_iff] at h ⊢
            refine ⟨h.1, ?_⟩
            have := ih
            simp only [Kont.dead, Kont.plug, Expr.val, Val.i32] at this
            have e₁ : ∀ Y, (Expr.pair (.prim (.lit (.i32 m))) Y).hin = {} ++ Y.hin := fun _ => rfl
            rw [e₁, e₁, empty_append, empty_append] at this
            exact this h.2
        · rename_i hf
          rw [if_neg hf]
          rw [append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩

/-- **A shifted context's frames are the context's.** -/
theorem plug_hin_shift {V : HIn} {a a' : Expr} (ha : Hole a) (h' : a'.hin ≤ V)
    {K : Kont} (h : (K.plug a).hin ≤ V) (d : Nat) : ((K.shift d 0).plug a').hin ≤ V := by
  have h₀ := plug_hin_le ha (a' := .var d) (fun _ => empty_le _) K h
  have h₁ : ((K.plug (.var d)).shift d 0).hin ≤ V := by rw [hin_shift]; exact h₀
  rw [Kont.plug_shift] at h₁
  simp only [Expr.shift, Nat.not_lt_zero, if_false] at h₁
  exact plug_hin_le (hole_var _) (fun _ => h') _ h₁

theorem isPerform_plug_hole {a : Expr} (ha : Hole a) (K : Kont) : isPerform (K.plug a) = false := by
  cases h : isPerform (K.plug a)
  · rfl
  · exact absurd (isPerform_iff.mp h) (hole_plug_not_prim ha K _)

/-- **A context's names performed, at another filling**. -/
theorem plug_pn_hole {V : HIn} {a a' : Expr} (ha : Hole a) (hpn : a.pn ≤ V → a'.pn ≤ V) :
    ∀ K : Kont, (K.plug a).pn ≤ V → (K.plug a').pn ≤ V := by
  intro K
  induction K with
  | hole => exact hpn
  | pairL K e ih | letpair K e ih | seq K e ih =>
      intro h
      simp only [Kont.plug, Expr.pn, append_le_iff] at h ⊢; exact ⟨ih h.1, h.2⟩
  | pairR v K ih =>
      intro h
      simp only [Kont.plug, Expr.val, Expr.pn, append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩
  | case K e₁ e₂ ih =>
      intro h
      simp only [Kont.plug, Expr.pn, append_le_iff] at h ⊢; exact ⟨⟨ih h.1.1, h.1.2⟩, h.2⟩
  | inj₁ K ih | inj₂ K ih =>
      intro h
      simp only [Kont.plug, Expr.pn] at h ⊢; exact ih h
  | appL K v ih =>
      intro h
      have hp : (Kont.appL K v).plug a = .app (K.plug a) v.1 := rfl
      have hp' : (Kont.appL K v).plug a' = .app (K.plug a') v.1 := rfl
      rw [hp] at h; rw [hp']
      rw [pn_app_eq (isPerform_plug_hole ha K), append_le_iff] at h
      exact le_trans (pn_app_le _ _) (append_le (ih h.1) h.2)
  | appR f K ih =>
      intro h
      have hp : (Kont.appR f K).plug a = .app f (K.plug a) := rfl
      have hp' : (Kont.appR f K).plug a' = .app f (K.plug a') := rfl
      rw [hp] at h; rw [hp']
      rw [Expr.pn_app] at h ⊢
      split at h
      · rename_i hf
        rw [if_pos hf]
        cases hl : isLitPair (K.plug a)
        · rw [pnArg_of_not hl] at h
          exact le_of_any (le_of_le_any h (any_top_append _))
        · obtain ⟨m, K', rfl⟩ := hole_plug_litPair ha hl
          simp only [Kont.plug, Expr.val, Val.i32, pnArg] at h ⊢
          rw [append_le_iff] at h ⊢
          refine ⟨h.1, ?_⟩
          have := ih
          simp only [Kont.plug, Expr.val, Val.i32] at this
          have e₁ : ∀ Y, (Expr.pair (.prim (.lit (.i32 m))) Y).pn = {} ++ Y.pn := fun _ => rfl
          rw [e₁, e₁, empty_append, empty_append] at this
          exact this h.2
      · rename_i hf
        rw [if_neg hf]
        rw [append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩

/-- **A dead region performs a part of the region's names.** -/
theorem plug_pn_dead {V : HIn} {a : Expr} (ha : Hole a) :
    ∀ K : Kont, (K.plug a).pn ≤ V → (K.dead.plug a).pn ≤ V := by
  intro K
  induction K with
  | hole => exact id
  | pairL K e ih | letpair K e ih | seq K e ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.pn, append_le_iff] at h ⊢; exact ⟨ih h.1, h.2⟩
  | pairR v K ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.val, Expr.pn, append_le_iff] at h ⊢
      exact ⟨h.1, ih h.2⟩
  | case K e₁ e₂ ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.pn, append_le_iff] at h ⊢
      exact ⟨⟨ih h.1.1, h.1.2⟩, h.2⟩
  | inj₁ K ih | inj₂ K ih =>
      intro h
      simp only [Kont.dead, Kont.plug, Expr.pn] at h ⊢; exact ih h
  | appL K v ih =>
      intro h
      have hp : (Kont.appL K v).plug a = .app (K.plug a) v.1 := rfl
      have hp' : (Kont.appL K v).dead.plug a = .app (K.dead.plug a) v.1 := rfl
      rw [hp] at h; rw [hp']
      rw [pn_app_eq (isPerform_plug_hole ha K), append_le_iff] at h
      exact le_trans (pn_app_le _ _) (append_le (ih h.1) h.2)
  | appR f K ih =>
      intro h
      have hp : (Kont.appR f K).plug a = .app f (K.plug a) := rfl
      rw [hp] at h
      simp only [Kont.dead]
      split
      · exact ih (le_trans (pn_app_ge _ _) h)
      · show (Expr.app f (K.dead.plug a)).pn ≤ V
        rw [Expr.pn_app] at h ⊢
        split at h
        · rename_i hf
          rw [if_pos hf]
          cases hl : isLitPair (K.plug a)
          · rw [pnArg_of_not hl] at h
            exact le_of_any (le_of_le_any h (any_top_append _))
          · obtain ⟨m, K', rfl⟩ := hole_plug_litPair ha hl
            simp only [Kont.dead, Kont.plug, Expr.val, Val.i32, pnArg] at h ⊢
            rw [append_le_iff] at h ⊢
            refine ⟨h.1, ?_⟩
            have := ih
            simp only [Kont.dead, Kont.plug, Expr.val, Val.i32] at this
            have e₁ : ∀ Y, (Expr.pair (.prim (.lit (.i32 m))) Y).pn = {} ++ Y.pn := fun _ => rfl
            rw [e₁, e₁, empty_append, empty_append] at this
            exact this h.2
        · rename_i hf
          rw [if_neg hf]
          rw [append_le_iff] at h ⊢; exact ⟨h.1, ih h.2⟩

/-- **A shifted context performs the context's names.** -/
theorem plug_pn_shift {V : HIn} {a a' : Expr} (ha : Hole a) (h' : a'.pn ≤ V)
    {K : Kont} (h : (K.plug a).pn ≤ V) (d : Nat) : ((K.shift d 0).plug a').pn ≤ V := by
  have h₀ := plug_pn_hole ha (a' := .var d) (fun _ => empty_le _) K h
  have h₁ : ((K.plug (.var d)).shift d 0).pn ≤ V := by rw [pn_shift]; exact h₀
  rw [Kont.plug_shift] at h₁
  simp only [Expr.shift, Nat.not_lt_zero, if_false] at h₁
  exact plug_pn_hole (hole_var _) (fun _ => h') _ h₁

/-! ### The terms a head step builds -/

theorem hin_app_of {V : HIn} {f x : Expr} (hf : f.hin ≤ V) (hx : x.hin ≤ V) :
    (Expr.app f x).hin ≤ V := le_trans (hin_app_le _ _) (append_le hf hx)

theorem pn_app_of {V : HIn} {f x : Expr} (hf : f.pn ≤ V) (hx : x.pn ≤ V) :
    (Expr.app f x).pn ≤ V := le_trans (pn_app_le _ _) (append_le hf hx)

theorem hin_app_inv {V : HIn} {f x : Expr} (hf : isHnd f = false) (h : (Expr.app f x).hin ≤ V) :
    f.hin ≤ V ∧ x.hin ≤ V := by
  rw [hin_app_eq hf, append_le_iff] at h; exact h

theorem pn_app_inv {V : HIn} {f x : Expr} (hf : isPerform f = false) (h : (Expr.app f x).pn ≤ V) :
    f.pn ≤ V ∧ x.pn ≤ V := by
  rw [pn_app_eq hf, append_le_iff] at h; exact h

theorem hin_lit (c : IntLit) : (Expr.prim (.lit c)).hin = {} := rfl
theorem pn_lit (c : IntLit) : (Expr.prim (.lit c)).pn = {} := rfl
theorem hin_i32 (n : UInt32) : (Val.i32 n).1.hin = {} := rfl
theorem pn_i32 (n : UInt32) : (Val.i32 n).1.pn = {} := rfl

/-- A bound holds what a term with none of its frames holds. -/
theorem le_of_eq_empty {a V : HIn} (h : a = {}) : a ≤ V := h ▸ empty_le _

theorem hndArg_shift (x : Expr) (d c : Nat) : hndArg (x.shift d c) = hndArg x := by
  cases hx : isLitPair x
  · rw [hndArg_of_not (by rw [isLitPair_shift]; exact hx), hndArg_of_not hx, hin_shift]
  · match x, hx with
    | .pair (.prim (.lit (.i32 m))) X, _ => simp only [Expr.shift, hndArg, hin_shift d X]

theorem pnArg_shift (x : Expr) (d c : Nat) : pnArg (x.shift d c) = pnArg x := by
  cases hx : isLitPair x
  · rw [pnArg_of_not (by rw [isLitPair_shift]; exact hx), pnArg_of_not hx, pn_shift]
  · match x, hx with
    | .pair (.prim (.lit (.i32 m))) X, _ => simp only [Expr.shift, pnArg, pn_shift d X]

/-- A handler frame's frames: its head's, by its name and rest, and its body's. -/
theorem hin_hndE (H : Val) (e : Expr) : (hndE H e).hin = hndArg H.1 ++ e.hin := by
  show (Expr.app (.app (.prim .hnd) H.1) e).hin = _
  rw [hin_app_eq rfl, Expr.hin_app]; rfl

theorem pn_hndE (H : Val) (e : Expr) : (hndE H e).pn = H.1.pn ++ e.pn := by
  show (Expr.app (.app (.prim .hnd) H.1) e).pn = _
  rw [pn_app_eq rfl, pn_app_eq rfl]
  show ({} ++ H.1.pn) ++ e.pn = _
  rw [empty_append]

theorem hndArg_hndVal (n : UInt32) (qs hr hs : Val) :
    hndArg (BoLo.hndVal n qs hr hs).1 = HIn.one n ++ (Val.pair qs (Val.pair hr hs)).1.hin := rfl

theorem fl_hndE_hndVal (n : UInt32) (qs hr hs : Val) (e : Expr) :
    (hndE (BoLo.hndVal n qs hr hs) e).fl = (Val.pair qs (Val.pair hr hs)).1.fl ++ e.hin :=
  fl_hnd_app n _ e

/-- What flows from a handler frame holds its body's frames. -/
theorem fl_hndE_ge (H : Val) (e : Expr) : e.hin ≤ (hndE H e).fl := by
  show e.hin ≤ (Expr.app (.app (.prim .hnd) H.1) e).fl
  cases hl : isLitPair H.1
  · have h₁ := (app_fl_ge e (f := .app (.prim .hnd) H.1) rfl).1
    rw [fh_app] at h₁
    simp only at h₁
    split at h₁
    · rename_i heq; rw [heq] at hl; simp [isLitPair] at hl
    · rw [fl_hnd_nonlit hl] at h₁
      exact le_of_any (le_of_le_any h₁ (any_top_append _))
  · match H, hl with
    | ⟨.pair (.prim (.lit (.i32 m))) X, _⟩, _ =>
        show e.hin ≤ (Expr.app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 m))) X)) e).fl
        rw [fl_hnd_app]; exact le_append_right _ _

theorem hin_ubindE (ND : Val) (e : Expr) : (BoLo.ubindE ND e).hin = HIn.final ++ ND.1.hin ++ e.hin :=
  rfl

theorem fl_ubindE (ND : Val) (e : Expr) : (BoLo.ubindE ND e).fl = ND.1.fl ++ e.fl :=
  fl_ubind_app _ _

theorem pn_ubindE (ND : Val) (e : Expr) : (BoLo.ubindE ND e).pn = {} ++ ND.1.pn ++ e.pn := by
  show (Expr.app (.app (.prim .ubind) ND.1) e).pn = _
  rw [pn_app_eq rfl, pn_app_eq rfl]; rfl

theorem hin_cfinE (st : Val) (e : Expr) : (BoLo.cfinE st e).hin = HIn.final ++ st.1.hin ++ e.hin :=
  rfl

theorem fl_cfinE (st : Val) (e : Expr) : (BoLo.cfinE st e).fl = st.1.fl ++ e.fl := fl_cfin_app _ _

theorem pn_cfinE (st : Val) (e : Expr) : (BoLo.cfinE st e).pn = {} ++ st.1.pn ++ e.pn := by
  show (Expr.app (.app (.prim .cfin) st.1) e).pn = _
  rw [pn_app_eq rfl, pn_app_eq rfl]; rfl

theorem hin_ccatchE (e : Expr) : (BoLo.ccatchE e).hin = HIn.one 0 ++ e.hin := rfl

theorem fl_ccatchE (e : Expr) : (BoLo.ccatchE e).fl = e.fl := fl_ccatch_app _

theorem pn_ccatchE (e : Expr) : (BoLo.ccatchE e).pn = {} ++ e.pn := by
  show (Expr.app (.prim .ccatch) e).pn = _
  rw [pn_app_eq rfl]; rfl

theorem hin_raiseE (p : Expr) : (BoLo.raiseE p).hin = {} ++ p.hin := rfl

theorem pn_raiseE (p : Expr) : (BoLo.raiseE p).pn = {} ++ p.pn := by
  show (Expr.app (.prim .raise) p).pn = _
  rw [pn_app_eq rfl]; rfl

theorem fl_raiseE (p : Expr) : (BoLo.raiseE p).fl = {} ++ p.fl := by
  show (Expr.app (.prim .raise) p).fl = _
  rw [fl_prim_app _ _ (by decide) (by decide)]; rfl

theorem hin_performE (p : Expr) : (BoLo.performE p).hin = {} ++ p.hin := rfl

theorem fl_performE (p : Expr) : (BoLo.performE p).fl = {} ++ p.fl := by
  show (Expr.app (.prim .perform) p).fl = _
  rw [fl_prim_app _ _ (by decide) (by decide)]; rfl

theorem pn_performE_payload (n i : UInt32) (v : Val) :
    (BoLo.performE (.val (BoLo.opPayload n i v))).pn = HIn.one n ++ (v.1.pn) := by
  show HIn.one n ++ ({} ++ v.1.pn) = _
  rw [empty_append]

theorem hin_opPayload (n i : UInt32) (v : Val) : (BoLo.opPayload n i v).1.hin = {} ++ ({} ++ v.1.hin) :=
  rfl

theorem pn_opPayload (n i : UInt32) (v : Val) : (BoLo.opPayload n i v).1.pn = {} ++ ({} ++ v.1.pn) :=
  rfl

theorem hin_freeE (e : Expr) : (BoLo.freeE e).hin = {} ++ e.hin := rfl
theorem pn_freeE (e : Expr) : (BoLo.freeE e).pn = {} ++ e.pn := by
  show (Expr.app (.prim .free) e).pn = _
  rw [pn_app_eq rfl]; rfl

theorem hin_stuckE : BoLo.stuckE.hin = {} := rfl
theorem pn_stuckE : BoLo.stuckE.pn = {} := rfl

theorem hin_errVal (err : Option Val) :
    (BoLo.errVal err).1.hin = match err with | none => {} | some E => E.1.hin := by
  cases err <;> rfl

theorem pn_errVal (err : Option Val) :
    (BoLo.errVal err).1.pn = match err with | none => {} | some E => E.1.pn := by
  cases err <;> rfl

/-- A clause of a tuple holds a part of its frames. -/
theorem hin_clauseAt : ∀ (e : Expr) (i : Nat) {c : Val}, BoLo.clauseAt e i = some c →
    c.1.hin ≤ e.hin ∧ c.1.pn ≤ e.pn
  | .pair c' r, 0, c, h => by
      simp only [BoLo.clauseAt] at h
      split at h
      · cases h; exact ⟨le_append_left _ _, le_append_left _ _⟩
      · cases h
  | .pair _ r, i + 1, c, h => by
      simp only [BoLo.clauseAt] at h
      have := hin_clauseAt r i h
      exact ⟨le_trans this.1 (le_append_right _ _), le_trans this.2 (le_append_right _ _)⟩
  | .var _, _, _, h | .unit, _, _, h | .inj₁ _, _, _, h | .inj₂ _, _, _, h
  | .lam _, _, _, h | .loc _, _, _, h | .prim _, _, _, h | .seq _ _, _, _, h
  | .letpair _ _, _, _, h | .case _ _ _, _, _, h | .app _ _, _, _, h => by
      simp [BoLo.clauseAt] at h

theorem hin_cancel_none : (BoLo.raiseE (.val (BoLo.cancelVal none))).hin = {} := rfl

theorem pn_cancel_none : (BoLo.raiseE (.val (BoLo.cancelVal none))).pn = {} := by
  rw [pn_raiseE]; rfl

theorem hndArg_val_shift (H : Val) (d c : Nat) : hndArg (H.shift d c).1 = hndArg H.1 := by
  rw [Val.val_shift, hndArg_shift]

/-- Close a conjunction of bounds from the hypotheses, every leaf a hypothesis or the empty set. -/
macro "hin_close" : tactic =>
  `(tactic| repeat' (first | exact HIn.empty_le _ | assumption | apply And.intro))

/-- **A continuation holds its handler and its context's frames**, and the cancel delimiter of its
cancel; all of it is code a value holds. -/
theorem kappaAt_le {V : HIn} (t : UInt32) {H : Val} {K : Kont} {x : Expr} (hx : Hole x)
    (hH : hndArg H.1 ≤ V) (hK : (K.plug x).hin ≤ V) (h0 : HIn.one 0 ≤ V) :
    (BoLo.kappaAt t H K).hin ≤ V ∧ (BoLo.kappaAt t H K).fl ≤ V := by
  have hres : ∀ d, ((K.shift d 0).plug (.var 0)).hin ≤ V := fun d =>
    plug_hin_shift hx (empty_le _) hK d
  have hcan : ∀ d, ((K.dead.shift d 0).plug (BoLo.raiseE (.val (BoLo.cancelVal none)))).hin ≤ V :=
    fun d => plug_hin_shift hx (by rw [hin_cancel_none]; exact empty_le _)
      (plug_hin_dead hx K hK) d
  have hH' : ∀ d, hndArg (H.shift d 0).1 ≤ V := fun d => by rw [hndArg_val_shift]; exact hH
  have := hH' 3; have := hH' 4; have := hres 3; have := hres 4; have := hcan 2; have := hcan 3
  have body : ∀ (B : Expr), B.hin ≤ V → (Expr.lam B).hin ≤ V ∧ (Expr.lam B).fl ≤ V :=
    fun B h => ⟨h, h⟩
  unfold BoLo.kappaAt
  split
  · -- must resume
    refine ⟨hin_app_of ?_ (hin_app_of (empty_le _) (empty_le _)), ?_⟩
    · show (Expr.case _ _ _).hin ≤ V
      simp only [Expr.val, Val.lam, Expr.hin, append_le_iff, hin_freeE, hin_hndE]
      hin_close
    · show (Expr.app (.lam _) _).fl ≤ V
      rw [fl_lam_app, append_le_iff]
      refine ⟨?_, ?_⟩
      · show (Expr.case _ _ _).hin ≤ V
        simp only [Expr.val, Val.lam, Expr.hin, append_le_iff, hin_freeE, hin_hndE]
        hin_close
      · exact le_trans (fl_le_hin _) (hin_app_of (empty_le _) (empty_le _))
  · split
    · -- cancellable
      refine ⟨hin_app_of ?_ (hin_app_of (empty_le _) (empty_le _)), ?_⟩
      · show (Expr.case _ _ _).hin ≤ V
        simp only [Expr.val, Val.lam, Expr.hin, append_le_iff, hin_freeE, hin_hndE, hin_ccatchE, if_true]
        hin_close
      · show (Expr.app (.lam _) _).fl ≤ V
        rw [fl_lam_app, append_le_iff]
        refine ⟨?_, ?_⟩
        · show (Expr.case _ _ _).hin ≤ V
          simp only [Expr.val, Val.lam, Expr.hin, append_le_iff, hin_freeE, hin_hndE, hin_ccatchE, if_true]
          hin_close
        · exact le_trans (fl_le_hin _) (hin_app_of (empty_le _) (empty_le _))
    · -- unrestricted
      apply body
      simp only [Expr.val, Val.lam, Expr.hin, append_le_iff, hin_hndE, hin_ccatchE]
      hin_close

/-- **A continuation performs its handler's and its context's names**. -/
theorem kappaAt_pn {V : HIn} (t : UInt32) {H : Val} {K : Kont} {x : Expr} (hx : Hole x)
    (hH : H.1.pn ≤ V) (hK : (K.plug x).pn ≤ V) : (BoLo.kappaAt t H K).pn ≤ V := by
  have hres : ∀ d, ((K.shift d 0).plug (.var 0)).pn ≤ V := fun d =>
    plug_pn_shift hx (empty_le _) hK d
  have hcan : ∀ d, ((K.dead.shift d 0).plug (BoLo.raiseE (.val (BoLo.cancelVal none)))).pn ≤ V :=
    fun d => plug_pn_shift hx (by rw [pn_cancel_none]; exact empty_le _)
      (plug_pn_dead hx K hK) d
  have hH' : ∀ d, (H.shift d 0).1.pn ≤ V := fun d => by rw [pn_shift_val]; exact hH
  have := hH' 3; have := hH' 4; have := hres 3; have := hres 4; have := hcan 2; have := hcan 3
  unfold BoLo.kappaAt
  split
  · refine pn_app_of ?_ (pn_app_of (empty_le _) (empty_le _))
    show (Expr.case _ _ _).pn ≤ V
    simp only [Expr.val, Val.lam, Expr.pn, append_le_iff, pn_freeE, pn_hndE]
    hin_close
  · split
    · refine pn_app_of ?_ (pn_app_of (empty_le _) (empty_le _))
      show (Expr.case _ _ _).pn ≤ V
      simp only [Expr.val, Val.lam, Expr.pn, append_le_iff, pn_freeE, pn_hndE, pn_ccatchE, if_true]
      hin_close
    · show (Expr.case _ _ _).pn ≤ V
      simp only [Expr.val, Val.lam, Expr.pn, append_le_iff, pn_hndE, pn_ccatchE]
      hin_close

theorem hin_pair_of {V : HIn} {a b : Expr} (ha : a.hin ≤ V) (hb : b.hin ≤ V) :
    (Expr.pair a b).hin ≤ V := append_le ha hb
theorem hin_seq_of {V : HIn} {a b : Expr} (ha : a.hin ≤ V) (hb : b.hin ≤ V) :
    (Expr.seq a b).hin ≤ V := append_le ha hb
theorem hin_letpair_of {V : HIn} {a b : Expr} (ha : a.hin ≤ V) (hb : b.hin ≤ V) :
    (Expr.letpair a b).hin ≤ V := append_le ha hb
theorem hin_case_of {V : HIn} {a b c : Expr} (ha : a.hin ≤ V) (hb : b.hin ≤ V) (hc : c.hin ≤ V) :
    (Expr.case a b c).hin ≤ V := append_le (append_le ha hb) hc
theorem hin_inj₁_of {V : HIn} {a : Expr} (ha : a.hin ≤ V) : (Expr.inj₁ a).hin ≤ V := ha
theorem hin_inj₂_of {V : HIn} {a : Expr} (ha : a.hin ≤ V) : (Expr.inj₂ a).hin ≤ V := ha
theorem hin_lam_of {V : HIn} {a : Expr} (ha : a.hin ≤ V) : (Expr.lam a).hin ≤ V := ha
theorem pn_pair_of {V : HIn} {a b : Expr} (ha : a.pn ≤ V) (hb : b.pn ≤ V) :
    (Expr.pair a b).pn ≤ V := append_le ha hb
theorem pn_seq_of {V : HIn} {a b : Expr} (ha : a.pn ≤ V) (hb : b.pn ≤ V) :
    (Expr.seq a b).pn ≤ V := append_le ha hb
theorem pn_letpair_of {V : HIn} {a b : Expr} (ha : a.pn ≤ V) (hb : b.pn ≤ V) :
    (Expr.letpair a b).pn ≤ V := append_le ha hb
theorem pn_case_of {V : HIn} {a b c : Expr} (ha : a.pn ≤ V) (hb : b.pn ≤ V) (hc : c.pn ≤ V) :
    (Expr.case a b c).pn ≤ V := append_le (append_le ha hb) hc
theorem pn_inj₁_of {V : HIn} {a : Expr} (ha : a.pn ≤ V) : (Expr.inj₁ a).pn ≤ V := ha
theorem pn_inj₂_of {V : HIn} {a : Expr} (ha : a.pn ≤ V) : (Expr.inj₂ a).pn ≤ V := ha
theorem pn_lam_of {V : HIn} {a : Expr} (ha : a.pn ≤ V) : (Expr.lam a).pn ≤ V := ha
theorem hin_shift_of {V : HIn} {v : Val} (h : v.1.hin ≤ V) (d c : Nat) : (v.shift d c).1.hin ≤ V := by
  rw [hin_shift_val]; exact h
theorem pn_shift_of {V : HIn} {v : Val} (h : v.1.pn ≤ V) (d c : Nat) : (v.shift d c).1.pn ≤ V := by
  rw [pn_shift_val]; exact h

/-- Bound a term built from parts within a bound: through its formers, each leaf a hypothesis, a
shifted hypothesis, or a term with no frames. -/
macro "bound" : tactic =>
  `(tactic| repeat' (first
    | assumption | exact HIn.empty_le _
    | exact le_of_eq_empty rfl
    | apply hin_shift_of | apply pn_shift_of
    | apply hin_app_of | apply hin_pair_of | apply hin_seq_of | apply hin_letpair_of
    | apply hin_case_of | apply hin_inj₁_of | apply hin_inj₂_of | apply hin_lam_of
    | apply pn_app_of | apply pn_pair_of | apply pn_seq_of | apply pn_letpair_of
    | apply pn_case_of | apply pn_inj₁_of | apply pn_inj₂_of | apply pn_lam_of))

theorem tabFill_le {V W : HIn} {f : Val} (hf : f.1.hin ≤ V) (hp : f.1.pn ≤ W) (ℓ : Loc) (n : UInt32) :
    ∀ i k, (tabFill f ℓ n i k).hin ≤ V ∧ (tabFill f ℓ n i k).pn ≤ W
  | _, 0 => ⟨le_of_eq_empty rfl, le_of_eq_empty rfl⟩
  | i, k + 1 => by
      have ih := tabFill_le hf hp ℓ n (i + 1) k
      obtain ⟨ih₁, ih₂⟩ := ih
      simp only [tabFill]
      exact ⟨by bound, by bound⟩

theorem dropFill_le {V W : HIn} {f : Val} (hf : f.1.hin ≤ V) (hp : f.1.pn ≤ W) (ℓ : Loc) :
    ∀ i k, (dropFill f ℓ i k).hin ≤ V ∧ (dropFill f ℓ i k).pn ≤ W
  | _, 0 => ⟨le_of_eq_empty rfl, le_of_eq_empty rfl⟩
  | i, k + 1 => by
      have ih := dropFill_le hf hp ℓ (i + 1) k
      obtain ⟨ih₁, ih₂⟩ := ih
      simp only [dropFill]
      exact ⟨by bound, by bound⟩

theorem countNext_le {V W : HIn} {f s : Val} (hf : f.1.hin ≤ V) (hs : s.1.hin ≤ V)
    (hpf : f.1.pn ≤ W) (hps : s.1.pn ≤ W) (n i : UInt32) :
    (countNext f n i s).hin ≤ V ∧ (countNext f n i s).pn ≤ W := by
  simp only [countNext]
  split
  · exact ⟨by bound, by bound⟩
  · exact ⟨hs, hps⟩

theorem countTryNext_le {V W : HIn} {f s : Val} (hf : f.1.hin ≤ V) (hs : s.1.hin ≤ V)
    (hpf : f.1.pn ≤ W) (hps : s.1.pn ≤ W) (n i : UInt32) :
    (countTryNext f n i s).hin ≤ V ∧ (countTryNext f n i s).pn ≤ W := by
  simp only [countTryNext]
  split
  · exact ⟨by bound, by bound⟩
  · exact ⟨hs, hps⟩

theorem boundedFixNext_le {V W : HIn} {s a : Val} (hs : s.1.hin ≤ V) (ha : a.1.hin ≤ V)
    (hps : s.1.pn ≤ W) (hpa : a.1.pn ≤ W) (k : UInt32) :
    (boundedFixNext s k a).hin ≤ V ∧ (boundedFixNext s k a).pn ≤ W := by
  simp only [boundedFixNext, fixSelf]
  split
  · exact ⟨by bound, by bound⟩
  · exact ⟨by bound, by bound⟩

theorem iterNext_le {V W : HIn} {f s : Val} (hf : f.1.hin ≤ V) (hs : s.1.hin ≤ V)
    (hpf : f.1.pn ≤ W) (hps : s.1.pn ≤ W) (hdiv : HIn.one divEff ≤ W) :
    (iterNext f s).hin ≤ V ∧ (iterNext f s).pn ≤ W := by
  have ht : tickE.pn ≤ W := by
    show HIn.one divEff ++ ({} ++ ({} ++ {})) ≤ W
    exact append_le hdiv (empty_le _)
  simp only [iterNext, iterTurn]
  exact ⟨by bound, by bound⟩

theorem idxAns_le (ℓ : Loc) (n i : UInt32) : (idxAns ℓ n i).1.hin = {} ∧ (idxAns ℓ n i).1.pn = {} := by
  simp only [idxAns]; split <;> exact ⟨rfl, rfl⟩

theorem splitAns_le (ℓ : Loc) (n i : UInt32) :
    (splitAns ℓ n i).1.hin = {} ∧ (splitAns ℓ n i).1.pn = {} := by
  simp only [splitAns]; split <;> exact ⟨rfl, rfl⟩

/-- **A host's answer holds no code.** -/
theorem host_le (H : Host) (op : HostOp) {v r : Val} (h : H.call op v = some r) :
    r.1.hin = {} ∧ r.1.pn = {} := by
  have hi32 : ∀ n, (Val.i32 n).1.hin = {} ∧ (Val.i32 n).1.pn = {} := fun _ => ⟨rfl, rfl⟩
  have hi64 : ∀ n, (Val.i64 n).1.hin = {} ∧ (Val.i64 n).1.pn = {} := fun _ => ⟨rfl, rfl⟩
  have hu8 : ∀ n, (Val.u8 n).1.hin = {} ∧ (Val.u8 n).1.pn = {} := fun _ => ⟨rfl, rfl⟩
  have hf32 : ∀ n, (Val.f32 n).1.hin = {} ∧ (Val.f32 n).1.pn = {} := fun _ => ⟨rfl, rfl⟩
  have hf64 : ∀ n, (Val.f64 n).1.hin = {} ∧ (Val.f64 n).1.pn = {} := fun _ => ⟨rfl, rfl⟩
  have hob : ∀ w n, (Val.ofBits w n).1.hin = {} ∧ (Val.ofBits w n).1.pn = {} := fun w _ => by
    cases w <;> exact ⟨rfl, rfl⟩
  have hbool : ∀ b, (Val.bool b).1.hin = {} ∧ (Val.bool b).1.pn = {} := fun b => by
    cases b <;> exact ⟨rfl, rfl⟩
  have hopt : ∀ (o : Option Val), (∀ v, o = some v → v.1.hin = {} ∧ v.1.pn = {}) →
      (Val.opt o).1.hin = {} ∧ (Val.opt o).1.pn = {} := fun o ho => by
    cases o with
    | none => exact ⟨rfl, rfl⟩
    | some v => exact ho v rfl
  cases op with
  | bin w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi64 _
  | div w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hopt _ fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hopt _ fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi64 _
  | un w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | eqz w =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hbool _
      · obtain ⟨_, -, rfl⟩ := h; exact hbool _
  | rel w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
  | wrap =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | extend_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend32_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | wrap8 =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hu8 _
  | extend8_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | fbin f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, _, -, rfl⟩ := h; exact hob _ _
  | fun1 f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | frel f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
  | convert f i sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | trunc i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h
      exact hopt _ fun v hv => by
        simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hob _ _
  | trunc_sat i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | demote =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob .f32 _
  | promote =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob .f64 _
  | reinterpret_i f =>
      cases f <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> obtain ⟨_, -, rfl⟩ := h
      · exact hi32 _
      · exact hi64 _
  | reinterpret_f f =>
      cases f <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> obtain ⟨_, -, rfl⟩ := h
      · exact hob .f32 _
      · exact hob .f64 _

/-! ### Head steps -/

section heads
variable {ℍ : Host} [HostIs ℍ]

/-- A redex is plain. -/
theorem head_plain {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') : PlainB a = true := by
  cases h <;> rfl

theorem hole_raiseE (p : Expr) : Hole (BoLo.raiseE p) := hole_app _ _

theorem hole_performE (p : Expr) : Hole (BoLo.performE p) := hole_app _ _

theorem nonLit_app (f x : Expr) (h : isHnd (.app f x) = false) : NonLit (.app f x) := ⟨rfl, h⟩

/-- The frames a raise in a context holds: its payload's are the context's filling's. -/
theorem raise_hin {V : HIn} {K : Kont} {p : Val} (h : (K.plug (BoLo.raiseE (.val p))).hin ≤ V) :
    p.1.hin ≤ V := by
  have := le_trans (plug_hin_ge ⟨rfl, rfl⟩ K) h
  rw [hin_raiseE, empty_append] at this; exact this

theorem raise_pn {V : HIn} {K : Kont} {p : Val} (h : (K.plug (BoLo.raiseE (.val p))).pn ≤ V) :
    p.1.pn ≤ V := by
  have := le_trans (plug_pn_ge rfl K) h
  rw [pn_raiseE, empty_append] at this; exact this

theorem perform_hin {V : HIn} {K : Kont} {p : Val} (h : (K.plug (BoLo.performE (.val p))).hin ≤ V) :
    p.1.hin ≤ V := by
  have := le_trans (plug_hin_ge ⟨rfl, rfl⟩ K) h
  rw [hin_performE, empty_append] at this; exact this

theorem hin_cancelVal {V : HIn} {err : Option Val} (h : (BoLo.cancelVal err).1.hin ≤ V) :
    ∀ E, err = some E → E.1.hin ≤ V := by
  intro E hE; subst hE
  have : (BoLo.cancelVal (some E)).1.hin = {} ++ ({} ++ E.1.hin) := rfl
  rw [this, empty_append, empty_append] at h; exact h

theorem cancelVal_hin_of {V : HIn} {err : Option Val} (h : ∀ E, err = some E → E.1.hin ≤ V) :
    (BoLo.cancelVal err).1.hin ≤ V := by
  cases err with
  | none => exact le_of_eq_empty rfl
  | some E =>
      have : (BoLo.cancelVal (some E)).1.hin = {} ++ ({} ++ E.1.hin) := rfl
      rw [this, empty_append, empty_append]; exact h E rfl

theorem pn_cancelVal {V : HIn} {err : Option Val} (h : (BoLo.cancelVal err).1.pn ≤ V) :
    ∀ E, err = some E → E.1.pn ≤ V := by
  intro E hE; subst hE
  have : (BoLo.cancelVal (some E)).1.pn = {} ++ ({} ++ E.1.pn) := rfl
  rw [this, empty_append, empty_append] at h; exact h

theorem cancelVal_pn_of {V : HIn} {err : Option Val} (h : ∀ E, err = some E → E.1.pn ≤ V) :
    (BoLo.cancelVal err).1.pn ≤ V := by
  cases err with
  | none => exact le_of_eq_empty rfl
  | some E =>
      have : (BoLo.cancelVal (some E)).1.pn = {} ++ ({} ++ E.1.pn) := rfl
      rw [this, empty_append, empty_append]; exact h E rfl

theorem prim_app_hin {V : HIn} {p : Prim} {x : Expr} (hp : p ≠ .hnd)
    (h : (Expr.app (.prim p) x).hin ≤ V) : x.hin ≤ V :=
  (hin_app_inv (by cases p <;> first | rfl | exact absurd rfl hp) h).2

theorem prim_app_pn {V : HIn} {p : Prim} {x : Expr} (hp : p ≠ .perform)
    (h : (Expr.app (.prim p) x).pn ≤ V) : x.pn ≤ V :=
  (pn_app_inv (by cases p <;> first | rfl | exact absurd rfl hp) h).2

/-- **A head step keeps the frames held within a bound** holding the memory's values' and the
name `0`.  `[spec §19]` -/
theorem head_hin {V : HIn} (h0 : HIn.one 0 ≤ V) {μ μ' : Heap} {a a' : Expr}
    (hμ : ∀ ℓ v, μ ℓ = some v → v.1.hin ≤ V) (h : Head (ℍ := ℍ) μ a μ' a') (ha : a.hin ≤ V) :
    a'.hin ≤ V := by
  cases h with
  | beta b v =>
      obtain ⟨hb, hv⟩ := hin_app_inv rfl ha
      exact hin_subst b 0 v hb hv
  | alloc v ℓ _ => exact le_of_eq_empty rfl
  | free ℓ v hv => exact hμ ℓ v hv
  | load ℓ v hv => exact hμ ℓ v hv
  | store ℓ v w _ => exact le_of_eq_empty rfl
  | seq e => simp only [Expr.hin, append_le_iff] at ha; exact ha.2
  | letpair v₁ v₂ e =>
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at ha
      obtain ⟨⟨h₁, h₂⟩, he⟩ := ha
      exact hin_subst _ 0 v₁ (hin_subst e 0 _ he (hin_shift_of h₂ 1 0)) h₁
  | case₁ v e₁ e₂ =>
      simp only [Expr.hin, append_le_iff] at ha
      exact hin_subst e₁ 0 v ha.1.2 ha.1.1
  | case₂ v e₁ e₂ =>
      simp only [Expr.hin, append_le_iff] at ha
      exact hin_subst e₂ 0 v ha.2 ha.1.1
  | host op v r hr => exact le_of_eq_empty (host_le ℍ op hr).1
  | tab c f ℓ _ =>
      have hf := prim_app_hin (by decide) ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at hf
      exact (tabFill_le (W := HIn.top) hf.2 (le_of_any rfl) ℓ _ _ _).1
  | idx ℓ n i => exact le_of_eq_empty (idxAns_le ℓ n i).1
  | split ℓ n i => exact le_of_eq_empty (splitAns_le ℓ n i).1
  | drop f ℓ n =>
      have hf := prim_app_hin (by decide) ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at hf
      exact (dropFill_le (W := HIn.top) hf.1 (le_of_any rfl) ℓ _ _).1
  | count f n i s =>
      have hf := prim_app_hin (by decide) ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at hf
      exact (countNext_le (W := HIn.top) hf.1 hf.2.2.2 (le_of_any rfl) (le_of_any rfl) n i).1
  | countTry f n i s =>
      have hf := prim_app_hin (by decide) ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at hf
      exact (countTryNext_le (W := HIn.top) hf.1 hf.2.2.2 (le_of_any rfl) (le_of_any rfl) n i).1
  | boundedFix s k x =>
      have hf := prim_app_hin (by decide) ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at hf
      exact (boundedFixNext_le (W := HIn.top) hf.1 hf.2.2 (le_of_any rfl) (le_of_any rfl) k).1
  | iterate f s =>
      have hf := prim_app_hin (by decide) ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at hf
      exact (iterNext_le (W := HIn.top) hf.1 hf.2 (le_of_any rfl) (le_of_any rfl)
        (le_of_any rfl)).1
  | hret n qs hr hs w =>
      rw [hin_hndE, hndArg_hndVal] at ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at ha
      obtain ⟨⟨-, -, hhr, -⟩, hw⟩ := ha
      bound
  | hop n i qs hr hs c v K hc _ =>
      rw [hin_hndE] at ha
      obtain ⟨hH, hx⟩ := append_le_iff.mp ha
      have hH' := hH
      rw [hndArg_hndVal] at hH'
      simp only [Val.pair, Expr.hin, append_le_iff] at hH'
      have hcl := le_trans (hin_clauseAt _ _ hc).1 hH'.2.2.2
      have hv := perform_hin hx
      rw [hin_opPayload, empty_append, empty_append] at hv
      have hk := (kappaAt_le (BoLo.capTag qs.1 i.toNat) (hole_performE _) hH hx h0).1
      bound
  | hunwind n i qs hr hs c v K hc _ =>
      rw [hin_hndE] at ha
      obtain ⟨hH, hx⟩ := append_le_iff.mp ha
      rw [hndArg_hndVal] at hH
      simp only [Val.pair, Expr.hin, append_le_iff] at hH
      have hcl := le_trans (hin_clauseAt _ _ hc).1 hH.2.2.2
      have hv := raise_hin hx
      rw [hin_opPayload, empty_append, empty_append] at hv
      bound
  | uthen N D w =>
      rw [hin_ubindE] at ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at ha
      obtain ⟨⟨-, hN, -⟩, hw⟩ := ha
      bound
  | ufin N D n i v K _ _ =>
      rw [hin_ubindE] at ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at ha
      obtain ⟨⟨-, -, hD⟩, hx⟩ := ha
      have hp := raise_hin hx
      have hr : (BoLo.raiseE (.val (BoLo.opPayload n i v))).hin ≤ V := by
        rw [hin_raiseE]; exact append_le (empty_le _) hp
      bound
  | ufinC N D err K _ =>
      rw [hin_ubindE] at ha
      simp only [Expr.val, Val.pair, Expr.hin, append_le_iff] at ha
      obtain ⟨⟨hf, -, hD⟩, hx⟩ := ha
      have hp := raise_hin hx
      rw [hin_cfinE]
      exact append_le (append_le hf hp) (hin_app_of hD (empty_le _))
  | cfret err w =>
      rw [hin_cfinE, append_le_iff, append_le_iff] at ha
      rw [hin_raiseE]; exact append_le (empty_le _) ha.1.2
  | cferr err m j w K _ _ =>
      rw [hin_cfinE, append_le_iff, append_le_iff] at ha
      have hp := raise_hin ha.2
      rw [hin_raiseE]
      refine append_le (empty_le _) (cancelVal_hin_of fun E hE => ?_)
      cases err with
      | some E' =>
          simp only [BoLo.errNext, Option.or] at hE; cases hE
          exact hin_cancelVal ha.1.2 _ rfl
      | none =>
          simp only [BoLo.errNext, Option.or] at hE; cases hE; exact hp
  | cfcancel err err' K _ =>
      rw [hin_cfinE, append_le_iff, append_le_iff] at ha
      have hp := raise_hin ha.2
      rw [hin_raiseE]
      refine append_le (empty_le _) (cancelVal_hin_of fun E hE => ?_)
      cases err with
      | some E' =>
          simp only [Option.or] at hE; cases hE
          exact hin_cancelVal ha.1.2 _ rfl
      | none =>
          simp only [Option.or] at hE
          exact hin_cancelVal hp _ hE
  | cancel K _ => exact le_of_eq_empty rfl
  | creraise E K _ =>
      rw [hin_ccatchE, append_le_iff] at ha
      have hp := raise_hin ha.2
      rw [hin_raiseE]
      exact append_le (empty_le _) (hin_cancelVal hp _ rfl)

/-- **A head step keeps the names performed within a bound** holding the memory's values' and
the tick's name `divEff`.  `[spec §19]` -/
theorem head_pn {W : HIn} (hdiv : HIn.one divEff ≤ W) {μ μ' : Heap} {a a' : Expr}
    (hμ : ∀ ℓ v, μ ℓ = some v → v.1.pn ≤ W) (h : Head (ℍ := ℍ) μ a μ' a') (ha : a.pn ≤ W) :
    a'.pn ≤ W := by
  cases h with
  | beta b v =>
      obtain ⟨hb, hv⟩ := pn_app_inv rfl ha
      exact pn_subst b 0 v hb hv
  | alloc v ℓ _ => exact le_of_eq_empty rfl
  | free ℓ v hv => exact hμ ℓ v hv
  | load ℓ v hv => exact hμ ℓ v hv
  | store ℓ v w _ => exact le_of_eq_empty rfl
  | seq e => simp only [Expr.pn, append_le_iff] at ha; exact ha.2
  | letpair v₁ v₂ e =>
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at ha
      obtain ⟨⟨h₁, h₂⟩, he⟩ := ha
      exact pn_subst _ 0 v₁ (pn_subst e 0 _ he (pn_shift_of h₂ 1 0)) h₁
  | case₁ v e₁ e₂ =>
      simp only [Expr.pn, append_le_iff] at ha
      exact pn_subst e₁ 0 v ha.1.2 ha.1.1
  | case₂ v e₁ e₂ =>
      simp only [Expr.pn, append_le_iff] at ha
      exact pn_subst e₂ 0 v ha.2 ha.1.1
  | host op v r hr => exact le_of_eq_empty (host_le ℍ op hr).2
  | tab c f ℓ _ =>
      have hf := prim_app_pn (by decide) ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at hf
      exact (tabFill_le (V := HIn.top) (le_of_any rfl) hf.2 ℓ _ _ _).2
  | idx ℓ n i => exact le_of_eq_empty (idxAns_le ℓ n i).2
  | split ℓ n i => exact le_of_eq_empty (splitAns_le ℓ n i).2
  | drop f ℓ n =>
      have hf := prim_app_pn (by decide) ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at hf
      exact (dropFill_le (V := HIn.top) (le_of_any rfl) hf.1 ℓ _ _).2
  | count f n i s =>
      have hf := prim_app_pn (by decide) ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at hf
      exact (countNext_le (V := HIn.top) (le_of_any rfl) (le_of_any rfl) hf.1 hf.2.2.2 n i).2
  | countTry f n i s =>
      have hf := prim_app_pn (by decide) ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at hf
      exact (countTryNext_le (V := HIn.top) (le_of_any rfl) (le_of_any rfl) hf.1 hf.2.2.2 n i).2
  | boundedFix s k x =>
      have hf := prim_app_pn (by decide) ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at hf
      exact (boundedFixNext_le (V := HIn.top) (le_of_any rfl) (le_of_any rfl) hf.1 hf.2.2 k).2
  | iterate f s =>
      have hf := prim_app_pn (by decide) ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at hf
      exact (iterNext_le (V := HIn.top) (le_of_any rfl) (le_of_any rfl) hf.1 hf.2 hdiv).2
  | hret n qs hr hs w =>
      rw [pn_hndE] at ha
      simp only [BoLo.hndVal, Val.pair, Expr.val, Expr.pn, append_le_iff] at ha
      obtain ⟨⟨-, -, hhr, -⟩, hw⟩ := ha
      bound
  | hop n i qs hr hs c v K hc _ =>
      rw [pn_hndE] at ha
      obtain ⟨hH, hx⟩ := append_le_iff.mp ha
      have hH' := hH
      simp only [BoLo.hndVal, Val.pair, Expr.pn, append_le_iff] at hH'
      have hcl := le_trans (hin_clauseAt _ _ hc).2 hH'.2.2.2
      have hv : v.1.pn ≤ W := by
        have := le_trans (plug_pn_ge rfl K) hx
        rw [pn_performE_payload, append_le_iff] at this; exact this.2
      have hk := kappaAt_pn (BoLo.capTag qs.1 i.toNat) (hole_performE _) hH hx
      bound
  | hunwind n i qs hr hs c v K hc _ =>
      rw [pn_hndE] at ha
      obtain ⟨hH, hx⟩ := append_le_iff.mp ha
      simp only [BoLo.hndVal, Val.pair, Expr.pn, append_le_iff] at hH
      have hcl := le_trans (hin_clauseAt _ _ hc).2 hH.2.2.2
      have hv := raise_pn hx
      rw [pn_opPayload, empty_append, empty_append] at hv
      bound
  | uthen N D w =>
      rw [pn_ubindE] at ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at ha
      obtain ⟨⟨-, hN, -⟩, hw⟩ := ha
      bound
  | ufin N D n i v K _ _ =>
      rw [pn_ubindE] at ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at ha
      obtain ⟨⟨-, -, hD⟩, hx⟩ := ha
      have hp := raise_pn hx
      have hr : (BoLo.raiseE (.val (BoLo.opPayload n i v))).pn ≤ W := by
        rw [pn_raiseE]; exact append_le (empty_le _) hp
      bound
  | ufinC N D err K _ =>
      rw [pn_ubindE] at ha
      simp only [Expr.val, Val.pair, Expr.pn, append_le_iff] at ha
      obtain ⟨⟨-, -, hD⟩, hx⟩ := ha
      have hp := raise_pn hx
      rw [pn_cfinE]
      exact append_le (append_le (empty_le _) hp) (pn_app_of hD (empty_le _))
  | cfret err w =>
      rw [pn_cfinE, append_le_iff, append_le_iff] at ha
      rw [pn_raiseE]; exact append_le (empty_le _) ha.1.2
  | cferr err m j w K _ _ =>
      rw [pn_cfinE, append_le_iff, append_le_iff] at ha
      have hp := raise_pn ha.2
      rw [pn_raiseE]
      refine append_le (empty_le _) (cancelVal_pn_of fun E hE => ?_)
      cases err with
      | some E' =>
          simp only [BoLo.errNext, Option.or] at hE; cases hE
          exact pn_cancelVal ha.1.2 _ rfl
      | none =>
          simp only [BoLo.errNext, Option.or] at hE; cases hE; exact hp
  | cfcancel err err' K _ =>
      rw [pn_cfinE, append_le_iff, append_le_iff] at ha
      have hp := raise_pn ha.2
      rw [pn_raiseE]
      refine append_le (empty_le _) (cancelVal_pn_of fun E hE => ?_)
      cases err with
      | some E' =>
          simp only [Option.or] at hE; cases hE
          exact pn_cancelVal ha.1.2 _ rfl
      | none =>
          simp only [Option.or] at hE
          exact pn_cancelVal hp _ hE
  | cancel K _ => exact le_of_eq_empty rfl
  | creraise E K _ =>
      rw [pn_ccatchE, append_le_iff] at ha
      have hp := raise_pn ha.2
      rw [pn_raiseE]
      exact append_le (empty_le _) (pn_cancelVal hp _ rfl)

/-- **A head step stores only what its redex holds.** -/
theorem head_heap {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a') :
    ∀ ℓ v, μ' ℓ = some v → μ ℓ = some v ∨ (v.1.hin ≤ a.fl ∧ v.1.pn ≤ a.pn) := by
  intro k w hk
  cases h with
  | alloc v ℓ _ =>
      by_cases e : k = ℓ
      · subst e; simp only [Heap.upd_same, Option.some.injEq] at hk; subst hk
        right
        show v.1.hin ≤ (Expr.app (.prim .alloc) v.1).fl ∧ v.1.pn ≤ (Expr.app (.prim .alloc) v.1).pn
        rw [fl_prim_app _ _ (by decide) (by decide), pn_app_eq rfl]
        exact ⟨le_trans v.2.hin_le_fl (le_append_right _ _), le_append_right _ _⟩
      · rw [Heap.upd_other e] at hk; exact .inl hk
  | free ℓ v _ =>
      by_cases e : k = ℓ
      · subst e; simp at hk
      · rw [Heap.del_other e] at hk; exact .inl hk
  | store ℓ v x _ =>
      by_cases e : k = ℓ
      · subst e; simp only [Heap.upd_same, Option.some.injEq] at hk; subst hk
        right
        show v.1.hin ≤ (Expr.app (.app (.prim .store) (.loc k)) v.1).fl ∧
          v.1.pn ≤ (Expr.app (.app (.prim .store) (.loc k)) v.1).pn
        rw [pn_app_eq rfl]
        exact ⟨le_trans v.2.hin_le_fl (app_fl_ge _ rfl).2, le_append_right _ _⟩
      · rw [Heap.upd_other e] at hk; exact .inl hk
  | tab c f ℓ _ =>
      simp only [Heap.fill] at hk
      split at hk
      · cases hk; right; exact ⟨empty_le _, empty_le _⟩
      · exact .inl hk
  | _ => exact .inl hk

theorem val_hin_of_fl {V : HIn} {v : Val} (h : v.1.fl ≤ V) : v.1.hin ≤ V :=
  le_trans v.2.hin_le_fl h

theorem prim_app_fl {V : HIn} {p : Prim} {x : Expr} (hp : p ≠ .hnd) (hc : p ≠ .ccatch)
    (h : (Expr.app (.prim p) x).fl ≤ V) : x.fl ≤ V := by
  rw [fl_prim_app _ _ hp hc, append_le_iff] at h; exact h.2

/-- The raise's payload flows from the context it is in. -/
theorem raise_fl {V : HIn} {K : Kont} {p : Val} (h : (K.plug (BoLo.raiseE (.val p))).fl ≤ V) :
    p.1.hin ≤ V := by
  have := (plug_fl_ge (a := BoLo.raiseE (.val p)) rfl K).1 h
  rw [fl_raiseE, empty_append] at this; exact val_hin_of_fl this

/-- **A head step keeps what flows within a bound** holding the memory's values', the name `0`
and every name performed.  `[spec §19]` -/
theorem head_fl {V W : HIn} (hW : W ≤ V) (h0 : HIn.one 0 ≤ V) {μ μ' : Heap} {a a' : Expr}
    (hμ : ∀ ℓ v, μ ℓ = some v → v.1.hin ≤ V) (h : Head (ℍ := ℍ) μ a μ' a') (ha : a.fl ≤ V)
    (hp : a.pn ≤ W) : a'.fl ≤ V := by
  cases h with
  | beta b v =>
      change (Expr.app (.lam b) v.1).fl ≤ V at ha
      rw [fl_lam_app, append_le_iff] at ha
      exact fl_subst b 0 v ha.1 (val_hin_of_fl ha.2)
  | alloc v ℓ _ => exact le_of_eq_empty rfl
  | free ℓ v hv => exact le_trans (fl_le_hin _) (hμ ℓ v hv)
  | load ℓ v hv => exact le_trans (fl_le_hin _) (hμ ℓ v hv)
  | store ℓ v w _ => exact le_of_eq_empty rfl
  | seq e => simp only [Expr.fl, append_le_iff] at ha; exact ha.2
  | letpair v₁ v₂ e =>
      change (Expr.letpair (Val.pair v₁ v₂).1 e).fl ≤ V at ha
      simp only [Expr.fl, append_le_iff] at ha
      have hv := val_hin_of_fl ha.1
      simp only [Val.pair, Expr.hin, append_le_iff] at hv
      exact fl_subst _ 0 v₁ (fl_subst e 0 _ ha.2 (hin_shift_of hv.2 1 0)) hv.1
  | case₁ v e₁ e₂ =>
      change (Expr.case (Val.inj₁ v).1 e₁ e₂).fl ≤ V at ha
      simp only [Expr.fl, append_le_iff] at ha
      exact fl_subst e₁ 0 v ha.1.2 (val_hin_of_fl (v := Val.inj₁ v) ha.1.1)
  | case₂ v e₁ e₂ =>
      change (Expr.case (Val.inj₂ v).1 e₁ e₂).fl ≤ V at ha
      simp only [Expr.fl, append_le_iff] at ha
      exact fl_subst e₂ 0 v ha.2 (val_hin_of_fl (v := Val.inj₂ v) ha.1.1)
  | host op v r hr => exact le_trans (fl_le_hin _) (le_of_eq_empty (host_le ℍ op hr).1)
  | tab c f ℓ _ =>
      have hf := val_hin_of_fl (v := Val.pair (Val.i32 c) f) (prim_app_fl (by decide) (by decide) ha)
      simp only [Val.pair, Expr.hin, append_le_iff] at hf
      exact le_trans (fl_le_hin _) (tabFill_le (W := HIn.top) hf.2 (le_of_any rfl) ℓ _ _ _).1
  | idx ℓ n i => exact le_trans (fl_le_hin _) (le_of_eq_empty (idxAns_le ℓ n i).1)
  | split ℓ n i => exact le_trans (fl_le_hin _) (le_of_eq_empty (splitAns_le ℓ n i).1)
  | drop f ℓ n =>
      have hf := val_hin_of_fl (v := Val.pair f (Val.arr ℓ n)) (prim_app_fl (by decide) (by decide) ha)
      simp only [Val.pair, Expr.hin, append_le_iff] at hf
      exact le_trans (fl_le_hin _) (dropFill_le (W := HIn.top) hf.1 (le_of_any rfl) ℓ _ _).1
  | count f n i s =>
      have hf := val_hin_of_fl (v := Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))
        (prim_app_fl (by decide) (by decide) ha)
      simp only [Val.pair, Expr.hin, append_le_iff] at hf
      exact le_trans (fl_le_hin _)
        (countNext_le (W := HIn.top) hf.1 hf.2.2.2 (le_of_any rfl) (le_of_any rfl) n i).1
  | countTry f n i s =>
      have hf := val_hin_of_fl (v := Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))
        (prim_app_fl (by decide) (by decide) ha)
      simp only [Val.pair, Expr.hin, append_le_iff] at hf
      exact le_trans (fl_le_hin _)
        (countTryNext_le (W := HIn.top) hf.1 hf.2.2.2 (le_of_any rfl) (le_of_any rfl) n i).1
  | boundedFix s k x =>
      have hf := val_hin_of_fl (v := Val.pair s (Val.pair (Val.i32 k) x))
        (prim_app_fl (by decide) (by decide) ha)
      simp only [Val.pair, Expr.hin, append_le_iff] at hf
      exact le_trans (fl_le_hin _)
        (boundedFixNext_le (W := HIn.top) hf.1 hf.2.2 (le_of_any rfl) (le_of_any rfl) k).1
  | iterate f s =>
      have hf := val_hin_of_fl (v := Val.pair f s) (prim_app_fl (by decide) (by decide) ha)
      simp only [Val.pair, Expr.hin, append_le_iff] at hf
      exact le_trans (fl_le_hin _)
        (iterNext_le (W := HIn.top) hf.1 hf.2 (le_of_any rfl) (le_of_any rfl) (le_of_any rfl)).1
  | hret n qs hr hs w =>
      rw [fl_hndE_hndVal, append_le_iff] at ha
      have hX := val_hin_of_fl ha.1
      simp only [Val.pair, Expr.hin, append_le_iff] at hX
      have hhr := hX.2.1
      have hw := ha.2
      exact le_trans (fl_le_hin _) (by bound)
  | hop n i qs hr hs c v K hc hK =>
      have hn : HIn.one n ≤ V := by
        have := le_trans (plug_pn_ge rfl K) (le_trans (pn_app_ge _ _) hp)
        rw [pn_performE_payload, append_le_iff] at this
        exact le_trans this.1 hW
      have ha' : (hndE (BoLo.hndVal n qs hr hs) (K.plug (BoLo.performE (.val
          (BoLo.opPayload n i v))))).hin ≤ V := by
        rw [fl_hndE_hndVal, append_le_iff] at ha
        rw [hin_hndE, hndArg_hndVal]
        exact append_le (append_le hn (val_hin_of_fl ha.1)) ha.2
      exact le_trans (fl_le_hin _) (head_hin h0 hμ (.hop μ n i qs hr hs c v K hc hK) ha')
  | hunwind n i qs hr hs c v K hc _ =>
      rw [fl_hndE_hndVal, append_le_iff] at ha
      have hX := val_hin_of_fl ha.1
      simp only [Val.pair, Expr.hin, append_le_iff] at hX
      have hcl := le_trans (hin_clauseAt _ _ hc).1 hX.2.2
      have hv := raise_hin ha.2
      rw [hin_opPayload, empty_append, empty_append] at hv
      exact le_trans (fl_le_hin _) (by bound)
  | uthen N D w =>
      rw [fl_ubindE, append_le_iff] at ha
      have hND := val_hin_of_fl ha.1
      simp only [Val.pair, Expr.hin, append_le_iff] at hND
      have hN := hND.1
      have hw := val_hin_of_fl ha.2
      exact le_trans (fl_le_hin _) (by bound)
  | ufin N D n i v K _ _ =>
      rw [fl_ubindE, append_le_iff] at ha
      have hND := val_hin_of_fl ha.1
      simp only [Val.pair, Expr.hin, append_le_iff] at hND
      have hD := hND.2
      have hpay := raise_fl ha.2
      have hr : (BoLo.raiseE (.val (BoLo.opPayload n i v))).hin ≤ V := by
        rw [hin_raiseE]; exact append_le (empty_le _) hpay
      exact le_trans (fl_le_hin _) (by bound)
  | ufinC N D err K _ =>
      rw [fl_ubindE, append_le_iff] at ha
      have hND := val_hin_of_fl ha.1
      simp only [Val.pair, Expr.hin, append_le_iff] at hND
      have hpay := raise_fl ha.2
      rw [fl_cfinE]
      exact append_le (le_trans (fl_le_hin _) hpay)
        (le_trans (fl_le_hin _) (hin_app_of hND.2 (empty_le _)))
  | cfret err w =>
      rw [fl_cfinE, append_le_iff] at ha
      have hs := val_hin_of_fl ha.1
      rw [fl_raiseE]; exact append_le (empty_le _) (le_trans (fl_le_hin _) hs)
  | cferr err m j w K _ _ =>
      rw [fl_cfinE, append_le_iff] at ha
      have hs := val_hin_of_fl ha.1
      have hpay := raise_fl ha.2
      rw [fl_raiseE]
      refine append_le (empty_le _) (le_trans (fl_le_hin _) (cancelVal_hin_of fun E hE => ?_))
      cases err with
      | some E' =>
          simp only [BoLo.errNext, Option.or] at hE; cases hE
          exact hin_cancelVal hs _ rfl
      | none =>
          simp only [BoLo.errNext, Option.or] at hE; cases hE; exact hpay
  | cfcancel err err' K _ =>
      rw [fl_cfinE, append_le_iff] at ha
      have hs := val_hin_of_fl ha.1
      have hpay := raise_fl ha.2
      rw [fl_raiseE]
      refine append_le (empty_le _) (le_trans (fl_le_hin _) (cancelVal_hin_of fun E hE => ?_))
      cases err with
      | some E' =>
          simp only [Option.or] at hE; cases hE
          exact hin_cancelVal hs _ rfl
      | none =>
          simp only [Option.or] at hE
          exact hin_cancelVal hpay _ hE
  | cancel K _ => exact le_of_eq_empty rfl
  | creraise E K _ =>
      rw [fl_ccatchE] at ha
      have hpay := raise_fl ha
      rw [fl_raiseE]
      exact append_le (empty_le _) (le_trans (fl_le_hin _) (hin_cancelVal hpay _ rfl))

end heads

/-! ### Runs -/

/-- **The names a run of `e₀` may perform**: the names `e₀` performs, and the tick's `divEff`,
which a loop performs.  `[spec §19]` -/
def performed (e₀ : Expr) : HIn := e₀.pn ++ HIn.one divEff

/-- **What may flow in a run of `e₀`**: what flows from `e₀`; the name of every handler frame a
continuation may capture, which is a name the run performs; and the name `0`, of the cancel
delimiter every continuation's cancel holds.  `[spec §19]` -/
def flows (e₀ : Expr) : HIn := e₀.fl ++ performed e₀ ++ HIn.one 0

/-- **The flow invariant**: what flows from the term, and every value its memory holds, are within
`V`; the names it and its memory perform are within `W`. -/
def FlowInv (V W : HIn) (μ : Heap) (e : Expr) : Prop :=
  e.fl ≤ V ∧ e.pn ≤ W ∧ ∀ ℓ v, μ ℓ = some v → v.1.hin ≤ V ∧ v.1.pn ≤ W

section runs
variable {ℍ : Host} [HostIs ℍ]

/-- **A step keeps the flow invariant**, at bounds that hold every name performed, the name `0`,
and the tick's name.  `[spec §19]` -/
theorem step1_flowInv {V W : HIn} (hW : W ≤ V) (h0 : HIn.one 0 ≤ V) (hdiv : HIn.one divEff ≤ W)
    {μ μ' : Heap} {e e' : Expr} (h : Step1 (ℍ := ℍ) μ e μ' e') (hi : FlowInv V W μ e) :
    FlowInv V W μ' e' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  obtain ⟨hfl, hpn, hμ⟩ := hi
  have ha := head_plain hh
  have hafl := (plug_fl_ge ha K).1 hfl
  have hapn := le_trans (plug_pn_ge ha K) hpn
  refine ⟨(plug_le ha (fun h₁ => head_fl hW h0 (fun ℓ v hv => (hμ ℓ v hv).1) hh h₁ hapn)
      (fun h₁ => head_hin h0 (fun ℓ v hv => (hμ ℓ v hv).1) hh h₁) K).1 hfl,
    plug_pn_le ha (fun h₁ => head_pn hdiv (fun ℓ v hv => (hμ ℓ v hv).2) hh h₁) K hpn,
    fun ℓ v hv => ?_⟩
  rcases head_heap hh ℓ v hv with h | h
  · exact hμ ℓ v h
  · exact ⟨le_trans h.1 hafl, le_trans h.2 hapn⟩

/-- **A run keeps the flow invariant.**  `[spec §19]` -/
theorem steps_flowInv {V W : HIn} (hW : W ≤ V) (h0 : HIn.one 0 ≤ V) (hdiv : HIn.one divEff ≤ W)
    {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e') (hi : FlowInv V W μ e) :
    FlowInv V W μ' e' := by
  induction h with
  | refl => exact hi
  | more h₁ _ ih => exact ih (step1_flowInv hW h0 hdiv h₁ hi)

/-- **A run of `e₀` from a memory that holds no code keeps within `flows e₀`.** -/
theorem steps_flows {e₀ : Expr} {μ₀ μ : Heap} {e : Expr} (h : Steps (ℍ := ℍ) μ₀ e₀ μ e)
    (hμ₀ : ∀ ℓ v, μ₀ ℓ = some v → v.1.hin = {} ∧ v.1.pn = {}) :
    FlowInv (flows e₀) (performed e₀) μ e := by
  have hW : performed e₀ ≤ flows e₀ :=
    le_append_of_le_left (le_append_right _ _)
  have h0 : HIn.one 0 ≤ flows e₀ := le_append_right _ _
  have hdiv : HIn.one divEff ≤ performed e₀ := le_append_right _ _
  refine steps_flowInv hW h0 hdiv h ⟨le_append_of_le_left (le_append_left _ _), le_append_left _ _,
    fun ℓ v hv => ?_⟩
  obtain ⟨h₁, h₂⟩ := hμ₀ ℓ v hv
  exact ⟨le_of_eq_empty h₁, le_of_eq_empty h₂⟩

/-- **The theorem: condition 2 of the direct call of a clause.** In a run of `e₀` from a memory
that holds no code, at every configuration that holds a handler frame over a context `K` filled by
`p` (an operation the handler catches, `perform (n, …)`, among them), a row `Σ` none of whose names
`flows e₀` may catch is unhandled in `K`: no frame of `K` catches an operation or a raise of a name
of `Σ`.  `[spec §19]` -/
theorem steps_unhandledIn {e₀ : Expr} {μ₀ μ : Heap} {e : Expr} (h : Steps (ℍ := ℍ) μ₀ e₀ μ e)
    (hμ₀ : ∀ ℓ v, μ₀ ℓ = some v → v.1.hin = {} ∧ v.1.pn = {}) {K₀ K : Kont} {H : Val} {p : Expr}
    (he : e = K₀.plug (hndE H (K.plug p))) {S : Row} (hS : ∀ o ∈ S, ¬ (flows e₀).Catches o.n) :
    UnhandledIn S K := by
  have hfl := (steps_flows h hμ₀).1
  rw [he] at hfl
  have hx : (K.plug p).hin ≤ flows e₀ :=
    le_trans (fl_hndE_ge H _) ((plug_fl_ge (a := hndE H (K.plug p)) rfl K₀).1 hfl)
  intro o ho
  cases hc : K.Catches o.n
  · rfl
  · exact absurd (Catches.mono hx (catches_hin p hc)) (hS o ho)

/-- **The frames a run holds**: within `e₀`'s and the name `0`, from a memory that holds no
code.  `[spec §19]` -/
theorem steps_hin {e₀ : Expr} {μ₀ μ : Heap} {e : Expr} (h : Steps (ℍ := ℍ) μ₀ e₀ μ e)
    (hμ₀ : ∀ ℓ v, μ₀ ℓ = some v → v.1.hin = {}) :
    e.hin ≤ e₀.hin ++ HIn.one 0 ∧ ∀ ℓ v, μ ℓ = some v → v.1.hin ≤ e₀.hin ++ HIn.one 0 := by
  have h0 : HIn.one 0 ≤ e₀.hin ++ HIn.one 0 := le_append_right _ _
  have step : ∀ {μ μ' : Heap} {e e' : Expr}, Step1 (ℍ := ℍ) μ e μ' e' →
      e.hin ≤ e₀.hin ++ HIn.one 0 ∧ (∀ ℓ v, μ ℓ = some v → v.1.hin ≤ e₀.hin ++ HIn.one 0) →
      e'.hin ≤ e₀.hin ++ HIn.one 0 ∧ (∀ ℓ v, μ' ℓ = some v → v.1.hin ≤ e₀.hin ++ HIn.one 0) := by
    intro μ μ' e e' hs hi
    obtain ⟨K, a, a', rfl, rfl, hh⟩ := hs
    have ha := head_plain hh
    have hahin := le_trans (plug_hin_ge (PlainB.nonLit ha) K) hi.1
    refine ⟨plug_hin_le (PlainB.hole ha) (fun h₁ => head_hin h0 hi.2 hh h₁) K hi.1,
      fun ℓ v hv => ?_⟩
    rcases head_heap hh ℓ v hv with h | h
    · exact hi.2 ℓ v h
    · exact le_trans h.1 (le_trans (fl_le_hin _) hahin)
  have base : e₀.hin ≤ e₀.hin ++ HIn.one 0 ∧
      ∀ ℓ v, μ₀ ℓ = some v → v.1.hin ≤ e₀.hin ++ HIn.one 0 :=
    ⟨le_append_left _ _, fun ℓ v hv => by rw [hμ₀ ℓ v hv]; exact empty_le _⟩
  revert base
  generalize e₀.hin ++ HIn.one 0 = V at *
  intro base
  clear hμ₀
  induction h with
  | refl => exact base
  | more h₁ _ ih => exact ih (step h₁ base)

/-- **A handler frame of `m` is among the frames held**. -/
theorem hasHnd_hin {m : UInt32} : ∀ {K : Kont} (e : Expr), K.HasHnd m = true →
    (K.plug e).hin.HasHnd m
  | .hole, _, h => by simp [Kont.HasHnd] at h
  | .pairL K _, e, h | .letpair K _, e, h | .seq K _, e, h =>
      HasHnd.mono (le_append_left _ _) (hasHnd_hin e h)
  | .case K _ _, e, h =>
      HasHnd.mono (le_trans (le_append_left _ _) (le_append_left _ _)) (hasHnd_hin e h)
  | .pairR _ K, e, h => HasHnd.mono (le_append_right _ _) (hasHnd_hin e h)
  | .inj₁ K, e, h | .inj₂ K, e, h => hasHnd_hin (K := K) e h
  | .appL K v, e, h => by
      simp only [Kont.HasHnd] at h
      have := hasHnd_hin (K := K) e h
      cases K with
      | hole => simp [Kont.HasHnd] at h
      | _ => exact HasHnd.mono (hin_app_ge_fun _ (by simp [Kont.plug, isHnd])) this
  | .appR f K, e, h => by
      simp only [Kont.HasHnd, Bool.or_eq_true] at h
      rcases h with h | h
      · split at h
        · rename_i n X
          simp only [beq_iff_eq] at h
          subst h
          have hf : (Expr.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) X)).hin.HasHnd n :=
            .inl (by simp [Expr.hin, HIn.one])
          exact HasHnd.mono (hin_app_ge_fun _ rfl) hf
        · cases h
      · exact HasHnd.mono (hin_app_ge _ _) (hasHnd_hin e h)

/-- **The run invariant: every handler frame a run reaches is of a handle node of the program.**
In a run of `e₀` from a memory that holds no code, every handler frame of the context of a
configuration has the name of a handle node of `e₀` (a literal name of `hnd` in it), the reserved
name `0`, or `e₀` holds `hnd` at a name that is not a literal.  `[spec §19]` -/
theorem steps_frame_of_node {e₀ : Expr} {μ₀ μ : Heap} {e : Expr} (h : Steps (ℍ := ℍ) μ₀ e₀ μ e)
    (hμ₀ : ∀ ℓ v, μ₀ ℓ = some v → v.1.hin = {}) {K : Kont} {a : Expr} (he : e = K.plug a)
    {m : UInt32} (hm : K.HasHnd m = true) :
    m ∈ e₀.hin.names ∨ m = 0 ∨ e₀.hin.any = true := by
  have hb := (steps_hin h hμ₀).1
  rw [he] at hb
  rcases HasHnd.mono hb (hasHnd_hin a hm) with h | h
  · simp only [names_append, List.mem_append, HIn.one, List.mem_singleton] at h
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · simp only [any_append, Bool.or_eq_true] at h
    rcases h with h | h
    · exact .inr (.inr h)
    · simp [HIn.one] at h

end runs

end BoCa.Fig16.LogRel.Core.ClauseKinds
