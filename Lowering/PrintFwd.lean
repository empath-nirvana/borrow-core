import Lowering.BigStep
import Lowering.LIRSim

/-!
# Lowering — the print's forward simulation, on the core fragment  `[spec §56]`

A run of the source machine to a value is followed by the interpreter on the print
(`fwd`): at every fuel the interpreter answers the corresponding value or runs out of fuel, and
from some fuel on it answers. The source's host is the interpreter's, `lirHost`.

- **Values** correspond (`VRel`): `()`, literals as their words, pairs and injections
  componentwise, a `λ` as the closure of its code, its captured slots' values in its environment,
  and `copy`, `forget` and a host operation as the closures of their codes.
- **Frames.** The print's variable `ρ k` holds the value of the slot `k` while `k` is unconsumed
  (`FrameOK`); the budget `bud k ≤ 1` says whether it is. A subterm consumes exactly the slots its
  returning paths use (`cnt`, read off `occ`), and no other variable of the frame (`Post`), so a
  function's frame is empty when its body returns: explicit ownership (`explicitB`) is what makes
  the interpreter's consumption checks hold.
- **The interpreter's other checks**: a `copy` or `drop` is at a variable whose type is `unit`
  (`tyTable`), so it passes the type checks; the print writes no `load`.
-/

namespace Lowering
open BoCa
open BoCa.BoLo (Heap Head Step1 Steps Kont)
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op LV St IM)

local instance : HostIs Backend2.lirHost := ⟨⟩

/-! ### Uses -/

/-- How often the slot `k` is used on `e`'s returning paths. -/
def cnt (e : Expr) (k : Nat) : Nat :=
  match occ e k with
  | some ⟨some r, _⟩ => r
  | _ => 0

/-- Every slot's uses, at most `bud` on every path. -/
def BudOK (e : Expr) (bud : Nat → Nat) : Prop :=
  ∀ k, ∃ u, occ e k = some u ∧ u.ret.getD 0 ≤ bud k ∧ u.stop.getD 0 ≤ bud k

/-- Every slot's uses have a returning path. -/
def Returns (e : Expr) : Prop := ∀ k, ∃ u r, occ e k = some u ∧ u.ret = some r

/-- `u` uses at most `B` on every path. -/
def Bnd (u : Uses) (B : Nat) : Prop := u.ret.getD 0 ≤ B ∧ u.stop.getD 0 ≤ B

/-- `u` has a path. -/
def NE (u : Uses) : Prop := u.ret.isSome ∨ u.stop.isSome

theorem maxO_ge_left (a b : Option Nat) : a.getD 0 ≤ (maxO a b).getD 0 := by
  cases a <;> cases b <;> simp [maxO]

theorem maxO_ge_right (a b : Option Nat) : b.getD 0 ≤ (maxO a b).getD 0 := by
  cases a <;> cases b <;> simp [maxO]

theorem maxO_le {a b : Option Nat} {B : Nat} (ha : a.getD 0 ≤ B) (hb : b.getD 0 ≤ B) :
    (maxO a b).getD 0 ≤ B := by
  cases a <;> cases b <;> simp_all [maxO]

theorem ne_andThen {a b : Uses} (ha : NE a) (hb : NE b) : NE (a.andThen b) := by
  unfold Uses.andThen
  cases hr : a.ret with
  | none => simpa [hr] using ha
  | some r =>
      rcases hb with hb | hb
      · left; simp only; cases h : b.ret <;> simp_all
      · right; simp only; cases h : b.stop <;> cases a.stop <;> simp_all [maxO]

theorem ne_join {a b j : Uses} (ha : NE a) (hb : NE b) (h : Uses.join a b = some j) : NE j := by
  unfold Uses.join at h
  split at h
  · split at h
    · cases h; left; rfl
    · cases h
  · cases h; left; rfl
  · cases h; left; rfl
  · cases h; right
    rename_i h₁ h₂
    simp only [NE, h₁, h₂, Option.isSome_none] at ha hb
    cases h₃ : a.stop <;> cases h₄ : b.stop <;> simp_all [maxO]

theorem occ_nonempty : ∀ (e : Expr) (k : Nat) (u : Uses), occ e k = some u → NE u := by
  intro e
  induction e with
  | var j =>
      intro k u h; simp only [occ, Option.some.injEq] at h; subst h
      split <;> simp [NE, Uses.one, Uses.zero]
  | unit | loc _ | prim _ =>
      intro k u h; simp only [occ, Option.some.injEq] at h; subst h; simp [NE, Uses.zero]
  | pair a b iha ihb | seq a b iha ihb =>
      intro k u h
      simp only [occ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ua, ha, ub, hb, rfl⟩ := h
      exact ne_andThen (iha k ua ha) (ihb k ub hb)
  | app f a ihf iha =>
      intro k u h
      simp only [occ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ua, ha, uf, hf, rfl⟩ := h
      exact ne_andThen (iha k ua ha) (ihf k uf hf)
  | letpair a b iha ihb =>
      intro k u h
      simp only [occ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨ua, ha, ub, hb, rfl⟩ := h
      exact ne_andThen (iha k ua ha) (ihb _ ub hb)
  | inj₁ a ih | inj₂ a ih => intro k u h; exact ih k u h
  | lam b _ => intro k u h; simp only [occ, Option.some.injEq] at h; subst h; simp [NE]
  | case v a b ihv iha ihb =>
      intro k u h
      simp only [occ] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨uv, hv, rfl⟩ := h
        exact ne_andThen (ihv k uv hv) (by simp [NE, Uses.halt])
      · cases hv : occ v k <;> cases ha : occ a (k + 1) <;> cases hb : occ b (k + 1) <;>
          simp only [hv, ha, hb, Option.bind_eq_bind, Option.bind_none, Option.bind_some,
            reduceCtorEq] at h
        rename_i uv ua ub
        cases hj : Uses.join ua ub <;> simp only [hj, Option.bind_none, Option.bind_some,
          reduceCtorEq, Option.pure_def, Option.some.injEq] at h
        subst h
        exact ne_andThen (ihv k uv hv) (ne_join (iha _ ua ha) (ihb _ ub hb) hj)

theorem bnd_andThen_left {a b : Uses} {B : Nat} (h : Bnd (a.andThen b) B) (hb : NE b) : Bnd a B := by
  unfold Uses.andThen at h
  cases hr : a.ret with
  | none => simpa [hr] using h
  | some r =>
      simp only [hr] at h
      refine ⟨?_, le_trans (maxO_ge_left _ _) h.2⟩
      rcases hb with hb | hb
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hb
        have := h.1; simp [hx] at this; simp [hr]; omega
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hb
        have := le_trans (maxO_ge_right _ _) h.2; simp [hx] at this; simp [hr]; omega

theorem bnd_andThen_right {a b : Uses} {B r : Nat} (h : Bnd (a.andThen b) B) (hr : a.ret = some r) :
    Bnd b (B - r) := by
  unfold Uses.andThen at h
  simp only [hr] at h
  constructor
  · cases hx : b.ret with
    | none => simp
    | some x => have := h.1; simp [hx] at this; simp; omega
  · cases hx : b.stop with
    | none => simp
    | some x => have := le_trans (maxO_ge_right _ _) h.2; simp [hx] at this; simp; omega

theorem ret_andThen {a b : Uses} {r r' : Nat} (ha : a.ret = some r) (hb : b.ret = some r') :
    (a.andThen b).ret = some (r + r') := by
  simp [Uses.andThen, ha, hb]

theorem join_bnd {a b j : Uses} {B : Nat} (h : Uses.join a b = some j) (hj : Bnd j B) :
    Bnd a B ∧ Bnd b B := by
  unfold Uses.join at h
  split at h
  · split at h
    · cases h; rename_i x y h₁ h₂ hxy
      exact ⟨⟨by simpa [h₁] using hj.1, le_trans (maxO_ge_left _ _) hj.2⟩,
        ⟨by simpa [h₂, ← hxy] using hj.1, le_trans (maxO_ge_right _ _) hj.2⟩⟩
    · cases h
  · cases h; rename_i x h₁ h₂
    exact ⟨⟨by simpa [h₁] using hj.1, le_trans (maxO_ge_left _ _) hj.2⟩,
      ⟨by simp [h₂], le_trans (maxO_ge_right _ _) hj.2⟩⟩
  · cases h; rename_i x h₁ h₂
    exact ⟨⟨by simp [h₁], le_trans (maxO_ge_left _ _) hj.2⟩,
      ⟨by simpa [h₂] using hj.1, le_trans (maxO_ge_right _ _) hj.2⟩⟩
  · cases h; rename_i h₁ h₂
    exact ⟨⟨by simp [h₁], le_trans (maxO_ge_left _ _) hj.2⟩,
      ⟨by simp [h₂], le_trans (maxO_ge_right _ _) hj.2⟩⟩

theorem join_ret_left {a b j : Uses} {x : Nat} (h : Uses.join a b = some j) (ha : a.ret = some x) :
    j.ret = some x := by
  unfold Uses.join at h
  rw [ha] at h
  cases hb : b.ret with
  | none => simp only [hb, Option.some.injEq] at h; subst h; rfl
  | some y =>
      simp only [hb] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · cases h

theorem join_ret_right {a b j : Uses} {x : Nat} (h : Uses.join a b = some j) (hb : b.ret = some x) :
    j.ret = some x := by
  unfold Uses.join at h
  rw [hb] at h
  cases ha : a.ret with
  | none => simp only [ha, Option.some.injEq] at h; subst h; rfl
  | some y =>
      simp only [ha] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rename_i hxy; simp [hxy]
      · cases h

/-! ### Values -/

/-- **The correspondence of values**: `()`, a literal and its word, pairs and injections
componentwise, a `λ` and the closure of its code with its captured slots' values, and `copy`,
`forget` and a host operation and their codes' closures. -/
inductive VRel (p : Prog) (N : Nat) : Val → LV → Prop where
  | unit : VRel p N Val.unit .unit
  | lit (c : IntLit) : VRel p N (Val.prim (.lit c)) (Backend2.litV c)
  | pair {a b : Val} {x y : LV} (ha : VRel p N a x) (hb : VRel p N b y) :
      VRel p N (Val.pair a b) (.pair x y)
  | inj₁ {a : Val} {x : LV} (ha : VRel p N a x) : VRel p N (Val.inj₁ a) (.inj false x)
  | inj₂ {a : Val} {x : LV} (ha : VRel p N a x) : VRel p N (Val.inj₂ a) (.inj true x)
  | host (op : HostOp) (c : Nat) (h : CodeAt p c 0 (hostFn op)) :
      VRel p N (Val.prim (.host op)) (.clos c [])
  | copy (c : Nat) (h : CodeAt p c 0 copyFn) :
      VRel p N (Val.lam (.pair (.var 0) (.var 0))) (.clos c [])
  | forget (c : Nat) (h : CodeAt p c 0 forgetFn) : VRel p N (Val.lam .unit) (.clos c [])
  | lam {c m : Nat} {b : Expr} {tb : Tm} {γ : List Val} {env : List LV}
      (hcp : Expr.lam b ≠ copy) (hfg : Expr.lam b ≠ forget)
      (hpr : Pr p N (lamEnv b) ((capt b).length + 1) b tb m) (hm : m ≤ N)
      (hc : CodeAt p c (capt b).length tb)
      (hx : explicitB isCF b = true) (h0 : once (occ b 0) = true) (hcap : capOnceB b = true)
      (hcore : coreB b = true) (hlen : env.length = (capt b).length)
      (hcapl : ∀ k, k ∈ capt b → k < γ.length)
      (hrel : ∀ i (hi : i < env.length) (k : Nat) (hk : k < γ.length), (capt b)[i]? = some k →
        VRel p N γ[k] env[i]) :
      VRel p N (Val.lam (Expr.psub 1 γ b)) (.clos c env)

theorem vrel_pair_inv {p : Prog} {N : Nat} {a b : Val} {lv : LV} (h : VRel p N (Val.pair a b) lv) :
    ∃ x y, lv = .pair x y ∧ VRel p N a x ∧ VRel p N b y := by
  generalize hV : Val.pair a b = V at h
  cases h with
  | pair ha hb =>
      have e := congrArg Subtype.val hV
      simp only [Val.pair, Expr.pair.injEq] at e
      obtain ⟨e₁, e₂⟩ := e
      rw [Subtype.ext e₁, Subtype.ext e₂]
      exact ⟨_, _, rfl, ha, hb⟩
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.prim, Val.inj₁,
      Val.inj₂, Val.lam] at e

theorem vrel_inj₁_inv {p : Prog} {N : Nat} {a : Val} {lv : LV} (h : VRel p N (Val.inj₁ a) lv) :
    ∃ x, lv = .inj false x ∧ VRel p N a x := by
  generalize hV : Val.inj₁ a = V at h
  cases h with
  | inj₁ ha =>
      have e := congrArg Subtype.val hV
      simp only [Val.inj₁, Expr.inj₁.injEq] at e
      rw [Subtype.ext e]
      exact ⟨_, rfl, ha⟩
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.prim, Val.inj₁,
      Val.inj₂, Val.lam] at e

theorem vrel_inj₂_inv {p : Prog} {N : Nat} {a : Val} {lv : LV} (h : VRel p N (Val.inj₂ a) lv) :
    ∃ x, lv = .inj true x ∧ VRel p N a x := by
  generalize hV : Val.inj₂ a = V at h
  cases h with
  | inj₂ ha =>
      have e := congrArg Subtype.val hV
      simp only [Val.inj₂, Expr.inj₂.injEq] at e
      rw [Subtype.ext e]
      exact ⟨_, rfl, ha⟩
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.prim, Val.inj₁,
      Val.inj₂, Val.lam] at e

theorem vrel_unit_inv {p : Prog} {N : Nat} {lv : LV} (h : VRel p N Val.unit lv) : lv = .unit := by
  generalize hV : Val.unit = V at h
  cases h with
  | unit => rfl
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.prim, Val.inj₁,
      Val.inj₂, Val.lam] at e

/-! ### Frames -/

/-- **The frame holds the slots not yet consumed**: every variable below `n`; at each slot of
budget `1`, its variable holds a value corresponding to the slot's; the budgets at most `1`, and
`ρ` one-to-one on the slots of budget `1`. -/
structure FrameOK (p : Prog) (N : Nat) (γ : List Val) (ρ : Nat → Nat) (n : Nat) (bud : Nat → Nat)
    (F : Std.HashMap Var LV) : Prop where
  fresh : ∀ (x : Nat) v, F[x]? = some v → x < n
  le : ∀ k, bud k ≤ 1
  live : ∀ k, bud k = 1 → ∃ (hk : k < γ.length) (v : LV), F[ρ k]? = some v ∧ VRel p N γ[k] v
  inj : ∀ k k', bud k = 1 → bud k' = 1 → ρ k = ρ k' → k = k'

/-- **What a run of `e` leaves of the frame**: the slots its returning paths use are consumed,
and every other variable is as it was. -/
def Post (e : Expr) (ρ : Nat → Nat) (bud : Nat → Nat) (F F' : Std.HashMap Var LV) : Prop :=
  (∀ k, bud k = 1 → cnt e k = 1 → F'[ρ k]? = none) ∧
  (∀ x : Nat, (∀ k, bud k = 1 → cnt e k = 1 → ρ k ≠ x) → F'[x]? = F[x]?)

/-! ### Head steps of values -/

theorem head_lam_inv {μ μ' : Heap} {b r : Expr} {v : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (.lam b) v.1) μ' r) : μ' = μ ∧ r = b.subst 0 v := by
  generalize hE : Expr.app (.lam b) v.1 = E at h
  cases h with
  | beta b' v' =>
      simp only [Expr.app.injEq, Expr.val, Val.lam, Expr.lam.injEq] at hE
      obtain ⟨rfl, hv⟩ := hE
      have : v = v' := Subtype.ext hv
      subst this; exact ⟨rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_host_inv {μ μ' : Heap} {op : HostOp} {r : Expr} {v : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (.prim (.host op)) v.1) μ' r) :
    μ' = μ ∧ ∃ r' : Val, Backend2.lirHost.call op v = some r' ∧ r = r'.1 := by
  generalize hE : Expr.app (.prim (.host op)) v.1 = E at h
  cases h with
  | host op' v' r' hr =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, Expr.prim.injEq, Prim.host.injEq] at hE
      obtain ⟨rfl, hv⟩ := hE
      have : v = v' := Subtype.ext hv
      subst this; exact ⟨rfl, r', hr, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

/-- A literal takes no head step when applied. -/
theorem head_lit_false {μ μ' : Heap} {c : IntLit} {a r : Expr}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (.prim (.lit c)) a) μ' r) : False := by
  generalize hE : Expr.app (.prim (.lit c)) a = E at h
  cases h <;> simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim,
    Val.lam]

/-- A value that is not a function takes no head step when applied. -/
theorem head_nonfun {μ μ' : Heap} {f : Val} {a r : Expr}
    (h : Head (ℍ := Backend2.lirHost) μ (.app f.1 a) μ' r)
    (hf : ∀ b, f.1 ≠ .lam b) (hp : ∀ q, f.1 ≠ .prim q) (hs : ∀ x, f.1 ≠ .app (.prim .store) x) :
    False := by
  generalize hE : Expr.app f.1 a = E at h
  cases h <;> simp only [Expr.app.injEq, Expr.val, Val.lam, Val.prim, BoLo.hndE,
      BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE] at hE <;>
    first
    | exact hf _ hE.1
    | exact hp _ hE.1
    | exact hs _ hE.1
    | (obtain ⟨h₁, -⟩ := hE; have h₂ := h₁ ▸ f.2; simp at h₂)
    | (cases hE)

/-! ### Host operations -/

/-- The word that holds a width's bits. -/
def wordOf : (w : Width) → w.bits → UInt64
  | .w32, a => a.toUInt64
  | .w64, a => a
  | .w8, a => a.toUInt64
  | .f32, a => a.toUInt64
  | .f64, a => a

theorem vrel_ofBits {p : Prog} {N : Nat} (w : Width) (a : w.bits) :
    VRel p N (Val.ofBits w a) (.int (wordOf w a)) := by
  cases w <;> exact .lit _

theorem vrel_argAt {p : Prog} {N : Nat} {w : Width} {v : Val} {lv : LV} {a : w.bits}
    (hv : VRel p N v lv) (h : v.1.argAt? w = some a) : lv = .int (wordOf w a) := by
  cases hv with
  | lit c =>
      cases w <;> cases c <;>
        simp_all [Expr.argAt?, Expr.arg32?, Expr.arg64?, Expr.arg8?, Expr.lit?, Val.prim,
          Backend2.litV, wordOf]
  | _ => cases w <;> simp_all [Expr.argAt?, Expr.arg32?, Expr.arg64?, Expr.arg8?, Expr.lit?,
      Val.prim, Val.unit, Val.pair, Val.inj₁, Val.inj₂, Val.lam]

theorem vrel_argsAt {p : Prog} {N : Nat} {w : Width} {v : Val} {lv : LV} {a b : w.bits}
    (hv : VRel p N v lv) (h : v.1.argsAt? w = some (a, b)) :
    lv = .pair (.int (wordOf w a)) (.int (wordOf w b)) := by
  cases hv with
  | pair ha hb =>
      simp only [Val.pair, Expr.argsAt?, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hx, y, hy, rfl, rfl⟩ := h
      rw [vrel_argAt ha hx, vrel_argAt hb hy]
  | _ => simp_all [Expr.argsAt?, Val.prim, Val.unit, Val.inj₁, Val.inj₂, Val.lam]

theorem args32_argsAt {e : Expr} : e.args32? = e.argsAt? .w32 := by
  cases e <;> rfl

theorem args64_argsAt {e : Expr} : e.args64? = e.argsAt? .w64 := by
  cases e <;> rfl

theorem arg32_argAt {e : Expr} : e.arg32? = e.argAt? .w32 := rfl
theorem arg64_argAt {e : Expr} : e.arg64? = e.argAt? .w64 := rfl
theorem arg8_argAt {e : Expr} : e.arg8? = e.argAt? .w8 := rfl

theorem vrel_bool {p : Prog} {N : Nat} (b : Bool) :
    VRel p N (Val.bool b) (.inj (Backend2.toBit b != 0) .unit) := by
  cases b
  · exact .inj₁ .unit
  · exact .inj₂ .unit

theorem fbits_wordOf (f : FWidth) (a : f.width.bits) : Backend2.fbits f (wordOf f.width a) = a := by
  cases f
  · exact UInt32.toUInt32_toUInt64 a
  · rfl

theorem fword_eq (f : FWidth) (x : f.width.bits) : Backend2.fword f x = wordOf f.width x := by
  cases f <;> rfl

theorem ibits_wordOf (i : IWidth) (a : i.width.bits) : Backend2.ibits i (wordOf i.width a) = a := by
  cases i
  · exact UInt32.toUInt32_toUInt64 a
  · rfl

theorem iword_eq (i : IWidth) (x : i.width.bits) : Backend2.iword i x = wordOf i.width x := by
  cases i <;> rfl

/-- The interpreter's answer of a host operation from its words' answer. -/
def hostRes : Nat → Option UInt64 → IM LV
  | 0, some w => pure (.int w)
  | 1, some w => pure (.inj (w != 0) .unit)
  | 2, some w => pure (.inj false (.int w))
  | 2, none => pure (.inj true .unit)
  | _, _ => Backend2.bad "a host operation with no answer"

theorem hostOp_pair {op : HostOp} {a b : UInt64} {s : St} (hb : Backend2.isBinary op = true)
    {r : Option UInt64} (hw : Backend2.hostWords op [a, b] = .ok r) :
    (Backend2.hostOp op (.pair (.int a) (.int b))).run s = (hostRes (Backend2.resKind op) r).run s := by
  unfold Backend2.hostOp
  rw [hb]
  dsimp only
  rw [pure_bind, hw]
  rfl

theorem hostOp_int {op : HostOp} {a : UInt64} {s : St} (hb : Backend2.isBinary op = false)
    {r : Option UInt64} (hw : Backend2.hostWords op [a] = .ok r) :
    (Backend2.hostOp op (.int a)).run s = (hostRes (Backend2.resKind op) r).run s := by
  unfold Backend2.hostOp
  rw [hb]
  dsimp only
  rw [pure_bind, hw]
  rfl

theorem vrel_opt {p : Prog} {N : Nat} {w : Width} (o : Option w.bits) :
    VRel p N (Val.opt (o.map (Val.ofBits w))) (match o.map (wordOf w) with
      | some x => .inj false (.int x)
      | none => .inj true .unit) := by
  cases o with
  | none => exact .inj₂ .unit
  | some x => exact .inj₁ (vrel_ofBits w x)

/-- **A host operation at the source is the interpreter's**: on corresponding operands, the
interpreter answers a value corresponding to the source's answer, and leaves the state. -/
theorem host_corr {p : Prog} {N : Nat} {op : HostOp} {v r : Val} {lv : LV}
    (h : Backend2.lirHost.call op v = some r) (hv : VRel p N v lv) (s : St) :
    ∃ lr, (Backend2.hostOp op lv).run s = .ok (lr, s) ∧ VRel p N r lr := by
  cases op with
  | bin w o =>
      cases w with
      | w32 =>
          simp only [Host.call, Option.map_eq_some_iff, args32_argsAt] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          rw [vrel_argsAt hv hab, hostOp_pair rfl (r := some (Backend2.lirHost.bin32 o a b).toUInt64)
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, VRel.lit (.i32 _)⟩
      | w64 =>
          simp only [Host.call, Option.map_eq_some_iff, args64_argsAt] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          rw [vrel_argsAt hv hab, hostOp_pair rfl (r := some (Backend2.lirHost.bin64 o a b))
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, VRel.lit (.i64 _)⟩
      | _ => simp [Host.call] at h
  | div w o =>
      cases w with
      | w32 =>
          simp only [Host.call, Option.map_eq_some_iff, args32_argsAt] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          rw [vrel_argsAt hv hab, hostOp_pair rfl
            (r := (Backend2.lirHost.div32 o a b).map (wordOf .w32))
            (by simp [Backend2.hostWords, wordOf]; rfl)]
          have := vrel_opt (p := p) (N := N) (w := .w32) (Backend2.lirHost.div32 o a b)
          cases hd : Backend2.lirHost.div32 o a b <;> simp_all [Val.ofBits] <;>
            exact ⟨_, rfl, this⟩
      | w64 =>
          simp only [Host.call, Option.map_eq_some_iff, args64_argsAt] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          rw [vrel_argsAt hv hab, hostOp_pair rfl
            (r := Backend2.lirHost.div64 o a b)
            (by simp [Backend2.hostWords, wordOf])]
          have := vrel_opt (p := p) (N := N) (w := .w64) (Backend2.lirHost.div64 o a b)
          cases hd : Backend2.lirHost.div64 o a b <;> simp_all [Val.ofBits] <;>
            exact ⟨_, rfl, this⟩
      | _ => simp [Host.call] at h
  | un w o =>
      cases w with
      | w32 =>
          simp only [Host.call, Option.map_eq_some_iff, arg32_argAt] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.un32 o a).toUInt64)
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, VRel.lit (.i32 _)⟩
      | w64 =>
          simp only [Host.call, Option.map_eq_some_iff, arg64_argAt] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.un64 o a))
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, VRel.lit (.i64 _)⟩
      | _ => simp [Host.call] at h
  | eqz w =>
      cases w with
      | w32 =>
          simp only [Host.call, Option.map_eq_some_iff, arg32_argAt] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.toBit (Backend2.lirHost.eqz32 a)))
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, vrel_bool _⟩
      | w64 =>
          simp only [Host.call, Option.map_eq_some_iff, arg64_argAt] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.toBit (Backend2.lirHost.eqz64 a)))
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, vrel_bool _⟩
      | _ => simp [Host.call] at h
  | rel w o =>
      cases w with
      | w32 =>
          simp only [Host.call, Option.map_eq_some_iff, args32_argsAt] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          rw [vrel_argsAt hv hab, hostOp_pair rfl
            (r := some (Backend2.toBit (Backend2.lirHost.rel32 o a b)))
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, vrel_bool _⟩
      | w64 =>
          simp only [Host.call, Option.map_eq_some_iff, args64_argsAt] at h
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
          rw [vrel_argsAt hv hab, hostOp_pair rfl
            (r := some (Backend2.toBit (Backend2.lirHost.rel64 o a b)))
            (by simp [Backend2.hostWords, wordOf])]
          exact ⟨_, rfl, vrel_bool _⟩
      | _ => simp [Host.call] at h
  | wrap =>
      simp only [Host.call, Option.map_eq_some_iff, arg64_argAt] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.wrap a).toUInt64)
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.i32 _)⟩
  | extend_s =>
      simp only [Host.call, Option.map_eq_some_iff, arg32_argAt] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.extendS a))
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.i64 _)⟩
  | extend_u =>
      simp only [Host.call, Option.map_eq_some_iff, arg32_argAt] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.extendU a))
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.i64 _)⟩
  | extend32_s =>
      simp only [Host.call, Option.map_eq_some_iff, arg64_argAt] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.extend32S a))
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.i64 _)⟩
  | wrap8 =>
      simp only [Host.call, Option.map_eq_some_iff, arg32_argAt] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.wrap8 a).toUInt64)
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.u8 _)⟩
  | extend8_u =>
      simp only [Host.call, Option.map_eq_some_iff, arg8_argAt] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.extend8U a).toUInt64)
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.i32 _)⟩
  | fbin f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
      rw [vrel_argsAt hv hab, hostOp_pair rfl
        (r := some (wordOf f.width (Backend2.lirHost.fbin f o a b)))
        (by simp only [Backend2.hostWords, fbits_wordOf, fword_eq])]
      exact ⟨_, rfl, vrel_ofBits f.width _⟩
  | fun1 f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl
        (r := some (wordOf f.width (Backend2.lirHost.fun1 f o a)))
        (by simp only [Backend2.hostWords, fbits_wordOf, fword_eq])]
      exact ⟨_, rfl, vrel_ofBits f.width _⟩
  | frel f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := h
      rw [vrel_argsAt hv hab, hostOp_pair rfl
        (r := some (Backend2.toBit (Backend2.lirHost.frel f o a b)))
        (by simp only [Backend2.hostWords, fbits_wordOf])]
      exact ⟨_, rfl, vrel_bool _⟩
  | convert f i sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl
        (r := some (wordOf f.width (Backend2.lirHost.convert f i sx a)))
        (by simp only [Backend2.hostWords, ibits_wordOf, fword_eq])]
      exact ⟨_, rfl, vrel_ofBits f.width _⟩
  | trunc i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl
        (r := (Backend2.lirHost.trunc i f sx a).map (wordOf i.width))
        (by simp only [Backend2.hostWords, fbits_wordOf]
            exact congrArg _ (congrArg (Option.map · _) (funext (iword_eq i))))]
      have := vrel_opt (p := p) (N := N) (w := i.width) (Backend2.lirHost.trunc i f sx a)
      cases hd : Backend2.lirHost.trunc i f sx a <;> simp_all <;> exact ⟨_, rfl, this⟩
  | trunc_sat i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl
        (r := some (wordOf i.width (Backend2.lirHost.truncSat i f sx a)))
        (by simp only [Backend2.hostWords, fbits_wordOf, iword_eq])]
      exact ⟨_, rfl, vrel_ofBits i.width _⟩
  | demote =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.demote a).toUInt64)
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.f32 _)⟩
  | promote =>
      simp only [Host.call, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [vrel_argAt hv ha, hostOp_int rfl (r := some (Backend2.lirHost.promote a))
        (by simp [Backend2.hostWords, wordOf])]
      exact ⟨_, rfl, VRel.lit (.f64 _)⟩
  | reinterpret_i f =>
      cases f with
      | f32 =>
          simp only [Host.call, Option.map_eq_some_iff] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (wordOf .f32 a))
            (by simp [Backend2.hostWords])]
          exact ⟨_, rfl, VRel.lit (.i32 _)⟩
      | f64 =>
          simp only [Host.call, Option.map_eq_some_iff] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (wordOf .f64 a))
            (by simp [Backend2.hostWords])]
          exact ⟨_, rfl, VRel.lit (.i64 _)⟩
  | reinterpret_f f =>
      cases f with
      | f32 =>
          simp only [Host.call, Option.map_eq_some_iff, arg32_argAt] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (wordOf .w32 a))
            (by simp [Backend2.hostWords])]
          exact ⟨_, rfl, VRel.lit (.f32 _)⟩
      | f64 =>
          simp only [Host.call, Option.map_eq_some_iff, arg64_argAt] at h
          obtain ⟨a, ha, rfl⟩ := h
          rw [vrel_argAt hv ha, hostOp_int rfl (r := some (wordOf .w64 a))
            (by simp [Backend2.hostWords])]
          exact ⟨_, rfl, VRel.lit (.f64 _)⟩

/-! ### Supporting facts for the simulation -/

theorem pr_le {p : Prog} {N : Nat} {ρ : Nat → Nat} {n n' : Nat} {e : Expr} {t : Tm}
    (h : Pr p N ρ n e t n') : n ≤ n' := by
  induction h <;> omega

theorem psub_var_lt {γ : List Val} {k : Nat} (h : k < γ.length) :
    Expr.psub 0 γ (.var k) = γ[k].1 := by
  simp [Expr.psub, List.getElem?_eq_getElem h, Val.shift_zero]

theorem psub_var_ge {γ : List Val} {k : Nat} (h : γ.length ≤ k) :
    Expr.psub 0 γ (.var k) = .var (k - γ.length) := by
  simp [Expr.psub, List.getElem?_eq_none h]

theorem psub_arm (γ : List Val) (v : Val) (a : Expr) :
    (Expr.psub 1 γ a).subst 0 v = Expr.psub 0 (v :: γ) a := by
  rw [Expr.psub_cons 0 v γ a, Val.shift_zero]

theorem psub_body2 (γ : List Val) (v₁ v₂ : Val) (b : Expr) :
    ((Expr.psub 2 γ b).subst 0 (v₂.shift 1 0)).subst 0 v₁ = Expr.psub 0 (v₂ :: v₁ :: γ) b := by
  rw [Expr.psub_cons₂ 0 v₂ v₁ γ b, Val.shift_zero]

theorem psub_copy (k : Nat) (γ : List Val) : Expr.psub k γ copy = copy :=
  BoCa.Fig16.LogRel.Core.psub_closedAt _ γ rfl (Nat.zero_le k)

theorem psub_forget (k : Nat) (γ : List Val) : Expr.psub k γ forget = forget :=
  BoCa.Fig16.LogRel.Core.psub_closedAt _ γ rfl (Nat.zero_le k)

theorem psub_stuck (k : Nat) (γ : List Val) : Expr.psub k γ BoLo.stuckE = BoLo.stuckE :=
  BoCa.Fig16.LogRel.Core.psub_closedAt _ γ rfl (Nat.zero_le k)

theorem big_var_false {n : Nat} {μ μ' : Heap} {j : Nat} {w : Val}
    (h : BigN (ℍ := Backend2.lirHost) n μ (.var j) μ' w) : False := by
  generalize he : Expr.var j = E at h
  cases h with
  | val => have := he ▸ w.2; simp at this
  | _ => simp at he

theorem big_stuck_false {n : Nat} {μ μ' : Heap} {w : Val}
    (h : BigN (ℍ := Backend2.lirHost) n μ BoLo.stuckE μ' w) : False := by
  obtain ⟨i, j, k, μa, μf, μr, va, vf, r, -, -, -, h₁, h₂, h₃, -⟩ :=
    big_app_inv (f := .unit) h (by simp)
  obtain ⟨rfl, rfl⟩ := big_val_inv h₂ Val.unit rfl
  exact head_nonfun h₃ (by simp [Val.unit]) (by simp [Val.unit]) (by simp [Val.unit])

theorem cnt_of {e : Expr} {k : Nat} {u : Uses} {r : Nat} (h : occ e k = some u)
    (hr : u.ret = some r) : cnt e k = r := by
  obtain ⟨ret, stop⟩ := u
  simp only at hr; subst hr
  simp [cnt, h]

/-- `e`'s uses are `a`'s, then `b`'s past `sh` binders. -/
def SeqOcc (e a b : Expr) (sh : Nat) : Prop :=
  ∀ k, occ e k = (do let ua ← occ a k; let ub ← occ b (k + sh); pure (ua.andThen ub))

theorem SeqOcc.parts {e a b : Expr} {sh : Nat} (h : SeqOcc e a b sh) {k : Nat} {u : Uses}
    (hu : occ e k = some u) : ∃ ua ub, occ a k = some ua ∧ occ b (k + sh) = some ub ∧
      u = ua.andThen ub := by
  rw [h k] at hu
  cases ha : occ a k <;> cases hb : occ b (k + sh) <;> simp_all

theorem SeqOcc.bud_left {e a b : Expr} {sh : Nat} {bud : Nat → Nat} (h : SeqOcc e a b sh)
    (hb : BudOK e bud) : BudOK a bud := by
  intro k
  obtain ⟨u, hu, h₁, h₂⟩ := hb k
  obtain ⟨ua, ub, ha, hb', rfl⟩ := h.parts hu
  exact ⟨ua, ha, bnd_andThen_left ⟨h₁, h₂⟩ (occ_nonempty _ _ _ hb')⟩

theorem SeqOcc.bud_right {e a b : Expr} {sh : Nat} {bud : Nat → Nat} (h : SeqOcc e a b sh)
    (hb : BudOK e bud) (hr : Returns a) :
    ∀ k, ∃ u, occ b (k + sh) = some u ∧ Bnd u (bud k - cnt a k) := by
  intro k
  obtain ⟨u, hu, h₁, h₂⟩ := hb k
  obtain ⟨ua, ub, ha, hb', rfl⟩ := h.parts hu
  obtain ⟨ua', r, ha', hra⟩ := hr k
  rw [ha] at ha'; cases ha'
  have hc : cnt a k = r := cnt_of ha hra
  exact ⟨ub, hb', hc ▸ bnd_andThen_right ⟨h₁, h₂⟩ hra⟩

theorem SeqOcc.returns {e a b : Expr} {sh : Nat} (h : SeqOcc e a b sh) (ha : Returns a)
    (hb : ∀ k, ∃ u r, occ b (k + sh) = some u ∧ u.ret = some r) : Returns e := by
  intro k
  obtain ⟨ua, ra, ha', hra⟩ := ha k
  obtain ⟨ub, rb, hb', hrb⟩ := hb k
  exact ⟨ua.andThen ub, ra + rb, by rw [h k, ha', hb']; rfl, ret_andThen hra hrb⟩

theorem SeqOcc.cnt_eq {e a b : Expr} {sh : Nat} (h : SeqOcc e a b sh) (ha : Returns a)
    (hb : ∀ k, ∃ u r, occ b (k + sh) = some u ∧ u.ret = some r) (k : Nat) :
    cnt e k = cnt a k + cnt b (k + sh) := by
  obtain ⟨ua, ra, ha', hra⟩ := ha k
  obtain ⟨ub, rb, hb', hrb⟩ := hb k
  have he : occ e k = some (ua.andThen ub) := by rw [h k, ha', hb']; rfl
  rw [cnt_of he (ret_andThen hra hrb), cnt_of ha' hra, cnt_of hb' hrb]

theorem seqOcc_pair (a b : Expr) : SeqOcc (.pair a b) a b 0 := fun _ => rfl
theorem seqOcc_seq (a b : Expr) : SeqOcc (.seq a b) a b 0 := fun _ => rfl
theorem seqOcc_app (f a : Expr) : SeqOcc (.app f a) a f 0 := fun _ => rfl
theorem seqOcc_letpair (a b : Expr) : SeqOcc (.letpair a b) a b 2 := fun _ => rfl

theorem returns_var (k : Nat) : Returns (.var k) := fun j => by
  by_cases h : k = j
  · exact ⟨_, 1, by simp [occ, h]; rfl, rfl⟩
  · exact ⟨_, 0, by simp [occ, h]; rfl, rfl⟩

theorem cnt_var (k j : Nat) : cnt (.var k) j = if k = j then 1 else 0 := by
  by_cases h : k = j
  · subst h; simp [cnt, occ, Uses.one]
  · simp [cnt, occ, h, Uses.zero]

theorem returns_closed {e : Expr} (h : ∀ k, occ e k = some Uses.zero) : Returns e :=
  fun k => ⟨_, 0, h k, rfl⟩

/-! ### The simulation, case by case -/

/-- **The simulation of a print**, at derivations of size at most `sz`: a run of the source from
`e` at the values `γ` to `w` is followed by the interpreter from a frame holding the slots of
budget `1`, to a value corresponding to `w`, consuming the slots `e`'s returning paths use. -/
def FwdAt (p : Prog) (N sz : Nat) (ρ : Nat → Nat) (n : Nat) (e : Expr) (t : Tm) (n' : Nat) : Prop :=
  n' ≤ N → ∀ (γ : List Val) (bud : Nat → Nat) (s : St) (μ μ' : Heap) (w : Val) (k : Nat), k ≤ sz →
    BigN (ℍ := Backend2.lirHost) k μ (Expr.psub 0 γ e) μ' w → explicitB isCF e = true →
    coreB e = true → BudOK e bud → FrameOK p N γ ρ n bud s.frame → ∀ rt : LTy,
    ∃ v F', VRel p N w v ∧ μ' = μ ∧ Returns e ∧ Post e ρ bud s.frame F' ∧
      Sim (fun f => Backend2.eval p f rt t) s (.ok (v, ({ s with frame := F' } : St)))

theorem FrameOK.mono {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n m : Nat}
    {bud : Nat → Nat} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ n bud F) (hm : n ≤ m) :
    FrameOK p N γ ρ m bud F :=
  ⟨fun x v hx => lt_of_lt_of_le (h.fresh x v hx) hm, h.le, h.live, h.inj⟩

theorem FrameOK.lt {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {bud : Nat → Nat} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ n bud F) {k : Nat}
    (hk : bud k = 1) : ρ k < n := by
  obtain ⟨_, v, hv, -⟩ := h.live k hk
  exact h.fresh _ _ hv

theorem post_refl_zero {e : Expr} {ρ : Nat → Nat} {bud : Nat → Nat} {F : Std.HashMap Var LV}
    (h : ∀ k, cnt e k = 0) : Post e ρ bud F F :=
  ⟨fun k _ hc => (by rw [h k] at hc; cases hc), fun _ _ => rfl⟩

theorem cnt_closed {e : Expr} (h : ∀ k, occ e k = some Uses.zero) (k : Nat) : cnt e k = 0 :=
  cnt_of (h k) rfl

theorem occ_unit (k : Nat) : occ .unit k = some Uses.zero := rfl
theorem occ_prim (q : Prim) (k : Nat) : occ (.prim q) k = some Uses.zero := rfl
theorem occ_copy (k : Nat) : occ copy k = some ⟨some 0, none⟩ := by
  simp [copy, occ, mentions, BoCa.v0, Expr.val, Val.lam]
theorem occ_forget (k : Nat) : occ forget k = some ⟨some 0, none⟩ := by
  simp [forget, occ, mentions, BoCa.unit', Expr.val, Val.lam, Val.unit]

/-- After a subterm has run and its value is bound to the fresh `x`, the frame holds the slots
the subterm left. -/
theorem FrameOK.after {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n m x : Nat}
    {bud : Nat → Nat} {a : Expr} {F F₁ : Std.HashMap Var LV} {va : LV}
    (hf : FrameOK p N γ ρ n bud F) (hp : Post a ρ bud F F₁) (hx : n ≤ x) (hm : x < m) :
    FrameOK p N γ ρ m (fun k => bud k - cnt a k) (F₁.insert x va) := by
  have hcons : ∀ y : Nat, F₁[y]? ≠ none → F₁[y]? = F[y]? := by
    intro y hy
    apply hp.2 y
    intro k hk hc hρ
    subst hρ
    exact hy (hp.1 k hk hc)
  refine ⟨fun y v hy => ?_, fun k => le_trans (Nat.sub_le _ _) (hf.le k), fun k hk => ?_,
    fun k k' hk hk' he => hf.inj k k' (by have := hf.le k; omega) (by have := hf.le k'; omega) he⟩
  · rw [Std.HashMap.getElem?_insert] at hy
    by_cases hxy : x = y
    · subst hxy; exact hm
    · simp only [beq_iff_eq, hxy, if_false] at hy
      rw [hcons y (by rw [hy]; simp)] at hy
      exact lt_of_lt_of_le (hf.fresh y v hy) (by omega)
  · have hb : bud k = 1 := by have := hf.le k; omega
    have hc : cnt a k = 0 := by have := hf.le k; omega
    obtain ⟨hk', v, hv, hrel⟩ := hf.live k hb
    refine ⟨hk', v, ?_, hrel⟩
    have hne : x ≠ ρ k := by have := hf.fresh _ _ hv; omega
    rw [insert_get_ne hne]
    rw [hp.2 (ρ k) (fun k' hk'' hc' he => by
      have := hf.inj k' k hk'' hb he; subst this; rw [hc] at hc'; cases hc')]
    exact hv

/-! #### Leaves -/

theorem fwd_var {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n k : Nat) :
    FwdAt p N sz ρ n (.var k) (.var (ρ k)) n := by
  intro _ γ bud s μ μ' w kk _ hb _ _ hbud hf rt
  by_cases hk' : k < γ.length
  · rw [psub_var_lt hk'] at hb
    obtain ⟨rfl, rfl⟩ := big_val_inv hb γ[k] rfl
    have hb1 : bud k = 1 := by
      obtain ⟨u, hu, h1, -⟩ := hbud k
      simp only [occ, if_pos, Option.some.injEq] at hu
      subst hu; simp [Uses.one] at h1; have := hf.le k; omega
    obtain ⟨_, v, hv, hrel⟩ := hf.live k hb1
    refine ⟨v, s.frame.erase (ρ k), hrel, rfl, returns_var k, ⟨fun j hj hc => ?_, fun x hx => ?_⟩,
      sim_var hv⟩
    · rw [cnt_var] at hc
      split at hc
      · subst_vars; exact erase_get_self
      · cases hc
    · exact erase_get_ne (hx k hb1 (by simp [cnt_var]))
  · rw [psub_var_ge (by omega)] at hb; exact (big_var_false hb).elim

theorem fwd_unit {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n : Nat) :
    FwdAt p N sz ρ n .unit .unit n := by
  intro _ γ bud s μ μ' w kk _ hb _ _ _ _ rt
  obtain ⟨rfl, rfl⟩ := big_val_inv hb Val.unit rfl
  exact ⟨.unit, s.frame, .unit, rfl, returns_closed occ_unit, post_refl_zero (cnt_closed occ_unit),
    by simpa using sim_unit (p := p) (rt := rt) (s := s)⟩

theorem fwd_lit {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n : Nat) (c : IntLit) :
    FwdAt p N sz ρ n (.prim (.lit c)) (.lit c) n := by
  intro _ γ bud s μ μ' w kk _ hb _ _ _ _ rt
  obtain ⟨rfl, rfl⟩ := big_val_inv hb (Val.prim (.lit c)) rfl
  exact ⟨_, s.frame, .lit c, rfl, returns_closed (occ_prim _),
    post_refl_zero (cnt_closed (occ_prim _)), by simpa using sim_lit (p := p) (rt := rt) (s := s) c⟩

theorem sim_clos_nil {p : Prog} {rt : LTy} {c : Nat} {s : St} :
    Sim (fun f => Backend2.eval p f rt (.clos c [])) s (.ok (.clos c [], s)) := by
  have h := sim_clos (p := p) (rt := rt) (c := c) (env := []) (vs := []) (s := s) rfl
  simpa [eraseL] using h

theorem fwd_hostV {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n : Nat) (op : HostOp) (c : Nat)
    (h : CodeAt p c 0 (hostFn op)) : FwdAt p N sz ρ n (.prim (.host op)) (.clos c []) n := by
  intro _ γ bud s μ μ' w kk _ hb _ _ _ _ rt
  obtain ⟨rfl, rfl⟩ := big_val_inv hb (Val.prim (.host op)) rfl
  exact ⟨_, s.frame, .host op c h, rfl, returns_closed (occ_prim _),
    post_refl_zero (cnt_closed (occ_prim _)), by simpa using sim_clos_nil (p := p) (rt := rt) (c := c) (s := s)⟩

theorem fwd_copyV {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n c : Nat) (h : CodeAt p c 0 copyFn) :
    FwdAt p N sz ρ n copy (.clos c []) n := by
  intro _ γ bud s μ μ' w kk _ hb _ _ _ _ rt
  rw [psub_copy] at hb
  obtain ⟨rfl, rfl⟩ := big_val_inv hb (Val.lam (.pair (.var 0) (.var 0))) rfl
  exact ⟨_, s.frame, .copy c h, rfl, fun k => ⟨_, 0, occ_copy k, rfl⟩,
    post_refl_zero (fun k => cnt_of (occ_copy k) rfl),
    by simpa using sim_clos_nil (p := p) (rt := rt) (c := c) (s := s)⟩

theorem fwd_forgetV {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n c : Nat)
    (h : CodeAt p c 0 forgetFn) : FwdAt p N sz ρ n forget (.clos c []) n := by
  intro _ γ bud s μ μ' w kk _ hb _ _ _ _ rt
  rw [psub_forget] at hb
  obtain ⟨rfl, rfl⟩ := big_val_inv hb (Val.lam .unit) rfl
  exact ⟨_, s.frame, .forget c h, rfl, fun k => ⟨_, 0, occ_forget k, rfl⟩,
    post_refl_zero (fun k => cnt_of (occ_forget k) rfl),
    by simpa using sim_clos_nil (p := p) (rt := rt) (c := c) (s := s)⟩

/-! #### Closures -/

theorem mem_capt {b : Expr} {k : Nat} : k ∈ capt b ↔ mentions b (k + 1) = true := by
  simp only [capt, List.mem_filter, List.mem_range, and_iff_right_iff_imp]
  intro h; have := mentions_lt h; omega

theorem capt_nodup (b : Expr) : (capt b).Nodup := (List.nodup_range).filter _

theorem occ_lam (b : Expr) (k : Nat) :
    occ (.lam b) k = some ⟨some (if mentions b (k + 1) then 1 else 0), none⟩ := rfl

theorem cnt_lam (b : Expr) (k : Nat) : cnt (.lam b) k = if mentions b (k + 1) then 1 else 0 :=
  cnt_of (occ_lam b k) rfl

theorem isCF_lam {b : Expr} (hcp : Expr.lam b ≠ copy) (hfg : Expr.lam b ≠ forget) :
    isCF (.lam b) = false := by
  simp only [isCF, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; exact ⟨hcp, hfg⟩

theorem explicitB_lam {b : Expr} (hcp : Expr.lam b ≠ copy) (hfg : Expr.lam b ≠ forget)
    (h : explicitB isCF (.lam b) = true) :
    explicitB isCF b = true ∧ once (occ b 0) = true ∧ capOnceB b = true := by
  rw [explicitB, isCF_lam hcp hfg, Bool.false_or] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem fwd_lam {p : Prog} {N sz : Nat} (ρ : Nat → Nat) (n m : Nat) (b : Expr) (tb : Tm) (c : Nat)
    (hcp : Expr.lam b ≠ copy) (hfg : Expr.lam b ≠ forget)
    (hpr : Pr p N (lamEnv b) ((capt b).length + 1) b tb m) (hm : m ≤ N)
    (hc : CodeAt p c (capt b).length tb) :
    FwdAt p N sz ρ n (.lam b) (.clos c ((capt b).map ρ)) n := by
  intro _ γ bud s μ μ' w kk _ hb hx hcore hbud hf rt
  obtain ⟨rfl, rfl⟩ := big_val_inv hb (Val.lam (Expr.psub 1 γ b)) rfl
  obtain ⟨hxb, h0, hcap⟩ := explicitB_lam hcp hfg hx
  have hbud1 : ∀ k, k ∈ capt b → bud k = 1 := by
    intro k hk
    obtain ⟨u, hu, h1, -⟩ := hbud k
    rw [occ_lam, Option.some.injEq] at hu; subst hu
    simp only [mem_capt.mp hk, if_true, Option.getD_some] at h1
    have := hf.le k; omega
  have hnd : ((capt b).map ρ).Nodup :=
    (capt_nodup b).map_on fun k hk k' hk' he => hf.inj k k' (hbud1 k hk) (hbud1 k' hk') he
  obtain ⟨vs, hrun, hlen, hget⟩ := takeAll_run ((capt b).map ρ) s hnd (fun x hx' => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨_, v, hv, -⟩ := hf.live k (hbud1 k hk)
    exact ⟨v, hv⟩)
  refine ⟨.clos c vs, eraseL s.frame ((capt b).map ρ), ?_, rfl,
    fun k => ⟨_, _, occ_lam b k, rfl⟩, ⟨fun k hk hck => ?_, fun x hxk => ?_⟩, sim_clos hrun⟩
  · refine .lam hcp hfg hpr hm hc hxb h0 hcap (by simpa [coreB] using hcore) (by simpa using hlen)
      (fun k hk => (hf.live k (hbud1 k hk)).1) (fun i hi k hk hik => ?_)
    have hi' : i < (capt b).length := by rw [hlen] at hi; simpa using hi
    have hk' : (capt b)[i] = k := by simpa [List.getElem?_eq_getElem hi'] using hik
    have hkm : k ∈ capt b := hk' ▸ List.getElem_mem hi'
    obtain ⟨_, v, hv, hrel⟩ := hf.live k (hbud1 k hkm)
    have := hget i (by simpa using hi')
    simp only [List.getElem_map, hk', hv, List.getElem?_eq_getElem hi] at this
    cases this
    exact hrel
  · rw [cnt_lam] at hck
    split at hck
    · rename_i hmk
      rw [eraseL_get, if_pos (List.mem_map.mpr ⟨k, mem_capt.mpr hmk, rfl⟩)]
    · cases hck
  · rw [eraseL_get, if_neg]
    intro hxm
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hxm
    exact hxk k (hbud1 k hk) (by rw [cnt_lam, if_pos (mem_capt.mp hk)]) rfl

/-! #### Frames after a sequence -/

theorem cnt_le_bud {e : Expr} {bud : Nat → Nat} (hb : BudOK e bud) (k : Nat) : cnt e k ≤ bud k := by
  obtain ⟨u, hu, h1, -⟩ := hb k
  obtain ⟨ret, stop⟩ := u
  cases ret with
  | none => simp [cnt, hu]
  | some r => simpa [cnt, hu] using h1

theorem Post.high {e : Expr} {ρ : Nat → Nat} {bud : Nat → Nat} {F F₁ : Std.HashMap Var LV}
    {p : Prog} {N : Nat} {γ : List Val} {n : Nat} (hf : FrameOK p N γ ρ n bud F)
    (hp : Post e ρ bud F F₁) {z : Nat} (hz : n ≤ z) : F₁[z]? = none := by
  rw [hp.2 z (fun k (hk : bud k = 1) _ he => by
    have hlt := hf.lt hk; rw [he] at hlt; omega)]
  cases h : F[z]? with
  | none => rfl
  | some v => have := hf.fresh z v h; omega

/-- **The frame after one part**, when the rest consumes only fresh variables. -/
theorem post_one {e a : Expr} {ρ : Nat → Nat} {bud : Nat → Nat} {F F₁ F' : Std.HashMap Var LV}
    {p : Prog} {N : Nat} {γ : List Val} {n : Nat} (hf : FrameOK p N γ ρ n bud F)
    (hpa : Post a ρ bud F F₁) (hcnt : ∀ k, cnt e k = cnt a k)
    (hlow : ∀ z : Nat, z < n → F'[z]? = F₁[z]?) (hhigh : ∀ z : Nat, n ≤ z → F'[z]? = none) :
    Post e ρ bud F F' := by
  refine ⟨fun k hk hc => ?_, fun x hx => ?_⟩
  · rw [hlow _ (hf.lt hk)]; exact hpa.1 k hk (hcnt k ▸ hc)
  · by_cases hxn : x < n
    · rw [hlow x hxn]; exact hpa.2 x fun k hk hc => hx k hk (by rw [hcnt]; exact hc)
    · rw [hhigh x (by omega)]
      cases h : F[x]? with
      | none => rfl
      | some v => have := hf.fresh x v h; omega

/-- **The frame after two parts**: the first `a` at the budget `bud`, the second (`cntB`) at what
`a` left, from a frame `G` that agrees with `a`'s below `n`. -/
theorem post_two {e a : Expr} {cntB : Nat → Nat} {ρ : Nat → Nat} {bud : Nat → Nat}
    {F F₁ G F₂ F' : Std.HashMap Var LV} {p : Prog} {N : Nat} {γ : List Val} {n : Nat}
    (hf : FrameOK p N γ ρ n bud F) (hpa : Post a ρ bud F F₁)
    (hG : ∀ z : Nat, z < n → G[z]? = F₁[z]?)
    (hpb1 : ∀ k, bud k - cnt a k = 1 → cntB k = 1 → F₂[ρ k]? = none)
    (hpb2 : ∀ x : Nat, x < n → (∀ k, bud k - cnt a k = 1 → cntB k = 1 → ρ k ≠ x) →
      F₂[x]? = G[x]?)
    (hcnt : ∀ k, cnt e k = cnt a k + cntB k) (hle : ∀ k, cnt e k ≤ bud k)
    (hlow : ∀ z : Nat, z < n → F'[z]? = F₂[z]?) (hhigh : ∀ z : Nat, n ≤ z → F'[z]? = none) :
    Post e ρ bud F F' := by
  refine ⟨fun k hk hc => ?_, fun x hx => ?_⟩
  · have hρ := hf.lt hk
    rw [hlow _ hρ]
    have := hcnt k; have := hle k
    by_cases ha : cnt a k = 1
    · rw [hpb2 _ hρ (fun k' hk' hc' he => by
        have hb' : bud k' = 1 := by have := hf.le k'; omega
        have := hf.inj k' k hb' hk he; subst this; omega), hG _ hρ]
      exact hpa.1 k hk ha
    · exact hpb1 k (by omega) (by omega)
  · by_cases hxn : x < n
    · rw [hlow x hxn, hpb2 x hxn (fun k (hk : bud k - cnt a k = 1) (hc : cntB k = 1) =>
        hx k (by have := hf.le k; omega) (by have := hf.le k; rw [hcnt]; omega)), hG x hxn]
      exact hpa.2 x fun k (hk : bud k = 1) (hc : cnt a k = 1) =>
        hx k hk (by have := hcnt k; have := hle k; omega)
    · rw [hhigh x (by omega)]
      cases h : F[x]? with
      | none => rfl
      | some v => have := hf.fresh x v h; omega

theorem isCF_pair (a b : Expr) : isCF (.pair a b) = false := by simp [isCF, copy, forget]
theorem isCF_seq (a b : Expr) : isCF (.seq a b) = false := by simp [isCF, copy, forget]
theorem isCF_app (a b : Expr) : isCF (.app a b) = false := by simp [isCF, copy, forget]
theorem isCF_letpair (a b : Expr) : isCF (.letpair a b) = false := by simp [isCF, copy, forget]
theorem isCF_case (v a b : Expr) : isCF (.case v a b) = false := by simp [isCF, copy, forget]
theorem isCF_inj₁ (a : Expr) : isCF (.inj₁ a) = false := by simp [isCF, copy, forget]
theorem isCF_inj₂ (a : Expr) : isCF (.inj₂ a) = false := by simp [isCF, copy, forget]

/-! #### Pairs -/

theorem fwd_pair {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {a b : Expr} {ta tb : Tm}
    (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (ha : Pr p N ρ (n + 2) a ta n₁) (hb : Pr p N ρ n₁ b tb n₂)
    (iha : FwdAt p N sz ρ (n + 2) a ta n₁) (ihb : FwdAt p N sz ρ n₁ b tb n₂) :
    FwdAt p N sz ρ n (.pair a b) (.letv n ta (.letv (n + 1) tb (.pair n (n + 1)))) n₂ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le ha; have hn₂ := pr_le hb
  simp only [Expr.psub] at hbig
  obtain ⟨i, j, μ₁, u₁, u₂, hi, hj, hba, hbb, rfl⟩ := big_pair_inv hbig
  rw [explicitB, isCF_pair, Bool.false_or, Bool.and_eq_true] at hx
  simp only [coreB, Bool.and_eq_true] at hcore
  obtain ⟨va, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s μ μ₁ u₁ i (by omega) hba hx.1
    hcore.1 ((seqOcc_pair a b).bud_left hbud) (hf.mono (by omega)) LTy.unit
  have hbr := (seqOcc_pair a b).bud_right hbud hra
  obtain ⟨vb, F₂, hvb, rfl, hrb, hpb, hsb⟩ := ihb (by omega) γ (fun k => bud k - cnt a k)
    ({ s with frame := F₁.insert n va } : St) _ _ u₂ j (by omega) hbb hx.2 hcore.2
    (fun k => by simpa [Bnd] using hbr k) (hf.after hpa (le_refl n) (by omega)) LTy.unit
  have hrb' : ∀ k, ∃ u r, occ b (k + 0) = some u ∧ u.ret = some r := fun k => by simpa using hrb k
  have hF₂n : F₂[n]? = some va := by
    rw [hpb.2 n (fun k (hk : bud k - cnt a k = 1) _ he => by
      have hlt := hf.lt (k := k) (by have := hf.le k; omega)
      rw [he] at hlt; exact Nat.lt_irrefl _ hlt)]
    exact insert_get_self
  have hne : n ≠ n + 1 := by omega
  refine ⟨.pair va vb, ((F₂.insert (n + 1) vb).erase n).erase (n + 1), .pair hva hvb, rfl,
    (seqOcc_pair a b).returns hra hrb', ?_, ?_⟩
  · refine post_two (cntB := cnt b) hf hpa (G := F₁.insert n va) (F₂ := F₂)
      (fun z hz => insert_get_ne (by omega)) (fun k h1 h2 => hpb.1 k h1 h2)
      (fun x _ h => hpb.2 x h) (fun k => by simpa using (seqOcc_pair a b).cnt_eq hra hrb' k)
      (cnt_le_bud hbud) (fun z hz => ?_) (fun z hz => ?_)
    · rw [erase_get_ne (by omega), erase_get_ne (by omega), insert_get_ne (by omega)]
    · by_cases h1 : z = n + 1
      · subst h1; exact erase_get_self
      · rw [erase_get_ne (Ne.symm h1)]
        by_cases h2 : z = n
        · subst h2; exact erase_get_self
        · rw [erase_get_ne (Ne.symm h2), insert_get_ne (Ne.symm h1)]
          rw [hpb.2 z (fun k (hk : bud k - cnt a k = 1) _ he => by
            have hlt := hf.lt (k := k) (by have := hf.le k; omega)
            rw [he] at hlt; omega)]
          rw [insert_get_ne (Ne.symm h2)]
          exact hpa.high hf hz
  · refine sim_letv (hty n (by omega)) hsa (sim_letv (hty (n + 1) (by omega)) hsb ?_)
    have h1 : (F₂.insert (n + 1) vb)[n]? = some va := by rw [insert_get_ne (Ne.symm hne)]; exact hF₂n
    have h2 : ((F₂.insert (n + 1) vb).erase n)[n + 1]? = some vb := by
      rw [erase_get_ne hne]; exact insert_get_self
    exact sim_pair h1 h2

/-! #### More frames and uses -/

theorem isEmpty_of_none {F : Std.HashMap Var LV} (h : ∀ x : Nat, F[x]? = none) : F.isEmpty = true := by
  rw [Std.HashMap.isEmpty_iff_forall_not_mem]
  intro x hx
  rw [Std.HashMap.mem_iff_isSome_getElem?, h x] at hx
  simp at hx

theorem FrameOK.congr {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {bud : Nat → Nat} {F G : Std.HashMap Var LV} (h : FrameOK p N γ ρ n bud F)
    (hG : ∀ x : Nat, G[x]? = F[x]?) : FrameOK p N γ ρ n bud G :=
  ⟨fun x v hx => h.fresh x v (hG x ▸ hx), h.le, fun k hk => by
    obtain ⟨hk', v, hv, hr⟩ := h.live k hk; exact ⟨hk', v, (hG _).trans hv, hr⟩, h.inj⟩

/-- The frame of a function's call: its parameters `0, …` at the arguments. -/
theorem zipFrame_get : ∀ (vs : List LV) (x : Nat),
    ((List.range vs.length).zip vs |>.foldl (fun m x => m.insert x.1 x.2) (∅ : Std.HashMap Var LV))[x]? =
      vs[x]? := by
  intro vs
  induction vs using List.reverseRecOn with
  | nil => intro x; simp
  | append_singleton vs v ih =>
      intro x
      rw [List.length_append, List.length_singleton, List.range_succ,
        List.zip_append (by simp), List.foldl_append]
      simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil]
      rw [Std.HashMap.getElem?_insert]
      by_cases hx : vs.length = x
      · subst hx; simp
      · simp only [beq_iff_eq, hx, if_false, ih]
        by_cases hlt : x < vs.length
        · rw [List.getElem?_append_left hlt]
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem bnd_andThen_mk {a b : Uses} {B₁ B₂ : Nat} (ha : Bnd a B₁) (hb : Bnd b B₂) :
    Bnd (a.andThen b) (B₁ + B₂) := by
  unfold Uses.andThen
  cases hr : a.ret with
  | none => exact ⟨by simp [hr],
      le_trans ha.2 (Nat.le_add_right _ _)⟩
  | some r =>
      have hra : r ≤ B₁ := by simpa [hr] using ha.1
      refine ⟨?_, maxO_le (le_trans ha.2 (Nat.le_add_right _ _)) ?_⟩
      · have := hb.1; cases hb' : b.ret <;> simp_all; omega
      · have := hb.2; cases hb' : b.stop <;> simp_all; omega

theorem bnd_join {a b : Uses} (ha : Bnd a 0) (hb : Bnd b 0) :
    ∃ j, Uses.join a b = some j ∧ Bnd j 0 := by
  obtain ⟨ar, as⟩ := a
  obtain ⟨br, bs⟩ := b
  simp only [Bnd] at ha hb
  have hs : (maxO as bs).getD 0 ≤ 0 := maxO_le ha.2 hb.2
  cases ar with
  | none =>
      cases br with
      | none => exact ⟨_, rfl, by simp, hs⟩
      | some y =>
          have : y = 0 := by simpa using hb.1
          subst this; exact ⟨_, rfl, by simp, hs⟩
  | some x =>
      have : x = 0 := by simpa using ha.1
      subst this
      cases br with
      | none => exact ⟨_, rfl, by simp, hs⟩
      | some y =>
          have : y = 0 := by simpa using hb.1
          subst this; exact ⟨_, rfl, by simp, hs⟩

/-- **A slot a term does not mention** is used on none of its paths. -/
theorem occ_unmentioned : ∀ (e : Expr) (k : Nat), mentions e k = false →
    ∃ u, occ e k = some u ∧ Bnd u 0 := by
  intro e
  induction e with
  | var j =>
      intro k h
      simp only [mentions, beq_eq_false_iff_ne, ne_eq] at h
      exact ⟨_, rfl, by simp [h, Uses.zero, Bnd]⟩
  | unit | loc _ | prim _ => intro k _; exact ⟨_, rfl, by simp [Uses.zero, Bnd]⟩
  | pair a b iha ihb | seq a b iha ihb =>
      intro k h
      simp only [mentions, Bool.or_eq_false_iff] at h
      obtain ⟨ua, ha, ba⟩ := iha k h.1
      obtain ⟨ub, hb, bb⟩ := ihb k h.2
      exact ⟨ua.andThen ub, by simp [occ, ha, hb], bnd_andThen_mk ba bb⟩
  | app f a ihf iha =>
      intro k h
      simp only [mentions, Bool.or_eq_false_iff] at h
      obtain ⟨ua, ha, ba⟩ := iha k h.2
      obtain ⟨uf, hf, bf⟩ := ihf k h.1
      exact ⟨ua.andThen uf, by simp [occ, ha, hf], bnd_andThen_mk ba bf⟩
  | letpair a b iha ihb =>
      intro k h
      simp only [mentions, Bool.or_eq_false_iff] at h
      obtain ⟨ua, ha, ba⟩ := iha k h.1
      obtain ⟨ub, hb, bb⟩ := ihb (k + 2) h.2
      exact ⟨ua.andThen ub, by simp [occ, ha, hb], bnd_andThen_mk ba bb⟩
  | inj₁ a ih | inj₂ a ih => intro k h; exact ih k h
  | lam b _ =>
      intro k h
      simp only [mentions] at h
      exact ⟨_, rfl, by simp [h, Bnd]⟩
  | case v a b ihv iha ihb =>
      intro k h
      simp only [mentions, Bool.or_eq_false_iff] at h
      obtain ⟨uv, hv, bv⟩ := ihv k h.1.1
      by_cases hab : a = BoLo.stuckE ∧ b = BoLo.stuckE
      · have hh : Bnd Uses.halt 0 := by simp [Uses.halt, Bnd]
        exact ⟨uv.andThen Uses.halt, by simp [occ, hab, hv], bnd_andThen_mk bv hh⟩
      · obtain ⟨ua, ha, ba⟩ := iha (k + 1) h.1.2
        obtain ⟨ub, hb, bb⟩ := ihb (k + 1) h.2
        obtain ⟨j, hj, bj⟩ := bnd_join ba bb
        exact ⟨uv.andThen j, by simp [occ, hab, hv, ha, hb, hj], bnd_andThen_mk bv bj⟩

/-- `once` bounds the uses by `1`. -/
theorem once_bnd {o : Option Uses} (h : once o = true) : ∃ u, o = some u ∧ Bnd u 1 := by
  obtain _ | ⟨r, st⟩ := o
  · simp [once] at h
  · refine ⟨_, rfl, ?_, ?_⟩
    · simp only [once, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      rcases h.1 with h1 | h1 <;> simp [h1]
    · simp only [once, Bool.and_eq_true] at h
      cases st with
      | none => simp
      | some x => simpa using h.2

/-- `once`, on a returning path, is a use of exactly one. -/
theorem once_ret {o : Option Uses} {u : Uses} {r : Nat} (h : once o = true) (ho : o = some u)
    (hr : u.ret = some r) : r = 1 := by
  subst ho
  obtain ⟨ret, st⟩ := u
  simp only at hr; subst hr
  simp only [once, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.some.injEq,
    reduceCtorEq, or_false] at h
  exact h.1

/-! #### One part, then an operation on its value -/

/-- The frame after one part whose value at the fresh `x` is then consumed, with what else is
fresh: below `n` it is the part's, above it empty. -/
theorem post_low_high {a : Expr} {ρ : Nat → Nat} {bud : Nat → Nat} {F F₁ : Std.HashMap Var LV}
    {p : Prog} {N : Nat} {γ : List Val} {n : Nat} (hf : FrameOK p N γ ρ n bud F)
    (hpa : Post a ρ bud F F₁) {x : Nat} (hx : n ≤ x) {va : LV} :
    (∀ z : Nat, z < n → ((F₁.insert x va).erase x)[z]? = F₁[z]?) ∧
      (∀ z : Nat, n ≤ z → ((F₁.insert x va).erase x)[z]? = none) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [erase_get_ne (by omega), insert_get_ne (by omega)]
  · by_cases hzx : x = z
    · subst hzx; exact erase_get_self
    · rw [erase_get_ne hzx, insert_get_ne hzx]; exact hpa.high hf hz

theorem fwd_inj {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ : Nat} {a : Expr} {ta : Tm}
    (r : Bool) (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (ha : Pr p N ρ (n + 1) a ta n₁) (iha : FwdAt p N sz ρ (n + 1) a ta n₁) :
    FwdAt p N sz ρ n (if r then .inj₂ a else .inj₁ a) (.letv n ta (.inj r n)) n₁ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le ha
  have hocc : ∀ k, occ (if r then .inj₂ a else .inj₁ a) k = occ a k := by
    intro k; cases r <;> rfl
  have hcnt : ∀ k, cnt (if r then .inj₂ a else .inj₁ a) k = cnt a k := by
    intro k; simp only [cnt, hocc]
  have hbud' : BudOK a bud := fun k => by rw [← hocc]; exact hbud k
  have hxa : explicitB isCF a = true := by
    cases r <;> simpa [explicitB, isCF_inj₁, isCF_inj₂] using hx
  have hca : coreB a = true := by cases r <;> simpa [coreB] using hcore
  have key : ∃ i u, i ≤ kk ∧ BigN (ℍ := Backend2.lirHost) i μ (Expr.psub 0 γ a) μ' u ∧
      w = (if r then Val.inj₂ u else Val.inj₁ u) := by
    cases r
    · obtain ⟨i, u, hi, h, rfl⟩ := big_inj₁_inv (by simpa [Expr.psub] using hbig)
      exact ⟨i, u, hi, h, rfl⟩
    · obtain ⟨i, u, hi, h, rfl⟩ := big_inj₂_inv (by simpa [Expr.psub] using hbig)
      exact ⟨i, u, hi, h, rfl⟩
  obtain ⟨i, u, hi, hba, rfl⟩ := key
  obtain ⟨va, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s _ _ u i (by omega) hba hxa
    hca hbud' (hf.mono (by omega)) LTy.unit
  obtain ⟨hlow, hhigh⟩ := post_low_high (va := va) hf hpa (le_refl n)
  refine ⟨.inj r va, (F₁.insert n va).erase n, ?_, rfl, fun k => by rw [hocc]; exact hra k,
    post_one hf hpa hcnt hlow hhigh, sim_letv (hty n (by omega)) hsa (sim_inj insert_get_self)⟩
  cases r
  · exact .inj₁ hva
  · exact .inj₂ hva

theorem fwd_absurd {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ : Nat} {v : Expr} {ts : Tm} :
    FwdAt p N sz ρ n (absurdL v) (.letv n ts (.absurd n)) n₁ := by
  intro _ γ bud s μ μ' w kk _ hbig _ _ _ _ _
  simp only [absurdL, Expr.psub, psub_stuck] at hbig
  rcases big_case_inv hbig with ⟨i, j, μ₁, u, -, -, -, h⟩ | ⟨i, j, μ₁, u, -, -, -, h⟩ <;>
    rw [show BoLo.stuckE.subst 0 u = BoLo.stuckE from rfl] at h <;>
    exact (big_stuck_false h).elim

theorem FrameOK.erase {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {n : Nat}
    {bud : Nat → Nat} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ n bud F) {x : Nat}
    (hx : ∀ k, bud k = 1 → ρ k ≠ x) : FrameOK p N γ ρ n bud (F.erase x) := by
  refine ⟨fun y v hy => ?_, h.le, fun k hk => ?_, h.inj⟩
  · by_cases hxy : x = y
    · subst hxy; rw [erase_get_self] at hy; cases hy
    · rw [erase_get_ne hxy] at hy; exact h.fresh y v hy
  · obtain ⟨hk', v, hv, hr⟩ := h.live k hk
    exact ⟨hk', v, by rw [erase_get_ne (Ne.symm (hx k hk))]; exact hv, hr⟩

theorem occ_forget' (k : Nat) : occ forget (k + 0) = some ⟨some 0, none⟩ := occ_forget _
theorem occ_copy' (k : Nat) : occ copy (k + 0) = some ⟨some 0, none⟩ := occ_copy _

theorem fwd_seq {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {a b : Expr} {ta tb : Tm}
    (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (ha : Pr p N ρ (n + 1) a ta n₁) (hb : Pr p N ρ n₁ b tb n₂)
    (iha : FwdAt p N sz ρ (n + 1) a ta n₁) (ihb : FwdAt p N sz ρ n₁ b tb n₂) :
    FwdAt p N sz ρ n (.seq a b) (.letv n ta (.drop n tb)) n₂ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le ha; have hn₂ := pr_le hb
  simp only [Expr.psub] at hbig
  obtain ⟨i, j, μ₁, hi, hj, hba, hbb⟩ := big_seq_inv hbig
  rw [explicitB, isCF_seq, Bool.false_or, Bool.and_eq_true] at hx
  simp only [coreB, Bool.and_eq_true] at hcore
  obtain ⟨va, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s _ _ Val.unit i (by omega) hba
    hx.1 hcore.1 ((seqOcc_seq a b).bud_left hbud) (hf.mono (by omega)) LTy.unit
  obtain rfl := vrel_unit_inv hva
  have hbr := (seqOcc_seq a b).bud_right hbud hra
  have hG : FrameOK p N γ ρ n₁ (fun k => bud k - cnt a k) ((F₁.insert n LV.unit).erase n) :=
    (hf.after hpa (le_refl n) (by omega)).erase (fun k hk he => by
      have hlt := hf.lt (k := k) (by have := hf.le k; omega); omega)
  obtain ⟨w', F₂, hw, rfl, hrb, hpb, hsb⟩ := ihb (by omega) γ (fun k => bud k - cnt a k)
    ({ s with frame := (F₁.insert n LV.unit).erase n } : St) _ _ w j (by omega) hbb hx.2 hcore.2
    (fun k => by simpa [Bnd] using hbr k) hG rt
  have hrb' : ∀ k, ∃ u r, occ b (k + 0) = some u ∧ u.ret = some r := fun k => by simpa using hrb k
  obtain ⟨hlow, hhigh⟩ := post_low_high (va := LV.unit) hf hpa (le_refl n)
  refine ⟨w', F₂, hw, rfl, (seqOcc_seq a b).returns hra hrb', ?_, ?_⟩
  · refine post_two (cntB := cnt b) hf hpa (G := (F₁.insert n LV.unit).erase n) (F₂ := F₂) hlow
      (fun k h1 h2 => hpb.1 k h1 h2) (fun x _ h => hpb.2 x h)
      (fun k => by simpa using (seqOcc_seq a b).cnt_eq hra hrb' k) (cnt_le_bud hbud)
      (fun z _ => rfl) (fun z hz => ?_)
    rw [hpb.2 z (fun k (hk : bud k - cnt a k = 1) _ he => by
      have hlt := hf.lt (k := k) (by have := hf.le k; omega); omega)]
    exact hhigh z hz
  · exact sim_letv (hty n (by omega)) hsa (sim_drop (hty n (by omega)) insert_get_self hsb)

theorem fwd_appForget {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ : Nat} {a : Expr} {ta : Tm}
    (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (ha : Pr p N ρ (n + 1) a ta n₁) (iha : FwdAt p N sz ρ (n + 1) a ta n₁) :
    FwdAt p N sz ρ n (.app forget a) (.letv n ta (.drop n .unit)) n₁ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le ha
  simp only [Expr.psub, psub_forget] at hbig
  obtain ⟨i, j, k, μa, μf, μr, va, vf, r, hi, -, -, hba, hbf, hh, hbr⟩ :=
    big_app_inv hbig (by simp [forget, Expr.val, Val.lam])
  obtain ⟨rfl, rfl⟩ := big_val_inv hbf (Val.lam .unit) rfl
  obtain ⟨rfl, rfl⟩ := head_lam_inv hh
  obtain ⟨rfl, rfl⟩ := big_val_inv hbr Val.unit rfl
  rw [explicitB, isCF_app, Bool.false_or, Bool.and_eq_true] at hx
  simp only [coreB, Bool.and_eq_true] at hcore
  obtain ⟨lva, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s _ _ va i (by omega) hba
    hx.2 hcore.2 ((seqOcc_app forget a).bud_left hbud) (hf.mono (by omega)) LTy.unit
  have hrf : ∀ k, ∃ u r, occ forget (k + 0) = some u ∧ u.ret = some r :=
    fun k => ⟨_, 0, occ_forget' k, rfl⟩
  obtain ⟨hlow, hhigh⟩ := post_low_high (va := lva) hf hpa (le_refl n)
  refine ⟨.unit, (F₁.insert n lva).erase n, .unit, rfl, (seqOcc_app forget a).returns hra hrf,
    post_one hf hpa (fun k => by
      rw [(seqOcc_app forget a).cnt_eq hra hrf k, cnt_of (occ_forget' k) rfl, Nat.add_zero]) hlow hhigh,
    sim_letv (hty n (by omega)) hsa (sim_drop (hty n (by omega)) insert_get_self sim_unit)⟩

theorem fwd_appCopy {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ : Nat} {a : Expr} {ta : Tm}
    (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (ha : Pr p N ρ (n + 2) a ta n₁) (iha : FwdAt p N sz ρ (n + 2) a ta n₁) :
    FwdAt p N sz ρ n (.app copy a) (.letv n ta (.copy n (n + 1) (.pair n (n + 1)))) n₁ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le ha
  simp only [Expr.psub, psub_copy] at hbig
  obtain ⟨i, j, k, μa, μf, μr, va, vf, r, hi, -, -, hba, hbf, hh, hbr⟩ :=
    big_app_inv hbig (by simp [copy, Expr.val, Val.lam])
  obtain ⟨rfl, rfl⟩ := big_val_inv hbf (Val.lam (.pair (.var 0) (.var 0))) rfl
  obtain ⟨rfl, rfl⟩ := head_lam_inv hh
  obtain ⟨rfl, rfl⟩ := big_val_inv hbr (Val.pair va va) rfl
  rw [explicitB, isCF_app, Bool.false_or, Bool.and_eq_true] at hx
  simp only [coreB, Bool.and_eq_true] at hcore
  obtain ⟨lva, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s _ _ va i (by omega) hba
    hx.2 hcore.2 ((seqOcc_app copy a).bud_left hbud) (hf.mono (by omega)) LTy.unit
  have hrf : ∀ k, ∃ u r, occ copy (k + 0) = some u ∧ u.ret = some r :=
    fun k => ⟨_, 0, occ_copy' k, rfl⟩
  have hne : n ≠ n + 1 := by omega
  refine ⟨.pair lva lva, (((F₁.insert n lva).insert (n + 1) lva).erase n).erase (n + 1),
    .pair hva hva, rfl, (seqOcc_app copy a).returns hra hrf,
    post_one hf hpa (fun k => by
      rw [(seqOcc_app copy a).cnt_eq hra hrf k, cnt_of (occ_copy' k) rfl, Nat.add_zero]) (fun z hz => ?_)
      (fun z hz => ?_), ?_⟩
  · rw [erase_get_ne (by omega), erase_get_ne (by omega), insert_get_ne (by omega),
      insert_get_ne (by omega)]
  · by_cases h1 : z = n + 1
    · subst h1; exact erase_get_self
    · rw [erase_get_ne (Ne.symm h1)]
      by_cases h2 : z = n
      · subst h2; exact erase_get_self
      · rw [erase_get_ne (Ne.symm h2), insert_get_ne (Ne.symm h1), insert_get_ne (Ne.symm h2)]
        exact hpa.high hf hz
  · have h1 : ((F₁.insert n lva).insert (n + 1) lva)[n]? = some lva := by
      rw [insert_get_ne (Ne.symm hne)]; exact insert_get_self
    have h2 : (((F₁.insert n lva).insert (n + 1) lva).erase n)[n + 1]? = some lva := by
      rw [erase_get_ne hne]; exact insert_get_self
    exact sim_letv (hty n (by omega)) hsa (sim_copy (hty n (by omega)) insert_get_self
      (sim_pair h1 h2))

theorem fwd_appHost {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ : Nat} {a : Expr} {ta : Tm}
    (op : HostOp) (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (ha : Pr p N ρ (n + 1) a ta n₁) (iha : FwdAt p N sz ρ (n + 1) a ta n₁) :
    FwdAt p N sz ρ n (.app (.prim (.host op)) a) (.letv n ta (.prim (.host op) [n])) n₁ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le ha
  simp only [Expr.psub] at hbig
  obtain ⟨i, j, k, μa, μf, μr, va, vf, r, hi, -, -, hba, hbf, hh, hbr⟩ :=
    big_app_inv hbig (by simp)
  obtain ⟨rfl, rfl⟩ := big_val_inv hbf (Val.prim (.host op)) rfl
  obtain ⟨rfl, r', hcall, rfl⟩ := head_host_inv hh
  obtain ⟨rfl, rfl⟩ := big_val_inv hbr r' rfl
  rw [explicitB, isCF_app, Bool.false_or, Bool.and_eq_true] at hx
  simp only [coreB, Bool.and_eq_true] at hcore
  obtain ⟨lva, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s _ _ va i (by omega) hba
    hx.2 hcore.2 ((seqOcc_app (.prim (.host op)) a).bud_left hbud) (hf.mono (by omega)) LTy.unit
  have hrf : ∀ k, ∃ u r, occ (.prim (.host op)) (k + 0) = some u ∧ u.ret = some r :=
    fun k => ⟨_, 0, rfl, rfl⟩
  obtain ⟨lr, hrun, hrel⟩ := host_corr (p := p) (N := N) hcall hva
    ({ s with frame := (F₁.insert n lva).erase n } : St)
  obtain ⟨hlow, hhigh⟩ := post_low_high (va := lva) hf hpa (le_refl n)
  exact ⟨lr, (F₁.insert n lva).erase n, hrel, rfl, (seqOcc_app _ a).returns hra hrf,
    post_one hf hpa (fun k => by
      rw [(seqOcc_app _ a).cnt_eq hra hrf k, cnt_of (occ_prim _ (k + 0)) rfl, Nat.add_zero]) hlow hhigh,
    sim_letv (hty n (by omega)) hsa (sim_host insert_get_self hrun)⟩

/-! #### Binders -/

/-- **A binder's value pushed** at the fresh variable `x`: the slot `0` holds it, at budget `1`. -/
theorem FrameOK.push {p : Prog} {N : Nat} {γ : List Val} {ρ : Nat → Nat} {m m' : Nat}
    {bud : Nat → Nat} {F : Std.HashMap Var LV} (h : FrameOK p N γ ρ m bud F) {x : Nat}
    (hxF : ∀ (y : Nat) v, F[y]? = some v → y < x) (hx : x < m') (hm : m ≤ m') {v : Val} {lv : LV}
    (hv : VRel p N v lv) :
    FrameOK p N (v :: γ) (cons1 x ρ) m' (fun j => if j = 0 then 1 else bud (j - 1))
      (F.insert x lv) := by
  refine ⟨fun y w hy => ?_, fun j => ?_, fun j hj => ?_, fun j j' hj hj' he => ?_⟩
  · by_cases hxy : x = y
    · subst hxy; exact hx
    · rw [insert_get_ne hxy] at hy; exact lt_of_lt_of_le (h.fresh y w hy) hm
  · split
    · exact le_refl 1
    · exact h.le _
  · cases j with
    | zero => exact ⟨by simp, lv, by simp [cons1], by simpa using hv⟩
    | succ j =>
        simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj
        obtain ⟨hj', w, hw, hr⟩ := h.live j hj
        have hne : x ≠ ρ j := by have := hxF _ _ hw; omega
        refine ⟨by simpa using hj', w, ?_, by simpa using hr⟩
        simp only [cons1, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        rw [insert_get_ne hne]; exact hw
  · cases j with
    | zero =>
        cases j' with
        | zero => rfl
        | succ j' =>
            simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj'
            simp only [cons1, if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at he
            obtain ⟨_, w, hw, -⟩ := h.live j' hj'
            have := hxF _ _ hw; omega
    | succ j =>
        cases j' with
        | zero =>
            simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj
            simp only [cons1, if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at he
            obtain ⟨_, w, hw, -⟩ := h.live j hj
            have := hxF _ _ hw; omega
        | succ j' =>
            simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hj hj'
            simp only [cons1, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at he
            rw [h.inj j j' hj hj' he]

theorem cons2_eq (y x : Nat) (ρ : Nat → Nat) : cons2 y x ρ = cons1 y (cons1 x ρ) := by
  funext i
  simp only [cons2, cons1]
  split
  · rfl
  · split
    · rename_i h₁ h₂; simp [h₂]
    · rename_i h₁ h₂
      rw [if_neg (by omega)]
      congr 1

theorem fwd_letpair {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {a b : Expr} {ta tb : Tm}
    (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (ha : Pr p N ρ (n + 3) a ta n₁) (hb : Pr p N (cons2 (n + 2) (n + 1) ρ) n₁ b tb n₂)
    (iha : FwdAt p N sz ρ (n + 3) a ta n₁)
    (ihb : FwdAt p N sz (cons2 (n + 2) (n + 1) ρ) n₁ b tb n₂) :
    FwdAt p N sz ρ n (.letpair a b) (.letv n ta (.letpair (n + 1) (n + 2) n tb)) n₂ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le ha; have hn₂ := pr_le hb
  simp only [Expr.psub] at hbig
  obtain ⟨i, j, μ₁, v₁, v₂, hi, hj, hba, hbb⟩ := big_letpair_inv hbig
  rw [psub_body2] at hbb
  rw [explicitB, isCF_letpair, Bool.false_or] at hx
  simp only [Bool.and_eq_true] at hx
  obtain ⟨⟨⟨hxa, hxb⟩, h0⟩, h1⟩ := hx
  simp only [coreB, Bool.and_eq_true] at hcore
  obtain ⟨va, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s _ _ _ i (by omega) hba
    hxa hcore.1 ((seqOcc_letpair a b).bud_left hbud) (hf.mono (by omega)) LTy.unit
  obtain ⟨lx, ly, rfl, hx₁, hx₂⟩ := vrel_pair_inv hva
  have hbr := (seqOcc_letpair a b).bud_right hbud hra
  let bud' : Nat → Nat := fun k => bud k - cnt a k
  have hF₀ : FrameOK p N γ ρ (n + 1) bud' ((F₁.insert n (.pair lx ly)).erase n) :=
    (hf.after hpa (le_refl n) (by omega)).erase (fun k hk he => by
      have hlt := hf.lt (k := k) (by have := hf.le k; omega); omega)
  have hkeys : ∀ (z : Nat) v, ((F₁.insert n (.pair lx ly)).erase n)[z]? = some v → z < n := by
    intro z v hz
    by_cases hzn : n = z
    · subst hzn; rw [erase_get_self] at hz; cases hz
    · rw [erase_get_ne hzn, insert_get_ne hzn] at hz
      by_contra hc
      rw [hpa.high hf (by omega)] at hz; cases hz
  have hF₁ := hF₀.push (fun z v hz => Nat.lt_succ_of_lt (hkeys z v hz)) (x := n + 1) (by omega)
    (by omega) hx₁ (m' := n + 2)
  have hF₂ := hF₁.push (x := n + 2) (fun z v hz => by
      by_cases hzx : n + 1 = z
      · omega
      · rw [insert_get_ne hzx] at hz; have := hkeys z v hz; omega) (by omega) (by omega) hx₂
      (m' := n₁)
  rw [← cons2_eq] at hF₂
  let bud₂ : Nat → Nat := fun j => if j = 0 then 1 else
    (fun j => if j = 0 then 1 else bud' (j - 1)) (j - 1)
  have hbud₂ : BudOK b bud₂ := by
    intro jj
    match jj with
    | 0 => obtain ⟨u, hu, hb⟩ := once_bnd h0; exact ⟨u, hu, by simpa [bud₂, Bnd] using hb⟩
    | 1 => obtain ⟨u, hu, hb⟩ := once_bnd h1; exact ⟨u, hu, by simpa [bud₂, Bnd] using hb⟩
    | k + 2 =>
        obtain ⟨u, hu, hb⟩ := hbr k
        exact ⟨u, hu, by simpa [bud₂, bud', Bnd] using hb⟩
  obtain ⟨vw, F₂, hvw, rfl, hrb, hpb, hsb⟩ := ihb (by omega) (v₂ :: v₁ :: γ) bud₂
    ({ s with frame := ((((F₁.insert n (.pair lx ly)).erase n).insert (n + 1) lx).insert
      (n + 2) ly) } : St) _ _ _ j (by omega) hbb hxb hcore.2 hbud₂ hF₂ rt
  have hrb' : ∀ k, ∃ u r, occ b (k + 2) = some u ∧ u.ret = some r := fun k => hrb (k + 2)
  have hc0 : cnt b 0 = 1 := by
    obtain ⟨u, r, hu, hr⟩ := hrb 0; rw [cnt_of hu hr]; exact once_ret h0 hu hr
  have hc1 : cnt b 1 = 1 := by
    obtain ⟨u, r, hu, hr⟩ := hrb 1; rw [cnt_of hu hr]; exact once_ret h1 hu hr
  have hρ2 : ∀ k, cons2 (n + 2) (n + 1) ρ (k + 2) = ρ k := fun k => by simp [cons2]
  refine ⟨vw, F₂, hvw, rfl, (seqOcc_letpair a b).returns hra hrb', ?_, ?_⟩
  · refine post_two (cntB := fun k => cnt b (k + 2)) hf hpa
      (G := (((F₁.insert n (.pair lx ly)).erase n).insert (n + 1) lx).insert (n + 2) ly) (F₂ := F₂)
      (fun z hz => by
        rw [insert_get_ne (by omega), insert_get_ne (by omega), erase_get_ne (by omega),
          insert_get_ne (by omega)])
      (fun k h1' h2' => by
        have := hpb.1 (k + 2) (by simpa [bud₂, bud'] using h1') h2'; rwa [hρ2] at this)
      (fun x hxn h => hpb.2 x (fun jj hj hc he => by
        rcases jj with _ | _ | k
        · simp [cons2] at he; omega
        · simp [cons2] at he; omega
        · rw [hρ2] at he; exact h k (by simpa [bud₂, bud'] using hj) hc he))
      (fun k => (seqOcc_letpair a b).cnt_eq hra hrb' k) (cnt_le_bud hbud) (fun z _ => rfl)
      (fun z hz => ?_)
    by_cases hz2 : z = n + 2
    · subst hz2; have := hpb.1 0 (by simp [bud₂]) hc0; simpa [cons2] using this
    by_cases hz1 : z = n + 1
    · subst hz1; have := hpb.1 1 (by simp [bud₂]) hc1; simpa [cons2] using this
    rw [hpb.2 z (fun jj hj hc he => by
      rcases jj with _ | _ | k
      · simp [cons2] at he; omega
      · simp [cons2] at he; omega
      · rw [hρ2] at he
        have hlt := hf.lt (k := k) (by simp [bud₂, bud'] at hj; have := hf.le k; omega)
        omega)]
    rw [insert_get_ne (Ne.symm hz2), insert_get_ne (Ne.symm hz1)]
    by_cases hzn : n = z
    · subst hzn; exact erase_get_self
    · rw [erase_get_ne hzn, insert_get_ne hzn]; exact hpa.high hf hz
  · have hq : (F₁.insert n (.pair lx ly))[n]? = some (.pair lx ly) := insert_get_self
    exact sim_letv (hty n (by omega)) hsa (sim_letpair hq hsb)

/-! #### Cases -/

theorem occ_case_parts {s a b : Expr} (hab : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE)) {k : Nat}
    {u : Uses} (h : occ (.case s a b) k = some u) :
    ∃ us ua ub j, occ s k = some us ∧ occ a (k + 1) = some ua ∧ occ b (k + 1) = some ub ∧
      Uses.join ua ub = some j ∧ u = us.andThen j := by
  simp only [occ, if_neg hab] at h
  cases hs : occ s k <;> cases ha : occ a (k + 1) <;> cases hb : occ b (k + 1) <;>
    simp_all [Option.bind_eq_bind]
  rename_i us ua ub
  cases hj : Uses.join ua ub <;> simp_all

theorem occ_case_eq {s a b : Expr} (hab : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE)) {k : Nat}
    {us ua ub j : Uses} (hs : occ s k = some us) (ha : occ a (k + 1) = some ua)
    (hb : occ b (k + 1) = some ub) (hj : Uses.join ua ub = some j) :
    occ (.case s a b) k = some (us.andThen j) := by
  simp [occ, hab, hs, ha, hb, hj]

/-- What a `case` uses when one of its arms (`ua`) runs and returns. -/
theorem case_facts {s a b : Expr} (hab : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE)) {bud : Nat → Nat}
    (hbud : BudOK (.case s a b) bud) (hrs : Returns s) (left : Bool)
    (hret : ∀ k, ∃ u r, occ (if left then a else b) (k + 1) = some u ∧ u.ret = some r) :
    (∀ k, ∃ u, occ (if left then a else b) (k + 1) = some u ∧ Bnd u (bud k - cnt s k)) ∧
    Returns (.case s a b) ∧
    ∀ k, cnt (.case s a b) k = cnt s k + cnt (if left then a else b) (k + 1) := by
  have hparts : ∀ k, ∃ us ua ub j, occ s k = some us ∧ occ a (k + 1) = some ua ∧
      occ b (k + 1) = some ub ∧ Uses.join ua ub = some j ∧ occ (.case s a b) k = some (us.andThen j) :=
    fun k => by
      obtain ⟨u, hu, -⟩ := hbud k
      obtain ⟨us, ua, ub, j, h1, h2, h3, h4, rfl⟩ := occ_case_parts hab hu
      exact ⟨us, ua, ub, j, h1, h2, h3, h4, hu⟩
  have hjret : ∀ k, ∃ us ua ub j r, occ s k = some us ∧ occ a (k + 1) = some ua ∧
      occ b (k + 1) = some ub ∧ Uses.join ua ub = some j ∧ j.ret = some r ∧
      occ (if left then a else b) (k + 1) = some (if left then ua else ub) ∧
      (if left then ua else ub).ret = some r ∧ occ (.case s a b) k = some (us.andThen j) := by
    intro k
    obtain ⟨us, ua, ub, j, h1, h2, h3, h4, h5⟩ := hparts k
    obtain ⟨u', r, hu', hr⟩ := hret k
    cases left
    · simp only [Bool.false_eq_true, if_false] at hu' ⊢
      rw [h3] at hu'; cases hu'
      exact ⟨us, ua, ub, j, r, h1, h2, h3, h4, join_ret_right h4 hr, h3, hr, h5⟩
    · simp only [if_true] at hu' ⊢
      rw [h2] at hu'; cases hu'
      exact ⟨us, ua, ub, j, r, h1, h2, h3, h4, join_ret_left h4 hr, h2, hr, h5⟩
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_⟩
  · obtain ⟨u, hu, hb⟩ := hbud k
    obtain ⟨us, ua, ub, j, r, h1, h2, h3, h4, -, h6, -, h8⟩ := hjret k
    rw [h8] at hu; cases hu
    obtain ⟨us', rs, h1', hrs'⟩ := hrs k
    rw [h1] at h1'; cases h1'
    have hb' := bnd_andThen_right hb hrs'
    rw [cnt_of h1 hrs']
    have := join_bnd h4 hb'
    cases left
    · exact ⟨ub, h6, this.2⟩
    · exact ⟨ua, h6, this.1⟩
  · obtain ⟨us, ua, ub, j, r, h1, -, -, -, h5, -, -, h8⟩ := hjret k
    obtain ⟨us', rs, h1', hrs'⟩ := hrs k
    rw [h1] at h1'; cases h1'
    exact ⟨_, _, h8, ret_andThen hrs' h5⟩
  · obtain ⟨us, ua, ub, j, r, h1, -, -, -, h5, h6, h7, h8⟩ := hjret k
    obtain ⟨us', rs, h1', hrs'⟩ := hrs k
    rw [h1] at h1'; cases h1'
    rw [cnt_of h8 (ret_andThen hrs' h5), cnt_of h1 hrs', cnt_of h6 h7]

theorem case_bud {s a b : Expr} (hab : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE)) {bud : Nat → Nat}
    (hbud : BudOK (.case s a b) bud) (hrs : Returns s) (k : Nat) :
    (∃ u, occ a (k + 1) = some u ∧ Bnd u (bud k - cnt s k)) ∧
      (∃ u, occ b (k + 1) = some u ∧ Bnd u (bud k - cnt s k)) := by
  obtain ⟨u, hu, hb⟩ := hbud k
  obtain ⟨us, ua, ub, j, h1, h2, h3, h4, rfl⟩ := occ_case_parts hab hu
  obtain ⟨us', rs, h1', hrs'⟩ := hrs k
  rw [h1] at h1'; cases h1'
  have hb' := bnd_andThen_right hb hrs'
  rw [cnt_of h1 hrs']
  have := join_bnd h4 hb'
  exact ⟨⟨ua, h2, this.1⟩, ⟨ub, h3, this.2⟩⟩

theorem case_bud_s {s a b : Expr} (hab : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE)) {bud : Nat → Nat}
    (hbud : BudOK (.case s a b) bud) : BudOK s bud := by
  intro k
  obtain ⟨u, hu, hb⟩ := hbud k
  obtain ⟨us, ua, ub, j, h1, h2, h3, h4, rfl⟩ := occ_case_parts hab hu
  exact ⟨us, h1, bnd_andThen_left hb (ne_join (occ_nonempty _ _ _ h2) (occ_nonempty _ _ _ h3) h4)⟩

theorem fwd_case {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ n₃ : Nat} {v a b : Expr}
    {tv ta tb : Tm} (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit)
    (hab : ¬ (a = BoLo.stuckE ∧ b = BoLo.stuckE))
    (hv : Pr p N ρ (n + 3) v tv n₁) (ha : Pr p N (cons1 (n + 1) ρ) n₁ a ta n₂)
    (hb : Pr p N (cons1 (n + 2) ρ) n₂ b tb n₃)
    (ihv : FwdAt p N sz ρ (n + 3) v tv n₁) (iha : FwdAt p N sz (cons1 (n + 1) ρ) n₁ a ta n₂)
    (ihb : FwdAt p N sz (cons1 (n + 2) ρ) n₂ b tb n₃) :
    FwdAt p N sz ρ n (.case v a b) (.letv n tv (.case n (n + 1) ta (n + 2) tb)) n₃ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hf rt
  have hn₁ := pr_le hv; have hn₂ := pr_le ha; have hn₃ := pr_le hb
  simp only [Expr.psub] at hbig
  rw [explicitB, isCF_case, Bool.false_or, if_neg hab] at hx
  simp only [Bool.and_eq_true] at hx
  obtain ⟨⟨⟨⟨hxv, hxa⟩, hxb⟩, h0a⟩, h0b⟩ := hx
  simp only [coreB, Bool.and_eq_true] at hcore
  have hρ1 : ∀ (x : Nat) k, cons1 x ρ (k + 1) = ρ k := fun x k => by simp [cons1]
  rcases big_case_inv hbig with ⟨i, j, μ₁, u, hi, hj, hbv, hba⟩ | ⟨i, j, μ₁, u, hi, hj, hbv, hba⟩
  · rw [psub_arm] at hba
    obtain ⟨vs, F₁, hvs, rfl, hrs, hps, hss⟩ := ihv (by omega) γ bud s _ _ _ i (by omega) hbv hxv
      hcore.1.1 (case_bud_s hab hbud) (hf.mono (by omega)) LTy.unit
    obtain ⟨lv, rfl, hlv⟩ := vrel_inj₁_inv hvs
    let bud' : Nat → Nat := fun k => bud k - cnt v k
    have hF₀ : FrameOK p N γ ρ (n + 1) bud' ((F₁.insert n (.inj false lv)).erase n) :=
      (hf.after hps (le_refl n) (by omega)).erase (fun k hk he => by
        have hlt := hf.lt (k := k) (by have := hf.le k; omega); omega)
    have hkeys : ∀ (z : Nat) w, ((F₁.insert n (.inj false lv)).erase n)[z]? = some w → z < n + 1 := by
      intro z w hz
      by_cases hzn : n = z
      · subst hzn; rw [erase_get_self] at hz; cases hz
      · rw [erase_get_ne hzn, insert_get_ne hzn] at hz
        by_contra hc
        rw [hps.high hf (by omega)] at hz; cases hz
    have hF₁ := hF₀.push hkeys (x := n + 1) (by omega) (by omega) hlv (m' := n₁)
    have hbud₁ : BudOK a (fun jj => if jj = 0 then 1 else bud' (jj - 1)) := by
      intro jj
      rcases jj with _ | k
      · obtain ⟨u, hu, hb⟩ := once_bnd h0a; exact ⟨u, hu, by simpa [Bnd] using hb⟩
      · obtain ⟨u, hu, hb⟩ := (case_bud hab hbud hrs k).1
        exact ⟨u, hu, by simpa [bud', Bnd] using hb⟩
    obtain ⟨vw, F₂, hvw, rfl, hra, hpa, hsa⟩ := iha (by omega) (u :: γ) _
      ({ s with frame := ((F₁.insert n (.inj false lv)).erase n).insert (n + 1) lv } : St) _ _ _ j
      (by omega) hba hxa hcore.1.2 hbud₁ hF₁ rt
    obtain ⟨hbs, hret, hcnt⟩ := case_facts hab hbud hrs true (fun k => by simpa using hra (k + 1))
    have hc0 : cnt a 0 = 1 := by
      obtain ⟨u, r, hu, hr⟩ := hra 0; rw [cnt_of hu hr]; exact once_ret h0a hu hr
    refine ⟨vw, F₂, hvw, rfl, hret, ?_, ?_⟩
    · refine post_two (cntB := fun k => cnt a (k + 1)) hf hps
        (G := ((F₁.insert n (.inj false lv)).erase n).insert (n + 1) lv) (F₂ := F₂)
        (fun z hz => by rw [insert_get_ne (by omega), erase_get_ne (by omega), insert_get_ne (by omega)])
        (fun k h1' h2' => by
          have := hpa.1 (k + 1) (by simpa using h1') h2'; rwa [hρ1] at this)
        (fun x hxn h => hpa.2 x (fun jj hj hc he => by
          rcases jj with _ | k
          · simp [cons1] at he; omega
          · rw [hρ1] at he; exact h k (by simpa using hj) hc he))
        (fun k => by simpa using hcnt k) (cnt_le_bud hbud) (fun z _ => rfl) (fun z hz => ?_)
      by_cases hz1 : z = n + 1
      · subst hz1; have := hpa.1 0 (by simp) hc0; simpa [cons1] using this
      rw [hpa.2 z (fun jj hj hc he => by
        rcases jj with _ | k
        · simp [cons1] at he; omega
        · rw [hρ1] at he
          have hlt := hf.lt (k := k) (by simp [bud'] at hj; have := hf.le k; omega)
          omega)]
      rw [insert_get_ne (Ne.symm hz1)]
      by_cases hzn : n = z
      · subst hzn; exact erase_get_self
      · rw [erase_get_ne hzn, insert_get_ne hzn]; exact hps.high hf hz
    · have hq : (F₁.insert n (.inj false lv))[n]? = some (.inj false lv) := insert_get_self
      exact sim_letv (hty n (by omega)) hss (sim_case_l hq hsa)
  · rw [psub_arm] at hba
    obtain ⟨vs, F₁, hvs, rfl, hrs, hps, hss⟩ := ihv (by omega) γ bud s _ _ _ i (by omega) hbv hxv
      hcore.1.1 (case_bud_s hab hbud) (hf.mono (by omega)) LTy.unit
    obtain ⟨lv, rfl, hlv⟩ := vrel_inj₂_inv hvs
    let bud' : Nat → Nat := fun k => bud k - cnt v k
    have hF₀ : FrameOK p N γ ρ (n + 1) bud' ((F₁.insert n (.inj true lv)).erase n) :=
      (hf.after hps (le_refl n) (by omega)).erase (fun k hk he => by
        have hlt := hf.lt (k := k) (by have := hf.le k; omega); omega)
    have hkeys : ∀ (z : Nat) w, ((F₁.insert n (.inj true lv)).erase n)[z]? = some w → z < n + 2 := by
      intro z w hz
      by_cases hzn : n = z
      · subst hzn; rw [erase_get_self] at hz; cases hz
      · rw [erase_get_ne hzn, insert_get_ne hzn] at hz
        by_contra hc
        rw [hps.high hf (by omega)] at hz; cases hz
    have hF₁ := (hF₀.mono (m := n + 2) (by omega)).push hkeys (x := n + 2) (by omega) (by omega) hlv
      (m' := n₂)
    have hbud₁ : BudOK b (fun jj => if jj = 0 then 1 else bud' (jj - 1)) := by
      intro jj
      rcases jj with _ | k
      · obtain ⟨u, hu, hb⟩ := once_bnd h0b; exact ⟨u, hu, by simpa [Bnd] using hb⟩
      · obtain ⟨u, hu, hb⟩ := (case_bud hab hbud hrs k).2
        exact ⟨u, hu, by simpa [bud', Bnd] using hb⟩
    obtain ⟨vw, F₂, hvw, rfl, hrb, hpb, hsb⟩ := ihb (by omega) (u :: γ) _
      ({ s with frame := ((F₁.insert n (.inj true lv)).erase n).insert (n + 2) lv } : St) _ _ _ j
      (by omega) hba hxb hcore.2 hbud₁ hF₁ rt
    obtain ⟨hbs, hret, hcnt⟩ := case_facts hab hbud hrs false (fun k => by simpa using hrb (k + 1))
    have hc0 : cnt b 0 = 1 := by
      obtain ⟨u, r, hu, hr⟩ := hrb 0; rw [cnt_of hu hr]; exact once_ret h0b hu hr
    refine ⟨vw, F₂, hvw, rfl, hret, ?_, ?_⟩
    · refine post_two (cntB := fun k => cnt b (k + 1)) hf hps
        (G := ((F₁.insert n (.inj true lv)).erase n).insert (n + 2) lv) (F₂ := F₂)
        (fun z hz => by rw [insert_get_ne (by omega), erase_get_ne (by omega), insert_get_ne (by omega)])
        (fun k h1' h2' => by
          have := hpb.1 (k + 1) (by simpa using h1') h2'; rwa [hρ1] at this)
        (fun x hxn h => hpb.2 x (fun jj hj hc he => by
          rcases jj with _ | k
          · simp [cons1] at he; omega
          · rw [hρ1] at he; exact h k (by simpa using hj) hc he))
        (fun k => by simpa using hcnt k) (cnt_le_bud hbud) (fun z _ => rfl) (fun z hz => ?_)
      by_cases hz2 : z = n + 2
      · subst hz2; have := hpb.1 0 (by simp) hc0; simpa [cons1] using this
      rw [hpb.2 z (fun jj hj hc he => by
        rcases jj with _ | k
        · simp [cons1] at he; omega
        · rw [hρ1] at he
          have hlt := hf.lt (k := k) (by simp [bud'] at hj; have := hf.le k; omega)
          omega)]
      rw [insert_get_ne (Ne.symm hz2)]
      by_cases hzn : n = z
      · subst hzn; exact erase_get_self
      · rw [erase_get_ne hzn, insert_get_ne hzn]; exact hps.high hf hz
    · have hq : (F₁.insert n (.inj true lv))[n]? = some (.inj true lv) := insert_get_self
      exact sim_letv (hty n (by omega)) hss (sim_case_r hq hsb)

/-! #### Calls -/

theorem getElem_idxOf_mem {l : List Nat} {k : Nat} (h : k ∈ l) : l[l.idxOf k]? = some k := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h)]
  simp [List.getElem_idxOf]

theorem capOnce_of_mem {b : Expr} (h : capOnceB b = true) {k : Nat} (hk : k ∈ capt b) :
    once (occ b (k + 1)) = true := by
  have hm := mem_capt.mp hk
  have hl := mentions_lt hm
  have := List.all_eq_true.mp h k (List.mem_range.mpr (by omega))
  simpa [hm] using this

/-- The frame of a closure's call: its captured values, then its argument. -/
abbrev callFrame (env : List LV) (lv : LV) : Std.HashMap Var LV :=
  ((List.range (env.length + 1)).zip (env ++ [lv])).foldl (fun m x => m.insert x.1 x.2) ∅

theorem callFrame_get (env : List LV) (lv : LV) (x : Nat) :
    (callFrame env lv)[x]? = (env ++ [lv])[x]? := by
  have := zipFrame_get (env ++ [lv]) x
  simpa using this

/-- **A call of a closure of a `λ`**: from the closure's frame the body runs to the value
corresponding to the call's, and the frame it returns with is empty. -/
theorem call_lam {p : Prog} {N : Nat} {c m : Nat} {b : Expr} {tb : Tm} {γc : List Val}
    {env : List LV} {va w : Val} {lva : LV} {μ μ' : Heap} {k : Nat} (s : St) (hm : m ≤ N)
    (hc : CodeAt p c (capt b).length tb)
    (hx : explicitB isCF b = true) (h0 : once (occ b 0) = true) (hcap : capOnceB b = true)
    (hcore : coreB b = true) (hlen : env.length = (capt b).length)
    (hcapl : ∀ k, k ∈ capt b → k < γc.length)
    (hrel : ∀ i (hi : i < env.length) (k : Nat) (hk : k < γc.length), (capt b)[i]? = some k →
      VRel p N γc[k] env[i])
    (hva : VRel p N va lva)
    (hbig : BigN (ℍ := Backend2.lirHost) k μ (Expr.psub 0 (va :: γc) b) μ' w)
    (hfw : FwdAt p N k (lamEnv b) ((capt b).length + 1) b tb m) :
    ∃ v, VRel p N w v ∧ μ' = μ ∧
      Sim (fun f => Backend2.callClos p f (.clos c env) (some lva) 0) s (.ok (v, s)) := by
  obtain ⟨hcode, fn, hfn, hpar, hbody⟩ := hc
  have hK : (capt b).length = (capt b).length := rfl
  let bud : Nat → Nat := fun jj => if jj = 0 then 1 else if jj - 1 ∈ capt b then 1 else 0
  have hnd := capt_nodup b
  have hle : ∀ jj, bud jj ≤ 1 := fun jj => by simp only [bud]; split <;> (try split) <;> omega
  have hlam0 : lamEnv b 0 = (capt b).length := by simp [lamEnv]
  have hlamS : ∀ k, lamEnv b (k + 1) = (capt b).idxOf k := fun k => by simp [lamEnv]
  have hfr : FrameOK p N (va :: γc) (lamEnv b) ((capt b).length + 1) bud (callFrame env lva) := by
    refine ⟨fun x v hx => ?_, hle, fun jj hj => ?_, fun jj jj' hj hj' he => ?_⟩
    · rw [callFrame_get] at hx
      have := (List.getElem?_eq_some_iff.mp hx).1
      simpa [hlen] using this
    · rcases jj with _ | k
      · refine ⟨by simp, lva, ?_, by simpa using hva⟩
        rw [hlam0, callFrame_get, List.getElem?_append_right (by omega)]
        simp [hlen]
      · have hk : k ∈ capt b := by
          by_contra hn; simp [bud, hn] at hj
        have hkl := hcapl k hk
        have hi := List.idxOf_lt_length_of_mem hk
        refine ⟨by simpa using hkl, env[(capt b).idxOf k]'(by omega), ?_, ?_⟩
        · rw [hlamS, callFrame_get, List.getElem?_append_left (by omega),
            List.getElem?_eq_getElem (by omega)]
        · simpa using hrel _ (by omega) k hkl (getElem_idxOf_mem hk)
    · rcases jj with _ | k <;> rcases jj' with _ | k'
      · rfl
      · have hk' : k' ∈ capt b := by by_contra hn; simp [bud, hn] at hj'
        rw [hlam0, hlamS] at he
        have := List.idxOf_lt_length_of_mem hk'; omega
      · have hk : k ∈ capt b := by by_contra hn; simp [bud, hn] at hj
        rw [hlam0, hlamS] at he
        have := List.idxOf_lt_length_of_mem hk; omega
      · have hk : k ∈ capt b := by by_contra hn; simp [bud, hn] at hj
        have hk' : k' ∈ capt b := by by_contra hn; simp [bud, hn] at hj'
        rw [hlamS, hlamS] at he
        have e1 := getElem_idxOf_mem hk
        have e2 := getElem_idxOf_mem hk'
        rw [he] at e1; rw [e1] at e2; cases e2; rfl
  have hbud : BudOK b bud := by
    intro jj
    rcases jj with _ | k
    · obtain ⟨u, hu, hb⟩ := once_bnd h0; exact ⟨u, hu, by simpa [bud, Bnd] using hb⟩
    · by_cases hk : k ∈ capt b
      · obtain ⟨u, hu, hb⟩ := once_bnd (capOnce_of_mem hcap hk)
        exact ⟨u, hu, by simpa [bud, hk, Bnd] using hb⟩
      · obtain ⟨u, hu, hb⟩ := occ_unmentioned b (k + 1) (by
          cases h : mentions b (k + 1)
          · rfl
          · exact absurd (mem_capt.mpr h) hk)
        exact ⟨u, hu, by simpa [bud, hk, Bnd] using hb⟩
  have hs₀ : ({ s with frame := (fn.params.zip (env ++ [lva])).foldl (fun m x => m.insert x.1 x.2) ∅ } : St).frame = callFrame env lva := by
    show _ = ((List.range (env.length + 1)).zip (env ++ [lva])).foldl _ _
    rw [hpar, hlen]
  obtain ⟨v, Fb, hv, rfl, hret, hpost, hsim⟩ := hfw hm (va :: γc) bud
    ({ s with frame := (fn.params.zip (env ++ [lva])).foldl (fun m x => m.insert x.1 x.2) ∅ } : St)
    μ μ' w k (le_refl k) hbig hx hcore hbud (hs₀ ▸ hfr) fn.ret
  have hempty : ∀ x : Nat, Fb[x]? = none := by
    intro x
    by_cases hxK : x = (capt b).length
    · subst hxK
      obtain ⟨u, r, hu, hr⟩ := hret 0
      have := hpost.1 0 (by simp [bud]) (by rw [cnt_of hu hr]; exact once_ret h0 hu hr)
      rwa [hlam0] at this
    by_cases hxl : x < (capt b).length
    · have hk : (capt b)[x] ∈ capt b := List.getElem_mem hxl
      obtain ⟨u, r, hu, hr⟩ := hret ((capt b)[x] + 1)
      have := hpost.1 ((capt b)[x] + 1) (by simp [bud, hk])
        (by rw [cnt_of hu hr]; exact once_ret (capOnce_of_mem hcap hk) hu hr)
      rwa [hlamS, List.Nodup.idxOf_getElem hnd x hxl] at this
    · rw [hpost.2 x (fun jj hj _ he => by
        rcases jj with _ | k
        · rw [hlam0] at he; omega
        · rw [hlamS] at he; have := List.idxOf_le_length (l := capt b) (a := k); omega)]
      rw [hs₀, callFrame_get, List.getElem?_eq_none (by simp [hlen]; omega)]
  refine ⟨v, hv, rfl, ?_⟩
  have hcall := sim_callFn (p := p) (c := c) (fn := fn) (args := env ++ [lva]) (s := s) hfn
    (by simp [hpar, hlen]) (by rw [hbody]; exact hsim) (isEmpty_of_none hempty)
  exact sim_callClos hcode hcall

/-- **A call of a closure of a code with no environment**, whose body returns with its frame
empty. -/
theorem call_simple {p : Prog} {c : Nat} {body : Tm} {lva r : LV} (s : St)
    (hc : CodeAt p c 0 body)
    (hb : ∀ rt : LTy, ∃ Fb : Std.HashMap Var LV, (∀ x : Nat, Fb[x]? = none) ∧
      Sim (fun f => Backend2.eval p f rt body)
        ({ s with frame := (∅ : Std.HashMap Var LV).insert 0 lva } : St)
        (.ok (r, ({ s with frame := Fb } : St)))) :
    Sim (fun f => Backend2.callClos p f (.clos c []) (some lva) 0) s (.ok (r, s)) := by
  obtain ⟨hcode, fn, hfn, hpar, hbody⟩ := hc
  obtain ⟨Fb, hFb, hsim⟩ := hb fn.ret
  have hfr : (fn.params.zip ([] ++ [lva])).foldl (fun m x => m.insert x.1 x.2) (∅ : Std.HashMap Var LV) =
      (∅ : Std.HashMap Var LV).insert 0 lva := by rw [hpar]; rfl
  have hcall := sim_callFn (s := s) (args := [] ++ [lva]) (s' := ({ s with frame := Fb } : St))
    hfn (by simp [hpar]) (by rw [hbody, hfr]; exact hsim) (isEmpty_of_none hFb)
  exact sim_callClos hcode hcall

theorem single_get (lva : LV) (x : Nat) :
    ((∅ : Std.HashMap Var LV).insert 0 lva)[x]? = if x = 0 then some lva else none := by
  rw [Std.HashMap.getElem?_insert]
  by_cases h : x = 0
  · subst h; simp
  · simp [h, Ne.symm h]

theorem body_copy {p : Prog} {N : Nat} (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit) (hN : 2 ≤ N)
    (lva : LV) (s : St) (rt : LTy) :
    ∃ Fb : Std.HashMap Var LV, (∀ x : Nat, Fb[x]? = none) ∧
      Sim (fun f => Backend2.eval p f rt copyFn)
        ({ s with frame := (∅ : Std.HashMap Var LV).insert 0 lva } : St)
        (.ok (.pair lva lva, ({ s with frame := Fb } : St))) := by
  let F₀ : Std.HashMap Var LV := (∅ : Std.HashMap Var LV).insert 0 lva
  have g0 : F₀[(0 : Nat)]? = some lva := by rw [single_get]; rfl
  refine ⟨((F₀.insert 1 lva).erase 0).erase 1, fun x => ?_, ?_⟩
  · by_cases h1 : x = 1
    · subst h1; exact erase_get_self
    · rw [erase_get_ne (Ne.symm h1)]
      by_cases h0 : x = 0
      · subst h0; exact erase_get_self
      · rw [erase_get_ne (Ne.symm h0), insert_get_ne (Ne.symm h1), single_get, if_neg h0]
  · have h1 : (F₀.insert 1 lva)[(0 : Nat)]? = some lva := by rw [insert_get_ne (by omega)]; exact g0
    have h2 : ((F₀.insert 1 lva).erase 0)[(1 : Nat)]? = some lva := by
      rw [erase_get_ne (by omega)]; exact insert_get_self
    exact sim_copy (hty 0 (by omega)) g0 (sim_pair h1 h2)

theorem body_forget {p : Prog} {N : Nat} (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit) (hN : 2 ≤ N)
    (lva : LV) (s : St) (rt : LTy) :
    ∃ Fb : Std.HashMap Var LV, (∀ x : Nat, Fb[x]? = none) ∧
      Sim (fun f => Backend2.eval p f rt forgetFn)
        ({ s with frame := (∅ : Std.HashMap Var LV).insert 0 lva } : St)
        (.ok (.unit, ({ s with frame := Fb } : St))) := by
  let F₀ : Std.HashMap Var LV := (∅ : Std.HashMap Var LV).insert 0 lva
  have g0 : F₀[(0 : Nat)]? = some lva := by rw [single_get]; rfl
  refine ⟨F₀.erase 0, fun x => ?_, sim_drop (hty 0 (by omega)) g0 sim_unit⟩
  by_cases h0 : x = 0
  · subst h0; exact erase_get_self
  · rw [erase_get_ne (Ne.symm h0), single_get, if_neg h0]

theorem body_host {p : Prog} {lva lr : LV} {op : HostOp} (s : St)
    (hrun : (Backend2.hostOp op lva).run
      ({ s with frame := ((∅ : Std.HashMap Var LV).insert 0 lva).erase 0 } : St) =
      .ok (lr, ({ s with frame := ((∅ : Std.HashMap Var LV).insert 0 lva).erase 0 } : St)))
    (rt : LTy) :
    ∃ Fb : Std.HashMap Var LV, (∀ x : Nat, Fb[x]? = none) ∧
      Sim (fun f => Backend2.eval p f rt (hostFn op))
        ({ s with frame := (∅ : Std.HashMap Var LV).insert 0 lva } : St)
        (.ok (lr, ({ s with frame := Fb } : St))) := by
  let F₀ : Std.HashMap Var LV := (∅ : Std.HashMap Var LV).insert 0 lva
  have g0 : F₀[(0 : Nat)]? = some lva := by rw [single_get]; rfl
  refine ⟨F₀.erase 0, fun x => ?_, sim_host g0 hrun⟩
  by_cases h0 : x = 0
  · subst h0; exact erase_get_self
  · rw [erase_get_ne (Ne.symm h0), single_get, if_neg h0]

theorem host_call {p : Prog} {N : Nat} {op : HostOp} {va r : Val} {lva : LV} {c : Nat}
    (hcl : Backend2.lirHost.call op va = some r) (hva : VRel p N va lva)
    (hc : CodeAt p c 0 (hostFn op)) (s : St) :
    ∃ v, VRel p N r v ∧
      Sim (fun f => Backend2.callClos p f (.clos c []) (some lva) 0) s (.ok (v, s)) := by
  obtain ⟨lr, hrun, hlr⟩ := host_corr (p := p) (N := N) hcl hva
    ({ s with frame := ((∅ : Std.HashMap Var LV).insert 0 lva).erase 0 } : St)
  exact ⟨lr, hlr, call_simple _ hc (body_host _ hrun)⟩

theorem big_app_store {n : Nat} {μ μ' : Heap} {a : Expr} {w : Val}
    (h : BigN (ℍ := Backend2.lirHost) n μ (.app (.prim .store) a) μ' w) : IsVal a := by
  generalize he : Expr.app (.prim .store) a = E at h
  cases h with
  | val => exact (isVal_app_iff.mp (he ▸ w.2)).2
  | app h₁ h₂ h₃ h₄ =>
      simp only [Expr.app.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := big_val_inv h₂ (Val.prim .store) rfl
      exact (not_head_store h₃).elim
  | _ => simp at he

theorem vrel_not_store {p : Prog} {N : Nat} {v : Val} {lv : LV} (h : VRel p N v lv)
    (hs : v.1 = .prim .store) : False := by
  cases h <;> simp_all [Val.unit, Val.prim, Val.pair, Val.inj₁, Val.inj₂, Val.lam]

theorem fwd_app {p : Prog} {N sz : Nat} {ρ : Nat → Nat} {n n₁ n₂ : Nat} {f a : Expr} {ta tf : Tm}
    (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit) (hN2 : 2 ≤ N)
    (hcp : f ≠ copy) (hfg : f ≠ forget) (hh : ∀ op, f ≠ .prim (.host op))
    (ha : Pr p N ρ (n + 2) a ta n₁) (hf : Pr p N ρ n₁ f tf n₂)
    (iha : FwdAt p N sz ρ (n + 2) a ta n₁) (ihf : FwdAt p N sz ρ n₁ f tf n₂)
    (ihout : ∀ sz', sz' < sz → ∀ (ρ' : Nat → Nat) m e t m', Pr p N ρ' m e t m' →
      FwdAt p N sz' ρ' m e t m') :
    FwdAt p N sz ρ n (.app f a) (.letv n ta (.letv (n + 1) tf (.app (n + 1) n))) n₂ := by
  intro hN γ bud s μ μ' w kk hk hbig hx hcore hbud hfr rt
  have hn₁ := pr_le ha; have hn₂ := pr_le hf
  simp only [Expr.psub] at hbig
  rw [explicitB, isCF_app, Bool.false_or, Bool.and_eq_true] at hx
  simp only [coreB, Bool.and_eq_true] at hcore
  -- the function is not `store`: a core term, or a slot's value, which corresponds to the
  -- interpreter's
  have hst : Expr.psub 0 γ f ≠ .prim .store := by
    intro hst
    cases f with
    | var k =>
        by_cases hkl : k < γ.length
        · rw [psub_var_lt hkl] at hst
          have hva' : IsVal (Expr.psub 0 γ a) := by
            rw [psub_var_lt hkl, hst] at hbig; exact big_app_store hbig
          obtain ⟨va, F₁, hva, -, hra, -, -⟩ := iha (by omega) γ bud s μ μ ⟨_, hva'⟩ 0 (by omega)
            (.val μ ⟨_, hva'⟩) hx.2 hcore.2 ((seqOcc_app (.var k) a).bud_left hbud)
            (hfr.mono (by omega)) LTy.unit
          have hbk : bud k = 1 := by
            obtain ⟨u, hu, h1, -⟩ := hbud k
            obtain ⟨ua, ub, hua, hub, rfl⟩ := (seqOcc_app (.var k) a).parts hu
            obtain ⟨ua', r, hua', hr⟩ := hra k
            rw [hua] at hua'; cases hua'
            simp only [Nat.add_zero, occ, if_pos, Option.some.injEq] at hub
            subst hub
            simp [Uses.andThen, hr, Uses.one] at h1
            have := hfr.le k; omega
          obtain ⟨_, lv, -, hrel⟩ := hfr.live k hbk
          exact vrel_not_store hrel hst
        · rw [psub_var_ge (by omega)] at hst; cases hst
    | prim q =>
        simp only [Expr.psub, Expr.prim.injEq] at hst; subst hst; simp [coreB] at hcore
    | _ => simp [Expr.psub] at hst
  obtain ⟨i, j, k, μa, μf, μr, va, vf, r, hi, hj, hk', hba, hbf, hhd, hbr⟩ := big_app_inv hbig hst
  obtain ⟨lva, F₁, hva, rfl, hra, hpa, hsa⟩ := iha (by omega) γ bud s _ _ va i (by omega) hba
    hx.2 hcore.2 ((seqOcc_app f a).bud_left hbud) (hfr.mono (by omega)) LTy.unit
  have hbr' := (seqOcc_app f a).bud_right hbud hra
  obtain ⟨lvf, F₂, hvf, rfl, hrf, hpf, hsf⟩ := ihf (by omega) γ (fun k => bud k - cnt a k)
    ({ s with frame := F₁.insert n lva } : St) _ _ vf j (by omega) hbf hx.1 hcore.1
    (fun k => by simpa [Bnd] using hbr' k) (hfr.after hpa (le_refl n) (by omega)) LTy.unit
  have hrf' : ∀ k, ∃ u r, occ f (k + 0) = some u ∧ u.ret = some r := fun k => by simpa using hrf k
  have hF₂n : F₂[n]? = some lva := by
    rw [hpf.2 n (fun k (hk : bud k - cnt a k = 1) _ he => by
      have hlt := hfr.lt (k := k) (by have := hfr.le k; omega)
      rw [he] at hlt; exact Nat.lt_irrefl _ hlt)]
    exact insert_get_self
  have hne : n ≠ n + 1 := by omega
  -- the call
  have hcall : ∃ v, VRel p N w v ∧ μ' = μf ∧
      Sim (fun f => Backend2.callClos p f lvf (some lva) 0)
        ({ s with frame := ((F₂.insert (n + 1) lvf).erase (n + 1)).erase n } : St)
        (.ok (v, ({ s with frame := ((F₂.insert (n + 1) lvf).erase (n + 1)).erase n } : St))) := by
    cases hvf with
    | lam hcp' hfg' hpr hm hc hxb h0 hcap hcoreb hlen hcapl hrel =>
        obtain ⟨rfl, rfl⟩ := head_lam_inv hhd
        rw [psub_arm] at hbr
        exact call_lam _ hm hc hxb h0 hcap hcoreb hlen hcapl hrel hva hbr
          (ihout k (by omega) _ _ _ _ _ hpr)
    | copy c hc =>
        obtain ⟨rfl, rfl⟩ := head_lam_inv hhd
        obtain ⟨rfl, rfl⟩ := big_val_inv hbr (Val.pair va va) rfl
        exact ⟨_, .pair hva hva, rfl, call_simple _ hc (body_copy hty hN2 lva _)⟩
    | forget c hc =>
        obtain ⟨rfl, rfl⟩ := head_lam_inv hhd
        obtain ⟨rfl, rfl⟩ := big_val_inv hbr Val.unit rfl
        exact ⟨_, .unit, rfl, call_simple _ hc (body_forget hty hN2 lva _)⟩
    | host op c hc =>
        obtain ⟨rfl, r', hcl, rfl⟩ := head_host_inv hhd
        obtain ⟨rfl, rfl⟩ := big_val_inv hbr r' rfl
        obtain ⟨v, hv, hs⟩ := host_call hcl hva hc _
        exact ⟨v, hv, rfl, hs⟩
    | unit => exact (head_nonfun hhd (by simp [Val.unit]) (by simp [Val.unit]) (by simp [Val.unit])).elim
    | lit c => exact (head_lit_false hhd).elim
    | pair => exact (head_nonfun hhd (by simp [Val.pair]) (by simp [Val.pair]) (by simp [Val.pair])).elim
    | inj₁ => exact (head_nonfun hhd (by simp [Val.inj₁]) (by simp [Val.inj₁]) (by simp [Val.inj₁])).elim
    | inj₂ => exact (head_nonfun hhd (by simp [Val.inj₂]) (by simp [Val.inj₂]) (by simp [Val.inj₂])).elim
  obtain ⟨v, hv, rfl, hsc⟩ := hcall
  refine ⟨v, ((F₂.insert (n + 1) lvf).erase (n + 1)).erase n, hv, rfl,
    (seqOcc_app f a).returns hra hrf', ?_, ?_⟩
  · refine post_two (cntB := cnt f) hfr hpa (G := F₁.insert n lva) (F₂ := F₂)
      (fun z hz => insert_get_ne (by omega)) (fun k h1 h2 => hpf.1 k h1 h2)
      (fun x _ h => hpf.2 x h) (fun k => by simpa using (seqOcc_app f a).cnt_eq hra hrf' k)
      (cnt_le_bud hbud) (fun z hz => ?_) (fun z hz => ?_)
    · rw [erase_get_ne (by omega), erase_get_ne (by omega), insert_get_ne (by omega)]
    · by_cases h2 : z = n
      · subst h2; exact erase_get_self
      · rw [erase_get_ne (Ne.symm h2)]
        by_cases h1 : z = n + 1
        · subst h1; exact erase_get_self
        · rw [erase_get_ne (Ne.symm h1), insert_get_ne (Ne.symm h1)]
          rw [hpf.2 z (fun k (hk : bud k - cnt a k = 1) _ he => by
            have hlt := hfr.lt (k := k) (by have := hfr.le k; omega)
            rw [he] at hlt; omega)]
          rw [insert_get_ne (Ne.symm h2)]
          exact hpa.high hfr hz
  · have h1 : (F₂.insert (n + 1) lvf)[n + 1]? = some lvf := insert_get_self
    have h2 : ((F₂.insert (n + 1) lvf).erase (n + 1))[n]? = some lva := by
      rw [erase_get_ne hne.symm, insert_get_ne hne.symm]; exact hF₂n
    exact sim_letv (hty n (by omega)) hsa (sim_letv (hty (n + 1) (by omega)) hsf
      (sim_app h1 h2 hsc))

/-- Forward simulation: every term in the print relation evaluates, under the LIR
interpreter, to a value related to the one its source computes. -/
theorem fwd {p : Prog} {N : Nat} (hty : ∀ x, x < N → p.ty[x]? = some LTy.unit) (hN2 : 2 ≤ N) :
    ∀ sz (ρ : Nat → Nat) m e t m', Pr p N ρ m e t m' → FwdAt p N sz ρ m e t m' := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | _ sz ihsz =>
    intro ρ m e t m' h
    induction h with
    | var ρ n k => exact fwd_var ρ n k
    | unit ρ n => exact fwd_unit ρ n
    | lit ρ n c => exact fwd_lit ρ n c
    | hostV ρ n op c hc => exact fwd_hostV ρ n op c hc
    | copyV ρ n c hc => exact fwd_copyV ρ n c hc
    | forgetV ρ n c hc => exact fwd_forgetV ρ n c hc
    | pair ha hb iha ihb => exact fwd_pair hty ha hb iha ihb
    | inj₁ ha iha => exact fwd_inj false hty ha iha
    | inj₂ ha iha => exact fwd_inj true hty ha iha
    | seq ha hb iha ihb => exact fwd_seq hty ha hb iha ihb
    | letpair ha hb iha ihb => exact fwd_letpair hty ha hb iha ihb
    | case hab hs ha hb ihs iha ihb => exact fwd_case hty hab hs ha hb ihs iha ihb
    | absurd hs _ => exact fwd_absurd
    | lam c hcp hfg hb hm hc _ => exact fwd_lam _ _ _ _ _ c hcp hfg hb hm hc
    | appCopy ha iha => exact fwd_appCopy hty ha iha
    | appForget ha iha => exact fwd_appForget hty ha iha
    | appHost op ha iha => exact fwd_appHost op hty ha iha
    | app hcp hfg hh ha hf iha ihf =>
        exact fwd_app hty hN2 hcp hfg hh ha hf iha ihf
          (fun sz' h' ρ' m e t m' hpr => ihsz sz' h' ρ' m e t m' hpr)


end Lowering
