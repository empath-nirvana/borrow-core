import Lowering.PrintFwd

/-!
# Lowering — the print's calls  `[spec §56]`

`CallAt` for every value a source run applies: a `λ` (its body's print, `FwdOne`), a host
operation, `store ℓ`, and each of the machine's primitives, whose codes keep the source's memory
(`HRel`) as the source's head step changes it. The primitives that run a callback (`tab`,
`drop`, `count`, `count_try`, `bounded_fix`) loop as the source's reducts do (`tabFill`,
`dropFill`, `countNext`, `countTryNext`, `boundedFixNext`), calling the callback through
`CallAt` at smaller derivations.
-/

namespace Lowering
open BoCa
open BoCa.BoLo (Heap Head Step1 Steps Kont Alloc AHead)
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op LV St IM)

local instance : HostIs Backend2.lirHost := ⟨⟩

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
  | rt q c hq =>
      cases q <;> simp only [rtCode, reduceCtorEq] at hq <;>
        cases w <;> simp_all [Expr.argAt?, Expr.arg32?, Expr.arg64?, Expr.arg8?, Expr.lit?, Val.prim]
  | _ => cases w <;> simp_all [Expr.argAt?, Expr.arg32?, Expr.arg64?, Expr.arg8?, Expr.lit?,
      Val.prim, Val.unit, Val.pair, Val.inj₁, Val.inj₂, Val.lam, Val.loc, Val.storeV]

theorem vrel_argsAt {p : Prog} {N : Nat} {w : Width} {v : Val} {lv : LV} {a b : w.bits}
    (hv : VRel p N v lv) (h : v.1.argsAt? w = some (a, b)) :
    lv = .pair (.int (wordOf w a)) (.int (wordOf w b)) := by
  cases hv with
  | pair ha hb =>
      simp only [Val.pair, Expr.argsAt?, Option.pure_def, Option.bind_eq_bind,
        Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨x, hx, y, hy, rfl, rfl⟩ := h
      rw [vrel_argAt ha hx, vrel_argAt hb hy]
  | _ => simp_all [Expr.argsAt?, Val.prim, Val.unit, Val.inj₁, Val.inj₂, Val.lam, Val.loc,
      Val.storeV]

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



/-! ### The operations on the source's memory -/

/-- The state after `cellNew v`, its frame `F`. -/
def stNew (s : St) (F : Std.HashMap Var LV) (v : LV) : St :=
  { s with frame := F, mem := s.mem.insert s.next (some v), objs := s.objs.insert s.next 1,
           next := s.next + Backend2.regionSize }

/-- The state after `cellFree a`, its frame `F`. -/
def stFree (s : St) (F : Std.HashMap Var LV) (a : Nat) : St :=
  { s with frame := F, mem := s.mem.erase a, objs := s.objs.erase a }

/-- The state after `cellStore a v`, its frame `F`. -/
def stStore (s : St) (F : Std.HashMap Var LV) (a : Nat) (v : LV) : St :=
  { s with frame := F, mem := s.mem.insert a (some v) }

theorem evalOp_cellNew {p : Prog} {rt : LTy} {s : St} {x : Var} {v : LV}
    (hx : s.frame[x]? = some v) :
    (Backend2.evalOp (Backend2.tyIn p) .cellNew [x] rt).run s =
      .ok (.loc s.next, stNew s (s.frame.erase x) v) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  rfl

theorem evalOp_cellFree {p : Prog} {rt : LTy} {s : St} {x : Var} {a : Nat} {v : LV}
    (hx : s.frame[x]? = some (.loc a)) (ha : s.mem[a]? = some (some v)) :
    (Backend2.evalOp (Backend2.tyIn p) .cellFree [x] rt).run s =
      .ok (v, stFree s (s.frame.erase x) a) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    Except.bind, Except.pure, ha, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    StateT.pure]
  rfl

theorem evalOp_cellLoad {p : Prog} {rt : LTy} {s : St} {x : Var} {a : Nat} {v : LV}
    (hx : s.frame[x]? = some (.loc a)) (ha : s.mem[a]? = some (some v)) :
    (Backend2.evalOp (Backend2.tyIn p) .cellLoad [x] rt).run s =
      .ok (v, { s with frame := s.frame.erase x }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    Except.bind, Except.pure, ha, StateT.pure]

theorem takeAll_two_run {x y : Var} {u v : LV} {s : St} (hx : s.frame[x]? = some u)
    (hy : (s.frame.erase x)[y]? = some v) :
    (Backend2.takeAll [x, y]).run s =
      .ok ([u, v], ({ s with frame := (s.frame.erase x).erase y } : St)) :=
  takeAll_cons_run hx (takeAll_one_run (s := { s with frame := s.frame.erase x }) hy)

theorem evalOp_cellStore {p : Prog} {rt : LTy} {s : St} {x y : Var} {a : Nat} {v w : LV}
    (hx : s.frame[x]? = some (.loc a)) (hy : (s.frame.erase x)[y]? = some v)
    (ha : s.mem[a]? = some (some w)) :
    (Backend2.evalOp (Backend2.tyIn p) .cellStore [x, y] rt).run s =
      .ok (.unit, stStore s ((s.frame.erase x).erase y) a v) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_two_run hx hy]
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    Except.bind, Except.pure, ha, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    StateT.pure]
  rfl

/-! ### The source's memory, kept -/

theorem HRel.new {p : Prog} {N c : Nat} {μ : Heap} {s : St} (h : HRel p N c μ s)
    (F : Std.HashMap Var LV) {v : Val} {lv : LV} (hv : VRel p N v lv) :
    HRel p N (c + 1) (μ.upd (regionBase c) v) (stNew s F lv) := by
  have hfree : μ (regionBase c) = none := by
    by_contra hne; exact absurd (h.below _ hne) (lt_irrefl _)
  refine ⟨?_, fun a => ?_, fun a w hw => ?_, fun a => ?_, fun a ha => ?_⟩
  · simp only [stNew, h.next, regionBase]; ring
  · by_cases ha : a = regionBase c
    · subst ha; simp [stNew, h.next]
    · simp only [BoLo.Heap.upd_other ha, stNew, h.next, Std.HashMap.getElem?_insert, beq_iff_eq,
        Ne.symm ha, if_false]; exact h.dom a
  · by_cases ha : a = regionBase c
    · subst ha; simp only [BoLo.Heap.upd_same, Option.some.injEq] at hw; subst hw
      exact ⟨lv, by simp [stNew, h.next], hv⟩
    · rw [BoLo.Heap.upd_other ha] at hw
      simp only [stNew, h.next, Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm ha, if_false]
      exact h.val a w hw
  · by_cases ha : a = regionBase c
    · subst ha; simp [stNew, h.next]
    · simp only [BoLo.Heap.upd_other ha, stNew, h.next, Std.HashMap.getElem?_insert, beq_iff_eq,
        Ne.symm ha, if_false]; exact h.objs a
  · have hle : regionBase c < regionBase (c + 1) := by
      simp only [regionBase, Backend2.regionSize]; omega
    by_cases ha' : a = regionBase c
    · subst ha'; exact hle
    · rw [BoLo.Heap.upd_other ha'] at ha
      exact lt_trans (h.below a ha) hle

theorem HRel.free {p : Prog} {N c : Nat} {μ : Heap} {s : St} (h : HRel p N c μ s)
    (F : Std.HashMap Var LV) {ℓ : Nat} :
    HRel p N c (μ.del ℓ) (stFree s F ℓ) := by
  refine ⟨h.next, fun a => ?_, fun a w hw => ?_, fun a => ?_, fun a ha => ?_⟩
  · by_cases ha : a = ℓ
    · subst ha; simp [stFree]
    · simp only [BoLo.Heap.del_other ha, stFree, Std.HashMap.getElem?_erase, beq_iff_eq,
        Ne.symm ha, if_false]; exact h.dom a
  · by_cases ha : a = ℓ
    · subst ha; simp at hw
    · rw [BoLo.Heap.del_other ha] at hw
      simp only [stFree, Std.HashMap.getElem?_erase, beq_iff_eq, Ne.symm ha, if_false]
      exact h.val a w hw
  · by_cases ha : a = ℓ
    · subst ha; simp [stFree]
    · simp only [BoLo.Heap.del_other ha, stFree, Std.HashMap.getElem?_erase, beq_iff_eq,
        Ne.symm ha, if_false]; exact h.objs a
  · by_cases ha' : a = ℓ
    · subst ha'; simp at ha
    · rw [BoLo.Heap.del_other ha'] at ha; exact h.below a ha

theorem HRel.store {p : Prog} {N c : Nat} {μ : Heap} {s : St} (h : HRel p N c μ s)
    (F : Std.HashMap Var LV) {ℓ : Nat} {w : Val} (hw : μ ℓ = some w) {v : Val} {lv : LV}
    (hv : VRel p N v lv) : HRel p N c (μ.upd ℓ v) (stStore s F ℓ lv) := by
  refine ⟨h.next, fun a => ?_, fun a u hu => ?_, fun a => ?_, fun a ha => ?_⟩
  · by_cases ha : a = ℓ
    · subst ha; simp [stStore]
    · simp only [BoLo.Heap.upd_other ha, stStore, Std.HashMap.getElem?_insert, beq_iff_eq,
        Ne.symm ha, if_false]; exact h.dom a
  · by_cases ha : a = ℓ
    · subst ha; simp only [BoLo.Heap.upd_same, Option.some.injEq] at hu; subst hu
      exact ⟨lv, by simp [stStore], hv⟩
    · rw [BoLo.Heap.upd_other ha] at hu
      simp only [stStore, Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm ha, if_false]
      exact h.val a u hu
  · simp only [stStore]
    by_cases ha : a = ℓ
    · subst ha; rw [h.objs a, hw]; simp
    · rw [BoLo.Heap.upd_other ha]; exact h.objs a
  · by_cases ha' : a = ℓ
    · subst ha'; exact h.below a (by rw [hw]; simp)
    · rw [BoLo.Heap.upd_other ha'] at ha; exact h.below a ha


/-! ### The source's head steps on a function and an argument -/

theorem ahead_det {A : Alloc} {c c₁ : Nat} {μ μ₁ : Heap} {a r : Expr}
    (h : AHead (ℍ := Backend2.lirHost) A c μ a c₁ μ₁ r) (hn : a.allocs = false) :
    c₁ = c ∧ Head (ℍ := Backend2.lirHost) μ a μ₁ r := by
  cases h with
  | det h _ => exact ⟨rfl, h⟩
  | alloc => simp [Expr.allocs] at hn
  | tab => simp [Expr.allocs] at hn

theorem head_lam_inv {μ μ' : Heap} {b r : Expr} {v : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.lam b).1 v.1) μ' r) : μ' = μ ∧ r = b.subst 0 v := by
  generalize hE : Expr.app (Val.lam b).1 v.1 = E at h
  cases h with
  | beta b' v' =>
      simp only [Expr.app.injEq, Expr.val, Val.lam, Expr.lam.injEq] at hE
      obtain ⟨rfl, hv⟩ := hE
      have : v = v' := Subtype.ext hv
      subst this; exact ⟨rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim, Val.lam]

theorem head_host_inv {μ μ' : Heap} {op : HostOp} {r : Expr} {v : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim (.host op)).1 v.1) μ' r) :
    μ' = μ ∧ ∃ r' : Val, Backend2.lirHost.call op v = some r' ∧ r = r'.1 := by
  generalize hE : Expr.app (Val.prim (.host op)).1 v.1 = E at h
  cases h with
  | host op' v' r' hr =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, Expr.prim.injEq, Prim.host.injEq] at hE
      obtain ⟨rfl, hv⟩ := hE
      have : v = v' := Subtype.ext hv
      subst this; exact ⟨rfl, r', hr, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_free_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .free).1 va.1) μ₁ r) :
    ∃ ℓ v, va = Val.loc ℓ ∧ μ ℓ = some v ∧ μ₁ = μ.del ℓ ∧ r = v.1 := by
  generalize hE : Expr.app (Val.prim .free).1 va.1 = E at h
  cases h with
  | free ℓ v hv =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨ℓ, v, Subtype.ext hE, hv, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_load_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .load).1 va.1) μ₁ r) :
    ∃ ℓ v, va = Val.loc ℓ ∧ μ ℓ = some v ∧ μ₁ = μ ∧ r = v.1 := by
  generalize hE : Expr.app (Val.prim .load).1 va.1 = E at h
  cases h with
  | load ℓ v hv =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨ℓ, v, Subtype.ext hE, hv, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_store_inv {μ μ₁ : Heap} {r : Expr} {v₀ va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.storeV v₀).1 va.1) μ₁ r) :
    ∃ ℓ w, v₀ = Val.loc ℓ ∧ μ ℓ = some w ∧ μ₁ = μ.upd ℓ va ∧ r = Val.unit.1 := by
  generalize hE : Expr.app (Val.storeV v₀).1 va.1 = E at h
  cases h with
  | store ℓ v w hw =>
      simp only [Expr.app.injEq, Expr.val, Val.storeV, Val.prim, true_and] at hE
      obtain ⟨h₁, h₂⟩ := hE
      have e₂ : va = v := Subtype.ext h₂
      subst e₂
      exact ⟨ℓ, w, Subtype.ext h₁, hw, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim, Val.storeV]

theorem head_idx_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .idx).1 va.1) μ₁ r) :
    ∃ ℓ n i, va = Val.pair (Val.arr ℓ n) (Val.i32 i) ∧ μ₁ = μ ∧ r = (idxAns ℓ n i).1 := by
  generalize hE : Expr.app (Val.prim .idx).1 va.1 = E at h
  cases h with
  | idx ℓ n i =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨ℓ, n, i, Subtype.ext hE, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_split_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .split).1 va.1) μ₁ r) :
    ∃ ℓ n i, va = Val.pair (Val.arr ℓ n) (Val.i32 i) ∧ μ₁ = μ ∧ r = (splitAns ℓ n i).1 := by
  generalize hE : Expr.app (Val.prim .split).1 va.1 = E at h
  cases h with
  | split ℓ n i =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨ℓ, n, i, Subtype.ext hE, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_drop_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .drop).1 va.1) μ₁ r) :
    ∃ f ℓ n, va = Val.pair f (Val.arr ℓ n) ∧ μ₁ = μ ∧ r = dropFill f ℓ 0 n.toNat := by
  generalize hE : Expr.app (Val.prim .drop).1 va.1 = E at h
  cases h with
  | drop f ℓ n =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨f, ℓ, n, Subtype.ext hE, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_count_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .count).1 va.1) μ₁ r) :
    ∃ f n i st, va = Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) st)) ∧ μ₁ = μ ∧
      r = countNext f n i st := by
  generalize hE : Expr.app (Val.prim .count).1 va.1 = E at h
  cases h with
  | count f n i st =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨f, n, i, st, Subtype.ext hE, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_countTry_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .countTry).1 va.1) μ₁ r) :
    ∃ f n i st, va = Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) st)) ∧ μ₁ = μ ∧
      r = countTryNext f n i st := by
  generalize hE : Expr.app (Val.prim .countTry).1 va.1 = E at h
  cases h with
  | countTry f n i st =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨f, n, i, st, Subtype.ext hE, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem head_bf_inv {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (Val.prim .boundedFix).1 va.1) μ₁ r) :
    ∃ sv k a, va = Val.pair sv (Val.pair (Val.i32 k) a) ∧ μ₁ = μ ∧ r = boundedFixNext sv k a := by
  generalize hE : Expr.app (Val.prim .boundedFix).1 va.1 = E at h
  cases h with
  | boundedFix sv k a =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨sv, k, a, Subtype.ext hE, rfl, rfl⟩
  | _ => simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim]

theorem ahead_alloc_inv {c c₁ : Nat} {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .alloc).1 va.1) c₁ μ₁ r) :
    c₁ = c + 1 ∧ μ₁ = μ.upd (bumpAlloc.pick c μ 1) va ∧ r = (Val.loc (bumpAlloc.pick c μ 1)).1 := by
  generalize hE : Expr.app (Val.prim .alloc).1 va.1 = E at h
  cases h with
  | det h hn => subst hE; simp [Expr.allocs, Val.prim] at hn
  | alloc v hv =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      have : va = v := Subtype.ext hE
      subst this; exact ⟨rfl, rfl, rfl⟩
  | tab => simp_all [Expr.val, Val.prim]

theorem ahead_tab_inv {c c₁ : Nat} {μ μ₁ : Heap} {r : Expr} {va : Val}
    (h : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .tab).1 va.1) c₁ μ₁ r) :
    ∃ cc f, va = Val.pair (Val.i32 cc) f ∧ c₁ = c + 1 ∧
      μ₁ = μ.fill (bumpAlloc.pick c μ (arrLen cc).toNat) (arrLen cc).toNat Val.unit ∧
      r = tabFill f (bumpAlloc.pick c μ (arrLen cc).toNat) (arrLen cc) 0 (arrLen cc).toNat := by
  generalize hE : Expr.app (Val.prim .tab).1 va.1 = E at h
  cases h with
  | det h hn => subst hE; simp [Expr.allocs, Val.prim] at hn
  | alloc => simp_all [Expr.val, Val.prim]
  | tab cc f hv =>
      simp only [Expr.app.injEq, Expr.val, Val.prim, true_and] at hE
      exact ⟨cc, f, Subtype.ext hE, rfl, rfl, rfl⟩

/-! ### Calls of the primitives' codes -/

theorem HRel.congr {p : Prog} {N c : Nat} {μ : Heap} {s s' : St} (h : HRel p N c μ s)
    (hm : s'.mem = s.mem) (ho : s'.objs = s.objs) (hn : s'.next = s.next) : HRel p N c μ s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨hn ▸ h1, fun a => hm ▸ h2 a, fun a v hv => hm ▸ h3 a v hv, fun a => ho ▸ h4 a, h5⟩

theorem vrel_loc_inv {p : Prog} {N : Nat} {ℓ : Loc} {lv : LV} (h : VRel p N (Val.loc ℓ) lv) :
    lv = .loc ℓ := by
  generalize hV : Val.loc ℓ = V at h
  cases h with
  | loc ℓ' =>
      have e := congrArg Subtype.val hV
      simp only [Val.loc, Expr.loc.injEq] at e; subst e; rfl
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.prim, Val.inj₁,
      Val.inj₂, Val.lam, Val.loc, Val.storeV] at e

theorem vrel_i32_inv {p : Prog} {N : Nat} {n : UInt32} {lv : LV} (h : VRel p N (Val.i32 n) lv) :
    lv = .int n.toUInt64 := by
  generalize hV : Val.i32 n = V at h
  cases h with
  | lit c =>
      have e := congrArg Subtype.val hV
      simp only [Val.i32, Val.prim, Expr.prim.injEq, Prim.lit.injEq] at e; subst e; rfl
  | rt q c hq =>
      have e := congrArg Subtype.val hV
      simp only [Val.i32, Val.prim, Expr.prim.injEq] at e; subst e; simp [rtCode] at hq
  | host op c _ =>
      have e := congrArg Subtype.val hV
      simp [Val.i32, Val.prim] at e
  | _ => have e := congrArg Subtype.val hV; simp [Val.pair, Val.unit, Val.inj₁,
      Val.inj₂, Val.lam, Val.loc, Val.storeV, Val.i32] at e

theorem single_get (lva : LV) (x : Nat) :
    ((∅ : Std.HashMap Var LV).insert 0 lva)[x]? = if x = 0 then some lva else none := by
  rw [Std.HashMap.getElem?_insert]
  by_cases h : x = 0
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **A call of a code of one parameter**: its body from the frame of its argument. -/
theorem call1 {p : Prog} {c : Nat} {body : Tm} (hc : CodeAt p c 0 body) {la v : LV} {s s₁ : St}
    (hb : ∀ rt : LTy, Sim (fun f => Backend2.eval p f rt body)
      ({ s with frame := (∅ : Std.HashMap Var LV).insert 0 la } : St) (.ok (v, s₁)))
    (he : ∀ x : Nat, s₁.frame[x]? = none) :
    Sim (fun f => Backend2.callClos p f (.clos c []) (some la) 0) s
      (.ok (v, ({ s₁ with frame := s.frame } : St))) :=
  sim_callClos hc.1 (sim_code hc (args := [] ++ [la]) rfl (fun rt => by
    rw [show (([] : List LV) ++ [la]) = [la] from rfl, zip1]; exact hb rt) he)

theorem empty_erase0 (la : LV) (x : Nat) :
    (((∅ : Std.HashMap Var LV).insert 0 la).erase 0)[x]? = none := by
  by_cases hx : 0 = x
  · subst hx; exact erase_get_self
  · rw [erase_get_ne hx, insert_get_ne hx]; simp

theorem call_free {p : Prog} {N : Nat} (hrt : RT p N) {va : Val} {la : LV} {s : St}
    {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .free).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 1 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨ℓ, v, rfl, hv, rfl, rfl⟩ := head_free_inv hd
  obtain ⟨rfl, rfl, hw⟩ := big_val_inv hbr v rfl
  subst hw
  obtain rfl := vrel_loc_inv hva
  obtain ⟨lv, hlv, hrel⟩ := hh.val ℓ _ hv
  let s₀ : St := { s with frame := (∅ : Std.HashMap Var LV).insert 0 (.loc ℓ) }
  refine ⟨lv, { stFree s₀ (s₀.frame.erase 0) ℓ with frame := s.frame }, hrel,
    (hh.free s.frame).congr rfl rfl rfl, rfl, call1 hrt.free (fun rt => ?_) (empty_erase0 _)⟩
  exact sim_prim (fun f => by rw [Backend2.eval] <;> simp)
    (evalOp_cellFree (s := s₀) insert_get_self hlv)

theorem call_load {p : Prog} {N : Nat} (hrt : RT p N) {va : Val} {la : LV} {s : St}
    {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .load).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 2 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨ℓ, v, rfl, hv, rfl, rfl⟩ := head_load_inv hd
  obtain ⟨rfl, rfl, hw⟩ := big_val_inv hbr v rfl
  subst hw
  obtain rfl := vrel_loc_inv hva
  obtain ⟨lv, hlv, hrel⟩ := hh.val ℓ _ hv
  let s₀ : St := { s with frame := (∅ : Std.HashMap Var LV).insert 0 (.loc ℓ) }
  refine ⟨lv, { s with frame := s.frame }, hrel, hh, rfl, ?_⟩
  exact call1 (s₁ := { s₀ with frame := s₀.frame.erase 0 }) hrt.load (fun rt =>
    sim_prim (fun f => by rw [Backend2.eval] <;> simp)
      (evalOp_cellLoad (s := s₀) insert_get_self hlv)) (empty_erase0 _)

theorem call_alloc {p : Prog} {N : Nat} (hrt : RT p N) {va : Val} {la : LV} {s : St}
    {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .alloc).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 0 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, rfl, rfl⟩ := ahead_alloc_inv hhd
  have hpick : bumpAlloc.pick c μ 1 = regionBase c := bumpAlloc_pick (fun i hi => by
    have : i = 0 := by omega
    subst this
    by_contra hne
    have h' := hh.below _ hne
    rw [Nat.add_zero] at h'
    exact absurd h' (lt_irrefl _))
  rw [hpick] at hbr
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbr (Val.loc (regionBase c)) rfl
  let s₀ : St := { s with frame := (∅ : Std.HashMap Var LV).insert 0 la }
  refine ⟨.loc (regionBase c), { stNew s₀ (s₀.frame.erase 0) la with frame := s.frame }, .loc _,
    (hh.new s.frame hva).congr rfl rfl rfl, rfl, ?_⟩
  have := call1 (s := s) (s₁ := stNew s₀ (s₀.frame.erase 0) la) hrt.alloc (fun rt =>
    sim_prim (fun f => by rw [Backend2.eval] <;> simp)
      (evalOp_cellNew (s := s₀) insert_get_self)) (empty_erase0 _)
  rw [show s₀.next = regionBase c from hh.next] at this
  exact this

theorem zip2 (a b : LV) :
    (((List.range (1 + 1)).zip [a, b]).foldl (fun m x => m.insert x.1 x.2) (∅ : Std.HashMap Var LV)) =
      ((∅ : Std.HashMap Var LV).insert 0 a).insert 1 b := rfl

theorem empty_erase01 (a b : LV) (x : Nat) :
    (((((∅ : Std.HashMap Var LV).insert 0 a).insert 1 b).erase 0).erase 1)[x]? = none := by
  by_cases h1 : 1 = x
  · subst h1; exact erase_get_self
  rw [erase_get_ne h1]
  by_cases h0 : 0 = x
  · subst h0; exact erase_get_self
  rw [erase_get_ne h0, insert_get_ne h1, insert_get_ne h0]; simp

/-- **A call of a code of one captured value and an argument.** -/
theorem call2 {p : Prog} {c : Nat} {body : Tm} (hc : CodeAt p c 1 body) {a la v : LV} {s s₁ : St}
    (hb : ∀ rt : LTy, Sim (fun f => Backend2.eval p f rt body)
      ({ s with frame := ((∅ : Std.HashMap Var LV).insert 0 a).insert 1 la } : St) (.ok (v, s₁)))
    (he : ∀ x : Nat, s₁.frame[x]? = none) :
    Sim (fun f => Backend2.callClos p f (.clos c [a]) (some la) 0) s
      (.ok (v, ({ s₁ with frame := s.frame } : St))) :=
  sim_callClos hc.1 (sim_code hc (args := [a] ++ [la]) rfl (fun rt => by
    rw [show (([a] : List LV) ++ [la]) = [a, la] from rfl, zip2]; exact hb rt) he)

theorem call_store1 {p : Prog} {N : Nat} (hrt : RT p N) {v₀ va : Val} {lv₀ la : LV} {s : St}
    {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.storeV v₀).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hv₀ : VRel p N v₀ lv₀)
    (hva : VRel p N va la) (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos store1Code [lv₀]) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨ℓ, w', rfl, hw', rfl, rfl⟩ := head_store_inv hd
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbr Val.unit rfl
  obtain rfl := vrel_loc_inv hv₀
  obtain ⟨lw', hlw', -⟩ := hh.val ℓ w' hw'
  let s₀ : St := { s with frame := ((∅ : Std.HashMap Var LV).insert 0 (.loc ℓ)).insert 1 la }
  refine ⟨.unit, { stStore s₀ ((s₀.frame.erase 0).erase 1) ℓ la with frame := s.frame }, .unit,
    (hh.store s.frame hw' hva).congr rfl rfl rfl, rfl, call2 hrt.store1 (fun rt => ?_)
    (empty_erase01 _ _)⟩
  exact sim_prim (fun f => by rw [Backend2.eval] <;> simp)
    (evalOp_cellStore (s := s₀) (x := 0) (y := 1) (a := ℓ) (v := la)
      (by show (((∅ : Std.HashMap Var LV).insert 0 (LV.loc ℓ)).insert 1 la)[(0 : Nat)]? =
            some (LV.loc ℓ)
          rw [insert_get_ne (by omega)]; exact insert_get_self)
      (by show ((((∅ : Std.HashMap Var LV).insert 0 (LV.loc ℓ)).insert 1 la).erase 0)[(1 : Nat)]? =
            some la
          rw [erase_get_ne (by omega)]; exact insert_get_self) hlw')

theorem call_host {p : Prog} {N : Nat} {op : HostOp} {c₀ : Nat} (hc : CodeAt p c₀ 0 (hostFn op))
    {va : Val} {la : LV} {s : St} {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim (.host op)).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos c₀ []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨rfl, r', hcl, rfl⟩ := head_host_inv hd
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbr r' rfl
  let s₀ : St := { s with frame := (∅ : Std.HashMap Var LV).insert 0 la }
  obtain ⟨lr, hrun, hlr⟩ := host_corr (p := p) (N := N) hcl hva
    ({ s₀ with frame := s₀.frame.erase 0 } : St)
  refine ⟨lr, { s with frame := s.frame }, hlr, hh, rfl, ?_⟩
  exact call1 (s₁ := { s₀ with frame := s₀.frame.erase 0 }) hc
    (fun rt => sim_host (s := s₀) insert_get_self hrun) (empty_erase0 _)

theorem vrel_arr_idx_inv {p : Prog} {N : Nat} {ℓ : Loc} {n i : UInt32} {lv : LV}
    (h : VRel p N (Val.pair (Val.arr ℓ n) (Val.i32 i)) lv) :
    lv = .pair (.pair (.loc ℓ) (.int n.toUInt64)) (.int i.toUInt64) := by
  obtain ⟨x, y, rfl, hx, hy⟩ := vrel_pair_inv h
  obtain ⟨x₁, x₂, rfl, hx₁, hx₂⟩ := vrel_pair_inv hx
  rw [vrel_loc_inv hx₁, vrel_i32_inv hx₂, vrel_i32_inv hy]

theorem evalOp_famIdx {p : Prog} {rt : LTy} {s : St} {x y : Var} {ℓ : Nat} {n i : UInt64}
    (hx : s.frame[x]? = some (.pair (.loc ℓ) (.int n))) (hy : (s.frame.erase x)[y]? = some (.int i)) :
    (Backend2.evalOp (Backend2.tyIn p) .famIdx [x, y] rt).run s =
      .ok (if i.toUInt32 < n.toUInt32 then .inj false (.loc (ℓ + i.toUInt32.toNat))
        else .inj true .unit, { s with frame := (s.frame.erase x).erase y }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_two_run hx hy]
  rfl

theorem evalOp_famSplit {p : Prog} {rt : LTy} {s : St} {x y : Var} {ℓ : Nat} {n i : UInt64}
    (hx : s.frame[x]? = some (.pair (.loc ℓ) (.int n))) (hy : (s.frame.erase x)[y]? = some (.int i)) :
    (Backend2.evalOp (Backend2.tyIn p) .famSplit [x, y] rt).run s =
      .ok (if i.toUInt32 ≤ n.toUInt32 then
          .inj false (.pair (.pair (.loc ℓ) (.int i.toUInt32.toUInt64))
            (.pair (.loc (ℓ + i.toUInt32.toNat)) (.int (n.toUInt32 - i.toUInt32).toUInt64)))
        else .inj true (.pair (.loc ℓ) (.int n.toUInt32.toUInt64)),
        { s with frame := (s.frame.erase x).erase y }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_two_run hx hy]
  rfl

/-- The frame of `letpair 1 2 0` on the argument `(a, b)`. -/
abbrev lp0 (a b : LV) : Std.HashMap Var LV :=
  ((((∅ : Std.HashMap Var LV).insert 0 (.pair a b)).erase 0).insert 1 a).insert 2 b

theorem lp0_1 (a b : LV) : (lp0 a b)[(1 : Nat)]? = some a := by
  simp only [lp0]; rw [insert_get_ne (by omega)]; exact insert_get_self

theorem lp0_2 (a b : LV) : ((lp0 a b).erase 1)[(2 : Nat)]? = some b := by
  rw [erase_get_ne (by omega)]; exact insert_get_self

theorem lp0_empty (a b : LV) (x : Nat) : (((lp0 a b).erase 1).erase 2)[x]? = none := by
  by_cases h2 : 2 = x
  · subst h2; exact erase_get_self
  rw [erase_get_ne h2]
  by_cases h1 : 1 = x
  · subst h1; exact erase_get_self
  rw [erase_get_ne h1]
  simp only [lp0]
  rw [insert_get_ne h2, insert_get_ne h1]
  by_cases h0 : 0 = x
  · subst h0; exact erase_get_self
  rw [erase_get_ne h0, insert_get_ne h0]; simp

theorem call_idx {p : Prog} {N : Nat} (hrt : RT p N) {va : Val} {la : LV} {s : St}
    {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .idx).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 5 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨ℓ, n, i, rfl, rfl, rfl⟩ := head_idx_inv hd
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbr _ rfl
  obtain rfl := vrel_arr_idx_inv hva
  let a : LV := .pair (.loc ℓ) (.int n.toUInt64)
  let b : LV := .int i.toUInt64
  let s₁ : St := { s with frame := lp0 a b }
  refine ⟨if i.toUInt64.toUInt32 < n.toUInt64.toUInt32 then
      .inj false (.loc (ℓ + i.toUInt64.toUInt32.toNat)) else .inj true .unit,
    { s₁ with frame := s.frame }, ?_, hh, rfl,
    call1 (s₁ := { s₁ with frame := (s₁.frame.erase 1).erase 2 }) hrt.idx (fun rt => ?_)
      (lp0_empty a b)⟩
  · simp only [UInt32.toUInt32_toUInt64, idxAns]
    split
    · exact .inj₁ (.loc _)
    · exact .inj₂ .unit
  · refine sim_letpair (s := { s with frame := (∅ : Std.HashMap Var LV).insert 0 (.pair a b) })
      insert_get_self ?_
    exact sim_prim (fun f => by rw [Backend2.eval] <;> simp) (evalOp_famIdx (lp0_1 a b) (lp0_2 a b))

theorem call_split {p : Prog} {N : Nat} (hrt : RT p N) {va : Val} {la : LV} {s : St}
    {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .split).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 6 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨ℓ, n, i, rfl, rfl, rfl⟩ := head_split_inv hd
  obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbr _ rfl
  obtain rfl := vrel_arr_idx_inv hva
  let a : LV := .pair (.loc ℓ) (.int n.toUInt64)
  let b : LV := .int i.toUInt64
  let s₁ : St := { s with frame := lp0 a b }
  refine ⟨if i.toUInt64.toUInt32 ≤ n.toUInt64.toUInt32 then
      .inj false (.pair (.pair (.loc ℓ) (.int i.toUInt64.toUInt32.toUInt64))
        (.pair (.loc (ℓ + i.toUInt64.toUInt32.toNat))
          (.int (n.toUInt64.toUInt32 - i.toUInt64.toUInt32).toUInt64)))
      else .inj true (.pair (.loc ℓ) (.int n.toUInt64.toUInt32.toUInt64)),
    { s₁ with frame := s.frame }, ?_, hh, rfl,
    call1 (s₁ := { s₁ with frame := (s₁.frame.erase 1).erase 2 }) hrt.split (fun rt => ?_)
      (lp0_empty a b)⟩
  · simp only [UInt32.toUInt32_toUInt64, splitAns]
    split
    · exact .inj₁ (.pair (.pair (.loc _) (.lit (.i32 _))) (.pair (.loc _) (.lit (.i32 _))))
    · exact .inj₂ (.pair (.loc _) (.lit (.i32 _)))
  · refine sim_letpair (s := { s with frame := (∅ : Std.HashMap Var LV).insert 0 (.pair a b) })
      insert_get_self ?_
    exact sim_prim (fun f => by rw [Backend2.eval] <;> simp) (evalOp_famSplit (lp0_1 a b) (lp0_2 a b))

/-! ### Calls of `λ`s -/

theorem getElem_idxOf_mem {l : List Nat} {k : Nat} (h : k ∈ l) : l[l.idxOf k]? = some k := by
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem h)]
  simp [List.getElem_idxOf]

/-- **A call of a `λ`'s closure**: its body's print runs from the frame of its captured values
and its argument, its argument dropped first when the body does not read it. -/
theorem call_lam {p : Prog} {N sz : Nat} (hty : TyOK p N)
    (hfwd : ∀ ρ n out e t n', Pr p N ρ n out e t n' → FwdOne p N sz ρ n out e t n')
    {c m : Nat} {b : Expr} {tb : Tm} {γ : List Val} {env : List LV}
    (hpr : Pr p N (lamEnv b) ((capt b).length + 1) noOut b tb m) (hm : m ≤ N)
    (hc : CodeAt p c (capt b).length (dropIf (!mentions b 0) (capt b).length tb))
    (hlen : env.length = (capt b).length) (hcapl : ∀ k, k ∈ capt b → k < γ.length)
    (hrel : ∀ i (hi : i < env.length) (k : Nat) (hk : k < γ.length), (capt b)[i]? = some k →
      VRel p N γ[k] env[i])
    {va : Val} {la : LV} {s : St} {c₀ c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hk : k ≤ sz)
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c₀ μ
      (.app (Val.lam (Expr.psub 1 γ b)).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c₀ μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos c env) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨rfl, rfl⟩ := head_lam_inv hd
  rw [psub_arm] at hbr
  have hm₀ := pr_le hpr
  let K := (capt b).length
  let F₀ := ((List.range (K + 1)).zip (env ++ [la])).foldl (fun m x => m.insert x.1 x.2)
    (∅ : Std.HashMap Var LV)
  have hF₀ : ∀ x : Nat, F₀[x]? = (env ++ [la])[x]? := fun x => by
    have := zipFrame_get (env ++ [la]) x
    simp only [List.length_append, List.length_singleton, hlen] at this
    exact this
  let F₁ := if (!mentions b 0) = true then F₀.erase K else F₀
  have hlam0 : lamEnv b 0 = K := by simp [lamEnv, K]
  have hlamS : ∀ k, lamEnv b (k + 1) = (capt b).idxOf k := fun k => by simp [lamEnv]
  have hnd := capt_nodup b
  have hfr : FrameOK p N (va :: γ) (lamEnv b) (K + 1) (need b noOut) F₁ := by
    refine ⟨fun x v hx => ?_, fun j hj => ?_, fun j j' hj hj' he => ?_⟩
    · have hx' : F₀[x]? = some v := by
        simp only [F₁] at hx; split at hx
        · by_cases hxK : K = x
          · subst hxK; rw [erase_get_self] at hx; cases hx
          · rwa [erase_get_ne hxK] at hx
        · exact hx
      rw [hF₀] at hx'
      have := (List.getElem?_eq_some_iff.mp hx').1
      simpa [hlen, K] using this
    · have hjm : mentions b j = true := by simpa [need, noOut] using hj
      rcases j with _ | k
      · refine ⟨va, la, rfl, ?_, hva⟩
        rw [hlam0]
        simp only [F₁, hjm, Bool.not_true, Bool.false_eq_true, if_false]
        rw [hF₀, List.getElem?_append_right (by omega)]
        simp [hlen, K]
      · have hkc : k ∈ capt b := mem_capt.mpr hjm
        have hkl := hcapl k hkc
        have hi := List.idxOf_lt_length_of_mem hkc
        refine ⟨γ[k], env[(capt b).idxOf k]'(by omega), by simp [List.getElem?_eq_getElem hkl], ?_,
          hrel _ (by omega) k hkl (getElem_idxOf_mem hkc)⟩
        rw [hlamS]
        have hne : K ≠ (capt b).idxOf k := by omega
        have : F₁[(capt b).idxOf k]? = F₀[(capt b).idxOf k]? := by
          simp only [F₁]; split
          · exact erase_get_ne hne
          · rfl
        rw [this, hF₀, List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
    · have hjm : mentions b j = true := by simpa [need, noOut] using hj
      have hjm' : mentions b j' = true := by simpa [need, noOut] using hj'
      rcases j with _ | k <;> rcases j' with _ | k'
      · rfl
      · rw [hlam0, hlamS] at he
        have := List.idxOf_lt_length_of_mem (mem_capt.mpr hjm'); omega
      · rw [hlam0, hlamS] at he
        have := List.idxOf_lt_length_of_mem (mem_capt.mpr hjm); omega
      · rw [hlamS, hlamS] at he
        have e1 := getElem_idxOf_mem (mem_capt.mpr hjm)
        have e2 := getElem_idxOf_mem (mem_capt.mpr hjm')
        rw [he] at e1; rw [e1] at e2; cases e2; rfl
  obtain ⟨lw, s', hlw, hh', hpost, hsim⟩ := hfwd _ _ _ _ _ _ hpr hm (va :: γ)
    { s with frame := F₁ } c₁ μ₁ c' μ' w k hk hbr hfr (hh.frame _)
  have hempty : ∀ x : Nat, s'.frame[x]? = none := by
    intro x
    by_cases hxK : x = K
    · subst hxK
      by_cases h0 : mentions b 0 = true
      · have := hpost.1 0 (by simp [cons, noOut, h0]); rwa [hlam0] at this
      · rw [hpost.2 _ (fun j hj he => by
          rcases j with _ | k
          · simp [cons, noOut] at hj; exact h0 hj
          · rw [hlamS] at he
            have := List.idxOf_lt_length_of_mem (mem_capt.mpr (by simpa [cons, noOut] using hj))
            omega)]
        show F₁[K]? = none
        simp only [F₁]
        rw [if_pos (by simpa using h0)]; exact erase_get_self
    by_cases hxl : x < K
    · have hk : (capt b)[x] ∈ capt b := List.getElem_mem hxl
      have := hpost.1 ((capt b)[x] + 1) (by simp [cons, noOut, mem_capt.mp hk])
      rwa [hlamS, List.Nodup.idxOf_getElem hnd x hxl] at this
    · rw [hpost.2 x (fun j hj he => by
        rcases j with _ | k
        · rw [hlam0] at he; omega
        · rw [hlamS] at he; have := List.idxOf_le_length (l := capt b) (a := k); omega)]
      show F₁[x]? = none
      have : F₀[x]? = none := by
        rw [hF₀, List.getElem?_eq_none (by simp [hlen]; omega)]
      simp only [F₁]; split
      · rw [erase_get_ne (Ne.symm hxK)]; exact this
      · exact this
  refine ⟨lw, { s' with frame := s.frame }, hlw, hh'.frame _, rfl, ?_⟩
  refine sim_callClos hc.1 (sim_code hc (by simp [hlen]) (fun rt => ?_) hempty)
  refine sim_dropIf (hty _ (by omega)) (fun h0 => ⟨la, ?_⟩) ?_
  · show F₀[K]? = some la
    rw [hF₀, List.getElem?_append_right (by omega)]; simp [hlen, K]
  · exact hsim rt

/-! ### Counters -/

theorem mask32 (x : UInt64) : (x &&& 0xFFFFFFFF).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and]
  have : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem mask32_word (n : UInt32) : (n.toUInt64 &&& 0xFFFFFFFF) = n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [mask32, UInt32.toNat_toUInt64]
  exact Nat.mod_eq_of_lt n.toNat_lt

theorem mask32_succ (i : UInt32) : ((i.toUInt64 + 1) &&& 0xFFFFFFFF) = (i + 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [mask32, UInt32.toNat_toUInt64, UInt64.toNat_add, UInt32.toNat_add, UInt32.toNat_toUInt64]
  have := i.toNat_lt
  simp only [UInt64.toNat_ofNat, UInt32.toNat_ofNat]
  omega

theorem mask32_pred (i : UInt32) : ((i.toUInt64 - 1) &&& 0xFFFFFFFF) = (i - 1).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [mask32, UInt32.toNat_toUInt64, UInt64.toNat_sub, UInt32.toNat_sub, UInt32.toNat_toUInt64]
  have := i.toNat_lt
  simp only [UInt64.toNat_ofNat, UInt32.toNat_ofNat]
  omega

theorem clamp_word (n : UInt32) :
    (if n.toUInt64.toUInt32 < 0x80000000 then n.toUInt64 &&& 0xFFFFFFFF else 0) =
      (arrLen n).toUInt64 := by
  simp only [UInt32.toUInt32_toUInt64, mask32_word, arrLen]
  split <;> rfl

theorem evalOp_clampLen {p : Prog} {rt : LTy} {s : St} {x : Var} {a : UInt64}
    (hx : s.frame[x]? = some (.int a)) :
    (Backend2.evalOp (Backend2.tyIn p) .clampLen [x] rt).run s =
      .ok (.int (if a.toUInt32 < 0x80000000 then a &&& 0xFFFFFFFF else 0),
        { s with frame := s.frame.erase x }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  rfl

theorem evalOp_cntSucc {p : Prog} {rt : LTy} {s : St} {x : Var} {a : UInt64}
    (hx : s.frame[x]? = some (.int a)) :
    (Backend2.evalOp (Backend2.tyIn p) .cntSucc [x] rt).run s =
      .ok (.int ((a + 1) &&& 0xFFFFFFFF), { s with frame := s.frame.erase x }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  rfl

theorem evalOp_cntPred {p : Prog} {rt : LTy} {s : St} {x : Var} {a : UInt64}
    (hx : s.frame[x]? = some (.int a)) :
    (Backend2.evalOp (Backend2.tyIn p) .cntPred [x] rt).run s =
      .ok (.int ((a - 1) &&& 0xFFFFFFFF), { s with frame := s.frame.erase x }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  rfl

theorem evalOp_cntLt {p : Prog} {rt : LTy} {s : St} {x y : Var} {a b : UInt64}
    (hx : s.frame[x]? = some (.int a)) (hy : (s.frame.erase x)[y]? = some (.int b)) :
    (Backend2.evalOp (Backend2.tyIn p) .cntLt [x, y] rt).run s =
      .ok (.inj (decide (a.toUInt32 < b.toUInt32)) .unit,
        { s with frame := (s.frame.erase x).erase y }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_two_run hx hy]
  rfl

theorem evalOp_locAdd {p : Prog} {rt : LTy} {s : St} {x y : Var} {l : Nat} {i : UInt64}
    (hx : s.frame[x]? = some (.loc l)) (hy : (s.frame.erase x)[y]? = some (.int i)) :
    (Backend2.evalOp (Backend2.tyIn p) .locAdd [x, y] rt).run s =
      .ok (.loc (l + i.toNat), { s with frame := (s.frame.erase x).erase y }) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_two_run hx hy]
  rfl

/-- The state after `cellsNew`, its frame `F`. -/
def stFill (s : St) (F : Std.HashMap Var LV) (k : Nat) : St :=
  { s with frame := F, mem := (Backend2.fillCells s.mem s.objs s.next k).1,
           objs := (Backend2.fillCells s.mem s.objs s.next k).2, next := s.next + Backend2.regionSize }

theorem evalOp_cellsNew {p : Prog} {rt : LTy} {s : St} {x : Var} {a : UInt64}
    (hx : s.frame[x]? = some (.int a)) :
    (Backend2.evalOp (Backend2.tyIn p) .cellsNew [x] rt).run s =
      .ok (.loc s.next, stFill s (s.frame.erase x) (Backend2.lenOf a)) := by
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  rfl

/-! ### A callback's call -/

/-- **A call of a value on a value**, as the source runs it: a head step and its result's run,
or `store` applied. -/
theorem call_val {p : Prog} {N sz : Nat} (hrt : RT p N) (hcall : ∀ m, m < sz → CallAt p N m)
    {vf va : Val} {lf la : LV} {s : St} {c c' k : Nat} {μ μ' : Heap} {w : Val} (hk : k ≤ sz)
    (hb : BigN (ℍ := Backend2.lirHost) bumpAlloc k c μ (.app vf.1 va.1) c' μ' w)
    (hvf : VRel p N vf lf) (hva : VRel p N va la) (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f lf (some la) 0) s (.ok (lw, s')) := by
  rcases big_app_inv hb with
      ⟨i, j, k', c₁, μ₁, c₂, μ₂, c₃, μ₃, va', vf', r, hi, hj, hk', hba, hbf, hhd, hbr⟩ |
      ⟨i, j, c₁, μ₁, va', hi, hj, hba, hbf, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := big_val_inv hba va rfl
    subst c₁ μ₁ va'
    obtain ⟨h4, h5, h6⟩ := big_val_inv hbf vf rfl
    subst c₂ μ₂ vf'
    exact hcall k' (by omega) vf va lf la s c μ c₃ μ₃ r c' μ' w k' (le_refl _) hhd hbr hvf hva hh
  · obtain ⟨h1, h2, h3⟩ := big_val_inv hba va rfl
    subst c₁ μ₁ va'
    obtain ⟨h4, h5, hvs⟩ := big_val_inv hbf vf rfl
    subst c' μ' hvs
    obtain rfl := vrel_store_inv hvf
    exact ⟨_, s, .store1 hva, hh, rfl, call_store0 hrt la s⟩

theorem vrel_count_inv {p : Prog} {N : Nat} {f st : Val} {n i : UInt32} {lv : LV}
    (h : VRel p N (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) st))) lv) :
    ∃ lf ls, lv = .pair lf (.pair (.int n.toUInt64) (.pair (.int i.toUInt64) ls)) ∧
      VRel p N f lf ∧ VRel p N st ls := by
  obtain ⟨x, y, rfl, hx, hy⟩ := vrel_pair_inv h
  obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := vrel_pair_inv hy
  obtain ⟨z₁, z₂, rfl, hz₁, hz₂⟩ := vrel_pair_inv hy₂
  rw [vrel_i32_inv hy₁, vrel_i32_inv hz₁]
  exact ⟨x, z₂, rfl, hx, hz₂⟩

/-- A lookup in a frame written by inserts and erases. -/
macro "fr" : tactic =>
  `(tactic| simp +zetaDelta +decide only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase,
    Std.HashMap.getElem?_empty, beq_iff_eq, ite_true, ite_false, if_true, if_false,
    Bool.false_eq_true, reduceCtorEq] <;> try rfl)

/-- A frame written by inserts and erases holds nothing: every lookup is a chain of tests. -/
syntax "frx" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| frx [$ts,*]) =>
    `(tactic| (simp +zetaDelta only [$ts,*, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty, beq_iff_eq]; split_ifs <;>
      first | rfl | omega))

/-- `fr`, with the given equations. -/
syntax "frw" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| frw [$ts,*]) =>
    `(tactic| simp +zetaDelta +decide only [$ts,*, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty, beq_iff_eq, ite_true, ite_false,
      if_true, if_false, Bool.false_eq_true, reduceCtorEq, eraseL, List.foldl_cons,
      List.foldl_nil] <;> try rfl)

/-- The state with `x` bound to `v`. -/
abbrev stI (s : St) (x : Var) (v : LV) : St := { s with frame := s.frame.insert x v }

/-- The state with `x` consumed. -/
abbrev stE (s : St) (x : Var) : St := { s with frame := s.frame.erase x }

theorem sim_lp {p : Prog} {rt : LTy} {x y q : Var} {b : Tm} {va vc : LV} {s : St}
    {r : Except String (LV × St)} (hq : s.frame[q]? = some (.pair va vc))
    (hb : Sim (fun f => Backend2.eval p f rt b) (stI (stI (stE s q) x va) y vc) r) :
    Sim (fun f => Backend2.eval p f rt (.letpair x y q b)) s r := sim_letpair hq hb

theorem sim_lv {p : Prog} {rt : LTy} {x : Var} {e b : Tm} {s s₁ : St} {v : LV}
    {r : Except String (LV × St)} (hty : p.ty[x]? = some .unit)
    (he : Sim (fun f => Backend2.eval p f .unit e) s (.ok (v, s₁)))
    (hb : Sim (fun f => Backend2.eval p f rt b) (stI s₁ x v) r) :
    Sim (fun f => Backend2.eval p f rt (.letv x e b)) s r := sim_letv hty he hb

theorem sim_cp {p : Prog} {rt : LTy} {x x' : Var} {b : Tm} {v : LV} {s : St}
    {r : Except String (LV × St)} (hty : p.ty[x]? = some .unit) (hx : s.frame[x]? = some v)
    (hb : Sim (fun f => Backend2.eval p f rt b) (stI s x' v) r) :
    Sim (fun f => Backend2.eval p f rt (.copy x x' b)) s r := sim_copy hty hx hb

theorem sim_dr {p : Prog} {rt : LTy} {x : Var} {b : Tm} {v : LV} {s : St}
    {r : Except String (LV × St)} (hty : p.ty[x]? = some .unit) (hx : s.frame[x]? = some v)
    (hb : Sim (fun f => Backend2.eval p f rt b) (stE s x) r) :
    Sim (fun f => Backend2.eval p f rt (.drop x b)) s r := sim_drop hty hx hb

theorem sim_pr {p : Prog} {rt : LTy} {a b : Var} {va vb : LV} {s : St}
    (ha : s.frame[a]? = some va) (hb : (s.frame.erase a)[b]? = some vb) :
    Sim (fun f => Backend2.eval p f rt (.pair a b)) s (.ok (.pair va vb, stE (stE s a) b)) :=
  sim_pair ha hb

/-! ### `count` -/

section count
variable {p : Prog} {N : Nat} (hty : TyOK p N) (hN : rtBound ≤ N)
variable (s : St) (lf ls : LV) (n i : UInt32)

/-- `count`'s frame when it starts, on `(f, (n, (i, s)))`. -/
def cnt0 : St :=
  let a : LV := .pair lf (.pair (.int n.toUInt64) (.pair (.int i.toUInt64) ls))
  { s with frame := (∅ : Std.HashMap Var LV).insert 0 a }

/-- After the test: `i < len(n)` at `10`. -/
def cnt7 : St :=
  let A1 := stI (stI (stE (cnt0 s lf ls n i) 0) 1 lf) 2
    (.pair (.int n.toUInt64) (.pair (.int i.toUInt64) ls))
  let A2 := stI (stI (stE A1 2) 3 (.int n.toUInt64)) 4 (.pair (.int i.toUInt64) ls)
  let A3 := stI (stI (stE A2 4) 5 (.int i.toUInt64)) 6 ls
  let A4 := stI A3 7 (.int n.toUInt64)
  let A5 := stI (stE A4 7) 8 (.int (arrLen n).toUInt64)
  let A6 := stI A5 9 (.int i.toUInt64)
  stI (stE (stE A6 9) 8) 10 (.inj (decide (i < arrLen n)) .unit)

/-- `count`'s and `count_try`'s code up to its test, then the case on it. -/
def cntPrefix (A B : Tm) : Tm :=
  .letpair 1 2 0 (.letpair 3 4 2 (.letpair 5 6 4 (.copy 3 7 (.letv 8 (.prim .clampLen [7])
    (.copy 5 9 (.letv 10 (.prim .cntLt [9, 8]) (.case 10 11 A 12 B)))))))

include hty hN in
theorem cnt_pre {A B : Tm} {rt : LTy} {r' : Except String (LV × St)}
    (hrest : Sim (fun f => Backend2.eval p f rt (.case 10 11 A 12 B)) (cnt7 s lf ls n i) r') :
    Sim (fun f => Backend2.eval p f rt (cntPrefix A B)) (cnt0 s lf ls n i) r' := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  refine sim_lp (va := lf) (vc := .pair (.int n.toUInt64) (.pair (.int i.toUInt64) ls))
    (by simp only [cnt0]; fr) ?_
  refine sim_lp (va := .int n.toUInt64) (vc := .pair (.int i.toUInt64) ls) (by simp only [cnt0]; fr) ?_
  refine sim_lp (va := .int i.toUInt64) (vc := ls) (by simp only [cnt0]; fr) ?_
  refine sim_cp (v := .int n.toUInt64) (ht 3 (by decide)) (by simp only [cnt0]; fr) ?_
  refine sim_lv (ht 8 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
    (evalOp_clampLen (a := n.toUInt64) (by simp only [cnt0]; fr))) ?_
  rw [clamp_word]
  refine sim_cp (v := .int i.toUInt64) (ht 5 (by decide)) (by simp only [cnt0]; fr) ?_
  refine sim_lv (ht 10 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
    (evalOp_cntLt (a := i.toUInt64) (b := (arrLen n).toUInt64) (by simp only [cnt0]; fr)
      (by simp only [cnt0]; fr))) ?_
  simp only [UInt32.toUInt32_toUInt64]
  exact hrest

include hty hN in
theorem countB_pre {rt : LTy} {r' : Except String (LV × St)}
    (hrest : Sim (fun f => Backend2.eval p f rt (.case 10 11 (.drop 11 (.drop 1 (.drop 3 (.drop 5 (.var 6)))))
        12 (.drop 12 (.copy 1 13 (.copy 5 14 (.letv 15 (.pair 14 6) (.letv 16 (.app 13 15)
          (.letv 17 (.prim .cntSucc [5]) (.letv 18 (.pair 17 16) (.letv 19 (.pair 3 18)
            (.letv 20 (.pair 1 19) (.letv 21 (.clos 11 []) (.app 21 20)))))))))))))
        (cnt7 s lf ls n i) r') :
    Sim (fun f => Backend2.eval p f rt countB) (cnt0 s lf ls n i) r' :=
  cnt_pre hty hN s lf ls n i hrest

/-- Before the step's call, the step's function at `13` and argument at `15` taken. -/
def cntB : St :=
  let A11 := stI (stI (stE (stI (stE (cnt7 s lf ls n i) 10) 12 .unit) 12) 13 lf) 14 (.int i.toUInt64)
  let A12 := stI (stE (stE A11 14) 6) 15 (.pair (.int i.toUInt64) ls)
  stE (stE A12 13) 15

/-- Before the loop's call, from the state `s₁` after the step's, its value `lr`. -/
def cntC (s₁ : St) (lr : LV) : St :=
  let A13 := stI s₁ 16 lr
  let A14 := stI (stE A13 5) 17 (.int (i + 1).toUInt64)
  let A15 := stI (stE (stE A14 17) 16) 18 (.pair (.int (i + 1).toUInt64) lr)
  let A16 := stI (stE (stE A15 3) 18) 19 (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lr))
  let A17 := stI (stE (stE A16 1) 19) 20
    (.pair lf (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lr)))
  let A18 := stI A17 21 (.clos 11 [])
  stE (stE A18 21) 20

set_option maxHeartbeats 2000000 in
include hty hN in
theorem countB_go (hlt : i < arrLen n) {lr lw : LV} {s₁ s₃ : St}
    (hsim₁ : Sim (fun f => Backend2.callClos p f lf (some (.pair (.int i.toUInt64) ls)) 0)
      (cntB s lf ls n i) (.ok (lr, s₁)))
    (hfr₁ : s₁.frame = (cntB s lf ls n i).frame)
    (hsim₃ : Sim (fun f => Backend2.callClos p f (.clos 11 [])
      (some (.pair lf (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lr)))) 0)
      (cntC lf n i s₁ lr) (.ok (lw, s₃)))
    (hfr₃ : s₃.frame = (cntC lf n i s₁ lr).frame) :
    (∀ x : Nat, s₃.frame[x]? = none) ∧
      ∀ rt, Sim (fun f => Backend2.eval p f rt countB) (cnt0 s lf ls n i) (.ok (lw, s₃)) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  refine ⟨fun x => ?_, fun rt => countB_pre hty hN s lf ls n i ?_⟩
  · rw [hfr₃]
    simp only [cntC, stE]
    rw [hfr₁]
    simp only [cntB, cnt7, cnt0, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]
  have hd : decide (i < arrLen n) = true := by simp [hlt]
  refine sim_case_r (v := .unit) (by frw [cnt7, hd]) ?_
  refine sim_dr (v := .unit) (ht 12 (by decide)) (by frw [cnt7]) ?_
  refine sim_cp (v := lf) (ht 1 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_cp (v := .int i.toUInt64) (ht 5 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_lv (ht 15 (by decide)) (sim_pr (by frw [cnt7, cnt0]) (by frw [cnt7, cnt0])) ?_
  refine sim_lv (ht 16 (by decide)) (sim_app (by frw [cnt7, cnt0]) (by frw [cnt7, cnt0]) hsim₁) ?_
  refine sim_lv (ht 17 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
    (evalOp_cntSucc (a := i.toUInt64) (by frw [hfr₁, cntB, cnt7, cnt0]))) ?_
  rw [mask32_succ]
  refine sim_lv (ht 18 (by decide)) (sim_pr (by frw [hfr₁, cntB, cnt7, cnt0])
    (by frw [hfr₁, cntB, cnt7, cnt0])) ?_
  refine sim_lv (ht 19 (by decide)) (sim_pr (by frw [hfr₁, cntB, cnt7, cnt0])
    (by frw [hfr₁, cntB, cnt7, cnt0])) ?_
  refine sim_lv (ht 20 (by decide)) (sim_pr (by frw [hfr₁, cntB, cnt7, cnt0])
    (by frw [hfr₁, cntB, cnt7, cnt0])) ?_
  refine sim_lv (ht 21 (by decide)) sim_clos_nil ?_
  exact sim_app (by frw [hfr₁, cntB, cnt7, cnt0]) (by frw [hfr₁, cntB, cnt7, cnt0]) hsim₃

theorem cntB_heap : (cntB s lf ls n i).mem = s.mem ∧ (cntB s lf ls n i).objs = s.objs ∧
    (cntB s lf ls n i).next = s.next := by
  simp [cntB, cnt7, cnt0]

theorem cntC_heap (s₁ : St) (lr : LV) : (cntC lf n i s₁ lr).mem = s₁.mem ∧
    (cntC lf n i s₁ lr).objs = s₁.objs ∧ (cntC lf n i s₁ lr).next = s₁.next := by
  simp [cntC]

/-- After the loop's last turn. -/
def cntStop : St :=
  let A := stI (stE (cnt7 s lf ls n i) 10) 11 .unit
  stE (stE (stE (stE (stE A 11) 1) 3) 5) 6

theorem cntStop_heap : (cntStop s lf ls n i).mem = s.mem ∧ (cntStop s lf ls n i).objs = s.objs ∧
    (cntStop s lf ls n i).next = s.next := by
  simp [cntStop, cnt7, cnt0]

include hty hN in
theorem countB_stop (hge : ¬ i < arrLen n) :
    (∀ x : Nat, (cntStop s lf ls n i).frame[x]? = none) ∧
      ∀ rt, Sim (fun f => Backend2.eval p f rt countB) (cnt0 s lf ls n i)
        (.ok (ls, cntStop s lf ls n i)) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  refine ⟨fun x => ?_, fun rt => countB_pre hty hN s lf ls n i ?_⟩
  · simp only [cntStop, cnt7, cnt0, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]
  have hd : decide (i < arrLen n) = false := by simp [hge]
  refine sim_case_l (v := .unit) (by frw [cnt7, hd]) ?_
  refine sim_dr (v := .unit) (ht 11 (by decide)) (by frw [cnt7]) ?_
  refine sim_dr (v := lf) (ht 1 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_dr (v := .int n.toUInt64) (ht 3 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_dr (v := .int i.toUInt64) (ht 5 (by decide)) (by frw [cnt7, cnt0]) ?_
  exact sim_var (by frw [cnt7, cnt0])

/-! #### `count_try` -/

/-- `count_try`'s code, through `cntPrefix`. -/
theorem countTryB_eq : countTryB = cntPrefix (.drop 11 (.drop 1 (.drop 3 (.drop 5 (.inj false 6)))))
    (.drop 12 (.copy 1 13 (.copy 5 14 (.letv 15 (.pair 14 6) (.letv 16 (.app 13 15)
      (.case 16 17 (.letv 18 (.prim .cntSucc [5]) (.letv 19 (.pair 18 17)
          (.letv 20 (.pair 3 19) (.letv 21 (.pair 1 20) (.letv 22 (.clos 12 []) (.app 22 21))))))
        23 (.drop 1 (.drop 3 (.drop 5 (.inj true 23)))))))))) := rfl

/-- Before `count_try`'s next turn, from the state `s₁` after the step's call, its `inl` payload. -/
def ctC (s₁ : St) (lr : LV) : St :=
  let A := stI (stE (stI s₁ 16 (.inj false lr)) 16) 17 lr
  let A18 := stI (stE A 5) 18 (.int (i + 1).toUInt64)
  let A19 := stI (stE (stE A18 18) 17) 19 (.pair (.int (i + 1).toUInt64) lr)
  let A20 := stI (stE (stE A19 3) 19) 20 (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lr))
  let A21 := stI (stE (stE A20 1) 20) 21
    (.pair lf (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lr)))
  let A22 := stI A21 22 (.clos 12 [])
  stE (stE A22 22) 21

theorem ctC_heap (s₁ : St) (lr : LV) : (ctC lf n i s₁ lr).mem = s₁.mem ∧
    (ctC lf n i s₁ lr).objs = s₁.objs ∧ (ctC lf n i s₁ lr).next = s₁.next := by
  simp [ctC]

/-- After `count_try`'s step answered `inr e`. -/
def ctR (s₁ : St) (le : LV) : St :=
  let A := stI (stE (stI s₁ 16 (.inj true le)) 16) 23 le
  stE (stE (stE (stE A 1) 3) 5) 23

theorem ctR_heap (s₁ : St) (le : LV) : (ctR s₁ le).mem = s₁.mem ∧
    (ctR s₁ le).objs = s₁.objs ∧ (ctR s₁ le).next = s₁.next := by
  simp [ctR]

/-- After `count_try`'s last turn. -/
def ctStop : St :=
  let A := stI (stE (cnt7 s lf ls n i) 10) 11 .unit
  stE (stE (stE (stE (stE A 11) 1) 3) 5) 6

theorem ctStop_heap : (ctStop s lf ls n i).mem = s.mem ∧ (ctStop s lf ls n i).objs = s.objs ∧
    (ctStop s lf ls n i).next = s.next := by
  simp [ctStop, cnt7, cnt0]

/-- The test's branch into `count_try`'s turn, up to its step's value. -/
theorem ctry_call (hlt : i < arrLen n) {rt : LTy} {r' : Except String (LV × St)} {lr : LV} {s₁ : St}
    (hsim₁ : Sim (fun f => Backend2.callClos p f lf (some (.pair (.int i.toUInt64) ls)) 0)
      (cntB s lf ls n i) (.ok (lr, s₁)))
    (hrest : Sim (fun f => Backend2.eval p f rt
      (.case 16 17 (.letv 18 (.prim .cntSucc [5]) (.letv 19 (.pair 18 17)
          (.letv 20 (.pair 3 19) (.letv 21 (.pair 1 20) (.letv 22 (.clos 12 []) (.app 22 21))))))
        23 (.drop 1 (.drop 3 (.drop 5 (.inj true 23)))))) (stI s₁ 16 lr) r')
    (hty : TyOK p N) (hN : rtBound ≤ N) :
    Sim (fun f => Backend2.eval p f rt countTryB) (cnt0 s lf ls n i) r' := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  rw [countTryB_eq]
  refine cnt_pre hty hN s lf ls n i ?_
  have hd : decide (i < arrLen n) = true := by simp [hlt]
  refine sim_case_r (v := .unit) (by frw [cnt7, hd]) ?_
  refine sim_dr (v := .unit) (ht 12 (by decide)) (by frw [cnt7]) ?_
  refine sim_cp (v := lf) (ht 1 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_cp (v := .int i.toUInt64) (ht 5 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_lv (ht 15 (by decide)) (sim_pr (by frw [cnt7, cnt0]) (by frw [cnt7, cnt0])) ?_
  exact sim_lv (ht 16 (by decide)) (sim_app (by frw [cnt7, cnt0]) (by frw [cnt7, cnt0]) hsim₁) hrest

include hty hN in
theorem ctry_go_l {lr lw : LV} {s₁ s₃ : St} (hfr₁ : s₁.frame = (cntB s lf ls n i).frame)
    (hsim₃ : Sim (fun f => Backend2.callClos p f (.clos 12 [])
      (some (.pair lf (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lr)))) 0)
      (ctC lf n i s₁ lr) (.ok (lw, s₃)))
    (hfr₃ : s₃.frame = (ctC lf n i s₁ lr).frame) (rt : LTy) :
    (∀ x : Nat, s₃.frame[x]? = none) ∧
    Sim (fun f => Backend2.eval p f rt
      (.case 16 17 (.letv 18 (.prim .cntSucc [5]) (.letv 19 (.pair 18 17)
          (.letv 20 (.pair 3 19) (.letv 21 (.pair 1 20) (.letv 22 (.clos 12 []) (.app 22 21))))))
        23 (.drop 1 (.drop 3 (.drop 5 (.inj true 23)))))) (stI s₁ 16 (.inj false lr)) (.ok (lw, s₃)) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  refine ⟨fun x => ?_, ?_⟩
  · rw [hfr₃]
    simp only [ctC, stE]
    rw [hfr₁]
    simp only [cntB, cnt7, cnt0, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]
  refine sim_case_l (v := lr) (by fr) ?_
  refine sim_lv (ht 18 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
    (evalOp_cntSucc (a := i.toUInt64) (by frw [hfr₁, cntB, cnt7, cnt0]))) ?_
  rw [mask32_succ]
  refine sim_lv (ht 19 (by decide)) (sim_pr (by frw [hfr₁, cntB, cnt7, cnt0])
    (by frw [hfr₁, cntB, cnt7, cnt0])) ?_
  refine sim_lv (ht 20 (by decide)) (sim_pr (by frw [hfr₁, cntB, cnt7, cnt0])
    (by frw [hfr₁, cntB, cnt7, cnt0])) ?_
  refine sim_lv (ht 21 (by decide)) (sim_pr (by frw [hfr₁, cntB, cnt7, cnt0])
    (by frw [hfr₁, cntB, cnt7, cnt0])) ?_
  refine sim_lv (ht 22 (by decide)) sim_clos_nil ?_
  exact sim_app (by frw [hfr₁, cntB, cnt7, cnt0]) (by frw [hfr₁, cntB, cnt7, cnt0]) hsim₃

include hty hN in
theorem ctry_go_r {le : LV} {s₁ : St} (hfr₁ : s₁.frame = (cntB s lf ls n i).frame) (rt : LTy) :
    (∀ x : Nat, (ctR s₁ le).frame[x]? = none) ∧
    Sim (fun f => Backend2.eval p f rt
      (.case 16 17 (.letv 18 (.prim .cntSucc [5]) (.letv 19 (.pair 18 17)
          (.letv 20 (.pair 3 19) (.letv 21 (.pair 1 20) (.letv 22 (.clos 12 []) (.app 22 21))))))
        23 (.drop 1 (.drop 3 (.drop 5 (.inj true 23)))))) (stI s₁ 16 (.inj true le))
      (.ok (.inj true le, ctR s₁ le)) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  refine ⟨fun x => ?_, ?_⟩
  · simp only [ctR, stE]
    rw [hfr₁]
    simp only [cntB, cnt7, cnt0, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]
  refine sim_case_r (v := le) (by fr) ?_
  refine sim_dr (v := lf) (ht 1 (by decide)) (by frw [hfr₁, cntB, cnt7, cnt0]) ?_
  refine sim_dr (v := .int n.toUInt64) (ht 3 (by decide)) (by frw [hfr₁, cntB, cnt7, cnt0]) ?_
  refine sim_dr (v := .int i.toUInt64) (ht 5 (by decide)) (by frw [hfr₁, cntB, cnt7, cnt0]) ?_
  exact sim_inj (by frw [hfr₁, cntB, cnt7, cnt0])

include hty hN in
theorem ctry_stop (hge : ¬ i < arrLen n) :
    (∀ x : Nat, (ctStop s lf ls n i).frame[x]? = none) ∧
      ∀ rt, Sim (fun f => Backend2.eval p f rt countTryB) (cnt0 s lf ls n i)
        (.ok (.inj false ls, ctStop s lf ls n i)) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  refine ⟨fun x => ?_, fun rt => ?_⟩
  · simp only [ctStop, cnt7, cnt0, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]
  rw [countTryB_eq]
  refine cnt_pre hty hN s lf ls n i ?_
  have hd : decide (i < arrLen n) = false := by simp [hge]
  refine sim_case_l (v := .unit) (by frw [cnt7, hd]) ?_
  refine sim_dr (v := .unit) (ht 11 (by decide)) (by frw [cnt7]) ?_
  refine sim_dr (v := lf) (ht 1 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_dr (v := .int n.toUInt64) (ht 3 (by decide)) (by frw [cnt7, cnt0]) ?_
  refine sim_dr (v := .int i.toUInt64) (ht 5 (by decide)) (by frw [cnt7, cnt0]) ?_
  exact sim_inj (by frw [cnt7, cnt0])

end count

set_option maxHeartbeats 400000 in
theorem call_count {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m)
    {va : Val} {la : LV} {s : St} {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hk : k ≤ sz)
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .count).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 11 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨f, n, i, st, rfl, rfl, rfl⟩ := head_count_inv hd
  obtain ⟨lf, ls, rfl, hlf, hls⟩ := vrel_count_inv hva
  unfold countNext at hbr
  by_cases hlt : i < arrLen n
  · rw [if_pos hlt] at hbr
    rcases big_app_inv hbr with
        ⟨i₁, j₁, k₂, c₂, μ₂, c₃, μ₃, c₄, μ₄, va₂, vf₂, r₂, hi₁, hj₁, hk₂, hA, hF, hhd₂, hr₂⟩ |
        ⟨i₁, j₁, c₂, μ₂, va₂, hi₁, hj₁, hA, hF, -⟩
    swap
    · obtain ⟨-, -, he⟩ := big_val_inv hF (Val.prim .count) rfl
      exact absurd (congrArg Subtype.val he) (by simp [Val.prim])
    obtain ⟨h1, h2, h3⟩ := big_val_inv hF (Val.prim .count) rfl
    subst c₃ μ₃ vf₂
    obtain ⟨q₁, q₂, ca, μa, u₁, u₂, hq₁, hq₂, hf1, hrest, rfl⟩ := big_pair_inv hA
    obtain ⟨h4, h5, h6⟩ := big_val_inv hf1 f rfl
    subst ca μa u₁
    obtain ⟨q₃, q₄, cb, μb, u₃, u₄, hq₃, hq₄, hn1, hrest2, rfl⟩ := big_pair_inv hrest
    obtain ⟨h7, h8, h9⟩ := big_val_inv hn1 (Val.i32 n) rfl
    subst cb μb u₃
    obtain ⟨q₅, q₆, cd, μd, u₅, u₆, hq₅, hq₆, hi1, happ, rfl⟩ := big_pair_inv hrest2
    obtain ⟨h10, h11, h12⟩ := big_val_inv hi1 (Val.i32 (i + 1)) rfl
    subst cd μd u₅
    obtain ⟨lr₁, s₁, hlr₁, hh₁, hfr₁, hsim₁⟩ := call_val (k := _) (sz := sz) hrt hcall (by omega)
      happ hlf (.pair (.lit (.i32 i)) hls) (s := cntB s lf ls n i)
      (hh.congr (cntB_heap s lf ls n i).1 (cntB_heap s lf ls n i).2.1 (cntB_heap s lf ls n i).2.2)
    obtain ⟨lw, s₃, hlw, hh₃, hfr₃, hsim₃⟩ := hcall k₂ (by omega) (Val.prim .count) _ (.clos 11 [])
      (.pair lf (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lr₁)))
      (cntC lf n i s₁ lr₁) c₂ μ₂ c₄ μ₄ r₂ c' μ' w k₂ (le_refl _) hhd₂ hr₂ (.rt .count 11 rfl)
      (.pair hlf (.pair (.lit (.i32 n)) (.pair (.lit (.i32 (i + 1))) hlr₁)))
      (hh₁.congr (cntC_heap lf n i s₁ lr₁).1 (cntC_heap lf n i s₁ lr₁).2.1 (cntC_heap lf n i s₁ lr₁).2.2)
    obtain ⟨hemp, hsim⟩ := countB_go hty hN s lf ls n i hlt hsim₁ hfr₁ hsim₃ hfr₃
    exact ⟨lw, { s₃ with frame := s.frame }, hlw, hh₃.frame _, rfl, call1 hrt.count hsim hemp⟩
  · rw [if_neg hlt] at hbr
    obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbr st rfl
    obtain ⟨hemp, hsim⟩ := countB_stop hty hN s lf ls n i hlt
    exact ⟨ls, { cntStop s lf ls n i with frame := s.frame }, hls,
      hh.congr (cntStop_heap s lf ls n i).1 (cntStop_heap s lf ls n i).2.1
        (cntStop_heap s lf ls n i).2.2, rfl, call1 hrt.count hsim hemp⟩

set_option maxHeartbeats 400000 in
theorem call_countTry {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m)
    {va : Val} {la : LV} {s : St} {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hk : k ≤ sz)
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .countTry).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 12 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨f, n, i, st, rfl, rfl, rfl⟩ := head_countTry_inv hd
  obtain ⟨lf, ls, rfl, hlf, hls⟩ := vrel_count_inv hva
  unfold countTryNext at hbr
  by_cases hlt : i < arrLen n
  · rw [if_pos hlt] at hbr
    have hB := cntB_heap s lf ls n i
    rcases big_case_inv hbr with ⟨i₁, j₁, c₂, μ₂, v, hi₁, hj₁, hsc, harm⟩ |
        ⟨i₁, j₁, c₂, μ₂, v, hi₁, hj₁, hsc, harm⟩
    · obtain ⟨lr₁, s₁, hlr₁, hh₁, hfr₁, hsim₁⟩ := call_val (k := _) (sz := sz) hrt hcall (by omega)
        hsc hlf (.pair (.lit (.i32 i)) hls) (s := cntB s lf ls n i) (hh.congr hB.1 hB.2.1 hB.2.2)
      obtain ⟨lv, rfl, hlv⟩ := vrel_inj₁_inv hlr₁
      rw [countTry_cont_subst] at harm
      rcases big_app_inv harm with
          ⟨i₂, j₂, k₂, c₃, μ₃, c₄, μ₄, c₅, μ₅, va₂, vf₂, r₂, hi₂, hj₂, hk₂, hA, hF, hhd₂, hr₂⟩ |
          ⟨i₂, j₂, c₃, μ₃, va₂, hi₂, hj₂, hA, hF, -⟩
      swap
      · obtain ⟨-, -, he⟩ := big_val_inv hF (Val.prim .countTry) rfl
        exact absurd (congrArg Subtype.val he) (by simp [Val.prim])
      obtain ⟨h1, h2, h3⟩ := big_val_inv hA _ rfl
      subst c₃ μ₃ va₂
      obtain ⟨h4, h5, h6⟩ := big_val_inv hF (Val.prim .countTry) rfl
      subst c₄ μ₄ vf₂
      have hC := ctC_heap lf n i s₁ lv
      obtain ⟨lw, s₃, hlw, hh₃, hfr₃, hsim₃⟩ := hcall k₂ (by omega) (Val.prim .countTry) _
        (.clos 12 []) (.pair lf (.pair (.int n.toUInt64) (.pair (.int (i + 1).toUInt64) lv)))
        (ctC lf n i s₁ lv) c₂ μ₂ c₅ μ₅ r₂ c' μ' w k₂ (le_refl _) hhd₂ hr₂ (.rt .countTry 12 rfl)
        (.pair hlf (.pair (.lit (.i32 n)) (.pair (.lit (.i32 (i + 1))) hlv)))
        (hh₁.congr hC.1 hC.2.1 hC.2.2)
      have hemp := (ctry_go_l hty hN s lf ls n i hfr₁ hsim₃ hfr₃ LTy.unit).1
      exact ⟨lw, { s₃ with frame := s.frame }, hlw, hh₃.frame _, rfl,
        call1 hrt.countTry (fun rt => ctry_call s lf ls n i hlt hsim₁
          (ctry_go_l hty hN s lf ls n i hfr₁ hsim₃ hfr₃ rt).2 hty hN) hemp⟩
    · obtain ⟨lr₁, s₁, hlr₁, hh₁, hfr₁, hsim₁⟩ := call_val (k := _) (sz := sz) hrt hcall (by omega)
        hsc hlf (.pair (.lit (.i32 i)) hls) (s := cntB s lf ls n i) (hh.congr hB.1 hB.2.1 hB.2.2)
      obtain ⟨le, rfl, hle⟩ := vrel_inj₂_inv hlr₁
      simp only [Expr.subst, if_pos] at harm
      obtain ⟨i₃, u, -, harm', rfl⟩ := big_inj₂_inv harm
      obtain ⟨h1, h2, h3⟩ := big_val_inv harm' v rfl
      subst c' μ' u
      have hR := ctR_heap s₁ le
      exact ⟨.inj true le, { ctR s₁ le with frame := s.frame }, .inj₂ hle,
        hh₁.congr hR.1 hR.2.1 hR.2.2, rfl,
        call1 hrt.countTry (fun rt => ctry_call s lf ls n i hlt hsim₁
          (ctry_go_r hty hN s lf ls n i hfr₁ rt).2 hty hN)
          (ctry_go_r hty hN s lf ls n i (le := le) hfr₁ LTy.unit).1⟩
  · rw [if_neg hlt] at hbr
    obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hbr (Val.inj₁ st) rfl
    obtain ⟨hemp, hsim⟩ := ctry_stop hty hN s lf ls n i hlt
    have hS := ctStop_heap s lf ls n i
    exact ⟨.inj false ls, { ctStop s lf ls n i with frame := s.frame }, .inj₁ hls,
      hh.congr hS.1 hS.2.1 hS.2.2, rfl, call1 hrt.countTry hsim hemp⟩

/-! ### `bounded_fix` -/

theorem capt_fixBody : capt fixBody = [0, 1] := rfl

theorem fixSelf_ne {sv : Val} {k : UInt32} (hk : k ≠ 0) :
    fixSelf sv k = Val.inj₂ (Val.lam (Expr.psub 1 [sv, Val.i32 (k - 1)] fixBody)) := by
  simp only [fixSelf, if_neg hk]
  rfl

theorem vrel_bf_inv {p : Prog} {N : Nat} {sv a : Val} {k : UInt32} {lv : LV}
    (h : VRel p N (Val.pair sv (Val.pair (Val.i32 k) a)) lv) :
    ∃ ls la, lv = .pair ls (.pair (.int k.toUInt64) la) ∧ VRel p N sv ls ∧ VRel p N a la := by
  obtain ⟨x, y, rfl, hx, hy⟩ := vrel_pair_inv h
  obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := vrel_pair_inv hy
  rw [vrel_i32_inv hy₁]
  exact ⟨x, y₂, rfl, hx, hy₂⟩

/-- `bounded_fix`'s frame after its test, the budget `k`. -/
def bf7 (s : St) (ls la : LV) (k : UInt32) : St :=
  let a : LV := .pair ls (.pair (.int k.toUInt64) la)
  let A0 : St := { s with frame := (∅ : Std.HashMap Var LV).insert 0 a }
  let A1 := stI (stI (stE A0 0) 1 ls) 2 (.pair (.int k.toUInt64) la)
  let A2 := stI (stI (stE A1 2) 3 (.int k.toUInt64)) 4 la
  let A5 := stI A2 5 (.int 0)
  let A6 := stI A5 6 (.int k.toUInt64)
  stI (stE (stE A6 5) 6) 7 (.inj (decide ((0 : UInt64).toUInt32 < k.toUInt64.toUInt32)) .unit)

/-- At the call of the step: at `k = 0`, its function at `1` and argument at `11` taken. -/
def bfZ (s : St) (ls la : LV) (k : UInt32) : St :=
  let A := stI (stE (stE (stI (stE (bf7 s ls la k) 7) 8 .unit) 8) 3) 9 .unit
  let A10 := stI (stE A 9) 10 (.inj false .unit)
  let A11 := stI (stE (stE A10 10) 4) 11 (.pair (.inj false .unit) la)
  stE (stE A11 1) 11

/-- At the call of the step: at `k ≠ 0`, its function at `1` and argument at `17` taken. -/
def bfS (s : St) (ls la : LV) (k : UInt32) : St :=
  let A := stI (stE (stI (stE (bf7 s ls la k) 7) 12 .unit) 12) 13 ls
  let A14 := stI (stE A 3) 14 (.int (k - 1).toUInt64)
  let A15 := stI (stE (stE A14 13) 14) 15 (.clos fixSelfCode [ls, .int (k - 1).toUInt64])
  let A16 := stI (stE A15 15) 16 (.inj true (.clos fixSelfCode [ls, .int (k - 1).toUInt64]))
  let A17 := stI (stE (stE A16 16) 4) 17
    (.pair (.inj true (.clos fixSelfCode [ls, .int (k - 1).toUInt64])) la)
  stE (stE A17 1) 17

theorem bf_frames (s : St) (ls la : LV) (k : UInt32) :
    (∀ x : Nat, (bfZ s ls la k).frame[x]? = none) ∧ (∀ x : Nat, (bfS s ls la k).frame[x]? = none) ∧
    (bfZ s ls la k).mem = s.mem ∧ (bfZ s ls la k).objs = s.objs ∧ (bfZ s ls la k).next = s.next ∧
    (bfS s ls la k).mem = s.mem ∧ (bfS s ls la k).objs = s.objs ∧ (bfS s ls la k).next = s.next := by
  refine ⟨fun x => ?_, fun x => ?_, by simp [bfZ, bf7], by simp [bfZ, bf7], by simp [bfZ, bf7],
    by simp [bfS, bf7], by simp [bfS, bf7], by simp [bfS, bf7]⟩
  · simp only [bfZ, bf7, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]
  · simp only [bfS, bf7, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]

theorem bf_run {p : Prog} {N : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (s : St) (ls la : LV)
    (k : UInt32) {lw : LV} {s' : St} {rt : LTy}
    (hz : k = 0 → Sim (fun f => Backend2.callClos p f ls (some (.pair (.inj false .unit) la)) 0)
      (bfZ s ls la k) (.ok (lw, s')))
    (hs : k ≠ 0 → Sim (fun f => Backend2.callClos p f ls
      (some (.pair (.inj true (.clos fixSelfCode [ls, .int (k - 1).toUInt64])) la)) 0)
      (bfS s ls la k) (.ok (lw, s'))) :
    Sim (fun f => Backend2.eval p f rt boundedFixB)
      { s with frame := (∅ : Std.HashMap Var LV).insert 0 (.pair ls (.pair (.int k.toUInt64) la)) }
      (.ok (lw, s')) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  refine sim_lp (va := ls) (vc := .pair (.int k.toUInt64) la) (by fr) ?_
  refine sim_lp (va := .int k.toUInt64) (vc := la) (by fr) ?_
  refine sim_lv (ht 5 (by decide)) (sim_lit (.i32 0)) ?_
  refine sim_cp (v := .int k.toUInt64) (ht 3 (by decide)) (by fr) ?_
  refine sim_lv (ht 7 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
    (evalOp_cntLt (a := 0) (b := k.toUInt64) (by fr) (by fr))) ?_
  by_cases hk : k = 0
  · subst hk
    refine sim_case_l (v := .unit) (by frw [bf7]) ?_
    refine sim_dr (v := .unit) (ht 8 (by decide)) (by frw [bf7]) ?_
    refine sim_dr (v := .int (0 : UInt32).toUInt64) (ht 3 (by decide)) (by frw [bf7]) ?_
    refine sim_lv (ht 9 (by decide)) sim_unit ?_
    refine sim_lv (ht 10 (by decide)) (sim_inj (by frw [bf7])) ?_
    refine sim_lv (ht 11 (by decide)) (sim_pr (by frw [bf7]) (by frw [bf7])) ?_
    exact sim_app (by frw [bf7]) (by frw [bf7]) (hz rfl)
  · have hd : decide ((0 : UInt64).toUInt32 < k.toUInt64.toUInt32) = true := by
      simp only [UInt32.toUInt32_toUInt64, decide_eq_true_eq]
      exact UInt32.pos_iff_ne_zero.mpr hk
    refine sim_case_r (v := .unit) (by frw [bf7, hd]) ?_
    refine sim_dr (v := .unit) (ht 12 (by decide)) (by frw [bf7]) ?_
    refine sim_cp (v := ls) (ht 1 (by decide)) (by frw [bf7]) ?_
    refine sim_lv (ht 14 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
      (evalOp_cntPred (a := k.toUInt64) (by frw [bf7]))) ?_
    rw [mask32_pred]
    refine sim_lv (ht 15 (by decide)) (sim_clos (takeAll_two_run (by frw [bf7]) (by frw [bf7]))) ?_
    refine sim_lv (ht 16 (by decide)) (sim_inj (by frw [bf7])) ?_
    refine sim_lv (ht 17 (by decide)) (sim_pr (by frw [bf7]) (by frw [bf7])) ?_
    exact sim_app (by frw [bf7]) (by frw [bf7]) (hs hk)

theorem call_bf {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m)
    {va : Val} {la : LV} {s : St} {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hk : k ≤ sz)
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .boundedFix).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 13 []) (some la) 0) s (.ok (lw, s')) := by
  obtain ⟨rfl, hd⟩ := ahead_det hhd rfl
  obtain ⟨sv, kk, a, rfl, rfl, rfl⟩ := head_bf_inv hd
  obtain ⟨ls, la', rfl, hls, hla⟩ := vrel_bf_inv hva
  unfold boundedFixNext at hbr
  obtain ⟨hZ, hS, hZm, hZo, hZn, hSm, hSo, hSn⟩ := bf_frames s ls la' kk
  by_cases hk0 : kk = 0
  · subst hk0
    have h0 : fixSelf sv 0 = Val.inj₁ Val.unit := rfl
    rw [h0] at hbr
    obtain ⟨lw, s', hlw, hh', hfr', hsim'⟩ := call_val (sz := sz) hrt hcall hk hbr hls
      (.pair (.inj₁ .unit) hla) (s := bfZ s ls la' 0) (hh.congr hZm hZo hZn)
    exact ⟨lw, { s' with frame := s.frame }, hlw, hh'.frame _, rfl,
      call1 hrt.boundedFix (fun rt => bf_run hty hN s ls la' 0 (fun _ => hsim')
        (fun h => absurd rfl h)) (by rw [hfr']; exact hZ)⟩
  · rw [fixSelf_ne hk0] at hbr
    obtain ⟨tb, m, hpr, hm, hcode⟩ := hrt.fixSelf
    have hvl : VRel p N (Val.lam (Expr.psub 1 [sv, Val.i32 (kk - 1)] fixBody))
        (.clos fixSelfCode [ls, .int (kk - 1).toUInt64]) := by
      refine .lam hpr hm hcode (by simp [capt_fixBody]) (fun j hj => ?_) (fun i hi j hj hij => ?_)
      · rw [capt_fixBody] at hj; simp at hj; simp; omega
      · rw [capt_fixBody] at hij
        rcases i with _ | _ | i
        · simp at hij; subst hij; exact hls
        · simp at hij; subst hij; exact .lit (.i32 _)
        · simp at hi
    obtain ⟨lw, s', hlw, hh', hfr', hsim'⟩ := call_val (sz := sz) hrt hcall hk hbr hls
      (.pair (.inj₂ hvl) hla) (s := bfS s ls la' kk) (hh.congr hSm hSo hSn)
    exact ⟨lw, { s' with frame := s.frame }, hlw, hh'.frame _, rfl,
      call1 hrt.boundedFix (fun rt => bf_run hty hN s ls la' kk (fun h => absurd h hk0)
        (fun _ => hsim')) (by rw [hfr']; exact hS)⟩

/-! ### `drop` -/

/-- `dropLoop`'s frame when it starts, on `(f, ℓ, i, k)`. -/
def dl0 (s : St) (lf : LV) (ℓ i k : Nat) : St :=
  let F := ((((∅ : Std.HashMap Var LV).insert 0 lf).insert 1 (.loc ℓ)).insert 2
    (.int (UInt32.ofNat i).toUInt64)).insert 3 (.int (UInt32.ofNat k).toUInt64)
  { s with frame := F }

theorem zip4 (a b c d : LV) :
    (((List.range (3 + 1)).zip [a, b, c, d]).foldl (fun m x => m.insert x.1 x.2)
      (∅ : Std.HashMap Var LV)) = ((((∅ : Std.HashMap Var LV).insert 0 a).insert 1 b).insert 2 c).insert 3 d :=
  rfl

/-- After `dropLoop`'s test. -/
def dl6 (s : St) (lf : LV) (ℓ i k : Nat) : St :=
  let A4 := stI (dl0 s lf ℓ i k) 4 (.int 0)
  let A5 := stI A4 5 (.int (UInt32.ofNat k).toUInt64)
  stI (stE (stE A5 4) 5) 6 (.inj (decide ((0 : UInt64).toUInt32 <
    (UInt32.ofNat k).toUInt64.toUInt32)) .unit)

/-- At the cell's free: its address at `12`. -/
def dlF (s : St) (lf : LV) (ℓ i k : Nat) : St :=
  let A := stI (stE (stI (stE (dl6 s lf ℓ i k) 6) 8 .unit) 8) 9 lf
  let A10 := stI A 10 (.loc ℓ)
  let A11 := stI A10 11 (.int (UInt32.ofNat i).toUInt64)
  stI (stE (stE A11 10) 11) 12 (.loc (ℓ + i))

/-- Before the callback's call on the cell's contents `v`, the cell freed. -/
def dlB (s : St) (lf : LV) (ℓ i k : Nat) (v : LV) : St :=
  let A := stFree (dlF s lf ℓ i k) ((dlF s lf ℓ i k).frame.erase 12) (ℓ + i)
  stE (stE (stI A 13 v) 9) 13

/-- Before the loop's next turn, from the state `s₁` after the callback's call, its value `r`:
the arguments taken. -/
def dlC (s₁ : St) (r : LV) (i k : Nat) : St :=
  let T := stE (stI s₁ 14 r) 14
  let T15 := stI (stE T 2) 15 (.int (UInt32.ofNat i + 1).toUInt64)
  let T16 := stI (stE T15 3) 16 (.int (UInt32.ofNat k - 1).toUInt64)
  stE (stE (stE (stE T16 0) 1) 15) 16

theorem ofNat_succ32 (i : Nat) : UInt32.ofNat i + 1 = UInt32.ofNat (i + 1) := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_add, UInt32.toNat_ofNat]

theorem ofNat_pred32 (k : Nat) : UInt32.ofNat (k + 1) - 1 = UInt32.ofNat k := by
  rw [← ofNat_succ32]; simp

theorem dl_frames (s : St) (lf : LV) (ℓ i k : Nat) (v : LV) (s₁ : St) (r : LV)
    (hfr₁ : s₁.frame = (dlB s lf ℓ i k v).frame) :
    (∀ x : Nat, (dlC s₁ r i k).frame[x]? = none) := by
  intro x
  simp only [dlC, stE]
  rw [hfr₁]
  simp only [dlB, dlF, dl6, dl0, stI, stE, stFree]
  simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
    beq_iff_eq]
  rcases Nat.lt_or_ge x 24 with hx | hx
  · interval_cases x <;> simp
  · simp (disch := omega) only [if_neg]

theorem dl_heaps (s : St) (lf : LV) (ℓ i k : Nat) (v : LV) (s₁ : St) (r : LV) :
    ((dlF s lf ℓ i k).mem = s.mem ∧ (dlF s lf ℓ i k).objs = s.objs ∧
      (dlF s lf ℓ i k).next = s.next) ∧
    ((dlB s lf ℓ i k v).mem = (stFree s s.frame (ℓ + i)).mem ∧
      (dlB s lf ℓ i k v).objs = (stFree s s.frame (ℓ + i)).objs ∧
      (dlB s lf ℓ i k v).next = (stFree s s.frame (ℓ + i)).next) ∧
    ((dlC s₁ r i k).mem = s₁.mem ∧ (dlC s₁ r i k).objs = s₁.objs ∧ (dlC s₁ r i k).next = s₁.next) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp [dlF, dlB, dlC, dl6, dl0, stFree]

theorem lt32 {i : Nat} (h : i < 2 ^ 32) : (UInt32.ofNat i).toUInt64.toNat = i := by
  simp; omega

theorem dl_stop_frames (s : St) (lf : LV) (ℓ i : Nat) :
    ∀ x : Nat, (stE (stE (stE (stE (stE (stI (stE (dl6 s lf ℓ i 0) 6) 7 .unit) 7) 0) 1) 2) 3).frame[x]?
      = none := by
  intro x
  simp only [dl6, dl0, stI]
  simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
    beq_iff_eq]
  rcases Nat.lt_or_ge x 24 with hx | hx
  · interval_cases x <;> simp
  · simp (disch := omega) only [if_neg]

/-- **`dropLoop`**: the cells `ℓ + i, …, ℓ + i + k − 1` freed in order, each one's contents handed
to the callback, as `dropFill` runs. -/
theorem dropLoop_sim {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m) {f : Val} {lf : LV} (hlf : VRel p N f lf) (ℓ : Nat) :
    ∀ (k i : Nat), i + k < 2 ^ 32 → ∀ (s : St) (c c' : Nat) (μ μ' : Heap) (w : Val) (q : Nat),
      q ≤ sz → BigN (ℍ := Backend2.lirHost) bumpAlloc q c μ (dropFill f ℓ i k) c' μ' w →
      HRel p N c μ s →
      w = Val.unit ∧ ∃ s', HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
        Sim (fun g => Backend2.callFn p g dropLoopCode
          [lf, .loc ℓ, .int (UInt32.ofNat i).toUInt64, .int (UInt32.ofNat k).toUInt64]) s
          (.ok (.unit, s')) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  intro k
  induction k with
  | zero =>
      intro i hik s c c' μ μ' w q hq hb hh
      obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hb Val.unit rfl
      let E := stE (stE (stE (stE (stE (stI (stE (dl6 s lf ℓ i 0) 6) 7 .unit) 7) 0) 1) 2) 3
      have hE : E.mem = s.mem ∧ E.objs = s.objs ∧ E.next = s.next := by simp [E, dl6, dl0]
      refine ⟨rfl, { E with frame := s.frame }, hh.congr hE.1 hE.2.1 hE.2.2, rfl,
        sim_code (s' := E) hrt.dropLoop rfl (fun rt => ?_) (dl_stop_frames s lf ℓ i)⟩
      rw [zip4]
      refine sim_lv (ht 4 (by decide)) (sim_lit (.i32 0)) ?_
      refine sim_cp (v := .int (UInt32.ofNat 0).toUInt64) (ht 3 (by decide)) (by fr) ?_
      refine sim_lv (ht 6 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntLt (a := 0) (b := (UInt32.ofNat 0).toUInt64) (by fr) (by fr))) ?_
      refine sim_case_l (v := .unit) (by frw [dl6, dl0]) ?_
      refine sim_dr (v := .unit) (ht 7 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_dr (v := lf) (ht 0 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_dr (v := .loc ℓ) (ht 1 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_dr (v := .int (UInt32.ofNat i).toUInt64) (ht 2 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_dr (v := .int (UInt32.ofNat 0).toUInt64) (ht 3 (by decide)) (by frw [dl6, dl0]) ?_
      exact sim_unit
  | succ k ih =>
      intro i hik s c c' μ μ' w q hq hb hh
      simp only [dropFill] at hb
      obtain ⟨q₁, q₂, c₁, μ₁, hq₁, hq₂, hfirst, hrest⟩ := big_seq_inv hb
      rcases big_app_inv hfirst with
          ⟨i₁, j₁, k₁, c₂, μ₂, c₃, μ₃, c₄, μ₄, va, vf, r, hi₁, hj₁, hk₁, hA, hF, hhd, hr⟩ |
          ⟨i₁, j₁, c₂, μ₂, va, hi₁, hj₁, hA, hF, he⟩
      swap
      · exact absurd (congrArg Subtype.val he) (by simp [Val.storeV, Val.unit])
      obtain ⟨h1, h2, h3⟩ := big_val_inv hF f rfl
      subst c₃ μ₃ vf
      -- the free of the cell `ℓ + i`
      rcases big_app_inv hA with
          ⟨i₂, j₂, k₂, c₅, μ₅, c₆, μ₆, c₇, μ₇, va₂, vf₂, r₂, hi₂, hj₂, hk₂, hA₂, hF₂, hhd₂, hr₂⟩ |
          ⟨i₂, j₂, c₅, μ₅, va₂, hi₂, hj₂, hA₂, hF₂, -⟩
      swap
      · obtain ⟨-, -, he⟩ := big_val_inv hF₂ (Val.prim .free) rfl
        exact absurd (congrArg Subtype.val he) (by simp [Val.prim])
      obtain ⟨h4, h5, h6⟩ := big_val_inv hA₂ (Val.loc (ℓ + i)) rfl
      subst c₅ μ₅ va₂
      obtain ⟨h7, h8, h9⟩ := big_val_inv hF₂ (Val.prim .free) rfl
      subst c₆ μ₆ vf₂
      obtain ⟨hc7, hd₂⟩ := ahead_det hhd₂ rfl
      subst c₇
      obtain ⟨ℓ', v, hℓ, hv, rfl, rfl⟩ := head_free_inv hd₂
      obtain rfl : ℓ' = ℓ + i := (Val.loc_inj.mp hℓ).symm
      obtain ⟨h10, h11, h12⟩ := big_val_inv hr₂ v rfl
      subst c₂ μ₂ va
      obtain ⟨lv, hlv, hrel⟩ := hh.val (ℓ + i) v hv
      obtain ⟨⟨hFm, hFo, hFn⟩, ⟨hBm, hBo, hBn⟩, -⟩ := dl_heaps s lf ℓ i (k + 1) lv s .unit
      have hhF : HRel p N c (μ.del (ℓ + i)) (dlB s lf ℓ i (k + 1) lv) :=
        (hh.free s.frame).congr hBm hBo hBn
      obtain ⟨lw, s₁, hlw, hh₁, hfr₁, hsim₁⟩ := hcall k₁ (by omega) f v lf lv _ c (μ.del (ℓ + i))
        c₄ μ₄ r c₁ μ₁ Val.unit k₁ (le_refl _) hhd hr hlf hrel hhF
      obtain rfl := vrel_unit_inv hlw
      obtain ⟨-, -, ⟨hCm, hCo, hCn⟩⟩ := dl_heaps s lf ℓ i (k + 1) lv s₁ .unit
      obtain ⟨rfl, s', hh', hfr', hsim'⟩ := ih (i + 1) (by omega) (dlC s₁ .unit i (k + 1)) c₁ c' μ₁ μ'
        w q₂ (by omega) hrest (hh₁.congr hCm hCo hCn)
      refine ⟨rfl, { s' with frame := s.frame }, hh'.frame _, rfl, sim_code hrt.dropLoop rfl
        (fun rt => ?_) (by rw [hfr']; exact dl_frames s lf ℓ i (k + 1) lv s₁ .unit hfr₁)⟩
      rw [zip4]
      refine sim_lv (ht 4 (by decide)) (sim_lit (.i32 0)) ?_
      refine sim_cp (v := .int (UInt32.ofNat (k + 1)).toUInt64) (ht 3 (by decide)) (by fr) ?_
      refine sim_lv (ht 6 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntLt (a := 0) (b := (UInt32.ofNat (k + 1)).toUInt64) (by fr) (by fr))) ?_
      have hd : decide ((0 : UInt64).toUInt32 < (UInt32.ofNat (k + 1)).toUInt64.toUInt32) = true := by
        simp only [UInt32.toUInt32_toUInt64, decide_eq_true_eq]
        apply UInt32.lt_iff_toNat_lt.mpr
        simp; omega
      refine sim_case_r (v := .unit) (by frw [dl6, dl0, hd]) ?_
      refine sim_dr (v := .unit) (ht 8 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_cp (v := lf) (ht 0 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_cp (v := .loc ℓ) (ht 1 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_cp (v := .int (UInt32.ofNat i).toUInt64) (ht 2 (by decide)) (by frw [dl6, dl0]) ?_
      refine sim_lv (ht 12 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_locAdd (l := ℓ) (i := (UInt32.ofNat i).toUInt64) (by frw [dl6, dl0])
          (by frw [dl6, dl0]))) ?_
      rw [lt32 (by omega)]
      refine sim_lv (ht 13 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cellFree (a := ℓ + i) (by frw [dl6, dl0]) (by exact hlv))) ?_
      refine sim_lv (ht 14 (by decide)) (sim_app (by frw [dlF, dl6, dl0, stFree])
        (by frw [dlF, dl6, dl0, stFree]) hsim₁) ?_
      refine sim_dr (v := .unit) (ht 14 (by decide)) (by fr) ?_
      refine sim_lv (ht 15 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntSucc (a := (UInt32.ofNat i).toUInt64) (by frw [hfr₁, dlB, dlF, dl6, dl0, stFree]))) ?_
      rw [mask32_succ]
      refine sim_lv (ht 16 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntPred (a := (UInt32.ofNat (k + 1)).toUInt64)
          (by frw [hfr₁, dlB, dlF, dl6, dl0, stFree]))) ?_
      rw [mask32_pred]
      refine sim_call (takeAll_cons_run (by frw [hfr₁, dlB, dlF, dl6, dl0, stFree])
        (takeAll_cons_run (by frw [hfr₁, dlB, dlF, dl6, dl0, stFree])
          (takeAll_cons_run (by frw [hfr₁, dlB, dlF, dl6, dl0, stFree])
            (takeAll_one_run (by frw [hfr₁, dlB, dlF, dl6, dl0, stFree]))))) ?_
      have hsim'' : Sim (fun g => Backend2.callFn p g dropLoopCode
          [lf, .loc ℓ, .int (UInt32.ofNat i + 1).toUInt64, .int (UInt32.ofNat (k + 1) - 1).toUInt64])
          (dlC s₁ .unit i (k + 1)) (.ok (.unit, s')) := by
        rw [ofNat_succ32, ofNat_pred32]; exact hsim'
      exact hsim''

theorem vrel_drop_inv {p : Prog} {N : Nat} {f : Val} {ℓ : Loc} {n : UInt32} {lv : LV}
    (h : VRel p N (Val.pair f (Val.arr ℓ n)) lv) :
    ∃ lf, lv = .pair lf (.pair (.loc ℓ) (.int n.toUInt64)) ∧ VRel p N f lf := by
  obtain ⟨x, y, rfl, hx, hy⟩ := vrel_pair_inv h
  obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := vrel_pair_inv hy
  rw [vrel_loc_inv hy₁, vrel_i32_inv hy₂]
  exact ⟨x, rfl, hx⟩

theorem call_drop {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m)
    {va : Val} {la : LV} {s : St} {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hk : k ≤ sz)
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .drop).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 9 []) (some la) 0) s (.ok (lw, s')) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  obtain ⟨hc, hd⟩ := ahead_det hhd rfl
  subst c₁
  obtain ⟨f, ℓ, n, rfl, rfl, rfl⟩ := head_drop_inv hd
  obtain ⟨lf, rfl, hlf⟩ := vrel_drop_inv hva
  let a₀ : LV := .pair lf (.pair (.loc ℓ) (.int n.toUInt64))
  let S0 : St := { s with frame := (∅ : Std.HashMap Var LV).insert 0 a₀ }
  let A1 := stI (stI (stE S0 0) 1 lf) 2 (.pair (.loc ℓ) (.int n.toUInt64))
  let A2 := stI (stI (stE A1 2) 3 (.loc ℓ)) 4 (.int n.toUInt64)
  let A3 := stI A2 5 (Backend2.litV (.i32 0))
  let s₀ : St := stE (stE (stE (stE A3 1) 3) 5) 4
  have hs₀ : s₀.mem = s.mem ∧ s₀.objs = s.objs ∧ s₀.next = s.next := by simp [s₀, A3, A2, A1, S0]
  obtain ⟨rfl, s', hh', hfr', hsim'⟩ := dropLoop_sim hty hN hrt hcall hlf ℓ n.toNat 0
    (by have := n.toNat_lt; omega) s₀ c c' μ₁ μ' w k hk hbr (hh.congr hs₀.1 hs₀.2.1 hs₀.2.2)
  refine ⟨.unit, { s' with frame := s.frame }, .unit, hh'.frame _, rfl,
    call1 (s₁ := s') hrt.drop (fun rt => ?_) (fun x => ?_)⟩
  · refine sim_lp (va := lf) (vc := .pair (.loc ℓ) (.int n.toUInt64)) (by fr) ?_
    refine sim_lp (va := .loc ℓ) (vc := .int n.toUInt64) (by fr) ?_
    refine sim_lv (ht 5 (by decide)) (sim_lit (.i32 0)) ?_
    have e2 : UInt32.ofNat n.toNat = n := UInt32.ofNat_toNat
    have e0 : UInt32.ofNat 0 = 0 := rfl
    rw [e2, e0] at hsim'
    exact sim_call (s₁ := s₀) (vs := [lf, .loc ℓ, .int (0 : UInt32).toUInt64, .int n.toUInt64])
      (takeAll_cons_run (by fr) (takeAll_cons_run (by fr)
        (takeAll_cons_run (by fr) (takeAll_one_run (by fr))))) hsim'
  · rw [hfr']
    show s₀.frame[x]? = none
    simp only [s₀, A3, A2, A1, S0, a₀]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]

/-! ### `tab` -/

theorem fillCells_get : ∀ (k : Nat) (mem : Std.HashMap Nat (Option LV)) (objs : Std.HashMap Nat Nat)
    (a x : Nat), (Backend2.fillCells mem objs a k).1[x]? =
      (if a ≤ x ∧ x < a + k then some (some .unit) else mem[x]?) ∧
    (Backend2.fillCells mem objs a k).2[x]? = (if a ≤ x ∧ x < a + k then some 1 else objs[x]?)
  | 0, mem, objs, a, x => by simp [Backend2.fillCells]
  | k + 1, mem, objs, a, x => by
      simp only [Backend2.fillCells]
      obtain ⟨h1, h2⟩ := fillCells_get k (mem.insert a (some .unit)) (objs.insert a 1) (a + 1) x
      rw [h1, h2]
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
      constructor
      · by_cases hx : a = x
        · subst hx; simp
        · by_cases hr : a + 1 ≤ x ∧ x < a + 1 + k
          · rw [if_pos hr, if_pos (by omega)]
          · rw [if_neg hr, if_neg hx, if_neg (by omega)]
      · by_cases hx : a = x
        · subst hx; simp
        · by_cases hr : a + 1 ≤ x ∧ x < a + 1 + k
          · rw [if_pos hr, if_pos (by omega)]
          · rw [if_neg hr, if_neg hx, if_neg (by omega)]

theorem lenOf_word (c : UInt32) : Backend2.lenOf c.toUInt64 = (arrLen c).toNat := by
  simp only [Backend2.lenOf, UInt32.toUInt32_toUInt64, arrLen]
  split <;> rfl

theorem HRel.fill {p : Prog} {N c : Nat} {μ : Heap} {s : St} (h : HRel p N c μ s)
    (F : Std.HashMap Var LV) {k : Nat} (hk : k < 2 ^ 32) :
    HRel p N (c + 1) (μ.fill (regionBase c) k Val.unit) (stFill s F k) := by
  have hle : regionBase c + k < regionBase (c + 1) := by
    simp only [regionBase, Backend2.regionSize]; omega
  have hlt : regionBase c < regionBase (c + 1) := lt_of_le_of_lt (Nat.le_add_right _ _) hle
  refine ⟨?_, fun a => ?_, fun a w hw => ?_, fun a => ?_, fun a ha => ?_⟩
  · simp only [stFill, h.next, regionBase]; ring
  · simp only [BoLo.Heap.fill, stFill, h.next, (fillCells_get k _ _ _ a).1]
    split
    · simp
    · exact h.dom a
  · simp only [BoLo.Heap.fill] at hw
    simp only [stFill, h.next, (fillCells_get k _ _ _ a).1]
    split at hw
    · cases hw; rw [if_pos (by assumption)]; exact ⟨_, rfl, .unit⟩
    · rw [if_neg (by assumption)]; exact h.val a w hw
  · simp only [BoLo.Heap.fill, stFill, h.next, (fillCells_get k _ _ _ a).2]
    split
    · simp
    · exact h.objs a
  · simp only [BoLo.Heap.fill] at ha
    split at ha
    · rename_i hr; exact lt_trans hr.2 hle
    · exact lt_trans (h.below a ha) hlt

/-- `tabLoop`'s frame when it starts, on `(f, ℓ, n, i, k)`. -/
def tl0 (s : St) (lf : LV) (ℓ : Nat) (nn : UInt64) (i k : Nat) : St :=
  let F := (((((∅ : Std.HashMap Var LV).insert 0 lf).insert 1 (.loc ℓ)).insert 2 (.int nn)).insert 3
    (.int (UInt32.ofNat i).toUInt64)).insert 4 (.int (UInt32.ofNat k).toUInt64)
  { s with frame := F }

theorem zip5 (a b c d e : LV) :
    (((List.range (4 + 1)).zip [a, b, c, d, e]).foldl (fun m x => m.insert x.1 x.2)
      (∅ : Std.HashMap Var LV)) =
      (((((∅ : Std.HashMap Var LV).insert 0 a).insert 1 b).insert 2 c).insert 3 d).insert 4 e :=
  rfl

/-- After `tabLoop`'s test, its answer `bb`. -/
def tl7 (s : St) (lf : LV) (ℓ : Nat) (nn : UInt64) (i k : Nat) (bb : Bool) : St :=
  let A5 := stI (tl0 s lf ℓ nn i k) 5 (Backend2.litV (.i32 0))
  let A6 := stI A5 6 (.int (UInt32.ofNat k).toUInt64)
  stI (stE (stE A6 5) 6) 7 (.inj bb .unit)

/-- Before the callback's call on the index `i`. -/
def tlB (s : St) (lf : LV) (ℓ : Nat) (nn : UInt64) (i k : Nat) : St :=
  let A := stI (stI (stE (stI (stE (tl7 s lf ℓ nn i k true) 7) 9 .unit) 9) 10 lf) 11
    (.int (UInt32.ofNat i).toUInt64)
  stE (stE A 10) 11

/-- At the store of the callback's value `v` into `ℓ + i`, from the state `s₁` after the call. -/
def tlS (s₁ : St) (v : LV) (ℓ i : Nat) : St :=
  let A := stI (stI (stI s₁ 12 v) 13 (.loc ℓ)) 14 (.int (UInt32.ofNat i).toUInt64)
  stI (stE (stE A 13) 14) 15 (.loc (ℓ + i))

/-- Before the loop's next turn: the arguments taken. -/
def tlC (s₁ : St) (v : LV) (ℓ i k : Nat) : St :=
  let X := tlS s₁ v ℓ i
  let A := stE (stI (stStore X ((X.frame.erase 15).erase 12) (ℓ + i) v) 16 .unit) 16
  let A17 := stI (stE A 3) 17 (.int (UInt32.ofNat i + 1).toUInt64)
  let A18 := stI (stE A17 4) 18 (.int (UInt32.ofNat k - 1).toUInt64)
  stE (stE (stE (stE (stE A18 0) 1) 2) 17) 18

/-- After `tabLoop`'s last turn. -/
def tlStop (s : St) (lf : LV) (ℓ : Nat) (nn : UInt64) (i : Nat) : St :=
  let A := stE (stE (stE (stE (stI (stE (tl7 s lf ℓ nn i 0 false) 7) 8 .unit) 8) 0) 3) 4
  stE (stE A 1) 2

theorem tl_empty (s : St) (lf : LV) (ℓ : Nat) (nn : UInt64) (i k : Nat) (s₁ : St) (v : LV)
    (hfr₁ : s₁.frame = (tlB s lf ℓ nn i k).frame) : ∀ x : Nat, (tlC s₁ v ℓ i k).frame[x]? = none := by
  intro x
  simp only [tlC, tlS, stI, stE, stStore]
  rw [hfr₁]
  simp only [tlB, tl7, tl0, stI, stE]
  simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
    beq_iff_eq]
  rcases Nat.lt_or_ge x 24 with hx | hx
  · interval_cases x <;> simp
  · simp (disch := omega) only [if_neg]

theorem tl_facts (s : St) (lf : LV) (ℓ : Nat) (nn : UInt64) (i k : Nat) (s₁ : St) (v : LV) :
    (∀ x : Nat, (tlStop s lf ℓ nn i).frame[x]? = none) ∧
    ((tlB s lf ℓ nn i k).mem = s.mem ∧ (tlB s lf ℓ nn i k).objs = s.objs ∧
      (tlB s lf ℓ nn i k).next = s.next) ∧
    ((tlS s₁ v ℓ i).mem = s₁.mem ∧ (tlS s₁ v ℓ i).objs = s₁.objs ∧ (tlS s₁ v ℓ i).next = s₁.next) ∧
    ((tlC s₁ v ℓ i k).mem = (stStore s₁ s₁.frame (ℓ + i) v).mem ∧
      (tlC s₁ v ℓ i k).objs = (stStore s₁ s₁.frame (ℓ + i) v).objs ∧
      (tlC s₁ v ℓ i k).next = (stStore s₁ s₁.frame (ℓ + i) v).next) ∧
    ((tlStop s lf ℓ nn i).mem = s.mem ∧ (tlStop s lf ℓ nn i).objs = s.objs ∧
      (tlStop s lf ℓ nn i).next = s.next) := by
  refine ⟨fun x => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [tlStop, tl7, tl0, stI, stE]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]
  all_goals refine ⟨?_, ?_, ?_⟩ <;> simp [tlB, tlS, tlC, tlStop, tl7, tl0, stStore]

set_option maxHeartbeats 2000000 in
/-- **`tabLoop`**: the cells `ℓ + i, …, ℓ + i + k − 1` written in order with the callback's values
at their indices, as `tabFill` runs; then the family `(ℓ, n)`. -/
theorem tabLoop_sim {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m) {f : Val} {lf : LV} (hlf : VRel p N f lf) (ℓ : Nat)
    (nn : UInt32) :
    ∀ (k i : Nat), i + k < 2 ^ 32 → ∀ (s : St) (c c' : Nat) (μ μ' : Heap) (w : Val) (q : Nat),
      q ≤ sz → BigN (ℍ := Backend2.lirHost) bumpAlloc q c μ (tabFill f ℓ nn i k) c' μ' w →
      HRel p N c μ s →
      w = Val.arr ℓ nn ∧ ∃ s', HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
        Sim (fun g => Backend2.callFn p g tabLoopCode
          [lf, .loc ℓ, .int nn.toUInt64, .int (UInt32.ofNat i).toUInt64,
            .int (UInt32.ofNat k).toUInt64]) s
          (.ok (.pair (.loc ℓ) (.int nn.toUInt64), s')) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  intro k
  induction k with
  | zero =>
      intro i hik s c c' μ μ' w q hq hb hh
      obtain ⟨rfl, rfl, rfl⟩ := big_val_inv hb (Val.arr ℓ nn) rfl
      obtain ⟨hstop, -, -, -, hE⟩ := tl_facts s lf ℓ nn.toUInt64 i 0 s .unit
      refine ⟨rfl, { tlStop s lf ℓ nn.toUInt64 i with frame := s.frame },
        (hh.congr hE.1 hE.2.1 hE.2.2).frame s.frame, rfl,
        sim_code (s' := tlStop s lf ℓ nn.toUInt64 i) hrt.tabLoop rfl (fun rt => ?_) hstop⟩
      rw [zip5]
      change Sim _ (tl0 s lf ℓ nn.toUInt64 i 0) _
      refine sim_lv (ht 5 (by decide)) (sim_lit (.i32 0)) ?_
      refine sim_cp (v := .int (UInt32.ofNat 0).toUInt64) (ht 4 (by decide)) (by frw [tl0]) ?_
      refine sim_lv (ht 7 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntLt (a := (0 : UInt32).toUInt64) (b := (UInt32.ofNat 0).toUInt64) (by frw [tl0])
          (by frw [tl0]))) ?_
      have hd0 : decide ((0 : UInt32).toUInt64.toUInt32 < (UInt32.ofNat 0).toUInt64.toUInt32) =
          false := by decide
      rw [hd0]
      refine sim_case_l (v := .unit) (by frw [tl7, tl0]) ?_
      refine sim_dr (v := .unit) (ht 8 (by decide)) (by frw [tl7, tl0]) ?_
      refine sim_dr (v := lf) (ht 0 (by decide)) (by frw [tl7, tl0]) ?_
      refine sim_dr (v := .int (UInt32.ofNat i).toUInt64) (ht 3 (by decide)) (by frw [tl7, tl0]) ?_
      refine sim_dr (v := .int (UInt32.ofNat 0).toUInt64) (ht 4 (by decide)) (by frw [tl7, tl0]) ?_
      have h1 := sim_pr (p := p) (rt := rt) (va := .loc ℓ) (vb := .int nn.toUInt64)
        (s := stE (stE (stE (stE (stI (stE (tl7 s lf ℓ nn.toUInt64 i 0 false) 7) 8 .unit) 8) 0) 3) 4)
        (a := 1) (b := 2) (by frw [tl7, tl0]) (by frw [tl7, tl0])
      exact h1
  | succ k ih =>
      intro i hik s c c' μ μ' w q hq hb hh
      simp only [tabFill] at hb
      obtain ⟨q₁, q₂, c₁, μ₁, hq₁, hq₂, hfirst, hrest⟩ := big_seq_inv hb
      rcases big_app_inv hfirst with
          ⟨i₁, j₁, k₁, c₂, μ₂, c₃, μ₃, c₄, μ₄, va, vf, r, hi₁, hj₁, hk₁, hA, hF, hhd, hr⟩ |
          ⟨i₁, j₁, c₂, μ₂, va, hi₁, hj₁, hA, hF, he⟩
      swap
      · exact absurd (congrArg Subtype.val he) (by simp [Val.storeV, Val.unit])
      obtain ⟨h1, h2, h3⟩ := big_val_inv hF (Val.storeV (Val.loc (ℓ + i))) rfl
      subst c₃ μ₃ vf
      obtain ⟨hc4, hd⟩ := ahead_det hhd rfl
      subst c₄
      obtain ⟨ℓ', w', hℓ, hw', rfl, rfl⟩ := head_store_inv hd
      obtain rfl : ℓ' = ℓ + i := (Val.loc_inj.mp hℓ).symm
      obtain ⟨h4, h5, h6⟩ := big_val_inv hr Val.unit rfl
      subst c₁ μ₁
      obtain ⟨-, hBh, -, -, -⟩ := tl_facts s lf ℓ nn.toUInt64 i (k + 1) s .unit
      obtain ⟨lv, s₁, hlv, hh₁, hfr₁, hsim₁⟩ := call_val (k := _) (sz := sz) hrt hcall (by omega) hA
        hlf (.lit (.i32 (UInt32.ofNat i))) (s := tlB s lf ℓ nn.toUInt64 i (k + 1))
        (hh.congr hBh.1 hBh.2.1 hBh.2.2)
      obtain ⟨-, -, hSh, hCh, -⟩ := tl_facts s lf ℓ nn.toUInt64 i (k + 1) s₁ lv
      have hCe := tl_empty s lf ℓ nn.toUInt64 i (k + 1) s₁ lv hfr₁
      obtain ⟨lw', hlw', -⟩ := hh₁.val (ℓ + i) w' hw'
      have hhC : HRel p N c₂ (μ₂.upd (ℓ + i) va) (tlC s₁ lv ℓ i (k + 1)) :=
        (hh₁.store s₁.frame hw' hlv).congr hCh.1 hCh.2.1 hCh.2.2
      obtain ⟨hwv, s', hh', hfr', hsim'⟩ := ih (i + 1) (by omega) (tlC s₁ lv ℓ i (k + 1)) c₂ c'
        (μ₂.upd (ℓ + i) va) μ' w q₂ (by omega) hrest hhC
      refine ⟨hwv, { s' with frame := s.frame }, hh'.frame _, rfl, sim_code hrt.tabLoop rfl
        (fun rt => ?_) (by rw [hfr']; exact hCe)⟩
      rw [zip5]
      change Sim _ (tl0 s lf ℓ nn.toUInt64 i (k + 1)) _
      refine sim_lv (ht 5 (by decide)) (sim_lit (.i32 0)) ?_
      refine sim_cp (v := .int (UInt32.ofNat (k + 1)).toUInt64) (ht 4 (by decide)) (by frw [tl0]) ?_
      refine sim_lv (ht 7 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntLt (a := (0 : UInt32).toUInt64) (b := (UInt32.ofNat (k + 1)).toUInt64) (by frw [tl0])
          (by frw [tl0]))) ?_
      have hd : decide ((0 : UInt32).toUInt64.toUInt32 < (UInt32.ofNat (k + 1)).toUInt64.toUInt32)
          = true := by
        simp only [UInt32.toUInt32_toUInt64, decide_eq_true_eq]
        apply UInt32.lt_iff_toNat_lt.mpr
        simp; omega
      rw [hd]
      refine sim_case_r (v := .unit) (by frw [tl7, tl0]) ?_
      refine sim_dr (v := .unit) (ht 9 (by decide)) (by frw [tl7, tl0]) ?_
      refine sim_cp (v := lf) (ht 0 (by decide)) (by frw [tl7, tl0]) ?_
      refine sim_cp (v := .int (UInt32.ofNat i).toUInt64) (ht 3 (by decide)) (by frw [tl7, tl0]) ?_
      refine sim_lv (ht 12 (by decide)) (sim_app (by frw [tl7, tl0]) (by frw [tl7, tl0]) hsim₁) ?_
      refine sim_cp (v := .loc ℓ) (ht 1 (by decide)) (by frw [hfr₁, tlB, tl7, tl0]) ?_
      refine sim_cp (v := .int (UInt32.ofNat i).toUInt64) (ht 3 (by decide))
        (by frw [hfr₁, tlB, tl7, tl0]) ?_
      refine sim_lv (ht 15 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_locAdd (l := ℓ) (i := (UInt32.ofNat i).toUInt64) (by frw [hfr₁, tlB, tl7, tl0])
          (by frw [hfr₁, tlB, tl7, tl0]))) ?_
      rw [lt32 (by omega)]
      refine sim_lv (ht 16 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cellStore (a := ℓ + i) (v := lv) (w := lw') (by frw [hfr₁, tlB, tl7, tl0])
          (by frw [hfr₁, tlB, tl7, tl0]) (by simpa using hlw'))) ?_
      refine sim_dr (v := .unit) (ht 16 (by decide)) (by frw [tl0]) ?_
      refine sim_lv (ht 17 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntSucc (a := (UInt32.ofNat i).toUInt64)
          (by frw [hfr₁, tlB, tl7, tl0, stStore]))) ?_
      rw [mask32_succ]
      refine sim_lv (ht 18 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
        (evalOp_cntPred (a := (UInt32.ofNat (k + 1)).toUInt64)
          (by frw [hfr₁, tlB, tl7, tl0, stStore]))) ?_
      rw [mask32_pred]
      have hsim'' : Sim (fun g => Backend2.callFn p g tabLoopCode
          [lf, .loc ℓ, .int nn.toUInt64, .int (UInt32.ofNat i + 1).toUInt64,
            .int (UInt32.ofNat (k + 1) - 1).toUInt64])
          (tlC s₁ lv ℓ i (k + 1)) (.ok (.pair (.loc ℓ) (.int nn.toUInt64), s')) := by
        rw [ofNat_succ32, ofNat_pred32]; exact hsim'
      exact sim_call (s₁ := tlC s₁ lv ℓ i (k + 1))
        (takeAll_cons_run (by frw [hfr₁, tlB, tl7, tl0, stStore])
          (takeAll_cons_run (by frw [hfr₁, tlB, tl7, tl0, stStore])
            (takeAll_cons_run (by frw [hfr₁, tlB, tl7, tl0, stStore])
              (takeAll_cons_run (by frw [hfr₁, tlB, tl7, tl0, stStore])
                (takeAll_one_run (by frw [hfr₁, tlB, tl7, tl0, stStore])))))) hsim''

theorem vrel_tab_inv {p : Prog} {N : Nat} {f : Val} {cc : UInt32} {lv : LV}
    (h : VRel p N (Val.pair (Val.i32 cc) f) lv) :
    ∃ lf, lv = .pair (.int cc.toUInt64) lf ∧ VRel p N f lf := by
  obtain ⟨x, y, rfl, hx, hy⟩ := vrel_pair_inv h
  rw [vrel_i32_inv hx]
  exact ⟨y, rfl, hy⟩

theorem arrLen_lt (cc : UInt32) : (arrLen cc).toNat < 2 ^ 31 := by
  unfold arrLen; split
  · rename_i h; have := UInt32.lt_iff_toNat_lt.mp h; simpa using this
  · simp

set_option maxHeartbeats 1000000 in
theorem call_tab {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m)
    {va : Val} {la : LV} {s : St} {c c₁ c' k : Nat} {μ μ₁ μ' : Heap} {r : Expr} {w : Val}
    (hk : k ≤ sz)
    (hhd : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app (Val.prim .tab).1 va.1) c₁ μ₁ r)
    (hbr : BigN (ℍ := Backend2.lirHost) bumpAlloc k c₁ μ₁ r c' μ' w) (hva : VRel p N va la)
    (hh : HRel p N c μ s) :
    ∃ lw s', VRel p N w lw ∧ HRel p N c' μ' s' ∧ s'.frame = s.frame ∧
      Sim (fun f => Backend2.callClos p f (.clos 7 []) (some la) 0) s (.ok (lw, s')) := by
  have ht : ∀ x : Nat, x < rtBound → p.ty[x]? = some .unit := fun x hx => hty x (by omega)
  obtain ⟨cc, f, rfl, rfl, rfl, rfl⟩ := ahead_tab_inv hhd
  have hpick : bumpAlloc.pick c μ (arrLen cc).toNat = regionBase c := bumpAlloc_pick (fun i hi => by
    by_contra hne
    exact absurd (lt_of_le_of_lt (Nat.le_add_right _ _) (hh.below _ hne)) (lt_irrefl _))
  have hnx : s.next = regionBase c := hh.next
  rw [hpick, ← hnx] at hbr
  obtain ⟨lf, rfl, hlf⟩ := vrel_tab_inv hva
  let L := (arrLen cc).toNat
  have hL := arrLen_lt cc
  let S0 : St := { s with frame := (∅ : Std.HashMap Var LV).insert 0 (.pair (.int cc.toUInt64) lf) }
  let A2 := stI (stI (stE S0 0) 1 (.int cc.toUInt64)) 2 lf
  let A3 := stI A2 3 (.int cc.toUInt64)
  let A4 := stI (stFill A3 (A3.frame.erase 1) L) 4 (.loc A3.next)
  let A5 := stI (stE A4 3) 5 (.int (arrLen cc).toUInt64)
  let A6 := stI A5 6 (.int (arrLen cc).toUInt64)
  let A7 := stI A6 7 (Backend2.litV (.i32 0))
  let Sp := stE (stE (stE (stE (stE A7 2) 4) 5) 7) 6
  have hSp : HRel p N (c + 1) (μ.fill s.next L Val.unit) Sp := by
    have := hh.fill (A3.frame.erase 1) (k := L) (by omega)
    rw [← hnx] at this
    exact this.congr (by simp [Sp, A7, A6, A5, A4, A3, A2, S0, stFill])
      (by simp [Sp, A7, A6, A5, A4, A3, A2, S0, stFill])
      (by simp [Sp, A7, A6, A5, A4, A3, A2, S0, stFill])
  obtain ⟨rfl, s', hh', hfr', hsim'⟩ := tabLoop_sim hty hN hrt hcall hlf s.next (arrLen cc)
    L 0 (by omega) Sp (c + 1) c' _ μ' w k hk hbr hSp
  refine ⟨.pair (.loc s.next) (.int (arrLen cc).toUInt64), { s' with frame := s.frame },
    .pair (.loc _) (.lit (.i32 _)), hh'.frame _, rfl, call1 (s₁ := s') hrt.tab (fun rt => ?_)
      (fun x => ?_)⟩
  · refine sim_lp (va := .int cc.toUInt64) (vc := lf) (by fr) ?_
    refine sim_cp (v := .int cc.toUInt64) (ht 1 (by decide)) (by fr) ?_
    refine sim_lv (ht 4 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
      (evalOp_cellsNew (a := cc.toUInt64) (by fr))) ?_
    rw [lenOf_word]
    refine sim_lv (ht 5 (by decide)) (sim_prim (fun f => by rw [Backend2.eval] <;> simp)
      (evalOp_clampLen (a := cc.toUInt64) (by frw [stFill]))) ?_
    rw [clamp_word]
    refine sim_cp (v := .int (arrLen cc).toUInt64) (ht 5 (by decide)) (by frw [stFill]) ?_
    refine sim_lv (ht 7 (by decide)) (sim_lit (.i32 0)) ?_
    have e1 : UInt32.ofNat L = arrLen cc := UInt32.ofNat_toNat
    have e0 : UInt32.ofNat 0 = 0 := rfl
    rw [e1, e0] at hsim'
    exact sim_call (s₁ := Sp) (takeAll_cons_run (by frw [stFill]) (takeAll_cons_run (by frw [stFill])
      (takeAll_cons_run (by frw [stFill]) (takeAll_cons_run (by frw [stFill])
        (takeAll_one_run (by frw [stFill])))))) hsim'
  · rw [hfr']
    show Sp.frame[x]? = none
    simp only [Sp, A7, A6, A5, A4, A3, A2, S0, stFill]
    simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, Std.HashMap.getElem?_empty,
      beq_iff_eq]
    rcases Nat.lt_or_ge x 24 with hx | hx
    · interval_cases x <;> simp
    · simp (disch := omega) only [if_neg]

/-! ### Every call -/

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

theorem ahead_nonfun {c c₁ : Nat} {μ μ₁ : Heap} {f va : Val} {r : Expr}
    (h : AHead (ℍ := Backend2.lirHost) bumpAlloc c μ (.app f.1 va.1) c₁ μ₁ r)
    (hf : ∀ b, f.1 ≠ .lam b) (hp : ∀ q, f.1 ≠ .prim q) (hs : ∀ x, f.1 ≠ .app (.prim .store) x) :
    False := by
  generalize hE : Expr.app f.1 va.1 = E at h
  cases h with
  | det h _ => subst hE; exact head_nonfun h hf hp hs
  | alloc => simp only [Expr.app.injEq, Expr.val, Val.prim] at hE; exact hp _ hE.1
  | tab => simp only [Expr.app.injEq, Expr.val, Val.prim] at hE; exact hp _ hE.1

theorem head_lit_false {μ μ' : Heap} {c : IntLit} {a r : Expr}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (.prim (.lit c)) a) μ' r) : False := by
  generalize hE : Expr.app (.prim (.lit c)) a = E at h
  cases h <;> simp_all [BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE, Expr.val, Val.prim,
    Val.lam]

theorem head_store0_false {μ μ' : Heap} {a r : Expr}
    (h : Head (ℍ := Backend2.lirHost) μ (.app (.prim .store) a) μ' r) : False := by
  cases h

/-- **Every call is simulated**, at derivations of size `sz`, given the bodies' prints at `sz`
and every call below it. -/
theorem callAt_of {p : Prog} {N sz : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m)
    (hfwd : ∀ ρ n out e t n', Pr p N ρ n out e t n' → FwdOne p N sz ρ n out e t n') :
    CallAt p N sz := by
  intro vf va lf la s c μ c₁ μ₁ r c' μ' w k hk hhd hbr hvf hva hh
  cases hvf with
  | unit => exact (ahead_nonfun hhd (by simp [Val.unit]) (by simp [Val.unit])
      (by simp [Val.unit])).elim
  | lit q =>
      obtain ⟨-, hd⟩ := ahead_det hhd rfl
      exact (head_lit_false hd).elim
  | loc ℓ => exact (ahead_nonfun hhd (by simp [Val.loc]) (by simp [Val.loc])
      (by simp [Val.loc])).elim
  | pair => exact (ahead_nonfun hhd (by simp [Val.pair]) (by simp [Val.pair])
      (by simp [Val.pair])).elim
  | inj₁ => exact (ahead_nonfun hhd (by simp [Val.inj₁]) (by simp [Val.inj₁])
      (by simp [Val.inj₁])).elim
  | inj₂ => exact (ahead_nonfun hhd (by simp [Val.inj₂]) (by simp [Val.inj₂])
      (by simp [Val.inj₂])).elim
  | host op c hc => exact call_host hc hhd hbr hva hh
  | store1 hv => exact call_store1 hrt hhd hbr hv hva hh
  | lam hpr hm hc hlen hcapl hrel =>
      exact call_lam hty hfwd hpr hm hc hlen hcapl hrel hk hhd hbr hva hh
  | rt q c hq =>
      cases q <;> simp only [rtCode, reduceCtorEq, Option.some.injEq] at hq <;> subst hq
      · exact call_alloc hrt hhd hbr hva hh
      · exact call_free hrt hhd hbr hva hh
      · exact call_load hrt hhd hbr hva hh
      · obtain ⟨-, hd⟩ := ahead_det hhd rfl
        exact (head_store0_false hd).elim
      · exact call_tab hty hN hrt hcall hk hhd hbr hva hh
      · exact call_idx hrt hhd hbr hva hh
      · exact call_drop hty hN hrt hcall hk hhd hbr hva hh
      · exact call_split hrt hhd hbr hva hh
      · exact call_count hty hN hrt hcall hk hhd hbr hva hh
      · exact call_countTry hty hN hrt hcall hk hhd hbr hva hh
      · exact call_bf hty hN hrt hcall hk hhd hbr hva hh

/-- **The print of every term is simulated at derivations of size `sz`**, given every call below
it. -/
theorem fwd_pr {p : Prog} {N sz : Nat} (hty : TyOK p N) (hrt : RT p N)
    (hcall : ∀ m, m < sz → CallAt p N m) :
    ∀ ρ n out e t n', Pr p N ρ n out e t n' → FwdOne p N sz ρ n out e t n' := by
  intro ρ n out e t n' h
  induction h with
  | varCopy ρ n out k h => exact fwd_varCopy hty ρ n out k h
  | varMove ρ n out k h => exact fwd_varMove ρ n out k h
  | unit ρ n out =>
      exact fwd_value Val.unit .unit rfl (fun _ => rfl) .unit (fun _ _ => sim_unit)
  | loc ρ n out ℓ =>
      exact fwd_value (Val.loc ℓ) (.loc ℓ) rfl (fun _ => rfl) (.loc ℓ) (fun _ _ => sim_locAt)
  | lit ρ n out c =>
      exact fwd_value (Val.prim (.lit c)) (Backend2.litV c) rfl (fun _ => rfl) (.lit c)
        (fun _ _ => sim_lit c)
  | hostV ρ n out op c hc =>
      exact fwd_value (Val.prim (.host op)) (.clos c []) rfl (fun _ => rfl) (.host op c hc)
        (fun _ _ => sim_clos_nil)
  | rtV ρ n out q c hq =>
      exact fwd_value (Val.prim q) (.clos c []) rfl (fun _ => rfl) (.rt q c hq)
        (fun _ _ => sim_clos_nil)
  | pair ha hb iha ihb => exact fwd_pair hty ha hb iha ihb
  | inj₁ ha iha => exact fwd_inj false hty ha iha
  | inj₂ ha iha => exact fwd_inj true hty ha iha
  | seq ha hb iha ihb => exact fwd_seq hty ha hb iha ihb
  | app ha hf iha ihf => exact fwd_app hty hrt ha hf iha ihf hcall
  | letpair ha hb iha ihb => exact fwd_letpair hty ha hb iha ihb
  | case hs ha hb ihs iha ihb => exact fwd_case hty hs ha hb ihs iha ihb
  | lam c hb hm hc _ => exact fwd_lam hty c hb hm hc

/-- **The simulation**, at every size: every print and every call. -/
theorem fwd_all {p : Prog} {N : Nat} (hty : TyOK p N) (hN : rtBound ≤ N) (hrt : RT p N) :
    ∀ sz, (∀ ρ n out e t n', Pr p N ρ n out e t n' → FwdOne p N sz ρ n out e t n') ∧
      CallAt p N sz := by
  intro sz
  induction sz using Nat.strong_induction_on with
  | _ sz ih =>
      have hcall : ∀ m, m < sz → CallAt p N m := fun m hm => (ih m hm).2
      have hf := fwd_pr hty hrt hcall
      exact ⟨hf, callAt_of hty hN hrt hcall hf⟩

end Lowering
