import Lowering.PrintRel

/-!
# Lowering — runs of the LIR interpreter at every fuel  `[spec §56]`

The interpreter (`Backend2/Interp.lean`) is a function of its fuel. `Sim E s r` says of a family
of computations `E f` indexed by the fuel that from the state `s` each either answers `r` or runs
out of fuel (`LeR`), and that from some fuel on each answers `r`. It composes through `bind`
(`Sim.bind`), so a run of the print is read one operation at a time. `Sim.eval` is the step from
`eval p (f + 1)` to `eval p f`.
-/

namespace Lowering
open Backend2 (Var Tm Fn Code CodeKind Prog LTy LCTy Op LV St IM eval callFn callClos takeV
  bindV tyIn peekV takeAll bad)

/-- `a` is `b`, or `a` ran out of fuel. -/
def LeR {α : Type} (a b : Except String α) : Prop := a = b ∨ a = .error outOfFuel

/-- **A run at every fuel**: from `s`, each `E f` answers `r` or runs out of fuel, and from some
fuel on each answers `r`. -/
def Sim {α : Type} (E : Nat → IM α) (s : St) (r : Except String (α × St)) : Prop :=
  (∀ f, LeR ((E f).run s) r) ∧ ∃ F₀, ∀ f, F₀ ≤ f → (E f).run s = r

theorem Sim.const {α : Type} {m : IM α} {s : St} {r : Except String (α × St)} (h : m.run s = r) :
    Sim (fun _ => m) s r :=
  ⟨fun _ => .inl h, 0, fun _ _ => h⟩

theorem Sim.bind {α β : Type} {M : Nat → IM α} {K : Nat → α → IM β} {s s₁ : St} {a : α}
    {r : Except String (β × St)} (hm : Sim M s (.ok (a, s₁))) (hk : Sim (fun f => K f a) s₁ r) :
    Sim (fun f => M f >>= K f) s r := by
  refine ⟨fun f => ?_, ?_⟩
  · rcases hm.1 f with h | h
    · show LeR ((M f >>= K f).run s) r
      rw [StateT.run_bind, h]
      exact hk.1 f
    · right
      show (M f >>= K f).run s = _
      rw [StateT.run_bind, h]; rfl
  · obtain ⟨F₁, h₁⟩ := hm.2
    obtain ⟨F₂, h₂⟩ := hk.2
    refine ⟨max F₁ F₂, fun f hf => ?_⟩
    show (M f >>= K f).run s = r
    rw [StateT.run_bind, h₁ f (le_of_max_le_left hf)]
    exact h₂ f (le_of_max_le_right hf)

theorem Sim.bind_const {α β : Type} {m : IM α} {K : Nat → α → IM β} {s s₁ : St} {a : α}
    {r : Except String (β × St)} (hm : m.run s = .ok (a, s₁)) (hk : Sim (fun f => K f a) s₁ r) :
    Sim (fun f => m >>= K f) s r :=
  Sim.bind (M := fun _ => m) (Sim.const hm) hk

/-- **One step of fuel**: a run of `eval p (f + 1)` is one of `eval p f`, which at fuel `0` runs
out. -/
theorem Sim.eval {p : Prog} {rt : LTy} {t : Tm} {s : St} {r : Except String (LV × St)}
    (h : Sim (fun f => eval p (f + 1) rt t) s r) : Sim (fun f => eval p f rt t) s r := by
  refine ⟨fun f => ?_, ?_⟩
  · cases f with
    | zero => right; rw [eval_zero]
    | succ f => exact h.1 f
  · obtain ⟨F₀, h₀⟩ := h.2
    refine ⟨F₀ + 1, fun f hf => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    exact h₀ g (by omega)

theorem Sim.congr {α : Type} {E E' : Nat → IM α} {s : St} {r : Except String (α × St)}
    (h : Sim E s r) (he : ∀ f, E' f = E f) : Sim E' s r := by
  have : E' = E := funext he
  subst this; exact h

/-! ### The frame -/

theorem takeV_run {x : Var} {v : LV} {s : St} (h : s.frame[x]? = some v) :
    (takeV x).run s = .ok (v, ({ s with frame := s.frame.erase x } : St)) := by
  unfold takeV
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    Except.bind, Except.pure, h, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    StateT.pure]

theorem bindV_run (x : Var) (v : LV) (s : St) :
    (bindV x v).run s = .ok ((), ({ s with frame := s.frame.insert x v } : St)) := rfl

theorem tyIn_run {p : Prog} {x : Var} {t : LTy} (s : St) (h : p.ty[x]? = some t) :
    (tyIn p x).run s = .ok (t, s) := by
  unfold tyIn
  simp only [StateT.run, h, pure, StateT.pure, Except.pure]

theorem peekV_run {x : Var} {v : LV} {s : St} (h : s.frame[x]? = some v) :
    (peekV x).run s = .ok (v, s) := by
  unfold peekV
  simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    Except.bind, Except.pure, h, StateT.pure]

/-! ### The interpreter's terms -/

theorem sim_var {p : Prog} {rt : LTy} {x : Var} {v : LV} {s : St} (h : s.frame[x]? = some v) :
    Sim (fun f => eval p f rt (.var x)) s (.ok (v, ({ s with frame := s.frame.erase x } : St))) :=
  Sim.eval (Sim.congr (Sim.const (takeV_run h)) fun f => by rw [eval])

theorem sim_unit {p : Prog} {rt : LTy} {s : St} :
    Sim (fun f => eval p f rt .unit) s (.ok (.unit, s)) :=
  Sim.eval (Sim.congr (Sim.const rfl) fun f => by rw [eval])

theorem sim_lit {p : Prog} {rt : LTy} {s : St} (c : BoCa.IntLit) :
    Sim (fun f => eval p f rt (.lit c)) s (.ok (Backend2.litV c, s)) :=
  Sim.eval (Sim.congr (Sim.const rfl) fun f => by rw [eval])

theorem sim_letv {p : Prog} {rt t : LTy} {x : Var} {e b : Tm} {s s₁ : St} {v : LV}
    {r : Except String (LV × St)} (hty : p.ty[x]? = some t)
    (he : Sim (fun f => eval p f t e) s (.ok (v, s₁)))
    (hb : Sim (fun f => eval p f rt b) ({ s₁ with frame := s₁.frame.insert x v } : St) r) :
    Sim (fun f => eval p f rt (.letv x e b)) s r := by
  refine Sim.eval (Sim.congr (Sim.bind_const (tyIn_run s hty) ?_) fun f => by rw [eval])
  exact Sim.bind he (Sim.bind_const (bindV_run x v s₁) hb)

theorem sim_pair {p : Prog} {rt : LTy} {a b : Var} {va vb : LV} {s : St}
    (ha : s.frame[a]? = some va) (hb : (s.frame.erase a)[b]? = some vb) :
    Sim (fun f => eval p f rt (.pair a b)) s
      (.ok (.pair va vb, ({ s with frame := (s.frame.erase a).erase b } : St))) := by
  refine Sim.eval (Sim.congr (Sim.bind_const (takeV_run ha) ?_) fun f => by rw [eval])
  exact Sim.bind_const (takeV_run (s := ({ s with frame := s.frame.erase a } : St)) hb)
    (Sim.const rfl)

theorem sim_inj {p : Prog} {rt : LTy} {r : Bool} {a : Var} {va : LV} {s : St}
    (ha : s.frame[a]? = some va) :
    Sim (fun f => eval p f rt (.inj r a)) s
      (.ok (.inj r va, ({ s with frame := s.frame.erase a } : St))) := by
  exact Sim.eval (Sim.congr (Sim.bind_const (K := fun _ x => pure (LV.inj r x)) (takeV_run ha)
    (Sim.const rfl)) fun f => by rw [eval])

theorem sim_letpair {p : Prog} {rt : LTy} {x y q : Var} {b : Tm} {va vc : LV} {s : St}
    {r : Except String (LV × St)} (hq : s.frame[q]? = some (.pair va vc))
    (hb : Sim (fun f => eval p f rt b)
      ({ s with frame := ((s.frame.erase q).insert x va).insert y vc } : St) r) :
    Sim (fun f => eval p f rt (.letpair x y q b)) s r := by
  refine Sim.eval (Sim.congr (Sim.bind_const (takeV_run hq) ?_) fun f => by rw [eval])
  exact Sim.bind_const (bindV_run x va _) (Sim.bind_const (bindV_run y vc _) hb)

theorem sim_case_l {p : Prog} {rt : LTy} {q x y : Var} {b₁ b₂ : Tm} {v : LV} {s : St}
    {r : Except String (LV × St)} (hq : s.frame[q]? = some (.inj false v))
    (hb : Sim (fun f => eval p f rt b₁) ({ s with frame := (s.frame.erase q).insert x v } : St) r) :
    Sim (fun f => eval p f rt (.case q x b₁ y b₂)) s r := by
  refine Sim.eval (Sim.congr (Sim.bind_const (takeV_run hq) ?_) fun f => by rw [eval])
  exact Sim.bind_const (bindV_run x v _) hb

theorem sim_case_r {p : Prog} {rt : LTy} {q x y : Var} {b₁ b₂ : Tm} {v : LV} {s : St}
    {r : Except String (LV × St)} (hq : s.frame[q]? = some (.inj true v))
    (hb : Sim (fun f => eval p f rt b₂) ({ s with frame := (s.frame.erase q).insert y v } : St) r) :
    Sim (fun f => eval p f rt (.case q x b₁ y b₂)) s r := by
  refine Sim.eval (Sim.congr (Sim.bind_const (takeV_run hq) ?_) fun f => by rw [eval])
  exact Sim.bind_const (bindV_run y v _) hb

theorem sim_copy {p : Prog} {rt : LTy} {x x' : Var} {b : Tm} {v : LV} {s : St}
    {r : Except String (LV × St)} (hty : p.ty[x]? = some .unit) (hx : s.frame[x]? = some v)
    (hb : Sim (fun f => eval p f rt b) ({ s with frame := s.frame.insert x' v } : St) r) :
    Sim (fun f => eval p f rt (.copy x x' b)) s r := by
  refine Sim.eval (Sim.congr (Sim.bind_const (tyIn_run s hty) ?_) fun f => by rw [eval])
  refine Sim.congr (E := fun f => (peekV x >>= fun w => bindV x' w >>= fun _ => eval p f rt b))
    (Sim.bind_const (peekV_run hx) (Sim.bind_const (bindV_run x' v s) hb)) fun f => ?_
  simp only [show LTy.ownsN true 64 LTy.unit = false from rfl, Bool.false_eq_true, if_false]

theorem sim_drop {p : Prog} {rt : LTy} {x : Var} {b : Tm} {v : LV} {s : St}
    {r : Except String (LV × St)} (hty : p.ty[x]? = some .unit) (hx : s.frame[x]? = some v)
    (hb : Sim (fun f => eval p f rt b) ({ s with frame := s.frame.erase x } : St) r) :
    Sim (fun f => eval p f rt (.drop x b)) s r := by
  refine Sim.eval (Sim.congr (Sim.bind_const (tyIn_run s hty) ?_) fun f => by rw [eval])
  refine Sim.congr (E := fun f => (takeV x >>= fun _ => eval p f rt b))
    (Sim.bind_const (takeV_run hx) hb) fun f => ?_
  simp only [show LTy.ownsN false 64 LTy.unit = false from rfl, Bool.false_eq_true, if_false]

theorem sim_app {p : Prog} {rt : LTy} {g a : Var} {vg va : LV} {s : St}
    {r : Except String (LV × St)} (hg : s.frame[g]? = some vg)
    (ha : (s.frame.erase g)[a]? = some va)
    (hc : Sim (fun f => callClos p f vg (some va) 0)
      ({ s with frame := (s.frame.erase g).erase a } : St) r) :
    Sim (fun f => eval p f rt (.app g a)) s r := by
  refine Sim.eval (Sim.congr (Sim.bind_const (takeV_run hg) ?_) fun f => by rw [eval])
  exact Sim.bind_const (takeV_run (s := ({ s with frame := s.frame.erase g } : St)) ha) hc

theorem sim_callClos {p : Prog} {c : Nat} {env : List LV} {a : LV} {s : St}
    {r : Except String (LV × St)} (hc : p.codes[c]? = some (lamCode c))
    (hf : Sim (fun f => callFn p f c (env ++ [a])) s r) :
    Sim (fun f => callClos p f (.clos c env) (some a) 0) s r :=
  Sim.congr hf fun f => by rw [callClos, hc]; rfl

/-- **A call of a function**: its frame its parameters at the arguments; the caller's frame is
restored when the body returns with its frame empty. -/
theorem sim_callFn {p : Prog} {c : Nat} {fn : Fn} {args : List LV} {s s' : St} {v : LV}
    (hfn : p.fns[c]? = some fn) (hlen : fn.params.length = args.length)
    (hb : Sim (fun f => eval p f fn.ret fn.body)
      ({ s with frame := (fn.params.zip args).foldl (fun m x => m.insert x.1 x.2) ∅ } : St)
      (.ok (v, s')))
    (hempty : s'.frame.isEmpty = true) :
    Sim (fun f => callFn p f c args) s (.ok (v, ({ s' with frame := s.frame } : St))) := by
  have key : ∀ f r, (eval p f fn.ret fn.body).run
      ({ s with frame := (fn.params.zip args).foldl (fun m x => m.insert x.1 x.2) ∅ } : St) = r →
      (r = .ok (v, s') → (callFn p f c args).run s = .ok (v, ({ s' with frame := s.frame } : St))) ∧
      (r = .error outOfFuel → (callFn p f c args).run s = .error outOfFuel) := by
    intro f r hr
    rw [Backend2.callFn, hfn]
    simp only [hlen, bne_self_eq_false, Bool.false_eq_true, if_false, StateT.run_bind,
      StateT.run_get, StateT.run_modify, pure_bind]
    rw [hr]
    constructor
    · rintro rfl
      simp only [bind, Except.bind, hempty, Bool.not_true, Bool.false_eq_true, if_false, pure]
      rfl
    · rintro rfl; rfl
  refine ⟨fun f => ?_, ?_⟩
  · rcases hb.1 f with h | h
    · exact .inl ((key f _ h).1 rfl)
    · exact .inr ((key f _ h).2 rfl)
  · obtain ⟨F₀, h₀⟩ := hb.2
    exact ⟨F₀, fun f hf => (key f _ (h₀ f hf)).1 rfl⟩

theorem takeAll_one_run {x : Var} {v : LV} {s : St} (hx : s.frame[x]? = some v) :
    (takeAll [x]).run s = .ok ([v], ({ s with frame := s.frame.erase x } : St)) := by
  simp only [takeAll, List.mapM_cons, List.mapM_nil, StateT.run_bind, takeV_run hx]
  rfl

theorem sim_host {p : Prog} {rt : LTy} {op : BoCa.HostOp} {x : Var} {v r : LV} {s : St}
    (hx : s.frame[x]? = some v)
    (hop : (Backend2.hostOp op v).run ({ s with frame := s.frame.erase x } : St) =
      .ok (r, ({ s with frame := s.frame.erase x } : St))) :
    Sim (fun f => eval p f rt (.prim (.host op) [x])) s
      (.ok (r, ({ s with frame := s.frame.erase x } : St))) := by
  refine Sim.eval (Sim.congr (E := fun _ => Backend2.evalOp (tyIn p) (.host op) [x] rt)
    (Sim.const ?_) fun f => by rw [eval] <;> simp)
  unfold Backend2.evalOp
  rw [StateT.run_bind, takeAll_one_run hx]
  exact hop

theorem erase_get_ne {F : Std.HashMap Var LV} {x y : Nat} (h : x ≠ y) : (F.erase x)[y]? = F[y]? := by
  rw [Std.HashMap.getElem?_erase]; simp [h]

theorem erase_get_self {F : Std.HashMap Var LV} {x : Nat} : (F.erase x)[x]? = none := by
  rw [Std.HashMap.getElem?_erase]; simp

theorem insert_get_ne {F : Std.HashMap Var LV} {x y : Nat} {v : LV} (h : x ≠ y) :
    (F.insert x v)[y]? = F[y]? := by
  rw [Std.HashMap.getElem?_insert]; simp [h]

theorem insert_get_self {F : Std.HashMap Var LV} {x : Nat} {v : LV} : (F.insert x v)[x]? = some v := by
  rw [Std.HashMap.getElem?_insert]; simp

/-- The frame with the variables `xs` erased. -/
def eraseL (F : Std.HashMap Var LV) (xs : List Var) : Std.HashMap Var LV :=
  xs.foldl (fun m x => m.erase x) F

theorem eraseL_get (F : Std.HashMap Var LV) : ∀ (xs : List Var) (y : Var),
    (eraseL F xs)[y]? = if y ∈ xs then none else F[y]?
  | [], y => by simp [eraseL]
  | x :: xs, y => by
      simp only [eraseL, List.foldl_cons]
      rw [show List.foldl (fun m x => m.erase x) (F.erase x) xs = eraseL (F.erase x) xs from rfl,
        eraseL_get (F.erase x) xs y, Std.HashMap.getElem?_erase]
      by_cases h₁ : y ∈ xs
      · simp [h₁]
      · by_cases h₂ : x = y
        · subst h₂; simp
        · simp [h₁, h₂, Ne.symm h₂]

/-- **The values of distinct live variables, taken**: each once, the frame without them. -/
theorem takeAll_run : ∀ (xs : List Var) (s : St), xs.Nodup → (∀ x ∈ xs, ∃ v, s.frame[x]? = some v) →
    ∃ vs : List LV, (takeAll xs).run s = .ok (vs, ({ s with frame := eraseL s.frame xs } : St)) ∧
      vs.length = xs.length ∧ ∀ i (hi : i < xs.length), s.frame[xs[i]]? = vs[i]?
  | [], s, _, _ => ⟨[], rfl, rfl, fun i hi => absurd hi (by simp)⟩
  | x :: xs, s, hn, hl => by
      obtain ⟨v, hv⟩ := hl x (by simp)
      have hn' := (List.nodup_cons.mp hn)
      obtain ⟨vs, hrun, hlen, hget⟩ := takeAll_run xs ({ s with frame := s.frame.erase x } : St)
        hn'.2 (fun y hy => by
          obtain ⟨w, hw⟩ := hl y (by simp [hy])
          refine ⟨w, ?_⟩
          show (s.frame.erase x)[y]? = some w
          rw [erase_get_ne (fun (h : x = y) => hn'.1 (h ▸ hy))]; exact hw)
      refine ⟨v :: vs, ?_, by simp [hlen], fun i hi => ?_⟩
      · simp only [takeAll, List.mapM_cons, StateT.run_bind, takeV_run hv]
        show (List.mapM takeV xs >>= fun vs => pure (v :: vs)).run _ = _
        rw [StateT.run_bind]
        simp only [takeAll] at hrun
        rw [hrun]; rfl
      · cases i with
        | zero => simpa using hv
        | succ i =>
            have hi' : i < xs.length := by simpa using hi
            have := hget i hi'
            simp only [List.getElem_cons_succ, List.getElem?_cons_succ]
            rw [← this]
            exact (erase_get_ne (fun (h : x = xs[i]) => hn'.1 (h ▸ List.getElem_mem hi'))).symm

theorem sim_clos {p : Prog} {rt : LTy} {c : Nat} {env : List Var} {vs : List LV} {s : St}
    (h : (takeAll env).run s = .ok (vs, ({ s with frame := eraseL s.frame env } : St))) :
    Sim (fun f => eval p f rt (.clos c env)) s
      (.ok (.clos c vs, ({ s with frame := eraseL s.frame env } : St))) :=
  Sim.eval (Sim.congr (Sim.bind_const (K := fun _ x => pure (LV.clos c x)) h (Sim.const rfl))
    fun f => by rw [eval])

/-- **An operation**, the interpreter's step to its definition at every fuel. -/
theorem sim_prim {p : Prog} {rt : LTy} {op : Op} {as : List Var} {s : St}
    {r : Except String (LV × St)} (heq : ∀ f, eval p (f + 1) rt (.prim op as) =
      Backend2.evalOp (tyIn p) op as rt)
    (h : (Backend2.evalOp (tyIn p) op as rt).run s = r) :
    Sim (fun f => eval p f rt (.prim op as)) s r :=
  Sim.eval (Sim.congr (Sim.const h) heq)

/-- **A direct call**: its arguments taken, then the function's call. -/
theorem sim_call {p : Prog} {rt : LTy} {fn : Nat} {as : List Var} {vs : List LV} {s s₁ : St}
    {r : Except String (LV × St)} (ht : (takeAll as).run s = .ok (vs, s₁))
    (hc : Sim (fun f => callFn p f fn vs) s₁ r) :
    Sim (fun f => eval p f rt (.call fn as)) s r :=
  Sim.eval (Sim.congr (Sim.bind_const ht hc) fun f => by rw [eval])

theorem takeAll_nil_run (s : St) : (takeAll []).run s = .ok ([], s) := rfl

theorem takeAll_cons_run {x : Var} {xs : List Var} {v : LV} {vs : List LV} {s s₁ : St}
    (hx : s.frame[x]? = some v)
    (hxs : (takeAll xs).run ({ s with frame := s.frame.erase x } : St) = .ok (vs, s₁)) :
    (takeAll (x :: xs)).run s = .ok (v :: vs, s₁) := by
  simp only [takeAll, List.mapM_cons, StateT.run_bind, takeV_run hx]
  show (List.mapM takeV xs >>= fun vs => pure (v :: vs)).run _ = _
  rw [StateT.run_bind]
  simp only [takeAll] at hxs
  rw [hxs]; rfl

end Lowering
