import Core.HandledNames

/-!
# Core — the names a clause's own code performs or raises  `[spec §19]`

Condition 2 of the direct call of a tail-resumptive clause (`docs/effect-lowering.md` §2.3) asks
that no frame of the continuation `K` between a `perform` and its handler catch a name the
clause's work performs or raises. This file states it over the names the clause's own code
performs or raises, not over its declared row `Σ`.

* `Expr.own C e` is the names `e` performs or raises when it runs only code it holds: `perform` and
  `raise` at a literal name, through `λ`s applied in place, the primitives that run no code they
  are given (`primOwn`), and the calls of the continuation slots `C` (`κ`, an alias of it, the
  answer of its resume), whose code is the continuation's, not the clause's. It is `none` where
  `e` may run code it does not hold: an application of any other variable or computed function, a
  primitive that runs a function it is given (a loop, an array's fill, a handler, a finaliser), or
  an operation at a name that is not a literal.
* `Fo N e` (*first-order at `N`*) says of a term that the only code it applies is its own, at
  `λ`s applied in place and those primitives, and that each `perform` and `raise` in it is at a
  literal name of `N`. A value is `Fo N` whatever code it holds in a data position: the term never
  applies it. `Fo N` is closed under the substitution of any value (`Fo.subst`) and under every
  step of the machine (`Fo.steps`), from any memory.
* A configuration that is `Fo N` performs and raises only names of `N` (`Fo.perform_mem`,
  `Fo.raise_mem`).
* **The clause's work** (`tail_work_names`): a tail-resumptive clause's body `M` with `κ` in the
  slot `0` and its work `M'`, `M` without its resumes (`TailResumesAt 0 M M'`), whose own names
  are `ns` (`M.own [0] = some ns`), is `Fo ns` (`fo_of_tail`). So every run of the work, at every
  argument, every value its free variables are given (the handler's captures among them) and from
  every memory, performs and raises only names of `ns`. This is the code the direct call runs at
  the `perform`, inside `K`.
* **Condition 2 over the names** (`UnhandledNames ns K`): no frame of `K` catches a name of `ns`.
  At no names it holds everywhere (`unhandledNames_nil`); otherwise the program's flow record
  decides it as it decides `UnhandledIn` (`steps_unhandledNames`).
-/

namespace BoCa.Fig16.LogRel.Core.ClauseKinds
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Heap Head Step1 Steps performE raiseE opPayload)

/-! ### First-order terms -/

/-- **A primitive that runs no code it is given**, applied: memory, integers and the host, an
array's index and split. A loop, an array's fill and disposal, a handler, a finaliser and a cancel
delimiter run code they are given; an operation is `perform` or `raise`.  `[spec §19]` -/
def primOwn : Prim → Bool
  | .alloc | .free | .load | .store | .lit _ | .host _ | .idx | .split => true
  | _ => false

/-- **First-order at the names `N`**: the term applies only code it holds, a `λ` applied in place,
a primitive that runs no code it is given (`primOwn`) or the curried `store`; each `perform` and
`raise` in it is at a literal name of `N`. A `λ` in a data position is not constrained: the term
never applies it.  `[spec §19]` -/
inductive Fo (N : List UInt32) : Expr → Prop where
  | var (i : Nat) : Fo N (.var i)
  | unit : Fo N .unit
  | loc (ℓ : Loc) : Fo N (.loc ℓ)
  | prim (p : Prim) : Fo N (.prim p)
  | lam (b : Expr) : Fo N (.lam b)
  | pair {a b : Expr} : Fo N a → Fo N b → Fo N (.pair a b)
  | seq {a b : Expr} : Fo N a → Fo N b → Fo N (.seq a b)
  | letpair {a b : Expr} : Fo N a → Fo N b → Fo N (.letpair a b)
  | case {a b c : Expr} : Fo N a → Fo N b → Fo N c → Fo N (.case a b c)
  | inj₁ {a : Expr} : Fo N a → Fo N (.inj₁ a)
  | inj₂ {a : Expr} : Fo N a → Fo N (.inj₂ a)
  | beta {b x : Expr} : Fo N b → Fo N x → Fo N (.app (.lam b) x)
  | primApp {p : Prim} {x : Expr} : primOwn p = true → Fo N x → Fo N (.app (.prim p) x)
  | store {a x : Expr} : Fo N a → Fo N x → Fo N (.app (.app (.prim .store) a) x)
  | perform {m : UInt32} {X : Expr} : m ∈ N → Fo N X →
      Fo N (.app (.prim .perform) (.pair (.prim (.lit (.i32 m))) X))
  | raise {m : UInt32} {X : Expr} : m ∈ N → Fo N X →
      Fo N (.app (.prim .raise) (.pair (.prim (.lit (.i32 m))) X))

namespace Fo

theorem mono {N N' : List UInt32} (hN : ∀ m ∈ N, m ∈ N') {e : Expr} (h : Fo N e) : Fo N' e := by
  induction h with
  | var i => exact .var i
  | unit => exact .unit
  | loc ℓ => exact .loc ℓ
  | prim p => exact .prim p
  | lam b => exact .lam b
  | pair _ _ iha ihb => exact .pair iha ihb
  | seq _ _ iha ihb => exact .seq iha ihb
  | letpair _ _ iha ihb => exact .letpair iha ihb
  | case _ _ _ iha ihb ihc => exact .case iha ihb ihc
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | beta _ _ ihb ihx => exact .beta ihb ihx
  | primApp hp _ ih => exact .primApp hp ih
  | store _ _ iha ihx => exact .store iha ihx
  | perform hm _ ih => exact .perform (hN _ hm) ih
  | raise hm _ ih => exact .raise (hN _ hm) ih

/-- **A value is first-order at any names**: it applies nothing. -/
theorem of_isVal {N : List UInt32} {v : Expr} (h : IsVal v) : Fo N v := by
  induction h with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam => exact .lam _
  | loc => exact .loc _
  | prim => exact .prim _
  | storeV _ ih => exact .primApp rfl ih

theorem of_val {N : List UInt32} (v : Val) : Fo N v.1 := of_isVal v.2

/-- **Substituting any value keeps a term first-order**: the term's variables are only in data
positions, where the value's code is never applied.  `[spec §19]` -/
theorem subst {N : List UInt32} {e : Expr} (h : Fo N e) : ∀ (j : Nat) (s : Val), Fo N (e.subst j s) := by
  induction h with
  | var i =>
      intro j s
      simp only [Expr.subst]
      split
      · exact of_val s
      · split <;> exact .var _
  | unit => intro _ _; exact .unit
  | loc ℓ => intro _ _; exact .loc ℓ
  | prim p => intro _ _; exact .prim p
  | lam b => intro _ _; exact .lam _
  | pair _ _ iha ihb => intro j s; exact .pair (iha j s) (ihb j s)
  | seq _ _ iha ihb => intro j s; exact .seq (iha j s) (ihb j s)
  | letpair _ _ iha ihb => intro j s; exact .letpair (iha j s) (ihb (j + 2) (s.shift 2 0))
  | case _ _ _ iha ihb ihc =>
      intro j s; exact .case (iha j s) (ihb (j + 1) (s.shift 1 0)) (ihc (j + 1) (s.shift 1 0))
  | inj₁ _ ih => intro j s; exact .inj₁ (ih j s)
  | inj₂ _ ih => intro j s; exact .inj₂ (ih j s)
  | beta _ _ ihb ihx => intro j s; exact .beta (ihb (j + 1) (s.shift 1 0)) (ihx j s)
  | primApp hp _ ih => intro j s; exact .primApp hp (ih j s)
  | store _ _ iha ihx => intro j s; exact .store (iha j s) (ihx j s)
  | perform hm _ ih => intro j s; exact .perform hm (ih j s)
  | raise hm _ ih => intro j s; exact .raise hm (ih j s)

theorem app_arg {N : List UInt32} {f x : Expr} (h : Fo N (.app f x)) : Fo N x := by
  cases h with
  | beta _ hx => exact hx
  | primApp _ hx => exact hx
  | store _ hx => exact hx
  | perform _ hX => exact .pair (.prim _) hX
  | raise _ hX => exact .pair (.prim _) hX

theorem app_fun {N : List UInt32} {f x : Expr} (h : Fo N (.app f x)) : Fo N f := by
  cases h with
  | beta _ _ => exact .lam _
  | primApp _ _ => exact .prim _
  | store ha _ => exact .primApp rfl ha
  | perform _ _ => exact .prim _
  | raise _ _ => exact .prim _

end Fo

/-! ### Contexts and steps -/

/-- **A redex of a first-order configuration is first-order.** -/
theorem Fo.plug_inv {N : List UInt32} : ∀ (K : Kont) {a : Expr}, Fo N (K.plug a) → Fo N a
  | .hole, _, h => h
  | .pairL K _, _, h => by cases h with | pair h _ => exact Fo.plug_inv K h
  | .pairR _ K, _, h => by cases h with | pair _ h => exact Fo.plug_inv K h
  | .letpair K _, _, h => by cases h with | letpair h _ => exact Fo.plug_inv K h
  | .case K _ _, _, h => by cases h with | case h _ _ => exact Fo.plug_inv K h
  | .seq K _, _, h => by cases h with | seq h _ => exact Fo.plug_inv K h
  | .inj₁ K, _, h => by cases h with | inj₁ h => exact Fo.plug_inv K h
  | .inj₂ K, _, h => by cases h with | inj₂ h => exact Fo.plug_inv K h
  | .appR _ K, _, h => Fo.plug_inv K h.app_arg
  | .appL K _, _, h => Fo.plug_inv K h.app_fun

/-- No step's redex is the curried `store` applied to one argument. -/
theorem head_not_store {ℍ : Host} [HostIs ℍ] {μ μ' : Heap} {y a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.prim .store) y) μ' a') : False := by
  cases h

theorem plug_ne_lam {a : Expr} (ha : PlainB a = true) : ∀ (K : Kont) (b : Expr), K.plug a ≠ .lam b
  | .hole, b => by rintro rfl; simp [PlainB] at ha
  | .pairL .., _ | .pairR .., _ | .letpair .., _ | .case .., _ | .appR .., _ | .appL .., _
  | .seq .., _ | .inj₁ _, _ | .inj₂ _, _ => by simp [Kont.plug]

/-- **Replacing a first-order configuration's redex by a first-order term keeps it first-order**,
at a redex that is plain and not the curried `store`. -/
theorem Fo.plug {N : List UInt32} {a a' : Expr} (ha : PlainB a = true)
    (hs : ∀ y, a ≠ .app (.prim .store) y) (ha' : Fo N a') :
    ∀ (K : Kont), Fo N (K.plug a) → Fo N (K.plug a')
  | .hole, _ => ha'
  | .pairL K _, h => by cases h with | pair h₁ h₂ => exact .pair (Fo.plug ha hs ha' K h₁) h₂
  | .pairR _ K, h => by cases h with | pair h₁ h₂ => exact .pair h₁ (Fo.plug ha hs ha' K h₂)
  | .letpair K _, h => by
      cases h with | letpair h₁ h₂ => exact .letpair (Fo.plug ha hs ha' K h₁) h₂
  | .case K _ _, h => by
      cases h with | case h₁ h₂ h₃ => exact .case (Fo.plug ha hs ha' K h₁) h₂ h₃
  | .seq K _, h => by cases h with | seq h₁ h₂ => exact .seq (Fo.plug ha hs ha' K h₁) h₂
  | .inj₁ K, h => by cases h with | inj₁ h => exact .inj₁ (Fo.plug ha hs ha' K h)
  | .inj₂ K, h => by cases h with | inj₂ h => exact .inj₂ (Fo.plug ha hs ha' K h)
  | .appR f K, h => by
      simp only [Kont.plug] at h ⊢
      have ih := Fo.plug ha hs ha' K h.app_arg
      generalize hk : K.plug a = ka at h
      cases h with
      | beta hb _ => exact .beta hb ih
      | primApp hp _ => exact .primApp hp ih
      | store h₁ _ => exact .store h₁ ih
      | perform hm _ =>
          cases K with
          | hole => subst hk; simp [PlainB] at ha
          | pairL K' _ =>
              simp only [Kont.plug, Expr.pair.injEq] at hk
              exact absurd hk.1 (plug_not_prim ha K' _)
          | pairR v K' =>
              simp only [Kont.plug, Expr.pair.injEq] at hk
              obtain ⟨hv, rfl⟩ := hk
              simp only [Kont.plug] at ih ⊢
              rw [hv]
              cases ih with | pair _ h₂ => exact .perform hm h₂
          | _ => simp [Kont.plug] at hk
      | raise hm _ =>
          cases K with
          | hole => subst hk; simp [PlainB] at ha
          | pairL K' _ =>
              simp only [Kont.plug, Expr.pair.injEq] at hk
              exact absurd hk.1 (plug_not_prim ha K' _)
          | pairR v K' =>
              simp only [Kont.plug, Expr.pair.injEq] at hk
              obtain ⟨hv, rfl⟩ := hk
              simp only [Kont.plug] at ih ⊢
              rw [hv]
              cases ih with | pair _ h₂ => exact .raise hm h₂
          | _ => simp [Kont.plug] at hk
  | .appL K v, h => by
      simp only [Kont.plug] at h ⊢
      generalize hk : K.plug a = ka at h
      generalize hvx : Expr.val v = vx at h ⊢
      cases h with
      | beta _ _ => exact absurd hk (plug_ne_lam ha K _)
      | primApp _ _ => exact absurd hk (plug_not_prim ha K _)
      | perform _ _ => exact absurd hk (plug_not_prim ha K _)
      | raise _ _ => exact absurd hk (plug_not_prim ha K _)
      | store h₁ h₂ =>
          cases K with
          | hole => exact absurd hk (hs _)
          | appR f K' =>
              simp only [Kont.plug, Expr.app.injEq] at hk
              obtain ⟨rfl, hk⟩ := hk
              have ih := Fo.plug ha hs ha' (.appR (.prim .store) K')
                (by simp only [Kont.plug]; rw [hk]; exact .primApp rfl h₁)
              simp only [Kont.plug] at ih ⊢
              exact .store ih.app_arg h₂
          | appL K' w =>
              simp only [Kont.plug, Expr.app.injEq] at hk
              exact absurd hk.1 (plug_not_prim ha K' _)
          | _ => simp [Kont.plug] at hk

section steps
variable {ℍ : Host} [HostIs ℍ]

/-- **A head step keeps a first-order term first-order**: the only code it runs is a `λ` the
term holds, applied in place, and the values it reads go to data positions.  `[spec §19]` -/
theorem Fo.head {N : List UInt32} {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a')
    (ha : Fo N a) : Fo N a' := by
  cases h with
  | beta b v => cases ha with | beta hb _ => exact hb.subst 0 v
  | alloc => exact Fo.of_val _
  | free => exact Fo.of_val _
  | load => exact Fo.of_val _
  | store => exact .unit
  | seq => cases ha with | seq _ h => exact h
  | letpair v₁ v₂ e =>
      cases ha with | letpair _ h => exact (h.subst 0 (v₂.shift 1 0)).subst 0 v₁
  | case₁ v => cases ha with | case _ h _ => exact h.subst 0 v
  | case₂ v => cases ha with | case _ _ h => exact h.subst 0 v
  | host => exact Fo.of_val _
  | tab => cases ha with | primApp hp _ => simp [primOwn] at hp
  | idx => exact Fo.of_val _
  | split => exact Fo.of_val _
  | drop => cases ha with | primApp hp _ => simp [primOwn] at hp
  | count => cases ha with | primApp hp _ => simp [primOwn] at hp
  | countTry => cases ha with | primApp hp _ => simp [primOwn] at hp
  | boundedFix => cases ha with | primApp hp _ => simp [primOwn] at hp
  | iterate => cases ha with | primApp hp _ => simp [primOwn] at hp
  | hret => cases ha
  | hop => cases ha
  | hunwind => cases ha
  | uthen => cases ha
  | ufin => cases ha
  | ufinC => cases ha
  | cfret => cases ha
  | cferr => cases ha
  | cfcancel => cases ha
  | cancel => cases ha with | primApp hp _ => simp [primOwn] at hp
  | creraise => cases ha with | primApp hp _ => simp [primOwn] at hp

/-- **A step keeps a first-order term first-order**, from any memory.  `[spec §19]` -/
theorem Fo.step1 {N : List UInt32} {μ μ' : Heap} {e e' : Expr} (h : Step1 (ℍ := ℍ) μ e μ' e')
    (he : Fo N e) : Fo N e' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  exact Fo.plug (head_plain hh) (fun y hy => head_not_store (hy ▸ hh))
    ((Fo.plug_inv K he).head hh) K he

/-- **A run keeps a first-order term first-order**, from any memory.  `[spec §19]` -/
theorem Fo.steps {N : List UInt32} {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e')
    (he : Fo N e) : Fo N e' := by
  induction h with
  | refl => exact he
  | more h₁ _ ih => exact ih (he.step1 h₁)

end steps

/-- **A first-order configuration performs only names of `N`.**  `[spec §19]` -/
theorem Fo.perform_mem {N : List UInt32} {K : Kont} {m i : UInt32} {v : Val}
    (h : Fo N (K.plug (performE (.val (opPayload m i v))))) : m ∈ N := by
  have h := Fo.plug_inv K h
  cases h with
  | primApp hp _ => simp [primOwn] at hp
  | perform hm _ => exact hm

/-- **A first-order configuration raises only names of `N`.**  `[spec §19]` -/
theorem Fo.raise_mem {N : List UInt32} {K : Kont} {m i : UInt32} {v : Val}
    (h : Fo N (K.plug (raiseE (.val (opPayload m i v))))) : m ∈ N := by
  have h := Fo.plug_inv K h
  cases h with
  | primApp hp _ => simp [primOwn] at hp
  | raise hm _ => exact hm

/-! ### The names a term's own code performs or raises -/

/-- The term is a continuation slot of `C`, or an application of one: `κ`, `κ.1`, `κ.1 N`. -/
def contHead (C : List Nat) : Expr → Bool
  | .var i => C.contains i
  | .app f _ => contHead C f
  | _ => false

/-- Two optional lists of names, joined; `none` if either is. -/
def oapp (x y : Option (List UInt32)) : Option (List UInt32) := x.bind fun a => y.map (a ++ ·)

theorem oapp_eq_some {x y : Option (List UInt32)} {n : List UInt32} :
    oapp x y = some n ↔ ∃ a b, x = some a ∧ y = some b ∧ n = a ++ b := by
  cases x <;> cases y <;> simp [oapp, eq_comm]

/-- The slots `C` under `d` more binders. -/
def shiftC (d : Nat) (C : List Nat) : List Nat := C.map (· + d)

/-- **The names `e`'s own code performs or raises**, the continuation slots `C`'s calls excluded:
`perform` and `raise` at literal names, through every `λ` it holds, the primitives that run no
code they are given, and the arguments of a call of a continuation slot. A `λ` applied in place
to a continuation (an alias of `κ`, or the answer of its resume) binds a continuation slot. `none`
where `e` may run code it does not hold: an application of a variable that is not a continuation
slot or of a computed function, a primitive that runs a function it is given, or an operation at a
name that is not a literal.  `[spec §19]` -/
def _root_.BoCa.Expr.own (C : List Nat) : Expr → Option (List UInt32)
  | .var _ | .unit | .loc _ | .prim _ => some []
  | .lam b => b.own (shiftC 1 C)
  | .pair a b | .seq a b => oapp (a.own C) (b.own C)
  | .letpair a b => oapp (a.own C) (b.own (shiftC 2 C))
  | .case a b c => oapp (oapp (a.own C) (b.own (shiftC 1 C))) (c.own (shiftC 1 C))
  | .inj₁ a | .inj₂ a => a.own C
  | .app f x =>
      if contHead C f then oapp (f.own C) (x.own C) else
      match f with
      | .lam b => oapp (b.own (if contHead C x then 0 :: shiftC 1 C else shiftC 1 C)) (x.own C)
      | .prim .perform => match x with
          | .pair (.prim (.lit (.i32 m))) X => oapp (some [m]) (X.own C)
          | _ => none
      | .prim .raise => match x with
          | .pair (.prim (.lit (.i32 m))) X => oapp (some [m]) (X.own C)
          | _ => none
      | .prim p => if primOwn p then x.own C else none
      | .app (.prim .store) a => oapp (a.own C) (x.own C)
      | _ => none

theorem contHead_mentions {C : List Nat} : ∀ {e : Expr}, contHead C e = true →
    ∃ j ∈ C, mentions j e = true
  | .var i, h => ⟨i, by simpa [contHead] using h, by simp [mentions]⟩
  | .app f _, h => by
      obtain ⟨j, hj, hm⟩ := contHead_mentions (e := f) h
      exact ⟨j, hj, by simp [mentions, hm]⟩

theorem not_contHead {C : List Nat} {e : Expr} (h : ∀ j ∈ C, mentions j e = false) :
    contHead C e = false := by
  cases hc : contHead C e
  · rfl
  · obtain ⟨j, hj, hm⟩ := contHead_mentions hc
    rw [h j hj] at hm; cases hm

theorem mem_shiftC {d : Nat} {C : List Nat} {j : Nat} : j ∈ shiftC d C ↔ ∃ c ∈ C, j = c + d := by
  simp [shiftC, eq_comm]

/-- The slots under binders mention nothing a term under them does not. -/
theorem shiftC_free {d : Nat} {C : List Nat} {b : Expr}
    (h : ∀ j ∈ C, mentions (j + d) b = false) : ∀ j ∈ shiftC d C, mentions j b = false := by
  intro j hj
  obtain ⟨c, hc, rfl⟩ := mem_shiftC.mp hj
  exact h c hc

/-- **A term whose own code mentions none of the continuation slots is first-order at its own
names**: then no call of a slot is in it, and its own names are what it performs and raises.
`[spec §19]` -/
theorem fo_of_own : ∀ (e : Expr) {C : List Nat} {ns : List UInt32}, e.own C = some ns →
    (∀ j ∈ C, mentions j e = false) → Fo ns e ∧ ∀ b, e = .lam b → Fo ns b
  | .var _, _, _, _, _ => ⟨.var _, fun _ h => by cases h⟩
  | .unit, _, _, _, _ => ⟨.unit, fun _ h => by cases h⟩
  | .loc _, _, _, _, _ => ⟨.loc _, fun _ h => by cases h⟩
  | .prim _, _, _, _, _ => ⟨.prim _, fun _ h => by cases h⟩
  | .lam b, C, ns, h, hm => by
      simp only [Expr.own] at h
      have := (fo_of_own b h (shiftC_free (d := 1) fun j hj => by
        have := hm j hj; simpa [mentions] using this)).1
      exact ⟨.lam _, fun b' hb => by cases hb; exact this⟩
  | .pair a b, C, ns, h, hm => by
      simp only [Expr.own, oapp_eq_some] at h
      obtain ⟨na, nb, ha, hb, rfl⟩ := h
      simp only [mentions, Bool.or_eq_false_iff] at hm
      exact ⟨.pair ((fo_of_own a ha fun j hj => (hm j hj).1).1.mono fun _ h => by simp [h])
        ((fo_of_own b hb fun j hj => (hm j hj).2).1.mono fun _ h => by simp [h]),
        fun _ h => by cases h⟩
  | .seq a b, C, ns, h, hm => by
      simp only [Expr.own, oapp_eq_some] at h
      obtain ⟨na, nb, ha, hb, rfl⟩ := h
      simp only [mentions, Bool.or_eq_false_iff] at hm
      exact ⟨.seq ((fo_of_own a ha fun j hj => (hm j hj).1).1.mono fun _ h => by simp [h])
        ((fo_of_own b hb fun j hj => (hm j hj).2).1.mono fun _ h => by simp [h]),
        fun _ h => by cases h⟩
  | .letpair a b, C, ns, h, hm => by
      simp only [Expr.own, oapp_eq_some] at h
      obtain ⟨na, nb, ha, hb, rfl⟩ := h
      simp only [mentions, Bool.or_eq_false_iff] at hm
      exact ⟨.letpair ((fo_of_own a ha fun j hj => (hm j hj).1).1.mono fun _ h => by simp [h])
        ((fo_of_own b hb (shiftC_free fun j hj => (hm j hj).2)).1.mono fun _ h => by simp [h]),
        fun _ h => by cases h⟩
  | .case a b c, C, ns, h, hm => by
      simp only [Expr.own, oapp_eq_some] at h
      obtain ⟨nab, nc, hab, hc, rfl⟩ := h
      obtain ⟨na, nb, ha, hb, rfl⟩ := hab
      simp only [mentions, Bool.or_eq_false_iff] at hm
      exact ⟨.case ((fo_of_own a ha fun j hj => (hm j hj).1.1).1.mono fun _ h => by simp [h])
        ((fo_of_own b hb (shiftC_free fun j hj => (hm j hj).1.2)).1.mono fun _ h => by simp [h])
        ((fo_of_own c hc (shiftC_free fun j hj => (hm j hj).2)).1.mono fun _ h => by simp [h]),
        fun _ h => by cases h⟩
  | .inj₁ a, C, ns, h, hm => by
      simp only [Expr.own] at h
      exact ⟨.inj₁ (fo_of_own a h fun j hj => by simpa [mentions] using hm j hj).1,
        fun _ h => by cases h⟩
  | .inj₂ a, C, ns, h, hm => by
      simp only [Expr.own] at h
      exact ⟨.inj₂ (fo_of_own a h fun j hj => by simpa [mentions] using hm j hj).1,
        fun _ h => by cases h⟩
  | .app f x, C, ns, h, hm => by
      simp only [mentions, Bool.or_eq_false_iff] at hm
      have hf : ∀ j ∈ C, mentions j f = false := fun j hj => (hm j hj).1
      have hx : ∀ j ∈ C, mentions j x = false := fun j hj => (hm j hj).2
      refine ⟨?_, fun _ h => by cases h⟩
      unfold Expr.own at h
      rw [if_neg (by simp [not_contHead hf])] at h
      split at h
      · rename_i b
        rw [if_neg (by simp [not_contHead hx])] at h
        obtain ⟨nb, nx, hb, hx', rfl⟩ := oapp_eq_some.mp h
        have hb' := (fo_of_own (.lam b) (C := C) (by simpa [Expr.own] using hb) hf).2 b rfl
        exact .beta (hb'.mono fun _ h => by simp [h])
          ((fo_of_own x hx' hx).1.mono fun _ h => by simp [h])
      · split at h
        · rename_i m X
          obtain ⟨_, nX, h₁, hX, rfl⟩ := oapp_eq_some.mp h
          cases h₁
          have hX' : ∀ j ∈ C, mentions j X = false := fun j hj => by
            have := hx j hj; simp only [mentions, Bool.or_eq_false_iff] at this; exact this.2
          exact .perform (by simp) ((fo_of_own X hX hX').1.mono fun _ h => by simp [h])
        · cases h
      · split at h
        · rename_i m X
          obtain ⟨_, nX, h₁, hX, rfl⟩ := oapp_eq_some.mp h
          cases h₁
          have hX' : ∀ j ∈ C, mentions j X = false := fun j hj => by
            have := hx j hj; simp only [mentions, Bool.or_eq_false_iff] at this; exact this.2
          exact .raise (by simp) ((fo_of_own X hX hX').1.mono fun _ h => by simp [h])
        · cases h
      · rename_i p _ _
        split at h
        · rename_i hp
          exact .primApp hp (fo_of_own x h hx).1
        · cases h
      · rename_i a
        obtain ⟨na, nx, ha, hx', rfl⟩ := oapp_eq_some.mp h
        have ha' : ∀ j ∈ C, mentions j a = false := fun j hj => by
          have := hf j hj; simp only [mentions, Bool.or_eq_false_iff] at this; exact this.2
        exact .store ((fo_of_own a ha ha').1.mono fun _ h => by simp [h])
          ((fo_of_own x hx' hx).1.mono fun _ h => by simp [h])
      · cases h

/-! ### The work of a tail-resumptive clause -/

/-- **The work of a tail-resumptive clause is first-order at the clause's own names.** `M`
resumes `κ`, in the slot `k`, in tail position on every path, and `M'` is `M` without its
resumes; the continuation slots `C` hold `k`, and `M` mentions no other of them. Then `M'` is
first-order at `M`'s own names: each resume `κ.1 N` leaves its answer `N`, whose names are among
the resume's, and an alias of `κ` is a slot `M'` no longer has.  `[spec §19]` -/
theorem fo_of_tail {k : Nat} {M M' : Expr} (h : TailResumesAt k M M') :
    ∀ {C : List Nat} {ns : List UInt32}, M.own C = some ns → k ∈ C →
      (∀ j ∈ C, j ≠ k → mentions j M = false) → Fo ns M' := by
  induction h with
  | @resume k N hN =>
      intro C ns h hk hC
      have hc : contHead C (resumeAt k) = true := by simp [resumeAt, contHead, hk]
      have hr : (resumeAt k).own C = some [] := by
        simp [resumeAt, Expr.own, contHead, hk, oapp, Expr.val, Val.inj₁, Val.unit]
      unfold Expr.own at h
      rw [if_pos hc, hr] at h
      obtain ⟨_, nN, h₁, hN', rfl⟩ := oapp_eq_some.mp h
      refine (fo_of_own N hN' fun j hj => ?_).1.mono fun _ h => by simp [h]
      by_cases hjk : j = k
      · subst hjk; exact hN
      · have := hC j hj hjk
        simp only [mentions, Bool.or_eq_false_iff] at this
        exact this.2
  | @case k e B₁ B₂ B₁' B₂' he _ _ ih₁ ih₂ =>
      intro C ns h hk hC
      simp only [Expr.own, oapp_eq_some] at h
      obtain ⟨nab, nc, hab, hc, rfl⟩ := h
      obtain ⟨na, nb, ha, hb, rfl⟩ := hab
      have hm : ∀ j ∈ C, j ≠ k → mentions j e = false ∧ mentions (j + 1) B₁ = false ∧
          mentions (j + 1) B₂ = false := fun j hj hjk => by
        have := hC j hj hjk; simp only [mentions, Bool.or_eq_false_iff] at this
        exact ⟨this.1.1, this.1.2, this.2⟩
      have hsh : ∀ (B : Expr), (∀ j ∈ C, j ≠ k → mentions (j + 1) B = false) →
          ∀ j ∈ shiftC 1 C, j ≠ k + 1 → mentions j B = false := fun B hB j hj hjk => by
        obtain ⟨c, hc, rfl⟩ := mem_shiftC.mp hj
        exact hB c hc (fun h => hjk (by rw [h]))
      have hk' : k + 1 ∈ shiftC 1 C := mem_shiftC.mpr ⟨k, hk, rfl⟩
      refine .case ((fo_of_own e ha fun j hj => ?_).1.mono fun _ h => by simp [h])
        ((ih₁ hb hk' (hsh _ fun j hj hjk => (hm j hj hjk).2.1)).mono fun _ h => by simp [h])
        ((ih₂ hc hk' (hsh _ fun j hj hjk => (hm j hj hjk).2.2)).mono fun _ h => by simp [h])
      by_cases hjk : j = k
      · subst hjk; exact he
      · exact (hm j hj hjk).1
  | @letpair k e B B' he _ ih =>
      intro C ns h hk hC
      simp only [Expr.own, oapp_eq_some] at h
      obtain ⟨na, nb, ha, hb, rfl⟩ := h
      have hm : ∀ j ∈ C, j ≠ k → mentions j e = false ∧ mentions (j + 2) B = false :=
        fun j hj hjk => by
          have := hC j hj hjk; simp only [mentions, Bool.or_eq_false_iff] at this; exact this
      have hk' : k + 2 ∈ shiftC 2 C := mem_shiftC.mpr ⟨k, hk, rfl⟩
      refine .letpair ((fo_of_own e ha fun j hj => ?_).1.mono fun _ h => by simp [h])
        ((ih hb hk' fun j hj hjk => ?_).mono fun _ h => by simp [h])
      · by_cases hjk : j = k
        · subst hjk; exact he
        · exact (hm j hj hjk).1
      · obtain ⟨c, hc, rfl⟩ := mem_shiftC.mp hj
        exact (hm c hc (fun h => hjk (by rw [h]))).2
  | @seq k e B B' he _ ih =>
      intro C ns h hk hC
      simp only [Expr.own, oapp_eq_some] at h
      obtain ⟨na, nb, ha, hb, rfl⟩ := h
      have hm : ∀ j ∈ C, j ≠ k → mentions j e = false ∧ mentions j B = false :=
        fun j hj hjk => by
          have := hC j hj hjk; simp only [mentions, Bool.or_eq_false_iff] at this; exact this
      refine .seq ((fo_of_own e ha fun j hj => ?_).1.mono fun _ h => by simp [h])
        ((ih hb hk fun j hj hjk => (hm j hj hjk).2).mono fun _ h => by simp [h])
      by_cases hjk : j = k
      · subst hjk; exact he
      · exact (hm j hj hjk).1
  | @bind k e B B' he _ ih =>
      intro C ns h hk hC
      have hm : ∀ j ∈ C, j ≠ k → mentions (j + 1) B = false ∧ mentions j e = false :=
        fun j hj hjk => by
          have := hC j hj hjk
          simp only [mentions, Expr.val, Val.lam, Bool.or_eq_false_iff] at this; exact this
      have he' : ∀ j ∈ C, mentions j e = false := fun j hj => by
        by_cases hjk : j = k
        · subst hjk; exact he
        · exact (hm j hj hjk).2
      have hce := not_contHead he'
      simp only [Expr.val, Val.lam] at h ⊢
      unfold Expr.own at h
      simp only [contHead, hce, if_false, Bool.false_eq_true] at h
      obtain ⟨nb, ne, hb, hE, rfl⟩ := oapp_eq_some.mp h
      have hk' : k + 1 ∈ shiftC 1 C := mem_shiftC.mpr ⟨k, hk, rfl⟩
      refine .beta ((ih hb hk' fun j hj hjk => ?_).mono fun _ h => by simp [h])
        ((fo_of_own e hE he').1.mono fun _ h => by simp [h])
      obtain ⟨c, hc, rfl⟩ := mem_shiftC.mp hj
      exact (hm c hc (fun h => hjk (by rw [h]))).1
  | @ret k X X' R₀ _ _ ih =>
      intro C ns h hk hC
      simp only [Expr.val, Val.lam] at h
      unfold Expr.own at h
      simp only [contHead, if_false, Bool.false_eq_true] at h
      obtain ⟨_, nX, _, hX, rfl⟩ := oapp_eq_some.mp h
      refine (ih hX hk fun j hj hjk => ?_).mono fun _ h => by simp [h]
      have := hC j hj hjk
      simp only [mentions, Expr.val, Val.lam, Bool.or_eq_false_iff] at this
      exact this.2
  | @rebind k B B' hB _ ih =>
      intro C ns h hk hC
      have hck : contHead C (.var k) = true := by simp [contHead, hk]
      simp only [Expr.val, Val.lam] at h
      unfold Expr.own at h
      simp only [contHead, hk, if_false, Bool.false_eq_true, List.contains_eq_mem,
        decide_true, if_true] at h
      obtain ⟨nb, _, hb, hv, rfl⟩ := oapp_eq_some.mp h
      have hB' : Fo nb B' := ih hb (List.mem_cons_self) fun j hj hj0 => by
        rcases List.mem_cons.mp hj with rfl | hj
        · exact absurd rfl hj0
        obtain ⟨c, hc, rfl⟩ := mem_shiftC.mp hj
        by_cases hck : c = k
        · subst hck; exact hB
        · have := hC c hc hck
          simp only [mentions, Expr.val, Val.lam, Bool.or_eq_false_iff] at this
          exact this.1
      exact (hB'.subst 0 .unit).mono fun _ h => by simp [h]

/-- `e'` is `e` with values given to some of its variables, one substitution at a time. -/
inductive SubstOf : Expr → Expr → Prop where
  | refl (e : Expr) : SubstOf e e
  | subst {e e' : Expr} (j : Nat) (v : Val) : SubstOf e e' → SubstOf e (e'.subst j v)

theorem Fo.substOf {N : List UInt32} {e e' : Expr} (h : SubstOf e e') (he : Fo N e) : Fo N e' := by
  induction h with
  | refl => exact he
  | subst j v _ ih => exact ih.subst j v

section work
variable {ℍ : Host} [HostIs ℍ]

/-- **The names a tail-resumptive clause's work performs or raises.** For a clause body `M`, `κ`
in the slot `0`, whose work is `M'` (`TailResumesAt 0 M M'`) and whose own names are `ns`: every
run of the work, with any values given to its variables (the operation's argument and the
handler's captures among them), from any memory, performs and raises only names of `ns`.  This
is the code the direct call of the clause runs at the `perform`.  `[spec §19]` -/
theorem tail_work_names {M M' : Expr} {ns : List UInt32} (hk : TailResumesAt 0 M M')
    (hown : M.own [0] = some ns) {W : Expr} (hW : SubstOf M' W) {μ μ' : Heap} {e : Expr}
    (hs : Steps (ℍ := ℍ) μ W μ' e) {K : Kont} {m i : UInt32} {v : Val} :
    (e = K.plug (performE (.val (opPayload m i v))) → m ∈ ns) ∧
    (e = K.plug (raiseE (.val (opPayload m i v))) → m ∈ ns) := by
  have hfo : Fo ns e :=
    ((fo_of_tail hk hown (List.mem_singleton.mpr rfl) fun j hj h0 =>
      absurd (List.mem_singleton.mp hj) h0).substOf hW).steps hs
  exact ⟨fun he => Fo.perform_mem (he ▸ hfo), fun he => Fo.raise_mem (he ▸ hfo)⟩

end work

/-! ### Condition 2 over the clause's names -/

/-- **The names `ns` are unhandled in `K`**: no frame of `K` catches an operation or a raise of a
name of `ns`.  `[spec §19]` -/
def UnhandledNames (ns : List UInt32) (K : Kont) : Prop := ∀ m ∈ ns, K.Catches m = false

/-- A clause whose own code performs and raises nothing meets condition 2 in every `K`. -/
theorem unhandledNames_nil (K : Kont) : UnhandledNames [] K := fun _ h => absurd h (by simp)

/-- Over a row's names, condition 2 is `UnhandledIn`. -/
theorem unhandledIn_iff_names {S : Row} {K : Kont} :
    UnhandledIn S K ↔ UnhandledNames (S.map (·.n)) K := by
  constructor
  · intro h m hm
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
    exact h o ho
  · intro h o ho
    exact h o.n (List.mem_map.mpr ⟨o, ho, rfl⟩)

section runs
variable {ℍ : Host} [HostIs ℍ]

/-- **Condition 2 over names, at the program's flow record.** In a run of `e₀` from a memory that
holds no code, at every configuration that holds a handler frame over a context `K` filled by `p`,
names none of which `flows e₀` may catch are unhandled in `K`.  `[spec §19]` -/
theorem steps_unhandledNames {e₀ : Expr} {μ₀ μ : Heap} {e : Expr} (h : Steps (ℍ := ℍ) μ₀ e₀ μ e)
    (hμ₀ : ∀ ℓ v, μ₀ ℓ = some v → v.1.hin = {} ∧ v.1.pn = {}) {K₀ K : Kont} {H : Val} {p : Expr}
    (he : e = K₀.plug (BoLo.hndE H (K.plug p))) {ns : List UInt32}
    (hS : ∀ m ∈ ns, ¬ (flows e₀).Catches m) : UnhandledNames ns K := by
  have hfl := (steps_flows h hμ₀).1
  rw [he] at hfl
  have hx : (K.plug p).hin ≤ flows e₀ :=
    HIn.le_trans (fl_hndE_ge H _) ((plug_fl_ge (a := BoLo.hndE H (K.plug p)) rfl K₀).1 hfl)
  intro m hm
  cases hc : K.Catches m
  · rfl
  · exact absurd (HIn.Catches.mono hx (catches_hin p hc)) (hS m hm)

end runs

end BoCa.Fig16.LogRel.Core.ClauseKinds
